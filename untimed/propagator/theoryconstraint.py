import logging
from collections import defaultdict, namedtuple
import clingo

from typing import List, Dict, Tuple, Set, Any, Optional

import untimed.util as util

CONSTRAINT_CHECK = {"NONE": 0,
                    "UNIT": 1,
                    "CONFLICT": -1}


class AtomInfo:

	__slots__ = ["sign", "time_mod", "name"]

	def __init__(self, sign, time_mod, name):
		self.sign = sign
		self.time_mod = time_mod
		self.name = name


# just an alias
atom_info = AtomInfo


class PropagationError(Exception):
	pass


class TimeAtomToSolverLit:
	"""
	Maps a name id to a solver literal.
	Has helper methods to retrieve either a literal or a name id

	name_id is a Tuple[sign, name, time]
	"""
	name_to_lit: Dict[Tuple[int, str, int], int] = {}

	lit_to_name: Dict[int, Set[Tuple[int, str, int]]] = defaultdict(set)

	@classmethod
	#@profile
	def add(cls, name_id, lit):
		if name_id not in cls.name_to_lit:
			cls.name_to_lit[name_id] = lit

		cls.lit_to_name[lit].add(name_id)

	@classmethod
	def grab_lit(cls, name_id):
		return cls.name_to_lit[name_id]

	@classmethod
	def grab_name(cls, lit):
		return cls.lit_to_name[lit]

	@classmethod
	def has_name(cls, name_id):
		return name_id in cls.name_to_lit

	@classmethod
	def reset(cls):
		cls.name_to_lit = {}
		cls.lit_to_name = defaultdict(set)


class SymbolToProgramLit:
	symbol_to_lit: Dict[Any, int] = {}

	@classmethod
	def add(cls, symbol, lit):
		if symbol not in cls.symbol_to_lit:
			cls.symbol_to_lit[symbol] = lit

	@classmethod
	def grab_lit(cls, symbol):
		return cls.symbol_to_lit[symbol]

	@classmethod
	def reset(cls):
		cls.symbol_to_lit = {}
		cls.symbol_to_lit.clear()

@util.Timer("parse_atom")
#@profile
def parse_atoms(constraint) -> Tuple[Dict[str, atom_info], int, int, Set[Tuple[str, int]]]:
	"""
	Extract the relevant information of the given theory atom and populate self.t_atom_info

	:param constraint: clingo TheoryAtom
	"""
	t_atom_info: Dict[str, atom_info] = {}

	min_time, max_time = parse_constraint_times(constraint.term.arguments)

	signatures = set()
	for atom in constraint.elements:
		# this gives me the "type" of the term | e.g. for +~on(..) it would return +~
		term_type: str = atom.terms[0].name

		signature: Tuple[str, int] = (
			atom.terms[0].arguments[0].name, len(atom.terms[0].arguments[0].arguments) + 1)

		name: str = str(atom.terms[0].arguments[0])[:-1] + ","

		uq_name: str = term_type + name

		if term_type == "+.":
			sign = 1
			time_mod = 0
		elif term_type == "+~":
			sign = 1
			time_mod = +1
		elif term_type == "-.":
			sign = -1
			time_mod = 0
		elif term_type == "-~":
			sign = -1
			time_mod = +1
		else:
			raise TypeError(f"Invalid term prefix {term_type} used in {constraint}")

		t_atom_info[uq_name] = atom_info(sign=sign, time_mod=time_mod, name=name)

		signatures.add(signature)

	return t_atom_info, min_time, max_time, signatures


def parse_constraint_times(times) -> Tuple[int, int]:
	"""
	Get the minimum and maximum time from the theory atom

	:param times: List of theory atom arguments
	"""
	if len(times) == 1:
		max_time = times[0].number
		min_time = 0
	else:
		max_time = times[1].number
		min_time = times[0].number

	return min_time, max_time


def build_symbol_id(info, time):
	"""
	Builds the name_id for TimeAtomToSolverLit

	:param info: Information dictionary for a particular atom
	:param time: The time point
	:return: A name_id Triple
	"""
	return info.sign, info.name, time


def parse_time(s_atom) -> int:
	"""
	Parses the time point of the given atom
	:param s_atom: clingo symbolic atom
	:return: time
	"""
	# time = str(s_atom.symbol).split(",")[-1].replace(")", "").strip()
	time = s_atom.symbol.arguments[-1].number
	return int(time)


def get_assigned_time(info: atom_info, time: int) -> int:
	"""
	Calculates the assigned time based on the real time point

	:param info: Information dictionary for a particular atom
	:param time: The time point
	:return: assigned time
	"""
	return time + info.time_mod


def reverse_assigned_time(info: atom_info, assigned_time: int) -> int:
	"""
	Calculates the real time point based on the assigned time

	:param info: Information dictionary for a particular atom
	:param assigned_time: The assigned time
	:return: time
	"""
	return assigned_time - info.time_mod


def form_nogood(t_atom_info, assigned_time: int) -> Optional[List[int]]:
	"""
	Forms a nogood based on the assigned time and atoms of a theory constraint

	:param t_atom_info: Complete information dictionary of the theory constraint
	:param assigned_time: the assigned time
	:return: the nogood for the given assigned time and constraint
	"""

	ng: List[int] = []

	try:
		for uq_name in t_atom_info.keys():
			time: int = reverse_assigned_time(t_atom_info[uq_name], assigned_time)
			ng.append(TimeAtomToSolverLit.grab_lit(build_symbol_id(t_atom_info[uq_name], time)))
	except KeyError:
		# this error would happen if an id is not in the mapping
		# if this happens it means the nogood does not exist for this assigned time
		return None
	return list(ng)


def check_assignment(nogood, control) -> int:
	"""
	Checks if a nogood is a conflict or unit in the current assignment

	:param nogood: nogood that will be checked
	:param control: clingo PropagateControl class
	:return int value that denotes the result of the check. See CONSTRAINT_CHECK for details
	"""
	if nogood is None:
		return CONSTRAINT_CHECK["NONE"]

	true_count: int = 0

	for lit in nogood:
		if control.assignment.is_true(lit):
			# if its true
			true_count += 1
		elif control.assignment.is_false(lit):
			# if one is false then it doesnt matter
			return CONSTRAINT_CHECK["NONE"]

	if true_count == len(nogood):
		return CONSTRAINT_CHECK["CONFLICT"]
	elif true_count == len(nogood) - 1:
		return CONSTRAINT_CHECK["UNIT"]
	else:
		return CONSTRAINT_CHECK["NONE"]


def check_assignment_complete(nogood, control) -> int:
	"""
	Checks if a nogood is a conflict under a complete assignment

	:param nogood: nogood that will be checked
	:param control: clingo PropagateControl class
	:return int value that denotes the result of the check. See CONSTRAINT_CHECK for details
	"""
	if nogood is None:
		return CONSTRAINT_CHECK["NONE"]

	true_count: int = 0

	for lit in nogood:
		if control.assignment.is_false(lit):
			# if one is false then it doesnt matter
			return CONSTRAINT_CHECK["NONE"]

	# if no literal is false it means they are all true
	# which leads to a conflict
	return CONSTRAINT_CHECK["CONFLICT"]


def get_at_from_name_id(name_id: Tuple[int, str, int], t_atom_info):
	sign, name, time = name_id

	ats = set()
	for uq_name, info in t_atom_info.items():
		if info.sign == sign and info.name == name:
			ats.add(get_assigned_time(info, time))

	return ats

SYMBOLS_LOOKED = set()
class TheoryConstraint:
	"""
	Base class for all theory constraints.

	Members:
	t_atom_info             -- Dictionary that holds relevant information
								for all atoms in the constraint

	max_time                -- Max time of the theory constraint

	min_time                -- Min time of the theory constraint

	"""

	__slots__ = ["t_atom_info", "max_time", "min_time", "signatures", "logger"]

	def __init__(self, constraint) -> None:
		self.logger = logging.getLogger(self.__module__ + "." + self.__class__.__name__)

		self.t_atom_info: Dict[str, atom_info] = {}

		self.max_time: int = None
		self.min_time: int = None

		self.signatures: Set[Tuple[str, int]]

		self.t_atom_info, self.min_time, self.max_time, self.signatures = parse_atoms(constraint)

	@property
	def t_atom_names(self):
		return self.t_atom_info.keys()

	@property
	def size(self) -> int:
		return len(self.t_atom_info.keys())

	@util.Count("Init")
	@util.Timer("Init")
	def init(self, init) -> List[int]:
		self.init_mappings(init)
		self.signatures = 0
		return self.build_watches(init)

	#@profile
	def init_mappings(self, init) -> None:
		"""
		Loop through the symbolic atoms matching the signatures of the atoms in the theory constraint.
		If a match is found, we add it to TimeAtomToSolverLit

		:param init: clingo PropagateInit class
		"""
		for uq_name, info in self.t_atom_info.items():
			max_time = self.max_time - info.time_mod
			min_time = self.min_time - info.time_mod
			for time in range(min_time, max_time + 1):

				symbol = clingo.parse_term(f"{info.name}{time})")
				if symbol in SYMBOLS_LOOKED:
					continue

				SYMBOLS_LOOKED.add(symbol)
				try:
					solver_lit: int = init.solver_literal(SymbolToProgramLit.grab_lit(symbol)) * info.sign
				except KeyError:
					# If this happens, it means that the symbol is not in the SymbolToProgramLit mapping
					# this can only happen if the symbol does not exist!
					# so, just continue
					continue
				TimeAtomToSolverLit.add(build_symbol_id(info, time), solver_lit)

	def build_watches(self, init) -> List[int]:
		"""
		Add watches to the solver. This should be implemented by child class
		:param init: clingo PropagateInit class
		:return: List of literals that are watches by this theory constraint
		"""
		pass

	@util.Timer("Undo")
	@util.Count("Undo")
	def undo(self, thread_id, assign, changes) -> None:
		pass

	def propagate(self, control, changes) -> Optional[List[Tuple[int, int]]]:
		pass

	def check(self, control):
		for assigned_time in range(self.min_time, self.max_time + 1):
			ng = form_nogood(self.t_atom_info, assigned_time)
			if check_assignment_complete(ng, control) == CONSTRAINT_CHECK["CONFLICT"]:
				if not control.add_nogood(ng) or not control.propagate():
					for lit in ng:
						print("lit: {}, val: {}".format(lit, str(control.assignment.value)))
					return None
		return 0

class TheoryConstraintSize1(TheoryConstraint):
	__slots__ = []

	def __init__(self, constraint) -> None:
		super().__init__(constraint)
		self.logger = logging.getLogger(self.__module__ + "." + self.__class__.__name__)

	def init_mappings(self, init) -> None:
		"""
		Instead of adding to TimeAtomToSolverLit it immediately adds a clause for the nogood
		"""
		for uq_name, info in self.t_atom_info.items():
			max_time = self.max_time - info.time_mod
			min_time = self.min_time - info.time_mod
			for time in range(min_time, max_time + 1):

				symbol = clingo.parse_term(f"{info.name}{time})")
				try:
					solver_lit: int = init.solver_literal(SymbolToProgramLit.grab_lit(symbol)) * info.sign
				except KeyError:
					# If this happens, it means that the symbol is not in the SymbolToProgramLit mapping
					# this can only happen if the symbol does not exist!
					# so, just continue
					continue

				# add nogood
				init.add_clause([-solver_lit])

			self.t_atom_info[uq_name].clear()

		del self.min_time
		del self.max_time

	def check(self, *args, **kwargs):
		return 0


class TheoryConstraintSize2(TheoryConstraint):
	__slots__ = []

	def __init__(self, constraint) -> None:
		super().__init__(constraint)
		self.logger = logging.getLogger(self.__module__ + "." + self.__class__.__name__)

	def build_watches(self, init) -> Set[int]:
		"""
		Since there are only 2 atoms in the constraint we add all literals as watches
		"""
		watches = set()
		for assigned_time in range(self.min_time, self.max_time + 1):
			lits = form_nogood(self.t_atom_info, assigned_time)
			if lits is None:
				continue
			for lit in lits:
				init.add_watch(lit)
				watches.add(lit)

		return watches

	@util.Count("Propagation")
	def propagate(self, control, changes) -> Optional[List[Tuple]]:
		"""
		For any relevant change, immediately form the nogood
		for the assigned times it is in and add it to the solver

		:param control: clingo PropagateControl class
		:param changes: list of watches that were assigned
		:return None if propagation has to stop, A list of (delete, add) pairs of watches if propagation can continue
		"""
		with util.Timer("Propagation"):
			if type(changes) == int:
				changes = [changes]

			for lit in changes:
				ats = set()
				for name_id in TimeAtomToSolverLit.grab_name(lit):
					ats.update(get_at_from_name_id(name_id, self.t_atom_info))

				for assigned_time in ats:
					ng = form_nogood(self.t_atom_info, assigned_time)
					if ng is None:
						continue
					if not control.add_nogood(ng) or not control.propagate():
						return None

			return []


class TheoryConstraintSize2ForProp2WatchMap(TheoryConstraint):
	__slots__ = []

	def __init__(self, constraint) -> None:
		super().__init__(constraint)
		self.logger = logging.getLogger(self.__module__ + "." + self.__class__.__name__)

	def build_watches(self, init) -> Set[int]:
		"""
		Since there are only 2 atoms in the constraint we add all literals as watches
		"""
		watches = set()
		for assigned_time in range(self.min_time, self.max_time + 1):
			lits = form_nogood(self.t_atom_info, assigned_time)
			if lits is None:
				continue
			for lit in lits:
				init.add_watch(lit)
				watches.add((lit, assigned_time))

		return watches

	@util.Count("Propagation")
	def propagate(self, control, change) -> Optional[List[Tuple]]:
		"""
		For any relevant change, immediately form the nogood
		for the assigned times it is in and add it to the solver

		:param control: clingo PropagateControl object
		:param change: lit and assigned time pair
		:return None if propagation has to stop, A list of (delete, add) pairs of watches if propagation can continue
		"""
		with util.Timer("Propagation"):

			lit, assigned_time = change

			ng = form_nogood(self.t_atom_info, assigned_time)
			if ng is None:
				return []
			if not control.add_nogood(ng) or not control.propagate():
				return None

			return []


class TheoryConstraintNaive(TheoryConstraint):
	__slots__ = []

	def __init__(self, constraint) -> None:
		super().__init__(constraint)
		self.logger = logging.getLogger(self.__module__ + "." + self.__class__.__name__)

	def build_watches(self, init) -> Set[int]:
		"""
		Since there are only 2 atoms in the constraint we add all literals as watches
		"""
		watches = set()
		for assigned_time in range(self.min_time, self.max_time + 1):
			lits = form_nogood(self.t_atom_info, assigned_time)
			if lits is None:
				continue
			for lit in lits:
				init.add_watch(lit)
				watches.add(lit)

		return watches

	@util.Count("Propagation")
	def propagate(self, control, changes) -> Optional[List[Tuple]]:
		"""
		For any relevant change, check the assignment of the whole nogood
		for the assigned times it is in. If it it conflicting or unit add the nogood to the solver

		:param control: clingo PropagateControl object
		:param changes: list of watches that were assigned
		:return None if propagation has to stop, A list of (delete, add) pairs of watches if propagation can continue
		"""

		with util.Timer("Propagation"):
			if type(changes) == int:
				changes = [changes]

			for lit in changes:
				ats = set()
				for name_id in TimeAtomToSolverLit.grab_name(lit):
					ats.update(get_at_from_name_id(name_id, self.t_atom_info))

				for assigned_time in ats:
					ng = form_nogood(self.t_atom_info, assigned_time)
					if ng is None:
						continue

					update_result = check_assignment(ng, control)

					if update_result == CONSTRAINT_CHECK["CONFLICT"] or update_result == CONSTRAINT_CHECK["UNIT"]:
						if not control.add_nogood(ng) or not control.propagate():
							return None

			return []


def choose_lit(lits: List[int], current_watch: int, control) -> Optional[int]:
	"""
	Checks the literals for a nogood and check for new watches

	:param lits: the current nogood
	:param current_watch: the watch being propagated
	:param  control: A clingo PropagateControl object

	:return: None or the new watch
	:rtype: None or int

	"""
	for possible_watch in lits:
		if possible_watch != current_watch:
			if control.assignment.value(possible_watch) is None and not control.has_watch(possible_watch):
				return possible_watch

	return None


def get_replacement_watch(nogood: List[int], lit: int, control) -> Optional[List[int]]:
	"""
	choose a new watch for the given assigned time if possible
	:param int nogood: the nogood
	:param int lit: the current literal being propagated
	:param control: A clingo PropagateControl object

	if a new watch can be found:
	:return: old_watch: int, new_watch: int, assigned_time: int

	if no new watch is found:
	:returns None
	"""

	new_watch: Optional[int] = choose_lit(nogood, lit, control)
	if new_watch is not None:
		return [lit, new_watch]

	return None


class TheoryConstraint2watch(TheoryConstraint):
	"""
	Members:

	watches_to_at           --  Dictionary mapping the current watches to
								their respective assigned time(s)
	"""

	__slots__ = ["watches_to_at"]

	def __init__(self, constraint) -> None:
		super().__init__(constraint)
		self.logger = logging.getLogger(self.__module__ + "." + self.__class__.__name__)
		self.watches_to_at: Dict[int, Set[int]] = defaultdict(set)

	def build_watches(self, init) -> List[int]:
		"""
		Only add watches for the first 2 literals of a nogood
		"""
		watches = set()
		for assigned_time in range(self.min_time, self.max_time + 1):
			lits = form_nogood(self.t_atom_info, assigned_time)
			if lits is None:
				continue
			for lit in lits[:2]:
				self.watches_to_at[lit].add(assigned_time)
				init.add_watch(lit)
				watches.add(lit)

		return watches

	# @profile
	@util.Count("Propagation")
	def propagate(self, control, changes) -> Optional[List[Tuple]]:
		"""
		For any relevant change, check the assignment of the whole nogood
		for the assigned times it is in. If it it conflicting or unit add the nogood to the solver

		After the check, replace the watch if possible.

		:param control: clingo PropagateControl object
		:param changes: list of watches that were assigned
		:return None if propagation has to stop, A list of (delete, add) pairs of watches if propagation can continue
		"""
		with util.Timer("Propagation"):

			delete_add = []

			replacement_info: List[List[int]] = []
			if type(changes) == int:
				changes = [changes]

			for lit in changes:
				for assigned_time in self.watches_to_at[lit]:
					ng = form_nogood(self.t_atom_info, assigned_time)
					if ng is None:
						continue

					update_result = check_assignment(ng, control)

					if update_result == CONSTRAINT_CHECK["CONFLICT"] or update_result == CONSTRAINT_CHECK["UNIT"]:
						if not control.add_nogood(ng) or not control.propagate():
							return None

					info = get_replacement_watch(ng, lit, control)
					if info is not None:
						delete_add.append(info)
						replacement_info.append(info + [assigned_time])

			self.replace_watches(replacement_info, control)

			return delete_add

	def replace_watches(self, info: List[List[int]], control) -> None:
		"""
		Update the watches_to_at dictionary based on the info returned by get_replacement_watch
		Also, add the new watch to the solver and remove the old watch if necessary

		:param info: List of info about the replacement. Each element is a return type of get_replacement_watch
		:param control: clingo PropagateControl object
		"""

		for old_watch, new_watch, assigned_time in info:
			# remove the lit as a watch for constraint assigned_time
			self.watches_to_at[old_watch].remove(assigned_time)

			# add new watch as a watch for constraint assigned_time
			self.watches_to_at[new_watch].add(assigned_time)

			if not control.has_watch(new_watch):
				control.add_watch(new_watch)

			# if lit is not watching a constraint eliminate it
			if len(self.watches_to_at[old_watch]) == 0:
				control.remove_watch(old_watch)


class TheoryConstraint2watchForProp(TheoryConstraint2watch):
	__slots__ = []

	def replace_watches(self, info: List[List[int]], control) -> None:
		"""
		Update the watches_to_at dictionary based on the info returned by get_replacement_watch
		control parameter is only there for compatibility

		:param info: List of info about the replacement. Each element is a return type of get_replacement_watch
		:param control: clingo PropagateControl object
		"""

		for old_watch, new_watch, assigned_time in info:
			# remove the lit as a watch for constraint assigned_time
			self.watches_to_at[old_watch].remove(assigned_time)

			# add new watch as a watch for constraint assigned_time
			self.watches_to_at[new_watch].add(assigned_time)


class TheoryConstraint2watchForPropMap(TheoryConstraint):
	__slots__ = []

	def __init__(self, constraint) -> None:
		super().__init__(constraint)
		self.logger = logging.getLogger(self.__module__ + "." + self.__class__.__name__)

	def build_watches(self, init) -> List[int]:
		"""
		Only add watches for the first 2 literals of a nogood
		"""
		watches = set()
		for assigned_time in range(self.min_time, self.max_time + 1):
			lits = form_nogood(self.t_atom_info, assigned_time)
			if lits is None:
				continue
			for lit in lits[:2]:
				init.add_watch(lit)
				watches.add((lit, assigned_time))

		return watches

	def propagate(self, control, change) -> Optional[List[Tuple]]:
		"""
		For any relevant change, check the assignment of the whole nogood
		for the assigned times it is in. If it it conflicting or unit add the nogood to the solver

		After the check, replace the watch if possible.

		:param control: clingo PropagateControl object
		:param change: watch and assigned time pair
		:return None if propagation has to stop, A list of (delete, add) pairs of watches if propagation can continue
		"""
		with util.Timer("Propagation"):

			delete_add = []

			lit, assigned_time = change
			ng = form_nogood(self.t_atom_info, assigned_time)
			if ng is None:
				return []

			update_result = check_assignment(ng, control)

			if update_result == CONSTRAINT_CHECK["CONFLICT"] or update_result == CONSTRAINT_CHECK["UNIT"]:
				if not control.add_nogood(ng) or not control.propagate():
					return None

			info = get_replacement_watch(ng, lit, control)
			if info is not None:
				delete_add.append(info)

			return delete_add


class TheoryConstraintSize2Timed(TheoryConstraint):
	__slots__ = []

	def __init__(self, constraint) -> None:
		super().__init__(constraint)
		self.logger = logging.getLogger(self.__module__ + "." + self.__class__.__name__)

	def build_watches(self, init) -> None:
		"""
		add all solver literals for the constraint as watches
		"""
		for assigned_time in range(self.min_time, self.max_time + 1):
			lits = form_nogood(self.t_atom_info, assigned_time)
			if lits is None:
				continue
			for lit in lits:
				init.add_watch(lit)

	@util.Count("Propagation")
	def propagate(self, control, change) -> Optional[List[Tuple]]:
		"""
		look for assigned times of the change and add the nogoods of those times to
		the solver

		:param control: clingo PropagateControl object
		:param change: tuple containing the info of the change. Tuple[sign, name, time]
		:return None if propagation has to stop, A list of (delete, add) pairs of watches if propagation can continue
		"""

		ats = get_at_from_name_id(change, self.t_atom_info)

		for assigned_time in ats:
			ng = form_nogood(self.t_atom_info, assigned_time)
			if ng is None:
				continue

			if not control.add_nogood(ng) or not control.propagate():
				return None

		return []


class TheoryConstraintNaiveTimed(TheoryConstraint):
	__slots__ = []

	def __init__(self, constraint) -> None:
		super().__init__(constraint)
		self.logger = logging.getLogger(self.__module__ + "." + self.__class__.__name__)

	def build_watches(self, init) -> None:
		"""
		add all solver literals for the constraint as watches
		"""
		for assigned_time in range(self.min_time, self.max_time + 1):
			lits = form_nogood(self.t_atom_info, assigned_time)
			if lits is None:
				continue
			for lit in lits:
				init.add_watch(lit)

	@util.Count("Propagation")
	def propagate(self, control, change) -> Optional[List[Tuple]]:
		"""
		:param control: clingo PropagateControl object
		:param change: literal that was assigned
		:return None if propagation has to stop, A list of (delete, add) pairs of watches if propagation can continue
		"""

		ats = get_at_from_name_id(change, self.t_atom_info)

		for assigned_time in ats:
			ng = form_nogood(self.t_atom_info, assigned_time)
			if ng is None:
				continue

			update_result = check_assignment(ng, control)

			if update_result == CONSTRAINT_CHECK["CONFLICT"] or update_result == CONSTRAINT_CHECK["UNIT"]:
				if not control.add_nogood(ng) or not control.propagate():
					return None

		return []
