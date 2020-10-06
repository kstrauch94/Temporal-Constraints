import logging
from collections import defaultdict
import clingo

from typing import List, Dict, Tuple, Set, Any, Optional

import untimed.util as util

CONSTRAINT_CHECK = {"NONE": 0,
                    "UNIT": 1,
                    "CONFLICT": -1}


class PropagationError(Exception):
	pass


class Map_Name_Lit:
	"""
	Maps a name id to a solver literal.
	Has helper methods to retrieve either a literal or a name id

	name_id is a Tuple[sign, name, time]
	"""
	name_to_lit: Dict[Tuple[int, str, int], int] = {}

	lit_to_name: Dict[int, Set[str]] = defaultdict(set)

	@classmethod
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


def parse_atoms(constraint) -> Tuple[Dict[str, Dict[str, Any]], int, int]:
	"""
	Extract the relevant information of the given theory atom and populate self.t_atom_info

	:param constraint: clingo TheoryAtom
	"""
	t_atom_info: Dict[str, Dict[str, Any]] = {}

	min_time, max_time = parse_constraint_times(constraint.term.arguments)
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

		t_atom_info[uq_name] = {"sign": sign,
		                        "time_mod": time_mod,
		                        "signature": signature,
		                        "args": [clingo.parse_term(str(a)) for a in atom.terms[0].arguments[0].arguments],
		                        "name": name}

	return t_atom_info, min_time, max_time


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
	Builds the name_id for Map_Name_Lit

	:param info: Information dictionary for a particular atom
	:param time: The time point
	:return: A name_id Triple
	"""
	return info["sign"], info["name"], time


def parse_time(s_atom) -> int:
	"""
	Parses the time point of the given atom
	:param s_atom: clingo symbolic atom
	:return: time
	"""
	time = str(s_atom.symbol).split(",")[-1].replace(")", "").strip()
	return int(time)


def get_assigned_time(info: Dict[str, Any], time: int) -> int:
	"""
	Calculates the assigned time based on the real time point

	:param info: Information dictionary for a particular atom
	:param time: The time point
	:return: assigned time
	"""
	return time + info["time_mod"]


def reverse_assigned_time(info: Dict[str, Any], assigned_time: int) -> int:
	"""
	Calculates the real time point based on the assigned time

	:param info: Information dictionary for a particular atom
	:param assigned_time: The assigned time
	:return: time
	"""
	return assigned_time - info["time_mod"]


def form_nogood(t_atom_info, assigned_time: int) -> Optional[List[int]]:
	"""
	Forms a nogood based on the assigned time and atoms of a theoryconstraint

	:param t_atom_info: Complete information dictionary of the theory constraint
	:param assigned_time: the assigned time
	:return: the nogood for the given assigned time and constraint
	"""

	ng: Set[int] = set()

	try:
		for uq_name in t_atom_info.keys():
			time: int = reverse_assigned_time(t_atom_info[uq_name], assigned_time)
			ng.add(Map_Name_Lit.grab_lit(build_symbol_id(t_atom_info[uq_name], time)))
	except KeyError:
		# this error would happen is an id is not in the mapping
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


def get_at_from_name_id(name_id: Tuple[int, str, int], t_atom_info):
	sign, name, time = name_id

	ats = set()
	for uq_name, info in t_atom_info.items():
		if info["sign"] == sign and info["name"] == name:
			ats.add(get_assigned_time(info, time))

	return ats


class TheoryConstraint:
	"""
	Base class for all theory constraints.

	Members:
	t_atom_info             -- Dictionary that holds relevant information
								for all atoms in the constraint

	max_time                -- Max time of the theory constraint

	min_time                -- Min time of the theory constraint

	"""

	__slots__ = ["t_atom_info", "max_time", "min_time", "logger"]

	def __init__(self, constraint) -> None:

		self.t_atom_info: Dict[str, Dict[str, Any]] = {}

		self.max_time: int = None
		self.min_time: int = None

		self.t_atom_info, self.min_time, self.max_time = parse_atoms(constraint)

	@property
	def t_atom_names(self):
		return self.t_atom_info.keys()

	@property
	def size(self) -> int:
		return len(self.t_atom_names)

	@util.Timer("Init")
	def init(self, init) -> None:
		self.init_mappings(init)
		self.build_watches(init)

	def init_mappings(self, init) -> None:
		"""
		Loop through the symbolic atoms matching the signatures of the atoms in the theory constraint.
		If a match is found, we add it to Map_Name_Lit

		:param init: clingo PropagateInit class
		"""
		for uq_name, info in self.t_atom_info.items():
			for s_atom in init.symbolic_atoms.by_signature(*info["signature"]):
				if s_atom.symbol.arguments[:-1] == info["args"]:
					time: int = parse_time(s_atom)
					assigned_time: int = get_assigned_time(self.t_atom_info[uq_name], time)

					# max time and min time can not be none! add some detection just in case?
					if self.max_time is not None and assigned_time > self.max_time:
						self.logger.debug("no watch for lit cause assigned time would be too big: %s", s_atom.symbol)
						continue

					elif self.min_time is not None and assigned_time < self.min_time:
						self.logger.debug("no watch for lit cause assigned time would be too small: %s", s_atom.symbol)
						continue

					solver_lit: int = init.solver_literal(s_atom.literal) * self.t_atom_info[uq_name]["sign"]

					Map_Name_Lit.add(build_symbol_id(self.t_atom_info[uq_name], time), solver_lit)

	def build_watches(self, init):
		"""
		Add watches to the solver. This should be implemented by child class
		:param init: clingo PropagateInit class
		"""
		pass

	@util.Timer("Undo")
	@util.Count("Undo")
	def undo(self, thread_id, assign, changes) -> None:
		pass

	def propagate(self, control, changes) -> None:
		pass


class TheoryConstraintSize1(TheoryConstraint):

	def __init__(self, constraint) -> None:
		super().__init__(constraint)
		self.logger = logging.getLogger(self.__module__ + "." + self.__class__.__name__)

	def init_mappings(self, init) -> None:
		"""
		Instead of adding to Map_Name_Lit it immediately adds a clause for the nogood
		"""
		for uq_name, info in self.t_atom_info.items():
			for s_atom in init.symbolic_atoms.by_signature(*info["signature"]):
				if s_atom.symbol.arguments[:-1] == info["args"]:
					time: int = parse_time(s_atom)
					assigned_time: int = get_assigned_time(self.t_atom_info[uq_name], time)

					# max time and min time can not be none! add some detection just in case?
					if self.max_time is not None and assigned_time > self.max_time:
						self.logger.debug("no watch for lit cause assigned time would be too big: %s", s_atom.symbol)
						continue

					elif self.min_time is not None and assigned_time < self.min_time:
						self.logger.debug("no watch for lit cause assigned time would be too small: %s", s_atom.symbol)
						continue

					solver_lit: int = init.solver_literal(s_atom.literal) * self.t_atom_info[uq_name]["sign"]

					# add nogood
					init.add_clause([-solver_lit])


class TheoryConstraintRegularWatch(TheoryConstraint):
	"""
	Parent class of Theory constraints that will Implement propagation
	using solver literals. This class only adds the members below.

	Members:

	watches_to_at           --  Dictionary mapping the current watches to
								their respective assigned time(s)
	"""

	__slots__ = ["watches_to_at"]

	def __init__(self, constraint) -> None:
		super().__init__(constraint)
		self.watches_to_at: Dict[int, Set[int]] = defaultdict(set)


class TheoryConstraintSize2(TheoryConstraint):

	def __init__(self, constraint) -> None:
		super().__init__(constraint)
		self.logger = logging.getLogger(self.__module__ + "." + self.__class__.__name__)

	def build_watches(self, init) -> None:
		"""
		Since there are only 2 atoms in the constraint we add all literals as watches
		"""
		for assigned_time in range(self.min_time, self.max_time + 1):
			lits = form_nogood(self.t_atom_info, assigned_time)
			if lits is None:
				continue
			for lit in lits:
				init.add_watch(lit)

	@util.Count("Propagation")
	def propagate(self, control, changes) -> None:
		"""
		For any relevant change, immediately form the nogood
		for the assigned times it is in and add it to the solver

		:param control: clingo PropagateControl class
		:param changes: list of watches that were assigned
		"""
		with util.Timer("Propagation"):

			for lit in changes:
				ats = set()
				for name_id in Map_Name_Lit.grab_name(lit):
					ats.update(get_at_from_name_id(name_id, self.t_atom_info))

				for assigned_time in ats:
					ng = form_nogood(self.t_atom_info, assigned_time)
					if ng is None:
						continue
					if not control.add_nogood(ng) or not control.propagate():
						return

			return


class TheoryConstraintNaive(TheoryConstraint):

	def __init__(self, constraint) -> None:
		super().__init__(constraint)
		self.logger = logging.getLogger(self.__module__ + "." + self.__class__.__name__)

	def build_watches(self, init) -> None:
		"""
		For a naive treatment of watches, we simply
		add all solver literals for the constraint as watches
		"""
		for assigned_time in range(self.min_time, self.max_time + 1):
			lits = form_nogood(self.t_atom_info, assigned_time)
			if lits is None:
				continue
			for lit in lits:
				init.add_watch(lit)

	@util.Count("Propagation")
	def propagate(self, control, changes) -> None:
		"""
		For any relevant change, check the assignment of the whole nogood
		for the assigned times it is in. If it it conflicting or unit add the nogood to the solver

		:param control: clingo PropagateControl class
		:param changes: list of watches that were assigned
		:return 0 if propagation has to stop, 1 if propagation can continue
		"""

		with util.Timer("Propagation"):

			for lit in changes:
				ats = set()
				for name_id in Map_Name_Lit.grab_name(lit):
					ats.update(get_at_from_name_id(name_id, self.t_atom_info))

				for assigned_time in ats:
					ng = form_nogood(self.t_atom_info, assigned_time)
					if ng is None:
						continue

					update_result = check_assignment(ng, control)

					if update_result == CONSTRAINT_CHECK["CONFLICT"] or update_result == CONSTRAINT_CHECK["UNIT"]:
						if not control.add_nogood(ng) or not control.propagate():
							return

			return


def choose_lit(lits: List[int], current_watch: int, control) -> Optional[int]:
	"""
	Checks the literals for a nogood and check for new watches

	:param lits: the current nogood
	:param current_watch: the watch being propagated
	:param  control: A clingo PropagateControl object for the current solver thread

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
	:param PropagateControl control: A clingo PropagateControl object for the current solver thread

	if a new watch can be found:
	:return: old_watch: int, new_watch: int, assigned_time: int

	if no new watch is found:
	:returns None
	"""

	new_watch: Optional[int] = choose_lit(nogood, lit, control)
	if new_watch is not None:
		return [lit, new_watch]

	return None


class TheoryConstraint2watch(TheoryConstraintRegularWatch):
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

	def build_watches(self, init) -> None:
		"""
		Only add watches for the first 2 literals of a nogood
		"""
		for assigned_time in range(self.min_time, self.max_time + 1):
			lits = form_nogood(self.t_atom_info, assigned_time)
			if lits is None:
				continue
			for lit in lits[:2]:
				self.watches_to_at[lit].add(assigned_time)
				init.add_watch(lit)

	# @profile
	@util.Count("Propagation")
	def propagate(self, control, changes) -> None:
		"""
		For any relevant change, check the assignment of the whole nogood
		for the assigned times it is in. If it it conflicting or unit add the nogood to the solver

		After the check, replace the watch if possible.

		:param control: clingo PropagateControl class
		:param changes: list of watches that were assigned
		:return 0 if propagation has to stop, 1 if propagation can continue
		"""
		with util.Timer("Propagation"):

			replacement_info: List[List[int]] = []
			for lit in changes:
				for assigned_time in self.watches_to_at[lit]:
					ng = form_nogood(self.t_atom_info, assigned_time)
					if ng is None:
						continue

					update_result = check_assignment(ng, control)

					if update_result == CONSTRAINT_CHECK["CONFLICT"] or update_result == CONSTRAINT_CHECK["UNIT"]:
						if not control.add_nogood(ng) or not control.propagate():
							return

					info = get_replacement_watch(ng, lit, control)
					if info is not None:
						replacement_info.append(info + [assigned_time])

			self.replace_watches(replacement_info, control)

			return

	def replace_watches(self, info: List[List[int]], control) -> None:
		"""
		Update the watches_to_at dictionary based on the info returned by get_replacement_watch
		Also, add the new watch to the solver and remove the old watch if necessary

		:param info: List of info about the replacement. Each element is a return type of get_replacement_watch
		:param control: clingo PropagateControl
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


class TimedAtomPropagator:
	"""
	Propagator that handles the propagation of "time atoms"(aka theory atoms of theory constraints).

	Members:
	t_atom_to_tc                -- Mapping from a "time atom" to a theoryconstraint.

	theory_constraints          -- List of all theory constraints
	"""
	__slots__ = ["t_atom_to_tc", "theory_constraints"]

	def __init__(self):
		self.t_atom_to_tc: Dict[Tuple[int, str], Set["TheoryConstraint"]] = defaultdict(set)

		self.theory_constraints: List["TheoryConstraint"] = []

	def add_tc(self, tc):
		self.theory_constraints.append(tc)

	def add_atom_observer(self, tc):
		"""
		Add the tc to the list of tcs to be notified when their respective atoms are propagated
		:param tc: theory constraint for timed watches
		"""
		if tc.size == 1:
			return

		for uq_name, info in tc.t_atom_info.items():
			self.t_atom_to_tc[info["sign"], info["name"]].add(tc)

	def init(self, init):
		for tc in self.theory_constraints:
			tc.init(init)
			self.add_atom_observer(tc)

	@util.Timer("Propagation")
	def propagate(self, control, changes):
		for lit in changes:
			for sign, name, time in Map_Name_Lit.grab_name(lit):
				for tc in self.t_atom_to_tc[sign, name]:
					if not tc.propagate(control, (sign, name, time)):
						return


class TheoryConstraintSize2Timed(TheoryConstraint):

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
	def propagate(self, control, change) -> int:
		"""
		look for assigned times of the change and add the nogoods of those times to
		the solver

		:param control: clingo PropagateControl class
		:param change: tuple containing the info of the change. Tuple[sign, name, time]
		:return 0 if propagation has to stop, 1 if propagation can continue
		"""

		ats = get_at_from_name_id(change, self.t_atom_info)

		for assigned_time in ats:
			ng = form_nogood(self.t_atom_info, assigned_time)
			if ng is None:
				continue

			if not control.add_nogood(ng) or not control.propagate():
				return 0

		return 1


class TheoryConstraintNaiveTimed(TheoryConstraint):

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
	def propagate(self, control, change) -> int:
		"""
		:param control:
		:param change:
		:return 0 if propagation has to stop, 1 if propagation can continue
		"""

		ats = get_at_from_name_id(change, self.t_atom_info)

		for assigned_time in ats:
			ng = form_nogood(self.t_atom_info, assigned_time)
			if ng is None:
				continue

			update_result = check_assignment(ng, control)

			if update_result == CONSTRAINT_CHECK["CONFLICT"] or update_result == CONSTRAINT_CHECK["UNIT"]:
				if not control.add_nogood(ng) or not control.propagate():
					return 0

		return 1
