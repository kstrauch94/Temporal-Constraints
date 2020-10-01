import logging
from collections import defaultdict
import clingo

from typing import List, Dict, Tuple, Set, Callable, Any, Optional

CONSTRAINT_CHECK = {"NONE": 0,
                    "UNIT": 1,
                    "CONFLICT": -1}


class PropagationError(Exception):
	pass


class Map_Name_Lit:
	"""
	Maps a name id to a solver literal.
	Has helper methods to retrieve either a literal or a name id
	"""
	name_to_lit: Dict[Tuple[int, str, int], int] = {}
	#lit_to_name: Dict[int, Set[str]] = defaultdict(set)

	@classmethod
	def add(cls, name_id, lit):
		if name_id not in cls.name_to_lit:
			cls.name_to_lit[name_id] = lit

		#cls.lit_to_name[lit].add(name_id)

	@classmethod
	def grab_lit(cls, name_id):
		return cls.name_to_lit[name_id]

#	@classmethod
#	def grab_name(cls, lit):
#		return cls.lit_to_name[lit]

	@classmethod
	def has_name(cls, name_id):
		return name_id in cls.name_to_lit


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


def form_nogood(t_atom_info, assigned_time: int, existing_at) -> List[int]:
	"""
	Forms a nogood based on the assigned time and atoms of a theoryconstraint

	:param t_atom_info: Complete information dictionary of the theory constraint
	:param assigned_time: the assigned time
	:param existing_at: list of valid assigned times
	:return: the nogood for the given assigned time and constraint
	"""
	if assigned_time not in existing_at:
		return []

	ng: Set[int] = set()

	for uq_name in t_atom_info.keys():
		time: int = reverse_assigned_time(t_atom_info[uq_name], assigned_time)
		ng.add(Map_Name_Lit.grab_lit(build_symbol_id(t_atom_info[uq_name], time)))

	return list(ng)


class TheoryConstraint:
	"""
	Base class for all theory constraints.

	Members:
	t_atom_info             -- Dictionary that holds relevant information
	                           for all atoms in the constraint

	watches_to_at           -- Dictionary mapping the current watches to
							   their respective assigned time(s)

	max_time                -- Max time of the theory constraint

	min_time                -- Min time of the theory constraint

	existing_at             -- List of the valid assigned times

	"""

	def __init__(self, constraint):

		self.t_atom_info: Dict[str, Dict[str, Any]] = {}

		self.watches_to_at: Dict[int, Set[int]] = defaultdict(set)
		self.at_size: Dict[int, int] = defaultdict(lambda: 0)

		self.max_time: int = None
		self.min_time: int = None

		self.existing_at: List[int] = []

		self.parse_atoms(constraint)

	@property
	def t_atom_names(self):
		return self.t_atom_info.keys()

	@property
	def watches(self):
		return self.watches_to_at.keys()

	def parse_atoms(self, constraint) -> None:
		"""
		Extract the relevant information of the given theory atom and populate self.t_atom_info

		:param constraint: clingo TheoryAtom
		"""
		self.parse_constraint_times(constraint.term.arguments)
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

			self.t_atom_info[uq_name] = {"sign": sign,
			                             "time_mod": time_mod,
			                             "signature": signature,
			                             "args": [clingo.parse_term(str(a)) for a in atom.terms[0].arguments[0].arguments],
			                             "name": name}

	def parse_constraint_times(self, times):
		"""
		Get the minimum and maximum time from the theory atom

		:param times: List of theory atom arguments
		"""
		if len(times) == 1:
			self.max_time = times[0].number
			self.min_time = 0
		else:
			self.max_time = times[1].number
			self.min_time = times[0].number

	def init(self, init, propagate: bool = False) -> None:
		self.init_watches(init)
		self.propagate_init(init, propagate)
		self.build_watches(init)

	def init_watches(self, init) -> None:
		"""
		Name is somewhat misleading!
		Loop through the symbolic atoms matching the signatures of the atoms in the theory constraint.
		If a match is found, we add it to Map_Name_Lit and update self.at_size and self.existing_at

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

					self.at_size[assigned_time] += 1
					if assigned_time not in self.existing_at:
						self.existing_at.append(assigned_time)

					Map_Name_Lit.add(build_symbol_id(self.t_atom_info[uq_name], time), solver_lit)

	def propagate_init(self, init, propagate: bool = False) -> None:
		"""
		We find out which assigned times are not valid.
		If the assigned time is valid and propagate is True we check all nogoods of the theoryconstraint
		for conflicts or unit and deal with them accordingly

		:param init: clingo PropagateInit class
		:param propagate: Flag that enables checking for conflicts/units
		"""
		invalid_at = []
		for assigned_time in self.existing_at:
			if self.at_size[assigned_time] < self.size:
				# if this happens, it could be because for one
				# of the names in the constraint for a particular
				# assigned time there was no symbolic atom for it
				# this means that the atom does not exist
				# hence, it is false and the nogood is useless
				# so we delete it
				invalid_at.append(assigned_time)
				continue

			if not propagate:
				# if we don't want propagate no init then just continue and check the next assigned time
				# for a nogood that is always false
				continue

			ng = form_nogood(self.t_atom_info, assigned_time, self.existing_at)
			result = self.check_assignment(ng, init)
			if result == CONSTRAINT_CHECK["CONFLICT"]:
				init.add_clause([-lit for lit in ng])

			elif result == CONSTRAINT_CHECK["UNIT"]:
				# if nogood is already unit at init
				# then we can add the clause so it propagates at time 0
				# then we delete assigned time because
				# it will never pop up again
				init.add_clause([-lit for lit in ng])
				invalid_at.append(assigned_time)

		for iat in invalid_at:
			self.existing_at.remove(iat)

	def check_assignment(self, nogood, control) -> int:
		"""
		Checks if a nogood is a conflict or unit in the current assignment

		:param nogood: nogood that will be checked
		:param control: clingo PropagateControl class
		:return int value that denotes the result of the check. See CONSTRAINT_CHECK for details
		"""
		ng: List[int] = []
		true_count: int = 0

		for lit in nogood:

			if control.assignment.is_true(lit):
				# if its true
				ng.append(lit)
				true_count += 1
			elif control.assignment.is_false(lit):
				# if one is false then it doesnt matter
				return CONSTRAINT_CHECK["NONE"]

		if true_count == self.size:
			return CONSTRAINT_CHECK["CONFLICT"]
		elif true_count == self.size - 1:
			return CONSTRAINT_CHECK["UNIT"]
		else:
			return CONSTRAINT_CHECK["NONE"]

	def build_watches(self, init):
		"""
		Add watches to the solver. This should be implement by child class
		:param init: clingo PropagateInit class
		"""
		pass

	def undo(self, thread_id, assign, changes) -> None:
		pass

	def propagate(self, control, changes):
		pass

	@property
	def size(self) -> int:
		return len(self.t_atom_names)


class TheoryConstraintSize1(TheoryConstraint):

	def __init__(self, constraint) -> None:
		super().__init__(constraint)
		self.logger = logging.getLogger(self.__module__ + "." + self.__class__.__name__)

	def propagate_init(self, init, propagate: bool = False) -> None:
		"""
		overwriting parent class method so it does nothing when called
		"""
		pass

	def init_watches(self, init) -> None:
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


class TheoryConstraintSize2(TheoryConstraint):

	def __init__(self, constraint) -> None:
		super().__init__(constraint)
		self.logger = logging.getLogger(self.__module__ + "." + self.__class__.__name__)

	def build_watches(self, init) -> None:
		"""
		Since there are only 2 atoms in the constraint we add all literals as watches
		"""
		for assigned_time in self.existing_at:
			lits = form_nogood(self.t_atom_info, assigned_time, self.existing_at)
			for lit in lits:
				init.add_watch(lit)
				self.watches_to_at[lit].add(assigned_time)

	def propagate(self, control, changes) -> None:
		"""
		For any relevant change, immediately form the nogood
		for the assigned times it is in and add it to the solver

		:param control: clingo PropagateControl class
		:param changes: list of watches that were assigned
		"""
		for lit in changes:
			if lit in self.watches_to_at:
				for assigned_time in self.watches_to_at[lit]:
					ng = form_nogood(self.t_atom_info, assigned_time, self.existing_at)

					if not control.add_nogood(ng) or not control.propagate():
						return 0

		return 1


class TheoryConstraintNaive(TheoryConstraint):

	def __init__(self, constraint) -> None:
		super().__init__(constraint)
		self.logger = logging.getLogger(self.__module__ + "." + self.__class__.__name__)

	def build_watches(self, init) -> None:
		"""
		For a naive treatment of watches, we simply
		add all solver literals for the constraint as watches
		"""
		for assigned_time in self.existing_at:
			lits = form_nogood(self.t_atom_info, assigned_time, self.existing_at)
			for lit in lits:
				init.add_watch(lit)
				self.watches_to_at[lit].add(assigned_time)

	def propagate(self, control, changes) -> None:
		"""
		For any relevant change, check the assignment of the whole nogood
		for the assigned times it is in. If it it conflicting or unit add the nogood to the solver

		:param control: clingo PropagateControl class
		:param changes: list of watches that were assigned
		:return 0 if propagation has to stop, 1 if propagation can continue
		"""
		for lit in changes:
			if lit in self.watches_to_at:
				for assigned_time in self.watches_to_at[lit]:
					ng = form_nogood(self.t_atom_info, assigned_time, self.existing_at)
					update_result = self.check_assignment(ng, control)

					if update_result == CONSTRAINT_CHECK["CONFLICT"] or update_result == CONSTRAINT_CHECK["UNIT"]:
						if not control.add_nogood(ng) or not control.propagate():
							return 0

		return 1


def choose_lit(lits: Set[int], current_watch: int, control) -> Optional[int]:
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


def get_replacement_watch(nogood: List[int], lit: int, control) -> Optional[Tuple[int, int]]:
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


class TheoryConstraint2watch(TheoryConstraint):

	def __init__(self, constraint):

		super().__init__(constraint)
		self.logger = logging.getLogger(self.__module__ + "." + self.__class__.__name__)

	def build_watches(self, init) -> None:
		"""
		Only add watches for the first 2 literals of a nogood
		"""
		for assigned_time in self.existing_at:
			lits = form_nogood(self.t_atom_info, assigned_time, self.existing_at)
			for lit in lits[:2]:
				self.watches_to_at[lit].add(assigned_time)
				init.add_watch(lit)

	# @profile
	def propagate(self, control, changes) -> None:
		"""
		For any relevant change, check the assignment of the whole nogood
		for the assigned times it is in. If it it conflicting or unit add the nogood to the solver

		After the check, replace the watch if possible.

		Finally, add all unit constraints to the solver.

		:param control: clingo PropagateControl class
		:param changes: list of watches that were assigned
		:return 0 if propagation has to stop, 1 if propagation can continue
		"""
		replacement_info: List[Tuple[int, int, int]] = []
		for lit in changes:
			if lit in self.watches_to_at:
				for assigned_time in self.watches_to_at[lit]:
					ng = form_nogood(self.t_atom_info, assigned_time, self.existing_at)
					update_result = self.check_assignment(ng, control)

					if update_result == CONSTRAINT_CHECK["CONFLICT"] or update_result == CONSTRAINT_CHECK["UNIT"]:
						if not control.add_nogood(ng) or not control.propagate():
							return 0

					info = get_replacement_watch(ng, lit, control)
					if info is not None:
						replacement_info.append(info + [assigned_time])

		self.replace_watches(replacement_info, control)

		return 1

	def replace_watches(self, info: List[Tuple[int, int, int]], control) -> None:
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
