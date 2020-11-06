import logging

from typing import List, Dict, Tuple, Set, Any, Optional

import untimed.util as util

from untimed.propagator.theoryconstraint_data import atom_info
from untimed.propagator.theoryconstraint_data import TimeAtomToSolverLit
from untimed.propagator.theoryconstraint_data import Signatures
from untimed.propagator.theoryconstraint_data import Looked
from untimed.propagator.theoryconstraint_data import CONSTRAINT_CHECK


@util.Timer("parse_atom")
# @profile
def parse_atoms(constraint) -> Tuple[Dict[str, atom_info], int, int, Set[Tuple[str, int]]]:
	"""
	Extract the relevant information of the given theory atom and populate self.t_atom_info

	:param constraint: clingo TheoryAtom
	"""
	t_atom_info: Dict[str, atom_info] = {}

	min_time, max_time = parse_constraint_times(constraint.term.arguments)

	for atom in constraint.elements:
		# this gives me the "type" of the term | e.g. for +~on(..) it would return +~
		term_type: str = atom.terms[0].name

		signature: Tuple[str, int] = (
			atom.terms[0].arguments[0].name, len(atom.terms[0].arguments[0].arguments) + 1)

		Signatures.sigs.add(signature)

		# after selecting the atom we convert it to a string and delete the parenthesis
		name: str = str(atom.terms[0].arguments[0])[:-1]

		# after selecting the atom we further select its arguments
		# if the length is 0 we don't add a ","
		# if it is longer then we add "," for ease of use later on
		if len(atom.terms[0].arguments[0].arguments) != 0:
			name = f"{name},"

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


# @profile
def form_nogood(t_atom_info, assigned_time: int) -> Optional[List[int]]:
	"""
	Forms a nogood based on the assigned time and atoms of a theory constraint

	:param t_atom_info: Complete information dictionary of the theory constraint
	:param assigned_time: the assigned time
	:return: the nogood for the given assigned time and constraint
	"""
	tup = tuple(t_atom_info.keys())
	if (tup, assigned_time) in Looked.looked:
		return Looked.looked[tup, assigned_time]

	ng: List[int] = []

	try:
		for uq_name in t_atom_info.keys():
			time: int = reverse_assigned_time(t_atom_info[uq_name], assigned_time)
			ng.append(TimeAtomToSolverLit.grab_lit(build_symbol_id(t_atom_info[uq_name], time)))
	except KeyError:
		# this error would happen if an id is not in the mapping
		# if this happens it means the nogood does not exist for this assigned time
		Looked.looked[tup, assigned_time] = None
		return None

	Looked.looked[tup, assigned_time] = ng
	return ng


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


def init_TA2L_mapping(init):
	for sig in Signatures.sigs:
		for s_atom in init.symbolic_atoms.by_signature(*sig):
			time = parse_time(s_atom)
			# if argument size is 1 then only time is present
			if len(s_atom.symbol.arguments) == 1:
				name: str = f"{s_atom.symbol.name}("
			else:
				name: str = str(s_atom.symbol).split(",")[:-1]
				name = "".join(name)
				name = f"{name},"

			lit = init.solver_literal(s_atom.literal)
			TimeAtomToSolverLit.add((-1, name, time), -lit)
			TimeAtomToSolverLit.add((1, name, time), lit)


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
		self.logger = logging.getLogger(self.__module__ + "." + self.__class__.__name__)

		self.t_atom_info: Dict[str, atom_info] = {}

		self.max_time: int = None
		self.min_time: int = None

		self.t_atom_info, self.min_time, self.max_time = parse_atoms(constraint)

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
		return self.build_watches(init)

	def init_mappings(self, init) -> None:
		"""
		This is only used when there are many propagators
		Initializes the TimeAtomToSolverLit mapping ONCE
		then on every subsequent init call from all other theoryconstraints it does nothing

		:param init: clingo PropagateInit class
		"""
		if not Signatures.finished:
			init_TA2L_mapping(init)

			Signatures.finished = True

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

	@util.Timer("check")
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

	def init(self, init):
		if not TimeAtomToSolverLit.initialized:
			init_TA2L_mapping(init)

		self.init_mappings(init)

	def init_mappings(self, init) -> None:
		"""
		Instead of adding to TimeAtomToSolverLit it immediately adds a clause for the nogood
		"""
		for uq_name, info in self.t_atom_info.items():
			for assigned_time in range(self.min_time, self.max_time + 1):
				try:
					solver_lit = TimeAtomToSolverLit.grab_lit((info.sign, info.name, assigned_time - info.time_mod))
				except KeyError:
					continue

				# add nogood
				init.add_clause([-solver_lit])

			self.t_atom_info[uq_name] = False

	def check(self, *args, **kwargs):
		return 0
