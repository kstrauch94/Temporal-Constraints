import logging

from typing import List, Dict, Tuple, Set, Any, Optional

import untimed.util as util

from untimed.propagator.theoryconstraint_data import atom_info
from untimed.propagator.theoryconstraint_data import TimeAtomToSolverLit
from untimed.propagator.theoryconstraint_data import Signatures
from untimed.propagator.theoryconstraint_data import CONSTRAINT_CHECK

import clingo

@util.Timer("parse_atom")
# @profile
def parse_atoms(constraint) -> Tuple[Dict[str, atom_info], int, int, Set[Tuple[str, int]]]:
	"""
	Extract the relevant information of the given theory atom and populate self.t_atom_info

	:param constraint: clingo TheoryAtom
	"""
	t_atom_info: List[atom_info] = []

	min_time, max_time = parse_constraint_times(constraint.term.arguments)

	for atom in constraint.elements:
		# this gives me the "type" of the term | e.g. for +~on(..) it would return +~
		term_type: str = atom.terms[0].name

		"""	
		# after selecting the atom we convert it to a string and delete the parenthesis
		name: str = str(atom.terms[0].arguments[0])[:-1]

		# after selecting the atom we further select its arguments
		# if the length is 0 we don't add a ","
		# if it is longer then we add "," for ease of use later on
		if len(atom.terms[0].arguments[0].arguments) != 0:
			name = f"{name},"

		uq_name: str = term_type + name
		"""

		untimed_name = atom.terms[0].arguments[0].name
		untimed_args = tuple(atom.terms[0].arguments[0].arguments)

		untimed_lit = Signatures.fullsigs_term[untimed_name, untimed_args]

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

		t_atom_info.append(atom_info(sign=sign, time_mod=time_mod, untimed_lit=untimed_lit * sign))

	return t_atom_info, min_time, max_time


def parse_signature(constraint):
	"""
	Extract the relevant information of the given theory atom and populate self.t_atom_info

	:param constraint: clingo TheoryAtom
	"""
	for atom in constraint.elements:

		# this gives me the "type" of the term | e.g. for +~on(..) it would return +~
		term_type: str = atom.terms[0].name

		if "+" in term_type:
			sign = 1
		elif "-" in term_type:
			sign = -1

		signature: Tuple[str, int] = (
			atom.terms[0].arguments[0].name, len(atom.terms[0].arguments[0].arguments) + 1)

		Signatures.sigs.add((sign, signature))

		sig_tuple_term = (atom.terms[0].arguments[0].name, tuple(atom.terms[0].arguments[0].arguments))
		s_atom = clingo.parse_term(str(atom.terms[0].arguments[0]))
		sig_tuple = (s_atom.name, tuple(s_atom.arguments))

		Signatures.add_fullsig(sig_tuple, sig_tuple_term)


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
	Builds the untimed_lit for TimeAtomToSolverLit

	:param info: Information dictionary for a particular atom
	:param time: The time point
	:return: A untimed_lit Triple
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


def untimed_lit_to_internal_lit(info: atom_info, time):
	# multiply the sign to make sure that what we add is of the same sign as the untimed lit
	return info.untimed_lit + (time * Signatures.fullsig_size * info.sign)

# @profile
def form_nogood(t_atom_info, assigned_time: int) -> Optional[List[int]]:
	"""
	Forms a nogood based on the assigned time and atoms of a theory constraint

	:param t_atom_info: Complete information dictionary of the theory constraint
	:param assigned_time: the assigned time
	:return: the nogood for the given assigned time and constraint
	"""

	ng: Set[int] = set()

	for info in t_atom_info:
		time: int = reverse_assigned_time(info, assigned_time)
		try:
			lit = TimeAtomToSolverLit.grab_lit(untimed_lit_to_internal_lit(info, time))
		except KeyError:
			# this error would happen if an id is not in the mapping
			# if this happens it means the atom does not exist for this assigned time
			# if sign is 1 then it means that a POSITIVE atom does not exist -> a false atom in the nogood -> automatically ok
			if info.sign == 1:
				return None

			#if sign is -1 then is means that a POSITIVE atom does not exist and hence this NEGATIVE atom for that atom is always positive
			# so we can assign the 1 to lit
			lit = 1

		#if lit == 1:
		#	continue
		if lit == -1:
			return None

		ng.add(lit)

	return sorted(ng)


def check_assignment_build(tc: "TheoryConstraint", assigned_time, control) -> int:
	"""
	Checks if a nogood is a conflict or unit in the current assignment and builds the nogood
	return the nogood if no values are false

	:param nogood: nogood that will be checked
	:param control: clingo PropagateControl class
	:return int value that denotes the result of the check. See CONSTRAINT_CHECK for details
	"""
	true_count: int = 0
	nogood = []

	for uq_name, info in tc.t_atom_info.items():
		try:
			time = assigned_time - info.time_mod
			lit = TimeAtomToSolverLit.grab_lit(build_symbol_id(info, time))
		except KeyError:
			# this error would happen if an id is not in the mapping
			# if this happens it means the nogood does not exist for this assigned time
			if info.sign == 1:
				return CONSTRAINT_CHECK["NONE"], []

		if lit == 1:
			continue

		if lit == -1:
			return CONSTRAINT_CHECK["NONE"], []

		if control.assignment.is_true(lit):
			# if its true
			true_count += 1
		elif control.assignment.is_false(lit):
			# if one is false then it doesnt matter
			return CONSTRAINT_CHECK["NONE"], []

		nogood.append(lit)

	if true_count == len(nogood):
		return CONSTRAINT_CHECK["CONFLICT"], nogood
	elif true_count == len(nogood) - 1:
		return CONSTRAINT_CHECK["UNIT"], nogood
	else:
		return CONSTRAINT_CHECK["NONE"], []


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


def get_at_from_internal_lit(internal_lit: int, t_atom_info):
	ats = set()
	for info in t_atom_info:
		if Signatures.convert_to_untimed_lit(internal_lit) == info.untimed_lit:
			time = Signatures.convert_to_time(internal_lit)
			ats.add(get_assigned_time(info, time))

	return ats


def init_TA2L_mapping(init):
	for sign, sig in Signatures.sigs:
		for s_atom in init.symbolic_atoms.by_signature(*sig):
			time = parse_time(s_atom)
			# if argument size is 1 then only time is present
			if len(s_atom.symbol.arguments) == 1:
				name: str = f"{s_atom.symbol.name}("
			else:
				name: str = str(s_atom.symbol).split(",")[:-1]
				name = ",".join(name)
				name = f"{name},"
			lit = init.solver_literal(s_atom.literal)
			#TimeAtomToSolverLit.add((sign, name, time), lit * sign)
			#TimeAtomToSolverLit.add((1, name, time), lit)

	Signatures.finished = True


def init_TA2L_mapping_integers(init):

	for sign, sig in Signatures.sigs:
		for s_atom in init.symbolic_atoms.by_signature(*sig):
			time = parse_time(s_atom)

			name = s_atom.symbol.name
			args = tuple(s_atom.symbol.arguments[:-1])

			if (name, args) not in Signatures.fullsigs:
				# if it is skipped it should be because it is not in the domain!
				# signatures should be giving the domain of the function!!!
				continue

			lit = init.solver_literal(s_atom.literal) * sign
			internal_lit = Signatures.fullsigs[name, args] + (Signatures.fullsig_size * time)
			internal_lit *= sign
			TimeAtomToSolverLit.add(internal_lit, lit)

			"""
			print("  ")
			print("symbol: ", str(s_atom.symbol), lit)
			print("lit of the base(untimed lit): ", Signatures.fullsigs[name, args] * sign)
			print("size of the base: ", Signatures.fullsig_size)
			print("time: ", time)
			print("internal lit: ", internal_lit)
			print("using grab_lit: ", TimeAtomToSolverLit.grab_lit(internal_lit))
			print("using grab_id: ", TimeAtomToSolverLit.grab_id(lit))
			print("doing the % thing (untimed lit): ", Signatures.convert_to_untimed_lit(internal_lit))
			print("doing the // thing (time): ", Signatures.convert_to_time(internal_lit))

			# test
			print("lit = grab_lit: ", lit == TimeAtomToSolverLit.grab_lit(internal_lit))
			print("internal lit = grab_id: ", internal_lit in TimeAtomToSolverLit.grab_id(lit))
			print("time = internal lit // size: ", time == Signatures.convert_to_time(internal_lit))
			print("untimed_lit == internal_lit % size: ", Signatures.fullsigs[name, args] * sign == Signatures.convert_to_untimed_lit(internal_lit))
			2"""

	TimeAtomToSolverLit.size = Signatures.fullsig_size

	Signatures.sigs.clear()
	Signatures.fullsigs.clear()

	Signatures.finished = True

def choose_lit(lits: List[int], current_watches: int, control) -> Optional[int]:
	"""
	Checks the literals for a nogood and check for new watches

	:param lits: the current nogood
	:param current_watches: the current 2 watches
	:param  control: A clingo PropagateControl object

	:return: None or the new watch
	:rtype: None or int

	"""
	for possible_watch in lits:
		if possible_watch not in current_watches:
			if control.assignment.value(possible_watch) is None:# and not control.has_watch(possible_watch):
				return possible_watch

	return None


def get_replacement_watch(nogood: List[int], current_watches: List[int], control) -> Optional[List[int]]:
	"""
	choose a new watch for the given assigned time if possible
	:param nogood: the nogood
	:param current_watches: The current 2 watches
	:param control: A clingo PropagateControl object

	if a new watch can be found:
	:return: old_watch: int, new_watch: int, assigned_time: int

	if no new watch is found:
	:returns None
	"""

	new_watch: Optional[int] = choose_lit(nogood, current_watches, control)
	if new_watch is not None:
		return new_watch

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

	__slots__ = ["t_atom_info", "max_time", "min_time", "logger", "lock_nogoods"]

	def __init__(self, constraint, lock_nogoods=-1) -> None:
		self.logger = logging.getLogger(self.__module__ + "." + self.__class__.__name__)

		self.t_atom_info: List[atom_info]

		self.max_time: int = None
		self.min_time: int = None

		self.t_atom_info, self.min_time, self.max_time = parse_atoms(constraint)

		if lock_nogoods == -1:
			# never lock
			self.lock_nogoods = False

		elif lock_nogoods == 0:
			# always lock
			self.lock_nogoods = True

		elif lock_nogoods > 0:
			# lock once when it uses the same nogood x amount of times
			self.lock_nogoods = [lock_nogoods] * (self.max_time + 2)
			for i in range(-1, self.min_time):
				self.lock_nogoods[i] = None
			self.lock_nogoods[-1] = None # this one just captures the extra one just in case a literal gets an assigned time outside of the max bound

	@property
	def t_atom_names(self):
		return self.t_atom_info

	@property
	def size(self) -> int:
		return len(self.t_atom_info)

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
			init_TA2L_mapping_integers(init)

	def build_watches(self, init) -> List[int]:
		"""
		Add watches to the solver. This should be implemented by child class
		Basic case returns all literals in the nogood
		:param init: clingo PropagateInit class
		:return: List of literals that are watches by this theory constraint
		"""
		for assigned_time in range(self.min_time, self.max_time + 1):
			lits = form_nogood(self.t_atom_info, assigned_time)
			if lits is None:
				continue

			yield lits

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
						print("CHECK ERROR! lit: {}, val: {}".format(lit, control.assignment.value))
					return None
		return 0

	def check_if_lock(self, assigned_time):

		if self.lock_nogoods == True:
			return True

		elif self.lock_nogoods == False:
			return False

		else: # when we have the list
			self.lock_nogoods[assigned_time] -= 1
			if self.lock_nogoods[assigned_time] == 0:
				# del self.lock_nogoods[assigned_time]
				util.Count.add("locked_ng")
				self.lock_nogoods[assigned_time] = None

				return True

			else:
				return False

	def is_valid_time(self, assigned_time):
		# returns True if time is valid
		# False otherwise
		if type(self.lock_nogoods) == bool:
			if assigned_time < self.min_time or assigned_time > self.max_time:
				return False
		elif self.lock_nogoods[assigned_time] is None:
			return False

		return True

class TheoryConstraintSize1(TheoryConstraint):
	__slots__ = []

	def __init__(self, constraint) -> None:
		super().__init__(constraint)
		self.logger = logging.getLogger(self.__module__ + "." + self.__class__.__name__)

	def init(self, init):
		if not Signatures.finished:
			init_TA2L_mapping_integers(init)

		self.init_mappings(init)

	def init_mappings(self, init) -> None:
		"""
		Instead of adding to TimeAtomToSolverLit it immediately adds a clause for the nogood
		"""
		for info in self.t_atom_info:
			for assigned_time in range(self.min_time, self.max_time + 1):
				try:
					internal_lit = untimed_lit_to_internal_lit(info, assigned_time - info.time_mod)
					solver_lit = TimeAtomToSolverLit.grab_lit(internal_lit)
				except KeyError:
					continue

				# add nogood
				init.add_clause([-solver_lit])

		self.t_atom_info = None

	def check(self, *args, **kwargs):
		return 0
