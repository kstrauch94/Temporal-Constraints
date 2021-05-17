import logging

from typing import List, Tuple, Set, Optional

import untimed.util as util

from untimed.propagator.theoryconstraint_data import atom_info
from untimed.propagator.theoryconstraint_data import TimeAtomToSolverLit
from untimed.propagator.theoryconstraint_data import Signatures
from untimed.propagator.theoryconstraint_data import CONSTRAINT_CHECK
from untimed.propagator.theoryconstraint_data import GlobalConfig

import clingo


@util.Timer("parse_atom")
# @profile
def parse_atoms(constraint) -> Tuple[List[atom_info], int, int]:
	"""
	Extract the relevant information of the given theory atom and populate t_atom_info with atominfo instances
	Also returns the min and max time of a given constraint

	:param constraint: clingo TheoryAtom
	"""
	t_atom_info: List[atom_info] = []

	min_time, max_time = parse_constraint_times(constraint.term.arguments)

	for atom in constraint.elements:
		# this gives me the "type" of the term | e.g. for +~on(..) it would return +~
		term_type: str = atom.terms[0].name

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


def parse_signature(constraint) -> None:
	"""
	Extract the signature information of the theory terms of the theory atom
	Populate the Signature data structure with that information

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

	:param info: atominfo named tuple
	:param time: The time point
	:return: assigned time
	"""
	return time + info.time_mod


def reverse_assigned_time(info: atom_info, assigned_time: int) -> int:
	"""
	Calculates the real time point based on the assigned time

	:param info: atominfo named tuple
	:param assigned_time: The assigned time
	:return: time
	"""
	return assigned_time - info.time_mod


def untimed_lit_to_internal_lit(info: atom_info, time) -> int:
	"""
	transform the "untimed" version of the literal to an internal literal
	internal literals contains information about the time point and sign
	:param info: atominfo named tuple
	:param time: time point(int)h
	:return: the untimed literal
	"""
	# multiply the sign to make sure that what we add is of the same sign as the untimed lit
	return info.untimed_lit + (time * Signatures.fullsig_size * info.sign)


# @profile
def form_nogood(t_atom_info, assigned_time: int) -> Optional[List[int]]:
	"""
	Forms a nogood based on the assigned time and atoms of a theory constraint

	:param t_atom_info: List of atominfo namedtuples of a particular constraint
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


def check_assignment(nogood, control) -> int:
	"""
	Checks if a nogood is a conflict or unit in the current assignment

	:param nogood: nogood that will be checked as a list of ints
	:param control: clingo PropagateControl object
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


def get_at_from_internal_lit(internal_lit: int, t_atom_info) -> List[int]:
	"""
	Calculate the assigned times for a particular theory constraint given an internal literal
	:param internal_lit: The internal literal (int)
	:param t_atom_info: List of atominfo named tuples of the constraint
	:return: a set of assigned times
	"""
	ats = set()
	for info in t_atom_info:
		if Signatures.convert_to_untimed_lit(internal_lit) == info.untimed_lit:
			time = Signatures.convert_to_time(internal_lit)
			ats.add(get_assigned_time(info, time))

	return ats


def init_TA2L_mapping_integers(init) -> None:
	"""
	Initialize the TA2L mapping using the signatures in the Signatures class
	:param init: clingo PropagateInit object
	"""
	# go through all signatures and signs

	for sign, sig in Signatures.sigs:

		# look at all the atoms that have that same signature
		# to avoid looking at the same list of atom multiple times with the same sig
		# then we could instead of saving tuples (sign, sig) make a dict {sig: [signs...]}
		for s_atom in init.symbolic_atoms.by_signature(*sig):
			time = parse_time(s_atom)

			name = s_atom.symbol.name
			args = tuple(s_atom.symbol.arguments[:-1])

			if (name, args) not in Signatures.fullsigs:
				# This happens when a symbol exists but the arguments are NOT within the given domain
				# for example, when the constraint uses a subset of the domain
				#
				# if it is skipped it is because it is not in the domain!
				# signatures should be giving the domain of the function!!!
				continue

			# grab the solver literal and apply the sign (solver literal is always positive since we look only for positive atoms)
			lit = init.solver_literal(s_atom.literal) * sign
			# convert it to an internal literal, dont forget to apply the sign!!
			internal_lit = Signatures.fullsigs[name, args] + (Signatures.fullsig_size * time)
			internal_lit *= sign
			# update the mapping
			TimeAtomToSolverLit.add(internal_lit, lit)

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

	new_watch = choose_lit(nogood, current_watches, control)
	if new_watch is not None:
		return new_watch

	return None


class TheoryConstraint:
	"""
	Base class for all theory constraints.

	Members:
	t_atom_info             -- List that holds atominfo named tuples
								for every theory term in the constraint

	max_time                -- Max time of the theory constraint

	min_time                -- Min time of the theory constraint

	lock_nogoods            -- List containing amount of times the nogood of a specific
								assigned time has to be added to lock the nogood
								or None
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
			if self.lock_on_build(lits, assigned_time, init):
				# if it is locked then we continue since we dont need to yield the lits(no need to watch them)
				continue
			yield lits

	def ground(self, init):
		"""
		This function is used in the all watches propagator to "ground" the constraints given the options
		lock_up_to and lock_from
		:param init: clingo PropagateInit object
		:return: None
		"""

		for assigned_time in range(self.min_time, self.max_time + 1):
			if assigned_time <= GlobalConfig.lock_up_to or assigned_time >= self.max_time - GlobalConfig.lock_from:
				util.Count.add("pre-grounded")
				lits = form_nogood(self.t_atom_info, assigned_time)
				if lits is None:
					continue

				self.lock_on_build(lits, assigned_time, init)

	@util.Timer("Undo")
	@util.Count("Undo")
	def undo(self, thread_id, assign, changes) -> None:
		"""
		Should be implemented in a child class if it is needed
		"""
		pass

	def propagate(self, control, changes) -> Optional[List[Tuple[int, int]]]:
		""""
		Should be implemented by the child class
		"""
		pass

	def propagate_main(self, assigned_time, control):

		if not self.is_valid_time(assigned_time):
			return 1

		ng = form_nogood(self.t_atom_info, assigned_time)
		if ng is None:
			return 1

		if check_assignment(ng, control) == CONSTRAINT_CHECK["NONE"]:
			return 1

		lock = self.check_if_lock(assigned_time)

		if not control.add_nogood(ng, lock=lock) or not control.propagate():
			util.Count.add("Conflicts added")
			return None

		util.Count.add("Units added")

		return 1

	def check(self, control) -> Optional[int]:
		"""
		Goes through every assigned time and checks the assignment of the nogood
		:param control: clingo PropagateControl object
		:return: None if a conflict was found, 0 otherwise
		"""
		for assigned_time in range(self.min_time, self.max_time + 1):
			if not self.is_valid_time(assigned_time):
				continue
			ng = form_nogood(self.t_atom_info, assigned_time)
			if check_assignment_complete(ng, control) == CONSTRAINT_CHECK["CONFLICT"]:
				if not control.add_nogood(ng) or not control.propagate():
					# model has some conflicts
					return None
		return 0

	def check_if_lock(self, assigned_time) -> bool:
		"""
		check if the nogood on a particular assigned time is to be locked
		:param assigned_time: the assigned time
		:return: True if it should be locked, False otherwise
		"""

		if self.lock_nogoods == True:
			util.Count.add("locked_ng")
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
		"""
		checks if an assigned time is valid for the theory constraint
		:param assigned_time: the assigned time
		:return: True if it is valid, False otherwise
		"""
		# returns True if time is valid
		# False otherwise
		if type(self.lock_nogoods) == bool:
			if assigned_time < self.min_time or assigned_time > self.max_time:
				return False
		else:
			try:
				if self.lock_nogoods[assigned_time] is None:
					return False
			except IndexError:
				# this could happen when using the timed_aw watch type and using lock-ng >= 1
				# basically, since we watch everything it is possible to get
				# literals from outside the scope of the constraint
				# and we might get an issue where we have a lock_nogoods list of a size that is lower than the time
				# point that the literal appears in
				return False

		return True

	def lock_on_build(self, ng, at, init):
		if at <= GlobalConfig.lock_up_to or at >= self.max_time - GlobalConfig.lock_from:
			init.add_clause([-l for l in ng])
			util.Count.add("pre-grounded")
			
			if type(self.lock_nogoods) == list:
				self.lock_nogoods[at] = None

			return True

		return False


class TheoryConstraintSize1(TheoryConstraint):
	"""
	Implement function for a theory constraint of size 1
	"""
	__slots__ = []

	def __init__(self, constraint) -> None:
		super().__init__(constraint)
		self.logger = logging.getLogger(self.__module__ + "." + self.__class__.__name__)

	def init(self, init):
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
		"""
		nothing needs to be checked
		"""
		return 0
