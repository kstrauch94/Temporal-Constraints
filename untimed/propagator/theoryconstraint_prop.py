import logging
from collections import defaultdict

from typing import List, Dict, Tuple, Set, Optional

import untimed.util as util

from untimed.propagator.theoryconstraint_data import TimeAtomToSolverLit

from untimed.propagator.theoryconstraint_data import ConstraintCheck, StatNames

from untimed.propagator.theoryconstraint_base import TheoryConstraint
from untimed.propagator.theoryconstraint_base import form_nogood
from untimed.propagator.theoryconstraint_base import get_at_from_internal_lit
from untimed.propagator.theoryconstraint_base import check_assignment
from untimed.propagator.theoryconstraint_base import get_replacement_watch
from untimed.propagator.theoryconstraint_base import Signatures
from untimed.propagator.theoryconstraint_base import check_assignment_complete

import types


class TheoryConstraintSize2Prop(TheoryConstraint):
	__slots__ = []

	def __init__(self, constraint, lock_nogoods=-1) -> None:
		super().__init__(constraint, lock_nogoods=lock_nogoods)
		self.logger = logging.getLogger(self.__module__ + "." + self.__class__.__name__)

	# @profile
	def propagate(self, control, change) -> Optional[List[Tuple]]:
		"""
		For any relevant change, immediately form the nogood
		for the assigned times it is in and add it to the solver

		:param control: clingo PropagateControl class
		:param change: watch that was assigned
		:return None if propagation has to stop, A list of (delete, add) pairs of watches if propagation can continue
		"""

		ats = set()
		for internal_lit in TimeAtomToSolverLit.grab_id(change):
			ats.update(get_at_from_internal_lit(internal_lit, self.t_atom_info))

		for assigned_time in ats:
			if self.propagate_main(assigned_time, control) is None:
				return None

		return []


class TheoryConstraintSize2Prop2WatchMap(TheoryConstraint):
	__slots__ = []

	def __init__(self, constraint, lock_nogoods=-1) -> None:
		super().__init__(constraint, lock_nogoods=lock_nogoods)
		self.logger = logging.getLogger(self.__module__ + "." + self.__class__.__name__)

	def build_watches(self, init) -> Set[int]:
		"""
		Since there are only 2 atoms in the constraint we add all literals as watches
		We also return all literals in the nogood in order to tell the propagator which literals could
		potentially be watched as well.
		"""
		for lits, assigned_time in self.build_watches_at(init):
			yield lits, assigned_time, lits

	def propagate(self, control, change) -> Optional[List[Tuple]]:
		"""
		For any relevant change, immediately form the nogood
		for the assigned times it is in and add it to the solver

		:param control: clingo PropagateControl object
		:param change: lit and assigned time pair
		:return None if propagation has to stop, A list of (delete, add) pairs of watches if propagation can continue
		"""

		lit, assigned_time = change

		if not self.is_valid_time(assigned_time):
			return [], ConstraintCheck.UNIT

		ng = form_nogood(self.t_atom_info, assigned_time)
		if ng is None:
			return [], ConstraintCheck.UNIT

		if check_assignment(ng, control) == ConstraintCheck.NONE:
			return [], ConstraintCheck.UNIT

		lock = self.check_if_lock(assigned_time)

		if not control.add_nogood(ng, lock=lock) or not control.propagate():
			util.Count.add(StatNames.CONF_COUNT_MSG.value)
			return None
		util.Count.add(StatNames.UNITS_COUNT_MSG.value)

		# always return UNIT so that it doesnt attempt to change the watches for size 2
		return [], ConstraintCheck.UNIT


class TheoryConstraintNaiveProp(TheoryConstraint):
	__slots__ = []

	def __init__(self, constraint, lock_nogoods=-1) -> None:
		super().__init__(constraint, lock_nogoods=lock_nogoods)
		self.logger = logging.getLogger(self.__module__ + "." + self.__class__.__name__)

	# @profile
	def propagate(self, control, change) -> Optional[List[Tuple]]:
		"""
		For any relevant change, check the assignment of the whole nogood
		for the assigned times it is in. If it it conflicting or unit add the nogood to the solver

		:param control: clingo PropagateControl object
		:param change: watch that was assigned
		:return None if propagation has to stop, 1 otherwise
		"""

		ats = set()
		for internal_lit in TimeAtomToSolverLit.grab_id(change):
			ats.update(get_at_from_internal_lit(internal_lit, self.t_atom_info))

		for assigned_time in ats:
			if self.propagate_main(assigned_time, control) is None:
				return None

		return 1


class TheoryConstraint2watchProp(TheoryConstraint):
	"""
	Members:

	watches_to_at           --  Dictionary mapping the current watches to
								their respective assigned time(s)
	"""

	__slots__ = ["watches_to_at"]

	def __init__(self, constraint, lock_nogoods=-1) -> None:
		super().__init__(constraint, lock_nogoods=lock_nogoods)
		self.logger = logging.getLogger(self.__module__ + "." + self.__class__.__name__)
		self.watches_to_at: Dict[int, Set[int]] = defaultdict(set)

	# @profile
	def build_watches(self, init) -> List[int]:
		"""
		Only add watches for the first 2 literals of a nogood
		"""
		for lits, at in self.build_watches_at(init):
			for lit in lits[:2]:
				self.watches_to_at[lit].add(at)
			yield lits[:2]

	# @profile
	def propagate(self, control, change) -> Optional[List[Tuple]]:
		"""
		For any relevant change, check the assignment of the whole nogood
		for the assigned times it is in. If it it conflicting or unit add the nogood to the solver

		After the check, replace the watch if possible.

		:param control: clingo PropagateControl object
		:param change: watch that was assigned
		:return None if propagation has to stop, A list of (delete, add) pairs of watches if propagation can continue
		"""

		delete_add = []

		replacement_info: List[List[int]] = []

		for assigned_time in self.watches_to_at[change]:
			if not self.is_valid_time(assigned_time):
				continue

			ng = form_nogood(self.t_atom_info, assigned_time)
			if ng is None:
				continue

			result = self.check_assignment(ng, control, assigned_time)
			if result is None:
				return None
			elif result == ConstraintCheck.UNIT:
				continue
			else:
				# only look for replacement if nogood is not conflicting nor unit
				for lit, ats in self.watches_to_at.items():
					if lit != change:
						if assigned_time in ats:
							second_watch = lit
							break

				new_watch = get_replacement_watch(ng, [change, second_watch], control)
				if new_watch is not None:
					delete_add.append((change, new_watch))
					replacement_info.append([change, new_watch, assigned_time])

		self.replace_watches(replacement_info, control)

		return delete_add

	def replace_watches(self, info: List[List[int]], control) -> None:
		"""
		Update the watches_to_at dictionary based on the info returned by get_replacement_watch

		:param info: List of info about the replacement. Each element is a return type of get_replacement_watch
		:param control: clingo PropagateControl object
		"""

		for old_watch, new_watch, assigned_time in info:
			# remove the lit as a watch for constraint assigned_time
			self.watches_to_at[old_watch].remove(assigned_time)

			# add new watch as a watch for constraint assigned_time
			self.watches_to_at[new_watch].add(assigned_time)

class TheoryConstraint1watch(TheoryConstraint):
	"""
	Members:

	watches_to_at           --  Dictionary mapping the current watches to
								their respective assigned time(s)
	"""

	__slots__ = ["watches_to_at"]

	def __init__(self, constraint, lock_nogoods=-1) -> None:
		super().__init__(constraint, lock_nogoods=lock_nogoods)
		self.logger = logging.getLogger(self.__module__ + "." + self.__class__.__name__)
		self.watches_to_at: Dict[int, set[int]] = defaultdict(set)

	# @profile
	def build_watches(self, init) -> List[int]:
		"""
		Only add watches for the first 2 literals of a nogood
		"""
		for lits, at in self.build_watches_at(init):
			self.watches_to_at[lits[0]].add(at)
			yield [lits[0]]

	# @profile
	def propagate(self, control, change) -> Optional[List[Tuple]]:
		"""
		For any relevant change, check the assignment of the whole nogood
		for the assigned times it is in. If it it conflicting or unit add the nogood to the solver

		After the check, replace the watch if possible.

		:param control: clingo PropagateControl object
		:param change: watch that was assigned
		:return None if propagation has to stop, A list of (delete, add) pairs of watches if propagation can continue
		"""

		delete_add = []

		replacement_info: List[List[int]] = []

		for assigned_time in self.watches_to_at[change]:
			if not self.is_valid_time(assigned_time):
				continue

			ng = form_nogood(self.t_atom_info, assigned_time)
			if ng is None:
				continue

			result = self.check_assignment(ng, control, assigned_time)
			if result is None:
				return None
			elif result == ConstraintCheck.UNIT:
				return []
			else:
				for lit in ng:
					if lit == change:
						continue

					if control.assignment.value is None:
						self.watches_to_at[change].remove(assigned_time)
						self.watches_to_at[lit].add(assigned_time)
						delete_add.append([change, lit])
						break

		return delete_add

	def replace_watches(self, info: List[List[int]], control) -> None:
		"""
		Update the watches_to_at dictionary based on the info returned by get_replacement_watch

		:param info: List of info about the replacement. Each element is a return type of get_replacement_watch
		:param control: clingo PropagateControl object
		"""

		for old_watch, new_watch, assigned_time in info:
			# remove the lit as a watch for constraint assigned_time
			self.watches_to_at[old_watch].remove(assigned_time)

			# add new watch as a watch for constraint assigned_time
			self.watches_to_at[new_watch].add(assigned_time)


class TheoryConstraint2watchPropMap(TheoryConstraint):
	__slots__ = []

	def __init__(self, constraint, lock_nogoods=-1) -> None:
		super().__init__(constraint, lock_nogoods=lock_nogoods)
		self.logger = logging.getLogger(self.__module__ + "." + self.__class__.__name__)

	def build_watches(self, init) -> List[int]:
		"""
		Only add watches for the first 2 literals of a nogood
		"""
		for lits, assigned_time in self.build_watches_at(init):
			yield lits[:2], assigned_time, lits

	def propagate(self, control, change) -> Optional[List[Tuple]]:
		"""
		For any relevant change, check the assignment of the whole nogood
		for the assigned times it is in. If it it conflicting or unit add the nogood to the solver

		After the check, replace the watch if possible.

		:param control: clingo PropagateControl object
		:param change: watch and assigned time pair
		:return None if propagation has to stop, A list of (delete, add) pairs of watches if propagation can continue
		"""

		lit, assigned_time = change

		if not self.is_valid_time(assigned_time):
			return [], ConstraintCheck.UNIT

		ng = form_nogood(self.t_atom_info, assigned_time)
		if ng is None:
			return [], ConstraintCheck.UNIT

		update_result = check_assignment(ng, control)
		if update_result == ConstraintCheck.NONE:
			return ng, update_result

		lock = self.check_if_lock(assigned_time)
		if not control.add_nogood(ng, lock=lock) or not control.propagate():
			util.Count.add(StatNames.CONF_COUNT_MSG.value)
			return None
		util.Count.add(StatNames.UNITS_COUNT_MSG.value)

		return ng, update_result


class TheoryConstraintSize2TimedProp(TheoryConstraint):
	__slots__ = []

	def __init__(self, constraint, lock_nogoods=-1) -> None:
		super().__init__(constraint, lock_nogoods=lock_nogoods)
		self.logger = logging.getLogger(self.__module__ + "." + self.__class__.__name__)

	def propagate(self, control, change) -> Optional[List[Tuple]]:
		"""
		look for assigned times of the change and add the nogoods of those times to
		the solver

		:param control: clingo PropagateControl object
		:param change: tuple containing the info of the change. Tuple[sign, name, time]
		:return None if propagation has to stop, A list of (delete, add) pairs of watches if propagation can continue
		"""

		ats = get_at_from_internal_lit(change, self.t_atom_info)

		for assigned_time in ats:
			if self.propagate_main(assigned_time, control) is None:
				return None

		return 1


class TheoryConstraintTimedProp(TheoryConstraint):
	__slots__ = []

	def __init__(self, constraint, lock_nogoods=-1) -> None:
		super().__init__(constraint, lock_nogoods=lock_nogoods)
		self.logger = logging.getLogger(self.__module__ + "." + self.__class__.__name__)

	def propagate(self, control, change) -> Optional[List[Tuple]]:
		"""
		:param control: clingo PropagateControl object
		:param change: literal that was assigned
		:return None if propagation has to stop, A list of (delete, add) pairs of watches if propagation can continue
		"""

		ats = get_at_from_internal_lit(change, self.t_atom_info)

		for assigned_time in ats:
			if self.propagate_main(assigned_time, control) is None:
				return None

		return 1


class TAtomConseqs():
	__slots__ = ["untimed_lit", "conseqs", "lock_nogoods"]

	def __init__(self, untimed_atom=None, lock_nogoods=-1) -> None:
		#self.logger = logging.getLogger(self.__module__ + "." + self.__class__.__name__)

		self.untimed_lit = untimed_atom
		self.conseqs = []

		if lock_nogoods == -1:
			# never lock
			self.lock_nogoods = False

		elif lock_nogoods >= 0:
			# always lock
			self.lock_nogoods = True


	def build_conseqs(self, info, min, max):
		"""
		Extend the conseqs list given the theory constraint
		:param tc: theory constraint that involves the untimed atom for this atom
		:return:
		"""
		self_time_mod = None
		other_time_mod = None
		other_lit = None
		for i in info:
			if i.untimed_lit != self.untimed_lit:
				other_time_mod = i.time_mod
				other_lit = i.untimed_lit

			else:
				self_time_mod = i.time_mod

		if other_time_mod is None:
			# in this case both atoms are the same
			# we add the time mods in both orders

			self_time_mod = info[0].time_mod
			other_time_mod = info[1].time_mod

			conseq = [self.untimed_lit, self_time_mod, other_time_mod, min, max]
			# if we have constraints with the same atom just in different time steps
			# then we check so that we don't add the same consequence
			if conseq not in self.conseqs:
				self.conseqs.append(conseq)

			conseq = [self.untimed_lit, other_time_mod, self_time_mod, min, max]
			if conseq not in self.conseqs:
				self.conseqs.append(conseq)

			return

		conseq = [other_lit, self_time_mod, other_time_mod, min, max]
		# if we have constraints with the same atom just in different time steps
		# then we check so that we don't add the same consequence
		if conseq not in self.conseqs:
			self.conseqs.append(conseq)

	def is_valid_time(self, assigned_time, min_time, max_time):
		"""
		checks if an assigned time is valid for the theory constraint
		:param assigned_time: the assigned time
		:return: True if it is valid, False otherwise
		"""
		# returns True if time is valid
		# False otherwise
		if assigned_time < min_time or assigned_time > max_time:
			return False

		return True

	def propagate(self, control, change) -> Optional[List[Tuple]]:
		"""
		look for assigned times of the change and add the nogoods of those times to
		the solver

		:param control: clingo PropagateControl object
		:param change: tuple containing the internal literal and solver literal
		:return None if propagation has to stop, A list of (delete, add) pairs of watches if propagation can continue
		"""

		internal_lit, lit = change
		time = Signatures.convert_to_time(internal_lit)
		for conseq, self_time_mod, other_time_mod, min_time, max_time in self.conseqs:
			assigned_time = time + self_time_mod
			if not self.is_valid_time(assigned_time, min_time, max_time):
				continue

			other_lit = TimeAtomToSolverLit.grab_lit(Signatures.convert_to_internal_lit(conseq, assigned_time - other_time_mod, util.sign(conseq)))
			ng = [lit, other_lit]

			if check_assignment(ng, control) == ConstraintCheck.NONE:
				continue

			if not control.add_nogood(ng, lock=self.lock_nogoods) or not control.propagate():
				util.Count.add(StatNames.CONF_COUNT_MSG.value)
				return None

			util.Count.add(StatNames.UNITS_COUNT_MSG.value)

		return 1

	def check_if_lock(self, assigned_time):
		return self.lock_nogoods

	def check(self, control):
		for conseq, self_time_mod, other_time_mod, min_time, max_time in self.conseqs:
			for assigned_time in range(min_time, max_time):
				lit = TimeAtomToSolverLit.grab_lit(Signatures.convert_to_internal_lit(self.untimed_lit, assigned_time - self_time_mod, util.sign(self.untimed_lit)))
				other_lit = TimeAtomToSolverLit.grab_lit(Signatures.convert_to_internal_lit(conseq, assigned_time - other_time_mod, util.sign(conseq)))

				if check_assignment_complete([lit, other_lit], control) == ConstraintCheck.CONFLICT:
					lock = self.check_if_lock(assigned_time)
					if not control.add_nogood(ng, lock=lock) or not control.propagate():
						return None

		return 1

class TheoryConstraintCountProp(TheoryConstraint):
	__slots__ = ["counts"]

	def __init__(self, constraint, lock_nogoods=-1) -> None:
		super().__init__(constraint, lock_nogoods=lock_nogoods)
		self.counts: Dict[int, int] = {}
		for i in range(self.min_time, self.max_time + 1):
			self.counts[i] = 0
		self.logger = logging.getLogger(self.__module__ + "." + self.__class__.__name__)

	def propagate(self, control, change) -> Optional[List[Tuple]]:
		"""
		:param control: clingo PropagateControl object
		:param change: literal that was assigned
		:return None if propagation has to stop, A list of (delete, add) pairs of watches if propagation can continue
		"""

		ats = get_at_from_internal_lit(change, self.t_atom_info)

		for assigned_time in ats:
			if not self.is_valid_time(assigned_time):
				continue

			self.counts[assigned_time] += 1
			if self.counts[assigned_time] >= self.size - 1:
				ng = form_nogood(self.t_atom_info, assigned_time)
				if ng is None:
					continue

				if self.check_assignment(ng, control, assigned_time) is None:
					return None
		return 1

	def undo(self, change):
		ats = get_at_from_internal_lit(change, self.t_atom_info)
		for assigned_time in ats:
			if not self.is_valid_time(assigned_time):
				continue
			self.counts[assigned_time] -= 1
			if self.counts[assigned_time] < 0:
				print("ERROR: count for a particular assigned time should never be below 0 !!!")
				print("ERROR on assigned time: {}".format(assigned_time))


class TheoryConstraintMetaProp(TheoryConstraint):
	__slots__ = ["propagate_func"]

	def __init__(self, constraint, lock_nogoods=-1) -> None:
		super().__init__(constraint, lock_nogoods=lock_nogoods)

		self.logger = logging.getLogger(self.__module__ + "." + self.__class__.__name__)

	#@profile
	def build_prop_function(self):
		func_str = prop_template_start.format(f_name="prop_test", size=Signatures.fullsig_size)

		for info in self.t_atom_info:

			sign, untimed_lit, time_mod = info.sign, info.untimed_lit, info.time_mod

			grab_lit_str = []
			for other_info in self.t_atom_names:
				grab_lit = check_mapping.format(untimed_lit=other_info.untimed_lit, time_mod=other_info.time_mod, sign=other_info.sign)
				grab_lit_str.append(grab_lit)

			ng_str = "ng = [{}]".format(", ".join(grab_lit_str))

			if self.size > 2:
				func_str += if_template.format(untimed_lit=untimed_lit, t_mod=time_mod, min=self.min_time,
				                               max=self.max_time, ng=ng_str)
			else:
				func_str += if_template_size2.format(untimed_lit=untimed_lit, t_mod=time_mod, min=self.min_time,
				                                     max=self.max_time, ng=ng_str)

		func_str += prop_template_end

		with util.Timer("exec"):
			exec(func_str, globals())

		self.propagate_func = types.MethodType(prop_test, self)

		return self.propagate_func


prop_template_start = """
def {f_name}(self, control, change):
	# change is the internal literal
	time = Signatures.convert_to_time(change)

"""

prop_template_t_atom_start = """
def {f_name}(self, control, change):
	# propagate func for t_atom: {t_atom}
	time = Signatures.convert_to_time(change)
"""

prop_template_end = """
	return 1
"""

if_template = """
	if Signatures.convert_to_untimed_lit(change) == {untimed_lit}:
		at = time + {t_mod}
		if self.is_valid_time(at):
			{ng}
			if self.check_assignment(ng, control, at) is None:
				return None

"""

if_template_size2 = """
	if Signatures.convert_to_untimed_lit(change) == {untimed_lit}:
		at = time + {t_mod}
		if self.is_valid_time(at):
			{ng}
			if self.check_assignment(ng, control, at) is None:
				return None
"""

if_template_t_atom = """
	at = time + {t_mod}
	if at >= {min} and at <= {max}:
		{ng}
		update_result = check_assignment(ng, control)
		if update_result == ConstraintCheck.CONFLICT or update_result == ConstraintCheck.UNIT:
			lock = self.check_if_lock(at)
			if not control.add_nogood(ng, lock=lock) or not control.propagate():
				util.Count.add(StatNames.CONF_COUNT_MSG.value)
				return None
			util.Count.add(StatNames.UNITS_COUNT_MSG.value)
"""

check_mapping = "TimeAtomToSolverLit.grab_lit(Signatures.convert_to_internal_lit({untimed_lit}, at-{time_mod}, {sign}))"


class MetaTAtomProp():
	__slots__ = ["t_atom", "propagate_func", "func_str", "if_blocks"]

	def __init__(self, t_atom, time_mod) -> None:
		self.t_atom = t_atom
		self.if_blocks = []

		self.func_str = None

		self.propagate_func = None

	def propagate(self, control, change) -> Optional[List[Tuple]]:
		"""
		:param control: clingo PropagateControl object
		:param change: literal that was assigned
		:return None if propagation has to stop, A list of (delete, add) pairs of watches if propagation can continue
		"""
		return self.propagate_func(control, change)

	#@profile
	def build_prop_function(self, t_atom_info, time_mod, min_time, max_time):

		grab_lit_str = []

		for info in t_atom_info:
			grab_lit = check_mapping.format(untimed_lit=info.untimed_lit, time_mod=info.time_mod, sign=info.sign)
			grab_lit_str.append(grab_lit)

		ng_str = "ng = [{}]".format(", ".join(grab_lit_str))

		self.if_blocks.append(if_template_t_atom.format(t_mod=time_mod, min=min_time, max=max_time, ng=ng_str))

	#@profile
	def finish_prop_func(self):

		self.func_str = "{}\n{}\n{}".format(prop_template_t_atom_start.format(f_name="prop_test", t_atom=self.t_atom),
		                     "\n".join(self.if_blocks), prop_template_end)

		with util.Timer("exec"):
			exec(self.func_str, globals())

		self.propagate_func = types.MethodType(prop_test, self)
		self.func_str = None

	def check_if_lock(self, at):
		return False
