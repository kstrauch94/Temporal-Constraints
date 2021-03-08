import logging
from collections import defaultdict

from typing import List, Dict, Tuple, Set, Any, Optional

import untimed.util as util

from untimed.propagator.theoryconstraint_data import TimeAtomToSolverLit

from untimed.propagator.theoryconstraint_data import CONSTRAINT_CHECK

from untimed.propagator.theoryconstraint_base import TheoryConstraint
from untimed.propagator.theoryconstraint_base import form_nogood
from untimed.propagator.theoryconstraint_base import get_at_from_internal_lit
from untimed.propagator.theoryconstraint_base import check_assignment
from untimed.propagator.theoryconstraint_base import get_replacement_watch


class TheoryConstraintSize2Prop(TheoryConstraint):
	__slots__ = []

	def __init__(self, constraint, lock_nogoods=-1) -> None:
		super().__init__(constraint, lock_nogoods=lock_nogoods)
		self.logger = logging.getLogger(self.__module__ + "." + self.__class__.__name__)

	# @profile
	def build_watches(self, init) -> Set[int]:
		"""
		Since there are only 2 atoms in the constraint we add all literals as watches
		"""
		# has to be a list so that a watch can be added multiple times in case it is watched by multiple timepoints
		watches = []
		for assigned_time in range(self.min_time, self.max_time + 1):
			lits = form_nogood(self.t_atom_info, assigned_time)
			if lits is None:
				continue
			watches.extend(lits)

		return watches

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
			if not self.is_valid_time(assigned_time):
				continue

			ng = form_nogood(self.t_atom_info, assigned_time)
			if ng is None:
				continue

			lock = self.check_if_lock(assigned_time)

			if not control.add_nogood(ng, lock=lock) or not control.propagate():
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
		"""
		watches = []
		all_lits = set()
		for assigned_time in range(self.min_time, self.max_time + 1):
			lits = form_nogood(self.t_atom_info, assigned_time)
			if lits is None:
				continue
			for lit in lits:
				watches.append((lit, assigned_time))
			all_lits.update(lits)
		return watches, all_lits

	def propagate(self, control, change) -> Optional[List[Tuple]]:
		"""
		For any relevant change, immediately form the nogood
		for the assigned times it is in and add it to the solver

		:param control: clingo PropagateControl object
		:param change: lit and assigned time pair
		:return None if propagation has to stop, A list of (delete, add) pairs of watches if propagation can continue
		"""

		lit, assigned_time = change

		ng = form_nogood(self.t_atom_info, assigned_time)
		if ng is None:
			return []

		lock = self.check_if_lock(assigned_time)

		if not control.add_nogood(ng, lock=lock) or not control.propagate():
			return None

		return []


class TheoryConstraintNaiveProp(TheoryConstraint):
	__slots__ = []

	def __init__(self, constraint, lock_nogoods=-1) -> None:
		super().__init__(constraint, lock_nogoods=lock_nogoods)
		self.logger = logging.getLogger(self.__module__ + "." + self.__class__.__name__)

	# @profile
	def build_watches(self, init) -> Set[int]:

		watches = set()
		for assigned_time in range(self.min_time, self.max_time + 1):
			lits = form_nogood(self.t_atom_info, assigned_time)
			if lits is None:
				continue

			watches.update(lits)

		return watches

	# @profile
	def propagate(self, control, change) -> Optional[List[Tuple]]:
		"""
		For any relevant change, check the assignment of the whole nogood
		for the assigned times it is in. If it it conflicting or unit add the nogood to the solver

		:param control: clingo PropagateControl object
		:param change: watch that was assigned
		:return None if propagation has to stop, A list of (delete, add) pairs of watches if propagation can continue
		"""

		ats = set()
		for internal_lit in TimeAtomToSolverLit.grab_id(change):
			ats.update(get_at_from_internal_lit(internal_lit, self.t_atom_info))

		for assigned_time in ats:
			if not self.is_valid_time(assigned_time):
				continue
			ng = form_nogood(self.t_atom_info, assigned_time)
			if ng is None:
				continue

			update_result = check_assignment(ng, control)

			if update_result == CONSTRAINT_CHECK["CONFLICT"] or update_result == CONSTRAINT_CHECK["UNIT"]:

				lock = self.check_if_lock(assigned_time)

				if not control.add_nogood(ng, lock=lock) or not control.propagate():
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
		watches = []
		for assigned_time in range(self.min_time, self.max_time + 1):
			lits = form_nogood(self.t_atom_info, assigned_time)
			if lits is None:
				continue
			for lit in lits[:2]:
				self.watches_to_at[lit].add(assigned_time)
			watches.extend(lits)

		return watches

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

			update_result = check_assignment(ng, control)

			if update_result == CONSTRAINT_CHECK["CONFLICT"] or update_result == CONSTRAINT_CHECK["UNIT"]:
				lock = self.check_if_lock(assigned_time)
				if not control.add_nogood(ng, lock=lock) or not control.propagate():
					return None

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
		Also, add the new watch to the solver and remove the old watch if necessary

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
		all_lits = set()
		watches = []
		for assigned_time in range(self.min_time, self.max_time + 1):
			lits = form_nogood(self.t_atom_info, assigned_time)
			if lits is None:
				continue
			for lit in lits[:2]:
				watches.append((lit, assigned_time))

			all_lits.update(lits)

		return watches, all_lits

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
		ng = form_nogood(self.t_atom_info, assigned_time)
		if ng is None:
			return []

		update_result = check_assignment(ng, control)

		if update_result == CONSTRAINT_CHECK["CONFLICT"] or update_result == CONSTRAINT_CHECK["UNIT"]:
			lock = self.check_if_lock(assigned_time)
			if not control.add_nogood(ng, lock=lock) or not control.propagate():
				return None

		return ng


class TheoryConstraintSize2TimedProp(TheoryConstraint):
	__slots__ = []

	def __init__(self, constraint, lock_nogoods=-1) -> None:
		super().__init__(constraint, lock_nogoods=lock_nogoods)
		self.logger = logging.getLogger(self.__module__ + "." + self.__class__.__name__)

	def build_watches(self, init) -> None:
		"""
		add all solver literals for the constraint as watches
		"""
		for assigned_time in range(self.min_time, self.max_time + 1):
			lits = form_nogood(self.t_atom_info, assigned_time)
			if lits is None:
				continue
			yield lits

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

			if not self.is_valid_time(assigned_time):
				continue

			ng = form_nogood(self.t_atom_info, assigned_time)
			if ng is None:
				continue

			lock = self.check_if_lock(assigned_time)

			if not control.add_nogood(ng, lock=lock) or not control.propagate():
				return None

		return 1


class TheoryConstraintTimedProp(TheoryConstraint):
	__slots__ = []

	def __init__(self, constraint, lock_nogoods=-1) -> None:
		super().__init__(constraint, lock_nogoods=lock_nogoods)
		self.logger = logging.getLogger(self.__module__ + "." + self.__class__.__name__)

	def build_watches(self, init) -> None:
		"""
		add all solver literals for the constraint as watches
		"""
		for assigned_time in range(self.min_time, self.max_time + 1):
			lits = form_nogood(self.t_atom_info, assigned_time)
			if lits is None:
				continue

			yield lits

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
			ng = form_nogood(self.t_atom_info, assigned_time)
			if ng is None:
				continue

			update_result = check_assignment(ng, control)

			if update_result == CONSTRAINT_CHECK["CONFLICT"] or update_result == CONSTRAINT_CHECK["UNIT"]:
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

	def build_watches(self, init) -> None:
		"""
		add all solver literals for the constraint as watches
		"""
		for assigned_time in range(self.min_time, self.max_time + 1):
			lits = form_nogood(self.t_atom_info, assigned_time)
			if lits is None:
				continue

			yield lits

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
				lock = self.check_if_lock(assigned_time)
				if not control.add_nogood(ng, lock=lock) or not control.propagate():
					return None

		return 1

	def undo(self, change):
		ats = get_at_from_internal_lit(change, self.t_atom_info)
		for assigned_time in ats:
			if not self.is_valid_time(assigned_time):
				continue
			self.counts[assigned_time] -= 1
			if self.counts[assigned_time] < 0:
				print("ERROR???")


class TheoryConstraintMetaProp(TheoryConstraint):
	__slots__ = ["propagate_func"]

	def __init__(self, constraint, lock_nogoods=-1) -> None:
		super().__init__(constraint, lock_nogoods=lock_nogoods)

		self.logger = logging.getLogger(self.__module__ + "." + self.__class__.__name__)

	def build_watches(self, init) -> None:
		"""
		add all solver literals for the constraint as watches
		"""
		for assigned_time in range(self.min_time, self.max_time + 1):
			lits = form_nogood(self.t_atom_info, assigned_time)
			if lits is None:
				continue
			yield lits

	def propagate(self, control, change) -> Optional[List[Tuple]]:
		"""
		:param control: clingo PropagateControl object
		:param change: literal that was assigned
		:return None if propagation has to stop, A list of (delete, add) pairs of watches if propagation can continue
		"""
		return self.propagate_func(control, change)

	#@profile
	def build_prop_function(self):
		func_str = prop_template_start.format(f_name="prop_test")

		for info in self.t_atom_info:

			sign, untimed_lit, time_mod = info.sign, info.untimed_lit, info.time_mod

			grab_lit_str = []
			for other_info in self.t_atom_names:
				time_modifier = time_mod - other_info.time_mod
				grab_lit = check_mapping.format(untimed_lit=other_info.untimed_lit)
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

		return prop_test


prop_template_start = """
def {f_name}(control, change):
	# change is the internal literal
	time = Signatures.convert_to_time(change)

"""

prop_template_t_atom_start = """
def {f_name}(control, change):
	# propagate func for t_atom: {t_atom}
	time = Signatures.convert_to_time(change)
"""

prop_template_end = """
	return 1
"""

if_template = """
	if Signature.convert_to_untimed_lit(change) == {untimed_lit}:
		at = time + {t_mod}
		if at >= {min} and at <= {max}:	
			{ng}	
			update_result = check_assignment(ng, control)
			if update_result == CONSTRAINT_CHECK["CONFLICT"] or update_result == CONSTRAINT_CHECK["UNIT"]:
				if not control.add_nogood(ng, lock=self.lock_nogood) or not control.propagate():
					return None
"""

if_template_size2 = """
	if Signature.convert_to_untimed_lit(change) == {untimed_lit}:
		at = time + {t_mod}
		if at >= {min} and at <= {max}:	
			{ng}	
			if not control.add_nogood(ng, lock=self.lock_nogods) or not control.propagate():
				return None
"""

if_template_t_atom = """
	at = time + {t_mod}
	if at >= {min} and at <= {max}:	
		{ng}
		update_result = check_assignment(ng, control)
		if update_result == CONSTRAINT_CHECK["CONFLICT"] or update_result == CONSTRAINT_CHECK["UNIT"]:
			if not control.add_nogood(ng, lock=self.lock_nogods) or not control.propagate():
				return None
"""

check_mapping = "TimeAtomToSolverLit.grab_lit({untimed_lit})"

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
			grab_lit = check_mapping.format(untimed_lit=info.untimed_lit)
			grab_lit_str.append(grab_lit)

		ng_str = "ng = [{}]".format(", ".join(grab_lit_str))

		self.if_blocks.append(if_template_t_atom.format(t_mod=time_mod, min=min_time, max=max_time, ng=ng_str))

	#@profile
	def finish_prop_func(self):

		self.func_str = "{}\n{}\n{}".format(prop_template_t_atom_start.format(f_name="prop_test", t_atom=self.t_atom),
		                     "\n".join(self.if_blocks), prop_template_end)

		#print(self.func_str)

		with util.Timer("exec"):
			exec(self.func_str, globals())

		self.propagate_func = prop_test
		self.func_str = None
