import logging
from collections import defaultdict

from typing import List, Dict, Tuple, Set, Any, Optional

import untimed.util as util

from untimed.propagator.theoryconstraint_data import TimeAtomToSolverLit

from untimed.propagator.theoryconstraint_data import CONSTRAINT_CHECK

from untimed.propagator.theoryconstraint_base import TheoryConstraint
from untimed.propagator.theoryconstraint_base import form_nogood
from untimed.propagator.theoryconstraint_base import get_at_from_name_id
from untimed.propagator.theoryconstraint_base import check_assignment
from untimed.propagator.theoryconstraint_base import get_replacement_watch


class TheoryConstraintSize2Prop(TheoryConstraint):
	__slots__ = []

	def __init__(self, constraint) -> None:
		super().__init__(constraint)
		self.logger = logging.getLogger(self.__module__ + "." + self.__class__.__name__)

	#@profile
	def build_watches(self, init) -> Set[int]:
		"""
		Since there are only 2 atoms in the constraint we add all literals as watches
		"""
		watches = set()
		for assigned_time in range(self.min_time, self.max_time + 1):
			lits = form_nogood(self, assigned_time)
			if lits is None:
				continue
			for lit in lits:
				init.add_watch(lit)
				watches.add(lit)

		return watches

	@util.Count("Propagation")
	#@profile
	def propagate(self, control, change) -> Optional[List[Tuple]]:
		"""
		For any relevant change, immediately form the nogood
		for the assigned times it is in and add it to the solver

		:param control: clingo PropagateControl class
		:param change: watch that was assigned
		:return None if propagation has to stop, A list of (delete, add) pairs of watches if propagation can continue
		"""
		with util.Timer("Propagation"):

			ats = set()
			for name_id in TimeAtomToSolverLit.grab_name(change):
				ats.update(get_at_from_name_id(name_id, self.t_atom_info))

			for assigned_time in ats:
				ng = form_nogood(self, assigned_time)
				if ng is None:
					continue
				if not control.add_nogood(ng) or not control.propagate():
					return None

			return []


class TheoryConstraintSize2Prop2WatchMap(TheoryConstraint):
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
			lits = form_nogood(self, assigned_time)
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

			ng = form_nogood(self, assigned_time)
			if ng is None:
				return []
			if not control.add_nogood(ng) or not control.propagate():
				return None

			return []


class TheoryConstraintNaiveProp(TheoryConstraint):
	__slots__ = []

	def __init__(self, constraint) -> None:
		super().__init__(constraint)
		self.logger = logging.getLogger(self.__module__ + "." + self.__class__.__name__)

	#@profile
	def build_watches(self, init) -> Set[int]:
		"""
		Since there are only 2 atoms in the constraint we add all literals as watches
		"""
		watches = set()
		for assigned_time in range(self.min_time, self.max_time + 1):
			lits = form_nogood(self, assigned_time)
			if lits is None:
				continue
			for lit in lits:
				init.add_watch(lit)
				watches.add(lit)

		return watches

	@util.Count("Propagation")
	#@profile
	def propagate(self, control, change) -> Optional[List[Tuple]]:
		"""
		For any relevant change, check the assignment of the whole nogood
		for the assigned times it is in. If it it conflicting or unit add the nogood to the solver

		:param control: clingo PropagateControl object
		:param change: watch that was assigned
		:return None if propagation has to stop, A list of (delete, add) pairs of watches if propagation can continue
		"""

		with util.Timer("Propagation"):
			ats = set()
			for name_id in TimeAtomToSolverLit.grab_name(change):
				ats.update(get_at_from_name_id(name_id, self.t_atom_info))

			for assigned_time in ats:
				ng = form_nogood(self, assigned_time)
				if ng is None:
					continue

				update_result = check_assignment(ng, control)

				if update_result == CONSTRAINT_CHECK["CONFLICT"] or update_result == CONSTRAINT_CHECK["UNIT"]:
					if not control.add_nogood(ng) or not control.propagate():
						return None
		return 1


class TheoryConstraint2watchProp(TheoryConstraint):
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

	#@profile
	def build_watches(self, init) -> List[int]:
		"""
		Only add watches for the first 2 literals of a nogood
		"""
		watches = set()
		for assigned_time in range(self.min_time, self.max_time + 1):
			lits = form_nogood(self, assigned_time)
			if lits is None:
				continue
			for lit in lits[:2]:
				self.watches_to_at[lit].add(assigned_time)
				init.add_watch(lit)
				watches.add(lit)

		return watches

	@util.Count("Propagation")
	#@profile
	def propagate(self, control, change) -> Optional[List[Tuple]]:
		"""
		For any relevant change, check the assignment of the whole nogood
		for the assigned times it is in. If it it conflicting or unit add the nogood to the solver

		After the check, replace the watch if possible.

		:param control: clingo PropagateControl object
		:param change: watch that was assigned
		:return None if propagation has to stop, A list of (delete, add) pairs of watches if propagation can continue
		"""
		with util.Timer("Propagation"):

			delete_add = []

			replacement_info: List[List[int]] = []

			for assigned_time in self.watches_to_at[change]:
				ng = form_nogood(self, assigned_time)
				if ng is None:
					continue

				update_result = check_assignment(ng, control)

				if update_result == CONSTRAINT_CHECK["CONFLICT"] or update_result == CONSTRAINT_CHECK["UNIT"]:
					if not control.add_nogood(ng) or not control.propagate():
						return None

				info = get_replacement_watch(ng, change, control)
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


class TheoryConstraint2watchPropMap(TheoryConstraint):
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
			lits = form_nogood(self, assigned_time)
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
			ng = form_nogood(self, assigned_time)
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


class TheoryConstraintSize2TimedProp(TheoryConstraint):
	__slots__ = []

	def __init__(self, constraint) -> None:
		super().__init__(constraint)
		self.logger = logging.getLogger(self.__module__ + "." + self.__class__.__name__)

	def build_watches(self, init) -> None:
		"""
		add all solver literals for the constraint as watches
		"""
		for assigned_time in range(self.min_time, self.max_time + 1):
			lits = form_nogood(self, assigned_time)
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
			ng = form_nogood(self, assigned_time)
			if ng is None:
				continue

			if not control.add_nogood(ng) or not control.propagate():
				return None

		return 1


class TheoryConstraintTimedProp(TheoryConstraint):
	__slots__ = []

	def __init__(self, constraint) -> None:
		super().__init__(constraint)
		self.logger = logging.getLogger(self.__module__ + "." + self.__class__.__name__)

	def build_watches(self, init) -> None:
		"""
		add all solver literals for the constraint as watches
		"""
		for assigned_time in range(self.min_time, self.max_time + 1):
			lits = form_nogood(self, assigned_time)
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
			ng = form_nogood(self, assigned_time)
			if ng is None:
				continue

			update_result = check_assignment(ng, control)

			if update_result == CONSTRAINT_CHECK["CONFLICT"] or update_result == CONSTRAINT_CHECK["UNIT"]:
				if not control.add_nogood(ng) or not control.propagate():
					return None

		return 1
