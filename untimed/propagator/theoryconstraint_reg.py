import logging
from collections import defaultdict

from typing import List, Dict, Tuple, Set, Optional

import untimed.util as util

from untimed.propagator.theoryconstraint_data import TimeAtomToSolverLit

from untimed.propagator.theoryconstraint_data import CONSTRAINT_CHECK

from untimed.propagator.theoryconstraint_base import TheoryConstraint
from untimed.propagator.theoryconstraint_base import form_nogood
from untimed.propagator.theoryconstraint_base import get_at_from_name_id
from untimed.propagator.theoryconstraint_base import check_assignment
from untimed.propagator.theoryconstraint_base import choose_lit
from untimed.propagator.theoryconstraint_base import get_replacement_watch


class TheoryConstraintSize2Reg(TheoryConstraint):
	__slots__ = []

	def __init__(self, constraint) -> None:
		super().__init__(constraint)
		self.logger = logging.getLogger(self.__module__ + "." + self.__class__.__name__)

	#@profile
	def build_watches(self, init) -> Set[int]:
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
	#@profile
	def propagate(self, control, changes) -> Optional[List[Tuple]]:
		"""
		For any relevant change, immediately form the nogood
		for the assigned times it is in and add it to the solver

		:param control: clingo PropagateControl class
		:param changes: list of watches that were assigned
		:return None if propagation has to stop, A list of (delete, add) pairs of watches if propagation can continue
		"""
		with util.Timer("Propagation"):

			for lit in changes:
				ats = set()
				for name_id in TimeAtomToSolverLit.grab_name(lit):
					ats.update(get_at_from_name_id(name_id, self.t_atom_info))

				for assigned_time in ats:
					if assigned_time < self.min_time or assigned_time > self.max_time:
						continue
					ng = form_nogood(self.t_atom_info, assigned_time)
					if ng is None:
						continue
					if not control.add_nogood(ng) or not control.propagate():
						return


class TheoryConstraintNaiveReg(TheoryConstraint):
	__slots__ = []

	def __init__(self, constraint) -> None:
		super().__init__(constraint)
		self.logger = logging.getLogger(self.__module__ + "." + self.__class__.__name__)

	#@profile
	def build_watches(self, init):
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
	#@profile
	def propagate(self, control, changes) -> Optional[List[Tuple]]:
		"""
		For any relevant change, check the assignment of the whole nogood
		for the assigned times it is in. If it it conflicting or unit add the nogood to the solver

		:param control: clingo PropagateControl object
		:param changes: list of watches that were assigned
		:return None if propagation has to stop, A list of (delete, add) pairs of watches if propagation can continue
		"""

		with util.Timer("Propagation"):
			for lit in changes:
				ats = set()
				for name_id in TimeAtomToSolverLit.grab_name(lit):
					ats.update(get_at_from_name_id(name_id, self.t_atom_info))

			# no indent here so it first gathers all assigned times
			for assigned_time in ats:
				if assigned_time < self.min_time or assigned_time > self.max_time:
					continue
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


class TheoryConstraint2watchReg(TheoryConstraint):
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
		for assigned_time in range(self.min_time, self.max_time + 1):
			lits = form_nogood(self.t_atom_info, assigned_time)
			if lits is None:
				continue
			for lit in lits[:2]:
				self.watches_to_at[lit].add(assigned_time)
				init.add_watch(lit)

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
