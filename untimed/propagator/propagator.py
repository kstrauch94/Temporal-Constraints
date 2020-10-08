from typing import Dict, Tuple, List
from collections import defaultdict

import untimed.util as util

from untimed.propagator.theoryconstraint import Map_Name_Lit
from untimed.propagator.theoryconstraint import TheoryConstraint


class TimedAtomPropagator:
	"""
	Propagator that handles the propagation of "time atoms"(aka theory atoms of theory constraints).

	Members:
	t_atom_to_tc                -- Mapping from a "time atom" to a theory constraint.

	theory_constraints          -- List of all theory constraints
	"""
	__slots__ = ["t_atom_to_tc", "theory_constraints"]

	def __init__(self):
		self.t_atom_to_tc: Dict[Tuple[int, str], List["TheoryConstraint"]] = defaultdict(list)

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
			self.t_atom_to_tc[info["sign"], info["name"]].append(tc)

	def init(self, init):
		for tc in self.theory_constraints:
			tc.init(init)
			self.add_atom_observer(tc)

	@util.Timer("Propagation")
	def propagate(self, control, changes):
		for lit in changes:
			for sign, name, time in Map_Name_Lit.grab_name(lit):
				for tc in self.t_atom_to_tc[sign, name]:
					if tc.propagate(control, (sign, name, time)) is None:
						return


class RegularAtomPropagatorNaive:
	"""
	Propagator that handles the propagation of "time atoms"(aka theory atoms of theory constraints).

	Members:
	watch_to_tc                -- Mapping from a literal to a theory constraint.

	theory_constraints          -- List of all theory constraints
	"""
	__slots__ = ["watch_to_tc", "theory_constraints"]

	def __init__(self):

		self.watch_to_tc: Dict[int, List["TheoryConstraint"]] = defaultdict(list)

		self.theory_constraints: List["TheoryConstraint"] = []

	def add_tc(self, tc):
		self.theory_constraints.append(tc)

	def add_atom_observer(self, tc, watches):
		"""
		Add the tc to the list of tcs to be notified when their respective atoms are propagated
		:param tc: theory constraint for timed watches
		:param watches: watches that will inform the given theory constraint
		"""
		if tc.size == 1:
			return

		for lit in watches:
			self.watch_to_tc[lit].append(tc)

	def init(self, init):
		for tc in self.theory_constraints:
			tc.init_mappings(init)
			watches = tc.build_watches(init)
			self.add_atom_observer(tc, watches)

	@util.Timer("Propagation")
	def propagate(self, control, changes):
		for lit in changes:
			for tc in self.watch_to_tc[lit]:
				if tc.propagate(control, lit) is None:
					return


class RegularAtomPropagator2watch:
	"""
	Propagator that handles the propagation of "time atoms"(aka theory atoms of theory constraints).

	Members:
	watch_to_tc                -- Mapping from a literal to a theory constraint.

	theory_constraints          -- List of all theory constraints
	"""
	__slots__ = ["watch_to_tc", "theory_constraints"]

	def __init__(self):

		self.watch_to_tc: Dict[int, List["TheoryConstraint"]] = defaultdict(list)

		self.theory_constraints: List["TheoryConstraint"] = []

	def add_tc(self, tc):
		self.theory_constraints.append(tc)

	def add_atom_observer(self, tc, watches):
		"""
		Add the tc to the list of tcs to be notified when their respective watches are propagated
		:param tc: theory constraint for timed watches
		:param watches: watches that will inform the given theory constraint
		"""
		if tc.size == 1:
			return

		for lit in watches:
			self.watch_to_tc[lit].append(tc)

	def init(self, init):
		for tc in self.theory_constraints:
			watches = tc.init(init)
			self.add_atom_observer(tc, watches)

	@util.Timer("Propagation")
	def propagate(self, control, changes):
		for lit in changes:
			for tc in set(self.watch_to_tc[lit]):
				result = tc.propagate(control, lit)
				if result is None:
					return

				for delete, add in result:
					self.watch_to_tc[delete].remove(tc)
					self.watch_to_tc[add].append(tc)

					control.add_watch(add)

					if self.watch_to_tc[delete] == []:
						control.remove_watch(delete)
