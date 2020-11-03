from typing import Dict, Tuple, List, Any
from collections import defaultdict

import untimed.util as util

from untimed.propagator.theoryconstraint import TimeAtomToSolverLit
from untimed.propagator.theoryconstraint import TheoryConstraint
from untimed.propagator.theoryconstraint import SymbolToProgramLit
from untimed.propagator.theoryconstraint import SymbolsLooked

from untimed.propagator.theoryconstraint import parse_time


class Propagator:
	"""
	Propagator that handles the propagation of "time atoms"(aka theory atoms of theory constraints).

	Members:
	watch_to_tc                -- Mapping from a literal to a theory constraint.

	theory_constraints          -- List of all theory constraints
	"""

	__slots__ = ["watch_to_tc", "theory_constraints"]

	def __init__(self):

		self.watch_to_tc: Dict[Any, List["TheoryConstraint"]] = defaultdict(list)

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

	@util.Timer("Prop_init")
	def init(self, init):

		signatures = set()
		for tc in self.theory_constraints:
			signatures.update(tc.signatures)

		for sig in signatures:
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

		for tc in self.theory_constraints:
			if tc.size == 1:
				tc.init(init)
			else:
				watches = tc.build_watches(init)
				self.add_atom_observer(tc, watches)

		SymbolToProgramLit.reset()

	def propagate(self, control, changes):
		...

	@util.Timer("check")
	@util.Count("check")
	def check(self, control):
		for tc in self.theory_constraints:
			if tc.check(control) is None:
				#print("check failed?")
				return


class TimedAtomPropagator(Propagator):
	"""
	Propagator that handles the propagation of "time atoms"(aka theory atoms of theory constraints).

	"""
	__slots__ = []

	def add_atom_observer(self, tc, watches):
		"""
		Add the tc to the list of tcs to be notified when their respective atoms are propagated
		:param tc: theory constraint for timed watches
		:param watches: Not used, just here for compatibility
		"""
		if tc.size == 1:
			return

		for uq_name, info in tc.t_atom_info.items():
			self.watch_to_tc[info.sign, info.name].append(tc)

	@util.Timer("Propagation")
	def propagate(self, control, changes):
		for lit in changes:
			for sign, name, time in TimeAtomToSolverLit.grab_name(lit):
				for tc in self.watch_to_tc[sign, name]:
					if tc.propagate(control, (sign, name, time)) is None:
						return


class RegularAtomPropagatorNaive(Propagator):
	"""
	Propagator that handles the propagation of "time atoms"(aka theory atoms of theory constraints).
	"""

	__slots__ = []

	@util.Timer("Propagation")
	def propagate(self, control, changes):
		for lit in changes:
			for tc in self.watch_to_tc[lit]:
				if tc.propagate(control, lit) is None:
					return


class RegularAtomPropagator2watch(Propagator):
	"""
	Propagator that handles the propagation of "time atoms"(aka theory atoms of theory constraints).

	Members:
	watch_to_tc                -- Mapping from a literal to a theory constraint.

	theory_constraints          -- List of all theory constraints
	"""
	__slots__ = []

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


class RegularAtomPropagator2watchMap(Propagator):
	"""
	Propagator that handles the propagation of "time atoms"(aka theory atoms of theory constraints).

	Members:
	watch_to_tc                -- Mapping from a literal to a theory constraint.

	theory_constraints          -- List of all theory constraints
	"""
	__slots__ = []

	def add_atom_observer(self, tc, watches):
		"""
		Add the tc to the list of tcs to be notified when their respective watches are propagated
		For the given lit, we save the tc along with the respective assigned time
		:param tc: theory constraint for timed watches
		:param watches: List of watches and assigned time pairs
		"""
		if tc.size == 1:
			return

		for lit, at in watches:
			self.watch_to_tc[lit].append((tc, at))

	@util.Timer("Propagation")
	def propagate(self, control, changes):
		for lit in changes:
			for tc, at in set(self.watch_to_tc[lit]):
				result = tc.propagate(control, (lit, at))
				if result is None:
					return

				for delete, add in result:
					self.watch_to_tc[delete].remove((tc, at))
					self.watch_to_tc[add].append((tc, at))

					control.add_watch(add)

					if self.watch_to_tc[delete] == []:
						control.remove_watch(delete)
