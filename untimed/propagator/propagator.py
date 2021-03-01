from typing import Dict, Tuple, List, Any, Set
from collections import defaultdict

import untimed.util as util

from untimed.propagator.theoryconstraint_reg import TimeAtomToSolverLit
from untimed.propagator.theoryconstraint_reg import TheoryConstraint
from untimed.propagator.theoryconstraint_base import init_TA2L_mapping
from untimed.propagator.theoryconstraint_base import get_replacement_watch
from untimed.propagator.theoryconstraint_base import TheoryConstraintSize1

from untimed.propagator.theoryconstraint_prop import MetaTAtomProp

from untimed.propagator.theoryconstraint_prop import TheoryConstraintSize2Prop
from untimed.propagator.theoryconstraint_prop import TheoryConstraintNaiveProp
from untimed.propagator.theoryconstraint_prop import TheoryConstraint2watchProp
from untimed.propagator.theoryconstraint_prop import TheoryConstraintSize2Prop2WatchMap
from untimed.propagator.theoryconstraint_prop import TheoryConstraint2watchPropMap
from untimed.propagator.theoryconstraint_prop import TheoryConstraintSize2TimedProp
from untimed.propagator.theoryconstraint_prop import TheoryConstraintTimedProp
from untimed.propagator.theoryconstraint_prop import TheoryConstraintMetaProp
from untimed.propagator.theoryconstraint_prop import TheoryConstraintCountProp

from untimed.propagator.theoryconstraint_prop import propagate_timed


class Propagator:
	"""
	Propagator that handles the propagation of "time atoms"(aka theory atoms of theory constraints).

	Members:
	watch_to_tc                -- Mapping from a literal to a theory constraint.

	theory_constraints          -- List of all theory constraints
	"""

	__slots__ = ["watch_to_tc", "theory_constraints"]

	def __init__(self):

		self.watch_to_tc: Dict[Any, Set["TheoryConstraint"]] = defaultdict(list)

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
		init_TA2L_mapping(init)

		t_atom_count = 0
		for t_atom_count, t_atom in enumerate(init.theory_atoms, start=1):
			if t_atom.term.name == "constraint":
				tc = self.make_tc(t_atom)
				if tc.size == 1:
					tc.init(init)
				else:
					watches = tc.build_watches(init)
					self.add_atom_observer(tc, watches)

		for lit in self.watch_to_tc:
			init.add_watch(lit)
		util.Stats.add("Theory Constraints", t_atom_count)

	def propagate(self, control, changes):
		...

	# if we want to check we need the theory constraints list. look in the init to see if we delete it or not
	@util.Count("check")
	def check(self, control):
		for tc in self.theory_constraints:
			if tc.check(control) is None:
				# print("check failed?")
				return

	def make_tc(self, t_atom):
		pass


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

	@util.Timer("Prop_init")
	def init(self, init):
		watches = set()
		init_TA2L_mapping(init)

		t_atom_count = 0
		all_t_atom_count = 0
		for all_t_atom_count, t_atom in enumerate(init.theory_atoms, start=1):
			if t_atom.term.name == "constraint":
				t_atom_count += 1
				tc = self.make_tc(t_atom)
				if isinstance(tc, TheoryConstraint) and tc.size == 1:
					tc.init(init)
				else:
					for lits in tc.build_watches(init):
						watches.update(lits)
					self.add_atom_observer(tc, watches)

		for lit in watches:
			init.add_watch(lit)

		util.Stats.add("Theory Constraints", t_atom_count)
		util.Stats.add("Signature Constraints", all_t_atom_count - t_atom_count)

	@util.Count("Propagation")
	@util.Timer("Propagation")
	def propagate(self, control, changes):
		for lit in changes:
			for sign, name, time in TimeAtomToSolverLit.grab_name(lit):
				for tc in self.watch_to_tc[sign, name]:
					if tc.propagate(control, (sign, name, time)) is None:
						return

	def make_tc(self, t_atom):
		size = len(t_atom.elements)
		if size == 1:
			return TheoryConstraintSize1(t_atom)
		elif size == 2:
			util.Count.add("size_2")
			return TheoryConstraintSize2TimedProp(t_atom)
		else:
			util.Count.add("size_-1}")
			return TheoryConstraintTimedProp(t_atom)


class TimedAtomAllWatchesPropagator(TimedAtomPropagator):
	"""
	Propagator that handles the propagation of "time atoms"(aka theory atoms of theory constraints).

	"""
	__slots__ = []

	@util.Timer("Prop_init")
	def init(self, init):
		init_TA2L_mapping(init)

		t_atom_count = 0
		for t_atom_count, t_atom in enumerate(init.theory_atoms, start=1):
			if t_atom.term.name == "constraint":
				tc = self.make_tc(t_atom)
				if isinstance(tc, TheoryConstraint) and tc.size == 1:
					tc.init(init)
				else:
					self.add_atom_observer(tc, None)

		self.build_watches(init)

		util.Stats.add("Theory Constraints", t_atom_count)

	def build_watches(self, init):
		for lit in TimeAtomToSolverLit.lit_to_name.keys():
			if lit != -1:
				init.add_watch(lit)


class CountPropagator(TimedAtomPropagator):

	@util.Timer("Undo")
	def undo(self, thread_id, assignment, changes):
		for lit in changes:
			for sign, name, time in TimeAtomToSolverLit.grab_name(lit):
				for tc in self.watch_to_tc[sign, name]:
					if tc.size > 2:
						if tc.undo((sign, name, time)) is None:
							return

	def make_tc(self, t_atom):
		size = len(t_atom.elements)
		if size == 1:
			return TheoryConstraintSize1(t_atom)
		elif size == 2:
			util.Count.add("size_2")
			return TheoryConstraintSize2TimedProp(t_atom)
		else:
			util.Count.add("size_{}".format(size))
			return TheoryConstraintCountProp(t_atom)


class MetaPropagator(Propagator):
	def add_atom_observer(self, tc, prop_func):
		"""
		Add the tc to the list of tcs to be notified when their respective atoms are propagated
		:param tc: theory constraint for timed watches
		:param prop_func: Function used to propagate the watches
		"""
		if tc.size == 1:
			return

		for uq_name, info in tc.t_atom_info.items():
			self.watch_to_tc[info.sign, info.name].append(prop_func)

	@util.Timer("Prop_init")
	def init(self, init):
		watches = set()
		init_TA2L_mapping(init)

		t_atom_count = 0
		for t_atom_count, t_atom in enumerate(init.theory_atoms, start=1):
			if t_atom.term.name == "constraint":
				tc = self.make_tc(t_atom)
				if tc.size == 1:
					tc.init(init)
				else:
					for lits in tc.build_watches(init):
						watches.update(lits)
					self.add_atom_observer(tc, tc.build_prop_function())

		for lit in watches:
			init.add_watch(lit)

		util.Stats.add("Theory Constraints", t_atom_count)

	@util.Count("Propagation")
	@util.Timer("Propagation")
	def propagate(self, control, changes):

		for lit in changes:
			for sign, name, time in TimeAtomToSolverLit.grab_name(lit):
				for prop_func in self.watch_to_tc[sign, name]:
					if prop_func(control, (sign, name, time)) is None:
						return

	def make_tc(self, t_atom):
		size = len(t_atom.elements)
		if size == 1:
			return TheoryConstraintSize1(t_atom)
		elif size == 2:
			util.Count.add("size_2")
			return TheoryConstraintMetaProp(t_atom)
		else:
			util.Count.add("size_{}".format(size))
			return TheoryConstraintMetaProp(t_atom)


class MetaTAtomPropagator(TimedAtomPropagator):

	def add_atom_observer(self, tc):
		"""
		Add the tc to the list of tcs to be notified when their respective atoms are propagated
		:param tc: theory constraint for timed watches
		:param watches: Not used, just here for compatibility
		"""
		for t_atom in tc.t_atom_names:
			info = tc.t_atom_info[t_atom]
			if (info.sign, info.name) not in self.watch_to_tc:
				self.watch_to_tc[info.sign, info.name] = MetaTAtomProp((info.sign, info.name), info.time_mod)

			self.watch_to_tc[info.sign, info.name].build_prop_function(tc.t_atom_info, info.time_mod, tc.min_time, tc.max_time)

	@util.Timer("Prop_init")
	def init(self, init):
		watches = set()
		init_TA2L_mapping(init)

		t_atom_count = 0
		for t_atom_count, t_atom in enumerate(init.theory_atoms, start=1):
			if t_atom.term.name == "constraint":
				tc = self.make_tc(t_atom)
				if tc.size == 1:
					tc.init(init)
				else:
					for lits in tc.build_watches(init):
						watches.update(lits)

					self.add_atom_observer(tc)

		for t_atom, meta_tc in self.watch_to_tc.items():
			meta_tc.finish_prop_func()

		for lit in watches:
			init.add_watch(lit)

		util.Stats.add("Theory Constraints", t_atom_count)

	@util.Count("Propagation")
	@util.Timer("Propagation")
	def propagate(self, control, changes):

		for lit in changes:
			for sign, name, time in TimeAtomToSolverLit.grab_name(lit):
				if self.watch_to_tc[sign, name].propagate(control, (sign, name, time)) is None:
					return

	def make_tc(self, t_atom):
		size = len(t_atom.elements)
		if size == 1:
			return TheoryConstraintSize1(t_atom)
		elif size == 2:
			util.Count.add("size_2")
			return TheoryConstraint(t_atom)
		else:
			util.Count.add("size_{}".format(size))
			return TheoryConstraint(t_atom)


class RegularAtomPropagatorNaive(Propagator):
	"""
	Propagator that handles the propagation of "time atoms"(aka theory atoms of theory constraints).
	"""

	__slots__ = []

	@util.Count("Propagation")
	@util.Timer("Propagation")
	def propagate(self, control, changes):
		for lit in changes:
			for tc in self.watch_to_tc[lit]:
				if tc.propagate(control, lit) is None:
					return

	def make_tc(self, t_atom):
		size = len(t_atom.elements)
		if size == 1:
			return TheoryConstraintSize1(t_atom)
		elif size == 2:
			util.Count.add("size_2")
			return TheoryConstraintSize2Prop(t_atom)
		else:
			util.Count.add("size_{}".format(size))
			return TheoryConstraintNaiveProp(t_atom)


class RegularAtomPropagator2watch(Propagator):
	"""
	Propagator that handles the propagation of "time atoms"(aka theory atoms of theory constraints).

	Members:
	watch_to_tc                -- Mapping from a literal to a theory constraint.

	theory_constraints          -- List of all theory constraints
	"""
	__slots__ = []

	@util.Count("Propagation")
	@util.Timer("Propagation")
	# @profile
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

	def make_tc(self, t_atom):
		size = len(t_atom.elements)
		if size == 1:
			return TheoryConstraintSize1(t_atom)
		elif size == 2:
			util.Count.add("size_2")
			return TheoryConstraintSize2Prop(t_atom)
		else:
			util.Count.add("size_{}".format(size))
			return TheoryConstraint2watchProp(t_atom)


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

	@util.Timer("Prop_init")
	def init(self, init):
		all_watches = set()
		init_TA2L_mapping(init)

		t_atom_count = 0
		for t_atom_count, t_atom in enumerate(init.theory_atoms, start=1):
			if t_atom.term.name == "constraint":
				tc = self.make_tc(t_atom)
				if tc.size == 1:
					tc.init(init)
				else:
					watches, all_lits = tc.build_watches(init)
					self.add_atom_observer(tc, watches)

					all_watches.update(all_lits)

		for lit in all_watches:
			init.add_watch(lit)

		util.Stats.add("Theory Constraints", t_atom_count)

		self.theory_constraints = []

	@util.Count("Propagation")
	@util.Timer("Propagation")
	def propagate(self, control, changes):
		for lit in changes:
			for tc, at in set(self.watch_to_tc[lit]):
				ng = tc.propagate(control, (lit, at))
				if ng is None:
					return
				if not ng:  # if ng is empty
					continue

				for ng_lit in ng:
					if ng_lit != lit:
						if (tc, at) in self.watch_to_tc[ng_lit]:
							second_watch = ng_lit
							break

				new_watch = get_replacement_watch(ng, [lit, second_watch], control)
				if new_watch is not None:
					self.watch_to_tc[lit].remove((tc, at))
					self.watch_to_tc[new_watch].append((tc, at))

	def make_tc(self, t_atom):
		size = len(t_atom.elements)
		if size == 1:
			return TheoryConstraintSize1(t_atom)
		elif size == 2:
			util.Count.add("size_2")
			return TheoryConstraintSize2Prop2WatchMap(t_atom)
		else:
			util.Count.add("size_{}".format(size))
			return TheoryConstraint2watchPropMap(t_atom)