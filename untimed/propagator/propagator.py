from typing import Dict, List, Any, Set
from collections import defaultdict

import heapq
import random

import untimed.util as util
from untimed.propagator.theoryconstraint_data import ConstraintCheck
from untimed.propagator.theoryconstraint_data import TimeAtomToSolverLit
from untimed.propagator.theoryconstraint_data import StatNames
from untimed.propagator.theoryconstraint_data import GlobalConfig
from untimed.propagator.theoryconstraint_data import NOID


from untimed.propagator.theoryconstraint_base import TheoryConstraint
from untimed.propagator.theoryconstraint_base import TheoryConstraintSize1
from untimed.propagator.theoryconstraint_base import init_TA2L_mapping_integers
from untimed.propagator.theoryconstraint_base import Signatures
from untimed.propagator.theoryconstraint_base import get_replacement_watch
from untimed.propagator.theoryconstraint_base import parse_atoms, form_nogood

from untimed.propagator.theoryconstraint_prop import MetaTAtomProp
from untimed.propagator.theoryconstraint_prop import TAtomConseqs

from untimed.propagator.theoryconstraint_prop import TheoryConstraintSize2Prop
from untimed.propagator.theoryconstraint_prop import TheoryConstraintNaiveProp
from untimed.propagator.theoryconstraint_prop import TheoryConstraint2watchProp
from untimed.propagator.theoryconstraint_prop import TheoryConstraintSize2Prop2WatchMap
from untimed.propagator.theoryconstraint_prop import TheoryConstraint2watchPropMap
from untimed.propagator.theoryconstraint_prop import TheoryConstraintSize2TimedProp
from untimed.propagator.theoryconstraint_prop import TheoryConstraintTimedProp
from untimed.propagator.theoryconstraint_prop import TheoryConstraintMetaProp
from untimed.propagator.theoryconstraint_prop import TheoryConstraintCountProp
from untimed.propagator.theoryconstraint_prop import TheoryConstraint1watch

class Heuristic:

	def __init__(self) -> None:
		pass

	def init(self, init):
		pass

	def add_var(self, var):
		pass

	def heur_decide(self, assignment, fallback):
		return fallback

	def increase_conflict_count(self):
		pass

	def update_conflict(self, vars):
		pass

	def set_unassigned(self, vars):
		pass

	def add_active(self, vars):
		pass

	def set_assigned(self, vars):
		pass

	def update(self, conflict_exists):
		pass

	def increase_var_count(self, vars):
		pass

class GHBHeuristic(Heuristic):

	def __init__(self) -> None:
		self.num_conflicts = 0
		self.active = set()

		self.last_conflict = {}

		self.heur_value = {}

		self.__alpha = 0.4

		self.__decay = 10e-6

		self.assigned = set()
		self.assigned.add(1)

		self.heap = []

	def init(self, init):
		for atom in init.symbolic_atoms:
			lit = init.solver_literal(atom.literal)
			if lit == 1:
				continue
			self.add_var(lit)
			self.add_var(-lit)

			init.add_watch(lit)
			init.add_watch(-lit)

		util.Count.add("Heur watches", len(self.heur_value.keys()))

	def propagate(self, control, changes):
		self.add_active(changes)
		self.set_assigned(changes)

		self.update(conflict_exists=False)


	@util.Timer("Time to decide")
	def decide(self, thread_id, assignment, fallback):
		return self.heur_decide(assignment, fallback)

	def undo(self, thread_id, assignment, changes):
		#self.heuristic.increase_conflict_count()
		#self.heuristic.update_conflict(changes)
		self.set_unassigned(changes)

	@util.Timer("Heuristic")
	def add_var(self, var):
		self.last_conflict[var] = 0

		self.heur_value[var] = 0

	@util.Timer("Heuristic")
	def set_assigned(self, vars):
		self.assigned.update(vars)

	@util.Timer("Heuristic")
	def set_unassigned(self, vars):
		self.assigned.difference_update(vars)

	@util.Timer("Heuristic")
	def add_active(self, vars):
		self.active.update(vars)

	@util.Timer("Heuristic-update")
	def update(self, conflict_exists):
		#return 
		if conflict_exists:
			multiplier = 1.0
		else:
			multiplier = 0.9

		for v in self.active:
			reward = multiplier / ( self.num_conflicts - self.last_conflict[v] + 1 )

			self.heur_value[v] = ( (1.0 - self.__alpha) * self.heur_value[v] ) + (self.__alpha * reward)

			#heapq.heappush(self.heap, (-self.heur_value[v], v))

		if self.__alpha > 0.06:
			self.__alpha -= self.__decay

	@util.Timer("Heuristic")
	def increase_conflict_count(self):
		self.num_conflicts += 1

	@util.Timer("Heuristic")

	def heur_decide(self, assignment, fallback):
		#return fallback

		if self.active.issubset(self.assigned):
			util.Count.add("returning fallback")
			return fallback
		
		"""
		best = None
		while 1:
			if len(self.heap) == 0:
				break
			val, best = heapq.heappop(self.heap)

			if best not in self.active or best in self.assigned:
				continue
			else:
				break
		"""
		
		"""
		max = 0
		best = None
		for v in self.active:
			if v not in self.assigned:
				if self.heur_value[v] > max:
					max = self.heur_value[v]
					best = v
		"""
		best = None
		heap = []
		for v in self.active:
			if v not in self.assigned:
				heapq.heappush(heap, (-self.heur_value[v], v))
		
		if len(heap) != 0:
			val, best = heapq.heappop(heap)

		if best is None:
			util.Count.add("returning fallback")
			return fallback

		util.Count.add("returning heur best")
		return best


class MomsHeuristic(Heuristic):

	def __init__(self) -> None:
		self.moms_scores = []
		self.heur_value = {}

		self.assigned = set()
		self.assigned.add(1)
		self.assigned.add(-1)

		self.alpha = 0.9

		self.decision_taken = 0

		self.sorted = False

	@util.Timer("Heuristic")
	def add_var(self, var):
		if var not in self.heur_value:
			self.heur_value[var] = 0
	
	@util.Timer("Heuristic")
	def increase_var_count(self, vars):
		for v in vars:
			self.add_var(v)
			self.heur_value[v] += 1

	@util.Timer("Heuristic")
	def set_assigned(self, vars):
		self.assigned.update(vars)

	@util.Timer("Heuristic")
	def set_unassigned(self, vars):
		self.assigned.difference_update(vars)

	@util.Timer("Heuristic decide")
	def heur_decide(self, assignment, fallback):
		if not self.sorted:
			self.moms_scores = sorted(self.heur_value.items(), key=lambda x: x[1], reverse=True)
			self.sorted = True

		self.decision_taken += 1

		# formula is   1 / (X^alpha)   where X is the decisions taken
		if random.random() <= 1.0/(float(self.decision_taken) ** self.alpha):
			# choose the variable with the highest moms score
			# that has not yet been assigned
			for v, score in self.moms_scores:
				if assignment.is_free(v):
					util.Count.add("Heuristic Decisions")
					return v
				
		util.Count.add("Fallback Decisions")
		return fallback


class Propagator:
	"""
	Propagator for theory constraints

	Members:
	watch_to_tc                 -- Mapping from a literal to a theory constraint.

	theory_constraints          -- List of all theory constraints

	lock_ng                     -- Tells the theory constraints when to lock nogoods
	"""

	__slots__ = ["watch_to_tc", "theory_constraints", "lock_ng", "watches", "id", "heuristic"]

	def __init__(self, id, lock_ng=-1, heuristic=None):

		self.id = id

		self.watch_to_tc: Dict[Any, Set["TheoryConstraint"]] = defaultdict(set)

		self.theory_constraints: List["TheoryConstraint"] = []

		self.lock_ng = lock_ng

		if heuristic is None:
			self.heuristic = Heuristic()
		elif heuristic == "moms":
			self.heuristic = MomsHeuristic()
		elif heuristic == "ghb":
			self.heuristic = GHBHeuristic()

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
			self.watch_to_tc[lit].add(tc)

	@util.Timer(StatNames.INIT_TIMER_MSG.value)
	def init(self, init):
		#print("Starting Initialization of propagator...")
		self.watches = set()
		init_TA2L_mapping_integers(init)

		for t_atom in init.theory_atoms:
			if t_atom.term.name == "constraint":
				if self.id is not None:
					if len(t_atom.term.arguments) == 2 and self.id != NOID:
						continue
					elif t_atom.term.arguments[-1].name != self.id:
						continue
				tc = self.make_tc(t_atom)
				if tc.size == 1:
					tc.init(init)
				else:
					self.build_watches(tc, init)

					self.add_tc(tc)

		for lit in self.watches:
			init.add_watch(lit)
			self.heuristic.add_var(lit)
		
		util.Count.add("Normal watches {self.id}", len(self.watches))

		self.watches = None
		del self.watches

		util.Count.add(f"Untimed watches {self.id}", len(self.watch_to_tc.keys()))

	@util.Timer("Time to decide")
	def decide(self, thread_id, assignment, fallback):
		return self.heuristic.heur_decide(assignment, fallback)

	def undo(self, thread_id, assignment, changes):
		self.heuristic.increase_conflict_count()
		self.heuristic.update_conflict(changes)
		self.heuristic.set_unassigned(changes)

	def build_watches(self, tc, init):
		for lits in tc.build_watches(init):
			self.watches.update(lits)
			self.add_atom_observer(tc, lits)
			self.heuristic.increase_var_count(lits)

	@util.Count(StatNames.PROP_CALLS_MSG.value)
	def propagate(self, control, changes):
		...

	# if we want to check we need the theory constraints list. look in the init to see if we delete it or not
	@util.Count(StatNames.CHECK_CALLS_MSG.value)
	@util.Timer(StatNames.CHECK_TIMER_MSG.value)
	def check(self, control):
		for tc in self.theory_constraints:
			if tc.check(control) is None:
				# check failed because there was a conflict
				return

	def make_tc(self, t_atom):
		pass

class TimedAtomPropagator(Propagator):
	"""
	Propagator that handles the propagation of "time atoms" (aka theory atoms of theory constraints).

	"""
	__slots__ = []

	def add_atom_observer(self, tc):
		"""
		Add the tc to the list of tcs to be notified when their respective atoms are propagated
		:param tc: theory constraint for timed watches
		:param watches: Not used, just here for compatibility
		"""
		if tc.size == 1:
			return

		for info in tc.t_atom_info:
			self.watch_to_tc[info.untimed_lit].add(tc)

	def build_watches(self, tc, init):
		for lits in tc.build_watches(init):
			self.watches.update(lits)
			self.heuristic.increase_var_count(lits)
		self.add_atom_observer(tc)

	@util.Count(StatNames.PROP_CALLS_MSG.value)
	def propagate(self, control, changes):
		self.heuristic.add_active(changes)
		self.heuristic.set_assigned(changes)
		with util.Timer("Propagation-{}".format(str(self.id))):
			for lit in changes:
				for internal_lit in TimeAtomToSolverLit.grab_id(lit):
					for tc in self.watch_to_tc[Signatures.convert_to_untimed_lit(internal_lit)]:
						if tc.propagate(control, internal_lit) is None:
							self.heuristic.update(conflict_exists=True)
							return

		self.heuristic.update(conflict_exists=False)


	def make_tc(self, t_atom):
		size = len(t_atom.elements)
		if size == 1:
			return TheoryConstraintSize1(t_atom)
		elif size == 2:
			util.Count.add(StatNames.SIZE2_COUNT_MSG.value)
			return TheoryConstraintSize2TimedProp(t_atom, self.lock_ng)
		else:
			util.Count.add(StatNames.SIZEN_COUNT_MSG.value)
			return TheoryConstraintTimedProp(t_atom, self.lock_ng)


class TimedAtomPropagatorCheck(Propagator):
	"""
	Propagator that handles the propagation of "time atoms" (aka theory atoms of theory constraints).

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

		for info in tc.t_atom_info:
			self.watch_to_tc[info.untimed_lit].add(tc)

	def build_watches(self, tc, init):
		tc.ground(init)

	def make_tc(self, t_atom):
		size = len(t_atom.elements)
		if size == 1:
			return TheoryConstraintSize1(t_atom)
		elif size == 2:
			util.Count.add(StatNames.SIZE2_COUNT_MSG.value)
			return TheoryConstraintSize2TimedProp(t_atom, self.lock_ng)
		else:
			util.Count.add(StatNames.SIZEN_COUNT_MSG.value)
			return TheoryConstraintTimedProp(t_atom, self.lock_ng)


class TimedAtomAllWatchesPropagator(TimedAtomPropagator):
	"""
	Propagator that handles the propagation of "time atoms"(aka theory atoms of theory constraints).

	"""
	__slots__ = []

	@util.Timer(StatNames.INIT_TIMER_MSG.value)
	def init(self, init):
		super().init(init)

		self.add_watches(init)

	def build_watches(self, tc, init):
		tc.ground(init)
		self.add_atom_observer(tc)

	def add_watches(self, init):
		"""
		Watch every literal in the mapping
		:param init: clingo PropagateInit object
		"""
		for lit in TimeAtomToSolverLit.lit_to_id.keys():
			if lit != -1:
				init.add_watch(lit)
				self.heuristic.add_var(lit)
		
		util.Count.add("Normal watches {self.id}", len(TimeAtomToSolverLit.lit_to_id.keys()))


class CountPropagator(TimedAtomPropagator):

	@util.Count(StatNames.UNDO_CALLS_MSG.value)
	@util.Timer(StatNames.UNDO_TIMER_MSG.value)
	def undo(self, thread_id, assignment, changes):
		for lit in changes:
			for internal_lit in TimeAtomToSolverLit.grab_id(lit):
				for tc in self.watch_to_tc[Signatures.convert_to_untimed_lit(internal_lit)]:
					if tc.size > 2:
						if tc.undo(internal_lit) is None:
							return

	def make_tc(self, t_atom):
		size = len(t_atom.elements)
		if size == 1:
			return TheoryConstraintSize1(t_atom)
		elif size == 2:
			util.Count.add(StatNames.SIZE2_COUNT_MSG.value)
			return TheoryConstraintSize2TimedProp(t_atom, self.lock_ng)
		else:
			util.Count.add(StatNames.SIZEN_COUNT_MSG.value)
			return TheoryConstraintCountProp(t_atom, self.lock_ng)


class MetaPropagator(Propagator):
	def add_atom_observer(self, tc, prop_func):
		"""
		Add the tc to the list of tcs to be notified when their respective atoms are propagated
		:param tc: theory constraint for timed watches
		:param prop_func: Function used to propagate the watches
		"""
		if tc.size == 1:
			return

		for info in tc.t_atom_info:
			self.watch_to_tc[info.untimed_lit].add(prop_func)

	def build_watches(self, tc, init):
		for lits in tc.build_watches(init):
			self.watches.update(lits)
		self.add_atom_observer(tc, tc.build_prop_function())

	@util.Count(StatNames.PROP_CALLS_MSG.value)
	def propagate(self, control, changes):
		with util.Timer("Propagation-{}".format(str(self.id))):
			for lit in changes:
				for internal_lit in TimeAtomToSolverLit.grab_id(lit):
					for prop_func in self.watch_to_tc[Signatures.convert_to_untimed_lit(internal_lit)]:
						if prop_func(control, internal_lit) is None:
							return

	def make_tc(self, t_atom):
		size = len(t_atom.elements)
		if size == 1:
			return TheoryConstraintSize1(t_atom)
		elif size == 2:
			util.Count.add(StatNames.SIZE2_COUNT_MSG.value)
			return TheoryConstraintMetaProp(t_atom, self.lock_ng)
		else:
			util.Count.add(StatNames.SIZEN_COUNT_MSG.value)
			return TheoryConstraintMetaProp(t_atom, self.lock_ng)


class MetaTAtomPropagator(TimedAtomPropagator):

	def add_atom_observer(self, tc):
		"""
		Add the tc to the list of tcs to be notified when their respective atoms are propagated
		:param tc: theory constraint for timed watches
		:param watches: Not used, just here for compatibility
		"""
		for info in tc.t_atom_names:
			if info.untimed_lit not in self.watch_to_tc:
				self.watch_to_tc[info.untimed_lit] = MetaTAtomProp(info.untimed_lit, info.time_mod)

			self.watch_to_tc[info.untimed_lit].build_prop_function(tc.t_atom_info, info.time_mod, tc.min_time, tc.max_time)

	@util.Timer(StatNames.INIT_TIMER_MSG.value)
	def init(self, init):
		super().init(init)

		for t_atom, meta_tc in self.watch_to_tc.items():
			meta_tc.finish_prop_func()

	@util.Count(StatNames.PROP_CALLS_MSG.value)
	def propagate(self, control, changes):
		with util.Timer("Propagation-{}".format(str(self.id))):
			for lit in changes:
				for internal_lit in TimeAtomToSolverLit.grab_id(lit):
					# have to check if untimed lit is in the mapping because it is possible that the
					# solver lit is associated with internal literals that are not relevant to this
					# propagator. This is only needed for this and Conseq since the mapping directly
					# gives the function. On other propagator types then mapping returns an empty list
					# and hence it does not loop at all
					untimed_lit = Signatures.convert_to_untimed_lit(internal_lit)
					if untimed_lit in self.watch_to_tc:
						if self.watch_to_tc[untimed_lit].propagate(control, internal_lit) is None:
							return

	def make_tc(self, t_atom):
		size = len(t_atom.elements)
		if size == 1:
			return TheoryConstraintSize1(t_atom)
		elif size == 2:
			util.Count.add(StatNames.SIZE2_COUNT_MSG.value)
			return TheoryConstraint(t_atom, self.lock_ng)
		else:
			util.Count.add(StatNames.SIZEN_COUNT_MSG.value)
			return TheoryConstraint(t_atom, self.lock_ng)


class ConseqsPropagator(TimedAtomPropagator):

	def add_atom_observer(self, tc):
		"""
		Add the tc to the list of tcs to be notified when their respective atoms are propagated
		:param tc: theory constraint for timed watches
		:param watches: Not used, just here for compatibility
		"""
		for info in tc.t_atom_names:
			if info.untimed_lit not in self.watch_to_tc:
				self.watch_to_tc[info.untimed_lit] = TAtomConseqs(info.untimed_lit, self.lock_ng)

			self.watch_to_tc[info.untimed_lit].build_conseqs(tc.t_atom_info, tc.min_time, tc.max_time)

	@util.Count(StatNames.PROP_CALLS_MSG.value)
	def propagate(self, control, changes):
		with util.Timer("Propagation-{}".format(str(self.id))):
			for lit in changes:
				for internal_lit in TimeAtomToSolverLit.grab_id(lit):
					# Check meta_ta to see the reason we check if untimed lit is in the mapping
					untimed_lit = Signatures.convert_to_untimed_lit(internal_lit)
					if untimed_lit in self.watch_to_tc:
						if self.watch_to_tc[untimed_lit].propagate(control, (internal_lit, lit)) is None:
							return

	def add_tc(self, tc):
		pass

	def make_tc(self, t_atom):
		size = len(t_atom.elements)
		if size == 1:
			return TheoryConstraintSize1(t_atom)
		elif size == 2:
			util.Count.add(StatNames.SIZE2_COUNT_MSG.value)
			return TheoryConstraint(t_atom, self.lock_ng)
		else:
			raise Exception("Conseqs propagator can not handle constraints of size > 2")

	@util.Count(StatNames.CHECK_CALLS_MSG.value)
	@util.Timer(StatNames.CHECK_TIMER_MSG.value)
	def check(self, control):
		for temporal_atom, ta in self.watch_to_tc.items():
			if ta.check(control) is None:
				# check failed because there was a conflict
				return

class RegularAtomPropagatorNaive(Propagator):
	"""
	Propagator that handles the propagation of "time atoms"(aka theory atoms of theory constraints).
	"""

	__slots__ = []

	@util.Count(StatNames.PROP_CALLS_MSG.value)
	def propagate(self, control, changes):
		with util.Timer("Propagation-{}".format(str(self.id))):
			for lit in changes:
				for tc in self.watch_to_tc[lit]:
					if tc.propagate(control, lit) is None:
						return

	def make_tc(self, t_atom):
		size = len(t_atom.elements)
		if size == 1:
			return TheoryConstraintSize1(t_atom)
		elif size == 2:
			util.Count.add(StatNames.SIZE2_COUNT_MSG.value)
			return TheoryConstraintSize2Prop(t_atom, self.lock_ng)
		else:
			util.Count.add(StatNames.SIZEN_COUNT_MSG.value)
			return TheoryConstraintNaiveProp(t_atom, self.lock_ng)


class RegularAtomPropagator2watch(Propagator):
	"""
	Propagator that handles the propagation of "time atoms"(aka theory atoms of theory constraints).

	Members:
	watch_to_tc                -- Mapping from a literal to a theory constraint.

	theory_constraints          -- List of all theory constraints
	"""
	__slots__ = []

	def __init__(self, id, lock_ng=-1):
		super().__init__(id, lock_ng=lock_ng)

		self.watch_to_tc = defaultdict(list)

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

	@util.Count(StatNames.PROP_CALLS_MSG.value)
	# @profile
	def propagate(self, control, changes):
		with util.Timer("Propagation-{}".format(str(self.id))):
			for lit in changes:
				for tc in set(self.watch_to_tc[lit]):
					result = tc.propagate(control, lit)
					if result is None:
						return

					for delete, add in result:
						self.watch_to_tc[delete].remove(tc)
						self.watch_to_tc[add].append(tc)

						if len(self.watch_to_tc[add]) == 1:
							# if the size is 1 then it contains only the new tc
							# so it wasn't watched before
							control.add_watch(add)

						if self.watch_to_tc[delete] == []:
							control.remove_watch(delete)

	def make_tc(self, t_atom):
		size = len(t_atom.elements)
		if size == 1:
			return TheoryConstraintSize1(t_atom)
		elif size == 2:
			util.Count.add(StatNames.SIZE2_COUNT_MSG.value)
			return TheoryConstraintSize2Prop(t_atom, self.lock_ng)
		else:
			util.Count.add(StatNames.SIZEN_COUNT_MSG.value)
			return TheoryConstraint2watchProp(t_atom, self.lock_ng)


class Propagator1watch(Propagator):
	"""
	Propagator that handles the propagation of "time atoms"(aka theory atoms of theory constraints).

	Members:
	watch_to_tc                -- Mapping from a literal to a theory constraint.

	theory_constraints          -- List of all theory constraints
	"""
	__slots__ = []

	@util.Count(StatNames.PROP_CALLS_MSG.value)
	# @profile
	def propagate(self, control, changes):
		with util.Timer("Propagation-{}".format(str(self.id))):
			for lit in changes:
				for tc in set(self.watch_to_tc[lit]):
					result = tc.propagate(control, lit)
					if result is None:
						return

					for delete, add in result:
						self.watch_to_tc[delete].remove(tc)
						self.watch_to_tc[add].add(tc)

						if len(self.watch_to_tc[add]) == 1:
							# if the size is 1 then it contains only the new tc
							# so it wasn't watched before
							control.add_watch(add)

						if self.watch_to_tc[delete] == []:
							control.remove_watch(delete)

	def make_tc(self, t_atom):
		size = len(t_atom.elements)
		if size == 1:
			return TheoryConstraintSize1(t_atom)
		elif size == 2:
			util.Count.add(StatNames.SIZE2_COUNT_MSG.value)
			return TheoryConstraint1watch(t_atom, self.lock_ng)
		else:
			util.Count.add(StatNames.SIZEN_COUNT_MSG.value)
			return TheoryConstraint1watch(t_atom, self.lock_ng)

class RegularAtomPropagator2watchMap(Propagator):
	"""
	Propagator that handles the propagation of "time atoms"(aka theory atoms of theory constraints).

	Members:
	watch_to_tc                -- Mapping from a literal to a theory constraint.

	theory_constraints          -- List of all theory constraints
	"""
	__slots__ = []

	def add_atom_observer(self, tc, watches, at):
		"""
		Add the tc to the list of tcs to be notified when their respective watches are propagated
		For the given lit, we save the tc along with the respective assigned time
		:param tc: theory constraint for timed watches
		:param watches: List of watches and assigned time pairs
		"""
		if tc.size == 1:
			return

		for lit in watches:
			self.watch_to_tc[lit].add((tc, at))

	def build_watches(self, tc, init):
		for lits, at, all_lits in tc.build_watches(init):
			self.add_atom_observer(tc, lits, at)
			self.watches.update(all_lits)

	@util.Count(StatNames.PROP_CALLS_MSG.value)
	def propagate(self, control, changes):
		with util.Timer("Propagation-{}".format(str(self.id))):
			for lit in changes:
				for tc, at in set(self.watch_to_tc[lit]):
					res = tc.propagate(control, (lit, at))
					if res is None:
						return

					ng, check = res
					if not ng:  # if ng is empty
						continue

					if check == ConstraintCheck.NONE:
						# only update watches if ng was not unit or conflict
						for ng_lit in ng:
							if ng_lit != lit:
								if (tc, at) in self.watch_to_tc[ng_lit]:
									second_watch = ng_lit
									break

						new_watch = get_replacement_watch(ng, [lit, second_watch], control)
						if new_watch is not None:
							self.watch_to_tc[lit].remove((tc, at))
							self.watch_to_tc[new_watch].add((tc, at))

	def make_tc(self, t_atom):
		size = len(t_atom.elements)
		if size == 1:
			return TheoryConstraintSize1(t_atom)
		elif size == 2:
			util.Count.add(StatNames.SIZE2_COUNT_MSG.value)
			return TheoryConstraintSize2Prop2WatchMap(t_atom, self.lock_ng)
		else:
			util.Count.add(StatNames.SIZEN_COUNT_MSG.value)
			return TheoryConstraint2watchPropMap(t_atom, self.lock_ng)


class GrounderPropagator:

	def __init__(self, id, lock_ng=-1):
		GlobalConfig.lock_up_to = 100000000

	@util.Timer(StatNames.INIT_TIMER_MSG.value)
	def init(self, init):
		init_TA2L_mapping_integers(init)

		for t_atom in init.theory_atoms:
			if t_atom.term.name == "constraint":
				self.build_constraints(init, t_atom)

		TimeAtomToSolverLit.reset()

	def build_constraints(self, init, t_atom) -> List[int]:
		t_atom_info, min_time, max_time = parse_atoms(t_atom)

		for assigned_time in range(min_time, max_time + 1):
			lits = form_nogood(t_atom_info, assigned_time)
			if lits is None:
				continue

			init.add_clause([-l for l in lits if l != 1])

	@util.Count(StatNames.CHECK_CALLS_MSG.value)
	@util.Timer(StatNames.CHECK_TIMER_MSG.value)
	def check(self, control):
		pass

	def make_tc(self, t_atom):
		size = len(t_atom.elements)
		if size == 1:
			return TheoryConstraintSize1(t_atom)
		elif size == 2:
			util.Count.add(StatNames.SIZE2_COUNT_MSG.value)
			return TheoryConstraintSize2Prop(t_atom, self.lock_ng)
		else:
			util.Count.add(StatNames.SIZEN_COUNT_MSG.value)
			return TheoryConstraintNaiveProp(t_atom, self.lock_ng)
