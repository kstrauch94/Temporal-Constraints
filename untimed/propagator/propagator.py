import logging

import untimed.util as util

from typing import Any, List, Dict, Union, Optional

from untimed.propagator.theoryconstraint import TheoryConstraintNaive
from untimed.propagator.theoryconstraint import TheoryConstraint2watch
from untimed.propagator.theoryconstraint import TheoryConstraintSize1
from untimed.propagator.theoryconstraint import TheoryConstraintSize2

TWO_WATCH_TC = {1: TheoryConstraintSize1,
                2: TheoryConstraintSize2,
                -1: TheoryConstraint2watch}

NAIVE_TC = {1: TheoryConstraintSize1,
            2: TheoryConstraintSize2,
            -1: TheoryConstraintNaive}


TC_DICT = {"2watch": TWO_WATCH_TC,
           "naive" : NAIVE_TC}


def build_tc(t_atom, tc_dict):
	l = len(t_atom.elements)
	if l in tc_dict:
		return tc_dict[l](t_atom)
	else:
		return tc_dict[-1](t_atom)


class ConstraintPropagator:

	def __init__(self, prop_type="2watch", prop_init: bool = True):
		self.logger = logging.getLogger(self.__module__ + "." + self.__class__.__name__)

		self.constraints: List[Any] = []
		self.max_time: Optional[int] = None

		self.prop_type = prop_type

		self.prop_init = prop_init

	@util.Timer("Init")
	def init(self, init):

		for t_atom in init.theory_atoms:
			if t_atom.term.name == "constraint":
				self.logger.debug(str(t_atom))
				self.constraints.append(build_tc(t_atom, TC_DICT[self.prop_type]))

		for c in self.constraints:
			c.init(init, self.prop_init)

	@util.Count("propagation")
	@util.Timer("Propagation")
	def propagate(self, control, changes):

		for tc in self.constraints:
			tc.propagate(control, changes)
			if not control.propagate():
				return

	@util.Count("undo")
	@util.Timer("undo")
	def undo(self, thread_id, assign, changes):

		for tc in self.constraints:
			tc.undo(thread_id, assign, changes)

	def print_stats(self):
		print(f"{self.__class__.__name__} Propagator stats")
		for name, time in util.Timer.timers.items():
			print(f"{name:15}:\t{time}")

		for name, count in util.Count.counts.items():
			print(f"{name:15}:\t{count}")

		print("DONE")


class ConstraintPropagatorMany:

	def __init__(self, t_atom, prop_type="2watch", prop_init=True):
		self.logger = logging.getLogger(self.__module__ + "." + self.__class__.__name__)

		self.constraint = build_tc(t_atom, TC_DICT[prop_type])

		self.lit_to_constraints = {}

		self.prop_type = prop_type

		self.prop_init = prop_init

	def add_max_time(self, max_time):
		self.constraint.add_max_time(max_time)

	@util.Timer("Init")
	def init(self, init):

		self.constraint.init(init, self.prop_init)

	# @util.Timer("Propagation")
	@util.Count("propagation")
	def propagate(self, control, changes):
		with util.Timer("Propagation"):
			self.constraint.propagate(control, changes)
			if not control.propagate():
				return

	@util.Timer("undo")
	@util.Count("undo")
	def undo(self, thread_id, assign, changes):

		self.constraint.undo(thread_id, assign, changes)

	def print_stats(self):
		print(f"{self.__class__.__name__} Propagator stats")
		for name, time in util.Timer.timers.items():
			print(f"{name:15}:\t{time}")

		for name, count in util.Count.counts.items():
			print(f"{name:15}:\t{count}")

		print("DONE")
