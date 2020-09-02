import clingo
import logging

import sys
import untimed.util as util
import time as time_module
from collections import defaultdict

from typing import Any, List, Dict, Union, Optional

from untimed.propagator.theoryconstraint import TheoryConstraintNaive
from untimed.propagator.theoryconstraint import TheoryConstraint2watchBig


class ConstraintPropagator:

	def __init__(self, tc_class: Any = TheoryConstraint2watchBig, prop_init: bool = True):
		self.logger = logging.getLogger(self.__module__ + "." + self.__class__.__name__)

		self.constraints: List[Any] = []
		self.max_time: Optional[int] = None

		self.tc_class = tc_class

		self.prop_init = prop_init
	
	@util.Timer("Init")
	def init(self, init):

		for t_atom in init.theory_atoms:
			if t_atom.term.name == "constraint":
				self.logger.debug(str(t_atom))
				self.constraints.append(self.tc_class(t_atom))
				
		for c in self.constraints:
			for sig in c.atom_signatures:
				for s_atom in init.symbolic_atoms.by_signature(*sig):
					c.init_watches(s_atom, init)
			if self.prop_init:
				c.propagate_init(init)

			c.build_watches(init)
	
	@util.Count("propagation")
	@util.Timer("Propagation")
	def propagate(self, control, changes):
		
		all_nogoods = []
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

	def __init__(self, t_atom, tc_class=TheoryConstraint2watchBig, prop_init=True):
		self.logger = logging.getLogger(self.__module__ + "." + self.__class__.__name__)

		self.constraint = tc_class(t_atom)

		self.lit_to_constraints = {}

		self.tc_class = tc_class
	
		self.prop_init = prop_init


	def add_max_time(self, max_time):
		self.constraint.add_max_time(max_time)

	@util.Timer("Init")
	def init(self, init):
		
		for sig in self.constraint.atom_signatures:
			for s_atom in init.symbolic_atoms.by_signature(*sig):
				self.constraint.init_watches(s_atom, init)

		if self.prop_init:
			self.constraint.propagate_init(init)

		self.constraint.build_watches(init)
	
	#@util.Timer("Propagation")
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
