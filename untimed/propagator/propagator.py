import logging

import untimed.util as util

from typing import Any, List

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
	"""
	return an appropriate TheoryConstraint object for the given theory atom size
	:param t_atom: theory atom
	:param tc_dict: theory constraint size dict
	:return: TheoryConstraint object
	"""
	l = len(t_atom.elements)
	if l in tc_dict:
		return tc_dict[l](t_atom)
	else:
		return tc_dict[-1](t_atom)


class ConstraintPropagator:
	"""
	This implements the Propagator interface for clingo.

	Members:

	constraints             -- List of the theory constraints handled by this propagator

	prop_type               -- The type of propagator (Either naive or 2watch)

	prop_init               -- Flag that says if the constraint should propagate on the init call
	"""

	def __init__(self, prop_type="2watch", prop_init: bool = True):
		self.logger = logging.getLogger(self.__module__ + "." + self.__class__.__name__)

		self.constraints: List[Any] = []

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

	@util.Count("Propagation")
	@util.Timer("Propagation")
	def propagate(self, control, changes):

		for tc in self.constraints:
			if not tc.propagate(control, changes):
				return

	@util.Count("Undo")
	@util.Timer("Undo")
	def undo(self, thread_id, assign, changes):

		for tc in self.constraints:
			tc.undo(thread_id, assign, changes)


class ConstraintPropagatorMany:
	"""
	This implements the Propagator interface for clingo.

	Members:

	constraint              -- The theory constraint handled by this propagator

	prop_type               -- The type of propagator (Either naive or 2watch)

	prop_init               -- Flag that says if the constraint should propagate on the init call
	"""

	def __init__(self, t_atom, prop_type="2watch", prop_init=True):
		self.logger = logging.getLogger(self.__module__ + "." + self.__class__.__name__)

		self.constraint = build_tc(t_atom, TC_DICT[prop_type])

		self.prop_type = prop_type

		self.prop_init = prop_init

	@util.Timer("Init")
	def init(self, init):

		self.constraint.init(init, self.prop_init)

	# @util.Timer("Propagation")
	@util.Count("Propagation")
	def propagate(self, control, changes):
		with util.Timer("Propagation"):
			return self.constraint.propagate(control, changes)

	@util.Timer("Undo")
	@util.Count("Undo")
	def undo(self, thread_id, assign, changes):

		self.constraint.undo(thread_id, assign, changes)
