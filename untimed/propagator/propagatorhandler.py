import logging
import os
from typing import List

from untimed import util

from untimed.propagator.theoryconstraint_base import TheoryConstraintSize1

from untimed.propagator.theoryconstraint_reg import TheoryConstraint
from untimed.propagator.theoryconstraint_reg import TheoryConstraintNaiveReg
from untimed.propagator.theoryconstraint_reg import TheoryConstraint2watchReg
from untimed.propagator.theoryconstraint_reg import TheoryConstraintSize2Reg

from untimed.propagator.theoryconstraint_prop import TheoryConstraintSize2Prop
from untimed.propagator.theoryconstraint_prop import TheoryConstraintNaiveProp
from untimed.propagator.theoryconstraint_prop import TheoryConstraint2watchProp
from untimed.propagator.theoryconstraint_prop import TheoryConstraintSize2Prop2WatchMap
from untimed.propagator.theoryconstraint_prop import TheoryConstraint2watchPropMap
from untimed.propagator.theoryconstraint_prop import TheoryConstraintSize2TimedProp
from untimed.propagator.theoryconstraint_prop import TheoryConstraintTimedProp


from untimed.propagator.propagator import TimedAtomPropagator
from untimed.propagator.propagator import RegularAtomPropagatorNaive
from untimed.propagator.propagator import RegularAtomPropagator2watch
from untimed.propagator.propagator import RegularAtomPropagator2watchMap


theory_file = os.path.abspath(os.path.join(os.path.dirname(__file__), "../theory/untimed_theory.lp"))

TWO_WATCH_TC = {1: TheoryConstraintSize1,
                2: TheoryConstraintSize2Reg,
                -1: TheoryConstraint2watchReg}

NAIVE_TC = {1: TheoryConstraintSize1,
            2: TheoryConstraintSize2Reg,
            -1: TheoryConstraintNaiveReg}

TIMED_TC = {1: TheoryConstraintSize1,
            2: TheoryConstraintSize2TimedProp,
            -1: TheoryConstraintTimedProp}

NAIVE_TC_PROP = {1: TheoryConstraintSize1,
                 2: TheoryConstraintSize2Prop,
                 -1: TheoryConstraintNaiveProp}

TWO_WATCH_TC_PROP = {1: TheoryConstraintSize1,
                     2: TheoryConstraintSize2Prop,
                     -1: TheoryConstraint2watchProp}

TWO_WATCH_MAP_TC_PROP = {1: TheoryConstraintSize1,
                     2: TheoryConstraintSize2Prop2WatchMap,
                     -1: TheoryConstraint2watchPropMap}

TC_DICT = {"2watch": TWO_WATCH_TC,
           "naive": NAIVE_TC,
           "timed_prop": TIMED_TC,
           "naive_prop": NAIVE_TC_PROP,
           "2watch_prop": TWO_WATCH_TC_PROP,
           "2watchmap_prop": TWO_WATCH_MAP_TC_PROP}

PROPAGATORS = {"timed": TimedAtomPropagator,
               "naive": RegularAtomPropagatorNaive,
               "2watch": RegularAtomPropagator2watch,
               "2watchmap": RegularAtomPropagator2watchMap}


def build_tc(t_atom, tc_dict) -> TheoryConstraint:
	"""
	return an appropriate TheoryConstraint object for the given theory atom size
	:param t_atom: theory atom
	:param tc_dict: theory constraint size dict
	:return: TheoryConstraint object
	"""
	size = len(t_atom.elements)
	if size in tc_dict:
		return tc_dict[size](t_atom)
	else:
		return tc_dict[-1](t_atom)


def add_theory(prg) -> None:
	prg.load(theory_file)


class TheoryHandler:

	def __init__(self, prop_type: str = "2watch") -> None:
		"""
		:param prop_type: type of propagator for general nogoods ["2watch", "naive"]
		"""
		self.logger = logging.getLogger(self.__module__ + "." + self.__class__.__name__)

		if prop_type not in TC_DICT:
			raise ValueError("Handler does not support {} watch type".format(prop_type))

		self.prop_type: str = prop_type

	@util.Timer("Register")
	def register(self, prg) -> None:
		"""
		This function needs to be called AFTER grounding
		because it relies on looking at the grounded theory atoms 
		to create a propagator for each one
		"""
		theory_constraints: List[TheoryConstraint] = []
		for t_atom in prg.theory_atoms:
			if t_atom.term.name == "constraint":
				tc = build_tc(t_atom, TC_DICT[self.prop_type])
				theory_constraints.append(tc)

				prg.register_propagator(tc)

	def __str__(self) -> str:
		return self.__class__.__name__ + " with propagator type {}".format(self.prop_type)


class TheoryHandlerWithPropagator:

	def __init__(self, prop_type: str = "timed") -> None:

		self.logger = logging.getLogger(self.__module__ + "." + self.__class__.__name__)

		if prop_type + "_prop" not in TC_DICT:
			raise ValueError("Propagator Handler does not support {} watch type".format(prop_type))

		self.propagator = PROPAGATORS[prop_type]()

		self.tc_dict = TC_DICT[prop_type + "_prop"]

	@util.Timer("Register")
	def register(self, prg) -> None:
		"""
		This function needs to be called AFTER grounding
		because it relies on looking at the grounded theory atoms
		to create a propagator for each one
		"""
		for t_atom in prg.theory_atoms:
			if t_atom.term.name == "constraint":
				tc = build_tc(t_atom, self.tc_dict)
				self.propagator.add_tc(tc)

		prg.register_propagator(self.propagator)

	def __str__(self) -> str:
		return self.__class__.__name__
