import logging
import os
from typing import List

from untimed import util

from untimed.propagator.theoryconstraint_base import TheoryConstraintSize1
from untimed.propagator.theoryconstraint_base import parse_signature

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
from untimed.propagator.theoryconstraint_prop import TheoryConstraintMetaProp
from untimed.propagator.theoryconstraint_prop import TheoryConstraintCountProp


from untimed.propagator.propagator import TimedAtomPropagator
from untimed.propagator.propagator import CountPropagator
from untimed.propagator.propagator import MetaPropagator
from untimed.propagator.propagator import MetaTAtomPropagator
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

META_TC = {1: TheoryConstraintSize1,
            2: TheoryConstraintMetaProp,
            -1: TheoryConstraintMetaProp}

META_TATOM_TC = {1: TheoryConstraintSize1,
            2: TheoryConstraint,
            -1: TheoryConstraint}

COUNT_TC = {1: TheoryConstraintSize1,
            2: TheoryConstraintSize2TimedProp,
            -1: TheoryConstraintCountProp}

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
           "2watchmap_prop": TWO_WATCH_MAP_TC_PROP,
           "meta_prop": META_TC,
           "meta_ta_prop": META_TATOM_TC,
           "count_prop": COUNT_TC}

PROPAGATORS = {"timed": TimedAtomPropagator,
               "meta": MetaPropagator,
               "meta_ta":MetaTAtomPropagator,
               "naive": RegularAtomPropagatorNaive,
               "2watch": RegularAtomPropagator2watch,
               "2watchmap": RegularAtomPropagator2watchMap,
               "count": CountPropagator}


def build_tc(t_atom, tc_dict) -> TheoryConstraint:
	"""
	return an appropriate TheoryConstraint object for the given theory atom size
	:param t_atom: theory atom
	:param tc_dict: theory constraint size dict
	:return: TheoryConstraint object
	"""
	size = len(t_atom.elements)
	if size in tc_dict:
		util.Count.add("size_{}".format(size))
		return tc_dict[size](t_atom)
	else:
		util.Count.add("size_{}".format(-1))
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
		for t_atom in prg.theory_atoms:
			if t_atom.term.name == "constraint":
				tc = build_tc(t_atom, TC_DICT[self.prop_type])

				prg.register_propagator(tc)

	def __str__(self) -> str:
		return self.__class__.__name__ + " with propagator type {}".format(self.prop_type)


class TheoryHandlerWithPropagator:

	def __init__(self, prop_type: str = "timed") -> None:

		self.logger = logging.getLogger(self.__module__ + "." + self.__class__.__name__)

		if prop_type + "_prop" not in TC_DICT:
			raise ValueError("Propagator Handler does not support {} watch type".format(prop_type))

		self.tc_dict = TC_DICT[prop_type + "_prop"]

		self.propagator = PROPAGATORS[prop_type](lambda t_atom : build_tc(t_atom, self.tc_dict))

	@util.Timer("Register")
	def register(self, prg) -> None:
		"""
		This function needs to be called AFTER grounding
		because it relies on looking at the grounded theory atoms
		to create a propagator for each one
		"""
		for t_atom in prg.theory_atoms:
			if t_atom.term.name == "signature":
				parse_signature(t_atom)

		prg.register_propagator(self.propagator)

	def __str__(self) -> str:
		return self.__class__.__name__
