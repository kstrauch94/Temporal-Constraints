import logging
import os
from typing import List

from untimed.propagator.theoryconstraint import TheoryConstraint
from untimed.propagator.theoryconstraint import TheoryConstraintNaive
from untimed.propagator.theoryconstraint import TheoryConstraint2watch
from untimed.propagator.theoryconstraint import TheoryConstraintSize1
from untimed.propagator.theoryconstraint import TheoryConstraintSize2

from untimed.propagator.theoryconstraint import TimedAtomPropagator

from untimed.propagator.theoryconstraint import TheoryConstraintSize2Timed
from untimed.propagator.theoryconstraint import TheoryConstraintNaiveTimed




theory_file = os.path.abspath(os.path.join(os.path.dirname(__file__), "../theory/untimed_theory.lp"))


TWO_WATCH_TC = {1: TheoryConstraintSize1,
				2: TheoryConstraintSize2,
				-1: TheoryConstraint2watch}

NAIVE_TC = {1: TheoryConstraintSize1,
			2: TheoryConstraintSize2,
			-1: TheoryConstraintNaive}

TIMED_TC = {1: TheoryConstraintSize1,
			2: TheoryConstraintSize2Timed,
			-1: TheoryConstraintNaiveTimed}


TC_DICT = {"2watch": TWO_WATCH_TC,
		   "naive" : NAIVE_TC,
		   "timed_watch": TIMED_TC}


def build_tc(t_atom, tc_dict) -> TheoryConstraint:
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


def add_theory(prg) -> None:
	prg.load(theory_file)


class TheoryHandler:

	def __init__(self, prop_type: str = "2watch") -> None:
		"""
		:param prop_type: type of propagator for general nogoods ["2watch", "naive"]
		"""
		self.logger = logging.getLogger(self.__module__ + "." + self.__class__.__name__)

		self.propagators: List[TheoryConstraint] = []

		self.prop_type: str = prop_type

	def register(self, prg) -> None:
		"""
		This function needs to be called AFTER grounding
		because it relies on looking at the grounded theory atoms 
		to create a propagator for each one
		"""
		for t_atom in prg.theory_atoms:
			if t_atom.term.name == "constraint":
				tc = build_tc(t_atom, TC_DICT[self.prop_type])
				self.propagators.append(tc)

				prg.register_propagator(tc)

	def __str__(self) -> str:
		return self.__class__.__name__ + " with propagator type {}".format(self.prop_type)


class TheoryHandlerTimedWatch:

	def __init__(self) -> None:

		self.logger = logging.getLogger(self.__module__ + "." + self.__class__.__name__)

		self.propagator = TimedAtomPropagator()

	def register(self, prg) -> None:
		"""
		This function needs to be called AFTER grounding
		because it relies on looking at the grounded theory atoms
		to create a propagator for each one
		"""
		for t_atom in prg.theory_atoms:
			if t_atom.term.name == "constraint":
				tc = build_tc(t_atom, TC_DICT["timed_watch"])
				self.propagator.add_tc(tc)

		prg.register_propagator(self.propagator)

	def __str__(self) -> str:
		return self.__class__.__name__