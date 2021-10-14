import logging
import os

import clingo

from untimed import util

from untimed.propagator.theoryconstraint_data import StatNames

from untimed.propagator.theoryconstraint_base import parse_signature

from untimed.propagator.propagator import TimedAtomPropagator
from untimed.propagator.propagator import TimedAtomAllWatchesPropagator
from untimed.propagator.propagator import CountPropagator
from untimed.propagator.propagator import MetaPropagator
from untimed.propagator.propagator import MetaTAtomPropagator
from untimed.propagator.propagator import RegularAtomPropagatorNaive
from untimed.propagator.propagator import RegularAtomPropagator2watch
from untimed.propagator.propagator import RegularAtomPropagator2watchMap
from untimed.propagator.propagator import TimedAtomPropagatorCheck
from untimed.propagator.propagator import ConseqsPropagator
from untimed.propagator.propagator import Propagator1watch
from untimed.propagator.propagator import GrounderPropagator

theory_file = os.path.abspath(os.path.join(os.path.dirname(__file__), "../theory/untimed_theory.lp"))

PROPAGATORS = {"timed": TimedAtomPropagator,
			"timed_aw": TimedAtomAllWatchesPropagator,
			"meta": MetaPropagator,
			"meta_ta":MetaTAtomPropagator,
			"naive": RegularAtomPropagatorNaive,
			"2watch": RegularAtomPropagator2watch,
			"2watchmap": RegularAtomPropagator2watchMap,
			"count": CountPropagator,
			"check": TimedAtomPropagatorCheck,
			"conseq": ConseqsPropagator,
			"1watch": Propagator1watch,
			"ground": GrounderPropagator}

def add_theory(prg) -> None:
	prg.load(theory_file)


class TheoryHandler:

	supported_types = PROPAGATORS.keys()


	def __init__(self, prop_type: str = "timed", lock_ng=-1, ignore_id=clingo.Flag(False)) -> None:

		self.logger = logging.getLogger(self.__module__ + "." + self.__class__.__name__)

		if prop_type not in TheoryHandler.supported_types:
			raise ValueError("Propagator Handler does not support {} watch type".format(prop_type))

		self.propagator = lambda id: PROPAGATORS[prop_type](id, lock_ng)

		self.prop_ids = set()

		self.ignore_id = ignore_id.flag

	@util.Timer(StatNames.REGISTER_TIMER_MSG.value)
	def register(self, prg) -> None:
		"""
		This function needs to be called AFTER grounding
		because it relies on looking at the grounded theory atoms
		to create a propagator for each one
		"""
		t_atom_count = 0
		for t_atom in prg.theory_atoms:
			if t_atom.term.name == "signature":
				parse_signature(t_atom)
				util.Count.add(StatNames.SIG_COUNT_MSG.value)

			else:
				util.Count.add(StatNames.TC_COUNT_MSG.value)

				if not self.ignore_id and t_atom.term.name == "constraint":
					id = t_atom.term.arguments[-1].name
					self.prop_ids.add(id)

		if self.ignore_id:
			self.prop_ids.add(None)

		for id in self.prop_ids:
			prg.register_propagator(self.propagator(id))

	def __str__(self) -> str:
		return self.__class__.__name__
