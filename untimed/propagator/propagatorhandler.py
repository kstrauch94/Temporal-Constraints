import logging
import os
from typing import Dict, Any, List

from untimed.propagator.propagator import ConstraintPropagator
from untimed.propagator.propagator import ConstraintPropagatorMany

theory_file = os.path.abspath(os.path.join(os.path.dirname(__file__), "../theory/untimed_theory.lp"))


class TheoryHandler:

	def __init__(self, prop_type: str = "2watch", prop_init: bool = True):
		self.logger = logging.getLogger(self.__module__ + "." + self.__class__.__name__)

		self.prop_type = prop_type

		self.prop_init = prop_init

	def add_theory(self, prg) -> None:
		prg.load(theory_file)

	def register(self, prg) -> None:
		"""
		Unlike TheoryHandlerMany, this can be called before
		grounding since the ConstraintPropagator takes care
		of reading the theory atoms when the init call is made
		to the propagator
		"""
		self.propagator = ConstraintPropagator(self.prop_type, self.prop_init)

		prg.register_propagator(self.propagator)

	def on_stats(self) -> None:
		self.propagator.print_stats()

	def __str__(self) -> str:
		return self.__class__.__name__ + " with propagator type {}".format(self.prop_type)


class TheoryHandlerMany:

	def __init__(self, prop_type: str = "2watch", prop_init: bool = True):
		self.logger = logging.getLogger(self.__module__ + "." + self.__class__.__name__)

		self.propagators: List[ConstraintPropagatorMany] = []

		self.prop_type: str = prop_type

		self.prop_init: bool = prop_init

	def add_theory(self, prg) -> None:
		prg.load(theory_file)

	def register(self, prg) -> None:
		"""
		This function needs to be called AFTER grounding
		because it relies on looking at the grounded theory atoms 
		to create a propagator for each one
		"""
		for t_atom in prg.theory_atoms:
			if t_atom.term.name == "constraint":
				self.logger.debug(str(t_atom))
				prop = ConstraintPropagatorMany(t_atom, self.prop_type, self.prop_init)
				self.propagators.append(prop)

		for p in self.propagators:
			prg.register_propagator(p)

	def on_stats(self) -> None:
		if self.propagators:
			self.propagators[0].print_stats()

	def __str__(self) -> str:
		return self.__class__.__name__ + " with propagator type {}".format(self.prop_type)
