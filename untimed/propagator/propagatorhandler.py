import logging
import os
from typing import Dict, Any, List

from untimed.propagator.propagator import ConstraintPropagator
from untimed.propagator.propagator import ConstraintPropagatorMany

from untimed.propagator.theoryconstraint import TheoryConstraintNaive
from untimed.propagator.theoryconstraint import TheoryConstraint2watch
from untimed.propagator.theoryconstraint import TheoryConstraint2watchBig

propagators: Dict[str, Any] = {}
propagators["naive"] = TheoryConstraintNaive
propagators["2watch"] = TheoryConstraint2watchBig


theory_file = os.path.abspath(os.path.join(os.path.dirname(__file__), "../theory/untimed_theory.lp"))

class TheoryHandler:

	def __init__(self, prop_type: str = "2watch", prop_init: bool = True):
		self.logger = logging.getLogger(self.__module__ + "." + self.__class__.__name__)

		self.tc_class = propagators[prop_type]

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
		self.propagator = ConstraintPropagator(self.tc_class, self.prop_init)

		prg.register_propagator(self.propagator)

	def on_stats(self) -> None:

		self.propagator.print_stats()

	def __str__(self) -> str:
		return(self.__class__.__name__ + " with propagator type {}".format(self.prop_type))

class TheoryHandlerMany:

	def __init__(self, prop_type: str = "2watch", prop_init: bool = True):
		self.logger = logging.getLogger(self.__module__ + "." + self.__class__.__name__)

		self.tc_class = propagators[prop_type]
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
				prop = ConstraintPropagatorMany(t_atom, self.tc_class, self.prop_init)
				self.propagators.append(prop)

			elif t_atom.term.name == "time":
				self.logger.debug(str(t_atom))
				max_time = int(str(t_atom.elements[0]).replace("+","")[1:-1])
 
		for p in self.propagators:
			# add a max time for the constraint
			# this has to be done before init_watches
			p.add_max_time(max_time)
			
			prg.register_propagator(p)	

	def on_stats(self) -> None:
		self.propagators[0].print_stats()

	def __str__(self) -> str:
		return self.__class__.__name__ + " with propagator type {}".format(self.prop_type)
