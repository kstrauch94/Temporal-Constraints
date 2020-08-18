from propagator.propagator import ConstraintPropagator2
from propagator.theoryconstraint import TheoryConstraintNaive, TheoryConstraint2watch

propagators = {}
propagators["naive"] = TheoryConstraintNaive
propagators["2watch"] = TheoryConstraint2watch

theory_file = "propagator/theory/untimed_theory.lp"

class TheoryHandler:

	def __init__(self, prop_type="2watch"):

		self.tc_class = propagators[prop_type]

	def register(self, prg):

		self.propagator = ConstraintPropagator2(self.tc_class)

		prg.register_propagator(self.propagator)

		prg.load(theory_file)

	def on_stats(self):

		self.propagator.print_stats()
