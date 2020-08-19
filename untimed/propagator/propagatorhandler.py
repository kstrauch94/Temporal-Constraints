import logging

from untimed.propagator.propagator import ConstraintPropagator
from untimed.propagator.propagator import ConstraintPropagatorMany


from untimed.propagator.theoryconstraint import TheoryConstraintNaive
from untimed.propagator.theoryconstraint import TheoryConstraint2watch
from untimed.propagator.theoryconstraint import TheoryConstraint2watchBig

propagators = {}
propagators["naive"] = TheoryConstraintNaive
propagators["2watch"] = TheoryConstraint2watchBig

theory_file = "untimed/theory/untimed_theory.lp"

class TheoryHandler:

	def __init__(self, prop_type="2watch"):
		self.logger = logging.getLogger(self.__module__ + "." + self.__class__.__name__)

		self.tc_class = propagators[prop_type]

	def add_theory(self, prg):
		prg.load(theory_file)

	def register(self, prg):

		self.propagator = ConstraintPropagator(self.tc_class)

		prg.register_propagator(self.propagator)


	def on_stats(self):

		self.propagator.print_stats()


class TheoryHandlerMany:

	def __init__(self, prop_type="2watch"):
		self.logger = logging.getLogger(self.__module__ + "." + self.__class__.__name__)

		self.tc_class = propagators[prop_type]
		self.propagators = []

	def add_theory(self, prg):
		prg.load(theory_file)

	def register(self, prg):
		# has to be called AFTER grounding!
		for t_atom in prg.theory_atoms:
			if t_atom.term.name == "constraint":
				self.logger.debug(str(t_atom))
				prop = ConstraintPropagatorMany(t_atom, self.tc_class)
				self.propagators.append(prop)

			elif t_atom.term.name == "time":
				self.logger.debug(str(t_atom))
				max_time = int(str(t_atom.elements[0]).replace("+","")[1:-1])
 
		for p in self.propagators:
			# add a max time for the constraint
			# this has to be done before init_watches
			p.add_max_time(max_time)
			
			prg.register_propagator(p)	

	def on_stats(self):
		print("IMPLEMENT STATS PLEASE")
		#self.propagator.print_stats()