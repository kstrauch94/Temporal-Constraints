import unittest
from untimed.propagator.propagatorhandler import TheoryHandler, TheoryHandlerWithPropagator, add_theory
from untimed.propagator.theoryconstraint_data import TimeAtomToSolverLit, Signatures

import clingo

program = """
#const maxtime = 3.
time(1..maxtime).
domain_ab(1..2).

{a(V,T)} :- domain_ab(V), time(T).
{b(V,T)} :- domain_ab(V), time(T).

"""

program_no_dom = """
#const maxtime = 7.
time(1..maxtime).

{a(T)} :- time(T).
{b(T)} :- time(T).

"""


def parse_model(m):
	ret = []
	for sym in m.symbols(shown=True):
		ret.append(sym)

	return list(map(str, sorted(ret)))


def solve(programs, handler_class, handler_args, print_r=False):
	r = []

	handler = handler_class(**handler_args)

	prg = clingo.Control(['0'], message_limit=0)

	for p in programs:
		prg.add("base", [], p)

	add_theory(prg)

	prg.ground([("base", [])])

	handler.register(prg)

	prg.solve(on_model=lambda m: r.append(parse_model(m)))

	if print_r:
		print("solve")
		print(sorted(r))
		print(len(r))

	return sorted(r)


def solve_regular(programs, print_r=False):
	r = []

	prg = clingo.Control(['0'], message_limit=0)

	for p in programs:
		prg.add("base", [], p)

	prg.ground([("base", [])])

	prg.solve(on_model=lambda m: r.append(parse_model(m)))

	if print_r:
		print("solve reg")
		print(sorted(r))
		print(len(r))

	return sorted(r)


class TestApp(unittest.TestCase):

	def reset_mappings(self):
		TimeAtomToSolverLit.reset()
		Signatures.reset()

	def test_naive_regular(self):
		self.reset_mappings()
		handler_class = TheoryHandler
		handler_args = {"prop_type": "naive"}

		self.handler_test(handler_class, handler_args)

	def test_2watch_regular(self):
		self.reset_mappings()
		handler_class = TheoryHandler
		handler_args = {"prop_type": "2watch"}

		self.handler_test(handler_class, handler_args)

	def test_timed_prop(self):
		self.reset_mappings()
		handler_class = TheoryHandlerWithPropagator
		handler_args = {"prop_type": "timed"}

		self.handler_test(handler_class, handler_args)

	def test_timed_aw_prop(self):
		self.reset_mappings()
		handler_class = TheoryHandlerWithPropagator
		handler_args = {"prop_type": "timed_aw"}

		self.handler_test(handler_class, handler_args)
	def test_meta_prop(self):
		self.reset_mappings()
		handler_class = TheoryHandlerWithPropagator
		handler_args = {"prop_type": "meta"}

		self.handler_test(handler_class, handler_args)

	def test_meta_ta_prop(self):
		self.reset_mappings()
		handler_class = TheoryHandlerWithPropagator
		handler_args = {"prop_type": "meta_ta"}

		self.handler_test(handler_class, handler_args)

	def test_count_prop(self):
		self.reset_mappings()
		handler_class = TheoryHandlerWithPropagator
		handler_args = {"prop_type": "count"}

		self.handler_test(handler_class, handler_args)

	def test_naive_prop(self):
		self.reset_mappings()
		handler_class = TheoryHandlerWithPropagator
		handler_args = {"prop_type": "naive"}

		self.handler_test(handler_class, handler_args)

	def test_2watch_prop(self):
		self.reset_mappings()
		handler_class = TheoryHandlerWithPropagator
		handler_args = {"prop_type": "2watch"}

		self.handler_test(handler_class, handler_args)

	def test_2watchmap_prop(self):
		self.reset_mappings()
		handler_class = TheoryHandlerWithPropagator
		handler_args = {"prop_type": "2watchmap"}

		self.handler_test(handler_class, handler_args)

	def handler_test(self, handler_class, handler_args):

		# tests with atoms only having time

		c = "&constraint(1,maxtime){+.a()}. &signature{++a()}."
		c_reg = ":- a(T), time(T)."
		self.assertEqual(solve([program_no_dom, c], handler_class, handler_args),
		                 solve_regular([program_no_dom, c_reg]))

		self.reset_mappings()
		c = "&constraint(1,maxtime){+.a(); +.b()}. &signature{++a() ; ++b()}."
		c_reg = ":- a(T), b(T), time(T)."
		self.assertEqual(solve([program_no_dom, c], handler_class, handler_args),
		                 solve_regular([program_no_dom, c_reg]))

		self.reset_mappings()
		c = "&constraint(1,maxtime){+.a(); +~b()}. &signature{++a() ; ++b()}."
		c_reg = ":- a(T), b(T-1), time(T)."
		self.assertEqual(solve([program_no_dom, c], handler_class, handler_args),
		                 solve_regular([program_no_dom, c_reg]))

		self.reset_mappings()
		c = "&constraint(1,maxtime){+.a(); -~b()}. &signature{++a() ; --b()}."
		c_reg = ":- a(T), not b(T-1), time(T)."
		self.assertEqual(solve([program_no_dom, c], handler_class, handler_args),
		                 solve_regular([program_no_dom, c_reg]))


		# tests with constraints of size 1
		self.reset_mappings()
		c = """&constraint(1,maxtime){+.a(1)}. &signature{++a(1)}."""
		c_reg = ":- a(1,T), time(T)."
		self.assertEqual(solve([program, c], handler_class, handler_args),
		                 solve_regular([program, c_reg]))

		self.reset_mappings()
		c = """&constraint(1,maxtime){-.a(1)}. &signature{--a(1)}."""
		c_reg = ":- not a(1,T), time(T)."
		self.assertEqual(solve([program, c], handler_class, handler_args),
		                 solve_regular([program, c_reg]))

		self.reset_mappings()
		c = """&constraint(1,maxtime){-~a(1)}. &signature{--a(1)}."""
		c_reg = ":- not a(1,T-1), time(T)."
		self.assertEqual(solve([program, c], handler_class, handler_args),
		                 solve_regular([program, c_reg]))

		self.reset_mappings()
		c = """&constraint(1,maxtime){+~a(1)}. &signature{++a(1)}."""
		c_reg = ":- a(1,T-1), time(T)."
		self.assertEqual(solve([program, c], handler_class, handler_args),
		                 solve_regular([program, c_reg]))

		# tests with constraints of size 2

		self.reset_mappings()
		c = """&constraint(1,maxtime){+.a(1); +.b(1)}. &signature{++a(1) ; ++b(1)}."""
		c_reg = ":- a(1,T), b(1,T), time(T)."
		self.assertEqual(solve([program, c], handler_class, handler_args),
		                 solve_regular([program, c_reg]))

		self.reset_mappings()
		c = """&constraint(1,maxtime){+.a(1); -.b(1)}. &signature{++a(1) ; --b(1)}."""
		c_reg = ":- a(1,T), not b(1,T), time(T)."
		self.assertEqual(solve([program, c], handler_class, handler_args),
		                 solve_regular([program, c_reg]))

		self.reset_mappings()
		c = """&constraint(1,maxtime){-.a(1); -.b(1)}.  &signature{--a(1) ; --b(1)}."""
		c_reg = ":- not a(1,T), not b(1,T), time(T)."
		self.assertEqual(solve([program, c], handler_class, handler_args),
		                 solve_regular([program, c_reg]))

		self.reset_mappings()
		c = """&constraint(1,maxtime){-.a(1); +.b(1)}.  &signature{--a(1) ; ++b(1)}."""
		c_reg = ":- not a(1,T), b(1,T), time(T)."
		self.assertEqual(solve([program, c], handler_class, handler_args),
		                 solve_regular([program, c_reg]))

		self.reset_mappings()
		c = """&constraint(1,maxtime){+~a(1); -.b(1)}.  &signature{++a(1) ; --b(1)}."""
		c_reg = ":- a(1,T-1), not b(1,T), time(T)."
		self.assertEqual(solve([program, c], handler_class, handler_args),
		                 solve_regular([program, c_reg]))

		self.reset_mappings()
		c = """&constraint(1,maxtime){-~a(1); +.b(1)}.  &signature{--a(1) ; ++b(1)}."""
		c_reg = ":- not a(1,T-1), b(1,T), time(T)."
		self.assertEqual(solve([program, c], handler_class, handler_args),
		                 solve_regular([program, c_reg]))

		self.reset_mappings()
		c = """&constraint(1,maxtime){-~a(1); -.b(1)}.  &signature{--a(1) ; --b(1)}."""
		c_reg = ":- not a(1,T-1), not b(1,T), time(T)."
		self.assertEqual(solve([program, c], handler_class, handler_args),
		                 solve_regular([program, c_reg]))

		self.reset_mappings()
		c = """&constraint(1,maxtime){-~a(1); -~b(1)}.  &signature{--a(1) ; --b(1)}."""
		c_reg = ":- not a(1,T-1), not b(1,T-1), time(T)."
		self.assertEqual(solve([program, c], handler_class, handler_args),
		                 solve_regular([program, c_reg]))

		# size 2 but with same atom

		self.reset_mappings()
		c = """&constraint(1,maxtime){+.a(1); +~a(1)}.  &signature{++a(1)}."""
		c_reg = ":- a(1,T), a(1,T-1), time(T)."
		self.assertEqual(solve([program, c], handler_class, handler_args),
		                 solve_regular([program, c_reg]))

		self.reset_mappings()
		c = """&constraint(1,maxtime){-.a(1); -~a(1)}.  &signature{--a(1)}."""
		c_reg = ":- not a(1,T), not a(1,T-1), time(T)."
		self.assertEqual(solve([program, c], handler_class, handler_args),
		                 solve_regular([program, c_reg]))

		self.reset_mappings()
		c = """&constraint(1,maxtime){+.a(1); -~a(1)}.  &signature{++a(1) ; --a(1)}."""
		c_reg = ":- a(1,T), not a(1,T-1), time(T)."
		self.assertEqual(solve([program, c], handler_class, handler_args),
		                 solve_regular([program, c_reg]))

		# tests with size > 2

		self.reset_mappings()
		c = """&constraint(1,maxtime){+.a(1); +.b(1); +~b(1)}.  &signature{++a(1) ; ++b(1)}."""
		c_reg = ":- a(1,T), b(1,T), b(1,T-1), time(T)."
		self.assertEqual(solve([program, c], handler_class, handler_args),
		                 solve_regular([program, c_reg]))

		self.reset_mappings()
		c = """&constraint(1,maxtime){+.a(1); +.b(1); +~b(1)}.  &signature{++a(1) ; ++b(1)}."""
		c_reg = ":- a(1,T), b(1,T), b(1,T-1), time(T)."
		self.assertEqual(solve([program, c], handler_class, handler_args),
		                 solve_regular([program, c_reg]))

		self.reset_mappings()
		c = """&constraint(1,maxtime){+.a(1); +.a(2); +.b(1); +~b(1)}. &signature{++a(1) ; ++a(2) ; ++b(1)}."""
		c_reg = ":- a(1,T), a(2,T), b(1,T), b(1,T-1), time(T)."
		self.assertEqual(solve([program, c], handler_class, handler_args),
		                 solve_regular([program, c_reg]))

		self.reset_mappings()
		c = """&constraint(1,maxtime){+.a(1); -.a(2); -.b(1); +~b(1)}. &signature{++a(1) ; --a(2) ; --b(1) ; ++b(1)}."""
		c_reg = ":- a(1,T), not a(2,T), not b(1,T), b(1,T-1), time(T)."
		self.assertEqual(solve([program, c], handler_class, handler_args),
		                 solve_regular([program, c_reg]))

		self.reset_mappings()
		c = """&constraint(1,maxtime){+.a(1); -.a(2); +.b(1); -~b(1)}. &signature{++a(1) ; --a(2) ; ++b(1) ; --b(1)}."""
		c_reg = ":- a(1,T), not a(2,T), b(1,T), not b(1,T-1), time(T)."
		self.assertEqual(solve([program, c], handler_class, handler_args),
		                 solve_regular([program, c_reg]))

		# multiple constraints

		self.reset_mappings()
		c = """&constraint(1,maxtime){+.a(1); +.a(2); +.b(1); +~b(1)}.
			   &constraint(1,maxtime){+~b(2); -.a(2)}. 
			   &signature{++a(1) ; ++a(2) ; --a(2) ; ++b(1) ; ++b(2)}."""
		c_reg = """:- a(1,T), a(2,T), b(1,T), b(1,T-1), time(T).
				   :- b(2,T-1), not a(2,T), time(T)."""
		self.assertEqual(solve([program, c], handler_class, handler_args),
		                 solve_regular([program, c_reg]))

		self.reset_mappings()
		c = """&constraint(1,maxtime){+.a(1); +.a(2); +.b(1); +~b(1)}.
			   &constraint(1,maxtime){+~b(2); -.a(2)}.
			   &constraint(1,maxtime){+.a(2); +.b(1); -~a(1)}.
			   &signature{++a(1) ; ++a(2) ; --a(1) ; --a(2) ; ++b(1) ; ++b(2) }."""
		c_reg = """:- a(1,T), a(2,T), b(1,T), b(1,T-1), time(T).
				   :- b(2,T-1), not a(2,T), time(T).
				   :- a(2,T), b(1,T), not a(1,T-1), time(T)."""
		self.assertEqual(solve([program, c], handler_class, handler_args),
		                 solve_regular([program, c_reg]))

		# more complex atoms
		self.reset_mappings()
		program2 = """{ c((a(D),b(D)),T) : domain_ab(D), domain_ab(D)} 1 :- time(T)."""

		c = """&constraint(1,maxtime){+.c((a(D),b(D))); -~a(D); -~b(D)} :- domain_ab(D).
		&signature{++c((a(D),b(D))) ; --a(D) ; --b(D)} :- domain_ab(D)."""
		c_reg = ":- c((a(D),b(D)),T), not a(D,T-1), not b(D,T-1), domain_ab(D), domain_ab(D), time(T)."
		self.assertEqual(solve([program, program2, c], handler_class, handler_args),
		                 solve_regular([program, program2, c_reg]))


if __name__ == "__main__":
	unittest.main()
