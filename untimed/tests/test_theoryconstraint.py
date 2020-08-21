import unittest
from untimed.propagator.propagatorhandler import TheoryHandler
from untimed.propagator.propagatorhandler import TheoryHandlerMany


import clingo

program = """
#const maxtime = 3.
time(1..maxtime).
domain_ab(1..2).

{a(V,T)} :- domain_ab(V), time(T).
{b(V,T)} :- domain_ab(V), time(T).

"""
def parse_model(m):
	ret = []
	for sym in m.symbols(shown=True):
		ret.append(sym)

	return list(map(str, sorted(ret)))

def solve(programs, handler_class, htype, print_r=False):

	r = []

	handler = handler_class(htype)

	prg = clingo.Control(['0'], message_limit=0)

	for p in programs:
		prg.add("base", [], p)

	handler.add_theory(prg)

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

	def test_naive_regular(self):
		handler_class = TheoryHandler
		htype = "naive"

		self.handler_test(handler_class, htype)

	def test_naive_many(self):
		handler_class = TheoryHandlerMany
		htype = "naive"

		self.handler_test(handler_class, htype)

	def test_2watch_regular(self):
		handler_class = TheoryHandler
		htype = "2watch"

		self.handler_test(handler_class, htype)

	def test_2watch_many(self):
		handler_class = TheoryHandlerMany
		htype = "2watch"

		self.handler_test(handler_class, htype)

	def handler_test(self, handler_class, htype):

		# tests with constraints of size 1
		c = """:-&constraint{+.a(1)}. &time{ +B } :- B=maxtime."""
		c_reg = ":- a(1,T), time(T)."
		self.assertEqual(solve([program, c], handler_class, htype), 
						 solve_regular([program, c_reg]))

		c = """:-&constraint{-.a(1)}. &time{ +B } :- B=maxtime."""
		c_reg = ":- not a(1,T), time(T)."
		self.assertEqual(solve([program, c], handler_class, htype), 
						 solve_regular([program, c_reg]))

		c = """:-&constraint{-~a(1)}. &time{ +B } :- B=maxtime."""
		c_reg = ":- not a(1,T-1), time(T), time(T-1)."
		self.assertEqual(solve([program, c], handler_class, htype), 
						 solve_regular([program, c_reg]))

		c = """:-&constraint{+~a(1)}. &time{ +B } :- B=maxtime."""
		c_reg = ":- a(1,T-1), time(T), time(T-1)."
		self.assertEqual(solve([program, c], handler_class, htype), 
						 solve_regular([program, c_reg]))

		# tests with constraints of size 2

		c = """:-&constraint{+.a(1); +.b(1)}. &time{ +B } :- B=maxtime."""
		c_reg = ":- a(1,T), b(1,T), time(T)."
		self.assertEqual(solve([program, c], handler_class, htype), 
						 solve_regular([program, c_reg]))

		c = """:-&constraint{+.a(1); -.b(1)}. &time{ +B } :- B=maxtime."""
		c_reg = ":- a(1,T), not b(1,T), time(T)."
		self.assertEqual(solve([program, c], handler_class, htype), 
						 solve_regular([program, c_reg]))

		c = """:-&constraint{-.a(1); -.b(1)}. &time{ +B } :- B=maxtime."""
		c_reg = ":- not a(1,T), not b(1,T), time(T)."
		self.assertEqual(solve([program, c], handler_class, htype), 
						 solve_regular([program, c_reg]))

		c = """:-&constraint{-.a(1); +.b(1)}. &time{ +B } :- B=maxtime."""
		c_reg = ":- not a(1,T), b(1,T), time(T)."
		self.assertEqual(solve([program, c], handler_class, htype), 
						 solve_regular([program, c_reg]))

		c = """:-&constraint{+~a(1); -.b(1)}. &time{ +B } :- B=maxtime."""
		c_reg = ":- a(1,T-1), not b(1,T), time(T), time(T-1)."
		self.assertEqual(solve([program, c], handler_class, htype), 
						 solve_regular([program, c_reg]))

		c = """:-&constraint{-~a(1); +.b(1)}. &time{ +B } :- B=maxtime."""
		c_reg = ":- not a(1,T-1), b(1,T), time(T), time(T-1)."
		self.assertEqual(solve([program, c], handler_class, htype), 
						 solve_regular([program, c_reg]))

		c = """:-&constraint{-~a(1); -.b(1)}. &time{ +B } :- B=maxtime."""
		c_reg = ":- not a(1,T-1), not b(1,T), time(T), time(T-1)."
		self.assertEqual(solve([program, c], handler_class, htype), 
						 solve_regular([program, c_reg]))

		c = """:-&constraint{-~a(1); -~b(1)}. &time{ +B } :- B=maxtime."""
		c_reg = ":- not a(1,T-1), not b(1,T-1), time(T), time(T-1)."
		self.assertEqual(solve([program, c], handler_class, htype), 
						 solve_regular([program, c_reg]))

		# size 2 but with same atom

		c = """:-&constraint{+.a(1); +~a(1)}. &time{ +B } :- B=maxtime."""
		c_reg = ":- a(1,T), a(1,T-1), time(T), time(T-1)."
		self.assertEqual(solve([program, c], handler_class, htype), 
						 solve_regular([program, c_reg]))

		c = """:-&constraint{-.a(1); -~a(1)}. &time{ +B } :- B=maxtime."""
		c_reg = ":- not a(1,T), not a(1,T-1), time(T), time(T-1)."
		self.assertEqual(solve([program, c], handler_class, htype), 
						 solve_regular([program, c_reg]))

		c = """:-&constraint{+.a(1); -~a(1)}. &time{ +B } :- B=maxtime."""
		c_reg = ":- a(1,T), not a(1,T-1), time(T), time(T-1)."
		self.assertEqual(solve([program, c], handler_class, htype), 
						 solve_regular([program, c_reg]))

		# tests with size > 2

		c = """:-&constraint{+.a(1); +.b(1); +~b(1)}. &time{ +B } :- B=maxtime."""
		c_reg = ":- a(1,T), b(1,T), b(1,T-1), time(T), time(T-1)."
		self.assertEqual(solve([program, c], handler_class, htype), 
						 solve_regular([program, c_reg]))

		c = """:-&constraint{+.a(1); +.b(1); +~b(1)}. &time{ +B } :- B=maxtime."""
		c_reg = ":- a(1,T), b(1,T), b(1,T-1), time(T), time(T-1)."
		self.assertEqual(solve([program, c], handler_class, htype), 
						 solve_regular([program, c_reg]))

		c = """:-&constraint{+.a(1); +.a(2); +.b(1); +~b(1)}. &time{ +B } :- B=maxtime."""
		c_reg = ":- a(1,T), a(2,T), b(1,T), b(1,T-1), time(T), time(T-1)."
		self.assertEqual(solve([program, c], handler_class, htype), 
						 solve_regular([program, c_reg]))


if __name__ == "__main__":
	unittest.main()