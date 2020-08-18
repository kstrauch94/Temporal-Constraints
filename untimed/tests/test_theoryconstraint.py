import unittest
from untimed.propagator.propagatorhandler import TheoryHandler

import clingo

program = """
time(1..1).
domain_ab(1..1).

{a(V,T)} :- domain_ab(V), time(T).
{b(V,T)} :- domain_ab(V), time(T).

"""
def parse_model(m):
	ret = []
	for sym in m.symbols(shown=True):
		ret.append(sym)

	return list(map(str, sorted(ret)))

def solve(programs, handler):

	r = []

	prg = clingo.Control(['0'], message_limit=0)

	handler.register(prg)

	for p in programs:
		prg.add("base", [], p)

	prg.ground([("base", [])])

	prg.solve(on_model=lambda m: r.append(parse_model(m)))
	print(sorted(r))
	return sorted(r)

def solve_regular(programs):
	
	r = []

	prg = clingo.Control(['0'], message_limit=0)

	for p in programs:
		prg.add("base", [], p)

	prg.ground([("base", [])])

	prg.solve(on_model=lambda m: r.append(parse_model(m)))
	print(sorted(r))
	return sorted(r)


class TestApp(unittest.TestCase):

	def test_naive(self):
		handler = TheoryHandler("naive")
		
		c = """:-&constraint{+.a(1); +.b(1)}. &time{ +1 }."""
		c_reg = ":- a(1,T), b(1,T)."
		self.assertEqual(solve([program, c], handler), 
						 solve_regular([program, c_reg]))


if __name__ == "__main__":
	unittest.main()