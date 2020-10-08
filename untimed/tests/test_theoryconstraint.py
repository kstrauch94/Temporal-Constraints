import unittest
from untimed.propagator.propagatorhandler import TheoryHandler, TheoryHandlerTimedWatch, add_theory

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


def prepare_prg(programs):
	prg = clingo.Control(['0'], message_limit=0)

	for p in programs:
		prg.add("base", [], p)

	add_theory(prg)

	prg.ground([("base", [])])

	return prg


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


def get_naive_handler():
	handler_class = TheoryHandler
	handler_args = {"prop_type": "naive"}

	return handler_class(*handler_args)


def get_2watch_handler():
	handler_class = TheoryHandler
	handler_args = {"prop_type": "2watch"}

	return handler_class(*handler_args)


def get_timed_handler():
	handler_class = TheoryHandlerTimedWatch
	handler_args = {}

	return handler_class(*handler_args)


class TestApp(unittest.TestCase):

	def test_parse_atoms(self, handler):
		pass


if __name__ == "__main__":
	unittest.main()
