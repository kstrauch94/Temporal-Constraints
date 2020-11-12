import unittest
from untimed.propagator.propagatorhandler import TheoryHandler, add_theory

from collections import defaultdict

from untimed.propagator.theoryconstraint_base import parse_atoms
from untimed.propagator.theoryconstraint_base import parse_time
from untimed.propagator.theoryconstraint_base import TheoryConstraint
from untimed.propagator.theoryconstraint_base import TimeAtomToSolverLit
from untimed.propagator.theoryconstraint_base import form_nogood
from untimed.propagator.theoryconstraint_base import atom_info
from untimed.propagator.theoryconstraint_base import init_TA2L_mapping

from untimed.propagator.theoryconstraint_data import Signatures

import clingo

from clingo import parse_term

program = """
#const maxtime = 3.
time(1..maxtime).
domain_ab(1..2).

{a(V,T)} :- domain_ab(V), time(T).
{b(V,T)} :- domain_ab(V), time(T).

"""

c1 = """:-&constraint(1,maxtime){+.a(1); +.a(2); +.b(1); +~b(1)}."""

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


def get_naive_handler():
	handler_class = TheoryHandler
	handler_args = {"prop_type": "naive"}

	return handler_class(*handler_args)


def get_2watch_handler():
	handler_class = TheoryHandler
	handler_args = {"prop_type": "2watch"}

	return handler_class(*handler_args)


def reset_mappings():
	TimeAtomToSolverLit.reset()
	Signatures.reset()


class MockInit:
	solver_lit_map = {}

	def __init__(self, control):
		self.control = control

	@property
	def symbolic_atoms(self):
		return self.control.symbolic_atoms

	def solver_literal(self, some_int):
		if some_int not in MockInit.solver_lit_map:
			MockInit.solver_lit_map[some_int] = len(MockInit.solver_lit_map)

		return MockInit.solver_lit_map[some_int]


class TestApp(unittest.TestCase):


	def test_parse_atoms(self):
		reset_mappings()

		c = """:-&constraint(1,maxtime){+.a(1); +.a(2); -.b(1); +~b(1)}."""

		real_info = {"+.a(1,": atom_info(sign=1, time_mod=0, name="a(1,"),
		             "+.a(2,": atom_info(sign=1, time_mod=0, name="a(2,"),
		             "-.b(1,": atom_info(sign=-1, time_mod=0, name="b(1,"),
		             "+~b(1,": atom_info(sign=1, time_mod=1, name="b(1,")}
		prg = prepare_prg([program, c])

		t_atom = next(prg.theory_atoms)

		info, min_t, max_t = parse_atoms(t_atom)

		self.assertEqual(1, min_t)
		self.assertEqual(3, max_t) # maxtime in program in 3

		real_sigs = set( [(1, ("a", 2)), (1, ("b", 2)), (-1, ("b", 2))] )

		self.assertEqual(Signatures.sigs, real_sigs)

		self.assertDictEqual(info, real_info)

		#################################
		reset_mappings()

		c = """:-&constraint(0,5){+.a(b(1,c(1,2,3))); -.b("this. is. TEST.", 3)}."""

		real_info = {"+.a(b(1,c(1,2,3)),": atom_info(sign=1, time_mod=0, name="a(b(1,c(1,2,3)),"),
		             '-.b("this. is. TEST.",3,': atom_info(sign=-1, time_mod=0, name='b("this. is. TEST.",3,')}

		prg = prepare_prg([program, c])

		t_atom = next(prg.theory_atoms)

		info, min_t, max_t = parse_atoms(t_atom)

		self.assertEqual(0, min_t)
		self.assertEqual(5, max_t) # maxtime in program in 3

		self.assertDictEqual(info, real_info)

		#######################
		reset_mappings()

		c = """:-&constraint(-1,5){+.a(1); -~b(3)}."""

		prg = prepare_prg([program, c])

		t_atom = next(prg.theory_atoms)

		self.assertRaises(RuntimeError, parse_atoms, t_atom)

		c = """:-&constraint(a,5){+.a(1); -~b(3)}."""

		prg = prepare_prg([program, c])

		t_atom = next(prg.theory_atoms)

		self.assertRaises(RuntimeError, parse_atoms, t_atom)

	def test_parse_time(self):
		reset_mappings()
		class SymbolicAtomMock:

			def __init__(self, symbol_str):
				self.s = parse_term(symbol_str)

			@property
			def symbol(self):
				return self.s

		s = SymbolicAtomMock('b("this. is. TEST.",3,5)')
		self.assertEqual(parse_time(s), 5)

		s = SymbolicAtomMock("b(b(b(b(2))),1)")
		self.assertEqual(parse_time(s), 1)

		s = SymbolicAtomMock("a(1)")
		self.assertEqual(parse_time(s), 1)

		s = SymbolicAtomMock("a(-1)")
		self.assertEqual(parse_time(s), -1)

		s = SymbolicAtomMock("a(1231231)")
		self.assertEqual(parse_time(s), 1231231)

		s = SymbolicAtomMock("a(1,d)")
		self.assertRaises(TypeError, parse_time, s)

		s = SymbolicAtomMock("a((1,d))")
		self.assertRaises(TypeError, parse_time, s)

	def test_init_TA2L_mapping(self):
		reset_mappings()

		program = """
		#const maxtime = 3.
		time(1..maxtime).
		domain_ab(1..2).

		{a(V,T)} :- domain_ab(V), time(T).
		{b(V,T)} :- domain_ab(V), time(T).
		{c(V,T)} :- domain_ab(V), time(T).
		"""

		c = """:-&constraint(1,maxtime){+.a(1); -~b(2); +~a(2)}.
				:-&constraint(2,maxtime){+.c(1)}."""

		prg = prepare_prg([program, c])
		init_mock = MockInit(prg)

		for t_atom in prg.theory_atoms:
			TheoryConstraint(t_atom)

		init_TA2L_mapping(init_mock)

		self.assertIn((1, "a(1,", 1), TimeAtomToSolverLit.name_to_lit)
		self.assertIn((1, "a(1,", 2), TimeAtomToSolverLit.name_to_lit)
		self.assertIn((1, "a(1,", 3), TimeAtomToSolverLit.name_to_lit)

		self.assertIn((-1, "b(2,", 1), TimeAtomToSolverLit.name_to_lit)
		self.assertIn((-1, "b(2,", 2), TimeAtomToSolverLit.name_to_lit)
		self.assertIn((-1, "b(2,", 3), TimeAtomToSolverLit.name_to_lit) # this is not in cause assigned time would be too high

		self.assertIn((1, "c(1,", 1), TimeAtomToSolverLit.name_to_lit) # not in because assigned time is too low
		self.assertIn((1, "c(1,", 2), TimeAtomToSolverLit.name_to_lit)
		self.assertIn((1, "c(1,", 3), TimeAtomToSolverLit.name_to_lit)

	def test_form_nogood(self):
		reset_mappings()

		TimeAtomToSolverLit.add((1, "a(1,", 2), 1)
		TimeAtomToSolverLit.add((1, "a(2,", 1), 2)
		TimeAtomToSolverLit.add((1, "b(1,", 2), 3)
		TimeAtomToSolverLit.add((-1, "c(1,", 2), -4)

		real_info = {"+.a(1,": atom_info(sign=1, time_mod=0, name="a(1,"),
		             "+~a(2,": atom_info(sign=1, time_mod=1, name="a(2,"),
		             "+.b(1,": atom_info(sign=1, time_mod=0, name="b(1,"),
		             "-.c(1,": atom_info(sign=-1, time_mod=0, name="c(1,")}

		ng = form_nogood(real_info, 2)
		actual_ng = [-4, 1, 2, 3]

		self.assertEqual(sorted(ng), actual_ng)

		self.assertIsNone(form_nogood(real_info, 1))

	def test_check_assignment(self):
		pass


if __name__ == "__main__":
	unittest.main()
