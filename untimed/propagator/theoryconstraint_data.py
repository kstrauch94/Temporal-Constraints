from collections import defaultdict

from typing import Dict, Tuple, Set, Any

CONSTRAINT_CHECK = {"NONE": 0,
					"UNIT": 1,
					"CONFLICT": -1}


class AtomInfo:

	__slots__ = ["sign", "time_mod", "name"]

	def __init__(self, sign, time_mod, name):
		self.sign = sign
		self.time_mod = time_mod
		self.name = name


# just an alias
atom_info = AtomInfo

class TimeAtomToSolverLit:
	"""
	Maps a name id to a solver literal.
	Has helper methods to retrieve either a literal or a name id

	name_id is a Tuple[sign, name, time]
	"""
	name_to_lit: Dict[Tuple[int, str, int], int] = {}

	lit_to_name: Dict[int, Set[Tuple[int, str, int]]] = defaultdict(set)

	@classmethod
	#@profile
	def add(cls, name_id, lit):
		if name_id not in cls.name_to_lit:
			cls.name_to_lit[name_id] = lit

			cls.lit_to_name[lit].add(name_id)

	@classmethod
	def grab_lit(cls, name_id):
		return cls.name_to_lit[name_id]

	@classmethod
	def grab_name(cls, lit):
		return cls.lit_to_name[lit]

	@classmethod
	def has_name(cls, name_id):
		return name_id in cls.name_to_lit

	@classmethod
	def reset(cls):
		cls.name_to_lit = {}
		cls.lit_to_name = defaultdict(set)


class SymbolToProgramLit:
	symbol_to_lit: Dict[Any, int] = {}

	@classmethod
	def add(cls, symbol, lit):
		if symbol not in cls.symbol_to_lit:
			cls.symbol_to_lit[symbol] = lit

	@classmethod
	def grab_lit(cls, symbol):
		return cls.symbol_to_lit[symbol]

	@classmethod
	def reset(cls):
		cls.symbol_to_lit = {}
		cls.symbol_to_lit.clear()


class Signatures:
	sigs: Set[Tuple[Any, int]] = set()
	finished = False

	@classmethod
	def reset(cls):
		cls.sigs = set()
		cls.finished = False
