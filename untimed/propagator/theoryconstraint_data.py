from collections import defaultdict

from typing import Dict, Tuple, Set, Any, Optional, List

CONSTRAINT_CHECK = {"NONE": 0,
					"UNIT": 1,
					"CONFLICT": -1}


class AtomInfo:

	__slots__ = ["sign", "time_mod", "name"]

	def __init__(self, sign, time_mod, name):
		self.sign = sign
		self.time_mod = time_mod
		self.name = name

	def __eq__(self, other):
		if other.sign == self.sign and other.time_mod == self.time_mod and other.name == self.name:
			return True

		return False


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

	initialized: bool = False

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
		cls.initialized = False


class Signatures:
	sigs: Set[Tuple[int, Tuple[Any, int]]] = set()
	finished = False

	@classmethod
	def reset(cls):
		cls.sigs = set()
		cls.finished = False