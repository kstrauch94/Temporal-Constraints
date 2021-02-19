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


class ConstraintInfo:

	__slots__ = ["min_time", "max_time", "t_atom_info"]

	def __init__(self, t_atom_info, min_time, max_time):
		self.min_time = min_time
		self.max_time = max_time
		self.t_atom_info = t_atom_info


	@property
	def size(self):
		return len(self.t_atom_info)


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
		try:
			lit = cls.name_to_lit[name_id]
		except KeyError:
			# this error would happen if an id is not in the mapping
			# if this happens it means the atom does not exist for this assigned time
			# if sign is 1 then it means that a POSITIVE atom does not exist -> a false atom in the nogood -> automatically ok
			#return -1
			if name_id[0] == 1:
				cls.add(name_id, -1)
				return -1

			#if sign is -1 then is means that a POSITIVE atom does not exist and hence this NEGATIVE atom for that atom is always positive
			# so we can assign the 1 to lit
			cls.add(name_id, 1)
			return 1



		return lit

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


class LitToId:

	lit2id: Dict[int, int] = {}
	id2lit: Dict[int, int] = {}
	size: int = 0

	def add_base_lit(self, lit):
		lit2id = 0

class Signatures:
	sigs: Set[Tuple[int, Tuple[Any, int]]] = set()
	finished = False

	@classmethod
	def reset(cls):
		cls.sigs = set()
		cls.finished = False