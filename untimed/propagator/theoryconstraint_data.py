from collections import defaultdict

from typing import Dict, Tuple, Set, Any, Optional, List

CONSTRAINT_CHECK = {"NONE": 0,
					"UNIT": 1,
					"CONFLICT": -1}


class AtomInfo:

	__slots__ = ["sign", "time_mod", "internal_lit"]

	def __init__(self, sign, time_mod, internal_lit):
		self.sign = sign
		self.time_mod = time_mod
		self.internal_lit = internal_lit

	def __eq__(self, other):
		if other.sign == self.sign and other.time_mod == self.time_mod and other.internal_lit == self.internal_lit:
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

	internal_lit is a Tuple[sign, name, time]
	"""
	id_to_lit: Dict[int, int] = {}

	lit_to_id: Dict[int, Set[int]] = defaultdict(set)

	initialized: bool = False

	@classmethod
	#@profile
	def add(cls, internal_lit, lit):
		if internal_lit not in cls.id_to_lit:
			cls.id_to_lit[internal_lit] = lit

			cls.lit_to_id[lit].add(internal_lit)

	@classmethod
	def grab_lit(cls, internal_lit):
		try:
			lit = cls.id_to_lit[internal_lit]
		except KeyError:
			# this error would happen if an id is not in the mapping
			# if this happens it means the atom does not exist for this assigned time
			# if sign is 1 then it means that a POSITIVE atom does not exist -> a false atom in the nogood -> automatically ok
			#return -1

			#on the new paradigm with internal lits, i will always look with opsitive internal lits, so we can assume
			# it is negative if it is not in the mapping
			# so we add it as -1 and return it
			cls.add(internal_lit, -1)
			return -1


		return lit

	@classmethod
	def grab_id(cls, lit):
		return cls.lit_to_id[lit]

	@classmethod
	def has_name(cls, name_id):
		return name_id in cls.id_to_lit

	@classmethod
	def reset(cls):
		cls.id_to_lit = {}
		cls.lit_to_ids = defaultdict(set)
		cls.initialized = False


class LitToId:

	lit2id: Dict[int, int] = {}
	id2lit: Dict[int, int] = {}
	size: int = 0

	def add_base_lit(self, lit):
		lit2id = 0

class Signatures:
	sigs: Set[Tuple[int, Tuple[Any, int]]] = set()
	sigs_0 = set()
	fullsigs = {}
	fullsigs_term = {}
	fullsig_size = 0
	finished = False

	@classmethod
	def reset(cls):
		cls.sigs = set()
		cls.finished = False

	@classmethod
	def add_fullsig(cls, fullsig, fullsig_term):
		cls.fullsigs[fullsig] = cls.fullsig_size
		cls.fullsigs_term[fullsig_term] = cls.fullsig_size

		cls.fullsig_size += 1
