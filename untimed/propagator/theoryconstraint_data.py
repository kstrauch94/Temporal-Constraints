from collections import defaultdict

from typing import Dict, Tuple, Set, Any, Optional, List

import untimed.util as util

CONSTRAINT_CHECK = {"NONE": 0,
					"UNIT": 1,
					"CONFLICT": -1}


class AtomInfo:

	__slots__ = ["sign", "time_mod", "untimed_lit"]

	def __init__(self, sign, time_mod, untimed_lit):
		self.sign = sign
		self.time_mod = time_mod
		self.untimed_lit = untimed_lit

	def __eq__(self, other):
		if other.sign == self.sign and other.time_mod == self.time_mod and other.untimed_lit == self.untimed_lit:
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
	Has helper methods to retrieve either a literal or an internal_lit

	"""
	id_to_lit: Dict[int, int] = {}

	lit_to_id: Dict[int, Set[int]] = defaultdict(set)

	initialized: bool = False

	size: int = None

	@classmethod
	#@profile
	def add(cls, internal_lit, lit):
		if internal_lit not in cls.id_to_lit:
			cls.id_to_lit[internal_lit] = lit

			cls.lit_to_id[lit].add(internal_lit)

	@classmethod
	def grab_lit(cls, internal_lit):
	
		if internal_lit not in cls.id_to_lit:
			util.Count.add("Keyerror mapping")
			# this would happen if an id is not in the mapping
			# if this happens it means the atom does not exist for this time point
			# if sign is 1 then it means that a POSITIVE atom does not exist so we add it as -1
			# otherwise a negative atom does not exit which means that the positive counterpart
			# is always true so we assign it 1

			if internal_lit >= 0:
				# it is negative if it is not in the mapping
				# so we add it as -1 and return it
				cls.add(internal_lit, -1)
				#cls.add(internal_lit * -1, 1)
				return -1
			else:
				cls.add(internal_lit, 1)
				#cls.add(internal_lit * -1, -1)
				return 1
			
		return cls.id_to_lit[internal_lit]


	@classmethod
	def grab_id(cls, lit):
		return cls.lit_to_id[lit]

	@classmethod
	def has_name(cls, name_id):
		return name_id in cls.id_to_lit

	@classmethod
	def reset(cls):
		cls.id_to_lit.clear()
		cls.lit_to_id.clear()
		cls.initialized = False
		cls.size = 0

class Signatures:
	sigs: Set[Tuple[int, Tuple[Any, int]]] = set()
	fullsigs = {}
	fullsigs_term = {}
	fullsig_size = 0
	finished = False

	@classmethod
	def reset(cls):
		cls.sigs = set()
		cls.fullsigs.clear()
		cls.fullsig_size = 0
		cls.fullsigs_term.clear()
		cls.finished = False

	@classmethod
	def add_fullsig(cls, fullsig, fullsig_term):
		if fullsig in cls.fullsigs:
			return
		cls.fullsig_size += 1
		cls.fullsigs[fullsig] = cls.fullsig_size
		cls.fullsigs_term[fullsig_term] = cls.fullsig_size

	@classmethod
	def get_sig(cls, ulit):
		for sig, val in cls.fullsigs.items():
			if int(val) == int(ulit):
				return sig

	@classmethod
	def convert_to_untimed_lit(cls, internal_lit):
		intermediate = internal_lit % cls.fullsig_size
		if intermediate == 0:
			intermediate = cls.fullsig_size
		return intermediate * util.sign(internal_lit)

	@classmethod
	def convert_to_internal_lit(cls, untimed_lit, time, sign):
		return untimed_lit + (cls.fullsig_size * time * sign)

	@classmethod
	def convert_to_time(cls, interal_lit):
		return (abs(interal_lit) - 1) // cls.fullsig_size


class GlobalConfig:

	lock_up_to = -1
	lock_from = -1
