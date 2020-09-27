import logging
from collections import defaultdict
import clingo

from typing import List, Dict, Tuple, Set, Callable, Any, Optional
import untimed.util as util

CONSTRAINT_CHECK = {"NONE": 0,
                    "UNIT": 1,
                    "CONFLICT": -1}


class PropagationError(Exception):
	pass


class Map_Name_Lit:
	name_to_lit: Dict[Tuple[int, str, int], int] = {}
	lit_to_name: Dict[int, Set[str]] = defaultdict(set)

	@classmethod
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


def build_symbol_id(info, time):
	return info["sign"], info["name"], time


def parse_time(s_atom) -> int:
	time = str(s_atom.symbol).split(",")[-1].replace(")", "").strip()
	return int(time)


def get_assigned_time(info: Dict[str, Any], time: int) -> int:
	# info is the info of just ONE atom
	return time + info["time_mod"]


def reverse_assigned_time(info: Dict[str, Any], assigned_time: int) -> int:
	return assigned_time - info["time_mod"]


def form_nogood(t_atom_info, assigned_time: int, existing_at) -> List[int]:
	# full info is the info of all the atoms
	if assigned_time not in existing_at:
		return []

	ng: Set[int] = set()

	for uq_name in t_atom_info.keys():
		time: int = reverse_assigned_time(t_atom_info[uq_name], assigned_time)
		ng.add(Map_Name_Lit.grab_lit(build_symbol_id(t_atom_info[uq_name], time)))

	return list(ng)


class TheoryConstraint:

	def __init__(self, constraint):

		self.t_atom_info: Dict[str, Dict[str, Any]] = {}
		self.atom_signatures: Set[Tuple[str, int]] = set()

		self.watches_to_at: Dict[int, Set[int]] = defaultdict(set)
		self.at_size: Dict[int, int] = defaultdict(lambda: 0)

		self.max_time: int
		self.min_time: int

		self.existing_at: List[int] = []

		self.unit_constraints: List[List[int]] = []

		self.parse_atoms(constraint)

	@property
	def t_atom_names(self):
		return self.t_atom_info.keys()

	@property
	def watches(self):
		return self.watches_to_at.keys()

	def parse_atoms(self, constraint) -> None:
		self.parse_constraint_times(constraint.term.arguments)
		for atom in constraint.elements:
			# this gives me the "type" of the term | e.g. for +~on(..) it would return +~
			term_type: str = atom.terms[0].name

			signature: Tuple[str, int] = (
				atom.terms[0].arguments[0].name, len(atom.terms[0].arguments[0].arguments) + 1)

			name: str = str(atom.terms[0].arguments[0])[:-1] + ","

			uq_name: str = term_type + name

			self.atom_signatures.add(signature)

			if term_type == "+.":
				sign = 1
				time_mod = 0
			elif term_type == "+~":
				sign = 1
				time_mod = +1
			elif term_type == "-.":
				sign = -1
				time_mod = 0
			elif term_type == "-~":
				sign = -1
				time_mod = +1

			self.t_atom_info[uq_name] = {"sign": sign,
			                             "time_mod": time_mod,
			                             "signature": signature,
			                             "args": [clingo.parse_term(str(a)) for a in atom.terms[0].arguments[0].arguments],
			                             "name": name}

	def parse_constraint_times(self, times):
		if len(times) == 1:
			self.max_time = times[0].number
			self.min_time = 0
		else:
			self.max_time = times[1].number
			self.min_time = times[0].number

	def init(self, init, propagate: bool = False) -> None:
		self.init_watches(init)
		self.propagate_init(init, propagate)
		self.build_watches(init)

	def init_watches(self, init) -> None:
		for uq_name, info in self.t_atom_info.items():
			for s_atom in init.symbolic_atoms.by_signature(*info["signature"]):
				if s_atom.symbol.arguments[:-1] == info["args"]:
					time: int = parse_time(s_atom)
					assigned_time: int = get_assigned_time(self.t_atom_info[uq_name], time)

					# max time and min time can not be none! add some detection just in case?
					if self.max_time is not None and assigned_time > self.max_time:
						self.logger.debug("no watch for lit cause assigned time would be too big: %s", s_atom.symbol)
						continue

					elif self.min_time is not None and assigned_time < self.min_time:
						self.logger.debug("no watch for lit cause assigned time would be too small: %s", s_atom.symbol)
						continue

					solver_lit: int = init.solver_literal(s_atom.literal) * self.t_atom_info[uq_name]["sign"]

					self.at_size[assigned_time] += 1
					if assigned_time not in self.existing_at:
						self.existing_at.append(assigned_time)

					Map_Name_Lit.add(build_symbol_id(self.t_atom_info[uq_name], time), solver_lit)

	def propagate_init(self, init, propagate: bool = False) -> None:
		invalid_at = []
		for assigned_time in self.existing_at:
			if self.at_size[assigned_time] < self.size:
				# if this happens, it could be because for one
				# of the names in the constraint for a particular
				# assigned time there was no symbolic atom for it
				# this means that the atom does not exist
				# hence, it is false and the nogood is useless
				# so we delete it
				invalid_at.append(assigned_time)
				continue

			if not propagate:
				# if we don't want propagate no init then just continue and check the next assigned time
				# for a nogood that is always false
				continue

			result, ng = self.check_assignment(assigned_time, init)
			if result == CONSTRAINT_CHECK["CONFLICT"]:
				init.add_clause([-l for l in ng])

			elif result == CONSTRAINT_CHECK["UNIT"]:
				# if nogood is already unit at init
				# then we can add the clause so it propagates at time 0
				# then we delete assigned time because
				# it will never pop up again
				init.add_clause([-l for l in ng])
				invalid_at.append(assigned_time)

		for iat in invalid_at:
			self.existing_at.remove(iat)

	def propagate_unit_constraints(self, control):
		for ng in self.unit_constraints:
			if not control.add_nogood(ng):  # and control.propagate():
				self.logger.debug("added unit ng but prop stops!")
				self.unit_constraints = []
				return

		self.unit_constraints = []

	def check_assignment(self, assigned_time, control) -> Tuple[int, List[int]]:
		ng: List[int] = []
		true_count: int = 0

		for uq_name in self.t_atom_names:
			time = reverse_assigned_time(self.t_atom_info[uq_name], assigned_time)
			name_id = build_symbol_id(self.t_atom_info[uq_name], time)

			if not Map_Name_Lit.has_name(name_id):
				# if it is not in the dict then it is false always
				return CONSTRAINT_CHECK["NONE"], []

			lit: int = Map_Name_Lit.grab_lit(name_id)

			if control.assignment.is_true(lit):
				# if its true
				ng.append(lit)
				true_count += 1
			elif control.assignment.is_false(lit):
				# if one is false then it doesnt matter
				return CONSTRAINT_CHECK["NONE"], []
			else:
				# if value is None we still add it to ng
				ng.append(lit)

		if true_count == self.size:
			return CONSTRAINT_CHECK["CONFLICT"], ng
		elif true_count == self.size - 1:
			self.unit_constraints.append(ng)
			return CONSTRAINT_CHECK["UNIT"], ng
		else:
			return CONSTRAINT_CHECK["NONE"], []

	def build_watches(self, init):
		pass

	def undo(self, thread_id, assign, changes) -> None:
		pass

	def propagate(self, control, changes):
		pass

	@property
	def size(self) -> int:
		return len(self.t_atom_names)


class TheoryConstraintSize1(TheoryConstraint):

	def __init__(self, constraint) -> None:
		super().__init__(constraint)
		self.logger = logging.getLogger(self.__module__ + "." + self.__class__.__name__)

	def propagate_init(self, init, propagate: bool = False) -> None:
		"""
		overwriting parent class method so it does nothing when called
		"""
		pass

	def init_watches(self, init) -> None:

		for uq_name, info in self.t_atom_info.items():
			for s_atom in init.symbolic_atoms.by_signature(*info["signature"]):
				if s_atom.symbol.arguments[:-1] == info["args"]:
					time: int = parse_time(s_atom)
					assigned_time: int = get_assigned_time(self.t_atom_info[uq_name], time)

					# max time and min time can not be none! add some detection just in case?
					if self.max_time is not None and assigned_time > self.max_time:
						self.logger.debug("no watch for lit cause assigned time would be too big: %s", s_atom.symbol)
						continue

					elif self.min_time is not None and assigned_time < self.min_time:
						self.logger.debug("no watch for lit cause assigned time would be too small: %s", s_atom.symbol)
						continue

					solver_lit: int = init.solver_literal(s_atom.literal) * self.t_atom_info[uq_name]["sign"]

					# add nogood
					init.add_clause([-solver_lit])


class TheoryConstraintSize2(TheoryConstraint):

	def __init__(self, constraint) -> None:
		super().__init__(constraint)
		self.logger = logging.getLogger(self.__module__ + "." + self.__class__.__name__)

	def build_watches(self, init) -> None:
		for assigned_time in self.existing_at:
			lits = form_nogood(self.t_atom_info, assigned_time, self.existing_at)
			for lit in lits:
				init.add_watch(lit)
				self.watches_to_at[lit].add(assigned_time)

	def propagate(self, control, changes) -> None:
		for lit in changes:
			if lit in self.watches_to_at:
				for assigned_time in self.watches_to_at[lit]:
					ng = form_nogood(self.t_atom_info, assigned_time, self.existing_at)

					if not control.add_nogood(ng):
						return


class TheoryConstraintNaive(TheoryConstraint):

	def __init__(self, constraint) -> None:
		super().__init__(constraint)
		self.logger = logging.getLogger(self.__module__ + "." + self.__class__.__name__)

	def build_watches(self, init) -> None:
		for assigned_time in self.existing_at:
			lits = form_nogood(self.t_atom_info, assigned_time, self.existing_at)
			for lit in lits:
				init.add_watch(lit)
				self.watches_to_at[lit].add(assigned_time)

	def propagate(self, control, changes) -> None:
		for lit in changes:
			if lit in self.watches_to_at:
				for assigned_time in self.watches_to_at[lit]:
					update_result, ng = self.check_assignment(assigned_time, control)

					if update_result == CONSTRAINT_CHECK["CONFLICT"]:
						if not control.add_nogood(ng):
							self.unit_constraints = []
							return
						else:
							PropagationError("constraint for a conflict added but propagations continues")

		self.propagate_unit_constraints(control)


def choose_lit(lits: Set[int], current_watch: int, control) -> Optional[int]:
	"""
	Checks the literals for a nogood and check for new watches
	:param Set[int] lits: the current nogood
	:param int current_watch: the watch being propagated
	:param PropagateControl control: A clingo PropagateControl object for the current solver thread

	:return: None or the new watch
	:rtype: None or int

	"""
	for possible_watch in lits:
		if possible_watch != current_watch:
			if control.assignment.value(possible_watch) is None and not control.has_watch(possible_watch):
				return possible_watch

	return None


class TheoryConstraint2watch(TheoryConstraint):

	def __init__(self, constraint):

		super().__init__(constraint)
		self.logger = logging.getLogger(self.__module__ + "." + self.__class__.__name__)

	def build_watches(self, init) -> None:
		for assigned_time in self.existing_at:
			lits = form_nogood(self.t_atom_info, assigned_time, self.existing_at)
			for lit in lits[:2]:
				self.watches_to_at[lit].add(assigned_time)
				init.add_watch(lit)

	# @profile
	def propagate(self, control, changes) -> None:
		self.logger.debug("Propagating for constraint: %s", self.t_atom_names)

		replacement_info: List[Tuple[int, int, int]] = []
		for lit in changes:
			if lit in self.watches_to_at:
				for assigned_time in self.watches_to_at[lit]:

					result, ng = self.check_assignment(assigned_time, control)

					if result == CONSTRAINT_CHECK["CONFLICT"]:

						if not control.add_nogood(ng):  # or not control.propagate():
							self.unit_constraints = []
							return
						else:
							self.logger.debug("constraint for a conflict added and propagations continues?")

					info = self.get_replacement_watch(assigned_time, lit, control)
					if info is not None:
						replacement_info.append(info)

		self.replace_watches(replacement_info, control)

		self.propagate_unit_constraints(control)

	def replace_watches(self, info: List[Tuple[int, int, int]], control) -> None:

		for old_watch, new_watch, assigned_time in info:
			self.logger.debug("removing watch %i and replacing it by watch %i for assigned time %i", old_watch,
			                  new_watch, assigned_time)

			# remove the lit as a watch for constraint assigned_time
			self.watches_to_at[old_watch].remove(assigned_time)

			# add new watch as a watch for constraint assigned_time
			self.watches_to_at[new_watch].add(assigned_time)

			if not control.has_watch(new_watch):
				control.add_watch(new_watch)

			# if lit is not watching a constraint eliminate it
			if len(self.watches_to_at[old_watch]) == 0:
				control.remove_watch(old_watch)

	def get_replacement_watch(self, assigned_time: int, lit: int, control) -> Optional[Tuple[int, int, int]]:
		"""
		choose a new watch for the given assigned time if possible
		:param int assigned_time: the assigned time
		:param int lit: the current literal being propagated
		:param PropagateControl control: A clingo PropagateControl object for the current solver thread

		if a new watch can be found:
		:return: old_watch: int, new_watch: int, assigned_time: int

		if no new watch is found:
		:returns None
		"""

		new_watch: Optional[int] = choose_lit(form_nogood(self.t_atom_info, assigned_time, self.existing_at), lit,
		                                           control)
		if new_watch is not None:
			return lit, new_watch, assigned_time

		return None
