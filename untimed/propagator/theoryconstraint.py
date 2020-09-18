import logging
from collections import defaultdict

from typing import List, Dict, Tuple, Set, Callable, Any, Optional

CONSTRAINT_CHECK = {"NONE": 0,
                    "UNIT": 1,
                    "CONFLICT": -1}


class PropagationError(Exception):
	pass


class Map_Name_Lit:
	name_to_lit: Dict[str, int] = {}
	lit_to_name: Dict[int, Set[str]] = defaultdict(set)

	@classmethod
	def add(cls, name, lit, time):
		if name not in cls.name_to_lit:
			cls.name_to_lit[name] = lit

		cls.lit_to_name[lit].add(name)

	@classmethod
	def grab_lit(cls, name):
		return cls.name_to_lit[name]

	@classmethod
	def grab_name(cls, lit):
		return cls.lit_to_name[lit]

	@classmethod
	def has_name(cls, name):
		return name in cls.name_to_lit


class TheoryConstraint:

	def __init__(self, constraint):

		self.t_atom_info: Dict[str, Dict[str, Any]] = {}
		self.t_atom_names: List[str] = []
		self.atom_signatures: Set[Tuple[str, int]] = set()

		self.watches_to_at: Dict[int, Set[int]] = defaultdict(set)
		self.at_size: Dict[int, int] = defaultdict(lambda: 0)

		self.max_time: int
		self.min_time: int

		self.existing_at: List[int] = []

		self.unit_constraints: List[List[int]] = []

		self.parse_atoms(constraint)

	@property
	def watches(self):
		return self.watches_to_at.keys()

	def parse_atoms(self, constraint) -> None:
		self.parse_constraint_times(constraint.term.arguments)
		for atom in constraint.elements:
			term_type: str = atom.terms[
				0].name  # this gives me the "type" of the term | e.g. for +~on(..) it would return +~

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
			                             "arity": signature[1],
			                             "name": name}

			self.t_atom_names.append(uq_name)

	def parse_constraint_times(self, times):
		if len(times) == 1:
			self.max_time = times[0].number
			self.min_time = 0
		else:
			self.max_time = times[1].number
			self.min_time = times[0].number

	def build_symbol_str(self, uq_name, time):
		name = self.t_atom_info[uq_name]["name"]

		if self.t_atom_info[uq_name]["sign"] == 1:
			return f"{name}{time})"
		elif self.t_atom_info[uq_name]["sign"] == -1:
			return f"not {name}{time})"

	def init_watches(self, s_atom, init) -> None:

		uq_name: str
		for uq_name in self.t_atom_names:
			name: str = self.t_atom_info[uq_name]["name"]
			if str(s_atom.symbol).startswith(name):
				time: int = self.parse_time(s_atom)
				assigned_time: int = self.get_assigned_time(uq_name, time)

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

				Map_Name_Lit.add(self.build_symbol_str(uq_name, time), solver_lit, time)

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

	def parse_time(self, s_atom) -> int:
		time = str(s_atom.symbol).split(",")[-1].replace(")", "").strip()
		return int(time)

	def get_assigned_time(self, uq_name: str, time: int) -> int:
		return time + self.t_atom_info[uq_name]["time_mod"]

	def reverse_assigned_time(self, uq_name: str, assigned_time: int) -> int:
		return assigned_time - self.t_atom_info[uq_name]["time_mod"]

	def check_assignment(self, assigned_time, control) -> Tuple[int, List[int]]:
		ng: List[int] = []
		true_count: int = 0

		for uq_name in self.t_atom_names:
			time = self.reverse_assigned_time(uq_name, assigned_time)
			name = self.build_symbol_str(uq_name, time)

			if not Map_Name_Lit.has_name(name):
				# if it is not in the dict then it is false always
				return CONSTRAINT_CHECK["NONE"], []

			lit: int = Map_Name_Lit.grab_lit(name)

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

	def form_nogood(self, assigned_time: int) -> List[int]:
		if assigned_time not in self.existing_at:
			return []
		# with this function I can make nogoods just from an assigned time
		ng: Set[int] = set()
		self.logger.debug("Form nogoods for assigned time: {}, {}".format(assigned_time, self.t_atom_names))
		for uq_name in self.t_atom_names:
			time: int = self.reverse_assigned_time(uq_name, assigned_time)
			ng.add(Map_Name_Lit.grab_lit(self.build_symbol_str(uq_name, time)))

		return list(ng)

	def build_watches(self, init):
		pass

	def undo(self, thread_id, assign, changes) -> None:
		pass

	def propagate(self, control, changes):
		pass

	@property
	def size(self) -> int:
		return len(self.t_atom_names)


class TheoryConstraintNaive(TheoryConstraint):

	def __init__(self, constraint) -> None:
		super().__init__(constraint)
		self.logger = logging.getLogger(self.__module__ + "." + self.__class__.__name__)

	def build_watches(self, init) -> None:
		for assigned_time in self.existing_at:
			lits = self.form_nogood(assigned_time)
			for lit in lits:
				init.add_watch(lit)
				self.watches_to_at[lit].add(assigned_time)

	def propagate(self, control, changes) -> None:
		self.logger.debug("Propagating for constraint: {}".format(self.t_atom_names))
		for lit in changes:
			if lit in self.watches_to_at:
				for assigned_time in self.watches_to_at[lit]:
					update_result, ng = self.check_assignment(assigned_time, control)

					if update_result == CONSTRAINT_CHECK["CONFLICT"]:

						self.logger.debug("immediately return the conflict!")
						self.logger.debug("adding nogood lits CONF: %s", ng)

						if not control.add_nogood(ng):
							self.unit_constraints = []
							return
						else:
							PropagationError("constraint for a conflict added but propagations continues")

		ng: List[int]
		for ng in self.unit_constraints:
			try:
				if not control.add_nogood(ng):  # or not control.propagate():
					self.logger.debug("assignment conflict because add_nogoog returned False: {}".format(
						control.assignment.has_conflict))
					self.logger.debug("added unit ng but prop stops!")
					self.unit_constraints = []
					break
			except RuntimeError as e:
				self.logger.debug("assignment conflict from runtime error: {}".format(control.assignment.has_conflict))
				for l in ng:
					self.logger.info("{}, {}".format(Map_Name_Lit.grab_name[l], control.assignment.value(l)))
				raise PropagationError(
					e + "\nwe tried to add a nogood but the assignment was already conflicting -> how didnt we realise this?")

		self.unit_constraints = []
	# the handler will call propagate


class TheoryConstraint2watch(TheoryConstraint):

	def __init__(self, constraint):

		super().__init__(constraint)
		self.logger = logging.getLogger(self.__module__ + "." + self.__class__.__name__)

	def build_watches(self, init) -> None:
		for assigned_time in self.existing_at:
			lits = self.form_nogood(assigned_time)
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

					self.logger.debug("propagating %i to assigned time %i", lit, assigned_time)

					result, ng = self.check_assignment(assigned_time, control)

					if result == CONSTRAINT_CHECK["CONFLICT"]:

						self.logger.debug("immediately return the conflict!")

						self.logger.debug("adding nogood lits CONF: %s", ng)

						if not control.add_nogood(ng):  # or not control.propagate():
							self.unit_constraints = []
							return
						else:
							self.logger.debug("constraint for a conflict added and propagations continues???")

					info = self.get_replacement_watch(assigned_time, lit, control)
					if info is not None:
						replacement_info.append(info)

		self.replace_watches(replacement_info, control)

		for ng in self.unit_constraints:
			self.logger.debug("adding nogood lits UNIT: %s", ng)
			self.logger.debug("lit names:")
			for l in ng:
				self.logger.debug(Map_Name_Lit.grab_name(l))

			if not control.add_nogood(ng):  # and control.propagate():
				self.logger.debug("added unit ng but prop stops!")
				self.unit_constraints = []
				return

		self.unit_constraints = []

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

		new_watch: Optional[int] = self.choose_lit(self.form_nogood(assigned_time), lit,
		                                           control)
		if new_watch is not None:
			return lit, new_watch, assigned_time

		return None

	def choose_lit(self, lits: Set[int], current_watch: int, control) -> Optional[int]:
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
