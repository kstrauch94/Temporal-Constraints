import clingo
import logging

import sys
import untimed.util as util
import time as time_module
from collections import defaultdict

from typing import List, Dict, Tuple, Set, Callable, Any, Optional

CONSTRAINT_CHECK = { "NONE": 0,
					"UNIT": 1,
					"CONFLICT": -1} 


class TimedConstraintError(Exception):
	pass

class PropagationError(Exception):
	pass

class TheoryConstraint:

	def __init__(self, constraint):

		self.t_atom_info: Dict[str, Dict[str, Any]] = {}
		self.t_atom_names: List[str] = []
		self.atom_signatures: Set[Tuple[str, int]] = set()

		self.max_time: int
		self.min_time: Optional[int]

		self.parse_atoms(constraint)

	def parse_atoms(self, constraint) -> None:
		self.parse_constraint_times(constraint.term.arguments)
		for atom in constraint.elements:
			term_type: str = atom.terms[0].name # this gives me the "type" of the term | e.g. for +~on(..) it would return +~

			signature: Tuple[str, int] = (atom.terms[0].arguments[0].name, len(atom.terms[0].arguments[0].arguments)+1)
			
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

			self.t_atom_info[uq_name] = {"sign" : sign,
									  "time_mod" : time_mod,
									  "arity": signature[1],
									  "name" : name}

			self.t_atom_names.append(uq_name)

	def parse_constraint_times(self, times):
		if len(times) == 1:
			self.max_time = times[0].number
			self.min_time = None
		else:
			self.max_time = times[1].number
			self.min_time = times[0].number

	def parse_untimed_term(self, atom, term_type):

		signature: Tuple[str, int] = (atom.terms[0].arguments[0].name, len(atom.terms[0].arguments[0].arguments)+1)
		
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

		self.t_atom_info[uq_name] = {"sign" : sign,
								  "time_mod" : time_mod,
								  "arity": signature[1],
								  "name" : name}

		self.t_atom_names.append(uq_name)

	def init_watches(self, s_atom, init) -> None:

		uq_name :str
		for uq_name in self.t_atom_names:
			name: str = self.t_atom_info[uq_name]["name"]
			if str(s_atom.symbol).startswith(name):
				time: int = self.parse_time(s_atom)
				assigned_time: int = self.get_assigned_time(uq_name, time)

				if self.max_time is not None and assigned_time > self.max_time:
					self.logger.debug("no watch for lit cause assigned time would be too big: %s", s_atom.symbol)
					continue

				elif self.min_time is not None and assigned_time < self.min_time:
					self.logger.debug("no watch for lit cause assigned time would be too small: %s", s_atom.symbol)
					continue
				
				solver_lit: int = init.solver_literal(s_atom.literal) * self.t_atom_info[uq_name]["sign"] 

				self.lit_to_name[solver_lit].append((uq_name,assigned_time))

				self.name_to_lit[uq_name, assigned_time] = solver_lit

				self.at_to_lit[assigned_time].add(solver_lit)

	def parse_time(self, s_atom) -> int:
		time = str(s_atom.symbol).split(",")[-1].replace(")","").strip()
		
		return int(time)

	def get_assigned_time(self, uq_name: str, time: int) -> int:
		return time + self.t_atom_info[uq_name]["time_mod"]

	def reverse_assigned_time(self, uq_name: str, assigned_time: int) -> int:
		return assigned_time - self.t_atom_info[uq_name]["time_mod"]

	def form_nogood(self, assigned_time) -> List[int]:
		# with this function I can make nogoods just from an assigned time
		ng: Set[int] = set()
		self.logger.debug("Form nogoods for assigned time: {}, {}".format(assigned_time, self.t_atom_names))
		for uq_name in self.t_atom_names:
			ng.add(self.name_to_lit[uq_name, assigned_time])
		return list(ng)

	def undo(self, thread_id, assign, changes) -> None:
		pass

class TimedConstraint:

	def __init__(self, names: List[str], lits: List[int], time: int, unit_callback: Callable) -> None:

		self.logger = logging.getLogger(self.__module__ + "." + self.__class__.__name__)

		self.names: List[str] = names
		self.lits: List[int] = lits
		self.time: int = time
		self.size: int = len(names)

		self.unit_callback: Callable = unit_callback

		self.truth: Dict[str, Any] = {}

		for name in names:
			self.truth[name] = None

		self.assigned: int = 0

	def update_lit(self, name: str) -> int:
		self.logger.debug("updated lit of time {}, of name {}".format(self.time, name))
		self.logger.debug("lits in const: {}".format(self.lits))
		if self.truth[name] == 1:
			raise TimedConstraintError("assigning name {} to true when it was already true\nlits: {}".format(name, self.lits))
		self.truth[name] = 1
		self.assigned += 1

		return self.check()

	def check(self) -> int:

		if self.assigned == self.size:
			# constraint
			return CONSTRAINT_CHECK["CONFLICT"]

		elif self.assigned == self.size - 1:
			# unit
			self.unit_callback(self.nogood)

			return CONSTRAINT_CHECK["UNIT"]

		elif self.assigned > self.size:
			self.logger.debug("this should not happen! assigned > size")
			raise TimedConstraintError("assigned {} > size {}\nnames assigned: {}".format(self.assigned, self.size, self.truth))

		elif self.assigned < 0:
			self.logger.debug("This should not happen! assigned < 0")
			raise TimedConstraintError("assigned < 0")
		else:
			return CONSTRAINT_CHECK["NONE"]

	def undo_lit(self, name) -> None:
		if self.truth[name] is not None:
			self.truth[name] = None
			self.assigned -= 1

	@property
	def nogood(self) -> List[int]:
		return self.lits

class TheoryConstraintNaive(TheoryConstraint):

	def __init__(self, constraint) -> None:

		self.logger = logging.getLogger(self.__module__ + "." + self.__class__.__name__)

		self.t_atom_info: Dict[str, Dict[str, Any]] = {}
		self.t_atom_names: List[str] = []
		self.watches: Set[int] = set()
		self.lit_to_name: Dict[int, List[Tuple[str, int]]] = defaultdict(list)
		self.name_to_lit: Dict[Tuple[str, int], int] = {}
		self.at_to_lit: Dict[int, Set[int]] = defaultdict(set)
		self.active_constraints: Dict[int, TimedConstraint] = {}

		self.atom_signatures: Set[Tuple[str, int]] = set()

		self.unit_constraints: List[List[int]] = []

		self.max_time: int
		self.min_time: Optional[int]

		self.parse_atoms(constraint)

	def propagate_init(self, init) -> None:
		done_at = []
		for assigned_time, lits in self.at_to_lit.items():
			if len(lits) < self.size:
				# if this happens, it could be because for one
				# of the names in the constraint for a particular
				# assigned time there was no symbolic atom for it
				# this means that the atom does not exist
				# hence, it is false and the nogood is useless
				# so we delete it
				done_at.append(assigned_time)
				continue

			# careful here, check assignment 2 only looks at 
			# the lits we have for that particular assigned time
			# if a lit is not added because it doesnt exist
			# it will NOT count it as false
			# and it might return that the clause is unit or conflicting
			# when in fact its not
			result = self.check_assignment(assigned_time, init)
			if result == CONSTRAINT_CHECK["CONFLICT"]:
				ng = self.form_nogood(assigned_time)
				init.add_clause([-l for l in ng])

			elif result == CONSTRAINT_CHECK["UNIT"]:
				# if nogood is already unit at init
				# then we can add the clause so it propagates at time 0
				# then we delete assigned time because 
				# it will never pop up again
				
				ng = self.form_nogood(assigned_time)
				init.add_clause([-l for l in self.at_to_lit[assigned_time]])
				done_at.append(assigned_time)

		for dat in done_at:
			self.at_to_lit.pop(dat)

	def build_watches(self, init) -> None:
		for assigned_time, lits in self.at_to_lit.items():
			for lit in lits:
				init.add_watch(lit)
				self.watches.add(lit)

	def propagate(self, control, changes) -> None:
		self.logger.debug("Propagating for constraint: {}".format(self.t_atom_names))
		for lit in changes:
			if lit in self.watches:

				for uq_name, assigned_time in self.lit_to_name[lit]:
					
					self.logger.debug("propagating {} to time {} and assigned time {}".format(uq_name, 
																					   self.reverse_assigned_time(uq_name, assigned_time), 
																					   assigned_time))

					if assigned_time not in self.active_constraints:
						try:
							for n in self.t_atom_names:
								self.logger.debug("name: {}, reverse at: {}".format(n, self.reverse_assigned_time(n, assigned_time)))

							#constraint_lits = [self.name_to_lit[n, assigned_time] for n in self.t_atom_names]
							constraint_lits = self.form_nogood(assigned_time)
							self.logger.debug("const_lits {}, form ng: {}".format(constraint_lits, self.form_nogood(assigned_time)))

						except KeyError:
							self.logger.debug("Here, we skipped creating a constraint with names {} and time {} for name {}".format(self.t_atom_names, assigned_time, uq_name))
							self.logger.debug("because one of them is not a watched literal")
							continue
						
						c = TimedConstraint(self.t_atom_names, constraint_lits, assigned_time, self.unit_callback)
						self.active_constraints[assigned_time] = c

					update_result = self.active_constraints[assigned_time].update_lit(uq_name)

					if update_result == CONSTRAINT_CHECK["CONFLICT"]:
						
						self.logger.debug("immediately return the conflict!")
						
						ng = self.active_constraints[assigned_time].nogood #self.form_nogood(assigned_time)
						 
						self.logger.debug("adding nogood lits CONF: {}".format(ng))
						self.logger.debug("form nogood: {}".format(self.form_nogood(assigned_time)))

						if not control.add_nogood(ng):
							self.unit_constraints = []
							return 
						else:
							PropagationError("constraint for a conflict added but propagations continues")

		ng: List[int]
		for ng in self.unit_constraints:
			self.logger.debug("assignment conflict before adding ng: {}".format(control.assignment.has_conflict))
			self.logger.debug("adding nogood lits UNIT: {}".format(ng))
			self.logger.debug("lit names:")
			for l in ng:
				self.logger.debug("{}, {}".format(self.lit_to_name[l], control.assignment.value(l)))
		   
			try:
				if not control.add_nogood(ng): # or not control.propagate():
					self.logger.debug("assignment conflict because add_nogoog returned False: {}".format(control.assignment.has_conflict))
					self.logger.debug("added unit ng but prop stops!")
					self.unit_constraints = []
					break
			except RuntimeError as e:
				self.logger.debug("assignment conflict from runtime error: {}".format(control.assignment.has_conflict))
				for l in ng:
					self.logger.info("{}, {}".format(self.lit_to_name[l], control.assignment.value(l)))
				raise PropagationError(e + "\nwe tried to add a nogood but the assignment was already conflicting -> how didnt we realise this?")

			self.logger.debug("assignment conflict after adding ng: {}".format(control.assignment.has_conflict))
 
		self.unit_constraints = []

		# the handler will call propagate
			
	def unit_callback(self, ng) -> None:
		self.unit_constraints.append(ng)
 
	def undo(self, thread_id, assign, changes) -> None:
		
		for lit in changes:
			if lit in self.watches:
				for uq_name, assigned_time in self.lit_to_name[lit]:

					if assigned_time in self.active_constraints:
						self.logger.debug("undoing {} of time {}".format(uq_name, assigned_time))
						self.active_constraints[assigned_time].undo_lit(uq_name)

	def check_assignment(self, assigned_time, control) -> int:
		true_count: int = 0
		for uq_name in self.t_atom_names:

			if (uq_name, assigned_time) not in self.name_to_lit:
				self.logger.debug("return NONE because name {} with time {} is not part of constraint".format(uq_name, assigned_time))
				return CONSTRAINT_CHECK["NONE"]
			lit: int = self.name_to_lit[uq_name, assigned_time]

			if control.assignment.is_true(lit):
				# if its true
				true_count += 1
			elif control.assignment.is_false(lit):
				# if one is false then it doesnt matter
				self.logger.debug("check is none cause one lit is false: {}".format(lit))
				return CONSTRAINT_CHECK["NONE"]

		if true_count == self.size:
			self.logger.debug("check returning a conflict!")
			return CONSTRAINT_CHECK["CONFLICT"]
		elif true_count == self.size - 1:
			self.logger.debug("check returning unit?")
			return CONSTRAINT_CHECK["UNIT"]
		else:
			self.logger.debug("check returning none?")
			return CONSTRAINT_CHECK["NONE"]
		
	def check(self, control) -> None:
		self.logger.debug("checking constraint {}".format(self.t_atom_names))
		for at in range(1, self.max_time + 1):
			self.logger.debug("for at: {}".format(at))
			if self.check_assignment(at, control) == CONSTRAINT_CHECK["CONFLICT"]:
				ng: List[int] = self.form_nogood(at)
				control.add_nogood(ng)
				return

	@property
	def size(self) -> int:
		return len(self.t_atom_names)

class TheoryConstraint2watch(TheoryConstraint):

	def __init__(self, constraint):

		self.logger = logging.getLogger(self.__module__ + "." + self.__class__.__name__)

		self.t_atom_info: Dict[str, Dict[str, Any]] = {}
		self.t_atom_names: List[str] = []
		self.atom_signatures: Set[Tuple[str, int]] = set()
		self.watches_to_at: Dict[int, Set[int]] = defaultdict(set)
		self.at_to_watches: Dict[int, Set[int]] = defaultdict(set)
		self.watches: Set[int] = set()

		self.lit_to_name: Dict[int, List[Tuple[str, int]]] = defaultdict(list)
		self.name_to_lit: Dict[Tuple[str, int], int] = {}
		
		self.lit_to_at: Dict[int, Set[int]] = defaultdict(set)
		self.at_to_lit: Dict[int, Set[int]] = defaultdict(set)

		self.unit_constraints: List[List[int]] = []

		self.max_time: int
		self.min_time: Optional[int]
		
		self.name = constraint

		self.parse_atoms(constraint)

	@property
	def size(self) -> int:
		return len(self.t_atom_names)

	#@profile
	def propagate_init(self, init, propagate: bool = True) -> None:
		done_at = []
		for assigned_time, lits in self.at_to_lit.items():
			if len(lits) < self.size:
				# if this happens, it could be because for one
				# of the names in the constraint for a particular
				# assigned time there was no symbolic atom for it
				# this means that the atom does not exist
				# hence, it is false and the nogood is useless
				# so we delete it
				done_at.append(assigned_time)
				continue

			# careful here, check assignment 2 only looks at 
			# the lits we have for that particular assigned time
			# if a lit is not added because it doesnt exist
			# it will NOT count it as false
			# and it might return that the clause is unit or conflicting
			# when in fact its not
			result, ng = self.check_assignment2(assigned_time, init)
			if result == CONSTRAINT_CHECK["CONFLICT"]:
				init.add_clause([-l for l in ng])

			elif result == CONSTRAINT_CHECK["UNIT"]:
				# if nogood is already unit at init
				# then we can add the clause so it propagates at time 0
				# then we delete assigned time because 
				# it will never pop up again

				init.add_clause([-l for l in self.at_to_lit[assigned_time]])
				done_at.append(assigned_time)

		for dat in done_at:
			self.at_to_lit.pop(dat)

	def build_watches(self, init) -> None:
		for at, lits in self.at_to_lit.items():
			for lit in lits:
				self.lit_to_at[lit].add(at)

		for assigned_time, lits in self.at_to_lit.items():
			for lit in lits:
				if len(self.at_to_watches[assigned_time]) >= 2:
					break
				self.at_to_watches[assigned_time].add(lit)
				self.watches_to_at[lit].add(assigned_time)
				self.watches.add(lit)
				init.add_watch(lit)

	#@profile
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
						
						if not control.add_nogood(ng): # or not control.propagate():
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
				self.logger.debug(self.lit_to_name[l])
			
			if not control.add_nogood(ng): # and control.propagate():
				self.logger.debug("added unit ng but prop stops!")
				self.unit_constraints = []
				return

		self.unit_constraints = []

	def replace_watches(self, info: List[Tuple[int, int, int]], control) -> None:
		
		for old_watch, new_watch, assigned_time in info:
			self.logger.debug("removing watch %i and replacing it by watch %i for assigned time %i", old_watch, new_watch, assigned_time)

			self.logger.debug("old at to watches %s", self.at_to_watches[assigned_time])

			#remove the lit as a watch for constraint assigned_time
			self.watches_to_at[old_watch].remove(assigned_time)
			self.at_to_watches[assigned_time].remove(old_watch)

			# add new watch as a watch for constraint assigned_time
			self.watches_to_at[new_watch].add(assigned_time)
			self.at_to_watches[assigned_time].add(new_watch)

			self.logger.debug("new watch to at %s", self.at_to_watches[assigned_time])
			self.logger.debug("old watches: %s", self.watches)
			# add new watch
			# if it isnt watched yet

			self.watches.add(new_watch)

			if not control.has_watch(new_watch):
				control.add_watch(new_watch)

			# if lit is not watching a constraint eliminate it
			if len(self.watches_to_at[old_watch]) == 0:
				control.remove_watch(old_watch)
				self.watches.remove(old_watch)

			self.logger.debug("new watches: %s", self.watches)


	def get_replacement_watch(self, assigned_time: int, lit: int, control) -> Optional[Tuple[int, int, int]]:
		"""
		choose a new watch for the given assigned time if possible
		"""

		new_watch: Optional[int] = self.choose_lit(self.at_to_lit[assigned_time], self.at_to_watches[assigned_time], control)

		if new_watch is not None:
			return lit, new_watch, assigned_time

		return None

	def choose_lit(self, lits: Set[int], exempt: Set[int], control) -> Optional[int]:
		"""
		return a watch that has not been assigned yet
		if every watch has been assigned, return nothing
		"""
		for possible_watch in lits:
			if possible_watch not in exempt:
				if control.assignment.value(possible_watch) is None:
					return possible_watch

		return None

	def check_assignment(self, assigned_time, control) -> Tuple[int, List[int]]:
		# not sure which one is faster
		ng: List[int] = []
		true_count: int = 0

		for uq_name in self.t_atom_names:
			if (uq_name, assigned_time) not in self.name_to_lit:
				# if it is not in the dict then it is false always
				return CONSTRAINT_CHECK["NONE"], []

			lit: int = self.name_to_lit[uq_name, assigned_time]

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
			return CONSTRAINT_CHECK["UNIT"], []
		else:
			return CONSTRAINT_CHECK["NONE"], []

	def check_assignment2(self, assigned_time, control) -> Tuple[int, List[int]]:
		ng: List[int] = []
		true_count: int = 0

		if assigned_time not in self.at_to_lit:
			return CONSTRAINT_CHECK["NONE"], []

		for lit in self.at_to_lit[assigned_time]:
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
			return CONSTRAINT_CHECK["UNIT"], []
		else:
			return CONSTRAINT_CHECK["NONE"], [] 

class TheoryConstraint2watchBig(TheoryConstraint2watch):

	...