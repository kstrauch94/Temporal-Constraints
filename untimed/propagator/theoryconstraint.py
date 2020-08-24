import clingo
import logging

import sys
import untimed.util as util
import time as time_module
from collections import defaultdict

CONSTRAINT_CHECK = { "NONE": None,
					"UNIT": 1,
					"CONFLICT": -1} 


class TimedConstraintError(Exception):
	pass

class PropagationError(Exception):
	pass

class TimedConstraint:

	def __init__(self, names, lits, time, unit_callback):

		self.logger = logging.getLogger(self.__module__ + "." + self.__class__.__name__)

		self.names = names
		self.lits = lits
		self.time = time
		self.size = len(names)

		self.unit_callback = unit_callback

		self.truth = {}
		for name in names:
			self.truth[name] = None

		self.assigned = 0

	def update_lit(self, name):
		self.logger.debug("updated lit of time {}, of name {}".format(self.time, name))
		self.logger.debug("lits in const: {}".format(self.lits))
		if self.truth[name] == 1:
			raise TimedConstraintError("assigning name {} to true when it was already true\nlits: {}".format(name, self.lits))
		self.truth[name] = 1
		self.assigned += 1

		return self.check()

	def check(self):

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

	def undo_lit(self, name):
		if self.truth[name] is not None:
			self.truth[name] = None
			self.assigned -= 1

	@property
	def nogood(self):
		return self.lits

class TheoryConstraintNaive:

	def __init__(self, constraint):

		self.logger = logging.getLogger(self.__module__ + "." + self.__class__.__name__)

		self.t_atom_info = {}
		self.t_atom_names = []
		self.watches = set()
		self.lit_to_name = {}
		self.name_to_lit = {}
		self.active_constraints = {}

		self.atom_signatures = set()

		self.unit_constraints = []

		self.parse_atoms(constraint)

		self.max_time = None

	def parse_atoms(self, constraint):
		for atom in constraint.elements:
			signature = (atom.terms[0].arguments[0].name, len(atom.terms[0].arguments[0].arguments)+1)
			args = atom.terms[0].arguments[0].arguments

			term_type = atom.terms[0].name # this gives me the "type" of the term | e.g. for +~on(..) it would return +~
			
			name = str(atom.terms[0].arguments[0]).replace(")", ",")

			uq_name = term_type + name
			
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
									  "name" : name,
									  "args" : args}

			self.t_atom_names.append(uq_name)

	def add_max_time(self, time):
		self.max_time = time

	def init_watches(self, s_atom, init):
		for uq_name in self.t_atom_names:
			name = self.t_atom_info[uq_name]["name"]
			self.logger.debug("testing uq_name {} and symbol {}".format(uq_name, str(s_atom.symbol)))
			if str(s_atom.symbol).startswith(name):
				t = time_module.time()
				solver_lit = init.solver_literal(s_atom.literal) * self.t_atom_info[uq_name]["sign"] 
				
				if solver_lit == 1:
					continue

				time = self.parse_time(s_atom)

				assigned_time = self.get_assigned_time(uq_name, time)

				if self.max_time is not None and assigned_time > self.max_time:
					self.logger.debug("no watch for lit cause assigned time would be too big: {}".format(str(s_atom.symbol)))
					continue
	
				if solver_lit not in self.lit_to_name:
					self.lit_to_name[solver_lit] = []
				
				self.lit_to_name[solver_lit].append((uq_name,assigned_time))

				self.name_to_lit[uq_name, assigned_time] = solver_lit

				self.logger.debug("watch: {}, solver lit {}, time {}, at {}".format(str(s_atom.symbol), solver_lit, time, assigned_time))
				self.logger.debug("name {} to lit: {}".format(uq_name, self.name_to_lit[uq_name, assigned_time]))
				
	def propagate_init(self, init):
		return

	def build_watches(self, init):
		for lit, name_at in self.lit_to_name.items():
			init.add_watch(lit)
			self.watches.add(lit)


	def parse_time(self, s_atom):
		time = str(s_atom.symbol).split(",")[-1].replace(")","").strip()
		
		return int(time)

	def get_assigned_time(self, uq_name, time):
		return time + self.t_atom_info[uq_name]["time_mod"]

	def reverse_assigned_time(self, uq_name, assigned_time):
		return assigned_time - self.t_atom_info[uq_name]["time_mod"]

	def propagate(self, control, changes):
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

							constraint_lits = [self.name_to_lit[n, assigned_time] for n in self.t_atom_names]

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
							return 1
						else:
							PropagationError("constraint for a conflict added but propagations continues")


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

		return 1
			
	def unit_callback(self, ng):
		self.unit_constraints.append(ng)
 
	def undo(self, thread_id, assign, changes):
		
		for lit in changes:
			if lit in self.watches:
				for uq_name, assigned_time in self.lit_to_name[lit]:

					if assigned_time in self.active_constraints:
						self.logger.debug("undoing {} of time {}".format(uq_name, assigned_time))
						self.active_constraints[assigned_time].undo_lit(uq_name)

	def form_nogood(self, assigned_time):
		# with this function I can make nogoods just from an assigned time
		ng = set()
		self.logger.debug("Form nogoods for assigned time: {}, {}".format(assigned_time, self.t_atom_names))
		for uq_name in self.t_atom_names:
			try:
				ng.add(self.name_to_lit[uq_name, assigned_time])
			except KeyError:
				self.logger.debug("Keyerror for name: {}, this means it doesnt exist? maybe...".format(uq_name))
				return []
		return list(ng)

	def check_assignment(self, assigned_time, control):
		true_count = 0
		for uq_name in self.t_atom_names:

			if (uq_name, assigned_time) not in self.name_to_lit:
				self.logger.debug("return NONE because name {} with time {} is not part of constraint".format(uq_name, assigned_time))
				return CONSTRAINT_CHECK["NONE"]
			lit = self.name_to_lit[uq_name, assigned_time]

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
		
	def check(self, control):
		self.logger.debug("checking constraint {}".format(self.t_atom_names))
		for at in range(1, self.max_time + 1):
			self.logger.debug("for at: {}".format(at))
			if self.check_assignment(at, control) == CONSTRAINT_CHECK["CONFLICT"]:
				ng = self.form_nogood(at)
				self.control.add_nogood(ng)
				return

	@property
	def size(self):
		return len(self.t_atom_names)

class TheoryConstraint2watch:

	def __init__(self, constraint):

		self.logger = logging.getLogger(self.__module__ + "." + self.__class__.__name__)

		self.t_atom_info = {}
		self.t_atom_names = []
		self.atom_signatures = set()
		self.watches_to_at = defaultdict(set)
		self.at_to_watches = defaultdict(set)
		self.watches = set()

		self.lit_to_name = defaultdict(list)
		self.name_to_lit = {}
		
		self.lit_to_at = defaultdict(set)
		self.at_to_lit = defaultdict(set)

		self.unit_constraints = []

		self.parse_atoms(constraint)

		self.max_time = None

		self.name = constraint

	@property
	def size(self):
		return len(self.t_atom_names)

	def parse_atoms(self, constraint):
		for atom in constraint.elements:
			signature = (atom.terms[0].arguments[0].name, len(atom.terms[0].arguments[0].arguments)+1)
			args = atom.terms[0].arguments[0].arguments

			term_type = atom.terms[0].name # this gives me the "type" of the term | e.g. for +~on(..) it would return +~
			
			name = str(atom.terms[0].arguments[0]).replace(")", ",")

			uq_name = term_type + name
			
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
									  "name" : name,
									  "args" : args}

			self.t_atom_names.append(uq_name)

	def add_max_time(self, time):
		self.max_time = time

	#@profile
	def init_watches(self, s_atom, init):

		for uq_name in self.t_atom_names:
			name = self.t_atom_info[uq_name]["name"]
			if str(s_atom.symbol).startswith(name):
				time = self.parse_time(s_atom)
				assigned_time = self.get_assigned_time(uq_name, time)

				if self.max_time is not None and assigned_time > self.max_time:
					self.logger.debug("no watch for lit cause assigned time would be too big: %s", s_atom.symbol)
					continue
				
				solver_lit = init.solver_literal(s_atom.literal) * self.t_atom_info[uq_name]["sign"] 

				self.lit_to_name[solver_lit].append((uq_name,assigned_time,time))

				self.name_to_lit[uq_name, assigned_time] = solver_lit

				self.at_to_lit[assigned_time].add(solver_lit)

		return  

	#@profile
	def propagate_init(self, init, propagate=True):
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

	def build_watches(self, init):
		for at in self.at_to_lit:
			for lit in self.at_to_lit[at]:
				self.lit_to_at[lit].add(at)

		for assigned_time, lits in self.at_to_lit.items():
			for lit in lits:
				if len(self.at_to_watches[assigned_time]) >= 2:
					break
				self.at_to_watches[assigned_time].add(lit)
				self.watches_to_at[lit].add(assigned_time)
				self.watches.add(lit)
				init.add_watch(lit)

	def parse_time(self, s_atom):
		time = str(s_atom.symbol).split(",")[-1].replace(")","").strip()
		
		return int(time)

	def get_assigned_time(self, uq_name, time):
		return time + self.t_atom_info[uq_name]["time_mod"]

	def reverse_assigned_time(self, uq_name, assigned_time):
		return assigned_time - self.t_atom_info[uq_name]["time_mod"]

	#@profile
	def propagate(self, control, changes):
		self.logger.debug("Propagating for constraint: %s", self.t_atom_names)
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
							return 1
						else:
							PropagationError("constraint for a conflict added but propagations continues")

		for ng in self.unit_constraints:
			self.logger.debug("adding nogood lits UNIT: %s", ng)
			self.logger.debug("lit names:")
			for l in ng:
				self.logger.debug(self.lit_to_name[l])
			
			if not control.add_nogood(ng): # and control.propagate():
				self.logger.debug("added unit ng but prop stops!")
				self.unit_constraints = []
				return 1

		self.unit_constraints = []

		return 1

	def check_assignment(self, assigned_time, control):
		# not sure which one is faster
		ng = []
		true_count = 0

		for uq_name in self.t_atom_names:
			if (uq_name, assigned_time) not in self.name_to_lit:
				# if it is not in the dict then it is false always
				return CONSTRAINT_CHECK["NONE"], []

			lit = self.name_to_lit[uq_name, assigned_time]

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

	def check_assignment2(self, assigned_time, control):
		ng = []
		true_count = 0

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

	def form_nogood(self, assigned_time):
		# with this function I can make nogoods just from an assigned time
		ng = set()
		self.logger.debug("Form nogoods for assigned time: {}, {}".format(assigned_time, self.t_atom_names))
		for uq_name in self.t_atom_names:
			try:
				ng.add(self.name_to_lit[uq_name, assigned_time])
			except KeyError:
				self.logger.debug("Keyerror for name: {}, this means it doesnt exist? maybe...".format(uq_name))
				return []
		return list(ng)

	def undo(self, thread_id, assign, changes):
		pass    

class TheoryConstraint2watchBig(TheoryConstraint2watch):

	def propagate(self, control, changes):
		self.logger.debug("Propagating for constraint: %s", self.t_atom_names)
		
		replacement_info = []
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
							return 1
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
				return 1

		self.unit_constraints = []

		return 1

	def replace_watches(self, info, control):
		
		for old_watch, new_watch, assigned_time in info:
			self.logger.debug("removing watch %i and replacing it by watch %i for assigned time %i", old_watch, new_watch, assigned_time)

			#remove the lit as a watch for constraint assigned_time
			self.watches_to_at[old_watch].remove(assigned_time)
			self.at_to_watches[assigned_time].remove(old_watch)

			# add new watch as a watch for constraint assigned_time
			self.watches_to_at[new_watch].add(assigned_time)
			self.at_to_watches[assigned_time].add(new_watch)

			# add new watch
			# if it isnt watched yet
			if not control.has_watch(new_watch):
				control.add_watch(new_watch)
				self.watches.add(new_watch)

			# if lit is not watching a constraint eliminate it
			if len(self.watches_to_at[old_watch]) == 0:
				control.remove_watch(old_watch)
				self.watches.remove(old_watch)

	def get_replacement_watch(self, assigned_time, lit, control):
		"""
		choose a new watch for the given assigned time if possible
		"""

		new_watch = self.choose_lit(self.at_to_lit[assigned_time], self.at_to_watches[assigned_time], control)

		if new_watch is not None:
			return [lit, new_watch, assigned_time]

		return None

	def choose_lit(self, lits, exempt, control):
		# return a watch that has not been assigned yet
		# if every watch has been assigned, return nothing
		for possible_watch in lits:
			if possible_watch not in exempt:
				if control.assignment.value(possible_watch) is None:
					return possible_watch

		return None
