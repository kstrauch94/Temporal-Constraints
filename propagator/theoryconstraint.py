import clingo
import logging

import sys
import util
import time as time_module
from collections import defaultdict

CONSTRAINT_CHECK = { "NONE": None,
                    "UNIT": 1,
                    "CONFLICT": -1} 



class TimedConstraint:

    def __init__(self, names, lits, time, unit_callback):

        self.logger = logging.getLogger(self.__module__ + "." + self.__class__.__name__)

        self.names = names
        self.lits = lits
        self.time = time
        self.size = len(names)

        self.unit_callback = unit_callback

        self.truth = {}
        for name in self.names:
            self.truth[name] = None

        self.assigned = 0

        for l in lits:
            if l == 1:
                self.assigned += 1

    def update_lit(self, name):
        self.logger.debug("updated lit of time {}, of name {}".format(self.time, name))
        self.logger.debug("lits in const: {}".format(self.lits))
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

        elif self.assigned < 0:
            self.logger.debug("This should not happen! assigned < 0")

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
        self.t_atom_names = set()
        self.watches = {}
        self.lit_to_name = {}
        self.name_to_lit = {}
        self.active_constraints = {}

        self.unit_constraints = []

        self.parse_atoms(constraint)

        self.max_time = None

    def parse_atoms(self, constraint):
        for atom in constraint.elements:
            atom = str(atom)[1:-1]

            if atom.startswith("+."):
                sign = 1
                time_mod = 0
                arity = len(atom.split(","))
                name = atom[2:]
            elif atom.startswith("+~"):
                sign = 1
                time_mod = +1
                arity = len(atom.split(","))
                name = atom[2:]
            elif atom.startswith("-."):
                sign = -1
                time_mod = 0
                arity = len(atom.split(","))
                name = atom[2:]
            elif atom.startswith("-~"):
                sign = -1
                time_mod = +1
                arity = len(atom.split(","))
                name = atom[2:]

            name = name.replace(")", "")
            self.t_atom_info[name] = {"sign" : sign,
                                      "time_mod" : time_mod,
                                      "arity": arity,
                                      "name" : name}

            self.t_atom_names.add(name)

    def add_max_time(self, time):
        self.max_time = time

    def init_watches(self, s_atom, init):
        t_str = 0
        for name in self.t_atom_names:
            if str(s_atom.symbol).startswith(name+","):
                t = time_module.time()
                solver_lit = init.solver_literal(s_atom.literal) * self.t_atom_info[name]["sign"] 
                time = self.parse_time(s_atom)

                if self.max_time is not None and self.get_assigned_time(name, time) > self.max_time:
                    self.logger.debug("no watch for lit cause assigned time would be too big: {}".format(str(s_atom.symbol)))
                    continue

                self.watches[solver_lit] = time
    
                if solver_lit not in self.lit_to_name:
                    self.lit_to_name[solver_lit] = []
                
                self.lit_to_name[solver_lit].append((name,time))

                self.name_to_lit[name, time] = solver_lit

                self.logger.debug("watch: {}, solver lit {}, time {}".format(str(s_atom.symbol), solver_lit, time))
                self.logger.debug("name {} to lit: {}".format(name, self.name_to_lit[name, time]))
                init.add_watch(solver_lit)
                
                t_str += time_module.time() - t

        if ("where(1", 1) in self.name_to_lit:
            self.logger.debug("where(1, is lit {}".format(self.name_to_lit["where(1", 1]))
        
        return t_str    
        # TODO:
        # MAYBE ADD CHECK FOR NOGOODS OF SIZE 1?
        # DO it by making nogoods for all times and seeing if the resulting lists are size 1?

    def parse_time(self, s_atom):
        time = str(s_atom.symbol).split(",")[-1].replace(")","").strip()
        
        return int(time)

    def get_assigned_time(self, name, time):
        return time + self.t_atom_info[name]["time_mod"]

    def reverse_assigned_time(self, name, assigned_time):
        return assigned_time - self.t_atom_info[name]["time_mod"]

    def propagate(self, control, changes):
        self.logger.debug("Propagating for constraint: {}".format(self.t_atom_names))
        for lit in changes:
            if lit in self.watches:

                for name, time in self.lit_to_name[lit]:
                    assigned_time = self.get_assigned_time(name, time)
                    
                    self.logger.debug("propagating {} to time {} and assigned time {}".format(name, time, assigned_time))

                    if assigned_time not in self.active_constraints:
                        try:
                            for n in self.t_atom_names:
                                self.logger.debug("name: {}, reverse at: {}".format(n, self.reverse_assigned_time(n, assigned_time)))
                            constraint_lits = [self.name_to_lit[n, self.reverse_assigned_time(n, assigned_time)] for n in self.t_atom_names]
                            self.logger.debug("const_lits {}, form ng: {}".format(constraint_lits, self.form_nogood(assigned_time)))

                        except KeyError:
                            self.logger.debug("Here, we skipped creating a constraint with names {} and time {} for name {}".format(self.t_atom_names, time, name))
                            self.logger.debug("because one of them is not a watched literal")
                            continue
                        
                        c = TimedConstraint(self.t_atom_names, constraint_lits, assigned_time, self.unit_callback)
                        self.active_constraints[assigned_time] = c

                    update_result = self.active_constraints[assigned_time].update_lit(name)

                    if update_result == CONSTRAINT_CHECK["CONFLICT"]:
                        
                        self.logger.debug("immediately return the conflict!")
                        
                        ng = self.active_constraints[assigned_time].nogood #self.form_nogood(assigned_time)
                         
                        self.logger.debug("adding nogood lits CONF: {}".format(ng))
                        self.logger.debug("form nogood: {}".format(self.form_nogood(assigned_time)))

                        if not control.add_nogood(ng):
                            self.unit_constraints = []
                            return 1
                        else:
                            self.logger.debug("constraint for a conflict added and propagations continues???")


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
                self.logger.info("assignment conflict from runtime error: {}".format(control.assignment.has_conflict))
                for l in ng:
                    self.logger.info("{}, {}".format(self.lit_to_name[l], control.assignment.value(l)))
                raise RuntimeError(e)

            self.logger.debug("assignment conflict after adding ng: {}".format(control.assignment.has_conflict))
 
        self.unit_constraints = []

        # the handler will call propagate

        return 1
            
    def unit_callback(self, ng):
        self.unit_constraints.append(ng)
 
    def undo(self, thread_id, assign, changes):
        
        for lit in changes:
            if lit in self.watches:
                for name, time in self.lit_to_name[lit]:
                    assigned_time = self.get_assigned_time(name, time)
                    if assigned_time in self.active_constraints:
                        self.logger.debug("undoing {} of time {}".format(name, assigned_time))
                        self.active_constraints[assigned_time].undo_lit(name)

    def form_nogood(self, assigned_time):
        # with this function I can make nogoods just from an assigned time
        ng = set()
        self.logger.debug("Form nogoods for assigned time: {}, {}".format(assigned_time, self.t_atom_names))
        for name in self.t_atom_names:
            time = self.reverse_assigned_time(name, assigned_time)
            try:
                ng.add(self.name_to_lit[name, time])
            except KeyError:
                self.logger.debug("Keyerror for name: {}, this means it doesnt exist? maybe...".format(name))
                return []
        return list(ng)

    def check_assignment(self, at, control):
        true_count = 0
        for name in self.t_atom_names:
            time = self.reverse_assigned_time(name, at)
            if (name, time) not in self.name_to_lit:
                self.logger.debug("return NONE because name {} with time {} is not part of constraint".format(name, time))
                return CONSTRAINT_CHECK["NONE"]
            lit = self.name_to_lit[name, time]

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

    @util.Timer("tcinit")
    def __init__(self, constraint):

        self.logger = logging.getLogger(self.__module__ + "." + self.__class__.__name__)

        self.t_atom_info = {}
        self.t_atom_names = []
        self.atom_signatures = {}
        self.watches_to_at = defaultdict(list)
        self.at_to_watches = defaultdict(list)
        self.lit_to_name = defaultdict(list)
        self.name_to_lit = {}
        
        self.lit_to_at = defaultdict(list)

        self.unit_constraints = []

        self.parse_atoms(constraint)

        self.max_time = None

    @property
    def size(self):
        return len(self.t_atom_names)

    def parse_atoms(self, constraint):
        for atom in constraint.elements:
            signature = [atom.terms[0].arguments[0].name, len(atom.terms[0].arguments[0].arguments)+1]
            args = atom.terms[0].arguments[0].arguments

            term_type = atom.terms[0].name # this gives me the "type" of the term | e.g. for +~on(..) it would return +~
            
            name = str(atom.terms[0].arguments[0]).replace(")", ",")
            
            self.atom_signatures[name] = signature

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

            self.t_atom_info[name] = {"sign" : sign,
                                      "time_mod" : time_mod,
                                      "arity": signature[1],
                                      "name" : name,
                                      "args" : args}

            self.t_atom_names.append(name)

    def add_max_time(self, time):
        self.max_time = time

    #@profile
    def init_watches(self, s_atom, init):
        for name in self.t_atom_names:
            if str(s_atom.symbol).startswith(name):
                time = self.parse_time(s_atom)
                assigned_time = self.get_assigned_time(name, time)

                if self.max_time is not None and assigned_time > self.max_time:
                    self.logger.debug("no watch for lit cause assigned time would be too big: {}", s_atom.symbol)
                    continue
                
                solver_lit = init.solver_literal(s_atom.literal) * self.t_atom_info[name]["sign"] 


                if len(self.at_to_watches[assigned_time]) < 2:
                    self.logger.debug("watch: {}, {}, {}", str(s_atom.symbol), solver_lit, time)
                    self.at_to_watches[assigned_time].append(solver_lit)
                    self.watches_to_at[solver_lit].append(assigned_time)
                    init.add_watch(solver_lit)

    
                self.lit_to_name[solver_lit].append((name,time))

                self.name_to_lit[name, time] = solver_lit

                self.lit_to_at[solver_lit].append(assigned_time)

        # TODO:
        # check for literls that are true at top level
        # if check if any constraints are already unit here and add them?

        return    

    def parse_time(self, s_atom):
        time = str(s_atom.symbol).split(",")[-1].replace(")","").strip()
        
        return int(time)

    def get_assigned_time(self, name, time):
        return time + self.t_atom_info[name]["time_mod"]

    def reverse_assigned_time(self, name, assigned_time):
        return assigned_time - self.t_atom_info[name]["time_mod"]

    #@profile
    def propagate(self, control, changes):
        self.logger.debug("Propagating for constraint: {}", self.t_atom_names)
        for lit in changes:
            if lit in self.watches_to_at:
                for assigned_time in self.watches_to_at[lit]:

                    self.logger.debug("propagating {} to assigned time {}", lit, assigned_time)
                        
                    result, ng = self.check_assignment(assigned_time, control)

                    if result == CONSTRAINT_CHECK["CONFLICT"]:
                        
                        self.logger.debug("immediately return the conflict!")
                        
                        self.logger.debug("adding nogood lits CONF: {}", ng)
                        
                        if not control.add_nogood(ng): # or not control.propagate():
                            self.unit_constraints = []
                            return 1
                        else:
                            self.logger.debug("constraint for a conflict added and propagations continues???")

        for ng in self.unit_constraints:
            self.logger.debug("adding nogood lits UNIT: {}", ng)
            self.logger.debug("lit names:")
            for l in ng:
                self.logger.debug(self.lit_to_name[l])
            
            if not control.add_nogood(ng): # and control.propagate():
                self.logger.debug("added unit ng but prop stops!")
                self.unit_constraints = []
                return 1

        self.unit_constraints = []

        return 1

    def check_assignment(self, at, control):
        ng = []
        possible_watches = []
        true_count = 0
        for name in self.t_atom_names:
            time = self.reverse_assigned_time(name, at)
            if (name, time) not in self.name_to_lit:
                # if it is not in the dict then it is false always
                return CONSTRAINT_CHECK["NONE"], []

            lit = self.name_to_lit[name, time]

            if control.assignment.is_true(lit):
                # if its true
                ng.append(lit)
                true_count += 1
            elif control.assignment.is_false(lit):
                # if one is false then it doesnt matter
                return CONSTRAINT_CHECK["NONE"], []

            else:
                # if valye is None we still add it to ng
                ng.append(lit)

        if true_count == self.size:
            return CONSTRAINT_CHECK["CONFLICT"], ng
        elif true_count == self.size - 1:
            self.unit_constraints.append(ng)
            return CONSTRAINT_CHECK["UNIT"], []
        else:
            return CONSTRAINT_CHECK["NONE"], []
        

    def undo(self, thread_id, assign, changes):
        pass        

