import clingo
import logging

import sys
import util
import time as time_module


CONSTRAINT_CHECK = { "NONE": None,
                    "UNIT": 1,
                    "CONFLICT": -1} 

TIMERS = {}
TIMERS["INIT"] = 0
TIMERS["PROP"] = 0

THEORY = "untimed_theory.lp"


def setup_logger():

    root_logger = logging.getLogger()
    root_logger.setLevel(logging.INFO)

    logger_handler = logging.StreamHandler(stream=sys.stdout)

    formatter = logging.Formatter("%(levelname)s:%(name)s:\t%(message)s")

    logger_handler.setFormatter(formatter)

    root_logger.addHandler(logger_handler)


class TimedConstraint:

    def __init__(self, names, lits, time):

        self.logger = logging.getLogger(self.__module__ + "." + self.__class__.__name__)

        self.names = names
        self.lits = lits
        self.time = time
        self.size = len(names)

        self.truth = {}
        for name in self.names:
            self.truth[name] = None

        self.assigned = 0

    def update_lit(self, name):
        self.logger.debug("updated lit of time {}, of name {}".format(self.time, name))
        self.truth[name] = 1
        self.assigned += 1

        return self.check()

    def check(self):

        if self.assigned == self.size:
            # constraint
            return CONSTRAINT_CHECK["CONFLICT"]

        elif self.assigned == self.size - 1:
            # unit
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

class TheoryConstraint:

    def __init__(self, constraint):

        self.logger = logging.getLogger(self.__module__ + "." + self.__class__.__name__)

        self.t_atom_info = {}
        self.t_atom_names = set()
        self.watches = {}
        self.lit_to_name = {}
        self.name_to_lit = {}
        self.active_constraints = {}

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
            if str(s_atom.symbol).startswith(name):
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

                self.logger.debug("watch: {}, {}, {}".format(str(s_atom.symbol), solver_lit, time))
                init.add_watch(solver_lit)
                
                t_str += time_module.time() - t


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
                            constraint_lits = [self.name_to_lit[n, self.reverse_assigned_time(n, assigned_time)] for n in self.t_atom_names]
                        except KeyError:
                            self.logger.debug("Here, we skipped creating a constraint with names {} and time {} for name {}".format(self.t_atom_names, time, name))
                            self.logger.debug("because one of them is not a watched literal")
                            continue

                        c = TimedConstraint(self.t_atom_names, constraint_lits, assigned_time)
                        self.active_constraints[assigned_time] = c

                    update_result = self.active_constraints[assigned_time].update_lit(name)

                    if update_result == CONSTRAINT_CHECK["CONFLICT"]:
                        
                        self.logger.debug("immediately return the conflict!")
                        
                        ng = self.active_constraints[assigned_time].nogood #self.form_nogood(assigned_time)
                        
                        self.logger.debug("adding nogood lits CONF: {}".format(ng))
                        
                        continue_propagation = control.add_nogood(ng)
                        if not continue_propagation:
                            return
                        else:
                            self.logger.debug("constraint for a conflict added and propagations continues???")

        #if we make it here there were no conflicts and we can check for units
        for time, gc in self.active_constraints.items():
            if gc.check() == CONSTRAINT_CHECK["UNIT"]:
                ng = gc.nogood #self.form_nogood(time)
                if ng != []:
                    self.logger.debug("adding nogood lits UNIT: {}".format(ng))
                    self.logger.debug("lit names:")
                    for l in ng:
                        self.logger.debug(self.lit_to_name[l])

                    #try:
                    if not control.add_nogood(ng): # and control.propagate():
                        self.logger.debug("added unit ng but prop stops!")
                        break
                    #except RuntimeError:
                    #    continue

        control.propagate()

        return

        return ngs, CONSTRAINT_CHECK["UNIT"]

    def undo(self, changes):
        
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

class ConstraintPropagator:

    def __init__(self):
        self.logger = logging.getLogger(self.__module__ + "." + self.__class__.__name__)

        self.constraints = []
        self.lit_to_constraints = {}
        self.max_time = None
    
    def init(self, init):
        t = time_module.time()


        t2 = time_module.time()
        for t_atom in init.theory_atoms:
            if t_atom.term.name == "constraint":
                self.logger.debug(str(t_atom))
                self.constraints.append(TheoryConstraint(t_atom))
            elif t_atom.term.name == "time":
                self.logger.debug(str(t_atom))
                self.max_time = int(str(t_atom.elements[0]).replace("+","")[1:-1])
   
        self.logger.info("init theory: {}".format(time_module.time() - t2))

        for c in self.constraints:
            # add a max time for the constraint
            # this has to be done before init_watches
            c.add_max_time(self.max_time)

        t3 = time_module.time()
        for atom in init.symbolic_atoms:
            for c in self.constraints:
                c.init_watches(atom, init)

        self.logger.info("init watches: {}".format(time_module.time() - t3))

        for c in self.constraints:
            for lit in c.watches.keys():
                if lit in self.lit_to_constraints:
                    self.lit_to_constraints[lit].append(c)
                else:
                    self.lit_to_constraints[lit] = [c]

        TIMERS["INIT"] += time_module.time() - t

        self.logger.info("time for init: {}".format(TIMERS["INIT"]))

    def propagate(self, control, changes):
        t = time_module.time()
        
        all_nogoods = []
        for tc in self.constraints:
            tc.propagate(control, changes)

        TIMERS["PROP"] += time_module.time() - t

    def undo(self, thread_id, assign, changes):
        t = time_module.time()
        for tc in self.constraints:
            tc.undo(changes)

        TIMERS["PROP"] += time_module.time() - t
