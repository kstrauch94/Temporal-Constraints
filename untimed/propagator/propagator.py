import clingo
import logging

import sys
import untimed.util as util
import time as time_module
from collections import defaultdict

from untimed.propagator.theoryconstraint import TheoryConstraintNaive
from untimed.propagator.theoryconstraint import TheoryConstraint2watch


class ConstraintPropagator:

    def __init__(self, tc_class=TheoryConstraintNaive):
        self.logger = logging.getLogger(self.__module__ + "." + self.__class__.__name__)

        self.constraints = []
        self.lit_to_constraints = {}
        self.max_time = None

        self.tc_class = tc_class

    @util.Timer("Init") 
    def init(self, init):
        for t_atom in init.theory_atoms:
            if t_atom.term.name == "constraint":
                self.logger.debug(str(t_atom))
                self.constraints.append(self.tc_class(t_atom))
            elif t_atom.term.name == "time":
                self.logger.debug(str(t_atom))
                self.max_time = int(str(t_atom.elements[0]).replace("+","")[1:-1])
   
        for c in self.constraints:
            # add a max time for the constraint
            # this has to be done before init_watches
            c.add_max_time(self.max_time)

        for atom in init.symbolic_atoms:
            for c in self.constraints:
                c.init_watches(atom, init)

        for c in self.constraints:
            for lit in c.watches.keys():
                if lit in self.lit_to_constraints:
                    self.lit_to_constraints[lit].append(c)
                else:
                    self.lit_to_constraints[lit] = [c]
    
    @util.Timer("Propagation")
    def propagate(self, control, changes):
        
        for tc in self.constraints:
            tc.propagate(control, changes)
            if not control.propagate():
                return
    
    @util.Timer("undo")
    def undo(self, thread_id, assign, changes):
        for tc in self.constraints:
            tc.undo(thread_id, assign, changes)

    @util.Timer("check")
    def check(self, control):

        self.logger.debug("check")
        for tc in self.constraints:
            tc.check(control)
            if not control.propagate():
                return

    def print_stats(self):
        self.logger.info(util.Timer.timers)


class ConstraintPropagator2:

    def __init__(self, tc_class=TheoryConstraint2watch):
        self.logger = logging.getLogger(self.__module__ + "." + self.__class__.__name__)

        self.constraints = []
        self.lit_to_constraints = {}
        self.max_time = None

        self.tc_class = tc_class
    
    @util.Timer("Init")
    def init(self, init):

        for t_atom in init.theory_atoms:
            if t_atom.term.name == "constraint":
                self.logger.debug(str(t_atom))
                self.constraints.append(self.tc_class(t_atom))
            elif t_atom.term.name == "time":
                self.logger.debug(str(t_atom))
                self.max_time = int(str(t_atom.elements[0]).replace("+","")[1:-1])
   
        for c in self.constraints:
            # add a max time for the constraint
            # this has to be done before init_watches
            c.add_max_time(self.max_time)
        
        for c in self.constraints:
            for name in c.t_atom_names:
                for s_atom in init.symbolic_atoms.by_signature(*c.atom_signatures[name]):
                    c.init_watches(s_atom, init)
        
        for c in self.constraints:
            for lit in c.watches:
                if lit in self.lit_to_constraints:
                    self.lit_to_constraints[lit].append(c)
                else:
                    self.lit_to_constraints[lit] = [c]
    
    @util.Timer("Propagation")
    def propagate(self, control, changes):
        
        all_nogoods = []
        for tc in self.constraints:
            tc.propagate(control, changes)
            if not control.propagate():
                return

    @util.Timer("undo")
    def undo(self, thread_id, assign, changes):
        
        for tc in self.constraints:
            tc.undo(thread_id, assign, changes)    

    def print_stats(self):
        print(f"{self.__class__.__name__} Propagator stats")
        for name, time in util.Timer.timers.items():
            print(f"{name:15}:\t{time}")

        print("DONE")