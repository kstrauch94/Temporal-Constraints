import clingo
import propagator.untimed_propagator

import logging
import sys

class Application:

    def __init__(self, name):
        self.program_name = name
        self.version = "0.1"
        
        self.__propagator = untimed_propagator.ConstraintPropagator()
   

    def __on_stats(self, step, accu):
        self.__propagator.print_stats()

    def main(self, prg, files):

        prg.register_propagator(self.__propagator)
        prg.load(untimed_propagator.THEORY)

        for name in files:
            prg.load(name)

        prg.ground([("base", [])])

        prg.solve(on_statistics=self.__on_stats)



def setup_logger():

    root_logger = logging.getLogger()
    root_logger.setLevel(logging.INFO)

    logger_handler = logging.StreamHandler(stream=sys.stdout)

    formatter = logging.Formatter("%(levelname)s:%(name)s:\t%(message)s")

    logger_handler.setFormatter(formatter)

    root_logger.addHandler(logger_handler)

if __name__ == "__main__":
    setup_logger()
    sys.exit(int(clingo.clingo_main(Application("test"), sys.argv[1:])))
