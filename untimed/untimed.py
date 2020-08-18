import clingo
from untimed.propagator.propagatorhandler import TheoryHandler

import logging
import sys


def solve(prg, on_statistics):

    prg.ground([("base", [])])

    prg.solve(on_statistics=on_statistics)

class Application:

    def __init__(self):
        self.version = "0.1"
        
        self.__handler = TheoryHandler("naive")

        self.programs = []
   

    def __on_stats(self, step, accu):
        self.__handler.on_stats()

    def add(self, program):
        """
        Add a program str to the list or programs.
        Every program in the list will be added to clingo in the main
        function
        """
        self.programs.append(program)

    def main(self, prg, files):

        self.__handler.register(prg)

        for name in files:
            prg.load(name)

        solve(prg, on_statistics=self.__on_stats)


def setup_logger():

    root_logger = logging.getLogger()
    root_logger.setLevel(logging.INFO)

    logger_handler = logging.StreamHandler(stream=sys.stdout)

    formatter = logging.Formatter("%(levelname)s:%(name)s:\t%(message)s")

    logger_handler.setFormatter(formatter)

    root_logger.addHandler(logger_handler)


def main():
    setup_logger()
    sys.exit(int(clingo.clingo_main(Application(), sys.argv[1:])))

if __name__ == "__main__":
    main()