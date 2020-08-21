import clingo
from untimed.propagator.propagatorhandler import TheoryHandler
from untimed.propagator.propagatorhandler import TheoryHandlerMany

import logging
import sys

class Application:

	def __init__(self):
		self.version = "0.1"
		
		self.__handler = TheoryHandlerMany("2watch")
   
	def __on_stats(self, step, accu):
		self.__handler.on_stats()

	def main(self, prg, files):

		for name in files:
			prg.load(name)

		self.__handler.add_theory(prg)

		prg.ground([("base", [])])

		self.__handler.register(prg)

		prg.solve(on_statistics=self.__on_stats)

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