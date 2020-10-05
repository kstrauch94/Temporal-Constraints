import clingo

from typing import Any, Dict
from untimed.propagator.propagatorhandler import TheoryHandler
import untimed.util as util

import textwrap as _textwrap

import logging
import sys

propagators = ["naive", "2watch"]

class Application:

	def __init__(self):
		self.version = "0.1"

		self.__handler = None

		self.__handler_type = TheoryHandler

		self.propagator = "2watch"

	def __on_stats(self, step, accu):
		util.print_stats()

	def __parse_propagator(self, prop):
		if prop not in propagators:
			return False

		self.propagator = prop
		return True

	def register_options(self, options):
		"""
		See clingo.clingo_main().
		"""

		group = "Untimed Options"

		options.add(group, "propagator", _textwrap.dedent("""Propagator type to use [2watch]
				<arg>: {2watch|naive}"""), self.__parse_propagator)

	def __build_handler(self):

		self.__handler = self.__handler_type(self.propagator)

	def main(self, prg, files):

		for name in files:
			prg.load(name)

		self.__build_handler()

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
