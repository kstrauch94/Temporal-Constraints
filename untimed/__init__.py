import clingo

from typing import Any, Dict
from untimed.propagator.propagatorhandler import TheoryHandler
from untimed.propagator.propagatorhandler import TheoryHandlerWithPropagator

from untimed.propagator.propagatorhandler import add_theory

import untimed.util as util

import textwrap as _textwrap

import logging
import sys


handlers: Dict[str, Any] = {}
handlers["prop"] = TheoryHandlerWithPropagator
handlers["regular"] = TheoryHandler

watch_types = ["naive", "2watch", "timed", "timed_aw", "2watchmap", "meta", "meta_ta", "count"]


class Application:

	def __init__(self):
		self.version = "0.5"

		self.__handler = None

		self.__handler_type = "prop"

		self.watch_type = "naive"
		self.lock_ng = -1

		self.__prop_init = clingo.Flag(False)

	def __on_stats(self, step, accu):
		util.print_stats()

	def __parse_theory_handler(self, val):
		if val not in handlers:
			return False

		self.__handler_type = val
		return True

	def __parse_watch_type(self, prop):
		if prop not in watch_types:
			return False

		self.watch_type = prop
		return True

	def __parse_lock_ng(self, n):
		n = int(n)
		if n < -1:
			return False

		self.lock_ng = n
		return True

	def register_options(self, options):
		"""
		See clingo.clingo_main().
		"""

		group = "Untimed Options"
		options.add(group, "handler", _textwrap.dedent("""Handler directly adds theory constraints as propagator
				or it creates a propagator that manages all theory constraints [prop]
				<arg>: {regular|prop}"""), self.__parse_theory_handler)
		options.add(group, "watch-type", _textwrap.dedent("""Watch type to use along with the handler. [naive]
				regular handler supports 2watch and naive
				prop handler support timed, naive, 2watch and 2watchmap
				<arg>: {2watch|2watchmap|naive|timed}"""), self.__parse_watch_type)

		options.add(group, "lock-ng", _textwrap.dedent("""Lock the nogood if it is found to be unit or conflicting after [-1]
		        <n> times it was added. -1 means it will never be locked.
		        <n> = [1..max_int] """),
		            self.__parse_lock_ng)

	def __build_handler(self):
		self.__handler = handlers[self.__handler_type](self.watch_type, self.lock_ng)

	def main(self, prg, files):
		with util.Timer("until solve"):
			for name in files:
				prg.load(name)

			self.__build_handler()

			add_theory(prg)

			with util.Timer("ground time"):
				prg.ground([("base", [])])
			print("clingo grounding done")
			self.__handler.register(prg)

		with util.Timer("solve time"):
			prg.solve(on_statistics=self.__on_stats)
		print("done!")
		util.print_stats()

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
