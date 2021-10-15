import clingo

from untimed.propagator.propagatorhandler import TheoryHandler, PROPAGATORS

from untimed.propagator.propagatorhandler import add_theory

from untimed.propagator.theoryconstraint_data import GlobalConfig, StatNames

import untimed.util as util

import textwrap as _textwrap

import logging
import sys

watch_types = PROPAGATORS.keys()

class Application:

	def __init__(self):
		self.version = "1.0"

		self.__handler = None

		self.watch_type = "timed"
		self.lock_ng = -1
		self.use_ids = clingo.Flag(False)

	def __on_stats(self, step, accu):
		util.print_stats(step, accu)

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

	def __parse_ground_up_to(self, time):
		time = int(time)

		if time < 0:
			return False

		GlobalConfig.lock_up_to = time
		return True

	def __parse_ground_from(self, time):
		time = int(time)

		if time < 0:
			return False

		GlobalConfig.lock_from = time
		return True

	def register_options(self, options):
		"""
		See clingo.clingo_main().
		"""

		group = "Untimed Options"

		options.add(group, "watch-type", _textwrap.dedent("""Watch type to use [timed]"""), self.__parse_watch_type)

		options.add(group, "lock-ng", _textwrap.dedent("""Lock the nogood if it is found to be unit or conflicting after [-1]
		        <n> times it was added. -1 means it will never be locked. This option does not work with time_aw watch type"""),
		            self.__parse_lock_ng)

		options.add(group, "ground-up-to", _textwrap.dedent("""Add the nogoods up to the specified time point from the start[0]"""),
		            self.__parse_ground_up_to)

		options.add(group, "ground-from", _textwrap.dedent("""Add the nogoods max - <n> time point to the max timepoint [0]"""),
		            self.__parse_ground_from)

		options.add_flag(group, "use-ids", _textwrap.dedent("""Create a propagator per constraint id"""),
					self.use_ids)

	def main(self, prg, files):
		with util.Timer(StatNames.UNTILSOLVE_TIMER_MSG.value):
			for name in files:
				prg.load(name)

			self.__handler = TheoryHandler(self.watch_type, self.lock_ng, self.use_ids)

			add_theory(prg)

			with util.Timer(StatNames.GROUND_TIMER_MSG.value):
				prg.ground([("base", [])])
			print("clingo grounding done")

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
