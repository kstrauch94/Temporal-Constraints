import time
import functools
from typing import Dict
from collections import defaultdict

from typing import Any


class TimerError(Exception):
    pass

class Timer:

    timers : Dict[str, float] = defaultdict(lambda : 0)

    def __init__(self, name : str):
        self.name = name

        self._time_start = None

    def start(self) -> None:

        if self._time_start is not None:
            raise TimerError("Timer started twice without stopping")

        self._time_start = time.perf_counter()

    def stop(self) -> float:

        if self._time_start is None:
            raise TimerError("Timer stopped without starting")

        stop = time.perf_counter() - self._time_start
        self._time_start = None

        Timer.timers[self.name] += stop

        return stop

    def __enter__(self) -> "Timer":
        self.start()

        return self

    def __exit__(self, *exc_info: Any) -> None:
        self.stop()

    def __call__(self, func) -> "Timer":
    
        @functools.wraps(func)
        def wrapper_timer(*args, **kwargs):
            with self:
                return func(*args, **kwargs)

        return wrapper_timer
