import sys
from typing import Callable, Any, TypeVar, NamedTuple
from math import floor
from itertools import count

import module_ as module_
import _dafny as _dafny
import System_ as System_
import FormalLanguages as FormalLanguages
import PDA__Simulation as PDA__Simulation

# Module: DFSM

class default__:
    def  __init__(self):
        pass

    @staticmethod
    def K(M):
        return (M)[0]

    @staticmethod
    def Sigma(M):
        return (M)[1]

    @staticmethod
    def Delta(M):
        return (M)[2]

    @staticmethod
    def s(M):
        return (M)[3]

    @staticmethod
    def A(M):
        return (M)[4]


class RegularLanguage:
    def  __init__(self):
        pass

    @staticmethod
    def default():
        return _dafny.Set({})
