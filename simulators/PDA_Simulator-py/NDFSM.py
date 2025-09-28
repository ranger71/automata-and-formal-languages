import sys
from typing import Callable, Any, TypeVar, NamedTuple
from math import floor
from itertools import count

import module_ as module_
import _dafny as _dafny
import System_ as System_
import FormalLanguages as FormalLanguages
import PDA__Simulation as PDA__Simulation
import DFSM as DFSM

# Module: NDFSM

class default__:
    def  __init__(self):
        pass

    @staticmethod
    def ND__K(M):
        return (M)[0]

    @staticmethod
    def ND__Sigma(M):
        return (M)[1]

    @staticmethod
    def ND__Delta(M):
        return (M)[2]

    @staticmethod
    def ND__s(M):
        return (M)[3]

    @staticmethod
    def ND__A(M):
        return (M)[4]

    @staticmethod
    def eps(q, M):
        return default__.eps__recursive(_dafny.Set({q}), M)

    @staticmethod
    def eps__successors(states, M):
        def iife0_():
            def lambda0_(exists_var_0_):
                d_1_p_: int = exists_var_0_
                return ((d_1_p_) in (states)) and (((d_1_p_, MaybeSymbol_epsilon(), d_0_r_)) in (default__.ND__Delta(M)))

            coll0_ = _dafny.Set()
            compr_0_: int
            for compr_0_ in (default__.ND__K(M)).Elements:
                d_0_r_: int = compr_0_
                if System_.nat._Is(d_0_r_):
                    if ((d_0_r_) in (default__.ND__K(M))) and (_dafny.quantifier((states).Elements, False, lambda0_)):
                        coll0_ = coll0_.union(_dafny.Set([d_0_r_]))
            return _dafny.Set(coll0_)
        return iife0_()
        

    @staticmethod
    def eps__recursive(states, M):
        while True:
            with _dafny.label():
                d_0_eps__successor__states_ = default__.eps__successors(states, M)
                if (d_0_eps__successor__states_).issubset(states):
                    return states
                elif True:
                    in0_ = (states) | (d_0_eps__successor__states_)
                    in1_ = M
                    states = in0_
                    M = in1_
                    raise _dafny.TailCall()
                break


class MaybeSymbol:
    @classmethod
    def default(cls, ):
        return lambda: MaybeSymbol_epsilon()
    def __ne__(self, __o: object) -> bool:
        return not self.__eq__(__o)
    @property
    def is_epsilon(self) -> bool:
        return isinstance(self, MaybeSymbol_epsilon)
    @property
    def is_sym(self) -> bool:
        return isinstance(self, MaybeSymbol_sym)

class MaybeSymbol_epsilon(MaybeSymbol, NamedTuple('epsilon', [])):
    def __dafnystr__(self) -> str:
        return f'NDFSM.MaybeSymbol.epsilon'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, MaybeSymbol_epsilon)
    def __hash__(self) -> int:
        return super().__hash__()

class MaybeSymbol_sym(MaybeSymbol, NamedTuple('sym', [('h0_', Any)])):
    def __dafnystr__(self) -> str:
        return f'NDFSM.MaybeSymbol.sym({_dafny.string_of(self.h0_)})'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, MaybeSymbol_sym) and self.h0_ == __o.h0_
    def __hash__(self) -> int:
        return super().__hash__()

