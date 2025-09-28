import sys
from typing import Callable, Any, TypeVar, NamedTuple
from math import floor
from itertools import count

import module_ as module_
import _dafny as _dafny
import System_ as System_
import FormalLanguages as FormalLanguages

# Module: PDA__Simulation

class default__:
    def  __init__(self):
        pass

    @staticmethod
    def PDA__K(M):
        return (M)[0]

    @staticmethod
    def PDA__Sigma(M):
        return (M)[1]

    @staticmethod
    def PDA__Gamma(M):
        return (M)[2]

    @staticmethod
    def PDA__Delta(M):
        return (M)[3]

    @staticmethod
    def PDA__s(M):
        return (M)[4]

    @staticmethod
    def PDA__A(M):
        return (M)[5]

    @staticmethod
    def Accepting__PDA__Configuration(C, M):
        return ((((C)[0]) in (default__.PDA__A(M))) and (((C)[1]) == (FormalLanguages.default__.EPSILON))) and (((C)[2]) == (FormalLanguages.default__.EPSILON))

    @staticmethod
    def PrintPDA(M):
        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\n(K = "))).VerbatimString(False))
        _dafny.print(_dafny.string_of(default__.PDA__K(M)))
        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ", Sigma = "))).VerbatimString(False))
        _dafny.print((default__.PDA__Sigma(M)).VerbatimString(False))
        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ", Gamma = "))).VerbatimString(False))
        _dafny.print((default__.PDA__Gamma(M)).VerbatimString(False))
        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ", DELTA = "))).VerbatimString(False))
        _dafny.print(_dafny.string_of(default__.PDA__Delta(M)))
        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ", s = "))).VerbatimString(False))
        _dafny.print(_dafny.string_of(default__.PDA__s(M)))
        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ", A = "))).VerbatimString(False))
        _dafny.print(_dafny.string_of(default__.PDA__A(M)))
        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ")"))).VerbatimString(False))

    @staticmethod
    def pdasimulate(M, w):
        accepted: bool = False
        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\nRun the PDA "))).VerbatimString(False))
        default__.PrintPDA(M)
        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\non input string \""))).VerbatimString(False))
        _dafny.print((w).VerbatimString(False))
        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\""))).VerbatimString(False))
        d_0_initial__configuration_: tuple
        d_0_initial__configuration_ = (default__.PDA__s(M), w, FormalLanguages.default__.EPSILON)
        d_1_previous__configurations_: _dafny.Seq
        d_1_previous__configurations_ = _dafny.SeqWithoutIsStrInference([])
        out0_: bool
        out0_ = default__.pdasimulate__recursive(M, d_0_initial__configuration_, d_1_previous__configurations_, 0)
        accepted = out0_
        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\nThe input string \""))).VerbatimString(False))
        _dafny.print((w).VerbatimString(False))
        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\" is "))).VerbatimString(False))
        if not(accepted):
            _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "NOT "))).VerbatimString(False))
        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "in the language accepted by this PDA.\n"))).VerbatimString(False))
        return accepted

    @staticmethod
    def Print__PDA__Configuration(C, steps):
        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\nConfiguration #"))).VerbatimString(False))
        _dafny.print(_dafny.string_of(steps))
        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ": <(state="))).VerbatimString(False))
        _dafny.print(_dafny.string_of((C)[0]))
        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ", suffix=\""))).VerbatimString(False))
        _dafny.print(((C)[1]).VerbatimString(False))
        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\", stack=\""))).VerbatimString(False))
        _dafny.print(((C)[2]).VerbatimString(False))
        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\")>"))).VerbatimString(False))

    @staticmethod
    def pdasimulate__recursive(M, C, previous__configurations, steps):
        accepted: bool = False
        default__.Print__PDA__Configuration(C, steps)
        if default__.Accepting__PDA__Configuration(C, M):
            _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\nThis configuration is accepting!"))).VerbatimString(False))
            accepted = True
        elif (C) in (previous__configurations):
            _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " This configuration is not new. Backtracking."))).VerbatimString(False))
            accepted = False
        elif True:
            d_0_next__configurations_: _dafny.Seq
            out0_: _dafny.Seq
            out0_ = default__.pdasimulate__one__step(M, C)
            d_0_next__configurations_ = out0_
            if (len(d_0_next__configurations_)) == (0):
                _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\n"))).VerbatimString(False))
                _dafny.print((((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "At the end of the input string reached a non-accepting state.")) if ((C)[0]) not in (default__.PDA__A(M)) else _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "At the end of the input string the stack is not empty."))) if (len((C)[1])) == (0) else _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Stuck with no potential transitions.")))).VerbatimString(False))
                _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " Backtracking."))).VerbatimString(False))
                accepted = False
            elif (len(d_0_next__configurations_)) == (1):
                out1_: bool
                out1_ = default__.pdasimulate__recursive(M, (d_0_next__configurations_)[0], (previous__configurations) + (_dafny.SeqWithoutIsStrInference([C])), (steps) + (1))
                accepted = out1_
            elif True:
                _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\nFound "))).VerbatimString(False))
                _dafny.print(_dafny.string_of(len(d_0_next__configurations_)))
                _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " next configurations. Trying each of them in order."))).VerbatimString(False))
                d_1_i_: int
                d_1_i_ = 0
                accepted = False
                while ((d_1_i_) != (len(d_0_next__configurations_))) and (not(accepted)):
                    out2_: bool
                    out2_ = default__.pdasimulate__recursive(M, (d_0_next__configurations_)[d_1_i_], (previous__configurations) + (_dafny.SeqWithoutIsStrInference([C])), (steps) + (1))
                    accepted = out2_
                    d_1_i_ = (d_1_i_) + (1)
        return accepted

    @staticmethod
    def pdasimulate__one__step(M, C):
        next__configurations: _dafny.Seq = _dafny.Seq({})
        d_0_current__state_: int
        d_1_suffix_: _dafny.Seq
        d_2_current__stack_: _dafny.Seq
        rhs0_ = (C)[0]
        rhs1_ = (C)[1]
        rhs2_ = (C)[2]
        d_0_current__state_ = rhs0_
        d_1_suffix_ = rhs1_
        d_2_current__stack_ = rhs2_
        d_3_all__transitions_: _dafny.Seq
        d_3_all__transitions_ = default__.PDA__Delta(M)
        next__configurations = _dafny.SeqWithoutIsStrInference([])
        d_4_i_: int
        d_4_i_ = 0
        while (d_4_i_) != (len(d_3_all__transitions_)):
            d_5_T_: tuple
            d_5_T_ = (d_3_all__transitions_)[d_4_i_]
            d_6_from__state_: int
            d_7_with_: MaybeSymbol
            d_8_pop__str_: _dafny.Seq
            d_9_to__state_: int
            d_10_push__str_: _dafny.Seq
            rhs3_ = ((d_5_T_)[0])[0]
            rhs4_ = ((d_5_T_)[0])[1]
            rhs5_ = ((d_5_T_)[0])[2]
            rhs6_ = ((d_5_T_)[1])[0]
            rhs7_ = ((d_5_T_)[1])[1]
            d_6_from__state_ = rhs3_
            d_7_with_ = rhs4_
            d_8_pop__str_ = rhs5_
            d_9_to__state_ = rhs6_
            d_10_push__str_ = rhs7_
            if (((d_6_from__state_) == (d_0_current__state_)) and (((d_7_with_) == (MaybeSymbol_epsilon())) or (((d_1_suffix_) != (_dafny.SeqWithoutIsStrInference([]))) and ((d_7_with_) == (MaybeSymbol_sym((d_1_suffix_)[0])))))) and ((d_8_pop__str_) <= (d_2_current__stack_)):
                if (d_7_with_) == (MaybeSymbol_epsilon()):
                    next__configurations = (next__configurations) + (_dafny.SeqWithoutIsStrInference([(d_9_to__state_, d_1_suffix_, (d_10_push__str_) + (_dafny.SeqWithoutIsStrInference((d_2_current__stack_)[len(d_8_pop__str_)::])))]))
                if ((d_1_suffix_) != (_dafny.SeqWithoutIsStrInference([]))) and ((d_7_with_) == (MaybeSymbol_sym((d_1_suffix_)[0]))):
                    next__configurations = (next__configurations) + (_dafny.SeqWithoutIsStrInference([(d_9_to__state_, _dafny.SeqWithoutIsStrInference((d_1_suffix_)[1::]), (d_10_push__str_) + (_dafny.SeqWithoutIsStrInference((d_2_current__stack_)[len(d_8_pop__str_)::])))]))
            d_4_i_ = (d_4_i_) + (1)
        return next__configurations

    @staticmethod
    def Main_k():
        d_0_accepted_: bool
        out0_: bool
        out0_ = default__.pdasimulate(default__.M__AnBn, _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "")))
        d_0_accepted_ = out0_
        out1_: bool
        out1_ = default__.pdasimulate(default__.M__AnBn, _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "aaab")))
        d_0_accepted_ = out1_
        out2_: bool
        out2_ = default__.pdasimulate(default__.M__AnBn, _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "aaabbb")))
        d_0_accepted_ = out2_
        out3_: bool
        out3_ = default__.pdasimulate(default__.M__AnBn_k, _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "")))
        d_0_accepted_ = out3_
        out4_: bool
        out4_ = default__.pdasimulate(default__.M__AnBn_k, _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "aaab")))
        d_0_accepted_ = out4_
        out5_: bool
        out5_ = default__.pdasimulate(default__.M__AnBn_k, _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "aaabbb")))
        d_0_accepted_ = out5_

    @_dafny.classproperty
    def DELTA__AnBn(instance):
        return _dafny.SeqWithoutIsStrInference([((1, MaybeSymbol_sym(_dafny.CodePoint('a')), FormalLanguages.default__.EPSILON), (1, _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "a")))), ((1, MaybeSymbol_sym(_dafny.CodePoint('b')), _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "a"))), (2, FormalLanguages.default__.EPSILON)), ((2, MaybeSymbol_sym(_dafny.CodePoint('b')), _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "a"))), (2, FormalLanguages.default__.EPSILON))])
    @_dafny.classproperty
    def s__AnBn(instance):
        return 1
    @_dafny.classproperty
    def A__AnBn(instance):
        return _dafny.SeqWithoutIsStrInference([1, 2])
    @_dafny.classproperty
    def K__AnBn(instance):
        return _dafny.SeqWithoutIsStrInference([1, 2])
    @_dafny.classproperty
    def Sigma__AnBn(instance):
        return _dafny.SeqWithoutIsStrInference([_dafny.CodePoint('a'), _dafny.CodePoint('b')])
    @_dafny.classproperty
    def Gamma__AnBn(instance):
        return _dafny.SeqWithoutIsStrInference([_dafny.CodePoint('a')])
    @_dafny.classproperty
    def M__AnBn(instance):
        return (default__.K__AnBn, default__.Sigma__AnBn, default__.Gamma__AnBn, default__.DELTA__AnBn, default__.s__AnBn, default__.A__AnBn)
    @_dafny.classproperty
    def DELTA__AnBn_k(instance):
        return _dafny.SeqWithoutIsStrInference([((1, MaybeSymbol_sym(_dafny.CodePoint('a')), FormalLanguages.default__.EPSILON), (1, _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "a")))), ((1, MaybeSymbol_epsilon(), FormalLanguages.default__.EPSILON), (2, FormalLanguages.default__.EPSILON)), ((2, MaybeSymbol_sym(_dafny.CodePoint('b')), _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "a"))), (2, FormalLanguages.default__.EPSILON))])
    @_dafny.classproperty
    def A__AnBn_k(instance):
        return _dafny.SeqWithoutIsStrInference([2])
    @_dafny.classproperty
    def M__AnBn_k(instance):
        return (default__.K__AnBn, default__.Sigma__AnBn, default__.Gamma__AnBn, default__.DELTA__AnBn_k, default__.s__AnBn, default__.A__AnBn_k)

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
        return f'PDA_Simulation.MaybeSymbol.epsilon'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, MaybeSymbol_epsilon)
    def __hash__(self) -> int:
        return super().__hash__()

class MaybeSymbol_sym(MaybeSymbol, NamedTuple('sym', [('h0_', Any)])):
    def __dafnystr__(self) -> str:
        return f'PDA_Simulation.MaybeSymbol.sym({_dafny.string_of(self.h0_)})'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, MaybeSymbol_sym) and self.h0_ == __o.h0_
    def __hash__(self) -> int:
        return super().__hash__()

