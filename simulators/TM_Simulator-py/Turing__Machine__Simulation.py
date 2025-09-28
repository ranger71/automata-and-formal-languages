import sys
from typing import Callable, Any, TypeVar, NamedTuple
from math import floor
from itertools import count

import module_ as module_
import _dafny as _dafny
import System_ as System_
import FormalLanguages as FormalLanguages

# Module: Turing__Machine__Simulation

class default__:
    def  __init__(self):
        pass

    @staticmethod
    def TM__K(M):
        return (M)[0]

    @staticmethod
    def TM__Sigma(M):
        return (M)[1]

    @staticmethod
    def TM__Gamma(M):
        return (M)[2]

    @staticmethod
    def TM__Delta(M):
        return (M)[3]

    @staticmethod
    def TM__s(M):
        return (M)[4]

    @staticmethod
    def TM__H(M):
        return (M)[5]

    @staticmethod
    def NoLeadingBlanks(str):
        return ((len(str)) == (0)) or (((str)[0]) != (default__.BLANK__SQUARE))

    @staticmethod
    def NoTrailingBlanks(str):
        return ((len(str)) == (0)) or (((str)[(len(str)) - (1)]) != (default__.BLANK__SQUARE))

    @staticmethod
    def Halting__TM__Configuration(C, M):
        return ((C)[0]) in (default__.TM__H(M))

    @staticmethod
    def delta__9(k, c):
        if (k) == (1):
            if (c) == (default__.BLANK__SQUARE):
                return (2, c, Direction_Right())
            elif True:
                return (7, c, Direction_Right())
        elif (k) == (2):
            if (c) == (_dafny.CodePoint('a')):
                return (3, _dafny.CodePoint('$'), Direction_Right())
            elif (c) == (default__.BLANK__SQUARE):
                return (6, c, Direction_Left())
            elif True:
                return (7, c, Direction_Right())
        elif (k) == (3):
            if (((c) == (_dafny.CodePoint('a'))) or ((c) == (_dafny.CodePoint('$')))) or ((c) == (_dafny.CodePoint('#'))):
                return (3, c, Direction_Right())
            elif ((c) == (_dafny.CodePoint('b'))) or ((c) == (default__.BLANK__SQUARE)):
                return (4, _dafny.CodePoint('#'), Direction_Left())
            elif True:
                return (7, c, Direction_Right())
        elif (k) == (4):
            if (c) == (_dafny.CodePoint('a')):
                return (3, _dafny.CodePoint('$'), Direction_Right())
            elif ((c) == (_dafny.CodePoint('$'))) or ((c) == (_dafny.CodePoint('#'))):
                return (4, c, Direction_Left())
            elif (c) == (default__.BLANK__SQUARE):
                return (5, c, Direction_Right())
            elif True:
                return (7, c, Direction_Right())
        elif True:
            if (c) == (_dafny.CodePoint('$')):
                return (5, _dafny.CodePoint('a'), Direction_Right())
            elif (c) == (_dafny.CodePoint('#')):
                return (5, _dafny.CodePoint('b'), Direction_Right())
            elif (c) == (default__.BLANK__SQUARE):
                return (6, c, Direction_Left())
            elif True:
                return (7, c, Direction_Right())

    @staticmethod
    def tmsimulate(M, w):
        output: tuple = (int(0), _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "")), _dafny.CodePoint('D'), _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "")))
        steps: int = int(0)
        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Run a TM on input string "))).VerbatimString(False))
        _dafny.print((w).VerbatimString(False))
        steps = 0
        d_0_st_: int
        d_0_st_ = default__.TM__s(M)
        d_1_tape__left_: _dafny.Seq
        d_2_c_: str
        d_3_tape__right_: _dafny.Seq
        rhs0_ = _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ""))
        rhs1_ = default__.BLANK__SQUARE
        rhs2_ = w
        d_1_tape__left_ = rhs0_
        d_2_c_ = rhs1_
        d_3_tape__right_ = rhs2_
        d_4_blanks_: _dafny.Seq
        d_4_blanks_ = _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ""))
        while not(default__.Halting__TM__Configuration((d_0_st_, d_1_tape__left_, d_2_c_, d_3_tape__right_), M)):
            _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\n "))).VerbatimString(False))
            _dafny.print((((d_1_tape__left_) + (_dafny.SeqWithoutIsStrInference([d_2_c_]))) + (d_3_tape__right_)).VerbatimString(False))
            _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\t\tConfiguration #"))).VerbatimString(False))
            _dafny.print(_dafny.string_of(steps))
            _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ": <"))).VerbatimString(False))
            _dafny.print(_dafny.string_of((d_0_st_, d_1_tape__left_, d_2_c_, d_3_tape__right_)))
            _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ">"))).VerbatimString(False))
            d_5_action_: tuple
            d_5_action_ = default__.TM__Delta(M)(d_0_st_, d_2_c_)
            d_0_st_ = (d_5_action_)[0]
            d_6_tape_: _dafny.Seq
            d_6_tape_ = ((d_1_tape__left_) + (_dafny.SeqWithoutIsStrInference([(d_5_action_)[1]]))) + (d_3_tape__right_)
            d_7_c__index_: int
            if ((d_5_action_)[2]) == (Direction_Left()):
                d_7_c__index_ = (len(d_1_tape__left_)) - (1)
            elif True:
                d_7_c__index_ = (len(d_1_tape__left_)) + (1)
            if (d_7_c__index_) < (0):
                rhs3_ = _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ""))
                rhs4_ = default__.BLANK__SQUARE
                rhs5_ = d_6_tape_
                d_1_tape__left_ = rhs3_
                d_2_c_ = rhs4_
                d_3_tape__right_ = rhs5_
            elif (d_7_c__index_) >= (len(d_6_tape_)):
                rhs6_ = d_6_tape_
                rhs7_ = default__.BLANK__SQUARE
                rhs8_ = _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ""))
                d_1_tape__left_ = rhs6_
                d_2_c_ = rhs7_
                d_3_tape__right_ = rhs8_
            elif True:
                rhs9_ = _dafny.SeqWithoutIsStrInference((d_6_tape_)[:d_7_c__index_:])
                rhs10_ = (d_6_tape_)[d_7_c__index_]
                rhs11_ = _dafny.SeqWithoutIsStrInference((d_6_tape_)[(d_7_c__index_) + (1)::])
                d_1_tape__left_ = rhs9_
                d_2_c_ = rhs10_
                d_3_tape__right_ = rhs11_
            if ((len(d_1_tape__left_)) == (1)) and ((d_1_tape__left_) == (_dafny.SeqWithoutIsStrInference([default__.BLANK__SQUARE]))):
                d_1_tape__left_ = _dafny.SeqWithoutIsStrInference([])
            if ((len(d_3_tape__right_)) == (1)) and ((d_3_tape__right_) == (_dafny.SeqWithoutIsStrInference([default__.BLANK__SQUARE]))):
                d_3_tape__right_ = _dafny.SeqWithoutIsStrInference([])
            steps = (steps) + (1)
        output = (d_0_st_, d_1_tape__left_, d_2_c_, d_3_tape__right_)
        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\n "))).VerbatimString(False))
        _dafny.print(((((output)[1]) + (_dafny.SeqWithoutIsStrInference([(output)[2]]))) + ((output)[3])).VerbatimString(False))
        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\t\tConfiguration #"))).VerbatimString(False))
        _dafny.print(_dafny.string_of(steps))
        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ": <"))).VerbatimString(False))
        _dafny.print(_dafny.string_of(output))
        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ">"))).VerbatimString(False))
        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\nTM halts after "))).VerbatimString(False))
        _dafny.print(_dafny.string_of(steps))
        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " steps."))).VerbatimString(False))
        return output, steps

    @staticmethod
    def Main(noArgsParameter__):
        d_0_output_: tuple
        d_1_steps_: int
        out0_: tuple
        out1_: int
        out0_, out1_ = default__.tmsimulate(default__.M__9, _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "aaab")))
        d_0_output_ = out0_
        d_1_steps_ = out1_

    @_dafny.classproperty
    def BLANK__SQUARE(instance):
        return _dafny.CodePoint(' ')
    @_dafny.classproperty
    def Sigma__9(instance):
        return _dafny.Set({_dafny.CodePoint('a'), _dafny.CodePoint('b')})
    @_dafny.classproperty
    def Gamma__9(instance):
        return (default__.Sigma__9) | (_dafny.Set({default__.BLANK__SQUARE, _dafny.CodePoint('$'), _dafny.CodePoint('#')}))
    @_dafny.classproperty
    def K__9(instance):
        return _dafny.Set({1, 2, 3, 4, 5, 6, 7})
    @_dafny.classproperty
    def H__9(instance):
        return _dafny.Set({6, 7})
    @_dafny.classproperty
    def s__9(instance):
        return 1
    @_dafny.classproperty
    def M__9(instance):
        return (default__.K__9, default__.Sigma__9, default__.Gamma__9, default__.delta__9, default__.s__9, default__.H__9)

class Direction:
    @_dafny.classproperty
    def AllSingletonConstructors(cls):
        return [Direction_Left(), Direction_Right()]
    @classmethod
    def default(cls, ):
        return lambda: Direction_Left()
    def __ne__(self, __o: object) -> bool:
        return not self.__eq__(__o)
    @property
    def is_Left(self) -> bool:
        return isinstance(self, Direction_Left)
    @property
    def is_Right(self) -> bool:
        return isinstance(self, Direction_Right)

class Direction_Left(Direction, NamedTuple('Left', [])):
    def __dafnystr__(self) -> str:
        return f'Turing_Machine_Simulation.Direction.Left'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, Direction_Left)
    def __hash__(self) -> int:
        return super().__hash__()

class Direction_Right(Direction, NamedTuple('Right', [])):
    def __dafnystr__(self) -> str:
        return f'Turing_Machine_Simulation.Direction.Right'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, Direction_Right)
    def __hash__(self) -> int:
        return super().__hash__()

