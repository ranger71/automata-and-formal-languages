import sys
from typing import Callable, Any, TypeVar, NamedTuple
from math import floor
from itertools import count

import module_ as module_
import _dafny as _dafny
import System_ as System_

# Module: FormalLanguages

class default__:
    def  __init__(self):
        pass

    @staticmethod
    def Length(s):
        return len(s)

    @staticmethod
    def Count(c, s):
        d_0___accumulator_ = 0
        while True:
            with _dafny.label():
                if (len(s)) == (0):
                    return (0) + (d_0___accumulator_)
                elif ((s)[0]) == (c):
                    d_0___accumulator_ = (d_0___accumulator_) + (1)
                    in0_ = c
                    in1_ = _dafny.SeqWithoutIsStrInference((s)[1::])
                    c = in0_
                    s = in1_
                    raise _dafny.TailCall()
                elif True:
                    in2_ = c
                    in3_ = _dafny.SeqWithoutIsStrInference((s)[1::])
                    c = in2_
                    s = in3_
                    raise _dafny.TailCall()
                break

    @staticmethod
    def Concat(x, y):
        return (x) + (y)

    @staticmethod
    def Rep(w, i):
        if (i) == (0):
            return default__.EPSILON
        elif True:
            return default__.Concat(default__.Rep(w, (i) - (1)), w)

    @staticmethod
    def Reverse(w):
        if (len(w)) == (0):
            return default__.EPSILON
        elif True:
            d_0_u_ = _dafny.SeqWithoutIsStrInference((w)[:(len(w)) - (1):])
            d_1_a_ = (w)[(len(w)) - (1)]
            return default__.Concat(_dafny.SeqWithoutIsStrInference([d_1_a_]), default__.Reverse(d_0_u_))

    @_dafny.classproperty
    def EPSILON(instance):
        return _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ""))
    @_dafny.classproperty
    def Alphabet__a__b(instance):
        return _dafny.Set({_dafny.CodePoint('a'), _dafny.CodePoint('b')})
    @_dafny.classproperty
    def EMPTY__LANGUAGE(instance):
        return _dafny.Set({})
