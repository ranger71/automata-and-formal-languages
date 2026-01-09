import sys
from typing import Callable, Any, TypeVar, NamedTuple
from math import floor
from itertools import count

import module_ as module_
import _dafny as _dafny
import System_ as System_
import FormalLanguages as FormalLanguages
import DFSM as DFSM
import NDFSM as NDFSM

# Module: FSM__SIMULATION

class default__:
    def  __init__(self):
        pass

    @staticmethod
    def dfsmsimulate(M, w):
        accepted: bool = False
        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Run a DFSM on input string "))).VerbatimString(False))
        _dafny.print((w).VerbatimString(False))
        d_0_st_: int
        d_0_st_ = DFSM.default__.s(M)
        d_1_i_: int
        d_1_i_ = 0
        d_2_blanks_: _dafny.Seq
        d_2_blanks_ = _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ""))
        while (d_1_i_) < (len(w)):
            _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\nConfiguration #"))).VerbatimString(False))
            _dafny.print(_dafny.string_of(d_1_i_))
            _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ": <"))).VerbatimString(False))
            _dafny.print((d_2_blanks_).VerbatimString(False))
            _dafny.print((_dafny.SeqWithoutIsStrInference((w)[d_1_i_::])).VerbatimString(False))
            _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ", "))).VerbatimString(False))
            _dafny.print(_dafny.string_of(d_0_st_))
            _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ">"))).VerbatimString(False))
            d_3_c_: str
            d_3_c_ = (w)[d_1_i_]
            d_0_st_ = DFSM.default__.Delta(M)(d_0_st_, d_3_c_)
            d_2_blanks_ = (d_2_blanks_) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " ")))
            d_1_i_ = (d_1_i_) + (1)
        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\nConfiguration #"))).VerbatimString(False))
        _dafny.print(_dafny.string_of(d_1_i_))
        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ": <"))).VerbatimString(False))
        _dafny.print((d_2_blanks_).VerbatimString(False))
        _dafny.print((_dafny.SeqWithoutIsStrInference((w)[d_1_i_::])).VerbatimString(False))
        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ", "))).VerbatimString(False))
        _dafny.print(_dafny.string_of(d_0_st_))
        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ">"))).VerbatimString(False))
        accepted = (d_0_st_) in (DFSM.default__.A(M))
        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\nResult: "))).VerbatimString(False))
        _dafny.print(((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Accepted")) if accepted else _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Rejected")))).VerbatimString(False))
        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\n"))).VerbatimString(False))
        return accepted

    @staticmethod
    def ndfsmsimulate(M, w):
        accepted: bool = False
        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Run an NDFSM on input string "))).VerbatimString(False))
        _dafny.print((w).VerbatimString(False))
        d_0_current__state_: _dafny.Set
        d_0_current__state_ = NDFSM.default__.eps(NDFSM.default__.ND__s(M), M)
        d_1_i_: int
        d_1_i_ = 0
        d_2_blanks_: _dafny.Seq
        d_2_blanks_ = _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ""))
        while ((d_1_i_) < (len(w))) and ((d_0_current__state_) != (_dafny.Set({}))):
            _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\n<"))).VerbatimString(False))
            _dafny.print((d_2_blanks_).VerbatimString(False))
            _dafny.print((_dafny.SeqWithoutIsStrInference((w)[d_1_i_::])).VerbatimString(False))
            _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ", "))).VerbatimString(False))
            _dafny.print(_dafny.string_of(d_0_current__state_))
            _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ">"))).VerbatimString(False))
            d_3_c_: str
            d_3_c_ = (w)[d_1_i_]
            d_4_next__state_: _dafny.Set
            def iife0_():
                coll0_ = _dafny.Set()
                compr_0_: int
                for compr_0_ in (d_0_current__state_).Elements:
                    d_5_q_: int = compr_0_
                    if (d_5_q_) in (d_0_current__state_):
                        compr_1_: int
                        for compr_1_ in (NDFSM.default__.ND__K(M)).Elements:
                            d_6_r_: int = compr_1_
                            if System_.nat._Is(d_6_r_):
                                if ((d_6_r_) in (NDFSM.default__.ND__K(M))) and (((d_5_q_, NDFSM.MaybeSymbol_sym(d_3_c_), d_6_r_)) in (NDFSM.default__.ND__Delta(M))):
                                    compr_2_: int
                                    for compr_2_ in (NDFSM.default__.eps(d_6_r_, M)).Elements:
                                        d_7_r_k_: int = compr_2_
                                        if System_.nat._Is(d_7_r_k_):
                                            if (d_7_r_k_) in (NDFSM.default__.eps(d_6_r_, M)):
                                                coll0_ = coll0_.union(_dafny.Set([d_7_r_k_]))
                return _dafny.Set(coll0_)
            d_4_next__state_ = iife0_()
            
            d_0_current__state_ = d_4_next__state_
            d_2_blanks_ = (d_2_blanks_) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " ")))
            d_1_i_ = (d_1_i_) + (1)
        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\n<"))).VerbatimString(False))
        _dafny.print((d_2_blanks_).VerbatimString(False))
        _dafny.print((_dafny.SeqWithoutIsStrInference((w)[d_1_i_::])).VerbatimString(False))
        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ", "))).VerbatimString(False))
        _dafny.print(_dafny.string_of(d_0_current__state_))
        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ">"))).VerbatimString(False))
        accepted = ((d_0_current__state_).intersection(NDFSM.default__.ND__A(M))) != (_dafny.Set({}))
        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\nResult: "))).VerbatimString(False))
        _dafny.print(((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Accepted")) if accepted else _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Rejected")))).VerbatimString(False))
        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\n"))).VerbatimString(False))
        return accepted

    @staticmethod
    def delta__5__4(k, c):
        if ((k) == (default__.q0)) and ((c) == (_dafny.CodePoint('0'))):
            return default__.q0
        elif ((k) == (default__.q0)) and ((c) == (_dafny.CodePoint('1'))):
            return default__.q1
        elif ((k) == (default__.q1)) and ((c) == (_dafny.CodePoint('0'))):
            return default__.q1
        elif True:
            return default__.q0

    @staticmethod
    def Main(noArgsParameter__):
        d_0_accepted_: bool
        out0_: bool
        out0_ = default__.dfsmsimulate(default__.M__5__4, _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "1001")))
        d_0_accepted_ = out0_
        out1_: bool
        out1_ = default__.dfsmsimulate(default__.M__5__4, _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "10011")))
        d_0_accepted_ = out1_
        out2_: bool
        out2_ = default__.ndfsmsimulate(default__.M__59, _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "")))
        d_0_accepted_ = out2_
        out3_: bool
        out3_ = default__.ndfsmsimulate(default__.M__59, _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "aba")))
        d_0_accepted_ = out3_
        out4_: bool
        out4_ = default__.ndfsmsimulate(default__.M__59, _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "baa")))
        d_0_accepted_ = out4_
        out5_: bool
        out5_ = default__.ndfsmsimulate(default__.M__59, _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "abba")))
        d_0_accepted_ = out5_

    @_dafny.classproperty
    def K__5__4(instance):
        return _dafny.Set({0, 1})
    @_dafny.classproperty
    def Sigma__5__4(instance):
        return _dafny.Set({_dafny.CodePoint('0'), _dafny.CodePoint('1')})
    @_dafny.classproperty
    def q0(instance):
        return 0
    @_dafny.classproperty
    def q1(instance):
        return 1
    @_dafny.classproperty
    def s__5__4(instance):
        return default__.q0
    @_dafny.classproperty
    def A__5__4(instance):
        return _dafny.Set({default__.q1})
    @_dafny.classproperty
    def M__5__4(instance):
        return (default__.K__5__4, default__.Sigma__5__4, default__.delta__5__4, default__.s__5__4, default__.A__5__4)
    @_dafny.classproperty
    def K__59(instance):
        return _dafny.Set({0, 1, 2, 3, 4, 5, 6})
    @_dafny.classproperty
    def sigma__59(instance):
        return _dafny.Set({_dafny.CodePoint('a'), _dafny.CodePoint('b')})
    @_dafny.classproperty
    def DELTA__59(instance):
        return _dafny.Set({(0, NDFSM.MaybeSymbol_epsilon(), 1), (0, NDFSM.MaybeSymbol_epsilon(), 4), (1, NDFSM.MaybeSymbol_sym(_dafny.CodePoint('a')), 1), (1, NDFSM.MaybeSymbol_sym(_dafny.CodePoint('b')), 1), (1, NDFSM.MaybeSymbol_sym(_dafny.CodePoint('a')), 2), (2, NDFSM.MaybeSymbol_sym(_dafny.CodePoint('a')), 3), (3, NDFSM.MaybeSymbol_sym(_dafny.CodePoint('a')), 3), (3, NDFSM.MaybeSymbol_sym(_dafny.CodePoint('b')), 3), (4, NDFSM.MaybeSymbol_sym(_dafny.CodePoint('a')), 4), (4, NDFSM.MaybeSymbol_sym(_dafny.CodePoint('b')), 4), (4, NDFSM.MaybeSymbol_sym(_dafny.CodePoint('b')), 5), (5, NDFSM.MaybeSymbol_sym(_dafny.CodePoint('b')), 6), (6, NDFSM.MaybeSymbol_sym(_dafny.CodePoint('a')), 6), (6, NDFSM.MaybeSymbol_sym(_dafny.CodePoint('b')), 6)})
    @_dafny.classproperty
    def s__59(instance):
        return 0
    @_dafny.classproperty
    def A__59(instance):
        return _dafny.Set({3, 6})
    @_dafny.classproperty
    def M__59(instance):
        return (default__.K__59, default__.sigma__59, default__.DELTA__59, default__.s__59, default__.A__59)
