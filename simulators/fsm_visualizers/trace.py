from __future__ import annotations

import sys
from pathlib import Path
from typing import Dict, List, Tuple, Set, Any


def _add_generated_dir_to_syspath() -> Path:
    """Add the Dafny-generated Python dir to sys.path and return it."""
    # This file lives in simulators/visualizer; generated dir is ../FSM_Simulators-py
    here = Path(__file__).resolve()
    generated_dir = here.parent.parent / "FSM_Simulators-py"
    if str(generated_dir) not in sys.path:
        sys.path.insert(0, str(generated_dir))
    return generated_dir


_generated_dir = _add_generated_dir_to_syspath()

# Imports rely on sys.path containing the generated directory
import _dafny as _dafny  # type: ignore
import DFSM as DFSM  # type: ignore
import NDFSM as NDFSM  # type: ignore
import FSM__SIMULATION as FSM_SIM  # type: ignore


# ----------------------
# Trace construction API
# ----------------------

class DFSMTraceStep(dict):
    i: int
    prefix: str
    suffix: str
    state: int


class NDFSMTraceStep(dict):
    i: int
    prefix: str
    suffix: str
    states: Set[int]


def _to_codepoint(c: str) -> Any:
    return _dafny.CodePoint(c)


def dfsm_trace(M: Any, input_string: str) -> List[DFSMTraceStep]:
    """Simulate a DFSM and return a step-by-step trace.

    Each step k (0..n) represents the configuration BEFORE consuming symbol k
    (k == len(input_string) is the final configuration).
    """
    steps: List[DFSMTraceStep] = []

    # Initial state
    state = DFSM.default__.s(M)

    # Record initial configuration (before any input consumed)
    steps.append(DFSMTraceStep(i=0, prefix="", suffix=input_string, state=state))

    # Iterate through input
    for i, ch in enumerate(input_string, start=1):
        cp = _to_codepoint(ch)
        state = DFSM.default__.Delta(M)(state, cp)
        steps.append(DFSMTraceStep(i=i, prefix=input_string[:i], suffix=input_string[i:], state=state))

    return steps


def ndfsm_trace(M: Any, input_string: str) -> List[NDFSMTraceStep]:
    """Simulate an NDFSM and return a step-by-step trace of state-sets."""
    steps: List[NDFSMTraceStep] = []

    current_state = NDFSM.default__.eps(NDFSM.default__.ND__s(M), M)
    steps.append(NDFSMTraceStep(i=0, prefix="", suffix=input_string, states=set(current_state.Elements)))

    i = 0
    while i < len(input_string) and current_state != _dafny.Set({}):
        ch = input_string[i]
        cp = _to_codepoint(ch)

        # Compute next-state set with epsilon-closure, mirroring generated code
        coll: Set[int] = set()
        for q in current_state.Elements:
            for r in NDFSM.default__.ND__K(M).Elements:
                if (q, NDFSM.MaybeSymbol_sym(cp), r) in NDFSM.default__.ND__Delta(M):
                    for r_k in NDFSM.default__.eps(r, M).Elements:
                        coll.add(r_k)

        current_state = _dafny.Set(coll)
        i += 1
        steps.append(NDFSMTraceStep(i=i, prefix=input_string[:i], suffix=input_string[i:], states=set(current_state.Elements)))

    return steps


def dfsm_accepts(M: Any, last_state: int) -> bool:
    return last_state in DFSM.default__.A(M)


def ndfsm_accepts(M: Any, last_states: Set[int]) -> bool:
    return _dafny.Set(last_states).intersection(NDFSM.default__.ND__A(M)) != _dafny.Set({})


# ----------------------
# Graph construction API
# ----------------------

def build_dfsm_graph(M: Any) -> Tuple[Set[int], Dict[Tuple[int, int], Set[str]]]:
    """Return nodes and labeled edges for DFSM.

    Edges are mapped (u,v) -> set(labels). Labels are strings; if we cannot
    safely decode symbols, we still build edges with empty labels.
    """
    nodes: Set[int] = set(DFSM.default__.K(M).Elements)
    edges: Dict[Tuple[int, int], Set[str]] = {}

    for q in DFSM.default__.K(M).Elements:
        for sym in DFSM.default__.Sigma(M).Elements:
            try:
                label = _dafny.string_of(sym)
                # _dafny.string_of returns a Dafny Seq; get a Python string best-effort
                if hasattr(label, "VerbatimString"):
                    label_str = label.VerbatimString(False)
                else:
                    label_str = str(label)
            except Exception:
                label_str = ""
            r = DFSM.default__.Delta(M)(q, sym)
            edges.setdefault((q, r), set()).add(label_str)
    return nodes, edges


def build_ndfsm_graph(M: Any) -> Tuple[Set[int], Dict[Tuple[int, int], Set[str]]]:
    nodes: Set[int] = set(NDFSM.default__.ND__K(M).Elements)
    edges: Dict[Tuple[int, int], Set[str]] = {}

    for (p, maybe_sym, r) in NDFSM.default__.ND__Delta(M).Elements:
        if getattr(maybe_sym, "is_epsilon", False):
            label = "ε"
        else:
            try:
                s = _dafny.string_of(maybe_sym.h0_)
                label = s.VerbatimString(False) if hasattr(s, "VerbatimString") else str(s)
            except Exception:
                label = ""
        edges.setdefault((p, r), set()).add(label)
    return nodes, edges


# ----------------------
# Machine access helpers
# ----------------------

def get_dfsm_machine() -> Any:
    # From generated FSM__SIMULATION: DFSM machine named M__16
    return FSM_SIM.default__.M__16


def get_ndfsm_machine() -> Any:
    # From generated FSM__SIMULATION: NDFSM machine named M__59
    return FSM_SIM.default__.M__59



