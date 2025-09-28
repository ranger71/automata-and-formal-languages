from __future__ import annotations

import sys
from pathlib import Path
from typing import Any, Dict, List, Optional, Sequence, Set, Tuple


def _add_generated_dir_to_syspath() -> Path:
    """Add the Dafny-generated Python dir for the PDA to sys.path and return it.

    Expected path: simulators/PDA_Simulator-py relative to this file.
    """
    here = Path(__file__).resolve()
    generated_dir = here.parent.parent / "PDA_Simulator-py"
    if str(generated_dir) not in sys.path:
        sys.path.insert(0, str(generated_dir))
    return generated_dir


_generated_dir = _add_generated_dir_to_syspath()

# Imports rely on sys.path containing the generated directory
import _dafny as _dafny  # type: ignore

# Try both naming schemes that Dafny may emit
PDA_SIM = None  # type: ignore
try:  # pragma: no cover
    import PDA__Simulation as PDA_SIM  # type: ignore
except Exception:
    try:
        import PDA__SIMULATION as PDA_SIM  # type: ignore
    except Exception:
        PDA_SIM = None  # type: ignore


# ----------------------
# Helper conversions
# ----------------------

def _to_py_str(dafny_seq: Any) -> str:
    """Best-effort conversion of Dafny Seq to Python str."""
    try:
        if hasattr(dafny_seq, "VerbatimString"):
            return str(dafny_seq.VerbatimString(False))
        return str(dafny_seq)
    except Exception:
        return str(dafny_seq)


def _epsilon_symbol() -> str:
    return "ε"


# ----------------------
# Machine discovery
# ----------------------

def list_pda_machines() -> Dict[str, Any]:
    """Return mapping of available machine constants from generated module.

    We look for attributes on `PDA_SIM.default__` that look like 6-tuples,
    corresponding to: (K, Sigma, Gamma, Delta, s, A).
    """
    if PDA_SIM is None:
        return {}
    machines: Dict[str, Any] = {}
    default = PDA_SIM.default__
    for name in dir(default):
        if name.startswith("_"):
            continue
        try:
            val = getattr(default, name)
            # Some constants are classproperties. Evaluate if needed.
            if callable(val) and hasattr(val, "fget"):
                val = val.__get__(None, default)  # classproperty access
            # Accept 6-tuple machines
            if isinstance(val, tuple) and len(val) == 6:
                machines[name] = val
        except Exception:
            continue
    return machines


def get_default_machine() -> Tuple[str, Any]:
    machines = list_pda_machines()
    if not machines:
        raise RuntimeError("No PDA machines discovered in generated module.")
    # Prefer a name starting with 'M' if present
    for k in sorted(machines.keys()):
        if k.startswith("M"):
            return k, machines[k]
    # Fallback to first sorted
    k = sorted(machines.keys())[0]
    return k, machines[k]


# ----------------------
# Trace computation (single-path DFS)
# ----------------------

class PDATraceStep(dict):
    i: int
    state: int
    suffix: str
    stack: str


def _pda_parts(M: Any):
    # M = (K, Sigma, Gamma, DELTA, s, A)
    return M[0], M[1], M[2], M[3], M[4], M[5]


def _seq_elements(collection: Any) -> Sequence[Any]:
    # Dafny seq has Elements or is a Python list/tuple
    if hasattr(collection, "Elements"):
        return list(collection.Elements)
    if isinstance(collection, (list, tuple)):
        return list(collection)
    # Dafny Set/Seq wrappers often have an iterator
    try:
        return list(collection)
    except Exception:
        return []


def _stringify_seq_of_codepoints(dafny_seq: Any) -> str:
    try:
        return _to_py_str(dafny_seq)
    except Exception:
        return str(dafny_seq)


def _match_transition(with_symbol: Any, suffix: str) -> Tuple[bool, str]:
    # with_symbol is MaybeSymbol (epsilon or sym(cp))
    if getattr(with_symbol, "is_epsilon", False):
        return True, suffix
    if getattr(with_symbol, "is_sym", False):
        cp = with_symbol.h0_
        ch = _to_py_str(cp)
        if len(suffix) > 0 and suffix[0] == ch:
            return True, suffix[1:]
    return False, suffix


def _prefix_match(stack: str, pop_str: str) -> Optional[str]:
    # Return remainder of stack after popping pop_str from the left (top)
    if pop_str == "":
        return stack
    if stack.startswith(pop_str):
        return stack[len(pop_str):]
    return None


def pda_dfs_trace(M: Any, input_string: str, max_steps: int = 2000) -> Tuple[List[PDATraceStep], bool]:
    """Perform a depth-first search along one accepting path if it exists.

    Returns (steps, accepted) where steps is a sequence of configurations
    along the chosen path. Steps include the initial configuration.
    """
    K, Sigma, Gamma, DELTA, s, A = _pda_parts(M)

    def normalize_str(dafny_seq: Any) -> str:
        return _stringify_seq_of_codepoints(dafny_seq)

    initial_state = s
    if callable(s) and hasattr(s, "fget"):
        initial_state = s
    if callable(initial_state):  # classproperty pattern
        initial_state = initial_state.__get__(None, None)

    stack = ""  # start with empty stack per example

    visited: Set[Tuple[int, str, str]] = set()
    steps: List[PDATraceStep] = [PDATraceStep(i=0, state=initial_state, suffix=input_string, stack=stack)]
    # Track deepest explored path to provide a meaningful trace even on rejection
    best_len: int = 1
    best_steps: List[PDATraceStep] = list(steps)

    def delta_transitions() -> List[Any]:
        return list(_seq_elements(DELTA))

    def dfs(state: int, suffix: str, stack: str, depth: int) -> bool:
        if depth > max_steps:
            return False
        cfg = (state, suffix, stack)
        if cfg in visited:
            return False
        visited.add(cfg)

        # Acceptance: state in A, empty suffix and empty stack
        accepting_states = set(_seq_elements(A)) if hasattr(A, "Elements") or isinstance(A, (list, tuple)) else set()
        if suffix == "" and stack == "" and state in accepting_states:
            return True

        # Try each transition
        for tr in delta_transitions():
            try:
                (from_state, with_symbol, pop_seq), (to_state, push_seq) = tr
                pop_str = normalize_str(pop_seq)
                push_str = normalize_str(push_seq)
            except Exception:
                continue
            if from_state != state:
                continue
            ok, new_suffix = _match_transition(with_symbol, suffix)
            if not ok:
                continue
            remainder = _prefix_match(stack, pop_str)
            if remainder is None:
                continue
            new_stack = push_str + remainder
            steps.append(PDATraceStep(i=len(steps), state=to_state, suffix=new_suffix, stack=new_stack))
            # record deepest path
            nonlocal best_len, best_steps  # type: ignore
            if len(steps) > best_len:
                best_len = len(steps)
                best_steps = list(steps)
            if dfs(to_state, new_suffix, new_stack, depth + 1):
                return True
            # backtrack
            steps.pop()
        return False

    accepted = dfs(initial_state, input_string, stack, 0)
    if accepted:
        return steps, True
    # On rejection, return the deepest explored path so the UI can step through
    return best_steps, False


# ----------------------
# Graph construction API
# ----------------------

def build_pda_graph(M: Any) -> Tuple[Set[int], List[Tuple[int, int, str]]]:
    K, Sigma, Gamma, DELTA, s, A = _pda_parts(M)
    nodes: Set[int] = set(_seq_elements(K))
    edges: List[Tuple[int, int, str]] = []

    def _cp_to_str(cp: Any) -> str:
        try:
            s = _dafny.string_of(cp)
            out = s.VerbatimString(False) if hasattr(s, "VerbatimString") else str(s)
        except Exception:
            out = str(cp)
        # Strip surrounding quotes if present
        if len(out) >= 2 and ((out[0] == "'" and out[-1] == "'") or (out[0] == '"' and out[-1] == '"')):
            return out[1:-1]
        return out

    def _fmt_stack_str(s: str) -> str:
        if len(s) == 0:
            return _epsilon_symbol()
        if len(s) == 1:
            return s[0]
        return s

    for tr in _seq_elements(DELTA):
        try:
            (p, with_symbol, pop_seq), (q, push_seq) = tr
        except Exception:
            continue
        if getattr(with_symbol, "is_epsilon", False):
            read = _epsilon_symbol()
        elif getattr(with_symbol, "is_sym", False):
            read = _cp_to_str(with_symbol.h0_)
        else:
            read = "?"
        pop_s = _fmt_stack_str(_stringify_seq_of_codepoints(pop_seq))
        push_s = _fmt_stack_str(_stringify_seq_of_codepoints(push_seq))
        label = f"{read} / {pop_s} / {push_s}"
        edges.append((p, q, label))
    return nodes, edges


def get_accepting_states(M: Any) -> Set[int]:
    _, _, _, _, _, A = _pda_parts(M)
    return set(_seq_elements(A))


def get_start_state(M: Any) -> int:
    _, _, _, _, s, _ = _pda_parts(M)
    return s


