from __future__ import annotations

import sys
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Dict, List, Optional, Sequence, Tuple


def _add_generated_dir_to_syspath() -> Path:
    here = Path(__file__).resolve()
    generated_dir = here.parent.parent / "TM_Simulator-py"
    if str(generated_dir) not in sys.path:
        sys.path.insert(0, str(generated_dir))
    return generated_dir


_generated_dir = _add_generated_dir_to_syspath()

import _dafny as _dafny  # type: ignore

# Try likely module names for Turing_Machine_Simulation
TM_SIM = None  # type: ignore
try:
    import Turing__Machine__Simulation as TM_SIM  # type: ignore
except Exception:
    try:
        import TM__Simulation as TM_SIM  # type: ignore
    except Exception:
        TM_SIM = None  # type: ignore


def _to_py_str(dafny_seq: Any) -> str:
    try:
        if hasattr(dafny_seq, "VerbatimString"):
            return str(dafny_seq.VerbatimString(False))
        return str(dafny_seq)
    except Exception:
        return str(dafny_seq)


def _cp_from_char(ch: str) -> Any:
    return _dafny.CodePoint(ch)


def _cp_to_char(cp: Any) -> str:
    try:
        s = _dafny.string_of(cp)
        out = s.VerbatimString(False) if hasattr(s, "VerbatimString") else str(s)
    except Exception:
        out = str(cp)
    if len(out) >= 2 and ((out[0] == "'" and out[-1] == "'") or (out[0] == '"' and out[-1] == '"')):
        return out[1:-1]
    return out


def _is_left(direction: Any) -> bool:
    name = getattr(direction, "__class__", type(direction)).__name__.lower()
    return "left" in name


def _is_right(direction: Any) -> bool:
    name = getattr(direction, "__class__", type(direction)).__name__.lower()
    return "right" in name


def _epsilon() -> str:
    return "ε"


def get_default_machine() -> Tuple[str, Any]:
    if TM_SIM is None:
        raise RuntimeError("TM module not found. Build TM_Simulator.dfy first.")
    machines: Dict[str, Any] = {}
    default = TM_SIM.default__
    for name in dir(default):
        if name.startswith("_"):
            continue
        try:
            val = getattr(default, name)
            if callable(val) and hasattr(val, "fget"):
                val = val.__get__(None, default)
            # TM: tuple of length 6 for TuringMachine
            if isinstance(val, tuple) and len(val) == 6:
                machines[name] = val
        except Exception:
            continue
    if not machines:
        raise RuntimeError("No TM machines discovered in generated module.")
    for k in sorted(machines.keys()):
        if k.startswith("M"):
            return k, machines[k]
    k = sorted(machines.keys())[0]
    return k, machines[k]


def get_halt_states(M: Any) -> Sequence[int]:
    return list((M[5]).Elements) if hasattr(M[5], "Elements") else list(M[5])


def get_start_state(M: Any) -> int:
    return M[4]


@dataclass
class TMConfig:
    state: int
    left: str
    head: str
    right: str


class TMRunner:
    def __init__(self, M: Any, input_string: str, blank: Optional[str] = None):
        self.M = M
        self.K, self.Sigma, self.Gamma, self.Delta, self.s, self.H = M
        # BLANK symbol from module if available
        if blank is None:
            try:
                blank_cp = getattr(TM_SIM.default__, "BLANK__SQUARE")
                blank = _cp_to_char(blank_cp)
            except Exception:
                blank = " "
        self.blank = blank
        self.history: List[TMConfig] = [
            TMConfig(state=self.s, left="", head=self.blank, right=input_string)
        ]
        self.halted: bool = False

    def current(self) -> TMConfig:
        return self.history[-1]

    def step(self) -> bool:
        if self.halted:
            return False
        cfg = self.current()
        if cfg.state in get_halt_states(self.M):
            self.halted = True
            return False
        # Get action from Delta
        read_cp = _cp_from_char(cfg.head)
        action = self.Delta(cfg.state, read_cp)
        try:
            new_state, write_cp, direction = action
        except Exception:
            # Some backends return tuple-like with attributes
            new_state = action[0]
            write_cp = action[1]
            direction = action[2]
        write_ch = _cp_to_char(write_cp)
        tape = cfg.left + write_ch + cfg.right
        # Move head
        c_index = (len(cfg.left) - 1) if _is_left(direction) else (len(cfg.left) + 1)
        if c_index < 0:
            left, head, right = "", self.blank, tape
        elif c_index >= len(tape):
            left, head, right = tape, self.blank, ""
        else:
            left, head, right = tape[:c_index], tape[c_index], tape[c_index + 1 :]
        # Trim single blank segments
        if len(left) == 1 and left == self.blank:
            left = ""
        if len(right) == 1 and right == self.blank:
            right = ""
        self.history.append(TMConfig(state=new_state, left=left, head=head, right=right))
        if new_state in get_halt_states(self.M):
            self.halted = True
        return True

    def back(self) -> bool:
        if len(self.history) <= 1:
            return False
        self.history.pop()
        self.halted = False
        return True


