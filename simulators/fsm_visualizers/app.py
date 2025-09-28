from __future__ import annotations

import io
from pathlib import Path
from typing import Dict, Tuple, Set

import streamlit as st
import graphviz as gv
from streamlit.components.v1 import html

import trace


st.set_page_config(page_title="FSM Visualizer", layout="wide")
st.title("FSM Visualizer (Dafny-generated)")


@st.cache_data(show_spinner=False)
def load_machines():
    return {
        "DFSM": trace.get_dfsm_machine(),
        "NDFSM": trace.get_ndfsm_machine(),
    }


machines = load_machines()

col_left, col_right = st.columns([1, 3], gap="large")

with col_left:
    machine_kind = st.selectbox("Machine type", ["DFSM", "NDFSM"], index=0)
    # Graphviz is the only renderer now

    default_input = "1001" if machine_kind == "DFSM" else "abba"
    user_input = st.text_input("Input string", value=default_input)

    run_clicked = st.button("Run / Reset")

    if run_clicked:
        st.session_state.clear()

    # Compute trace
    if machine_kind == "DFSM":
        M = machines["DFSM"]
        steps = trace.dfsm_trace(M, user_input)
        accepts = trace.dfsm_accepts(M, steps[-1]["state"]) if steps else False
        nodes, edges = trace.build_dfsm_graph(M)
        start_state = steps[0]["state"] if steps else None
    else:
        M = machines["NDFSM"]
        steps = trace.ndfsm_trace(M, user_input)
        accepts = trace.ndfsm_accepts(M, steps[-1]["states"]) if steps else False
        nodes, edges = trace.build_ndfsm_graph(M)
        start_states = steps[0]["states"] if steps else set()

    # Reset step when machine or input changes; ensure current_step exists
    if "current_step" not in st.session_state:
        st.session_state.current_step = 0
    if (
        st.session_state.get("last_machine_kind") != machine_kind
        or st.session_state.get("last_input") != user_input
    ):
        st.session_state.current_step = 0
    st.session_state.last_machine_kind = machine_kind
    st.session_state.last_input = user_input

    max_step = len(steps) - 1

    # Button controls first so state updates apply before rendering the slider
    btn_col1, btn_col2 = st.columns([1, 1])
    with btn_col1:
        if st.button("◀ Prev", use_container_width=True, disabled=(len(steps) == 0) or st.session_state.current_step <= 0):
            st.session_state.current_step = max(0, st.session_state.current_step - 1)
    with btn_col2:
        if st.button("Next ▶", use_container_width=True, disabled=(len(steps) == 0) or st.session_state.current_step >= max_step):
            st.session_state.current_step = min(max_step, st.session_state.current_step + 1)

    # Now render the slider using the possibly updated state; sync back if user drags it
    if len(steps) > 0:
        new_step = st.slider(
            "Step", min_value=0, max_value=max_step, value=st.session_state.current_step, step=1
        )
        if new_step != st.session_state.current_step:
            st.session_state.current_step = new_step

    

    # Step indicator (acceptance shown only at final step below)
    if len(steps) > 0:
        st.caption(f"Step {st.session_state.current_step} of {max_step}")

    # Show prefix/suffix and compute current highlight if steps exist
    if len(steps) > 0:
        cur = steps[st.session_state.current_step]
        prefix = cur["prefix"]
        suffix = cur["suffix"]

        def _esc(s: str) -> str:
            return s.replace("&", "&amp;").replace("<", "&lt;").replace(">", "&gt;")

        if len(suffix) > 0:
            next_char = _esc(suffix[0])
            rest_suffix = _esc(suffix[1:])
            highlighted_suffix = f"<span style=\"background:#FFF59D;color:#000;font-weight:600;\">{next_char}</span>{rest_suffix}"
        else:
            highlighted_suffix = ""

        st.markdown(
            f"""
            <div style=\"margin-top: 0.25rem;\"><strong>Configuration {cur['i']}:</strong></div>
            <div style=\"font-family: ui-monospace, SFMono-Regular, Menlo, Monaco, Consolas, 'Liberation Mono', 'Courier New', monospace; font-size: 1.2rem; padding: 6px 8px; border: 1px solid #eceff1; border-radius: 6px; display: inline-block;\">
              &lt;{_esc(prefix)} | {highlighted_suffix}&gt;
            </div>
            """,
            unsafe_allow_html=True,
        )

        current_highlight: Set[int]
        if machine_kind == "DFSM":
            current_highlight = {cur["state"]}
        else:
            current_highlight = set(cur["states"])  # may be empty
        # Show acceptance only at last configuration
        if st.session_state.current_step == max_step:
            st.markdown(
                f"**Result:** {'✅ Accepted' if accepts else '❌ Rejected'}"
            )
    else:
        current_highlight = set()
        st.info("No configurations to display for this input.")

with col_right:
    def _sanitize_label_str(s: str) -> str:
        # Remove surrounding quote characters from codepoint renderings
        return s.replace("'", "").replace('"', "")
    start_nodes: Set[int]
    if machine_kind == "DFSM":
        start_nodes = {steps[0]["state"]} if len(steps) > 0 else set()
        accepting = set(trace.DFSM.default__.A(machines["DFSM"]).Elements)
        start_single = trace.DFSM.default__.s(machines["DFSM"])  # unique start state
    else:
        start_nodes = set(steps[0]["states"]) if len(steps) > 0 else set()
        accepting = set(trace.NDFSM.default__.ND__A(machines["NDFSM"]).Elements)
        start_single = trace.NDFSM.default__.ND__s(machines["NDFSM"])  # underlying start state

    # Graphviz with classical FSM styling
    dot = gv.Digraph(engine="dot")
    dot.attr(rankdir="LR")
    dot.graph_attr.update({"nodesep": "0.2", "ranksep": "0.4"})
    # Nodes
    for n in sorted(nodes):
        is_accept = n in accepting
        is_current = n in current_highlight
        attrs = {"shape": "doublecircle" if is_accept else "circle"}
        if is_current:
            attrs.update({"style": "filled", "fillcolor": "#FF5722"})
        else:
            attrs.update({"style": "filled", "fillcolor": "#CFD8DC"})
        dot.node(str(n), **attrs)
    # Edges
    for (u, v), labels in edges.items():
        label = ",".join(sorted(_sanitize_label_str(s) for s in labels if s))
        dot.edge(str(u), str(v), label=label)
    # Ghost start arrow (very short, not a real transition)
    ghost_id = f"ghost_start"
    dot.node(ghost_id, shape="none", label="")
    dot.edge(ghost_id, str(start_single), arrowhead="normal", constraint="false")

    # Render as SVG for zooming; fall back to Streamlit renderer on error
    svg = None
    try:
        svg = dot.pipe(format="svg").decode("utf-8")
    except Exception:
        svg = None

    # Zoom control for the graph (buttons at bottom)
    if "graph_zoom" not in st.session_state:
        st.session_state.graph_zoom = 100
    zc1, zc2, zc3 = st.columns([1, 1, 2])
    with zc1:
        if st.button("Zoom −", use_container_width=True):
            st.session_state.graph_zoom = max(10, st.session_state.graph_zoom - 10)
    with zc2:
        if st.button("Zoom +", use_container_width=True):
            st.session_state.graph_zoom = min(1000, st.session_state.graph_zoom + 10)
    with zc3:
        st.write(f"Zoom: {st.session_state.graph_zoom}%")

    scale = max(0.05, min(10.0, st.session_state.graph_zoom / 100.0))
    if svg is not None:
        container_height = 800
        html(
            f"""
            <div style=\"width: 100%; height: {container_height}px; overflow: auto; border: 1px solid #eceff1; background: #fff;\">\n              <div style=\"transform: scale({scale}); transform-origin: 0 0; display: inline-block;\">{svg}</div>\n            </div>
            """,
            height=820,
        )
    else:
        st.graphviz_chart(dot, use_container_width=True)



