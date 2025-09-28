from __future__ import annotations

from typing import Set

import streamlit as st
import graphviz as gv
from streamlit.components.v1 import html

import trace


st.set_page_config(page_title="PDA Visualizer", layout="wide")
st.title("PDA Visualizer (Dafny-generated)")


@st.cache_data(show_spinner=False)
def load_default_machine():
    name, M = trace.get_default_machine()
    return name, M


name, M = load_default_machine()

col_left, col_right = st.columns([1, 3], gap="large")

with col_left:
    st.write(f"Machine: {name}")
    user_input = st.text_input("Input string", value="aaabbb")

    run_clicked = st.button("Run / Reset")
    if run_clicked:
        st.session_state.clear()

    steps, accepted = trace.pda_dfs_trace(M, user_input)

    max_step = len(steps) - 1
    if "current_step" not in st.session_state:
        st.session_state.current_step = 0
    if st.session_state.get("last_input") != user_input:
        st.session_state.current_step = 0
    st.session_state.last_input = user_input

    # Prev/Next
    c1, c2 = st.columns([1, 1])
    with c1:
        if st.button("◀ Prev", use_container_width=True, disabled=(len(steps) == 0) or st.session_state.current_step <= 0):
            st.session_state.current_step = max(0, st.session_state.current_step - 1)
    with c2:
        if st.button("Next ▶", use_container_width=True, disabled=(len(steps) == 0) or st.session_state.current_step >= max_step):
            st.session_state.current_step = min(max_step, st.session_state.current_step + 1)

    if len(steps) > 1:
        new_step = st.slider("Step", min_value=0, max_value=max_step, value=st.session_state.current_step, step=1)
        if new_step != st.session_state.current_step:
            st.session_state.current_step = new_step

    # Show configuration
    if len(steps) > 0:
        cur = steps[st.session_state.current_step]
        st.caption(f"Step {st.session_state.current_step} of {max_step}")
        st.markdown(
            f"**Configuration {cur['i']}:** (state={cur['state']}, suffix=\"{cur['suffix']}\", stack=\"{cur['stack']}\")"
        )
        # Only show result at the final step. For rejections, avoid
        # revealing the result immediately when there is only the
        # initial configuration to step through.
        if st.session_state.current_step == max_step and (accepted or max_step > 0):
            st.markdown(f"**Result:** {'✅ Accepted' if accepted else '❌ Rejected'}")
    else:
        st.info("No configurations to display for this input.")

with col_right:
    nodes, edges = trace.build_pda_graph(M)
    accepting = trace.get_accepting_states(M)
    start = trace.get_start_state(M)
    current_state = steps[st.session_state.current_step]["state"] if len(steps) > 0 else None

    # Graphviz
    dot = gv.Digraph(engine="dot")
    dot.attr(rankdir="LR")

    for n in sorted(nodes):
        is_accept = n in accepting
        is_current = (current_state is not None and n == current_state)
        attrs = {"shape": "doublecircle" if is_accept else "circle"}
        if is_current:
            attrs.update({"style": "filled", "fillcolor": "#FF5722"})
        else:
            attrs.update({"style": "filled", "fillcolor": "#CFD8DC"})
        dot.node(str(n), **attrs)

    for u, v, label in edges:
        dot.edge(str(u), str(v), label=label)

    ghost_id = "ghost_start"
    dot.node(ghost_id, shape="none", label="")
    dot.edge(ghost_id, str(start), arrowhead="normal", constraint="false")

    # Zoomable SVG
    svg = None
    try:
        svg = dot.pipe(format="svg").decode("utf-8")
    except Exception:
        svg = None

    if "graph_zoom" not in st.session_state:
        st.session_state.graph_zoom = 100
    z1, z2, z3 = st.columns([1, 1, 2])
    with z1:
        if st.button("Zoom −", use_container_width=True):
            st.session_state.graph_zoom = max(10, st.session_state.graph_zoom - 10)
    with z2:
        if st.button("Zoom +", use_container_width=True):
            st.session_state.graph_zoom = min(1000, st.session_state.graph_zoom + 10)
    with z3:
        st.write(f"Zoom: {st.session_state.graph_zoom}%")

    scale = max(0.05, min(10.0, st.session_state.graph_zoom / 100.0))
    if svg is not None:
        html(
            f"""
            <div style=\"width: 100%; height: 800px; overflow: auto; border: 1px solid #eceff1; background: #fff;\">
              <div style=\"transform: scale({scale}); transform-origin: 0 0; display: inline-block;\">{svg}</div>
            </div>
            """,
            height=820,
        )
    else:
        st.graphviz_chart(dot, use_container_width=True)
