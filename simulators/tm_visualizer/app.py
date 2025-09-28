from __future__ import annotations

import streamlit as st
import graphviz as gv
from streamlit.components.v1 import html

import trace


st.set_page_config(page_title="TM Visualizer", layout="wide")
st.title("Turing Machine Visualizer (Dafny-generated)")


@st.cache_data(show_spinner=False)
def load_machine():
    return trace.get_default_machine()


name, M = load_machine()

col_left, col_right = st.columns([1, 3], gap="large")

with col_left:
    st.write(f"Machine: {name}")
    user_input = st.text_input("Input string", value="aaab")

    if "tm_runner" not in st.session_state or st.session_state.get("last_input") != user_input:
        st.session_state.tm_runner = trace.TMRunner(M, user_input)
        st.session_state.last_input = user_input

    runner: trace.TMRunner = st.session_state.tm_runner

    # Controls
    c1, c2 = st.columns([1, 1])
    with c1:
        if st.button("◀ Prev", use_container_width=True, disabled=len(runner.history) <= 1):
            runner.back()
    with c2:
        if st.button("Next ▶", use_container_width=True, disabled=False):
            runner.step()

    # Status
    st.caption(f"Configuration {len(runner.history)-1}")

    # Show configuration (left [head] right)
    cfg = runner.current()
    st.markdown(
        f"""
        <div style=\"font-family: ui-monospace, SFMono-Regular, Menlo, Monaco, Consolas, 'Liberation Mono', 'Courier New', monospace; font-size: 1.2rem; padding: 6px 8px; border: 1px solid #eceff1; border-radius: 6px; display: inline-block;\">
          {cfg.left}<span style=\"background:#FFF59D;color:#000;font-weight:600;\">{cfg.head}</span>{cfg.right}
        </div>
        """,
        unsafe_allow_html=True,
    )

    if runner.halted:
        st.markdown("**Result:** TM halted.")
    
    # Simplicity toggle for graph
    show_only_current = st.checkbox("Show only transitions from current state", value=True)

with col_right:
    # Graphviz: states and transitions are implicit in Delta; we visualize only states with start/halting marks
    dot = gv.Digraph(engine="dot")
    dot.attr(rankdir="LR")
    # Simple layout: basic splines and modest spacing
    dot.graph_attr.update({
        "overlap": "false",
        "splines": "true",
        "nodesep": "0.7",
        "ranksep": "0.8",
    })
    dot.edge_attr.update({
        "fontname": "Helvetica",
        "fontsize": "10",
        "arrowsize": "0.8",
    })

    # Node styling
    _, _, Gamma, Delta, start_state, halt_set = M
    halt_states = set(halt_set.Elements) if hasattr(halt_set, "Elements") else set(halt_set)
    current = runner.current().state

    # Discover states from K if present
    K = M[0]
    nodes = list(K.Elements) if hasattr(K, "Elements") else list(K)

    for n in sorted(nodes):
        is_halt = n in halt_states
        is_current = n == current
        attrs = {"shape": "doublecircle" if is_halt else "circle"}
        attrs.update({"style": "filled", "fillcolor": "#FF5722" if is_current else "#CFD8DC"})
        dot.node(str(n), **attrs)

    # Add transition edges with labels: read/write/dir
    def fmt_sym(ch: str) -> str:
        return "□" if ch == runner.blank else ch

    gamma_elems = list(Gamma.Elements) if hasattr(Gamma, "Elements") else list(Gamma)
    # Aggregate parallel edges so labels don't overlap/vanish
    edge_labels = {}
    for n in nodes:
        if show_only_current and n != current:
            continue
        if n in halt_states:
            continue
        for cp in gamma_elems:
            read_ch = trace._cp_to_char(cp)
            try:
                action = Delta(n, cp)
                new_state, write_cp, direction = action
            except Exception:
                try:
                    new_state = action[0]
                    write_cp = action[1]
                    direction = action[2]
                except Exception:
                    continue
            write_ch = trace._cp_to_char(write_cp)
            arrow = "←" if trace._is_left(direction) else "→"
            label = f"{fmt_sym(read_ch)}/{fmt_sym(write_ch)}/{arrow}"
            edge_labels.setdefault((n, new_state), []).append(label)

    for (u, v), labels in edge_labels.items():
        # Multi-line label for clarity
        dot.edge(str(u), str(v), label="\n".join(sorted(set(labels))))

    ghost_id = "ghost_start"
    dot.node(ghost_id, shape="none", label="")
    dot.edge(ghost_id, str(start_state), arrowhead="normal", constraint="false")

    # Zoomable SVG
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
