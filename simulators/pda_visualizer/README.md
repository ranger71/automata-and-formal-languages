# PDA Visualizer (Dafny-generated)

Graphviz-based visualizer for the PDA simulator generated from `PDA_Simulator.dfy`.

## Prerequisites
- Python 3.9+
- Dafny CLI
- Graphviz installed system-wide (e.g., `brew install graphviz` on macOS)

## Generate Python code
```bash
# From repo root
dafny build --target:py "simulators/PDA_Simulator.dfy"
```
This creates `simulators/PDA_Simulator-py/`.

## Install and run
```bash
cd simulators/pda_visualizer
python3 -m venv .venv && source .venv/bin/activate
pip install -r requirements.txt
streamlit run app.py
```

## Using the app
- Enter an input string and step through PDA configurations.
- Double-circle nodes are accepting; a short arrow indicates the start state.
- Zoom with the buttons at the bottom.
