# TM Visualizer (Dafny-generated)

On-demand stepper for the Turing Machine simulator generated from `TM_Simulator.dfy`. No slider; use Next/Prev.

## Prerequisites
- Python 3.9+
- Dafny CLI
- Graphviz installed (`brew install graphviz` on macOS)

## Generate Python code
```bash
# From repo root
dafny build --target:py "simulators/TM_Simulator.dfy"
```
This creates `simulators/TM_Simulator-py/`.

## Install and run
```bash
cd simulators/tm_visualizer
python3 -m venv .venv && source .venv/bin/activate
pip install -r requirements.txt
streamlit run app.py
```

## Using the app
- Enter an input string
- Click Next to generate the next configuration; Prev to go back
- Halting states are double-circled; current state is orange
