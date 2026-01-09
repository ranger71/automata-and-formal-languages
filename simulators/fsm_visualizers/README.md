# FSM Visualizer (Dafny-generated)

Interactive UI to step through DFSM and NDFSM runs produced by your Dafny program and see configurations `<prefix | suffix>` with highlighted state(s).

## Prerequisites
- Python 3.9+
- Dafny CLI installed
- Generated Python present (run once):

```bash
# From repo root
dafny build --target:py "simulators/FSM_Simulators.dfy"
```

This creates `simulators/FSM_Simulators-py/` with `_dafny.py` and generated modules.

## Install and Run
```bash
cd simulators/fsm_visualizers
python3 -m venv .venv && source .venv/bin/activate
pip install -r requirements.txt
streamlit run app.py
```

## Using the App
- Select machine type (DFSM or NDFSM).
- Enter an input string.
- Use the Step slider to move forward/back. The UI shows:
  - Current configuration as `<prefix | suffix>`
  - Graph with current state(s) highlighted
  - Acceptance result
  - Buttons: ◀ Prev, Next ▶ for precise stepping

### Renderer
- Graphviz only: traditional FSM look (double-circle accepting states, short ghost start arrow).

## Graph legend
- Start node: small incoming arrow from a ghost node (start marker; not a real transition). The start state may still have regular incoming transitions.
- Accepting nodes: double circle (thick border)
- Current node(s): orange fill
- Other nodes: gray fill

- DFSM current state: exactly one orange node at each step.
- NDFSM current states: multiple orange nodes are possible.

## Notes
- The app auto-loads the generated code from `../FSM_Simulators-py`.
- If you see `ModuleNotFoundError: _dafny`, re-run the build step above.
- Edge labels are best-effort from Dafny `CodePoint`; blank labels can occur but do not affect stepping.

## Customize
- Machines are imported from the generated `FSM__SIMULATION.py` (`M__5__4` DFSM, `M__59` NDFSM). Update those in Dafny and re-run `dafny build` to refresh.
