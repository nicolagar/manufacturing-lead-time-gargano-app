# Manufacturing Lead Time Hybrid

This version keeps the classic backend-served page structure (calculator, Gantt, process input, formula input, schedule export) and replaces only the network diagram area with the rewritten router bundle.

## Deploy on Render

Build command:

```bash
pip install -r requirements.txt
```

Start command:

```bash
uvicorn app:app --host 0.0.0.0 --port $PORT
```


Updated in v3: horizontal tree layout rule for successors; validated no connector crossings or connector overlaps on PERT_v3_03.


## v4 update
- Critical styling for nested processes is now recursive based on `schedule[].critical`.
- Compound/nested processes on the critical path get a red outer contour even when they are both a parent and a child.
