"""Redraw figures from unchanged recorded CSVs; no trajectory rerun."""
from pathlib import Path
import argparse, csv, importlib.util
from collections import defaultdict
p=argparse.ArgumentParser()
p.add_argument('--data',default='output')
p.add_argument('--out',default='output')
p.add_argument('--program',default='run_experiments.py')
a=p.parse_args(); data=Path(a.data); out=Path(a.out);out.mkdir(parents=True,exist_ok=True)
spec=importlib.util.spec_from_file_location('bb_figures',a.program)
mod=importlib.util.module_from_spec(spec);spec.loader.exec_module(mod)
with (data/'cubic_gap.csv').open(newline='') as f:
    cubic=[{k:(v if k=='word' else float(v)) for k,v in row.items()} for row in csv.DictReader(f)]
traces=defaultdict(list)
with (data/'finite_budget_traces.csv').open(newline='') as f:
    for row in csv.DictReader(f):
        traces[row['case'],row['method']].append({'log10_norm_ratio':float(row['log10_norm_ratio'])})
mod.plots(out,cubic,traces)
print('Figures regenerated from stored traces; CBB2 raw key displays as CBB1(m=2).')
