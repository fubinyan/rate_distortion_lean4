"""Render the report overview from machine-extracted dependency data.

Run after GenerateDependencyGraph.lean and GenerateDependencyArtifacts.ps1.
Requires reportlab; writes a vector PDF beside this script.
"""
from pathlib import Path
import json
import re
import textwrap
from reportlab.pdfgen import canvas
from reportlab.lib.colors import HexColor, Color

ROOT = Path(__file__).resolve().parent
raw = (ROOT / 'rate_distortion_dependency_data.js').read_text(encoding='utf-8-sig')
graph = json.loads(raw.split('=', 1)[1].strip().removesuffix(';'))
nodes = {n['id']: n for n in graph['nodes']}
core = {k: n for k, n in nodes.items() if n['overview']}
adj = {k: set() for k in nodes}
for edge in graph['edges']:
    adj[edge['source']].add(edge['target'])
# Hide non-overview nodes, preserving paths to the next overview node.
edges = set()
for source in core:
    pending = list(adj[source])
    seen = set()
    while pending:
        target = pending.pop()
        if target in seen:
            continue
        seen.add(target)
        if target in core:
            edges.add((source, target))
        else:
            pending.extend(adj[target])
# Transitive reduction on the overview DAG.
def alternate(source, target, skip):
    seen, pending = set(), [source]
    while pending:
        u = pending.pop()
        for a, b in edges:
            if a == u and (a, b) != skip and b not in seen:
                if b == target:
                    return True
                seen.add(b)
                pending.append(b)
    return False
reduced = [e for e in sorted(edges) if not alternate(*e, e)]

W, H = 1140, 610
c = canvas.Canvas(str(ROOT / 'rate_distortion_dependency_graph_report.pdf'), pagesize=(W, H))
c.setTitle('Rate-distortion proof dependencies: generated overview')
labels = ['Finite probability', 'Information measures', 'Test-channel optimization',
          'Memoryless random coding', 'Finite-block converse', 'Asymptotic theorems']
fills = ['#e8f0f8', '#eaf3e9', '#f5efe5', '#e9f2f2', '#f2eaf5', '#f7ece8']
positions = {}
for group in range(6):
    group_nodes = [k for k, n in core.items() if n['groupIndex'] == group]
    x = 16 + group * 188
    for i, key in enumerate(group_nodes):
        positions[key] = (x, H - 106 - i * 78, 172, 66)

c.setStrokeColor(Color(.34, .42, .49, alpha=.45))
c.setLineWidth(.65)
for source, target in reduced:
    x, y, w, h = positions[source]
    u, v, tw, th = positions[target]
    if x == u:
        a, b = x + w/2, y
        d, e = u + tw/2, v + th
    else:
        a, b = x + w, y + h/2
        d, e = u, v + th/2
    p = c.beginPath()
    p.moveTo(a, b)
    p.curveTo(a + 18, b, d - 18, e, d, e)
    c.drawPath(p)
    c.line(d - 4, e + 2, d, e)
    c.line(d - 4, e - 2, d, e)

for group, title in enumerate(labels):
    c.setFillColor(HexColor('#263b4b'))
    c.setFont('Helvetica-Bold', 11)
    for j, line in enumerate(textwrap.wrap(title, 24)):
        c.drawString(16 + group * 188, H - 23 - j * 13, line)
for key, (x, y, w, h) in positions.items():
    c.setFillColor(HexColor(fills[core[key]['groupIndex']]))
    c.setStrokeColor(HexColor('#8c9ca9'))
    c.roundRect(x, y, w, h, 4, fill=1, stroke=1)
    lines = textwrap.wrap(key, 23, break_long_words=True)
    font = min(11, 48 / max(1, len(lines)))
    c.setFont('Courier', font)
    c.setFillColor(HexColor('#172b3a'))
    for j, line in enumerate(lines):
        c.drawString(x+7, y+h-13-j*(font+1), line)
c.setFont('Helvetica', 10)
c.setFillColor(HexColor('#3b4a55'))
c.drawString(16, 18, f'{len(core)} selected overview declarations; {len(reduced)} reduced dependency paths. Full interactive graph: {len(nodes)} declarations.')
c.save()
print(f'Generated report graph: {len(core)} nodes, {len(reduced)} dependency paths.')
