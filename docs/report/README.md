# Reproducing the architecture report

Run these commands from the repository root after installing Lean and building the project:

```sh
lake exe cache get
lake build
lake env lean docs/report/GenerateDependencyGraph.lean
pwsh -File docs/report/GenerateDependencyArtifacts.ps1
python -m pip install -r docs/report/requirements.txt
python docs/report/render_dependency_graph.py
```

The Lean extractor inspects constant references in the compiled `RateDistortion` module. The PowerShell script merges edge types and computes a transitive reduction. The Python script renders a smaller overview, preserving paths through hidden nodes. Its PDF is used in the report; the HTML presents the full selected-declaration graph.

Open `docs/report/rate_distortion_dependency_graph.html` in a browser, keeping `rate_distortion_dependency_data.js` beside it. No server is required.

To build the report, use XeLaTeX with Times New Roman, Arial, and Consolas installed (as in the original Windows report environment). On another system, install these fonts or adapt the three font declarations in the preamble:

```sh
cd docs/report
xelatex -interaction=nonstopmode -halt-on-error rate_distortion_formalization_infrastructure.tex
xelatex -interaction=nonstopmode -halt-on-error rate_distortion_formalization_infrastructure.tex
```

Copy the resulting PDF to `rate_distortion_formalization_infrastructure.pdf` at the repository root. The root copy is the reader-facing report linked from the main README.

Lean excerpts in the report are explanatory: section variables and some arguments are abbreviated. The actual `.lean` files are the compilation targets and authoritative theorem signatures.
