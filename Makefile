# Uniform forests of complete graphs: paper and verification repository.
#
# Targets
#   make check       fast verification  (NMAX =  260)  NOT proof-complete
#   make check-proof proof-complete with overlap (NMAX = 700; minimum is 650)
#   make check-full  full published seam(NMAX = 1200)
#   make paper       build paper/main.pdf with a plain pdflatex loop
#   make sums        (re)generate evidence/SHA256SUMS.txt
#   make clean       remove build by-products
#
# Everything is stdlib Python 3 and plain pdflatex.  No latexmk, no bibtex,
# no third-party Python package, no network access.  Peak RSS stays well under
# 1 GiB for every target; the largest, check-full, peaks in the tens of MiB.

PYTHON   ?= python3
PDFLATEX ?= pdflatex
CHECK     = tests/check.py

# Pin the PDF creation date so that `make paper` is byte-reproducible and the
# hash recorded in evidence/SHA256SUMS.txt is stable across rebuilds.
SOURCE_DATE_EPOCH ?= 1
export SOURCE_DATE_EPOCH
FORCE_SOURCE_DATE ?= 1
export FORCE_SOURCE_DATE

.PHONY: all check check-proof check-full paper sums clean

all: check-proof paper

# --- verification ----------------------------------------------------------

# Fast default.  Section C of the checker -- every analytic constant in the
# note -- is independent of NMAX and is fully exercised here; only the finite
# integer seam is shortened.  The run prints a loud NOT PROOF-COMPLETE banner
# listing exactly which finite blocks it did not establish.
check:
	$(PYTHON) $(CHECK) --nmax 260 --quick

# Default proof run: the exact seam 3..700 overlaps the analytic range n >= 651.
# The mathematical minimum is NMAX=650; tests/check.py accepts that boundary.
check-proof:
	$(PYTHON) $(CHECK) --nmax 700

# The wider seam quoted in the note (Computation A.2), including the strict
# monotonicity of both orbit ratios and the independent pair-count cross-check
# over their full stated finite ranges.
check-full:
	$(PYTHON) $(CHECK) --nmax 1200 --ncross 1200

# --- manuscript ------------------------------------------------------------

# Three passes: hyperref's outlines settle after the references resolve.
# The bibliography is a manual thebibliography environment, so bibtex is never
# invoked; paper/references.bib ships for reuse only.
paper: paper/main.pdf

paper/main.pdf: paper/main.tex
	cd paper && $(PDFLATEX) -interaction=nonstopmode -halt-on-error main.tex
	cd paper && $(PDFLATEX) -interaction=nonstopmode -halt-on-error main.tex
	cd paper && $(PDFLATEX) -interaction=nonstopmode -halt-on-error main.tex

# --- evidence --------------------------------------------------------------

sums:
	@rm -f evidence/SHA256SUMS.txt
	@find . -type f \
	    -not -path './.git/*' \
	    -not -path '*/__pycache__/*' \
	    -not -name 'SHA256SUMS.txt' \
	    -not -name '*.aux' -not -name '*.log' -not -name '*.out' \
	    -not -name '*.toc' -not -name '*.pyc' \
	  | LC_ALL=C sort | xargs sha256sum > evidence/SHA256SUMS.txt
	@echo "wrote evidence/SHA256SUMS.txt ($$(wc -l < evidence/SHA256SUMS.txt) files)"

clean:
	rm -f paper/*.aux paper/*.log paper/*.out paper/*.toc
	rm -rf tests/__pycache__ __pycache__
