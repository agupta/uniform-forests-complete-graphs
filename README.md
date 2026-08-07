# Negative correlation in uniform forests of complete graphs

[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.21833802.svg)](https://doi.org/10.5281/zenodo.21833802)

This repository accompanies Anish Gupta's preprint *Edges of the uniform
random forest of K_n are pairwise negatively correlated for every n*.

The paper proves pairwise negative correlation for every complete graph.  It
reduces the disjoint-edge inequality to exact component and degree moments,
uses effective analytic bounds above a finite threshold, and checks the
remaining values by exact integer recurrence.

- [Read the paper](paper/main.pdf)
- [Citable preprint v1 on Zenodo](https://doi.org/10.5281/zenodo.21833802)
- [See the preferred citation](CITATION.cff)

## Verification

The standalone checker uses only Python's standard library.

```sh
make check       # fast diagnostic seam; explicitly not proof-complete
make check-proof # proof-complete finite/analytic overlap
make check-full  # wider seam and independent pair-count checks
make paper       # reproducible three-pass PDF build
```

Status: preprint, 7 August 2026.  This repository is a public landing page and
reproducibility companion; it is not a claim of peer review.

## Repository contents

```text
paper/                    manuscript source, bibliography, and PDF
tests/check.py            standalone exact and analytic verifier
evidence/SHA256SUMS.txt   release-tree integrity manifest
CITATION.cff              citation metadata
LICENSES.md               manuscript/software licence boundary
```

## Citation

The citable preprint v1 is archived at
[doi:10.5281/zenodo.21833802](https://doi.org/10.5281/zenodo.21833802).
Preferred citation metadata are provided in [`CITATION.cff`](CITATION.cff).

Software and the `Makefile` are MIT-licensed.  The manuscript and public
documentation are CC BY 4.0; see [LICENSES.md](LICENSES.md).

Contact: Anish Gupta, independent researcher,
`ag2269@cantab.ac.uk`, [ORCID 0009-0008-8137-7729](https://orcid.org/0009-0008-8137-7729).
