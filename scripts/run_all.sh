#!/usr/bin/env bash
# Regenerate every number, table and figure of the paper, then compile it.
set -euo pipefail
cd "$(dirname "$0")"
python3 -I experiments.py              # Figures 1-3, Tables 2-3, results.json (about 1 minute)
python3 -I peak_heights.py             # Table 1
python3 -I impurities_and_circle.py    # Tables 4-6, Figure 4
python3 -I weil_form_zero_side.py "math.log(13)" 8     # zero-side cross-check for Table 7
python3 -I weil_form_mp.py "log(13)" 8 80              # Table 7, left column
for n in 4 6 8 10 12 14; do python3 -I weil_form_mp.py "log(13)" $n 90; done   # Table 8
python3 -I weil_form_mp.py "log(100)" 16 70            # e^L = 100 ground state
python3 -I frobenius_turns.py          # Table 9, Figure 5
python3 -I stepanov_sweep.py           # Table 10 (about 6 minutes)
python3 -I quasi_rh_recursion.py       # Table 11
python3 -I fig6_routes.py              # Figure 6
python3 -I torus_closure.py            # Table 13 (about 20 minutes)
python3 -I prime_spirals.py            # Figure 7
python3 -I character_family.py         # Table 14, Figure 8
python3 -I amplifier.py                # Table 15, Figure 9
python3 -I worst_member.py             # Table 16
python3 -I siegel_check.py             # smallest L(1, chi)
python3 -I q163.py                     # q = 163 prime sums (about 2 minutes)
python3 -I q163_zeros.py               # Table 17
python3 -I fig10_q163.py               # Figure 10
cd ../paper && latexmk -pdf -interaction=nonstopmode -halt-on-error Angles_and_Radii_of_the_Riemann_Zeros.tex
