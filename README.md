# Fricke supersingular polynomials at levels 5, 7 and 13

Paper and verification code for

> D. Jordan, *Fricke supersingular polynomials at levels 5, 7 and 13* (2026).

The paper proves Sakai's Heun conjecture for the Fricke groups of levels 5 and 7, corrected
forms of Nakaya's Conjectures 1 and 3, and an explicit five-term recurrence for the
supersingular polynomial of the Fricke group of level 13.

## Contents

| Path | What it is |
|---|---|
| `Fricke_Supersingular_Polynomials_v1_4.tex`, `.pdf` | The paper |
| `code/levels_5_7/identities.gp` | Exact certificates for levels 5 and 7 (Appendix A of the paper) |
| `code/level_13/identities13.gp` | Exact certificates for level 13 (Appendix A) |
| `code/levels_5_7/finite_check.gp` | Bounded check of the level 5 and 7 results, all primes p <= 2000 |
| `code/level_13/finite13.gp` | Bounded check of the level-13 results, all primes p <= 2000 |
| `code/level_13/t0search.gp` | Primes p <= 6000 where the level-13 recurrence polynomial loses a degree |
| `code/levels_5_7/p11_counterexample.gp` | The printed Conjecture 1 against the corrected one at N = 7, p = 11 |
| `code/run_gp.py` | Runs a `.gp` file through `cypari2` if no `gp` binary is installed |
| `logs/` | Output of the runs made for the paper |

The `identities*.gp` scripts certify the characteristic-zero identities used in the
proofs. The `finite*.gp` and `t0search.gp` scripts are consistency checks only; the proofs do
not depend on them.

## Running

With PARI/GP 2.15 or later:

    gp -q code/levels_5_7/identities.gp
    gp -q code/level_13/identities13.gp
    gp -q code/levels_5_7/finite_check.gp      # about 2 minutes
    gp -q code/level_13/finite13.gp            # about 4 minutes

Without a `gp` binary:

    pip install cypari2
    python3 code/run_gp.py code/level_13/finite13.gp 8000000000

Each script ends with `ALL CHECKS PASSED` or a count of failures. The recorded runs used
PARI 2.17.2 through `cypari2`.

## Notation

The scripts were written before the final version of the paper, and some variable names
differ from it: `e4`, `e6` in the scripts are the paper's `v_4`, `v_6`, and the level-13
exponents `a`, `b` are the paper's `e_2`, `e_3`.

## Use of AI tools

The mathematics, code and text were developed with substantial assistance from AI systems
(ChatGPT and Claude), as stated in the paper.

## Licence

MIT (see `LICENSE`).
