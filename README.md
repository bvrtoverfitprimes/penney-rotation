# The rotation strategy in Penney's game for permutations

This repository holds data, tables, code, and formal proofs on Penney's game for permutations: the
second player answers a pattern `a_1 a_2 ... a_k` with its rotation `a_k a_1 ... a_(k-1)`, and wins
with probability greater than one half for every `k >= 3`. This is Conjecture 6.1 of S. Elizalde
and Y. Lin, *Penney's game for permutations*, Discrete Mathematics & Theoretical Computer Science
28:1 (2026).

All counts are exact integers and all bounds are exact rationals. No floating-point value is used in
any decision.

## Contents

| Path | Contents |
| --- | --- |
| `code/cluster_dp.py` | The rank-insertion recurrence for the signed cluster coefficients `d_n` and the arrival counts used for the refined tail bound. |
| `code/certificates.py` | The exact certificates for `3 <= k <= 7`, the constant for `k >= 8`, and a check of the cluster factorization against direct enumeration of first occurrences for every pattern of length 3 and 4 through length 8. Writes `data/certificates.json` and `data/pair_bounds_k*.csv`. |
| `code/linear_extensions.cpp`, `code/independent_check.py` | An independent enumeration of the cluster coefficients and prefix counts by linear extensions, compared with the recurrence for every representative with `k = 4` (`h = 4`) and `k = 5` (`h = 1`). |
| `code/first_counts.cpp`, `code/finite_horizon.py` | Exhaustive first-occurrence counts `a_n`, `b_n` for every pattern and every `3 <= k < n <= 11`. Writes `data/finite_horizon.json`. |
| `code/make_tables.py` | Formats the records in `data/` into the tables in `tables/`. |
| `data/certificates.json` | For `k = 3, 4, 5`: every complement representative, its coefficients `d_(k+1), ..., d_(k+R-1)`, prefix count, and certified lower bound for `k! D`. For `k = 6, 7`: the minima. |
| `data/pair_bounds_k6.csv`, `data/pair_bounds_k7.csv` | The bound `J(A)` for all 360 and 2520 complement representatives, sorted. |
| `data/finite_horizon.json` | The minimum of `b_n - a_n` over all patterns for each `(k, n)`. |
| `tables/*.tex` | The generated LaTeX tables. |
| `lean/` | Formal proofs for Lean 4 with Mathlib. |

## Running the computations

Python 3.8 or later is required, with no external packages, together with a C++17 compiler.

```
g++ -O3 -std=c++17 code/first_counts.cpp -o code/first_counts
g++ -O3 -std=c++17 code/linear_extensions.cpp -o code/linear_extensions
python code/certificates.py
python code/independent_check.py
python code/finite_horizon.py
python code/make_tables.py
```

On Windows, add `.exe` to the two output names. Each script stops with an error if any check fails.
On a laptop, the first three scripts take about one, two, and half a minute.

## Checking the formal proofs

```
cd lean
lake exe cache get
lake build
lake env lean Axioms.lean
```

| File | Contents |
| --- | --- |
| `Rotation/Cancellation.lean` | The total signed weight of the clusters on one ordering is `-1`, `0`, or `1`; a connected chain meets every block of `k - 1` starts. |
| `Rotation/Tail.lean` | The geometric tail sums and their closed forms. |
| `Rotation/Shuffle.lean` | Twice the number of interleavings is at most `C(2d, d)` when the two gap vectors differ. |
| `Rotation/Leading.lean` | A self-overlapping pattern is monotone; the leading coefficient `d_(k+1)` is at least one. |
| `Rotation/Uniform.lean` | The estimate `(k+1)(S_k + H_k) < 1` and `D > 0` for every `k >= 8`, and the lower bound on the advantage. |
| `CertDefs/Defs.lean`, `Rotation/Certificates.lean` | The certificates for `3 <= k <= 7` and the cross-checks, evaluated with `native_decide`. |

`Axioms.lean` prints the axioms used by the main theorems. The analytic results use only the standard
axioms. The certificates also rely on the Lean compiler through `native_decide`. The probability
model, the cluster factorization, and the overlap product formula are not formalized; the last two
are checked numerically by `factorization_check` and `overlap_check`.

## Licence

The code in `code/` and `lean/` is released under the MIT License (`LICENSE`). The tables and the
data records are released under the Creative Commons Attribution 4.0 International License
(`LICENSE-CC-BY-4.0.md`).

## Citation

Please cite this repository (see `CITATION.cff`).
