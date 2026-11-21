# 84 · Levent Alpöge with Claude (2026)

On November 20, 2026, Levent Alpöge released a Lean proof that every nontrivial zero of the Riemann zeta function has real part ½. The release also proves the generalized Riemann hypothesis for Dirichlet L-functions. The original proof can be read locally starting at `.lake/lean/src/Main.lean`, or in the [community source mirror](https://github.com/leanprover-community/riemann-hypothesis/blob/main/src/Main.lean).

## Place on the RH map

Corridor 7 groups work on RH through arithmetic geometry. Alpöge traces the argument to Stepanov's treatment of multiplicity over function fields and describes using chains of theta lifts to recover its effect over the integers. The dotted edge from the finite-field RH node records that analogy. The solid edge from node 84 to RH records the conclusion checked by independent proof kernels. Node 76, Alpöge–Furman, remains the earlier result on the proportion of critical-line zeros. [Author’s note](https://alpo.ge/remark.pdf) · [November RH map](../../The%20RH%20Map%20-%20Nov%2021,%202026%20-%20Mermaid%20Diagram.txt)

## Reading the Lean source

Start with `src/Main.lean` in the extracted project. It exports the five theorems below. The four explicit propositions are in `src/Statements.lean`. The bridge in `src/Supplements/Kernels/MainTheorems.lean` defines `allChi` using `UpperTheory.FinalTheorems.everyCharacter`, then applies `Formalism.VW.rh_of_every` to obtain `rhOfAll`, the proof of classical RH. [Main](https://github.com/leanprover-community/riemann-hypothesis/blob/main/src/Main.lean) · [Statements](https://github.com/leanprover-community/riemann-hypothesis/blob/main/src/Statements.lean) · [Proof bridge](https://github.com/leanprover-community/riemann-hypothesis/blob/main/src/Supplements/Kernels/MainTheorems.lean)

| Export | Conclusion |
| --- | --- |
| `riemannHypothesis` | Mathlib’s existing proposition `RiemannHypothesis`. |
| `riemannZeta_eq_zero_re` | A zeta zero distinct from 1 and the negative even integers has real part ½. |
| `LFunction_ne_zero_of_half_lt_re` | For every Dirichlet character of positive modulus, the L-function is nonzero to the right of ½, with the principal character at 1 excepted. |
| `LFunction_eq_zero_re` | For any such character, a zero in the open critical strip has real part ½. |
| `LFunction_eq_zero_re_of_isPrimitive` | The same critical-strip conclusion for primitive characters. |

## Verification record

- **Local kernel replay, November 21, 2026.** con-leche accepted all 1,468,418 declarations in the published proof export and justified all five challenge theorems. The conclusion of `riemannHypothesis` is Mathlib’s `RiemannHypothesis`. Checking the challenge alone stopped at the missing RH proof. The verified comparison exited 0 after 16 minutes 21 seconds on 12 Windows workers. The independent reports below document the source-to-export build. [Published exports](https://math.mit.edu/~drew/grh/) · [Local checker transcript](Verification/2026-11-21-con-leche.txt) · [Command, hashes and checker revision](Verification/2026-11-21-run.json)
- **Local source intake, November 21, 2026.** The 14 author-hosted parts concatenate to the 239,275,554-byte archive identified below. Its SHA-256 matches the MIT and LUMI records. All 175,187 Lean sources and three configuration files in the extracted tree matched the archive byte for byte (1,030,536,719 bytes). Local source inspection also confirmed the five exports and toolchain pins.
- **Andrew Sutherland, MIT.** His November 21 report at 08:45 UTC records a full compile and kernel replay, acceptance of the exported proof by nanoda and con-leche, and successful matching of all five theorem statements. The five depend only on `propext`, `Classical.choice`, and `Quot.sound`. The end-to-end `lake comparator` run was still in progress at that timestamp. [Verification report](https://math.mit.edu/~drew/grh/) · [Axiom audit](https://math.mit.edu/~drew/grh/audit.log)
- **Aapo Lipponen, LUMI.** A second build compiled all 175,187 modules in a network-isolated environment. The compiled `Main` and `Statements` files matched Sutherland’s hashes. [Build record](https://github.com/aapolipponen/rh-lean-check-lumi)

## Source pins and restoration

| Local file | SHA-256 |
| --- | --- |
| `Sources/lean.tar.gz` | `9631b4f020199e580ba86178cb56c6e9b09f690c2369a80dc4334aa93f49c7fc` |
| `Sources/remark.pdf` | `3fc97784b71ddd44ff8aa0a177e99622a1c61b13cfa843a0989ee4a7a0cfeb8d` |

The sources use Lean `v4.33.1` and Mathlib commit `0df444a360eaa60ab8c11dca51a86af692955474`. The node keeps the author’s files as local downloads. Git carries the [restoration script](Sources/fetch.py) and pins. The community mirror reports that the release was published without a license. [Release and verification instructions](https://github.com/leanprover-community/riemann-hypothesis)

On a fresh checkout, run these commands **from this node** with Python 3.11 or newer, curl, and tar. The first command also checks both hashes on an existing checkout. Extract into an empty destination to preserve any local work on the proof.

```powershell
python Sources/fetch.py
if ($LASTEXITCODE -ne 0) { throw 'Source verification failed' }
if (Test-Path -LiteralPath '.lake/lean') { throw 'Source tree already exists' }
New-Item -ItemType Directory -Force .lake | Out-Null
tar -xzf Sources/lean.tar.gz -C .lake
```

## Bibliography addendum for November 21, 2026

**[84]** Levent Alpöge (2026). Announcement of a proof of the Riemann hypothesis and Dirichlet GRH, developed with Claude. Four-page author’s note and accompanying 14-part Lean source archive, released November 20. [Original note and archive references](https://alpo.ge/remark.pdf)
