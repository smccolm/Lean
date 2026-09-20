# Energy-powering source obstruction

Status: kernel-checked counterexample, permanently preserved. On 20 September
2026 the owner authorized a separate cardinality/energy repair; that full
replacement is now proved, completing corrected EPZAE-34. Its evidence is in
`Tao-Trudgian-Yang Energy Powering Repair.md`.
The printed source and this counterexample have not been altered. Only the
supporting-lemma contract changes; all advertised final outputs stay frozen.

## Exact source conflict

The pinned paper, arXiv `2501.16779v1`, Lemma 62 (`power-energy`), requires
output points of the five-dimensional energy region with `s' ≤ s/k`.
This requirement applies to each of its three potentially different
witnesses, not merely to a proposed stronger single witness.
The local source is
`Sources/TaoTrudgianYang-v1-source/Tao_Trudgian_Yang_v2.tex`, lines 1519–1529.
The [rendered paper](https://arxiv.org/html/2501.16779v1) and the
[live ANTEDB blueprint, Lemma 10.12](https://teorth.github.io/expdb/blueprint/energy-chapter.html)
were checked online and contain the same coordinate restriction.

The double zeta sum is the source's **unnormalized** quantity

```text
S(N,W) = Σ(t,u ∈ W) |Σ(n ∈ [N,2N]) n^(-i(t-u))|².
```

No normalization, endpoint convention, or multiplicity convention has been
changed to produce this obstruction.

## Concrete counterexample

For each integer `N > 1`, take coefficients all equal to one, `W = {0}`,
`T = N²`, `V = N^(3/4)`, and ordinate interval `[0,T]`. This is a genuine
large-value pattern: at zero the polynomial has value `N+1 ≥ V`.
Its cardinality and additive energy are both one, while

```text
S(N,{0}) = (N+1)².
```

Consequently `(3/4, 2, 0, 0, 2)` lies in the energy region. The proof checks
every positive approximation radius and every arbitrarily large scale
threshold; it is not just a finite numerical example.

Every energy-region point satisfies `ρ + 2 ≤ s`, because the diagonal
terms contribute at least `|W| N²`. Since `ρ ≥ 0`, every such point has
`s ≥ 2`. With `k = 2`, the printed lemma demands an output with `s' ≤ 1`.
There is no such point at all, regardless of its other coordinates.

## Lean evidence

`Extension/TaoTrudgianYang2025/EnergyPoweringObstruction.lean` proves:

- `singletonLargeValuePattern_doubleZetaSum` — exact singleton sum;
- `singleton_mem_largeValueEnergyRegion` — region membership, more generally
  for every `1/2 ≤ σ ≤ 1` and `τ ≥ 0`;
- `InLargeValueEnergyRegion.two_le_s` — the universal lower bound;
- `energyPowering_source_counterexample` — the explicit input and failure
  of even the single-output consequence of the source lemma.

All names are in namespace `TaoTrudgianYang2025`. The module is imported by
the root library, explicitly included in the principal runner inventory,
and covered by named axiom audits and semantic regressions. Verification
details are recorded in the reproduction manifest.

## Interpretation and scope

The source proof partitions the ordinate set after replacing the polynomial
scale `N` by a scale of order `N^k`. Partition estimates at fixed `N` do not
control `S(N',W')` at that new scale. The singleton example makes this
distinction explicit: its sum grows like `(N')²`, not like `N²`.
This identifies the failed inference; it does **not** establish a corrected
transformation law. Merely replacing `s` by `s-2` in the statement is not
a proved repair.

The live blueprint still contains the printed claim. No correction was
located in the arXiv version history or the author's announcement/comments
checked during this investigation. This is not an exhaustive assertion
that no erratum exists anywhere. No upstream issue or message was posted.

This counterexample refutes the required supporting lemma, not the four
new exponent pairs, the zero-density outputs, or the nine `Add-est`
clauses. The new proof of `zeroe-from-large` does not use the false lemma.
The bounded-range corollary remains open and must now consume the proved
two-witness repair; it must not inherit the disproved fifth-coordinate restriction.

Proving the original EPZAE-34 statement literally is impossible. The owner
has now authorized replacing it by two cardinality/energy witnesses, with
independent existential fifth coordinates and no `s/k` restriction. The
repair's general analytic proof is `correctedCardinalityEnergyPowering`.
Retain this counterexample,
preserve the original source and final output contracts, and make no
paper-completion claim. Authorization is no longer a blocker.
