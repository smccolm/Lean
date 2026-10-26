# ramanujan-petersson Blueprint

Source file: `../ramanujan-petersson.md`
Project slug: `ramanujan-petersson`
Lean package: `RamanujanPetersson`

This blueprint is the informal companion for the Lean formalization. Treat the source paper as
read-only. Use this file to adapt exposition, split claims into Lean-sized pieces, and document
how the informal story maps onto declarations in the Lean project.

## Status

- Source imported: reviewed (2026-03-20)
- Lean first pass: completed (2026-03-20)
- Paper-faithful layer: completed (2026-03-20)
- Blueprint synced with Lean: updated (2026-03-20, paper-facing layer added)
- Paper patch review: updated (2026-03-20, paper-facing review items refreshed)

## Difference Policy

- `encoding-only`: Lean-specific definitions or APIs. Update this blueprint, not the source paper.
- `lemma-split`: Proof decomposition for formalization. Update this blueprint, not the source paper.
- `added-assumption`: Record in `paper_patch.md` for human review.
- `weakened-statement`: Record in `paper_patch.md` for human review.
- `gap-found`: Record in `paper_patch.md` for human review.

## Claim Ledger

The structured claim tracker lives in `claims.yaml`. Keep that file aligned with this blueprint and
with the generated Lean declarations.

## Adapted Outline

### 1. Core statements

- `RamanujanPetersson.rankTwoTraceBound` formalizes Lemma 5.1 from the source note.
- `RamanujanPetersson.theorem31_localCharpoly_witnessForm` formalizes a generated
  witness-form consequence of Theorem 3.1: given an explicit rank-two witness matrix
  with the stated local characteristic polynomial, one recovers the trace and
  determinant identities appearing in the theorem.
- `RamanujanPetersson.witnessSqueeze` packages the exact witness–squeeze step used in
  the proof of Theorem 2.1.
- `RamanujanPetersson.theorem41_purity_witnessForm` formalizes a generated
  witness-form version of Theorem 4.1: for a chosen complex realization of the
  two Frobenius eigenvalues, the purity conclusion is recorded directly as the
  pair of norm equalities used later in the proof of Theorem 2.1.
- `RamanujanPetersson.theorem21_witnessForm` formalizes a generated witness-form of
  Theorem 2.1: from explicit spectral data `αₚ, βₚ` with the required norms, one
  obtains the stated Ramanujan–Petersson inequality.
- `RamanujanPetersson.corollary53_primePowers_witnessForm` formalizes the prime-power
  clause of Corollary 5.3 in witness form: from an explicit coefficient expansion
  `a = ∑_{j=0}^m α^j β^(m-j)` and the same spectral norm data, one obtains the bound
  `‖a‖ ≤ (m + 1) * ((p : ℝ)^((k - 1 : ℝ) / 2))^m`.
- `RamanujanPetersson.corollary53_coprimeIndices_witnessForm` formalizes a generated
  witness form of the coprime-index clause of Corollary 5.3: from an explicit finite
  multiplicative decomposition of `aₙ` into prime-power factors together with witness
  identities for the divisor-count term and the power of `n`, one obtains
  `‖aₙ‖ ≤ d(n) * n^((k - 1) / 2)` in the chosen witness interface.
- `RamanujanPetersson.theorem31_paperFaithful` adds a paper-facing layer for Theorem 3.1:
  it packages the representation-level continuity, semisimplicity, unramifiedness,
  local characteristic polynomial, trace, and determinant data into the existential
  paper-shaped statement used downstream.
- `RamanujanPetersson.theorem41_paperFaithful` adds a paper-facing layer for Theorem 4.1:
  it packages algebraic Hecke roots in `Qbar` together with the chosen-embedding
  sum/product identities and the purity equalities for every embedding.
- `RamanujanPetersson.theorem21_paperFaithful` adds a paper-facing layer for Theorem 2.1:
  it deduces `‖aₚ‖ ≤ 2 p^((k-1)/2)` directly from the paper-facing `Qbar` root data.
- `RamanujanPetersson.corollary53_primePowers_paperFaithful` adds a paper-facing layer
  for the prime-power clause of Corollary 5.3 while still abstracting the coefficient
  formula as an input interface.
- `RamanujanPetersson.corollary53_coprimeIndices_paperFaithful` adds a paper-facing
  layer for the coprime-index clause of Corollary 5.3 while still abstracting the
  multiplicativity and divisor-arithmetic facts as input interfaces.
- The witness layer remains in the repo as an internal reduction/API layer. The new
  paper-facing layer is the preferred public Lean surface for comparing against the
  source note.

### 2. Definitions adapted for Lean

- The first pass works over `ℂ` directly and uses norms `‖·‖` rather than introducing
  modular-form or Galois-representation structures.
- `RamanujanPetersson.PaperInterfaces` introduces a paper-facing interface layer:
  `Qbar`, `QbarEmbedding`, `chosenEmbedding`, abstract Galois-representation predicates,
  and helper packages such as `HeckeRootPair`, `PurityInput`, `DeligneInput`,
  `PrimePowerInput`, and `CoprimeIndexInput`.
- The generated Theorem 3.1 witness form works with a concrete `2 × 2` complex matrix
  standing in for `ρ_{f,ℓ}(\mathrm{Frob}_p)` and records only the local
  characteristic-polynomial consequence.
- The paper's theorem is split into an abstract reduction step (`witnessSqueeze`) and
  the elementary inequality (`rankTwoTraceBound`).
- The generated theorem `theorem21_witnessForm` keeps the paper's final inequality but
  replaces the unformalized modular-form/Galois-representation input by explicit
  witness hypotheses on `αₚ` and `βₚ`.
- The generated theorem `theorem41_purity_witnessForm` keeps the paper's purity
  conclusion but replaces the algebraic-number / embedding quantification by a
  chosen complex witness pair `αₚ, βₚ` and direct norm equalities.
- The generated theorem `corollary53_primePowers_witnessForm` keeps the paper's
  prime-power inequality but replaces the unformalized Hecke/Euler-product input by
  an explicit coefficient-sum witness and spectral norm hypotheses.
- The generated theorem `corollary53_coprimeIndices_witnessForm` keeps the paper's
  coprime-index inequality but replaces the unformalized multiplicativity/divisor
  argument by an explicit finite witness decomposition and real identities for the
  divisor-count and `n^((k - 1) / 2)` factors.
- The paper-facing theorem layer keeps the source theorem names and shapes closer to
  the note, but it still treats Deligne's existence theorem, Euler-product identities,
  and multiplicativity infrastructure as abstract inputs rather than deriving them from
  a full modular-form formalization.

### 3. Proof decomposition

- Source Lemma 5.1 → `RamanujanPetersson.rankTwoTraceBound`
- Source Theorem 3.1, local characteristic-polynomial consequence →
  `RamanujanPetersson.theorem31_localCharpoly_witnessForm`
- Source Theorem 3.1, paper-facing existential packaging →
  `RamanujanPetersson.theorem31_paperFaithful`
- Source Theorem 2.1, final triangle-inequality step → `RamanujanPetersson.witnessSqueeze`
- Source Theorem 4.1, purity conclusion in chosen complex witness form →
  `RamanujanPetersson.theorem41_purity_witnessForm`
- Generated witness form of source Theorem 2.1 → `RamanujanPetersson.theorem21_witnessForm`
- Source Theorem 4.1, paper-facing `Qbar` packaging →
  `RamanujanPetersson.theorem41_paperFaithful`
- Source Theorem 2.1, paper-facing prime bound →
  `RamanujanPetersson.theorem21_paperFaithful`
- Source Corollary 5.3, prime-power coefficient estimate →
  `RamanujanPetersson.corollary53_primePowers_witnessForm`
- Source Corollary 5.3, prime-power clause in paper-facing interface →
  `RamanujanPetersson.corollary53_primePowers_paperFaithful`
- Source Corollary 5.3, coprime-index divisor-bound consequence →
  `RamanujanPetersson.corollary53_coprimeIndices_witnessForm`
- Source Corollary 5.3, coprime-index clause in paper-facing interface →
  `RamanujanPetersson.corollary53_coprimeIndices_paperFaithful`
- Remaining work for a fuller formalization:
  - derive the paper-facing interface layer from a full modular-form formalization;
  - connect Deligne existence/purity inputs to the paper-facing theorem layer;
  - replace the current explicit finite-product witnesses for the coprime-index
    divisor-bound clause of Corollary 5.3 by formal Euler-product / multiplicativity
    infrastructure.

### 4. Review queue

- `paper_patch.md` now treats the witness layer as internal scaffolding and tracks only
  the remaining paper-facing abstraction boundaries that may or may not need to be
  discharged by a fuller modular-form formalization.
- Next mathematical decision: whether the present paper-facing interface layer is the
  desired public endpoint, or whether the project should continue until Deligne input
  and Hecke multiplicativity are derived rather than abstractly packaged.
