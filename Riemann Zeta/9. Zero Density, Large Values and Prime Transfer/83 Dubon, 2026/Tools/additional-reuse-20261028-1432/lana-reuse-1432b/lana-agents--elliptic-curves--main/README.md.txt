# Elliptic curves

A [Lean 4](https://leanprover.github.io/) formalisation project on the arithmetic
of elliptic curves, built on top of [Mathlib](https://github.com/leanprover-community/mathlib4)
(Lean `v4.32.0`, Mathlib `v4.32.0`; no other dependencies).

License: Apache 2.0 (see LICENSE)

## Scope

The aim of this repository is to formalise results about the reduction theory of
elliptic curves over local and global fields, following Silverman's
*The Arithmetic of Elliptic Curves* (GTM 106). The project builds on Mathlib's
existing theory of Weierstrass and elliptic curves
(`Mathlib.AlgebraicGeometry.EllipticCurve.*`).

The two headline targets are:

* **Semi-stable reduction** of elliptic curves.
* The **Néron–Ogg–Shafarevich criterion**: an elliptic curve has good reduction
  if and only if its Tate module is unramified.

Neither is finished. The *good ⇒ unramified* direction of Néron–Ogg–Shafarevich is
proved for an abstract complete DVR; the converse, and the classical local-field
packaging in which inertia is realised inside `Gal(Kᵘʳ/K)`, are open. For semi-stable
reduction, the reduction-type trichotomy, the `j`-invariant criteria and the
potential-good / potential-multiplicative dichotomy are in place (`Reduction/`), but
the theorem itself is not assembled.

### Status

Measured at `edcab20` (2026-10-07). The library is **`sorry`-free and axiom-free**:
`git grep -nw sorry -- '*.lean'` finds the word only in prose (*"sorry-free"* and the
like), never as a tactic, and no `axiom` declaration exists. `EllipticCurves.lean` imports
all 480 modules under `EllipticCurves/`, so `lake build` checks every one. Everything below
is therefore **proved under the hypotheses in its signature**; the hypotheses, not a
missing proof, are what "conditional" means on this page. The recurring ones are an
algebraically closed base field `F` and `(2 : F) ≠ 0`.

### What is formalised

The main results, by directory. Names are unqualified; all live in the
`WeierstrassCurve` or `WeierstrassCurve.Affine` namespace (some Tate-module results in
`WeierstrassCurve.Affine.tateModule`).

* **Reduction over a discrete valuation ring** (`Reduction/`).
  * Néron–Ogg–Shafarevich, good ⇒ unramified (Silverman VII.7.1),
    `neronOggShafarevich_galoisRep_eq_one` (ℓ-adic) and
    `neronOggShafarevich_galoisRepMod_eq_one` (mod `ℓ`), in `NeronOggShafarevich.lean`:
    for a valuation subring `A ⊆ L` that is an adically complete DVR, if `W'⁄L` has
    good reduction over `A` and `ℓ` is invertible in `A`, then `ρ_ℓ` (resp. `ρ̄_ℓ`) is
    trivial on `A.inertiaSubgroup K`. **Open:** the converse, and the local-field form.
  * The kernel of reduction is the formal group: `E₁AddEquiv : E₁(K) ≃+ Ê(𝔪)` over a
    complete DVR (Silverman VII.2.2); injectivity of reduction on prime-to-`p` torsion,
    `reduction_injOn_torsion`.
  * Reduction types: `hasGoodReduction_trichotomy`; good reduction from `v(Δ) = 0`,
    `hasGoodReduction_of_valuation_Δ_eq_one`; the `j`-invariant obstructions to
    potentially good and potentially multiplicative reduction,
    `isIntegral_j_of_hasGoodReduction_baseChange_over` and
    `not_isIntegral_j_of_hasMultiplicativeReduction_baseChange_over`.
    **Open:** the semi-stable reduction theorem.
* **The Weierstrass formal group** (`FormalGroup/`) — `formalGroup : FormalGroup R` over
  an arbitrary commutative ring, with associativity `formalGroupZW_assoc_commRing`;
  the formal logarithm and its additivity `formalLog_subst_formalGroupZW`; the
  exponential and the multiplication-by-`n` series.
* **Torsion** (`Torsion/`, `DivisionPolynomial/`), over an algebraically closed `F` with
  `(2 : F) ≠ 0` and `(n : F) ≠ 0`: `#E[n] = n²` (`card_torsion_eq_sq`) and
  `E[n] ≃+ (ℤ/nℤ)²` (`nonempty_torsion_addEquiv`), both in `StructureGeneral.lean`;
  off `F̄`, the structure follows from the count alone (`nonempty_torsion_addEquiv_of_card`).
  Finiteness of `E[n]`, with no closure hypothesis: `finite_torsion_of_charZero` and
  `finite_torsion_of_not_dvd_charP` (`XSupport.lean`). Recent work removes
  `(2 : F) ≠ 0` from the division-polynomial layer, e.g. `n • P = 0 ↔ ψₙ(P) = 0` for a
  point that is not `2`-torsion, `nsmul_eq_zero_iff_ψ_evalEval_eq_zero'`
  (`NsmulOrderCharFree.lean`).
* **The Tate module and Galois representations** (`TateModule/`), at every prime
  `ℓ` with `(2 : F) ≠ 0`, `(ℓ : F) ≠ 0`, `F` algebraically closed:
  `T_ℓE ≅ ℤ_ℓ²` (`nonempty_tateModuleEquivProd_of_natCast_ne_zero`,
  `free_tateModule_of_natCast_ne_zero`, `FreeGeneral.lean`); the continuous matrix
  representation `ρ_ℓ : G → GL₂(ℤ_ℓ)` (`exists_continuous_galoisRepMatrix_of_natCast_ne_zero`)
  and the mod-`n` one (`exists_galoisRepModMatrix_of_natCast_ne_zero`). In characteristic
  `2` the case `ℓ = 3` is done separately
  (`exists_continuous_galoisRepMatrix_three_of_two_eq_zero`, `MatrixRepThreeCharTwo.lean`).
  **Not described:** the image of `ρ_ℓ` (Serre's open image theorem is not attempted).
* **The Weil pairing** `eₙ : E[n] × E[n] → μₙ` (`FunctionField/WeilPairing*.lean`), built
  on the function field `F(W)`, its places and divisors (`FunctionField/`). Over an
  algebraically closed `F` with `(2 : F) ≠ 0` and `((n : ℤ) : F) ≠ 0`, every property of
  Silverman III.8.1 is proved: the pullback-principality input
  (`exists_gS_of_ne_zero_of_isAlgClosed`), bilinearity, the alternating property
  (`exists_weilPairingElt_self_eq_one_of_hprin_n_of_algClosed`), antisymmetry
  (`exists_weilPairingElt_eq_inv_n_of_isAlgClosed`), Galois equivariance, perfectness
  (`bijective_weilPairingNHom`, `weilPairingNEquiv`) and index compatibility
  (`weilPairingEltN_mul_index_nsmul_right`). Off `F̄` the principality input is a
  hypothesis (`hprin`) discharged in special cases, e.g. at a general `n` from Galois
  data (`exists_gS_n_of_galois`).
* **The determinant is the cyclotomic character**: `galoisDetMod n = χₙ`
  (`galoisDetMod_n_eq_galoisModularCyclotomicChar`) and ℓ-adically `det ρ_{E,ℓ} = χ_ℓ`
  (`galoisDet_eq_galoisCyclotomicChar`, `TateDeterminantCyclotomic.lean`), same hypotheses.
* Supporting Galois-theoretic material (`Galois/`) and the Newton-polygon dichotomy for a
  Weierstrass equation (`NewtonPolygon.lean`).

Module docstrings carry the precise hypotheses, scope notes and non-vacuity certificates
(`Fixtures.lean`); the rules for those docstrings are `## Docstring conventions` below.

### Use in the IUT programme

[`lana-agents/iut`](https://github.com/lana-agents/iut) depends on this repository only
transitively, through
[`tempered-fundamental-groups`](https://github.com/lana-agents/tempered-fundamental-groups),
which pins `bebec3f` (2026-09-28, an ancestor of `main`). Its one consumer is
`TemperedFundamentalGroups/Orbicurve/GeomModel.lean`, which imports
`EllipticCurves.Torsion.XSupport` and uses `finite_torsion_of_charZero` and
`finite_torsion_of_not_dvd_charP` to show that the removed set `E[ℓ] + M` of the model
orbicurves is finite.

## Layout

Measured at commit `edcab20`; the counts drift, the directory structure does not.

```
EllipticCurves.lean          -- root module, imports the whole library
EllipticCurves/
├── Basic.lean               -- re-exports two Mathlib modules; only EllipticCurves.lean imports it
├── Fixtures.lean            -- the certificate curves the non-vacuity blocks run on
├── NewtonPolygon.lean       -- the slope-3/2 dichotomy at a pole of a Weierstrass equation
├── UniversalCurve.lean      -- the universal Weierstrass curve and the specialisation map
├── DivisionPolynomial/      --   2 files  division polynomials
├── FormalGroup/             --  57 files  the Weierstrass formal group law and Ê(𝔪)
├── FunctionField/           -- 208 files  F(W), its places and divisors; the Weil pairing
├── Galois/                  --   4 files  cyclotomic character, unramified Galois modules
├── Reduction/               --  67 files  reduction over a DVR; reduction types; NOS
├── TateModule/              --  48 files  T_ℓE and the ℓ-adic representation ρ_ℓ
└── Torsion/                 --  90 files  E[n] and the torsion structure theorem
```

The seven directory counts sum to **476**; with the four top-level modules that is **480**
under `EllipticCurves/`, and **481** tree-wide once the root module is counted.
`FunctionField/` is flat rather than nested; within it the file-name prefixes
`MulByTwo`/`MulByThree`/`MulByN`, `Translation`, `Place`, `Divisor` and `WeilPairing` are
what group the material.

New files should be added under `EllipticCurves/` and imported from the root
`EllipticCurves.lean` module (kept in sync with `lake exe mk_all`).

The sections from here on are the project's contributor rulebook (docstring conventions,
linting, the merge gate, reviewing); Lean docstrings and `.orchestra/validation.sh` cite
them by heading.

## Docstring conventions

### Reach clauses

A **reach clause** is a docstring phrase that says how far a named declaration or a named
layer goes — *"at every `3`-smooth `n`"*, *"at every `n` with `(n : F) ≠ 0`"*, *"the same at
every index"*. They are what a reader consults instead of the signature, and on this
development they are the one kind of prose that has repeatedly gone stale in a way no build
can see.

**A reach clause names every hypothesis of the statement it describes, or it names none.**
The defect is the *proper non-empty subset*: naming the index condition and silently dropping
`(2 : F) ≠ 0` reads as a complete hypothesis list, because a clause that lists one condition
looks like a clause that lists them all. Concretely:

```
-- wrong: `card_torsion_eq_sq` also takes `(2 : F) ≠ 0`
`card_torsion_eq_sq` is `#E[n] = n²` at every `n` with `(n : F) ≠ 0`

-- right
`card_torsion_eq_sq` is `#E[n] = n²` at every `n` with `(2 : F) ≠ 0` and `(n : F) ≠ 0`

-- also right: no `with` clause at all, deferring to the signature
`card_torsion_eq_sq` is `#E[n] = n²` at a general index
```

**Some phrases look like reach clauses and are not**, and their number is deliberately not given
(`#1678`), on the precedent `### Scope of the rules above` sets for its own list. Each has been
flagged, triaged and cleared more than once, so the discriminators are written down here rather
than re-derived each round. ⚠️ This read *"**Two phrases look like reach clauses and are not.**
Both have been flagged, triaged and cleared more than once"* (`f1d1473`, `#1569`, PR #620),
true from that commit until the third discriminator below was added — a numeral standing over a
list is falsified by whatever next extends the list, which that section states in terms and
answered the same way. ⚠️ **Both numeral-bearing words are quoted, and they are two words rather
than one**: *"Two"* and *"Both"* were written by one commit and either alone would leave the
other with no account of why it changed. The ordinal reference below — *"The second
discriminator"* — is untouched, because it names a **position** and not a count. They are:

* **A phrase that says which indices the statement is a claim *about* is part of naming the
  theorem, not a hypothesis list**; a phrase that enumerates the conditions under which the
  statement holds is. *"Away from the multiples of the least vanishing index, `ψ` does not
  vanish"* (`ψ_evalEval_ne_zero_of_not_dvd`) is the `∀ m, ¬(d ∣ m)` **inside** the conclusion, not
  a restriction on when the theorem applies. Same for `ψ_evalEval_eq_zero_of_dvd`.

  ⚠️ **`divT_add_mul_of_not_dvd` and `divY_add_mul_of_not_dvd` are the same register with that
  quantifier telescoped, and this is why the discriminator is not syntactic.** They bind
  `(j : ℕ) (hj : ¬ ((e + 3) ∣ j))` **explicitly** and conclude `∀ q : ℕ, …`; the conclusion's own
  quantifier is the `∀ q` the headline calls *"at every multiple of the period"*, while the phrase
  cleared here — *"off the multiples of `d`"* — is a binder. A rule keyed on which side of the `:`
  the condition sits would clear two of these four sites and convict the other two.

  ⚠️ **And no sharper syntactic rule is available**, so do not write one. `card_torsion_pow_of_odd`
  telescopes identically — `{p : ℕ} (hodd : Odd p) (hp : (p : F) ≠ 0)` *is* `∀ p, Odd p → …` — and
  *"at an odd `p`"* **was** a defect (PR #619). The test that does separate them is to **delete the
  phrase and read what is left.** If the remainder is a statement of the same kind, the phrase was a
  restriction on when it applies and is a reach clause: *"`#E[pᵏ] = (pᵏ)²`"* stands perfectly well
  without *"at an odd `p`"*, and `card_torsion_eq_sq` is that statement. If the remainder is no
  longer the theorem, the phrase was part of the predicate: *"`ψ` does not vanish"* without *"away
  from the multiples of the least vanishing index"* is contradicted by the declaration immediately
  below it, `ψ_evalEval_eq_zero_of_dvd`, and *"the predicted `ψ₂`-value is periodic with period
  `d`"* without *"off the multiples of `d`"* is not what `divT_add_mul_of_not_dvd` proves —
  `divT_add_of_not_dvd`, the single step it iterates, asks `¬ (d ∣ j)` at every rung.

  ⚠️ **The test asks whether the remainder is a claim of the same kind, not whether it is still
  true.** **Every** reach clause leaves something false when it is deleted — that is what *"the
  conditions under which the statement holds"* means — so *"the remainder is not true"* holds of
  the entire class and is never on its own a reason to call a phrase part of the predicate. Read
  the second half that way and it clears `card_torsion_pow_of_odd`, the declaration the paragraph
  above opens by convicting: `#E[pᵏ] = (pᵏ)²` with nothing attached is false in characteristic `p`
  too, and is nonetheless what *"stands perfectly well"* means. Both halves are already carrying
  that distinction in their citations — `card_torsion_eq_sq` **is** `#E[pᵏ] = (pᵏ)²` under a
  different condition, while `ψ_evalEval_eq_zero_of_dvd` proves the **opposite** on exactly the set
  *"away from the multiples of the least vanishing index"* removes — so read what the tree proves
  beside a row before deleting anything in its headline.

  ⚠️ **On a row this bullet does not already decide by name, the truth-reading inverts, and it
  reached a confirmed proper-subset defect.** *"as soon as `e_2(P, T) ≠ 1`"*
  (`intCast_eq_zero_of_zsmul_add_zsmul_eq_zero_two`,
  `EllipticCurves.FunctionField.WeilPairingDeterminant`) also leaves something false when deleted,
  so a truth-reading calls it predicate; the headline was then left with no reach clause at all and
  the row landed **cleared** on the *"or it names none"* branch. It is not the case of the four
  sites above: nothing in that file proves anything on the set the phrase removes, and *"`P` and
  `T` are `ℤ/2`-independent"* is the same claim about the same `P` and `T` with the phrase saying
  when it holds. So it is a reach clause; the statement also binds `(2 : F) ≠ 0`, and the headline
  **named it nowhere**. `…_three` is the identical shape. Neither was repaired by this clause — it
  only stopped the test from clearing them, and PR #631 (`#1576`) then repaired both: the headlines
  now read *"over a field with `(2 : F) ≠ 0`, as soon as `e_2(P, T) ≠ 1`"* and *"over a field with
  `(2 : F) ≠ 0` and `(3 : F) ≠ 0`, as soon as `e_3(P, T) ≠ 1`"*, so the *"or it names none"*
  escape went with them. ⚠️ **The classification is what this paragraph is for and the repair
  does not touch it**: the phrase is a reach clause because of what the file proves beside it, not
  because the row was defective, and a row repaired on that reading is evidence the reading was
  right.
  ⚠️ **A clause that restricts the POINT or the PLACE rather than the index is decided by this same
  test, and the answer is not uniform across a case split** (`#1728`). *"at an affine point that is
  not `n`-torsion"*, *"at every affine `P` that is not `n`-torsion"*, *"at every affine `n`-torsion
  point"* and *"every affine `n`-torsion place"* are one clause in four wordings, carried by the
  **six** rows of `EllipticCurves.FunctionField.MulByNFibre`'s *"### The contraction at a rational
  point, at every `n` with `((n : ℤ) : F) ≠ 0`"* section that carry one at all — ⚠️ **not** the
  shorter *"### The contraction at a rational point"* section above it, which is a different
  four-row section and is what a grep for the short title finds first —
  `ord_mulByNCoordHom_XClass_pos`, `ord_mulByNCoordHom_YClass_pos`,
  `ord_mulByNEndo_genX_nonneg`, `comapProjPointN_pointClosedPoint_of_ΨSq_ne_zero`,
  `ord_mulByNEndo_genX_neg` and `comapProjPointN_pointClosedPoint_of_eval_ΨSq_eq_zero` — and the
  test sorts them **five to one**. Ask what the tree proves with the clause struck out:
  * **Some declaration states the same conclusion with the case hypothesis gone.** Then the split
    is an artefact of the proof, the clause says when *this row* applies, and it is a reach clause
    owing the rest of the list. `comapProjPointN_pointClosedPoint_of_ΨSq_ne_zero` is the one row
    here on this side: strike its clause and what is left — *"`[n]` on places is `[n]` on points"* —
    is `comapProjPointN_projPointOfPoint_of_ne_zero`, the assembly that section is built around,
    whose docstring names this row as one of the three **branches** it puts together.
  * **No declaration does.** Then the clause is part of the predicate and the headline is on the
    *"or it names none"* branch. Either a sibling proves the **opposite** on exactly the set the
    clause removes — `ord_mulByNEndo_genX_nonneg` (*"`x ∘ [n]` is regular …"*) and
    `ord_mulByNEndo_genX_neg` (*"… has a pole …"*) are the `ψ_evalEval_ne_zero_of_not_dvd` /
    `ψ_evalEval_eq_zero_of_dvd` pair above transposed, eighty lines apart and split on the same
    `ΨSqₙ(x) ≠ 0`, and `comapProjPointN_pointClosedPoint_of_eval_ΨSq_eq_zero` is contradicted on
    its own removed set by the branch beside it — or the conclusion is not **formable** at all off
    the clause, which is the
    two `ord_mulByNCoordHom_*_pos` rows: `x(n • P)` is `Φₙ(x)/ΨSqₙ(x)`, and at an `n`-torsion `P`
    there is nothing for the headline to say vanishes.

  ⚠️ **Decide this only when you are about to CLEAR a row, never when you are about to complete
  one.** An insertion is branch-neutral: it moves a headline from *"or it names none"* to *"names
  every hypothesis"*, and both branches are compliant, so appending the missing conditions is right
  whichever way the call goes. That is what makes `fddba5c`'s four `ord_*` repairs (`#1664`,
  PR #684) correct under the ruling above even though it puts all four on the predicate side, and
  it is why nothing here reopens them — `### Scope of the rules above`'s *"clearing this one would
  have left the block with rows in two registers"* is an independent ground for them in any case. A
  **clearance** is the one move that turns on the headline having no reach clause at all, and it is
  the only move that has to pay for this call.

  ⚠️ **The `n = 2` and `n = 3` ancestors of the convicted row were convicted with it, and are named
  rather than counted.** `comapProjPointTwo_pointClosedPoint`
  (`EllipticCurves.FunctionField.MulByTwoFibreAffine`) and `comapProjPointThree_pointClosedPoint`
  (`EllipticCurves.FunctionField.MulByThreeFibre`) carry the same clause on the same generic
  branch — each is the generic case of an assembly that states the conclusion unrestricted — and
  all three headlines now name their conditions (`#1735`): *"…at an affine non-`2`-torsion point,
  with `(2 : F) ≠ 0`"*, *"…at an affine non-`3`-torsion point, with `(2 : F) ≠ 0` and
  `(3 : F) ≠ 0`"*, and at general `n` the wording of the four `ord_*` rows beside it.
  ⚠️ This read *"neither headline names `h2`, nor, at `n = 3`, `h3`"*, with a second ⚠️ adding that
  both answered it in a *"No hypothesis on `F` beyond …"* sentence **lower in the same docstring**,
  which `### Scope of the rules above` rules does not repair a headline (`0a1049f`, `#1728`,
  PR #688) — true when written and false from the repair on both counts, since those two sentences
  were re-scoped to the `[W.IsElliptic]` contrast they also carry, which is the half no headline
  here states. ⚠️ **The conviction itself is not retired and is what the repair discharged**: an
  insertion is branch-neutral, so a repaired row is evidence for the reading that convicted it and
  never against it, which is what this bullet already says in terms of
  `intCast_eq_zero_of_zsmul_add_zsmul_eq_zero_two` and `…_three` above. Their
  two `_of_eval_…_eq_zero` siblings are cleared with `MulByNFibre`'s. ⚠️ **The tree-wide population
  of point-and-place clauses is much larger and is deliberately not counted here**, on this
  section's own precedent: a first-pass recogniser returns over a hundred headlines and is already
  known to miss rows on a backtick boundary, so measuring it is `#1137`'s, and the three convicted
  rows named above — one at general `n`, one at `n = 2`, one at `n = 3` — were filed with it as
  `#1735` rather than swept here, and repaired under that issue.
* **A phrase about a fixed numeral is a remark, not a reach clause.** *"`#E[10] = 100`, at an index
  that is neither odd nor `3`-smooth"* (`card_torsion_ten`) cannot be a hypothesis list, because
  `10` is not quantified and there is nothing for a condition to range over. Same for
  `nonempty_torsionThirtySix_addEquiv`, `card_torsion_four`, `nonempty_torsionFour_addEquiv` and
  `nonempty_torsionTwelve_addEquiv`.
* **A phrase that says which declaration this one generalises is provenance, not a reach clause**
  (`#1678`). *"The general-`n` form of `X`"* names a **lineage** — this declaration is the
  general-`n` layer's version of the numeral-indexed `X` — and answers *which merged declaration
  this generalises*, not *which indices this reaches*.
  ⚠️ **The deletion test above does not decide this class, which is why it needs a bullet of its
  own.** Delete *"the general-`n` form of `mulByTwoCoordHom_injective`"* from
  `mulByNCoordHom_injective`'s headline and the remainder — *"Dominance for `mulByNCoordHom`"* —
  is a claim of the same kind, so the test returns **reach clause**, wrongly. That test sorts
  *predicate* from *reach*, and provenance is a third thing neither of its branches has room for.
  What does decide it is `### Scope of the rules above`'s *"**The subject decides, not the
  string**"*: a reach clause's subject is this declaration and its predicate is a set of indices,
  while this phrase's subject is the **pair** of declarations and its predicate is a relation
  between them.
  ⚠️ **The wide reading is refuted by the tree rather than merely unattractive.** Measured at
  `8d31527` with a nesting-aware `/-`-depth extractor over every `EllipticCurves/**/*.lean`,
  whitespace-normalised and `**`-stripped, matching ``the general-`n` forms? of``
  **case-insensitively** — ⚠️ **the case matters and is not a detail**: this tree writes both
  *"The general-`n` form of"* at the head of a headline and *"the general-`n` form of"* mid
  sentence, and either anchoring alone splits the class rather than measuring it — lowercase
  `the` returns **23**, capital `The` **33**, and only the two together are the 56. The phrase
  occurs **56** times — **43** in `/--` blocks, **13** in `/-!` module blocks — and
  **29** of the 43 head a declaration binding a condition on the index: `n ≠ 0`, `(n : F) ≠ 0`,
  `((n : ℤ) : F) ≠ 0`, `3`-smoothness of `n`, or the instance `[NeZero n]` — **28** if that
  instance is not counted, and one of the 29 (`divisorProj_mulByNEndoOfAlgClosed`) takes `n ≠ 0`
  from a `variable` line and not from its own binder list, so the count is over the binders **in
  scope** and not over the ones written at the declaration.
  ⚠️ **The phrase is matched anywhere in a block; the headline cut defined further down this
  bullet is applied to the matched blocks afterwards, and only for the range test.** The corpus
  line above read *"in `/--` headlines"* where it now reads *"in `/--` blocks"* (`7f0a162`,
  `#1678`, PR #685) — **false** under this bullet's own definition of *headline*, which is the cut
  prefix and not the block. Matched against the cut prefix the figure is **5**, not **43**: this
  tree writes the phrase in a *later* sentence of a docstring — *"The general-`n` form of
  `ord_mulByTwoEndo_genX_nonneg`."* — and almost never in a headline. ⚠️ **Only the noun was
  wrong and no figure moves**, which is why this is a correction in place; it is quoted rather
  than silently fixed because a reader who implements the line as written gets **5** rows, a
  binder count of **4** and a **one**-row witness slot, and the three names printed under the slot
  are the only thing that tells them to try again.
  ⚠️ **Both quotations in the case split above are singular and the pattern is not — the `s?` is
  load-bearing and it carries five rows.** *"the general-`n` forms of"* occurs **5** times, all
  lowercase and all in `/-!` blocks, so the singular alone returns **51** splitting **43 / 8**, and
  puts **18** under lowercase `the` against the published **23**. ⚠️ **The 43 does not move on that
  read**, which is why the binder **29 / 28**, the range test and the witness slot are all untouched
  by it. This clause is here because the misread happened: `#1749` was filed against this paragraph
  proposing the **23** be corrected to **18**, read off the two singular quotations rather than off
  the pattern two lines above them.
  ⚠️ **The hyphen is literal, and one site writes the phrase without it.** `nsmul_genericPoint_eq`
  (`EllipticCurves.FunctionField.MulByNPullback`) says *"This is the general `n` form of the merged
  `genericPoint_add_self`"* in a later sentence, and it is **outside** the corpus as published.
  Folding it in moves **56 → 57** and **43 → 44** and adds one row to the *states none* side of the
  range test — **30 / 13 → 30 / 14** at `3e1bef2` — and moves **nothing else**: the binder
  **29 / 28** and the slot are unchanged and membership-identical at that sha and at head, because
  its only hypothesis about `n` is the non-constancy the paragraph below rules is not a condition on
  the index. **Decided rather than left open** (`#1749`): the corpus stays hyphenated, so every
  figure dated to `3e1bef2` keeps its meaning, and the cost of the other choice is on the page.
  ⚠️ **The non-constancy hypothesis is not a condition on the index, and the other 14 rows are
  not convicted by carrying one.** Thirteen of them bind
  `Transcendental F (n • genericPoint …).xCoord` and nothing else about `n` — three of those add
  an `n`-torsion condition on a *point*, which is a condition on the pair and not on the index —
  and `fixedFieldN` binds nothing about the index at all.
  `EllipticCurves.FunctionField.WeilPairingGaloisRootN` rules exactly this of its own brick, whose
  *"at every `n`"* stands beside the non-constancy and is true. ⚠️ **A binder NAME decides
  nothing**: this tree writes the non-constancy as `hn` as readily as `hT` or `h`, so a recogniser
  keyed on the name `hn` sorts `functionFieldMap_mulByNEndo` and `mulByNCoordHom_injective` — the
  same hypothesis over the same reach, one named `hn` and one `hT` — onto opposite sides, and
  convicts the brick (`#1678`). Read as a reach clause the phrase tells the reader those 29 reach
  *the general* indices, which is **false** rather than partial, and this
  section treats false the more severely of the two. **29** of the 43 also state an index range in
  the same headline — ⚠️ **a different 29**: this one is measured on headline text and the first
  on the binders in scope, and neither set contains the other. ⚠️ **Only one direction of that is
  witnessed by name here, and the asymmetry is the point**: **four** rows state a range and bind no
  index condition — `galoisFunctionField_mulByNEndo`, `functionFieldMap_mulByNEndo`,
  `weilPairingElt_divisorSlot_add_n` and `weilPairingElt_pow_eq_one_of_gS_n_torsion` — and stating
  a range a signature does not ask for is nobody's sweep, so those four are durable — both
  figures on the recogniser published below. The other
  direction is the **witness slot** measured further down this bullet, and it is named there under
  a date rather than here under a present tense (`#1728`) —
  **24** of them a range
  strictly narrower than every `n`, so the wide
  reading has those headlines answering one question twice and incompatibly:
  `torsionNMulGaloisEquiv_of_ne_zero` (`EllipticCurves.FunctionField.MulByNGaloisGroup`) reads
  *"at every `n` with `(2 : F) ≠ 0` and `(n : F) ≠ 0` … the general-`n` form of
  `torsionNMulGaloisEquiv`"*, and `card_torsionNMul`
  (`EllipticCurves.FunctionField.TranslationActionN`) *"at every `3`-smooth `n ≠ 0` with
  `(2 : F) ≠ 0` and `(3 : F) ≠ 0` … the general-`n` form of `card_torsionThreeMul`"*.
  ⚠️ **That second witness used to be `ord_mulByNEndo_genX_nonneg`, and `#1664` falsified it
  twenty-three minutes after this bullet landed** (`#1725`). It read
  *"`ord_mulByNEndo_genX_nonneg` binds `((n : ℤ) : F) ≠ 0` and states none"* (`7f0a162`, `#1678`,
  PR #685); that row's headline now names `(2 : F) ≠ 0` and `((n : ℤ) : F) ≠ 0`, as does
  `ord_mulByNEndo_genX_neg` beside it, so both state what they bind and neither witnesses anything.
  ⚠️ **A dated census does not owe a re-measure and this parenthetical did, and the difference is
  the discriminator worth keeping**: `## Layout`'s *"the counts drift, the directory structure does
  not"* and `### Module-block bullets`' *"Date the answer"* say a **count** under a named head is
  not falsified by a later head. A **present-tense claim about a named declaration** is not a count
  — a reader checks it against the declaration, not against the head — so it is falsified, and
  `### Retired claims` binds on it and not on the figures beside it.
  ⚠️ **The `29` and the `24` are a triage pair and not a measurement**, on the precedent
  `### Module-block bullets` sets two sections down for its own `59`: the recogniser for them is
  the one figure in this bullet never written out, and four implementations of it return **27**,
  **28**, **29** and **30** over the same 43 rows, differing on the phrase list and above all on
  whether a range over *points* — *"at every affine `n`-torsion point"*, *"at an affine point
  that is not `n`-torsion"* — counts as a range over the index. **The two rows named above have
  since crossed onto both sides.** They corroborate and are not the argument: the two examples
  are, and both are still true at head.
  ⚠️ **The witness slot — the rows that bind an index condition and state no range — is published
  with its recogniser** (`#1658`, `#1728`), because that is the one figure the pair above never
  wrote out. Measured at `3e1bef2` over the same 43 rows and the same extractor: a headline states
  an index range if it either **(a)** carries an index-quantifier phrase — ``at every `n` `` (19),
  ``at every `3`-smooth `n ≠ 0` `` (6), *"at every index"* (1), ``at general `n` `` (1),
  ``for every `n ≠ 0` `` (1), and *"at a general index"* / *"at an odd `p`"*, which are declared and
  match nothing in this corpus (0) — or **(b)** carries an inline code span constraining the
  index — `` `n ≠ 0` ``, `` `(n : F) ≠ 0` ``, `` `((n : ℤ) : F) ≠ 0` ``, `` `3`-smooth ``. Headline
  means the block text `**`-stripped and whitespace-normalised, cut at the first `.` followed by
  optional bold, code-span, bracket or quote marks and a space, or at the first ⚠️, whichever comes
  first. That returns **30** stating a range and **13** not — and it is *"or"*, not *"and"*, which
  is where two implementations part: (a) alone returns 28 and
  (b) alone 25, which is the spread the marking above is for and the reason a bare numeral was
  never going to settle it. ⚠️ **Match the (a) phrases as they are written here, condition and
  all.** The corpus writes the index span with its own condition inside it, so the normalised forms
  ``at every `3`-smooth `n` `` and ``for every `n` `` match **zero** rows and drop (a) to **21** —
  whether a quantifier phrase's index span may carry a condition is a **fifth** axis of the spread,
  and it is the one that moves the slot: an (a)-only recogniser reading the normalised forms puts
  **12** rows in it, against the **5** an (a)-only recogniser reading these forms does and the
  **3** the full test below finds.
  ⚠️ **The trailing space inside those (a) spans is code-span syntax and not part of the phrase**,
  and it is the second way to fail to reproduce a correct figure from correct text. A code span
  whose content ends in a backtick needs that space to close, so ``at every `n` `` cannot be
  written without it — and CommonMark does not strip it, because stripping needs a space at
  **both** ends, so it renders as though it were part of the phrase. It is not: the corpus ends
  that phrase with a full stop twice and a comma once, and requiring the space literally drops
  (a) from **28** to **25**. Match the phrases with surrounding whitespace normalised away.
  ⚠️ **The slot has three rows at `3e1bef2`, and a dated measurement may name what a
  present-tense parenthetical may not:**
  * `comapProjPointN_pointClosedPoint_of_ΨSq_ne_zero`
    (`EllipticCurves.FunctionField.MulByNFibre`) — **short**, convicted by the case-split
    discriminator in the first bullet of this section, `#1137`'s to repair, and it leaves the slot
    when it is repaired — ⚠️ **which `#1735` has since done**, so the count above is the `3e1bef2`
    measurement it says it is and two rows sit here at head. The row's headline now names
    `(2 : F) ≠ 0` and `((n : ℤ) : F) ≠ 0`; the entry is kept rather than deleted because the
    measurement is what makes the other two readable as *permanent* occupants and not as a
    remainder.
  * `comapProjPointN_pointClosedPoint_of_eval_ΨSq_eq_zero`, same file — **cleared** by that
    discriminator, so its headline is on the *"or it names none"* branch and no sweep reaches it.
  * `torsion_le_weilPairingPointSubgroup_n`
    (`EllipticCurves.FunctionField.WeilPairingTranslationSlotHprinN`) — binds **only** the instance
    `[NeZero n]`, which *"Instance arguments are ambient"* below exempts in terms, so no sweep
    reaches it either. ⚠️ It is in the binder-**29** and not in the **28**, so it witnesses on one
    of that count's two conventions and not on the other.

  ⚠️ **So the slot is not a subset of the class `#1137` is sweeping, and that is the answer to what
  a witness drawn from a swept population raises** (`#1728`): *states none* is a **compliant
  branch** of this section's rule and not only a symptom of a short clause, so a row can sit in the
  slot permanently, and two of these three do. What made the parenthetical above a countdown was
  not the slot — it was naming a **survivor** in the present tense, which the sweep falsifies the
  moment it arrives and `### Retired claims` then charges for. **Name rows inside a dated
  measurement, where `## Layout`'s *"the counts drift, the directory structure does not"* protects
  them; do not name in a present-tense parenthetical a row a standing sweep is scheduled to reach.**
  ⚠️ **The qualifier is the rule and not a softening of it**, and the reason is one line up: a name
  is a countdown only when something is scheduled to falsify it. That is why the **four**
  range-stating rows named above keep the present tense — no sweep on this front removes a range
  statement from a headline or adds an index binder to a signature, so nothing is scheduled to
  reach them — and why the slot's three are named under a date instead, the one of those three
  `#1137` **was** scheduled to reach at `3e1bef2` carrying its own expiry in the sentence that
  names it. ⚠️ **That expiry has since fired** (`#1735`, `b41a87c`) and the entry above records
  it, which is why this clause is tensed and dated rather than retired: a claim that announces its
  own expiry and is read again when the expiry fires is discharged by the record and not falsified
  by it — the ruling this bullet already applies to the entry itself. That is the
  ruling `#1728` asked for, and it is
  why the *"and states none"* half of that parenthetical is now a pointer to this paragraph rather
  than a name.
  ⚠️ **Everything else in this bullet is confirmed unmoved at `fddba5c`, not assumed**: `56` /
  `43` / `13`, the `23` / `33` case split, the `132` and the `120` / `113` siblings all re-run to
  the unit, and the binder-measured **29** cannot have moved at all, because every commit from
  `8d31527` to `fddba5c` is **docstring-only** — six `.lean` files touched and their stripped code
  byte-identical, so no signature in the tree changed. ⚠️ **Re-derived again at `3e1bef2`** by a
  fourth extractor (`#1728`), which also returns the binder-**29** with
  `divisorProj_mulByNEndoOfAlgClosed` taking its condition from a `variable` line and the **28**
  once `[NeZero n]` is dropped — so the two figures this bullet does not mark as triage have now
  reproduced across implementations, and the two it does mark have not.
  ⚠️ **The sibling wordings go the same way**, because the ground is the phrase's subject and not
  its noun: ``general-`n` <noun>`` (*"the general-`n` surjectivity"*, *"the general-`n` layer"*)
  and *"at general `n`"* — ``general-`n` (?!forms? of)[a-z]`` and ``at general `n` ``, same
  extractor, same case-insensitivity, **132** and **120** further sites at `8d31527`. The ruling
  clears them, and both recognisers are written out beside their counts so the next census meets
  a **measured** rule rather than inferring the width from this bullet's examples. ⚠️ **The second
  figure is what the case rule costs if it is skipped**: case-sensitively it reads **113**, and
  that is the number a first pass at this issue produced.
  ⚠️ **A row cleared here lands on the *"or it names none"* branch and is not exempt from the
  rule.** If its headline names nothing else, the signature is what the reader is deferred to; if
  it names a proper non-empty subset of the hypotheses it is defective for that reason, and the
  phrase neither repairs it nor makes it worse. ⚠️ **So this ruling clears a *phrase*, not the 43
  rows.** **37** of the 43 head a declaration binding an explicit `Transcendental …` argument, and
  what their headlines say about it is `#1137`'s standing question, decided by each file's own
  transcendence register and untouched here.

⚠️ The second discriminator is what separates *"at an index that is neither odd nor `3`-smooth"*
from *"at an odd `p`"*: the first describes the numeral `10`, while the second restricts a variable.
⚠️ Restricting a variable is **not** on its own what makes a clause a reach clause — *"off the
multiples of `d`"* restricts one too. *"at an odd `p`"* is one because it also fails the deletion
test above: `#E[pᵏ] = (pᵏ)²` is still a claim of the same kind once that phrase is removed, and
`divT`'s periodicity without *"off the multiples of `d`"* is not. ⚠️ *Of the same kind*, not
*still true* — `#E[pᵏ] = (pᵏ)²` bare is false in characteristic `p`, and the ⚠️ opening *"The test
asks whether the remainder is a claim of the same kind"* rules that reading out for every row, this
one included.

The rule is about **explicit** hypotheses, and the discriminator is the **binder info**: a binder
Lean elaborates as `instImplicit` is outside the rule, one it elaborates as `explicit` is inside it.
That is one test, it is the whole of the answer, and it settles every case this development has
without an exemption for any of them — because none of them was ever *in* the rule for an exemption
to take it out of. The ground is that doc-gen renders the **declaration's** instance list beside its
docstring, so a reader is never consulting the clause *instead of* that list, which is what makes a
partial **hypothesis** list a defect and is the argument of *"A phrase that names one instance"*
below as well.

⚠️ **The ground published with this paragraph had three clauses and the middle one is false**, and
that is what kept the question open long enough to be filed as an issue. It read *"Instance
arguments are ambient, are carried by the module's `variable` block, and are visible in the
signature doc-gen renders beside the docstring"* (`ee3c067`, `#1137`, PR #613); the `variable`-block
clause is falsified six paragraphs below by this section's own ⚠️ *"**The instance list is per
declaration, not per `variable` block**"*, and by the tree. Measured at `d459037` from the
elaborated telescope: **2179** of the **3599** documented declarations bind at least one
propositional instance, and **571** of those write one **in their own binder list**, across **163**
modules. ⚠️ **One of the 571 is the row this section cites the exemption on.**
`torsion_le_weilPairingPointSubgroup_n`
(`EllipticCurves.FunctionField.WeilPairingTranslationSlotHprinN`) — the witness-slot entry above
that *"binds **only** the instance `[NeZero n]`"* — writes `[NeZero n]` in its own `theorem` line
and takes **that** instance from no `variable` block, so the published ground was false of the
section's own worked case for it. ⚠️ **Retired, and here rather than at the theorem it names**
(`4efeb97`, `#1774`, PR #706): the clause read *"and takes no instance from a `variable` block at
all"*, and the row's own elaborated telescope falsifies it — `[Field F]` and the **propositional**
`[W.IsElliptic]` are bound by the `variable` line that opens
`WeilPairingTranslationSlotHprinN`'s `CoordinateRing` namespace — the one that also binds
`{xT yT : F}` — there is no `section` or `end` between it and the
`theorem torsion_le_weilPairingPointSubgroup_n`, and both are included because the statement
mentions `W`. ⚠️ **Both coordinates were line numbers and both had gone stale** (`#2037`): they were
exact at `830a050`, the commit that wrote them, and at `02a1652` they name a bibliography bullet and
an `open Classical in`. The sha this sentence carries is an **attribution** and resolves neither, so
the repair is the content key rather than a new number. `#1694`'s subject test puts the quotation
here rather than in that file: the claim is about **this section's ground**, not about what the
theorem says, so a reader of the file it names has no stake in it. ⚠️ **Only the universal fell.**
`[NeZero n]` is written at the declaration and carried by no `variable` block, which is the whole
of what makes the retired middle clause above false of
its own worked case. ⚠️ **The shape is `#1694`'s — claiming too much — and this section's own
census is the counterexample**: `[W.IsElliptic]` is propositional, so the row is one of the **1352**
the `IsElliptic` figures below count. It is PR #694's ``carries no`` gloss again, retired below in
this section (`#1756`) — each a universal asserted wider than its own check: this one read on the
binder `[NeZero n]` and asserted of every instance on the row, PR #694's read for identity claims
over the **56** and asserted of what each of them names, where **16** falsify it.
⚠️ **Retired** (`87c5313`, `#1782`, PR #707; `#1789`), and the clause above is what replaced it:
the gloss read *"true of the rows it was read on, false of every"*, and it is false of both claims
it glosses. PR #694's gloss was read on the **56** and **16** of those 56 falsify it, so it is false
of rows it was read on; and no narrower reading rescues it, since over the **40** absence claims
that are its proper subject *"a single"* fails on a further **6**, all of them rows it was read on
as well. PR #706's clause was read on **one** row and is false of that row — that
`torsion_le_weilPairingPointSubgroup_n` takes `[Field F]` and `[W.IsElliptic]` from a `variable`
block is the whole argument above. What is true of what that clause was read on is a claim about a
**binder**, which is what ⚠️ *"Only the universal fell"* above states in the right unit (`#1660`).
⚠️ **A shape-gloss that summarises two falsified universals is itself a universal and is checked
against both** — `#1628`'s membership rather than a total, transposed from counts onto glosses. This
is the third over-broad universal in three consecutive PRs on this one paragraph and the last of
them landed inside the sentence that names the shape, which is the evidence that line is written
from. ⚠️ **The 571 is a
floor, and the recogniser convention costs two rows.** It matches each bracket group written at
the declaration against the telescope's `inst`-and-`Prop` binders on the head identifier's last
component, so
`[(XYIdeal W x (C y)).IsPrime]` (`isIntegrallyClosed_localization_of_nonsingular`) and
`[∀ i, HasEnoughRootsOfUnity F (p ^ i)]` (`galoisCyclotomicChar_spec`) have no head to key on and
drop — counting those the figures
are **573** and **164** — and **38** further declarations could not be matched to a source signature
at all. It is `Prop`-only by construction, so `pullbackDivisorN_single_eq_sum_torsion_of_ne_zero`,
one of the three rows the per-declaration ⚠️ below names, is **not** in it:
`[Fintype (W.torsion n)]` is data.

⚠️ **`#1774` is that issue, and it is answered here rather than by a new sentence anywhere else.**
It asks for **one** discriminator covering `[IsAlgClosed F]`,
`[W.IsElliptic]` / `[IsDedekindDomain W.CoordinateRing]` and `[NeZero n]`, on the reading that the
first is named in headlines everywhere
and the middle pair *nowhere*. ⚠️ **That reading is wrong about the middle pair, and the correction
is what makes the discriminator obvious**: measured on the same dump, **20** headlines carry a
bracketed `IsElliptic` mention — `degProj_divisorProj`'s *"unconditional in `[W.IsElliptic]`"*,
`isOpen_ker_galoisRepMod_two_pow`'s *"and otherwise over an algebraically closed field with
`(2 : F) ≠ 0` and `[(W'⁄F).IsElliptic]`"* — while **0** name `[IsDedekindDomain W.CoordinateRing]`
and **0**
name `[NeZero n]`. **1350** declarations carry an `IsElliptic` propositional instance and **15** of
them name it in the headline, so `[W.IsElliptic]` behaves exactly as `[IsAlgClosed F]` does, named
on a small minority of the rows that carry it and unnamed on the rest — which is what a **mention**
rule predicts, and which a *must name* rule would turn into **1335** defects on that one instance.
⚠️ **Both of those figures are the head key's, and it costs two rows here exactly as it costs two
above.** The telescope carries **1352** declarations with an `IsElliptic` propositional instance, so
**1337** on the *must name* reading; the two that drop are `torsion_isUnramifiedAt`
(`EllipticCurves.Reduction.ReductionUnramified`) and
`galois_smul_eq_of_isUnit_nsmul_of_residue_trivial`
(`EllipticCurves.Reduction.ReductionGaloisEquivariant`), whose instance is written
`(W'.baseChange L).IsElliptic` and `(W'.baseChange K).IsElliptic` — a leading `(`, so no head
identifier to key on. Membership rather than a total (`#1628`): the 1352 are **1200**
`WeierstrassCurve.IsElliptic W`, **89** `W.IsElliptic`, **57** `… (W'.baseChange F)`, **2**
`… (W'.baseChange L)` and one each of four further forms, one instance per declaration.
⚠️ **No verdict moves and nothing retires** — *"named on a small minority of the rows that carry
it"* is true at 15 / 1350 and at 15 / 1352 alike, and a count over a population that can grow
under it stays true of what it counted, which is the open branch of *"short is partial,
over-reaching is false"* below (`#1782`): this telescope grew.
The binder info sorts all four the same way, and two consequences the issue tabled are settled with
it:

* **The `μ`-valued front clears on `[NeZero n]`.** `exists_weilPairingMu_self_eq_one_of_hprin_two`
  and `…_three` (`WeilPairingAlternatingBaseChange`) and
  `exists_weilPairingMu_self_eq_one_of_card_two` (`WeilPairingAlternatingTwoRational`) write
  `[NeZero n]` in their own binder lists, and each headline names that declaration's whole
  **explicit** list — the characteristic conditions, the nonsingularity and the torsion of `T`, and
  `hprin` or, at `…_of_card_two`, the rational-`E[2]` and rational-halving hypotheses standing in
  its place. `[NeZero n]` is the only binder beside them that could add anything, and it is
  `instImplicit`, so **no insertion is owed** and PR #704's conditional residue (`#1770`) is empty
  rather than pending.
* **A headline whose only reach phrase is an instance mention names no hypothesis at all**, so it
  lands on the *"or it names none"* branch and is compliant. That is the whole of `#1779`'s ten
  `_of_algClosed` rows — `exists_weilPairingElt_self_eq_one_of_algClosed_two` and `…_three`
  (`WeilPairingAlternatingTwo`, `WeilPairingAlternatingThree`),
  `exists_forall_weilPairingElt_self_eq_one_of_algClosed_two` and `…_three`
  (`WeilPairingRootIndependence`), and their six twins in `WeilPairingAlternatingTwoAlgClosed`,
  `WeilPairingAlternatingThreeAlgClosed` and `WeilPairingRootIndependenceAlgClosed` — **cleared,
  with no diff**, over signatures binding `h2`, `h3`, `htors` and `hprin`.
  ⚠️ **On the reach axis only, and six of the ten carry a second half this does not reach.** Those
  six add *"with no hypothesis beyond the setting"*, and a totality phrase stated relative to a gate
  list is a gate-discharge claim governed by `### Gate-discharge claims`, which this section's ⚠️
  *"A totality phrase stated **relative to a named gate list**"* below says in terms. `#1781` is
  about that half; nothing here clears it, and a clearance on this axis must not be quoted as one on
  that one.
  ⚠️ **The clearance is also not a reason to revert an insertion**, on the branch-neutrality ruling
  the first bullet of this section states: appending the missing conditions moves a headline from
  one compliant branch to the other, so `#1763` / PR #702's four repaired `_of_algClosed` headlines
  in `WeilPairingAlternatingAssemblyN` stand, and so would a repair of any of these ten.
* ⚠️ **The `residueDegreeN_none_eq_one` withdrawal does not transpose to an instance**, which is the
  second of the two routes `#1774` rules out and the one that needs an account rather than a denial.
  That withdrawal turns on *"`hn` is a condition on the index, and `xCoord_zero` makes it false at
  `n = 0`"* — and `hn` is an **explicit** binder in both members of the pair it is argued from,
  printed as such in the fenced signatures below. It is a ruling inside the explicit side of this
  paragraph's first sentence and reaches no `instImplicit` binder. ⚠️ The same goes the other way:
  nothing here reinstates the data-argument clearance for an explicit binder, and `#1631`'s
  occurrence-test wording stays retired.

**A phrase that names one instance is a claim about that one instance and commits the clause to
nothing else.** *"over `F̄`"* says `[IsAlgClosed F]` is in the declaration's instance list; *"with
no `[IsAlgClosed F]`"* says it is not. Each is compliant exactly when it is true of the instance it
names, and neither is a partial list, because the list is rendered beside the docstring — the
reader is not consulting the phrase *instead of* the signature, which is what makes a partial
**hypothesis** list a defect. So an instance mention is a defect only when it is **wrong about the
instance it names**, and whether a block mentions one at all is a per-block uniformity question
under `### Scope of the rules above`, not a defect question.

**Name all of them or none binds a phrase that quantifies over the list, not one that names a member
of it.** *"over an arbitrary field"* is a claim about every instance constraining `F` and is held to
all of them: `translateEndo_eq_self_of_mul_algebraMap_cube_eq`
(`EllipticCurves.FunctionField.WeilPairingAlternatingThree`) carries `[Field F]`, `[W.IsElliptic]`
and `[IsDedekindDomain W.CoordinateRing]`; the last two are conditions on the curve and not on `F`,
so the claim holds. ⚠️ A totality phrase stated **relative to a named gate list** —
*"unconditionally"*, *"with no hypothesis left"* — is a gate-discharge claim and is governed by
`### Gate-discharge claims` below, not by this paragraph.

⚠️ **The two directions are not equally safe, and that asymmetry is why any of this is written
down.** doc-gen renders what a declaration *has*, so a presence mention is contradicted on its own
page as soon as it goes stale, while an absence claim is contradicted by nothing a reader can see:
adding one instance to a `variable` line silently falsifies every *"needs no `[…]`"* below it.
`not_forall_det_eq_intCast_of_zsmul_add_zsmul`
(`EllipticCurves.FunctionField.WeilPairingDeterminantLinear`) is the form to copy — it says *"needs
neither `[IsAlgClosed F]` nor `[W.IsElliptic]`"* and records that the `omit` above it is measured
rather than guessed, `unusedSectionVars` having reported both.

⚠️ **The instance list is per declaration, not per `variable` block**, so check it there. `omit
[DecidableEq F] in` removes an instance from the declaration below it, and a declaration may bind
instances the block never had. In `EllipticCurves.FunctionField.MulByNFibre`,
`card_fibre_comapProjPointN_projPointOfPoint_of_ne_zero` and
`fibre_comapProjPointN_eq_range_of_ne_zero` are 24 lines apart with different instance lists, and
`pullbackDivisorN_single_eq_sum_torsion_of_ne_zero` binds `[Fintype (W.torsion n)]` in the
statement. An instrument that reads the `variable` lines and stops gets all three wrong.

⚠️ **This paragraph is not a further discriminator for the bullet list above.** It does not say that
an instance mention looks like a reach clause and is not; it says the reach-clause rule never
reached instances, so there is nothing for the *"or it names none"* branch to decide.

⚠️ **Retired.** PR #613 (`#1137`), which first wrote this paragraph, ended it *"But a clause that
does make an instance claim (with no [IsAlgClosed F]) is making a complete-list claim about
instances, and then the same rule applies to those: name all of them or none."* Read literally that
convicts every headline that names one instance and not the rest —
`card_fibre_comapProjPointN_projPointOfPoint_of_ne_zero`
(`EllipticCurves.FunctionField.MulByNFibre`) says *"over `F̄`"* and carries `[W.IsElliptic]` and
`[IsDedekindDomain W.CoordinateRing]` unnamed beside it. The paragraphs above replace it: a
**mention** is a single-membership claim, and only a phrase quantifying over the list inherits
*name all of them or none*.

Two alternatives were weighed and rejected on a measurement of the tree at `681c146`, where **621**
documented declarations carry `[IsAlgClosed …]` in their effective instance list, **163** name the
closure in the headline, and **45** of the **116** files holding such a declaration are split.
Requiring the mention, and then every instance beside it, moves **458** headlines and needs a policy
for `omit`ted and per-declaration instances; forbidding the mention moves **163** and deletes
*"over `F̄`"* from statements that are false without it. Both replace phrases that are true where
they stand with a rule to be re-derived at every row, and the census found **no headline naming a
closure the declaration does not have** — so on the mention side the class this ruling calls a
defect is, today, empty, and neither alternative would have paid off a single wrong claim.

The rule binds every **explicit** hypothesis, with two narrow exemptions. **The first is
derivability**: a clause may omit a hypothesis that is **derivable from the hypotheses the clause
does name**, since such a hypothesis adds no reach information the clause has not already given.
Where the exemption is used, the derivation is cited once in the module block, so a reader can
check it instead of taking it.

The case this development has is the transcendence parameter of the `[n]∗` layer,
`h : Transcendental F (n • genericPoint).xCoord`, which every statement about `mulByNEndo n h` or
`comapProjPointN n h` carries as an explicit argument:

```
-- right: `h` follows from the two conditions the clause already names, by
-- `transcendental_xCoord_nsmul_genericPoint_of_intCast_ne_zero` (either cast form)
`fixedFieldN_eq_mulByNFieldRange_of_ne_zero` at every `n` with `(2 : F) ≠ 0` and `(n : F) ≠ 0`

-- wrong: `ramificationIdxN_pos` names no other hypothesis, so `h` is the only thing restricting
-- which `n` are reached, and omitting it reads as unconditional.  It is not: `xCoord_zero` makes
-- `h` false at `n = 0`.
`ramificationIdxN_pos` is `0 < e_p` at every `n`
```

⚠️ **That exemption is about derivability, not about where the hypothesis appears.** A rule keyed
on *"the hypothesis occurs in the conclusion"* would reach `(2 : F) ≠ 0`, which is an explicit
argument of `mulByTwoEndo`, `mulByThreeEndo`, `comapProjPointTwo` and `weilPairingTwo`, and so
occurs inside the conclusion of every statement about them. `(2 : F) ≠ 0` is derivable from nothing
any reach clause on this development names — not from `3`-smoothness, not from `(n : F) ≠ 0` — so it
is reach, and the rule binds it. Omitting it is the defect class `#1137` exists to pay off.

⚠️ **Whose module block: the one that STATES the declaration, not every module whose prose recites
its reach.** The sentence above does not say which, and the two readings convict two files and
twenty-four. Seed, over the whitespace-normalised text of every tracked `.lean` and `.md` blob —
normalise first, a line-anchored `grep` sees 30 of the 77 rows below and 26 of the 62:

```
PHRASE = every\s+`?n`?\s+with\s+`\(2 : F\) ≠ 0`\s+and\s+`\(\(n : ℤ\) : F\) ≠ 0`
DER    = transcendental_xCoord_nsmul_genericPoint_of_intCast_ne_zero
```

**77 rows in 33 files at `42c9b11`, and 62 in 23 at `58df5a5`.** Sort the `.lean` files by whether
the blob writes the token `Transcendental` at all — one that never writes it states nothing binding
`h`, so no statement of its own can be using the exemption:

* **the blob binds `h`** — 10 files carrying 50 rows at `42c9b11`, 10 carrying 47 at `58df5a5`, and
  **every one of them names the derivation**;
* **the blob never writes `Transcendental`** — 22 files carrying 24 rows at `42c9b11`, 12 carrying
  13 at `58df5a5`, and **not one of them names it**. Every row in this class is a pointer to a
  declaration stated somewhere else.

⚠️ **The correlation is exact at both refs** — 10 of 10 and 22 of 22 at the later one — so the tree
has been paying this clause once per *defining* module throughout, and the twenty-two are not an
unpaid backlog. The other reading is the expensive one and buys a reader nothing: it writes this one
derivation into twenty-two further module blocks, eight of them `TateModule` files that state
nothing about `[n]∗`, about transcendence or about the function field, for a hypothesis no statement
of theirs takes — while a reader who follows the pointer arrives at the defining block, which cites
it, having already passed the derivation worked out above on this page.

⚠️ **The sweep has run (`#1881`), and the row count is the wrong key: a module can owe this
citation while carrying no row of the phrase at all.** Two paragraphs stood here and both are
retired. The first said *"What the clause still convicts is two files, and the defect there is
placement and not absence"* and named `PullbackPrincipalityN` (12 rows) and
`WeilPairingAlternatingBaseChangeN` (3); the second said *"A pointer that names a MODULE rather
than a declaration is not decided here"*, of four rows in `WeilPairing`,
`WeilPairingNondegenerateMu`, `WeilPairingNondegenerateThree` and `WeilPairingNondegenerateTwo`.
**One of those two convictions is false and the other is paid; the four rows are decided.** The
seed's own population is **77 rows in 33 files at `02a1652`**, with the same 10 / 50 and 22 / 24
split as at `42c9b11`, so every figure above this paragraph is exact at its own sha and none of
them moves.

⚠️ **The repair is self-populating, and the delta is published rather than left for a re-runner to
convict.** A block that cites the derivation has to say *which* clauses omit the parameter, and
saying so restates the clause verbatim, so the two blocks repaired below add **2 rows in 1 new
file**: `PullbackPrincipalityN` 12 → **13** and `WeilPairingNondegenerateN` 0 → **1**, taking the
10 / 50 half to 11 / 52 and leaving the 22 / 24 half untouched. ⚠️ **The delta is the durable
figure and the total is not, and this paragraph says which is which rather than printing a sum
with no sha**: the tree `02a1652` + this diff reads **79 rows in 34 files**, and PR #768 at
`130cf38` adds a further row in a further file (`WeilPairingPerfect`), so whichever of the two
lands second stands in a tree of **80 / 35**. The delta survives either order and the sum does not.
**Every one of the two new rows is inside a paragraph whose subject is the exemption itself**, which
is the one place in the tree where the phrase is mentioned rather than used. This is `#2036`'s
finding on a different seed — *the house repair form does not remove a row from a vocabulary-keyed
population, it adds one* — and a seed that wants the live rows alone needs the
quotation-and-mention filter that issue specifies.

⚠️ **The key that decides the question is `names the derivation somewhere but not in its module
block`, and it returns four files at `02a1652`** — `PullbackPrincipalityN`,
`WeilPairingAlternatingBaseChangeN`, `MulByNDegreeGeneral` and `WeilPairingNondegenerateN`. The
last two are the ones a row-keyed sort cannot see, and they are invisible to it for two different
reasons: `MulByNDegreeGeneral` carries no row of the phrase under either reading of the seed, and
`WeilPairingNondegenerateN` carries none under the published reading and **one** under the
emphasis-tolerant reading the third flag on that seed names — a row standing inside the very module
block convicted here, which leaves that file convicted twice over rather than once. A module owes
the citation by *stating* a declaration whose clause omits the parameter, and reciting someone
else's reach is neither necessary nor sufficient for that.

* **`PullbackPrincipalityN` — convicted, and paid.** **Nine** of its twelve rows describe
  statements of its own that bind `h`, and its module block now cites the derivation. ⚠️ **The
  other three take the three dispositions this list gives the other files, inside the convicted
  one**, and the block says which: the `## Main statements` bullet for `exists_gS_n_of_isAlgClosed`
  *names* the parameter rather than omitting it, the headline of
  `exists_gS_of_ne_zero_of_isAlgClosed` describes a statement that applies the derivation inside
  itself and so binds none, and the row naming
  `pullbackDivisorN_single_eq_sum_torsion_of_ne_zero` is a pointer to `MulByNFibre`. A row of the
  phrase is not by itself a use of the exemption, in the convicted file either. ⚠️ The block
  already named `transcendental_xCoord_nsmul_of_isAlgClosed`, which is a **different** derivation —
  the one that route deliberately does not take — so a reader who saw *a* transcendence lemma in
  the block was not being sent to the one the clauses rest on.
* **`WeilPairingAlternatingBaseChangeN` — acquitted, and nothing there is changed.** Two of its
  three rows describe `exists_weilPairingElt_self_eq_one_of_ne_zero_of_baseChange`, which applies
  the derivation *inside* the statement and therefore binds no transcendence parameter and omits
  nothing; the third is a pointer to `exists_gS_n_of_isAlgClosed`, stated in
  `PullbackPrincipalityN`. **Exactly one** clause in that file uses the exemption — the `3`-smooth
  `translatePointEndo_eq_self_of_prod_eq_of_pow_eq_of_baseChange` — and its derivation is
  `transcendental_xCoord_nsmul_of_smooth`, which that module block cites twice. Of the four other
  statements there that bind the parameter, three name it in their headlines as *"with a
  non-constant `[n]∗`"*, and the fourth is the `example` restating the first verbatim, which makes
  no reach clause of its own. ⚠️ **It was convicted by a file-level token key, not by any row of
  its own.**
* **`MulByNDegreeGeneral` — acquitted**, for the reason the paragraph above already gives about
  `exists_gS_n_weilPairingElt_ne_one`: `finrank_mulByNFieldRange_eq_sq_of_two_ne_zero` applies the
  derivation inside the statement.
* **`WeilPairingNondegenerateN` — convicted, and paid. ⚠️ It is also what the four module rows
  owed.** They recite the reach of statements that bind `hT` as an explicit argument, so the
  exemption *is* in use in them; under *whose module block* what they owe is a citation in the
  module that states those statements, and that module had none. Five of its seven bind `hT`;
  `exists_gS_n_weilPairingElt_ne_one` and `exists_gS_n_weilPairingMu_ne_one` do not, because they
  apply the derivation inside the statement, and its block now names which are which. One of the
  twenty-four pointer rows was already decided this way: `MatrixRepMod` names
  `exists_gS_n_weilPairingElt_ne_one` by itself, so its clause omits nothing and owes nothing.

⚠️ **Three flags on that seed; the second is a whole second population and the third is a blind
spot rather than a choice.** Requiring the backticks round `n` returns the same 77 and 62, so that
choice costs no row. The sibling clause carrying `(n : F) ≠ 0` where this one carries
`((n : ℤ) : F) ≠ 0` returns 71 rows at `42c9b11` and is excluded by construction: the two are
interderivable propositions but different clauses, matched to the declaration suffix, and this seed
reads only the `ℤ`-cast one. ⚠️ **And every count this section publishes over it is
emphasis-blind**, because a `**` falling inside the span stops the match. Strip the emphasis
markers from the normalised text before matching and the population is 79 in 34 at `42c9b11`, at
`02a1652` and at `9147113`, and 63 in 24 at `58df5a5` — **two hidden rows at `42c9b11`, `02a1652`
and `9147113`, and one at `58df5a5`, which is what 62 → 63 says.**
`WeilPairingNondegenerateN` hides one at all four refs, at line 22 in each, where a bold span
closes between the quantifier and the index.
`WeilPairing` hides the other at `42c9b11`, `02a1652` and `9147113`, at line 181 in
each, where a bold span closes between the index and the word `with`; ⚠️ **at `58df5a5` it hides
none, because that sentence is not in that file at that ref under either key**, and line 181 there
is a different sentence of the same bullet. ⚠️ **Neither reading is wrong, and they differ by two
rows at those three refs and by one at `58df5a5`**, so a figure over this seed owes its flag the
way it owes its sha. What is **not** measured is
whether each of the 50 rows in the ten binding files is itself a use of the exemption — nothing
above turns on it, because those files name the derivation either way.

**The second exemption is the non-vanishing of the function a statement is an equation about**, and
it is not the first one in other clothes — `hf : f ≠ 0` is derivable from nothing. A reach clause
answers *where* a statement holds, over which fields and at which indices, because that is the
question a reader settles once and then builds a layer on. A non-vanishing side condition on the
subject function answers *which argument*, and the caller supplying the argument already holds the
answer. `divisorProj_mulByNEndo` (`EllipticCurves.FunctionField.MulByNPlacePullback`) binds
`hf : f ≠ 0`, and its headline names the index condition and not it; that is not the
`card_torsion_eq_sq` defect, because `f` is neither a field nor an index and no layer is built on
the set of `f` at which the identity holds.

⚠️ **The discriminator is what the condition is *about*, and it is NOT *"the binder occurs in the
conclusion"* — that test is ruled out by name two paragraphs above and this one does not reinstate
it.** The two are easy to confuse, because a non-vanishing does typically occur in the
conclusion: `torsion_le_weilPairingPointSubgroup_two`
(`EllipticCurves.FunctionField.WeilPairingTranslationSlotHom`) concludes
`W.torsion 2 ≤ weilPairingPointSubgroup hg 2`. But so does `(2 : F) ≠ 0`, in every statement about
`mulByTwoEndo h2` or `mulByNEndoOfAlgClosed h2 hn` — `divisorProj_mulByNEndoOfAlgClosed`
(`…MulByNPlacePullback`) concludes an equation whose **both sides** take `h2`, and it is a row
PR #637 (`#1605`) repaired on exactly this axis. An occurrence test would clear it and reverse that
repair. What separates them is subject matter: `(2 : F) ≠ 0` restricts the field the statement is
over, `f ≠ 0` restricts the argument its caller passes in.

⚠️ **That discriminator is the whole of the *data-argument* clearance too, and `#1631` is what it
cost to find that out.** `### Module-block bullets` below **used to clear** a binder that is
*"a data argument of the object the bullet is about"*, and gave the test as *"does not typecheck
without it"* — at `5c3fce2^`, where that section carried both as a live clearance.
⚠️ **The premise belongs in the past tense, and this is a tense and not a cut** (`#1935`): PR #651
withdrew the ground and rewrote that section in the **same** diff that wrote this sentence, so the
present tense was false at the commit that wrote it, and `#1643` (PR #657) made the identical
repair to the sibling premise in this section without reaching this one. That section carries
the wording still, under *"This document used to clear that on the ground that"*, and names **this**
section as what withdrew the ground — so in the present tense this paragraph had the document
withdrawing a ground and resting on it at once. That wording is an occurrence test — the
one the paragraph above rules out by name and this one says it does not reinstate — and read as
written it cleared `(2 : F) ≠ 0` in every statement about `mulByTwoEndo h2` or
`mulByNEndoOfAlgClosed h2 hn`, which is the occurrence reading the paragraph above says *"would
clear it and reverse that repair"* of PR #637 (`#1605`). **The clearance is real; that wording of it
is not.** What clears a binder is the same thing that clears `f ≠ 0`: the condition is about the
argument the caller passes in — a supplied root, a certificate, a point on the curve. Being an
explicit argument of the object the statement is about is **necessary and nowhere near sufficient**,
because the field and the index reach the conclusion that way too.

⚠️ **So a binder that reaches the object only through a projection is a data argument, and the
projection was never the deciding feature.** `#1631` asked whether `h : W.Nonsingular xT yT`, which
`pointClosedPoint h.left` receives as `h.left` rather than as `h`, clears where a signature binding
`W.Equation x y` outright would. It does, and for a reason that never looks at the application node:
`W.Nonsingular xT yT` is a condition on the point the caller passes in, and it is that whether the
conclusion takes `h`, `h.left`, or a term derived from `h` any other way.
`WeilPairingGaloisRootN`'s `exists_weilPairingElt_galois_of_smooth_of_hprin` and
`exists_weilPairingMu_galois_of_smooth_of_hprin` — one file, one slot, one binding the `Equation`
and the other the `Nonsingular` — are **one case**, and a test that splits them is reporting the
shape of a signature rather than the reach of a clause.

⚠️ **And no narrowing of the occurrence reading rescues it, because this pair is identical on every
feature such a test can see:**

```
theorem residueDegreeN_none_eq_one (n : ℕ)
    (hn : Transcendental F (n • genericPoint (W := W)).xCoord) :
    residueDegreeN n hn (none : ProjPoint W) = 1

theorem ramificationIdxN_pos (n : ℕ)
    (hn : Transcendental F (n • genericPoint (W := W)).xCoord) (p : ProjPoint W) :
    0 < ramificationIdxN n hn p
```

Same binder, same explicit-argument position in the conclusion, the same *"at every `n`"* clause
naming nothing else. This section convicts the second by name above; `### Module-block bullets`
**used to clear** the first by name below, on the data-argument ground this section withdraws — at
`5c3fce2^` that section read *"it is compliant for the other reason, that the declaration's one
propositional binder is a data argument of the object the bullet is about"*. ⚠️ **The opposition is
this argument's premise, and it belongs in the past tense**: PR #651 withdrew the ground, rewrote
that section and wrote this sentence in **one** diff, so *"clears the first by name below"* was
false at the commit that wrote it (`#1643`). What the pair is evidence of does not move — the
document *had* decided two rows no such test can tell apart in opposite directions. Under the
discriminator both are **reach** — `hn` is a condition on the index, and `xCoord_zero` makes it
false at `n = 0` — so the second stays convicted and the first is convicted with it. ⚠️ **Neither
is a sweep and neither is repaired here**: the repair of `residueDegreeN_none_eq_one`'s reading
belongs where that reading stands (⚠️ until `#1649` this clause read *"the two readings below are
corrected where they stand"*, promising a repair for each member of the pair and pointing *below*
for a reading this document keeps above, in its own fenced `-- wrong:` row), and the
`residueDegreeN` row itself belongs to `#1616`.

⚠️ **And the first has since been repaired there**, which is where the sentence above put it:
`#1636` (PR #653) named the condition in the row — it now reads *"at every `n` at which `[n]` is
non-constant"* — and `### Module-block bullets` below carries it as a **repaired** row, the
conviction standing and the reading that drew it marked there as retired. ⚠️ **Nor are the two
*"at every `n`"* clauses this pair is argued from alike, and neither of them is a live bullet
today.** `residueDegreeN_none_eq_one`'s was one until PR #653 and is now a retired reading;
`ramificationIdxN_pos`'s never was — the fenced *wrong* row above is written **for** this document,
and that declaration's own bullet (`EllipticCurves.FunctionField.MulByNPlacePullback`) reads
*"`…ramificationIdxN_pos` giving `0 < e_p`"* and carries no reach clause at all. So the pair argues
a **clause form**, which is what the *right*/*wrong* rows above are for; the live row it touched is
repaired, and `ramificationIdxN_pos` had nothing to repair.

**One mechanical backstop is available, and it is worth running before arguing a row.** Where
deleting the binder leaves the statement provable, it constrains nothing and there is no reach for
a clause to misreport. This is the deletion test above run on the binder side, with the **compiler**
deciding instead of a reader: restate the declaration without the binder and build. `ord` and
`ordInfty` carry documented junk values at `0` (`ordInfty_zero`, *"matching the convention
`ord v 0 = 0`"*), so `div (f ∘ [n]) = [n]∗ (div f)` reads `0 = 0` at `f = 0` and
`divisorProj_mulByNEndo`'s `hf` is a convenience of the proof rather than a condition of the
theorem. ⚠️ The backstop is one-directional and never reaches `(2 : F) ≠ 0`, for two reasons at two
kinds of row: where `h2` is a free-standing hypothesis the deleted form elaborates and is **false**
in characteristic `2`, and where it is an argument of `mulByTwoEndo` or `mulByNEndoOfAlgClosed` the
deleted form does not elaborate at all. Either way the restatement does not build, which is what
makes this a backstop rather than a second discriminator.

⚠️ **This exemption stops at a claim that counts hypotheses.** Where the non-vanishing is
load-bearing *and* the docstring makes a gate-discharge or totality claim about the hypothesis
list, `### Gate-discharge claims` below binds and the word still has to have a subject.
`exists_eq_algebraMap_of_divisorProj_nonneg` (`EllipticCurves.FunctionField.ProjectiveDivisor`)
is the row: its conclusion `∃ c ≠ 0, f = algebraMap c` is **false** at `f = 0`, where the no-pole
hypothesis holds, so its `f ≠ 0` is **load-bearing**, this exemption does not reach it, and
`### Gate-discharge claims` governs its headline. The headline **said** *"from the single
hypothesis that `f` has no pole"* over a signature binding `f ≠ 0` as well, and PR #640 (`#1608`)
repaired it together with the module bullet describing the same row; both now read *"for `f ≠ 0`
and from the single **non-negativity** hypothesis"*. ⚠️ **The classification is what this paragraph
is for and the repair does not touch it**: only the quotation is a claim about the row's text, and
it is past tense for that reason.

Measured at `27d4f29`, from the elaborated telescope: **239** documented declarations bind a
`FunctionField`-valued `≠ 0` hypothesis, every one of them in `FunctionField/`, and **225** of their
headlines do not name it. Of the **18** whose headline named some other condition and not it, **10**
are vestigial by the backstop above, **3** are constituents of the object the statement is about
(the supplied root in `weilPairingPointSubgroup hg 2`, and the data argument of a `def`), and **5**
are load-bearing — of which exactly one makes a counting claim and is therefore governed by
`### Gate-discharge claims` below. Naming it in the other seventeen would put a uniform directory
into two registers, which is what `### Scope of the rules above` is for.

**A cited declaration's *name* does not complete the clause that cites it.** *"surjectivity holds
at every nonzero index (`nsmul_surjective_of_two_ne_zero`,
`EllipticCurves.Torsion.TwoTorsionOrder`)"* is short of `(2 : F) ≠ 0`, and the `_of_two_ne_zero`
inside the backticked identifier four words away does not repair it. A reach clause is what a
reader consults *instead of* the signature; an identifier is a name, not a hypothesis list.

⚠️ **The suffix rule this document already has is a *matching* rule, not a substituting one.**
`### Scope of the rules above` says *"`(n : F) ≠ 0` and `((n : ℤ) : F) ≠ 0` are different clauses.
The `_of_natCast_ne_zero` and `_of_intCast_ne_zero` suffixes say which, and a reach clause should
match the suffix."* That lets a suffix decide **which** of two conditions a clause that already
names one is naming. It does not let a suffix supply a condition the clause names nowhere, and the
two are not points on a spectrum: the defect this section defines is the **proper non-empty
subset**, and a clause that lists the index and drops `(2 : F) ≠ 0` reads as a complete hypothesis
list however the cited identifier is spelled.

⚠️ **Three further grounds, each decisive on its own.**

* The rule would be keyed on **naming luck**. It clears `nsmul_surjective_of_two_ne_zero` and
  clears nothing for `card_torsion_eq_sq`, which binds the identical `h2` and carries no suffix —
  so one block would hold rows in two registers for a reason that is not about the mathematics,
  which is what `### Scope of the rules above` exists to forbid.
* The suffix is **itself a proper subset**. `_of_two_ne_zero` names `h2` and not the `hn : n ≠ 0`
  beside it, so a reader told to read identifiers as hypothesis lists is reading a partial one.
* The development **already writes the compliant form** for this declaration in this phrasing —
  *"`[n]`-surjectivity at every `n ≠ 0` with `(2 : F) ≠ 0`"*
  (`EllipticCurves.TateModule.DeterminantModSmooth`). **12** sentences in the tree named both
  conditions before `#1659`, measured at `5dfd94d` with the recogniser published on that issue. If
  the suffix cleared, all twelve would be redundant and somebody would have deleted them.

⚠️ **This rules on citations, which is the layer no register reaches.** A reach clause about a
declaration whose file the writer is not editing is covered by no register in either file, and no
review of the defining module ever looks at it; the trigger for it going stale is an edit somewhere
else. It is bound by this section exactly as a headline or a `## Main *` bullet is, and the repair
is the one this section already prescribes: name the condition in the clause, or name none.

**A clause that points at another list is a third branch, and it is exactly as complete as the
list it points at.** *"under the same hypotheses"*, *"at the same hypotheses"*, *"with it"*,
*"under the hypotheses of `X`"* name neither every hypothesis nor none: they **incorporate** a list
by reference, so the rule above binds them through their antecedent. A short antecedent is a defect
at every clause pointing at it, in every file, and it is invisible where it lands, because the
pointing clause contains no hypothesis to be missing. ⚠️ Read the antecedent, and read it **for the
anaphor's own subject** — two declarations in one sentence need not share a list, since a condition
may be a binder of one and sit inside the other's predicate. `hasXCoordFormula_of_two_ne_zero`
carries `ΨSqₙ(x) ≠ 0` inside `HasXCoordFormula` while `nsmul_eq_some_omegaY_of_ΨSq_ne_zero` binds
it, and `EllipticCurves.Torsion.Collinearity`'s six words were complete for the first and short for
the second at once. **Where the antecedent is what is short, repair the antecedent**: one insertion
pays off two sentences and stops the propagation.

⚠️ **An anaphor can also fail by importing too much, and that direction is the one nothing
renders.** `neronOggShafarevich_galoisRepMod_eq_one`
(`EllipticCurves.Reduction.NeronOggShafarevich`) said *"under the same hypotheses"* over an
antecedent headline reading *"`ℓ` is a prime invertible in `A`"* — **prime** — and binds no
`[Fact ℓ.Prime]`: a correct instance **mention** was carried across a declaration boundary onto a
declaration that does not have the instance, where it is wrong about the instance it names. The
paragraphs above make a stale mention a defect exactly there, and the asymmetry they rest on is
what makes this shape worse than a stale mention in place — doc-gen contradicts a wrong mention on
its own declaration's page, and cannot contradict one imported from another's.

**Identity is measured on reach, not on the telescope.** *"X has the same hypotheses as Y"* is a
reach clause whenever it is doing reach work, and what it is held to is whether the two are claims
about the same situations, not whether their binder lists match token for token. Two consequences,
each of which decides a row this section would otherwise leave undecidable:

* a binder cleared by the derivability exemption above does not count against it.
  `isGalois_mulByNFieldRange_of_smooth`'s *"the separable half is `#1219`'s
  `isSeparable_mulByNFieldRange_of_smooth`, at the same hypotheses"* is **complete** — the two bind
  the identical five arguments and the transcendence `h` neither names is the exempt one, cited in
  `EllipticCurves.FunctionField.MulByNGalois`'s own transcendence section;
* a residual binder at a fixed numeral restricts nothing, by the *"a phrase about a fixed numeral
  is a remark"* discriminator above. `finrank_torsion_of_smooth h2 h3 (n := 3)` *"has the same
  hypotheses as the merged `finrank_torsion_three`"*
  (`EllipticCurves.TateModule.DeterminantModSmooth`) is **true** although `1 < 3` and `hfac` are
  still binders of the applied term, and `EllipticCurves.FunctionField.MulByThreeGalois`'s *"the
  general-`n` package carries the same hypotheses as this file's at `n = 3` and no fewer"* is true
  for the same reason — `isGalois_mulByNFieldRange_three` certifies it, over `h2` and `h3` alone.

⚠️ **An anaphor is a pointer and not evidence of completeness, so a census may not clear a row on
one.** `#1679` publishes ``under the same hypotheses`` and ``with it`` as **field seeds**, which
clears a row on the strength of a neighbouring list without checking that list is complete for the
new subject. That is sound only where the antecedent has been read: on the `h2` axis it has been,
and `EllipticCurves.TateModule.Profinite`'s *"`card_torsion_le_sq` there proves `#E[n] ≤ n²` under
the same hypotheses"* is the correct row it protects. On any other axis a seeded row is
**unmeasured, not clean** — `Collinearity` above was cleared by that seed on the `h2` axis,
correctly, and was short on the `hΨ` axis in the same six words. The class is small enough that
reading it is the instrument: **25** bare anaphors in **18** files at `4148f23`, out of **32**
occurrences of the phrase family in **23** files, from **231** seeded occurrences in **123** files,
every one read; the seeds and the row-by-row verdicts are on `#1705`.
⚠️ **That `25` is the count on the PHRASE axis while this ruling is keyed on the CLAIM, so it is
short of the population the ruling governs** (`#1714`). Re-run at `cb6ad1f` over twelve seeds chosen
for the claim rather than the wording — `the hypotheses of`, `the same reach`, ``same binders?``,
``keeps? the hypotheses``, ``inherits? the hypotheses``, ``weakens? or strengthens``,
``no (further|extra|additional) hypothes``, ``carries no\b``, `same telescope`,
`binder for binder`,
`argument position`, and `hypotheses` followed by `inherited`, `unchanged` or `verbatim` — over the
same nesting-aware `/-`-depth comment regions, whitespace squeezed, case-insensitive: **107** raw
hits over **420** files, every one read, of which **8** state reach identity and are **not** among
the 25 — `MulByNFibre:999` and `:1164`, `WeilPairingRootIndependence:202`,
`WeilPairingCyclotomic:50`, `DeterminantModGeneral:218` and `:239`, `MatrixRepModGeneral:120`, and
`WeilPairing`'s `## What non-degeneracy actually consumes`. **The identity axis is 33 rows in 23
files, not 25 in 18.** ⚠️ **The seven line addresses in that list resolve at `cb6ad1f`, which is the
sha this paragraph names and not the tree** (`#2037`), and `WeilPairingCyclotomic:50` resolves there
and necessarily not at `HEAD`, because this paragraph records below that that row was repaired. The
eighth resolved at neither and is keyed by heading here: it read `WeilPairing:303`, exact only at
`1d79187`, which added it to a list the other seven had been in since `bde07d8`. Seven are true —
the two `binder for binder` restatement claims were read against the four `_of_smooth` signatures
they name, `omit` lines included — and one, `WeilPairingCyclotomic`'s *"Nothing here weakens or
strengthens the hypotheses of the merged equivariance statements"*, was **false** and is repaired in
that file. ⚠️ **The 25 is not retired**: it is a true, dated count of the rows the phrase seeds
return, so it is **partial** and takes the qualification above rather than a marked quotation. Run
*"false or merely partial"* before opening `### Retired claims` on a count that is merely **short**.

⚠️ **An inhabitation claim is not a reach clause, and the widest claim-axis seed is almost all
inhabitation.** *"The hypotheses of `X` are satisfiable"*, *"… are also necessary"*, and the
non-vacuity certificates that carry them, say a hypothesis **list is inhabited**; they do not say
which situations `X` reaches, so nothing in this section binds them. **Ten of the 28
`the hypotheses of` hits are non-vacuity certificates and five more are section titles named after
one**, and ``carries no\b`` is **56** hits in **49** files of which **none** is an identity claim.
The discriminator, written down so the next census does not re-derive it: a clause is on this
branch when its subject is a **declaration's reach**, and off it when its subject is a **hypothesis
list's inhabitants** (`#1714`).

⚠️ **Retired.** PR #694 (`#1714`), which first published that **56**, glossed it *"every one names
a single absent binder, instance or name component, which is the absence register (#1682, #1683)
and not this branch"*. The operative half stands and is what the paragraph above keeps: all 56 were
read, none states reach identity, and the seed returns **zero** rows on this branch. The gloss is a
**universal**, and **16** of the 56 falsify it (`#1756`). What replaces it, re-derived at `039d7e4`
with the recogniser above: **40** of the 56 are absence claims naming a binder, an instance or a
name component, and those — only those — are `#1682` / `#1683`'s register; the other **16** say an
object *carries no information, content, weight, dependencies or basis*, or that a docstring
*carries no line number, issue number, certificate or falsity claim*. Those name neither a
hypothesis nor a declaration, so no register in this section governs them, and a sweeper working
from the old gloss reaches them with nothing to file. ⚠️ *"A single"* fails as well, on **6** of
the 40: `MulByNDegreeTower:27` names five, `WeilPairingTelescopeN:236` and
`WeilPairingTelescopeThree:216` three each, `WeilPairingTelescopeTwo:131`, `MulByTwoDegree:92` and
`WeilPairingProductRelationRootIndependentHprin:36` two each.

⚠️ **That retirement is the worked contrast to the `25` qualified above, and both came out of the
same PR.** Each was run through *"false or merely partial"* first and they answer differently:
a **count over a population that can grow under it** stays true of what it counted and is only ever
**short**, so the 25 took a qualification in place; a **universal** is falsified by a single
counterexample and this one had 16, so it takes a marked quotation. **Short is partial,
over-reaching is false**, and the two live one paragraph apart here so that the next census does not
have to guess which shape it is holding.
⚠️ **That scope is a retirement and not a reading.** The clause read *"a **count** stays true of
what it counted and is only ever **short**"* when it landed (`8fda8c4`, `#1756`, PR #698) —
unqualified, over every count — and **a count can over-reach**. The witness is on this page and
needs no tree: `### Gate-discharge claims`' *"bind `h2` (four also `h3`)"* stood over a population
of exactly **six** that the same sentence closes, and `h3` is bound by **three** of them, the three
whose names end `_three`, so there is no fourth row for the numeral to be true of. It is false
rather than short, and that section gives it a marked quotation. ⚠️ **What replaces the clause is
the question *what could move this numeral*.** If the only thing that can is the population growing
under it, growth never makes a count say more than it counted: it is only ever short and takes a
qualification in place. If the sentence itself pins the denominator — *k* of a row set it names —
then *k* can name rows that are not there, a *k* with no *k*-th row is **false**, and
`### Retired claims` binds. ⚠️ **The slogan survives the retirement and was never the defect**:
*"over-reaching is false"* is exactly what convicts the four. What the retired clause got wrong was
denying that a count can reach that half at all.
⚠️ **The retired words have one other live use, it is on the open branch, and that is what makes
this a scope rather than a deletion.** Whitespace-normalised, `stays true of what it counted`
occurs three times in this file at `d3a4ac5` and four at this commit: the scoped rule here, the
quotation of the unqualified form beside it, one use in the `1350` / `1352` paragraph of this
section whose count is over a telescope that grew under it, and — the fourth, and the reason the
figure carries both ends (`#1749`) — this sentence's own mention of the words, in the code span
that opens it. ⚠️ **The bare literal is the wrong instrument and that is why the transform is
named** (`#1749`): the quotation beside this rule wraps mid-phrase, so `grep -nF` returns two and
three where the normalised seed returns three and four, and a reader who runs the literal finds
neither figure. That one live use is scoped where it stands rather than retired, because a clause
applied on the branch that survives is a use and not a copy, and `### Retired claims` counts
retirements rather than occurrences (`#1811`).
⚠️ **The reading is argued and not assumed, because the two candidates cost differently.** Read as a
universal over counts the clause is **false**, one measured counterexample is enough, and
`### Retired claims` binds. Read instead as a claim about the two worked examples it stands
between, it is true of both, merely short of the wider class, and would take a qualification in
place with nothing retired. **The first reading is the one the sentence asks for**: it is written in
the same indefinite singular as *"a **universal** is falsified by a single counterexample"* one
clause later, which is unarguably about every universal and not about the one it stands over; and
the sentence closes by handing the slogan to *"the next census"*, which a rule scoped to its own two
examples would tell nothing. Hence the marked quotation rather than the softer disposition, and the
reading is recorded here because this front has had to settle it three times (`#1782`, `#1780`,
`#1790`).
⚠️ **Which branch a numeral is on is measured rather than assumed, and the pinned branch is the
larger one.** Seed, fence-aware over this file's own non-fenced prose: a `**`-bold span whose whole
content is a numeral, in digits or as an English number word. ⚠️ **The flags known to decide what
that returns are published here and none of them stood here until `#1864`**, which is why the
sentence was reimplemented five times and reproduced once before any of them did — a count that can
only grow, and the sixth reimplementation is what found the fifth flag: run from the four as
published it returned **154** at `2947444`, eleven short. ⚠️ **`known` is load-bearing**: the flags
that decide what the seed returns are a fixed set of unknown size — a fifth was found by running the
four — so *the* flags that decide would assert a closure nobody has checked, and a sixth would
falsify it exactly as the count it replaces is falsified below. What is published is what is known,
and a later flag extends that rather than breaking it. The match is **case-insensitive**, so the
sentence-initial `Seven`, `Three`, `Nine`, `Four` and `Eight` are in: the same regex read
case-sensitively returns **162** at `2947444` where this one returns 165, and **186** at `444da7f`
where this one returns 191 — the gaps are three and five rather than five and five because only
`Nine`, `Four` and `Eight` are there at `2947444`, `Seven` and `Three` arriving with PR #714, and
`Seven` is this paragraph's own worked example. The word list stops at `twelve`, so `Fourteen` is
out, and this is the flag the verdict below turns on, so it is measured rather than asserted:
admitting `fourteen` adds exactly one at every dated ref, which turns 165 into the **166** this
paragraph retires but turns the seven readings that do reproduce into **176**, **185** and **192**.
⚠️ **A recogniser wrong in that direction would be wrong at every ref, and seven of the eight are
exact** — that is what makes the verdict *the count was wrong* rather than *the recogniser was
wrong*, and without it the two are equally available. `**zero**` is matched. And the seed is
fence-aware but **not** inline-code-aware, so a `**zero**` written inside backticks counts too, and
one of that 191 is this paragraph's own. ⚠️ **Bold spans are paired over the whole document and not
line by line**, which is the flag the four above did not include: this file wraps a bold span across
a line break, and on the line that closes one the first `**` is a closer and not an opener, so every
`**` after it on that line pairs one position out — **287** lines at `2947444` and **405** at
`444da7f` carry an odd number of them. A line-keyed regex returns **154** and **182**; a
document-wide non-greedy one returns **156** and **180**. ⚠️ **They are short by 11 and 9 and by 9
and 11 — the two miss in opposite amounts**, which is the inconsistent direction of disagreement
`#1864` was filed on, now with a mechanism under it rather than a missing rule. A CommonMark parse
pairs them correctly and is what every figure this paragraph attributes to **the seed** was run on;
the **154** / **182**, the **156** / **180** and the two odd-`**` line counts are what the three
other instruments return, and are named as theirs rather than as the seed's.
⚠️ **AND THAT CLAUSE IS WHERE THE RECIPE STOPS SHORT, because a CommonMark parse ALONE implements
four of the five flags** (`#2080`): to such a parse a backticked bold numeral is a single
`code_inline` token and not a bold span at all, so an implementation keyed on `strong_open` /
`strong_close` cannot see the inline-code flag's population however carefully it reads the clause
that states it. **The count is two passes summed** — the bold spans that parse pairs, plus a
`**`-delimited numeral matched literally inside every `code_inline` token. What every figure here
publishes is the sum, which tells a reimplementation the total it missed and never which pass, so
the split is published too: at `9147113` the first pass over this file returns `296` and the
second `4`, and `c28c462`'s own message publishes their sum as `300`. ⚠️ **Calibrate at `d3a4ac5`,
or at a ref after it, or you have not calibrated**: the second pass returns `0` at `2947444`, so a
one-pass reading reproduces the `165` this paragraph dates there and is short at every dated ref
after that one — by `1` at `e80a588`, `0eb4f70`, `d3a4ac5`, `5a2fe24`, `b2d1981`, `444da7f` and
`3c183d8`, and by `4` at `77fb54d`, at `9147113`, at `c28c462` and at `93cf1d4`. Every site it
misses is the word `zero`, so the one-pass reading is exact in digits and short by that same count
on the word form and on the total. ⚠️ **Nothing published at `93cf1d4` that this page or a commit
message attributes to the seed is a one-pass value, and that was read rather than assumed**
(`#1749`): `18` of the `728` commit messages reachable from `93cf1d4` name this seed, keyed
case-insensitively on `bolded.numeral` over the whitespace-flattened body, and all `18` were read.
The one one-pass pair among them is in `c28c462`'s own message, which quotes it from PR #777 and
prints it at `+4` of its own — naming the gap, and not the flag that is its cause.
⚠️ **Retired — a count of the flags, and it was one too low** (`#1864`): this sentence read
*"Four flags decide what that returns and none of them stood here until `#1864`"*, bold across the
whole clause in the original and wrapped after *that*, so a single-line `grep` for it returns 0 and
the check is whitespace-normalised. The pairing rule is a fifth. The numeral is dropped rather than
raised, which is the remedy `#1864` names for a figure its own sentence does not need — publishing
the flags is what a re-runner needs and counting them buys nothing. Under the flags above the seed
returns **165** at `2947444` and **175** at `e80a588`, which is PR #714's head.
⚠️ **Retired, and it is the count that was wrong and not the recogniser** (`#1864`): this paragraph
read *"**166** occurrences"* at `2947444`, where the seed returns **165**, so `### Reach clauses`'
own test returns **false** rather than partial and the figure retires here — it is a claim about
this page's own population, published on this page. ⚠️ **Every other dated reading this page gives
for this seed reproduces to the digit** — seven of them, at `e80a588`, `d3a4ac5`, `0eb4f70`,
`5a2fe24`, `b2d1981`, `444da7f` and `3c183d8` — both ends of each of the three
`### Scope of the rules above` bullets that re-run this seed, and the head this paragraph's own
*"**nine** more than the 166"* was written against. So the base figure alone was one too high, and
that clause is **ten** more than the 165.
⚠️ **The split retires with it, because it was a partition of the 166 and not three lists.** It
read *"**Seven** are not counts over a population at all … of the remaining **159**, **51** are
dated totals a recogniser returned over the tree and **108** are counts inside a set the same
sentence names"*, and 7 + 159 = 166 with 51 + 108 = 159; at a true total of 165 exactly one of the
three is one too high, and nothing on record says which, because the reading published counts and
never the rows. ⚠️ **What the split was written to establish survives it**: the pinned branch is
the larger one however the row comes off, since the three ways it can are 108 of 159, 108 of 158
and 107 of 158, and every one of them is about two thirds.
⚠️ **Recogniser limits, published beside the count because the count depends on them** (`#1749`):
the seed is bold-keyed and the witness that falsifies the rule is **not** bold — *"four"* was
written bare — so it cannot find the defect it was written for. ⚠️ **Retired — the only claim in
this paragraph to go that is a rule rather than a count** (`#1864`): it read
*"`**zero**` and `**once**` are number-shaped words the pattern omits"*. `**once**` is; `**zero**`
is not, and excluding it drops every dated figure by exactly its own occurrence count — **165**
becomes 163 at `2947444` and **191** becomes 188 at `444da7f`, against **2** and **3** occurrences —
so the published numbers count it and a reimplementer who obeyed the clause lands low by that much
at every dated ref. And open against pinned is read off each sentence, so the split was a reading
and re-running the regex is not the check. ⚠️ **The ordinal that headline carried is dropped rather
than raised**: it read *"the third claim in this paragraph to go, and the only one of the three"*
from `4655854` (`#1864`, PR #734) and was true until the flag-count retirement above was written
into the same paragraph — a numeral standing over a list is falsified by whatever next extends the
list, and no clause under it can repair the numeral, which is the answer this section gave for its
own discriminator list and `### Scope of the rules above` gave for its own.
⚠️ **There are four; the third is in `### Gate-discharge claims`** (`#1765`, `#1780`): a
universal that **survives its first measurement** is neither short nor over-reaching, and what it
takes is the measurement itself, published where the claim stood. That is a **pointer and not a
copy** (`#1766`) — the paragraph stays over there because its own remedy is *publish it where the
claim stood*, so moving it here would falsify the rule by the act of stating it. ⚠️ **The slogan
is untouched**: neither half of it is falsified by a third shape, since a shape that is neither
short nor over-reaching is outside both. What was short is *"the two"* — a count of the shapes
stated here, over a class that grew under it rather than one this page closes — so this is the
qualification in place the open branch prescribes, and **nothing retires**. ⚠️ **The fourth is
the over-reaching count the retirement above is written on**, and it belongs here rather than over
there because its subject is this section's own rule: a count whose denominator its own sentence
pins can fail its measurement, where the third shape is a universal that survives one. **Three**
went short exactly as *"the two"* did, on the same open branch and for the same reason, and takes
the same qualification.
⚠️ **The third shape is general, not gate-specific**: its discriminator is the claim's own form, a
count or a universal, together with what the measurement returned, and neither of those mentions a
register; the paragraph carrying it sits under a gate heading because that is where the claim it
repaired stood. **This section holds a standing instance of its population** — *"A reach clause
about a declaration whose file the writer is not editing is covered by no register in either file,
and no review of the defining module ever looks at it"* above is a universal over registers and over
reviews, carrying no count, no sha and no recogniser, where every other population claim in this
section carries all three. Measuring it is `#1794`, not this pointer. ⚠️ **`### Retired claims` gets
no second pointer**: it delegates this test rather than restating its branches, so the list is
complete there as soon as it is complete here. ⚠️ And this **unmeasured** is not the one above —
that one is a *row* a seed cleared on an axis nobody read, this one is a *claim this page makes
about its own population*. ⚠️ **The seed is also boundary-anchored**: written as the bare literal
`carries no` it returns **60** hits in **51** files rather than 56, so the list above publishes
``carries no\b``. A published recogniser that does not return its published count is `#1749`'s
defect, one notch smaller.

⚠️ **A clause that points *and* names is not on this branch**, which is what separates those two
counts. *"with the same hypothesis `ΨSqₙ(x) ≠ 0` that … `hasXCoordFormula_of_two_ne_zero` asks of
the `x`-half"* (`EllipticCurves.Torsion.NsmulYPeriodic`) and *"at **every** prime `p` with
`(2 : F) ≠ 0` and `(p : F) ≠ 0` — the same pair as the display above"*
(`EllipticCurves.Torsion.StructureGeneral`) are ordinary reach clauses with an attribution
attached: they carry their own list, so the paragraphs above measure them directly and nothing has
to be resolved elsewhere. The branch is for the clause that points **instead of** naming.

⚠️ **Completing such a clause does not retire anything.** *"at every nonzero index"* is not
falsified by *"at every nonzero index with `(2 : F) ≠ 0`"* — the words stay and a condition is
added — so `### Retired claims` does not bind, and `#1659` added no marked quotation at any of its
sites for that reason. ⚠️ Contrast `#1660`, where *"at every `n`"* over a binder
`xCoord_zero` falsifies at `n = 0` **was** false and each replacement was quoted and attributed.
**Read whether the old clause was false or merely partial before deciding.**

⚠️ **That test has been run on *"over an arbitrary field"*, and the answer is *partial*: the phrase
denies a structural assumption on `F` and composes with a `with` clause, so it takes an insertion
and retires nothing** (`#1733`). Recogniser: the case-insensitive literal *"over an arbitrary
field"* in the **headline** of a `/--` block of an `EllipticCurves/**/*.lean` file, headline meaning
the block text `**`-stripped and whitespace-normalised, cut at the first `.` followed by optional
bold, code-span, bracket or quote marks and a space, or at the first ⚠️, whichever comes first. At
`2765fc9` the phrase occurs **211** times in **63** files — **96** `/--` blocks and **77** `/-!`
blocks — and **88** occurrences fall inside a `/--` headline. Joining those 88 to their declarations
and reading every `(2 : F) ≠ 0`, `(3 : F) ≠ 0`, `((n : ℤ) : F) ≠ 0`, `(n : F) ≠ 0`,
`[IsAlgClosed F]`, `[CharZero F]`, `[PerfectField F]` and `[Fintype F]` binder **in scope** — own
list plus every `variable` line above the block — splits them **57 / 8 / 23**: 57 bind a condition
on `F` the headline does not name, 8 already carry the completion, and 23 bind nothing about `F`
and are true as written.  After `#1733` the split is **47 / 18 / 23**.

⚠️ **The 8 decide it, and they decide it against the closed reading.**
`sum_ramificationIdxN_mul_residueDegreeN_of_isSeparable`
(`EllipticCurves.FunctionField.MulByNInertia`), `**`-stripped as the recogniser reads it, is
*"`∑_{p ↦ q} e_p · f_p = n²` for `[n]∗` at every `3`-smooth `n ≠ 0` with `(2 : F) ≠ 0` and
`(3 : F) ≠ 0`, over an arbitrary field, with separability carried as a hypothesis."* — the phrase
and a `with` clause naming two conditions on `F`, in one headline, and
`…_of_isSeparable_of_ne_zero` below it does the same at `(n : F) ≠ 0`. If
*"over an arbitrary field"* closed a list about `F`, those two headlines would contradict
themselves in their own text. They do not, because the phrase denies a **structural** assumption —
an algebraic closure — and the tree glosses it in exactly those words itself:
`exists_nsmul_three_eq_some_of_root` (`EllipticCurves.Torsion.TriplingSurjective`) ends its headline
*"with no algebraic closure"*.

⚠️ **The closed wordings are a different phrase and they do retire**, so do not read this ruling
across to them. *"Nothing else about `F` is assumed"* and *"the hypotheses are `hcard` and `hP` and
nothing else about `F`"* (`dcc912e`, `#1339`, PR #508) were both ruled **false** and quoted under
`### Retired claims` by PR #687 (`#1719`) — in the same file, one paragraph from the ten
*"over an arbitrary field"* headlines that took a completion under `#1733`. *"Nothing else"* closes
the list; *"arbitrary"* does not.

⚠️ **The 57 are a population to read, not a verdict, and only ten of them are repaired.** `#1733`
completed the ten in `EllipticCurves.FunctionField.PullbackPrincipalityTwoRationalTorsion` — in
that file's own wording, *"over an arbitrary field with `(2 : F) ≠ 0`"* — leaving **47** in eleven
files, filed rather than swept. At least one will clear on a reading rather than a count:
`exists_weilPairingElt_self_eq_one_of_smooth_of_baseChange`
(`EllipticCurves.FunctionField.WeilPairingAlternatingBaseChangeN`) closes its headline *"with
`hprin` the only hypothesis that is not about the characteristic"*, which tells the reader the
characteristic conditions exist without naming them, while its neighbour of the same shape at
`…_of_ne_zero_of_baseChange` names `(2 : F) ≠ 0` and `((n : ℤ) : F) ≠ 0` outright. ⚠️ **A module
H1 cannot always take the insertion**, and that is the one place this ruling and the heading rule
below pull apart: completing `PullbackPrincipalityTwoRationalTorsion`'s title in place makes it
**117** columns, so the phrase was dropped from the title to the prose instead, on
`### Scope of the rules above`'s heading bullet.

⚠️ **Rule a phrase before repairing rows of it when the repair is a `with` clause hung off the
phrase, and not before otherwise** (`#1733`). This is the cost that ruling makes visible rather
than a rule invented for it: **three PRs inside four hours** on 2026-09-05 — `fddba5c`
(`#1664`, PR #684), `2765fc9` (`#1719`, PR #687) and `#1733`'s own — repaired rows of
*"over an arbitrary field"* in one file, each correct under its own issue, and the file stood in
**two registers** on one phrase in between. A repair that merely *appends* conditions a headline
names nowhere is safe to make before the phrase is classified, because naming every hypothesis is
compliant on any reading.
⚠️ **Appending to the phrase is not that repair.** *"over an arbitrary field with `(2 : F) ≠ 0`"*
is compliant only on the *partial* reading; had the phrase come out **closed**, the same words
would assert and deny a condition on `F` in one clause, and the repair owed would have been a
deletion with a marked quotation instead. **Ask whether the words you are adding lean on the
phrase's classification. If they do, rule it first; if they do not, repair now.**
⚠️ **This narrows *"an insertion is branch-neutral"* above (`#1728`) rather than contradicting
it, and the two are one rule read together.** That sentence is about an insertion of conditions the
headline names **nowhere**, which is compliant on both branches of *"names every hypothesis, or it
names none"*. The move it does not cover is an insertion **hung off a phrase whose own
classification is the open question** — there the added words inherit the phrase's reading, so the
result is compliant on one branch and self-contradictory on the other. Branch-neutrality is a
property of the **repaired sentence**, not of the act of inserting.

### Gate-discharge claims

A third exemption is narrower still, and it has a different shape: it is not about which
hypotheses a clause omits but about **what kind of claim the clause is making**.

A **gate-discharge claim** says that a statement is owed *nothing further* — *"with `#E[p] = p²`
as the only hypothesis"*, *"with no hypothesis left"*, *"unconditionally"*. It is not a hypothesis
list. It is a claim **relative to a gate list**: the hypotheses that some *other* declaration or
module records as owed, and which this statement has discharged. Read as a reach clause it is a
false universal, and a bolded one; read as what it says it is usually exactly true, and sharper
than the list it would be replaced by.

**A gate-discharge claim is bound by the reach-clause rule only where the gate list it is relative
to is not named.** Where the docstring does name it, the claim is compliant and the completeness
obligation *moves*: the naming sentence is then held to the rule the headline was let off, and
must name every explicit hypothesis of the statement.

```
-- right: `nonempty_torsionPow_addEquiv_of_odd` (`EllipticCurves.Torsion.PrimaryTowerOdd`) binds
-- `h2`, `hp : p.Prime`, `hodd`, `hpF`, and its headline names two of the four
**The structure theorem for `E[pᵏ]` at an odd prime `p`, with no hypothesis left.**
This is the signature `EllipticCurves.Torsion.PrimaryTower`'s gate list reduces to once
`card_torsion_eq_sq_of_odd` supplies `hcard`: over an algebraically closed field with
`(2 : F) ≠ 0`, at an odd prime `p` with `(p : F) ≠ 0`, ... is owed nothing further.

-- wrong: `card_torsion_pow_of_odd` read *"at an odd `p`, unconditionally"* over the same field
-- and index hypotheses, and named no gate list.  Its next sentence made a hypothesis-*list*
-- claim instead — *"asks of `p` only that it be odd and nonzero in `F`"*, which is itself short
-- of `h2` — so nothing in the docstring gave the word a subject.
```

The repair there was to **re-scope the word rather than delete it**: *"with `(2 : F) ≠ 0`, at an
odd `p` with `(p : F) ≠ 0`, and with no `hcard`"*. That is the cheapest form of a gate-discharge
claim and the one to prefer — it names the discharged gate **inside** the clause, so it is
compliant on either reading and needs no second sentence to prop it up.

⚠️ **In the same docstring is the whole of the exemption.** *Declaration headlines are reach
clauses too* below is unchanged by it: a `## Hypotheses` section elsewhere in the module does not
repair a partial headline, because doc-gen renders the rest of *this* docstring beside the
headline and the module block nowhere near it.

⚠️ **A gate-discharge register is a per-file object, and a sweep sees per declaration.**
`EllipticCurves.Torsion.PrimaryTowerAlgClosed` runs one from its H1 (*"`#E[p] = p²` is the only
hypothesis left"*) through its module block and down into the declaration headlines, and factors
the field conditions out into a `## What the substitution costs` section of its own, on purpose.
Repairing one headline of such a file in isolation is a worse outcome than repairing none. Before
repairing a headline whose omitted hypothesis is named in a section like that, read the module
block: the decision on offer is about the file, not the row.

⚠️ **And a per-front one: *"the setting"*.** The whole `WeilPairing*` front writes a gate-discharge
claim in the words *"with no hypothesis beyond the setting"*, and `grep` finds no definition of the
term *as such* anywhere in the tree. Read as a hypothesis list the sharpest of them —
`exists_weilPairingElt_mul_swap_eq_one_two`, which binds `(2 : F) ≠ 0` and six point hypotheses —
is a bolded false universal. It is not one. ***"The setting"* is this development's word for a
gate list**, and `EllipticCurves.FunctionField.WeilPairingGaloisRoot` says so in the one sentence
in the tree that comes near a definition:

> *"It is the pairing's own setting — `e_n` is a pairing on `E[n] × E[n]` — and not a gate carried
> in from elsewhere; in exchange the caller supplies no rung-5 data and no `hpow` proof."*

So the setting is the ambient `variable` block, the front's standing characteristic hypotheses,
and **the data the statement is about** — the points, their torsion, and the group relation among
them. What the clause claims is that no **gate** is carried: no `hprin`, no product relation
`hprod`, no caller-supplied root, no rung-4/5 certificate. That is checkable, and the test is one
question of the signature — *does it bind a gate the clause says is gone?*

⚠️ **This is the one exception to *"in the same docstring is the whole of the exemption"* above,
and it is narrow.** *"The setting"* is a term **this document defines**, not prose sitting
elsewhere in the module: a reader who meets a defined term looks it up once and is then equipped
for the whole register, where a reader who meets a partial hypothesis list has no signal that a
completing sentence exists anywhere. That asymmetry is the whole of what earns the exception, so a
phrase a file coins for itself earns nothing here — until a term is defined in this section, it is
module prose and the boundary above applies to it unchanged.

⚠️ **And the completeness obligation does not move to a second sentence here — it moves to the
signature test.** Under *"the naming sentence … must name every explicit hypothesis"* above,
`exists_weilPairingElt_mul_swap_eq_one_two` would still be a defect: its docstring is the headline
plus one ⚠️ about why `R = S ⊕ T` need not be assumed `2`-torsion, and no sentence in it names the
statement's seven explicit hypotheses (the ⚠️ names three binders in passing, inside a remark about
the proof, and never `h2`). What discharges it instead is that the clause is a claim about
**gates** and the signature carries none. The hypothesis count is the signature's job, which is
what the ⚠️ below already says — so for this register the signature test *is* the obligation, and
demanding a naming sentence as well would convict the whole register for not restating what
doc-gen prints beside them.

```
-- right: `exists_weilPairingElt_divisorSlot_add_two` binds `h2` and eight point hypotheses, and
-- no gate — it produces its three roots — so the clause is true of what it is a claim about
Divisor-slot bilinearity at `n = 2`, over `F̄` with no hypothesis beyond the setting.

-- right: `exists_weilPairingElt_divisorSlot_add_of_smooth_of_hprin` does bind `hprin`, and says so
Divisor-slot bilinearity at every `3`-smooth `n ≠ 0`, with `hprin` the only hypothesis beyond the
setting.

-- wrong: the same clause over a signature that still carries `hprin`, `hprod` or a root the
-- caller supplies.  Naming the carried thing is what the compliant form above does.
-- Two live instances, and they clear on this remedy rather than on the shape being absent:
-- `weilPairingElt_mul_swap_eq_one_two_of_isAlgClosed` and its `_three` twin (`#1781`, below).
```

⚠️ **The line that stood in that code block is retired, and it was false at the commit that
published it.** It read *"No live instance, and that is the point: the register is self-policing
across the whole front, with the word "no" never standing over a signature that carries a gate"*,
measured on `#1571` and published at `685d755`. Two rows falsify it, and both predate it by eleven
days (`bb81ce0`): `weilPairingElt_mul_swap_eq_one_two_of_isAlgClosed` and
`weilPairingElt_mul_swap_eq_one_three_of_isAlgClosed`
(`EllipticCurves.FunctionField.WeilPairingProductRelationRootIndependent`) say *"over an
algebraically closed field with no hypothesis beyond the setting"* over signatures binding `hdS`,
`hdT`, `hgS`, `hgT`, `huS` and `huT` — a divisor certificate and a rung-5 relation on a root **the
caller supplies**, which is the third item of this section's own gate list. ⚠️ **Both rows clear
all the same**, on the eight `_of_hprin` rows' own remedy above: each names the carried thing —
*"for roots the caller supplies"* — in the same sentence as the clause. Splitting them off from
those eight is not available either, since `weilPairingElt_mul_swap_eq_one_three_of_hprin`
(`EllipticCurves.FunctionField.WeilPairingProductRelationRootIndependentHprin`) cites the second of
them by name and `### Scope of the rules above` forbids two blocks answering one question in
different registers. **What was false is the sentence, not the register**: the remedy clears rows,
and a universal quantified over *signatures* is not repaired by what a docstring names.

⚠️ **The census below cannot see this shape at all, which is why the line survived.** Its seed is
`` the only (gate|hypothes\w*) ``, and *"with **no** hypothesis beyond the setting"* does not match
it, so no row of this shape is among the 95, and `#1765`'s signature test over the 76 rows of
buckets one and two reached none of them — **including this section's own worked *right* example**,
`exists_weilPairingElt_divisorSlot_add_two`. Measured at `4efeb97` with the headline rule above and
the seed `` no (gates?|hypothes\w*) … beyond the setting ``: **32** declaration headlines carry the
shape, across **11** files, every one a `theorem`. Six further matches are `/-!` blocks — two `###`
sub-headings standing over rows already counted (`WeilPairingTranslationSlotHom` and
`WeilPairingTranslationSlotNondegenerate`), and four the headline cut running past an H1 that
carries no full stop, onto prose about *another* module's declarations — and one `/--` block
(`WeilPairingAlternating`) carries the phrase **below** its headline, in the same kind of prose.
⚠️ **The population is 32 and not 33**: keyed on the phrase anywhere in a `/--` block it is 33,
and the extra row is that last one, which makes no claim about its own signature.

⚠️ **Run over the 32, this section's own test convicts the two above and clears the other 30.**
Gate-shaped is read as `#1765` read it — an explicit binder whose type mentions a divisor, an
endomorphism, a root, a division-polynomial identity or `hprin` itself — and the recogniser is
calibrated by re-deriving that paragraph's **13 of 67** over its own 76 rows, returning the same
thirteen declarations. ⚠️ **A `•` beside an identifier beginning `g` is not a root**: the nine
`_of_hprin_n` rows binding `hn : Transcendental F (n • genericPoint …).xCoord` match such a seed
and are transcendence hypotheses, and a predicate that takes them returns **22** where the page
publishes 13. The 30 that clear bind nothing but `(2 : F) ≠ 0`, `(3 : F) ≠ 0`, the nonsingularity
or equation of their points, those points' torsion, the group relation `hadd`, on
`WeilPairingGaloisRoot`'s four the automorphism `σ` the conclusion is about together with the
`[IsAlgClosed F]` the other 26 take from a `variable` line, and on
`WeilPairingAlternatingTwoAlgClosed`'s and `WeilPairingAlternatingThreeAlgClosed`'s `μ` rows the
index `(n : ℕ)` with its `[NeZero n]`. ⚠️ **Both binder lists here — this one and `#1781`'s six in
the paragraph below — are over what a row writes at its own `theorem` line, the points' coordinates
aside** (`#1790`), and the scope is stated because a list closed over the elaborated telescope
would have to name the ambient `variable` blocks — which are the setting by this section's own
definition of it — and those coordinates, implicit at the declaration on **20** of the 30. The
characteristic hypotheses, the points, their torsion and `hadd` are named in this section's own
description of the setting, so on those the 30 are compliant on it in terms rather than by an
exemption. ⚠️ **`σ`, that `[IsAlgClosed F]` and the index pair are not, and they clear on the test
rather than on that enumeration**: the clause is a claim about **gates**, and an automorphism, an
algebraic closure, an index and a `NeZero` on it are none of `hprin`, `hprod`, a caller-supplied
root or a rung-4/5 certificate. The two grounds are not interchangeable and the setting's
enumeration does not reach every binder, which is why the test this section sets is the signature
question and not the list.

⚠️ **That settles `#1781`'s six, and settles them clear with no `.lean` diff.**
`WeilPairingAlternatingTwoAlgClosed`'s and `WeilPairingAlternatingThreeAlgClosed`'s
`_of_isAlgClosed` pairs and `WeilPairingRootIndependenceAlgClosed`'s two bind `h2` (three also
`h3`, and they are exactly the three whose names end `_three`), `h : W.Nonsingular …`, `htors`, and
on the two `μ` rows the index `(n : ℕ)` with its `[NeZero n]`, and nothing else: `h2` and `h3` are
the front's standing characteristic hypotheses, and `htors` is *"the data the statement is about —
the points, **their torsion**"*, both named in the description of the setting above, and the index
pair clears on the gate test as `σ` does. ⚠️ **`htors` clearing here is not `htors` clearing on the
reach axis**, and neither may be quoted as the other: the paragraph below says in terms that *"the
data the statement is about"* describes a **gate list** and is not a second route to clearing a
data hypothesis from a reach clause, where `htors` is reach by name. `#1774` had already cleared
the reach half of the same six on a different ground — their only reach phrase is an instance
mention, so they name none — so both halves are answered and neither answer carries to the other.

⚠️ **Both lists above were short of `(n : ℕ)` when they landed, and completing them retires
nothing** (`#1790`). `exists_weilPairingMu_self_eq_one_of_isAlgClosed_two` and its `_three` twin
bind the index and its `[NeZero n]` in their own `theorem` lines; neither is gate-shaped, so no
verdict moved — but both clauses **close** a list, which is the shape `### Module-block bullets`
names in terms (*"from nothing but"*, *"and nothing else"* … *"claims about the hypothesis list
itself"*), here over a list that carries data binders as well, and a reader checking either against
a signature would have found it short. ⚠️ **`### Reach clauses`' *"false or merely partial"* test
decides the disposition, and it is worth showing on this pair**, because a clause on this same axis
was retired in that section on the same day and this pair is not it. Its criterion is *"Completing
such a clause does not retire anything … the words stay and a condition is added"*: here the words
stay and the missing binders go **into** the list, so `### Retired claims` does not bind and
neither list owes a marked quotation. Contrast the clause PR #707 retired — PR #706's *"takes no
instance from a `variable` block **at all**"* — where completing it meant striking *"at all"* and
re-scoping the *"no"*, so its own words could not survive the repair. ⚠️ **That is the
discriminator, and it is cheaper than counting counterexamples**: ask whether the clause can be
completed by extending its own list, or only by deleting its own words.

⚠️ **It does not reach a wrong cross-reference, and `### Retired claims` does not bind one.**
*"the discriminator below"* over a target that is above cannot be completed by extending anything,
so read literally this discriminator answers *delete* and sends a one-word direction error to that
section for a marked quotation. The ground that section gives is that a reader who remembers the
old claim learns why it went — and no reader carries a direction word out of a previous reading,
because a pointer asserts nothing about a declaration, a hypothesis or a population. It is an
instruction for finding text that is on the page whichever way it points, so **the word is corrected
in place and nothing retires**. ⚠️ The exemption is for the **direction** and not for the clause
carrying it: a sentence that points *and* asserts is still read for its assertion, on the
assertion's own terms. The measurement that produced this ruling is in
`### Scope of the rules above`, which is where one of the two rows it clears sits.

⚠️ **A wrong distance takes the same exemption as a wrong direction, and the two rows repaired
under it were both distances** (`#1811`): *"one section down"* for a section three sections down,
and *"two paragraphs up"* for a target in the same paragraph. Neither asserts anything about a
declaration, a hypothesis or a population, and no reader carries a distance out of a previous
reading either, so both are corrected in place and nothing retires. ⚠️ **The prospective half is
the part worth having: prefer a direction to a distance, and a heading's name to both.** A distance
is falsified by any insertion between the pointer and its target, so it rots with nobody touching
either; a direction survives everything but a move, and a name survives that too. Both repairs
apply it — one drops its count rather than correcting it — and it governs what is written next
rather than what is on the page: *"two sections down"* in `### Reach clauses` is right today and is
not convicted by preferring the other form.

⚠️ **It does not reach a wrong sha on the ground stated for a direction, and it reaches an
attribution sha on a different one** (`#1819`). A sha points at a commit and not at a place in this
file, so *"an instruction for finding text that is on the page whichever way it points"* cannot
carry it: at the wrong commit the text is not there, and
`git show d3a4ac5:README.md | grep -c "about a module docstring"` returns 0 for a gloss that landed
at `0eb4f70`. What carries instead is that an attribution sha never travels alone — the `PR #n`
beside it names the same commit a second time, so the reader is handed the target twice and one
wrong half cannot strand them, which is true of both rows PR #716 repaired. ⚠️ **That ground splits
the axis rather than covering it**: a sha with no PR number beside it is the sole address of what
its sentence measures, and that sentence asserts a figure *at* that commit, so this exemption's own
caveat — *"still read for its assertion, on the assertion's own terms"* — governs, and
`### Retired claims` binds it. ⚠️ **The convention was enforced against a PR twice before it was
written here** (`#1749`): an attribution sha is the commit where the clause **landed**, which is
that PR's own merge and not the merge before it. Fence-aware over this file's non-fenced prose at
`5a2fe24`, with a `` `[0-9a-f]{7,40}` `` inline code span a citation and a citation within 40
characters of a `PR #n` in the whitespace-joined text an attribution: 69 citations, 40 distinct,
40 of 40 resolving under `git cat-file -t`, and 23 paired, every one read. One of the 23 is
`### Module-block bullets`' *"was live at `ee0b8a4`"*, a measurement at the merge before PR #667's
and right to be there; the other **22 of 22** are on the convention. The population is
window-sensitive and the verdict is not: at 70 characters `5a2fe24` gives 25 rows with that same
single row the only one off it. ⚠️ **This paragraph is inside its own population and carries both
ends for it** (`#1749`): at this head the census reads 73 citations and 41 distinct, the
40-character figure is unmoved at 22 of the 23 paired, and at 70 characters this paragraph's own
quotation of that row is a second row off the convention — quoting a measurement sha reproduces its
shape, which is why a census of this axis is dated rather than standing.

⚠️ **One figure in that account was not short but wrong, and it takes the other branch.** The
sentence above read *"bind `h2` (four also `h3`)"* when it landed (PR #708, `5018e25`); `h3` is
bound by **three** of the six — the three whose names end `_three`, whose `theorem` lines are
`WeilPairingAlternatingThreeAlgClosed:125` and `:149` and
`WeilPairingRootIndependenceAlgClosed:184` and whose docstrings open at `:115`, `:137` and `:174` —
and none of the three files' `variable` blocks carries a characteristic hypothesis, so the other
three bind `h2` and no other condition on the characteristic. ⚠️ **The numeral over-reaches rather
than falling short**: it counts a fourth row over a population of exactly six and there is no
fourth, so *"short is partial, over-reaching is false"* in `### Reach clauses` sends it to
`### Retired claims` and it takes a **marked quotation** — where PR #707's **1350** and **1335**
take a qualification in place, because those under-report and stay true of what they counted. The
extend-or-delete discriminator gives the same answer in the other vocabulary: a numeral that
over-reaches cannot be completed by extending anything, only replaced. It is marked here rather
than in the three files it is about because the claim is this section's account of why those rows
clear and no docstring of theirs says it, which is `#1694`'s subject test applied as PR #707
applied it above. ⚠️ **No verdict moves**: `h3` is a standing characteristic hypothesis on either
count, the six still clear, and `#1781`'s *"no `.lean` diff"* stands.

⚠️ **The count rule in `### Reach clauses` now covers this case, and this paragraph cites it
rather than restating it** (`#1799`). That rule was unqualified when this row was convicted, and it
is retired there: it is scoped to a count over a population that can grow under it, and given a
second branch for a count whose denominator its own sentence pins. The *"four"* of the six is that
branch's worked case, so the disposition above is what the rule prescribes and no longer something
this paragraph decides for itself — which is why it is a citation, `### Scope of the rules above`
forbidding two blocks answering one question in different registers. ⚠️ **It is still not the
third shape the pointer up there names**: that one is a universal that **survives** its measurement,
and this is a count that does not, which is the fourth item in that section's branch list.

⚠️ **It is not a licence to say the signature is short.** *"Beyond the setting"* says nothing about
how many hypotheses a statement has and everything about which gates it does not carry; a reader
who wants the count reads the signature doc-gen prints beside the docstring. A headline that omits
`(2 : F) ≠ 0` while making a plain hypothesis-list claim is not rescued by this paragraph. The
boundary is the `card_torsion_pow_of_odd` one above: the word has to have a subject.

⚠️ **The register's own population was measured on `#1754`, and the largest part of it is `example`
blocks that a noun-keyed census convicts wrongly.** Over `EllipticCurves/**/*.lean` with the
headline rule above and the seed `` the only (gate|hypothes\w*) ``: **95** headline occurrences at
`5cfd485`, splitting **53 / 19 / 23** — noun it *gate*, noun it *hypothesis beyond the setting*, or
noun it *hypothesis* with no gate list named. ⚠️ **The noun buckets a row in either number**:
`gates` folds into *gate* and *hypotheses beyond the setting* into its singular. **5** of the 95 are
plural, so keying the buckets on the literal singular drops all five and returns **52 / 15 / 28**
and **56 / 15 / 24** where this paragraph publishes 53 / 19 / 23 and 57 / 19 / 19, and a re-runner
concludes the seed is broken when it is the bucket names that are (`#1766`). ⚠️ **The
`card_torsion_pow_of_odd` repair below moves the four `…AssemblyN` rows out of the third bucket and
into the first, leaving 95 splitting 57 / 19 / 19.**
The total is invariant and each split holds only at the sha named beside it: re-run the seed before
that commit and it returns **53 / 19 / 23**, after it **57 / 19 / 19**. A census figure this page
publishes and then moves in the same breath has to carry both, or the recogniser reads as broken
(`#1749`). The first two buckets are the compliant forms, and they stay two: the paragraph below
rules that the per-block clause does not fire between them, so there is nothing to converge
(`#1754`). **Fourteen of the third bucket are non-vacuity `example` blocks** —
fourteen of the 23 before the repair, of the 19 after — over a concrete curve (`ℚ`,
`exampleField`), and for **eleven** of them *"with `hprin` the only hypothesis left"* is a
hypothesis-**list** claim that is literally true: `hprin` is their whole top-level binder list.
⚠️ **The other three bind an automorphism and an equation proof besides** —
`WeilPairingGaloisRootHprin`'s two and `WeilPairingGaloisRootN`'s one, each of the shape
`example (σ : …) {x₂ y₂ : …} (h₂ : … .Equation x₂ y₂) (hprin : …)` — so they are true on the
*setting* reading and not on the count. **The test is the declaration's top-level binder list, not
the block's shape**: a census keyed on `example` clears three rows it has not read, and one keyed
on the noun alone convicts eleven it should not.

⚠️ **That the first two buckets are compliant is measured rather than asserted** (`#1765`), and this
paragraph is what replaced the assertion. The section's own test — *does the signature bind a gate
the clause says is gone?* — was run over all **76** rows of those two buckets at `f317634`, reading
an explicit binder as gate-shaped when its type mentions a divisor, an endomorphism, a root, a
division-polynomial identity or `hprin` itself, which is what makes the four items of the gate list
above one test. **Nine** of the 76 are module-block headlines and have no binder list for it to
read; the other **67** are declarations, and **13** of those bind a gate-shaped hypothesis besides
`hprin`. **Five name it as the clause's own subject** — `OmegaPairCoprime:304`'s `hid`,
`WronskianRecurrence:360`'s `hC1` and `hC2`, `WronskianUniversal:255`'s `h`, and
`WeilPairingAlternatingConsumerN:171` and `:194`, which name `htel`, `hpow`, `hg`, `hc` and `hc₀`
one by one. ⚠️ **The other eight are the only rows in the register whose clause names a gate that
does not exhaust the signature's**, and they are `WeilPairingProductRelationRootIndependentHprin`'s
`_of_hprin` family: *"with `hprin` the only gate"* over a signature that also takes the caller's
`fS`, `fT`, `gS`, `gT` with their divisor and root certificates. **They clear on the wrong example's
own remedy** — each says *"for roots the caller supplies"* or *"for supplied roots"* in the same
sentence, and *"naming the carried thing"* is what that remedy prescribes. ⚠️ **The `hpowST` and
`hpowTS` the four `μ` rows add are not on the gate axis at all**: `weilPairingMu hS.left hpowST` is
a term of their own conclusion, so an object in the conclusion takes them — the same test the
paragraph on *"the data the statement is about"* below applies to `htors`, `hPT`, `hS` and `hm₂`
*"which no object in any of these conclusions takes"*, returning the opposite answer. **No row of
either bucket is convicted**, and the eight are named here so the next census does not re-read them.

⚠️ **A universal that survives its first measurement is a third shape beside `### Reach clauses`'
*"short is partial, over-reaching is false"* above**, and *"nothing is owed on them"* — which stood
in this paragraph until `#1765` — was it. Nothing convicts it, so it was not over-reaching and
`### Retired claims` does not bind; it is not a count, so it was not merely short either. It was
**unmeasured**, and what that takes is neither a marked quotation nor a qualification in place but
the measurement, published where the claim stood.

⚠️ **The prospective half of that is a rule about form, and this development already writes it.** A
clause saying that something *has not been measured* is a claim whose truth moves under other
people's commits, and it comes in three forms that decay at three different rates. ⚠️ **The
discriminator is where the sentence says the measuring did not happen, not what the measurement
would be of.**

* **Dated** — *"was **not** re-measured when the entry was retired"* — is a claim about a past act,
  so nothing merged afterwards can falsify it. ⚠️ **A sweep must not "refresh" one**: re-dating it
  to today's head trades a permanent truth for a perishable one.
* **Scoped** — *"not measured here"*, *"and this file does not measure it"* — is a claim about one
  file, so the only thing that falsifies it is *that file* gaining the measurement and the check is
  a one-file read. ⚠️ **Cheap, not immune**, and the tree carries the worked case:
  `EllipticCurves.FunctionField.WeilPairingTranslationSlotHprinN` retires its own *"not measured
  here"* with *"It has now been measured (`#1549`)"* — measured by that file, which is the only way
  a scoped clause can fall.
* **Neither** — *"not measured, here or anywhere"* — is a claim about the whole tree at the moment
  of reading, and a merge in a file its author never opened falsifies it silently. Only this form
  can be put through `### Reach clauses`' *"false or merely partial"* test by a merge elsewhere: the
  scoped form reaches that test too — `WeilPairingTranslationSlotHprinN`'s retirement above is it
  returning **false** — but only from inside the file that measures.

**Prefer a date to a scope, and a scope to neither**, on the ground *"prefer a direction to a
distance, and a heading's name to both"* above gives for the pointer axis: *"A distance is falsified
by any insertion between the pointer and its target, so it rots with nobody touching either"*. An
undated, unscoped *not measured* rots the same way and over the whole tree rather than over one
file. ⚠️ **It governs what is written next and convicts nothing standing** — the eleven undated
rows the census below counts are a population and not a worklist, and re-dating them would be a
sweep, which `### Scope of the rules above` refuses.

⚠️ **Codification and not a preference: the tree applies this rule already and cites the issue
because this page did not carry it.** `EllipticCurves.FunctionField.WeilPairing`'s
`## Explicitly out of scope` keeps the dated half of a sentence whose antecedent it retires, on the
ground that it *"is a claim about the moment the reason was withdrawn, not about the tree, so it
cannot go stale"*. ⚠️ **It is ruled here and not in `### Reach clauses` on `#1694`'s subject
test**: the subject is what a docstring's own *form* costs the next editor, which is this section's
subject in the pointer rulings above, and not that section's hypothesis lists.

⚠️ **The census, with the recogniser beside it** (`#1867`), as `### Module-block bullets`' *"publish
the recogniser beside any count, or write no count"* asks — over whitespace-normalised whole blobs
of every tracked `.lean` and `.md` file, case-insensitive:

```
\b(?:not|never)\b[^.]{0,40}?(?:re-)?measured   |   \bun-?measured\b
```

At `4655854` it returns **57** clauses in **42** files: **17** dated, **5** scoped, **11** undated
and unscoped, **12** already-retired quotations, **2** rows of prose about the form itself, **5**
seed false positives and **5** rows of this page's own prose about the disposition. Every clause
this axis has convicted sits in the third bucket, and of the twelve retirements **none quotes a
dated clause**, exactly one quotes a scoped one, and the other eleven quote undated unscoped ones.
⚠️ **The figure is dated to the base and no head figure is written**, because this paragraph is in
the population it counts: it quotes all three forms and lands in the last bucket, so a re-runner at
any head carrying these lines reads more than 57, and the difference is these lines.

⚠️ **The count is invariant under a correct repair and the split is not.** A retirement *quotes* the
clause it retires and a qualification *leaves it standing*, so both dispositions keep the words: the
seed returns **54 in 42** at `2aebb05` and **57 in 42** here, across a `#1848` cut whose repairs
keep the words either way; it is **byte-identical** at `855f993`, `1d79187` and `4655854`, so a
merge that touches neither the clauses nor the seed moves nothing on this axis. **Publish the
split; a count on this axis measures nothing.**

⚠️ **The boundary between the second and third buckets is written down rather than left to the next
reader.** `EllipticCurves.Torsion.ThreePrimaryBasis`'s *"what this file still takes at `ℓ = 3` only
was not re-measured"* scopes its **subject** to the file and leaves the measuring unqualified, so it
is undated and unscoped here; `EllipticCurves.FunctionField.NthRootOfPullbackN`'s retired *"which of
this file's inputs is now the binding one was not re-measured"* is the same shape and was retired as
one. A clause is scoped when it says the *measuring* did not happen here, and not when the thing
left unmeasured happens to be local. ⚠️ **A clause that says both is scoped**:
`EllipticCurves.Torsion.EllipticNetRegularity`'s *"is **unmeasured**, and this file does not measure
it"* pairs an unlocated conjunct with a located one, and the second glosses the first rather than
adding a claim beside it — adding a conjunct cannot make a sentence harder to falsify, so the pair
is read as scoped and goes in the second bucket. Its neighbour
`EllipticCurves.Torsion.EllipticNetSlices` states the same proposition **without** the gloss and is
in the third for exactly that reason. ⚠️ **On that shape the recogniser's hit does not decide the
bucket**: the seed matches the unlocated conjunct, so a re-runner reads *unmeasured* and never
reaches *"does not measure it"* — the two buckets are separated by reading the sentence, never by
the span the seed returns.

⚠️ **Normalise whitespace, and check it per string rather than per axis.** All eight surviving
copies of *"**Whether it unblocks those two fibre descriptions is still NOT measured**, here or
anywhere in this tree"* wrap between *NOT* and *measured*, so a single-line `grep` for them returns
**0**; the sixteen copies of the dated clause wrap nowhere at `4655854` and a single-line `grep`
finds all sixteen there. One axis, two replications, opposite answers.

⚠️ **And *"the only hypothesis left"* standing over a theorem is the `card_torsion_pow_of_odd`
shape, so the four that were theorems were repaired** (`#1754`):
`EllipticCurves.FunctionField.WeilPairingAlternatingAssemblyN`'s `_of_algClosed` and
`_of_algClosed_of_ne_zero` pairs took `### Retired claims`' move **whole** — the noun goes from
*hypothesis* to *gate* **and** the `(2 : F) ≠ 0` insertion goes in beside it. ⚠️ **The re-scope
alone would not have discharged them**, and that file's own module block says why: `#1637` had
already convicted the identical words about the identical declaration one layer up, recording that
they *"formerly read 'with `hprin` the only hypothesis left', which was short of `(2 : F) ≠ 0` and
of the torsion this register names"*. A headline left saying less than the bullet that was repaired
for saying too little is the same defect one layer down, where doc-gen surfaces it in preference.

The per-block clause below does not fire *between* the two registers. A gate-discharge claim and a
hypothesis list are different kinds of claim, not two dialects of one, so a block may hold both
provided each row is compliant on its own terms; what it must not hold is two rows making the
**same** kind of claim in different registers.

⚠️ **And *"the setting"* does not reach a clause that makes no gate-discharge claim.** The question
was filed as `#1626` against thirteen `WeilPairing*` module bullets whose reach clauses — *"at every
`3`-smooth `n ≠ 0`"*, *"at every `n` with `((n : ℤ) : F) ≠ 0`"*, *"over an arbitrary field"* — stand
over signatures binding points, their torsion, a halving point and `hprin` besides. The answer is
**no**, on two independent grounds, and it adds no exemption and withdraws none.

* **This exemption is keyed on the kind of claim, not on which hypotheses a clause omits** — the
  paragraph opening this section says exactly that. *"The setting"* supplies the **subject** of a
  gate-discharge word; a clause carrying no such word has no subject to supply, and there is nothing
  for the term to do. That is the asymmetry `### Module-block bullets` below turns on: a
  gate-discharge word *"is visibly relative to something"*, and a bare reach clause carries no
  signal at all. It is *"not a licence to say the signature is short"* read at its own layer, since
  the licence those thirteen rows need is the one that sentence refuses.
* **And on this front there is no such register to read them against.** A nesting-aware comment
  scanner — one that tracks `/-` nesting and tells `/-!` from `/--`, since these files carry later
  `/-! … -/` section blocks, so a line below the module block need not be in a declaration
  docstring — puts every occurrence of *"the setting"* in these seven files inside a declaration
  docstring, with one module block excepted: `WeilPairingAlternatingBaseChangeN`'s, where the phrase
  occurs only in sentences **declining** the register, not declaring one. ⚠️ **No count is written
  here on purpose**: one docstring moves any number, and what carries the argument is that no module
  block on this front **declares** such a register. Under `### Scope of the rules above` a module
  list and the file's headlines are two blocks, and by `### Module-block bullets`' *"the traffic
  runs one way"* a headline repairs no bullet. So a **yes** would have cleared none of the thirteen
  either; the two answers differ only in what they license next.

**Twelve of the thirteen are therefore defects**, and the repair is the `DeterminantModGeneral`
opener `### Module-block bullets` names — one **reach register** at the head of each of the six
lists — not thirteen rewritten bullets. The thirteenth,
`EllipticCurves.FunctionField.WeilPairingTranslationSlotNotInjective`'s *"for **every** `S`, every
rung-5 root and every certificate"*, clears outright and **not on this ruling**:
`not_injective_weilPairingTorsionMuHom_two` binds `h2`, `hgS` and `hu` and nothing else, the clause
names `(2 : F) ≠ 0` itself, and `hgS` and `hu` are conditions on the root and the certificate it
also names, so the residue is empty. ⚠️ **Not** because all three are arguments of
`weilPairingTorsionMuHom_two h2 hgS hu`: `h2` is an argument of it and is reach all the same
(`### Reach clauses`, `#1631`). `…_three` is the same with `h3`. ⚠️ `#1626`'s own table reports that
row as short of `hu` and an anonymous binder; the signature binds no anonymous explicit
propositional binder, and two further rows of that table are joined to
`transcendental_xCoord_nsmul_genericPoint_of_intCast_ne_zero`, which those two bullets **cite** and
are not about. **Re-derive a row before repairing it** — the join is where these tables go wrong,
and a triage set inherited is a triage set unread.

⚠️ **This is the answer PR #643 (`#1619`) already gave one layer up, and the two repairs differ for
a reason stated above.** #643 named `h` and `htors` in two bullets of
`WeilPairingAlternatingBaseChangeN` rather than leaving them to the setting. Those rows say the
conditions they list *"are the whole hypothesis list"* — a **count** — and *"a register says what a
list omits. It cannot make a count true."* So a head-of-list register was unavailable there and
naming in-row was forced. The twelve make **reach** claims, which a register does reach. Two blocks
in different registers on one question is what `### Scope of the rules above` forbids; two kinds of
claim repaired the two ways this document already prescribes is not.

⚠️ **What this does not decide.** *"The data the statement is about"* is a phrase in this section's
description of a **gate list**. It is not a second route to clearing a data hypothesis from a reach
clause: that job belongs to the data-argument clearance in `### Reach clauses` above, which has its
own discriminator — what the condition is about — and which `### Module-block bullets` applies to a
bullet exactly as to a headline. Read as such a route it
would clear `htors`, `hPT`, `hS` and `hm₂`, which no object in any of these conclusions takes, and
it would swallow `(2 : F) ≠ 0`, which `### Reach clauses` names as reach in terms. ⚠️ Nor does it
settle whether a binder reaching the conclusion only through a **projection**
(`pointClosedPoint h.left` over `h : W.Nonsingular xT yT`) is a data argument: it was one on this
document's plain words and not one under the direct-argument mechanisation, and the two split
`exists_weilPairingElt_galois_of_smooth_of_hprin` from its `Mu` twin in the same file — the first
binds the `Equation` and the second the `Nonsingular`. ⚠️ **Neither reading changes the verdict on
any of the twelve** — each keeps `hprin`, a torsion hypothesis or
`(2 : F) ≠ 0` in its residue on both. It was filed as `#1631` and is answered in
`### Reach clauses` above rather than here — a condition on the point the caller passes in is a data
argument however the conclusion reaches it — so what those registers must name is settled, and it is
not settled by this section.

⚠️ **A `#NNNN` citation names a gate list by reference, and it reaches exactly what the record it
names reaches.** That is `### Reach clauses`' anaphor branch — *"a clause that points at another
list is a third branch, and it is exactly as complete as the list it points at"* — applied to a
tracker record rather than to a signature, so it inherits that branch's two directions and adds
nothing to them. A citing sentence may **narrow** a record, because a gate standing over a range
stands at each point of it; it may not **widen** one. The reader's only move on meeting `#NNNN` is
to open it, and a record that denies the sentence which sent them there leaves them unable to tell
which of the two is wrong — the failure
`EllipticCurves.FunctionField.PullbackPrincipalityN`'s `## Scope` wrote its warning heading
against, in the words *"the confusion is one letter deep"*.
⚠️ **Silence is the compliant other branch**, exactly as *"names every hypothesis, or it names
none"* is. *"`hprin` over a **general** field (`#962`)"* states no index and is clean; *"there
`#962` is the standing gate at a general index"* states one the record excludes and is not. A gloss
is held to what it asserts, and asserting no range asserts nothing false — so a sweep on this axis
convicts far fewer citations than an occurrence test suggests, and the difference is not a
judgement call.
⚠️ **The two directions sort as `### Reach clauses` sorts them: short is partial, over-reaching is
false.** A citation short of its record completes in place. A citation wider than its record
over-reaches, so `### Retired claims` binds — and it binds **once, at the subject**, because every
copy asserts one proposition about one record and one reading of that record falsifies all of them
together. That is `### Retired claims`' *equation_div_of_ψ_ne_zero* test and not its
*"universal over the block's own list"* contrast: the block a copy sits in is not what the claim is
about, and the place the tree says what the record is, is.
⚠️ **Where the wider claim is the true one, say it and leave the citation at the record's range.**
*"`hprin` is the standing gate at every index"* is true over the base field, and the proposition is
already the tree's own: `EllipticCurves.FunctionField.NthRootOfPullbackN` states it in that file's
own words, *"it stays open at every index"* — one occurrence tree-wide at `855f993`. ⚠️ **The
wording quoted first is the sweep's, not that file's**, and it is nowhere in the tree at `855f993`;
what is already the tree's is the claim. What no docstring can do is attach a record to a range the
record refuses. Widening a record is a change to the tracker and is made there.

⚠️ **The worked case, measured** (`#1888`). The recogniser, over whitespace-normalised whole blobs
of every tracked `.lean` and `.md` file — the citation, and an index word within ±160 characters of
it:

```
`#962`
general index | general `n` | every `n` | arbitrary `n` | composite `n`
| `n = 2` and `n = 3` | numeral
```

At `855f993` it returns **63** citations in **45** files, of which **38** carry an index word; all
63 were read, and **13 in 13 files** attributed to `#962` a reach outside `n = 2` and `n = 3`.
Its title, its statement section and its `## Explicitly NOT this issue` section — *"**General `n`.**
`#404`'s `ωₙ` crux, and `#938`'s double obstruction at composite `n`. This issue is `n = 2` and
`n = 3` only"* — all three refuse that reach, so the thirteen are false and not short. They are
repaired under `#1888`, and at head the same recogniser returns **95** citations in the same **45**
files, **67** with an index word, and **none** of the thirteen left. ⚠️ **Both counts grow under
their own repair and the file count does not**, because each repair names the two numerals beside
the citation and each repaired block carries a pointer to the retirement, which cites `#962` again —
the phantom `### Module-block bullets` prices for phrase-keyed counts, arriving in the census's own
subject and including this paragraph. **Every surviving occurrence of *"`#962` is the standing
gate"* is inside a marked quotation**, which is what `### Retired claims` asks for and not a
residue; ⚠️ **no count is written for that phrase on purpose**, because the sentence writing it
would be in the population it counts.
⚠️ **The seed misses one of the thirteen, and the miss is published because it is the instructive
one**: `EllipticCurves.FunctionField.WeilPairingDeterminant`'s *"the pairing on `E[2 ^ k]` at
`k > 1` **over the base field**, and there `#962` is the standing gate"* carries its range in a
**variable** and in no index word. A range can be spelled in a bound variable, so an index-word
seed is a candidate set on this axis and never a conviction set.
⚠️ **Three of the fifty clean citations are negative controls and each names the wider range while
keeping the citation off it**: `WeilPairingAlternatingMu`'s *"`hprin` over a **general** field
(`#962`) and general `n`"*, `PlaceOrder`'s *"discharging `hprin` there is open (`#962`), and so is
every `n` outside `{2, 3}`"*, and `WeilPairingAlternatingAssemblyN`'s *"at general `n` nothing does,
and `#962` records the general field case"*. **The compliant form was already in the tree three
times over**, which is what makes this a ruling on the page rather than a preference: the sweep
writes what three files had written for themselves.
⚠️ **`#962`'s stated reason for its scope is falsified and its scope has not moved, and the
distinction is the whole of this rule.** The record gives the two numerals *"because those are the
only `n` at which the `F̄` statement exists"*, and `exists_gS_n_of_isAlgClosed`
(`EllipticCurves.FunctionField.PullbackPrincipalityN`) is that statement at every `n` with
`(2 : F) ≠ 0` and `((n : ℤ) : F) ≠ 0`. That is an argument for amending the record; it is not a
licence for a docstring to read the record as already amended, and a reader who opens `#962` today
meets the unamended text. ⚠️ **Whether the wider gate should have a record of its own is a question
about the tracker and not about any docstring** — nothing here files one, and nothing here is
evidence that one is owed.

⚠️ **An indexical address is a kind of claim this section has not sorted, and the tree writes one:
*this commit*** (`#1877`). This section sorts a clause by *"what kind of claim the clause is
making"*, and an address is a claim about a **commit**. In a commit message it is self-resolving,
because the message is part of the commit it names. In a **file** it is not, and two resolutions
are available that do not agree: `git blame` on the line carrying the words, and `git log -S` on
the words the clause is about. ⚠️ **Blame is the unsound one**, and it is the one this page names
in passing.
⚠️ **The failure this rule is written on sits inside one paragraph of one file, and the commit that
broke it never touched the sentence it broke.**
`EllipticCurves.FunctionField.WeilPairingAlternatingBaseChangeN`'s retirement block carries four
copies of the words, all written by `ecfb3e9` (2026-09-07, `#1843`, PR #723). `aadc404`
(2026-09-07, `#1861`, PR #727) later completed a reach clause inside that block and reflowed two of
its lines, so *"What this commit adds is the general-index `F̄` form"* now sits on a line `aadc404`
owns. That commit adds `(2 : F) ≠ 0` to a clause about `n = 2` and adds nothing of the
general-index form, while the three sibling copies in the same block still blame to `ecfb3e9`.
**Identical words, one paragraph, two referents, one of them wrong.**
⚠️ **`git log -S` on the quoted words is the resolver, and the tree says so rather than this page
inventing it.** `EllipticCurves.FunctionField.WeilPairing`'s retirement brackets its quotation at
`bec91b5` (2026-08-10, `#419`, PR #156) and says in terms that per-line blame returns a different
commit for it, `3f8ba10`, *"which is only what a per-line `git blame` returns"* — on the ground
that `git log -S` on the quoted words *"adds them once, at `bec91b5`, and removes them never"*.
⚠️ **That is the compliant form of the class**: the end of the bracket that can be written as a sha
is written as one, and only the end that cannot be — the commit being authored — is left
indexical.
⚠️ **The second gap is not blame at all: *this commit's parent* names two different commits.** A
one-commit PR lands as a squash whose parent is `main` at merge time, while the tree its figures
were measured against is the branch it was built on; the two differ whenever anything lands in
between. `3c183d8`'s parent is `8e55db0` (2026-09-07), and the other end `### Reach clauses` names
for that same commit is `444da7f` — **six commits earlier**. ⚠️ **A delta is safe and a state-at is
not.** A clause of the shape *"What is recorded instead is what this commit adds to that
population"*, measured against the commit's own parent, is true by construction of the squash
whichever tree that parent is, and `### Scope of the rules above` already draws the distinction for
shas in the bullet that writes it: *"No sha this commit adds is a state-at instance"*. ⚠️ **That
bullet — the `#1810` distance one — writes *this commit's parent* five times at `e122163`: one
delta, one mention, and three figures that name a tree and need the right one**, among them
*"at this commit's parent the distance seed's nineteen matches fall on eighteen lines"*. **That
figure survives**, the distance seed returning 19 on 18 lines at `444da7f` and at `8e55db0` alike,
**by luck and not by form.**
⚠️ **A base-named self-measurement has two ends, and they resolve under different rules** (`#2084`).
The head end resolves at the commit carrying it, because a message is part of the commit it names,
which this rule's opening paragraph already says; the base end resolves at the ref its own sentence
names, and ⚠️ **only a sha names a ref**. Each half convicts a different landed row, which is what
makes the split worth stating rather than assuming. ⚠️ **A delta takes neither limb: its base end
is the commit's own parent and never the ref the sentence names**, because parent-relativity is the
only thing the squash preserves — so the two ends are the reading for a state-at figure, and a
delta is scored against the parent whatever ref its own heading names.
⚠️ **The head end is where a delta stops being safe, and one clause of `ebb4d42` carries both
verdicts at once.** It publishes *"SELF-MEASUREMENT, base `77fb54d` -> head"* and, inside that
block, *"bolded-numeral +0 (279 at both ends)"*. `77fb54d` is six commits older than that commit's
parent `046022d`, and the seed under its five published flags returns `279` at `77fb54d`, `289` at
`046022d` and `289` at `ebb4d42`. ⚠️ **So the `+0` is exact against the parent while the
`279 at both ends` is false of the head end it names** — the delta limb scores `289` against `289`
at a parent that sentence never names, since a figure *"measured against the commit's own parent"*
is what a squash preserves whichever tree that parent turns out to be, while the endpoint pair is a
state-at claim keyed six commits too far into the history. **Naming an older base does not extend a
delta's protection to the endpoints; it converts them into state-at figures**, which is this rule's
*"A delta is safe and a state-at is not"* meeting the case it was not written for.
⚠️ **And a commit's own base is not a name.** `42c9b11` calls `49b327d` its base where its parent
is `eb4b11a`; its `268 / 224` is exact at the ref it names and false of its parent, so what fails
there is the description of the ref and not the figure — the opposite disposition from the row
convicted first, and on the same seed. A branch's base while it is being written and the landed
commit's parent are different objects whenever anything lands in between, and the squash is what
re-parents it.
⚠️ **The head end cannot be addressed at all, so it is re-run rather than named.** An author cannot
write the sha of the commit being authored, so the remedy is the one this page already gives for a
self-figure — measure it on the finished text and iterate to a fixed point — and, where the figure
is about the tree rather than about the message, key it to `git rev-parse HEAD^{tree}`. ⚠️ **That
key is stable under an amend and not under the landing**: the squash re-trees a branch exactly as
it re-parents it, so it addresses the draft and settles nothing about what lands once `main` has
moved over the same file. Where a tree figure has to survive the landing there is no name for it at
all, and the durable form is the delta against the parent.
⚠️ **The reading that says such a figure asserts nothing once it is pushed is refused here, and the
ground is that a gate which cannot come out false is not a gate.** Every gate block in this
development's messages is offered as a discharge, and a discharge no subsequent call can
check discharges nothing.
⚠️ **The ruling is prospective and it sweeps nothing** (`#1938`): a landed message cannot be
amended, so `eb4b11a`'s `254` — false at both ends under either half of the rule, the seed
returning `279` at `949369c` and at `eb4b11a` alike — stays on record as `#2084`'s row rather than
being repaired anywhere.
⚠️ **The population, dated, with its seed stated.** Over `git log --format=%B` for every commit
reachable from `ab5ec3a`, bodies whitespace-flattened and matched case-insensitively against the
alternation of `` self[-\s]measurement ``, `` base\s*(?:->|→)\s*head ``, `at both ends`,
`unmoved at`, `` re-run rather than assumed `` and `` checked rather than assumed ``: `31` of
`729`. ⚠️ **`14` of the `31` carry no backticked seven-hex sha within `200` characters of any
match, and `13` of those `14` carry one somewhere else in the message**, so what the bolded figure
measures is the window and not the class. ⚠️ **Carrying a sha is not naming a base** — which this
paragraph already says of shas *inside* the window, and which holds outside it too. All `14` were
read one at a time, and they partition in `4` ways rather than `2`: `8` name the base of their
matched clause by no sha, `2` have no base end for a sha to name, `3` name it, and `1` is named
under one limb of this rule and not the other. ⚠️ **The `8` are `855f993`, `77fb54d`, `4655854`,
`31177f4`, `8e55db0` and `7c0460d`** — each writing `base -> head` or `at both ends` over its own
parent while carrying only attributions to other commits — **`8f95181`, which carries no sha
anywhere, and `b2d1981`**, whose *"All three self-measurement seeds unmoved"* is a state-at pair
naming no ref, its parent `4769f3e` standing in a different commit's bullet of a concatenated
body. ⚠️ **The `2` are the seed matching a clause that measures nothing**: `cb6ad1f`'s *"stripping
needs a space at both ends"* is about CommonMark and `2aebb05`'s *"false at both ends of the
discharge front"* is about a front, so this predicate has a third verdict — *not applicable* —
and no instrument stated here emits one. The `3` name their base in terms: `3f61ad7` writes *"every
figure ... is measured at `ebb4d42` -> this head"*, `aadc404` writes *"base `2aebb05` → head"*, and
`e122163`'s `4655854` stands inside the code span `` `upstream/main = 4655854` `` — cleared by
reading and convicted by the seed, because a recogniser keyed on a backtick-delimited sha cannot
see a sha sharing its span. ⚠️ **And `2` rows, not `1`, are sorted differently by the two limbs,
in opposite senses**: `42c9b11` names `49b327d`, so its state-at end IS named while its parent
`eb4b11a` is not, and `b2d1981`'s *"unmoved"* is safe under the delta limb and unnamed under the
state-at one, which is `ebb4d42`'s own disposition arriving on a second row.
⚠️ **That window is a flag and not the class, and the count is a population and not a backlog**:
it misses `42c9b11`'s own `49b327d`, which sits outside it; a sha
inside the window may be an attribution rather than a base; and which of the other `17` name a
base is a reading nobody has done. **The vocabulary is a cut** (`#1846`), and a rule does not
need a census to land.
⚠️ **The commit that lands this paragraph joins that population**, which is why the figure carries
its sha in the sentence that gives it.
⚠️ **The disposition is `#1862`'s, it has landed, and it is restated here rather than re-decided.**
An author cannot write their own sha and a rebase moves any sha they do write, so the indexical is
not a defect when it is written: it is a placeholder whose debt falls due the moment the commit
lands. Re-key it to the seven-character sha, resolved with `git log -S` and confirmed with
`git cat-file -t`. **Nothing retires on the re-key** — the claim about what the text read, and
about the commit at which it stopped reading it, is the same claim, and only its anchor changes, so
`### Reach clauses`' *"false or merely partial"* test has no old claim to sort and
`### Retired claims`, which that test gates, is not reached. ⚠️ **Anchor any exemption to the file
and not to the commit, and bound it by naming rather than by counting**: a clearance saying *this
commit* moves none of the others is a fresh instance of the thing it clears, and a numeral standing
over a list is falsified by whatever next extends the list. Both are that PR's findings against its
own drafts.
⚠️ **A quotation of the words is a mention and not an address.** An occurrence italicised inside a
retirement, or quoted in order to be ruled on, asserts nothing about any commit; the test is
whether taking the quotation marks off would change what the sentence claims. **Every occurrence
of the words in this rule is a mention**, and none of them is bare.
⚠️ **The seed, with its flags, because a recogniser that does not state them is reimplemented as
the other branch** (`#1864`, `#1895`). Over whole blobs of every tracked `.lean` and `.md` file:

```
\bthis\s+commit\b        case-insensitive, whole blobs — the phrase wraps across source lines
```

At `e122163` it returns **36** occurrences on **32** lines in **6** files. ⚠️ **Both flags cost
two**: read case-sensitively it returns 34, read line by line it returns 34, and read both ways 32.
Fence-filtering costs nothing at that sha or at `cc74561`, so it is not a flag on this seed and is
recorded rather than assumed. At that sha **26 of the 36 are on this page**, **19** of those in
`### Scope of the rules above` where each commit records what it did, and the other **10** are in
five `.lean` files. At `cc74561`, **8** commits earlier, the same seed returns **22** on **19**
lines in **5** files. ⚠️ **The thirty-six at `e122163` are not read one at a time here, and this
rule clears none of them** — that reading is `#1877`'s sweep, and this is the ruling it asked for
first.
⚠️ **The question the sweep stopped on — whether a *delta* is owed a sha at all — is decided here,
and it is decided against an exemption** (`#1877`). That sweep's `.lean` half read its population
one site at a time and could place three shapes: a retirement bracket, a figure naming a tree, and
a clause of the form *"Both are repaired in this commit, one word each"* — bold in the original
over that clause, and a specimen standing in `### Scope of the rules above` on this page rather than
in any of the five `.lean` files — which describes the very edit its reader is looking at. The
reading that exempts the third says such a clause self-resolves the way a commit message does.
⚠️ **It does not, and the counter-example is the failure this rule is written on**: the
general-index clause quoted here is of exactly that shape, and it is the one that went wrong. A
message is part of the commit it names, which this rule's opening paragraph already says; what
follows from it — stated here rather than quoted, because the page does not carry it — is that a
**file** outlives its commit and is read at heads that commit cannot name. **Nothing is exempt by
what a clause asserts**, and this rule's
*"A delta is safe and a state-at is not"* — bold in the original over that whole sentence — is true
of the **parent** gap alone: a delta is immune to which tree a parent is, and a reflow breaks it
exactly like every other shape.
⚠️ **The record that looks like an exemption is luck, and the mechanism behind it is live on this
page.** Walking every commit that has touched this file and comparing per-line blame against the
whitespace-normalised resolver at each of them, keyed on a 90-character window either side of each
occurrence: **74** commits, **388** occurrence-readings, and blame names the writing commit **388**
times — not one disagreement, where the `.lean` half went wrong on the same day it was written.
⚠️ **But this page is not append-only and its rows are not one commit each**: **49** of those 74
commits delete a line, and **4** of the **14** top-level rows of `### Scope of the rules above` —
the lines opening `* ` at column zero between that heading and the next — carry text from more than
one commit, two of them rows that carry occurrences of this seed. So a commit that did not write a
row does edit it here, and the only reason nothing has gone wrong is that those edits have missed
the lines carrying the words. **A clean record over a live mechanism is what this section already
calls luck and not form.**
⚠️ **What the record does buy is an order of work, and an order is not a clearance.** A wrong
resolution costs most where the sentence cannot be used without it: a bracket loses the end that
dates it and a figure loses the tree it was measured on, while a delta's content — that two
pointers are repaired, one word each — is checkable against the head in front of the reader
whatever the address resolves to. So a sweep takes the tree-naming and bracketing sites first and
the deltas after them, and no site is cleared by being second.
⚠️ **The debt regenerates by one row per commit, and saying so is part of the ruling.** An author
cannot write their own sha, so every row recording what its commit did falls due the moment it
lands, and a sweep that pays twelve of them writes a thirteenth. A sweep of this class is therefore
periodic and never final. ⚠️ **The one form that retires the debt instead of deferring it is a
record whose subject is the file rather than the commit** — *both pointers now read the other way*,
which any reader settles by opening the file, against *this commit repairs both*, which no reader
settles at all. That is the cheaper form for whoever writes the next row; it is not imposed on the
rows already here, which are owed a sha and not a rewrite.
⚠️ **`git log -S` is the resolver this page names, it takes a LITERAL string, and a source line is
the only unit of this tree that is one.** Three readings of it, taken over this page's 34
occurrences at `49b327d`. Given the words **as they read**, flattened across the wrap, which is how
a re-runner types them, **0 of 34** resolve: the pickaxe returns the empty set, because a window
wide enough to be distinctive is wider than this file's 100-column wrap and so occurs in no blob at
all. Given the **source line** carrying them, quoted whole, **34 of 34** return the writing commit.
And given a flattened phrase that happens to fit one line at the head but was **wrapped when it was
written**, it returns the wrong commit, which is the one this rule exists to avoid:
`git log -S 'What this commit adds is the general-index'` at `7c0460d`, on
`EllipticCurves.FunctionField.WeilPairingAlternatingBaseChangeN`, returns **`aadc404`** — the
reflowing commit — because `ecfb3e9` wrote those words across two source lines and the literal
count really did go 0 → 1 at the reflow.
⚠️ **So quote the source line, or normalise both sides before comparing, and never the words as
they read.** The sound form is a walk over the file's own history oldest-first, taking the first
commit whose whitespace-normalised blob carries the words while its parent's does not; it returns
the writing commit for all 34 here and agrees with every one of `#1877`'s nine `.lean` re-keys.
⚠️ **The key is a flag of that resolver and it decides the answer** (`#1910`): *the words* means the
clause's own span, or the source line carrying it, and never a fixed-width neighbourhood of it.
Keyed instead on the 90-character window this rule's own walk uses, the same resolver agrees with
only seven of those nine, and one of the two it loses is the
`EllipticCurves.FunctionField.WeilPairingAlternatingBaseChangeN` clause this rule is written on,
where it returns `aadc404` — the wrong answer the rule exists to prevent. A 180-character window is
not the words but the neighbourhood, and a neighbourhood was written first by whichever commit last
edited any part of it.
⚠️ **The naming-not-counting clause in this rule reaches any clause standing over a population,
not only an exemption.** It was written against an exemption because that is the instance PR #726
had, but its mechanism — a numeral standing over a list is falsified by whatever next extends the
list — is indifferent to what the clause does with the numeral. Two of the re-key notes `#1877`'s
sweep landed bound themselves by a numeral, each inside a bold clause:
`EllipticCurves.FunctionField.PullbackPrincipalityN`'s opens on *Both addresses in this module* and
`EllipticCurves.FunctionField.WeilPairingAlternatingBaseChangeN`'s on *Those four addresses*, where
each stands over the addresses of a module that a single edit can extend. **Neither is false at
this head and neither clears anything**, so both are short rather than wrong, nothing retires, and
`### Retired claims` is not reached. They are named so that whoever next edits either module bounds
them by naming, and so that the next such note is written that way outright.
⚠️ **The population, with the seed's flags restated because a count that does not carry them is
reimplemented as the other branch** (`#1910`). Over whole blobs of every tracked `.lean` and `.md`
file, case-insensitively, at `49b327d` the seed returns **41** occurrences on **36** lines in
**6** files. ⚠️ **The line unit is a flag too, and it is the one this rule was short of**: a line is
a source line carrying at least one *complete* match, which is the unit of the pairs this rule
already publishes — 19 at `cc74561` and 32 at `e122163` — where counting every line a match touches
gives 21, 34 and 40 instead. ⚠️ **Both the other flags still cost**: read case-sensitively the seed
returns 39 occurrences, read line by line 38, and read both ways 36. Those three are occurrence
counts, and at this sha two of them collide with a line count taken under another unit, which is
the reason the unit has to be said at all. **Seven are in five `.lean` files and every one of those
is italicised** — `#1877`'s sweep left no bare occurrence in any of them — and the other **34** are
on this page,
split by its `^### ` fences as five in `### What is formalised`, one in `### Reach clauses`, eight
in this rule, one in `### Module-block bullets` and **nineteen** in `### Scope of the rules above`.
⚠️ **This completion adds four more to the eight, and every one of the four is a mention**, so the
seed grows by it and the reading of the 34 does not. ⚠️ **Read one site at a time, which is a
reading and not a recogniser**: **ten** are mentions and **twenty-four** are addresses, of which
twelve name a tree or date a bracket — the five retirements of `### What is formalised`, the two
figures outside that list, and the five inside it written against *this commit's parent* — and
twelve are deltas. **Nothing is cleared here and nothing is re-keyed here**: the re-keying is
`#1877`'s sweep, which now has the decision it was held on.

### Module-block bullets

A `## Main statements` / `## Main results` bullet makes the same kind of claim, about the same
declaration, as that declaration's headline does. The two registers above therefore reach it, and
`### Scope of the rules above` below scopes this section as it scopes them — but the reader is in a
different position, and one clause of that section, *"Declaration headlines are reach clauses too"*,
**inverts** here.

**A bullet is read inside its own list.** *"Declaration headlines are reach clauses too"* is
justified by rendering distance: doc-gen prints the rest of *this* docstring beside a headline and
the module block nowhere near it, so a completing sentence in the module block is one the reader of
a headline never sees. At the module-block layer that distance is zero — a bullet's context *is* the
block, contiguously above it. So a **register** — a sentence in the block that says what the bullets
under it leave out — can reach a bullet in a way that the same sentence could never reach a
headline, and such a bullet is compliant relative to it.

⚠️ **How far it reaches depends on which of the two registers above the bullet is answerable to,
and the two scopes are not the same.** This is the whole of the reading, and getting it wrong in
either direction decides a different population.

* A **reach register** names the hypotheses its bullets omit. It binds **the list it heads** and
  nothing further up the docstring. The tree writes these —
  `EllipticCurves.FunctionField.MulByNFibre` (*"**Every one of the thirteen below does take
  both**"*, scoped inside a bullet) and
  `EllipticCurves.TateModule.DeterminantModGeneral`, whose `## Main statements` **opens** *"**Every
  statement and definition below takes `(2 : F) ≠ 0` and `(n : F) ≠ 0`**, and the rank and the basis
  take `1 < n` as well; the bullets give the conclusions and not the hypotheses"*.
  ⚠️ **`DeterminantModGeneral`'s closing clause is not the form to copy, and it is the last live
  instance of it in the tree.** *"The bullets give the conclusions and not the hypotheses"* is a
  **universal over the bullets**, which `#1647` decided against — as a **form**, and separately
  from whether it is true of any particular list. That quotation is not edited here: what this
  section prescribes is the **naming** half of the sentence, and the closing form to copy is below.
  ⚠️ **`MulByNFibre` closed on the same clause until `#1686` and no longer does**, which is why
  only its naming half is quoted: its universal was false of the thirteen on the day it landed, two
  of the rows naming the binders their declarations bind. `DeterminantModGeneral`'s list was read
  row by row and its universal **holds**, which is why it is left standing.
* A **gate-discharge register** supplies the *subject* of *"unconditionally"*, *"with no hypothesis
  left"*, *"nothing further"* — the gate list the word is a delta against. It may sit **anywhere in
  the module block**. `### Gate-discharge claims` above already treats such a register as a
  per-file object and names the precedent, `EllipticCurves.Torsion.PrimaryTowerAlgClosed`, which
  runs one from its H1 through its module block and down into the declaration headlines.

⚠️ **The asymmetry is not new either — it is the one `### Gate-discharge claims` states, with the
unit moved.** That section earns its exception on the ground that *"a reader who meets a defined
term looks it up once and is then equipped for the whole register, where a reader who meets a
partial hypothesis list has no signal that a completing sentence exists anywhere"*. A
gate-discharge word carries that signal — it is visibly relative to something — so a subject
anywhere on the page it is printed on will do. A partial reach clause carries no signal at all, so
the register has to be where the reader meets it, and a paragraph two `##` sections up is the
*"prose sitting elsewhere in the module"* the boundary excludes. What this section contributes is
therefore the **reach** half; the gate-discharge half follows from the rule above once the unit is
the module docstring.

⚠️ **How far above its list a reach register may sit, in terms, because the two sentences above
name two different units and both call theirs *"the block"*** (`#1668`). *"It binds the list it
heads"* and *"a bullet's context **is** the block, contiguously above it"* are consistent read
each against its own unit and inconsistent read against the other's; what settles it is that the
two registers do not share a unit, and this document already fixes both:

* a **reach register**'s unit is **its list**. That is the `## Main *` section it opens, or a
  sub-list inside one: it begins at that heading and ends at the next heading of the same or a
  higher level, and the register binds the bullets **below** it inside that span and nothing else.
  `### Scope of the rules above` is where the unit is written down — *"a `## Main statements` list
  … is one place"* — so *"the block"* in *"a bullet's context is the block"* is that list.
* a **gate-discharge register**'s unit is the **module docstring**, which is what *"anywhere in the
  module block"* says, and `MulByNResidueDegree`'s worked example below is a subject sitting two
  `##` sections above the list it serves.

⚠️ **So prose in another `##` section does not clear a bullet, and the distance does not enter.**
*"A paragraph two `##` sections up"* above is the instance the boundary was stated on, not the
boundary: **one** section up is excluded on the same ground, and so is one paragraph up on the
other side of a heading. ⚠️ **Nor does a register reach a bullet *above* it** — that is the
*"nothing further up the docstring"* half read in the other direction, and it is what makes a
sub-list's register invisible to the outer list, as the *"Not reached"* row below records.

⚠️ **This narrows nothing and retires nothing.** Each wording was true of the unit it governs, so
`### Reach clauses`' *"false or merely partial"* test puts this paragraph under **completing** a
clause, and `### Retired claims` says completing retires nothing. What is new is that the two units
are named beside each other, which is the whole of what `#1668` asked for.

⚠️ **And it points the same way as *"Nor does a sentence lower in the declaration's own
docstring"*** in `### Scope of the rules above` (`#1660`), which is the reconciliation that decides
this rather than the wording. That ruling holds a completing sentence **four lines** from its
headline insufficient, on the ground that the reader meets the clause first and a partial one
carries no signal. A register in another `##` section is fifty lines from its bullet. The two
rulings differ in **unit** — a headline is its own unit, a bullet's unit is its list — and give the
same answer for the same reason; a rule that let a bullet reach further than a headline would have
to say why, and there is no ground for it.

⚠️ **A sentence that cites the derivability exemption is not thereby a register**, and calling it
one is a label rather than a reach claim — which is what the convicted population turns on.
`EllipticCurves.FunctionField.MulByNGalois`, `…MulByNGaloisGroup` and `…MulByNPlaceComposition`
each open a `## ⚠️ The transcendence parameter` section with the same sentence, and
`…MulByNComposition` carries it under `## Hypotheses, and the one that has to be composed first`;
all four say **in the next clause** that the exemption is what clears their rows, so no bullet of
theirs hangs on the label. `…MulByNInertia` said *"cleared by the register and not by the
exemption"* of three declarations, which is a clearance stated **on** the register, and is what
this ruling convicts.

**Measured at `8d31527`, with the recogniser written out, as this section requires.** Over every
`/-! … -/` block of every `git ls-files '*.lean'`, lines matching `\bregister\b`, or matching
`(every|all|each).*(below|above).*(takes?|binds?|carr(y|ies)|is stated|is an)`
**case-insensitively**, keyed to the `## ` section they sit in — **150** lines in **68** files,
read one by one.

⚠️ **The universal alternative is loose on three axes on purpose, and every one of the three was
found by losing rows to it.** It is **unanchored**, because this tree writes *"Everything below
carries …"* as a third wording of the same object and `\b(Every|All|Each)\b` drops every one of
them; it is **case-insensitive**, because the same universal is also written mid-sentence in lower
case — `…FunctionField.MulByNComposition`'s *"so every statement below takes the hypothesis as an
ordinary argument"*, `…TateModule.FreeGeneral`'s *"every `_of_natCast_ne_zero` statement below
carries `h2` as well as `hℓ`"* and `…PullbackPrincipalityTwoRationalTorsion`'s *"every statement
below takes `hcard` as **binder**"*, which are three of the fourteen rows below; and its **verb
list is wide**, because the bare stems and *"is an"* catch wordings that
`takes|binds|carries|is stated` does not. **A recogniser published beside a count is an
instrument, and anchoring, case and the verb list are three independent ways for it to be short of
its own rows.** ⚠️ **So run the count
you are about to publish, and assert that every row you name is in its output** — a one-line
membership check, which is what found the fourteenth row below; all fourteen are asserted present
in the 150.

**Fourteen** are a universal over hypotheses or over the setting, sitting outside the `## Main *`
section whose bullets it could be read as clearing. Of those, **one** states a clearance on
itself: `MulByNInertia`, **two** bullets covering **three** declarations, repaired in the row by
this PR. **Four** are the exemption-citation label above. The remaining **nine** clear no bullet:

* three because every bullet of their list names its own hypotheses or names none —
  `EllipticCurves.Torsion.StructureGeneral`, `EllipticCurves.TateModule.FreeGeneral`,
  `…FunctionField.PullbackPrincipalityTwoRationalTorsion`;
* four because the sentence sits **below** its list, which is the *"nothing further up the
  docstring"* half read in the other direction — `…FunctionField.TranslationMulByNCommGeneral`;
  `…PullbackPrincipalityThree` and `…WeilPairingTranslationSlotNotInjective`, each of which
  carries *"Everything below carries `[IsAlgClosed F]`"* in a `## Scope` section printed **after**
  the `## Main *` list it could otherwise be read against; and `…WeilPairingGaloisRootN`, whose
  *"everything general below carries `hprin`"* sits in
  `## ⚠️ What is NOT here, and why it cannot be`, printed after `## Main statements` — and that
  list opens with a register of its own, so no bullet of it was waiting on the later sentence;
* two because what they quantify over is an **instance** or the setting, which `### Reach clauses`
  leaves ambient — `…WeilPairingAlternatingTwoRational` (`[DecidableEq F]`) and
  `…TranslationActionN` (*"at an arbitrary `n` over an arbitrary field"*).

⚠️ **Exclusions with their grounds, because an exclusion needs one as much as a conviction does.**
The bulk of the 150 are non-vacuity paragraphs quantifying over what is **above** them (*"Every
statement above carries `[IsDedekindDomain W.CoordinateRing]`"*), which can clear no bullet below
by construction; and `…PlaceDegreeComparison`'s `## Scope` hit is a marked `### Retired claims`
quotation of a wording that is already gone, not a live claim. The widened alternative adds **22**
lines over the anchored one: **three** are rows already counted above, **one** is the fourteenth,
and the other **18** are excluded on four grounds — **four** sit **inside** their own `## Main *`
section and are safe by construction, **five** quantify over what is **above**, **seven** quantify
over **content, provenance or naming** rather than over hypotheses or the setting, and **two** are
not universals at all but substring matches (*"taken"* on `take`, *"Integrally"* on `all`).

⚠️ **The borderline row is excluded on its *subject*, and that is the whole of the ground.**
`EllipticCurves.TateModule.ImageProfinite`'s *"All fifteen names below carry a `Two`, and all
fifteen statements are byte-identical to what this file shipped before the extraction"* sits in
`## Naming`, printed **above** that file's `## Main statements` — the geometry of a candidate — and
is excluded because it quantifies over **names and byte-identity**, not over hypotheses or the
setting, so it leaves no hypothesis for a bullet to be short of. `…TateModule.FreeGeneral`'s
*"Every statement below is an application"* goes the same way for the same reason. ⚠️ **If that
ground is rejected they are two further rows that *clear*, not two convictions**: neither says a
hypothesis is taken or is absent, so no bullet below them is short of anything they assert.

⚠️ **Every register PR #654 wrote is inside its own `## Main *` section and is safe by
construction**, which is why the convicted count is one and not fourteen: this rule bites on prose
registers written before that PR fixed the placement, and on nothing written from this section.

⚠️ **That `DeterminantModGeneral` opener is the form to copy for the naming half**, and it is
the cheap repair for a list whose bullets are each short of the same hypotheses: name them
**once**, at the head of the list, and say that the bullets do not repeat them. The alternative —
inserting the same two conditions into a dozen bullets — is what `### Scope of the rules above`
calls making the block worse, and it is not what a reader of a list wants.

⚠️ **What it is not the form to copy for is the sentence it closes on**, and a register written
from this document rather than from a sibling file is how that sentence keeps being re-introduced.
*"The bullets give the conclusions and not the hypotheses"* is a universal over the bullets, and it
cannot survive this development's own repairs: a count is repaired **in the row** (*"a register
says what a list omits. It cannot make a count true"*, below), and every such repair costs the
universal another instance. ⚠️ **Nor did it survive its own lists** — the test below is weaker than
a count and most of the blocks that carried it failed it on the day it was written. `#1647` decided
it and PR #658 replaced it in
`EllipticCurves.FunctionField.WeilPairingAlternatingAssemblyN` with the form to copy here — a
**routing** sentence rather than a universal:

> ⚠️ **Where a bullet says nothing about hypotheses, read it against this register; where a
> bullet counts them, the count is that bullet's own claim and no register makes it true.** Naming
> some without counting is neither, and sits under this register unchanged; reporting one
> *discharged* is a gate-discharge claim, which `README.md` `### Gate-discharge claims` governs.

Every branch of it is decided elsewhere in this document and the sentence only routes: silence to
the register, a count past every register, a discharged hypothesis to `### Gate-discharge claims`.
⚠️ **The branch worth reading twice is *"naming some without counting"***, because it is what a
reach-register list is *for* and it is the one a phrase-keyed sweep keeps re-triaging as a defect:
a bullet that names two of its declaration's four hypotheses and claims nothing about the rest sits
under its register **unchanged**, and repairing it in the row is what makes a block worse.

⚠️ **A fifth branch, and the routing form has no home for it: a bullet that says a named
hypothesis is ABSENT** (`#1682`, `#1683`). *"Prime or not"*, *"no `[IsAlgClosed F]`"*, *"it needs
no `g ≠ 0`"*, *"no `(3 : F) ≠ 0` and no smoothness"* fall through all four: such a bullet says
something about hypotheses, so it is not the first branch; it is none of this document's count
phrases, so it is not the second; it is a **denial** and not a naming, so filing it under the third
is a mis-file; and where the absent thing is in no gate list of its own file, the fourth does not
reach it either. **An absence claim is the bullet's own claim, and the test is one question of the
signature — does the declaration bind the thing the bullet says is gone?** Where the absent thing
*is* a gate, `### Gate-discharge claims` governs and asks that same question over its own
population, which is where *"no `hcard`"* goes.

⚠️ **A register can falsify such a bullet, and can make one true only when it closes a LIST.** The
distinction is count versus list and it is not a quibble. A complete **count** — a register that
says only how many hypotheses each row takes — entails no particular absence, which is what
*"A register says what a list omits. It cannot make a count true."* already says. A complete
**list** — `PrimaryTowerOdd`'s *"That is the whole **explicit hypothesis list** of every
declaration below"*, which names `p.Prime` and `q.Prime` on the two rows that take them — entails
every absence it excludes, so it does make that block's *"prime or not"* true. ⚠️ **The general
answer is nevertheless the signature**: of the 33 rows this branch's census finds, **30 sit in
blocks carrying no register at
all**, and a reader who meets an absence claim has no signal telling them which kind of block they
are in. A register is a sufficient ground where a block has one, never a necessary one, and no
bullet may be written on the expectation that a reader will go looking for one.

⚠️ **The measurement demand transfers to this branch unchanged, and the section that makes it is
`### Reach clauses`.** `#1682`'s description attributes it to `### Gate-discharge claims`; the
paragraph it means is in `### Reach clauses`, which says in terms that the gate question is decided
by that other section and not by itself, so the attribution is worth correcting here rather than
inheriting. `### Reach clauses` is where the asymmetry is stated — *"a presence mention is
contradicted on its own page as soon as it goes stale, while an absence claim is contradicted by
nothing a reader can see"* — and where
`not_forall_det_eq_intCast_of_zsmul_add_zsmul` is named as the form to copy because it *"records
that the `omit` above it is measured rather than guessed"*. At the bullet layer the measurement is
the **elaborated telescope**, instance binders included. Reading the `theorem` line alone is
`#1577`'s `variable`-block blindspot and it decides rows in both directions here.

⚠️ **The setting is not part of what such a clause denies**: `[Field F]`, `[DecidableEq F]` and
`[Algebra S F]` are the scaffolding a statement is written in, not conditions
a clause claims are absent, so *"no hypothesis on `F`"* is read against the **mathematical**
conditions — characteristic, closure, ellipticity, torsion, smoothness. Seven rows turn on that
convention and none changes verdict under it; stating it is what stops the next sweep convicting
them.

**The census, with the recogniser beside it, as this section requires.** Over every `/-! … -/`
docstring of every `EllipticCurves/**/*.lean`, take each `## Main *` section, split it at
`\n(?=\* )` so a wrapped row stays whole, whitespace-normalise each row, and keep the rows
matching, case-insensitively, the alternation

```
\bno\s+`                                                        \bprime or not\b
\bno\s+(primality|hypothesis|condition|further|extra|hcard|halving)
\bwithout\s+`     \bneeds no\b     \btakes no\b     \bnot required\b     \bno longer\b
```

⚠️ **Bound the section by its docstring**: without that bound the same scan reads a row's text
straight through the closing `-/` and on to the next `##` anywhere in the file, which on two rows
is several hundred lines of Lean. It changes no row here, and that is luck rather than a property
of the seed. **1696** `## Main *` bullets tree-wide and **64** matching rows, at `8f95181` and at
`6c22e12` — the tree this paragraph shipped in — alike. ⚠️ **That second ref read *"this commit"*
until `#2291` named it.** The pair was exact at both refs when it was written and is exact at both
refs today, so naming the sha is a **re-keying and not a retirement**; what the indexical cost is
four paragraphs below, where this same seed is re-run at a later tree and returns another answer.
Over the tree `#1683` itself measured, which is `b764fae` and is `#1656`,
PR #667, the same instrument returns **63** — the one addition being `MulByNInertia`'s *"needs no
separability at all"*, which `#1665` wrote. **Every one of the 64 was read**, and they split four
ways. **15** are gate-relative, and `### Gate-discharge claims` decides them. **3** are a complete
count in absence clothing — `EllipticCurves.Torsion.OmegaChordSum`'s bullet for
`card_torsion_eq_sq_of_odd` reads
*"with no hypothesis beyond `2 ≠ 0` and `(n : F) ≠ 0`"* — which is the second branch, and belongs
to the counting axis (`#1645`, `#1767`) rather than here. **13** are not about a hypothesis
list at all and are false positives of the seed — claims about Mathlib's API, about what the tree
does not contain, about a refactor, or about a statement's vocabulary. And **33** are this branch.

⚠️ **Of the 33, thirty-two are TRUE and one was FALSE**, and the false one is the shape this branch
exists to catch. `EllipticCurves.FunctionField.MulByTwoFibreInfinity`'s row for
`comapProjPointTwo_pointClosedPoint_of_eval_Ψ₂Sq_eq_zero` read *"No hypothesis on `F`"* over a
signature binding `h2 : (2 : F) ≠ 0`, while that declaration's **own headline in the same file**
reads *"No hypothesis on `F` beyond `(2 : F) ≠ 0`"* — and `903ef4d` (`#774`, PR #314) wrote both,
so the block and the declaration disagreed from the commit that created them. ⚠️ **No register was
involved and none would have helped**: that block carries none, and is one of the 30.
The repair is the qualification the declaration already carried, and the retired wording is quoted
at the row.

⚠️ **Two limits of the seed, published because a recogniser owes them** (`#1749`). It is
**vocabulary-keyed**: an absence written *"free of `hprin`"*, *"drops `[IsAlgClosed F]`"* or
*"neither condition is needed"* does not match, so 64 is a floor and not a population. And it reads
`## Main *` bullets **only** — a headline absence claim is a different layer with a different
denominator, and the `.lean` docstrings are the whole of its reach, so nothing this document says
about itself is inside it.

⚠️ **This paragraph and `#1680` are different sentences of this section and neither answers the
other.** `#1680` is open against the `EllipticCurves.TateModule.DeterminantModGeneral` *"form to
copy"* naming above; nothing here edits that sentence or the paragraph holding it. If `#1680`
lands first, this branch is unaffected; if this lands first, `#1680`'s repair is unaffected.

⚠️ **The same seed, re-run at a later tree, and this is what the indexical above cost.** At
`6a733e1e` (PR #875, `#2282`) the census is **1954** `## Main *` bullets over **462** sections in
**397** of **453** module docstrings, with **107** matching rows — against **1696** / **425** /
**364** / **419** / **64** at `6c22e12`. ⚠️ **The matching population grew by 43 and not by 44.**
Keyed on the pair (path, whitespace-collapsed row text), **44** rows appear and **1** disappears,
and one of the 44 is the re-worded form of the 1: the `WeilPairingProductRelationRootIndependent`
row for `weilPairingElt_eq_of_smul_pow_eq_of_divisor_eq` went from *"for arbitrary `n`"* to
*"at every `m ≠ 0`"* and still matches. So `64 + 44 − 1 = 107`, and *44 new* would be a
set-difference artefact rather than a count of rows. ⚠️ **The two limits above carry over
unchanged**: 107 is a floor and not a population, and the growth is the tree's and not the seed's —
a larger figure out of a vocabulary-keyed recogniser is not a stronger claim. ⚠️⚠️ **The four-way
split, the *"thirty-two are TRUE and one was FALSE"* verdict and the `MulByTwoFibreInfinity` repair
are facts about the 64 at `6c22e12` and are left keyed there.** The 43 new rows are **counted here
and not read**, so nothing above is restated of them; reading them is `#2291`'s forward-filed half.

⚠️ **A re-implementation of a published recogniser owes its calibration and not only its
output**, and that is the cell `#2282` twice lacked: both of its review rounds found this census
suspect and neither could convict it, because the instrument in hand returned `1690 / 63` where this
page publishes `1696 / 64` **at the same commit** — so it could not separate drift from its own
error, and `#1664`'s ruling (a dated census drifts, and drift is not falsification) correctly
governed. The figures above come from an instrument that first reproduced **six** published cells at
**four** refs: `1696 / 64` at `8f95181`; the same pair at `6c22e12`; **63** at `b764fae`; the
`b764fae` → `8f95181` delta as **exactly one row added and none removed**, that row being
`MulByNInertia`'s *"needs no separability at all"*; and **1696** bullets in **425** sections over
**364** of **419** docstrings at `7495d3e`. ⚠️ **The `7495d3e` census in
`### Gate-discharge claims` is dated by sha at both ends, so it is correct-and-stale rather than
wrong and nothing here edits it.** ⚠️ Its **1690** counts how many of the 1696 bullets resolve
to a declaration of this development, which is **not** a bullet count — so the collision with the
number an uncalibrated bullet scan produced is a coincidence, and reading it as agreement is the
trap that a calibration step exists to stop.

⚠️ **The 43 are now READ, and the answer is a clean sheet — keyed at `0094b84`.** `#2294` triages
the arrivals the `6a733e1e` census above counts, four ways as the 64 were, against the
**elaborated telescope** of every declaration each names and never against a `theorem` line: **0**
are gate-relative, **7** are a complete count in absence clothing, **7** are false positives of the
seed, and **29** are this branch. ⚠️ **All 29 are TRUE and none is FALSE**, so the
`MulByTwoFibreInfinity` shape has no second instance among them. ⚠️ **A clean sheet is a weaker
result than a repair and is reported as one**: what this pays is that the largest unread block
this axis has carried is no longer unread, not that the tree was found sound. ⚠️ **The
gate-relative class is EMPTY by measurement and not by assumption** — no row of the 43 carries
*"unconditionally"*, *"no hypothesis left"*, *"owed nothing further"* or *"the only hypothesis"*,
so `### Gate-discharge claims` takes none of them, against **15** of the 64. The reading was run
with `#2291`'s own instrument and re-verified at **eight** cells before any row was read: the six
above, plus **1942** bullets and **106** matching at `7ba33ed`, and **1954 / 462 / 397** of
**453 / 107** at `0094b84` — ⚠️ **identical to the `6a733e1e` cell, so the three landings between
`6a733e1e` and `0094b84` moved no bullet of this population** (`git rev-list --count`, **0** merge
commits: `5f9b50e`, `6c31bb2`, `0094b84`). ⚠️ **That sentence read *"the four landings between
them"* until `#2294` round 2, and the pronoun is what made it wrong rather than the arithmetic.**
It names **three** shas and then says *"them"*, which leaves two pairings and ⚠️ **the one that
makes the numeral right makes the claim false**: `6a733e1e`↔`0094b84` is **3** landings with the
census equal at both ends, while `7ba33ed`↔`0094b84` is **4** with **106 ≠ 107**. **So state the
pair by sha wherever a between-count is published here** — a count of landings is keyed to an
ordered pair, and a sentence that names three endpoints has supplied none.

⚠️ **The census above is keyed to `0094b84` and the population has moved once since; the delta is
reported here rather than folded in, because a census is dated by the sha it was measured at.** At
`3f9e3239` the same instrument returns **1967** bullets over **464** sections in **399** of **455**
docstrings with **108** matching — **one** row appears and **none** disappears, and it is
`EllipticCurves.FunctionField.PullbackPrincipalityNRationalTorsion`'s row for
`card_torsionNMul_of_card`. ⚠️ **It is the `MulByTwoFibreInfinity` shape in form — a bare *"No
hypothesis on `n` and none on `F`"* — and it is TRUE**: that declaration's elaborated telescope is
`{F : Type*} [Field F] {W : Affine F} [DecidableEq F] {n : ℕ}` with
`hcard : Nat.card ↥(W.torsion n) = n ^ 2` as its one hypothesis, which the row names. **So the
clean sheet is 44 of 44, and the shape's having no second instance survives the landing that moved
the base.**

⚠️ **It has moved once more, and the two arrivals are READ here rather than counted, so the clean
sheet is 46 of 46.** At `7f30e87` the same instrument returns **1970** bullets over **465**
sections in **400** of **456** docstrings with **110** matching — **two** rows appear and **none**
disappears, both in `EllipticCurves.FunctionField.PullbackPrincipalityNGeneral` and both arriving
with `8e55647`. Resolved against `#check` telescopes and not against the `theorem` lines:

* `exists_nsmul_divisor_eq_divisor_mulByNEndo_of_galois` claims *"**No `[DecidableEq F]`**"* and
  that *"it binds `[W.IsElliptic]`"*. The telescope is `[Field F] {W} [IsElliptic W] (N) [Field N]
  [Algebra F N] [FiniteDimensional F N] [IsGalois F N] [DecidableEq N] {n}` ahead of the nine
  *"Reach:"* items, so both halves hold and nothing beyond the setting is unlisted. **TRUE**
* `mem_torsion_baseChange_of_nsmul_eq_zero` claims it *"binds `[DecidableEq F]` and
  `[DecidableEq N]` and no `[W.IsElliptic]`"*. The telescope is `[Field F] {W} [DecidableEq F] (N)
  [Field N] [Algebra F N] [DecidableEq N] {n} {x y} (hns)`. **TRUE**

⚠️ **Three cells of that reading are worth more than the verdicts, because each retires a figure
the next sweep would otherwise re-spend.** The census is **identical at `60e3031` and at
`7f30e87`** — and `7f30e87` is this section's own landing, which is the control that the seed reads
`.lean` docstrings and nothing this document says about itself. It is **also identical at PR #882's
head**, whose only commit rewrites the very file both new rows live in: that round's hunks fall in
a `### FINDING` block and in `## Recovery`, not in `## Main statements`, so **0 appear and 0
disappear** and this cell does not depend on the order those two land in. ⚠️ **And the instrument
is a fourth independent implementation of the published seed, calibrated before use on every cell
this section already carries** — `8f95181` and `6c22e12` at **1696 / 425 / 364 of 419 / 64**,
`b764fae` at **63**, `7ba33ed` at **1942 / 106**, `6a733e1e` and `0094b84` at
**1954 / 462 / 397 of 453 / 107**, `3f9e3239` at **1967 / 464 / 399 of 455 / 108**. **A census
instrument that reproduces the behaviour delta at `b764fae` as well as the totals is being checked
against the recogniser rather than against a number.**

⚠️ **Two conventions decided rows, and both are written here so that the next sweep does not
convict what this one cleared.** The first is the setting convention above, applied as it stands.
The second is not in its list of three: ⚠️ **`[W.IsElliptic]` is carried as setting by a *"no
hypothesis beyond …"* clause, not denied by one.** ⚠️ **The reading is fixed by a row this section
has ALREADY read and quoted, not by this sweep**: `EllipticCurves.Torsion.OmegaChordSum`'s
`card_torsion_eq_sq_of_odd` is one of the three complete-count rows of the 64 above, its clause is
quoted there as *"with no hypothesis beyond `2 ≠ 0` and `(n : F) ≠ 0`"*, and its signature binds
`[W.IsElliptic]` — which that clause does not name. **So a sweep that convicts this reading
convicts a certified row first.** ⚠️ **No population figure is published for the shape, and that
is deliberate**: the census would be a clause pattern crossed with elaborated telescopes, this
round publishes no such pattern, and *publish the recogniser beside any count, or write no count*
(`#1749`) forbids the count rather than excusing it. ⚠️ **The same holds file-locally for a
standing characteristic.** `EllipticCurves.Torsion.TwoTorsionCharTwo` writes *"no hypothesis on
`F` whatsoever"* **beside** *"characteristic `2`"* in one sentence, so its `_of_char_two` rows are
read modulo `h2 : (2 : F) = 0`; that is the ground on which
`torsion_two_eq_bot_of_a₁_eq_zero_of_char_two`'s *"needs no hypothesis on `F` at all"* is TRUE
where `MulByTwoFibreInfinity`'s bare *"No hypothesis on `F`"* was FALSE. ⚠️ **The two differ by
what the file says elsewhere and by nothing in the row**, which is why no verdict here was read
off a row alone.

⚠️ **One prediction filed forward with this population is REFUTED, and it was an instrument
artefact rather than a signal about the rows.** `` `[A-Za-z][A-Za-z0-9_.']*_[A-Za-z0-9_.']*` ``
finds no backticked `snake_case` identifier in **21** of the 43 — and **20** of those 21 do name a
declaration, in names this tree spells with `Ψ`, `ψ`, `ω`, `Φ` and the subscripts `₁`–`₈`, every
one of which that character class excludes. ⚠️ **Widen the token to any backticked run carrying an
underscore and the figure is 1 of 43**, and that one is
`EllipticCurves.Torsion.TriplingGaloisTower`'s base-change-bridges row, which names no
declaration and is a false positive of the seed. **So the
false-positive share did not rise with the population: it is 7 of 43 here against 13 of 64 there.**
⚠️ **An ASCII-only character class is not a neutral instrument over this tree**, and a census
keyed on identifier shape owes that limit beside its figure.

⚠️ **A third limit of the recogniser, measured because a recogniser owes its limits** (`#1749`).
The bound `/-!(.*?)-/` this section prescribes is non-greedy and **not** comment-nesting-aware, so
a module docstring that displays `` `/-! ## … -/` `` inside a code span ends at that `-/`, where
Lean — whose block comments nest — reads on. ⚠️ **Exactly one file is affected at `0094b84`**,
`EllipticCurves.Torsion.TriplingGaloisTower`, whose docstring the published bound reads to
**10,486** of its **18,923** codepoints. ⚠️ **The cost falls in the denominator and not in the
numerator**: a nesting-aware bound returns **1962** bullets and **107** matching rows against the
published **1954** and **107**, and that file's one row in the population is the same row
truncated and whole. **The 107, the 43 and every verdict above are therefore unaffected**, and the
count above is left as the published instrument returns it.

⚠️ **The population, with the recogniser beside it**, because this section's own rule is
*publish the recogniser beside any count, or write no count*. Scan **whole** `## Main *` blocks —
not the prose above the first bullet, since one instance sits inside a bullet and another after the
list — for a sentence carrying both a quantifier (`every`, `all`, `none`, `no `, `each`,
`not read`, `neither`) and a bullet-subject (`bullet`, `row`, `the entries`, `list above/below`),
and **read** every hit rather than counting it. ⚠️ **Date the answer.** At `064208e` with `#1686`
applied — the tree this paragraph ships in — ten `## Main *` blocks in ten files close over their
own bullets, in three live wordings: **one** in `DeterminantModGeneral`'s, which is that block
alone; **eight** in the routing form above (`WeilPairingAlternatingAssemblyN`,
`WeilPairingAlternatingBaseChangeN`, `WeilPairingTranslationSlotHprinN`, `WeilPairingGaloisRootN`,
`WeilPairingAlternatingConsumerN`, `WeilPairingDivisorSlotBilinearHprinN`, `MulByNFibre` — whose
instance is scoped inside a bullet — and `EllipticCurves.Torsion.PrimaryTowerOdd`); and **one**
converse — *"Every bullet above names the whole explicit hypothesis list"*
(`EllipticCurves.Torsion.WronskianSeparable`, over a list that carries no register on purpose, so
*"a register cannot make a count true"* does not bite; its failure mode is the mirror one, going
stale when a bullet is **simplified** rather than completed). A fourth wording — *"the bullets … are
not read for hypotheses at all"* — survives only as `PrimaryTowerOdd`'s own retired quotation
(`#1656`, PR #667), and was live at `ee0b8a4`. That is what the date is for.

⚠️ **Four ways to miscount it, all of them live, and no two agree.** Over the first wording: a
**phrase**-keyed census reads eight where there is one, because the other seven — `…AssemblyN`,
`…AlternatingBaseChangeN`, `…TranslationSlotHprinN`, `…GaloisRootN`, `…AlternatingConsumerN`,
`…DivisorSlotBilinearHprinN` and `MulByNFibre` — each carry it as a retired quotation under
`### Retired claims`, and a retired quotation is not a live universal; and a **line**-keyed `grep`
reads three of those eight, because the phrase wraps mid-sentence in five of them. ⚠️ **The gap
widens with every repair**, since a repair converts a live instance into a retired quotation and
leaves the occurrence count where it was. Over the converse: a **file**-keyed census reads two where
there is one, because `…AlternatingBaseChangeN` quotes `WronskianSeparable`'s sentence as a
cross-reference to another file's register — ⚠️ **and a census that joins lines without collapsing
whitespace cannot see that second occurrence at all**, since the quotation wraps inside an
*indented* bullet and leaves two spaces mid-phrase. Join the lines **and** squeeze runs of
whitespace, or the trap you are publishing a warning about is invisible to your own recogniser.

⚠️ **What falsifies that universal is a bullet that NAMES a hypothesis, not only one that counts
them.** The sentence says the bullets give the conclusions *and not the hypotheses*, so a bullet
that gives one is a counterexample; counting is the narrower, stronger failure that the routing
form's second branch is about. ⚠️ **Do not borrow the routing form's leniency to certify the
sentence it replaced** — *"naming some without counting is neither"* is a branch that form **adds**,
and the want of it is why the old wording had to go. The merged statement of the test is
`WeilPairingAlternatingAssemblyN`'s own retired-claims paragraph, which retires the wording as
*"false already of the first bullet, which has **named** `hprin` and the halving point"*.

⚠️ **`#1647`'s no-sweep instruction stands, and it is an instruction rather than a verdict.**
The rule is to replace the universal *"in the rest as each is touched rather than re-arguing it"*;
this tree does not pre-emptively edit sentences that are not wrong, and nothing here orders a sweep.
But the exemption it grants is *"true of its list"*, and ⚠️ **that truth is a per-bullet reading,
not a property of the phrase**. **Eight** blocks are on record as having carried this wording — the
eight the phrase-keyed census finds — and **seven** have now been read row by row — `…AssemblyN`
(`#1647`), `…AlternatingBaseChangeN` (`#1650`, whose retirement records the read), `…GaloisRootN`
(`#1662`), `…AlternatingConsumerN`, `…DivisorSlotBilinearHprinN` and `MulByNFibre` (`#1686`), and
`DeterminantModGeneral` — and **only `DeterminantModGeneral` held.** (The eighth,
`…TranslationSlotHprinN`, retired the wording on a prose contradiction rather than on a row read, so
it is not counted here.) One falsifying shape is a house idiom rather than an accident: an
`_of_smooth` or `_of_ne_zero` bullet reading *"the same at every `3`-smooth `n ≠ 0`"* or *"at every
`n` with `((n : ℤ) : F) ≠ 0`"* names an explicit binder of its own declaration. ⚠️ **It is not the
only shape** — `MulByNFibre`'s falsifying rows name no index condition at all; they restrict the
ambient quantifier (*"at an affine `P` that is not `n`-torsion"*, *"regular off the `n`-torsion
locus"*) over the very binders that restriction is, which is the same naming in a sentence that does
not look like a reach clause. ⚠️ **So do not write *"the rest are fine"* from a census, and read the
list before quoting a table's `true` column** — a census tells you where a phrase is, never whether
it is true there.

⚠️ **Repairing a sentence already known to be false is not the sweep `#1647` ruled out**, which is
the ground `#1686` repaired the three false blocks on rather than leaving them to the next agent who
happened to touch them. ⚠️ **`DeterminantModGeneral` was left standing on the same ground**: its
universal is true of both its lists, so editing it *would* be the pre-emptive edit `#1647` ruled
out. What the routing form binds unconditionally is the **next** register written or repaired —
including any written from this section.

One file shows the reach half in both directions, and both readings are decided by the signatures
rather than argued:

* **Reached.** `MulByNFibre`'s register is the first bullet of its `### The general layer` sub-list.
  The bullet five rows below it reads *"…`comapProjPointN_add_torsion_of_ne_zero`, and **over
  `F̄`** `…card_fibre_comapProjPointN_projPointOfPoint_of_ne_zero`, …"* — a reach clause naming the
  instance and nothing else, over a signature binding `(2 : F) ≠ 0` and `((n : ℤ) : F) ≠ 0` as well.
  Those are the two the register names, so the bullet is compliant relative to it, and repairing the
  row in place would mean repairing all thirteen. ⚠️ **The register is not the whole account of that
  row, and a reach verdict is owed one for every binder.** That signature binds a third hypothesis,
  the transcendence `h`, which the register does not name; it clears on the **derivability**
  exemption, whose price that file has already paid — `MulByNFibre`'s `## The non-constancy
  hypothesis is not named in the headlines below` cites both derivations, and the general one runs
  from `(2 : F) ≠ 0` and `((n : ℤ) : F) ≠ 0` — exactly the two the register names.
  ⚠️ **It does not clear as a data argument**, which is what this bullet used to say: `h` is a
  condition on the index, and `### Reach clauses` convicts exactly that omission by name in
  `ramificationIdxN_pos`. Same verdict, and not the same ground (`#1631`).
* **Not reached.** The **outer** `## Main statements` list higher up the same docstring is a
  different block. Its own head is *"⚠️ Every public declaration of this file is listed"* and
  declares no register, so its bullets are read against that and get nothing from the sub-list below
  them — including the two that carry a reach clause of their own over signatures binding more
  (`#1616`).

And the gate-discharge half, where the subject legitimately sits two `##` sections above the list:
`residueDegreeN_none_eq_one` (`EllipticCurves.FunctionField.MulByNResidueDegree`) is bulleted
*"`f_∞ = 1`, at every `n` at which `[n]` is non-constant, unconditionally"* under a list whose head
declares no register at all. The word's subject is written out in full under that module's
`## ⚠️ The residue degree at infinity is *not* in the composition class` — the declaration *"holds
at every `n` at which `[n]` is non-constant, with no `3`-smoothness, no `(2 : F) ≠ 0`, no
`(3 : F) ≠ 0`, no `[IsAlgClosed F]`"* — and that is a gate list, the hypotheses `#1214`'s
composition route carries and this one does not. A subject, not a hypothesis list, and compliant
where it stands.

⚠️ **Read the two clauses of that bullet separately, because the halves decide independently — and
this row is the worked example of their deciding differently.** The gate-discharge half was
compliant throughout. The reach half was **not**, and it is the half that had to be repaired.

**The old reading, retired** (`### Retired claims` below): until `#1636` (PR #653) the row read
*"`f_∞ = 1`, at every `n`, unconditionally"*, naming no index condition at all. This document
used to clear that on the ground that the declaration's one propositional binder is a **data
argument of the object the bullet is about** — `residueDegreeN n hn p` does not typecheck without
it, so there was *"no reach for the clause to misreport"*. `### Reach clauses` withdraws that ground
(`#1631`): `hn` is a condition on the index, which is one of the two things a reach clause reports,
and that section convicts the identical omission by name in `ramificationIdxN_pos`, whose signature
is this one. ⚠️ And *"unconditionally"* is the strongest form of a clause, not a mitigation of it —
which is why the repair **kept the word, in place**, and moved only the reach half. A bullet that
mixes the registers is answerable to both, and a row that clears is not evidence that it cleared on
the ground you had in mind.

⚠️ **That list's head still declares no register, and the reason is worth a clause of its own.** The
`DeterminantModGeneral` opener above is *"the cheap repair for a list whose bullets are each short
of the same hypotheses"*, and `…residueDegreeN_two` and `…residueDegreeN_three` bind **no**
transcendence — they take `(2 : F) ≠ 0`, the second `(3 : F) ≠ 0` as well, and derive it. A register
saying every statement below takes the non-constancy would be **false** of them: the opener's
*"each"* is doing the work, and a row that **derives** a hypothesis fails that test exactly as a row
that never needed it would. So the repair named the condition in the rows that make a claim
about which `n` are reached — this one and `…residueDegreeN_eq_one` — and the module block
records why there is no register, so the next census does not re-measure the list to find out.

⚠️ **A register says what a list omits. It cannot make a count true.** So a register's reach stops
exactly where `### Gate-discharge claims` stops, and for the same reason: *"the whole hypothesis
list"*, *"the single hypothesis"*, *"from nothing but"*, *"and nothing else"* are claims about the
hypothesis list itself, and no sentence elsewhere in the block supplies a member such a claim
excludes. The compliant form is `ψ_pair_mul_of_ψ_eq_zero`
(`EllipticCurves.Torsion.OmegaPairCoprime`), bulleted *"at every `n : ℤ` and with no hypothesis but
`ψₙ(x, y) = 0`"* over a signature whose one propositional binder is that equation.

⚠️ **The traffic runs one way.** A block repairs a bullet; a bullet repairs nothing. Under
`### Scope of the rules above` a module list and the file's headlines are two blocks, so a row this
section clears as a bullet is still held to the rules above as a headline, and the two layers are
repaired separately. **A sibling bullet is not a register either** — it is a bullet, so a count in
one bullet is not completed by the hypotheses another bullet of the same list happens to name.

⚠️ **This is not a further exemption, and it must not be counted as one.** `### Reach clauses` above
states its exemptions and `### Gate-discharge claims` adds the next; this section adds none. It is a
**scoping** rule — it says which text a bullet is read against — and every exemption above then
applies to a bullet exactly as it does to a headline.

⚠️ **And it does not reopen *"a phrase a file coins for itself earns nothing here"*** in
`### Gate-discharge claims`. That clause governs a **declaration headline**, whose unit is its own
docstring, and it turns on an asymmetry it names: a reader who meets a partial hypothesis list in a
headline *"has no signal that a completing sentence exists anywhere"*. A bullet's own docstring
**is** the module docstring. A register at the head of its list is *in the same docstring* rather
than *"prose sitting elsewhere in the module"*, and the reader of a bullet is reading the list. The
boundary is unchanged; the **unit** moves with the layer, which is the same fact stated twice.

Measured at `7495d3e`, and the two halves of this paragraph are of different qualities. **1696**
bullets in **425** `## Main *` sections — reproduced to the unit by three independently written
extractors — spread over **364** of the tree's **419** module docstrings. Measured **once**, on
`#1614`, by a join against the elaborated environment: **1690** of the 1696 resolve to a declaration
of this development, the misses being anonymous `instance :` rows, brace-contracted name patterns
and two prose bullets. **59** rows are triaged individually on `#1614` and are named there.

⚠️ **That 59 is a triage set, not a measurement, and the number should not be quoted as one.** It
was found with a phrase list — `the whole hypothesis list`, `the only hypothesis`,
`the single hypothesis`, `the only gate`, `unconditional`, `with no hypothesis`,
`no hypothesis beyond`, `the entire hypothesis`, `the only input` — and on this tree that list is
not stable under choices no one would think to publish. The same nine phrases over the same 1696
bullets return **57** matched case-sensitively, **59** case-insensitively, and **54** if a bullet is
terminated at the end of its list instead of absorbing the module prose that follows it; four
further phrases the tree does use (`nothing else`, `nothing but`, `no other hypothes…`,
`the only remaining`) add **6** more. `#1584` is the standing record of what a phrase list does to
this front, and this is the same fact one layer up: **publish the recogniser beside any count, or
write no count.** The remaining ~1640 bullets have not been read on this axis, and this section is
not a claim about them.

### Scope of the rules above

They apply **per block, not per phrase** — a `## Main statements` list, or a `generality` table
column, is one place. A fix that repairs one row and leaves its neighbour partial makes the
block worse rather than better, because the reader now has two rows in different registers and
no way to tell which is which.
⚠️ **The neighbour may instead be compliant on the OTHER branch, and that case is not the one
above** (`#1748`). *"Names every hypothesis, or it names none"* has two compliant sides, so a
section can hold a row naming a field condition beside one that binds it and names none, with
neither row defective. Measured at `823cf46` over
`FunctionField.MulBy{TwoFibreAffine,TwoFibreInfinity,ThreeFibre,NFibre}` — a row listed when it
binds `(2 : F) ≠ 0` or `(3 : F) ≠ 0`, from its own binder list or a `variable` line above it, and
its headline names neither — **49** rows sit in the silent register and **five** `` /-! ### ``
sections hold both. ⚠️ **Two of the five are in `MulByNFibre` itself**, and they are the answer
rather than the problem: its silent rows are `comapProjPointN_pointClosedPoint_of_eval_ΨSq_eq_zero`,
which the first bullet of `### Reach clauses` clears by name, and
`card_fibre_comapProjPointN_le_sq_five`, which the fixed-numeral discriminator above exempts.
**A split section is sound when every silent row in it is silent on a ground the reader can reach,
and unsound when the difference is left to be guessed.**
⚠️ **The other three were unsound and are repaired by insertion rather than by a note** (`#1748`).
Two are `ord_*` rows — `ord_mulByTwoEndo_genX_nonneg`, `ord_mulByThreeEndo_genX_nonneg` — standing
beside a crux a ruling had just repaired, carrying a **word-identical** point clause and naming
nothing, with the reason they are silent (`#1728` sorts them *predicate*, because the transposed
pair `ord_mulBy{Two,Three}Endo_genX_neg` proves the **opposite** off the clause) recorded only for
`MulByNFibre`'s copies. The third is `comapProjPointThree_projPointOfPoint`, left as the one silent
row of four by `#1743`, whose general-`n` counterpart
`comapProjPointN_projPointOfPoint_of_ne_zero` names its conditions. `fddba5c` (`#1664`, PR #684)
met this shape in `MulByNFibre`'s own six-row section and took the insertion *"even though it puts
all four on the predicate side"*, because an insertion is branch-neutral (`#1728`) and needs no
ruling to be defended; the same move transposed to the ancestors costs three lines and makes the
three indices read alike.
⚠️ **The remaining 46 are NOT defects and none is repaired**, so do not read the figure as a
backlog. They sit in sections no ruling has reached, so there is no split to close, and converting
them would be a preference dressed as a sweep.

Consequences worth stating, because each has cost a review cycle. ⚠️ **Their number is
deliberately not given** (`#1667`): this line read *"Four consequences worth stating"* from
`f1d1473` (`#1569`, PR #620) onwards and was true until the *"A heading is one source line"*
bullet below made it five, in the same PR that wrote the bullet. A numeral standing over a list
is falsified by whatever next extends the list, and no bullet under it can repair the numeral —
which is `### Module-block bullets`' *"A register says what a list omits. It cannot make a count
true"*, one layer up, in this document's own prose. They are:

* **The subject decides, not the string.** *"it is `natDegree_ΨSq` that needs `(n : F) ≠ 0`"*
  is correct — Mathlib's `natDegree_ΨSq` asks that and nothing else — while the identical
  phrase about a statement of this development that also takes `h2` is a defect. Resolve each
  clause's subject to a declaration and read its binders; a `grep`-keyed sweep of this class
  produces false positives as well as false negatives.
  ⚠️ **A reach clause is a clause, not a sentence** (`#1679`). A sentence can carry two subjects,
  and a condition named for one of them does **not** reach the other; a census keyed on sentences
  cannot see the difference, because the sentence passes its field test on either subject's
  strength. The instruction above therefore reads *"each clause's subject"*; it read *"the
  sentence's subject"* until `#1679`, which is a **completion** and not a retirement — the old
  words were partial rather than false, which is the test `### Reach clauses` sets.
  ⚠️ **The class is anti-monotone under this front's own repair programme**, so it does not shrink
  on its own: repairing one clause is what hides its neighbour. All four rows `#1679` found are
  `#1137`'s own residue — PR #602, PR #605 and PR #616 each wrote `(2 : F) ≠ 0` into the clause
  beside `nsmul_surjective_of_two_ne_zero`'s and left that one naming the index alone, and from
  each of those commits a sentence-keyed test reads the whole sentence as clear.
  ⚠️ **A list item is a unit too.** Two of the four are bullets, where what the reader meets is
  the bullet and not the sentence a splitter would cut out of it.
* **`(n : F) ≠ 0` and `((n : ℤ) : F) ≠ 0` are different clauses.** The `_of_natCast_ne_zero`
  and `_of_intCast_ne_zero` suffixes say which, and a reach clause should match the suffix.
* **Declaration headlines are reach clauses too**, and doc-gen surfaces them in preference to
  module prose. A `## Hypotheses` section elsewhere in the same module does not repair a
  partial headline. ⚠️ **Nor does a sentence lower in the declaration's own docstring** (`#1660`).
  This is where this rule and `### Gate-discharge claims` part company, and not a second
  application of one boundary: that section's exemption is *"in the same docstring"* precisely
  because a gate-discharge word is **visibly relative to something**, so a reader who meets one
  knows a subject for it exists and reads on. `### Module-block bullets` states the asymmetry —
  *"A partial reach clause carries no signal at all, so the register has to be where the reader
  meets it"* — and for a headline the place the reader meets the clause **is** the headline.
  The worked case is `residueDegreeN_none_eq_one`
  (`EllipticCurves.FunctionField.MulByNResidueDegree`), whose headline read *"`[n]∗` is residually
  trivial at the point at infinity, at every `n`"* while a ⚠️ in the same docstring named the
  non-constancy as *"the only thing `n` is asked for"*: the ⚠️ was true, the headline was false at
  `n = 0`, and a reader who stopped at the headline had nothing telling them not to.
  ⚠️ **The paragraph opening this section decides it the same way**, which is what makes the
  ruling cheap rather than a new cost: that headline's two neighbours in the same section were
  short of the same condition and take the insertion on nobody's argument, so clearing this one
  would have left the block with rows in two registers and no way to tell which is which.
* **A heading is one source line, because a heading that wraps is a heading that is cut off
  there** (`#1667`). A Markdown ATX heading (`# `, `## `, …) is a leaf block that ends at the end
  of its line, and there is no continuation syntax, so a title written across two lines renders as
  a heading containing the first line and an ordinary **paragraph** containing the rest. The reader
  who consults the heading — the reader this section's previous bullet is about — is therefore
  given a clause chopped at whatever word the line broke on:
  `EllipticCurves.FunctionField.MulByNFibre`'s H1 named two index ranges and doc-gen printed
  *"…and the fibre over one — at"*. ⚠️ **The hundred-column limit is therefore a limit on what a
  heading may *say*, not only on how it is typed**: a title that does not fit has to be shortened,
  and a reach clause that does not fit inside the shortened title has to be dropped to the
  *"or it names none"* branch of `### Reach clauses` and stated in the prose below, not wrapped.
  ⚠️ **Prefixing the second line with its own `#` does not join it either** — it makes a *second*
  heading. `EllipticCurves.FunctionField.WeilPairingDivisorSlotBilinearHprinN` carried
  *"…and it stopped being so"* / *"twelve hours ago"* as two `##`s, and doc-gen printed
  *"twelve hours ago"* as a section of the module. ⚠️ That variant is invisible to a census keyed
  on *"a heading followed by prose"*, which is how it survived the sweep that found the other
  three: read every heading whose text begins in lower case as well.
  ⚠️ It is only headings. A paragraph, a bullet and a `**bold**` span all cross a line break
  correctly, and several repairs on this front rely on that.
  ⚠️⚠️ **It is EVERY heading level and not only a module `# H1`, and that was already decided on
  this page twice over rather than being widened by `#2325`.** First, this bullet's own enumeration
  is (`# `, `## `, …), which generalises over the levels instead of stopping at two, and its
  ground — the reader is handed a clause chopped at whatever word the line broke on — is
  level-independent, because CommonMark makes every ATX level a leaf block by the same rule.
  Second, **the bullet below rules on the three layers by name** — *"a module `# H1`, a `##`
  heading inside a module docstring, or a standalone `/-! ### … -/` section header"* — and fixes
  one unit for all three; a ruling about what a `###` heading *reaches* presupposes that a `###`
  heading is a heading for this page's purposes. ⚠️ **What does NOT generalise is the RANKING
  argument, and it is about severity rather than scope**: *"an H1 is the block this page ranks
  above module prose"* makes a wrapped `# ` worse than a wrapped `###`, and a reviewer should say
  so when charging them together — but a `###` whose continuation carries load renders exactly as
  badly, which `#2325` confirmed by running `markdown-it` on both shapes rather than inferring it.
  `#2325`'s two `### ⚠️ FINDING …` sites are repaired on the enumeration-and-ground reading above,
  and its `# H1` site on that reading **and** the ranking one.
  ⚠️ **The census is a gate in `.orchestra/validation.sh` from `#2325` onwards rather than a sweep
  someone remembers to run**, and the reason it could be wired at all is that the same commit took
  the defect count to **0**: a hard gate with a standing baseline fails every push, which is why
  `#2325` repaired first and wired second rather than the other way round. Its population is this
  page plus the tracked `.lean` files — `#1667`'s own population, not a narrower one — and both of
  its recognisers and both of its exemptions are in the script with the reason each is there.
  ⚠️⚠️ **IT DOES NOT REACH A COMMIT-MESSAGE BODY AT `must` GRADE, AND THE CARRY HAS TO BE MADE
  RATHER THAN ASSUMED** (`#2326`). The bullet below rules on three layers by name and a message
  body is none of them, and this page has held once already that a file-layer definition does not
  travel by itself: `## Reviewing`'s message-layer touching test says *"`### The render gate`
  defines *paragraph* for a **file** and for nothing else; no clause carries that definition to a
  commit message"* (`#2205`). ⚠️ **The grade is `should` and the ground is GREPPABILITY rather
  than rendering**, which is a departure from this bullet's own ground above and is the one cell
  that cannot be checked here: no instrument in this repository reads how GitHub displays a
  commit, so a `must` resting on a truncated reader would rest on an unmeasured claim.
  ⚠️⚠️ **What IS measured is that every reader of a message this page prescribes is a
  line-oriented SOURCE reader** — `grep -n` in `### Answering a verdict`, `difflib` over stripped
  lines in the touching test, a marker key over flattened messages in `### Tool-behaviour claims`
  — **and a title split across source lines is invisible to all of them.** Over `git rev-list` at
  `484de4ac`, `2026-10-06 02:5xZ`: **868** bodies, **940** ATX headings, and **12** wrapped titles
  in **8** messages, every one of the 12 returning **0** under a whole-string search of its own
  body while every complete one-line title in those same eight bodies is found by it.
  ⚠️ **It escalates to a `must` where the cut half carries a figure, a name or a predicate the
  round's own argument needs**, because what is lost there is the enumeration this page requires
  and not the typography: `22db66e2`'s cut half is a NUMERAL, `8e4a1dfc`'s is the PREDICATE, and
  `d60c3ccc`'s first title promises *"BOTH HALVES"* and cuts the clause naming the second. ⚠️
  **The landed messages are out of scope for repair and this rule is PROSPECTIVE**, by
  `### Tool-behaviour claims`' own ruling that a landed message is unamendable so what is owed is
  a count and not an edit; no sweep over them is proposed here and none would be executable.
  ⚠️⚠️ **AND THE `#`-PREFIXED VARIANT NEEDS A STRUCTURAL RECOGNISER, BECAUSE THE LOWER-CASE
  READING IS A HEURISTIC THAT UNDER-COUNTS IT.** A run of two or more CONSECUTIVE ATX heading
  lines returns **8** runs in **5** messages at that base with **0** false positives, it CONTAINS
  every one of the lower-case reading's **6**, and the **2** it adds open in upper case and in a
  code span, so no reading of the continuation's first character can reach them. ⚠️ Its exposure
  over the tracked files is **0** at **2551** headings, so wiring it into the gate above would
  cost nothing today and is left to a round that owns that gate. ⚠️ **One defect is one TITLE and
  not one source line**, which is the convention this census takes and the reason it has one: a
  **314**-codepoint title over **four** `##` lines is counted once.
  ⚠️⚠️ **The two message-layer gates are INDEPENDENT and neither subsumes the other**, which is
  measured and not argued, and it is the answer to *"if the body is not read as Markdown the `**`
  gate is meaningless, and if it is the heading is cut"*: **7** of the 8 bodies carrying a wrapped
  title render **0** surviving literal `**`, and **4** of the **5** bodies that do carry one hold
  no wrapped title at all. One asks whether a delimiter pairs in the SOURCE and needs no reader;
  the other asks what a reader is handed. ⚠️ **They overlap on exactly one body, and there the
  heading is the CAUSE** — all **4** of `ebb8735b`'s surviving `**` come from its two multi-line
  titles, proved by a control that changes not one word: joining the four-line title to one source
  line takes the count to **2** and raises `<strong>` by exactly **1**. **So a surviving literal
  `**` is a signal of this defect**, and it is what found the recogniser's blind spot above.
* **A heading is its own unit, so a reach clause in one is read against that line and nothing
  else** (`#1879`). The bullet above fixes what a heading *is*; this fixes what it *reaches*.
  `### Reach clauses` fixes the unit for a **declaration headline** — its own docstring, and by
  `#1660` not even a sentence lower down in it — and `### Module-block bullets` fixes it for a
  **bullet**, whose unit is the list it sits in. Neither covers a module `# H1`, a `##` heading
  inside a module docstring, or a standalone `/-! ### … -/` section header, and the two grounds
  already on this page point opposite ways: the rendering ground — *"doc-gen renders the rest of
  **this** docstring beside the headline"* — clears an H1, because doc-gen does render a module
  body beside its H1, while `#1660`'s ground — *"the reader meets the clause first and a partial
  one carries no signal"* — convicts it.
  ⚠️ **`#1660`'s ground governs, and neither reason for that is new.** First, the rendering ground
  is not what decides a headline either: `#1660` overrode it *inside a single docstring*, holding a
  completing sentence four lines below a headline insufficient, so *"the body is rendered beside
  it"* has already been held not to reach at the layer this one is being compared to. Second, **the
  bullet above already treats a heading this way, and its remedy is only coherent under this
  unit** — *"a reach clause that does not fit inside the shortened title has to be dropped to the
  'or it names none' branch … and stated in the prose below, not wrapped"*. If a heading's unit ran
  on into the prose below it, an over-long clause could be **continued** there and stay a naming
  clause; it is required to be **dropped** instead, and all-or-nothing in the heading is what that
  requirement means.
  ⚠️ **So the repair for a heading is usually the *"or it names none"* branch, and it is the
  cheaper of the two.** A heading is one source line inside a hundred columns and a complete
  hypothesis list often does not fit beside a title: deleting the clause from the heading and
  stating it in the prose below is compliant, costs no width, and is already what the bullet above
  asks for when the line overflows.
  ⚠️ **A heading over a LAYER may have no single hypothesis list to name**, which is the same
  conclusion reached from the other side. `EllipticCurves.FunctionField.MulByNGalois` says in its
  own `##` section *"Two ranges of `n` live in this file, and they must not be conflated"* that its
  two halves carry different conditions, so its H1's clause has no one list to complete and
  *"names none"* is the only branch open to it.
  ⚠️ **This is about reach clauses only and leaves `### Gate-discharge claims` exactly where it
  was.** A gate-discharge word is *visibly relative to something*, so its subject may sit anywhere
  in the module block: `EllipticCurves.Torsion.PrimaryTowerAlgClosed` runs one from its H1 down
  into the declaration headlines and is named above as the precedent for doing so, and
  `EllipticCurves.Torsion.PrimaryTowerOdd`'s H1 — *"at an odd `p`, **with no hypothesis left**"* —
  is compliant on that branch and is **not** convicted here.
  ⚠️ **It narrows nothing and retires nothing.** `### Module-block bullets`' *"the **unit** moves
  with the layer"* named the unit at two layers; this names it at a third, which
  `### Reach clauses`' *"false or merely partial"* test sorts as **completing**, and
  `### Retired claims` says completing retires nothing. `#1660` is untouched — it and this bullet
  give the same answer for the same reason, one layer apart.
  ⚠️ **The population, dated, with its recogniser — and it is a CANDIDATE set and not a conviction
  set.** At `58df5a5`, over every tracked `EllipticCurves/**.lean`: ATX headings inside `/-!`
  blocks, the file's **first** such block being the module docstring and every later one a section
  header, number **3193** — **421** module H1s, **1736** `##` / `###` headings inside a module
  docstring, and **1036** standalone `/-! ## … -/` and `/-! ### … -/` section headers. Over the
  heading text alone, case-insensitively, the substring alternation `at every`, `at each`,
  `at any`, `at a `, `at an `, `for every`, `for all`, `over a `, `over an `, `over any`,
  `over every`, `in every characteristic`, `in any characteristic`, `unconditional`,
  `prime to the characteristic`, `≠ 0`, `invertible`, `at composite`, `at odd`, `-smooth`,
  `at the numeral` returns **219** — 95 H1, 113 section header, 11 in-module. The narrower cut that
  names an index condition and no field condition returns **65** — 19 H1, 41 section header, 5
  in-module — and its two lists are case-insensitive substrings of the heading text like the seed,
  except that the backticks inside three of the index literals are **part of the literal**: those
  three are written with a space at each end, which CommonMark strips, so what renders is the
  literal exactly and the warning at `### Reach clauses` about a one-sided trailing space does not
  apply to them. Index:
  `prime to the characteristic`, `at every`, `at each`, `at any index`, `at a general`,
  `` for every `n` ``, `` `(n : F) ≠ 0` ``, `` `((n : ℤ) : F) ≠ 0` ``, `-smooth`, `at composite`,
  `at an odd`. Field, which excludes: `(2 : F) ≠ 0`, `(3 : F) ≠ 0`, `characteristic ≠`, `char ≠`,
  `characteristic other`, `characteristic zero`, `invertible`, `≠ 2`, `odd characteristic`,
  `charzero`, `char f`.
  ⚠️ **The cut is a second recogniser and not a partition of the seed, so do not try to rebuild it
  from the twenty-one above** — **16** of these 22 literals are not among them. Exhaustively: of the
  2²¹ ways of splitting the seed's own literals into an index list and a field list, 15808 reach the
  total **65** and **none** reaches the split 19 / 41 / 5.
  ⚠️ **Both cuts over-report and the second under-reports too, and the rows that have been read say
  by how much.** All **5** in-module rows are titles carrying no reach clause at all
  (`EllipticCurves.Torsion.ChordSum`'s *"The proof, and what each hypothesis is spent on"* is the
  shape), and `EllipticCurves.Torsion.PrimaryTowerOdd`'s H1 is one of the 19 and clears on the
  gate-discharge branch above. In the other direction the field list excludes H1s that do match the
  index list: **10** at `58df5a5` and eleven at `949369c`, the extra one `Torsion.StructureGeneral`,
  which PR #731 completed into the excluded set. **7** of them are the `TateModule.*General` family
  whose only condition was `ℓ ≠ char F`; they were outside the 65 and were **not** thereby cleared.
  ⚠️ **`#1885` read all seven against `#check`-level signatures at `949369c` and repaired them, and
  not one was a false positive**: all twenty-two declarations under the seven take `(2 : F) ≠ 0`.
  Twenty of the twenty-two take `(ℓ : F) ≠ 0` as well; the two that do not are `FreeGeneral`'s
  `exists_closure_pair_eq_torsion`, which is the `n`-level lemma, and
  `proj_surjective_of_two_ne_zero`, which holds on `h2` alone and says so in its own docstring. So
  all seven named the index condition and dropped the field one. Four name it in the heading; the
  other three, whose completed clause does not fit inside a hundred columns, take the
  *"or it names none"* branch above.
  ⚠️ **That repair moves the excluded set and not only the headings**: it takes the eleven at
  `949369c` to eight, four of them the family, because the three rows that dropped their clause
  leave the index list while the four completions stay in both.
  ⚠️ **What that leaves unread is the cut itself**: it returns sixty-two rows at `949369c`, six of
  them the five in-module titles and `PrimaryTowerOdd` above, and the other fifty-six are unread —
  that issue's work rather than this bullet's.
* **A nested list is closed by a blank line, and parent-level prose that resumes without one is
  swallowed by the sub-list's last row** (`#1833`). A `  * ` sub-bullet's own continuation lines are
  written at four spaces and are right at every site in this file. The prose that returns to the
  parent bullet's column is written at two, and CommonMark reads a two-space line touching the row
  it follows as a lazy continuation of that row rather than as a new block of the parent. The
  sub-list therefore never closes: the returning paragraph renders inside the final sub-item, and a
  second `  * ` run written after that paragraph joins the same list instead of opening a new one.
  ⚠️ **This file already writes the closing form once, so what follows is that form made general
  and not a new convention** — the blank line that closes the two-branch sub-list of
  `### Reach clauses`' first bullet and puts the paragraph opening *"Decide this only when you are
  about to CLEAR a row"* at the parent's own level, where it reads as the bullet's conclusion.

  ⚠️ **The census, at `b2d1981`, and every row of it is repaired in this commit.** Three of the five
  swallowed paragraphs open on a sentence of the form *"Both are repaired in this commit"* — a claim
  over **every** row of the list it closes, rendered as the closing sentence of **one row** of it,
  so a reader of the rendered page was told the last defect alone had been repaired and was shown
  nothing at all about the others. The five sites swallowed 190 lines of parent prose between them:
  `:464` in `### Reach clauses`, and `:2091`, `:2140`, `:2236` and `:2273` in this section.
  ⚠️ **The flattening is the same defect read from the other side.** Two source runs separated by
  swallowed prose render as one list, so the two rules in this section that carry two runs of
  sub-bullets rendered as a **four-item** and a **five-item** list where the source writes 2 + 2 and
  2 + 3, each with a heading sentence that introduces only its own run. Both split correctly once
  the blank lines are in, and no row of either moves.

  ⚠️ **The cost is one list turning loose and it is this section's**, measured with a CommonMark
  parser at both trees rather than inferred from the specification. A blank line inside a list item
  makes the whole enclosing list *loose*, so each of this section's top-level rules is now
  wrapped in `<p>`, and the ones that were already here carry vertical space they did not. Nothing
  else moves, and `### Reach clauses`' three-item list was one of the lists already loose, since
  it holds one such blank line, and every sub-list in the file stays tight. ⚠️ **And it is the
  only source form there is** — nothing ends a list and returns to the parent's prose without a
  blank line — so the choice is between that spacing and a paragraph rendered inside a row it
  quantifies over, which is a false claim on the page and not a matter of taste.

  ⚠️ **Where a NEW bullet may be added to a long top-level rule, which is the half of this that has
  already sprung.** A `  * ` written at the end of such a rule joins whatever sub-list came before
  it, however much prose sits between the two: PR #719's first round added two general rulings that
  way and they rendered as items six and seven of a three-item list about what a sha does. The only
  placement that reliably renders as a sibling of the top-level rules is `* ` at column 0 with its
  continuation lines at two spaces, which is the form every rule in this section already uses.
  ⚠️ **Check the render rather than reading the source**, with
  `readme-list-structure-render-check.js` from this project's memory: markdown-it in its
  `commonmark` preset, which agrees with the `cmark-gfm` that GitHub renders this page with.
  `marked` disagrees with it at four of the five sites and agrees at the fifth, which is what makes
  it useless rather than merely wrong: at `:2091`, `:2140`, `:2236` and `:2273` it cuts the
  swallowed paragraph off partway — after sixteen of the forty lines at `:2091` and after a single
  line at `:2273` — and reports the tail as parent-level prose, while at `:464` it swallows all
  forty-five lines and returns exactly what CommonMark returns. Measured at `marked` 4.3.0 and at
  18.0.11, which agree site for site, so a version pin does not rescue it; it was checked against a
  hand-written minimal case and discarded.

  ⚠️ **This changes what a reader sees and no ruling this file makes.** Each of the five paragraphs
  is moved by one blank line and not a word of any of them is touched, so no clause is false and
  none is partial. `#1667`'s *"a paragraph, a bullet and a `**bold**` span all cross a line break
  correctly"* stands untouched and is about the other mechanism: a continuation line does cross a
  line break, and what does not cross is the boundary out of a list, which only a blank line
  crosses. Nothing here retires, so `### Retired claims` does not bind.

  ⚠️ **None of the `markdown-it` `commonmark` figures enumerated below names the version it
  was taken under, while the `marked` comparison beside them names two** — `4.3.0` and `18.0.11`, at
  the end of the paragraph that discards `marked`, and **not** the one immediately above — so the
  page pinned the tool it rejected and left unnamed the tool it kept (`#2153`). Said rather than
  repaired by assertion, because for most of them it is not recoverable. **The ones that name no
  parser at all** are the `190` swallowed lines, the *"four-item"* and *"five-item"* pair,
  *"every sub-list in the file stays tight"* and *"items six and seven"*. ⚠️ **The other two
  are COMPARISONS, and it is their CommonMark half that is unkeyed**: *"four of the five"* sites and
  the *"sixteen of the forty"* and forty-five swallow lengths each need both parsers, and only the
  `marked` side of them carries a version. All seven were written by `b9d353e` (2026-09-07), whose
  message names no parser at all, and the first commit in this file's own history to name a
  `markdown-it` version is `c28c462` (2026-09-19), twelve days later. The two readings of the same
  kind below this bullet, the `2 / 7 / 16` block split and *"one paragraph and names no ref"*, were
  written by `ab5ec3a`, whose message does name one, for a different cell of the same commit:
  *"`markdown-it` 14.3.2 `commonmark`"*.
  ⚠️ **Unrecorded is not unreproducible, and the control is published rather than assumed.** Under
  `markdown-it` **14.3.2** and **15.0.2**, each installed into a package root of its own and read
  back through that root's absolute path, `readme-list-structure-render-check.js` over the whole
  file is **byte-identical**: **339** rows at `b9d353e` and **522** at `0eb7e8b`, the commit this
  bullet is written against, which this insertion takes to **523**. This section's own rules agree
  under both as well — **7 / 0** top-level rules and `<p>`-wrapped rows at `b2d1981`, **9 / 0** at
  `6c22e12`, **10 / 10** at `b9d353e` and **16 / 16** at `0eb7e8b`, unmoved by this insertion, with
  **0** loose sub-lists at all four. **So no figure here is in question by the version difference**;
  what is missing is the key and not the number.  ⚠️ **Every count in this paragraph is keyed
  to a sha rather than to *"this tree"*, and a rebase is what that buys against**: an earlier draft
  published the whole-file row count under the indexical, the branch was rebased under it
  **twice**, and the numeral stayed at the value of the head it was taken at — while the `339`
  beside it, keyed to a sha from the start, survived both.
  ⚠️ **And that script's install recipe is pinned by accident, which is how this bullet could lose
  its parser without anything failing.** Its header says to run `npm install markdown-it` *in
  `/tmp`*, and `npm` installs into the nearest enclosing package root, walking **up** from `$PWD`:
  this harness carries an untracked `/tmp/package.json` whose `^14.3.2` is already satisfied, so
  the unpinned command installs nothing, reports success, and the script's hardcoded
  `require('/tmp/node_modules/markdown-it')` resolves to whatever that root happens to hold — while
  the same command in a directory that has a `package.json` of its own resolves **15.0.2**.
  ⚠️ **Give the run a package root of its own, pin the version in the install itself, and read the
  version back through that root's absolute path.** A bare `require('markdown-it/package.json')`
  walks the same chain and reports the ambient answer, so it cannot tell the two apart.
  ⚠️ **Retired, and the emphasis is the source's NAMED OUTSIDE the quotation rather than
  reproduced inside it**, because the retired text carries italic-quoted spans of its own and an
  italic span inside an italic span is `<em>` inside `<em>`, which applies one style twice and
  shows a reader nothing. The clause read *"Five name no parser at all"* — **bold in the source,
  and wrapping the line break between `at` and `all`** — over a list whose third member was
  *"the `ten` and the `nine`"*, under an opening clause that read *"None of the seven
  `markdown-it` `commonmark` figures enumerated below"*. `#2354` (PR #952, `71aff0c8`,
  2026-10-07) deleted both numerals from this section count-free, so the page carries neither
  string: `section's ten top-level` and `the nine that were already here` each go **1 to 0** across
  that push while the other members hold at **2 / 3 / 2 / 2 / 2**, which leaves the ones that name
  no parser at **four** groups and the enumerated population at **six**. ⚠️ **It is one
  retirement and not two**: both cardinals stand over one population closed by one enumeration and
  are falsified by one push, and this section counts retirements and not copies. ⚠️ **And it
  is false rather than short.** `### Reach clauses`' *what could move this numeral* asks whether
  the sentence pins its own denominator, and both of these do — each is a *k* over a row set it
  names — so a dead member leaves a *k* with no *k*-th row, which is that section's own test for
  false. **Short is partial, over-reaching is false**, and the asymmetry is the whole of it: a
  population that can only GROW leaves a count merely short, while one that can SHRINK makes it
  over-reach. ⚠️ **The sha-keyed clause beside them is NOT retired and is not touched**:
  *"All seven were written by `b9d353e`"* names its own commit rather than this tree, so nothing
  later can move it — and it holds, which I checked rather than assumed: each of the ten strings
  this bullet's members are read by occurs exactly **once** at `b9d353e`, 10 of 10. What replaces
  the two cardinals that are retired is the membership above and no total, which is this section's
  own opening rule — *"no bullet under it can repair the numeral"* — applied inside the list it
  governs.

* **Sort the class before repairing it, and expect to do two things at once.** A headline that
  lists too few hypotheses takes an **insertion**; one that *also* asserts there are no others takes
  that insertion **and** a deletion or a re-scoping of the assertion — because *"with `(2 : F) ≠ 0`
  … as the only hypothesis"* names a hypothesis and then denies there is one. Both forms are on the
  board, and neither is insertion-free:
  * **Delete the assertion.** `card_torsion_pow_of_separable` and `finite_torsion_pow_of_separable`
    (`EllipticCurves.Torsion.OddTorsionCount`, PR #619) read *"at an odd `p`, from separability of
    `preΨ p` **alone**"*. The repair dropped *"alone"* **and** added the two conditions the list was
    short of, giving *"with `(2 : F) ≠ 0`, at an odd `p` with `(p : F) ≠ 0`, from separability of
    `preΨ p`"*. ⚠️ Deleting *"alone"* and stopping there would have left `h2` and `(p : F) ≠ 0`
    unnamed under a headline that still named `Odd p` — a proper non-empty subset, the defect again.
  * **Re-scope it**, which is the form to prefer wherever the word is true of a gate. Three of the
    `card_torsion_eq_sq_*` headlines (PR #622) said *"and nothing else"*;
    `card_torsion_eq_sq_of_wronskian_identity` went from *"at odd `n`, from the Wronskian identity
    **and nothing else**"* to *"with `(2 : F) ≠ 0`, at odd `n` with `(n : F) ≠ 0`, with the
    Wronskian identity **the only gate left**"*: the noun moves from *hypothesis* to *gate*, and the
    insertion then goes in beside it without contradiction. See `### Gate-discharge claims` above,
    which is what the re-scoped word is then read under.
    ⚠️ **The body prose has to follow the headline.** The same PR changed *"it is now the only
    **hypothesis**"* to *"the only **gate**"* and *"no second **hypothesis**"* to *"no second
    **gate**"*, a few lines below two of those headlines. A repair that stops at the headline leaves
    the docstring contradicting itself.
* **A cross-reference's direction is a claim about this page, and no register here reads one.**
  Every rule above is keyed on something else — `### Reach clauses` on hypothesis lists,
  `### Gate-discharge claims` on gate words, `### Module-block bullets` on a bullet's register and
  this section's other bullets on phrases, subjects and headings — while a pointer's target is a
  **location**, and none of those four recognises one. ⚠️ **Measured at `2947444`**, over
  `README.md`, case-insensitively, with the **noun-and-direction** seed — named here because that
  is the name every citation of it uses — `<noun>` + whitespace **within one source line** +
  `above` or `below`, where `<noun>` ranges over `discriminator`, `rule`, `test`, `bullet`,
  `clause`, `slogan`, `convention`, `paragraph`, `register`, `ruling`, `list`, `sentence`,
  `account`, `census`, `figure`, `table`, `note` and `branch`: **34** matches on 34 distinct
  lines, **none** inside a code fence. ⚠️ **The line key is the seed's and not the axis's**, and
  a noun whose direction word wrapped to the next line is not a match: the same key the distance
  seed in this list publishes for itself, and unstated here until `#2100`. The limits price it.
  **Five are not pointers at this document** and are excluded with their grounds: the match on
  `list above/below` is this page's own bullet-subject literal quoted inside a recogniser, and four
  more quote or describe a **module docstring**'s layout — *"quantifying over what is above them"*,
  *"no bullet below them"*, *"Every bullet above names the whole explicit hypothesis list"* and
  *"the sub-list below them"* — where the direction is a fact about that docstring and not about
  this page. **Twenty-nine point at this document. Twenty-seven of them point the right way and two
  did not**, and both were false at the commit that published them:
  * `### Gate-discharge claims`' *"The census **above** cannot see this shape"* — the census it
    names, `#1754`'s, was **46** lines *below* it at `5018e25`, the commit that wrote the sentence,
    and **104** below it at `2947444`.
  * this section's *"which the fixed-numeral discriminator **below** exempts"* — that discriminator
    is the second bullet of `### Reach clauses`, **1539** lines *above* it at `2947444`, and this
    section's own neighbouring clause names that section correctly one line earlier. First recorded
    in PR #695's review and re-observed in PR #707's and PR #712's without being paid (`#1803`).

  **Both are repaired in this commit, one word each**, on the ruling in `### Gate-discharge claims`
  above: a wrong pointer is a typo and not a claim, so nothing retires and neither takes a marked
  quotation. ⚠️ **One of the 27 is not forced by its own grammar and is named rather than counted
  silently**: *"the **3** the full test **below** finds"* in `### Reach clauses` resolves if the
  direction word attaches to where those three rows are listed, which is below it, and does not if
  it attaches to *the full test*, which is defined above it. It is read the first way here.
  ⚠️ **The seed's limits, because a published recogniser owes them** (`#1749`). It leaves **172**
  bare `above`/`below` tokens unread, and at least three of those are pointers it should have
  caught — *"the paragraph on ... below"*, *"is covered by no register in either file ... above"*
  and *"a register says what a list omits ..., below"* — all three of which resolve correctly, so
  **the population is wider than 34 and the two convictions are a floor, not a total**. ⚠️ **Inline
  emphasis defeats it**: `census **above**` does not match, which is why this bullet's own
  quotations of the two convicted rows do not re-enter the count. It is not fence-aware, so the
  fence check was run separately. And it sees **direction** only — a pointer wrong by **target** is
  invisible to it, as is one wrong by **distance**: *"the paragraph **immediately** above"* in
  `### Reach clauses` (`712c35e`, `#1608`, PR #639) pointed the right way at a paragraph two above
  it. ⚠️ **This commit takes those words out of that section** — the distance axis in this same
  list convicts that row and repairs its count — so what is quoted here is dated to the commit that
  wrote it and is not a claim about what that section reads now.
  ⚠️ **The line key is a limit as well, and it is worth exactly three.** Taking the whitespace as
  `\s+` over the whole blob rather than within one line returns **37** where this sentence
  publishes 34, and it is **+3** at every one of the five refs this page dates this seed at and at
  `c97ba1a` as well — 37, 43, 43, 45, 52 and 58 against 34, 40, 40, 42, 49 and 55 at `2947444`,
  `d3a4ac5`, `5a2fe24`, `444da7f`, `77fb54d` and `c97ba1a`.
  ⚠️ **It is the same three wrapped pairs at every one of the six**, and all three were read
  rather than counted: `paragraph` / `above` and `rule` / `below` in `### Reach clauses`, and
  `list` / `above` in `### Gate-discharge claims`, are each a cross-reference at this page and
  each points the right way, so the line key costs this axis **no** conviction — which is exactly
  what it costs the distance axis. They sit inside the
  *"wider than 34"* limit stated here, and they sit inside it as **read** and not as unread.
  ⚠️ **The same question was put to the other two seeds and they answer differently, which is
  why it is worth stating.** The nine-word seed is inert under it: it anchors on a single token,
  so a blob reading and a line reading agree at all six refs. The distance seed's
  already-published line key is **live**, worth **+1** at `2947444` and **+2** at the other five.
  So the flag is not decoration on the one seed of the three that carried it, and this is the
  seed that wrapped. ⚠️ **The 172 is dated to `2947444` and is not re-keyed here**, as the 34 is
  not.
  ⚠️ **This bullet is inside its own
  population, so the figure moves by being stated.** Re-run at head and the same seed returns
  **40**: the two repaired rows still match, with their direction words swapped, and six
  matches are new — **one** genuine pointer, in this bullet's own opening paragraph, which
  resolves, and **five** quotations or literals carried by this bullet and by that ruling. The two
  convicted rows are quoted here and are **not** among the six: their directions are emphasised.
  ⚠️ **The axis is not new, only unmeasured.** `### Reach clauses` already carries one direction
  error as a retired quotation: *"the two readings **below** are corrected where they stand"*
  pointed below for a reading this document keeps above (`#1649`). It was caught by a reader
  following the pointer, which is still the only instrument there is.
  ⚠️ **`above` and `below` are not the direction words, only the two this seed knows, and the rest
  of the axis is measured here** (`#1811`). Second seed, the **nine-word** seed under the name its
  citations use, case-insensitive over this file's non-fenced prose at `d3a4ac5`, on `\b`
  boundaries — the hyphen is one — with no noun anchor because these words carry their own:
  `up`, `down`, `earlier`, `later`, `preceding`, `following`, `overleaf`, `previously`,
  `beforehand`. **41 matches**, none in a fence, split `up` 19, `down` 11, `later` 7, `following` 3
  and `earlier` 1 — and **31 are not pointers at this page**, each excluded on a stated ground:
  idiom (*"written down"*, *"looks it up"*, *"prop it up"*), the preposition (*"following
  Silverman's"*), a time rather than a place (*"a later PR"*, *"falsified by a later head"*), a
  **module docstring**'s own layout (*"a later sentence"*, *"nothing further up the docstring"*,
  *"down into the declaration headlines"*), the docstring **layer** rather than any location
  (*"one layer up"*, five of them), and quotations of rows already counted here. **Ten point at
  this page, eight of them correctly, and both misses are wrong by DISTANCE with the direction
  right** — which is the class named as invisible to the first seed, now measured rather than
  named:
  * `### Reach clauses`' *"the precedent `### Scope of the rules above` sets one section down"* —
    that section is three `###` sections down, and it was three at `7f0a162` (`#1678`, PR #685),
    the commit that wrote the clause. The parallel clause in the same section,
    *"`### Module-block bullets` sets two sections down"*, counts the same way from the same origin
    and is right.
  * `### Reach clauses`' *"the over-reaching count two paragraphs up"* (`#1799`, PR #714) — its
    target sits in the **same** blank-line-delimited paragraph, which is what *paragraph* means
    wherever this file measures one: *"the two live one paragraph apart here"* is true with exactly
    one such paragraph between the rows it counts. On the `⚠️`-block reading it is three up.

  **Both are repaired in this commit**, on the wrong-pointer ruling in `### Gate-discharge claims`,
  which that ruling now extends to a distance; and both were false at the commit that published
  them, which makes four of four on the rows these two seeds have convicted.
  ⚠️ **The limits, and they are wider than the first seed's.** The nine words are a list and not a
  class, and the five candidates tried against it are keyed the way this bullet's other figures
  are, at both ends: `ahead`, `supra`, `infra` and `hereafter` return **0 matches** each at
  `d3a4ac5` and **1 match** each here, which is this clause naming them, while `back` returns
  **1 match** at `d3a4ac5` — *"an `n`-th root of the pulled-back function"* in
  `### What is formalised` — and **3 matches** here. ⚠️ **The boundary belongs to the seed and not
  to this clause**, which is why it is now stated where the seed is: a tenth word added to the
  list inherits `\b` with the hyphen inside it, and owes its result under that. The one hit is a
  compound and not a direction word, so no eleventh pointer appears and the 41, 78, ten and eight
  this bullet publishes are untouched — the claim was short of the token, never false of the axis.
  `higher` and `lower` return **7 matches** at `d3a4ac5` and **9 matches** here, the two new ones
  being this clause's own two words. ⚠️ **The seven rows were read one by one, and the gloss they
  were read to confirm does not survive them** (`#1628`): *"every one is about a module
  docstring"* — PR #715 (`#1811`), at `0eb4f70` — is true of four of them and **false** of three,
  which is the over-reaching branch, so it retires rather than taking a qualification. **Two of
  the three** name *"the declaration's own docstring"* in those words — one in
  `### Module-block bullets` and one in this section, the ruling that a sentence there does not
  repair a headline — and the third, in `### Reach clauses`, answers a headline from inside its
  own docstring without using the phrase. That ruling is the boundary the gloss crossed, and it
  is itself a row of the population glossed. What holds of all seven is that **none of them is
  about this page**: three put a sentence in a docstring, one puts a `## Main statements` list
  there, one is a heading **level** inside one, and two are about letter **case** — so three of
  the seven name no place at all, which is the point the gloss was making and the reason the
  correction costs the clause nothing. ⚠️ **The bucket noun was measured against this page's own
  rule rather than left as a synonym**: this section rules that *"A list item is a unit too … what
  the reader meets is the bullet and not the sentence a splitter would cut out of it"*, so a
  *sentence* bucket pinned at four rows and true of three over-reaches, and over-reaching is
  **false** rather than short. It is repaired here rather than retired, and the ground is the one
  thing separating it from the gloss it sits inside: that gloss was **published** — PR #715
  (`#1811`), at `0eb4f70` — and this wording never left an unmerged branch, so there is no claim in
  the record for a marked quotation to preserve. And four of the nine themselves —
  `preceding`, `overleaf`, `previously`, `beforehand` — matched nothing at `d3a4ac5` and are
  carried for the next reader rather than for this count. Neither **target** nor **distance** is
  mechanical, so both convictions came from reading all 41 rather than from the regex. And a pointer
  carrying no direction word at all is invisible to both seeds: *"the first bullet of
  `### Reach clauses`"* is an address, and this axis can neither convict nor clear one. ⚠️ **The
  softest of the ten** is `## Scope`'s *"The following are developed here"*, a cataphora to the list
  under it rather than a cross-reference; it resolves either way, and a reader who excludes it gets
  nine, seven and the same two. ⚠️ **This bullet is inside its own population, exactly as the seed
  it extends is.** The second seed returns 78 at this head. The two convicted rows **leave** it —
  both repairs drop the direction word rather than turning it round, which is the preference in
  `### Gate-discharge claims` applied to itself — and 39 matches are new: the nine seed words
  written out, the exclusion grounds quoted, the split counts, and the wording of the two
  convictions. ⚠️ **The other two populations are unmoved, and that was checked rather than
  assumed**: no bolded numeral standing alone is added here, so the bolded-numeral seed
  `### Reach clauses` publishes returns 184 at `d3a4ac5` and 184 at this head — its own dated 175 is
  at PR #714's head, one merge earlier — and the first seed returns 40 at both ends.
* **A citation's provenance is a claim about this page too, and it is the third pointer axis**
  (`#1818`). A sha, and a citation that names a section by its heading, are both addresses carrying
  no direction word, so neither seed of the axis stated just before this one matches a single member
  of this population: the three axes are **disjoint by construction** rather than nested. That is
  why two members of this one survived a round-1 rejection, a round-2 delivery, a round-2 rejection,
  a round-3 rejection and a round-4 re-delivery of one seven-line clause in PR #716 (`#1812`). ⚠️
  **Measured at `5a2fe24`**, fence-aware over `README.md`, with two recognisers and this file's own
  heading table. ⚠️ **The heading-citation recogniser, and it must not be keyed on a line.** An
  inline code span whose content is two to six `#` characters, a space and a title: **138 spans**,
  none inside a fence. A reader who scans line by line gets 137, because one span wraps across a
  source line — `## The non-constancy hypothesis is not named in the headlines below` — and that
  pair of lines is one of the three odd-backtick pairs this file's own checks already carry. ⚠️
  **Split it against the heading table, never against the `#` count.** Resolving each cited title
  against this file's headings puts **110 of the 138** on a title this file also carries; two of
  those name a `.lean` module's own section of the same title, so **108 cite this page** — 104 at
  `###` and 4 at `##` — and **30 name a heading inside a `.lean` docstring**. Keying on the `#`
  count alone gives 105 / 33, and it discards the four `##` citations of this page: **two of the
  three defects convicted here are among those four**. ⚠️ **The test is on the span, never on
  proximity.** Resolve the named section's span from the heading table, find what the citing
  sentence attributes to it, and test that against the span. ⚠️ **A cited section's span nests**:
  it ends at the next heading whose `#` count is no greater, so a `##` section holds its `###`
  children rather than stopping at the first of them. This file writes that convention for a
  **reach register**'s unit in `### Module-block bullets` and nowhere for a section of this page,
  and it decides exactly one citation of the 110 — `## Scope`'s, whose quoted words sit in
  `### What is formalised`. On the flat reading, where a span stops at the next heading of any
  level, that one row is a wrong-section citation and this axis convicts four rather than three.
  Nothing else in the file turns on the choice: there is no `####` heading anywhere, so all 104
  `###` citations of this page have the same span either way, `## Layout` has no `###` child, and
  the single `## Docstring conventions` citation attributes no quotation a span test can read.
  Of the 110, **59 carry a marked quotation bound to the citation** and 51 attribute nothing a
  span test can check; those 51 were read one at a time rather than counted. The 59 give
  **62 pairs**, of which **34 land inside** the named span at this head. Of the 28 that do not,
  **20 are the binder over-reaching** — the quotation is of a `.lean` docstring or of some other
  subject, and the citing sentence attributes it to no section — **five quote a wording that is
  already gone** and every one of the five lands inside the named span at the commit its own row
  dates it to (`5018e25`, `2947444`, `7f0a162`, `d3a4ac5`, and the parent of `5c3fce2`), and
  **three are defects**. ⚠️ **The three, and not one of them names the wrong section.**
  * `## Layout`'s *"the counts drift, the structure does not"*, quoted twice in `### Reach clauses`
    (`3e1bef2`, `#1725`, PR #686 and `0a1049f`, `#1728`, PR #688) and verbatim at both of those
    commits. `2947444` (`#1802`, PR #711) re-measured `## Layout`, and the sentence there now reads
    *"the counts drift, the **directory** structure does not"*. Two marked quotations were falsified
    by an edit to what they quote, with nothing about either citing sentence touched.
  * `### Reach clauses`' *"was the old clause false or merely partial"*, in
    `### Module-block bullets`, was **never** verbatim. That section has read *"Read whether the old
    clause was false or merely partial before deciding."* since `ee0b8a4` (`#1659`, PR #666); the
    quotation reorders it, so it was false at `365dd39` (`#1668`, PR #683), the commit that wrote
    it, while the same words are quoted correctly as *"false or merely partial"* at three other
    sites in this file.

  **All three are repaired in this commit, one span each**, on the wrong-pointer ruling in
  `### Gate-discharge claims`: the sentence a reader is sent to is on the page whichever words the
  quotation gives for it, so this is a typo and not a claim, nothing retires and none of the three
  takes a marked quotation. The `### Module-block bullets` row is repaired to the shorter *"false or
  merely partial"* and not to the full sentence, because that is the form this file already uses at
  those three other sites. ⚠️ **The typo ruling reaches a drifted quotation more easily than it
  reaches a sha**, and `#1819` has since settled that difference in `### Gate-discharge claims`: a
  drifted quotation names a place that still holds the sentence one word from the quoted form,
  where a wrong sha names a commit at which the text is not there at all, so what carries the
  exemption there is that the `PR #<n>` beside an attribution names the same commit a second time.
  ⚠️ **What this axis convicts is fidelity, and no recogniser reads fidelity.** No citation of the
  108 names the wrong section at `5a2fe24`, the commit that population is measured at, and it clears
  nothing this page has gained since. A verbatim check catches a drifted quotation only once the
  section has been resolved mechanically, and PR #716's round-4 review is the converse failure — a
  quotation verified verbatim against text that sat in a different section, 59 lines past the
  boundary and in prose that reads like the section it was cited to — so the two halves of the test
  fail independently and neither substitutes for the other. ⚠️ **A quotation goes stale by an edit
  somewhere else**: neither `## Layout` citation was touched after it was written, and the commit
  that falsified both was re-measuring a third thing. ⚠️ **The sha half, where the population is
  clean and the syntax is not.** `[0-9a-f]{7,40}` inside an inline code span, non-fenced: **69
  spans**, **40 distinct**, and `git cat-file -t` resolves all 40 to commits of this repository, so
  no sha in this file dangles. **25 sit within 70 characters** of a `PR #<n>`, and **24 of those**
  are that PR's merge on `main`. The one that is not is `ee0b8a4`, and it is **cleared by reading
  and not by the test**: that sentence says the wording *"was live at"* the commit rather than that
  it landed there, and `EllipticCurves.Torsion.PrimaryTowerOdd` carries the wording as live prose at
  `ee0b8a4` and as a marked retired quotation at `b764fae`, which is PR #667's merge. ⚠️ **A sha
  does three jobs here under one syntax, and this file distinguishes none of them:**
  * **Attribution** — *where a clause landed*. The sha must be that PR's merge, and all 24 agreeing
    rows are of this kind.
  * **Measurement** — *the base a figure was taken at*. Any commit, and the row owes a statement of
    what was measured; the axis stated just before this one uses `d3a4ac5` that way six times.
  * **State-at** — *the commit at which a wording that is now gone was still live*, which is by
    construction **not** the commit that changed it. `ee0b8a4` is the only instance in this file,
    and it is the whole reason a PR-to-merge check cannot be the instrument.

  PR #716 was convicted twice for writing an attribution inside a sentence that had already fixed a
  measurement sha, which is the pair of senses a reader conflates most easily. ⚠️ **The 30 citations
  of a `.lean` docstring heading are in scope, and their test is a different instrument.** **14 of
  the 30 name a heading of a named module** — 17 checks, since one citation covers three files and
  another covers two — and every check resolves: that file's docstring carries that heading. The
  other **16 name a heading shape** over no particular file and assert nothing an address test can
  check. ⚠️ **Three of the 14 name their heading by a prefix of it**, five of the 17 checks:
  `EllipticCurves.FunctionField.MulByNGalois`, `…MulByNGaloisGroup` and `…MulByNPlaceComposition`
  each open a section whose heading runs on past the cited words, and `…PlaceDegreeComparison`'s and
  `…MulByNFibre`'s do the same. A reader greps and finds all five, so all five take the typo reading
  and none is repaired — but no rule on this page says a cited heading may be abbreviated, and that
  is what this axis leaves open. ⚠️ **This bullet is inside its own population and beside the other
  three.** ⚠️ **The census is dated to `5a2fe24`, and `4769f3e` is this commit's parent**, a merge
  that added a paragraph to `### Gate-discharge claims` and moved both recognisers without reaching
  a conviction: 140 heading spans on 112 titles this file also carries, and 73 sha spans on 41
  distinct. Re-run at this head, the heading-citation recogniser returns **156 spans**, **125
  citing this page** and **31 naming a `.lean` heading**, and the sha recogniser returns **93
  spans**, **45 distinct**, with none dangling and with the merge check still flagging exactly one
  sha, `ee0b8a4`, now on three rows — the row this census cleared, the quotation of it that parent
  added, and this bullet's. The span test **loses the three repaired rows and gains five**, and all
  five are this bullet's own quotations of the two convicted wordings, paired with the citation
  beside each. ⚠️ **The three seeds the axis just before this one
  publishes are unmoved, and that was checked rather than assumed**: the bolded-numeral seed returns
  184 at `5a2fe24` and 184 here, the noun-and-direction seed 40 matches on 39 lines at both ends,
  and the nine-word seed 78 at both ends, with that seed's five negative results — 3, and 1 each for
  the other four — and the 9 beside them unchanged. No numeral in this bullet stands alone inside a
  bold span, none of the nine words is written here, and no noun of the first seed's list is put in
  front of a direction word.

  ⚠️ **THE AXIS IS RE-RUN HERE, BOTH HALVES HAVE GROWN BY MORE THAN HALF, AND THE ONE CONVICTION IS
  ONE NO SPAN TEST COULD HAVE MADE** (`#1935`). Measured at **`49b327d`**, this commit's base, with
  the two recognisers this bullet publishes: **226 heading-citation spans** (**225 line-keyed**, the
  wrap costing exactly one still), **192 on a title this file also carries**, and the binding window
  splits those into **97 bound to a marked quotation** and **95 attributing nothing a span test can
  check**, giving **102 pairs**. ⚠️ **The calibration is what licenses those, and it is twelve
  figures at three commits, eleven of which this bullet already publishes**: the same recogniser
  returns 138 spans, 137 line-keyed and 110 title-matching at `5a2fe24` and the same window returns
  59 / 51 / 62 there; 140 spans on 112 titles at `4769f3e`; and 156 spans, 155 line-keyed, at
  `b2d1981`, splitting 125 / 31 on this bullet's own sort. ⚠️ **The twelfth is that 155, and at
  this head this paragraph is the only place on the page it occurs**: it is derived and not
  published, and a calibration is checked by looking each figure up in the text it is claimed from
  — so a reader who takes all twelve to this bullet finds eleven and fails on the last.
  ⚠️ **`b2d1981` is where the *"Re-run at this head"* figures belong, and the sentence that
  publishes them does not date them**: `4769f3e` is named there as the parent, so a reader takes
  the pair as one measurement. ⚠️ **The sha is on this page, three times at `49b327d`, and never
  beside the figures.** The decisive site is the next bullet of this list, `49b327d:2895`, whose
  own arithmetic binds figure to sha by name: its clearance names 108 citations of this page
  measured at `5a2fe24`, then *"the census in the same bullet returns 125 at `b2d1981`"*, and 125
  is one of the figures in question. `49b327d:1131` names the same sha as one end of this bullet's
  own re-run; `49b327d:2565` dates a different census. ⚠️ **So the defect is placement and not
  absence**, and that is the harder shape to catch: `49b327d:2859` publishes the figures and
  `49b327d:2895` dates them, 36 lines below, in a sentence arguing something else — so the one
  sentence a reader checking the figures reads is the one that withholds the date. `git log -S` on
  the publishing sentence returns `b2d1981` too, and the commit that follows it on `main` returns
  160 spans rather than 156.
  The span test — the quoted words, whitespace-normalised over the whole file, with the quotation's
  own printing dropped **by offset and never by line** — puts **49 pairs inside** the named span,
  leaves **39 whose words are not on this page at all**, and returns **14 candidates**. ⚠️ **Every
  one of the fourteen was read, thirteen are the binder over-reaching** this bullet already names,
  and the fourteenth is the paragraph `### Reach clauses` repairs in this commit. ⚠️ **The filter
  did not catch it on the section, and after the repair it still returns it**: the section that
  paragraph names is the right one and holds the words, and what the filter matched on is a leading
  article and a bold marker. What was false there is the **verb** — that section says *used to* of
  the wording the paragraph had it giving — so a citation can name the right section, quote it
  verbatim, and still be false. **That is the second way provenance goes stale and no recogniser on
  this page reads it.** ⚠️ **What this paragraph does to the figures it publishes was checked and
  not assumed.** It names a section once and binds no quotation to that name, so at this commit's
  head the span count is 227 on 193 titles and the unbound half is 96, while **the bound half, the
  pairs and all three verdict counts are unmoved** — 97, 102, and 49 / 14 / 39. The repair this
  commit makes moves none of the nine: it retires no heading citation, and the quotation it adds has
  no citation inside the window. No numeral written here stands alone inside a bold span.
* **A clearance is not a count, and the discriminator in `### Reach clauses` does not reach it**
  (`#1824`). That discriminator sorts a dated census, which a new head does not falsify, from a
  present-tense claim about a named declaration, which it does. A **clearance** — the claim that no
  member of a named population is defective — sits with the census on that test and with neither on
  what going stale costs. A stale count **under-reports**: it says the population is smaller than it
  is, and the reader who cares re-runs the recogniser. A stale clearance **hollows**: the population
  grew, the verdict did not, and the rows nobody read look exactly like the rows somebody did. The
  first is visible to the next person who counts and the second is visible to no one. ⚠️ **So a
  clearance is keyed to one commit at both ends and never to the head**: it names the size of the
  population it cleared and the commit that population was measured at, and it is silent about every
  commit past that one. A head-relative phrase is what a count may use and a clearance may not,
  because a reader who dates one by `git blame` repairs a count by re-running a recogniser and a
  clearance only by reading rows. ⚠️ **A count phrased against the head is dated by the commit that
  wrote it, and this file already leaves such a count standing**: `### Gate-discharge claims` gives
  its sha census at the head that published it, the commit after that moved both figures and did not
  re-key them, and that account rules for itself that a census of the axis is dated rather than
  standing. This commit does the same to the figures in the bullet it repairs, deliberately rather
  than by oversight, and that licence is exactly what a clearance must not have. ⚠️ **The other
  branch — a clearance that binds at head — is refused because nothing could check it.** It puts a
  standing obligation on every author who adds a citation to re-run a fidelity test over a
  population they did not measure, and the citation-provenance bullet in this list is the
  demonstration that no recogniser reads fidelity. ⚠️ **That bullet is the standing instance**,
  which is why the rule is written beside it: its clearance names 108 citations of this page
  measured at `5a2fe24`, the census in the same bullet returns 125 at `b2d1981`, and the
  **17 in the difference** are covered by no clearance here, as is every citation this page has
  gained since. Dating the verdict convicts nothing — the clause was **partial in its scope and
  never false of its population**, which is the test `### Retired claims` requires first.
* **A figure this page states about itself is decided by the tree it lands in, and a figure that
  names no commit names none** (`#1972`). The clearance rule this list carries for `#1824` sorts a
  dated census — which a new head does not falsify — from a present-tense claim about a named
  declaration, which it does. ⚠️ **A self-figure keyed to *"this head"* is neither of those, and it
  is the shape this page has most of.** Its subject is the tree, so a new head decides it; and its
  key is an indexical address (`#1877`), so what it is a claim about is recoverable only through
  `git blame`. What lands is not the branch tip the figure was resolved against but the **merge**
  of that tip with whatever `main` has become, and a commit that touches no line near the figure
  moves it.

  ⚠️ **The ruling is that every self-figure takes this and not only the seeds**, because the
  instance that forced it was a census sentence and not a seed. A wording confined to the seeds was
  drafted first and would have cleared the two branches that failed on it in one session. Each
  published a nine-figure provenance census as an absolute at its own tip, and each had the same
  four of the nine falsified by one heading citation that landed first.

  ⚠️ **The key is convicted and not merely dispreferred, and one row does the convicting.** The
  noun-and-direction seed is restated in this section at *"at head"* with the value **40**.
  `git log -S` on that source line — the resolver this page names — returns `3c183d8`, and per-line
  `git blame` returns it too, and at `3c183d8` that seed returns 42: that commit reflowed the line
  and wrote none of the sentence. A walk that flattens each blob with `re.sub(r'\s+', ' ', blob)`
  and searches all 79 commits that had touched this file at `77fb54d` returns `10519af`, where the
  seed returns 40. **So a reader who resolves the indexical the way this page says to resolve one
  arrives at a commit where the printed figure is wrong.** ⚠️ **That does not falsify this page's
  own walk of the *"this commit"* seed**, which found blame naming the writing commit 388 times out
  of 388: this occurrence carries none of those words and is outside that population. What it shows
  is that the agreement there does not extend to a figure's key. And the reading on which
  *"at head"* simply denotes whatever commit wrote it is the one `#1824` refuses, since a date is a
  commit **named** and not a commit gestured at.

  ⚠️ **The repair is a delta, and the reason is a property and not a preference.** A delta is a
  fact about the block a commit inserts; an absolute is a fact about a ref. Splice this bullet's
  own block at its own index into each of the three bases named at the end of this item and all
  three trees return the same deltas — and they would still be the same against any base into which
  the block merges cleanly, because not one of them is computed from a base at all.

  ⚠️ **A sha is the other repair and it is cheaper**, since it re-measures nothing: a figure that
  was right when it was written stays right forever once the commit it was measured at is written
  beside it.

  ⚠️ **The gate, written out because it is cheap and nothing on this board runs it.** Difference a
  branch's `README.md` against its own base; if that is one contiguous insertion, splice the
  inserted block into `main`'s `README.md` at the same index, run the census on the branch tip and
  on the spliced tree, and report every figure that differs. Then, for each such figure, search the
  **block** for its value as a standalone numeral: a branch is exposed exactly where it prints one.

  ⚠️ **The second half of that is a coincidence detector, every hit has to be read, and a run says
  nothing at all unless its base and its heads are one moment.** Run at `be1a4d5` over the six
  branches under review when it landed — PRs #741, #746, #749, #750, #751 and #752 — it reaches
  three of them: two change no `README.md` line and one is not a single contiguous insertion. **It
  flags all three that it reaches, and two of the flags are true.** PR #746 and PR #749, at the
  heads they stood at then — `bab331934268736c261877b291e8bcff52096a47` and
  `f7b25145082e5b7e2faaaa778a2927af75fa1d36`, both force-pushed over since — each printed a
  provenance census as an absolute at its own tip, and the same four figures of it — spans,
  line-keyed, title-matching and unbound — are each one short at the merged tree. The third flag is
  false: PR #751's block prints `25`, which is that branch's own distance-seed value and is 26 at
  the merged tree, and reading the row shows the `25` is that bullet's absence-seed widening figure
  and not the distance seed at all. ⚠️ **Re-run at `77fb54d` over PRs #741, #746, #749, #751,
  #752, #753, #754 and #755, PR #751's is the only flag left**, because a subsequent round of each
  of the other two converted its census to deltas or keyed it to a sha — which is the repair this
  item asks for, arriving twice before the rule was written.
  ⚠️ **That population is enumerated and not counted at a date**: a calendar day names no commit,
  and the set of branches under review is not constant over one, so a count keyed to a date is true
  at an instant the clause does not give.
  ⚠️ **The parenthesis's CLAUSE about how those two heads resolve is retired here rather than
  deleted — and its two seven-character names are NOT retired but RE-KEYED to their full object
  names**, which is the opposite operation and is why the sentence above now carries the forty. The
  clause read *"force-pushed since, so both resolve only through `refs/pull/<n>/head`"*, written by
  `046022dc` (PR #755, `2026-09-15T03:38:43Z`), whose row key *#1972* resolves to no row — so the
  record names a commit and a pull request and no seat. ⚠️ **That reading is the parenthesis's
  trailing clause and not the whole of it**: the parenthesis opened by naming the two heads, so a
  frame calling the whole of it retired would identify the unit by the half it drops.
  ⚠️ **`### Reach clauses`' *"false or merely partial"* test returns FALSE of the clause, and in
  BOTH directions**: no condition completes it into something true, because the full object name
  reaches both heads and the route the clause names reaches neither. Into a `mktemp -d` plus
  `git init -q` holding **no** objects, under `git` 2.39.5,
  `git fetch --depth=1 <url> bab331934268736c261877b291e8bcff52096a47` exits **0** and
  `git cat-file -t FETCH_HEAD` then answers `commit`, identically for
  `f7b25145082e5b7e2faaaa778a2927af75fa1d36`; the same fetch at seven characters exits **128** with
  `fatal: couldn't find remote ref bab3319`, and neither head is at the tip of **any** of the refs
  `git ls-remote` advertises.
  ⚠️⚠️ **What replaces the clause is the distinction and not the bare correction: a
  `refs/pull/<n>/head` outlives a DELETED branch but TRACKS a force-pushed one.** PR #897's branch
  `docs/oddtorsioncountsplits-address-rekey-2310` is advertised nowhere, and `refs/pull/897/head`
  still reads that pull request's own head; `refs/pull/746/head` and `refs/pull/749/head` moved with
  the force-pushes and point at neither of the two heads above. ⚠️ **So for a superseded head the
  full object name is the durable key and the pull-request ref is not** — the clause had both ends
  backwards, which is why it is retired and not narrowed.
  ⚠️ **The two forty-character names are in backticks, and this retirement cites no seven-character
  form at all**: the one seven inside it sits in the verbatim `git` error message above, reproduced
  rather than cited, so the italics rule has nothing here to reach. **The ground for the backticks
  is that the forty RESOLVE** — this section asks for italics because *"a retired name in backticks
  is indistinguishable from a dangling one"*, and the forty resolves into a repository holding
  nothing, so italicising it would assert the one thing the measurement above refutes.
  ⚠️ **And that rule is read NARROWLY here: it governs retired DECLARATION names, and a commit
  object name is not one** — it is the rationale clause and not the rule that reaches a sha, and the
  backticks stand under either reading. ⚠️ **The two DISTINCT eight-character keys in this
  retirement, `046022dc` and `43c84ed0`, are LIVE citations and are backticked for that reason**:
  they resolve in this repository, nothing here retires them, and they are not names of the two
  heads at all.
  ⚠️ **Both pull requests are still open, so their two ref values can move again and are
  deliberately not written here**; the two forty-character names are frozen by being unreachable,
  which is what makes them the key.
  ⚠️ **`### The render gate`'s clause about tree-wide fetchability is a different proposition and
  retires at its own block** (`#2320`): this quotation is about this sentence's two heads and the
  route it names for them, which is why *"A claim about the block it sits in retires where it sits"*
  puts it here and asks for no second copy of that one. ⚠️⚠️ **And that block's own text asks for
  exactly this quotation**: its *"One copy of the same claim SURVIVES this repair"* sentence names
  this copy by base blob `43c84ed0:README.md` and says `### Retired claims` asks for its own
  quotation and not a second copy of that one — so this is that quotation. ⚠️ **It is KEYED to
  `43c84ed0` and to its own round, so once this lands it is correct-and-stale at its own ref and not
  false**, and it is not edited here.

  ⚠️ **The landed population is measured, and the sweep is filed rather than folded in here**
  (`#1975`, PR #614). Counting every restatement of the four seeds this section publishes and of the
  sha census `### Gate-discharge claims` publishes that is keyed by an indexical and not by a sha:
  **13** at `77fb54d`. ⚠️ **Every one of the thirteen was true at the commit the walk returns for
  it** — not one is a measurement error — and **12** state a value the seed no longer returns. At
  `77fb54d` the noun-and-direction seed returns 49 where three of them state 40 and one states 42,
  the nine-word seed returns 88 where three state 78, the bolded-numeral seed returns 279 where two
  state 184 and one states 191, the distance seed returns 26 where one states 23, and the sha census
  returns 207 citations and 74 distinct where one states 73 and 41 — 4 + 3 + 3 + 1 + 1, which is the
  12. The thirteenth is true, and it is checkable only because `### Gate-discharge claims` dates it
  in a sentence 1,193 lines away at `77fb54d`, arguing something else — the
  *"the defect is placement and not absence"* shape, bold in the original, that this section already
  names, met for a second time.

  ⚠️ **The clearance this ruling reaches first is the one asserting it has nothing to reach.** The
  last item of this section clears its own seed with
  *"keyed to a sha or to the commit that wrote it, so none of them is falsified"*, and **three** of
  that seed's readings on this page at `77fb54d` take the second disjunct and no other. The disjunct
  licenses precisely the key convicted here, so the clause is true only on the reading `#1824`
  refuses. It is `#1975`'s to repair with the rows, and it is named here because a universal over a
  population that has now been read is a different thing from one over a population that has not.

  ⚠️ **This item is inside its own population, so it is written as this commit's own delta, and
  every other figure it states about this page is keyed to `77fb54d`.** Spliced at its own index
  into `d559108`, into `be1a4d5` and into `77fb54d`, the three trees return the same deltas: it adds
  **3** heading-citation spans, all three line-keyed and all three on a title this file also
  carries, **1** to the bound half and **2** to the unbound, for one new pair, which the span test
  scores `OUT`: this item quotes *"the defect is placement and not absence"*, bold in the original,
  whose words are in this section, and the binder reaches past it to the heading citation in the
  same sentence — which is the over-reach the citation-provenance item in this list already prices,
  arriving in prose about it. **No pre-existing row of any verdict moves**, checked as a row-set
  identity and not inferred from the totals. The noun-and-direction, nine-word and distance seeds
  gain nothing. The bolded-numeral seed gains **10**, and that figure counts itself: four stand in
  the paragraphs above and six stand in this one. It carries **17** sha citations naming seven
  distinct shas, **6** of which this page does not carry at `77fb54d`, so the sha census that
  `### Gate-discharge claims` publishes gains seventeen there. ⚠️ **The two halves are not the same
  kind of figure, and only one of them is merge-invariant.** Seventeen counts spans this block adds,
  so every tree it merges into gains seventeen. Six counts shas the base does not already carry, so
  it moves with the base: three of the six are consecutive commits of `main`, and against a tree
  that has already taken those the distinct gain is three and not six. ⚠️ **This item's own thesis
  reaches this item's own delta** — which is why this paragraph publishes a tuple and not a number.
* **A cited heading may be shortened to a prefix of it and to nothing else** (`#1824`). The five
  prefix citations the citation-provenance bullet names are correct as written, and no rule on this
  page said so when they were written. ⚠️ **The ground is that a reader searches for the cited words
  and lands on the heading**, and it holds under three conditions rather than in general: the cited
  words are a contiguous run at the **start** of the heading, so they are in the file verbatim and
  in the order given; the citing sentence **names the file**, without which a title this page also
  carries — and one of the five is such a title — resolves here instead; and no second heading of
  the named file opens the same way. All five meet all three, re-checked against the `.lean` files
  at this head, and none is repaired. ⚠️ **Nothing else about a citation is licensed by this.** A
  title with words dropped from its middle, or with its words put in another order, is neither a
  prefix nor what a reader would search for. And the rule is about an **address**: it reaches no
  marked quotation, which claims the words themselves, so the reordered quotation convicted in that
  same bullet stays convicted. ⚠️ **It is also why a short citation is not a short reach clause**,
  though `### Reach clauses` sorts short as partial and would otherwise take both: a reach clause
  that names some of a declaration's conditions leaves a reader no way to learn the rest exist,
  where a prefix leaves the rest of the heading one search away in a file the sentence has already
  named.
* **A cross-reference's *distance* is the fourth pointer claim, and the unit for a `line` was
  never written** (`#1810`). The two direction seeds this section publishes key on a direction word
  and the citation-provenance axis in this same list keys on an address; this one keys on the count
  in front of a direction. ⚠️ **The four populations are neither nested nor disjoint, and that was
  measured**: at this commit's parent the distance seed's nineteen matches fall on eighteen lines,
  of which none is matched by the noun-and-direction seed and eleven by the nine-word seed — and
  **not one of the four rows convicted here is matched by either**, so no direction seed could have
  reached them. ⚠️ **Two of the three questions this axis raises are answered already, and neither
  is restated here.** `### Gate-discharge claims` disposes of a wrong count — *"A wrong distance
  takes the same exemption as a wrong direction"* — and the second direction seed fixes the unit for
  a **paragraph** as the blank-line-delimited block (`#1811`), on this file's own calibration
  `### Reach clauses`' *"the two live one paragraph apart here"*. ⚠️ **What no sentence decides is
  the unit for a `line`, and it is a separate question with its own answer.** *"N lines above X"*
  can name the line N nearer the top of the file than X, or the Nth of N lines counted from X
  inclusive, and those differ by one at every row. **It is the subtraction, and four of the six line
  distances this file stated at this commit's parent agreed on it**: the two one-line pointers it
  carries, one in `### Reach clauses` and one here, each name the line immediately before themselves
  and that line is in both cases the target; and the two dated figures this section's direction axis
  publishes are exact subtractions, the census `#1754` took opening 46 lines past the clause that
  names it at `5018e25` and the fixed-numeral discriminator sitting 1539 lines before the clause
  that cited it at `2947444`. ⚠️ **The other two were the two rows this axis convicts, and they did
  not fall the same way.** The fifth site read like a calibration and was not one — it is the fourth
  defect convicted here, the only one whose target sits in a `.lean` file rather than on this page,
  and its count was right under neither reading, so it settled nothing either way. ⚠️ **The sixth is
  the first row convicted here, and it was this file's only evidence for the reading this ruling
  discards** — counted the second way its numeral was right, since the third of three lines taken
  from the pair it counts from, inclusive, is the pattern it names. ⚠️ **The population is dated
  because this commit empties both dissents out of it**: the fifth has its count dropped and the
  sixth has its numeral corrected, so at this head five line distances are stated and all five
  agree, and the two that disagreed survive only as this bullet's dated quotations of them. The
  ruling is therefore made at the parent, where both dissents were still in the file to be weighed.
  **So this is a ruling and not a reading-off, and it is made four against one**: the four are
  preferred because under the second reading a pointer that counts from its own line names that line
  rather than the one it means, which is a form neither of the two one-line rows can be written in.
  A **section** distance needs no ruling here: the two rows that state one count `###` headings, and
  no `##` heading falls between either pair, so the two readings agree. ⚠️ **The distance seed,
  under the name its citations use, published so it can be re-run** (`#1749`): case-insensitive and
  fence-aware, matching a numeral, a unit and a direction in that order, or a unit, the word
  `immediately` and a direction. The numeral is
  `immediately`, `a`, a word for one of the numbers 1 to 10, or a digit string; the unit is
  `paragraph`, `section`, `line`, `bullet`, `row`, `clause` or `entry`, with an optional plural; the
  direction is any of the eleven the two direction seeds key on, the first's two and the second's
  nine. ⚠️ **And it is keyed on a source line**, which is a property of the seed and not of the
  distances it looks for; the limits state it and measure what it costs. ⚠️ **Six of those eleven
  never occur in that position** at either end, so the count does not turn on which of the two sets
  is taken as the source. It returns **14 matches** at `d3a4ac5` and 19 at this commit's parent, and
  every one of the 19 was read rather than sampled.
  **Seven quote a row counted elsewhere**, six of them carried by that ruling and by the direction
  axis's own bullet. **Four state a `.lean` docstring's own layout rather than a place on this
  page**, and the two of those four that make a checkable claim about a named file split one each:
  `MulByNFibre`'s register bullet and the one *"five rows below"* it are the first and the sixth of
  a single sub-list, which holds; the `MulByNResidueDegree` row is the fourth defect convicted here.
  **Eight point at this page, five of them correctly and three not** — a miss rate the direction
  axis's 2 of 29 does not predict, which is what this axis was filed on — and all three of those
  were already wrong at the commit that published them, as was the fourth conviction, whose count is
  right at no commit. That makes eight of eight on every row this page's direction and distance
  seeds have convicted — the denominator is what the seeds convicted and not what points at this
  page, and the fourth is outside that class and inside this one.
  * `### Reach clauses`' *"the pattern three lines above them"* (`acbf51a`, `#1749`, PR #692) — the
    pattern it contrasts and the two singular quotations it contrasts them with are two lines apart,
    here and at `:269` and `:271` at that commit.
  * `### Reach clauses`' *"falsified four paragraphs below"* (`4efeb97`, `#1774`, PR #706) — six
    blank-line-delimited paragraphs separate that clause from the ⚠️ whose words it quotes, here and
    at that commit, and no construction returns four without dropping a bullet list from the count
    and merging two unmarked paragraphs into one.
  * `### Reach clauses`' *"the paragraph immediately above"* (`712c35e`, `#1608`, PR #639) — the
    paragraph immediately before that clause is the `f ≠ 0` exemption, which says nothing about the
    occurrence test; the one that rules the test out by name is two, here and at that commit. The
    direction axis names the same target as *"a paragraph two above it"*, as a limit of its own
    seed rather than as a defect, and its quotation of the wording this row removes is dated in
    this commit rather than left standing as a claim about what that section reads now.
  * this section's *"four lines above"* (`06b014d`, `#1660`, PR #663) — the only one of the four
    whose target is in a `.lean` docstring, and the only one whose own quotation fixes which commit
    it is a claim about: the headline it quotes still carried those words at that commit's parent,
    and there the ⚠️ it names opens two lines past it. `#1660` repaired that headline — the repair
    this sentence exists to record — and the gap became three, which is what it still is.
    ⚠️ **Four is the gap at no commit**, and the choice of anchor does not rescue it. Measuring to
    the line carrying the quoted words rather than to the ⚠️ that carries them reaches four only at
    a commit where the quoted headline is not in the file at all, and it is not the reading this
    file calibrates: the dated 46 is counted to the line its target *opens* on.

  **All four are repaired in this commit** on the exemption named above: two take the corrected
  count, the third is rewritten around it so that the clause reads as one sentence again, and the
  fourth has its count **dropped rather than corrected**, because it is the demonstration that a
  distance into a file this page does not own is moved by the very edit the sentence describes — and
  its target is already named by the words it quotes, in a file it names. Nothing retires and none
  of the four takes a marked quotation. ⚠️ **The false-or-partial test is not what decides that, and
  running it is the argument for why it cannot be.** *"three lines"* and *"four lines"* both
  over-reach their gaps, where *"four paragraphs"* and *"immediately"* both under-report theirs — so
  `### Reach clauses`' *"over-reaching is false"* would retire two of these four and complete the
  other two, splitting one class on a distinction no reader who follows a pointer can use. The
  exemption reaches all four alike. That is the conflict `#1810` was filed to have resolved, and the
  four rows are the evidence for resolving it the way `#1811` did.
  ⚠️ **The limits, measured rather than named** (`#1749`). The seed is bare-token keyed and inline
  emphasis defeats it, exactly as emphasis defeats the first seed: relaxing it to allow a bold,
  italic or code marker around each of the three tokens takes 19 to **24 matches** at the parent,
  and all five it recovers are live rows — two in `### Module-block bullets`, two in this section's
  direction axis, where both dated line figures are written with the numeral bolded and the
  direction italicised, and that axis's own quotation of the third of the four rows convicted here.
  **So 19 is a floor and 24 is a floor as well**: a distance that names no numeral, or that puts the
  target between the count and the direction, is invisible to both. The seed reads distance only,
  so a pointer wrong by *target* is as unmeasured after this axis as it was after the two direction
  seeds; and it matches quotations, which is why the split above separates them out rather than
  counting them as pointers.
  ⚠️ **The third limit is the line key itself, and this page has already ruled against one.** The
  citation-provenance axis in this same list publishes its heading recogniser with the ruling that
  it must not be keyed on a line, and this seed is keyed on one all the same: a distance phrase
  that wraps across a source line is invisible to it. Dropping the line key and changing nothing
  else takes the three counts to 16 at `d3a4ac5`, 21 at the parent and 25 at this head, and the
  rows it recovers are the same two at every one of the three. One is in `### What is formalised`,
  wrapping between its numeral and its unit, and its target is the set of bullets in that section
  whose stated index range had been superseded; the other is in `### Reach clauses`, wrapping in
  the same place, and its target is the clause on the far side of the semicolon that closes the one
  it counts from.
  ⚠️ **Both are correct**, so the line key costs this axis no conviction — what it costs is a
  direction word: one of the second seed's nine reaches this position on no other row, so the line
  key hides its only occurrence, which is why six of the eleven never occur in this position and not
  five.
  ⚠️ **This bullet is inside its own population, so its own figure moves by being stated.** Re-run
  at this head the seed returns 23 and the relaxed variant 28, and the five each gains are this
  bullet's own quotations of rows already counted in it — the four wordings it convicts and the
  `.lean` layout row it clears. ⚠️ **Three of the four repairs keep their row inside the seed** and
  the fourth takes it out, which is what dropping a count does: nineteen at the parent, less that
  one row, plus these five quotations is the 23. A re-run sees the same eight pointers at this page
  that this one did, since the row that leaves is one of the four naming a `.lean` layout. ⚠️ **The
  other seeds this section publishes were checked rather than assumed**: the bolded-numeral seed
  returns 191 at the parent and 191 here, with its added and removed multisets both empty; the
  noun-and-direction seed 42 matches on 41 lines at both ends; and the nine-word seed 78 at both
  ends, with its split byte-identical and its five negative results unchanged. No numeral in this
  bullet stands alone inside a bold span, no noun of the first seed's list is put in front of a
  direction word, and none of the nine words is written here. ⚠️ **The citation-provenance axis's
  figures do move, and they are not re-keyed here**: they are counts phrased against their own head,
  which the clearance ruling in this list dates to the commit that wrote them rather than to this
  one. ⚠️ **What is recorded instead is what this commit adds to that population**, measured against
  this commit's parent with that axis's own recogniser: ten heading-citation spans, all ten citing
  this page and none naming a heading inside a `.lean` docstring, and ten sha spans on eight shas,
  three of them new to the file, all three resolving and none of the three flagged by the merge
  check, which still flags `ee0b8a4` and nothing else. ⚠️ **Nothing here is keyed to an absolute
  count, to a line address or to the parent's sha**, and that is one defence and not three: a rebase
  moves all three and leaves the sentence that quotes them behind, where a difference between two
  heads, a gap between two lines, and *this commit's parent* name the same thing at every base this
  commit can land on. ⚠️ **No sha this commit adds is a state-at instance**, so that sense keeps the
  single occupant the sha bullet records: the ones written beside a `PR #<n>` are that PR's merge
  and agree with the check, the rest date a measurement and say what was measured beside them, and
  the one that does neither is the sha the check itself flags, written here as its result.

  ⚠️ **The fifth pointer claim names no distance at all, and it is the one this list has never
  written down**: a bare **demonstrative** — a *the*- or *that*-phrase standing for a unit named
  earlier — sends a reader to that unit without counting to it, so every seed named here is blind to
  it by construction, and no register here reads one for whether it resolves. `### Reach clauses`
  does read anaphors, but its subject is whether an antecedent supplies a hypothesis list rather
  than whether a back-reference resolves to the unit it means, so `#1694`'s test puts this ruling
  here and doubles no register. ⚠️ **A demonstrative resolves by being determinate and not by being
  near, and two of them in `### Reach clauses` rank those two properties against each other
  at `77fb54d`**, where *"The 8 decide it"* stands four lines below the `57 / 8 / 23` it means
  and two lines below a later split of the same 88 rows in which no bucket is 8, and *"The 57 are a
  population to read"* stands at the far end of the same chain with no other 57 anywhere between it
  and that figure. **The nearer of the two is the one whose nearest figure is the wrong one**, so
  proximity ranks them backwards and a rule keyed on the gap would repair the row that does not need
  it. Both rows are live, and a repair that anchors either is what this ruling asks for rather than
  a falsification of it: the measurement is dated to `77fb54d` and not to this page's head.
  ⚠️ **The record is six convictions in one day and it is a floor rather than a census**: its
  population is this board's review threads, and no seed on this page can open one. PR #747
  round 2, PR #750 rounds 1 and 2, PR #752 rounds 1 and 2 and this bullet's own round 1 were each
  rejected in part for this shape, at 11:53Z, 16:32Z, 17:54Z, 18:57Z, 21:01Z and 22:46Z on
  2026-09-13, and the shape is older than the day: PR #689 was rejected for it on 2026-09-05, on a
  *that*-phrase whose nearest antecedent was the wrong file. The earliest of the six states the
  rule in terms — in a review comment, which is the one place a later round does not read.
  **A convention that lives in a review is paid once per round and never once for good**, and that
  is `#1915`'s ruling on sources turned on this page's own conventions rather than on a delivery's
  figures. ⚠️ **One of the six was recorded by the session that drafted this paragraph, 44 minutes
  before round 1 of this bullet was committed, and one is the review of that round** — so the
  count is a floor for a stronger reason than a record growing after the fact: a row can sit in
  the drafting session's own thread and still be outside it, and no instrument on this page could
  check that.
  ⚠️ **The repair is not to move the interposed text back, and that has been convicted rather than
  argued.** PR #750 round 2 took the move, which returned the gap to its base value and left the
  displaced paragraph needing a new opener; the opener it got at that round gave *the ten headlines*
  the direction **above**, where at `77fb54d` `PullbackPrincipalityTwoRationalTorsion:42` gives
  the same ten *below* and that file carries no declaration headline until `:184`. **A move
  converts an anaphora into a pointer, and a pointer is a claim this same list convicts on two axes
  already.** It also cannot be run twice: the displaced text has to sit somewhere, and in a chain
  written as this one is, every somewhere is directly above the next demonstrative.
  ⚠️ **So the repair is to make the referent determinate rather than close**: name it in apposition,
  or anchor it to the ref its figure is dated to. Both cost one clause, neither creates a pointer,
  and both survive an insertion of any length — which is the property a gap does not have and the
  reason this is ruled here rather than handed to the seed. ⚠️ **The population is unmeasured and
  this is a ruling and not a reading** (`#1628`): a demonstrative carries no direction word and no
  distance numeral: where it carries a figure at all, as this ruling's own two witnesses do, the
  figure counts its referent and not lines, and the bolded-numeral seed wants one standing alone
  inside a bold span where theirs wrap a sentence. So not one of the four seeds this section
  publishes could return it, and nothing written here says how many of them this page holds.
  ⚠️ **The two gaps this paragraph states are themselves inside the distance seed's population**
  and they are the only rows this commit adds to that population.

* **A line number is the fifth pointer claim, and the only one that goes false with no edit to
  either end** (`#2037`). A declaration name, a heading, a marked quotation and an import edge are
  content-keyed and survive their target moving; a `` `Module:NNN` `` does not, and the commit that
  falsifies it need touch neither the citing file nor the cited declaration. ⚠️ **A line address
  resolves at the ref named in the smallest RENDERED BLOCK that names one — its paragraph, or the
  list item that holds it, and the nearest ref above it where that block names several — and at
  the tree the reader has checked out when no enclosing block names any** — and the three senses
  of a sha this list distinguishes above decide which ref that is: a **measurement** or
  **state-at** sha resolves a line address, an **attribution** sha does **not**, because it dates
  a claim's landing and not a coordinate. ⚠️ **The unit is the block and not the sentence, and
  which one it is was measured rather than chosen**: of the sixteen bare rows this page keys to a
  ref at `02a1652`, the sentence clears **2**, the paragraph **7** and the enclosing list item
  **16**, because the fourteen keyed to `b2d1981` are spread over four paragraphs of one bullet
  and only its second names the sha. ⚠️ **The block is also the unit `### The render gate` already
  computes** — `md.parse`'s `paragraph_open` and `list_item_open` maps — so a re-runner settles it
  with the instrument this file publishes and not by reading for a full stop. ⚠️ **Prefer a
  content key wherever one exists**: a line is admissible where the target has no name — a
  `variable` line, an `open Classical in`, a blank line — and re-pointing a stale number leaves it
  stale after the next insertion above it, which is why the two repairs this branch makes under it
  replace the number rather than move it.

  The census, at `02a1652`, over `EllipticCurves/**/*.lean` and this file, keyed on
  `` `([A-Z][A-Za-z0-9]*):(\d+)(?:-(\d+))?` `` with the name required to be a module stem of this
  tree, and on `` `:(\d+)(?:-(\d+))?` `` for the bare continuation form: **22 named** (20 here, 2 in
  `.lean`) and **36 bare** (25 here, 11 in `.lean`). ⚠️ **The named key requires the name to be a
  module stem of this tree, and that is a boundary and not a definition**: three further spans of
  the same shape carry a path-prefixed or `.lean`-suffixed name — `PlaceResidueComap` cites
  `RingTheory/RamificationInertia/Basic.lean` by line twice, and `MatrixRepModGeneral` cites
  `MatrixRepMod.lean` by line once. ⚠️ **The first two address a file of Mathlib, and a
  cross-repository line address resolves at no head of THIS repository at all**, because the pin
  moves under it: name the declaration and the pin. ⚠️ **Two tests, and they convict different
  rows.** Blank-or-out-of-bounds is automatic and is a floor and not a staleness test: it returns
  the two `.lean` rows and clears both live defects here. The drift test — the cited line's text at
  the commit that introduced the citation token (`git log -1 -S`) against its text at the resolving
  ref — returns **4 of the 22**: those two, which are repaired on an unlanded branch and are left
  alone here, and the two this branch repairs.

  ⚠️ **The bare form is the cleaner half and no automatic test can read it.** Sixteen of its 25
  rows at `02a1652` are keyed to a ref the block they sit in names — fourteen to `b2d1981` and two
  to `acbf51a` — and every one resolves there. ⚠️ **Re-scored against `9147113`, NOT ONE OF THE
  SIXTEEN IS CLEARED BY BOTH TESTS**: the drift test convicts **14**, the blank-or-out-of-bounds
  floor convicts **6**, they agree on **4**, and between them they cover all sixteen. ⚠️ **The two
  the drift test clears are the same address twice**, `:283`, blank at `b2d1981` and blank there —
  and those are the two the floor convicts wrongly, because the sentence cites that line AS a
  blank one. What has moved is the paragraph it is described as closing: *"Decide this only when
  you are about to CLEAR a row"* stands at `b2d1981:284` and **46** lines further down at
  `9147113`. **So on that row the floor convicts a correct citation while drift clears a stale
  one, and only the ruling above gets it right** — which is what a rule is for where two automatic
  tests disagree with each other and with the truth.
  And the module of a bare number is **not** the nearest named citation before it: at
  `02a1652:1576` three of them are distributed across the two modules that sentence names, in
  order, so a nearest-preceding resolver mis-assigns `:115` and reports a blank line that is not
  there. ⚠️ **Two of the 36 are convicted under this ruling, and the second is the sharper of the
  two.** The first is the `theorem`-line coordinate of the `#1774` retirement this branch repairs,
  whose block names a sha that is an **attribution** and so resolves nothing. The second is in
  `EllipticCurves.TateModule.ImageThree`, in the module-docstring paragraph that counts
  `EllipticCurves.TateModule.Image`'s declarations: it says that line 27 of that file is a fenced
  `lean` block, and line 27 is prose — the fence opens at line 23, the quoted `instance` stands at
  line 24 and the fence closes at line 25, and a `grep` for a fence in that file returns exactly
  those two. Its enclosing paragraph names no ref, so it resolves at the reader's tree, and there
  it is false. ⚠️ **And it was exact at no ref at all**: `git log -1 -S` puts the citation in
  `ffc3e20` (2026-08-24), where that file's fence already stood at the same three lines. **So the
  floor clears it — line 27 is not blank — and the drift test clears it too, because the cited
  line's text is byte-identical at the introducing commit and at the resolving ref. Only the
  ruling convicts it.** That is a third bucket beside *stale* and *blank*, it is the one no
  automatic test can reach at any ref, and the other 34 clear the blank-or-out-of-bounds test at
  their resolving ref. ⚠️ **That clearance is a floor and is not the drift test**, which does
  not run on this form at all, because a bare number's module is not mechanically recoverable. The
  shape that carries no risk is the one this file writes **five** times at `02a1652` — the sha and
  the line in one span, `49b327d:2895` — which resolves forever and is what a coordinate wants
  where no content key exists.
  ⚠️ **This bullet is inside two of the three populations it counts, and the figure that matters
  is the one for the tree this branch lands in.** ⚠️ **A ledger over this population has to be
  double-entered or it does not close**, and the rows here move in pairs: the two repairs take the
  `#1774` retirement's two coordinates out — one named, one bare — print the
  `WeilPairingCyclotomic` row of the eight-row list a second time in the new resolver clause, and
  move that list's eighth pointer out of it and back in as the quotation of the address retired
  there. **Two named tokens out and two in, so the two repairs are net 0 on the named form**; one
  bare out and two in — the number this bullet quotes and the blank line the paragraph above
  reads. Score the re-print as an addition without scoring the removal it pairs with and the sum
  derives one more than the tree has. ⚠️ **But the repairs are not the whole of it, and a ledger
  that stops at them does not close.** This bullet also PRINTS, as census tokens of its own, the
  two addresses PR #769 added to the tree — named, **+2** — and the three sha-and-line spans it
  writes itself, one as the shape that carries no risk and two as addresses — **+3**. So base
  `9147113`'s **24 named / 36 bare / 5 sha-keyed** becomes **26 / 37 / 8** with both commits
  in, and the three lines close: named 24 + 0 + 2, bare 36 − 1 + 2, sha-keyed 5 + 0 + 3.
  ⚠️ **The 22 in the census paragraph above is dated to `02a1652`, and that is drift and not
  falsification**: PR #769 landed as `9147113` and added `NthRootOfPullbackN:176` and
  `XDifference:53` on one table row of the triage in `### Import-closure membership`.

  ⚠️ **Those two are the newest rows in this population, and the ruling scores them the hard
  way.** The block they sit in is that table, which under the `commonmark` parse
  `### The render gate` prescribes is one paragraph and names no ref; the sentence that does name
  one — *"The triage of the 64, at `3f61ad7`"* — is the paragraph before it. So they resolve at
  the reader's tree, and at the reader's tree two of the three addresses in that row point at
  their own repair: `9147113` rewrites `XDifference.lean` and
  `WeilPairingAlternatingTwoRational.lean` in the same commit that writes the row, so the `false`
  verdict the cell records is true at `3f61ad7` while the line it addresses carries the **repair**
  here. ⚠️ **That is this axis's own mechanism in landed prose rather than in a commit message,
  and the drift test cannot see it**: the citation token and the resolving ref are the same
  commit, so drift is **0** by construction. Widen the block to the paragraph that names
  `3f61ad7` and both are exact; leave it as written and both are one commit stale on arrival.

  ⚠️ **And the third address in that cell is invisible to the named key**: its module stem is
  ELIDED to a leading `…`, so `[A-Z][A-Za-z0-9]*` does not match and the census counts two where
  the row has three. It is the **fourth** shape outside that key's boundary and the worst of the
  four — a path prefix or a `.lean` suffix still lets a reader recover the module, and an elision
  destroys the name, so the coordinate resolves only for a reader who already knows which file is
  meant. **One occurrence in the tree at `9147113`, and it landed today.** ⚠️ **An elided name
  must never carry a line address**: there is nothing left to re-point. ⚠️ **These are figures
  about `9147113` plus this branch and not forecasts**: PR #768 at `130cf38` adds three bare
  numbers, and whichever of the two lands last re-measures rather than copies.

* **An address a delivery did not derive has been checked by nobody, and what handed it over does
  not change that** (`#1915`). A `### `-heading citation, a line address, or an attribution of a
  property to a named seed is re-resolved against the tree the delivery is landing on, whatever its
  source: an issue description, a review comment, a round of the same branch that has already been
  pushed, a note in this project's memory, or a sibling section of this page. None of those is a
  checked source, and a delivery that repeats one has published it.
  ⚠️ **The review is the source worth naming, because it is the one nobody expects to fail.** A
  reject comment is a claim and not a verification, and a reviewer who has just re-derived every
  figure in a delivery to the digit will be believed on the clause they did not run — the accuracy
  of the checked half is what licenses the rest. `### Gate-discharge claims` takes a wrong pointer
  out of `### Retired claims`' reach on the ground that *a pointer asserts nothing about a
  declaration, a hypothesis or a population*, plain in the original — which settles what a wrong
  pointer costs once it has landed.  ⚠️ **The half before that is stated in the same section, for
  one source and one shape**: the worked example on `#1626`'s triage table closes with
  *Re-derive a row before repairing it*, bold in the original over that clause alone, and
  *a triage set inherited is a triage set unread*, plain. That names an issue and a table row and
  reaches no address, no figure and no review; what is written here generalises it.
  ⚠️ **Re-resolving is a different operation for each of the two shapes this page writes, and
  neither of them is a string comparison**:

  * a **heading citation carrying a line address** is resolved by locating that heading and its own
    line range in the base blob and asking whether the cited line falls inside it. The sections of
    this file run to hundreds of lines, so an address that sat inside one when it was written is
    inside its neighbour once enough insertion has gone in between, while the citation beside it
    still names the section it always named — two halves of one span that rot at different rates.
  * an **attribution of a property to a named seed** is resolved by reading that seed's own
    defining paragraph. The paragraph asserting the property is where a wrong attribution reads
    true, and on this page the two are routinely several screens apart.

  ⚠️ **A figure is inherited on the same terms as an address**, which a rule about line numbers
  alone would miss: a count arrives with a reading attached to it, and a count copied out of a
  review arrives with that reviewer's reading rather than with the one the page publishes. Which
  reading is right is what `### Module-block bullets`' recogniser rule decides; what this adds is
  that copying the number does not import the flag.
  ⚠️ **It governs what is written next and no sweep is owed, which is a measured statement rather
  than a convenient one.** No seed over this tree can find an inherited address, because what makes
  one inherited is a fact about a source that is not in the tree: a blob records what a sentence
  says and never where its author read it. So there is no population here to size and no count is
  written for one, which is the second branch of the rule `### Module-block bullets` states twice.
  ⚠️ **An instance already on the page is paid, and it is this rule failing with the observation
  running the other way**: the direction error recorded in this section's own pointer axis as
  *First recorded in PR #695's review and re-observed in PR #707's and PR #712's without being
  paid*, plain in the original. Three reviews saw that one, and none of the eleven deliveries
  that touched this file between the commit that wrote the pointer and the commit that repaired it
  re-resolved it, which is the same failure as trusting a review — a reject comment and a review's
  silence are both claims about a delivery and neither is a check of it.

* **A published recogniser is not published until its flags are** (`#1910`).
  `### Module-block bullets` rules *publish the recogniser beside any count, or write no count*,
  writing those words twice and both times about a count of its own, and it is silent on what
  publishing one takes. That is **short** and not false, which is the branch `### Reach clauses`'
  test sends to completion in place, so nothing retires here and neither copy is edited.
  ⚠️ **The bullet `#1915` landed in this list (`2f1a674`, PR #742) defers to that rule for exactly
  what the rule does not carry**: it rules that a count copied out of a review arrives with that
  reviewer's reading rather than with the one this page publishes, and that *Which reading is right
  is what `### Module-block bullets`' recogniser rule decides*, plain in the original. A reading is
  decided by the flags a count was published with, so that deferral lands on what is written here
  rather than on the sentence it names, and neither bullet edits the other.
  ⚠️ **It is completed in this list rather than in that section because its subject is what any
  published count owes a re-runner**, and three of the four readings that earned it are elsewhere:
  a seed on this page (`#1864`), a census inside a `.lean` docstring (`#1895`), and a paragraph of
  `### Gate-discharge claims` (`#1877`). Carrying a rule stated in one section out to the rest is
  what this list already does for *Declaration headlines are reach clauses too*. Beside the
  pattern, a count states:
  * ⚠️ **The name it will be cited by.** A seed is re-run because some other sentence names it, and
    a recogniser published under no name cannot be reached from the sentences that cite it: `grep`
    for the name finds the citations and never the flags. **Measured at `a570d4d`**, over
    `README.md`, the three seeds `### Module-block bullets`' pointer axis publishes are cited by
    name in `20` places — `7`, `5` and `8` for the noun-and-direction, nine-word and distance seeds
    — and are named at their own definitions in `0` of the three (`#2087`). All three now carry
    their name where they are defined; not one flag of any of them changed, and no figure any of
    them publishes moves. ⚠️ **The three are reproducible from what is printed beside them**, which
    is what makes the missing name the whole defect: re-implemented cold from those sentences
    alone they return `34` on `34` distinct lines at `2947444`, `41` at `d3a4ac5` and `14` at
    `d3a4ac5`, each exact, and a re-runner handed one of the names can still find none of them.
    ⚠️ **The control is the fourth seed of that axis** — the one with no noun anchor, keyed on the
    two direction words the first seed knows: `` `\b(above|below)\b` ``, case-insensitive over
    this file's non-fenced prose, which is the one recogniser of the family a stranger can guess
    from its name, and the guess is exact at `321` at `93cf1d4` and `328` at `a570d4d`.
    **A name a re-runner can resolve is worth as much as a flag**, and it is the cheapest one
    stated here.
  * **Case** — whether the match is case-insensitive.
  * **The unit of reading** — whole blob, or line by line. ⚠️ **A count of *lines* published beside
    a count of *occurrences* has to come out of one run of the seed**, or say which reading each is
    from: once a match may wrap, it lies on two lines and is a hit on neither of them line by line.
  * **Window anchoring and width**, for a proximity seed — centred on the match, or one-sided and
    which side.
  * **What one site is**, when the seed relates two tokens — which of the two the count is taken
    per. ⚠️ **The anchoring flag does not settle this**: a window taken *either side* of a token is
    a **symmetric** relation and admits the same pairs whichever end it is cut from, so what is
    left to decide is the projection. The worked case is the census this bullet states (`#1916`):
    the same **58** pairs at `e122163` are **36** sites counted one per matched phrase and **38**
    counted one per anchor token.
  * **Which files** — extensions, and whether anything untracked or generated is in.
  * **Whitespace normalisation**, and whether it is applied before the window is cut or after.
  * **Fence and markup handling, including when it costs nothing.** That a fence filter changes no
    figure at a named sha is a measurement; not having thought about fences is not. This list
    already records that inline emphasis defeats **both** of the phrase-keyed seeds its pointer
    axis publishes — the noun-and-direction seed and the distance seed — which is this flag met on
    two axes of this section and never carried off them. ⚠️ **And it is silent on the third, where
    the same flag costs nothing.** That seed keys on a bare token at a `\b` boundary, so a marker
    around the word leaves it matching, and the **41** it publishes at `d3a4ac5` counts a match
    written inside a pair of italic markers. A flag that defeats two seeds of an axis and leaves
    its third untouched is exactly the one a re-runner cannot guess.

  ⚠️ **The consequence is the half that pays**: a figure that cannot be reproduced from the flags
  printed beside it is not evidence, and a reader whose implementation disagrees with a published
  count should suspect the **flags** before either the figure or their own code. Four sessions on
  `#1895` and five reimplementations on `#1864` suspected the figure, and in both the figure was
  right and a flag was missing.
  ⚠️ **The flag that moves an answer furthest is not case, and it is the one this page states
  least often.** The `#962` citation census names its anchoring, in the `±160` of its own window;
  the attribution seed keyed on a citation *within 40 characters of a `PR #n`* is published twice
  here, names a width and no side both times, and sits in a paragraph that says in terms that
  *"The population is window-sensitive and the verdict is not"*.
  `EllipticCurves.FunctionField.WeilPairingTranslationSlotHprinN` publishes its census, at
  `2f1a674`, as: match *general `n`* or *uniform `n`* case-insensitively, within 170 characters
  either side of `ωₙ`, over every tracked `.lean` and `.md` file with whitespace normalised to
  single spaces. ⚠️ **That sentence does not state its unit**, and every figure here is counted one
  site per matched phrase; `#1916` holds the repair of it. Hold the phrases, the width and the sha
  fixed at `8b6571b` and move only the two flags, and it returns
  **39** sites in **30** modules centred and case-insensitively, **32 / 24** centred and
  case-sensitively, **30 / 26** and **23 / 20** with the window taken to the right of the match
  only, and **10 / 8** either way with it taken to the left. **Anchoring costs a factor of four,
  39 to 10, where case costs seven sites, 39 to 32** — a ratio and a difference, named as such
  because a parallel construction otherwise elides the second into *a factor of seven*, which is
  false and reverses the claim it is the evidence for. The sentence that first published that
  census stated neither flag.
  ⚠️ **Fence filtering moves no cell of that table at that sha**, under either reading of the
  filter — dropping the matches that sit in a fence, or deleting fenced text before the window is
  cut. That it costs nothing there is a measurement and not an omission, and it does not cost
  nothing everywhere: at `2f1a674` the second reading takes the same census from 36 to 37, because
  deleting a fence shortens the distances the window measures.
  ⚠️ **Writing the seed out here moves it, and a delta is what may be written about that.** The two
  phrases above land inside their own window, so this bullet adds exactly **two** matches to that
  census and no module — a difference between two trees, which holds at whatever base it lands on
  where a count of the tree would not. The defining file records **36** sites in **21** modules at
  `e122163` and dates every figure it publishes to a sha, so none of them is falsified, and the
  phantom a phrase-keyed count takes from prose about itself is one `### Module-block bullets`
  already prices.
  ⚠️ **What this bullet does to the other seeds this section publishes was checked and not
  assumed.** It adds no member of any of its three seeds, and it puts **14** bolded numerals
  standing alone on this page — counting the one in this clause, which is what makes that figure a
  fixed point rather than a count of the lines above it. ⚠️ **In digits, because that seed's word
  list stops at `twelve`**: written as a word this figure would not count itself, which is the
  calibration `#1864` landed and the cheapest demonstration of it. Every reading of the
  bolded-numeral seed this page gives is keyed to a sha or to the commit that wrote it, so none of
  them is falsified.
  ⚠️ **A sub-count flat across a long range of commits is a smell and not a corroboration.** The
  case-sensitive reading of that census is constant at **33 in 19** across all **58** commits from
  `6a1b8bf` to `e122163` inclusive, while the case-insensitive one steps 34 → 36 at `1d79187`. So
  the sessions that recorded the census as failing to reproduce also recorded base and head as
  equal and read the second as evidence for the first. One missing flag produced both readings.
  ⚠️ **The rule governs what is written next, and what is standing is named rather than swept.**
  `### Gate-discharge claims` publishes *"**36** occurrences on **32** lines in **6** files"*, with
  all three numerals bold in the original, under a seed it declares case-insensitive and read over
  whole blobs — and no single run returns that pair. Both of those figures are true of that tree:
  over whole blobs the 36 matches begin on 33 lines and touch 34, while the reading that gives 32
  lines gives 34 occurrences. ⚠️ **The pair is short of a flag rather than false**, which is why
  it takes a clause and not a retirement; `#1877` holds that seed's population and it is left
  there.
  ⚠️ **No count of compliant seeds is written here and none is owed.** Sizing that population is a
  reading job — `recogniser` is a word this page uses about seeds and about itself, so a
  vocabulary count is not a population of them — and `#1848`'s trap is a rule whose test is a
  count. A rule does not need a census to land.

### Retired claims

A clause that a later PR falsifies is kept as a **marked quotation** — the old text in
italics, attributed, followed by what replaced it — rather than deleted, so that a reader who
remembers the old claim learns why it went. ⚠️ **Retired declaration names are written in
italics, not backticks.** Backticks are how this development marks a live citation, and every
name-resolution check keys on them; a retired name in backticks is indistinguishable from a
dangling one.

⚠️ **A clause replicated into many blocks retires once if those blocks share its subject, and once
per block otherwise.** `#1694` is what forced the question: one sentence about
`WeierstrassCurve.Affine.equation_div_of_ψ_ne_zero` was copy-pasted into 37 module blocks by a
single sweep (`5d6884a`, PR #561), and read literally this section asked for 37 quotations of it. It
asks for **one**, in `EllipticCurves.Torsion.OmegaCrux` — the file that defines the declaration the
clause was about — because the 37 copies asserted **one proposition, not 37**: each said the same
thing about the same declaration, one reading of one signature falsified all of them at once, and
the reader this section serves is a reader who wants to know what that declaration says. ⚠️
**Contrast the two wordings that were retired once per block, at each site that falsified them**,
neither of them replicated any less: *"the bullets give the conclusions and not the hypotheses"*
across seven blocks (`#1647`, `#1650`, `#1662`, `#1686`) and *"no reach clause names it"* across
five (`#1688`, `#1696`). Both are universals over **the block's own list**, so each copy is a
different proposition falsified by a different list, and one quotation elsewhere would leave every
other block with no account of why its own sentence changed. ⚠️ **Both wordings are also still LIVE
at one site each, and that is this test working rather than an exception to it**:
`EllipticCurves.TateModule.DeterminantModGeneral` carries the first (eight blocks held it, seven
retired) and `EllipticCurves.FunctionField.MulByNSeparable` the second (six held it, five retired),
each read row by row and each true of *that* block's own list. **Occupancy never triggers this
section; falsification does**, so the counts above count retirements and not copies. **The test is
what the clause is about — not how many files carry it, and not how many PRs repaired it.** A claim
about the block it sits in retires where it sits; a claim about a subject that lives elsewhere
retires at the subject, once. ⚠️ Apply `### Reach clauses`' *"Read whether the old clause was false
or merely partial"* first: it decides whether this section binds at all, and only then does the
count above apply. ⚠️ **No census width changes either way.** `### Module-block bullets` already
prices the phantom that a retirement leaves in a phrase-keyed count, and says the gap widens with
every repair; that cost is accepted there and is **not** what decides placement here. ⚠️ **The rule
is retrospective and nothing is owed to it** — both rulings on record already comply, which is why
this paragraph states the tree rather than changing it.

⚠️ **A marked quotation's emphasis is the source's, and the form it is recorded in is free**
(`#1875`). `EllipticCurves.FunctionField.MulByNInertia` rules, of one retirement it makes, that the
emphasis is named outside the quotation rather than reproduced inside it, and until this paragraph
that reading was written down nowhere else. Read as a rule about **form** it is a rule this tree
has never held. The seed is whole-tree over every tracked `.lean` and `.md` file with runs of
whitespace collapsed: a marked quotation is an italic span wrapping a quoted string, and it breaks
the form when a bold span falls inside the quotation. At `42c9b11` that returns 1445 marked
quotations with 124 carrying a bold span inside, in 48 files — 50 in this file, 54 under
`EllipticCurves/FunctionField/`, and four in the file that publishes the ruling. At `aadc404` it
returns 1340 and 107. ⚠️ **A rule its own file breaks four times and this file breaks fifty times
is not an unswept rule**, and the direction of travel says the same: of the seventeen added in
those five days, fifteen are in this file, so the form is being exercised and not repaired.
⚠️ **The seed carries one flag and it costs five rows.** Refuse a `*` that is the second of a `**`
run to open a quotation, and refuse the same at the close, and the counts read 1433 and 129 at
`42c9b11`, 1328 and 112 at `aadc404`. The looser reading is the one every figure here is published
at; under either the population is in three digits and the finding does not move.
⚠️ **What the ruling is right about is fidelity, and fidelity is the test.** The emphasis a
quotation shows a reader must be the emphasis its source carries. Reproducing it inside the span
and naming it outside are both compliant, and the two defects are emphasis the source carries and
the quotation **drops** — the old text loses a part this section asks for — and emphasis the source
does not carry and the quotation **asserts**, which is the worse of the two, because it wears the
compliant form and no seed keyed on markup inside the span can see it.
⚠️ **Reproduce inside only where the reproduction renders.** A bold span inside a marked quotation
is `<strong>` inside `<em>` and a reader sees it; a single-asterisk span inside the same quotation
is `<em>` inside `<em>`, which applies one style twice and shows a reader nothing.
⚠️ **That, and not the bold, is the population the ruling's clause names, and it is nine rows** —
the same nine at `aadc404` and at `42c9b11`, every one of them a retirement:
`FunctionField.MulByNGalois`, `…MulByThreeGalois`, `…MulByTwoGalois`, `…MulByNInertia`,
`…WeilPairingAlternatingBaseChange`, `…WeilPairingAlternatingMu`, `…WeilPairingNondegenerateMu`,
`TateModule.FreeThree` and `TateModule.PrimaryImage`. ⚠️ **An uncalibrated seed decides nothing, so
one row is worked**: `MulByNGalois`'s quotes a bullet that stood at `06d36c8`, and the source there
— **with `group` in italics** — read *"`IsGalois` is delivered; the Galois group is not identified
with `E[n]`"*. That row is faithful and only its rendering is not, which is the distinction this
paragraph turns on.
⚠️ **The seed for the nine is given in words and not in markup, because this page is inside its
own corpus.** A printed example would itself be a row of the population it measures, which is how a
recogniser moves the figure it publishes. It is the marked quotation above, with a span opened and
closed by a lone asterisk inside it. Four delimiter flags decide what that returns, and set the way
below it returns ten rows at `42c9b11` and ten at `aadc404`, nine of them the nine.
⚠️ **Each of the first three flags set the other way returns twelve — the second only where bold is
left in — and the first returns a different twelve.** The opening asterisk may not be the second of
a doubled run: allow it and two bold spans wrapping a plain quoted string score, and one of those
false spans opens forty-eight lines above `TateModule.PrimaryImage`'s row and swallows it, so a
reader who diffs by module name sees agreement where the rows disagree. The closing asterisk may be
followed by another: refuse that and a quotation sitting inside a bold span — which closes on three
asterisks in a row — loses its close, runs on to the next quotation mark and scores whatever italic
lies between, which is two further rows, one of them in this file. The span inside may not cross a
line break: allow it and two wrapped lines join at unrelated asterisks, for two more. ⚠️ **The
fourth flag is whether bold runs are cut from the quotation before the span inside is looked for**,
and it is free at the setting above and worth those two rows at any setting where the closing flag
is wrong — a flag that costs nothing alone and something in company, which is the kind a seed
published one flag at a time hides.
⚠️ **The tenth row is an artefact and is dropped in the open rather than in a comment**: in
`EllipticCurves.FunctionField.WeilPairing` the span opens on the asterisk of an ordinary italic
clause that happens to contain a quoted phrase, so it is not a marked quotation at all. Every
implementation of the seed returns ten and this page names nine; the row above is the difference,
and a reader who finds it has reproduced the figure rather than contradicted it.
⚠️ **Emphasis that is not inline cannot be reproduced inside at all**, and that is the ruling's own
row: it closed under a ⚠️ as well as in bold, and a ⚠️ is paragraph structure rather than part of
the sentence, so naming the ⚠️ outside was the only way to record the ⚠️. The bold beside it is not
in that position — it renders inside a marked quotation — so naming the two outside together was
one compliant form of two, and the only way to record one of them rather than either. That is a
reason at that site and not a rule about bold. Its clause is partial in its scope and never false
of its own row, which `### Reach clauses` decides before this section binds, so it is scoped where
it stands rather than retired.
⚠️ **What is NOT measured, dated to `42c9b11` and scoped to this ruling.** None of the nine rows is
read against its source here — one worked row is not a census — so whether each reproduces its
source's emphasis, drops one, or asserts one is the read this rule makes possible, and it is owed.
The dropped half has no seed, because deciding it needs the old text at the attributed ref, and its
confirmed floor is four rows. The asserted half has no seed either, and its one known instance came
from a review comment's own emphasis being read back as the source's — the one mode with a known
cause, and the rule it wants is to re-read the source at the named ref rather than carry markup
across from a thread.

### Import-closure membership

A module docstring that says *"`X` is not in this file's import closure"*, *"the two are
import-incomparable"*, *"that module imports this one"* or *"this file is a leaf"* is making a claim
about the project's import graph from inside one file. ⚠️ **Each one is decided by a single walk
over the `^import EllipticCurves…` lines, in seconds, with no build** — the cheapest per-row cost of
any axis this page carries — and the population had never been walked before `#2033`.

**The recogniser and the count.** At `3f61ad7`:

```
git grep -o "import closure" 3f61ad7 -- '*.lean' README.md | wc -l   →  64
git grep -l "import closure" 3f61ad7 -- '*.lean' README.md | wc -l   →  47
git grep -o "import closure" 3f61ad7 -- README.md            | wc -l   →   0
```

⚠️ **Run it at a ref and not at `HEAD`, because this section is inside the population.** The third
figure is what makes this a `.lean`-docstring axis, and it is `0` at `3f61ad7` and at no commit
carrying these paragraphs: prose *about* a vocabulary is written *in* it. The same trap is on
`#2036`, where the house retirement form quotes the clause it retires and so keeps a paid row in
the seed's population — **a seed whose subject is prose has to say whether the rules text is in
scope**, and here it is not: the 64 are `.lean` docstring rows.

⚠️ **That is the narrow key and it is a vocabulary key, so the number it returns is a floor.** The
widened seed is ten atoms and is printed as a command rather than as a list of phrases:

```
W='import closure|import-incomparable|is a leaf|import graph|reverse import cone'
W="$W"'|does not import|neither imports|in the closure of|reached through|imported by'
W="$W"'|imports this file|imports this one|imports this module'
git grep -Eh "$W" 3f61ad7 -- '*.lean' README.md | wc -l                      →  178
git grep -El "$W" 3f61ad7 -- '*.lean' README.md | wc -l                      →  101
git grep -Eh "$W" 3f61ad7 -- '*.lean' README.md | grep -Evc "import closure"  →  114
```

⚠️ **`ten` counts ATOMS and the command prints THIRTEEN alternatives; the reading that reconciles
them is below, and stating it here is this section carrying out its own instruction.** The triage
further down already convicts the gap — *"the seed is printed as thirteen alternatives and described
above as ten in two places"*, and *"if a count of its atoms is offered, say what an atom is"* — and
supplies the only arithmetic that gets from thirteen to ten: **drop `import closure`, which is the
narrow key and not a widening atom, and count the three `imports this …` spellings as one atom.**
`13 − 1 − 2 = 10`. ⚠️ **Neither step was written at the site offering the count, which is here, so a
re-implementer counting alternatives as a check got thirteen and could not tell which reading was
wrong.** ⚠️ **Do not "repair" either `ten` to a `thirteen`**: the count is correct under this
definition, and the triage paragraph below quotes both `ten` sites verbatim, so changing them
falsifies it.

The second step is measured and not merely stipulated. `.lean` only, at `6f051d4`:
`imports this file` **39** rows in **30** files, `imports this one` **12** in **10**, and ⚠️
`imports this module` **0** in **0** — so the three spellings are **two** in practice, and were two
at `ac462ef` as well.

⚠️ **The pathspec is the seed's other degree of freedom, and a figure quoting this seed must name
it.** The command above walks `'*.lean' README.md`; the pair the seed is quoted for elsewhere on
this board is `.lean` **only**. Both readings, at `6f051d4`:

| pathspec | wide seed | narrow `"import closure"` key |
| --- | --- | --- |
| `-- '*.lean' README.md`, as printed above | **257** in **118** | **94** in **63** |
| ⚠️ `-- '*.lean'` alone | ⚠️ **220** in **117** | ⚠️ **83** in **62** |

⚠️ **`220 / 117` beside `83 / 62` is the `.lean`-only reading, and both pairs are unmoved at
`e4345ae` and `6f051d4`** — two shas a fresh clone can resolve, two seeds, every cell. They are also
unmoved at two superseded `#2248` / `#2254` round heads,
`9265c0f632293d6919f2b29c7656ebdfcdc8cce3` and `153312c85bb441ba95be549f2aa0aeb6ed33c8eb`, given at
full width because ⚠️ **`git ls-remote upstream` advertises neither and neither is an ancestor of
`main`, so a seven-hex abbreviation of either expands from nothing.** At `3f61ad7` the same
`.lean`-only reading is `176 / 100` and `64 / 47`, so the stability is across this pair of shas and
is not a property of the seed. **What a re-runner of this pair gets wrong is therefore the pathspec
and not the sha** — the opposite of what the *"run it at a ref"* warning above prepares them for:
that warning is about this section sitting inside its own population, and dropping `README.md` is
exactly how a quoter steps back out of it.

⚠️ **This round is inside that population and moves it, which is why every figure above is keyed to
a ref and none to `HEAD`.** The paragraphs added here carry **4** further rows of the wide seed and
**2** of the narrow key, taking this page from **37** to **41** and from **11** to **13**, and the
`README.md`-inclusive reading from `257 / 118` to `261 / 118` and from `94 / 63` to `96 / 63` — the
file counts unmoved, since this page was already a member of both. ⚠️ **The `.lean`-only reading
does not move at all**: `220 / 117` and `83 / 62` are what they were, which is the sharpest argument
for that pathspec being the one a figure about *docstrings* should quote.

**114 of those are outside the narrow key and none has been read**; the triage below is over the
64 and says nothing about them. ⚠️ **Print the alternation, not a prose list of its atoms.** Ten
quoted phrases in running prose read as a recogniser and are not one: drop a single atom in
transcription and the count moves by four lines and one file, with nothing in the wording to show a
re-implementer which atom is missing — `imported by` is the one that is easiest to lose, because
every other atom in the list is written from the importing end.

**The triage of the 64, at `3f61ad7`.** **43 true, 3 false, 5 true of less than they are offered
for, 6 counts routed to `#2005`, 7 not claims about this tree's graph at all.**

| bucket | n | what it is |
| --- | --- | --- |
| true | 43 | the relation holds, in the direction and at the strength the sentence states |
| **false** | **3** | `NthRootOfPullbackN:176`, `XDifference:53`, `…TwoRational:303` |
| split | 5 | one sentence copied into five files: true of the module it names, offered for two |
| count | 6 | a **standing figure** for a file's own closure size — `#2005`'s population |
| not a graph claim | 7 | a `Mathlib` closure, a scratch module, or *"a large import closure"* |

⚠️ **The `count` bucket is keyed on the figure being the claim, not on a number appearing.** Six
further rows carry a closure size as *evidence* for a membership or placement claim and are scored
`true`, because what they assert is the membership: `FormalGroup.GenuineLawComm:55` (**14**, and
*does not contain* `GenuineLawTransfer`), `FunctionField.TranslationMulByNCommGeneral:116` (**19**,
and `Torsion.NsmulOrder` is not among them), `TateModule.DeterminantModGeneral:34` (`37 → 71` and
`40 → 74`, pricing an edge *not* taken), `Galois.SubfieldAut:17` (**empty**, i.e. *"imports nothing
from this development"*), and `TateModule.Determinant:147` and `TateModule.GaloisAction:32`, which
list a sibling's closure out member for member. **All six figures were re-walked and all six are
exact.**

⚠️ **Say where the population stops.** `EllipticCurves.lean` imports **every** module under
`EllipticCurves/` directly, so the root aggregator is in *every* answer to *"which modules have both
`X` and `Y` in their closure"* and moves every such count by one. ⚠️ **This cell carried the
numeral 423, and `#2105` drops it rather than bumping it — measured, the cell was already stale by
seventeen before this branch reached it**: the root aggregator imports `423` modules at `3f61ad7`
and at this branch's first base `ee48553`, **440** at `main` `52d6dea`, and one more with this
commit. No ordinal is published for the module this commit adds, for the same reason. `mk_all
--check` is what enforces the *every* — so the count was the only part of this cell that could go
stale, and nothing on this board was re-checking it. `Torsion.XDifference:54-55` still publishes
the figure, pinned to `3f61ad7`, where it is exact.
**The counts in this section and in the rows they repair exclude it**, and the tree's prose already
names it when it is the only member — `TateModule.MatrixRepCompat:65-66`, *"its reverse import cone
being empty apart from the root aggregator `EllipticCurves`"*, which is exact.

⚠️ **The rule the three false rows share is one sentence: a membership claim that quantifies over
the tree is a COUNT, and must carry one.** *"`X` is not in this file's closure"* names two modules
and is refuted by one walk from one of them. *"the unique module in the tree whose closure contains
both"* and *"in the closure of **each** of its three imports"* quantify over modules the sentence
does not name, and neither carried a number:

* `Torsion.XDifference` said `XDifferencePoint` was **the unique** module whose closure contains
  both it and `Torsion.NsmulSurjective`. **51** modules do; **two** of them are minimal, the second
  being `Torsion.NsmulLadder`, which imports `XDifference` directly exactly as the named witness
  does. Repaired with the count and both witnesses.
* `FunctionField.WeilPairingAlternatingTwoRational` said two modules were in the closure of **each
  of its three imports**. It has **four**, and the fourth is `EllipticCurves.Fixtures` — a leaf with
  an empty `EllipticCurves` closure, which contains neither. ⚠️ **A leaf is the import an *"each of
  its imports"* clause forgets**, because it is the one nothing was taken from. Repaired.
* `FunctionField.NthRootOfPullbackN` denied that `Torsion.NsmulOrder` was in its closure in one
  clause and announced, in the next, the `MulByNXCoordFormula` edge that put it there. That row is
  `#2005`'s and is repaired on its branch; it is counted here because the axis convicts it and a
  triage that dropped it would publish 2 where the walk returns 3.

⚠️ **`import` in this tree's prose means the Lean keyword, and a sentence that means the closure
should say so.** Under the closure reading a sentence contrasting *"imports"* with *"reached through
them"* says nothing, which is the tell that the direct reading was meant. Two true rows are loose
here rather than wrong, and they are loose in different ways. `Torsion.DivisionPolynomialEval:171`
writes *"they import this file"* of **two** consumers — its subject is *"Both consumers named
above"*, `Torsion.TriplingSurjective` and `Torsion.OmegaNumerator` — and **neither imports it**: the
first reaches it through `Torsion.DoublingSurjective`, the second through its single import
`Torsion.OmegaOnCurve`. ⚠️ **It is the cleanest instance of the rule this paragraph states**, being
the only row loose about *both* modules it names; its second clause, *"neither is in its import
closure"*, is true and is about the other direction. `Torsion.WardR1:67` writes *"those modules
import this file"* of **two**, and is the split shape rather than the loose one:
`Torsion.WardR1Core` imports `WardR1` **directly**, and only `Torsion.WardHalving` reaches it
transitively — through its single import `Torsion.EllipticNetSlices`. ⚠️ **The two-module sentence
is where this axis keeps failing**: every false row above quantifies past what it names, and so does
this one, by one module. The form that gets it right is in the tree already, at
`Torsion.WardR1Core:116-117`: *"that module imports this one (through
`EllipticCurves.Torsion.EllipticNetSlices`)"*. Name the route or write *"reaches"*.

**The split bucket is not a fifth false row and must not be reported as one.** One sentence in
`TateModule/DeterminantThree`, `ImageProfiniteThree`, `ImageThree`, `MatrixContinuityThree` and
`MatrixRepThree` reads *"`EllipticCurves.Torsion.StructureGeneral` is not in `OpenKernel`'s import
closure at all"*, one clause after naming **both** `OpenKernel` and `OpenKernelGeneral`. It is true
of `OpenKernel`; `OpenKernelGeneral`'s closure **does** contain `StructureGeneral`. Being in a
closure is not taking a hypothesis through it, so the claim the sentence is supporting stands, and
the defect — if a reader agrees there is one — is elision and not falsity. ⚠️ **Five files carry it
and one walk decides all five**, so under `#1614` it is one repair, not five.

⚠️ **Walk the source, not the environment, and say which you walked.** `ModuleData.imports` from a
`run_cmd` is the same graph *of the modules in that environment*, and an environment built on a
branch carries modules that are not in the tree: the same probe returned **52** where the source
walk returns **51**, the extra being a module from an unlanded branch's `.olean`s left in the build
directory. ⚠️ **And a source walk that counts the root aggregator returns 52 too, with different
membership** — agreeing on the number is not agreeing on the answer, which is why the population
clause above is not optional. `env.allImportedModuleNames` answers a third question — what the
*querying* file imports — and a scratch file that imports both `A` and `B` reports `B` in `A`'s
closure whatever `A` does.
**Per-module is `moduleData[idx].imports` transitively, or the `^import` lines; nothing else.**

**The widened residue, read one row at a time at `ac462ef`.** The narrow key's 64 were triaged
above; the widened alternation returns **117** further `.lean` rows in **75** files that the narrow
key does not see, and that is all of them **at that sha**. (The same alternation returns 130 rows
over `.lean` and `README.md` together; the other **13** are on this page, which is the rules text
and is out of this axis's scope by the same clause that makes the narrow key's `README.md` figure
`0`.) ⚠️ **A population figure is keyed on the left and reads forward, and this one moved while it
was in review**: it is **119** rows in **77** files at `1f3c95c`, the two arrivals being
`TateModule/FreeThree:117` and `TateModule/PrimaryFree:147`, both landed by PR #428. **Both are
read here and both are TRUE** — `MatrixRepThree` imports `FreeThree` on an `^import` line and
`FreeThree` does not reach `TateModule.GaloisAction`; `PrimaryFree` and `PrimaryMatrixRep` import
neither the other, and their common ancestors are **exactly** `TateModule.Basic` and
`Torsion.Defs`, two of two. **So the `true` bucket is 85 at `ac462ef` and 87 at `1f3c95c`, and the
`false` and `loose` counts below are the whole residue at either sha.**

| bucket | n | what it is |
| --- | --- | --- |
| true | 85 | the relation holds, in the direction and at the strength the sentence states |
| **false** | **7** | in **6** files, listed below; all six are repaired in this commit |
| **loose** | **9** | true of the closure, false of the `import` the page prescribes |
| not a graph claim | 16 | a route through a *lemma*, a Mathlib closure, or `AddSubgroup.closure` |

⚠️ **The seed is printed as thirteen alternatives and described above as ten in two places, only
one of which carries the words** — the widened-seed paragraph writes *"ten atoms"* and the
paragraph beside the alternation writes *"Ten quoted phrases in running prose"* — **and no rule on
this page gets from one number to the other.**  ⚠️ **A count of *two* over the quoted span is
therefore a count over the CLAIM and not over the WORDS**, which is a distinction this page
enforces on other files' prose and must state when it counts its own.

The only arithmetic that gets from thirteen to ten: drop `import closure`, which is the narrow key
and not a widening atom, and read
`imports this file` / `imports this one` / `imports this module` as three spellings of one atom —
`13 − 1 − 2 = 10`. ⚠️ **Both steps are needed and neither is written down**, which matters because
the paragraph beside the count is the one telling a re-implementer that *"drop a single atom in
transcription and the count moves by four lines and one file"*: **a re-implementer counting the
atoms as a check gets thirteen and cannot tell which reading is wrong.** Print the alternation, and
if a count of its atoms is offered, say what an atom is. (`imports this module` returns **0**
`.lean` rows at `ac462ef` — its one hit there is the alternation line on this page printing
itself — so the three spellings are two in practice as well.)

⚠️ **The `count` bucket is empty here and that is a property of the key, not of the tree**: a
standing closure *size* is written with the words `import closure`, so the narrow key already holds
every one of them and the residue holds none. The residue's own size figures — *"closures of **19**
and **24**"* (`Torsion.NsmulSmoothSurjective:47`), `Continuity`'s three-member closure listed out —
are evidence for a membership claim and score `true`, as the six above do.

⚠️ **Four of the seven were exact at the commit that wrote them and the other three were false
when written, and the four split again by *where the falsifying edit was*.** Two are claims about
the rest of the tree — a reverse import cone, a count of modules — and are falsified by an edit to
a file they do not name, which no reviewer of the carrying file ever sees. **The other two are
falsified by an edit to the file that carries them**: one counts that file's own `^import` lines
and the file gained one; one is a *marginal* cost, which is a function of the other imports, and
the file gained three. ⚠️ **That second half is the cheap one — the diff that breaks the figure is
the diff a reviewer is already reading** — and it is half of **the four**, which is **two of the
seven**: *bucket* is this table's word for the seven, and both denominators are live in this
paragraph.

* `FunctionField.MulByNFibre:853` — *"nothing imports this file"*. At `ac462ef` the reverse cone
  apart from the root is **4** and the direct importers are **1**; at `135f257`, where it was
  written, both are **0**. Exact, then rotted. ⚠️ **Which of the two a row reports is itself part
  of the row** — see the paragraph below this list.
* `Torsion.Collinearity:59-62` — *"measured over all **387** project modules"*, *"the only module
  whose closure contains this file and any of them is the root aggregator"* and *"this file's only
  direct importer"*. At `ac462ef`: **429**, **29** other modules, and `Torsion.NetVieta`. **All
  three were exact at `b1a4cda`**, where they were written.
* `…WeilPairingProductRelationRootIndependent:138` — *"one of this file's **two** imports"*. Three
  at `ac462ef`; **two at `dd08255`**, and the one it gained is `Fixtures`, a leaf.
* `…WeilPairingAlternatingAssemblyN:167` — *"`MulByNComposition` costs **12** more"*. **1** at
  `ac462ef`; **12 at `4ad5475`**, where it was written.
* `…WeilPairingAlternatingAssemblyN:169` — *"nothing imports this file … a file that is a leaf"*.
  At `ac462ef` the reverse cone apart from the root is **4** and the direct importers are **3**;
  at `4ad5475` both are ⚠️ **1: false when it was written**, under either reading.
* `TateModule.PrimaryMatrixRepBasisChange:109` — a reverse cone **enumerated** as four modules. At
  `ac462ef` the cone apart from the root is **5** and the direct importers are **3**, and ⚠️ **the
  cone was 5 at `ee0b8a4` too**: short from the start, not rotted.
* `TateModule.MatrixRepModGeneral:33` — *"**+34** modules (40 → 74)"*. The walk gives **+35**
  (40 → 75) at `ac462ef` ⚠️ **and at `a1910da`**, where it was written.

⚠️ **A REVERSE-CONE COUNT AND A DIRECT-IMPORTER COUNT ARE DIFFERENT NUMBERS, AND A ROW THAT
REPORTS ONE IN THE OTHER'S WORDING IS THE SAME DEFECT THIS AXIS EXISTS TO FIND.** *"`X` imports
this file"* and *"`X` has this file in its closure"* are the two relations this section already
rules between, and the false rows above are a running demonstration that the numbers come apart:
`MulByNFibre` is **4 / 1** at `ac462ef`, `…AssemblyN:169` is **4 / 3**, and
`PrimaryMatrixRepBasisChange:109` is **5 / 3**. ⚠️ **At the older end of a two-ref comparison they
routinely agree** — `MulByNFibre` is `0 / 0` at `135f257`, `…AssemblyN` is `1 / 1` at `4ad5475` —
**so only the right-hand end can expose a count taken with one instrument and written with the
other**, and a repair that carries the old wording forward re-commits the row it retires.
**The three rows above whose figure is a reverse-cone count — `MulByNFibre:853`,
`…AssemblyN:169` and `PrimaryMatrixRepBasisChange:109` — therefore print the direct count beside
it, and the other four count something else (a joint closure condition, a file's own `^import`
lines, a marginal cost, a closure size) and say which.** ⚠️ **The refutation needs no walker**:
`git show <sha>:<file> | grep '^import'` over each *named* module decides the direct half of an
enumerated claim outright, with no graph walk and no build — which is how an enumeration is
checked against its own wording.

⚠️ **Two of the seven are arithmetic rather than membership, and each is worth a rule.** The first:
**an edge costs the module it adds *as well as* that module's closure.**
`MatrixRepModGeneral`'s `+34` is exactly the closure of the module the import names with the module
itself dropped, and the same paragraph writes *"the **53** modules in `StructureGeneral`'s
closure"*, which counts it — **both conventions in one sentence, and they differ by one at every
row**. The second: **a marginal cost is a function of the *other* imports, so it is falsified by a
sibling.** `MulByNComposition`'s `12` did not move because anything about that module changed; it
moved to `1` because `WeilPairingAlternatingAssemblyN` has since taken three further imports that
carry eleven of the twelve between them.

⚠️ **`leaf`, *as an import-graph word*, is written in this tree in three incompatible senses, and
nothing on this page said so.**  ⚠️ **The scope is not decoration, because the word is wider than
the graph**: `\bleaf\b` returns **43** occurrences on **41** lines in **22** `.lean` files at
`ac462ef`, and **four** of those lines are not about imports at all — `WeilPairing:626` and `:640`
and `WeilPairingAntisymmetric:99` name the leaf of an **issue** tree, and `LocalRingTaylor:132` is
about *"the leaf polynomials"* of a Taylor expansion. ⚠️ **And a fourth graph reading is not one
of the three: a sense SCOPED TO A SUBTREE, which no tree-wide walk decides.**
`TranslationAutomorphism:239` and `TranslationProjAction:84` each keep a file *"a leaf of the
translation subtree"* — sense 1 scoped — and `MatrixRepMod:99-100`, which this paragraph holds up
below as the form to copy, is sense 2 scoped to `TateModule/`. **That is eight line numbers in
seven citations across six files**, and ⚠️ **six of the eight resolve identically at `ac462ef` and
at this head — two do NOT.** `WeilPairing:626` and `:640` are `:688` and `:702` at `1f3c95c`:
PR #804's `+66 / −4` in that file all lands above them and shifts both by **62**, with no edit to
either line and no round of this branch touching the file, which is `#2037`'s class exactly. They
are quoted here at `ac462ef`, the sha this section is keyed to. None of the six files is touched
by this commit. `EllipticCurves.Fixtures` is
*"a leaf importing no `EllipticCurves` module at all"* — it imports nothing.
`WeilPairingAlternatingAssemblyN:169` and `TateModule.MatrixRepMod:99-100` call a file a leaf for
the opposite reason, that nothing imports **it**. And `MatrixRepModGeneral:33`
writes *"a leaf **over** `StructureGeneral`"*, which is neither: it means *adds nothing over `X`
that the file being charged already has*, a claim about three modules. ⚠️ **The first two are
opposite ends of the same edge and the third is not an edge at all**, so a bare *"is a leaf"* is
decided by no walk until the sentence says which. `MatrixRepMod:99` is the form to copy — *"is a
leaf: **nothing here or elsewhere under `TateModule/` imports it**"* — and it is exact: the module
it says that of is `FunctionField.MatrixRepDeterminantCharacter`, whose reverse cone at `ac462ef`
is **0** apart from the root aggregator and whose direct importers are **0** as well, so the row
does not turn on the distinction at all.

**The loose bucket, and why the nine are not a fifth false row.** Each is true of the closure and
false of the `import` this page prescribes — `DivisionPolynomialEval:171`'s shape, one bucket
wider. They are `Torsion.XDifference:40`, `:84` and `:159`, `Torsion.WardR1Core:155`,
`Torsion.OmegaCrux:249`, `FunctionField.MulByNXCoordRatFunc:309`,
`FunctionField.ValuationAtInfinity:452`, `FunctionField.WeilPairingProductRelation:114` and
`FunctionField.WeilPairingDivisorSlotBilinearHprinN:68`. Three of them are worth naming:

* ⚠️ **One edge, described from both ends, each end true only under the opposite reading.**
  `WeilPairingProductRelation:114` says *"`WeilPairingFunctionThree` imports this file"* and
  `WeilPairingFunctionThree:46` says *"this file does not import that module"*. Both are about the
  same pair; the module is in the closure and is not one of the four `^import` lines. **The pair
  is the cleanest argument on this board for the page's own rule**, because no single reading makes
  both sentences true.
* ⚠️ **The file this page holds up as the form to copy contains the counterexample.**
  `WardR1Core:116-117` is quoted above as the right shape — *"that module imports this one (through
  `EllipticCurves.Torsion.EllipticNetSlices`)"* — and it is exact. Thirty-nine lines later, about
  the same pair, `:155` writes *"since that module imports this one"* with no route.
* ⚠️ **A sentence that advertises the measurement can still group the two.** `OmegaCrux:249` opens
  *"The three sit differently against this file, and the difference is measured"* and then says
  `NsmulYCoord` and `NsmulYPeriodic` *"both import this module"*: the first is an `^import` line,
  the second reaches it through the first.

⚠️ **`XDifference` carries three of the nine and the direct form beside them** — `:52` says
*"`XDifferencePoint` imports this file"*, which is an `^import` line, while `:40`, `:84` and `:159`
say *"`Torsion.NsmulOrder` … which imports this file"*, which is two hops (through `NsmulLadder` or
`NsmulSurjective`). **Both spellings are in one docstring**, which is why the fix for this bucket
is a house word and not a per-row judgement: write *"reaches"*, or name the route.

⚠️ **Run the widened seed at `ac462ef` and not at this head, for the reason the narrow key already
gives.** The repairs this commit makes quote the clauses they retire and this section names the
vocabulary it rules on, so the residue at the head of the commit that publishes these figures is
**123** rows in **77** files — against **119** in **77** at `1f3c95c`, this commit's base, and
**117** in **75** at `ac462ef`, the sha the triage is keyed to — and the page's own share is
**26** rather than 13. ⚠️ **A head figure is re-run at the head it names and never carried from
an earlier round's head, because the base under it moves**: this commit adds **4** rows to the
`.lean` residue and takes none away, and changes no file's membership at all, so a head cell of
**75** under a base cell of **77** is refuted by arithmetic before any grep is run. **A triage is
keyed to the tree it read, and this one is keyed to `ac462ef`.**

**What reproduced exactly, and is worth knowing before the next reorganisation.**
`WeilPairingFunctionN:109`'s route table — *"three of those seven modules are `import`s of this
file and four are reached through them"* — is exact row for row at `ac462ef`, **including** its
sharpest clause, that `#854`'s module rides in **only** through `WeilPairingFunctionTwo`.
`TateModule.Continuity:28` is the residue's only sha-keyed row and it reproduces at both ends,
under the exclusion the row itself states (*"apart from the root aggregator and this one"*): at
`807ac29` `TateModule.GaloisAction`'s reverse cone is **8**, and at `ac462ef` it is **51**, which
is the *"wider margin"* that row claims without having to be re-run. ⚠️ **Dropping only the root
gives 9 and 52** — one exclusion, stated once in the source and owed at both ends of any
re-measurement of it.

## Building

This project pins a specific Mathlib revision via `lake-manifest.json` and the
matching toolchain in `lean-toolchain`. To build:

```bash
lake exe cache get   # download the Mathlib build cache
lake build
```

## Linting

Two different linter suites apply to this project, and they are easy to confuse.

* The **syntactic** linters run during elaboration and surface as build warnings.
  They are enabled by `weak.linter.mathlibStandardSet = true` in `lakefile.toml`,
  and `lake build --wfail` (see below) is what enforces them.
* The **environment** linters — `simpNF`, `unusedArguments`, `defsWithUnderscore`,
  `docBlame`, `synTaut`, `checkType`, `deprecatedNoSince`, `impossibleInstance`,
  `nonClassInstance`, `simpComm`, `structureInType`, `subsetDotNotationLinter`,
  `tacticDocs`, `unusedHavesSuffices` — are a **post-hoc pass over the elaborated
  environment**, run by Batteries' `runLinter` driver. `lake build` never invokes
  them, so a green, warning-free build says nothing at all about them.

Run the second suite with:

```bash
lake lint            # auto-detects the default target, `EllipticCurves`
```

It takes roughly 10–20 s on top of a warm build (measured: ~11 s locally, 15–18 s on a
CI runner), and prints `-- Linting passed for EllipticCurves.` when clean.

CI runs it on every push and pull request: `leanprover/lean-action@v1` probes with
`lake check-lint` and runs `lake lint` itself when it finds a driver. **The driver is the
single line `lintDriver = "batteries/runLinter"` in `lakefile.toml`**, and it is
load-bearing. Remove it and the two halves behave very differently:

* `lake lint` **fails loudly** — `error: no lint driver configured and builtin linting
  is disabled`, exit 1. Locally you cannot miss it. ⚠️ **The version that status was taken
  at is the one the tracked `lean-toolchain` pins** — `leanprover/lean4:v4.32.0`, which
  carries Lake — so `### Tool-behaviour claims`' rule is paid here by a POINTER to a tracked
  file and not by a transcribed string, which is a key that cannot drift out of step with the
  tree it describes. ⚠️ **That section's Lean carve-out states a narrower warrant than the
  claim it licenses** — *"so a job count is reproducible by construction"* — and an exit
  status is not a job count; the pointer above is written to hold under either reading.
* CI, under `lean-action`'s default `lint: default`, would **not**: the probe fails, the
  action logs `lake check-lint failed -> will not run lake lint`, and the job stays green
  with the suite never run. That is the silent failure mode, and it is why the workflow
  passes `lint: "true"` explicitly — that setting turns a missing driver into
  `::error::lake check-lint failed: could not find a lint driver` and a red job, rather
  than a skipped step.

That silence is not hypothetical: the suite had never been run on this repository at
all, and when it first was, it reported 53 findings — 33 `@[simp]` lemmas whose
left-hand side was not in simp-normal form (so they could never fire), 16 naming
violations and 4 unused hypotheses — against a build that was, and had always been,
warning-free.

## Development

The `.orchestra/` folder contains scripts used to prepare and validate the
project in an automated setting:

* `before.sh` warms the Mathlib build cache.
* `validation.sh` checks that the worktree is clean, that no line inside a Lean
  comment looks like an `import` to the import-closure walkers (see
  [Import-closure figures](#import-closure-figures)), that no Markdown ATX
  heading wraps onto a second source line (see `### Scope of the rules above`'s
  *"A heading is one source line"* bullet), that every `.lean` file is
  imported (`mk_all --check`), that the project builds with warnings treated as
  errors (`lake build --wfail`), and that the environment linters pass
  (`lake lint`; see [Linting](#linting) — the last two are different suites).
  ⚠️ **The first three cost seconds and run ahead of everything that needs
  Lake**, so a branch author learns about a whitespace position or a wrapped
  title without waiting for a build.

### Tool-behaviour claims

Every other gate on this page resolves a claim against a **blob**: a quotation, a count, a
coordinate, an import closure. A clause that says *"`lake lint` exits 1"* or *"`merge-tree` prints
nothing on stdout"* does not. It is a claim about a **tool's behaviour**, and the only thing that
resolves it is **running the tool**. ⚠️ **So it is the cheapest claim here to falsify and the one
nothing above can see**: the span test resolves quotations, the render gate parses, the merge gate
merges, the page census counts, and **none of them can see a wrong exit code.**

⚠️ **Every figure in this section — not only the two tree rows below — was taken at `git 2.39.5`,
`bash 5.2.15(1)-release`, `python3` 3.11.2 and Lake 5.0.0-src+8c9756b / Lean 4.32.0.** ⚠️ **The list
is the tools that produce a figure HERE and nothing else**: `git` every merge-tree cell, `bash` the
`|| exit 1` row, `python3` every census and the whole four-window sweep, Lake and Lean both lint
rows. **`markdown-it` is deliberately absent**, because it produces no figure in this section at all
— and it is the one tool the pins table below shows this page pinning to the patch level in
34 places, which is the asymmetry that rule exists to close. The sentence is scoped to the whole
section deliberately: the rule at the bottom is that a behaviour claim names its version, and the
first place it falls due is the section that states it.

**The population, at `0b8f3d1` (`README.md` blob `146026e`, `lakefile.toml` blob `dadf0ad`).**
⚠️ **Every citation below names a section and a quotation and not a line**, because a coordinate in
this file has **three** ways to go false against a quotation's one (`#2037`): an insertion above it,
a **deletion** above it, and a re-flow of the paragraph it points into, which moves nothing above it
at all. ⚠️ **The deletion half is not hypothetical — `60` of the `759` commits at `0b8f3d1` delete
lines from `README.md`**, and the count is **60** at `a232601` too; the reading is
`git log --numstat -- README.md`, rows whose second column is nonzero, with `c6ef24a` at `+14 / −7`,
`ab5ec3a` at `+134 / −10` and `dba89ee` at `+91 / −22`. And `#2037`'s own two tree rows sit **on a
blank line**, which is neither an insertion nor a deletion above them. The line numbers here are in
another file and carry that file's blob sha. Recogniser, case-insensitive, the
alternatives joined by a **bare `|`** — the spaces around the pipes and the fold are display only —
over text whitespace-normalised to single spaces:

```text
exits? \*?\*?[01]\*?\*?\b | exit (status|code) (of )?\*?\*?[01]\*?\*?\b | prints nothing
| prints? no output | silent(ly)? (fails|succeeds) | survives `set -e`
```

⚠️ **AND THE CORPUS PREPARATION IS PART OF THE RECOGNISER, BECAUSE THIS IS THE FIRST SECTION HERE
WHOSE CORPUS IS NOT `.md`/`.lean`: classify and strip PER LINE — for a non-prose file keep only its
comment lines, with the comment marker stripped — and flatten AFTER, not before.** Flattening first
destroys the line boundaries the classification needs, and it is the whole difference between the
last two rows:

| key | occurrences | carriers |
|---|---|---|
| landed commit messages, all **759** | **221** | **115** |
| the tree, the tracked `.md`/`.lean` files | **the baseline** | **the baseline** |
| ⚠️ the tree, all tracked files, per line first | **+ the comment claims** | **+ their files** |
| ⚠️ the same, flattened first | ⚠️ **+1 per shell `exit 1`** | **+ the code-only carriers** |

⚠️⚠️ **THE TREE ROWS ARE PUBLISHED AS DIFFERENCES AND NOT AS TOTALS, AND THE DECISION IS THE
ARTIFACT HERE.** The absolutes were measured, keyed and true at `0b8f3d1`, and under `#1664` they
are correct-and-stale at that ref rather than false — but they rot on every landing that writes a
behaviour claim, and **this page has become the overwhelming carrier of its own key**, so the cell
doing the arguing was the cell least able to hold still. ⚠️ **The two contrasts the paragraph
below is about hold where the totals do not, and that is measured at three refs rather than
argued**: the all-tracked key exceeds the `.md`/`.lean` key by **+1** occurrence in **+1** carrier
at `0b8f3d1`, at `ab3d3ab` and at this head alike. ⚠️ **The flatten-order row is the one whose
difference is NOT a one, and a single numeral there would be the wrong shape**: its carrier delta
is **+1** at all three refs, while its OCCURRENCE delta is one per `exit 1` the shell script
spells — **4**, **5** and **6** at those refs, under three different blobs.  ⚠️⚠️ **AND EACH DELTA
IS NAMED BY WHAT IT COUNTS AND NOT BY A NUMERAL, BECAUSE A DIFFERENCE ROTS TOO AND ITS ROT IS THE
WORSE SHAPE**: a `+1` that should read `+2` still announces itself as a figure, while a carrier
`+1` that should read **0** asserts the ABSENCE of the contrast the paragraph below exists to
argue. ⚠️ **So the conditions are stated here instead, and no re-key is ever owed**: the per-line
row's two deltas move whenever a non-prose file gains a behaviour claim in a COMMENT, and the
flatten-order row's carrier column empties as soon as every code-only carrier has gained one — a
`.orchestra/validation.sh` that gains one comment claim does both at once. ⚠️⚠️ **AND A RELATION
FOR THE TOTALS WAS TRIED AND THERE IS NONE TO STATE**, which is the negative result `#2304`'s
repair asks for and here does not get: no module count and no pinned population stands on the
right-hand side, only *how often this page happens to say `exit 1`*, and it is proportional to the
corpus in no reading — between `0b8f3d1` and this head the tracked set grew by under a tenth while
`README.md`'s own carriage grew by more than an order of magnitude. ⚠️ **The differences are also
a fixed point of the round that publishes them**, which no total ever was: `README.md` is in both
tree corpora, so its own prose cancels out of both deltas and this clause moves neither.

⚠️ **The `.md`/`.lean` key is short by one, and the file it misses is the one a reader would check
first.** `lakefile.toml`:**9–10** (blob `dadf0ad`, unmoved at all three refs above) carries
*"Without this line `lake lint` fails with `no lint driver configured` (exit 1)"* — the **same**
behaviour claim `## Linting` makes of the same flag, written twice and gated nowhere; the line the
claim is *about*, `lintDriver`, is **13**. ⚠️ **Flattening first overshoots by one for each `exit 1`
that `.orchestra/validation.sh` spells as *shell code*** (**4** of them at blob `d286aa8`); per line
that file contributes **0** at that blob — its claims are code-only there, and one in a comment
would move it into the row above — so the code-versus-prose discriminator falls out of the order for
free instead of needing a second pass. ⚠️ **And the order is what makes that quotation resolve at
all**: flattened first it is `NO-SOURCE` in every tracked file, because the sentence wraps across
lines 9 and 10 and the continuation opens with `# ` — and **a `#` is not whitespace**, so the
flattened file reads *"fails # with"*.

**Both tree-resident claims re-run rather than assumed.** ⚠️ **Both are TRUE, and the class
convicts neither** — which is why the rule below is about naming a version, not about repairing a
row. ⚠️ **At `0b8f3d1` that pair was the whole of the tree's population and it is not that now**,
so what the differential rows above rest on is the two contrasts and not the pair's completeness.

* **`## Linting`, and `lakefile.toml`:9–10** — *"`lake lint` **fails loudly**"*, with
  `error: no lint driver configured and builtin linting is disabled` and exit 1.
  ✅ **Exact, message and status.**
* **`### The neighbour population`** — *"`git merge-tree --write-tree <main> 6327391e` exits **1**
  against `ac462ef`, `44272f7` and `871a224` alike"*. ✅ **Exit 1 at all three, and at `0b8f3d1`.**

The controls are what make those two readings worth anything. For the lint row: with a driver
**configured but broken** the status is still 1 and the message is *different*
(`invalid lint driver: unknown script or executable`), so the quoted string really does pick out the
*missing*-driver case; and `lake check-lint`, which is what CI probes with, is **exit 0** with a
driver and **exit 1** without. For the merge row, `--write-tree` on a conflicting pair — base
`0b8f3d1` against `6327391e`, **default `merge.conflictStyle`**, which is what an unconfigured slot
has:

| reading | value |
|---|---|
| exit status | **1** |
| marker lines on **stdout** | **0** |
| `^CONFLICT` lines on stdout | ⚠️ **2**, naming both conflicted files |
| stdout / stderr | ⚠️ **987** bytes / **0** bytes |
| marker lines **inside the written tree** | **9** + **6** = ⚠️ **15**, across **2** files |

⚠️ **THE SPLIT IS THE PUBLISHABLE FIGURE AND THE TREE'S OID IS NOT.** The conflict is two files
deep — **9** marker lines in `MulByNGaloisGroup.lean` and **6** in `NegYGaloisGroup.lean` — so a
bare **9** is one file's share of it and a re-runner who greps the tree gets **15**. The 15, the
9 + 6, the 0 on stdout and the 987 bytes are invariant across all five bases tried (`0b8f3d1`,
`5dba859`, `ac462ef`, `44272f7`, `871a224`) and across the order of the two arguments. **The written
tree's oid is invariant under none of it**: five bases give five oids, `diff3` and `zdiff3` give a
sixth, and swapping the arguments gives a seventh — and `diff3` moves the marker count to
**24 + 8 = 32**, because it adds a `|||||||` section. ⚠️ **So a gate line that prints an oid owes
base, conflict style and argument order beside it; one that prints the split owes nothing.**

⚠️ **And a byte count owes its capture idiom.** The raw stdout is **987** bytes; `$(…)` strips the
trailing newline and gives **986**. Both are right, and the discriminator is the shell and not
`git` — which is the same shape as the version rule one tool down.

⚠️ **THE EXIT STATUS IS NOT QUITE THE WHOLE TEST, AND THE FLAG THAT MAKES IT SO HAS A NAME.** At the
default, stdout carries `CONFLICT (content): Merge conflict in …` **twice**, so a
`grep -c '^CONFLICT'` is a second test that does discriminate. **`--no-messages` deletes exactly
that**: stdout falls from 987 bytes to **647**, the two `CONFLICT` lines to **0**, and the written
tree is unchanged. The
*marker* grep is **0** under every flag and style tried. So `#2149`'s claim is exactly right in the
form that matters — **a marker grep on stdout cannot fail** — and one flag too strong in the form
`#2149` and two landed messages (`07e7e9e`, `53c2f09`) put it: *"the exit status is the whole
test"*. The control is a clean pair: self-merge is **exit 0** with **41** bytes on stdout, the oid
and nothing else.

⚠️ **THE MESSAGE LAYER IS OUT OF SCOPE FOR REPAIR AND IN SCOPE FOR A VERDICT.** A landed message is
unamendable (`#1857`, `#2085`), so what is owed is a count, not an edit — and the count refutes the
shape of the question. **The 221 are not 221 behaviour claims.** A behaviour claim generalises; a
gate line reports one run on one tree, and *that* resolves against a blob after all, namely the tree
the commit landed. Keyed on a generalising marker, **published in full, because a seed whose word
list ends in an ellipsis is reconstructible from the page in no reading (`#2087`)**:

```text
would | cannot | never | refuses | is merely | survives | no other way | without that
| must | could not
```

⚠️ **and the scope is half the key.** Scoped to **the matched sentence** — the span between the
nearest `. ` on either side of the match in the flattened message — those ten markers return
**12 in 9**. The same ten return **2 in 2** by clause (nearest of `. `, `; `, `, `, `: `, `— `),
**47 in 25** by paragraph and **188 in 86** over whole messages. ⚠️ **The paragraph window is a
blank-line split taken BEFORE the flattening, and the order is the whole cell**: a flattened message
has no paragraphs left to split on, so flatten-first returns **188 in 86** — byte-identical to the
whole-message row beside it, which is the tell. Normalising each paragraph after the split changes
nothing (**47 in 25** under both). That is this section's own corpus rule — *"flatten AFTER, not
before"* — in a second spelling, and the reason it is restated is that the first statement of it is
scoped to the FILE corpus and this key is over messages. **A marker count is a function of its
window, so the window — and the order the window is taken in — is published with it.**

| | at `5dba859` | at `0b8f3d1` |
|---|---|---|
| matched occurrences | **218** in **114** of **758** | **221** in **115** of **759** |
| modal candidates, sentence-scoped | **12** in **9** | ⚠️ **12** in **9**, unmoved |
| generalising, hand-read | **8** in **6** | **8** in **6**, being **6** distinct claims |
| the key's false positives | **4** in **4** | **4** in **4** |

⚠️ **The candidate set is invariant across the base move although the raw count is not**: the commit
that moved `main` adds **3** matched occurrences and **0** candidates, all three of them gate lines
reporting one run on one tree. That is this section's own discriminator working on a commit that
landed after the section was drafted. The six, all re-run here:

* **`07e7e9e`** — *`--write-tree` puts markers in the written blobs, never on stdout.*
  ✅ **15 marker lines inside the written tree, 0 on stdout.**
* **`231becd`** — *under the two-argument form a `<<<<<<<` grep on stdout cannot come out any other
  way.* ✅ **0 at every base, style and argument order tried.**
* **`f3debb8`** — *a tree that has not moved must give the same written tree.* ✅ The same oid across
  three consecutive runs, at a fixed base and style.
* **`976ebf2`** — *clean against `main` neither implies nor could imply clean against every
  other head.* ✅ #471 conflicts at all three bases named above.
* **`51a55d7`** — *a failing step that is not the script's last statement does not fail the
  script.* ✅ Exit **0** without `|| exit 1`, **1** with it, **1** when the step is last.
* **`d5951f8`** — *`lake check-lint` failing is merely logged and the job stays green under
  `lint: default`, and is red under `lint: "true"`.* ⚠️ **Half measurable — see below.**

⚠️ **Nought of the six is false**, which is the answer nobody had, and the honest qualifier is on
the last: its `lake check-lint` half is measured (**exit 1** with no driver), and its
`leanprover/lean-action` half is a claim about a **third party's** `scripts/config.sh` and is **not
falsifiable in a slot** — no network, and the action is not vendored here. **A behaviour claim about
a tool this repository does not carry is a citation, not a measurement, and should be written as
one.** The **4** false positives fail in one shared way and it is worth naming: **the modal governs
something other than the matched status** — a commit-concatenation impossibility, a *claim* that
survives rather than a command, a job count that an empty diff *must* leave alone, and which
instance a `synthInstance` probe names.

**THE RULE, and it is the render gate's rule pointed at a second tool: a claim about a command's
exit status or output names the version it was taken under, and any flag that moves either.** The
asymmetry that motivates it is stark:

| pin, at `0b8f3d1` (blob `146026e`, **759** messages) | in `README.md` | in the messages |
|---|---|---|
| `markdown-it` at the patch level (`14.3.2`) | **4** | **30**, in 17 |
| any `git` version (`git 2.x`) | ⚠️ **0** | ⚠️ **0** |
| any `bash` version (`bash 5.x`, `GNU bash`) | ⚠️ **0** | ⚠️ **0** |
| `git --version` as a recipe step | ⚠️ **0** | ⚠️ **0** |

**At `0b8f3d1` this page pinned its markdown parser to the patch level in 34 places (4 + 30) —
`#2122` and `#2153` exist entirely to enforce that — and recorded the version of the tool that
produces almost every figure it publishes in none of them, nor the shell's.** ⚠️ **This section is
the commit that makes those three zeroes nonzero, and that is the rule being paid rather than an
embarrassment.** ⚠️ **It is also why the table is keyed to a sha**: a `0 / 0` cell whose whole point
is the zero is falsified by the diff that argues from it, which is `#1972` and `#2084`, and the
first round of this section was rejected for exactly that.

⚠️ **The Lean side needs no rule because a tracked file already is one**: `lean-toolchain` pins
`leanprover/lean4:v4.32.0` and `lakefile.toml` pins mathlib at `v4.32.0`, so a job count is
reproducible by construction. **`git` is pinned by nothing at all, and its output *and* its exit
status are both flag- and version-sensitive** — the oid, the byte count and the marker count above
each move under a flag this page had never named. So: run `git --version`, and print it and the
flags beside the verdict, exactly as the render gate prints `14.3.2` beside the parse.

⚠️ **AND A NARROWER CLASS, FOUND THE SAME WAY: A DELIVERABLE TRANSCRIBED FROM ITS ISSUE IS
INHERITED, NOT MEASURED.** Rounds here re-derive the *numbers* they inherit — `#2204` exists because
one round re-ran a carried census instead of carrying it — but nobody re-runs an inherited claim
about how a tool behaves, because it does not look like a figure: no denominator, no sha, no clock,
so no gate above flags it as carried. **A round owes its issue's factual claims the same instrument
it owes its own**, and the check is one line: *does any factual claim in this diff appear verbatim
in the issue description, and was it re-derived?* The confirmed row is PR #810 round 3, whose
*"exits 0, and prints nothing"* is `#2204`'s wording carried unrun — every other figure in that
round was re-derived from the tree, and the only wrong one is the one quoted from the filing.

⚠️ **A LAST SUB-CLASS, AND IT IS NARROWER THAN `#2037`: A COORDINATE CERTIFIED AS *INVARIANT* HAS
NOT BEEN CERTIFIED AS *TRUE*.** The first round of this section carried one line number, checked it
against the only predicate a self-figure gate knows — *does this insertion move it?* — recorded that
the file is one the diff does not touch, and published a number that pointed at neither end of its
own quotation. **The two predicates are different, and a gate that runs one owes which one.**

⚠️⚠️ **AND A SUB-CLASS THAT IS NEITHER A WRONG STATUS NOR A CARRIED CLAIM: A PROBE WHOSE OUTPUT
DOES NOT CONTAIN THE THING THE CLAIM IS ABOUT.** Everything above fails loudly — a wrong exit code,
a count that moves under an unnamed flag, a sentence quoted unrun. ⚠️ **These two fail SILENTLY:
the command runs, exits 0, prints something true, and says nothing about the question asked of
it.** The class is `#2308`, filed out of `#2305` round 1, where each of the two produced a
published-and-wrong `must` **in opposite directions within four hours** — one charge replaced a
true clause with a false one, one review endorsed a false mechanism, and in both the instrument was
clean.

**`#check` prints a type's REMAINDER, not its type, so it cannot settle *"X does not occur in the
type"*.** An instance binder that the printed remainder never mentions again can still sit inside
the type, reached through another instance's arguments. The witness is one declaration,
`WeierstrassCurve.Affine.torsion`, and no section is needed:
`#check @WeierstrassCurve.Affine.torsion` ends
`[inst_1 : DecidableEq F] → (W : WeierstrassCurve.Affine F) → ℕ → AddSubgroup W.Point`, whose
remainder names neither `inst` nor `inst_1`. ⚠️ **`set_option pp.explicit true` is the probe, and
the same declaration reads:**

```text
@WeierstrassCurve.Affine.torsion : … [inst_1 : DecidableEq F] → (W) → Nat →
  @AddSubgroup (@WeierstrassCurve.Affine.Point F (@Field.toCommRing F inst) W)
    (@AddCommGroup.toAddGroup (@WeierstrassCurve.Affine.Point F (@Field.toCommRing F inst) W)
      (@WeierstrassCurve.Affine.Point.instAddCommGroup F inst W inst_1))
```

⚠️⚠️ **`inst_1` IS the `[DecidableEq F]`, and it is an argument of `Point.instAddCommGroup` inside
the result type** — so `AddSubgroup W.Point` is a remainder that suppresses it rather than a type
that lacks it. ⚠️ **`linter.unusedDecidableInType` keys on the type, exactly as its own message
says** (*"does not use the following hypothesis **in its type**"*), **so where the two disagree
about a declaration the linter is right and the printed remainder is not evidence.** The control is
a pair with identical empty proofs:

```text
set_option linter.unusedDecidableInType true
variable [DecidableEq F] [W.IsElliptic]
theorem tstE {n : ℕ} : Nat.card (W.torsion n) = Nat.card (W.torsion n) := rfl   -- SILENT
theorem tstF {n : ℕ} : (W.preΨ (n : ℤ)) = (W.preΨ (n : ℤ)) := rfl               -- FIRES
```

**`rfl` on both, opposite verdicts, only the statement differs** — and `linter.unusedSectionVars`
corroborates from the other side at the same two declarations, flagging `[W.IsElliptic]` alone on
`tstE` and **both** binders on `tstF`. ⚠️ **Proof use is an ADDITIONAL route to silence — a proof
term's dependence makes the instance reachable — and it does not displace the type criterion.**

**`omit X in` before a `def` is a TOTAL no-op, so `omit`-and-build is not a test of
load-bearingness there.** On `Torsion/OddTorsionCount`'s `torsionOddEquiv`, whose own docstring
block carries this finding at the declaration that caused it, inserting `omit [IsAlgClosed F] in`
and rebuilding the module leaves `#check` and a binder-name walk over `ConstantInfo.type`
**byte-for-byte identical — `diff` empty, `cmp` clean, 737 bytes both ways** — hygienic suffixes
included. ⚠️ **It is not a name removed and anonymously re-added; nothing happens at all.** That
section's `variable` line is three *anonymous* instance binders, so there was never a name for
`omit` to take, and the asymmetry a reader sees — one instance printed with a name beside one
without — is already in the unmodified file, the printer naming only binders the rest of the type
mentions. ⚠️⚠️ **So a clean build after an `omit` on a `def` is a FALSE GREEN and not a result**,
and `#check` alone cannot separate *kept* from *re-added*. The binder walk can, and it says neither
happened:

```text
open Lean Elab Command in
run_cmd do
  let some ci := (← getEnv).find? `WeierstrassCurve.Affine.torsionOddEquiv | throwError "missing"
  let mut t := ci.type; let mut names := #[]
  while t.isForall do names := names.push (toString t.bindingName!); t := t.bindingBody!
  logInfo m!"{names}"
```

**The sound half of the pair is the THEOREM case and it must be kept**: the same line before
`torsionOddOfRoot_bijective`, which references the variable, answers
`error: cannot omit referenced section variable` with the hygienic name in **backticks** and not in
`'…'`. ⚠️ **And the `omit` goes BEFORE the doc comment** — after it the answer is
`error: unexpected token 'omit'; expected 'lemma'`, a parse error that is easy to read as a result
and is not one.

⚠️ **Both facts were re-run for this paragraph rather than carried from `#2308`**, which is this
section's own inherited-claim rule falling due on the clause that states it, at `git 2.39.5`,
`bash 5.2.15(1)-release`, `python3` 3.11.2 and `leanprover/lean4:v4.32.0` (`lean-toolchain` blob
`94b9f495`, `lake-manifest.json` blob `e2a21bd4`, `lakefile.toml` blob `dadf0ad`). ⚠️⚠️ **The flags
are named because the rule above requires it, and the asymmetry between the two is itself the
finding**: the first reading moves under `pp.explicit` and under `linter.unusedDecidableInType`,
which `lakefile.toml`'s `weak.linter.mathlibStandardSet` does not turn on; **the `omit` reading
moves under no flag at all, which is exactly why it misleads** — there is nothing to set
differently and the answer is still not about the question. ⚠️ **The snippets above are fenced
`text` and not `lean` because this file has never carried a `lean` fence**, and this section's own
two fences are `text`.

### The merge gate's base

`### The neighbour population`, below, decides which pull requests the merge gate is run
**over**, and says in terms that it does not decide what the gate's output means.  This section
is about the gate's other end — the base it is keyed to, and how a round knows that the landing
it has been waiting for has happened.  ⚠️ **Each of the three rules below was paid for by a
published figure that was wrong**, and the worked cases are kept because every one of those
figures looked sound when it was published.

**A gate paid at a base `main` has left is not a gate.**  `#2258` names the one case in which the
build need not be re-run, and ⚠️ **its precondition is a statement about the SYMMETRIC DIFFERENCE
and not about the branch**: if `git diff --name-only <old merged tree> <new merged tree>` carries
no `.lean` row, then the merged tree's Lean content is byte-identical to a tree already built
green, and `EXIT 0` follows by construction rather than by running anything.  ⚠️ **Both commands
in that precondition are `git 2.39.5`'s** — the `diff --name-only` and the `merge-tree` that
wrote the two trees — and ⚠️ **the `EXIT 0` itself is INHERITED rather than measured**: it is
the earlier build's status under the tracked `lean-toolchain`, which is what *by construction*
means here and why no version is named for it beyond that file.  ⚠️ **Difference the
two trees; do not read the precondition off the branch's own shape.**  A branch that edits only
`README.md` can still fail it, and ⚠️ **a SINGLE commit of base movement can carry it away**: one
landing past `d8fde75`, the two merged trees of PR #819 differ at five paths, **four of them
`.lean`** — `EllipticCurves.lean`, `Fixtures.lean`, `ThreeTorsionSplitCertificate.lean` and
`ThreeTorsionStructure.lean` — so a build published against `d8fde75` eleven minutes earlier was
void, and its `3755` jobs were a figure about a merge that could no longer happen.

⚠️ **`git fetch` is not a read, and the base is the one field a round must not take from a local
ref.**  In a working clone of this repository `git fetch upstream` has been observed to return
success **without advancing `refs/remotes/upstream/main`**: `main` had been `6733352` since
`2026-09-29T14:19:26Z`, and `git log -1 upstream/main` still answered `d8fde75` after the fetch.
The clone prints `warning: There are too many unreachable loose objects` and carries a
`.git/gc.log`; ⚠️ **the cause is not diagnosed here, and it is the observable and not a diagnosis
that this rule is written against.**  **Take the base from
`git ls-remote upstream refs/heads/main`**, or difference the local ref against it, before any
figure is keyed to it —
⚠️ **and a round whose sign-off reads *"every ref from `git ls-remote upstream`"*, which is the
form this board writes, is asserting that of the base too.**  The cross-check costs nothing and
was available in the minute the error was made: ⚠️ **a `mergedAt` that a round prints and a base
that predates it cannot both be right.**

⚠️ **A sha change on `main` is not evidence that your own branch landed.**
`git merge-base --is-ancestor` is already ruled out one section below, because the merger
squashes; ⚠️ **"the sha
moved" fails for a second and independent reason — the sha you are comparing it against can itself
be stale**, and then the movement recorded is an older landing surfacing in a live read for the
first time.  A bid placed at `14:32:5xZ` appeared to be served **28 seconds** later and was not:
the landing was `#789`'s, fourteen minutes old, and a *sub-minute service latency* was one step
from being published off it.  **Compare the landed tree against the tree your own gate certified**
— `git rev-parse upstream/main^{tree}` — **or read `gh pr view <n> --json state,mergedAt`.**  A
squash cannot fool a tree.

**What the merger does with a bid is not known here, and this section does not guess.**  What is
recorded is that the latency is bimodal and that nothing found so far separates the two modes.  At
`2026-09-29T14:2xZ` six certified pull requests — #819, #831, #834, #835, #844 and #845 — were
simultaneously unlanded between **1.5 and 20 hours** after their approvals, ⚠️ **all six
`git merge-tree --write-tree` exit 0 against live `main`, at `git 2.39.5`** and all six green in
CI, while the three
landings at `13:24:27Z`, `13:37:00Z` and `14:19:26Z` each followed their approval within minutes.
⚠️ **Conflict, CI, size and behind-ness are each ruled out by measurement** — #789 landed at
**3 behind** while #844, `0 behind` at its own approval, did not — ⚠️ **and so is the arrival of
newer bids, which is the reading that looks likeliest and is false**: #819's bid of `07:01:32Z`
was the only one outstanding for at least 42 minutes, and `main` did not move at all for
**5 h 06 min** after it.  ⚠️ **Three controlled trials have each failed to yield a mechanism, so
none is written down here.  A round that finds the separator keys to `#2270` rather than
re-deriving this**, and a round that is merely waiting should record the clock and spend nothing.

⚠️ **And the rule of prose that all of this was found through: a count that carries an argument
gets counted.**  The paragraph above was first drafted as *"nine or ten landings"* where the answer
is **four**, and that numeral was not decoration — it was the entire case for the mechanism the
corrected count then ruled out.  *"Roughly a dozen"*, *"six hours of traffic"* and *"most of them"*
read as scene-setting and function as evidence.  ⚠️ **If a numeral bears weight it is `git log`-ed
at a named ref, or it is not published** — and the first `#2270` comment to correct an instrument
was worth less than the second, which corrected a figure nobody had measured at all.

⚠️⚠️ **THE SQUASH MESSAGE IS BYTE-CAPPED AND THE CUT IS A PREFIX CUT: WHAT DOES NOT LAND IS THE
TAIL.**  ⇒ ⚠️⚠️ **WHICH REGIONS ARE LOST IS THEREFORE A FACT ABOUT THE BRANCH'S OWN LAYOUT AND NOT
ABOUT THE MERGER, AND THIS BOARD RUNS BOTH LAYOUTS.**  On a newest-FIRST `%B` the tail is the
OLDEST regions, which is the worked case below.  ⛔ **On a newest-LAST `%B` the tail is the round's
OWN region**: the object `09fbee41b48936a709f4f6abe241aea0b63b4d4e` carries `===` section headers
at `:3`, `:52` and `:184` in INCREASING round order and **64630** bytes of `%B` against the
**65542** below, so the first text its cap would take is its newest round's.  ⚠️ **A 40-hex object
is named rather than a branch, because a tip moves under review and an object does not.**  `#2348`
round 8 is the worked case.  The branch head
`56f379f684697c8ab00de4d492634a0616f6b36e` carries **102129** bytes over **99549** codepoints in
**nine** blank-line regions; its landing `a4bb7a1667f9fac2cca54614d1179afdc7f3c826` carries
**65591** bytes over **63974** codepoints in **seven**.  Round 8's own region landed verbatim — as
**6449** codepoints against **6442**, the subject gaining ` (#945)` — and so did rounds 7, 6, 5 and
4's, at **5826**, **7223**, **11336** and **15773**; round 3's is **TRUNCATED at 17311 of 22607**,
mid-word; and round 2's two regions and round 1's are **ABSENT**.  ⚠️ **The overflow is replaced by
one `U+2026` and the `Co-authored-by:` trailer is appended BELOW the cut**, so the landed message
ends in an ellipsis and then a trailer and reads as complete.

⚠️ **The instrument, because these lengths are convention-sensitive.**  Take the message from
`git cat-file commit <sha>` after its first blank line, split the regions on a blank line, and read
codepoints with `len()` on the decoded string and bytes with `len()` on the raw.  ⛔ **Never
`git log --format=%B` for a length** — it supplies a trailing newline the stored object may not
carry, which `#2348` round 8 settled at the object layer.  ⚠️⚠️ **And strip the trailing newline
from BOTH ends before splitting, or the FINAL region alone reads one codepoint long**: round 1's
region on that branch is **13522** stripped and **13523** under a bare split, and the
entirely-dropped total inherits it at **30325** against **30326**.  **Both endpoints are published
because a figure whose two conventions differ by one is unreadable without its convention
(`#1749`).**

⚠️⚠️ **THE CAP IS A BYTE CAP, AND TWO LANDINGS PIN THE UNIT WHERE ONE COULD NOT.**  `a4bb7a16` and
`0ed9e02b7a5002fc0e0129be8b55942a16dd8f20` — a different branch, landed `2026-10-06T10:01:44Z` —
carry bodies of **65545** bytes each, ellipsis included, over **65542** bytes of surviving text,
while their codepoints are **63928** and **64104** ⇒ **the quantity that agrees across the two is
the byte count and the quantity that disagrees is the codepoint count.**  ⚠️ **The trailer is
outside the cap**: those two messages total **65591** and **65584** bytes because their trailers
are **44** and **37**, under bodies that are byte-equal.  ⛔ **`65536` is NOT the figure and is not
written here as one**: the surviving text is `65542` bytes at both points, six over it, and two
points do not pin whether the merger counts the subject line, the ` (#NNN)` it appends — **7**
bytes at both, so that cell cannot discriminate — or something else.  ⚠️ **The control at the other
end is `87c2072bdba9541f69ef728db61f49eba5b6bc07`, whose body landed with no truncation ellipsis at
**64789** bytes** — ⚠️ **under the trailer-BLOCK convention the pair above uses; a cut at the last
`Co-authored-by:` line alone reads **64835**, because that control's trailer block is TWO lines and
**98** bytes.  Both endpoints are published with the convention named, as above (`#1749`).**  ⇒ the
boundary lies between the larger of those and `65542`, and nothing here narrows it further.
⛔ **No cardinality of the truncated population is published** (`## Import-closure figures`): the
two above are named, and a third landing past the cap would move a count written here.

⚠️⚠️ **A LANDING KEY MUST SIT INSIDE THE CAP — which is the round's own region only when the round
PREPENDS, and is measurable in either layout as the key's byte offset in the message.**  ✅ **The
worked case demonstrates that rule rather than the luck it was first read as.**  `ROUND 4 REPAIR`
is still `grep -qF`-reachable
on `main`, and the cut did fall six words past its last surviving occurrence, the tail reading
`ROUND 4 REPAIR: *NOBODY HAS TESTED ONE FIGURE I…`.  ⛔ **But that is not why it survives.**  The
branch spreads that string **1** in round 4's own region against **10** in round 3's, and the
landing keeps **1** and **7** ⇒ **the single occurrence in the round's own region lands whatever
the cut does, and a membership test over the whole message succeeds if ANY occurrence survives**,
so the cut's position is immaterial once the key is inside the cap.  ✅ **The control is in the same
pair of objects: `ROUND 8 REPAIR` sits twice in round 8's own region and twice on `main`.**
⛔ **What the cap CAN take is a key every occurrence of which lies PAST the cap** — the oldest
regions on a newest-first `%B`, the newest on a newest-last one — then
`git log -1 --format=%B <sha> | grep -qF '<key>'` FAILS on `main` for a round that landed, which is
a false negative on the certificate this board writes in nearly every delivery comment.

⚠️ **And the grading rule takes a scope rather than a retirement.**  *"A false figure in the `%B`
lands, and landed text is permanent"* is why `%B` cells are graded harder than comment cells and
why a multi-round branch protects its earlier regions byte-identically.  ⛔ **It holds only of text
inside the cap**: round 1's region on `#2348` was protected byte-identically for three rounds and
reaches `main` not at all.  ✅ **The protection discipline is unweakened by that** — it is a claim
about the object a reviewer reads and re-derives figures from, which is the branch head and not the
squash — ⚠️ **but a round that grades a cell by *it lands, therefore it is permanent* owes the byte
reading of its own message first, and a round whose `%B` is approaching this scale should read the
byte offset of its own landing key rather than trust its region.**

### The neighbour population

A round in review publishes a **merge gate**: `git merge-tree` against `main`, and against the
other pull requests that are open at the same time, to show that the branch is not about to collide
with one of them **in any hunk**.  ⚠️⚠️ **That last clause is the scope, and it is narrow: exit
`0` there is a claim about TEXT and says nothing about whether the merged tree elaborates**, which
is what the clause and the sweep below this paragraph are about.  ⚠️ **The right-hand ends of that
gate are other branches, which makes it the one gate here whose POPULATION drifts as well as its
values.**  Every other **gate** a round publishes
is a function of `(tree, base)` and moves only when one of those moves; this one moves when
somebody else opens or lands a pull request, with no edit to either side.  ⚠️ **Not every
*figure*, and the wider claim is false in this file**: a count whose population is this board's own
record drifts the same way and is not a gate — `### Scope of the rules above` publishes a
conviction count whose own sentence says *"its population is this board's review threads, and no
seed on this page can open one"* (`#1969`).  **What is peculiar to this gate is that
its right-hand ends are other branches**, not that nothing else drifts.  **This section decides
which pull requests the gate is run over.  It does not decide what the gate's output means.**

⚠️⚠️ **WHAT THE GATE DOES NOT SHOW, AND IT IS NOT AN EDGE CASE.**  `merge-tree` exit `0` says the
two branches have no **textual** conflict; it says nothing whatever about whether the merged tree
**elaborates**.  ⚠️ **The mechanism needs no pathological input: two branches that add the SAME
declarations in DIFFERENTLY-NAMED files conflict in no hunk at all** — neither side touches a line
the other side touches, so a three-way merge has nothing to disagree about, and the two `mk_all`
insertions into `EllipticCurves.lean` land at different lines and merge cleanly as well.
⚠️ **This is not the reserved question of the paragraph above.**  That one is what a given output
*means* — item 3 below is where a conflict is read as a fact about one branch rather than the other
— and this is what exit `0` does not *cover*, a boundary on the gate's reach, which is what
licenses a second instrument instead of a re-reading of the first.  ⚠️ Run `### Reach clauses`'
*"false or merely partial"* test on the opening sentence and the answer is **partial** — the words
stay and a scope is added — so it takes the qualification in place that it now carries and
`### Retired claims` does not bind.

⚠️⚠️ **THE WORKED CASE PASSED THE GATE IN BOTH DIRECTIONS, WAS MISSED BY THE TWO-DIRECTION
NEIGHBOUR SWEEP, AND DOES NOT ELABORATE.**  PR #937 (head `6ae2b3f5`,
for `#2296`) and PR #932 (head `db54badc`, for `#2341`) each add one new module —
`EllipticCurves/Torsion/NthPartTower.lean` at **680** lines and
`EllipticCurves/Torsion/NthPartGaloisTower.lean` at **849** — and of their public declaration
names **36 are identical, every one in namespace `WeierstrassCurve.Affine`**, out of **44** public
in #937 and **42** in #932, among them `nthPartX`, `nthPartXField`, `nthPartTower`,
`nthPartGaloisField`, `instIsScalarTowerNthPartTower` and `nDivisionFieldToNthPartGalois`.

* ⚠️ `git merge-tree --write-tree` between the two heads exits **0 in BOTH directions** and writes
  `503bd5f4bd3c4957398d7c2918e7f1e157f9df3d` in both, at **`git 2.39.5`**.
* ⚠️⚠️ **`lake build` on that merged tree exits 1, and the reading is one line** — at
  **Lake 5.0.0-src+8c9756b / Lean 4.32.0**, `commit-tree` over the written tree and
  `lake build EllipticCurves`, the log line folded here at this page's column cap and nowhere
  else:

  ```text
  error: EllipticCurves.lean:1:0: import EllipticCurves.Torsion.NthPartTower failed,
      environment already contains 'WeierstrassCurve.Affine.nthPartYPoly'
      from EllipticCurves.Torsion.NthPartGaloisTower
  ```

* ⚠️⚠️ **AND 3787 OF THE 3789 JOBS SUCCEED, INCLUDING BOTH NEW MODULES.**  Neither imports the
  other, so each elaborates alone; the only job that fails is the `mk_all` root `EllipticCurves`,
  which is the one file that imports both.  **A build restricted to the modules a branch touches is
  green on this defect**, and so is every per-branch gate this board runs.
* ⚠️ **The error names ONE of the 36 and stops.**  `import` aborts at the first collision, so the
  message under-reports the overlap by **35** and the count has to come from the name sets.
* ⚠️⚠️ **AND THE TWO-DIRECTION NEIGHBOUR SWEEP MISSES IT TOO, RE-DERIVED HERE AND NOT TAKEN FROM
  THE ROUND THAT FIRST RAN IT.**  Over the open pull requests less #937 itself at
  `2026-10-06T10:0xZ`, the set conflicting with bare `main` has **20** members and the set
  conflicting with PR #937 has those **20** plus **#931** — so the branch-caused set is exactly
  `{931}`, whose conflict is the benign `EllipticCurves.lean` add/add, and **#932, the real
  collision, is in neither.**  The gate's one discriminating output named the harmless branch and
  missed the fatal one.  ⚠️ **What found the duplicate was reading the other branch's `--numstat`
  path list**, which until this clause no rule on this page asked for.

⚠️⚠️ **THE SWEEP THAT SEES IT IS A NAME SWEEP AND NOT A PATH SWEEP, AND THE PATH LIST IS ONLY ITS
CHEAP FILTER.**  Over the population this section already decides, and with the leading `+` the
fetch paragraph below makes load-bearing:

```sh
git --version                            # every figure above is at 2.39.5
for n in $(gh pr list --state open --limit 300 --json number -q '.[].number'); do
  git fetch -q upstream "+refs/pull/$n/head:refs/remotes/pr/$n"
  git diff --name-only "$(git merge-base refs/remotes/pr/$n upstream/main)" "refs/remotes/pr/$n"
done                                     # the PATH filter: who else is in this subtree at all
# then, for every branch that filter keeps, the ANSWER, in both directions:
comm -12 <(names theirs.lean | sort) <(names mine.lean | sort)   # the collision set
comm -23 <(names theirs.lean | sort) <(names mine.lean | sort)   # theirs only
comm -13 <(names theirs.lean | sort) <(names mine.lean | sort)   # mine only
```

⚠️⚠️ **AND `names` OWES ITS OWN DEFINITION**, which is `### Tool-behaviour claims`' rule falling
due on a recogniser rather than on a tool.  The one every figure above is taken under:

* a **nesting-aware** comment strip — `/-` … `-/` nest, which covers `/--` and `/-!` both, `--`
  runs to end of line, and both forms are suppressed inside `"…"` with `\` escapes;
* a declaration is a stripped line beginning **at column 0** with zero or more of `@[…]`,
  `private`, `protected`, `noncomputable`, `partial`, `unsafe`, `nonrec`, `scoped` or `local`,
  then one of `theorem`, `lemma`, `def`, `abbrev`, `instance`, `structure`, `class`, `inductive`,
  `opaque`, `axiom`, `example`;
* the **name** is the next token up to the first whitespace or one of `:(){}[]⦃⦄⟨⟩`, prefixed by
  the `namespace` stack — maintained over `namespace X` and `end X`, with `section` and a bare
  `end` leaving it alone — and an `instance` or `example` carrying no name contributes none;
* **public** is `private` absent from those modifiers.

⚠️ **A bare `grep -c '^theorem'` is not a substitute and the gap is not marginal**: over the two
files above it reads **31** and **30** against this recogniser's **44** and **42**, so it misses
**13** of the first file's public declarations and **12** of the second's — every
`noncomputable def`, every `noncomputable abbrev` and the one named `instance` in each.
⚠️ **`#2337` round 3 banked the neighbouring trap** — four of seventeen `lake` jobs are bare
identifiers, and a classifier keyed on punctuation mis-sorts exactly those four while its own sum
invariant still balances.  **A recogniser that owes no definition is a count nobody can re-run.**

⚠️⚠️ **AND THE CLOCK IS *BEFORE CLAIMING*, NOT BEFORE PUSHING.**  Those are different clocks and
only the first is cheap: the worked case's author did sweep before pushing, correctly, and it was
already too late, the 680 lines being written.  ⚠️ **An attached pull request cannot be withdrawn
by an agent** — `gh pr close` is barred by `orchestra-pull-requests`, there is no MCP substitute,
and `attach_pr` has no inverse — so a duplicate put in front of a reviewer **stays** there until a
human closes it.  That is `#2299`'s wall at a new layer, and it is the whole argument for the
earlier clock.  ⚠️ **This is not a fifth member of the four-item list below, and for a different
reason from the fetch clause's**: those four are what a merge bullet says at REVIEW time, and this
one is run by the AUTHOR before the claim, so a round that first publishes it in a merge bullet has
already paid for it in full.

⚠️⚠️ **AND THE CHEAPEST CHECK IS NOT A SWEEP AT ALL: A ROW WHOSE PARENT OR CHILD CARRIES AN
UNMERGED PULL REQUEST IS NOT AN OPEN ROW.**  `#2341` is `parent=2296`, it sat in the review queue
in the same listing that showed `#2296` open, and it named PR #932 in its own title — three
readings of one listing, any one of which was enough.  **Read the tree of the row before the tree
of the repository**, and only then sweep.

⚠️ **On a prose branch the name sweep is vacuous and the path filter has no discriminating power at
all, so the unit is the SECTION.**  At `2026-10-06T10:06:07Z` there are **47** open pull requests —
**48** half an hour earlier, the one departure being PR #934 by *landing* and the entering set
EMPTY, which is the shape item 4 below asks for — and **25** of the 47 touch `README.md`, which is
exactly what makes a path list useless here.  Mapping each one's hunks to the enclosing heading
**in its own base** puts **two** of them in this very section, PR #809 and PR #810, and PR #802 in
`## Reviewing`.  ⚠️ **Neither of the two is branch-caused against the head that publishes this**:
#809 merges with it at exit **0 in both directions**, and #810 conflicts with bare `main` itself
and so is excluded by item 3's own control.  **A shared section is a thing the merge gate cannot
see, not a restatement of what it already says.**  ⚠️ **And the heading recogniser owes a flag of
its own — it must be FENCE-AWARE**, or a `#` comment inside a fenced block is read as a heading.
That flag is a **no-op** over the 25 above and is **not** one on PR #934, where the naive form
answers a `# the worked case's two heads …` comment line in place of `## Reviewing`; ⚠️ that pull
request has since landed, and `refs/pull/934/head` is what keeps the case re-runnable from a
closed population.  **The same instrument at the layer this file is written in, and as cheap.**

⚠️ **The word the messages use for that population is used on this page for something else.**
The stem occurs **12** times in this file at `ac462ef` — whitespace-flattened, keyed
`[Nn]eighbour[a-z]*`, and unmoved at `871a224`, which does not touch this file — and it carries
**two** senses here, neither of them a pull request:

* **9 occurrences, on 9 lines: an adjacent unit of text** — a clause, row, bullet, list, section or
  declaration, as in *"leaves its neighbour partial"* and *"its neighbour of the same shape"*.
* **3 occurrences, on 2 lines: a fixed-width character window.**  This is `neighbourhood`, and
  `### Gate-discharge claims` defines it *against* the first sense in terms — *"A 180-character
  window is not the words but the neighbourhood"* — so collecting it under *adjacent* contradicts
  the page.
* **0 occurrences: a pull request.**

⚠️ **Count occurrences or count lines, and say which**: the same twelve are `9 / 3` by occurrence
and `9 / 2` by line, because one sentence carries `neighbourhood` twice.  ⚠️ **And say which SITES,
because in two ratios a unit disagreement and a missed one look the same.**  Two reviews of the
round that wrote this paragraph returned `9 / 3` and `10 / 2`, and the second is not the first
taken by line: their window buckets are lines `2237` and `2242` twice against line `2242` twice, at
`ac462ef`, so the two read different twelves and `10` is the second's count of what it filed as
adjacent — one of them a window occurrence.  The site that separates them is `2237`,
*"the clause's own span, or the source line carrying it, and never a fixed-width neighbourhood of
it"*, and ⚠️ **the first of the two reviews had already printed both of its window sites with their
quotations while the second printed neither**, so the ratios were reconstructed with a bucket list
already sitting in the thread they were reconstructed from.  **A sense census owes its unit
exactly as a seed owes its flags, and it owes its sites for the same reason**: printed as lines
`1151`, `1432`, `1860`, `2741`, `2744`, `2793`, `2816`, `3031` and `3791` against `2237` and
`2242`, all at `ac462ef`, the gap is one `comm` rather than a reconstruction of somebody's
arithmetic — which is what the two ratios forced, and it got the mechanism wrong.
⚠️ **This section is inside its own population, so the figure is resolved at both ends** (`#1972`)
— ⚠️ **and it is published as a DELTA, because the right-hand end is decided by the merger's queue
and not by this branch**: the stem returns **12** on **11** lines at `ac462ef`, and this section
adds **10** occurrences on **9** lines, **2** of them its own `NEIGHBOURS`, quoted from the two
messages that make the case-insensitive key load-bearing.  ⚠️ **Three open pull requests add the
stem to this file** — one, three and two occurrences — so an endpoint pair is true only if this
branch lands next, while `+10 on +9` is what all four landing orders return.  That is
`### The render gate`'s *"Publish the delta and not the endpoints"* one section below, applied to a
population figure rather than to a token count.  ⚠️ **The delta is a self-figure too, and repairing
the paragraph above moved it**: quoting the site that separates the two window buckets put one more
instance of the stem on this page, so the round that retired the endpoint moved the delta it
replaced it with, by one.  **A count of a page by that page is re-derived at the head that
publishes it, every round, or it is stale by construction.**

On `main` the same stem splits the other way round: **15 occurrences in 7** messages are the
pull-request sense and **30 in 25** are the docstring sense — **45 in 32** together, out of
**745** messages at `871a224` (**743** at `ac462ef`, with the same 45 in 32).  ⚠️ **That seed is
case-INSENSITIVE and this page has to say so**: `c28c462` and `dba89ee` write `NEIGHBOURS` in
capitals, a `[Nn]`-keyed grep returns **43 in 30**, and both messages it drops are inside the
**seven** the pull-request sense is counted over — so the flag is load-bearing for the split and
not incidental to it.  So a reader who meets *"every neighbour"* in a merge bullet and looks the
word up here does not find it undefined — they find **two different** senses of it, which is worse.
**Write *open pull requests*, and use *neighbour* only after saying which one is meant.**

**The population is a three-way partition of the pull refs, and two of the three parts are decided
by one command each.**  `git ls-remote upstream 'refs/pull/*/head'` answers for every pull request
this repository has ever had — **796** at 2026-09-22T12:33:09Z — and ⚠️ **a `head` ref is frozen at
the pull request's last head and outlives the pull request**, so it answers just as readily for one
that landed a week ago.  It decides nothing.  These two do:

* ⚠️ **`refs/pull/<n>/merge` is advertised only while the pull request is OPEN**, and is deleted the
  moment it merges or closes.  **35** at 12:33:09Z, and the key is **sound**: #757, #764, #770,
  #790 and #793 have all landed and not one of the five is advertised.
* ⚠️ **A pull request has landed iff its number is the TRAILING `(#N)` of a subject on `main`** —
  the merger writes `(#issue) (#pr)` and the pull number is last, so the trailing position is what
  separates the two.  **742** distinct numbers over `main`'s **743** subjects at `ac462ef` (exactly
  one subject carries no trailing `(#N)`), with **0** of the open set among them.  ⚠️ **`git
  merge-base --is-ancestor` is not this test and cannot be made into one**: the merger squashes, so
  a landed head is an ancestor of nothing and the ancestry test reads *live* at all 742.
  ⚠️ **The key is checked in BOTH directions against an oracle, not only in the direction the
  partition needs**: at 15:30:49Z the trailing-subject key returns **744** numbers and
  `gh pr list --state merged --limit 2000 --json number` returns **744**, and the two sets are
  identical — `comm -13` and `comm -23` are both empty — with every one of the 744 also carrying a
  head ref.  An *iff* asserted in one direction is a rule; checked in both it is a measurement.

The two keys are **disjoint** — no number satisfies both — and together they account for **777** of
the 796:

```text
796 head refs  =  35 open (merge ref)  +  742 landed (trailing subject)  +  19 residue   @ 12:33:09Z
800 head refs  =  37 open (merge ref)  +  744 landed (trailing subject)  +  19 residue   @ 15:30:49Z
```

⚠️ **AND THE RESIDUE IS NOT EMPTY, SO THE MERGE REF IS A LOWER BOUND AND NOT THE OPEN SET.**  At
12:33:09Z this repository has **36** open pull requests against **35** merge refs.  The missing one
is **PR #471**, open since 2026-08-30: `refs/pull/471/head` resolves, to
`6327391e25667aebb7cfec4b5f5b9d970b9e28c4`, and `refs/pull/471/merge` does not exist.  ⚠️ **Do not
write GitHub's `mergeable` field down as the reason.**  It is a cache invalidated whenever the base
moves, and for this pull request it read `UNKNOWN` at 12:33:09Z, **`CONFLICTING`** at 15:01:10Z and
`UNKNOWN` again at 15:25:20Z, with the pull request itself untouched across all three.  The two
durable facts are that the ref is absent at every one of those clocks and that
`git merge-tree --write-tree <main> 6327391e` exits **1** against `ac462ef`, `44272f7` and
`871a224` alike, at `git 2.39.5` — which is item 3's control, and it needs no server-side field
at all. ⚠️ **That status is also the one cell of this reading invariant under every flag and
style `### Tool-behaviour claims` measured**: `--no-messages` empties the two `CONFLICT` lines
from stdout and `merge.conflictStyle` moves the written tree's oid, and neither moves the **1**.
The other
**18** of the residue are pull requests closed without merging.
**So a sweep keyed on merge refs is short, and being short is the failure a total on the left of
*of N* cannot show** — the same numeral reads identically whether the world had 35 members or the
sweeper found 35 of 36.  **Publish the residue's size beside the count.**

⚠️⚠️ **AND THE POPULATION IS NAMES WHILE THE GATE NEEDS OBJECTS — the step between them is a fetch,
and it is where the head you swept stops being the head you named.**  `ls-remote` answers in refs
and `merge-tree` takes commits, so a sweep resolves every head into the local repository first, and
⚠️ **on the branches this board rebuilds a non-forced refspec is REFUSED there rather than obeyed.**
A plain `git fetch upstream refs/pull/<n>/head:refs/remotes/pr/<n>` permits a fast-forward only;
a branch rebuilt by `--amend` or by `commit-tree` has a head that is not a descendant of its
predecessor, so the update is declined, **the local ref goes on serving the superseded commit**,
and the gate then runs to completion against a commit the pull request no longer has.  ⚠️⚠️ **The
predicate is one this page already publishes under another name**: the fetch is refused **iff**
`git merge-base --is-ancestor <the stored local ref> <the live head>` exits **1**, which is the
signature of the amend regime itself — so a branch whose rounds are reported as *not ancestors of
one another* is exactly a branch whose pull ref will not fetch, and the two facts are one fact.
**Write the `+`** — `+refs/pull/<n>/head:refs/remotes/pr/<n>`, or `--force` — **and check the refs
you resolved against ONE `ls-remote` advertisement pass**, which is the instrument this section
already prescribes for the population and which costs one command for the whole board, rather than a
per-request `headRefOid` read that costs one for each member of it.

⚠️ **That is a behaviour claim, so it names its version and its flag** —
`### Tool-behaviour claims`' rule, stated two sections above this one, falling due here: at
**`git 2.39.5`** the refused fetch prints `! [rejected]` with `(non-fast-forward)` against the
refspec and **exits 1** with the ref unmoved, and the flag that moves both is the leading `+` or
`--force`, and with it the fetch prints `(forced update)` and exits **0**.  ⚠️⚠️ **It is NOT silent,
and this clause discovers nothing: the mechanism has been right in the record since 2026-09-29.**
`#2272` round 1 stated it first, in a delivery comment — the rejection **printed**, the local ref
**left in place**, the leading `+` as the repair — and two landed commit bodies carried it the same
day, `2958f49` crediting that row and `5d81349` quoting the rejection line itself, which no other
landed body reachable from this branch's base does.  ⚠️ **What no SECTION carried is the step, and
that placement is the whole of this clause**: the paragraph that decides which pull requests the
gate runs over never named the fetch, so every sweep rediscovered it from a commit message.
**The one wording corrected here is a LATER one** — a review thread four days on called the
rejection silent — **and it resolves in no blob, so nothing is retired anywhere.**
⚠️⚠️ **The defence is the status, and what it has to survive is whatever `git` prints after the
rejection line.**  Nothing is concealed by `git`; what conceals it is that trailing output read
through a `tail` — and ⚠️ **that needs no misconfigured checkout, because a sweep fetches every head
in ONE `git fetch` and the rejection is one line among whatever that fetch had to say.**  ⚠️⚠️ **But
what it has to say is clone state and not fetch behaviour, so neither a count nor a position here is
a fact about the fetch**: a refspec whose ref CHANGES prints a line and one already current prints
none — with nothing to report there is no header either — a fresh clone prints every member as
`[new ref]`, an auto-followed tag appends one more, and a due auto-`gc` appends its housekeeping
block after all of them, which is what a `tail -2` loses the rejection to in THIS checkout.
⚠️ **Measured at `git 2.39.5`, and the flags and config that move the output are the leading `+` or
`--force`, `--no-tags` and `gc.auto`** — `### Tool-behaviour claims`' rule, due here a second time.
⚠️ **What IS invariant over every refused reading is the status and the ref**: the fetch exits **1**
and the local ref is unmoved, which is why the status, and not the last line of the log, is the
test — and the condition is a property of ONE working copy's output, never of the repository.

⚠️ **And it is realised rather than hypothetical, at one clock and in one checkout.**  Of the **46**
pull requests open at `2026-10-03T21:26:36Z` every one had a local head ref, and ⚠️⚠️ **one of
the 46 was stale — `#2313`'s, whose own row title was at that moment warning readers off the very
commit that local ref was serving** — with `--is-ancestor` exiting 1 on the pair, so a non-forced
fetch would have declined to repair it; `#2304`'s was stale in the same checkout an hour earlier
and was repaired by the `+`.  **29** of those 46 carried at least one `head_ref_force_pushed`
event.  ⚠️ **Publish the two as the bounds they are**: a force-push is **necessary** for this and
not sufficient, so the **29** bounds the exposed set from above while the ancestry test is the only
sufficient one, and the realised count is a reading of one working copy rather than of the board.
⚠️ **This clause joins neither census a reader might expect it to.**  It is not a fifth member of
the list below — those four are what a merge bullet *says*, and this is what the gate it reports
was *run against* — and it is not a seventh **audited behaviour claim** either: those six are the
hand-read generalising subset of `### Tool-behaviour claims`' recogniser over the landed COMMIT
messages, three filters down from its raw hits, so a clause in this file is not a candidate for
them by construction.  ⚠️ **That section's RULE does reach here** — name the version and the flag —
**and it is paid above.**

**What a merge bullet owes, then, is four things and none of them is a bigger sweep:**

1. **The rule and the clock, not the number alone** — *open pull requests, read from
   `refs/pull/*/merge` in one advertisement pass at `<time>`, `N` of them, with `R` head refs
   neither open nor landed under the trailing-subject key*.
2. **Both buckets, with the excluded set named in full.**  At `ac462ef` the 35 split **23 clean** /
   **12 conflicting with `main` ITSELF**: #481 #483 #484 #493 #504 #507 #514 #541 #644 #645 #648
   #668.  Excluding those twelve is defensible; omitting them in silence is not, because a reader
   given one number cannot tell *not swept* from *swept and clean*.
3. **The control that licenses the exclusion.**  A conflict against a branch that already conflicts
   with `main` is a fact about **that** branch.  Run each excluded head against `main` with the
   branch under test out of the picture, and print the result: the twelve above are exactly the
   heads that fail it, and no branch of ours is the cause of any of them.
4. **What entered and what left since the previous matrix.**  ⚠️ **Two equal counts at two clocks
   are not two readings of one set.**  The merge-ref population was **35** at 2026-09-21T21:41:18Z
   and **35** at 2026-09-22T12:33:09Z, and **six** memberships moved in between: #757, #764 and
   #793 left by *landing*, and #794, #795 and #796 entered by being opened.  The conflicting bucket
   went **13 → 12** over the same window, and its one departure is #764 — which left by landing,
   not by being repaired.  **Say which moved, or an unchanged total is a coincidence and not a
   check.**

   ⚠️ **The clock is not optional in the second slot either, and this paragraph is the proof.**
   Written with *"and is **35** now"* — the draft wording round 1 of this branch published and this
   section replaced, so it is recorded on `#2146` and resolves in no blob (`#1969`) — the sentence
   was false within the minute: the pull request carrying it was opened at **12:42:18Z**,
   **33 seconds after** the commit that wrote it, and it is itself the seventh move.  Four
   readings of one population, each explained by the moves between them:

```text
35  @ 12:33:09Z     +#797 12:42:18  +#798 13:53:59  −#796 landed 14:25:38
37  @ 14:54:46Z     +#799 14:43:15
36  @ 15:25:20Z     −#799 landed 15:03:45
37  @ 15:30:49Z     +#800 15:26:25
```

   **Publish the derived SET at both ends and not the count at both.**  A reader given `35` and
   `35` cannot recover the seventh move; a reader given the two sets has it by `comm`.

### The render gate

`README.md` is the one file here that several branches edit at once, and the check that catches an
edit which quietly **re-nests** the document — a list item that becomes a paragraph, a paragraph
that is swallowed by a fence — is not a diff. It is a **block-token delta**: parse the file with
`markdown-it` in its `commonmark` preset at the base and at the head, and report the longest common
prefix of the two top-level token arrays, the longest common suffix, and whatever is left between
them. An edit that adds prose and nothing else shows up as one contiguous insertion and no removal;
anything else means the surrounding structure moved, which a line diff will not tell you.

⚠️ **Everything below measures a DIFF, and the question a reader actually has is about the TREE:
does any landed paragraph print its markup instead of rendering it?** Nothing on this page had
asked it. The reading is one pass and its verdict is the render itself rather than any count:

```js
const md = require('markdown-it')('commonmark');                 // 14.3.2; name the version (#2122)
const h = md.render(paragraph).replace(/<code[^>]*>[\s\S]*?<\/code>/g, '');
if (h.includes('**')) { /* this paragraph prints its own markers */ }
```

A *paragraph* is a run of lines between blank lines, taken inside every `/-! … -/` and `/-- … -/`
block for a `.lean` file and over the whole of this one. ⚠️ **The `<code>` strip is not cosmetic**:
without it every paragraph that *discusses* the marker scores, and at `c6ef24a` that is **13** of
this file's **282** `**`-carrying paragraphs — ⚠️ **measured with the instrument above and the
strip deleted**, which is not the population any parity reading returns and must not be carried
from one. ⚠️ **And the `[^>]*` in it is load-bearing**: a fenced block renders as
`<code class="language-js">`, an attribute-less strip does not match it, and the two fences of this
block are then the only paragraphs here that still score — the worked example is the instruments'
own publication.

**At `c6ef24a`: `**`-carrying paragraphs `7295`, of which `2` print a literal `**`, both of them in
`.lean` docstrings and `0` of them here.** The two are `MulByNFibre:692` and `WardR1:125`.
⚠️ **That cell is dated and its count is a RATE, not a standing property of the tree**: `2` at
that ref, `1` at `28d0edb`, **`0`** at `ceb5db9`, and the membership turns over as well as the
number — both of the two named above are repaired, the `1` between them is neither of them, and its
own repair is what takes the count to `0`. ⚠️ **The population cell is instrument-dependent and the
verdict cell is not, which is the measured reason to re-derive rather than to carry**: over four
readings of the unit — paragraph against whole BLOCK, `commonmark` against the default preset,
nesting-aware against naive block extraction — the paragraph total at `0a07de7` runs `17425` down
to `6740`, a **61%** spread, while `2` → `1` → `0` comes back under every one of them.
**Re-derive the verdict at your own base and key it there**; the `2` is kept here because it is this
section's worked instance of both mechanisms below, not because it is current.
⚠️ **Every `Module:NNN` pointer in this section names the line the construct named beside it sits
on, never the line its paragraph starts on** — the two keyings differ at **two** of the three rows
here and coincide at the third, which is how a wrong one survives. Enumerated rather than counted:
`MulByNFibre` starts at `687` against the pointer's `692`, `ReductionBaseChange` at `29` against
`30`, and `WardR1` at `125` against `125` — the one row a pointer read either way gets right. The
two mechanisms are different, which is why one instrument is worth more than one rule:

* **Nested emphasis inside a marked quotation.** `**not**` recorded *inside* a `*"…"*` span that is
  itself inside a `**…**` framing pairs with itself and leaves the framing's opener with no
  partner, so the opener prints raw and the sentence loses its bold. ⚠️ `MulByNInertia` leaves the
  form free — *"recorded inside the span or named outside it"*, fidelity and not form (`#1875`) —
  and **this reading is what decides between them at a row where the inside form does not render**.
  ⚠️ **The tree had already settled it by habit and nobody had counted**: `This paragraph used to
  read` occurs on **4** lines under `EllipticCurves/` at `c6ef24a`, and the **3** that are not this
  row close the bold *before* the quotation opens — the form the repair moves the fourth into.
* **A wrapped code span whose continuation line begins `+ `.** A line-leading `+` is a bullet
  marker, so the paragraph splits, the `` ` `` never closes and neither does the `**`: one
  `/-- … -/` headline rendered as a one-item list with three raw markers in it.
  ⚠️ **`+` is the INSTANCE and the render is the population.** `grep -rn '^+ ' EllipticCurves/
  --include=*.lean` returned **1** line at `c6ef24a` and returns **0** in the tree this sentence
  lands in, and ⚠️ **the `1` → `0` IS the check on this repair** — a reader who runs it here and
  reads a present tense concludes the repair is absent. It is not a sweep for the mechanism: `+` is
  one of five spellings CommonMark reads as a block start, and at `c6ef24a` the five occur
  `-` **0**, `+` **1**, `*` **3684**, `>` **212** and `N.` **120** times,
  ⚠️ **Four of the five interrupt a paragraph unconditionally and this `+` is one of them**: only
  the ordered spelling is conditional, and of its **120** just the **34** written `1.` can, which
  is why the render and not the grep is the instrument. All **4016** other than this `+` sit in
  paragraphs the pass above renders clean, and that pass returns `0` over the tree this sentence
  lands in. The repair is to end the previous line with the `+`.

⚠️ **Do not publish emphasis PARITY as the seed, and this is the reusable half.** An odd `**` count
looks like the instrument and is not — and ⚠️ **it is not one seed either, because the unit decides
the answer**. Strip its two false-positive classes first, inline code spans and path globs like
`EllipticCurves/**/*.lean`, which is one line over whichever unit is chosen:

```js
const odd = paragraph.replace(/`[^`]*`/g, '').split('**').length % 2 === 0;   // strip, then count
```

⚠️ **At `c6ef24a` that returns `3` rows over a whole `/-! … -/` or `/-- … -/` BLOCK, and over the
paragraph defined above `2` or `3` according to a second flag the one line above does not carry —
the POPULATION it is run over.** Restricted to the `**`-carrying paragraphs this section counts it
returns `2`; run over every paragraph it returns `3`, because the strip JOINS the two single `*` of
an italicised code span — `` *`Classical.choice`* `` at `ReductionBaseChange:30` — into a `**` the
raw text never had. ⚠️ **The paragraph you are reading acquires that artefact by naming it**:
printing the span once takes its own stripped `**` count from **30** to **31**, so the seed flags
this paragraph too, at both populations, and the pass above renders it clean. ⚠️ **So the cell
attaches to the unit AND to the population, and no one wording covers both:** over the BLOCK unit
**2** of the `3` are false and the miss is a **fourth** row; over the `**`-carrying paragraph unit
**1** of the `2` is and the miss is a **third**. `MulByNFibre:692` it finds under every reading;
`NsmulOrder` it flags at both units and `ReductionBaseChange` at the block unit — at both, if the
population is unrestricted — and both render clean. And `WardR1:125` is **even** in all **16** of
`WardR1.lean`'s `**`-carrying paragraphs and all **8** of its `**`-carrying blocks, and in all
**42** and **24** of them unrestricted, so the one row that costs a `/-- … -/` headline its render
is the row no parity reading can see. ⚠️ **Stripping a false-positive class flips parity in both
directions** — a `**` inside a code span can balance a genuinely unclosed one — so the pre-filter
cannot carry a verdict. Render, then look.

```bash
mkdir -p /tmp/render && cd /tmp/render
printf '{"name":"render","private":true}\n' > package.json
npm install --cache /tmp/npm-cache markdown-it
```

```js
const md = require('markdown-it')('commonmark');
const toks = f =>
  md.parse(require('fs').readFileSync(f, 'utf8'), {}).map(t => `${t.type}:${t.tag}:${t.level}`);
```

Key each token by `type@level` rather than by `type@nesting`: both are stable, but `nesting` is
only `+1`, `0` or `-1` — opening, self-closing, closing — so it cannot tell a `paragraph_open` at
one depth from one at another, and `level` can.
⚠️ **`tag` is the third field the recipe above reads, and it is not optional.** A heading's rank
lives in `tag` and nowhere else, so `type` and `level` alone score `## H` and `### H` equal; the
ranking of `level` over `nesting` is untouched by adding it, and the case is worked below.

⚠️ **Name the key beside the figure, because `type@level` is not the only one.** `md.parse` returns
token *objects*, so a *common prefix* is undefined until you say what makes two of them equal, and
keying by `type@level` **together with `content`** is a second reading that answers differently on
the same diff. This section's own insertion is the worked instance: against `ebb4d42` it reads
`prefix 1116 / suffix 15` keyed by level and `prefix 1111 / suffix 20` keyed with content, out of
one `md.parse` of one pair of files. `#2021` carries the census over every render figure published
here.

⚠️ **Publish the delta and not the endpoints.** `N inserted / M removed`, with the inserted token
types named, is the same number **at any base**; a prefix and a suffix are neither. ⚠️ **It is not
the same number under either key** (`#2092`), and the reason is the arithmetic rather than the keys:
a prefix/suffix-derived delta spans the first differing token to the last and scores everything
between them as churn, so a paragraph whose words change is free under `type:tag:level` — an
`inline` is still an `inline` — and costs the whole span from the first differing token to the last
once `content` is in the key, whether or not anything structural changed anywhere in the diff.
⚠️ **A structural edit widens that span; it is not what sets it.** At the seven census rows whose
structural delta is `0 / 0` there is no structural edit anywhere in the diff to be near — the
type-keyed multiset is `+0 / -0` at all seven — and the content-keyed pair is nonzero regardless:
`16 / 16` at `dc82d79`, which is the gap between two reworded bullets, and `1 / 1` at the other
six, which is a gap of zero.
`046022d`'s commit message states `common prefix 896, common suffix 179, 32 inserted, 0 removed`
for the pair its round measured, and at the pair that commit *is* — `2d7f0e0` to `046022d` — the
content-keyed prefix, insertion and removal still read `896`, `32` and `0` while the suffix reads
`200`: `2d7f0e0` carries 21 block tokens beneath the insertion point that `77fb54d`, the base that
round measured against, does not. Nothing there is re-opened by saying so; it is why the delta is
the form to publish.
⚠️ **Measured over this section's own population, the two keys disagree more often than they agree,
and the number of hunks is not the discriminator.** The `markdown-it` recogniser — the substring in
a whole commit body, whitespace-flattened — returns **23** messages at `08096d3`: the **15** at
`9147113` and `c28c462`, `dba89ee`, `ab5ec3a`, `a570d4d`, `c97ba1a`, `dc82d79`, `ea5022d` and
`3f7d03c` since.
Each is re-run at the pair its commit *is*, `README.md` only, one `md.parse` per end and both keys
off the same two arrays; the thirteen that disagree are:

```
head      parent    hunks   type:tag:level   with content   content multiset
3f7d03c   ea5022d     1         0 / 0            1 / 1         +1 / -1
dc82d79   c97ba1a     2         0 / 0           16 / 16        +2 / -2
c97ba1a   a570d4d     4         5 / 0          198 / 193       +8 / -3
ab5ec3a   93cf1d4     3        17 / 0          822 / 805      +19 / -2
3c183d8   8e55db0     6        30 / 0          678 / 648      +35 / -5
c28c462   9147113     3        21 / 0           48 / 27       +23 / -2
31177f4   2d5ce68     2        42 / 0           49 / 7        +43 / -1
dba89ee   c28c462     1        25 / 0           32 / 7        +28 / -3
a570d4d   ab5ec3a     1         0 / 0            1 / 1         +1 / -1
949369c   49b327d     1         0 / 0            1 / 1         +1 / -1
4655854   1d79187     1         0 / 0            1 / 1         +1 / -1
aadc404   2aebb05     1         0 / 0            1 / 1         +1 / -1
2d5ce68   9bc0c1b     2         0 / 0            1 / 1         +1 / -1
```

**The ten that agree are `3f61ad7`, `ebb4d42`, `046022d`, `ac0a053`, `be1a4d5`, `49b327d`,
`2f1a674`, `7c0460d`, `855f993` and `ea5022d`**, every one of them a single contiguous insertion
that rewords nothing. ⚠️ **All seven multi-hunk diffs disagree, and so do six single-hunk ones**,
because the unit is the *token* and not the hunk: two hunks inside one paragraph are one changed
`inline` (`2d5ce68`), and one hunk that replaces three paragraphs while adding a bullet list is
three `inline`s out and eight in beside a twenty-token block insertion (`dba89ee`, `+91 / -22` lines
in a single hunk, multiset `+28 / -3`). ⚠️ **Seven of the thirteen disagree as `0 / 0` against
something** — under the structural key a commit that only rewords is invisible, which is the
sharpest statement both of what that key is for and of what it cannot see. The something is `1 / 1`
at six of them and `16 / 16` at `dc82d79`, whose two reworded bullets are all it changes and whose
multiset is `+2 / -2`: the content-keyed pair is charging for the sixteen tokens that lie between
them.
⚠️ **And the newest row is the sharpest, because NO token-keyed figure tells it from a one-word
reword.** `3f7d03c` adds **74** lines and removes none, in one hunk carrying **no blank line**, so
all seventy-four fold into the paragraph that was already there: top-level tokens **1313 at both
ends**, `type:tag:level` `0 / 0` with multiset `+0 / -0`, and `content` `1 / 1` with multiset
`+1 / -1` — the pair five other rows in the table return for a single changed `inline` — while the
rendered page gains **21** `<strong>` and **84** `<code>` spans over the same pair. ⚠️ **The
multiset does not rescue that one**, because it is token-keyed too: prose added inside an existing
paragraph is one token however it is counted, and what sees it is the line figure `+74 / -0` and the
rendered-span counts beside it, neither of which is token-keyed. ⚠️ **This section is written in
exactly that shape**, flush-left prose in long paragraphs, so it is not a curiosity — it is what a
round inserting here measures about itself.
⚠️ **The multiset delta is the form that is additive over edit sites**: count tokens by key at each
end and difference the two bags. Over all twenty-three rows the type-keyed multiset equals the
type-keyed prefix/suffix delta — **twenty-three of twenty-three**, so nothing is given up by
publishing it — while the content-keyed prefix/suffix form is out against its own multiset by a
factor of **43** on the insertion and **402** on the removal at the worst row
(`ab5ec3a`, `822 / 805` against `+19 / -2`). ⚠️ **It earns that keep at exactly seven of the
twenty-three** — `dc82d79`, `c97ba1a`, `ab5ec3a`, `3c183d8`, `c28c462`, `31177f4` and `dba89ee` —
and costs nothing at the other sixteen, where the content-keyed pair already equals its own
multiset; that includes all six of the `0 / 0` against `1 / 1` rows, at which `1 / 1` **is**
`+1 / -1`. ⚠️ **The hunk count is not the discriminator there either, and it fails in both
directions**: `2d5ce68` has two hunks and needs no multiset, `dba89ee` has one and does.
**So publish the prefix/suffix pair with its key and its base, and where a diff changes more than
one token publish the multiset beside it**: it is the only one of the two whose figure a re-runner
reconstructs without also reconstructing the distance between the edits.
⚠️ **`#2021` is unaffected in its population and affected in its verdicts.** It asks *which key* a
landed figure was taken under; this asks *which arithmetic*, and a structurally keyed figure is
unmoved by every reword in its diff. ⚠️ **The two populations are not the same set.** `#2021`'s
census is the **nine** published render figures its own table carries, and at `08096d3` five of
them are landed — `2f1a674`, `49b327d`, `ac0a053`, `949369c`, and `046022d`, which is that table's
PR #755 row `0904ac7` as its own thread records the merge — while the other four are unmerged PR
heads (`31b471b`, `91c6980`, `9471324`, `8db312f`) and so are not messages on `main` at all. The
population the fenced table ranges over is the twenty-three landed ones; the overlap is exactly
those five, and neither flag settles the other.

⚠️ **Both lines of the install matter, and when either is missing the result looks exactly like the
package being unavailable.**

* **`--cache <writable dir>`.** Without it `npm` exits `EACCES` on `mkdir` of its default cache
  directory. The error names the **cache folder**; it names no registry, no host and no network, so
  a reader who concludes from it that the package cannot be fetched is reading something that is
  not in front of them.
* **The local `package.json`.** `npm install` walks *up* for one. Run in a subdirectory of a
  directory that already has a `package.json`, it installs **there** rather than where you are, and
  reports success. ⚠️ **A `require` from that same subdirectory nonetheless resolves** — Node's
  resolver makes the identical walk for `node_modules` — so the `MODULE_NOT_FOUND` this looks as
  though it must produce comes from elsewhere: a `require` run from **outside** that parent. This
  harness resets the working directory between commands, so a `cd` in one and a `node` in the next
  runs from the repository root and fails there, which reads exactly like a failed install. Write
  the one-line `package.json` first so the install lands where you named it, and chain the `cd` and
  the `node` in a single command.

⚠️ **This is written down because the opposite was published rather than measured.** More than one
round on more than one branch recorded the gate as not re-run, on a ground with two halves — that
`markdown-it` was absent from the slot writing the round, and that there was no network to fetch
it. The first half is a property of a slot. The second was nobody's measurement until `#1992` ran
the install; it took under a second, and both gates it had excused then passed with the figures
their rounds had published. **A gate line is a claim like any other on this page**: run it, or
write that you did not attempt to. ⚠️ **It has happened again since, and this paragraph was
already on the page when it did** — `#2294` round 2's review recorded the gate as not re-run on
exactly the two-half ground retired here, *"`markdown-it` is absent here and `npm install` fails
(no network; root-owned npm cache)"*, and substituted a parity reading. **So the failure mode named
here is now a failure to read it rather than a missing rule**, which is the one diagnosis it did
not carry. ⚠️ **One cell of that round is a real addition, and it is about the install's LOCATION
rather than its availability: `--prefix` is as load-bearing as `--cache`, because an install into
the repository root leaves an untracked `node_modules/` and `.orchestra/validation.sh`'s FIRST gate
is `git status --porcelain` being empty** — so an install that succeeds can still turn the run red,
and it does so at the cheapest gate rather than at the build. The `/tmp` recipe this section
prescribes is already right; this is why it must not be simplified to a bare `npm install` in
place.

⚠️ **The key this section prescribed before this paragraph matched an `h2` against an `h3`, and the
one pair in this page's own history where the two skeleton keys disagree is exactly that**
(`#2021`). A heading's rank lives in `tag` and nowhere else, so a key built from `type` and `level`
alone cannot see it:
`## H` rewritten as `### H` scores **0 inserted / 0 removed** under `type@level` and under
`type@level` with `content`, and **3 in / 3 out** under `type:tag:level`. That is not a corner.
Across the fifteen landed messages this section now counts, each re-run at the pair its commit
*is* — its parent to itself — `type@level` and `type:tag:level` return the same prefix and suffix at
fourteen and differ at one, `ebb4d42` → `3f61ad7`: `1116 / 15` against `1110 / 21`. ⚠️ **Each of
the three answers is produced by a different field, and they are produced by two different tokens.**
At index 1110 of that base array the base holds a `heading_open` whose `tag` is `h2` and the head
one whose `tag` is `h3`; `type` and `level` score those equal and walk six tokens further, to
`1116`, which is the whole of the `tag` axis. ⚠️ **The heading's words are not in that token** —
its `content` is the empty string at both ends — and *"Reviewing"* against *"The render gate"* is
index 1111, the `inline`, which is where a key carrying `content` diverges. That is why the three
prefixes are `1116 / 1110 / 1111` and not `1116 / 1110 / 1110`, and the six tokens the first two
answers straddle are a `heading_open`, an `inline`, a `heading_close`, a `paragraph_open`, an
`inline` and a `paragraph_close`. ⚠️ **That commit is the one that wrote this section**, so the
rule and its counter-example landed together, and a heading demotion is the re-nesting a line diff
hides best.

⚠️ **So key by `type:tag:level`.** It is a strict refinement of `type@level`, it is what four of
the five landed messages that state a key state, and it leaves the reason given for preferring
`level` to `nesting` standing — `tag` adds what `level` cannot carry rather than replacing it. The
clause *"Key each token by `type@level` rather than by `type@nesting`"* is **completed and not
retired**: `### Reach clauses`' test for which of those applies is whether the old clause was false
or merely partial, and that one ranks two keys correctly and is silent on a third. ⚠️ **The
completion is in place above and not deferred to this paragraph** — the sentence keeps its ranking
and gains the `tag` field beside it, and the runnable recipe maps `type:tag:level`, so the
imperative and the executable form of it name one key. **A section that prescribes in prose and
implements something else is read through the code**, which is the thing a re-runner copies. So is
*"keying by `type@level` **together with `content`** is a second reading"* — a second, and not the
last.

⚠️ **The landed record, with its recogniser and its date.** `git log --format=%B` over `main`,
whole bodies whitespace-flattened, substring `markdown-it`: **15** of **725** messages at
`9147113`. The two other substrings tried return **6** (`common prefix`) and **2** (`block token`)
and add no message the first does not. Of the fifteen, **5** state a key as a field list —
`type:tag:level` four times, which `aadc404` writes *"type / tag / level"*, and `type@level` once,
beside `type@level` with `content` — **4** say *"token skeleton"* and give no fields, and **6**
name nothing at all. ⚠️ **A round keying by `type@level` on this section's word takes one landed
message in five as its authority.**

⚠️ **Three keys, three answers, and the pair that produces all three is this section's own
insertion.** The fifteen re-run at their parent pairs under the three: **6** give one prefix and
suffix under all of them, **8** give two, and **1** gives three — `ebb4d42` → `3f61ad7`,
`1116 / 15` by level, `1110 / 21` by `type:tag:level`, `1111 / 20` with `content`. The insertion
count there is **35** under every one of the three, which is the delta rule measured rather than
asserted.
⚠️ **Unpacked, that bucket points the other way from the ruling, and the ruling is still the right
one.** The axis this section now prescribes separates `type@level` from `type:tag:level` at **1**
of the fifteen; `content` separates itself from `type:tag:level` at **9** — `3f61ad7`, `046022d`,
`949369c`, `31177f4`, `2d5ce68`, `4655854`, `855f993`, `3c183d8` and `aadc404` — so the whole of
the *"two answers"* bucket is the `content` axis and none of it is the `tag` axis. ⚠️ **That is
what a structural gate looks like when it is working.** The question this gate is built to answer
is whether the surrounding structure moved — a list item that became a paragraph, a heading that
changed rank, a paragraph swallowed by a fence — and a prose rewrite that moves no block is a
change a line diff already shows in full. A key carrying `content` re-scores every one of those
edits as a token insertion and a token removal, which is why four of the fifteen honestly read
`0 in / 0 out` on a diff that changed words: the zero is the gate saying *nothing re-nested*, and
it is the answer the gate was asked for. `content` stays a second reading rather than the
prescribed one for that reason and not by headcount.

⚠️ **An index is an endpoint, and the delta rule does not yet exclude one.** `ebb4d42`'s message
publishes its gate as *"+3 block tokens with the divergence at token 928"*, under its own clause
*"stated as DELTAS and not as endpoints, because an endpoint is base-relative and a delta is not"*.
The `+3` and the three token types it names are base-invariant and reproduce at every pair; the
**928** is a position in the base array, and at the pair that commit is — a parent that round never
saw — the same three tokens sit at **960**. Publish `N inserted / M removed` with the types named,
and name the `base → head` pair beside them; do not publish a position **as the figure**. ⚠️ **An
index used to say why two keys disagree is not a figure and is exempt**, which is what the `1110`
and the `1111` above are: both ends of their pair are landed shas, so the arrays they index are
fixed forever, and the sentence is unreadable without them. The rule binds on a position offered
as the gate's answer, because that is the one a later base silently re-numbers.

⚠️ **No figure in the fifteen is false under the key and the pair its author used**, recorded so
that the census is not re-run blind. The two measured against a base other than their commit's own
parent both reproduce at the base they name: `046022d`'s `prefix 896 / suffix 179` at
`77fb54d` → `0904ac7` keyed with `content`, and `ebb4d42`'s `928` at `77fb54d` → `91c6980` under
all three keys. ⚠️ **Both pairs share that base**, and ⚠️⚠️ **the clause that stood here about their
two heads is retired immediately below, because it was FALSE and not merely partial.**

Retired: *"what is luck is the two heads — a branch head force-pushed over is not fetchable by sha
afterwards, so a figure keyed to one can be re-derived but never re-run"*, written by `c28c462`
(2026-09-19T19:44:37Z). ⚠️⚠️ **The emphasis is NAMED here and not reproduced inside the span,
which is the second of the two compliant forms `### Retired claims` gives**: in `c28c462` the
quoted clause as far as *"two heads"* sits inside a bold span, and that span OPENS at the
surviving *"Both pairs share that base, and"* one line above — so carrying the `**` pair inside
this quotation would have to re-quote as RETIRED a half that is LIVE, and the fidelity the section
asks for is served by saying where the bold runs instead. ⚠️ The clause was contradicted by
`## Reviewing`'s *"a superseded head is re-fetchable"* **19 h 28 min 58 s later**, at `ea5022d`
(2026-09-20T15:13:35Z) — so this page has carried both readings for a fortnight,
`### The render gate` denying what `## Reviewing` asserts, and the wrong one was the stated REASON
for *"re-derived but never re-run"*.

⚠️⚠️ **Its own two heads refute it.** `91c6980e5977b37de58b85bd2200f94505956c05` and
`0904ac7642d0c5f7178f09ca064cd202616f3406` are at the tip of `refs/pull/753/head` and
`refs/pull/755/head`, which outlive their deleted branches, and neither is an ancestor of `main`; at
`git 2.39.5`, into a `git init` holding zero objects, `git fetch --depth=1 <url> <40-hex>` exits
**0** for each and `cat-file -t` then answers `commit`, while the same fetch at **seven** characters
exits **128** with `fatal: couldn't find remote ref`. ⚠️ **The harder case answers the same**: the
heads of `#2313` round 1, `#2313` round 2 and `#2315` round 3 —
`08eb1606fce785ae67d102a18a142c0fa66ae7c6`, `20d7fa45af99314e86f82c0a94cfd805f7c78352` and
`f380f9eafc5fcfbd5044c044c28fe27ca48d4d11` — are at the tip of **none** of the refs the remote
advertises and fetch at the forty just the same. ⇒ ⚠️⚠️ **The fragile thing is the KEY'S WIDTH and
never the head's fate**, and a figure keyed to a force-pushed-over head is RE-RUN and not merely
re-derived, for any instrument that reads one ref.

⚠️⚠️ **What `--depth=1` does not restore is HISTORY, and that is the half of the old clause worth
keeping**: at such a head `rev-list --count` is **1**, `git cat-file -t <40-hex>^` is *"Not a valid
object name"* — ⚠️ **and the command is named because that message is 1 of 7 forms**: `rev-parse`,
`rev-parse --verify`, `~1`, `log -1` and `show` all answer `unknown revision` or
`Needed a single revision` instead, and ⚠️⚠️ **`rev-parse <40-hex>^{commit}` SUCCEEDS and returns
the sha itself, because peeling is not parenting** — while `blame` over the whole file is **1**
boundary commit, the head itself, and ⚠️ **`log -S` reports that boundary commit for any string
the file merely CONTAINS**, answering `08eb160` for *"superseded head is re-fetchable"*, a string
that entered at `ea5022d`. **So re-run a one-ref gate at a superseded head, and never blame, count
or `-S` at one.** ⚠️ **The durability half is therefore
SCOPED and not deleted: a pair is only as durable as its weaker END KEY**, seven characters being
what dead-ends at the server — which is why `## Reviewing` prescribes publishing the forty beside
the figure at the moment the figure is published.

⚠️ **Attribution is by sha and date because the prescribed ROW key is unavailable at BOTH ends**:
`c28c462`'s subject ends `(#2021) (#776)` and `ea5022d`'s ends `(#2001) (#782)`, the PENULTIMATE tag
being the row — and `#2021` and `#2001` resolve to **no taxis row of this project**, while `#776`
and `#782` are the pull requests whose own merge commits those two shas ARE, read at both.

⚠️⚠️ **One copy of the same claim SURVIVES this repair, and it is named rather than left to be
found**: base blob `43c84ed0:README.md`:`3757` says of two force-pushed heads *"so both resolve only
through `refs/pull/<n>/head`"*, and BOTH halves are false —
`bab331934268736c261877b291e8bcff52096a47` and `f7b25145082e5b7e2faaaa778a2927af75fa1d36` fetch
at the forty (exit **0**, `cat-file -t` `commit`), while `refs/pull/746/head` and
`refs/pull/749/head` point at neither of them — read `2026-10-04T04:40:54Z`, both pull requests
`OPEN` — so the named route is the one route that does NOT reach them. ⚠️ **The two ref values are
deliberately NOT published here**: they are a live board reading, and the conclusion needs only the
forty and the miss. ⚠️ **It is a different block about the same behaviour, so
`### Retired claims` asks for its own quotation and not a second copy of this one**, and it is out
of this clause's scope. ⚠️⚠️ **PR #783 carries BOTH retirements and has been OPEN since
2026-09-20 with CI green and 0 reviews**; ⚠️⚠️ **it merges cleanly only up to `43c84ed0`, the base
this paragraph was written against, and it ACQUIRED A CONFLICT AT `24825726` — the squash that
landed this very block.** `git merge-tree --write-tree <main> refs/pull/783/head` exits **0** at
`43c84ed0` and at `0d2a7307` and **1** at `24825726` and at every `main` after it, so the
conflict is **`main`'s** and the clause that first reported it as this branch's is retired by the
landing that caused it: **#783 cannot land without a rebase whether or not any other branch
exists.** ⚠️ **No behind-count is given here and that is deliberate** — it was `105` at
`43c84ed0`, `110` at `0d2a7307` and `114` at `7fa78aea`, a figure whose far endpoint is whatever
`main` is when the sentence is read. **Re-derive both readings rather than citing either**:
`git merge-tree --write-tree $(git ls-remote upstream main | cut -f1) refs/pull/783/head`, exit
from `$?`. **Only one of the two can land.**

⚠️ **And the key prescribed above costs the landed record almost nothing, which is a better warrant
for it than four-of-five.** Every one of the **4** messages that say *"token skeleton"* and name no
fields returns, under `type:tag:level` at the pair it names, exactly the figure it published:
`949369c` `1038 / 0` with 0 in and 0 out at `0199a96` → itself, and `49b327d` `915 / 78` with 45
in, `2f1a674` `895 / 78` with 20 in and `7c0460d` `471 / 453` with 7 in, each at its parent. So
does `ac0a053`, which names no key at all — `1075 / 0`, 21 in, 0 out. The three that already write
`type:tag:level` are true by construction. ⚠️ **Two published figures are not the prescribed key's
answer, and only one of the two leaves a reader unable to tell**: `3f61ad7` gives `1116 / 15` and
`1111 / 20` and **names both keys**, so a reader has what they need; `046022d` gives
`prefix 896 / suffix 179` where `type:tag:level` reads `898 / 177` at the same
`77fb54d` → `0904ac7`, and **names none**. **The ruling retro-validates every landed figure whose
author said what they measured**, which is what makes *name the key* the half of this section that
was always load-bearing.

⚠️ **One exception to the clearance above, and it is not about the key at all — it is about the
word *this*.** `31177f4` writes *"the whole token skeleton (`type:tag:level`, **966** tokens) is
**byte-identical** `88f9253` → this head"*. `88f9253` still resolves and carries **966** tokens, so
the base is fine; **`this head` is what does not hold still**. It was the branch head the round was
written at, that head was amended away, and read at the commit the sentence landed in the pair is
`88f9253` → `31177f4`, which is **966 → 973** with **7** inserted under all three keys — one
`fence`, one `bullet_list` and five more. The same bullet's other figures are measured parent to
**landed** and reproduce, so *this head* is the landed commit and the identity claim is false there.
⚠️ **A pair with a landed sha at each end can be re-run forever; a pair with `this` at one end is
re-measured by every later round of its own branch**, and this is the one row of the fifteen where
that happened. Name both ends by sha, in a message that is still open to be amended.
## Reviewing

Work here is dispatched to several agent slots at once, and a pull request is normally written in
rounds: one push, answering the review before it. **Until this section, who may review a round was
stated nowhere here**, and leaving it unstated has not left it unused: `#2001` names five different
strengths in which it was invoked in one day, each in good faith and each stated as a requirement
on the next round, and on one branch — `#1810`, PR #753 — two consecutive comments have given
opposite answers about the same slot. This section is about process and not about prose: the
docstring conventions of this file do not reach it, and it does not reach them.

⚠️ **Who may review and what a DELIVERING round owes the verdict set are different questions, and
only the first is settled above**: the second is `### Answering a verdict`, at the end of this
section, and that subsection's `must`s bind the DELIVERING round and not the reviewer.

**The hard bar is one sentence, and every other bar here is a preference: a reviewer must not be
the author of the round under review.** A round certified by the agent that wrote it is not
certified, and no amount of disclosure repairs that.

**A prior reviewer of the same branch may review a subsequent round**, and should open by saying
so. Checking whether one's own charge was paid is the cheapest check this board has, and it is the
one check no other slot can make as quickly.

**A prior author of any round of the branch may review a subsequent round when that round touches
none of the text they wrote.** ⚠️ **That is not the same claim as having written no part of the
round under review, and it is the touching and not the authorship that the test here checks**:
compare `HEAD^{tree}` across the two heads, or difference the round against the head last
certified, restricted to the hunks that author wrote. Where the round does rewrite prose the
reviewer wrote, they *should* stand aside and say why.

⚠️ **The clause above names two instruments and only the first of them always exists.** *"The head
last certified"* is the convenient one, and it is **vacuous on a branch no round of which has been
certified** — the normal state of a branch in its second or third round, because a rejection
certifies nothing. ⚠️⚠️ **So the two-head comparison is the primary instrument and the other is a
shortcut that an approval creates**, and the two heads are the PREVIOUS ROUND's head and this
round's. **What is not the test under either form is the branch against `main`.** A rejected round's
deletions stay in the branch, so a branch-level figure charges an earlier round's touches to the
round in front of you.

⚠️ **The worked case cost one lane 7 h 24 min, and three slots measured it the same wrong way.**
`#2303`, PR #890, carries round 2 (`3c31bdb`) and round 3 (`579165c`) on base `2b18bbd`, and round 2
was rejected, so nothing on that branch was ever certified. Against `main` `0e13ff0` the branch
replaces **21** base lines, **6** of them one slot's (`e7813f80`); ⚠️ **round 3 alone — `3c31bdb` to
`579165c` — replaces 39, of which 26 are round 2's own text, 13 are a second slot's and ZERO are the
first slot's.** Those six are round 2's deletions, and the blame totals say it a second way:
`e7813f80` holds **67** lines of `Galois/SubfieldAut.lean` at `0e13ff0`, **61** at round 2's head
and **61** at round 3's, while the second slot's two commits hold **110**, **110** and **97**. ⚠️
**The two slots' stand-asides were exactly swapped relative to the rounds** — the one that reviewed
round 2 held none of its text and the one that stood aside from round 3 held none of that either —
and the round sat `OPEN` from its delivery comment at `09:02:40Z`, CI green at `09:04:18Z`, to the
round-3 verdict at `16:28:50Z` — **7 h 24 min** of it green and unreviewed — while its author was
hard-barred and both other present slots believed themselves `should`-barred.

⚠️⚠️ **Name the error's DIRECTION, because this section warns about only one of the two.** The
paragraph beginning *"A touch list is a claim about a diff"* convicts a touch list wrong toward MORE
eligibility, *"because nothing downstream catches it"*. ⚠️ **A branch-level figure errs toward LESS,
and nothing downstream catches that either**: a stand-aside reads as conservative diligence, its
arithmetic is the one number no later round re-runs, and what it costs is the starved lane the
paragraph below exists to prevent. **So re-derive the partition with the round-level instrument
BEFORE concluding that no slot satisfies the preferences.** On the case above the hatch was reached
for twice and declined twice, each time after careful reasoning about which slots were live; ⚠️
**both of those judgements were unnecessary, and the deadlock was arithmetic rather than
scheduling.**

⚠️ **The test is per ROUND and also per LAYER, and the message-layer paragraph below settles the
unit for what a reviewer may SAY rather than for who may SIT.** A round that freezes the tree — one
answering a charge against a commit message with `--amend` — has no file diff at all, so every file
figure on the branch reaches nothing and the unit is the stripped non-blank MESSAGE line, by that
paragraph's own recipe. ⚠️ **`#2310`, PR #897, is the case, and the rule below reaches it first, so
its two heads are paired at full width beneath this paragraph**: `383bdbd^{tree}` is `85f68bc2`,
byte-identical to round 1's, and of round 1's **77** stripped message lines — `N → M` is
**77 → 103** — round 2 replaces **5** and leaves **72** standing, over a region floor of **3**. The
slot that stood aside from round 1 on a measured **9 of 9** replaced base lines, in a file whose
**417 of 417** lines at `0e13ff0` are its own one commit, holds **0** of those message lines and is
clean on round 2; ⚠️ **the slot that wrote the message is the only one the `should` reaches there.**
**Consecutive rounds of one branch can therefore bar opposite slots, and a touch figure is a fact
about one round and one layer and about nothing else.**

⚠️ **The pair at full width, because this case is the clause's own named failure — an amend in place
— and a figure without its two names is unre-runnable by construction.** Round 1's head is at the
tip of **none** of the refs the remote advertises and round 2's is at exactly **one**,
`refs/pull/897/head`, which outlives the deleted branch; seven characters fetch neither
(`fatal: couldn't find remote ref 37280c1`), and the server serves both by full object name into an
empty `git init`, which is what makes the figure re-runnable from a fresh clone:

```sh
git fetch --depth=1 https://github.com/lana-agents/elliptic-curves.git \
  37280c104584e6df8796bdf306ea131b8853b220 383bdbd829decba45b7c3b2217a841662b8cc3ec
```

⚠️⚠️ **`N → M` is the cell that names the reading and `standing` is the cell that cannot.** With
blanks KEPT rather than dropped, the two flags this section fixes below — whether the blank line
preceding the trailer goes with the trailer, and which of `pop 0` / `pop 1` / `pop 2` is taken —
carry this one pair over **six** readings that collapse to **four** distinct tuples: `97 → 128`,
`96 → 127`, `95 → 126` and `94 → 125`, with `standing` **92 / 91 / 90 / 89** against the landed
reading's **72**, and the region floor **4** at all six against **3** under the drop — invariant
within each side and not a quadruple. ⚠️ **`pop all`, the convention named below as the one NOT to
take, is what moves the floor**: it returns `94 → 124` at both trailer readings, having eaten the
trailing `insert` opcode the other three leave standing. The disturbed **5** is invariant at all
**twelve** readings — these six and the six under the drop, where every flag here is one of the
exact no-ops this section proves them to be — and at all **twenty-four** with `autojunk` toggled,
which the five-pair table below reads at `False`.

⚠️⚠️ **And the SUBJECT LINE's leading ordinal names the round the push CREATES, which is the one
cell of an `--amend` that no reviewer-side rule here reaches.** The paragraphs above fix what a
reviewer may read on a frozen tree and who may sit; ⛔ **neither they nor `### Answering a verdict`
say what a DELIVERING round owes its own subject, so the convention has been practice with no
clause behind it** — the shape `#2001` had before this section existed. **A round that amends
re-points the leading ordinal to its own number, and a round that answers a verdict names that
verdict's CLOCK somewhere in the `%B`.** ⚠️ **The direction of the error is the expensive one: a
subject naming an EARLIER round reads, at the width `git log --oneline`, `git log --format=%s | cut`
and `gh pr list` show, as a round that has already been reviewed** — the stale-title hazard that row
titles here carry *"READ THE … COMMENT, NOT THIS TITLE"* against at the taxis layer, with no such
warning available at the `%B` layer. ⛔ **And the repair is an ADDITION at the head plus the
re-point, never a retirement**: the body is cumulative here, a `ROUND N PAYS …` clause about an
earlier round is TRUE, and nothing licenses deleting a prior round's account to make room for a
newer one.

⚠️ **The worked case is `#2354` round 3, PR #952, landed as `71aff0c8`, and nothing in it is false
— which is why it is cited here and not in `### Retired claims`.** Its subject's leading clause is
*"`#2354` **ROUND 2 PAYS** slot-1's `06:37:15Z` VERDICT IN FULL"*, a true proposition about round 2;
read in the landed `%B` off `main`, `09:05:22Z` — the clock of the verdict round 3 pays — occurs
**ZERO** times, `ROUND 3 PAYS` **ZERO** and `06:37:15Z` **SIX**, while the body knows which round it
is at **eight** `ROUND 3` mentions including **five** `ROUND 3 REPAIR` markers. ⇒ ⚠️ **the
information is present and the leading clause is where it is absent**, and no clause names the
paying verdict in the FULL form `### Answering a verdict`'s instrument anchors on. The body names
it twice: once unkeyed, as *"slot-1 wrote the verdict this round pays"*, which resolves to nothing
once a row has drawn two; and once in this board's minute-masked form, as *"slot-1's `09:0xZ`
reading"*, which the anchored grep matches at **ZERO**. ⚠️ **So the point is the INSTRUMENT and not
the absence: a round that names only the masked form still defeats it.**

⚠️ **The convention was already 7 of 8, keyed at `a4bb7a16`**: of the ten most recent landings
there, eight open with an ordinal and **seven** name the landing round — `#2348` round 8, `#2358`
round 1, `#2352` round 4, `#2353` round 2, `#2351` round 3, `#2349` round 2 and `#2345` stage 2 file
2 round 2 — the eighth being `71aff0c8` above; the two with no ordinal, `#2355` and `#2350`, are
both round 1s, where there is no earlier round to be mistaken for. ⚠️ **Each round number there is
taken from the row's verdict record and from the commit BODY and never from the subject, which
would assume what it tests, and the subjects off `git log -1 --format=%s` and never
`gh --jq .messageHeadline`, which truncates.** ⚠️⚠️ **The census survives the truncation its own
first row carries, and that is a property of the instrument rather than luck: `a4bb7a16`'s landed
body is CUT by the squash cap, but regions are prepended newest-first there, so what the cap takes
is the OLDEST and the maximal self-referential `ROUND n` lives in the NEWEST, which survives.**
⛔ **A branch that APPENDS its regions inverts that, and the same census run over one would read
the ordinal of a round the cap had removed.** ⚠️⚠️ **TWO prior CROSS-AUTHOR amends are
measured here and BOTH did what the rule above says; no wider census is run and no cardinal is
asserted over the population.** `6ab5647b`, `#2351` round 3: its own seat paragraph records that
slot-0 filed the row and authored rounds 1 and 2 while the round itself is another slot's, and its
subject opens `ROUND 3 PAYS` and carries that round's own verdict clock, `02:49:46Z`.
⚠️⚠️ **The second is the convicted branch's OWN round 2** — `6dd23be2`, slot-2 amending slot-0's
round 1 — **whose subject went from the ordinal-free *"`#2354` TAKES HORN (i)"* at `827d105e` to
*"`#2354` ROUND 2 PAYS slot-1's `06:37:15Z` VERDICT IN FULL"*: it added the ordinal AND the
clock.** ⇒ ⛔ **So the convicted clause was CORRECT WHEN IT WAS WRITTEN — round 2 wrote it, about
round 2 — and went wrong only because round 3's `--amend` INHERITED it unchanged.** ⚠️ **That is
why the rule binds the DELIVERING round and is stated as *"a round that amends re-points"*, and
why the next cross-author amend should not have to re-derive it.**

**Where no slot satisfies the preferences, the hard bar alone governs.** ⚠️ **A rule with no
escape hatch starves the lane, and a starved lane is how an uncertified round lands.** The
reviewer takes the round, opens with every prior touch they hold on the branch, and re-derives
from the tree — not from their own prior record — every figure that bears on text of their own.

⚠️ **An exclusion is not inherited, and that is what keeps this from ratcheting.** A round that
closes by naming the slots its successor may not use is asserting a rule rather than recording a
fact, and such assertions only accumulate: each round adds a name, none removes one, and the
exclusion set reaches every slot while the branch is still live. **Record the touches instead** —
who wrote which round, who wrote which review — and let each reviewer derive eligibility from the
bar and the preferences stated here. A touch list is a fact about the branch that a subsequent
round can only extend; an exclusion list is a claim about a slot that nothing re-examines.

⚠️ **The section above is the rule, and its failure mode now is that rounds ask for it rather than
read it.** In the **71 minutes** between `2026-09-20T03:09Z` and `04:20Z`, four comments on three
branches closed by declaring the lane deadlocked and this rule unwritten — *"`#2001` is still
written down nowhere"*, *"what is missing is the rule about what to do when it empties the pool"*,
*"no eligible reviewer left … `#2001` is now the board's binding constraint"* and *"landing that
rule on the page is still owed"* — with this section live since `ac0a053`, **five days and six
hours** before the first of them. ⚠️ **Two of the four are on the thread whose own openings quote
it**: through the comment that says it, that thread names `## Reviewing` as governing **14** times,
and **5 h 47 min** before the *"still owed"* clause the same slot on the same branch quoted this
section's *"a prior reviewer of the same branch may review a subsequent round"* verbatim, to
license a reviewer by it. **A round must not close by asking for a rule stated here, and a review
must not close by declaring a branch unreviewable.** ⚠️ **The worked case convicts itself**: the
*"no eligible reviewer left"* review was written at 03:28Z, and the round it handed off was
reviewed and approved **1 h 27 min later by the slot that wrote it**, under the prior-reviewer
permission above — no hatch, no exception, the rule as printed. A closing of that shape is the
exclusion list in a new spelling, and it costs a round its reviewer.

⚠️ **A touch list is a claim about a diff, and it has to be checked before it is relied on.** The
paragraph above says to record the touches; it does not say that a recorded touch is evidence, and
⚠️ **a touch claim published as a measurement is still a claim.** The worked case is one that was.
A correction dated `2026-09-15` holds that round 5 of one branch *"carries no hunk in"* the
`=== ROUND 4 …` section of its own commit message, that section being *"byte-identical"* at
`263fa34` and `e5efa77`, and that the stand-aside asked of that round was therefore unnecessary.
Re-run at those two shas, counting its `===` heading through its last non-blank line: the section
is **323** lines at `263fa34` and **326** at `e5efa77`, and round 5 carries **four hunks,
−7 / +10**, inside it — two heading citations re-keyed, one declaration line key dropped, and a
marked quotation re-scoped. ⚠️ **So the stand-aside was right
and the correction was the error, in the direction toward MORE eligibility** — the worse of the
two, because nothing downstream catches it: the slot a wrong touch list nominates has no reason to
doubt the nomination. The check is two commands — `git diff <the head last certified> <this head>`,
then read whose text each hunk replaces. **Never take it from the round's own ledger, and never
from a note about the ledger.**

⚠️ **The attribution half of that check has one regime where its obvious instrument is wrong by
construction: a branch whose earlier round heads are not ancestors of the head under review.**
`git commit --amend` is one way in and `commit-tree` or a rebase is another; ⚠️ **the mechanism is
the ancestry and not the command.** ⚠️ **It is the ordinary regime and not the exotic one, and the
frequency is measured rather than asserted**: `head_ref_force_pushed` is non-empty on **10** of the
**16** pull requests `884`–`899`, read at **`2026-10-04T01:42Z`** — an upper bound, because a
force-push can be a fast-forward — so **at least** six of the sixteen are stacked, where blame is
sound. ⚠️ **One of the six zeros can still move and the other five cannot**: `#887` is OPEN at zero
while the other five are `MERGED` and frozen, so one push to it reads `11 of 16` with nothing else
on the board moving. The displaced head cannot be reached from the
head under review, so `git blame` there credits that round's surviving text to the commit that
replaced it. ⚠️ **Detect the regime before attributing anything, and then attribute by CONTENT and
not by blame**: the two heads are the PREVIOUS ROUND's and this round's — ⚠️⚠️ **which is NOT the
paragraph above's `<the head last certified>`, a head that does not exist on a branch no round of
which was certified**, and the worked case below is such a branch. ⚠️ **Every exit status and
message in this clause was read at `git 2.39.5`** — `### Tool-behaviour claims`' own rule, falling
due on the claim this clause adds; the base sites that rule does not yet reach are `#2321`'s and are
untouched here.

```sh
git merge-base --is-ancestor <prev round head> <this head>  # 1 ⇒ the regime, 0 ⇒ stacked
git diff <prev round head> <this head>                      # whose text each hunk replaces
git fetch --depth=1 <url> <40-hex>                          # the prev head is at no ref tip
# the worked case's two heads at full width, since ls-remote expands neither abbreviation:
git fetch --depth=1 <url> 08eb1606fce785ae67d102a18a142c0fa66ae7c6   # #2313 round 1
git fetch --depth=1 <url> 20d7fa45af99314e86f82c0a94cfd805f7c78352   # #2313 round 2
```

⚠️ **The worked case is this section's own neighbour and the blame is wrong 8 of 8.** `#2313`'s
round-1 head `08eb1606` and round-2 head `20d7fa45` both name `0e13ff0` as their only parent, so
`--is-ancestor` exits **1**; round 3 replaces **8** lines of the per-layer paragraph, and those 8
are **byte-identical** at the two heads — `5690`–`5697` at round 1's and `5692`–`5699` at round
2's, displaced by re-wraps in the two paragraphs immediately above them, ⚠️ **one line from each
and not two from one** — with `git diff 08eb1606 20d7fa45` carrying **no hunk** that touches them.
**Blame at round 2's head answers `20d7fa45`, 8 of 8; blame at round 1's head answers `08eb1606`, 8
of 8.** A partition built from the first hard-bars the slot that wrote nothing and clears the slot
that should stand aside — ⚠️⚠️ **both directions at once, which is what makes this instrument worse
than either**: the clearing half is the MORE-eligibility direction the paragraph above calls the
worse of the two, the barring half is the LESS-eligibility direction, and neither needs anybody to
mis-state a figure. ⚠️⚠️ **And the fetch restores the CONTENT, not the blame.** Neither head is at
the tip of any ref the remote advertises — **0**, and ⚠️ **the denominator drifts inside the day
its date names**: it read `1017` and then `1020` on `2026-10-03`, so the membership is the cell and
the population is not. The 7-character abbreviation fails with `fatal: couldn't find remote ref`
while the full 40-hex object name is served into an empty `git init`, ⚠️ **so both forties are in
the fence above and not only their eight-character forms**; inside that shallow clone
**every** line blames to the boundary commit `^08eb160` whoever wrote it. **So the content
comparison is the instrument, and a blame is at most a cross-check taken in a full clone at the
EARLIER head.** ⚠️ **A second mechanism, measured on a second branch**: `#2307` round 4 rebuilt
rounds 2 and 3 with `commit-tree`, keeping each tree byte-identical, so neither `18206f4` nor
`db8307d` is an ancestor of that branch's head and `--is-ancestor` exits `1` for both — no
`--amend` anywhere. **A round that re-authors a commit at all leaves this regime behind it,
whatever command it used.**

⚠️ **The touching test decides the ROUND; it does not decide what an approval certifies, and the
two come apart.** An approval certifies the head and not the hunks, so a slot's text can be absent
from every hunk of the round under review and still be most of what lands. Measured on a branch
whose tree was frozen across four rounds: of the **25** non-blank lines round 6 inserted into this
file against `046022d`, **19** are still among round 7's **39** — a slot that wrote no line of
round 7 wrote half of what round 7 would land. ⚠️ **A rejection does not clear an author**: it
targets a clause, and the round inherits everything it did not target. **So the touching test
governs whether a slot may take the round, and a `should` governs what it may then say about it**:
text the head still carries and this round did not touch is **carried, not certified**, and a
reviewer who wrote it either re-derives it from the tree or says that it is carried. ⚠️ **That is
also the ground of the prior-reviewer permission above, which is asserted there without one — and
the ground this clause replaces was FALSE.** It read *"a reviewer leaves no text in the artifact, so
the intersection is empty by construction"*; ⚠️ **the emptiness is CONDITIONAL and not
constructional.** It holds of a reviewer that authored no round of the branch, and ⚠️ **it fails for
a slot that delivered an earlier round and takes a later one under that permission** — on a
multi-round row the common case rather than an exotic one, and there the intersection is neither
empty by construction nor empty in fact and can be nearly the whole artifact. ⚠️ **The failure is
memory and not reasoning, because a review record HIDES authorship**: *"I reviewed rounds 3 and 4"*
reads as *"I wrote none of this"*. **So derive it rather than recall it — and derive it as a SUM
over that slot's own pushes, never as a subtraction.** For each commit `c` that slot pushed, take
the head-side ranges of `git diff -U0 <the head that push replaced> c` and carry them forward
through every later push; their union is that slot's share of the head. ⚠️⚠️ **The left operand is
the REPLACED HEAD and never `c^`**: under the amend regime `c^` is the branch's base, so it returns
the cumulative diff and reports the same pair for every round of a branch alike — a round that
rewrote half the insert and a round that changed one word come out identical. ⚠️ **Take the replaced
head's 40-hex name from the row's dated delivery comment**, because an amended branch leaves it at
the tip of no ref and `--is-ancestor` exits `1` on it. ⚠️ **The complement is not the answer**:
`<this head>`'s line total less the ranges added since one of that slot's commits credits every
other slot's untouched text to that slot, and it fixes no rule for choosing the commit when the slot
pushed more than one. ⚠️⚠️ **Nor are the raw per-push ranges a partition**, because a later round
can replace a line an earlier one added, so uncarried they over-count. **The restriction the test
above already prints — *restricted to the hunks that author wrote* — is what makes the sum sound;
without it the figure is an upper bound and must be published as one.** ⚠️ **Key the pushes to the
ROW tag — on a squashed subject the PENULTIMATE `(#NNN)`, the trailing one being the pull request —
and to that row's thread, never to `%an`, because `git` author metadata here is slot-blind.** ⚠️⚠️
**Naming the class is not pedantry, because the trailing numeral is a pull request by POSITION and
not by magnitude**: at `74f065cd` **627** of this file's **839** reachable subjects carry the
two-parenthesis form, and every one of those trailing numerals falls inside the row-ID range, so
nothing but the position tells them apart — and ⚠️⚠️ **exactly one commit escapes BOTH halves of
that prescription, and it is the one that created this file**: the root commit `2e6ee266`, *Create
README.md*, carries a human name rather than the single bot account every other commit carries, and
carries no `(#NNN)` tag at all. So the prescription is right and its universal is not: `%an` is
*more* misleading there, not less. ⚠️ **And where the thread half dead-ends, say unattributed rather
than unowned**: the base lines this clause replaces are `ea5022d9`'s, whose subject ends
`(#2001) (#782)` — and ⚠️⚠️ **BOTH halves dead-end, which is a stronger instance of this clause's
own point than one half would be.** The row tag `(#2001)` resolves to no taxis row at all; the
trailing `(#782)` is the pull request, whose own merge commit IS `ea5022d9`; and the taxis row
bearing that number is a live, unrelated, completed one with no pull request attached. **So the
subject resolves and nothing signed attributes those lines.** ⚠️ **Measured** (`#2307`, `#2316`): a
five-round row whose ROUND-4 VERDICT, written by the slot that had itself delivered round 1,
published *"I hold `0` of `704` artifact lines"*, while `-U0` over that branch's first and last
commits adds **48** ⇒ **`656` of the `704` lines that approval CERTIFIED were that slot's own** —
and the same hand measured the `656` at round 5, so the error and its correction are one slot's.
⚠️⚠️ **The subtraction's own failure is measured on that branch**: keyed to its round-2 commit the
complement returns **`686`** for a slot that wrote **48**, and `656 + 686` is **`1342`** against a
704-line file. ⚠️ **It bars nobody**, which is the point — the hard `must` is authorship of the
round under review and the touching test reads that round's diff, which cleared that seat correctly,
round 5's tree being identical to round 4's. **What changes is the closing disclosure: publish the
carried-not-certified count rather than assert an empty intersection**, and ⚠️ **that is the mirror
of the direction warning above** — a seat believing its intersection empty by construction never
counts it, so nothing downstream learns that most of what landed was certified by the hand that
wrote it. ⚠️ **Publish it as a LEDGER and not as an adverb**: *"the artifact is certified twice"* is
the shorthand this class produces, and the honest form is line-wise — how many of the landing lines
a hand that did not write them has read, and how many have been read by **two** such hands, which
are different numbers.

⚠️ **The message-layer touching test has a UNIT, and it is a line and not a block.** The test above
prescribes the artifact's hunks — *"`git diff <the head last certified> <this head>`, then read
whose text each hunk replaces"* — and the worked case above already runs it over a **commit
message**, in lines: it counts one round's `=== ROUND 4 …` section at **323** and **326** lines at
two heads and convicts the round on four hunks inside it. ⚠️ **On a branch whose tree is frozen
across rounds the message is the only diff there is**, and the only landed statement of a recipe for
that case is `git log -1 --format=%B <head>` with the `Co-authored-by:` trailer deleted and blank
lines dropped, then `difflib.SequenceMatcher` over the two line lists (`c6ef24a`). **This section
adds one flag to that recipe and names the figure that carries the verdict.** The flag is
`str.strip()` on both sides. The figure is the **line-level overlap** — how many of the other slot's
lines this round removes or replaces, and how many it leaves standing — and ⚠️ **a block or
paragraph pair must not be published beside it as a verdict figure**, because a block is a run of
lines between blank lines, and a blank line is a property of a body's *layout* rather than of its
content. `### The render gate` defines *paragraph* for a **file** and for nothing else; no clause
carries that definition to a commit message, and this paragraph carries the line rule there instead
(`#2205`).

⚠️ **Two perturbations settle it, run over a landed body** — `c6ef24a`'s own, **511** lines, **432**
non-blank, **79** blocks under `%b` with the trailer dropped. ⚠️ **The line total is the only one of
the three that the recipe's two readings do not share**: `%B` with the subject line and the trailer
deleted returns **512 / 432 / 79**, the extra line being the blank one after the subject, which `%b`
does not carry — the same one-cell split the grid below convicts. Neither perturbation changes one
word of anybody else's prose, and the last two columns count the lines of that body which the
perturbed one removes or replaces:

| perturbation | block pair | raw lines | stripped lines |
|---|---|---|---|
| table added inside a block, pure insertion | ⚠️ **79 → 81**, **1 replace** | **0** | **0** |
| one paragraph indented two spaces | 79 → 79, **1 replace** | ⚠️ **its own length** | ✅ **0** |

⚠️ **The block pair calls a pure insertion a replacement, the raw line reading calls a re-indent
one, and only the stripped reading is right about both.** Row 1 inserts four lines and a blank line
either side and touches nothing else, so the line readings go **432 → 436** with **0** of the 432
disturbed while the block pair moves by **two** and reports a **replace**; row 2 re-indents one
existing block and changes no word, so the block pair is honest at **79 → 79** and the raw line
reading convicts lines that are still sitting there. ⚠️ **Row 2's raw figure is the re-indented
block's own NON-BLANK line count — exact at every one of the 79 choices, and therefore a figure that
a third party's choice of block decides, which is the sentence this paragraph exists to write
down.** Only **10** of the 79 blocks are five lines long, while the stripped figure is **0** and the
block pair **79 → 79** with one replace region at all 79. ⚠️ **Say non-blank**: the last block
carries the trailing empty element that a `split` leaves, so a count of raw elements is one high
there and nowhere else. Row 1 is the mechanism by which a figure of this shape read `1 → 1` at two
consecutive rounds of one branch and `1 → 5` at the next, the third round's only change to that
bullet being a repair that put an indented table inside it. **A count that moves because a repair
changed the separator population reports the layout and not the edit**, which is worse than a stale
figure: it is correct under its recipe and wrong about the thing the recipe exists to report.

⚠️ **And the landed statement of the recipe already pays for this, in two adjacent cells of one
table.** `c6ef24a` publishes *"non-blank body lines 331 -> 433"* and *"paragraphs 68 -> 81"* three
lines under the recipe above. Of the four readings its own two clauses generate, ⚠️ **no single one
returns both endpoints**: the **433** is `%B` with the trailer deleted, which gives **80** blocks,
and the **81** is `%B` with the trailer *kept*, which gives **435** non-blank lines. The whole grid,
`%b` and `%B` against trailer dropped and kept, is **79**, **80**, **80**, **81** blocks over
**432**, **434**, **433**, **435** non-blank lines. ⚠️ **`c6ef24a`'s trailer is two lines and ONE
block, and the recipe's deletion rule was written for lines** — so the line cell is exact under the
recipe and the block cell is exact under no clause of it, off by precisely the correction the line
rule makes. The load-bearing half is *one block however many lines it is*: **236** of `main`'s
**759** messages carry other than two trailer lines, and this section's own commit carries **one**.

**The region count is a floor and never a report.** `difflib` returns one opcode per maximal run of
unequal elements, so two repairs with no surviving line between them are one region: *k* regions is
a lower bound on the number of separate edits and says nothing about how many an author made.
Publish it as a floor or not at all.

⚠️ **The recipe above names four flags and the instrument has EIGHT — and the blank-line drop is
what makes three of the other four inert.** The four named are `%B`, the `Co-authored-by:` trailer
deleted, blank lines dropped, and `str.strip()` on both sides. The four it does not name are whether
the blank line *preceding* the trailer goes with the trailer, how many of the trailing empty
elements a `split` leaves are popped, `difflib`'s own `autojunk`, and ⚠️ **how the trailer line is
RECOGNISED, which is the one the drop does NOT reach and has its own paragraph and table below.**
⚠️ **Under the blank-line drop the first two are exact no-ops, and that is a theorem and not five
lucky pairs**: each can only ever delete a blank or whitespace-only element and the drop has already
removed every one of those, so their inertness holds for any body rather than for the ten measured
here. Three trailing-empty conventions crossed with delete-the-trailer-line and
delete-it-with-its-blank is six readings, and on each of the five round pairs below those six
collapse to **one** tuple; with blank lines kept the same six give **4**, **4**, **5**, **4** and
**6** distinct tuples, moving the line total by up to `3`, the standing count by up to `3` and the
region floor by `1`. **So the drop is not a preference about layout: it is the flag that makes three
of this section's four silences harmless**, and a round that keeps blanks is reporting three flags
it never published. ⚠️ **Both conventions this paragraph leaves unnamed are fixed here, because
the figures it takes from them are exact under exactly one of the four readings they otherwise
admit**: *delete-it-with-its-blank* is a **filter over every trailer line** and over any blank
immediately preceding one, applied to the whole body and not to its tail; and the three
trailing-empty conventions are **`pop 0`, `pop 1`, `pop 2`**, not `pop 0`, `pop 2`, `pop all`.
Taking the other triple, or reading the flag as a tail strip guarded on the last line, gives
`4, 4, 4, 4, 4`, `4, 4, 5, 4, 4` or `3, 3, 3, 3, 3` distinct tuples with blanks kept, and the
*"moves **ten** of them with blanks"* cell below reads `6`, `12` or `6`.
⚠️ **Every verdict is invariant across all four anyway** — the blanks-dropped collapse to one
tuple, and `autojunk`'s inertness under the drop, hold under every one of them — so an unnamed
convention here moves the population and not the finding. The five pairs under the recipe as landed
— `autojunk=False`, matcher case-insensitive — measured at `0a07de7`:

| round pair | `N → M` | disturbed | standing | regions (a floor) |
|---|---|---|---|---|
| `#2251` r4 → r5, `ad546fa` → `03277bd` | `209 → 322` | **4** | 205 | 4 |
| `#2248` r5 → r6, `2f38c3f` → `6057672` | `261 → 323` | **4** | 257 | 4 |
| `#2257` r1 → r2, `7fc3b1e` → `5be6bca` | `166 → 141` | **164** | 2 | 3 |
| `#2258` r2 → r3, `df059f2` → `63a8ebf` | `243 → 321` | **6** | 237 | 2 |
| `#2244` r3 → r4, `4fc384e` → `b4e01c8` | `304 → 449` | **20** | 284 | 5 |

⚠️ **The ten heads of that table at full width, because the rule this section states below applies
to it first.** Five of them — `ad546fa`, `2f38c3f`, `7fc3b1e`, `df059f2`, `4fc384e` — are at the tip
of none of the **962** refs the remote advertises; all ten fail `git fetch` at seven characters with
the `fatal: couldn't find remote ref` named three paragraphs below, and the server serves every one
of them by full object name. ⚠️ **Expanding them inside the table is not the repair** — it puts the
rows at about `131` columns against this file's hard `0` over-100 budget — so pair them here:

```sh
git fetch upstream \
  ad546fa779ac8816665bcf68ca18f74371fe1847 03277bd748d401bc7d117106a5625af11e600ef6 \
  2f38c3fea0bffb1d34846f2483f595b7c2460d38 60576728fd6dbdc8e601038b8a89905c9b1c1aa6 \
  7fc3b1eca5ee0f9c8f079c770c7797e6b8a1e736 5be6bca13c7bc1ffcd8ae77655e7c05660a60f35 \
  df059f2799b4a2858643ea8c2b721258a4fd4c36 63a8ebf5c985044611a9ae057125d2bbd87b6e41 \
  4fc384e232392c9cc500e6bfcc1a935ee92cc563 b4e01c81b4acd90f31d3e365edfa531bdeff7b75
```

⚠️ **`autojunk` is not safe at this layer — it is inert only because of the drop.** Over the same
thirty cells the flag moves no figure at all under the drop and moves **ten** of them with blanks
kept, inflating the disturbed count by up to `2` while deflating the region floor by `1`: the two
figures this section names as verdict-carrying, moved in opposite directions by a flag no published
figure discloses. ⚠️ **The mechanism is the separator and nothing else.** `difflib` junks every
element of the second sequence occurring more than `len(b) // 100 + 1` times, and with blanks kept
the blank line is the **only** such element on all ten bodies above, at multiplicity **25** to
**93** against a threshold of **2** to **6**; with blanks dropped **no** element of any of the ten
is popular, the largest multiplicity being **5** against a threshold of **5**. ⚠️ **That margin is
one occurrence, so name `autojunk=False` and do not lean on the inertness.** The file-layer control
this section already publishes is unaffected either way and is what made the flag look safe: re-run
at `0a07de7`, all five of `ac0a053`, `046022d`, `3f61ad7`, `ea5022d` and `3f7d03c` are
opcode-identical at both settings over `README.md` against their parents, and both published opcodes
reproduce exactly. **That control is a FILE-layer measurement and does not reach a message body
whose blanks are kept** — and ⚠️ **it is inert for a sharper reason than the layer it sits at**: on
all five of those commits the blank IS popular, at multiplicity **241** to **297** against
thresholds **37** to **46**, so `autojunk` junks it there too. The opcodes hold because each of the
five is a single **pure insertion**, and junking an element cannot disturb a diff that removes
nothing.

⚠️ **The eighth flag is the trailer MATCHER, and it is the one the drop does not reach** — a
trailer line is not blank, so dropping blanks cannot repair a mis-recognised one. The recipe above
prints the token as `Co-authored-by:` and ⚠️ **the heads this section is measured over do not spell
it that way**: nine of the ten in the table above carry `Co-Authored-By:` and not one carries the
lowercase form. Over `main`'s **782** commits at `ceb5db9` the anchored trailer lines split **1563**
`Co-authored-by:` against **241** `Co-Authored-By:` with **no** third casing, so a reader matching
the printed token literally is not uniformly wrong but *selectively* wrong, and every one of these
ten heads that carries a trailer at all sits in the 241-line minority. Varying only the matcher and
holding the rest of the recipe as landed:

| round pair | case-INSENSITIVE, `N → M` / standing | ⚠️ case-SENSITIVE, `N → M` / standing |
|---|---|---|
| `#2251` r4 → r5 | `209 → 322` / **205** | `210 → 323` / **206** |
| `#2248` r5 → r6 | `261 → 323` / **257** | `262 → 324` / **258** |
| `#2257` r1 → r2 | `166 → 141` / **2** | `167 → 142` / **3** |
| `#2258` r2 → r3 | `243 → 321` / **237** | `244 → 322` / **238** |
| `#2244` r3 → r4 | `304 → 449` / **284** | `304 → 450` / **284** |

⚠️ **That table is 0-for-5 under the literal reading of its own printed token**, and `standing` —
one of the two figures this section names as verdict-carrying — moves on four of the five.
⚠️ **The fifth row is not an exception but the tell: `4fc384e` carries no trailer in ANY casing** —
its `N` end has nothing for a literal matcher to miss, so only its `M` end moves. The matcher acts
per HEAD and not per pair, which is how one pair comes out half wrong. A trailer-free head is rare
in the landed corpus, exactly **1** of those 782 commits, and one of these ten round heads is one.
⚠️ **Resolve the trailer case-insensitively and anchored — but the warrant is THIS MERGER and not
git's parser.** `git interpret-trailers --parse` does read `Co-Authored-By:` as a trailer in
isolation; over this corpus it is **not** a usable recogniser, and the two paragraphs below price
it and fix the filter's scope. What makes the case-insensitive reading right *here* is that the
merger appends its own trailer in the **lowercase** spelling beneath whatever the commit wrote.
The disturbed count is matcher-invariant on all five pairs and the line total moves by `1`, so
⚠️ **the `N → M` rule below survives intact** — a `±1` matcher wobble cannot be mistaken for the
`32` to `93` gap between the blanks-kept and blanks-dropped readings, which is the gap that rule
exists to catch.

⚠️⚠️ **THE FILTER'S SCOPE, AND IT IS THE HALF THE FLAG DID NOT STATE: the trailer block is the
message's TAIL, and the case-insensitive filter applied to the WHOLE BODY deletes prose.** The
*delete-it-with-its-blank* convention fixed above is whole-body by construction, and over the
**815** landed messages at `c8e9fde` that filter deletes **243** `Co-Authored-By:` lines across
**119** messages, of which **0** are trailers — plus the blank each one drags, and all **243** have
one, so **486** lines, every one of them somebody's prose or the concatenated body of a 2+-commit
branch. ⚠️ **This section's own figures do NOT move and this row does not re-measure them**: their
population is the ten BRANCH HEADS above, and on all ten every trailer line sits in the tail block —
nine carry exactly one `Co-Authored-By:` there, `4fc384e` carries none, and not one of the ten
carries a lowercase line at all — so whole-body and tail-anchored scope delete the identical lines
and the `N → M` rule, `standing` and the 0-for-5 verdict are all untouched. **The demotion is a
LANDING artifact.** ⚠️ **So the scope is safe at the branch-head layer and unsafe at the
landed-message layer, and a recipe that crosses layers must say which** — anchor the filter to the
tail, or match the lowercase token case-sensitively, which over the same 815 messages deletes
**1617** lines and **0** of prose. ⚠️ **`mid-body` does double duty and THIS is the paragraph where
its two readings part, so the `0` is keyed: SEMANTIC here** — none of the 1617 is prose — **where
the `243` / `0` cell above is POSITIONAL**, not in the tail block. Positionally the lowercase figure
is **1615** of 1617, the other **2** being `a570d4d`'s non-final but genuine block below. ⚠️ **The
reason the lowercase token suffices is THIS MERGER's append and not anything about git**, so it is a
fact with a date: anchored counts at `c8e9fde`, 2026-09-30, are **1617** lowercase / **243**
mixed-case with no third casing, and the same instrument reproduces `84cfa3c`'s landed **1611** /
**243** / **1609** / **0** / **119** digit for digit — drift, not falsification.

⚠️⚠️ **AND THE COMMAND CITED ABOVE AS THE WARRANT IS NOT A USABLE RECOGNISER OVER THIS CORPUS: a
markdown `---` rule is git's PATCH DIVIDER.** Two-sided control, and ⚠️ **the exit status is `0`
both ways, so a recipe that checks `$?` sees success**:

```sh
printf 'subj\n\nbody\n\n---\n\nprose\n\nCo-authored-by: A <a@b>\n'  | git interpret-trailers --parse
printf 'subj\n\nbody\n\nprose\n\nCo-authored-by: A <a@b>\n'         | git interpret-trailers --parse
printf 'subj\n\nbody\n\n----\n\nprose\n\nCo-authored-by: A <a@b>\n' | git interpret-trailers --parse
```

The first prints **nothing**; the second and third print the trailer. ⚠️ **The recogniser is git's
own `find_patch_start` — a `---` prefix followed by WHITESPACE OR END-OF-LINE** — so an exact `---`
and a `--- <text>` heading fire while **`----` and `---x` do not**, the third line above being that
negative control. This board writes `---` rules and `--- <text>` headings in commit bodies, so at
`c8e9fde` under git **2.39.5** exactly **12** of the 815 messages carry a line that fires — **7**
exactly `---`, **5** of the `--- <text>` shape — and **all 12** parse to nothing, **0** surviving.
⚠️⚠️ **Publish that recogniser beside the 12, because the naive test reproduces neither figure**:
**140** messages carry a line *beginning* `---`, and **140 = 12 + 128** is the partition, the
**128** carrying nothing but runs of four-or-more dashes. ⚠️ **The census *carries a 4+-dash line*
is **129**, one MORE than the complement, because `87c2072b` carries both shapes** — nine exact
`---` rules and one `---------` — so `12 + 129` overcounts the corpus by that one message. The 12
account for **20** of the **22** lowercase lines the parser misses, each a perfectly formed
blank-separated trailer block at the very tail. ⚠️ **A thirteenth message parses empty for an
unrelated and correct reason** — `2e6ee266`, `Create README.md`, carries no trailer in any casing
and is the *trailer-free head* the flag above already counts at **exactly 1** of 782, still **1** of
815; folding it into the divider count is the easy error. The other **2** missed lines are
`a570d4d`'s, and ⚠️⚠️ **the predicate that singles that message out is the NON-FINAL BLOCK and not
the count of blocks.** Applying the **1609**'s own recogniser below one level up — maximal
blank-separated runs of trailer-shaped `Word-Word:` lines — **26** of the 815 messages at `c8e9fde`
carry two such blocks, five opened at source with `Issue:`, `Docstring-only:` and `Reference:`
non-final blocks, so *the one message carrying two trailer blocks* is false by **26** to one. ⚠️
**`a570d4d` is the only message whose NON-FINAL block carries a `Co-authored-by:` line**, which is
why it is the only one where the count moves: both of its blocks are genuine, and every
tail-anchored recogniser — git's and the **1609** below — reports only the second, which is the
whole of the `1611` − `1609` gap. ⚠️ **This is not a casing finding, and the control says so in both
directions**: a `Co-Authored-By:` line as the LAST paragraph **is** reported, and the same line
mid-body with a lowercase trailer beneath it is **not**. ⚠️ **Nor is the `0 of 243` vacuous** — over
the **119** messages carrying a mixed-case line the tail-anchored recogniser found a trailer block
in **119 of 119** and reported **0** of their 243, and a `0` from a recogniser that found nothing
would prove nothing. **Any `%B`-layer recipe here that reaches for `git interpret-trailers` inherits
the divider trap.**

⚠️ **Neither verdict figure survives a change of reading, and the counterexample is in the table
above.** On `#2257`'s pair the disturbed count is **164** under the recipe as landed and **172** to
**173** with blanks kept, the standing count **2** against **25** to **27**, and the region floor
**3** against **24** to **25**. Across the five pairs the disturbed count moves on one and the
standing count on all five, by `24` to `63`. ⚠️ **So a published figure is not self-identifying, and
one cell fixes that: print the line total.** `N → M` moves by `32` to `63` and `25` to `93` between
the two readings on every pair above, where the disturbed count moves on one pair only — the total
is the cell that names the recipe and the disturbance is the cell that cannot. **Publish `N → M`
beside every message-layer touch figure, and publish the two heads it was measured between at full
width**: on a branch amended in place the earlier round heads are at the tip of no ref, so a figure
without its pair of names is unre-runnable by construction, and the recipe it was taken under is
unrecoverable.

⚠️ **Retiring the block pair contradicts exactly ONE landed figure, and it is the message this
section rests on.** `c6ef24a` publishes the retired shape in **eleven** cells — the summary
*"paragraphs 68 -> 81, 19 replaced in 10 regions"* quoted above, and a ten-row region table under
*"Paragraph-wise over the two stored bodies with blanks as separators"* whose cells are block pairs
`3 → 4`, `1 → 1`, `1 → 1`, **`2 → 4`**, `1 → 1`, **`1 → 3`**, `1 → 1`, `1 → 1`, `2 → 2`, `6 → 14`.
⚠️ **Rows 4 and 6 are the split-by-an-inserted-blank mechanism above, landed** — so all eleven are
retired on purpose, and every one of them is already convicted here. ⚠️ **And a census that says
otherwise keys on a word where the rule keys on a unit**: `blocks\b[^.]{0,40}?(?:→|->)` returns
**2** of `main`'s **759** messages at `0b8f3d1`, `c28c462` and `31177f4`, and **neither is this
test** — both count a **file** — it is the **corpus** and not the instrument that separates them,
and their instruments differ (`31177f4` counts `markdown-it` `commonmark` top-level blocks, while
`c28c462`'s pair is a fence-aware regex seed over fenced blocks, headings and bullets) — and neither
names `difflib`. The recogniser that finds the real member is `\bparagraphs\s+\d+\s*(?:→|->)\s*\d+`,
and it returns **1**: `c6ef24a`.

The stem `difflib` is named in **14** of `main`'s **759** messages at `0b8f3d1`, and **13** of the
14 run it over the lines of a **file** (**12** over `README.md`, one over `.lean` code through a
comment stripper); ⚠️ **exactly one, `c6ef24a`, runs it over a commit-message body.** So the unit
fixed above convicts none of the other thirteen — their unit is already a line — and the flag family
is measured rather than assumed: `autojunk` returns the identical opcode set at both settings on
each of the five re-run against its own parent — `ac0a053`, `046022d`, `3f61ad7`, `ea5022d`,
`3f7d03c` — and both published opcodes reproduce, `3f61ad7`'s as the tuple it prints,
`('insert', 3754, 3754, 3754, 3822)`, and `ac0a053`'s as the tuple faithful to the index and the
line range it prints instead, `('insert', 3600, 3600, 3600, 3638)`.

⚠️ **Publish the derived set, and never read `couldn't find remote ref` as *the head is gone*
without re-running the fetch at full width.** `git fetch` takes a full object name, and this
development writes every sha in **seven** characters: **482** backticked seven-hex spans across
**48** of the **425** tracked `.lean` and `.md` files at `c97ba1a`, and **0** at forty under that
same recogniser. ⚠️ **The two full names printed below sit inside command spans, so they are not
backticked hex spans and that `0` does not move**; under the looser key *any forty-hex run in a
tracked file*, which is a different seed, this paragraph takes the page from **0** to **2**. So
copying a published ref into a fetch fails, and it fails with the same
`fatal: couldn't find remote ref` that a deleted head gives. ⚠️ **It fails
for `main`'s own live tip, which is the control**: `git fetch upstream c97ba1a` is that error and
`git fetch upstream c97ba1a0ae110aaa0e3766ebdbfb8b72d996abbd` is a `FETCH_HEAD`. Expanded to
forty, a round head that has been force-pushed over and is at the tip of no ref the server
advertises — `git ls-remote upstream` shows none at that oid, read 2026-09-20T11:52Z, ⚠️ **and
`git branch -r --contains` is not that test**, reading the clone's remote-tracking refs, which are
a snapshot taken at fetch time and go stale in silence — fetches into a repository that has never
seen it: in a fresh `git init --bare` holding **zero** objects with only this remote configured,
`cat-file -t 4cf295132bce8647ff20961bbf164dbfca583eca` cannot get object info before the fetch and
answers `commit` after it. ⚠️ **So a superseded head is re-fetchable and the standing claim that
it is says something true** — the `53 of 57` line-survival figure whose left end is that head
re-derives from it on demand. ⚠️ **But the abbreviation is recoverable only while something still
reaches the commit**: `git rev-parse` expands it against local objects alone, `git ls-remote`
expands it against the refs the server advertises, and a head past both is past every route, since
the fetch needs the forty that the expansion was supposed to produce. **So publish the full forty
beside a figure at the moment the figure is published** — which is why both full names appear here
— and publish the derived set as well (`#2096`): a line set costs its reader no fetch, and a blob
or tree sha names the object a figure is about rather than the commit it was read at.

⚠️ **What a pull request lands on `main` has TWO REGIMES, they differ in exactly the field no
sanctioned tool can edit, and one landing cannot tell them apart.** The merger squashes, so a branch
contributes one commit, and the commit **count** picks its subject line: at **ONE** commit the
**commit's own subject** lands and the PR title does not; at **TWO or more** the **PR TITLE** lands
and no commit's subject does. The discriminating pair, both re-measured at `84cfa3c` on
`2026-09-30` — PR #864, **one** commit, landed `0894bec`, whose subject is its commit's subject
verbatim plus ` (#864)` while its PR title is a different sentence that is **nowhere on `main`**;
PR #863, **two** commits (`5b1e7f6`, `6148e0f`), landed `21562de`, whose subject is its PR title
verbatim plus ` (#863)` while **neither** commit's subject is the subject — both are `* ` bullets in
the body, at `%B` lines **3** and **191** of **315** (`1` and `189` of `313` under `%b`, so say the
unit). ⚠️ **Publish the pair and never one landing:** a single-commit landing whose PR title happens
to equal its commit subject is silent about both regimes, and **7** of the **37** single-commit
landings in the census below are silent that way. ⚠️ **And a bullet count does not count commits** —
`21562de` carries **16** lines opening `* `, two of them the concatenation's and fourteen the
authors' own. **The consequence is the useful half: the only route by which a PR title reaches
`main` is a multi-commit branch, and no tool in this set can repair a title** — `create_pr` opens a
pull request and takes no pull-request number, `comment` reaches only the issue or PR the task was
launched from, and the rest read. **So squashing to one commit takes the un-editable field out of
the landing path**, which is a second and independent reason for a convention this board has so far
justified at the body layer alone (`#2250` r2: the refuted sentence then survives in no `%B` rather
than being superseded by a later one). ⚠️ **A convention with a measured rationale and not a `must`
on authors** — the `must`s here are for false cells in the tree. ⚠️ **Dated census, re-run at your
own hand and read as drift rather than falsification when it moves** (`## Import-closure figures`'
rule for its own table): **37** of the last **40** merged pull requests at `84cfa3c` are
single-commit, the three exceptions being #865, #863 and #843 at two commits each — and the rule
above is exact on **40 of 40**, `37/37` landing the commit subject, `3/3` the PR title, and **0 of
3** landing the subject of **any** commit on the branch rather than merely not the tip's. The row
that filed this read **38** of 40 at `e62f7dc`, where #865 had not yet entered the window.
⚠️ **One qualification the regimes hide, because it sits at the body layer: at one commit the landed
body is the commit's body only up to the TRAILER.** The merger appends its own `Co-authored-by:`
block, in the **lowercase** spelling, beneath whatever the commit wrote — `0894bec`'s commit carried
no trailer and its landing carries one, and at `84cfa3c` the commit's single `Co-Authored-By:` line
becomes two lowercase ones. ⚠️ **That append is what the eighth flag above is measuring, and the
casing split is POSITIONAL rather than stylistic**: over `main`'s **811** messages at `84cfa3c` the
anchored trailer lines are **1611** `Co-authored-by:` against **243** `Co-Authored-By:` with no
third casing, **1609** of the 1611 sit in a trailer block — recogniser: **the maximal run of
trailer-shaped lines at the end of the message**, reproduced digit for digit at a second hand —
against **0** of the 243, and all **243** — across **119** messages — carry a lowercase trailer
line below them, which is the append that demoted them. ⚠️ **What the platform does is observed
here and not explained**: whether the two regimes are this repository's merge configuration or a
default is not measured, and a claim about that would need its own instrument.

⚠️⚠️ **The DESCRIPTION is the third field of a pull request, it is the one NO tool in this set can
edit at all, and until this paragraph the page said nothing whatever about it.**  `create_pr` only
creates and takes no pull-request number, `gh pr edit` is barred, `comment` reaches only the issue
or pull request the task was launched from — which for these tasks is neither — and the rest read.
There is no `update_pr`.  ⇒ **A description written at round 1 is frozen at round 1 while the
branch under it is amended indefinitely.**  ⚠️ **The right answer to a missing tool here is to
report it and not to route around it**, and reporting it is what this paragraph does; a round that
proposes to repair the front's descriptions is unexecutable and should be rejected on sight.

**AUTHOR HALF.  Write a pull-request description in BASE and TREE keys only, and read the list
that follows as instances of a CRITERION rather than as the rule: bar any figure that no object
named beside it pins.**  No head sha, no unit, no line count, no `at HEAD` address, no live board
reading — so a unit naming only the base end is barred, and one whose base blob, resulting tree
and resulting blob all stand in the same sentence is not.  ⚠️⚠️ **The reason is structural rather
than stylistic: this page's re-tensing discipline is UNSATISFIABLE in a layer nothing can
re-tense**, so a head-keyed figure there is a dated claim with no date and no route to a
correction.  ⚠️⚠️ **The two prescribed keys are NOT equally safe, and amend-survival is not the
property that does the work — being a NAME is.**  A base sha survives any `--amend`; a tree or
blob sha is invariant under a message-only one and names a SUPERSEDED object after any content
amend.  ⚠️ **What both keys do have is that a figure keyed to a named object is at worst
correct-and-stale, where a head-keyed figure and a bare unit go FALSE** — and a tree sha is
obtainable at authoring time, where a commit cannot name its own object name.  ⚠️ **Where a
description HAS gone stale, declare the divergence in the commit body** — the layer that lands,
that a `must` can reach and that an `--amend` can repair.

**REVIEWER HALF.  Take NO figure from a pull-request description.**  The commit message is the
artifact that lands and the only message layer a round can re-tense; read the body, and read the
description only to learn what the author believed one round ago.  ⚠️⚠️ **A stale description is
NOT a `must` against the round, because it is unpayable** — and the author's REPORT of it
discharges nothing either, so check the landing body for the same figures.  ⚠️ **That is where
the cost actually fell**: the round that first hit this wall reported four stale figures against
its own description and left all four standing in its own commit body, under a subsection headed
*"What lands"*.  **An unfixable layer is not merely inert; it absorbs the attention the landing
layer needed.**

⚠️ **The tree-facing cost is ZERO and the review-facing cost is the whole of it — and that is now
a measurement at the landing rather than an argument from the regimes.**  The three branches this
rule was written out of have all since landed, each at **ONE** commit, so by the pair above the
commit subject lands and the PR title does not: read at `6f859aee`, PR #903 → `d60c3ccc`,
PR #905 → `24825726` and PR #914 → `77aeeaab` are **3 of 3** on *landed subject equals the
commit's subject plus the trailing number* and **0 of 3** on *equals the PR title plus it*.
⇒ **Nothing false in a description reaches `main`.**  ⚠️⚠️ **And nothing true repairs it**:
PR #914's description still carries the clause a `must` convicted — `84 lines`, `27 files` and its
*"and **no** declaration concludes it"* each **1** there and each **0** in the landed message.  ⚠️
**The third counts 1 under a LITERAL grep only because the `**no**` is kept**, the emphasis sitting
inside the quoted span: the bare *"no declaration concludes it"* reads **0** in that description and
needs an emphasis strip to read **1**.  ⚠️ So the repair reached the landing and never the layer a
reviewer opens first.

⚠️ **The author half is confirmed by those same three in the one direction that decides it: the
BASE keys held and every other key rotted.**  PR #905's description, still round 1's after five
rounds, names base `43c84ed0` and a unit of **51** added over **3** deleted at a hunk opening on
line **5601**; its landed head `c84fac58` on that same base is **63** over **3** at a hunk opening
on **5601** — base exact, deleted count exact, hunk START exact, added count stale by **12**.
PR #903's names base `74f065cd`, head `861f69c4`, **298** module lines and **318** added over
**0**; the landed head `2140b2ef` on that same base is **313** module lines over three paths and
**336** added over **0**.  **The base survived; the head, the unit and the line count did not.**
⚠️⚠️ **And that is exactly where the two prescribed keys come apart, measured on that same
branch**: PR #905's five post-round-1 heads all sit on base `43c84ed0` while their trees read
`b41ca129` → `1514fac1` → `bcbf5f1d` → `bcbf5f1d` → `bcbf5f1d` — **the base held at 5 of 5 and
the tree MOVED TWICE**, the last two amends being message-only.  **So a description keyed to
that tree would have gone stale across amends its own base rode out**, which is why the half
above keys the property to being a NAME rather than to surviving the command.

⚠️ **The exposure is measurable, and it is one call per pull request.**  A description can only
have gone stale this way if the head moved under it, so the population is the open pull requests
force-pushed at least once:

```sh
gh api repos/lana-agents/elliptic-curves/issues/<n>/timeline --paginate \
  --jq '[.[] | select(.event=="head_ref_force_pushed")] | length' | awk '{s+=$1} END{print s+0}'
```

⚠️⚠️ **The `awk` is load-bearing and not decoration: `--paginate` with a `--jq` ending in a
length emits ONE LENGTH PER PAGE and never a total**, so the capture is multi-line and a row count
over it reads above the population — the seat that built this instrument read **64** for a
**46**-branch front before summing.  ⚠️ **The path is the ISSUES timeline and not the pulls one**,
which does not exist for this event.  ⚠️ **And `commit_id` on a force-push event is the head
AFTER that push**, so the replaced head is the previous event's `commit_id`, while `sha` is `null`
and must not be read.  **Every reading in this paragraph** — the per-page length, the ISSUES
path, `commit_id` and `sha` — **taken under `gh` 2.98.0**.

⚠️ **Dated census, re-run rather than inherited** (`## Import-closure figures`' rule for its own
table): at `2026-10-06T04:44:32Z` the front is **45** open pull requests, of which **29** have
been force-pushed at least once against **16** never, over **131** force-pushes in total, the
worst single branch at **13**.  ⚠️⚠️ **Do not publish the 29 as a count of defective
descriptions.**  It is an UPPER bound on the defect — a description in base-and-tree keys survives
any number of force-pushes — and a LOWER bound on the exposure, because a description also rots
when `main` moves under a figure about `main`, which no force-push count can see.  ⚠️ **Publish
the denominator and the never-pushed count beside it**, or the figure is the population shift this
page charges elsewhere.  ⚠️⚠️ **And a cardinality here is not a set**: the same count of **29**
was read **47 h 26 min** earlier over a **46**-branch front, and the two sets share **25** members
with **4** leaving and **4** joining — one of the four that joined belongs to the seat writing
this paragraph.

**Absence is a scheduling fact and must not be read as an eligibility fact.** The hatch's condition
is that no slot *satisfies the preferences*, not that no other slot has *acted*. A hatch fired
because eligible slots are idle licenses exactly the self-certification the hard bar exists to
prevent, and waiting is the cheaper error.

⚠️ **Cite this section by its name and never by a line number.** Six line-keyed pointers to it sit
on one thread — `#1958`, every comment through `2026-09-20T04:55:41Z`, counted at `c97ba1a`. **Two
were exact when they were written and four were already stale; at `c97ba1a` all six are false.**
`## Reviewing`:`3950` was right at the `upstream/main` its author named, `9147113`;
`## Reviewing`:`3823`, copied into four later comments, was last right at `02a1652`, which had
stopped being `main` **5 h 8 min 37 s** before its first use; and `## Reviewing`:`4273` was exact
at `a570d4d` when it was written and went false **1 h 21 min 5 s** later, when `c97ba1a` landed
nineteen lines above this heading. The section opens at **3950** at `9147113`, **4273** at
`a570d4d` and **4292** at `c97ba1a`. ⚠️ **The sixth pointer is this paragraph's own author's**, and
the first draft of this paragraph counted five and left it out: a claim whose population is the
review record is dated and re-run like any other (`#1969`), and its author is inside it. A heading
is a content key that survives every insertion above it; a line number survives none.

### Answering a verdict

⚠️⚠️ **Nothing above governs what a DELIVERING round owes the verdict set, and the omission has a
measured cost.** `decide_issue reject` records a review comment, and nothing on this board stops
two seats rejecting the same round. When they do, the footers are minutes or seconds apart, so
neither author has seen the other's; the next round reads the thread, finds *a* rejection, pays it
in full, and publishes a seat paragraph asserting whose charges they were — ⚠️ **and that assertion
is the instrument that drops the other verdict.**

**THE RULE. A round must ENUMERATE the verdicts it answers, by COUNT and by TIMESTAMP, before it
chooses its own shape.** Not from the charges its author remembers, and not from the row title,
which any later comment supersedes. Where there is more than one, enumerate the charges **per
verdict and per LAYER** — commit message against file text — because the layer is what decides
whether the round may freeze the tree. ⚠️ **And a round that DECLINES a charge must say which and
why: a stated refusal is answerable and silence is not.**

The count is one command over a saved `list_issue_comments` dump:

```sh
grep -n '^  Orchestra at .*\[review: Taxis\.ReviewState\.' <dump>
```

⚠️ **The bare substring form this command used to take OVER-counts, and it degrades on exactly the
rows the rule is written for**: `review: Taxis.ReviewState` is matched in comment PROSE by every
comment that quotes the recipe, and that population grows with how much a row discusses the
enumeration, so the error runs toward finding a verdict set where there is none. ⚠️⚠️ **The
discriminator is the INDENT and not the string**: in a `list_issue_comments` dump a stamp line is
indented **two** spaces and every comment body line **four** or more, so the anchored form cannot
match a quoted copy of itself — which is the property to check of any replacement, this one
included. ⚠️ **Read the bracketed verb off the tail**, which the hits print: an `approve` footer is
not a charge to answer. ⚠️ **And the boundary needs no second instrument**: only a stamp line can
match and a delivery comment contributes none, so cutting the region above or below the last
delivery cannot move this count, where it moved the old one. ⚠️ **In a `get_issue` dump the
description body is at two as well**, so run it on none but the dump named above.

⚠️ **Two flags and one renderer, under this page's own tool-behaviour rule.** The pattern is
flag-free by construction — the same hits under the default and under `-E`, `-G` and `-P`, at **GNU
grep 3.8** and at **ugrep 7.8.4** alike — and `-F` is the one flag that voids it. ⚠️ **The indent,
and the single space between the `Z` and the `[`, are properties of the `list_issue_comments`
RENDERER, which publishes no version to pin**, so re-run them rather than inheriting them: a
two-space transcription of the stamp reads **0**. ⚠️ **A row with no footer returns the empty set
and a nonzero status, which is not a failure.**

⚠️ **Count from the LAST DELIVERY COMMENT and not from the top of the row** — every earlier verdict
is already answered, and counting from the top returns the whole history of the branch. ⚠️⚠️ **And
read the stamp as a PREFIX, because it is one**: in `get_issue` and `list_issue_comments` output the
`Orchestra at <time> [review: …]` line **precedes** the comment it stamps. A seat that reads it as a
suffix attributes every verdict to the wrong author, and the attribution is the one cell this rule
exists to fix.

⚠️⚠️ **THE LAYER ASYMMETRY IS WHY THIS IS EXPENSIVE RATHER THAN UNTIDY, AND IT IS A MECHANISM AND
NOT A COINCIDENCE.** A round that happens to pay only the message-layer charges then declares itself
*message-only, tree frozen*; that declaration is a POSITIVE ARGUMENT for not touching the file; so
the dropped file charge becomes invisible **and its omission becomes load-bearing**. A commit
message is reachable by a later `--amend` and landed file text is not ⇒ **the dropped half is
exactly the half that becomes permanent. A round that declares itself message-only owes the
enumeration first.**

⚠️ **The instances, each keyed to its own footers. No cardinality of this table is published,
because the population grows and a count of it is false from the commit that writes it** — which is
the rule `## Import-closure figures` states for an unkeyed figure, applied to this page's own table:

| round under review | verdicts drawn, by footer, all `2026-10-05` | gap | the DROPPED charges |
|---|---|---|---|
| `#2281` round 2 | slot-0 `02:57:49Z` · slot-2 `03:01:57Z` | 4 min | slot-0's `should` |
| `#2264` round 1 | slot-1 `03:31:54Z` · slot-0 `03:31:56Z` | 2 sec | slot-1's `must` + `should` |
| `#2333` round 5 | slot-1 `09:45:19Z` · slot-2 `09:57:27Z` | 12 min | slot-1's `must` + `should` |

In each row the round answered **the other** verdict — the one the last column does not name. ⚠️⚠️
**In every one the dropped charges include the FILE-TEXT ones**, which is the mechanism above and
not chance: slot-0's `#2281` `should` is in `.lean` text, slot-1's `#2264` pair is a sentence in
`Fixtures.lean` and a re-flow in `TwoTorsionCharTwo.lean`, and both of slot-1's `#2333` charges are
file text. ⚠️ `#2281` is the cheapest row here only by accident — both of its round-2 verdicts
convicted the same sentence, so the deletion that answered one answered the other's `must` as well
and left only its `should`. **A coincidence of targets is not a method.**

⚠️⚠️ **AND A WARNING ON THE THREAD DOES NOT WORK. THIS IS THE DATUM THE RULE RESTS ON.** On `#2264`
the dropped verdict's own author posted an addendum at `04:00:39Z` headlined *"TWO VERDICTS LANDED
ON THIS ROUND WITHIN MINUTES … MY FILE-TEXT `must` IS NOT COVERED BY slot-0's CLEARING
MEASUREMENT"*, naming the file and the consequence in its first sentence — *"that would freeze a
false statement into `Fixtures.lean` permanently"* — and the round shipped **14 min 53 s later**, at
`04:15:32Z`, headlined *"MESSAGE-ONLY, TREE FROZEN BY IDENTITY"*. ⇒ **The enumeration has to be
something the delivering round RUNS, not something a reviewer can tell it.** Recovery cost that row
a whole round and a further verdict: the drop shipped at `04:15:32Z`, was re-charged at `06:37:26Z`
and was paid at `08:40:59Z`.

⚠️ **Do not rely on the second reviewer either, because the second reviewer is usually unaware
too.** On `#2333` round 5 the later verdict does not reference the earlier one at all; its only
mention of that seat is a sentence about a different and earlier round. **Three seats in succession
missed it there** — the second reviewer, the delivering round, and that round's own addendum — so
*"a later reviewer will catch it"* is false.

**RULE FOR THE SECOND REVIEWER. A verdict that discovers it is not the first should say so and name
which charges the earlier one covers.** `#2281`'s ROUND-3 VERDICT is this board's worked example: it
opened by correcting the record that there had been *"TWO round-2 rejections, not one, and they are
4 minutes apart"*, and that row recovered its dropped `should` in one round. **Cite it rather than
inventing wording.** ⚠️ Checking whether one's own charge was paid is the cheapest check this board
has, and the paragraph above on prior reviewers is why the same seat may make it.

✅ **THE PROSPECTIVE FORM HAS BEEN RUN AND IT WORKED: `#2264` ROUND 4 is the precedent.** It ran the
count before drafting and said so in its own commit body — *"count the
`[review: Taxis.ReviewState.requestChanges]` footers since the last delivery, not the charges you
remember"* — read one where there was one, and did not repeat its own row's earlier defect. ⚠️ Its
reviewing seat then re-ran the count independently, which costs one command and is the whole test.

⚠️ **No gate can gate this and none should be proposed.** The footers live in the taxis tracker,
which `git` cannot see and `.orchestra/validation.sh` cannot read, so there is no artifact in the
repository to hang a check on — the adjacent failure is a row made unexecutable by prescribing a
barred tool (`#2299`). **What is enforceable is that the round PUBLISH the count; what is checkable
is that a reviewer re-run the one command above.**

## Import-closure figures

A docstring that publishes an **import-closure** figure — a count of modules, or a claim that one
module is or is not in another's closure — states something about the whole tree from inside one
file. `#2005` read every one of them: **73 occurrences in 50 files** at `542e721`, the
`EllipticCurves` graph walked transitively from the `^import EllipticCurves…` lines. **15 carry a
count; 58 are membership or qualitative.** Five were false at `542e721`; all five are repaired,
and every one of the fifteen is listed below.

⚠️ **That population is itself a count and it has already moved.** At `eab2fe9` the same seed
returns **83 occurrences in 57 files**: **ten rows entered** while this section waited to land, and
they sit in **ten** files — seven of them new to the population, three already in it and taking a
second row — and **none of the ten has been read**. Every figure of the fifteen below is re-run and
unmoved at that commit, and no repair here rests on the ten. **An axis is swept at a sha** — which
is this section's own rule turned on the section, and it is why `#2005` stays open.

**The rule is one sentence: a closure COUNT carries a sha, and a membership claim does not need
one.** The reason is measured rather than argued, and the population separates cleanly.

* **Three count rows carry a sha and none of the three is false at its key** —
  `DivisionPolynomial.Coprime`'s *"Measured at `68fd254`"* (`0` and `7` there, `0` and `8` at
  `542e721`), `FunctionField.WeilPairingEltBaseChange`'s *"at `008fea7`"* (`12`, `9`, `10`, `76`)
  and `Galois.SubfieldAut`'s *"Measured at `320f413`"* table (`0` / `22` / `74`;
  `MulByNGaloisGroup` is `107` at `542e721`). ⚠️ **That one sha keys all three figure columns of a
  four-column table at once, and one of them — the total over this project plus all nine
  `.lake/packages` — cannot be re-measured from this repository at all**, the package trees not
  being tracked in it. That is what a key buys, and re-measuring is not a substitute for it.
* **Four of the twelve unkeyed count rows are false**, and every one of them was exactly right at
  the commit that wrote it. Two were written by one commit, `008fea7`, in two different files.

**The fifteen, because the 3 / 12 split is the whole of the argument above and a reader who cannot
audit it has to take it.** Verdicts at `542e721`, re-run and unmoved at `2a72ea2` and at `eab2fe9`
— ⚠️ **except the two rows `#2348` repaired, whose count, key and verdict cells are read at
`73ee8eb1` and say so.** ⚠️ **The `key` column records what the FIGURE's own text carries and not
what its file does**, which is why `SubfieldAut:17` shows a `—` while its own file prints shas of
its own, and its own figure prints none.  ⚠️ **No count is given here on purpose**: a sha census
over a file this section's own repairs do not touch is falsified by any later edit to that file.

| row | the count | key | verdict |
| --- | --- | --- | --- |
| `Coprime:196` | `0` and `7`; `1` and `8` after a leaf | `68fd254` | true at its key |
| `GenuineLawComm:55` | `GroupLawBundle` is `14` | — | true, unkeyed |
| `MulByN:42` | this file is `0` | — | true, exempt |
| `MatrixRepDeterminantCharacter:26` | `39`, `168`; `40`, `171` | `d0ae34e`, `542e721` | repaired |
| `MulByNGaloisGroup:82` | `70` → `71`; `107` | `008fea7`, `542e721` | repaired |
| `NegYGaloisGroup:62` | `71` → `19`, `17`; `22`, `20` | `008fea7`, `542e721` | repaired |
| `NthRootOfPullbackN:177` | `78` → `88`, an edge of `10` | `6df393f` | repaired |
| `TranslationMulByNCommGeneral:116` | `NsmulSmoothSurjective` is `20` | `73ee8eb1` | repaired |
| `WeilPairingEltBaseChange:84` | `12`, `9`, `10`, `76` | `008fea7` | true at its key |
| `SubfieldAut:17` | this file is `0` | — | true, exempt |
| `SubfieldAut:48` | `0` / `22` / `74`, and two totals | `320f413` | true at its key |
| `Determinant:147` | `Continuity`'s closure, listed in full | — | true, unkeyed |
| `DeterminantModGeneral:34` | `38` → `72`, `41` → `75` | `73ee8eb1` | repaired |
| `GaloisAction:32` | this file's closure, listed in full | — | true, unkeyed |
| `DivisionPolynomialEval:62` | this file is `0`; an intersection of `1` | — | true, `0` exempt |

⚠️ **Two of the fifteen carry no numeral at all** — `Determinant:147` and `GaloisAction:32` name a
closure by listing it out — so no numeral-keyed triage of this population can return the fifteen,
and a reviewer who reaches for one comes up short.

⚠️ **The exemption, and it is the only one.** A count of **0** stated of a module that imports
nothing from this development is falsifiable only by that module's own `import` lines, so its
subject is the file and its own diff can always see it (`Galois.SubfieldAut`, `FormalGroup.MulByN`,
`Torsion.DivisionPolynomialEval`). **Every other count's subject is the tree**: an edge added
anywhere upstream moves it, and the file carrying it is in no part of that commit's diff.

⚠️ **SIX of the fifteen carry no sha once `#2348` keys its two rows, and this rule convicts
FOUR of them.** Two of the six are wholly inside the exemption — `MulByN:42` and `SubfieldAut:17`.
The other four are **true** at `542e721` and at `2a72ea2`, and are named rather than repaired:
`GenuineLawComm:55`, `Determinant:147`, `GaloisAction:32`, and `DivisionPolynomialEval:62` — whose
own `0` is exempt, but whose second figure, the claim that this module alone lies in the
intersection of two **other** modules' closures, is a count over the tree and is not. ⚠️ **A rule
that lands with live instances nobody has counted reads as swept when it is not**, so they are
counted here; keying or retiring the four is `#2005`'s to finish.

⚠️⚠️ **THAT CENSUS READ *"Eight of the fifteen carry no sha once the four repairs land, and
this rule convicts six of them"* AND NAMED SIX ROWS AS *"named rather than repaired"* (`ac462ef7`,
PR #764, `#2005`), AND `#2348` FALSIFIED BOTH WITH ITS OWN PAYLOAD.** Both were exact until that
round keyed two of the fifteen ROWS — ⚠️ three figures in two files, `DeterminantModGeneral:34`
being one row that carries two — so the eight became six, the convicted six became four, and the
six names became four in the commit that repaired them. ⚠️ **The derivation is published and not
the result alone, because this pair moves again the next time anybody keys one of the four**:
EIGHT unkeyed at `542e721`, LESS the two `#2348` keyed, LESS the two exempt. ⚠️⚠️ **A census of
RESOLUTION is dated by a repair and not by an edge landing upstream, so it is the one figure in
this section that its own payload can falsify** — which is what happened here, and it is the
complement of the consolidation shape the next paragraph records.

⚠️⚠️ **TWO OF THE SIX ROWS UNKEYED AND NON-EXEMPT AT `542e721` ARE FALSE AT `main` — THREE
FIGURES, `DeterminantModGeneral:34` CARRYING TWO — AND ONE COMMIT FALSIFIED ALL THREE, WHICH IS A
MECHANISM AND NOT A COINCIDENCE.** The census above is keyed and is exact at its own two keys;
what a key cannot say is what a later landing does. Re-walked at `73ee8eb1`, three rows are
**UNMOVED** — `GenuineLawComm:55` at **14** with its membership still false, `Determinant:147`'s
3-member set and `GaloisAction:32`'s 2-member set — while `TranslationMulByNCommGeneral`'s **19**
reads **20**, and `DeterminantModGeneral:34`'s `37 → 71` and `40 → 74` read **38 → 72** and
**41 → 75**. ⚠️ **Each moved by exactly `+1`, all three at `0e13ff0f`, and the single entering
module is `EllipticCurves.Torsion.FourNeZero` in every one**; that commit retired seven `private`
copies of one lemma into a shared public leaf, and ⚠️ **its own diff names neither of the two files
carrying the figures it dated.** The three figures are repaired in place by `#2348`; the three rows
re-walked beside them are left exact and unkeyed, `DivisionPolynomialEval:62`'s intersection figure
is not re-walked here at all, and all four of those are still `#2005`'s.

⚠️⚠️ **SO A CONSOLIDATION REFACTOR IS A CLOSURE-FIGURE KILLER, AND IT IS THE COMPLEMENT OF THE
`NthRootOfPullbackN` SHAPE BELOW RATHER THAN ANOTHER INSTANCE OF IT.** That one is **wrong at the
commit that wrote it**; these were **exact at theirs**, under this section's own exclude-self
convention, and were dated afterwards. Retiring `N` private copies into one shared leaf adds
**one** module to the closure of **every** consumer at once, so a single such commit dates every
count-shaped figure in **other** files naming any of them, and no gate on this board reports it: the
build is green, the linter is silent, and the consolidating round's own unit names only the files it
edits. ⚠️ **A figure named for another module therefore owes the REF it was read at and not only its
convention** — all three above named their convention correctly and were still unreadable three
weeks later, because nothing in them said *when*. ⚠️ **And read which half rots before repairing**:
the `+34` delta of the second pair survives both landings, so there the endpoints were dated and the
placement argument was not.

⚠️ **The convention belongs beside the figure and must not be assumed.** `Galois.SubfieldAut` rules
that the `EllipticCurves` closure does **not** count the module itself while a total closure does,
*"and assuming one convention for both is how a re-run comes out one high on three cells"*. Reading
the other convention into a figure written under this one is how
`FunctionField.NthRootOfPullbackN` came to publish `79 → 89` where the walker returns `78 → 88` —
**wrong at the commit that wrote it, not stale**, and invisible to any reviewer who re-ran it
under the reading it was written in.

⚠️⚠️ **AND THE RULE ABOVE GOVERNS BOTH SHAPES OF THE FIGURE, WHICH NOBODY HAD WRITTEN DOWN AND TWO
LANDED FILES READ OPPOSITE WAYS.** A closure count comes in two shapes — *what **this** file costs*
and *what **another** module reaches* — and `Torsion/NsmulYCoord` and `Torsion/NsmulYPeriodic` state
a second default for the second shape, *"A count named for another module is that module **and**
everything it reaches"*, while `Torsion/OmegaIntegral` leads with `Torsion.NsmulYCoord` *"not
counting itself — the convention `README.md`'s `## Import-closure figures` states"*. ⚠️ **Both are
exact and both are keyed to `e4345ae`, where that module's closure is `31` excluding itself and `32`
including it**, so two landed files print `31` and `32` for ONE module at ONE commit, and a reader
who carries either file's stated rule to the other's numeral concludes the other is stale by one.
**That is the `FunctionField.NthRootOfPullbackN` failure the paragraph above names, arriving between
two files that both cite this section** (`#2255`).

⚠️⚠️ **The default is settled by MEASUREMENT and not by fiat, and the sweep is keyed because it
moves under every landing.** The count-shaped seed is a line matching
`closure|import graph|reverse import cone` **and** carrying `**N**`, `closure of N` or `N modules`,
over the tracked `.lean` files: **47 rows in 33 files at `bed1bb64`**, against **27 in 21** at
`e4345ae` and **29 in 21** at `153312c`, over `473` tracked `.lean` files here and `440` at both of
those. ⚠️ **The narrow `import closure` key moves with it** — `103` lines in `77` files here against
`83` in `62` at `e4345ae` *and* at `153312c` — **so a figure of this population that was stable
across one branch's rounds is not stable across a week, and none of these readings may be carried to
another head.** ⚠️ **No split of the 47 by *whether the row names its reading* is published here,
and the omission is deliberate**: that predicate is a judgement about prose rather than a grep, and
three defensible phrase keys over the same 47 rows disagree with one another. **What decides the
default is the restricted population and not the 47** — the EIGHT *named-for-another* rows this
rule governs, where it is six to two, below — because the rule above reaches only a figure named
for ANOTHER module, and the seed that returns the 47 tests for neither that shape nor resolution.

⚠️⚠️ **And of the EIGHT *named-for-another* rows whose numeral resolves against the walk at its own
key, SIX exclude the module named and TWO include it** — each re-derived from the `import` lines
rather than taken from the file that prints it. **Exclude**: `Coprime:196` (`NsmulSurjective` **7**
at `68fd254`), `NegYGaloisGroup:65` (`NegYGalois` **20** at `542e721`), `MulByThreeGalois:383` and
`:387` (`PlaceBelowIntegralClosure` **51** and `MulByThreeDegree` **24** at `0b8f3d1`),
`TriplingGaloisTower:153` (`TriplingSeparable` **53** at `bebec3f`) and `OmegaIntegral:532`
(`NsmulYCoord` **31** at `e4345ae`). **Include**: `NsmulYCoord:117` (`NsmulLadder` **22**, the
walk's `21` plus itself) and `NsmulYPeriodic:140` (`NsmulYCoord` **32**, the walk's `31` plus
itself) — ⚠️ **both of those two addresses read in the tree this sentence lands in and not in its
base, the same commit having re-wrapped the paragraph above each of them.** ⚠️
`MatrixRepModGeneral:39` states **exclude** in words — *"with that module itself dropped"* — and
carries no key, so it is evidence of the practice and not one of the eight. ⚠️⚠️ **The two
include-self rows are the `Nsmul` pair's two files, and the six exclude-self rows are six rows in
FIVE files — `MulByThreeGalois.lean` carries two of them, `:383` and `:387` — spread over THREE
directories (`DivisionPolynomial`, `FunctionField` ×2, `Torsion` ×2), so this tree's practice is
EXCLUDE-self in BOTH shapes and the rule above governs both**: the `Nsmul` lane's reading is a
**stated local exception**, which those two files now say of themselves, and not a second default.

**The rule, then: a figure of the *named-for-another* shape prints BOTH numerals or names its
reading in words.** **Six of the eight rows above already do, and two do not**:
`DivisionPolynomial/Coprime.lean`:`196` and `FunctionField/NegYGaloisGroup.lean`:`65` each print one
numeral and name their reading nowhere in their own file — a whole-file grep for `excluding`,
`excludes`, `not counting`, `itself dropped`, `itself excluded`, `including it`, `counting it` and
`module itself` returns **0** in both at `bed1bb64` — **so they are the two sites this clause
reaches, and they are named here, with their paths, rather than left to be found** (⚠️ `Coprime` is
one of this tree's two duplicated basenames and `Torsion/Coprime.lean` has a line `196` as well).
It is one clause, and it is the only form under which a `±1` cannot be read either way. ⚠️⚠️ **And a
self-inclusion convention has THREE sources here and not two**: the walk's `− {seed}`, the figure's
SUBJECT — *this* file against *another* module — and, for the elaborator instrument, the probe's
PLACEMENT. During elaboration of a module that module is not yet in its own environment header, so
`(← Lean.getEnv).header.moduleNames` read from a probe that *imports* the measured module carries it
and the same probe appended *inside* that module does not: **32** against **31** for
`Torsion.NsmulYCoord` at `e4345ae`. **A sentence naming two of the three leaves the same `±1`
open.**

⚠️ **A membership claim needs no sha because it is *cheap* to re-run, not because it is safe.**
*"`X` is not in this file's import closure"* is refuted by any new edge whose far end reaches `X`,
and the commit that adds that edge is usually the commit that announces it:
`FunctionField.NthRootOfPullbackN` denied that `Torsion.NsmulOrder` was in its closure in one
clause and announced the `MulByNXCoordFormula` edge that put it there in the next, in one diff.
**Before adding an `import`, re-run every closure claim in the file you are adding it to** — the
one you falsify is most often in the paragraph you are editing.

⚠️ **A cross-file word-identity figure has THREE degrees of freedom — the SPAN, the NORMALISATION
and the REF — and a number naming fewer than all three is not re-runnable.** Two docstrings
stating the same convention in the same words invite a character count as evidence, and
`6f051d4`'s own message publishes one: *"Both files now read, word-identically (**699**
characters, checked as a string equality and not by eye)"*, printed above a block quote. **All
four readings of that claim are exact** at `6f051d4`, over `Torsion/NsmulYCoord.lean` and
`Torsion/NsmulYPeriodic.lean`, whitespace-normalised by `re.sub(r'\s+', ' ', s)` except where
stated:

| reading | length |
| --- | --- |
| the block quote exactly as printed beneath the figure | **408** |
| ⚠️ published span: `A count named for *another* module…` → `…which needs no build.` | **699** |
| ⚠️ the true longest common substring of the two files | ⚠️ **866** |
| the same longest common substring, raw, with no normalisation | **294** |

⚠️ **So the `699` is exact for a span beginning two sentences before the quote printed under it**,
its normalisation is named nowhere, and the identity it reports is in fact **narrower** than the
one that holds — the common run is `866`. A re-runner who measures what is printed gets `408` and
reads the figure as wrong; one who measures raw gets `294`, because the two files wrap the
paragraph differently. ⚠️ **The two docstrings are not the defect and are not changed here: the
identity is real and both reviews certified it.**

⚠️ **And the REF is a degree of freedom in its own right, stated here because the tree PROVES it
and not because it is prudent.** The same span, the same normalisation and the same two files, at
`#2254`'s two round heads — ⚠️ **and then at one further key whose SPAN is a different one, which
the clause under the table says in terms**:

| ref | published span | normalised longest common substring | the same, raw |
| --- | --- | --- | --- |
| `153312c85bb441ba95be549f2aa0aeb6ed33c8eb` — `#2254` round 1 | **516** | **683** | **687** |
| `6f051d4fd44516ee225703b66ccb3b4b01781ded` — `main`, round 2 | **699** | **866** | **294** |
| ⚠️ `#2255` — keyed by BLOB, named below | **1019** | **1186** | **253** |

⚠️ **`git diff --numstat` over the two files between those refs is `9 / 7` in `NsmulYCoord.lean`
and `4 / 2` in `NsmulYPeriodic.lean` — 13 lines added and 9 removed — and that edit is the whole
of `516 → 699`.** ⚠️ **The raw column is the sharper cell: at round 1 raw and normalised agree to
within four characters, `687` against `683`, because the two files wrapped the paragraph the same
way; at `main` raw COLLAPSES to `294` while normalised GROWS to `866`.** So the `294` in the table
above is not a standing property of the pair — it is an artefact of one round's rewrap, and it
moved in the very round that made the identity wider. **The rule, then: such a figure carries its
endpoints, its normalisation AND its ref, or it stays a review-time measurement** — and ⚠️ **a
landing message cannot be amended, so the durable home for one is this page and not a commit
body** (`#2258`).

⚠️⚠️ **The third row is this page's own mechanism firing a second time, and its span is NOT the
second row's.** `#2255`'s round declares the `Nsmul` lane's named-for-another reading a stated
local exception, which re-words the shared paragraph in both files; the published span is
therefore measured from `⚠️ **The reading HERE is a stated local EXCEPTION…` to the same
`…which needs no build.`, it goes `699 → 1019`, and the identity WIDENS `866 → 1186` while the
raw reading COLLAPSES `294 → 253` — ⚠️ **the same round, again, both directions at once.**
⚠️ **It is keyed by BLOB and not by commit because the merger squashes**, so a branch-head sha
for it would name no object reachable from `main`: the two blobs are
`dc8ae1b1a80149e837c06432b2cec736468852e8` for `Torsion/NsmulYCoord.lean` and
`4fd078b4cfcbbaeb3c2890dc6fb1d8aaf0eaa065` for `Torsion/NsmulYPeriodic.lean`.

**The gate, for a branch author.** `#1972`'s splice test is defined on `README.md` and cannot reach
this layer: a `.lean` closure figure is not a block that can be spliced into another page, it is a
claim about the tree, and the only resolver is to re-run the walk. ⚠️ **Re-run it at
`upstream/main` and not at your base** — a `.lean`-only base move is exactly the case a
`README.md`-keyed gate reports as clean.

⚠️ **And a lexical rule the walks themselves need: no line of a `.lean` file may begin with the
word `import` at column 0 unless it is a real `import`.** The walkers agents write against this
tree read `^(public |private |meta )*import (\S+)`, so a docstring sentence reflowed to start with
*import* contributes a phantom module named after the next word, reachable from every file that
reaches it. **Ten sites had accumulated at `ebb8735`**, and are repaired in the commit that names
it as base; the regression seed is that grep, scored against which arguments resolve to a real
`.lean` file, and it must return **0**. ⚠️ **It falsifies no figure this document publishes, and
the reason is the ARGUMENT filter and not the lexical prefix.** This section's own seed is narrower
still — the `EllipticCurves` graph from `^import EllipticCurves…` lines, carrying no
`public `/`private `/`meta ` alternation at all — and a phantom named `edge.` or `closure` resolves
to no module under either shape. **A rule about keeping the instrument honest, not a repair.**

⚠️ **And the rule is GATED as of the commit that names this paragraph as its base:
`.orchestra/validation.sh` runs the seed over the tracked `.lean` files before anything that
needs Lake, and prints the offending `file:line` and the phantom argument and not only a count.**
Its discriminator is a **comment mask** — the defect's own definition, *a textual `import` line
Lean never reads because it sits inside a comment* — and not the argument-resolution proxy above,
so it consults no module index and never touches `.lake`; the two agree **site for site** on every
site this class has ever had, the gate reading **4** at `977452c`, **3** at `35eb801`, **2** at
`6389efc` and **0** at `8d50ca3`.

⚠️⚠️ **And the argument-resolution seed stated for that rule is STRICTLY WEAKER than the rule
itself, so a `0` from it discharges nothing.** The rule is violated by ANY comment-interior `import`
at column 0, whatever its argument; the seed fires only when the argument FAILS to resolve. **The
two part on exactly the fenced-code subclass this section defines, whose displayed module names are
chosen BECAUSE they are real.** ⚠️ **Measured at `21562de`, not argued**: seed a fence body at
column 0, inside a module docstring, displaying `EllipticCurves.TateModule.MatrixRepMod` — this
section's own probe name, and one that resolves — and over the same **449** tracked `.lean` files a
comment-mask test of the rule reports **1** and exits `1`, naming file and line, while the
argument-resolution seed reports **0** and exits `0`. ⚠️ **It does not MISS the line: its grep total
moves `1724` → `1725`, so it sees the line and scores it clean.** Indent that fence body two spaces
and both read `0` again. ⚠️⚠️ **AND THE CONSEQUENCE INVERTS THIS SECTION'S OWN STATED REASON.**
*"It falsifies no figure this document publishes, and the reason is the ARGUMENT filter…"* is true
of the ten sites it was written about, whose eight distinct arguments resolve to nothing — but as a
property of the filter it is backwards: a NON-resolving phantom adds a node no walk reaches, while a
RESOLVING one adds a real EDGE between two real nodes, which is what a closure figure is made of.
The same probe placed in `Torsion/NsmulYCoord.lean` takes that module's `^import EllipticCurves…`
closure from **31** to **60** at `21562de`, not counting itself. **So the filter admits precisely
the subclass that can move a published figure.** ⚠️ **What each `0` licenses, which is the half a
reader needs: a `0` from the comment-mask test IS the rule, over the tracked `.lean` files; a `0`
from the argument-resolution seed says only that no phantom named after a non-resolving word
survives, and `#2278` is the row that puts a mask implementation into `.orchestra/validation.sh`.**
⚠️ **The argument filter is NOT retired and must not be** — it is deliberate and load-bearing and
is the right instrument wherever the question really is resolution, and `#2250`'s reviewer retracted
a finding for reading it as an oversight.

⚠️ **And the class ACCRETES, which the paragraph above could not say at the time: the seed returned
`1` and not `0` in the very tree that rule landed in.** An eleventh site — a *"seed the base import
list"* sentence in `Torsion/ThreeTorsionStructure.lean` — landed as `9f25690` (PR #836) while the
ten-site round sat in review, so it postdates that round's base and its frozen tree and could not
have been repaired there. It is reflowed in the commit that names **this** paragraph as its base,
taking the seed to **0**. ⚠️ **So a reader who meets the rule above and reads a non-zero seed has
most likely found a NEW site rather than a stale instrument** — run it, name the file, reflow it,
and do not conclude the rule is wrong: the population went `10` → `11` inside one review window.
⚠️ **The repair is a reflow and only a reflow, and the gate that proves it one is cheap**: the
edited file's word sequence, numeral sequence and total character count must all be identical at
base and head. The width budget is what makes the shape non-obvious — prepending `import` to the
previous line costs `+7` and overflows the hard `100`, so the word *before* it moves DOWN instead,
cascading to the next line if that one overflows too.

⚠️ **And a SECOND SUBCLASS, which the reflow repair cannot reach and whose gate is therefore a
different one: a fenced code block that DISPLAYS Lean `import` syntax.** Its lines begin with
`import` because that is what they illustrate, so there is no prose sentence to reflow and the
sentence above is not a universal. **The repair is a two-space indent of the fence body — every
line of it, not only the lines that match**, because a recipe with two of its three lines indented
is visibly broken. ⚠️ **And it is measured rather than assumed: an indented `import` resolves
identically.** Two probes seeded at `EllipticCurves.TateModule.MatrixRepMod`, one at column `0` and
one indented two spaces, each read **4119** `moduleNames` with empty stderr, and the sorted lists
are set-identical — so the indent costs the recipe nothing. ⚠️ **The character-count half of the
gate above does NOT transfer**, since an indent adds `2` characters per line; what survives, and is
the equal-strength invariant for this subclass, is that the **non-whitespace text is identical** at
base and head — an indent adds only whitespace. **So state the invariant your repair satisfies
rather than inheriting the reflow triple.** `#2265`, in `Torsion/TwoTorsionCharTwo.lean`'s fenced
`run_meta … moduleNames` recipe (`:414`–`:416` at `e95af0e`; the fence, not the line number, is the
durable key).
