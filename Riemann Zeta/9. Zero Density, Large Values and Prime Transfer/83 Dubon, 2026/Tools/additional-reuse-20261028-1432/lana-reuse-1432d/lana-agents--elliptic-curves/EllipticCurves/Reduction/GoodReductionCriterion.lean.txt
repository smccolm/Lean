/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Mathlib.AlgebraicGeometry.EllipticCurve.ModelsWithJ
import Mathlib.AlgebraicGeometry.EllipticCurve.Reduction
import Mathlib.RingTheory.PowerSeries.Inverse

/-!
# A sufficient criterion for good reduction, and a curve with prescribed `j` that has it

Let `R` be a discrete valuation ring with fraction field `K = Frac R`.  Mathlib defines
`WeierstrassCurve.HasGoodReduction R W` as `IsMinimal R W` together with
`valuation K (maximalIdeal R) W.Δ = 1`, and `IsMinimal` is a `MaximalFor` condition over the
whole `VariableChange K` orbit of `W`.  ⚠️ **What this development lacked was a way to
ESTABLISH `IsMinimal` for a curve the caller already holds.**  ⚠️ Every route to good reduction
that existed *before this file* — here and in Mathlib — takes minimality as an input, where a
*route* is the term a caller applies and, for an `Iff`, that term is its `.2`.  ⚠️⚠️ **Both
qualifications are load-bearing and neither is decorative.**  Read over SIGNATURES the sentence
is refuted by Mathlib's pre-existing `hasGoodReduction_iff`, which binds no `IsMinimal`
anywhere — and yet its `.2` cannot be applied without one, its argument being `IsMinimal R W`
conjoined with the valuation equality, so what carries minimality is the ARGUMENT and not the
binder list, and the three `@[mk_iff]` lemmas are all of that shape.  ⚠️ Read in the present
TENSE it is refuted by `hasGoodReduction_of_valuation_Δ_eq_one` below, which binds `IsIntegral`
and the valuation equality and no `IsMinimal` at all — which is what *before this file* is
there for.  ⚠️⚠️ **Mathlib's side is given as a NAMED SET**, this paragraph's predecessor
having carried a wrong exact set that is retired below.  `exists_isMinimal` concludes
`∃ C : VariableChange K, IsMinimal R (C • W)`, a model the caller does not hold; the
**instance** `instIsMinimalMinimal` concludes `IsMinimal R (W.minimal R)`, a *definite* model
that is still not `W`, and ⚠️ it is the sharpest evidence FOR the gap rather than against it —
it fires by instance synthesis with no caller action at all and still says nothing about `W`;
`HasGoodReduction.toIsMinimal`, `HasMultiplicativeReduction.toIsMinimal` and
`HasAdditiveReduction.toIsMinimal` run *out* of classes that already extend `IsMinimal`; and
`IsMinimal.mk` asks for the definitional data.  ⚠️⚠️ **The instrument is a conclusion-*mention*
census over the elaborated environment, never a `grep` and never a conclusion-*head* census,
and the difference is load-bearing rather than pedantic**: a head census returns neither
`exists_isMinimal`, whose head is `Exists`, nor any `@[mk_iff]` lemma, while an `Iff` hands a
caller `IsMinimal R W` as readily as a conclusion head does.  At Mathlib `81a5d25`
(`lake-manifest.json`'s revision, Lean `v4.32.0`) the mention census returns ELEVEN on
Mathlib's side, and ⚠️ **the figure is keyed because it is a reading of Mathlib rather than of
this tree, while what cannot rot is the PARTITION**: every one of the eleven is another model
(`exists_isMinimal`, `instIsMinimalMinimal`), or a strictly stronger class (the three
`toIsMinimal` projections and their three `@[mk_iff]` twins `hasGoodReduction_iff`,
`hasMultiplicativeReduction_iff` and `hasAdditiveReduction_iff`, each carrying `IsMinimal R W`
as the first conjunct on its right), or the definitional datum (`IsMinimal.mk` and its twin
`isMinimal_iff`, the same `MaximalFor` condition spelled two ways), or auto-generated
congruence (`IsMinimal.congr_simp`).  ⚠️ So none of the eleven reaches `W` itself from anything
cheaper than the definition or a strictly stronger class, which is the ESTABLISH-`IsMinimal`
lack above, not the *route* universal that follows it.  ⚠️⚠️ **Run the census over the ROOT
environment and after a full build.**  The same walk over this module's own import closure
still reads ELEVEN on Mathlib's side, so that figure is closure-robust; the TOTAL is not, the
root reading exceeding this one by exactly the two it cannot see here, this tree's own
`isMinimal_baseChange` and `reduction.congr_simp`.  ⚠️ `exists_isIntegral` is **not** in that
set: it concludes `∃ C, IsIntegral R (C • W)` — a *different predicate* — and binds
`[ValuationRing R]` rather than `[IsDiscreteValuationRing R]`.  This file closes that gap at
`isMinimal_of_valuation_Δ_eq_one`, and `hasGoodReduction_of_valuation_Δ_eq_one` adds the same
valuation equality to it through `HasGoodReduction`'s own structure instance — ⚠️ **not**
through `hasGoodReduction_iff`, which no code line in this file mentions.

`Reduction.GoodReductionBaseChange`'s `hasGoodReduction_baseChange` does conclude
`HasGoodReduction`, so this file is not the first declaration in `Reduction/` to conclude it; but
that one binds `[HasGoodReduction R W]` and transports it to a DVR extension, which is propagation
and not establishment.  So before this module no curve anywhere in this development had been shown
to have good reduction, and `section Nonvacuity`'s `example` is the first closed term of the
predicate in the tree.  This file closes the gap at the cheapest place it closes, and then exhibits
a curve.

⚠️ **Retired, and the clause was false rather than partial**, so `### Retired claims` binds rather
than `### Reach clauses`.  This paragraph read *"every pre-existing route consumed it, or an
equivalent, as an input, so nothing could start the chain"* — of `HasGoodReduction` — and two
sentences later *"`hasGoodReduction_iff` and `hasGoodReduction_iff_isElliptic_reduction` conclude an
`Iff` and each takes `IsMinimal` as an input"*, both from `77aeeaab` (`%cI` 2026-10-05T02:16:54Z,
`#2333`, PR #914).  That commit introduced both clauses, so the contradiction reached `main` and is
retired here rather than amended out of a message no longer reachable.  Three readings sink it.
`Reduction.ReductionNodeCusp`'s `hasGoodReduction_iff_reduction_Δ_ne_zero` and
`Reduction.ReductionTrichotomy`'s `hasGoodReduction_iff_not_multiplicative_and_not_additive` are
pre-existing, sit in this directory, bind `[IsMinimal R W]` and not `HasGoodReduction`, and their
`.2` concludes the predicate from a discriminant condition — so the universal is false on its own
terms.  `IsMinimal` is not an *equivalent* of `HasGoodReduction` either, the latter being a class
that extends the former with a further field and so strictly more data; and on a reading of
*"an equivalent"* loose enough to cover it, the clause convicts this file's own
`hasGoodReduction_of_valuation_Δ_eq_one`, whose hypotheses are `IsIntegral` and the valuation
equality.  ⚠️ And `hasGoodReduction_iff` is the class's `@[mk_iff]` lemma, binding no `IsMinimal`
at all, so *"each"* was wrong on one of the two it quantified over.  **What survives is the
`IsMinimal` reading above** — which `exists_isMinimal` was always evidence for, and
`exists_isIntegral` only in the weaker form `77aeeaab` itself used, that both hand back a change
of variables rather than a reduction type.

## The criterion

The minimality condition quantifies over the orbit, but the quantity it maximises takes values in
the subtype `{v : ℤᵐ⁰ // v ≤ 1}` (`WeierstrassCurve.valuation_Δ_aux`), and `1` is the **top**
element of that subtype: an integral Weierstrass equation has `v(Δ) ≤ 1` and nothing in the orbit
can do better.  So a single integral equation whose discriminant valuation is already `1` is
minimal for a reason that never looks at the orbit — `isMinimal_of_valuation_Δ_eq_one` — and is
therefore of good reduction, `hasGoodReduction_of_valuation_Δ_eq_one`.  In the form a user meets
it, `hasGoodReduction_baseChange_of_isUnit_Δ`: an integral model `W : WeierstrassCurve R` whose
discriminant is a **unit of `R`** base-changes to a curve over `K` of good reduction.

⚠️ **That argument was already in this directory in one special case**, and
`isMinimal_of_valuation_Δ_eq_one` is it with the hypothesis abstracted:
`Reduction.GoodReductionBaseChange`'s `isMinimal_baseChange` runs the same subtype bound on `W⁄L`
with the valuation equality supplied by `valuation_Δ_baseChange_eq_one` instead of assumed.  ⚠️
That proof carries an inline comment stating the mechanism in its OWN words and not in these —
*"The discriminant of `1 • (W⁄L)` has the top valuation `1`, so every isomorphic integral model
has smaller-or-equal discriminant valuation"* — whose wording is near-verbatim with this
section's opening paragraph above rather than with this sentence, which is why it is quoted here
instead of cited.  Both of that file's conclusions follow from the two lemmas here once
`isIntegral_baseChange` has supplied integrality over the extension ring, which was checked
rather than predicted; neither is rewritten, because shortening a landed proof is a separate row
from stating the lemma it is a case of.

## The witness

Mathlib's `WeierstrassCurve.ofJNe0Or1728 j = ⟨j - 1728, 0, 0, -36(j - 1728)³, -(j - 1728)⁵⟩` is
defined over any commutative ring, with `Δ = j²(j - 1728)⁹` and `j`-invariant `j` whenever `j` and
`j - 1728` are units.  Over a discrete valuation ring those two unit conditions say exactly that
`v(j) = 0` and `v(j - 1728) = 0`, so the criterion applies and
`hasGoodReduction_baseChange_ofJNe0Or1728` gives, for every such `j : R`, a curve over `K` with
good reduction over `R` whose `j`-invariant is `algebraMap R K j` (`j_map_ofJNe0Or1728`).

⚠️ `ofJ0` and `ofJ1728` are **not** instantiated here, and the reason is that their unit conditions
are about `R` rather than about a parameter: their discriminants are `-27` and `-64`, so
`hasGoodReduction_baseChange_of_isUnit_Δ` applies to them exactly when `3`, respectively `2`, is a
unit of `R` — a hypothesis on the residue characteristic.  The criterion already covers them and no
further lemma is needed to state it.

## Main results

* `WeierstrassCurve.isMinimal_of_valuation_Δ_eq_one` — an integral equation with
  `valuation K (maximalIdeal R) W.Δ = 1` is minimal.
* `WeierstrassCurve.hasGoodReduction_of_valuation_Δ_eq_one` — and is of good reduction.
* `WeierstrassCurve.hasGoodReduction_baseChange_of_isUnit_Δ` — for `W : WeierstrassCurve R` with
  `IsUnit W.Δ`, the base change `W⁄K` is of good reduction over `R`.
* `WeierstrassCurve.map_ofJNe0Or1728` — `ofJNe0Or1728` commutes with any ring homomorphism.
* `WeierstrassCurve.isUnit_Δ_ofJNe0Or1728` — its discriminant is a unit when `j` and `j - 1728`
  are, over any commutative ring.
* `WeierstrassCurve.hasGoodReduction_baseChange_ofJNe0Or1728` and
  `WeierstrassCurve.j_map_ofJNe0Or1728` — the witness and its `j`-invariant, both from the one
  hypothesis pair `IsUnit j` and `IsUnit (j - 1728)`.

## Scope

This is the *witness* half of the converse direction of Silverman AEC VII.5.5 (`j` integral at the
base place ⟹ potential good reduction) and not that converse.  Two further inputs are open: a
curve over `K` with the same `j`-invariant as the model above becomes isomorphic to it only over an
extension, and Mathlib's `exists_variableChange_of_j_eq` supplies that change of variables over a
separably closed field only; and a separably closed field carries no discrete valuation, so the
isomorphism has to be descended to a finite subextension and a discrete valuation subring of that
subextension lying over `R` has to be produced.  Neither is attempted here.

## References

* [J. H. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], VII.1, VII.5.
-/

open IsDedekindDomain.HeightOneSpectrum IsDiscreteValuationRing

namespace WeierstrassCurve

section Model

variable {S A : Type*} [CommRing S] [CommRing A]

/-- **`ofJNe0Or1728` commutes with a ring homomorphism.**  Its coefficients are integer polynomials
in the parameter, so the model over `S` with parameter `j` maps to the model over `A` with parameter
`f j`.  This is what lets the good-reduction criterion below be applied over a discrete valuation
ring and read off over its fraction field. -/
lemma map_ofJNe0Or1728 (f : S →+* A) (j : S) :
    (ofJNe0Or1728 j).map f = ofJNe0Or1728 (f j) := by
  ext <;> simp [ofJNe0Or1728, map_ofNat]

/-- **The discriminant of `ofJNe0Or1728 j` is a unit when `j` and `j - 1728` are**, over any
commutative ring, because it is `j² (j - 1728)⁹` (`WeierstrassCurve.ofJNe0Or1728_Δ`). -/
lemma isUnit_Δ_ofJNe0Or1728 {j : S} (hj : IsUnit j) (hj' : IsUnit (j - 1728)) :
    IsUnit (ofJNe0Or1728 j).Δ := by
  rw [ofJNe0Or1728_Δ]
  exact (hj.pow 2).mul (hj'.pow 9)

end Model

variable (R : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]

/-- **An integral Weierstrass equation whose discriminant valuation is already `1` is minimal.**

`IsMinimal R W` asks for `valuation_Δ_aux R (C • W)` to be maximal over those `C : VariableChange K`
for which `C • W` is integral.  That quantity lands in `{v : ℤᵐ⁰ // v ≤ 1}`, so `1` is its top
value and the hypothesis puts `W` there; the comparison with the rest of the orbit is then the
subtype's own bound and no property of `C` is used. -/
theorem isMinimal_of_valuation_Δ_eq_one (W : WeierstrassCurve K) [IsIntegral R W]
    (hΔ : valuation K (maximalIdeal R) W.Δ = 1) : IsMinimal R W := by
  refine ⟨⟨by simpa using ‹IsIntegral R W›, fun {C} _ _ => Subtype.coe_le_coe.mp ?_⟩⟩
  have h1 : (valuation_Δ_aux R ((1 : VariableChange K) • W)).1 = 1 := by
    rw [one_smul]
    exact (valuation_Δ_aux_eq_of_isIntegral R W).trans hΔ
  rw [h1]
  exact (valuation_Δ_aux R (C • W)).2

/-- **An integral Weierstrass equation whose discriminant valuation is `1` has good reduction.**
`HasGoodReduction` is minimality together with that equality, and minimality is
`isMinimal_of_valuation_Δ_eq_one`. -/
theorem hasGoodReduction_of_valuation_Δ_eq_one (W : WeierstrassCurve K) [IsIntegral R W]
    (hΔ : valuation K (maximalIdeal R) W.Δ = 1) : HasGoodReduction R W :=
  { isMinimal_of_valuation_Δ_eq_one R W hΔ with goodReduction := hΔ }

/-- **A model over `R` with unit discriminant base-changes to a curve of good reduction.**  This is
the criterion in the form a user meets it: no valuation appears in the hypothesis, only
`IsUnit W.Δ` in `R`.  The valuation equality comes from `IsUnit W.Δ` through
`IsDedekindDomain.HeightOneSpectrum.valuation_eq_one_iff_notMem` and
`IsLocalRing.notMem_maximalIdeal`, and integrality is witnessed by `W` itself. -/
theorem hasGoodReduction_baseChange_of_isUnit_Δ (W : WeierstrassCurve R) (hΔ : IsUnit W.Δ) :
    HasGoodReduction R (W⁄K) := by
  haveI : IsIntegral R (W⁄K) := ⟨W, rfl⟩
  refine hasGoodReduction_of_valuation_Δ_eq_one R _ ?_
  rw [show (W⁄K).Δ = algebraMap R K W.Δ from map_Δ W _]
  exact (valuation_eq_one_iff_notMem (maximalIdeal R)).2 (IsLocalRing.notMem_maximalIdeal.2 hΔ)

/-- **A curve over `K` of good reduction over `R` with prescribed `j`-invariant.**  For `j : R`
with `IsUnit j` and `IsUnit (j - 1728)` — over a discrete valuation ring, `v(j) = 0` and
`v(j - 1728) = 0` — the base change of Mathlib's model `ofJNe0Or1728 j` has good reduction.  Its
`j`-invariant is `algebraMap R K j` by `j_map_ofJNe0Or1728`, which takes these same two `IsUnit`
hypotheses and no instance. -/
theorem hasGoodReduction_baseChange_ofJNe0Or1728 {j : R} (hj : IsUnit j)
    (hj' : IsUnit (j - 1728)) : HasGoodReduction R ((ofJNe0Or1728 j)⁄K) :=
  hasGoodReduction_baseChange_of_isUnit_Δ R _ (isUnit_Δ_ofJNe0Or1728 hj hj')

omit [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R K] in
/-- **The `j`-invariant of the witness is the prescribed one.**

⚠️ The two unit conditions are plain hypotheses, and the `Fact` instances that Mathlib's
`ofJNe0Or1728_j` asks for are built from them **inside the statement** rather than bound.  They
cannot be dropped: `WeierstrassCurve.j` is defined only under `[IsElliptic]`, and on this model the
only route to that instance is the pair of `Fact`s, so the equation is not formable without them.
But the binder list is the wrong place for them, because a reader holding
`hasGoodReduction_baseChange_ofJNe0Or1728`'s own `IsUnit` hypotheses would then have to manufacture
two instances before the citation in that declaration's docstring could be used at all.  A consumer
who holds the `Fact` instances instead applies this one as `j_map_ofJNe0Or1728 R hj.out hj'.out`,
so neither hypothesis shape is shut out and both were checked.

⚠️ Stated through `map (algebraMap R K)` rather than through the `⁄` notation, and that is forced
rather than preferred: `WeierstrassCurve.baseChange` is a plain `def`, so
`((ofJNe0Or1728 j)⁄K).IsElliptic` is not found from the `IsElliptic` instance on the model by
instance search, and the `j`-invariant cannot even be *stated* without it — see
`EllipticCurves.Fixture.instIsEllipticBaseChange`'s docstring for the same obstruction and the
reason this module adds no third copy of that bridge.  The two terms are `rfl`-equal, so a consumer
who wants the `⁄` spelling of this equation needs no lemma to move between them. -/
theorem j_map_ofJNe0Or1728 {j : R} (hj : IsUnit j) (hj' : IsUnit (j - 1728)) :
    haveI : Fact (IsUnit j) := ⟨hj⟩
    haveI : Fact (IsUnit (j - 1728)) := ⟨hj'⟩
    ((ofJNe0Or1728 j).map (algebraMap R K)).j = algebraMap R K j := by
  haveI : Fact (IsUnit j) := ⟨hj⟩
  haveI : Fact (IsUnit (j - 1728)) := ⟨hj'⟩
  rw [map_j, ofJNe0Or1728_j]

/-! ## Non-vacuity

The two unit hypotheses of `hasGoodReduction_baseChange_ofJNe0Or1728` are satisfiable together with
the discrete-valuation-ring hypotheses, on a ring that exists.  The certificate base is the formal
power series ring `PowerSeries ℚ`, which Mathlib knows is a discrete valuation ring, with its
generic fraction field `FractionRing (PowerSeries ℚ)`; the parameter is `j = 1`, for which
`j - 1728 = -1727` is a nonzero rational constant and hence a unit.

⚠️ The certificate is declared here rather than in `EllipticCurves.Fixtures`, and the reason is that
module's leaf property: it imports two Mathlib modules and is imported very widely, so putting a
power-series base there would add `Mathlib.RingTheory.PowerSeries.Inverse` to the import closure of
every file that imports it.  Its five fixtures are also curves over a bare commutative ring, which
is not the shape a good-reduction statement takes. -/

section Nonvacuity

private lemma exampleOne : IsUnit (1 : PowerSeries ℚ) := isUnit_one

private lemma exampleSub : IsUnit ((1 : PowerSeries ℚ) - 1728) := by
  have h : (1 : PowerSeries ℚ) - 1728 = algebraMap ℚ (PowerSeries ℚ) (1 - 1728) := by
    rw [map_sub, map_one, map_ofNat]
  rw [h]
  exact (isUnit_iff_ne_zero.2 (by norm_num)).map _

/-- **⚠️ THE LOAD-BEARING CERTIFICATE**: a curve of good reduction exists.  Everything in
`Reduction/` is stated for a curve with a reduction type, and until this example no term of
`HasGoodReduction` had been produced anywhere in this development. -/
example : HasGoodReduction (PowerSeries ℚ)
    ((ofJNe0Or1728 (1 : PowerSeries ℚ))⁄(FractionRing (PowerSeries ℚ))) :=
  hasGoodReduction_baseChange_ofJNe0Or1728 _ exampleOne exampleSub

end Nonvacuity

end WeierstrassCurve
