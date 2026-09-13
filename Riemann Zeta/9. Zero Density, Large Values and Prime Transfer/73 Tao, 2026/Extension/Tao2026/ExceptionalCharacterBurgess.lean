import Tao2026.ExceptionalCharacterFamilies

/-!
# Exact Burgess interface for Tao's exceptional-character sieve

`ExceptionalCharacterFamilies` intentionally exposed a convenient uniform
prefix predicate.  The proof of Lemma 5.1 only needs the sieve prefixes
`floor ((2Z-1)/d)`.  This file records that weaker exact interface and proves
how a source-shaped explicit Burgess estimate supplies it once the elementary
large-prefix and period-range inequalities are available.

No Burgess estimate is asserted here.  `TaoExplicitCubefreeBurgessBound` is a
proposition-valued target for the remaining analytic proof.
-/

namespace Tao2026

open Finset Complex
open scoped BigOperators ComplexConjugate

noncomputable section

/-- Exactly the character prefixes produced after expanding Tao's sieve
weight. -/
def TaoCubefreeSievePrefixBound (R Z : ℕ) (E : ℝ) : Prop :=
  ∀ (q : ℕ) (χ : DirichletCharacter ℂ q),
    Squarefree q →
    (q : ℝ) ≤ (Z : ℝ) ^ taoBurgessPeriodExponent →
    χ ≠ 1 →
    ∀ d ∈ (primorial R).divisors, (d : ℝ) ≤ R →
      ‖∑ n ∈ Finset.Ioc 0 ((2 * Z - 1) / d), χ (n : ZMod q)‖ ≤ E

/-- The stronger all-prefix interface implies the exact sieve-prefix one. -/
theorem TaoCubefreeCharacterPrefixBound.toSievePrefixBound
    {R Z : ℕ} {E : ℝ}
    (h : TaoCubefreeCharacterPrefixBound Z E) :
    TaoCubefreeSievePrefixBound R Z E := by
  intro q χ hq hqZ hχ d hd hdR
  exact h q χ ((2 * Z - 1) / d) hq hqZ hχ
    ((Nat.div_le_self _ _).trans (Nat.sub_le _ _))

/-- Source-shaped explicit specialization of the cubefree Burgess theorem.
The constant and lower cutoff are explicit parameters; the exponent is
Tao's `1-0.0163`, and the period range is `q ≤ H^3.1`. -/
def TaoExplicitCubefreeBurgessBound (C : ℝ) (H₀ : ℕ) : Prop :=
  ∀ (H q : ℕ) (χ : DirichletCharacter ℂ q),
    H₀ ≤ H →
    Squarefree q →
    (q : ℝ) ≤ (H : ℝ) ^ (31 / 10 : ℝ) →
    χ ≠ 1 →
    ‖∑ n ∈ Finset.Ioc 0 H, χ (n : ZMod q)‖ ≤
      C * (H : ℝ) ^ (1 - taoBurgessSavingExponent)

/-- An explicit Burgess bound yields all sieve prefixes once their lengths
are beyond its cutoff and the `Z^3.09` period envelope lies in their
`H^3.1` range. -/
theorem TaoExplicitCubefreeBurgessBound.toSievePrefixBound
    {C : ℝ} {H₀ R Z : ℕ}
    (hC : 0 ≤ C)
    (hburgess : TaoExplicitCubefreeBurgessBound C H₀)
    (hlarge : ∀ d ∈ (primorial R).divisors, (d : ℝ) ≤ R →
      H₀ ≤ (2 * Z - 1) / d)
    (hrange : ∀ d ∈ (primorial R).divisors, (d : ℝ) ≤ R →
      (Z : ℝ) ^ taoBurgessPeriodExponent ≤
        (((2 * Z - 1) / d : ℕ) : ℝ) ^ (31 / 10 : ℝ)) :
    TaoCubefreeSievePrefixBound R Z
      (C * (2 * Z : ℝ) ^ (1 - taoBurgessSavingExponent)) := by
  intro q χ hq hqZ hχ d hd hdR
  have hprefix := hburgess ((2 * Z - 1) / d) q χ
    (hlarge d hd hdR) hq (hqZ.trans (hrange d hd hdR)) hχ
  refine hprefix.trans ?_
  apply mul_le_mul_of_nonneg_left _ hC
  apply Real.rpow_le_rpow
  · exact_mod_cast Nat.zero_le ((2 * Z - 1) / d)
  · exact_mod_cast (Nat.div_le_self (2 * Z - 1) d).trans
      (Nat.sub_le (2 * Z) 1)
  · norm_num [taoBurgessSavingExponent]

/-- Complete finite Lemma 5.1 reduction using only the exact sieve-prefix
Burgess interface. -/
theorem sum_finiteNormalizedPrimeBandSum_sq_le_exceptionalFamily_of_sieveBurgess
    {q₁ R Z : ℕ} (hR : 1 < R) (hRZ : R < Z)
    (hq₁ : Squarefree q₁)
    (W : Finset (TaoExceptionalCharacterDatum q₁ Z)) (E : ℝ)
    (hZ : (taoDyadicPrimeBand Z).Nonempty)
    (hE : 0 ≤ E)
    (hsep : IsSeparatedTaoExceptionalFamily W)
    (hburgess : TaoCubefreeSievePrefixBound R Z E) :
    ∑ a ∈ W,
        ‖finiteNormalizedPrimeBandSum Z a.value‖ ^ 2 ≤
      ((((2 * Z : ℕ) : ℝ) * (2 / Real.log R) +
          (R : ℝ) * (1 + Real.log R) ^ 3) +
        ((W.card - 1 : ℕ) : ℝ) *
          (((R : ℝ) * (1 + Real.log R) ^ 3) * E)) /
        (taoDyadicPrimeBand Z).card := by
  apply sum_finiteNormalizedPrimeBandSum_sq_le_exceptionalFamily
    hR hRZ W E hZ hE
  intro a ha b hb hba d hd hdR
  exact hburgess (taoExceptionalPairPeriod a b)
    (taoExceptionalPairCharacter a b)
    (taoExceptionalPairPeriod_squarefree a b hq₁)
    (taoExceptionalPairPeriod_cast_le_rpow a b
      (Nat.pos_of_ne_zero hq₁.ne_zero))
    (taoExceptionalPairCharacter_ne_one_of_changeLevel_ne a b
      (hsep a ha b hb hba)) d hd hdR

/-- Source-shaped explicit Burgess theorem plus the two elementary prefix
side conditions imply the complete finite exceptional-family estimate. -/
theorem sum_finiteNormalizedPrimeBandSum_sq_le_exceptionalFamily_of_explicitBurgess
    {C : ℝ} {H₀ q₁ R Z : ℕ}
    (hC : 0 ≤ C)
    (hR : 1 < R) (hRZ : R < Z)
    (hq₁ : Squarefree q₁)
    (W : Finset (TaoExceptionalCharacterDatum q₁ Z))
    (hZ : (taoDyadicPrimeBand Z).Nonempty)
    (hsep : IsSeparatedTaoExceptionalFamily W)
    (hburgess : TaoExplicitCubefreeBurgessBound C H₀)
    (hlarge : ∀ d ∈ (primorial R).divisors, (d : ℝ) ≤ R →
      H₀ ≤ (2 * Z - 1) / d)
    (hrange : ∀ d ∈ (primorial R).divisors, (d : ℝ) ≤ R →
      (Z : ℝ) ^ taoBurgessPeriodExponent ≤
        (((2 * Z - 1) / d : ℕ) : ℝ) ^ (31 / 10 : ℝ)) :
    ∑ a ∈ W,
        ‖finiteNormalizedPrimeBandSum Z a.value‖ ^ 2 ≤
      ((((2 * Z : ℕ) : ℝ) * (2 / Real.log R) +
          (R : ℝ) * (1 + Real.log R) ^ 3) +
        ((W.card - 1 : ℕ) : ℝ) *
          (((R : ℝ) * (1 + Real.log R) ^ 3) *
            (C * (2 * Z : ℝ) ^
              (1 - taoBurgessSavingExponent)))) /
        (taoDyadicPrimeBand Z).card := by
  apply sum_finiteNormalizedPrimeBandSum_sq_le_exceptionalFamily_of_sieveBurgess
    hR hRZ hq₁ W
      (C * (2 * Z : ℝ) ^ (1 - taoBurgessSavingExponent)) hZ
  · positivity
  · exact hsep
  · exact hburgess.toSievePrefixBound hC hlarge hrange

end

end Tao2026
