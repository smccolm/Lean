import Tao2026.BurgessWeilPrimeKummerNewtonLiteralWeil
import Tao2026.BurgessWeilPrimeKummerLegendreDeterminantIntegral

/-!
# Unconditional low-degree higher-root Newton integrality

The quadratic-extension correlation is decomposed into Frobenius orbits.
Its fixed points are the base field and contribute the squared base weights;
the non-fixed points occur in pairs.  Comparing this with the coordinate-swap
decomposition of the square of the base correlation writes the second Newton
coefficient as an explicit sum of algebraic integers.

Consequently the Newton elementary coefficients in degrees zero, one, and
two are integral for every prime root-multiset input, without assuming a
Frobenius spectrum, Weil bounds, or a recurrence.
-/

namespace Tao2026

open Finset
open scoped BigOperators

noncomputable section

theorem complexNewtonElementary_one (u : ℕ → ℂ) :
    complexNewtonElementary u 1 = u 1 := by
  rw [show 1 = 0 + 1 by omega, complexNewtonElementary_succ]
  have hadone : {a ∈ Finset.antidiagonal 1 | a.1 < 1} =
      {(0, 1)} := by decide
  norm_num only at hadone ⊢
  rw [hadone]
  simp [complexNewtonElementary]

theorem quadratic_rootMultisetWeight_frob
    (p : ℕ) [NeZero p] [Fact p.Prime]
    (χ : MulChar (ZMod p) ℂ) (R : Multiset (ZMod p))
    (x : FiniteField.Extension (ZMod p) p 2) :
    let E := FiniteField.Extension (ZMod p) p 2
    let χE := finiteFieldNormLiftMulChar (ZMod p) E χ
    let σ : E ≃ₐ[ZMod p] E :=
      FiniteField.frobeniusAlgEquivOfAlgebraic _ _
    (∏ r ∈ R.toFinset,
        (χE ^ R.count r) (σ x - algebraMap (ZMod p) E r)) =
      ∏ r ∈ R.toFinset,
        (χE ^ R.count r) (x - algebraMap (ZMod p) E r) := by
  dsimp only
  let E := FiniteField.Extension (ZMod p) p 2
  let χE := finiteFieldNormLiftMulChar (ZMod p) E χ
  let σ : E ≃ₐ[ZMod p] E :=
    FiniteField.frobeniusAlgEquivOfAlgebraic _ _
  apply Finset.prod_congr rfl
  intro r hr
  rw [show σ x - algebraMap (ZMod p) E r =
      σ (x - algebraMap (ZMod p) E r) by simp]
  change ((finiteFieldNormLiftMulChar (ZMod p) E χ) ^ R.count r)
      (σ (x - algebraMap (ZMod p) E r)) = _
  rw [← map_pow (finiteFieldNormLiftMulChar (ZMod p) E) χ (R.count r)]
  rw [finiteFieldNormLiftMulChar_apply]
  rw [show Algebra.norm (ZMod p) (σ (x - algebraMap (ZMod p) E r)) =
      Algebra.norm (ZMod p) (x - algebraMap (ZMod p) E r) by
    exact quadratic_norm_frob p _]
  exact (finiteFieldNormLiftMulChar_apply (ZMod p) E
    (χ ^ R.count r) (x - algebraMap (ZMod p) E r)).symm

theorem quadratic_rootMultisetWeight_algebraMap
    (p : ℕ) [NeZero p] [Fact p.Prime]
    (χ : MulChar (ZMod p) ℂ) (R : Multiset (ZMod p)) (a : ZMod p) :
    let E := FiniteField.Extension (ZMod p) p 2
    let χE := finiteFieldNormLiftMulChar (ZMod p) E χ
    (∏ r ∈ R.toFinset,
        (χE ^ R.count r)
          (algebraMap (ZMod p) E a - algebraMap (ZMod p) E r)) =
      (∏ r ∈ R.toFinset, (χ ^ R.count r) (a - r)) ^ 2 := by
  dsimp only
  let E := FiniteField.Extension (ZMod p) p 2
  have hfinrank : Module.finrank (ZMod p)
      (FiniteField.Extension (ZMod p) p 2) = 2 := by
    refine Nat.pow_right_injective (Finite.one_lt_card :
      2 ≤ Nat.card (ZMod p)) ?_
    simp only [← Module.natCard_eq_pow_finrank,
      FiniteField.natCard_extension]
  rw [← Finset.prod_pow]
  apply Finset.prod_congr rfl
  intro r hr
  rw [← map_sub]
  rw [← map_pow (finiteFieldNormLiftMulChar (ZMod p) E) χ (R.count r)]
  rw [finiteFieldNormLiftMulChar_apply, Algebra.norm_algebraMap, hfinrank]
  exact map_pow (χ ^ R.count r) (a - r) 2

theorem quadratic_rootMultisetCorrelation_orbit_decomposition
    (p : ℕ) [NeZero p] [Fact p.Prime]
    (χ : MulChar (ZMod p) ℂ) (R : Multiset (ZMod p)) :
    let E := FiniteField.Extension (ZMod p) p 2
    letI : Fintype E := Fintype.ofFinite E
    letI : DecidableEq E := Classical.decEq E
    letI : LinearOrder E := Equiv.linearOrder (Fintype.equivFin E)
    let χE := finiteFieldNormLiftMulChar (ZMod p) E χ
    let σ : E ≃ₐ[ZMod p] E :=
      FiniteField.frobeniusAlgEquivOfAlgebraic _ _
    finiteFieldRootMultisetCorrelation (ZMod p) E χE R =
      ∑ a : ZMod p,
          (∏ r ∈ R.toFinset, (χ ^ R.count r) (a - r)) ^ 2 +
        2 * ∑ x ∈ Finset.univ.filter (fun x : E => x < σ x),
          ∏ r ∈ R.toFinset,
            (χE ^ R.count r) (x - algebraMap (ZMod p) E r) := by
  dsimp only
  let E := FiniteField.Extension (ZMod p) p 2
  letI : Fintype E := Fintype.ofFinite E
  letI : DecidableEq E := Classical.decEq E
  letI : LinearOrder E := Equiv.linearOrder (Fintype.equivFin E)
  let χE := finiteFieldNormLiftMulChar (ZMod p) E χ
  let σ : E ≃ₐ[ZMod p] E :=
    FiniteField.frobeniusAlgEquivOfAlgebraic _ _
  let w : E → ℂ := fun x =>
    ∏ r ∈ R.toFinset,
      (χE ^ R.count r) (x - algebraMap (ZMod p) E r)
  have horbit :
      (∑ x : E, w x) =
        ∑ x ∈ Finset.univ.filter (fun x : E => σ x = x), w x +
          2 * ∑ x ∈ Finset.univ.filter (fun x : E => x < σ x), w x := by
    apply sum_involution σ.toEquiv
    · intro x
      exact quadratic_frob_involutive p x
    · intro x
      exact quadratic_rootMultisetWeight_frob p χ R x
  have hfixed :
      (∑ x ∈ Finset.univ.filter (fun x : E => σ x = x), w x) =
        ∑ a : ZMod p,
          (∏ r ∈ R.toFinset, (χ ^ R.count r) (a - r)) ^ 2 := by
    symm
    refine Finset.sum_bij
      (fun a (_ha : a ∈ (Finset.univ : Finset (ZMod p))) =>
        algebraMap (ZMod p) E a) ?_ ?_ ?_ ?_
    · intro a ha
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      simp [σ]
    · intro a₁ ha₁ a₂ ha₂ h
      exact (algebraMap (ZMod p) E).injective h
    · intro x hx
      have hxfix : σ x = x := (Finset.mem_filter.mp hx).2
      obtain ⟨a, ha⟩ := (quadratic_frob_fixed_iff p x).mp (by
        simpa [σ] using hxfix)
      exact ⟨a, Finset.mem_univ a, ha⟩
    · intro a ha
      change (∏ r ∈ R.toFinset, (χ ^ R.count r) (a - r)) ^ 2 =
        w (algebraMap (ZMod p) E a)
      exact (quadratic_rootMultisetWeight_algebraMap p χ R a).symm
  unfold finiteFieldRootMultisetCorrelation
  change (∑ x : E, w x) = _
  rw [horbit, hfixed]

theorem primeRootMultisetSecondNewtonNumerator_integral
    (p : ℕ) [NeZero p] [Fact p.Prime]
    (χ : MulChar (ZMod p) ℂ) (R : Multiset (ZMod p)) :
    IsIntegral ℤ
      ((primeRootMultisetExtensionCorrelation p χ R 0 ^ 2 +
        primeRootMultisetExtensionCorrelation p χ R 1) / 2) := by
  let u : ZMod p → ℂ := fun a =>
    ∏ r ∈ R.toFinset, (χ ^ R.count r) (a - r)
  let P := ZMod p × ZMod p
  letI : Fintype P := inferInstance
  letI : DecidableEq P := Classical.decEq P
  letI : LinearOrder P := Equiv.linearOrder (Fintype.equivFin P)
  let swap : P ≃ P :=
    { toFun := fun z => (z.2, z.1)
      invFun := fun z => (z.2, z.1)
      left_inv := fun z => by cases z; rfl
      right_inv := fun z => by cases z; rfl }
  let B : ℂ :=
    ∑ z ∈ Finset.univ.filter (fun z : P => z < swap z), u z.1 * u z.2
  let D : ℂ := ∑ a : ZMod p, u a ^ 2
  let E := FiniteField.Extension (ZMod p) p 2
  letI : Fintype E := Fintype.ofFinite E
  letI : DecidableEq E := Classical.decEq E
  letI : LinearOrder E := Equiv.linearOrder (Fintype.equivFin E)
  let χE := finiteFieldNormLiftMulChar (ZMod p) E χ
  let σ : E ≃ₐ[ZMod p] E :=
    FiniteField.frobeniusAlgEquivOfAlgebraic _ _
  let w : E → ℂ := fun x =>
    ∏ r ∈ R.toFinset,
      (χE ^ R.count r) (x - algebraMap (ZMod p) E r)
  let X : ℂ :=
    ∑ x ∈ Finset.univ.filter (fun x : E => x < σ x), w x
  have hbase :
      primeRootMultisetExtensionCorrelation p χ R 0 ^ 2 =
        D + 2 * B := by
    change (∑ a : ZMod p, u a) ^ 2 = D + 2 * B
    exact sum_sq_orbit_decomposition u
  have hext :
      primeRootMultisetExtensionCorrelation p χ R 1 =
        D + 2 * X := by
    change finiteFieldRootMultisetCorrelation (ZMod p) E χE R = D + 2 * X
    exact quadratic_rootMultisetCorrelation_orbit_decomposition p χ R
  have hformula :
      (primeRootMultisetExtensionCorrelation p χ R 0 ^ 2 +
          primeRootMultisetExtensionCorrelation p χ R 1) / 2 =
        D + B + X := by
    rw [hbase, hext]
    ring
  have hu (a : ZMod p) : IsIntegral ℤ (u a) := by
    unfold u
    exact IsIntegral.prod (fun r : ZMod p =>
      (χ ^ R.count r) (a - r))
      (fun r _hr => isIntegral_finiteFieldMulChar_apply
        (χ ^ R.count r) (a - r))
  have hD : IsIntegral ℤ D := by
    unfold D
    exact IsIntegral.sum (fun a : ZMod p => u a ^ 2)
      (fun a _ha => (hu a).pow 2)
  have hB : IsIntegral ℤ B := by
    unfold B
    exact IsIntegral.sum (fun z : P => u z.1 * u z.2)
      (fun z _hz => (hu z.1).mul (hu z.2))
  have hX : IsIntegral ℤ X := by
    unfold X w
    exact IsIntegral.sum
      (fun x : E => ∏ r ∈ R.toFinset,
        (χE ^ R.count r) (x - algebraMap (ZMod p) E r))
      (fun x _hx => IsIntegral.prod
        (fun r : ZMod p =>
          (χE ^ R.count r) (x - algebraMap (ZMod p) E r))
        (fun r _hr => isIntegral_finiteFieldMulChar_apply
          (χE ^ R.count r) (x - algebraMap (ZMod p) E r)))
  rw [hformula]
  exact (hD.add hB).add hX

theorem primeRootMultisetNewtonElementary_two_integral
    (p : ℕ) [NeZero p] [Fact p.Prime]
    (χ : MulChar (ZMod p) ℂ) (R : Multiset (ZMod p)) :
    IsIntegral ℤ (primeRootMultisetNewtonElementary p χ R 2) := by
  have h := primeRootMultisetSecondNewtonNumerator_integral p χ R
  convert h using 1
  rw [primeRootMultisetNewtonElementary, show 2 = 1 + 1 by omega,
    complexNewtonElementary_succ]
  have had : {a ∈ Finset.antidiagonal 2 | a.1 < 2} =
      {(0, 2), (1, 1)} := by decide
  norm_num only at had ⊢
  rw [had]
  norm_num [Finset.sum_insert]
  rw [complexNewtonElementary_one]
  norm_num [Finset.sum_insert, complexNewtonElementary,
    primeRootMultisetNewtonPowerSum]
  ring

/-- Every literal root-multiset extension correlation is an algebraic
integer. -/
theorem isIntegral_primeRootMultisetExtensionCorrelation
    (p : ℕ) [NeZero p] [Fact p.Prime]
    (χ : MulChar (ZMod p) ℂ) (R : Multiset (ZMod p)) (q : ℕ) :
    IsIntegral ℤ (primeRootMultisetExtensionCorrelation p χ R q) := by
  rw [← primeKummerExtensionCorrelation_eq_rootMultiset p χ R q]
  exact isIntegral_primeKummerExtensionCorrelation p χ
    (primeKummerRootMultisetPolynomial R) q

theorem primeRootMultisetNewtonElementary_zero_integral
    (p : ℕ) [NeZero p] [Fact p.Prime]
    (χ : MulChar (ZMod p) ℂ) (R : Multiset (ZMod p)) :
    IsIntegral ℤ (primeRootMultisetNewtonElementary p χ R 0) := by
  rw [primeRootMultisetNewtonElementary, complexNewtonElementary]
  exact isIntegral_one

theorem primeRootMultisetNewtonElementary_one_integral
    (p : ℕ) [NeZero p] [Fact p.Prime]
    (χ : MulChar (ZMod p) ℂ) (R : Multiset (ZMod p)) :
    IsIntegral ℤ (primeRootMultisetNewtonElementary p χ R 1) := by
  rw [primeRootMultisetNewtonElementary, complexNewtonElementary_one,
    primeRootMultisetNewtonPowerSum]
  exact (isIntegral_primeRootMultisetExtensionCorrelation p χ R 0).neg

/-- The first three Newton elementary coefficients are unconditional. -/
theorem primeRootMultisetNewtonElementary_integral_of_le_two
    (p : ℕ) [NeZero p] [Fact p.Prime]
    (χ : MulChar (ZMod p) ℂ) (R : Multiset (ZMod p))
    (j : ℕ) (hj : j ≤ 2) :
    IsIntegral ℤ (primeRootMultisetNewtonElementary p χ R j) := by
  interval_cases j
  · exact primeRootMultisetNewtonElementary_zero_integral p χ R
  · exact primeRootMultisetNewtonElementary_one_integral p χ R
  · exact primeRootMultisetNewtonElementary_two_integral p χ R

end

end Tao2026
