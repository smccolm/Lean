import Dubon2026.SourceBernoulliPrimeDenominator

/-! DUB-17 Theorem 2.6 / DUB-18 Corollary 8.2 -> higher symmetric-power
continuation -> automorphy and residual association -> original Frobenius/inertia
-> modular-curve good reduction -> exact residue-field degree -> prime j
nonmembership. The integral Eisenstein series of weight ell - 1 supplies the
Hasse polynomial input with nonzero constant reduction. This file does not yet
construct that polynomial or prove unconditional prime nonmembership.
Adapted from anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2,
S_ModularCurve_StarBank_eisInt_series. Reuses the pinned Mathlib
von Staudt-Clausen and Eisenstein q-expansion theorems directly. -/
namespace Dubon2026.SourceFunctionField
noncomputable section
open scoped ArithmeticFunction.sigma
open Finset

theorem eisInt_not_dvd_num {ℓ : ℕ} [Fact ℓ.Prime] (hℓ5 : 5 ≤ ℓ) :
    ¬ (ℓ : ℤ) ∣ (bernoulli (ℓ - 1)).num := by
  intro hdvd
  have hden := eisInt_dvd_den hℓ5
  have hnum : ℓ ∣ (bernoulli (ℓ - 1)).num.natAbs := by
    have := Int.natAbs_dvd_natAbs.mpr hdvd
    simpa using this
  have hcop := (bernoulli (ℓ - 1)).reduced
  have hgcd : ℓ ∣ Nat.gcd (bernoulli (ℓ - 1)).num.natAbs (bernoulli (ℓ - 1)).den :=
    Nat.dvd_gcd hnum hden
  unfold Nat.Coprime at hcop
  rw [hcop] at hgcd
  exact (Nat.Prime.one_lt (Fact.out : ℓ.Prime)).ne' (Nat.dvd_one.mp hgcd)

theorem eisInt_bernoulli_ne_zero
    {ℓ : ℕ} [Fact ℓ.Prime] (hℓ5 : 5 ≤ ℓ) : bernoulli (ℓ - 1) ≠ 0 := by
  intro h
  have := eisInt_dvd_den hℓ5
  rw [h, Rat.den_zero] at this
  exact (Nat.Prime.one_lt (Fact.out : ℓ.Prime)).ne' (Nat.dvd_one.mp this)

theorem eisInt_coeff {ℓ : ℕ} [Fact ℓ.Prime] (hℓ5 : 5 ≤ ℓ)
    (hk : 3 ≤ ℓ - 1) (m : ℕ) :
    ∃ z : ℤ, ((bernoulli (ℓ - 1)).num : ℂ)
          * (UpperHalfPlane.qExpansion 1 (ModularForm.E hk)).coeff m = ↑z
        ∧ (m = 0 → z = (bernoulli (ℓ - 1)).num) ∧ (1 ≤ m → (ℓ : ℤ) ∣ z) := by
  classical
  have hℓp : ℓ.Prime := Fact.out
  have hkeven : Even (ℓ - 1) := by
    obtain ⟨c, hc⟩ := hℓp.odd_of_ne_two (by omega); exact ⟨c, by omega⟩
  set B := bernoulli (ℓ - 1) with hBdef
  have hB0 : B ≠ 0 := eisInt_bernoulli_ne_zero hℓ5
  have hcoeff := EisensteinSeries.E_qExpansion_coeff hk hkeven m
  rcases Nat.eq_zero_or_pos m with hm0 | hm1
  · subst hm0
    refine ⟨B.num, ?_, fun _ => rfl, by omega⟩
    rw [hcoeff]; simp
  ·
    have hm1' : m ≠ 0 := hm1.ne'
    rw [hcoeff, if_neg hm1']
    refine ⟨-(2 * (↑(ℓ - 1) : ℤ) * (↑B.den : ℤ) * (↑(σ (ℓ - 1 - 1) m) : ℤ)), ?_, ?_, ?_⟩
    ·
      have hnum : (B.num : ℂ) ≠ 0 := by
        exact_mod_cast Rat.num_ne_zero.mpr hB0
      have hcast : ((B : ℚ) : ℂ) = (B.num : ℂ) / (B.den : ℂ) := by
        exact_mod_cast Rat.cast_def (K := ℂ) B
      rw [hcast]
      have hden0 : (B.den : ℂ) ≠ 0 := by
        exact_mod_cast B.den_ne_zero
      field_simp
      push_cast
      ring
    · intro h; omega
    · intro _
      have hd : (ℓ : ℤ) ∣ (↑B.den : ℤ) :=
        Int.natCast_dvd_natCast.mpr (eisInt_dvd_den hℓ5)
      exact dvd_neg.mpr ((hd.mul_left _).mul_right _)


end
end Dubon2026.SourceFunctionField
