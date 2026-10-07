/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanModularForms contributors

The q-parameter and sparse-sum lemmas adapt LevelRaise.lean at
LeanModularForms 7c41b9b1747d47298f76bdb51f07031087702198.
-/
import Dubon2026.ModularDegeneracy

/-! # Fourier coefficients of actual Gamma0 degeneracy maps -/

namespace Dubon2026

open Matrix.SpecialLinearGroup CongruenceSubgroup UpperHalfPlane
open scoped MatrixGroups ModularForm

noncomputable section

/-- **qParam scaling under `d`-dilation.** For positive `N : ℝ` and
positive integer `d`, `qParam N (d · z) = (qParam N z) ^ d`. -/
lemma qParam_nat_mul_eq_pow (h : ℝ) (d : ℕ) (z : ℂ) :
    Function.Periodic.qParam h ((d : ℂ) * z) =
      (Function.Periodic.qParam h z) ^ d := by
  simp only [Function.Periodic.qParam, ← Complex.exp_nat_mul]
  ring_nf

/-- **Sparse reindexing** of a HasSum over `(q^d)^j` as a HasSum over
`q^n` with zero coefficients at non-multiples of `d`.  For
`HasSum (j ↦ a j • (q ^ d) ^ j) S`, we obtain
`HasSum (n ↦ if d ∣ n then a (n / d) • q ^ n else 0) S`. -/
lemma hasSum_pow_dvd_reindex {d : ℕ} (hd : 0 < d) {a : ℕ → ℂ} {q : ℂ}
    {S : ℂ} (h : HasSum (fun j : ℕ ↦ a j • (q ^ d) ^ j) S) :
    HasSum (fun n : ℕ ↦ if d ∣ n then a (n / d) • q ^ n else 0) S := by
  have hinj : Function.Injective (fun j : ℕ ↦ d * j) :=
    fun _ _ ↦ Nat.mul_left_cancel hd
  have h_zero : ∀ n : ℕ, n ∉ Set.range (fun j : ℕ ↦ d * j) →
      (fun n : ℕ ↦ if d ∣ n then a (n / d) • q ^ n else 0) n = 0 := by
    intro n hn
    refine if_neg fun hdvd ↦ ?_
    obtain ⟨j, rfl⟩ := hdvd
    exact hn ⟨j, rfl⟩
  have h_eq : ((fun n : ℕ ↦ if d ∣ n then a (n / d) • q ^ n else 0) ∘
      (fun j : ℕ ↦ d * j)) = fun j : ℕ ↦ a j • (q ^ d) ^ j := by
    funext j
    simp only [Function.comp_apply]
    rw [if_pos ⟨j, rfl⟩, Nat.mul_div_cancel_left j hd, pow_mul]
  rwa [← hinj.hasSum_iff h_zero, h_eq]


/-- Fourier coefficients of f(dz): a(n/d) on multiples of d and zero otherwise. -/
theorem cuspDegeneracyMap_coeff {M N : ℕ} (d : ℕ) [NeZero d] (h : d * M ∣ N)
    {k : ℤ} (f : CuspForm ((Gamma0 M).map (mapGL ℝ)) k) (n : ℕ) :
    cuspCoefficients (cuspDegeneracyMap d h k f) n =
      if d ∣ n then cuspCoefficients f (n / d) else 0 := by
  have hsum : ∀ τ : ℍ, HasSum (fun j : ℕ =>
      (if d ∣ j then cuspCoefficients f (j / d) else 0) •
        Function.Periodic.qParam 1 (τ : ℂ) ^ j) (cuspDegeneracyMap d h k f τ) := by
    intro τ
    rw [cuspDegeneracyMap_apply]
    have hs := cuspCoefficients_hasSum f (levelRaiseMatrix d • τ)
    rw [coe_levelRaiseMatrix_smul, qParam_nat_mul_eq_pow] at hs
    have hs' := hasSum_pow_dvd_reindex (Nat.pos_of_neZero d) (by
      simpa only [smul_eq_mul] using hs)
    convert hs' using 1
    funext j
    split_ifs <;> simp [smul_eq_mul]
  exact (ModularFormClass.qExpansion_coeff_unique zero_lt_one
    (by simp : (1 : ℝ) ∈ ((Gamma0 N).map (mapGL ℝ)).strictPeriods) hsum n).symm

/-- A genuine dilation by d>1 has zero first Fourier coefficient. -/
theorem cuspDegeneracyMap_coeff_one {M N : ℕ} (d : ℕ) [NeZero d]
    (h : d * M ∣ N) (hd : 1 < d) {k : ℤ}
    (f : CuspForm ((Gamma0 M).map (mapGL ℝ)) k) :
    cuspCoefficients (cuspDegeneracyMap d h k f) 1 = 0 := by
  rw [cuspDegeneracyMap_coeff, if_neg (by simpa [Nat.dvd_one] using hd.ne')]

/-- Evaluation of the nth actual Fourier coefficient is a complex linear map. -/
def cuspCoefficientLinear (N : ℕ) (k : ℤ) (n : ℕ) :
    CuspForm ((Gamma0 N).map (mapGL ℝ)) k →ₗ[ℂ] ℂ where
  toFun f := cuspCoefficients f n
  map_add' f g := by
    change (qExpansion 1 (f + g)).coeff n = _
    rw [ModularForm.qExpansion_add zero_lt_one (by simp), map_add]
    rfl
  map_smul' c f := by
    change (qExpansion 1 (c • f)).coeff n = _
    rw [ModularForm.qExpansion_smul zero_lt_one (by simp), PowerSeries.coeff_smul]
    rfl

end
end Dubon2026
