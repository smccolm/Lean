/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanModularForms contributors

Adapted prime representative factorizations from HeckeT_p.lean at
LeanModularForms 7c41b9b1747d47298f76bdb51f07031087702198.
The target group here is Gamma0, without diamond-operator assumptions.
-/
import Dubon2026.HeckePrimeReindex

/-! # Integral Gamma0 transition matrices for prime Hecke representatives -/

namespace Dubon2026

open Matrix Matrix.SpecialLinearGroup CongruenceSubgroup HeckePrimeReindex
open scoped MatrixGroups

noncomputable section

/-- Away from its pole, an upper prime representative has an integral Gamma0 transition. -/
theorem heckePrime_upper_factor {Q p : ℕ} [NeZero p] (hp : Nat.Prime p)
    (σ : SL(2, ℤ)) (hσ : σ ∈ Gamma0 Q) (b : Fin p)
    (hA : ¬(p : ℤ) ∣ (σ.val 0 0 + b.val * σ.val 1 0)) :
    ∃ δ : SL(2, ℤ), δ ∈ Gamma0 Q ∧
      heckeTriangularMatrix 1 p b.val * mapGL ℝ σ =
        mapGL ℝ δ * heckeTriangularMatrix 1 p (moebiusFin p hp σ.val b).val := by
  haveI : Fact p.Prime := ⟨hp⟩
  set M := σ.val
  have hA_ne : ((M 0 0 + b.val * M 1 0 : ℤ) : ZMod p) ≠ 0 :=
    fun h => hA ((ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp h)
  set j := (((M 0 1 + b.val * M 1 1 : ℤ) : ZMod p) *
    ((M 0 0 + b.val * M 1 0 : ℤ) : ZMod p)⁻¹).val with hj
  have hm : (moebiusFin p hp M b).val = j := by
    simp only [moebiusFin]
    rw [if_neg hA_ne]
  obtain ⟨q, hq⟩ := dvd_sub_mul_inv_val (M 0 1 + b.val * M 1 1)
    (M 0 0 + b.val * M 1 0) hA_ne
  rw [← hj] at hq
  let δ : SL(2, ℤ) :=
    ⟨!![M 0 0 + b.val * M 1 0, q; p * M 1 0, M 1 1 - M 1 0 * j],
      upper_tau_det_eq_one (sl2z_fin_two_det_eq_one σ) p b.val j q hq⟩
  refine ⟨δ, ?_, ?_⟩
  · rw [Gamma0_mem] at hσ ⊢
    change (((p : ℤ) * M 1 0 : ℤ) : ZMod Q) = 0
    push_cast
    rw [hσ, mul_zero]
  · rw [show (moebiusFin p hp σ.val b).val = j from hm]
    apply Units.ext
    ext i l
    fin_cases i <;> fin_cases l <;>
      simp [heckeTriangularMatrix_val, mapGL_coe_matrix,
        Matrix.mul_apply, Fin.sum_univ_two, δ, M] <;>
      first | ring1 | exact_mod_cast (show σ.val 0 1 + b.val * σ.val 1 1 =
        (σ.val 0 0 + b.val * σ.val 1 0) * j + q * p by dsimp [M] at hq; linarith [hq])

/-- At the pole, an upper prime representative changes to the diagonal representative. -/
theorem heckePrime_upper_pole_factor {Q p : ℕ} [NeZero p]
    (σ : SL(2, ℤ)) (hσ : σ ∈ Gamma0 Q) (b : Fin p)
    (hA : (p : ℤ) ∣ (σ.val 0 0 + b.val * σ.val 1 0)) :
    ∃ δ : SL(2, ℤ), δ ∈ Gamma0 Q ∧
      heckeTriangularMatrix 1 p b.val * mapGL ℝ σ =
        mapGL ℝ δ * heckeTriangularMatrix p 1 0 := by
  obtain ⟨a, ha⟩ := hA
  let δ : SL(2, ℤ) :=
    ⟨!![a, σ.val 0 1 + b.val * σ.val 1 1; σ.val 1 0, p * σ.val 1 1],
      upper_div_tau_det_eq_one (sl2z_fin_two_det_eq_one σ) p a b.val
        (by rw [ha]; ring)⟩
  refine ⟨δ, ?_, ?_⟩
  · rw [Gamma0_mem] at hσ ⊢
    exact hσ
  · apply Units.ext
    ext i l
    fin_cases i <;> fin_cases l <;>
      simp [heckeTriangularMatrix_val, mapGL_coe_matrix,
        Matrix.mul_apply, Fin.sum_univ_two, δ] <;>
      first | ring1 | exact_mod_cast (show σ.val 0 0 + b.val * σ.val 1 0 = a * p by linarith [ha])

/-- A diagonal prime representative moves to an upper representative when its lower entry is a unit. -/
theorem heckePrime_lower_factor {Q p : ℕ} [NeZero p] (hp : Nat.Prime p)
    (σ : SL(2, ℤ)) (hσ : σ ∈ Gamma0 Q) (hC : ¬(p : ℤ) ∣ σ.val 1 0) :
    ∃ δ : SL(2, ℤ), δ ∈ Gamma0 Q ∧
      heckeTriangularMatrix p 1 0 * mapGL ℝ σ = mapGL ℝ δ *
        heckeTriangularMatrix 1 p (((σ.val 1 1 : ZMod p) * (σ.val 1 0 : ZMod p)⁻¹).val) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hC_ne : (σ.val 1 0 : ZMod p) ≠ 0 :=
    fun h => hC ((ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp h)
  set j := (((σ.val 1 1 : ZMod p) * (σ.val 1 0 : ZMod p)⁻¹).val) with hj
  obtain ⟨q, hq⟩ := dvd_sub_mul_inv_val (σ.val 1 1) (σ.val 1 0) hC_ne
  rw [← hj] at hq
  let δ : SL(2, ℤ) :=
    ⟨!![p * σ.val 0 0, σ.val 0 1 - σ.val 0 0 * j; σ.val 1 0, q],
      lower_tau_det_eq_one (sl2z_fin_two_det_eq_one σ) p j q hq⟩
  refine ⟨δ, ?_, ?_⟩
  · rw [Gamma0_mem] at hσ ⊢
    exact hσ
  · apply Units.ext
    ext i l
    fin_cases i <;> fin_cases l <;>
      simp [heckeTriangularMatrix_val, mapGL_coe_matrix,
        Matrix.mul_apply, Fin.sum_univ_two, δ] <;>
      first | ring1 | exact_mod_cast (show σ.val 1 1 = σ.val 1 0 * j + q * p by linarith [hq])

/-- At good primes, a divisible lower entry gives an integral Gamma0 diagonal transition. -/
theorem heckePrime_lower_div_factor {Q p : ℕ} [NeZero p] (hpQ : Nat.Coprime p Q)
    (σ : SL(2, ℤ)) (hσ : σ ∈ Gamma0 Q) (hC : (p : ℤ) ∣ σ.val 1 0) :
    ∃ δ : SL(2, ℤ), δ ∈ Gamma0 Q ∧
      heckeTriangularMatrix p 1 0 * mapGL ℝ σ =
        mapGL ℝ δ * heckeTriangularMatrix p 1 0 := by
  obtain ⟨c, hc⟩ := hC
  let δ : SL(2, ℤ) :=
    ⟨!![σ.val 0 0, p * σ.val 0 1; c, σ.val 1 1],
      lower_div_tau_det_eq_one (sl2z_fin_two_det_eq_one σ) p c hc⟩
  refine ⟨δ, ?_, ?_⟩
  · rw [Gamma0_mem] at hσ ⊢
    change (c : ZMod Q) = 0
    rw [hc, Int.cast_mul, Int.cast_natCast] at hσ
    exact (IsUnit.mul_right_eq_zero ((ZMod.isUnit_iff_coprime p Q).mpr hpQ)).mp hσ
  · apply Units.ext
    ext i l
    fin_cases i <;> fin_cases l <;>
      simp [heckeTriangularMatrix_val, mapGL_coe_matrix,
        Matrix.mul_apply, Fin.sum_univ_two, δ] <;>
      first | ring1 | exact_mod_cast (show σ.val 1 0 = c * p by linarith [hc])

end
end Dubon2026
