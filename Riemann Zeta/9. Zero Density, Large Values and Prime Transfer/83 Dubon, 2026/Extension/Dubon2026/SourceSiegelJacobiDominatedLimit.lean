import Dubon2026.SourceSiegelJacobiProductBounds
import Mathlib.Analysis.Normed.Group.Tannery

/-! DUB-17/18 -> original Gamma1 degree/genus preservation -> level-power
slash integrality -> peaked auxiliary -> Siegel-product transformation
and holomorphy -> Jacobi theta product. These are the exact convergence
bounds for the finite Gaussian approximation. Mathlib supplies the
geometric-product convergence and dominated convergence; the source
quotient bounds discharge their actual denominator hypotheses.
Adapted from anthropics/fermats-last-theorem, Apache-2.0, revision
6e837e75355538c7f80bab5b956861e86c4eacc2,
S_jacobiTheta_two_eq_tprod. -/
namespace Dubon2026.SourceFunctionField.GammaOne.PeakedAuxiliary.JacobiProduct
open Finset Filter Topology
variable {Q : ℂ}

/-- The actual finite Gaussian sum extended by zero outside its interval. -/
def fam (c : ℕ → ℤ → ℂ) (t : ℤ → ℂ) (N : ℕ) (j : ℤ) : ℂ :=
  if -(N : ℤ) ≤ j ∧ j ≤ N then c N j * t j else 0

theorem sum_Icc_eq_tsum_fam (c : ℕ → ℤ → ℂ) (t : ℤ → ℂ) (N : ℕ) :
    ∑ j ∈ Finset.Icc (-(N : ℤ)) N, c N j * t j = ∑' j, fam c t N j := by
  rw [tsum_eq_sum (s := Finset.Icc (-(N : ℤ)) N)]
  · refine Finset.sum_congr rfl fun j hj => ?_
    rw [Finset.mem_Icc] at hj
    rw [fam, if_pos hj]
  · intro j hj
    rw [Finset.mem_Icc] at hj
    rw [fam, if_neg hj]

theorem tendsto_sum_Icc (hQ : ‖Q‖ < 1) {t : ℤ → ℂ} (ht : Summable fun j => ‖t j‖)
    (c : ℕ → ℤ → ℂ)
    (hc : ∀ (N : ℕ) (j : ℤ), -(N : ℤ) ≤ j → j ≤ N →
      c N j = qfact Q (2 * N) / (qfact Q (N + j).toNat * qfact Q (N - j).toNat)) :
    Tendsto (fun N : ℕ => ∑ j ∈ Finset.Icc (-(N : ℤ)) N, c N j * t j) atTop
      (𝓝 ((∏' n : ℕ, (1 - Q ^ (n + 1)))⁻¹ * ∑' j : ℤ, t j)) := by
  classical
  have hE0 : (∏' n : ℕ, (1 - Q ^ (n + 1))) ≠ 0 := tprod_one_sub_pow_ne_zero hQ
  have he0 : 0 < ∏' n : ℕ, ((1 : ℝ) - ‖Q‖ ^ (n + 1)) := tprod_pfact_pos hQ
  have hle : ∀ m, (∏' n : ℕ, ((1 : ℝ) - ‖Q‖ ^ (n + 1))) ≤ ‖qfact Q m‖ := le_norm_qfact hQ
  have hP0 : 0 ≤ Real.exp (∑' n : ℕ, ‖Q‖ ^ (n + 1)) := (Real.exp_pos _).le
  have hPle : ∀ m, ‖qfact Q m‖ ≤ Real.exp (∑' n : ℕ, ‖Q‖ ^ (n + 1)) := norm_qfact_le hQ
  set E : ℂ := ∏' n : ℕ, (1 - Q ^ (n + 1))
  set e : ℝ := ∏' n : ℕ, ((1 : ℝ) - ‖Q‖ ^ (n + 1))
  set P : ℝ := Real.exp (∑' n : ℕ, ‖Q‖ ^ (n + 1))
  simp_rw [sum_Icc_eq_tsum_fam c t]
  rw [← tsum_mul_left]
  refine tendsto_tsum_of_dominated_convergence (bound := fun j => P / (e * e) * ‖t j‖)
    (ht.mul_left _) (fun j => ?_) (Eventually.of_forall fun N j => ?_)
  ·
    have h2 : Tendsto (fun N : ℕ => qfact Q (2 * N)) atTop (𝓝 E) :=
      (tendsto_qfact hQ).comp
        (tendsto_atTop_mono (fun N : ℕ => show N ≤ 2 * N by omega) tendsto_id)
    have hp : Tendsto (fun N : ℕ => qfact Q ((N : ℤ) + j).toNat) atTop (𝓝 E) :=
      (tendsto_qfact hQ).comp
        (tendsto_atTop_mono (fun N : ℕ => show N - j.natAbs ≤ ((N : ℤ) + j).toNat by omega)
          (tendsto_sub_atTop_nat j.natAbs))
    have hm : Tendsto (fun N : ℕ => qfact Q ((N : ℤ) - j).toNat) atTop (𝓝 E) :=
      (tendsto_qfact hQ).comp
        (tendsto_atTop_mono (fun N : ℕ => show N - j.natAbs ≤ ((N : ℤ) - j).toNat by omega)
          (tendsto_sub_atTop_nat j.natAbs))
    have hlim : Tendsto (fun N : ℕ => qfact Q (2 * N) /
        (qfact Q ((N : ℤ) + j).toNat * qfact Q ((N : ℤ) - j).toNat) * t j) atTop
        (𝓝 (E / (E * E) * t j)) :=
      (h2.div (hp.mul hm) (mul_ne_zero hE0 hE0)).mul tendsto_const_nhds
    have hEE : E / (E * E) * t j = E⁻¹ * t j := by
      rw [div_eq_mul_inv, mul_inv, ← mul_assoc, mul_inv_cancel₀ hE0, one_mul]
    rw [← hEE]
    refine hlim.congr' ?_
    filter_upwards [eventually_ge_atTop j.natAbs] with N hN
    have h1 : -(N : ℤ) ≤ j := by omega
    have h1' : j ≤ (N : ℤ) := by omega
    rw [fam, if_pos ⟨h1, h1'⟩, hc N j h1 h1']
  ·
    show ‖fam c t N j‖ ≤ P / (e * e) * ‖t j‖
    by_cases h : -(N : ℤ) ≤ j ∧ j ≤ N
    · rw [fam, if_pos h, hc N j h.1 h.2, norm_mul, norm_div, norm_mul]
      refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
      exact div_le_div₀ hP0 (hPle _) (mul_pos he0 he0)
        (mul_le_mul (hle _) (hle _) he0.le (norm_nonneg _))
    · rw [fam, if_neg h, norm_zero]
      exact mul_nonneg (div_nonneg hP0 (mul_pos he0 he0).le) (norm_nonneg _)


end Dubon2026.SourceFunctionField.GammaOne.PeakedAuxiliary.JacobiProduct
