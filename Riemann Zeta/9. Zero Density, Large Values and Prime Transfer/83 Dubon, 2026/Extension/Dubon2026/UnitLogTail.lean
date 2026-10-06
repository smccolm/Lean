import Dubon2026.LogDeficit

/-! # Quantitative truncation error on unit intervals of the actual vertical family -/

namespace Dubon2026

open MeasureTheory Set

noncomputable section

/-- Difference between the positive-threshold logarithm and the actual totalized logarithm. -/
def logTruncationError (ε : ℝ) (w : ℂ) : ℝ :=
  Real.log (max ‖w‖ ε) - Real.log ‖w‖

theorem logTruncationError_nonneg {ε : ℝ} {w : ℂ} (hw : w ≠ 0) :
    0 ≤ logTruncationError ε w :=
  sub_nonneg.mpr (Real.log_le_log (norm_pos_iff.mpr hw) (le_max_left _ _))

theorem exists_uniform_unit_logTruncationError_bound {a : ℕ → ℂ} {N : ℕ}
    (hN : 1 ≤ N) (ha : a 1 ≠ 0) (σ : ℝ) :
    ∃ (K : ℕ) (η C : ℝ), 0 < K ∧ 0 < η ∧ 0 < C ∧
      ∀ z : PrimeTorus N, ∀ R : ℝ, 0 ≤ R →
        (∫ t in Icc (0 : ℝ) 1,
          logTruncationError (η * Real.exp (-(K : ℝ) * R)) (verticalFamily a N σ z t)) ≤
            (K : ℝ) * C * Real.exp (-R) := by
  obtain ⟨K, η, C, hK, hη, hC, hb⟩ := exists_uniform_vertical_logDeficit_bound hN ha σ
  refine ⟨K, η, C, hK, hη, hC, ?_⟩
  intro z R hR
  calc
    _ = ∫ t in Icc (0 : ℝ) 1, (K : ℝ) * logDeficit K η R (verticalFamily a N σ z t) := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_of_ae (verticalFamily_ne_zero_ae hN ha σ z)] with t ht
      exact log_truncation_eq_mul_logDeficit hK hη R ht
    _ = (K : ℝ) * ∫ t in Icc (0 : ℝ) 1, logDeficit K η R (verticalFamily a N σ z t) :=
      integral_const_mul _ _
    _ ≤ (K : ℝ) * (C * Real.exp (-R)) := mul_le_mul_of_nonneg_left (hb z R hR) (Nat.cast_nonneg K)
    _ = _ := by ring

theorem primeTorusFlow_add (N : ℕ) (t u : ℝ) :
    primeTorusFlow N (t + u) = primeTorusFlow N t + primeTorusFlow N u := by
  funext p
  simp only [primeTorusFlow, Pi.add_apply]
  rw [← AddCircle.coe_add]
  congr 1
  ring

theorem verticalFamily_add_height (a : ℕ → ℂ) (N : ℕ) (σ : ℝ)
    (z : PrimeTorus N) (t u : ℝ) :
    verticalFamily a N σ z (t + u) = verticalFamily a N σ (z + primeTorusFlow N u) t := by
  rw [verticalFamily_eq_torus_translate, verticalFamily_eq_torus_translate, primeTorusFlow_add]
  congr 1
  abel

theorem verticalFamily_zero_phase (a : ℕ → ℂ) (N : ℕ) (σ t : ℝ) :
    verticalFamily a N σ 0 t = dirichletSum a N ((σ : ℂ) + Complex.I * t) := by
  rw [verticalFamily_eq_torus_translate, zero_add, bohrOnTorus_verticalFlow]

end

end Dubon2026
