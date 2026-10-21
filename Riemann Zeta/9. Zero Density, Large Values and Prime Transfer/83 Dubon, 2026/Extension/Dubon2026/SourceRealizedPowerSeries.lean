import Mathlib.NumberTheory.ModularForms.NormTrace
import Mathlib.Tactic

/-! DUB-17/18 -> cusp-form lower dimension bound -> regular differential
realization -> original finite function-field extension -> modular polynomial
relations -> rational coefficient descent. This selects the literal Laurent
principal-part removal and the actual analytic realization argument, reusing
pinned weight-zero constancy and q-expansion coefficient uniqueness. No
polynomial relation or coefficient descent is postulated.
Adapted from anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2,
P2M/Sol/S_ModularCurve_coeff_eq_zero_of_hasSum_of_slash_invariant.lean.
-/
namespace Dubon2026.SourceFunctionField
noncomputable section
open Matrix.SpecialLinearGroup UpperHalfPlane Complex Filter Topology Function Polynomial
open scoped MatrixGroups ModularForm
local notation "𝕢" => Function.Periodic.qParam

namespace Realized

variable {h : ℝ} {F : ℍ → ℂ} {c : ℕ → ℂ}

lemma norm_qParam_lt_one_of_pos (hh : 0 < h) (τ : ℍ) : ‖𝕢 h (τ : ℂ)‖ < 1 := by
  rw [Periodic.norm_qParam, Real.exp_lt_one_iff, neg_mul, coe_im, neg_mul, neg_div, neg_lt_zero]
  exact div_pos (by positivity [τ.im_pos]) hh

lemma hasSum_cuspFunction_punctured (hh : 0 < h)
    (hF : ∀ τ : ℍ, HasSum (fun m : ℕ => c m * 𝕢 h (τ : ℂ) ^ m) (F τ)) {q : ℂ} (hq : ‖q‖ < 1)
    (hq1 : q ≠ 0) : HasSum (fun m : ℕ => c m * q ^ m) (cuspFunction h F q) := by
  have h1 := Periodic.im_invQParam_pos_of_norm_lt_one hh hq hq1
  let τ : ℍ := ⟨Periodic.invQParam h q, h1⟩
  have h2 := Periodic.cuspFunction_eq_of_nonzero h (F ∘ ofComplex) hq1
  have h3 : cuspFunction h F q = F τ := by
    simpa [τ, cuspFunction, UpperHalfPlane.ofComplex_apply_of_im_pos h1] using h2
  have h4 : 𝕢 h (τ : ℂ) = q := Periodic.qParam_right_inv hh.ne' hq1
  rw [h3, ← h4]
  exact hF τ

lemma hasFPowerSeriesOnBall_update (hh : 0 < h)
    (hF : ∀ τ : ℍ, HasSum (fun m : ℕ => c m * 𝕢 h (τ : ℂ) ^ m) (F τ)) :
    HasFPowerSeriesOnBall (update (cuspFunction h F) 0 (c 0)) (.ofScalars ℂ c) 0 1 := by
  constructor
  · refine le_of_forall_lt_imp_le_of_dense fun r hr ↦ ?_
    rcases eq_or_ne r 0 with rfl | hr'
    · simp
    · lift r to NNReal using hr.ne_top
      letI : FiniteDimensional ℝ ℂ := basisOneI.finiteDimensional_of_finite
      apply FormalMultilinearSeries.le_radius_of_summable
      simpa [norm_mul, mul_comm] using
        (hasSum_cuspFunction_punctured hh hF (q := r) (by simpa using hr)
          (mod_cast hr')).summable.norm
  · simp
  · intro y hy
    rw [zero_add]
    rw [← ENNReal.coe_one, Metric.eball_coe, NNReal.coe_one, mem_ball_zero_iff] at hy
    rcases eq_or_ne y 0 with rfl | hy'
    · simpa +contextual [zero_pow_eq] using hasSum_ite_eq 0 (c 0)
    · simpa [update_of_ne hy', mul_comm] using hasSum_cuspFunction_punctured hh hF hy hy'

/-- The actual cusp function with the constant coefficient filled in at zero. -/
def discFun (h : ℝ) (F : ℍ → ℂ) (c : ℕ → ℂ) : ℂ → ℂ := update (cuspFunction h F) 0 (c 0)

lemma hasSum_discFun (hh : 0 < h) (hF : ∀ τ : ℍ, HasSum (fun m : ℕ => c m * 𝕢 h (τ : ℂ) ^ m) (F τ))
    {q : ℂ} (hq : ‖q‖ < 1) : HasSum (fun m : ℕ => c m * q ^ m) (discFun h F c q) := by
  have hy : q ∈ Metric.eball (0 : ℂ) 1 := by
    rw [← ENNReal.coe_one, Metric.eball_coe]; simpa using hq
  have h := (hasFPowerSeriesOnBall_update hh hF).hasSum hy
  rw [zero_add] at h
  simpa [discFun, mul_comm] using h

lemma apply_eq_discFun (hh : 0 < h) (hF : ∀ τ : ℍ, HasSum (fun m : ℕ => c m * 𝕢 h (τ : ℂ) ^ m) (F τ))
    (τ : ℍ) : F τ = discFun h F c (𝕢 h (τ : ℂ)) :=
  (hF τ).unique (hasSum_discFun hh hF (norm_qParam_lt_one_of_pos hh τ))

lemma differentiableOn_discFun (hh : 0 < h)
    (hF : ∀ τ : ℍ, HasSum (fun m : ℕ => c m * 𝕢 h (τ : ℂ) ^ m) (F τ)) :
    DifferentiableOn ℂ (discFun h F c) (Metric.ball 0 1) := by
  have h1 := (hasFPowerSeriesOnBall_update hh hF).differentiableOn
  rwa [← ENNReal.coe_one, Metric.eball_coe, NNReal.coe_one] at h1

lemma continuousAt_discFun (hh : 0 < h)
    (hF : ∀ τ : ℍ, HasSum (fun m : ℕ => c m * 𝕢 h (τ : ℂ) ^ m) (F τ)) {q : ℂ} (hq : ‖q‖ < 1) :
    ContinuousAt (discFun h F c) q :=
  ((differentiableOn_discFun hh hF).differentiableAt
    (Metric.isOpen_ball.mem_nhds (by simpa using hq))).continuousAt

lemma discFun_zero : discFun h F c 0 = c 0 := by simp [discFun]

theorem mdifferentiable (hh : 0 < h)
    (hF : ∀ τ : ℍ, HasSum (fun m : ℕ => c m * 𝕢 h (τ : ℂ) ^ m) (F τ)) :
    MDifferentiable (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) F := by
  rw [UpperHalfPlane.mdifferentiable_iff]
  have h1 : DifferentiableOn ℂ (fun z : ℂ => discFun h F c (𝕢 h z)) {z : ℂ | 0 < z.im} := by
    intro z hz
    have hzq : ‖𝕢 h z‖ < 1 := by
      have := norm_qParam_lt_one_of_pos hh ⟨z, hz⟩
      simpa using this
    exact (((differentiableOn_discFun hh hF).differentiableAt
      (Metric.isOpen_ball.mem_nhds (by simpa using hzq))).comp z
      ((Periodic.differentiable_qParam (h := h)) z)).differentiableWithinAt
  refine h1.congr fun z hz => ?_
  simp only [Function.comp_apply, apply_eq_discFun hh hF, ofComplex_apply_of_im_pos hz]

theorem tendsto_atImInfty (hh : 0 < h)
    (hF : ∀ τ : ℍ, HasSum (fun m : ℕ => c m * 𝕢 h (τ : ℂ) ^ m) (F τ)) :
    Tendsto F atImInfty (𝓝 (c 0)) := by
  have h1 : Tendsto (fun τ : ℍ => discFun h F c (𝕢 h (τ : ℂ))) atImInfty (𝓝 (discFun h F c 0)) :=
    (continuousAt_discFun hh hF (q := 0) (by simp)).tendsto.comp (qParam_tendsto_atImInfty hh)
  rw [discFun_zero] at h1
  exact h1.congr fun τ => (apply_eq_discFun hh hF τ).symm

theorem isBoundedAtImInfty (hh : 0 < h)
    (hF : ∀ τ : ℍ, HasSum (fun m : ℕ => c m * 𝕢 h (τ : ℂ) ^ m) (F τ)) :
    IsBoundedAtImInfty F :=
  (tendsto_atImInfty hh hF).isBigO_one ℝ

end Realized

end
end Dubon2026.SourceFunctionField
