import TaoTrudgianYang2025.BetaExpandedModelJets

/-!
# Reference inverse jets on the entire positive slope axis

These coordinates use the explicit reciprocal power, not the arbitrary
off-image value of the interval-restricted reference inverse. Their
differentiation recurrence is proved before they enter any error estimate.
-/

noncomputable section

open Set Expdb Filter
open scoped ContDiff Topology

namespace TaoTrudgianYang2025

theorem reciprocalModel_hasDerivAt_inverse_curvature
    {σ v : ℝ} (hσ : 0 < σ) (hv : 0 < v) :
    HasDerivAt (fun w : ℝ => w^(-σ⁻¹))
      (deriv (deriv (referenceModelPrimitive σ)) (v^(-σ⁻¹)))⁻¹ v := by
  have hu : 0 < v^(-σ⁻¹) := Real.rpow_pos_of_pos hv _
  have hf := ((referenceModelPrimitive_contDiffAt σ hu).derivWithin
    (m := ∞) (by simp)).differentiableAt (by simp : (∞ : WithTop ℕ∞) ≠ 0)
  have hp := Real.hasDerivAt_rpow_const (p := -σ⁻¹) (Or.inl hv.ne')
  have hc := hf.hasDerivAt.comp v hp
  have he : (fun w : ℝ => deriv (referenceModelPrimitive σ) (w^(-σ⁻¹))) =ᶠ[𝓝 v] id := by
    filter_upwards [isOpen_Ioi.mem_nhds hv] with w hw
    rw [(referenceModelPrimitive_hasDerivAt σ (Real.rpow_pos_of_pos hw _)).deriv,
      reciprocal_modelPhase_identity hσ hw.le]
    rfl
  have hprod : deriv (deriv (referenceModelPrimitive σ)) (v^(-σ⁻¹))*
      ((-σ⁻¹)*v^(-σ⁻¹-1)) = 1 :=
    hc.unique ((hasDerivAt_id v).congr_of_eventuallyEq he)
  have hne : deriv (deriv (referenceModelPrimitive σ)) (v^(-σ⁻¹)) ≠ 0 := by
    intro h
    rw [h,zero_mul] at hprod
    norm_num at hprod
  have hcoef : (-σ⁻¹)*v^(-σ⁻¹-1) =
      (deriv (deriv (referenceModelPrimitive σ)) (v^(-σ⁻¹)))⁻¹ := by
    apply (mul_left_cancel₀ hne)
    rw [mul_inv_cancel₀ hne]
    exact hprod
  rwa [hcoef] at hp

theorem referenceModelPrimitive_secondDeriv_reciprocal_ne_zero
    {σ v : ℝ} (hσ : 0 < σ) (hv : 0 < v) :
    deriv (deriv (referenceModelPrimitive σ)) (v^(-σ⁻¹)) ≠ 0 := by
  have hi := reciprocalModel_hasDerivAt_inverse_curvature hσ hv
  have hp := Real.hasDerivAt_rpow_const (p := -σ⁻¹) (Or.inl hv.ne')
  have he := hi.unique hp
  intro hz
  rw [hz,inv_zero] at he
  have hn : (-σ⁻¹)*v^(-σ⁻¹-1) ≠ 0 :=
    mul_ne_zero (neg_ne_zero.mpr (inv_ne_zero hσ.ne')) (Real.rpow_pos_of_pos hv _).ne'
  exact hn he.symm

def expandedReferenceInverseJet (σ v : ℝ) : ℕ → ℝ
  | 0 => v^(-σ⁻¹)
  | 1 => (deriv (deriv (referenceModelPrimitive σ)) (v^(-σ⁻¹)))⁻¹
  | n+2 => iteratedDeriv (n+2) (referenceModelPrimitive σ) (v^(-σ⁻¹))

theorem expandedReferenceInverseJet_hasDerivAt
    {σ v : ℝ} (hσ : 0 < σ) (hv : 0 < v) (j : ℕ) :
    HasDerivAt (fun w => expandedReferenceInverseJet σ w j)
      (inversePhaseEval (inversePhaseAtomDerivative j) (expandedReferenceInverseJet σ v)) v := by
  have hi := reciprocalModel_hasDerivAt_inverse_curvature hσ hv
  have hu : 0 < v^(-σ⁻¹) := Real.rpow_pos_of_pos hv _
  match j with
  | 0 => exact hi
  | 1 =>
      have hc : DifferentiableAt ℝ (iteratedDeriv 2 (referenceModelPrimitive σ)) (v^(-σ⁻¹)) :=
        (contDiffAt_iteratedDeriv_infty
        (referenceModelPrimitive_contDiffAt σ hu) 2).differentiableAt
          (by simp : (∞ : WithTop ℕ∞) ≠ 0)
      have hne : iteratedDeriv 2 (referenceModelPrimitive σ) (v^(-σ⁻¹)) ≠ 0 := by
        simpa only [iteratedDeriv_succ,iteratedDeriv_zero] using
          referenceModelPrimitive_secondDeriv_reciprocal_ne_zero hσ hv
      have hcomp : HasDerivAt
          (fun w : ℝ => iteratedDeriv 2 (referenceModelPrimitive σ) (w^(-σ⁻¹)))
          (deriv (iteratedDeriv 2 (referenceModelPrimitive σ)) (v^(-σ⁻¹))*
            (deriv (deriv (referenceModelPrimitive σ)) (v^(-σ⁻¹)))⁻¹) v :=
        HasDerivAt.comp v (h₂ := iteratedDeriv 2 (referenceModelPrimitive σ))
          hc.hasDerivAt hi
      have hh := hcomp.inv hne
      convert hh using 1
      · funext w
        simp only [expandedReferenceInverseJet,Pi.inv_apply,
          iteratedDeriv_succ,iteratedDeriv_zero]
      · simp only [inversePhaseEval,inversePhaseAtomDerivative,expandedReferenceInverseJet,
          iteratedDeriv_succ,iteratedDeriv_zero,div_eq_mul_inv]
        ring
  | n+2 =>
      have hc : DifferentiableAt ℝ (iteratedDeriv (n+2) (referenceModelPrimitive σ)) (v^(-σ⁻¹)) :=
        (contDiffAt_iteratedDeriv_infty
        (referenceModelPrimitive_contDiffAt σ hu) (n+2)).differentiableAt
          (by simp : (∞ : WithTop ℕ∞) ≠ 0)
      convert hc.hasDerivAt.comp v hi using 1
      simp only [inversePhaseEval,inversePhaseAtomDerivative,expandedReferenceInverseJet,
        iteratedDeriv_succ]

theorem inversePhaseEval_expandedReferenceInverseJet_hasDerivAt
    {σ v : ℝ} (hσ : 0 < σ) (hv : 0 < v) (e : InversePhaseExpression) :
    HasDerivAt (fun w => inversePhaseEval e (expandedReferenceInverseJet σ w))
      (inversePhaseEval (inversePhaseDifferentiate e) (expandedReferenceInverseJet σ v)) v := by
  induction e with
  | scalar c => exact hasDerivAt_const v c
  | atom j => exact expandedReferenceInverseJet_hasDerivAt hσ hv j
  | add e f he hf => exact he.add hf
  | mul e f he hf => exact he.mul hf

theorem iteratedDeriv_modelPhase_expanded_inverseJet_formula
    {σ v : ℝ} (hσ : 0 < σ) (hv : 0 < v) (n : ℕ) :
    iteratedDeriv n (modelPhase σ⁻¹) v =
      inversePhaseEval (inversePhaseDerivativeExpression n) (expandedReferenceInverseJet σ v) := by
  induction n generalizing v with
  | zero => rfl
  | succ n ih =>
      rw [iteratedDeriv_succ]
      have he : iteratedDeriv n (modelPhase σ⁻¹) =ᶠ[𝓝 v]
          (fun w => inversePhaseEval (inversePhaseDerivativeExpression n)
            (expandedReferenceInverseJet σ w)) := by
        filter_upwards [isOpen_Ioi.mem_nhds hv] with w hw
        exact ih hw
      rw [he.deriv_eq,
        (inversePhaseEval_expandedReferenceInverseJet_hasDerivAt hσ hv
          (inversePhaseDerivativeExpression n)).deriv]
      rfl

end TaoTrudgianYang2025
