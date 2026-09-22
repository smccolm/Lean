import TaoTrudgianYang2025.ExponentPairShiftPhase
import Mathlib.Topology.Order.OrderClosed

/-!
# Reference-jet and endpoint bridges for compressed differences

The reference parameter increases from sigma to sigma+1 after a
normalized negative difference. Interior estimates extend to the actual
closed model interval by continuity of within derivatives.
-/

noncomputable section

open Set Expdb Filter
open scoped ContDiff Topology

namespace TaoTrudgianYang2025

theorem modelPhase_iteratedDeriv_succ_parameter (σ : ℝ) {u : ℝ}
    (hu : 0 < u) (p : ℕ) :
    iteratedDeriv (p+1) (modelPhase σ) u =
      -σ*iteratedDeriv p (modelPhase (σ+1)) u := by
  have he : deriv (modelPhase σ) =ᶠ[𝓝 u] fun x => -σ*modelPhase (σ+1) x := by
    filter_upwards [isOpen_Ioi.mem_nhds hu] with x hx
    have hd := (Real.hasDerivAt_rpow_const (Or.inl hx.ne') (p := -σ)).deriv
    simpa only [modelPhase,show -σ-1 = -(σ+1) by ring] using hd
  rw [iteratedDeriv_succ',he.iteratedDeriv_eq p,iteratedDeriv_const_mul_field]

theorem approximateModelPhase_of_interior_bounds
    {F : ℝ → ℝ} {σ ε : ℝ} {P : ℕ}
    (hF : ContDiffOn ℝ ∞ F phaseInterval)
    (hb : ∀ u ∈ Ioo (1 : ℝ) 2, ∀ p ≤ P,
      |iteratedDeriv (p+1) F u-iteratedDeriv p (modelPhase σ) u| ≤ ε) :
    IsApproximateModelPhaseFunction F σ P ε := by
  refine ⟨hF,?_⟩
  intro p hp u
  have hc : ContinuousOn (fun x =>
      ‖iteratedDerivWithin (p+1) F phaseInterval x-
        iteratedDerivWithin p (modelPhase σ) phaseInterval x‖) phaseInterval :=
    ((hF.continuousOn_iteratedDerivWithin
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl (p+1)) uniqueDiffOn_phaseInterval).sub
      (continuousOn_iteratedDerivWithin_modelPhase σ p)).norm
  have hi : ∀ x ∈ Ioo (1 : ℝ) 2,
      ‖iteratedDerivWithin (p+1) F phaseInterval x-
        iteratedDerivWithin p (modelPhase σ) phaseInterval x‖ ≤ ε := by
    intro x hx
    have hxI : x ∈ phaseInterval := ⟨hx.1.le,hx.2.le⟩
    have hxN : phaseInterval ∈ 𝓝 x :=
      mem_of_superset (isOpen_Ioo.mem_nhds hx) Ioo_subset_Icc_self
    have hf : ContDiffAt ℝ (p+1) F x :=
      (hF x hxI).contDiffAt hxN |>.of_le
        (ENat.natCast_le_of_coe_top_le_withTop le_rfl (p+1))
    have hm : ContDiffAt ℝ p (modelPhase σ) x :=
      Real.contDiffAt_rpow_const_of_ne (zero_lt_one.trans hx.1).ne'
    rw [iteratedDerivWithin_eq_iteratedDeriv uniqueDiffOn_phaseInterval hf hxI,
      iteratedDerivWithin_eq_iteratedDeriv uniqueDiffOn_phaseInterval hm hxI,Real.norm_eq_abs]
    exact hb x hx p hp
  have hcl : closure (Ioo (1 : ℝ) 2) = phaseInterval := by
    rw [closure_Ioo (by norm_num : (1 : ℝ) ≠ 2)]
    rfl
  exact le_on_closure hi (by simpa only [hcl] using hc) continuousOn_const
    (by simpa only [hcl] using u.property)

theorem aProcessShiftPhase_iteratedDeriv
    {F : ℝ → ℝ} {η u : ℝ}
    (hF : ContDiffOn ℝ ∞ F phaseInterval) (hη : 0 ≤ η) (hη₁ : η < 1)
    (hu : u ∈ Ioo (1 : ℝ) 2) (σ : ℝ) (n : ℕ) :
    iteratedDeriv n (aProcessShiftPhase F σ η) u =
      (1-η)^n/(σ*η) *
        (iteratedDeriv n F (aProcessShiftPoint η 0 u)-
         iteratedDeriv n F (aProcessShiftPoint η 1 u)) := by
  have hi (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      aProcessShiftPoint η t u ∈ Ioo (1 : ℝ) 2 :=
    aProcessShiftPoint_mem_Ioo hη hη₁ ht hu
  have hc (G : ℝ → ℝ) (hG : ContDiffOn ℝ ∞ G phaseInterval)
      (x : ℝ) (hx : x ∈ Ioo (1 : ℝ) 2) :
      iteratedDerivWithin n G phaseInterval x = iteratedDeriv n G x := by
    apply iteratedDerivWithin_eq_iteratedDeriv uniqueDiffOn_phaseInterval
    · exact ((hG x ⟨hx.1.le,hx.2.le⟩).contDiffAt
        (mem_of_superset (isOpen_Ioo.mem_nhds hx) Ioo_subset_Icc_self)).of_le
          (ENat.natCast_le_of_coe_top_le_withTop le_rfl n)
    · exact ⟨hx.1.le,hx.2.le⟩
  have h := aProcessShiftPhase_iteratedDerivWithin hF hη hη₁.le
    (u := u) ⟨hu.1.le,hu.2.le⟩ σ n
  rw [hc _ (aProcessShiftPhase_contDiffOn hF hη hη₁.le σ) _ hu,
    hc _ hF _ (hi 0 (by norm_num)),hc _ hF _ (hi 1 (by norm_num))] at h
  exact h

end TaoTrudgianYang2025
