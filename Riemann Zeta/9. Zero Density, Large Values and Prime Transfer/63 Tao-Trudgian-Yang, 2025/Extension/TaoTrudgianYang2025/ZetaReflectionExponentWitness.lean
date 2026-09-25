import TaoTrudgianYang2025.ZetaReflectionMassLimits
import TaoTrudgianYang2025.ZetaReflectionCounterexampleFamilies

/-! Failure of a source bound yields an actual reflected exponent witness. -/

noncomputable section
open Complex Filter MeasureTheory Set Topology
namespace TaoTrudgianYang2025

theorem exists_reflection_exponent_witness {σ τ B : ℝ}
    (hσ : 1/2 ≤ σ) (hτ : 1 < τ) (hnot : ¬ IsZetaLargeValueBound σ τ B) :
    ∃ η : ℝ, 0 < η ∧ ∃ v ∈ Icc (σ+τ/2-1) (τ-1),
      (((B+η+(σ+τ/2-1)-v)/(τ-1) : ℝ) : EReal) ≤
        zetaLargeValueExponent (v/(τ-1)) (τ/(τ-1)) := by
  obtain ⟨η,hη,err,_he,he0,P,Q,hNtop,hTlog,hVlog,hdata⟩ :=
    exists_reflection_counterexample_families hσ hτ hnot
  have hs := fun n => (hdata n).2.2.1
  have ht := fun n => (hdata n).2.2.2.1
  have hne := fun n => (hdata n).2.1
  have hval := fun n => (hdata n).2.2.2.2.1
  have hscale := reflection_tendsto_log_scale P Q hNtop hTlog hs
  have hQtop := reflection_tendsto_target_scale P Q hτ hNtop hTlog hs
  have hQT := reflection_tendsto_target_height_exponent P Q hτ hNtop hTlog hs ht
  obtain ⟨v,hv,φ,hφ,hlim⟩ := exists_reflection_amplitude_subsequence P Q err
    hNtop he0 hTlog hVlog hscale hne hval
  have hφtop := hφ.tendsto_atTop
  have hscale' : Tendsto (fun n => Real.logb (P (φ n)).N (Q (φ n)).N)
      atTop (nhds (τ-1)) := hscale.comp hφtop
  have hQvalue : Tendsto (fun n => Real.logb (Q (φ n)).N (Q (φ n)).V)
      atTop (nhds (v/(τ-1))) :=
    tendsto_logb_rebase _ _ _ v (τ-1) (sub_pos.mpr hτ).ne'
      (fun n => (P (φ n)).one_lt_N) hscale' hlim
  have hfloor := (reflection_tendsto_log_value_floor P err he0 hTlog hVlog).comp hφtop
  refine ⟨η,hη,v,hv,?_⟩
  exact reflection_mass_le_zeta_exponent (fun n => P (φ n)) (fun n => Q (φ n))
    (fun n => err (φ n)) (sub_pos.mpr hτ) (hQtop.comp hφtop) (hQT.comp hφtop)
    hQvalue (fun n => hne (φ n)) hscale' hlim hfloor
    (fun n => (hdata (φ n)).1) (fun n => (hdata (φ n)).2.2.2.2.2)

end TaoTrudgianYang2025
