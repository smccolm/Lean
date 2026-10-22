import Dubon2026.SourceMeromorphicLocalLog
import Dubon2026.SourceOriginalMeromorphicCellPrimitives
import Dubon2026.SourceOriginalSimplePoleSpaceFinite

/-! DUB-17/18 -> original Abel-Jacobi -> meromorphic loop-period generation.
Restore a local logarithmic term to the analytic residue-subtracted primitive.
The existing zero-residue regularity theorem handles cancellation at the cell
center. Native logarithm differentiation then gives the original coefficient
on a constructed open neighborhood of every allowed center point.
Adapted from S_AlgebraicCurve_CellDissection_exists_int_pathIntegral_eq_sum_periods_add_sum_residues,
anthropics/fermats-last-theorem, Apache-2.0,
commit 6e837e75355538c7f80bab5b956861e86c4eacc2.
-/
namespace Dubon2026.SourceFunctionField.CellGeometry.MeromorphicPeriods
noncomputable section
open SourceCurve Set Filter Complex Metric KaehlerDifferential
open scoped Real Topology Manifold
attribute [local instance] OriginalChart.placeTopology OriginalChart.placeChartedSpace
variable {N : ℕ} [NeZero N] {R : Type*}
local notation "F" => modularFunctionFieldOver N ℂ

theorem regCoeff_eq_coeff {𝒟 : CellDissection N} (S : Finset (Place ℂ F)) (θ : R → Ω[F⁄ℂ])
    (hθ : ∀ r v, -1 ≤ v.ordDifferential (θ r) ∧ (v ∉ S → 0 ≤ v.ordDifferential (θ r)))
    (hS : PolePos 𝒟 S) {r : R} {D : 𝒟.ιC} (hρ : ρ 𝒟 S θ D r = 0)
    {w : ℂ} (hw : w ∈ goodSet (S := S) D) :
    regCoeff S θ r D w = coeffIn (𝒟.cell D).ζ (θ r) w := by
  by_cases hwq : w = (𝒟.cell D).R.q
  · subst hwq

    have hreg : 0 ≤ ((𝒟.cell D).ζ.symm (𝒟.cell D).R.q).ordDifferential (θ r) := by
      by_cases hqS : (𝒟.cell D).ζ.symm (𝒟.cell D).R.q ∈ S
      · have hint := (goodSet_pole hS hw hqS).1
        have hρ' := congrFun (ρ_eq_of_mem θ hS hqS hint) r
        rw [hρ] at hρ'
        apply original_simple_pole_regular_of_residue_zero N _ _ ((hθ r _).1)
        rw [originalDifferentialResidue_simplePole N _ _ ((hθ r _).1)]
        exact hρ'.symm
      · exact (hθ r _).2 hqS
    have hca := (𝒟.cell D).toAnalyticCoord.analyticAt_coeff (θ r) hw.1
      (((𝒟.cell D).ζ.symm _).mem_of_ord_nonneg hreg)
    have h1 : regCoeff S θ r D (𝒟.cell D).R.q = limUnder (𝓝[≠] (𝒟.cell D).R.q)
        (fun w => coeffIn (𝒟.cell D).ζ (θ r) w - ρ 𝒟 S θ D r / (w - (𝒟.cell D).R.q)) := by
      simp [regCoeff]
    rw [h1]
    refine Filter.Tendsto.limUnder_eq ?_
    refine (hca.continuousAt.tendsto.mono_left nhdsWithin_le_nhds).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with u hu
    simp [hρ]
  · rw [regCoeff_of_ne S θ hwq, hρ, zero_div, sub_zero]


theorem exists_logPrimitive {𝒟 : CellDissection N} (S : Finset (Place ℂ F)) (θ : R → Ω[F⁄ℂ])
    (hθ : ∀ r v, -1 ≤ v.ordDifferential (θ r) ∧ (v ∉ S → 0 ≤ v.ordDifferential (θ r)))
    (hS : PolePos 𝒟 S) {V : 𝒟.ιC → Set ℂ} {Ψ : R → 𝒟.ιC → ℂ → ℂ}
    (hP : RegPrimData S θ V Ψ) (r : R) (D : 𝒟.ιC) {c : ℂ} (hc : c ∈ V D)
    (hcq : ρ 𝒟 S θ D r ≠ 0 → c ≠ (𝒟.cell D).R.q) :
    ∃ W : Set ℂ, IsOpen W ∧ c ∈ W ∧ ∀ w ∈ W,
      HasDerivAt (fun w => Ψ r D w + ρ 𝒟 S θ D r * Lg (𝒟.cell D).R.q c w)
        (coeffIn (𝒟.cell D).ζ (θ r) w) w := by
  set q := (𝒟.cell D).R.q with hq
  by_cases hρ : ρ 𝒟 S θ D r = 0
  · refine ⟨V D, hP.hVo D, hc, fun w hw => ?_⟩
    have h1 := hP.hΨ r D w hw
    rw [regCoeff_eq_coeff S θ hθ hS hρ (hP.hVgood D hw)] at h1
    have : (fun w => Ψ r D w + ρ 𝒟 S θ D r * Lg q c w) = fun w => Ψ r D w + 0 := by
      funext w; rw [hρ, zero_mul]
    rw [this]
    exact h1.add_const 0
  · have hcq' : c ≠ q := hcq hρ
    refine ⟨V D ∩ ball c ‖c - q‖, (hP.hVo D).inter isOpen_ball, ⟨hc, ?_⟩, fun w hw => ?_⟩
    · exact mem_ball_self (norm_pos_iff.2 (sub_ne_zero.2 hcq'))
    · have hwq : w ≠ q := by
        intro h
        have := hw.2
        rw [h, mem_ball, dist_comm, dist_eq_norm] at this
        exact lt_irrefl _ this
      have h1 := hP.hΨ r D w hw.1
      rw [regCoeff_of_ne S θ hwq] at h1
      have h2 := (hasDerivAt_Lg (q := q) hw.2).const_mul (ρ 𝒟 S θ D r)
      convert h1.add h2 using 1
      rw [← hq]
      field_simp
      ring

end
end Dubon2026.SourceFunctionField.CellGeometry.MeromorphicPeriods
