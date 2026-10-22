import Dubon2026.SourceOriginalMeromorphicPoleNeighborhoods

/-! DUB-17/18 -> original Abel-Jacobi -> meromorphic loop-period generation.
Subtract the actual simple-pole residue term in each marked original cell.
The original coefficient expansion makes the remainder analytic on a common
open neighborhood; the already proved radial primitive theorem integrates it.
Adapted from S_AlgebraicCurve_CellDissection_exists_int_pathIntegral_eq_sum_periods_add_sum_residues,
anthropics/fermats-last-theorem, Apache-2.0,
commit 6e837e75355538c7f80bab5b956861e86c4eacc2.
All original coordinate, simple-pole and primitive calculus is reused.
-/
namespace Dubon2026.SourceFunctionField.CellGeometry.MeromorphicPeriods
noncomputable section
open SourceCurve Set Filter KaehlerDifferential
open scoped Topology Manifold
attribute [local instance] OriginalChart.placeTopology OriginalChart.placeChartedSpace
variable {N : ℕ} [NeZero N] {R : Type*}
local notation "F" => modularFunctionFieldOver N ℂ

variable {𝒟 : CellDissection N} (S : Finset (Place ℂ F)) (θ : R → Ω[F⁄ℂ])

/-- The coefficient after removing its residue term, filled in by its removable limit. -/
noncomputable def regCoeff {𝒟 : CellDissection N} (S : Finset (Place ℂ F))
    (θ : R → Ω[F⁄ℂ]) (r : R) (C : 𝒟.ιC) (w : ℂ) : ℂ :=
  if w = (𝒟.cell C).R.q then
    limUnder (𝓝[≠] (𝒟.cell C).R.q)
      (fun w => coeffIn (𝒟.cell C).ζ (θ r) w - ρ 𝒟 S θ C r / (w - (𝒟.cell C).R.q))
  else coeffIn (𝒟.cell C).ζ (θ r) w - ρ 𝒟 S θ C r / (w - (𝒟.cell C).R.q)

theorem regCoeff_of_ne {𝒟 : CellDissection N} (S : Finset (Place ℂ F))
    (θ : R → Ω[F⁄ℂ]) {r : R} {C : 𝒟.ιC} {w : ℂ} (hw : w ≠ (𝒟.cell C).R.q) :
    regCoeff S θ r C w = coeffIn (𝒟.cell C).ζ (θ r) w - ρ 𝒟 S θ C r / (w - (𝒟.cell C).R.q) := by
  simp [regCoeff, hw]

theorem analyticAt_regCoeff {𝒟 : CellDissection N} (S : Finset (Place ℂ F))
    (θ : R → Ω[F⁄ℂ])
    (hθ : ∀ r v, -1 ≤ v.ordDifferential (θ r) ∧ (v ∉ S → 0 ≤ v.ordDifferential (θ r)))
    (hS : PolePos 𝒟 S) (r : R) (C : 𝒟.ιC) {w : ℂ}
    (hw : w ∈ goodSet (S := S) C) : AnalyticAt ℂ (regCoeff S θ r C) w := by
  set q := (𝒟.cell C).R.q with hq

  have hraw : ∀ w ∈ goodSet (S := S) C, w ≠ q →
      AnalyticAt ℂ (fun w => coeffIn (𝒟.cell C).ζ (θ r) w - ρ 𝒟 S θ C r / (w - q)) w := by
    intro w hw hwq
    have hreg : 0 ≤ ((𝒟.cell C).ζ.symm w).ordDifferential (θ r) := by
      refine (hθ r _).2 fun hwS => hwq ?_
      exact (goodSet_pole hS hw hwS).2
    refine ((𝒟.cell C).toAnalyticCoord.analyticAt_coeff (θ r) hw.1 (((𝒟.cell C).ζ.symm _).mem_of_ord_nonneg hreg)).sub ?_
    exact analyticAt_const.div (analyticAt_id.sub analyticAt_const) (sub_ne_zero.2 hwq)
  by_cases hwq : w = q
  ·
    subst hwq
    by_cases hpole : ∃ v ∈ S, v ∈ (𝒟.cell C).interior'
    · obtain ⟨v, hv, hvC⟩ := hpole
      have hvq : (𝒟.cell C).ζ v = q := (hS.center hv (Cell.interior_subset_carrier _ hvC)).2
      have hvs : v ∈ (𝒟.cell C).ζ.source := by
        obtain ⟨z, hz, rfl⟩ := Cell.interior_subset_carrier _ hvC
        exact (𝒟.cell C).ζ.map_target ((𝒟.cell C).hKt hz)
      obtain ⟨G, hGa, hG⟩ := (𝒟.cell C).toAnalyticCoord.coeff_simple_pole hvs (θ r) ((hθ r v).1)
      rw [hvq] at hGa hG
      have hρ : ρ 𝒟 S θ C r = res v (θ r) := by rw [ρ_eq_of_mem θ hS hv hvC]

      have hpunct : ∀ᶠ w in 𝓝[≠] q, regCoeff S θ r C w = G w := by
        filter_upwards [hG, self_mem_nhdsWithin] with w hw hwq
        rw [regCoeff_of_ne S θ hwq, hw, hρ, res]
        ring

      have hlim : regCoeff S θ r C q = G q := by
        have h1 : regCoeff S θ r C q = limUnder (𝓝[≠] q)
            (fun w => coeffIn (𝒟.cell C).ζ (θ r) w - ρ 𝒟 S θ C r / (w - q)) := by
          simp [regCoeff, hq]
        rw [h1]
        refine Filter.Tendsto.limUnder_eq ?_
        have hGc : Tendsto G (𝓝[≠] q) (𝓝 (G q)) := hGa.continuousAt.tendsto.mono_left
          nhdsWithin_le_nhds
        refine hGc.congr' ?_
        filter_upwards [hG, self_mem_nhdsWithin] with w hw hwq
        rw [hw, hρ, res]; ring
      have heq : regCoeff S θ r C =ᶠ[𝓝 q] G := by
        rw [eventually_nhdsWithin_iff] at hpunct
        filter_upwards [hpunct] with w hw
        by_cases h : w = q
        · rw [h, hlim]
        · exact hw h
      exact hGa.congr heq.symm
    ·
      have hpole' : ∀ v ∈ S, v ∉ (𝒟.cell C).interior' :=
        fun v hv hvC => hpole ⟨v, hv, hvC⟩
      have hρ : ρ 𝒟 S θ C = 0 := ρ_eq_zero θ hpole'
      have hreg : 0 ≤ ((𝒟.cell C).ζ.symm q).ordDifferential (θ r) := by
        refine (hθ r _).2 fun hS' => hpole' _ hS' (goodSet_pole hS hw hS').1
      have hca := (𝒟.cell C).toAnalyticCoord.analyticAt_coeff (θ r) hw.1 (((𝒟.cell C).ζ.symm _).mem_of_ord_nonneg hreg)
      have heq : regCoeff S θ r C =ᶠ[𝓝 q] coeffIn (𝒟.cell C).ζ (θ r) := by
        have hpunct : ∀ᶠ w in 𝓝[≠] q, regCoeff S θ r C w = coeffIn (𝒟.cell C).ζ (θ r) w := by
          filter_upwards [self_mem_nhdsWithin] with w hwq
          rw [regCoeff_of_ne S θ hwq]; simp [hρ]
        have hlim : regCoeff S θ r C q = coeffIn (𝒟.cell C).ζ (θ r) q := by
          have h1 : regCoeff S θ r C q = limUnder (𝓝[≠] q)
              (fun w => coeffIn (𝒟.cell C).ζ (θ r) w - ρ 𝒟 S θ C r / (w - q)) := by
            simp [regCoeff, hq]
          rw [h1]
          refine Filter.Tendsto.limUnder_eq ?_
          refine (hca.continuousAt.tendsto.mono_left nhdsWithin_le_nhds).congr' ?_
          filter_upwards [self_mem_nhdsWithin] with w hwq
          simp [hρ]
        rw [eventually_nhdsWithin_iff] at hpunct
        filter_upwards [hpunct] with w hw
        by_cases h : w = q
        · rw [h, hlim]
        · exact hw h
      exact hca.congr heq.symm
  · have heq : regCoeff S θ r C =ᶠ[𝓝 w]
        fun w => coeffIn (𝒟.cell C).ζ (θ r) w - ρ 𝒟 S θ C r / (w - q) := by
      filter_upwards [isOpen_ne.mem_nhds hwq] with u hu
      exact regCoeff_of_ne S θ hu
    exact (hraw w hw hwq).congr heq.symm


end
end Dubon2026.SourceFunctionField.CellGeometry.MeromorphicPeriods
