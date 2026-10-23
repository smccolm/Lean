import Dubon2026.SourceOriginalFiniteCuspClassLocal
import Dubon2026.SourceOriginalPathPrimitives

/-! DUB-17/18 -> original Picard-period Hecke comparison -> reverse
period-lattice inclusion. Along every actual path avoiding the poles of
j, local original primitives and the descended modular primitive class
have the same increments. Their difference is locally constant on the
connected parameter interval. In particular every such loop has its
actual period in the modular period lattice.
-/
namespace Dubon2026.SourceFunctionField.OriginalChart
noncomputable section
open UpperHalfPlane SourceCurve Filter KaehlerDifferential
open scoped Topology
variable (N : ℕ) [NeZero N]
attribute [local instance] placeTopology

theorem original_finite_path_integral_modular_class {n : ℕ}
    (b : Fin n → regularDifferentials ℂ (modularFunctionFieldOver N ℂ))
    {P Q : Place ℂ (modularFunctionFieldOver N ℂ)} (γ : Path P Q)
    (hγ : ∀ t, jOver N ℂ ∈ (γ t).toValuationSubring) :
    (originalCuspPeriodLattice N b).mkQ (fun i => pathIntegral N (b i).val γ) =
      originalFiniteCuspClass N b ⟨γ 1, hγ 1⟩ - originalFiniteCuspClass N b ⟨γ 0, hγ 0⟩ := by
  choose g hg using fun i => exists_isPrimitiveAlong N (b i).val (b i).property γ
  let L := originalCuspPeriodLattice N b
  let C := fun t : unitInterval => originalFiniteCuspClass N b ⟨γ t, hγ t⟩
  have hlc : IsLocallyConstant (fun t : unitInterval => L.mkQ (fun i => g i t) - C t) := by
    apply (IsLocallyConstant.iff_eventually_eq _).mpr
    intro s
    obtain ⟨τ, hτ⟩ := exists_original_analytic_place_eq N (γ s) (hγ s)
    choose Φ hΦ hgp using fun i => hg i s
    have hΦ₀ : ∀ i, ∀ᶠ u in 𝓝 (0 : ℂ),
        HasDerivAt (Φ i) (readDifferential N (originalAnalyticPlace N τ) (b i).val u) u := by
      intro i
      rw [hτ]
      simpa only [placeChart_self] using hΦ i
    let k := fun t : unitInterval => placeChart N (γ s) (γ t)
    have hk : Tendsto k (𝓝 s) (𝓝 (0 : ℂ)) := by
      have hc := (continuousAt_placeChart N (γ s) (γ s) (mem_placeChart_source N (γ s))).comp
        γ.continuous.continuousAt
      simpa only [Function.comp_apply, placeChart_self] using hc.tendsto
    have hc := hk.eventually (originalFiniteCuspClass_chart_primitive N b τ Φ hΦ₀)
    have hs := γ.continuous.continuousAt.eventually (placeChart_source_mem_nhds N (γ s))
    filter_upwards [hc, hs, Filter.eventually_all.mpr hgp] with t hct hts hgt
    have hfamily : placeFamily N (originalAnalyticPlace N τ) (k t) = γ t := by
      rw [hτ]
      exact (placeChart N (γ s)).left_inv hts
    have hmem : jOver N ℂ ∈ (placeFamily N (originalAnalyticPlace N τ) (k t)).toValuationSubring :=
      hfamily.symm ▸ hγ t
    have hC := hct hmem
    have hcenter := originalFiniteCuspClass_apply N b ⟨γ s, hγ s⟩ τ hτ
    rw [← hcenter] at hC
    have harg : (⟨placeFamily N (originalAnalyticPlace N τ) (k t), hmem⟩ :
        {v : Place ℂ (modularFunctionFieldOver N ℂ) // jOver N ℂ ∈ v.toValuationSubring}) =
        ⟨γ t, hγ t⟩ := Subtype.ext hfamily
    rw [harg] at hC
    have hv : (fun i => g i t) - (fun i => g i s) = fun i => Φ i (k t) - Φ i 0 := by
      funext i
      have hi := (hgp i).self_of_nhds
      rw [placeChart_self] at hi
      exact congrArg₂ (· - ·) (hgt i) hi
    change C t - C s = L.mkQ (fun i => Φ i (k t) - Φ i 0) at hC
    rw [← hv, map_sub] at hC
    change L.mkQ (fun i => g i t) - C t = L.mkQ (fun i => g i s) - C s
    apply sub_eq_sub_iff_sub_eq_sub.mpr
    exact hC.symm
  have he := hlc.apply_eq_of_preconnectedSpace 1 0
  have hv : (fun i => pathIntegral N (b i).val γ) = (fun i => g i 1) - (fun i => g i 0) := by
    funext i
    exact pathIntegral_eq_of_isPrimitiveAlong N (hg i)
  rw [hv, map_sub]
  exact sub_eq_sub_iff_sub_eq_sub.mp he

theorem original_finite_loop_period_mem_cusp_lattice {n : ℕ}
    (b : Fin n → regularDifferentials ℂ (modularFunctionFieldOver N ℂ))
    {P : Place ℂ (modularFunctionFieldOver N ℂ)} (γ : Path P P)
    (hγ : ∀ t, jOver N ℂ ∈ (γ t).toValuationSubring) :
    (fun i => pathIntegral N (b i).val γ) ∈ originalCuspPeriodLattice N b := by
  apply (Submodule.Quotient.mk_eq_zero (originalCuspPeriodLattice N b)).mp
  have he := original_finite_path_integral_modular_class N b γ hγ
  have hv : (⟨γ 1, hγ 1⟩ :
      {v : Place ℂ (modularFunctionFieldOver N ℂ) // jOver N ℂ ∈ v.toValuationSubring}) =
      ⟨γ 0, hγ 0⟩ := Subtype.ext (γ.target.trans γ.source.symm)
  rw [hv, sub_self] at he
  exact he

end
end Dubon2026.SourceFunctionField.OriginalChart
