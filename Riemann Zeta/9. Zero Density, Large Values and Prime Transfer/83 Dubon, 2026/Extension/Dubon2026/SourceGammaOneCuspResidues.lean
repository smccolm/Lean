import Dubon2026.SourceGammaOneCuspPlaces
import Dubon2026.SourceGammaOneAnalyticResidues

/-! DUB-17/18 -> original all-weight arithmetic association -> actual
Gamma1 Picard/period comparison -> cusp-order control. Reuse the proved
translated cusp germs, their normalized place orders, and actual rational
residue evaluation. Regular cusp germs converge to the actual residue;
nonzero cusp limits force normalized order zero. Exhaustion of every
j-pole place by these cusps remains a separate obligation. -/
namespace Dubon2026.SourceFunctionField.GammaOne
noncomputable section
open UpperHalfPlane Filter SourceCurve
open scoped MatrixGroups Topology
variable {Γ : Subgroup SL(2, ℤ)}
  (N : ℕ) [NeZero N] (hΓ : CongruenceSubgroup.Gamma N ≤ Γ)
  (hT : ModularGroup.T ∈ Γ)

include hΓ hT

theorem cuspPlace_mem_iff (γ : SL(2, ℤ)) (f : functionFieldOver Γ ℂ) :
    f ∈ (cuspPlace N hΓ hT γ).toValuationSubring ↔ 0 ≤ cuspOrder Γ N γ f :=
  (exists_cusp_place N hΓ hT γ).choose_spec.choose_spec.2.1 f

theorem cuspRealize_sub_constant_eventuallyEq
    (f : functionFieldOver Γ ℂ) (c : ℂ) (γ : SL(2, ℤ)) :
    cuspRealize Γ N γ ((f - algebraMap ℂ (functionFieldOver Γ ℂ) c :
      functionFieldOver Γ ℂ) : LaurentSeries ℂ) =ᶠ[𝓝[≠] (0 : ℂ)]
      fun q => cuspRealize Γ N γ (f : LaurentSeries ℂ) q - c := by
  have he : f - algebraMap ℂ (functionFieldOver Γ ℂ) c =
      f + algebraMap ℂ (functionFieldOver Γ ℂ) (-c) := by
    rw [map_neg, sub_eq_add_neg]
  rw [he]
  filter_upwards [cuspRealize_add_eventuallyEq N hΓ hT f
    (algebraMap ℂ (functionFieldOver Γ ℂ) (-c)) γ,
    cuspRealize_const_eventuallyEq N hT γ (-c)] with q hq hc
  have hconst : cuspRealize Γ N γ
      ((algebraMap ℂ (functionFieldOver Γ ℂ) (-c) : functionFieldOver Γ ℂ) :
        LaurentSeries ℂ) q = -c := hc
  simpa only [Pi.add_apply, hconst, sub_eq_add_neg] using hq

theorem cuspPlace_order_eq_zero_of_tendsto
    (γ : SL(2, ℤ)) (f : functionFieldOver Γ ℂ) (hf : f ≠ 0)
    {c : ℂ} (hc : c ≠ 0)
    (hlim : Tendsto (cuspRealize Γ N γ (f : LaurentSeries ℂ))
      (𝓝[≠] (0 : ℂ)) (𝓝 c)) : (cuspPlace N hΓ hT γ).ord f = 0 := by
  have ho : cuspOrder Γ N γ f = 0 :=
    (tendsto_ne_zero_iff_meromorphicOrderAt_eq_zero
      (meromorphicAt_cuspRealize N hΓ hT f γ)).mp ⟨c, hc, hlim⟩
  rw [cuspPlace_order N hΓ hT γ f hf] at ho
  have he : (cuspRamification N hΓ hT γ : ℤ) * (cuspPlace N hΓ hT γ).ord f = 0 :=
    WithTop.coe_eq_zero.mp ho
  exact (mul_eq_zero.mp he).resolve_left
    (Int.natCast_pos.mpr (cuspRamification_pos N hΓ hT γ)).ne'

variable [Γ.FiniteIndex]

theorem cuspRealize_tendsto_residue (γ : SL(2, ℤ)) (f : functionFieldOver Γ ℂ)
    (hf : f ∈ (cuspPlace N hΓ hT γ).toValuationSubring) :
    Tendsto (cuspRealize Γ N γ (f : LaurentSeries ℂ))
      (𝓝[≠] (0 : ℂ)) (𝓝 (placeEval hT (cuspPlace N hΓ hT γ) f)) := by
  let v := cuspPlace N hΓ hT γ
  let c := placeEval hT v f
  by_cases hc : f = algebraMap ℂ (functionFieldOver Γ ℂ) c
  · change Tendsto _ _ (𝓝 c)
    rw [hc]
    exact tendsto_const_nhds.congr' (cuspRealize_const_eventuallyEq N hT γ c).symm
  · have hne : f - algebraMap ℂ (functionFieldOver Γ ℂ) c ≠ 0 := sub_ne_zero.mpr hc
    have hz : v.rationalEval (place_residue_bijective hT v)
        (f - algebraMap ℂ (functionFieldOver Γ ℂ) c) = 0 := by
      rw [v.rationalEval_sub_algebraMap _ hf]
      exact sub_self c
    have ho := (v.rationalEval_eq_zero_iff_ord_pos (place_residue_bijective hT v)
      (sub_mem hf (v.algebraMap_mem' c)) hne).mp hz
    have hp : 0 < cuspOrder Γ N γ
        (f - algebraMap ℂ (functionFieldOver Γ ℂ) c) := by
      rw [cuspPlace_order N hΓ hT γ _ hne]
      exact WithTop.coe_pos.mpr (mul_pos
        (Int.natCast_pos.mpr (cuspRamification_pos N hΓ hT γ)) ho)
    have hlim := (tendsto_zero_of_meromorphicOrderAt_pos hp).congr'
      (cuspRealize_sub_constant_eventuallyEq N hΓ hT f c γ)
    simpa only [sub_add_cancel, zero_add] using hlim.add_const c

theorem regular_cusp_analytic_representative (γ : SL(2, ℤ))
    (f : functionFieldOver Γ ℂ)
    (hf : f ∈ (cuspPlace N hΓ hT γ).toValuationSubring) :
    ∃ g : ℂ → ℂ, AnalyticAt ℂ g 0 ∧
      g 0 = placeEval hT (cuspPlace N hΓ hT γ) f ∧
      g =ᶠ[𝓝[≠] (0 : ℂ)] cuspRealize Γ N γ (f : LaurentSeries ℂ) := by
  let F := cuspRealize Γ N γ (f : LaurentSeries ℂ)
  have hm : MeromorphicAt F 0 := meromorphicAt_cuspRealize N hΓ hT f γ
  let g := toMeromorphicNFAt F 0
  have he : F =ᶠ[𝓝[≠] (0 : ℂ)] g := hm.eq_nhdsNE_toMeromorphicNFAt
  have ha : AnalyticAt ℂ g 0 := by
    apply meromorphicNFAt_toMeromorphicNFAt.meromorphicOrderAt_nonneg_iff_analyticAt.mp
    rw [← meromorphicOrderAt_congr he]
    exact (cuspPlace_mem_iff N hΓ hT γ f).mp hf
  refine ⟨g, ha, ?_, he.symm⟩
  exact tendsto_nhds_unique_of_eventuallyEq
    (ha.continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
    (cuspRealize_tendsto_residue N hΓ hT γ f hf) he.symm

end
end Dubon2026.SourceFunctionField.GammaOne
