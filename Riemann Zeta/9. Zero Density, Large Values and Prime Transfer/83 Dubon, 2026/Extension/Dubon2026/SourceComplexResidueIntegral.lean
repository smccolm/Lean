import Dubon2026.SourceComplexResidueLocalModels

/-! DUB-17/18 -> original Gamma1 Picard/H1 -> Abel-Jacobi converse ->
analytic reciprocity -> compact-support logarithmic residue identity.
Actual local simple-pole expansions give finite residue support and an
analytic remainder. Previously proved dbar integrability and the kernel
normalization are reused; no integration formula is assumed. -/
namespace Dubon2026.SourceComplexReciprocity.Residue
noncomputable section
open MeasureTheory Filter Complex Metric Set DbarFundamental
open scoped Topology Real

theorem integral_mul_dbar_eq_residues (U : Set ℂ) (hU : IsOpen U) (F c : ℂ → ℂ)
    (hloc : ∀ a ∈ U, ∃ g : ℂ → ℂ, AnalyticAt ℂ g a ∧
      ∀ᶠ z in 𝓝[≠] a, F z = c a / (z - a) + g z)
    (h : ℂ → ℂ) (hh : ContDiff ℝ 1 h) (hsupp : HasCompactSupport h) (hU' : tsupport h ⊆ U) :
    ∫ z, F z * D h z = -π * ∑ᶠ a, c a * h a := by
  have hK : IsCompact (tsupport h) := hsupp
  have hfin := finite_exceptional hU hloc hK hU'

  obtain ⟨T, hmemT⟩ : ∃ T : Finset ℂ, ∀ p, p ∈ T ↔ p ∈ tsupport h ∧ c p ≠ 0 := by
    have hfinT : {z ∈ tsupport h | c z ≠ 0}.Finite :=
      hfin.subset fun z hz => ⟨hz.1, Or.inl hz.2⟩
    exact ⟨hfinT.toFinset, fun p => by simp [Set.Finite.mem_toFinset]⟩

  obtain ⟨R, hR⟩ : ∃ R : ℂ → ℂ, ∀ z, R z = ∑ p ∈ T, c p / (z - p) := ⟨_, fun z => rfl⟩
  obtain ⟨G, hG⟩ : ∃ G : ℂ → ℂ, ∀ z, G z = Freg F c z - R z := ⟨_, fun z => rfl⟩

  obtain ⟨V, hV⟩ : ∃ V : Set ℂ, ∀ z, z ∈ V ↔ z ∈ U ∧ (c z ≠ 0 → z ∈ tsupport h) :=
    ⟨{z | z ∈ U ∧ (c z ≠ 0 → z ∈ tsupport h)}, fun z => Iff.rfl⟩
  have hKV : tsupport h ⊆ V := fun z hz => (hV z).2 ⟨hU' hz, fun _ => hz⟩
  have hVo : IsOpen V := by
    rw [isOpen_iff_mem_nhds]
    intro x hxV
    obtain ⟨hxU, hx⟩ := (hV x).1 hxV
    obtain ⟨g, r, hr, hsub, hg, hFreg, hexc⟩ := clean hU hloc hxU
    refine mem_of_superset (ball_mem_nhds x hr) fun z hz => (hV z).2 ⟨hsub hz, fun hcz => ?_⟩
    by_cases hzx : z = x
    · rw [hzx]
      exact hx (hzx ▸ hcz)
    · exact absurd (hexc z hz hzx).1 hcz
  have hGd : DifferentiableOn ℂ G V := by
    intro x hxV
    obtain ⟨hxU, hx⟩ := (hV x).1 hxV
    obtain ⟨g, r, hr, hsub, hg, hFreg, hexc⟩ := clean hU hloc hxU
    have hGev : G =ᶠ[𝓝 x] fun w => c x / (w - x) + g w - R w := by
      filter_upwards [ball_mem_nhds x hr] with w hw
      rw [hG w, hFreg w hw]
    have hRd : ∀ s : Finset ℂ, x ∉ s →
        DifferentiableAt ℂ (fun w => ∑ p ∈ s, c p / (w - p)) x := by
      intro s hxs
      refine DifferentiableAt.fun_sum fun p hp => ?_
      have hxp : x - p ≠ 0 := sub_ne_zero.2 fun h' => hxs (h' ▸ hp)
      exact (differentiableAt_const _).div (differentiableAt_id.sub_const p) hxp
    have hΦ : DifferentiableAt ℂ (fun w => c x / (w - x) + g w - R w) x := by
      by_cases hxT : x ∈ T
      · have hfun : (fun w => c x / (w - x) + g w - R w)
            = fun w => g w - ∑ p ∈ T.erase x, c p / (w - p) := by
          funext w
          rw [hR w, ← Finset.add_sum_erase T (fun p => c p / (w - p)) hxT]
          ring
        rw [hfun]
        exact (hg x (mem_ball_self hr)).differentiableAt.sub (hRd _ (Finset.notMem_erase x T))
      · have hcx : c x = 0 := by
          by_contra hcx
          exact hxT ((hmemT x).2 ⟨hx hcx, hcx⟩)
        have hfun : (fun w => c x / (w - x) + g w - R w)
            = fun w => g w - ∑ p ∈ T, c p / (w - p) := by
          funext w
          rw [hR w, hcx, zero_div, zero_add]
        rw [hfun]
        exact (hg x (mem_ball_self hr)).differentiableAt.sub (hRd _ hxT)
    exact (hΦ.congr_of_eventuallyEq hGev).differentiableWithinAt

  have hDh_cont : Continuous (D h) := D_continuous hh
  have hDh_supp : HasCompactSupport (D h) := D_hasCompactSupport hsupp
  have hIG : Integrable fun z => G z * D h z :=
    integrable_mul_of_tsupport_subset hVo hGd.continuousOn hDh_cont hDh_supp
      ((tsupport_D_subset h).trans hKV)
  have hIp : ∀ p, Integrable fun z => c p * ((z - p)⁻¹ * D h z) := fun p =>
    (integrable_inv_sub_mul p hDh_cont hDh_supp).const_mul _
  have hIR : Integrable fun z => ∑ p ∈ T, c p * ((z - p)⁻¹ * D h z) :=
    integrable_finsetSum _ fun p _ => hIp p

  have hae : (fun z => F z * D h z)
      =ᵐ[volume] fun z => G z * D h z + ∑ p ∈ T, c p * ((z - p)⁻¹ * D h z) := by
    filter_upwards [hfin.countable.ae_notMem volume] with z hz
    by_cases hzK : z ∈ tsupport h
    · have hFz : F z = Freg F c z := by
        by_contra hne
        exact hz ⟨hzK, Or.inr hne⟩
      have hsum : ∑ p ∈ T, c p / (z - p) * D h z = ∑ p ∈ T, c p * ((z - p)⁻¹ * D h z) :=
        Finset.sum_congr rfl fun p _ => by ring
      rw [hFz, hG z, hR z, sub_mul, Finset.sum_mul, hsum]
      ring
    · have h0 : D h z = 0 := D_eq_zero_of_notMem_tsupport hzK
      simp [h0]

  have hHG : ∫ z, G z * D h z = 0 :=
    Dubon2026.SourceComplexReciprocity.integral_mul_dbar_eq_zero V hVo G hGd h hh hsupp hKV
  have hHp : ∀ p, ∫ z, (z - p)⁻¹ * D h z = -π * h p := fun p =>
    DbarFundamental.integral_inv_sub_mul_dbar p h hh hsupp

  have hfs : ∑ᶠ a, c a * h a = ∑ p ∈ T, c p * h p := by
    apply finsum_eq_sum_of_support_subset
    intro a ha
    rw [Function.mem_support, mul_ne_zero_iff] at ha
    rw [Finset.mem_coe, hmemT]
    exact ⟨subset_tsupport _ ha.2, ha.1⟩
  rw [integral_congr_ae hae, integral_add hIG hIR, integral_finsetSum _ (fun p _ => hIp p), hHG,
    zero_add, hfs, Finset.mul_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [integral_const_mul, hHp p]
  ring

end
end Dubon2026.SourceComplexReciprocity.Residue
