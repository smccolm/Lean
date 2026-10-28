import Dubon2026.SourceMeromorphicPeriodUntwist

/-! DUB-17/18 -> original Gamma1 Picard/H1 -> Abel-Jacobi converse ->
analytic reciprocity -> nonzero limits of normalized untwisting at cusps.
Use native upper-half-plane analytic action and local normalization.
The local order-zero bound is adapted from the pinned Apache-2.0
scope-848 untwisting primary; no custom Mobius infrastructure is needed. -/
namespace Dubon2026.SourcePeriodUntwist
noncomputable section
open UpperHalfPlane Filter Matrix.SpecialLinearGroup
open scoped MatrixGroups Topology

theorem order_translate (F : ℍ → ℂ) (σ : SL(2, ℤ)) (τ : ℍ) :
    meromorphicOrderAt (fun z => F (σ • ofComplex z)) (τ : ℂ) =
      meromorphicOrderAt (F ∘ ofComplex) ((σ • τ : ℍ) : ℂ) := by
  have hd1 : (σ : GL (Fin 2) ℝ).val.det = 1 := Matrix.SpecialLinearGroup.det_coe _
  have hd : 0 < (σ : GL (Fin 2) ℝ).val.det := by rw [hd1]; exact one_pos
  simpa using meromorphicOrderAt_comp_smul (f := F) (τ := τ) hd

theorem meromorphicAt_translate (F : ℍ → ℂ)
    (hF : ∀ τ : ℍ, MeromorphicAt (F ∘ ofComplex) (τ : ℂ))
    (σ : SL(2, ℤ)) (τ : ℍ) :
    MeromorphicAt (fun z => F (σ • ofComplex z)) (τ : ℂ) := by
  have hd1 : (σ : GL (Fin 2) ℝ).val.det = 1 := Matrix.SpecialLinearGroup.det_coe _
  have hd : 0 < (σ : GL (Fin 2) ℝ).val.det := by rw [hd1]; exact one_pos
  have ha := τ.analyticAt_smul hd
  have hm : MeromorphicAt (F ∘ ofComplex)
      ((fun z : ℂ => (((σ : GL (Fin 2) ℝ) • ofComplex z : ℍ) : ℂ)) (τ : ℂ)) := by
    simpa only [ofComplex_apply] using hF ((σ : GL (Fin 2) ℝ) • τ)
  simpa [Function.comp_def] using
    MeromorphicAt.comp_analyticAt (g := fun z : ℂ =>
      (((σ : GL (Fin 2) ℝ) • ofComplex z : ℍ) : ℂ)) (x := (τ : ℂ)) hm ha

theorem reg_eq_nhdsNE (F : ℍ → ℂ)
    (hF : ∀ τ : ℍ, MeromorphicAt (F ∘ ofComplex) (τ : ℂ)) (τ : ℍ) :
    (fun w : ℍ => reg F w) =ᶠ[𝓝[≠] τ] F := by
  have hm : MeromorphicOn (F ∘ ofComplex) upperHalfPlaneSet := fun z hz => hF ⟨z, hz⟩
  apply SourceFunctionField.ModularRatios.eventually_nhdsNE_coe_iff.mp
  filter_upwards [hm.toMeromorphicNFOn_eq_self_on_nhdsNE τ.im_pos,
    eventually_nhdsWithin_of_eventually_nhds
      (isOpen_upperHalfPlaneSet.mem_nhds τ.im_pos)] with z he him
  simpa only [Function.comp_apply, ofComplex_apply_of_im_pos him] using he

theorem analyticAt_reg_of_order_zero (F : ℍ → ℂ)
    (hF : ∀ τ : ℍ, MeromorphicAt (F ∘ ofComplex) (τ : ℂ)) (τ : ℍ)
    (ho : meromorphicOrderAt (F ∘ ofComplex) (τ : ℂ) = 0) :
    AnalyticAt ℂ (reg F) (τ : ℂ) := by
  have hm : MeromorphicOn (F ∘ ofComplex) upperHalfPlaneSet := fun z hz => hF ⟨z, hz⟩
  apply (meromorphicNFOn_toMeromorphicNFOn (F ∘ ofComplex) upperHalfPlaneSet
    τ.im_pos).meromorphicOrderAt_nonneg_iff_analyticAt.mp
  rw [meromorphicOrderAt_toMeromorphicNFOn hm τ.im_pos, ho]

theorem meromorphicOrderAt_eq_zero_of_near {g : ℂ → ℂ} {z L : ℂ} (hg : MeromorphicAt g z)
    (hL : L ≠ 0) (hnear : ∀ᶠ w in 𝓝[≠] z, dist (g w) L < ‖L‖ / 2) :
    meromorphicOrderAt g z = 0 := by
  have hLpos : 0 < ‖L‖ := norm_pos_iff.2 hL
  have hntop : meromorphicOrderAt g z ≠ ⊤ := by
    intro htop
    rw [meromorphicOrderAt_eq_top_iff] at htop
    obtain ⟨w, hw0, hw⟩ := (htop.and hnear).exists
    rw [hw0, dist_comm, dist_zero_right] at hw
    linarith
  have hnneg : 0 ≤ meromorphicOrderAt g z := by
    by_contra hneg
    rw [not_le] at hneg
    have hcob := tendsto_cobounded_of_meromorphicOrderAt_neg hneg
    have hbig : ∀ᶠ w in 𝓝[≠] z, 2 * ‖L‖ + 1 ≤ ‖g w‖ :=
      hcob.eventually (eventually_cobounded_le_norm (2 * ‖L‖ + 1))
    obtain ⟨w, hw1, hw2⟩ := (hbig.and hnear).exists
    have : ‖g w‖ ≤ dist (g w) L + ‖L‖ := by
      simpa [dist_eq_norm] using norm_le_norm_sub_add (g w) L
    linarith
  obtain ⟨c, hc⟩ := tendsto_nhds_of_meromorphicOrderAt_nonneg hg hnneg
  have hcL : dist c L ≤ ‖L‖ / 2 :=
    le_of_tendsto (hc.dist tendsto_const_nhds) (hnear.mono fun w hw => hw.le)
  have hc0 : c ≠ 0 := by
    intro h0
    rw [h0, dist_comm, dist_zero_right] at hcL
    linarith
  exact (tendsto_ne_zero_iff_meromorphicOrderAt_eq_zero hg).1 ⟨c, hc0, hc⟩

end
end Dubon2026.SourcePeriodUntwist
