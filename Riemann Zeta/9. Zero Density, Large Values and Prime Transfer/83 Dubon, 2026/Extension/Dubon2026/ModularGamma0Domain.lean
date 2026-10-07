import Dubon2026.ModularCosetProjection

/-! # The Gamma0 fundamental domain and the actual Petersson integral -/

namespace Dubon2026

open Matrix.SpecialLinearGroup CongruenceSubgroup UpperHalfPlane ModularGroup MeasureTheory
open scoped MatrixGroups Pointwise ModularForm

noncomputable section

local notation "μ_hyp" => (volume : Measure ℍ)

variable (Q : ℕ) [NeZero Q]

/-- The genuine finite integer coset space at positive level. -/
local instance gamma0DomainQuotientFintype : Fintype (SL(2, ℤ) ⧸ Gamma0 Q) :=
  Subgroup.fintypeQuotientOfFiniteIndex

/-- The actual union of inverse-coset translates of the open modular domain. -/
def gamma0FundamentalDomain : Set ℍ :=
  ⋃ q : SL(2, ℤ) ⧸ Gamma0 Q, (q.out : SL(2, ℤ))⁻¹ • (fdo : Set ℍ)

/-- The literal integer coset tiling is a fundamental domain for projective Gamma0. -/
theorem isFundamentalDomain_gamma0 :
    IsFundamentalDomain (projectiveGamma0 Q) (gamma0FundamentalDomain Q) μ_hyp := by
  have h := fundamentalDomain_iUnion_smul_of_transversal isFundamentalDomain_fdo_PSL
    (r := fun q : SL(2, ℤ) ⧸ Gamma0 Q => (QuotientGroup.mk q.out : PSL(2, ℤ))⁻¹)
    (gamma0CosetEquiv Q) (fun q => by simpa only [inv_inv] using gamma0CosetEquiv_out Q q)
  exact h

omit [NeZero Q] in
/-- The actual coset tiles overlap only on hyperbolic null sets. -/
theorem gamma0Domain_tiles_aedisjoint :
    Pairwise (fun q₁ q₂ : SL(2, ℤ) ⧸ Gamma0 Q =>
      AEDisjoint μ_hyp ((q₁.out : SL(2, ℤ))⁻¹ • (fdo : Set ℍ))
        ((q₂.out : SL(2, ℤ))⁻¹ • (fdo : Set ℍ))) := by
  intro q₁ q₂ hne
  have hne' : (QuotientGroup.mk q₁.out : PSL(2, ℤ))⁻¹ ≠
      (QuotientGroup.mk q₂.out : PSL(2, ℤ))⁻¹ := by
    intro he
    apply hne
    apply (gamma0CosetEquiv Q).injective
    rw [gamma0CosetEquiv_out, gamma0CosetEquiv_out, inv_injective he]
  have hdisj := isFundamentalDomain_fdo_PSL.aedisjoint hne'
  exact hdisj

omit [NeZero Q] in
/-- Each literal inverse-coset tile is hyperbolically measurable. -/
theorem gamma0Domain_tile_nullMeasurable (q : SL(2, ℤ) ⧸ Gamma0 Q) :
    NullMeasurableSet ((q.out : SL(2, ℤ))⁻¹ • (fdo : Set ℍ)) μ_hyp :=
  isOpen_fdo.measurableSet.nullMeasurableSet.smul _

/-- The genuine higher-level fundamental domain has finite hyperbolic volume. -/
theorem gamma0FundamentalDomain_volume_lt_top : μ_hyp (gamma0FundamentalDomain Q) < ⊤ := by
  unfold gamma0FundamentalDomain
  refine lt_of_le_of_lt (measure_iUnion_le _) ?_
  rw [tsum_fintype]
  refine ENNReal.sum_lt_top.mpr fun q _ => ?_
  rw [measure_smul]
  exact lt_of_le_of_lt (measure_mono fdo_subset_fd) hyperbolicMeasure_fd_lt_top

/-- Integrability of the actual Petersson integrand on the whole higher-level domain. -/
theorem integrableOn_petersson_gamma0Domain {k : ℤ}
    (f g : CuspForm ((Gamma0 Q).map (mapGL ℝ)) k) :
    IntegrableOn (petersson k f g) (gamma0FundamentalDomain Q) μ_hyp := by
  obtain ⟨C, hC⟩ := CuspFormClass.petersson_bounded_left k ((Gamma0 Q).map (mapGL ℝ)) f g
  exact IntegrableOn.of_bound (gamma0FundamentalDomain_volume_lt_top Q)
    ((petersson_continuous k (ModularFormClass.continuous f)
      (ModularFormClass.continuous g)).aestronglyMeasurable.restrict)
    C (ae_of_all _ hC)

/-- The finite coset Petersson pairing equals the integral over the actual Gamma0 domain. -/
theorem cuspPetersson_eq_gamma0Domain_integral {k : ℤ}
    (f g : CuspForm ((Gamma0 Q).map (mapGL ℝ)) k) :
    cuspPetersson f g = ∫ τ in gamma0FundamentalDomain Q, petersson k f g τ ∂μ_hyp := by
  have hint := integrableOn_petersson_gamma0Domain Q f g
  rw [gamma0FundamentalDomain] at hint ⊢
  rw [integral_iUnion_ae (gamma0Domain_tile_nullMeasurable Q)
    (gamma0Domain_tiles_aedisjoint Q) hint, tsum_fintype]
  unfold cuspPetersson
  apply Finset.sum_congr rfl
  intro q _
  unfold peterssonInner
  simp_rw [petersson_slash_SL]
  rw [setIntegral_fd_eq_fdo]
  exact ((measurePreserving_smul (q.out : SL(2, ℤ))⁻¹ μ_hyp).setIntegral_image_emb
    (measurableEmbedding_const_smul _) _ _).symm


omit [NeZero Q] in
/-- The actual Petersson integrand is invariant under projective Gamma0. -/
theorem petersson_projectiveGamma0_invariant {k : ℤ}
    (f g : CuspForm ((Gamma0 Q).map (mapGL ℝ)) k)
    (γ : projectiveGamma0 Q) (τ : ℍ) : petersson k f g (γ • τ) = petersson k f g τ := by
  obtain ⟨δ, hδ, he⟩ := γ.property
  change petersson k f g ((γ : PSL(2, ℤ)) • τ) = _
  rw [← he]
  change petersson k f g (δ • τ) = _
  rw [← petersson_slash_SL, slash_Gamma0_eq f δ hδ,
    slash_Gamma0_eq g δ hδ]

/-- The finite coset pairing is independent of the chosen genuine Gamma0 fundamental domain. -/
theorem cuspPetersson_eq_fundamentalDomain_integral {k : ℤ}
    (f g : CuspForm ((Gamma0 Q).map (mapGL ℝ)) k) {S : Set ℍ}
    (hS : IsFundamentalDomain (projectiveGamma0 Q) S μ_hyp) :
    cuspPetersson f g = ∫ τ in S, petersson k f g τ ∂μ_hyp := by
  rw [cuspPetersson_eq_gamma0Domain_integral Q]
  exact (isFundamentalDomain_gamma0 Q).setIntegral_eq hS
    (petersson_projectiveGamma0_invariant Q f g)

end
end Dubon2026
