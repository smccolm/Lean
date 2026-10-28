import Dubon2026.SourceModularSmoothGeometry

/-! Adapted from anthropics/fermats-last-theorem (Apache-2.0), frozen primary
Def_ModularCurve_SmoothedFundamental and
S_ModularCurve_contDiff_and_finsum_smoothedFundamental_eq_one;
exact hashes are recorded in modular-smooth-partition-route-875.json.
DUB-17/18 -> actual Gamma1 Picard/H1 -> Abel-Jacobi converse ->
analytic reciprocity -> winding-period limit -> compact smooth modular
partition. The native group/coset equivalence preserves the exact chosen
coset representatives; no separate bijection or orbit-sum assumption is
introduced. The integral normalization remains a separate obligation. -/
namespace Dubon2026.SourceSmoothedFundamental
noncomputable section
open UpperHalfPlane hiding I coe_smul
open Filter Complex MulAction Set
open scoped MatrixGroups Topology ContDiff Pointwise
local notation "𝕌" => UpperHalfPlane.upperHalfPlaneSet

theorem pOne_contDiff (n : ℕ∞) : ContDiff ℝ n pOne :=
  (Real.smoothTransition.contDiff.comp (contDiff_id.add contDiff_const)).sub
    Real.smoothTransition.contDiff

theorem pTwo_contDiff (T : ℝ) (n : ℕ∞) : ContDiff ℝ n (pTwo T) :=
  (Real.smoothTransition.contDiff.comp ((contDiff_const.mul contDiff_id).sub contDiff_const)).mul
    (Real.smoothTransition.contDiff.comp (contDiff_const.sub contDiff_id))

theorem bump_contDiff (T : ℝ) (n : ℕ∞) : ContDiff ℝ n (bump T) :=
  ((pOne_contDiff n).comp Complex.reCLM.contDiff).mul
    ((pTwo_contDiff T n).comp Complex.imCLM.contDiff)

theorem recip_contDiff (n : ℕ∞) : ContDiff ℝ n recip := by
  refine contDiff_iff_contDiffAt.2 fun t => ?_
  rcases lt_or_ge (1 / 8 : ℝ) t with h | h
  · exact ((Real.smoothTransition.contDiff.comp
      ((contDiff_const.mul contDiff_id).sub contDiff_const)).contDiffAt).div contDiffAt_id
      (by positivity)
  · have : recip =ᶠ[𝓝 t] fun _ => 0 := by
      filter_upwards [Iio_mem_nhds (show t < 1 / 4 by linarith)] with s hs
      simp [recip, Real.smoothTransition.zero_of_nonpos (by linarith [hs.out] : 4 * s - 1 ≤ 0)]
    exact contDiffAt_const.congr_of_eventuallyEq this

theorem gcut_contDiff (T : ℝ) (n : ℕ∞) : ContDiff ℝ n (gcut T) :=
  contDiff_const.sub (Real.smoothTransition.contDiff.comp (Complex.imCLM.contDiff.sub
    contDiff_const))

/-- Upper-half-plane preimage of the compact cutoff rectangle. -/
def boxH (T : ℝ) : Set ℍ := ((↑) : ℍ → ℂ) ⁻¹' box T

theorem isCompact_coe_preimage {K : Set ℂ} (hK : IsCompact K) (hK' : K ⊆ 𝕌) :
    IsCompact (((↑) : ℍ → ℂ) ⁻¹' K) := by
  refine isEmbedding_coe.isCompact_iff.2 ?_
  rw [image_preimage_eq_of_subset]
  · exact hK
  · intro z hz; exact ⟨⟨z, hK' hz⟩, rfl⟩

theorem box_subset (T : ℝ) : box T ⊆ 𝕌 := fun _ hz => im_pos_of_mem_box hz

theorem isCompact_boxH (T : ℝ) : IsCompact (boxH T) :=
  isCompact_coe_preimage (isCompact_box T) (box_subset T)

theorem hasFiniteSupport_bump_mob (T : ℝ) (τ : ℍ) :
    Function.HasFiniteSupport fun γ : SL(2, ℤ) => bump T (mob γ τ) := by
  refine (finite_moving {τ} (boxH T) isCompact_singleton (isCompact_boxH T)).subset ?_
  intro γ hγ
  refine ⟨γ • τ, ⟨τ, rfl, rfl⟩, ?_⟩
  show ((γ • τ : ℍ) : ℂ) ∈ box T
  rw [coe_smul]
  exact support_bump_subset T hγ

theorem hasFiniteSupport_puCut_mob (T : ℝ) (τ : ℍ) :
    Function.HasFiniteSupport fun γ : SL(2, ℤ) => puCut T (mob γ τ) :=
  (hasFiniteSupport_bump_mob T τ).subset fun _ hγ =>
    support_pu_subset T (left_ne_zero_of_mul hγ)

theorem hasFiniteSupport_pu_mob (T : ℝ) (τ : ℍ) :
    Function.HasFiniteSupport fun γ : SL(2, ℤ) => pu T (mob γ τ) :=
  (hasFiniteSupport_bump_mob T τ).subset fun _ hγ => support_pu_subset T hγ

theorem bump_le_cover (T : ℝ) (τ : ℍ) (γ : SL(2, ℤ)) : bump T (mob γ τ) ≤ cover T τ :=
  single_le_finsum γ (hasFiniteSupport_bump_mob T τ) fun _ => bump_nonneg _ _

theorem cover_mob (T : ℝ) (γ' : SL(2, ℤ)) (τ : ℍ) : cover T (mob γ' τ) = cover T τ := by
  unfold cover
  simp_rw [mob_mob]
  exact finsum_comp_equiv (Equiv.mulRight γ') (f := fun γ => bump T (mob γ τ))

theorem half_le_cover {T : ℝ} (τ : ℍ) (h1 : τ.im ≤ T + 3) (h2 : τ.im⁻¹ ≤ T + 3) :
    1 / 2 ≤ cover T τ := by
  obtain ⟨γ, hre, him, him'⟩ := exists_smul_nice τ
  refine le_trans ?_ (bump_le_cover T τ γ)
  rw [← coe_smul]
  unfold bump
  rw [pTwo_eq_one (by rw [coe_im]; exact him)
    (by rw [coe_im]; exact him'.trans (max_le h1 h2)), mul_one]

  have hx : |(↑(γ • τ) : ℂ).re| ≤ 1 / 2 := by rw [coe_re]; exact hre
  rcases abs_le.1 hx with ⟨hx1, hx2⟩
  have st_half : Real.smoothTransition (1 / 2 : ℝ) = 1 / 2 := by
    unfold Real.smoothTransition
    have h : (1 : ℝ) - 1 / 2 = 1 / 2 := by norm_num
    rw [h]
    have hp := expNegInvGlue.pos_of_pos (show (0 : ℝ) < 1 / 2 by norm_num)
    rw [div_eq_iff (by positivity)]
    ring
  unfold pOne
  rcases le_total (↑(γ • τ) : ℂ).re 0 with h | h
  · rw [Real.smoothTransition.zero_of_nonpos h, sub_zero, ← st_half]
    exact Real.smoothTransition.monotone (by linarith)
  · rw [Real.smoothTransition.one_of_one_le (by linarith)]
    have := Real.smoothTransition.monotone (show (↑(γ • τ) : ℂ).re ≤ 1 / 2 by linarith)
    rw [st_half] at this
    linarith

theorem finsum_pu_mob {T : ℝ} (τ : ℍ) (h : 1 / 2 ≤ cover T τ) :
    ∑ᶠ γ : SL(2, ℤ), pu T (mob γ τ) = 1 := by
  unfold pu
  simp_rw [cover_mob]
  rw [← finsum_mul]
  exact mul_recip_of_half_le h

theorem finsum_pu_mob_le_one (T : ℝ) (τ : ℍ) : ∑ᶠ γ : SL(2, ℤ), pu T (mob γ τ) ≤ 1 := by
  unfold pu
  simp_rw [cover_mob]
  rw [← finsum_mul]
  exact mul_recip_le_one _

theorem cover_eventuallyEq_sum (T : ℝ) {z₀ : ℂ} (hz₀ : 0 < z₀.im) :
    ∃ s : Finset SL(2, ℤ), cover T =ᶠ[𝓝 z₀] fun z => ∑ γ ∈ s, bump T (mob γ z) := by
  have hN : Metric.closedBall z₀ (z₀.im / 2) ⊆ 𝕌 := by
    intro z hz
    have h1 := abs_im_le_norm (z - z₀)
    rw [Metric.mem_closedBall, dist_eq_norm] at hz
    rw [sub_im] at h1
    have := (abs_le.1 (h1.trans hz)).1
    show 0 < z.im
    linarith
  have hNH : IsCompact (((↑) : ℍ → ℂ) ⁻¹' Metric.closedBall z₀ (z₀.im / 2)) :=
    isCompact_coe_preimage (isCompact_closedBall _ _) hN
  have hfin := finite_moving _ (boxH T) hNH (isCompact_boxH T)
  refine ⟨hfin.toFinset, ?_⟩
  filter_upwards [Metric.closedBall_mem_nhds z₀ (by positivity : 0 < z₀.im / 2)] with z hz
  apply finsum_eq_sum_of_support_subset
  intro γ hγ
  simp only [Set.Finite.coe_toFinset, mem_setOf_eq]
  refine ⟨γ • ⟨z, hN hz⟩, ⟨⟨z, hN hz⟩, hz, rfl⟩, ?_⟩
  show ((γ • (⟨z, hN hz⟩ : ℍ) : ℍ) : ℂ) ∈ box T
  rw [coe_smul]
  exact support_bump_subset T hγ

theorem cover_contDiffAt (T : ℝ) {z : ℂ} (hz : 0 < z.im) (n : ℕ∞) :
    ContDiffAt ℝ n (cover T) z := by
  obtain ⟨s, hs⟩ := cover_eventuallyEq_sum T hz
  refine ContDiffAt.congr_of_eventuallyEq ?_ hs
  exact ContDiffAt.sum fun γ _ => (bump_contDiff T n).contDiffAt.comp z (mob_contDiffAt γ hz n)

theorem pu_contDiff (T : ℝ) (n : ℕ∞) : ContDiff ℝ n (pu T) := by
  refine contDiff_iff_contDiffAt.2 fun z => ?_
  rcases lt_or_ge 0 z.im with hz | hz
  · exact (bump_contDiff T n).contDiffAt.mul ((recip_contDiff n).contDiffAt.comp z
      (cover_contDiffAt T hz n))
  · have : pu T =ᶠ[𝓝 z] fun _ => 0 := by
      filter_upwards [(Complex.continuous_im.isOpen_preimage _ isOpen_Iio).mem_nhds
        (show z ∈ Complex.im ⁻¹' Iio (5 / 8 : ℝ) by
          simp only [mem_preimage, mem_Iio]; linarith)] with w hw
      have hb : bump T w = 0 := by
        by_contra hb
        have := (mem_of_bump_ne_zero hb).2.1
        simp only [mem_preimage, mem_Iio] at hw; linarith
      simp [pu, hb]
    exact contDiffAt_const.congr_of_eventuallyEq this

theorem puCut_contDiff (T : ℝ) (n : ℕ∞) : ContDiff ℝ n (puCut T) :=
  (pu_contDiff T n).mul (gcut_contDiff T n)


end
end Dubon2026.SourceSmoothedFundamental
