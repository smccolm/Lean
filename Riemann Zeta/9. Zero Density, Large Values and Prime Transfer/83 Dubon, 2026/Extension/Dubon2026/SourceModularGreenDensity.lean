import Dubon2026.SourceModularGreenEdges
import Dubon2026.SourceModularGreenMeasure

/-! DUB-17/18 -> original all-weight arithmetic association -> Gamma1 Picard/H1
-> Abel-Jacobi converse -> reciprocity -> winding-period boundary identity.
Actual differential transformation, translated cusp estimates and finite
hyperbolic volume prove integrability. The existing projective tiling then
gives the exact finite sum of planar tile integrals. Adapted from pinned
Apache-2.0 anthropics source; no tiling or integrability certificate is assumed. -/
namespace Dubon2026.SourceModularGreenPairing
noncomputable section
open UpperHalfPlane hiding I
open Filter Complex MeasureTheory Asymptotics
open SourceSmoothedUnfolding SourceSmoothDivisor SourceSmoothOrbitIntegral SourceModularSidePairing
open SourceComplexReciprocity.Dipole
open scoped MatrixGroups Topology ModularForm ComplexConjugate Real NNReal Pointwise
variable {Γ : Subgroup SL(2, ℤ)}

variable (g : CuspForm (Γ.map (Matrix.SpecialLinearGroup.mapGL ℝ)) 2) (L : ℂ → ℂ)
  (L' : ℂ → ℂ →L[ℝ] ℂ)
  (hL : ∀ z : ℂ, 0 < z.im → HasFDerivAt L (L' z) z)
  (hL' : ContinuousOn L' {z : ℂ | 0 < z.im})
  (c : SL(2, ℤ) → ℂ) (hLc : ∀ γ ∈ Γ, ∀ τ : ℍ, L ((γ • τ : ℍ) : ℂ) = L τ + c γ)
  (hbd : ∀ σ : SL(2, ℤ), ∃ C Y : ℝ, ∀ z : ℂ, Y ≤ z.im →
    ‖L ((σ • ofComplex z : ℍ) : ℂ)‖ ≤ C ∧
      ‖fderiv ℝ (fun u : ℂ => L ((σ • ofComplex u : ℍ) : ℂ)) z‖ ≤ C)

/-- Actual antiholomorphic-logarithm density in hyperbolic coordinates. -/
def Pd (L' : ℂ → ℂ →L[ℝ] ℂ) (g : ℍ → ℂ) (τ : ℍ) : ℂ :=
  dbarL (L' τ) * g τ * ((τ.im : ℂ) ^ 2)

/-- The native slashed cusp density on one modular tile in planar coordinates. -/
def Hd (L' : ℂ → ℂ →L[ℝ] ℂ) (g : ℍ → ℂ) (σ : SL(2, ℤ)) (z : ℂ) : ℂ :=
  tilePull g σ z * (conj (dsm σ z) * dbarL (L' (sm σ z)))

include hL hLc in

theorem dbarL_smul (γ : SL(2, ℤ)) (hγ : γ ∈ Γ) (τ : ℍ) :
    dbarL (L' ((γ • τ : ℍ) : ℂ)) = conj (denom (γ : GL (Fin 2) ℝ) τ) ^ 2 * dbarL (L' τ) := by
  have hτ : 0 < (τ : ℂ).im := τ.im_pos

  have hev : (fun u => L (sm γ u)) =ᶠ[𝓝 (τ : ℂ)] fun u => L u + c γ := by
    filter_upwards [isOpen_upperHalfPlaneSet.mem_nhds hτ] with u hu
    have := hLc γ hγ (ofComplex u)
    rw [coe_ofComplex hu] at this
    exact this
  have h1 : HasFDerivAt (fun u => L (sm γ u)) (L' τ) τ := by
    refine HasFDerivAt.congr_of_eventuallyEq ?_ hev
    exact (hL _ hτ).add_const _
  have h2 : HasFDerivAt (fun u => L (sm γ u)) (Fd L' γ τ) τ := hasFDerivAt_Lt L L' hL γ hτ
  have heq : Fd L' γ τ = L' τ := h2.unique h1
  have h3 := dbarL_Fd L' γ τ
  rw [heq, sm_coe, dsm_coe] at h3
  have hD : denom (γ : GL (Fin 2) ℝ) τ ≠ 0 := UpperHalfPlane.denom_ne_zero _ _
  have hcD : conj (denom (γ : GL (Fin 2) ℝ) τ) ≠ 0 := (map_ne_zero _).2 hD
  rw [h3, map_div₀, map_one, map_pow]
  field_simp

theorem Pd_smul (σ : SL(2, ℤ)) (τ : ℍ) : Pd L' g (σ • τ) = Hd L' g σ τ * ((τ.im : ℂ) ^ 2) := by
  simp only [Pd, Hd]
  have hD : denom (σ : GL (Fin 2) ℝ) τ ≠ 0 := UpperHalfPlane.denom_ne_zero _ _
  have hcD : conj (denom (σ : GL (Fin 2) ℝ) τ) ≠ 0 := (map_ne_zero _).2 hD
  have hg : g (σ • τ) = tilePull g σ τ * denom (σ : GL (Fin 2) ℝ) τ ^ 2 := by
    rw [tilePull, ofComplex_apply, ModularForm.SL_slash_apply, zpow_neg]
    norm_cast
    field_simp
  have him : ((σ • τ).im : ℂ) = (τ.im : ℂ) / (Complex.normSq (denom (σ : GL (Fin 2) ℝ) τ) : ℂ) := by
    rw [ModularGroup.im_smul_eq_div_normSq]; push_cast; rfl
  have hns : (Complex.normSq (denom (σ : GL (Fin 2) ℝ) τ) : ℂ) =
      conj (denom (σ : GL (Fin 2) ℝ) τ) * denom (σ : GL (Fin 2) ℝ) τ := by
    rw [Complex.normSq_eq_conj_mul_self]
  rw [← sm_coe, hg, him, hns, sm_coe, dsm_coe, map_div₀, map_one, map_pow]
  rw [← sm_coe]
  field_simp

include hL' in
theorem continuous_Pd : Continuous (Pd L' g) := by
  unfold Pd
  have h1 : Continuous fun τ : ℍ => L' (τ : ℂ) :=
    hL'.comp_continuous UpperHalfPlane.continuous_coe fun τ => τ.im_pos
  have h2 : Continuous fun τ : ℍ => dbarL (L' (τ : ℂ)) := by
    unfold dbarL
    exact (((ContinuousLinearMap.apply ℝ ℂ (1 : ℂ)).continuous.comp h1).add
      (continuous_const.mul ((ContinuousLinearMap.apply ℝ ℂ I).continuous.comp h1))).div_const _
  exact (h2.mul (CuspFormClass.holo g).continuous).mul
    ((Complex.continuous_ofReal.comp UpperHalfPlane.continuous_im).pow 2)

theorem sq_mul_exp_neg_le {c : ℝ} (hc : 0 < c) {v : ℝ} (hv : 0 ≤ v) :
    v ^ 2 * Real.exp (-c * v) ≤ 2 / c ^ 2 := by
  have h := Real.quadratic_le_exp_of_nonneg (mul_nonneg hc.le hv)
  have hexp : 0 < Real.exp (c * v) := Real.exp_pos _
  have h1 : (c * v) ^ 2 / 2 ≤ Real.exp (c * v) := by nlinarith [mul_nonneg hc.le hv]
  rw [show -c * v = -(c * v) by ring, Real.exp_neg]
  rw [le_div_iff₀ (by positivity : (0 : ℝ) < c ^ 2)]
  have : v ^ 2 * (Real.exp (c * v))⁻¹ * c ^ 2 = (c * v) ^ 2 / Real.exp (c * v) := by
    field_simp
  rw [this, div_le_iff₀ hexp]
  linarith

variable [Γ.FiniteIndex]

include hL hL' hbd in

theorem Pd_bound_tile (σ : SL(2, ℤ)) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ u : ℍ, u ∈ ModularGroup.fd → ‖Pd L' g (σ • u)‖ ≤ M := by
  have h2 : (0 : ℝ) < 1 / 2 := by norm_num
  obtain ⟨c₁, hc₁, C₁, hC₁0, hC₁⟩ := tilePull_decay g σ h2
  obtain ⟨CF, hCF⟩ := Fd_bound L L' hL hL' σ (hbd σ)
  refine ⟨C₁ * (2 / c₁ ^ 2) * max CF 0, by positivity, fun u hu => ?_⟩
  have huC : (u : ℂ) ∈ SourceModularGreen.D := coe_mem_fdC_of_mem_fd hu
  have hui : 1 / 2 ≤ (u : ℂ).im := (im_gt_of_mem_fdC huC).le
  have hure : |(u : ℂ).re| ≤ 1 := huC.1.trans (by norm_num)
  rw [Pd_smul, Hd, ← dbarL_Fd, norm_mul, norm_mul]
  have hF : ‖dbarL (Fd L' σ u)‖ ≤ max CF 0 :=
    ((norm_dbarL_le _).trans (hCF _ hui hure)).trans (le_max_left _ _)
  have hG : ‖tilePull g σ u‖ ≤ C₁ * Real.exp (-c₁ * (u : ℂ).im) := hC₁ _ hui
  have hsq : ‖((u.im : ℂ)) ^ 2‖ = u.im ^ 2 := by
    rw [norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos u.im_pos]
  rw [hsq]
  have hv := sq_mul_exp_neg_le hc₁ u.im_pos.le
  have him : (u : ℂ).im = u.im := rfl
  rw [him] at hG
  calc ‖tilePull g σ u‖ * ‖dbarL (Fd L' σ u)‖ * u.im ^ 2
      ≤ (C₁ * Real.exp (-c₁ * u.im)) * max CF 0 * u.im ^ 2 := by gcongr
    _ = C₁ * (u.im ^ 2 * Real.exp (-c₁ * u.im)) * max CF 0 := by ring
    _ ≤ C₁ * (2 / c₁ ^ 2) * max CF 0 := by gcongr

variable [Fintype (SL(2, ℤ) ⧸ Γ)]

include hL hL' hbd in

theorem integrableOn_Pd :
    IntegrableOn (Pd L' g) (closedDomain Γ) := by
  choose M hM0 hM using fun q : SL(2, ℤ) ⧸ Γ => Pd_bound_tile g L L' hL hL' hbd (Quotient.out q)⁻¹
  refine Measure.integrableOn_of_bounded (M := ∑ q, M q)
    (volume_closedDomain_lt_top Γ).ne
    (continuous_Pd g L' hL').aestronglyMeasurable ?_
  refine ae_restrict_of_forall_mem (measurableSet_closedDomain Γ) fun τ hτ => ?_
  obtain ⟨q, hq⟩ := Set.mem_iUnion.mp hτ
  have hq' : Quotient.out q • τ ∈ ModularGroup.fd := by
    simpa only [Set.mem_smul_set_iff_inv_smul_mem, inv_inv] using hq
  have hτeq : τ = (Quotient.out q)⁻¹ • (Quotient.out q • τ) := by rw [inv_smul_smul]
  rw [hτeq]
  refine (hM q _ hq').trans ?_
  exact Finset.single_le_sum (f := M) (fun q _ => hM0 q) (Finset.mem_univ q)

variable (hΓ : (-1 : SL(2, ℤ)) ∈ Γ)

include hL hL' hbd hΓ in

theorem lhs_unfold :
    ∫ τ in closedDomain Γ, Pd L' g τ =
      ∑ q : SL(2, ℤ) ⧸ Γ, ∫ z in SourceModularGreen.D, Hd L' g (Quotient.out q)⁻¹ z := by
  rw [integral_closedDomain_eq_sum Γ hΓ _
    (integrableOn_Pd g L L' hL hL' hbd)]
  refine Finset.sum_congr rfl fun q _ => ?_
  set σ : SL(2, ℤ) := (Quotient.out q)⁻¹
  calc ∫ τ in ModularGroup.fd, Pd L' g (σ • τ)
      = ∫ τ in ModularGroup.fd, Hd L' g σ τ * ((τ.im : ℝ) : ℂ) ^ 2 := by
        refine setIntegral_congr_fun measurableSet_fd fun τ _ => ?_
        rw [Pd_smul]
    _ = ∫ z in SourceModularGreen.D, Hd L' g σ (ofComplex z) := setIntegral_fd_mul_im_sq _
    _ = ∫ z in SourceModularGreen.D, Hd L' g σ z := by
        refine setIntegral_congr_fun measurableSet_fdC fun z hz => ?_
        rw [coe_ofComplex hz.2.2]


end
end Dubon2026.SourceModularGreenPairing
