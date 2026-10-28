import Dubon2026.SourceGammaOnePeterssonSmoothLimit

/-! DUB-17/18 -> original Gamma1 Picard/H1 -> principal-divisor converse ->
integral Petersson duality. Nondegeneracy on the actual closed coset domain
follows from positivity on one open tile and native holomorphic continuation.
Reuse the proved integrability and central-sign extension; no Riesz theorem,
new inner-product instance or fundamental-domain identification is required. -/
namespace Dubon2026.SourcePeterssonClosed
noncomputable section
open UpperHalfPlane ModularGroup MeasureTheory Filter Set
open SourceSmoothedUnfolding SourceFunctionField.GammaOne
open scoped MatrixGroups Topology Pointwise ComplexConjugate
variable {Γ : Subgroup SL(2, ℤ)} [Γ.FiniteIndex]
local notation "V" => CuspForm (Γ.map (Matrix.SpecialLinearGroup.mapGL ℝ)) 2

theorem self_re (f : ℍ → ℂ) (τ : ℍ) :
    (petersson 2 f f τ).re = Complex.normSq (f τ) * τ.im ^ 2 := by
  simp only [petersson, ← Complex.normSq_eq_conj_mul_self, zpow_ofNat,
    ← Complex.ofReal_pow, ← Complex.ofReal_mul, Complex.ofReal_re]

theorem eq_zero_of_self_integral_eq_zero (f : V)
    (hpet : (∫ τ in closedDomain Γ, petersson 2 f f τ) = 0) : f = 0 := by
  let R : ℍ → ℝ := fun τ => (petersson 2 f f τ).re
  have hi := sourceCusp_petersson_integrable_closedDomain Γ f f
  have hR0 : (∫ τ in closedDomain Γ, R τ) = 0 := by
    trans Complex.re (∫ τ in closedDomain Γ, petersson 2 f f τ)
    · exact integral_re hi
    · rw [hpet]; rfl
  have hiR : IntegrableOn R (closedDomain Γ) := hi.re
  have hRae : R =ᶠ[ae (volume.restrict (closedDomain Γ))] 0 := by
    apply (integral_eq_zero_iff_of_nonneg_ae
      (ae_of_all _ fun τ => show 0 ≤ R τ from by
        change 0 ≤ (petersson 2 f f τ).re
        rw [self_re]
        exact mul_nonneg (Complex.normSq_nonneg _) (sq_nonneg _)) hiR).mp
    exact hR0
  have hRc : Continuous R :=
    Complex.continuous_re.comp (petersson_continuous 2
      (ModularFormClass.continuous f) (ModularFormClass.continuous f))
  let q : SL(2, ℤ) ⧸ Γ := ((1 : SL(2, ℤ)) : SL(2, ℤ) ⧸ Γ)
  let U : Set ℍ := (Quotient.out q)⁻¹ • (fdo : Set ℍ)
  have hU : IsOpen U := isOpen_fdo.smul _
  have hsub : U ⊆ closedDomain Γ := by
    intro z hz
    obtain ⟨w, hw, rfl⟩ := Set.mem_smul_set.mp hz
    exact Set.mem_iUnion.mpr ⟨q, Set.mem_smul_set.mpr ⟨w, fdo_subset_fd hw, rfl⟩⟩
  have hRU : EqOn R 0 U := Measure.eqOn_open_of_ae_eq
    (hRae.filter_mono (ae_mono (Measure.restrict_mono hsub le_rfl)))
    hU hRc.continuousOn continuousOn_const
  have hfU : ∀ τ ∈ U, f τ = 0 := by
    intro τ hτ
    have he := hRU hτ
    change (petersson 2 f f τ).re = 0 at he
    rw [self_re] at he
    exact Complex.normSq_eq_zero.mp
      ((mul_eq_zero.mp he).resolve_right (pow_ne_zero 2 τ.im_pos.ne'))
  let τ₀ : ℍ := ⟨⟨0, 2⟩, by norm_num⟩
  have hτ₀ : τ₀ ∈ fdo := by
    refine ⟨by norm_num [Complex.normSq_apply], ?_⟩
    change |(τ₀ : ℂ).re| < 1 / 2
    norm_num
  have hp : (Quotient.out q)⁻¹ • τ₀ ∈ U :=
    Set.mem_smul_set.mpr ⟨τ₀, hτ₀, rfl⟩
  have hev := Filter.eventually_of_mem (hU.mem_nhds hp) hfU
  have he := UpperHalfPlane.eq_zero_of_frequently (CuspFormClass.holo f)
    (hev.filter_mono nhdsWithin_le_nhds).frequently
  ext τ
  exact congr_fun he τ

theorem eq_zero_of_signed_self_integral_eq_zero (f : V)
    (hpet : (∫ τ in closedDomain (plusMinus Γ), petersson 2 f f τ) = 0) : f = 0 := by
  have he : SignedForms.extend Γ f = 0 :=
    eq_zero_of_self_integral_eq_zero (SignedForms.extend Γ f) hpet
  apply SignedForms.extend_injective Γ
  simpa only [map_zero] using he

theorem eq_of_signed_petersson_eq (k f : V)
    (he : ∀ g : V, (∫ τ in closedDomain (plusMinus Γ), petersson 2 k g τ) =
      ∫ τ in closedDomain (plusMinus Γ), petersson 2 f g τ) : k = f := by
  apply sub_eq_zero.mp
  apply eq_zero_of_signed_self_integral_eq_zero
  have hsub : (fun τ : ℍ => petersson 2 (k - f : V) (k - f : V) τ) =
      fun τ : ℍ => petersson 2 k (k - f : V) τ - petersson 2 f (k - f : V) τ := by
    funext τ
    simp only [petersson, CuspForm.coe_sub, Pi.sub_apply, map_sub, sub_mul]
  have hi1 : IntegrableOn (petersson 2 k (k - f : V)) (closedDomain (plusMinus Γ)) :=
    sourceCusp_petersson_integrable_closedDomain (plusMinus Γ)
      (SignedForms.extend Γ k) (SignedForms.extend Γ (k - f : V))
  have hi2 : IntegrableOn (petersson 2 f (k - f : V)) (closedDomain (plusMinus Γ)) :=
    sourceCusp_petersson_integrable_closedDomain (plusMinus Γ)
      (SignedForms.extend Γ f) (SignedForms.extend Γ (k - f : V))
  rw [hsub, integral_sub hi1 hi2, he, sub_self]

end
end Dubon2026.SourcePeterssonClosed
