import Dubon2026.SourceInvariantRealPart
import Dubon2026.SourceReflectedPrimitive
import Dubon2026.SourceSL2Reflection

/-! DUB-17/18 -> residual Galois association -> parabolic Hecke realization
-> period-pair injectivity. An invariant difference of the original
holomorphic primitive and a reflected holomorphic primitive has zero
holomorphic derivative. The two real-part constancy applications follow
anthropics/fermats-last-theorem, commit
6e837e75355538c7f80bab5b956861e86c4eacc2,
P2M/Sol/S_ModularCurve_periodHomPair_injective.lean (Apache 2.0).
Their zero derivatives directly extract vanishing, avoiding a separate
mixed real-linear derivative comparison.
-/
namespace Dubon2026
noncomputable section
open UpperHalfPlane Complex Filter CongruenceSubgroup
open scoped MatrixGroups Topology ComplexConjugate

/-- The actual mixed primitive invariance and finite limits at all original
cusps force the holomorphic integrand to vanish. -/
theorem sourceMixedPrimitive_derivative_zero {N : ℕ} [NeZero N]
    {f g F G : ℍ → ℂ}
    (hF : ∀ τ : ℍ, HasDerivAt (F ∘ ofComplex) (f τ) (τ : ℂ))
    (hG : ∀ τ : ℍ, HasDerivAt (G ∘ ofComplex) (g τ) (τ : ℂ))
    (hFlim : ∀ δ : SL(2, ℤ), ∃ L : ℂ,
      Tendsto (fun w : ℍ => F (δ • w)) atImInfty (𝓝 L))
    (hGlim : ∀ δ : SL(2, ℤ), ∃ L : ℂ,
      Tendsto (fun w : ℍ => G (δ • w)) atImInfty (𝓝 L))
    (hinv : ∀ γ : Gamma0 N, ∀ z : ℍ,
      F (γ.val • z) - G (J • (γ.val • z)) = F z - G (J • z))
    (τ : ℍ) : f τ = 0 := by
  let K : ℍ → ℂ := fun z => conj (G (J • z))
  have hK (z : ℍ) : HasDerivAt (K ∘ ofComplex) (-conj (g (J • z))) (z : ℂ) :=
    sourceReflectedPrimitive_hasDerivAt hG z
  have hKlim (δ : SL(2, ℤ)) : ∃ L : ℂ,
      Tendsto (fun w : ℍ => K (δ • w)) atImInfty (𝓝 L) := by
    obtain ⟨L, hL⟩ := hGlim (sourceJConjugateSL δ)
    refine ⟨conj L, ?_⟩
    simpa only [K, sourceJ_smul_SL, Function.comp_def] using
      (Complex.continuous_conj.tendsto L).comp (hL.comp sourceReflectedPrimitive_tendsto)
  let φ : ℍ → ℂ := fun z => F z - K z
  let χ : ℍ → ℂ := fun z => -Complex.I * (F z + K z)
  have hφ (z : ℍ) : HasDerivAt (φ ∘ ofComplex)
      (f z + conj (g (J • z))) (z : ℂ) := by
    simpa only [φ, Function.comp_def, sub_neg_eq_add] using (hF z).sub (hK z)
  have hχ (z : ℍ) : HasDerivAt (χ ∘ ofComplex)
      (-Complex.I * (f z - conj (g (J • z)))) (z : ℂ) := by
    simpa only [χ, Function.comp_def, sub_eq_add_neg] using
      ((hF z).add (hK z)).const_mul (-Complex.I)
  have hφre (z : ℍ) : (φ z).re = (F z - G (J • z)).re := by
    simp only [φ, K, Complex.sub_re, Complex.conj_re]
  have hχre (z : ℍ) : (χ z).re = (F z - G (J • z)).im := by
    simp only [χ, K, Complex.neg_re, Complex.mul_re, Complex.neg_im,
      Complex.I_re, Complex.I_im, Complex.add_re, Complex.add_im,
      Complex.conj_re, Complex.conj_im, Complex.sub_im]
    ring
  have hφinv (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 N) (z : ℍ) :
      (φ (γ • z)).re = (φ z).re := by
    rw [hφre, hφre, hinv ⟨γ, hγ⟩ z]
  have hχinv (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 N) (z : ℍ) :
      (χ (γ • z)).re = (χ z).re := by
    rw [hχre, hχre, hinv ⟨γ, hγ⟩ z]
  have hφlim (δ : SL(2, ℤ)) : ∃ L : ℂ,
      Tendsto (fun w : ℍ => φ (δ • w)) atImInfty (𝓝 L) := by
    obtain ⟨L₁, h₁⟩ := hFlim δ
    obtain ⟨L₂, h₂⟩ := hKlim δ
    exact ⟨L₁ - L₂, h₁.sub h₂⟩
  have hχlim (δ : SL(2, ℤ)) : ∃ L : ℂ,
      Tendsto (fun w : ℍ => χ (δ • w)) atImInfty (𝓝 L) := by
    obtain ⟨L₁, h₁⟩ := hFlim δ
    obtain ⟨L₂, h₂⟩ := hKlim δ
    exact ⟨-Complex.I * (L₁ + L₂), (h₁.add h₂).const_mul (-Complex.I)⟩
  have hcφ := sourceGamma0_realPart_constant hφ hφinv hφlim
  have hcχ := sourceGamma0_realPart_constant hχ hχinv hχlim
  have hzφ : f τ + conj (g (J • τ)) = 0 := by
    apply sourceHolomorphic_re_zero_deriv ((hφ τ).sub_const (φ UpperHalfPlane.I))
    intro z
    simp only [Function.comp_apply, ofComplex_apply, Complex.sub_re,
      hcφ z UpperHalfPlane.I, sub_self]
  have hzχ : -Complex.I * (f τ - conj (g (J • τ))) = 0 := by
    apply sourceHolomorphic_re_zero_deriv ((hχ τ).sub_const (χ UpperHalfPlane.I))
    intro z
    simp only [Function.comp_apply, ofComplex_apply, Complex.sub_re,
      hcχ z UpperHalfPlane.I, sub_self]
  have hd : f τ - conj (g (J • τ)) = 0 :=
    (mul_eq_zero.mp hzχ).resolve_left (neg_ne_zero.mpr Complex.I_ne_zero)
  linear_combination (1 / 2 : ℂ) * hzφ + (1 / 2 : ℂ) * hd

end
end Dubon2026
