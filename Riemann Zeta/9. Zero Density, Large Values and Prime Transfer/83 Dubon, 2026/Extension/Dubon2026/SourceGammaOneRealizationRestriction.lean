import Dubon2026.SourceGammaOneAnalyticPlaceInvariance
import Mathlib.Topology.Homeomorph.Lemmas

/-! DUB-17/18 -> original Gamma1 Frobenius norm -> adjacent-j
nonmembership. Restrict the proved equal-weight modular quotient to the
actual intersection subgroup. Continuous analytic representatives inherit
the original field's invariance through the already proved quotient germs;
no field-identification or invariance certificate is supplied separately. -/
namespace Dubon2026.SourceFunctionField.GammaOne
noncomputable section
open UpperHalfPlane Filter Matrix.SpecialLinearGroup
open scoped MatrixGroups Topology

theorem realize_restrict_eventuallyEq {Γ Δ : Subgroup SL(2, ℤ)}
    (h : Δ ≤ Γ) (hT : ModularGroup.T ∈ Δ)
    (x : functionFieldOver Γ ℂ) (τ : ℍ) :
    (fun z : ℂ => realize Δ (x : LaurentSeries ℂ) (ofComplex z))
      =ᶠ[𝓝[≠] (τ : ℂ)] fun z => realize Γ (x : LaurentSeries ℂ) (ofComplex z) := by
  obtain ⟨k, g, f, hf, hx⟩ := functionFieldOver_modular_ratio (h hT) x
  let g' := ModularNormPolynomial.restrict (Subgroup.map_mono h) g
  let f' := ModularNormPolynomial.restrict (Subgroup.map_mono h) f
  have hf' : f' ≠ 0 := by
    intro hz
    apply hf
    ext z
    exact congrArg (fun a => a z) hz
  have hx' : (x : LaurentSeries ℂ) * ModularRatios.qL f' = ModularRatios.qL g' := hx
  filter_upwards [realize_eventuallyEq_of_ratio hT g' f' x hf' hx' τ,
    realize_eventuallyEq_of_ratio (h hT) g f x hf hx τ] with z he he'
  rw [he, he']
  rfl

theorem continuous_invariant_of_realize_germs {Γ : Subgroup SL(2, ℤ)}
    (hT : ModularGroup.T ∈ Γ) (x : functionFieldOver Γ ℂ)
    (G : ℍ → ℂ) (hG : Continuous G)
    (he : ∀ τ : ℍ, (G ∘ ofComplex) =ᶠ[𝓝[≠] (τ : ℂ)]
      fun z => realize Γ (x : LaurentSeries ℂ) (ofComplex z)) :
    ∀ γ ∈ Γ, ∀ τ : ℍ, G (γ • τ) = G τ := by
  have heH (τ : ℍ) : G =ᶠ[𝓝[≠] τ] realize Γ (x : LaurentSeries ℂ) :=
    SourceFunctionField.ModularRatios.eventually_nhdsNE_coe_iff.mp (he τ)
  intro γ hγ τ
  have ht : Tendsto (fun w : ℍ => γ • w) (𝓝[≠] τ) (𝓝[≠] (γ • τ)) :=
    le_of_eq ((Homeomorph.smul (γ : GL (Fin 2) ℝ)).map_punctured_nhds_eq τ)
  have hi : (fun w : ℍ => realize Γ (x : LaurentSeries ℂ) (γ • w))
      =ᶠ[𝓝[≠] τ] realize Γ (x : LaurentSeries ℂ) :=
    SourceFunctionField.ModularRatios.eventually_nhdsNE_coe_iff.mp
      (realize_smul_eventuallyEq hT x ⟨γ, hγ⟩ τ)
  have hev : (fun w : ℍ => G (γ • w)) =ᶠ[𝓝[≠] τ] G := by
    filter_upwards [(heH (γ • τ)).comp_tendsto ht, hi, heH τ] with w hw hiw hw'
    exact hw.trans (hiw.trans hw'.symm)
  exact tendsto_nhds_unique_of_eventuallyEq
    ((hG.comp (Homeomorph.smul (γ : GL (Fin 2) ℝ)).continuous).continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
    (hG.continuousAt.tendsto.mono_left nhdsWithin_le_nhds) hev

end
end Dubon2026.SourceFunctionField.GammaOne
