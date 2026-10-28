import Dubon2026.SourceGammaOneHeckeDegeneracy
import Dubon2026.SourceGammaOneMeromorphicRealization

/-! DUB17/18 -> all-weight arithmetic association -> actual Gamma1
Picard/Hecke comparison -> analytic degeneracy maps. Restrict the proved
equal-weight modular ratio to the literal correspondence subgroup.
Its unchanged q-expansion identifies the alpha germ at the same point.
This avoids a new generator theorem for the Gamma1 field. -/
namespace Dubon2026.SourceFunctionField.GammaOne
noncomputable section
open UpperHalfPlane Filter CongruenceSubgroup Matrix.SpecialLinearGroup
open scoped MatrixGroups Topology

theorem realize_heckeAlpha_eventuallyEq (M d : ℕ)
    (hT : ModularGroup.T ∈ Gamma1 M)
    (hH : ModularGroup.T ∈ Gamma1 M ⊓ Gamma0 (d * M))
    (x : functionFieldOver (Gamma1 M) ℂ) (τ : ℍ) :
    (fun z : ℂ => realize (Gamma1 M ⊓ Gamma0 (d * M))
      (heckeAlpha ℂ M d x : LaurentSeries ℂ) (ofComplex z))
      =ᶠ[𝓝[≠] (τ : ℂ)]
        fun z => realize (Gamma1 M) (x : LaurentSeries ℂ) (ofComplex z) := by
  obtain ⟨k, g, h, hh, hx⟩ := functionFieldOver_modular_ratio hT x
  let hg : (Gamma1 M ⊓ Gamma0 (d * M)).map (mapGL ℝ) ≤
      (Gamma1 M).map (mapGL ℝ) := Subgroup.map_mono inf_le_left
  let g' := ModularNormPolynomial.restrict hg g
  let h' := ModularNormPolynomial.restrict hg h
  have hh' : h' ≠ 0 := by
    intro hz
    apply hh
    ext z
    exact congrArg (fun f => f z) hz
  have hx' : (heckeAlpha ℂ M d x : LaurentSeries ℂ) *
      ModularRatios.qL h' = ModularRatios.qL g' := hx
  filter_upwards [realize_eventuallyEq_of_ratio hH g' h' _ hh' hx' τ,
    realize_eventuallyEq_of_ratio hT g h x hh hx τ] with z he hf
  rw [he, hf]
  rfl

end
end Dubon2026.SourceFunctionField.GammaOne
