import Dubon2026.SourceGammaOneRationalAnalyticGerms

/-! DUB-17/18 -> original Gamma1 norm reduction -> exact diamond
identification. The actual field realization is faithful because it is a
unital homomorphism from a field into the nontrivial punctured germ ring.
This converts the proved analytic comparison into original field equality. -/
namespace Dubon2026.SourceFunctionField.GammaOne
noncomputable section
open UpperHalfPlane Filter
open scoped MatrixGroups Topology

theorem eq_of_realize_upperHalfPlane_eventuallyEq {Γ : Subgroup SL(2, ℤ)}
    (hT : ModularGroup.T ∈ Γ) (x y : functionFieldOver Γ ℂ) (τ : ℍ)
    (h : realize Γ (x : LaurentSeries ℂ) =ᶠ[𝓝[≠] τ] realize Γ (y : LaurentSeries ℂ)) :
    x = y := by
  apply (upperHalfPlaneRealizeGerm Γ hT τ).injective
  exact Germ.coe_eq.mpr h

end
end Dubon2026.SourceFunctionField.GammaOne
