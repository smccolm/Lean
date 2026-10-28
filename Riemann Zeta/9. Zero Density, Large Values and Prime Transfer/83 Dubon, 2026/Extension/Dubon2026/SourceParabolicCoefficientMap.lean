import Dubon2026.SourceParabolicCohomology
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Functoriality

/-! DUB17/18 -> original parabolic character -> original analytic
period-class entry. Native coefficient morphisms preserve the literal
local coboundaries. This isolates the coefficient-functor identity
before instantiating the original dual-to-homogeneous period isomorphism. -/
namespace Dubon2026
noncomputable section
open CategoryTheory groupCohomology
open scoped MatrixGroups
variable {R : Type} [CommRing R] (Γ : Subgroup SL(2, ℤ))
  (A B : Rep R Γ) (φ : A ⟶ B)

theorem sourceParabolicCocycles_coefficientMap
    {c : cocycles₁ A} (hc : c ∈ sourceParabolicCocycles Γ A) :
    mapCocycles₁ (A := A) (B := B) (MonoidHom.id Γ) φ c ∈
      sourceParabolicCocycles Γ B := by
  intro γ hγ
  obtain ⟨v, hv⟩ := hc γ hγ
  refine ⟨φ.hom v, ?_⟩
  change φ.hom (c γ) = B.ρ γ (φ.hom v) - φ.hom v
  rw [hv, map_sub, Rep.hom_comm_apply]

end
end Dubon2026
