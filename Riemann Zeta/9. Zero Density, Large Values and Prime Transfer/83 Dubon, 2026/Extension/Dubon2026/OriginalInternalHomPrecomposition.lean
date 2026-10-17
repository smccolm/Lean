import Dubon2026.OriginalInternalHomShortExact
import Mathlib.RepresentationTheory.Invariants

/-! # Actual internal-Hom precomposition

The two-shift route to DUB-17's converse norm criterion extends
original coefficient morphisms across the existing coinduced
embedding. The required contravariant maps are literal precomposition.
-/
namespace Dubon2026
noncomputable section
open CategoryTheory
variable {k G : Type} [CommRing k] [Group G]
variable {A B : Rep.{0} k G} (C : Rep.{0} k G)

/-- Precomposition on the original internal Hom is an equivariant coefficient map. -/
def originalInternalHomPrecomposition (f : A ⟶ B) :
    (Rep.ihom B).obj C ⟶ (Rep.ihom A).obj C :=
  Rep.ofHom ⟨LinearMap.lcomp k C f.hom.toLinearMap, fun g => by
    apply LinearMap.ext
    intro η
    apply LinearMap.ext
    intro a
    change C.ρ g (η (B.ρ g⁻¹ (f.hom a))) =
      C.ρ g (η (f.hom (A.ρ g⁻¹ a)))
    rw [Rep.hom_comm_apply]⟩

/-- The internal-Hom precomposition map applies the same original coefficient inclusion. -/
theorem originalInternalHomPrecomposition_apply (f : A ⟶ B)
    (η : B →ₗ[k] C) :
    (originalInternalHomPrecomposition C f).hom η = η.comp f.hom.toLinearMap := rfl

end
end Dubon2026
