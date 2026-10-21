import Mathlib.RepresentationTheory.Homological.GroupCohomology.LowDegree
import Mathlib.LinearAlgebra.Isomorphisms

/-! Change of coefficients on native first cohomology.
DUB-17/18 -> residual modular Galois association -> integral-to-residual
binary H1 eigensystem. The actual coefficient map induces a semilinear
map on cocycles and descends through the native cocycle quotient.
This constructs the required change-of-coefficients map; its injectivity
after tensor extension is a separate obligation.
-/

namespace Dubon2026
noncomputable section

variable {R S G : Type} [CommRing R] [CommRing S] [Group G]
    (A : Rep R G) (B : Rep S G) (φ : R →+* S) (L : A →ₛₗ[φ] B)
    (hL : ∀ (g : G) (x : A), L (A.ρ g x) = B.ρ g (L x))

/-- An actual semilinear equivariant coefficient map acts on native one-cocycles. -/
def sourceSemilinearCocycles :
    groupCohomology.cocycles₁ A →ₛₗ[φ] groupCohomology.cocycles₁ B where
  toFun c := ⟨fun g => L (c g), (groupCohomology.mem_cocycles₁_iff _).mpr (by
    intro g h
    rw [(groupCohomology.mem_cocycles₁_iff c).mp c.property, map_add, hL])⟩
  map_add' c d := by
    apply groupCohomology.cocycles₁_ext
    intro g
    exact map_add L (c g) (d g)
  map_smul' r c := by
    apply groupCohomology.cocycles₁_ext
    intro g
    exact L.map_smulₛₗ r (c g)

/-- Coefficient change on cocycles is literally pointwise coefficient change. -/
theorem sourceSemilinearCocycles_apply (c : groupCohomology.cocycles₁ A) (g : G) :
    sourceSemilinearCocycles A B φ L hL c g = L (c g) := rfl

private def semilinearQuotient :
    (groupCohomology.cocycles₁ A ⧸ LinearMap.ker (groupCohomology.H1π A).hom)
      →ₛₗ[φ] groupCohomology.H1 B :=
  (LinearMap.ker (groupCohomology.H1π A).hom).liftQ
    ((groupCohomology.H1π B).hom.comp (sourceSemilinearCocycles A B φ L hL)) (by
      intro c hc
      obtain ⟨v, hv⟩ := (groupCohomology.H1π_eq_zero_iff c).mp hc
      apply (groupCohomology.H1π_eq_zero_iff _).mpr
      refine ⟨L v, ?_⟩
      funext g
      change B.ρ g (L v) - L v = L (c g)
      rw [← hL, ← map_sub]
      exact congrArg L (congrFun hv g))

/-- The actual semilinear coefficient map descends to the full native H1. -/
def sourceSemilinearH1 : groupCohomology.H1 A →ₛₗ[φ] groupCohomology.H1 B :=
  (semilinearQuotient A B φ L hL).comp
    ((groupCohomology.H1π A).hom.quotKerEquivOfSurjective
      ((ModuleCat.epi_iff_surjective _).mp inferInstance)).symm.toLinearMap

/-- The descended coefficient map has the actual pointwise-transformed cocycle representative. -/
theorem sourceSemilinearH1_cocycle (c : groupCohomology.cocycles₁ A) :
    sourceSemilinearH1 A B φ L hL (groupCohomology.H1π A c) =
      groupCohomology.H1π B (sourceSemilinearCocycles A B φ L hL c) := by
  change semilinearQuotient A B φ L hL
    (((groupCohomology.H1π A).hom.quotKerEquivOfSurjective
      ((ModuleCat.epi_iff_surjective _).mp inferInstance)).symm
        ((groupCohomology.H1π A).hom c)) = _
  rw [LinearMap.quotKerEquivOfSurjective_symm_apply]
  rfl

end
end Dubon2026
