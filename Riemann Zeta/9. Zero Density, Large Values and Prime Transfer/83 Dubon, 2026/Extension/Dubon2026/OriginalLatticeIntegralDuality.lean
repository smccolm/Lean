import Dubon2026.OriginalIntegralCharacterDuality
import Mathlib.LinearAlgebra.Dual.Lemmas

/-! # Original finite-lattice degree-two duality

Pinned finite-projective biduality identifies the original lattice
with its double integral dual, including the original group action.
The character connecting map then pairs its actual H2 with H1 of its
integral dual. This is the precise integral pairing needed before
DUB-17's remaining class-coefficient norm-quotient comparison.
-/
namespace Dubon2026
noncomputable section
open CategoryTheory
attribute [local instance 1100] Rep.hV2

/-- The original finite projective coefficient is equivariantly identified with its literal double dual. -/
def originalLinearBidualIso {k G : Type} [CommRing k] [Group G]
    (M : Rep.{0} k G) [Module.Finite k M] [Module.Projective k M] :
    M ≅ originalLinearCharacterRep k (originalLinearCharacterRep k M) :=
  Rep.mkIso {
    toLinearEquiv := Module.evalEquiv k M
    isIntertwining' := fun g => by
      apply LinearMap.ext
      intro x
      apply LinearMap.ext
      intro φ
      change M →ₗ[k] k at φ
      change φ (M.ρ g x) = φ (M.ρ g⁻¹⁻¹ x)
      rw [inv_inv] }

/-- The bidual comparison is the literal evaluation map on the original coefficient. -/
theorem originalLinearBidualIso_toLinearMap {k G : Type} [CommRing k] [Group G]
    (M : Rep.{0} k G) [Module.Finite k M] [Module.Projective k M] :
    (originalLinearBidualIso M).hom.hom.toLinearMap = Module.Dual.eval k M := rfl

variable {G : Type} [Group G] (M : Rep.{0} ℤ G)
variable [Module.Finite ℤ M] [Module.Projective ℤ M]

/-- The integral dual of the original finite projective lattice is projective over the integers. -/
theorem originalIntegralDual_projective :
    Module.Projective ℤ (originalLinearCharacterRep ℤ M) :=
  inferInstanceAs (Module.Projective ℤ (Module.Dual ℤ M))

variable [Fintype G]

/-- Actual H2 of the original finite lattice is the rational-circle character module of H1 of its integral dual. -/
def originalLatticeIntegralDuality :
    groupCohomology M 2 ≃ₗ[ℤ]
      (groupHomology (originalLinearCharacterRep ℤ M) 1 →ₗ[ℤ] AddCircle (1 : ℚ)) := by
  letI := originalIntegralDual_projective M
  exact ((groupCohomology.functor ℤ G 2).mapIso (originalLinearBidualIso M)).toLinearEquiv.trans
    (originalIntegralCharacterDuality (originalLinearCharacterRep ℤ M))

/-- The actual lattice pairing detects zero in the original lattice H2. -/
theorem originalLatticeIntegralDuality_left_nondegenerate (x : groupCohomology M 2)
    (hx : ∀ y, originalLatticeIntegralDuality M x y = 0) : x = 0 := by
  apply (originalLatticeIntegralDuality M).injective
  rw [map_zero]
  exact LinearMap.ext hx

/-- The actual lattice pairing detects zero in first homology of the original integral dual. -/
theorem originalLatticeIntegralDuality_right_nondegenerate
    (y : groupHomology (originalLinearCharacterRep ℤ M) 1)
    (hy : ∀ x, originalLatticeIntegralDuality M x y = 0) : y = 0 := by
  letI := originalIntegralDual_projective M
  apply originalIntegralCharacterDuality_right_nondegenerate (originalLinearCharacterRep ℤ M) y
  intro c
  let e := ((groupCohomology.functor ℤ G 2).mapIso (originalLinearBidualIso M)).toLinearEquiv
  obtain ⟨x, hx⟩ := e.surjective c
  have he := hy x
  change originalIntegralCharacterDuality (originalLinearCharacterRep ℤ M) (e x) y = 0 at he
  rw [hx] at he
  exact he

end
end Dubon2026
