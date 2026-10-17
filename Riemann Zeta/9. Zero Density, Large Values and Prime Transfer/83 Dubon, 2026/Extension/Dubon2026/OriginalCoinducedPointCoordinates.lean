import Dubon2026.OriginalCoinducedNormKernel

/-! # Literal point coordinates for original coinduced internal Hom

These original point functions and evaluations give the exact coordinate
isomorphism for internal Hom from coinduction, needed for the mod-p
internal-Hom vanishing on DUB-17's integral projectivity route.
-/
namespace Dubon2026
noncomputable section
open CategoryTheory

variable {k G : Type} [CommRing k] [Group G] (D : Rep.{0} k G)

/-- The original coefficient supported at the specified group element. -/
def originalCoinducedPointAt (g : G) : D →ₗ[k] originalCoinducedFunctionRep D :=
  (originalCoinducedFunctionRep D).ρ g⁻¹ ∘ₗ originalCoinducedPoint D

/-- Literal evaluation of an original coinduced function. -/
def originalCoinducedEvaluation (g : G) : originalCoinducedFunctionRep D →ₗ[k] D :=
  LinearMap.proj g ∘ₗ (Representation.coindV (⊥ : Subgroup G).subtype
    (Rep.res (⊥ : Subgroup G).subtype D).ρ).subtype

/-- Original point coordinates have exactly the indicated one-point support. -/
theorem originalCoinducedPointAt_apply [DecidableEq G] (g h : G) (d : D) :
    (originalCoinducedPointAt D g d).val h = if h = g then d else 0 := by
  classical
  simp [originalCoinducedPointAt, originalCoinducedPoint,
    originalCoinducedFunction, mul_inv_eq_one]

/-- The original action translates literal point coordinates by the inverse group element. -/
theorem originalCoinducedPointAt_action (h g : G) (d : D) :
    (originalCoinducedFunctionRep D).ρ h (originalCoinducedPointAt D g d) =
      originalCoinducedPointAt D (g * h⁻¹) d := by
  change (originalCoinducedFunctionRep D).ρ h
    ((originalCoinducedFunctionRep D).ρ g⁻¹ (originalCoinducedPoint D d)) = _
  simp only [← Module.End.mul_apply, ← map_mul, originalCoinducedPointAt,
    mul_inv_rev, inv_inv, LinearMap.comp_apply]

end
end Dubon2026
