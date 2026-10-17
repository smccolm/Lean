import Dubon2026.OriginalCoinducedPointCoordinates

/-! # Actual internal-Hom coordinates for the coinduced coefficient

These mutually inverse linear maps untwist the original internal Hom
into coinduced linear-valued functions. They are the concrete maps
required for mod-p internal-Hom vanishing on DUB-17's projectivity route.
-/
namespace Dubon2026
noncomputable section
open CategoryTheory

variable {k G : Type} [CommRing k] [Group G] [Fintype G] (D R : Rep.{0} k G)

/-- Original pointwise linear maps, with trivial action before coinduction. -/
abbrev originalInternalHomPointRep : Rep k G := Rep.trivial k G (D →ₗ[k] R)

/-- The actual internal-Hom map expressed on original point functions and untwisted by the target action. -/
def originalCoinducedInternalHomForward :
    (originalCoinducedFunctionRep D →ₗ[k] R) →ₗ[k]
      originalCoinducedFunctionRep (originalInternalHomPointRep D R) where
  toFun φ := originalCoinducedFunction _
    (fun g => R.ρ g ∘ₗ φ ∘ₗ originalCoinducedPointAt D g)
  map_add' φ ψ := by
    apply Subtype.ext
    funext g
    apply LinearMap.ext
    intro d
    exact (R.ρ g).map_add _ _
  map_smul' r φ := by
    apply Subtype.ext
    funext g
    apply LinearMap.ext
    intro d
    exact (R.ρ g).map_smul r _

/-- The literal inverse reconstruction, a finite sum using original evaluations and inverse target actions. -/
def originalCoinducedInternalHomBackward :
    originalCoinducedFunctionRep (originalInternalHomPointRep D R) →ₗ[k]
      (originalCoinducedFunctionRep D →ₗ[k] R) where
  toFun F := ∑ g : G, R.ρ g⁻¹ ∘ₗ F.val g ∘ₗ originalCoinducedEvaluation D g
  map_add' F H := by
    apply LinearMap.ext
    intro x
    simp only [LinearMap.sum_apply, LinearMap.comp_apply, Submodule.coe_add,
      Pi.add_apply, LinearMap.add_apply, map_add, Finset.sum_add_distrib]
  map_smul' r F := by
    apply LinearMap.ext
    intro x
    simp only [LinearMap.sum_apply, LinearMap.comp_apply, Submodule.coe_smul,
      Pi.smul_apply, LinearMap.smul_apply, map_smul, Finset.smul_sum, RingHom.id_apply]

/-- The actual inverse reconstruction evaluates a literal point function in its single matching coordinate. -/
theorem originalCoinducedInternalHomBackward_point
    (F : originalCoinducedFunctionRep (originalInternalHomPointRep D R)) (g : G) (d : D) :
    originalCoinducedInternalHomBackward D R F (originalCoinducedPointAt D g d) =
      R.ρ g⁻¹ (F.val g d) := by
  classical
  change (∑ h : G, R.ρ h⁻¹ ∘ₗ F.val h ∘ₗ originalCoinducedEvaluation D h) _ = _
  rw [LinearMap.sum_apply, Finset.sum_eq_single g]
  · change R.ρ g⁻¹ (F.val g ((originalCoinducedPointAt D g d).val g)) = _
    rw [originalCoinducedPointAt_apply, if_pos rfl]
  · intro h _ hh
    change R.ρ h⁻¹ (F.val h ((originalCoinducedPointAt D g d).val h)) = 0
    rw [originalCoinducedPointAt_apply, if_neg hh, map_zero, map_zero]
  · simp

end
end Dubon2026
