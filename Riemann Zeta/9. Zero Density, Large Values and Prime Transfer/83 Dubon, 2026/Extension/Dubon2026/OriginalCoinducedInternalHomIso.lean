import Dubon2026.OriginalCoinducedInternalHomMaps

/-! # The actual internal Hom from coinduction is coinduced

The original point-coordinate maps are inverse and intertwine the
actual internal-Hom action. This exact isomorphism supplies mod-p
internal-Hom vanishing on DUB-17's integral projectivity route. It
adapts the inspected upstream untwisting argument to the existing
original function model, without a separate induced tensor model.
-/
namespace Dubon2026
noncomputable section
open CategoryTheory

variable {k G : Type} [CommRing k] [Group G] [Fintype G] (D R : Rep.{0} k G)

/-- Actual point-coordinate reconstruction recovers every original linear map. -/
theorem originalCoinducedInternalHom_backward_forward
    (φ : originalCoinducedFunctionRep D →ₗ[k] R) :
    originalCoinducedInternalHomBackward D R (originalCoinducedInternalHomForward D R φ) = φ := by
  apply LinearMap.ext
  intro x
  change (∑ g : G, R.ρ g⁻¹ ∘ₗ (R.ρ g ∘ₗ φ ∘ₗ originalCoinducedPointAt D g) ∘ₗ
    originalCoinducedEvaluation D g) x = φ x
  simp only [LinearMap.sum_apply, LinearMap.comp_apply]
  change (∑ g : G, R.ρ g⁻¹ (R.ρ g (φ (originalCoinducedPointAt D g (x.val g))))) = φ x
  simp only [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
  rw [← map_sum]
  exact congrArg φ (originalCoinduced_point_sum D x).symm

/-- The original forward map recovers every coinduced linear-valued function. -/
theorem originalCoinducedInternalHom_forward_backward
    (F : originalCoinducedFunctionRep (originalInternalHomPointRep D R)) :
    originalCoinducedInternalHomForward D R (originalCoinducedInternalHomBackward D R F) = F := by
  apply Subtype.ext
  funext g
  apply LinearMap.ext
  intro d
  change R.ρ g (originalCoinducedInternalHomBackward D R F (originalCoinducedPointAt D g d)) = F.val g d
  rw [originalCoinducedInternalHomBackward_point, ← Module.End.mul_apply, ← map_mul,
    mul_inv_cancel, map_one, Module.End.one_apply]

/-- The literal original internal-Hom representation from coinduction is isomorphic to actual coinduced linear-valued functions. -/
def originalCoinducedInternalHomIso :
    (Rep.ihom (originalCoinducedFunctionRep D)).obj R ≅
      originalCoinducedFunctionRep (originalInternalHomPointRep D R) :=
  Rep.mkIso {
    toFun := originalCoinducedInternalHomForward D R
    invFun := originalCoinducedInternalHomBackward D R
    left_inv := originalCoinducedInternalHom_backward_forward D R
    right_inv := originalCoinducedInternalHom_forward_backward D R
    map_add' := (originalCoinducedInternalHomForward D R).map_add
    map_smul' := (originalCoinducedInternalHomForward D R).map_smul
    isIntertwining' := fun h => by
      apply LinearMap.ext
      intro φ
      apply Subtype.ext
      funext g
      apply LinearMap.ext
      intro d
      change R.ρ g (R.ρ h (φ ((originalCoinducedFunctionRep D).ρ h⁻¹
        (originalCoinducedPointAt D g d)))) = R.ρ (g * h) (φ (originalCoinducedPointAt D (g * h) d))
      rw [originalCoinducedPointAt_action, inv_inv, ← Module.End.mul_apply, ← map_mul] }

/-- Positive cohomology of the actual internal Hom from an original coinduced coefficient vanishes. -/
theorem originalCoinducedInternalHom_positive_zero (n : ℕ) :
    Limits.IsZero (groupCohomology ((Rep.ihom (originalCoinducedFunctionRep D)).obj R) (n + 1)) :=
  (originalCoinducedFunction_positive_zero (originalInternalHomPointRep D R) n).of_iso
    ((groupCohomology.functor k G (n + 1)).mapIso (originalCoinducedInternalHomIso D R))

end
end Dubon2026
