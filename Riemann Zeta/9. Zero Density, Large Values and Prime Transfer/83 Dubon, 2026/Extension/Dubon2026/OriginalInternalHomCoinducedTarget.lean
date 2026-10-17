import Dubon2026.OriginalCoinducedInternalHomMaps
import Dubon2026.OriginalCoinducedDimensionShift

/-! # Internal Hom into original coinduction

Literal evaluation and inverse source action identify internal Hom into
the original coinduced coefficient with coinduced linear-valued functions.
This allows DUB-17's required lattice acyclicity to follow directly from
the actual projective presentation, avoiding a separate tensor model.
-/
namespace Dubon2026
noncomputable section
open CategoryTheory

variable {k G : Type} [CommRing k] [Group G] (M D : Rep.{0} k G)

/-- Untwist the actual internal-Hom source action in each original function coordinate. -/
def originalInternalHomCoinducedTargetForward :
    (M →ₗ[k] originalCoinducedFunctionRep D) →ₗ[k]
      originalCoinducedFunctionRep (originalInternalHomPointRep M D) where
  toFun φ := originalCoinducedFunction _
    (fun g => originalCoinducedEvaluation D g ∘ₗ φ ∘ₗ M.ρ g⁻¹)
  map_add' φ ψ := by
    apply Subtype.ext
    funext g
    apply LinearMap.ext
    intro m
    rfl
  map_smul' r φ := by
    apply Subtype.ext
    funext g
    apply LinearMap.ext
    intro m
    rfl

/-- Reconstruct the original linear map by the source action in every actual function coordinate. -/
def originalInternalHomCoinducedTargetBackward :
    originalCoinducedFunctionRep (originalInternalHomPointRep M D) →ₗ[k]
      (M →ₗ[k] originalCoinducedFunctionRep D) where
  toFun F := {
    toFun := fun m => originalCoinducedFunction D (fun g => F.val g (M.ρ g m))
    map_add' := fun x y => by
      apply Subtype.ext
      funext g
      exact (congrArg (F.val g) ((M.ρ g).map_add x y)).trans ((F.val g).map_add _ _)
    map_smul' := fun r m => by
      apply Subtype.ext
      funext g
      exact (congrArg (F.val g) ((M.ρ g).map_smul r m)).trans ((F.val g).map_smul r _) }
  map_add' F H := by
    apply LinearMap.ext
    intro m
    rfl
  map_smul' r F := by
    apply LinearMap.ext
    intro m
    rfl

/-- Actual internal Hom into the original function model is coinduced, without any finite-rank source assumption. -/
def originalInternalHomCoinducedTargetIso :
    (Rep.ihom M).obj (originalCoinducedFunctionRep D) ≅
      originalCoinducedFunctionRep (originalInternalHomPointRep M D) :=
  Rep.mkIso {
    toFun := originalInternalHomCoinducedTargetForward M D
    invFun := originalInternalHomCoinducedTargetBackward M D
    left_inv := fun φ => by
      apply LinearMap.ext
      intro m
      apply Subtype.ext
      funext g
      change (φ (M.ρ g⁻¹ (M.ρ g m))).val g = (φ m).val g
      rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
    right_inv := fun F => by
      apply Subtype.ext
      funext g
      apply LinearMap.ext
      intro m
      change F.val g (M.ρ g (M.ρ g⁻¹ m)) = F.val g m
      rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
    map_add' := (originalInternalHomCoinducedTargetForward M D).map_add
    map_smul' := (originalInternalHomCoinducedTargetForward M D).map_smul
    isIntertwining' := fun h => by
      apply LinearMap.ext
      intro φ
      apply Subtype.ext
      funext g
      apply LinearMap.ext
      intro m
      change (φ (M.ρ h⁻¹ (M.ρ g⁻¹ m))).val (g * h) =
        (φ (M.ρ (g * h)⁻¹ m)).val (g * h)
      rw [mul_inv_rev, map_mul, Module.End.mul_apply] }

/-- Positive cohomology of the actual internal Hom into original coinduction vanishes. -/
theorem originalInternalHomCoinducedTarget_positive_zero [Fintype G] (n : ℕ) :
    Limits.IsZero (groupCohomology ((Rep.ihom M).obj (originalCoinducedFunctionRep D)) (n + 1)) :=
  (originalCoinducedFunction_positive_zero (originalInternalHomPointRep M D) n).of_iso
    ((groupCohomology.functor k G (n + 1)).mapIso (originalInternalHomCoinducedTargetIso M D))

end
end Dubon2026
