import Dubon2026.LinearIsometryCompletion
import Mathlib.RepresentationTheory.Basic

/-! # Completion of an actual norm-preserving representation -/

namespace Dubon2026

noncomputable section
open UniformSpace

variable {G V : Type*} [Group G] [NormedAddCommGroup V] [NormedSpace ℂ V]
  (ρ : Representation ℂ G V) (hρ : ∀ g x, ‖ρ g x‖ = ‖x‖)

/-- Each actual norm-preserving representation operator is a genuine continuous linear map. -/
def isometricRepresentationOperator (g : G) : V →L[ℂ] V :=
  (show V →ₗᵢ[ℂ] V from { toLinearMap := ρ g, norm_map' := hρ g }).toContinuousLinearMap

/-- The actual completed original operator, obtained from the continuous linear completion functor. -/
def isometricRepresentationCompletionOperator (g : G) : Completion V →L[ℂ] Completion V :=
  (isometricRepresentationOperator ρ hρ g).completion

/-- Completed original operators agree with the actual representation on every original vector. -/
theorem isometricRepresentationCompletionOperator_coe (g : G) (x : V) :
    isometricRepresentationCompletionOperator ρ hρ g (x : Completion V) = (ρ g x : Completion V) :=
  ContinuousLinearMap.completion_apply_coe _ x

/-- The genuine completed identity operator fixes every completed vector. -/
theorem isometricRepresentationCompletionOperator_one (x : Completion V) :
    isometricRepresentationCompletionOperator ρ hρ 1 x = x := by
  induction x using Completion.induction_on with
  | hp => exact isClosed_eq (isometricRepresentationCompletionOperator ρ hρ 1).continuous continuous_id
  | ih x => rw [isometricRepresentationCompletionOperator_coe]; simp only [map_one, Module.End.one_apply]

/-- Genuine operator multiplication is retained by completion. -/
theorem isometricRepresentationCompletionOperator_mul (g h : G) (x : Completion V) :
    isometricRepresentationCompletionOperator ρ hρ (g * h) x =
      isometricRepresentationCompletionOperator ρ hρ g
        (isometricRepresentationCompletionOperator ρ hρ h x) := by
  induction x using Completion.induction_on with
  | hp =>
    exact isClosed_eq (isometricRepresentationCompletionOperator ρ hρ (g * h)).continuous
      ((isometricRepresentationCompletionOperator ρ hρ g).continuous.comp
        (isometricRepresentationCompletionOperator ρ hρ h).continuous)
  | ih x =>
    rw [isometricRepresentationCompletionOperator_coe, isometricRepresentationCompletionOperator_coe,
      isometricRepresentationCompletionOperator_coe]
    simp only [map_mul, Module.End.mul_apply]

/-- Completion of the original representation by its actual continuous norm-preserving operators. -/
def isometricRepresentationCompletion : Representation ℂ G (Completion V) where
  toFun g := (isometricRepresentationCompletionOperator ρ hρ g).toLinearMap
  map_one' := by ext x; exact isometricRepresentationCompletionOperator_one ρ hρ x
  map_mul' g h := by ext x; exact isometricRepresentationCompletionOperator_mul ρ hρ g h x

/-- The completed representation preserves every genuine completed norm. -/
theorem isometricRepresentationCompletion_norm (g : G) (x : Completion V) :
    ‖isometricRepresentationCompletion ρ hρ g x‖ = ‖x‖ := by
  induction x using Completion.induction_on with
  | hp =>
    exact isClosed_eq
      (continuous_norm.comp (isometricRepresentationCompletionOperator ρ hρ g).continuous) continuous_norm
  | ih x =>
    change ‖isometricRepresentationCompletionOperator ρ hρ g (x : Completion V)‖ = ‖(x : Completion V)‖
    rw [isometricRepresentationCompletionOperator_coe, Completion.norm_coe, Completion.norm_coe, hρ]

/-- A proved original isometric intertwiner extends to the actual completed representation. -/
theorem isometricRepresentationCompletion_intertwines {W : Type*}
    [NormedAddCommGroup W] [NormedSpace ℂ W] [CompleteSpace W]
    (T : V →ₗᵢ[ℂ] W) (g : G) (B : W →L[ℂ] W)
    (h : ∀ x, T (ρ g x) = B (T x)) (x : Completion V) :
    linearIsometryCompletion T (isometricRepresentationCompletion ρ hρ g x) =
      B (linearIsometryCompletion T x) :=
  linearIsometryCompletion_intertwines T (isometricRepresentationOperator ρ hρ g) B h x

end
end Dubon2026
