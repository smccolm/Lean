import Dubon2026.LinearIsometryCompletion

/-! # Completion preserves genuine isometric inclusions and commuting diagrams -/

namespace Dubon2026

noncomputable section
open UniformSpace

variable {V W H : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
  [NormedAddCommGroup W] [NormedSpace ℂ W]
  [NormedAddCommGroup H] [NormedSpace ℂ H]

/-- Complete both sides of an actual linear isometry, using the genuine completion embedding. -/
def linearIsometryCompletionFunctor (J : V →ₗᵢ[ℂ] W) : Completion V →ₗᵢ[ℂ] Completion W :=
  linearIsometryCompletion ((Completion.toComplₗᵢ : W →ₗᵢ[ℂ] Completion W).comp J)

/-- The completed inclusion sends every original vector to the original included vector. -/
theorem linearIsometryCompletionFunctor_coe (J : V →ₗᵢ[ℂ] W) (x : V) :
    linearIsometryCompletionFunctor J (x : Completion V) = (J x : Completion W) :=
  linearIsometryCompletion_coe _ x

/-- A commuting diagram of original isometries remains commutative on the actual completed domain. -/
theorem linearIsometryCompletion_diagram [CompleteSpace H]
    (J : V →ₗᵢ[ℂ] W) (T : W →ₗᵢ[ℂ] H) (S : V →ₗᵢ[ℂ] H)
    (h : ∀ x, T (J x) = S x) (x : Completion V) :
    linearIsometryCompletion T (linearIsometryCompletionFunctor J x) =
      linearIsometryCompletion S x := by
  induction x using Completion.induction_on with
  | hp =>
    exact isClosed_eq ((linearIsometryCompletion T).continuous.comp
      (linearIsometryCompletionFunctor J).continuous) (linearIsometryCompletion S).continuous
  | ih x =>
    rw [linearIsometryCompletionFunctor_coe, linearIsometryCompletion_coe,
      linearIsometryCompletion_coe]
    exact h x

/-- Completion preserves exact composition of genuine isometric transition maps. -/
theorem linearIsometryCompletionFunctor_comp (J : V →ₗᵢ[ℂ] W) (T : W →ₗᵢ[ℂ] H)
    (x : Completion V) :
    linearIsometryCompletionFunctor T (linearIsometryCompletionFunctor J x) =
      linearIsometryCompletionFunctor (T.comp J) x :=
  linearIsometryCompletion_diagram J
    ((Completion.toComplₗᵢ : H →ₗᵢ[ℂ] Completion H).comp T)
    ((Completion.toComplₗᵢ : H →ₗᵢ[ℂ] Completion H).comp (T.comp J)) (fun _ => rfl) x

end
end Dubon2026
