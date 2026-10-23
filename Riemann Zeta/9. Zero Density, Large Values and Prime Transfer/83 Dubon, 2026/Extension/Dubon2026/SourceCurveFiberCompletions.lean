import Dubon2026.SourceCurveCompletionFinite
import Dubon2026.SourceCurveFiberPrimes
import Mathlib.RingTheory.TensorProduct.Basic

/-! The actual completion maps for every place in a restriction fiber.
Their tensor-product components are the maps whose joint bijectivity will
assemble local field traces. This serves the remaining DUB-17/18 global
residue obligation, using the already proved finite spanning basis. -/

noncomputable section

namespace Dubon2026.SourceCurve.Place

open scoped TensorProduct

variable {K F E : Type*} [Field K] [Field F] [Field E]
  [Algebra K F] [Algebra K E] [Algebra F E] [IsScalarTower K F E]
  [Algebra.IsIntegral F E] (v : Place K F)

/-- The actual base-completion action on the completion of a place above it. -/
instance fiberCompletionAlgebra (w : {w : Place K E // w.restrict F = v}) :
    Algebra v.adicCompletion w.1.adicCompletion := by
  rcases w with ⟨w, hw⟩
  subst v
  exact w.completionExtensionAlgebra (F := F)

/-- The original base-field action commutes with each fiber completion. -/
instance fiberCompletionTower (w : {w : Place K E // w.restrict F = v}) :
    IsScalarTower F v.adicCompletion w.1.adicCompletion := by
  rcases w with ⟨w, hw⟩
  subst v
  exact w.completionExtensionTower (F := F)

/-- The actual component of the completed tensor algebra at a place above the base place. -/
def fiberCompletionComponent (w : {w : Place K E // w.restrict F = v}) :
    v.adicCompletion ⊗[F] E →ₐ[v.adicCompletion] w.1.adicCompletion :=
  Algebra.TensorProduct.lift (Algebra.ofId v.adicCompletion w.1.adicCompletion)
    (IsScalarTower.toAlgHom F E w.1.adicCompletion) (fun _ _ => mul_comm _ _)

/-- The component map multiplies the literal completed images of a pure tensor. -/
theorem fiberCompletionComponent_tmul (w : {w : Place K E // w.restrict F = v})
    (c : v.adicCompletion) (g : E) :
    v.fiberCompletionComponent w (c ⊗ₜ[F] g) =
      algebraMap v.adicCompletion w.1.adicCompletion c * algebraMap E w.1.adicCompletion g := by
  rw [fiberCompletionComponent, Algebra.TensorProduct.lift_tmul]
  rfl

/-- The proved completed spanning basis makes every individual component surjective. -/
theorem fiberCompletionComponent_surjective [FiniteDimensional F E]
    (w : {w : Place K E // w.restrict F = v}) :
    Function.Surjective (v.fiberCompletionComponent w) := by
  classical
  rcases w with ⟨w, hw⟩
  subst v
  intro y
  let b := Module.finBasis F E
  obtain ⟨c, hc⟩ := w.completionLinearCombination_surjective b y
  refine ⟨∑ i, c i ⊗ₜ[F] b i, ?_⟩
  rw [map_sum, ← hc]
  change _ = Fintype.linearCombination (w.restrict F).adicCompletion
    (fun i => algebraMap E w.adicCompletion (b i)) c
  rw [Fintype.linearCombination_apply]
  apply Finset.sum_congr rfl
  intro i _
  rw [fiberCompletionComponent_tmul, Algebra.smul_def]

/-- The literal diagonal map to the product of all completions over the base place. -/
def fiberCompletionDiagonal : v.adicCompletion ⊗[F] E →ₐ[v.adicCompletion]
    ((w : {w : Place K E // w.restrict F = v}) → w.1.adicCompletion) :=
  Pi.algHom v.adicCompletion _ (v.fiberCompletionComponent (E := E))

/-- On original elements the diagonal map is exactly the family of original completion embeddings. -/
theorem fiberCompletionDiagonal_one_tmul (g : E) (w : {w : Place K E // w.restrict F = v}) :
    v.fiberCompletionDiagonal ((1 : v.adicCompletion) ⊗ₜ[F] g) w =
      algebraMap E w.1.adicCompletion g := by
  change v.fiberCompletionComponent w ((1 : v.adicCompletion) ⊗ₜ[F] g) = _
  rw [v.fiberCompletionComponent_tmul, map_one, one_mul]

end Dubon2026.SourceCurve.Place
