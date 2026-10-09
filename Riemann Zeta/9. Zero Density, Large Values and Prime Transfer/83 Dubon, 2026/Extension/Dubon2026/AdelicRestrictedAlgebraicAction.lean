import Dubon2026.AdelicRestrictedActionOnStage

/-! # The genuine restricted algebraic tensor action of original full adelic GL2 -/

namespace Dubon2026

noncomputable section

variable {N : ℕ} [NeZero N] {k : ℤ} (F : PrimitiveCuspForm N k)

/-- The true finite-stage external action descends by its proved compatibility to the actual directed quotient. -/
def adelicRestrictedAlgebraicAction (a : RationalAdelicGL2) :
    AdelicRestrictedAlgebraicTensor F →ₗ[ℂ] AdelicRestrictedAlgebraicTensor F :=
  DirectLimit.Module.lift ℂ ℕ (fun n => adelicRestrictedStage F.toCuspForm n)
    (fun n m h => (adelicRestrictedStageMap F.toCuspForm (primitiveCuspForm_ne_zero F) n m h).toLinearMap)
    (adelicRestrictedActionOnStage F a) (adelicRestrictedActionOnStage_compatible F a)

/-- On each genuine finite-stage tensor, the descended action is precisely its actual finite external recipe. -/
theorem adelicRestrictedAlgebraicAction_of (a : RationalAdelicGL2) (n : ℕ)
    (x : adelicRestrictedStage F.toCuspForm n) :
    adelicRestrictedAlgebraicAction F a (adelicRestrictedTensorOf F n x) = adelicRestrictedActionOnStage F a n x := rfl

/-- The genuine descended restricted action intertwines with the original full adelic representation on every algebraic vector. -/
theorem adelicRestrictedAlgebraicAction_intertwines (a : RationalAdelicGL2) (x : AdelicRestrictedAlgebraicTensor F) :
    adelicRestrictedAlgebraicTensorIsometry F (adelicRestrictedAlgebraicAction F a x) =
      adelicCyclicHilbertRepresentation F.toCuspForm a (adelicRestrictedAlgebraicTensorIsometry F x) := by
  obtain ⟨n, y, rfl⟩ := adelicRestrictedTensor_exists_stage F x
  rw [adelicRestrictedAlgebraicAction_of, adelicRestrictedActionOnStage_intertwines,
    adelicRestrictedAlgebraicTensorIsometry_of]

/-- The actual descended finite-stage external action at the original identity is the identity operator. -/
theorem adelicRestrictedAlgebraicAction_one : adelicRestrictedAlgebraicAction F 1 = 1 := by
  apply LinearMap.ext
  intro x
  apply (adelicRestrictedAlgebraicTensorIsometry F).injective
  change adelicRestrictedAlgebraicTensorIsometry F (adelicRestrictedAlgebraicAction F 1 x) =
    adelicRestrictedAlgebraicTensorIsometry F x
  have h := adelicRestrictedAlgebraicAction_intertwines F 1 x
  simpa only [map_one, Module.End.one_apply] using h

/-- The actual descended finite-stage external actions compose according to original adelic matrix multiplication. -/
theorem adelicRestrictedAlgebraicAction_mul (a b : RationalAdelicGL2) :
    adelicRestrictedAlgebraicAction F (a * b) = adelicRestrictedAlgebraicAction F a * adelicRestrictedAlgebraicAction F b := by
  apply LinearMap.ext
  intro x
  apply (adelicRestrictedAlgebraicTensorIsometry F).injective
  change adelicRestrictedAlgebraicTensorIsometry F (adelicRestrictedAlgebraicAction F (a * b) x) =
    adelicRestrictedAlgebraicTensorIsometry F (adelicRestrictedAlgebraicAction F a (adelicRestrictedAlgebraicAction F b x))
  have h₁ := adelicRestrictedAlgebraicAction_intertwines F (a * b) x
  have h₂ := adelicRestrictedAlgebraicAction_intertwines F a (adelicRestrictedAlgebraicAction F b x)
  have h₃ := adelicRestrictedAlgebraicAction_intertwines F b x
  have hm := @representation_hom_mul_apply RationalAdelicGL2 RationalAdelicGL2
    (AdelicCyclicHilbert F.toCuspForm) inferInstance inferInstance inferInstance inferInstance
    (adelicCyclicHilbertRepresentation F.toCuspForm) (MonoidHom.id _) a b
    (adelicRestrictedAlgebraicTensorIsometry F x)
  exact h₁.trans (hm.trans ((congrArg (adelicCyclicHilbertRepresentation F.toCuspForm a) h₃.symm).trans h₂.symm))

/-- The independently constructed external action satisfies the group identity and multiplication laws on the genuine quotient. -/
def adelicRestrictedAlgebraicRepresentation : Representation ℂ RationalAdelicGL2 (AdelicRestrictedAlgebraicTensor F) where
  toFun := adelicRestrictedAlgebraicAction F
  map_one' := adelicRestrictedAlgebraicAction_one F
  map_mul' := adelicRestrictedAlgebraicAction_mul F

/-- The actual external restricted algebraic representation preserves its independently descended tensor norm. -/
theorem adelicRestrictedAlgebraicRepresentation_norm (a : RationalAdelicGL2) (x : AdelicRestrictedAlgebraicTensor F) :
    ‖adelicRestrictedAlgebraicRepresentation F a x‖ = ‖x‖ :=
  @linearMap_norm_of_isometric_intertwiner (AdelicRestrictedAlgebraicTensor F) (AdelicCyclicHilbert F.toCuspForm)
    inferInstance inferInstance inferInstance inferInstance
    (adelicRestrictedAlgebraicTensorIsometry F) (adelicRestrictedAlgebraicAction F a)
    (adelicCyclicHilbertRepresentation F.toCuspForm a)
    (adelicRestrictedAlgebraicAction_intertwines F a) (adelicCyclicHilbertOperator_norm F.toCuspForm a) x

end
end Dubon2026
