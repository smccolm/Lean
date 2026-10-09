import Dubon2026.AdelicSplitActionOnStage

/-! # The genuine fully split algebraic tensor action of original full adelic GL2 -/

namespace Dubon2026

noncomputable section

variable {N : ℕ} [NeZero N] {k : ℤ} (F : PrimitiveCuspForm N k) (hk : 0 < k)

/-- The true finite-stage external action descends by its proved compatibility to the actual directed quotient. -/
def adelicSplitAlgebraicAction (a : RationalAdelicGL2) :
    AdelicSplitAlgebraicTensor F →ₗ[ℂ] AdelicSplitAlgebraicTensor F :=
  DirectLimit.Module.lift ℂ ℕ (fun n => adelicSplitStage F.toCuspForm n)
    (fun n m h => (adelicSplitStageMap F.toCuspForm (primitiveCuspForm_ne_zero F) n m h).toLinearMap)
    (adelicSplitActionOnStage F a) (adelicSplitActionOnStage_compatible F hk a)

/-- On each genuine finite-stage tensor, the descended action is precisely its actual finite external recipe. -/
theorem adelicSplitAlgebraicAction_of (a : RationalAdelicGL2) (n : ℕ)
    (x : adelicSplitStage F.toCuspForm n) :
    adelicSplitAlgebraicAction F hk a (adelicSplitTensorOf F n x) = adelicSplitActionOnStage F a n x := rfl

/-- The genuine descended fully split action intertwines with the original full adelic representation on every algebraic vector. -/
theorem adelicSplitAlgebraicAction_intertwines (a : RationalAdelicGL2) (x : AdelicSplitAlgebraicTensor F) :
    adelicSplitAlgebraicTensorIsometry F hk (adelicSplitAlgebraicAction F hk a x) =
      adelicCyclicHilbertRepresentation F.toCuspForm a (adelicSplitAlgebraicTensorIsometry F hk x) := by
  obtain ⟨n, y, rfl⟩ := adelicSplitTensor_exists_stage F x
  rw [adelicSplitAlgebraicAction_of, adelicSplitActionOnStage_intertwines F hk,
    adelicSplitAlgebraicTensorIsometry_of]

/-- The actual descended finite-stage external action at the original identity is the identity operator. -/
theorem adelicSplitAlgebraicAction_one : adelicSplitAlgebraicAction F hk 1 = 1 := by
  apply LinearMap.ext
  intro x
  apply (adelicSplitAlgebraicTensorIsometry F hk).injective
  change adelicSplitAlgebraicTensorIsometry F hk (adelicSplitAlgebraicAction F hk 1 x) =
    adelicSplitAlgebraicTensorIsometry F hk x
  have h := adelicSplitAlgebraicAction_intertwines F hk 1 x
  simpa only [map_one, Module.End.one_apply] using h

/-- The actual descended finite-stage external actions compose according to original adelic matrix multiplication. -/
theorem adelicSplitAlgebraicAction_mul (a b : RationalAdelicGL2) :
    adelicSplitAlgebraicAction F hk (a * b) = adelicSplitAlgebraicAction F hk a * adelicSplitAlgebraicAction F hk b := by
  apply LinearMap.ext
  intro x
  apply (adelicSplitAlgebraicTensorIsometry F hk).injective
  change adelicSplitAlgebraicTensorIsometry F hk (adelicSplitAlgebraicAction F hk (a * b) x) =
    adelicSplitAlgebraicTensorIsometry F hk (adelicSplitAlgebraicAction F hk a (adelicSplitAlgebraicAction F hk b x))
  have h₁ := adelicSplitAlgebraicAction_intertwines F hk (a * b) x
  have h₂ := adelicSplitAlgebraicAction_intertwines F hk a (adelicSplitAlgebraicAction F hk b x)
  have h₃ := adelicSplitAlgebraicAction_intertwines F hk b x
  have hm := @representation_hom_mul_apply RationalAdelicGL2 RationalAdelicGL2
    (AdelicCyclicHilbert F.toCuspForm) inferInstance inferInstance inferInstance inferInstance
    (adelicCyclicHilbertRepresentation F.toCuspForm) (MonoidHom.id _) a b
    (adelicSplitAlgebraicTensorIsometry F hk x)
  exact h₁.trans (hm.trans ((congrArg (adelicCyclicHilbertRepresentation F.toCuspForm a) h₃.symm).trans h₂.symm))

/-- The independently constructed external action satisfies the group identity and multiplication laws on the genuine quotient. -/
def adelicSplitAlgebraicRepresentation : Representation ℂ RationalAdelicGL2 (AdelicSplitAlgebraicTensor F) where
  toFun := adelicSplitAlgebraicAction F hk
  map_one' := adelicSplitAlgebraicAction_one F hk
  map_mul' := adelicSplitAlgebraicAction_mul F hk

/-- The actual external fully split algebraic representation preserves its independently descended tensor norm. -/
theorem adelicSplitAlgebraicRepresentation_norm (a : RationalAdelicGL2) (x : AdelicSplitAlgebraicTensor F) :
    ‖adelicSplitAlgebraicRepresentation F hk a x‖ = ‖x‖ :=
  @linearMap_norm_of_isometric_intertwiner (AdelicSplitAlgebraicTensor F) (AdelicCyclicHilbert F.toCuspForm)
    inferInstance inferInstance inferInstance inferInstance
    (adelicSplitAlgebraicTensorIsometry F hk) (adelicSplitAlgebraicAction F hk a)
    (adelicCyclicHilbertRepresentation F.toCuspForm a)
    (adelicSplitAlgebraicAction_intertwines F hk a) (adelicCyclicHilbertOperator_norm F.toCuspForm a) x

end
end Dubon2026
