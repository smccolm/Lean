import Dubon2026.AdelicRestrictedAlgebraicAction
import Dubon2026.AdelicRestrictedTensorCompletion
import Dubon2026.IsometricRepresentationCompletion

/-! # Genuine completed restricted tensor action and original full adelic equivariance -/

namespace Dubon2026

noncomputable section

variable {N : ℕ} [NeZero N] {k : ℤ} (F : PrimitiveCuspForm N k)

/-- The true algebraic external action extends by its proved isometries to the genuine restricted Hilbert tensor. -/
def adelicRestrictedHilbertTensorRepresentation :
    Representation ℂ RationalAdelicGL2 (AdelicRestrictedHilbertTensor F) :=
  isometricRepresentationCompletion (adelicRestrictedAlgebraicRepresentation F)
    (adelicRestrictedAlgebraicRepresentation_norm F)

/-- The genuine completed external action agrees exactly with the original full adelic representation on every completed vector. -/
theorem adelicRestrictedHilbertTensorIsometry_intertwines (a : RationalAdelicGL2) (x : AdelicRestrictedHilbertTensor F) :
    adelicRestrictedHilbertTensorIsometry F (adelicRestrictedHilbertTensorRepresentation F a x) =
      adelicCyclicHilbertRepresentation F.toCuspForm a (adelicRestrictedHilbertTensorIsometry F x) :=
  @isometricRepresentationCompletion_intertwines RationalAdelicGL2 (AdelicRestrictedAlgebraicTensor F)
    inferInstance inferInstance inferInstance
    (adelicRestrictedAlgebraicRepresentation F) (adelicRestrictedAlgebraicRepresentation_norm F)
    (AdelicCyclicHilbert F.toCuspForm) inferInstance inferInstance inferInstance
    (adelicRestrictedAlgebraicTensorIsometry F) a (adelicCyclicHilbertOperator F.toCuspForm a)
    (adelicRestrictedAlgebraicAction_intertwines F a) x

/-- The independently constructed genuine restricted tensor action is strongly continuous for the original adelic topology. -/
theorem adelicRestrictedHilbertTensorRepresentation_stronglyContinuous (x : AdelicRestrictedHilbertTensor F) :
    Continuous (fun a => adelicRestrictedHilbertTensorRepresentation F a x) :=
  @isometric_intertwiner_stronglyContinuous RationalAdelicGL2
    (AdelicRestrictedHilbertTensor F) (AdelicCyclicHilbert F.toCuspForm)
    inferInstance inferInstance inferInstance inferInstance inferInstance
    (fun a x => adelicRestrictedHilbertTensorRepresentation F a x)
    (fun a x => adelicCyclicHilbertRepresentation F.toCuspForm a x)
    (adelicRestrictedHilbertTensorIsometry F) (adelicRestrictedHilbertTensorIsometry_intertwines F)
    (adelicCyclicHilbertRepresentation_stronglyContinuous F.toCuspForm) x

/-- The actual completed tensor equivalence is equivariant for the genuine full external adelic action. -/
theorem adelicRestrictedHilbertTensorEquiv_intertwines (a : RationalAdelicGL2) (x : AdelicRestrictedHilbertTensor F) :
    adelicRestrictedHilbertTensorEquiv F (adelicRestrictedHilbertTensorRepresentation F a x) =
      adelicCyclicHilbertRepresentation F.toCuspForm a (adelicRestrictedHilbertTensorEquiv F x) :=
  adelicRestrictedHilbertTensorIsometry_intertwines F a x

end
end Dubon2026
