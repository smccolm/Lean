import Dubon2026.AdelicSplitAlgebraicAction
import Dubon2026.AdelicSplitTensorCompletion
import Dubon2026.IsometricRepresentationCompletion

/-! # Genuine completed fully split tensor action and original full adelic equivariance -/

namespace Dubon2026

noncomputable section

variable {N : ℕ} [NeZero N] {k : ℤ} (F : PrimitiveCuspForm N k) (hk : 0 < k)

/-- The true algebraic external action extends by its proved isometries to the genuine fully split Hilbert tensor. -/
def adelicSplitHilbertTensorRepresentation :
    Representation ℂ RationalAdelicGL2 (AdelicSplitHilbertTensor F) :=
  isometricRepresentationCompletion (adelicSplitAlgebraicRepresentation F hk)
    (adelicSplitAlgebraicRepresentation_norm F hk)

/-- The genuine completed external action agrees exactly with the original full adelic representation on every completed vector. -/
theorem adelicSplitHilbertTensorIsometry_intertwines (a : RationalAdelicGL2) (x : AdelicSplitHilbertTensor F) :
    adelicSplitHilbertTensorIsometry F hk (adelicSplitHilbertTensorRepresentation F hk a x) =
      adelicCyclicHilbertRepresentation F.toCuspForm a (adelicSplitHilbertTensorIsometry F hk x) :=
  @isometricRepresentationCompletion_intertwines RationalAdelicGL2 (AdelicSplitAlgebraicTensor F)
    inferInstance inferInstance inferInstance
    (adelicSplitAlgebraicRepresentation F hk) (adelicSplitAlgebraicRepresentation_norm F hk)
    (AdelicCyclicHilbert F.toCuspForm) inferInstance inferInstance inferInstance
    (adelicSplitAlgebraicTensorIsometry F hk) a (adelicCyclicHilbertOperator F.toCuspForm a)
    (adelicSplitAlgebraicAction_intertwines F hk a) x

/-- The independently constructed genuine fully split tensor action is strongly continuous for the original adelic topology. -/
theorem adelicSplitHilbertTensorRepresentation_stronglyContinuous (x : AdelicSplitHilbertTensor F) :
    Continuous (fun a => adelicSplitHilbertTensorRepresentation F hk a x) :=
  @isometric_intertwiner_stronglyContinuous RationalAdelicGL2
    (AdelicSplitHilbertTensor F) (AdelicCyclicHilbert F.toCuspForm)
    inferInstance inferInstance inferInstance inferInstance inferInstance
    (fun a x => adelicSplitHilbertTensorRepresentation F hk a x)
    (fun a x => adelicCyclicHilbertRepresentation F.toCuspForm a x)
    (adelicSplitHilbertTensorIsometry F hk) (adelicSplitHilbertTensorIsometry_intertwines F hk)
    (adelicCyclicHilbertRepresentation_stronglyContinuous F.toCuspForm) x

/-- The actual completed tensor equivalence is equivariant for the genuine full external adelic action. -/
theorem adelicSplitHilbertTensorEquiv_intertwines (a : RationalAdelicGL2) (x : AdelicSplitHilbertTensor F) :
    adelicSplitHilbertTensorEquiv F hk (adelicSplitHilbertTensorRepresentation F hk a x) =
      adelicCyclicHilbertRepresentation F.toCuspForm a (adelicSplitHilbertTensorEquiv F hk x) :=
  adelicSplitHilbertTensorIsometry_intertwines F hk a x

end
end Dubon2026
