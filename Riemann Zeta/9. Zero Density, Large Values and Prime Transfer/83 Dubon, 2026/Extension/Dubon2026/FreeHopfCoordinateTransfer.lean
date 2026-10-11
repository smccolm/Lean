import Dubon2026.BialgebraInjectiveDescent
import Dubon2026.HopfInjectiveAntipodeDescent
import Dubon2026.BialgebraCocommutativeDescent
import Mathlib.RingTheory.Bialgebra.Equiv

/-! # Transport the actual free Hopf coordinates through an original algebra equivalence -/

namespace Dubon2026
noncomputable section
open scoped TensorProduct

variable {R A B : Type*} [CommRing R] [CommRing A] [HopfAlgebra R A] [Module.Free R A]
  [CommRing B] [Algebra R B]

/-- The original comultiplication, expressed in the genuinely equivalent coordinates. -/
def freeHopfCoordinateTransferComul (e : B ≃ₐ[R] A) : B →ₐ[R] B ⊗[R] B :=
  (Algebra.TensorProduct.congr e e).symm.toAlgHom.comp
    ((Bialgebra.comulAlgHom R A).comp e.toAlgHom)

omit [Module.Free R A] in
private theorem freeHopfCoordinateTransferComul_diagram (e : B ≃ₐ[R] A) :
    (Algebra.TensorProduct.map e.toAlgHom e.toAlgHom).comp (freeHopfCoordinateTransferComul e) =
      (Bialgebra.comulAlgHom R A).comp e.toAlgHom := by
  apply AlgHom.ext
  intro b
  change (Algebra.TensorProduct.congr e e)
      ((Algebra.TensorProduct.congr e e).symm (Coalgebra.comul (e b))) = Coalgebra.comul (e b)
  exact (Algebra.TensorProduct.congr e e).apply_symm_apply _

/-- The genuine original bialgebra identities descend along the original coordinate equivalence. -/
abbrev freeHopfCoordinateTransferBialgebra (e : B ≃ₐ[R] A) : Bialgebra R B := by
  letI : Module.Free R B := Module.Free.of_equiv e.symm.toLinearEquiv
  exact bialgebraInjectiveDescent e.toAlgHom e.injective (freeHopfCoordinateTransferComul e)
    ((Bialgebra.counitAlgHom R A).comp e.toAlgHom) (freeHopfCoordinateTransferComul_diagram e) rfl

/-- The original algebra equivalence is a genuine coordinate bialgebra map for the constructed structure. -/
def freeHopfCoordinateTransferMap (e : B ≃ₐ[R] A) :
    letI := freeHopfCoordinateTransferBialgebra e
    B →ₐc[R] A := by
  letI := freeHopfCoordinateTransferBialgebra e
  exact BialgHom.ofAlgHom e.toAlgHom rfl (freeHopfCoordinateTransferComul_diagram e)

/-- Express the same original antipode in the equivalent coordinates. -/
def freeHopfCoordinateTransferAntipode (e : B ≃ₐ[R] A) : B →ₐ[R] B :=
  e.symm.toAlgHom.comp ((commutativeHopfAntipode (R := R) (A := A)).comp e.toAlgHom)

omit [Module.Free R A] in
private theorem freeHopfCoordinateTransferAntipode_diagram (e : B ≃ₐ[R] A) :
    e.toAlgHom.comp (freeHopfCoordinateTransferAntipode e) =
      (commutativeHopfAntipode (R := R) (A := A)).comp e.toAlgHom := by
  apply AlgHom.ext
  intro b
  exact e.apply_symm_apply _

/-- Construct the actual Hopf algebra in the equivalent coordinates by deriving both original antipode identities through the genuine coordinate equivalence. -/
abbrev freeHopfCoordinateTransfer (e : B ≃ₐ[R] A) : HopfAlgebra R B := by
  letI := freeHopfCoordinateTransferBialgebra e
  exact hopfInjectiveAntipodeDescent (freeHopfCoordinateTransferMap e) e.injective
    (freeHopfCoordinateTransferAntipode e) (freeHopfCoordinateTransferAntipode_diagram e)

/-- The original equivalence becomes a genuine bialgebra equivalence for the constructed original-coordinate Hopf structure. -/
def freeHopfCoordinateTransferEquiv (e : B ≃ₐ[R] A) :
    letI := freeHopfCoordinateTransfer e
    B ≃ₐc[R] A := by
  letI := freeHopfCoordinateTransfer e
  exact BialgEquiv.ofAlgEquiv e rfl (freeHopfCoordinateTransferComul_diagram e)

/-- The actual transferred Hopf antipode is the original antipode through the same coordinate equivalence. -/
theorem freeHopfCoordinateTransfer_antipode (e : B ≃ₐ[R] A) (b : B) :
    letI := freeHopfCoordinateTransfer e
    e (HopfAlgebra.antipode R b) = HopfAlgebra.antipode R (e b) := by
  letI := freeHopfCoordinateTransfer e
  exact e.apply_symm_apply _

/-- Genuine cocommutativity is preserved by the same coordinate equivalence. -/
theorem freeHopfCoordinateTransfer_isCocomm [Coalgebra.IsCocomm R A] (e : B ≃ₐ[R] A) :
    letI := freeHopfCoordinateTransfer e
    Coalgebra.IsCocomm R B := by
  letI := freeHopfCoordinateTransfer e
  letI : Module.Free R B := Module.Free.of_equiv e.symm.toLinearEquiv
  exact bialgebraIsCocomm_of_injective (freeHopfCoordinateTransferEquiv e).toBialgHom e.injective

end
end Dubon2026
