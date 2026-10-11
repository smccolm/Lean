import Dubon2026.BialgebraSurjectiveDescent
import Dubon2026.HopfSurjectiveAntipodeDescent
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-! # Constructing the actual coordinate Hopf quotient from explicit ideal stability -/

namespace Dubon2026
noncomputable section
open scoped TensorProduct

variable {R A : Type*} [CommRing R] [CommRing A] [HopfAlgebra R A]

/-- The original comultiplication descends when its actual quotient tensor map kills the original ideal. -/
def hopfCoordinateQuotientComul (I : Ideal A)
    (hd : I ≤ RingHom.ker (((Algebra.TensorProduct.map (Ideal.Quotient.mkₐ R I)
      (Ideal.Quotient.mkₐ R I)).comp (Bialgebra.comulAlgHom R A)).toRingHom)) :
    A ⧸ I →ₐ[R] (A ⧸ I) ⊗[R] (A ⧸ I) :=
  Ideal.Quotient.liftₐ I ((Algebra.TensorProduct.map (Ideal.Quotient.mkₐ R I)
    (Ideal.Quotient.mkₐ R I)).comp (Bialgebra.comulAlgHom R A)) hd

/-- The same original counit descends through its literal ideal vanishing condition. -/
def hopfCoordinateQuotientCounit (I : Ideal A)
    (he : I ≤ RingHom.ker (Bialgebra.counitAlgHom R A).toRingHom) :
    A ⧸ I →ₐ[R] R := Ideal.Quotient.liftₐ I (Bialgebra.counitAlgHom R A) he

/-- Derive every bialgebra axiom for the actual quotient maps through the genuine coordinate surjection. -/
abbrev hopfCoordinateQuotientBialgebra (I : Ideal A)
    (hd : I ≤ RingHom.ker (((Algebra.TensorProduct.map (Ideal.Quotient.mkₐ R I)
      (Ideal.Quotient.mkₐ R I)).comp (Bialgebra.comulAlgHom R A)).toRingHom))
    (he : I ≤ RingHom.ker (Bialgebra.counitAlgHom R A).toRingHom) : Bialgebra R (A ⧸ I) :=
  bialgebraSurjectiveDescent (Ideal.Quotient.mkₐ R I) (Ideal.Quotient.mkₐ_surjective R I)
    (hopfCoordinateQuotientComul I hd) (hopfCoordinateQuotientCounit I he)
    (by ext a; rfl) (by ext a; rfl)

/-- The actual quotient map is a bialgebra homomorphism for the constructed original quotient structure. -/
def hopfCoordinateQuotientMap (I : Ideal A)
    (hd : I ≤ RingHom.ker (((Algebra.TensorProduct.map (Ideal.Quotient.mkₐ R I)
      (Ideal.Quotient.mkₐ R I)).comp (Bialgebra.comulAlgHom R A)).toRingHom))
    (he : I ≤ RingHom.ker (Bialgebra.counitAlgHom R A).toRingHom) :
    letI := hopfCoordinateQuotientBialgebra I hd he
    A →ₐc[R] A ⧸ I :=
  letI := hopfCoordinateQuotientBialgebra I hd he
  BialgHom.ofAlgHom (Ideal.Quotient.mkₐ R I) (by ext a; rfl) (by ext a; rfl)

/-- Explicit ideal stability makes the original antipode descend; the actual source Hopf identities then prove the quotient Hopf structure. -/
abbrev hopfCoordinateQuotient (I : Ideal A)
    (hd : I ≤ RingHom.ker (((Algebra.TensorProduct.map (Ideal.Quotient.mkₐ R I)
      (Ideal.Quotient.mkₐ R I)).comp (Bialgebra.comulAlgHom R A)).toRingHom))
    (he : I ≤ RingHom.ker (Bialgebra.counitAlgHom R A).toRingHom)
    (hs : I ≤ I.comap (commutativeHopfAntipode (R := R)).toRingHom) :
    HopfAlgebra R (A ⧸ I) :=
  letI := hopfCoordinateQuotientBialgebra I hd he
  hopfSurjectiveAntipodeDescent (hopfCoordinateQuotientMap I hd he)
    (Ideal.Quotient.mkₐ_surjective R I)
    (Ideal.quotientMapₐ I (commutativeHopfAntipode (R := R)) hs) (by ext a; rfl)

/-- Comultiplication in the constructed Hopf quotient is exactly the original comultiplication followed by the actual quotient tensor map. -/
theorem hopfCoordinateQuotient_comul_mk (I : Ideal A)
    (hd : I ≤ RingHom.ker (((Algebra.TensorProduct.map (Ideal.Quotient.mkₐ R I)
      (Ideal.Quotient.mkₐ R I)).comp (Bialgebra.comulAlgHom R A)).toRingHom))
    (he : I ≤ RingHom.ker (Bialgebra.counitAlgHom R A).toRingHom)
    (hs : I ≤ I.comap (commutativeHopfAntipode (R := R)).toRingHom) (a : A) :
    letI := hopfCoordinateQuotient I hd he hs
    Coalgebra.comul (R := R) (Ideal.Quotient.mk I a) =
      (Algebra.TensorProduct.map (Ideal.Quotient.mkₐ R I) (Ideal.Quotient.mkₐ R I))
        (Coalgebra.comul a) := by
  rfl

/-- Antipode evaluation in the constructed quotient is the same original coordinate antipode followed by the same quotient map. -/
theorem hopfCoordinateQuotient_antipode_mk (I : Ideal A)
    (hd : I ≤ RingHom.ker (((Algebra.TensorProduct.map (Ideal.Quotient.mkₐ R I)
      (Ideal.Quotient.mkₐ R I)).comp (Bialgebra.comulAlgHom R A)).toRingHom))
    (he : I ≤ RingHom.ker (Bialgebra.counitAlgHom R A).toRingHom)
    (hs : I ≤ I.comap (commutativeHopfAntipode (R := R)).toRingHom) (a : A) :
    letI := hopfCoordinateQuotient I hd he hs
    HopfAlgebra.antipode R (Ideal.Quotient.mk I a) =
      Ideal.Quotient.mk I (HopfAlgebra.antipode R a) := by
  rfl

end
end Dubon2026
