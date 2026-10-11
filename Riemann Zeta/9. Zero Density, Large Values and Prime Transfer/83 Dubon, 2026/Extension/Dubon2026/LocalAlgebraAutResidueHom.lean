import Dubon2026.LocalAlgebraAutMaximalStabilizer
import Mathlib.RingTheory.Invariant.Basic
import Mathlib.RingTheory.LocalRing.ResidueField.Basic

/-! # The actual residue algebra automorphism map of an original local algebra -/

namespace Dubon2026
noncomputable section

open IsLocalRing

variable {R S : Type} [CommRing R] [CommRing S] [Algebra R S]
  [IsLocalRing R] [IsLocalRing S] [IsLocalHom (algebraMap R S)]

/-- Original local algebra automorphisms act on the actual residue field
extension through the genuine maximal-ideal stabilizer quotient map. -/
def localAlgebraAutResidueHom : (S ≃ₐ[R] S) →*
    (ResidueField S ≃ₐ[ResidueField R] ResidueField S) :=
  (Ideal.Quotient.stabilizerHom (maximalIdeal S) (maximalIdeal R) (S ≃ₐ[R] S)).comp
    localAlgebraAutMaximalStabilizerEquiv.toMonoidHom

/-- Actual residue reduction retains the original automorphism on every
original integer-ring representative. -/
theorem localAlgebraAutResidueHom_apply (g : S ≃ₐ[R] S) (x : S) :
    localAlgebraAutResidueHom g (residue S x) = residue S (g x) := by
  rfl

/-- The pinned actual invariant-ring residue theorem makes the original
residue automorphism map surjective for a finite original automorphism group. -/
theorem localAlgebraAutResidueHom_surjective [Finite (S ≃ₐ[R] S)]
    [Algebra.IsInvariant R S (S ≃ₐ[R] S)] :
    Function.Surjective (localAlgebraAutResidueHom (R := R) (S := S)) :=
  (Ideal.Quotient.stabilizerHom_surjective (S ≃ₐ[R] S) (maximalIdeal R)
    (maximalIdeal S)).comp localAlgebraAutMaximalStabilizerEquiv.surjective

end
end Dubon2026
