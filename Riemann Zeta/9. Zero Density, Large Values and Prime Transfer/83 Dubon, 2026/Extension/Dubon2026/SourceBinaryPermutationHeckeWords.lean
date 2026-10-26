import Dubon2026.SourceBinaryPermutationHecke
import Dubon2026.SourceBinaryH1HeckeAlgebra
import Dubon2026.SourceIntegralWordAdditiveNaturality
import Dubon2026.SourceBinaryHeckeChange

/-! DUB-17/18 -> original all-weight adic association -> finite geometric
Hecke realization. Compare the actual integral and permutation Hecke words
using the existing additive word intertwiner. No new word induction or
assumed Hecke compatibility is needed. -/
namespace Dubon2026
noncomputable section
open CategoryTheory CongruenceSubgroup

/-- Word evaluation in the original integral binary H1 Hecke algebra. -/
def sourceBinaryH1HeckeWord (Q w : ℕ) :
    FreeAlgebra ℤ (sourceBinaryHeckePrime Q) →ₐ[ℤ] sourceBinaryH1HeckeAlgebra Q w :=
  (FreeAlgebra.lift ℤ (sourceBinaryH1PrimeOperators ℤ Q w)).codRestrict _ (by
    intro a
    rw [sourceBinaryH1HeckeAlgebra, Algebra.adjoin_range_eq_range_freeAlgebra_lift]
    exact ⟨a, rfl⟩)

/-- Every actual integral Hecke operator is an integral prime word. -/
theorem sourceBinaryH1HeckeWord_surjective (Q w : ℕ) :
    Function.Surjective (sourceBinaryH1HeckeWord Q w) := by
  intro T
  have h : T.val ∈ Algebra.adjoin ℤ (Set.range (sourceBinaryH1PrimeOperators ℤ Q w)) := T.property
  rw [Algebra.adjoin_range_eq_range_freeAlgebra_lift] at h
  obtain ⟨a, ha⟩ := h
  exact ⟨a, Subtype.ext ha⟩

/-- The actual full prime correspondences on permutation H1. -/
def sourceBinaryPermutationPrimeOperators (R : Type) [CommRing R] (Q w : ℕ) :
    sourceBinaryHeckePrime Q → Module.End R (groupCohomology.H1
      (sourceCoefficientPermutationRep (sourceBinaryCoefficientRep R Q w))) :=
  fun ell => letI : NeZero ell.val := ⟨ell.property.1.ne_zero⟩
    sourceBinaryPermutationHeckeH1 R ell.property.1 w

/-- The image of the actual permutation prime-word action. -/
def sourceBinaryPermutationHeckeAlgebra (R : Type) [CommRing R] (Q w : ℕ) :=
  (FreeAlgebra.lift ℤ (sourceBinaryPermutationPrimeOperators R Q w)).range

/-- Permutation evaluation intertwines every integral word in the actual
good-prime correspondences. -/
theorem sourceBinaryPermutationHeckeWord_evaluation
    (R : Type) [CommRing R] (Q w : ℕ)
    (a : FreeAlgebra ℤ (sourceBinaryHeckePrime Q))
    (x : groupCohomology.H1
      (sourceCoefficientPermutationRep (sourceBinaryCoefficientRep R Q w))) :
    ((groupCohomology.functor R (Gamma0 Q) 1).map
      (sourceCoefficientPermutationEvaluation (sourceBinaryCoefficientRep R Q w)))
        (FreeAlgebra.lift ℤ (sourceBinaryPermutationPrimeOperators R Q w) a x) =
      FreeAlgebra.lift ℤ (sourceBinaryH1PrimeOperators R Q w) a
        (((groupCohomology.functor R (Gamma0 Q) 1).map
          (sourceCoefficientPermutationEvaluation (sourceBinaryCoefficientRep R Q w))) x) := by
  apply sourceHeckeWord_intertwine_addHom _ _
    (((groupCohomology.functor R (Gamma0 Q) 1).map
      (sourceCoefficientPermutationEvaluation (sourceBinaryCoefficientRep R Q w))).hom.toAddMonoidHom)
  intro ell y
  letI : NeZero ell.val := ⟨ell.property.1.ne_zero⟩
  exact sourceBinaryPermutationHeckeH1_evaluation R ell.property.1 w y

/-- Literal coefficient reduction intertwines the same entire original
integral prime-word action. -/
theorem sourceBinaryH1HeckeWord_change (N Q w : ℕ)
    (a : FreeAlgebra ℤ (sourceBinaryHeckePrime Q))
    (x : groupCohomology.H1 (sourceBinaryCoefficientRep ℤ Q w)) :
    sourceBinaryH1Change (Int.castRingHom (ZMod N)) Q w
        ((sourceBinaryH1HeckeWord Q w a).val x) =
      FreeAlgebra.lift ℤ (sourceBinaryH1PrimeOperators (ZMod N) Q w) a
        (sourceBinaryH1Change (Int.castRingHom (ZMod N)) Q w x) := by
  change sourceBinaryH1Change (Int.castRingHom (ZMod N)) Q w
      (FreeAlgebra.lift ℤ (sourceBinaryH1PrimeOperators ℤ Q w) a x) = _
  apply sourceHeckeWord_intertwine_addHom _ _
    (sourceBinaryH1Change (Int.castRingHom (ZMod N)) Q w).toAddMonoidHom
  intro ell y
  letI : NeZero ell.val := ⟨ell.property.1.ne_zero⟩
  exact sourceBinaryH1Change_hecke (Int.castRingHom (ZMod N)) ell.property.1 w y

end
end Dubon2026
