import Dubon2026.CMFiniteAdelicSmallParabolicLevels

/-! # The original small unitary auxiliary quotient

The source family quotient is realized in the full original unitary
adelic group while preserving the separate principal-congruence place.
This discharges the quotient and its arithmetic finiteness for the
actual levels used by DUB-17's automorphic comparison.
-/

namespace Dubon2026
noncomputable section
open NumberField IsDedekindDomain
open scoped NumberField

variable (K : Type) [Field K] [NumberField K] [IsCMField K]
variable {S : Type*} (v : S → HeightOneSpectrum (𝓞 K)) (n : ℕ)

/-- The quotient of the two actual small auxiliary levels in the full original unitary group. -/
abbrev CMFiniteAdelicSmallParabolicQuotient
    (H : Matrix (Fin (n + 1)) (Fin (n + 1)) K) (w : HeightOneSpectrum (𝓞 K)) :=
  cmFiniteAdelicSmallParabolicZero K v n H w ⧸
    (cmFiniteAdelicSmallParabolicOne K v n H w).subgroupOf
      (cmFiniteAdelicSmallParabolicZero K v n H w)

variable [Fintype S]
variable (H : (Matrix (Fin (n + 1)) (Fin (n + 1)) K)ˣ) (hH : star H = H)
variable (hv : ∀ s, v s ≠ cmFinitePlaceConjugation K (v s))
variable (hlocal : ∀ s, cmFiniteAdelicFormIntegralAtConjugate K H (v s))
variable (hsep : Pairwise fun s t => v s ≠ v t ∧ v s ≠ cmFinitePlaceConjugation K (v t))
variable (w : HeightOneSpectrum (𝓞 K))
variable (hw : ∀ s, w ≠ v s ∧ w ≠ cmFinitePlaceConjugation K (v s))

/-- The actual small unitary auxiliary quotient is the existing original arithmetic local family quotient. -/
def cmFiniteAdelicSmallParabolicQuotientEquiv :
    CMFiniteAdelicSmallParabolicQuotient K v n H.val w ≃* FinitePlaceParabolicFamilyQuotient K v n := by
  letI := subgroupPairImage_normal
    (cmFiniteAdelicPrincipalParabolicZero K v n H.val w)
    (cmFiniteAdelicPrincipalParabolicOne K v n H.val w)
    (cmFiniteAdelicPrincipalLevel K H.val w).subtype Subtype.val_injective
  letI := subgroupPairPreimage_normal (finitePlaceParabolicFamilyLevelZero K v n)
    (finitePlaceParabolicFamilyLevelOne K v n) (cmFiniteAdelicPrincipalFamilyMap K v n H.val w)
  exact (subgroupPairImageQuotientEquiv
    (cmFiniteAdelicPrincipalParabolicZero K v n H.val w)
    (cmFiniteAdelicPrincipalParabolicOne K v n H.val w)
    (cmFiniteAdelicPrincipalLevel K H.val w).subtype Subtype.val_injective).symm.trans
      (subgroupPairPreimageQuotientEquiv _ _ _
        (cmFiniteAdelicPrincipalFamilyMap_surjective K v n H hH hv hlocal hsep w hw))

include hH hv hlocal hsep hw

/-- The original small unitary auxiliary quotient is finite by the proved source local realization. -/
theorem cmFiniteAdelicSmallParabolicQuotient_finite :
    Finite (CMFiniteAdelicSmallParabolicQuotient K v n H.val w) :=
  Finite.of_equiv (FinitePlaceParabolicFamilyQuotient K v n)
    (cmFiniteAdelicSmallParabolicQuotientEquiv K v n H hH hv hlocal hsep w hw).symm.toEquiv

/-- The actual small unitary quotient has the source product of original residue-unit orders. -/
theorem cmFiniteAdelicSmallParabolicQuotient_card :
    Nat.card (CMFiniteAdelicSmallParabolicQuotient K v n H.val w) =
      ∏ s, (Nat.card (𝓞 K ⧸ (v s).asIdeal) - 1) :=
  (Nat.card_congr (cmFiniteAdelicSmallParabolicQuotientEquiv K v n H hH hv hlocal hsep w hw).toEquiv).trans
    (finitePlaceParabolicFamilyQuotient_card K v n)

end
end Dubon2026
