import Dubon2026.SourcePrimeConjugateBaseChange
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-! DUB-17/18 -> numerical modular genus -> all-level original j-map degree.
Both orientations of the same prime polynomial relation are read directly
from the proved conjugate product: its distinguished root gives the forward
relation, and its untwisted finite root gives the reverse relation. These
are the integral relations needed for divisor and prime-power generation;
no polynomial symmetry or all-level degree is assumed.
-/
namespace Dubon2026.SourceFunctionField
noncomputable section
open Polynomial

theorem prime_product_forward_root (p : ℕ) [Fact p.Prime]
    (K : Type*) [Field K] [Algebra ℚ K] (ζ : Kˣ)
    (P : Polynomial (Polynomial ℤ))
    (hP : P.map (((coeffEmb K).comp (qExpand ℚ p)).comp evalAtJ) =
      PhiGen.phiProd p (PhiGen.conj p ζ)) :
    P.eval₂ evalAtJ (qExpand ℚ p jq) = 0 := by
  let H := (coeffEmb K).comp (qExpand ℚ p)
  have hroot := PhiGen.phiProd_eval_conj p (PhiGen.conj p ζ) 0
  rw [← hP, Polynomial.eval_map] at hroot
  have he : H (qExpand ℚ p jq) = PhiGen.conj p ζ 0 := by
    change coeffEmb K (qExpand ℚ p (qExpand ℚ p jq)) = _
    rw [qExpand_qExpand, PhiGen.conj_zero]
    exact coeffMap_qExpand (algebraMap ℚ K) (p * p) jq
  apply H.injective
  rw [map_zero, Polynomial.hom_eval₂, he]
  exact hroot

theorem prime_product_reverse_root (p : ℕ) [Fact p.Prime]
    (K : Type*) [Field K] [Algebra ℚ K] (ζ : Kˣ)
    (P : Polynomial (Polynomial ℤ))
    (hP : P.map (((coeffEmb K).comp (qExpand ℚ p)).comp evalAtJ) =
      PhiGen.phiProd p (PhiGen.conj p ζ)) :
    P.eval₂ ((qExpand ℚ p).comp evalAtJ) jq = 0 := by
  have hroot := PhiGen.phiProd_eval_conj p (PhiGen.conj p ζ) (Fin.succ (0 : Fin p))
  rw [← hP, Polynomial.eval_map, PhiGen.conj_succ] at hroot
  simp only [Fin.val_zero, pow_zero, qTwist_one_apply] at hroot
  apply (coeffEmb K).injective
  rw [map_zero, Polynomial.hom_eval₂]
  exact hroot

theorem exists_prime_bidirectional_relation (p : ℕ) [Fact p.Prime] :
    ∃ P : Polynomial (Polynomial ℤ), P.Monic ∧ P.natDegree = p + 1 ∧
      P.eval₂ evalAtJ (qExpand ℚ p jq) = 0 ∧
      P.eval₂ ((qExpand ℚ p).comp evalAtJ) jq = 0 := by
  obtain ⟨ζ, P, _, hPm, hdeg, hP⟩ :=
    exists_prime_product_algClosed p (AlgebraicClosure ℚ)
  exact ⟨P, hPm, hdeg, prime_product_forward_root p _ ζ P hP,
    prime_product_reverse_root p _ ζ P hP⟩

end
end Dubon2026.SourceFunctionField
