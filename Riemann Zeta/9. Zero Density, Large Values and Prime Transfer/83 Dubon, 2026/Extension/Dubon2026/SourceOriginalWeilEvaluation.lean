import Dubon2026.SourceOriginalPlaceInverseValues
import Dubon2026.SourceCurveDivisorDegree
import Mathlib.Algebra.BigOperators.Finsupp.Basic

/-! DUB-17/18 -> original primitive-form Frobenius determinant ->
arithmetic Weil pairing on original Picard torsion -> literal function
evaluation on divisors with disjoint support. Reuse the proved original
residue identification, including its pole convention, and native finite
products. The required nonvanishing and multiplicativity are proved here;
reciprocity, quotient descent and nondegeneracy remain separate obligations.
Adapted from Def_AlgebraicCurve_PlaceEvaluation and PlaceEvaluationAlgebra,
anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2. -/
namespace Dubon2026.SourceFunctionField
noncomputable section
open SourceCurve
variable (N : ℕ) [NeZero N] (L : Type*) [Field L] [Algebra ℚ L] [IsAlgClosed L]
local notation "FF" => modularFunctionFieldOver N L

theorem originalPlaceEval_one (v : Place L FF) : originalPlaceEval N L v 1 = 1 := by
  simpa only [map_one] using originalPlaceEval_algebraMap N L v 1

theorem originalPlaceEval_mul_of_mem (v : Place L FF) {f g : FF}
    (hf : f ∈ v.toValuationSubring) (hg : g ∈ v.toValuationSubring) :
    originalPlaceEval N L v (f * g) = originalPlaceEval N L v f * originalPlaceEval N L v g := by
  rw [originalPlaceEval_of_mem N L v (mul_mem hf hg),
    originalPlaceEval_of_mem N L v hf, originalPlaceEval_of_mem N L v hg]
  exact (originalPlaceRegularEval N L v).map_mul ⟨f, hf⟩ ⟨g, hg⟩

theorem originalPlaceEval_ne_zero_of_ord_eq_zero (v : Place L FF) {f : FF}
    (hf : f ≠ 0) (ho : v.ord f = 0) : originalPlaceEval N L v f ≠ 0 := by
  intro hz
  have hp := (originalPlaceEval_eq_zero_iff_ord_pos N L v
    (v.mem_of_ord_nonneg ho.ge) hf).mp hz
  rw [ho] at hp
  exact (lt_irrefl 0) hp

/-- Literal evaluation of an original rational function on an integer divisor. -/
def originalDivisorEval (f : FF) (D : Divisor L FF) : L :=
  D.prod fun v n => originalPlaceEval N L v f ^ n

theorem originalDivisorEval_zero (f : FF) : originalDivisorEval N L f 0 = 1 :=
  Finsupp.prod_zero_index

theorem originalDivisorEval_single (f : FF) (v : Place L FF) (n : ℤ) :
    originalDivisorEval N L f (Finsupp.single v n) = originalPlaceEval N L v f ^ n := by
  exact Finsupp.prod_single_index (zpow_zero _)

theorem originalDivisorEval_ne_zero (f : FF) (hf : f ≠ 0) (D : Divisor L FF)
    (hD : ∀ v ∈ D.support, v.ord f = 0) : originalDivisorEval N L f D ≠ 0 := by
  classical
  apply Finsupp.prod_ne_zero_iff.mpr
  intro v hv
  exact zpow_ne_zero _ (originalPlaceEval_ne_zero_of_ord_eq_zero N L v hf (hD v hv))

theorem originalDivisorEval_mul (f g : FF) (D : Divisor L FF)
    (hf : ∀ v ∈ D.support, f ∈ v.toValuationSubring)
    (hg : ∀ v ∈ D.support, g ∈ v.toValuationSubring) :
    originalDivisorEval N L (f * g) D = originalDivisorEval N L f D * originalDivisorEval N L g D := by
  classical
  simp only [originalDivisorEval, Finsupp.prod]
  rw [← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun v hv => by
    rw [originalPlaceEval_mul_of_mem N L v (hf v hv) (hg v hv), mul_zpow]

theorem originalDivisorEval_add (f : FF) (D E : Divisor L FF)
    (h : ∀ v, v ∈ D.support ∨ v ∈ E.support → originalPlaceEval N L v f ≠ 0) :
    originalDivisorEval N L f (D + E) = originalDivisorEval N L f D * originalDivisorEval N L f E := by
  classical
  exact Finsupp.prod_add_index (fun _ _ => zpow_zero _)
    (fun v hv a b => zpow_add₀ (h v (Finset.mem_union.mp hv)) a b)

end
end Dubon2026.SourceFunctionField
