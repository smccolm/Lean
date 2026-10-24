import Dubon2026.SourceJointChartUnitPolynomialBounds
import Dubon2026.SourceValuationIntegralCriterion

/-! DUB-17/18 -> Picard torsion injectivity -> Kummer power lifting ->
sum-of-genera inequality -> the common residue chart has only constants.
These algebraic ingredients support that exact chart-intersection argument;
the actual joint chart consumer remains to be assembled. Adapted from the
frozen Apache-2.0 FLT source, commit
6e837e75355538c7f80bab5b956861e86c4eacc2. -/
namespace Dubon2026.SourceCurve.RegularProlongation.JointChartConstants
noncomputable section
open Polynomial

theorem exists_eq_algebraMap_of_forall_mem
    {L F : Type*} [Field L] [Field F] [Algebra L F] [IsAlgClosed L] {x : F}
    (hx : ∀ V : ValuationSubring F, (∀ c : L, algebraMap L F c ∈ V) → x ∈ V) :
    ∃ c : L, x = algebraMap L F c := by
  have hint := ConstantField.isIntegral_of_forall_mem_valuationSubring x hx
  have h1 : (minpoly L x).degree = 1 :=
    IsAlgClosed.degree_eq_one_of_irreducible L (minpoly.irreducible hint)
  have h0 := minpoly.aeval L x
  rw [Polynomial.eq_X_add_C_of_degree_eq_one h1,
    show (minpoly L x).leadingCoeff = 1 from minpoly.monic hint,
    Polynomial.C_1, one_mul, Polynomial.aeval_add, Polynomial.aeval_X,
    Polynomial.aeval_C, add_eq_zero_iff_eq_neg] at h0
  exact ⟨-(minpoly L x).coeff 0, by rw [map_neg]; exact h0⟩

theorem constant_of_unit_polynomial_chart_bounds
    {L : Type*} [Field L] [IsAlgClosed L] (A : ValuationSubring L)
    {F : Type*} [Field F] [Algebra L F] {f : F} (hf : Transcendental L f)
    (t t' : L[X]) (ht : IsGood A t) (ht' : IsGood A t') (x : F)
    (hx : ∀ V : ValuationSubring F, (∀ c : L, algebraMap L F c ∈ V) → f ∈ V →
      x * aeval f t ∈ V)
    (hx' : ∀ V : ValuationSubring F, (∀ c : L, algebraMap L F c ∈ V) → f⁻¹ ∈ V →
      x * aeval f⁻¹ t' ∈ V) : ∃ c : L, x = algebraMap L F c :=
  exists_eq_algebraMap_of_forall_mem (mem_of_forall A hf ht ht' hx hx')

end
end Dubon2026.SourceCurve.RegularProlongation.JointChartConstants
