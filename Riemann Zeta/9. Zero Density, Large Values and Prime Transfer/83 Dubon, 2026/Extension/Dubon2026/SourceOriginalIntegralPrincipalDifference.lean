import Dubon2026.SourceModularPrimitiveFractionForm
import Dubon2026.SourceResidueOriginalSpecialization
import Dubon2026.SourceOriginalPrincipalDivisors
import Dubon2026.SourceOriginalCoefficientPlaceAction

/-! DUB-17/18 -> Hecke compatibility on torsion -> principal agreement.
Reuse the proved primitive fraction decomposition in the actual original
field. Constants have zero order, so every principal divisor is a difference
of two integral Laurent principal divisors with nonzero reductions. -/
namespace Dubon2026.SourceFunctionField
noncomputable section
open SourceCurve GaussReduction
local notation "L" => AlgebraicClosure ℚ
variable (A : ValuationSubring L) (N : ℕ) [NeZero N]
local notation "FF" => modularFunctionFieldOver N L

omit [NeZero N] in
theorem original_integral_fraction_form (f : FF) (hf : f ≠ 0) :
    ∃ (c : L), c ≠ 0 ∧ ∃ (x y : LaurentSeries A)
      (_hx : coeffMap A.subtype x ∈ FF) (_hy : coeffMap A.subtype y ∈ FF),
      coeffMap (IsLocalRing.residue A) x ≠ 0 ∧
      coeffMap (IsLocalRing.residue A) y ≠ 0 ∧
      (f : LaurentSeries L) * coeffMap A.subtype y =
        algebraMap L (LaurentSeries L) c * coeffMap A.subtype x := by
  let fc := originalCoefficientEquiv N f
  have hfc : fc ≠ 0 := (map_ne_zero (originalCoefficientEquiv N)).mpr hf
  obtain ⟨c, hc, x, y, hrx, hry, hxc, hyc, hprod⟩ := exists_frac_form A N fc hfc
  have hx : ι A x ∈ FF := ((originalCoefficientEquiv N).symm ⟨ι A x, hxc⟩).property
  have hy : ι A y ∈ FF := ((originalCoefficientEquiv N).symm ⟨ι A y, hyc⟩).property
  exact ⟨c, hc, x, y, hx, hy, hrx, hry, hprod⟩

theorem original_principal_difference_of_mul_eq (f x y : FF)
    (hf : f ≠ 0) (hx : x ≠ 0) (hy : y ≠ 0)
    (c : L) (hc : c ≠ 0) (he : f * y = algebraMap L FF c * x) :
    originalPrincipalDivisor N L f =
      originalPrincipalDivisor N L x - originalPrincipalDivisor N L y := by
  ext P
  change P.ord f = P.ord x - P.ord y
  have ho := congrArg P.ord he
  rw [P.ord_mul hf hy, P.ord_mul ((map_ne_zero (algebraMap L FF)).mpr hc) hx,
    P.ord_algebraMap, zero_add] at ho
  omega

theorem original_principal_divisor_integral_difference (f : FF) (hf : f ≠ 0) :
    ∃ (x y : LaurentSeries A)
      (hx : coeffMap A.subtype x ∈ FF) (hy : coeffMap A.subtype y ∈ FF),
      coeffMap (IsLocalRing.residue A) x ≠ 0 ∧
      coeffMap (IsLocalRing.residue A) y ≠ 0 ∧
      originalPrincipalDivisor N L f =
        originalPrincipalDivisor N L ⟨coeffMap A.subtype x, hx⟩ -
          originalPrincipalDivisor N L ⟨coeffMap A.subtype y, hy⟩ := by
  obtain ⟨c, hc, x, y, hx, hy, hrx, hry, he⟩ := original_integral_fraction_form A N f hf
  have hx0 : (⟨coeffMap A.subtype x, hx⟩ : FF) ≠ 0 := fun h => (ϖ_ne_zero_ne_zero hrx)
    ((ι_eq_zero_iff A x).mp (congrArg Subtype.val h))
  have hy0 : (⟨coeffMap A.subtype y, hy⟩ : FF) ≠ 0 := fun h => (ϖ_ne_zero_ne_zero hry)
    ((ι_eq_zero_iff A y).mp (congrArg Subtype.val h))
  exact ⟨x, y, hx, hy, hrx, hry,
    original_principal_difference_of_mul_eq N f _ _ hf hx0 hy0 c hc (Subtype.ext he)⟩

end
end Dubon2026.SourceFunctionField
