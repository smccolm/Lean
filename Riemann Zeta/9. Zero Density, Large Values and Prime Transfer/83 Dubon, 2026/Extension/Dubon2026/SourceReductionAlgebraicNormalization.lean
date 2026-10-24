import Dubon2026.SourceAlgebraicValuationPowers
import Dubon2026.SourceCurveRegularProlongation
import Mathlib.FieldTheory.IsAlgClosed.Basic

/-! DUB-17/18 -> Picard torsion injectivity -> Kummer power lifting ->
extending regular reductions. Algebraically closed constants give a short
normalization argument for every algebraic extension of the original
regular prolongation. A positive power of the extension value is a base
value; the original normalization and a constant-field root normalize the
extension element itself. This replaces the more general source argument
through arbitrary valuation coarsenings without changing the required
arithmetic modular-field contract. -/
namespace Dubon2026.SourceCurve.RegularProlongation
noncomputable section
variable {L F Fbar E : Type*} [Field L] [IsAlgClosed L] {A : ValuationSubring L}
  [Field F] [Algebra L F] [Field Fbar] [Algebra (IsLocalRing.ResidueField A) Fbar]
  [Field E] [Algebra F E] [Algebra L E] [IsScalarTower L F E]

theorem exists_smul_valuation_eq_one_of_isIntegral
    (R : RegularProlongation A F Fbar) (V : ValuationSubring E)
    (hV : V.comap (algebraMap F E) = R.integers)
    {x : E} (hx : x ≠ 0) (hint : IsIntegral F x) :
    ∃ c : L, V.valuation (c • x) = 1 := by
  obtain ⟨n, a, hn, ha, hpow⟩ := exists_valuation_pow_eq_of_isIntegral V.valuation hx hint
  obtain ⟨c, hc, hcres⟩ := R.exists_smul_mem a ha
  let incl : R.integers →+* V :=
    { toFun := fun y => ⟨algebraMap F E (y : F), by
        rw [← ValuationSubring.mem_comap, hV]
        exact y.2⟩
      map_one' := Subtype.ext (map_one _)
      map_mul' y z := Subtype.ext (map_mul _ _ _)
      map_zero' := Subtype.ext (map_zero _)
      map_add' y z := Subtype.ext (map_add _ _ _) }
  have hunit : IsUnit (incl ⟨c • a, hc⟩) := (R.isUnit_of_residue_ne_zero hcres).map incl
  have hnorm := (V.valuation_eq_one_iff _).mp hunit
  change V.valuation (algebraMap F E (c • a)) = 1 at hnorm
  rw [Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply L F E, map_mul] at hnorm
  obtain ⟨b, hb⟩ := IsAlgClosed.exists_pow_nat_eq c hn
  refine ⟨b, ?_⟩
  apply (pow_eq_one_iff_of_nonneg zero_le' hn.ne').mp
  rw [Algebra.smul_def, map_mul, mul_pow, ← map_pow, ← map_pow, hb, hpow]
  exact hnorm

end
end Dubon2026.SourceCurve.RegularProlongation
