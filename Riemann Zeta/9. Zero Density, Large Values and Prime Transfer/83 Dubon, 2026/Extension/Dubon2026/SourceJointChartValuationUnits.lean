import Dubon2026.SourceJointChartIntegralAlgebras
import Dubon2026.SourceJointChartMonomialDenominators

/-! DUB-17/18 -> original-field Kummer power lifting -> genus inequality ->
common residue-chart constants. These localizations use denominators whose
reduction is a nonzero monomial. They provide the two charts and overlap
needed by the already proved idempotent gluing theorem. Adapted from
Apache-2.0 FLT commit 6e837e75355538c7f80bab5b956861e86c4eacc2;
native integral-closure algebras replace the external chart predicate. -/
namespace Dubon2026.SourceCurve.RegularProlongation.JointChartConstants
noncomputable section
open Polynomial IsLocalRing

variable {L : Type*} [Field L] {A : ValuationSubring L}
variable {F : Type*} [Field F] [Algebra L F]
variable {Fb : Type*} [Field Fb] [Algebra (ResidueField A) Fb]
variable (R : RegularProlongation A F Fb)

theorem mem_iff_le (x : F) : x ∈ R.integers ↔ R.integers.valuation x ≤ 1 :=
  (R.integers.valuation_le_one_iff x).symm

theorem residue_eq_zero_iff {x : F} (hx : x ∈ R.integers) :
    R.residue ⟨x, hx⟩ = 0 ↔ R.integers.valuation x < 1 := by
  rw [← R.integers.valuation_lt_one_iff ⟨x, hx⟩, ← R.ker_residue, RingHom.mem_ker]

theorem valuation_algebraMap_lt {a : L} (ha : A.valuation a < 1) :
    R.integers.valuation (algebraMap L F a) < 1 := by
  have haA : a ∈ A := (A.valuation_le_one_iff a).mp ha.le
  rw [← residue_eq_zero_iff R (((R.algebraMap_mem_iff _).mpr haA))]
  have hmax : (⟨a, haA⟩ : A) ∈ maximalIdeal A := (A.valuation_lt_one_iff _).mpr ha
  have := residue_constHom R ⟨a, haA⟩
  rw [(IsLocalRing.residue_eq_zero_iff _).mpr hmax, map_zero] at this
  exact this

theorem valuation_constHom_eq_one {a : L} (ha : A.valuation a = 1) :
    R.integers.valuation (algebraMap L F a) = 1 := by
  have haA : a ∈ A := (A.valuation_le_one_iff a).mp ha.le
  have hu : IsUnit (⟨a, haA⟩ : A) := (A.valuation_eq_one_iff _).mpr ha
  have := (R.integers.valuation_eq_one_iff (constHom R ⟨a, haA⟩)).mp (hu.map (constHom R))
  simpa using this

theorem valuation_aeval_eq_one {g : F} (hg : g ∈ R.integers) {t : L[X]} (ht : IsGoodAt A 0 t) :
    R.integers.valuation (aeval g t) = 1 := by
  rw [aeval_eq_sum_range, Finset.sum_range_succ', pow_zero]
  have hmain : R.integers.valuation (t.coeff 0 • (1 : F)) = 1 := by
    rw [Algebra.smul_def, mul_one]; exact valuation_constHom_eq_one R ht.1
  have hrest : R.integers.valuation
      (∑ k ∈ Finset.range t.natDegree, t.coeff (k + 1) • g ^ (k + 1)) < 1 := by
    refine Valuation.map_sum_lt _ one_ne_zero fun k _ => ?_
    rw [Algebra.smul_def, map_mul, map_pow]
    calc R.integers.valuation (algebraMap L F (t.coeff (k + 1))) * R.integers.valuation g ^ (k + 1)
        ≤ R.integers.valuation (algebraMap L F (t.coeff (k + 1))) * 1 :=
          by gcongr; exact pow_le_one' ((mem_iff_le R g).mp hg) _
      _ < 1 := by rw [mul_one]; exact valuation_algebraMap_lt R (ht.2 _ (Nat.succ_ne_zero k))
  rw [Valuation.map_add_eq_of_lt_right _ (by rw [hmain]; exact hrest), hmain]

end
end Dubon2026.SourceCurve.RegularProlongation.JointChartConstants
