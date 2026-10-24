import Dubon2026.SourceAlgebraicValuationDimension
import Mathlib

/-! DUB-17/18 -> Picard torsion injectivity -> Kummer power lifting ->
sum-of-genera inequality -> the common residue chart has only constants.
These algebraic ingredients support that exact chart-intersection argument;
the actual joint chart consumer remains to be assembled. Adapted from the
frozen Apache-2.0 FLT source, commit
6e837e75355538c7f80bab5b956861e86c4eacc2. -/
namespace Dubon2026.SourceCurve.RegularProlongation.JointChartConstants
noncomputable section
open IsLocalRing

theorem exists_dvd_pow {R : Type*} [CommRing R] [IsDomain R] [IsLocalRing R] [Ring.KrullDimLE 1 R]
    {b : R} (hb : b ≠ 0) {c : R} (hc : c ∈ maximalIdeal R) : ∃ n : ℕ, b ∣ c ^ n := by
  by_cases hu : IsUnit b
  · exact ⟨0, hu.dvd⟩
  · have hne : Ideal.span {b} ≠ ⊤ := by
      rwa [Ne, Ideal.span_singleton_eq_top]
    have hrad : (Ideal.span {b}).radical = maximalIdeal R := by
      rw [Ideal.radical_eq_sInf]
      refine le_antisymm (sInf_le ⟨IsLocalRing.le_maximalIdeal hne, inferInstance⟩) (le_sInf ?_)
      rintro J ⟨hJ, hJp⟩
      have hJ0 : J ≠ ⊥ := by
        intro h0
        rw [h0, Ideal.span_singleton_le_iff_mem, Ideal.mem_bot] at hJ
        exact hb hJ
      exact (IsLocalRing.eq_maximalIdeal (hJp.isMaximal_of_ne_bot hJ0)).ge
    have hc' : c ∈ (Ideal.span {b}).radical := hrad ▸ hc
    obtain ⟨n, hn⟩ := hc'
    exact ⟨n, Ideal.mem_span_singleton.mp hn⟩

theorem algebraicClosure_rat_nonunit_power_dvd
    (A : ValuationSubring (AlgebraicClosure ℚ)) {b : A} (hb : b ≠ 0)
    {c : A} (hc : c ∈ IsLocalRing.maximalIdeal A) : ∃ n : ℕ, b ∣ c ^ n := by
  letI := Dubon2026.SourceCurve.algebraicClosure_rat_valuation_krullDimLE_one A
  exact exists_dvd_pow hb hc

end
end Dubon2026.SourceCurve.RegularProlongation.JointChartConstants
