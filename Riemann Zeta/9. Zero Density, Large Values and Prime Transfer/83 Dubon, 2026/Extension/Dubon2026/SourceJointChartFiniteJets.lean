import Dubon2026.SourceJointChartIntegralPartialFractions

/-! DUB-17/18 -> Kummer power lifting -> finite overlap. Integral Bezout
with the monic polynomial X^m and division produce a finite polynomial jet
of a good-denominator fraction. The remainder has degree at most m; this
gives the finite Laurent window without a separate recursive framework. -/
namespace Dubon2026.SourceCurve.RegularProlongation.JointChartConstants
noncomputable section
open Polynomial

theorem exists_good_fraction_finite_jet
    {L : Type} [Field L] (A : ValuationSubring L)
    {F : Type*} [Field F] [Algebra L F] (g : F) (hg : Transcendental L g)
    (p t : L[X]) (hp : ∀ k, p.coeff k ∈ A) (ht : IsGood A t) (m : ℕ) :
    ∃ r q : L[X], (∀ k, r.coeff k ∈ A) ∧ (∀ k, q.coeff k ∈ A) ∧
      r.natDegree ≤ m ∧
      aeval g p / aeval g t = aeval g r + g ^ m * (aeval g q / aeval g t) := by
  have hlift (v : L[X]) (hv : ∀ k, v.coeff k ∈ A) : ∃ vA : A[X], vA.map A.subtype = v := by
    apply (Polynomial.mem_lifts v).mp
    apply (Polynomial.lifts_iff_coeff_lifts v).mpr
    exact fun k => ⟨⟨_, hv k⟩, rfl⟩
  obtain ⟨pA, hpA⟩ := hlift p hp
  obtain ⟨tA, htA⟩ := hlift t (show IsGoodAt A 0 t from ht).coeff_mem
  obtain ⟨qA, rA, hr, he⟩ := exists_integral_partial_fraction_numerators
    A pA (X ^ m) tA (monic_X_pow m) (by rwa [htA])
  let q := qA.map A.subtype
  let r := rA.map A.subtype
  have he' : p = q * X ^ m + r * t := by
    have hh := congrArg (Polynomial.map A.subtype) he
    simpa only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_pow,
      map_X, hpA, htA] using hh
  have hat : aeval g t ≠ 0 := fun h => ht.ne_zero A (transcendental_iff.mp hg _ h)
  refine ⟨r, q, ?_, ?_, ?_, ?_⟩
  · intro k
    change (rA.map A.subtype).coeff k ∈ A
    rw [coeff_map]
    exact (rA.coeff k).2
  · intro k
    change (qA.map A.subtype).coeff k ∈ A
    rw [coeff_map]
    exact (qA.coeff k).2
  · simpa only [r, natDegree_map_eq_of_injective (f := A.subtype) Subtype.val_injective,
      natDegree_X_pow] using hr
  · have hev := congrArg (aeval g) he'
    simp only [map_add, map_mul, map_pow, aeval_X] at hev
    field_simp
    linear_combination hev

end
end Dubon2026.SourceCurve.RegularProlongation.JointChartConstants
