import Dubon2026.SourceJointChartIntegralPartialFractions

/-! DUB-17/18 -> Kummer power lifting -> finite overlap -> two-chart
decomposition. Split every integral-numerator fraction with monomial residue
denominator into good-denominator fractions in the two coordinate charts.
Integral Bezout and monic division replace the external recursive IsLam/InM
framework; reflection identifies the inverse chart exactly. -/
namespace Dubon2026.SourceCurve.RegularProlongation.JointChartConstants
noncomputable section
open Polynomial

theorem exists_two_chart_fraction_decomposition
    {L : Type} [Field L] [IsAlgClosed L] (A : ValuationSubring L)
    {F : Type*} [Field F] [Algebra L F] (f : F) (hf : Transcendental L f)
    (p t : L[X]) (hp : ∀ k, p.coeff k ∈ A) {d : ℕ} (ht : IsGoodAt A d t) :
    ∃ p₁ t₁ q s : L[X], (∀ k, p₁.coeff k ∈ A) ∧ (∀ k, q.coeff k ∈ A) ∧
      IsGood A t₁ ∧ IsGood A s ∧
      aeval f p / aeval f t = aeval f p₁ / aeval f t₁ + aeval f⁻¹ q / aeval f⁻¹ s := by
  classical
  obtain ⟨u, a, b, hu, hui, ha, hgooda, hgoodb, hfac⟩ := exists_monic_good_factors A ht
  have hlift (v : L[X]) (hv : ∀ k, v.coeff k ∈ A) : ∃ vA : A[X], vA.map A.subtype = v := by
    apply (Polynomial.mem_lifts v).mp
    apply (Polynomial.lifts_iff_coeff_lifts v).mpr
    exact fun k => ⟨⟨_, hv k⟩, rfl⟩
  obtain ⟨aA, haA⟩ := hlift a hgooda.coeff_mem
  obtain ⟨bA, hbA⟩ := hlift b (show IsGoodAt A 0 b from hgoodb).coeff_mem
  obtain ⟨pA, hpA⟩ := hlift (C u⁻¹ * p) (fun k => by
    rw [coeff_C_mul]
    exact mul_mem hui (hp k))
  have hmon : aA.Monic := Polynomial.monic_of_injective Subtype.val_injective (by rwa [haA])
  obtain ⟨P, r, hrdeg, hPr⟩ := exists_integral_partial_fraction_numerators A pA aA bA hmon
    (by rwa [hbA])
  let P₁ := P.map A.subtype
  let r₁ := r.map A.subtype
  have hdec : C u⁻¹ * p = P₁ * a + r₁ * b := by
    have hh := congrArg (Polynomial.map A.subtype) hPr
    simpa only [Polynomial.map_add, Polynomial.map_mul, hpA, haA, hbA] using hh
  have hrbound : r₁.natDegree ≤ a.natDegree := by
    rw [← haA]
    simpa only [r₁, natDegree_map_eq_of_injective (f := A.subtype) Subtype.val_injective] using hrdeg
  have hf0 : f ≠ 0 := fun h => hf (h ▸ isAlgebraic_zero)
  have haeval : aeval f a ≠ 0 := fun h => ha.ne_zero (transcendental_iff.mp hf _ h)
  have hbeval : aeval f b ≠ 0 := fun h => hgoodb.ne_zero A (transcendental_iff.mp hf _ h)
  have hueval : algebraMap L F u ≠ 0 := by
    simpa only [map_zero] using (algebraMap L F).injective.ne hu
  have hfrac : aeval f p / aeval f t = aeval f P₁ / aeval f b + aeval f r₁ / aeval f a := by
    have he := congrArg (aeval f) hdec
    simp only [map_mul, map_add, aeval_C, map_inv₀] at he
    rw [hfac, map_mul, map_mul, aeval_C]
    field_simp
    field_simp at he
    linear_combination he
  let q := reflect a.natDegree r₁
  let s := reflect a.natDegree a
  have hqeval : aeval f⁻¹ q = aeval f r₁ * f⁻¹ ^ a.natDegree := by
    simpa only [inv_inv] using aeval_reflect_eq (inv_ne_zero hf0) r₁ hrbound
  have hseval : aeval f⁻¹ s = aeval f a * f⁻¹ ^ a.natDegree := by
    simpa only [inv_inv] using aeval_reflect_eq (inv_ne_zero hf0) a le_rfl
  refine ⟨P₁, b, q, s, ?_, ?_, hgoodb, good_reflect_top hgooda, ?_⟩
  · intro k
    change (P.map A.subtype).coeff k ∈ A
    rw [coeff_map]
    exact (P.coeff k).2
  · intro k
    change (reflect a.natDegree (r.map A.subtype)).coeff k ∈ A
    rw [coeff_reflect, coeff_map]
    exact (r.coeff _).2
  · rw [hfrac, hqeval, hseval, mul_div_mul_right _ _ (pow_ne_zero _ (inv_ne_zero hf0))]

end
end Dubon2026.SourceCurve.RegularProlongation.JointChartConstants
