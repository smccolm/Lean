import Dubon2026.SourceJointChartGoodPolynomials

/-! DUB-17/18 -> Picard torsion injectivity -> Kummer power lifting ->
sum-of-genera inequality -> the common residue chart has only constants.
These algebraic ingredients support that exact chart-intersection argument;
the actual joint chart consumer remains to be assembled. Adapted from the
frozen Apache-2.0 FLT source, commit
6e837e75355538c7f80bab5b956861e86c4eacc2. -/
namespace Dubon2026.SourceCurve.RegularProlongation.JointChartConstants
noncomputable section
open Polynomial

variable {L : Type*} [Field L] (A : ValuationSubring L)


variable {F : Type*} [Field F] [Algebra L F]

omit A in

theorem valuation_algebraMap_eq_one (V : ValuationSubring F) (hV : ∀ c : L, algebraMap L F c ∈ V)
    {c : L} (hc : c ≠ 0) : V.valuation (algebraMap L F c) = 1 := by
  have h1 : V.valuation (algebraMap L F c) ≤ 1 := (V.valuation_le_one_iff _).mpr (hV c)
  have h2 : V.valuation (algebraMap L F c⁻¹) ≤ 1 := (V.valuation_le_one_iff _).mpr (hV c⁻¹)
  have h3 : V.valuation (algebraMap L F c) * V.valuation (algebraMap L F c⁻¹) = 1 := by
    rw [← map_mul, ← map_mul, mul_inv_cancel₀ hc, map_one, map_one]
  apply le_antisymm h1
  by_contra hlt
  push Not at hlt
  have : V.valuation (algebraMap L F c) * V.valuation (algebraMap L F c⁻¹) < 1 :=
    calc V.valuation (algebraMap L F c) * V.valuation (algebraMap L F c⁻¹)
        ≤ V.valuation (algebraMap L F c) * 1 := by gcongr
      _ < 1 := by rw [mul_one]; exact hlt
  rw [h3] at this
  exact lt_irrefl _ this

omit A in
theorem valuation_algebraMap_le_one (V : ValuationSubring F) (hV : ∀ c : L, algebraMap L F c ∈ V)
    (c : L) : V.valuation (algebraMap L F c) ≤ 1 :=
  (V.valuation_le_one_iff _).mpr (hV c)

theorem valuation_aeval_eq_one_of_lt (V : ValuationSubring F) (hV : ∀ c : L, algebraMap L F c ∈ V)
    {g : F} (hg : V.valuation g < 1) {t : L[X]} (ht : IsGood A t) :
    V.valuation (aeval g t) = 1 := by
  rw [aeval_eq_sum_range, Finset.sum_range_succ']
  simp only [pow_zero, Algebra.smul_def, mul_one]
  have h0 : V.valuation (algebraMap L F (t.coeff 0)) = 1 :=
    valuation_algebraMap_eq_one V hV (ht.coeff_zero_ne A)
  rw [Valuation.map_add_eq_of_lt_right]
  · exact h0
  · rw [h0]
    apply Valuation.map_sum_lt _ one_ne_zero
    intro j _
    rw [map_mul, map_pow]
    calc V.valuation (algebraMap L F (t.coeff (j + 1))) * V.valuation g ^ (j + 1)
        ≤ 1 * V.valuation g ^ (j + 1) := by gcongr; exact valuation_algebraMap_le_one V hV _
      _ < 1 := by rw [one_mul]; exact pow_lt_one₀ zero_le' hg (Nat.succ_ne_zero j)

theorem valuation_aeval_eq_one_of_sub_lt (V : ValuationSubring F)
    (hV : ∀ c : L, algebraMap L F c ∈ V) {g : F} {c : L} (hc : A.valuation c < 1)
    (hgc : V.valuation (g - algebraMap L F c) < 1) {t : L[X]} (ht : IsGood A t) :
    V.valuation (aeval g t) = 1 := by
  have hg1 : V.valuation g ≤ 1 := by
    have : g = (g - algebraMap L F c) + algebraMap L F c := by ring
    rw [this]
    exact (V.valuation.map_add _ _).trans (max_le hgc.le (valuation_algebraMap_le_one V hV c))

  have hev : V.valuation (algebraMap L F (t.eval c)) = 1 := by
    apply valuation_algebraMap_eq_one V hV
    intro h0
    have := ht.valuation_eval_eq_one A hc
    rw [h0, map_zero] at this
    exact zero_ne_one this
  have hdiff : aeval g t - algebraMap L F (t.eval c) =
      ∑ j ∈ Finset.range (t.natDegree + 1),
        algebraMap L F (t.coeff j) * (g ^ j - algebraMap L F c ^ j) := by
    rw [aeval_eq_sum_range, eval_eq_sum_range, map_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Algebra.smul_def, map_mul, map_pow, mul_sub]
  have hlt : V.valuation (aeval g t - algebraMap L F (t.eval c)) < 1 := by
    rw [hdiff]
    apply Valuation.map_sum_lt _ one_ne_zero
    intro j _
    rw [map_mul]
    have hpow : V.valuation (g ^ j - algebraMap L F c ^ j) < 1 := by
      rw [← geom_sum₂_mul, map_mul]
      have hs : V.valuation (∑ i ∈ Finset.range j, g ^ i * algebraMap L F c ^ (j - 1 - i)) ≤ 1 := by
        apply Valuation.map_sum_le
        intro i _
        rw [map_mul, map_pow, map_pow]
        calc V.valuation g ^ i * V.valuation (algebraMap L F c) ^ (j - 1 - i) ≤ 1 * 1 := by
              gcongr
              · exact pow_le_one₀ zero_le' hg1
              · exact pow_le_one₀ zero_le' (valuation_algebraMap_le_one V hV c)
          _ = 1 := one_mul 1
      calc V.valuation (∑ i ∈ Finset.range j, g ^ i * algebraMap L F c ^ (j - 1 - i)) *
            V.valuation (g - algebraMap L F c) ≤ 1 * V.valuation (g - algebraMap L F c) := by
            gcongr
        _ < 1 := by rw [one_mul]; exact hgc
    calc V.valuation (algebraMap L F (t.coeff j)) * V.valuation (g ^ j - algebraMap L F c ^ j)
        ≤ 1 * V.valuation (g ^ j - algebraMap L F c ^ j) := by
          gcongr; exact valuation_algebraMap_le_one V hV _
      _ < 1 := by rw [one_mul]; exact hpow
  have : aeval g t = algebraMap L F (t.eval c) + (aeval g t - algebraMap L F (t.eval c)) := by ring
  rw [this, Valuation.map_add_eq_of_lt_left _ (by rw [hev]; exact hlt), hev]

theorem mem_of_forall [IsAlgClosed L] {f : F} (hf : Transcendental L f) {t t' : L[X]}
    (ht : IsGood A t) (ht' : IsGood A t') {x : F}
    (hx : ∀ V : ValuationSubring F, (∀ c : L, algebraMap L F c ∈ V) → f ∈ V → x * aeval f t ∈ V)
    (hx' : ∀ V : ValuationSubring F, (∀ c : L, algebraMap L F c ∈ V) → f⁻¹ ∈ V →
      x * aeval f⁻¹ t' ∈ V)
    (V : ValuationSubring F) (hV : ∀ c : L, algebraMap L F c ∈ V) : x ∈ V := by
  classical
  have hf0 : f ≠ 0 := fun h => hf (h ▸ isAlgebraic_zero)

  have key : ∀ d : F, V.valuation d = 1 → x * d ∈ V → x ∈ V := by
    intro d hd hxd
    rw [← V.valuation_le_one_iff] at hxd ⊢
    rw [map_mul, hd, mul_one] at hxd
    exact hxd
  rcases lt_trichotomy (V.valuation f) 1 with hlt | heq | hgt
  ·
    exact key _ (valuation_aeval_eq_one_of_lt A V hV hlt ht)
      (hx V hV ((V.valuation_le_one_iff _).mp hlt.le))
  ·
    have hfV : f ∈ V := (V.valuation_le_one_iff _).mp heq.le
    have hfiV : f⁻¹ ∈ V := (V.valuation_le_one_iff _).mp (by rw [map_inv₀, heq, inv_one])
    obtain ⟨u, cs, hu0, hcs, htfac⟩ := ht.exists_eq_C_mul_prod A
    by_cases hunit : ∀ c ∈ cs, V.valuation (1 - algebraMap L F c * f) = 1
    ·
      apply key _ ?_ (hx V hV hfV)
      rw [htfac, map_mul, aeval_C, map_mul, valuation_algebraMap_eq_one V hV hu0, one_mul,
        map_multiset_prod, Multiset.map_map, map_multiset_prod, Multiset.map_map]
      apply Multiset.prod_eq_one
      intro v hv
      rw [Multiset.mem_map] at hv
      obtain ⟨c, hc, rfl⟩ := hv
      simp only [Function.comp_apply, map_sub, map_one, map_mul, aeval_C, aeval_X]
      exact hunit c hc
    ·
      push Not at hunit
      obtain ⟨c, hc, hne⟩ := hunit
      have hle : V.valuation (1 - algebraMap L F c * f) ≤ 1 :=
        (V.valuation_le_one_iff _).mpr (sub_mem V.one_mem (mul_mem (hV c) hfV))
      have hlt : V.valuation (1 - algebraMap L F c * f) < 1 := lt_of_le_of_ne hle hne
      have hcA := hcs c hc
      have hc0 : c ≠ 0 := by
        rintro rfl
        rw [map_zero, zero_mul, sub_zero, map_one] at hlt
        exact lt_irrefl _ hlt

      have hsub : V.valuation (f⁻¹ - algebraMap L F c) < 1 := by
        have : f⁻¹ - algebraMap L F c = f⁻¹ * (1 - algebraMap L F c * f) := by
          field_simp
        rw [this, map_mul, map_inv₀, heq, inv_one, one_mul]
        exact hlt
      exact key _ (valuation_aeval_eq_one_of_sub_lt A V hV hcA hsub ht') (hx' V hV hfiV)
  ·
    have hlt : V.valuation f⁻¹ < 1 := by
      rw [map_inv₀]; exact inv_lt_one_of_one_lt₀ hgt
    exact key _ (valuation_aeval_eq_one_of_lt A V hV hlt ht')
      (hx' V hV ((V.valuation_le_one_iff _).mp hlt.le))


end
end Dubon2026.SourceCurve.RegularProlongation.JointChartConstants
