import Dubon2026.SourceCurveLocalPrincipalParts

/-! Pure poles for a specified order-one parameter, using the existing
valuation proof of pole independence. The rational residue theorem needs
the actual coordinates X-c and 1/X, rather than a chosen DVR generator.
This is the local normalization input to DUB-17/18 global residue vanishing. -/

namespace Dubon2026.SourceCurve.Place
noncomputable section
variable {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)

/-- An actual order-one parameter is nonzero. -/
theorem parameter_ne_zero {t : F} (ht : v.ord t = 1) : t ≠ 0 := by
  intro h
  rw [h, v.ord_zero] at ht
  exact zero_ne_one ht

/-- The class of a pure pole modulo functions integral at the place. -/
def parameterPoleClass (t : F) (n : ℕ) : F ⧸ v.integralFunctions :=
  Submodule.Quotient.mk (t ^ (-(n + 1 : ℤ)))

variable {t : F}

theorem valuation_smul_parameter_neg_pow (ht : v.ord t = 1) {c : K} (hc : c ≠ 0) (n : ℕ) :
    v.adicValuation (c • t ^ (-(n + 1 : ℤ))) =
      WithZero.exp (n + 1 : ℤ) := by
  rw [Algebra.smul_def, Valuation.map_mul,
    v.adicValuation_eq_exp_neg_ord (by simpa using hc : algebraMap K F c ≠ 0),
    v.ord_eq_zero_of_isAlgebraic (isAlgebraic_algebraMap c), neg_zero,
    WithZero.exp_zero, one_mul,
    v.adicValuation_eq_exp_neg_ord (zpow_ne_zero _ (v.parameter_ne_zero ht)),
    v.ord_zpow, ht, mul_one, neg_neg]

theorem parameterPoleClass_linearIndependent (ht : v.ord t = 1) :
    LinearIndependent K (v.parameterPoleClass t) := by
  classical
  rw [linearIndependent_iff']
  intro s a hsum i hi
  by_contra hai
  let indices := s.filter fun j => a j ≠ 0
  have hindices : indices.Nonempty := ⟨i, Finset.mem_filter.mpr ⟨hi, hai⟩⟩
  let j := indices.max' hindices
  have hj : j ∈ indices := Finset.max'_mem indices hindices
  have haj : a j ≠ 0 := (Finset.mem_filter.mp hj).2
  have hval : v.adicValuation (∑ k ∈ indices, a k • t ^ (-(k + 1 : ℤ))) =
      WithZero.exp (j + 1 : ℤ) := by
    rw [v.adicValuation.map_sum_eq_of_lt hj]
    · exact v.valuation_smul_parameter_neg_pow ht haj j
    · intro k hk
      have hkt := (Finset.mem_sdiff.mp hk).1
      have hkj : k ≠ j := by simpa using (Finset.mem_sdiff.mp hk).2
      have hklt : k < j := lt_of_le_of_ne (Finset.le_max' indices k hkt) hkj
      rw [v.valuation_smul_parameter_neg_pow ht (Finset.mem_filter.mp hkt).2,
        v.valuation_smul_parameter_neg_pow ht haj]
      exact WithZero.exp_lt_exp.mpr (by omega)
  have hs : (∑ k ∈ indices, a k • t ^ (-(k + 1 : ℤ))) =
      ∑ k ∈ s, a k • t ^ (-(k + 1 : ℤ)) := by
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro k hk hkt
    have hk0 : a k = 0 := by simpa [indices, hk] using hkt
    simp only [hk0, zero_smul]
  have hmem : (∑ k ∈ indices, a k • t ^ (-(k + 1 : ℤ))) ∈
      v.integralFunctions := by
    rw [hs, ← Submodule.Quotient.mk_eq_zero]
    change v.integralFunctions.mkQ (∑ k ∈ s, a k • t ^ (-(k + 1 : ℤ))) = 0
    simpa only [map_sum, map_smul, Submodule.mkQ_apply, parameterPoleClass] using hsum
  have hle := v.adicValuation_le_one_of_mem hmem
  rw [hval] at hle
  have hgt : (1 : WithZero (Multiplicative ℤ)) < WithZero.exp (j + 1 : ℤ) := by
    rw [← WithZero.exp_zero]
    exact WithZero.exp_lt_exp.mpr (by omega)
  exact (not_lt_of_ge hle) hgt

end
end Dubon2026.SourceCurve.Place
