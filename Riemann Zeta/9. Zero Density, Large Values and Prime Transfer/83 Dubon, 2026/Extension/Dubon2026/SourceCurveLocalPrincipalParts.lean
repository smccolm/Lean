import Dubon2026.SourceCurveAdeleLocalQuotient
import Dubon2026.SourceCurveTranscendence
import Dubon2026.SourceCurveLocalDifferentials
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-! DUB-17/18 -> original regular differential dimension -> Riemann--Roch
-> residue duality -> the actual canonical local residue. Negative powers
of a uniformizer are independent modulo integral functions. A largest pole
in a finite sum cannot cancel. This supplies the coefficient functional
without introducing completion or general residue-field sections.
-/
namespace Dubon2026.SourceCurve.Place
noncomputable section
variable {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)

/-- The actual functions integral at this place, as a vector subspace. -/
def integralFunctions : Submodule K F where
  carrier := v.toValuationSubring
  zero_mem' := zero_mem _
  add_mem' := add_mem
  smul_mem' c f hf := by
    rw [Algebra.smul_def]
    exact mul_mem (v.algebraMap_mem' c) hf

/-- The class of a pure pole modulo functions integral at the place. -/
def poleClass (n : ℕ) : F ⧸ v.integralFunctions :=
  Submodule.Quotient.mk (v.uniformizer ^ (-(n + 1 : ℤ)))

theorem valuation_smul_uniformizer_neg_pow {c : K} (hc : c ≠ 0) (n : ℕ) :
    v.adicValuation (c • v.uniformizer ^ (-(n + 1 : ℤ))) =
      WithZero.exp (n + 1 : ℤ) := by
  rw [Algebra.smul_def, Valuation.map_mul,
    v.adicValuation_eq_exp_neg_ord (by simpa using hc : algebraMap K F c ≠ 0),
    v.ord_eq_zero_of_isAlgebraic (isAlgebraic_algebraMap c), neg_zero,
    WithZero.exp_zero, one_mul,
    v.adicValuation_eq_exp_neg_ord (zpow_ne_zero _ v.uniformizer_ne_zero),
    v.ord_zpow, v.ord_uniformizer, mul_one, neg_neg]

theorem poleClass_linearIndependent : LinearIndependent K v.poleClass := by
  classical
  rw [linearIndependent_iff']
  intro s a hsum i hi
  by_contra hai
  let t := s.filter fun j => a j ≠ 0
  have ht : t.Nonempty := ⟨i, Finset.mem_filter.mpr ⟨hi, hai⟩⟩
  let j := t.max' ht
  have hj : j ∈ t := Finset.max'_mem t ht
  have haj : a j ≠ 0 := (Finset.mem_filter.mp hj).2
  have hval : v.adicValuation (∑ k ∈ t, a k • v.uniformizer ^ (-(k + 1 : ℤ))) =
      WithZero.exp (j + 1 : ℤ) := by
    rw [v.adicValuation.map_sum_eq_of_lt hj]
    · exact v.valuation_smul_uniformizer_neg_pow haj j
    · intro k hk
      have hkt := (Finset.mem_sdiff.mp hk).1
      have hkj : k ≠ j := by simpa using (Finset.mem_sdiff.mp hk).2
      have hklt : k < j := lt_of_le_of_ne (Finset.le_max' t k hkt) hkj
      rw [v.valuation_smul_uniformizer_neg_pow (Finset.mem_filter.mp hkt).2,
        v.valuation_smul_uniformizer_neg_pow haj]
      exact WithZero.exp_lt_exp.mpr (by omega)
  have hs : (∑ k ∈ t, a k • v.uniformizer ^ (-(k + 1 : ℤ))) =
      ∑ k ∈ s, a k • v.uniformizer ^ (-(k + 1 : ℤ)) := by
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro k hk hkt
    have hk0 : a k = 0 := by simpa [t, hk] using hkt
    simp only [hk0, zero_smul]
  have hmem : (∑ k ∈ t, a k • v.uniformizer ^ (-(k + 1 : ℤ))) ∈
      v.integralFunctions := by
    rw [hs, ← Submodule.Quotient.mk_eq_zero]
    change v.integralFunctions.mkQ (∑ k ∈ s, a k • v.uniformizer ^ (-(k + 1 : ℤ))) = 0
    simpa only [map_sum, map_smul, Submodule.mkQ_apply, poleClass] using hsum
  have hle := v.adicValuation_le_one_of_mem hmem
  rw [hval] at hle
  have hgt : (1 : WithZero (Multiplicative ℤ)) < WithZero.exp (j + 1 : ℤ) := by
    rw [← WithZero.exp_zero]
    exact WithZero.exp_lt_exp.mpr (by omega)
  exact (not_lt_of_ge hle) hgt

end
end Dubon2026.SourceCurve.Place
