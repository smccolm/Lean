import Dubon2026.SourceCurveCoordinateSupport
import Dubon2026.SourceCurveRiemannRochSpace

/-! DUB-17/18 -> modular good reduction -> lifting the integral j chart.
An integral function is regular wherever the coordinate is regular, by
the existing integral-closure membership lemma. Its finitely many remaining
pole orders are bounded by a multiple of the coordinate pole divisor.
This is the input needed by the proved large-pole-space lifting theorem. -/
namespace Dubon2026.SourceCurve
noncomputable section
variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem Place.mem_of_integral_adjoin (v : Place K F) {x f : F}
    (hx : x ∈ v.toValuationSubring) (hf : IsIntegral (Algebra.adjoin K {x}) f) :
    f ∈ v.toValuationSubring := by
  let V : Subalgebra K F :=
    { v.toValuationSubring.toSubring with algebraMap_mem' := v.algebraMap_mem' }
  have hle : Algebra.adjoin K {x} ≤ V :=
    Algebra.adjoin_le (Set.singleton_subset_iff.mpr hx)
  exact integralClosure_mem_of_base_mem v (fun a => hle a.property) ⟨f, hf⟩

theorem exists_pole_bound_of_integral_adjoin (x f : F)
    (hf : IsIntegral (Algebra.adjoin K {x}) f)
    (D : Divisor K F) (hD : ∀ v, D v = max 0 (-v.ord x)) :
    ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m → f ∈ LSpace (m • D) := by
  classical
  let m₀ := D.support.sup fun v => (-v.ord f).toNat
  refine ⟨m₀, fun m hm => mem_lSpace_iff_ord.mpr (Or.inr fun v => ?_)⟩
  have hmul : (m • D) v = (m : ℤ) * D v := by simp
  rw [hmul]
  by_cases hx : 0 ≤ v.ord x
  · have hv := v.ord_nonneg_of_mem (v.mem_of_integral_adjoin (v.mem_of_ord_nonneg hx) hf)
    simpa only [hD, max_eq_left (neg_nonpos.mpr hx), mul_zero, neg_zero] using hv
  · have hneg : v.ord x < 0 := lt_of_not_ge hx
    have hDv : D v = -v.ord x := by rw [hD, max_eq_right (by omega)]
    have hsupp : v ∈ D.support := by rw [Finsupp.mem_support_iff, hDv]; omega
    have hsup : (-v.ord f).toNat ≤ m₀ :=
      Finset.le_sup (f := fun v => (-v.ord f).toNat) hsupp
    have hbound : -v.ord f ≤ (m : ℤ) := by
      have hnat := Int.self_le_toNat (-v.ord f)
      omega
    have hone : (1 : ℤ) ≤ D v := by rw [hDv]; omega
    have hproduct := mul_le_mul_of_nonneg_left hone (Int.natCast_nonneg m)
    linarith

theorem mul_pow_mem_pole_space_of_inverse_bound (x : F) (hx : x ≠ 0)
    (D Dinv : Divisor K F) (hD : ∀ v, D v = max 0 (-v.ord x))
    (hDinv : ∀ v, Dinv v = max 0 (v.ord x)) (m : ℕ)
    {f : F} (hf : f ∈ LSpace (m • Dinv)) : f * x ^ m ∈ LSpace (m • D) := by
  rcases mem_lSpace_iff_ord.mp hf with rfl | hf
  · rw [zero_mul]
    exact zero_mem _
  rcases eq_or_ne f 0 with rfl | hf0
  · rw [zero_mul]
    exact zero_mem _
  apply mem_lSpace_iff_ord.mpr
  right
  intro v
  have hv := hf v
  simp only [Finsupp.smul_apply, nsmul_eq_mul, hDinv] at hv
  rw [v.ord_mul hf0 (pow_ne_zero m hx), ← zpow_natCast, v.ord_zpow]
  simp only [Finsupp.smul_apply, nsmul_eq_mul, hD]
  by_cases ho : 0 ≤ v.ord x
  · rw [max_eq_right ho] at hv
    rw [max_eq_left (neg_nonpos.mpr ho)]
    linarith
  · rw [max_eq_left (le_of_not_ge ho)] at hv
    rw [max_eq_right (by omega)]
    linarith

end
end Dubon2026.SourceCurve
