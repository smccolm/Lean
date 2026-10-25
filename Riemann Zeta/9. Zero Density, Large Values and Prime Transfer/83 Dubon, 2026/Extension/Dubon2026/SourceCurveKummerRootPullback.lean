import Dubon2026.SourceCurveDivisorPullback
import Dubon2026.SourceCurvePicardPushforward

/-! DUB-17/18 -> finite Weil detection -> the moved Kummer-root divisor.
The actual power equation and normalized restriction orders identify the
root divisor with the existing ramification-weighted pullback. -/
namespace Dubon2026.SourceCurve
noncomputable section
variable {K F E : Type*} [Field K] [Field F] [Field E]
variable [Algebra K F] [Algebra K E] [Algebra F E] [IsScalarTower K F E]
variable [FiniteDimensional F E] [Algebra.IsSeparable F E]

theorem finitePullback_apply_zero_of_restrict (D : Divisor K F) (w : Place K E)
    (h : D (w.restrict F) = 0) : Divisor.finitePullback E D w = 0 := by
  rw [Divisor.finitePullback_apply, h, zero_mul]

omit [FiniteDimensional F E] in
theorem disjoint_geometricPushforward_of_avoiding (D : Divisor K F) (B : Divisor K E)
    (h : ∀ w ∈ B.support, D (w.restrict F) = 0) :
    ∀ v, D v = 0 ∨ Divisor.geometricPushforward F B v = 0 := by
  classical
  intro v
  by_cases hv : D v = 0
  · exact Or.inl hv
  right
  change (B.mapDomain (fun q : Place K E => q.restrict F)) v = 0
  apply Finsupp.mapDomain_of_not_mem_image_support
  rintro ⟨q, hq, heq⟩
  exact hv (heq ▸ h q hq)

theorem ord_eq_finitePullback_of_pow_eq (n : ℕ) [NeZero n] (D : Divisor K F)
    (f : F) (h : E) (hord : ∀ v, v.ord f = (n : ℤ) * D v)
    (hpow : h ^ n = algebraMap F E f) (w : Place K E) :
    w.ord h = Divisor.finitePullback E D w := by
  apply mul_left_cancel₀ (show (n : ℤ) ≠ 0 from Nat.cast_ne_zero.mpr (NeZero.ne n))
  calc
    (n : ℤ) * w.ord h = w.ord (h ^ n) := by rw [← zpow_natCast, w.ord_zpow]
    _ = w.ord (algebraMap F E f) := congrArg w.ord hpow
    _ = ((n : ℤ) * D (w.restrict F)) *
        w.ord (algebraMap F E (w.restrict F).uniformizer) := by
      rw [w.ord_algebraMap_restrict, hord]
    _ = (n : ℤ) * Divisor.finitePullback E D w := by
      rw [Divisor.finitePullback_apply, mul_assoc]

end
end Dubon2026.SourceCurve
