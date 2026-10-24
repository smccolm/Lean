import Dubon2026.SourceEllipticOfJDiscriminantOrder
import Dubon2026.SourceEllipticStabilizerBoundsFive
import Dubon2026.SourceCurveOrders

/-! Unequal-order addition removes the irrelevant factor of the ofJ(X)
discriminant at each exceptional value. Thus six divides the positive
order at zero and four divides the positive order at 1728. Together with
the proved stabilizer bounds this is precisely the lower-bound step of
the DUB-17/18 inertia-image argument. -/
namespace Dubon2026.SourceEllipticReduction
open WeierstrassCurve SourceCurve
noncomputable section
variable {K M : Type*} [Field K] [Field M]
variable [Algebra (RatFunc K) M] [Algebra K M] [IsScalarTower K (RatFunc K) M]
variable [DecidableEq (RatFunc K)]

omit [Algebra (RatFunc K) M] [IsScalarTower K (RatFunc K) M] [DecidableEq (RatFunc K)] in
theorem ord_sub_constant_eq_zero_of_pos (v : Place K M) {t : M}
    (ht : 0 < v.ord t) (a : K) (ha : a ≠ 0) :
    v.ord (t - algebraMap K M a) = 0 := by
  have ht0 : t ≠ 0 := by rintro rfl; simp at ht
  have ha0 : algebraMap K M (-a) ≠ 0 := by
    simpa only [map_zero] using (algebraMap K M).injective.ne (neg_ne_zero.mpr ha)
  have h := v.ord_add_eq_of_lt ha0 ht0 (by rw [v.ord_algebraMap]; exact ht)
  rw [v.ord_algebraMap, map_neg, add_comm, ← sub_eq_add_neg] at h
  exact h

theorem ofJ_exceptional_order_divisibility
    (p : ℕ) [CharP K p] (hp : 5 ≤ p)
    (v : Place K M) (W : WeierstrassCurve v.toValuationSubring) (κ : VariableChange M)
    (hκ : κ • (ofJ (RatFunc.X : RatFunc K)).baseChange M =
      W.map v.toValuationSubring.subtype) (hW : IsUnit W.Δ) :
    (0 < v.ord (algebraMap (RatFunc K) M RatFunc.X) →
      (6 : ℤ) ∣ v.ord (algebraMap (RatFunc K) M RatFunc.X)) ∧
    (0 < v.ord (algebraMap (RatFunc K) M RatFunc.X - 1728) →
      (4 : ℤ) ∣ v.ord (algebraMap (RatFunc K) M RatFunc.X - 1728)) := by
  obtain ⟨h2, h3⟩ := isUnit_two_three_of_five_le K K p hp
  have h1728 : (1728 : K) ≠ 0 := by
    rw [show (1728 : K) = 2 ^ 6 * 3 ^ 3 by norm_num]
    exact mul_ne_zero (pow_ne_zero _ h2.ne_zero) (pow_ne_zero _ h3.ne_zero)
  have hd := ofJ_good_model_order_divisibility v W κ hκ hW
  constructor
  · intro ht
    have hz := ord_sub_constant_eq_zero_of_pos v ht 1728 h1728
    rw [map_ofNat] at hz
    rw [hz, mul_zero, add_zero] at hd
    omega
  · intro ht
    have hz := ord_sub_constant_eq_zero_of_pos v ht (-1728) (neg_ne_zero.mpr h1728)
    rw [map_neg, map_ofNat, sub_neg_eq_add, sub_add_cancel] at hz
    rw [hz, mul_zero, zero_add] at hd
    omega

end
end Dubon2026.SourceEllipticReduction
