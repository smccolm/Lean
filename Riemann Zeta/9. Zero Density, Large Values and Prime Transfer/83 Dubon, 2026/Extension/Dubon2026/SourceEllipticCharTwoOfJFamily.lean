import Dubon2026.SourceEllipticOfJDiscriminantOrder

/-! DUB-17/18 -> characteristic-two weighted census -> full inertia image.
Identify the actual generic ofJ curve with the literal characteristic-two
family used by the eighth-power factorization. -/
namespace Dubon2026.SourceEllipticCharTwo
open WeierstrassCurve
noncomputable section

theorem ofJ_X_baseChange_of_char_two
    {K M : Type*} [Field K] [Field M] [CharP K 2]
    [Algebra (RatFunc K) M] [Algebra K M] [IsScalarTower K (RatFunc K) M]
    [DecidableEq (RatFunc K)] :
    (ofJ (RatFunc.X : RatFunc K)).baseChange M =
      (⟨algebraMap (RatFunc K) M RatFunc.X, 0, 0, 0,
        (algebraMap (RatFunc K) M RatFunc.X) ^ 5⟩ : WeierstrassCurve M) := by
  have h2K : (2 : K) = 0 := CharP.cast_eq_zero K 2
  have h2F : (2 : RatFunc K) = 0 := by
    simpa only [map_ofNat, map_zero] using congrArg (algebraMap K (RatFunc K)) h2K
  have h1728F : (1728 : RatFunc K) = 0 := by linear_combination 864 * h2F
  have h2M : (2 : M) = 0 := by
    simpa only [map_ofNat, map_zero] using congrArg (algebraMap K M) h2K
  have h1728M : (1728 : M) = 0 := by linear_combination 864 * h2M
  have h36M : (36 : M) = 0 := by linear_combination 18 * h2M
  have hX1728 : (RatFunc.X : RatFunc K) ≠ 1728 := by
    rw [h1728F]
    exact RatFunc.X_ne_zero
  rw [ofJ_ne_0_ne_1728 _ RatFunc.X_ne_zero hX1728, WeierstrassCurve.baseChange]
  ext <;> simp only [ofJNe0Or1728, WeierstrassCurve.map, map_zero, map_sub, map_mul,
    map_pow, map_neg, map_ofNat, h1728M, sub_zero, h36M, zero_mul, neg_zero]
  linear_combination -h2M * (algebraMap (RatFunc K) M RatFunc.X) ^ 5

end
end Dubon2026.SourceEllipticCharTwo
