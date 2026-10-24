import Dubon2026.SourceEllipticOfJDiscriminantOrder

/-! The existing actual good-model discriminant relation becomes
12 dividing ord(j) in characteristic three. This supplies the inertia
order lower bound for the DUB-17/18 wild exceptional-fiber census. -/
namespace Dubon2026.SourceEllipticReduction
open WeierstrassCurve SourceCurve
noncomputable section
variable {K M : Type*} [Field K] [Field M] [CharP K 3]
variable [Algebra (RatFunc K) M] [Algebra K M] [IsScalarTower K (RatFunc K) M]
variable [DecidableEq (RatFunc K)]

theorem ofJ_good_model_order_divisibility_of_char_three
    (v : Place K M) (W : WeierstrassCurve v.toValuationSubring) (κ : VariableChange M)
    (hκ : κ • (ofJ (RatFunc.X : RatFunc K)).baseChange M =
      W.map v.toValuationSubring.subtype) (hW : IsUnit W.Δ) :
    (12 : ℤ) ∣ v.ord (algebraMap (RatFunc K) M RatFunc.X) := by
  have h1728K : (1728 : K) = 0 := by
    have h3 : (3 : K) = 0 := CharP.cast_eq_zero K 3
    linear_combination 576 * h3
  have h1728 : (1728 : M) = 0 := by
    simpa only [map_ofNat, map_zero] using congrArg (algebraMap K M) h1728K
  have hd := ofJ_good_model_order_divisibility v W κ hκ hW
  rw [h1728, sub_zero] at hd
  omega

end
end Dubon2026.SourceEllipticReduction
