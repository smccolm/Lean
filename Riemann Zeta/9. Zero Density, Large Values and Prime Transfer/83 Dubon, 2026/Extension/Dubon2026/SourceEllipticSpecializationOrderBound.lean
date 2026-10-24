import Dubon2026.SourceEllipticOfJExceptionalOrders

/-! The literal good-model discriminant and the proved actual elliptic
stabilizer bounds give the exact order-versus-stabilizer dichotomy used
by the source inertia-image proof. No equality between decomposition
cardinality and normalized order is assumed or claimed here. -/
namespace Dubon2026.SourceEllipticReduction
open WeierstrassCurve SourceCurve
noncomputable section

theorem ofJ_specialization_stabilizer_order_bound
    {K M : Type*} [Field K] [Field M]
    [Algebra (RatFunc K) M] [Algebra K M] [IsScalarTower K (RatFunc K) M]
    [DecidableEq (RatFunc K)] (p : ℕ) [CharP K p] (hp : 5 ≤ p)
    (E₀ : WeierstrassCurve K) [E₀.IsElliptic]
    (v : Place K M) (W : WeierstrassCurve v.toValuationSubring) (κ : VariableChange M)
    (hκ : κ • (ofJ (RatFunc.X : RatFunc K)).baseChange M =
      W.map v.toValuationSubring.subtype) (hW : IsUnit W.Δ)
    (hv : 0 < v.ord (algebraMap (RatFunc K) M RatFunc.X - algebraMap K M E₀.j)) :
    Nat.card (MulAction.stabilizer (VariableChange K) E₀) ≤
        (v.ord (algebraMap (RatFunc K) M RatFunc.X - algebraMap K M E₀.j)).toNat ∨
      Nat.card (MulAction.stabilizer (VariableChange K) E₀) ≤ 2 := by
  obtain ⟨_, h6, h4, h2⟩ := SourceEllipticStabilizer.stabilizer_bounds_of_five_le K p hp E₀
  obtain ⟨hd6, hd4⟩ := ofJ_exceptional_order_divisibility p hp v W κ hκ hW
  by_cases hj0 : E₀.j = 0
  · left
    rw [hj0, map_zero, sub_zero] at hv ⊢
    apply (h6 hj0).trans
    have hle := Int.le_of_dvd hv (hd6 hv)
    omega
  · by_cases hj1728 : E₀.j = 1728
    · left
      rw [hj1728, map_ofNat] at hv ⊢
      apply (h4 hj1728).trans
      have hle := Int.le_of_dvd hv (hd4 hv)
      omega
    · exact Or.inr (h2 hj0 hj1728)

end
end Dubon2026.SourceEllipticReduction
