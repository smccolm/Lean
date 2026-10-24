import Dubon2026.SourceRatFuncGaloisCoordinate
import Dubon2026.SourceCurveLocalDifferentials
import Mathlib.AlgebraicGeometry.EllipticCurve.ModelsWithJ
import Mathlib.AlgebraicGeometry.EllipticCurve.VariableChange
import Mathlib.Tactic

/-! The literal ofJ(X) discriminant forces a divisibility relation on
the actual normalized place orders whenever the source good model exists.
This is the ramification lower bound needed to identify the inertia image
for the DUB-17/18 exceptional fibers. Native model discriminant formulas
and the existing normalized-order arithmetic suffice.
Source: anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2,
S_ModularCurve_exists_equivariant_torsion_reduction_ofJ, h12 argument. -/
namespace Dubon2026.SourceEllipticReduction
open WeierstrassCurve SourceCurve
noncomputable section
variable {K M : Type*} [Field K] [Field M]
variable [Algebra (RatFunc K) M] [Algebra K M] [IsScalarTower K (RatFunc K) M]
variable [DecidableEq (RatFunc K)]

omit [Algebra K M] [IsScalarTower K (RatFunc K) M] in
theorem ofJ_X_baseChange_discriminant :
    ((ofJ (RatFunc.X : RatFunc K)).baseChange M).Δ =
      (algebraMap (RatFunc K) M RatFunc.X) ^ 2 *
        (algebraMap (RatFunc K) M RatFunc.X - 1728) ^ 9 := by
  have h1728 : (RatFunc.X : RatFunc K) ≠ 1728 := by
    intro h
    apply RatFunc.transcendental_X (K := K)
    rw [h]
    simpa only [map_ofNat] using isAlgebraic_algebraMap (R := K) (A := RatFunc K) (1728 : K)
  rw [ofJ_ne_0_ne_1728 _ RatFunc.X_ne_zero h1728, WeierstrassCurve.baseChange,
    map_Δ, ofJNe0Or1728_Δ, map_mul, map_pow, map_pow, map_sub, map_ofNat]

theorem ofJ_good_model_order_divisibility
    (v : Place K M) (W : WeierstrassCurve v.toValuationSubring) (κ : VariableChange M)
    (hκ : κ • (ofJ (RatFunc.X : RatFunc K)).baseChange M =
      W.map v.toValuationSubring.subtype) (hW : IsUnit W.Δ) :
    (12 : ℤ) ∣ 2 * v.ord (algebraMap (RatFunc K) M RatFunc.X) +
      9 * v.ord (algebraMap (RatFunc K) M RatFunc.X - 1728) := by
  let t := algebraMap (RatFunc K) M RatFunc.X
  have ht : Transcendental K t := SourceCurve.rationalCoordinate_transcendental K (M := M)
  have ht0 : t ≠ 0 := by
    intro h
    exact ht (h ▸ isAlgebraic_zero)
  have ht1728 : t - 1728 ≠ 0 := by
    intro h
    apply ht
    rw [sub_eq_zero.mp h]
    simpa only [map_ofNat] using isAlgebraic_algebraMap (R := K) (A := M) (1728 : K)
  have hd := congrArg WeierstrassCurve.Δ hκ
  rw [variableChange_Δ, map_Δ, ofJ_X_baseChange_discriminant] at hd
  have ho := congrArg v.ord hd
  have hunit : v.ord (v.toValuationSubring.subtype W.Δ) = 0 := by
    obtain ⟨u, hu⟩ := hW
    rw [← hu]
    exact v.ord_coe_unit u
  rw [v.ord_mul (pow_ne_zero _ (κ.u⁻¹).ne_zero)
      (mul_ne_zero (pow_ne_zero _ ht0) (pow_ne_zero _ ht1728)),
    v.ord_mul (pow_ne_zero _ ht0) (pow_ne_zero _ ht1728)] at ho
  simp only [← zpow_natCast, Place.ord_zpow, Units.val_inv_eq_inv_val, Place.ord_inv] at ho
  rw [hunit] at ho
  refine ⟨v.ord (κ.u : M), ?_⟩
  push_cast at ho
  linarith

end
end Dubon2026.SourceEllipticReduction
