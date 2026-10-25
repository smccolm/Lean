import Dubon2026.SourceEllipticCharTwoOfJFamily
import Dubon2026.SourceEllipticCharTwoEighthPower
import Dubon2026.SourceCurvePlaceCenters

/-! DUB-17/18 -> characteristic-two weighted census -> full inertia image.
The actual good-model discriminant gives divisibility by twelve. The
actual three-torsion count and eighth-power factorization give divisibility
by eight at the exceptional fiber. Their combination forces inertia order
at least twenty-four, to be matched with the proved stabilizer cardinality. -/
namespace Dubon2026.SourceEllipticReduction
open WeierstrassCurve WeierstrassCurve.Affine SourceCurve SourceEllipticCharTwo
noncomputable section
variable {K M : Type*} [Field K] [Field M] [CharP K 2]
variable [Algebra (RatFunc K) M] [Algebra K M] [IsScalarTower K (RatFunc K) M]
variable [DecidableEq (RatFunc K)]

theorem ofJ_good_model_order_divisibility_of_char_two
    (v : Place K M) (W : WeierstrassCurve v.toValuationSubring) (κ : VariableChange M)
    (hκ : κ • (ofJ (RatFunc.X : RatFunc K)).baseChange M =
      W.map v.toValuationSubring.subtype) (hW : IsUnit W.Δ) :
    (12 : ℤ) ∣ v.ord (algebraMap (RatFunc K) M RatFunc.X) := by
  have h1728K : (1728 : K) = 0 := by
    have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
    linear_combination 864 * h2
  have h1728 : (1728 : M) = 0 := by
    simpa only [map_ofNat, map_zero] using congrArg (algebraMap K M) h1728K
  have hd := ofJ_good_model_order_divisibility v W κ hκ hW
  rw [h1728, sub_zero] at hd
  omega

theorem ofJ_order_eight_dvd_of_full_three_torsion
    [DecidableEq M] (v : Place K M) (hv : 0 < v.ord (algebraMap (RatFunc K) M RatFunc.X))
    (hcard : Nat.card {P : ((ofJ (RatFunc.X : RatFunc K)).baseChange M).toAffine.Point //
      (3 : ℕ) • P = 0} = 9) :
    (8 : ℤ) ∣ v.ord (algebraMap (RatFunc K) M RatFunc.X) := by
  classical
  letI : CharP M 2 := charP_of_injective_ringHom (algebraMap K M).injective 2
  let t := algebraMap (RatFunc K) M RatFunc.X
  have ht0 : t ≠ 0 := by
    simpa only [map_zero] using (algebraMap (RatFunc K) M).injective.ne RatFunc.X_ne_zero
  have ht : t ∈ v.toValuationSubring := v.mem_iff_ord_nonneg.mpr hv.le
  have htu : ¬ IsUnit (⟨t, ht⟩ : v.toValuationSubring) :=
    (IsLocalRing.mem_maximalIdeal _).mp ((v.mem_maximalIdeal_iff_ord_pos ht0 ht).mpr hv)
  rw [ofJ_X_baseChange_of_char_two] at hcard
  let C : WeierstrassCurve M := ⟨t, 0, 0, 0, t ^ 5⟩
  haveI : Finite {P : C.toAffine.Point // (3 : ℕ) • P = 0} :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  have h9 : 1 < Nat.card {P : C.toAffine.Point // (3 : ℕ) • P = 0} := by
    rw [hcard]; norm_num
  haveI := Finite.one_lt_card_iff_nontrivial.mp h9
  obtain ⟨⟨P, hP⟩, hne⟩ := exists_ne
    (⟨0, by rw [smul_zero]⟩ : {P : C.toAffine.Point // (3 : ℕ) • P = 0})
  have hPne : P ≠ 0 := fun h => hne (Subtype.ext h)
  rcases P with _ | ⟨x, y, hxy⟩
  · exact False.elim (hPne rfl)
  obtain ⟨μ, u, hu, htμ⟩ := exists_unit_mul_eighth_power v.toValuationSubring ht htu hxy hP
  have hu0 : (u : M) ≠ 0 := fun h => hu.ne_zero (Subtype.ext h)
  have hμ0 : μ ≠ 0 := by
    intro h
    apply ht0
    rw [htμ, h, zero_pow (by decide), mul_zero]
  have huord : v.ord (u : M) = 0 := by
    obtain ⟨a, ha⟩ := hu
    rw [← ha]
    exact v.ord_coe_unit a
  refine ⟨v.ord μ, ?_⟩
  change v.ord t = 8 * v.ord μ
  rw [htμ, v.ord_mul hu0 (pow_ne_zero _ hμ0), huord, zero_add,
    ← zpow_natCast, Place.ord_zpow]
  push_cast
  ring

end
end Dubon2026.SourceEllipticReduction
