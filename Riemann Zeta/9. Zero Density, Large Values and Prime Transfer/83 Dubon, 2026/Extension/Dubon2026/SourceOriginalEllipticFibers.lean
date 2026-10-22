import Dubon2026.SourceOriginalEllipticCoordinate
import Dubon2026.SourceOriginalAnalyticRamification
import Mathlib.Analysis.Normed.Ring.Finite
import Mathlib.RingTheory.RootsOfUnity.Complex

/-! DUB-17/18 -> original torsion cardinality -> elliptic charts.
The existing exact ramification formula makes the squared inverse
denominator character run through all ramification roots of unity.
The explicit centered coordinate then identifies each power fiber by
an actual Gamma0 stabilizer element. Its original-place invariance gives
equality of the literal places, discharging the fiber-invariance premise
of analytic power descent.
-/
namespace Dubon2026.SourceFunctionField.EllipticCoordinate
noncomputable section
open UpperHalfPlane
open scoped MatrixGroups ComplexConjugate SubgroupStabilizer

theorem multiplier_eq_inv_square (Γ : Subgroup SL(2, ℤ)) (τ : ℍ)
    (γ : MulAction.stabilizer Γ τ) :
    conj (SubgroupStabilizer.chi Γ τ γ) / SubgroupStabilizer.chi Γ τ γ =
      (SubgroupStabilizer.chi Γ τ γ ^ 2)⁻¹ := by
  have hn := ((SubgroupStabilizer.chi Γ τ).isOfFinOrder (isOfFinOrder_of_finite γ)).norm_eq_one
  rw [← Complex.inv_eq_conj hn, div_eq_mul_inv, ← pow_two, ← inv_pow]

theorem exists_stabilizer_multiplier (N : ℕ) [NeZero N] (τ : ℍ) (ζ : ℂ)
    (hζ : ζ ^ originalAnalyticRamification N τ = 1) :
    ∃ γ : MulAction.stabilizer (CongruenceSubgroup.Gamma0 N) τ,
      conj (SubgroupStabilizer.chi (CongruenceSubgroup.Gamma0 N) τ γ) /
        SubgroupStabilizer.chi (CongruenceSubgroup.Gamma0 N) τ γ = ζ := by
  let Γ := CongruenceSubgroup.Gamma0 N
  let e := originalAnalyticRamification N τ
  letI : NeZero e := ⟨(originalAnalyticRamification_pos N τ).ne'⟩
  letI := SubgroupStabilizer.isCyclic_stabilizer Γ τ
  obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := MulAction.stabilizer Γ τ)
  have hp : IsPrimitiveRoot (SubgroupStabilizer.chi Γ τ g) (2 * e) := by
    apply IsPrimitiveRoot.iff_orderOf.mpr
    rw [orderOf_injective _ (SubgroupStabilizer.chi_injective Γ τ), hg]
    exact (original_two_mul_ramification_eq_stabilizer_card N τ).symm
  have hp2 : IsPrimitiveRoot ((SubgroupStabilizer.chi Γ τ g ^ 2)⁻¹) e :=
    (hp.pow (mul_pos (by norm_num) (originalAnalyticRamification_pos N τ)) rfl).inv
  obtain ⟨i, _, hi⟩ := hp2.eq_pow_of_pow_eq_one hζ
  refine ⟨g ^ i, ?_⟩
  rw [multiplier_eq_inv_square, map_pow, ← hi, inv_pow, ← pow_mul, ← pow_mul, Nat.mul_comm i 2]

theorem place_eq_of_coord_power_eq (N : ℕ) [NeZero N] (τ z w : ℍ)
    (h : coord τ z ^ originalAnalyticRamification N τ =
      coord τ w ^ originalAnalyticRamification N τ) :
    originalAnalyticPlace N z = originalAnalyticPlace N w := by
  let e := originalAnalyticRamification N τ
  have he : e ≠ 0 := (originalAnalyticRamification_pos N τ).ne'
  by_cases hz : coord τ z = 0
  · have hw : coord τ w = 0 := by
      apply (pow_eq_zero_iff he).mp
      rw [← h, hz, zero_pow he]
    have hzw : z = w := by
      apply UpperHalfPlane.ext
      rw [← param_coord τ z, ← param_coord τ w, hz, hw]
    rw [hzw]
  · have hζ : (coord τ w / coord τ z) ^ e = 1 := by
      rw [div_pow, ← h, div_self (pow_ne_zero _ hz)]
    obtain ⟨γ, hγ⟩ := exists_stabilizer_multiplier N τ (coord τ w / coord τ z) hζ
    have hc : coord τ ((((γ : CongruenceSubgroup.Gamma0 N) : SL(2, ℤ)) • z : ℍ) : ℂ) =
        coord τ w := by
      rw [coord_smul τ _ γ.2]
      change (conj (SubgroupStabilizer.chi (CongruenceSubgroup.Gamma0 N) τ γ) /
        SubgroupStabilizer.chi (CongruenceSubgroup.Gamma0 N) τ γ) * coord τ z = _
      rw [hγ, div_mul_cancel₀ _ hz]
    have hzw : (((γ : CongruenceSubgroup.Gamma0 N) : SL(2, ℤ)) • z : ℍ) = w := by
      apply UpperHalfPlane.ext
      rw [← param_coord τ ((((γ : CongruenceSubgroup.Gamma0 N) : SL(2, ℤ)) • z : ℍ)),
        ← param_coord τ w, hc]
    rw [← hzw, originalAnalyticPlace_smul]

end
end Dubon2026.SourceFunctionField.EllipticCoordinate
