import Dubon2026.SourceGammaOneExactRamification
import Dubon2026.SourceOriginalEllipticFibers

/-! DUB-17/18 -> actual Gamma1 global charts -> elliptic power-fiber descent.
The exact stabilizer formula makes the centered-coordinate multipliers run
through every ramification root of unity. Actual Gamma1 places are invariant
under the subgroup with central signs adjoined, so equal coordinate powers
give equal actual places at every nonzero level, including elliptic points. -/
namespace Dubon2026.SourceFunctionField.GammaOne
noncomputable section
open UpperHalfPlane CongruenceSubgroup EllipticCoordinate
open scoped MatrixGroups ComplexConjugate SubgroupStabilizer GammaOne

theorem exists_stabilizer_multiplier (N : ℕ) [NeZero N]
    (hT : ModularGroup.T ∈ Gamma1 N) (τ : ℍ) (ζ : ℂ)
    (hζ : ζ ^ analyticRamification hT τ = 1) :
    ∃ γ : MulAction.stabilizer (plusMinus (Gamma1 N)) τ,
      conj (SubgroupStabilizer.chi (plusMinus (Gamma1 N)) τ γ) /
        SubgroupStabilizer.chi (plusMinus (Gamma1 N)) τ γ = ζ := by
  let Γ := plusMinus (Gamma1 N)
  let e := analyticRamification hT τ
  letI : NeZero e := ⟨(analyticRamification_pos hT τ).ne'⟩
  letI := SubgroupStabilizer.isCyclic_stabilizer Γ τ
  obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := MulAction.stabilizer Γ τ)
  have hp : IsPrimitiveRoot (SubgroupStabilizer.chi Γ τ g) (2 * e) := by
    apply IsPrimitiveRoot.iff_orderOf.mpr
    rw [orderOf_injective _ (SubgroupStabilizer.chi_injective Γ τ), hg]
    exact (two_mul_ramification_eq_stabilizer_card N hT τ).symm
  have hp2 : IsPrimitiveRoot ((SubgroupStabilizer.chi Γ τ g ^ 2)⁻¹) e :=
    (hp.pow (mul_pos (by norm_num) (analyticRamification_pos hT τ)) rfl).inv
  obtain ⟨i, _, hi⟩ := hp2.eq_pow_of_pow_eq_one hζ
  refine ⟨g ^ i, ?_⟩
  rw [multiplier_eq_inv_square, map_pow, ← hi, inv_pow, ← pow_mul, ← pow_mul, Nat.mul_comm i 2]

theorem place_eq_of_coord_power_eq (N : ℕ) [NeZero N]
    (hT : ModularGroup.T ∈ Gamma1 N) (τ z w : ℍ)
    (h : coord τ z ^ analyticRamification hT τ = coord τ w ^ analyticRamification hT τ) :
    analyticPlace hT z = analyticPlace hT w := by
  let e := analyticRamification hT τ
  have he : e ≠ 0 := (analyticRamification_pos hT τ).ne'
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
    obtain ⟨γ, hγ⟩ := exists_stabilizer_multiplier N hT τ (coord τ w / coord τ z) hζ
    have hc : coord τ ((((γ : plusMinus (Gamma1 N)) : SL(2, ℤ)) • z : ℍ) : ℂ) =
        coord τ w := by
      rw [coord_smul τ _ γ.2]
      change (conj (SubgroupStabilizer.chi (plusMinus (Gamma1 N)) τ γ) /
        SubgroupStabilizer.chi (plusMinus (Gamma1 N)) τ γ) * coord τ z = _
      rw [hγ, div_mul_cancel₀ _ hz]
    have hzw : (((γ : plusMinus (Gamma1 N)) : SL(2, ℤ)) • z : ℍ) = w := by
      apply UpperHalfPlane.ext
      rw [← param_coord τ ((((γ : plusMinus (Gamma1 N)) : SL(2, ℤ)) • z : ℍ)),
        ← param_coord τ w, hc]
    rw [← hzw, analyticPlace_smul_plusMinus hT (γ : plusMinus (Gamma1 N)).2]

end
end Dubon2026.SourceFunctionField.GammaOne
