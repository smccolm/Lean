import Dubon2026.SourceOriginalTateWeilArithmetic
import Mathlib.NumberTheory.Cyclotomic.CyclotomicCharacter
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed

/-! DUB-17/18 -> Frobenius determinant -> cyclotomic pairing multiplier.
Reuse Mathlib's actual p-adic cyclotomic character and the native Tate scalar
coordinates. No choice of a primitive-root sequence or target basis is needed
to identify the arithmetic action as cyclotomic scalar multiplication. -/
namespace Dubon2026.SourceFunctionField
noncomputable section
local notation "Qbar" => AlgebraicClosure ℚ
variable (p : ℕ) [Fact p.Prime]

omit [Fact p.Prime] in
theorem originalTateRoots_coordinate_pow (x : TateModule p (Additive Qbarˣ)) (k : ℕ) :
    (((x : ℕ → Additive Qbarˣ) k).toMul : Qbar) ^ (p ^ k) = 1 := by
  have h := congrArg (fun a : Additive Qbarˣ => (a.toMul : Qbar)) (TateModule.torsion x k)
  simpa only [toMul_zsmul, zpow_natCast, Units.val_pow_eq_pow_val, toMul_zero, Units.val_one] using h

theorem originalTateRootsGalois_eq_cyclotomic_smul (σ : Qbar ≃ₐ[ℚ] Qbar)
    (x : TateModule p (Additive Qbarˣ)) :
    originalTateRootsGalois p σ x =
      (cyclotomicCharacter Qbar p σ.toRingEquiv : ℤ_[p]) • x := by
  apply Subtype.ext
  funext k
  rw [originalTateRootsGalois, TateModule.coe_tateMap_apply, TateModule.smul_apply]
  apply Additive.toMul.injective
  apply Units.ext
  simp only [toMul_zsmul, zpow_natCast, Units.val_pow_eq_pow_val]
  change σ (((x : ℕ → Additive Qbarˣ) k).toMul : Qbar) = _
  have h := cyclotomicCharacter.spec p σ.toRingEquiv _ (originalTateRoots_coordinate_pow p x k)
  rw [TateModule.toZModPow_eq_appr, ZMod.val_natCast,
    Nat.mod_eq_of_lt (PadicInt.appr_lt _ k)] at h
  exact h

theorem originalTateWeilPairing_cyclotomic (N : ℕ) [NeZero N]
    (σ : Qbar ≃ₐ[ℚ] Qbar) (x y : TateModule p (originalJZero N)) :
    originalTateWeilPairing N p (originalTateGaloisRep N p σ x)
      (originalTateGaloisRep N p σ y) =
      (cyclotomicCharacter Qbar p σ.toRingEquiv : ℤ_[p]) • originalTateWeilPairing N p x y := by
  rw [originalTateWeilPairing_galois, originalTateRootsGalois_eq_cyclotomic_smul]

end
end Dubon2026.SourceFunctionField
