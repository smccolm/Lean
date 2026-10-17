import Dubon2026.RationalPrimeCyclotomicResidualReduction

/-! # The character identity required by two-primary quotient reciprocity

Use the pinned primitive-root action and residue APIs to translate the
proved inverse-quotient action into the exact conductor-unit cancellation.
This is the remaining character step between cyclic-subfield reciprocity
and DUB-17's real/away-prime product comparison.
-/
namespace Dubon2026
noncomputable section

/-- An inverse-quotient root action cancels the forward residue quotient. -/
theorem primitiveRoot_autToPow_mul_quotient_eq_one
    (K F : Type*) [Field K] [Field F] [Algebra K F]
    (m : ℕ) [NeZero m] {ζ : F} (hζ : IsPrimitiveRoot ζ m)
    (σ : Gal(F/K)) (a b d : ℕ)
    (ha : a.Coprime m) (hb : b.Coprime m) (hd : d.Coprime m)
    (hab : a * b ≡ 1 [MOD m]) (hσ : σ ζ = ζ ^ (b * d)) :
    hζ.autToPow K σ *
      (ZMod.unitOfCoprime a ha * (ZMod.unitOfCoprime d hd)⁻¹) = 1 := by
  have hmod : (hζ.autToPow K σ : ZMod m).val ≡ b * d [MOD m] := by
    have h := (hζ.isOfFinOrder (NeZero.ne m)).pow_eq_pow_iff_modEq.mp
      ((hζ.autToPow_spec K σ).trans hσ)
    simpa only [hζ.eq_orderOf] using h
  have hchar : hζ.autToPow K σ = ZMod.unitOfCoprime b hb * ZMod.unitOfCoprime d hd := by
    apply Units.ext
    change (hζ.autToPow K σ : ZMod m) = (b : ZMod m) * d
    rw [← Nat.cast_mul, ← ZMod.natCast_zmod_val (hζ.autToPow K σ : ZMod m)]
    exact (ZMod.natCast_eq_natCast_iff _ _ m).2 hmod
  have hinv : ZMod.unitOfCoprime b hb * ZMod.unitOfCoprime a ha = 1 := by
    apply Units.ext
    change (b : ZMod m) * a = 1
    rw [← Nat.cast_mul, ← Nat.cast_one]
    exact (ZMod.natCast_eq_natCast_iff _ _ m).2 (by simpa only [Nat.mul_comm] using hab)
  rw [hchar]
  calc
    (ZMod.unitOfCoprime b hb * ZMod.unitOfCoprime d hd) *
        (ZMod.unitOfCoprime a ha * (ZMod.unitOfCoprime d hd)⁻¹) =
      (ZMod.unitOfCoprime b hb * ZMod.unitOfCoprime a ha) *
        (ZMod.unitOfCoprime d hd * (ZMod.unitOfCoprime d hd)⁻¹) := by ac_rfl
    _ = 1 := by rw [hinv, mul_inv_cancel, mul_one]

end
end Dubon2026
