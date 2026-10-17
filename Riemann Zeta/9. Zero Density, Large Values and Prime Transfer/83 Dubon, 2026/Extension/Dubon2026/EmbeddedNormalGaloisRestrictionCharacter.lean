import Dubon2026.RationalCyclotomicPrincipalStageBridge

/-! # The power character under the same embedded normal restriction

The native compositum character proof uses only the actual embedding and
restriction commutation law. This form applies directly to the global
cyclotomic containing-field embedding needed in DUB-17's principal product.
-/
namespace Dubon2026
noncomputable section

/-- Restriction through an actual normal-field embedding preserves the
primitive-root power character, even when the fixed base changes. -/
theorem embeddedNormalGaloisRestriction_autToPow
    (R K F C : Type) [Field R] [Field K] [Field F] [Field C]
    [Algebra R K] [Algebra R F] [Algebra K C] [Algebra R C]
    [IsScalarTower R K C] [Normal R F]
    (j : F →ₐ[R] C) (m : ℕ) [NeZero m] {ζ : F} (hζ : IsPrimitiveRoot ζ m)
    (σ : Gal(C/K)) :
    hζ.autToPow R (embeddedNormalGaloisRestriction (F := K) j σ) =
      (hζ.map_of_injective j.injective).autToPow K σ := by
  let hμ : IsPrimitiveRoot (j ζ) m := hζ.map_of_injective j.injective
  apply Units.ext
  apply ZMod.val_injective m
  apply hμ.pow_inj (ZMod.val_lt _) (ZMod.val_lt _)
  calc
    (j ζ) ^ (hζ.autToPow R (embeddedNormalGaloisRestriction (F := K) j σ) : ZMod m).val =
        j (ζ ^ (hζ.autToPow R (embeddedNormalGaloisRestriction (F := K) j σ) : ZMod m).val) :=
      (map_pow j ζ _).symm
    _ = j (embeddedNormalGaloisRestriction (F := K) j σ ζ) := by rw [hζ.autToPow_spec R]
    _ = σ (j ζ) := embeddedNormalGaloisRestriction_commutes j σ ζ
    _ = (j ζ) ^ (hμ.autToPow K σ : ZMod m).val := (hμ.autToPow_spec K σ).symm

end
end Dubon2026
