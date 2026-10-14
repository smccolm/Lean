import Dubon2026.LocalFieldFrobeniusUnitRoots
import Dubon2026.LocalFieldRootIntegerUnit

/-! # Original unramified Frobenius on actual field roots of unity

The integer unit is constructed from the original field root, using the
proved original order-kernel theorem. Prime-to-residue root detection
then gives the actual field Frobenius formula needed by DUB-17's unramified
cyclotomic local terms. No integer representative is assumed.
-/
namespace Dubon2026
noncomputable section
open scoped ValuativeRel

variable (K L : Type) [Field K] [Field L] [Algebra K L] [IsGalois K L]
  [ValuativeRel K] [ValuativeRel L] [TopologicalSpace K] [TopologicalSpace L]
  [IsNonarchimedeanLocalField K] [IsNonarchimedeanLocalField L]
  [(ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation L)]
  [Algebra.FormallyUnramified 𝒪[K] 𝒪[L]]

/-- Original arithmetic Frobenius acts by the residue-cardinality power on every original field root of prime-to-residue order. -/
theorem localFieldArithmeticFrobenius_field_root {n : ℕ}
    (hn : (n : 𝓀[L]) ≠ 0) (ζ : L) (hζ : ζ ^ n = 1) :
    localFieldArithmeticFrobenius K L ζ = ζ ^ Nat.card 𝓀[K] := by
  haveI : NeZero n := ⟨by intro h; exact hn (by rw [h, Nat.cast_zero])⟩
  obtain ⟨u, hu, he⟩ := localFieldRoot_exists_integer_unit L ζ hζ
  have hf := localFieldArithmeticFrobenius_unit_root K L hn u hu
  rwa [he] at hf

end
end Dubon2026
