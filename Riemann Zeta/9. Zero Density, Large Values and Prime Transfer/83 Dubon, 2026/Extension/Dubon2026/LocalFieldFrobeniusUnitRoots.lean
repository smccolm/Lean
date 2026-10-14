import Dubon2026.PrimeToResidueRootUniqueness
import Dubon2026.LocalFieldArithmeticFrobenius

/-! # Original arithmetic Frobenius acts by residue cardinality on tame roots

The existing unit-exponent root detection lifts the already proved original residue Frobenius
formula to the actual integer units and their actual field values. These
are the unramified local cyclotomic terms required for DUB-17's principal
product and arithmetic invariant sum-zero.
-/
namespace Dubon2026
noncomputable section
open scoped ValuativeRel

variable (K L : Type) [Field K] [Field L] [Algebra K L] [IsGalois K L]
  [ValuativeRel K] [ValuativeRel L] [TopologicalSpace K] [TopologicalSpace L]
  [IsNonarchimedeanLocalField K] [IsNonarchimedeanLocalField L]
  [(ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation L)]
  [Algebra.FormallyUnramified 𝒪[K] 𝒪[L]]

/-- The original arithmetic Frobenius acts on an actual prime-to-residue integer unit root by the residue-cardinality power. -/
theorem localFieldArithmeticFrobenius_integer_unit_root {n : ℕ}
    (hn : (n : 𝓀[L]) ≠ 0) (u : 𝒪[L]ˣ) (hu : u ^ n = 1) :
    localFieldIntegerGaloisEquiv K L (localFieldArithmeticFrobenius K L) (u : 𝒪[L]) =
      (u : 𝒪[L]) ^ Nat.card 𝓀[K] := by
  let f := (localFieldIntegerGaloisEquiv K L
    (localFieldArithmeticFrobenius K L)).toAlgHom.toMonoidHom
  have hx : (Units.map f u) ^ n = 1 := by rw [← map_pow, hu, map_one]
  have hy : (u ^ Nat.card 𝓀[K]) ^ n = 1 := by rw [pow_right_comm, hu, one_pow]
  have hr : IsLocalRing.residue 𝒪[L] (Units.map f u : 𝒪[L]) =
      IsLocalRing.residue 𝒪[L] ((u ^ Nat.card 𝓀[K] : 𝒪[L]ˣ) : 𝒪[L]) := by
    change IsLocalRing.residue 𝒪[L]
      (localFieldIntegerGaloisEquiv K L (localFieldArithmeticFrobenius K L) (u : 𝒪[L])) =
        IsLocalRing.residue 𝒪[L] ((u : 𝒪[L]) ^ Nat.card 𝓀[K])
    rw [map_pow]
    exact localFieldArithmeticFrobenius_residue K L u
  exact congrArg (fun v : 𝒪[L]ˣ => (v : 𝒪[L]))
    (primeToResidue_unit_roots_eq hn (Units.map f u) (u ^ Nat.card 𝓀[K]) hx hy hr)

/-- The same original Frobenius formula holds on the literal field value of the original integer unit root. -/
theorem localFieldArithmeticFrobenius_unit_root {n : ℕ}
    (hn : (n : 𝓀[L]) ≠ 0) (u : 𝒪[L]ˣ) (hu : u ^ n = 1) :
    localFieldArithmeticFrobenius K L (algebraMap 𝒪[L] L (u : 𝒪[L])) =
      algebraMap 𝒪[L] L (u : 𝒪[L]) ^ Nat.card 𝓀[K] := by
  have h := congrArg (algebraMap 𝒪[L] L)
    (localFieldArithmeticFrobenius_integer_unit_root K L hn u hu)
  rwa [localFieldIntegerGaloisEquiv_apply, map_pow] at h

end
end Dubon2026
