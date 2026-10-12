import Dubon2026.ContinuousKummerH1Map
import Dubon2026.ContinuousCohomologyCup
import Mathlib.Algebra.Module.ZMod

/-! # The original root/finite-character coefficient pairing

This is the literal exponent pairing used to compare the actual Kummer cup with
cyclic carry cocycles. It is a coefficient pairing, not an arithmetic duality assertion.
-/

namespace Dubon2026
noncomputable section

variable {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω]
  (n : ℕ) [NeZero n]

/-- The actual roots of unity form a module over the original residue ring,
because their original nth powers are one. -/
abbrev galoisRootZModModule :
    Module (ZMod n) (galoisRootOfUnityRepresentation (K := K) (Ω := Ω) n) :=
  AddCommGroup.zmodModule (fun x => by
    apply Rep.toAdditive.injective
    apply Subtype.ext
    change ((Additive.toMul (Rep.toAdditive x) : rootsOfUnity n Ω) : Ωˣ) ^ n = 1
    exact (Additive.toMul (Rep.toAdditive x) : rootsOfUnity n Ω).property)

attribute [local instance] galoisRootZModModule

/-- The coefficient pairing is literal exponentiation of the original root by
the original residue class, written additively in the original representation. -/
def galoisRootExponentPairing :
    galoisRootOfUnityRepresentation (K := K) (Ω := Ω) n →ₗ[ℤ]
      (Rep.of (1 : Representation ℤ Gal(Ω/K) (ZMod n))) →ₗ[ℤ]
        galoisRootOfUnityRepresentation (K := K) (Ω := Ω) n :=
  LinearMap.mk₂ ℤ (fun x t => t • x)
    (fun x y t => smul_add t x y)
    (fun r x t => smul_comm t r x)
    (fun x t u => add_smul t u x)
    (fun r x t => smul_assoc r t x)

/-- The coefficient pairing retains the actual root and canonical integer exponent. -/
theorem galoisRootExponentPairing_apply
    (x : galoisRootOfUnityRepresentation (K := K) (Ω := Ω) n) (t : ZMod n) :
    ((Additive.toMul (Rep.toAdditive (galoisRootExponentPairing n x t)) : rootsOfUnity n Ω) : Ωˣ) =
      ((Additive.toMul (Rep.toAdditive x) : rootsOfUnity n Ω) : Ωˣ) ^ t.val := by
  have ht : t • x = t.val • x := by
    conv_lhs => rw [← ZMod.natCast_zmod_val t]
    exact Nat.cast_smul_eq_nsmul (ZMod n) t.val x
  change ((Additive.toMul (Rep.toAdditive (t • x)) : rootsOfUnity n Ω) : Ωˣ) = _
  rw [ht]
  rfl

/-- The actual exponent pairing is equivariant for the original Galois root
action and the trivial finite-character coefficient action. -/
theorem galoisRootExponentPairing_equivariant (g : Gal(Ω/K))
    (x : galoisRootOfUnityRepresentation (K := K) (Ω := Ω) n) (t : ZMod n) :
    galoisRootExponentPairing n
      ((galoisRootOfUnityRepresentation (K := K) (Ω := Ω) n).ρ g x)
      ((Rep.of (1 : Representation ℤ Gal(Ω/K) (ZMod n))).ρ g t) =
    (galoisRootOfUnityRepresentation (K := K) (Ω := Ω) n).ρ g
      (galoisRootExponentPairing n x t) := by
  apply Rep.toAdditive.injective
  apply Subtype.ext
  change ((Additive.toMul (Rep.toAdditive
    (galoisRootExponentPairing n
      ((galoisRootOfUnityRepresentation (K := K) (Ω := Ω) n).ρ g x) t)) :
        rootsOfUnity n Ω) : Ωˣ) =
      g • ((Additive.toMul (Rep.toAdditive (galoisRootExponentPairing n x t)) :
        rootsOfUnity n Ω) : Ωˣ)
  rw [galoisRootExponentPairing_apply, galoisRootExponentPairing_apply]
  exact (smul_pow' g _ t.val).symm

end
end Dubon2026
