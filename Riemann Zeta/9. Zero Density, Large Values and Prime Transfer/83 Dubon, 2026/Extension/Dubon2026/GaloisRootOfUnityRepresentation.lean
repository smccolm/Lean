import Mathlib.RingTheory.RootsOfUnity.Basic
import Mathlib.RepresentationTheory.Rep.Basic
import Mathlib.FieldTheory.Galois.Basic

/-! # The actual Galois representation on original roots of unity -/

namespace Dubon2026
noncomputable section

variable {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] (n : ℕ)

/-- The actual Galois automorphism acts on an original root-of-unity unit.
Its original nth power is preserved by that same field automorphism. -/
instance galoisRootOfUnitySMul : SMul Gal(Ω/K) (rootsOfUnity n Ω) where
  smul g u := ⟨g • u.val, by
    change (g • u.val) ^ n = 1
    rw [← smul_pow', u.property, smul_one]⟩

/-- The actual unit inclusion transfers the original multiplicative Galois
action to the original root subgroup, preserving its original multiplication. -/
instance galoisRootOfUnityMulDistribMulAction :
    MulDistribMulAction Gal(Ω/K) (rootsOfUnity n Ω) :=
  Function.Injective.mulDistribMulAction (rootsOfUnity n Ω).subtype
    Subtype.val_injective (fun _ _ => rfl)

/-- The original root inclusion is equivariant for the same original Galois action. -/
theorem galoisRootOfUnity_smul_val (g : Gal(Ω/K)) (u : rootsOfUnity n Ω) :
    ((g • u : rootsOfUnity n Ω) : Ωˣ) = g • (u : Ωˣ) := by
  rfl

/-- The original unit power map commutes with the original Galois action. -/
theorem galoisUnitPower_equivariant (g : Gal(Ω/K)) (u : Ωˣ) :
    (powMonoidHom n : Ωˣ →* Ωˣ) (g • u) =
      g • (powMonoidHom n : Ωˣ →* Ωˣ) u := by
  exact (smul_pow' g u n).symm

/-- The genuine integer-linear Galois representation on the additive tag of
the original root-of-unity group, with its actual automorphism action. -/
def galoisRootOfUnityRepresentation : Rep ℤ Gal(Ω/K) :=
  Rep.ofMulDistribMulAction Gal(Ω/K) (rootsOfUnity n Ω)

/-- The original representation acts by exactly the original Galois action
on the same root of unity, through the pinned additive-tag equivalence. -/
theorem galoisRootOfUnityRepresentation_apply (g : Gal(Ω/K))
    (x : galoisRootOfUnityRepresentation (K := K) (Ω := Ω) n) :
    (galoisRootOfUnityRepresentation (K := K) (Ω := Ω) n).ρ g x =
      Rep.toAdditive.symm (Additive.ofMul (g • Additive.toMul (Rep.toAdditive x))) := by
  rfl

end
end Dubon2026
