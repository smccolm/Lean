import Dubon2026.ContinuousRootCharacterCup
import Dubon2026.CyclotomicRootAdditiveEquiv

/-! # Original root coefficients when the primitive root lies in the base field

This supplies the concrete trivial-action identification needed to apply the
existing cup skew symmetry to the opposite local nondegeneracy direction.
-/

namespace Dubon2026
noncomputable section

variable {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω]
  {n : ℕ} [NeZero n] {ζ : K} (hζ : IsPrimitiveRoot ζ n)

/-- The actual base primitive root identifies residue coefficients with the
original roots in the extension field. -/
def basePrimitiveRootCoefficientEquiv :
    ZMod n ≃+ galoisRootOfUnityRepresentation (K := K) (Ω := Ω) n :=
  (primitiveRootAdditiveEquiv (hζ.map_of_injective (algebraMap K Ω).injective)).trans
    Rep.toAdditive.symm

/-- The identification is the literal power of the original base root after
the given algebra map. -/
theorem basePrimitiveRootCoefficientEquiv_apply (x : ZMod n) :
    (((Additive.toMul (Rep.toAdditive (basePrimitiveRootCoefficientEquiv (Ω := Ω) hζ x)) :
      rootsOfUnity n Ω) : Ωˣ) : Ω) = algebraMap K Ω ζ ^ x.val :=
  primitiveRootAdditiveEquiv_apply (hζ.map_of_injective (algebraMap K Ω).injective) x

include hζ in
/-- Every original Galois automorphism fixes every actual root coefficient
when the primitive root is already in the base field. -/
theorem basePrimitiveRootCoefficient_action (g : Gal(Ω/K))
    (x : galoisRootOfUnityRepresentation (K := K) (Ω := Ω) n) :
    (galoisRootOfUnityRepresentation (K := K) (Ω := Ω) n).ρ g x = x := by
  obtain ⟨t, rfl⟩ := (basePrimitiveRootCoefficientEquiv (Ω := Ω) hζ).surjective x
  apply Rep.toAdditive.injective
  apply Subtype.ext
  apply Units.ext
  change g (((Additive.toMul (Rep.toAdditive
    (basePrimitiveRootCoefficientEquiv (Ω := Ω) hζ t)) : rootsOfUnity n Ω) : Ωˣ) : Ω) = _
  rw [basePrimitiveRootCoefficientEquiv_apply, map_pow, AlgEquiv.commutes]
  exact (basePrimitiveRootCoefficientEquiv_apply (Ω := Ω) hζ t).symm

/-- The two actual exponent pairings agree after the original primitive-root
identification. This is the coefficient symmetry used with cup skew symmetry. -/
theorem basePrimitiveRootExponentPairing_symm (x y : ZMod n) :
    galoisRootExponentPairing n (basePrimitiveRootCoefficientEquiv (Ω := Ω) hζ x) y =
      galoisRootExponentPairing n (basePrimitiveRootCoefficientEquiv (Ω := Ω) hζ y) x := by
  apply Rep.toAdditive.injective
  apply Subtype.ext
  apply Units.ext
  have hx := congrArg Units.val (galoisRootExponentPairing_apply n
    (basePrimitiveRootCoefficientEquiv (Ω := Ω) hζ x) y)
  have hy := congrArg Units.val (galoisRootExponentPairing_apply n
    (basePrimitiveRootCoefficientEquiv (Ω := Ω) hζ y) x)
  have hxy :
      (((Additive.toMul (Rep.toAdditive (basePrimitiveRootCoefficientEquiv (Ω := Ω) hζ x)) :
        rootsOfUnity n Ω) : Ωˣ) : Ω) ^ y.val =
      (((Additive.toMul (Rep.toAdditive (basePrimitiveRootCoefficientEquiv (Ω := Ω) hζ y)) :
        rootsOfUnity n Ω) : Ωˣ) : Ω) ^ x.val := by
    rw [basePrimitiveRootCoefficientEquiv_apply, basePrimitiveRootCoefficientEquiv_apply,
      ← pow_mul, ← pow_mul, Nat.mul_comm]
  exact hx.trans (hxy.trans hy.symm)

end
end Dubon2026
