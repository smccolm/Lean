import Dubon2026.ArithmeticRootCoefficients

/-! # The actual compatible global-to-local root coefficient map

The coefficient map is proved to be the original field embedding on every
root, and to intertwine the original arithmetic restriction. It is the
coefficient edge for DUB-17's global reciprocity diagram.
-/

namespace Dubon2026
noncomputable section
open scoped NumberField

variable (a : 𝓞 ℚ) (q : ℕ) [Fact q.Prime] (hqa : (q : 𝓞 ℚ) ∣ a)
  (p : ℕ) (hp : p.Prime)

/-- Keep the original rational algebra structure for the actual embedding. -/
local instance arithmeticRootMapAlgebra : Algebra ℚ (rationalUnramifiedExtension a) :=
  (rationalUnramifiedExtension a).algebra'

/-- Keep the original arithmetic automorphism action on genuine roots. -/
local instance arithmeticRootMapAction :
    MulDistribMulAction (rationalArithmeticGaloisGroup a)
      (rootsOfUnity q (rationalUnramifiedExtension a)) :=
  galoisRootOfUnityMulDistribMulAction (K := ℚ) (Ω := rationalUnramifiedExtension a) q

/-- The original embedding of the global root group into the actual local
root group, expressed in the proved compatible scalar coordinates. -/
def rationalArithmeticRootLocalEquiv :
    rationalArithmeticRootRepresentation a q ≃+
      galoisRootOfUnityRepresentation
        (K := rationalPrimeLocalField p hp) (Ω := rationalPrimeLocalClosure p hp) q :=
  (rationalArithmeticRootCoefficientEquiv a q hqa).symm.trans
    (rationalArithmeticLocalRootCoefficientEquiv a q hqa p hp)

/-- This map is the actual arithmetic field embedding on every original
root, not just an abstract equivalence of cyclic groups. -/
theorem rationalArithmeticRootLocalEquiv_value
    (x : rationalArithmeticRootRepresentation a q) :
    (((Additive.toMul (Rep.toAdditive
      (rationalArithmeticRootLocalEquiv a q hqa p hp x)) :
        rootsOfUnity q (rationalPrimeLocalClosure p hp)) :
          (rationalPrimeLocalClosure p hp)ˣ) : rationalPrimeLocalClosure p hp) =
      rationalArithmeticLocalEmbedding a
        (((Additive.toMul (Rep.toAdditive x) :
          rootsOfUnity q (rationalUnramifiedExtension a)) :
            (rationalUnramifiedExtension a)ˣ) : rationalUnramifiedExtension a) := by
  obtain ⟨y, rfl⟩ := (rationalArithmeticRootCoefficientEquiv a q hqa).surjective x
  simpa only [rationalArithmeticRootLocalEquiv, AddEquiv.trans_apply,
    AddEquiv.symm_apply_apply] using
      (rationalArithmeticRootCoefficientEquiv_local a q hqa p hp y).symm

/-- The literal root map intertwines the genuine arithmetic restriction
with the original local action, using the already proved character identity. -/
theorem rationalArithmeticRootLocalEquiv_equivariant
    (g : Gal(rationalPrimeLocalClosure p hp / rationalPrimeLocalField p hp))
    (x : rationalArithmeticRootRepresentation a q) :
    rationalArithmeticRootLocalEquiv a q hqa p hp
      ((rationalArithmeticRootRepresentation a q).ρ
        (rationalPrimeArithmeticRestriction a p hp g) x) =
      (galoisRootOfUnityRepresentation
        (K := rationalPrimeLocalField p hp) (Ω := rationalPrimeLocalClosure p hp) q).ρ g
        (rationalArithmeticRootLocalEquiv a q hqa p hp x) := by
  obtain ⟨y, rfl⟩ := (rationalArithmeticRootCoefficientEquiv a q hqa).surjective x
  rw [← rationalArithmeticRootCoefficientEquiv_equivariant]
  simp only [rationalArithmeticRootLocalEquiv, AddEquiv.trans_apply,
    AddEquiv.symm_apply_apply]
  have hc := DFunLike.congr_fun
    (rationalArithmeticCyclotomicCoefficientCharacter_restriction a q hqa p hp (ZMod q)) g
  change rationalArithmeticLocalRootCoefficientEquiv a q hqa p hp
      (rationalArithmeticCyclotomicCoefficientCharacter a q hqa (ZMod q)
        (rationalPrimeArithmeticRestriction a p hp g) * y) = _
  rw [show rationalArithmeticCyclotomicCoefficientCharacter a q hqa (ZMod q)
      (rationalPrimeArithmeticRestriction a p hp g) =
      rationalPrimeCyclotomicCoefficientCharacter p hp q (ZMod q) g from hc]
  exact rationalArithmeticLocalRootCoefficientEquiv_equivariant a q hqa p hp g y

end
end Dubon2026
