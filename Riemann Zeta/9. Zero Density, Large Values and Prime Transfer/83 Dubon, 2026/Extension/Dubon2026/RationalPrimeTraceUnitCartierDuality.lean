import Dubon2026.GaloisUnitCartierHom
import Dubon2026.RationalPrimeCyclotomicH2Scalar
import Dubon2026.TraceZeroTwistedDuality

/-! # The actual prime-local trace dual in extension-field units

Reuse the native perfect trace pairing and the very same local primitive-root
normalization as the scalar H2 invariant. This supplies the local Cartier
coefficient input of the relation route for DUB-17 reverse localization.
-/

namespace Dubon2026
noncomputable section
open Matrix
attribute [local instance 1100] Rep.hV2

variable {ι : Type} [Fintype ι] [DecidableEq ι]
  (p : ℕ) (hp : p.Prime) (q : ℕ) [Fact q.Prime]
  (σ : Gal(rationalPrimeLocalClosure p hp / rationalPrimeLocalField p hp) →* GeneralLinearGroup ι (ZMod q))

/-- The same original trace-zero adjoint, with its integer-linear action. -/
def rationalPrimeTraceZeroIntegerRep : Rep ℤ (Gal(rationalPrimeLocalClosure p hp / rationalPrimeLocalField p hp)) :=
  Rep.of {
    toFun g := (matrixTraceZeroAdjointRepresentation σ g).toAddMonoidHom.toIntLinearMap
    map_one' := by
      apply LinearMap.ext
      intro x
      exact LinearMap.congr_fun (map_one (matrixTraceZeroAdjointRepresentation σ)) x
    map_mul' g h := by
      apply LinearMap.ext
      intro x
      exact LinearMap.congr_fun ((matrixTraceZeroAdjointRepresentation σ).map_mul g h) x }

/-- Retain the existing prime-field scalar structure on the same underlying trace module. -/
local instance primeTraceIntegerRepPrimeFieldModule :
    Module (ZMod q) (rationalPrimeTraceZeroIntegerRep p hp q σ) :=
  inferInstanceAs (Module (ZMod q) (matrixTraceZeroSubmodule ι (ZMod q)))

/-- The actual trace-zero coefficients are killed by the original prime, derived from their scalars. -/
theorem rationalPrimeTraceZeroIntegerRep_prime_annihilates
    (x : rationalPrimeTraceZeroIntegerRep p hp q σ) : (q : ℤ) • x = 0 := by
  let y : matrixTraceZeroSubmodule ι (ZMod q) := x
  exact (Int.cast_smul_eq_zsmul (R := ZMod q) (q : ℤ) y).symm.trans
    (by rw [Int.cast_natCast, ZMod.natCast_self, zero_smul]; rfl)

/-- Root-valued Hom for the original trace-zero adjoint is exactly extension-field unit-valued Hom. -/
def rationalPrimeTraceUnitCartierHomEquiv :
    (rationalPrimeTraceZeroIntegerRep p hp q σ →ₗ[ℤ]
      (galoisRootOfUnityRepresentation (K := rationalPrimeLocalField p hp)
        (Ω := rationalPrimeLocalClosure p hp) q)) ≃ₗ[ℤ]
    (rationalPrimeTraceZeroIntegerRep p hp q σ →ₗ[ℤ]
      Rep.ofAlgebraAutOnUnits (rationalPrimeLocalField p hp) (rationalPrimeLocalClosure p hp)) :=
  galoisUnitCartierHomEquiv (rationalPrimeLocalField p hp) (rationalPrimeLocalClosure p hp) q
    (rationalPrimeTraceZeroIntegerRep p hp q σ)
    (rationalPrimeTraceZeroIntegerRep_prime_annihilates p hp q σ)

/-- The specialization retains literal evaluation through the original root inclusion. -/
theorem rationalPrimeTraceUnitCartierHomEquiv_apply
    (f : rationalPrimeTraceZeroIntegerRep p hp q σ →ₗ[ℤ]
      (galoisRootOfUnityRepresentation (K := rationalPrimeLocalField p hp)
        (Ω := rationalPrimeLocalClosure p hp) q))
    (x : rationalPrimeTraceZeroIntegerRep p hp q σ) :
    rationalPrimeTraceUnitCartierHomEquiv p hp q σ f x =
      (galoisKummerInclusion (K := rationalPrimeLocalField p hp) (Ω := rationalPrimeLocalClosure p hp) q).hom (f x) := rfl

variable (hn : (Fintype.card ι : ZMod q) ≠ 0)

/-- The original trace dual is identified with integer-linear maps into the same prime-local roots. -/
def rationalPrimeTraceRootHomEquiv :
    matrixTraceZeroSubmodule ι (ZMod q) ≃+
      (rationalPrimeTraceZeroIntegerRep p hp q σ →ₗ[ℤ]
        (galoisRootOfUnityRepresentation (K := rationalPrimeLocalField p hp)
        (Ω := rationalPrimeLocalClosure p hp) q)) where
  toFun X := ((rationalPrimeCyclotomicRootCoefficientEquiv p hp q).toAddMonoidHom.comp
    ((matrixTraceZeroCharacterDuality hn σ
      (rationalPrimeCyclotomicCoefficientCharacter p hp q (ZMod q)).toMonoidHom X).toAddMonoidHom)).toIntLinearMap
  invFun f := (matrixTraceZeroCharacterDuality hn σ
      (rationalPrimeCyclotomicCoefficientCharacter p hp q (ZMod q)).toMonoidHom).symm
    (((rationalPrimeCyclotomicRootCoefficientEquiv p hp q).symm.toAddMonoidHom.comp
      f.toAddMonoidHom).toZModLinearMap q)
  left_inv X := by
    apply (matrixTraceZeroCharacterDuality hn σ
      (rationalPrimeCyclotomicCoefficientCharacter p hp q (ZMod q)).toMonoidHom).injective
    change (matrixTraceZeroCharacterDuality hn σ
      (rationalPrimeCyclotomicCoefficientCharacter p hp q (ZMod q)).toMonoidHom).toLinearEquiv
      ((matrixTraceZeroCharacterDuality hn σ
      (rationalPrimeCyclotomicCoefficientCharacter p hp q (ZMod q)).toMonoidHom).toLinearEquiv.symm _) = _
    rw [LinearEquiv.apply_symm_apply]
    apply LinearMap.ext
    intro Y
    exact (rationalPrimeCyclotomicRootCoefficientEquiv p hp q).symm_apply_apply _
  right_inv f := by
    apply LinearMap.ext
    intro Y
    change rationalPrimeCyclotomicRootCoefficientEquiv p hp q
      (matrixTraceZeroCharacterDuality hn σ
      (rationalPrimeCyclotomicCoefficientCharacter p hp q (ZMod q)).toMonoidHom
        ((matrixTraceZeroCharacterDuality hn σ
      (rationalPrimeCyclotomicCoefficientCharacter p hp q (ZMod q)).toMonoidHom).symm _) Y) = f Y
    rw [Representation.Equiv.apply_symm_apply]
    exact (rationalPrimeCyclotomicRootCoefficientEquiv p hp q).apply_symm_apply _
  map_add' X Y := by
    apply LinearMap.ext
    intro Z
    change rationalPrimeCyclotomicRootCoefficientEquiv p hp q
      (matrixTraceZeroCharacterDuality hn σ
      (rationalPrimeCyclotomicCoefficientCharacter p hp q (ZMod q)).toMonoidHom (X + Y) Z) = _
    rw [map_add, LinearMap.add_apply, map_add]
    rfl

/-- The constructed trace/root Hom comparison evaluates the original matrix trace. -/
theorem rationalPrimeTraceRootHomEquiv_apply
    (X Y : matrixTraceZeroSubmodule ι (ZMod q)) :
    rationalPrimeTraceRootHomEquiv p hp q σ hn X Y =
      rationalPrimeCyclotomicRootCoefficientEquiv p hp q (Matrix.trace (X.val * Y.val)) := by
  exact congrArg (rationalPrimeCyclotomicRootCoefficientEquiv p hp q)
    (matrixTraceZeroCharacterDuality_apply hn σ
      (rationalPrimeCyclotomicCoefficientCharacter p hp q (ZMod q)).toMonoidHom X Y)

/-- The original trace/root Hom identification intertwines the genuine prime-local actions. -/
theorem rationalPrimeTraceRootHomEquiv_equivariant
    (g : Gal(rationalPrimeLocalClosure p hp / rationalPrimeLocalField p hp)) (X : matrixTraceZeroSubmodule ι (ZMod q)) :
    rationalPrimeTraceRootHomEquiv p hp q σ hn
      (coefficientCharacterTwist (matrixTraceZeroAdjointRepresentation σ)
        (rationalPrimeCyclotomicCoefficientCharacter p hp q (ZMod q)).toMonoidHom g X) =
      Representation.linHom (rationalPrimeTraceZeroIntegerRep p hp q σ).ρ
        ((galoisRootOfUnityRepresentation (K := rationalPrimeLocalField p hp)
        (Ω := rationalPrimeLocalClosure p hp) q)).ρ g
        (rationalPrimeTraceRootHomEquiv p hp q σ hn X) := by
  apply LinearMap.ext
  intro Y
  have hd := LinearMap.congr_fun
    ((matrixTraceZeroCharacterDuality hn σ
      (rationalPrimeCyclotomicCoefficientCharacter p hp q (ZMod q)).toMonoidHom).isIntertwining' g) X
  have hv := congrArg (fun f : matrixTraceZeroSubmodule ι (ZMod q) →ₗ[ZMod q] ZMod q => f Y) hd
  exact (congrArg (rationalPrimeCyclotomicRootCoefficientEquiv p hp q) hv).trans
    (rationalPrimeCyclotomicRootCoefficientEquiv_equivariant p hp q g
      (matrixTraceZeroCharacterDuality hn σ
      (rationalPrimeCyclotomicCoefficientCharacter p hp q (ZMod q)).toMonoidHom X
        (matrixTraceZeroAdjointRepresentation σ g⁻¹ Y)))

/-- The original twisted trace coefficient is identified with the actual prime-local extension-field unit Hom. -/
def rationalPrimeTraceUnitDualEquiv :
    matrixTraceZeroSubmodule ι (ZMod q) ≃+
      (rationalPrimeTraceZeroIntegerRep p hp q σ →ₗ[ℤ]
        Rep.ofAlgebraAutOnUnits (rationalPrimeLocalField p hp) (rationalPrimeLocalClosure p hp)) :=
  (rationalPrimeTraceRootHomEquiv p hp q σ hn).trans
    (rationalPrimeTraceUnitCartierHomEquiv p hp q σ).toAddEquiv

/-- The original trace becomes its coherently normalized root in the actual extension-field unit group. -/
theorem rationalPrimeTraceUnitDualEquiv_apply
    (X Y : matrixTraceZeroSubmodule ι (ZMod q)) :
    rationalPrimeTraceUnitDualEquiv p hp q σ hn X Y =
      (galoisKummerInclusion (K := rationalPrimeLocalField p hp) (Ω := rationalPrimeLocalClosure p hp) q).hom
        (rationalPrimeCyclotomicRootCoefficientEquiv p hp q (Matrix.trace (X.val * Y.val))) := by
  exact congrArg (galoisKummerInclusion (K := rationalPrimeLocalField p hp) (Ω := rationalPrimeLocalClosure p hp) q).hom
    (rationalPrimeTraceRootHomEquiv_apply p hp q σ hn X Y)

/-- The extension-field unit-valued trace dual preserves the actual conjugate prime-local Galois action. -/
theorem rationalPrimeTraceUnitDualEquiv_equivariant
    (g : Gal(rationalPrimeLocalClosure p hp / rationalPrimeLocalField p hp)) (X : matrixTraceZeroSubmodule ι (ZMod q)) :
    rationalPrimeTraceUnitDualEquiv p hp q σ hn
      (coefficientCharacterTwist (matrixTraceZeroAdjointRepresentation σ)
        (rationalPrimeCyclotomicCoefficientCharacter p hp q (ZMod q)).toMonoidHom g X) =
      Representation.linHom (rationalPrimeTraceZeroIntegerRep p hp q σ).ρ
        (Rep.ofAlgebraAutOnUnits (rationalPrimeLocalField p hp) (rationalPrimeLocalClosure p hp)).ρ g
        (rationalPrimeTraceUnitDualEquiv p hp q σ hn X) := by
  change rationalPrimeTraceUnitCartierHomEquiv p hp q σ
    (rationalPrimeTraceRootHomEquiv p hp q σ hn
      (coefficientCharacterTwist (matrixTraceZeroAdjointRepresentation σ)
        (rationalPrimeCyclotomicCoefficientCharacter p hp q (ZMod q)).toMonoidHom g X)) = _
  rw [rationalPrimeTraceRootHomEquiv_equivariant]
  exact galoisUnitCartierHomEquiv_equivariant (rationalPrimeLocalField p hp) (rationalPrimeLocalClosure p hp) q
    (rationalPrimeTraceZeroIntegerRep p hp q σ)
    (rationalPrimeTraceZeroIntegerRep_prime_annihilates p hp q σ) g
    (rationalPrimeTraceRootHomEquiv p hp q σ hn X)

end
end Dubon2026
