import Dubon2026.ArithmeticSUnitCartierHom
import Dubon2026.ArithmeticTraceZeroCyclotomicDuality
import Dubon2026.ArithmeticRootCoefficients

/-! # Actual trace-zero Cartier coefficients in arithmetic S-units

The original trace-zero action is restricted to the integers. Its coefficient
prime annihilator is derived from the original prime-field scalars. The actual
root-valued Hom identification therefore applies without a torsion premise.
-/

namespace Dubon2026
noncomputable section
open Matrix
open scoped NumberField
attribute [local instance 1100] Rep.hV2

variable {ι : Type} [Fintype ι] [DecidableEq ι]
  (a : 𝓞 ℚ) (ha : a ≠ 0) (q : ℕ) [Fact q.Prime]
  (σ : rationalArithmeticGaloisGroup a →* GeneralLinearGroup ι (ZMod q))

/-- The same original trace-zero adjoint, with its integer-linear action. -/
def rationalArithmeticTraceZeroIntegerRep : Rep ℤ (rationalArithmeticGaloisGroup a) :=
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
local instance traceIntegerRepPrimeFieldModule :
    Module (ZMod q) (rationalArithmeticTraceZeroIntegerRep a q σ) :=
  inferInstanceAs (Module (ZMod q) (matrixTraceZeroSubmodule ι (ZMod q)))

omit ha in
/-- The actual trace-zero coefficients are killed by the original prime, derived from their scalars. -/
theorem rationalArithmeticTraceZeroIntegerRep_prime_annihilates
    (x : rationalArithmeticTraceZeroIntegerRep a q σ) : (q : ℤ) • x = 0 := by
  let y : matrixTraceZeroSubmodule ι (ZMod q) := x
  exact (Int.cast_smul_eq_zsmul (R := ZMod q) (q : ℤ) y).symm.trans
    (by rw [Int.cast_natCast, ZMod.natCast_self, zero_smul]; rfl)

/-- Root-valued Hom for the original trace-zero adjoint is exactly S-unit-valued Hom. -/
def rationalArithmeticTraceSUnitCartierHomEquiv :
    (rationalArithmeticTraceZeroIntegerRep a q σ →ₗ[ℤ]
      rationalArithmeticRootRepresentation a q) ≃ₗ[ℤ]
    (rationalArithmeticTraceZeroIntegerRep a q σ →ₗ[ℤ]
      originalArithmeticSUnitRepresentation ℚ (AlgebraicClosure ℚ) a ha) :=
  originalArithmeticSUnitCartierHomEquiv ℚ (AlgebraicClosure ℚ) a ha q
    (rationalArithmeticTraceZeroIntegerRep a q σ)
    (rationalArithmeticTraceZeroIntegerRep_prime_annihilates a q σ)

/-- The specialization retains literal evaluation through the original root inclusion. -/
theorem rationalArithmeticTraceSUnitCartierHomEquiv_apply
    (f : rationalArithmeticTraceZeroIntegerRep a q σ →ₗ[ℤ]
      rationalArithmeticRootRepresentation a q)
    (x : rationalArithmeticTraceZeroIntegerRep a q σ) :
    rationalArithmeticTraceSUnitCartierHomEquiv a ha q σ f x =
      (originalArithmeticSUnitKummerInclusion ℚ (AlgebraicClosure ℚ) a ha q).hom (f x) := rfl

variable (hqa : (q : 𝓞 ℚ) ∣ a) (hn : (Fintype.card ι : ZMod q) ≠ 0)

/-- The original trace dual is identified with integer-linear maps into the same arithmetic roots. -/
def rationalArithmeticTraceRootHomEquiv :
    matrixTraceZeroSubmodule ι (ZMod q) ≃+
      (rationalArithmeticTraceZeroIntegerRep a q σ →ₗ[ℤ]
        rationalArithmeticRootRepresentation a q) where
  toFun X := ((rationalArithmeticRootCoefficientEquiv a q hqa).toAddMonoidHom.comp
    ((rationalArithmeticTraceZeroCyclotomicDuality a q hqa σ hn X).toAddMonoidHom)).toIntLinearMap
  invFun f := (rationalArithmeticTraceZeroCyclotomicDuality a q hqa σ hn).symm
    (((rationalArithmeticRootCoefficientEquiv a q hqa).symm.toAddMonoidHom.comp
      f.toAddMonoidHom).toZModLinearMap q)
  left_inv X := by
    apply (rationalArithmeticTraceZeroCyclotomicDuality a q hqa σ hn).injective
    change (rationalArithmeticTraceZeroCyclotomicDuality a q hqa σ hn).toLinearEquiv
      ((rationalArithmeticTraceZeroCyclotomicDuality a q hqa σ hn).toLinearEquiv.symm _) = _
    rw [LinearEquiv.apply_symm_apply]
    apply LinearMap.ext
    intro Y
    exact (rationalArithmeticRootCoefficientEquiv a q hqa).symm_apply_apply _
  right_inv f := by
    apply LinearMap.ext
    intro Y
    change rationalArithmeticRootCoefficientEquiv a q hqa
      (rationalArithmeticTraceZeroCyclotomicDuality a q hqa σ hn
        ((rationalArithmeticTraceZeroCyclotomicDuality a q hqa σ hn).symm _) Y) = f Y
    rw [Representation.Equiv.apply_symm_apply]
    exact (rationalArithmeticRootCoefficientEquiv a q hqa).apply_symm_apply _
  map_add' X Y := by
    apply LinearMap.ext
    intro Z
    change rationalArithmeticRootCoefficientEquiv a q hqa
      (rationalArithmeticTraceZeroCyclotomicDuality a q hqa σ hn (X + Y) Z) = _
    rw [map_add, LinearMap.add_apply, map_add]
    rfl

/-- The constructed trace/root Hom comparison evaluates the original matrix trace. -/
theorem rationalArithmeticTraceRootHomEquiv_apply
    (X Y : matrixTraceZeroSubmodule ι (ZMod q)) :
    rationalArithmeticTraceRootHomEquiv a q σ hqa hn X Y =
      rationalArithmeticRootCoefficientEquiv a q hqa (Matrix.trace (X.val * Y.val)) := by
  exact congrArg (rationalArithmeticRootCoefficientEquiv a q hqa)
    (rationalArithmeticTraceZeroCyclotomicDuality_apply a q hqa σ hn X Y)

/-- The original trace/root Hom identification intertwines the genuine arithmetic actions. -/
theorem rationalArithmeticTraceRootHomEquiv_equivariant
    (g : rationalArithmeticGaloisGroup a) (X : matrixTraceZeroSubmodule ι (ZMod q)) :
    rationalArithmeticTraceRootHomEquiv a q σ hqa hn
      (rationalArithmeticTraceZeroCyclotomicTwist a q hqa σ g X) =
      Representation.linHom (rationalArithmeticTraceZeroIntegerRep a q σ).ρ
        (rationalArithmeticRootRepresentation a q).ρ g
        (rationalArithmeticTraceRootHomEquiv a q σ hqa hn X) := by
  apply LinearMap.ext
  intro Y
  have hd := LinearMap.congr_fun
    ((rationalArithmeticTraceZeroCyclotomicDuality a q hqa σ hn).isIntertwining' g) X
  have hv := congrArg (fun f : matrixTraceZeroSubmodule ι (ZMod q) →ₗ[ZMod q] ZMod q => f Y) hd
  exact (congrArg (rationalArithmeticRootCoefficientEquiv a q hqa) hv).trans
    (rationalArithmeticRootCoefficientEquiv_equivariant a q hqa g
      (rationalArithmeticTraceZeroCyclotomicDuality a q hqa σ hn X
        (matrixTraceZeroAdjointRepresentation σ g⁻¹ Y)))

/-- The original twisted trace coefficient is identified with the actual arithmetic S-unit Hom. -/
def rationalArithmeticTraceSUnitDualEquiv :
    matrixTraceZeroSubmodule ι (ZMod q) ≃+
      (rationalArithmeticTraceZeroIntegerRep a q σ →ₗ[ℤ]
        originalArithmeticSUnitRepresentation ℚ (AlgebraicClosure ℚ) a ha) :=
  (rationalArithmeticTraceRootHomEquiv a q σ hqa hn).trans
    (rationalArithmeticTraceSUnitCartierHomEquiv a ha q σ).toAddEquiv

/-- The original trace becomes its coherently normalized root in the actual S-unit group. -/
theorem rationalArithmeticTraceSUnitDualEquiv_apply
    (X Y : matrixTraceZeroSubmodule ι (ZMod q)) :
    rationalArithmeticTraceSUnitDualEquiv a ha q σ hqa hn X Y =
      (originalArithmeticSUnitKummerInclusion ℚ (AlgebraicClosure ℚ) a ha q).hom
        (rationalArithmeticRootCoefficientEquiv a q hqa (Matrix.trace (X.val * Y.val))) := by
  exact congrArg (originalArithmeticSUnitKummerInclusion ℚ (AlgebraicClosure ℚ) a ha q).hom
    (rationalArithmeticTraceRootHomEquiv_apply a q σ hqa hn X Y)

/-- The S-unit-valued trace dual preserves the actual conjugate arithmetic Galois action. -/
theorem rationalArithmeticTraceSUnitDualEquiv_equivariant
    (g : rationalArithmeticGaloisGroup a) (X : matrixTraceZeroSubmodule ι (ZMod q)) :
    rationalArithmeticTraceSUnitDualEquiv a ha q σ hqa hn
      (rationalArithmeticTraceZeroCyclotomicTwist a q hqa σ g X) =
      Representation.linHom (rationalArithmeticTraceZeroIntegerRep a q σ).ρ
        (originalArithmeticSUnitRepresentation ℚ (AlgebraicClosure ℚ) a ha).ρ g
        (rationalArithmeticTraceSUnitDualEquiv a ha q σ hqa hn X) := by
  change rationalArithmeticTraceSUnitCartierHomEquiv a ha q σ
    (rationalArithmeticTraceRootHomEquiv a q σ hqa hn
      (rationalArithmeticTraceZeroCyclotomicTwist a q hqa σ g X)) = _
  rw [rationalArithmeticTraceRootHomEquiv_equivariant]
  exact originalArithmeticSUnitCartierHomEquiv_equivariant ℚ (AlgebraicClosure ℚ) a ha q
    (rationalArithmeticTraceZeroIntegerRep a q σ)
    (rationalArithmeticTraceZeroIntegerRep_prime_annihilates a q σ) g
    (rationalArithmeticTraceRootHomEquiv a q σ hqa hn X)

end
end Dubon2026
