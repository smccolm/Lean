import Dubon2026.RationalCoherentRootH2Coordinate
import Dubon2026.RationalPrimeTraceUnitCartierDuality

/-! The normalized local Cartier map has the literal coherent global-root
value. This is needed when identifying DUB-17's recovered global S-unit
cocycle with the original trace-dual localization. -/
namespace Dubon2026
noncomputable section
open scoped NumberField
attribute [local instance 1100] Rep.hV2
attribute [local instance] exceptionalTraceRootTopology exceptionalTraceRootDiscrete
  exceptionalTraceUnitTopology exceptionalTraceUnitDiscrete

variable {ι : Type} [Fintype ι] [DecidableEq ι]
  (a : 𝓞 ℚ) (q : ℕ) [Fact q.Prime] (hqa : (q : 𝓞 ℚ) ∣ a)
  (p : ℕ) (hp : p.Prime)
  (ρ : Gal(rationalPrimeLocalClosure p hp / rationalPrimeLocalField p hp) →*
    Matrix.GeneralLinearGroup ι (ZMod q))
  (hn : (Fintype.card ι : ZMod q) ≠ 0)

/-- Scaling by the exact invariant-coordinate factor sends the original
trace value to the image of the same arithmetic primitive root. -/
theorem rationalPrimeTraceUnitDualEquiv_coherent_value
    (X Y : matrixTraceZeroSubmodule ι (ZMod q)) :
    rationalPrimeTraceUnitDualEquiv p hp q ρ hn
      (rationalArithmeticLocalNormalizationScalar a q hqa p hp • X) Y =
      (galoisKummerInclusion (K := rationalPrimeLocalField p hp)
        (Ω := rationalPrimeLocalClosure p hp) q).hom
        (rationalArithmeticLocalRootCoefficientEquiv a q hqa p hp (Matrix.trace (X.val * Y.val))) := by
  rw [rationalPrimeTraceUnitDualEquiv_apply]
  change (galoisKummerInclusion (K := rationalPrimeLocalField p hp)
      (Ω := rationalPrimeLocalClosure p hp) q).hom
      (rationalPrimeCyclotomicRootCoefficientEquiv p hp q
        (Matrix.trace ((rationalArithmeticLocalNormalizationScalar a q hqa p hp • X.val) * Y.val))) = _
  rw [Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul,
    ← rationalArithmeticLocalRootCoefficientEquiv_normalization]

end
end Dubon2026
