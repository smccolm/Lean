import Dubon2026.ArithmeticCyclotomicCoefficientCharacter
import Dubon2026.TraceZeroTwistedDuality

/-! # The actual arithmetic trace-zero cyclotomic dual and its local restriction -/

namespace Dubon2026
noncomputable section
open Matrix
open scoped NumberField

variable {ι k : Type} [Fintype ι] [DecidableEq ι] [Field k] [TopologicalSpace k]
variable (a : 𝓞 ℚ) (n : ℕ) [NeZero n] [CharP k n] (hna : (n : 𝓞 ℚ) ∣ a)
    (σ : rationalArithmeticGaloisGroup a →* GeneralLinearGroup ι k)

/-- The original trace-zero adjoint twisted by the genuine arithmetic cyclotomic
character in the same coefficient field. -/
def rationalArithmeticTraceZeroCyclotomicTwist :
    Representation k (rationalArithmeticGaloisGroup a) (matrixTraceZeroSubmodule ι k) :=
  coefficientCharacterTwist (matrixTraceZeroAdjointRepresentation σ)
    (rationalArithmeticCyclotomicCoefficientCharacter a n hna k).toMonoidHom

/-- Perfect trace duality identifies the actual arithmetic cyclotomic twist with
linear maps into its actual cyclotomic coefficient representation. This is coefficient
duality, not a local or global cohomological duality theorem. -/
def rationalArithmeticTraceZeroCyclotomicDuality (hn : (Fintype.card ι : k) ≠ 0) :
    Representation.Equiv (rationalArithmeticTraceZeroCyclotomicTwist a n hna σ)
      (Representation.linHom (matrixTraceZeroAdjointRepresentation σ)
        (coefficientCharacterTwist (1 : Representation k (rationalArithmeticGaloisGroup a) k)
          (rationalArithmeticCyclotomicCoefficientCharacter a n hna k).toMonoidHom)) :=
  matrixTraceZeroCharacterDuality hn σ
    (rationalArithmeticCyclotomicCoefficientCharacter a n hna k).toMonoidHom

/-- The constructed perfect arithmetic coefficient duality retains the literal
trace pairing of the same two original trace-zero matrices. -/
theorem rationalArithmeticTraceZeroCyclotomicDuality_apply
    (hn : (Fintype.card ι : k) ≠ 0) (X Y : matrixTraceZeroSubmodule ι k) :
    rationalArithmeticTraceZeroCyclotomicDuality a n hna σ hn X Y =
      Matrix.trace (X.val * Y.val) := by
  exact matrixTraceZeroCharacterDuality_apply hn σ
    (rationalArithmeticCyclotomicCoefficientCharacter a n hna k).toMonoidHom X Y

/-- Actual arithmetic restriction identifies the entire original cyclotomic twist
with the twist of the restricted matrices by the genuine prime-local character. -/
theorem rationalArithmeticTraceZeroCyclotomicTwist_restriction
    (p : ℕ) (hp : p.Prime) :
    (rationalArithmeticTraceZeroCyclotomicTwist a n hna σ).comp
        (rationalPrimeArithmeticRestriction a p hp).toMonoidHom =
      coefficientCharacterTwist
        (matrixTraceZeroAdjointRepresentation
          (σ.comp (rationalPrimeArithmeticRestriction a p hp).toMonoidHom))
        (rationalPrimeCyclotomicCoefficientCharacter p hp n k).toMonoidHom := by
  apply MonoidHom.ext
  intro g
  apply LinearMap.ext
  intro X
  have hc := DFunLike.congr_fun
    (rationalArithmeticCyclotomicCoefficientCharacter_restriction a n hna p hp k) g
  change rationalArithmeticCyclotomicCoefficientCharacter a n hna k
      (rationalPrimeArithmeticRestriction a p hp g) •
        matrixTraceZeroAdjointRepresentation σ (rationalPrimeArithmeticRestriction a p hp g) X =
    rationalPrimeCyclotomicCoefficientCharacter p hp n k g •
      matrixTraceZeroAdjointRepresentation
        (σ.comp (rationalPrimeArithmeticRestriction a p hp).toMonoidHom) g X
  rw [show rationalArithmeticCyclotomicCoefficientCharacter a n hna k
    (rationalPrimeArithmeticRestriction a p hp g) =
      rationalPrimeCyclotomicCoefficientCharacter p hp n k g from hc]
  apply congrArg
  apply Subtype.ext
  change (σ (rationalPrimeArithmeticRestriction a p hp g)).val * X.val *
    (σ ((rationalPrimeArithmeticRestriction a p hp g)⁻¹)).val =
    (σ (rationalPrimeArithmeticRestriction a p hp g)).val * X.val *
    (σ (rationalPrimeArithmeticRestriction a p hp g⁻¹)).val
  exact congrArg (fun y =>
    (σ (rationalPrimeArithmeticRestriction a p hp g)).val * X.val * (σ y).val)
      ((rationalPrimeArithmeticRestriction a p hp).map_inv g).symm

end
end Dubon2026
