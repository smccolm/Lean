import Dubon2026.ArithmeticCyclotomicLocalUnramified
import Dubon2026.RationalPrimeFrobeniusFieldRoots
import Dubon2026.ArithmeticFiniteLocalRestrictionSquare

/-! # Actual arithmetic local Frobenius on the original cyclotomic root

Unramifiedness is derived for the original cyclotomic local compositum.
Its original Frobenius acts by pth power on the embedded root, and literal
field restriction returns that equality on the same original global root.
This supplies the unramified cyclotomic action required by DUB-17's
principal product with no unramifiedness premise at the endpoint.
-/
namespace Dubon2026
noncomputable section
open scoped NumberField ValuativeRel

attribute [local instance] arithmeticFiniteLocalStageAlgebra
  arithmeticFiniteLocalStageGalois arithmeticFiniteLocalStageRationalAlgebra

variable (a : 𝓞 ℚ) (F : FiniteGaloisIntermediateField ℚ (rationalUnramifiedExtension a))
  (p : ℕ) (hp : p.Prime)
  [ValuativeRel (rationalArithmeticFiniteLocalStage a F p hp)]
  [TopologicalSpace (rationalArithmeticFiniteLocalStage a F p hp)]
  [IsNonarchimedeanLocalField (rationalArithmeticFiniteLocalStage a F p hp)]
  [(ValuativeRel.valuation (rationalPrimeLocalField p hp)).HasExtension
    (ValuativeRel.valuation (rationalArithmeticFiniteLocalStage a F p hp))]

/-- The original arithmetic local Frobenius restricts to pth power on the original cyclotomic root; local unramifiedness is derived from its actual conductor. -/
theorem arithmeticCyclotomicFiniteLocal_frobenius_root
    (n : ℕ) [NeZero n] [IsCyclotomicExtension {n} ℚ F] (hpn : ¬p ∣ n)
    (ζ : F) (hζ : ζ ^ n = 1) :
    letI : Algebra.FormallyUnramified 𝒪[rationalPrimeLocalField p hp]
        𝒪[rationalArithmeticFiniteLocalStage a F p hp] :=
      arithmeticCyclotomicFiniteLocalStage_integer_unramified a F p hp n hpn
    rationalArithmeticFiniteLocalRestriction a F p hp
      (localFieldArithmeticFrobenius (rationalPrimeLocalField p hp)
        (rationalArithmeticFiniteLocalStage a F p hp)) ζ = ζ ^ p := by
  letI := arithmeticCyclotomicFiniteLocalStage_integer_unramified a F p hp n hpn
  let j := rationalArithmeticFiniteLocalStageInclusion a F p hp
  have hj : (j ζ) ^ n = 1 := by rw [← map_pow, hζ, map_one]
  have hf := rationalPrimeArithmeticFrobenius_field_root p hp
    (rationalArithmeticFiniteLocalStage a F p hp) hpn (j ζ) hj
  apply j.injective
  change j (embeddedNormalGaloisRestriction j
    (localFieldArithmeticFrobenius (rationalPrimeLocalField p hp)
      (rationalArithmeticFiniteLocalStage a F p hp)) ζ) = j (ζ ^ p)
  rw [embeddedNormalGaloisRestriction_commutes, map_pow]
  exact hf

end
end Dubon2026
