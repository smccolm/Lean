import Dubon2026.ArithmeticCyclotomicLocalFrobenius
import Mathlib.NumberTheory.Cyclotomic.Gal

/-! # The original unramified cyclotomic Frobenius character is p

The actual original root action identifies the original cyclotomic character
with the unit represented by p modulo the actual conductor. This is the
finite-group identity used in DUB-17's cyclotomic principal product.
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

/-- The original cyclotomic character sends the literal restricted arithmetic Frobenius to p modulo the original conductor. -/
theorem arithmeticCyclotomicFiniteLocal_frobenius_character
    (n : ℕ) [NeZero n] [IsCyclotomicExtension {n} ℚ F] (hpn : ¬p ∣ n)
    {ζ : F} (hζ : IsPrimitiveRoot ζ n) :
    letI : Algebra.FormallyUnramified 𝒪[rationalPrimeLocalField p hp]
        𝒪[rationalArithmeticFiniteLocalStage a F p hp] :=
      arithmeticCyclotomicFiniteLocalStage_integer_unramified a F p hp n hpn
    hζ.autToPow ℚ (rationalArithmeticFiniteLocalRestriction a F p hp
      (localFieldArithmeticFrobenius (rationalPrimeLocalField p hp)
        (rationalArithmeticFiniteLocalStage a F p hp))) =
      ZMod.unitOfCoprime p (hp.coprime_iff_not_dvd.mpr hpn) := by
  letI := arithmeticCyclotomicFiniteLocalStage_integer_unramified a F p hp n hpn
  apply Units.ext
  apply ZMod.val_injective
  apply hζ.pow_inj (ZMod.val_lt _) (ZMod.val_lt _)
  rw [hζ.autToPow_spec ℚ,
    arithmeticCyclotomicFiniteLocal_frobenius_root a F p hp n hpn ζ hζ.pow_eq_one,
    ZMod.coe_unitOfCoprime, ZMod.val_natCast, hζ.eq_orderOf, pow_mod_orderOf]

end
end Dubon2026
