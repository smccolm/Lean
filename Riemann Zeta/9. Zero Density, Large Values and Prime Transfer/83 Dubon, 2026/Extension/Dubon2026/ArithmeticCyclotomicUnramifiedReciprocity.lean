import Dubon2026.ArithmeticCyclotomicFrobeniusCharacter
import Dubon2026.LocalFieldFrobeniusCharacterImage
import Mathlib.NumberTheory.Cyclotomic.Gal

/-! # The actual unramified cyclotomic local reciprocity character

The original normalized reciprocity map, actual field restriction and original
cyclotomic character give the prime raised to the original positive valuation.
Unramifiedness and local cyclicity are derived, so neither is an endpoint
premise. This is the unramified factor in DUB-17's principal-product route to
the actual arithmetic invariant sum-zero theorem and then global duality.
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


variable [TopologicalSpace (Rep.ofAlgebraAutOnUnits
    (rationalPrimeLocalField p hp) (rationalPrimeLocalClosure p hp))]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits
    (rationalPrimeLocalField p hp) (rationalPrimeLocalClosure p hp))]

/-- At a prime not dividing the conductor, the original local reciprocity character is the prime to the original normalized order. -/
theorem arithmeticCyclotomicFiniteLocal_reciprocity_character
    (n : ℕ) [NeZero n] [IsCyclotomicExtension {n} ℚ F] (hpn : ¬p ∣ n)
    {ζ : F} (hζ : IsPrimitiveRoot ζ n) (u : (rationalPrimeLocalField p hp)ˣ) :
    letI : Algebra.FormallyUnramified 𝒪[rationalPrimeLocalField p hp]
        𝒪[rationalArithmeticFiniteLocalStage a F p hp] :=
      arithmeticCyclotomicFiniteLocalStage_integer_unramified a F p hp n hpn
    letI : IsCyclic Gal(rationalArithmeticFiniteLocalStage a F p hp /
        rationalPrimeLocalField p hp) :=
      (unramifiedLocalFieldResidueGaloisEquiv (rationalPrimeLocalField p hp)
        (rationalArithmeticFiniteLocalStage a F p hp)).isCyclic.mpr inferInstance
    hζ.autToPow ℚ (rationalArithmeticFiniteLocalRestriction a F p hp
      (localFieldFiniteCyclicReciprocity (rationalPrimeLocalField p hp)
        (rationalPrimeLocalClosure p hp) (rationalArithmeticFiniteLocalStage a F p hp)
        (Additive.ofMul u)).toMul) =
      ZMod.unitOfCoprime p (hp.coprime_iff_not_dvd.mpr hpn) ^
        localFieldUnitOrder (rationalPrimeLocalField p hp) (Additive.ofMul u) := by
  letI := arithmeticCyclotomicFiniteLocalStage_integer_unramified a F p hp n hpn
  letI : IsCyclic Gal(rationalArithmeticFiniteLocalStage a F p hp /
      rationalPrimeLocalField p hp) :=
    (unramifiedLocalFieldResidueGaloisEquiv (rationalPrimeLocalField p hp)
      (rationalArithmeticFiniteLocalStage a F p hp)).isCyclic.mpr inferInstance
  have hf := localFieldFiniteCyclicReciprocity_frobenius_image
    (rationalPrimeLocalField p hp) (rationalPrimeLocalClosure p hp)
    (rationalArithmeticFiniteLocalStage a F p hp)
    ((hζ.autToPow ℚ).comp (rationalArithmeticFiniteLocalRestriction a F p hp)) u
  exact hf.trans (congrArg (fun z => z ^
    localFieldUnitOrder (rationalPrimeLocalField p hp) (Additive.ofMul u))
      (arithmeticCyclotomicFiniteLocal_frobenius_character a F p hp n hpn hζ))

end
end Dubon2026
