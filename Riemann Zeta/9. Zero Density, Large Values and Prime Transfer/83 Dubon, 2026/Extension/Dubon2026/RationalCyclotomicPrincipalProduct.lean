import Dubon2026.RationalCyclotomicPrincipalStageBridge
import Dubon2026.RationalPrimeCyclotomicPrincipalCharacter

/-! # The actual rational cyclotomic principal product -/

namespace Dubon2026
noncomputable section

open IsDedekindDomain HeightOneSpectrum Metric
open scoped NumberField ValuativeRel

set_option maxHeartbeats 1200000
set_option synthInstance.maxHeartbeats 200000

attribute [local instance] arithmeticFiniteLocalStageAlgebra
  arithmeticFiniteLocalStageGalois arithmeticFiniteLocalStageRationalAlgebra

/-- The ramified reciprocity value, real sign, and all nontrivial away-prime
reciprocity values of a rational principal element multiply to the identity
on every actual rational prime-power cyclotomic stage. -/
theorem rationalPrimeNormalizedResidual_exists_arithmetic_principal_product
    (a : 𝓞 ℚ)
    (F : FiniteGaloisIntermediateField ℚ (rationalUnramifiedExtension a))
    [IsCyclic Gal(F/ℚ)]
    (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (m : ℕ)
    [IsCyclotomicExtension {p ^ (m + 1)} ℚ F]
    {ζ : F} (hζ : IsPrimitiveRoot ζ (p ^ (m + 1))) (q : ℚˣ) :
    let N := p ^ (m + 1)
    letI : NeZero N := ⟨pow_ne_zero _ hp.ne_zero⟩
    let r := rationalPrimeNormalizedResidual p hp q
    ∃ S : Finset (HeightOneSpectrum ℤ),
        (∀ v ∈ S, ¬Rat.HeightOneSpectrum.natGenerator v ∣ N) ∧
        (∀ v ∉ S, v.valuation ℚ r.val = 1) ∧
        (if 0 < r.val then (1 : ℚ) else -1) *
          (∏ v ∈ S, (Rat.HeightOneSpectrum.natGenerator v : ℚ) ^
            localFieldUnitOrder
              (rationalPrimeLocalField (Rat.HeightOneSpectrum.natGenerator v)
                (Rat.HeightOneSpectrum.prime_natGenerator v))
              (Additive.ofMul
                (rationalPrimeRationalUnit (Rat.HeightOneSpectrum.natGenerator v)
                  (Rat.HeightOneSpectrum.prime_natGenerator v) r))) = r.val ∧
        rationalArithmeticFiniteLocalReciprocityAut a F p hp r *
          arithmeticCyclotomicSignedAwayProduct a F N S r = 1 := by
  dsimp only
  let N := p ^ (m + 1)
  letI : NeZero N := ⟨pow_ne_zero _ hp.ne_zero⟩
  let r := rationalPrimeNormalizedResidual p hp q
  obtain ⟨S, hS, houtside, hproduct, c, d, hc0, hd0, hd, hc, u, hu,
      b, e, hcc, hce, hcb, hcd, hcbInv, hdeInv, _haction, hchar⟩ :=
    rationalPrimeNormalizedResidual_exists_cyclotomic_principal_character
      p hp hp2 m q
  refine ⟨S, hS, houtside, hproduct, ?_⟩
  have hram := rationalArithmeticFiniteLocalRestriction_ramified_autToPow
    a F p hp hp2 m hζ c u hu hc r
  have haway := arithmeticCyclotomicSignedAwayProduct_autToPow
    a F N S hS hζ r
  apply hζ.autToPow_injective ℚ
  rw [map_mul, hram, haway]
  simpa only [rationalPrimeOriginalCyclotomicReciprocityAut, r, N, map_one] using hchar

end
end Dubon2026
