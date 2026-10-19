import Dubon2026.ArithmeticKernelFunctionalPrimes
import Dubon2026.TraceCocycleKernelDetection
import Dubon2026.ArithmeticCyclotomicRootKernel
import Dubon2026.ArithmeticCyclotomicCohomologyRestriction

/-! Actual twisted trace-zero Selmer localization from the residual
kernel and commuting-matrix test. The character-one and functional-invariance
premises are derived from the original root and trace pairing. The output
uses the native prime-local cyclotomic H1 restriction, via its proved
coefficient equivalence. The residual-image existence step remains open. -/

namespace Dubon2026
noncomputable section
open Matrix
open scoped NumberField

variable {ι : Type} [Fintype ι] [DecidableEq ι]
  (a : 𝓞 ℚ) (q : ℕ) [Fact q.Prime] (hqa : (q : 𝓞 ℚ) ∣ a)
  (ρ : rationalArithmeticGaloisGroup a →* GeneralLinearGroup ι (ZMod q))
  (hρ : Continuous ρ)

/-- The native prime-local cyclotomic coefficient comparison preserves
nonvanishing of the original continuous H1 restriction. -/
theorem rationalPrimeCyclotomicAdjointH1Restriction_ne_zero_of_original
    (p : ℕ) (hp : p.Prime)
    (x : ContinuousRepresentationH1
      (matrixTraceZeroCharacterRep ρ
        (rationalArithmeticCyclotomicCoefficientCharacter a q hqa (ZMod q)).toMonoidHom)
      (matrixTraceZeroCharacterAction_continuous ρ hρ
        (rationalArithmeticCyclotomicCoefficientCharacter a q hqa (ZMod q)).toMonoidHom
        (rationalArithmeticCyclotomicCoefficientCharacter a q hqa (ZMod q)).continuous))
    (hx : rationalArithmeticH1PrimeRestriction a _ _ p hp x ≠ 0) :
    rationalPrimeCyclotomicAdjointH1Restriction a q hqa p hp ρ hρ x ≠ 0 := by
  let χG := rationalArithmeticCyclotomicCoefficientCharacter a q hqa (ZMod q)
  let χP := rationalPrimeCyclotomicCoefficientCharacter p hp q (ZMod q)
  let j := rationalPrimeArithmeticRestriction a p hp
  let e := continuousH1CoefficientCongr
    (rationalArithmeticTraceZeroCyclotomicTwist_restriction a q hqa ρ p hp)
    (restrictedCoefficientAction_continuous (matrixTraceZeroCharacterRep ρ χG.toMonoidHom)
      j.toMonoidHom j.continuous
      (matrixTraceZeroCharacterAction_continuous ρ hρ χG.toMonoidHom χG.continuous))
    (matrixTraceZeroCharacterAction_continuous (ρ.comp j.toMonoidHom)
      (hρ.comp j.continuous) χP.toMonoidHom χP.continuous)
  intro hz
  apply hx
  exact e.injective (hz.trans (map_zero e).symm)

/-- Root-fixing residual elements, a scalar kernel image and a commuting
trace-zero matrix with nonzero cocycle pairing give an actual good prime
detecting the original twisted trace H1 class. Its native prime-local
cyclotomic restriction is nonzero, and the original residual image is
conjugate to one of the two specified residual elements. -/
theorem rationalArithmetic_trace_exists_detecting_prime
    (ha : a ≠ 0) (n : ℕ)
    (c : continuousRepresentationCocyclesOne (matrixTraceZeroCharacterRep ρ
      (rationalArithmeticCyclotomicCoefficientCharacter a q hqa (ZMod q)).toMonoidHom)) :
    let U := rationalUnramifiedExtension a
    letI : Algebra ℚ U := U.algebra'
    letI : IsGalois ℚ U := originalUnramifiedGaloisUnion_isGalois a
    ∃ ζ : U, IsPrimitiveRoot ζ (q ^ (n + 1)) ∧
      ∀ g τ : Gal(U/ℚ), g ζ = ζ → τ ζ = ζ →
        ∀ d : ZMod q, (ρ τ).val = d • (1 : Matrix ι ι (ZMod q)) →
          ∀ M : matrixTraceZeroSubmodule ι (ZMod q),
            (ρ g).val * M.val = M.val * (ρ g).val →
            Matrix.trace ((c.val τ).val * M.val) ≠ 0 →
            ∀ S : Finset ℕ, ∃ p : ℕ, ∃ hp : p.Prime,
              p ∉ S ∧ ¬ (p : 𝓞 ℚ) ∣ a ∧ p ≡ 1 [MOD q ^ n] ∧
              (∃ γ : Gal(rationalPrimeLocalClosure p hp / rationalPrimeLocalField p hp),
                IsConj (ρ (rationalPrimeArithmeticRestriction a p hp γ)) (ρ g) ∨
                IsConj (ρ (rationalPrimeArithmeticRestriction a p hp γ)) (ρ (τ * g))) ∧
              rationalPrimeCyclotomicAdjointH1Restriction a q hqa p hp ρ hρ
                (Submodule.Quotient.mk c) ≠ 0 := by
  let U := rationalUnramifiedExtension a
  letI : Algebra ℚ U := U.algebra'
  letI : IsGalois ℚ U := originalUnramifiedGaloisUnion_isGalois a
  let χ := rationalArithmeticCyclotomicCoefficientCharacter a q hqa (ZMod q)
  let A := matrixTraceZeroCharacterRep ρ χ.toMonoidHom
  let hA := matrixTraceZeroCharacterAction_continuous ρ hρ χ.toMonoidHom χ.continuous
  let χres : rationalArithmeticGaloisGroup a →ₜ* GeneralLinearGroup ι (ZMod q) := ⟨ρ, hρ⟩
  have hprimes := rationalArithmetic_exists_prime_detecting_kernel_functional
    a ha q (n + 1) hqa A hA χres c
  obtain ⟨ζ, hζ, hF⟩ := hprimes
  refine ⟨ζ, hζ, ?_⟩
  intro g τ hg hτ d hscalar M hM hc S
  have hχg : χ g = 1 :=
    rationalArithmeticCyclotomicCoefficient_eq_one_of_fixed_power_root a q n hqa (ZMod q) hζ g hg
  have hχτ : χ τ = 1 :=
    rationalArithmeticCyclotomicCoefficient_eq_one_of_fixed_power_root a q n hqa (ZMod q) hζ τ hτ
  have hAτ := matrixTraceZeroCharacterRep_eq_one_of_scalar ρ χ.toMonoidHom τ hχτ d hscalar
  have hℓ := matrixTraceZero_traceFunctional_fixed ρ χ.toMonoidHom g hχg M hM
  have hselected := hF g τ hg hτ hAτ (matrixTraceZeroTracePairing.flip M) hℓ hc S
  obtain ⟨p, hp, hpS, hpa, hmod, himage, hne⟩ := hselected
  refine ⟨p, hp, hpS, hpa, hmod.of_dvd (pow_dvd_pow q (Nat.le_succ n)), himage, ?_⟩
  exact rationalPrimeCyclotomicAdjointH1Restriction_ne_zero_of_original
    a q hqa ρ hρ p hp (Submodule.Quotient.mk c) hne

end
end Dubon2026
