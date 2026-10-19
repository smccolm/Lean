import Dubon2026.ArithmeticTorusAuxiliaryPrime
import Dubon2026.ArithmeticSymmetricConjugateClassPrimes
import Dubon2026.RationalPrimeSymmetricUnramifiedDimension
import Dubon2026.RationalPrimeUnramifiedTraceClasses
import Dubon2026.ArithmeticSymmetricDetectingFamily

/-! The same primes both detect the original dual Selmer classes and
have the proved original local unramified tangent dimension. This joins
the two required DUB-17 auxiliary-prime dependencies. -/

namespace Dubon2026
noncomputable section
open Matrix
open scoped NumberField MatrixGroups
attribute [local instance] rationalArithmeticOriginalFiniteGalois

variable (a : 𝓞 ℚ) (ha : a ≠ 0) (q degree level : ℕ) [Fact q.Prime]
  [NeZero (2 : ZMod q)] [NeZero (3 : ZMod q)]
  (hqa : (q : 𝓞 ℚ) ∣ a) (hsize : 2 * degree < q - 1)
  (ρ : rationalArithmeticGaloisGroup a →* GeneralLinearGroup (Fin 2) (ZMod q))
  (hρ : Continuous ρ)
  (himage : (SpecialLinearGroup.toGL (n := Fin 2) (R := ZMod q)).range ≤ ρ.range)

include ha hsize himage

/-- Every original nonzero dual H1 class is detected at a split regular good
congruence prime with the proved original local unramified dimension,
independently of its chosen continuous cocycle representative. -/
theorem rationalArithmetic_symmetric_class_detecting_torus_prime_with_dimension
    (x : RationalArithmeticTraceDualH1 a q hqa ((homogeneousSymmetricGL degree).comp ρ)
      ((homogeneousSymmetricGL_continuous degree).comp hρ)) (hx : x ≠ 0)
    (S : Finset ℕ) :
    ∃ p : Nat.Primes, p.val ∉ S ∧
      RationalArithmeticTorusAuxiliaryPrime a q degree level ((homogeneousSymmetricGL degree).comp ρ) p ∧
      Module.finrank (ZMod q) (rationalPrimeUnramifiedTraceClasses p.val p.property q
        (((homogeneousSymmetricGL degree).comp ρ).comp
          (rationalPrimeArithmeticRestriction a p.val p.property).toMonoidHom)
        (((homogeneousSymmetricGL_continuous degree).comp hρ).comp
          (rationalPrimeArithmeticRestriction a p.val p.property).continuous)) = degree ∧
      rationalPrimeCyclotomicAdjointH1Restriction a q hqa p.val p.property
        ((homogeneousSymmetricGL degree).comp ρ)
        ((homogeneousSymmetricGL_continuous degree).comp hρ) x ≠ 0 := by
  let R := (homogeneousSymmetricGL degree).comp ρ
  let hR := (homogeneousSymmetricGL_continuous degree).comp hρ
  let χ := rationalArithmeticCyclotomicCoefficientCharacter a q hqa (ZMod q)
  let A := matrixTraceZeroCharacterRep R χ.toMonoidHom
  let hA := matrixTraceZeroCharacterAction_continuous R hR χ.toMonoidHom χ.continuous
  have hsurj := (continuousRepresentationCoboundariesOne A hA).mkQ_surjective
  have hrep := hsurj x
  obtain ⟨c, hc⟩ := hrep
  change (Submodule.Quotient.mk c : ContinuousRepresentationH1 A hA) = x at hc
  have hc' : (Submodule.Quotient.mk c : RationalArithmeticTraceDualH1 a q hqa
      ((homogeneousSymmetricGL degree).comp ρ)
      ((homogeneousSymmetricGL_continuous degree).comp hρ)) ≠ 0 := by
    simpa only [hc] using hx
  have hprimes := rationalArithmetic_symmetric_nonzero_class_conjugate_primes
    a ha q degree level hqa hsize ρ hρ himage c hc'
  obtain ⟨u, hu, F, hF'⟩ := hprimes
  obtain ⟨ψ, hψ, hF⟩ := hF'
  have hprime := hF S
  obtain ⟨p, hp, hpS, hpa, hmod, hunr, hlocal, hne⟩ := hprime
  obtain ⟨γ, hγ, hconj, _⟩ := hlocal
  have hu' : 2 * degree < orderOf u := by rw [hu]; exact hsize
  have hdim := rationalPrime_symmetric_unramified_finrank a p hp q degree R hR F
  have hdim' := hdim ψ hψ hunr γ hγ u hu' hconj
  refine ⟨⟨p, hp⟩, hpS, ⟨hpa, hmod, u, hu', F, ψ, hψ, hunr, γ, hγ, hconj⟩, ?_, ?_⟩
  · let σ := R.comp (rationalPrimeArithmeticRestriction a p hp).toMonoidHom
    let hσ := hR.comp (rationalPrimeArithmeticRestriction a p hp).continuous
    have he := congrArg (fun T : Submodule (ZMod q) (ContinuousTraceZeroAdjointH1 σ hσ) =>
        Module.finrank (ZMod q) T)
      (rationalPrimeUnramifiedTraceClasses_eq_generic p hp q σ hσ)
    exact he.trans hdim'
  · simpa only [hc] using hne

end
end Dubon2026
