import Dubon2026.ArithmeticSymmetricNonzeroClassPrimes
import Dubon2026.FiniteDetectingFamily
import Dubon2026.ArithmeticTraceGlobalH1Finite

/-! Dimension-bounded families of genuine regular auxiliary primes.
The original global H1 finiteness and individual prime theorem construct
jointly injective restriction on every dual Selmer subspace. This is the
auxiliary-family input to DUB-17's arithmetic patching route. -/

namespace Dubon2026
noncomputable section
open Matrix
open scoped NumberField MatrixGroups
attribute [local instance] rationalArithmeticOriginalFiniteGalois

/-- A good congruence prime with a finite factor of the original residual
representation and a literal original local Frobenius of regular image. -/
def RationalArithmeticRegularAuxiliaryPrime
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (a : 𝓞 ℚ) (q level : ℕ) [Fact q.Prime]
    (R : rationalArithmeticGaloisGroup a →* GeneralLinearGroup ι (ZMod q))
    (p : Nat.Primes) : Prop :=
  ¬ (p.val : 𝓞 ℚ) ∣ a ∧ p.val ≡ 1 [MOD q ^ level] ∧
  (let U := rationalUnramifiedExtension a
   letI : Algebra ℚ U := U.algebra'
   letI : IsGalois ℚ U := originalUnramifiedGaloisUnion_isGalois a
   ∃ F : FiniteGaloisIntermediateField ℚ U,
     ∃ ψ : Gal(F/ℚ) →* GeneralLinearGroup ι (ZMod q),
       (∀ w : Gal(U/ℚ), ψ (AlgEquiv.restrictNormalHom F w) = R w) ∧
       (letI : NumberField F := NumberField.of_module_finite ℚ F
        Chebotarev.UnramifiedIn ℚ F (Ideal.span {(p.val : 𝓞 ℚ)}) ∧
        ∃ γ : Gal(rationalPrimeLocalClosure p.val p.property /
            rationalPrimeLocalField p.val p.property),
          Chebotarev.frobeniusClass ℚ F (Ideal.span {(p.val : 𝓞 ℚ)}) =
            ConjClasses.mk (AlgEquiv.restrictNormalHom F
              (rationalPrimeArithmeticRestriction a p.val p.property γ)) ∧
          (R (rationalPrimeArithmeticRestriction a p.val p.property γ)).val.charpoly.Separable))

variable (a : 𝓞 ℚ) (ha : a ≠ 0) (q degree level : ℕ) [Fact q.Prime]
  [NeZero (2 : ZMod q)] [NeZero (3 : ZMod q)]
  (hqa : (q : 𝓞 ℚ) ∣ a) (hsize : 2 * degree < q - 1)
  (ρ : rationalArithmeticGaloisGroup a →* GeneralLinearGroup (Fin 2) (ZMod q))
  (hρ : Continuous ρ)
  (himage : (SpecialLinearGroup.toGL (n := Fin 2) (R := ZMod q)).range ≤ ρ.range)

include ha hsize himage

/-- The individual regular-prime theorem applies to every actual H1 class,
independently of its chosen continuous cocycle representative. -/
theorem rationalArithmetic_symmetric_class_detecting_prime
    (x : RationalArithmeticTraceDualH1 a q hqa ((homogeneousSymmetricGL degree).comp ρ)
      ((homogeneousSymmetricGL_continuous degree).comp hρ)) (hx : x ≠ 0)
    (S : Finset ℕ) :
    ∃ p : Nat.Primes, p.val ∉ S ∧
      RationalArithmeticRegularAuxiliaryPrime a q level ((homogeneousSymmetricGL degree).comp ρ) p ∧
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
  have hprimes := rationalArithmetic_symmetric_nonzero_class_regular_primes
    a ha q degree level hqa hsize ρ hρ himage c hc'
  obtain ⟨F, hF'⟩ := hprimes
  obtain ⟨ψ, hψ, hF⟩ := hF'
  have hprime := hF S
  obtain ⟨p, hp, hpS, hpa, hmod, hunr, hlocal, hne⟩ := hprime
  refine ⟨⟨p, hp⟩, hpS, ⟨hpa, hmod, F, ψ, hψ, hunr, hlocal⟩, ?_⟩
  simpa only [hc] using hne

/-- Every original dual Selmer subspace is jointly detected at a family
of regular congruence primes of cardinality at most its actual dimension.
Global finite-dimensionality and the pointwise detection are derived. -/
theorem rationalArithmetic_symmetric_finite_detecting_family
    (P : Submodule (ZMod q) (RationalArithmeticTraceDualH1 a q hqa
      ((homogeneousSymmetricGL degree).comp ρ)
      ((homogeneousSymmetricGL_continuous degree).comp hρ)))
    (S : Finset ℕ) :
    ∃ Q : Finset Nat.Primes, Q.card ≤ Module.finrank (ZMod q) P ∧
      (∀ p ∈ Q, p.val ∉ S ∧ RationalArithmeticRegularAuxiliaryPrime a q level
        ((homogeneousSymmetricGL degree).comp ρ) p) ∧
      (∀ x : P, (∀ p ∈ Q, rationalPrimeCyclotomicAdjointH1Restriction a q hqa
        p.val p.property ((homogeneousSymmetricGL degree).comp ρ)
        ((homogeneousSymmetricGL_continuous degree).comp hρ) x.val = 0) → x = 0) := by
  classical
  let R := (homogeneousSymmetricGL degree).comp ρ
  let hR := (homogeneousSymmetricGL_continuous degree).comp hρ
  haveI := rationalArithmeticTraceDualH1_finite a q hqa ha R hR
  haveI : Module.Finite (ZMod q) P := Module.Finite.of_finite
  let L (p : Nat.Primes) : P →ₗ[ZMod q] rationalArithmeticPrimeTraceDualH1Module a q R hR p :=
    (rationalPrimeCyclotomicAdjointH1Restriction a q hqa p.val p.property R hR).comp P.subtype
  let Good (p : Nat.Primes) := p.val ∉ S ∧ RationalArithmeticRegularAuxiliaryPrime a q level R p
  have hdetect : ∀ T : Finset Nat.Primes, ∀ x : P, x ≠ 0 →
      ∃ p, p ∉ T ∧ Good p ∧ L p x ≠ 0 := by
    intro T x hx
    have hx' : x.val ≠ 0 := fun h => hx (Subtype.ext h)
    have hprimes := rationalArithmetic_symmetric_class_detecting_prime
      a ha q degree level hqa hsize ρ hρ himage
    have hprimeX := hprimes x.val hx' (S ∪ T.image Subtype.val)
    obtain ⟨p, hpX⟩ := hprimeX
    obtain ⟨hp, hgood, hne⟩ := hpX
    have hp' := Finset.notMem_union.mp hp
    refine ⟨p, fun hpT => hp'.2 (Finset.mem_image.mpr ⟨p, hpT, rfl⟩),
      ⟨hp'.1, hgood⟩, ?_⟩
    change rationalPrimeCyclotomicAdjointH1Restriction a q hqa p.val p.property R hR x.val ≠ 0
    exact hne
  have hfamily := finite_detecting_family_of_pointwise L Good hdetect ∅
  obtain ⟨Q, hcard, hQ, hzero⟩ := hfamily
  exact ⟨Q, hcard, fun p hp => (hQ p hp).2, hzero⟩

end
end Dubon2026
