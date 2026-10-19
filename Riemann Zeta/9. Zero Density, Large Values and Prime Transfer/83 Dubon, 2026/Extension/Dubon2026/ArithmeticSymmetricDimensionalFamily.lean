import Dubon2026.ArithmeticSymmetricDimensionalPrime

/-! Dimension-bounded auxiliary-prime families that simultaneously kill
the original dual Selmer subspace and carry the proved local unramified
trace-zero dimension, for DUB-17's arithmetic patching dependency. -/

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

/-- Every original dual Selmer subspace is jointly detected at a family
of regular congruence primes of cardinality at most its actual dimension.
Global finite-dimensionality, pointwise detection and the original local
unramified dimension at each selected prime are derived. -/
theorem rationalArithmetic_symmetric_finite_detecting_family_with_dimension
    (P : Submodule (ZMod q) (RationalArithmeticTraceDualH1 a q hqa
      ((homogeneousSymmetricGL degree).comp ρ)
      ((homogeneousSymmetricGL_continuous degree).comp hρ)))
    (S : Finset ℕ) :
    ∃ Q : Finset Nat.Primes, Q.card ≤ Module.finrank (ZMod q) P ∧
      (∀ p ∈ Q, p.val ∉ S ∧ RationalArithmeticRegularAuxiliaryPrime a q level
        ((homogeneousSymmetricGL degree).comp ρ) p ∧
        Module.finrank (ZMod q) (rationalPrimeUnramifiedTraceClasses p.val p.property q
          (((homogeneousSymmetricGL degree).comp ρ).comp
            (rationalPrimeArithmeticRestriction a p.val p.property).toMonoidHom)
          (((homogeneousSymmetricGL_continuous degree).comp hρ).comp
            (rationalPrimeArithmeticRestriction a p.val p.property).continuous)) = degree) ∧
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
  let Good (p : Nat.Primes) := p.val ∉ S ∧ RationalArithmeticRegularAuxiliaryPrime a q level R p ∧
    Module.finrank (ZMod q) (rationalPrimeUnramifiedTraceClasses p.val p.property q
      (R.comp (rationalPrimeArithmeticRestriction a p.val p.property).toMonoidHom)
      (hR.comp (rationalPrimeArithmeticRestriction a p.val p.property).continuous)) = degree
  have hdetect : ∀ T : Finset Nat.Primes, ∀ x : P, x ≠ 0 →
      ∃ p, p ∉ T ∧ Good p ∧ L p x ≠ 0 := by
    intro T x hx
    have hx' : x.val ≠ 0 := fun h => hx (Subtype.ext h)
    have hprimes := rationalArithmetic_symmetric_class_detecting_prime_with_dimension
      a ha q degree level hqa hsize ρ hρ himage
    have hprimeX := hprimes x.val hx' (S ∪ T.image Subtype.val)
    obtain ⟨p, hpX⟩ := hprimeX
    obtain ⟨hp, hgood, hdim, hne⟩ := hpX
    have hp' := Finset.notMem_union.mp hp
    refine ⟨p, fun hpT => hp'.2 (Finset.mem_image.mpr ⟨p, hpT, rfl⟩),
      ⟨hp'.1, hgood, hdim⟩, ?_⟩
    change rationalPrimeCyclotomicAdjointH1Restriction a q hqa p.val p.property R hR x.val ≠ 0
    exact hne
  have hfamily := finite_detecting_family_of_pointwise L Good hdetect ∅
  obtain ⟨Q, hcard, hQ, hzero⟩ := hfamily
  exact ⟨Q, hcard, fun p hp => (hQ p hp).2, hzero⟩

end
end Dubon2026
