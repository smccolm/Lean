import Dubon2026.ArithmeticSymmetricTorusSelmer
import Dubon2026.ArithmeticExceptionalTraceLocalConditions

/-! The selected actual auxiliary primes kill the original dual Selmer
subspace after imposing zero restriction at those primes. The original
exceptional local conditions and their scalar-cup orthogonality are retained.
Realizing these added conditions by arithmetic deformation rings and Hecke
modules is still required for DUB-17's automorphy-lifting dependency. -/

namespace Dubon2026
noncomputable section
open Matrix
open scoped NumberField MatrixGroups
attribute [local instance] exceptionalTraceRootTopology exceptionalTraceRootDiscrete
  exceptionalTraceUnitTopology exceptionalTraceUnitDiscrete

/-- The complete original selected-family property: cardinality,
avoidance, split torus congruence, local dimensions and zero common
dual-Selmer restriction kernel. This definition states the output;
the existence theorem below proves it from the native selection. -/
@[irreducible]
def ArithmeticSymmetricSelectedFamilyProperty
    (a : 𝓞 ℚ) (ha : a ≠ 0) (q degree level : ℕ) [Fact q.Prime]
    (hqa : (q : 𝓞 ℚ) ∣ a)
    (ρ : rationalArithmeticGaloisGroup a →* GeneralLinearGroup (Fin 2) (ZMod q))
    (hρ : Continuous ρ)
    (C : ∀ p : rationalArithmeticExceptionalPrimes a ha,
      Submodule (ZMod q) (rationalArithmeticPrimeTraceH1Module a q
        ((homogeneousSymmetricGL degree).comp ρ)
        ((homogeneousSymmetricGL_continuous degree).comp hρ) p.val))
    (S : Finset ℕ) (Q : Finset Nat.Primes) : Prop :=
    let R := (homogeneousSymmetricGL degree).comp ρ
    let hR := (homogeneousSymmetricGL_continuous degree).comp hρ
    let P := rationalArithmeticTraceDualSelmer a q hqa ha R hR
      (rationalArithmeticTraceLocalConditionProduct a q ha R hR C)
    Q.card ≤ Module.finrank (ZMod q) P ∧
      (∀ p ∈ Q, p.val ∉ S ∧ RationalArithmeticTorusAuxiliaryPrime a q degree level R p ∧
        Module.finrank (ZMod q) (rationalPrimeUnramifiedTraceClasses p.val p.property q
          (R.comp (rationalPrimeArithmeticRestriction a p.val p.property).toMonoidHom)
          (hR.comp (rationalPrimeArithmeticRestriction a p.val p.property).continuous)) = degree) ∧
      P ⊓ LinearMap.ker (LinearMap.pi fun p : Q =>
        show RationalArithmeticTraceDualH1 a q hqa R hR →ₗ[ZMod q]
          rationalArithmeticPrimeTraceDualH1Module a q R hR p.val from
            rationalPrimeCyclotomicAdjointH1Restriction a q hqa p.val.val p.val.property R hR) = ⊥

/-- The native arithmetic selection proves the entire named
family property with every original prime and local subspace retained. -/
theorem arithmeticSymmetric_exists_selectedFamilyProperty
    (a : 𝓞 ℚ) (ha : a ≠ 0) (q degree level : ℕ) [Fact q.Prime]
    [NeZero (2 : ZMod q)] [NeZero (3 : ZMod q)]
    (hqa : (q : 𝓞 ℚ) ∣ a) (hsize : 2 * degree < q - 1)
    (ρ : rationalArithmeticGaloisGroup a →* GeneralLinearGroup (Fin 2) (ZMod q))
    (hρ : Continuous ρ)
    (himage : (SpecialLinearGroup.toGL (n := Fin 2) (R := ZMod q)).range ≤ ρ.range)
    (C : ∀ p : rationalArithmeticExceptionalPrimes a ha,
      Submodule (ZMod q) (rationalArithmeticPrimeTraceH1Module a q
        ((homogeneousSymmetricGL degree).comp ρ)
        ((homogeneousSymmetricGL_continuous degree).comp hρ) p.val))
    (S : Finset ℕ) :
    ∃ Q : Finset Nat.Primes,
      ArithmeticSymmetricSelectedFamilyProperty a ha q degree level hqa ρ hρ C S Q := by
  unfold ArithmeticSymmetricSelectedFamilyProperty
  exact rationalArithmetic_symmetric_torus_auxiliary_dualSelmer_eq_bot
    a ha q degree level hqa hsize ρ hρ himage C S

/-- The retained native property supplies the exact good-prime
hypothesis used by the actual auxiliary deformation comparison. -/
theorem ArithmeticSymmetricSelectedFamilyProperty.good
    (a : 𝓞 ℚ) (ha : a ≠ 0) (q degree level : ℕ) [Fact q.Prime]
    (hqa : (q : 𝓞 ℚ) ∣ a)
    (ρ : rationalArithmeticGaloisGroup a →* GeneralLinearGroup (Fin 2) (ZMod q))
    (hρ : Continuous ρ)
    (C : ∀ p : rationalArithmeticExceptionalPrimes a ha,
      Submodule (ZMod q) (rationalArithmeticPrimeTraceH1Module a q
        ((homogeneousSymmetricGL degree).comp ρ)
        ((homogeneousSymmetricGL_continuous degree).comp hρ) p.val))
    (S : Finset ℕ) (Q : Finset Nat.Primes)
    (h : ArithmeticSymmetricSelectedFamilyProperty a ha q degree level hqa ρ hρ C S Q) :
    ∀ p : Q, RationalArithmeticTorusAuxiliaryPrime a q degree level
      ((homogeneousSymmetricGL degree).comp ρ) p.val := by
  unfold ArithmeticSymmetricSelectedFamilyProperty at h
  exact fun p => (h.2.1 p.val p.property).2.1

end
end Dubon2026
