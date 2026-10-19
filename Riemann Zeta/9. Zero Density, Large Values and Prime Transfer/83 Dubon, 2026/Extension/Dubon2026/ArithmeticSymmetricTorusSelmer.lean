import Dubon2026.ArithmeticSymmetricTorusFamily
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

/-- A dimension-bounded split regular auxiliary family has zero common
restriction kernel on the genuine original dual Selmer group. -/
theorem rationalArithmetic_symmetric_torus_auxiliary_dualSelmer_eq_bot
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
    let R := (homogeneousSymmetricGL degree).comp ρ
    let hR := (homogeneousSymmetricGL_continuous degree).comp hρ
    let P := rationalArithmeticTraceDualSelmer a q hqa ha R hR
      (rationalArithmeticTraceLocalConditionProduct a q ha R hR C)
    ∃ Q : Finset Nat.Primes, Q.card ≤ Module.finrank (ZMod q) P ∧
      (∀ p ∈ Q, p.val ∉ S ∧ RationalArithmeticTorusAuxiliaryPrime a q degree level R p ∧
        Module.finrank (ZMod q) (rationalPrimeUnramifiedTraceClasses p.val p.property q
          (R.comp (rationalPrimeArithmeticRestriction a p.val p.property).toMonoidHom)
          (hR.comp (rationalPrimeArithmeticRestriction a p.val p.property).continuous)) = degree) ∧
      P ⊓ LinearMap.ker (LinearMap.pi fun p : Q =>
        show RationalArithmeticTraceDualH1 a q hqa R hR →ₗ[ZMod q]
          rationalArithmeticPrimeTraceDualH1Module a q R hR p.val from
            rationalPrimeCyclotomicAdjointH1Restriction a q hqa p.val.val p.val.property R hR) = ⊥ := by
  let R := (homogeneousSymmetricGL degree).comp ρ
  let hR := (homogeneousSymmetricGL_continuous degree).comp hρ
  let P := rationalArithmeticTraceDualSelmer a q hqa ha R hR
    (rationalArithmeticTraceLocalConditionProduct a q ha R hR C)
  have hfam := rationalArithmetic_symmetric_finite_detecting_torus_family_with_dimension
    a ha q degree level hqa hsize ρ hρ himage P S
  obtain ⟨Q, hcard, hQ, hzero⟩ := hfam
  refine ⟨Q, hcard, hQ, le_antisymm ?_ bot_le⟩
  intro x hx
  have hres : ∀ p ∈ Q,
      rationalPrimeCyclotomicAdjointH1Restriction a q hqa p.val p.property R hR x = 0 := by
    intro p hp
    exact congrFun hx.2 ⟨p, hp⟩
  have hxzero := hzero ⟨x, hx.1⟩ hres
  exact congrArg Subtype.val hxzero

end
end Dubon2026
