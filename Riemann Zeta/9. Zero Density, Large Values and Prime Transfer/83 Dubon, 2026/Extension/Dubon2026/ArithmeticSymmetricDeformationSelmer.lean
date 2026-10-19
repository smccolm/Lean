import Dubon2026.RationalRegularPrimeInertia
import Dubon2026.ArithmeticSymmetricDimensionalSelmer

/-! The same selected primes kill original dual Selmer and have the
dimension of the actual unramified fixed-determinant deformation subspace.
Residual inertia triviality is derived at each prime. Together with the
actual-lift comparison, this supplies the first-order unramified local
condition in DUB-17's chain to arithmetic patching. Full Taylor-Wiles local
rings and the arithmetic Hecke comparison remain separate obligations. -/

namespace Dubon2026
noncomputable section
open Matrix
open scoped NumberField MatrixGroups
attribute [local instance] exceptionalTraceRootTopology exceptionalTraceRootDiscrete
  exceptionalTraceUnitTopology exceptionalTraceUnitDiscrete

/-- The existing symmetric-degree bound makes the original residual
matrix rank invertible, without an extra coefficient assumption. -/
theorem symmetric_auxiliary_rank_ne_zero
    (q degree : ℕ) (hsize : 2 * degree < q - 1) :
    (Fintype.card (Fin (degree + 1)) : ZMod q) ≠ 0 := by
  rw [Fintype.card_fin]
  intro h
  have hd := (ZMod.natCast_eq_zero_iff (degree + 1) q).mp h
  have hlt : degree + 1 < q := by omega
  exact Nat.not_dvd_of_pos_of_lt (Nat.succ_pos degree) hlt hd

/-- The same original dual-Selmer-killing family has actual residually
trivial inertia and the genuine unramified fixed-determinant first-order
dimension, as well as its original regularity and congruence conditions. -/
theorem rationalArithmetic_symmetric_deformation_auxiliary_dualSelmer_eq_bot
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
      (∀ p ∈ Q, p.val ∉ S ∧ RationalArithmeticRegularAuxiliaryPrime a q level R p ∧
        (rationalPrimeNormInertia p.val p.property ≤
          (R.comp (rationalPrimeArithmeticRestriction a p.val p.property).toMonoidHom).ker) ∧
        Module.finrank (ZMod q) (continuousUnramifiedFixedDeterminantClasses
          (R.comp (rationalPrimeArithmeticRestriction a p.val p.property).toMonoidHom)
          (hR.comp (rationalPrimeArithmeticRestriction a p.val p.property).continuous)
          (rationalPrimeNormInertia p.val p.property)) = degree) ∧
      P ⊓ LinearMap.ker (LinearMap.pi fun p : Q =>
        show RationalArithmeticTraceDualH1 a q hqa R hR →ₗ[ZMod q]
          rationalArithmeticPrimeTraceDualH1Module a q R hR p.val from
            rationalPrimeCyclotomicAdjointH1Restriction a q hqa p.val.val p.val.property R hR) = ⊥ := by
  let R := (homogeneousSymmetricGL degree).comp ρ
  let hR := (homogeneousSymmetricGL_continuous degree).comp hρ
  have hfamily := rationalArithmetic_symmetric_dimensional_auxiliary_dualSelmer_eq_bot
    a ha q degree level hqa hsize ρ hρ himage C S
  obtain ⟨Q, hcard, hQ, hzero⟩ := hfamily
  refine ⟨Q, hcard, ?_, hzero⟩
  intro p hp
  have hprime := hQ p hp
  refine ⟨hprime.1, hprime.2.1,
    rationalArithmetic_regular_auxiliary_inertia a q level R p hprime.2.1, ?_⟩
  have he := (continuousUnramifiedTraceFixedDeterminantEquiv
    (symmetric_auxiliary_rank_ne_zero q degree hsize)
    (R.comp (rationalPrimeArithmeticRestriction a p.val p.property).toMonoidHom)
    (hR.comp (rationalPrimeArithmeticRestriction a p.val p.property).continuous)
    (rationalPrimeNormInertia p.val p.property)).finrank_eq
  exact he.symm.trans hprime.2.2

end
end Dubon2026
