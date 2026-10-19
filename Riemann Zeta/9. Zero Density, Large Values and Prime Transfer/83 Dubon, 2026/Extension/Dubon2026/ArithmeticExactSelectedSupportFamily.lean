import Dubon2026.ArithmeticSelectedSupportFamily
import Dubon2026.ArithmeticSymmetricExactTorusSelmer

/-! The original selected-family property now has exactly the required
cardinality, so one fixed number of genuine auxiliary directions can
be used at every level in DUB-17's common parameter algebra. -/

namespace Dubon2026
noncomputable section
open Matrix
open scoped NumberField MatrixGroups
attribute [local instance] exceptionalTraceRootTopology exceptionalTraceRootDiscrete
  exceptionalTraceUnitTopology exceptionalTraceUnitDiscrete

/-- The full original family property and exact dual-Selmer dimension
hold for one actual selected family, without added zero directions. -/
theorem arithmeticSymmetric_exists_exactSelectedFamilyProperty
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
    ∃ Q : Finset Nat.Primes,
      ArithmeticSymmetricSelectedFamilyProperty a ha q degree level hqa ρ hρ C S Q ∧
      Q.card = Module.finrank (ZMod q) P := by
  unfold ArithmeticSymmetricSelectedFamilyProperty
  exact (rationalArithmetic_symmetric_exact_torus_auxiliary_dualSelmer_eq_bot
    a ha q degree level hqa hsize ρ hρ himage C S).imp
      (fun Q h => ⟨⟨h.1.le, h.2.1, h.2.2⟩, h.1⟩)

end
end Dubon2026
