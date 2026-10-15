import Dubon2026.ArithmeticTraceSUnitCartierDuality
import Dubon2026.PrimeDivisibleIntegerExt

/-! # Actual arithmetic S-unit integer Ext vanishing

The original unramified-root construction proves the target divisibility.
The free mod-q resolution therefore removes all positive integer Ext for the
actual trace coefficients. Equivariant/continuous comparisons remain separate.
-/

namespace Dubon2026
noncomputable section
open CategoryTheory CategoryTheory.Abelian
open scoped NumberField
attribute [local instance 1100] Rep.hV2

variable (K Ω : Type) [Field K] [Field Ω] [NumberField K] [Algebra K Ω]
  [IsAlgClosure K Ω] (a : 𝓞 K) (ha : a ≠ 0) (q : ℕ) [Fact q.Prime]
  (hqa : (q : 𝓞 K) ∣ a)

include hqa in
/-- The actual arithmetic S-unit coefficients have no positive integer Ext from prime-field modules. -/
theorem originalArithmeticSUnit_integerExt_eq_zero
    (A : Type) [AddCommGroup A] [Module (ZMod q) A] (n : ℕ)
    (x : Ext (ModuleCat.of ℤ A)
      (ModuleCat.of ℤ (originalArithmeticSUnitRepresentation K Ω a ha)) (n + 1)) : x = 0 := by
  apply primeDivisible_primeField_ext_eq_zero q
    (originalArithmeticSUnitRepresentation K Ω a ha) ?_ A n x
  intro u
  obtain ⟨v, hv⟩ := originalArithmeticSUnitPower_surjective K Ω a ha q hqa u
  exact ⟨v, (originalArithmeticSUnitPower_eq_zsmul K Ω a ha q v).symm.trans hv⟩

/-- The vanishing applies to the original trace-zero adjoint coefficients, with no Ext or
divisibility hypothesis supplied to the theorem. -/
theorem rationalArithmeticTraceSUnit_integerExt_eq_zero
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (a : 𝓞 ℚ) (ha : a ≠ 0) (q : ℕ) [Fact q.Prime] (hqa : (q : 𝓞 ℚ) ∣ a)
    (σ : rationalArithmeticGaloisGroup a →* Matrix.GeneralLinearGroup ι (ZMod q))
    (n : ℕ)
    (x : Ext (ModuleCat.of ℤ (rationalArithmeticTraceZeroIntegerRep a q σ))
      (ModuleCat.of ℤ (originalArithmeticSUnitRepresentation ℚ (AlgebraicClosure ℚ) a ha))
      (n + 1)) : x = 0 := by
  have hAlg : @AlgebraicClosure.instAlgebra ℚ _ ℚ _ (Algebra.id ℚ) =
      (inferInstance : Algebra ℚ (AlgebraicClosure ℚ)) := Subsingleton.elim _ _
  letI : IsAlgClosure ℚ (AlgebraicClosure ℚ) := by
    have h := AlgebraicClosure.instIsAlgClosure ℚ
    rw [hAlg] at h
    exact h
  letI : Module (ZMod q) (rationalArithmeticTraceZeroIntegerRep a q σ) :=
    inferInstanceAs (Module (ZMod q) (matrixTraceZeroSubmodule ι (ZMod q)))
  exact originalArithmeticSUnit_integerExt_eq_zero ℚ (AlgebraicClosure ℚ) a ha q hqa
    (rationalArithmeticTraceZeroIntegerRep a q σ) n x

end
end Dubon2026
