import Dubon2026.SourceIntegralParabolicCharacterLift

/-! DUB-17/18 -> original Gamma1 Picard/H1 -> Abel-Jacobi -> unitary
multiplier logarithms. Consume the proved integral lift on the actual
Gamma1 subgroup at every nonzero level and every natural modulus. -/
namespace Dubon2026
open CongruenceSubgroup
open scoped MatrixGroups

theorem sourceGamma1_integral_parabolic_character_lift (N : ℕ) [NeZero N] (n : ℕ)
    (φ : Additive (Gamma1 N) →+ ZMod n)
    (hpar : ∀ γ : Gamma1 N, γ.val.val.trace ^ 2 = 4 → φ (Additive.ofMul γ) = 0)
    (hfin : ∀ γ : Gamma1 N, IsOfFinOrder γ → φ (Additive.ofMul γ) = 0) :
    ∃ x : Additive (Gamma1 N) →+ ℤ,
      (∀ γ : Gamma1 N, γ.val.val.trace ^ 2 = 4 → x (Additive.ofMul γ) = 0) ∧
      (Int.castAddHom (ZMod n)).comp x = φ :=
  SourceIntegralCharacterLift.exists_int_lift (Gamma1 N) n φ hpar hfin

end Dubon2026
