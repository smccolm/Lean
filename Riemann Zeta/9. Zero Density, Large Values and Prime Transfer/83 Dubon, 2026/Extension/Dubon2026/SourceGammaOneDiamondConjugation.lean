import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic

/-! DUB17/18 -> original all-weight association -> arithmetic Gamma1
realization -> diamond comparison on the actual parabolic H1.
Reuse the native Gamma0 character kernel to construct literal conjugation
on Gamma1. This is the single-coset route in the inspected TauCeti diamond
operators; no second modular-symbol space or normalizer theory is needed.
The coefficient and arithmetic comparisons are separate obligations. -/
namespace Dubon2026
open CongruenceSubgroup
open scoped MatrixGroups

theorem sourceGammaOneDiamond_conj_mem (N : ℕ) (g : Gamma0 N) (γ : Gamma1 N) :
    g.val * γ.val * g.val⁻¹ ∈ Gamma1 N := by
  let γ₀ : Gamma0 N := ⟨γ.val, Gamma1_in_Gamma0 N γ.property⟩
  have hγ : Gamma0Map N γ₀ = 1 := (Gamma1_mem N γ.val).mp γ.property |>.2.1
  have hker : g * γ₀ * g⁻¹ ∈ Gamma1' N := by
    change Gamma0Map N (g * γ₀ * g⁻¹) = 1
    rw [map_mul, map_mul, hγ, mul_one, ← map_mul, mul_inv_cancel, map_one]
  exact (Gamma1_mem N _).mpr ((Gamma1_to_Gamma0_mem _).mp hker)

/-- Literal conjugation by a Gamma0 lift on the actual Gamma1 subgroup. -/
def sourceGammaOneDiamondConjugation (N : ℕ) (g : Gamma0 N) : Gamma1 N →* Gamma1 N where
  toFun γ := ⟨g.val * γ.val * g.val⁻¹, sourceGammaOneDiamond_conj_mem N g γ⟩
  map_one' := by apply Subtype.ext; simp
  map_mul' γ δ := by apply Subtype.ext; simp [mul_assoc]

theorem sourceGammaOneDiamondConjugation_trace (N : ℕ) (g : Gamma0 N) (γ : Gamma1 N) :
    (sourceGammaOneDiamondConjugation N g γ).val.val.trace = γ.val.val.trace := by
  change (g.val * γ.val * g.val⁻¹).val.trace = γ.val.val.trace
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.trace_mul_comm,
    ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel_left]

theorem sourceGammaOneDiamondConjugation_mul (N : ℕ) (g h : Gamma0 N) (γ : Gamma1 N) :
    sourceGammaOneDiamondConjugation N (g * h) γ =
      sourceGammaOneDiamondConjugation N g (sourceGammaOneDiamondConjugation N h γ) := by
  apply Subtype.ext
  change (g.val * h.val) * γ.val * (g.val * h.val)⁻¹ =
    g.val * (h.val * γ.val * h.val⁻¹) * g.val⁻¹
  group

end Dubon2026
