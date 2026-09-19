import TaoTrudgianYang2025.ZeroCountBridge
import Mathlib.Data.EReal.Basic

/-!
# Zero-density exponent semantics

This module states the paper's non-asymptotic epsilon-loss predicate using the
actual multiplicity-weighted zero count. The exponent itself is the extended-
real infimum, allowing the value `-∞` when a half-plane is eventually
zero-free.
-/

namespace TaoTrudgianYang2025

/-- A real exponent `A` satisfies the paper's zero-density estimate at `σ`.
The real-part shift `δ` and the loss `ε` have the source quantifier order. -/
def IsZeroDensityBound (σ A : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ C : ℝ, 1 ≤ C ∧
      ∃ δ : ℝ, 0 < δ ∧
        ∀ T : ℝ, C ≤ T →
          (paperZeroCount (σ - δ) T : ℝ) ≤
            C * T ^ (A * (1 - σ) + ε)

/-- The real candidates entering the definition of `A(σ)`. -/
def zeroDensityBounds (σ : ℝ) : Set ℝ :=
  {A | IsZeroDensityBound σ A}

/-- The paper's zero-density exponent, valued in the extended reals so that
an eventually zero-free region can have exponent `-∞`. -/
noncomputable def zeroDensityExponent (σ : ℝ) : EReal :=
  sInf (((fun A : ℝ ↦ (A : EReal)) '' zeroDensityBounds σ) : Set EReal)

theorem mem_zeroDensityBounds {σ A : ℝ} :
    A ∈ zeroDensityBounds σ ↔ IsZeroDensityBound σ A :=
  Iff.rfl

/-- Every proved non-asymptotic bound is an upper bound for the infimum
defining the density exponent. -/
theorem zeroDensityExponent_le_of_bound {σ A : ℝ}
    (hA : IsZeroDensityBound σ A) :
    zeroDensityExponent σ ≤ (A : EReal) := by
  apply sInf_le
  exact ⟨A, hA, rfl⟩

/-- On the source range `σ < 1`, weakening the real exponent preserves a
zero-density bound. -/
theorem IsZeroDensityBound.mono {σ A B : ℝ}
    (hσ : σ < 1) (hA : IsZeroDensityBound σ A) (hAB : A ≤ B) :
    IsZeroDensityBound σ B := by
  intro ε hε
  obtain ⟨C, hC, δ, hδ, hbound⟩ := hA ε hε
  refine ⟨C, hC, δ, hδ, ?_⟩
  intro T hCT
  calc
    (paperZeroCount (σ - δ) T : ℝ) ≤
        C * T ^ (A * (1 - σ) + ε) := hbound T hCT
    _ ≤ C * T ^ (B * (1 - σ) + ε) := by
      apply mul_le_mul_of_nonneg_left _ (zero_le_one.trans hC)
      apply Real.rpow_le_rpow_of_exponent_le (hC.trans hCT)
      nlinarith

end TaoTrudgianYang2025
