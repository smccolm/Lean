/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

Adapted for the original Dubon coefficient route from
Nyll/ClassFieldTheory/LubinTate/Padic/ChangedUniformizerCoefficient.lean at
dc55774a7fe03e742f2b4c6114aab5e7d01edfb1. The Apache 2.0 license is retained
in Dependencies/NYLL-ClassFieldTheory-LICENSE.txt.
-/

import Dubon2026.AdicContractingAdditiveEquation
import Dubon2026.PrimeWittFrobeniusRotation
import Mathlib.RingTheory.WittVector.Complete

/-! # Higher semilinear coefficients over the actual Witt ring

The original degree-at-least-two coefficient operator raises the actual
prime-adic filtration, because Frobenius fixes p and the coefficient contains
p^(m-1). The complete-ring fixed-point proof therefore constructs its unique
coefficient. This serves the changed-uniformizer series, auxiliary field and
normed-uniformizer/Frobenius comparison required for DUB-17's ramified
cyclotomic formula, principal product and arithmetic invariant sum-zero.
-/
namespace Dubon2026
noncomputable section

private noncomputable def primeWittCoefficientOperator
    (p : ℕ) [Fact p.Prime]
    (u : (WittVector p (AlgebraicClosure (ZMod p)))ˣ)
    (m : ℕ) :
    WittVector p (AlgebraicClosure (ZMod p)) →+
      WittVector p (AlgebraicClosure (ZMod p)) where
  toFun a :=
    (↑(u⁻¹) :
        WittVector p (AlgebraicClosure (ZMod p))) *
      (p : WittVector p (AlgebraicClosure (ZMod p))) ^ (m - 1) *
      WittVector.frobenius a
  map_zero' := by simp
  map_add' a b := by
    simp only [map_add, mul_add]

private theorem primeWittCoefficientOperator_maps_pow_succ
    (p : ℕ) [Fact p.Prime]
    (u : (WittVector p (AlgebraicClosure (ZMod p)))ˣ)
    (m : ℕ) (hm : 2 ≤ m) :
    let I : Ideal (WittVector p (AlgebraicClosure (ZMod p))) :=
      Ideal.span ({(p : WittVector p (AlgebraicClosure (ZMod p)))} : Set _)
    ∀ (n : ℕ) {x : WittVector p (AlgebraicClosure (ZMod p))},
      x ∈ I ^ n →
        primeWittCoefficientOperator p u m x ∈
          I ^ (n + 1) := by
  dsimp only
  let W := WittVector p (AlgebraicClosure (ZMod p))
  let I : Ideal W := Ideal.span ({(p : W)} : Set W)
  let φ : W →+* W := WittVector.frobenius
  have hφI : I.map φ = I := by
    dsimp only [I]
    rw [Ideal.map_span, Set.image_singleton]
    dsimp only [φ]
    rw [map_natCast]
  have hpI : (p : W) ∈ I :=
    Ideal.subset_span (Set.mem_singleton (p : W))
  have hmPos : 0 < m - 1 := by omega
  have hpPowI : (p : W) ^ (m - 1) ∈ I :=
    I.pow_mem_of_mem hpI (m - 1) hmPos
  have hcI :
      (↑(u⁻¹) : W) *
          (p : W) ^ (m - 1) ∈ I :=
    I.mul_mem_left
      (↑(u⁻¹) : W)
      hpPowI
  intro n x hx
  have hφxMap : φ x ∈ (I ^ n).map φ :=
    Ideal.mem_map_of_mem φ hx
  have hφx : φ x ∈ I ^ n := by
    rw [Ideal.map_pow φ I n, hφI] at hφxMap
    exact hφxMap
  have hmul :
      ((↑(u⁻¹) : W) *
          (p : W) ^ (m - 1)) * φ x ∈ I * I ^ n :=
    Ideal.mul_mem_mul hcI hφx
  change
    ((↑(u⁻¹) : W) *
          (p : W) ^ (m - 1)) * φ x ∈ I ^ (n + 1)
  rw [pow_succ, mul_comm (I ^ n) I]
  exact hmul

/-- Every coefficient equation of degree at least two in the required
semilinear changed-uniformizer series has a unique solution in the completed-unramified
Witt ring. -/
theorem primeWitt_existsUnique_higher_coefficient
    (p : ℕ) [Fact p.Prime]
    (u : (WittVector p (AlgebraicClosure (ZMod p)))ˣ)
    (m : ℕ) (hm : 2 ≤ m)
    (b : WittVector p (AlgebraicClosure (ZMod p))) :
    ∃! a : WittVector p (AlgebraicClosure (ZMod p)),
      a =
        b +
          (↑(u⁻¹) :
              WittVector p (AlgebraicClosure (ZMod p))) *
            (p : WittVector p (AlgebraicClosure (ZMod p))) ^ (m - 1) *
            WittVector.frobenius a := by
  let I : Ideal (WittVector p (AlgebraicClosure (ZMod p))) :=
    Ideal.span
      ({(p : WittVector p (AlgebraicClosure (ZMod p)))} : Set _)
  change
    ∃! a : WittVector p (AlgebraicClosure (ZMod p)),
      a = b + primeWittCoefficientOperator p u m a
  exact
    adicComplete_existsUnique_affine_fixedPoint
      I (primeWittCoefficientOperator p u m)
      (primeWittCoefficientOperator_maps_pow_succ
        p u m hm)
      b

end
end Dubon2026
