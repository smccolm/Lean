/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanModularForms contributors

The Bezout representative adapts AdjointTheory.lean at LeanModularForms
7c41b9b1747d47298f76bdb51f07031087702198. The finite Gamma0 coset proof is local.
-/
import Dubon2026.ModularRealProjective
import Dubon2026.HeckePrimeOrbits

/-! # The genuine finite upper-congruence Hecke transversal -/

namespace Dubon2026

open Matrix.SpecialLinearGroup CongruenceSubgroup ModularGroup
open scoped MatrixGroups

noncomputable section

/-- The actual upper-right congruence subgroup inside Gamma0. -/
def heckeUpperSubgroup (Q p : ℕ) : Subgroup (Gamma0 Q) where
  carrier γ := ((γ.val 0 1 : ℤ) : ZMod p) = 0
  one_mem' := by
    change (((1 : Matrix (Fin 2) (Fin 2) ℤ) 0 1 : ℤ) : ZMod p) = 0
    norm_num
  mul_mem' {γ δ} hγ hδ := by
    change (((γ.val * δ.val) 0 1 : ℤ) : ZMod p) = 0
    simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]
    push_cast
    rw [hγ, hδ]
    ring
  inv_mem' {γ} hγ := by
    change (((γ.val⁻¹) 0 1 : ℤ) : ZMod p) = 0
    simpa [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two] using congrArg Neg.neg hγ

/-- Bezout's actual integral identity for a good prime and the level. -/
theorem heckePrime_bezout {p Q : ℕ} (hpQ : Nat.Coprime p Q) :
    (p : ℤ) * Int.gcdA p Q + (Q : ℤ) * Int.gcdB p Q = 1 := by
  simpa [Int.gcd_natCast_natCast, hpQ.gcd_eq_one] using
    (Int.gcd_eq_gcd_ab (p : ℤ) Q).symm

/-- The genuine missing representative with upper-left entry p and lower-left entry Q. -/
def heckeBezoutRepresentative (p Q : ℕ) (hpQ : Nat.Coprime p Q) : Gamma0 Q :=
  ⟨⟨!![(p : ℤ), -(Int.gcdB p Q); (Q : ℤ), Int.gcdA p Q], by
    have h := heckePrime_bezout hpQ
    simp only [Matrix.det_fin_two_of]
    linarith⟩, by rw [Gamma0_mem]; simp⟩

/-- The actual upper unipotent translation, as an integral Gamma0 matrix. -/
def heckeUpperTranslation (Q : ℕ) (x : ℤ) : Gamma0 Q :=
  ⟨⟨!![1, x; 0, 1], by simp [Matrix.det_fin_two]⟩, by rw [Gamma0_mem]; simp⟩

/-- The p translations and the actual Bezout representative. -/
def heckeUpperRepresentative (p Q : ℕ) (hpQ : Nat.Coprime p Q) : Option (ZMod p) → Gamma0 Q
  | some x => heckeUpperTranslation Q (x.val : ℤ)
  | none => heckeBezoutRepresentative p Q hpQ

/-- The actual left coset of the inverse representative, as required for domain tiling. -/
def heckeUpperCoset (p Q : ℕ) (hpQ : Nat.Coprime p Q) (x : Option (ZMod p)) :
    Gamma0 Q ⧸ heckeUpperSubgroup Q p := QuotientGroup.mk (heckeUpperRepresentative p Q hpQ x)⁻¹

/-- The Bezout upper-right entry does not vanish modulo the good prime. -/
theorem heckeBezout_upper_ne_zero {p Q : ℕ} (hp : Nat.Prime p) (hpQ : Nat.Coprime p Q) :
    ((-(Int.gcdB p Q) : ℤ) : ZMod p) ≠ 0 := by
  letI : Fact (Nat.Prime p) := ⟨hp⟩
  intro hz
  have hb := congrArg (Int.cast : ℤ → ZMod p) (heckePrime_bezout hpQ)
  push_cast at hb hz
  have hg : ((Int.gcdB p Q : ℤ) : ZMod p) = 0 := neg_eq_zero.mp hz
  simp [hg] at hb

/-- The explicit inverse representatives have distinct actual subgroup cosets. -/
theorem heckeUpperCoset_injective {p Q : ℕ} (hp : Nat.Prime p) (hpQ : Nat.Coprime p Q) :
    Function.Injective (heckeUpperCoset p Q hpQ) := by
  haveI : NeZero p := ⟨hp.ne_zero⟩
  intro x y he
  have hm := QuotientGroup.eq.mp he
  change ((heckeUpperRepresentative p Q hpQ x)⁻¹)⁻¹ *
    (heckeUpperRepresentative p Q hpQ y)⁻¹ ∈ heckeUpperSubgroup Q p at hm
  rw [inv_inv] at hm
  change (((((heckeUpperRepresentative p Q hpQ x).val) *
    ((heckeUpperRepresentative p Q hpQ y).val)⁻¹) 0 1 : ℤ) : ZMod p) = 0 at hm
  cases x with
  | none =>
    cases y with
    | none => rfl
    | some y =>
      exfalso
      apply heckeBezout_upper_ne_zero hp hpQ
      simpa [heckeUpperRepresentative, heckeBezoutRepresentative, heckeUpperTranslation,
        Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_inv,
        Matrix.adjugate_fin_two, Matrix.mul_apply, Fin.sum_univ_two] using hm
  | some x =>
    cases y with
    | none =>
      exfalso
      have hz : ((Int.gcdB p Q : ℤ) : ZMod p) = 0 := by
        simpa [heckeUpperRepresentative, heckeBezoutRepresentative, heckeUpperTranslation,
          Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_inv,
          Matrix.adjugate_fin_two, Matrix.mul_apply, Fin.sum_univ_two] using hm
      exact heckeBezout_upper_ne_zero hp hpQ (by simpa using congrArg Neg.neg hz)
    | some y =>
      congr 1
      have hsub : x - y = 0 := by
        simpa [heckeUpperRepresentative, heckeUpperTranslation, Matrix.SpecialLinearGroup.coe_mul,
          Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two,
          Matrix.mul_apply, Fin.sum_univ_two, sub_eq_add_neg, add_comm] using hm
      exact sub_eq_zero.mp hsub

/-- Every actual subgroup coset has one of the p+1 explicit inverse representatives. -/
theorem heckeUpperCoset_surjective {p Q : ℕ} (hp : Nat.Prime p) (hpQ : Nat.Coprime p Q) :
    Function.Surjective (heckeUpperCoset p Q hpQ) := by
  letI : Fact (Nat.Prime p) := ⟨hp⟩
  intro q
  induction q using Quotient.inductionOn with | h γ => ?_
  by_cases hd : ((γ.val 1 1 : ℤ) : ZMod p) = 0
  · refine ⟨none, QuotientGroup.eq.mpr ?_⟩
    change ((heckeUpperRepresentative p Q hpQ none)⁻¹)⁻¹ * γ ∈ heckeUpperSubgroup Q p
    rw [inv_inv]
    change (((((heckeUpperRepresentative p Q hpQ none).val) * γ.val) 0 1 : ℤ) : ZMod p) = 0
    simp [heckeUpperRepresentative, heckeBezoutRepresentative, Matrix.SpecialLinearGroup.coe_mul,
      Matrix.mul_apply, Fin.sum_univ_two, hd]
  · let x : ZMod p := -((γ.val 0 1 : ℤ) : ZMod p) / ((γ.val 1 1 : ℤ) : ZMod p)
    refine ⟨some x, QuotientGroup.eq.mpr ?_⟩
    change ((heckeUpperRepresentative p Q hpQ (some x))⁻¹)⁻¹ * γ ∈ heckeUpperSubgroup Q p
    rw [inv_inv]
    change (((((heckeUpperRepresentative p Q hpQ (some x)).val) * γ.val) 0 1 : ℤ) : ZMod p) = 0
    simp [heckeUpperRepresentative, heckeUpperTranslation, Matrix.SpecialLinearGroup.coe_mul,
      Matrix.mul_apply, Fin.sum_univ_two, x, hd]

/-- The exact finite transversal equivalence for the upper-congruence Hecke subgroup. -/
def heckeUpperCosetEquiv {p Q : ℕ} (hp : Nat.Prime p) (hpQ : Nat.Coprime p Q) :
    Option (ZMod p) ≃ Gamma0 Q ⧸ heckeUpperSubgroup Q p :=
  Equiv.ofBijective (heckeUpperCoset p Q hpQ)
    ⟨heckeUpperCoset_injective hp hpQ, heckeUpperCoset_surjective hp hpQ⟩

/-- Equality with an actual coset is precisely the representative membership condition. -/
theorem heckeUpperCoset_eq_iff {p Q : ℕ} (hpQ : Nat.Coprime p Q)
    (x : Option (ZMod p)) (γ : Gamma0 Q) :
    heckeUpperCoset p Q hpQ x = QuotientGroup.mk γ ↔
      heckeUpperRepresentative p Q hpQ x * γ ∈ heckeUpperSubgroup Q p := by
  unfold heckeUpperCoset
  rw [QuotientGroup.eq, inv_inv]

end
end Dubon2026
