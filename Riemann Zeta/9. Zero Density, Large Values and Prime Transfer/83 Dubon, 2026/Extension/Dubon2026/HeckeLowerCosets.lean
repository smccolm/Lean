import Dubon2026.HeckeUpperCosets

/-! # The genuine lower-congruence Hecke transversal -/

namespace Dubon2026

open Matrix.SpecialLinearGroup CongruenceSubgroup
open scoped MatrixGroups

noncomputable section

/-- The actual lower-left congruence subgroup inside Gamma0. -/
def heckeLowerSubgroup (Q p : ℕ) : Subgroup (Gamma0 Q) where
  carrier γ := ((γ.val 1 0 : ℤ) : ZMod p) = 0
  one_mem' := by
    change (((1 : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℤ) : ZMod p) = 0
    norm_num
  mul_mem' {γ δ} hγ hδ := by
    change (((γ.val * δ.val) 1 0 : ℤ) : ZMod p) = 0
    simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]
    push_cast
    rw [hγ, hδ]
    ring
  inv_mem' {γ} hγ := by
    change (((γ.val⁻¹) 1 0 : ℤ) : ZMod p) = 0
    simpa [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two] using congrArg Neg.neg hγ

/-- The genuine lower unipotent translation, retaining the level in its lower-left entry. -/
def heckeLowerTranslation (Q : ℕ) (x : ℤ) : Gamma0 Q :=
  ⟨⟨!![1, 0; (Q : ℤ) * x, 1], by simp [Matrix.det_fin_two]⟩,
    by rw [Gamma0_mem]; simp⟩

/-- The genuine complementary lower-coset representative. -/
def heckeLowerBezoutRepresentative (p Q : ℕ) (hpQ : Nat.Coprime p Q) : Gamma0 Q :=
  ⟨⟨!![Int.gcdA p Q, -(Int.gcdB p Q); (Q : ℤ), (p : ℤ)], by
    have h := heckePrime_bezout hpQ
    simp only [Matrix.det_fin_two_of]
    nlinarith⟩, by rw [Gamma0_mem]; simp⟩

/-- The p lower translations and their complementary actual Gamma0 representative. -/
def heckeLowerRepresentative (p Q : ℕ) (hpQ : Nat.Coprime p Q) : Option (ZMod p) → Gamma0 Q
  | some x => heckeLowerTranslation Q (x.val : ℤ)
  | none => heckeLowerBezoutRepresentative p Q hpQ

/-- The actual lower-congruence coset of the inverse representative. -/
def heckeLowerCoset (p Q : ℕ) (hpQ : Nat.Coprime p Q) (x : Option (ZMod p)) :
    Gamma0 Q ⧸ heckeLowerSubgroup Q p := QuotientGroup.mk (heckeLowerRepresentative p Q hpQ x)⁻¹

/-- The level is a nonzero residue at a good prime. -/
theorem heckePrime_level_ne_zero {p Q : ℕ} (hp : Nat.Prime p) (hpQ : Nat.Coprime p Q) :
    (Q : ZMod p) ≠ 0 := by
  letI : Fact (Nat.Prime p) := ⟨hp⟩
  exact ((ZMod.isUnit_iff_coprime Q p).mpr hpQ.symm).ne_zero

/-- The explicit inverse lower representatives occupy distinct genuine cosets. -/
theorem heckeLowerCoset_injective {p Q : ℕ} (hp : Nat.Prime p) (hpQ : Nat.Coprime p Q) :
    Function.Injective (heckeLowerCoset p Q hpQ) := by
  letI : Fact (Nat.Prime p) := ⟨hp⟩
  intro x y he
  have hm := QuotientGroup.eq.mp he
  change ((heckeLowerRepresentative p Q hpQ x)⁻¹)⁻¹ *
    (heckeLowerRepresentative p Q hpQ y)⁻¹ ∈ heckeLowerSubgroup Q p at hm
  rw [inv_inv] at hm
  change (((((heckeLowerRepresentative p Q hpQ x).val) *
    ((heckeLowerRepresentative p Q hpQ y).val)⁻¹) 1 0 : ℤ) : ZMod p) = 0 at hm
  cases x with
  | none =>
    cases y with
    | none => rfl
    | some y =>
      exfalso
      apply heckePrime_level_ne_zero hp hpQ
      simpa [heckeLowerRepresentative, heckeLowerBezoutRepresentative, heckeLowerTranslation,
        Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_inv,
        Matrix.adjugate_fin_two, Matrix.mul_apply, Fin.sum_univ_two] using hm
  | some x =>
    cases y with
    | none =>
      exfalso
      have hz : -(Q : ZMod p) = 0 := by
        simpa [heckeLowerRepresentative, heckeLowerBezoutRepresentative, heckeLowerTranslation,
          Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_inv,
          Matrix.adjugate_fin_two, Matrix.mul_apply, Fin.sum_univ_two] using hm
      exact heckePrime_level_ne_zero hp hpQ (neg_eq_zero.mp hz)
    | some y =>
      congr 1
      have hsub : (Q : ZMod p) * (x - y) = 0 := by
        convert hm using 1
        simp [heckeLowerRepresentative, heckeLowerTranslation, Matrix.SpecialLinearGroup.coe_mul,
          Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two,
          Matrix.mul_apply, Fin.sum_univ_two]
        ring
      exact sub_eq_zero.mp ((mul_eq_zero.mp hsub).resolve_left (heckePrime_level_ne_zero hp hpQ))

/-- The p+1 inverse lower representatives cover every actual subgroup coset. -/
theorem heckeLowerCoset_surjective {p Q : ℕ} (hp : Nat.Prime p) (hpQ : Nat.Coprime p Q) :
    Function.Surjective (heckeLowerCoset p Q hpQ) := by
  letI : Fact (Nat.Prime p) := ⟨hp⟩
  intro q
  induction q using Quotient.inductionOn with | h γ => ?_
  by_cases ha : ((γ.val 0 0 : ℤ) : ZMod p) = 0
  · refine ⟨none, QuotientGroup.eq.mpr ?_⟩
    change ((heckeLowerRepresentative p Q hpQ none)⁻¹)⁻¹ * γ ∈ heckeLowerSubgroup Q p
    rw [inv_inv]
    change (((((heckeLowerRepresentative p Q hpQ none).val) * γ.val) 1 0 : ℤ) : ZMod p) = 0
    simp [heckeLowerRepresentative, heckeLowerBezoutRepresentative, Matrix.SpecialLinearGroup.coe_mul,
      Matrix.mul_apply, Fin.sum_univ_two, ha]
  · let x : ZMod p := -((γ.val 1 0 : ℤ) : ZMod p) / ((Q : ZMod p) * ((γ.val 0 0 : ℤ) : ZMod p))
    refine ⟨some x, QuotientGroup.eq.mpr ?_⟩
    change ((heckeLowerRepresentative p Q hpQ (some x))⁻¹)⁻¹ * γ ∈ heckeLowerSubgroup Q p
    rw [inv_inv]
    change (((((heckeLowerRepresentative p Q hpQ (some x)).val) * γ.val) 1 0 : ℤ) : ZMod p) = 0
    simp [heckeLowerRepresentative, heckeLowerTranslation, Matrix.SpecialLinearGroup.coe_mul,
      Matrix.mul_apply, Fin.sum_univ_two, x]
    field_simp [ha, heckePrime_level_ne_zero hp hpQ]
    ring1

/-- The exact lower-congruence transversal equivalence. -/
def heckeLowerCosetEquiv {p Q : ℕ} (hp : Nat.Prime p) (hpQ : Nat.Coprime p Q) :
    Option (ZMod p) ≃ Gamma0 Q ⧸ heckeLowerSubgroup Q p :=
  Equiv.ofBijective (heckeLowerCoset p Q hpQ)
    ⟨heckeLowerCoset_injective hp hpQ, heckeLowerCoset_surjective hp hpQ⟩

/-- Equality with an actual coset is precisely the representative membership condition. -/
theorem heckeLowerCoset_eq_iff {p Q : ℕ} (hpQ : Nat.Coprime p Q)
    (x : Option (ZMod p)) (γ : Gamma0 Q) :
    heckeLowerCoset p Q hpQ x = QuotientGroup.mk γ ↔
      heckeLowerRepresentative p Q hpQ x * γ ∈ heckeLowerSubgroup Q p := by
  unfold heckeLowerCoset
  rw [QuotientGroup.eq, inv_inv]

end
end Dubon2026
