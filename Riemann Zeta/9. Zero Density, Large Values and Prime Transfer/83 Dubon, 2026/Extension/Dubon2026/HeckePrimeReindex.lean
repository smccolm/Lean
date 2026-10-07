/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanModularForms contributors

Selected finite reindexing and integral matrix calculations from HeckeT_p.lean
at LeanModularForms 7c41b9b1747d47298f76bdb51f07031087702198.
-/
import Dubon2026.HeckeTriangular

/-! # Finite Mobius permutations for the genuine prime Hecke representatives -/

namespace Dubon2026.HeckePrimeReindex

open Matrix Matrix.SpecialLinearGroup
open scoped MatrixGroups

noncomputable section

private lemma zmod_mul_inv {p : ℕ} [hp : Fact p.Prime] [NeZero p]
    {a : ZMod p} (ha : a ≠ 0) : a * a⁻¹ = 1 := by
  have vcz : ∀ x : ZMod p, (x.val : ZMod p) = x := fun x ↦ by rw [ZMod.natCast_val, ZMod.cast_id]
  conv_lhs => rw [show a = (a.val : ZMod p) from (vcz a).symm,
    show ((a.val : ZMod p))⁻¹ = (((a.val : ZMod p)⁻¹).val : ZMod p) from (vcz _).symm]
  exact ZMod.mul_val_inv (hp.out.coprime_iff_not_dvd.2 fun h ↦ ha (by
    rw [show a = (a.val : ZMod p) by rw [ZMod.natCast_val, ZMod.cast_id]]
    simp [Nat.eq_zero_of_dvd_of_lt h (ZMod.val_lt a)])).symm

/-- The actual finite Mobius reindexing, with the omitted projective value inserted at its pole. -/
noncomputable def moebiusFin (p : ℕ) (hp : Nat.Prime p)
    (M : Matrix (Fin 2) (Fin 2) ℤ) (b : Fin p) : Fin p :=
  haveI : NeZero p := ⟨hp.ne_zero⟩
  let A : ℤ := M 0 0 + ↑b.val * M 1 0
  let B : ℤ := M 0 1 + ↑b.val * M 1 1
  if (A : ZMod p) = 0 then
    ⟨((M 1 1 : ZMod p) * (M 1 0 : ZMod p)⁻¹).val, ZMod.val_lt _⟩
  else
    ⟨((B : ZMod p) * (A : ZMod p)⁻¹).val, ZMod.val_lt _⟩

private lemma intCast_zmod_eq_zero_of_mul (p : ℕ) (hp : Nat.Prime p) {a b : ℤ}
    (hab : ((a * b : ℤ) : ZMod p) = 0) (hb : ((b : ℤ) : ZMod p) ≠ 0) :
    ((a : ℤ) : ZMod p) = 0 := by
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at hab ⊢
  exact (Int.Prime.dvd_mul' hp hab).resolve_right fun h ↦
    hb ((ZMod.intCast_zmod_eq_zero_iff_dvd b p).mpr h)

private lemma fin_val_eq_of_intCast_sub_dvd {p : ℕ} (hp : Nat.Prime p) (x y : Fin p)
    (h : (p : ℤ) ∣ ((x.val : ℤ) - y.val)) : x.val = y.val := by
  obtain ⟨c, hc⟩ := h
  have hxp : (x.val : ℤ) < p := by exact_mod_cast x.prop
  have hyp : (y.val : ℤ) < p := by exact_mod_cast y.prop
  have hpp : (0 : ℤ) < p := by exact_mod_cast hp.pos
  have hc0 : c = 0 := by nlinarith
  subst hc0
  omega

private lemma zmod_mul_eq_of_mul_inv_eq {p : ℕ} [Fact p.Prime] [NeZero p]
    {a b c d : ZMod p} (hb : b ≠ 0) (hd : d ≠ 0)
    (h : a * b⁻¹ = c * d⁻¹) : a * d = c * b := by
  have inv_mul {x : ZMod p} (hx : x ≠ 0) : x⁻¹ * x = 1 := by
    rw [mul_comm]
    exact zmod_mul_inv hx
  have := congr_arg (· * (b * d)) h
  simp only [mul_assoc] at this
  rwa [show b⁻¹ * (b * d) = d by rw [← mul_assoc, inv_mul hb, one_mul],
       show d⁻¹ * (b * d) = b by
          rw [mul_comm b d, ← mul_assoc, inv_mul hd, one_mul]] at this

private lemma botLeft_ne_zero_of_topLeft_add_eq_zero {p : ℕ} [Fact p.Prime]
    (M : Matrix (Fin 2) (Fin 2) ℤ) (hdet : M 0 0 * M 1 1 - M 0 1 * M 1 0 = 1)
    (c : ℤ) (hAc : ((M 0 0 + c * M 1 0 : ℤ) : ZMod p) = 0) :
    ((M 1 0 : ℤ) : ZMod p) ≠ 0 := by
  intro h10
  have hdet_p : ((M 0 0 * M 1 1 - M 0 1 * M 1 0 : ℤ) : ZMod p) = 1 := by simp [hdet]
  have h00 : ((M 0 0 : ℤ) : ZMod p) = 0 := by
    have hsum := hAc
    push_cast at hsum
    rw [h10, mul_zero, add_zero] at hsum
    exact_mod_cast hsum
  push_cast at hdet_p
  rw [h00, h10] at hdet_p
  simp at hdet_p

private lemma false_of_topLeft_zero_and_nonzero {p : ℕ} [Fact p.Prime] [NeZero p]
    (M : Matrix (Fin 2) (Fin 2) ℤ) (hdet : M 0 0 * M 1 1 - M 0 1 * M 1 0 = 1)
    (c d : ℤ) (hAc : ((M 0 0 + c * M 1 0 : ℤ) : ZMod p) = 0)
    (hAd : ((M 0 0 + d * M 1 0 : ℤ) : ZMod p) ≠ 0)
    (heq : ((M 1 1 : ℤ) : ZMod p) * ((M 1 0 : ℤ) : ZMod p)⁻¹ =
      ((M 0 1 + d * M 1 1 : ℤ) : ZMod p) * ((M 0 0 + d * M 1 0 : ℤ) : ZMod p)⁻¹) :
    False := by
  have hdet_p : ((M 0 0 * M 1 1 - M 0 1 * M 1 0 : ℤ) : ZMod p) = 1 := by simp [hdet]
  have hdet_d : ((M 1 1 : ℤ) : ZMod p) * ((M 0 0 + d * M 1 0 : ℤ) : ZMod p) -
      ((M 1 0 : ℤ) : ZMod p) * ((M 0 1 + d * M 1 1 : ℤ) : ZMod p) = 1 := by
    push_cast at hdet_p ⊢
    linear_combination hdet_p
  exact one_ne_zero (hdet_d.symm.trans (by
    rw [zmod_mul_eq_of_mul_inv_eq (botLeft_ne_zero_of_topLeft_add_eq_zero M hdet c hAc) hAd heq]
    ring))

/-- A determinant-one matrix induces an injective finite reindexing. -/
lemma moebiusFin_injective (p : ℕ) (hp : Nat.Prime p)
    (M : Matrix (Fin 2) (Fin 2) ℤ) (hdet : M.det = 1) :
    Function.Injective (moebiusFin p hp M) := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : NeZero p := ⟨hp.ne_zero⟩
  have hdet_eq : M 0 0 * M 1 1 - M 0 1 * M 1 0 = 1 := by rwa [det_fin_two] at hdet
  have hdet_p : ((M 0 0 * M 1 1 - M 0 1 * M 1 0 : ℤ) : ZMod p) = 1 := by simp [hdet_eq]
  intro b₁ b₂ heq
  have hv : (moebiusFin p hp M b₁).val = (moebiusFin p hp M b₂).val :=
    congr_arg Fin.val heq
  simp only [moebiusFin] at hv
  set A₁ : ZMod p := ((M 0 0 + ↑b₁.val * M 1 0 : ℤ) : ZMod p) with hA₁_def
  set A₂ : ZMod p := ((M 0 0 + ↑b₂.val * M 1 0 : ℤ) : ZMod p) with hA₂_def
  set B₁ : ZMod p := ((M 0 1 + ↑b₁.val * M 1 1 : ℤ) : ZMod p) with hB₁_def
  set B₂ : ZMod p := ((M 0 1 + ↑b₂.val * M 1 1 : ℤ) : ZMod p) with hB₂_def
  suffices hsuff : b₁.val = b₂.val by
    ext
    exact hsuff
  by_cases hA₁ : A₁ = 0 <;> by_cases hA₂ : A₂ = 0
  · have h_ring : A₁ - A₂ =
        ((↑b₁.val - ↑b₂.val : ℤ) : ZMod p) * ((M 1 0 : ℤ) : ZMod p) := by
      simp only [hA₁_def, hA₂_def]
      push_cast
      ring
    rw [hA₁, hA₂, sub_self] at h_ring
    have hb_zero : ((↑b₁.val - ↑b₂.val : ℤ) : ZMod p) = 0 := by
      have h := h_ring.symm
      rw [← Int.cast_mul] at h
      exact intCast_zmod_eq_zero_of_mul p hp h
        (botLeft_ne_zero_of_topLeft_add_eq_zero M hdet_eq _ hA₁)
    exact fin_val_eq_of_intCast_sub_dvd hp b₁ b₂
      ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hb_zero)
  · rw [if_pos hA₁, if_neg hA₂] at hv
    exact (false_of_topLeft_zero_and_nonzero M hdet_eq _ _ hA₁ hA₂
      (ZMod.val_injective p hv)).elim
  · rw [if_neg hA₁, if_pos hA₂] at hv
    exact (false_of_topLeft_zero_and_nonzero M hdet_eq _ _ hA₂ hA₁
      (ZMod.val_injective p hv).symm).elim
  · rw [if_neg hA₁, if_neg hA₂] at hv
    have h_cross_det : B₁ * A₂ - B₂ * A₁ =
        ((↑b₁.val - ↑b₂.val : ℤ) : ZMod p) *
        ((M 0 0 * M 1 1 - M 0 1 * M 1 0 : ℤ) : ZMod p) := by
      simp only [hA₁_def, hA₂_def, hB₁_def, hB₂_def]
      push_cast
      ring
    have h0 : B₁ * A₂ - B₂ * A₁ = 0 := by
      rw [zmod_mul_eq_of_mul_inv_eq hA₁ hA₂ (ZMod.val_injective p hv)]
      ring
    rw [h0, hdet_p, mul_one] at h_cross_det
    exact fin_val_eq_of_intCast_sub_dvd hp b₁ b₂
      ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp h_cross_det.symm)

/-- The literal two-by-two determinant identity for an integral special linear matrix. -/
lemma sl2z_fin_two_det_eq_one (σ : SL(2, ℤ)) :
    (σ : Matrix (Fin 2) (Fin 2) ℤ) 0 0 * (σ : Matrix (Fin 2) (Fin 2) ℤ) 1 1 -
      (σ : Matrix (Fin 2) (Fin 2) ℤ) 0 1 * (σ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 = 1 := by
  simpa only [Matrix.det_fin_two] using σ.prop

/-- A zero lower-left entry modulo p forces every upper-translate denominator to be nonzero. -/
lemma not_dvd_topLeft_add_of_dvd_botLeft (p : ℕ) (hp : Nat.Prime p)
    (M : Matrix (Fin 2) (Fin 2) ℤ) (hdet : M 0 0 * M 1 1 - M 0 1 * M 1 0 = 1)
    (h10 : (p : ℤ) ∣ M 1 0) (b : ℤ) : ¬(p : ℤ) ∣ (M 0 0 + b * M 1 0) := by
  haveI : Fact p.Prime := ⟨hp⟩
  intro hdvd
  have h10' : ((M 1 0 : ℤ) : ZMod p) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr h10
  have h00 : ((M 0 0 : ℤ) : ZMod p) = 0 := by
    have := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hdvd
    push_cast at this
    rwa [h10', mul_zero, add_zero] at this
  have hd : ((M 0 0 * M 1 1 - M 0 1 * M 1 0 : ℤ) : ZMod p) = 1 := by simp [hdet]
  push_cast at hd
  rw [h00, h10', zero_mul, mul_zero, sub_zero] at hd
  exact zero_ne_one hd

/-- When the lower-left entry is nonzero, the canonical finite index is the unique pole. -/
lemma dvd_topLeft_add_canonicalIndex (p : ℕ) (hp : Nat.Prime p)
    (M : Matrix (Fin 2) (Fin 2) ℤ) (h10_ne : ((M 1 0 : ℤ) : ZMod p) ≠ 0) :
    (p : ℤ) ∣ (M 0 0 +
      ↑((-(M 0 0 : ZMod p) * ((M 1 0 : ℤ) : ZMod p)⁻¹).val) * M 1 0) := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : NeZero p := ⟨hp.ne_zero⟩
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  push_cast
  rw [ZMod.natCast_val, ZMod.cast_id]
  have : (-(M 0 0 : ZMod p) * ((M 1 0 : ℤ) : ZMod p)⁻¹) * ((M 1 0 : ℤ) : ZMod p) =
      -(M 0 0 : ZMod p) := by
    rw [mul_assoc, mul_comm ((M 1 0 : ℤ) : ZMod p)⁻¹ _, zmod_mul_inv h10_ne, mul_one]
  rw [this, add_neg_cancel]

/-- Replacing one reindexed value by the projective term preserves the full finite sum. -/
lemma sum_ite_swap_eq {p : ℕ} {V : Type*} [AddCommGroup V]
    (g : Fin p → V) (lower' : V) (φ : Fin p → Fin p) (hφ : Function.Bijective φ)
    (b₀ : Fin p) (P : Fin p → Prop) [DecidablePred P]
    (hP : ∀ i, P i ↔ i = b₀) :
    (∑ x, if P x then lower' else g (φ x)) + g (φ b₀) = (∑ x, g x) + lower' := by
  have h_ite_eq : ∀ i : Fin p,
      (if P i then lower' else g (φ i)) =
      g (φ i) + if i = b₀ then lower' - g (φ b₀) else 0 := by
    intro i
    simp only [hP]
    split_ifs with h1
    · subst h1
      abel
    · rw [add_zero]
  simp_rw [h_ite_eq, Finset.sum_add_distrib]
  rw [Finset.sum_ite_eq' Finset.univ b₀ (fun _ ↦ lower' - g (φ b₀)),
      if_pos (Finset.mem_univ _)]
  have h_bij_sum : ∑ x : Fin p, g (φ x) = ∑ x, g x :=
    Finset.sum_equiv (Equiv.ofBijective _ hφ)
      (fun _ ↦ ⟨fun _ ↦ Finset.mem_univ _, fun _ ↦ Finset.mem_univ _⟩)
      (fun _ _ ↦ rfl)
  rw [h_bij_sum]
  abel

/-- The exceptional divisibility condition singles out exactly the canonical index. -/
lemma dvd_topLeft_add_iff_eq_canonicalIndex (p : ℕ) (hp : Nat.Prime p)
    (M : Matrix (Fin 2) (Fin 2) ℤ) (hdet : M.det = 1) (b₀ : Fin p)
    (hb₀ : (p : ℤ) ∣ (M 0 0 + ↑b₀.val * M 1 0)) (i : Fin p) :
    (p : ℤ) ∣ (M 0 0 + ↑i.val * M 1 0) ↔ i = b₀ := by
  refine ⟨fun hdvd ↦ moebiusFin_injective p hp M hdet ?_, fun h ↦ h ▸ hb₀⟩
  simp only [moebiusFin,
    show ((M 0 0 + ↑i.val * M 1 0 : ℤ) : ZMod p) = 0 from
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hdvd,
    show ((M 0 0 + ↑b₀.val * M 1 0 : ℤ) : ZMod p) = 0 from
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hb₀, ↓reduceIte]

/-- The residue quotient gives an exact divisible integer remainder. -/
lemma dvd_sub_mul_inv_val {p : ℕ} [Fact p.Prime] [NeZero p]
    (num den : ℤ) (hden : (den : ZMod p) ≠ 0) :
    (p : ℤ) ∣ (num - den * ↑((num : ZMod p) * (den : ZMod p)⁻¹).val) := by
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  push_cast
  rw [ZMod.natCast_val, ZMod.cast_id, sub_eq_zero, mul_comm (num : ZMod p) _, ← mul_assoc,
    zmod_mul_inv hden, one_mul]

/-- The upper-to-upper integral transition matrix has determinant one. -/
lemma upper_tau_det_eq_one {M : Matrix (Fin 2) (Fin 2) ℤ}
    (hdet : M 0 0 * M 1 1 - M 0 1 * M 1 0 = 1) (p : ℕ) (b j' q : ℤ)
    (hq : (M 0 1 + b * M 1 1) - (M 0 0 + b * M 1 0) * j' = ↑p * q) :
    (!![M 0 0 + b * M 1 0, q; ↑p * M 1 0, M 1 1 - M 1 0 * j'] :
      Matrix (Fin 2) (Fin 2) ℤ).det = 1 := by
  rw [det_fin_two_of]
  linear_combination M 1 0 * hq + hdet

/-- The upper-to-diagonal integral transition matrix has determinant one. -/
lemma upper_div_tau_det_eq_one {M : Matrix (Fin 2) (Fin 2) ℤ}
    (hdet : M 0 0 * M 1 1 - M 0 1 * M 1 0 = 1) (p : ℕ) (a b : ℤ)
    (ha : M 0 0 + b * M 1 0 = a * ↑p) :
    (!![a, M 0 1 + b * M 1 1; M 1 0, ↑p * M 1 1] : Matrix (Fin 2) (Fin 2) ℤ).det = 1 := by
  rw [det_fin_two_of]
  linear_combination -M 1 1 * ha + hdet

/-- The diagonal-to-upper integral transition matrix has determinant one. -/
lemma lower_tau_det_eq_one {M : Matrix (Fin 2) (Fin 2) ℤ}
    (hdet : M 0 0 * M 1 1 - M 0 1 * M 1 0 = 1) (p : ℕ) (j' q : ℤ)
    (hq : M 1 1 - M 1 0 * j' = ↑p * q) :
    (!![↑p * M 0 0, M 0 1 - M 0 0 * j'; M 1 0, q] : Matrix (Fin 2) (Fin 2) ℤ).det = 1 := by
  rw [det_fin_two_of]
  linear_combination -M 0 0 * hq + hdet

/-- The diagonal-to-diagonal integral transition matrix has determinant one. -/
lemma lower_div_tau_det_eq_one {M : Matrix (Fin 2) (Fin 2) ℤ}
    (hdet : M 0 0 * M 1 1 - M 0 1 * M 1 0 = 1) (p : ℕ) (c : ℤ)
    (hc : M 1 0 = ↑p * c) :
    (!![M 0 0, ↑p * M 0 1; c, M 1 1] : Matrix (Fin 2) (Fin 2) ℤ).det = 1 := by
  rw [det_fin_two_of]
  linear_combination M 0 1 * hc + hdet


end
end Dubon2026.HeckePrimeReindex
