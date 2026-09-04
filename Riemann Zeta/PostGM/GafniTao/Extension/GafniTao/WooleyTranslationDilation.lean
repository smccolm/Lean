import GafniTao.WooleyPadicToCritical

/-!
# Exact translation--dilation algebra for the Vinogradov system

This file supplies the monomial specialization of Wooley Section 4.  We keep
the variables integral and prove the full binomial expansion before extracting
the divisibility left after a common translation and prime-power dilation.
-/

open Finset
open scoped BigOperators

namespace GafniTao

noncomputable section

def wooleyPowerSum {s : ℕ} (x : Fin s → ℤ) (j : ℕ) : ℤ :=
  ∑ i, x i ^ j

theorem wooleyPowerSum_affine
    {s : ℕ} (x : Fin s → ℤ) (q c : ℤ) (j : ℕ) :
    wooleyPowerSum (fun i ↦ q * x i + c) j =
      ∑ m ∈ range (j + 1),
        (j.choose m : ℤ) * q ^ m * c ^ (j - m) * wooleyPowerSum x m := by
  simp only [wooleyPowerSum, add_pow]
  rw [sum_comm]
  apply sum_congr rfl
  intro m hm
  calc
    (∑ i, (q * x i) ^ m * c ^ (j - m) * (j.choose m : ℤ)) =
        ∑ i, (j.choose m : ℤ) * q ^ m * c ^ (j - m) * x i ^ m := by
      apply sum_congr rfl
      intro i hi
      rw [mul_pow]
      ring
    _ = (j.choose m : ℤ) * q ^ m * c ^ (j - m) *
        ∑ i, x i ^ m := by rw [mul_sum]

theorem wooleyPowerSum_affine_sub
    {s : ℕ} (x y : Fin s → ℤ) (q c : ℤ) (j : ℕ) :
    wooleyPowerSum (fun i ↦ q * x i + c) j -
        wooleyPowerSum (fun i ↦ q * y i + c) j =
      ∑ m ∈ range (j + 1),
        (j.choose m : ℤ) * q ^ m * c ^ (j - m) *
          (wooleyPowerSum x m - wooleyPowerSum y m) := by
  rw [wooleyPowerSum_affine, wooleyPowerSum_affine]
  rw [← sum_sub_distrib]
  apply sum_congr rfl
  intro m hm
  rw [← mul_sub]

/-- Divisibility form of the triangular binomial inversion.  If every affine
power-sum difference through degree `j` is divisible by `M`, and the lower
unscaled differences already have the expected divisibility, then the top
term `q^j * D_j` is divisible by `M`. -/
theorem dvd_top_powerSum_term_of_affine
    {s j : ℕ} (x y : Fin s → ℤ) (q c M : ℤ)
    (haffine : ∀ d, d ≤ j →
      M ∣ wooleyPowerSum (fun i ↦ q * x i + c) d -
        wooleyPowerSum (fun i ↦ q * y i + c) d)
    (hlower : ∀ d, d < j →
      M ∣ q ^ d * (wooleyPowerSum x d - wooleyPowerSum y d)) :
    M ∣ q ^ j * (wooleyPowerSum x j - wooleyPowerSum y j) := by
  have hall := haffine j le_rfl
  rw [wooleyPowerSum_affine_sub] at hall
  have hsplit :
      (∑ m ∈ range (j + 1),
          (j.choose m : ℤ) * q ^ m * c ^ (j - m) *
            (wooleyPowerSum x m - wooleyPowerSum y m)) =
        q ^ j * (wooleyPowerSum x j - wooleyPowerSum y j) +
          ∑ m ∈ range j,
            (j.choose m : ℤ) * q ^ m * c ^ (j - m) *
              (wooleyPowerSum x m - wooleyPowerSum y m) := by
    rw [Finset.sum_range_succ]
    simp only [Nat.choose_self, Nat.cast_one, one_mul, Nat.sub_self, pow_zero,
      mul_one]
    ac_rfl
  rw [hsplit] at hall
  have hrest : M ∣
      ∑ m ∈ range j,
        (j.choose m : ℤ) * q ^ m * c ^ (j - m) *
          (wooleyPowerSum x m - wooleyPowerSum y m) := by
    apply dvd_sum
    intro m hm
    have hmj : m < j := mem_range.mp hm
    have hd := hlower m hmj
    simpa [mul_assoc, mul_left_comm, mul_comm] using
      hd.mul_left ((j.choose m : ℤ) * c ^ (j - m))
  exact (dvd_add_left hrest).mp hall

theorem pow_mul_dvd_pow_of_le
    {p a j B : ℕ} (h : j * a ≤ B) :
    (p : ℤ) ^ (j * a) ∣ (p : ℤ) ^ B := by
  exact pow_dvd_pow (p : ℤ) h

/-- Cancelling a visible prime-power factor in an integer divisibility
relation.  No coprimality is needed because this is cancellation in the
integral domain `ℤ`, not cancellation modulo a composite modulus. -/
theorem pow_dvd_of_mul_pow_dvd
    {p a j B : ℕ} (hp : p ≠ 0) (hja : j * a ≤ B) {z : ℤ}
    (h : (p : ℤ) ^ B ∣ (p : ℤ) ^ (j * a) * z) :
    (p : ℤ) ^ (B - j * a) ∣ z := by
  obtain ⟨w, hw⟩ := h
  have hpow : (p : ℤ) ^ B =
      (p : ℤ) ^ (j * a) * (p : ℤ) ^ (B - j * a) := by
    rw [← pow_add, Nat.add_sub_of_le hja]
  rw [hpow] at hw
  have hpz : ((p : ℤ) ^ (j * a)) ≠ 0 :=
    pow_ne_zero _ (by exact_mod_cast hp)
  have hz : z = (p : ℤ) ^ (B - j * a) * w := by
    apply mul_left_cancel₀ hpz
    simpa [mul_assoc] using hw
  exact ⟨w, hz⟩

/-- Exact monomial translation--dilation consequence.  The hypotheses are
the source congruences after writing each original variable as `p^a*u+c`.
For every degree whose visible factor fits in the modulus, the unscaled
power sums are congruent modulo `p^(B-j*a)`. -/
theorem wooley_translation_dilation
    {s k p a B : ℕ} (x y : Fin s → ℤ) (c : ℤ)
    (hp : p ≠ 0)
    (hcong : ∀ d, 1 ≤ d → d ≤ k →
      Int.ModEq ((p : ℤ) ^ B)
        (wooleyPowerSum (fun i ↦ (p : ℤ) ^ a * x i + c) d)
        (wooleyPowerSum (fun i ↦ (p : ℤ) ^ a * y i + c) d)) :
    ∀ j, 1 ≤ j → j ≤ k → j * a ≤ B →
      Int.ModEq ((p : ℤ) ^ (B - j * a))
        (wooleyPowerSum x j) (wooleyPowerSum y j) := by
  intro j hj hje hja
  have htri : ∀ d, 1 ≤ d → d ≤ k →
      (p : ℤ) ^ B ∣
        ((p : ℤ) ^ a) ^ d *
          (wooleyPowerSum x d - wooleyPowerSum y d) := by
    intro d
    induction d using Nat.strong_induction_on with
    | h d ih =>
        intro hd hdk
        have haffine : ∀ e, e ≤ d →
            (p : ℤ) ^ B ∣
              wooleyPowerSum (fun i ↦ (p : ℤ) ^ a * x i + c) e -
                wooleyPowerSum (fun i ↦ (p : ℤ) ^ a * y i + c) e := by
          intro e hed
          by_cases he : e = 0
          · subst e
            simp [wooleyPowerSum]
          · exact (hcong e (by omega) (hed.trans hdk)).symm.dvd
        apply dvd_top_powerSum_term_of_affine x y ((p : ℤ) ^ a) c
          ((p : ℤ) ^ B) haffine
        intro e hed
        by_cases he : e = 0
        · subst e
          simp [wooleyPowerSum]
        · exact ih e hed (by omega) (hed.le.trans hdk)
  have htop := htri j hj hje
  rw [← pow_mul, Nat.mul_comm a j] at htop
  have hdiv := pow_dvd_of_mul_pow_dvd hp hja htop
  exact Int.modEq_iff_dvd.mpr (by
    simpa only [neg_sub] using (dvd_neg.mpr hdiv))

#print axioms wooleyPowerSum_affine
#print axioms dvd_top_powerSum_term_of_affine
#print axioms pow_dvd_of_mul_pow_dvd
#print axioms wooley_translation_dilation

end

end GafniTao
