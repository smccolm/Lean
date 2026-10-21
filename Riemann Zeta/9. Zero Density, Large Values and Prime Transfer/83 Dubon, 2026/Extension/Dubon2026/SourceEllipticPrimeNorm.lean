import Dubon2026.SourceSL2CocycleMatrices
import Mathlib.Data.Nat.Sqrt

/-! DUB-17/18 -> residual Galois association -> the detected finite-order
branch of original weight-two H1 -> Hecke eigenvalues ell+1.
Adapted from anthropics/fermats-last-theorem,
revision 6e837e75355538c7f80bab5b956861e86c4eacc2,
P2M/Sol/S_CohCarrier_heckeT_top_apply_eq_smul_of_isOfFinOrder.lean.txt
(Apache-2.0; retained LICENSE and NOTICE).
The local reuse search found no finite-order diagonal-Hecke conjugacy
calculation. Existing original integral conjugation and native H1 are reused.
-/
namespace Dubon2026.SourceFiniteOrder
noncomputable section
open Matrix Matrix.SpecialLinearGroup
open scoped MatrixGroups

/-- For the two nonzero small traces, the prime norm cannot be twice the prime under the root congruence. -/
theorem norm_ne_two_mul {t : ℤ} (ht : t = 1 ∨ t = -1) {ℓ : ℕ} (hℓ : ℓ.Prime) (x y a r : ℤ)
    (hr : a ^ 2 - t * a + 1 = ℓ * r) (hQ : x ^ 2 + t * x * y + y ^ 2 = ℓ * 2) : False := by
  have hpar : ∀ u v w : ZMod 2, u ^ 2 + w * u * v + v ^ 2 = 0 → w = 0 ∨ (u = 0 ∧ v = 0) := by
    decide
  have hroot : ∀ u w : ZMod 2, w ≠ 0 → u ^ 2 - w * u + 1 ≠ 0 := by decide
  have ht2 : ((t : ℤ) : ZMod 2) ≠ 0 := by
    rcases ht with rfl | rfl
    · rw [Int.cast_one]; decide
    · rw [Int.cast_neg, Int.cast_one]; decide
  have h20 : ((2 : ℤ) : ZMod 2) = 0 := by decide
  have hc := congrArg (fun z : ℤ => (z : ZMod 2)) hQ
  simp only [Int.cast_add, Int.cast_mul, Int.cast_pow, h20, mul_zero] at hc
  obtain h | ⟨hx0, hy0⟩ := hpar _ _ _ hc
  · exact ht2 h
  obtain ⟨x', rfl⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd x 2).mp hx0
  obtain ⟨y', rfl⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd y 2).mp hy0
  push_cast at hQ
  have hℓ2 : (ℓ : ℤ) = 2 * (x' ^ 2 + t * x' * y' + y' ^ 2) := by
    rcases ht with rfl | rfl <;> · ring_nf at hQ ⊢; linarith
  have h2dvd : (2 : ℕ) ∣ ℓ := Int.natCast_dvd_natCast.mp ⟨_, hℓ2⟩
  have hℓeq : ℓ = 2 := by
    rcases (Nat.dvd_prime hℓ).mp h2dvd with h | h
    · norm_num at h
    · exact h.symm
  subst hℓeq
  have hc' := congrArg (fun z : ℤ => (z : ZMod 2)) hr
  simp only [Int.cast_add, Int.cast_sub, Int.cast_mul, Int.cast_pow, Int.cast_one, Nat.cast_ofNat,
    h20, zero_mul] at hc'
  exact hroot _ _ ht2 hc'

/-- Each required small-trace integral quadratic norm is positive away from the zero vector. -/
theorem norm_pos {t : ℤ} (ht : t = 0 ∨ t = 1 ∨ t = -1) {x y : ℤ} (hne : x ≠ 0 ∨ y ≠ 0) :
    0 < x ^ 2 + t * x * y + y ^ 2 := by
  rcases hne with h | h
  · have h0 : 0 < x ^ 2 := by positivity
    rcases ht with rfl | rfl | rfl <;> nlinarith [sq_nonneg (x + y), sq_nonneg (x - y), sq_nonneg y]
  · have h0 : 0 < y ^ 2 := by positivity
    rcases ht with rfl | rfl | rfl <;> nlinarith [sq_nonneg (x + y), sq_nonneg (x - y), sq_nonneg x]

/-- The required quadratic norm is bounded by three times the coordinate bound squared. -/
theorem norm_le {t : ℤ} (ht : t = 0 ∨ t = 1 ∨ t = -1) {x y m : ℤ} (hxl : -m ≤ x) (hxu : x ≤ m)
    (hyl : -m ≤ y) (hyu : y ≤ m) : x ^ 2 + t * x * y + y ^ 2 ≤ 3 * m ^ 2 := by
  have hx2 : x ^ 2 ≤ m ^ 2 := by nlinarith
  have hy2 : y ^ 2 ≤ m ^ 2 := by nlinarith
  rcases ht with rfl | rfl | rfl <;> nlinarith [sq_nonneg (x + y), sq_nonneg (x - y)]

/-- A root congruence for the small-trace characteristic polynomial produces an exact integral norm representation of the prime. -/
theorem exists_norm_eq_prime {ℓ : ℕ} (hℓ : ℓ.Prime) (t a : ℤ) (ht : t.natAbs ≤ 1)
    (ha : (ℓ : ℤ) ∣ a ^ 2 - t * a + 1) :
    ∃ x y : ℤ, x ^ 2 + t * x * y + y ^ 2 = ℓ ∧ (ℓ : ℤ) ∣ x + a * y := by
  haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
  obtain ⟨r, hr⟩ := ha

  set m : ℕ := Nat.sqrt ℓ with hm
  have hm1 : m * m ≤ ℓ := Nat.sqrt_le ℓ
  have hm2 : ℓ < (m + 1) * (m + 1) := Nat.lt_succ_sqrt ℓ
  have hm3 : m * m < ℓ := by
    refine lt_of_le_of_ne hm1 fun h => ?_
    have hdvd : m ∣ ℓ := ⟨m, h.symm⟩
    rcases (Nat.dvd_prime hℓ).mp hdvd with h1 | h1
    · rw [h1] at h
      exact hℓ.one_lt.ne' (by simpa using h.symm)
    · rw [h1] at h
      have := hℓ.two_le
      nlinarith

  let f : Fin (m + 1) × Fin (m + 1) → ZMod ℓ :=
    fun p => (((p.1 : ℕ) : ℤ) + a * ((p.2 : ℕ) : ℤ) : ℤ)
  have hcard : Fintype.card (ZMod ℓ) < Fintype.card (Fin (m + 1) × Fin (m + 1)) := by
    rw [ZMod.card, Fintype.card_prod, Fintype.card_fin]
    exact hm2
  obtain ⟨p, q, hpq, hf⟩ := Fintype.exists_ne_map_eq_of_card_lt f hcard
  set x : ℤ := ((p.1 : ℕ) : ℤ) - ((q.1 : ℕ) : ℤ) with hx
  set y : ℤ := ((p.2 : ℕ) : ℤ) - ((q.2 : ℕ) : ℤ) with hy
  have hp1 := p.1.is_lt
  have hp2 := p.2.is_lt
  have hq1 := q.1.is_lt
  have hq2 := q.2.is_lt
  have hxl : -(m : ℤ) ≤ x := by omega
  have hxu : x ≤ m := by omega
  have hyl : -(m : ℤ) ≤ y := by omega
  have hyu : y ≤ m := by omega
  have hne : x ≠ 0 ∨ y ≠ 0 := by
    rcases eq_or_ne x 0 with hx0 | hx0
    · refine Or.inr fun hy0 => hpq ?_
      have h1 : (p.1 : ℕ) = q.1 := by omega
      have h2 : (p.2 : ℕ) = q.2 := by omega
      exact Prod.ext (Fin.ext h1) (Fin.ext h2)
    · exact Or.inl hx0
  have hdvd : (ℓ : ℤ) ∣ x + a * y := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    have : ((x + a * y : ℤ) : ZMod ℓ) = f p - f q := by
      simp only [f, hx, hy]
      push_cast
      ring
    rw [this, hf, sub_self]
  obtain ⟨s, hs⟩ := hdvd
  refine ⟨x, y, ?_, ⟨s, hs⟩⟩

  set k : ℤ := s * (ℓ * s - 2 * a * y + t * y) + y ^ 2 * r with hk
  have hQk : x ^ 2 + t * x * y + y ^ 2 = ℓ * k := by
    rw [hk]
    linear_combination (x + ℓ * s - a * y + t * y) * hs + y ^ 2 * hr

  have hx2 : x ^ 2 ≤ (m : ℤ) ^ 2 := by nlinarith only [hxl, hxu]
  have hy2 : y ^ 2 ≤ (m : ℤ) ^ 2 := by nlinarith only [hyl, hyu]
  have hm3' : (m : ℤ) ^ 2 < ℓ := by
    have : ((m * m : ℕ) : ℤ) < ℓ := by exact_mod_cast hm3
    push_cast at this
    nlinarith only [this]
  have hℓpos : (0 : ℤ) < ℓ := by exact_mod_cast hℓ.pos
  have ht3 : t = 0 ∨ t = 1 ∨ t = -1 := by omega
  have hQpos : 0 < x ^ 2 + t * x * y + y ^ 2 := norm_pos ht3 hne
  have hQle : x ^ 2 + t * x * y + y ^ 2 ≤ 3 * (m : ℤ) ^ 2 := norm_le ht3 hxl hxu hyl hyu
  clear_value x y k
  have hk1 : 0 < k := by
    by_contra h
    rw [not_lt] at h
    nlinarith only [hQpos, hQk, hℓpos, h]
  have hk3 : k < 3 := by
    by_contra h
    rw [not_lt] at h
    nlinarith only [hQle, hm3', hQk, hℓpos, h]
  have hk12 : k = 1 ∨ k = 2 := by omega
  rcases hk12 with h1 | h2
  · rw [hQk, h1, mul_one]
  · exfalso
    rw [h2] at hQk
    rcases ht3 with rfl | rfl | rfl
    ·
      nlinarith only [hQk, hx2, hy2, hm3']
    · exact norm_ne_two_mul (Or.inl rfl) hℓ x y a r hr hQk
    · exact norm_ne_two_mul (Or.inr rfl) hℓ x y a r hr hQk


end
end Dubon2026.SourceFiniteOrder
