import Dubon2026.PrimitiveSatakeParameters
import Mathlib.Algebra.Ring.GeomSum

/-! # Exact local symmetric-power traces of the actual Hecke roots -/

namespace Dubon2026

open Polynomial

noncomputable section

/-- The complete homogeneous degree-r trace of two actual local roots. -/
def satakeSymmetricTrace (α β : ℂ) (r : ℕ) : ℂ :=
  ∑ i ∈ Finset.range (r + 1), α ^ i * β ^ (r - i)

/-- The exact first-order finite-sum identity, including repeated local roots. -/
theorem satakeSymmetricTrace_succ (α β : ℂ) (r : ℕ) :
    satakeSymmetricTrace α β (r + 1) = α * satakeSymmetricTrace α β r + β ^ (r + 1) := by
  unfold satakeSymmetricTrace
  rw [Finset.sum_range_succ']
  simp only [pow_zero, Nat.sub_zero, one_mul, Nat.add_sub_add_right, pow_succ']
  rw [Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- The actual finite trace satisfies the determinant-weighted second-order recurrence. -/
theorem satakeSymmetricTrace_recurrence (α β : ℂ) (r : ℕ) :
    satakeSymmetricTrace α β (r + 2) =
      (α + β) * satakeSymmetricTrace α β (r + 1) - α * β * satakeSymmetricTrace α β r := by
  have h1 := satakeSymmetricTrace_succ α β r
  have h2 := satakeSymmetricTrace_succ α β (r + 1)
  rw [pow_succ] at h2
  linear_combination h2 - β * h1

/-- Determinant-one local roots have exactly the rescaled Chebyshev character trace. -/
theorem satakeSymmetricTrace_chebyshev {α β : ℂ} (hprod : α * β = 1) (r : ℕ) :
    satakeSymmetricTrace α β r = (Chebyshev.S ℂ (r : ℤ)).eval (α + β) := by
  induction r using Nat.twoStepInduction with
  | zero => simp [satakeSymmetricTrace]
  | one => simp [satakeSymmetricTrace, Finset.sum_range_succ, add_comm]
  | more r ih0 ih1 =>
    rw [satakeSymmetricTrace_recurrence, hprod, one_mul, ih0, ih1]
    simp only [Nat.cast_add, Nat.cast_one, Nat.cast_ofNat, Chebyshev.S_add_two,
      eval_sub, eval_mul, eval_X]

/-- The true primitive prime-power coefficient equals the complete finite trace of its own constructed roots. -/
theorem primitive_primePower_eq_satakeTrace {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : PrimitiveCuspForm Q k) {p : ℕ} (hp : Nat.Prime p) (hpQ : ¬p ∣ Q) (r : ℕ) :
    normalizedCuspCoefficients f.toCuspForm (p ^ r) =
      satakeSymmetricTrace (primitiveSatakePlus f p) (primitiveSatakeMinus f p) r := by
  rw [satakeSymmetricTrace_chebyshev (primitiveSatake_trace_det f p).2,
    (primitiveSatake_trace_det f p).1]
  exact primitiveCuspForm_normalized_primePower_chebyshev f hp hpQ r

/-- Unit local roots bound every actual symmetric-power trace by its precise dimension. -/
theorem norm_satakeSymmetricTrace_le {α β : ℂ} (hα : ‖α‖ = 1) (hβ : ‖β‖ = 1) (r : ℕ) :
    ‖satakeSymmetricTrace α β r‖ ≤ (r : ℝ) + 1 := by
  unfold satakeSymmetricTrace
  calc
    _ ≤ ∑ i ∈ Finset.range (r + 1), ‖α ^ i * β ^ (r - i)‖ := norm_sum_le _ _
    _ = _ := by simp only [norm_mul, norm_pow, hα, hβ, one_pow, mul_one,
      Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one, Nat.cast_add, Nat.cast_one]

/-- The precise prime-power Ramanujan bound follows for the genuine coefficients from the explicit prime bound. -/
theorem primitive_primePower_norm_le_of_prime_bound {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : PrimitiveCuspForm Q k) {p : ℕ} (hp : Nat.Prime p) (hpQ : ¬p ∣ Q)
    (hb : ‖normalizedCuspCoefficients f.toCuspForm p‖ ≤ 2) (r : ℕ) :
    ‖normalizedCuspCoefficients f.toCuspForm (p ^ r)‖ ≤ (r : ℝ) + 1 := by
  obtain ⟨hα,hβ⟩ := (primitiveSatake_unit_iff_bound f hp hpQ).mpr hb
  rw [primitive_primePower_eq_satakeTrace f hp hpQ]
  exact norm_satakeSymmetricTrace_le hα hβ r

end
end Dubon2026
