import Dubon2026.SatakeSymmetricTrace
import Dubon2026.RankinSpectralTraces

/-! # Exact tensor decomposition of determinant-one local roots -/

namespace Dubon2026

noncomputable section

/-- A real determinant-one trace makes every symmetric character real. -/
theorem satakeSymmetricTrace_im_zero {α β : ℂ} (hp : α * β = 1)
    (hr : (α + β).im = 0) (r : ℕ) : (satakeSymmetricTrace α β r).im = 0 := by
  induction r using Nat.twoStepInduction with
  | zero => simp [satakeSymmetricTrace]
  | one => simpa [satakeSymmetricTrace, Finset.sum_range_succ, add_comm] using hr
  | more r ih0 ih1 =>
    rw [satakeSymmetricTrace_recurrence, hp, one_mul, Complex.sub_im,
      Complex.mul_im, hr, ih0, ih1]
    ring

/-- Taking powers of the genuine symmetric roots gives the symmetric trace of the powered roots. -/
theorem satakeSymmetricTrace_power_sum (α β : ℂ) (r m : ℕ) :
    (∑ i ∈ Finset.range (r + 1), (α ^ i * β ^ (r - i)) ^ m) =
      satakeSymmetricTrace (α ^ m) (β ^ m) r := by
  unfold satakeSymmetricTrace
  apply Finset.sum_congr rfl
  intro i _
  simp only [mul_pow, ← pow_mul]
  rw [Nat.mul_comm i m, Nat.mul_comm (r - i) m]

/-- Removing the first row and last column of the tensor square leaves the previous tensor square
and exactly the next even symmetric power. This identity also covers repeated roots. -/
theorem satake_tensor_product_step {M : Type*} [CommMonoid M]
    {α β : ℂ} (hp : α * β = 1) (g : ℂ → M) (r : ℕ) :
    (∏ i ∈ Finset.range (r + 2), ∏ j ∈ Finset.range (r + 2),
      g ((α ^ i * β ^ (r + 1 - i)) * (α ^ j * β ^ (r + 1 - j)))) =
    (∏ i ∈ Finset.range (r + 1), ∏ j ∈ Finset.range (r + 1),
      g ((α ^ i * β ^ (r - i)) * (α ^ j * β ^ (r - j)))) *
    ∏ i ∈ Finset.range (2 * (r + 1) + 1), g (α ^ i * β ^ (2 * (r + 1) - i)) := by
  have hinter (i j : ℕ) (hj : j < r + 1) :
      (α ^ (i + 1) * β ^ (r + 1 - (i + 1))) *
        (α ^ j * β ^ (r + 1 - j)) =
      (α ^ i * β ^ (r - i)) * (α ^ j * β ^ (r - j)) := by
    rw [Nat.add_sub_add_right, show r + 1 - j = (r - j) + 1 by omega,
      pow_succ, pow_succ]
    calc
      _ = (α * β) * ((α ^ i * β ^ (r - i)) * (α ^ j * β ^ (r - j))) := by ring
      _ = _ := by rw [hp, one_mul]
  have hrow (j : ℕ) (hj : j < r + 2) :
      (α ^ 0 * β ^ (r + 1 - 0)) * (α ^ j * β ^ (r + 1 - j)) =
        α ^ j * β ^ (2 * (r + 1) - j) := by
    simp only [pow_zero, Nat.sub_zero, one_mul]
    rw [mul_left_comm, ← pow_add, show r + 1 + (r + 1 - j) = 2 * (r + 1) - j by omega]
  have hcol (i : ℕ) (hi : i < r + 1) :
      (α ^ (i + 1) * β ^ (r + 1 - (i + 1))) *
        (α ^ (r + 1) * β ^ (r + 1 - (r + 1))) =
        α ^ ((r + 2) + i) * β ^ (2 * (r + 1) - ((r + 2) + i)) := by
    simp only [Nat.sub_self, pow_zero, mul_one, Nat.add_sub_add_right]
    rw [mul_right_comm, ← pow_add]
    rw [show i + 1 + (r + 1) = r + 2 + i by omega,
      show 2 * (r + 1) - (r + 2 + i) = r - i by omega]
  rw [Finset.prod_range_succ']
  simp_rw [Finset.prod_range_succ (n := r + 1)]
  rw [Finset.prod_mul_distrib]
  have hinner :
      (∏ i ∈ Finset.range (r + 1), ∏ j ∈ Finset.range (r + 1),
        g ((α ^ (i + 1) * β ^ (r + 1 - (i + 1))) * (α ^ j * β ^ (r + 1 - j)))) =
      ∏ i ∈ Finset.range (r + 1), ∏ j ∈ Finset.range (r + 1),
        g ((α ^ i * β ^ (r - i)) * (α ^ j * β ^ (r - j))) := by
    apply Finset.prod_congr rfl
    intro i _
    apply Finset.prod_congr rfl
    intro j hj
    rw [hinter i j (Finset.mem_range.mp hj)]
  rw [hinner]
  have hlast :
      (∏ i ∈ Finset.range (r + 1), g ((α ^ (i + 1) * β ^ (r + 1 - (i + 1))) *
        (α ^ (r + 1) * β ^ (r + 1 - (r + 1))))) =
      ∏ i ∈ Finset.range (r + 1), g (α ^ ((r + 2) + i) * β ^ (2 * (r + 1) - ((r + 2) + i))) := by
    apply Finset.prod_congr rfl
    intro i hi
    rw [hcol i (Finset.mem_range.mp hi)]
  rw [hlast]
  have hfirst :
      (∏ j ∈ Finset.range (r + 1), g ((α ^ 0 * β ^ (r + 1 - 0)) *
        (α ^ j * β ^ (r + 1 - j)))) *
        g ((α ^ 0 * β ^ (r + 1 - 0)) * (α ^ (r + 1) * β ^ (r + 1 - (r + 1)))) =
      ∏ j ∈ Finset.range (r + 2), g (α ^ j * β ^ (2 * (r + 1) - j)) := by
    rw [← Finset.prod_range_succ]
    apply Finset.prod_congr rfl
    intro j hj
    rw [hrow j (Finset.mem_range.mp hj)]
  rw [hfirst]
  rw [show 2 * (r + 1) + 1 = (r + 2) + (r + 1) by omega,
    Finset.prod_range_add (fun i => g (α ^ i * β ^ (2 * (r + 1) - i))) (r + 2) (r + 1)]
  ac_rfl

/-- The actual tensor-square Euler multiset is the sum of the even symmetric-power multisets. -/
theorem satake_tensor_product_decomposition {M : Type*} [CommMonoid M]
    {α β : ℂ} (hp : α * β = 1) (g : ℂ → M) (r : ℕ) :
    (∏ i ∈ Finset.range (r + 1), ∏ j ∈ Finset.range (r + 1),
      g ((α ^ i * β ^ (r - i)) * (α ^ j * β ^ (r - j)))) =
    ∏ t ∈ Finset.range (r + 1), ∏ i ∈ Finset.range (2 * t + 1),
      g (α ^ i * β ^ (2 * t - i)) := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [show r + 1 + 1 = r + 2 by omega, satake_tensor_product_step hp, ih,
      Finset.prod_range_succ (n := r + 1)]

end
end Dubon2026
