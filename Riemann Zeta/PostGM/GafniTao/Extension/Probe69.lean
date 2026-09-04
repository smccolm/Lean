import GafniTao.WooleyInitialConditioning

open Finset
open scoped BigOperators

theorem probe_real_add_pow_le {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    {s : ℕ} (hs : 1 ≤ s) :
    (a + b) ^ s ≤ 2 ^ (s - 1) * (a ^ s + b ^ s) := by
  let aa : ℝ≥0 := ⟨a, ha⟩
  let bb : ℝ≥0 := ⟨b, hb⟩
  have h := NNReal.rpow_add_le_mul_rpow_add_rpow aa bb
    (p := (s : ℝ)) (by exact_mod_cast hs)
  norm_cast at h
  simpa [aa, bb, Real.rpow_natCast] using h
