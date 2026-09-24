import TaoTrudgianYang2025.ClassicalBottomSourceIndexed
import TaoTrudgianYang2025.ClassicalTypeIIEnergyTransfer

/-!
# Physical scales for the two bottom global source blocks

The source support gives Q/4 < N < 2Q. For r=0 or r=1 and
Y=floor(T^a), this forces T^(a/2) ≤ N ≤ T^(2a) at large height.
The logarithmic scale is consequently in the compact general-LV range.
-/

noncomputable section
namespace TaoTrudgianYang2025
open RiemannZeta.GuthMaynard

theorem classicalBottomSource_physical_bounds
    (T a : ℝ) (r N : ℕ)
    (hT : 0 < T) (hPower : 8 ≤ T^(a/2)) (hr : r < 2)
    (hLower : 2^r*⌊T^a⌋₊ < 4*N)
    (hUpper : N < 2*(2^r*⌊T^a⌋₊)) :
    T^(a/2) ≤ (N : ℝ) ∧ (N : ℝ) ≤ T^(2*a) := by
  let Y := ⌊T^a⌋₊
  have hPow : 1 ≤ 2^r ∧ 2^r ≤ 2 := by
    interval_cases r <;> norm_num
  have hYQ : Y ≤ 2^r*Y := by
    simpa only [one_mul] using Nat.mul_le_mul_right Y hPow.1
  have hQY : 2^r*Y ≤ 2*Y := Nat.mul_le_mul_right Y hPow.2
  have hYL : (Y : ℝ) < 4*N := by
    exact_mod_cast hYQ.trans_lt hLower
  have hNU : (N : ℝ) < 4*Y := by
    have hn : N < 4*Y := hUpper.trans_le (by dsimp only [Y] at hQY ⊢; omega)
    exact_mod_cast hn
  have hFloor : T^a < (Y : ℝ)+1 := by
    simpa only [Y,Nat.cast_add,Nat.cast_one] using Nat.lt_floor_add_one (T^a)
  have hFloorU : (Y : ℝ) ≤ T^a := Nat.floor_le (Real.rpow_nonneg hT.le _)
  have hSquare : (T^(a/2))^2 = T^a := by
    rw [← Real.rpow_natCast,← Real.rpow_mul hT.le]
    congr 1
    ring
  have hDouble : (T^a)^2 = T^(2*a) := by
    rw [← Real.rpow_natCast,← Real.rpow_mul hT.le]
    congr 1
    ring
  constructor
  · nlinarith [sq_nonneg (T^(a/2)-8)]
  · nlinarith [sq_nonneg (T^a-4)]

theorem eventually_classicalBottomSource_physical_bounds
    (a : ℝ) (ha : 0 < a) :
    ∀ᶠ T : ℝ in Filter.atTop, ∀ r N : ℕ, r < 2 →
      2^r*⌊T^a⌋₊ < 4*N → N < 2*(2^r*⌊T^a⌋₊) →
      T^(a/2) ≤ (N : ℝ) ∧ (N : ℝ) ≤ T^(2*a) := by
  filter_upwards [Filter.eventually_ge_atTop (1 : ℝ),
    (tendsto_rpow_atTop (by linarith : 0 < a/2)).eventually
      (Filter.eventually_ge_atTop (8 : ℝ))] with T hT hPower
  intro r N hr hLower hUpper
  exact classicalBottomSource_physical_bounds T a r N
    (zero_lt_one.trans_le hT) hPower hr hLower hUpper

theorem eventually_classicalBottomSource_logScale_near_interval
    (a δ : ℝ) (ha : 0 < a) (hδ : 0 < δ) :
    ∀ᶠ T : ℝ in Filter.atTop, ∀ (r N : ℕ) (H : ℝ), r < 2 →
      2^r*⌊T^a⌋₊ < 4*N → N < 2*(2^r*⌊T^a⌋₊) →
      T ≤ H → H ≤ 3*T →
      ∃ τ ∈ Set.Icc (1/(2*a)) (2/a), |Real.logb (N : ℝ) H-τ| ≤ δ := by
  filter_upwards [eventually_classicalBottomSource_physical_bounds a ha,
    eventually_classicalTypeII_logScale_near_interval (2*a) (a/2) δ
      (by positivity) (by positivity) (by linarith) hδ] with T hBounds hNear
  intro r N H hr hLower hUpper hHL hHU
  obtain ⟨hNL,hNU⟩ := hBounds r N hr hLower hUpper
  have hInv : 1/(a/2) = 2/a := by rw [div_div_eq_mul_div]; ring
  simpa only [hInv] using hNear N H hNL hNU hHL hHU

end TaoTrudgianYang2025
