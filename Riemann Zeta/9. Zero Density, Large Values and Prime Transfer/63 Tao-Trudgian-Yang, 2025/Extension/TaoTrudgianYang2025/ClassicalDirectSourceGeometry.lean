import TaoTrudgianYang2025.ClassicalDirectSourceRadius

/-!
# Literal two-length direct-source geometry

The two dyadic lengths are Q/2 and Q, with Q=2^r floor(T^a).
Both retain the physical lower cutoff. When the original source scale
is at least two, their actual logarithmic scales stay in [2,1/a].
-/

noncomputable section
namespace TaoTrudgianYang2025
open RiemannZeta.GuthMaynard

theorem classicalDirectDyadicLength_physical_lower
    (T a : ℝ) (r : ℕ) (c : Fin 2)
    (hPower : 2 ≤ T^a) (hr : 2 ≤ r) :
    T^a ≤ (classicalDirectDyadicLength (2^r*⌊T^a⌋₊) c : ℝ) := by
  let Y := ⌊T^a⌋₊
  have hFloor : T^a < (Y : ℝ)+1 := by
    simpa only [Y,Nat.cast_add,Nat.cast_one] using Nat.lt_floor_add_one (T^a)
  have hTwice : T^a ≤ 2*(Y : ℝ) := by linarith
  have hPow : 4 ≤ 2^r := by
    simpa using Nat.pow_le_pow_right (by omega : 0 < 2) hr
  have hQ : 4*Y ≤ 2^r*Y := Nat.mul_le_mul_right Y hPow
  have hHalf : 2*Y ≤ (2^r*Y)/2 := by omega
  have hLength := (classicalDirectDyadicLength_bounds (2^r*Y) c).1
  have hLower : 2*Y ≤ classicalDirectDyadicLength (2^r*Y) c := hHalf.trans hLength
  have hCast : 2*(Y : ℝ) ≤ (classicalDirectDyadicLength (2^r*Y) c : ℝ) := by
    exact_mod_cast hLower
  exact hTwice.trans hCast

theorem classicalDirectDyadicLength_logarithmic_bounds
    (T a : ℝ) (r : ℕ) (c : Fin 2)
    (hT : 1 ≤ T) (ha : 0 < a) (hPower : 2 ≤ T^a) (hr : 2 ≤ r)
    (hScale : 2 ≤ typeILogarithmicScale T (2^r*⌊T^a⌋₊)) :
    let N := classicalDirectDyadicLength (2^r*⌊T^a⌋₊) c
    1 < N ∧ (N : ℝ) ≤ T ∧ T^a ≤ (N : ℝ) ∧
      2 ≤ typeILogarithmicScale T N ∧ typeILogarithmicScale T N ≤ 1/a := by
  dsimp only
  let Q := 2^r*⌊T^a⌋₊
  let N := classicalDirectDyadicLength Q c
  have hLower := classicalDirectDyadicLength_physical_lower T a r c hPower hr
  have hNReal : (1 : ℝ) < N := by
    change (1 : ℝ) < (classicalDirectDyadicLength (2^r*⌊T^a⌋₊) c : ℝ)
    linarith
  have hN : 1 < N := by exact_mod_cast hNReal
  have hNQ : N ≤ Q := (classicalDirectDyadicLength_bounds Q c).2
  have hQ : 1 < Q := hN.trans_le hNQ
  have hTPos : 0 < T := zero_lt_one.trans_le hT
  have hLogLower : 2 ≤ typeILogarithmicScale T N :=
    hScale.trans (typeILogarithmicScale_antitone_length hT hN hNQ)
  have hNUpper : (N : ℝ) ≤ T := by
    have hPhysical := (Real.le_logb_iff_rpow_le hNReal hTPos).mp hLogLower
    have hSelf : (N : ℝ) ≤ (N : ℝ)^(2 : ℝ) :=
      Real.self_le_rpow_of_one_le hNReal.le (by norm_num)
    exact hSelf.trans hPhysical
  have hLogUpper : typeILogarithmicScale T N ≤ 1/a := by
    apply (Real.logb_le_iff_le_rpow hNReal hTPos).mpr
    calc
      T = (T^a)^(1/a) := by
        rw [← Real.rpow_mul hTPos.le]
        have hCancel : a*(1/a) = 1 := by field_simp
        rw [hCancel,Real.rpow_one]
      _ ≤ (N : ℝ)^(1/a) := Real.rpow_le_rpow (Real.rpow_nonneg hTPos.le _)
        hLower (by positivity)
  exact ⟨hN,hNUpper,hLower,hLogLower,hLogUpper⟩

end TaoTrudgianYang2025
