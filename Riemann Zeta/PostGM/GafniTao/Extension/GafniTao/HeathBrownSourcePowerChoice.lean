import GafniTao.ClassicalBinaryHeathBrownSourceDetector

/-!
# Arbitrary physical power choice in the Heath--Brown reduction

For a selected length `N` well below the height `B`, the source chooses the
integer part of `log B / log N`.  The resulting powered length lies below
`B`, its companion lies above `B`, and its logarithmic scale is at most
`3/2`.  This is the arbitrary-power version required when the detector's
two small cutoff exponents tend to zero.
-/

namespace GafniTao

noncomputable section

/-- The literal integer power selected from the physical scales. -/
noncomputable def heathBrownSourcePower (N : Nat) (B : Real) : Nat :=
  Nat.floor (Real.log B / Real.log (N : Real))

private theorem heathBrown_height_eq_rpow_log_ratio
    {N : Nat} {B : Real} (hN : 1 < N) (hB : 0 < B) :
    (N : Real) ^ (Real.log B / Real.log (N : Real)) = B := by
  have hNReal : (1 : Real) < N := by exact_mod_cast hN
  have hlogN : 0 < Real.log (N : Real) := Real.log_pos hNReal
  rw [Real.rpow_def_of_pos (by positivity)]
  have harg : Real.log B / Real.log (N : Real) * Real.log (N : Real) =
      Real.log B := by field_simp
  rw [mul_comm (Real.log (N : Real)), harg, Real.exp_log hB]

/-- Exact source scale window for the selected arbitrary power. -/
theorem heathBrownSourcePower_spec
    {N : Nat} {B : Real} (hN : 1 < N) (hB : 0 < B)
    (hNcube : (N : Real) ^ 3 <= B) :
    let p := heathBrownSourcePower N B
    3 <= p /\ (N : Real) ^ p <= B /\ B < (N : Real) ^ (p + 1) /\
      B ^ 2 <= ((N : Real) ^ p) ^ 3 := by
  dsimp only
  let q := Real.log B / Real.log (N : Real)
  let p := Nat.floor q
  have hNReal : (1 : Real) < N := by exact_mod_cast hN
  have hNPos : (0 : Real) < N := by positivity
  have hlogN : 0 < Real.log (N : Real) := Real.log_pos hNReal
  have hBLower : (1 : Real) < B := by
    have hCubeOne : (1 : Real) < (N : Real) ^ 3 := by
      calc
        (1 : Real) = (N : Real) ^ (0 : Real) := (Real.rpow_zero _).symm
        _ < (N : Real) ^ (3 : Real) :=
          Real.strictMono_rpow_of_base_gt_one hNReal (by norm_num)
        _ = (N : Real) ^ (3 : Nat) := Real.rpow_natCast _ 3
    exact hCubeOne.trans_le hNcube
  have hlogB : 0 < Real.log B := Real.log_pos hBLower
  have hqNonneg : 0 <= q := by
    dsimp only [q]
    positivity
  have hqThree : (3 : Real) <= q := by
    have hlogPow : Real.log ((N : Real) ^ 3) <= Real.log B :=
      Real.log_le_log (by positivity) hNcube
    rw [Real.log_pow] at hlogPow
    dsimp only [q]
    apply (le_div_iff₀ hlogN).2
    simpa only [Nat.cast_ofNat] using hlogPow
  have hpThree : 3 <= p := by
    apply (Nat.le_floor_iff hqNonneg).2
    exact hqThree
  have hpLeQ : (p : Real) <= q := Nat.floor_le hqNonneg
  have hqLt : q < (p : Real) + 1 := by
    simpa only [Nat.cast_add, Nat.cast_one] using Nat.lt_floor_add_one q
  have hBAsPower : (N : Real) ^ q = B := by
    simpa only [q] using heathBrown_height_eq_rpow_log_ratio hN hB
  have hBase : (N : Real) ^ p <= B := by
    rw [show (N : Real) ^ p = (N : Real) ^ (p : Real) by
      exact (Real.rpow_natCast (N : Real) p).symm, ← hBAsPower]
    exact (Real.strictMono_rpow_of_base_gt_one hNReal).monotone hpLeQ
  have hCompanion : B < (N : Real) ^ (p + 1) := by
    calc
      B = (N : Real) ^ q := hBAsPower.symm
      _ < (N : Real) ^ ((p : Real) + 1) :=
        Real.strictMono_rpow_of_base_gt_one hNReal hqLt
      _ = (N : Real) ^ (p + 1 : Nat) := by
        rw [← Real.rpow_natCast]
        push_cast
        rfl
  have hTwoQThreeP : 2 * q <= 3 * (p : Real) := by
    have hpTwo : (2 : Real) <= p := by exact_mod_cast (show 2 <= p by omega)
    linarith
  have hScale : B ^ 2 <= ((N : Real) ^ p) ^ 3 := by
    calc
      B ^ (2 : Nat) = B ^ (2 : Real) := (Real.rpow_natCast B 2).symm
      _ = ((N : Real) ^ q) ^ (2 : Real) := by rw [hBAsPower]
      _ = (N : Real) ^ (q * 2) := (Real.rpow_mul hNPos.le q 2).symm
      _ <= (N : Real) ^ ((p : Real) * 3) :=
        (Real.strictMono_rpow_of_base_gt_one hNReal).monotone (by
          simpa only [Nat.cast_ofNat, mul_comm] using hTwoQThreeP)
      _ = ((N : Real) ^ (p : Real)) ^ (3 : Real) :=
        Real.rpow_mul hNPos.le (p : Real) 3
      _ = ((N : Real) ^ p) ^ (3 : Real) := by
        exact congrArg (fun z : Real => z ^ (3 : Real))
          (Real.rpow_natCast (N : Real) p)
      _ = ((N : Real) ^ p) ^ (3 : Nat) :=
        Real.rpow_natCast ((N : Real) ^ p) 3
  simpa only [heathBrownSourcePower, p, q] using
    And.intro hpThree (And.intro hBase (And.intro hCompanion hScale))

/-- Exact source scale window when only the square of the selected length is
known to lie below the physical height.  The exponent `2` is the sharp
threshold needed for `B^2 <= (N^p)^3`: from `p <= q < p + 1` and `2 <= p`
one obtains `2 * q <= 3 * p`. -/
theorem heathBrownSourcePower_spec_two
    {N : Nat} {B : Real} (hN : 1 < N) (hB : 0 < B)
    (hNsq : (N : Real) ^ 2 <= B) :
    let p := heathBrownSourcePower N B
    2 <= p /\ (N : Real) ^ p <= B /\ B < (N : Real) ^ (p + 1) /\
      B ^ 2 <= ((N : Real) ^ p) ^ 3 := by
  dsimp only
  let q := Real.log B / Real.log (N : Real)
  let p := Nat.floor q
  have hNReal : (1 : Real) < N := by exact_mod_cast hN
  have hNPos : (0 : Real) < N := by positivity
  have hlogN : 0 < Real.log (N : Real) := Real.log_pos hNReal
  have hBLower : (1 : Real) < B := by
    have hSquareOne : (1 : Real) < (N : Real) ^ 2 := by
      calc
        (1 : Real) = (N : Real) ^ (0 : Real) := (Real.rpow_zero _).symm
        _ < (N : Real) ^ (2 : Real) :=
          Real.strictMono_rpow_of_base_gt_one hNReal (by norm_num)
        _ = (N : Real) ^ (2 : Nat) := Real.rpow_natCast _ 2
    exact hSquareOne.trans_le hNsq
  have hlogB : 0 < Real.log B := Real.log_pos hBLower
  have hqNonneg : 0 <= q := by
    dsimp only [q]
    positivity
  have hqTwo : (2 : Real) <= q := by
    have hlogPow : Real.log ((N : Real) ^ 2) <= Real.log B :=
      Real.log_le_log (by positivity) hNsq
    rw [Real.log_pow] at hlogPow
    dsimp only [q]
    apply (le_div_iff₀ hlogN).2
    simpa only [Nat.cast_ofNat] using hlogPow
  have hpTwo : 2 <= p := by
    apply (Nat.le_floor_iff hqNonneg).2
    exact hqTwo
  have hpLeQ : (p : Real) <= q := Nat.floor_le hqNonneg
  have hqLt : q < (p : Real) + 1 := by
    simpa only [Nat.cast_add, Nat.cast_one] using Nat.lt_floor_add_one q
  have hBAsPower : (N : Real) ^ q = B := by
    simpa only [q] using heathBrown_height_eq_rpow_log_ratio hN hB
  have hBase : (N : Real) ^ p <= B := by
    rw [show (N : Real) ^ p = (N : Real) ^ (p : Real) by
      exact (Real.rpow_natCast (N : Real) p).symm, ← hBAsPower]
    exact (Real.strictMono_rpow_of_base_gt_one hNReal).monotone hpLeQ
  have hCompanion : B < (N : Real) ^ (p + 1) := by
    calc
      B = (N : Real) ^ q := hBAsPower.symm
      _ < (N : Real) ^ ((p : Real) + 1) :=
        Real.strictMono_rpow_of_base_gt_one hNReal hqLt
      _ = (N : Real) ^ (p + 1 : Nat) := by
        rw [← Real.rpow_natCast]
        push_cast
        rfl
  have hTwoQThreeP : 2 * q <= 3 * (p : Real) := by
    have hpTwoReal : (2 : Real) <= p := by exact_mod_cast hpTwo
    linarith
  have hScale : B ^ 2 <= ((N : Real) ^ p) ^ 3 := by
    calc
      B ^ (2 : Nat) = B ^ (2 : Real) := (Real.rpow_natCast B 2).symm
      _ = ((N : Real) ^ q) ^ (2 : Real) := by rw [hBAsPower]
      _ = (N : Real) ^ (q * 2) := (Real.rpow_mul hNPos.le q 2).symm
      _ <= (N : Real) ^ ((p : Real) * 3) :=
        (Real.strictMono_rpow_of_base_gt_one hNReal).monotone (by
          simpa only [Nat.cast_ofNat, mul_comm] using hTwoQThreeP)
      _ = ((N : Real) ^ (p : Real)) ^ (3 : Real) :=
        Real.rpow_mul hNPos.le (p : Real) 3
      _ = ((N : Real) ^ p) ^ (3 : Real) := by
        exact congrArg (fun z : Real => z ^ (3 : Real))
          (Real.rpow_natCast (N : Real) p)
      _ = ((N : Real) ^ p) ^ (3 : Nat) :=
        Real.rpow_natCast ((N : Real) ^ p) 3
  simpa only [heathBrownSourcePower, p, q] using
    And.intro hpTwo (And.intro hBase (And.intro hCompanion hScale))

/-- A fixed positive lower power of the physical height bounds the selected
source power uniformly.  This is the exact ceiling comparison used after a
source block has been localized; no logarithmic-scale variable is inserted. -/
theorem heathBrownSourcePower_le_ceil_of_rpow_le
    {N : Nat} {B delta : Real}
    (hN : 1 < N) (hB : 1 < B) (hdelta : 0 < delta)
    (hLower : B ^ (delta / 4) <= (N : Real)) :
    heathBrownSourcePower N B <= Nat.ceil (4 / delta) := by
  have hlogB : 0 < Real.log B := Real.log_pos hB
  have hBPos : 0 < B := zero_lt_one.trans hB
  have hNReal : (1 : Real) < N := by exact_mod_cast hN
  have hlogN : 0 < Real.log (N : Real) := Real.log_pos hNReal
  have hLogLower : (delta / 4) * Real.log B <= Real.log (N : Real) := by
    have h := Real.log_le_log (Real.rpow_pos_of_pos hBPos _)
      (by simpa only using hLower)
    rw [Real.log_rpow hBPos] at h
    exact h
  have hRatio : Real.log B / Real.log (N : Real) <= 4 / delta := by
    apply (div_le_iff₀ hlogN).2
    calc
      Real.log B = (4 / delta) * ((delta / 4) * Real.log B) := by
        field_simp [hdelta.ne']
      _ <= (4 / delta) * Real.log (N : Real) := by
        gcongr
  have hRatioNonneg : 0 <= Real.log B / Real.log (N : Real) := by positivity
  have hFloor : (heathBrownSourcePower N B : Real) <= 4 / delta := by
    exact (Nat.floor_le hRatioNonneg).trans hRatio
  exact_mod_cast hFloor.trans (Nat.le_ceil (4 / delta))

#print axioms heathBrownSourcePower_spec
#print axioms heathBrownSourcePower_spec_two
#print axioms heathBrownSourcePower_le_ceil_of_rpow_le

end

end GafniTao
