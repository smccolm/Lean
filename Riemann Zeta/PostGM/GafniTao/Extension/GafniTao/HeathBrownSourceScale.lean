import GafniTao.HeathBrownSourcePowerChoice
import GafniTao.ClassicalBinarySelectedScale

/-!
# Physical scale bounds at the two source cutoffs

This file keeps the two zero-detection cutoffs distinct.  It proves the
eventual floor comparison needed to turn the Type-II lower cutoff into a
uniform logarithmic lower bound, and then derives the exact physical window
and a fixed upper bound for the source power.
-/

namespace GafniTao

noncomputable section

open Filter RiemannZeta.GuthMaynard

/-- If `0 < a < b`, then the floor of `U^b` eventually dominates `U^a`.
The statement retains the natural floor rather than replacing it
definitionally by a real power. -/
theorem eventually_rpow_le_natFloor_rpow
    {a b : Real} (ha : 0 < a) (hab : a < b) :
    exists U0 : Real, 1 <= U0 /\ forall U : Real, U0 <= U ->
      U ^ a <= (Nat.floor (U ^ b) : Real) := by
  obtain ⟨Ufloor, hUfloor, hFloor⟩ :=
    eventually_half_rpow_le_natFloor b (ha.trans hab)
  have hGap : 0 < b - a := by linarith
  have hTend : Tendsto (fun U : Real => U ^ (b - a)) atTop atTop :=
    tendsto_rpow_atTop hGap
  have hEventually : ∀ᶠ U : Real in atTop, 2 <= U ^ (b - a) :=
    (tendsto_atTop.1 hTend) 2
  rw [eventually_atTop] at hEventually
  obtain ⟨Ugap, hUgap⟩ := hEventually
  let U0 := max Ufloor Ugap
  refine ⟨U0, hUfloor.trans (le_max_left _ _), ?_⟩
  intro U hU
  have hFloor := hFloor U ((le_max_left _ _).trans hU)
  have hGapU := hUgap U ((le_max_right _ _).trans hU)
  have hUOne : 1 <= U := hUfloor.trans ((le_max_left _ _).trans hU)
  have hUPos : 0 < U := zero_lt_one.trans_le hUOne
  have haNonneg : 0 <= U ^ a := (Real.rpow_pos_of_pos hUPos _).le
  have hFactor : 2 * U ^ a <= U ^ b := by
    calc
      2 * U ^ a <= U ^ (b - a) * U ^ a :=
        mul_le_mul_of_nonneg_right hGapU haNonneg
      _ = U ^ b := by
        rw [← Real.rpow_add hUPos]
        congr 1
        ring
  exact (by linarith [hFactor, hFloor.1] : U ^ a <=
    (Nat.floor (U ^ b) : Real))

/-- Exact source-scale consequences for a Type-II block.  The hypothesis on
`delta1 + delta2/2` is precisely what makes the cube of every selected length
fit below the physical height. -/
theorem eventually_heathBrown_source_typeII_scale
    {delta1 delta2 : Real}
    (hdelta1 : 0 < delta1) (hdelta2 : 0 < delta2)
    (hCubeExponent : 3 * (delta1 + delta2 / 2) <= 1) :
    exists U0 : Real, 8 <= U0 /\ forall U : Real, U0 <= U ->
      let X := Nat.floor (U ^ (delta2 / 2))
      let Y := Nat.floor (U ^ delta1)
      forall {kI kII : Nat} (_hkII : kII <= Nat.clog 2 Y)
        (q : Fin (kI * 2 + kII * 2)) (r : Fin (kII * 2)),
        binaryScaleLabel q = Sum.inr r ->
        let N := classicalBinarySelectedN Y X kI kII q
        let p := heathBrownSourcePower N U
        1 < N /\ U ^ (delta2 / 4) <= (N : Real) /\
          (N : Real) < U ^ (delta1 + delta2 / 2) /\
          (N : Real) ^ 3 <= U /\
          3 <= p /\ (N : Real) ^ p <= U /\
          U < (N : Real) ^ (p + 1) /\
          U ^ 2 <= ((N : Real) ^ p) ^ 3 /\
          p <= Nat.ceil (4 / delta2) := by
  obtain ⟨Ulower, hUlower, hLower⟩ :=
    eventually_rpow_le_natFloor_rpow
      (a := delta2 / 4) (b := delta2 / 2) (by positivity) (by linarith)
  let U0 := max 8 Ulower
  refine ⟨U0, le_max_left _ _, ?_⟩
  intro U hU
  dsimp only
  intro kI kII _hkII q r hq
  let X := Nat.floor (U ^ (delta2 / 2))
  let Y := Nat.floor (U ^ delta1)
  let N := classicalBinarySelectedN Y X kI kII q
  have hUEight : 8 <= U := (le_max_left _ _).trans hU
  have hUOne : 1 <= U := by linarith
  have hUPos : 0 < U := zero_lt_one.trans_le hUOne
  have hLowerX : U ^ (delta2 / 4) <= (X : Real) := by
    simpa only [X] using hLower U ((le_max_right _ _).trans hU)
  have hXPosReal : (0 : Real) < X :=
    (Real.rpow_pos_of_pos hUPos _).trans_le hLowerX
  have hXPos : 0 < X := by exact_mod_cast hXPosReal
  have hRange := classicalBinarySelectedN_typeII_range hXPos _hkII q r hq
  have hNLowerX : (X : Real) <= (N : Real) := by exact_mod_cast hRange.1
  have hNLower : U ^ (delta2 / 4) <= (N : Real) :=
    hLowerX.trans hNLowerX
  have hNPowLower : (1 : Real) < U ^ (delta2 / 4) :=
    Real.one_lt_rpow (by linarith [hUEight]) (by positivity)
  have hNOne : 1 < N := by
    exact_mod_cast hNPowLower.trans_le hNLower
  have hYUpper : (Y : Real) <= U ^ delta1 :=
    Nat.floor_le (Real.rpow_nonneg hUPos.le _)
  have hXUpper : (X : Real) <= U ^ (delta2 / 2) :=
    Nat.floor_le (Real.rpow_nonneg hUPos.le _)
  have hNProduct : (N : Real) < (Y : Real) * (X : Real) := by
    exact_mod_cast hRange.2
  have hNUpper : (N : Real) < U ^ (delta1 + delta2 / 2) := by
    calc
      (N : Real) < (Y : Real) * (X : Real) := hNProduct
      _ <= U ^ delta1 * U ^ (delta2 / 2) := by gcongr
      _ = U ^ (delta1 + delta2 / 2) := (Real.rpow_add hUPos _ _).symm
  have hCubeStrict : (N : Real) ^ 3 <
      (U ^ (delta1 + delta2 / 2)) ^ 3 :=
    pow_lt_pow_left₀ hNUpper (by positivity) (by norm_num)
  have hExponent : 3 * (delta1 + delta2 / 2) <= (1 : Real) :=
    hCubeExponent
  have hPowerUpper : (U ^ (delta1 + delta2 / 2)) ^ (3 : Nat) <= U := by
    calc
      (U ^ (delta1 + delta2 / 2)) ^ (3 : Nat) =
          U ^ ((delta1 + delta2 / 2) * 3) :=
        (Real.rpow_mul_natCast hUPos.le _ 3).symm
      _ <= U ^ (1 : Real) :=
        Real.rpow_le_rpow_of_exponent_le hUOne (by linarith)
      _ = U := Real.rpow_one U
  have hCube : (N : Real) ^ 3 <= U := hCubeStrict.le.trans hPowerUpper
  have hPower := heathBrownSourcePower_spec hNOne hUPos hCube
  dsimp only at hPower
  let p := heathBrownSourcePower N U
  have hlogU : 0 < Real.log U := Real.log_pos (by linarith [hUEight])
  have hlogN : 0 < Real.log (N : Real) :=
    Real.log_pos (by exact_mod_cast hNOne)
  have hLogLower : (delta2 / 4) * Real.log U <= Real.log (N : Real) := by
    have := Real.log_le_log (Real.rpow_pos_of_pos hUPos _)
      (by simpa only using hNLower)
    rw [Real.log_rpow hUPos] at this
    exact this
  have hRatioUpper : Real.log U / Real.log (N : Real) <= 4 / delta2 := by
    apply (div_le_iff₀ hlogN).2
    calc
      Real.log U = (4 / delta2) * ((delta2 / 4) * Real.log U) := by
        field_simp [hdelta2.ne']
      _ <= (4 / delta2) * Real.log (N : Real) := by
        gcongr
  have hpReal : (p : Real) <= 4 / delta2 := by
    exact (Nat.floor_le (by positivity : 0 <=
      Real.log U / Real.log (N : Real))).trans hRatioUpper
  have hpBound : p <= Nat.ceil (4 / delta2) := by
    exact_mod_cast hpReal.trans (Nat.le_ceil (4 / delta2))
  exact ⟨hNOne, hNLower, hNUpper, hCube, hPower.1, hPower.2.1,
    hPower.2.2.1, hPower.2.2.2, hpBound⟩

#print axioms eventually_rpow_le_natFloor_rpow
#print axioms eventually_heathBrown_source_typeII_scale

end

end GafniTao
