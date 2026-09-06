import GafniTao.ClassicalBinaryPhysicalDetector

/-!
# Exact Heath--Brown cutoff for the classical binary detector

The natural floor in `floor (U^(1/4))` prevents the literal comparison
`U <= X^4`.  Heath--Brown's exponent calculation is insensitive to fixed
constants, so the faithful finite choice is

`X = 4 * floor (U^(1/4))`,  `B = X^4`.

For large `U`, this gives `16 U <= B <= 256 U`.  Every selected Type-II
scale `N` lies in `[X,X^2)`, hence satisfies the exact physical window
`N^2 <= B <= N^4`.  No floor is silently replaced by a real power.
-/

namespace GafniTao

noncomputable section

open Filter RiemannZeta.GuthMaynard

/-- The constant-expanded fourth-root cutoff used in the finite
Heath--Brown argument. -/
noncomputable def classicalBinaryHeathBrownCutoff (U : Real) : Nat :=
  4 * classicalBinaryPhysicalCutoff U (1 / 4)

/-- The corresponding exact ambient height. -/
noncomputable def classicalBinaryHeathBrownHeight (U : Real) : Real :=
  (classicalBinaryHeathBrownCutoff U : Real) ^ 4

/-- Eventually the expanded cutoff is admissible and its fourth power is
within fixed constant factors of the source height. -/
theorem eventually_classicalBinaryHeathBrownCutoff_spec :
    ∃ U0 : Real, 8 ≤ U0 ∧ ∀ U : Real, U0 ≤ U →
      let X := classicalBinaryHeathBrownCutoff U
      0 < X ∧ (X : Real) ≤ U ∧
        X ≤ Nat.floor (sharpZetaCutoff U) ∧
        16 * U ≤ (X : Real) ^ 4 ∧
        (X : Real) ^ 4 ≤ 256 * U := by
  obtain ⟨Uf, hUf, hFloor⟩ :=
    eventually_classicalBinaryPhysicalCutoff_spec
      (alpha := (1 / 4 : Real)) (by norm_num) (by norm_num)
  have hTend : Tendsto (fun U : Real => U ^ (3 / 4 : Real)) atTop atTop :=
    tendsto_rpow_atTop (by norm_num)
  have hEventually : ∀ᶠ U : Real in atTop, 4 ≤ U ^ (3 / 4 : Real) :=
    hTend (eventually_ge_atTop 4)
  rw [eventually_atTop] at hEventually
  obtain ⟨Ug, hUg⟩ := hEventually
  let U0 := max Uf Ug
  refine ⟨U0, hUf.trans (le_max_left _ _), ?_⟩
  intro U hU
  have hUfU : Uf ≤ U := (le_max_left _ _).trans hU
  have hUgU : Ug ≤ U := (le_max_right _ _).trans hU
  have hSpec := hFloor U hUfU
  let x := classicalBinaryPhysicalCutoff U (1 / 4)
  have hUOne : 1 ≤ U := by linarith [hUf.trans hUfU]
  have hUPos : 0 < U := zero_lt_one.trans_le hUOne
  have hxPos : 0 < x := by simpa only [x] using hSpec.1
  have hxLower : U ^ (1 / 4 : Real) / 2 ≤ (x : Real) := by
    simpa only [x] using hSpec.2.1
  have hxUpper : (x : Real) ≤ U ^ (1 / 4 : Real) := by
    simpa only [x] using hSpec.2.2.1
  have hQuarterNonneg : 0 ≤ U ^ (1 / 4 : Real) :=
    Real.rpow_nonneg hUPos.le _
  have hCastX : (classicalBinaryHeathBrownCutoff U : Real) = 4 * (x : Real) := by
    simp [classicalBinaryHeathBrownCutoff, x]
  have hXLeU : (classicalBinaryHeathBrownCutoff U : Real) ≤ U := by
    calc
      (classicalBinaryHeathBrownCutoff U : Real) = 4 * (x : Real) := hCastX
      _ ≤ 4 * U ^ (1 / 4 : Real) :=
        mul_le_mul_of_nonneg_left hxUpper (by norm_num)
      _ ≤ U ^ (3 / 4 : Real) * U ^ (1 / 4 : Real) :=
        mul_le_mul_of_nonneg_right (hUg U hUgU) hQuarterNonneg
      _ = U := by
        rw [← Real.rpow_add hUPos]
        norm_num
  have hXSharp : classicalBinaryHeathBrownCutoff U ≤
      Nat.floor (sharpZetaCutoff U) := by
    apply Nat.le_floor
    exact hXLeU.trans (by
      exact (show U ≤ 4 * U by nlinarith).trans
        (four_mul_lt_sharpZetaCutoff U).le)
  have hLowerBase : 2 * U ^ (1 / 4 : Real) ≤
      (classicalBinaryHeathBrownCutoff U : Real) := by
    rw [hCastX]
    linarith
  have hUpperBase : (classicalBinaryHeathBrownCutoff U : Real) ≤
      4 * U ^ (1 / 4 : Real) := by
    rw [hCastX]
    exact mul_le_mul_of_nonneg_left hxUpper (by norm_num)
  have hPowQuarter : (U ^ (1 / 4 : Real)) ^ 4 = U := by
    calc
      (U ^ (1 / 4 : Real)) ^ 4 =
          U ^ ((1 / 4 : Real) * (4 : Real)) :=
        (Real.rpow_mul_natCast hUPos.le (1 / 4 : Real) 4).symm
      _ = U := by norm_num
  have hLowerFourth := pow_le_pow_left₀
    (by positivity : 0 ≤ 2 * U ^ (1 / 4 : Real)) hLowerBase 4
  have hUpperFourth := pow_le_pow_left₀
    (by positivity : 0 ≤ (classicalBinaryHeathBrownCutoff U : Real))
    hUpperBase 4
  refine ⟨by
      unfold classicalBinaryHeathBrownCutoff
      exact Nat.mul_pos (by omega) hxPos,
    hXLeU,
    hXSharp, ?_, ?_⟩
  · calc
      16 * U = (2 * U ^ (1 / 4 : Real)) ^ 4 := by
        rw [mul_pow, hPowQuarter]
        norm_num
      _ ≤ (classicalBinaryHeathBrownCutoff U : Real) ^ 4 := hLowerFourth
  · calc
      (classicalBinaryHeathBrownCutoff U : Real) ^ 4 ≤
          (4 * U ^ (1 / 4 : Real)) ^ 4 := hUpperFourth
      _ = 256 * U := by
        rw [mul_pow, hPowQuarter]
        norm_num

/-- Eventually the expanded ambient height contains the complete oriented
shell whenever the detector displacement exponent is at most one. -/
theorem eventually_classicalBinaryHeathBrownHeight_contains_shell
    {delta : Real} (hdelta : delta ≤ 1) :
    ∃ U0 : Real, 8 ≤ U0 ∧ ∀ U : Real, U0 ≤ U →
      2 * (2 * U + U ^ delta) ≤ classicalBinaryHeathBrownHeight U := by
  obtain ⟨U0, _hU0, hSpec⟩ :=
    eventually_classicalBinaryHeathBrownCutoff_spec
  refine ⟨U0, _hU0, ?_⟩
  intro U hLarge
  have h := hSpec U hLarge
  dsimp only at h
  have hUOne : 1 ≤ U := by linarith [_hU0]
  have hPow : U ^ delta ≤ U := by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le hUOne hdelta
  unfold classicalBinaryHeathBrownHeight
  linarith [h.2.2.2.1]

/-- Every Type-II scale selected at the expanded cutoff lies in the exact
two-to-four physical power window for the comparable ambient height. -/
theorem classicalBinarySelected_typeII_heathBrown_powerWindow
    {kI kII : Nat} {U : Real}
    (hX : 0 < classicalBinaryHeathBrownCutoff U)
    (hkII : kII ≤ Nat.clog 2 (classicalBinaryHeathBrownCutoff U))
    (q : Fin (kI * 2 + kII * 2))
    (r : Fin (kII * 2)) (hq : binaryScaleLabel q = Sum.inr r) :
    let X := classicalBinaryHeathBrownCutoff U
    let N := classicalBinarySelectedN X X kI kII q
    (N : Real) ^ 2 ≤ classicalBinaryHeathBrownHeight U ∧
      classicalBinaryHeathBrownHeight U ≤ (N : Real) ^ 4 := by
  dsimp only
  have hRange := classicalBinarySelectedN_typeII_equal_cutoff_range
    hX hkII q r hq
  unfold classicalBinaryHeathBrownHeight
  constructor
  · have hUpper : (classicalBinarySelectedN
        (classicalBinaryHeathBrownCutoff U)
        (classicalBinaryHeathBrownCutoff U) kI kII q : Real) ≤
        (classicalBinaryHeathBrownCutoff U : Real) ^ 2 := by
      exact_mod_cast hRange.2.le
    calc
      (classicalBinarySelectedN
          (classicalBinaryHeathBrownCutoff U)
          (classicalBinaryHeathBrownCutoff U) kI kII q : Real) ^ 2 ≤
          ((classicalBinaryHeathBrownCutoff U : Real) ^ 2) ^ 2 :=
        pow_le_pow_left₀ (by positivity) hUpper 2
      _ = (classicalBinaryHeathBrownCutoff U : Real) ^ 4 := by ring
  · have hLower : (classicalBinaryHeathBrownCutoff U : Real) ≤
        (classicalBinarySelectedN
          (classicalBinaryHeathBrownCutoff U)
          (classicalBinaryHeathBrownCutoff U) kI kII q : Real) := by
      exact_mod_cast hRange.1
    exact pow_le_pow_left₀ (by positivity) hLower 4

#print axioms eventually_classicalBinaryHeathBrownCutoff_spec
#print axioms classicalBinarySelected_typeII_heathBrown_powerWindow

end

end GafniTao
