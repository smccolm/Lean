import GafniTao.HeathBrownHighAlgebra

/-!
# The two-or-three power choice in the high Heath--Brown cell

This is the exact scale selection in the high-`sigma` part of the pinned
ANTEDB reproduction of Heath--Brown's energy argument.  Put
`a = (4 * sigma - 1) / 2`.  For a physical scale in
`[2 * a, 4 * a]`, choose power two up to `3 * a` and power three above it.
The powered scale is then in `[a, 3 * a / 2]`, and the next-power scale is
at most `2 * a = 4 * sigma - 1`.
-/

namespace GafniTao

noncomputable section

/-- The literal `k = 2,3` choice in the high-energy source proof. -/
def heathBrownHighPower (sigma tau : Real) : Nat :=
  if tau ≤ 3 * (4 * sigma - 1) / 2 then 2 else 3

theorem heathBrownHighPower_eq_two_or_three (sigma tau : Real) :
    heathBrownHighPower sigma tau = 2 ∨
      heathBrownHighPower sigma tau = 3 := by
  by_cases h : tau ≤ 3 * (4 * sigma - 1) / 2
  · left
    simp [heathBrownHighPower, h]
  · right
    simp [heathBrownHighPower, h]

theorem heathBrownHighPower_pos (sigma tau : Real) :
    0 < heathBrownHighPower sigma tau := by
  rcases heathBrownHighPower_eq_two_or_three sigma tau with h | h <;>
    simp [h]

theorem heathBrownHighPower_le_three (sigma tau : Real) :
    heathBrownHighPower sigma tau ≤ 3 := by
  rcases heathBrownHighPower_eq_two_or_three sigma tau with h | h <;>
    simp [h]

/-- Exact source window for the energy-producing `k`-th power. -/
theorem heathBrownHighPower_scale_window
    {sigma tau : Real} (hsigma : 1 / 2 < sigma)
    (htauLower : 4 * sigma - 1 ≤ tau)
    (htauUpper : tau ≤ 2 * (4 * sigma - 1)) :
    (4 * sigma - 1) / 2 ≤
        tau / (heathBrownHighPower sigma tau : Real) ∧
      tau / (heathBrownHighPower sigma tau : Real) ≤
        3 * (4 * sigma - 1) / 4 := by
  have hscale : 0 < 4 * sigma - 1 := by linarith
  by_cases h : tau ≤ 3 * (4 * sigma - 1) / 2
  · simp only [heathBrownHighPower, if_pos h, Nat.cast_ofNat]
    constructor <;> linarith
  · have htauCut : 3 * (4 * sigma - 1) / 2 < tau := lt_of_not_ge h
    simp only [heathBrownHighPower, if_neg h, Nat.cast_ofNat]
    constructor <;> linarith

/-- The companion `(k+1)`-st power lies in the source's ordinary
large-value range. -/
theorem heathBrownHighPower_companion_scale
    {sigma tau : Real} (hsigma : 1 / 2 < sigma)
    (htauUpper : tau ≤ 2 * (4 * sigma - 1)) :
    tau / ((heathBrownHighPower sigma tau + 1 : Nat) : Real) ≤
      4 * sigma - 1 := by
  have hscale : 0 < 4 * sigma - 1 := by linarith
  by_cases h : tau ≤ 3 * (4 * sigma - 1) / 2
  · simp only [heathBrownHighPower, if_pos h, Nat.reduceAdd,
      Nat.cast_ofNat]
    linarith
  · simp only [heathBrownHighPower, if_neg h, Nat.reduceAdd,
      Nat.cast_ofNat]
    linarith

/-- The actual two-or-three choice gives the sharper companion bound used
by the Huxley large-value theorem.  The source prose records the weaker
upper bound `4 * sigma - 1`; division by `k+1` in fact saves a factor two. -/
theorem heathBrownHighPower_companion_scale_strong
    {sigma tau : Real} (hsigma : 1 / 2 < sigma)
    (htauUpper : tau ≤ 2 * (4 * sigma - 1)) :
    tau / ((heathBrownHighPower sigma tau + 1 : Nat) : Real) ≤
      (4 * sigma - 1) / 2 := by
  have hscale : 0 < 4 * sigma - 1 := by linarith
  by_cases h : tau ≤ 3 * (4 * sigma - 1) / 2
  · simp only [heathBrownHighPower, if_pos h, Nat.reduceAdd,
      Nat.cast_ofNat]
    linarith
  · simp only [heathBrownHighPower, if_neg h, Nat.reduceAdd,
      Nat.cast_ofNat]
    linarith

/-- Above three quarters, the sharper companion bound lies in the literal
Huxley range `tau ≤ 4 * sigma - 2`. -/
theorem heathBrownHighPower_companion_huxley_range
    {sigma tau : Real} (hsigmaLower : 3 / 4 ≤ sigma)
    (htauUpper : tau ≤ 2 * (4 * sigma - 1)) :
    tau / ((heathBrownHighPower sigma tau + 1 : Nat) : Real) ≤
      4 * sigma - 2 := by
  have hsigma : 1 / 2 < sigma := by linarith
  exact (heathBrownHighPower_companion_scale_strong hsigma htauUpper).trans
    (by linarith)

/-- The selected power is the first of `2,3` whose powered scale belongs
to the required interval. -/
theorem heathBrownHighPower_is_first
    {sigma tau : Real} (hsigma : 1 / 2 < sigma)
    (htauLower : 4 * sigma - 1 ≤ tau)
    (htauUpper : tau ≤ 2 * (4 * sigma - 1)) :
    (4 * sigma - 1) / 2 ≤
        tau / (heathBrownHighPower sigma tau : Real) ∧
      tau / (heathBrownHighPower sigma tau : Real) ≤
        3 * (4 * sigma - 1) / 4 ∧
      ∀ j : Nat, 2 ≤ j → j < heathBrownHighPower sigma tau →
        ¬ (tau / (j : Real) ≤ 3 * (4 * sigma - 1) / 4) := by
  have hwindow := heathBrownHighPower_scale_window hsigma htauLower htauUpper
  refine ⟨hwindow.1, hwindow.2, ?_⟩
  intro j hjLower hjUpper
  have hpCases := heathBrownHighPower_eq_two_or_three sigma tau
  rcases hpCases with hp | hp
  · omega
  · have hj : j = 2 := by omega
    subst j
    have hcut : ¬ tau ≤ 3 * (4 * sigma - 1) / 2 := by
      simpa [heathBrownHighPower] using hp
    have hcut' : 3 * (4 * sigma - 1) / 2 < tau := lt_of_not_ge hcut
    norm_num
    linarith

#print axioms heathBrownHighPower_scale_window
#print axioms heathBrownHighPower_companion_scale
#print axioms heathBrownHighPower_companion_scale_strong
#print axioms heathBrownHighPower_companion_huxley_range
#print axioms heathBrownHighPower_is_first

end

end GafniTao
