import GafniTao.HeathBrownSourceScale

/-!
# Branch-independent powered scale above the square threshold

The low and middle Heath--Brown cells power every selected detector block
whose physical length `N` satisfies `N^2 <= U`.  This file proves the exact
finite bridge for both detector labels.  The square hypothesis is deliberately
kept explicit: short Type-I blocks require the separate reflection argument.
-/

namespace GafniTao

noncomputable section

open RiemannZeta.GuthMaynard

/-- Eventually, every selected classical binary scale that lies beyond the
physical square threshold admits the literal source power
`floor (log U / log N)`.  The power is at least two, is bounded uniformly in
the detector height, brackets `U` by consecutive powers, and has the exact
cube domination required by the Heath--Brown energy input. -/
theorem eventually_heathBrown_selected_scale_two
    {delta1 delta2 : Real}
    (hdelta1 : 0 < delta1) (hdelta2 : 0 < delta2)
    (hdeltaOrder : delta2 / 2 <= delta1)
    (hdelta1Upper : delta1 <= 1) :
    exists U0 : Real, 8 <= U0 /\ forall U : Real, U0 <= U ->
      let X := Nat.floor (U ^ (delta2 / 2))
      let Y := Nat.floor (U ^ delta1)
      forall {kI kII : Nat} (q : Fin (kI * 2 + kII * 2)),
        let N := classicalBinarySelectedN Y X kI kII q
        (N : Real) ^ 2 <= U ->
        let p := heathBrownSourcePower N U
        1 < N /\ U ^ (delta2 / 4) <= (N : Real) /\
          2 <= p /\ (N : Real) ^ p <= U /\
          U < (N : Real) ^ (p + 1) /\
          U ^ 2 <= ((N : Real) ^ p) ^ 3 /\
          p <= Nat.ceil (4 / delta2) := by
  obtain ⟨Ulower, hUlower, hLower⟩ :=
    eventually_rpow_le_natFloor_rpow
      (a := delta2 / 4) (b := delta2 / 2) (by positivity) (by linarith)
  obtain ⟨Ucut, hUcut, hCut⟩ :=
    eventually_classical_dichotomy_cutoffs delta1 delta2 hdelta1 hdelta2
      hdeltaOrder hdelta1Upper
  let U0 := max Ulower Ucut
  refine ⟨U0, hUcut.trans (le_max_right _ _), ?_⟩
  intro U hU
  dsimp only
  intro kI kII q hSquare
  let X := Nat.floor (U ^ (delta2 / 2))
  let Y := Nat.floor (U ^ delta1)
  let N := classicalBinarySelectedN Y X kI kII q
  have hLowerU : Ulower <= U := (le_max_left _ _).trans hU
  have hCutU : Ucut <= U := (le_max_right _ _).trans hU
  have hCutData := hCut U hCutU
  dsimp only at hCutData
  have hUEight : 8 <= U := hUcut.trans hCutU
  have hUOne : 1 <= U := by linarith
  have hUPos : 0 < U := zero_lt_one.trans_le hUOne
  have hLowerX : U ^ (delta2 / 4) <= (X : Real) := by
    simpa only [X] using hLower U hLowerU
  have hNLowerX : X <= N := by
    exact le_classicalBinarySelectedN hCutData.2.2.1 q
  have hNLowerXReal : (X : Real) <= (N : Real) := by exact_mod_cast hNLowerX
  have hNLower : U ^ (delta2 / 4) <= (N : Real) :=
    hLowerX.trans hNLowerXReal
  have hNPowLower : (1 : Real) < U ^ (delta2 / 4) :=
    Real.one_lt_rpow (by linarith [hUEight]) (by positivity)
  have hNOne : 1 < N := by
    exact_mod_cast hNPowLower.trans_le hNLower
  have hPower := heathBrownSourcePower_spec_two hNOne hUPos hSquare
  dsimp only at hPower
  let p := heathBrownSourcePower N U
  have hlogU : 0 < Real.log U := Real.log_pos (by linarith [hUEight])
  have hlogN : 0 < Real.log (N : Real) :=
    Real.log_pos (by exact_mod_cast hNOne)
  have hLogLower : (delta2 / 4) * Real.log U <= Real.log (N : Real) := by
    have hLog := Real.log_le_log (Real.rpow_pos_of_pos hUPos _)
      (by simpa only using hNLower)
    rw [Real.log_rpow hUPos] at hLog
    exact hLog
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
  exact ⟨hNOne, hNLower, hPower.1, hPower.2.1, hPower.2.2.1,
    hPower.2.2.2, hpBound⟩

#print axioms eventually_heathBrown_selected_scale_two

end

end GafniTao
