import GafniTao.Pintz2023LogScale

/-!
# Pintz (2023), equations (4.15)--(4.16): bounded power choice

This file formalizes the two cases in the paragraph following equation
(4.15).  The smallness reserve on `epsilon` is explicit; it is later derived
when the single source perturbation is chosen.
-/

namespace GafniTao

noncomputable section

noncomputable def pintz2023EllThreshold
    (eta epsilon : ℝ) (ell : ℕ) : ℝ :=
  1 / pintzEllDenominator eta epsilon ell

noncomputable def pintz2023EllPowerWindowUpper
    (eta epsilon : ℝ) (ell : ℕ) : ℝ :=
  (3 / 2 : ℝ) * pintz2023EllThreshold eta epsilon ell +
    epsilon / (20 * (ell : ℝ))

/-- Under the explicit source smallness reserve, the perturbed ell-threshold
is less than `5/(3 ell)`. -/
theorem pintz2023EllThreshold_lt_five_thirds
    {eta epsilon : ℝ} {k ell : ℕ}
    (hcell : PintzCell eta k ell)
    (hepsilonSmall : 6 * (ell : ℝ) * epsilon < 1 / 15) :
    pintz2023EllThreshold eta epsilon ell < 5 / (3 * (ell : ℝ)) := by
  have hell : 3 ≤ ell := hcell.2.1
  have hellReal : (0 : ℝ) < ell := by exact_mod_cast (show 0 < ell by omega)
  have hellThree : (3 : ℝ) ≤ ell := by exact_mod_cast hell
  have hcellEll :
      2 * eta * (ell : ℝ) * ((ell : ℝ) - 1) < 1 := by
    simpa using hcell.2.2.2.2.1
  have hcore :
      2 * eta * ((ell : ℝ) - 1) < 1 / (ell : ℝ) := by
    rw [lt_div_iff₀ hellReal]
    nlinarith
  have hinv : 1 / (ell : ℝ) ≤ 1 / 3 := by
    rw [div_le_div_iff₀ hellReal (by norm_num : (0 : ℝ) < 3)]
    nlinarith
  have hparen : (3 / 5 : ℝ) <
      1 - 2 * eta * ((ell : ℝ) - 1) - 6 * (ell : ℝ) * epsilon := by
    nlinarith
  have hdenLower : 3 * (ell : ℝ) / 5 <
      pintzEllDenominator eta epsilon ell := by
    have hmul := mul_lt_mul_of_pos_left hparen hellReal
    unfold pintzEllDenominator
    nlinarith
  have hbasePos : 0 < 3 * (ell : ℝ) / 5 := by positivity
  have hinvStrict := one_div_lt_one_div_of_lt hbasePos hdenLower
  unfold pintz2023EllThreshold
  calc
    1 / pintzEllDenominator eta epsilon ell <
        1 / (3 * (ell : ℝ) / 5) := hinvStrict
    _ = 5 / (3 * (ell : ℝ)) := by field_simp

/-- Exact two-case choice of the power following Pintz (4.15).  The first
alternative is literal squaring; the second lands in `J_ell(eta)`. -/
theorem exists_pintz2023_power_choice
    {eta epsilon u : ℝ} {k ell : ℕ}
    (hcell : PintzCell eta k ell)
    (hepsilon : 0 < epsilon) (hepsilonUpper : epsilon ≤ 1)
    (hepsilonSmall : 6 * (ell : ℝ) * epsilon < 1 / 15)
    (huLower : epsilon / (11 * (ell : ℝ)) < u)
    (huUpper : u < pintz2023EllThreshold eta epsilon ell) :
    ∃ h : ℕ,
      2 ≤ h ∧ (h : ℝ) < 20 / epsilon ∧
      pintz2023EllThreshold eta epsilon ell < (h : ℝ) * u ∧
      (h = 2 ∨
        (h : ℝ) * u < pintz2023EllPowerWindowUpper eta epsilon ell) := by
  have hell : 0 < ell := lt_of_lt_of_le (by omega) hcell.2.1
  have hellReal : (0 : ℝ) < ell := by exact_mod_cast hell
  have hthresholdUpper :=
    pintz2023EllThreshold_lt_five_thirds hcell hepsilonSmall
  have hthresholdPos : 0 < pintz2023EllThreshold eta epsilon ell := by
    unfold pintz2023EllThreshold
    apply one_div_pos.mpr
    apply pintzEllDenominator_pos hell
    have hbase :
        2 * eta * (ell : ℝ) * ((ell : ℝ) - 1) < 1 := by
      simpa using hcell.2.2.2.2.1
    have hcore :
        2 * eta * ((ell : ℝ) - 1) < 1 / (ell : ℝ) := by
      rw [lt_div_iff₀ hellReal]
      nlinarith
    have hinv : 1 / (ell : ℝ) ≤ 1 / 3 := by
      rw [div_le_div_iff₀ hellReal (by norm_num : (0 : ℝ) < 3)]
      have : (3 : ℝ) ≤ ell := by exact_mod_cast hcell.2.1
      nlinarith
    nlinarith
  have huPos : 0 < u := by
    have : 0 < epsilon / (11 * (ell : ℝ)) := by positivity
    linarith
  have htwenty : (2 : ℝ) < 20 / epsilon := by
    rw [lt_div_iff₀ hepsilon]
    nlinarith
  by_cases hsquare :
      pintz2023EllThreshold eta epsilon ell +
          epsilon / (10 * (ell : ℝ)) ≤ 2 * u
  · refine ⟨2, by omega, by simpa using htwenty, ?_, Or.inl rfl⟩
    have hmargin : 0 < epsilon / (10 * (ell : ℝ)) := by positivity
    norm_num
    linarith
  · have htwoUpper : 2 * u <
        pintz2023EllThreshold eta epsilon ell +
          epsilon / (10 * (ell : ℝ)) := lt_of_not_ge hsquare
    have hepsilonSplit : epsilon / (10 * (ell : ℝ)) =
        2 * (epsilon / (20 * (ell : ℝ))) := by
      field_simp
      ring
    have huWindow : u <
        pintz2023EllThreshold eta epsilon ell / 2 +
          epsilon / (20 * (ell : ℝ)) := by
      rw [hepsilonSplit] at htwoUpper
      nlinarith
    obtain ⟨h, hhOne, hhLower, hhMinimal⟩ :=
      exists_positive_nat_power_minimal hthresholdPos.le huPos
    have hhTwo : 2 ≤ h := by
      by_contra hnot
      have hhLe : h ≤ 1 := Nat.le_of_lt_succ (lt_of_not_ge hnot)
      have : h = 1 := Nat.le_antisymm hhLe hhOne
      subst h
      norm_num at hhLower
      exact (not_lt_of_ge huUpper.le) hhLower
    have hhWindow : (h : ℝ) * u <
        pintz2023EllPowerWindowUpper eta epsilon ell := by
      unfold pintz2023EllPowerWindowUpper
      calc
        (h : ℝ) * u ≤ pintz2023EllThreshold eta epsilon ell + u := hhMinimal
        _ < pintz2023EllThreshold eta epsilon ell +
            (pintz2023EllThreshold eta epsilon ell / 2 +
              epsilon / (20 * (ell : ℝ))) :=
          by linarith
        _ = (3 / 2 : ℝ) * pintz2023EllThreshold eta epsilon ell +
            epsilon / (20 * (ell : ℝ)) := by ring
    have hfactorPos : 0 < 20 / epsilon - 1 := by
      rw [sub_pos, lt_div_iff₀ hepsilon]
      nlinarith
    have hnumeric :
        5 / (3 * (ell : ℝ)) <
          (20 / epsilon - 1) *
            (epsilon / (11 * (ell : ℝ))) := by
      field_simp [hepsilon.ne', hellReal.ne']
      nlinarith
    have hfactorLower :
        pintz2023EllThreshold eta epsilon ell <
          (20 / epsilon - 1) * u := by
      have hmul := mul_lt_mul_of_pos_left huLower hfactorPos
      exact hthresholdUpper.trans (hnumeric.trans hmul)
    have hsum :
        pintz2023EllThreshold eta epsilon ell + u <
          (20 / epsilon) * u := by
      calc
        pintz2023EllThreshold eta epsilon ell + u <
            (20 / epsilon - 1) * u + u :=
          by linarith
        _ = (20 / epsilon) * u := by ring
    have hhProduct : (h : ℝ) * u < (20 / epsilon) * u :=
      hhMinimal.trans_lt hsum
    have hhBound : (h : ℝ) < 20 / epsilon := by
      nlinarith
    exact ⟨h, hhTwo, hhBound, hhLower, Or.inr hhWindow⟩

#print axioms pintz2023EllThreshold_lt_five_thirds
#print axioms exists_pintz2023_power_choice

end

end GafniTao
