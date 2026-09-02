import GafniTao.FordLemma36FinalExponent

/-!
# Ford Lemma 3.6: the branch below `Delta = k`

Ford dispatches the complementary branch of Lemma 3.6 in one sentence.  The
rounded choice is then exactly `r = k`; the canonical `phi` schedule makes the
next permissible exponent contract by the factor `1 - 1/k`.  This file keeps
that argument explicit, including positivity of the next exponent.
-/

namespace GafniTao

noncomputable section

theorem fordR36_eq_k_of_pos_le
    {k : ℕ} {delta : ℝ} (hk : 26 ≤ k)
    (hdeltaPos : 0 < delta) (hdeltaUpper : delta ≤ k) :
    fordR36 k delta = k := by
  have hkR : (0 : ℝ) < k := by positivity
  let x : ℝ := (k : ℝ) - delta / k + 1
  have hdivPos : 0 < delta / (k : ℝ) := div_pos hdeltaPos hkR
  have hdivUpper : delta / (k : ℝ) ≤ 1 :=
    (div_le_one hkR).2 (by simpa using hdeltaUpper)
  have hx0 : 0 ≤ x := by
    dsimp [x]
    have hk26 : (26 : ℝ) ≤ k := by exact_mod_cast hk
    linarith
  change ⌊x⌋₊ = k
  apply Nat.le_antisymm
  · have hlt : ⌊x⌋₊ < k + 1 := by
      rw [Nat.floor_lt hx0]
      dsimp [x]
      norm_num [Nat.cast_add, Nat.cast_one]
      linarith
    omega
  · apply (Nat.le_floor_iff hx0).2
    dsimp [x]
    linarith

theorem fordDeltaZero35_below_contracts
    {k : ℕ} {delta : ℝ} (hk : 1000 ≤ k)
    (hdeltaPos : 0 < delta) (hdeltaUpper : delta ≤ k) :
    0 < fordDeltaZero35 k (fordR36 k delta) delta ∧
      fordDeltaZero35 k (fordR36 k delta) delta ≤
        delta * (1 - 1 / (k : ℝ)) := by
  have hk26 : 26 ≤ k := by omega
  have hkR : (0 : ℝ) < k := by positivity
  have hrEq := fordR36_eq_k_of_pos_le hk26 hdeltaPos hdeltaUpper
  let j := fordJ35 k k delta
  let Φ := fordCanonicalPhiSchedule k k j delta
  have hy : 0 ≤ fordY35 k k delta := by
    simp [fordY35]
    linarith
  have hj := fordJ35_admissible (k := k) (r := k) (delta := delta)
    (by omega) hy
  have h38y : (((j - 1) * (j - 2) : ℕ) : ℝ) ≤ fordY35 k k delta := by
    simpa [j] using hj.2
  have hdeltaRange : 2 * delta ≤ (k : ℝ) ^ 2 - k := by
    have hk1000 : (1000 : ℝ) ≤ k := by exact_mod_cast hk
    nlinarith
  have hstarLower : 1 / (((k + 1 : ℕ) : ℝ)) ≤
      fordPhiStar35 k k delta := by
    unfold fordPhiStar35 fordY35
    rw [div_le_div_iff₀ (by positivity : (0 : ℝ) < ((k + 1 : ℕ) : ℝ))
      (by positivity : (0 : ℝ) < 2 * (k : ℝ) * k +
        (2 * delta - ((k : ℝ) - k) * ((k : ℝ) - k + 1)))]
    push_cast
    nlinarith
  have hphiLowerCanonical := fordCanonicalPhiSchedule_lower
    (k := k) (r := k) (j := j) (delta := delta)
    (by omega) (by omega) h38y hdeltaRange hstarLower
  have hphiLowerAll : ∀ i, 1 ≤ i → i ≤ j →
      1 / (((k + 1 : ℕ) : ℝ)) ≤ Φ.phi i := by
    simpa [Φ] using hphiLowerCanonical
  have h38source := fordJ35_equation_3_8
    (k := k) (r := k) (delta := delta) (by omega) le_rfl hy
  have hphiUpperAll := FordPhiSchedule.le_inv_r Φ
    (by omega) (by omega) le_rfl hj.1 h38source hphiLowerAll
  have hjOne : 1 ≤ j := by
    have : 1 ≤ fordJ35 k k delta := by omega
    simpa [j] using this
  have hphiUpper : Φ.phi 1 ≤ 1 / (k : ℝ) :=
    hphiUpperAll 1 (by omega) hjOne
  have hstarPhiCanonical := fordCanonicalPhiSchedule_phiStar_le
    (k := k) (r := k) (j := j) (delta := delta)
    (by omega) (by omega) h38y hdeltaRange 1 (by omega)
      hjOne
  have hstarPhi : fordPhiStar35 k k delta ≤ Φ.phi 1 := by
    simpa [Φ] using hstarPhiCanonical
  have hfactor : 0 ≤ (k : ℝ) ^ 2 - delta := by
    have hk1000 : (1000 : ℝ) ≤ k := by exact_mod_cast hk
    nlinarith
  have hupperMul := mul_le_mul_of_nonneg_right hphiUpper hfactor
  have hlowerMul := mul_le_mul_of_nonneg_right hstarPhi hfactor
  have hbaseEq :
      delta - k + fordPhiStar35 k k delta * ((k : ℝ) ^ 2 - delta) =
        delta * ((k : ℝ) ^ 2 + delta - 2 * k) /
          ((k : ℝ) ^ 2 + delta) := by
    unfold fordPhiStar35 fordY35
    norm_num
    field_simp
    ring
  have hbasePos :
      0 < delta - k + fordPhiStar35 k k delta *
        ((k : ℝ) ^ 2 - delta) := by
    rw [hbaseEq]
    have hk1000 : (1000 : ℝ) ≤ k := by exact_mod_cast hk
    have hnumPos : 0 < (k : ℝ) ^ 2 + delta - 2 * k := by nlinarith
    exact div_pos (mul_pos hdeltaPos hnumPos) (by positivity)
  have hsource :
      fordDeltaZero35 k k delta =
        delta - k + Φ.phi 1 * ((k : ℝ) ^ 2 - delta) := by
    rw [fordDeltaZero35_eq]
    simp only [Φ, j]
    unfold fordDeltaPrime34
    ring
  rw [hrEq, hsource]
  constructor
  · linarith
  · calc
      delta - k + Φ.phi 1 * ((k : ℝ) ^ 2 - delta) ≤
          delta - k + (1 / (k : ℝ)) * ((k : ℝ) ^ 2 - delta) := by
        linarith
      _ = delta * (1 - 1 / (k : ℝ)) := by
        field_simp
        ring

theorem fordLemma36_target_ge_contracted_k
    {k N : ℕ} (hk : 1000 ≤ k)
    (hN : (N : ℝ) ≤
      (k : ℝ) / 2 * (1 / 2 + Real.log (3 * (k : ℝ) / 8)) + 1) :
    (k : ℝ) * (1 - 1 / (k : ℝ)) ≤
      (3 / 8 : ℝ) * (k : ℝ) ^ 2 * Real.exp
        (1 / 2 - 2 * (N : ℝ) / (k : ℝ) +
          169 / (100 * (k : ℝ))) := by
  have hkR : (0 : ℝ) < k := by positivity
  have harg : 0 < 3 * (k : ℝ) / 8 := by positivity
  have hexponent :
      -Real.log (3 * (k : ℝ) / 8) - 31 / (100 * (k : ℝ)) ≤
        1 / 2 - 2 * (N : ℝ) / (k : ℝ) +
          169 / (100 * (k : ℝ)) := by
    have hscaled := mul_le_mul_of_nonneg_left hN (show 0 ≤ 2 / (k : ℝ) by positivity)
    have hleft : (2 / (k : ℝ)) * (N : ℝ) =
        2 * (N : ℝ) / (k : ℝ) := by ring
    have hright : (2 / (k : ℝ)) *
        ((k : ℝ) / 2 * (1 / 2 + Real.log (3 * (k : ℝ) / 8)) + 1) =
          1 / 2 + Real.log (3 * (k : ℝ) / 8) + 2 / (k : ℝ) := by
      field_simp
    rw [hleft, hright] at hscaled
    calc
      -Real.log (3 * (k : ℝ) / 8) - 31 / (100 * (k : ℝ)) =
          1 / 2 -
            (1 / 2 + Real.log (3 * (k : ℝ) / 8) + 2 / (k : ℝ)) +
              169 / (100 * (k : ℝ)) := by
        field_simp
        ring
      _ ≤ 1 / 2 - 2 * (N : ℝ) / (k : ℝ) +
          169 / (100 * (k : ℝ)) := by linarith
  have hlinear :
      1 - 1 / (k : ℝ) ≤ 1 - 31 / (100 * (k : ℝ)) := by
    have : 31 / (100 * (k : ℝ)) ≤ 1 / (k : ℝ) := by
      calc
        31 / (100 * (k : ℝ)) = (31 / 100 : ℝ) / (k : ℝ) := by ring
        _ ≤ 1 / (k : ℝ) := div_le_div_of_nonneg_right (by norm_num) hkR.le
    linarith
  have hexpSmall :
      1 - 1 / (k : ℝ) ≤ Real.exp (-31 / (100 * (k : ℝ))) := by
    refine hlinear.trans ?_
    calc
      1 - 31 / (100 * (k : ℝ)) =
          -31 / (100 * (k : ℝ)) + 1 := by ring
      _ ≤ Real.exp (-31 / (100 * (k : ℝ))) :=
        Real.add_one_le_exp (-31 / (100 * (k : ℝ)))
  calc
    (k : ℝ) * (1 - 1 / (k : ℝ)) ≤
        (k : ℝ) * Real.exp (-31 / (100 * (k : ℝ))) := by gcongr
    _ = (3 / 8 : ℝ) * (k : ℝ) ^ 2 *
        Real.exp (-Real.log (3 * (k : ℝ) / 8) -
          31 / (100 * (k : ℝ))) := by
      rw [Real.exp_sub, Real.exp_neg, Real.exp_log harg]
      field_simp
      rw [← Real.exp_add]
      convert Real.exp_zero using 1
      ring_nf
    _ ≤ (3 / 8 : ℝ) * (k : ℝ) ^ 2 * Real.exp
        (1 / 2 - 2 * (N : ℝ) / (k : ℝ) +
          169 / (100 * (k : ℝ))) := by
      gcongr

theorem fordLemma36_delta_exponent_of_prev_below
    {k m : ℕ} (hk : 1000 ≤ k)
    (hprevPos : 0 < fordDeltaSequence36 k m)
    (hprevUpper : fordDeltaSequence36 k m ≤ k)
    (hN : (((m + 2 : ℕ) : ℝ)) ≤
      (k : ℝ) / 2 * (1 / 2 + Real.log (3 * (k : ℝ) / 8)) + 1) :
    fordDeltaSequence36 k (m + 1) ≤
      (3 / 8 : ℝ) * (k : ℝ) ^ 2 * Real.exp
        (1 / 2 - 2 * (((m + 2 : ℕ) : ℝ)) / (k : ℝ) +
          169 / (100 * (k : ℝ))) := by
  have hstep := (fordDeltaZero35_below_contracts hk hprevPos hprevUpper).2
  have hstep' : fordDeltaSequence36 k (m + 1) ≤
      fordDeltaSequence36 k m * (1 - 1 / (k : ℝ)) := by
    simpa [fordDeltaSequence36_succ, fordRSequence36] using hstep
  have hfactor : 0 ≤ 1 - 1 / (k : ℝ) := by
    have hkR : (1 : ℝ) ≤ k := by exact_mod_cast (show 1 ≤ k by omega)
    exact sub_nonneg.mpr ((div_le_one (by positivity : (0 : ℝ) < k)).2 hkR)
  have hscale := mul_le_mul_of_nonneg_right hprevUpper hfactor
  exact hstep'.trans (hscale.trans (fordLemma36_target_ge_contracted_k hk hN))

theorem fordDeltaSequence36_pos_le_of_pos_le
    {k m n : ℕ} (hk : 1000 ≤ k) (hmn : m ≤ n)
    (hmPos : 0 < fordDeltaSequence36 k m)
    (hmUpper : fordDeltaSequence36 k m ≤ k) :
    0 < fordDeltaSequence36 k n ∧ fordDeltaSequence36 k n ≤ k := by
  induction n, hmn using Nat.le_induction with
  | base => exact ⟨hmPos, hmUpper⟩
  | succ n hmn ih =>
      have hstep := fordDeltaZero35_below_contracts hk ih.1 ih.2
      have hnextPos : 0 < fordDeltaSequence36 k (n + 1) := by
        simpa [fordDeltaSequence36_succ, fordRSequence36] using hstep.1
      have hfactor : 0 ≤ 1 - 1 / (k : ℝ) ∧ 1 - 1 / (k : ℝ) ≤ 1 := by
        constructor
        · have hkR : (1 : ℝ) ≤ k := by exact_mod_cast (show 1 ≤ k by omega)
          exact sub_nonneg.mpr ((div_le_one (by positivity : (0 : ℝ) < k)).2 hkR)
        · have : 0 ≤ 1 / (k : ℝ) := by positivity
          linarith
      have hnextUpperPrev : fordDeltaSequence36 k (n + 1) ≤
          fordDeltaSequence36 k n := by
        calc
          fordDeltaSequence36 k (n + 1) ≤
              fordDeltaSequence36 k n * (1 - 1 / (k : ℝ)) := by
            simpa [fordDeltaSequence36_succ, fordRSequence36] using hstep.2
          _ ≤ fordDeltaSequence36 k n := by
            nlinarith [mul_nonneg ih.1.le hfactor.1]
      exact ⟨hnextPos, hnextUpperPrev.trans ih.2⟩

#print axioms fordR36_eq_k_of_pos_le
#print axioms fordDeltaZero35_below_contracts
#print axioms fordLemma36_target_ge_contracted_k
#print axioms fordLemma36_delta_exponent_of_prev_below
#print axioms fordDeltaSequence36_pos_le_of_pos_le

end

end GafniTao
