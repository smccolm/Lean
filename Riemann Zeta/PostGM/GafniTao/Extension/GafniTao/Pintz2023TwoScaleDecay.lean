import GafniTao.Pintz2023Equation420Arithmetic

/-!
# Two-scale decay for Pintz equation (4.20)

The powered block has two simultaneous lower bounds: one from its critical
`T`-scale and one from the local-frequency branch.  This elementary lemma
combines them without comparing a negative power of the local frequency in
the wrong direction.
-/

namespace GafniTao

noncomputable section

/-- If `N` dominates both `S^a` and `x^b`, interpolation gives the displayed
power saving whenever the combined exponent has a strict reserve. -/
theorem two_scale_rpow_decay
    {N x S a b p q d : ℝ}
    (hx : 1 ≤ x) (hS : 1 ≤ S)
    (ha : 0 < a) (hb : 0 < b) (hp : 0 ≤ p)
    (hq : 0 < q) (hd : 0 < d)
    (hSScale : S ^ a ≤ N) (hxScale : x ^ b ≤ N)
    (hexponent : a * (p / b - q) ≤ -d) :
    N ^ (-q) * x ^ p ≤ S ^ (-d) := by
  have hxPos : 0 < x := zero_lt_one.trans_le hx
  have hSPos : 0 < S := zero_lt_one.trans_le hS
  have habPos : 0 < a / b := div_pos ha hb
  have heNeg : p - b * q < 0 := by
    have hinside : p / b - q < 0 := by
      by_contra hnot
      have : 0 ≤ p / b - q := le_of_not_gt hnot
      have : 0 ≤ a * (p / b - q) := mul_nonneg ha.le this
      linarith
    have hmul := mul_lt_mul_of_pos_left hinside hb
    field_simp [hb.ne'] at hmul
    nlinarith
  by_cases hsmall : x ≤ S ^ (a / b)
  · have hNPower :
        N ^ (-q) ≤ (S ^ a) ^ (-q) :=
      Real.rpow_le_rpow_of_nonpos
        (Real.rpow_pos_of_pos hSPos a) hSScale (by linarith)
    have hxPower : x ^ p ≤ (S ^ (a / b)) ^ p :=
      Real.rpow_le_rpow hxPos.le hsmall hp
    calc
      N ^ (-q) * x ^ p ≤
          (S ^ a) ^ (-q) * (S ^ (a / b)) ^ p :=
        mul_le_mul hNPower hxPower
          (Real.rpow_nonneg hxPos.le p)
          (Real.rpow_nonneg (Real.rpow_nonneg hSPos.le a) (-q))
      _ = S ^ (a * (-q) + (a / b) * p) := by
        rw [← Real.rpow_mul hSPos.le, ← Real.rpow_mul hSPos.le,
          ← Real.rpow_add hSPos]
      _ = S ^ (a * (p / b - q)) := by
        congr 1
        field_simp [hb.ne']
        ring_nf
      _ ≤ S ^ (-d) :=
        Real.rpow_le_rpow_of_exponent_le hS hexponent
  · have hlarge : S ^ (a / b) ≤ x := le_of_not_ge hsmall
    have hNPower : N ^ (-q) ≤ (x ^ b) ^ (-q) :=
      Real.rpow_le_rpow_of_nonpos
        (Real.rpow_pos_of_pos hxPos b) hxScale (by linarith)
    have hcombine :
        (x ^ b) ^ (-q) * x ^ p = x ^ (p - b * q) := by
      rw [← Real.rpow_mul hxPos.le, ← Real.rpow_add hxPos]
      congr 1
      ring_nf
    have hreverse :
        x ^ (p - b * q) ≤
          (S ^ (a / b)) ^ (p - b * q) :=
      Real.rpow_le_rpow_of_nonpos
        (Real.rpow_pos_of_pos hSPos (a / b)) hlarge heNeg.le
    calc
      N ^ (-q) * x ^ p ≤ (x ^ b) ^ (-q) * x ^ p := by
        exact mul_le_mul_of_nonneg_right hNPower
          (Real.rpow_nonneg hxPos.le p)
      _ = x ^ (p - b * q) := hcombine
      _ ≤ (S ^ (a / b)) ^ (p - b * q) := hreverse
      _ = S ^ (a * (p / b - q)) := by
        rw [← Real.rpow_mul hSPos.le]
        congr 1
        field_simp [hb.ne']
      _ ≤ S ^ (-d) :=
        Real.rpow_le_rpow_of_exponent_le hS hexponent

/-- Correct two-scale form of Pintz (4.20).  The critical-scale lower bound
and the local-frequency branch are both explicit; neither is silently
replaced by an ambient-height comparison. -/
theorem pintz2023_equation420_two_scale_decay
    {eta target S x N : ℝ} {k ell : ℕ}
    (hcell : PintzCell eta k ell)
    (data : Pintz2023PowerMarginData eta target k ell)
    (hx : 1 ≤ x) (hS : 1 ≤ S)
    (hCritical :
      S ^ pintz2023EllThreshold eta data.epsilon ell ≤ N)
    (hFrequency : x ^ (19 / (10 * (ell : ℝ))) ≤ N) :
    N ^ (-4 * eta) *
        x ^ pintz2023NearOneGramExponent eta eta data.epsilon ≤
      S ^ (-data.epsilon / (k : ℝ)) := by
  have heta : 0 < eta := pintzCell_eta_pos hcell
  have hk : 0 < k := lt_of_lt_of_le (by omega) hcell.1
  have hell : 0 < ell := lt_of_lt_of_le (by omega) hcell.2.1
  have hkReal : (0 : ℝ) < k := by exact_mod_cast hk
  have hellReal : (0 : ℝ) < ell := by exact_mod_cast hell
  let a : ℝ := pintz2023EllThreshold eta data.epsilon ell
  let b : ℝ := 19 / (10 * (ell : ℝ))
  let p : ℝ := pintz2023NearOneGramExponent eta eta data.epsilon
  let q : ℝ := 4 * eta
  let d : ℝ := data.epsilon / (k : ℝ)
  have hDenPos : 0 < pintzEllDenominator eta data.epsilon ell :=
    pintzEllDenominator_pos hell data.ell_margin
  have hDenLt :
      pintzEllDenominator eta data.epsilon ell < (ell : ℝ) := by
    unfold pintzEllDenominator
    have hellOneNat : 1 ≤ ell := le_trans (by omega) hcell.2.1
    have hellOne : (1 : ℝ) ≤ ell := by exact_mod_cast hellOneNat
    have hellGtOneNat : 1 < ell := lt_of_lt_of_le (by omega) hcell.2.1
    have hellGtOne : (1 : ℝ) < ell := by
      exact_mod_cast hellGtOneNat
    have hEtaTerm : 0 < 2 * eta * ((ell : ℝ) - 1) :=
      mul_pos (mul_pos (by norm_num) heta) (sub_pos.mpr hellGtOne)
    have hEpsilonTerm : 0 < 6 * (ell : ℝ) * data.epsilon :=
      mul_pos (mul_pos (by norm_num) hellReal) data.epsilon_pos
    nlinarith
  have haLower : 1 / (ell : ℝ) < a := by
    dsimp only [a, pintz2023EllThreshold]
    exact one_div_lt_one_div_of_lt hDenPos hDenLt
  have ha : 0 < a := (by positivity : 0 < 1 / (ell : ℝ)).trans haLower
  have hb : 0 < b := by dsimp only [b]; positivity
  have hp : 0 ≤ p := by
    dsimp only [p, pintz2023NearOneGramExponent,
      pintz2023NearOneGramMaxDistance]
    exact add_nonneg
      (mul_nonneg (by norm_num) (Real.rpow_nonneg (by positivity) _))
      data.epsilon_pos.le
  have hq : 0 < q := by dsimp only [q]; positivity
  have hd : 0 < d := by
    dsimp only [d]
    exact div_pos data.epsilon_pos hkReal
  have hmargin := pintz2023_equation420_exponent_margin
    hcell data.equation420_small
  have hmargin' :
      (10 * (ell : ℝ) / 19) *
          ((1 / 2 : ℝ) * (6 * eta) ^ (3 / 2 : ℝ) + data.epsilon) +
        (ell : ℝ) * (data.epsilon / (k : ℝ)) < 4 * eta := by
    convert hmargin using 1
    ring_nf
  have hpShape :
      p = (1 / 2 : ℝ) * (6 * eta) ^ (3 / 2 : ℝ) +
        data.epsilon := by
    dsimp only [p, pintz2023NearOneGramExponent,
      pintz2023NearOneGramMaxDistance]
    congr 2
    ring_nf
  have hbInv : 1 / b = 10 * (ell : ℝ) / 19 := by
    dsimp only [b]
    field_simp [hellReal.ne']
  have hbInv' : b⁻¹ = 10 * (ell : ℝ) / 19 := by
    simpa only [one_div] using hbInv
  have hinside : p / b - q < -(ell : ℝ) * d := by
    calc
      p / b - q =
          (10 * (ell : ℝ) / 19) *
              ((1 / 2 : ℝ) * (6 * eta) ^ (3 / 2 : ℝ) +
                data.epsilon) - 4 * eta := by
        dsimp only [q]
        rw [div_eq_mul_inv, hbInv', hpShape]
        ring_nf
      _ < -(ell : ℝ) * (data.epsilon / (k : ℝ)) := by
        linarith
      _ = -(ell : ℝ) * d := by rfl
  have hinsideNeg : p / b - q < 0 := by
    have : 0 < (ell : ℝ) * d := mul_pos hellReal hd
    linarith
  have hexponent : a * (p / b - q) ≤ -d := by
    have hmul := mul_lt_mul_of_neg_right haLower hinsideNeg
    have hdiv : (1 / (ell : ℝ)) *
        (-(ell : ℝ) * d) = -d := by field_simp
    exact (calc
      a * (p / b - q) <
          (1 / (ell : ℝ)) * (p / b - q) := hmul
      _ < (1 / (ell : ℝ)) * (-(ell : ℝ) * d) := by
        exact mul_lt_mul_of_pos_left hinside (by positivity)
      _ = -d := hdiv).le
  simpa only [p, q, d, neg_mul, neg_div] using
    (two_scale_rpow_decay hx hS ha hb hp hq hd
    (by simpa only [a] using hCritical)
    (by simpa only [b] using hFrequency) hexponent)

#print axioms two_scale_rpow_decay
#print axioms pintz2023_equation420_two_scale_decay

end

end GafniTao
