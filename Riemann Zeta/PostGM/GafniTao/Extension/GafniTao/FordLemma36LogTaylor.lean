import GafniTao.FordLemma36Lower

/-!
# Ford Lemma 3.6: logarithmic Taylor inequalities

These are the two one-sided Taylor estimates used in Ford's passage from
equation (3.14) to the logarithmic potential recurrence.  They are proved on
their full source ranges, with the logarithm differentiated directly.
-/

namespace GafniTao

noncomputable section

theorem log_one_sub_le_cubic {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) :
    Real.log (1 - x) ≤ -x - x ^ 2 / 2 - x ^ 3 / 3 := by
  let f : ℝ → ℝ :=
    fun y => -y - y ^ 2 / 2 - y ^ 3 / 3 - Real.log (1 - y)
  have hderiv : ∀ y ∈ Set.Icc (0 : ℝ) x,
      HasDerivAt f (y ^ 3 / (1 - y)) y := by
    intro y hy
    have hy1 : y < 1 := lt_of_le_of_lt hy.2 hx1
    have hlog : HasDerivAt (fun z : ℝ => Real.log (1 - z))
        (-1 / (1 - y)) y := by
      have hn : ((fun z : ℝ => 1 - z) y) ≠ 0 := by
        simp only
        linarith
      simpa only [Pi.sub_apply, id_eq, zero_sub, one_div, neg_mul, one_mul] using
        (((hasDerivAt_const y (1 : ℝ)).sub (hasDerivAt_id y)).log hn)
    convert ((((hasDerivAt_id y).neg.sub
        ((hasDerivAt_pow 2 y).div_const 2)).sub
          ((hasDerivAt_pow 3 y).div_const 3)).sub hlog) using 1
    field_simp [ne_of_gt (sub_pos.mpr hy1)]
    ring
  have hmono : MonotoneOn f (Set.Icc 0 x) :=
    monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 x)
      (fun y hy => (hderiv y hy).continuousAt.continuousWithinAt)
      (fun y hy => (hderiv y (interior_subset hy)).hasDerivWithinAt)
      (by
        intro y hy
        simp only [interior_Icc, Set.mem_Ioo] at hy
        have hy1 : y < 1 := lt_of_lt_of_le hy.2 hx1.le
        exact div_nonneg (pow_nonneg hy.1.le 3) (sub_nonneg.mpr hy1.le))
  have h := hmono (show 0 ∈ Set.Icc (0 : ℝ) x by exact ⟨le_rfl, hx0⟩)
    (show x ∈ Set.Icc (0 : ℝ) x by exact ⟨hx0, le_rfl⟩) hx0
  simpa [f] using h

theorem log_one_add_le_cubic {x : ℝ} (hx0 : 0 ≤ x) :
    Real.log (1 + x) ≤ x - x ^ 2 / 2 + x ^ 3 / 3 := by
  let f : ℝ → ℝ := fun y => y - y ^ 2 / 2 + y ^ 3 / 3 - Real.log (1 + y)
  have hderiv : ∀ y ∈ Set.Icc (0 : ℝ) x,
      HasDerivAt f (y ^ 3 / (1 + y)) y := by
    intro y hy
    have hypos : 0 < 1 + y := by linarith [hy.1]
    have hlog : HasDerivAt (fun z : ℝ => Real.log (1 + z))
        (1 / (1 + y)) y := by
      have hn : ((fun z : ℝ => 1 + z) y) ≠ 0 := by
        simp only
        linarith
      simpa only [Pi.add_apply, id_eq, zero_add, one_div, one_mul] using
        (((hasDerivAt_const y (1 : ℝ)).add (hasDerivAt_id y)).log hn)
    convert ((((hasDerivAt_id y).sub
        ((hasDerivAt_pow 2 y).div_const 2)).add
          ((hasDerivAt_pow 3 y).div_const 3)).sub hlog) using 1
    field_simp [hypos.ne']
    ring
  have hmono : MonotoneOn f (Set.Icc 0 x) :=
    monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 x)
      (fun y hy => (hderiv y hy).continuousAt.continuousWithinAt)
      (fun y hy => (hderiv y (interior_subset hy)).hasDerivWithinAt)
      (by
        intro y hy
        simp only [interior_Icc, Set.mem_Ioo] at hy
        exact div_nonneg (pow_nonneg hy.1.le 3) (by linarith [hy.1]))
  have h := hmono (show 0 ∈ Set.Icc (0 : ℝ) x by exact ⟨le_rfl, hx0⟩)
    (show x ∈ Set.Icc (0 : ℝ) x by exact ⟨hx0, le_rfl⟩) hx0
  simpa [f] using h

#print axioms log_one_sub_le_cubic
#print axioms log_one_add_le_cubic

end

end GafniTao
