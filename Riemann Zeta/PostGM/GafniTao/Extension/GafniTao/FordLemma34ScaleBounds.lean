import GafniTao.FordLemma34InductionPredicate

/-!
# Ford Lemma 3.4: lower bounds for the physical `Q_i` scales

This records the first, lossless part of Ford's equation (3.9): the
restriction `i/r ≤ 9/10` leaves a positive tenth of the original exponent.
-/

namespace GafniTao

noncomputable section

theorem fordQScale_one_le_of_ten_index_le_nine_r
    {k r j i : ℕ} {delta P : ℝ}
    (Φ : FordPhiSchedule k r j delta)
    (hP : 1 ≤ P) (hr : 1 ≤ r) (hi : i ≤ j)
    (hupper : ∀ n, 1 ≤ n → n ≤ j → Φ.phi n ≤ 1 / (r : ℝ))
    (hir : 10 * i ≤ 9 * r) :
    1 ≤ fordQScale P Φ i := by
  have hrR : (0 : ℝ) < r := by exact_mod_cast (show 0 < r by omega)
  have hprefix := fordPhiPrefix_le_index_div_r Φ hupper hi
  have hirR : (10 : ℝ) * i ≤ 9 * r := by exact_mod_cast hir
  have hratio : (i : ℝ) / r ≤ 9 / 10 := by
    rw [div_le_iff₀ hrR]
    nlinarith
  have hexp : 0 ≤ 1 - fordPhiPrefix Φ i := by
    linarith
  exact Real.one_le_rpow hP hexp

theorem fordQScale_terminal_one_le
    {k r j : ℕ} {delta P : ℝ}
    (Φ : FordPhiSchedule k r j delta)
    (hP : 1 ≤ P) (hr : 1 ≤ r)
    (hupper : ∀ n, 1 ≤ n → n ≤ j → Φ.phi n ≤ 1 / (r : ℝ))
    (hjUpper : 10 * j ≤ 9 * r) :
    1 ≤ fordQScale P Φ j :=
  fordQScale_one_le_of_ten_index_le_nine_r Φ hP hr le_rfl hupper hjUpper

#print axioms fordQScale_one_le_of_ten_index_le_nine_r
#print axioms fordQScale_terminal_one_le

end

end GafniTao
