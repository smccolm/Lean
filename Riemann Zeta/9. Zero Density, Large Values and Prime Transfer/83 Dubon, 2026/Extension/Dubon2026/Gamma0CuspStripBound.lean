import Dubon2026.Gamma0CuspEntire
import Dubon2026.LatticeCuspStripBound

/-! # Polynomial strip growth of the actual completed general-level Rankin integral -/

namespace Dubon2026

open CongruenceSubgroup Matrix.SpecialLinearGroup

noncomputable section

/-- The finite Möbius lattice coefficient has a uniform real-power bound on a closed spectral strip. -/
theorem norm_gamma0LatticeCoefficient_le (Q : ℕ) (hQ : 0 < Q) (d : Q.divisors)
    {s : ℂ} {σ : ℝ} (hs : 1 - s.re ≤ σ) :
    ‖(ArithmeticFunction.moebius d.val : ℂ) * ((Q : ℂ) * d.val) ^ (-s)‖ ≤
      ‖(ArithmeticFunction.moebius d.val : ℂ)‖ * ((Q * d.val : ℕ) : ℝ) ^ σ := by
  have hn : 0 < Q * d.val := Nat.mul_pos hQ (Nat.pos_of_mem_divisors d.property)
  rw [norm_mul, ← Nat.cast_mul, ← Complex.ofReal_natCast,
    Complex.norm_cpow_eq_rpow_re_of_pos (Nat.cast_pos.mpr hn), Complex.neg_re]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn) (by linarith)

/-- On every closed spectral strip the genuine entire completed Rankin integral has at most quadratic growth. -/
theorem exists_gamma0CuspEntire_strip_bound {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : CuspForm ((Gamma0 Q).map (mapGL ℝ)) k) {σ : ℝ} (hσ : 1 < σ) :
    ∃ C : ℝ, 0 < C ∧ ∀ s : ℂ, s.re ≤ σ → 1 - s.re ≤ σ →
      ‖gamma0CuspEntire f s‖ ≤ C * (1 + ‖s‖) ^ 2 := by
  let B : ℝ := ∑ d : Q.divisors,
    ‖(ArithmeticFunction.moebius d.val : ℂ)‖ * ((Q * d.val : ℕ) : ℝ) ^ σ *
      (rectangularLatticeCuspStripMajorant f Q d.val (Nat.pos_of_neZero Q)
        (Nat.pos_of_mem_divisors d.property) σ + ‖cuspPetersson f f‖ / 2)
  have hB : 0 ≤ B := by
    apply Finset.sum_nonneg
    intro d hd
    exact mul_nonneg (mul_nonneg (norm_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg _) _))
      (add_nonneg (rectangularLatticeCuspStripMajorant_nonneg _ _ _ _ _ _) (by positivity))
  refine ⟨B + 1, by linarith, ?_⟩
  intro s hs hs'
  calc
    _ ≤ ∑ d : Q.divisors,
        ‖(ArithmeticFunction.moebius d.val : ℂ) * ((Q : ℂ) * d.val) ^ (-s) *
          rectangularLatticeCuspEntire f Q d.val (Nat.pos_of_neZero Q)
            (Nat.pos_of_mem_divisors d.property) s‖ := norm_sum_le _ _
    _ ≤ B * (1 + ‖s‖) ^ 2 := by
      dsimp only [B]
      rw [Finset.sum_mul]
      apply Finset.sum_le_sum
      intro d hd
      rw [norm_mul]
      have h := mul_le_mul
        (norm_gamma0LatticeCoefficient_le Q (Nat.pos_of_neZero Q) d hs')
        (norm_rectangularLatticeCuspEntire_le_quadratic f Q d.val (Nat.pos_of_neZero Q)
          (Nat.pos_of_mem_divisors d.property) hσ hs hs') (norm_nonneg _)
        (mul_nonneg (norm_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg _) _))
      simpa only [mul_assoc] using h
    _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg _)

end
end Dubon2026
