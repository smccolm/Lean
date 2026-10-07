import Dubon2026.LatticeCuspFunctionalEquation

/-! # Proved vertical-strip bounds for the actual integrated lattice continuation -/

namespace Dubon2026

open UpperHalfPlane MeasureTheory CongruenceSubgroup Matrix.SpecialLinearGroup

noncomputable section

/-- The actual positive convergent integral majorizing a fixed spectral strip. -/
def rectangularLatticeCuspStripMajorant {Q : ℕ} {k : ℤ}
    (f : CuspForm ((Gamma0 Q).map (mapGL ℝ)) k) (a b : ℕ) (ha : 0 < a) (hb : 0 < b) (σ : ℝ) : ℝ :=
  2 * ∫ z : ℍ in gamma0FundamentalDomain Q,
    ‖latticeCompletedMellin (rectangularLatticePoint a b ha hb z) (σ : ℂ)‖ * ‖petersson k f f z‖

/-- The actual integrated strip majorant is nonnegative. -/
theorem rectangularLatticeCuspStripMajorant_nonneg {Q : ℕ} {k : ℤ}
    (f : CuspForm ((Gamma0 Q).map (mapGL ℝ)) k) (a b : ℕ) (ha : 0 < a) (hb : 0 < b) (σ : ℝ) :
    0 ≤ rectangularLatticeCuspStripMajorant f a b ha hb σ :=
  mul_nonneg (by norm_num) (integral_nonneg (fun _ => mul_nonneg (norm_nonneg _) (norm_nonneg _)))

/-- The true entire regularized cusp integral is uniformly bounded on every closed vertical strip by a proved convergent integral. -/
theorem norm_rectangularLatticeCuspRegular_le {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : CuspForm ((Gamma0 Q).map (mapGL ℝ)) k) (a b : ℕ) (ha : 0 < a) (hb : 0 < b)
    {σ : ℝ} (hσ : 1 < σ) {s : ℂ} (hs : s.re ≤ σ) (hs' : 1 - s.re ≤ σ) :
    ‖rectangularLatticeCuspRegular f a b ha hb s‖ ≤ rectangularLatticeCuspStripMajorant f a b ha hb σ := by
  have hR := (integrableOn_rectangular_lattice_regular_petersson f a b ha hb s).norm
  have hM := (integrableOn_norm_rectangular_lattice_petersson f a b ha hb hσ).const_mul 2
  calc
    _ ≤ ∫ z : ℍ in gamma0FundamentalDomain Q,
        ‖latticeCompletedMellinRegular (rectangularLatticePoint a b ha hb z) s * petersson k f f z‖ :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ z : ℍ in gamma0FundamentalDomain Q,
        2 * (‖latticeCompletedMellin (rectangularLatticePoint a b ha hb z) (σ : ℂ)‖ *
          ‖petersson k f f z‖) := by
      apply integral_mono hR hM
      intro z
      dsimp only
      rw [norm_mul, ← mul_assoc]
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
      exact (norm_latticeCompletedMellinRegular_le _ hσ hs hs').trans
        (mul_le_mul_of_nonneg_left (Complex.re_le_norm _) (by norm_num))
    _ = _ := by rw [integral_const_mul]; rfl

/-- Multiplication by s(s−1) gives a polynomial vertical-strip bound on the actual entire completion. -/
theorem norm_rectangularLatticeCuspEntire_le {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : CuspForm ((Gamma0 Q).map (mapGL ℝ)) k) (a b : ℕ) (ha : 0 < a) (hb : 0 < b)
    {σ : ℝ} (hσ : 1 < σ) {s : ℂ} (hs : s.re ≤ σ) (hs' : 1 - s.re ≤ σ) :
    ‖rectangularLatticeCuspEntire f a b ha hb s‖ ≤
      ‖s‖ * ‖s - 1‖ * rectangularLatticeCuspStripMajorant f a b ha hb σ + ‖cuspPetersson f f‖ / 2 := by
  unfold rectangularLatticeCuspEntire
  apply (norm_add_le (s * (s - 1) * rectangularLatticeCuspRegular f a b ha hb s)
    (cuspPetersson f f / 2)).trans
  rw [norm_mul, norm_mul, norm_div, Complex.norm_ofNat]
  exact add_le_add (mul_le_mul_of_nonneg_left
    (norm_rectangularLatticeCuspRegular_le f a b ha hb hσ hs hs')
      (mul_nonneg (norm_nonneg s) (norm_nonneg (s - 1)))) le_rfl

/-- The pole-cleared lattice integral has a quadratic norm bound uniformly across the whole closed strip. -/
theorem norm_rectangularLatticeCuspEntire_le_quadratic {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : CuspForm ((Gamma0 Q).map (mapGL ℝ)) k) (a b : ℕ) (ha : 0 < a) (hb : 0 < b)
    {σ : ℝ} (hσ : 1 < σ) {s : ℂ} (hs : s.re ≤ σ) (hs' : 1 - s.re ≤ σ) :
    ‖rectangularLatticeCuspEntire f a b ha hb s‖ ≤
      (rectangularLatticeCuspStripMajorant f a b ha hb σ + ‖cuspPetersson f f‖ / 2) * (1 + ‖s‖) ^ 2 := by
  have hM := rectangularLatticeCuspStripMajorant_nonneg f a b ha hb σ
  have hs0 := norm_nonneg s
  have hP := norm_nonneg (cuspPetersson f f)
  have hn : ‖s - 1‖ ≤ ‖s‖ + 1 := by simpa only [norm_one] using norm_sub_le s 1
  calc
    _ ≤ ‖s‖ * ‖s - 1‖ * rectangularLatticeCuspStripMajorant f a b ha hb σ + ‖cuspPetersson f f‖ / 2 :=
      norm_rectangularLatticeCuspEntire_le f a b ha hb hσ hs hs'
    _ ≤ ‖s‖ * (‖s‖ + 1) * rectangularLatticeCuspStripMajorant f a b ha hb σ + ‖cuspPetersson f f‖ / 2 :=
      add_le_add (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hn hs0) hM) le_rfl
    _ ≤ _ := by
      have h1 : ‖s‖ * (‖s‖ + 1) ≤ (1 + ‖s‖) ^ 2 := by nlinarith
      have h2 : 1 ≤ (1 + ‖s‖) ^ 2 := by nlinarith
      have h3 := mul_le_mul_of_nonneg_right h1 hM
      have h4 := mul_le_mul_of_nonneg_left h2 (show (0 : ℝ) ≤ ‖cuspPetersson f f‖ / 2 by positivity)
      nlinarith

end
end Dubon2026
