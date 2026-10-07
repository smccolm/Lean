import Dubon2026.CuspTraceCoefficients
import Dubon2026.CuspPeriodMellin

/-! # Exact Mellin transform of the actual full-level cusp trace -/

namespace Dubon2026

open UpperHalfPlane Matrix.SpecialLinearGroup CongruenceSubgroup MeasureTheory Set
open scoped MatrixGroups

noncomputable section

variable {N : ℕ} {H : Subgroup SL(2, ℤ)} [Fintype (SL(2, ℤ) ⧸ H)]
  (hH : Gamma N ≤ H) {k : ℤ} (f : CuspForm (H.map (mapGL ℝ)) k)

/-- The actual aggregate horizontal energy, integrated on the literal full-level unit interval. -/
def cuspTraceHorizontalEnergy (y : ℝ) : ℝ :=
  ∫ x in (0 : ℝ)..1, ∑ q : SL(2, ℤ) ⧸ H,
    ‖cuspCosetFamily hH f q (UpperHalfPlane.ofComplex ((x : ℂ) + y * Complex.I))‖ ^ 2

/-- The unit-interval trace energy equals the finite sum of the actual common-period averages. -/
theorem cuspTraceHorizontalEnergy_eq_sum (hN : 0 < N) {y : ℝ} (hy : 0 < y) :
    cuspTraceHorizontalEnergy hH f y =
      ∑ q : SL(2, ℤ) ⧸ H, cuspPeriodHorizontalEnergy (cuspCosetFamily hH f q) N y := by
  have ht := hasSum_cusp_coset_horizontal_energy hN hH f hy
  have hs := hasSum_sum (s := Finset.univ) (fun q _ => hasSum_cuspPeriodHorizontalEnergy
    (cuspCosetFamily hH f q) (h := (N : ℝ)) (by exact_mod_cast hN)
    (by simp [strictPeriods_Gamma]) hy)
  have he (n : ℕ) : -((4 * Real.pi / N) * n) * y = -4 * Real.pi * n * y / N := by ring
  simp_rw [he] at hs
  have hs' : HasSum (fun n : ℕ => (∑ q : SL(2, ℤ) ⧸ H,
      ‖(qExpansion (N : ℝ) (cuspCosetFamily hH f q)).coeff n‖ ^ 2) *
        Real.exp (-4 * Real.pi * n * y / N))
      (∑ q : SL(2, ℤ) ⧸ H, cuspPeriodHorizontalEnergy (cuspCosetFamily hH f q) N y) := by
    simpa only [Finset.sum_mul] using hs
  rw [← ht.unique hs']
  unfold cuspTraceHorizontalEnergy
  apply intervalIntegral.integral_congr
  intro x _
  dsimp only
  rw [UpperHalfPlane.ofComplex_apply_of_im_pos (by simpa using hy)]

/-- The actual full-level trace Mellin integral is absolutely convergent from its genuine period-coefficient bounds. -/
theorem integrableOn_cuspTrace_mellin [NeZero N] (hk : 0 < k) {s : ℂ} (hs : 1 < s.re) :
    IntegrableOn (fun y : ℝ => (y : ℂ) ^ (s + (k : ℂ) - 2) *
      (cuspTraceHorizontalEnergy hH f y : ℂ)) (Ioi 0) := by
  have hi := integrable_finsetSum Finset.univ (fun q _ => integrableOn_cuspPeriodRankin_mellin
    (cuspCosetFamily hH f q) (h := (N : ℝ)) (by exact_mod_cast Nat.pos_of_neZero N)
    (by simp [strictPeriods_Gamma]) hk hs)
  apply hi.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
  simp only [cuspTraceHorizontalEnergy_eq_sum hH f (Nat.pos_of_neZero N) hy,
    Complex.ofReal_sum, Finset.mul_sum]

/-- The literal trace integral equals the genuine normalized trace-square L-series with the exact common-period Gamma factor. -/
theorem cuspTrace_mellin_identity [NeZero N] (hk : 0 < k) {s : ℂ} (hs : 1 < s.re) :
    (∫ y : ℝ in Ioi 0, (y : ℂ) ^ (s + (k : ℂ) - 2) * (cuspTraceHorizontalEnergy hH f y : ℂ)) =
      (((4 * Real.pi / N : ℝ) : ℂ) ^ (-(s + (k : ℂ) - 1)) * Complex.Gamma (s + (k : ℂ) - 1)) *
        LSeries (fun n => (cuspTraceSquareCoefficients hH f n : ℂ)) s := by
  have hi (q : SL(2, ℤ) ⧸ H) := integrableOn_cuspPeriodRankin_mellin
    (cuspCosetFamily hH f q) (h := (N : ℝ)) (by exact_mod_cast Nat.pos_of_neZero N)
    (by simp [strictPeriods_Gamma]) hk hs
  calc
    _ = ∫ y : ℝ in Ioi 0, ∑ q : SL(2, ℤ) ⧸ H,
        (y : ℂ) ^ (s + (k : ℂ) - 2) * (cuspPeriodHorizontalEnergy (cuspCosetFamily hH f q) N y : ℂ) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro y hy
      dsimp only
      rw [cuspTraceHorizontalEnergy_eq_sum hH f (Nat.pos_of_neZero N) hy,
        Complex.ofReal_sum, Finset.mul_sum]
    _ = _ := by
      rw [integral_finsetSum _ (fun q _ => hi q), cuspTraceSquare_LSeries hH f hk hs, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro q _
      exact cuspPeriodRankinSeries_mellin (cuspCosetFamily hH f q)
        (by exact_mod_cast Nat.pos_of_neZero N) (by simp [strictPeriods_Gamma]) hk hs

end
end Dubon2026
