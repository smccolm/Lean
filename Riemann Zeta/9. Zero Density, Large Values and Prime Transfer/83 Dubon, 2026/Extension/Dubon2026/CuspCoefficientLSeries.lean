import Dubon2026.CuspRankinSeries
import Dubon2026.PrimitiveNormalizedRecurrence
import Mathlib.NumberTheory.EulerProduct.DirichletLSeries

/-! # The actual normalized cusp L-series and its genuine Euler product

Absolute convergence is deduced from the proved square-series convergence;
no Deligne estimate is an input.
-/

namespace Dubon2026

open CongruenceSubgroup Matrix.SpecialLinearGroup Filter
open scoped Topology

noncomputable section

/-- The genuine normalized cusp Dirichlet summands are absolutely summable on Re(s)>1 without Deligne. -/
theorem summable_norm_cusp_dirichlet {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : CuspForm ((Gamma0 Q).map (mapGL ℝ)) k) (hk : 0 ≤ k) {s : ℂ} (hs : 1 < s.re) :
    Summable (fun n : ℕ => ‖normalizedCuspCoefficients f n * (n : ℂ) ^ (-s)‖) := by
  have hsq := (summable_normalized_cusp_square_dirichlet f hk hs).norm
  have hz : Summable (fun n : ℕ => ‖(n : ℂ) ^ (-s)‖) := summable_riemannZetaSummand hs
  apply (hsq.add hz).of_nonneg_of_le (fun n => norm_nonneg _) 
  intro n
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_sq]
  have hb : ‖normalizedCuspCoefficients f n‖ ≤ ‖normalizedCuspCoefficients f n‖ ^ 2 + 1 := by
    nlinarith [sq_nonneg (‖normalizedCuspCoefficients f n‖ - 1 / 2)]
  simpa only [add_mul, one_mul] using mul_le_mul_of_nonneg_right hb (norm_nonneg ((n : ℂ) ^ (-s)))

/-- The standard Mathlib term is precisely the actual normalized coefficient times its principal power, including the zero index. -/
theorem cusp_dirichlet_lseries_term {Q : ℕ} {k : ℤ}
    (f : CuspForm ((Gamma0 Q).map (mapGL ℝ)) k) (s : ℂ) (n : ℕ) :
    LSeries.term (normalizedCuspCoefficients f) s n = normalizedCuspCoefficients f n * (n : ℂ) ^ (-s) := by
  rw [LSeries.term_def]
  by_cases hn : n = 0
  · subst n
    simp [normalizedCuspCoefficients, shiftedCoefficients, cuspCoefficients_zero]
  · rw [if_neg hn, Complex.cpow_neg, div_eq_mul_inv]

/-- The actual normalized cusp L-series is absolutely convergent on its genuine Euler half-plane. -/
theorem normalized_cusp_lseries_summable {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : CuspForm ((Gamma0 Q).map (mapGL ℝ)) k) (hk : 0 ≤ k) {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable (normalizedCuspCoefficients f) s := by
  apply (summable_norm_cusp_dirichlet f hk hs).of_norm.congr
  intro n
  exact (cusp_dirichlet_lseries_term f s n).symm

/-- The actual primitive form supplies coprime multiplicativity and absolute convergence in the genuine prime Euler product. -/
theorem primitive_cusp_lseries_euler_hasProd {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : PrimitiveCuspForm Q k) (hk : 0 ≤ k) {s : ℂ} (hs : 1 < s.re) :
    HasProd (fun p : Nat.Primes => ∑' r : ℕ,
      normalizedCuspCoefficients f.toCuspForm ((p : ℕ) ^ r) * (((p : ℕ) ^ r : ℕ) : ℂ) ^ (-s))
      (LSeries (normalizedCuspCoefficients f.toCuspForm) s) := by
  have h1 : normalizedCuspCoefficients f.toCuspForm 1 * (1 : ℂ) ^ (-s) = 1 := by
    rw [normalizedCuspCoefficients_one f.toCuspForm f.normalized]
    simp
  have hm : ∀ n m : ℕ, n.Coprime m →
      normalizedCuspCoefficients f.toCuspForm (n * m) * ((n * m : ℕ) : ℂ) ^ (-s) =
        (normalizedCuspCoefficients f.toCuspForm n * (n : ℂ) ^ (-s)) *
        (normalizedCuspCoefficients f.toCuspForm m * (m : ℂ) ^ (-s)) := by
    intro n m hnm
    rw [primitiveCuspForm_normalized_mul f n m hnm, Nat.cast_mul, Complex.natCast_mul_natCast_cpow]
    ring
  have h0 : normalizedCuspCoefficients f.toCuspForm 0 * (0 : ℂ) ^ (-s) = 0 := by
    simp [normalizedCuspCoefficients, shiftedCoefficients, cuspCoefficients_zero]
  have he := EulerProduct.eulerProduct_hasProd
    (f := fun n => normalizedCuspCoefficients f.toCuspForm n * (n : ℂ) ^ (-s))
    (by simpa only [Nat.cast_one] using h1) (fun {m n} h => hm m n h)
    (summable_norm_cusp_dirichlet f.toCuspForm hk hs) (by simpa only [Nat.cast_zero] using h0)
  convert he using 1
  unfold LSeries
  apply tsum_congr
  exact cusp_dirichlet_lseries_term f.toCuspForm s

end
end Dubon2026
