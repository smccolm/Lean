import Dubon2026.CuspTraceEisensteinMellin
import Dubon2026.CuspTraceLatticeIntegral
import Dubon2026.CuspTraceRankinConvolution
import Dubon2026.LatticeEpsteinPrimitive

/-! # Exact completed Dirichlet series of the actual finite cusp trace -/

namespace Dubon2026

open UpperHalfPlane Matrix.SpecialLinearGroup CongruenceSubgroup MeasureTheory
open scoped MatrixGroups

noncomputable section

/-- The common-period trace completion retains its exact two Gamma factors. -/
def cuspTraceRankinFactor (N : ℕ) (k : ℤ) (s : ℂ) : ℂ :=
  (Real.pi : ℂ) ^ (-s) * Complex.Gamma s *
    (((4 * Real.pi / N : ℝ) : ℂ) ^ (-(s + (k : ℂ) - 1)) * Complex.Gamma (s + (k : ℂ) - 1))

/-- The actual trace convolution Dirichlet series absorbs exactly the full-level zeta square factor. -/
theorem cuspTraceRankin_LSeries_zeta {N : ℕ} [NeZero N] {H : Subgroup SL(2, ℤ)}
    [Fintype (SL(2, ℤ) ⧸ H)] (hH : Gamma N ≤ H) {k : ℤ}
    (f : CuspForm (H.map (mapGL ℝ)) k) (hk : 0 < k) {s : ℂ} (hs : 1 < s.re) :
    LSeries (cuspTraceRankinCoefficients hH f) s = riemannZeta (2 * s) *
      LSeries (fun n => (cuspTraceSquareCoefficients hH f n : ℂ)) s := by
  rw [cuspTraceRankin_LSeries hH f hk hs, cuspTraceSquare_LSeries hH f hk hs]
  simp only [DirichletCharacter.LFunctionTrivChar, DirichletCharacter.LFunction_modOne_eq]

/-- The actual completed lattice trace integral equals its genuine convolution series on the real convergence axis. -/
theorem lattice_cusp_trace_eq_series_real {N : ℕ} [NeZero N] {H : Subgroup SL(2, ℤ)}
    [Fintype (SL(2, ℤ) ⧸ H)] (hH : Gamma N ≤ H) {k : ℤ}
    (f : CuspForm (H.map (mapGL ℝ)) k) (hk : 0 < k) {σ : ℝ} (hσ : 1 < σ) :
    (∫ z : ℍ in ModularGroup.fdo, latticeCompletedMellin z (σ : ℂ) *
      ∑ q : SL(2, ℤ) ⧸ H, petersson k (cuspCosetFamily hH f q) (cuspCosetFamily hH f q) z) =
      cuspTraceRankinFactor N k (σ : ℂ) * LSeries (cuspTraceRankinCoefficients hH f) (σ : ℂ) := by
  simp_rw [latticeCompletedMellin_eq_completed_eisenstein _ (s := (σ : ℂ)) hσ, mul_assoc]
  simp_rw [integral_const_mul]
  rw [cuspTrace_eisenstein_mellin hH f hk hσ,
    cuspTraceRankin_LSeries_zeta hH f hk hσ, cuspTraceRankinFactor]
  ring

/-- The actual subgroup-domain integral is the exact completed Dirichlet series of all its genuine cusps. -/
theorem lattice_cusp_integral_eq_series_real {N : ℕ} [NeZero N] {H : Subgroup SL(2, ℤ)}
    [Fintype (SL(2, ℤ) ⧸ H)] (hH : Gamma N ≤ H) (hCenter : Subgroup.center SL(2, ℤ) ≤ H)
    {k : ℤ} (f : CuspForm (H.map (mapGL ℝ)) k) (hk : 0 < k) {σ : ℝ} (hσ : 1 < σ) :
    (∫ z : ℍ in integralSubgroupDomain H, latticeCompletedMellin z (σ : ℂ) * petersson k f f z) =
      cuspTraceRankinFactor N k (σ : ℂ) * LSeries (cuspTraceRankinCoefficients hH f) (σ : ℂ) := by
  rw [lattice_cusp_integral_eq_trace hH hCenter f hσ, lattice_cusp_trace_eq_series_real hH f hk hσ]

end
end Dubon2026
