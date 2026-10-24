import Dubon2026.SourceEllipticOddQuotientLatticeJ
import Dubon2026.SourceEllipticStandardCyclicComplete
import Dubon2026.SourcePrimeConjugateRealization

/-! Each actual standard odd cyclic quotient has the literal corresponding
analytic prime-Hecke j-value. This consumes the actual norm uniformization,
computed kernel lattices and genuine period invariants. It supplies the
geometric factors of the DUB-17/18 odd-prime modular-polynomial identity. -/

namespace Dubon2026.SourceEllipticPeriod
open WeierstrassCurve UpperHalfPlane SourceFunctionField
open SourceEllipticVelu.OddDiscriminant

theorem standardOddQuotientJ_eq (τ : ℍ) (C : VariableChange ℂ)
    (p : ℕ) [Fact p.Prime] (i : Fin (p + 1)) {n : ℕ}
    (hQ : addOrderOf (standardTorsionPoint τ C p i) = 2 * n + 1) :
    oddQuotientJ (C • periodCurve (PeriodLattice.ofTau τ)) hQ =
      JMultiplicity.jf (rep p i • τ) := by
  revert hQ
  refine Fin.cases ?_ (fun b => ?_) i
  · intro hQ
    have h := oddQuotientJ_eq_periodCurve_j_of_kernel_lattice
      (PeriodLattice.ofTau τ)
      (PeriodLattice.scale (PeriodLattice.ofTau (levelRaiseMatrix p • τ))
        (Units.mk0 (p : ℂ) (Nat.cast_ne_zero.mpr (NeZero.ne p)))⁻¹)
      C hQ (standard_diagonal_quotient_lattice τ C p)
    rw [periodCurve_scale_j, periodCurve_ofTau_j] at h
    have heq : rep p 0 • τ = levelRaiseMatrix p • τ := by
      rw [rep_zero, heckeTriangularMatrix_smul]
      apply UpperHalfPlane.ext
      simp only [heckeUpperPoint, Nat.cast_zero, add_zero, Nat.cast_one, div_one, coe_mk]
    simpa only [heq] using h
  · intro hQ
    have h := oddQuotientJ_eq_periodCurve_j_of_kernel_lattice
      (PeriodLattice.ofTau τ) (PeriodLattice.ofTau (heckeUpperPoint p b.val τ))
      C hQ (standard_upper_quotient_lattice τ C p b.val)
    rw [periodCurve_ofTau_j] at h
    have heq : rep p b.succ • τ = heckeUpperPoint p b.val τ := by
      rw [rep_succ, heckeTriangularMatrix_smul]
      congr 1
      apply UpperHalfPlane.ext
      simp only [coe_levelRaiseMatrix_smul, Nat.cast_one, one_mul]
    simpa only [heq] using h

end Dubon2026.SourceEllipticPeriod
