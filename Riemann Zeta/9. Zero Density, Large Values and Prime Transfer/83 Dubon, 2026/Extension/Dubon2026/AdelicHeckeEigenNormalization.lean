import Dubon2026.AdelicNormalizedHecke

/-! # Exact reversal of the genuine normalized Hecke eigenvalue equation -/

namespace Dubon2026

noncomputable section
open Matrix.SpecialLinearGroup CongruenceSubgroup
open scoped MatrixGroups

private theorem nonzero_scalar_eigen_iff {V : Type*} [AddCommGroup V] [Module ℂ V]
    (x y : V) (a b c : ℂ) (ha : a ≠ 0) (h : a * b = c) :
    a • y = c • x ↔ y = b • x := by
  rw [← h, ← smul_smul]
  exact (smul_right_injective V ha).eq_iff

variable {N : ℕ} [NeZero N] {k : ℤ} (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k)

omit [NeZero N] in
/-- The genuine unitary scalar times the original classical-to-adelic eigenvalue is exactly the original normalized Fourier coefficient. -/
theorem adelicHecke_eigenvalue_normalization (p : ℕ) [NeZero p] :
    (((p : ℝ) ^ (-(1 : ℝ) / 2) : ℝ) : ℂ) *
      ((Real.sqrt (p : ℝ) : ℂ) ^ (2 - k) * cuspCoefficients f p) = normalizedCuspCoefficients f p := by
  rw [← mul_assoc, hecke_unitary_scalar_normalization k (Nat.cast_pos.mpr (Nat.pos_of_neZero p))]
  rw [normalizedCuspCoefficients, shiftedCoefficients,
    ← Complex.ofReal_natCast p, ← Complex.ofReal_cpow (Nat.cast_nonneg p)]
  exact mul_comm _ _

/-- The nonzero actual unitary scalar permits recovering the full original Hecke-trace eigenvalue from its exact normalized equation. -/
theorem adelicNormalizedHecke_eigen_iff (p : ℕ) [NeZero p] (hpN : p.Coprime N) (x : AdelicCyclicHilbert f) :
    adelicNormalizedHecke f p hpN x = normalizedCuspCoefficients f p • x ↔
      adelicHilbertHeckeTrace f p hpN x =
        ((Real.sqrt (p : ℝ) : ℂ) ^ (2 - k) * cuspCoefficients f p) • x := by
  have hc : (((p : ℝ) ^ (-(1 : ℝ) / 2) : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.rpow_pos_of_pos (Nat.cast_pos.mpr (Nat.pos_of_neZero p)) _).ne'
  rw [adelicNormalizedHecke, ContinuousLinearMap.smul_apply, adelicBoundedHeckeTrace_apply]
  exact @nonzero_scalar_eigen_iff (AdelicCyclicHilbert f) inferInstance inferInstance x
    (adelicHilbertHeckeTrace f p hpN x) _ _ _ hc (adelicHecke_eigenvalue_normalization f p)

end
end Dubon2026
