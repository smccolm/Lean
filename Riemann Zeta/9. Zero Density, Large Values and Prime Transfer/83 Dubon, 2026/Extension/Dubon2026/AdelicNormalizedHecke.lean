import Dubon2026.AdelicBoundedHeckeTrace
import Dubon2026.HeckeUnitaryScalarNormalization
import Dubon2026.AdelicPrimitiveHeckeEigen

/-! # The actual bounded adelic Hecke operator with its original unitary eigenvalue -/

namespace Dubon2026

noncomputable section
open Matrix.SpecialLinearGroup CongruenceSubgroup
open scoped MatrixGroups

private theorem scalar_eigen_normalization {V : Type*} [AddCommGroup V] [Module ℂ V]
    (v : V) (a b c : ℂ) (h : a * b = c) : a • (b • v) = c • v := by
  rw [smul_smul, h]

/-- The genuine full finite-adelic coset trace with its p^(-1/2) unitary normalization. -/
def adelicNormalizedHecke {N : ℕ} [NeZero N] {k : ℤ}
    (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k) (p : ℕ) [NeZero p] (hpN : p.Coprime N) :
    AdelicCyclicHilbert f →L[ℂ] AdelicCyclicHilbert f :=
  (((p : ℝ) ^ (-(1 : ℝ) / 2) : ℝ) : ℂ) • adelicBoundedHeckeTrace f p hpN

/-- The original primitive Hilbert generator is an eigenvector of the actual normalized adelic Hecke operator with exactly its original normalized Fourier coefficient. -/
theorem adelicNormalizedHecke_primitive_generator {N p : ℕ} [NeZero N] [NeZero p]
    [Fact p.Prime] {k : ℤ} (f : PrimitiveCuspForm N k) (hpN : p.Coprime N) :
    adelicNormalizedHecke f.toCuspForm p hpN (adelicCyclicHilbertGenerator f.toCuspForm) =
      normalizedCuspCoefficients f.toCuspForm p • adelicCyclicHilbertGenerator f.toCuspForm := by
  rw [adelicNormalizedHecke, ContinuousLinearMap.smul_apply, adelicBoundedHeckeTrace_apply,
    adelicHilbertHeckeTrace_primitive_generator]
  apply @scalar_eigen_normalization (AdelicCyclicHilbert f.toCuspForm) inferInstance inferInstance
  rw [← mul_assoc, hecke_unitary_scalar_normalization k (Nat.cast_pos.mpr (Nat.pos_of_neZero p))]
  rw [normalizedCuspCoefficients, shiftedCoefficients,
    ← Complex.ofReal_natCast p, ← Complex.ofReal_cpow (Nat.cast_nonneg p)]
  exact mul_comm _ _

/-- The actual unitary-normalized operator preserves the genuine full level-fixed space. -/
theorem adelicNormalizedHecke_level {N p : ℕ} [NeZero N] [NeZero p] [Fact p.Prime] {k : ℤ}
    (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k) (hpN : p.Coprime N)
    (v : AdelicCyclicHilbert f) (hv : v ∈ adelicLevelFixedSpace f) :
    adelicNormalizedHecke f p hpN v ∈ adelicLevelFixedSpace f := by
  rw [adelicNormalizedHecke, ContinuousLinearMap.smul_apply, adelicBoundedHeckeTrace_apply]
  exact (adelicLevelFixedSpace f).smul_mem _ (adelicHilbertHeckeTrace_level f p hpN v hv)

end
end Dubon2026
