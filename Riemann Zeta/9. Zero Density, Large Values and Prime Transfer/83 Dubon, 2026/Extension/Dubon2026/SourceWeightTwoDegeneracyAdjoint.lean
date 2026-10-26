import Dubon2026.CuspOldNewProjection
import Dubon2026.SourceWeightTwoFullEigenlift
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-! DUB-17/18 -> close the actual parabolic branch -> primitive lower
level with the same good-prime eigensystem. The native finite-dimensional
adjoint is applied to the genuine degeneracy map and Petersson integrals.
This avoids reconstructing spectral or orthogonal-projection theory. -/
namespace Dubon2026
noncomputable section
open CongruenceSubgroup

theorem sourceWeightTwoPetersson_ext {N : ℕ} [NeZero N]
    (f g : CuspForm (Gamma0 N) 2)
    (h : ∀ v, cuspPetersson f v = cuspPetersson g v) : f = g := by
  apply sub_eq_zero.mp
  apply cuspPetersson_definite
  simp only [sub_eq_add_neg, cuspPetersson_add_left, cuspPetersson_neg_left]
  rw [h]
  exact add_neg_cancel _

theorem sourceWeightTwoDegeneracy_exists_adjoint {M N : ℕ} [NeZero M] [NeZero N]
    (d : ℕ) [NeZero d] (h : d * M ∣ N) (f : CuspForm (Gamma0 N) 2) :
    ∃ g : CuspForm (Gamma0 M) 2,
      ∀ v, cuspPetersson g v = cuspPetersson f (cuspDegeneracyMap d h 2 v) := by
  letI := SourceFunctionField.original_weight_two_cusp_finite M
  letI := SourceFunctionField.original_weight_two_cusp_finite N
  letI := cuspPeterssonCore M 2
  letI := InnerProductSpace.Core.toNormedAddCommGroup
    (𝕜 := ℂ) (F := CuspForm (Gamma0 M) 2)
  letI := InnerProductSpace.ofCore (cuspPeterssonCore M 2).toCore
  letI := cuspPeterssonCore N 2
  letI := InnerProductSpace.Core.toNormedAddCommGroup
    (𝕜 := ℂ) (F := CuspForm (Gamma0 N) 2)
  letI := InnerProductSpace.ofCore (cuspPeterssonCore N 2).toCore
  exact ⟨(cuspDegeneracyMap d h 2).adjoint f,
    fun v => LinearMap.adjoint_inner_left (cuspDegeneracyMap d h 2) v f⟩

theorem sourceWeightTwoDegeneracy_adjoint_eigen
    {M N p : ℕ} [NeZero M] [NeZero N] [NeZero p]
    (d : ℕ) [NeZero d] (h : d * M ∣ N) (hp : p.Prime)
    (hpN : Nat.Coprime p N) (z : ℂ)
    (f : CuspForm (Gamma0 N) 2) (g : CuspForm (Gamma0 M) 2)
    (hg : ∀ v, cuspPetersson g v = cuspPetersson f (cuspDegeneracyMap d h 2 v))
    (he : cuspHeckeLinear N 2 p f = z • f) :
    cuspHeckeLinear M 2 p g = z • g := by
  apply sourceWeightTwoPetersson_ext
  intro v
  have hpM : Nat.Coprime p M := hpN.of_dvd_right ((dvd_mul_left M d).trans h)
  rw [cuspHeckeLinear_coprime_selfAdjoint M 2 p hpM, hg,
    ← cuspHeckeLinear_prime_degeneracy d h 2 hp hpN,
    ← cuspHeckeLinear_coprime_selfAdjoint N 2 p hpN, he,
    cuspPetersson_conj_smul_left, cuspPetersson_conj_smul_left, hg]

end
end Dubon2026
