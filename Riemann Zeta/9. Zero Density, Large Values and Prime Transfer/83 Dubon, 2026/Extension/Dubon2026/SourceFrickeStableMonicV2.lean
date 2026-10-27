import Dubon2026.SourceFrickeStableFieldV2
import Mathlib.RingTheory.Invariant.Basic

/-! DUB-17/18 -> original all-weight arithmetic association -> finite Gamma1
character realization -> Picard/H1 comparison -> cusp differential realization
-> rational Fourier structure -> integral base change of actual Fricke fractions.
The native finite-action characteristic polynomial supplies the monic equation.
Its invariant coefficients are polynomials in the actual j by the proved
stable-algebra invariant theorem. No separate orbit coefficient bounds are needed.
-/
namespace Dubon2026.SourceFricke
noncomputable section
open UpperHalfPlane SourceFunctionField
open scoped MatrixGroups ModularForm Manifold

namespace LevelGens
variable {N : ℕ} [NeZero N] (D : LevelGens N)

theorem ring_monic_j_relation (a : ↥D.ring) :
    ∃ (d : ℕ) (p : Fin d → Polynomial ℂ), ∀ τ : ℍ,
      (a : ℍ → ℂ) τ ^ d + ∑ i : Fin d, (p i).eval (JMultiplicity.jf τ) * (a : ℍ → ℂ) τ ^ (i : ℕ) = 0 := by
  classical
  let Q := MulSemiringAction.charpoly (LevelGrp N) a
  have hm : Q.Monic := MulSemiringAction.monic_charpoly (LevelGrp N) a
  have hr : Q.eval a = 0 := MulSemiringAction.eval_charpoly (LevelGrp N) a
  choose P hP using fun n => D.ring_fixed_eq_aeval_j (Q.coeff n)
    (MulSemiringAction.smul_coeff_charpoly a n)
  have he := Polynomial.eval_eq_sum_range' (p := Q)
    (n := Q.natDegree + 1) (Nat.lt_succ_self Q.natDegree) a
  rw [Finset.sum_range_succ, hm.coeff_natDegree, one_mul, hr] at he
  have hrel : a ^ Q.natDegree +
      ∑ k ∈ Finset.range Q.natDegree, Polynomial.aeval D.jA (P k) * a ^ k = 0 := by
    rw [add_comm]
    simpa only [hP] using he.symm
  refine ⟨Q.natDegree, fun i => P i, fun τ => ?_⟩
  let ev : ↥D.ring →ₐ[ℂ] ℂ := (Pi.evalAlgHom ℂ (fun _ : ℍ => ℂ) τ).comp D.ring.val
  have hc (n : ℕ) : ev (Polynomial.aeval D.jA (P n)) = (P n).eval (JMultiplicity.jf τ) :=
    congrFun (D.coe_aeval_jA (P n)) τ
  have h := congrArg ev hrel
  simp only [map_add, map_sum, map_mul, map_pow, map_zero, hc] at h
  rw [← Fin.sum_univ_eq_sum_range (fun n => (P n).eval (JMultiplicity.jf τ) * ev a ^ n)
    Q.natDegree] at h
  exact h

end LevelGens
end
end Dubon2026.SourceFricke
