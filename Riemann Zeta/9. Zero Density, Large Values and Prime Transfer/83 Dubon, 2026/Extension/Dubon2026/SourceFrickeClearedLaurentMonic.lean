import Dubon2026.SourceFrickeCyclotomicLaurentLifts

/-! DUB-17/18 -> rational Fourier spanning -> holomorphic recovery of integral
Fricke Laurent summands. Clear the formal monic relation in the original
cyclotomic algebra, and use the already proved analytic identity principle
to obtain the corresponding relation between actual holomorphic functions. -/
namespace Dubon2026.SourceFricke
noncomputable section
open UpperHalfPlane SourceFunctionField
open scoped Manifold MatrixGroups ModularForm

theorem cyclotomic_polynomial_jf_mem (N : ℕ) (p : Polynomial (kN N)) :
    Polynomial.aeval JMultiplicity.jf p ∈ cyclotomicLevelRing N := by
  have hs : ({JMultiplicity.jf} : Set (ℍ → ℂ)) ⊆ levelGen N :=
    Set.singleton_subset_iff.mpr (Set.mem_insert _ _)
  exact (Algebra.adjoin_mono hs) (Polynomial.aeval_mem_adjoin_singleton (kN N) JMultiplicity.jf)

theorem represents_cyclotomic_polynomial_jf (N : ℕ) [NeZero N] (p : Polynomial (kN N)) :
    CuspTaylor.Represents (Polynomial.aeval (jqNModC ℂ N) p)
      (cuspFunction N (Polynomial.aeval JMultiplicity.jf p)) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simpa only [map_add, Pi.add_apply] using hp.cusp_add hq
  | monomial n c =>
    simpa only [Polynomial.aeval_monomial, Pi.mul_apply, Pi.pow_apply] using
      (CuspTaylor.represents_cusp_const N (c : ℂ)).cusp_mul ((represents_jqNModC N).cusp_pow n)

theorem cleared_cyclotomic_relation_of_laurent {N : ℕ} [NeZero N]
    {a b : ℍ → ℂ} {A B : LaurentSeries ℂ}
    (ha : a ∈ cyclotomicLevelRing N) (hb : b ∈ cyclotomicLevelRing N)
    (hAr : CuspTaylor.Represents A (cuspFunction N a))
    (hBr : CuspTaylor.Represents B (cuspFunction N b)) (d : ℕ) (p : ℕ → Polynomial (kN N))
    (hrel : A ^ d + ∑ k ∈ Finset.range d,
      Polynomial.aeval (jqNModC ℂ N) (p k) * B ^ (d - k) * A ^ k = 0) :
    a ^ d + ∑ k ∈ Finset.range d,
      Polynomial.aeval JMultiplicity.jf (p k) * b ^ (d - k) * a ^ k = 0 := by
  let T : ℍ → ℂ := a ^ d + ∑ k ∈ Finset.range d,
    Polynomial.aeval JMultiplicity.jf (p k) * b ^ (d - k) * a ^ k
  have hT : T ∈ cyclotomicLevelRing N :=
    Subalgebra.add_mem _ (Subalgebra.pow_mem _ ha _) (Subalgebra.sum_mem _ fun k _ =>
      Subalgebra.mul_mem _ (Subalgebra.mul_mem _ (cyclotomic_polynomial_jf_mem N (p k))
        (Subalgebra.pow_mem _ hb _)) (Subalgebra.pow_mem _ ha _))
  have hrep : CuspTaylor.Represents 0 (cuspFunction N T) := by
    have h := (hAr.cusp_pow d).cusp_add (CuspTaylor.Represents.cusp_sum (Finset.range d)
      fun k _ => ((represents_cyclotomic_polynomial_jf N (p k)).cusp_mul
        (hBr.cusp_pow (d - k))).cusp_mul (hAr.cusp_pow k))
    rw [hrel] at h
    convert h using 1
    congr 1
    funext τ
    simp only [T, Pi.add_apply, Pi.mul_apply, Pi.pow_apply, Finset.sum_apply]
  have hz : CuspTaylor.Represents 0 (cuspFunction N (0 : ℍ → ℂ)) := by
    simpa only [map_zero] using CuspTaylor.represents_cusp_const (N : ℝ) 0
  exact hrep.eq_upperHalfPlane hz (by exact_mod_cast NeZero.pos N)
    (cyclotomicLevelRing_holomorphic hT) mdifferentiable_const
    (cyclotomicLevelRing_periodic hT) (by intro z; rfl)

end
end Dubon2026.SourceFricke