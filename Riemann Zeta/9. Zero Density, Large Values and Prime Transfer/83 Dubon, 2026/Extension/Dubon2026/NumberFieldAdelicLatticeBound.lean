import Dubon2026.NumberFieldAdelicLattice

/-! # An actual adelic lattice lies in a fractional integral lattice

The denominator is derived from the original adelic matrix. This supplies
the finite-module step in DUB-17's arithmetic double-coset route, without
assuming finite generation of the attached lattice.
-/

namespace Dubon2026

noncomputable section

open NumberField IsDedekindDomain
open scoped NumberField

variable (K : Type*) [Field K] [NumberField K]
variable (ι : Type*) [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
/-- A denominator for an adelic matrix makes its product with every integral vector integral. -/
theorem numberFieldAdelicMatrix_mulVec_integral
    (M : Matrix ι ι (FiniteAdeleRing (𝓞 K) K)) (d : 𝓞 K)
    (hM : ∀ i j, M i j * algebraMap (𝓞 K) (FiniteAdeleRing (𝓞 K) K) d ∈
      numberFieldIntegralFiniteAdeles K)
    (y : ι → FiniteAdeleRing (𝓞 K) K)
    (hy : ∀ j, y j ∈ numberFieldIntegralFiniteAdeles K) (i : ι) :
    M.mulVec y i * algebraMap (𝓞 K) (FiniteAdeleRing (𝓞 K) K) d ∈
      numberFieldIntegralFiniteAdeles K := by
  rw [Matrix.mulVec, dotProduct, Finset.sum_mul]
  apply (numberFieldIntegralFiniteAdeles K).sum_mem
  intro j _
  simpa only [mul_right_comm] using (numberFieldIntegralFiniteAdeles K).mul_mem (hM i j) (hy j)

/-- Every vector in the actual adelic lattice becomes integral after one fixed nonzero scaling. -/
theorem numberFieldAdelicLattice_exists_denominator
    (g : Matrix.GeneralLinearGroup ι (FiniteAdeleRing (𝓞 K) K)) :
    ∃ d : 𝓞 K, d ≠ 0 ∧ ∀ x ∈ numberFieldAdelicLattice K ι g,
      ∀ i, IsIntegral ℤ ((d : K) * x i) := by
  obtain ⟨d, hd, hM⟩ := numberFieldFiniteAdeles_exists_common_integral_multiple K
    (fun ij : ι × ι => g.val ij.1 ij.2)
  refine ⟨d, hd, ?_⟩
  intro x hx i
  have hy := (numberFieldAdelicLattice_mem_iff K ι g x).mp hx
  have h := numberFieldAdelicMatrix_mulVec_integral K ι g.val d
    (fun i j => hM (i, j)) _ hy i
  have hc : g.val.mulVec ((g⁻¹).val.mulVec
      (fun j => algebraMap K (FiniteAdeleRing (𝓞 K) K) (x j))) =
        (fun j => algebraMap K (FiniteAdeleRing (𝓞 K) K) (x j)) := by
    rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
  rw [congrFun hc i] at h
  apply (numberFieldFiniteAdele_integral_iff K _).mp
  simpa only [map_mul, IsScalarTower.algebraMap_apply (𝓞 K) K
    (FiniteAdeleRing (𝓞 K) K), mul_comm] using h

end
end Dubon2026
