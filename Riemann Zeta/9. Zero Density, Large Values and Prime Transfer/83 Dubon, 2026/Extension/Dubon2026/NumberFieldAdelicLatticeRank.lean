import Dubon2026.NumberFieldAdelicLatticeFinite
import Mathlib.LinearAlgebra.Span.TensorProduct
import Mathlib.RingTheory.Flat.TorsionFree

/-! # Full rank of the original adelic lattice

Denominators for the inverse matrix place a nonzero multiple of the
original integral vectors inside the attached lattice. Comparing the
resulting injective integral maps in both directions gives exactly its
expected rational rank. This serves the actual trace-lattice step of
DUB-17, before local comparison and uniform determinant control.
-/

namespace Dubon2026

noncomputable section

open NumberField IsDedekindDomain
open scoped NumberField

variable (K : Type*) [Field K] [NumberField K]
variable (ι : Type*) [Fintype ι] [DecidableEq ι]

/-- A nonzero multiple of every original integral vector belongs to the actual attached lattice. -/
theorem numberFieldAdelicLattice_contains_scaled_integers
    (g : Matrix.GeneralLinearGroup ι (FiniteAdeleRing (𝓞 K) K)) :
    ∃ d : 𝓞 K, d ≠ 0 ∧ ∀ z : ι → 𝓞 K,
      (fun i => (d : K) * (z i : K)) ∈ numberFieldAdelicLattice K ι g := by
  obtain ⟨d, hd, hM⟩ := numberFieldFiniteAdeles_exists_common_integral_multiple K
    (fun ij : ι × ι => (g⁻¹).val ij.1 ij.2)
  refine ⟨d, hd, ?_⟩
  intro z
  apply (numberFieldAdelicLattice_mem_iff K ι g _).mpr
  intro i
  have hy (j : ι) : algebraMap K (FiniteAdeleRing (𝓞 K) K) (z j : K) ∈
      numberFieldIntegralFiniteAdeles K :=
    (numberFieldFiniteAdele_integral_iff K _).mpr (z j).property
  have h := numberFieldAdelicMatrix_mulVec_integral K ι (g⁻¹).val d
    (fun i j => hM (i, j)) _ hy i
  have he : (fun j => algebraMap K (FiniteAdeleRing (𝓞 K) K) ((d : K) * (z j : K))) =
      algebraMap (𝓞 K) (FiniteAdeleRing (𝓞 K) K) d •
        (fun j => algebraMap K (FiniteAdeleRing (𝓞 K) K) (z j : K)) := by
    ext j
    simp only [map_mul, Pi.smul_apply, smul_eq_mul,
      IsScalarTower.algebraMap_apply (𝓞 K) K (FiniteAdeleRing (𝓞 K) K)]
  rw [he, Matrix.mulVec_smul]
  simpa only [Pi.smul_apply, smul_eq_mul, mul_comm] using h

/-- The original attached lattice has exactly the expected rational rank. -/
theorem numberFieldAdelicLattice_finrank
    (g : Matrix.GeneralLinearGroup ι (FiniteAdeleRing (𝓞 K) K)) :
    Module.finrank ℤ (numberFieldAdelicLattice K ι g) =
      Fintype.card ι * Module.finrank ℚ K := by
  letI := numberFieldAdelicLattice_finite K ι g
  have hupper : Module.finrank ℤ (numberFieldAdelicLattice K ι g) ≤
      Module.finrank ℤ (ι → 𝓞 K) := by
    obtain ⟨d, hd, hint⟩ := numberFieldAdelicLattice_exists_denominator K ι g
    exact LinearMap.finrank_le_finrank_of_injective
      (numberFieldAdelicLatticeIntegralMap_injective K ι g d hint hd)
  have hlower : Module.finrank ℤ (ι → 𝓞 K) ≤
      Module.finrank ℤ (numberFieldAdelicLattice K ι g) := by
    obtain ⟨d, hd, hint⟩ := numberFieldAdelicLattice_contains_scaled_integers K ι g
    let f : (ι → 𝓞 K) →ₗ[ℤ] numberFieldAdelicLattice K ι g :=
      { toFun := fun z => ⟨fun i => (d : K) * (z i : K), hint z⟩
        map_add' := by
          intro x y
          ext i
          change (d : K) * ((x i : K) + (y i : K)) =
            (d : K) * (x i : K) + (d : K) * (y i : K)
          exact mul_add _ _ _
        map_smul' := by
          intro n x
          ext i
          change (d : K) * (n • (x i : K)) = n • ((d : K) * (x i : K))
          simpa only [zsmul_eq_mul] using mul_left_comm (d : K) (n : K) (x i : K) }
    apply LinearMap.finrank_le_finrank_of_injective (f := f)
    intro x y h
    funext i
    apply Subtype.ext
    have hdK : (d : K) ≠ 0 := by
      intro hz
      exact hd (Subtype.ext hz)
    exact mul_left_cancel₀ hdK (congrArg (fun z : numberFieldAdelicLattice K ι g => z.val i) h)
  have he := le_antisymm hupper hlower
  simpa only [Module.finrank_pi_fintype, RingOfIntegers.rank,
    Finset.sum_const, Finset.card_univ, smul_eq_mul] using he

/-- The rational span of the actual attached lattice is the entire original vector space. -/
theorem numberFieldAdelicLattice_span_rat
    (g : Matrix.GeneralLinearGroup ι (FiniteAdeleRing (𝓞 K) K)) :
    Submodule.span ℚ (numberFieldAdelicLattice K ι g : Set (ι → K)) = ⊤ := by
  let L := (numberFieldAdelicLattice K ι g).restrictScalars ℤ
  letI := numberFieldAdelicLattice_finite K ι g
  letI := numberFieldAdelicLattice_free K ι g
  let e : L ≃ₗ[ℤ] numberFieldAdelicLattice K ι g :=
    (Submodule.restrictScalarsEquiv ℤ (𝓞 K) (ι → K)
      (numberFieldAdelicLattice K ι g)).restrictScalars ℤ
  letI : Module.Finite ℤ L := Module.Finite.equiv e.symm
  letI : Module.Free ℤ L := Module.Free.of_equiv e.symm
  have hr : Module.finrank ℚ (Submodule.span ℚ
      (numberFieldAdelicLattice K ι g : Set (ι → K))) =
        Module.finrank ℤ (numberFieldAdelicLattice K ι g) :=
    (Submodule.finrank_span_eq_finrank (A := ℚ) L).trans e.finrank_eq
  apply Submodule.eq_top_of_finrank_eq
  rw [hr, numberFieldAdelicLattice_finrank K ι g, Module.finrank_pi_fintype]
  simp

end
end Dubon2026
