import Dubon2026.ScaledLatticeProducts
import Mathlib.RingTheory.Norm.Transitivity
import Mathlib.RingTheory.Trace.Basic

/-! # The actual norm minus its trace term gains a lattice factor -/

namespace Dubon2026
noncomputable section

open scoped BigOperators

/-- The nonlinear error of an original finite product lies in the smaller
additive subgroup whenever every pair of original factors has that property. -/
theorem finite_product_one_add_lattice_error
    {S ι : Type*} [CommRing S] (A B : AddSubgroup S)
    (hBA : B ≤ A) (hmul : ∀ x ∈ A, ∀ y ∈ A, x * y ∈ B)
    (s : Finset ι) (f : ι → S) (hf : ∀ i ∈ s, f i ∈ A) :
    (∏ i ∈ s, (1 + f i)) - 1 ∈ A ∧
      (∏ i ∈ s, (1 + f i)) - 1 - ∑ i ∈ s, f i ∈ B := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    have hfi : f i ∈ A := hf i (Finset.mem_insert_self i s)
    have hfs : ∀ j ∈ s, f j ∈ A := fun j hj => hf j (Finset.mem_insert_of_mem hj)
    obtain ⟨hp, he⟩ := ih hfs
    simp only [Finset.prod_insert hi, Finset.sum_insert hi]
    constructor
    · have hid : (1 + f i) * (∏ j ∈ s, (1 + f j)) - 1 =
          f i + ((∏ j ∈ s, (1 + f j)) - 1) +
            f i * ((∏ j ∈ s, (1 + f j)) - 1) := by ring
      rw [hid]
      exact A.add_mem (A.add_mem hfi hp) (hBA (hmul _ hfi _ hp))
    · have hid : (1 + f i) * (∏ j ∈ s, (1 + f j)) - 1 -
          (f i + ∑ j ∈ s, f j) =
          ((∏ j ∈ s, (1 + f j)) - 1 - ∑ j ∈ s, f j) +
            f i * ((∏ j ∈ s, (1 + f j)) - 1) := by ring
      rw [hid]
      exact B.add_mem he (hmul _ hfi _ hp)

/-- For the actual Galois field norm, the error after the original trace
term lies in `π` times the same original scaled lattice. The original normal
lattice bounds and Galois stability supply every factor of the norm product. -/
theorem galoisNorm_small_lattice_error
    (R K L : Type) [CommRing R] [Field K] [Field L]
    [Algebra R K] [Algebra K L] [Algebra R L] [IsScalarTower R K L]
    [FiniteDimensional K L] [IsGalois K L]
    (A : Submodule R L) (B : Subring L) (π : R) (n : ℕ)
    (hupper : ∀ x ∈ A, x ∈ B) (hlower : ∀ x ∈ B, π ^ n • x ∈ A)
    (hstable : ∀ σ : Gal(L/K), ∀ x ∈ A, σ x ∈ A)
    {x : L} (hx : x ∈ scalarLatticeImage A (π ^ (n + 1))) :
    algebraMap K L (Algebra.norm K (1 + x)) - 1 -
        algebraMap K L (Algebra.trace K L x) ∈
      scalarLatticeImage (scalarLatticeImage A (π ^ (n + 1))) π := by
  classical
  let Λ := scalarLatticeImage A (π ^ (n + 1))
  let Δ := scalarLatticeImage Λ π
  have hDA : Δ ≤ Λ := by
    intro z hz
    obtain ⟨a, ha, rfl⟩ := (mem_scalarLatticeImage Λ π z).mp hz
    exact Λ.smul_mem π ha
  have hm : ∀ a ∈ Λ.toAddSubgroup, ∀ b ∈ Λ.toAddSubgroup, a * b ∈ Δ.toAddSubgroup := by
    intro a ha b hb
    obtain ⟨z, hz, he⟩ := scalarLatticeImage_product_gain A B π n hupper hlower ha hb
    exact (mem_scalarLatticeImage Λ π (a * b)).mpr ⟨z, hz, he.symm⟩
  have hg (σ : Gal(L/K)) : σ x ∈ Λ := by
    obtain ⟨a, ha, rfl⟩ := (mem_scalarLatticeImage A _ x).mp hx
    refine (mem_scalarLatticeImage A _ _).mpr ⟨σ a, hstable σ a ha, ?_⟩
    exact ((σ.restrictScalars R).toLinearMap.map_smul (π ^ (n + 1)) a).symm
  have he := (finite_product_one_add_lattice_error Λ.toAddSubgroup Δ.toAddSubgroup
    hDA hm Finset.univ (fun σ : Gal(L/K) => σ x) (fun σ _ => hg σ)).2
  rw [Algebra.norm_eq_prod_automorphisms, trace_eq_sum_automorphisms]
  simpa only [map_add, map_one] using he

end
end Dubon2026
