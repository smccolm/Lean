import Dubon2026.NumberFieldAdelicLattice
import Dubon2026.NumberFieldFiniteAdeleDensity
import Mathlib.Topology.Instances.Matrix
import Mathlib.Topology.Algebra.OpenSubgroup

/-! # The actual adelic closure of the attached lattice

Strong approximation identifies the closure of principal vectors from
the attached lattice with the exact adelic region cut out by inverse
matrix integrality. This is the source-entry bridge for DUB-17's local
trace-lattice comparison, not a separately assumed approximation property.
-/

namespace Dubon2026

noncomputable section

open NumberField IsDedekindDomain Topology
open scoped NumberField

variable (K : Type*) [Field K] [NumberField K]
variable (ι : Type*) [Fintype ι] [DecidableEq ι]

/-- The genuine adelic integral region transformed by the given invertible matrix. -/
def numberFieldAdelicLatticeRegion
    (g : Matrix.GeneralLinearGroup ι (FiniteAdeleRing (𝓞 K) K)) :
    Set (ι → FiniteAdeleRing (𝓞 K) K) :=
  {y | ∀ i, (g⁻¹).val.mulVec y i ∈ numberFieldIntegralFiniteAdeles K}

/-- The actual transformed adelic integral region is open. -/
theorem numberFieldAdelicLatticeRegion_isOpen
    (g : Matrix.GeneralLinearGroup ι (FiniteAdeleRing (𝓞 K) K)) :
    IsOpen (numberFieldAdelicLatticeRegion K ι g) := by
  have hc : Continuous (g⁻¹).val.mulVec := by
    apply continuous_pi
    intro i
    exact continuous_finsetSum _ fun j _ => continuous_const.mul (continuous_apply j)
  have ho := (isOpen_set_pi Set.finite_univ
    (fun (_ : ι) _ => numberFieldIntegralFiniteAdeles_isOpen K)).preimage hc
  simpa only [numberFieldAdelicLatticeRegion, Set.preimage_setOf_eq,
    Set.pi, Set.mem_univ, forall_const] using ho

/-- The actual transformed adelic integral region is closed. -/
theorem numberFieldAdelicLatticeRegion_isClosed
    (g : Matrix.GeneralLinearGroup ι (FiniteAdeleRing (𝓞 K) K)) :
    IsClosed (numberFieldAdelicLatticeRegion K ι g) := by
  have hc (i : ι) : Continuous (fun y => (g⁻¹).val.mulVec y i) :=
    continuous_finsetSum _ fun j _ => continuous_const.mul (continuous_apply j)
  have h := isClosed_iInter fun i =>
    ((numberFieldIntegralFiniteAdeles K).toAddSubgroup.isClosed_of_isOpen
      (numberFieldIntegralFiniteAdeles_isOpen K)).preimage (hc i)
  simpa only [numberFieldAdelicLatticeRegion, Set.setOf_forall] using h

/-- The principal vectors from the actual attached lattice are dense in its exact adelic region. -/
theorem numberFieldAdelicLattice_closure
    (g : Matrix.GeneralLinearGroup ι (FiniteAdeleRing (𝓞 K) K)) :
    closure (Set.range (fun x : numberFieldAdelicLattice K ι g =>
      numberFieldAdelicVectorMap K ι x.val)) = numberFieldAdelicLatticeRegion K ι g := by
  apply Set.Subset.antisymm
  · apply closure_minimal _ (numberFieldAdelicLatticeRegion_isClosed K ι g)
    rintro _ ⟨x, rfl⟩
    exact (numberFieldAdelicLattice_mem_iff K ι g x.val).mp x.property
  · intro y hy
    have h := (numberFieldVectors_dense_finiteAdeles K ι).subset_closure_image_preimage_of_isOpen
      (numberFieldAdelicLatticeRegion_isOpen K ι g) hy
    apply closure_mono _ h
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨⟨x, (numberFieldAdelicLattice_mem_iff K ι g x).mpr hx⟩, rfl⟩

end
end Dubon2026
