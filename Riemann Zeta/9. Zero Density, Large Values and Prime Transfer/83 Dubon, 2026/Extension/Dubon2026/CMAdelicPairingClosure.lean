import Dubon2026.CMAdelicTraceDualPairing
import Dubon2026.NumberFieldAdelicLatticeClosure

/-! # Extending original integral pairings to the actual adelic lattice

The proved density of the attached lattice and closedness of integral
adeles extend its integral pairings to every vector in the specified
adelic region. This removes the approximation input in the uniform
trace-dual containment needed for DUB-17's Gram determinant bound.
-/

namespace Dubon2026

noncomputable section

open NumberField IsDedekindDomain Matrix Topology
attribute [local instance] cmFiniteAdeleStarRing

variable (K : Type) [Field K] [NumberField K] [IsCMField K]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Integral original pairings extend to every vector of the exact adelic lattice region. -/
theorem cmAdelicPairing_integral_on_region (H : Matrix ι ι K) (n : ℤ)
    (g : cmFiniteAdelicUnitaryGroup K H) (x : ι → K)
    (hx : ∀ y : numberFieldAdelicLattice K ι g.val,
      IsIntegral ℤ (n • dotProduct (star x) (H.mulVec y.val)))
    (y : ι → FiniteAdeleRing (𝓞 K) K)
    (hy : y ∈ numberFieldAdelicLatticeRegion K ι g.val) :
    n • dotProduct (star (numberFieldAdelicVectorMap K ι x))
      (((algebraMap K (FiniteAdeleRing (𝓞 K) K)).mapMatrix H).mulVec y) ∈
        numberFieldIntegralFiniteAdeles K := by
  let F : (ι → FiniteAdeleRing (𝓞 K) K) → FiniteAdeleRing (𝓞 K) K :=
    fun z => n • dotProduct (star (numberFieldAdelicVectorMap K ι x))
      (((algebraMap K (FiniteAdeleRing (𝓞 K) K)).mapMatrix H).mulVec z)
  have hc : Continuous F := by
    unfold F
    simp only [dotProduct, mulVec, zsmul_eq_mul]
    exact continuous_const.mul (continuous_finsetSum _ fun i _ =>
      continuous_const.mul (continuous_finsetSum _ fun j _ =>
        continuous_const.mul (continuous_apply j)))
  have hclosed : IsClosed (F ⁻¹' (numberFieldIntegralFiniteAdeles K :
      Set (FiniteAdeleRing (𝓞 K) K))) :=
    ((numberFieldIntegralFiniteAdeles K).toAddSubgroup.isClosed_of_isOpen
      (numberFieldIntegralFiniteAdeles_isOpen K)).preimage hc
  have hr : Set.range (fun z : numberFieldAdelicLattice K ι g.val =>
      numberFieldAdelicVectorMap K ι z.val) ⊆ F ⁻¹' (numberFieldIntegralFiniteAdeles K :
        Set (FiniteAdeleRing (𝓞 K) K)) := by
    rintro _ ⟨z, rfl⟩
    change n • dotProduct (star (fun i => algebraMap K (FiniteAdeleRing (𝓞 K) K) (x i)))
      (((algebraMap K (FiniteAdeleRing (𝓞 K) K)).mapMatrix H).mulVec
        (fun i => algebraMap K (FiniteAdeleRing (𝓞 K) K) (z.val i))) ∈ numberFieldIntegralFiniteAdeles K
    rw [← cmFiniteAdelicPairing_principal K H x z.val]
    simpa only [zsmul_eq_mul, map_mul, map_intCast] using
      (numberFieldFiniteAdele_integral_iff K _).mpr (hx z)
  have h := closure_minimal hr hclosed
  rw [numberFieldAdelicLattice_closure] at h
  exact h hy

end
end Dubon2026
