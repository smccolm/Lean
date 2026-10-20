import Dubon2026.NumberFieldAdelicLatticeClosure
import Dubon2026.NumberFieldFiniteAdelicMatrixProjection

/-! # Recovery of the original completed lattice at every finite place

The closure of the actual global lattice in each original completion is
exactly the image of the completed integral vectors under the specified
adelic matrix at that place. This discharges DUB-17's local recovery input
for the trace-lattice route; uniform integral trace determinant control
and finite CM action structures are still separate obligations.
-/

namespace Dubon2026

noncomputable section

open NumberField IsDedekindDomain Topology
open scoped NumberField

variable (K : Type*) [Field K] [NumberField K]
variable (ι : Type*) [Fintype ι] [DecidableEq ι]

/-- Projection commutes with the actual finite adelic matrix action on vectors. -/
theorem numberFieldAdelicMatrix_mulVec_projection
    (g : Matrix.GeneralLinearGroup ι (FiniteAdeleRing (𝓞 K) K))
    (v : HeightOneSpectrum (𝓞 K)) (x : ι → FiniteAdeleRing (𝓞 K) K) :
    (fun i => (g.val.mulVec x i) v) =
      (numberFieldFiniteAdelicMatrixProjection K ι v g).val.mulVec (fun i => x i v) := by
  funext i
  exact RingHom.map_mulVec (RestrictedProduct.evalRingHom
    (fun w : HeightOneSpectrum (𝓞 K) => w.adicCompletion K) v) g.val x i

/-- The prescribed local lattice, expressed by inverse-matrix integrality in the actual completion. -/
def numberFieldLocalAdelicLatticeRegion
    (g : Matrix.GeneralLinearGroup ι (FiniteAdeleRing (𝓞 K) K))
    (v : HeightOneSpectrum (𝓞 K)) : Set (ι → v.adicCompletion K) :=
  {y | ∀ i, ((numberFieldFiniteAdelicMatrixProjection K ι v g)⁻¹).val.mulVec y i ∈
    v.adicCompletionIntegers K}

/-- The prescribed lattice is closed in the original finite completion. -/
theorem numberFieldLocalAdelicLatticeRegion_isClosed
    (g : Matrix.GeneralLinearGroup ι (FiniteAdeleRing (𝓞 K) K))
    (v : HeightOneSpectrum (𝓞 K)) : IsClosed (numberFieldLocalAdelicLatticeRegion K ι g v) := by
  have hc (i : ι) : Continuous (fun y =>
      ((numberFieldFiniteAdelicMatrixProjection K ι v g)⁻¹).val.mulVec y i) :=
    continuous_finsetSum _ fun j _ => continuous_const.mul (continuous_apply j)
  have h := isClosed_iInter fun i =>
    (Valued.isClosed_valuationSubring (v.adicCompletion K)).preimage (hc i)
  simpa only [numberFieldLocalAdelicLatticeRegion, Set.setOf_forall] using h

/-- The actual adelic integral region projects onto the full prescribed lattice at every place. -/
theorem numberFieldAdelicLatticeRegion_projection
    (g : Matrix.GeneralLinearGroup ι (FiniteAdeleRing (𝓞 K) K))
    (v : HeightOneSpectrum (𝓞 K)) :
    (fun x : ι → FiniteAdeleRing (𝓞 K) K => fun i => x i v) ''
      numberFieldAdelicLatticeRegion K ι g = numberFieldLocalAdelicLatticeRegion K ι g v := by
  classical
  apply Set.Subset.antisymm
  · rintro _ ⟨x, hx, rfl⟩ i
    have h := numberFieldAdelicMatrix_mulVec_projection K ι g⁻¹ v x
    rw [map_inv] at h
    have hi := hx i v
    change ((g⁻¹).val.mulVec x i) v ∈ v.adicCompletionIntegers K at hi
    rwa [congrFun h i] at hi
  · intro y hy
    let u : ι → v.adicCompletion K :=
      ((numberFieldFiniteAdelicMatrixProjection K ι v g)⁻¹).val.mulVec y
    let z : ι → FiniteAdeleRing (𝓞 K) K := fun i =>
      numberFieldIntegralFiniteAdeleMap K
        (Function.update (fun w : HeightOneSpectrum (𝓞 K) => (0 : w.adicCompletionIntegers K))
          v ⟨u i, hy i⟩)
    have hz (i : ι) : z i ∈ numberFieldIntegralFiniteAdeles K := by
      intro w
      exact (Function.update
        (fun w : HeightOneSpectrum (𝓞 K) => (0 : w.adicCompletionIntegers K)) v ⟨u i, hy i⟩ w).property
    have hzv : (fun i => z i v) = u := by
      funext i
      change ((Function.update
        (fun w : HeightOneSpectrum (𝓞 K) => (0 : w.adicCompletionIntegers K)) v ⟨u i, hy i⟩ v) :
        v.adicCompletion K) = u i
      rw [Function.update_self]
    refine ⟨g.val.mulVec z, ?_, ?_⟩
    · change ∀ i, (g⁻¹).val.mulVec (g.val.mulVec z) i ∈ numberFieldIntegralFiniteAdeles K
      rw [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]
      exact hz
    · change (fun i => (g.val.mulVec z i) v) = y
      rw [numberFieldAdelicMatrix_mulVec_projection, hzv]
      change (numberFieldFiniteAdelicMatrixProjection K ι v g).val.mulVec
        (((numberFieldFiniteAdelicMatrixProjection K ι v g)⁻¹).val.mulVec y) = y
      rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]

/-- The actual global lattice recovers exactly the prescribed completed lattice at every original place. -/
theorem numberFieldAdelicLattice_local_closure
    (g : Matrix.GeneralLinearGroup ι (FiniteAdeleRing (𝓞 K) K))
    (v : HeightOneSpectrum (𝓞 K)) :
    closure (Set.range (fun x : numberFieldAdelicLattice K ι g =>
      fun i => algebraMap K (v.adicCompletion K) (x.val i))) =
        numberFieldLocalAdelicLatticeRegion K ι g v := by
  let P : (ι → FiniteAdeleRing (𝓞 K) K) → (ι → v.adicCompletion K) := fun x i => x i v
  have hc : Continuous P := continuous_pi fun i =>
    (RestrictedProduct.continuous_eval v).comp (continuous_apply i)
  have he : P '' Set.range (fun x : numberFieldAdelicLattice K ι g =>
      numberFieldAdelicVectorMap K ι x.val) = Set.range
        (fun x : numberFieldAdelicLattice K ι g =>
          fun i => algebraMap K (v.adicCompletion K) (x.val i)) := by
    ext y
    constructor
    · rintro ⟨_, ⟨x, rfl⟩, rfl⟩
      exact ⟨x, rfl⟩
    · rintro ⟨x, rfl⟩
      exact ⟨numberFieldAdelicVectorMap K ι x.val, ⟨x, rfl⟩, rfl⟩
  apply Set.Subset.antisymm
  · apply closure_minimal _ (numberFieldLocalAdelicLatticeRegion_isClosed K ι g v)
    rw [← he, ← numberFieldAdelicLatticeRegion_projection K ι g v]
    apply Set.image_mono
    rintro _ ⟨x, rfl⟩
    exact (numberFieldAdelicLattice_mem_iff K ι g x.val).mp x.property
  · rw [← numberFieldAdelicLatticeRegion_projection K ι g v,
      ← numberFieldAdelicLattice_closure K ι g, ← he]
    exact image_closure_subset_closure_image hc

end
end Dubon2026
