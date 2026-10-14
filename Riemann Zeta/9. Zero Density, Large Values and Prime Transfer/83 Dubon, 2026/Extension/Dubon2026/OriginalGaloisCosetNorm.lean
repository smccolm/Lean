import Dubon2026.GaloisFixingSubgroupTopology
import Mathlib.RingTheory.Norm.Transitivity

/-! # The original Galois coset product is the actual field norm

The fixing cosets parametrize the original field embeddings by their actual
representatives. The pinned embedding formula then identifies their product
with the original norm. This is the coefficient bridge for carry
corestriction and DUB-17's normalized cyclotomic reciprocity calculation.
-/
namespace Dubon2026
noncomputable section
open scoped BigOperators

variable (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω]
  (E : IntermediateField K Ω)

/-- Restrict the literal representative of a genuine fixing coset to the original field. -/
def originalGaloisCosetEmbedding (q : Gal(Ω/K) ⧸ E.fixingSubgroup) : E →ₐ[K] Ω :=
  q.out.toAlgHom.comp E.val

omit [IsGalois K Ω] in
/-- The original coset embedding of an automorphism retains its literal restriction. -/
theorem originalGaloisCosetEmbedding_mk (g : Gal(Ω/K)) :
    originalGaloisCosetEmbedding K Ω E (QuotientGroup.mk g) = g.toAlgHom.comp E.val := by
  obtain ⟨s, hs⟩ := QuotientGroup.mk_out_eq_mul (s := E.fixingSubgroup) g
  ext x
  change (QuotientGroup.mk g : Gal(Ω/K) ⧸ E.fixingSubgroup).out (x : Ω) = g (x : Ω)
  rw [hs]
  change g (s.val (x : Ω)) = g (x : Ω)
  rw [(IntermediateField.mem_fixingSubgroup_iff E s.val).mp s.property x x.property]

omit [IsGalois K Ω] in
/-- Two original fixing cosets agree exactly when their original field embeddings agree. -/
theorem originalGaloisCosetEmbedding_injective :
    Function.Injective (originalGaloisCosetEmbedding K Ω E) := by
  intro q r h
  have he : (q.out : Gal(Ω/K) ⧸ E.fixingSubgroup) = r.out := by
    apply QuotientGroup.eq.mpr
    apply (IntermediateField.mem_fixingSubgroup_iff E _).mpr
    intro x hx
    have hv := congrArg (fun f : E →ₐ[K] Ω => f ⟨x, hx⟩) h
    change q.out x = r.out x at hv
    change q.out.symm (r.out x) = x
    rw [← hv, AlgEquiv.symm_apply_apply]
  simpa only [QuotientGroup.out_eq'] using he

/-- Every original field embedding is represented by an actual automorphism coset. -/
theorem originalGaloisCosetEmbedding_surjective :
    Function.Surjective (originalGaloisCosetEmbedding K Ω E) := by
  intro f
  let g : Gal(Ω/K) := AlgEquiv.ofBijective (f.liftNormal Ω)
    (AlgHom.normal_bijective K Ω Ω _)
  refine ⟨QuotientGroup.mk g, ?_⟩
  rw [originalGaloisCosetEmbedding_mk]
  ext x
  exact f.liftNormal_commutes Ω x

/-- The actual embedding parametrization of the genuine original fixing cosets. -/
def originalGaloisCosetEmbeddingEquiv : (Gal(Ω/K) ⧸ E.fixingSubgroup) ≃ (E →ₐ[K] Ω) :=
  Equiv.ofBijective (originalGaloisCosetEmbedding K Ω E)
    ⟨originalGaloisCosetEmbedding_injective K Ω E,
      originalGaloisCosetEmbedding_surjective K Ω E⟩

variable [FiniteDimensional K E] [IsAlgClosed Ω]
  [Fintype (Gal(Ω/K) ⧸ E.fixingSubgroup)]

/-- The literal product over original fixing-coset representatives equals the original field norm in the same closure. -/
theorem originalGaloisCosetProduct_eq_norm (x : E) :
    (∏ q : Gal(Ω/K) ⧸ E.fixingSubgroup, q.out (x : Ω)) =
      algebraMap K Ω (Algebra.norm K x) := by
  rw [Algebra.norm_eq_prod_embeddings K Ω]
  exact Equiv.prod_comp (originalGaloisCosetEmbeddingEquiv K Ω E) (fun f => f x)

end
end Dubon2026
