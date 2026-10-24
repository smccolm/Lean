import Dubon2026.SourceEllipticCharTwoEmbeddingKernel
import Dubon2026.SourceEllipticFullTorsionNonemptyCyclic
import Dubon2026.SourceCoordinateEmbeddingFixedFieldMap

/-! DUB-17/18 -> characteristic-two genus/Picard -> wild different bound.
The actual order-twelve inertia sign quotient fixes original modular
embeddings. Existing coordinate fixing-field and normal-place order proofs
provide the finite Galois auxiliary field; full census data is not assumed. -/
namespace Dubon2026.SourceEllipticDivisionField
open WeierstrassCurve SourceCurve SourceEllipticCharTwo
open SourceFunctionField SourceFunctionField.CoefficientPresentation
noncomputable section
attribute [local instance] SourceEllipticCharTwo.charTwoSignSubgroup_normal

theorem exists_char_two_modular_normal_field
    (K Ω : Type*) [Field K] [IsAlgClosed K] [DecidableEq K]
    [Field Ω] [IsAlgClosed Ω] [DecidableEq Ω]
    [Algebra (RatFunc K) Ω] [Algebra K Ω] [IsScalarTower K (RatFunc K) Ω]
    [Algebra.IsAlgebraic (RatFunc K) Ω] [DecidableEq (RatFunc K)]
    [CharP K 2] (N : ℕ) (hNK : (N : K) ≠ 0) :
    ∃ M : IntermediateField (RatFunc K) Ω,
      FiniteDimensional (RatFunc K) M ∧ IsGalois (RatFunc K) M ∧
      ∃ L : IntermediateField (RatFunc K) M,
        FiniteDimensional (RatFunc K) L ∧ IsGalois (RatFunc K) L ∧
        ∃ ι : modularFunctionFieldCoeff N K →ₐ[K] L,
          ι (jCoeff N K) = algebraMap (RatFunc K) L RatFunc.X ∧
          ∃ (v : Place K M)
            (π : v.toValuationSubring.inertiaSubgroup (RatFunc K) →* ((MulAction.stabilizer (VariableChange K) (ofJ0 K)) ⧸ charTwoSignSubgroup)),
            0 < v.ord (algebraMap (RatFunc K) M RatFunc.X) ∧
            Nat.card (((MulAction.stabilizer (VariableChange K) (ofJ0 K)) ⧸ charTwoSignSubgroup)) = 12 ∧
            ∀ σ, π σ = 1 → ∀ a : L, σ.val.val (a : M) = a := by
  obtain ⟨M, hfd, hgal, hcard, v, π, hv, hperm, Φ, _, hker⟩ :=
    exists_char_two_exceptional_embedding_kernel K Ω N hNK
  letI := hfd
  letI := hgal
  have hNM : (N : M) ≠ 0 := by
    simpa only [map_natCast] using (_root_.map_ne_zero (algebraMap K M)).mpr hNK
  obtain ⟨S⟩ := SourceEllipticVelu.nonempty_cyclic_subgroups_of_full_torsion (L := Ω)
    ((ofJ (RatFunc.X : RatFunc K)).baseChange M) N hNM hcard
  let ψ := Φ S
  let L := coordinateEmbeddingFixingField (K := K) (M := M) (jCoeff N K)
  let ι := coordinateEmbeddingIntoFixingField (jCoeff N K) ψ.val ψ.property
  refine ⟨M, hfd, hgal, L, inferInstance,
    coordinateEmbedding_fixingField_isGalois (jCoeff N K), ι,
    coordinateEmbeddingIntoFixingField_coordinate (jCoeff N K) ψ.val ψ.property,
    v, π, hv, hperm, ?_⟩
  intro σ hσ a
  exact coordinateEmbedding_fixingField_fixed (jCoeff N K) σ.val.val (hker σ hσ) a

end
end Dubon2026.SourceEllipticDivisionField
