import Dubon2026.FiniteGaloisEmbeddingStage
import Dubon2026.UnramifiedGaloisStageUnion

/-! # The scalar criterion's original stage inside the arithmetic union

Reuse the actual finite Galois image of the original stage inclusion.
The literal ambient-value identity places a descended source stage below
it. This is the field edge needed to compare DUB-17's source cup with the
same enlarged stage used by the proved scalar relation criterion.
-/
namespace Dubon2026
noncomputable section
open scoped NumberField
variable {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] [NumberField K]
  (a : 𝓞 K)

/-- The original arithmetic stage, realized by its actual inclusion in the
same unramified union. -/
def originalUnramifiedStageInUnion (F : OriginalUnramifiedGaloisStage (Ω := Ω) a) :
    FiniteGaloisIntermediateField K (originalUnramifiedGaloisUnion (Ω := Ω) a) :=
  finiteGaloisEmbeddingStage (IntermediateField.inclusion (originalUnramifiedGaloisStage_le_union a F))

/-- The original stage and its actual image in the union are equivalent
through the literal inclusion. -/
def originalUnramifiedStageInUnionEquiv (F : OriginalUnramifiedGaloisStage (Ω := Ω) a) :
    F.val ≃ₐ[K] originalUnramifiedStageInUnion a F :=
  finiteGaloisEmbeddingStageEquiv (IntermediateField.inclusion (originalUnramifiedGaloisStage_le_union a F))

omit [NumberField K] in
/-- The image equivalence retains every original ambient-field element. -/
theorem originalUnramifiedStageInUnionEquiv_coe
    (F : OriginalUnramifiedGaloisStage (Ω := Ω) a) (x : F.val) :
    (((originalUnramifiedStageInUnionEquiv a F x).val :
      originalUnramifiedGaloisUnion (Ω := Ω) a) : Ω) = (x : Ω) := rfl

omit [NumberField K] in
/-- Inclusion of original arithmetic stages is preserved inside the same union. -/
theorem originalUnramifiedStageInUnion_mono
    (F L : OriginalUnramifiedGaloisStage (Ω := Ω) a)
    (hFL : F.val.toIntermediateField ≤ L.val.toIntermediateField) :
    originalUnramifiedStageInUnion a F ≤ originalUnramifiedStageInUnion a L := by
  intro x hx
  obtain ⟨y, rfl⟩ := hx
  exact ⟨⟨y.val, hFL y.property⟩, rfl⟩

omit [NumberField K] in
/-- An actual embedding with the original ambient values places the
descended finite source stage below the realized scalar-criterion stage. -/
theorem originalUnramifiedStageInUnion_contains_embedded
    (P : FiniteGaloisIntermediateField K (originalUnramifiedGaloisUnion (Ω := Ω) a))
    (F : OriginalUnramifiedGaloisStage (Ω := Ω) a) (i : P →ₐ[K] F.val)
    (hi : ∀ x : P, (i x : Ω) = (x.val : Ω)) :
    P ≤ originalUnramifiedStageInUnion a F := by
  intro x hx
  refine ⟨i ⟨x, hx⟩, ?_⟩
  exact Subtype.ext (hi ⟨x, hx⟩)

omit [NumberField K] in
/-- The composed image embedding is the original intermediate-field
inclusion, not an independently chosen realization. -/
theorem originalUnramifiedStageInUnion_embedding_eq_inclusion
    (P : FiniteGaloisIntermediateField K (originalUnramifiedGaloisUnion (Ω := Ω) a))
    (F : OriginalUnramifiedGaloisStage (Ω := Ω) a) (i : P →ₐ[K] F.val)
    (hi : ∀ x : P, (i x : Ω) = (x.val : Ω)) :
    (originalUnramifiedStageInUnionEquiv a F).toAlgHom.comp i =
      IntermediateField.inclusion (originalUnramifiedStageInUnion_contains_embedded a P F i hi) := by
  ext x
  exact hi x

end
end Dubon2026
