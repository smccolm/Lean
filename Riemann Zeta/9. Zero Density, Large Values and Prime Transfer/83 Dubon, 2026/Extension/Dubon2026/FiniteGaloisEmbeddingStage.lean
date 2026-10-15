import Mathlib.FieldTheory.Galois.GaloisClosure
import Mathlib.FieldTheory.IsSepClosed

/-! # Actual finite Galois images inside the original separably closed field -/

namespace Dubon2026
noncomputable section

variable {K L Ω : Type} [Field K] [Field L] [Field Ω]
  [Algebra K L] [Algebra K Ω] [FiniteDimensional K L] [IsGalois K L]

/-- The actual image of a displayed embedding, with its finite and Galois
properties transported through the genuine range equivalence. -/
def finiteGaloisEmbeddingStage (i : L →ₐ[K] Ω) : FiniteGaloisIntermediateField K Ω := by
  let e : L ≃ₐ[K] i.fieldRange := AlgEquiv.ofInjective i i.injective
  exact
    { toIntermediateField := i.fieldRange
      finiteDimensional := e.toLinearEquiv.finiteDimensional
      isGalois := IsGalois.of_algEquiv e }

/-- The displayed finite extension is equivalent to its actual image stage. -/
def finiteGaloisEmbeddingStageEquiv (i : L →ₐ[K] Ω) :
    L ≃ₐ[K] finiteGaloisEmbeddingStage i :=
  AlgEquiv.ofInjective i i.injective

/-- The range equivalence followed by the original inclusion is exactly the
displayed field embedding, on every original coefficient. -/
theorem finiteGaloisEmbeddingStageEquiv_coe (i : L →ₐ[K] Ω) (x : L) :
    ((finiteGaloisEmbeddingStageEquiv i x : finiteGaloisEmbeddingStage i) : Ω) = i x :=
  rfl

/-- Two realizations of the same finite Galois extension in one ambient field
have the same actual intermediate field. Normality is the essential input:
the equivalence between the two images, followed by the second inclusion, has
field range equal to both images. -/
theorem finiteGaloisEmbeddingStage_eq (i j : L →ₐ[K] Ω) :
    finiteGaloisEmbeddingStage i = finiteGaloisEmbeddingStage j := by
  let Ei := finiteGaloisEmbeddingStage i
  let Ej := finiteGaloisEmbeddingStage j
  let e : Ei ≃ₐ[K] Ej :=
    (finiteGaloisEmbeddingStageEquiv i).symm.trans
      (finiteGaloisEmbeddingStageEquiv j)
  let f : Ei →ₐ[K] Ω := Ej.val.comp e.toAlgHom
  have hEi : f.fieldRange = Ei.toIntermediateField :=
    AlgHom.fieldRange_of_normal f
  have hEj : f.fieldRange = Ej.toIntermediateField := by
    apply le_antisymm
    · rintro x ⟨y, rfl⟩
      exact (e y).property
    · intro x hx
      obtain ⟨y, hy⟩ := e.surjective ⟨x, hx⟩
      refine ⟨y, ?_⟩
      change (e y : Ω) = x
      exact congrArg Subtype.val hy
  apply FiniteGaloisIntermediateField.val_injective
  exact hEi.symm.trans hEj

/-- The automorphism of the first actual image that carries the first
realization to the second. The equality of the two normal image fields turns
the natural equivalence between them into an automorphism of one fixed stage. -/
def finiteGaloisEmbeddingStageAut (i j : L →ₐ[K] Ω) :
    Gal(finiteGaloisEmbeddingStage i / K) :=
  let Ei := finiteGaloisEmbeddingStage i
  let Ej := finiteGaloisEmbeddingStage j
  let e : Ei ≃ₐ[K] Ej :=
    (finiteGaloisEmbeddingStageEquiv i).symm.trans
      (finiteGaloisEmbeddingStageEquiv j)
  e.trans (IntermediateField.equivOfEq <|
    congrArg FiniteGaloisIntermediateField.toIntermediateField
      (finiteGaloisEmbeddingStage_eq i j).symm)

/-- The stage automorphism between two realizations sends every displayed
coefficient of the first realization to the corresponding coefficient of the
second realization, as literal elements of the common ambient field. -/
theorem finiteGaloisEmbeddingStageAut_apply (i j : L →ₐ[K] Ω) (x : L) :
    ((finiteGaloisEmbeddingStageAut i j
        (finiteGaloisEmbeddingStageEquiv i x) : finiteGaloisEmbeddingStage i) : Ω) =
      j x := by
  simp only [finiteGaloisEmbeddingStageAut, AlgEquiv.trans_apply,
    AlgEquiv.symm_apply_apply, IntermediateField.equivOfEq_apply]
  rfl

attribute [local instance] IsCyclic.commGroup

/-- In a cyclic actual image, an automorphism action known in one realization
holds in every other realization. The transport automorphism commutes with the
given action, so no naturality theorem for the construction of that action is
needed. -/
theorem finiteGaloisEmbeddingStage_action_transport
    (i j : L →ₐ[K] Ω) [IsCyclic Gal(finiteGaloisEmbeddingStage i / K)]
    (g : Gal(finiteGaloisEmbeddingStage i / K)) (x y : L)
    (h : ((g (finiteGaloisEmbeddingStageEquiv i x) :
      finiteGaloisEmbeddingStage i) : Ω) = i y) :
    ((g (finiteGaloisEmbeddingStageAut i j
        (finiteGaloisEmbeddingStageEquiv i x)) :
      finiteGaloisEmbeddingStage i) : Ω) = j y := by
  let τ := finiteGaloisEmbeddingStageAut i j
  have hcomm : g * τ = τ * g := mul_comm g τ
  calc
    ((g (τ (finiteGaloisEmbeddingStageEquiv i x)) :
        finiteGaloisEmbeddingStage i) : Ω) =
        ((τ (g (finiteGaloisEmbeddingStageEquiv i x)) :
          finiteGaloisEmbeddingStage i) : Ω) := by
            exact congrArg Subtype.val
              (DFunLike.congr_fun hcomm (finiteGaloisEmbeddingStageEquiv i x))
    _ = ((τ (finiteGaloisEmbeddingStageEquiv i y) :
          finiteGaloisEmbeddingStage i) : Ω) := by
            have hsub : g (finiteGaloisEmbeddingStageEquiv i x) =
                finiteGaloisEmbeddingStageEquiv i y := Subtype.ext h
            rw [hsub]
    _ = j y := finiteGaloisEmbeddingStageAut_apply i j y

/-- An actual finite Galois extension occurs inside the original separably
closed field, with the same original degree. This is an algebraic realization;
it does not yet transfer the original local topology or integer ring. -/
theorem finiteGalois_exists_original_stage [IsSepClosed Ω] :
    ∃ E : FiniteGaloisIntermediateField K Ω,
      Nonempty (L ≃ₐ[K] E) ∧ Module.finrank K E = Module.finrank K L := by
  let i : L →ₐ[K] Ω := IsSepClosed.lift
  let e := finiteGaloisEmbeddingStageEquiv i
  exact ⟨finiteGaloisEmbeddingStage i, ⟨e⟩, e.toLinearEquiv.finrank_eq.symm⟩

end
end Dubon2026
