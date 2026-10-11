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
