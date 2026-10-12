import Mathlib.FieldTheory.Galois.GaloisClosure

/-! # The original compositum with a finite Galois field over an arbitrary base -/

namespace Dubon2026
noncomputable section

variable {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω]

/-- After adjoining the original finite Galois subfield to any
intermediate base, a genuine separable polynomial still splits and
generates the entire compositum. -/
theorem intermediateField_compositum_splitting_polynomial
    (E : IntermediateField K Ω) (F : FiniteGaloisIntermediateField K Ω) :
    ∃ q : Polynomial E, q.Separable ∧
      q.IsSplittingField E (IntermediateField.adjoin E (F.toIntermediateField : Set Ω)) := by
  obtain ⟨p, hp, hsplit⟩ := IsGalois.is_separable_splitting_field K F
  have hF := (IntermediateField.isSplittingField_iff.mp hsplit).2
  let q := p.map (algebraMap K E)
  have hroots : q.rootSet Ω = p.rootSet Ω := by
    simp [q, Set.ext_iff, Polynomial.mem_rootSet']
  have hadjoin : IntermediateField.adjoin E (F.toIntermediateField : Set Ω) =
      IntermediateField.adjoin E (q.rootSet Ω) := by
    apply IntermediateField.restrictScalars_injective K
    rw [IntermediateField.restrictScalars_adjoin_eq_sup,
      IntermediateField.restrictScalars_adjoin_eq_sup, IntermediateField.adjoin_self, hroots, ← hF]
  refine ⟨q, hp.map, ?_⟩
  rw [hadjoin]
  apply IntermediateField.adjoin_rootSet_isSplittingField
  dsimp only [q]
  rw [Polynomial.map_map, ← IsScalarTower.algebraMap_eq]
  exact Polynomial.Splits.of_algHom hsplit.splits' (IsScalarTower.toAlgHom K F Ω)

/-- The literal supremum, with its fixed base extended, is exactly
the field obtained by adjoining the original finite Galois subfield. -/
theorem intermediateField_compositum_extendScalars_eq
    (E : IntermediateField K Ω) (F : FiniteGaloisIntermediateField K Ω) :
    IntermediateField.extendScalars (show E ≤ E ⊔ F.toIntermediateField from le_sup_left) =
      IntermediateField.adjoin E (F.toIntermediateField : Set Ω) := by
  apply IntermediateField.restrictScalars_injective K
  rw [IntermediateField.extendScalars_restrictScalars,
    IntermediateField.restrictScalars_adjoin_eq_sup, IntermediateField.adjoin_self]

/-- The actual compositum E F is a finite Galois stage over E.
There is no normality or finiteness hypothesis on E over the original base. -/
def finiteGaloisCompositumOverIntermediate
    (E : IntermediateField K Ω) (F : FiniteGaloisIntermediateField K Ω) :
    FiniteGaloisIntermediateField E Ω where
  toIntermediateField := IntermediateField.extendScalars
    (show E ≤ E ⊔ F.toIntermediateField from le_sup_left)
  finiteDimensional := by
    rw [intermediateField_compositum_extendScalars_eq]
    obtain ⟨q, _, hq⟩ := intermediateField_compositum_splitting_polynomial E F
    letI := hq
    exact Polynomial.IsSplittingField.finiteDimensional _ q
  isGalois := by
    rw [intermediateField_compositum_extendScalars_eq]
    obtain ⟨q, hsep, hq⟩ := intermediateField_compositum_splitting_polynomial E F
    letI := hq
    exact IsGalois.of_separable_splitting_field hsep

/-- The constructed stage retains exactly the original supremum's elements. -/
theorem finiteGaloisCompositumOverIntermediate_coe
    (E : IntermediateField K Ω) (F : FiniteGaloisIntermediateField K Ω) :
    ((finiteGaloisCompositumOverIntermediate E F).toIntermediateField : Set Ω) =
      (E ⊔ F.toIntermediateField : IntermediateField K Ω) := rfl

end
end Dubon2026
