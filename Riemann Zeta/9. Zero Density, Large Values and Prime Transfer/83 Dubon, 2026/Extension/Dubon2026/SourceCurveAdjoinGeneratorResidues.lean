import Dubon2026.SourceCurveGeneratorGlobalResidues

/-! Apply the rational-generator residue theorem to the literal field
adjoined by a transcendental coordinate. This is the exact base field in
the modular j-coordinate trace transfer for DUB-17/18 global residues. -/

noncomputable section

namespace Dubon2026.SourceCurve

open IntermediateField

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

/-- The actual adjoined coordinate generates its own intermediate field. -/
theorem adjoin_simple_gen_eq_top (t : F) :
    IntermediateField.adjoin K ({AdjoinSimple.gen K t} : Set K⟮t⟯) = ⊤ := by
  apply (IntermediateField.map_injective (K⟮t⟯).val)
  rw [IntermediateField.adjoin_map, Set.image_singleton,
    ← AlgHom.fieldRange_eq_map, IntermediateField.fieldRange_val]
  rfl

/-- Global Tate residues vanish on the actual transcendental-coordinate field. -/
theorem sum_tateResidue_adjoin_generator_eq_zero [IsAlgClosed K]
    (t : F) (ht : Transcendental K t) (f : K⟮t⟯) :
    (∑ᶠ v : Place K K⟮t⟯, v.tateResidue f (AdjoinSimple.gen K t)) = 0 := by
  have ht' : Transcendental K (AdjoinSimple.gen K t) :=
    (transcendental_algebraMap_iff (algebraMap K⟮t⟯ F).injective).mp ht
  exact sum_tateResidue_generator_eq_zero _ ht' (adjoin_simple_gen_eq_top t) f

end Dubon2026.SourceCurve
