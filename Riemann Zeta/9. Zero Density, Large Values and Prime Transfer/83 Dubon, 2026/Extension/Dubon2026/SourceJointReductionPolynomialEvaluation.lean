import Dubon2026.SourceReductionEquationSpecialization

/-! DUB-17/18 -> Kummer genus inequality -> monic residue-chart torsion.
Polynomial evaluation commutes with the constructed reduction map. Native
homomorphism evaluation and the existing constant-map identities provide
the integral lift and its exact residue, with no new residue-map interface. -/
namespace Dubon2026.SourceCurve.RegularProlongation.Joint
noncomputable section
open IsLocalRing Polynomial
variable {L F Fbar : Type*} [Field L] {A : ValuationSubring L}
  [Field F] [Algebra L F] [Field Fbar] [Algebra (ResidueField A) Fbar]

theorem eval₂_mem_integers (R : RegularProlongation A F Fbar)
    (q : Polynomial A) (f : F) (hf : f ∈ R.integers) :
    q.eval₂ ((algebraMap L F).comp A.subtype) f ∈ R.integers := by
  have h := Polynomial.hom_eval₂ q (constHom R) R.integers.subtype ⟨f, hf⟩
  rw [subtype_comp_constHom] at h
  exact h ▸ (q.eval₂ (constHom R) ⟨f, hf⟩).2

theorem eval₂_mk (R : RegularProlongation A F Fbar)
    (q : Polynomial A) (f : F) (hf : f ∈ R.integers) :
    (⟨_, eval₂_mem_integers R q f hf⟩ : R.integers) =
      q.eval₂ (constHom R) ⟨f, hf⟩ := by
  apply Subtype.ext
  have h := Polynomial.hom_eval₂ q (constHom R) R.integers.subtype ⟨f, hf⟩
  rw [subtype_comp_constHom] at h
  exact h.symm

theorem residue_eval₂ (R : RegularProlongation A F Fbar)
    (q : Polynomial A) (f : F) (hf : f ∈ R.integers) :
    R.residue ⟨_, eval₂_mem_integers R q f hf⟩ =
      Polynomial.aeval (R.residue ⟨f, hf⟩) (q.map (IsLocalRing.residue A)) := by
  rw [eval₂_mk, Polynomial.hom_eval₂, residue_comp_constHom, aeval_def, eval₂_map]
  rfl

end
end Dubon2026.SourceCurve.RegularProlongation.Joint
