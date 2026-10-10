import Dubon2026.MatrixRepresentationStrictConjugacy

/-! # Actual strict conjugators under genuine coefficient and residue maps -/

namespace Dubon2026
noncomputable section
open Matrix

variable {G ι A B K L : Type*} [Group G] [Fintype ι] [DecidableEq ι]
  [CommRing A] [CommRing B] [CommRing K] [CommRing L]

omit [CommRing B] in
/-- Postcomposing the genuine reduction sends the original identity reduction of a strict conjugator to the identity. -/
theorem matrixStrictlyConjugate_comp_reduction (r : A →+* K) (s : K →+* L)
    (ρ τ : G →* GeneralLinearGroup ι A) (h : MatrixStrictlyConjugate r ρ τ) :
    MatrixStrictlyConjugate (s.comp r) ρ τ := by
  obtain ⟨U, hU, hconj⟩ := h
  refine ⟨U, ?_, hconj⟩
  change GeneralLinearGroup.map s (GeneralLinearGroup.map r U) = 1
  rw [hU, map_one]

omit [CommRing L] in
/-- A genuine residue-compatible coefficient map carries the actual original conjugator to a strict conjugator for the entire mapped representation. -/
theorem matrixStrictlyConjugate_map (rA : A →+* K) (rB : B →+* K)
    (f : A →+* B) (hres : rB.comp f = rA)
    (ρ τ : G →* GeneralLinearGroup ι A) (h : MatrixStrictlyConjugate rA ρ τ) :
    MatrixStrictlyConjugate rB ((GeneralLinearGroup.map f).comp ρ)
      ((GeneralLinearGroup.map f).comp τ) := by
  obtain ⟨U, hU, hconj⟩ := h
  refine ⟨GeneralLinearGroup.map f U, ?_, ?_⟩
  · change GeneralLinearGroup.map (rB.comp f) U = 1
    rw [hres]
    exact hU
  · intro g
    change GeneralLinearGroup.map f (τ g) =
      GeneralLinearGroup.map f U * GeneralLinearGroup.map f (ρ g) *
        (GeneralLinearGroup.map f U)⁻¹
    rw [hconj g, map_mul, map_mul, map_inv]

end
end Dubon2026
