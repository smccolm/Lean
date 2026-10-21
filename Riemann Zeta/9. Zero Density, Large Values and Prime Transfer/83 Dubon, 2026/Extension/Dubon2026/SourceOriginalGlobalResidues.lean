import Dubon2026.SourceOriginalGaloisResidueDescent

/-! DUB-17/18 -> original regular differential dimension -> residue duality.
Descent proves global residue vanishing for dj. The already proved fact that
dj spans the original Kaehler module extends this to every actual original
differential and every global function. These are derived identities on the
literal source field, with no global residue theorem supplied as a premise.
-/
namespace Dubon2026.SourceFunctionField
noncomputable section
open SourceCurve KaehlerDifferential
variable (N : ℕ) [NeZero N] (L : Type*) [Field L] [Algebra ℚ L] [IsAlgClosed L]

theorem original_global_residue_sum_zero
    (ω : Ω[modularFunctionFieldOver N L⁄L]) (f : modularFunctionFieldOver N L) :
    (∑ᶠ v : Place L (modularFunctionFieldOver N L),
      kaehlerResidueTermKFam (originalCanonicalLocalResidueData N L) ω
        (diagonalHom L (modularFunctionFieldOver N L) f) v) = 0 := by
  haveI : ∀ v : Place L (modularFunctionFieldOver N L), v.DCoordGenerates :=
    original_place_dCoordGenerates N L
  haveI : Nontrivial Ω[modularFunctionFieldOver N L⁄L] :=
    Module.nontrivial_of_finrank_eq_succ (n := 0) (finrank_original_differentials N L)
  have hmem : ω ∈ Submodule.span (modularFunctionFieldOver N L)
      {D L (modularFunctionFieldOver N L) (jOver N L)} := by
    rw [span_D_jOver N L]
    exact Submodule.mem_top
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hmem
  have h := originalResidueFunctional_j_diagonal_zero N L (f * c)
  rw [originalResidueFunctional_diagonal_apply] at h
  calc
    _ = ∑ᶠ v : Place L (modularFunctionFieldOver N L),
        kaehlerResidueTermKFam (originalCanonicalLocalResidueData N L)
          (D L (modularFunctionFieldOver N L) (jOver N L))
          (diagonalHom L (modularFunctionFieldOver N L) (f * c)) v := by
      apply finsum_congr
      intro v
      simp only [kaehlerResidueTermKFam_apply, v.differentialCoeff_smul]
      change Algebra.trace L v.ResidueField ((originalCanonicalLocalResidueData N L v).res
        (f * (c * v.differentialCoeff (D L (modularFunctionFieldOver N L) (jOver N L))))) = _
      rw [← mul_assoc]
      rfl
    _ = 0 := h

theorem originalResidueFunctional_diagonal_zero
    {ω : Ω[modularFunctionFieldOver N L⁄L]} (hω : ω ≠ 0)
    (f : modularFunctionFieldOver N L) :
    originalResidueFunctional N L hω (originalPrincipalAdele N L f) = 0 := by
  rw [originalResidueFunctional_diagonal_apply]
  exact original_global_residue_sum_zero N L ω f

end
end Dubon2026.SourceFunctionField
