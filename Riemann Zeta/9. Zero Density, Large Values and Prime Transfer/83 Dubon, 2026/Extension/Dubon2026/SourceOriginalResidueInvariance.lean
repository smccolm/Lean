import Dubon2026.SourceCurveResidueSumEquiv
import Dubon2026.SourceOriginalRationalResidues

/-! DUB-17/18 -> original regular differential dimension -> global residue
identity. The actual original functional of dj is invariant under every
automorphism preserving constants and fixing the literal j-coordinate. The local
finite differential and residue-field inputs are derived from the original
field. This does not assume or assert that the original extension is Galois;
the actual auxiliary finite Galois field and residue descent are assembled
in SourceOriginalGaloisResidueDescent and SourceOriginalGlobalResidues.
-/
namespace Dubon2026.SourceFunctionField
noncomputable section
open SourceCurve KaehlerDifferential
variable (N : ℕ) [NeZero N] (L : Type*) [Field L] [Algebra ℚ L] [IsAlgClosed L]

theorem originalResidueFunctional_diagonal_apply
    {ω : Ω[modularFunctionFieldOver N L⁄L]} (hω : ω ≠ 0)
    (g : modularFunctionFieldOver N L) :
    originalResidueFunctional N L hω (originalPrincipalAdele N L g) =
      ∑ᶠ v : Place L (modularFunctionFieldOver N L),
        kaehlerResidueTermKFam (originalCanonicalLocalResidueData N L) ω
          (diagonalHom L (modularFunctionFieldOver N L) g) v := rfl

theorem originalResidueFunctional_jInvariant
    (e : modularFunctionFieldOver N L ≃ₐ[L] modularFunctionFieldOver N L)
    (hj : e (jOver N L) = jOver N L) (g : modularFunctionFieldOver N L) :
    originalResidueFunctional N L (D_jOver_ne_zero N L)
      (originalPrincipalAdele N L (e g)) =
        originalResidueFunctional N L (D_jOver_ne_zero N L)
          (originalPrincipalAdele N L g) := by
  rw [originalResidueFunctional_diagonal_apply, originalResidueFunctional_diagonal_apply]
  haveI : CharZero L := charZero_of_injective_algebraMap (algebraMap ℚ L).injective
  haveI : ∀ v : Place L (modularFunctionFieldOver N L),
      Module.Finite v.toValuationSubring Ω[v.toValuationSubring⁄L] :=
    finite_original_place_differentials N L
  haveI : ∀ v : Place L (modularFunctionFieldOver N L), Algebra.IsSeparable L v.ResidueField :=
    fun v => by
      haveI := original_place_residue_isAlgebraic N L v
      infer_instance
  haveI : ∀ v : Place L (modularFunctionFieldOver N L), v.DCoordGenerates :=
    original_place_dCoordGenerates N L
  haveI : Nontrivial Ω[modularFunctionFieldOver N L⁄L] :=
    Module.nontrivial_of_finrank_eq_succ (n := 0) (finrank_original_differentials N L)
  have h := residueSum_equiv (originalCanonicalLocalResidueData N L)
    (original_place_residue_algebraMap_bijective N L) e g (jOver N L)
  rw [hj] at h
  exact h

end
end Dubon2026.SourceFunctionField
