import Dubon2026.SourceCurveResiduePullbackSum
import Dubon2026.SourceOriginalGaloisResidueVanishing
import Dubon2026.SourceOriginalResidueInvariance

/-! DUB-17/18 -> original regular differential dimension -> global residue
identity. The actual normal-closure residue sum is the original dj residue
sum multiplied by the actual extension degree. All finite-support, local
differential, residue-field and finite separability inputs are derived for
the literal original field and its literal normal closure.
-/
namespace Dubon2026.SourceFunctionField
noncomputable section
open SourceCurve KaehlerDifferential
attribute [local instance] originalGaloisClosureOriginalModule
variable (N : ℕ) [NeZero N] (L : Type*) [Field L] [Algebra ℚ L] [IsAlgClosed L]

theorem originalGaloisResidue_support_finite (f : originalGaloisClosure N L) :
    (Function.support (kaehlerResidueTermKFam (originalGaloisCanonicalLocalResidueData N L)
      (D L (originalGaloisClosure N L) (originalGaloisJ N L))
      (diagonalHom L (originalGaloisClosure N L) f))).Finite :=
  diagonal_residue_support_finite (originalGaloisCanonicalLocalResidueData N L)
    (D L (originalGaloisClosure N L) (originalGaloisJ N L)) f
    (finite_originalGaloisClosure_divisor_support N L f)
    (finite_originalGaloisClosure_D_j_support N L)

theorem originalGaloisResidueMap_pullback (f : modularFunctionFieldOver N L) :
    originalGaloisResidueMap N L
      (algebraMap (modularFunctionFieldOver N L) (originalGaloisClosure N L) f) =
      (Module.finrank (modularFunctionFieldOver N L) (originalGaloisClosure N L) : L) *
        originalResidueFunctional N L (D_jOver_ne_zero N L) (originalPrincipalAdele N L f) := by
  haveI : CharZero L := charZero_of_injective_algebraMap (algebraMap ℚ L).injective
  haveI := finite_originalGaloisClosure_over_original N L
  haveI : CharZero (modularFunctionFieldOver N L) :=
    charZero_of_injective_algebraMap (algebraMap L (modularFunctionFieldOver N L)).injective
  haveI : ∀ v : Place L (originalGaloisClosure N L),
      Module.Finite v.toValuationSubring Ω[v.toValuationSubring⁄L] :=
    finite_originalGaloisClosure_place_differentials N L
  haveI : ∀ v : Place L (originalGaloisClosure N L), Algebra.IsSeparable L v.ResidueField :=
    fun v => by
      haveI := originalGaloisClosure_place_residue_isAlgebraic N L v
      infer_instance
  haveI : ∀ v : Place L (originalGaloisClosure N L), v.DCoordGenerates :=
    originalGaloisClosure_place_dCoordGenerates N L
  haveI : ∀ v : Place L (modularFunctionFieldOver N L), v.DCoordGenerates :=
    original_place_dCoordGenerates N L
  haveI : Nontrivial Ω[originalGaloisClosure N L⁄L] :=
    Module.nontrivial_of_finrank_eq_succ (n := 0) (finrank_originalGaloisClosure_differentials N L)
  haveI : Nontrivial Ω[modularFunctionFieldOver N L⁄L] :=
    Module.nontrivial_of_finrank_eq_succ (n := 0) (finrank_original_differentials N L)
  exact residueSum_pullback_differential (originalCanonicalLocalResidueData N L)
    (originalGaloisCanonicalLocalResidueData N L)
    (original_place_residue_algebraMap_bijective N L)
    (originalGaloisClosure_place_residue_bijective N L)
    (jOver N L) f (originalGaloisResidue_support_finite N L _)

theorem originalResidueFunctional_j_diagonal_zero (f : modularFunctionFieldOver N L) :
    originalResidueFunctional N L (D_jOver_ne_zero N L) (originalPrincipalAdele N L f) = 0 := by
  haveI : CharZero L := charZero_of_injective_algebraMap (algebraMap ℚ L).injective
  haveI := finite_originalGaloisClosure_over_original N L
  have h := originalGaloisResidueMap_pullback N L f
  rw [originalGaloisResidueMap_eq_zero, LinearMap.zero_apply] at h
  have hd : (Module.finrank (modularFunctionFieldOver N L) (originalGaloisClosure N L) : L) ≠ 0 := by
    exact_mod_cast (Module.finrank_pos (R := modularFunctionFieldOver N L)
      (M := originalGaloisClosure N L)).ne'
  exact (mul_eq_zero.mp h.symm).resolve_left hd

end
end Dubon2026.SourceFunctionField
