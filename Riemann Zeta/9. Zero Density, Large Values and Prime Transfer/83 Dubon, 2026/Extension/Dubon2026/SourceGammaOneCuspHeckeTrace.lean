import Dubon2026.SourceGammaOneHeckeTraceCosets
import Dubon2026.ModularDegeneracy

/-! DUB17/18 -> actual Gamma1 Picard/H1 Hecke comparison -> actual
analytic trace. Restrict the actual inverse-dilation translate to the
proved upper subgroup, then use Mathlib's cusp-form trace. The explicit
coset formula identifies the resulting cusp form with the intended sum. -/
namespace Dubon2026.SourceFunctionField.GammaOne
noncomputable section
open CongruenceSubgroup Matrix.SpecialLinearGroup UpperHalfPlane
open scoped MatrixGroups ModularForm Pointwise
variable (M d : ℕ) [NeZero d]

theorem heckeGLUpper_le_conj :
    heckeGLUpper M d ≤
      ConjAct.toConjAct (heckeTriangularMatrix 1 d 0)⁻¹ • (Gamma1 M).map (mapGL ℝ) := by
  rintro x ⟨g, hg, rfl⟩
  rw [Subgroup.mem_smul_pointwise_iff_exists]
  refine ⟨mapGL ℝ (sourceGammaOneHeckeConjugation M d ⟨g, hg⟩).val,
    Subgroup.mem_map.mpr ⟨_, (sourceGammaOneHeckeConjugation M d ⟨g, hg⟩).property, rfl⟩, ?_⟩
  rw [ConjAct.toConjAct_smul, inv_inv, mul_assoc, inv_mul_eq_iff_eq_mul]
  exact (sourceGammaOneHeckeConjugation_matrix M d ⟨g, hg⟩).symm

/-- The actual weight-two inverse-dilation cusp form on the real upper subgroup. -/
def cuspHeckeDiagonal (f : CuspForm ((Gamma1 M).map (mapGL ℝ)) 2) :
    CuspForm (heckeGLUpper M d) 2 :=
  cuspRestrictSubgroup (heckeGLUpper_le_conj M d)
    (CuspForm.translate f (heckeTriangularMatrix 1 d 0))

/-- The native finite cusp trace of the actual weight-two inverse-dilation translate. -/
def cuspHeckeTrace (f : CuspForm ((Gamma1 M).map (mapGL ℝ)) 2) :
    CuspForm ((Gamma1 M).map (mapGL ℝ)) 2 :=
  letI := heckeGLUpper_finiteRelIndex M d
  CuspForm.trace ((Gamma1 M).map (mapGL ℝ)) (cuspHeckeDiagonal M d f)

private local instance : Fintype (Gamma1 M ⧸ sourceGammaOneHeckeUpper M d) := by
  letI := sourceGammaOneHeckeUpper_finiteIndex M d
  exact Fintype.ofFinite _

theorem cuspHeckeTrace_coe (f : CuspForm ((Gamma1 M).map (mapGL ℝ)) 2) :
    ⇑(cuspHeckeTrace M d f) =
      ∑ q : Gamma1 M ⧸ sourceGammaOneHeckeUpper M d,
        sourceGammaOneWeightTwoHeckeCoset M d f q := by
  classical
  letI := heckeGLUpper_finiteRelIndex M d
  letI : Fintype (((Gamma1 M).map (mapGL ℝ)) ⧸
      (heckeGLUpper M d).subgroupOf ((Gamma1 M).map (mapGL ℝ))) := Fintype.ofFinite _
  change (∑ q, SlashInvariantForm.quotientFunc (cuspHeckeDiagonal M d f) q) = _
  rw [← (heckeCosetGLEquiv M d).sum_comp]
  apply Finset.sum_congr rfl
  intro q _
  induction q using Quotient.inductionOn with
  | h g =>
    rw [heckeCosetGLEquiv_mk, SlashInvariantForm.quotientFunc_mk,
      sourceGammaOneWeightTwoHeckeCoset_mk]
    change (⇑f ∣[(2 : ℤ)] heckeTriangularMatrix 1 d 0) ∣[(2 : ℤ)] (mapGL ℝ g.val)⁻¹ = _
    rw [map_inv]

end
end Dubon2026.SourceFunctionField.GammaOne
