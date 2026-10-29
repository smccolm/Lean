import Dubon2026.SourceGammaOneAdjacentJAutomorphism
import Dubon2026.SourceOriginalTensorCoefficientEquivR2
import Dubon2026.SourceGammaOneHeckeDegeneracy

/-! DUB-17/18 -> original Gamma1 Frobenius norm -> complete embeddings.
Extend the proved rational reverse automorphism by the native algebraic
tensor realization. Laurent adjoin extensionality proves the forward
Hecke equation on the entire original lower field, and the adjacent-j
equation survives coefficient extension. The reverse equation on general
beta inputs, with its diamond convention, remains to be identified. -/
namespace Dubon2026.SourceFunctionField.GammaOne
noncomputable section
open IntermediateField CongruenceSubgroup
variable (L : Type*) [Field L] [Algebra ℚ L] [Algebra.IsAlgebraic ℚ L]
variable (M p : ℕ) [NeZero M] [Fact p.Prime]

theorem exists_gammaOne_adjacentJ_over (hcop : Nat.Coprime M p) :
    ∃ w : laurentBaseChange L (x1x0FunctionFieldC ℚ M (p * M)) ≃ₐ[L]
        laurentBaseChange L (x1x0FunctionFieldC ℚ M (p * M)),
      (∀ x, w (heckeAlpha L M p x) = heckeBeta L M p x) ∧
      w (heckeBeta L M p (jCoordinateOver (Gamma1 M) L)) =
        heckeAlpha L M p (jCoordinateOver (Gamma1 M) L) := by
  obtain ⟨σ, hbase, hj⟩ := exists_gammaOne_adjacentJ_automorphism M p hcop
  let w := geomAut L (x1x0FunctionFieldC ℚ M (p * M)) σ
  have hcoeff (z : x1FunctionField M) :
      w (heckeAlpha L M p ⟨coeffEmb L z, coeffEmb_mem_laurentBaseChange L z.2⟩) =
        heckeBeta L M p ⟨coeffEmb L z, coeffEmb_mem_laurentBaseChange L z.2⟩ := by
    apply Subtype.ext
    have hz : (z : LaurentSeries ℚ) ∈ x1x0FunctionFieldC ℚ M (p * M) :=
      x1FunctionFieldC_le_x1x0 ℚ M (p * M) z.2
    have hc := coe_geomAut_coeffEmb L (x1x0FunctionFieldC ℚ M (p * M)) σ ⟨z, hz⟩
    change (w (heckeAlpha L M p
      ⟨coeffEmb L z, coeffEmb_mem_laurentBaseChange L z.2⟩) : LaurentSeries L) =
        qExpand L p (coeffEmb L z)
    apply hc.trans
    change coeffEmb L (σ ⟨z, hz⟩) = _
    rw [hbase z hz]
    exact coeffMap_qExpand (algebraMap ℚ L) p z
  have hf : w.toAlgHom.comp (heckeAlpha L M p) = heckeBeta L M p := by
    apply IntermediateField.algHom_ext_of_eq_adjoin L rfl
    rintro x ⟨y, hy, rfl⟩
    exact hcoeff ⟨y, hy⟩
  refine ⟨w, fun x => DFunLike.congr_fun hf x, ?_⟩
  have harg : heckeBeta L M p (jCoordinateOver (Gamma1 M) L) =
      ⟨coeffEmb L (qExpand ℚ p jq),
        coeffEmb_mem_laurentBaseChange L (adjacentJ_mem_correspondence M p)⟩ := by
    apply Subtype.ext
    exact (coeffMap_qExpand (algebraMap ℚ L) p jq).symm
  rw [harg]
  apply Subtype.ext
  exact (coe_geomAut_coeffEmb L (x1x0FunctionFieldC ℚ M (p * M)) σ
    ⟨qExpand ℚ p jq, adjacentJ_mem_correspondence M p⟩).trans (congrArg (coeffEmb L) hj)

end
end Dubon2026.SourceFunctionField.GammaOne
