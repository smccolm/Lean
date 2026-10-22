import Dubon2026.SourceJSeedCuspRatio
import Dubon2026.SourceOriginalPairBaseChange
import Dubon2026.SourceLaurentCoefficientReindex

/-! DUB-17/18 -> analytic realization of the original field. Actual
weight-24 cusp degeneracy maps give equal-weight numerator/denominator
representations of each literal j(q^d), d dividing N. Their injectivity
discharges denominator nonvanishing; the proved Laurent coefficient
identity gives exact equality with the original coefficient embedding.
These are the generator inputs to the original two-generator field.
-/
namespace Dubon2026.SourceFunctionField
noncomputable section
open UpperHalfPlane CongruenceSubgroup
open scoped MatrixGroups

theorem exists_jqd_cusp_ratio (N d : ℕ) [NeZero d] (hd : d ∣ N) :
    ∃ (g h : CuspForm (Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 24), h ≠ 0 ∧
      qExpand ℂ d (jqModC ℂ) * (qExpansion 1 (h : UpperHalfPlane → ℂ) : LaurentSeries ℂ) =
        (qExpansion 1 (g : UpperHalfPlane → ℂ) : LaurentSeries ℂ) := by
  obtain ⟨g, h, hh, he⟩ := exists_jq_cusp_ratio
  have hd1 : d * 1 ∣ N := by simpa using hd
  refine ⟨cuspDegeneracyMap d hd1 24 g, cuspDegeneracyMap d hd1 24 h, ?_, ?_⟩
  · intro hzero
    apply hh
    exact cuspDegeneracyMap_injective d hd1 24 (hzero.trans (map_zero _).symm)
  · rw [cuspDegeneracyMap_laurent, cuspDegeneracyMap_laurent, ← map_mul, he]

theorem isRatio_coeffEmb_qExpand_jq (N d : ℕ) [NeZero d] (hd : d ∣ N) :
    ModularRatios.IsRatio N (coeffEmb ℂ (qExpand ℚ d jq)) := by
  obtain ⟨g, h, hh, he⟩ := exists_jqd_cusp_ratio N d hd
  have hmap : coeffEmb ℂ (qExpand ℚ d jq) = qExpand ℂ d (jqModC ℂ) := by
    calc
      _ = qExpand ℂ d (coeffEmb ℂ jq) := coeffMap_qExpand (algebraMap ℚ ℂ) d jq
      _ = _ := by rw [coeffEmb_jq]
  refine ⟨24, CuspForm.toModularFormₗ g, CuspForm.toModularFormₗ h, ?_, ?_⟩
  · intro hzero
    exact hh (CuspForm.toModularFormₗ_injective (hzero.trans (map_zero _).symm))
  · change coeffEmb ℂ (qExpand ℚ d jq) *
        (qExpansion 1 (h : UpperHalfPlane → ℂ) : LaurentSeries ℂ) =
          (qExpansion 1 (g : UpperHalfPlane → ℂ) : LaurentSeries ℂ)
    rw [hmap]
    exact he

end
end Dubon2026.SourceFunctionField
