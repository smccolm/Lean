import Dubon2026.SourceGammaOneDiamondConjugation
import Dubon2026.SourceGammaOneCuspHeckeTrace
import Dubon2026.SourceGammaOnePeriodNormalization

/-! DUB17/18 -> original all-weight association -> actual arithmetic
Gamma1 diamond comparison -> original analytic periods. Reuse native
cusp translation and subgroup restriction, then the already proved
weight-two primitive chain rule and endpoint uniqueness. No slash
stability, derivative or period-normalization premise is supplied. -/
namespace Dubon2026.SourceFunctionField.GammaOne
noncomputable section
open CongruenceSubgroup Matrix.SpecialLinearGroup UpperHalfPlane
open scoped MatrixGroups ModularForm Pointwise
variable (M : ℕ) (g : Gamma0 M)

theorem diamondGL_le_conj :
    (Gamma1 M).map (mapGL ℝ) ≤
      ConjAct.toConjAct (mapGL ℝ g.val)⁻¹ • (Gamma1 M).map (mapGL ℝ) := by
  rintro x ⟨γ, hγ, rfl⟩
  rw [Subgroup.mem_smul_pointwise_iff_exists]
  refine ⟨mapGL ℝ (sourceGammaOneDiamondConjugation M g ⟨γ, hγ⟩).val,
    Subgroup.mem_map.mpr ⟨_, (sourceGammaOneDiamondConjugation M g ⟨γ, hγ⟩).property, rfl⟩, ?_⟩
  change (mapGL ℝ g.val)⁻¹ * mapGL ℝ (g.val * γ * g.val⁻¹) * mapGL ℝ g.val = mapGL ℝ γ
  rw [map_mul, map_mul, map_inv]
  group

/-- The actual weight-two slash diamond cusp form for a Gamma0 lift. -/
def cuspDiamond (f : CuspForm ((Gamma1 M).map (mapGL ℝ)) 2) :
    CuspForm ((Gamma1 M).map (mapGL ℝ)) 2 :=
  cuspRestrictSubgroup (diamondGL_le_conj M g) (CuspForm.translate f (mapGL ℝ g.val))

theorem cuspDiamond_coe (f : CuspForm ((Gamma1 M).map (mapGL ℝ)) 2) :
    ⇑(cuspDiamond M g f) = ⇑f ∣[(2 : ℤ)] mapGL ℝ g.val := rfl

variable [NeZero M]

theorem diamondPrimitive_hasDerivAt
    (f : CuspForm ((Gamma1 M).map (mapGL ℝ)) 2) (τ : ℍ) :
    HasDerivAt (fun z : ℂ => sourceWeightTwoPrimitive 1 f (g.val • ofComplex z))
      (cuspDiamond M g f τ) (τ : ℂ) := by
  have hg : 0 < ((mapGL ℝ g.val) : Matrix (Fin 2) (Fin 2) ℝ).det := by
    rw [← Matrix.GeneralLinearGroup.val_det_apply, det_mapGL, Units.val_one]
    exact zero_lt_one
  have hT : ModularGroup.T ∈ Gamma1 M := by simp [Gamma1_mem, ModularGroup.T]
  have hd := sourceHasDerivAt_comp_smul
    (fun z => sourceWeightTwoPrimitive_hasDerivAt f one_pos (hper hT) z) hg τ
  simpa only [Function.comp_apply, ofComplex_apply, cuspDiamond_coe] using hd

theorem diamondPrimitive_difference
    (f : CuspForm ((Gamma1 M).map (mapGL ℝ)) 2) (a b : ℍ) :
    sourceWeightTwoPrimitive 1 f (g.val • b) - sourceWeightTwoPrimitive 1 f (g.val • a) =
      sourceWeightTwoPrimitive 1 (cuspDiamond M g f) b -
        sourceWeightTwoPrimitive 1 (cuspDiamond M g f) a := by
  have hT : ModularGroup.T ∈ Gamma1 M := by simp [Gamma1_mem, ModularGroup.T]
  exact sourceUpperHalfPlane_primitive_difference
    (F := fun z => sourceWeightTwoPrimitive 1 f (g.val • z))
    (G := sourceWeightTwoPrimitive 1 (cuspDiamond M g f))
    (fun z => diamondPrimitive_hasDerivAt M g f z)
    (fun z => sourceWeightTwoPrimitive_hasDerivAt (cuspDiamond M g f) one_pos (hper hT) z) a b

end
end Dubon2026.SourceFunctionField.GammaOne
