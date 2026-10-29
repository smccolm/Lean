import Dubon2026.SourceGammaOneResidueRatioDegree
import Dubon2026.SourceGammaOneHeckeCoordinateDegree

/-! DUB-17/18 -> original Gamma1 good reduction -> degree and residue-field
comparison. Consume the exact signed-index lower bound supplied by the
selected integral Eisenstein separation route. The native original signed
index, actual residue upper degree and proved integral-ratio inclusion derive
both original degree preservation and equality of the two residue fields.
The signed-index lower bound is still an explicit upstream theorem obligation;
it is not asserted here. Genus preservation and the full acceptance gates
remain open. -/
namespace Dubon2026.SourceFunctionField.GammaOne.CoefficientReduction
noncomputable section
open IntermediateField CongruenceSubgroup
open scoped MatrixGroups
variable {L : Type*} [Field L] [Algebra ℚ L] (A : ValuationSubring L)
  (M : ℕ) [NeZero M]
local notation "kk" => IsLocalRing.ResidueField A
local notation "Γ" => Gamma1 M
private local instance : Algebra kk (residueImage A Γ) := (residueImage A Γ).toSubalgebra.algebra

theorem gammaOne_degree_and_residueField_of_integral_ratio_index
    (hindex : (plusMinus Γ).index ≤ relfinrank kk⟮jqModC kk⟯ (qExpFunctionFieldC kk Γ)) :
    Module.finrank L⟮jCoordinateOver Γ L⟯ (functionFieldOver Γ L) =
        Module.finrank kk⟮residueJCoordinate A Γ⟯ (residueImage A Γ) ∧
      residueImage A Γ = qExpFunctionFieldC kk Γ := by
  have hT : ModularGroup.T ∈ Γ := by simp [Gamma1_mem, ModularGroup.T]
  obtain ⟨hfinite, hupper⟩ := finite_residueCoordinate_and_degree_le A Γ hT
  letI : FiniteDimensional kk⟮residueJCoordinate A Γ⟯ (residueImage A Γ) := hfinite
  have hchar : Module.finrank L⟮jCoordinateOver Γ L⟯ (functionFieldOver Γ L) =
      (plusMinus Γ).index :=
    (coordinate_finrank_eq_relfinrank Γ L).trans (gammaOne_coordinate_relfinrank_eq_index M L)
  have hratio := integral_ratio_residue_coordinate_degree_le A Γ hT
  have hdegree : Module.finrank L⟮jCoordinateOver Γ L⟯ (functionFieldOver Γ L) =
      Module.finrank kk⟮residueJCoordinate A Γ⟯ (residueImage A Γ) := by
    apply le_antisymm
    · rw [hchar]
      exact hindex.trans hratio
    · exact hupper
  refine ⟨hdegree, ?_⟩
  have heq : relfinrank kk⟮jqModC kk⟯ (qExpFunctionFieldC kk Γ) =
      Module.finrank kk⟮residueJCoordinate A Γ⟯ (residueImage A Γ) := by
    apply le_antisymm hratio
    rw [← hdegree, hchar]
    exact hindex
  have hpos : 0 < relfinrank kk⟮jqModC kk⟯ (qExpFunctionFieldC kk Γ) := by
    rw [heq]
    exact Module.finrank_pos
  rw [residue_coordinate_degree_eq_relfinrank A Γ] at heq
  have hbase : kk⟮jqModC kk⟯ ≤ qExpFunctionFieldC kk Γ := by
    rw [adjoin_simple_le_iff]
    exact jqModC_mem_integralRatioField kk Γ
  have hincl := qExpFunctionFieldC_le_residueImage A Γ
  have hmul := relfinrank_mul_relfinrank hbase hincl
  rw [← heq] at hmul
  have hrel : relfinrank (qExpFunctionFieldC kk Γ) (residueImage A Γ) = 1 :=
    mul_left_cancel₀ (ne_of_gt hpos) (hmul.trans (mul_one _).symm)
  exact le_antisymm (relfinrank_eq_one_iff.mp hrel) hincl

end
end Dubon2026.SourceFunctionField.GammaOne.CoefficientReduction
