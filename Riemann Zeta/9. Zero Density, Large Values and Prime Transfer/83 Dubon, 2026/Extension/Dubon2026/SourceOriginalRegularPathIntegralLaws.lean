import Dubon2026.SourceOriginalRegularPathPrimitives
import Dubon2026.SourceOriginalPathIntegralLaws

/-! DUB-17/18 -> original torsion cardinality -> Abel-Jacobi converse ->
global meromorphic exponential. Reversal and concatenation laws need only
regularity along the paths, allowing the actual third-kind differential.
Existing primitive restrictions and endpoint uniqueness avoid rebuilding
concatenated primitives or introducing a separate integral definition.
-/
namespace Dubon2026.SourceFunctionField.OriginalChart
noncomputable section
open SourceCurve Filter KaehlerDifferential
open scoped Topology
variable (N : ℕ) [NeZero N]
attribute [local instance] placeTopology
local notation "F" => modularFunctionFieldOver N ℂ

theorem pathIntegral_trans_of_primitive {η : Ω[F⁄ℂ]} {P Q R : Place ℂ F}
    (γ : Path P Q) (δ : Path Q R) {g : unitInterval → ℂ}
    (hg : IsPrimitiveAlong N η (γ.trans δ) g) :
    pathIntegral N η (γ.trans δ) = pathIntegral N η γ + pathIntegral N η δ := by
  rw [pathIntegral_eq_of_isPrimitiveAlong N hg,
    pathIntegral_eq_of_isPrimitiveAlong N (isPrimitiveAlong_trans_left N hg),
    pathIntegral_eq_of_isPrimitiveAlong N (isPrimitiveAlong_trans_right N hg)]
  change g 1 - g 0 =
    (g ⟨(1 : ℝ) / 2, by norm_num⟩ - g ⟨(0 : ℝ) / 2, by norm_num⟩) +
    (g ⟨((1 : ℝ) + 1) / 2, by norm_num⟩ - g ⟨((0 : ℝ) + 1) / 2, by norm_num⟩)
  norm_num

theorem pathIntegral_trans_of_coeff_mem {η : Ω[F⁄ℂ]} {P Q R : Place ℂ F}
    (γ : Path P Q) (δ : Path Q R)
    (hγ : ∀ t, (γ t).differentialCoeff η ∈ (γ t).toValuationSubring)
    (hδ : ∀ t, (δ t).differentialCoeff η ∈ (δ t).toValuationSubring) :
    pathIntegral N η (γ.trans δ) = pathIntegral N η γ + pathIntegral N η δ := by
  have hreg : ∀ t, ((γ.trans δ) t).differentialCoeff η ∈ ((γ.trans δ) t).toValuationSubring := by
    intro t
    rw [Path.trans_apply]
    split_ifs
    · exact hγ _
    · exact hδ _
  obtain ⟨g, hg⟩ := exists_isPrimitiveAlong_of_coeff_mem N η (γ.trans δ) hreg
  exact pathIntegral_trans_of_primitive N γ δ hg

theorem pathIntegral_symm_of_coeff_mem {η : Ω[F⁄ℂ]} {P Q : Place ℂ F}
    (γ : Path P Q) (hγ : ∀ t, (γ t).differentialCoeff η ∈ (γ t).toValuationSubring) :
    pathIntegral N η γ.symm = -pathIntegral N η γ := by
  obtain ⟨g, hg⟩ := exists_isPrimitiveAlong_of_coeff_mem N η γ hγ
  rw [pathIntegral_eq_of_isPrimitiveAlong N hg,
    pathIntegral_eq_of_isPrimitiveAlong N (isPrimitiveAlong_symm N hg)]
  simp only [Function.comp_apply, unitInterval.symm_one, unitInterval.symm_zero]
  ring

end
end Dubon2026.SourceFunctionField.OriginalChart
