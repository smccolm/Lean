import Dubon2026.SourceOriginalWeilCoverRegularPathPrimitives
import Dubon2026.SourceOriginalWeilCoverPathIntegralLaws

/-! DUB-17/18 -> auxiliary point division -> cover Abel converse -> integral-period exponential and principality. Adapt the native original-curve deduction to the literal cover, using proved chart, residue and meromorphic comparison inputs. No global regularity or completed Abel converse is assumed. -/
namespace Dubon2026.SourceFunctionField.OriginalWeilCoverChart
noncomputable section
open SourceCurve Filter Set Metric KaehlerDifferential OriginalPrimitiveGlue
open scoped Topology
variable (N : ℕ) [NeZero N] (n : ℕ) [NeZero n] (radicand : modularFunctionFieldOver N ℂ)
local notation "FF" => modularFunctionFieldOver N ℂ
local notation "EE" => Polynomial.SplittingField (Polynomial.X ^ n - Polynomial.C radicand : Polynomial FF)
variable (A : Divisor ℂ (modularFunctionFieldOver N ℂ)) (hRadicand : radicand ≠ 0)
variable (hOrders : ∀ v : Place ℂ (modularFunctionFieldOver N ℂ), v.ord radicand = (n : ℤ) * A v)
include A hRadicand hOrders
local notation "CoverPath" => @Path (Place ℂ EE) (placeTopology N n radicand A hRadicand hOrders)

theorem pathIntegral_trans_of_primitive {η : Ω[EE⁄ℂ]} {P Q R : Place ℂ EE}
    (γ : CoverPath P Q) (δ : CoverPath Q R) {g : unitInterval → ℂ}
    (hg : IsPrimitiveAlong N n radicand A hRadicand hOrders η ((@Path.trans (Place ℂ EE) (placeTopology N n radicand A hRadicand hOrders) _ _ _ γ δ)) g) :
    pathIntegral N n radicand A hRadicand hOrders η ((@Path.trans (Place ℂ EE) (placeTopology N n radicand A hRadicand hOrders) _ _ _ γ δ)) = pathIntegral N n radicand A hRadicand hOrders η γ + pathIntegral N n radicand A hRadicand hOrders η δ := by
  letI := placeTopology N n radicand A hRadicand hOrders
  rw [pathIntegral_eq_of_isPrimitiveAlong N n radicand A hRadicand hOrders hg,
    pathIntegral_eq_of_isPrimitiveAlong N n radicand A hRadicand hOrders (isPrimitiveAlong_trans_left N n radicand A hRadicand hOrders hg),
    pathIntegral_eq_of_isPrimitiveAlong N n radicand A hRadicand hOrders (isPrimitiveAlong_trans_right N n radicand A hRadicand hOrders hg)]
  change g 1 - g 0 =
    (g ⟨(1 : ℝ) / 2, by norm_num⟩ - g ⟨(0 : ℝ) / 2, by norm_num⟩) +
    (g ⟨((1 : ℝ) + 1) / 2, by norm_num⟩ - g ⟨((0 : ℝ) + 1) / 2, by norm_num⟩)
  norm_num

theorem pathIntegral_trans_of_coeff_mem {η : Ω[EE⁄ℂ]} {P Q R : Place ℂ EE}
    (γ : CoverPath P Q) (δ : CoverPath Q R)
    (hγ : ∀ t, (γ t).differentialCoeff η ∈ (γ t).toValuationSubring)
    (hδ : ∀ t, (δ t).differentialCoeff η ∈ (δ t).toValuationSubring) :
    pathIntegral N n radicand A hRadicand hOrders η ((@Path.trans (Place ℂ EE) (placeTopology N n radicand A hRadicand hOrders) _ _ _ γ δ)) = pathIntegral N n radicand A hRadicand hOrders η γ + pathIntegral N n radicand A hRadicand hOrders η δ := by
  letI := placeTopology N n radicand A hRadicand hOrders
  have hreg : ∀ t, (((@Path.trans (Place ℂ EE) (placeTopology N n radicand A hRadicand hOrders) _ _ _ γ δ)) t).differentialCoeff η ∈ (((@Path.trans (Place ℂ EE) (placeTopology N n radicand A hRadicand hOrders) _ _ _ γ δ)) t).toValuationSubring := by
    intro t
    rw [Path.trans_apply]
    split_ifs
    · exact hγ _
    · exact hδ _
  obtain ⟨g, hg⟩ := exists_isPrimitiveAlong_of_coeff_mem N n radicand A hRadicand hOrders η ((@Path.trans (Place ℂ EE) (placeTopology N n radicand A hRadicand hOrders) _ _ _ γ δ)) hreg
  exact pathIntegral_trans_of_primitive N n radicand A hRadicand hOrders γ δ hg

theorem pathIntegral_symm_of_coeff_mem {η : Ω[EE⁄ℂ]} {P Q : Place ℂ EE}
    (γ : CoverPath P Q) (hγ : ∀ t, (γ t).differentialCoeff η ∈ (γ t).toValuationSubring) :
    pathIntegral N n radicand A hRadicand hOrders η (@Path.symm (Place ℂ EE) (placeTopology N n radicand A hRadicand hOrders) _ _ γ) = -pathIntegral N n radicand A hRadicand hOrders η γ := by
  letI := placeTopology N n radicand A hRadicand hOrders
  obtain ⟨g, hg⟩ := exists_isPrimitiveAlong_of_coeff_mem N n radicand A hRadicand hOrders η γ hγ
  rw [pathIntegral_eq_of_isPrimitiveAlong N n radicand A hRadicand hOrders hg,
    pathIntegral_eq_of_isPrimitiveAlong N n radicand A hRadicand hOrders (isPrimitiveAlong_symm N n radicand A hRadicand hOrders hg)]
  simp only [Function.comp_apply, unitInterval.symm_one, unitInterval.symm_zero]
  ring


end
end Dubon2026.SourceFunctionField.OriginalWeilCoverChart
