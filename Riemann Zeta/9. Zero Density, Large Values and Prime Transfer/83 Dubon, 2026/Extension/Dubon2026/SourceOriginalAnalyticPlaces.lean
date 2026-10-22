import Dubon2026.SourceCurveOrderMapPlaces
import Dubon2026.SourceOriginalAnalyticOrderNontrivial

/-! DUB-17/18 -> analytic regular-differential realization -> genuine
analytic places of the original field. The original meromorphic order
map supplies every valuation law and nontriviality hypothesis of the
normalized-place construction. The chosen place and positive scaling
factor therefore come with proved membership and exact order formulas.
No place dictionary, normalization or local-order premise is assumed.
-/
namespace Dubon2026.SourceFunctionField
noncomputable section
open UpperHalfPlane SourceCurve
variable (N : ℕ) [NeZero N]

theorem exists_original_analytic_place (τ : ℍ) :
    ∃ (P : Place ℂ (modularFunctionFieldOver N ℂ)) (e : ℕ), 0 < e ∧
      (∀ x, x ∈ P.toValuationSubring ↔ 0 ≤ originalAnalyticOrder N τ x) ∧
      ∀ x, x ≠ 0 → originalAnalyticOrder N τ x = (((e : ℤ) * P.ord x : ℤ) : WithTop ℤ) :=
  Place.exists_place_of_orderMap (originalAnalyticOrder N τ)
    (originalAnalyticOrder_eq_top_iff N τ) (originalAnalyticOrder_mul N τ)
    (originalAnalyticOrder_add N τ) (originalAnalyticOrder_algebraMap N τ)
    (exists_originalAnalyticOrder_pos N τ)

/-- The genuine normalized place defined by original meromorphic realization. -/
def originalAnalyticPlace (τ : ℍ) : Place ℂ (modularFunctionFieldOver N ℂ) :=
  (exists_original_analytic_place N τ).choose

/-- The positive integer relating analytic order to the normalized original place. -/
def originalAnalyticRamification (τ : ℍ) : ℕ :=
  (exists_original_analytic_place N τ).choose_spec.choose

theorem originalAnalyticRamification_pos (τ : ℍ) : 0 < originalAnalyticRamification N τ :=
  (exists_original_analytic_place N τ).choose_spec.choose_spec.1

theorem originalAnalyticPlace_mem_iff (τ : ℍ) (x : modularFunctionFieldOver N ℂ) :
    x ∈ (originalAnalyticPlace N τ).toValuationSubring ↔ 0 ≤ originalAnalyticOrder N τ x :=
  (exists_original_analytic_place N τ).choose_spec.choose_spec.2.1 x

theorem originalAnalyticPlace_order (τ : ℍ) (x : modularFunctionFieldOver N ℂ) (hx : x ≠ 0) :
    originalAnalyticOrder N τ x =
      (((originalAnalyticRamification N τ : ℤ) * (originalAnalyticPlace N τ).ord x : ℤ) : WithTop ℤ) :=
  (exists_original_analytic_place N τ).choose_spec.choose_spec.2.2 x hx

end
end Dubon2026.SourceFunctionField
