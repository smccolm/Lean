import Dubon2026.SourceGammaOneAnalyticOrderNontrivial
import Dubon2026.SourceCurveOrderMapPlaces

/-! DUB-17/18 -> actual Gamma1 differential/cusp converse -> finite
analytic regularity. Apply the existing normalized-place theorem to the
proved meromorphic order of the original field. No global place dictionary
or ramification classification is required for this local construction. -/
namespace Dubon2026.SourceFunctionField.GammaOne
noncomputable section
open UpperHalfPlane SourceCurve
variable {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ)}
  (hT : ModularGroup.T ∈ Γ)

include hT

theorem exists_analytic_place (τ : ℍ) :
    ∃ (P : Place ℂ (functionFieldOver Γ ℂ)) (e : ℕ), 0 < e ∧
      (∀ x, x ∈ P.toValuationSubring ↔ 0 ≤ analyticOrder Γ τ x) ∧
      ∀ x, x ≠ 0 → analyticOrder Γ τ x = (((e : ℤ) * P.ord x : ℤ) : WithTop ℤ) :=
  Place.exists_place_of_orderMap (analyticOrder Γ τ)
    (analyticOrder_eq_top_iff hT τ) (analyticOrder_mul hT τ)
    (analyticOrder_add hT τ) (analyticOrder_algebraMap hT τ)
    (exists_analyticOrder_pos hT τ)

/-- The normalized place defined by the actual modular-quotient germ. -/
def analyticPlace (τ : ℍ) : Place ℂ (functionFieldOver Γ ℂ) :=
  (exists_analytic_place hT τ).choose

/-- The positive integral scaling of actual analytic order. -/
def analyticRamification (τ : ℍ) : ℕ :=
  (exists_analytic_place hT τ).choose_spec.choose

theorem analyticRamification_pos (τ : ℍ) : 0 < analyticRamification hT τ :=
  (exists_analytic_place hT τ).choose_spec.choose_spec.1


theorem analyticPlace_order (τ : ℍ) (x : functionFieldOver Γ ℂ) (hx : x ≠ 0) :
    analyticOrder Γ τ x =
      (((analyticRamification hT τ : ℤ) * (analyticPlace hT τ).ord x : ℤ) : WithTop ℤ) :=
  (exists_analytic_place hT τ).choose_spec.choose_spec.2.2 x hx

end
end Dubon2026.SourceFunctionField.GammaOne
