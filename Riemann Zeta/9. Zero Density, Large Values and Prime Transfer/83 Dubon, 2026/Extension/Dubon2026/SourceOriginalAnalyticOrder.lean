import Dubon2026.SourceOriginalRealizationAlgebra

/-! DUB-17/18 -> normalized analytic places -> the actual original
meromorphic order map. Germ-level field operations and proved analytic
realization establish the valuation laws, triviality on constants and
the exact zero fiber. These are derived for the original function field,
not postulated in a place interface.
-/
namespace Dubon2026.SourceFunctionField
noncomputable section
open UpperHalfPlane
open scoped Topology
variable (N : ℕ) [NeZero N]

/-- Meromorphic order of the actual original field element at a complex point. -/
def originalAnalyticOrder (τ : ℍ) (x : modularFunctionFieldOver N ℂ) : WithTop ℤ :=
  meromorphicOrderAt (fun z : ℂ => realize N (x : LaurentSeries ℂ) (ofComplex z)) (τ : ℂ)

theorem originalAnalyticOrder_ne_top (τ : ℍ) {x : modularFunctionFieldOver N ℂ} (hx : x ≠ 0) :
    originalAnalyticOrder N τ x ≠ ⊤ := meromorphicOrderAt_original_realize_ne_top N x hx τ

omit [NeZero N] in
theorem originalAnalyticOrder_zero (τ : ℍ) : originalAnalyticOrder N τ 0 = ⊤ := by
  change meromorphicOrderAt (fun z : ℂ => realize N (0 : LaurentSeries ℂ) (ofComplex z)) (τ : ℂ) = ⊤
  have hz : (0 : LaurentSeries ℂ) = algebraMap ℂ (LaurentSeries ℂ) 0 := (map_zero _).symm
  simp only [hz, realize_algebraMap, meromorphicOrderAt_const, ite_true]

theorem originalAnalyticOrder_eq_top_iff (τ : ℍ) (x : modularFunctionFieldOver N ℂ) :
    originalAnalyticOrder N τ x = ⊤ ↔ x = 0 := by
  constructor
  · intro he
    by_contra hx
    exact originalAnalyticOrder_ne_top N τ hx he
  · rintro rfl
    exact originalAnalyticOrder_zero N τ

omit [NeZero N] in
theorem originalAnalyticOrder_algebraMap (τ : ℍ) (c : ℂ) (hc : c ≠ 0) :
    originalAnalyticOrder N τ (algebraMap ℂ (modularFunctionFieldOver N ℂ) c) = 0 := by
  change meromorphicOrderAt (fun z : ℂ => realize N
    (algebraMap ℂ (LaurentSeries ℂ) c) (ofComplex z)) (τ : ℂ) = 0
  simp only [realize_algebraMap, meromorphicOrderAt_const, if_neg hc]

omit [NeZero N] in
theorem originalAnalyticOrder_one (τ : ℍ) : originalAnalyticOrder N τ 1 = 0 := by
  simpa only [map_one] using originalAnalyticOrder_algebraMap N τ 1 one_ne_zero

theorem originalAnalyticOrder_mul (τ : ℍ) (x y : modularFunctionFieldOver N ℂ) :
    originalAnalyticOrder N τ (x * y) = originalAnalyticOrder N τ x + originalAnalyticOrder N τ y := by
  unfold originalAnalyticOrder
  rw [meromorphicOrderAt_congr (original_realize_mul_eventuallyEq N x y τ),
    meromorphicOrderAt_mul (meromorphicAt_original_realize N x τ) (meromorphicAt_original_realize N y τ)]

theorem originalAnalyticOrder_add (τ : ℍ) (x y : modularFunctionFieldOver N ℂ) :
    min (originalAnalyticOrder N τ x) (originalAnalyticOrder N τ y) ≤ originalAnalyticOrder N τ (x + y) := by
  unfold originalAnalyticOrder
  rw [meromorphicOrderAt_congr (original_realize_add_eventuallyEq N x y τ)]
  exact meromorphicOrderAt_add (meromorphicAt_original_realize N x τ) (meromorphicAt_original_realize N y τ)

end
end Dubon2026.SourceFunctionField
