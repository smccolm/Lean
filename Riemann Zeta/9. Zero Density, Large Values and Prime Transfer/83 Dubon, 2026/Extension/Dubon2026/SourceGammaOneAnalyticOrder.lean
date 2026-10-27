import Dubon2026.SourceGammaOneRealizationAlgebra

/-! DUB-17/18 -> actual Gamma1 differential/cusp converse -> local regularity.
The actual meromorphic quotient defines an integer order map with proved
zero fiber, multiplication, ultrametric addition and constant laws. -/
namespace Dubon2026.SourceFunctionField.GammaOne
noncomputable section
open UpperHalfPlane
open scoped Topology
variable {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ)} (hT : ModularGroup.T ∈ Γ)

/-- Meromorphic order of the actual original field element at a complex point. -/
def analyticOrder (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ)) (τ : ℍ) (x : functionFieldOver Γ ℂ) : WithTop ℤ :=
  meromorphicOrderAt (fun z : ℂ => realize Γ (x : LaurentSeries ℂ) (ofComplex z)) (τ : ℂ)

include hT

theorem analyticOrder_ne_top (τ : ℍ) {x : functionFieldOver Γ ℂ} (hx : x ≠ 0) :
    analyticOrder Γ τ x ≠ ⊤ := meromorphicOrderAt_realize_ne_top hT x hx τ

theorem analyticOrder_zero (τ : ℍ) : analyticOrder Γ τ 0 = ⊤ := by
  change meromorphicOrderAt (fun z : ℂ => realize Γ (0 : LaurentSeries ℂ) (ofComplex z)) (τ : ℂ) = ⊤
  have hz : (0 : LaurentSeries ℂ) = algebraMap ℂ (LaurentSeries ℂ) 0 := (map_zero _).symm
  simp only [hz, realize_algebraMap hT, meromorphicOrderAt_const, ite_true]

theorem analyticOrder_eq_top_iff (τ : ℍ) (x : functionFieldOver Γ ℂ) :
    analyticOrder Γ τ x = ⊤ ↔ x = 0 := by
  constructor
  · intro he
    by_contra hx
    exact analyticOrder_ne_top hT τ hx he
  · rintro rfl
    exact analyticOrder_zero hT τ

theorem analyticOrder_algebraMap (τ : ℍ) (c : ℂ) (hc : c ≠ 0) :
    analyticOrder Γ τ (algebraMap ℂ (functionFieldOver Γ ℂ) c) = 0 := by
  change meromorphicOrderAt (fun z : ℂ => realize Γ
    (algebraMap ℂ (LaurentSeries ℂ) c) (ofComplex z)) (τ : ℂ) = 0
  simp only [realize_algebraMap hT, meromorphicOrderAt_const, if_neg hc]

theorem analyticOrder_one (τ : ℍ) : analyticOrder Γ τ 1 = 0 := by
  simpa only [map_one] using analyticOrder_algebraMap hT τ 1 one_ne_zero

theorem analyticOrder_mul (τ : ℍ) (x y : functionFieldOver Γ ℂ) :
    analyticOrder Γ τ (x * y) = analyticOrder Γ τ x + analyticOrder Γ τ y := by
  unfold analyticOrder
  rw [meromorphicOrderAt_congr (realize_mul_eventuallyEq hT x y τ),
    meromorphicOrderAt_mul (meromorphicAt_realize hT x τ) (meromorphicAt_realize hT y τ)]

theorem analyticOrder_add (τ : ℍ) (x y : functionFieldOver Γ ℂ) :
    min (analyticOrder Γ τ x) (analyticOrder Γ τ y) ≤ analyticOrder Γ τ (x + y) := by
  unfold analyticOrder
  rw [meromorphicOrderAt_congr (realize_add_eventuallyEq hT x y τ)]
  exact meromorphicOrderAt_add (meromorphicAt_realize hT x τ) (meromorphicAt_realize hT y τ)

end
end Dubon2026.SourceFunctionField.GammaOne
