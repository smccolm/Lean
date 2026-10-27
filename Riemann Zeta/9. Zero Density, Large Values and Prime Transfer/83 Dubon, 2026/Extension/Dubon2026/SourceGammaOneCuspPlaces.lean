import Dubon2026.SourceGammaOneCuspJOrder
import Dubon2026.SourceCurveOrderMapPlaces

/-! DUB-17/18 -> actual Gamma1 differential/cusp comparison -> cusp
vanishing. The proved order of the translated original field defines an
actual normalized place. The pole of j makes this order nontrivial. -/
namespace Dubon2026.SourceFunctionField.GammaOne
noncomputable section
open UpperHalfPlane SourceCurve
open scoped MatrixGroups
variable {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ)}
  (N : ℕ) [NeZero N] (hΓ : CongruenceSubgroup.Gamma N ≤ Γ)
  (hT : ModularGroup.T ∈ Γ)

include hΓ hT

theorem exists_cusp_place (γ : SL(2, ℤ)) :
    ∃ (P : Place ℂ (functionFieldOver Γ ℂ)) (e : ℕ), 0 < e ∧
      (∀ x, x ∈ P.toValuationSubring ↔ 0 ≤ cuspOrder Γ N γ x) ∧
      ∀ x, x ≠ 0 → cuspOrder Γ N γ x = (((e : ℤ) * P.ord x : ℤ) : WithTop ℤ) :=
  Place.exists_place_of_orderMap (cuspOrder Γ N γ)
    (cuspOrder_eq_top_iff N hΓ hT γ) (cuspOrder_mul N hΓ hT γ)
    (cuspOrder_add N hΓ hT γ) (cuspOrder_algebraMap N hT γ)
    (exists_cuspOrder_pos N hΓ hT γ)

/-- The normalized place of the actual translated cusp germ. -/
def cuspPlace (γ : SL(2, ℤ)) : Place ℂ (functionFieldOver Γ ℂ) :=
  (exists_cusp_place N hΓ hT γ).choose

/-- Positive scaling between the actual cusp order and its normalized place. -/
def cuspRamification (γ : SL(2, ℤ)) : ℕ :=
  (exists_cusp_place N hΓ hT γ).choose_spec.choose

theorem cuspRamification_pos (γ : SL(2, ℤ)) : 0 < cuspRamification N hΓ hT γ :=
  (exists_cusp_place N hΓ hT γ).choose_spec.choose_spec.1

theorem cuspPlace_order (γ : SL(2, ℤ)) (x : functionFieldOver Γ ℂ) (hx : x ≠ 0) :
    cuspOrder Γ N γ x =
      (((cuspRamification N hΓ hT γ : ℤ) * (cuspPlace N hΓ hT γ).ord x : ℤ) : WithTop ℤ) :=
  (exists_cusp_place N hΓ hT γ).choose_spec.choose_spec.2.2 x hx

theorem cuspPlace_j_neg (γ : SL(2, ℤ)) :
    (cuspPlace N hΓ hT γ).ord (jCoordinateOver Γ ℂ) < 0 := by
  have hj0 : jCoordinateOver Γ ℂ ≠ 0 := by
    intro he
    exact transcendental_jCoordinateOver Γ ℂ (he ▸ isAlgebraic_zero)
  have hn := cuspOrder_jCoordinate_neg N hT γ
  rw [cuspPlace_order N hΓ hT γ _ hj0, ← WithTop.coe_zero, WithTop.coe_lt_coe] at hn
  have hp : (0 : ℤ) < cuspRamification N hΓ hT γ := by
    exact_mod_cast cuspRamification_pos N hΓ hT γ
  nlinarith

end
end Dubon2026.SourceFunctionField.GammaOne
