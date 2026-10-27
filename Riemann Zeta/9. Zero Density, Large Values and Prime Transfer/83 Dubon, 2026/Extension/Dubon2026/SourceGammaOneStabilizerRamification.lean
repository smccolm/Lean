import Dubon2026.SourceGammaOneAnalyticPlaces
import Dubon2026.SourceOriginalAnalyticRamification

/-! DUB-17/18 -> original Gamma1 global charts -> elliptic ramification.
The actual place uniformizer is an existing equal-weight modular quotient.
Its subgroup invariance and exact normalized order feed the already-proved
stabilizer-character theorem. This proves the required divisibility, not the
reverse bound or the final ramification equality.
Reuse of SourceOriginalAnalyticRamification preserves its actual uniformizer
and modular forms; no stabilizer or order formula is assumed. -/
namespace Dubon2026.SourceFunctionField.GammaOne
noncomputable section
open UpperHalfPlane Filter
open scoped MatrixGroups Topology

theorem stabilizer_card_dvd_two_mul_ramification
    {Γ : Subgroup SL(2, ℤ)} (hT : ModularGroup.T ∈ Γ) (τ : ℍ) :
    Nat.card (MulAction.stabilizer (Γ) τ) ∣
      2 * analyticRamification hT τ := by
  let P := analyticPlace hT τ
  obtain ⟨k, g, h, hh, hx⟩ := functionFieldOver_modular_ratio hT P.uniformizer
  have hF : ∀ γ ∈ Γ, ∀ z : ℍ,
      g (γ • z) / h (γ • z) = g z / h z := by
    intro γ hγ z
    rw [SlashInvariantForm.slash_action_eqn_SL'' g hγ z,
      SlashInvariantForm.slash_action_eqn_SL'' h hγ z]
    exact mul_div_mul_left _ _ (zpow_ne_zero k (denom_ne_zero _ _))
  have he : meromorphicOrderAt (fun z : ℂ => g (ofComplex z) / h (ofComplex z)) (τ : ℂ) =
      ((analyticRamification hT τ : ℤ) : WithTop ℤ) := by
    rw [← meromorphicOrderAt_congr (realize_eventuallyEq_of_ratio hT g h P.uniformizer hh hx τ)]
    change analyticOrder Γ τ P.uniformizer = _
    rw [analyticPlace_order hT τ _ P.uniformizer_ne_zero]
    change (((analyticRamification hT τ : ℤ) * P.ord P.uniformizer : ℤ) : WithTop ℤ) = _
    rw [P.ord_uniformizer, mul_one]
  have hd := SubgroupStabilizer.main (Γ)
    (fun z => g z / h z) hF τ (analyticRamification hT τ) he
  exact_mod_cast hd

end
end Dubon2026.SourceFunctionField.GammaOne
