import Dubon2026.SourceOriginalConstructedRegularPeriods

/-! DUB-17/18 -> original Abel-Jacobi -> discrete original periods.
Reindex the actual 2g complementary edge loops by the source Fin g + Fin g
index, retaining their actual base places and common integer period coefficients.
This uses only a finite equivalence; no extra loop or period hypothesis is added.
-/
namespace Dubon2026.SourceFunctionField.CellGeometry.DissectionPeriods
noncomputable section
open SourceCurve Set KaehlerDifferential OriginalChart
attribute [local instance] placeTopology placeChartedSpace
variable {N : ℕ} [NeZero N] {κ : Type*}
local notation "F" => modularFunctionFieldOver N ℂ

theorem exists_reindexed_cycle_periods (D : CellDissection N) (η : κ → Ω[F⁄ℂ])
    (T Ts : Finset D.ιE) {n : ℕ} (hc : (T ∪ Ts)ᶜ.card = 2 * n)
    (γ : (j : D.ιE) → Path (D.vert (D.ends j).1) (D.vert (D.ends j).1))
    (hR : RegularCycleGeneration D η T Ts γ) :
    ∃ (Pz : Fin n ⊕ Fin n → Place ℂ F) (Z : ∀ k, Path (Pz k) (Pz k)),
      ∀ (P : Place ℂ F) (δ : Path P P), ∃ a : Fin n ⊕ Fin n → ℤ, ∀ i,
        pathIntegral N (η i) δ = ∑ k, (a k : ℂ) * pathIntegral N (η i) (Z k) := by
  let e : (Fin n ⊕ Fin n) ≃ {l // l ∈ (T ∪ Ts)ᶜ} := Fintype.equivOfCardEq (by
    simp only [Fintype.card_sum, Fintype.card_fin, Fintype.card_coe]
    rw [hc, two_mul])
  let Pz : Fin n ⊕ Fin n → Place ℂ F := fun k => D.vert (D.ends (e k).1).1
  let Z : ∀ k, Path (Pz k) (Pz k) := fun k => γ (e k).1
  refine ⟨Pz, Z, fun P δ => ?_⟩
  obtain ⟨a, ha⟩ := hR P δ
  refine ⟨fun k => a (e k).1, fun i => ?_⟩
  rw [ha i, ← Finset.sum_coe_sort]
  exact (e.sum_comp (fun l => (a l.1 : ℂ) * pathIntegral N (η i) (γ l.1))).symm

end
end Dubon2026.SourceFunctionField.CellGeometry.DissectionPeriods
