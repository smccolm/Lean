import Dubon2026.SourceRadialMeromorphicLocalAtlasData

/-! DUB-17/18 -> cover Abel converse -> pole-avoiding path atlas.
Locally constant differences of cell primitives identify the corrected atlas
with a single local logarithmic primitive along a neighborhood of the path.
Finite closed carriers synchronize the possible cell choices. -/
namespace Dubon2026.SourceFunctionField.CellGeometry.RadialMeromorphicPeriods
noncomputable section
open Set Filter RadialDissectionPeriods
open scoped Topology
variable {X R : Type*} [TopologicalSpace X] [T2Space X]

theorem eventually_Gθ_eq_Φloc {D : RadialCellDissection X} (S : Finset X)
    (residue : X → R → ℂ) (Ψ : R → D.ιC → ℂ → ℂ)
    (δ : unitInterval → X) (hδ : Continuous δ) {t₀ : unitInterval} (hy₀ : δ t₀ ∉ S)
    (hcomp : ∀ E : D.ιC, δ t₀ ∈ (D.cell E).carrier →
      ∀ᶠ z in 𝓝 (δ t₀),
        Φloc S residue Ψ E (δ t₀) z - Φloc S residue Ψ (cellOf D (δ t₀)) (δ t₀) z =
          Φloc S residue Ψ E (δ t₀) (δ t₀) -
            Φloc S residue Ψ (cellOf D (δ t₀)) (δ t₀) (δ t₀)) :
    ∀ᶠ t in 𝓝 t₀, Gθ S residue Ψ (δ t₀) (δ t) =
      Φloc S residue Ψ (cellOf D (δ t₀)) (δ t₀) (δ t) := by
  have hev1 : ∀ᶠ t in 𝓝 t₀, δ t ∈ Uset D S (δ t₀) :=
    hδ.continuousAt.preimage_mem_nhds
      ((isOpen_Uset D S (δ t₀)).mem_nhds (mem_Uset_self D S hy₀))
  have hev2 : ∀ᶠ t in 𝓝 t₀, ∀ E : D.ιC, δ t₀ ∈ (D.cell E).carrier →
      Φloc S residue Ψ E (δ t₀) (δ t) - Φloc S residue Ψ (cellOf D (δ t₀)) (δ t₀) (δ t) =
        Φloc S residue Ψ E (δ t₀) (δ t₀) -
          Φloc S residue Ψ (cellOf D (δ t₀)) (δ t₀) (δ t₀) := by
    refine Filter.eventually_all.2 fun E => ?_
    by_cases hE : δ t₀ ∈ (D.cell E).carrier
    · have h := hδ.continuousAt (x := t₀) |>.eventually (hcomp E hE)
      filter_upwards [h] with t ht _
      exact ht
    · exact Filter.Eventually.of_forall fun t h => absurd h hE
  filter_upwards [hev1, hev2] with t ht1 ht2
  obtain ⟨_, hb, _⟩ := mem_Uset ht1
  have hE : δ t₀ ∈ (D.cell (cellOf D (δ t))).carrier :=
    mem_carrier_of_not_mem_badCarrierSet D hb (mem_cellOf D (δ t))
  have h := ht2 _ hE
  rw [Φloc_self, Φloc_self] at h
  simp only [Gθ]
  rw [sub_eq_iff_eq_add] at h
  rw [h]
  abel

end
end Dubon2026.SourceFunctionField.CellGeometry.RadialMeromorphicPeriods
