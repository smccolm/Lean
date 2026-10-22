import Dubon2026.SourceOriginalMeromorphicLocalPrimitives
import Dubon2026.SourceOriginalPoleAvoidingNeighborhoods
import Dubon2026.SourceOriginalCoordinatePrimitiveComparison

/-! DUB-17/18 -> original Abel-Jacobi -> meromorphic loop-period generation.
Local logarithmic primitives agree up to constants on the existing place charts.
This reuses the original coefficient pullback and primitive uniqueness proofs.
Adapted from S_AlgebraicCurve_CellDissection_exists_int_pathIntegral_eq_sum_periods_add_sum_residues,
anthropics/fermats-last-theorem, Apache-2.0,
commit 6e837e75355538c7f80bab5b956861e86c4eacc2.
-/
namespace Dubon2026.SourceFunctionField.CellGeometry.MeromorphicPeriods
noncomputable section
open SourceCurve Set Filter Complex KaehlerDifferential DissectionPeriods
open scoped Real Topology Manifold
attribute [local instance] OriginalChart.placeTopology OriginalChart.placeChartedSpace
variable {N : ℕ} [NeZero N] {R : Type*}
local notation "F" => modularFunctionFieldOver N ℂ

/-- The cell primitive with a logarithmic branch centered at the chosen place. -/
noncomputable def Φloc {𝒟 : CellDissection N} (S : Finset (Place ℂ F)) (θ : R → Ω[F⁄ℂ]) (Ψ : R → 𝒟.ιC → ℂ → ℂ) (D : 𝒟.ιC) (x z : Place ℂ F) : R → ℂ :=
  fun r => Ψ r D ((𝒟.cell D).ζ z) + ρ 𝒟 S θ D r * Lg (𝒟.cell D).R.q ((𝒟.cell D).ζ x) ((𝒟.cell D).ζ z)

theorem Φloc_self {𝒟 : CellDissection N} (S : Finset (Place ℂ F)) (θ : R → Ω[F⁄ℂ]) (Ψ : R → 𝒟.ιC → ℂ → ℂ) (D : 𝒟.ιC) (x : Place ℂ F) :
    Φloc S θ Ψ D x x = pval S θ Ψ D x := by
  funext r
  simp only [Φloc, pval, Lg_self]

/-- A local primitive chart corrected by the fixed cell readings at its center. -/
noncomputable def Gθ {𝒟 : CellDissection N} (S : Finset (Place ℂ F)) (θ : R → Ω[F⁄ℂ]) (Ψ : R → 𝒟.ιC → ℂ → ℂ) (x y : Place ℂ F) : R → ℂ :=
  Φloc S θ Ψ (cellOf 𝒟 y) x y - pval S θ Ψ (cellOf 𝒟 y) x + pval S θ Ψ (cellOf 𝒟 x) x

theorem Gθ_self {𝒟 : CellDissection N} (S : Finset (Place ℂ F)) (θ : R → Ω[F⁄ℂ]) (Ψ : R → 𝒟.ιC → ℂ → ℂ) (x : Place ℂ F) :
    Gθ S θ Ψ x x = pval S θ Ψ (cellOf 𝒟 x) x := by
  rw [Gθ, Φloc_self]; abel

theorem eventually_Φloc_sub [Finite R] {𝒟 : CellDissection N} (S : Finset (Place ℂ F)) (θ : R → Ω[F⁄ℂ])
    (hθ : ∀ r v, -1 ≤ v.ordDifferential (θ r) ∧ (v ∉ S → 0 ≤ v.ordDifferential (θ r)))
    (hS : PolePos 𝒟 S) {V : 𝒟.ιC → Set ℂ} {Ψ : R → 𝒟.ιC → ℂ → ℂ}
    (hP : RegPrimData S θ V Ψ) {y : Place ℂ F} (hyS : y ∉ S) {D D' : 𝒟.ιC}
    (hD : y ∈ (𝒟.cell D).carrier) (hD' : y ∈ (𝒟.cell D').carrier) :
    ∀ᶠ z in 𝓝 y, Φloc S θ Ψ D y z - Φloc S θ Ψ D' y z =
      Φloc S θ Ψ D y y - Φloc S θ Ψ D' y y := by
  have hsrc : ∀ {E : 𝒟.ιC}, y ∈ (𝒟.cell E).carrier →
      y ∈ (𝒟.cell E).ζ.source ∧ (𝒟.cell E).ζ y ∈ V E := by
    rintro E ⟨z, hz, rfl⟩
    have ht := (𝒟.cell E).hKt hz
    exact ⟨(𝒟.cell E).ζ.map_target ht, by rw [(𝒟.cell E).ζ.right_inv ht]; exact hP.hKV E hz⟩
  have hreg : ∀ r, 0 ≤ y.ordDifferential (θ r) := fun r => (hθ r y).2 hyS
  have key : ∀ r, ∀ᶠ z in 𝓝 y, Φloc S θ Ψ D y z r - Φloc S θ Ψ D' y z r =
      Φloc S θ Ψ D y y r - Φloc S θ Ψ D' y y r := by
    intro r
    have hloc : ∀ {E : 𝒟.ιC}, y ∈ (𝒟.cell E).carrier →
        ∀ᶠ z in 𝓝 (extChartAt 𝓘(ℂ, ℂ) y y),
          HasDerivAt ((fun w => Ψ r E w + ρ 𝒟 S θ E r * Lg (𝒟.cell E).R.q ((𝒟.cell E).ζ y) w) ∘
            (𝒟.cell E).ζ ∘ (extChartAt 𝓘(ℂ, ℂ) y).symm) (OriginalChart.readDifferential N y (θ r) z) z := by
      intro E hE
      obtain ⟨W, hWo, hcW, hW⟩ := exists_logPrimitive S θ hθ hS hP r E (hsrc hE).2
        (fun hρ => ζ_ne_q S θ hS hyS hE (fun h => hρ (by rw [h]; rfl)))
      exact hasDerivAt_coordPrimitive (𝒟.cell E).toAnalyticCoord (hsrc hE).1 hWo hcW hW (hreg r)
    have h3 := eventually_coordPrimitive_sub_eq (hloc hD) (hloc hD')
    have hin : ∀ᶠ z in 𝓝 y, z ∈ (extChartAt 𝓘(ℂ, ℂ) y).source := extChartAt_source_mem_nhds y
    filter_upwards [h3, hin] with z hz hzs
    simp only [Function.comp_apply, (extChartAt 𝓘(ℂ, ℂ) y).left_inv hzs,
      (extChartAt 𝓘(ℂ, ℂ) y).left_inv (mem_extChartAt_source y)] at hz
    exact hz
  filter_upwards [Filter.eventually_all.2 key] with z hz
  funext r
  exact hz r

end
end Dubon2026.SourceFunctionField.CellGeometry.MeromorphicPeriods
