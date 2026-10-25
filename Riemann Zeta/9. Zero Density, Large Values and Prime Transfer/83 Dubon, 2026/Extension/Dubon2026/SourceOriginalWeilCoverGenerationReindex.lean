import Dubon2026.SourceFiniteIntegerGenerationReindex
import Dubon2026.SourceOriginalWeilCoverRawReciprocityData

/-! DUB-17/18 -> cover Abel converse -> prescribed cycle coordinates.
Transport each of the two proved generation formulas through the same finite
equivalence. Integer coefficients remain common to the whole differential family. -/
namespace Dubon2026.SourceFunctionField.OriginalWeilCoverChart
noncomputable section
open SourceCurve Filter Set Metric KaehlerDifferential
open scoped Topology
variable (N : ℕ) [NeZero N] (n : ℕ) [NeZero n] (radicand : modularFunctionFieldOver N ℂ)
local notation "FF" => modularFunctionFieldOver N ℂ
local notation "EE" => Polynomial.SplittingField (Polynomial.X ^ n - Polynomial.C radicand : Polynomial FF)
variable (baseDivisor : Divisor ℂ (modularFunctionFieldOver N ℂ)) (hRadicand : radicand ≠ 0)
variable (hOrders : ∀ v : Place ℂ (modularFunctionFieldOver N ℂ), v.ord radicand = (n : ℤ) * baseDivisor v)
include baseDivisor hRadicand hOrders
local notation "CoverPath" => @Path (Place ℂ EE) (placeTopology N n radicand baseDivisor hRadicand hOrders)


open CellGeometry RadialDissectionPeriods


theorem cover_regular_generation_reindex {kDim : ℕ} :
    letI := placeTopology N n radicand baseDivisor hRadicand hOrders
    ∀ (D : RadialCellDissection (Place ℂ EE)) (η : Fin kDim → Ω[EE⁄ℂ])
      (T Ts : Finset D.ιE)
      (γ : (j : D.ιE) → Path (D.vert (D.ends j).1) (D.vert (D.ends j).1))
      (e : Fin kDim ⊕ Fin kDim ≃ {l // l ∈ (T ∪ Ts)ᶜ}),
      CoverRegularCycleGeneration N n radicand baseDivisor hRadicand hOrders D η T Ts γ →
      ∀ (P : Place ℂ EE) (δ : Path P P), ∃ κ : Fin kDim ⊕ Fin kDim → ℤ, ∀ i,
        pathIntegral N n radicand baseDivisor hRadicand hOrders (η i) δ =
          ∑ k, (κ k : ℂ) * pathIntegral N n radicand baseDivisor hRadicand hOrders (η i) (γ (e k).1) := by
  letI := placeTopology N n radicand baseDivisor hRadicand hOrders
  classical
  intro D η T Ts γ e hR
  exact reindex_integer_generation (T ∪ Ts)ᶜ e
    (fun _ δ i => pathIntegral N n radicand baseDivisor hRadicand hOrders (η i) δ)
    (fun l i => pathIntegral N n radicand baseDivisor hRadicand hOrders (η i) (γ l)) hR

theorem cover_meromorphic_generation_reindex {kDim : ℕ} :
    letI := placeTopology N n radicand baseDivisor hRadicand hOrders
    ∀ (D : RadialCellDissection (Place ℂ EE)) (S : Finset (Place ℂ EE))
      (T Ts : Finset D.ιE)
      (γ : (j : D.ιE) → Path (D.vert (D.ends j).1) (D.vert (D.ends j).1))
      (e : Fin kDim ⊕ Fin kDim ≃ {l // l ∈ (T ∪ Ts)ᶜ}),
      CoverMeromorphicCycleGeneration N n radicand baseDivisor hRadicand hOrders D S T Ts γ →
      ∀ (P : Place ℂ EE) (δ : Path P P), (∀ t, δ t ∉ S) →
        ∃ (κ : Fin kDim ⊕ Fin kDim → ℤ) (w : Place ℂ EE → ℤ), ∀ θ : Ω[EE⁄ℂ],
          (∀ v : Place ℂ EE, -1 ≤ v.ordDifferential θ) →
          (∀ v : Place ℂ EE, v ∉ S → 0 ≤ v.ordDifferential θ) →
          pathIntegral N n radicand baseDivisor hRadicand hOrders θ δ =
            ∑ k, (κ k : ℂ) * pathIntegral N n radicand baseDivisor hRadicand hOrders θ (γ (e k).1) +
            2 * Real.pi * Complex.I * ∑ v ∈ S, (w v : ℂ) *
              v.rationalEval (originalWeilKummerCover_residue_bijective N ℂ n radicand v)
                (v.uniformizer * v.differentialCoeff θ) := by
  letI := placeTopology N n radicand baseDivisor hRadicand hOrders
  classical
  intro D S T Ts γ e hG
  exact reindex_integer_generation_with_residues (W := Place ℂ EE → ℤ) (T ∪ Ts)ᶜ e
    (fun _ δ θ => pathIntegral N n radicand baseDivisor hRadicand hOrders θ δ)
    (fun l θ => pathIntegral N n radicand baseDivisor hRadicand hOrders θ (γ l))
    (fun (w : Place ℂ EE → ℤ) θ => 2 * Real.pi * Complex.I * ∑ v ∈ S, (w v : ℂ) *
      v.rationalEval (originalWeilKummerCover_residue_bijective N ℂ n radicand v)
        (v.uniformizer * v.differentialCoeff θ))
    (fun _ δ => ∀ t, δ t ∉ S)
    (fun θ => ∀ v : Place ℂ EE, -1 ≤ v.ordDifferential θ)
    (fun θ => ∀ v : Place ℂ EE, v ∉ S → 0 ≤ v.ordDifferential θ) hG

end
end Dubon2026.SourceFunctionField.OriginalWeilCoverChart
