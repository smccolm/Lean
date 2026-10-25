import Dubon2026.SourceOriginalWeilCoverNormalizedWeightedResidues
import Dubon2026.SourceRadialWeightedCycleSums
import Dubon2026.SourceRadialCellCarrierNeighborhoods

/-! DUB-17/18 -> cover Abel converse -> bilinear and third-kind reciprocity.
The exact weighted residue sum is converted to the same cycle-period matrix.
Specializing to regular forms gives the zero bilinear relation. No new
integration or cycle decomposition is assumed beyond the existing constructed data. -/
namespace Dubon2026.SourceFunctionField.OriginalWeilCoverChart
noncomputable section
open SourceCurve Set Filter KaehlerDifferential CellGeometry
open scoped Topology
variable (N : ℕ) [NeZero N] (n : ℕ) [NeZero n]
variable (radicand : modularFunctionFieldOver N ℂ)
local notation "FF" => modularFunctionFieldOver N ℂ
local notation "EE" => Polynomial.SplittingField (Polynomial.X ^ n - Polynomial.C radicand : Polynomial FF)
variable (baseDivisor : Divisor ℂ (modularFunctionFieldOver N ℂ)) (hRadicand : radicand ≠ 0)
variable (hOrders : ∀ v : Place ℂ (modularFunctionFieldOver N ℂ), v.ord radicand = (n : ℤ) * baseDivisor v)
include baseDivisor hRadicand hOrders
local notation "PC" => placeChart N n radicand baseDivisor hRadicand hOrders
local notation "PF" => placeFamily N n radicand baseDivisor hRadicand hOrders
local notation "RD" => readDifferential N n radicand baseDivisor hRadicand hOrders
local notation "CF" => coverCoeffIn N n radicand baseDivisor hRadicand hOrders

local notation "BI" => coverBoundaryIntegrand N n radicand baseDivisor hRadicand hOrders

open MeasureTheory

open scoped Real

open RadialDissectionPeriods
variable {κ : Type*}

theorem cover_loop_bilinear_eq_neg_edge_jumps :
    letI := placeTopology N n radicand baseDivisor hRadicand hOrders
    ∀ (D : RadialCellDissection (Place ℂ EE)) (η : κ → Ω[EE⁄ℂ])
    (T Ts : Finset D.ιE) (Z : D.ιE → D.ιE → ℤ) (J : D.ιE → κ → ℂ)
    (P : D.ιE → D.ιE → ℤ)
    (γ : (j : D.ιE) → Path (D.vert (D.ends j).1) (D.vert (D.ends j).1))
    (_ : ∀ e, J e = ∑ l ∈ Tᶜ, Z l e • J l) (_ : ∀ e ∈ Ts, J e = 0)
    (_ : ∀ j ∉ Ts, J j = -∑ l ∈ (T ∪ Ts)ᶜ,
      (P j l : ℂ) • (fun i => pathIntegral N n radicand baseDivisor hRadicand hOrders (η i) (γ l)))
    (θ : Ω[EE⁄ℂ])
    (_ : ∀ j, pathIntegral N n radicand baseDivisor hRadicand hOrders θ (γ j) = ∑ e, (Z j e : ℂ) * coverEdgeIntegral N n radicand baseDivisor hRadicand hOrders D θ e) (i : κ),
    (∑ j ∈ (T ∪ Ts)ᶜ, ∑ l ∈ (T ∪ Ts)ᶜ,
      pathIntegral N n radicand baseDivisor hRadicand hOrders θ (γ j) * (P j l : ℂ) * pathIntegral N n radicand baseDivisor hRadicand hOrders (η i) (γ l)) =
        -∑ e, J e i * coverEdgeIntegral N n radicand baseDivisor hRadicand hOrders D θ e := by
  letI := placeTopology N n radicand baseDivisor hRadicand hOrders
  intro D η T Ts Z J P γ hdec hJ0 hrow θ hγθ i
  have hz : ∀ j, cycleScalarIntegral Z (coverEdgeIntegral N n radicand baseDivisor hRadicand hOrders D θ) j = pathIntegral N n radicand baseDivisor hRadicand hOrders θ (γ j) :=
    fun j => (hγθ j).symm
  have h := sum_mul_jump_eq_cycle_bilinear hdec hJ0
    (fun l i => pathIntegral N n radicand baseDivisor hRadicand hOrders (η i) (γ l)) P hrow (coverEdgeIntegral N n radicand baseDivisor hRadicand hOrders D θ) i
  simp_rw [hz] at h
  calc
    _ = -∑ e, coverEdgeIntegral N n radicand baseDivisor hRadicand hOrders D θ e * J e i := (neg_eq_iff_eq_neg).mp h.symm
    _ = _ := by
      congr 1
      exact Finset.sum_congr rfl fun e _ => mul_comm _ _


theorem cover_cycle_bilinear_eq_neg_residue :
    letI := placeTopology N n radicand baseDivisor hRadicand hOrders
    ∀ (D : RadialCellDissection (Place ℂ EE)) (η : κ → Ω[EE⁄ℂ])
    (V : D.ιC → Set ℂ) (Ψ : κ → D.ιC → ℂ → ℂ) (J : D.ιE → κ → ℂ)
    (_ : CoverPrimData N n radicand baseDivisor hRadicand hOrders D η V Ψ) (_ : IsJump D Ψ J)
    (T Ts : Finset D.ιE) (Z : D.ιE → D.ιE → ℤ) (P : D.ιE → D.ιE → ℤ)
    (γ : (j : D.ιE) → Path (D.vert (D.ends j).1) (D.vert (D.ends j).1))
    (_ : ∀ e, J e = ∑ l ∈ Tᶜ, Z l e • J l) (_ : ∀ e ∈ Ts, J e = 0)
    (_ : ∀ j ∉ Ts, J j = -∑ l ∈ (T ∪ Ts)ᶜ,
      (P j l : ℂ) • (fun i => pathIntegral N n radicand baseDivisor hRadicand hOrders (η i) (γ l)))
    (_ : ∀ j (θ : Ω[EE⁄ℂ]), (∀ v ∈ D.skeleton, 0 ≤ v.ordDifferential θ) →
      (∃ g, IsPrimitiveAlong N n radicand baseDivisor hRadicand hOrders θ (γ j) g) ∧
        pathIntegral N n radicand baseDivisor hRadicand hOrders θ (γ j) = ∑ e, (Z j e : ℂ) * coverEdgeIntegral N n radicand baseDivisor hRadicand hOrders D θ e)
    (S : Finset (Place ℂ EE))
    (_ : ∀ C : D.ιC, ((D.cell C).carrier ∩ (S : Set (Place ℂ EE))).Subsingleton)
    (_ : ∀ v ∈ S, ∃ C : D.ιC, v ∈ (D.cell C).interior' ∧
      (D.cell C).ζ v = (D.cell C).R.q)
    (c : Place ℂ EE → D.ιC) (_ : ∀ v ∈ S, v ∈ (D.cell (c v)).interior')
    (θ : Ω[EE⁄ℂ]) (_ : ∀ v ∈ S, -1 ≤ v.ordDifferential θ)
    (_ : ∀ v : Place ℂ EE, v ∉ S → 0 ≤ v.ordDifferential θ) (i : κ),
    (∑ j ∈ (T ∪ Ts)ᶜ, ∑ l ∈ (T ∪ Ts)ᶜ,
      pathIntegral N n radicand baseDivisor hRadicand hOrders θ (γ j) * (P j l : ℂ) * pathIntegral N n radicand baseDivisor hRadicand hOrders (η i) (γ l)) =
      -(2 * π * Complex.I * ∑ v ∈ S,
        v.rationalEval (originalWeilKummerCover_residue_bijective N ℂ n radicand v) (v.uniformizer * v.differentialCoeff θ) *
          Ψ i (c v) ((D.cell (c v)).ζ v)) := by
  letI := placeTopology N n radicand baseDivisor hRadicand hOrders
  intro D η V Ψ J hP hJ T Ts Z P γ hdec hJ0 hrow hγi S hsep hcent c hc θ hpol hreg i
  have hskel := cover_regular_on_skeleton N n radicand baseDivisor hRadicand hOrders D S (fun v hv => ⟨c v, hc v hv⟩) θ hreg
  rw [cover_loop_bilinear_eq_neg_edge_jumps N n radicand baseDivisor hRadicand hOrders D η T Ts Z J P γ hdec hJ0 hrow θ
    (fun j => (hγi j θ hskel).2) i,
    ← cover_normalized_weighted_residue_sum N n radicand baseDivisor hRadicand hOrders D η V Ψ J hP hJ S hsep hcent c hc θ hpol hreg i]


theorem cover_riemann_cycle_bilinear :
    letI := placeTopology N n radicand baseDivisor hRadicand hOrders
    ∀ (D : RadialCellDissection (Place ℂ EE)) (η : κ → Ω[EE⁄ℂ])
    (V : D.ιC → Set ℂ) (Ψ : κ → D.ιC → ℂ → ℂ) (J : D.ιE → κ → ℂ)
    (_ : CoverPrimData N n radicand baseDivisor hRadicand hOrders D η V Ψ) (_ : IsJump D Ψ J)
    (T Ts : Finset D.ιE) (Z : D.ιE → D.ιE → ℤ) (P : D.ιE → D.ιE → ℤ)
    (γ : (j : D.ιE) → Path (D.vert (D.ends j).1) (D.vert (D.ends j).1))
    (_ : ∀ e, J e = ∑ l ∈ Tᶜ, Z l e • J l) (_ : ∀ e ∈ Ts, J e = 0)
    (_ : ∀ j ∉ Ts, J j = -∑ l ∈ (T ∪ Ts)ᶜ,
      (P j l : ℂ) • (fun i => pathIntegral N n radicand baseDivisor hRadicand hOrders (η i) (γ l)))
    (_ : ∀ j (θ : Ω[EE⁄ℂ]), (∀ v ∈ D.skeleton, 0 ≤ v.ordDifferential θ) →
      (∃ g, IsPrimitiveAlong N n radicand baseDivisor hRadicand hOrders θ (γ j) g) ∧
        pathIntegral N n radicand baseDivisor hRadicand hOrders θ (γ j) = ∑ e, (Z j e : ℂ) * coverEdgeIntegral N n radicand baseDivisor hRadicand hOrders D θ e)
    (i i' : κ),
    (∑ j ∈ (T ∪ Ts)ᶜ, ∑ l ∈ (T ∪ Ts)ᶜ,
      pathIntegral N n radicand baseDivisor hRadicand hOrders (η i') (γ j) * (P j l : ℂ) * pathIntegral N n radicand baseDivisor hRadicand hOrders (η i) (γ l)) = 0 := by
  letI := placeTopology N n radicand baseDivisor hRadicand hOrders
  intro D η V Ψ J hP hJ T Ts Z P γ hdec hJ0 hrow hγi i i'
  have h := cover_cycle_bilinear_eq_neg_residue N n radicand baseDivisor hRadicand hOrders D η V Ψ J hP hJ T Ts Z P γ hdec hJ0 hrow hγi
    ∅ (by simp) (by simp) (cellOf D) (by simp) (η i') (by simp)
    (fun Q _ => (mem_cover_regularDifferentials_iff_ord_nonneg N n radicand (η i')).mp (hP.2.2.2.2 i') Q) i
  simpa only [Finset.sum_empty, mul_zero, neg_zero] using h

end
end Dubon2026.SourceFunctionField.OriginalWeilCoverChart
