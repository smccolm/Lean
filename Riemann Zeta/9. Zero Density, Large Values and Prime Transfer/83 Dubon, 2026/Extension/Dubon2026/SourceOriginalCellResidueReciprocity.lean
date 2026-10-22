import Dubon2026.SourceOriginalNormalizedAbelReadings
import Dubon2026.SourceOriginalBilinearPeriodPolygon
import Dubon2026.SourceOriginalSimplePoleSpaceFinite

/-! DUB-17/18 -> original Abel-Jacobi -> raw residue reciprocity.
The exact weighted cell identity becomes the original Abel-divisor identity.
Zero residue removes poles outside the divisor support; skew symmetry fixes
the order of the two period factors, and normalized Abel readings supply one
common integer correction for all basis coordinates.
-/
namespace Dubon2026.SourceFunctionField.CellGeometry.DissectionPeriods
noncomputable section
open SourceCurve Set KaehlerDifferential OriginalChart
open scoped Real
attribute [local instance] placeTopology placeChartedSpace
variable {N : ℕ} [NeZero N]
local notation "F" => modularFunctionFieldOver N ℂ

theorem residue_reciprocity_of_weighted_cells {n : ℕ} (D : CellDissection N)
    (η : Fin n → Ω[F⁄ℂ]) (V : D.ιC → Set ℂ) (Ψ : Fin n → D.ιC → ℂ → ℂ)
    (J : D.ιE → Fin n → ℂ) (hP : PrimData D η V Ψ) (hJ : IsJump D Ψ J)
    (T Ts : Finset D.ιE)
    (γ : (j : D.ιE) → Path (D.vert (D.ends j).1) (D.vert (D.ends j).1))
    (hcl : AddSubgroup.closure (range J) ≤ AddSubgroup.closure
      ((fun l i => pathIntegral N (η i) (γ l)) '' ((T ∪ Ts)ᶜ : Finset D.ιE)))
    (P₀ : Place ℂ F) (hzero : gvec D Ψ P₀ (cellOf D P₀) = 0)
    (S : Finset (Place ℂ F)) (Q : D.ιE → D.ιE → ℤ)
    (hskew : ∀ j ∈ (T ∪ Ts)ᶜ, ∀ l ∈ (T ∪ Ts)ᶜ, Q l j = -Q j l)
    (hweighted : ∀ θ : Ω[F⁄ℂ], (∀ v ∈ S, -1 ≤ v.ordDifferential θ) →
      (∀ v : Place ℂ F, v ∉ S → 0 ≤ v.ordDifferential θ) → ∀ i,
      (∑ j ∈ (T ∪ Ts)ᶜ, ∑ l ∈ (T ∪ Ts)ᶜ,
        pathIntegral N θ (γ j) * (Q j l : ℂ) * pathIntegral N (η i) (γ l)) =
        -(2 * Real.pi * Complex.I * ∑ v ∈ S,
          originalPlaceEval N ℂ v (v.uniformizer * v.differentialCoeff θ) *
            gvec D Ψ v (cellOf D v) i))
    (E : Divisor ℂ F) (θ : Ω[F⁄ℂ]) (hθ : ∀ v : Place ℂ F, -1 ≤ v.ordDifferential θ)
    (hres : ∀ v : Place ℂ F,
      originalPlaceEval N ℂ v (v.uniformizer * v.differentialCoeff θ) = (E v : ℂ))
    (hE : E.support ⊆ S) :
    ∃ c : D.ιE → ℤ, ∀ i,
      (∑ j ∈ (T ∪ Ts)ᶜ, ∑ l ∈ (T ∪ Ts)ᶜ,
        (Q j l : ℂ) * pathIntegral N (η i) (γ j) * pathIntegral N θ (γ l)) =
        2 * Real.pi * Complex.I * (abelJacobiDiv N η P₀ E i +
          ∑ l ∈ (T ∪ Ts)ᶜ, (c l : ℂ) * pathIntegral N (η i) (γ l)) := by
  have hreg : ∀ v : Place ℂ F, v ∉ S → 0 ≤ v.ordDifferential θ := by
    intro v hv
    apply original_simple_pole_regular_of_residue_zero N v θ (hθ v)
    rw [originalDifferentialResidue_simplePole N v θ (hθ v), hres]
    have he : E v = 0 := Finsupp.notMem_support_iff.mp (fun h => hv (hE h))
    rw [he, Int.cast_zero]
  obtain ⟨c, hc⟩ := weighted_readings_eq_abel_add_periods D η V Ψ J hP hJ T Ts γ hcl
    P₀ hzero S E hE
  refine ⟨c, fun i => ?_⟩
  rw [← hc i]
  have hw := hweighted θ (fun v _ => hθ v) hreg i
  simp_rw [hres] at hw
  calc (∑ j ∈ (T ∪ Ts)ᶜ, ∑ l ∈ (T ∪ Ts)ᶜ,
        (Q j l : ℂ) * pathIntegral N (η i) (γ j) * pathIntegral N θ (γ l)) =
      -(∑ j ∈ (T ∪ Ts)ᶜ, ∑ l ∈ (T ∪ Ts)ᶜ,
        pathIntegral N θ (γ j) * (Q j l : ℂ) * pathIntegral N (η i) (γ l)) := by
          rw [Finset.sum_comm, ← Finset.sum_neg_distrib]
          refine Finset.sum_congr rfl fun l hl => ?_
          rw [← Finset.sum_neg_distrib]
          refine Finset.sum_congr rfl fun j hj => ?_
          rw [hskew j hj l hl, Int.cast_neg]
          ring
    _ = _ := by rw [hw, neg_neg]

end
end Dubon2026.SourceFunctionField.CellGeometry.DissectionPeriods
