import Dubon2026.SourceOriginalNormalizedWeightedEdges
import Dubon2026.SourceOriginalWeightedCycleSums
import Dubon2026.SourceOriginalConstructedUnimodularPeriods

/-! DUB-17/18 -> original Abel-Jacobi -> Riemann and residue reciprocity.
Convert the normalized weighted residue identity into the exact bilinear sum
of actual cycle periods. The regular specialization has zero residue term.
The same cycle integral formula and the same word-matrix rows are consumed.
-/
namespace Dubon2026.SourceFunctionField.CellGeometry.DissectionPeriods
noncomputable section
open SourceCurve Set KaehlerDifferential OriginalChart OriginalEdgePaths
open scoped Real
attribute [local instance] placeTopology placeChartedSpace
variable {N : ℕ} [NeZero N] {κ : Type*}
local notation "F" => modularFunctionFieldOver N ℂ

theorem loop_bilinear_eq_neg_edge_jumps (D : CellDissection N) (η : κ → Ω[F⁄ℂ])
    (T Ts : Finset D.ιE) (Z : D.ιE → D.ιE → ℤ) (J : D.ιE → κ → ℂ)
    (P : D.ιE → D.ιE → ℤ)
    (γ : (j : D.ιE) → Path (D.vert (D.ends j).1) (D.vert (D.ends j).1))
    (hdec : ∀ e, J e = ∑ l ∈ Tᶜ, Z l e • J l) (hJ0 : ∀ e ∈ Ts, J e = 0)
    (hrow : ∀ j ∉ Ts, J j = -∑ l ∈ (T ∪ Ts)ᶜ,
      (P j l : ℂ) • (fun i => pathIntegral N (η i) (γ l)))
    (θ : Ω[F⁄ℂ])
    (hγθ : ∀ j, pathIntegral N θ (γ j) = ∑ e, (Z j e : ℂ) * D.edgeInt θ e) (i : κ) :
    (∑ j ∈ (T ∪ Ts)ᶜ, ∑ l ∈ (T ∪ Ts)ᶜ,
      pathIntegral N θ (γ j) * (P j l : ℂ) * pathIntegral N (η i) (γ l)) =
        -∑ e, J e i * D.edgeInt θ e := by
  have hz : ∀ j, cycleScalarIntegral Z (D.edgeInt θ) j = pathIntegral N θ (γ j) :=
    fun j => (hγθ j).symm
  have h := sum_mul_jump_eq_cycle_bilinear hdec hJ0
    (fun l i => pathIntegral N (η i) (γ l)) P hrow (D.edgeInt θ) i
  simp_rw [hz] at h
  calc
    _ = -∑ e, D.edgeInt θ e * J e i := (neg_eq_iff_eq_neg).mp h.symm
    _ = _ := by
      congr 1
      exact Finset.sum_congr rfl fun e _ => mul_comm _ _

theorem cycle_bilinear_eq_neg_residue (D : CellDissection N) (η : κ → Ω[F⁄ℂ])
    (V : D.ιC → Set ℂ) (Ψ : κ → D.ιC → ℂ → ℂ) (J : D.ιE → κ → ℂ)
    (hP : PrimData D η V Ψ) (hJ : IsJump D Ψ J)
    (T Ts : Finset D.ιE) (Z : D.ιE → D.ιE → ℤ) (P : D.ιE → D.ιE → ℤ)
    (γ : (j : D.ιE) → Path (D.vert (D.ends j).1) (D.vert (D.ends j).1))
    (hdec : ∀ e, J e = ∑ l ∈ Tᶜ, Z l e • J l) (hJ0 : ∀ e ∈ Ts, J e = 0)
    (hrow : ∀ j ∉ Ts, J j = -∑ l ∈ (T ∪ Ts)ᶜ,
      (P j l : ℂ) • (fun i => pathIntegral N (η i) (γ l)))
    (hγi : ∀ j (θ : Ω[F⁄ℂ]), RegOnSkeleton D θ →
      (∃ g, IsPrimitiveAlong N θ (γ j) g) ∧
        pathIntegral N θ (γ j) = ∑ e, (Z j e : ℂ) * D.edgeInt θ e)
    (S : Finset (Place ℂ F))
    (hsep : ∀ C : D.ιC, ((D.cell C).carrier ∩ (S : Set (Place ℂ F))).Subsingleton)
    (hcent : ∀ v ∈ S, ∃ C : D.ιC, v ∈ (D.cell C).interior' ∧
      (D.cell C).ζ v = (D.cell C).R.q)
    (c : Place ℂ F → D.ιC) (hc : ∀ v ∈ S, v ∈ (D.cell (c v)).interior')
    (θ : Ω[F⁄ℂ]) (hpol : ∀ v ∈ S, -1 ≤ v.ordDifferential θ)
    (hreg : ∀ v : Place ℂ F, v ∉ S → 0 ≤ v.ordDifferential θ) (i : κ) :
    (∑ j ∈ (T ∪ Ts)ᶜ, ∑ l ∈ (T ∪ Ts)ᶜ,
      pathIntegral N θ (γ j) * (P j l : ℂ) * pathIntegral N (η i) (γ l)) =
      -(2 * π * Complex.I * ∑ v ∈ S,
        originalPlaceEval N ℂ v (v.uniformizer * v.differentialCoeff θ) *
          Ψ i (c v) ((D.cell (c v)).ζ v)) := by
  have hskel := D.regular_on_skeleton S (fun v hv => ⟨c v, hc v hv⟩) θ hreg
  rw [loop_bilinear_eq_neg_edge_jumps D η T Ts Z J P γ hdec hJ0 hrow θ
    (fun j => (hγi j θ hskel).2) i,
    ← normalized_weighted_residue_sum D η V Ψ J hP hJ S hsep hcent c hc θ hpol hreg i]

theorem riemann_cycle_bilinear (D : CellDissection N) (η : κ → Ω[F⁄ℂ])
    (V : D.ιC → Set ℂ) (Ψ : κ → D.ιC → ℂ → ℂ) (J : D.ιE → κ → ℂ)
    (hP : PrimData D η V Ψ) (hJ : IsJump D Ψ J)
    (T Ts : Finset D.ιE) (Z : D.ιE → D.ιE → ℤ) (P : D.ιE → D.ιE → ℤ)
    (γ : (j : D.ιE) → Path (D.vert (D.ends j).1) (D.vert (D.ends j).1))
    (hdec : ∀ e, J e = ∑ l ∈ Tᶜ, Z l e • J l) (hJ0 : ∀ e ∈ Ts, J e = 0)
    (hrow : ∀ j ∉ Ts, J j = -∑ l ∈ (T ∪ Ts)ᶜ,
      (P j l : ℂ) • (fun i => pathIntegral N (η i) (γ l)))
    (hγi : ∀ j (θ : Ω[F⁄ℂ]), RegOnSkeleton D θ →
      (∃ g, IsPrimitiveAlong N θ (γ j) g) ∧
        pathIntegral N θ (γ j) = ∑ e, (Z j e : ℂ) * D.edgeInt θ e)
    (i i' : κ) :
    (∑ j ∈ (T ∪ Ts)ᶜ, ∑ l ∈ (T ∪ Ts)ᶜ,
      pathIntegral N (η i') (γ j) * (P j l : ℂ) * pathIntegral N (η i) (γ l)) = 0 := by
  have h := cycle_bilinear_eq_neg_residue D η V Ψ J hP hJ T Ts Z P γ hdec hJ0 hrow hγi
    ∅ (by simp) (by simp) (cellOf D) (by simp) (η i') (by simp)
    (fun Q _ => hP.hη i' Q) i
  simpa only [Finset.sum_empty, mul_zero, neg_zero] using h

end
end Dubon2026.SourceFunctionField.CellGeometry.DissectionPeriods
