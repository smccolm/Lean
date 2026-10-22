import Dubon2026.SourceOriginalPrimitivePolygonWord

/-! DUB-17/18 -> original Abel-Jacobi -> raw reciprocity.
The same constructed original dissection, trees, integer cycles, actual loops
and normalized cell primitives have a polygon word with the exact signed
jump formula and all original corner and integer subword-cycle clauses.
No polygon, primitive, jump or loop premise is supplied. The matrix and
analytic period-generation conclusions remain required.
-/
namespace Dubon2026.SourceFunctionField.CellGeometry
noncomputable section
open SourceCurve Set IntegerEdgeChains DissectionTrees DissectionPolygon OriginalEdgePaths
open KaehlerDifferential OriginalChart
attribute [local instance] OriginalChart.placeTopology OriginalChart.placeChartedSpace
variable {N : ℕ} [NeZero N] {κ : Type*}
local notation "F" => modularFunctionFieldOver N ℂ

theorem exists_original_primitive_polygon_word (P₀ : Place ℂ F) (S : Finset (Place ℂ F))
    (η : κ → Ω[F⁄ℂ]) (hη : ∀ i, η i ∈ regularDifferentials ℂ F) :
    ∃ (Marked : Finset ℂ) (A : OriginalGlobalCellCover N Marked)
      (T Ts : Finset A.dissection.ιE) (Z : A.dissection.ιE → A.dissection.ιE → ℤ),
      (∀ P ∈ insert P₀ (S : Set (Place ℂ F)), ∃ i : A.Index,
        P ∈ (A.cell i).interior' ∧ (A.cell i).ζ P = (A.cell i).R.q) ∧
      (∀ i : A.Index, ((A.cell i).carrier ∩ (S : Set (Place ℂ F))).Subsingleton) ∧
      IsTree (hdΓ A.dissection) (tlΓ A.dissection) T ∧
      IsTree (fun e => Cside A.dissection e true) (fun e => Cside A.dissection e false) Ts ∧
      Disjoint T Ts ∧
      (T ∪ Ts)ᶜ.card = 2 * Module.finrank ℂ (regularDifferentials ℂ F) ∧
      IsWalkConn (hdΓ A.dissection) (tlΓ A.dissection) T ∧
      PolygonWordConclusion A.dissection Ts ∧
      (∀ j w, (∑ e with (A.dissection.ends e).2 = w, Z j e) =
        (∑ e with (A.dissection.ends e).1 = w, Z j e)) ∧
      (∀ j ∈ Tᶜ, ∀ j' ∈ Tᶜ, Z j j' = if j = j' then 1 else 0) ∧
      (∀ j ∈ T, Z j = 0) ∧
      (∀ {B : Type*} [AddCommGroup B] (f : A.dissection.ιE → B),
        (∀ w, (∑ e with (A.dissection.ends e).2 = w, f e) =
          (∑ e with (A.dissection.ends e).1 = w, f e)) →
        ∀ e, f e = ∑ j ∈ Tᶜ, Z j e • f j) ∧
      ∃ γ : (j : A.dissection.ιE) →
          Path (A.dissection.vert (A.dissection.ends j).1) (A.dissection.vert (A.dissection.ends j).1),
        (∀ j t, γ j t ∈ A.dissection.skeleton) ∧
        (∀ j (θ : Ω[F⁄ℂ]), RegOnSkeleton A.dissection θ →
          (∃ g, IsPrimitiveAlong N θ (γ j) g) ∧
          pathIntegral N θ (γ j) = ∑ e, (Z j e : ℂ) * A.dissection.edgeInt θ e) ∧
        ∃ (C₀ : A.dissection.ιC) (V : A.dissection.ιC → Set ℂ)
          (Ψ : κ → A.dissection.ιC → ℂ → ℂ) (J : A.dissection.ιE → κ → ℂ),
          P₀ ∈ (A.dissection.cell C₀).interior' ∧
          (∀ C, IsOpen (V C) ∧ (A.dissection.cell C).R.q ∈ V C ∧
            StarConvex ℝ (A.dissection.cell C).R.q (V C) ∧
            (A.dissection.cell C).R.K ⊆ V C ∧ V C ⊆ (A.dissection.cell C).ζ.target) ∧
          (∀ i C, ∀ w ∈ V C, HasDerivAt (Ψ i C) (coeffIn (A.dissection.cell C).ζ (η i) w) w) ∧
          (∀ e i,
            let p := A.dissection.arcOf (e, true)
            let n := A.dissection.arcOf (e, false)
            ∀ s ∈ (A.dissection.cell p.1).R.arcIcc p.2,
              Ψ i p.1 ((A.dissection.cell p.1).R.loop s) -
                Ψ i n.1 ((A.dissection.cell n.1).ζ ((A.dissection.cell p.1).bdry s)) = J e i) ∧
          (∀ e ∈ Ts, J e = 0) ∧ (∀ i, Ψ i C₀ ((A.dissection.cell C₀).ζ P₀) = 0) ∧
          (∀ w, (∑ e with (A.dissection.ends e).2 = w, J e) =
            ∑ e with (A.dissection.ends e).1 = w, J e) ∧
          (AddSubgroup.closure (Set.range J) ≤
            AddSubgroup.closure (J '' ((T ∪ Ts)ᶜ : Finset A.dissection.ιE))) ∧
          DissectionPeriods.PrimitivePolygonConclusion A.dissection η Ts J := by
  obtain ⟨Marked, A, T, Ts, Z, hcent, hsep, ht, hts, hd, hc, hw, hword,
    hz, hdelta, hzero, hdec, γ, hγs, hγi, C₀, V, Ψ, J, hP₀, hV, hΨ, hJ, hJ0, hΨ0,
    hcir, hgen⟩ := exists_original_jump_cycle_reduction P₀ S η hη
  have hP : DissectionPeriods.PrimData A.dissection η V Ψ :=
    ⟨fun C => (hV C).1, fun C => (hV C).2.2.2.1, fun C => (hV C).2.2.2.2,
      hΨ, fun i Q => Q.ord_nonneg_of_mem ((mem_original_regularDifferentials_iff N ℂ (η i)).mp (hη i) Q)⟩
  have hW := DissectionPeriods.exists_primitive_polygon_word A.dissection η V Ψ hP Ts J
    (fun i e => hJ e i) hJ0 hword
  exact ⟨Marked, A, T, Ts, Z, hcent, hsep, ht, hts, hd, hc, hw, hword,
    hz, hdelta, hzero, hdec, γ, hγs, hγi, C₀, V, Ψ, J, hP₀, hV, hΨ, hJ, hJ0, hΨ0,
    hcir, hgen, hW⟩

end
end Dubon2026.SourceFunctionField.CellGeometry
