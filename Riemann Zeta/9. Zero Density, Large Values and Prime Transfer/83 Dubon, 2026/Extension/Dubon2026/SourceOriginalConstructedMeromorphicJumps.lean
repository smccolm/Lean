import Dubon2026.SourceOriginalConstructedMeromorphicPrimitives
import Dubon2026.SourceOriginalMeromorphicNormalizedJumps

/-! DUB-17/18 -> original Abel-Jacobi -> meromorphic loop-period generation.
On the same actual original dissection, normalize the finite simple-pole basis
boundary primitives so all dual-tree jumps vanish. Keep the exact logarithmic
one-turn increment and original differential arc-integral identity, together
with every previously constructed regular-period and bilinear clause.
Meromorphic loop generation modulo residues and raw reciprocity remain open.
-/
namespace Dubon2026.SourceFunctionField.CellGeometry
noncomputable section
open SourceCurve Set IntegerEdgeChains DissectionTrees DissectionPolygon OriginalEdgePaths
open KaehlerDifferential OriginalChart
attribute [local instance] OriginalChart.placeTopology OriginalChart.placeChartedSpace
variable {N : ℕ} [NeZero N]
local notation "F" => modularFunctionFieldOver N ℂ

theorem exists_original_meromorphic_normalized_jumps (P₀ : Place ℂ F) (S : Finset (Place ℂ F))
    {n : ℕ} (b : Module.Basis (Fin n) ℂ (regularDifferentials ℂ F)) :
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
          (Ψ : Fin n → A.dissection.ιC → ℂ → ℂ) (J : A.dissection.ιE → Fin n → ℂ),
          P₀ ∈ (A.dissection.cell C₀).interior' ∧
          (∀ C, IsOpen (V C) ∧ (A.dissection.cell C).R.q ∈ V C ∧
            StarConvex ℝ (A.dissection.cell C).R.q (V C) ∧
            (A.dissection.cell C).R.K ⊆ V C ∧ V C ⊆ (A.dissection.cell C).ζ.target) ∧
          (∀ i C, ∀ w ∈ V C, HasDerivAt (Ψ i C) (coeffIn (A.dissection.cell C).ζ ((fun i => (b i : Ω[F⁄ℂ])) i) w) w) ∧
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
          DissectionPeriods.BilinearCyclePeriodPolygonConclusion A.dissection (fun i => (b i : Ω[F⁄ℂ])) T Ts J γ S Ψ ∧
          DissectionPeriods.RegularCycleGeneration A.dissection (fun i => (b i : Ω[F⁄ℂ])) T Ts γ ∧
          ∃ (d : ℕ) (bθ : Module.Basis (Fin d) ℂ (originalSimplePoleSpace N S)),
            (∀ θ : originalSimplePoleSpace N S, ∃ a : Fin d → ℂ,
              (θ : Ω[F⁄ℂ]) = ∑ i, a i • (bθ i : Ω[F⁄ℂ])) ∧
            ∃ (Vθ : A.dissection.ιC → Set ℂ)
              (Ψθ : Fin d → A.dissection.ιC → ℂ → ℂ),
              MeromorphicPeriods.RegPrimData S (fun i => (bθ i : Ω[F⁄ℂ])) Vθ Ψθ ∧
              ∃ Jθ : A.dissection.ιE → Fin d → ℂ,
                MeromorphicPeriods.IsJumpH A.dissection
                  (MeromorphicPeriods.hfun S (fun i => (bθ i : Ω[F⁄ℂ])) Ψθ) Jθ ∧
                (∀ e ∈ Ts, Jθ e = 0) ∧
                (∀ C s, MeromorphicPeriods.hfun S (fun i => (bθ i : Ω[F⁄ℂ])) Ψθ C (s + 2 * Real.pi) =
                  MeromorphicPeriods.hfun S (fun i => (bθ i : Ω[F⁄ℂ])) Ψθ C s +
                    (2 * Real.pi * Complex.I) • MeromorphicPeriods.ρ A.dissection S (fun i => (bθ i : Ω[F⁄ℂ])) C) ∧
                ∀ r C (k : Fin (A.dissection.cell C).R.N),
                  (∫ s in ((A.dissection.cell C).R.φs k.castSucc)..((A.dissection.cell C).R.φs k.succ),
                    (A.dissection.cell C).bdryIntegrand (bθ r) s) =
                    MeromorphicPeriods.hfun S (fun i => (bθ i : Ω[F⁄ℂ])) Ψθ C ((A.dissection.cell C).R.φs k.succ) r -
                      MeromorphicPeriods.hfun S (fun i => (bθ i : Ω[F⁄ℂ])) Ψθ C ((A.dissection.cell C).R.φs k.castSucc) r := by
  obtain ⟨Marked, A, T, Ts, Z, hcent, hsep, ht, hts, hd, hc, hw, hword,
    hz, hdelta, hzero, hdec, γ, hγs, hγi, C₀, V, Ψ, J, hP₀, hV, hΨ, hJ, hJ0, hΨ0,
    hcir, hgen, hW, hR, d, bθ, hspan, Vθ, Ψθ, hprim⟩ :=
    exists_original_meromorphic_cell_primitives P₀ S b
  have hS : MeromorphicPeriods.PolePos A.dissection S :=
    ⟨hsep, fun v hv => hcent v (Set.mem_insert_of_mem P₀ hv)⟩
  obtain ⟨Ψθ', Jθ, hprim', hJθ, hzeroθ⟩ := MeromorphicPeriods.normalize_regPrimData
    S (fun i => (bθ i : Ω[F⁄ℂ])) hprim Ts hts C₀
  refine ⟨Marked, A, T, Ts, Z, hcent, hsep, ht, hts, hd, hc, hw, hword,
    hz, hdelta, hzero, hdec, γ, hγs, hγi, C₀, V, Ψ, J, hP₀, hV, hΨ, hJ, hJ0, hΨ0,
    hcir, hgen, hW, hR, d, bθ, hspan, Vθ, Ψθ', hprim', Jθ, hJθ, hzeroθ, ?_, ?_⟩
  · exact fun C s => MeromorphicPeriods.hfun_add_two_pi S (fun i => (bθ i : Ω[F⁄ℂ])) Ψθ' C s
  · exact fun r C k => MeromorphicPeriods.arc_ftc_hfun S (fun i => (bθ i : Ω[F⁄ℂ]))
      (fun i => (bθ i).2) hS hprim' r C k

end
end Dubon2026.SourceFunctionField.CellGeometry
