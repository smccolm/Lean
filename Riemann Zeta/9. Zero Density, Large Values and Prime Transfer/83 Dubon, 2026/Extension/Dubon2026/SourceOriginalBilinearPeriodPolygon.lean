import Dubon2026.SourceOriginalCycleResidueBilinear

/-! DUB-17/18 -> original Abel-Jacobi -> exact bilinear period relations.
The same actual polygon and unimodular matrix now satisfy the Riemann bilinear
relation and the weighted residue reciprocity identity. The normalized cell
primitive readings are those used in its exact jump-to-period rows.
Meromorphic loop generation and the final Abel-path comparison remain required.
-/
namespace Dubon2026.SourceFunctionField.CellGeometry.DissectionPeriods
noncomputable section
open SourceCurve Set KaehlerDifferential OriginalChart OriginalEdgePaths
open scoped Real
attribute [local instance] OriginalChart.placeTopology OriginalChart.placeChartedSpace
variable {N : ℕ} [NeZero N] {κ : Type*}
local notation "F" => modularFunctionFieldOver N ℂ

/-- The actual polygon data, exact period matrix rows and generation of jumps by its loop periods. -/
abbrev BilinearCyclePeriodPolygonConclusion (𝒟 : CellDissection N) (η : κ → Ω[F⁄ℂ])
    (𝒯 𝒯s : Finset 𝒟.ιE) (J : 𝒟.ιE → κ → ℂ)
    (γ : (j : 𝒟.ιE) → Path (𝒟.vert (𝒟.ends j).1) (𝒟.vert (𝒟.ends j).1)) (S : Finset (Place ℂ F)) (Ψ : κ → 𝒟.ιC → ℂ → ℂ) : Prop :=
    let Cside : 𝒟.ιE → Bool → 𝒟.ιC :=
      fun e s => (Function.surjInv 𝒟.side_bij.surjective (e, s)).1
    let startV : 𝒟.ιE × Bool → 𝒟.ιV := fun q => if q.2 then (𝒟.ends q.1).1 else (𝒟.ends q.1).2
    let endV : 𝒟.ιE × Bool → 𝒟.ιV := fun q => if q.2 then (𝒟.ends q.1).2 else (𝒟.ends q.1).1
    let L := {q : 𝒟.ιE × Bool // q.1 ∉ 𝒯s}
    let m := Fintype.card L
    ∃ (_ : NeZero m) (wd : ZMod m ≃ L),
      (∀ i : ZMod m, endV (wd i).1 = startV (wd (i + 1)).1 ∧
        ∃ cs : List 𝒟.ιC, cs.head? = some (Cside (wd i).1.1 (wd i).1.2) ∧
          cs.getLast? = some (Cside (wd (i + 1)).1.1 (wd (i + 1)).1.2) ∧
          cs.IsChain (fun D D' => ∃ g ∈ 𝒯s,
            ((Cside g true = D ∧ Cside g false = D') ∨
             (Cside g true = D' ∧ Cside g false = D)) ∧
            (endV (wd i).1 = (𝒟.ends g).1 ∨ endV (wd i).1 = (𝒟.ends g).2))) ∧
      (∀ (e : 𝒟.ιE) (he : e ∉ 𝒯s),
        let αe : ZMod m := wd.symm ⟨(e, true), he⟩
        let βe : ZMod m := wd.symm ⟨(e, false), he⟩
        let pe : 𝒟.ιE → ℤ := fun e' =>
          ∑ i ∈ Finset.univ.filter
              (fun i : ZMod m => i ≠ αe ∧ (i - αe).val < (βe - αe).val),
            (if (wd i).1.2 then (1 : ℤ) else (-1)) * (if (wd i).1.1 = e' then 1 else 0)
        ∀ w : 𝒟.ιV,
          (∑ f with (𝒟.ends f).2 = w, pe f) = (∑ f with (𝒟.ends f).1 = w, pe f)) ∧
      (∀ (j : 𝒟.ιE) (hj : j ∉ 𝒯s),
        J j = -∑ i ∈ Finset.univ.filter
            (fun i : ZMod m => i ≠ wd.symm ⟨(j, true), hj⟩ ∧
              (i - wd.symm ⟨(j, true), hj⟩).val <
                (wd.symm ⟨(j, false), hj⟩ - wd.symm ⟨(j, true), hj⟩).val),
          (if (wd i).1.2 then (1 : ℂ) else -1) • Ivec 𝒟 η (wd i).1.1) ∧
      (∀ j ∉ 𝒯s, J j = -∑ l ∈ (𝒯 ∪ 𝒯s)ᶜ,
        (wordMatrix wd j l : ℂ) • (fun i => OriginalChart.pathIntegral N (η i) (γ l))) ∧
      AddSubgroup.closure (Set.range J) ≤
        AddSubgroup.closure ((fun l i => OriginalChart.pathIntegral N (η i) (γ l)) ''
          ((𝒯 ∪ 𝒯s)ᶜ : Finset 𝒟.ιE)) ∧
      (complementaryWordMatrix 𝒯 𝒯s wd).transpose = -complementaryWordMatrix 𝒯 𝒯s wd ∧
      IsUnit (complementaryWordMatrix 𝒯 𝒯s wd).det ∧
      (∀ i i', (∑ j ∈ (𝒯 ∪ 𝒯s)ᶜ, ∑ l ∈ (𝒯 ∪ 𝒯s)ᶜ,
        pathIntegral N (η i') (γ j) * (wordMatrix wd j l : ℂ) *
          pathIntegral N (η i) (γ l)) = 0) ∧
      ∀ (θ : Ω[F⁄ℂ]), (∀ v ∈ S, -1 ≤ v.ordDifferential θ) →
        (∀ v : Place ℂ F, v ∉ S → 0 ≤ v.ordDifferential θ) → ∀ i,
        (∑ j ∈ (𝒯 ∪ 𝒯s)ᶜ, ∑ l ∈ (𝒯 ∪ 𝒯s)ᶜ,
          pathIntegral N θ (γ j) * (wordMatrix wd j l : ℂ) *
            pathIntegral N (η i) (γ l)) =
          -(2 * π * Complex.I * ∑ v ∈ S,
            originalPlaceEval N ℂ v (v.uniformizer * v.differentialCoeff θ) *
              Ψ i (cellOf 𝒟 v) ((𝒟.cell (cellOf 𝒟 v)).ζ v))


theorem bilinear_period_polygon_of_primitives (D : CellDissection N) (η : κ → Ω[F⁄ℂ])
    (V : D.ιC → Set ℂ) (Ψ : κ → D.ιC → ℂ → ℂ) (J : D.ιE → κ → ℂ)
    (hP : PrimData D η V Ψ) (hJ : IsJump D Ψ J)
    (T Ts : Finset D.ιE) (Z : D.ιE → D.ιE → ℤ)
    (γ : (j : D.ιE) → Path (D.vert (D.ends j).1) (D.vert (D.ends j).1))
    (hdec : ∀ e, J e = ∑ l ∈ Tᶜ, Z l e • J l) (hJ0 : ∀ e ∈ Ts, J e = 0)
    (hγi : ∀ j (θ : Ω[F⁄ℂ]), RegOnSkeleton D θ →
      (∃ g, IsPrimitiveAlong N θ (γ j) g) ∧
        pathIntegral N θ (γ j) = ∑ e, (Z j e : ℂ) * D.edgeInt θ e)
    (S : Finset (Place ℂ F))
    (hsep : ∀ C : D.ιC, ((D.cell C).carrier ∩ (S : Set (Place ℂ F))).Subsingleton)
    (hcent : ∀ v ∈ S, ∃ C : D.ιC, v ∈ (D.cell C).interior' ∧
      (D.cell C).ζ v = (D.cell C).R.q)
    (hW : UnimodularCyclePeriodPolygonConclusion D η T Ts J γ) :
    BilinearCyclePeriodPolygonConclusion D η T Ts J γ S Ψ := by
  obtain ⟨hm, wd, hw₁, hw₃, hwjump, hrow, hcl, hskew, hu⟩ := hW
  letI := hm
  have hc : ∀ v ∈ S, v ∈ (D.cell (cellOf D v)).interior' := by
    intro v hv
    obtain ⟨C, hC, _⟩ := hcent v hv
    have he := D.eq_of_interior_mem_carrier hC (mem_cellOf D v)
    rw [← he]
    exact hC
  have hri := riemann_cycle_bilinear D η V Ψ J hP hJ T Ts Z (wordMatrix wd) γ hdec hJ0 hrow hγi
  have hres := cycle_bilinear_eq_neg_residue D η V Ψ J hP hJ T Ts Z (wordMatrix wd) γ
    hdec hJ0 hrow hγi S hsep hcent (cellOf D) hc
  unfold BilinearCyclePeriodPolygonConclusion
  intro Cside startV endV L m
  exact ⟨hm, wd, hw₁, hw₃, hwjump, hrow, hcl, hskew, hu, hri, hres⟩

end
end Dubon2026.SourceFunctionField.CellGeometry.DissectionPeriods
