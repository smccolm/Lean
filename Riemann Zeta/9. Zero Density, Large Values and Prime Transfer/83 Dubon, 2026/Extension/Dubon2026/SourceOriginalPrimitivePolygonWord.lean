import Dubon2026.SourceOriginalPolygonWordPrimitiveSum

/-! DUB-17/18 -> original Abel-Jacobi -> raw reciprocity.
The exact polygon word, its actual corner paths and its closed integer subword
cycles also carry the signed primitive-jump formula. The same word witnesses
all clauses, so the future integer matrix uses this actual analytic formula.
-/
namespace Dubon2026.SourceFunctionField.CellGeometry.DissectionPeriods
noncomputable section
open SourceCurve Set KaehlerDifferential
attribute [local instance] OriginalChart.placeTopology OriginalChart.placeChartedSpace
variable {N : ℕ} [NeZero N] {κ : Type*}
local notation "F" => modularFunctionFieldOver N ℂ

/-- The actual polygon-word contract together with its exact signed primitive-jump sum. -/
abbrev PrimitivePolygonConclusion (𝒟 : CellDissection N) (η : κ → Ω[F⁄ℂ])
    (𝒯s : Finset 𝒟.ιE) (J : 𝒟.ιE → κ → ℂ) : Prop :=
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
      ∀ (j : 𝒟.ιE) (hj : j ∉ 𝒯s),
        J j = -∑ i ∈ Finset.univ.filter
            (fun i : ZMod m => i ≠ wd.symm ⟨(j, true), hj⟩ ∧
              (i - wd.symm ⟨(j, true), hj⟩).val <
                (wd.symm ⟨(j, false), hj⟩ - wd.symm ⟨(j, true), hj⟩).val),
          (if (wd i).1.2 then (1 : ℂ) else -1) • Ivec 𝒟 η (wd i).1.1

theorem exists_primitive_polygon_word (D : CellDissection N) (η : κ → Ω[F⁄ℂ])
    (V : D.ιC → Set ℂ) (Ψ : κ → D.ιC → ℂ → ℂ) (hP : PrimData D η V Ψ)
    (Ts : Finset D.ιE) (J : D.ιE → κ → ℂ) (hJ : IsJump D Ψ J)
    (hJ0 : ∀ e ∈ Ts, J e = 0) (hw : DissectionPolygon.PolygonWordConclusion D Ts) :
    PrimitivePolygonConclusion D η Ts J := by
  unfold PrimitivePolygonConclusion
  intro Cside startV endV L m
  obtain ⟨hm, wd, hw₁, hw₃⟩ := hw
  letI := hm
  refine ⟨hm, wd, hw₁, hw₃, ?_⟩
  exact word_identity D η V Ψ hP hJ hJ0 wd hw₁

end
end Dubon2026.SourceFunctionField.CellGeometry.DissectionPeriods
