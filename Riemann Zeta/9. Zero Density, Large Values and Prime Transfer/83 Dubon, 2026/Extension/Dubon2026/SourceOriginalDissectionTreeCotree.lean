import Dubon2026.SourceOriginalCotreeComplementConnectivity

/-! DUB-17/18 -> original Abel-Jacobi -> 2g generating loops -> tree/cotree.
The primal and dual trees have disjoint actual edge sets. Their complement
has exactly twice the original regular-differential dimension. The original
Euler theorem supplies the numerical input at the actual-cover consumer.
-/
namespace Dubon2026.SourceFunctionField.CellGeometry.DissectionTrees
noncomputable section
open SourceCurve Set Real IntegerEdgeChains
attribute [local instance] OriginalChart.placeTopology OriginalChart.placeChartedSpace
variable {N : ℕ} [NeZero N]

theorem exists_tree_cotree
    (𝒟 : CellDissection N) [Nonempty 𝒟.ιC]
    (hvert : Function.Injective 𝒟.vert)
    (hends : ∀ v : 𝒟.ιV, ∃ e : 𝒟.ιE, (𝒟.ends e).1 = v ∨ (𝒟.ends e).2 = v)
    (hEuler : (Fintype.card 𝒟.ιV : ℤ) - (Fintype.card 𝒟.ιE : ℤ) + (Fintype.card 𝒟.ιC : ℤ)
      = 2 - 2 * (Module.finrank ℂ ↥(regularDifferentials ℂ (modularFunctionFieldOver N ℂ)) : ℤ)) :
    let Cside : 𝒟.ιE → Bool → 𝒟.ιC :=
      fun e s => (Function.surjInv 𝒟.side_bij.surjective (e, s)).1
    ∃ (𝒯 𝒯s : Finset 𝒟.ιE),
      (∀ u v : 𝒟.ιV, ∃! c : 𝒟.ιE → ℤ, (∀ e ∉ 𝒯, c e = 0) ∧
        ∀ w, (∑ e with (𝒟.ends e).2 = w, c e) - (∑ e with (𝒟.ends e).1 = w, c e) =
          (if w = v then (1 : ℤ) else 0) - (if w = u then 1 else 0)) ∧
      (∀ C C' : 𝒟.ιC, ∃! c : 𝒟.ιE → ℤ, (∀ e ∉ 𝒯s, c e = 0) ∧
        ∀ D, (∑ e with Cside e true = D, c e) - (∑ e with Cside e false = D, c e) =
          (if D = C' then (1 : ℤ) else 0) - (if D = C then 1 else 0)) ∧
      Disjoint 𝒯 𝒯s ∧
      (𝒯 ∪ 𝒯s)ᶜ.card = 2 * Module.finrank ℂ ↥(regularDifferentials ℂ (modularFunctionFieldOver N ℂ)) ∧
      ∀ u v : 𝒟.ιV, Relation.ReflTransGen
        (fun a b => ∃ e ∈ 𝒯, 𝒟.ends e = (a, b) ∨ 𝒟.ends e = (b, a)) u v := by
  classical

  haveI : Nonempty 𝒟.ιV := by
    obtain ⟨C⟩ := ‹Nonempty 𝒟.ιC›
    let k : Fin (𝒟.cell C).R.N := ⟨0, PowPullback.radialRegion_N_pos (𝒟.cell C).R⟩
    exact ⟨(𝒟.ends (𝒟.side C k).1).1⟩

  obtain ⟨𝒯s, _, h𝒯s, _⟩ := exists_spanningTree (fun e => DissectionTrees.Cside 𝒟 e true)
    (fun e => DissectionTrees.Cside 𝒟 e false) Finset.univ (Γstar_conn 𝒟)

  obtain ⟨𝒯, h𝒯sub, h𝒯, h𝒯walk⟩ := exists_spanningTree (hdΓ 𝒟) (tlΓ 𝒟) 𝒯sᶜ
    (Γconn_sdiff_cotree 𝒟 hvert hends 𝒯s h𝒯s)
  refine ⟨𝒯, 𝒯s, h𝒯, h𝒯s, ?_, ?_, ?_⟩
  ·
    exact Finset.disjoint_left.mpr (fun e he => Finset.mem_compl.mp (h𝒯sub he))
  ·
    have hTcard := spanningTree_card (hdΓ 𝒟) (tlΓ 𝒟) 𝒯 h𝒯
    have hTscard := spanningTree_card (fun e => DissectionTrees.Cside 𝒟 e true)
      (fun e => DissectionTrees.Cside 𝒟 e false) 𝒯s h𝒯s
    have hdisj : Disjoint 𝒯 𝒯s :=
      Finset.disjoint_left.mpr (fun e he => Finset.mem_compl.mp (h𝒯sub he))
    have hunion : (𝒯 ∪ 𝒯s).card = 𝒯.card + 𝒯s.card :=
      Finset.card_union_of_disjoint hdisj
    have hle : (𝒯 ∪ 𝒯s).card ≤ Fintype.card 𝒟.ιE := Finset.card_le_univ _
    have hcompl : ((𝒯 ∪ 𝒯s)ᶜ.card : ℤ) = (Fintype.card 𝒟.ιE : ℤ) - ((𝒯 ∪ 𝒯s).card : ℤ) := by
      have := Finset.card_compl (𝒯 ∪ 𝒯s)
      omega

    have hTZ : (𝒯.card : ℤ) + 1 = (Fintype.card 𝒟.ιV : ℤ) := by exact_mod_cast hTcard
    have hTsZ : (𝒯s.card : ℤ) + 1 = (Fintype.card 𝒟.ιC : ℤ) := by exact_mod_cast hTscard
    have hgoal : ((𝒯 ∪ 𝒯s)ᶜ.card : ℤ) =
        2 * (Module.finrank ℂ ↥(regularDifferentials ℂ (modularFunctionFieldOver N ℂ)) : ℤ) := by
      rw [hcompl]; push_cast [hunion]; linarith [hEuler, hTZ, hTsZ]
    exact_mod_cast hgoal
  ·
    intro u v
    refine Relation.ReflTransGen.mono (fun {a b} ⟨e, heT, hcase⟩ => ⟨e, heT, ?_⟩) (h𝒯walk u v)
    unfold hdΓ tlΓ at hcase
    rcases hcase with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
      [exact .inr (Prod.ext h2 h1); exact .inl (Prod.ext h2 h1)]

end
end Dubon2026.SourceFunctionField.CellGeometry.DissectionTrees
