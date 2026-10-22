import Dubon2026.SourceOriginalQuotientArcGeometry

/-! DUB-17/18 -> original Abel-Jacobi -> meromorphic loop-period generation.
The actual normalized logarithmic primitives satisfy every additive arc-value
clause modulo residue periods. Reuse original arc integration and reversal,
cyclic successor bijectivity, actual polygon corners and radial injectivity.
Adapted from S_AlgebraicCurve_CellDissection_exists_int_pathIntegral_eq_sum_periods_add_sum_residues,
anthropics/fermats-last-theorem, Apache-2.0,
commit 6e837e75355538c7f80bab5b956861e86c4eacc2.
-/
namespace Dubon2026.SourceFunctionField.CellGeometry.MeromorphicPeriods
noncomputable section
open SourceCurve Set Complex KaehlerDifferential ArcPeriods DissectionTrees CellDissection
open scoped Real
attribute [local instance] OriginalChart.placeTopology OriginalChart.placeChartedSpace
variable {N : ℕ} [NeZero N] {R : Type*}
local notation "F" => modularFunctionFieldOver N ℂ

theorem arcValuesH {𝒟 : CellDissection N} (S : Finset (Place ℂ F))
    (θ : R → Ω[F⁄ℂ])
    (hθ : ∀ r v, -1 ≤ v.ordDifferential (θ r) ∧ (v ∉ S → 0 ≤ v.ordDifferential (θ r)))
    (hS : PolePos 𝒟 S) (hvert : Function.Injective 𝒟.vert)
    {V : 𝒟.ιC → Set ℂ} {Ψ : R → 𝒟.ιC → ℂ → ℂ} (hP : RegPrimData S θ V Ψ)
    {J : 𝒟.ιE → R → ℂ} (hJ : IsJumpH 𝒟 (hfun S θ Ψ) J) :
    ArcValues 𝒟 (Aq S θ Ψ) (Bq S θ Ψ) (Iq S θ) (fun e => QuotientAddGroup.mk' _ (J e))
      (fun C => nxt (N := (𝒟.cell C).R.N)) := by
  refine ⟨?_, fun _ => nxt_bijective, ?_, ?_, ?_, ?_, fun C => sv_injective 𝒟 C⟩
  ·
    rintro ⟨C, k⟩
    have hftc : hfun S θ Ψ C ((𝒟.cell C).R.φs k.succ) - hfun S θ Ψ C ((𝒟.cell C).R.φs k.castSucc) =
        fun r => arcInt 𝒟 (fun C s => (𝒟.cell C).bdryIntegrand (θ r) s) ⟨C, k⟩ := by
      funext r
      rw [Pi.sub_apply, ← arc_ftc_hfun S θ hθ hS hP r C k]
      rfl
    have key : ∀ r, arcInt 𝒟 (fun C s => (𝒟.cell C).bdryIntegrand (θ r) s) ⟨C, k⟩ =
        if (𝒟.side C k).2 then edgeInt 𝒟 (θ r) (𝒟.side C k).1
          else -edgeInt 𝒟 (θ r) (𝒟.side C k).1 := by
      intro r
      have harc : arcOf 𝒟 (𝒟.side C k) = ⟨C, k⟩ := arcOf_side 𝒟 ⟨C, k⟩
      split_ifs with hsgn
      · have hq : 𝒟.side C k = ((𝒟.side C k).1, true) := Prod.ext rfl hsgn
        rw [hq] at harc
        show _ = arcInt 𝒟 (fun C s => (𝒟.cell C).bdryIntegrand (θ r) s) (arcOf 𝒟 ((𝒟.side C k).1, true))
        rw [harc]
      · have hq : 𝒟.side C k = ((𝒟.side C k).1, false) := Prod.ext rfl (by simpa using hsgn)
        rw [hq] at harc
        rw [← 𝒟.negative_arc_integral (𝒟.side C k).1
          (fun s hs => regular_bdry S θ hθ hS r _ _ hs), harc]
        rfl
    simp only [Aq, Bq, Iq, ← map_sub, hftc]
    split_ifs with hsgn
    · congr 1
      funext r
      rw [key r, if_pos hsgn]
    · rw [← map_neg]
      congr 1
      funext r
      rw [key r, if_neg hsgn, Pi.neg_apply]
  · exact fun C k => DissectionPolygon.corner_arc 𝒟 hvert C k
  ·
    intro C k
    simp only [Aq, Bq]
    by_cases hk : k.val + 1 < (𝒟.cell C).R.N
    · rw [castSucc_nxt_of_lt k hk]
    · obtain ⟨h0, hl⟩ := castSucc_nxt_of_not_lt k hk
      rw [h0, hl, (𝒟.cell C).R.hφ0, (𝒟.cell C).R.hφN, QuotientAddGroup.mk'_eq_mk']
      refine ⟨(2 * π * I) • ρ 𝒟 S θ C, AddSubgroup.subset_closure ⟨C, rfl⟩, ?_⟩
      rw [← hfun_add_two_pi, zero_add]
  ·
    intro e
    obtain ⟨ψ, -, ha, -, -, hJe⟩ := hJ e
    have := hJe _ (left_mem_Icc.2 ((𝒟.cell (arcOf 𝒟 (e, false)).1).R.hmono Fin.castSucc_lt_succ).le)
    rw [ha] at this
    simp only [Aq, Bq, ← map_sub, this]
  ·
    intro e
    obtain ⟨ψ, -, -, hb, -, hJe⟩ := hJ e
    have := hJe _ (right_mem_Icc.2 ((𝒟.cell (arcOf 𝒟 (e, false)).1).R.hmono Fin.castSucc_lt_succ).le)
    rw [hb] at this
    simp only [Aq, Bq, ← map_sub, this]

end
end Dubon2026.SourceFunctionField.CellGeometry.MeromorphicPeriods
