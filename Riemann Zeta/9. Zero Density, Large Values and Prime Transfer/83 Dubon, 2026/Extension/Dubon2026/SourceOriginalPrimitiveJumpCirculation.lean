import Dubon2026.SourceOriginalConstructedNormalizedPrimitives
import Dubon2026.SourceOriginalPairedBoundarySum

/-! DUB-17/18 -> original Abel-Jacobi -> periods and raw reciprocity.
Actual primitive jumps satisfy the vertex circulation law. Endpoint values
cancel around each actual cell boundary and the opposite arc orientations
pair them into edge jumps. This is the necessary input to the already-proved
universal fundamental-cycle decomposition. Adapted from the verified
Apache-2.0 source anthropics/fermats-last-theorem, commit
6e837e75355538c7f80bab5b956861e86c4eacc2.
-/
namespace Dubon2026.SourceFunctionField.CellGeometry.DissectionPeriods
noncomputable section
open SourceCurve Set Real CellDissection
attribute [local instance] OriginalChart.placeTopology OriginalChart.placeChartedSpace
variable {N : ℕ} [NeZero N]

theorem jump_kirchhoff (𝒟 : CellDissection N) (hvert : Function.Injective 𝒟.vert)
    (Ψ : 𝒟.ιC → ℂ → ℂ) (J : 𝒟.ιE → ℂ)
    (hJ : ∀ e : 𝒟.ιE, ∀ s ∈ Icc ((𝒟.cell (arcOf 𝒟 (e, true)).1).R.φs (arcOf 𝒟 (e, true)).2.castSucc)
        ((𝒟.cell (arcOf 𝒟 (e, true)).1).R.φs (arcOf 𝒟 (e, true)).2.succ),
      Ψ (arcOf 𝒟 (e, true)).1 ((𝒟.cell (arcOf 𝒟 (e, true)).1).R.loop s) -
        Ψ (arcOf 𝒟 (e, false)).1
          ((𝒟.cell (arcOf 𝒟 (e, false)).1).ζ ((𝒟.cell (arcOf 𝒟 (e, true)).1).bdry s)) = J e)
    (v : 𝒟.ιV) :
    (∑ e with (𝒟.ends e).2 = v, J e) = ∑ e with (𝒟.ends e).1 = v, J e := by
  classical

  set Vs : (Σ D : 𝒟.ιC, Fin (𝒟.cell D).R.N) → ℂ :=
    fun p => Ψ p.1 ((𝒟.cell p.1).R.loop ((𝒟.cell p.1).R.φs p.2.castSucc)) with hVs
  set Ve : (Σ D : 𝒟.ιC, Fin (𝒟.cell D).R.N) → ℂ :=
    fun p => Ψ p.1 ((𝒟.cell p.1).R.loop ((𝒟.cell p.1).R.φs p.2.succ)) with hVe
  set startV : 𝒟.ιE × Bool → 𝒟.ιV :=
    fun q => if q.2 then (𝒟.ends q.1).1 else (𝒟.ends q.1).2 with hstartV
  set endV : 𝒟.ιE × Bool → 𝒟.ιV :=
    fun q => if q.2 then (𝒟.ends q.1).2 else (𝒟.ends q.1).1 with hendV

  have hends : ∀ p : (Σ D : 𝒟.ιC, Fin (𝒟.cell D).R.N),
      (𝒟.cell p.1).bdry ((𝒟.cell p.1).R.φs p.2.castSucc) = 𝒟.vert (startV (𝒟.side p.1 p.2)) ∧
      (𝒟.cell p.1).bdry ((𝒟.cell p.1).R.φs p.2.succ) = 𝒟.vert (endV (𝒟.side p.1 p.2)) := by
    rintro ⟨D, k⟩
    exact 𝒟.arc_ends D k

  have hJe : ∀ e, J e = Ve (arcOf 𝒟 (e, true)) - Vs (arcOf 𝒟 (e, false)) := by
    intro e
    set p := arcOf 𝒟 (e, true) with hp
    set p' := arcOf 𝒟 (e, false) with hp'
    have h := hJ e _ (right_mem_Icc.2 ((𝒟.cell p.1).R.hmono Fin.castSucc_lt_succ).le)
    rw [← h]
    congr 1
    simp only [hVs]
    congr 1

    have h1 := (hends p).2
    have h2 := (hends p').1
    rw [hp, side_arcOf] at h1
    rw [hp', side_arcOf] at h2
    simp only [hendV, hstartV, if_true, if_false, Bool.false_eq_true] at h1 h2
    rw [← hp] at h1
    rw [← hp'] at h2
    rw [h1, ← h2]
    exact (Cell.bdry_coordinates _ _).2
  have hJs : ∀ e, J e = Vs (arcOf 𝒟 (e, true)) - Ve (arcOf 𝒟 (e, false)) := by
    intro e
    set p := arcOf 𝒟 (e, true) with hp
    set p' := arcOf 𝒟 (e, false) with hp'
    have h := hJ e _ (left_mem_Icc.2 ((𝒟.cell p.1).R.hmono Fin.castSucc_lt_succ).le)
    rw [← h]
    congr 1
    simp only [hVe]
    congr 1
    have h1 := (hends p).1
    have h2 := (hends p').2
    rw [hp, side_arcOf] at h1
    rw [hp', side_arcOf] at h2
    simp only [hendV, hstartV, if_true, if_false, Bool.false_eq_true] at h1 h2
    rw [← hp] at h1
    rw [← hp'] at h2
    rw [h1, ← h2]
    exact (Cell.bdry_coordinates _ _).2

  have hbij : Function.Bijective (arcOf 𝒟) :=
    Function.bijective_iff_has_inverse.2
      ⟨fun p => 𝒟.side p.1 p.2, fun q => side_arcOf 𝒟 q, fun p => arcOf_side 𝒟 p⟩
  set T : (Σ D : 𝒟.ιC, Fin (𝒟.cell D).R.N) → ℂ := fun p =>
    (if endV (𝒟.side p.1 p.2) = v then Ve p else 0) -
      (if startV (𝒟.side p.1 p.2) = v then Vs p else 0) with hT
  have hsumT : ∑ p : (Σ D : 𝒟.ιC, Fin (𝒟.cell D).R.N), T p = 0 := by
    rw [Fintype.sum_sigma]
    refine Finset.sum_eq_zero fun D _ => ?_

    set G : ℝ → ℂ := fun φ =>
      if (𝒟.cell D).bdry φ = 𝒟.vert v then Ψ D ((𝒟.cell D).R.loop φ) else 0 with hG
    have hTk : ∀ k : Fin (𝒟.cell D).R.N,
        T ⟨D, k⟩ = G ((𝒟.cell D).R.φs k.succ) - G ((𝒟.cell D).R.φs k.castSucc) := by
      intro k
      obtain ⟨h1, h2⟩ := hends ⟨D, k⟩
      dsimp only at h1 h2
      simp only [hT, hG, hVe, hVs]
      rw [h1, h2, hvert.eq_iff, hvert.eq_iff]
      split_ifs <;> rfl
    simp_rw [hTk]
    rw [Finset.sum_sub_distrib]
    have h2 := Fin.sum_univ_castSucc (fun i : Fin ((𝒟.cell D).R.N + 1) => G ((𝒟.cell D).R.φs i))
    have h3 := Fin.sum_univ_succ (fun i : Fin ((𝒟.cell D).R.N + 1) => G ((𝒟.cell D).R.φs i))
    have hlast : G ((𝒟.cell D).R.φs (Fin.last _)) = G ((𝒟.cell D).R.φs 0) := by
      rw [(𝒟.cell D).R.hφN, (𝒟.cell D).R.hφ0, show (2 * π : ℝ) = 0 + 2 * π by ring]
      simp only [hG, DissectionTrees.cell_bdry_periodic, (𝒟.cell D).R.loop_periodic 0]
    linear_combination h2 - h3 + hlast
  have hsumT' : ∑ q : 𝒟.ιE × Bool, T (arcOf 𝒟 q) = 0 := by
    rw [hbij.sum_comp T]; exact hsumT
  rw [Fintype.sum_prod_type] at hsumT'
  simp only [Fintype.sum_bool, hT, side_arcOf, hendV, hstartV, if_true, if_false,
    Bool.false_eq_true] at hsumT'

  rw [Finset.sum_filter, Finset.sum_filter]
  rw [← sub_eq_zero, ← Finset.sum_sub_distrib]
  refine Eq.trans ?_ hsumT'
  refine Finset.sum_congr rfl fun e _ => ?_
  have hE : Ve (arcOf 𝒟 (e, true)) - Vs (arcOf 𝒟 (e, false)) =
      Vs (arcOf 𝒟 (e, true)) - Ve (arcOf 𝒟 (e, false)) := by rw [← hJe, ← hJs]
  rw [hJe e]
  split_ifs <;> first | (linear_combination (-1 : ℂ) * hE) | ring1

end
end Dubon2026.SourceFunctionField.CellGeometry.DissectionPeriods
