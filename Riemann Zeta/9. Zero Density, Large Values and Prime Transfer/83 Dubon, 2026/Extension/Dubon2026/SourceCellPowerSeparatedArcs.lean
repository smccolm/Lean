import Dubon2026.SourceCellPowerArcInjectivity
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Topology.Separation.Regular

/-! DUB-17/18 -> original Abel-Jacobi -> actual branch and pole cells.
The source power pullback retains the exact radial preimage, multiplicity,
arc laps and separated inverse branches needed for geometric pairing.
Adapted from anthropics/fermats-last-theorem, Apache-2.0,
commit 6e837e75355538c7f80bab5b956861e86c4eacc2.
Existing radial periodicity and periodic argument evaluation are reused.
-/
namespace Dubon2026.SourceFunctionField.CellGeometry.PowPullback
noncomputable section
open scoped Real

theorem isCompact_arcSet (S : RadialRegion) (i : Fin S.N) : IsCompact (S.arcSet i) := by
  unfold RadialRegion.arcSet RadialRegion.arcIcc
  exact isCompact_Icc.image (S.continuous_loop)

theorem exists_separating_opens (R : RadialRegion) (hN : 2 ≤ R.N) (e : ℕ) (he : e ≠ 0)
    (k : Fin R.N) :
    ∃ U : Fin e → Set ℂ, (∀ j, IsOpen (U j)) ∧
      Pairwise (fun j j' => Disjoint (U j) (U j')) ∧
        ∀ j, (efold R e he).arcSet (lapIdx R e he j k) ⊆ U j := by
  obtain ⟨A, hA⟩ : ∃ A : Fin e → Set ℂ, ∀ j, A j = (efold R e he).arcSet (lapIdx R e he j k) :=
    ⟨fun j => (efold R e he).arcSet (lapIdx R e he j k), fun j => rfl⟩
  have hc : ∀ i, IsCompact (A i) := by
    intro i
    rw [hA i]
    exact isCompact_arcSet (efold R e he) (lapIdx R e he i k)
  have hsep : ∀ j j' : Fin e, ∃ δ : ℝ, 0 < δ ∧
      (j ≠ j' → Disjoint (Metric.thickening δ (A j)) (Metric.thickening δ (A j'))) := by
    intro j j'
    by_cases hjj' : j = j'
    · exact ⟨1, one_pos, fun h => absurd hjj' h⟩
    · have hd : Disjoint (A j) (A j') := by
        rw [hA j, hA j']
        exact arcSet_lap_disjoint R hN e he k hjj'
      obtain ⟨δ, hδ, hdisj⟩ := hd.exists_thickenings (hc j) (hc j').isClosed
      exact ⟨δ, hδ, fun _ => hdisj⟩
  choose δ hδpos hδ using hsep
  refine ⟨fun j => ⋂ i : Fin e, Metric.thickening (min (δ j i) (δ i j)) (A j), ?_, ?_, ?_⟩
  · intro j
    exact isOpen_iInter_of_finite fun i => Metric.isOpen_thickening
  · intro j j' hjj'
    have h1 : (⋂ i : Fin e, Metric.thickening (min (δ j i) (δ i j)) (A j))
        ⊆ Metric.thickening (δ j j') (A j) :=
      (Set.iInter_subset (fun i : Fin e => Metric.thickening (min (δ j i) (δ i j)) (A j)) j').trans
        (Metric.thickening_mono (min_le_left (δ j j') (δ j' j)) (A j))
    have h2 : (⋂ i : Fin e, Metric.thickening (min (δ j' i) (δ i j')) (A j'))
        ⊆ Metric.thickening (δ j j') (A j') :=
      (Set.iInter_subset (fun i : Fin e => Metric.thickening (min (δ j' i) (δ i j')) (A j')) j).trans
        (Metric.thickening_mono (min_le_right (δ j' j) (δ j j')) (A j'))
    exact Disjoint.mono h1 h2 (hδ j j' hjj')
  · intro j
    rw [← hA j]
    exact Set.subset_iInter fun i =>
      Metric.self_subset_thickening (lt_min (hδpos j i) (hδpos i j)) (A j)

theorem exists_pow_pullback_laps (R : RadialRegion) (hN : 2 ≤ R.N) (e : ℕ) (he : e ≠ 0) :
    ∃ R' : RadialRegion,
      R'.q = 0 ∧ R'.N = e * R.N ∧
      (∀ u : ℂ, u ∈ R'.K ↔ R.q + u ^ e ∈ R.K) ∧
      (∀ u : ℂ, u ∈ R'.Kint ↔ R.q + u ^ e ∈ R.Kint) ∧
      (∀ ψ : ℝ, R.q + R'.loop ψ ^ e = R.loop ((e : ℝ) * ψ)) ∧
      ∃ lap : Fin e → Fin R.N → Fin R'.N,
        Function.Bijective (fun jk : Fin e × Fin R.N => lap jk.1 jk.2) ∧
        (∀ (j : Fin e) (k : Fin R.N),
          R'.arcIcc (lap j k) = (fun t : ℝ => (2 * π * ((j : ℕ) : ℝ) + t) / (e : ℝ)) '' R.arcIcc k) ∧
        (∀ (j : Fin e) (k : Fin R.N),
          (fun u : ℂ => R.q + u ^ e) '' R'.arcSet (lap j k) = R.arcSet k) ∧
        (∀ (j : Fin e) (k : Fin R.N), Set.InjOn (fun u : ℂ => R.q + u ^ e) (R'.arcSet (lap j k))) ∧
        (∀ k : Fin R.N, ∃ U : Fin e → Set ℂ, (∀ j, IsOpen (U j)) ∧
          Pairwise (fun j j' => Disjoint (U j) (U j')) ∧ ∀ j, R'.arcSet (lap j k) ⊆ U j) :=
  ⟨efold R e he, efold_q R e he, efold_N R e he, mem_K_iff R e he, mem_Kint_iff R e he,
    loop_pow R e he, lapIdx R e he, ⟨lapIdx_injective R e he, lapIdx_surjective R e he⟩,
    arcIcc_lapIdx R e he, image_pow_arcSet R e he, injOn_pow_arcSet R hN e he,
    exists_separating_opens R hN e he⟩


end
end Dubon2026.SourceFunctionField.CellGeometry.PowPullback
