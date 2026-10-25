import Dubon2026.SourceRadialReversedArcImages
import Dubon2026.SourceOriginalCellPairingLiftIndices

/-! DUB-17/18 -> cover dissection -> common-point adjacency.
Full positive-edge reversal gives equality of paired lifted arc images.
Involutivity supplies the negative orientation without an additional choice. -/
namespace Dubon2026.SourceFunctionField.CellGeometry.CellPairing
open Set
variable {N : ℕ} [NeZero N] {ι : Type} {cell : ι → Cell N}
variable (P : CellPairing cell) (J : ι → Type)

theorem liftedPair_arc_images {X : Type*} (f : (i : ι) → J i → ℂ → X)
    (T : (e : P.Edge) → J e.1.1 ≃ J (P.pair e.1).1)
    (hpos : ∀ (e : P.Edge) j,
      f (P.pair e.1).1 (T e j) '' (cell (P.pair e.1).1).R.arcSet (P.pair e.1).2 =
        f e.1.1 j '' (cell e.1.1).R.arcSet e.1.2)
    (a : Σ a : (Σ c : ι, Fin (cell c).R.N), J a.1) :
    f (P.liftedPair J T a).1.1 (P.liftedPair J T a).2 ''
        (cell (P.liftedPair J T a).1.1).R.arcSet (P.liftedPair J T a).1.2 =
      f a.1.1 a.2 '' (cell a.1.1).R.arcSet a.1.2 := by
  have hp (b : Σ a : (Σ c : ι, Fin (cell c).R.N), J a.1) (hb : P.orient b.1 = true) :
      f (P.liftedPair J T b).1.1 (P.liftedPair J T b).2 ''
          (cell (P.liftedPair J T b).1.1).R.arcSet (P.liftedPair J T b).1.2 =
        f b.1.1 b.2 '' (cell b.1.1).R.arcSet b.1.2 := by
    obtain ⟨b, j⟩ := b
    rw [P.liftedPair_positive J T b hb j]
    exact hpos ⟨b, hb⟩ j
  by_cases ha : P.orient a.1 = true
  · exact hp a ha
  · have hb : P.orient (P.liftedPair J T a).1 = true := by
      rw [P.liftedPair_base]; exact P.orient_pair_of_not ha
    have h := hp (P.liftedPair J T a) hb
    rw [P.liftedPair_involutive J T a] at h
    exact h.symm

theorem liftedPair_arc_images_of_reversal {X : Type*} (f : (i : ι) → J i → ℂ → X)
    (T : (e : P.Edge) → J e.1.1 ≃ J (P.pair e.1).1)
    (hrev : ∀ e : P.Edge, ∃ ψ : ℝ → ℝ,
      StrictAntiOn ψ ((cell (P.pair e.1).1).R.arcIcc (P.pair e.1).2) ∧
      ContDiffOn ℝ 1 ψ ((cell (P.pair e.1).1).R.arcIcc (P.pair e.1).2) ∧
      ψ ((cell (P.pair e.1).1).R.φs (P.pair e.1).2.castSucc) = (cell e.1.1).R.φs e.1.2.succ ∧
      ψ ((cell (P.pair e.1).1).R.φs (P.pair e.1).2.succ) = (cell e.1.1).R.φs e.1.2.castSucc ∧
      ∀ j t, t ∈ (cell (P.pair e.1).1).R.arcIcc (P.pair e.1).2 →
        f (P.pair e.1).1 (T e j) ((cell (P.pair e.1).1).R.loop t) =
          f e.1.1 j ((cell e.1.1).R.loop (ψ t)))
    (a : Σ a : (Σ c : ι, Fin (cell c).R.N), J a.1) :
    f (P.liftedPair J T a).1.1 (P.liftedPair J T a).2 ''
        (cell (P.liftedPair J T a).1.1).R.arcSet (P.liftedPair J T a).1.2 =
      f a.1.1 a.2 '' (cell a.1.1).R.arcSet a.1.2 := by
  apply P.liftedPair_arc_images J f T _ a
  intro e j
  obtain ⟨ψ, ha, hc, hl, hr, he⟩ := hrev e
  exact RadialRegion.reversed_arc_images _ _ _ _ _ _ ψ ha hc.continuousOn hl hr (he j)

end Dubon2026.SourceFunctionField.CellGeometry.CellPairing
