import Dubon2026.SourceCoverLiftedCellIncidence
import Dubon2026.SourceOriginalLiftedPairArcImages
import Dubon2026.SourceOriginalGlobalCellPairing
import Dubon2026.SourceOriginalCellIntersectionChains

/-! DUB-17/18 -> cover reciprocity -> actual lifted intersection chains.
Lift the existing base intersection chain through a fixed cover point.
Equality of whole paired lifted arcs preserves that point at every step;
disjoint sheets identify the final lifted cell. No new planar decomposition
or independent connectivity premise is needed. -/
namespace Dubon2026.SourceFunctionField.CellGeometry.OriginalGlobalCellCover
noncomputable section
open SourceCurve Set
attribute [local instance] OriginalChart.placeTopology
variable {N : ℕ} [NeZero N] {Marked : Finset ℂ} (A : OriginalGlobalCellCover N Marked)

/-- Adjacency through the specified point on a genuinely paired lifted arc. -/
def LiftedPointStep {X : Type*} (J : A.Index → Type) (f : (i : A.Index) → J i → ℂ → X)
    (T : (e : A.pairing.Edge) → J e.1.1 ≃ J (A.pairing.pair e.1).1) (w : X)
    (i j : Σ c : A.Index, J c) : Prop :=
  ∃ (k : Fin (A.cell i.1).R.N) (l : Fin (A.cell j.1).R.N),
    A.pairing.liftedPair J T ⟨⟨i.1, k⟩, i.2⟩ = ⟨⟨j.1, l⟩, j.2⟩ ∧
      w ∈ f i.1 i.2 '' (A.cell i.1).R.arcSet k

theorem lifted_intersection_chain {X : Type*} [TopologicalSpace X]
    (p : X → Place ℂ (modularFunctionFieldOver N ℂ)) (J : A.Index → Type)
    (ζ : (i : A.Index) → J i → OpenPartialHomeomorph X ℂ)
    (hK : ∀ i j, (A.cell i).R.K ⊆ (ζ i j).target)
    (hp : ∀ i j z, z ∈ (A.cell i).R.K → p ((ζ i j).symm z) = (A.cell i).ζ.symm z)
    (hd : ∀ i, Pairwise fun j k => Disjoint (ζ i j).source (ζ i k).source)
    (T : (e : A.pairing.Edge) → J e.1.1 ≃ J (A.pairing.pair e.1).1)
    (harcs : ∀ a : Σ a : (Σ c : A.Index, Fin (A.cell c).R.N), J a.1,
      (ζ (A.pairing.liftedPair J T a).1.1 (A.pairing.liftedPair J T a).2).symm ''
          (A.cell (A.pairing.liftedPair J T a).1.1).R.arcSet (A.pairing.liftedPair J T a).1.2 =
        (ζ a.1.1 a.2).symm '' (A.cell a.1.1).R.arcSet a.1.2)
    (i j : Σ c : A.Index, J c) (w : X)
    (hi : w ∈ (ζ i.1 i.2).symm '' (A.cell i.1).R.K)
    (hj : w ∈ (ζ j.1 j.2).symm '' (A.cell j.1).R.K) :
    Relation.ReflTransGen (A.LiftedPointStep J (fun c s => (ζ c s).symm) T w) i j := by
  have hbase := A.intersection_chain i.1 j.1
    (SheetCover.lifted_carrier_projects p _ _ _ (hp i.1 i.2) hi)
    (SheetCover.lifted_carrier_projects p _ _ _ (hp j.1 j.2) hj)
  have key : ∀ b, Relation.ReflTransGen (A.PairStep (p w)) i.1 b →
      ∃ q : Σ c : A.Index, J c, q.1 = b ∧
        w ∈ (ζ q.1 q.2).symm '' (A.cell q.1).R.K ∧
        Relation.ReflTransGen (A.LiftedPointStep J (fun c s => (ζ c s).symm) T w) i q := by
    intro b hchain
    induction hchain with
    | refl => exact ⟨i, rfl, hi, .refl⟩
    | tail _ hstep ih =>
      obtain ⟨⟨c, s⟩, hq, hqw, hiq⟩ := ih
      dsimp only at hq hqw hiq
      subst hq
      obtain ⟨k, l, hpair, hwa⟩ := hstep
      have hw : w ∈ (ζ c s).symm '' (A.cell c).R.arcSet k :=
        (SheetCover.lifted_arc_iff_over_arc p _ _ _ (A.cell c).hKt (hp c s) hqw k).mpr hwa
      let a : Σ a : (Σ c : A.Index, Fin (A.cell c).R.N), J a.1 := ⟨⟨c, k⟩, s⟩
      let b := A.pairing.liftedPair J T a
      have hwb : w ∈ (ζ b.1.1 b.2).symm '' (A.cell b.1.1).R.arcSet b.1.2 := by
        rw [harcs a]; exact hw
      refine ⟨⟨b.1.1, b.2⟩, ?_, ?_, hiq.tail ?_⟩
      · exact congrArg Sigma.fst ((A.pairing.liftedPair_base J T a).trans hpair)
      · exact Set.image_mono ((A.cell b.1.1).R.arcSet_subset_K b.1.2) hwb
      · exact ⟨k, b.1.2, rfl, hw⟩
  obtain ⟨⟨c, s⟩, hq, hqw, hiq⟩ := key _ hbase
  obtain ⟨d, t⟩ := j
  dsimp only at hq hj
  subst d
  have hst : s = t := SheetCover.lifted_carrier_unique (ζ c) _ (hK c) (hd c) hqw hj
  subst t
  exact hiq

end
end Dubon2026.SourceFunctionField.CellGeometry.OriginalGlobalCellCover
