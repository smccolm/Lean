import Dubon2026.ContinuousRepresentationCohomology
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-! # The actual finite group order annihilates original continuous H2 -/

namespace Dubon2026
noncomputable section

variable {R G : Type} [CommRing R] [Group G] [Fintype G] (A : Rep R G)

/-- The undivided cocycle sum has boundary exactly the actual group order
times the original two-cocycle. Unlike field averaging, this uses no inverse
of the group order and applies to the original integer unit coefficients. -/
theorem finiteTwoCocycle_sum_boundary (c : groupCohomology.cocycles₂ A) :
    groupCohomology.d₁₂ A (fun g => ∑ t, c (g, t)) =
      fun z => Fintype.card G • c z := by
  funext z
  rcases z with ⟨g, h⟩
  have hperm : (∑ t, c (g, h * t)) = ∑ t, c (g, t) :=
    Fintype.sum_equiv (Equiv.mulLeft h) _ _ (fun _ => rfl)
  have hs : (∑ t, c (g * h, t)) + Fintype.card G • c (g, h) =
      A.ρ g (∑ t, c (h, t)) + ∑ t, c (g, t) := by
    calc
      (∑ t, c (g * h, t)) + Fintype.card G • c (g, h) =
          ∑ t, (c (g * h, t) + c (g, h)) := by
            simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ]
      _ = ∑ t, (A.ρ g (c (h, t)) + c (g, h * t)) := by
        apply Finset.sum_congr rfl
        intro t _
        exact (groupCohomology.mem_cocycles₂_iff _).mp c.property g h t
      _ = A.ρ g (∑ t, c (h, t)) + ∑ t, c (g, t) := by
        rw [Finset.sum_add_distrib, ← map_sum, hperm]
  change A.ρ g (∑ t, c (h, t)) - (∑ t, c (g * h, t)) +
    (∑ t, c (g, t)) = Fintype.card G • c (g, h)
  apply add_left_cancel (a := ∑ t, c (g * h, t))
  calc
    (∑ t, c (g * h, t)) +
        (A.ρ g (∑ t, c (h, t)) - (∑ t, c (g * h, t)) + ∑ t, c (g, t)) =
          A.ρ g (∑ t, c (h, t)) + ∑ t, c (g, t) := by abel
    _ = (∑ t, c (g * h, t)) + Fintype.card G • c (g, h) := hs.symm

variable [TopologicalSpace R] [TopologicalSpace G] [IsTopologicalGroup G]
  [TopologicalSpace A] [IsTopologicalAddGroup A] [ContinuousSMul R A]
  (hA : Continuous (fun z : G × A => A.ρ z.1 z.2))

omit [IsTopologicalGroup G] in
/-- The actual undivided finite sum is continuous in the original coefficient
topology, by joint continuity of the original two-cocycle. -/
theorem continuousTwoCocycle_sum_continuous (c : continuousRepresentationCocyclesTwo A) :
    Continuous (fun g => ∑ t, c.val (g, t)) := by
  apply continuous_finsetSum
  intro t _
  exact c.property.comp (continuous_id.prodMk continuous_const)

/-- The actual finite group order kills every original continuous H2 class.
The explicit undivided sum is its genuine continuous coboundary witness. -/
theorem continuousFiniteH2_card_nsmul_eq_zero
    (x : ContinuousRepresentationH2 A hA) : Fintype.card G • x = 0 := by
  induction x using Submodule.Quotient.induction_on with
  | _ c =>
    change (Submodule.Quotient.mk (Fintype.card G • c) :
      ContinuousRepresentationH2 A hA) = 0
    apply (Submodule.Quotient.mk_eq_zero _).mpr
    let b : C(G, A) := ⟨fun g => ∑ t, c.val (g, t), continuousTwoCocycle_sum_continuous A c⟩
    refine ⟨b, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    exact finiteTwoCocycle_sum_boundary A c.val

end
end Dubon2026
