import GafniTao.FordBoundaryCollision

/-!
# Ford Lemma 3.2: covering the whole boundary

The shifted boundary is injected into the disjoint sum of the `s` possible
left boundary coordinates and the `s` possible right boundary coordinates.
The collision itself is retained in the target, so the choice of the first
bad coordinate cannot collapse two source collisions.
-/

open Finset
open scoped BigOperators

namespace GafniTao

noncomputable section

abbrev FordS4ResidueRightBoundaryAt
    {k d T P p : ℕ} [NeZero p]
    (Ψ : FordIntegerPolynomialSystem k d T) (hdk : d ≤ k)
    (s Q q : ℕ) (c : ZMod p) (i : Fin s) :=
  {u : FordCharacterCollision
      (fordS4PolynomialMoment (P := P) (p := p) Ψ hdk)
      (fordS4ResidueMoment (k := k) q c :
        FordS4ResidueTuple s Q p c → Fin k → ℤ) //
    fordResidueIsBoundary c (u.1.2.2 i)}

def fordRightBoundarySwapEquiv
    {k d T P p s Q q : ℕ} [NeZero p]
    (Ψ : FordIntegerPolynomialSystem k d T) (hdk : d ≤ k)
    (c : ZMod p) (i : Fin s) :
    FordS4ResidueRightBoundaryAt (P := P) Ψ hdk s Q q c i ≃
      FordS4ResidueLeftBoundaryAt (P := P) Ψ hdk s Q q c i where
  toFun u := ⟨⟨(u.1.1.2, u.1.1.1), u.1.2.symm⟩, u.2⟩
  invFun u := ⟨⟨(u.1.1.2, u.1.1.1), u.1.2.symm⟩, u.2⟩
  left_inv u := by rfl
  right_inv u := by rfl

theorem ford_right_boundary_card_le_odd_integral
    {k d T P p s Q q : ℕ} [NeZero p]
    (Ψ : FordIntegerPolynomialSystem k d T) (hdk : d ≤ k)
    (c : ZMod p) (i : Fin s) (hs : 1 ≤ s) :
    (Nat.card (FordS4ResidueRightBoundaryAt (P := P)
        Ψ hdk s Q q c i) : ℝ) ≤
      fordS4OddIntegral (P := P) Ψ hdk s Q q c := by
  rw [Nat.card_congr (fordRightBoundarySwapEquiv (P := P) Ψ hdk c i)]
  exact ford_left_boundary_card_le_odd_integral Ψ hdk c i hs

theorem fordResidueIsBoundary_shiftIndexToResidue
    {Q p : ℕ} [NeZero p] (c : ZMod p)
    (u : FordShiftedResidueIndex Q p c) :
    fordResidueIsBoundary c (fordShiftIndexToResidueInterval c u) ↔
      ¬ u.1 < Q / p := by
  unfold fordResidueIsBoundary
  have heq : (fordResidueIntervalToShiftIndex c
      (fordShiftIndexToResidueInterval c u)).1 = u.1 :=
    congrArg (fun v : FordShiftedResidueIndex Q p c ↦ v.1)
      ((fordResidueShiftEquiv c).apply_symm_apply u)
  rw [heq]

def fordShiftedBoundaryCoverMap
    {k d T P p s Q q : ℕ} [NeZero p]
    (Ψ : FordIntegerPolynomialSystem k d T) (hdk : d ≤ k)
    (c : ZMod p) :
    FordS4ShiftedBoundary (P := P) Ψ hdk s Q q c →
      (Sigma fun i : Fin s ↦
          FordS4ResidueLeftBoundaryAt (P := P) Ψ hdk s Q q c i) ⊕
        (Sigma fun i : Fin s ↦
          FordS4ResidueRightBoundaryAt (P := P) Ψ hdk s Q q c i) := by
  intro u
  let r := fordS4ShiftedCollisionToResidue Ψ hdk c u.1
  by_cases hl : ∀ i : Fin s, (u.1.1.1.2 i).1 < Q / p
  · have hr : ¬ ∀ i : Fin s, (u.1.1.2.2 i).1 < Q / p := by
      intro hall
      exact u.2 ⟨hl, hall⟩
    let i := Classical.choose (not_forall.mp hr)
    have hi := Classical.choose_spec (not_forall.mp hr)
    exact Sum.inr ⟨i, ⟨r, (fordResidueIsBoundary_shiftIndexToResidue c _).2 hi⟩⟩
  · let i := Classical.choose (not_forall.mp hl)
    have hi := Classical.choose_spec (not_forall.mp hl)
    exact Sum.inl ⟨i, ⟨r, (fordResidueIsBoundary_shiftIndexToResidue c _).2 hi⟩⟩

def fordBoundaryCoverUnderlying
    {k d T P p s Q q : ℕ} [NeZero p]
    (Ψ : FordIntegerPolynomialSystem k d T) (hdk : d ≤ k)
    (c : ZMod p) :
    ((Sigma fun i : Fin s ↦
          FordS4ResidueLeftBoundaryAt (P := P) Ψ hdk s Q q c i) ⊕
        (Sigma fun i : Fin s ↦
          FordS4ResidueRightBoundaryAt (P := P) Ψ hdk s Q q c i)) →
      FordCharacterCollision
        (fordS4PolynomialMoment (P := P) (p := p) Ψ hdk)
        (fordS4ResidueMoment (k := k) q c :
          FordS4ResidueTuple s Q p c → Fin k → ℤ)
  | Sum.inl u => u.2.1
  | Sum.inr u => u.2.1

theorem fordBoundaryCoverUnderlying_map
    {k d T P p s Q q : ℕ} [NeZero p]
    (Ψ : FordIntegerPolynomialSystem k d T) (hdk : d ≤ k)
    (c : ZMod p) (u : FordS4ShiftedBoundary (P := P) Ψ hdk s Q q c) :
    fordBoundaryCoverUnderlying Ψ hdk c
        (fordShiftedBoundaryCoverMap Ψ hdk c u) =
      fordS4ShiftedCollisionToResidue Ψ hdk c u.1 := by
  classical
  by_cases hl : ∀ i : Fin s, (u.1.1.1.2 i).1 < Q / p
  · simp [fordShiftedBoundaryCoverMap, hl, fordBoundaryCoverUnderlying]
  · simp [fordShiftedBoundaryCoverMap, hl, fordBoundaryCoverUnderlying]

theorem fordShiftedBoundaryCoverMap_injective
    {k d T P p s Q q : ℕ} [NeZero p]
    (Ψ : FordIntegerPolynomialSystem k d T) (hdk : d ≤ k)
    (c : ZMod p) :
    Function.Injective (fordShiftedBoundaryCoverMap (P := P) (s := s)
      (Q := Q) (q := q) Ψ hdk c) := by
  intro u v huv
  have hr : fordS4ShiftedCollisionToResidue Ψ hdk c u.1 =
      fordS4ShiftedCollisionToResidue Ψ hdk c v.1 := by
    rw [← fordBoundaryCoverUnderlying_map Ψ hdk c u,
      ← fordBoundaryCoverUnderlying_map Ψ hdk c v, huv]
  have huv' : u.1 = v.1 :=
    (fordS4CollisionShiftEquiv Ψ hdk c).symm.injective hr
  exact Subtype.ext huv'

theorem ford_shifted_boundary_card_le_coordinate_sum
    {k d T P p s Q q : ℕ} [NeZero p]
    (Ψ : FordIntegerPolynomialSystem k d T) (hdk : d ≤ k)
    (c : ZMod p) :
    Nat.card (FordS4ShiftedBoundary (P := P) Ψ hdk s Q q c) ≤
      (∑ i : Fin s, Nat.card
          (FordS4ResidueLeftBoundaryAt (P := P) Ψ hdk s Q q c i)) +
        ∑ i : Fin s, Nat.card
          (FordS4ResidueRightBoundaryAt (P := P) Ψ hdk s Q q c i) := by
  let Target :=
    (Sigma fun i : Fin s ↦
        FordS4ResidueLeftBoundaryAt (P := P) Ψ hdk s Q q c i) ⊕
      (Sigma fun i : Fin s ↦
        FordS4ResidueRightBoundaryAt (P := P) Ψ hdk s Q q c i)
  have hcard : Nat.card (FordS4ShiftedBoundary (P := P) Ψ hdk s Q q c) ≤
      Nat.card Target := Nat.card_le_card_of_injective
        (fordShiftedBoundaryCoverMap Ψ hdk c)
        (fordShiftedBoundaryCoverMap_injective Ψ hdk c)
  simpa [Target, Nat.card_sum, Nat.card_sigma] using hcard

theorem ford_shifted_boundary_card_le_two_s_odd
    {k d T P p s Q q : ℕ} [NeZero p]
    (Ψ : FordIntegerPolynomialSystem k d T) (hdk : d ≤ k)
    (c : ZMod p) (hs : 1 ≤ s) :
    (Nat.card (FordS4ShiftedBoundary (P := P) Ψ hdk s Q q c) : ℝ) ≤
      (2 : ℝ) * s * fordS4OddIntegral (P := P) Ψ hdk s Q q c := by
  have hcover := ford_shifted_boundary_card_le_coordinate_sum
    (P := P) (s := s) (Q := Q) (q := q) Ψ hdk c
  calc
    (Nat.card (FordS4ShiftedBoundary (P := P) Ψ hdk s Q q c) : ℝ) ≤
        ((∑ i : Fin s, Nat.card
            (FordS4ResidueLeftBoundaryAt (P := P) Ψ hdk s Q q c i)) +
          ∑ i : Fin s, Nat.card
            (FordS4ResidueRightBoundaryAt (P := P) Ψ hdk s Q q c i) : ℕ) := by
      exact_mod_cast hcover
    _ = (∑ i : Fin s,
          (Nat.card (FordS4ResidueLeftBoundaryAt (P := P)
            Ψ hdk s Q q c i) : ℝ)) +
        ∑ i : Fin s,
          (Nat.card (FordS4ResidueRightBoundaryAt (P := P)
            Ψ hdk s Q q c i) : ℝ) := by push_cast; rfl
    _ ≤ (∑ _i : Fin s, fordS4OddIntegral (P := P) Ψ hdk s Q q c) +
        ∑ _i : Fin s, fordS4OddIntegral (P := P) Ψ hdk s Q q c := by
      apply add_le_add <;> apply Finset.sum_le_sum <;> intro i hi
      · exact ford_left_boundary_card_le_odd_integral Ψ hdk c i hs
      · exact ford_right_boundary_card_le_odd_integral Ψ hdk c i hs
    _ = (2 : ℝ) * s * fordS4OddIntegral (P := P) Ψ hdk s Q q c := by
      simp
      ring

#print axioms ford_shifted_boundary_card_le_two_s_odd

end

end GafniTao
