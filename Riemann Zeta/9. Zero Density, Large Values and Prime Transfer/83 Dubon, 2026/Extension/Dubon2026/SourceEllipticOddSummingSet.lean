import Dubon2026.SourceEllipticVeluTwoKernel

/-! The actual finite coordinate set of the first half of an odd cyclic
subgroup. This is the input to the odd-degree Velu discriminant identity and
quotient map, then prime modular-polynomial products and the cyclic-subgroup
inertia census required by DUB-17 / DUB-18. Adapted from
Def_WeierstrassCurve_OddOrderSummingSet and Def_WeierstrassCurve_VeluQuotientMap,
anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2. -/
namespace Dubon2026.SourceEllipticVelu
open WeierstrassCurve
noncomputable section

/-- Affine coordinates of a finite point, with a fixed value at infinity. -/
def coordsOrZero {R : Type*} [CommRing R] {W : WeierstrassCurve.Affine R} : W.Point → R × R
  | .zero => (0, 0)
  | .some x y _ => (x, y)

/-- Coordinates of the first n nonzero multiples of an odd-order generator. -/
def oddOrderSummingSet {F : Type*} [Field F] [DecidableEq F]
    (W : WeierstrassCurve F) (Q : W.toAffine.Point) (n : ℕ) : Finset (F × F) :=
  (Finset.Icc 1 n).image fun k => coordsOrZero (k • Q)

/-- Explicit equation, non-two-torsion and distinct-x conditions for a Velu sum. -/
structure IsOddVeluSet {F : Type*} [Field F] (W : WeierstrassCurve F)
    (S : Finset (F × F)) : Prop where
  /-- Each coordinate pair satisfies the original curve equation. -/
  equation : ∀ P ∈ S, W.toAffine.Equation P.1 P.2
  /-- No summand is a point of order two. -/
  gy_ne_zero : ∀ P ∈ S, veluGy W P.1 P.2 ≠ 0
  /-- The finite coordinate set contains at most one pair at each x value. -/
  x_injOn : ∀ P ∈ S, ∀ P' ∈ S, P.1 = P'.1 → P = P'

theorem mem_oddOrderSummingSet {F : Type*} [Field F] [DecidableEq F]
    {W : WeierstrassCurve F} {Q : W.toAffine.Point} {n : ℕ} {P : F × F} :
    P ∈ oddOrderSummingSet W Q n ↔
      ∃ k, 1 ≤ k ∧ k ≤ n ∧ coordsOrZero (k • Q) = P := by
  simp only [oddOrderSummingSet, Finset.mem_image, Finset.mem_Icc]
  exact ⟨fun ⟨k, ⟨h₁, h₂⟩, h₃⟩ => ⟨k, h₁, h₂, h₃⟩,
    fun ⟨k, h₁, h₂, h₃⟩ => ⟨k, ⟨h₁, h₂⟩, h₃⟩⟩

end
end Dubon2026.SourceEllipticVelu
