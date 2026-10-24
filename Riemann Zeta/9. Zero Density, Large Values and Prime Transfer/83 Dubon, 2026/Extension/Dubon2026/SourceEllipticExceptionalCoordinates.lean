import Dubon2026.SourceEllipticStabilizerPointAction
import Dubon2026.SourceEllipticOddOrbitDistinctness

/-! DUB-17/18 -> reverse genus -> exceptional j-fiber census ->
the actual quartic and cubic elliptic automorphisms. Optional coordinates
distinguish the zero point; the existing nonzero abscissa theorem proves
the same-coordinate dichotomy, and the existing stabilizer equivalence
supplies the coordinate action. No new point-action construction is needed.
Adapted from anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2, the two exceptional fixed-vcInvFun
subgroup-count source solutions. -/
namespace Dubon2026.SourceEllipticExceptional
open WeierstrassCurve WeierstrassCurve.Affine SourceEllipticVariableChange
open SourceEllipticStabilizer
noncomputable section
variable {L : Type*} [Field L]

/-- Coordinates retaining the distinction between zero and affine points. -/
def xy {W : WeierstrassCurve L} : W.toAffine.Point → Option (L × L)
  | 0 => none
  | .some x y _ => some (x, y)

theorem xy_injective {W : WeierstrassCurve L} : Function.Injective (xy (W := W)) := by
  rintro (_ | ⟨x, y, h⟩) (_ | ⟨x', y', h'⟩) hh
  · rfl
  · exact absurd hh (by simp [xy])
  · exact absurd hh (by simp [xy])
  · simp only [xy, Option.some.injEq, Prod.mk.injEq] at hh
    obtain ⟨rfl, rfl⟩ := hh
    rfl

theorem xy_vcInvFun (γ : VariableChange L) {W : WeierstrassCurve L} (P : W.toAffine.Point) :
    xy (vcInvFun γ W.toAffine P) = (xy P).map (fun q => (vcXInv γ q.1, vcYInv γ q.1 q.2)) := by
  rcases P with _ | ⟨x, y, h⟩ <;> rfl

/-- Abscissa retaining the distinction between zero and affine points. -/
def xco {W : WeierstrassCurve L} : W.toAffine.Point → Option L
  | 0 => none
  | .some x _ _ => some x

@[scoped simp] theorem xco_zero {W : WeierstrassCurve L} : xco (0 : W.toAffine.Point) = none := rfl
@[scoped simp] theorem xco_some {W : WeierstrassCurve L} {x y : L} (h : W.toAffine.Nonsingular x y) :
    xco (Point.some x y h) = some x := rfl

theorem xco_neg {W : WeierstrassCurve L} (P : W.toAffine.Point) : xco (-P) = xco P := by
  rcases P with _ | ⟨x, y, h⟩
  · rfl
  · rw [Point.neg_some]; rfl

theorem eq_or_eq_neg_of_xco_eq {W : WeierstrassCurve L}
    {P Q : W.toAffine.Point} (h : xco P = xco Q) : P = Q ∨ P = -Q := by
  rcases P with _ | ⟨x, y, hP⟩ <;> rcases Q with _ | ⟨x', y', hQ⟩
  · exact Or.inl rfl
  · simp [xco] at h
  · simp [xco] at h
  · apply SourceEllipticVelu.OddDiscriminant.eq_or_eq_neg_of_xco_eq
      (Point.some_ne_zero hP) (Point.some_ne_zero hQ)
    exact Option.some.inj h

theorem xy_cast [DecidableEq L] {V W : WeierstrassCurve L} (h : V = W) (P : V.toAffine.Point) :
    xy (AddEquiv.cast (M := fun E : WeierstrassCurve L => E.toAffine.Point) h P) = xy P := by
  subst W
  rfl

theorem xy_stabilizerPointEquiv [DecidableEq L] (W : WeierstrassCurve L)
    (C : VariableChange L) (hC : C • W = W) (P : W.toAffine.Point) :
    xy (stabilizerPointEquiv W C hC P) =
      (xy P).map (fun q => (vcXInv C q.1, vcYInv C q.1 q.2)) := by
  change xy (AddEquiv.cast (M := fun E : WeierstrassCurve L => E.toAffine.Point)
    hC (vcInvFun C W.toAffine P)) = _
  rw [xy_cast, xy_vcInvFun]

theorem exists_eq_some_of_xy_eq {W : WeierstrassCurve L} {Q : W.toAffine.Point} {x y : L}
    (h : xy Q = some (x, y)) : ∃ h', Q = Point.some x y h' := by
  rcases Q with _ | ⟨x', y', h'⟩
  · exact absurd h (by simp [xy])
  · simp only [xy, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨h', rfl⟩

theorem xy_neg {W : WeierstrassCurve L} (P : W.toAffine.Point) :
    xy (-P) = (xy P).map (fun q => (q.1, W.toAffine.negY q.1 q.2)) := by
  rcases P with _ | ⟨x, y, h⟩
  · rfl
  · rw [Affine.Point.neg_some]; rfl

theorem xco_eq_map_xy {W : WeierstrassCurve L} (P : W.toAffine.Point) : xco P = (xy P).map Prod.fst := by
  rcases P with _ | ⟨x, y, h⟩ <;> rfl

end
end Dubon2026.SourceEllipticExceptional
