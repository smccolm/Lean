import Dubon2026.SourceEllipticExceptionalCoordinates
import Dubon2026.SourceEllipticInverseCoordinateNaturality

/-! DUB-17/18 -> characteristic-two weighted census -> actual quaternion
actions and the order-twelve cyclic-subgroup action. Existing coordinate
naturality and coordinate injectivity make the actual stabilizer point maps
a group homomorphism. This avoids repeating curve casts in the two exact
elliptic fixed-subgroup-count consumers. -/
namespace Dubon2026.SourceEllipticStabilizer
open WeierstrassCurve SourceEllipticExceptional SourceEllipticVariableChange
open SourceEllipticReduction
noncomputable section
variable {K : Type*} [Field K] [DecidableEq K]

theorem stabilizerPointEquiv_one (W : WeierstrassCurve K)
    (h : (1 : VariableChange K) • W = W) (P : W.toAffine.Point) :
    stabilizerPointEquiv W 1 h P = P := by
  apply xy_injective
  rw [xy_stabilizerPointEquiv]
  rcases xy P with _ | ⟨x, y⟩
  · rfl
  · simp [vcXInv, vcYInv, VariableChange.one_def]

theorem stabilizerPointEquiv_mul (W : WeierstrassCurve K)
    (C D : VariableChange K) (hC : C • W = W) (hD : D • W = W)
    (hCD : (C * D) • W = W) (P : W.toAffine.Point) :
    stabilizerPointEquiv W (C * D) hCD P =
      stabilizerPointEquiv W C hC (stabilizerPointEquiv W D hD P) := by
  apply xy_injective
  rw [xy_stabilizerPointEquiv, xy_stabilizerPointEquiv, xy_stabilizerPointEquiv]
  rcases xy P with _ | ⟨x, y⟩
  · rfl
  · simp only [Option.map_some, vcXInv_mul, vcYInv_mul]

/-- The literal stabilized inverse coordinate maps as additive automorphisms. -/
def stabilizerPointHom (W : WeierstrassCurve K) :
    MulAction.stabilizer (VariableChange K) W →* AddAut W.toAffine.Point where
  toFun C := stabilizerPointEquiv W C.val (MulAction.mem_stabilizer_iff.mp C.property)
  map_one' := by
    ext P
    exact stabilizerPointEquiv_one W _ P
  map_mul' C D := by
    ext P
    exact stabilizerPointEquiv_mul W C.val D.val
      (MulAction.mem_stabilizer_iff.mp C.property)
      (MulAction.mem_stabilizer_iff.mp D.property)
      (MulAction.mem_stabilizer_iff.mp (C * D).property) P

end
end Dubon2026.SourceEllipticStabilizer
