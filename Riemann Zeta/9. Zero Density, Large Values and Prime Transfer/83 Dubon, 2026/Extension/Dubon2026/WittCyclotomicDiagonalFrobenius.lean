import Dubon2026.WittCyclotomicCoefficientFrobenius
import Dubon2026.WittCyclotomicNaturalIntertwining

/-! # Actual semilinear evaluation and the diagonal Frobenius

Continuity and the genuine convergent coefficient sum prove evaluation
compatibility. Combining coefficient Frobenius with the inverse natural
power action fixes the actual changed point by its proved formal Frobenius
identity. This is the necessary fixed-point input for DUB-17 auxiliary descent.
-/
namespace Dubon2026
noncomputable section
open scoped PowerSeries.WithPiTopology
attribute [local instance] wittCyclotomicRootDomain wittCyclotomicCoefficientUniformSpace
  wittCyclotomicRootWithIdeal wittCyclotomicRootCompleteSpace wittCyclotomicRootT2Space

/-- Actual continuous semilinear action commutes with convergent evaluation and actual coefficient Frobenius. -/
theorem wittCyclotomicFrobeniusHom_eval (p : ℕ) [Fact p.Prime] (n : ℕ)
    (f : wittCyclotomicRootAlgebra p n →+* wittCyclotomicRootAlgebra p n)
    (hf : ∀ c : WittVector p (AlgebraicClosure (ZMod p)),
      f (algebraMap _ (wittCyclotomicRootAlgebra p n) c) =
        algebraMap _ (wittCyclotomicRootAlgebra p n) (WittVector.frobenius c))
    (x : wittCyclotomicRootAlgebra p n) (hx : PowerSeries.HasEval x)
    (H : PowerSeries (WittVector p (AlgebraicClosure (ZMod p)))) :
    f (wittCyclotomicPowerSeriesEval p n x hx H) =
      wittCyclotomicPowerSeriesEval p n (f x)
        (hx.map (wittCyclotomicRootHom_continuous p n f)) (PowerSeries.map WittVector.frobenius H) := by
  have h := (PowerSeries.hasSum_eval₂ (φ := algebraMap _ (wittCyclotomicRootAlgebra p n))
    continuous_of_discreteTopology hx H).map f (wittCyclotomicRootHom_continuous p n f)
  have h' := PowerSeries.hasSum_eval₂ (φ := algebraMap _ (wittCyclotomicRootAlgebra p n))
    continuous_of_discreteTopology (hx.map (wittCyclotomicRootHom_continuous p n f))
    (PowerSeries.map WittVector.frobenius H)
  simp only [Function.comp_def, map_mul, map_pow, hf] at h
  simp only [PowerSeries.coeff_map] at h'
  simpa only [wittCyclotomicPowerSeriesEval, PowerSeries.coe_eval₂Hom] using h.unique h'

/-- The actual diagonal Frobenius uses the inverse natural power on primitive cyclotomic roots. -/
def wittCyclotomicDiagonalFrobenius (p : ℕ) [Fact p.Prime] (n a b : ℕ)
    (ha : a.Coprime (p ^ (n + 1))) (hb : b.Coprime (p ^ (n + 1)))
    (hab : a * b ≡ 1 [MOD p ^ (n + 1)]) :
    wittCyclotomicRootAlgebra p n ≃+* wittCyclotomicRootAlgebra p n :=
  (wittCyclotomicCoefficientFrobenius p n).trans
    (wittCyclotomicPowerEquiv p n b a hb ha (by simpa only [Nat.mul_comm] using hab)).toRingEquiv

/-- Diagonal Frobenius acts on actual Witt coefficients by their original Frobenius. -/
theorem wittCyclotomicDiagonalFrobenius_coefficient (p : ℕ) [Fact p.Prime] (n a b : ℕ)
    (ha : a.Coprime (p ^ (n + 1))) (hb : b.Coprime (p ^ (n + 1)))
    (hab : a * b ≡ 1 [MOD p ^ (n + 1)]) (c : WittVector p (AlgebraicClosure (ZMod p))) :
    wittCyclotomicDiagonalFrobenius p n a b ha hb hab
      (algebraMap _ (wittCyclotomicRootAlgebra p n) c) =
      algebraMap _ (wittCyclotomicRootAlgebra p n) (WittVector.frobenius c) := by
  rw [wittCyclotomicDiagonalFrobenius, RingEquiv.trans_apply, wittCyclotomicCoefficientFrobenius_coefficient]
  exact AlgEquiv.commutes _ _

/-- Diagonal Frobenius has the literal inverse-power action on the original translated cyclotomic root. -/
theorem wittCyclotomicDiagonalFrobenius_root (p : ℕ) [Fact p.Prime] (n a b : ℕ)
    (ha : a.Coprime (p ^ (n + 1))) (hb : b.Coprime (p ^ (n + 1)))
    (hab : a * b ≡ 1 [MOD p ^ (n + 1)]) :
    wittCyclotomicDiagonalFrobenius p n a b ha hb hab
      (AdjoinRoot.root (primePowerShiftedCyclotomic (WittVector p (AlgebraicClosure (ZMod p))) p n)) =
      (wittCyclotomicPrimitiveRoot p n) ^ b - 1 := by
  rw [wittCyclotomicDiagonalFrobenius, RingEquiv.trans_apply, wittCyclotomicCoefficientFrobenius_root]
  exact wittCyclotomicPowerHom_root p n b hb

/-- The inverse-unit diagonal Frobenius fixes the actual evaluated changed point. -/
theorem wittCyclotomicDiagonalFrobenius_changedPoint (p : ℕ) [Fact p.Prime] (n a b : ℕ)
    (ha : a.Coprime (p ^ (n + 1))) (hb : b.Coprime (p ^ (n + 1)))
    (hab : a * b ≡ 1 [MOD p ^ (n + 1)])
    (u : (WittVector p (AlgebraicClosure (ZMod p)))ˣ)
    (hu : (u : WittVector p (AlgebraicClosure (ZMod p))) = a) :
    wittCyclotomicDiagonalFrobenius p n a b ha hb hab (wittCyclotomicChangedPoint p u n) =
      wittCyclotomicChangedPoint p u n := by
  rw [wittCyclotomicChangedPoint]
  refine (wittCyclotomicFrobeniusHom_eval p n
    (wittCyclotomicDiagonalFrobenius p n a b ha hb hab).toRingHom
    (wittCyclotomicDiagonalFrobenius_coefficient p n a b ha hb hab)
    _ (wittCyclotomicRoot_hasEval p n) (primeWittIntertwiner p u)).trans ?_
  rw [primeWittIntertwiner_frobenius_nat p u a hu,
    wittCyclotomicPowerSeriesEval_subst p n _ _ _ _
      (PowerSeries.HasSubst.of_constantCoeff_zero' (primeWittNaturalSeries_constantCoeff p a))]
  simp only [wittCyclotomicNaturalSeries_eval]
  have hz : (1 + wittCyclotomicDiagonalFrobenius p n a b ha hb hab
      (AdjoinRoot.root (primePowerShiftedCyclotomic (WittVector p (AlgebraicClosure (ZMod p))) p n))) ^ a - 1 =
      AdjoinRoot.root (primePowerShiftedCyclotomic (WittVector p (AlgebraicClosure (ZMod p))) p n) := by
    rw [wittCyclotomicDiagonalFrobenius_root, ← add_sub_assoc, add_sub_cancel_left, ← pow_mul]
    have h : (wittCyclotomicPrimitiveRoot p n) ^ (b * a) =
        (wittCyclotomicPrimitiveRoot p n) ^ 1 :=
      pow_eq_pow_of_modEq (by simpa only [Nat.mul_comm] using hab)
      (wittCyclotomicPrimitiveRoot_isPrimitive p n).pow_eq_one
    rw [h, pow_one, wittCyclotomicPrimitiveRoot, add_sub_cancel_left]
  simp only [wittCyclotomicPowerSeriesEval, PowerSeries.coe_eval₂Hom]
  exact congrArg (fun x : wittCyclotomicRootAlgebra p n =>
    PowerSeries.eval₂ (algebraMap (WittVector p (AlgebraicClosure (ZMod p)))
      (wittCyclotomicRootAlgebra p n)) x (primeWittIntertwiner p u)) hz

end
end Dubon2026
