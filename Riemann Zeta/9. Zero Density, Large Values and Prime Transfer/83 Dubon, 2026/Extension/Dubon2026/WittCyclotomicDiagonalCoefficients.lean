import Dubon2026.WittCyclotomicDiagonalField

/-! # The actual coefficient-field action of diagonal Frobenius

Fraction-field uniqueness extends the proved Witt coefficient action to
all actual coefficient fractions. This is required to prove that diagonal
Frobenius fixes the literal original completion and hence its constructed
auxiliary field on DUB-17's ramified reciprocity route.
-/
namespace Dubon2026
noncomputable section
attribute [local instance] wittCyclotomicRootDomain wittCyclotomicRootFaithful
  wittCyclotomicFieldAlgebra wittCyclotomicFieldTower

/-- The actual diagonal field Frobenius extends precisely the original Witt fraction-field Frobenius. -/
theorem wittCyclotomicDiagonalFieldFrobenius_coefficient (p : ℕ) [Fact p.Prime] (n a b : ℕ)
    (ha : a.Coprime (p ^ (n + 1))) (hb : b.Coprime (p ^ (n + 1)))
    (hab : a * b ≡ 1 [MOD p ^ (n + 1)])
    (x : FractionRing (WittVector p (AlgebraicClosure (ZMod p)))) :
    wittCyclotomicDiagonalFieldFrobenius p n a b ha hb hab
      (algebraMap _ (wittCyclotomicField p n) x) =
    algebraMap _ (wittCyclotomicField p n)
      ((IsFractionRing.ringEquivOfRingEquiv (WittVector.frobeniusEquiv p (AlgebraicClosure (ZMod p))) :
        FractionRing (WittVector p (AlgebraicClosure (ZMod p))) ≃+*
          FractionRing (WittVector p (AlgebraicClosure (ZMod p)))) x) := by
  let W := WittVector p (AlgebraicClosure (ZMod p))
  let F := FractionRing W
  let L := wittCyclotomicField p n
  let S := wittCyclotomicRootAlgebra p n
  let σ := wittCyclotomicDiagonalFieldFrobenius p n a b ha hb hab
  let τ : F ≃+* F := IsFractionRing.ringEquivOfRingEquiv (WittVector.frobeniusEquiv p (AlgebraicClosure (ZMod p)))
  have h : σ.toRingHom.comp (algebraMap F L) = (algebraMap F L).comp τ.toRingHom := by
    apply IsFractionRing.ringHom_ext (A := W)
    intro c
    simp only [RingHom.comp_apply]
    change σ (algebraMap F L (algebraMap W F c)) =
      algebraMap F L (τ (algebraMap W F c))
    have hτ : τ (algebraMap W F c) = algebraMap W F (WittVector.frobenius c) :=
      IsFractionRing.ringEquivOfRingEquiv_algebraMap _ c
    rw [hτ, ← IsScalarTower.algebraMap_apply W F L,
      ← IsScalarTower.algebraMap_apply W F L,
      IsScalarTower.algebraMap_apply W S L, IsScalarTower.algebraMap_apply W S L]
    rw [wittCyclotomicDiagonalFieldFrobenius_integer,
      wittCyclotomicDiagonalFrobenius_coefficient]
  exact RingHom.congr_fun h x

end
end Dubon2026
