import Dubon2026.RationalPrimeChangedAuxiliaryField
import Dubon2026.WittCyclotomicDiagonalCoefficients

/-! # Diagonal Frobenius fixes the actual original auxiliary field

The actual coefficient-field Frobenius fixes the literal original
completion. Combined with the proved fixed changed point, field-adjoin
induction proves fixation of every element of the constructed finite
auxiliary field. These are the precise scalar conditions required for
the unramified-compositum Frobenius comparison in DUB-17 reciprocity.
-/
namespace Dubon2026
noncomputable section
open scoped ValuativeRel
attribute [local instance] rationalPrimeWittPrime wittCyclotomicRootDomain
  wittCyclotomicRootFaithful wittCyclotomicFieldAlgebra wittCyclotomicFieldTower
  rationalPrimeWittOriginalAlgebra rationalPrimeWittCyclotomicAlgebra rationalPrimeWittCyclotomicTower
  rationalPrimeWittCyclotomicModule rationalPrimeWittCyclotomicMulAction

/-- The actual diagonal field Frobenius fixes every element of the literal original completion. -/
theorem rationalPrimeDiagonalFrobenius_base (p : ℕ) (hp : p.Prime) (n a b : ℕ) :
    let q := Rat.HeightOneSpectrum.natGenerator (rationalPrimePlace p hp)
    ∀ (ha : a.Coprime (q ^ (n + 1))) (hb : b.Coprime (q ^ (n + 1)))
      (hab : a * b ≡ 1 [MOD q ^ (n + 1)]) (x : rationalPrimeLocalField p hp),
    wittCyclotomicDiagonalFieldFrobenius q n a b ha hb hab
      (algebraMap _ (wittCyclotomicField q n) x) = algebraMap _ (wittCyclotomicField q n) x := by
  dsimp only
  intro ha hb hab x
  change wittCyclotomicDiagonalFieldFrobenius _ n a b ha hb hab
    (algebraMap (rationalPrimeWittField p hp) _ (rationalPrimeWittFieldMap p hp x)) =
    algebraMap (rationalPrimeWittField p hp) _ (rationalPrimeWittFieldMap p hp x)
  rw [wittCyclotomicDiagonalFieldFrobenius_coefficient]
  change algebraMap (rationalPrimeWittField p hp) _
    (rationalPrimeWittFieldFrobenius p hp (rationalPrimeWittFieldMap p hp x)) = _
  rw [rationalPrimeWittFieldFrobenius_base]

/-- Every element of the actual finite auxiliary field is fixed by the inverse-unit diagonal Frobenius. -/
theorem rationalPrimeDiagonalFrobenius_auxiliary (p : ℕ) (hp : p.Prime) (n a b : ℕ)
    (u : 𝒪[rationalPrimeLocalField p hp]ˣ) (hu : u.val = a) :
    let q := Rat.HeightOneSpectrum.natGenerator (rationalPrimePlace p hp)
    ∀ (ha : a.Coprime (q ^ (n + 1))) (hb : b.Coprime (q ^ (n + 1)))
      (hab : a * b ≡ 1 [MOD q ^ (n + 1)]) (x : rationalPrimeChangedAuxiliaryField p hp n u),
    wittCyclotomicDiagonalFieldFrobenius q n a b ha hb hab x.val = x.val := by
  dsimp only
  intro ha hb hab x
  let q := Rat.HeightOneSpectrum.natGenerator (rationalPrimePlace p hp)
  let v := Units.map (rationalPrimeIntegerWittMap p hp).toMonoidHom u
  let σ := wittCyclotomicDiagonalFieldFrobenius q n a b ha hb hab
  have hv : (v : WittVector q (AlgebraicClosure (ZMod q))) = a := by
    change rationalPrimeIntegerWittMap p hp u.val = a
    rw [hu, map_natCast]
  have hθ : σ (wittCyclotomicChangedFieldPoint q v n) = wittCyclotomicChangedFieldPoint q v n :=
    wittCyclotomicDiagonalFieldFrobenius_changedPoint q n a b ha hb hab v hv
  apply IntermediateField.adjoin_induction (rationalPrimeLocalField p hp)
    (p := fun y _ => σ y = y) (h := x.property)
  · intro y hy
    obtain rfl := Set.mem_singleton_iff.mp hy
    exact hθ
  · exact rationalPrimeDiagonalFrobenius_base p hp n a b ha hb hab
  · intro y z _ _ hy hz
    rw [map_add, hy, hz]
  · intro y _ hy
    rw [map_inv₀, hy]
  · intro y z _ _ hy hz
    rw [map_mul, hy, hz]

end
end Dubon2026
