import Dubon2026.WittCyclotomicChangedNorm
import Dubon2026.RationalPrimeNaturalWittIntertwiner
import Dubon2026.RationalPrimeWittFractionField

/-! # The actual cyclotomic norm for an original rational natural unit

Construct the original valuation-integer unit, and consume its literal
Witt image in the evaluated primitive-point theorem. The negative point
has norm equal to the original coefficient image of ap. No convergent
series, primitive torsion, field degree or norm identity is assumed.
Descent of this finite construction to the original completion and its
unramified compositum remains necessary for DUB-17 ramified reciprocity.
-/
namespace Dubon2026
noncomputable section
open scoped ValuativeRel
attribute [local instance] rationalPrimeWittPrime wittCyclotomicRootDomain
  wittCyclotomicRootFaithful wittCyclotomicFieldAlgebra wittCyclotomicFieldTower
  wittCyclotomicFieldFinite

/-- Each original natural unit supplies an actual primitive field point with the exact required completed-coefficient norm. -/
theorem rationalPrimeNaturalWittNorm_exists (p : ℕ) (hp : p.Prime) (n a : ℕ) (ha : ¬p ∣ a) :
    let q := Rat.HeightOneSpectrum.natGenerator (rationalPrimePlace p hp)
    ∃ u : 𝒪[rationalPrimeLocalField p hp]ˣ, u.val = a ∧
      let v := Units.map (rationalPrimeIntegerWittMap p hp).toMonoidHom u
      IntermediateField.adjoin (rationalPrimeWittField p hp)
        ({wittCyclotomicChangedFieldPoint q v n} : Set (wittCyclotomicField q n)) = ⊤ ∧
      Algebra.norm (rationalPrimeWittField p hp) (-wittCyclotomicChangedFieldPoint q v n) =
        algebraMap _ (rationalPrimeWittField p hp)
          (rationalPrimeIntegerWittMap p hp (u.val * p)) := by
  dsimp only
  obtain ⟨u, hu, _⟩ := rationalPrimeNaturalWittIntertwiner_exists p hp a ha
  let q := Rat.HeightOneSpectrum.natGenerator (rationalPrimePlace p hp)
  let v := Units.map (rationalPrimeIntegerWittMap p hp).toMonoidHom u
  have hv : (v : WittVector q (AlgebraicClosure (ZMod q))) = a := by
    change rationalPrimeIntegerWittMap p hp u.val = a
    rw [hu, map_natCast]
  have haq : ¬q ∣ a := by simpa only [q, rationalPrimePlace_natGenerator] using ha
  refine ⟨u, hu, wittCyclotomicChangedFieldPoint_adjoin q v n a hv haq, ?_⟩
  rw [wittCyclotomicChangedFieldPoint_norm_neg q v n a hv haq]
  apply congrArg (algebraMap _ (rationalPrimeWittField p hp))
  change rationalPrimeIntegerWittMap p hp u.val * q =
    rationalPrimeIntegerWittMap p hp (u.val * p)
  rw [map_mul, map_natCast]
  exact congrArg (fun t : ℕ => rationalPrimeIntegerWittMap p hp u.val * t)
    (rationalPrimePlace_natGenerator p hp)

end
end Dubon2026
