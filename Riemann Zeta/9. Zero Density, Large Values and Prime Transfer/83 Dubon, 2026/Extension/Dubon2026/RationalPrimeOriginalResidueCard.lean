import Dubon2026.RationalPrimeLocalizedIntegerUnits
import Mathlib.NumberTheory.Padics.RingHoms

/-! # The original rational prime completion has residue cardinality p

The proved equality of original integer subrings and pinned completion
integer equivalence identify the actual residue cardinality. This supplies
the exponent in DUB-17's unramified cyclotomic Frobenius formula without
replacing the original arithmetic local field.
-/
namespace Dubon2026
noncomputable section
open scoped ValuativeRel
attribute [local instance 1100] Ring.toIntAlgebra

/-- The canonical residue field of the original rational prime completion has exactly p elements. -/
theorem rationalPrimeLocalField_residue_card (p : ℕ) (hp : p.Prime) :
    Nat.card 𝓀[rationalPrimeLocalField p hp] = p := by
  let v := rationalPrimePlace p hp
  letI : Fact (Rat.HeightOneSpectrum.primesEquiv v : ℕ).Prime :=
    ⟨(Rat.HeightOneSpectrum.primesEquiv v).property⟩
  let e₁ : 𝒪[rationalPrimeLocalField p hp] ≃+* rationalPrimeLocalIntegerRing p hp :=
    RingEquiv.subringCongr (rationalPrimeLocalInteger_subring_eq p hp)
  let e₂ := (Rat.HeightOneSpectrum.adicCompletionIntegers.padicIntEquiv v).toRingEquiv
  let e := (IsLocalRing.ResidueField.mapEquiv (e₁.trans e₂)).trans
    (PadicInt.residueField (p := Rat.HeightOneSpectrum.primesEquiv v))
  calc
    Nat.card 𝓀[rationalPrimeLocalField p hp] =
        Nat.card (ZMod (Rat.HeightOneSpectrum.primesEquiv v)) := Nat.card_congr e.toEquiv
    _ = (Rat.HeightOneSpectrum.primesEquiv v : ℕ) := Nat.card_zmod _
    _ = p := rationalPrimePlace_natGenerator p hp

end
end Dubon2026
