import Dubon2026.RationalPrimeWittFixedRing

/-! # The original rational prime field inside the Witt fraction field

Extend the proved injective original integer map by fraction-field
localization. Actual Witt Frobenius fixes the image of that same original
local field. These are the original-object maps required for coefficient
descent of the auxiliary finite field on DUB-17's ramified reciprocity route.
-/
namespace Dubon2026
noncomputable section
open scoped ValuativeRel
attribute [local instance] rationalPrimeWittPrime

/-- The actual fraction field of the completed-unramified Witt coefficients. -/
abbrev rationalPrimeWittField (p : ℕ) (hp : p.Prime) :=
  FractionRing (WittVector (Rat.HeightOneSpectrum.natGenerator (rationalPrimePlace p hp))
    (AlgebraicClosure (ZMod (Rat.HeightOneSpectrum.natGenerator (rationalPrimePlace p hp)))))

/-- The original rational prime field maps by localization of its actual integer coefficient map. -/
def rationalPrimeWittFieldMap (p : ℕ) (hp : p.Prime) :
    rationalPrimeLocalField p hp →+* rationalPrimeWittField p hp :=
  IsFractionRing.lift (K := rationalPrimeLocalField p hp)
    (g := (algebraMap _ (rationalPrimeWittField p hp)).comp (rationalPrimeIntegerWittMap p hp))
    ((IsFractionRing.injective _ _).comp (rationalPrimeIntegerWittMap_injective p hp))

/-- The original field map extends exactly the original integer map. -/
theorem rationalPrimeWittFieldMap_integer (p : ℕ) (hp : p.Prime)
    (z : 𝒪[rationalPrimeLocalField p hp]) :
    rationalPrimeWittFieldMap p hp (algebraMap 𝒪[rationalPrimeLocalField p hp]
      (rationalPrimeLocalField p hp) z) =
      algebraMap _ (rationalPrimeWittField p hp) (rationalPrimeIntegerWittMap p hp z) :=
  IsFractionRing.lift_algebraMap _ z

/-- The actual Witt fraction-field Frobenius, with its original coefficient action. -/
def rationalPrimeWittFieldFrobenius (p : ℕ) (hp : p.Prime) :
    rationalPrimeWittField p hp ≃+* rationalPrimeWittField p hp :=
  IsFractionRing.ringEquivOfRingEquiv
    (WittVector.frobeniusEquiv (Rat.HeightOneSpectrum.natGenerator (rationalPrimePlace p hp))
      (AlgebraicClosure (ZMod (Rat.HeightOneSpectrum.natGenerator (rationalPrimePlace p hp)))))

/-- The actual field Frobenius restricts to the actual Witt coefficient Frobenius. -/
theorem rationalPrimeWittFieldFrobenius_integer (p : ℕ) (hp : p.Prime)
    (x : WittVector (Rat.HeightOneSpectrum.natGenerator (rationalPrimePlace p hp))
      (AlgebraicClosure (ZMod (Rat.HeightOneSpectrum.natGenerator (rationalPrimePlace p hp))))) :
    rationalPrimeWittFieldFrobenius p hp (algebraMap _ (rationalPrimeWittField p hp) x) =
      algebraMap _ (rationalPrimeWittField p hp) (WittVector.frobenius x) := by
  unfold rationalPrimeWittFieldFrobenius
  rw [IsFractionRing.ringEquivOfRingEquiv_algebraMap]
  rfl

/-- Actual Witt field Frobenius fixes every element of the original rational prime local field. -/
theorem rationalPrimeWittFieldFrobenius_base (p : ℕ) (hp : p.Prime)
    (x : rationalPrimeLocalField p hp) :
    rationalPrimeWittFieldFrobenius p hp (rationalPrimeWittFieldMap p hp x) =
      rationalPrimeWittFieldMap p hp x := by
  have h : (rationalPrimeWittFieldFrobenius p hp).toRingHom.comp (rationalPrimeWittFieldMap p hp) =
      rationalPrimeWittFieldMap p hp := by
    apply IsFractionRing.ringHom_ext (A := 𝒪[rationalPrimeLocalField p hp])
    intro z
    rw [RingHom.comp_apply, rationalPrimeWittFieldMap_integer]
    exact (rationalPrimeWittFieldFrobenius_integer p hp (rationalPrimeIntegerWittMap p hp z)).trans
      (congrArg (algebraMap _ (rationalPrimeWittField p hp))
        (rationalPrimeIntegerWittMap_frobenius p hp z))
  exact RingHom.congr_fun h x

end
end Dubon2026
