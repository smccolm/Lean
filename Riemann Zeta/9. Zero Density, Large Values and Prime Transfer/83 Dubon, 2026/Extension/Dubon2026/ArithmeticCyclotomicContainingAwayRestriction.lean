import Dubon2026.ArithmeticCyclotomicContainingFieldAway
import Dubon2026.ArithmeticFiniteLocalRestrictionTower
import Dubon2026.RationalCyclotomicPrincipalStageBridge
import Dubon2026.LocalFieldFiniteCyclicReciprocityTower

/-! # The actual away-prime factor restricts to original cyclic reciprocity

The full cyclotomic containing field need not be cyclic. Its actual local
stage is cyclic away from the conductor, so original reciprocity supplies
the factor. The proved reciprocity tower and original restriction square
identify its restriction to the specified global cyclic subfield. DUB-17
needs precisely this identification in the global principal product.
-/
namespace Dubon2026
noncomputable section
open scoped NumberField

attribute [local instance] arithmeticFiniteLocalStageAlgebra
  arithmeticFiniteLocalStageGalois arithmeticFiniteLocalStageRationalAlgebra

variable (a : 𝓞 ℚ) (F : FiniteGaloisIntermediateField ℚ (rationalUnramifiedExtension a))
  (p : ℕ) (hp : p.Prime) (n : ℕ) [NeZero n]
  [IsCyclotomicExtension {n} ℚ F] (hpn : ¬p ∣ n) (q : ℚˣ)

include hp hpn q

/-- The containing-field factor is the restriction of original local
reciprocity, with local cyclicity derived from unramifiedness. -/
def arithmeticCyclotomicContainingAwayAut : Gal(F/ℚ) := by
  let K := rationalPrimeLocalField p hp
  let Ω := rationalPrimeLocalClosure p hp
  let N := rationalArithmeticFiniteLocalStage a F p hp
  letI : TopologicalSpace (Rep.ofAlgebraAutOnUnits K Ω) := ⊥
  letI : DiscreteTopology (Rep.ofAlgebraAutOnUnits K Ω) := ⟨rfl⟩
  letI : IsCyclic Gal(N/K) := arithmeticCyclotomicFiniteLocalStage_isCyclic_away a F p hp n hpn
  exact rationalArithmeticFiniteLocalRestriction a F p hp
    (localFieldFiniteCyclicReciprocity K Ω N
      (Additive.ofMul (rationalPrimeRationalUnit p hp q))).toMul

/-- The actual containing-field away-prime factor has the original
normalized prime-power character. -/
theorem arithmeticCyclotomicContainingAwayAut_autToPow
    {ζ : F} (hζ : IsPrimitiveRoot ζ n) :
    hζ.autToPow ℚ (arithmeticCyclotomicContainingAwayAut a F p hp n hpn q) =
      ZMod.unitOfCoprime p (hp.coprime_iff_not_dvd.mpr hpn) ^
        localFieldUnitOrder (rationalPrimeLocalField p hp)
          (Additive.ofMul (rationalPrimeRationalUnit p hp q)) := by
  let K := rationalPrimeLocalField p hp
  let Ω := rationalPrimeLocalClosure p hp
  letI : TopologicalSpace (Rep.ofAlgebraAutOnUnits K Ω) := ⊥
  letI : DiscreteTopology (Rep.ofAlgebraAutOnUnits K Ω) := ⟨rfl⟩
  exact arithmeticCyclotomicContainingField_reciprocity_away a F p hp n hpn hζ
    (rationalPrimeRationalUnit p hp q)

variable (E : FiniteGaloisIntermediateField ℚ (rationalUnramifiedExtension a))
    (hEF : E.toIntermediateField ≤ F.toIntermediateField) [IsCyclic Gal(E/ℚ)]

/-- The original containing-field away-prime factor restricts to the
literal original arithmetic reciprocity automorphism of the cyclic subfield. -/
theorem arithmeticCyclotomicContainingAwayAut_restrict :
    embeddedNormalGaloisRestriction (F := ℚ) (IntermediateField.inclusion hEF)
      (arithmeticCyclotomicContainingAwayAut a F p hp n hpn q) =
      rationalArithmeticFiniteLocalReciprocityAut a E p hp q := by
  let K := rationalPrimeLocalField p hp
  let Ω := rationalPrimeLocalClosure p hp
  let M := rationalArithmeticFiniteLocalStage a E p hp
  let N := rationalArithmeticFiniteLocalStage a F p hp
  let hMN := rationalArithmeticFiniteLocalStage_mono a E F hEF p hp
  letI : Algebra M N := (IntermediateField.inclusion hMN).toAlgebra
  letI : TopologicalSpace (Rep.ofAlgebraAutOnUnits K Ω) := ⊥
  letI : DiscreteTopology (Rep.ofAlgebraAutOnUnits K Ω) := ⟨rfl⟩
  letI : IsCyclic Gal(M/K) := arithmeticCyclotomicLocalCyclic a E p hp
  letI : IsCyclic Gal(N/K) := arithmeticCyclotomicFiniteLocalStage_isCyclic_away a F p hp n hpn
  let u := rationalPrimeRationalUnit p hp q
  have hR := rationalArithmeticFiniteLocalRestriction_tower a E F hEF p hp
    (localFieldFiniteCyclicReciprocity K Ω N (Additive.ofMul u)).toMul
  have hρ := localFieldFiniteCyclicReciprocity_restrict K Ω M N hMN u
  exact hR.trans (congrArg (rationalArithmeticFiniteLocalRestriction a E p hp) hρ)

end
end Dubon2026
