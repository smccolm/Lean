import Dubon2026.ContinuousRootCharacterCup

/-! # Bilinearity in the actual finite character of the original Kummer cup

This retains both original factors and allows character-side nondegeneracy to
give finiteness and the required dual map, rather than assuming those properties.
-/

namespace Dubon2026
noncomputable section

variable {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] (n : ℕ) [NeZero n]

/-- Pointwise multiplication of actual continuous finite characters gives
addition of the original trivial-action cocycles. -/
def continuousGaloisFiniteCharacterCocycleHom :
    Additive (Gal(Ω/K) →ₜ* Multiplicative (ZMod n)) →+
      continuousRepresentationCocyclesOne (Rep.of (1 : Representation ℤ Gal(Ω/K) (ZMod n))) where
  toFun χ := continuousGaloisFiniteCharacterOneCocycle n χ.toMul
  map_zero' := by
    apply Subtype.ext
    apply Subtype.ext
    funext g
    rfl
  map_add' χ ψ := by
    apply Subtype.ext
    apply Subtype.ext
    funext g
    rfl

variable [IsGalois K Ω]
  [TopologicalSpace (galoisRootOfUnityRepresentation (K := K) (Ω := Ω) n)]
  [DiscreteTopology (galoisRootOfUnityRepresentation (K := K) (Ω := Ω) n)]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits K Ω)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K Ω)]

/-- The original local Kummer cup is bilinear on the actual root H1 and the
additively written group of actual continuous finite characters. -/
def continuousKummerCharacterPairing :
    GaloisRootContinuousH1 (K := K) (Ω := Ω) n →ₗ[ℤ]
      Additive (Gal(Ω/K) →ₜ* Multiplicative (ZMod n)) →ₗ[ℤ]
        GaloisRootContinuousH2 (K := K) (Ω := Ω) n :=
  (continuousH1Cup
    (galoisRootOfUnityRepresentation (K := K) (Ω := Ω) n)
    (Rep.of (1 : Representation ℤ Gal(Ω/K) (ZMod n)))
    (galoisRootOfUnityRepresentation (K := K) (Ω := Ω) n)
    (galoisRootExponentPairing n) (galoisRootExponentPairing_equivariant n)
    continuous_of_discreteTopology
    (discreteGaloisRootAction_continuous n) continuous_snd
    (discreteGaloisRootAction_continuous n)).compl₂
      ((continuousRepresentationCoboundariesOne
        (Rep.of (1 : Representation ℤ Gal(Ω/K) (ZMod n))) continuous_snd).mkQ.comp
        (continuousGaloisFiniteCharacterCocycleHom (K := K) (Ω := Ω) n).toIntLinearMap)

/-- The bilinear map is exactly cup with the same original character and
the same original root H1 class. -/
theorem continuousKummerCharacterPairing_apply
    (x : GaloisRootContinuousH1 (K := K) (Ω := Ω) n)
    (χ : Additive (Gal(Ω/K) →ₜ* Multiplicative (ZMod n))) :
    continuousKummerCharacterPairing n x χ =
      continuousGaloisRootCharacterH1Cup n χ.toMul x := by
  rfl

end
end Dubon2026
