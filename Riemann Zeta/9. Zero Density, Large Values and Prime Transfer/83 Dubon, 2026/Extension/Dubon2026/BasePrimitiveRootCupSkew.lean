import Dubon2026.BasePrimitiveRootCocycleCharacter
import Dubon2026.ContinuousCupSkewSymmetry

/-! # The original root/character cups are skew over a base primitive root -/

namespace Dubon2026
noncomputable section

variable {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω]
  {n : ℕ} [NeZero n] {ζ : K} (hζ : IsPrimitiveRoot ζ n)
  [TopologicalSpace (galoisRootOfUnityRepresentation (K := K) (Ω := Ω) n)]
  [DiscreteTopology (galoisRootOfUnityRepresentation (K := K) (Ω := Ω) n)]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits K Ω)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K Ω)]

/-- The literal finite characters of two original root cocycles give opposite
cup classes after exchanging the original factors. The existing continuous
cup homotopy supplies the sign; no local-duality premise is used. -/
theorem basePrimitiveRootCocycleCup_swap_add
    (c d : continuousRepresentationCocyclesOne
      (galoisRootOfUnityRepresentation (K := K) (Ω := Ω) n)) :
    continuousGaloisRootCharacterH1Cup n (basePrimitiveRootCocycleCharacter hζ c)
        (Submodule.Quotient.mk d) +
      continuousGaloisRootCharacterH1Cup n (basePrimitiveRootCocycleCharacter hζ d)
        (Submodule.Quotient.mk c) = 0 := by
  let A := galoisRootOfUnityRepresentation (K := K) (Ω := Ω) n
  let B := Rep.of (1 : Representation ℤ Gal(Ω/K) (ZMod n))
  let β := galoisRootExponentPairing (K := K) (Ω := Ω) n
  let hc := continuousGaloisFiniteCharacterOneCocycle n (basePrimitiveRootCocycleCharacter hζ c)
  have hflip :
      continuousOneCocycleCup B A A β.flip
        (fun g x y => galoisRootExponentPairing_equivariant n g y x)
        continuous_of_discreteTopology (discreteGaloisRootAction_continuous n) hc d =
      continuousGaloisRootCharacterCupCocycle n (basePrimitiveRootCocycleCharacter hζ d) c := by
    apply Subtype.ext
    apply Subtype.ext
    funext z
    obtain ⟨g, h⟩ := z
    change galoisRootExponentPairing n (A.ρ g (d.val h))
      (basePrimitiveRootCocycleCharacter hζ c g).toAdd =
        galoisRootExponentPairing n (c.val g)
          (basePrimitiveRootCocycleCharacter hζ d h).toAdd
    rw [basePrimitiveRootCoefficient_action hζ]
    have he := basePrimitiveRootExponentPairing_symm (Ω := Ω) hζ
      (basePrimitiveRootCocycleCharacter hζ d h).toAdd
      (basePrimitiveRootCocycleCharacter hζ c g).toAdd
    rw [basePrimitiveRootCocycleCharacter_apply, basePrimitiveRootCocycleCharacter_apply] at he
    exact he
  have h := continuousCocycleCupClass_swap_add A B A β
    (galoisRootExponentPairing_equivariant n) continuous_of_discreteTopology
    (discreteGaloisRootAction_continuous n) continuous_snd
    (discreteGaloisRootAction_continuous n) d hc
  change (Submodule.Quotient.mk
    (continuousGaloisRootCharacterCupCocycle n (basePrimitiveRootCocycleCharacter hζ c) d) :
      GaloisRootContinuousH2 (K := K) (Ω := Ω) n) +
      Submodule.Quotient.mk
        (continuousOneCocycleCup B A A β.flip
          (fun g x y => galoisRootExponentPairing_equivariant n g y x)
          continuous_of_discreteTopology (discreteGaloisRootAction_continuous n) hc d) = 0 at h
  rw [hflip] at h
  exact h

end
end Dubon2026
