import Dubon2026.GaloisRootExponentPairing
import Mathlib.Topology.Instances.ZMod

/-! # The actual continuous Kummer/finite-character cup

This specializes the existing cohomology cup to the literal exponent pairing.
Its original cocycle formula is retained for the cyclic norm comparison.
-/

namespace Dubon2026
noncomputable section

variable {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω]
  (n : ℕ) [NeZero n]
  [TopologicalSpace (galoisRootOfUnityRepresentation (K := K) (Ω := Ω) n)]
  [DiscreteTopology (galoisRootOfUnityRepresentation (K := K) (Ω := Ω) n)]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits K Ω)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K Ω)]
  (χ : Gal(Ω/K) →ₜ* Multiplicative (ZMod n))

/-- An actual continuous finite character is the corresponding original
continuous one-cocycle for the trivial residue coefficient action. -/
def continuousGaloisFiniteCharacterOneCocycle :
    continuousRepresentationCocyclesOne (Rep.of (1 : Representation ℤ Gal(Ω/K) (ZMod n))) := by
  refine ⟨⟨fun g => (χ g).toAdd, ?_⟩, χ.continuous⟩
  apply (groupCohomology.mem_cocycles₁_iff _).mpr
  intro g h
  change (χ (g * h)).toAdd = (χ h).toAdd + (χ g).toAdd
  rw [map_mul, toAdd_mul, add_comm]

/-- The actual continuous root/character two-cocycle obtained from the same
original cohomological cup and literal exponent pairing. -/
def continuousGaloisRootCharacterCupCocycle
    (c : continuousRepresentationCocyclesOne
      (galoisRootOfUnityRepresentation (K := K) (Ω := Ω) n)) :
    continuousRepresentationCocyclesTwo
      (galoisRootOfUnityRepresentation (K := K) (Ω := Ω) n) :=
  continuousOneCocycleCup
    (galoisRootOfUnityRepresentation (K := K) (Ω := Ω) n)
    (Rep.of (1 : Representation ℤ Gal(Ω/K) (ZMod n)))
    (galoisRootOfUnityRepresentation (K := K) (Ω := Ω) n)
    (galoisRootExponentPairing n) (galoisRootExponentPairing_equivariant n)
    continuous_of_discreteTopology continuous_snd c
    (continuousGaloisFiniteCharacterOneCocycle n χ)

omit [IsGalois K Ω] [TopologicalSpace (Rep.ofAlgebraAutOnUnits K Ω)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K Ω)] in
/-- The original root/character cup evaluates to the actual root at g raised
to the canonical exponent of the original character at h. -/
theorem continuousGaloisRootCharacterCupCocycle_apply
    (c : continuousRepresentationCocyclesOne
      (galoisRootOfUnityRepresentation (K := K) (Ω := Ω) n)) (g h : Gal(Ω/K)) :
    ((Additive.toMul (Rep.toAdditive
      ((continuousGaloisRootCharacterCupCocycle n χ c).val (g, h))) :
        rootsOfUnity n Ω) : Ωˣ) =
      ((Additive.toMul (Rep.toAdditive (c.val g)) : rootsOfUnity n Ω) : Ωˣ) ^ (χ h).toAdd.val :=
  galoisRootExponentPairing_apply n (c.val g) (χ h).toAdd

/-- Cup with the original finite character, as a map on the actual original
root-valued H1 and H2 quotients. -/
def continuousGaloisRootCharacterH1Cup :
    GaloisRootContinuousH1 (K := K) (Ω := Ω) n →ₗ[ℤ]
      GaloisRootContinuousH2 (K := K) (Ω := Ω) n :=
  (continuousH1Cup
    (galoisRootOfUnityRepresentation (K := K) (Ω := Ω) n)
    (Rep.of (1 : Representation ℤ Gal(Ω/K) (ZMod n)))
    (galoisRootOfUnityRepresentation (K := K) (Ω := Ω) n)
    (galoisRootExponentPairing n) (galoisRootExponentPairing_equivariant n)
    continuous_of_discreteTopology
    (discreteGaloisRootAction_continuous (K := K) (Ω := Ω) n) continuous_snd
    (discreteGaloisRootAction_continuous (K := K) (Ω := Ω) n)).flip
      (Submodule.Quotient.mk (continuousGaloisFiniteCharacterOneCocycle n χ))

/-- The original H1 cup has the exact original continuous cocycle representative. -/
theorem continuousGaloisRootCharacterH1Cup_mk
    (c : continuousRepresentationCocyclesOne
      (galoisRootOfUnityRepresentation (K := K) (Ω := Ω) n)) :
    continuousGaloisRootCharacterH1Cup n χ (Submodule.Quotient.mk c) =
      Submodule.Quotient.mk (continuousGaloisRootCharacterCupCocycle n χ c) := by
  rfl

end
end Dubon2026
