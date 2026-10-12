import Dubon2026.ScalarCharacterDualKummerCohomology
import Dubon2026.LocalFieldRootH2Invariant

/-! # The original local character-dual cup normalized by its invariant

The actual character-line H2 is mapped through its root coefficient equivalence
and the existing local invariant. This is the scalar-valued pairing needed by
DUB-17 local duality; no annihilator or perfectness hypothesis defines it.
-/

namespace Dubon2026
noncomputable section

attribute [local instance] characterDualSequenceContinuousSMul

variable (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω] [IsAlgClosed Ω]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  (q : ℕ) [Fact q.Prime] (χ : Gal(Ω/K) →* ZMod q) (hχ : Continuous χ)
  (e : coefficientCharacterRep χ ≃+ galoisRootOfUnityRepresentation (K := K) (Ω := Ω) q)
  (heρ : ∀ g a, e ((coefficientCharacterRep χ).ρ g a) =
    (galoisRootOfUnityRepresentation (K := K) (Ω := Ω) q).ρ g (e a))
  [TopologicalSpace (galoisRootOfUnityRepresentation (K := K) (Ω := Ω) q)]
  [DiscreteTopology (galoisRootOfUnityRepresentation (K := K) (Ω := Ω) q)]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits K Ω)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K Ω)]

/-- The original local character H2 has a prime-field linear coordinate given
by the actual root identification and the normalized original local invariant. -/
def localCharacterLineH2ScalarEquiv :
    ContinuousRepresentationH2 (coefficientCharacterRep χ)
      (coefficientCharacterAction_continuous χ hχ) ≃ₗ[ZMod q] ZMod q :=
  { (scalarCharacterLineH2RootEquiv K Ω q χ hχ e heρ).trans
      (localFieldRootH2CyclicEquiv K Ω q).toAddEquiv with
    map_smul' := ZMod.map_smul ((scalarCharacterLineH2RootEquiv K Ω q χ hχ e heρ).trans
      (localFieldRootH2CyclicEquiv K Ω q).toAddEquiv) }

/-- The scalar coordinate preserves the original Kummer inclusion and the
full local invariant of the same original continuous H2 class. -/
theorem localCharacterLineH2ScalarEquiv_invariant
    (x : ContinuousRepresentationH2 (coefficientCharacterRep χ)
      (coefficientCharacterAction_continuous χ hχ)) :
    rationalCyclicInvariant q (localCharacterLineH2ScalarEquiv K Ω q χ hχ e heρ x) =
      localFieldContinuousH2InvariantEquiv K Ω
        (galoisKummerH2Inclusion (K := K) (Ω := Ω) q
          (scalarCharacterLineH2RootEquiv K Ω q χ hχ e heρ x)) :=
  localFieldRootH2CyclicEquiv_invariant K Ω q _

variable (A : Rep.{0} (ZMod q) Gal(Ω/K)) [Finite A] [TopologicalSpace A] [DiscreteTopology A]
  [TopologicalSpace (characterDualCoefficientRep A χ)] [DiscreteTopology (characterDualCoefficientRep A χ)]
  (hA : Continuous (fun z : Gal(Ω/K) × A => A.ρ z.1 z.2))

/-- The actual local character-dual cup composed with its original scalar
invariant. Its arguments retain the original continuous cocycle quotients. -/
def localCharacterDualH1ScalarCup :
    ContinuousRepresentationH1 A hA →ₗ[ZMod q]
      ContinuousRepresentationH1 (characterDualCoefficientRep A χ)
        (finiteCharacterDualAction_continuous A χ hA hχ) →ₗ[ZMod q] ZMod q :=
  (continuousCharacterDualH1Cup A χ hχ hA).compr₂
    (localCharacterLineH2ScalarEquiv K Ω q χ hχ e heρ).toLinearMap

/-- The invariant-valued pairing detects exactly the original cup class. -/
theorem localCharacterDualH1ScalarCup_eq_zero_iff
    (x : ContinuousRepresentationH1 A hA)
    (y : ContinuousRepresentationH1 (characterDualCoefficientRep A χ)
      (finiteCharacterDualAction_continuous A χ hA hχ)) :
    localCharacterDualH1ScalarCup K Ω q χ hχ e heρ A hA x y = 0 ↔
      continuousCharacterDualH1Cup A χ hχ hA x y = 0 :=
  (localCharacterLineH2ScalarEquiv K Ω q χ hχ e heρ).map_eq_zero_iff

end
end Dubon2026
