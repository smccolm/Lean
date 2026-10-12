import Dubon2026.ContinuousKummerCarryClass
import Dubon2026.LocalFieldFiniteCyclicCarryInvariant

/-! # The actual absolute cup retains the original finite character carry

The character is inflated through the literal restriction of automorphisms.
The original finite-stage H2 injection detects its vanishing exactly.
-/

namespace Dubon2026
noncomputable section

variable {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω]
  (E : FiniteGaloisIntermediateField K Ω) {n : ℕ} [NeZero n]
  (χ : Gal(E/K) →* Multiplicative (ZMod n))

/-- Inflate the original finite-stage character through actual restriction of
the original absolute Galois automorphisms; continuity is proved. -/
def finiteGaloisCharacterInflation : Gal(Ω/K) →ₜ* Multiplicative (ZMod n) where
  toMonoidHom := χ.comp (AlgEquiv.restrictNormalHom E)
  continuous_toFun :=
    (show Continuous χ from continuous_of_discreteTopology).comp
      (InfiniteGalois.restrictNormalHom_continuous E.toIntermediateField)

variable [TopologicalSpace (Rep.ofAlgebraAutOnUnits K Ω)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K Ω)]

/-- The actual finite-stage carry class inflates to the literal continuous
carry class of the inflated character, with its original base unit unchanged. -/
theorem continuousFiniteCharacterCarryClass_inflation (a : Kˣ) :
    galoisUnitH2FiniteStageMap K Ω E (localFieldFiniteCharacterCarryClass K Ω E χ a) =
      (Submodule.Quotient.mk
        (continuousGaloisCharacterCarryCocycle n (finiteGaloisCharacterInflation E χ) a) :
        GaloisUnitContinuousH2 (K := K) (Ω := Ω)) := by
  letI : TopologicalSpace (Rep.ofAlgebraAutOnUnits K E) := ⊥
  letI : DiscreteTopology (Rep.ofAlgebraAutOnUnits K E) := ⟨rfl⟩
  change galoisUnitFiniteStageH2Inflation E
    (Submodule.Quotient.mk (galoisUnitCharacterCarryCocycle χ a)) = _
  rw [galoisUnitFiniteStageH2Inflation_mk]
  congr 1

variable [IsAlgClosed Ω]
  [TopologicalSpace (galoisRootOfUnityRepresentation (K := K) (Ω := Ω) n)]
  [DiscreteTopology (galoisRootOfUnityRepresentation (K := K) (Ω := Ω) n)]

/-- The actual Kummer cup with an inflated finite character vanishes exactly
when the original finite-stage character carry class vanishes. -/
theorem continuousKummerH1Cup_inflated_eq_zero_iff (a : Kˣ) :
    continuousGaloisRootCharacterH1Cup n (finiteGaloisCharacterInflation E χ)
      (galoisKummerH1Class n a) = 0 ↔
        localFieldFiniteCharacterCarryClass K Ω E χ a = 0 := by
  rw [continuousKummerH1Cup_eq_zero_iff_carry,
    ← continuousFiniteCharacterCarryClass_inflation]
  letI : TopologicalSpace (Rep.ofAlgebraAutOnUnits K E) := ⊥
  letI : DiscreteTopology (Rep.ofAlgebraAutOnUnits K E) := ⟨rfl⟩
  exact galoisUnitFiniteStageH2Inflation_eq_zero_iff E _

end
end Dubon2026
