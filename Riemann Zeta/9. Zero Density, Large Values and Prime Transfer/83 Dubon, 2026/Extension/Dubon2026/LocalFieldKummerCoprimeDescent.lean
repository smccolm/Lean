import Dubon2026.GaloisRootCupCorestriction
import Dubon2026.LocalFieldRootCorestrictionInjection
import Dubon2026.LocalFieldKummerRootNondegeneracy

/-! # Descending the actual Kummer annihilator across a coprime local extension

The primitive-root hypothesis is required only over the actual extension.
The base conclusion follows from genuine H1 restriction, H2 corestriction and cup.
-/

namespace Dubon2026
noncomputable section

variable (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω] [IsAlgClosed Ω]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  (E : IntermediateField K Ω) [FiniteDimensional K E]
  [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
  [(ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation E)]
  (n : ℕ) [NeZero n]
  [TopologicalSpace (galoisRootOfUnityRepresentation (K := K) (Ω := Ω) n)]
  [DiscreteTopology (galoisRootOfUnityRepresentation (K := K) (Ω := Ω) n)]
  [tUnits : TopologicalSpace (Rep.ofAlgebraAutOnUnits K Ω)]
  [dUnits : DiscreteTopology (Rep.ofAlgebraAutOnUnits K Ω)]

/-- Derive Galoisness above the actual intermediate field from the original Galois extension. -/
local instance rootDescentIsGalois : IsGalois E Ω := IsGalois.tower_top_of_isGalois K E Ω
/-- Reuse the original root coefficient topology on the same roots over the finite base. -/
local instance rootDescentStageTopology : TopologicalSpace (galoisRootOfUnityRepresentation (K := E) (Ω := Ω) n) :=
  inferInstanceAs (TopologicalSpace (galoisRootOfUnityRepresentation (K := K) (Ω := Ω) n))
/-- The unchanged original root coefficient topology remains discrete. -/
local instance rootDescentStageDiscrete : DiscreteTopology (galoisRootOfUnityRepresentation (K := E) (Ω := Ω) n) :=
  inferInstanceAs (DiscreteTopology (galoisRootOfUnityRepresentation (K := K) (Ω := Ω) n))
/-- Reuse the original unit coefficient topology on the same units over the finite base. -/
local instance rootDescentUnitTopology : TopologicalSpace (Rep.ofAlgebraAutOnUnits E Ω) :=
  inferInstanceAs (TopologicalSpace (Rep.ofAlgebraAutOnUnits K Ω))
/-- The unchanged original unit coefficient topology remains discrete. -/
local instance rootDescentUnitDiscrete : DiscreteTopology (Rep.ofAlgebraAutOnUnits E Ω) :=
  inferInstanceAs (DiscreteTopology (Rep.ofAlgebraAutOnUnits K Ω))

/-- The actual base root H1 annihilator vanishes when an actual finite local
extension of coprime degree contains the primitive root. The actual cup projection
formula and the proved two kernels discharge the entire descent implication. -/
theorem localFieldKummer_root_annihilator_coprime_descent
    (hn : n.Coprime (Module.finrank K E)) {ζ : E} (hζ : IsPrimitiveRoot ζ n)
    (x : GaloisRootContinuousH1 (K := K) (Ω := Ω) n)
    (hx : ∀ χ : Gal(Ω/K) →ₜ* Multiplicative (ZMod n),
      continuousGaloisRootCharacterH1Cup n χ x = 0) : x = 0 := by
  apply galoisRootContinuousRestriction_coprime_zero K Ω E n hn x
  apply localFieldKummer_root_eq_zero_of_cup_zero E Ω hζ
  intro χ
  apply localFieldRootContinuousCorestriction_injective K Ω E n
  obtain ⟨ψ, hψ⟩ := galoisRootCharacterCup_corestriction K Ω E n χ
  exact (hψ x).trans ((hx ψ).trans (map_zero (galoisRootContinuousCorestriction K Ω E n)).symm)

end
end Dubon2026
