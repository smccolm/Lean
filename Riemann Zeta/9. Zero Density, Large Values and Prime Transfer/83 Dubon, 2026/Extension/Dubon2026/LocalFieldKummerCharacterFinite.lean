import Dubon2026.ContinuousKummerCharacterPairing
import Dubon2026.LocalFieldKummerCharacterNondegeneracy
import Dubon2026.LocalFieldKummerH1Finite
import Dubon2026.LocalFieldRootH2Invariant

/-! # The actual local finite-character dual map is injective and finite

These consequences use the proved original cup nondegeneracy, finite Kummer H1
and finite original H2 target. No reciprocity isomorphism is postulated.
-/

namespace Dubon2026
noncomputable section

variable (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω] [IsAlgClosed Ω]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  (n : ℕ) [NeZero n]
  [TopologicalSpace (galoisRootOfUnityRepresentation (K := K) (Ω := Ω) n)]
  [DiscreteTopology (galoisRootOfUnityRepresentation (K := K) (Ω := Ω) n)]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits K Ω)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K Ω)]

/-- Two original continuous finite characters inducing the same actual
Kummer cup functional are equal, by the proved character-side annihilator. -/
theorem localFieldKummerCharacterPairing_right_injective :
    Function.Injective (continuousKummerCharacterPairing (K := K) (Ω := Ω) n).flip := by
  intro χ ψ h
  have hz : (χ - ψ).toMul = 1 := by
    apply localFieldKummer_character_eq_one_of_cup_zero K Ω n
    intro x
    change (continuousKummerCharacterPairing n).flip (χ - ψ) x = 0
    rw [map_sub, LinearMap.sub_apply]
    exact sub_eq_zero.mpr (DFunLike.congr_fun h x)
  exact sub_eq_zero.mp hz

/-- The original continuous finite-character group is finite when n is
nonzero in the original local field. The proof injects it into actual
functionals between the already proved finite H1 and H2 groups. -/
theorem localField_continuousFiniteCharacters_finite (hn : (n : K) ≠ 0) :
    Finite (Gal(Ω/K) →ₜ* Multiplicative (ZMod n)) := by
  haveI := localFieldKummerH1_finite K Ω n hn
  haveI : Finite (GaloisRootContinuousH2 (K := K) (Ω := Ω) n) :=
    Finite.of_equiv (ZMod n) (localFieldRootH2CyclicEquiv K Ω n).symm.toEquiv
  haveI : Finite (GaloisRootContinuousH1 (K := K) (Ω := Ω) n →ₗ[ℤ]
      GaloisRootContinuousH2 (K := K) (Ω := Ω) n) :=
    Finite.of_injective DFunLike.coe DFunLike.coe_injective
  exact Finite.of_injective (continuousKummerCharacterPairing (K := K) (Ω := Ω) n).flip
    (localFieldKummerCharacterPairing_right_injective K Ω n)

end
end Dubon2026
