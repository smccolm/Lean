import Dubon2026.ContinuousFaithfulCyclicFactor
import Dubon2026.LocalFieldFiniteCyclicReciprocity

/-! # Every original nontrivial finite character has a nonzero local Kummer cup

The faithful cyclic fixed field, existing cyclic reciprocity surjectivity and
literal cup/carry comparison discharge the character-side nondegeneracy.
Finite-module local perfectness still requires the remaining duality steps.
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

/-- Every nontrivial actual continuous finite character detects a Kummer class
of an actual base unit under the original continuous cohomology cup. -/
theorem localFieldKummer_characterCup_exists_nonzero
    (χ : Gal(Ω/K) →ₜ* Multiplicative (ZMod n)) (hχ : χ ≠ 1) :
    ∃ a : Kˣ, continuousGaloisRootCharacterH1Cup n χ
      (galoisKummerH1Class n a) ≠ 0 := by
  obtain ⟨F, ψ, hi, hfactor⟩ := continuousGaloisCharacter_faithful_cyclic_factor χ
  haveI : IsCyclic Gal(F/K) := isCyclic_of_injective ψ hi
  have hψ : ψ ≠ 1 := by
    intro h
    apply hχ
    rw [← hfactor, h]
    ext g
    rfl
  obtain ⟨σ, hσ⟩ : ∃ σ : Gal(F/K), ψ σ ≠ 1 := by
    by_contra h
    apply hψ
    ext σ
    exact not_exists_not.mp h σ
  obtain ⟨u, hu⟩ := localFieldFiniteCyclicReciprocity_surjective K Ω F (Additive.ofMul σ)
  refine ⟨u.toMul, ?_⟩
  intro hz
  rw [← hfactor] at hz
  have hcarry := (continuousKummerH1Cup_inflated_eq_zero_iff F ψ u.toMul).mp hz
  have hinv := localFieldFiniteCyclicReciprocity_character K Ω F ψ u.toMul
  rw [hcarry, map_zero] at hinv
  change 0 = rationalCyclicInvariant n
    (ψ (localFieldFiniteCyclicReciprocity K Ω F u).toMul).toAdd at hinv
  rw [hu] at hinv
  have hzero : rationalCyclicInvariant n (ψ σ).toAdd = rationalCyclicInvariant n 0 :=
    hinv.symm.trans (map_zero _).symm
  exact hσ (Multiplicative.toAdd.injective ((rationalCyclicInvariant_injective n) hzero))

/-- An actual finite character annihilating every original root H1 class is
trivial. This is one side of nondegeneracy for the genuine local cup pairing. -/
theorem localFieldKummer_character_eq_one_of_cup_zero
    (χ : Gal(Ω/K) →ₜ* Multiplicative (ZMod n))
    (h : ∀ x : GaloisRootContinuousH1 (K := K) (Ω := Ω) n,
      continuousGaloisRootCharacterH1Cup n χ x = 0) : χ = 1 := by
  by_contra hχ
  obtain ⟨a, ha⟩ := localFieldKummer_characterCup_exists_nonzero K Ω n χ hχ
  exact ha (h (galoisKummerH1Class n a))

end
end Dubon2026
