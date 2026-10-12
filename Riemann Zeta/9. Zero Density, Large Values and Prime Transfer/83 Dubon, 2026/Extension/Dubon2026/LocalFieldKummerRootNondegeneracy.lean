import Dubon2026.BasePrimitiveRootCupSkew
import Dubon2026.LocalFieldKummerCharacterNondegeneracy

/-! # Root-side local Kummer nondegeneracy over a base primitive root

The actual character-side result and the original cup skew symmetry supply the
opposite annihilator statement. Finiteness, descent without base roots and full
finite-module local duality remain separate obligations toward DUB-17.
-/

namespace Dubon2026
noncomputable section

variable (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω] [IsAlgClosed Ω]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  {n : ℕ} [NeZero n] {ζ : K} (hζ : IsPrimitiveRoot ζ n)
  [TopologicalSpace (galoisRootOfUnityRepresentation (K := K) (Ω := Ω) n)]
  [DiscreteTopology (galoisRootOfUnityRepresentation (K := K) (Ω := Ω) n)]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits K Ω)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K Ω)]

include hζ

/-- Every nonzero original root H1 class is detected by an actual continuous
finite character if the original base field contains a primitive root. -/
theorem localFieldKummer_rootCup_exists_nonzero
    (x : GaloisRootContinuousH1 (K := K) (Ω := Ω) n) (hx : x ≠ 0) :
    ∃ χ : Gal(Ω/K) →ₜ* Multiplicative (ZMod n),
      continuousGaloisRootCharacterH1Cup n χ x ≠ 0 := by
  induction x using Submodule.Quotient.induction_on with
  | _ c =>
    have hc : c ≠ 0 := by
      intro h
      apply hx
      rw [h]
      exact map_zero (continuousRepresentationCoboundariesOne
        (galoisRootOfUnityRepresentation (K := K) (Ω := Ω) n)
        (discreteGaloisRootAction_continuous n)).mkQ
    have hχ : basePrimitiveRootCocycleCharacter hζ c ≠ 1 := by
      intro h
      exact hc ((basePrimitiveRootCocycleCharacter_eq_one_iff hζ c).mp h)
    obtain ⟨a, ha⟩ := localFieldKummer_characterCup_exists_nonzero K Ω n
      (basePrimitiveRootCocycleCharacter hζ c) hχ
    let d := galoisRootRadicalOneCocycle n a (galoisKummerRadical (Ω := Ω) n a)
      (galoisKummerRadical_pow n a)
    have hd : (Submodule.Quotient.mk d : GaloisRootContinuousH1 (K := K) (Ω := Ω) n) =
        galoisKummerH1Class n a := rfl
    refine ⟨basePrimitiveRootCocycleCharacter hζ d, ?_⟩
    intro hz
    have hs := basePrimitiveRootCocycleCup_swap_add hζ c d
    rw [hz, add_zero, hd] at hs
    exact ha hs

/-- Over an original base primitive root, a class annihilated by every actual
finite character is zero in the original continuous root H1 quotient. -/
theorem localFieldKummer_root_eq_zero_of_cup_zero
    (x : GaloisRootContinuousH1 (K := K) (Ω := Ω) n)
    (h : ∀ χ : Gal(Ω/K) →ₜ* Multiplicative (ZMod n),
      continuousGaloisRootCharacterH1Cup n χ x = 0) : x = 0 := by
  by_contra hx
  obtain ⟨χ, hχ⟩ := localFieldKummer_rootCup_exists_nonzero K Ω hζ x hx
  exact hχ (h χ)

end
end Dubon2026
