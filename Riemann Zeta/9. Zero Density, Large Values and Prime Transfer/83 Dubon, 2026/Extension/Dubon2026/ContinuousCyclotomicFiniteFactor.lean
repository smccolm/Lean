import Dubon2026.ContinuousGaloisFiniteFactors
import Dubon2026.PrimitiveRootCyclotomicContinuity

/-! The actual finite Galois factor for DUB-17 auxiliary primes must contain
the prescribed roots of unity as well as the residual representation.
Native continuity and finite factorization supply both in a single field. -/

namespace Dubon2026
noncomputable section

variable {K Ω T : Type} [Field K] [Field Ω] [Algebra K Ω]
  [IsGalois K Ω] [Group T] [TopologicalSpace T] [DiscreteTopology T]

/-- Factor the original continuous representation through an actual finite
Galois field containing the specified primitive root. The root membership is
proved from the cyclotomic character and Galois correspondence. -/
theorem continuous_galois_finite_factor_with_root
    (χ : Gal(Ω/K) →ₜ* T) {m : ℕ} [NeZero m]
    {ζ : Ω} (hζ : IsPrimitiveRoot ζ m) :
    ∃ F : FiniteGaloisIntermediateField K Ω, ζ ∈ F.toIntermediateField ∧
      ∃ ψ : Gal(F/K) →* T,
        ∀ g : Gal(Ω/K), ψ (AlgEquiv.restrictNormalHom F g) = χ g := by
  let γ : Gal(Ω/K) →ₜ* (ZMod m)ˣ :=
    ⟨hζ.autToPow K, primitiveRootCyclotomicCharacter_continuous hζ⟩
  obtain ⟨F, φ, hφ⟩ := continuous_galois_finite_factor (χ.prod γ)
  have hmem : ζ ∈ F.toIntermediateField := by
    rw [← InfiniteGalois.fixedField_fixingSubgroup F.toIntermediateField,
      IntermediateField.mem_fixedField_iff]
    intro g hg
    have hg1 : AlgEquiv.restrictNormalHom F g = 1 := by
      change g ∈ (AlgEquiv.restrictNormalHom F).ker
      rwa [IntermediateField.restrictNormalHom_ker]
    have hγ : γ g = 1 := by
      have he := congrArg Prod.snd (hφ g)
      rw [hg1, map_one] at he
      exact he.symm
    have he : hζ.autToPow K g = hζ.autToPow K 1 :=
      hγ.trans (map_one _).symm
    rw [← hζ.autToPow_spec K g, he, hζ.autToPow_spec K 1]
    rfl
  refine ⟨F, hmem, (MonoidHom.fst T ((ZMod m)ˣ)).comp φ, ?_⟩
  intro g
  exact congrArg Prod.fst (hφ g)

end
end Dubon2026
