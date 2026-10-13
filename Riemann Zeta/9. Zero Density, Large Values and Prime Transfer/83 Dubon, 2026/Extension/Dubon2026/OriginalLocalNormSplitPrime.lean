import Dubon2026.OriginalLocalNormDegreePowers

/-! # The original local norm is onto at completely split primes

Triviality of the actual prime stabilizer makes the proved norm of an
original base unit equal that unit. This supplies the unrestricted local
condition at the selected split primes in DUB-17's norm-index upper bound.
-/

namespace Dubon2026
noncomputable section
open NumberField IsDedekindDomain
open scoped NumberField Classical
variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [FiniteDimensional K L] [IsGalois K L]

attribute [-instance] UniformSpace.Completion.instSMul in
/-- Triviality of the actual original prime decomposition group makes its actual local norm surjective. -/
theorem originalFiniteLocalNorm_surjective_of_split
    (w : HeightOneSpectrum (𝓞 L)) (hw : OriginalFiniteDecompositionGroup K L w = ⊥) :
    Function.Surjective (originalFiniteLocalNorm K L w) := by
  letI := originalFinitePrimeBelow_liesOver K L w
  have hd : Fintype.card (OriginalFiniteDecompositionGroup K L w) = 1 := by
    rw [← Nat.card_eq_fintype_card, hw]
    exact Nat.card_unique
  intro u
  refine ⟨Units.map (originalAdicBaseChangeMap K L (originalFinitePrimeBelow K L w) w).toMonoidHom u, ?_⟩
  rw [originalFiniteLocalNorm_baseUnit, hd, pow_one]

end
end Dubon2026
