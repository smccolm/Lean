import Dubon2026.OriginalAdicNormGaloisProduct

/-! # Actual local norm preimages of integer units are integer units

The original local norm product and its valuation show that any preimage
of an original base integer unit already has valuation one. Therefore
assembling an original idele norm preimage from prescribed local preimages
requires no extra integral-preimage or unramifiedness hypothesis. This
removes the restricted-product obstacle on DUB-17's norm-index chain.
-/

namespace Dubon2026
noncomputable section
open NumberField IsDedekindDomain
open scoped NumberField Classical WithZero
variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
  (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L)) [w.asIdeal.LiesOver v.asIdeal]

attribute [-instance] UniformSpace.Completion.instSMul in
/-- The valuation of the original completed norm image is the decomposition-degree power of the original valuation. -/
theorem originalAdicNorm_valuation_product :
    letI : Algebra (v.adicCompletion K) (w.adicCompletion L) :=
      (originalAdicBaseChangeMap K L v w).toAlgebra
    ∀ x : w.adicCompletion L,
      Valued.v (originalAdicBaseChangeMap K L v w (Algebra.norm (v.adicCompletion K) x)) =
        (Valued.v x : ℤᵐ⁰) ^ Fintype.card (OriginalFiniteDecompositionGroup K L w) := by
  letI : Algebra (v.adicCompletion K) (w.adicCompletion L) :=
    (originalAdicBaseChangeMap K L v w).toAlgebra
  intro x
  rw [originalAdicNorm_galois_product, map_prod]
  simp_rw [numberFieldGaloisLocalTransport_valuation]
  rw [Finset.prod_const, Finset.card_univ]

attribute [-instance] UniformSpace.Completion.instSMul in
/-- Every actual local norm preimage of an original base integer unit is itself an original integer unit. -/
theorem originalAdicNorm_preimage_integerUnit :
    letI : Algebra (v.adicCompletion K) (w.adicCompletion L) :=
      (originalAdicBaseChangeMap K L v w).toAlgebra
    ∀ u : (w.adicCompletion L)ˣ,
      Units.map (Algebra.norm (v.adicCompletion K) (S := w.adicCompletion L)) u ∈
        (v.adicCompletionIntegers K).units → u ∈ (w.adicCompletionIntegers L).units := by
  letI : Algebra (v.adicCompletion K) (w.adicCompletion L) :=
    (originalAdicBaseChangeMap K L v w).toAlgebra
  intro u hu
  rw [HeightOneSpectrum.adicCompletionIntegers.mem_units_iff_valued_eq_one] at hu ⊢
  change Valued.v (Algebra.norm (v.adicCompletion K) u.val) = 1 at hu
  have hv := originalAdicNorm_valuation_product K L v w u.val
  rw [originalAdicBaseChangeMap_valuation, hu, one_pow] at hv
  exact (pow_eq_one_iff_of_nonneg zero_le Fintype.card_ne_zero).mp hv.symm

end
end Dubon2026
