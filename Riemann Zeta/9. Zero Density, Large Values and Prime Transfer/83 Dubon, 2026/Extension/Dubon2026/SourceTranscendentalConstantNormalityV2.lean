import Dubon2026.SourceTranscendentalConstantAlgebraV2

/-! DUB-17/18 -> original all-weight arithmetic association -> actual
Gamma1 character realization -> differential/cusp comparison -> rational
Fourier spanning -> integral base change of Fricke fractions. This is the
transcendental constant-adjoining step of the finite constant-list induction.
Native integral closure and polynomial normality recover integral coefficients
after clearing scalar denominators. The original finite generator integrality
and j transcendence are explicit inputs, supplied later by the actual Fricke field.
Adapted from anthropics/fermats-last-theorem,
6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0,
S_IsIntegral_mem_span_of_adjoin_simple_constants_transcendental.
All source proof-limit settings are omitted; native limits are unchanged. -/
namespace Dubon2026.SourceFricke.ConstantDescent
noncomputable section
open Polynomial
open scoped IntermediateField IntermediateField.algebraAdjoinAdjoin
/-- Normality recovers a ring element from an integral element of the evaluation fraction field. -/
theorem mem_range_of_fraction_monic_relation
    {R L : Type*} [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [Field L]
    (f : R →+* L) (hf : Function.Injective f)
    {x : L} (hx : x ∈ (IsFractionRing.lift (K := FractionRing R) hf).fieldRange)
    (n : ℕ) (b : ℕ → R)
    (hrel : x ^ n + ∑ k ∈ Finset.range n, f (b k) * x ^ k = 0) : x ∈ Set.range f := by
  let ψ : FractionRing R →+* L := IsFractionRing.lift hf
  have hψalg : ∀ a : R, ψ (algebraMap R (FractionRing R) a) = f a :=
    fun a => IsFractionRing.lift_algebraMap _ _
  obtain ⟨m, hm⟩ := RingHom.mem_fieldRange.mp hx
  change ψ m = x at hm
  have hmrel : m ^ n + ∑ k ∈ Finset.range n, algebraMap R (FractionRing R) (b k) * m ^ k = 0 := by
    apply ψ.injective
    rw [map_add, map_pow, map_sum, map_zero, hm]
    simp only [map_mul, map_pow, hψalg, hm]
    exact hrel
  have hmint : IsIntegral R m := by
    refine ⟨Polynomial.X ^ n + ∑ k ∈ Finset.range n, Polynomial.C (b k) * Polynomial.X ^ k,
      ?_, ?_⟩
    · exact Polynomial.monic_X_pow_add ((Polynomial.degree_sum_le _ _).trans_lt
        ((Finset.sup_lt_iff (WithBot.bot_lt_coe n)).mpr fun k hk =>
          (Polynomial.degree_C_mul_X_pow_le _ _).trans_lt
            (WithBot.coe_lt_coe.mpr (Finset.mem_range.mp hk))))
    · simp only [Polynomial.eval₂_add, Polynomial.eval₂_pow, Polynomial.eval₂_X,
        Polynomial.eval₂_finsetSum, Polynomial.eval₂_mul, Polynomial.eval₂_C]
      exact hmrel
  obtain ⟨a, ha⟩ := IsIntegrallyClosed.isIntegral_iff.mp hmint
  exact ⟨a, by rw [← hψalg, ha]; exact hm⟩

end
end Dubon2026.SourceFricke.ConstantDescent
