import Dubon2026.OriginalPrimeFibreDegree
import Mathlib.Topology.Instances.AddCircle.Defs

/-! # The original prime-fibre factor in the auxiliary invariant sum

Sum the proved decomposition degrees over the actual primes, then apply
the exact auxiliary scaling. When the target degree divides the auxiliary
degree, the normalized reciprocal-degree contribution vanishes. This is
the numerical part of DUB-17's auxiliary-class restriction; identifying
the canonical arithmetic coordinates remains a separate obligation.
-/
namespace Dubon2026
noncomputable section
open NumberField IsDedekindDomain
open scoped NumberField Classical
variable (K E : Type) [Field K] [NumberField K] [Field E] [NumberField E]
  [Algebra K E] [FiniteDimensional K E] [IsGalois K E]

/-- The weighted sum over the actual original prime fibre has the original global-degree factor. -/
theorem originalFinitePrime_finsum_invariant_degree
    (v : HeightOneSpectrum (𝓞 K)) (z : AddCircle (1 : ℚ)) :
    (∑ᶠ u : {u : HeightOneSpectrum (𝓞 E) // originalFinitePrimeBelow K E u = v},
      Nat.card (OriginalFiniteDecompositionGroup K E u.val) • z) = Module.finrank K E • z := by
  have hf : Set.Finite {u : HeightOneSpectrum (𝓞 E) | originalFinitePrimeBelow K E u = v} := by
    simpa only [Set.mem_singleton_iff] using
      originalFinitePrimeBelow_preimage_finite K E {v} (Set.finite_singleton v)
  letI : Fintype {u : HeightOneSpectrum (𝓞 E) // originalFinitePrimeBelow K E u = v} := hf.fintype
  rw [finsum_eq_sum_of_fintype, Finset.sum_nsmul_assoc,
    ← finsum_eq_sum_of_fintype, originalFinitePrime_finsum_decomposition_card]

/-- The actual prime-fibre total of the scaled reciprocal auxiliary degree vanishes when the original target degree divides the auxiliary degree. -/
theorem originalFinitePrime_scaled_auxiliary_sum_zero
    (v : HeightOneSpectrum (𝓞 K)) (n : ℕ) (hn : 0 < n) (hd : Module.finrank K E ∣ n) :
    (∑ᶠ u : {u : HeightOneSpectrum (𝓞 E) // originalFinitePrimeBelow K E u = v},
      (n / Module.finrank K E) •
        (Nat.card (OriginalFiniteDecompositionGroup K E u.val) •
          (↑((1 : ℚ) / n) : AddCircle (1 : ℚ)))) = 0 := by
  calc
    _ = ∑ᶠ u : {u : HeightOneSpectrum (𝓞 E) // originalFinitePrimeBelow K E u = v},
        Nat.card (OriginalFiniteDecompositionGroup K E u.val) •
          ((n / Module.finrank K E) • (↑((1 : ℚ) / n) : AddCircle (1 : ℚ))) := by
      apply finsum_congr
      intro u
      exact smul_comm _ _ _
    _ = Module.finrank K E •
        ((n / Module.finrank K E) • (↑((1 : ℚ) / n) : AddCircle (1 : ℚ))) :=
      originalFinitePrime_finsum_invariant_degree K E v _
    _ = n • (↑((1 : ℚ) / n) : AddCircle (1 : ℚ)) := by
      rw [← mul_smul, Nat.mul_div_cancel' hd]
    _ = 0 := by
      simpa only [AddCircle.addOrderOf_period_div hn] using
        addOrderOf_nsmul_eq_zero (↑((1 : ℚ) / n) : AddCircle (1 : ℚ))

end
end Dubon2026
