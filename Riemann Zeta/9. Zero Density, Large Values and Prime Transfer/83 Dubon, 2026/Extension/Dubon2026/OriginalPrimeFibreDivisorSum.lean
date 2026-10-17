import Dubon2026.OriginalPrimeFibreInvariantSum

/-! # Divisor scaling of the actual prime fibre

The required primary order divides the mixed target degree and the auxiliary
degree. Its scaling therefore has integral invariant sum. This supplies the
restriction-vanishing input for DUB-17's mixed-degree class construction.
-/
namespace Dubon2026
noncomputable section
open NumberField IsDedekindDomain
open scoped NumberField

/-- Scaling by the auxiliary degree divided by a divisor of the target degree
kills the sum over the actual original prime fibre. -/
theorem originalFinitePrime_divisor_scaled_sum_zero
    (K E : Type) [Field K] [NumberField K] [Field E] [NumberField E]
    [Algebra K E] [FiniteDimensional K E] [IsGalois K E]
    (v : HeightOneSpectrum (𝓞 K)) (d n : ℕ) (hn : 0 < n)
    (hdn : d ∣ n) (hd : d ∣ Module.finrank K E) :
    (∑ᶠ u : {u : HeightOneSpectrum (𝓞 E) // originalFinitePrimeBelow K E u = v},
      (n / d) • (Nat.card (OriginalFiniteDecompositionGroup K E u.val) •
        (↑((1 : ℚ) / n) : AddCircle (1 : ℚ)))) = 0 := by
  obtain ⟨k, hk⟩ := hd
  have hz : n • (↑((1 : ℚ) / n) : AddCircle (1 : ℚ)) = 0 := by
    simpa only [AddCircle.addOrderOf_period_div hn] using
      addOrderOf_nsmul_eq_zero (↑((1 : ℚ) / n) : AddCircle (1 : ℚ))
  calc
    _ = Module.finrank K E • ((n / d) • (↑((1 : ℚ) / n) : AddCircle (1 : ℚ))) := by
      calc
        _ = ∑ᶠ u : {u : HeightOneSpectrum (𝓞 E) // originalFinitePrimeBelow K E u = v},
            Nat.card (OriginalFiniteDecompositionGroup K E u.val) •
              ((n / d) • (↑((1 : ℚ) / n) : AddCircle (1 : ℚ))) :=
          finsum_congr (fun _ => smul_comm _ _ _)
        _ = _ := originalFinitePrime_finsum_invariant_degree K E v _
    _ = 0 := by
      rw [hk, mul_comm d k, mul_smul, ← mul_smul d, Nat.mul_div_cancel' hdn, hz, smul_zero]

end
end Dubon2026
