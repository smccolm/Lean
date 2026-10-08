import Dubon2026.PrimitiveHigherTensor
import Dubon2026.PositiveDirichletHalfPlane

/-! # Genuine higher tensor L-series and their even symmetric factors -/

namespace Dubon2026

noncomputable section

/-- The literal higher tensor Dirichlet series equals the finite product of its actual even
symmetric Euler functions in a proved common convergence half-plane. -/
theorem primitiveHigherTensorCoefficient_LSeries {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : PrimitiveCuspForm Q k) (hk : 2 ≤ k) (r : ℕ) {s : ℂ}
    (hs : ((2 * r + (r + 1) ^ 2 + 1 : ℕ) : ℝ) + 1 < s.re) :
    LSeries (primitiveHigherTensorCoefficient f r) s =
      ∏ t ∈ Finset.range (r + 1), primitiveSymmetricLFunction f (2 * t) s := by
  have hs2 : (2 * r : ℕ) < s.re := by
    have hsq : (0 : ℝ) ≤ ((r + 1) ^ 2 : ℕ) := Nat.cast_nonneg _
    push_cast at hs ⊢
    nlinarith
  have hsum : LSeriesSummable (primitiveHigherTensorCoefficient f r) s :=
    LSeriesSummable_of_abscissaOfAbsConv_lt_re
      ((primitiveHigherTensorCoefficient_abscissa_le f hk r).trans_lt (by exact_mod_cast hs))
  have he (p : Nat.Primes) :
      (∑' n : ℕ, PowerSeries.coeff n (spectralFormalEuler Finset.univ (primitiveHigherTensorRoots f r p)) *
        ((((p : ℕ) : ℂ) ^ (-s)) ^ n)) =
      ∏ t ∈ Finset.range (r + 1), primeSpectralEulerFactor (primitiveSymmetricSpectralRoots f (2 * t)) p s := by
    rw [(spectralFormalEuler_evaluation Finset.univ (primitiveHigherTensorRoots f r p)
      (((p : ℕ) : ℂ) ^ (-s)) (fun i _ => spectral_prime_coordinate_lt_one _ (2 * r)
        (primitiveHigherTensor_norm_le f hk r) p i hs2)).2.tsum_eq]
    exact primitiveHigherTensor_euler_factor f r p s
  apply (spectralDirichletCoefficient_hasProd (primitiveHigherTensorRoots f r) hsum).unique
  simp_rw [he]
  apply hasProd_prod
  intro t ht
  apply primitive_higher_symmetric_hasProd_far f hk (2 * t)
  have ht' : t ≤ r := by simpa only [Finset.mem_range, Nat.lt_succ_iff] using ht
  have htR : (t : ℝ) ≤ r := by exact_mod_cast ht'
  push_cast at hs ⊢
  nlinarith [sq_nonneg ((r : ℝ) + 1)]

/-- Holomorphic continuations of the genuine even symmetric powers force the actual
nonnegative tensor Dirichlet series to converge throughout Re(s)>1. The higher analytic
continuations remain explicit inputs. -/
theorem primitiveHigherTensor_abscissa_le_of_even_continuation {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : PrimitiveCuspForm Q k) (hk : 2 ≤ k) (H : ℕ → ℂ → ℂ)
    (hH : ∀ t, DifferentiableOn ℂ (H t) {s : ℂ | 1 < s.re})
    (hmatch : ∀ t, Set.EqOn (H t) (primitiveSymmetricLFunction f (2 * t))
      {s : ℂ | (2 * t : ℕ) + 1 < s.re}) (r : ℕ) :
    LSeries.abscissaOfAbsConv (primitiveHigherTensorCoefficient f r) ≤ (1 : ℝ) := by
  let A : ℝ := ((2 * r + (r + 1) ^ 2 + 1 : ℕ) : ℝ) + 1
  apply positive_dirichlet_abscissa_le_of_holomorphic
    (fun n => primitiveHigherTensorCoefficient_nonneg f r n)
    (F := fun s => ∏ t ∈ Finset.range (r + 1), H t s) (A := A)
  · exact DifferentiableOn.fun_finsetProd (fun t _ => hH t)
  · have hh := primitiveHigherTensorCoefficient_abscissa_le f hk r
    simpa only [A, EReal.coe_add, EReal.coe_one] using hh
  · intro s hs
    rw [primitiveHigherTensorCoefficient_LSeries f hk r hs]
    apply Finset.prod_congr rfl
    intro t ht
    apply hmatch t
    have ht' : t ≤ r := by simpa only [Finset.mem_range, Nat.lt_succ_iff] using ht
    have htR : (t : ℝ) ≤ r := by exact_mod_cast ht'
    dsimp only [Set.mem_setOf_eq, A] at hs ⊢
    push_cast at hs ⊢
    nlinarith [sq_nonneg ((r : ℝ) + 1)]

end
end Dubon2026
