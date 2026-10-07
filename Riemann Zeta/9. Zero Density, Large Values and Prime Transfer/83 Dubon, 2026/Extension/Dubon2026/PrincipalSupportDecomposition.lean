import Dubon2026.PrincipalOrbitCoprime

/-! # The coprime-support decomposition on the actual principal cusp orbit -/

namespace Dubon2026

open Matrix.SpecialLinearGroup CongruenceSubgroup
open scoped MatrixGroups

noncomputable section
attribute [local instance] principalNormal
attribute [local instance] primeFactorBaseNeZero primeFactorLevelNeZero primeFactorLowerFintype

/-- Actual common-invariant orbit vectors with zero coprime coefficients split into prime-supported
components inside that same genuine common invariant range. -/
theorem principalCoprime_support_decomposition (N : ℕ) [NeZero N] (k : ℤ)
    (f : CuspForm ((Gamma N).map (mapGL ℝ)) k) (v : principalCuspOrbit N k f)
    (hcommon : v ∈ LinearMap.range (principalCommonLowerProjection N k f))
    (hcoeff : ∀ n, N.Coprime n → principalCuspCoefficients v.val n = 0) :
    v ∈ ⨆ p : N.primeFactors, LinearMap.ker (1 - principalOrbitPrimeProjection N k f p) ⊓
      LinearMap.range (principalCommonLowerProjection N k f) := by
  obtain ⟨c, he, hp⟩ := principalLowerDivisor_commonCore N k f
  letI := c
  letI := InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℂ) (F := principalCuspOrbit N k f)
  letI := InnerProductSpace.ofCore c.toCore
  have hee : Set.Pairwise (↑(Finset.univ : Finset N.primeFactors))
      (fun p q => Commute (principalLowerProjection N k f p) (principalLowerProjection N k f q)) :=
    fun p _ q _ hpq => principalLowerProjection_commute N k f p q hpq
  have hpp : Set.Pairwise (↑(Finset.univ : Finset N.primeFactors))
      (fun p q => Commute (principalOrbitPrimeProjection N k f p) (principalOrbitPrimeProjection N k f q)) :=
    fun _ _ _ _ _ => principalOrbitDivisorProjection_commute _ _ k f
  have hep : Set.Pairwise (↑(Finset.univ : Finset N.primeFactors))
      (fun p q => Commute (principalLowerProjection N k f p) (principalOrbitPrimeProjection N k f q)) :=
    fun p _ q _ hpq => principalLowerDivisorProjection_cross_commute N k f p q hpq
  have hdec := finite_orthogonal_compression_decomposition Finset.univ
    (principalLowerProjection N k f) (principalOrbitPrimeProjection N k f)
    (fun p _ => ⟨principalLowerProjection_idempotent N k f p, he p⟩)
    (fun p _ => ⟨principalOrbitDivisorProjection_idempotent _ k f,
      hp p.val (Nat.dvd_of_mem_primeFactors p.property)⟩) hee hpp hep
  have hz := principalOrbitAvoidProjection_eq_zero N k f v hcoeff
  have hmem := hdec (show v ∈ LinearMap.ker (Finset.univ.noncommProd
      (fun p => 1 - principalOrbitPrimeProjection N k f p)
      (pairwise_projection_complements Finset.univ (principalOrbitPrimeProjection N k f) hpp)) ⊓
        LinearMap.range (principalCommonLowerProjection N k f) from ⟨hz, hcommon⟩)
  simpa only [Finset.mem_univ, iSup_true] using hmem

end
end Dubon2026
