import Dubon2026.PrincipalSupportDecomposition
import Dubon2026.CuspSparseOldspace
import Dubon2026.HeckeAllIndices

/-! # Coprime Fourier support forces genuine oldspace membership at every positive level -/

namespace Dubon2026

open Matrix.SpecialLinearGroup CongruenceSubgroup
open scoped MatrixGroups

noncomputable section
attribute [local instance] principalNormal
attribute [local instance] primeFactorBaseNeZero primeFactorLevelNeZero primeFactorLowerFintype

/-- Average into the common invariant range and descend to an actual Gamma0 cusp form. -/
def principalCommonGamma0Projection (N : ℕ) [NeZero N] (k : ℤ)
    (f : CuspForm ((Gamma N).map (mapGL ℝ)) k) :
    principalCuspOrbit N k f →ₗ[ℂ] CuspForm ((Gamma0 N).map (mapGL ℝ)) k :=
  (principalCommonToGamma0 N k f).comp (principalCommonLowerProjection N k f).rangeRestrict

/-- On the common invariant range the descent retains exactly the principal Fourier coefficients. -/
theorem principalCommonGamma0Projection_coeff (N : ℕ) [NeZero N] (k : ℤ)
    (f : CuspForm ((Gamma N).map (mapGL ℝ)) k) (v : principalCuspOrbit N k f)
    (hv : v ∈ LinearMap.range (principalCommonLowerProjection N k f)) (n : ℕ) :
    cuspCoefficients (principalCommonGamma0Projection N k f v) n = principalCuspCoefficients v.val n := by
  have hfix : principalCommonLowerProjection N k f v = v := by
    obtain ⟨w, rfl⟩ := hv
    exact LinearMap.congr_fun (principalCommonLowerProjection_idempotent N k f) w
  change cuspCoefficients (principalCommonToGamma0 N k f _) n = _
  rw [principalCommonToGamma0_coeff]
  change principalCuspCoefficients (principalCommonLowerProjection N k f v).val n = _
  rw [hfix]

/-- The original rescaled source descends back to exactly the given Gamma0 cusp form. -/
theorem principalCommonGamma0Projection_rescaled (N : ℕ) [NeZero N] (k : ℤ)
    (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k) :
    principalCommonGamma0Projection N k (cuspRescaledPrincipal N k f)
      ⟨cuspRescaledPrincipal N k f, mem_principalCuspOrbit N k _⟩ = f := by
  apply cuspCoefficients_injective N k
  funext n
  rw [principalCommonGamma0Projection_coeff N k _ _
    ⟨_, principalCommonLowerProjection_rescaled_fixed N k f⟩ n, cuspRescaledPrincipal_coeff]

/-- Each prime-supported component in the common range descends to a genuine oldform. -/
theorem principalCommonGamma0Projection_prime_old (N : ℕ) [NeZero N] (k : ℤ)
    (f : CuspForm ((Gamma N).map (mapGL ℝ)) k) (p : N.primeFactors)
    (v : principalCuspOrbit N k f)
    (hv : v ∈ LinearMap.ker (1 - principalOrbitPrimeProjection N k f p) ⊓
      LinearMap.range (principalCommonLowerProjection N k f)) :
    principalCommonGamma0Projection N k f v ∈ cuspOldspace N k := by
  apply cusp_sparse_mem_oldspace (Nat.dvd_of_mem_primeFactors p.property)
    (Nat.prime_of_mem_primeFactors p.property).one_lt k
  intro n hn
  rw [principalCommonGamma0Projection_coeff N k f v hv.2]
  have hfix : principalOrbitPrimeProjection N k f p v = v := by
    have h := hv.1
    change v - principalOrbitPrimeProjection N k f p v = 0 at h
    exact (sub_eq_zero.mp h).symm
  have hc := principalOrbitDivisorProjection_coeff (Nat.dvd_of_mem_primeFactors p.property) k f v n
  change principalCuspCoefficients (principalOrbitPrimeProjection N k f p v).val n = _ at hc
  rw [hfix, if_neg hn] at hc
  exact hc

/-- The full Atkin-Lehner coprime-support implication for actual cusp forms at every positive level. -/
theorem cusp_coprime_support_old (N : ℕ) [NeZero N] (k : ℤ)
    (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k)
    (hf : ∀ n, N.Coprime n → cuspCoefficients f n = 0) : f ∈ cuspOldspace N k := by
  let F := cuspRescaledPrincipal N k f
  let v : principalCuspOrbit N k F := ⟨F, mem_principalCuspOrbit N k F⟩
  have hv : v ∈ LinearMap.range (principalCommonLowerProjection N k F) :=
    ⟨v, principalCommonLowerProjection_rescaled_fixed N k f⟩
  have hd := principalCoprime_support_decomposition N k F v hv (by
    intro n hn
    change principalCuspCoefficients (cuspRescaledPrincipal N k f) n = 0
    rw [cuspRescaledPrincipal_coeff]
    exact hf n hn)
  have hle : (⨆ p : N.primeFactors, LinearMap.ker (1 - principalOrbitPrimeProjection N k F p) ⊓
      LinearMap.range (principalCommonLowerProjection N k F)) ≤
        (cuspOldspace N k).comap (principalCommonGamma0Projection N k F) := by
    apply iSup_le
    intro p w hw
    exact principalCommonGamma0Projection_prime_old N k F p w hw
  have hout := hle hd
  change principalCommonGamma0Projection N k (cuspRescaledPrincipal N k f)
    ⟨cuspRescaledPrincipal N k f, mem_principalCuspOrbit N k _⟩ ∈ cuspOldspace N k at hout
  rwa [principalCommonGamma0Projection_rescaled] at hout

/-- A genuine newspace vector at any positive level is determined by its coprime Fourier coefficients. -/
theorem cusp_new_coprime_eq_zero (N : ℕ) [NeZero N] (k : ℤ)
    (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k) (hnew : f ∈ cuspNewspace N k)
    (hf : ∀ n, N.Coprime n → cuspCoefficients f n = 0) : f = 0 :=
  Submodule.disjoint_def.mp (cuspOldspace_disjoint_newspace N k) f
    (cusp_coprime_support_old N k f hf) hnew

/-- Two actual newspace forms with the same coprime coefficients are equal at every positive level. -/
theorem cusp_new_eq_of_coprime_coefficients (N : ℕ) [NeZero N] (k : ℤ)
    (f g : CuspForm ((Gamma0 N).map (mapGL ℝ)) k)
    (hf : f ∈ cuspNewspace N k) (hg : g ∈ cuspNewspace N k)
    (hfg : ∀ n, N.Coprime n → cuspCoefficients f n = cuspCoefficients g n) : f = g := by
  apply sub_eq_zero.mp
  apply cusp_new_coprime_eq_zero N k (f - g) ((cuspNewspace N k).sub_mem hf hg)
  intro n hn
  change cuspCoefficientLinear N k n (f - g) = 0
  rw [map_sub]
  exact sub_eq_zero.mpr (hfg n hn)

end
end Dubon2026
