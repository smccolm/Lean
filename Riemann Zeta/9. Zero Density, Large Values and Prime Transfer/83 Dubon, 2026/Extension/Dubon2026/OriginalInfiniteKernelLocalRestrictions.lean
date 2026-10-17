import Dubon2026.OriginalInfiniteKernelLocalNormalization
import Dubon2026.OriginalCanonicalClassLocalRestrictions
import Dubon2026.OriginalCanonicalLocalClassNormalization
import Dubon2026.OriginalClassH2InvariantFromGenerator

/-! # One original global class with normalized local restrictions

Select the reciprocal-degree value in the proved invariant image. The
restriction-index law gives the reciprocal decomposition degree at every
prime. Injectivity identifies that restriction with the actual local-class
image already normalized by the same invariant system. This is DUB-17's
finite-stage local fundamental-class compatibility, retaining one global
class for all primes.
-/
namespace Dubon2026
noncomputable section
open CategoryTheory
open scoped NumberField
attribute [local instance 1100] AddCommGroup.toAddCommMonoid Rep.hV2

variable (K L : Type) [Field K] [Field L] [NumberField L]
  [Algebra K L] [FiniteDimensional K L] [IsGalois K L]

omit [NumberField L] in
private theorem index_reciprocal (S : Subgroup Gal(L/K)) :
    S.index • (↑((1 : ℚ) / Module.finrank K L) : AddCircle (1 : ℚ)) =
      ↑((1 : ℚ) / Nat.card S) := by
  rw [← AddCircle.coe_nsmul, nsmul_eq_mul]
  congr 1
  have hd : Module.finrank K L = Nat.card S * S.index :=
    (IsGalois.card_aut_eq_finrank K L).symm.trans S.card_mul_index.symm
  have hs0 : (Nat.card S : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  have hi0 : (S.index : ℚ) ≠ 0 := by
    apply Nat.cast_ne_zero.mpr
    intro hz
    rw [hz, mul_zero] at hd
    exact (Module.finrank_pos (R := K) (M := L)).ne' hd
  rw [hd]
  push_cast
  field_simp

/-- The same canonical invariant system and proved joint normalizations construct one full-order original global class whose actual restrictions are all the normalized local-class images. -/
theorem originalIdeleClass_exists_normalized_local_restrictions_of_infinite_kernel
    (localInvariant : IsDedekindDomain.HeightOneSpectrum (𝓞 L) →
      groupCohomology (originalFullIdeleRep K L) 2 →+ AddCircle (1 : ℚ))
    (total : groupCohomology (originalFullIdeleRep K L) 2 →+ AddCircle (1 : ℚ))
    (hc : OriginalInfiniteKernelClassInvariantTraceSystem K L total)
    (hn : ∀ w, OriginalLocalTraceJointNormalization K L w (localInvariant w) total) :
    OriginalNormalizedLocalRestrictions K L localInvariant := by
  letI : Fact (0 < (1 : ℚ)) := ⟨by norm_num⟩
  let z : AddCircle (1 : ℚ) := ↑((1 : ℚ) / Module.finrank K L)
  have ho : addOrderOf z = Module.finrank K L :=
    AddCircle.addOrderOf_period_div (Module.finrank_pos (R := K) (M := L))
  obtain ⟨invG, hiG, hrG, ht, hs⟩ := hc
  have hz : z ∈ invG.range := (hrG z).mpr (by rw [← ho]; exact addOrderOf_nsmul_eq_zero z)
  obtain ⟨u, hu⟩ := hz
  refine ⟨u, ?_, fun w => ?_⟩
  · exact (addOrderOf_injective invG hiG u).symm.trans ((congrArg addOrderOf hu).trans ho)
  · letI : Fintype (Gal(L/K) ⧸ OriginalFiniteDecompositionGroup K L w) := Fintype.ofFinite _
    obtain ⟨invD, hiD, _, hres, htrace⟩ := hs (OriginalFiniteDecompositionGroup K L w)
    obtain ⟨y, hl, hy⟩ := originalIdeleClass_local_normalization_of_infinite_kernel
      K L w (localInvariant w) total invG invD ht htrace (hn w)
    refine ⟨y, hl, hiD ?_⟩
    exact (hres u).trans ((congrArg (fun t =>
      (OriginalFiniteDecompositionGroup K L w).index • t) hu).trans
        ((index_reciprocal K L (OriginalFiniteDecompositionGroup K L w)).trans hy.symm))

end
end Dubon2026
