import Dubon2026.SourceCurveFiberDegrees
import Mathlib.RingTheory.Ideal.Norm.RelNorm

/-! DUB-17/18 -> original Picard Hecke correspondence -> principal-divisor
pushforward -> the actual norm/order identity. Existing prime-place order
and residue-degree comparisons let native Dedekind ideal norms be used
without reconstructing the external valuation and residue dictionaries.
The residue identifications are supplied by the original modular fields.
Adapted from anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2,
S_AlgebraicCurve_Place_ord_norm_eq_sum_fiberOver, DVR and IdealNorm sections.
-/
namespace Dubon2026.SourceCurve.Place
noncomputable section
open IsDedekindDomain IsLocalRing UniqueFactorizationMonoid

theorem ord_coe_of_span_eq_maximal_pow
    {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)
    {r : v.toValuationSubring} {n : ℕ}
    (h : Ideal.span {r} = maximalIdeal v.toValuationSubring ^ n) :
    v.ord (r : F) = n := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
  rw [hπ.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.span_singleton_eq_span_singleton] at h
  obtain ⟨u, hu⟩ := h
  have hr : r = ((u⁻¹ : v.toValuationSubringˣ) : v.toValuationSubring) * π ^ n := by
    rw [mul_comm, Units.eq_mul_inv_iff_mul_eq]
    exact hu
  have hcoe : (r : F) = (((u⁻¹ : v.toValuationSubringˣ) : v.toValuationSubring) : F) *
      (π : F) ^ (n : ℤ) := by
    rw [hr]
    push_cast
    rw [zpow_natCast]
  rw [hcoe, v.ord_unit_smul_zpow u⁻¹ hπ (n : ℤ)]

variable {K F E : Type*} [Field K] [Field F] [Field E]
variable [Algebra K F] [Algebra K E] [Algebra F E] [IsScalarTower K F E]
variable [FiniteDimensional F E] [Algebra.IsSeparable F E]

theorem fiberPrime_count_eq_order (v : Place K F)
    (P : HeightOneSpectrum (integralClosureAt E v))
    {c : integralClosureAt E v} (hc : c ≠ 0) :
    (normalizedFactors (Ideal.span {c})).count P.asIdeal =
      ((fiberPrimePlace E v P).ord (algebraMap (integralClosureAt E v) E c)).toNat := by
  rw [HeightOneSpectrum.count_normalizedFactors_eq_multiplicity (by simpa using hc)]
  rw [show fiberPrimePlace E v P = ofHeightOneSpectrum P from rfl,
    ord_ofHeightOneSpectrum_eq_multiplicity P hc, Int.toNat_natCast]

variable [CharZero F]

theorem relNorm_fiberPrime_eq_maximal (v : Place K F)
    (hbase : Function.Bijective (algebraMap K v.ResidueField))
    (htop : ∀ w : Place K E, Function.Bijective (algebraMap K w.ResidueField))
    (P : HeightOneSpectrum (integralClosureAt E v)) :
    Ideal.relNorm v.toValuationSubring P.asIdeal = maximalIdeal v.toValuationSubring := by
  haveI : CharZero v.toValuationSubring :=
    ⟨fun a b hab => Nat.cast_injective (R := F)
      (by simpa using congrArg (Subtype.val : v.toValuationSubring → F) hab)⟩
  haveI : P.asIdeal.IsMaximal := P.isPrime.isMaximal P.ne_bot
  haveI := fiberPrime_liesOver v P
  rw [Ideal.relNorm_eq_pow_of_isMaximal P.asIdeal (maximalIdeal v.toValuationSubring),
    fiberPrime_inertiaDeg_eq_one v hbase P (htop _), pow_one]

end
end Dubon2026.SourceCurve.Place
