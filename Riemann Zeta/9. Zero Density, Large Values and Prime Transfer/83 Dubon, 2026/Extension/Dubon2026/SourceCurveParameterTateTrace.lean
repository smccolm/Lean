import Dubon2026.SourceCurveParameterResidue
import Dubon2026.SourceCurveLocalRetractionTrace
import Dubon2026.SourceCurveFiniteRankTraceOne

/-! The actual Tate trace against any specified order-one parameter is
its simple-pole coefficient. Reuse the proved independence of the integral
retraction and the rank-one trace formula. This supplies the characteristic-
free rational-coordinate residue normalization needed for DUB-17/18. -/

noncomputable section

namespace Dubon2026.SourceCurve.Place

open ResidueTrace

variable {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)

/-- The original Tate residue against a specified parameter is its actual simple-pole coefficient. -/
theorem tateResidue_parameter {t : F} (ht : v.ord t = 1)
    (hres : Function.Surjective (algebraMap K v.ResidueField)) (f : F) :
    v.tateResidue f t = v.parameterResidueScalar t f := by
  let r := v.parameterIntegralRetraction ht hres
  let A := projectedEnd v.integralFunctions r (Algebra.lmul K F f)
  let B := projectedEnd v.integralFunctions r (Algebra.lmul K F t)
  let χ : v.integralFunctions →ₗ[K] K :=
    v.parameterResidueScalar t ∘ₗ Algebra.lmul K F f ∘ₗ v.integralFunctions.subtype
  let e : v.integralFunctions := ⟨1, one_mem v.toValuationSubring⟩
  have htmem : t ∈ v.toValuationSubring := v.mem_of_ord_nonneg (by omega)
  have hcomm : A ∘ₗ B - B ∘ₗ A = χ.smulRight e := by
    apply LinearMap.ext
    intro a
    apply Subtype.ext
    change v.parameterProj t (f * v.parameterProj t (t * (a : F))) -
      v.parameterProj t (t * v.parameterProj t (f * (a : F))) =
        v.parameterResidueScalar t (f * (a : F)) • (1 : F)
    rw [v.parameterProj_of_mem t (mul_mem htmem a.2), mul_left_comm f t,
      ← map_sub, ← mul_sub]
    have hp : f * (a : F) - v.parameterProj t (f * (a : F)) =
        v.parameterPrincipalPart t (f * (a : F)) := by
      change f * (a : F) - (f * (a : F) - v.parameterPrincipalPart t (f * (a : F))) = _
      abel
    rw [hp, v.parameterProj_mul_principalPart ht, Algebra.smul_def, mul_one]
  obtain ⟨_, htrace⟩ := v.tateResidue_eq_retraction_trace hres r
    (v.parameterIntegralRetraction_apply ht hres) f t htmem
  change v.tateResidue f t = finrankTrace (A ∘ₗ B - B ∘ₗ A) at htrace
  rw [htrace, hcomm, finrankTrace_smulRight]
  change v.parameterResidueScalar t (f * 1) = v.parameterResidueScalar t f
  rw [mul_one]

/-- The actual parameter residue of each pure negative power, with no characteristic restriction. -/
theorem tateResidue_parameter_neg_pow {t : F} (ht : v.ord t = 1)
    (hres : Function.Surjective (algebraMap K v.ResidueField)) (n : ℕ) :
    v.tateResidue (t ^ (-(n + 1 : ℤ))) t = if n = 0 then 1 else 0 := by
  rw [v.tateResidue_parameter ht hres, v.parameterResidueScalar_neg_pow ht]

/-- Nonnegative powers contribute no residue against the actual parameter. -/
theorem tateResidue_parameter_nat_pow {t : F} (ht : v.ord t = 1)
    (hres : Function.Surjective (algebraMap K v.ResidueField)) (n : ℕ) :
    v.tateResidue (t ^ n) t = 0 := by
  rw [v.tateResidue_parameter ht hres]
  exact v.parameterResidueScalar_of_mem t (pow_mem (v.mem_of_ord_nonneg (by omega)) n)

/-- All integer powers have their exact residue against the specified parameter. -/
theorem tateResidue_parameter_zpow {t : F} (ht : v.ord t = 1)
    (hres : Function.Surjective (algebraMap K v.ResidueField)) (n : ℤ) :
    v.tateResidue (t ^ n) t = if n = -1 then 1 else 0 := by
  cases n with
  | ofNat n =>
      rw [Int.ofNat_eq_natCast, zpow_natCast, v.tateResidue_parameter_nat_pow ht hres]
      simp
  | negSucc n =>
      rw [Int.negSucc_eq, v.tateResidue_parameter_neg_pow ht hres]
      by_cases hn : n = 0
      · subst n
        norm_num
      · rw [if_neg hn, if_neg (by omega)]

end Dubon2026.SourceCurve.Place
