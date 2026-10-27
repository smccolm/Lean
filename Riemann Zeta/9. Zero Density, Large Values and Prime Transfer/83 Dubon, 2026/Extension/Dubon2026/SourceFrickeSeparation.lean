import Dubon2026.SourceFrickeTorsionLattice
import Dubon2026.SourceFrickePrefactor
import Dubon2026.SourceFrickeFunctionTransformationV2

/-! DUB-17/18 -> original all-weight arithmetic association -> finite
Gamma1 characters -> Picard/H1 and diamond comparison -> differential
realization -> rational Fourier structure -> faithful Fricke generators.
The existing actual period map and exact kernel give separation at a
single point where E4 E6 is nonzero. That point exists by the native
constant Fourier coefficient, without any injectivity assumption. -/
namespace Dubon2026.SourceFricke
noncomputable section
open UpperHalfPlane ModularForm SourceEllipticPeriod
open scoped Manifold MatrixGroups ModularForm PeriodPair

theorem weierstrassP_frickeTorsionPt_eq_imp {N : ℕ} [NeZero N]
    (τ : ℍ) (a b : FrickeIdx N)
    (h : ℘[periodPairOfTau τ] (frickeTorsionPt N a.1 τ) =
      ℘[periodPairOfTau τ] (frickeTorsionPt N b.1 τ)) :
    b.1 = a.1 ∨ b.1 = -a.1 := by
  letI : (periodCurve (periodPairOfTau τ)).IsElliptic := by
    change (periodCurve (Dubon2026.SourceFunctionField.PeriodLattice.ofTau τ)).IsElliptic
    infer_instance
  rcases weierstrassP_eq_imp_lattice (periodPairOfTau τ)
    (frickeTorsionPt_notMem τ a.1 a.2) (frickeTorsionPt_notMem τ b.1 b.2) h with hd | hs
  · exact Or.inl ((frickeTorsionPt_sub_mem_iff τ a.1 b.1).mp hd).symm
  · right
    have he := (frickeTorsionPt_add_mem_iff τ a.1 b.1).mp hs
    simpa only [neg_neg] using (congrArg Neg.neg he).symm

theorem frickeF_eq_imp {N : ℕ} [NeZero N] (a b : FrickeIdx N)
    (h : frickeF N a.1 = frickeF N b.1) : b.1 = a.1 ∨ b.1 = -a.1 := by
  obtain ⟨τ, hτ⟩ := exists_E4E6_ne_zero
  have hp : (2 * (Real.pi : ℂ) * Complex.I) ^ 2 ≠ 0 :=
    pow_ne_zero _ (mul_ne_zero (mul_ne_zero (by norm_num)
      (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) Complex.I_ne_zero)
  apply weierstrassP_frickeTorsionPt_eq_imp τ a b
  have hf := congrFun h τ
  simp only [frickeF, wpNormZ] at hf
  exact mul_left_cancel₀ (inv_ne_zero hp)
    (mul_left_cancel₀ (frickePrefactor_ne_zero hτ) hf)

end
end Dubon2026.SourceFricke
