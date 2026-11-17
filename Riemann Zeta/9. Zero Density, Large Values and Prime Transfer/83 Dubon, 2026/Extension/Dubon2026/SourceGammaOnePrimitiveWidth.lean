import Dubon2026.SourceGammaOnePrimitiveCuspBoundary

/-! DUB-17/18 -> original all-weight characteristic-zero association ->
arithmetic realization of the exact joint operator character -> primitive
boundary Frobenius formula. The primitive cusp return time divides the
original level, so every good Hecke prime is coprime to it. This is the
specific input needed to compute the one- and prime-length cusp orbits.
Native principal-congruence normality and minimal-period divisibility are
reused; no boundary representation or Frobenius identity is assumed. -/
namespace Dubon2026.SourceFunctionField.GammaOne
noncomputable section
open CongruenceSubgroup
open scoped MatrixGroups

/-- Every actual primitive Gamma1 cusp return time divides the original level. -/
theorem primitiveCuspWidth_dvd_level (M : ℕ) (q : SL(2, ℤ) ⧸ Gamma1 M) :
    primitiveCuspWidth M q ∣ M := by
  have hT : ModularGroup.T ^ M ∈ Gamma M := by
    simpa only [zpow_natCast] using
      ModularGroup_T_pow_mem_Gamma (M : ℤ) (M : ℤ) dvd_rfl
  have hc : q.out⁻¹ * ModularGroup.T ^ M * q.out ∈ Gamma1 M := by
    have hg : q.out⁻¹ * ModularGroup.T ^ M * q.out ∈ Gamma M := by
      simpa only [inv_inv] using (Gamma_normal M).conj_mem _ hT q.out⁻¹
    obtain ⟨ha, _, hc, hd⟩ := Gamma_mem.mp hg
    exact (Gamma1_mem M _).mpr ⟨ha, hd, hc⟩
  apply MulAction.pow_smul_eq_iff_minimalPeriod_dvd.mp
  change ModularGroup.T ^ M • q = q
  conv_rhs => rw [← Quotient.out_eq' q]
  conv_lhs => rw [← Quotient.out_eq' q]
  change ((ModularGroup.T ^ M * q.out : SL(2, ℤ)) : SL(2, ℤ) ⧸ Gamma1 M) =
    (q.out : SL(2, ℤ) ⧸ Gamma1 M)
  apply QuotientGroup.eq.mpr
  simpa only [mul_inv_rev, inv_inv, mul_assoc] using (Gamma1 M).inv_mem hc

/-- At every good prime the actual primitive cusp width is prime to that prime. -/
theorem primitiveCuspWidth_coprime_good_prime (M : ℕ)
    (q : SL(2, ℤ) ⧸ Gamma1 M) (ell : sourceBinaryHeckePrime M) :
    Nat.Coprime ell.val (primitiveCuspWidth M q) :=
  ell.property.2.of_dvd_right (primitiveCuspWidth_dvd_level M q)

end
end Dubon2026.SourceFunctionField.GammaOne
