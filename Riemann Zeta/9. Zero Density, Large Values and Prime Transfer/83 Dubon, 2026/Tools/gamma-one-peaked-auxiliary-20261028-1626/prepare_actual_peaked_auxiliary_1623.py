from pathlib import Path
s=Path(__file__).parent
c=(s/'anthropic-even-integrality-depth-1503/S_ModularCurve_SiegelUnit_exists_gamma1_peaked_auxiliary_form_twelve_dvd.lean.txt').read_text(encoding='utf-8')
a=c.index('theorem solution');b=c.index(' := by',a)
sig=c[a:b].replace('theorem solution','theorem exists_gamma1_peaked_auxiliary_form_twelve_dvd')
header='''import SourcePeakedOrderGapDecay1622a
import SourcePeakedIntegralQExpansion1618b
import SourcePeakedTranslatedIntegralExpansion1620a

/-! DUB-17/18 -> original Gamma1 degree/genus preservation -> level-power
slash integrality -> actual even-weight peaked auxiliary. Consume the proved
separating exponent family, scale it by N, choose a discriminant power and
construct the actual modular form. Its exact integral expansions, nonzero
leading coefficient, level-cleared inverse, strict weight/order gap and
separated cusp decay are derived. No peaked-auxiliary premise remains.
The endpoint is the exact source existential statement. Level scaling avoids
the candidate's additive-orbit divisibility argument; proved nonnegative
shifted cusp orders avoid its unrestricted negative-order machinery.
Adapted from anthropics/fermats-last-theorem, Apache-2.0, revision
6e837e75355538c7f80bab5b956861e86c4eacc2,
S_ModularCurve_SiegelUnit_exists_gamma1_peaked_auxiliary_form_twelve_dvd. -/
namespace Dubon2026.SourceFunctionField.GammaOne.PeakedAuxiliary
noncomputable section
open UpperHalfPlane Filter Topology Construction Coefficients
open scoped MatrixGroups ModularForm

'''
proof=''' := by
  classical
  haveI : NeZero N := ⟨by omega⟩
  obtain ⟨m, A, hm00, htrans, hA, hpos, hsep⟩ := exists_level_multiple_peaked_exponent N hN
  obtain ⟨t, ht⟩ := exists_clearing_discriminant_power N m
  obtain ⟨m₀, hm₀, hweight⟩ := exists_width_one_order N m A hA hpos t
  obtain ⟨ϑ, hϑ, hdec⟩ :=
    Form.exists_modularForm_gamma1_coe_eq_prod_siegelFun_pow_mul_discriminant_pow N m hm00 htrans t
      (fun β => ht ((β 0 0 : ℤ) : ZMod N) ((β 1 0 : ℤ) : ZMod N))
  obtain ⟨a, hz, hne, hinv, hint⟩ :=
    qExpansion_one_coeff_of_coe_eq_prod_siegelFun_pow_mul_discriminant_pow N m hm00 t ϑ hϑ m₀ hm₀
  refine ⟨12 * (t : ℤ), m₀, a, 1 / (N : ℝ), ϑ, dvd_mul_right _ _, hweight, ?_, ?_, hz, hne, hinv, hint, ?_⟩
  · have : (0 : ℝ) < N := Nat.cast_pos.mpr (NeZero.pos N)
    positivity
  · intro n
    have hi := integral_qExpansion_slash_of_nonneg_order N m t ϑ hϑ ModularGroup.S
      (ht ((ModularGroup.S 0 0 : ℤ) : ZMod N) ((ModularGroup.S 1 0 : ℤ) : ZMod N)) n
    have hNi : IsIntegral ℤ (N : ℂ) := by
      exact_mod_cast (isIntegral_algebraMap : IsIntegral ℤ ((N : ℤ) : ℂ))
    exact (hNi.pow a).mul hi
  · intro β hβ hβS
    have hfirst : β ∉ plusMinus (CongruenceSubgroup.Gamma1 N) := by
      simpa only [mem_plusMinus_iff, not_or] using hβ
    have hsecond : ∀ j : ℤ, β * ModularGroup.T ^ j * ModularGroup.S⁻¹ ∉
        plusMinus (CongruenceSubgroup.Gamma1 N) := by
      intro j
      simpa only [mem_plusMinus_iff, not_or] using hβS j
    exact (hdec β).trans (cusp_order_gap_bigO N m t m₀ hm₀
      ((β 0 0 : ℤ) : ZMod N) ((β 1 0 : ℤ) : ZMod N) (hsep β hfirst hsecond))

end
end Dubon2026.SourceFunctionField.GammaOne.PeakedAuxiliary
'''
f=s/'SourceActualPeakedAuxiliary1623a.lean';assert not f.exists();f.write_text(header+sig+proof,encoding='utf-8')
print('Prepared actual source auxiliary assembly with all existence inputs proved.')
