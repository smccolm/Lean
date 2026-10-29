from pathlib import Path
s=Path(__file__).parent
old=s/'SourcePeakedExponents1550a.lean'
assert not old.with_suffix('.lean.txt').exists()
t=old.read_text(encoding='utf-8')
t=t.replace('intro h; apply h01; have := congrArg Neg.neg h; simpa using this','exact (neg_ne_zero.mpr (one_ne_zero : (1 : ZMod N) ≠ 0)).symm')
t=t.replace('ZMod.card, smul_eq_mul, nsmul_eq_mul','ZMod.card, nsmul_eq_mul')
old.rename(old.with_suffix('.lean.txt'))
f=s/'SourcePeakedExponents1550b.lean';assert not f.exists();f.write_text(t,encoding='utf-8')
f=s/'SourceGammaOnePeakedCuspOrders1551a.lean';assert not f.exists()
f.write_text('''import SourcePeakedExponents1550b
import SourceGammaOnePeakedCuspClasses1534a
import Dubon2026.SourceGammaOnePlusMinus

/-! DUB-17/18 -> original Gamma1 degree preservation -> level-power
slash integrality -> actual even-weight peaked auxiliary. Consume the
constructed exponent family on the actual first columns of SL(2,Z).
The determinant supplies primitivity and the proved cusp classification
turns the exact signed Gamma1 exclusions into Bernoulli order separation.
No primitive-column or separating-exponent premise remains. The analytic
Siegel-product construction and its expansions are still required. -/
namespace Dubon2026.SourceFunctionField.GammaOne.PeakedAuxiliary
open Finset
open scoped MatrixGroups

theorem exists_peaked_exponent_on_actual_cusps
    (N : ℕ) [NeZero N] (hN : 2 ≤ N) :
    ∃ (m : ZMod N → ZMod N → ℕ) (Ord : ZMod N → ZMod N → ℤ),
      (∀ x y : ZMod N, Ord x y =
        ∑ r : ZMod N, ∑ s : ZMod N, (m r s : ℤ) *
          Bernoulli.wt N (r * x + s * y).val) ∧
      m 0 0 = 0 ∧
      (∀ r s : ZMod N, m r (s + r) = m r s) ∧
      0 < Ord 1 0 ∧
      ∀ β : SL(2, ℤ), β ∉ plusMinus (CongruenceSubgroup.Gamma1 N) →
        (∀ j : ℤ, β * ModularGroup.T ^ j * ModularGroup.S⁻¹ ∉
          plusMinus (CongruenceSubgroup.Gamma1 N)) →
        Ord 1 0 < Ord ((β 0 0 : ℤ) : ZMod N) ((β 1 0 : ℤ) : ZMod N) := by
  obtain ⟨m, Ord, hOrd, hzero, htrans, hpos, hsep⟩ := Exponents.exists_peaked_exponent N hN
  refine ⟨m, Ord, hOrd, hzero, htrans, hpos, ?_⟩
  intro β hβ hβS
  obtain ⟨hfirst, hsecond, hprim⟩ := gammaOne_peaked_cusp_classes N β
  apply hsep _ _ hprim
  · intro h
    exact hβ ((mem_plusMinus_iff _ _).mpr (hfirst.mpr h))
  · intro h
    obtain ⟨j, hj⟩ := hsecond.mpr h
    exact hβS j ((mem_plusMinus_iff _ _).mpr hj)

end Dubon2026.SourceFunctionField.GammaOne.PeakedAuxiliary
''',encoding='utf-8')
