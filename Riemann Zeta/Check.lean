import RiemannZeta.GuthMaynard.DFIBesselMellin
#check MeasureTheory.Integrable.mono'
#check MeasureTheory.Integrable.congr
#check integrable_congr_iff
#check Real.rpow_add
#check Real.one_rpow
#check DifferentiableAt.const_cpow
#check DifferentiableAt.cpow_const
#check Complex.mul_cpow
#check Complex.mul_cpow_ofReal_nonneg
#check Complex.arg_real_mul
#check Complex.arg_neg_I
#check Complex.continuousAt_cpow_const
#check Complex.cpow_def_of_ne_zero
#check Complex.log_def
#check Complex.norm_real_mul
#check Complex.continuousAt_cpow_const
#check Complex.continuousAt_ofReal_cpow_const
#check continuousAt_cpow_const
#check Complex.inv_I
#check inv_I
#check Complex.I_mul_I
#check integral_image_eq_integral_abs_deriv_smul
#check Complex.cpow_nat_mul'
#check Complex.natCast_cpow
#check Real.strictMono_tanh
#check strictMono_tanh
#check Real.rpow_le_one
import RiemannZeta.GuthMaynard.DFIDivisorEpsilon

example (q : ℕ) [NeZero q] (z : ℤ) :
    Nat.gcd ((z : ZMod q).val) q = z.gcd q := by
  rw [← Int.gcd_emod z q, ← ZMod.val_intCast]
  rfl
