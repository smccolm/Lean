import GafniTao.PintzGaussianKernel

open Complex MeasureTheory

noncomputable def num (lambda : ℝ) (s : ℂ) : ℂ :=
  Complex.exp (s ^ 2 / (lambda : ℂ) + (lambda : ℂ) * s)

example (lambda c t : ℝ) (hlambda : 0 < lambda) :
    ‖num lambda ((c : ℂ) + Complex.I * t)‖ =
      Real.exp ((c ^ 2 - t ^ 2) / lambda + lambda * c) := by
  rw [num, Complex.norm_exp]
  congr 1
  have hlambdaNe : lambda ≠ 0 := ne_of_gt hlambda
  rw [add_re]
  rw [div_re]
  simp [Complex.normSq_apply, pow_two]
  field_simp

#check ContinuousAt.comp
#check ContinuousAt.comp_of_eq
#check DifferentiableAt.isBigO_sub
#check Asymptotics.IsBigO.div
#check Asymptotics.IsBigO.div_isBigO
#check Asymptotics.IsBigOWith.div
#check Asymptotics.IsBigOWith.of_bound
#check Asymptotics.isBigO_iff
#check Asymptotics.isBigO_iff_isBoundedUnder_le
