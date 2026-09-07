import GafniTao.FordFiniteZetaEndpoint
import Mathlib.NumberTheory.LSeries.HurwitzZeta

#check HurwitzZeta.hurwitzZeta
#check UnitAddCircle
#check Nat.floor_pos
#check Nat.floor_le
#check Complex.norm_add_le
#check norm_sub_le
#check Complex.ofReal_cpow
#check Real.norm_eq_abs
#check norm_cpow_eq_rpow_re_of_pos

open Complex HurwitzZeta

#check (hurwitzZeta (0 : UnitAddCircle) (2 : ℂ))
#check (hurwitzZeta ((1 / 2 : ℝ) : UnitAddCircle) (2 : ℂ))
