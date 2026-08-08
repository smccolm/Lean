import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Exp

open Complex

example (y : ℝ) : ‖exp (y * I)‖ = 1 := by
  simp
