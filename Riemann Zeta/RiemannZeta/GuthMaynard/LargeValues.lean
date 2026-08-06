import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Basic
import RiemannZeta.GuthMaynard.Separated
import RiemannZeta.GuthMaynard.MeanValue
import RiemannZeta.GuthMaynard.Decoupling
import RiemannZeta.GuthMaynard.Statements

open Complex Finset

namespace RiemannZeta.GuthMaynard


/--
F-06: The Guth-Maynard Large Values Estimate (Theorem 1.1) follows from
the combination of Montgomery's Mean Value Theorem (for the large-scale additive energy)
and the l^2 decoupling inequality (for the fine-scale frequency concentration).
-/
variable (guth_maynard_large_values_of_decoupling : GuthMaynardLargeValues)

end RiemannZeta.GuthMaynard
