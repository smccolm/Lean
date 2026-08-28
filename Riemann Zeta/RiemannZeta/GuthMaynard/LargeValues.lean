import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Basic
import RiemannZeta.GuthMaynard.Separated
import RiemannZeta.GuthMaynard.MeanValue
import RiemannZeta.GuthMaynard.LargeValuesDefinitions
import RiemannZeta.GuthMaynard.LargeValuesMatrix
import RiemannZeta.GuthMaynard.TraceDispersion
import RiemannZeta.GuthMaynard.LargeValuesCubic
import RiemannZeta.GuthMaynard.LargeValuesS3Refined
import RiemannZeta.GuthMaynard.Statements
import RiemannZeta.GuthMaynard.HeathBrownReflection
import RiemannZeta.GuthMaynard.LargeValuesEnergy

open Complex Finset

namespace RiemannZeta.GuthMaynard


/-!
The rejected parabola-decoupling model has been removed.  The imported modules
now provide the source cutoff, sampling matrix, exact Gram kernel, positive
Gram spectrum, the complete cubic Poisson split, Proposition 5.1 for `S₁`,
and sixth-moment dispersion reduction.  The exact finite Heath--Brown
difference expansion and coefficient-majorant bridge are also proved.  The
Section 11 consumers and the final assembly remain open, so this module does
not claim `GuthMaynardLargeValues`.
-/

end RiemannZeta.GuthMaynard
