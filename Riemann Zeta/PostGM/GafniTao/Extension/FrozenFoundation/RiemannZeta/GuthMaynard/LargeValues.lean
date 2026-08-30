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
import RiemannZeta.GuthMaynard.LargeValuesFinal

open Complex Finset

namespace RiemannZeta.GuthMaynard


/-!
The rejected parabola-decoupling model has been removed.  The imported modules
provide the source cutoff and localization, sampling matrix, trace reduction,
Poisson and smooth-reflection estimates, the `S₁`/`S₂`/`S₃` estimates,
the native Heath--Brown difference-set theorem, the Section 11 energy bound,
and the exact Sections 3 and 12 assembly.  In particular,
`guthMaynardLargeValues_native` proves `GuthMaynardLargeValues` from these
kernel-checked inputs.
-/

end RiemannZeta.GuthMaynard
