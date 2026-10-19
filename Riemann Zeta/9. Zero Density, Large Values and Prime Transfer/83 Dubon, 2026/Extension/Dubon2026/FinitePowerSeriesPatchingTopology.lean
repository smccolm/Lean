import Dubon2026.FiniteVariablePowerSeriesNoetherian
import Dubon2026.CompactSeparatedLocalAdicTopology
import Dubon2026.Reuse.Imperial.Patching.Utils.AdicTopology
import Mathlib.RingTheory.AdicCompletion.Noetherian
import Mathlib.RingTheory.MvPowerSeries.PiTopology
import Mathlib.RingTheory.MvPowerSeries.Inverse

/-! The fixed parameter ring meets the ring-topology hypotheses of
the existing generic patching theorem. Reuse finite-variable
Noetherianity and the compact separated local-ring adic theorem;
no new power-series completeness construction is required. -/

namespace Dubon2026
noncomputable section
open IsLocalRing
open scoped MvPowerSeries.WithPiTopology

variable {O η : Type} [CommRing O] [IsLocalRing O] [IsNoetherianRing O]
  [TopologicalSpace O] [IsTopologicalRing O] [CompactSpace O] [T2Space O]
  [Finite η]

omit [CommRing O] [IsLocalRing O] [IsNoetherianRing O] [IsTopologicalRing O]
  [T2Space O] [Finite η] in
/-- The original coefficientwise topology is compact by the product theorem. -/
theorem finitePowerSeries_compactSpace : CompactSpace (MvPowerSeries η O) :=
  inferInstanceAs (CompactSpace ((η →₀ ℕ) → O))

/-- The coefficientwise topology on the actual finite-variable
parameter ring is its maximal-adic topology. -/
theorem finitePowerSeries_isAdic : IsAdic (maximalIdeal (MvPowerSeries η O)) := by
  letI := finiteVariablePowerSeries_isNoetherian (R := O) η
  letI := finitePowerSeries_compactSpace (O := O) (η := η)
  exact compactSeparatedLocalRing_isAdic

/-- The original fixed parameter ring satisfies the exact adic
topology class consumed by the reused patching theorem. -/
theorem finitePowerSeries_isAdicTopology : IsAdicTopology (MvPowerSeries η O) :=
  ⟨finitePowerSeries_isAdic⟩

/-- Compactness in the original coefficientwise topology gives
maximal-adic completeness through the existing patching infrastructure. -/
theorem finitePowerSeries_isAdicComplete :
    IsAdicComplete (maximalIdeal (MvPowerSeries η O)) (MvPowerSeries η O) := by
  letI := finiteVariablePowerSeries_isNoetherian (R := O) η
  letI := finitePowerSeries_compactSpace (O := O) (η := η)
  letI := finitePowerSeries_isAdicTopology (O := O) (η := η)
  exact {}

end
end Dubon2026
