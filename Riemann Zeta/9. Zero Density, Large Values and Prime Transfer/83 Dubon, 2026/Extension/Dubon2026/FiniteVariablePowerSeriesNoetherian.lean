import Dubon2026.PowerSeriesVariableSplitting
import Dubon2026.ResidualRepresentationLocalization
import Mathlib.RingTheory.PowerSeries.Ideal
import Mathlib.RingTheory.MvPowerSeries.Rename
import Mathlib.Data.Fintype.Option

/-! # Noetherianity of actual formal power series in finitely many variables -/

namespace Dubon2026

noncomputable section

variable {R : Type*} [CommRing R] [IsNoetherianRing R]

/-- The actual power series ring in any finite variable type over a Noetherian coefficient ring is Noetherian. -/
theorem finiteVariablePowerSeries_isNoetherian (σ : Type*) [Finite σ] :
    IsNoetherianRing (MvPowerSeries σ R) := by
  apply Finite.induction_empty_option
    (P := fun τ => IsNoetherianRing (MvPowerSeries τ R))
  · intro α β e hα
    letI := hα
    exact isNoetherianRing_of_ringEquiv (MvPowerSeries α R)
      (MvPowerSeries.renameEquiv R e).toRingEquiv
  · exact isNoetherianRing_of_surjective R (MvPowerSeries PEmpty R)
      MvPowerSeries.C MvPowerSeries.C_surjective
  · intro α _ hα
    letI := hα
    let e : Option α ≃ Unit ⊕ α :=
      (Equiv.optionEquivSumPUnit α : Option α ≃ α ⊕ PUnit.{1}).trans
        ((Equiv.sumComm α PUnit.{1}).trans
          (Equiv.sumCongr (Equiv.ofUnique PUnit.{1} Unit) (Equiv.refl α)))
    let split : MvPowerSeries (Option α) R ≃+* PowerSeries (MvPowerSeries α R) :=
      (MvPowerSeries.renameEquiv R e).toRingEquiv.trans splitPowerSeriesVariablesEquiv
    exact isNoetherianRing_of_ringEquiv (PowerSeries (MvPowerSeries α R)) split.symm

variable {G ι O : Type*} [Group G] [Fintype ι] [DecidableEq ι]
  [CommRing O] [IsLocalRing O] [Group.FG G] [IsNoetherianRing O]

/-- In particular, finite-variable formal series over the genuine original residual local ring are Noetherian. -/
theorem residualRepresentationLocalPowerSeries_isNoetherian
    (ρ : G →* Matrix.GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (σ : Type*) [Finite σ] :
    IsNoetherianRing (MvPowerSeries σ (ResidualRepresentationLocalRing ρ)) := by
  letI := residualRepresentationLocalRing_isNoetherian ρ
  exact finiteVariablePowerSeries_isNoetherian (R := ResidualRepresentationLocalRing ρ) σ

end
end Dubon2026
