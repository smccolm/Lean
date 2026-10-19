import Dubon2026.FinitePowerSeriesVariableIdeal
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-! The augmentation comparison respects the common power-series
algebra, acting on the base ring through constant coefficients. This
discharges the scalar compatibility in the ring comparison required by
the existing generic patching theorem for DUB-17. -/

namespace Dubon2026
noncomputable section

variable {η O R A : Type*} [Fintype η] [CommRing O]
  [CommRing R] [Algebra O R] [CommRing A] [Algebra O A]

/-- After quotienting by the image of the variable ideal, the actual
parameter action is precisely the original constant-coefficient action. -/
theorem powerSeriesAugmentationQuotient_constantCoeff
    (e : MvPowerSeries η O →ₐ[O] R) (f : MvPowerSeries η O) :
    Ideal.Quotient.mk
      (Ideal.map e.toRingHom (Ideal.span (Set.range (MvPowerSeries.X (R := O) (σ := η)))))
      (e f) = algebraMap O
        (R ⧸ Ideal.map e.toRingHom
          (Ideal.span (Set.range (MvPowerSeries.X (R := O) (σ := η)))))
        (MvPowerSeries.constantCoeff f) := by
  let J := Ideal.map e.toRingHom
    (Ideal.span (Set.range (MvPowerSeries.X (R := O) (σ := η))))
  have hmem : e (f - MvPowerSeries.C (MvPowerSeries.constantCoeff f)) ∈ J :=
    Ideal.mem_map_of_mem e.toRingHom (finitePowerSeries_sub_constant_mem_variableIdeal f)
  have hzero := Ideal.Quotient.eq_zero_iff_mem.mpr hmem
  rw [map_sub, map_sub] at hzero
  have heC : e (MvPowerSeries.C (MvPowerSeries.constantCoeff f)) =
      algebraMap O R (MvPowerSeries.constantCoeff f) := e.commutes _
  rw [heC] at hzero
  exact sub_eq_zero.mp hzero

/-- Upgrade the same original coefficient-ring isomorphism to an
isomorphism over the common power-series algebra. Its base-ring action
is constructed from constant coefficients, without an assumed scalar
compatibility certificate. -/
def powerSeriesAugmentationQuotientEquivOverParameters
    (e : MvPowerSeries η O →ₐ[O] R)
    (c : (R ⧸ Ideal.map e.toRingHom
      (Ideal.span (Set.range (MvPowerSeries.X (R := O) (σ := η))))) ≃ₐ[O] A) :
    letI : Algebra (MvPowerSeries η O) R := e.toAlgebra
    letI : Algebra (MvPowerSeries η O) A :=
      ((algebraMap O A).comp MvPowerSeries.constantCoeff).toAlgebra
    (R ⧸ Ideal.map e.toRingHom
      (Ideal.span (Set.range (MvPowerSeries.X (R := O) (σ := η))))) ≃ₐ[MvPowerSeries η O] A := by
  letI : Algebra (MvPowerSeries η O) R := e.toAlgebra
  letI : Algebra (MvPowerSeries η O) A :=
    ((algebraMap O A).comp MvPowerSeries.constantCoeff).toAlgebra
  exact
    { c.toRingEquiv with
      commutes' := fun f => by
        change c (Ideal.Quotient.mk _ (e f)) = algebraMap O A (MvPowerSeries.constantCoeff f)
        rw [powerSeriesAugmentationQuotient_constantCoeff]
        exact c.commutes _ }

end
end Dubon2026
