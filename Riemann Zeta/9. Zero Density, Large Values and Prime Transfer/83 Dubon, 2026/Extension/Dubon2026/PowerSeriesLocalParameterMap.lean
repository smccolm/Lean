import Dubon2026.FinitePowerSeriesVariableIdeal
import Dubon2026.LocalCoefficientReduction
import Mathlib.RingTheory.MvPowerSeries.Inverse
import Mathlib.RingTheory.LocalRing.RingHom.Basic

/-! Locality of the constructed common parameter action. The original
residue algebra comparison supplies locality of the coefficient map;
the actual character differences supply the maximal-ideal variables. -/

namespace Dubon2026
noncomputable section
open IsLocalRing

/-- The original residue algebra identification makes the coefficient
algebra map local, without a separately supplied locality hypothesis. -/
theorem residueAlgebraEquiv_algebraMap_isLocal
    {O R : Type*} [CommRing O] [IsLocalRing O] [CommRing R] [IsLocalRing R]
    [Algebra O R] (e : ResidueField R ≃ₐ[O] ResidueField O) :
    IsLocalHom (algebraMap O R) := by
  letI : IsLocalHom (residue O) := IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective
  refine ⟨fun x hx => ?_⟩
  have h := hx.map (localCoefficientReduction e).toRingHom
  change IsUnit (localCoefficientReduction e (algebraMap O R x)) at h
  rw [(localCoefficientReduction e).commutes] at h
  exact (isUnit_map_iff (residue O) x).mp h

/-- A finite-variable parameter map is local when its coefficient
map is local and its genuine variable images lie in the maximal ideal. -/
theorem finitePowerSeries_parameterMap_isLocal
    {O R η : Type*} [CommRing O] [IsLocalRing O] [CommRing R] [IsLocalRing R]
    [Algebra O R] [IsLocalHom (algebraMap O R)] [Fintype η]
    (e : MvPowerSeries η O →ₐ[O] R)
    (hvars : ∀ i, e (MvPowerSeries.X i) ∈ maximalIdeal R) :
    IsLocalHom e.toRingHom := by
  have hspan : Ideal.span (Set.range (MvPowerSeries.X (R := O) (σ := η))) ≤
      Ideal.comap e.toRingHom (maximalIdeal R) := by
    apply Ideal.span_le.mpr
    rintro _ ⟨i, rfl⟩
    exact hvars i
  refine ⟨fun f hf => ?_⟩
  by_contra hfu
  have hc : MvPowerSeries.constantCoeff f ∈ maximalIdeal O :=
    fun hu => hfu (MvPowerSeries.isUnit_iff_constantCoeff.mpr hu)
  have hconstant : algebraMap O R (MvPowerSeries.constantCoeff f) ∈ maximalIdeal R :=
    map_nonunit (algebraMap O R) _ hc
  have hdifference := hspan (finitePowerSeries_sub_constant_mem_variableIdeal f)
  change e (f - MvPowerSeries.C (MvPowerSeries.constantCoeff f)) ∈ maximalIdeal R at hdifference
  rw [map_sub, show e (MvPowerSeries.C (MvPowerSeries.constantCoeff f)) =
    algebraMap O R (MvPowerSeries.constantCoeff f) from e.commutes _] at hdifference
  have hmem := (maximalIdeal R).add_mem hdifference hconstant
  rw [sub_add_cancel] at hmem
  exact hmem hf

end
end Dubon2026
