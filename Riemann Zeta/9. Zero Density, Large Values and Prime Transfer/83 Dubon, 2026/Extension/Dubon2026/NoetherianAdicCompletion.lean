import Dubon2026.FiniteVariablePowerSeriesNoetherian
import Dubon2026.CompletedCoefficientSurjectivity
import Dubon2026.CompletedResidualRepresentation
import Mathlib.RingTheory.MvPowerSeries.Equiv

/-! # Noetherianity of the actual original adic completion -/

namespace Dubon2026

noncomputable section

variable {R : Type*} [CommRing R] [IsNoetherianRing R]

/-- The actual completion of a Noetherian ring at any original ideal is Noetherian. -/
theorem noetherianAdicCompletion (I : Ideal R) : IsNoetherianRing (AdicCompletion I R) := by
  classical
  have hI : I.FG := (isNoetherianRing_iff_ideal_fg R).mp inferInstance I
  obtain ⟨s, hs⟩ := hI
  let P := MvPolynomial s R
  let J : Ideal P := MvPolynomial.idealOfVars s R
  let f : P →ₐ[R] R := MvPolynomial.aeval (fun j : s => (j : R))
  have hJI : J.map f.toRingHom = I := by
    have hrange : Set.range (fun j : s => (j : R)) = (s : Set R) := by
      ext x
      simp
    change (MvPolynomial.idealOfVars s R).map f.toRingHom = I
    rw [MvPolynomial.idealOfVars, Ideal.map_span, ← Set.range_comp']
    have heval : (fun j : s => f (MvPolynomial.X j)) = fun j : s => (j : R) := by
      funext j
      exact MvPolynomial.aeval_X (fun j : s => (j : R)) j
    change Ideal.span (Set.range (fun j : s => f (MvPolynomial.X j))) = I
    rw [heval, hrange]
    exact hs
  have hf : J ≤ Ideal.comap f.toRingHom I := Ideal.map_le_iff_le_comap.mp hJI.le
  have hsurj : Function.Surjective f := by
    intro r
    refine ⟨MvPolynomial.C r, ?_⟩
    exact MvPolynomial.aeval_C (fun j : s => (j : R)) r
  letI : IsNoetherianRing (MvPowerSeries s R) := finiteVariablePowerSeries_isNoetherian s
  letI : IsNoetherianRing (AdicCompletion J P) :=
    isNoetherianRing_of_ringEquiv (MvPowerSeries s R)
      (MvPowerSeries.toAdicCompletionAlgEquiv s R).toRingEquiv
  exact isNoetherianRing_of_surjective (AdicCompletion J P) (AdicCompletion I R)
    (adicCoefficientCompletionMap J I f hf).toRingHom
    (adicCoefficientCompletionMap_surjective J (MvPolynomial.idealOfVars_fg s R)
      I ((isNoetherianRing_iff_ideal_fg R).mp inferInstance I) f hf hJI hsurj)

variable {G ι O : Type*} [Group G] [Fintype ι] [DecidableEq ι]
  [CommRing O] [IsLocalRing O] [Group.FG G] [IsNoetherianRing O]

/-- The genuine original residual representation completion is Noetherian under the original abstract finite-generation and coefficient hypotheses. -/
theorem residualRepresentationCompletion_isNoetherian
    (ρ : G →* Matrix.GeneralLinearGroup ι (IsLocalRing.ResidueField O)) :
    IsNoetherianRing (ResidualRepresentationCompletion ρ) := by
  letI := residualRepresentationLocalRing_isNoetherian ρ
  let completedNoetherian := noetherianAdicCompletion (R := ResidualRepresentationLocalRing ρ)
    (RingHom.ker (R := ResidualRepresentationLocalRing ρ)
      (S := IsLocalRing.ResidueField O) (localizedResidualRepresentationEvaluation ρ).toRingHom)
  exact completedNoetherian

end
end Dubon2026
