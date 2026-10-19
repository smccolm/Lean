import Dubon2026.AdicRootPowerEvaluation
import Mathlib.RingTheory.MvPowerSeries.Evaluation
import Mathlib.RingTheory.LocalRing.ResidueField.Basic

/-! The actual residue-one auxiliary character differences are
convergent multivariate power-series parameters. This supplies the
evaluation hypothesis for the common parameter algebra in DUB-17's
arithmetic patching dependency. -/

namespace Dubon2026
noncomputable section
open IsLocalRing

/-- A finite family in the maximal ideal is an evaluation family in
the original topology once that topology has been proved maximal-adic. -/
theorem maximalAdic_finiteFamily_hasEval
    {R σ : Type*} [CommRing R] [IsLocalRing R] [TopologicalSpace R] [Finite σ]
    (hR : (inferInstance : TopologicalSpace R) = (maximalIdeal R).adicTopology)
    (x : σ → R) (hx : ∀ s, x s ∈ maximalIdeal R) : MvPowerSeries.HasEval x := by
  have h : @MvPowerSeries.HasEval σ R _ (maximalIdeal R).adicTopology x := by
    letI : WithIdeal R := ⟨maximalIdeal R⟩
    letI : TopologicalSpace R := (maximalIdeal R).adicTopology
    refine ⟨fun s => ?_, ?_⟩
    · have hs := adic_hasEval_of_pow_mem (x s) 1 (by simpa only [pow_one] using hx s)
      exact (PowerSeries.hasEval_def _).mp hs
    · simp only [Filter.cofinite_eq_bot, Filter.tendsto_bot]
  rw [← hR] at h
  exact h

/-- Every scalar difference of the original residue-one character
family is an actual convergent parameter; no analytic bound or extra
continuity condition on the characters is required. -/
theorem auxiliaryCharacterParameters_hasEval
    {R S ι : Type*} [CommRing R] [IsLocalRing R] [TopologicalSpace R]
    [Finite S] [Finite ι] {D : S → Type*} [∀ s, Group (D s)]
    (κ : ∀ s, D s →* (ι → R)ˣ)
    (hκ : ∀ s d i, residue R ((κ s d).val i) = 1)
    (hR : (inferInstance : TopologicalSpace R) = (maximalIdeal R).adicTopology)
    (g : ∀ s, D s) :
    MvPowerSeries.HasEval (fun si : S × ι => ((κ si.1 (g si.1)).val si.2) - 1) := by
  apply maximalAdic_finiteFamily_hasEval hR
  intro si
  apply (residue_eq_zero_iff _).mp
  rw [map_sub, hκ, map_one, sub_self]

end
end Dubon2026
