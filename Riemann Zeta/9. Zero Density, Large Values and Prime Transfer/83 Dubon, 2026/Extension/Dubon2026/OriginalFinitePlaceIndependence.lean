/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the upstream LICENSE.
Adapted from ClassFieldTheory commit dc55774a7fe03e742f2b4c6114aab5e7d01edfb1,
Nyll/ClassFieldTheory/AlgebraicNumberTheory/RayClass/Ideal.lean.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/
import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
import Mathlib.Analysis.AbsoluteValue.Equivalence

/-! # Independent original finite places

These are the nontriviality and independence hypotheses of the pinned
approximation theorem. Simultaneous approximation is needed to identify
the actual decomposition-group fixed completion with the original base
completion, and hence the native norm quotient on DUB-17's duality route.
-/

namespace Dubon2026
noncomputable section
open NumberField IsDedekindDomain
open scoped NumberField
variable (K : Type) [Field K] [NumberField K]

/-- An original finite-place absolute value is nontrivial. -/
theorem original_adicAbv_isNontrivial
    (v : HeightOneSpectrum (𝓞 K)) :
    (NumberField.HeightOneSpectrum.adicAbv K v).IsNontrivial := by
  obtain ⟨x, hxv, hx0⟩ :=
    Submodule.exists_mem_ne_zero_of_ne_bot v.ne_bot
  refine ⟨algebraMap (𝓞 K) K x, ?_, ?_⟩
  · exact (FaithfulSMul.algebraMap_eq_zero_iff (𝓞 K) K).not.mpr hx0
  · apply ne_of_lt
    rw [← FinitePlace.norm_embedding]
    exact (FinitePlace.norm_lt_one_iff_mem (K := K) v x).2 hxv

/-- Distinct original finite places have inequivalent absolute values. -/
theorem original_adicAbv_not_isEquiv_of_ne
    {v w : HeightOneSpectrum (𝓞 K)} (hvw : v ≠ w) :
    ¬ (NumberField.HeightOneSpectrum.adicAbv K v).IsEquiv
      (NumberField.HeightOneSpectrum.adicAbv K w) := by
  intro h
  have hnotle : ¬ v.asIdeal ≤ w.asIdeal := by
    intro hvw_le
    have htop_le : (⊤ : Ideal (𝓞 K)) ≤ w.asIdeal := by
      rw [← (v.isCoprime_of_ne w hvw).sup_eq]
      exact sup_le hvw_le le_rfl
    exact w.isPrime.ne_top (top_unique htop_le)
  obtain ⟨x, hxv, hxw⟩ := Set.not_subset.mp hnotle
  have hvlt :
      NumberField.HeightOneSpectrum.adicAbv K v
        (algebraMap (𝓞 K) K x) < 1 := by
    rw [← FinitePlace.norm_embedding]
    exact (FinitePlace.norm_lt_one_iff_mem (K := K) v x).2 hxv
  have hweq :
      NumberField.HeightOneSpectrum.adicAbv K w
        (algebraMap (𝓞 K) K x) = 1 := by
    rw [← FinitePlace.norm_embedding]
    exact (FinitePlace.norm_eq_one_iff_notMem (K := K) w x).2 hxw
  exact (ne_of_lt hvlt) (h.eq_one_iff.mpr hweq)


end
end Dubon2026
