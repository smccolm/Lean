import Mathlib.FieldTheory.RatFunc.Basic
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Theorems.Thm_AlgebraicCurve_RationalFunctionField_deg_eq_one_of_forall_ne_ofHeightOneSpectrum
import Theorems.Thm_AlgebraicCurve_RationalFunctionField_deg_ofHeightOneSpectrum
import P2M.Util
namespace P2MW.S_AlgebraicCurve_RationalFunctionField_deg_ne_zero
attribute [-instance] AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation
attribute [-simp] AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint

open AlgebraicCurve IsDedekindDomain Polynomial

theorem solution {K : Type*} [Field K] (v : Place K (RatFunc K)) : v.deg ≠ 0 := by
  by_cases h : ∀ w : HeightOneSpectrum K[X], v ≠ Place.ofHeightOneSpectrum w
  · rw [RationalFunctionField.deg_eq_one_of_forall_ne_ofHeightOneSpectrum v h]
    exact one_ne_zero
  · obtain ⟨w, hw⟩ : ∃ w : HeightOneSpectrum K[X], v = Place.ofHeightOneSpectrum w := by
      simpa using h
    subst hw
    obtain ⟨p, hp⟩ := Submodule.IsPrincipal.principal w.asIdeal
    rw [RationalFunctionField.deg_ofHeightOneSpectrum K hp]
    have hp0 : p ≠ 0 := by
      intro h0
      apply w.ne_bot
      rw [hp, h0]
      exact Ideal.span_singleton_eq_bot.mpr rfl
    have hprime : Prime p := by
      have hpr := w.isPrime
      rw [hp] at hpr
      exact (Ideal.span_singleton_prime hp0).mp hpr
    exact (natDegree_pos_iff_degree_pos.mpr (degree_pos_of_irreducible hprime.irreducible)).ne'
