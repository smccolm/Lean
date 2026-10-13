/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the upstream LICENSE.
Adapted from NYLL ClassFieldTheory, commit dc55774a7fe03e742f2b4c6114aab5e7d01edfb1,
Nyll/ClassFieldTheory/AlgebraicNumberTheory/SUnit/LogLattice.lean.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/
import Dubon2026.SUnitReducedLogarithm
import Mathlib.NumberTheory.NumberField.ProductFormula

/-! # The original S-unit product formula in logarithmic coordinates

The pinned number-field product formula is restricted to the actual
finite support of the original S-unit. Its logarithm puts the original
full logarithmic image in the sum-zero hyperplane required for the
equivariant lattice comparison in DUB-17's Herbrand-quotient argument.
-/

namespace Dubon2026
noncomputable section
open NumberField IsDedekindDomain
open scoped NumberField Classical BigOperators
variable (K : Type*) [Field K] [NumberField K]
  (S : Finset (HeightOneSpectrum (𝓞 K)))

/-- An original S-unit has normalized finite absolute value one outside the original S. -/
theorem sUnit_adicAbv_eq_one_of_not_mem
    (x : (S : Set (HeightOneSpectrum (𝓞 K))).unit K)
    (v : HeightOneSpectrum (𝓞 K)) (hv : v ∉ S) :
    NumberField.HeightOneSpectrum.adicAbv K v x.val.val = 1 := by
  rw [NumberField.HeightOneSpectrum.adicAbv_def, x.property v hv]
  simp

/-- The actual finite part of the original S-unit product formula is the product over its original S. -/
theorem sUnit_finitePlace_finprod
    (x : (S : Set (HeightOneSpectrum (𝓞 K))).unit K) :
    (∏ᶠ w : FinitePlace K, w x.val.val) =
      ∏ v : S, NumberField.HeightOneSpectrum.adicAbv K v.val x.val.val := by
  rw [← finprod_comp_equiv FinitePlace.equivHeightOneSpectrum.symm]
  simp_rw [FinitePlace.equivHeightOneSpectrum_symm_apply, FinitePlace.norm_embedding,
    NumberField.HeightOneSpectrum.adicAbv_def]
  rw [finprod_eq_prod_of_mulSupport_subset (s := S)]
  · exact (Finset.prod_coe_sort (s := S)
      (f := fun v : HeightOneSpectrum (𝓞 K) =>
        NumberField.HeightOneSpectrum.adicAbv K v x.val.val)).symm
  · intro v hv
    by_contra hnot
    apply hv
    simp [x.property v hnot]

/-- The actual original all-place logarithmic coordinates sum to zero. -/
theorem sUnit_sum_log_absoluteValues_eq_zero
    (x : (S : Set (HeightOneSpectrum (𝓞 K))).unit K) :
    (∑ w : InfinitePlace K, w.mult * Real.log (w x.val.val)) +
      ∑ v : S, Real.log (NumberField.HeightOneSpectrum.adicAbv K v.val x.val.val) = 0 := by
  have hx0 : x.val.val ≠ 0 := x.val.ne_zero
  have hprod := NumberField.prod_abs_eq_one hx0
  rw [sUnit_finitePlace_finprod K S x] at hprod
  have hinf : ∀ w : InfinitePlace K, w x.val.val ^ w.mult ≠ 0 :=
    fun w => pow_ne_zero _ ((w.pos_iff.mpr hx0).ne')
  have hf : ∀ v : S, NumberField.HeightOneSpectrum.adicAbv K v.val x.val.val ≠ 0 :=
    fun v => ((NumberField.HeightOneSpectrum.adicAbv K v.val).pos_iff.mpr hx0).ne'
  have hlog := congrArg Real.log hprod
  rw [Real.log_mul (Finset.prod_ne_zero_iff.mpr (fun w _ => hinf w))
    (Finset.prod_ne_zero_iff.mpr (fun v _ => hf v)),
    Real.log_prod (fun w _ => hinf w), Real.log_prod (fun v _ => hf v), Real.log_one] at hlog
  simpa only [Real.log_pow] using hlog

end
end Dubon2026
