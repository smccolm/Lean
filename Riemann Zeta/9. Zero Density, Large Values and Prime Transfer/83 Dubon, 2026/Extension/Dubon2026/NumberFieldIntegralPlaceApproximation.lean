/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/

import Dubon2026.NumberFieldIntegralFiniteAdeles
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas

/-! # Integral approximation at finitely many original places

Adapted from TauCetiProject/TauCeti at
51d586d1cdfd170cd66989af5fda3e6a9e07ca4d, AdicValuation/Completion and
AdicValuation/Approximation. The completion argument is shortened to use
open valuation balls directly, and the simultaneous argument reuses the
pinned Dedekind Chinese remainder theorem. This serves DUB-17's actual
adelic lattice local comparison; no broader Henselian infrastructure is
ported.
-/

namespace Dubon2026

noncomputable section

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum WithZero
open scoped NumberField

variable (K : Type*) [Field K] [NumberField K]

/-- A nonzero closed valuation ball is open in an original finite completion. -/
theorem numberFieldAdic_ball_isOpen (v : HeightOneSpectrum (𝓞 K))
    {γ : ℤᵐ⁰} (hγ : γ ≠ 0) :
    IsOpen {z : v.adicCompletion K | Valued.v z ≤ γ} := by
  obtain ⟨z, hz⟩ := v.valuedAdicCompletion_surjective K γ
  have hr0 : Valued.v.restrict z ≠ 0 := by
    rw [ne_eq, Valuation.restrict_eq_zero_iff, hz]
    exact hγ
  have h : {y : v.adicCompletion K | Valued.v y ≤ γ} =
      {y : v.adicCompletion K | Valued.v.restrict y ≤ Valued.v.restrict z} := by
    ext y
    rw [Set.mem_setOf_eq, Set.mem_setOf_eq, Valuation.restrict_le_iff, hz]
  rw [h]
  exact Valued.isOpen_closedBall _ hr0

/-- An original local integer can be approximated by a global algebraic integer to any precision. -/
theorem numberFieldIntegralPlace_approximation (v : HeightOneSpectrum (𝓞 K))
    (x : v.adicCompletionIntegers K) (n : ℕ) :
    ∃ a : 𝓞 K, Valued.v ((x : v.adicCompletion K) -
      algebraMap (𝓞 K) (v.adicCompletion K) a) ≤ exp (-(n : ℤ)) := by
  let U : Set (v.adicCompletion K) := {z | Valued.v ((x : v.adicCompletion K) - z) ≤
    exp (-(n : ℤ))}
  have hU : IsOpen U := (numberFieldAdic_ball_isOpen K v exp_ne_zero).preimage
    (continuous_const.sub continuous_id)
  obtain ⟨z, hz⟩ := (denseRange_algebraMap (K := K) v).exists_mem_open hU
    ⟨(x : v.adicCompletion K), by simp [U]⟩
  have hn : exp (-(n : ℤ)) ≤ (1 : ℤᵐ⁰) := by
    rw [← exp_zero, exp_le_exp]
    omega
  have hzint : v.valuation K z ≤ 1 := by
    have hv : Valued.v (algebraMap K (v.adicCompletion K) z) ≤ 1 := by
      rw [← sub_add_cancel (algebraMap K (v.adicCompletion K) z) (x : v.adicCompletion K)]
      apply Valuation.map_add_le _ _ x.property
      rw [Valuation.map_sub_swap]
      exact hz.trans hn
    simpa only [algebraMap_adicCompletion, Function.comp_apply,
      Algebra.algebraMap_self_apply, valuedAdicCompletion_eq_valuation'] using hv
  obtain ⟨a, ha⟩ := v.exists_valuation_sub_lt_of_integer hzint
    (Units.mk0 (exp (-(n : ℤ))) exp_ne_zero)
  refine ⟨a, ?_⟩
  have hza : Valued.v (algebraMap K (v.adicCompletion K) z -
      algebraMap (𝓞 K) (v.adicCompletion K) a) ≤ exp (-(n : ℤ)) := by
    rw [IsScalarTower.algebraMap_apply (𝓞 K) K (v.adicCompletion K), ← map_sub,
      algebraMap_adicCompletion, Function.comp_apply, valuedAdicCompletion_eq_valuation',
      Algebra.algebraMap_self, RingHom.id_apply, Valuation.map_sub_swap]
    exact ha.le
  rw [← sub_add_sub_cancel _ (algebraMap K (v.adicCompletion K) z)]
  exact Valuation.map_add_le _ hz hza

/-- Global algebraic integers approximate finitely many original local integers simultaneously. -/
theorem numberFieldIntegralPlaces_approximation (s : Finset (HeightOneSpectrum (𝓞 K)))
    (x : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletionIntegers K)
    (n : HeightOneSpectrum (𝓞 K) → ℕ) :
    ∃ r : 𝓞 K, ∀ v ∈ s,
      Valued.v ((x v : v.adicCompletion K) - algebraMap (𝓞 K) (v.adicCompletion K) r) ≤
        exp (-(n v : ℤ)) := by
  choose a ha using fun v => numberFieldIntegralPlace_approximation K v (x v) (n v)
  obtain ⟨r, hr⟩ := exists_forall_sub_mem_ideal (s := s) (fun v => v.asIdeal) n
    (fun v _ => v.prime) (fun _ _ _ _ hvw h => hvw (HeightOneSpectrum.ext h))
    (fun v => a v.val)
  refine ⟨r, fun v hv => ?_⟩
  rw [← sub_add_sub_cancel _ (algebraMap (𝓞 K) (v.adicCompletion K) (a v))]
  refine Valuation.map_add_le _ (ha v) ?_
  rw [← map_sub, IsScalarTower.algebraMap_apply (𝓞 K) K (v.adicCompletion K),
    algebraMap_adicCompletion, Function.comp_apply, valuedAdicCompletion_eq_valuation',
    Algebra.algebraMap_self_apply, valuation_of_algebraMap,
    Valuation.map_sub_swap, intValuation_le_pow_iff_mem]
  exact hr v hv

end
end Dubon2026
