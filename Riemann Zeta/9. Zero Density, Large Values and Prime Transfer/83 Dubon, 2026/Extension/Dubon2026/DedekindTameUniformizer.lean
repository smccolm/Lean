/-
Copyright 2026 Anthropic, PBC.
Released under Apache 2.0; see ../../Dependencies/AnthropicFLTReuse/LICENSE.
Adapted from anthropics/fermats-last-theorem commit 6e837e75355538c7f80bab5b956861e86c4eacc2,
P2M/Sol/S_ValuationSubring_exists_ideal_ringOfIntegers_inertia_eq_map_restrictNormalHom.lean,
KUM.exists_uniformizer. Modified to use the original height-one prime directly and native Mathlib
adic valuations, omitting the external algebraic-closure place dictionary and proof-limit changes.
This discharges the uniformizer assumptions in the finite tame inertia character required by
the auxiliary local deformation condition -> arithmetic patching -> Dubon Theorem 2.6.
-/
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.Tactic

namespace Dubon2026

open IsDedekindDomain

variable {A : Type*} [CommRing A] [IsDedekindDomain A]

theorem heightOne_exists_tame_uniformizer (w : HeightOneSpectrum A) :
    ∃ ϖ : A, ϖ ∈ w.asIdeal ∧
      (∀ x ∈ w.asIdeal, ∃ y : A, x - ϖ * y ∈ w.asIdeal ^ 2) ∧
      (∀ c : A, c * ϖ ∈ w.asIdeal ^ 2 → c ∈ w.asIdeal) := by
  obtain ⟨ϖ, hϖ⟩ := w.intValuation_exists_uniformizer
  have hϖP : ϖ ∈ w.asIdeal := by
    rw [← w.intValuation_lt_one_iff_mem, hϖ, ← WithZero.exp_zero, WithZero.exp_lt_exp]
    omega
  have hϖ2 : ϖ ∉ w.asIdeal ^ 2 := by
    rw [← w.intValuation_le_pow_iff_mem, hϖ, not_le, WithZero.exp_lt_exp]
    omega
  refine ⟨ϖ, hϖP, ?_, ?_⟩
  · intro x hx
    have hI : Ideal.span {ϖ} ⊔ w.asIdeal ^ 2 = w.asIdeal ^ 1 := by
      refine Ideal.eq_prime_pow_of_succ_lt_of_le w.ne_bot ?_ ?_
      · refine lt_of_le_of_ne le_sup_right fun h => hϖ2 ?_
        rw [h]
        exact Ideal.mem_sup_left (Ideal.mem_span_singleton_self ϖ)
      · rw [pow_one]
        exact sup_le ((Ideal.span_singleton_le_iff_mem _).mpr hϖP)
          (Ideal.pow_le_self two_ne_zero)
    rw [pow_one] at hI
    have hx' : x ∈ Ideal.span {ϖ} ⊔ w.asIdeal ^ 2 := by rw [hI]; exact hx
    obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp hx'
    obtain ⟨y, rfl⟩ := Ideal.mem_span_singleton'.mp ha
    refine ⟨y, ?_⟩
    have he : x - ϖ * y = b := by rw [← hab]; ring
    rw [he]
    exact hb
  · intro c hc
    rw [← w.intValuation_le_pow_iff_mem, map_mul, hϖ] at hc
    rw [← w.intValuation_lt_one_iff_mem]
    by_contra hge
    rw [not_lt] at hge
    have hle : WithZero.exp (-1 : ℤ) ≤ w.intValuation c * WithZero.exp (-1 : ℤ) :=
      le_mul_of_one_le_left zero_le' hge
    have hbad := hle.trans hc
    rw [WithZero.exp_le_exp] at hbad
    norm_num at hbad

end Dubon2026
