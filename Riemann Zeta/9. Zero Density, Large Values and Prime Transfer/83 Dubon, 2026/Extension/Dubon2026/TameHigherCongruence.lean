/-
Copyright 2026 Anthropic, PBC.
Released under Apache 2.0; see ../../Dependencies/AnthropicFLTReuse/LICENSE.
Adapted from anthropics/fermats-last-theorem commit 6e837e75355538c7f80bab5b956861e86c4eacc2,
P2M/Sol/S_ValuationSubring_exists_ideal_ringOfIntegers_inertia_eq_map_restrictNormalHom.lean.
Modified for Dubon: extract the required dependency closure, use the native namespace,
remove external elaboration macros and linter overrides, and retain default proof limits.
This supplies the finite tame local condition for arithmetic patching -> higher symmetric
power continuation -> Dubon Theorem 2.6 (DUB-17) and Corollary 8.2 (DUB-18).
-/

import Dubon2026.TameUniformizerCongruence

namespace Dubon2026.TameKernel

universe u v

section Higher
variable {B : Type u} [CommRing B] {G : Type v} [Group G] [MulSemiringAction G B]
variable (𝔓 : Ideal B)

theorem smul_sub_pow_mul_mem_pow_succ {σ : G} (hσ : σ ∈ 𝔓.inertia G) {t : B}
    (h1 : ∀ x ∈ 𝔓, σ • x - t * x ∈ 𝔓 ^ 2) (k : ℕ) :
    ∀ x ∈ 𝔓 ^ k, σ • x - t ^ k * x ∈ 𝔓 ^ (k + 1) := by
  induction k with
  | zero =>
    intro x _
    rw [pow_zero, one_mul, zero_add, pow_one]
    exact hσ x
  | succ k ih =>
    intro x hx
    rw [pow_succ] at hx
    refine Submodule.mul_induction_on hx (fun a ha b hb => ?_) (fun y z hy hz => ?_)
    ·
      have e : σ • (a * b) - t ^ (k + 1) * (a * b) = (σ • a - t ^ k * a) * (σ • b) + t ^ k * a * (σ • b - t * b) := by
        rw [smul_mul']; ring
      rw [e]
      refine (𝔓 ^ (k + 1 + 1)).add_mem ?_ ?_
      · rw [pow_succ]
        exact Ideal.mul_mem_mul (ih a ha) (smul_mem_of_mem_inertia 𝔓 hσ hb)
      · have : t ^ k * a * (σ • b - t * b) ∈ 𝔓 ^ k * 𝔓 ^ 2 :=
          Ideal.mul_mem_mul (Ideal.mul_mem_left _ _ ha) (h1 b hb)
        rw [← pow_add] at this
        exact this
    · have e : σ • (y + z) - t ^ (k + 1) * (y + z) = (σ • y - t ^ (k + 1) * y) + (σ • z - t ^ (k + 1) * z) := by
        rw [smul_add]; ring
      rw [e]; exact (𝔓 ^ (k + 1 + 1)).add_mem hy hz

theorem smul_sub_mem_pow_succ_of_forall {σ : G} (hσ : σ ∈ 𝔓.inertia G) (h1 : ∀ x : B, σ • x - x ∈ 𝔓 ^ 2)
    (k : ℕ) {x : B} (hx : x ∈ 𝔓 ^ k) : σ • x - x ∈ 𝔓 ^ (k + 1) := by
  have := smul_sub_pow_mul_mem_pow_succ 𝔓 hσ (t := 1) (fun x _ => by rw [one_mul]; exact h1 x) k x hx
  rwa [one_pow, one_mul] at this


end Higher
end Dubon2026.TameKernel
