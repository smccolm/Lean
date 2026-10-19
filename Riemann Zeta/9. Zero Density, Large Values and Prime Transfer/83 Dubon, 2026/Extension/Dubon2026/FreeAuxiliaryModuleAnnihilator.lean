import Dubon2026.Reuse.Imperial.Patching.Module
import Mathlib.LinearAlgebra.FreeModule.Basic

/-! Freeness over the actual auxiliary group algebra turns the proved
parameter-kernel convergence into the precise patching-system condition.
This deduction retains genuine Hecke-module freeness as its explicit
remaining arithmetic input, rather than assuming annihilator convergence. -/

namespace Dubon2026
noncomputable section
open IsLocalRing Filter

/-- Restriction of a faithful scalar action has exactly the kernel
of its coefficient homomorphism as annihilator. -/
theorem faithfulRestrictedModule_annihilator
    {Λ B M : Type*} [CommRing Λ] [CommRing B] [AddCommGroup M]
    [Module B M] [FaithfulSMul B M] (f : Λ →+* B) :
    letI : Module Λ M := Module.compHom M f
    Module.annihilator Λ M = RingHom.ker f := by
  letI : Module Λ M := Module.compHom M f
  ext x
  rw [Module.mem_annihilator, RingHom.mem_ker]
  constructor
  · intro hx
    apply eq_of_smul_eq_smul (α := M)
    intro m
    have hm := hx m
    change f x • m = 0 at hm
    simpa only [zero_smul] using hm
  · intro hx m
    change f x • m = 0
    rw [hx, zero_smul]

/-- The quantitative kernel bound constructs the exact existing
patching-system class for nonzero free auxiliary modules. Arithmetic
Hecke freeness remains explicit; no annihilator condition is supplied. -/
theorem convergingParameterActions_freeModules_isPatchingSystem
    (Λ : Type*) [CommRing Λ] [IsLocalRing Λ]
    [TopologicalSpace Λ] [IsTopologicalRing Λ] [IsAdicTopology Λ]
    (B : ℕ → Type*) [∀ i, CommRing (B i)]
    (M : ℕ → Type*) [∀ i, AddCommGroup (M i)] [∀ i, Nontrivial (M i)]
    [∀ i, Module (B i) (M i)] [∀ i, Module.Free (B i) (M i)]
    (f : ∀ i, Λ →+* B i)
    (hf : ∀ i, RingHom.ker (f i) ≤ maximalIdeal Λ ^ (i + 1)) :
    letI : ∀ i, Module Λ (M i) := fun i => Module.compHom (M i) (f i)
    IsPatchingSystem Λ M atTop := by
  letI : ∀ i, Module Λ (M i) := fun i => Module.compHom (M i) (f i)
  constructor
  intro α hα
  obtain ⟨n, _, hn⟩ := (hasBasis_maximalIdeal_pow Λ).mem_iff.mp (hα.mem_nhds (α.zero_mem))
  filter_upwards [eventually_ge_atTop n] with i hi
  rw [faithfulRestrictedModule_annihilator (M := M i)]
  exact (hf i).trans ((Ideal.pow_le_pow_right (hi.trans (Nat.le_succ i))).trans hn)

end
end Dubon2026
