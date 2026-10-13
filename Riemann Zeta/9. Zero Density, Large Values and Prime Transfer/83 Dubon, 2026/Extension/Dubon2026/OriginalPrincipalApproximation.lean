/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the retained upstream LICENSE.
The unit-ratio open set argument is adapted from ClassFieldTheory
dc55774a7fe03e742f2b4c6114aab5e7d01edfb1,
Nyll/ClassFieldTheory/AlgebraicNumberTheory/RayClass/Ideal.lean
and RayClass/Approximation.lean.
-/
import Dubon2026.OriginalMixedPlaceApproximation
import Mathlib.Topology.Algebra.IsOpenUnits

/-! # One actual principal unit satisfying all local open conditions

The original mixed-place density produces one global unit, with every local
ratio in the given open subgroup. Applied to actual local powers, it gives
the principal norm correction required for DUB-17's prime-selection argument.
-/
namespace Dubon2026
noncomputable section
open NumberField IsDedekindDomain
open scoped NumberField
variable (K : Type) [Field K] [NumberField K]

/-- One actual global unit meets the prescribed open multiplicative conditions
at all original infinite places and the selected original finite places. -/
theorem original_principalUnit_open_approximation
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (a : ∀ i, (OriginalApproximationCompletion K S i)ˣ)
    (U : ∀ i, Subgroup (OriginalApproximationCompletion K S i)ˣ)
    (hU : ∀ i, IsOpen (U i : Set (OriginalApproximationCompletion K S i)ˣ)) :
    ∃ x : Kˣ, ∀ i,
      a i * (Units.map (algebraMap K (OriginalApproximationCompletion K S i)).toMonoidHom x)⁻¹ ∈ U i := by
  let W (i : OriginalApproximationPlace K S) : Set (OriginalApproximationCompletion K S i) :=
    Units.val '' (fun y : (OriginalApproximationCompletion K S i)ˣ => a i * y⁻¹) ⁻¹' (U i : Set _)
  have hOpen : IsOpen (Set.univ.pi W) := by
    apply isOpen_set_pi Set.finite_univ
    intro i _
    apply IsOpenUnits.isOpenEmbedding_unitsVal.isOpenMap
    exact (hU i).preimage (continuous_const.mul continuous_inv)
  have hNonempty : (Set.univ.pi W).Nonempty := by
    refine ⟨fun i => (a i : OriginalApproximationCompletion K S i), ?_⟩
    intro i _
    exact ⟨a i, by simp, rfl⟩
  obtain ⟨x, hx⟩ := (original_mixedCompletions_dense K S).exists_mem_open hOpen hNonempty
  let w : InfinitePlace K := Classical.choice inferInstance
  obtain ⟨y, _, hy⟩ := hx (Sum.inr w) (Set.mem_univ _)
  have hx0 : x ≠ 0 := by
    intro hzero
    apply y.ne_zero
    simpa only [hzero, map_zero] using hy
  refine ⟨Units.mk0 x hx0, ?_⟩
  intro i
  obtain ⟨z, hz, hzx⟩ := hx i (Set.mem_univ _)
  have he : Units.map (algebraMap K (OriginalApproximationCompletion K S i)).toMonoidHom
      (Units.mk0 x hx0) = z := Units.ext hzx.symm
  rw [he]
  exact hz

end
end Dubon2026
