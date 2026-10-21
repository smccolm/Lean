import Mathlib.Algebra.FreeAlgebra
import Mathlib.Analysis.Complex.Basic
import Mathlib.RingTheory.Ideal.Maps

/-! Transport integral Hecke relations to an actual complex eigenclass.
DUB-17/18 -> residual modular Galois association -> residual H1 eigensystem
-> the integral H1 Hecke character. Free-algebra words encode every relation
in the generated operator algebra, without assuming commutativity.

Adapted from sections Words and exists_algHom_adjoin of
anthropics/fermats-last-theorem, revision
6e837e75355538c7f80bab5b956861e86c4eacc2,
P2M/Sol/S_HeckeEis_isEigensystemH1_binaryFormRepSL_of_heckeTLin_eq_smul.lean
(Apache-2.0; retained archive LICENSE and NOTICE).
-/

namespace Dubon2026
noncomputable section

private theorem word_intCast {ι A : Type} [Ring A] (t : ι → A) (r : ℤ) :
    FreeAlgebra.lift ℤ t (algebraMap ℤ (FreeAlgebra ℤ ι) r) = (r : A) := by
  rw [AlgHom.commutes, algebraMap_int_eq, eq_intCast]

/-- Compatibility with every generating operator implies compatibility with every integral operator word. -/
theorem sourceHeckeWord_intertwine {ι M V : Type}
    [AddCommGroup M] [Module ℤ M] [AddCommGroup V] [Module ℂ V]
    (t : ι → Module.End ℤ M) (u : ι → Module.End ℂ V) (Φ : M →+ V)
    (hΦ : ∀ i x, Φ (t i x) = u i (Φ x)) (a : FreeAlgebra ℤ ι) (x : M) :
    Φ (FreeAlgebra.lift ℤ t a x) = FreeAlgebra.lift ℤ u a (Φ x) := by
  induction a using FreeAlgebra.induction generalizing x with
  | grade0 r =>
    rw [word_intCast, word_intCast, Module.End.intCast_apply,
      Module.End.intCast_apply, map_zsmul]
  | grade1 i => rw [FreeAlgebra.lift_ι_apply, FreeAlgebra.lift_ι_apply, hΦ]
  | mul a b ha hb =>
    rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, ha, hb]
  | add a b ha hb =>
    rw [map_add, map_add, LinearMap.add_apply, LinearMap.add_apply, map_add, ha, hb]

/-- An actual common eigenvector evaluates every integral Hecke word at its original eigenvalues. -/
theorem sourceHeckeWord_eigenvector {ι V : Type} [AddCommGroup V] [Module ℂ V]
    (t : ι → Module.End ℂ V) (lam : ι → ℂ) (x : V)
    (hx : ∀ i, t i x = lam i • x) (a : FreeAlgebra ℤ ι) :
    FreeAlgebra.lift ℤ t a x = FreeAlgebra.lift ℤ lam a • x := by
  induction a using FreeAlgebra.induction with
  | grade0 r =>
    rw [word_intCast, word_intCast, Module.End.intCast_apply, Int.cast_smul_eq_zsmul]
  | grade1 i => rw [FreeAlgebra.lift_ι_apply, FreeAlgebra.lift_ι_apply, hx]
  | mul a b ha hb =>
    rw [map_mul, map_mul, Module.End.mul_apply, hb, map_smul, ha, smul_smul, mul_comm]
  | add a b ha hb =>
    rw [map_add, map_add, LinearMap.add_apply, ha, hb, add_smul]

/-- Vanishing of all actual integral operator relations gives a character of the generated algebra,
with its prescribed values on every original generator. -/
theorem sourceHeckeWord_exists_character {ι M F : Type}
    [AddCommGroup M] [Module ℤ M] [Field F]
    (t : ι → Module.End ℤ M) (lam : ι → F)
    (hker : ∀ a : FreeAlgebra ℤ ι, FreeAlgebra.lift ℤ t a = 0 →
      FreeAlgebra.lift ℤ lam a = 0) :
    ∃ χ : Algebra.adjoin ℤ (Set.range t) →ₐ[ℤ] F,
      ∀ i, χ ⟨t i, Algebra.subset_adjoin ⟨i, rfl⟩⟩ = lam i := by
  let f := (FreeAlgebra.lift ℤ t).rangeRestrict
  have hf : Function.Surjective f := AlgHom.rangeRestrict_surjective _
  have hkerle : RingHom.ker f.toRingHom ≤ RingHom.ker (FreeAlgebra.lift ℤ lam).toRingHom := by
    intro a ha
    rw [RingHom.mem_ker] at ha ⊢
    exact hker a (congrArg Subtype.val ha)
  let χ₀ : (FreeAlgebra.lift ℤ t).range →+* F :=
    RingHom.liftOfRightInverse f.toRingHom (Function.surjInv hf)
      (Function.rightInverse_surjInv hf) ⟨_, hkerle⟩
  have hχ₀ (a) : χ₀ (f a) = FreeAlgebra.lift ℤ lam a :=
    RingHom.liftOfRightInverse_comp_apply _ _ _ ⟨_, hkerle⟩ a
  let e : Algebra.adjoin ℤ (Set.range t) ≃ₐ[ℤ] (FreeAlgebra.lift ℤ t).range :=
    Subalgebra.equivOfEq _ _ (Algebra.adjoin_range_eq_range_freeAlgebra_lift ℤ (X := ι) t)
  refine ⟨{ toRingHom := χ₀.comp e.toRingHom, commutes' := fun r => ?_ }, fun i => ?_⟩
  · change χ₀ (e (algebraMap ℤ (Algebra.adjoin ℤ (Set.range t)) r)) = algebraMap ℤ F r
    rw [AlgEquiv.commutes, eq_intCast, map_intCast, eq_intCast]
  · change χ₀ (e ⟨t i, _⟩) = lam i
    have he : e ⟨t i, Algebra.subset_adjoin ⟨i, rfl⟩⟩ = f (FreeAlgebra.ι ℤ i) := by
      apply Subtype.ext
      exact (FreeAlgebra.lift_ι_apply t i).symm
    rw [he, hχ₀, FreeAlgebra.lift_ι_apply]

end
end Dubon2026
