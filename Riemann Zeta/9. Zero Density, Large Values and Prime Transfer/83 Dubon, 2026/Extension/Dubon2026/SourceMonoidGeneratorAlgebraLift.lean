import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Algebra.Algebra.Subalgebra.Lattice
import Mathlib.RingTheory.Ideal.Maps

/-! DUB-17/18 -> original Gamma1 genus preservation -> reverse genus inequality
-> cusp residue fiber bounds -> actual reduced slash field embedding. Native
monoid-algebra evaluation and the ring-homomorphism kernel quotient turn proved
finite linear relations on multiplicatively closed generators into an algebra
map. This avoids the reference's separate span map and bilinear multiplicativity
proof. The actual normalized modular generators supply every premise downstream. -/
namespace Dubon2026.SourceFunctionField.IntegralSlash
noncomputable section

theorem exists_algHom_adjoin_of_monoid_relations
    {K L T : Type*} [Field K] [Field L] [Field T] [Algebra K L] [Algebra K T]
    (M : Submonoid L) (θ : M →* T)
    (hlin : ∀ a : M →₀ K,
      (a.sum fun x c => c • (x : L)) = 0 → (a.sum fun x c => c • θ x) = 0) :
    ∃ Φ : Algebra.adjoin K (M : Set L) →ₐ[K] T,
      ∀ x : M, Φ ⟨x, Algebra.subset_adjoin x.property⟩ = θ x := by
  classical
  let e : MonoidAlgebra K M →ₐ[K] L := MonoidAlgebra.lift K L M M.subtype
  let t : MonoidAlgebra K M →ₐ[K] T := MonoidAlgebra.lift K T M θ
  have he : e.range = Algebra.adjoin K (M : Set L) := by
    apply le_antisymm
    · rintro x ⟨a, rfl⟩
      change e a ∈ Algebra.adjoin K (M : Set L)
      rw [show e a = a.sum fun x c => c • (x : L) from MonoidAlgebra.lift_apply _ _]
      exact Subalgebra.sum_mem _ fun x _ =>
        Subalgebra.smul_mem _ (Algebra.subset_adjoin x.property) _
    · apply Algebra.adjoin_le
      intro x hx
      refine ⟨MonoidAlgebra.single (⟨x, hx⟩ : M) 1, ?_⟩
      change e (MonoidAlgebra.single (⟨x, hx⟩ : M) 1) = x
      exact (MonoidAlgebra.lift_single M.subtype ⟨x, hx⟩ 1).trans (one_smul _ _)
  let f := e.rangeRestrict
  have hf : Function.Surjective f := AlgHom.rangeRestrict_surjective e
  have hker : RingHom.ker f.toRingHom ≤ RingHom.ker t.toRingHom := by
    intro a ha
    rw [RingHom.mem_ker] at ha ⊢
    have hzero : e a = 0 := congrArg Subtype.val ha
    rw [show e a = a.sum fun x c => c • (x : L) from MonoidAlgebra.lift_apply _ _] at hzero
    change t a = 0
    rw [show t a = a.sum fun x c => c • θ x from MonoidAlgebra.lift_apply _ _]
    exact hlin a hzero
  let ψ : e.range →+* T := RingHom.liftOfRightInverse f.toRingHom (Function.surjInv hf)
    (Function.rightInverse_surjInv hf) ⟨t.toRingHom, hker⟩
  have hψ (a) : ψ (f a) = t a :=
    RingHom.liftOfRightInverse_comp_apply _ _ _ ⟨_, hker⟩ a
  let ψA : e.range →ₐ[K] T :=
    { toRingHom := ψ
      commutes' := fun c => by
        change ψ (algebraMap K e.range c) = algebraMap K T c
        rw [← f.commutes c, hψ, t.commutes] }
  let E : Algebra.adjoin K (M : Set L) ≃ₐ[K] e.range :=
    Subalgebra.equivOfEq _ _ he.symm
  refine ⟨ψA.comp E.toAlgHom, fun x => ?_⟩
  have hE : E ⟨x, Algebra.subset_adjoin x.property⟩ =
      f (MonoidAlgebra.single x 1) := by
    apply Subtype.ext
    change (x : L) = e (MonoidAlgebra.single x 1)
    exact ((MonoidAlgebra.lift_single M.subtype x 1).trans (one_smul _ _)).symm
  change ψ (E ⟨x, Algebra.subset_adjoin x.property⟩) = θ x
  rw [hE, hψ]
  exact (MonoidAlgebra.lift_single θ x 1).trans (one_smul _ _)

end
end Dubon2026.SourceFunctionField.IntegralSlash
