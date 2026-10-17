import Dubon2026.OriginalPGroupCoinvariantDetection
import Mathlib.Algebra.Module.ZMod

/-! # Detection for the actual integral p-torsion coefficient

The original integral action on a coefficient killed by p has the same
values over the prime field. Original integral coinvariant relations
remain prime-field relations. This applies the proved detection lemma
to actual mod-p kernels and cokernels on DUB-17's projectivity route.
-/
namespace Dubon2026
noncomputable section
attribute [local instance 1100] Rep.hV2

variable {G W : Type} [Group G] [AddCommGroup W] [instInt : Module ℤ W]

/-- The original integral action with unchanged values, viewed over the prime field. -/
def originalIntegralPrimeAction (p : ℕ) [Module (ZMod p) W]
    (ρ : Representation ℤ G W) : Representation (ZMod p) G W where
  toFun g := (ρ g).toAddMonoidHom.toZModLinearMap p
  map_one' := by
    apply LinearMap.ext
    intro x
    exact congrArg (fun f : W →ₗ[ℤ] W => f x) ρ.map_one
  map_mul' g h := by
    apply LinearMap.ext
    intro x
    exact congrArg (fun f : W →ₗ[ℤ] W => f x) (ρ.map_mul g h)

/-- Every literal integral coinvariant relation remains a relation for the unchanged prime-field action. -/
theorem originalIntegralPrime_coinvariant_relation (p : ℕ) [Module (ZMod p) W]
    (ρ : Representation ℤ G W) (x : W)
    (hx : x ∈ Representation.Coinvariants.ker ρ) :
    x ∈ Representation.Coinvariants.ker (originalIntegralPrimeAction p ρ) := by
  refine Submodule.span_induction ?_ (Submodule.zero_mem _)
    (fun a b _ _ ha hb => Submodule.add_mem _ ha hb) (fun c a _ ha => ?_) hx
  · rintro _ ⟨⟨g, y⟩, rfl⟩
    exact Representation.Coinvariants.mem_ker_of_eq g y _ rfl
  · have he := int_smul_eq_zsmul instInt c a
    have hz := (Representation.Coinvariants.ker
      (originalIntegralPrimeAction p ρ)).toAddSubgroup.zsmul_mem ha c
    exact (congrArg (fun y => y ∈ Representation.Coinvariants.ker
      (originalIntegralPrimeAction p ρ)) he).mpr hz

/-- For the original integral p-torsion coefficient of a finite p-group, zero actual coinvariants force every original element to be zero. -/
theorem originalIntegralPrime_zero_of_coinvariants
    [Finite G] (A : Rep.{0} ℤ G) (p : ℕ) [Fact p.Prime] (hG : IsPGroup p G)
    (hp : ∀ x : A, p • x = 0)
    (hcoin : ∀ x : A, Representation.Coinvariants.mk A.ρ x = 0) (x : A) : x = 0 := by
  haveI : Module (ZMod p) A := AddCommGroup.zmodModule hp
  exact originalPGroup_zero_of_coinvariant_relations hG (originalIntegralPrimeAction p A.ρ)
    (fun y => originalIntegralPrime_coinvariant_relation p A.ρ y
      ((Representation.Coinvariants.mk_eq_zero A.ρ).mp (hcoin y))) x

end
end Dubon2026
