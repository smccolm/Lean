import Dubon2026.OriginalRelationModuleSequence
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-! # Restricted free-cover Hom cocycles from the actual kernel

Evaluate a Hom cocycle on the original free generators. Coboundaries on
the restriction kernel give a coboundary on the entire free-cover Hom.
The arithmetic consumer obtains those witnesses from already proved open
subgroup class H1 vanishing. This is the free-cover vanishing needed to
represent degree-one class duality by relation morphisms in DUB-17.
-/
namespace Dubon2026
noncomputable section
open CategoryTheory
attribute [local instance 1100] Rep.hV2
variable {R G H α : Type} [CommRing R] [Group G] [Group H]
  (π : G →* H) (hπ : Function.Surjective π) (C : Rep.{0} R G)

include hπ in
private theorem coordinate_coboundary
    (u : G → α → H → C)
    (hu : ∀ g t b h, u (g * t) b h = u g b h + C.ρ g (u t b ((π g)⁻¹ * h)))
    (v : α → C) (hv : ∀ b t, π t = 1 → u t b 1 = C.ρ t (v b) - v b) :
    ∃ w : α → H → C, ∀ g b h,
      C.ρ g (w b ((π g)⁻¹ * h)) - w b h = u g b h := by
  choose s hs using hπ
  let w : α → H → C := fun b h => C.ρ (s h) (v b) - u (s h) b h
  refine ⟨w, ?_⟩
  intro g b h
  let k := (π g)⁻¹ * h
  let t := (s h)⁻¹ * g * s k
  have ht : π t = 1 := by
    simp [t, k, map_mul, map_inv, hs, mul_assoc]
  have he : s h * t = g * s k := by simp [t, mul_assoc]
  have hd := hu g (s k) b h
  have hd' := hu (s h) t b h
  rw [he, hs, inv_mul_cancel, hv b t ht] at hd'
  rw [map_sub] at hd'
  have hact : C.ρ (s h) (C.ρ t (v b)) = C.ρ g (C.ρ (s k) (v b)) := by
    rw [← Module.End.mul_apply, ← map_mul, he, map_mul, Module.End.mul_apply]
  rw [hact, hd] at hd'
  change C.ρ g (C.ρ (s k) (v b) - u (s k) b k) -
    (C.ρ (s h) (v b) - u (s h) b h) = u g b h
  rw [map_sub]
  calc
    _ = u g b h + ((u (s h) b h + (C.ρ g (C.ρ (s k) (v b)) - C.ρ (s h) (v b))) -
        (u g b h + C.ρ g (u (s k) b k))) := by abel
    _ = u g b h := by rw [← hd', sub_self, add_zero]

include hπ in
/-- If the original generator evaluations of a restricted free-cover Hom
cocycle are coboundaries on the actual kernel, the entire Hom cocycle is
a coboundary. No finite-stage or cohomology comparison is assumed. -/
theorem restrictedFreeHomCocycle_exists_coboundary
    (c : groupCohomology.cocycles₁ ((Rep.ihom (Rep.res π (Rep.free R H α))).obj C))
    (hker : ∀ b : α, ∃ v : C, ∀ t : G, π t = 1 →
      DFunLike.coe (F := Rep.res π (Rep.free R H α) →ₗ[R] C) (c.val t)
        (Finsupp.single b (Finsupp.single 1 1)) = C.ρ t v - v) :
    ∃ v : (Rep.ihom (Rep.res π (Rep.free R H α))).obj C,
      ∀ g : G, ((Rep.ihom (Rep.res π (Rep.free R H α))).obj C).ρ g v - v = c.val g := by
  classical
  let u : G → α → H → C := fun g b h =>
    DFunLike.coe (F := Rep.res π (Rep.free R H α) →ₗ[R] C) (c.val g)
      (Finsupp.single b (Finsupp.single h 1))
  have hu : ∀ g t b h, u (g * t) b h = u g b h + C.ρ g (u t b ((π g)⁻¹ * h)) := by
    intro g t b h
    have hc := congrArg (fun l : (Rep.ihom (Rep.res π (Rep.free R H α))).obj C =>
      DFunLike.coe (F := Rep.res π (Rep.free R H α) →ₗ[R] C) l
        (Finsupp.single b (Finsupp.single h 1)))
      ((groupCohomology.mem_cocycles₁_iff _).mp c.property g t)
    change DFunLike.coe (F := Rep.res π (Rep.free R H α) →ₗ[R] C) (c.val (g * t))
        (Finsupp.single b (Finsupp.single h 1)) =
      C.ρ g (DFunLike.coe (F := Rep.res π (Rep.free R H α) →ₗ[R] C) (c.val t)
        (Representation.free R H α (π g⁻¹) (Finsupp.single b (Finsupp.single h 1)))) +
      DFunLike.coe (F := Rep.res π (Rep.free R H α) →ₗ[R] C) (c.val g)
        (Finsupp.single b (Finsupp.single h 1)) at hc
    simpa only [u, Representation.free_single_single, map_inv, add_comm] using hc
  choose v hv using hker
  obtain ⟨w, hw⟩ := coordinate_coboundary π hπ C u hu v hv
  let l : Rep.res π (Rep.free R H α) →ₗ[R] C :=
    Finsupp.lsum R (fun b => Finsupp.linearCombination R (w b))
  have hl (b : α) (h : H) (r : R) :
      l (Finsupp.single b (Finsupp.single h r)) = r • w b h := by
    simp [l, Finsupp.lsum_single, Finsupp.linearCombination_single]
  refine ⟨l, ?_⟩
  intro g
  apply Finsupp.lhom_ext
  intro b x
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => simpa only [Finsupp.single_add, map_add] using congrArg₂ (· + ·) hx hy
  | single h r =>
    change C.ρ g (l ((Rep.res π (Rep.free R H α)).ρ g⁻¹
      (Finsupp.single b (Finsupp.single h r)))) -
      l (Finsupp.single b (Finsupp.single h r)) =
        DFunLike.coe (F := Rep.res π (Rep.free R H α) →ₗ[R] C) (c.val g)
          (Finsupp.single b (Finsupp.single h r))
    change C.ρ g (l (Representation.free R H α (π g⁻¹)
      (Finsupp.single b (Finsupp.single h r)))) - _ = _
    rw [Representation.free_single_single, map_inv, hl, hl, map_smul, ← smul_sub, hw]
    change r • DFunLike.coe (F := Rep.res π (Rep.free R H α) →ₗ[R] C) (c.val g)
      (Finsupp.single b (Finsupp.single h 1)) = _
    rw [← map_smul]
    congr 1
    simp [Finsupp.smul_single]

end
end Dubon2026
