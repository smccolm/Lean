import Dubon2026.PartialRestrictionFreeHomCoordinates

/-! The actual local restriction of the global free cover need not have
surjective group image. Reconstruct its Hom cocycle using the proved coset
coordinates, retaining every original global generator. This is the precise
local free-cover input to DUB-17's relation representation. -/
namespace Dubon2026
noncomputable section
open CategoryTheory
attribute [local instance 1100] Rep.hV2
variable {R G H α : Type} [CommRing R] [Group G] [Group H]
  (π : G →* H) (C : Rep.{0} R G)

/-- Kernel coboundaries at the original free coordinates give a coboundary
for local restriction even when its decomposition group is proper. -/
theorem partialRestrictionFreeHomCocycle_exists_coboundary
    (c : groupCohomology.cocycles₁ ((Rep.ihom (Rep.res π (Rep.free R H α))).obj C))
    (hker : ∀ (b : α) (h : H), ∃ v : C, ∀ t : G, π t = 1 →
      DFunLike.coe (F := Rep.res π (Rep.free R H α) →ₗ[R] C) (c.val t)
        (Finsupp.single b (Finsupp.single h 1)) = C.ρ t v - v) :
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
  obtain ⟨w, hw⟩ := partialRestrictionFreeHom_coordinate_coboundary π C u hu v hv
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
