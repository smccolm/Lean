import Dubon2026.OriginalSubgroupCosetCoordinates
import Dubon2026.RestrictedFreeHomCocycleVanishing

/-! Coordinates for the actual local restriction of a global free cover.
The local decomposition group need not fill the global Galois group.
Original coset coordinates let kernel coboundaries reconstruct the Hom
coboundary without that false surjectivity premise. This supplies the local
relation representatives on DUB-17's reverse-localization chain. -/
namespace Dubon2026
noncomputable section
open CategoryTheory
attribute [local instance 1100] Rep.hV2
variable {R G H α : Type} [CommRing R] [Group G] [Group H]
  (π : G →* H) (C : Rep.{0} R G)

/-- Reconstruct the original free coordinates orbit by orbit for the actual
possibly nonsurjective local restriction map. -/
theorem partialRestrictionFreeHom_coordinate_coboundary
    (u : G → α → H → C)
    (hu : ∀ g t b h, u (g * t) b h = u g b h + C.ρ g (u t b ((π g)⁻¹ * h)))
    (v : α → H → C)
    (hv : ∀ b h t, π t = 1 → u t b h = C.ρ t (v b h) - v b h) :
    ∃ w : α → H → C, ∀ g b h,
      C.ρ g (w b ((π g)⁻¹ * h)) - w b h = u g b h := by
  classical
  let S := π.range
  let r : H → H := fun h => (subgroupCosetRepresentative S h⁻¹)⁻¹
  let a : H → S := fun h => (subgroupCosetRemainder S h⁻¹)⁻¹
  have har (h : H) : (a h : H) * r h = h := by
    have he := congrArg Inv.inv (subgroupCosetRepresentative_mul_remainder S h⁻¹)
    simpa only [mul_inv_rev, inv_inv] using he
  have hr (g : G) (h : H) : r ((π g)⁻¹ * h) = r h := by
    change (subgroupCosetRepresentative S ((π g)⁻¹ * h)⁻¹)⁻¹ = _
    rw [mul_inv_rev, inv_inv]
    exact congrArg Inv.inv (subgroupCosetRepresentative_mul S h⁻¹ ⟨π g, ⟨g, rfl⟩⟩)
  choose s hs using fun h => (a h).property
  have hsr (h : H) : π (s h) * r h = h := by rw [hs]; exact har h
  let w : α → H → C := fun b h => C.ρ (s h) (v b (r h)) - u (s h) b h
  refine ⟨w, ?_⟩
  intro g b h
  let k := (π g)⁻¹ * h
  let t := (s h)⁻¹ * g * s k
  have hrk : r k = r h := hr g h
  have hsk : π g * π (s k) = π (s h) := by
    apply mul_right_cancel (b := r h)
    calc
      π g * π (s k) * r h = π g * (π (s k) * r k) := by rw [hrk, mul_assoc]
      _ = π g * k := by rw [hsr]
      _ = h := by simp [k]
      _ = π (s h) * r h := (hsr h).symm
  have ht : π t = 1 := by
    simp only [t, map_mul, map_inv, mul_assoc, hsk, inv_mul_cancel]
  have he : s h * t = g * s k := by simp [t, mul_assoc]
  have hscoord : (π (s h))⁻¹ * h = r h := by
    calc
      _ = (π (s h))⁻¹ * (π (s h) * r h) :=
        congrArg (fun z => (π (s h))⁻¹ * z) (hsr h).symm
      _ = r h := inv_mul_cancel_left _ _
  have hd := hu g (s k) b h
  have hd' := hu (s h) t b h
  rw [he, hscoord, hv b (r h) t ht, map_sub] at hd'
  have hact : C.ρ (s h) (C.ρ t (v b (r h))) = C.ρ g (C.ρ (s k) (v b (r h))) := by
    rw [← Module.End.mul_apply, ← map_mul, he, map_mul, Module.End.mul_apply]
  rw [hact, hd] at hd'
  change C.ρ g (C.ρ (s k) (v b (r k)) - u (s k) b k) -
    (C.ρ (s h) (v b (r h)) - u (s h) b h) = u g b h
  rw [hrk, map_sub]
  calc
    _ = u g b h + ((u (s h) b h +
        (C.ρ g (C.ρ (s k) (v b (r h))) - C.ρ (s h) (v b (r h)))) -
        (u g b h + C.ρ g (u (s k) b k))) := by abel
    _ = u g b h := by rw [← hd', sub_self, add_zero]

end
end Dubon2026
