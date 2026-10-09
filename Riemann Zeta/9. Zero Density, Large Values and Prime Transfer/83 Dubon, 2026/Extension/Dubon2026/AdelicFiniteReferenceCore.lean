import Dubon2026.AdelicFiniteReferenceCoordinates
import Dubon2026.AdelicFiniteTensorCore

/-! # Actual complementary orbit-core inclusions for finite reference extensions -/

namespace Dubon2026

noncomputable section
open IsDedekindDomain Matrix Matrix.SpecialLinearGroup CongruenceSubgroup
open scoped MatrixGroups

/-- Restricting an actual orbit to a smaller subgroup gives a smaller actual algebraic orbit span. -/
theorem representationSubgroupOrbitSpan_mono {G V : Type*} [Group G]
    [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V) (y : V)
    {H K : Subgroup G} (h : H ≤ K) :
    Submodule.span ℂ (Set.range (fun a : H => ρ a.val y)) ≤
      Submodule.span ℂ (Set.range (fun a : K => ρ a.val y)) := by
  apply Submodule.span_le.mpr
  rintro _ ⟨a, rfl⟩
  exact Submodule.subset_span ⟨⟨a.val, h a.property⟩, rfl⟩

variable {N : ℕ} [NeZero N] {k : ℤ} {n : ℕ}
  (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k) (v : Fin (n + 1) → HeightOneSpectrum ℤ)

/-- The actual complement after adding a genuine place embeds as the identical matrices in the previous complement. -/
def adelicFiniteFamilyAwayInitHom :
    adelicFiniteFamilyAwayGroup v →* adelicFiniteFamilyAwayGroup (fun i : Fin n => v i.castSucc) :=
  Subgroup.inclusion (adelicFiniteFamilyAwayGroup_init_le v)

/-- The smaller actual complementary group has its original orbit core inside the previous complementary core. -/
theorem adelicFiniteFamilyAwayCore_init_le :
    adelicFiniteFamilyAwayCore f v ≤ adelicFiniteFamilyAwayCore f (fun i : Fin n => v i.castSucc) :=
  representationSubgroupOrbitSpan_mono (adelicCyclicHilbertRepresentation f) (adelicCyclicUnitReference f)
    (adelicFiniteFamilyAwayGroup_init_le v)

/-- The genuine complementary core inclusion preserves the original inherited Hilbert norm. -/
def adelicFiniteFamilyAwayCoreInitIsometry :
    adelicFiniteFamilyAwayCore f v →ₗᵢ[ℂ] adelicFiniteFamilyAwayCore f (fun i : Fin n => v i.castSucc) where
  toLinearMap := Submodule.inclusion (adelicFiniteFamilyAwayCore_init_le f v)
  norm_map' _ := rfl

/-- The actual complementary inclusion leaves every original normalized cusp orbit vector unchanged. -/
theorem adelicFiniteFamilyAwayCoreInitIsometry_orbit (a : adelicFiniteFamilyAwayGroup v) :
    adelicFiniteFamilyAwayCoreInitIsometry f v (adelicFiniteFamilyAwayOrbit f v a) =
      adelicFiniteFamilyAwayOrbit f (fun i : Fin n => v i.castSucc) (adelicFiniteFamilyAwayInitHom v a) := by
  apply Subtype.ext
  rfl

end
end Dubon2026
