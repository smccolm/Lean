import Dubon2026.FieldSL2Perfect
import Dubon2026.HomogeneousSymmetricMatrix
import Dubon2026.PrimitiveRootCyclotomicContinuity

/-! The original cyclotomic kernel retains a perfect residual subgroup.
For DUB-17 this supplies actual root-fixing lifts of every element of the
higher symmetric SL2 image. Residual image containment is still explicit;
this does not assert existence of a modular Galois representation. -/

namespace Dubon2026
noncomputable section
open scoped MatrixGroups

/-- A perfect subgroup of an actual image is already attained inside the
kernel of every original character with commutative target. -/
theorem perfect_subgroup_le_map_character_kernel
    {G H A : Type*} [Group G] [Group H] [CommGroup A]
    (ρ : G →* H) (χ : G →* A) (S : Subgroup H) [Group.IsPerfect S]
    (hS : S ≤ ρ.range) : S ≤ χ.ker.map ρ := by
  calc
    S = ⁅S, S⁆ := Subgroup.commutator_eq_self.symm
    _ ≤ ⁅ρ.range, ρ.range⁆ := Subgroup.commutator_mono hS hS
    _ = (commutator G).map ρ := by
      rw [commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map]
    _ ≤ χ.ker.map ρ := Subgroup.map_mono (Abelianization.commutator_subset_ker χ)

/-- Every literal symmetric SL2 image has an original Galois lift fixing
the specified primitive root. Perfection discharges the cyclotomic-kernel
image condition for every symmetric degree, not only degree one. -/
theorem galois_symmetricSL2_exists_root_fixing_lift
    {F Ω K : Type} [Field F] [Field Ω] [Algebra F Ω] [Field K]
    [NeZero (2 : K)] [NeZero (3 : K)]
    (n : ℕ) (ρ : Gal(Ω/F) →* Matrix.GeneralLinearGroup (Fin (n + 1)) K)
    (himage : ((homogeneousSymmetricGL (R := K) n).comp
      Matrix.SpecialLinearGroup.toGL).range ≤ ρ.range)
    {m : ℕ} [NeZero m] {ζ : Ω} (hζ : IsPrimitiveRoot ζ m)
    (g : SL(2, K)) :
    ∃ γ : Gal(Ω/F), γ ζ = ζ ∧
      ρ γ = homogeneousSymmetricGL n (Matrix.SpecialLinearGroup.toGL g) := by
  let ψ := (homogeneousSymmetricGL (R := K) n).comp Matrix.SpecialLinearGroup.toGL
  letI : Group.IsPerfect SL(2, K) := fieldSL2_isPerfect
  letI : Group.IsPerfect ψ.range := Group.IsPerfect.range ψ
  have h := perfect_subgroup_le_map_character_kernel ρ (hζ.autToPow F) ψ.range himage
  obtain ⟨γ, hγ, heγ⟩ := Subgroup.mem_map.mp (h (show ψ g ∈ ψ.range from ⟨g, rfl⟩))
  refine ⟨γ, ?_, heγ⟩
  have he : hζ.autToPow F γ = hζ.autToPow F 1 :=
    (show hζ.autToPow F γ = 1 from hγ).trans (map_one _).symm
  rw [← hζ.autToPow_spec F γ, he, hζ.autToPow_spec F 1]
  rfl

end
end Dubon2026
