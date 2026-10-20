import Dubon2026.ResidualGL2CentralScalar
import Dubon2026.PolarizedAdjointSwitch
import Dubon2026.NumberFieldCyclotomicSquareWitness

/-! The genuine symmetric-power adjoint kernel does not fix the original
primitive root, under the source full-SL2 image and large-prime conditions.
This discharges the root-noncontainment input on DUB-17's auxiliary-prime chain. -/

namespace Dubon2026
noncomputable section
open Matrix

/-- The full adjoint group action commutes with restriction of the original representation. -/
theorem matrixAdjointRepresentation_comp_asGroupHom
    {G B ι R : Type} [Group G] [Group B] [Fintype ι] [DecidableEq ι] [CommRing R]
    (ρ : G →* B) (τ : B →* GeneralLinearGroup ι R) :
    (matrixAdjointRepresentation (τ.comp ρ)).asGroupHom =
      (matrixAdjointRepresentation τ).asGroupHom.comp ρ := by
  apply MonoidHom.ext
  intro g
  apply Units.ext
  apply LinearMap.ext
  intro X
  change (τ (ρ g)).val * X * (τ (ρ g⁻¹)).val =
    (τ (ρ g)).val * X * (τ ((ρ g)⁻¹)).val
  rw [map_inv]

/-- An actual scalar value of the original matrix representation acts trivially on its full adjoint. -/
theorem matrixAdjointRepresentation_asGroupHom_eq_one_of_scalar
    {G ι R : Type} [Group G] [Fintype ι] [DecidableEq ι] [CommRing R]
    (ρ : G →* GeneralLinearGroup ι R) (g : G) (u : Rˣ)
    (hg : ρ g = GeneralLinearGroup.scalar ι u) :
    (matrixAdjointRepresentation ρ).asGroupHom g = 1 := by
  apply Units.ext
  apply LinearMap.ext
  intro X
  change (ρ g).val * X * (ρ g⁻¹).val = X
  rw [map_inv, hg]
  simpa using
    matrixAdjoint_scalar u (1 : GeneralLinearGroup ι R) X

/-- Full SL2 image and a nontrivial character square supply an element of the actual symmetric-adjoint kernel outside the character kernel. -/
theorem symmetricAdjoint_kernel_not_le_character_kernel
    {G B k : Type} [Group G] [CommGroup B] [Field k]
    [NeZero (2 : k)] [NeZero (3 : k)]
    (ρ : G →* GeneralLinearGroup (Fin 2) k) (χ : G →* B) (n : ℕ)
    (himage : (SpecialLinearGroup.toGL (n := Fin 2) (R := k)).range ≤ ρ.range)
    (g : G) (hg : χ g ^ 2 ≠ 1) :
    ¬ (matrixAdjointRepresentation ((homogeneousSymmetricGL n).comp ρ)).asGroupHom.ker ≤
      χ.ker := by
  obtain ⟨σ, hχ, hρ⟩ := residualGL2_exists_scalar_character_square ρ χ himage g
  intro hle
  apply hg
  rw [← hχ]
  apply hle
  apply matrixAdjointRepresentation_asGroupHom_eq_one_of_scalar
    ((homogeneousSymmetricGL n).comp ρ) σ (GeneralLinearGroup.det (ρ g) ^ n)
  change homogeneousSymmetricGL n (ρ σ) = _
  rw [hρ, homogeneousSymmetricGL_scalar_ring]

/-- The primitive root lies outside the fixed field of the actual symmetric-power adjoint kernel; neither root noncontainment nor cyclotomic surjectivity is assumed. -/
theorem symmetricAdjoint_primitiveRoot_not_mem_fixedField
    (K Ω k : Type) [Field K] [NumberField K] [Field Ω]
    [Algebra K Ω] [IsGalois K Ω] [Field k]
    [NeZero (2 : k)] [NeZero (3 : k)]
    (ρ : Gal(Ω/K) →* GeneralLinearGroup (Fin 2) k) (n l : ℕ) [Fact l.Prime]
    {z : Ω} (hz : IsPrimitiveRoot z l)
    (himage : (SpecialLinearGroup.toGL (n := Fin 2) (R := k)).range ≤ ρ.range)
    (hlarge : 2 * Module.finrank ℚ K < l - 1) :
    z ∉ IntermediateField.fixedField
      (matrixAdjointRepresentation ((homogeneousSymmetricGL n).comp ρ)).asGroupHom.ker := by
  obtain ⟨g, hg⟩ := numberField_primitiveRoot_exists_character_square_ne_one K Ω l hz hlarge
  have hsep := symmetricAdjoint_kernel_not_le_character_kernel ρ (hz.autToPow K) n himage g hg
  intro hfixed
  apply hsep
  intro σ hσ
  rw [IntermediateField.mem_fixedField_iff] at hfixed
  have hzσ := hfixed σ hσ
  change hz.autToPow K σ = 1
  rw [← map_one (hz.autToPow K)]
  apply Units.ext
  apply ZMod.val_injective
  apply hz.pow_inj (ZMod.val_lt _) (ZMod.val_lt _)
  rw [hz.autToPow_spec K σ, hz.autToPow_spec K 1]
  exact hzσ

end
end Dubon2026
