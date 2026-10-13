import Dubon2026.SUnitExtendedLogLattice

/-! # The original extended logarithmic lattice is the original lattice times integers

The exact coordinate splitting and proved membership criterion give an
integer-linear equivalence with the original full logarithmic lattice
and one integral diagonal coordinate. This is the original-object
identification needed to extract the diagonal cohomology factor from
DUB-17's finite-index permutation calculation.
-/

namespace Dubon2026
noncomputable section
open NumberField IsDedekindDomain
open scoped NumberField Classical
variable (L : Type) [Field L] [NumberField L]
  (S : Finset (HeightOneSpectrum (𝓞 L)))

/-- Insert an original lattice vector and integer diagonal through the exact inverse splitting. -/
def sUnitLatticeProdIntToExtended : (sUnitFullLogLattice L S × ℤ) →ₗ[ℤ]
    sUnitExtendedLogLattice L S := by
  let e := sUnitLogDiagonalEquiv L S
  let f := (e.symm.restrictScalars ℤ).toLinearMap.comp
    ((sUnitFullLogLattice L S).subtype.prodMap (Int.castAddHom ℝ).toIntLinearMap)
  exact f.codRestrict _ (fun z => by
    change e (e.symm (z.1.val, (z.2 : ℝ))) ∈ sUnitLogProductLattice L S
    rw [e.apply_symm_apply, sUnitLogProductLattice_mem]
    exact ⟨z.1.property, z.2, rfl⟩)

/-- The original product-to-extended-lattice map retains the exact original inverse coordinate splitting. -/
theorem sUnitLatticeProdIntToExtended_val (z : sUnitFullLogLattice L S × ℤ) :
    (sUnitLatticeProdIntToExtended L S z).val =
      (sUnitLogDiagonalEquiv L S).symm (z.1.val, (z.2 : ℝ)) := rfl

/-- The actual lattice and integer diagonal give unique original extended-lattice vectors. -/
theorem sUnitLatticeProdIntToExtended_bijective : Function.Bijective (sUnitLatticeProdIntToExtended L S) := by
  let e := sUnitLogDiagonalEquiv L S
  constructor
  · intro x y h
    have hp := congrArg (fun z : sUnitExtendedLogLattice L S => e z.val) h
    change e (e.symm (x.1.val, (x.2 : ℝ))) = e (e.symm (y.1.val, (y.2 : ℝ))) at hp
    simp only [e.apply_symm_apply] at hp
    exact Prod.ext (Subtype.ext (congrArg Prod.fst hp))
      (Int.cast_injective (congrArg Prod.snd hp))
  · intro z
    obtain ⟨hz, n, hn⟩ := (sUnitExtendedLogLattice_mem L S z.val).mp z.property
    refine ⟨(⟨(sUnitLogDiagonalSplit L S z.val).1, hz⟩, n), ?_⟩
    apply Subtype.ext
    apply e.injective
    change e (e.symm ((sUnitLogDiagonalSplit L S z.val).1, (n : ℝ))) = e z.val
    rw [e.apply_symm_apply]
    exact Prod.ext rfl hn

/-- The original extended lattice is integrally equivalent to its original logarithmic lattice and integer diagonal. -/
def sUnitExtendedLatticeProductEquiv : (sUnitFullLogLattice L S × ℤ) ≃ₗ[ℤ]
    sUnitExtendedLogLattice L S :=
  LinearEquiv.ofBijective (sUnitLatticeProdIntToExtended L S) (sUnitLatticeProdIntToExtended_bijective L S)

end
end Dubon2026
