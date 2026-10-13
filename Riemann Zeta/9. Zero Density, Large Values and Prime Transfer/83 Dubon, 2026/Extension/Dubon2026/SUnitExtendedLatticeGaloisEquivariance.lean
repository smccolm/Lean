import Dubon2026.SUnitExtendedLatticeProductEquiv

/-! # Original Galois compatibility of the integral diagonal extension

The original permutation action on the actual extended logarithmic
lattice is equivalent to the actual logarithmic-lattice action with a
trivial integer diagonal. This is the precise representation comparison
needed for DUB-17's invariant-diagonal Herbrand factor.
-/

namespace Dubon2026
noncomputable section
open NumberField IsDedekindDomain
open scoped NumberField Classical
variable (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L]
  (S : Finset (HeightOneSpectrum (𝓞 L)))
  (hS : ∀ (σ : Gal(L/K)) v, v ∈ S ↔ numberFieldGaloisPlaceEquiv K L σ v ∈ S)

/-- The original place-permutation action on the actual extended logarithmic lattice. -/
@[reducible]
def sUnitExtendedLogLatticeAction : DistribMulAction Gal(L/K) (sUnitExtendedLogLattice L S) := by
  letI := sUnitFullLogSpaceAction K L S hS
  exact {
    smul := fun σ z => ⟨σ • z.val, sUnitExtendedLogLattice_galois_mem L S K hS σ z.val z.property⟩
    one_smul := fun z => Subtype.ext (one_smul Gal(L/K) z.val)
    mul_smul := fun σ τ z => Subtype.ext (mul_smul σ τ z.val)
    smul_zero := fun σ => Subtype.ext (smul_zero σ)
    smul_add := fun σ z z' => Subtype.ext (smul_add σ z.val z'.val) }

/-- The original logarithmic-lattice action together with the actual invariant integer diagonal. -/
@[reducible]
def sUnitLatticeProdIntAction : DistribMulAction Gal(L/K) (sUnitFullLogLattice L S × ℤ) := by
  letI := sUnitFullLogLatticeAction L S K hS
  exact {
    smul := fun σ z => (σ • z.1, z.2)
    one_smul := fun z => Prod.ext (one_smul Gal(L/K) z.1) rfl
    mul_smul := fun σ τ z => Prod.ext (mul_smul σ τ z.1) rfl
    smul_zero := fun σ => Prod.ext (smul_zero σ) rfl
    smul_add := fun σ z z' => Prod.ext (smul_add σ z.1 z'.1) rfl }

/-- The original product-to-extended-lattice equivalence intertwines the actual original Galois actions. -/
theorem sUnitLatticeProdIntToExtended_galois (σ : Gal(L/K)) (x : sUnitFullLogLattice L S × ℤ) :
    letI : SMul Gal(L/K) (sUnitFullLogLattice L S × ℤ) :=
      (sUnitLatticeProdIntAction K L S hS).toMulAction.toSMul
    letI : SMul Gal(L/K) (sUnitExtendedLogLattice L S) :=
      (sUnitExtendedLogLatticeAction K L S hS).toMulAction.toSMul
    sUnitLatticeProdIntToExtended L S (σ • x) = σ • sUnitLatticeProdIntToExtended L S x := by
  letI := sUnitFullLogSpaceAction K L S hS
  letI := sUnitLogHyperplaneAction K L S hS
  let e := sUnitLogDiagonalEquiv L S
  apply Subtype.ext
  apply e.injective
  change e (e.symm (σ • x.1.val, (x.2 : ℝ))) = e (σ • e.symm (x.1.val, (x.2 : ℝ)))
  rw [e.apply_symm_apply]
  symm
  apply Prod.ext
  · change (sUnitLogDiagonalSplit L S (σ • e.symm (x.1.val, (x.2 : ℝ)))).1 = _
    rw [sUnitLogDiagonalSplit_fst_galois]
    change σ • (e (e.symm (x.1.val, (x.2 : ℝ)))).1 = σ • x.1.val
    rw [e.apply_symm_apply]
  · change sUnitLogCoordinateSum L S (σ • e.symm (x.1.val, (x.2 : ℝ))) = (x.2 : ℝ)
    rw [sUnitLogCoordinateSum_galois]
    exact congrArg Prod.snd (e.apply_symm_apply (x.1.val, (x.2 : ℝ)))

end
end Dubon2026
