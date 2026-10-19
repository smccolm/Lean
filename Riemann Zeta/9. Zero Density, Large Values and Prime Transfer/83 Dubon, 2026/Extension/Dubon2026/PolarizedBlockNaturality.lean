import Dubon2026.PolarizedBlockFaithfulness

/-! The faithful polarized matrix realization is compatible with original
coefficient reduction. This connects the same residual target to the
existing fixed-residual framed-ring construction in DUB-17's CM branch. -/

namespace Dubon2026
open Matrix

variable {R S ι : Type*} [CommRing R] [CommRing S] [Fintype ι] [DecidableEq ι]

/-- Coefficient change preserves the actual diagonal blocks. -/
theorem polarizedBlockDiagonal_map (f : R →+* S) (g h : GeneralLinearGroup ι R) :
    GeneralLinearGroup.map f (polarizedBlockDiagonal g h) =
      polarizedBlockDiagonal (GeneralLinearGroup.map f g) (GeneralLinearGroup.map f h) := by
  apply Units.ext
  ext i j
  cases i <;> cases j <;> simp [GeneralLinearGroup.map, polarizedBlockDiagonal]

/-- Coefficient change preserves the original block-exchange matrix. -/
theorem polarizedBlockSwap_map (f : R →+* S) :
    GeneralLinearGroup.map f (polarizedBlockSwap (ι := ι)) = polarizedBlockSwap := by
  apply Units.ext
  ext i j
  cases i <;> cases j <;>
    simp [GeneralLinearGroup.map, polarizedBlockSwap, Matrix.one_apply, apply_ite f]

/-- The identity-component matrix realization commutes with original reduction. -/
theorem polarizedIdentityBlockRepresentation_map (f : R →+* S)
    (x : GeneralLinearGroup ι R × Rˣ) :
    GeneralLinearGroup.map f (polarizedIdentityBlockRepresentation x) =
      polarizedIdentityBlockRepresentation (polarizedIdentityCoefficientMap f x) := by
  change GeneralLinearGroup.map f (polarizedBlockDiagonal x.1 (polarizedSwitch x).1) = _
  rw [polarizedBlockDiagonal_map]
  have hs := congrArg Prod.fst (polarizedSwitch_coefficientMap f x)
  change GeneralLinearGroup.map f (polarizedSwitch x).1 = _ at hs
  rw [hs]
  rfl

/-- The same faithful polarized representation specializes to the original residual one. -/
theorem polarizedBlockRepresentation_map (f : R →+* S) (x : PolarizedGaloisGroup ι R) :
    GeneralLinearGroup.map f (polarizedBlockRepresentation x) =
      polarizedBlockRepresentation (polarizedCoefficientMap f x) := by
  change GeneralLinearGroup.map f
      (polarizedIdentityBlockRepresentation x.left * polarizedComponentBlockRepresentation x.right) =
    polarizedIdentityBlockRepresentation (polarizedIdentityCoefficientMap f x.left) *
      polarizedComponentBlockRepresentation x.right
  rw [map_mul, polarizedIdentityBlockRepresentation_map]
  congr 1
  change GeneralLinearGroup.map f (if x.right.toAdd = 0 then 1 else polarizedBlockSwap) =
    (if x.right.toAdd = 0 then 1 else polarizedBlockSwap)
  split_ifs
  · exact map_one _
  · exact polarizedBlockSwap_map f

/-- Equality of reductions can be checked in the original faithful doubled matrices. -/
theorem polarizedCoefficientMap_eq_iff_block [Nonempty ι] [Nontrivial S]
    (f : R →+* S) (x : PolarizedGaloisGroup ι R) (y : PolarizedGaloisGroup ι S) :
    polarizedCoefficientMap f x = y ↔
      GeneralLinearGroup.map f (polarizedBlockRepresentation x) = polarizedBlockRepresentation y := by
  rw [polarizedBlockRepresentation_map]
  exact polarizedBlockRepresentation_injective.eq_iff.symm

end Dubon2026
