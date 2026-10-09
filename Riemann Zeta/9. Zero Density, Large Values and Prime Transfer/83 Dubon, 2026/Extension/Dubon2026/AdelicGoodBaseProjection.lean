import Dubon2026.FiniteAdelicRestrictionHom
import Dubon2026.AdelicGoodLevelBaseDecomposition
import Dubon2026.AdelicFiniteProductRealCoordinate

/-! # Actual canonical good-place and fixed-base components of the original full adelic group -/

namespace Dubon2026

noncomputable section
open IsDedekindDomain Matrix

/-- The actual finite coordinate of the original real-times-finite adelic group. -/
def adelicFiniteCoordinateHom : RationalAdelicGL2 →* GeneralLinearGroup (Fin 2) (FiniteAdeleRing ℤ ℚ) :=
  (MonoidHom.snd (GeneralLinearGroup (Fin 2) ℝ) (GeneralLinearGroup (Fin 2) (FiniteAdeleRing ℤ ℚ))).comp
    rationalAdelicGL2RealFiniteEquiv.toMonoidHom

/-- The actual good-place part retains every genuine good local coordinate and has identity real and bad coordinates. -/
def adelicGoodPartHom (N : ℕ) : RationalAdelicGL2 →* RationalAdelicGL2 :=
  rationalAdelicFiniteGL2Embedding.comp
    ((finiteAdelicGL2OnHom {v | IsGoodAdelicPlace N v}).comp adelicFiniteCoordinateHom)

/-- The actual fixed-base part retains the original real coordinate and every original bad finite coordinate. -/
def adelicBasePartHom (N : ℕ) : RationalAdelicGL2 →* RationalAdelicGL2 :=
  rationalAdelicGL2RealFiniteEquiv.symm.toMonoidHom.comp
    (((MonoidHom.fst (GeneralLinearGroup (Fin 2) ℝ) (GeneralLinearGroup (Fin 2) (FiniteAdeleRing ℤ ℚ))).comp
        rationalAdelicGL2RealFiniteEquiv.toMonoidHom).prod
      ((finiteAdelicGL2OnHom {v | ¬ IsGoodAdelicPlace N v}).comp adelicFiniteCoordinateHom))

/-- The actual good component has exactly its original retained finite coordinates and identity real coordinate. -/
theorem adelicGoodPartHom_coordinates (N : ℕ) (a : RationalAdelicGL2) :
    rationalAdelicGL2RealFiniteEquiv (adelicGoodPartHom N a) =
      (1, finiteAdelicGL2On {v | IsGoodAdelicPlace N v} (rationalAdelicGL2RealFiniteEquiv a).2) :=
  rationalAdelicFiniteGL2Embedding_coordinates _

/-- The actual base component has exactly the original real and retained bad-place coordinates. -/
theorem adelicBasePartHom_coordinates (N : ℕ) (a : RationalAdelicGL2) :
    rationalAdelicGL2RealFiniteEquiv (adelicBasePartHom N a) =
      ((rationalAdelicGL2RealFiniteEquiv a).1,
        finiteAdelicGL2On {v | ¬ IsGoodAdelicPlace N v} (rationalAdelicGL2RealFiniteEquiv a).2) :=
  rationalAdelicGL2RealFiniteEquiv.apply_symm_apply _

/-- At every genuine good place the actual good part is precisely the original matrix coordinate. -/
theorem adelicGoodPartHom_good (N : ℕ) (a : RationalAdelicGL2) (v : HeightOneSpectrum ℤ)
    (hv : IsGoodAdelicPlace N v) : adelicPlaceGL2Hom v (adelicGoodPartHom N a) = adelicPlaceGL2Hom v a := by
  rw [adelicPlaceGL2Hom_apply, adelicGoodPartHom_coordinates]
  exact finiteAdelicGL2On_mem _ _ v hv

/-- At every genuine bad place the actual good part has identity coordinate. -/
theorem adelicGoodPartHom_bad (N : ℕ) (a : RationalAdelicGL2) (v : HeightOneSpectrum ℤ)
    (hv : ¬ IsGoodAdelicPlace N v) : adelicPlaceGL2Hom v (adelicGoodPartHom N a) = 1 := by
  rw [adelicPlaceGL2Hom_apply, adelicGoodPartHom_coordinates]
  exact finiteAdelicGL2On_not_mem _ _ v hv

/-- At every genuine good place the actual base part has identity coordinate. -/
theorem adelicBasePartHom_good (N : ℕ) (a : RationalAdelicGL2) (v : HeightOneSpectrum ℤ)
    (hv : IsGoodAdelicPlace N v) : adelicPlaceGL2Hom v (adelicBasePartHom N a) = 1 := by
  rw [adelicPlaceGL2Hom_apply, adelicBasePartHom_coordinates]
  exact finiteAdelicGL2On_not_mem _ _ v (fun h => h hv)

/-- The actual canonical base part belongs to the original fixed base subgroup. -/
theorem adelicBasePartHom_mem (N : ℕ) (a : RationalAdelicGL2) : adelicBasePartHom N a ∈ adelicRestrictedBaseGroup N :=
  (adelicRestrictedBaseGroup_mem_iff N _).mpr (adelicBasePartHom_good N a)

/-- The original canonical base projection lands in the genuine fixed-base group, with its literal original matrices. -/
def adelicBaseProjection (N : ℕ) : RationalAdelicGL2 →* adelicRestrictedBaseGroup N :=
  (adelicBasePartHom N).codRestrict (adelicRestrictedBaseGroup N) (adelicBasePartHom_mem N)

/-- Every original full adelic matrix is exactly its genuine good-place part times its canonical fixed-base part. -/
theorem adelicGoodPart_mul_base (N : ℕ) (a : RationalAdelicGL2) :
    adelicGoodPartHom N a * (adelicBaseProjection N a).val = a := by
  apply rationalAdelicGL2RealFiniteEquiv.injective
  change rationalAdelicGL2RealFiniteEquiv (adelicGoodPartHom N a * adelicBasePartHom N a) = _
  rw [map_mul, adelicGoodPartHom_coordinates, adelicBasePartHom_coordinates]
  apply Prod.ext
  · exact one_mul _
  · exact finiteAdelicGL2On_mul_compl {v | IsGoodAdelicPlace N v} _

/-- The actual good-place and fixed-base parts commute for any two original adelic matrices. -/
theorem adelicGoodPart_base_commute (N : ℕ) (a b : RationalAdelicGL2) :
    Commute (adelicGoodPartHom N a) (adelicBaseProjection N b).val := by
  apply rationalAdelicGL2RealFiniteEquiv.injective
  change rationalAdelicGL2RealFiniteEquiv (adelicGoodPartHom N a * adelicBasePartHom N b) =
    rationalAdelicGL2RealFiniteEquiv (adelicBasePartHom N b * adelicGoodPartHom N a)
  rw [map_mul, map_mul, adelicGoodPartHom_coordinates, adelicBasePartHom_coordinates]
  apply Prod.ext
  · exact (one_mul _).trans (mul_one _).symm
  · exact (finiteAdelicGL2On_compl_commute {v | IsGoodAdelicPlace N v} _ _).eq

/-- An actual fixed-base matrix has trivial original good-place part. -/
theorem adelicGoodPartHom_base (N : ℕ) (b : adelicRestrictedBaseGroup N) : adelicGoodPartHom N b.val = 1 := by
  apply adelicRealFiniteCoordinates_ext
  · rw [adelicGoodPartHom_coordinates, map_one]
    rfl
  · intro v
    rw [map_one]
    by_cases hv : IsGoodAdelicPlace N v
    · rw [adelicGoodPartHom_good N _ v hv]
      exact adelicRestrictedBaseGroup_place b v hv
    · exact adelicGoodPartHom_bad N _ v hv

/-- The canonical actual base projection is the identity on every original base matrix. -/
theorem adelicBaseProjection_base (N : ℕ) (b : adelicRestrictedBaseGroup N) : adelicBaseProjection N b.val = b := by
  apply Subtype.ext
  have h := adelicGoodPart_mul_base N b.val
  rw [adelicGoodPartHom_base, one_mul] at h
  exact h

/-- An original matrix with identity real and bad coordinates is exactly its genuine good-place part. -/
theorem adelicGoodPartHom_eq_of_support (N : ℕ) (a : RationalAdelicGL2)
    (hReal : (rationalAdelicGL2RealFiniteEquiv a).1 = 1)
    (hBad : ∀ v, ¬ IsGoodAdelicPlace N v → adelicPlaceGL2Hom v a = 1) : adelicGoodPartHom N a = a := by
  apply adelicRealFiniteCoordinates_ext
  · rw [adelicGoodPartHom_coordinates]
    exact hReal.symm
  · intro v
    by_cases hv : IsGoodAdelicPlace N v
    · exact adelicGoodPartHom_good N a v hv
    · exact (adelicGoodPartHom_bad N a v hv).trans (hBad v hv).symm

/-- Every original matrix supported only at good finite places commutes with every true fixed-base matrix. -/
theorem adelicGoodSupported_base_commute (N : ℕ) (a : RationalAdelicGL2)
    (hReal : (rationalAdelicGL2RealFiniteEquiv a).1 = 1)
    (hBad : ∀ v, ¬ IsGoodAdelicPlace N v → adelicPlaceGL2Hom v a = 1) (b : adelicRestrictedBaseGroup N) :
    Commute a b.val := by
  have h := adelicGoodPart_base_commute N a b.val
  rw [adelicGoodPartHom_eq_of_support N a hReal hBad, adelicBaseProjection_base] at h
  exact h

end
end Dubon2026
