import Dubon2026.CanonicalAdelicCentralCharacter
import Dubon2026.AdelicProjectiveHaar

/-! # Actual scalar pairs in canonical full adelic coordinates -/

namespace Dubon2026

noncomputable section
open NumberField IsDedekindDomain Matrix Matrix.SpecialLinearGroup
open scoped MatrixGroups

/-- The original full adelic unit with a prescribed actual real unit and finite idele. -/
def rationalAdeleUnitPair (r : ℝˣ) (a : (FiniteAdeleRing ℤ ℚ)ˣ) : (AdeleRing ℤ ℚ)ˣ :=
  Units.map rationalAdeleRealFiniteRingEquiv.symm.toMonoidHom (MulEquiv.prodUnits.symm (r, a))

/-- The genuine scalar associated to an original adelic unit pair has precisely its real and finite scalar matrices. -/
theorem rationalAdeleUnitPair_scalar_coordinates (r : ℝˣ) (a : (FiniteAdeleRing ℤ ℚ)ˣ) :
    rationalAdelicGL2RealFiniteEquiv (GeneralLinearGroup.scalar (Fin 2) (rationalAdeleUnitPair r a)) =
      (GeneralLinearGroup.scalar (Fin 2) r, GeneralLinearGroup.scalar (Fin 2) a) := by
  have hr : Units.map ((RingHom.fst ℝ (FiniteAdeleRing ℤ ℚ)).comp
      rationalAdeleRealFiniteRingEquiv.toRingHom).toMonoidHom (rationalAdeleUnitPair r a) = r := by
    apply Units.ext
    change (rationalAdeleRealFiniteRingEquiv
      (rationalAdeleRealFiniteRingEquiv.symm (r.val, a.val))).1 = r.val
    rw [RingEquiv.apply_symm_apply]
  have ha : Units.map ((RingHom.snd ℝ (FiniteAdeleRing ℤ ℚ)).comp
      rationalAdeleRealFiniteRingEquiv.toRingHom).toMonoidHom (rationalAdeleUnitPair r a) = a := by
    apply Units.ext
    change (rationalAdeleRealFiniteRingEquiv
      (rationalAdeleRealFiniteRingEquiv.symm (r.val, a.val))).2 = a.val
    rw [RingEquiv.apply_symm_apply]
  rw [rationalAdelicGL2RealFiniteEquiv_scalar, hr, ha]

/-- Actual trivial full scalar invariance gives the original simultaneous real and finite scalar identity. -/
theorem adelicFunction_scalar_pair
    (v : GeneralLinearGroup (Fin 2) (AdeleRing ℤ ℚ) → ℂ)
    (hv : ∀ u : (AdeleRing ℤ ℚ)ˣ, ∀ g, v (GeneralLinearGroup.scalar (Fin 2) u * g) = v g)
    (r : ℝˣ) (a : (FiniteAdeleRing ℤ ℚ)ˣ) (g : GeneralLinearGroup (Fin 2) ℝ)
    (x : GeneralLinearGroup (Fin 2) (FiniteAdeleRing ℤ ℚ)) :
    v (rationalAdelicGL2RealFiniteEquiv.symm
      (GeneralLinearGroup.scalar (Fin 2) r * g, GeneralLinearGroup.scalar (Fin 2) a * x)) =
        v (rationalAdelicGL2RealFiniteEquiv.symm (g, x)) := by
  have he : rationalAdelicGL2RealFiniteEquiv.symm
      (GeneralLinearGroup.scalar (Fin 2) r * g, GeneralLinearGroup.scalar (Fin 2) a * x) =
      GeneralLinearGroup.scalar (Fin 2) (rationalAdeleUnitPair r a) *
        rationalAdelicGL2RealFiniteEquiv.symm (g, x) := by
    apply rationalAdelicGL2RealFiniteEquiv.injective
    rw [MulEquiv.apply_symm_apply, map_mul, rationalAdeleUnitPair_scalar_coordinates,
      MulEquiv.apply_symm_apply]
    rfl
  rw [he]
  exact hv _ _

/-- Actual negative identity in the real special-linear group is the original scalar action after its general-linear embedding. -/
theorem realSL2_toGL_neg_scalar (g : SL(2, ℝ)) :
    toGL (-g) = GeneralLinearGroup.scalar (Fin 2) (-1 : ℝˣ) * toGL g := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [GeneralLinearGroup.scalar, Matrix.scalar, toGL, coe_neg]

end
end Dubon2026
