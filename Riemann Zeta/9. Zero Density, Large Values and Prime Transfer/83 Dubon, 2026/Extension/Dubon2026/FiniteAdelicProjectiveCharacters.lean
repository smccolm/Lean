import Dubon2026.FiniteProjectiveGL2Topology
import Dubon2026.AdelicUnipotentCuspidality

/-! # Actual nonnegative characters of finite adelic GL2 with trivial scalar character -/

namespace Dubon2026

noncomputable section
open IsDedekindDomain Matrix Matrix.SpecialLinearGroup
open scoped MatrixGroups NNReal

/-- Every original character to a commutative monoid is unchanged by genuine group conjugation. -/
theorem commutative_character_conjugation {G A : Type*} [Group G] [CommMonoid A]
    (χ : G →* A) (g h : G) : χ (g * h * g⁻¹) = χ h := by
  calc
    χ (g * h * g⁻¹) = (χ g * χ g⁻¹) * χ h := by simp only [map_mul]; ac_rfl
    _ = χ h := by rw [← map_mul, mul_inv_cancel, map_one, one_mul]

/-- An original nonnegative real number whose square is one is exactly one. -/
theorem nnreal_mul_self_eq_one (x : ℝ≥0) (hx : x * x = 1) : x = 1 := by
  apply NNReal.coe_injective
  have he : (x : ℝ) * (x : ℝ) = 1 := by exact_mod_cast hx
  have hn : (0 : ℝ) ≤ (x : ℝ) := x.property
  change (x : ℝ) = 1
  nlinarith

/-- The literal original coordinate swap is an invertible matrix over every commutative ring. -/
def gl2CoordinateSwap {R : Type*} [CommRing R] : GeneralLinearGroup (Fin 2) R where
  val := !![0, 1; 1, 0]
  inv := !![0, 1; 1, 0]
  val_inv := by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  inv_val := by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

/-- Swapping an original unit diagonal and multiplying by that diagonal gives its actual scalar matrix. -/
theorem gl2CoordinateSwap_diagonal_scalar {R : Type*} [CommRing R] (u : Rˣ) :
    (gl2CoordinateSwap * gl2UnitFirstDiagonal u * gl2CoordinateSwap⁻¹) * gl2UnitFirstDiagonal u =
      GeneralLinearGroup.scalar (Fin 2) u := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [gl2CoordinateSwap, gl2UnitFirstDiagonal, GeneralLinearGroup.scalar,
      Matrix.scalar, Matrix.mul_apply, Fin.sum_univ_two]

/-- Actual reflection conjugation sends each original upper elementary matrix to its inverse. -/
theorem gl2Reflection_upper_inverse {R : Type*} [CommRing R] (t : R) :
    gl2UnitFirstDiagonal (-1 : Rˣ) * toGL (ringUpperUnipotent t) *
        (gl2UnitFirstDiagonal (-1 : Rˣ))⁻¹ = (toGL (ringUpperUnipotent t))⁻¹ := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [gl2UnitFirstDiagonal, ringUpperUnipotent, Matrix.mul_apply, Fin.sum_univ_two,
      toGL, coe_inv, Matrix.adjugate_fin_two]

/-- Actual reflection conjugation sends each original lower elementary matrix to its inverse. -/
theorem gl2Reflection_lower_inverse {R : Type*} [CommRing R] (t : R) :
    gl2UnitFirstDiagonal (-1 : Rˣ) * toGL (ringLowerUnipotent t) *
        (gl2UnitFirstDiagonal (-1 : Rˣ))⁻¹ = (toGL (ringLowerUnipotent t))⁻¹ := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [gl2UnitFirstDiagonal, ringLowerUnipotent, Matrix.mul_apply, Fin.sum_univ_two,
      toGL, coe_inv, Matrix.adjugate_fin_two]

/-- An actual nonnegative group character is one on any original element conjugate to its inverse. -/
theorem nnreal_character_eq_one_of_conjugate_inverse {G : Type*} [Group G]
    (χ : G →* ℝ≥0) (g h : G) (he : g * h * g⁻¹ = h⁻¹) : χ h = 1 := by
  have hc := commutative_character_conjugation χ g h
  rw [he] at hc
  apply nnreal_mul_self_eq_one
  calc
    χ h * χ h = χ (h⁻¹ * h) := by rw [map_mul, hc]
    _ = 1 := by rw [inv_mul_cancel, map_one]

/-- Every actual nonnegative character of finite adelic GL2 is one on the genuine special-linear subgroup. -/
theorem finiteAdelicGL2_character_specialLinear
    (χ : GeneralLinearGroup (Fin 2) (FiniteAdeleRing ℤ ℚ) →* ℝ≥0)
    (g : SL(2, FiniteAdeleRing ℤ ℚ)) : χ (toGL g) = 1 := by
  let ψ := χ.comp toGL
  have hu (t : FiniteAdeleRing ℤ ℚ) : ringUpperUnipotent t ∈ ψ.ker :=
    nnreal_character_eq_one_of_conjugate_inverse χ _ _ (gl2Reflection_upper_inverse t)
  have hl (t : FiniteAdeleRing ℤ ℚ) : ringLowerUnipotent t ∈ ψ.ker :=
    nnreal_character_eq_one_of_conjugate_inverse χ _ _ (gl2Reflection_lower_inverse t)
  exact finiteAdeleSL2_mem_of_unipotents ψ.ker hu hl g

/-- Every original nonnegative finite adelic character with trivial scalar action is the trivial character. -/
theorem finiteAdelicGL2_character_of_scalar
    (χ : GeneralLinearGroup (Fin 2) (FiniteAdeleRing ℤ ℚ) →* ℝ≥0)
    (hscalar : ∀ u : (FiniteAdeleRing ℤ ℚ)ˣ, χ (GeneralLinearGroup.scalar (Fin 2) u) = 1)
    (g : GeneralLinearGroup (Fin 2) (FiniteAdeleRing ℤ ℚ)) : χ g = 1 := by
  have hd (u : (FiniteAdeleRing ℤ ℚ)ˣ) : χ (gl2UnitFirstDiagonal u) = 1 := by
    apply nnreal_mul_self_eq_one
    have he := congrArg χ (gl2CoordinateSwap_diagonal_scalar u)
    rw [map_mul, commutative_character_conjugation, hscalar] at he
    exact he
  rw [gl2_eq_diagonal_mul_specialLinear g, map_mul, hd,
    finiteAdelicGL2_character_specialLinear, one_mul]

/-- Every actual nonnegative character of the genuine finite adelic projective group is trivial. -/
theorem finiteProjectiveGL2_nonnegative_character
    (χ : RationalFiniteProjectiveGL2 →* ℝ≥0) (g : RationalFiniteProjectiveGL2) : χ g = 1 := by
  obtain ⟨a, rfl⟩ := ProjGenLinGroup.mk_surjective g
  exact finiteAdelicGL2_character_of_scalar (χ.comp ProjGenLinGroup.mk)
    (fun u => by simp) a

end
end Dubon2026
