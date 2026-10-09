import Dubon2026.AdelicDirichletUnitary
import Dubon2026.RationalIdeleCoordinates

/-! # Genuine quadratic and integral values of the original full Dirichlet idele character -/

namespace Dubon2026

noncomputable section
open NumberField IsDedekindDomain

/-- An actual quadratic Dirichlet character takes square-one values on every genuine residue unit. -/
theorem dirichlet_quadratic_unit_sq {D : ℕ} (χ : DirichletCharacter ℂ D) (hχ : χ.IsQuadratic)
    (u : (ZMod D)ˣ) : χ u.val ^ 2 = 1 := by
  rcases hχ u.val with hz | ho | hm
  · have hn := χ.unit_norm_eq_one u
    rw [hz, norm_zero] at hn
    exact (zero_ne_one hn).elim
  · rw [ho, one_pow]
  · rw [hm]
    norm_num

/-- The actual finite idele character of a quadratic Dirichlet character has square-one values on all original finite ideles. -/
theorem finiteIdeleDirichletCharacter_quadratic {D : ℕ} [NeZero D]
    (χ : DirichletCharacter ℂ D) (hχ : χ.IsQuadratic) (a : (FiniteAdeleRing ℤ ℚ)ˣ) :
    finiteIdeleDirichletCharacter χ a ^ 2 = 1 := by
  change (χ (finiteAdeleResidue D (finiteIdeleIntegralUnitHom a).val))⁻¹ ^ 2 = 1
  have hs : χ (finiteAdeleResidue D (finiteIdeleIntegralUnitHom a).val) ^ 2 = 1 :=
    dirichlet_quadratic_unit_sq χ hχ
      (Units.map (finiteAdeleResidue D).toMonoidHom (finiteIdeleIntegralUnitHom a))
  rw [inv_pow, hs, inv_one]

/-- The actual real sign factor of a quadratic Dirichlet character has square-one values on every original real unit. -/
theorem realDirichletSignCharacter_quadratic {D : ℕ}
    (χ : DirichletCharacter ℂ D) (hχ : χ.IsQuadratic) (r : ℝˣ) :
    realDirichletSignCharacter χ r ^ 2 = 1 :=
  dirichlet_quadratic_unit_sq χ hχ (Units.map (SignType.castHom (α := ZMod D)).toMonoidHom
    (Units.map (signHom (α := ℝ)).toMonoidHom r))

/-- The genuine original full Dirichlet idele character is quadratic when its original Dirichlet character is quadratic. -/
theorem adelicDirichletCharacter_quadratic {D : ℕ} [NeZero D]
    (χ : DirichletCharacter ℂ D) (hχ : χ.IsQuadratic) (a : (AdeleRing ℤ ℚ)ˣ) :
    adelicDirichletCharacter χ a ^ 2 = 1 := by
  rw [adelicDirichletCharacter_apply, mul_pow, realDirichletSignCharacter_quadratic χ hχ,
    finiteIdeleDirichletCharacter_quadratic χ hχ, mul_one]

/-- The full original Dirichlet idele character restricts to exactly its constructed finite character at the actual finite embedding. -/
theorem adelicDirichletCharacter_finite {D : ℕ} [NeZero D]
    (χ : DirichletCharacter ℂ D) (a : (FiniteAdeleRing ℤ ℚ)ˣ) :
    adelicDirichletCharacter χ (rationalIdeleFiniteEmbedding a) = finiteIdeleDirichletCharacter χ a := by
  have hc : rationalIdeleCoordinateEquiv (rationalIdeleFiniteEmbedding a) = (1, a) :=
    rationalIdeleCoordinateEquiv.apply_symm_apply _
  have hr : rationalIdeleRealHom (rationalIdeleFiniteEmbedding a) = 1 := congrArg Prod.fst hc
  have hf : rationalIdeleFiniteHom (rationalIdeleFiniteEmbedding a) = a := congrArg Prod.snd hc
  rw [adelicDirichletCharacter_apply, hr, hf, map_one, one_mul]

/-- On every actual embedded integral finite idele, the full original character has precisely the inverse original Dirichlet residue value. -/
theorem adelicDirichletCharacter_integral {D : ℕ} [NeZero D]
    (χ : DirichletCharacter ℂ D) (u : finiteAdeleIntegerSubringˣ) :
    adelicDirichletCharacter χ (rationalIdeleFiniteEmbedding
      (Units.map finiteAdeleIntegerSubring.subtype.toMonoidHom u)) = (χ (finiteAdeleResidue D u.val))⁻¹ := by
  rw [adelicDirichletCharacter_finite, finiteIdeleDirichletCharacter_integral]

end
end Dubon2026
