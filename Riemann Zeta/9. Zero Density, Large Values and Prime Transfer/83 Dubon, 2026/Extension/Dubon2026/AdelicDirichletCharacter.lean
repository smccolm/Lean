import Dubon2026.FiniteIdeleDirichletContinuity
import Dubon2026.RealDirichletSignCharacter
import Dubon2026.RationalAdeleRealFinite

/-! # The actual continuous Dirichlet character on the original full rational ideles -/

namespace Dubon2026

noncomputable section
open NumberField IsDedekindDomain

/-- The original real unit coordinate of a genuine rational idele. -/
def rationalIdeleRealHom : (AdeleRing ℤ ℚ)ˣ →* ℝˣ :=
  Units.map (((RingHom.fst ℝ (FiniteAdeleRing ℤ ℚ)).comp
    rationalAdeleRealFiniteRingEquiv.toRingHom).toMonoidHom)

/-- The original finite unit coordinate of that same genuine rational idele. -/
def rationalIdeleFiniteHom : (AdeleRing ℤ ℚ)ˣ →* (FiniteAdeleRing ℤ ℚ)ˣ :=
  Units.map (((RingHom.snd ℝ (FiniteAdeleRing ℤ ℚ)).comp
    rationalAdeleRealFiniteRingEquiv.toRingHom).toMonoidHom)

/-- The actual real idele coordinate is continuous. -/
theorem rationalIdeleRealHom_continuous : Continuous rationalIdeleRealHom :=
  Continuous.units_map _ (continuous_fst.comp rationalAdeleRealFiniteRingEquiv_continuous)

/-- The actual finite idele coordinate is continuous. -/
theorem rationalIdeleFiniteHom_continuous : Continuous rationalIdeleFiniteHom :=
  Continuous.units_map _ (continuous_snd.comp rationalAdeleRealFiniteRingEquiv_continuous)

/-- Principal rational units retain their original real value in the actual idele coordinates. -/
theorem rationalIdeleRealHom_rational (q : ℚˣ) :
    rationalIdeleRealHom (Units.map (algebraMap ℚ (AdeleRing ℤ ℚ)).toMonoidHom q) =
      Units.map (Rat.castHom ℝ).toMonoidHom q := by
  apply Units.ext
  exact congrArg Prod.fst (rationalAdeleRealFiniteRingEquiv_algebraMap q.val)

/-- Principal rational units retain their original finite diagonal in the actual idele coordinates. -/
theorem rationalIdeleFiniteHom_rational (q : ℚˣ) :
    rationalIdeleFiniteHom (Units.map (algebraMap ℚ (AdeleRing ℤ ℚ)).toMonoidHom q) =
      Units.map (algebraMap ℚ (FiniteAdeleRing ℤ ℚ)).toMonoidHom q := by
  apply Units.ext
  exact congrArg Prod.snd (rationalAdeleRealFiniteRingEquiv_algebraMap q.val)

variable {D : ℕ} [NeZero D] (χ : DirichletCharacter ℂ D)

/-- The product of the original real sign and finite residue characters at the original idele coordinates. -/
def adelicDirichletCharacter : (AdeleRing ℤ ℚ)ˣ →* ℂ :=
  ((realDirichletSignCharacter χ).comp rationalIdeleRealHom) *
    ((finiteIdeleDirichletCharacter χ).comp rationalIdeleFiniteHom)

/-- The genuine full character evaluates the two actual coordinates of the same original idele. -/
theorem adelicDirichletCharacter_apply (a : (AdeleRing ℤ ℚ)ˣ) :
    adelicDirichletCharacter χ a = realDirichletSignCharacter χ (rationalIdeleRealHom a) *
      finiteIdeleDirichletCharacter χ (rationalIdeleFiniteHom a) := rfl

/-- The constructed full Dirichlet character is continuous on the actual original ideles. -/
theorem adelicDirichletCharacter_continuous : Continuous (adelicDirichletCharacter χ) :=
  ((realDirichletSignCharacter_continuous χ).comp rationalIdeleRealHom_continuous).mul
    ((finiteIdeleDirichletCharacter_continuous χ).comp rationalIdeleFiniteHom_continuous)

/-- The actual full character is trivial on positive principal rational units. -/
theorem adelicDirichletCharacter_positive_rational (q : ℚˣ) (hq : 0 < q.val) :
    adelicDirichletCharacter χ (Units.map (algebraMap ℚ (AdeleRing ℤ ℚ)).toMonoidHom q) = 1 := by
  rw [adelicDirichletCharacter_apply, rationalIdeleRealHom_rational, rationalIdeleFiniteHom_rational]
  have hr : 0 < (Units.map (Rat.castHom ℝ).toMonoidHom q).val := by
    change (0 : ℝ) < (q.val : ℝ)
    exact_mod_cast hq
  rw [realDirichletSignCharacter_positive χ _ hr, one_mul]
  have he : Units.mk0 q.val (ne_of_gt hq) = q := Units.ext rfl
  simpa only [he] using finiteIdeleDirichletCharacter_positive_rational χ q.val hq

end
end Dubon2026
