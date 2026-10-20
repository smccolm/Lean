import Dubon2026.IntegralDominantHighestVector

/-! The exact highest-weight character in the original induced action.
Base change of the actual Borel matrix and its diagonal units converts
the all-algebra covariance into an equality in the original module,
using the original generic-matrix evaluation identity. No replacement
representation or highest-weight certificate is assumed.
-/

namespace Dubon2026
noncomputable section
open Matrix

universe u
variable (R A : Type u) [CommRing R] [CommRing A] [Algebra R A] (n : ℕ)

/-- The original Borel matrix base changed to the actual coefficient algebra. -/
def integralWeightBorelBaseChange (b : generalLinearBorel R n) : generalLinearBorel A n :=
  ⟨GeneralLinearGroup.map (algebraMap R A) b.val, by
    intro i j hij
    change algebraMap R A (b.val.val i j) = 0
    rw [b.property hij, map_zero]⟩

/-- The original Borel diagonal units commute with actual coefficient base change. -/
theorem integralWeightBorelBaseChange_diagonal (b : generalLinearBorel R n) (i : Fin n) :
    generalLinearBorelDiagonalUnit (integralWeightBorelBaseChange R A n b) i =
      Units.map (algebraMap R A).toMonoidHom (generalLinearBorelDiagonalUnit b i) := by
  apply Units.ext
  rfl

/-- The exact highest-weight character commutes with original coefficient base change, including negative weights. -/
theorem integralWeightBorelBaseChange_character (lam : Fin n → ℤ) (b : generalLinearBorel R n) :
    (∏ i : Fin n, generalLinearBorelDiagonalUnit (integralWeightBorelBaseChange R A n b) i ^ lam i) =
      Units.map (algebraMap R A).toMonoidHom
        (∏ i : Fin n, generalLinearBorelDiagonalUnit b i ^ lam i) := by
  simp only [map_prod, map_zpow, integralWeightBorelBaseChange_diagonal]

/-- In the actual original representation, the constructed highest vector is an eigenvector for every original upper-Borel element with precisely the source highest-weight character. -/
theorem integralDominantHighestVector_action {m : ℕ}
    (lam : Fin (m + 1) → ℤ) (hlam : Antitone lam) (b : generalLinearBorel R (m + 1)) :
    generalLinearIntegralInducedRepresentation R (m + 1) lam b.val
      (integralDominantHighestVector R lam hlam) =
      ((∏ i : Fin (m + 1), generalLinearBorelDiagonalUnit b i ^ lam i : Rˣ) : R) •
        integralDominantHighestVector R lam hlam := by
  apply Subtype.ext
  change generalLinearRegularEval
      (generalLinearRegularGeneric R (m + 1) *
        GeneralLinearGroup.map (algebraMap R (GeneralLinearRegularFunctions R (m + 1))) b.val)
      (integralDominantHighestRegular R lam) =
      ((∏ i : Fin (m + 1), generalLinearBorelDiagonalUnit b i ^ lam i : Rˣ) : R) •
        integralDominantHighestRegular R lam
  have he := integralDominantHighestRegular_right_borel R lam hlam
    (generalLinearRegularGeneric R (m + 1))
    (integralWeightBorelBaseChange R (GeneralLinearRegularFunctions R (m + 1)) (m + 1) b)
  rw [integralWeightBorelBaseChange_character, generalLinearRegularEval_generic] at he
  simpa only [integralWeightBorelBaseChange, Units.coe_map, MonoidHom.coe_coe,
    AlgHom.id_apply, Algebra.smul_def] using he

end
end Dubon2026
