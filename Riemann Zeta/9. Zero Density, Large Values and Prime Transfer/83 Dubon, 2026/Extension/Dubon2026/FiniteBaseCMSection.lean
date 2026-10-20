import Dubon2026.FiniteBaseCMComponent

/-! The actual real-place involution splits the source quadratic component
map. This is the original arithmetic splitting used to extend polarized
representations from the CM subgroup in the DUB-17 deformation chain. -/

namespace Dubon2026
open NumberField Algebra
open scoped NumberField
noncomputable section

/-- Retain the original rational algebra in the source arithmetic component splitting. -/
local instance finiteBaseCMSectionUnionAlgebra (a : 𝓞 ℚ) :
    Algebra ℚ (rationalUnramifiedExtension a) := (rationalUnramifiedExtension a).algebra'

variable (a : 𝓞 ℚ) (F : IntermediateField ℚ (rationalUnramifiedExtension a))
  [FiniteDimensional ℚ F] [IsTotallyReal F]

/-- The actual real-place involution gives a continuous map from the component group. -/
def finiteBaseCMComponentSection : Multiplicative (ZMod 2) →ₜ* finiteBaseArithmeticGaloisGroup a F :=
  ⟨{ toFun := fun z => if z.toAdd = 0 then 1 else finiteBaseRealConjugation a F
     map_one' := by simp
     map_mul' := by
       intro z w
       change (if z.toAdd + w.toAdd = (0 : ZMod 2) then 1 else finiteBaseRealConjugation a F) =
         (if z.toAdd = 0 then 1 else finiteBaseRealConjugation a F) *
           (if w.toAdd = 0 then 1 else finiteBaseRealConjugation a F)
       generalize z.toAdd = x
       generalize w.toAdd = y
       fin_cases x <;> fin_cases y
       · change (1 : finiteBaseArithmeticGaloisGroup a F) = 1 * 1
         exact (one_mul 1).symm
       · change finiteBaseRealConjugation a F = 1 * finiteBaseRealConjugation a F
         exact (one_mul _).symm
       · change finiteBaseRealConjugation a F = finiteBaseRealConjugation a F * 1
         exact (mul_one _).symm
       · change 1 = finiteBaseRealConjugation a F * finiteBaseRealConjugation a F
         exact (finiteBaseRealConjugation_mul_self a F).symm },
    continuous_of_discreteTopology⟩

variable (K : IntermediateField F (rationalUnramifiedExtension a))
  [IsQuadraticExtension F K] [IsTotallyComplex K]

/-- The original arithmetic involution is a section of the actual CM component character. -/
theorem finiteBaseCMComponentSection_component (z : Multiplicative (ZMod 2)) :
    finiteBaseQuadraticComponent a F K (finiteBaseCMComponentSection a F z) = z := by
  by_cases hz : z.toAdd = 0
  · have hz' : z = 1 := hz
    subst z
    exact map_one _
  · have hz' : z = Multiplicative.ofAdd (1 : ZMod 2) := by
      change z.toAdd = (1 : ZMod 2)
      generalize z.toAdd = x at hz ⊢
      fin_cases x
      · exact (hz rfl).elim
      · rfl
    subst z
    exact finiteBaseCMComponent_conjugation a F K

include K in
/-- The actual source component section is injective. -/
theorem finiteBaseCMComponentSection_injective :
    Function.Injective (finiteBaseCMComponentSection a F) :=
  (show Function.LeftInverse (finiteBaseQuadraticComponent a F K)
    (finiteBaseCMComponentSection a F) from finiteBaseCMComponentSection_component a F K).injective

end
end Dubon2026
