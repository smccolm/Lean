import Dubon2026.CharacterDualTrivialLine
import Dubon2026.ContinuousScalarH1Coordinates
import Mathlib.LinearAlgebra.Dual.Basis

/-! # Actual dual basis coordinates of split coefficient modules

The character dual of an original trivial-action module has the original
scalar character action. Its dual basis coordinates are literal evaluation
after precomposition with the original basis-vector inclusions. These are
the coefficient identities needed for the right annihilator in DUB-17.
-/

namespace Dubon2026
noncomputable section

variable {k G ι : Type} [Field k] [Group G] [Finite ι]
  (A : Rep.{0} k G) (χ : G →* k) (b : Module.Basis ι k A)
  (htrivial : ∀ g a, A.ρ g a = a)

include htrivial in
omit [Finite ι] in
/-- The genuine character dual of the original split module has precisely
the original scalar character action on its actual linear functionals. -/
theorem trivialCoefficient_characterDual_scalar (g : G) (ℓ : characterDualCoefficientRep A χ) :
    (characterDualCoefficientRep A χ).ρ g ℓ = χ g • ℓ := by
  apply LinearMap.ext
  intro a
  change χ g * ℓ (A.ρ g⁻¹ a) = χ g * ℓ a
  rw [htrivial]

include htrivial in
omit [Finite ι] in
/-- Each actual basis-vector inclusion intertwines the two original trivial actions. -/
theorem trivialCoefficientBasisVector_equivariant (i : ι) (g : G) (t : k) :
    LinearMap.toSpanSingleton k A (b i) ((coefficientCharacterRep (1 : G →* k)).ρ g t) =
      A.ρ g (LinearMap.toSpanSingleton k A (b i) t) := by
  rw [htrivial]
  change (1 * t) • b i = t • b i
  rw [one_mul]

variable [DecidableEq ι]

/-- Dual basis coordinates are exactly original dual precomposition by a
basis-vector inclusion, followed by the actual scalar-dual evaluation. -/
theorem characterDualBasisCoordinate_evaluation (i : ι) (ℓ : characterDualCoefficientRep A χ) :
    characterDualTrivialLineEquiv χ
      (characterDualCoefficientMap (coefficientCharacterRep (1 : G →* k)) A χ
        (LinearMap.toSpanSingleton k A (b i)) ℓ) = b.dualBasis.coord i ℓ := by
  change ℓ ((1 : k) • b i) = b.dualBasis.repr ℓ i
  rw [one_smul]
  exact (b.dualBasis_repr ℓ i).symm

end
end Dubon2026
