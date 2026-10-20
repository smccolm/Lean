import Dubon2026.NumberFieldFiniteAdelicLocalGLMap
import Dubon2026.CMFiniteAdelicUnitaryGroup

/-! # The actual conjugate-place support of local adelic matrices

The CM involution moves a one-place matrix to its actual conjugate
place. Distinctness of these places will make the two Hermitian factors
commute, constructing the source split unitary factor for DUB-17.
-/

namespace Dubon2026
noncomputable section
open NumberField IsDedekindDomain Matrix
open scoped NumberField
attribute [local instance] cmFiniteAdeleStarRing

variable (K : Type) [Field K] [NumberField K] [IsCMField K]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Actual CM conjugation permutes the original finite places. -/
def cmFinitePlaceConjugation : HeightOneSpectrum (𝓞 K) ≃ HeightOneSpectrum (𝓞 K) :=
  numberFieldGaloisPlaceEquiv ℚ K ((IsCMField.complexConj K).restrictScalars ℚ)

/-- Conjugating an original finite place twice returns that same place. -/
theorem cmFinitePlaceConjugation_involutive : Function.Involutive (cmFinitePlaceConjugation K) := by
  intro v
  let σ : Gal(K/ℚ) := (IsCMField.complexConj K).restrictScalars ℚ
  have hσ : σ * σ = 1 := by
    ext x
    exact IsCMField.complexConj_apply_apply K x
  change numberFieldGaloisPlaceEquiv ℚ K σ (numberFieldGaloisPlaceEquiv ℚ K σ v) = v
  rw [← numberFieldGaloisPlaceEquiv_mul, hσ, numberFieldGaloisPlaceEquiv_one]

/-- The actual adelic adjoint of a one-place matrix is the identity away from its CM-conjugate place. -/
theorem cmFiniteAdelicLocalGL_star_ne
    (v w : HeightOneSpectrum (𝓞 K)) (hw : w ≠ cmFinitePlaceConjugation K v)
    (g : GeneralLinearGroup ι (v.adicCompletion K)) :
    numberFieldFiniteAdelicMatrixProjection K ι w (star (numberFieldFiniteAdelicLocalGL K v g)) = 1 := by
  let σ : Gal(K/ℚ) := (IsCMField.complexConj K).restrictScalars ℚ
  let e := numberFieldGaloisPlaceEquiv ℚ K σ
  let u := e.symm w
  have hu : u ≠ v := by
    intro h
    apply hw
    change w = e v
    rw [← h]
    exact (e.apply_symm_apply w).symm
  apply Units.ext
  apply Matrix.ext
  intro i j
  change numberFieldFiniteAdeleGaloisMap ℚ K σ
    (numberFieldFiniteAdelePlaceMatrix K v g.val j i) w = (1 : Matrix ι ι (w.adicCompletion K)) i j
  rw [numberFieldFiniteAdeleGaloisMap_apply ℚ K σ _ u w (e.apply_symm_apply w)]
  have he := congrArg (fun M => M j i) (numberFieldFiniteAdelePlaceMatrix_ne K v u hu g.val)
  change numberFieldFiniteAdelePlaceMatrix K v g.val j i u =
    (1 : Matrix ι ι (u.adicCompletion K)) j i at he
  rw [he]
  simp [Matrix.one_apply, eq_comm]

end
end Dubon2026
