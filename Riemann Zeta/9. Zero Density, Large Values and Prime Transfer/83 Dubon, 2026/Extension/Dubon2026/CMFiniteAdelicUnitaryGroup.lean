import Dubon2026.CMFiniteAdeleConjugation
import Dubon2026.CMHermitianArithmeticSmallLevel

/-! # The actual finite-adelic unitary group of the specified CM form

The group used in DUB-17's auxiliary automorphic functions now consists
of the original finite-adelic matrices preserving the original Hermitian
form under the actual place-permuting CM conjugation. Its closedness and
its principal arithmetic inclusion are proved from the existing maps.
Prescribed local quasi-split forms and finite double cosets remain required.
-/

namespace Dubon2026

noncomputable section

open NumberField IsDedekindDomain
open scoped NumberField RestrictedProduct

attribute [local instance] cmFiniteAdeleStarRing

variable (K : Type) [Field K] [NumberField K] [IsCMField K]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The original principal matrix embedding preserves the actual CM adelic involution. -/
def cmMatrixFiniteAdeleEmbedding :
    Matrix ι ι K →⋆* Matrix ι ι (FiniteAdeleRing (𝓞 K) K) where
  __ := (algebraMap K (FiniteAdeleRing (𝓞 K) K)).mapMatrix.toMonoidHom
  map_star' M := by
    apply Matrix.ext
    intro i j
    exact (cmFiniteAdeleConjugation_algebraMap K (M j i)).symm

/-- The original finite-adelic matrices preserving the specified CM Hermitian form. -/
def cmFiniteAdelicUnitaryGroup (H : Matrix ι ι K) :
    Subgroup (Matrix ι ι (FiniteAdeleRing (𝓞 K) K))ˣ where
  carrier := {M | star M.val * (algebraMap K (FiniteAdeleRing (𝓞 K) K)).mapMatrix H * M.val =
    (algebraMap K (FiniteAdeleRing (𝓞 K) K)).mapMatrix H}
  one_mem' := by simp
  mul_mem' {A B} ha hb := by
    let H0 := (algebraMap K (FiniteAdeleRing (𝓞 K) K)).mapMatrix H
    change star (A.val * B.val) * H0 * (A.val * B.val) = H0
    rw [star_mul]
    calc
      _ = star B.val * (star A.val * H0 * A.val) * B.val := by simp only [mul_assoc]
      _ = H0 := by rw [ha, hb]
  inv_mem' {M} hM := by
    let H0 := (algebraMap K (FiniteAdeleRing (𝓞 K) K)).mapMatrix H
    change star (M⁻¹).val * H0 * (M⁻¹).val = H0
    calc
      _ = star (M⁻¹).val * (star M.val * H0 * M.val) * (M⁻¹).val := by rw [hM]
      _ = star (M.val * (M⁻¹).val) * H0 * (M.val * (M⁻¹).val) := by
        simp only [star_mul, mul_assoc]
      _ = H0 := by simp

/-- The original Hermitian arithmetic group embeds in its actual finite-adelic unitary group. -/
theorem cmFiniteAdelicUnitaryGroup_principal (H : Matrix ι ι K)
    (M : cmHermitianUnitaryGroup H) :
    cmHermitianFiniteAdeleHom H M ∈ cmFiniteAdelicUnitaryGroup K H := by
  have h := congrArg (cmMatrixFiniteAdeleEmbedding K) M.property
  simpa only [map_mul, map_star] using h

/-- The actual finite-adelic unitary group is closed in the original general linear group. -/
theorem cmFiniteAdelicUnitaryGroup_isClosed (H : Matrix ι ι K) :
    IsClosed (cmFiniteAdelicUnitaryGroup K H :
      Set (Matrix ι ι (FiniteAdeleRing (𝓞 K) K))ˣ) := by
  letI : T2Space (FiniteAdeleRing (𝓞 K) K) := inferInstanceAs
    (T2Space (Πʳ v : HeightOneSpectrum (𝓞 K), [v.adicCompletion K, v.adicCompletionIntegers K]))
  letI : ContinuousStar (FiniteAdeleRing (𝓞 K) K) := ⟨cmFiniteAdeleConjugation_continuous K⟩
  exact isClosed_eq ((Units.continuous_val.star.mul continuous_const).mul Units.continuous_val)
    continuous_const

end
end Dubon2026
