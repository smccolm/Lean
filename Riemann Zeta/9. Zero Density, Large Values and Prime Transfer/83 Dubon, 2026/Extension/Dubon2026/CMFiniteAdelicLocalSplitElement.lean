import Dubon2026.CMFiniteAdelicLocalConjugation
import Dubon2026.HermitianCommutingUnitary

/-! # Original local matrices realized in the actual CM unitary group

At a pair of distinct CM-conjugate finite places, the original local
matrix and its Hermitian adjoint have disjoint supports. Their quotient
therefore preserves the specified original Hermitian form and projects
back to the original local matrix. This constructs the source split
factor required to put the parabolic levels inside DUB-17's actual
global unitary group.
-/

namespace Dubon2026
noncomputable section
open NumberField IsDedekindDomain Matrix
open scoped NumberField
attribute [local instance] cmFiniteAdeleStarRing

variable (K : Type) [Field K] [NumberField K] [IsCMField K]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Matrices supported at a place commute with the Hermitian adjoints supported at its distinct conjugate place. -/
theorem cmFiniteAdelicLocalGL_commute_adjoint
    (H : (Matrix ι ι (FiniteAdeleRing (𝓞 K) K))ˣ)
    (v : HeightOneSpectrum (𝓞 K)) (hv : v ≠ cmFinitePlaceConjugation K v)
    (a b : GeneralLinearGroup ι (v.adicCompletion K)) :
    Commute (numberFieldFiniteAdelicLocalGL K v a)
      (H⁻¹ * star (numberFieldFiniteAdelicLocalGL K v b) * H) := by
  change _ * _ = _ * _
  apply numberFieldFiniteAdelicGL_ext K
  intro w
  simp only [map_mul, map_inv]
  by_cases hw : w = v
  · subst w
    rw [cmFiniteAdelicLocalGL_star_ne K v v hv]
    simp
  · have ha : numberFieldFiniteAdelicMatrixProjection K ι w
        (numberFieldFiniteAdelicLocalGL K v a) = 1 :=
      numberFieldFiniteAdelicLocalGL_ne K v w hw a
    rw [ha]
    simp

/-- The principal finite-adelic image of an original Hermitian invertible matrix is still Hermitian. -/
theorem cmFiniteAdelicHermitianUnit_star
    (H : (Matrix ι ι K)ˣ) (hH : star H = H) :
    star (Units.map (algebraMap K (FiniteAdeleRing (𝓞 K) K)).mapMatrix.toMonoidHom H) =
      Units.map (algebraMap K (FiniteAdeleRing (𝓞 K) K)).mapMatrix.toMonoidHom H := by
  apply Units.ext
  change star (cmMatrixFiniteAdeleEmbedding K H.val) = cmMatrixFiniteAdeleEmbedding K H.val
  have h := congrArg (cmMatrixFiniteAdeleEmbedding K) (congrArg Units.val hH)
  change cmMatrixFiniteAdeleEmbedding K (star H.val) = cmMatrixFiniteAdeleEmbedding K H.val at h
  simpa only [map_star] using h

/-- Insert a local matrix and its compensating conjugate-place factor into the actual unitary group of the original Hermitian form. -/
def cmFiniteAdelicLocalSplitElement
    (H : (Matrix ι ι K)ˣ) (hH : star H = H)
    (v : HeightOneSpectrum (𝓞 K)) (hv : v ≠ cmFinitePlaceConjugation K v)
    (g : GeneralLinearGroup ι (v.adicCompletion K)) : cmFiniteAdelicUnitaryGroup K H.val := by
  let A := numberFieldFiniteAdelicLocalGL K v g
  let H0 := Units.map (algebraMap K (FiniteAdeleRing (𝓞 K) K)).mapMatrix.toMonoidHom H
  refine ⟨A * (H0⁻¹ * star A * H0)⁻¹, ?_⟩
  have he := hermitian_unitary_of_commute_adjoint H0 A (cmFiniteAdelicHermitianUnit_star K H hH)
    (cmFiniteAdelicLocalGL_commute_adjoint K H0 v hv g g)
  exact congrArg Units.val he

/-- Projection of the genuine split unitary insertion recovers the original local matrix. -/
theorem cmFiniteAdelicLocalSplitElement_section
    (H : (Matrix ι ι K)ˣ) (hH : star H = H)
    (v : HeightOneSpectrum (𝓞 K)) (hv : v ≠ cmFinitePlaceConjugation K v)
    (g : GeneralLinearGroup ι (v.adicCompletion K)) :
    numberFieldFiniteAdelicMatrixProjection K ι v
      (cmFiniteAdelicLocalSplitElement K H hH v hv g).val = g := by
  change numberFieldFiniteAdelicMatrixProjection K ι v
    (numberFieldFiniteAdelicLocalGL K v g *
      ((Units.map (algebraMap K (FiniteAdeleRing (𝓞 K) K)).mapMatrix.toMonoidHom H)⁻¹ *
        star (numberFieldFiniteAdelicLocalGL K v g) *
          Units.map (algebraMap K (FiniteAdeleRing (𝓞 K) K)).mapMatrix.toMonoidHom H)⁻¹) = g
  simp only [map_mul, map_inv, cmFiniteAdelicLocalGL_star_ne K v v hv,
    mul_one, inv_mul_cancel, inv_one]
  exact numberFieldFiniteAdelicLocalGL_same K v g

end
end Dubon2026
