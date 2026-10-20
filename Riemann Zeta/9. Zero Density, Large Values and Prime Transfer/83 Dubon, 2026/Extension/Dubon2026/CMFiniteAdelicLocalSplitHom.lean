import Dubon2026.CMFiniteAdelicLocalSplitElement

/-! # The actual split unitary insertion is a group section

The group law uses the proved disjoint-support commutation of opposite
CM-place factors. This is the source local factor homomorphism needed
to realize the original parabolic level quotient in DUB-17's actual
unitary adelic group; integrality and the prescribed family levels are
the next consumers.
-/

namespace Dubon2026
noncomputable section
open NumberField IsDedekindDomain Matrix
open scoped NumberField
attribute [local instance] cmFiniteAdeleStarRing

variable (K : Type) [Field K] [NumberField K] [IsCMField K]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The actual paired-place unitary insertion respects original local matrix multiplication. -/
theorem cmFiniteAdelicLocalSplitElement_mul
    (H : (Matrix ι ι K)ˣ) (hH : star H = H)
    (v : HeightOneSpectrum (𝓞 K)) (hv : v ≠ cmFinitePlaceConjugation K v)
    (a b : GeneralLinearGroup ι (v.adicCompletion K)) :
    cmFiniteAdelicLocalSplitElement K H hH v hv (a * b) =
      cmFiniteAdelicLocalSplitElement K H hH v hv a *
        cmFiniteAdelicLocalSplitElement K H hH v hv b := by
  let A := numberFieldFiniteAdelicLocalGL K v a
  let B := numberFieldFiniteAdelicLocalGL K v b
  let H0 := Units.map (algebraMap K (FiniteAdeleRing (𝓞 K) K)).mapMatrix.toMonoidHom H
  let Ad := H0⁻¹ * star A * H0
  let Bd := H0⁻¹ * star B * H0
  let τ := fun x : (Matrix ι ι (FiniteAdeleRing (𝓞 K) K))ˣ => x * (H0⁻¹ * star x * H0)⁻¹
  have hc : Commute B Ad := cmFiniteAdelicLocalGL_commute_adjoint K H0 v hv b a
  have hab : H0⁻¹ * star (A * B) * H0 = Bd * Ad := by
    rw [star_mul]
    dsimp only [Bd, Ad]
    group
  apply Subtype.ext
  change τ (numberFieldFiniteAdelicLocalGL K v (a * b)) = τ A * τ B
  rw [numberFieldFiniteAdelicLocalGL_mul]
  change (A * B) * (H0⁻¹ * star (A * B) * H0)⁻¹ = (A * Ad⁻¹) * (B * Bd⁻¹)
  calc
    _ = A * (B * Ad⁻¹) * Bd⁻¹ := by
      rw [hab, _root_.mul_inv_rev]
      group
    _ = A * (Ad⁻¹ * B) * Bd⁻¹ := by rw [hc.inv_right.eq]
    _ = _ := by group

/-- The original local general linear group embeds in the actual paired-place unitary group. -/
def cmFiniteAdelicLocalSplitHom
    (H : (Matrix ι ι K)ˣ) (hH : star H = H)
    (v : HeightOneSpectrum (𝓞 K)) (hv : v ≠ cmFinitePlaceConjugation K v) :
    GeneralLinearGroup ι (v.adicCompletion K) →* cmFiniteAdelicUnitaryGroup K H.val :=
  MonoidHom.mk' (cmFiniteAdelicLocalSplitElement K H hH v hv)
    (cmFiniteAdelicLocalSplitElement_mul K H hH v hv)

/-- Projection of the original unitary section is the identity on the original local matrix group. -/
theorem cmFiniteAdelicLocalSplitHom_section
    (H : (Matrix ι ι K)ˣ) (hH : star H = H)
    (v : HeightOneSpectrum (𝓞 K)) (hv : v ≠ cmFinitePlaceConjugation K v)
    (a : GeneralLinearGroup ι (v.adicCompletion K)) :
    numberFieldFiniteAdelicMatrixProjection K ι v (cmFiniteAdelicLocalSplitHom K H hH v hv a).val = a :=
  cmFiniteAdelicLocalSplitElement_section K H hH v hv a

/-- The actual split-place projection from the original unitary adelic group is surjective. -/
theorem cmFiniteAdelic_split_projection_surjective
    (H : (Matrix ι ι K)ˣ) (hH : star H = H)
    (v : HeightOneSpectrum (𝓞 K)) (hv : v ≠ cmFinitePlaceConjugation K v) :
    Function.Surjective (fun M : cmFiniteAdelicUnitaryGroup K H.val =>
      numberFieldFiniteAdelicMatrixProjection K ι v M.val) :=
  fun a => ⟨cmFiniteAdelicLocalSplitHom K H hH v hv a,
    cmFiniteAdelicLocalSplitHom_section K H hH v hv a⟩

end
end Dubon2026
