import Dubon2026.CMFiniteAdelicLocalSplitHom
import Dubon2026.NumberFieldFiniteAdelicLocalIntegral
import Dubon2026.CMFiniteAdelicPairing

/-! # The actual split unitary section preserves original integral levels

Only the form and its inverse at the conjugate place must be integral;
no global unimodularity of the original Hermitian matrix is imposed.
This proves the integral compatibility required before transferring the
source parabolic quotients to the actual unitary adelic level in DUB-17.
-/

namespace Dubon2026
noncomputable section
open NumberField IsDedekindDomain Matrix
open scoped NumberField
attribute [local instance] cmFiniteAdeleStarRing

variable (K : Type) [Field K] [NumberField K] [IsCMField K]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The actual CM adjoint preserves the original integral adelic matrix level. -/
theorem cmFiniteAdelicIntegralMatrix_star
    {M : (Matrix ι ι (FiniteAdeleRing (𝓞 K) K))ˣ}
    (hM : M ∈ numberFieldIntegralMatrixLevel K ι) :
    star M ∈ numberFieldIntegralMatrixLevel K ι := by
  rw [numberFieldIntegralMatrixLevel_mem_iff] at hM ⊢
  constructor
  · intro i j w
    change (star (M.val j i)) w ∈ w.adicCompletionIntegers K
    exact cmFiniteAdele_star_integral K (hM.1 j i) w
  · intro i j w
    change (star ((M⁻¹).val j i)) w ∈ w.adicCompletionIntegers K
    exact cmFiniteAdele_star_integral K (hM.2 j i) w

/-- The genuine split unitary insertion of an original integral local matrix lies in the original integral adelic level when the specified form is integral and invertible at the conjugate place. -/
theorem cmFiniteAdelicLocalSplitElement_integral
    (H : (Matrix ι ι K)ˣ) (hH : star H = H)
    (v : HeightOneSpectrum (𝓞 K)) (hv : v ≠ cmFinitePlaceConjugation K v)
    (hlocal : numberFieldFiniteAdelicMatrixProjection K ι (cmFinitePlaceConjugation K v)
      (Units.map (algebraMap K (FiniteAdeleRing (𝓞 K) K)).mapMatrix.toMonoidHom H) ∈
        (((cmFinitePlaceConjugation K v).adicCompletionIntegers K).matrix (n := ι)).toSubmonoid.units)
    (g : (Matrix ι ι (Valued.integer (v.adicCompletion K)))ˣ) :
    (cmFiniteAdelicLocalSplitElement K H hH v hv
      (Units.map (Valued.integer (v.adicCompletion K)).subtype.mapMatrix.toMonoidHom g)).val ∈
        numberFieldIntegralMatrixLevel K ι := by
  let a := Units.map (Valued.integer (v.adicCompletion K)).subtype.mapMatrix.toMonoidHom g
  let A := numberFieldFiniteAdelicLocalGL K v a
  let H0 := Units.map (algebraMap K (FiniteAdeleRing (𝓞 K) K)).mapMatrix.toMonoidHom H
  have hA : A ∈ numberFieldIntegralMatrixLevel K ι := numberFieldFiniteAdelicLocalGL_integral K v g
  have hs := cmFiniteAdelicIntegralMatrix_star K hA
  rw [numberFieldIntegralMatrixLevel_iff_local] at hs ⊢
  intro w
  by_cases hw : w = v
  · subst w
    rw [cmFiniteAdelicLocalSplitElement_section]
    exact ⟨fun i j => (g.val i j).property, fun i j => ((g⁻¹).val i j).property⟩
  · let L := ((w.adicCompletionIntegers K).matrix (n := ι)).toSubmonoid.units
    change numberFieldFiniteAdelicMatrixProjection K ι w (A * (H0⁻¹ * star A * H0)⁻¹) ∈ L
    have ha : numberFieldFiniteAdelicMatrixProjection K ι w A = 1 :=
      numberFieldFiniteAdelicLocalGL_ne K v w hw a
    simp only [map_mul, map_inv, ha, one_mul]
    by_cases hc : w = cmFinitePlaceConjugation K v
    · have hH0 : numberFieldFiniteAdelicMatrixProjection K ι w H0 ∈ L := by
        dsimp only [L, H0]
        rw [hc]
        exact hlocal
      exact L.inv_mem (L.mul_mem (L.mul_mem (L.inv_mem hH0) (hs w)) hH0)
    · have hstar : numberFieldFiniteAdelicMatrixProjection K ι w (star A) = 1 :=
        cmFiniteAdelicLocalGL_star_ne K v w hc a
      rw [hstar, mul_one, inv_mul_cancel, inv_one]
      exact L.one_mem

end
end Dubon2026
