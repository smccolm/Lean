import Dubon2026.CMHermitianPositiveMatrix
import Mathlib.Algebra.Order.Archimedean.Basic

/-! # A fixed bound for the original CM scalar action on the trace form

The finitely many original complex embeddings bound multiplication by
any fixed field element on the specified positive trace form. The bound
is independent of the attached lattice. This bounds the integral action
matrices after Gram reduction in DUB-17's arithmetic class argument.
-/

namespace Dubon2026

noncomputable section

open NumberField Matrix
open scoped ComplexOrder

variable (K : Type*) [Field K] [NumberField K] [IsCMField K]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
/-- The original Hermitian pairing scales by the CM norm of the scalar. -/
theorem cmHermitianPairing_smul (H : Matrix ι ι K) (a : K) (x : ι → K) :
    dotProduct (star (a • x)) (H.mulVec (a • x)) =
      (star a * a) * dotProduct (star x) (H.mulVec x) := by
  rw [star_smul, mulVec_smul, smul_dotProduct, dotProduct_smul]
  simp only [smul_eq_mul]
  ring

omit [IsCMField K] in
/-- The real image of the original rational trace is the sum of real parts over the original embeddings. -/
theorem numberField_trace_real_sum (z : K) :
    (Algebra.trace ℚ K z : ℝ) = ∑ φ : K →ₐ[ℚ] ℂ, (φ z).re := by
  have ht := congrArg Complex.re (trace_eq_sum_embeddings ℂ (x := z) (K := ℚ))
  change ((Algebra.trace ℚ K z : ℂ)).re = _ at ht
  simpa only [Complex.re_sum, Complex.ratCast_re] using ht

/-- Multiplication by a fixed original CM scalar has one uniform integer trace-form bound. -/
theorem cmHermitianTraceForm_scalar_bound (H : Matrix ι ι K)
    (hH : ∀ φ : K →+* ℂ, (φ.mapMatrix H).PosDef) (a : K) :
    ∃ c : ℤ, 0 ≤ c ∧ ∀ x : ι → K,
      cmHermitianRationalTraceForm K H (a • x) (a • x) ≤
        (c : ℚ) * cmHermitianRationalTraceForm K H x x := by
  classical
  obtain ⟨c, hc⟩ := exists_nat_ge (∑ φ : K →ₐ[ℚ] ℂ, Complex.normSq (φ a))
  refine ⟨c, Int.natCast_nonneg c, ?_⟩
  intro x
  have hphi (φ : K →ₐ[ℚ] ℂ) : Complex.normSq (φ a) ≤ (c : ℝ) :=
    (Finset.single_le_sum (fun ψ _ => Complex.normSq_nonneg (ψ a))
      (Finset.mem_univ φ)).trans hc
  have hnonneg (φ : K →ₐ[ℚ] ℂ) :
      0 ≤ (φ (dotProduct (star x) (H.mulVec x))).re := by
    have hp := (hH φ.toRingHom).posSemidef.dotProduct_mulVec_nonneg (fun i => φ (x i))
    change 0 ≤ dotProduct (star (fun i => φ.toRingHom (x i)))
      ((φ.toRingHom.mapMatrix H).mulVec (fun i => φ.toRingHom (x i))) at hp
    rw [← cmHermitianPairing_complex K H φ.toRingHom x x] at hp
    exact (Complex.nonneg_iff.mp hp).1
  have hlocal (φ : K →ₐ[ℚ] ℂ) :
      (φ (dotProduct (star (a • x)) (H.mulVec (a • x)))).re ≤
        (c : ℝ) * (φ (dotProduct (star x) (H.mulVec x))).re := by
    rw [cmHermitianPairing_smul, map_mul, map_mul,
      show φ (star a) = star (φ a) from
        IsCMField.complexEmbedding_complexConj K φ.toRingHom a]
    change (((starRingEnd ℂ) (φ a) * φ a) * φ (dotProduct (star x) (H.mulVec x))).re ≤ _
    rw [← Complex.normSq_eq_conj_mul_self]
    simpa only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero] using mul_le_mul_of_nonneg_right (hphi φ) (hnonneg φ)
  have hs := Finset.sum_le_sum (fun φ (_ : φ ∈ Finset.univ) => hlocal φ)
  rw [← Finset.mul_sum, ← numberField_trace_real_sum K,
    ← numberField_trace_real_sum K] at hs
  change Algebra.trace ℚ K (dotProduct (star (a • x)) (H.mulVec (a • x))) ≤
    (c : ℚ) * Algebra.trace ℚ K (dotProduct (star x) (H.mulVec x))
  exact_mod_cast hs

end
end Dubon2026
