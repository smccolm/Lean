import Dubon2026.CMHermitianRationalTraceForm

/-! # Positivity of the trace form from the original CM embeddings

The trace is the sum over the actual complex embeddings. Positivity of
the specified Hermitian form at every embedding therefore gives a
positive rational trace form. This is the positivity input for applying
integral Gram-class finiteness to DUB-17's actual unitary adelic lattices.
-/

namespace Dubon2026

noncomputable section

open NumberField Matrix
open scoped ComplexOrder

variable (K : Type*) [Field K] [NumberField K] [IsCMField K]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Every original complex embedding carries the actual CM pairing to the corresponding complex pairing. -/
theorem cmHermitianPairing_complex (H : Matrix ι ι K) (φ : K →+* ℂ) (x y : ι → K) :
    φ (dotProduct (star x) (H.mulVec y)) =
      dotProduct (star (fun i => φ (x i))) ((φ.mapMatrix H).mulVec (fun i => φ (y i))) := by
  change φ (∑ i, star (x i) * (∑ j, H i j * y j)) =
    ∑ i, star (φ (x i)) * (∑ j, φ (H i j) * φ (y j))
  simp only [map_sum, map_mul]
  apply Finset.sum_congr rfl
  intro i _
  rw [show φ (star (x i)) = star (φ (x i)) from
    IsCMField.complexEmbedding_complexConj K φ (x i)]

/-- Positivity at all original complex embeddings makes the actual rational trace form positive. -/
theorem cmHermitianRationalTraceForm_posDef (H : Matrix ι ι K)
    (hH : ∀ φ : K →+* ℂ, (φ.mapMatrix H).PosDef) :
    (cmHermitianRationalTraceForm K H).toQuadraticMap.PosDef := by
  classical
  letI : Nonempty (K →ₐ[ℚ] ℂ) :=
    ⟨(Classical.arbitrary (K →+* ℂ)).toRatAlgHom⟩
  intro x hx
  have hphi (φ : K →ₐ[ℚ] ℂ) :
      (0 : ℂ) < φ (dotProduct (star x) (H.mulVec x)) := by
    change (0 : ℂ) < φ.toRingHom (dotProduct (star x) (H.mulVec x))
    rw [cmHermitianPairing_complex K H φ.toRingHom x x]
    apply (hH φ.toRingHom).dotProduct_mulVec_pos
    intro hz
    apply hx
    funext i
    exact φ.injective (by simpa using congrFun hz i)
  have hs : (0 : ℂ) < ∑ φ : K →ₐ[ℚ] ℂ, φ (dotProduct (star x) (H.mulVec x)) :=
    Finset.sum_pos (fun φ _ => hphi φ) Finset.univ_nonempty
  rw [← trace_eq_sum_embeddings ℂ] at hs
  change (0 : ℂ) < (Algebra.trace ℚ K (dotProduct (star x) (H.mulVec x)) : ℂ) at hs
  have hr := (Complex.lt_def.mp hs).1
  simp only [Complex.zero_re, Complex.ratCast_re] at hr
  change (0 : ℚ) < Algebra.trace ℚ K (dotProduct (star x) (H.mulVec x))
  exact_mod_cast hr

end
end Dubon2026
