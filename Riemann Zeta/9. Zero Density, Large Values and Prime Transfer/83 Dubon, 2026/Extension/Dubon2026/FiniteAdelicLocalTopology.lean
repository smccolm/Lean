import Dubon2026.FiniteAdelicLocalHom
import Mathlib.Topology.Algebra.Group.Matrix

/-! # Continuity of the genuine original one-place adelic group embeddings -/

namespace Dubon2026

noncomputable section
open IsDedekindDomain Matrix Filter
open scoped RestrictedProduct

/-- Insertion at one actual finite place is continuous for the genuine restricted-product topology. -/
theorem finiteAdelePlaceSingle_continuous (v : HeightOneSpectrum ℤ) :
    Continuous (finiteAdelePlaceSingle v) := by
  classical
  let F : v.adicCompletion ℚ →
      Πʳ w : HeightOneSpectrum ℤ, [w.adicCompletion ℚ, w.adicCompletionIntegers ℚ]_[𝓟 {v}ᶜ] :=
    fun x => ⟨Pi.single v x, by
      change ∀ w ∈ ({v}ᶜ : Set (HeightOneSpectrum ℤ)), Pi.single v x w ∈ w.adicCompletionIntegers ℚ
      intro w hw
      rw [Pi.single_eq_of_ne (show w ≠ v from hw)]
      exact (w.adicCompletionIntegers ℚ).zero_mem⟩
  have hF : Continuous F := by
    apply RestrictedProduct.continuous_rng_of_principal.mpr
    apply continuous_pi
    intro w
    by_cases h : w = v
    · subst w
      simpa [F] using (continuous_id : Continuous (fun x : v.adicCompletion ℚ => x))
    · simpa [F, Pi.single_eq_of_ne h] using
        (continuous_const : Continuous (fun _ : v.adicCompletion ℚ => (0 : w.adicCompletion ℚ)))
  have hfilter : cofinite ≤ 𝓟 ({v}ᶜ : Set (HeightOneSpectrum ℤ)) := by simp
  exact (RestrictedProduct.continuous_inclusion hfilter).comp hF

/-- The actual inserted finite-adelic matrix varies continuously with its original local entries. -/
theorem finiteAdelePlaceMatrix_continuous (v : HeightOneSpectrum ℤ) :
    Continuous (finiteAdelePlaceMatrix v) := by
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  exact continuous_const.add ((finiteAdelePlaceSingle_continuous v).comp
    (((continuous_apply j).comp (continuous_apply i)).sub continuous_const))

/-- Both the original local matrix and its genuine inverse have continuous adelic insertion. -/
theorem finiteAdelicLocalGL2_continuous (v : HeightOneSpectrum ℤ) :
    Continuous (finiteAdelicLocalGL2Hom v) := by
  apply Units.continuous_iff.mpr
  constructor
  · exact (finiteAdelePlaceMatrix_continuous v).comp Units.continuous_val
  · exact (finiteAdelePlaceMatrix_continuous v).comp
      (Units.continuous_val.comp continuous_inv)

end
end Dubon2026
