import Dubon2026.OriginalInfiniteAdeleBaseChange
import Mathlib.RingTheory.Trace.Basic

/-! # Descent of actual fixed original infinite adeles

The original base infinite adeles form a closed subring. The actual Galois
trace lands in that subring on the dense original number field, hence
everywhere. Dividing the trace of a fixed adele gives its actual preimage.
This discharges the infinite part of original idele descent for DUB-17's
native norm quotient and subsequent global duality dependency chain.
-/

namespace Dubon2026
noncomputable section
open NumberField Topology
variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L]

omit [NumberField K] [NumberField L] in
/-- The actual original Galois map on infinite adeles is continuous. -/
theorem numberFieldInfiniteAdeleGaloisMap_continuous (σ : Gal(L/K)) :
    Continuous (numberFieldInfiniteAdeleGaloisMap K L σ) := by
  apply continuous_pi
  intro w
  exact (numberFieldGaloisArchimedeanTransport_continuous K L σ (σ⁻¹ • w) w _).comp
    (continuous_apply (σ⁻¹ • w))

/-- Every original base infinite adele is fixed by the actual Galois action. -/
theorem originalInfiniteAdeleBaseChangeMap_fixed (σ : Gal(L/K)) (a : InfiniteAdeleRing K) :
    numberFieldInfiniteAdeleGaloisMap K L σ (originalInfiniteAdeleBaseChangeMap K L a) =
      originalInfiniteAdeleBaseChangeMap K L a := by
  letI : T2Space (InfiniteAdeleRing L) := inferInstanceAs (T2Space ((w : InfinitePlace L) → w.Completion))
  refine (InfiniteAdeleRing.denseRange_algebraMap K).induction_on a ?_ ?_
  · exact isClosed_eq
      ((numberFieldInfiniteAdeleGaloisMap_continuous K L σ).comp
        (originalInfiniteAdeleBaseChangeMap_isClosedEmbedding K L).continuous)
      (originalInfiniteAdeleBaseChangeMap_isClosedEmbedding K L).continuous
  · intro x
    rw [originalInfiniteAdeleBaseChangeMap_algebraMap, numberFieldInfiniteAdeleGaloisMap_algebraMap,
      σ.commutes]

variable [FiniteDimensional K L] [IsGalois K L]

/-- The actual Galois trace of every original infinite adele lies in the original base-adele image. -/
theorem originalInfiniteAdeleTrace_mem_base (a : InfiniteAdeleRing L) :
    (∑ σ : Gal(L/K), numberFieldInfiniteAdeleGaloisMap K L σ a) ∈
      Set.range (originalInfiniteAdeleBaseChangeMap K L) := by
  refine (InfiniteAdeleRing.denseRange_algebraMap L).induction_on a ?_ ?_
  · exact (originalInfiniteAdeleBaseChangeMap_isClosedEmbedding K L).isClosed_range.preimage
      (continuous_finsetSum _ fun σ _ => numberFieldInfiniteAdeleGaloisMap_continuous K L σ)
  · intro x
    refine ⟨algebraMap K (InfiniteAdeleRing K) (Algebra.trace K L x), ?_⟩
    rw [originalInfiniteAdeleBaseChangeMap_algebraMap, trace_eq_sum_automorphisms, map_sum]
    simp only [numberFieldInfiniteAdeleGaloisMap_algebraMap]

/-- Every actual fixed original infinite adele descends to an original base infinite adele. -/
theorem originalInfiniteAdeleBaseChangeMap_surjective_fixed
    (a : InfiniteAdeleRing L)
    (ha : ∀ σ : Gal(L/K), numberFieldInfiniteAdeleGaloisMap K L σ a = a) :
    ∃ b : InfiniteAdeleRing K, originalInfiniteAdeleBaseChangeMap K L b = a := by
  obtain ⟨b, hb⟩ := originalInfiniteAdeleTrace_mem_base K L a
  refine ⟨b * algebraMap K (InfiniteAdeleRing K) ((Fintype.card Gal(L/K) : K)⁻¹), ?_⟩
  rw [map_mul, originalInfiniteAdeleBaseChangeMap_algebraMap, hb]
  simp_rw [ha]
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  funext w
  change (Fintype.card Gal(L/K) : w.Completion) * a w *
    algebraMap L w.Completion (algebraMap K L ((Fintype.card Gal(L/K) : K)⁻¹)) = a w
  simp only [map_inv₀, map_natCast]
  have hc : (Fintype.card Gal(L/K) : w.Completion) ≠ 0 := by
    rw [← map_natCast (algebraMap L w.Completion)]
    exact (map_ne_zero (algebraMap L w.Completion)).mpr
      (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)
  rw [mul_comm _ (a w), mul_assoc, mul_inv_cancel₀ hc, mul_one]

/-- The actual original infinite-adele fixed set is exactly the original base-adele image. -/
theorem originalInfiniteAdeleBaseChangeMap_range_iff_fixed (a : InfiniteAdeleRing L) :
    a ∈ Set.range (originalInfiniteAdeleBaseChangeMap K L) ↔
      ∀ σ : Gal(L/K), numberFieldInfiniteAdeleGaloisMap K L σ a = a := by
  constructor
  · rintro ⟨b, rfl⟩ σ
    exact originalInfiniteAdeleBaseChangeMap_fixed K L σ b
  · exact originalInfiniteAdeleBaseChangeMap_surjective_fixed K L a

end
end Dubon2026
