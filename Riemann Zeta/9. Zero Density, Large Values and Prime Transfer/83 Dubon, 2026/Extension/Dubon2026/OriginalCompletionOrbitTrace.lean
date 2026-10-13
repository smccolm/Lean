import Dubon2026.OriginalAdicBaseChangeClosed
import Dubon2026.OriginalFinitePlaceWeakApproximation
import Mathlib.RingTheory.Trace.Basic

/-! # Trace from the original finite orbit of completions

Simultaneous approximation and the original completed Galois transports
show that this actual trace lands in the original base completion.
This is the reverse-inclusion input for the fixed-field comparison needed
by DUB-17's native global norm quotient and arithmetic duality route.
-/

namespace Dubon2026
noncomputable section
open NumberField IsDedekindDomain Topology
open scoped NumberField Classical
variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [FiniteDimensional K L]

/-- The actual finite orbit of an original prime under the original Galois group. -/
def originalGaloisCompletionOrbit (w : HeightOneSpectrum (𝓞 L)) :
    Finset (HeightOneSpectrum (𝓞 L)) :=
  Finset.univ.image (fun σ : Gal(L/K) => numberFieldGaloisPlaceEquiv K L σ w)

/-- The actual source place of transport by a given automorphism into the chosen completion. -/
def originalGaloisCompletionSource (w : HeightOneSpectrum (𝓞 L)) (σ : Gal(L/K)) :
    originalGaloisCompletionOrbit K L w :=
  ⟨numberFieldGaloisPlaceEquiv K L σ⁻¹ w, Finset.mem_image.mpr ⟨σ⁻¹, Finset.mem_univ _, rfl⟩⟩

omit [NumberField K] [NumberField L] in
/-- The original source prime is transported to the chosen prime. -/
theorem originalGaloisCompletionSource_transport (w : HeightOneSpectrum (𝓞 L)) (σ : Gal(L/K)) :
    numberFieldGaloisPlaceEquiv K L σ (originalGaloisCompletionSource K L w σ).1 = w := by
  change numberFieldGaloisPlaceEquiv K L σ (numberFieldGaloisPlaceEquiv K L σ⁻¹ w) = w
  rw [← numberFieldGaloisPlaceEquiv_mul, mul_inv_cancel, numberFieldGaloisPlaceEquiv_one]

/-- Sum of actual Galois transports from the original orbit product into the chosen completion. -/
def originalCompletionOrbitTrace (w : HeightOneSpectrum (𝓞 L))
    (z : ∀ u : originalGaloisCompletionOrbit K L w, u.1.adicCompletion L) : w.adicCompletion L :=
  ∑ σ : Gal(L/K), numberFieldGaloisLocalTransport K L σ
    (originalGaloisCompletionSource K L w σ).1 w (originalGaloisCompletionSource_transport K L w σ)
    (z (originalGaloisCompletionSource K L w σ))

omit [NumberField K] in
/-- The actual orbit trace is continuous in the original product of completions. -/
theorem originalCompletionOrbitTrace_continuous (w : HeightOneSpectrum (𝓞 L)) :
    Continuous (originalCompletionOrbitTrace K L w) := by
  unfold originalCompletionOrbitTrace
  exact continuous_finsetSum _ fun σ _ =>
    (numberFieldGaloisLocalTransport_continuous K L σ _ w _).comp
      (continuous_apply (originalGaloisCompletionSource K L w σ))

omit [NumberField K] in
/-- On the original global field the orbit trace is exactly the original field trace. -/
theorem originalCompletionOrbitTrace_algebraMap [IsGalois K L]
    (w : HeightOneSpectrum (𝓞 L)) (x : L) :
    originalCompletionOrbitTrace K L w (fun u => algebraMap L (u.1.adicCompletion L) x) =
      algebraMap L (w.adicCompletion L) (algebraMap K L (Algebra.trace K L x)) := by
  unfold originalCompletionOrbitTrace
  simp_rw [numberFieldGaloisLocalTransport_algebraMap]
  rw [← map_sum, ← trace_eq_sum_automorphisms]

/-- Every orbit-product trace lies in the actual original base-completion image. -/
theorem originalCompletionOrbitTrace_mem_base [IsGalois K L]
    (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L))
    [w.asIdeal.LiesOver v.asIdeal]
    (z : ∀ u : originalGaloisCompletionOrbit K L w, u.1.adicCompletion L) :
    originalCompletionOrbitTrace K L w z ∈ Set.range (originalAdicBaseChangeMap K L v w) := by
  refine (original_finiteCompletions_dense L (originalGaloisCompletionOrbit K L w)).induction_on z ?_ ?_
  · exact (originalAdicBaseChangeMap_isClosedEmbedding K L v w).isClosed_range.preimage
      (originalCompletionOrbitTrace_continuous K L w)
  · intro x
    refine ⟨algebraMap K (v.adicCompletion K) (Algebra.trace K L x), ?_⟩
    rw [originalAdicBaseChangeMap_algebraMap, originalCompletionOrbitTrace_algebraMap]

end
end Dubon2026
