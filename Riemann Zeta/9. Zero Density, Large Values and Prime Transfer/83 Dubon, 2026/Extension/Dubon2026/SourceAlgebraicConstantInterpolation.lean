import Dubon2026.SourceAlgebraicConstantLift

/-! DUB-17/18 -> original all-weight arithmetic association -> actual
Gamma1 character realization -> differential/cusp comparison -> rational
Fourier spanning -> integral base change of Fricke fractions. The algebraic
constant-adjoining step expresses an integral element as a complex span of
integral elements over the original constants. Finite extension embeddings
and Lagrange interpolation discharge integrality of the actual coordinates.
Adapted from anthropics/fermats-last-theorem,
6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0,
S_IsIntegral_mem_span_of_adjoin_simple_constants. No proof limit is raised.
The later consumer is the actual Fricke fraction field; constant-extension
spanning and rational Fourier realization are not assumed. -/
namespace Dubon2026.SourceFricke.ConstantDescent
noncomputable section
open Polynomial
open scoped IntermediateField
variable {K : Type*} [Field K] [Algebra ℂ K]
variable (F : IntermediateField ℚ ℂ) (B S : Set K)
variable {B S}

attribute [local instance] Classical.propDecidable in

theorem isIntegral_coeff_lagrangeBasis {s : Finset K}
    (hs : ∀ r ∈ s, ∃ a : ℂ, IsIntegral ↥F a ∧ algebraMap ℂ K a = r)
    {r : K} (hr : r ∈ s) (k : ℕ) :
    IsIntegral ↥(TRng F B) ((Lagrange.basis s id r).coeff k) := by
  set ι := algebraMap ℂ K
  set Sf : Subfield K := (algebraicClosure ↥F ℂ).toSubfield.map ι
  have hmemS : ∀ r ∈ s, r ∈ Sf := by
    intro r hr
    obtain ⟨a, ha, rfl⟩ := hs r hr
    exact ⟨a, mem_algebraicClosure_iff.mpr ha.isAlgebraic, rfl⟩
  have hlift : Lagrange.basis s id r ∈ Polynomial.liftsRing Sf.subtype := by
    unfold Lagrange.basis
    refine Subring.prod_mem _ fun j hj ↦ ?_
    unfold Lagrange.basisDivisor
    have hrS : (id r : K) ∈ Set.range Sf.subtype := ⟨⟨r, hmemS r hr⟩, rfl⟩
    have hjS : (id j : K) ∈ Set.range Sf.subtype :=
      ⟨⟨j, hmemS j (Finset.mem_of_mem_erase hj)⟩, rfl⟩
    refine Subring.mul_mem _ ?_ (Subring.sub_mem _ ?_ ?_)
    · rw [← Polynomial.lifts_iff_liftsRing]
      apply Polynomial.C'_mem_lifts
      obtain ⟨a, ha⟩ := hrS; obtain ⟨b, hb⟩ := hjS
      exact ⟨(a - b)⁻¹, by rw [map_inv₀, map_sub, ha, hb]⟩
    · rw [← Polynomial.lifts_iff_liftsRing]; exact Polynomial.X_mem_lifts _
    · rw [← Polynomial.lifts_iff_liftsRing]; exact Polynomial.C'_mem_lifts hjS
  rw [← Polynomial.lifts_iff_liftsRing, Polynomial.lifts_iff_coeff_lifts] at hlift
  obtain ⟨⟨w, hw⟩, hw'⟩ := hlift k
  obtain ⟨a, ha, rfl⟩ := hw
  change ι a = _ at hw'
  rw [← hw']
  exact isIntegral_TRng_algebraMap F
    (isAlgebraic_iff_isIntegral.mp (mem_algebraicClosure_iff.mp ha))


end
end Dubon2026.SourceFricke.ConstantDescent
