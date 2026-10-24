import Dubon2026.SourceCurvePrimePlaces
import Mathlib.RingTheory.Valuation.LocalSubring

/-! DUB-17/18 -> original Frobenius/inertia -> good reduction -> reduction-place
comparison. A proper valuation containing a Dedekind chart is the actual
normalized place at its center. This applies to the separable modular residue
coordinate in arbitrary characteristic. It reuses native chart localizations
and valuation maximality rather than developing general curve normalization.
Adapted from the valuation-ring step of
S_AlgebraicCurve_RegularProlongation_existsUnique_place_forall_residue_sub_mem_nonunits,
anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2. -/
namespace Dubon2026.SourceCurve
noncomputable section
open IsDedekindDomain

theorem exists_place_of_dedekind_chart
    {K F R : Type*} [Field K] [Field F] [Algebra K F]
    [CommRing R] [IsDedekindDomain R] [Algebra R F] [IsFractionRing R F]
    (V : ValuationSubring F) (hK : ∀ c : K, algebraMap K F c ∈ V)
    (hR : ∀ r : R, algebraMap R F r ∈ V) (hV : V ≠ ⊤) :
    ∃ Q : Place K F, Q.toValuationSubring = V := by
  let φ : R →+* V := (algebraMap R F).codRestrict V hR
  let I : Ideal R := (IsLocalRing.maximalIdeal V).comap φ
  have hunit (s : R) (hs : s ∉ I) : V.valuation (algebraMap R F s) = 1 := by
    have hsu : IsUnit (φ s) := IsLocalRing.notMem_maximalIdeal.mp hs
    exact (V.valuation_eq_one_iff (φ s)).mp hsu
  have hI : I ≠ ⊥ := by
    intro hbot
    apply hV
    rw [eq_top_iff]
    intro z _
    obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := R) z
    have hbI : b ∉ I := by
      rw [hbot, Ideal.mem_bot]
      exact nonZeroDivisors.ne_zero hb
    apply (V.valuation_le_one_iff _).mp
    rw [map_div₀, hunit b hbI, div_one]
    exact V.valuation_le_one (φ a)
  let P : HeightOneSpectrum R := ⟨I, Ideal.comap_isPrime φ _, hI⟩
  have hle : HeightOneSpectrum.valuationSubringAtPrime F P ≤ V := by
    rintro z ⟨a, s, hs, rfl⟩
    apply (V.valuation_le_one_iff _).mp
    rw [map_mul, map_inv₀, hunit s hs, inv_one, mul_one]
    exact V.valuation_le_one (φ a)
  have heq : HeightOneSpectrum.valuationSubringAtPrime F P = V :=
    ValuationSubring.eq_of_le_of_ne_top _ hle hV
  refine ⟨⟨V, hK, hV, ?_⟩, rfl⟩
  rw [← heq]
  infer_instance

end
end Dubon2026.SourceCurve
