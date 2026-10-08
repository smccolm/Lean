import Dubon2026.CanonicalAdelicGL2CuspLift
import Mathlib.NumberTheory.Padics.ProperSpace

/-! # The actual compact integral finite adeles and rational additive representatives -/

namespace Dubon2026

noncomputable section
open IsDedekindDomain NumberField Set

/-- The canonical local rational integer rings are genuinely compact through their actual p-adic equivalences. -/
theorem rationalFiniteCompletionIntegers_compactSpace (v : HeightOneSpectrum ℤ) :
    CompactSpace (v.adicCompletionIntegers ℚ) := by
  letI : Algebra ℤ (v.adicCompletionIntegers ℚ) := Ring.toIntAlgebra _
  letI : Fact (Rat.HeightOneSpectrum.primesEquiv v).val.Prime :=
    ⟨(Rat.HeightOneSpectrum.primesEquiv v).property⟩
  exact (Rat.HeightOneSpectrum.adicCompletionIntegers.padicIntEquiv v).symm.toHomeomorph.compactSpace

/-- The image of the actual integral product is exactly the everywhere-integral finite adele subring. -/
theorem finiteAdeleIntegralEmbedding_range :
    Set.range finiteAdeleIntegralEmbedding =
      (finiteAdeleIntegerSubring : Set (FiniteAdeleRing ℤ ℚ)) := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    exact fun v => (y v).property
  · intro hx
    refine ⟨fun v => ⟨x v, hx v⟩, ?_⟩
    apply FiniteAdeleRing.ext
    intro v
    rfl

/-- The original everywhere-integral subring is compact in the actual finite adelic topology. -/
theorem finiteAdeleIntegerSubring_isCompact :
    IsCompact (finiteAdeleIntegerSubring : Set (FiniteAdeleRing ℤ ℚ)) := by
  letI (v : HeightOneSpectrum ℤ) : CompactSpace (v.adicCompletionIntegers ℚ) :=
    rationalFiniteCompletionIntegers_compactSpace v
  rw [← finiteAdeleIntegralEmbedding_range]
  exact isCompact_range finiteAdeleIntegralEmbedding_continuous

/-- Every actual finite adele differs from a principal rational adele by a genuinely integral adele. -/
theorem finiteAdele_exists_rational_integral (x : FiniteAdeleRing ℤ ℚ) :
    ∃ q : ℚ, x - algebraMap ℚ (FiniteAdeleRing ℤ ℚ) q ∈ finiteAdeleIntegerSubring := by
  have hopen : IsOpen {y : FiniteAdeleRing ℤ ℚ | x - y ∈ finiteAdeleIntegerSubring} :=
    finiteAdeleIntegerSubring_isOpen.preimage (continuous_const.sub continuous_id)
  exact rational_dense_finiteAdeles.exists_mem_open hopen ⟨x, by simp⟩

/-- Every actual full rational adele has a principal translate in the literal real unit interval times the integral finite adeles. -/
theorem rationalAdele_exists_integral_representative (x : AdeleRing ℤ ℚ) :
    ∃ q : ℚ,
      (rationalAdeleRealFiniteRingEquiv (x - algebraMap ℚ (AdeleRing ℤ ℚ) q)).1 ∈ Ico (0 : ℝ) 1 ∧
      (rationalAdeleRealFiniteRingEquiv (x - algebraMap ℚ (AdeleRing ℤ ℚ) q)).2 ∈
        finiteAdeleIntegerSubring := by
  let y := rationalAdeleRealFiniteRingEquiv x
  obtain ⟨q, hq⟩ := finiteAdele_exists_rational_integral y.2
  let n : ℤ := ⌊y.1 - (q : ℝ)⌋
  refine ⟨q + n, ?_, ?_⟩
  · rw [map_sub, rationalAdeleRealFiniteRingEquiv_algebraMap]
    change y.1 - ((q + n : ℚ) : ℝ) ∈ Ico (0 : ℝ) 1
    rw [Rat.cast_add, Rat.cast_intCast]
    constructor
    · have hf := Int.floor_le (y.1 - (q : ℝ))
      change (n : ℝ) ≤ y.1 - (q : ℝ) at hf
      linarith
    · have hf := Int.lt_floor_add_one (y.1 - (q : ℝ))
      change y.1 - (q : ℝ) < (n : ℝ) + 1 at hf
      linarith
  · rw [map_sub, rationalAdeleRealFiniteRingEquiv_algebraMap]
    change y.2 - algebraMap ℚ (FiniteAdeleRing ℤ ℚ) (q + n) ∈ _
    rw [map_add, map_intCast, ← sub_sub]
    exact finiteAdeleIntegerSubring.sub_mem hq (by simp)

end
end Dubon2026
