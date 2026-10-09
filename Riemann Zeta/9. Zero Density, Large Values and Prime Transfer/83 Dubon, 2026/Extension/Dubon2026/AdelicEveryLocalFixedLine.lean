import Dubon2026.AdelicBadLocalFixedLine
import Dubon2026.AdelicLocalCyclicProjection

/-! # The genuine local cyclic level-fixed line at every original finite place -/

namespace Dubon2026

noncomputable section
open IsDedekindDomain Matrix

/-- At every genuine finite place, the actual original primitive cyclic level-fixed space consists exactly of scalar multiples of its original generator. -/
theorem adelicEveryLocalCyclic_fixed_generator_scalar {N : ℕ} [NeZero N] {k : ℤ}
    (F : PrimitiveCuspForm N k) (hk : 0 < k) (v : HeightOneSpectrum ℤ)
    (x : AdelicCyclicHilbert F.toCuspForm) (hx : x ∈ adelicLocalCyclicClosedSpan F.toCuspForm v)
    (hfix : x ∈ adelicLocalFixedSpace F.toCuspForm v) :
    ∃ c : ℂ, x = c • adelicCyclicHilbertGenerator F.toCuspForm := by
  by_cases hv : IsGoodAdelicPlace N v
  · obtain ⟨p, hp, hpN, rfl⟩ := hv
    letI : NeZero p := ⟨hp.ne_zero⟩
    letI : Fact p.Prime := ⟨hp⟩
    exact adelicLocalCyclic_fixed_generator_scalar F hpN x hx hfix
  · exact adelicBadLocalCyclic_fixed_generator_scalar F hk v hv x hx hfix

/-- Every original finite place has precisely the genuine primitive generator line as its local cyclic level-fixed subspace. -/
theorem adelicEveryLocalCyclic_fixed_eq_generator_line {N : ℕ} [NeZero N] {k : ℤ}
    (F : PrimitiveCuspForm N k) (hk : 0 < k) (v : HeightOneSpectrum ℤ) :
    adelicLocalCyclicClosedSpan F.toCuspForm v ⊓ adelicLocalFixedSpace F.toCuspForm v =
      Submodule.span ℂ {adelicCyclicHilbertGenerator F.toCuspForm} := by
  apply le_antisymm
  · intro x hx
    obtain ⟨c, hc⟩ := adelicEveryLocalCyclic_fixed_generator_scalar F hk v x hx.1 hx.2
    exact Submodule.mem_span_singleton.mpr ⟨c, hc.symm⟩
  · apply Submodule.span_le.mpr
    intro x hx
    obtain rfl := Set.mem_singleton_iff.mp hx
    exact ⟨adelicLocalCyclicClosedSpan_generator_mem F.toCuspForm v,
      adelicCyclicHilbertGenerator_mem_localFixed F.toCuspForm v⟩

/-- The genuine original cyclic projection sends every actual local level-fixed Hilbert vector to the primitive generator line at every finite place. -/
theorem adelicEveryLocalCyclicProjection_fixed_scalar {N : ℕ} [NeZero N] {k : ℤ}
    (F : PrimitiveCuspForm N k) (hk : 0 < k) (v : HeightOneSpectrum ℤ)
    (x : AdelicCyclicHilbert F.toCuspForm) (hx : x ∈ adelicLocalFixedSpace F.toCuspForm v) :
    ∃ c : ℂ, adelicLocalCyclicProjection F.toCuspForm v x = c • adelicCyclicHilbertGenerator F.toCuspForm :=
  adelicEveryLocalCyclic_fixed_generator_scalar F hk v _
    (@Submodule.starProjection_apply_mem ℂ (AdelicCyclicHilbert F.toCuspForm)
      inferInstance inferInstance inferInstance (adelicLocalCyclicClosedSpan F.toCuspForm v) inferInstance x)
    (adelicLocalCyclicProjection_fixed F.toCuspForm v x hx)

end
end Dubon2026
