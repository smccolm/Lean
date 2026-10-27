import Dubon2026.SourceCyclotomicFrickeIndex
import Mathlib.NumberTheory.Cyclotomic.Basic
import Mathlib.RingTheory.Trace.Basic

/-! DUB-17/18 -> actual Gamma1 differential realization -> rational Fourier
structure -> trace descent over the original cyclotomic field. Reuse native
finite cyclotomic-extension and Galois theorems for the actual field generated
by the level root of unity. This supplies the trace-dual basis argument. -/
namespace Dubon2026.SourceFricke
noncomputable section

theorem isCyclotomicExtension_kN (N : ℕ) [NeZero N] :
    IsCyclotomicExtension {N} ℚ (kN N) := by
  have hζ := isPrimitiveRoot_zetaN (NeZero.ne N)
  change IsCyclotomicExtension {N} ℚ (IntermediateField.adjoin ℚ {zetaN N}).toSubalgebra
  rw [IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic
    (hζ.isIntegral (NeZero.pos N)).tower_top.isAlgebraic]
  exact hζ.adjoin_isCyclotomicExtension ℚ

theorem finiteDimensional_kN (N : ℕ) [NeZero N] : FiniteDimensional ℚ (kN N) := by
  letI := isCyclotomicExtension_kN N
  exact IsCyclotomicExtension.finiteDimensional {N} ℚ (kN N)

theorem isGalois_kN (N : ℕ) [NeZero N] : IsGalois ℚ (kN N) := by
  letI := isCyclotomicExtension_kN N
  exact IsCyclotomicExtension.isGalois {N} ℚ (kN N)

end
end Dubon2026.SourceFricke
