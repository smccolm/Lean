import Dubon2026.OriginalFinitePrimeOrbits
import Dubon2026.OriginalAdicDecompositionAction

/-! # The full-decomposition prime is the unique original prime above its base

Reuse the existing original prime-orbit theorem. This identifies the
selected arithmetic completion with the full-decomposition prime, so
DUB-17's actual total invariant evaluates the constructed local class.
-/
namespace Dubon2026
noncomputable section
open scoped NumberField

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [FiniteDimensional K L] [IsGalois K L]

omit [NumberField L] in
/-- A prime with full original decomposition group is the only original prime above its contracted base prime. -/
theorem originalFullDecomposition_prime_unique
    (w t : IsDedekindDomain.HeightOneSpectrum (𝓞 L))
    (hw : OriginalFiniteDecompositionGroup K L w = ⊤)
    (ht : originalFinitePrimeBelow K L w = originalFinitePrimeBelow K L t) : t = w := by
  obtain ⟨σ, hσ⟩ := (originalFinitePrimeBelow_eq_iff_orbit K L w t).mp ht
  have hs : σ ∈ OriginalFiniteDecompositionGroup K L w := by
    rw [hw]
    exact Subgroup.mem_top σ
  exact hσ.symm.trans hs

end
end Dubon2026
