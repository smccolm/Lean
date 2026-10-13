import Dubon2026.OriginalRamifiedValuationRestriction
import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
import Mathlib.Topology.Algebra.UniformRing

/-! # The actual base-field embedding at original finite places

The original completion map used in the idele-class norm comparison for
DUB-17 must exist at ramified places too. The proved valuation power
formula supplies its continuity without an unramifiedness assumption.
-/

namespace Dubon2026
noncomputable section
open IsDedekindDomain
open scoped NumberField WithZero nonZeroDivisors Topology
open MonoidWithZeroHom.ValueGroup₀

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
variable (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L))
  [w.asIdeal.LiesOver v.asIdeal]

/-- The original field valuation restricts as the ramification-index power. -/
theorem original_valuation_algebraMap_pow (x : K) :
    w.valuation L (algebraMap K L x) =
      v.valuation K x ^ v.asIdeal.ramificationIdx w.asIdeal := by
  obtain ⟨r, d, hrd⟩ := IsLocalization.exists_mk'_eq (𝓞 K)⁰ x
  rw [← hrd, IsFractionRing.mk'_eq_div, map_div₀, map_div₀, map_div₀]
  have hi (a : 𝓞 K) : algebraMap K L (algebraMap (𝓞 K) K a) =
      algebraMap (𝓞 L) L (algebraMap (𝓞 K) (𝓞 L) a) := by
    rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]
  rw [hi, hi]
  simp only [HeightOneSpectrum.valuation_of_algebraMap, div_pow]
  rw [original_intValuation_algebraMap_pow v w r,
    original_intValuation_algebraMap_pow v w (d : 𝓞 K)]

/-- The original algebra map is uniformly continuous in the original finite-place uniformities. -/
theorem original_adicFieldMap_uniformContinuous :
    UniformContinuous (WithVal.map (v.valuation K) (w.valuation L) (algebraMap K L)) := by
  let f := WithVal.map (v.valuation K) (w.valuation L) (algebraMap K L)
  apply uniformContinuous_of_continuousAt_zero f.toAddMonoidHom
  simp only [ContinuousAt, map_zero]
  rw [(Valued.hasBasis_nhds_zero (WithVal (v.valuation K)) ℤᵐ⁰).tendsto_iff
    (Valued.hasBasis_nhds_zero (WithVal (w.valuation L)) ℤᵐ⁰)]
  intro γ _
  obtain ⟨y, hy⟩ := restrict₀_surjective
    (Valued.v (R := WithVal (w.valuation L))) γ.val
  have hy0 : y ≠ 0 := by
    intro hz
    subst y
    exact Units.ne_zero γ (by simpa using hy.symm)
  obtain ⟨x, hx⟩ := v.valuation_surjective K (min (w.valuation L y.ofVal) 1)
  have hx0 : x ≠ 0 := by
    intro hz
    have hyv : w.valuation L y.ofVal ≠ 0 := by
      simpa using hy0
    have hm : min (w.valuation L y.ofVal) 1 ≠ 0 := ne_of_gt (lt_min
      (pos_iff_ne_zero.mpr hyv) zero_lt_one)
    apply hm
    simpa only [hz, map_zero] using hx.symm
  let x' := WithVal.toVal (v.valuation K) x
  refine ⟨Units.mk0 ((Valued.v (R := WithVal (v.valuation K))).restrict x')
    (by simp [Valuation.restrict_def, restrict₀_apply, x', hx0]), trivial, ?_⟩
  intro z hz
  change (Valued.v (R := WithVal (w.valuation L))).restrict (f z) < γ.val
  rw [← hy]
  change (Valued.v (R := WithVal (w.valuation L))).restrict (f z) <
    (Valued.v (R := WithVal (w.valuation L))).restrict y
  rw [Valuation.restrict_lt_iff]
  change (Valued.v (R := WithVal (v.valuation K))).restrict z <
    (Valued.v (R := WithVal (v.valuation K))).restrict x' at hz
  rw [Valuation.restrict_lt_iff] at hz
  change v.valuation K z.ofVal < v.valuation K x at hz
  rw [hx] at hz
  change w.valuation L (algebraMap K L z.ofVal) < w.valuation L y.ofVal
  rw [original_valuation_algebraMap_pow K L v w]
  have he : 0 < v.asIdeal.ramificationIdx w.asIdeal := Nat.pos_of_ne_zero
    (Ideal.IsDedekindDomain.ramificationIdx_ne_zero_of_liesOver w.asIdeal v.ne_bot)
  exact (pow_le_of_le_one zero_le (le_of_lt (lt_min_iff.mp hz).2) he.ne').trans_lt
    (lt_min_iff.mp hz).1

end
end Dubon2026
