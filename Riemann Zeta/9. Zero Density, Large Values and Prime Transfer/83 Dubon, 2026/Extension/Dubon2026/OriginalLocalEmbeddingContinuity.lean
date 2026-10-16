import Dubon2026.OriginalLocalEmbeddingValuation
import Dubon2026.LocalFieldOriginalNorm
import Mathlib.Topology.Algebra.UniformRing
import Mathlib.Algebra.Order.Archimedean.Basic

/-! # Continuity of the original embedding at its induced finite prime

The proved valuation equivalence and powers of the original rational
prime give an explicit neighbourhood comparison. This extends the actual
field embedding toward the individual completion in DUB-17's orbit indexing.
-/
namespace Dubon2026
noncomputable section
open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum Topology
open scoped NumberField ValuativeRel WithZero

variable (L E : Type) [Field L] [NumberField L] [Field E] [Algebra L E]
  (p : ℕ) (hp : p.Prime) [Algebra (rationalPrimeLocalField p hp) E]
  [ValuativeRel E] [UniformSpace E] [IsUniformAddGroup E] [IsNonarchimedeanLocalField E]
  [(ValuativeRel.valuation (rationalPrimeLocalField p hp)).HasExtension (ValuativeRel.valuation E)]

/-- The original field embedding, with the genuine induced adic uniformity on its domain. -/
def originalLocalEmbeddingAdicMap : WithVal ((originalLocalEmbeddingPrime L E p hp).valuation L) →+* E :=
  (algebraMap L E).comp (WithVal.equiv _).toRingHom

/-- The literal original embedding is uniformly continuous for the
genuine induced prime-adic uniformity and original local-field uniformity. -/
theorem originalLocalEmbeddingAdicMap_uniformContinuous :
    UniformContinuous (originalLocalEmbeddingAdicMap L E p hp) := by
  let w := originalLocalEmbeddingPrime L E p hp
  let A := WithVal (w.valuation L)
  let f := originalLocalEmbeddingAdicMap L E p hp
  let normE := localFieldOriginalNorm E
  letI : NontriviallyNormedField E := normE
  letI : NormedField E := normE.toNormedField
  have hpv : ValuativeRel.valuation E (p : E) < 1 := by
    rw [← map_natCast (algebraMap (rationalPrimeLocalField p hp) E) p]
    exact (Valuation.HasExtension.val_map_lt_one_iff
      (ValuativeRel.valuation (rationalPrimeLocalField p hp)) (ValuativeRel.valuation E) _).mpr
      (rationalPrimeLocal_valuation_prime_lt_one p hp)
  have hpn : ‖(p : E)‖ < 1 := by
    apply lt_of_not_ge
    intro h
    have he := (localFieldOriginalNorm_le_iff E 1 (p : E)).mp (by simpa only [norm_one] using h)
    exact (not_le_of_gt hpv) (by simpa only [map_one] using he)
  apply uniformContinuous_of_continuousAt_zero f.toAddMonoidHom
  rw [ContinuousAt, map_zero]
  change Filter.Tendsto f (𝓝 (0 : A)) (𝓝 (0 : E))
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hε hpn
  let t : A := WithVal.toVal (w.valuation L) ((p : L) ^ n)
  have ht : t ≠ 0 := by
    intro hz
    have he := congrArg (WithVal.equiv (w.valuation L)) hz
    have he' : (p : L) ^ n = 0 := he
    exact (pow_ne_zero n (Nat.cast_ne_zero.mpr hp.ne_zero)) he'
  have htv : 0 < (Valued.v (R := A)).restrict t := by
    apply pos_iff_ne_zero.mpr
    exact fun h => ht (((Valued.v (R := A)).zero_iff).mp
      (((Valued.v (R := A)).restrict_eq_zero_iff).mp h))
  have hb : {x : A | (Valued.v (R := A)).restrict x < (Valued.v (R := A)).restrict t} ∈ 𝓝 (0 : A) :=
    (Valued.isOpen_ball A _).mem_nhds (by
      change (Valued.v (R := A)).restrict 0 < (Valued.v (R := A)).restrict t
      simpa only [map_zero] using htv)
  filter_upwards [hb] with x hx
  have hxv : w.valuation L x.ofVal < w.valuation L ((p : L) ^ n) :=
    (Valued.v (R := A)).restrict_lt_iff.mp hx
  have he := (originalLocalEmbeddingPrime_valuation_isEquiv L E p hp).lt_iff_lt.mp hxv
  have he' : ValuativeRel.valuation E (f x) < ValuativeRel.valuation E ((p : E) ^ n) := by
    simpa only [Valuation.comap_apply, map_pow, map_natCast] using he
  have hnorm : ‖f x‖ < ‖(p : E) ^ n‖ := by
    apply lt_of_not_ge
    intro h
    exact (not_le_of_gt he') ((localFieldOriginalNorm_le_iff E _ _).mp h)
  simpa only [dist_zero_right, norm_pow] using hnorm.trans (by simpa only [norm_pow] using hn)

end
end Dubon2026
