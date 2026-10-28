import Dubon2026.SourceParabolicBinaryRationalSpan
import Dubon2026.SourceOriginalParabolicEigensystem

/-! DUB17/18 -> original all-weight association -> original parabolic
finite character -> rational structure of the actual source eigenclass.
The native cocycle quotient transports the proved parabolic rational
span. The original primitive period class is an explicit consumer.
Uniform integral parabolic denominator clearing and finite descent
remain; complex/rational spanning alone does not imply either. -/
namespace Dubon2026
noncomputable section
open CongruenceSubgroup groupCohomology

theorem sourceComplexParabolicBinaryH1_mem_rational_span (Q w : ℕ) [NeZero Q]
    (x : H1 (sourceBinaryCoefficientRep ℂ Q w))
    (hx : x ∈ sourceParabolicH1 (Gamma0 Q) (sourceBinaryCoefficientRep ℂ Q w)) :
    x ∈ Submodule.span ℂ (sourceBinaryH1Change (algebraMap ℚ ℂ) Q w ''
      (sourceParabolicH1 (Gamma0 Q) (sourceBinaryCoefficientRep ℚ Q w) :
        Set (H1 (sourceBinaryCoefficientRep ℚ Q w)))) := by
  obtain ⟨c, hc, rfl⟩ := hx
  have hspan := sourceComplexParabolicBinaryCocycle_mem_rational_span Q w c hc
  clear hc
  induction hspan using Submodule.span_induction with
  | mem c hc =>
    obtain ⟨z, hz, rfl⟩ := hc
    rw [← sourceBinaryH1Change_cocycle]
    exact Submodule.subset_span ⟨H1π _ z,
      (sourceParabolicH1_cocycle_iff _ _ _).mpr hz, rfl⟩
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add c d _ _ hc hd => rw [map_add]; exact Submodule.add_mem _ hc hd
  | smul a c _ hc => rw [map_smul]; exact Submodule.smul_mem _ _ hc

theorem sourcePrimitive_originalParabolicH1_mem_rational_span
    {Q : ℕ} [NeZero Q] {k : ℤ} (f : PrimitiveCuspForm Q k) (hk : 2 ≤ k) :
    sourceOriginalBinaryPeriodCohomology Q k hk f.toCuspForm ∈
      Submodule.span ℂ (sourceBinaryH1Change (algebraMap ℚ ℂ) Q (k - 2).toNat ''
        (sourceParabolicH1 (Gamma0 Q) (sourceBinaryCoefficientRep ℚ Q (k - 2).toNat) :
          Set (H1 (sourceBinaryCoefficientRep ℚ Q (k - 2).toNat)))) :=
  sourceComplexParabolicBinaryH1_mem_rational_span Q (k - 2).toNat _
    (sourceOriginalBinaryPeriodCohomology_parabolic Q k hk f.toCuspForm)

end
end Dubon2026
