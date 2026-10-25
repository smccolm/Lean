import Dubon2026.SourceCurveKummerDetectingEvaluation
import Dubon2026.SourceCurveKummerRootPullback

/-! DUB-17/18 -> finite Weil detection -> corrected norm evaluation.
The abstract field calculation keeps the actual cover consumer small. It
combines the principal moving correction with the proved norm/reciprocity
ratio. The caller supplies the point-difference evaluation, not the ratio. -/
namespace Dubon2026.SourceCurve
noncomputable section
open IntermediateField
variable {K F E : Type*} [Field K] [IsAlgClosed K] [CharZero K] [Field F] [Field E]
variable [Algebra K F] [Algebra K E] [Algebra F E] [IsScalarTower K F E]
variable [FiniteDimensional F E] [Algebra.IsSeparable F E] [HasPrincipalDivisors K E]
variable (t : E) [FiniteDimensional K⟮t⟯ E]
include t

theorem exists_kummer_moved_evaluation
    (hbase : ∀ v : Place K F, Function.Bijective (algebraMap K v.ResidueField))
    (htop : ∀ v : Place K E, Function.Bijective (algebraMap K v.ResidueField))
    (n : ℕ) [NeZero n] (D D' : Divisor K F) (A B : Divisor K E)
    (f : F) (hf : f ≠ 0) (hfD : ∀ v : Place K F, v.ord f = (n : ℤ) * D v)
    (h : E) (hh : h ^ n = algebraMap F E f)
    (σ : E ≃ₐ[F] E) (ζ : K) (hσ : σ h = algebraMap K E ζ * h)
    (w : Place K E) (u : E) (hu : u ≠ 0)
    (hU : ∀ q : Place K E, q.ord u = A q + n * B q)
    (r : F) (hr : r ≠ 0) (hrD : ∀ v : Place K F, v.ord r = D' v - D v)
    (hA : ∀ q ∈ A.support, D' (q.restrict F) = 0)
    (hB : ∀ q ∈ B.support, D' (q.restrict F) = 0)
    (hw : D' (w.restrict F) = 0)
    (hfiber : ∀ v ∈ D'.support, ∀ q : Place K E, q.restrict F = v → q.ord u = 0)
    (huSupport : ∀ q : Place K E, q.ord u ≠ 0 → D' (q.restrict F) = 0)
    (hpoint : ∀ H : E, H ≠ 0 → σ H = algebraMap K E ζ * H → w.ord H = 0 →
      rationalDivisorEval htop H A = ζ) :
    ∃ g : F, g ≠ 0 ∧ (∀ v : Place K F, v.ord g = (n : ℤ) * D' v) ∧
      rationalDivisorEval hbase g (Divisor.geometricPushforward F B) /
        rationalDivisorEval hbase (Algebra.norm F u) D' = ζ⁻¹ := by
  let g : F := f * r ^ n
  let H : E := h * algebraMap F E r
  have hg : g ≠ 0 := mul_ne_zero hf (pow_ne_zero n hr)
  have hh0 : h ≠ 0 := by
    intro hz
    rw [hz, zero_pow (NeZero.ne n)] at hh
    exact ((map_ne_zero (algebraMap F E)).mpr hf) hh.symm
  have hH : H ≠ 0 := mul_ne_zero hh0 ((map_ne_zero (algebraMap F E)).mpr hr)
  have hgD (v : Place K F) : v.ord g = (n : ℤ) * D' v := by
    change v.ord (f * r ^ n) = _
    rw [v.ord_mul hf (pow_ne_zero _ hr), ← zpow_natCast r n, v.ord_zpow, hfD, hrD]
    ring
  have hHpow : H ^ n = algebraMap F E g := by
    change (h * algebraMap F E r) ^ n = algebraMap F E (f * r ^ n)
    rw [mul_pow, hh, map_mul, map_pow]
  have hHσ : σ H = algebraMap K E ζ * H := by
    change σ (h * algebraMap F E r) = algebraMap K E ζ * (h * algebraMap F E r)
    rw [map_mul, hσ, σ.commutes, mul_assoc]
  have hHD := ord_eq_finitePullback_of_pow_eq n D' g H hgD hHpow
  have hHzero (q : Place K E) (hq : D' (q.restrict F) = 0) : q.ord H = 0 :=
    (hHD q).trans (finitePullback_apply_zero_of_restrict D' q hq)
  refine ⟨g, hg, hgD, ?_⟩
  exact kummer_norm_detecting_ratio t hbase htop n D' A B H u g ζ hH hu hg hHpow
    hU hHD (fun q hq => hHzero q (hA q hq)) (fun q hq => hHzero q (hB q hq))
    hfiber (fun q hq => hHzero q (huSupport q hq)) (hpoint H hH hHσ (hHzero w hw))

end
end Dubon2026.SourceCurve
