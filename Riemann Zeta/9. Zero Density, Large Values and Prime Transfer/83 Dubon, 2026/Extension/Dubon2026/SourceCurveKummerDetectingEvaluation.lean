import Dubon2026.SourceCurveFiniteCoordinateReciprocity

/-! DUB-17/18 -> the actual Kummer detecting ratio -> norm/reciprocity algebra.
Use the proved finite-coordinate reciprocity and norm adjunction at the
abstract field level. The literal cover consumer supplies the point-difference
evaluation and every geometric input. -/
namespace Dubon2026.SourceCurve
noncomputable section
open IntermediateField
variable {K F E : Type*} [Field K] [IsAlgClosed K] [CharZero K] [Field F] [Field E]
variable [Algebra K F] [Algebra K E] [Algebra F E] [IsScalarTower K F E]
variable [FiniteDimensional F E] [Algebra.IsSeparable F E] [HasPrincipalDivisors K E]
variable (t : E) [FiniteDimensional K⟮t⟯ E]
include t

theorem kummer_norm_detecting_ratio
    (hbase : ∀ v : Place K F, Function.Bijective (algebraMap K v.ResidueField))
    (htop : ∀ v : Place K E, Function.Bijective (algebraMap K v.ResidueField))
    (n : ℕ) (D : Divisor K F) (A B : Divisor K E) (H u : E) (g : F) (ζ : K)
    (hH : H ≠ 0) (hu : u ≠ 0) (hg : g ≠ 0)
    (hpow : H ^ n = algebraMap F E g)
    (hU : ∀ v : Place K E, v.ord u = A v + n * B v)
    (hHD : ∀ v : Place K E, v.ord H = Divisor.finitePullback E D v)
    (hA : ∀ v ∈ A.support, v.ord H = 0)
    (hB : ∀ v ∈ B.support, v.ord H = 0)
    (hD : ∀ v ∈ D.support, ∀ q : Place K E, q.restrict F = v → q.ord u = 0)
    (hdisj : ∀ v : Place K E, v.ord u ≠ 0 → v.ord H = 0)
    (hvalue : rationalDivisorEval htop H A = ζ) :
    rationalDivisorEval hbase g (Divisor.geometricPushforward F B) /
      rationalDivisorEval hbase (Algebra.norm F u) D = ζ⁻¹ := by
  let b := rationalDivisorEval htop H B
  have hb : b ≠ 0 := rationalDivisorEval_ne_zero htop H hH B hB
  have hnum : rationalDivisorEval hbase g (Divisor.geometricPushforward F B) = b ^ n := by
    rw [rationalDivisorEval_geometricPushforward hbase htop B g hg (by
      intro v hv
      rw [← hpow, ← zpow_natCast H n, v.ord_zpow, hB v hv, mul_zero])]
    rw [← hpow]
    exact rationalDivisorEval_pow htop H B (fun v hv => v.mem_of_ord_nonneg (hB v hv).ge) n
  have hrec : rationalDivisorEval htop u (Divisor.finitePullback E D) =
      rationalDivisorEval htop H (A + n • B) := by
    apply finite_coordinate_weil_reciprocity t htop u H hu hH (A + n • B)
      (Divisor.finitePullback E D)
    · intro v
      simpa only [Finsupp.add_apply, Finsupp.smul_apply, nsmul_eq_mul] using (hU v).symm
    · exact fun v => (hHD v).symm
    · exact hdisj
  have hne : ∀ v, v ∈ A.support ∨ v ∈ (n • B).support → v.rationalEval (htop v) H ≠ 0 := by
    intro v hv
    apply v.rationalEval_ne_zero_of_ord_eq_zero _ hH
    rcases hv with hv | hv
    · exact hA v hv
    · exact hB v (Finsupp.support_smul hv)
  have hden : rationalDivisorEval hbase (Algebra.norm F u) D = ζ * b ^ n := by
    rw [← rationalDivisorEval_finitePullback hbase htop D u
      (fun v hv q hq => (hD v hv q hq).ge), hrec,
      rationalDivisorEval_add htop H A (n • B) hne, hvalue, rationalDivisorEval_nsmul]
  rw [hnum, hden, div_mul_cancel_right₀ (pow_ne_zero n hb)]

end
end Dubon2026.SourceCurve
