import Dubon2026.SourceCurvePicardGroup

/-! DUB-17/18 -> Kummer detection -> principal function from point-class division.
Use the actual Picard quotient once at the abstract field level so the
literal splitting-field consumer need not unfold its large field construction.
The division premise remains explicit and is not proved by this deduction. -/
namespace Dubon2026.SourceCurve.Pic0
noncomputable section
variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem exists_principal_of_nsmul_mk (n : ℕ) (A : Divisor.degZero (K := K) (F := F))
    (hdiv : ∃ y : Pic0 K F, n • y = mk A) :
    ∃ B : Divisor.degZero (K := K) (F := F), ∃ u : F, u ≠ 0 ∧
      ∀ v, v.ord u = A.val v + n * B.val v := by
  obtain ⟨y, hy⟩ := hdiv
  obtain ⟨B, hB⟩ := mk_surjective y
  have hyB : n • mk B = mk A := (congrArg (fun z : Pic0 K F => n • z) hB).trans hy
  have hq : mk (A - n • B) = 0 := by
    rw [map_sub, map_nsmul, hyB, sub_self]
  obtain ⟨u, hu, hord⟩ := (mk_eq_zero_iff _).mp hq
  refine ⟨-B, u, hu, fun v => ?_⟩
  have hv := (hord v).symm
  change v.ord u = A.val v - (n • B.val) v at hv
  change v.ord u = A.val v + n * (-B.val) v
  simpa only [Finsupp.smul_apply, nsmul_eq_mul, Finsupp.neg_apply,
    mul_neg, sub_eq_add_neg] using hv

end
end Dubon2026.SourceCurve.Pic0
