import Dubon2026.SourceCurvePicardGroup

/-! DUB-17/18 -> auxiliary point-class division. A principal difference
between an integer multiple and the target divisor gives the required
division in the actual degree-zero Picard quotient. -/
namespace Dubon2026.SourceCurve.Pic0
noncomputable section
variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem exists_nsmul_mk_of_principal_difference (n : ℕ)
    (D : Divisor.degZero (K := K) (F := F)) (B : Divisor K F)
    (hB : Divisor.degree B = 0) (h : Divisor.IsPrincipal (n • B - D.val)) :
    ∃ y : Pic0 K F, n • y = mk D := by
  let B₀ : Divisor.degZero (K := K) (F := F) := ⟨B, hB⟩
  refine ⟨mk B₀, ?_⟩
  apply sub_eq_zero.mp
  rw [← map_nsmul, ← map_sub]
  exact (mk_eq_zero_iff _).mpr h

end
end Dubon2026.SourceCurve.Pic0
