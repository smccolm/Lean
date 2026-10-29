import Dubon2026.SourceGammaOneModularStretch
import Dubon2026.SourceFrickeTraceSubgroup

/-! DUB-17/18 -> original Gamma1 degree/genus -> reduced field action
-> uniform level-power SL2 slash integrality. The level-M^2 subgroup
has the required invariance after the actual arbitrary-cusp chart.
Reuse the native level-raising integral conjugate and matrix identity;
no second diagonal matrix or determinant proof is introduced.
Adapted from the pinned Apache-2.0 Anthropic Sol integral-slash proof. -/
namespace Dubon2026.SourceFunctionField.IntegralSlash
noncomputable section
open Matrix Matrix.SpecialLinearGroup CongruenceSubgroup UpperHalfPlane
open scoped MatrixGroups ModularForm Pointwise

theorem levelRaise_dvd_of_Gamma1_sq {M : ℕ} {δ : SL(2, ℤ)}
    (hδ : δ ∈ Gamma1 (M ^ 2)) : (M : ℤ) ∣ δ.val 1 0 := by
  rw [Gamma1_mem] at hδ
  have h := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hδ.2.2
  exact (show (M : ℤ) ∣ ((M ^ 2 : ℕ) : ℤ) from ⟨M, by push_cast; ring⟩).trans h

theorem levelRaiseConj_mem_Gamma {M : ℕ} [NeZero M] {δ : SL(2, ℤ)}
    (hδ : δ ∈ Gamma1 (M ^ 2)) :
    levelRaiseConjOfDvd M δ (levelRaise_dvd_of_Gamma1_sq hδ) ∈ Gamma M := by
  have hg := hδ
  rw [Gamma1_mem] at hg
  obtain ⟨h00, h11, h10⟩ := hg
  have hdvd : M ∣ M ^ 2 := ⟨M, by ring⟩
  have h00' : ((δ 0 0 : ℤ) : ZMod M) = 1 := by
    simpa using congrArg (ZMod.castHom hdvd (ZMod M)) h00
  have h11' : ((δ 1 1 : ℤ) : ZMod M) = 1 := by
    simpa using congrArg (ZMod.castHom hdvd (ZMod M)) h11
  have h10' : ((δ 1 0 / M : ℤ) : ZMod M) = 0 := by
    obtain ⟨c, hc⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp h10
    rw [hc, show ((M ^ 2 : ℕ) : ℤ) * c = M * (M * c) by push_cast; ring,
      Int.mul_ediv_cancel_left _ (Nat.cast_ne_zero.mpr (NeZero.ne M)),
      ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact ⟨c, rfl⟩
  rw [Gamma_mem]
  refine ⟨h00', ?_, h10', h11'⟩
  change (((M : ℤ) * δ 0 1 : ℤ) : ZMod M) = 0
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
  exact ⟨δ 0 1, rfl⟩

theorem Gamma1_sq_le_conj_cusp (M : ℕ) [NeZero M] (β : SL(2, ℤ)) :
    (Gamma1 (M ^ 2) : Subgroup (GL (Fin 2) ℝ)) ≤
      ConjAct.toConjAct ((β : GL (Fin 2) ℝ) * levelRaiseMatrix M)⁻¹ •
        (Gamma1 M : Subgroup (GL (Fin 2) ℝ)) := by
  rintro x ⟨δ, hδ, rfl⟩
  rw [IntegralFricke.mem_conj_iff]
  refine ⟨β * levelRaiseConjOfDvd M δ (levelRaise_dvd_of_Gamma1_sq hδ) * β⁻¹,
    ?_, ?_⟩
  · have hg := (Gamma_normal M).conj_mem _ (levelRaiseConj_mem_Gamma hδ) β
    rw [Gamma_mem] at hg
    change β * levelRaiseConjOfDvd M δ (levelRaise_dvd_of_Gamma1_sq hδ) * β⁻¹ ∈ Gamma1 M
    rw [Gamma1_mem]
    exact ⟨hg.1, hg.2.2.2, hg.2.2.1⟩
  have he := levelRaiseMatrix_mul_mapGL M δ (levelRaise_dvd_of_Gamma1_sq hδ)
  have hc : mapGL ℝ (levelRaiseConjOfDvd M δ (levelRaise_dvd_of_Gamma1_sq hδ)) =
      levelRaiseMatrix M * mapGL ℝ δ * (levelRaiseMatrix M)⁻¹ := by
    rw [eq_mul_inv_iff_mul_eq]
    exact he
  rw [map_mul, map_mul, map_inv, hc]
  simp only [_root_.mul_inv_rev, mul_assoc]
  rfl

end
end Dubon2026.SourceFunctionField.IntegralSlash
