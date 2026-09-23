import TaoTrudgianYang2025.SargosRealQuarticPrefix

/-! The finite prefix maximum equals the maximum over the source's real endpoints. -/

noncomputable section

open Set GafniTao
open scoped BigOperators

namespace TaoTrudgianYang2025

def sargosRealQuarticSumTo (M X : ℝ) (z : ℤ → ℂ) (α γ : ℝ) : ℂ :=
  ∑ n ∈ Finset.Ioc ⌊M⌋ ⌊X⌋,
    z n*fordAdditiveCharacter ((n:ℝ)^2*α+(n:ℝ)^4*γ)

def sargosRealEndpointMaximum (M : ℝ) (z : ℤ → ℂ) (α γ : ℝ) : ℝ :=
  sSup ((fun X : ℝ => ‖sargosRealQuarticSumTo M X z α γ‖) '' Ioc M (2*M))

theorem sargosRealQuarticSumTo_prefix {M X : ℝ} (hMX : M ≤ X)
    (z : ℤ → ℂ) (α γ : ℝ) :
    sargosRealQuarticSumTo M X z α γ =
      sargosRealQuarticPrefix M (⌊X⌋-⌊M⌋).toNat z α γ := by
  have hfloor := Int.floor_mono hMX
  have hcast := Int.toNat_of_nonneg (sub_nonneg.mpr hfloor)
  have he : ⌊M⌋+((⌊X⌋-⌊M⌋).toNat:ℤ) = ⌊X⌋ := by omega
  simp only [sargosRealQuarticSumTo,sargosRealQuarticPrefix,he]

theorem norm_sargosRealQuarticSumTo_le_maximum {M X : ℝ}
    (hMX : M ≤ X) (hX : X ≤ 2*M) (z : ℤ → ℂ) (α γ : ℝ) :
    ‖sargosRealQuarticSumTo M X z α γ‖ ≤ sargosRealQuarticMaximum M z α γ := by
  rw [sargosRealQuarticSumTo_prefix hMX]
  have hlen : (⌊X⌋-⌊M⌋).toNat ≤ sargosRealBlockLength M := by
    apply Int.toNat_le_toNat
    exact sub_le_sub_right (Int.floor_mono hX) _
  exact Finset.le_sup' (fun H => ‖sargosRealQuarticPrefix M H z α γ‖)
    (Finset.mem_range.mpr (Nat.lt_succ_of_le hlen))

theorem sargosRealQuarticMaximum_attained_endpoint {M : ℝ} (hM : 0 < M)
    (z : ℤ → ℂ) (α γ : ℝ) :
    ∃ X : ℝ, X ∈ Ioc M (2*M) ∧
      sargosRealQuarticMaximum M z α γ = ‖sargosRealQuarticSumTo M X z α γ‖ := by
  obtain ⟨H,hH,hatt⟩ := Finset.exists_mem_eq_sup'
    (Finset.nonempty_range_iff.mpr (Nat.succ_ne_zero (sargosRealBlockLength M)))
    (fun H => ‖sargosRealQuarticPrefix M H z α γ‖)
  have hHle : H ≤ sargosRealBlockLength M := Nat.le_of_lt_succ (Finset.mem_range.mp hH)
  change sargosRealQuarticMaximum M z α γ = ‖sargosRealQuarticPrefix M H z α γ‖ at hatt
  by_cases hH0 : H = 0
  · have hz : sargosRealQuarticMaximum M z α γ = 0 := by
      simpa only [hH0,sargosRealQuarticPrefix,Nat.cast_zero,add_zero,Finset.Ioc_self,
        Finset.sum_empty,norm_zero] using hatt
    refine ⟨2*M,⟨by linarith only [hM],le_rfl⟩,?_⟩
    have hb := norm_sargosRealQuarticSumTo_le_maximum
      (by linarith only [hM] : M ≤ 2*M) le_rfl z α γ
    rw [hz] at hb ⊢
    exact (le_antisymm hb (norm_nonneg _)).symm
  · let X : ℝ := ((⌊M⌋+(H:ℤ):ℤ):ℝ)
    have hL := sargosRealBlockLength_cast hM.le
    have hfloor := Int.floor_le (2*M)
    have hnext := Int.lt_floor_add_one M
    have hcast : (1:ℝ) ≤ H := by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hH0)
    have hle : (⌊M⌋:ℤ)+(H:ℤ) ≤ ⌊2*M⌋ := by omega
    have hleReal : X ≤ (⌊2*M⌋:ℝ) := by
      dsimp [X]
      exact_mod_cast hle
    have hMX : M < X := by dsimp [X]; push_cast; linarith only [hnext,hcast]
    refine ⟨X,⟨hMX,hleReal.trans hfloor⟩,?_⟩
    have he : ⌊X⌋ = ⌊M⌋+(H:ℤ) := by dsimp [X]; exact Int.floor_intCast _
    simpa only [sargosRealQuarticSumTo,he,sargosRealQuarticPrefix] using hatt

theorem sargosRealEndpointMaximum_eq {M : ℝ} (hM : 0 < M)
    (z : ℤ → ℂ) (α γ : ℝ) :
    sargosRealEndpointMaximum M z α γ = sargosRealQuarticMaximum M z α γ := by
  obtain ⟨X,hX,he⟩ := sargosRealQuarticMaximum_attained_endpoint hM z α γ
  have hmem : ‖sargosRealQuarticSumTo M X z α γ‖ ∈
      (fun X : ℝ => ‖sargosRealQuarticSumTo M X z α γ‖) '' Ioc M (2*M) :=
    ⟨X,hX,rfl⟩
  have hbound : ∀ y ∈ (fun X : ℝ => ‖sargosRealQuarticSumTo M X z α γ‖) '' Ioc M (2*M),
      y ≤ sargosRealQuarticMaximum M z α γ := by
    rintro y ⟨Y,hY,rfl⟩
    exact norm_sargosRealQuarticSumTo_le_maximum hY.1.le hY.2 z α γ
  apply le_antisymm
  · exact csSup_le ⟨_,hmem⟩ hbound
  · rw [he]
    exact le_csSup ⟨_,hbound⟩ hmem

end TaoTrudgianYang2025
