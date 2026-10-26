import Dubon2026.SourceWeierstrassTorsionFourierCoefficients

/-! DUB-17/18 -> original all-weight arithmetic association -> finite
Gamma1 character realization -> Picard/H1 and diamond comparison ->
differential realization -> rational Fourier structure -> cyclotomic
Fricke expansions. The actual torsion expansion is regrouped by its
finite exponent fibers and identified with the native q-expansion.
Adapted from anthropics/fermats-last-theorem at
6e837e75355538c7f80bab5b956861e86c4eacc2 (Apache License 2.0).
No external theorem module or toolchain is imported. -/
namespace Dubon2026.SourceFricke
noncomputable section
open Complex Real PeriodPair
open UpperHalfPlane hiding I
open scoped UpperHalfPlane Manifold MatrixGroups ModularForm

lemma summable_comp_fst_fin {β : Type*} {g : β → ℝ} (hg0 : ∀ b, 0 ≤ g b) (hg : Summable g)
    (k : ℕ) : Summable fun x : β × Fin k ↦ g x.1 := by
  refine (summable_prod_of_nonneg (fun x => hg0 x.1)).mpr ⟨fun _ => (hasSum_fintype _).summable, ?_⟩
  simpa [tsum_fintype] using hg.mul_left (k : ℝ)

theorem hasSum_wpMon {N a₁ a₂ : ℕ} (ha₁ : a₁ < N) {τ : ℂ} (hτ : 0 < τ.im) :
    HasSum (fun i : WpIdx ↦ wpMonCoeff N a₁ a₂ i * qN N τ ^ wpMonExp N a₁ i)
      (wpNormSeries N a₁ a₂ τ) := by
  have hN : 0 < N := by omega
  set q : ℂ := qN N τ with hqdef
  have hq : ‖q‖ < 1 := norm_qN_lt_one hN hτ
  set G : WpIdx → ℂ := fun i ↦ wpMonCoeff N a₁ a₂ i * q ^ wpMonExp N a₁ i with hG
  set r : ℂ := zetaN N ^ a₂ * q ^ a₁ with hr

  have h1 : HasSum (G ∘ Sum.inl)
      (1 / 12 + if a₁ = 0 then zetaN N ^ a₂ / (1 - zetaN N ^ a₂) ^ 2 else 0) := by
    have := hasSum_fintype (G ∘ Sum.inl)
    simpa [hG, wpMonCoeff, wpMonExp] using this

  have h2 : HasSum (G ∘ Sum.inr ∘ Sum.inl) (if a₁ = 0 then 0 else r / (1 - r) ^ 2) := by
    by_cases ha : a₁ = 0
    · simp only [ha, if_true]
      convert hasSum_zero with m
      simp [hG, wpMonCoeff, ha]
    · simp only [ha, if_false]
      have hr1 : ‖r‖ < 1 := by
        rw [hr, norm_mul, norm_pow, norm_zetaN, one_pow, one_mul, norm_pow]
        exact pow_lt_one₀ (norm_nonneg _) hq ha
      have hgeo := hasSum_coe_mul_geometric_of_norm_lt_one hr1
      have hs : Summable fun m : ℕ+ ↦ ((m : ℕ) : ℂ) * r ^ (m : ℕ) :=
        summable_pnat_iff_summable_nat.mpr hgeo.summable
      have h2' : HasSum (fun m : ℕ+ ↦ ((m : ℕ) : ℂ) * r ^ (m : ℕ)) (r / (1 - r) ^ 2) := by
        rw [hs.hasSum_iff, ← hgeo.tsum_eq, ← tsum_zero_pnat_eq_tsum_nat hgeo.summable]
        simp
      refine h2'.congr_fun fun m ↦ ?_
      simp only [hG, Function.comp_apply, wpMonCoeff, wpMonExp, ha, if_false, hr]
      rw [mul_pow, ← pow_mul, ← pow_mul]
      ring

  have hmaj := summable_comp_fst_fin (fun p ↦ by positivity)
    (summable_wpTail_majorant (norm_nonneg q) hq) 3
  have hq1 : ‖q‖ ≤ 1 := hq.le
  have hbound : ∀ x : (ℕ+ × ℕ+) × Fin 3, ‖(G ∘ Sum.inr ∘ Sum.inr) x‖ ≤
      4 * ((x.1.2 : ℕ) * ‖q‖ ^ ((x.1.1 : ℕ) * (x.1.2 : ℕ))) := by
    rintro ⟨⟨c, m⟩, i⟩
    obtain ⟨hc, hm⟩ := le_wpMonExp_tail ha₁ (c, m) i
    have hcm : (c : ℕ) * (m : ℕ) ≤ wpMonExp N a₁ (Sum.inr (Sum.inr ((c, m), i))) := by
      fin_cases i
      · exact Nat.mul_le_mul_right _ (le_add_right (Nat.le_mul_of_pos_right _ hN))
      · exact Nat.mul_le_mul_right _ (le_mul_sub_of_lt ha₁ c)
      · exact Nat.mul_le_mul_right _ (Nat.le_mul_of_pos_right _ hN)
    have hpow : ‖q‖ ^ wpMonExp N a₁ (Sum.inr (Sum.inr ((c, m), i))) ≤ ‖q‖ ^ ((c : ℕ) * (m : ℕ)) :=
      pow_le_pow_of_le_one (norm_nonneg _) hq1 hcm
    have hz : ‖zetaN N‖ = 1 := norm_zetaN N
    have hcoef : ‖wpMonCoeff N a₁ a₂ (Sum.inr (Sum.inr ((c, m), i)))‖ ≤ 2 * (m : ℕ) := by
      fin_cases i <;> simp [wpMonCoeff, hz]
    simp only [Function.comp_apply, hG, norm_mul, norm_pow]
    have hm0 : (0 : ℝ) ≤ (m : ℕ) := by positivity
    calc ‖wpMonCoeff N a₁ a₂ (Sum.inr (Sum.inr ((c, m), i)))‖ *
          ‖q‖ ^ wpMonExp N a₁ (Sum.inr (Sum.inr ((c, m), i)))
        ≤ (2 * (m : ℕ)) * ‖q‖ ^ ((c : ℕ) * (m : ℕ)) := by gcongr
      _ ≤ 4 * ((m : ℕ) * ‖q‖ ^ ((c : ℕ) * (m : ℕ))) := by nlinarith [pow_nonneg (norm_nonneg q) ((c : ℕ) * (m : ℕ))]
  have hs3 : Summable (G ∘ Sum.inr ∘ Sum.inr) := Summable.of_norm_bounded hmaj hbound
  have h3 : HasSum (G ∘ Sum.inr ∘ Sum.inr) (∑' p : ℕ+ × ℕ+, wpTail N a₁ a₂ p τ) := by
    rw [hs3.hasSum_iff, hs3.tsum_prod]
    refine tsum_congr fun p ↦ ?_
    rw [tsum_fintype, Fin.sum_univ_three]
    simp only [Function.comp_apply, hG, wpMonCoeff, wpMonExp, wpTail, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val, hqdef]
    ring
  have hall := h1.sum (h2.sum h3)
  have heq : (1 / 12 + if a₁ = 0 then zetaN N ^ a₂ / (1 - zetaN N ^ a₂) ^ 2 else 0) +
      ((if a₁ = 0 then 0 else r / (1 - r) ^ 2) + ∑' p : ℕ+ × ℕ+, wpTail N a₁ a₂ p τ) =
      wpNormSeries N a₁ a₂ τ := by
    by_cases ha : a₁ = 0
    · subst ha
      rw [if_pos rfl, if_pos rfl]
      unfold wpNormSeries
      rw [← hqdef, pow_zero, mul_one]
      ring
    · rw [if_neg ha, if_neg ha]
      unfold wpNormSeries
      rw [← hqdef, ← hr]
      ring
  rw [← heq]
  exact hall

theorem hasSum_wpQCoeff {N a₁ a₂ : ℕ} (ha₁ : a₁ < N) {τ : ℂ} (hτ : 0 < τ.im) :
    HasSum (fun n ↦ wpQCoeff N a₁ a₂ n * qN N τ ^ n) (wpNormSeries N a₁ a₂ τ) := by
  refine ((hasSum_wpMon (a₂ := a₂) ha₁ hτ).tsum_fiberwise (wpMonExp N a₁)).congr_fun fun n ↦ ?_
  rw [wpQCoeff, ← tsum_mul_right]
  exact tsum_congr fun i ↦ by rw [show wpMonExp N a₁ i = n from i.2]


end
end Dubon2026.SourceFricke
