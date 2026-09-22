import TaoTrudgianYang2025.BourgainLocalSquare

/-!
# Actual ordered differences enter the mixed local second moment

Two-unit separation makes the first-coordinate projection injective within
each strict difference bin. The proved displaced local square is therefore
summed with its exact ordered multiplicity, without replacing the source
polynomial or dropping either ordinate variable.
-/

open MeasureTheory RiemannZeta.GuthMaynard Set
open scoped Interval Classical

noncomputable section

namespace TaoTrudgianYang2025

theorem bourgain_difference_pairs_fst_injective {W : Finset ℝ}
    (hsep : IsSeparated 2 W) (ℓ : ℤ) :
    Set.InjOn Prod.fst
      (↑((W ×ˢ W).filter fun p => |p.1-p.2-(ℓ : ℝ)| < 1) : Set (ℝ × ℝ)) := by
  intro p hp q hq hpq
  have hp' := Finset.mem_filter.mp hp
  have hq' := Finset.mem_filter.mp hq
  have hpW := Finset.mem_product.mp hp'.1
  have hqW := Finset.mem_product.mp hq'.1
  apply Prod.ext hpq
  by_contra hne
  have hdist : 2 ≤ |p.2-q.2| := by
    simpa only [Real.dist_eq] using hsep p.2 hpW.2 q.2 hqW.2 hne
  have hb₁ := abs_lt.mp hp'.2
  have hb₂ := abs_lt.mp hq'.2
  have hlt : |p.2-q.2| < 2 := abs_lt.mpr (by constructor <;> linarith)
  linarith

/-- Summing a bound valid on every actual pair loses no multiplicity
inside a strict two-separated difference bin. -/
theorem bourgainDifferenceCount_mul_le {W : Finset ℝ}
    (hsep : IsSeparated 2 W) (ℓ : ℤ) (v : ℝ) (f : ℝ → ℝ)
    (hf : ∀ t ∈ W, 0 ≤ f t)
    (hpairs : ∀ t ∈ W, ∀ w ∈ W, |t-w-(ℓ : ℝ)| < 1 → v ≤ f t) :
    (bourgainDifferenceCount W ℓ : ℝ)*v ≤ ∑ t ∈ W, f t := by
  let E := (W ×ˢ W).filter fun p => |p.1-p.2-(ℓ : ℝ)| < 1
  have hinj : Set.InjOn Prod.fst (E : Set (ℝ × ℝ)) :=
    bourgain_difference_pairs_fst_injective hsep ℓ
  have hsub : E.image Prod.fst ⊆ W := by
    intro t ht
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp ht
    exact (Finset.mem_product.mp (Finset.mem_filter.mp hp).1).1
  calc
    _ = ∑ _p ∈ E, v := by simp only [Finset.sum_const, nsmul_eq_mul]; rfl
    _ ≤ ∑ p ∈ E, f p.1 := by
      apply Finset.sum_le_sum
      intro p hp
      obtain ⟨hpW, hbin⟩ := Finset.mem_filter.mp hp
      obtain ⟨ht, hw⟩ := Finset.mem_product.mp hpW
      exact hpairs p.1 ht p.2 hw hbin
    _ = ∑ t ∈ E.image Prod.fst, f t := (Finset.sum_image hinj).symm
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun t ht _ => hf t ht)

/-- An actual source-subset's ordered difference counts are bounded by
its mixed local second moment on every finite integer set. -/
theorem bourgain_mixed_local_difference_counts {η : ℝ} (hη : 0 < η) :
    ∃ C N₀ : ℝ, 0 < C ∧ 2 ≤ N₀ ∧ ∀ P : LargeValuePattern,
      N₀ ≤ P.N → ∀ σ δ : ℝ, 0 ≤ σ → δ ≤ 1 → P.N^(σ-δ) ≤ P.V →
      ∀ W : Finset ℝ, W ⊆ P.ordinates → IsSeparated 2 W →
      ∀ D : Finset ℤ,
        P.V^2*(∑ ℓ ∈ D, (bourgainDifferenceCount W ℓ : ℝ)) ≤
          C*P.N^η*
            (∫ u in -(1+2*Real.pi*P.N^η)..(1+2*Real.pi*P.N^η),
              ∑ t ∈ W, ∑ ℓ ∈ D,
                ‖∑ n ∈ P.indices, P.coeff n*dirichletPhase n (t-(ℓ : ℝ)+u)‖^2) := by
  obtain ⟨C, N₀, hC, hN₀, hm⟩ := bourgain_power_window_displaced_square hη
  refine ⟨C, N₀, hC, hN₀, ?_⟩
  intro P hN σ δ hσ hδ hV W hsub hsep D
  let R := 1+2*Real.pi*P.N^η
  let K := C*P.N^η
  let f := fun (t : ℝ) (ℓ : ℤ) (u : ℝ) =>
    ‖∑ n ∈ P.indices, P.coeff n*dirichletPhase n (t-(ℓ : ℝ)+u)‖^2
  let J := fun (t : ℝ) (ℓ : ℤ) => ∫ u in -R..R, f t ℓ u
  have hNp : 0 < P.N := zero_lt_one.trans P.one_lt_N
  have hR : 0 < R := by dsimp only [R]; positivity
  have hK : 0 < K := mul_pos hC (Real.rpow_pos_of_pos hNp _)
  have hfc (t : ℝ) (ℓ : ℤ) : Continuous (f t ℓ) :=
    (P.polynomial_norm_continuous.comp (by fun_prop)).pow 2
  have hJ (t : ℝ) (ℓ : ℤ) : 0 ≤ J t ℓ :=
    intervalIntegral.integral_nonneg (by linarith) (fun _ _ => sq_nonneg _)
  have hbin (ℓ : ℤ) :
      (bourgainDifferenceCount W ℓ : ℝ)*P.V^2 ≤
        K*∑ t ∈ W, J t ℓ := by
    rw [Finset.mul_sum]
    apply bourgainDifferenceCount_mul_le hsep ℓ (P.V^2) (fun t => K*J t ℓ)
      (fun t _ => mul_nonneg hK.le (hJ t ℓ))
    intro t ht w hw hnear
    apply hm P hN σ δ hσ hδ hV w (hsub hw) (t-(ℓ : ℝ))
    have heq : t-(ℓ : ℝ)-w = t-w-(ℓ : ℝ) := by ring
    rw [heq]
    exact hnear.le
  have hsum : P.V^2*(∑ ℓ ∈ D, (bourgainDifferenceCount W ℓ : ℝ)) ≤
      K*∑ t ∈ W, ∑ ℓ ∈ D, J t ℓ := by
    calc
      _ = ∑ ℓ ∈ D, (bourgainDifferenceCount W ℓ : ℝ)*P.V^2 := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro ℓ hℓ
        ring
      _ ≤ ∑ ℓ ∈ D, K*∑ t ∈ W, J t ℓ := Finset.sum_le_sum (fun ℓ _ => hbin ℓ)
      _ = _ := by rw [← Finset.mul_sum, Finset.sum_comm]
  have hinter :
      (∫ u in -R..R, ∑ t ∈ W, ∑ ℓ ∈ D, f t ℓ u) =
        ∑ t ∈ W, ∑ ℓ ∈ D, J t ℓ := by
    rw [intervalIntegral.integral_finsetSum]
    · apply Finset.sum_congr rfl
      intro t ht
      exact intervalIntegral.integral_finsetSum (fun ℓ _ => (hfc t ℓ).intervalIntegrable _ _)
    · intro t ht
      apply Continuous.intervalIntegrable
      exact continuous_finsetSum _ (fun ℓ _ => hfc t ℓ)
  change P.V^2*(∑ ℓ ∈ D, (bourgainDifferenceCount W ℓ : ℝ)) ≤
    K*(∫ u in -R..R, ∑ t ∈ W, ∑ ℓ ∈ D, f t ℓ u)
  rw [hinter]
  exact hsum

end TaoTrudgianYang2025

