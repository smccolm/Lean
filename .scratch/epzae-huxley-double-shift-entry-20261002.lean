import TaoTrudgianYang2025.ExponentPairShiftUniformity
import TaoTrudgianYang2025.ExponentPairSourceWeyl
import TaoTrudgianYang2025.BetaTaylorPolynomialRemainder
import GuthMaynard.ArithmeticCoefficients
import TaoTrudgianYang2025.HuxleyLinearForms
import TaoTrudgianYang2025.HeathBrownBetaTable
import TaoTrudgianYang2025.SquareProductCount
import TaoTrudgianYang2025.BetaHalfDuality

/-! The actual two-step A-process phase entry. These are source bridges,
not a proof of the short-range Huxley table or of its family estimate. -/

noncomputable section
open Set Expdb TaoTrudgianYang2025
open scoped BigOperators FourierTransform ContDiff
namespace HuxleyDoubleShiftScratch

private theorem twice_shift_uniform_model {σ ε : ℝ}
    (hσ : 0 < σ) (P : ℕ) (hε : 0 < ε) :
    ∃ δ η₀ : ℝ, 0 < δ ∧ 0 < η₀ ∧ η₀ ≤ 1/2 ∧
      ∀ (F : ℝ → ℝ) (η ξ : ℝ),
        IsApproximateModelPhaseFunction F σ (P+2) δ →
        0 < η → η ≤ η₀ → 0 < ξ → ξ ≤ η₀ →
        IsApproximateModelPhaseFunction
          (aProcessShiftPhase (aProcessShiftPhase F σ η) (σ+1) ξ)
          (σ+2) P ε := by
  obtain ⟨δ₂,η₂,hδ₂,hη₂,hη₂half,hmodel₂⟩ :=
    aProcessShiftPhase_uniform_model (by linarith : 0 < σ+1) P hε
  obtain ⟨δ₁,η₁,hδ₁,hη₁,hη₁half,hmodel₁⟩ :=
    aProcessShiftPhase_uniform_model hσ (P+1) hδ₂
  refine ⟨δ₁,min η₁ η₂,hδ₁,lt_min hη₁ hη₂,
    (min_le_left _ _).trans hη₁half,?_⟩
  intro F η ξ hF hη hηcap hξ hξcap
  have hfirst := hmodel₁ F η (by simpa only [Nat.add_assoc] using hF)
    hη (hηcap.trans (min_le_left _ _))
  have hsecond := hmodel₂ (aProcessShiftPhase F σ η) ξ hfirst
    hξ (hξcap.trans (min_le_right _ _))
  simpa only [show σ+1+1=σ+2 by ring] using hsecond

private theorem twice_shift_physical {F : ℝ → ℝ} {σ X M r s m : ℝ}
    (hM : M ≠ 0) (hMr : M-r ≠ 0) (hMrs : M-r-s ≠ 0)
    (hσ : σ ≠ 0) (hσ₁ : σ+1 ≠ 0) (hr : r ≠ 0) (hs : s ≠ 0) :
    ((σ+1)*(σ*X*r/M)*s/(M-r)) *
        aProcessShiftPhase (aProcessShiftPhase F σ (r/M)) (σ+1)
          (s/(M-r)) ((m-r-s)/(M-r-s)) =
      X*(F (m/M)-F ((m+r)/M)-F ((m+s)/M)+F ((m+r+s)/M)) := by
  have hsecond := aProcessShiftPhase_physical
    (F:=aProcessShiftPhase F σ (r/M)) (σ:=σ+1)
    (T:=σ*X*r/M) (N:=M-r) (r:=s) (m:=m-r) hMr hMrs hσ₁ hs
  have hfirst := aProcessShiftPhase_physical
    (F:=F) (σ:=σ) (T:=X) (N:=M) (r:=r) (m:=m) hM hMr hσ hr
  have hfirstShift := aProcessShiftPhase_physical
    (F:=F) (σ:=σ) (T:=X) (N:=M) (r:=r) (m:=m+s) hM hMr hσ hr
  rw [hsecond,mul_sub,hfirst]
  rw [show m-r+s=m+s-r by ring,hfirstShift]
  rw [show m+s+r=m+r+s by ring]
  ring


#print axioms twice_shift_uniform_model
#print axioms twice_shift_physical

private theorem product_fiber_card_le_divisors (S : Finset (ℕ × ℕ))
    {l : ℕ} (hl : 0 < l) :
    (S.filter (fun p => p.1*p.2=l)).card ≤ l.divisors.card := by
  classical
  apply Finset.card_le_card_of_injOn (fun p : ℕ × ℕ => p.1)
  · intro p hp
    have he := (Finset.mem_filter.mp hp).2
    exact Nat.mem_divisors.mpr ⟨⟨p.2,he.symm⟩,hl.ne'⟩
  · intro p hp q hq he
    change p.1=q.1 at he
    have hp' := (Finset.mem_filter.mp hp).2
    have hq' := (Finset.mem_filter.mp hq).2
    have hpp : 0 < p.1 := by
      by_contra h
      have hz : p.1=0 := by omega
      simp [hz] at hp'
      omega
    apply Prod.ext he
    apply Nat.mul_left_cancel hpp
    calc
      p.1*p.2=l := hp'
      _=q.1*q.2 := hq'.symm
      _=p.1*q.2 := by rw [he]

/-- Select an ACTUAL member of each product fiber. No identification of
different phases with the same product is used. The uniform divisor
constant precedes the finite family and its complex values. -/
private theorem product_fiber_actual_maximum {ε : ℝ} (hε : 0 < ε) :
    ∃ D : ℝ, 0 < D ∧
    ∀ (S : Finset (ℕ × ℕ)) (W : (ℕ × ℕ) → ℂ) (L : ℝ),
      (∀ p∈S, 0 < p.1 ∧ 0 < p.2) →
      (∀ p∈S, (p.1*p.2:ℕ) ≤ L) →
      ∃ pick : ℕ → ℕ × ℕ,
        (∀ l∈S.image (fun p => p.1*p.2),
          pick l∈S ∧ (pick l).1*(pick l).2=l ∧
          ∀ p∈S, p.1*p.2=l → ‖W p‖ ≤ ‖W (pick l)‖) ∧
        (∑ p∈S, ‖W p‖) ≤
          D*L^ε*(∑ l∈S.image (fun p => p.1*p.2), ‖W (pick l)‖) := by
  classical
  obtain ⟨D,hD,hdiv⟩ := RiemannZeta.GuthMaynard.divisorCountBound_native ε hε
  refine ⟨D,hD,?_⟩
  intro S W L hpos hcap
  let products := S.image (fun p => p.1*p.2)
  have hex (l : ℕ) : ∃ p : ℕ × ℕ, l∈products →
      p∈S ∧ p.1*p.2=l ∧ ∀ q∈S, q.1*q.2=l → ‖W q‖ ≤ ‖W p‖ := by
    by_cases hl : l∈products
    · obtain ⟨q,hq,heq⟩ := Finset.mem_image.mp hl
      have hn : (S.filter (fun p => p.1*p.2=l)).Nonempty :=
        ⟨q,Finset.mem_filter.mpr ⟨hq,heq⟩⟩
      obtain ⟨p,hp,hmax⟩ := Finset.exists_max_image _ (fun p => ‖W p‖) hn
      refine ⟨p,fun _ => ⟨(Finset.mem_filter.mp hp).1,
        (Finset.mem_filter.mp hp).2,?_⟩⟩
      intro q hq he
      exact hmax q (Finset.mem_filter.mpr ⟨hq,he⟩)
    · exact ⟨(1,1),fun h => (hl h).elim⟩
  choose pick hpick using hex
  refine ⟨pick,hpick,?_⟩
  have hfiber (l : ℕ) (hl : l∈products) :
      (∑ p∈S.filter (fun p => p.1*p.2=l), ‖W p‖) ≤
        D*L^ε*‖W (pick l)‖ := by
    obtain ⟨hp,he,hmax⟩ := hpick l hl
    have hpp := hpos (pick l) hp
    have hlpos : 0 < l := he ▸ Nat.mul_pos hpp.1 hpp.2
    have hlcap : (l:ℝ) ≤ L := by simpa only [he] using hcap (pick l) hp
    have hcard : ((S.filter (fun p => p.1*p.2=l)).card:ℝ) ≤ D*L^ε := by
      calc
        _ ≤ (l.divisors.card:ℝ) := by
          exact_mod_cast product_fiber_card_le_divisors S hlpos
        _ ≤ D*(l:ℝ)^ε := hdiv l hlpos
        _ ≤ D*L^ε := mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow (Nat.cast_nonneg _) hlcap hε.le) hD.le
    calc
      _ ≤ ∑ _p∈S.filter (fun p => p.1*p.2=l), ‖W (pick l)‖ := by
        apply Finset.sum_le_sum
        intro p hp
        exact hmax p (Finset.mem_filter.mp hp).1 (Finset.mem_filter.mp hp).2
      _ = ((S.filter (fun p => p.1*p.2=l)).card:ℝ)*‖W (pick l)‖ := by simp
      _ ≤ _ := mul_le_mul_of_nonneg_right hcard (norm_nonneg _)
  calc
    _ = ∑ l∈products, ∑ p∈S.filter (fun p => p.1*p.2=l), ‖W p‖ := by
      symm
      exact Finset.sum_fiberwise_of_maps_to
        (fun p hp => Finset.mem_image_of_mem (fun p => p.1*p.2) hp) _
    _ ≤ ∑ l∈products, D*L^ε*‖W (pick l)‖ := Finset.sum_le_sum hfiber
    _ = _ := by rw [Finset.mul_sum]

#print axioms product_fiber_card_le_divisors
#print axioms product_fiber_actual_maximum

private theorem source_weyl_length_cap (F : ℝ → ℝ) (T N : ℝ)
    (a L H : ℕ) {M : ℝ} (hH : 0 < H)
    (hL : (L:ℝ)+1 ≤ M) (hHM : (H:ℝ) ≤ M) :
    (H:ℝ)*‖exponentialSumAt F T N a (a+L)‖^2 ≤
      2*M*(M+2*∑ r∈Finset.Icc 1 (H-1), ‖sourceShiftCorrelation F T N a L r‖) := by
  have h := source_exponentialSum_weyl F T N a L H
  have hHp : (0:ℝ) < H := by exact_mod_cast hH
  have hM : 0 ≤ M := hHp.le.trans hHM
  have hC : 0 ≤ ∑ r∈Finset.Icc 1 (H-1), ‖sourceShiftCorrelation F T N a L r‖ :=
    Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  have hbound :
      (H:ℝ)*((H:ℝ)*‖exponentialSumAt F T N a (a+L)‖^2) ≤
        (H:ℝ)*(2*M*(M+2*∑ r∈Finset.Icc 1 (H-1),
          ‖sourceShiftCorrelation F T N a L r‖)) := by
    calc
      _ = (H:ℝ)^2*‖exponentialSumAt F T N a (a+L)‖^2 := by ring
      _ ≤ ((L+1+H:ℕ):ℝ)*((H:ℝ)*(L+1)+
          2*H*∑ r∈Finset.Icc 1 (H-1), ‖sourceShiftCorrelation F T N a L r‖) := h
      _ ≤ (2*M)*((H:ℝ)*M+
          2*H*∑ r∈Finset.Icc 1 (H-1), ‖sourceShiftCorrelation F T N a L r‖) := by
        apply mul_le_mul
        · push_cast
          linarith
        · gcongr
        · positivity
        · positivity
      _ = _ := by ring
  exact le_of_mul_le_mul_left hbound hHp

/-- Two successive Weyl inequalities for the literal source sum.
All correlations below are constructed from the original phase;
none is supplied as an analytic-bound hypothesis. -/
private theorem source_twice_weyl_fourth
    (F : ℝ → ℝ) (σ X M : ℝ) (a L H K : ℕ)
    (hσ : 0 < σ) (hH : 0 < H) (hK : 0 < K)
    (hHa : H ≤ a) (hHL : H ≤ L+1) (hKL : K ≤ L+1) (hHM : (H:ℝ) < M) :
    let D := ∑ r∈Finset.Icc 1 (H-1), ∑ s∈Finset.Icc 1 (K-1),
      ‖sourceShiftCorrelation (aProcessShiftPhase F σ ((r:ℝ)/M))
        (σ*X*r/M) (M-r) (a-r) (L-r) s‖
    (H:ℝ)^2*K*‖exponentialSumAt F X M a (a+L)‖^4 ≤
      8*K*((L:ℝ)+1)^4+64*(H:ℝ)^2*((L:ℝ)+1)^4+
        128*H*((L:ℝ)+1)^3*D := by
  classical
  intro D
  let n : ℝ := L+1
  let C : ℕ → ℝ := fun r => ‖sourceShiftCorrelation F X M a L r‖
  let E : ℕ → ℝ := fun r => ∑ s∈Finset.Icc 1 (K-1),
    ‖sourceShiftCorrelation (aProcessShiftPhase F σ ((r:ℝ)/M))
      (σ*X*r/M) (M-r) (a-r) (L-r) s‖
  let A := ∑ r∈Finset.Icc 1 (H-1), C r
  let B := ∑ r∈Finset.Icc 1 (H-1), (C r)^2
  have hn : 0 ≤ n := by dsimp [n]; positivity
  have hHp : (0:ℝ) < H := by exact_mod_cast hH
  have hKp : (0:ℝ) < K := by exact_mod_cast hK
  have hHLr : (H:ℝ) ≤ n := by dsimp only [n]; exact_mod_cast hHL
  have hKLr : (K:ℝ) ≤ n := by dsimp only [n]; exact_mod_cast hKL
  have hMp : 0 < M := hHp.trans hHM
  have hA : 0 ≤ A := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  have hB : 0 ≤ B := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hD : 0 ≤ D := Finset.sum_nonneg (fun _ _ =>
    Finset.sum_nonneg (fun _ _ => norm_nonneg _))
  have hcard : ((Finset.Icc 1 (H-1)).card:ℝ) ≤ H := by
    exact_mod_cast (show (Finset.Icc 1 (H-1)).card ≤ H by
      calc
        _ ≤ (Finset.range H).card := Finset.card_le_card (by
          intro r hr
          have hr' := Finset.mem_Icc.mp hr
          exact Finset.mem_range.mpr (by omega))
        _ = H := Finset.card_range H)
  have hfirst : (H:ℝ)*‖exponentialSumAt F X M a (a+L)‖^2 ≤ 2*n*(n+2*A) :=
    source_weyl_length_cap F X M a L H hH le_rfl hHLr
  have hsecond (r : ℕ) (hr : r∈Finset.Icc 1 (H-1)) :
      (K:ℝ)*(C r)^2 ≤ 2*n*(n+2*E r) := by
    have hr' := Finset.mem_Icc.mp hr
    have hrpos : 0 < r := by omega
    have hrL : r ≤ L := by omega
    have hra : r ≤ a := by omega
    have hrM : (r:ℝ) < M :=
      (by exact_mod_cast (show r < H by omega) : (r:ℝ) < H).trans hHM
    have heq := norm_sourceShiftCorrelation_compressed_sum
      (F:=F) (σ:=σ) (T:=X) (N:=M)
      hMp.ne' (by linarith : M-(r:ℝ) ≠ 0) hσ.ne' hrpos hra hrL
    dsimp only [C]
    rw [heq]
    exact source_weyl_length_cap _ _ _ _ _ K hK
      (by dsimp [n]; exact_mod_cast (show L-r+1 ≤ L+1 by omega)) hKLr
  have hsum : (K:ℝ)*B ≤ 2*n*((H:ℝ)*n+2*D) := by
    calc
      _ = ∑ r∈Finset.Icc 1 (H-1), (K:ℝ)*(C r)^2 := by rw [Finset.mul_sum]
      _ ≤ ∑ r∈Finset.Icc 1 (H-1), 2*n*(n+2*E r) := Finset.sum_le_sum hsecond
      _ = 2*n*(((Finset.Icc 1 (H-1)).card:ℝ)*n+2*D) := by
        rw [← Finset.mul_sum,Finset.sum_add_distrib]
        simp only [Finset.sum_const,nsmul_eq_mul]
        rw [← Finset.mul_sum]
      _ ≤ _ := by gcongr
  have hcs : A^2 ≤ (H:ℝ)*B := by
    have hh := Finset.sum_mul_sq_le_sq_mul_sq (Finset.Icc 1 (H-1)) C (fun _ => (1:ℝ))
    simp only [mul_one,one_pow,Finset.sum_const,nsmul_eq_mul,mul_one] at hh
    calc
      _ ≤ B*((Finset.Icc 1 (H-1)).card:ℝ) := hh
      _ ≤ B*H := mul_le_mul_of_nonneg_left hcard hB
      _ = _ := mul_comm _ _
  have hKA : (K:ℝ)*A^2 ≤ (H:ℝ)*(2*n*((H:ℝ)*n+2*D)) := by
    calc
      _ ≤ (K:ℝ)*((H:ℝ)*B) := mul_le_mul_of_nonneg_left hcs hKp.le
      _ = (H:ℝ)*((K:ℝ)*B) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hsum hHp.le
  have hfourth : (H:ℝ)^2*‖exponentialSumAt F X M a (a+L)‖^4 ≤
      8*n^4+32*n^2*A^2 := by
    calc
      _ = ((H:ℝ)*‖exponentialSumAt F X M a (a+L)‖^2)^2 := by ring
      _ ≤ (2*n*(n+2*A))^2 := pow_le_pow_left₀ (by positivity) hfirst 2
      _ = 4*n^2*(n+2*A)^2 := by ring
      _ ≤ 4*n^2*(2*n^2+8*A^2) := mul_le_mul_of_nonneg_left
        (by nlinarith only [sq_nonneg (n-2*A)]) (by positivity)
      _ = _ := by ring
  calc
    _ = (K:ℝ)*((H:ℝ)^2*‖exponentialSumAt F X M a (a+L)‖^4) := by ring
    _ ≤ (K:ℝ)*(8*n^4+32*n^2*A^2) :=
      mul_le_mul_of_nonneg_left hfourth hKp.le
    _ = 8*K*n^4+32*n^2*((K:ℝ)*A^2) := by ring
    _ ≤ 8*K*n^4+32*n^2*((H:ℝ)*(2*n*((H:ℝ)*n+2*D))) :=
      add_le_add_right (mul_le_mul_of_nonneg_left hKA (by positivity : 0 ≤ 32*n^2)) _
    _ = _ := by dsimp only [n]; ring

#print axioms source_weyl_length_cap
#print axioms source_twice_weyl_fourth

private theorem twice_shift_actual_sum {F : ℝ → ℝ} {σ X M : ℝ}
    {a L r s : ℕ} (hσ : 0 < σ) (hr : 0 < r) (hs : 0 < s)
    (hra : r+s ≤ a) (hrL : r ≤ L) (hrsM : (r:ℝ)+s < M) :
    ‖sourceShiftCorrelation (aProcessShiftPhase F σ ((r:ℝ)/M))
      (σ*X*r/M) (M-r) (a-r) (L-r) s‖ =
    ‖∑ j∈Finset.range (L+1-r-s),
      (𝐞 (X*(F (((a:ℝ)+j)/M)-F (((a:ℝ)+j+r)/M)-
        F (((a:ℝ)+j+s)/M)+F (((a:ℝ)+j+r+s)/M))) : ℂ)‖ := by
  have hrp : (0:ℝ) < r := by exact_mod_cast hr
  have hsp : (0:ℝ) < s := by exact_mod_cast hs
  have hM : M ≠ 0 := by linarith
  have hMr : M-(r:ℝ) ≠ 0 := by linarith
  have hMrs : M-(r:ℝ)-s ≠ 0 := by linarith
  by_cases hsL : s ≤ L-r
  · rw [norm_sourceShiftCorrelation_compressed_sum
      (σ:=σ+1) hMr hMrs (by linarith : σ+1 ≠ 0) hs (by omega) hsL,
      exponentialSumAt_eq_range]
    rw [show L-r-s+1=L+1-r-s by omega]
    apply congrArg norm
    apply Finset.sum_congr rfl
    intro j _
    apply congrArg (fun t : ℝ => (𝐞 t : ℂ))
    rw [Nat.cast_sub (show s ≤ a-r by omega),
      Nat.cast_sub (show r ≤ a by omega)]
    rw [show (a:ℝ)-r-s+j=(a:ℝ)+j-r-s by ring]
    exact twice_shift_physical hM hMr hMrs hσ.ne' (by linarith)
      hrp.ne' hsp.ne'
  · rw [sourceShiftCorrelation_empty _ _ _ _ _ _ (by omega)]
    simp [show L+1-r-s=0 by omega]

#print axioms twice_shift_actual_sum

/-- The actual double difference is product times the common second jet,
with an explicit shift-size error. This is the perturbation required
before using product-indexed family geometry. -/
private theorem double_difference_common_jet
    {F : ℝ → ℝ} {x r s B : ℝ} (hr : 0 ≤ r) (hs : 0 ≤ s) (hB : 0 ≤ B)
    (hreg : ∀ y∈Set.Icc x (x+r+s), ContDiffAt ℝ ∞ F y)
    (hthird : ∀ y∈Set.Icc x (x+r+s), |iteratedDeriv 3 F y| ≤ B) :
    |F x-F (x+r)-F (x+s)+F (x+r+s)-r*s*iteratedDeriv 2 F x| ≤
      B*r*s*(r+s) := by
  have hx : x∈Set.Icc x (x+r+s) := ⟨le_rfl,by linarith⟩
  have hd (j : ℕ) (y : ℝ) (hy : y∈Set.Icc x (x+r+s)) :
      HasDerivAt (iteratedDeriv j F) (iteratedDeriv (j+1) F y) y := by
    simpa only [iteratedDeriv_succ] using
      ((contDiffAt_iteratedDeriv_infty (hreg y hy) j).differentiableAt (by simp)).hasDerivAt
  have hjet (y : ℝ) (hy : y∈Set.Icc x (x+r+s)) :
      |iteratedDeriv 2 F y-iteratedDeriv 2 F x| ≤ B*(r+s) := by
    have hh := Convex.norm_image_sub_le_of_norm_deriv_le
      (fun z hz => (hd 2 z hz).differentiableAt)
      (fun z hz => by
        rw [(hd 2 z hz).deriv,Real.norm_eq_abs]
        exact hthird z hz)
      (convex_Icc x (x+r+s)) hx hy
    rw [Real.norm_eq_abs,Real.norm_eq_abs,
      abs_of_nonneg (show 0 ≤ y-x by linarith [hy.1])] at hh
    exact hh.trans (mul_le_mul_of_nonneg_left (by linarith [hy.2]) hB)
  let G : ℝ → ℝ := fun z => deriv F z-z*iteratedDeriv 2 F x
  have hdG (z : ℝ) (hz : z∈Set.Icc x (x+r+s)) :
      HasDerivAt G (iteratedDeriv 2 F z-iteratedDeriv 2 F x) z := by
    have hh := (hd 1 z hz).sub ((hasDerivAt_id z).mul_const (iteratedDeriv 2 F x))
    simpa only [iteratedDeriv_one,Nat.reduceAdd,one_mul] using hh
  have hsegment (y : ℝ) (hy : y∈Set.Icc x (x+r)) :
      |deriv F (y+s)-deriv F y-s*iteratedDeriv 2 F x| ≤ B*(r+s)*s := by
    have hsub (z : ℝ) (hz : z∈Set.Icc y (y+s)) : z∈Set.Icc x (x+r+s) :=
      ⟨hy.1.trans hz.1,by linarith [hy.2,hz.2]⟩
    have hh := Convex.norm_image_sub_le_of_norm_deriv_le
      (fun z hz => (hdG z (hsub z hz)).differentiableAt)
      (fun z hz => by
        rw [(hdG z (hsub z hz)).deriv,Real.norm_eq_abs]
        exact hjet z (hsub z hz))
      (convex_Icc y (y+s))
      (show y∈Set.Icc y (y+s) from ⟨le_rfl,by linarith⟩)
      (show y+s∈Set.Icc y (y+s) from ⟨by linarith,le_rfl⟩)
    rw [Real.norm_eq_abs,Real.norm_eq_abs,
      show y+s-y=s by ring,abs_of_nonneg hs] at hh
    convert hh using 1
    dsimp only [G]
    congr 1
    ring
  let E : ℝ → ℝ := fun y => F (y+s)-F y-y*s*iteratedDeriv 2 F x
  have hdE (y : ℝ) (hy : y∈Set.Icc x (x+r)) :
      HasDerivAt E (deriv F (y+s)-deriv F y-s*iteratedDeriv 2 F x) y := by
    have hy₀ : y∈Set.Icc x (x+r+s) := ⟨hy.1,by linarith [hy.2]⟩
    have hy₁ : y+s∈Set.Icc x (x+r+s) :=
      ⟨by linarith [hy.1],by linarith [hy.2]⟩
    have hleft := ((hreg (y+s) hy₁).differentiableAt (by simp)).hasDerivAt.comp y
      ((hasDerivAt_id y).add_const s)
    have hright := ((hreg y hy₀).differentiableAt (by simp)).hasDerivAt
    have hlin := (((hasDerivAt_id y).mul_const s).mul_const (iteratedDeriv 2 F x))
    simpa only [mul_one,one_mul] using (hleft.sub hright).sub hlin
  have hh := Convex.norm_image_sub_le_of_norm_deriv_le
    (fun y hy => (hdE y hy).differentiableAt)
    (fun y hy => by rw [(hdE y hy).deriv,Real.norm_eq_abs]; exact hsegment y hy)
    (convex_Icc x (x+r))
    (show x∈Set.Icc x (x+r) from ⟨le_rfl,by linarith⟩)
    (show x+r∈Set.Icc x (x+r) from ⟨by linarith,le_rfl⟩)
  rw [Real.norm_eq_abs,Real.norm_eq_abs,show x+r-x=r by ring,abs_of_nonneg hr] at hh
  convert hh using 1
  · dsimp only [E]
    congr 1
    ring
  · ring

#print axioms double_difference_common_jet

/-- Exact rational scale feasibility for the combined-parameter row-3
route. This is only the scale calculation, not the source-family bound. -/
private theorem short_row_three_combined_scales {α : ℝ}
    (hlo : (890:ℝ)/3277 ≤ α) (hhi : α ≤ (199:ℝ)/716) :
    let t := (α-(890:ℝ)/3277)/((199:ℝ)/716-(890:ℝ)/3277)
    let ν := (1-t)*(121373:ℝ)/1000000+t*(130455:ℝ)/1000000
    let h := (1-t)*(27201:ℝ)/1000000+t*(29341:ℝ)/1000000
    let β := (89+2243*α)/2706
    0 < h ∧ 0 < ν ∧
    5*α+1/10000 ≤ 1+3*ν ∧
    1+3*h+2*ν+1/10000 ≤ 5*α ∧
    2*ν+1/10000 ≤ α ∧
    3+9*h+11*ν+1/10000 ≤ 17*α ∧
    7+21*h+27*ν+1/10000 ≤ 41*α ∧
    8*h+1/10000 ≤ α ∧
    288*α-144*h+1/10000 ≤ 288*β ∧
    288*α-36*ν+1/10000 ≤ 288*β ∧
    648*α-72-216*h-216*ν+1/10000 ≤ 288*β ∧
    24+72*h+96*α+144*ν+1/10000 ≤ 288*β ∧
    21+45*h+177*α+33*ν+1/10000 ≤ 288*β ∧
    15+45*h+201*α+15*ν+1/10000 ≤ 288*β ∧
    19+57*h+182*α+9*ν+1/10000 ≤ 288*β ∧
    7+21*h+230*α+9*ν+1/10000 ≤ 288*β ∧
    4+12*h+260*α-24*ν+1/10000 ≤ 288*β := by
  dsimp only
  constructor
  · norm_num
    linarith
  constructor
  · norm_num
    linarith
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩ <;>
    norm_num <;> linarith

#print axioms short_row_three_combined_scales

/-- Actual product-indexed two-step Weyl reduction, with the divisor
multiplicity absorbed into a uniform epsilon loss. The selected phase
remains the literal double difference from a selected shift pair. -/
private theorem source_product_twice_weyl {ε : ℝ} (hε : 0 < ε) :
    ∃ D : ℝ, 0 < D ∧
    ∀ (F : ℝ → ℝ) (σ X M : ℝ) (a L H K : ℕ),
      0 < σ → 0 < H → 0 < K → H+K ≤ a →
      H ≤ L+1 → K ≤ L+1 → (H:ℝ)+K < M →
      let S := (Finset.Icc 1 (H-1)) ×ˢ (Finset.Icc 1 (K-1))
      let W := fun p : ℕ × ℕ => ∑ j∈Finset.range (L+1-p.1-p.2),
        (𝐞 (X*(F (((a:ℝ)+j)/M)-F (((a:ℝ)+j+p.1)/M)-
          F (((a:ℝ)+j+p.2)/M)+F (((a:ℝ)+j+p.1+p.2)/M))) : ℂ)
      ∃ pick : ℕ → ℕ × ℕ,
        (∀ l∈S.image (fun p => p.1*p.2),
          pick l∈S ∧ (pick l).1*(pick l).2=l ∧
          ∀ p∈S, p.1*p.2=l → ‖W p‖ ≤ ‖W (pick l)‖) ∧
        (H:ℝ)^2*K*‖exponentialSumAt F X M a (a+L)‖^4 ≤
          8*K*((L:ℝ)+1)^4+64*(H:ℝ)^2*((L:ℝ)+1)^4+
            128*H*((L:ℝ)+1)^3*
              (D*((H:ℝ)*K)^ε*
                (∑ l∈S.image (fun p => p.1*p.2), ‖W (pick l)‖)) := by
  classical
  obtain ⟨D,hD,hselect⟩ := product_fiber_actual_maximum hε
  refine ⟨D,hD,?_⟩
  intro F σ X M a L H K hσ hH hK hHa hHL hKL hM S W
  have hbound (p : ℕ × ℕ) (hp : p∈S) : 0 < p.1 ∧ p.1 < H ∧ 0 < p.2 ∧ p.2 < K := by
    obtain ⟨hr,hs⟩ := Finset.mem_product.mp hp
    obtain ⟨hr₁,hr₂⟩ := Finset.mem_Icc.mp hr
    obtain ⟨hs₁,hs₂⟩ := Finset.mem_Icc.mp hs
    omega
  obtain ⟨pick,hpick,hgroup⟩ := hselect S W ((H:ℝ)*K)
    (fun p hp => ⟨(hbound p hp).1,(hbound p hp).2.2.1⟩)
    (by
      intro p hp
      have hh := hbound p hp
      exact_mod_cast Nat.mul_le_mul hh.2.1.le hh.2.2.2.le)
  refine ⟨pick,hpick,?_⟩
  have hHp : (0:ℝ) < H := by exact_mod_cast hH
  have hKp : (0:ℝ) < K := by exact_mod_cast hK
  have hweyl := source_twice_weyl_fourth F σ X M a L H K
    hσ hH hK (by omega) hHL hKL (by linarith)
  dsimp only at hweyl
  have heq : (∑ r∈Finset.Icc 1 (H-1), ∑ s∈Finset.Icc 1 (K-1),
      ‖sourceShiftCorrelation (aProcessShiftPhase F σ ((r:ℝ)/M))
        (σ*X*r/M) (M-r) (a-r) (L-r) s‖) = ∑ p∈S, ‖W p‖ := by
    rw [Finset.sum_product]
    apply Finset.sum_congr rfl
    intro r hr
    apply Finset.sum_congr rfl
    intro s hs
    have hh := hbound (r,s) (Finset.mem_product.mpr ⟨hr,hs⟩)
    have hrH : (r:ℝ) < H := by exact_mod_cast hh.2.1
    have hsK : (s:ℝ) < K := by exact_mod_cast hh.2.2.2
    exact twice_shift_actual_sum hσ hh.1 hh.2.2.1
      (by omega) (by omega) (by linarith)
  rw [heq] at hweyl
  exact hweyl.trans (add_le_add le_rfl
    (mul_le_mul_of_nonneg_left hgroup (by positivity)))

#print axioms source_product_twice_weyl

private theorem double_difference_iterated_jet
    {F : ℝ → ℝ} {x r s : ℝ} (hr : 0 ≤ r) (hs : 0 ≤ s)
    (hreg : ∀ y∈Set.Icc x (x+r+s), ContDiffAt ℝ ∞ F y) (j : ℕ) :
    iteratedDeriv j (fun u => F u-F (u+r)-F (u+s)+F (u+r+s)) x =
      iteratedDeriv j F x-iteratedDeriv j F (x+r)-
        iteratedDeriv j F (x+s)+iteratedDeriv j F (x+r+s) := by
  have h0 : ContDiffAt ℝ j F x :=
    (hreg x ⟨le_rfl,by linarith⟩).of_le
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl j)
  have h1 : ContDiffAt ℝ j (fun u => F (u+r)) x :=
    ((hreg (x+r) ⟨by linarith,by linarith⟩).of_le
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl j)).comp x
        (contDiffAt_id.add contDiffAt_const)
  have h2 : ContDiffAt ℝ j (fun u => F (u+s)) x :=
    ((hreg (x+s) ⟨by linarith,by linarith⟩).of_le
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl j)).comp x
        (contDiffAt_id.add contDiffAt_const)
  have h3 : ContDiffAt ℝ j (fun u => F (u+r+s)) x :=
    ((hreg (x+r+s) ⟨by linarith,le_rfl⟩).of_le
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl j)).comp x
        ((contDiffAt_id.add contDiffAt_const).add contDiffAt_const)
  rw [iteratedDeriv_fun_add ((h0.sub h1).sub h2) h3,
    iteratedDeriv_fun_sub (h0.sub h1) h2,iteratedDeriv_fun_sub h0 h1]
  simp only [add_assoc,iteratedDeriv_comp_add_const]

private theorem double_difference_all_common_jets
    {F : ℝ → ℝ} {x r s B : ℝ} (hr : 0 ≤ r) (hs : 0 ≤ s) (hB : 0 ≤ B)
    (hreg : ∀ y∈Set.Icc x (x+r+s), ContDiffAt ℝ ∞ F y)
    (j : ℕ) (hjet : ∀ y∈Set.Icc x (x+r+s), |iteratedDeriv (j+3) F y| ≤ B) :
    |iteratedDeriv j (fun u => F u-F (u+r)-F (u+s)+F (u+r+s)) x-
      r*s*iteratedDeriv (j+2) F x| ≤ B*r*s*(r+s) := by
  rw [double_difference_iterated_jet hr hs hreg j]
  have hh := double_difference_common_jet (F:=iteratedDeriv j F) hr hs hB
    (fun y hy => contDiffAt_iteratedDeriv_infty (hreg y hy) j)
    (by
      intro y hy
      simpa only [iteratedDeriv_real_comp_order, Nat.add_comm] using hjet y hy)
  simpa only [iteratedDeriv_real_comp_order, Nat.add_comm] using hh

#print axioms double_difference_iterated_jet
#print axioms double_difference_all_common_jets

example {σ ε : ℝ}
    (hσ : 0 < σ) (P : ℕ) (hε : 0 < ε) :
    ∃ δ η₀ : ℝ, 0 < δ ∧ 0 < η₀ ∧ η₀ ≤ 1/2 ∧
      ∀ (F : ℝ → ℝ) (η ξ : ℝ),
        IsApproximateModelPhaseFunction F σ (P+2) δ →
        0 < η → η ≤ η₀ → 0 < ξ → ξ ≤ η₀ →
        IsApproximateModelPhaseFunction
          (aProcessShiftPhase (aProcessShiftPhase F σ η) (σ+1) ξ)
          (σ+2) P ε :=
  @HuxleyDoubleShiftScratch.twice_shift_uniform_model σ ε hσ P hε

example {F : ℝ → ℝ} {σ X M r s m : ℝ}
    (hM : M ≠ 0) (hMr : M-r ≠ 0) (hMrs : M-r-s ≠ 0)
    (hσ : σ ≠ 0) (hσ₁ : σ+1 ≠ 0) (hr : r ≠ 0) (hs : s ≠ 0) :
    ((σ+1)*(σ*X*r/M)*s/(M-r)) *
        aProcessShiftPhase (aProcessShiftPhase F σ (r/M)) (σ+1)
          (s/(M-r)) ((m-r-s)/(M-r-s)) =
      X*(F (m/M)-F ((m+r)/M)-F ((m+s)/M)+F ((m+r+s)/M)) :=
  @HuxleyDoubleShiftScratch.twice_shift_physical F σ X M r s m hM hMr hMrs hσ hσ₁ hr hs

example (S : Finset (ℕ × ℕ))
    {l : ℕ} (hl : 0 < l) :
    (S.filter (fun p => p.1*p.2=l)).card ≤ l.divisors.card :=
  @HuxleyDoubleShiftScratch.product_fiber_card_le_divisors S l hl

example {ε : ℝ} (hε : 0 < ε) :
    ∃ D : ℝ, 0 < D ∧
    ∀ (S : Finset (ℕ × ℕ)) (W : (ℕ × ℕ) → ℂ) (L : ℝ),
      (∀ p∈S, 0 < p.1 ∧ 0 < p.2) →
      (∀ p∈S, (p.1*p.2:ℕ) ≤ L) →
      ∃ pick : ℕ → ℕ × ℕ,
        (∀ l∈S.image (fun p => p.1*p.2),
          pick l∈S ∧ (pick l).1*(pick l).2=l ∧
          ∀ p∈S, p.1*p.2=l → ‖W p‖ ≤ ‖W (pick l)‖) ∧
        (∑ p∈S, ‖W p‖) ≤
          D*L^ε*(∑ l∈S.image (fun p => p.1*p.2), ‖W (pick l)‖) :=
  @HuxleyDoubleShiftScratch.product_fiber_actual_maximum ε hε

example (F : ℝ → ℝ) (T N : ℝ)
    (a L H : ℕ) {M : ℝ} (hH : 0 < H)
    (hL : (L:ℝ)+1 ≤ M) (hHM : (H:ℝ) ≤ M) :
    (H:ℝ)*‖exponentialSumAt F T N a (a+L)‖^2 ≤
      2*M*(M+2*∑ r∈Finset.Icc 1 (H-1), ‖sourceShiftCorrelation F T N a L r‖) :=
  @HuxleyDoubleShiftScratch.source_weyl_length_cap F T N a L H M hH hL hHM

example
    (F : ℝ → ℝ) (σ X M : ℝ) (a L H K : ℕ)
    (hσ : 0 < σ) (hH : 0 < H) (hK : 0 < K)
    (hHa : H ≤ a) (hHL : H ≤ L+1) (hKL : K ≤ L+1) (hHM : (H:ℝ) < M) :
    let D := ∑ r∈Finset.Icc 1 (H-1), ∑ s∈Finset.Icc 1 (K-1),
      ‖sourceShiftCorrelation (aProcessShiftPhase F σ ((r:ℝ)/M))
        (σ*X*r/M) (M-r) (a-r) (L-r) s‖
    (H:ℝ)^2*K*‖exponentialSumAt F X M a (a+L)‖^4 ≤
      8*K*((L:ℝ)+1)^4+64*(H:ℝ)^2*((L:ℝ)+1)^4+
        128*H*((L:ℝ)+1)^3*D :=
  @HuxleyDoubleShiftScratch.source_twice_weyl_fourth F σ X M a L H K hσ hH hK hHa hHL hKL hHM

example {F : ℝ → ℝ} {σ X M : ℝ}
    {a L r s : ℕ} (hσ : 0 < σ) (hr : 0 < r) (hs : 0 < s)
    (hra : r+s ≤ a) (hrL : r ≤ L) (hrsM : (r:ℝ)+s < M) :
    ‖sourceShiftCorrelation (aProcessShiftPhase F σ ((r:ℝ)/M))
      (σ*X*r/M) (M-r) (a-r) (L-r) s‖ =
    ‖∑ j∈Finset.range (L+1-r-s),
      (𝐞 (X*(F (((a:ℝ)+j)/M)-F (((a:ℝ)+j+r)/M)-
        F (((a:ℝ)+j+s)/M)+F (((a:ℝ)+j+r+s)/M))) : ℂ)‖ :=
  @HuxleyDoubleShiftScratch.twice_shift_actual_sum F σ X M a L r s hσ hr hs hra hrL hrsM

example
    {F : ℝ → ℝ} {x r s B : ℝ} (hr : 0 ≤ r) (hs : 0 ≤ s) (hB : 0 ≤ B)
    (hreg : ∀ y∈Set.Icc x (x+r+s), ContDiffAt ℝ ∞ F y)
    (hthird : ∀ y∈Set.Icc x (x+r+s), |iteratedDeriv 3 F y| ≤ B) :
    |F x-F (x+r)-F (x+s)+F (x+r+s)-r*s*iteratedDeriv 2 F x| ≤
      B*r*s*(r+s) :=
  @HuxleyDoubleShiftScratch.double_difference_common_jet F x r s B hr hs hB hreg hthird

example {α : ℝ}
    (hlo : (890:ℝ)/3277 ≤ α) (hhi : α ≤ (199:ℝ)/716) :
    let t := (α-(890:ℝ)/3277)/((199:ℝ)/716-(890:ℝ)/3277)
    let ν := (1-t)*(121373:ℝ)/1000000+t*(130455:ℝ)/1000000
    let h := (1-t)*(27201:ℝ)/1000000+t*(29341:ℝ)/1000000
    let β := (89+2243*α)/2706
    0 < h ∧ 0 < ν ∧
    5*α+1/10000 ≤ 1+3*ν ∧
    1+3*h+2*ν+1/10000 ≤ 5*α ∧
    2*ν+1/10000 ≤ α ∧
    3+9*h+11*ν+1/10000 ≤ 17*α ∧
    7+21*h+27*ν+1/10000 ≤ 41*α ∧
    8*h+1/10000 ≤ α ∧
    288*α-144*h+1/10000 ≤ 288*β ∧
    288*α-36*ν+1/10000 ≤ 288*β ∧
    648*α-72-216*h-216*ν+1/10000 ≤ 288*β ∧
    24+72*h+96*α+144*ν+1/10000 ≤ 288*β ∧
    21+45*h+177*α+33*ν+1/10000 ≤ 288*β ∧
    15+45*h+201*α+15*ν+1/10000 ≤ 288*β ∧
    19+57*h+182*α+9*ν+1/10000 ≤ 288*β ∧
    7+21*h+230*α+9*ν+1/10000 ≤ 288*β ∧
    4+12*h+260*α-24*ν+1/10000 ≤ 288*β :=
  @HuxleyDoubleShiftScratch.short_row_three_combined_scales α hlo hhi

example {ε : ℝ} (hε : 0 < ε) :
    ∃ D : ℝ, 0 < D ∧
    ∀ (F : ℝ → ℝ) (σ X M : ℝ) (a L H K : ℕ),
      0 < σ → 0 < H → 0 < K → H+K ≤ a →
      H ≤ L+1 → K ≤ L+1 → (H:ℝ)+K < M →
      let S := (Finset.Icc 1 (H-1)) ×ˢ (Finset.Icc 1 (K-1))
      let W := fun p : ℕ × ℕ => ∑ j∈Finset.range (L+1-p.1-p.2),
        (𝐞 (X*(F (((a:ℝ)+j)/M)-F (((a:ℝ)+j+p.1)/M)-
          F (((a:ℝ)+j+p.2)/M)+F (((a:ℝ)+j+p.1+p.2)/M))) : ℂ)
      ∃ pick : ℕ → ℕ × ℕ,
        (∀ l∈S.image (fun p => p.1*p.2),
          pick l∈S ∧ (pick l).1*(pick l).2=l ∧
          ∀ p∈S, p.1*p.2=l → ‖W p‖ ≤ ‖W (pick l)‖) ∧
        (H:ℝ)^2*K*‖exponentialSumAt F X M a (a+L)‖^4 ≤
          8*K*((L:ℝ)+1)^4+64*(H:ℝ)^2*((L:ℝ)+1)^4+
            128*H*((L:ℝ)+1)^3*
              (D*((H:ℝ)*K)^ε*
                (∑ l∈S.image (fun p => p.1*p.2), ‖W (pick l)‖)) :=
  @HuxleyDoubleShiftScratch.source_product_twice_weyl ε hε

example
    {F : ℝ → ℝ} {x r s : ℝ} (hr : 0 ≤ r) (hs : 0 ≤ s)
    (hreg : ∀ y∈Set.Icc x (x+r+s), ContDiffAt ℝ ∞ F y) (j : ℕ) :
    iteratedDeriv j (fun u => F u-F (u+r)-F (u+s)+F (u+r+s)) x =
      iteratedDeriv j F x-iteratedDeriv j F (x+r)-
        iteratedDeriv j F (x+s)+iteratedDeriv j F (x+r+s) :=
  @HuxleyDoubleShiftScratch.double_difference_iterated_jet F x r s hr hs hreg j

example
    {F : ℝ → ℝ} {x r s B : ℝ} (hr : 0 ≤ r) (hs : 0 ≤ s) (hB : 0 ≤ B)
    (hreg : ∀ y∈Set.Icc x (x+r+s), ContDiffAt ℝ ∞ F y)
    (j : ℕ) (hjet : ∀ y∈Set.Icc x (x+r+s), |iteratedDeriv (j+3) F y| ≤ B) :
    |iteratedDeriv j (fun u => F u-F (u+r)-F (u+s)+F (u+r+s)) x-
      r*s*iteratedDeriv (j+2) F x| ≤ B*r*s*(r+s) :=
  @HuxleyDoubleShiftScratch.double_difference_all_common_jets F x r s B hr hs hB hreg j hjet

/-- Move an approximate curvature level to a genuine nearby root. The
derivative lower bound gives both endpoint coverage and the displacement;
neither a root nor its distance is supplied. -/
private theorem reference_curvature_root_transfer
    (f f' : ℝ → ℝ) {a b x c ε q : ℝ}
    (hc : 0 < c) (hε : 0 ≤ ε) (hx : x∈Ioo a b)
    (hsmall : ε < c*min (x-a) (b-x))
    (hd : ∀ t∈Icc a b, HasDerivAt f (f' t) t)
    (hlower : ∀ t∈Icc a b, c ≤ f' t)
    (herror : |f x-q| ≤ ε) :
    ∃ v∈Ioo a b, f v=q ∧ |v-x| ≤ ε/c := by
  let d := ε/c
  have hd0 : 0 ≤ d := div_nonneg hε hc.le
  have hcd : c*d=ε := by dsimp only [d]; field_simp
  have hleft : a < x-d := by
    have hh : d < x-a := (div_lt_iff₀ hc).mpr (by
      simpa only [mul_comm] using
        hsmall.trans_le (mul_le_mul_of_nonneg_left (min_le_left _ _) hc.le))
    linarith
  have hright : x+d < b := by
    have hh : d < b-x := (div_lt_iff₀ hc).mpr (by
      simpa only [mul_comm] using
        hsmall.trans_le (mul_le_mul_of_nonneg_left (min_le_right _ _) hc.le))
    linarith
  have hsub : Icc (x-d) (x+d) ⊆ Icc a b :=
    fun _ ht => ⟨hleft.le.trans ht.1,ht.2.trans hright.le⟩
  have hg (u v : ℝ) (hu : u∈Icc a b) (hv : v∈Icc a b) (huv : u ≤ v) :
      c*(v-u) ≤ f v-f u := by
    rcases huv.eq_or_lt with he | he
    · subst v
      simp
    have hsub' : Icc u v ⊆ Icc a b :=
      fun _ ht => ⟨hu.1.trans ht.1,ht.2.trans hv.2⟩
    obtain ⟨t,ht,heq⟩ := exists_hasDerivAt_eq_slope f f' he
      (fun z hz => (hd z (hsub' hz)).continuousAt.continuousWithinAt)
      (fun z hz => hd z (hsub' ⟨hz.1.le,hz.2.le⟩))
    have hh := hlower t (hsub' ⟨ht.1.le,ht.2.le⟩)
    rw [heq] at hh
    exact (le_div_iff₀ (sub_pos.mpr he)).mp hh
  have hxl : x-d∈Icc a b := ⟨hleft.le,by linarith [hx.2]⟩
  have hxu : x+d∈Icc a b := ⟨by linarith [hx.1],hright.le⟩
  have hlow := hg (x-d) x hxl ⟨hx.1.le,hx.2.le⟩ (by linarith)
  have hupp := hg x (x+d) ⟨hx.1.le,hx.2.le⟩ hxu (by linarith)
  have hcont : ContinuousOn f (Icc (x-d) (x+d)) :=
    fun z hz => (hd z (hsub hz)).continuousAt.continuousWithinAt
  obtain ⟨v,hv,hvroot⟩ := intermediate_value_Icc (by linarith : x-d ≤ x+d)
    hcont (show q∈Icc (f (x-d)) (f (x+d)) from
      ⟨by nlinarith only [hlow,hcd,(abs_le.mp herror).2],
       by nlinarith only [hupp,hcd,(abs_le.mp herror).1]⟩)
  refine ⟨v,⟨hleft.trans_le hv.1,hv.2.trans_lt hright⟩,hvroot,?_⟩
  exact abs_le.mpr ⟨by linarith [hv.1],by linarith [hv.2]⟩

/-- The same constructed curvature root also transports the cubic profile
with an explicitly derived error; no profile coincidence at the new root
is assumed. -/
private theorem reference_curvature_profile_transfer
    (f f' g g' : ℝ → ℝ) {a b x c ε q B E u : ℝ}
    (hc : 0 < c) (hε : 0 ≤ ε) (hB : 0 ≤ B) (hx : x∈Ioo a b)
    (hsmall : ε < c*min (x-a) (b-x))
    (hd : ∀ t∈Icc a b, HasDerivAt f (f' t) t)
    (hlower : ∀ t∈Icc a b, c ≤ f' t)
    (herror : |f x-q| ≤ ε)
    (hgd : ∀ t∈Icc a b, HasDerivAt g (g' t) t)
    (hgupper : ∀ t∈Icc a b, |g' t| ≤ B)
    (hgerror : |g x-u| ≤ E) :
    ∃ v∈Ioo a b, f v=q ∧ |v-x| ≤ ε/c ∧ |g v-u| ≤ E+B*(ε/c) := by
  obtain ⟨v,hv,hroot,hdist⟩ :=
    reference_curvature_root_transfer f f' hc hε hx hsmall hd hlower herror
  refine ⟨v,hv,hroot,hdist,?_⟩
  have hprofile := Convex.norm_image_sub_le_of_norm_deriv_le
    (fun z hz => (hgd z hz).differentiableAt)
    (fun z hz => by rw [(hgd z hz).deriv,Real.norm_eq_abs]; exact hgupper z hz)
    (convex_Icc a b) (show x∈Icc a b from ⟨hx.1.le,hx.2.le⟩)
    (show v∈Icc a b from ⟨hv.1.le,hv.2.le⟩)
  simp only [Real.norm_eq_abs] at hprofile
  calc
    _ = |(g v-g x)+(g x-u)| := by congr 1; ring
    _ ≤ |g v-g x|+|g x-u| := abs_add_le _ _
    _ ≤ B*(ε/c)+E := add_le_add
      (hprofile.trans (mul_le_mul_of_nonneg_left hdist hB)) hgerror
    _ = _ := add_comm _ _

#print axioms reference_curvature_root_transfer
#print axioms reference_curvature_profile_transfer

example
    (f f' : ℝ → ℝ) {a b x c ε q : ℝ}
    (hc : 0 < c) (hε : 0 ≤ ε) (hx : x∈Ioo a b)
    (hsmall : ε < c*min (x-a) (b-x))
    (hd : ∀ t∈Icc a b, HasDerivAt f (f' t) t)
    (hlower : ∀ t∈Icc a b, c ≤ f' t)
    (herror : |f x-q| ≤ ε) :
    ∃ v∈Ioo a b, f v=q ∧ |v-x| ≤ ε/c :=
  @HuxleyDoubleShiftScratch.reference_curvature_root_transfer f f' a b x c ε q hc hε hx hsmall hd hlower herror

example
    (f f' g g' : ℝ → ℝ) {a b x c ε q B E u : ℝ}
    (hc : 0 < c) (hε : 0 ≤ ε) (hB : 0 ≤ B) (hx : x∈Ioo a b)
    (hsmall : ε < c*min (x-a) (b-x))
    (hd : ∀ t∈Icc a b, HasDerivAt f (f' t) t)
    (hlower : ∀ t∈Icc a b, c ≤ f' t)
    (herror : |f x-q| ≤ ε)
    (hgd : ∀ t∈Icc a b, HasDerivAt g (g' t) t)
    (hgupper : ∀ t∈Icc a b, |g' t| ≤ B)
    (hgerror : |g x-u| ≤ E) :
    ∃ v∈Ioo a b, f v=q ∧ |v-x| ≤ ε/c ∧ |g v-u| ≤ E+B*(ε/c) :=
  @HuxleyDoubleShiftScratch.reference_curvature_profile_transfer f f' g g' a b x c ε q B E u hc hε hB hx hsmall hd hlower herror hgd hgupper hgerror

/-- The direct product-parameter reference surface has the literal
curvature columns and a lower mixed-ratio derivative coming from the
ordinary two-jet determinant. No inverse-profile estimate is assumed. -/
private theorem linear_reference_curvature_data
    (f : ℝ → ℝ) {x y c U : ℝ}
    (hx : 0 < x) (hy : y∈Icc (1/2:ℝ) 3)
    (hc : 0 < c)
    (hf : ∀ u, 0 < u → ContDiffAt ℝ ∞ f u)
    (hlower : c ≤ deriv f x) (hupper : |deriv f x| ≤ U)
    (hdet : c ≤ |(deriv f x)^2-f x*iteratedDeriv 2 f x|) :
    let H := fun p : ℝ × ℝ => p.1*f p.2
    ContDiffAt ℝ 2 H (y,x) ∧
    fderiv ℝ H (y,x) (0,1)=y*deriv f x ∧
    fderiv ℝ H (y,x) (1,0)=f x ∧
    c/2 ≤ |fderiv ℝ H (y,x) (0,1)| ∧
    c/(3*U^2) ≤
      |deriv (fun u => fderiv ℝ H (y,u) (1,0)/
        fderiv ℝ H (y,u) (0,1)) x| := by
  intro H
  have hypos : 0 < y := by linarith only [hy.1]
  have hdpos : 0 < deriv f x := hc.trans_le hlower
  have hcol (u : ℝ) (hu : 0 < u) :
      fderiv ℝ H (y,u) (0,1)=y*deriv f u ∧
      fderiv ℝ H (y,u) (1,0)=f u := by
    have hd := ((hf u hu).differentiableAt (by simp)).hasDerivAt
    have hh := (hasFDerivAt_fst (𝕜:=ℝ) (p:=(y,u))).mul
      (hd.comp_hasFDerivAt (f:=fun p : ℝ × ℝ => p.2) (y,u) hasFDerivAt_snd)
    have he := hh.fderiv
    change fderiv ℝ H (y,u)=_ at he
    constructor
    · rw [he]
      change y*(deriv f u*1)+f u*0=_
      ring
    · rw [he]
      change y*(deriv f u*0)+f u*1=_
      ring
  refine ⟨(contDiffAt_fst.mul ((hf x hx).comp (y,x) contDiffAt_snd)).of_le
    (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2),
    (hcol x hx).1,(hcol x hx).2,?_,?_⟩
  · rw [(hcol x hx).1,abs_of_pos (mul_pos hypos hdpos)]
    nlinarith only [mul_le_mul hy.1 hlower hc.le hypos.le]
  · have hd := ((hf x hx).differentiableAt (by simp)).hasDerivAt
    have hdd : HasDerivAt (deriv f) (iteratedDeriv 2 f x) x := by
      simpa only [iteratedDeriv_succ,iteratedDeriv_one] using
        ((contDiffAt_iteratedDeriv_infty (hf x hx) 1).differentiableAt (by simp)).hasDerivAt
    have hratio := hd.div (hdd.const_mul y) (mul_pos hypos hdpos).ne'
    have hevent :
        (fun u => fderiv ℝ H (y,u) (1,0)/fderiv ℝ H (y,u) (0,1)) =ᶠ[nhds x]
          (fun u => f u/(y*deriv f u)) := by
      filter_upwards [isOpen_Ioi.mem_nhds hx] with u hu
      rw [(hcol u hu).1,(hcol u hu).2]
    have hratioder : deriv (fun u => f u/(y*deriv f u)) x =
        (deriv f x*(y*deriv f x)-f x*(y*iteratedDeriv 2 f x))/(y*deriv f x)^2 :=
      hratio.deriv
    rw [hevent.deriv_eq,hratioder]
    have heq :
        (deriv f x*(y*deriv f x)-f x*(y*iteratedDeriv 2 f x))/(y*deriv f x)^2 =
          ((deriv f x)^2-f x*iteratedDeriv 2 f x)/(y*(deriv f x)^2) := by
      field_simp
    rw [heq,abs_div,abs_of_pos (mul_pos hypos (sq_pos_of_pos hdpos))]
    have hsq : (deriv f x)^2 ≤ U^2 := by
      nlinarith only [(abs_le.mp hupper).2,hdpos]
    have hden : y*(deriv f x)^2 ≤ 3*U^2 :=
      mul_le_mul hy.2 hsq (sq_nonneg _) (by norm_num)
    exact (div_le_div_of_nonneg_left hc.le
      (mul_pos hypos (sq_pos_of_pos hdpos)) hden).trans
        (div_le_div_of_nonneg_right hdet (by positivity))

#print axioms linear_reference_curvature_data

example
    (f : ℝ → ℝ) {x y c U : ℝ}
    (hx : 0 < x) (hy : y∈Icc (1/2:ℝ) 3)
    (hc : 0 < c)
    (hf : ∀ u, 0 < u → ContDiffAt ℝ ∞ f u)
    (hlower : c ≤ deriv f x) (hupper : |deriv f x| ≤ U)
    (hdet : c ≤ |(deriv f x)^2-f x*iteratedDeriv 2 f x|) :
    let H := fun p : ℝ × ℝ => p.1*f p.2
    ContDiffAt ℝ 2 H (y,x) ∧
    fderiv ℝ H (y,x) (0,1)=y*deriv f x ∧
    fderiv ℝ H (y,x) (1,0)=f x ∧
    c/2 ≤ |fderiv ℝ H (y,x) (0,1)| ∧
    c/(3*U^2) ≤
      |deriv (fun u => fderiv ℝ H (y,u) (1,0)/
        fderiv ℝ H (y,u) (0,1)) x| :=
  @linear_reference_curvature_data f x y c U hx hy hc hf hlower hupper hdet

/-- A local count for actual approximate curvature coincidences.
All intermediate reference roots and their errors are constructed from
ordinary source derivatives; the existing curvature-fiber count supplies
the parameter compression. -/
private theorem linear_reference_local_parameter_count
    {c U : ℝ} (hc : 0 < c) (hU : 0 < U) :
    ∃ a C : ℝ, 0 < a ∧ a ≤ 1/4 ∧ 0 < C ∧
      ∀ (f : ℝ → ℝ) (x₀ y₀ ε E J q g : ℝ) (S : Finset ℝ) (x : ℝ → ℝ),
        x₀∈Icc (1:ℝ) 2 → y₀∈Icc (1:ℝ) 2 →
        (∀ u, 0 < u → ContDiffAt ℝ ∞ f u) →
        (∀ u∈Icc (1/2:ℝ) 3, c ≤ deriv f u) →
        (∀ u∈Icc (1/2:ℝ) 3,
          |f u| ≤ U ∧ |deriv f u| ≤ U ∧ |iteratedDeriv 2 f u| ≤ U) →
        (∀ u∈Icc (1/2:ℝ) 3,
          c ≤ |(deriv f u)^2-f u*iteratedDeriv 2 f u|) →
        0 ≤ ε → ε ≤ c/64 → 0 ≤ E → 0 < J →
        |y₀*f x₀-q| ≤ ε →
        (∀ y∈S, y∈Icc (1:ℝ) 2 ∧ |y-y₀| < a ∧ x y∈Icc (1:ℝ) 2) →
        (∀ y∈S, ∀ z∈S, y ≠ z → 1 ≤ J*|y-z|) →
        (∀ y∈S, |y*f (x y)-q| ≤ ε) →
        (∀ y∈S, |y*deriv f (x y)-g| ≤ E) →
        (S.card:ℝ) ≤ 1+C*(E+6*U*ε/c)*J := by
  classical
  let a := min (1/4:ℝ) (c/(64*U))
  let L := c/2
  let K := c/(3*U^2)
  have ha : 0 < a := lt_min (by norm_num) (by positivity)
  have hacap : a ≤ 1/4 := min_le_left _ _
  have hau : a*U ≤ c/64 := by
    have hh := (le_div_iff₀ (show 0 < 64*U by positivity)).mp
      (min_le_right (1/4:ℝ) (c/(64*U)))
    nlinarith only [hh]
  have hL : 0 < L := by dsimp only [L]; positivity
  have hK : 0 < K := by dsimp only [K]; positivity
  refine ⟨a,2/(L*K),ha,hacap,by positivity,?_⟩
  intro f x₀ y₀ ε E J q g S x hx₀ hy₀ hf hlower hupper hdet hε hεcap hE hJ
    hanchor hpoints hsep hlevels hprofiles
  let H := fun p : ℝ × ℝ => p.1*f p.2
  let ρ := fun y => Function.invFunOn (fun u => H (y,u)) (Ioo (3/4:ℝ) (9/4)) q
  have hsub : Icc (3/4:ℝ) (9/4) ⊆ Icc (1/2:ℝ) 3 := by
    intro u hu
    constructor <;> linarith only [hu.1,hu.2]
  have hpos (u : ℝ) (hu : u∈Icc (3/4:ℝ) (9/4)) : 0 < u := by
    linarith only [hu.1]
  have hinside (u : ℝ) (hu : u∈Icc (1:ℝ) 2) :
      u∈Ioo (3/4:ℝ) (9/4) ∧ (1/4:ℝ) ≤ min (u-3/4) (9/4-u) := by
    refine ⟨⟨by linarith only [hu.1],by linarith only [hu.2]⟩,?_⟩
    exact le_min (by linarith only [hu.1]) (by linarith only [hu.2])
  have hywide (y : ℝ) (hy : y∈Ioo (y₀-a) (y₀+a)) :
      y∈Icc (1/2:ℝ) 3 := by
    constructor <;> linarith only [hy.1,hy.2,hy₀.1,hy₀.2,hacap]
  have hder (y u : ℝ) (hu : u∈Icc (3/4:ℝ) (9/4)) :
      HasDerivAt (fun z => y*f z) (y*deriv f u) u :=
    (((hf u (hpos u hu)).differentiableAt (by simp)).hasDerivAt).const_mul y
  have hlow (y : ℝ) (hy : y∈Icc (1/2:ℝ) 3)
      (u : ℝ) (hu : u∈Icc (3/4:ℝ) (9/4)) : L ≤ y*deriv f u := by
    dsimp only [L]
    have hh := mul_le_mul hy.1 (hlower u (hsub hu)) hc.le (by linarith only [hy.1])
    nlinarith only [hh]
  have hdata (y : ℝ) (hy : y∈Ioo (y₀-a) (y₀+a))
      (u : ℝ) (hu : u∈Ioo (3/4:ℝ) (9/4)) :=
    linear_reference_curvature_data f (hpos u ⟨hu.1.le,hu.2.le⟩) (hywide y hy)
      hc hf (hlower u (hsub ⟨hu.1.le,hu.2.le⟩))
      (hupper u (hsub ⟨hu.1.le,hu.2.le⟩)).2.1
      (hdet u (hsub ⟨hu.1.le,hu.2.le⟩))
  have hroots (y : ℝ) (hy : y∈Ioo (y₀-a) (y₀+a)) :
      ρ y∈Ioo (3/4:ℝ) (9/4) ∧ H (y,ρ y)=q := by
    have hclose : |y-y₀| ≤ a :=
      (abs_lt.mpr ⟨by linarith only [hy.1],by linarith only [hy.2]⟩).le
    have herr : |y*f x₀-q| ≤ ε+a*U := by
      calc
        _ = |(y-y₀)*f x₀+(y₀*f x₀-q)| := by congr 1; ring
        _ ≤ |(y-y₀)*f x₀|+|y₀*f x₀-q| := abs_add_le _ _
        _ ≤ a*U+ε := by
          rw [abs_mul]
          exact add_le_add
            (mul_le_mul hclose (hupper x₀ ⟨by linarith only [hx₀.1],
              by linarith only [hx₀.2]⟩).1 (abs_nonneg _) ha.le) hanchor
        _ = _ := add_comm _ _
    have hsmall : ε+a*U < L*min (x₀-3/4) (9/4-x₀) := by
      have hh := mul_le_mul_of_nonneg_left (hinside x₀ hx₀).2 hL.le
      dsimp only [L] at hh ⊢
      nlinarith only [hh,hau,hεcap,hc]
    obtain ⟨v,hv,hvroot,_⟩ := reference_curvature_root_transfer
      (fun u => y*f u) (fun u => y*deriv f u) hL (by positivity)
      (hinside x₀ hx₀).1 hsmall (hder y) (hlow y (hywide y hy)) herr
    have himage : q∈(fun u => H (y,u)) '' Ioo (3/4:ℝ) (9/4) := ⟨v,hv,hvroot⟩
    exact ⟨Function.invFunOn_mem himage,Function.invFunOn_eq himage⟩
  have hS (y : ℝ) (hy : y∈S) : y∈Ioo (y₀-a) (y₀+a) := by
    have hh := abs_lt.mp (hpoints y hy).2.1
    constructor <;> linarith only [hh.1,hh.2]
  have hres (y : ℝ) (hy : y∈S) :
      |fderiv ℝ H (y,ρ y) (0,1)-g| ≤ E+6*U*ε/c := by
    have hyw := hywide y (hS y hy)
    have hx := (hpoints y hy).2.2
    have hsmall : ε < L*min (x y-3/4) (9/4-x y) := by
      have hh := mul_le_mul_of_nonneg_left (hinside (x y) hx).2 hL.le
      dsimp only [L] at hh ⊢
      linarith only [hh,hεcap,hc]
    have hgd (u : ℝ) (hu : u∈Icc (3/4:ℝ) (9/4)) :
        HasDerivAt (fun z => y*deriv f z) (y*iteratedDeriv 2 f u) u := by
      have hh : HasDerivAt (deriv f) (iteratedDeriv 2 f u) u := by
        simpa only [iteratedDeriv_succ,iteratedDeriv_one] using
          ((contDiffAt_iteratedDeriv_infty (hf u (hpos u hu)) 1).differentiableAt
            (by simp)).hasDerivAt
      exact hh.const_mul y
    have hgup (u : ℝ) (hu : u∈Icc (3/4:ℝ) (9/4)) :
        |y*iteratedDeriv 2 f u| ≤ 3*U := by
      rw [abs_mul,abs_of_nonneg (by linarith only [hyw.1] : 0 ≤ y)]
      exact mul_le_mul hyw.2 (hupper u (hsub hu)).2.2 (abs_nonneg _)
        (by norm_num)
    obtain ⟨v,hv,hvroot,_,hvprofile⟩ := reference_curvature_profile_transfer
      (fun u => y*f u) (fun u => y*deriv f u)
      (fun u => y*deriv f u) (fun u => y*iteratedDeriv 2 f u)
      hL hε (by positivity : 0 ≤ 3*U) (hinside (x y) hx).1 hsmall
      (hder y) (hlow y hyw) (hlevels y hy) hgd hgup (hprofiles y hy)
    have hmono : StrictMonoOn (fun u => y*f u) (Icc (3/4:ℝ) (9/4)) := by
      apply strictMonoOn_of_hasDerivWithinAt_pos (convex_Icc _ _)
        (fun u hu => (hder y u hu).continuousAt.continuousWithinAt)
        (fun u hu => (hder y u (interior_subset hu)).hasDerivWithinAt)
      exact fun u hu => hL.trans_le (hlow y hyw u (interior_subset hu))
    have hr := hroots y (hS y hy)
    have heq : ρ y=v := hmono.injOn ⟨hr.1.1.le,hr.1.2.le⟩
      ⟨hv.1.le,hv.2.le⟩ (hr.2.trans hvroot.symm)
    rw [(hdata y (hS y hy) (ρ y) hr.1).2.1,heq]
    convert hvprofile using 1
    dsimp only [L]
    ring
  have hcount := HuxleyRationalPhase.curvature_fiber_parameter_count S H ρ hL hK
    (show 0 ≤ E+6*U*ε/c by positivity) hJ hS hsep
    (fun y hy u hu => (hdata y hy u hu).1) hroots
    (fun y hy u hu => (hdata y hy u hu).2.2.2.1)
    (fun y hy u hu => (hdata y hy u hu).2.2.2.2) hres
  convert hcount using 1
  ring

#print axioms linear_reference_local_parameter_count

example
    {c U : ℝ} (hc : 0 < c) (hU : 0 < U) :
    ∃ a C : ℝ, 0 < a ∧ a ≤ 1/4 ∧ 0 < C ∧
      ∀ (f : ℝ → ℝ) (x₀ y₀ ε E J q g : ℝ) (S : Finset ℝ) (x : ℝ → ℝ),
        x₀∈Icc (1:ℝ) 2 → y₀∈Icc (1:ℝ) 2 →
        (∀ u, 0 < u → ContDiffAt ℝ ∞ f u) →
        (∀ u∈Icc (1/2:ℝ) 3, c ≤ deriv f u) →
        (∀ u∈Icc (1/2:ℝ) 3,
          |f u| ≤ U ∧ |deriv f u| ≤ U ∧ |iteratedDeriv 2 f u| ≤ U) →
        (∀ u∈Icc (1/2:ℝ) 3,
          c ≤ |(deriv f u)^2-f u*iteratedDeriv 2 f u|) →
        0 ≤ ε → ε ≤ c/64 → 0 ≤ E → 0 < J →
        |y₀*f x₀-q| ≤ ε →
        (∀ y∈S, y∈Icc (1:ℝ) 2 ∧ |y-y₀| < a ∧ x y∈Icc (1:ℝ) 2) →
        (∀ y∈S, ∀ z∈S, y ≠ z → 1 ≤ J*|y-z|) →
        (∀ y∈S, |y*f (x y)-q| ≤ ε) →
        (∀ y∈S, |y*deriv f (x y)-g| ≤ E) →
        (S.card:ℝ) ≤ 1+C*(E+6*U*ε/c)*J
  := @linear_reference_local_parameter_count c U hc hU

/-- The existing finite-bin globalization applied to the constructed
approximate-level count. The error tolerance is retained explicitly. -/
private theorem linear_reference_parameter_count
    {c U : ℝ} (hc : 0 < c) (hU : 0 < U) :
    ∃ K C : ℝ, 0 < K ∧ 0 < C ∧
      ∀ (f : ℝ → ℝ) (ε E J q g : ℝ) (S : Finset ℝ) (x : ℝ → ℝ),
        (∀ u, 0 < u → ContDiffAt ℝ ∞ f u) →
        (∀ u∈Icc (1/2:ℝ) 3, c ≤ deriv f u) →
        (∀ u∈Icc (1/2:ℝ) 3,
          |f u| ≤ U ∧ |deriv f u| ≤ U ∧ |iteratedDeriv 2 f u| ≤ U) →
        (∀ u∈Icc (1/2:ℝ) 3,
          c ≤ |(deriv f u)^2-f u*iteratedDeriv 2 f u|) →
        0 ≤ ε → ε ≤ c/64 → 0 ≤ E → 0 < J →
        (∀ y∈S, y∈Icc (1:ℝ) 2 ∧ x y∈Icc (1:ℝ) 2) →
        (∀ y∈S, ∀ z∈S, y ≠ z → 1 ≤ J*|y-z|) →
        (∀ y∈S, |y*f (x y)-q| ≤ ε) →
        (∀ y∈S, |y*deriv f (x y)-g| ≤ E) →
        (S.card:ℝ) ≤ K*(1+C*(E+6*U*ε/c)*J) := by
  classical
  obtain ⟨a,C,ha,_,hC,hlocal⟩ := linear_reference_local_parameter_count hc hU
  refine ⟨2+1/a,C,by positivity,hC,?_⟩
  intro f ε E J q g S x hf hlower hupper hdet hε hεcap hE hJ hpoints hsep hroot hres
  let bin := fun y : ℝ => ⌊y/a⌋
  let I := S.image bin
  let B := 1+C*(E+6*U*ε/c)*J
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  have hI : (I.card:ℝ) ≤ 2+1/a := by
    have hrange n (hn : n ∈ I) : 1/a-1 ≤ (n:ℝ) ∧ (n:ℝ) ≤ 2/a := by
      obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hn
      have hlo := Int.floor_le (y/a)
      have hhi := Int.lt_floor_add_one (y/a)
      have hyl := div_le_div_of_nonneg_right (hpoints y hy).1.1 ha.le
      have hyu := div_le_div_of_nonneg_right (hpoints y hy).1.2 ha.le
      change (bin y:ℝ) ≤ y/a at hlo
      change y/a < (bin y:ℝ)+1 at hhi
      constructor <;> linarith only [hlo,hhi,hyl,hyu]
    have hh := integer_card_le_interval_length_add_one I
      (show 1/a-1 ≤ 2/a from (sub_le_self _ zero_le_one).trans
        (div_le_div_of_nonneg_right (by norm_num : (1:ℝ) ≤ 2) ha.le)) hrange
    calc
      _ ≤ 2/a-(1/a-1)+1 := hh
      _ = _ := by ring
  have hfiber n : ((S.filter (fun y => bin y=n)).card:ℝ) ≤ B := by
    let V := S.filter (fun y => bin y=n)
    rcases V.eq_empty_or_nonempty with hv | hv
    · change (V.card:ℝ) ≤ B
      rw [hv,Finset.card_empty,Nat.cast_zero]
      exact hB
    obtain ⟨y₀,hy₀⟩ := hv
    have hy₀S : y₀ ∈ S := (Finset.mem_filter.mp hy₀).1
    have hclose y (hy : y ∈ V) : |y-y₀| < a := by
      have hbin : bin y=bin y₀ := (Finset.mem_filter.mp hy).2.trans
        (Finset.mem_filter.mp hy₀).2.symm
      have hylo := Int.floor_le (y/a)
      have hyhi := Int.lt_floor_add_one (y/a)
      have h₀lo := Int.floor_le (y₀/a)
      have h₀hi := Int.lt_floor_add_one (y₀/a)
      change (bin y:ℝ) ≤ y/a at hylo
      change y/a < (bin y:ℝ)+1 at hyhi
      change (bin y₀:ℝ) ≤ y₀/a at h₀lo
      change y₀/a < (bin y₀:ℝ)+1 at h₀hi
      rw [hbin] at hylo hyhi
      have hl₁ := (le_div_iff₀ ha).mp hylo
      have hu₁ := (div_lt_iff₀ ha).mp hyhi
      have hl₂ := (le_div_iff₀ ha).mp h₀lo
      have hu₂ := (div_lt_iff₀ ha).mp h₀hi
      exact abs_lt.mpr ⟨by nlinarith only [hl₁,hu₂],by nlinarith only [hu₁,hl₂]⟩
    exact hlocal f (x y₀) y₀ ε E J q g V x (hpoints y₀ hy₀S).2
      (hpoints y₀ hy₀S).1 hf hlower hupper hdet hε hεcap hE hJ (hroot y₀ hy₀S)
      (fun y hy => ⟨(hpoints y (Finset.mem_filter.mp hy).1).1,hclose y hy,
        (hpoints y (Finset.mem_filter.mp hy).1).2⟩)
      (fun y hy z hz hyz => hsep y (Finset.mem_filter.mp hy).1 z
        (Finset.mem_filter.mp hz).1 hyz)
      (fun y hy => hroot y (Finset.mem_filter.mp hy).1)
      (fun y hy => hres y (Finset.mem_filter.mp hy).1)
  have hcard : (S.card:ℝ)=∑ n ∈ I, ((S.filter (fun y => bin y=n)).card:ℝ) := by
    exact_mod_cast Finset.card_eq_sum_card_fiberwise
      (fun y hy => Finset.mem_image_of_mem bin hy)
  calc
    (S.card:ℝ) = _ := hcard
    _ ≤ ∑ _n ∈ I, B := Finset.sum_le_sum (fun n _ => hfiber n)
    _ = (I.card:ℝ)*B := by simp only [Finset.sum_const,nsmul_eq_mul]
    _ ≤ (2+1/a)*B := mul_le_mul_of_nonneg_right hI hB

#print axioms linear_reference_parameter_count

example
    {c U : ℝ} (hc : 0 < c) (hU : 0 < U) :
    ∃ K C : ℝ, 0 < K ∧ 0 < C ∧
      ∀ (f : ℝ → ℝ) (ε E J q g : ℝ) (S : Finset ℝ) (x : ℝ → ℝ),
        (∀ u, 0 < u → ContDiffAt ℝ ∞ f u) →
        (∀ u∈Icc (1/2:ℝ) 3, c ≤ deriv f u) →
        (∀ u∈Icc (1/2:ℝ) 3,
          |f u| ≤ U ∧ |deriv f u| ≤ U ∧ |iteratedDeriv 2 f u| ≤ U) →
        (∀ u∈Icc (1/2:ℝ) 3,
          c ≤ |(deriv f u)^2-f u*iteratedDeriv 2 f u|) →
        0 ≤ ε → ε ≤ c/64 → 0 ≤ E → 0 < J →
        (∀ y∈S, y∈Icc (1:ℝ) 2 ∧ x y∈Icc (1:ℝ) 2) →
        (∀ y∈S, ∀ z∈S, y ≠ z → 1 ≤ J*|y-z|) →
        (∀ y∈S, |y*f (x y)-q| ≤ ε) →
        (∀ y∈S, |y*deriv f (x y)-g| ≤ E) →
        (S.card:ℝ) ≤ K*(1+C*(E+6*U*ε/c)*J) :=
  @linear_reference_parameter_count c U hc hU

/-- The actual normalized double phase has the common reference jets,
with an explicit error uniform over all selected shift pairs. -/
private theorem normalized_double_difference_common_jet
    (F : ℝ → ℝ) {x r s δ y U w : ℝ} (j : ℕ)
    (hr : 0 ≤ r) (hs : 0 ≤ s) (hδ : 0 < δ) (hy : y∈Icc (1:ℝ) 2)
    (hU : 0 ≤ U) (hprod : r*s=δ*y) (hshift : r+s ≤ w)
    (hreg : ∀ u∈Icc x (x+r+s), ContDiffAt ℝ ∞ F u)
    (hjet : ∀ u∈Icc x (x+r+s), |iteratedDeriv (j+3) F u| ≤ U) :
    |iteratedDeriv j
      (fun u => (F u-F (u+r)-F (u+s)+F (u+r+s))/δ) x-
        y*iteratedDeriv (j+2) F x| ≤ 2*U*w := by
  have hbase := double_difference_all_common_jets hr hs hU hreg j hjet
  rw [iteratedDeriv_div_const]
  have heq :
      iteratedDeriv j (fun u => F u-F (u+r)-F (u+s)+F (u+r+s)) x/δ-
        y*iteratedDeriv (j+2) F x =
      (iteratedDeriv j (fun u => F u-F (u+r)-F (u+s)+F (u+r+s)) x-
        r*s*iteratedDeriv (j+2) F x)/δ := by
    rw [hprod]
    field_simp
  rw [heq,abs_div,abs_of_pos hδ]
  calc
    _ ≤ U*r*s*(r+s)/δ := div_le_div_of_nonneg_right hbase hδ.le
    _ = U*y*(r+s) := by
      rw [show U*r*s=U*(r*s) by ring,hprod]
      field_simp
    _ ≤ (U*2)*w := mul_le_mul
      (mul_le_mul_of_nonneg_left hy.2 hU) hshift (by positivity) (by positivity)
    _ = _ := by ring

#print axioms normalized_double_difference_common_jet

example
    (F : ℝ → ℝ) {x r s δ y U w : ℝ} (j : ℕ)
    (hr : 0 ≤ r) (hs : 0 ≤ s) (hδ : 0 < δ) (hy : y∈Icc (1:ℝ) 2)
    (hU : 0 ≤ U) (hprod : r*s=δ*y) (hshift : r+s ≤ w)
    (hreg : ∀ u∈Icc x (x+r+s), ContDiffAt ℝ ∞ F u)
    (hjet : ∀ u∈Icc x (x+r+s), |iteratedDeriv (j+3) F u| ≤ U) :
    |iteratedDeriv j
      (fun u => (F u-F (u+r)-F (u+s)+F (u+r+s))/δ) x-
        y*iteratedDeriv (j+2) F x| ≤ 2*U*w :=
  @normalized_double_difference_common_jet F x r s δ y U w j hr hs hδ hy hU hprod hshift hreg hjet

/-- A genuine consumer of the selected double-difference phases.
Only actual source-jet bounds, ordinary parameter spacing and observed
curvature/profile coincidences are premises. No reference root, profile
comparison or parameter-count certificate is supplied. -/
private theorem double_difference_parameter_count
    {c U : ℝ} (hc : 0 < c) (hU : 0 < U) :
    ∃ K C : ℝ, 0 < K ∧ 0 < C ∧
      ∀ (F : ℝ → ℝ) (δ w E J q g : ℝ) (S : Finset ℝ) (x r s : ℝ → ℝ),
        (∀ u, 0 < u → ContDiffAt ℝ ∞ F u) →
        (∀ u∈Icc (1/2:ℝ) 3, c ≤ iteratedDeriv 5 F u) →
        (∀ u∈Icc (1/2:ℝ) 3,
          |iteratedDeriv 4 F u| ≤ U ∧ |iteratedDeriv 5 F u| ≤ U ∧
            |iteratedDeriv 6 F u| ≤ U) →
        (∀ u∈Icc (1/2:ℝ) 3,
          c ≤ |(iteratedDeriv 5 F u)^2-iteratedDeriv 4 F u*iteratedDeriv 6 F u|) →
        0 < δ → 0 ≤ w → w ≤ 1/4 → 2*U*w ≤ c/64 → 0 ≤ E → 0 < J →
        (∀ y∈S, y∈Icc (1:ℝ) 2 ∧ x y∈Icc (1:ℝ) 2) →
        (∀ y∈S, ∀ z∈S, y ≠ z → 1 ≤ J*|y-z|) →
        (∀ y∈S, 0 ≤ r y ∧ 0 ≤ s y ∧ r y*s y=δ*y ∧ r y+s y ≤ w) →
        let Q := fun y u =>
          (F u-F (u+r y)-F (u+s y)+F (u+r y+s y))/δ
        (∀ y∈S, iteratedDeriv 2 (Q y) (x y)=q) →
        (∀ y∈S, |iteratedDeriv 3 (Q y) (x y)-g| ≤ E) →
        (S.card:ℝ) ≤ K*(1+C*(E+2*U*w+12*U^2*w/c)*J) := by
  obtain ⟨K,C,hK,hC,hcount⟩ := linear_reference_parameter_count hc hU
  refine ⟨K,C,hK,hC,?_⟩
  intro F δ w E J q g S x r s hf hlower hupper hdet hδ hw hwcap hsmall hE hJ
    hpoints hsep hshifts Q hlevels hprofiles
  have hfd : deriv (iteratedDeriv 4 F)=iteratedDeriv 5 F :=
    (iteratedDeriv_succ (n:=4) (f:=F)).symm
  have hfd₂ : iteratedDeriv 2 (iteratedDeriv 4 F)=iteratedDeriv 6 F := by
    rw [iteratedDeriv_real_comp_order]
  have hsub (y : ℝ) (hy : y∈S) :
      Icc (x y) (x y+r y+s y) ⊆ Icc (1/2:ℝ) 3 := by
    intro u hu
    have hp := (hpoints y hy).2
    have hs' := (hshifts y hy).2.2.2
    constructor <;> linarith only [hu.1,hu.2,hp.1,hp.2,hs',hwcap]
  have hjet (y : ℝ) (hy : y∈S) (j : ℕ) (hj : j=2 ∨ j=3) :
      |iteratedDeriv j (Q y) (x y)-y*iteratedDeriv (j+2) F (x y)| ≤ 2*U*w := by
    apply normalized_double_difference_common_jet F j (hshifts y hy).1
      (hshifts y hy).2.1 hδ (hpoints y hy).1 hU.le (hshifts y hy).2.2.1
      (hshifts y hy).2.2.2
    · intro u hu
      exact hf u (by linarith only [(hsub y hy hu).1])
    · intro u hu
      rcases hj with rfl | rfl
      · exact (hupper u (hsub y hy hu)).2.1
      · exact (hupper u (hsub y hy hu)).2.2
  have hlevels' (y : ℝ) (hy : y∈S) :
      |y*iteratedDeriv 4 F (x y)-q| ≤ 2*U*w := by
    have hh := hjet y hy 2 (Or.inl rfl)
    rw [hlevels y hy,abs_sub_comm] at hh
    exact hh
  have hprofiles' (y : ℝ) (hy : y∈S) :
      |y*deriv (iteratedDeriv 4 F) (x y)-g| ≤ E+2*U*w := by
    rw [hfd]
    calc
      _ = |(y*iteratedDeriv 5 F (x y)-iteratedDeriv 3 (Q y) (x y))+
        (iteratedDeriv 3 (Q y) (x y)-g)| := by congr 1; ring
      _ ≤ |y*iteratedDeriv 5 F (x y)-iteratedDeriv 3 (Q y) (x y)|+
        |iteratedDeriv 3 (Q y) (x y)-g| := abs_add_le _ _
      _ ≤ 2*U*w+E := add_le_add
        (by simpa only [abs_sub_comm] using hjet y hy 3 (Or.inr rfl)) (hprofiles y hy)
      _ = _ := add_comm _ _
  have hh := hcount (iteratedDeriv 4 F) (2*U*w) (E+2*U*w) J q g S x
    (fun u hu => contDiffAt_iteratedDeriv_infty (hf u hu) 4)
    (by simpa only [hfd] using hlower)
    (by simpa only [hfd,hfd₂] using hupper)
    (by simpa only [hfd,hfd₂] using hdet)
    (by positivity) hsmall (by positivity) hJ hpoints hsep hlevels' hprofiles'
  convert hh using 1
  ring

#print axioms double_difference_parameter_count

example
    {c U : ℝ} (hc : 0 < c) (hU : 0 < U) :
    ∃ K C : ℝ, 0 < K ∧ 0 < C ∧
      ∀ (F : ℝ → ℝ) (δ w E J q g : ℝ) (S : Finset ℝ) (x r s : ℝ → ℝ),
        (∀ u, 0 < u → ContDiffAt ℝ ∞ F u) →
        (∀ u∈Icc (1/2:ℝ) 3, c ≤ iteratedDeriv 5 F u) →
        (∀ u∈Icc (1/2:ℝ) 3,
          |iteratedDeriv 4 F u| ≤ U ∧ |iteratedDeriv 5 F u| ≤ U ∧
            |iteratedDeriv 6 F u| ≤ U) →
        (∀ u∈Icc (1/2:ℝ) 3,
          c ≤ |(iteratedDeriv 5 F u)^2-iteratedDeriv 4 F u*iteratedDeriv 6 F u|) →
        0 < δ → 0 ≤ w → w ≤ 1/4 → 2*U*w ≤ c/64 → 0 ≤ E → 0 < J →
        (∀ y∈S, y∈Icc (1:ℝ) 2 ∧ x y∈Icc (1:ℝ) 2) →
        (∀ y∈S, ∀ z∈S, y ≠ z → 1 ≤ J*|y-z|) →
        (∀ y∈S, 0 ≤ r y ∧ 0 ≤ s y ∧ r y*s y=δ*y ∧ r y+s y ≤ w) →
        let Q := fun y u =>
          (F u-F (u+r y)-F (u+s y)+F (u+r y+s y))/δ
        (∀ y∈S, iteratedDeriv 2 (Q y) (x y)=q) →
        (∀ y∈S, |iteratedDeriv 3 (Q y) (x y)-g| ≤ E) →
        (S.card:ℝ) ≤ K*(1+C*(E+2*U*w+12*U^2*w/c)*J) :=
  @double_difference_parameter_count c U hc hU

/-- Actual cubic and fourth jets on the enlarged rounding interval.
The positive cubic lower bound and every rounding derivative bound are
derived from the same normalized double phase. -/
private theorem double_difference_cubic_jet_bounds
    (F : ℝ → ℝ) {x r s δ y U c w : ℝ}
    (hx : x∈Icc (3/4:ℝ) (9/4)) (hy : y∈Icc (1:ℝ) 2)
    (hr : 0 ≤ r) (hs : 0 ≤ s) (hδ : 0 < δ) (hU : 0 < U) (hc : 0 < c)
    (hprod : r*s=δ*y) (hshift : r+s ≤ w) (hw : w ≤ 1/4)
    (hsmall : 2*U*w ≤ c/64)
    (hf : ∀ u, 0 < u → ContDiffAt ℝ ∞ F u)
    (hlower : ∀ u∈Icc (1/2:ℝ) 3, c ≤ iteratedDeriv 5 F u)
    (hbound : ∀ u∈Icc (1/2:ℝ) 3, ∀ n, 1 ≤ n → n ≤ 7 → |iteratedDeriv n F u| ≤ U) :
    let Q := fun u => (F u-F (u+r)-F (u+s)+F (u+r+s))/δ
    (∀ u, 0 < u → ContDiffAt ℝ ∞ Q u) ∧
      c/2 ≤ iteratedDeriv 3 Q x ∧
      |iteratedDeriv 3 Q x| ≤ 3*U ∧ |iteratedDeriv 4 Q x| ≤ 3*U := by
  intro Q
  have hx' : x∈Icc (1/2:ℝ) 3 :=
    ⟨by linarith only [hx.1],by linarith only [hx.2]⟩
  have hsub : Icc x (x+r+s) ⊆ Icc (1/2:ℝ) 3 := by
    intro u hu
    constructor <;> linarith only [hu.1,hu.2,hx.1,hx.2,hshift,hw]
  have hj (j : ℕ) (hj : j≤4) :
      |iteratedDeriv j Q x-y*iteratedDeriv (j+2) F x| ≤ 2*U*w :=
    normalized_double_difference_common_jet F j hr hs hδ hy hU.le hprod hshift
      (fun u hu => hf u (by linarith only [(hsub hu).1]))
      (fun u hu => hbound u (hsub hu) (j+3) (by omega) (by omega))
  have hsize (j : ℕ) (hj' : j≤4) : |iteratedDeriv j Q x| ≤ 3*U := by
    have hmain : |y*iteratedDeriv (j+2) F x| ≤ 2*U := by
      rw [abs_mul,abs_of_nonneg (by linarith only [hy.1] : 0 ≤ y)]
      exact mul_le_mul hy.2 (hbound x hx' (j+2) (by omega) (by omega)) (abs_nonneg _)
        (by norm_num)
    have htri := abs_add_le
      (iteratedDeriv j Q x-y*iteratedDeriv (j+2) F x)
      (y*iteratedDeriv (j+2) F x)
    rw [sub_add_cancel] at htri
    have herror := mul_le_mul_of_nonneg_left hw (show 0 ≤ 2*U by positivity)
    linarith only [htri,hmain,hj j hj',herror,hU]
  refine ⟨?_,?_,hsize 3 (by norm_num),hsize 4 (by norm_num)⟩
  · intro u hu
    exact ((((hf u hu).sub ((hf (u+r) (by positivity)).comp u
      (contDiffAt_id.add contDiffAt_const))).sub
        ((hf (u+s) (by positivity)).comp u (contDiffAt_id.add contDiffAt_const))).add
          ((hf (u+r+s) (by positivity)).comp u
            ((contDiffAt_id.add contDiffAt_const).add contDiffAt_const))).div_const δ
  · have hh := (abs_le.mp (hj 3 (by norm_num))).1
    have hmain : c ≤ y*iteratedDeriv 5 F x := by
      have hh' := mul_le_mul hy.1 (hlower x hx') hc.le (by linarith only [hy.1])
      simpa only [one_mul] using hh'
    linarith only [hh,hmain,hsmall,hc]

#print axioms double_difference_cubic_jet_bounds

example
    (F : ℝ → ℝ) {x r s δ y U c w : ℝ}
    (hx : x∈Icc (3/4:ℝ) (9/4)) (hy : y∈Icc (1:ℝ) 2)
    (hr : 0 ≤ r) (hs : 0 ≤ s) (hδ : 0 < δ) (hU : 0 < U) (hc : 0 < c)
    (hprod : r*s=δ*y) (hshift : r+s ≤ w) (hw : w ≤ 1/4)
    (hsmall : 2*U*w ≤ c/64)
    (hf : ∀ u, 0 < u → ContDiffAt ℝ ∞ F u)
    (hlower : ∀ u∈Icc (1/2:ℝ) 3, c ≤ iteratedDeriv 5 F u)
    (hbound : ∀ u∈Icc (1/2:ℝ) 3, ∀ n, 1 ≤ n → n ≤ 7 → |iteratedDeriv n F u| ≤ U) :
    let Q := fun u => (F u-F (u+r)-F (u+s)+F (u+r+s))/δ
    (∀ u, 0 < u → ContDiffAt ℝ ∞ Q u) ∧
      c/2 ≤ iteratedDeriv 3 Q x ∧
      |iteratedDeriv 3 Q x| ≤ 3*U ∧ |iteratedDeriv 4 Q x| ≤ 3*U :=
  @double_difference_cubic_jet_bounds F x r s δ y U c w hx hy hr hs hδ hU hc hprod hshift hw hsmall hf hlower hbound

/-- Reuse the measured rounded Third test with its exact two rounding
errors. The reference nonvanishing is explicit and is derived from the
actual cubic jet by the source consumer. -/
private theorem rounded_weighted_profile_bound
    (Ga Gb Da Db : ℝ → ℝ) {xa xb M B Δ q : ℝ}
    (hxa : xa∈Icc (1:ℝ) 2) (hxb : xb∈Icc (1:ℝ) 2)
    (hM : 2 ≤ M) (hB : 0 ≤ B) (hΔ : 0 ≤ Δ)
    (hda : ∀ u∈Icc (3/4:ℝ) (9/4), HasDerivAt Ga (Da u) u)
    (hdb : ∀ u∈Icc (3/4:ℝ) (9/4), HasDerivAt Gb (Db u) u)
    (hba : ∀ u∈Icc (3/4:ℝ) (9/4), |Da u| ≤ B)
    (hbb : ∀ u∈Icc (3/4:ℝ) (9/4), |Db u| ≤ B)
    (href : ∀ u∈Icc (3/4:ℝ) (9/4), |Ga u| ≤ B ∧ Ga u ≠ 0)
    (hnear : |Gb ((round (M*xb):ℝ)/M)/Ga ((round (M*xa):ℝ)/M)*q-1| ≤ Δ) :
    |Gb xb*q-Ga xa| ≤ B*(Δ+(|q|+1)/(2*M)) := by
  have hMpos : 0 < M := by linarith only [hM]
  let rd := fun x : ℝ => (round (M*x):ℝ)/M
  have hr x : |rd x-x| ≤ 1/(2*M) := by
    calc
      _ = |((round (M*x):ℝ)-M*x)/M| := by
        congr 1
        dsimp only [rd]
        field_simp
      _ = |(round (M*x):ℝ)-M*x|/M := by rw [abs_div,abs_of_pos hMpos]
      _ ≤ (1/2)/M := div_le_div_of_nonneg_right
        (by simpa only [abs_sub_comm] using abs_sub_round (M*x)) hMpos.le
      _ = _ := by ring
  have hquarter : 1/(2*M) ≤ (1/4:ℝ) := by
    apply (div_le_iff₀ (by positivity : 0 < 2*M)).mpr
    linarith only [hM]
  have hxext x (hx : x∈Icc (1:ℝ) 2) : x∈Icc (3/4:ℝ) (9/4) :=
    ⟨by linarith only [hx.1],by linarith only [hx.2]⟩
  have hrange x (hx : x∈Icc (1:ℝ) 2) : rd x∈Icc (3/4:ℝ) (9/4) := by
    have hb := abs_le.mp ((hr x).trans hquarter)
    constructor <;> linarith only [hb.1,hb.2,hx.1,hx.2]
  have herr (G D : ℝ → ℝ)
      (hd : ∀ u∈Icc (3/4:ℝ) (9/4), HasDerivAt G (D u) u)
      (hup : ∀ u∈Icc (3/4:ℝ) (9/4), |D u| ≤ B)
      (x : ℝ) (hx : x∈Icc (1:ℝ) 2) : |G x-G (rd x)| ≤ B/(2*M) := by
    have hh : |G x-G (rd x)| ≤ B*|x-rd x| := by
      apply (convex_Icc (3/4:ℝ) (9/4)).norm_image_sub_le_of_norm_deriv_le
        (fun z hz => (hd z hz).differentiableAt) (fun z hz => ?_)
        (hrange x hx) (hxext x hx)
      rw [(hd z hz).deriv,Real.norm_eq_abs]
      exact hup z hz
    calc
      _ ≤ B*|x-rd x| := hh
      _ ≤ B*(1/(2*M)) := mul_le_mul_of_nonneg_left
        (by simpa only [abs_sub_comm] using hr x) hB
      _ = _ := by ring
  have hGa : Ga (rd xa) ≠ 0 := (href (rd xa) (hrange xa hxa)).2
  have hcoinc : |Gb (rd xb)*q-Ga (rd xa)| ≤ B*Δ := by
    calc
      _ = |Ga (rd xa)| * |Gb (rd xb)/Ga (rd xa)*q-1| := by
        rw [←abs_mul]
        congr 1
        field_simp
      _ ≤ |Ga (rd xa)| * Δ := mul_le_mul_of_nonneg_left hnear (abs_nonneg _)
      _ ≤ B*Δ := mul_le_mul_of_nonneg_right (href (rd xa) (hrange xa hxa)).1 hΔ
  have he : Gb xb*q-Ga xa =
      (Gb xb-Gb (rd xb))*q+(Gb (rd xb)*q-Ga (rd xa))+(Ga (rd xa)-Ga xa) := by ring
  rw [he]
  calc
    _ ≤ |(Gb xb-Gb (rd xb))*q|+|Gb (rd xb)*q-Ga (rd xa)|+
        |Ga (rd xa)-Ga xa| :=
      (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ (B/(2*M))*|q|+B*Δ+B/(2*M) := by
      rw [abs_mul,abs_sub_comm (Ga (rd xa))]
      exact add_le_add (add_le_add
        (mul_le_mul_of_nonneg_right (herr Gb Db hdb hbb xb hxb) (abs_nonneg q)) hcoinc)
        (herr Ga Da hda hba xa hxa)
    _ = _ := by ring

#print axioms rounded_weighted_profile_bound

example
    (Ga Gb Da Db : ℝ → ℝ) {xa xb M B Δ q : ℝ}
    (hxa : xa∈Icc (1:ℝ) 2) (hxb : xb∈Icc (1:ℝ) 2)
    (hM : 2 ≤ M) (hB : 0 ≤ B) (hΔ : 0 ≤ Δ)
    (hda : ∀ u∈Icc (3/4:ℝ) (9/4), HasDerivAt Ga (Da u) u)
    (hdb : ∀ u∈Icc (3/4:ℝ) (9/4), HasDerivAt Gb (Db u) u)
    (hba : ∀ u∈Icc (3/4:ℝ) (9/4), |Da u| ≤ B)
    (hbb : ∀ u∈Icc (3/4:ℝ) (9/4), |Db u| ≤ B)
    (href : ∀ u∈Icc (3/4:ℝ) (9/4), |Ga u| ≤ B ∧ Ga u ≠ 0)
    (hnear : |Gb ((round (M*xb):ℝ)/M)/Ga ((round (M*xa):ℝ)/M)*q-1| ≤ Δ) :
    |Gb xb*q-Ga xa| ≤ B*(Δ+(|q|+1)/(2*M)) :=
  @rounded_weighted_profile_bound Ga Gb Da Db xa xb M B Δ q hxa hxb hM hB hΔ hda hdb hba hbb href hnear

/-- The actual physical rounded Third Condition discharges the
selected double-phase parameter count. Both T/M derivative scaling and
the rounding loss are proved, with the shift error still visible. -/
private theorem double_difference_physical_parameter_count
    {c U : ℝ} (hc : 0 < c) (hU : 0 < U) :
    ∃ K C : ℝ, 0 < K ∧ 0 < C ∧
      ∀ (F : ℝ → ℝ) (δ w ya xa Δ J q t T M : ℝ)
        (S : Finset ℝ) (x r s : ℝ → ℝ),
        (∀ u, 0 < u → ContDiffAt ℝ ∞ F u) →
        (∀ u∈Icc (1/2:ℝ) 3, c ≤ iteratedDeriv 5 F u) →
        (∀ u∈Icc (1/2:ℝ) 3, ∀ n, 1 ≤ n → n ≤ 7 → |iteratedDeriv n F u| ≤ U) →
        (∀ u∈Icc (1/2:ℝ) 3,
          c ≤ |(iteratedDeriv 5 F u)^2-iteratedDeriv 4 F u*iteratedDeriv 6 F u|) →
        0 < δ → 0 ≤ w → w ≤ 1/4 → 2*U*w ≤ c/64 →
        ya∈Icc (1:ℝ) 2 → 0 < T → 2 ≤ M → 0 ≤ Δ → 0 < J →
        t∈Icc (1/2:ℝ) 2 → xa∈Icc M (2*M) →
        (∀ y∈S, y∈Icc (1:ℝ) 2 ∧ x y∈Icc M (2*M)) →
        (∀ y∈S, ∀ z∈S, y ≠ z → 1 ≤ J*|y-z|) →
        (∀ y, y=ya ∨ y∈S →
          0 ≤ r y ∧ 0 ≤ s y ∧ r y*s y=δ*y ∧ r y+s y ≤ w) →
        let Q := fun y u => (F u-F (u+r y)-F (u+s y)+F (u+r y+s y))/δ
        let f := fun y z => T*Q y (z/M)
        let μ := fun y z => iteratedDeriv 3 (f y) (round z)/6
        (∀ y∈S, iteratedDeriv 2 (f y) (x y)/2=q) →
        (∀ y∈S, |μ y (x y)/μ ya xa*t^3-1| ≤ Δ) →
        (S.card:ℝ) ≤ K*(1+C*(24*U*(Δ+5/M)+2*U*w+12*U^2*w/c)*J) := by
  classical
  obtain ⟨K,C,hK,hC,hcount⟩ := double_difference_parameter_count hc hU
  refine ⟨K,C,hK,hC,?_⟩
  intro F δ w ya xa Δ J q t T M S x r s hf hlower hbound hdet hδ hw hwcap hsmall
    hya hT hM hΔ hJ ht hxa hpoints hsep hshifts Q f μ hmap hthird
  have hMpos : 0 < M := by linarith only [hM]
  have htpos : 0 < t := by linarith only [ht.1]
  have hpar (y : ℝ) (hy : y=ya ∨ y∈S) : y∈Icc (1:ℝ) 2 := by
    rcases hy with rfl | hy
    · exact hya
    · exact (hpoints y hy).1
  have hjet (y : ℝ) (hy : y=ya ∨ y∈S) (u : ℝ) (hu : u∈Icc (3/4:ℝ) (9/4)) :=
    double_difference_cubic_jet_bounds F hu (hpar y hy) (hshifts y hy).1
      (hshifts y hy).2.1 hδ hU hc (hshifts y hy).2.2.1 (hshifts y hy).2.2.2
      hwcap hsmall hf hlower hbound
  have hreg (y : ℝ) (hy : y=ya ∨ y∈S) :
      ∀ u, 0 < u → ContDiffAt ℝ ∞ (Q y) u :=
    (hjet y hy 1 (by norm_num)).1
  have hd (n : ℕ) (z y : ℝ) (hz : 0 < z) (hy : y=ya ∨ y∈S) :
      iteratedDeriv n (f y) z=T/M^n*iteratedDeriv n (Q y) (z/M) := by
    have ha := sargos_iteratedDeriv_comp_affine_local (f:=Q y)
      (l:=0) (r:=z+1) (c:=M⁻¹) (d:=0)
      (fun u hu => hreg y hy _ (by
        simpa only [add_zero] using mul_pos (inv_pos.mpr hMpos) hu.1))
      (show z∈Ioo (0:ℝ) (z+1) from ⟨hz,by linarith⟩) n
    change iteratedDeriv n (fun u => T*Q y (u/M)) z=_
    rw [iteratedDeriv_const_mul_field]
    have he : (fun u => Q y (u/M))=(fun u => Q y (M⁻¹*u+0)) := by
      funext u
      congr 1
      ring
    rw [he,ha]
    simp only [add_zero,inv_pow]
    rw [show M⁻¹*z=z/M by ring]
    ring
  have hnorm (z : ℝ) (hz : z∈Icc M (2*M)) : z/M∈Icc (1:ℝ) 2 :=
    ⟨(le_div_iff₀ hMpos).mpr (by simpa using hz.1),(div_le_iff₀ hMpos).mpr hz.2⟩
  let G := fun y u => iteratedDeriv 3 (Q y) u
  let g := G ya (xa/M)/t^3
  have hroots (y : ℝ) (hy : y∈S) : iteratedDeriv 2 (Q y) (x y/M)=2*M^2*q/T := by
    calc
      _ = (2*M^2/T)*(iteratedDeriv 2 (f y) (x y)/2) := by
        rw [hd 2 _ _ (hMpos.trans_le (hpoints y hy).2.1) (Or.inr hy)]
        field_simp
      _ = _ := by rw [hmap y hy]; ring
  have hnear (y : ℝ) (hy : y∈S) : |G y (x y/M)-g| ≤ 24*U*(Δ+5/M) := by
    have hroundpos (z : ℝ) (hz : z∈Icc M (2*M)) : (0:ℝ) < round z := by
      have hh := abs_le.mp (abs_sub_round z)
      linarith only [hh.2,hz.1,hM]
    have hμ (y z : ℝ) (hy : y=ya ∨ y∈S) (hz : z∈Icc M (2*M)) :
        μ y z=(T/(6*M^3))*G y ((round z:ℝ)/M) := by
      dsimp only [μ]
      rw [hd 3 _ _ (hroundpos z hz) hy]
      dsimp only [G]
      ring
    have hthird' :
        |G y ((round (M*(x y/M)):ℝ)/M)/
          G ya ((round (M*(xa/M)):ℝ)/M)*t^3-1| ≤ Δ := by
      have he (z : ℝ) : M*(z/M)=z := mul_div_cancel₀ z hMpos.ne'
      rw [he,he]
      have hh := hthird y hy
      rw [hμ y _ (Or.inr hy) (hpoints y hy).2,hμ ya _ (Or.inl rfl) hxa,
        mul_div_mul_left _ _ (show T/(6*M^3) ≠ 0 by positivity)] at hh
      exact hh
    have hdG (v : ℝ) (hv : v=ya ∨ v∈S) (u : ℝ)
        (hu : u∈Icc (3/4:ℝ) (9/4)) :
        HasDerivAt (G v) (iteratedDeriv 4 (Q v) u) u := by
      simpa only [G,iteratedDeriv_succ] using
        ((contDiffAt_iteratedDeriv_infty (hreg v hv u (by linarith only [hu.1])) 3).differentiableAt
          (by simp)).hasDerivAt
    have hh := rounded_weighted_profile_bound (G ya) (G y)
      (iteratedDeriv 4 (Q ya)) (iteratedDeriv 4 (Q y))
      (hnorm _ hxa) (hnorm _ (hpoints y hy).2) hM (by positivity : 0 ≤ 3*U) hΔ
      (hdG ya (Or.inl rfl)) (hdG y (Or.inr hy))
      (fun u hu => (hjet ya (Or.inl rfl) u hu).2.2.2)
      (fun u hu => (hjet y (Or.inr hy) u hu).2.2.2)
      (fun u hu => ⟨(hjet ya (Or.inl rfl) u hu).2.2.1,
        ne_of_gt ((show 0 < c/2 by positivity).trans_le
          (hjet ya (Or.inl rfl) u hu).2.1)⟩) hthird'
    have htp : |t^3| ≤ 8 := by
      rw [abs_of_nonneg (pow_nonneg htpos.le 3)]
      exact (pow_le_pow_left₀ htpos.le ht.2 3).trans_eq (by norm_num)
    have hround : (|t^3|+1)/(2*M) ≤ 5/M := by
      apply (div_le_div_iff₀ (show 0 < 2*M by positivity) hMpos).mpr
      nlinarith only [htp,hMpos]
    have hb : |G y (x y/M)*t^3-G ya (xa/M)| ≤ 3*U*(Δ+5/M) :=
      hh.trans (mul_le_mul_of_nonneg_left (add_le_add le_rfl hround) (by positivity))
    have htl : (1/8:ℝ) ≤ t^3 := by
      convert pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 1/2) ht.1 3 using 1
      norm_num
    calc
      _ = |G y (x y/M)*t^3-G ya (xa/M)|/t^3 := by
        have he : G y (x y/M)-g=(G y (x y/M)*t^3-G ya (xa/M))/t^3 := by
          dsimp only [g]
          field_simp
        rw [he,abs_div,abs_of_pos (pow_pos htpos 3)]
      _ ≤ |G y (x y/M)*t^3-G ya (xa/M)|/(1/8) :=
        div_le_div_of_nonneg_left (abs_nonneg _) (by norm_num) htl
      _ ≤ (3*U*(Δ+5/M))/(1/8) := div_le_div_of_nonneg_right hb (by norm_num)
      _ = _ := by ring
  exact hcount F δ w (24*U*(Δ+5/M)) J (2*M^2*q/T) g S (fun y => x y/M) r s
    hf hlower
    (fun u hu => ⟨hbound u hu 4 (by norm_num) (by norm_num),
      hbound u hu 5 (by norm_num) (by norm_num),hbound u hu 6 (by norm_num) (by norm_num)⟩)
    hdet hδ hw hwcap hsmall (by positivity) hJ
    (fun y hy => ⟨(hpoints y hy).1,hnorm _ (hpoints y hy).2⟩) hsep
    (fun y hy => hshifts y (Or.inr hy)) hroots hnear

#print axioms double_difference_physical_parameter_count

example
    {c U : ℝ} (hc : 0 < c) (hU : 0 < U) :
    ∃ K C : ℝ, 0 < K ∧ 0 < C ∧
      ∀ (F : ℝ → ℝ) (δ w ya xa Δ J q t T M : ℝ)
        (S : Finset ℝ) (x r s : ℝ → ℝ),
        (∀ u, 0 < u → ContDiffAt ℝ ∞ F u) →
        (∀ u∈Icc (1/2:ℝ) 3, c ≤ iteratedDeriv 5 F u) →
        (∀ u∈Icc (1/2:ℝ) 3, ∀ n, 1 ≤ n → n ≤ 7 → |iteratedDeriv n F u| ≤ U) →
        (∀ u∈Icc (1/2:ℝ) 3,
          c ≤ |(iteratedDeriv 5 F u)^2-iteratedDeriv 4 F u*iteratedDeriv 6 F u|) →
        0 < δ → 0 ≤ w → w ≤ 1/4 → 2*U*w ≤ c/64 →
        ya∈Icc (1:ℝ) 2 → 0 < T → 2 ≤ M → 0 ≤ Δ → 0 < J →
        t∈Icc (1/2:ℝ) 2 → xa∈Icc M (2*M) →
        (∀ y∈S, y∈Icc (1:ℝ) 2 ∧ x y∈Icc M (2*M)) →
        (∀ y∈S, ∀ z∈S, y ≠ z → 1 ≤ J*|y-z|) →
        (∀ y, y=ya ∨ y∈S →
          0 ≤ r y ∧ 0 ≤ s y ∧ r y*s y=δ*y ∧ r y+s y ≤ w) →
        let Q := fun y u => (F u-F (u+r y)-F (u+s y)+F (u+r y+s y))/δ
        let f := fun y z => T*Q y (z/M)
        let μ := fun y z => iteratedDeriv 3 (f y) (round z)/6
        (∀ y∈S, iteratedDeriv 2 (f y) (x y)/2=q) →
        (∀ y∈S, |μ y (x y)/μ ya xa*t^3-1| ≤ Δ) →
        (S.card:ℝ) ≤ K*(1+C*(24*U*(Δ+5/M)+2*U*w+12*U^2*w/c)*J) :=
  @double_difference_physical_parameter_count c U hc hU

/-- A compact, source-only tolerance preserves the positive fifth
jet of the original phase; positivity is derived from the actual model. -/
private theorem modelPhase_positive_fifth_test {σ : ℝ} (hσ : 0 < σ) :
    ∃ ε c : ℝ, 0 < ε ∧ 0 < c ∧
      ∀ F : ℝ → ℝ,
        (∀ x∈Icc (1/2:ℝ) 3,
          |iteratedDeriv 5 F x-iteratedDeriv 4 (Expdb.modelPhase σ) x| ≤ ε) →
        ∀ x∈Icc (1/2:ℝ) 3, c ≤ iteratedDeriv 5 F x := by
  have hcont : ContinuousOn (iteratedDeriv 4 (Expdb.modelPhase σ)) (Icc (1/2:ℝ) 3) := by
    intro x hx
    exact (contDiffAt_iteratedDeriv_infty
      (Real.contDiffAt_rpow_const_of_ne (by linarith only [hx.1] : x ≠ 0)) 4).continuousAt.continuousWithinAt
  have hpos (x : ℝ) (hx : x∈Icc (1/2:ℝ) 3) :
      0 < iteratedDeriv 4 (Expdb.modelPhase σ) x := by
    have hxpos : 0 < x := by linarith only [hx.1]
    have hj : iteratedDeriv 4 (Expdb.modelPhase σ) x =
        (descPochhammer ℝ 4).eval (-σ)*x^(-σ-(4:ℝ)) := by
      rw [iteratedDeriv_eq_iterate]
      exact Real.iter_deriv_rpow_const (-σ) x 4
    have he : (descPochhammer ℝ 4).eval (-σ)=σ*(σ+1)*(σ+2)*(σ+3) := by
      norm_num [descPochhammer_eval_eq_prod_range,Finset.prod_range_succ]
      ring
    rw [hj,he]
    positivity
  obtain ⟨x₀,hx₀,hmin⟩ := isCompact_Icc.exists_isMinOn
    (show (Icc (1/2:ℝ) 3).Nonempty from ⟨1,by norm_num⟩) hcont
  let c := iteratedDeriv 4 (Expdb.modelPhase σ) x₀/2
  have hc : 0 < c := by dsimp only [c]; exact half_pos (hpos x₀ hx₀)
  refine ⟨c,c,hc,hc,?_⟩
  intro F herror x hx
  have hh := (abs_le.mp (herror x hx)).1
  have hlo : iteratedDeriv 4 (Expdb.modelPhase σ) x₀ ≤
      iteratedDeriv 4 (Expdb.modelPhase σ) x := hmin hx
  dsimp only [c] at hh ⊢
  linarith only [hh,hlo]

#print axioms modelPhase_positive_fifth_test

example {σ : ℝ} (hσ : 0 < σ) :
    ∃ ε c : ℝ, 0 < ε ∧ 0 < c ∧
      ∀ F : ℝ → ℝ,
        (∀ x∈Icc (1/2:ℝ) 3,
          |iteratedDeriv 5 F x-iteratedDeriv 4 (Expdb.modelPhase σ) x| ≤ ε) →
        ∀ x∈Icc (1/2:ℝ) 3, c ≤ iteratedDeriv 5 F x :=
  @modelPhase_positive_fifth_test σ hσ

/-- The original source phase supplies one common extension and all
analytic hypotheses of the physical selected-product count. Constants
are chosen before the physical scale, phase and shift selection. The
prescribed jet tolerance and every original sharp prefix are retained. -/
private theorem approximateModelPhase_enlarged_double_difference_count
    {σ ε : ℝ} (hσ : 0 < σ) (hε : 0 < ε) :
    ∃ δ₀ c U K C : ℝ,
      0 < δ₀ ∧ 0 < c ∧ 0 < U ∧ 0 < K ∧ 0 < C ∧
      ∀ (M : ℝ) (F : ℝ → ℝ), 1 ≤ M →
        IsApproximateModelPhaseFunction F σ 7 δ₀ →
      ∃ Fext : ℝ → ℝ,
        (∀ u, 0 < u → ContDiffAt ℝ ∞ Fext u) ∧
        (∀ u∈Icc (1/2:ℝ) 3, ∀ n≤6,
          |iteratedDeriv (n+1) Fext u-iteratedDeriv n (Expdb.modelPhase σ) u| ≤ ε) ∧
        (∀ u∈Icc (1/2:ℝ) 3, ∀ n, 1 ≤ n → n ≤ 7 → |iteratedDeriv n Fext u| ≤ U) ∧
        (∀ u∈Icc (1/2:ℝ) 3, c ≤ iteratedDeriv 5 Fext u) ∧
        (∀ u∈Icc (1/2:ℝ) 3, ∀ j,
          c ≤ |HuxleyModel.tests (fun i : Fin 4 => iteratedDeriv (i.val+3) Fext u) j|) ∧
        (∀ u∈Icc (1/2:ℝ) 3, iteratedDeriv 4 Fext u ≤ -c) ∧
        (∀ (T : ℝ) (a b : ℕ), M ≤ (a:ℝ) → (b:ℝ) ≤ 2*M →
          ‖exponentialSumAt F T M a b-exponentialSumAt Fext T M a b‖ ≤ 6) ∧
        ∀ (δ w ya xa Δ J q t T : ℝ) (S : Finset ℝ) (x r s : ℝ → ℝ),
          0 < δ → 0 ≤ w → w ≤ 1/4 → 2*U*w ≤ c/64 →
          ya∈Icc (1:ℝ) 2 → 0 < T → 2 ≤ M → 0 ≤ Δ → 0 < J →
          t∈Icc (1/2:ℝ) 2 → xa∈Icc M (2*M) →
          (∀ y∈S, y∈Icc (1:ℝ) 2 ∧ x y∈Icc M (2*M)) →
          (∀ y∈S, ∀ z∈S, y ≠ z → 1 ≤ J*|y-z|) →
          (∀ y, y=ya ∨ y∈S →
            0 ≤ r y ∧ 0 ≤ s y ∧ r y*s y=δ*y ∧ r y+s y ≤ w) →
          let Q := fun y u =>
            (Fext u-Fext (u+r y)-Fext (u+s y)+Fext (u+r y+s y))/δ
          let f := fun y z => T*Q y (z/M)
          let μ := fun y z => iteratedDeriv 3 (f y) (round z)/6
          (∀ y∈S, iteratedDeriv 2 (f y) (x y)/2=q) →
          (∀ y∈S, |μ y (x y)/μ ya xa*t^3-1| ≤ Δ) →
          (S.card:ℝ) ≤ K*(1+C*(24*U*(Δ+5/M)+2*U*w+12*U^2*w/c)*J) := by
  obtain ⟨e₀,c₀,U,he₀,hc₀,hU,htests⟩ :=
    HuxleyRationalPhase.modelPhase_compact_jet_signed_source_tests hσ
  obtain ⟨e₅,c₅,he₅,hc₅,hfifth⟩ := modelPhase_positive_fifth_test hσ
  obtain ⟨D,hD,hbuild⟩ := HuxleyRationalPhase.approximateModelPhase_enlarged_sharp_transport 6
  let e := min ε (min e₀ e₅)
  let δ₀ := e/D
  let c := min c₀ c₅
  have hc : 0 < c := lt_min hc₀ hc₅
  have hDpos : 0 < D := zero_lt_one.trans_le hD
  have he : 0 < e := lt_min hε (lt_min he₀ he₅)
  have hδ₀ : 0 < δ₀ := div_pos he hDpos
  have heq : D*δ₀=e := by dsimp only [δ₀]; field_simp
  have heε : e ≤ ε := min_le_left _ _
  have he₀' : e ≤ e₀ := (min_le_right _ _).trans (min_le_left _ _)
  have he₅' : e ≤ e₅ := (min_le_right _ _).trans (min_le_right _ _)
  obtain ⟨K,C,hK,hC,hcount⟩ := double_difference_physical_parameter_count hc hU
  refine ⟨δ₀,c,U,K,C,hδ₀,hc,hU,hK,hC,?_⟩
  intro M F hM hF
  obtain ⟨Fext,hreg,hjets,hsharp⟩ := hbuild σ δ₀ M F hδ₀.le hM hF
  have hj (u : ℝ) (hu : u∈Icc (1/2:ℝ) 3) (n : ℕ) (hn : n≤6) :
      |iteratedDeriv (n+1) Fext u-iteratedDeriv n (Expdb.modelPhase σ) u| ≤ e := by
    simpa only [heq] using hjets u hu n hn
  obtain ⟨hbound,htest,hnegative⟩ := htests Fext
    (fun u hu n hn => (hj u hu n hn).trans he₀')
  have hfive : ∀ u∈Icc (1/2:ℝ) 3, c ≤ iteratedDeriv 5 Fext u := by
    have hh := hfifth Fext (fun u hu => (hj u hu 4 (by norm_num)).trans he₅')
    exact fun u hu => (min_le_right c₀ c₅).trans (hh u hu)
  have hbound' : ∀ u∈Icc (1/2:ℝ) 3, ∀ n, 1 ≤ n → n ≤ 7 →
      |iteratedDeriv n Fext u| ≤ U := by
    intro u hu n hn hn'
    simpa only [Nat.sub_add_cancel hn] using hbound u hu (n-1) (by omega)
  have htest' : ∀ u∈Icc (1/2:ℝ) 3, ∀ j,
      c ≤ |HuxleyModel.tests (fun i : Fin 4 => iteratedDeriv (i.val+3) Fext u) j| :=
    fun u hu j => (min_le_left c₀ c₅).trans (htest u hu j)
  have hdet : ∀ u∈Icc (1/2:ℝ) 3,
      c ≤ |(iteratedDeriv 5 Fext u)^2-iteratedDeriv 4 Fext u*iteratedDeriv 6 Fext u| := by
    intro u hu
    have hh := htest' u hu (4:Fin 7)
    simpa [HuxleyModel.tests,abs_sub_comm] using hh
  refine ⟨Fext,hreg,fun u hu n hn => (hj u hu n hn).trans heε,
    hbound',hfive,htest',
    fun u hu => (hnegative u hu).trans (neg_le_neg (min_le_left c₀ c₅)),hsharp,?_⟩
  intro δ w ya xa Δ J q t T S x r s hδ hw hwcap hsmall hya hT hM₂ hΔ hJ
    ht hxa hpoints hsep hshifts
  exact hcount Fext δ w ya xa Δ J q t T M S x r s hreg hfive hbound' hdet hδ
    hw hwcap hsmall hya hT hM₂ hΔ hJ ht hxa hpoints hsep hshifts

#print axioms approximateModelPhase_enlarged_double_difference_count

example
    {σ ε : ℝ} (hσ : 0 < σ) (hε : 0 < ε) :
    ∃ δ₀ c U K C : ℝ,
      0 < δ₀ ∧ 0 < c ∧ 0 < U ∧ 0 < K ∧ 0 < C ∧
      ∀ (M : ℝ) (F : ℝ → ℝ), 1 ≤ M →
        IsApproximateModelPhaseFunction F σ 7 δ₀ →
      ∃ Fext : ℝ → ℝ,
        (∀ u, 0 < u → ContDiffAt ℝ ∞ Fext u) ∧
        (∀ u∈Icc (1/2:ℝ) 3, ∀ n≤6,
          |iteratedDeriv (n+1) Fext u-iteratedDeriv n (Expdb.modelPhase σ) u| ≤ ε) ∧
        (∀ u∈Icc (1/2:ℝ) 3, ∀ n, 1 ≤ n → n ≤ 7 → |iteratedDeriv n Fext u| ≤ U) ∧
        (∀ u∈Icc (1/2:ℝ) 3, c ≤ iteratedDeriv 5 Fext u) ∧
        (∀ u∈Icc (1/2:ℝ) 3, ∀ j,
          c ≤ |HuxleyModel.tests (fun i : Fin 4 => iteratedDeriv (i.val+3) Fext u) j|) ∧
        (∀ u∈Icc (1/2:ℝ) 3, iteratedDeriv 4 Fext u ≤ -c) ∧
        (∀ (T : ℝ) (a b : ℕ), M ≤ (a:ℝ) → (b:ℝ) ≤ 2*M →
          ‖exponentialSumAt F T M a b-exponentialSumAt Fext T M a b‖ ≤ 6) ∧
        ∀ (δ w ya xa Δ J q t T : ℝ) (S : Finset ℝ) (x r s : ℝ → ℝ),
          0 < δ → 0 ≤ w → w ≤ 1/4 → 2*U*w ≤ c/64 →
          ya∈Icc (1:ℝ) 2 → 0 < T → 2 ≤ M → 0 ≤ Δ → 0 < J →
          t∈Icc (1/2:ℝ) 2 → xa∈Icc M (2*M) →
          (∀ y∈S, y∈Icc (1:ℝ) 2 ∧ x y∈Icc M (2*M)) →
          (∀ y∈S, ∀ z∈S, y ≠ z → 1 ≤ J*|y-z|) →
          (∀ y, y=ya ∨ y∈S →
            0 ≤ r y ∧ 0 ≤ s y ∧ r y*s y=δ*y ∧ r y+s y ≤ w) →
          let Q := fun y u =>
            (Fext u-Fext (u+r y)-Fext (u+s y)+Fext (u+r y+s y))/δ
          let f := fun y z => T*Q y (z/M)
          let μ := fun y z => iteratedDeriv 3 (f y) (round z)/6
          (∀ y∈S, iteratedDeriv 2 (f y) (x y)/2=q) →
          (∀ y∈S, |μ y (x y)/μ ya xa*t^3-1| ≤ Δ) →
          (S.card:ℝ) ≤ K*(1+C*(24*U*(Δ+5/M)+2*U*w+12*U^2*w/c)*J) :=
  @approximateModelPhase_enlarged_double_difference_count σ ε hσ hε

/-- Positive actual cubic derivatives make the physical curvature
injective on the original closed interval. Local Sargos affine scaling
is reused; no root-identification premise is assumed. -/
private theorem physical_curvature_strictMono_of_cubic
    (Q : ℝ → ℝ) {c T M : ℝ} (hc : 0 < c) (hT : 0 < T) (hM : 0 < M)
    (hreg : ∀ u, 0 < u → ContDiffAt ℝ ∞ Q u)
    (hlower : ∀ u∈Icc (1:ℝ) 2, c ≤ iteratedDeriv 3 Q u) :
    StrictMonoOn (fun z => iteratedDeriv 2 (fun u => T*Q (u/M)) z/2)
      (Icc M (2*M)) := by
  let f := fun u => T*Q (u/M)
  have hnorm (z : ℝ) (hz : z∈Icc M (2*M)) : z/M∈Icc (1:ℝ) 2 :=
    ⟨(le_div_iff₀ hM).mpr (by simpa using hz.1),(div_le_iff₀ hM).mpr hz.2⟩
  have hd (z : ℝ) (hz : z∈Icc M (2*M)) :
      HasDerivAt (fun u => iteratedDeriv 2 f u/2) (iteratedDeriv 3 f z/2) z := by
    have hcf : ContDiffAt ℝ ∞ f z :=
      contDiffAt_const.mul ((hreg (z/M) (div_pos (hM.trans_le hz.1) hM)).comp z
        (contDiffAt_id.div_const M))
    have hh : HasDerivAt (iteratedDeriv 2 f) (iteratedDeriv 3 f z) z := by
      simpa only [iteratedDeriv_succ] using
        ((contDiffAt_iteratedDeriv_infty hcf 2).differentiableAt (by simp)).hasDerivAt
    exact hh.div_const 2
  apply strictMonoOn_of_hasDerivWithinAt_pos (convex_Icc _ _)
    (fun z hz => (hd z hz).continuousAt.continuousWithinAt)
    (fun z hz => (hd z (interior_subset hz)).hasDerivWithinAt)
  intro z hz
  have hz' := interior_subset hz
  have hzpos : 0 < z := hM.trans_le hz'.1
  have ha := sargos_iteratedDeriv_comp_affine_local (f:=Q)
    (l:=0) (r:=z+1) (c:=M⁻¹) (d:=0)
    (fun u hu => hreg _ (by
      simpa only [add_zero] using mul_pos (inv_pos.mpr hM) hu.1))
    (show z∈Ioo (0:ℝ) (z+1) from ⟨hzpos,by linarith⟩) 3
  have hid : iteratedDeriv 3 f z=T/M^3*iteratedDeriv 3 Q (z/M) := by
    change iteratedDeriv 3 (fun u => T*Q (u/M)) z=_
    rw [iteratedDeriv_const_mul_field]
    have he : (fun u => Q (u/M))=(fun u => Q (M⁻¹*u+0)) := by
      funext u
      congr 1
      ring
    rw [he,ha]
    simp only [add_zero,inv_pow]
    rw [show M⁻¹*z=z/M by ring]
    ring
  rw [hid]
  exact half_pos (mul_pos (div_pos hT (pow_pos hM 3))
    (hc.trans_le (hlower _ (hnorm z hz'))))

#print axioms physical_curvature_strictMono_of_cubic

example
    (Q : ℝ → ℝ) {c T M : ℝ} (hc : 0 < c) (hT : 0 < T) (hM : 0 < M)
    (hreg : ∀ u, 0 < u → ContDiffAt ℝ ∞ Q u)
    (hlower : ∀ u∈Icc (1:ℝ) 2, c ≤ iteratedDeriv 3 Q u) :
    StrictMonoOn (fun z => iteratedDeriv 2 (fun u => T*Q (u/M)) z/2)
      (Icc M (2*M)) :=
  @physical_curvature_strictMono_of_cubic Q c T M hc hT hM hreg hlower

/-- Literal original-grid and parity fibers over the same actual
double phase have multiplicity at most six. The existing integer-grid
argument is reused after deriving physical curvature injectivity. -/
private theorem double_difference_physical_family_fiber_count
    {c U : ℝ} (hc : 0 < c) (hU : 0 < U) :
    ∃ K C : ℝ, 0 < K ∧ 0 < C ∧
      ∀ (S : Finset ((ℝ × ℤ) × Fin 2)) (F : ℝ → ℝ) (r s : ℝ → ℝ)
        (z : ℝ → ℤ → ℝ) (Alen : ℝ → ℤ → ℕ) (N : ℕ) (Z : ℝ → ℤ)
        (δ w ya xa Δ J q t T M : ℝ),
        (∀ u, 0 < u → ContDiffAt ℝ ∞ F u) →
        (∀ u∈Icc (1/2:ℝ) 3, c ≤ iteratedDeriv 5 F u) →
        (∀ u∈Icc (1/2:ℝ) 3, ∀ n, 1 ≤ n → n ≤ 7 → |iteratedDeriv n F u| ≤ U) →
        (∀ u∈Icc (1/2:ℝ) 3,
          c ≤ |(iteratedDeriv 5 F u)^2-iteratedDeriv 4 F u*iteratedDeriv 6 F u|) →
        0 < δ → 0 ≤ w → w ≤ 1/4 → 2*U*w ≤ c/64 →
        ya∈Icc (1:ℝ) 2 → 0 < T → 2 ≤ M → 0 < N → 0 ≤ Δ → 0 < J →
        t∈Icc (1/2:ℝ) 2 → xa∈Icc M (2*M) →
        (∀ ip∈S, ip.1.1∈Icc (1:ℝ) 2 ∧ z ip.1.1 ip.1.2∈Icc M (2*M)) →
        (∀ ip∈S, N ≤ Alen ip.1.1 ip.1.2 ∧ Alen ip.1.1 ip.1.2 ≤ 3*N ∧
          round (z ip.1.1 ip.1.2)+(Alen ip.1.1 ip.1.2:ℤ)=
            Z ip.1.1+(N:ℤ)*ip.1.2+2*(N:ℤ)) →
        (∀ ip∈S, ∀ jp∈S, ip.1.1 ≠ jp.1.1 → 1 ≤ J*|ip.1.1-jp.1.1|) →
        (∀ y, y=ya ∨ y∈S.image (fun ip => ip.1.1) →
          0 ≤ r y ∧ 0 ≤ s y ∧ r y*s y=δ*y ∧ r y+s y ≤ w) →
        let Q := fun y u => (F u-F (u+r y)-F (u+s y)+F (u+r y+s y))/δ
        let f := fun y u => T*Q y (u/M)
        let h := fun y u => iteratedDeriv 2 (f y) u/2
        let μ := fun y u => iteratedDeriv 3 (f y) (round u)/6
        (∀ ip∈S, h ip.1.1 (z ip.1.1 ip.1.2)=q) →
        (∀ ip∈S, |μ ip.1.1 (z ip.1.1 ip.1.2)/μ ya xa*t^3-1| ≤ Δ) →
        (S.card:ℝ) ≤ 6*K*(1+C*(24*U*(Δ+5/M)+2*U*w+12*U^2*w/c)*J) := by
  obtain ⟨K,C,hK,hC,hcount⟩ := double_difference_physical_parameter_count hc hU
  refine ⟨K,C,hK,hC,?_⟩
  intro S F r s z Alen N Z δ w ya xa Δ J q t T M hf hlower hbound hdet
    hδ hw hwcap hsmall hya hT hM hN hΔ hJ ht hxa hpoints hgeometry hsep hshifts
    Q f h μ hlevel hthird
  classical
  have hNp : (0:ℝ) < N := by exact_mod_cast hN
  have hMp : 0 < M := by linarith only [hM]
  let Y := S.image (fun ip => ip.1.1)
  have hex y (hy : y∈Y) : ∃ ip, ip∈S ∧ ip.1.1=y := Finset.mem_image.mp hy
  let pick := fun y => if hy : y∈Y then Classical.choose (hex y hy) else ((y,0),0)
  have hpick y (hy : y∈Y) : pick y∈S ∧ (pick y).1.1=y := by
    dsimp only [pick]
    rw [dif_pos hy]
    exact Classical.choose_spec (hex y hy)
  let root := fun y => z y (pick y).1.2
  have hparams y (hy : y∈Y) : y∈Icc (1:ℝ) 2 ∧ root y∈Icc M (2*M) := by
    have hh := hpoints _ (hpick y hy).1
    rw [(hpick y hy).2] at hh
    exact hh
  have hY := hcount F δ w ya xa Δ J q t T M Y root r s hf hlower hbound hdet
    hδ hw hwcap hsmall hya hT hM hΔ hJ ht hxa hparams
    (by
      intro y hy y' hy' hne
      have hh := hsep _ (hpick y hy).1 _ (hpick y' hy').1
      rw [(hpick y hy).2,(hpick y' hy').2] at hh
      exact hh hne) hshifts
    (by
      intro y hy
      have hh := hlevel _ (hpick y hy).1
      rw [(hpick y hy).2] at hh
      exact hh)
    (by
      intro y hy
      have hh := hthird _ (hpick y hy).1
      rw [(hpick y hy).2] at hh
      exact hh)
  have hcard : S.card ≤ 6*Y.card := by
    apply Finset.card_le_mul_card_image S 6
    intro y hy
    let E := S.filter (fun ip => ip.1.1=y)
    let m : ℝ := round (root y)
    obtain ⟨I,hI,_hIlow,hIhigh⟩ := HuxleyRationalPhase.physical_grid_interval_card (Z:=(Z y:ℝ))
      (x:=m-(N:ℝ)) (z:=m+(N:ℝ)) hNp (by linarith only [hNp])
    have hIcard : I.card ≤ 3 := by
      have hh : (I.card:ℝ) ≤ 3 := hIhigh.trans_eq (by field_simp; ring)
      exact_mod_cast hh
    have hjet (u : ℝ) (hu : u∈Icc (3/4:ℝ) (9/4)) :=
      double_difference_cubic_jet_bounds F hu (hparams y hy).1
        (hshifts y (Or.inr hy)).1 (hshifts y (Or.inr hy)).2.1 hδ hU hc
        (hshifts y (Or.inr hy)).2.2.1 (hshifts y (Or.inr hy)).2.2.2
        hwcap hsmall hf hlower hbound
    have hmono := physical_curvature_strictMono_of_cubic (Q y)
      (show 0 < c/2 by positivity) hT hMp (hjet 1 (by norm_num)).1
      (fun u hu => (hjet u ⟨by linarith only [hu.1],by linarith only [hu.2]⟩).2.1)
    have hsame ip (hip : ip∈E) : z ip.1.1 ip.1.2=root y := by
      have hd := Finset.mem_filter.mp hip
      have hz := (hpoints ip hd.1).2
      have he := hlevel ip hd.1
      have hp := hlevel _ (hpick y hy).1
      rw [hd.2] at hz he ⊢
      rw [(hpick y hy).2] at hp
      exact hmono.injOn hz (hparams y hy).2 (he.trans hp.symm)
    have hfiber : E.card ≤ (I ×ˢ (Finset.univ : Finset (Fin 2))).card := by
      apply Finset.card_le_card_of_injOn (fun ip => (ip.1.2,ip.2))
      · intro ip hip
        refine Finset.mem_product.mpr ⟨?_,Finset.mem_univ _⟩
        apply (hI ip.1.2).mpr
        have hd := Finset.mem_filter.mp hip
        have hg := hgeometry ip hd.1
        have hlo : (N:ℝ) ≤ Alen ip.1.1 ip.1.2 := by exact_mod_cast hg.1
        have hhi : (Alen ip.1.1 ip.1.2:ℝ) ≤ 3*(N:ℝ) := by exact_mod_cast hg.2.1
        have he : (round (z ip.1.1 ip.1.2):ℝ)+(Alen ip.1.1 ip.1.2:ℝ)=
            (Z ip.1.1:ℝ)+(N:ℝ)*ip.1.2+2*(N:ℝ) := by exact_mod_cast hg.2.2
        rw [hsame ip hip,hd.2] at he
        change m+(Alen y ip.1.2:ℝ)=(Z y:ℝ)+(N:ℝ)*ip.1.2+2*(N:ℝ) at he
        rw [hd.2] at hlo hhi
        constructor <;> nlinarith only [he,hlo,hhi]
      · intro ip hip jp hjp he
        have hi := (Finset.mem_filter.mp hip).2
        have hj := (Finset.mem_filter.mp hjp).2
        have he1 : ip.1.2=jp.1.2 := congrArg (fun p : ℤ × Fin 2 => p.1) he
        have he2 : ip.2=jp.2 := congrArg (fun p : ℤ × Fin 2 => p.2) he
        exact Prod.ext (Prod.ext (hi.trans hj.symm) he1) he2
    have he : (I ×ˢ (Finset.univ : Finset (Fin 2))).card=I.card*2 := by
      simp only [Finset.card_product,Finset.card_univ,Fintype.card_fin]
    rw [he] at hfiber
    change E.card ≤ 6
    omega
  have hcardR : (S.card:ℝ) ≤ 6*(Y.card:ℝ) := by exact_mod_cast hcard
  have hh := hcardR.trans (mul_le_mul_of_nonneg_left hY (by norm_num : (0:ℝ) ≤ 6))
  convert hh using 1
  ring

#print axioms double_difference_physical_family_fiber_count

example
    {c U : ℝ} (hc : 0 < c) (hU : 0 < U) :
    ∃ K C : ℝ, 0 < K ∧ 0 < C ∧
      ∀ (S : Finset ((ℝ × ℤ) × Fin 2)) (F : ℝ → ℝ) (r s : ℝ → ℝ)
        (z : ℝ → ℤ → ℝ) (Alen : ℝ → ℤ → ℕ) (N : ℕ) (Z : ℝ → ℤ)
        (δ w ya xa Δ J q t T M : ℝ),
        (∀ u, 0 < u → ContDiffAt ℝ ∞ F u) →
        (∀ u∈Icc (1/2:ℝ) 3, c ≤ iteratedDeriv 5 F u) →
        (∀ u∈Icc (1/2:ℝ) 3, ∀ n, 1 ≤ n → n ≤ 7 → |iteratedDeriv n F u| ≤ U) →
        (∀ u∈Icc (1/2:ℝ) 3,
          c ≤ |(iteratedDeriv 5 F u)^2-iteratedDeriv 4 F u*iteratedDeriv 6 F u|) →
        0 < δ → 0 ≤ w → w ≤ 1/4 → 2*U*w ≤ c/64 →
        ya∈Icc (1:ℝ) 2 → 0 < T → 2 ≤ M → 0 < N → 0 ≤ Δ → 0 < J →
        t∈Icc (1/2:ℝ) 2 → xa∈Icc M (2*M) →
        (∀ ip∈S, ip.1.1∈Icc (1:ℝ) 2 ∧ z ip.1.1 ip.1.2∈Icc M (2*M)) →
        (∀ ip∈S, N ≤ Alen ip.1.1 ip.1.2 ∧ Alen ip.1.1 ip.1.2 ≤ 3*N ∧
          round (z ip.1.1 ip.1.2)+(Alen ip.1.1 ip.1.2:ℤ)=
            Z ip.1.1+(N:ℤ)*ip.1.2+2*(N:ℤ)) →
        (∀ ip∈S, ∀ jp∈S, ip.1.1 ≠ jp.1.1 → 1 ≤ J*|ip.1.1-jp.1.1|) →
        (∀ y, y=ya ∨ y∈S.image (fun ip => ip.1.1) →
          0 ≤ r y ∧ 0 ≤ s y ∧ r y*s y=δ*y ∧ r y+s y ≤ w) →
        let Q := fun y u => (F u-F (u+r y)-F (u+s y)+F (u+r y+s y))/δ
        let f := fun y u => T*Q y (u/M)
        let h := fun y u => iteratedDeriv 2 (f y) u/2
        let μ := fun y u => iteratedDeriv 3 (f y) (round u)/6
        (∀ ip∈S, h ip.1.1 (z ip.1.1 ip.1.2)=q) →
        (∀ ip∈S, |μ ip.1.1 (z ip.1.1 ip.1.2)/μ ya xa*t^3-1| ≤ Δ) →
        (S.card:ℝ) ≤ 6*K*(1+C*(24*U*(Δ+5/M)+2*U*w+12*U^2*w/c)*J) :=
  @double_difference_physical_family_fiber_count c U hc hU

/-- Two ordinary mean-value theorems give the actual product jet
at one interior point. This controls common-model errors using only the
source jets through order j+2, without adding an extra derivative bound. -/
private theorem double_difference_mean_value_jet
    (F : ℝ → ℝ) {x r s : ℝ} (j : ℕ) (hr : 0 < r) (hs : 0 < s)
    (hf : ∀ u∈Icc x (x+r+s), ContDiffAt ℝ ∞ F u) :
    ∃ v∈Ioo x (x+r+s),
      iteratedDeriv j (fun u => F u-F (u+r)-F (u+s)+F (u+r+s)) x =
        r*s*iteratedDeriv (j+2) F v := by
  let G := fun u => iteratedDeriv j F (u+s)-iteratedDeriv j F u
  have hd (n : ℕ) (u : ℝ) (hu : u∈Icc x (x+r+s)) :
      HasDerivAt (iteratedDeriv n F) (iteratedDeriv (n+1) F u) u := by
    simpa only [iteratedDeriv_succ] using
      ((contDiffAt_iteratedDeriv_infty (hf u hu) n).differentiableAt (by simp)).hasDerivAt
  have hdG (u : ℝ) (hu : u∈Icc x (x+r)) :
      HasDerivAt G (iteratedDeriv (j+1) F (u+s)-iteratedDeriv (j+1) F u) u := by
    have h₁ := (hd j (u+s) ⟨by linarith only [hu.1,hs],
      by linarith only [hu.2]⟩).comp u ((hasDerivAt_id u).add_const s)
    have h₀ := hd j u ⟨hu.1,by linarith only [hu.2,hs]⟩
    simpa only [mul_one,Function.comp_def] using h₁.sub h₀
  obtain ⟨u,hu,huEq⟩ := exists_hasDerivAt_eq_slope G
    (fun u => iteratedDeriv (j+1) F (u+s)-iteratedDeriv (j+1) F u)
    (by linarith only [hr] : x < x+r)
    (fun u hu => (hdG u hu).continuousAt.continuousWithinAt)
    (fun u hu => hdG u ⟨hu.1.le,hu.2.le⟩)
  have hsub : Icc u (u+s) ⊆ Icc x (x+r+s) := by
    intro v hv
    constructor <;> linarith only [hu.1,hu.2,hv.1,hv.2]
  obtain ⟨v,hv,hvEq⟩ := exists_hasDerivAt_eq_slope (iteratedDeriv (j+1) F)
    (iteratedDeriv (j+2) F) (by linarith only [hs] : u < u+s)
    (fun v hv => (hd (j+1) v (hsub hv)).continuousAt.continuousWithinAt)
    (fun v hv => hd (j+1) v (hsub ⟨hv.1.le,hv.2.le⟩))
  rw [show x+r-x=r by ring] at huEq
  rw [show u+s-u=s by ring] at hvEq
  have hfirst := (eq_div_iff hr.ne').mp huEq
  have hsecond := (eq_div_iff hs.ne').mp hvEq
  refine ⟨v,⟨hu.1.trans hv.1,by linarith only [hu.2,hv.2]⟩,?_⟩
  rw [double_difference_iterated_jet hr.le hs.le hf j]
  calc
    _ = r*(iteratedDeriv (j+1) F (u+s)-iteratedDeriv (j+1) F u) := by
      dsimp only [G] at hfirst
      linear_combination -hfirst
    _ = r*(iteratedDeriv (j+2) F v*s) := by rw [hsecond]
    _ = _ := by ring

#print axioms double_difference_mean_value_jet

example
    (F : ℝ → ℝ) {x r s : ℝ} (j : ℕ) (hr : 0 < r) (hs : 0 < s)
    (hf : ∀ u∈Icc x (x+r+s), ContDiffAt ℝ ∞ F u) :
    ∃ v∈Ioo x (x+r+s),
      iteratedDeriv j (fun u => F u-F (u+r)-F (u+s)+F (u+r+s)) x =
        r*s*iteratedDeriv (j+2) F v :=
  @double_difference_mean_value_jet F x r s j hr hs hf

/-- One common normalization for nearby product parameters, on the
literal uncompressed original coordinate. The closed model predicate
is proved from source jets only through P+3 using actual mean-value points. -/
private theorem double_difference_common_model
    {σ : ℝ} (hσ : 0 < σ) (P : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ (F : ℝ → ℝ) (e d r s y y₀ : ℝ),
        0 ≤ e → 0 < d → 0 < r → 0 < s → r+s ≤ 1/4 →
        y∈Icc (1:ℝ) 2 → y₀∈Icc (1:ℝ) 2 → r*s=d*y →
        (∀ u, 0 < u → ContDiffAt ℝ ∞ F u) →
        (∀ u∈Icc (1/2:ℝ) 3, ∀ p≤P+2,
          |iteratedDeriv (p+1) F u-iteratedDeriv p (Expdb.modelPhase σ) u| ≤ e) →
        IsApproximateModelPhaseFunction
          (fun u => (F u-F (u+r)-F (u+s)+F (u+r+s))/(σ*(σ+1)*d*y₀))
          (σ+2) P (C*(e+r+s+|y-y₀|)) := by
  classical
  choose B hB hLip using fun j : Fin (P+1) =>
    iteratedDeriv_modelPhase_positive_compact_lipschitz
      (r:=3) (show (0:ℝ)<1/2 by norm_num) (σ+2) j.val
  let V := ∑ j : Fin (P+1), B j
  let J := ∑ j : Fin (P+1), modelPhaseJetCoefficient (σ+2) j.val
  let A := σ*(σ+1)
  have hA : 0 < A := by dsimp only [A]; positivity
  have hV : 0 ≤ V := Finset.sum_nonneg (fun j _ => zero_le_one.trans (hB j))
  have hJ : 0 ≤ J := Finset.sum_nonneg (fun j _ => modelPhaseJetCoefficient_nonneg _ _)
  let C := max 1 (max (2/A) (max (2*V) J))
  have hCe : 2/A ≤ C := (le_max_left _ _).trans (le_max_right _ _)
  have hCw : 2*V ≤ C := (le_max_left _ _).trans
    ((le_max_right _ _).trans (le_max_right _ _))
  have hCy : J ≤ C := (le_max_right _ _).trans
    ((le_max_right _ _).trans (le_max_right _ _))
  refine ⟨C,le_max_left _ _,?_⟩
  intro F e d r s y y₀ he hd hr hs hw hy hy₀ hprod hf hjets
  have hypos : 0 < y := zero_lt_one.trans_le hy.1
  have hy₀pos : 0 < y₀ := zero_lt_one.trans_le hy₀.1
  apply approximateModelPhase_of_interior_bounds
  · intro u hu
    have hupos : 0 < u := zero_lt_one.trans_le hu.1
    exact (((((hf u hupos).sub ((hf (u+r) (by positivity)).comp u
      (contDiffAt_id.add contDiffAt_const))).sub
        ((hf (u+s) (by positivity)).comp u (contDiffAt_id.add contDiffAt_const))).add
          ((hf (u+r+s) (by positivity)).comp u
            ((contDiffAt_id.add contDiffAt_const).add contDiffAt_const))).div_const
              (σ*(σ+1)*d*y₀)).contDiffWithinAt
  · intro u hu p hp
    let R := iteratedDeriv p (Expdb.modelPhase (σ+2)) u
    have hupos : 0 < u := zero_lt_one.trans hu.1
    have hwide (v : ℝ) (hv : v∈Icc u (u+r+s)) : v∈Icc (1/2:ℝ) 3 := by
      constructor <;> linarith only [hv.1,hv.2,hu.1,hu.2,hw]
    have huwide : u∈Icc (1/2:ℝ) 3 :=
      ⟨by linarith only [hu.1],by linarith only [hu.2]⟩
    obtain ⟨v,hv,hmean⟩ := double_difference_mean_value_jet F (p+1) hr hs
      (fun v hv => hf v (hupos.trans_le hv.1))
    have hvwide := hwide v ⟨hv.1.le,hv.2.le⟩
    have hvpos : 0 < v := hupos.trans hv.1
    have hBp : B ⟨p,by omega⟩ ≤ V :=
      Finset.single_le_sum (fun j _ => zero_le_one.trans (hB j)) (Finset.mem_univ _)
    have hJp : modelPhaseJetCoefficient (σ+2) p ≤ J :=
      Finset.single_le_sum (fun j _ => modelPhaseJetCoefficient_nonneg (σ+2) j.val)
        (Finset.mem_univ (⟨p,by omega⟩ : Fin (P+1)))
    have hmodel :
        iteratedDeriv (p+2) (Expdb.modelPhase σ) v =
          A*iteratedDeriv p (Expdb.modelPhase (σ+2)) v := by
      rw [show p+2=(p+1)+1 by omega,modelPhase_iteratedDeriv_succ_parameter σ hvpos (p+1),
        modelPhase_iteratedDeriv_succ_parameter (σ+1) hvpos p,
        show σ+1+1=σ+2 by ring]
      dsimp only [A]
      ring
    have herr : |iteratedDeriv (p+3) F v-A*R| ≤ e+A*V*(r+s) := by
      have hsrc := hjets v hvwide (p+2) (by omega)
      rw [hmodel] at hsrc
      have hlip : |iteratedDeriv p (Expdb.modelPhase (σ+2)) v-R| ≤ V*(r+s) := by
        have hh := hLip ⟨p,by omega⟩ v hvwide u huwide
        have hdist : |v-u| ≤ r+s := by
          rw [abs_of_pos (sub_pos.mpr hv.1)]
          linarith only [hv.2]
        exact hh.trans (mul_le_mul hBp hdist (abs_nonneg _) hV)
      calc
        _ = |(iteratedDeriv (p+3) F v-A*iteratedDeriv p (Expdb.modelPhase (σ+2)) v)+
          A*(iteratedDeriv p (Expdb.modelPhase (σ+2)) v-R)| := by congr 1; ring
        _ ≤ |iteratedDeriv (p+3) F v-A*iteratedDeriv p (Expdb.modelPhase (σ+2)) v|+
          |A*(iteratedDeriv p (Expdb.modelPhase (σ+2)) v-R)| := abs_add_le _ _
        _ ≤ e+A*(V*(r+s)) := by
          rw [abs_mul,abs_of_pos hA]
          exact add_le_add hsrc (mul_le_mul_of_nonneg_left hlip hA.le)
        _ = _ := by ring
    have hratio : y/y₀ ≤ 2 := (div_le_iff₀ hy₀pos).mpr (by linarith only [hy.2,hy₀.1])
    have hquot :
        |r*s*iteratedDeriv (p+3) F v/(A*d*y₀)-(y/y₀)*R| ≤
          (e/A+V*(r+s))*(y/y₀) := by
      have heq : r*s*iteratedDeriv (p+3) F v/(A*d*y₀)-(y/y₀)*R =
          (y/y₀)*(iteratedDeriv (p+3) F v-A*R)/A := by
        rw [hprod]
        field_simp
      rw [heq,abs_div,abs_mul,abs_of_pos hA,abs_of_pos (div_pos hypos hy₀pos)]
      have hh := div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left herr (div_nonneg hypos.le hy₀pos.le)) hA.le
      convert hh using 1
      field_simp
    have hquot' :
        |r*s*iteratedDeriv (p+3) F v/(A*d*y₀)-(y/y₀)*R| ≤ 2*e/A+2*V*(r+s) := by
      apply hquot.trans
      have hh := mul_le_mul_of_nonneg_left hratio
        (show 0 ≤ e/A+V*(r+s) by positivity)
      convert hh using 1
      ring
    have hR : |R| ≤ J :=
      (iteratedDeriv_modelPhase_abs_le (show 0 ≤ σ+2 by linarith only [hσ]) hu p).trans hJp
    have hamp : |(y/y₀)*R-R| ≤ J*|y-y₀| := by
      rw [show (y/y₀)*R-R=((y-y₀)/y₀)*R by field_simp,
        abs_mul,abs_div,abs_of_pos hy₀pos]
      calc
        _ ≤ |y-y₀| * J := mul_le_mul
          (div_le_self (abs_nonneg _) hy₀.1) hR (abs_nonneg _) (abs_nonneg _)
        _ = _ := by ring
    rw [iteratedDeriv_div_const,hmean]
    change |r*s*iteratedDeriv (p+3) F v/(A*d*y₀)-R| ≤ _
    calc
      _ ≤ |r*s*iteratedDeriv (p+3) F v/(A*d*y₀)-(y/y₀)*R|+|(y/y₀)*R-R| :=
        abs_sub_le _ _ _
      _ ≤ 2*e/A+2*V*(r+s)+J*|y-y₀| := add_le_add hquot' hamp
      _ ≤ C*e+C*(r+s)+C*|y-y₀| := by
        rw [show 2*e/A=(2/A)*e by ring]
        exact add_le_add (add_le_add
          (mul_le_mul_of_nonneg_right hCe he)
          (mul_le_mul_of_nonneg_right hCw (by positivity)))
          (mul_le_mul_of_nonneg_right hCy (abs_nonneg _))
      _ = _ := by ring

#print axioms double_difference_common_model

example
    {σ : ℝ} (hσ : 0 < σ) (P : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ (F : ℝ → ℝ) (e d r s y y₀ : ℝ),
        0 ≤ e → 0 < d → 0 < r → 0 < s → r+s ≤ 1/4 →
        y∈Icc (1:ℝ) 2 → y₀∈Icc (1:ℝ) 2 → r*s=d*y →
        (∀ u, 0 < u → ContDiffAt ℝ ∞ F u) →
        (∀ u∈Icc (1/2:ℝ) 3, ∀ p≤P+2,
          |iteratedDeriv (p+1) F u-iteratedDeriv p (Expdb.modelPhase σ) u| ≤ e) →
        IsApproximateModelPhaseFunction
          (fun u => (F u-F (u+r)-F (u+s)+F (u+r+s))/(σ*(σ+1)*d*y₀))
          (σ+2) P (C*(e+r+s+|y-y₀|)) :=
  @double_difference_common_model σ hσ P

/-- The source budgets J<=M and J*w<=1 absorb BOTH rounding and
actual shift errors into one source-only constant. This is a consumer
of the literal grid count, not a supplied Type-I counting certificate. -/
private theorem double_difference_physical_family_fiber_source_scale
    {c U : ℝ} (hc : 0 < c) (hU : 0 < U) :
    ∃ D : ℝ, 0 < D ∧
      ∀ (S : Finset ((ℝ × ℤ) × Fin 2)) (F : ℝ → ℝ) (r s : ℝ → ℝ)
        (z : ℝ → ℤ → ℝ) (Alen : ℝ → ℤ → ℕ) (N : ℕ) (Z : ℝ → ℤ)
        (δ w ya xa Δ J q t T M : ℝ),
        (∀ u, 0 < u → ContDiffAt ℝ ∞ F u) →
        (∀ u∈Icc (1/2:ℝ) 3, c ≤ iteratedDeriv 5 F u) →
        (∀ u∈Icc (1/2:ℝ) 3, ∀ n, 1 ≤ n → n ≤ 7 → |iteratedDeriv n F u| ≤ U) →
        (∀ u∈Icc (1/2:ℝ) 3,
          c ≤ |(iteratedDeriv 5 F u)^2-iteratedDeriv 4 F u*iteratedDeriv 6 F u|) →
        0 < δ → 0 ≤ w → w ≤ 1/4 → 2*U*w ≤ c/64 →
        ya∈Icc (1:ℝ) 2 → 0 < T → 2 ≤ M → 0 < N → 0 ≤ Δ → 0 < J → J ≤ M → w*J ≤ 1 →
        t∈Icc (1/2:ℝ) 2 → xa∈Icc M (2*M) →
        (∀ ip∈S, ip.1.1∈Icc (1:ℝ) 2 ∧ z ip.1.1 ip.1.2∈Icc M (2*M)) →
        (∀ ip∈S, N ≤ Alen ip.1.1 ip.1.2 ∧ Alen ip.1.1 ip.1.2 ≤ 3*N ∧
          round (z ip.1.1 ip.1.2)+(Alen ip.1.1 ip.1.2:ℤ)=
            Z ip.1.1+(N:ℤ)*ip.1.2+2*(N:ℤ)) →
        (∀ ip∈S, ∀ jp∈S, ip.1.1 ≠ jp.1.1 → 1 ≤ J*|ip.1.1-jp.1.1|) →
        (∀ y, y=ya ∨ y∈S.image (fun ip => ip.1.1) →
          0 ≤ r y ∧ 0 ≤ s y ∧ r y*s y=δ*y ∧ r y+s y ≤ w) →
        let Q := fun y u => (F u-F (u+r y)-F (u+s y)+F (u+r y+s y))/δ
        let f := fun y u => T*Q y (u/M)
        let h := fun y u => iteratedDeriv 2 (f y) u/2
        let μ := fun y u => iteratedDeriv 3 (f y) (round u)/6
        (∀ ip∈S, h ip.1.1 (z ip.1.1 ip.1.2)=q) →
        (∀ ip∈S, |μ ip.1.1 (z ip.1.1 ip.1.2)/μ ya xa*t^3-1| ≤ Δ) →
        (S.card:ℝ) ≤ D*(1+Δ*J) := by
  obtain ⟨K,C,hK,hC,hcount⟩ := double_difference_physical_family_fiber_count hc hU
  let B := 2*U+12*U^2/c
  let A := 1+C*(144*U+B)
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  have hA : 0 < A := by dsimp only [A]; positivity
  refine ⟨6*K*A,by positivity,?_⟩
  intro S F r s z Alen N Z δ w ya xa Δ J q t T M hf hlower hbound hdet
    hδ hw hwcap hsmall hya hT hM hN hΔ hJ hJM hwJ ht hxa hpoints hgeometry hsep
    hshifts Q f h μ hlevel hthird
  have hh := hcount S F r s z Alen N Z δ w ya xa Δ J q t T M hf hlower hbound hdet
    hδ hw hwcap hsmall hya hT hM hN hΔ hJ ht hxa hpoints hgeometry hsep hshifts
    hlevel hthird
  have hMp : 0 < M := by linarith only [hM]
  have hratio : J/M ≤ 1 := (div_le_iff₀ hMp).mpr (by simpa using hJM)
  have hbudget :
      (24*U*(Δ+5/M)+2*U*w+12*U^2*w/c)*J ≤ 24*U*(Δ*J)+120*U+B := by
    calc
      _ = 24*U*(Δ*J)+120*U*(J/M)+B*(w*J) := by dsimp only [B]; ring
      _ ≤ 24*U*(Δ*J)+120*U*1+B*1 :=
        add_le_add (add_le_add le_rfl (mul_le_mul_of_nonneg_left hratio (by positivity)))
          (mul_le_mul_of_nonneg_left hwJ hB)
      _ = _ := by ring
  have ha₀ : 1+C*(120*U+B) ≤ A := by
    dsimp only [A]
    nlinarith only [mul_nonneg hC.le hU.le]
  have ha₁ : 24*C*U ≤ A := by
    dsimp only [A]
    nlinarith only [mul_nonneg hC.le hU.le,mul_nonneg hC.le hB]
  have htotal :
      1+C*(24*U*(Δ+5/M)+2*U*w+12*U^2*w/c)*J ≤ A*(1+Δ*J) := by
    calc
      _ = 1+C*((24*U*(Δ+5/M)+2*U*w+12*U^2*w/c)*J) := by ring
      _ ≤ 1+C*(24*U*(Δ*J)+120*U+B) :=
        add_le_add le_rfl (mul_le_mul_of_nonneg_left hbudget hC.le)
      _ = (1+C*(120*U+B))+(24*C*U)*(Δ*J) := by ring
      _ ≤ A+A*(Δ*J) := add_le_add ha₀
        (mul_le_mul_of_nonneg_right ha₁ (mul_nonneg hΔ hJ.le))
      _ = _ := by ring
  exact hh.trans (by
    calc
      _ ≤ (6*K)*(A*(1+Δ*J)) := mul_le_mul_of_nonneg_left htotal (by positivity)
      _ = _ := by ring)

#print axioms double_difference_physical_family_fiber_source_scale

example
    {c U : ℝ} (hc : 0 < c) (hU : 0 < U) :
    ∃ D : ℝ, 0 < D ∧
      ∀ (S : Finset ((ℝ × ℤ) × Fin 2)) (F : ℝ → ℝ) (r s : ℝ → ℝ)
        (z : ℝ → ℤ → ℝ) (Alen : ℝ → ℤ → ℕ) (N : ℕ) (Z : ℝ → ℤ)
        (δ w ya xa Δ J q t T M : ℝ),
        (∀ u, 0 < u → ContDiffAt ℝ ∞ F u) →
        (∀ u∈Icc (1/2:ℝ) 3, c ≤ iteratedDeriv 5 F u) →
        (∀ u∈Icc (1/2:ℝ) 3, ∀ n, 1 ≤ n → n ≤ 7 → |iteratedDeriv n F u| ≤ U) →
        (∀ u∈Icc (1/2:ℝ) 3,
          c ≤ |(iteratedDeriv 5 F u)^2-iteratedDeriv 4 F u*iteratedDeriv 6 F u|) →
        0 < δ → 0 ≤ w → w ≤ 1/4 → 2*U*w ≤ c/64 →
        ya∈Icc (1:ℝ) 2 → 0 < T → 2 ≤ M → 0 < N → 0 ≤ Δ → 0 < J → J ≤ M → w*J ≤ 1 →
        t∈Icc (1/2:ℝ) 2 → xa∈Icc M (2*M) →
        (∀ ip∈S, ip.1.1∈Icc (1:ℝ) 2 ∧ z ip.1.1 ip.1.2∈Icc M (2*M)) →
        (∀ ip∈S, N ≤ Alen ip.1.1 ip.1.2 ∧ Alen ip.1.1 ip.1.2 ≤ 3*N ∧
          round (z ip.1.1 ip.1.2)+(Alen ip.1.1 ip.1.2:ℤ)=
            Z ip.1.1+(N:ℤ)*ip.1.2+2*(N:ℤ)) →
        (∀ ip∈S, ∀ jp∈S, ip.1.1 ≠ jp.1.1 → 1 ≤ J*|ip.1.1-jp.1.1|) →
        (∀ y, y=ya ∨ y∈S.image (fun ip => ip.1.1) →
          0 ≤ r y ∧ 0 ≤ s y ∧ r y*s y=δ*y ∧ r y+s y ≤ w) →
        let Q := fun y u => (F u-F (u+r y)-F (u+s y)+F (u+r y+s y))/δ
        let f := fun y u => T*Q y (u/M)
        let h := fun y u => iteratedDeriv 2 (f y) u/2
        let μ := fun y u => iteratedDeriv 3 (f y) (round u)/6
        (∀ ip∈S, h ip.1.1 (z ip.1.1 ip.1.2)=q) →
        (∀ ip∈S, |μ ip.1.1 (z ip.1.1 ip.1.2)/μ ya xa*t^3-1| ≤ Δ) →
        (S.card:ℝ) ≤ D*(1+Δ*J) :=
  @double_difference_physical_family_fiber_source_scale c U hc hU

/-- A finite source-uniform coloring of the ACTUAL selected products
constructs a common model per color and retains the full complex sum's
twelfth-power loss. The physical phase identity uses the same chosen center. -/
private theorem double_difference_colored_common_models
    {σ ε : ℝ} (hσ : 0 < σ) (P : ℕ) (hε : 0 < ε) :
    ∃ e w₀ a : ℝ, 0 < e ∧ 0 < w₀ ∧ w₀ ≤ 1/4 ∧ 0 < a ∧
      ∀ (F : ℝ → ℝ),
        (∀ u, 0 < u → ContDiffAt ℝ ∞ F u) →
        (∀ u∈Icc (1/2:ℝ) 3, ∀ p≤P+2,
          |iteratedDeriv (p+1) F u-iteratedDeriv p (Expdb.modelPhase σ) u| ≤ e) →
        ∀ {ι : Type*} (S : Finset ι) (y r s : ι → ℝ) (d : ℝ),
          0 < d →
          (∀ i∈S, y i∈Icc (1:ℝ) 2) →
          (∀ i∈S, 0 < r i ∧ 0 < s i ∧ r i+s i ≤ w₀ ∧ r i*s i=d*y i) →
          let color := fun i => ⌊y i/a⌋
          let Cap := 4/a+3
          ((S.image color).card:ℝ) ≤ Cap ∧
          (∀ z : ι → ℂ, ‖∑ i∈S,z i‖^12 ≤
            Cap^11*∑ j∈S.image color, ‖∑ i∈S.filter (fun i => color i=j),z i‖^12) ∧
          ∀ j∈S.image color, ∃ i₀∈S, color i₀=j ∧
            ∀ i∈S, color i=j →
              let G := fun u =>
                (F u-F (u+r i)-F (u+s i)+F (u+r i+s i))/(σ*(σ+1)*d*y i₀)
              IsApproximateModelPhaseFunction G (σ+2) P ε ∧
              ∀ T M A x : ℝ,
                heathBrownPhysicalPhase G (T*σ*(σ+1)*y i₀) M A 1 x =
                  T*(F ((A+x)/M)-F ((A+x)/M+r i)-F ((A+x)/M+s i)+
                    F ((A+x)/M+r i+s i))/d := by
  classical
  obtain ⟨C,hC,hmodel⟩ := double_difference_common_model hσ P
  have hCpos : 0 < C := zero_lt_one.trans_le hC
  let a := ε/(3*C)
  have ha : 0 < a := by dsimp only [a]; positivity
  refine ⟨a,min (1/4:ℝ) a,a,ha,lt_min (by norm_num) ha,min_le_left _ _,ha,?_⟩
  intro F hf hjets ι S y r s d hd hy hshifts color Cap
  have hcard : ((S.image color).card:ℝ) ≤ Cap := by
    have hh := HuxleyRationalPhase.scaled_floor_image_card (Q:=1) (δ:=a) (R:=2) S y
      (by norm_num) ha (by norm_num)
      (by
        intro i hi
        rw [abs_of_pos (zero_lt_one.trans_le (hy i hi).1)]
        simpa only [mul_one] using (hy i hi).2)
    simpa only [mul_one,show (2:ℝ)*2=4 by norm_num] using hh
  refine ⟨hcard,?_,?_⟩
  · intro z
    let J := S.image color
    let V := fun j => S.filter (fun i => color i=j)
    let g := fun j => ∑ i∈V j,z i
    have he : (∑ j∈J,g j)=∑ i∈S,z i :=
      Finset.sum_fiberwise_of_maps_to (fun i hi => Finset.mem_image_of_mem color hi) z
    have hnorm : ‖∑ i∈S,z i‖ ≤ ∑ j∈J,‖g j‖ := by
      rw [←he]
      exact norm_sum_le _ _
    have hp := pow_le_pow_left₀ (norm_nonneg _) hnorm 12
    have hholder := Real.rpow_sum_le_const_mul_sum_rpow_of_nonneg J
      (f:=fun j => ‖g j‖) (p:=(12:ℝ)) (by norm_num) (fun _ _ => norm_nonneg _)
    have hh : (∑ j∈J,‖g j‖)^12 ≤ (J.card:ℝ)^11*∑ j∈J,‖g j‖^12 := by
      simpa only [show (12:ℝ)-1=11 by norm_num,Real.rpow_ofNat] using hholder
    exact (hp.trans hh).trans (mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ (by positivity : (0:ℝ) ≤ J.card) hcard 11)
      (Finset.sum_nonneg (fun _ _ => pow_nonneg (norm_nonneg _) _)))
  · intro j hj
    obtain ⟨i₀,hi₀,hcol₀⟩ := Finset.mem_image.mp hj
    refine ⟨i₀,hi₀,hcol₀,?_⟩
    intro i hi hcol G
    have hbin : ⌊y i/a⌋=⌊y i₀/a⌋ := hcol.trans hcol₀.symm
    have hh := Int.abs_sub_lt_one_of_floor_eq_floor hbin
    rw [←sub_div,abs_div,abs_of_pos ha] at hh
    have hnear : |y i-y i₀| ≤ a :=
      (by simpa only [one_mul] using ((div_lt_iff₀ ha).mp hh).le)
    have hshift : r i+s i ≤ a := (hshifts i hi).2.2.1.trans (min_le_right _ _)
    have hm := hmodel F a d (r i) (s i) (y i) (y i₀) ha.le hd
      (hshifts i hi).1 (hshifts i hi).2.1
      ((hshifts i hi).2.2.1.trans (min_le_left _ _))
      (hy i hi) (hy i₀ hi₀) (hshifts i hi).2.2.2 hf hjets
    have htol : C*(a+r i+s i+|y i-y i₀|) ≤ ε := by
      have hh' := mul_le_mul_of_nonneg_left
        (show a+r i+s i+|y i-y i₀| ≤ 3*a by linarith only [hshift,hnear]) hCpos.le
      have he : C*(3*a)=ε := by dsimp only [a]; field_simp
      exact hh'.trans_eq he
    refine ⟨approximateModelPhase_mono hm le_rfl htol,?_⟩
    intro T M A x
    have hy₀pos : 0 < y i₀ := zero_lt_one.trans_le (hy i₀ hi₀).1
    have hσ₁ : σ+1 ≠ 0 := by linarith only [hσ]
    dsimp only [G,heathBrownPhysicalPhase]
    field_simp

#print axioms double_difference_colored_common_models

example
    {σ ε : ℝ} (hσ : 0 < σ) (P : ℕ) (hε : 0 < ε) :
    ∃ e w₀ a : ℝ, 0 < e ∧ 0 < w₀ ∧ w₀ ≤ 1/4 ∧ 0 < a ∧
      ∀ (F : ℝ → ℝ),
        (∀ u, 0 < u → ContDiffAt ℝ ∞ F u) →
        (∀ u∈Icc (1/2:ℝ) 3, ∀ p≤P+2,
          |iteratedDeriv (p+1) F u-iteratedDeriv p (Expdb.modelPhase σ) u| ≤ e) →
        ∀ {ι : Type*} (S : Finset ι) (y r s : ι → ℝ) (d : ℝ),
          0 < d →
          (∀ i∈S, y i∈Icc (1:ℝ) 2) →
          (∀ i∈S, 0 < r i ∧ 0 < s i ∧ r i+s i ≤ w₀ ∧ r i*s i=d*y i) →
          let color := fun i => ⌊y i/a⌋
          let Cap := 4/a+3
          ((S.image color).card:ℝ) ≤ Cap ∧
          (∀ z : ι → ℂ, ‖∑ i∈S,z i‖^12 ≤
            Cap^11*∑ j∈S.image color, ‖∑ i∈S.filter (fun i => color i=j),z i‖^12) ∧
          ∀ j∈S.image color, ∃ i₀∈S, color i₀=j ∧
            ∀ i∈S, color i=j →
              let G := fun u =>
                (F u-F (u+r i)-F (u+s i)+F (u+r i+s i))/(σ*(σ+1)*d*y i₀)
              IsApproximateModelPhaseFunction G (σ+2) P ε ∧
              ∀ T M A x : ℝ,
                heathBrownPhysicalPhase G (T*σ*(σ+1)*y i₀) M A 1 x =
                  T*(F ((A+x)/M)-F ((A+x)/M+r i)-F ((A+x)/M+s i)+
                    F ((A+x)/M+r i+s i))/d :=
  @double_difference_colored_common_models σ ε hσ P hε

/-- The actual double-phase curvature has a fixed negative band.
The common source fourth derivative and the actual mean-value point
supply both bounds, without a curvature-band premise. -/
private theorem double_difference_exact_curvature_band
    (F : ℝ → ℝ) {x r s d y c U : ℝ}
    (hx : x∈Icc (3/4:ℝ) (9/4)) (hy : y∈Icc (1:ℝ) 2)
    (hr : 0 < r) (hs : 0 < s) (hd : 0 < d) (hc : 0 < c) (hU : 0 < U)
    (hprod : r*s=d*y) (hshift : r+s ≤ 1/4)
    (hf : ∀ u, 0 < u → ContDiffAt ℝ ∞ F u)
    (hneg : ∀ u∈Icc (1/2:ℝ) 3, iteratedDeriv 4 F u ≤ -c)
    (hbound : ∀ u∈Icc (1/2:ℝ) 3, |iteratedDeriv 4 F u| ≤ U) :
    let Q := fun u => (F u-F (u+r)-F (u+s)+F (u+r+s))/d;
    -2*U ≤ iteratedDeriv 2 Q x ∧ iteratedDeriv 2 Q x ≤ -c := by
  intro Q
  have hxpos : 0 < x := by linarith only [hx.1]
  obtain ⟨v,hv,hmean⟩ := double_difference_mean_value_jet F 2 hr hs
    (fun u hu => hf u (hxpos.trans_le hu.1))
  have hvwide : v∈Icc (1/2:ℝ) 3 := by
    constructor <;> linarith only [hv.1,hv.2,hx.1,hx.2,hshift]
  have heq : iteratedDeriv 2 Q x=y*iteratedDeriv 4 F v := by
    dsimp only [Q]
    rw [iteratedDeriv_div_const,hmean,hprod]
    field_simp
  rw [heq]
  have hsign := hneg v hvwide
  have hlow := (abs_le.mp (hbound v hvwide)).1
  constructor
  · have hh := mul_le_mul_of_nonneg_left hlow (by linarith only [hy.1] : 0 ≤ y)
    have hh' := mul_le_mul_of_nonpos_right hy.2 (neg_nonpos.mpr hU.le)
    nlinarith only [hh,hh']
  · have hh := mul_le_mul_of_nonneg_left hsign (by linarith only [hy.1] : 0 ≤ y)
    have hh' := mul_le_mul_of_nonpos_right hy.1 (neg_nonpos.mpr hc.le)
    nlinarith only [hh,hh']

#print axioms double_difference_exact_curvature_band

example
    (F : ℝ → ℝ) {x r s d y c U : ℝ}
    (hx : x∈Icc (3/4:ℝ) (9/4)) (hy : y∈Icc (1:ℝ) 2)
    (hr : 0 < r) (hs : 0 < s) (hd : 0 < d) (hc : 0 < c) (hU : 0 < U)
    (hprod : r*s=d*y) (hshift : r+s ≤ 1/4)
    (hf : ∀ u, 0 < u → ContDiffAt ℝ ∞ F u)
    (hneg : ∀ u∈Icc (1/2:ℝ) 3, iteratedDeriv 4 F u ≤ -c)
    (hbound : ∀ u∈Icc (1/2:ℝ) 3, |iteratedDeriv 4 F u| ≤ U) :
    let Q := fun u => (F u-F (u+r)-F (u+s)+F (u+r+s))/d;
    -2*U ≤ iteratedDeriv 2 Q x ∧ iteratedDeriv 2 Q x ≤ -c :=
  @double_difference_exact_curvature_band F x r s d y c U hx hy hr hs hd hc hU hprod hshift hf hneg hbound

/-- Actual pair fibers are counted over the SAME matrix and original
first point. The second-point count consumes the proved double-phase
source-scale grid bound; no second family-cardinality factor is inserted. -/
private theorem double_difference_family_pair_card_le_matrix_points
    {c U : ℝ} (hc : 0 < c) (hU : 0 < U) :
    ∃ D : ℝ, 0 < D ∧
      ∀ (P : Finset (((ℝ × ℤ) × Fin 2) × ((ℝ × ℤ) × Fin 2)))
        (Mat : (((ℝ × ℤ) × Fin 2) × ((ℝ × ℤ) × Fin 2)) → Fin 4 → ℤ)
        (F : ℝ → ℝ) (r s : ℝ → ℝ) (z : ℝ → ℤ → ℝ) (Alen : ℝ → ℤ → ℕ)
        (N : ℕ) (Z : ℝ → ℤ) (d w Δ J T M : ℝ),
      (∀ w, 0 < w → ContDiffAt ℝ ∞ F w) →
      (∀ u∈Icc (1/2:ℝ) 3, c ≤ iteratedDeriv 5 F u) →
      (∀ u∈Icc (1/2:ℝ) 3, ∀ n, 1 ≤ n → n ≤ 7 → |iteratedDeriv n F u| ≤ U) →
      (∀ u∈Icc (1/2:ℝ) 3,
        c ≤ |(iteratedDeriv 5 F u)^2-iteratedDeriv 4 F u*iteratedDeriv 6 F u|) →
      0 < d → 0 ≤ w → w ≤ 1/4 → 2*U*w ≤ c/64 →
      0 < T → 2 ≤ M → 0 < N → 0 ≤ Δ → 0 < J → J ≤ M → w*J ≤ 1 →
      (∀ ij∈P,
        (ij.1.1.1∈Icc (1:ℝ) 2 ∧ z ij.1.1.1 ij.1.1.2∈Icc M (2*M)) ∧
        (ij.2.1.1∈Icc (1:ℝ) 2 ∧ z ij.2.1.1 ij.2.1.2∈Icc M (2*M))) →
      (∀ ij∈P, N ≤ Alen ij.2.1.1 ij.2.1.2 ∧ Alen ij.2.1.1 ij.2.1.2 ≤ 3*N ∧
        round (z ij.2.1.1 ij.2.1.2)+(Alen ij.2.1.1 ij.2.1.2:ℤ)=
          Z ij.2.1.1+(N:ℤ)*ij.2.1.2+2*(N:ℤ)) →
      (∀ ij∈P, ∀ kl∈P, ij.2.1.1 ≠ kl.2.1.1 → 1 ≤ J*|ij.2.1.1-kl.2.1.1|) →
      (∀ y∈(P.image (fun ij => ij.1.1.1)) ∪ (P.image (fun ij => ij.2.1.1)),
        0 ≤ r y ∧ 0 ≤ s y ∧ r y*s y=d*y ∧ r y+s y ≤ w) →
      let Q := fun y u => (F u-F (u+r y)-F (u+s y)+F (u+r y+s y))/d
      let f := fun y u => T*Q y (u/M)
      let h := fun y w => iteratedDeriv 2 (f y) w/2
      let μ := fun y w => iteratedDeriv 3 (f y) (round w)/6
      let t := fun ij => (Mat ij 2:ℝ)*h ij.1.1.1 (z ij.1.1.1 ij.1.1.2)+Mat ij 3
      (∀ ij∈P, t ij∈Icc (1/2:ℝ) 2) →
      (∀ ij∈P, ((Mat ij 0:ℝ)*h ij.1.1.1 (z ij.1.1.1 ij.1.1.2)+Mat ij 1)/t ij=
        h ij.2.1.1 (z ij.2.1.1 ij.2.1.2)) →
      (∀ ij∈P, |μ ij.2.1.1 (z ij.2.1.1 ij.2.1.2)/
        μ ij.1.1.1 (z ij.1.1.1 ij.1.1.2)*(t ij)^3-1| ≤ Δ) →
      (P.card:ℝ) ≤ D*(1+Δ*J)*
        ((P.image (fun ij => (Mat ij,ij.1))).card:ℝ) := by
  obtain ⟨D,hD,hcount⟩ := double_difference_physical_family_fiber_source_scale hc hU
  refine ⟨D,hD,?_⟩
  intro P Mat F r s z Alen N Z d w Δ J T M hf hlower hbound hdet
    hd hw hwcap hsmall hT hM hN hΔ hJ hJM hwJ hpoints hgeometry hsep hshifts
    Q f h μ t ht hmap hthird
  classical
  let key := fun ij => (Mat ij,ij.1)
  let I := P.image key
  let Vbound := D*(1+Δ*J)
  have hfiber k (hk : k∈I) :
      ((P.filter (fun ij => key ij=k)).card:ℝ) ≤ Vbound := by
    obtain ⟨ij₀,hij₀,he₀⟩ := Finset.mem_image.mp hk
    let E := P.filter (fun ij => key ij=k)
    let S := E.image Prod.snd
    have hmem ij (hij : ij∈E) : ij∈P ∧ Mat ij=Mat ij₀ ∧ ij.1=ij₀.1 := by
      have hh := Finset.mem_filter.mp hij
      exact ⟨hh.1,(congrArg Prod.fst hh.2).trans (congrArg Prod.fst he₀).symm,
        (congrArg Prod.snd hh.2).trans (congrArg Prod.snd he₀).symm⟩
    have htE ij (hij : ij∈E) : t ij=t ij₀ := by
      dsimp only [t]
      rw [(hmem ij hij).2.1,(hmem ij hij).2.2]
    have hcS := hcount S F r s z Alen N Z d w ij₀.1.1.1 (z ij₀.1.1.1 ij₀.1.1.2)
      Δ J (((Mat ij₀ 0:ℝ)*h ij₀.1.1.1 (z ij₀.1.1.1 ij₀.1.1.2)+Mat ij₀ 1)/t ij₀)
      (t ij₀) T M hf hlower hbound hdet hd hw hwcap hsmall (hpoints ij₀ hij₀).1.1
      hT hM hN hΔ hJ hJM hwJ (ht ij₀ hij₀) (hpoints ij₀ hij₀).1.2
      (by
        intro ip hip
        obtain ⟨ij,hij,rfl⟩ := Finset.mem_image.mp hip
        exact (hpoints ij (hmem ij hij).1).2)
      (by
        intro ip hip
        obtain ⟨ij,hij,rfl⟩ := Finset.mem_image.mp hip
        exact hgeometry ij (hmem ij hij).1)
      (by
        intro ip hip jp hjp hne
        obtain ⟨ij,hij,rfl⟩ := Finset.mem_image.mp hip
        obtain ⟨kl,hkl,rfl⟩ := Finset.mem_image.mp hjp
        exact hsep ij (hmem ij hij).1 kl (hmem kl hkl).1 hne)
      (by
        intro y hy
        apply hshifts y
        rcases hy with rfl | hy
        · exact Finset.mem_union_left _ (Finset.mem_image_of_mem _ hij₀)
        · obtain ⟨ip,hip,rfl⟩ := Finset.mem_image.mp hy
          obtain ⟨ij,hij,rfl⟩ := Finset.mem_image.mp hip
          exact Finset.mem_union_right _ (Finset.mem_image_of_mem _ (hmem ij hij).1))
      (by
        intro ip hip
        obtain ⟨ij,hij,rfl⟩ := Finset.mem_image.mp hip
        have hh := (hmap ij (hmem ij hij).1).symm
        rw [htE ij hij,(hmem ij hij).2.1,(hmem ij hij).2.2] at hh
        exact hh)
      (by
        intro ip hip
        obtain ⟨ij,hij,rfl⟩ := Finset.mem_image.mp hip
        have hh := hthird ij (hmem ij hij).1
        rw [htE ij hij,(hmem ij hij).2.2] at hh
        exact hh)
    have he : S.card=E.card := Finset.card_image_of_injOn (by
      intro ij hij kl hkl he
      exact Prod.ext ((hmem ij hij).2.2.trans (hmem kl hkl).2.2.symm) he)
    rw [he] at hcS
    exact hcS
  have he : (P.card:ℝ)=∑ k∈I,((P.filter (fun ij => key ij=k)).card:ℝ) := by
    exact_mod_cast Finset.card_eq_sum_card_image key P
  rw [he]
  calc
    _ ≤ ∑ k∈I,Vbound := Finset.sum_le_sum hfiber
    _ = Vbound*(I.card:ℝ) := by rw [Finset.sum_const,nsmul_eq_mul,mul_comm]
    _ = _ := rfl

#print axioms double_difference_family_pair_card_le_matrix_points

example
    {c U : ℝ} (hc : 0 < c) (hU : 0 < U) :
    ∃ D : ℝ, 0 < D ∧
      ∀ (P : Finset (((ℝ × ℤ) × Fin 2) × ((ℝ × ℤ) × Fin 2)))
        (Mat : (((ℝ × ℤ) × Fin 2) × ((ℝ × ℤ) × Fin 2)) → Fin 4 → ℤ)
        (F : ℝ → ℝ) (r s : ℝ → ℝ) (z : ℝ → ℤ → ℝ) (Alen : ℝ → ℤ → ℕ)
        (N : ℕ) (Z : ℝ → ℤ) (d w Δ J T M : ℝ),
      (∀ w, 0 < w → ContDiffAt ℝ ∞ F w) →
      (∀ u∈Icc (1/2:ℝ) 3, c ≤ iteratedDeriv 5 F u) →
      (∀ u∈Icc (1/2:ℝ) 3, ∀ n, 1 ≤ n → n ≤ 7 → |iteratedDeriv n F u| ≤ U) →
      (∀ u∈Icc (1/2:ℝ) 3,
        c ≤ |(iteratedDeriv 5 F u)^2-iteratedDeriv 4 F u*iteratedDeriv 6 F u|) →
      0 < d → 0 ≤ w → w ≤ 1/4 → 2*U*w ≤ c/64 →
      0 < T → 2 ≤ M → 0 < N → 0 ≤ Δ → 0 < J → J ≤ M → w*J ≤ 1 →
      (∀ ij∈P,
        (ij.1.1.1∈Icc (1:ℝ) 2 ∧ z ij.1.1.1 ij.1.1.2∈Icc M (2*M)) ∧
        (ij.2.1.1∈Icc (1:ℝ) 2 ∧ z ij.2.1.1 ij.2.1.2∈Icc M (2*M))) →
      (∀ ij∈P, N ≤ Alen ij.2.1.1 ij.2.1.2 ∧ Alen ij.2.1.1 ij.2.1.2 ≤ 3*N ∧
        round (z ij.2.1.1 ij.2.1.2)+(Alen ij.2.1.1 ij.2.1.2:ℤ)=
          Z ij.2.1.1+(N:ℤ)*ij.2.1.2+2*(N:ℤ)) →
      (∀ ij∈P, ∀ kl∈P, ij.2.1.1 ≠ kl.2.1.1 → 1 ≤ J*|ij.2.1.1-kl.2.1.1|) →
      (∀ y∈(P.image (fun ij => ij.1.1.1)) ∪ (P.image (fun ij => ij.2.1.1)),
        0 ≤ r y ∧ 0 ≤ s y ∧ r y*s y=d*y ∧ r y+s y ≤ w) →
      let Q := fun y u => (F u-F (u+r y)-F (u+s y)+F (u+r y+s y))/d
      let f := fun y u => T*Q y (u/M)
      let h := fun y w => iteratedDeriv 2 (f y) w/2
      let μ := fun y w => iteratedDeriv 3 (f y) (round w)/6
      let t := fun ij => (Mat ij 2:ℝ)*h ij.1.1.1 (z ij.1.1.1 ij.1.1.2)+Mat ij 3
      (∀ ij∈P, t ij∈Icc (1/2:ℝ) 2) →
      (∀ ij∈P, ((Mat ij 0:ℝ)*h ij.1.1.1 (z ij.1.1.1 ij.1.1.2)+Mat ij 1)/t ij=
        h ij.2.1.1 (z ij.2.1.1 ij.2.1.2)) →
      (∀ ij∈P, |μ ij.2.1.1 (z ij.2.1.1 ij.2.1.2)/
        μ ij.1.1.1 (z ij.1.1.1 ij.1.1.2)*(t ij)^3-1| ≤ Δ) →
      (P.card:ℝ) ≤ D*(1+Δ*J)*
        ((P.image (fun ij => (Mat ij,ij.1))).card:ℝ) :=
  @double_difference_family_pair_card_le_matrix_points c U hc hU

/-- The identity and bounded-action nontriangular branches have the
literal source scale I*M/N*(1+Delta*J) for the actual double-phase family.
Source curvature gives matrix nonvanishing and bounds; original grid
geometry gives the first-point count. No count certificate is assumed. -/
private theorem double_difference_type_one_matrix_source_scale
    {c U L : ℝ} (hc : 0 < c) (hU : 0 < U) (hL : 0 ≤ L) :
    ∃ D : ℝ, 0 < D ∧
      ∀ (P : Finset (((ℝ × ℤ) × Fin 2) × ((ℝ × ℤ) × Fin 2)))
        (Mat : (((ℝ × ℤ) × Fin 2) × ((ℝ × ℤ) × Fin 2)) → Fin 4 → ℤ)
        (F : ℝ → ℝ) (r s : ℝ → ℝ) (z : ℝ → ℤ → ℝ) (Alen : ℝ → ℤ → ℕ)
        (N : ℕ) (Z : ℝ → ℤ) (d w Δ J T M : ℝ),
      (∀ w, 0 < w → ContDiffAt ℝ ∞ F w) →
      (∀ u∈Icc (1/2:ℝ) 3, c ≤ iteratedDeriv 5 F u) →
      (∀ u∈Icc (1/2:ℝ) 3, ∀ n, 1 ≤ n → n ≤ 7 → |iteratedDeriv n F u| ≤ U) →
      (∀ u∈Icc (1/2:ℝ) 3,
        c ≤ |(iteratedDeriv 5 F u)^2-iteratedDeriv 4 F u*iteratedDeriv 6 F u|) →
      (∀ u∈Icc (1/2:ℝ) 3, iteratedDeriv 4 F u ≤ -c) →
      0 < d → 0 ≤ w → w ≤ 1/4 → 2*U*w ≤ c/64 →
      0 < T → 2 ≤ M → 0 < N → 0 ≤ Δ → 0 < J → (N:ℝ) ≤ M → J ≤ M → w*J ≤ 1 →
      (∀ ij∈P,
        (ij.1.1.1∈Icc (1:ℝ) 2 ∧ z ij.1.1.1 ij.1.1.2∈Icc M (2*M)) ∧
        (ij.2.1.1∈Icc (1:ℝ) 2 ∧ z ij.2.1.1 ij.2.1.2∈Icc M (2*M))) →
      (∀ ij∈P, N ≤ Alen ij.1.1.1 ij.1.1.2 ∧ Alen ij.1.1.1 ij.1.1.2 ≤ 3*N ∧
        round (z ij.1.1.1 ij.1.1.2)+(Alen ij.1.1.1 ij.1.1.2:ℤ)=
          Z ij.1.1.1+(N:ℤ)*ij.1.1.2+2*(N:ℤ)) →
      (∀ ij∈P, N ≤ Alen ij.2.1.1 ij.2.1.2 ∧ Alen ij.2.1.1 ij.2.1.2 ≤ 3*N ∧
        round (z ij.2.1.1 ij.2.1.2)+(Alen ij.2.1.1 ij.2.1.2:ℤ)=
          Z ij.2.1.1+(N:ℤ)*ij.2.1.2+2*(N:ℤ)) →
      (∀ ij∈P, ∀ kl∈P, ij.2.1.1 ≠ kl.2.1.1 → 1 ≤ J*|ij.2.1.1-kl.2.1.1|) →
      (∀ y∈(P.image (fun ij => ij.1.1.1)) ∪ (P.image (fun ij => ij.2.1.1)),
        0 ≤ r y ∧ 0 ≤ s y ∧ r y*s y=d*y ∧ r y+s y ≤ w) →
      (∀ ij∈P, Mat ij 0*Mat ij 3-Mat ij 1*Mat ij 2=1) →
      (∀ ij∈P, Mat ij=![1,0,0,1] ∨
        (Mat ij 1 ≠ 0 ∧ Mat ij 2 ≠ 0 ∧ |(Mat ij 2:ℝ)| * (U*T/M^2) ≤ L)) →
      let Q := fun y u => (F u-F (u+r y)-F (u+s y)+F (u+r y+s y))/d
      let f := fun y u => T*Q y (u/M)
      let h := fun y w => iteratedDeriv 2 (f y) w/2
      let μ := fun y w => iteratedDeriv 3 (f y) (round w)/6
      let t := fun ij => (Mat ij 2:ℝ)*h ij.1.1.1 (z ij.1.1.1 ij.1.1.2)+Mat ij 3
      (∀ ij∈P, ((Mat ij 0:ℝ)*h ij.1.1.1 (z ij.1.1.1 ij.1.1.2)+Mat ij 1)/t ij=
        h ij.2.1.1 (z ij.2.1.1 ij.2.1.2)) →
      (∀ ij∈P, |t ij-1| ≤ 1/(8*(L+3))) →
      (∀ ij∈P, |((Mat ij 0:ℝ)*h ij.1.1.1 (z ij.1.1.1 ij.1.1.2)+Mat ij 1)/
        h ij.1.1.1 (z ij.1.1.1 ij.1.1.2)-1| ≤ 1/(8*(L+3))) →
      (∀ ij∈P, |μ ij.2.1.1 (z ij.2.1.1 ij.2.1.2)/
        μ ij.1.1.1 (z ij.1.1.1 ij.1.1.2)*(t ij)^3-1| ≤ Δ) →
      (P.card:ℝ) ≤ D*((P.image (fun ij => ij.1.1.1)).card:ℝ)*(M/(N:ℝ))*(1+Δ*J) := by
  obtain ⟨D,hD,hcount⟩ := double_difference_family_pair_card_le_matrix_points hc hU
  let CMat := (2*(L+3)^2+1)*(2*L+5)^2*(L+3)^2
  have hCMat : 0 < CMat := by dsimp only [CMat]; positivity
  refine ⟨10*D*(1+CMat),by positivity,?_⟩
  intro P Mat F r s z Alen N Z d w Δ J T M hf hlower hbound hdet hnegative
    hd hw hwcap hsmall hT hM hN hΔ hJ hNM hJM hwJ hpoints hgeometryA hgeometryB
    hsep hshifts hmatdet hbranch Q f h μ t hmap hden hnum hthird
  classical
  have hMp : 0 < M := by linarith only [hM]
  have hNp : (0:ℝ) < N := by exact_mod_cast hN
  let Hcurv := U*T/M^2
  let Smat := P.image Mat
  let Snon := Smat.filter (fun A => A 1 ≠ 0)
  have hex A (hA : A∈Smat) : ∃ ij, ij∈P ∧ Mat ij=A := Finset.mem_image.mp hA
  let pick := fun A => if hA : A∈Smat then Classical.choose (hex A hA) else (((0,0),0),((0,0),0))
  have hpick A (hA : A∈Smat) : pick A∈P ∧ Mat (pick A)=A := by
    dsimp only [pick]
    rw [dif_pos hA]
    exact Classical.choose_spec (hex A hA)
  have hnon A (hA : A∈Snon) :
      A 1 ≠ 0 ∧ A 2 ≠ 0 ∧ |(A 2:ℝ)| * Hcurv ≤ L := by
    have hm := Finset.mem_filter.mp hA
    have hb := hbranch _ (hpick A hm.1).1
    rw [(hpick A hm.1).2] at hb
    rcases hb with he | hb
    · exfalso
      apply hm.2
      simp only [he,Matrix.cons_val_one,Matrix.cons_val_zero]
    · exact hb
  have hcurv y v
      (hy : y∈(P.image (fun ij => ij.1.1.1)) ∪ (P.image (fun ij => ij.2.1.1)))
      (hyI : y∈Icc (1:ℝ) 2) (hv : v∈Icc M (2*M)) :
      h y v ≠ 0 ∧ |h y v| ≤ Hcurv := by
    have hx : v/M∈Icc (3/4:ℝ) (9/4) := by
      constructor
      · apply (le_div_iff₀ hMp).mpr
        linarith only [hv.1,hMp]
      · apply (div_le_iff₀ hMp).mpr
        linarith only [hv.2,hMp]
    have hsdata := hshifts y hy
    have hprodpos : 0 < r y*s y := by
      rw [hsdata.2.2.1]
      exact mul_pos hd (by linarith only [hyI.1])
    have hrp : 0 < r y := by nlinarith only [hsdata.1,hsdata.2.1,hprodpos]
    have hsp : 0 < s y := by nlinarith only [hsdata.1,hsdata.2.1,hprodpos]
    have hband := double_difference_exact_curvature_band F hx hyI hrp hsp hd hc hU
      hsdata.2.2.1 (hsdata.2.2.2.trans hwcap) hf hnegative
      (fun u hu => hbound u hu 4 (by norm_num) (by norm_num))
    have hreg := (double_difference_cubic_jet_bounds F hx hyI hsdata.1 hsdata.2.1
      hd hU hc hsdata.2.2.1 hsdata.2.2.2 hwcap hsmall hf hlower hbound).1
    have ha := sargos_iteratedDeriv_comp_affine_local (f:=Q y)
      (l:=0) (r:=v+1) (c:=M⁻¹) (d:=0)
      (fun u hu => hreg _ (by
        simpa only [add_zero] using mul_pos (inv_pos.mpr hMp) hu.1))
      (show v∈Ioo (0:ℝ) (v+1) from ⟨hMp.trans_le hv.1,by linarith⟩) 2
    have heq : h y v=(T/M^2)*iteratedDeriv 2 (Q y) (v/M)/2 := by
      dsimp only [h,f]
      rw [iteratedDeriv_const_mul_field]
      have he : (fun u => Q y (u/M))=(fun u => Q y (M⁻¹*u+0)) := by
        funext u
        congr 1
        ring
      rw [he,ha]
      simp only [add_zero,inv_pow]
      rw [show M⁻¹*v=v/M by ring]
      ring
    have hscale : 0 < T/M^2 := div_pos hT (pow_pos hMp 2)
    have hneg : h y v < 0 := by
      rw [heq]
      exact div_neg_of_neg_of_pos
        (mul_neg_of_pos_of_neg hscale (lt_of_le_of_lt hband.2 (by linarith only [hc])))
        (by norm_num)
    refine ⟨ne_of_lt hneg,?_⟩
    rw [abs_of_neg hneg,heq]
    have hlo := mul_le_mul_of_nonneg_left hband.1 hscale.le
    change T/M^2*(-2*U) ≤ T/M^2*iteratedDeriv 2 (Q y) (v/M) at hlo
    dsimp only [Hcurv]
    convert neg_le_neg (div_le_div_of_nonneg_right hlo (by norm_num : (0:ℝ) ≤ 2)) using 1
    ring
  let x := fun A => h (pick A).1.1.1 (z (pick A).1.1.1 (pick A).1.1.2)
  let y := fun A => h (pick A).2.1.1 (z (pick A).2.1.1 (pick A).2.1.2)
  have hmat := HuxleyRationalPhase.bounded_action_narrow_nontriangular_matrix_count
    (H:=Hcurv) Snon x y hL
    (by
      intro A hA
      have hh := hmatdet _ (hpick A (Finset.mem_filter.mp hA).1).1
      rw [(hpick A (Finset.mem_filter.mp hA).1).2] at hh
      exact hh)
    (fun A hA => ⟨(hnon A hA).1,(hnon A hA).2.1⟩)
    (by
      intro A hA
      have hpickA := (hpick A (Finset.mem_filter.mp hA).1).1
      have hp := hpoints _ hpickA
      have ha := hcurv _ _
        (Finset.mem_union_left _ (Finset.mem_image_of_mem _ hpickA)) hp.1.1 hp.1.2
      have hb := hcurv _ _
        (Finset.mem_union_right _ (Finset.mem_image_of_mem _ hpickA)) hp.2.1 hp.2.2
      exact ⟨ha.1,ha.2,hb.2⟩)
    (fun A hA => (hnon A hA).2.2)
    (by
      intro A hA
      have hh := hmap _ (hpick A (Finset.mem_filter.mp hA).1).1
      dsimp only [t] at hh
      rw [(hpick A (Finset.mem_filter.mp hA).1).2] at hh
      exact hh)
    (by
      intro A hA
      have hh := hden _ (hpick A (Finset.mem_filter.mp hA).1).1
      dsimp only [t] at hh
      rw [(hpick A (Finset.mem_filter.mp hA).1).2] at hh
      exact hh)
    (by
      intro A hA
      have hh := hnum _ (hpick A (Finset.mem_filter.mp hA).1).1
      rw [(hpick A (Finset.mem_filter.mp hA).1).2] at hh
      exact hh)
  have hsubmat : Smat ⊆ insert ![1,0,0,1] Snon := by
    intro A hA
    have hb := hbranch _ (hpick A hA).1
    rw [(hpick A hA).2] at hb
    rcases hb with he | hb
    · exact Finset.mem_insert.mpr (Or.inl he)
    · exact Finset.mem_insert.mpr (Or.inr (Finset.mem_filter.mpr ⟨hA,hb.1⟩))
  have hmatall : (Smat.card:ℝ) ≤ 1+CMat := by
    have hh : (Smat.card:ℝ) ≤ (Snon.card:ℝ)+1 := by
      exact_mod_cast (Finset.card_le_card hsubmat).trans (Finset.card_insert_le _ _)
    linarith only [hh,hmat]
  have ht ij (hij : ij∈P) : t ij∈Icc (1/2:ℝ) 2 := by
    have hε : 1/(8*(L+3)) ≤ (1:ℝ)/24 :=
      one_div_le_one_div_of_le (by norm_num) (by linarith only [hL])
    have hh := abs_le.mp ((hden ij hij).trans hε)
    constructor <;> linarith only [hh.1,hh.2]
  have hpair := hcount P Mat F r s z Alen N Z d w Δ J T M hf hlower hbound hdet
    hd hw hwcap hsmall hT hM hN hΔ hJ hJM hwJ hpoints hgeometryB hsep hshifts
    ht hmap hthird
  have hsub : P.image (fun ij => (Mat ij,ij.1)) ⊆ Smat ×ˢ P.image Prod.fst := by
    intro a ha
    obtain ⟨ij,hij,rfl⟩ := Finset.mem_image.mp ha
    exact Finset.mem_product.mpr ⟨Finset.mem_image_of_mem Mat hij,Finset.mem_image_of_mem Prod.fst hij⟩
  have hcard : ((P.image (fun ij => (Mat ij,ij.1))).card:ℝ) ≤
      (Smat.card:ℝ)*((P.image Prod.fst).card:ℝ) := by
    exact_mod_cast (Finset.card_le_card hsub).trans_eq (Finset.card_product Smat (P.image Prod.fst))
  have hfirst := HuxleyRationalPhase.rounded_offset_family_point_count
    (P.image Prod.fst) z Alen N Z hMp.le hN
    (by
      intro ip hip
      obtain ⟨ij,hij,rfl⟩ := Finset.mem_image.mp hip
      exact (hpoints ij hij).1.2)
    (by
      intro ip hip
      obtain ⟨ij,hij,rfl⟩ := Finset.mem_image.mp hip
      exact hgeometryA ij hij)
  rw [Finset.image_image] at hfirst
  let I := ((P.image (fun ij => ij.1.1.1)).card:ℝ)
  have hI : 0 ≤ I := by dsimp only [I]; positivity
  have hscale : 1 ≤ M/(N:ℝ) := (le_div_iff₀ hNp).mpr (by simpa only [one_mul] using hNM)
  have hfirst' : ((P.image Prod.fst).card:ℝ) ≤ 10*(M/(N:ℝ))*I := by
    apply hfirst.trans
    apply mul_le_mul_of_nonneg_right _ hI
    linarith only [hscale]
  calc
    (P.card:ℝ) ≤ D*(1+Δ*J)*((P.image (fun ij => (Mat ij,ij.1))).card:ℝ) := hpair
    _ ≤ D*(1+Δ*J)*((Smat.card:ℝ)*((P.image Prod.fst).card:ℝ)) :=
      mul_le_mul_of_nonneg_left hcard (by positivity)
    _ ≤ D*(1+Δ*J)*((1+CMat)*(10*(M/(N:ℝ))*I)) := by gcongr
    _ = _ := by ring


#print axioms double_difference_type_one_matrix_source_scale

example
    {c U L : ℝ} (hc : 0 < c) (hU : 0 < U) (hL : 0 ≤ L) :
    ∃ D : ℝ, 0 < D ∧
      ∀ (P : Finset (((ℝ × ℤ) × Fin 2) × ((ℝ × ℤ) × Fin 2)))
        (Mat : (((ℝ × ℤ) × Fin 2) × ((ℝ × ℤ) × Fin 2)) → Fin 4 → ℤ)
        (F : ℝ → ℝ) (r s : ℝ → ℝ) (z : ℝ → ℤ → ℝ) (Alen : ℝ → ℤ → ℕ)
        (N : ℕ) (Z : ℝ → ℤ) (d w Δ J T M : ℝ),
      (∀ w, 0 < w → ContDiffAt ℝ ∞ F w) →
      (∀ u∈Icc (1/2:ℝ) 3, c ≤ iteratedDeriv 5 F u) →
      (∀ u∈Icc (1/2:ℝ) 3, ∀ n, 1 ≤ n → n ≤ 7 → |iteratedDeriv n F u| ≤ U) →
      (∀ u∈Icc (1/2:ℝ) 3,
        c ≤ |(iteratedDeriv 5 F u)^2-iteratedDeriv 4 F u*iteratedDeriv 6 F u|) →
      (∀ u∈Icc (1/2:ℝ) 3, iteratedDeriv 4 F u ≤ -c) →
      0 < d → 0 ≤ w → w ≤ 1/4 → 2*U*w ≤ c/64 →
      0 < T → 2 ≤ M → 0 < N → 0 ≤ Δ → 0 < J → (N:ℝ) ≤ M → J ≤ M → w*J ≤ 1 →
      (∀ ij∈P,
        (ij.1.1.1∈Icc (1:ℝ) 2 ∧ z ij.1.1.1 ij.1.1.2∈Icc M (2*M)) ∧
        (ij.2.1.1∈Icc (1:ℝ) 2 ∧ z ij.2.1.1 ij.2.1.2∈Icc M (2*M))) →
      (∀ ij∈P, N ≤ Alen ij.1.1.1 ij.1.1.2 ∧ Alen ij.1.1.1 ij.1.1.2 ≤ 3*N ∧
        round (z ij.1.1.1 ij.1.1.2)+(Alen ij.1.1.1 ij.1.1.2:ℤ)=
          Z ij.1.1.1+(N:ℤ)*ij.1.1.2+2*(N:ℤ)) →
      (∀ ij∈P, N ≤ Alen ij.2.1.1 ij.2.1.2 ∧ Alen ij.2.1.1 ij.2.1.2 ≤ 3*N ∧
        round (z ij.2.1.1 ij.2.1.2)+(Alen ij.2.1.1 ij.2.1.2:ℤ)=
          Z ij.2.1.1+(N:ℤ)*ij.2.1.2+2*(N:ℤ)) →
      (∀ ij∈P, ∀ kl∈P, ij.2.1.1 ≠ kl.2.1.1 → 1 ≤ J*|ij.2.1.1-kl.2.1.1|) →
      (∀ y∈(P.image (fun ij => ij.1.1.1)) ∪ (P.image (fun ij => ij.2.1.1)),
        0 ≤ r y ∧ 0 ≤ s y ∧ r y*s y=d*y ∧ r y+s y ≤ w) →
      (∀ ij∈P, Mat ij 0*Mat ij 3-Mat ij 1*Mat ij 2=1) →
      (∀ ij∈P, Mat ij=![1,0,0,1] ∨
        (Mat ij 1 ≠ 0 ∧ Mat ij 2 ≠ 0 ∧ |(Mat ij 2:ℝ)| * (U*T/M^2) ≤ L)) →
      let Q := fun y u => (F u-F (u+r y)-F (u+s y)+F (u+r y+s y))/d
      let f := fun y u => T*Q y (u/M)
      let h := fun y w => iteratedDeriv 2 (f y) w/2
      let μ := fun y w => iteratedDeriv 3 (f y) (round w)/6
      let t := fun ij => (Mat ij 2:ℝ)*h ij.1.1.1 (z ij.1.1.1 ij.1.1.2)+Mat ij 3
      (∀ ij∈P, ((Mat ij 0:ℝ)*h ij.1.1.1 (z ij.1.1.1 ij.1.1.2)+Mat ij 1)/t ij=
        h ij.2.1.1 (z ij.2.1.1 ij.2.1.2)) →
      (∀ ij∈P, |t ij-1| ≤ 1/(8*(L+3))) →
      (∀ ij∈P, |((Mat ij 0:ℝ)*h ij.1.1.1 (z ij.1.1.1 ij.1.1.2)+Mat ij 1)/
        h ij.1.1.1 (z ij.1.1.1 ij.1.1.2)-1| ≤ 1/(8*(L+3))) →
      (∀ ij∈P, |μ ij.2.1.1 (z ij.2.1.1 ij.2.1.2)/
        μ ij.1.1.1 (z ij.1.1.1 ij.1.1.2)*(t ij)^3-1| ≤ Δ) →
      (P.card:ℝ) ≤ D*((P.image (fun ij => ij.1.1.1)).card:ℝ)*(M/(N:ℝ))*(1+Δ*J) :=
  @double_difference_type_one_matrix_source_scale c U L hc hU hL

/-- A second route to the triangular source branch: count the actual
integer translation entries and use the linear family fibers. This avoids
assuming a triangular analytic count, at an explicit (1+B) cost. -/
private theorem double_difference_triangular_pair_source_scale
    {c U : ℝ} (hc : 0 < c) (hU : 0 < U) :
    ∃ D : ℝ, 0 < D ∧
      ∀ (P : Finset (((ℝ × ℤ) × Fin 2) × ((ℝ × ℤ) × Fin 2)))
        (Mat : (((ℝ × ℤ) × Fin 2) × ((ℝ × ℤ) × Fin 2)) → Fin 4 → ℤ)
        (F : ℝ → ℝ) (r s : ℝ → ℝ) (z : ℝ → ℤ → ℝ) (Alen : ℝ → ℤ → ℕ)
        (N : ℕ) (Z : ℝ → ℤ) (d w Δ J T M B : ℝ),
      (∀ w, 0 < w → ContDiffAt ℝ ∞ F w) →
      (∀ u∈Icc (1/2:ℝ) 3, c ≤ iteratedDeriv 5 F u) →
      (∀ u∈Icc (1/2:ℝ) 3, ∀ n, 1 ≤ n → n ≤ 7 → |iteratedDeriv n F u| ≤ U) →
      (∀ u∈Icc (1/2:ℝ) 3,
        c ≤ |(iteratedDeriv 5 F u)^2-iteratedDeriv 4 F u*iteratedDeriv 6 F u|) →
      0 < d → 0 ≤ w → w ≤ 1/4 → 2*U*w ≤ c/64 →
      0 < T → 2 ≤ M → 0 < N → 0 ≤ Δ → 0 < J → (N:ℝ) ≤ M → J ≤ M → w*J ≤ 1 → 0 ≤ B →
      (∀ ij∈P,
        (ij.1.1.1∈Icc (1:ℝ) 2 ∧ z ij.1.1.1 ij.1.1.2∈Icc M (2*M)) ∧
        (ij.2.1.1∈Icc (1:ℝ) 2 ∧ z ij.2.1.1 ij.2.1.2∈Icc M (2*M))) →
      (∀ ij∈P, N ≤ Alen ij.1.1.1 ij.1.1.2 ∧ Alen ij.1.1.1 ij.1.1.2 ≤ 3*N ∧
        round (z ij.1.1.1 ij.1.1.2)+(Alen ij.1.1.1 ij.1.1.2:ℤ)=
          Z ij.1.1.1+(N:ℤ)*ij.1.1.2+2*(N:ℤ)) →
      (∀ ij∈P, N ≤ Alen ij.2.1.1 ij.2.1.2 ∧ Alen ij.2.1.1 ij.2.1.2 ≤ 3*N ∧
        round (z ij.2.1.1 ij.2.1.2)+(Alen ij.2.1.1 ij.2.1.2:ℤ)=
          Z ij.2.1.1+(N:ℤ)*ij.2.1.2+2*(N:ℤ)) →
      (∀ ij∈P, ∀ kl∈P, ij.2.1.1 ≠ kl.2.1.1 → 1 ≤ J*|ij.2.1.1-kl.2.1.1|) →
      (∀ y∈(P.image (fun ij => ij.1.1.1)) ∪ (P.image (fun ij => ij.2.1.1)),
        0 ≤ r y ∧ 0 ≤ s y ∧ r y*s y=d*y ∧ r y+s y ≤ w) →
      (∀ ij∈P, Mat ij 0=1 ∧ Mat ij 3=1 ∧
        ((Mat ij 2=0 ∧ |(Mat ij 1:ℝ)| ≤ B) ∨ (Mat ij 1=0 ∧ |(Mat ij 2:ℝ)| ≤ B))) →
      let Q := fun y u => (F u-F (u+r y)-F (u+s y)+F (u+r y+s y))/d
      let f := fun y u => T*Q y (u/M)
      let h := fun y w => iteratedDeriv 2 (f y) w/2
      let μ := fun y w => iteratedDeriv 3 (f y) (round w)/6
      let t := fun ij => (Mat ij 2:ℝ)*h ij.1.1.1 (z ij.1.1.1 ij.1.1.2)+Mat ij 3
      (∀ ij∈P, t ij∈Icc (1/2:ℝ) 2) →
      (∀ ij∈P, ((Mat ij 0:ℝ)*h ij.1.1.1 (z ij.1.1.1 ij.1.1.2)+Mat ij 1)/t ij=
        h ij.2.1.1 (z ij.2.1.1 ij.2.1.2)) →
      (∀ ij∈P, |μ ij.2.1.1 (z ij.2.1.1 ij.2.1.2)/
        μ ij.1.1.1 (z ij.1.1.1 ij.1.1.2)*(t ij)^3-1| ≤ Δ) →
      (P.card:ℝ) ≤ D*(1+B)*((P.image (fun ij => ij.1.1.1)).card:ℝ)*(M/(N:ℝ))*(1+Δ*J) := by
  obtain ⟨D,hD,hcount⟩ := double_difference_family_pair_card_le_matrix_points hc hU
  refine ⟨40*D,by positivity,?_⟩
  intro P Mat F r s z Alen N Z d w Δ J T M B hf hlower hbound hdet
    hd hw hwcap hsmall hT hM hN hΔ hJ hNM hJM hwJ hB hpoints hgeometryA hgeometryB
    hsep hshifts hbranch Q f h μ t ht hmap hthird
  classical
  have hMp : 0 < M := by linarith only [hM]
  have hNp : (0:ℝ) < N := by exact_mod_cast hN
  let Smat := P.image Mat
  let Entries := Smat.image (fun A => A 1+A 2)
  have hdata A (hA : A∈Smat) : A 0=1 ∧ A 3=1 ∧
      ((A 2=0 ∧ |(A 1:ℝ)| ≤ B) ∨ (A 1=0 ∧ |(A 2:ℝ)| ≤ B)) := by
    obtain ⟨ij,hij,rfl⟩ := Finset.mem_image.mp hA
    exact hbranch ij hij
  have hentries : (Entries.card:ℝ) ≤ 2*B+1 :=
    integer_card_le_of_abs_sub_le (a:=0) Entries hB (by
      intro e he
      obtain ⟨A,hA,rfl⟩ := Finset.mem_image.mp he
      rcases (hdata A hA).2.2 with hb | hb
      · simpa only [hb.1,add_zero,sub_zero] using hb.2
      · simpa only [hb.1,zero_add,sub_zero] using hb.2)
  let Upper := Entries.image (fun e => (![1,e,0,1] : Fin 4 → ℤ))
  let Lower := Entries.image (fun e => (![1,0,e,1] : Fin 4 → ℤ))
  have hsubmat : Smat ⊆ Upper ∪ Lower := by
    intro A hA
    have he : A 1+A 2∈Entries := Finset.mem_image_of_mem _ hA
    have ha := hdata A hA
    rcases ha.2.2 with hb | hb
    · apply Finset.mem_union_left
      refine Finset.mem_image.mpr ⟨A 1+A 2,he,?_⟩
      funext j
      fin_cases j <;> simp [ha.1,ha.2.1,hb.1]
    · apply Finset.mem_union_right
      refine Finset.mem_image.mpr ⟨A 1+A 2,he,?_⟩
      funext j
      fin_cases j <;> simp [ha.1,ha.2.1,hb.1]
  have hmat : (Smat.card:ℝ) ≤ 4*(1+B) := by
    have hh : (Smat.card:ℝ) ≤ (Entries.card:ℝ)+(Entries.card:ℝ) := by
      exact_mod_cast (Finset.card_le_card hsubmat).trans
        ((Finset.card_union_le Upper Lower).trans
          (Nat.add_le_add (Finset.card_image_le) (Finset.card_image_le)))
    linarith only [hh,hentries]
  have hpair := hcount P Mat F r s z Alen N Z d w Δ J T M hf hlower hbound hdet
    hd hw hwcap hsmall hT hM hN hΔ hJ hJM hwJ hpoints hgeometryB hsep hshifts
    ht hmap hthird
  have hsub : P.image (fun ij => (Mat ij,ij.1)) ⊆ Smat ×ˢ P.image Prod.fst := by
    intro a ha
    obtain ⟨ij,hij,rfl⟩ := Finset.mem_image.mp ha
    exact Finset.mem_product.mpr ⟨Finset.mem_image_of_mem Mat hij,Finset.mem_image_of_mem Prod.fst hij⟩
  have hcard : ((P.image (fun ij => (Mat ij,ij.1))).card:ℝ) ≤
      (Smat.card:ℝ)*((P.image Prod.fst).card:ℝ) := by
    exact_mod_cast (Finset.card_le_card hsub).trans_eq (Finset.card_product Smat (P.image Prod.fst))
  have hfirst := HuxleyRationalPhase.rounded_offset_family_point_count
    (P.image Prod.fst) z Alen N Z hMp.le hN
    (by
      intro ip hip
      obtain ⟨ij,hij,rfl⟩ := Finset.mem_image.mp hip
      exact (hpoints ij hij).1.2)
    (by
      intro ip hip
      obtain ⟨ij,hij,rfl⟩ := Finset.mem_image.mp hip
      exact hgeometryA ij hij)
  rw [Finset.image_image] at hfirst
  let I := ((P.image (fun ij => ij.1.1.1)).card:ℝ)
  have hI : 0 ≤ I := by dsimp only [I]; positivity
  have hscale : 1 ≤ M/(N:ℝ) := (le_div_iff₀ hNp).mpr (by simpa only [one_mul] using hNM)
  have hfirst' : ((P.image Prod.fst).card:ℝ) ≤ 10*(M/(N:ℝ))*I := by
    apply hfirst.trans
    apply mul_le_mul_of_nonneg_right _ hI
    linarith only [hscale]
  calc
    (P.card:ℝ) ≤ D*(1+Δ*J)*((P.image (fun ij => (Mat ij,ij.1))).card:ℝ) := hpair
    _ ≤ D*(1+Δ*J)*((Smat.card:ℝ)*((P.image Prod.fst).card:ℝ)) :=
      mul_le_mul_of_nonneg_left hcard (by positivity)
    _ ≤ D*(1+Δ*J)*((4*(1+B))*(10*(M/(N:ℝ))*I)) := by gcongr
    _ = _ := by ring


#print axioms double_difference_triangular_pair_source_scale

example
    {c U : ℝ} (hc : 0 < c) (hU : 0 < U) :
    ∃ D : ℝ, 0 < D ∧
      ∀ (P : Finset (((ℝ × ℤ) × Fin 2) × ((ℝ × ℤ) × Fin 2)))
        (Mat : (((ℝ × ℤ) × Fin 2) × ((ℝ × ℤ) × Fin 2)) → Fin 4 → ℤ)
        (F : ℝ → ℝ) (r s : ℝ → ℝ) (z : ℝ → ℤ → ℝ) (Alen : ℝ → ℤ → ℕ)
        (N : ℕ) (Z : ℝ → ℤ) (d w Δ J T M B : ℝ),
      (∀ w, 0 < w → ContDiffAt ℝ ∞ F w) →
      (∀ u∈Icc (1/2:ℝ) 3, c ≤ iteratedDeriv 5 F u) →
      (∀ u∈Icc (1/2:ℝ) 3, ∀ n, 1 ≤ n → n ≤ 7 → |iteratedDeriv n F u| ≤ U) →
      (∀ u∈Icc (1/2:ℝ) 3,
        c ≤ |(iteratedDeriv 5 F u)^2-iteratedDeriv 4 F u*iteratedDeriv 6 F u|) →
      0 < d → 0 ≤ w → w ≤ 1/4 → 2*U*w ≤ c/64 →
      0 < T → 2 ≤ M → 0 < N → 0 ≤ Δ → 0 < J → (N:ℝ) ≤ M → J ≤ M → w*J ≤ 1 → 0 ≤ B →
      (∀ ij∈P,
        (ij.1.1.1∈Icc (1:ℝ) 2 ∧ z ij.1.1.1 ij.1.1.2∈Icc M (2*M)) ∧
        (ij.2.1.1∈Icc (1:ℝ) 2 ∧ z ij.2.1.1 ij.2.1.2∈Icc M (2*M))) →
      (∀ ij∈P, N ≤ Alen ij.1.1.1 ij.1.1.2 ∧ Alen ij.1.1.1 ij.1.1.2 ≤ 3*N ∧
        round (z ij.1.1.1 ij.1.1.2)+(Alen ij.1.1.1 ij.1.1.2:ℤ)=
          Z ij.1.1.1+(N:ℤ)*ij.1.1.2+2*(N:ℤ)) →
      (∀ ij∈P, N ≤ Alen ij.2.1.1 ij.2.1.2 ∧ Alen ij.2.1.1 ij.2.1.2 ≤ 3*N ∧
        round (z ij.2.1.1 ij.2.1.2)+(Alen ij.2.1.1 ij.2.1.2:ℤ)=
          Z ij.2.1.1+(N:ℤ)*ij.2.1.2+2*(N:ℤ)) →
      (∀ ij∈P, ∀ kl∈P, ij.2.1.1 ≠ kl.2.1.1 → 1 ≤ J*|ij.2.1.1-kl.2.1.1|) →
      (∀ y∈(P.image (fun ij => ij.1.1.1)) ∪ (P.image (fun ij => ij.2.1.1)),
        0 ≤ r y ∧ 0 ≤ s y ∧ r y*s y=d*y ∧ r y+s y ≤ w) →
      (∀ ij∈P, Mat ij 0=1 ∧ Mat ij 3=1 ∧
        ((Mat ij 2=0 ∧ |(Mat ij 1:ℝ)| ≤ B) ∨ (Mat ij 1=0 ∧ |(Mat ij 2:ℝ)| ≤ B))) →
      let Q := fun y u => (F u-F (u+r y)-F (u+s y)+F (u+r y+s y))/d
      let f := fun y u => T*Q y (u/M)
      let h := fun y w => iteratedDeriv 2 (f y) w/2
      let μ := fun y w => iteratedDeriv 3 (f y) (round w)/6
      let t := fun ij => (Mat ij 2:ℝ)*h ij.1.1.1 (z ij.1.1.1 ij.1.1.2)+Mat ij 3
      (∀ ij∈P, t ij∈Icc (1/2:ℝ) 2) →
      (∀ ij∈P, ((Mat ij 0:ℝ)*h ij.1.1.1 (z ij.1.1.1 ij.1.1.2)+Mat ij 1)/t ij=
        h ij.2.1.1 (z ij.2.1.1 ij.2.1.2)) →
      (∀ ij∈P, |μ ij.2.1.1 (z ij.2.1.1 ij.2.1.2)/
        μ ij.1.1.1 (z ij.1.1.1 ij.1.1.2)*(t ij)^3-1| ≤ Δ) →
      (P.card:ℝ) ≤ D*(1+B)*((P.image (fun ij => ij.1.1.1)).card:ℝ)*(M/(N:ℝ))*(1+Δ*J) :=
  @double_difference_triangular_pair_source_scale c U hc hU

/-- The ACTUAL completed two-parity Fourier cloud supplies the same
matrices, affine strips, cubic tests and rational coloring used by the
double-phase Type-I count. Its constants precede all source data. -/
private theorem double_difference_colored_fourier_cloud_type_one
    {c U L : ℝ} (hc : 0 < c) (hU : 0 < U) (hL : 0 ≤ L) :
    ∃ Dtype : ℝ, 0 < Dtype ∧
    ∀ (S : Finset (ℝ × ℤ)) (F rshift sshift : ℝ → ℝ)
      (z : (ℝ × ℤ) → ℝ) (r : (ℝ × ℤ) → ℚ) (v : (ℝ × ℤ) → ℤ)
      (Alen : (ℝ × ℤ) → ℕ) (Z : ℝ → ℤ)
      (Q K₀ N : ℕ) [NeZero K₀] (d Wmax T M Jsep : ℝ),
    (∀ u, 0 < u → ContDiffAt ℝ ∞ F u) →
    (∀ u∈Icc (1/2:ℝ) 3, c ≤ iteratedDeriv 5 F u) →
    (∀ u∈Icc (1/2:ℝ) 3, ∀ n, 1 ≤ n → n ≤ 7 → |iteratedDeriv n F u| ≤ U) →
    (∀ u∈Icc (1/2:ℝ) 3,
      c ≤ |(iteratedDeriv 5 F u)^2-iteratedDeriv 4 F u*iteratedDeriv 6 F u|) →
    (∀ u∈Icc (1/2:ℝ) 3, iteratedDeriv 4 F u ≤ -c) →
    0 < d → 0 ≤ Wmax → Wmax ≤ 1/4 → 2*U*Wmax ≤ c/64 →
    0 < T → 2 ≤ M → 0 < N → 0 < Q →
    0 < Jsep → (N:ℝ) ≤ M → Jsep ≤ M → Wmax*Jsep ≤ 1 →
    (∀ i∈S, i.1∈Icc (1:ℝ) 2) →
    (∀ i∈S, z i∈Icc M (2*M)) →
    (∀ i∈S, N ≤ Alen i ∧ Alen i ≤ 3*N ∧
      round (z i)+(Alen i:ℤ)=Z i.1+(N:ℤ)*i.2+2*(N:ℤ)) →
    (∀ i∈S, ∀ j∈S, i.1≠j.1 → 1 ≤ Jsep*|i.1-j.1|) →
    (∀ y∈S.image Prod.fst,
      0 ≤ rshift y ∧ 0 ≤ sshift y ∧ rshift y*sshift y=d*y ∧ rshift y+sshift y ≤ Wmax) →
    let Φ := fun y u =>
      (F u-F (u+rshift y)-F (u+sshift y)+F (u+rshift y+sshift y))/d
    let f := fun i : ℝ × ℤ => fun u => T*Φ i.1 (u/M)
    (∀ i∈S, iteratedDeriv 2 (f i) (z i)/2=(r i:ℝ)) →
    (∀ i∈S, (r i).den ≤ Q ∧ Q ≤ 2*(r i).den) →
    (∀ i∈S, ((r i).den:ℤ) ∣ (r i).num*v i-1) →
    let μ₀ := c*T/(12*M^3)
    let U₀ := U*T/(2*M^3)
    let q := fun i => (r i).den
    let μ := fun i => iteratedDeriv 3 (f i) (round (z i))/6
    let ℓ := fun i => deriv (f i) (round (z i))
    let b := fun i (p : Fin 2) => (⌊(q i:ℝ)*ℓ i⌋+(p:ℕ) : ℤ)
    let τ := fun i p => ((b i p:ℝ)-(q i:ℝ)*ℓ i)/2
    let K := fun i => -2*μ i*(Real.sqrt (2/(3*μ i*(q i:ℝ))))^3
    let x := fun i p =>
      (![-(v i:ℝ)*b i p/q i,-(v i:ℝ)/q i,K i,3*K i*τ i p/2] : Fin 4 → ℝ)
    let V := S ×ˢ (Finset.univ : Finset (Fin 2))
    let w := fun ip : (ℝ × ℤ) × Fin 2 =>
      (![Int.fract (x ip.1 ip.2 0),Int.fract (x ip.1 ip.2 1),
        x ip.1 ip.2 2/Real.sqrt K₀,x ip.1 ip.2 3/Real.sqrt K₀] : Fin 4 → ℝ)
    let radius : Fin 4 → ℝ :=
      ![1/(12*(K₀:ℝ)),1/(12*(K₀:ℝ)^2),(1/(K₀:ℝ)^2)/12,(1/(K₀:ℝ))/12]
    let P := (V ×ˢ V).filter (fun ij => ∀ d, |w ij.1 d-w ij.2 d| ≤ 2*radius d)
    let h := fun i => iteratedDeriv 2 (f i) (z i)/2
    let D := (Real.sqrt K₀/(9*(K₀:ℝ))+Real.sqrt K₀/(12*(K₀:ℝ)^2))*
      Real.sqrt (U₀*(Q:ℝ)^3)
    let δ := 1/(8*(L+3))
    let lambda := c*T/(2*M^2)
    let Hcurv := U*T/M^2
    let q₀ := (Q:ℝ)/2
    let p₀ := lambda*(Q:ℝ)/2
    let color := fun i => (⌊((r i).den:ℝ)/(δ*q₀)⌋,⌊((r i).num:ℝ)/(δ*p₀)⌋)
    let Cap := (4/δ+3)*(8*U/(c*δ)+3)
    ((S.image color).card:ℝ) ≤ Cap ∧
    (∀ coeff : (ℝ × ℤ) → ℂ, ‖∑ i∈S,coeff i‖^12 ≤ Cap^11*
      ∑ j∈S.image color, ‖∑ i∈S.filter (fun i => color i=j),coeff i‖^12) ∧
    ∃ A : (((ℝ × ℤ) × Fin 2) × ((ℝ × ℤ) × Fin 2)) → Fin 4 → ℤ,
      (∀ ij∈P,
        A ij 0*A ij 3-A ij 1*A ij 2=1 ∧
        let t := (A ij 2:ℝ)*h ij.1.1+A ij 3
        t=(q ij.2.1:ℝ)/q ij.1.1 ∧ (1:ℝ)/2 ≤ t ∧ t ≤ 2 ∧
        ((A ij 0:ℝ)*h ij.1.1+A ij 1)/t=h ij.2.1 ∧
        |(A ij 2:ℝ)| ≤ (Q:ℝ)^2/(6*(K₀:ℝ)^2) ∧
        |μ ij.2.1/μ ij.1.1*t^3-1| ≤
          (16*U₀/μ₀)*Real.sqrt (U₀*(Q:ℝ)^3)*Real.sqrt K₀/(6*(K₀:ℝ)^2) ∧
        |τ ij.1.1 ij.1.2-τ ij.2.1 ij.2.2| ≤ D ∧
        (∃ e₁ e₂ : ℤ,
          let F₁ := 2*(round (z ij.2.1):ℝ)-2*(A ij 3:ℝ)*(round (z ij.1.1):ℝ)-
            (A ij 2:ℝ)*ℓ ij.1.1
          let F₂ := ℓ ij.2.1-2*(A ij 1:ℝ)*(round (z ij.1.1):ℝ)-
            (A ij 0:ℝ)*ℓ ij.1.1
          |F₁-e₁| ≤ (q ij.2.1:ℝ)/(6*(K₀:ℝ))+|(A ij 2:ℝ)|/q ij.1.1 ∧
          |(F₂-e₂)-h ij.2.1*(F₁-e₁)| ≤ 2*D/q ij.2.1) ∧
        ((Q:ℝ)^2/(6*(K₀:ℝ)^2) < 1 →
          A ij 2=0 ∧ q ij.1.1=q ij.2.1 ∧
            (q ij.1.1:ℤ) ∣ (r ij.2.1).num-(r ij.1.1).num)) ∧
      (∀ ij∈P, color ij.1.1=color ij.2.1 →
        let t := (A ij 2:ℝ)*h ij.1.1+A ij 3
        |t-1| ≤ δ ∧
        |((A ij 0:ℝ)*h ij.1.1+A ij 1)/h ij.1.1-1| ≤ δ ∧
        ((A ij 0=1 ∧ A ij 1=0 ∧ A ij 2=0 ∧ A ij 3=1) ∨
         (A ij 0=1 ∧ A ij 3=1 ∧ A ij 2=0 ∧ A ij 1≠0 ∧ |(A ij 1:ℝ)| ≤ δ*Hcurv) ∨
         (A ij 0=1 ∧ A ij 3=1 ∧ A ij 1=0 ∧ A ij 2≠0 ∧ |(A ij 2:ℝ)| ≤ δ/lambda) ∨
         (A ij 1≠0 ∧ A ij 2≠0)) ∧
        (|(A ij 2:ℝ)| * Hcurv ≤ L →
          A ij 0+A ij 3=2 ∧ (A ij 0-1)^2= -A ij 1*A ij 2)) ∧
      let E := P.filter (fun ij =>
        color ij.1.1=color ij.2.1 ∧
        ((A ij 0=1 ∧ A ij 1=0 ∧ A ij 2=0 ∧ A ij 3=1) ∨
         (A ij 1≠0 ∧ A ij 2≠0 ∧ |(A ij 2:ℝ)| * Hcurv ≤ L)))
      let Δ := (16*U₀/μ₀)*Real.sqrt (U₀*(Q:ℝ)^3)*Real.sqrt K₀/(6*(K₀:ℝ)^2)
      (E.card:ℝ) ≤ Dtype*((S.image Prod.fst).card:ℝ)*(M/(N:ℝ))*(1+Δ*Jsep) := by
  obtain ⟨Dtype,hDtype,hcount⟩ := double_difference_type_one_matrix_source_scale hc hU hL
  refine ⟨Dtype,hDtype,?_⟩
  intro S F rshift sshift z r v Alen Z Q K₀ N _ d Wmax T M Jsep
    hf hlower hbound hdet hnegative hd hw hwcap hsmall hT hM hN hQ
    hJsep hNM hJM hwJ hy hz hgeometry hsep hshifts Φ f hlevel hden hinv
    μ₀ U₀ q μ ℓ b τ K x V w radius P h D δ lambda Hcurv q₀ p₀ color Cap
  classical
  have hMp : 0 < M := by linarith only [hM]
  have hδ : 0 < δ := by dsimp only [δ]; positivity
  have hδmax : δ < 1 := by
    dsimp only [δ]
    apply (div_lt_iff₀ (by positivity)).mpr
    linarith only [hL]
  have hlambda : 0 < lambda := by dsimp only [lambda]; positivity
  have hHcurv : 0 < Hcurv := by dsimp only [Hcurv]; positivity
  have hμ₀ : 0 < μ₀ := by dsimp only [μ₀]; positivity
  have hjet i (hi : i∈S) u (hu : u∈Icc (3/4:ℝ) (9/4)) :=
    double_difference_cubic_jet_bounds F hu (hy i hi)
      (hshifts i.1 (Finset.mem_image_of_mem Prod.fst hi)).1
      (hshifts i.1 (Finset.mem_image_of_mem Prod.fst hi)).2.1 hd hU hc
      (hshifts i.1 (Finset.mem_image_of_mem Prod.fst hi)).2.2.1
      (hshifts i.1 (Finset.mem_image_of_mem Prod.fst hi)).2.2.2
      hwcap hsmall hf hlower hbound
  have hphysical (n : ℕ) i (hi : i∈S) u (hu : 0 < u) :
      iteratedDeriv n (f i) u=T/M^n*iteratedDeriv n (Φ i.1) (u/M) := by
    have hreg := (hjet i hi 1 (by norm_num)).1
    have ha := sargos_iteratedDeriv_comp_affine_local (f:=Φ i.1)
      (l:=0) (r:=u+1) (c:=M⁻¹) (d:=0)
      (fun v hv => hreg _ (by
        simpa only [add_zero] using mul_pos (inv_pos.mpr hMp) hv.1))
      (show u∈Ioo (0:ℝ) (u+1) from ⟨hu,by linarith⟩) n
    change iteratedDeriv n (fun v => T*Φ i.1 (v/M)) u=_
    rw [iteratedDeriv_const_mul_field]
    have he : (fun v => Φ i.1 (v/M))=(fun v => Φ i.1 (M⁻¹*v+0)) := by
      funext v
      congr 1
      ring
    rw [he,ha]
    simp only [add_zero,inv_pow]
    rw [show M⁻¹*u=u/M by ring]
    ring
  have hcurv i (hi : i∈S) : lambda ≤ |h i| ∧ |h i| ≤ Hcurv := by
    have hzi := hz i hi
    have hpar := hy i hi
    have hx : z i/M∈Icc (3/4:ℝ) (9/4) := by
      constructor
      · apply (le_div_iff₀ hMp).mpr
        linarith only [hzi.1,hMp]
      · apply (div_le_iff₀ hMp).mpr
        linarith only [hzi.2,hMp]
    have hsdata := hshifts i.1 (Finset.mem_image_of_mem Prod.fst hi)
    have hprodpos : 0 < rshift i.1*sshift i.1 := by
      rw [hsdata.2.2.1]
      exact mul_pos hd (by linarith only [hpar.1])
    have hrp : 0 < rshift i.1 := by nlinarith only [hsdata.1,hsdata.2.1,hprodpos]
    have hsp : 0 < sshift i.1 := by nlinarith only [hsdata.1,hsdata.2.1,hprodpos]
    have hband := double_difference_exact_curvature_band F hx hpar hrp hsp hd hc hU
      hsdata.2.2.1 (hsdata.2.2.2.trans hwcap) hf hnegative
      (fun u hu => hbound u hu 4 (by norm_num) (by norm_num))
    have hband' : -2*U ≤ iteratedDeriv 2 (Φ i.1) (z i/M) ∧
        iteratedDeriv 2 (Φ i.1) (z i/M) ≤ -c := hband
    have hsign : iteratedDeriv 2 (Φ i.1) (z i/M) < 0 := by
      linarith only [hband'.2,hc]
    have he : |h i|=(T/M^2)*(-iteratedDeriv 2 (Φ i.1) (z i/M))/2 := by
      dsimp only [h]
      rw [hphysical 2 i hi _ (hMp.trans_le hzi.1),abs_div,abs_mul,
        abs_of_pos (div_pos hT (pow_pos hMp 2)),abs_of_neg hsign,abs_of_pos (by norm_num : (0:ℝ) < 2)]
    rw [he]
    constructor
    · calc
        lambda = (T/M^2)*c/2 := by dsimp only [lambda]; ring
        _ ≤ _ := div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left (by linarith only [hband'.2]) (by positivity)) (by norm_num)
    · calc
        _ ≤ (T/M^2)*(2*U)/2 := div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left (by linarith only [hband'.1]) (by positivity)) (by norm_num)
        _ = Hcurv := by dsimp only [Hcurv]; ring
  have hμbounds i (hi : i∈S) : μ₀ ≤ μ i ∧ μ i ≤ U₀ := by
    have hr := abs_le.mp (abs_sub_round (z i))
    have hzi := hz i hi
    have hrpos : (0:ℝ) < round (z i) := by linarith only [hr.2,hzi.1,hM]
    have hx : (round (z i):ℝ)/M∈Icc (3/4:ℝ) (9/4) := by
      constructor
      · apply (le_div_iff₀ hMp).mpr
        linarith only [hr.2,hzi.1,hM]
      · apply (div_le_iff₀ hMp).mpr
        linarith only [hr.1,hzi.2,hM]
    have hj := hjet i hi _ hx
    have hlo : c/2 ≤ iteratedDeriv 3 (Φ i.1) ((round (z i):ℝ)/M) := hj.2.1
    have hhi : iteratedDeriv 3 (Φ i.1) ((round (z i):ℝ)/M) ≤ 3*U :=
      (abs_le.mp hj.2.2.1).2
    have he : μ i=(T/M^3)*iteratedDeriv 3 (Φ i.1) ((round (z i):ℝ)/M)/6 := by
      dsimp only [μ]
      rw [hphysical 3 i hi _ hrpos]
    rw [he]
    constructor
    · calc
        μ₀ = (T/M^3)*(c/2)/6 := by dsimp only [μ₀]; ring
        _ ≤ _ := div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left hlo (by positivity)) (by norm_num)
    · calc
        _ ≤ (T/M^3)*(3*U)/6 := div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left hhi (by positivity)) (by norm_num)
        _ = U₀ := by dsimp only [U₀]; ring
  have hband := HuxleyRationalPhase.rational_narrow_band_twelfth_partition
    S r Q hQ hlambda hHcurv.le hδ
    (by
      intro i hi
      rw [←hlevel i hi]
      exact hcurv i hi) hden
  have hcap : (4/δ+3)*(4*Hcurv/(lambda*δ)+3)=Cap := by
    dsimp only [Hcurv,lambda,Cap]
    field_simp; ring
  simp only [hcap] at hband
  refine ⟨hband.1,hband.2.2,?_⟩
  obtain ⟨A,hA⟩ := HuxleyRationalPhase.source_arc_fourier_cloud_matrices
    S f z r v Q K₀ μ₀ U₀ hμ₀ hμbounds hlevel hden hinv
  have hclass : ∀ ij∈P, color ij.1.1=color ij.2.1 →
        let t := (A ij 2:ℝ)*h ij.1.1+A ij 3
        |t-1| ≤ δ ∧
        |((A ij 0:ℝ)*h ij.1.1+A ij 1)/h ij.1.1-1| ≤ δ ∧
        ((A ij 0=1 ∧ A ij 1=0 ∧ A ij 2=0 ∧ A ij 3=1) ∨
         (A ij 0=1 ∧ A ij 3=1 ∧ A ij 2=0 ∧ A ij 1≠0 ∧ |(A ij 1:ℝ)| ≤ δ*Hcurv) ∨
         (A ij 0=1 ∧ A ij 3=1 ∧ A ij 1=0 ∧ A ij 2≠0 ∧ |(A ij 2:ℝ)| ≤ δ/lambda) ∨
         (A ij 1≠0 ∧ A ij 2≠0)) ∧
        (|(A ij 2:ℝ)| * Hcurv ≤ L →
          A ij 0+A ij 3=2 ∧ (A ij 0-1)^2= -A ij 1*A ij 2) := by
    intro ij hij hcolor t
    have hpair := Finset.mem_product.mp (Finset.mem_filter.mp hij).1
    have hi : ij.1.1∈S := (Finset.mem_product.mp hpair.1).1
    have hj : ij.2.1∈S := (Finset.mem_product.mp hpair.2).1
    have hb := hband.2.1 _ hi _ hj hcolor
    have hp := hA ij hij
    have ht : t=(q ij.2.1:ℝ)/q ij.1.1 := hp.2.1
    have htpos : 0 < t := by
      have hh : (1:ℝ)/2 ≤ t := hp.2.2.1
      linarith only [hh]
    have hmap : ((A ij 0:ℝ)*h ij.1.1+A ij 1)/t=h ij.2.1 := hp.2.2.2.2.1
    have hcurvi := hcurv _ hi
    have hcurvj := hcurv _ hj
    have hx : h ij.1.1 ≠ 0 := abs_pos.mp (hlambda.trans_le hcurvi.1)
    have hri : h ij.1.1=(r ij.1.1:ℝ) := hlevel _ hi
    have hrj : h ij.2.1=(r ij.2.1:ℝ) := hlevel _ hj
    have hnumeq : ((A ij 0:ℝ)*h ij.1.1+A ij 1)/h ij.1.1=
        ((r ij.2.1).num:ℝ)/(r ij.1.1).num := by
      rw [(div_eq_iff htpos.ne').mp hmap,ht,hri,hrj]
      dsimp only [q]
      simp only [Rat.cast_def]
      field_simp
    have hden' : |t-1| ≤ δ := by simpa only [ht,q] using hb.1
    have hnum' : |((A ij 0:ℝ)*h ij.1.1+A ij 1)/h ij.1.1-1| ≤ δ := by
      simpa only [hnumeq] using hb.2
    refine ⟨hden',hnum',?_,?_⟩
    · exact HuxleyRationalPhase.narrow_band_matrix_translation_cases (A ij 0) (A ij 1) (A ij 2) (A ij 3)
        hlambda hcurvi.1 hcurvi.2 hδ.le hδmax hp.1 hden' hnum'
    · intro haction
      exact HuxleyRationalPhase.bounded_action_narrow_ratios_trace_two (A ij 0) (A ij 1) (A ij 2) (A ij 3)
        hp.1 hx hcurvi.2 hcurvj.2 haction hmap hden' hnum'
  refine ⟨A,hA,hclass,?_⟩
  intro E Δ
  have hΔ : 0 ≤ Δ := by dsimp only [Δ,U₀,μ₀]; positivity
  have hmem ij (hij : ij∈E) :
      ij∈P ∧ color ij.1.1=color ij.2.1 ∧
        ((A ij 0=1 ∧ A ij 1=0 ∧ A ij 2=0 ∧ A ij 3=1) ∨
         (A ij 1≠0 ∧ A ij 2≠0 ∧ |(A ij 2:ℝ)| * Hcurv ≤ L)) := by
    exact Finset.mem_filter.mp hij
  have hpoints ij (hij : ij∈P) : ij.1.1∈S ∧ ij.2.1∈S := by
    have hh := Finset.mem_product.mp (Finset.mem_filter.mp hij).1
    exact ⟨(Finset.mem_product.mp hh.1).1,(Finset.mem_product.mp hh.2).1⟩
  have hh := hcount E A F rshift sshift (fun a k => z (a,k)) (fun a k => Alen (a,k))
    N Z d Wmax Δ Jsep T M hf hlower hbound hdet hnegative hd hw hwcap hsmall
    hT hM hN hΔ hJsep hNM hJM hwJ
    (by
      intro ij hij
      have hp := hpoints ij (hmem ij hij).1
      exact ⟨⟨hy _ hp.1,hz _ hp.1⟩,⟨hy _ hp.2,hz _ hp.2⟩⟩)
    (fun ij hij => hgeometry _ (hpoints ij (hmem ij hij).1).1)
    (fun ij hij => hgeometry _ (hpoints ij (hmem ij hij).1).2)
    (fun ij hij kl hkl hne =>
      hsep _ (hpoints ij (hmem ij hij).1).2 _ (hpoints kl (hmem kl hkl).1).2 hne)
    (by
      intro y hy'
      apply hshifts y
      rcases Finset.mem_union.mp hy' with hy' | hy'
      · obtain ⟨ij,hij,rfl⟩ := Finset.mem_image.mp hy'
        exact Finset.mem_image_of_mem Prod.fst (hpoints ij (hmem ij hij).1).1
      · obtain ⟨ij,hij,rfl⟩ := Finset.mem_image.mp hy'
        exact Finset.mem_image_of_mem Prod.fst (hpoints ij (hmem ij hij).1).2)
    (fun ij hij => (hA ij (hmem ij hij).1).1)
    (by
      intro ij hij
      rcases (hmem ij hij).2.2 with hb | hb
      · left
        rcases hb with ⟨h0,h1,h2,h3⟩
        funext j
        fin_cases j <;> simp [h0,h1,h2,h3]
      · exact Or.inr hb)
    (fun ij hij => (hA ij (hmem ij hij).1).2.2.2.2.1)
    (fun ij hij => (hclass ij (hmem ij hij).1 (hmem ij hij).2.1).1)
    (fun ij hij => (hclass ij (hmem ij hij).1 (hmem ij hij).2.1).2.1)
    (fun ij hij => (hA ij (hmem ij hij).1).2.2.2.2.2.2.1)
  have hsub : E.image (fun ij => ij.1.1.1) ⊆ S.image Prod.fst := by
    intro a ha
    obtain ⟨ij,hij,rfl⟩ := Finset.mem_image.mp ha
    exact Finset.mem_image_of_mem Prod.fst (hpoints ij (hmem ij hij).1).1
  have hI : ((E.image (fun ij => ij.1.1.1)).card:ℝ) ≤ ((S.image Prod.fst).card:ℝ) := by
    exact_mod_cast Finset.card_le_card hsub
  exact hh.trans (by gcongr)


#print axioms double_difference_colored_fourier_cloud_type_one

example
    {c U L : ℝ} (hc : 0 < c) (hU : 0 < U) (hL : 0 ≤ L) :
    ∃ Dtype : ℝ, 0 < Dtype ∧
    ∀ (S : Finset (ℝ × ℤ)) (F rshift sshift : ℝ → ℝ)
      (z : (ℝ × ℤ) → ℝ) (r : (ℝ × ℤ) → ℚ) (v : (ℝ × ℤ) → ℤ)
      (Alen : (ℝ × ℤ) → ℕ) (Z : ℝ → ℤ)
      (Q K₀ N : ℕ) [NeZero K₀] (d Wmax T M Jsep : ℝ),
    (∀ u, 0 < u → ContDiffAt ℝ ∞ F u) →
    (∀ u∈Icc (1/2:ℝ) 3, c ≤ iteratedDeriv 5 F u) →
    (∀ u∈Icc (1/2:ℝ) 3, ∀ n, 1 ≤ n → n ≤ 7 → |iteratedDeriv n F u| ≤ U) →
    (∀ u∈Icc (1/2:ℝ) 3,
      c ≤ |(iteratedDeriv 5 F u)^2-iteratedDeriv 4 F u*iteratedDeriv 6 F u|) →
    (∀ u∈Icc (1/2:ℝ) 3, iteratedDeriv 4 F u ≤ -c) →
    0 < d → 0 ≤ Wmax → Wmax ≤ 1/4 → 2*U*Wmax ≤ c/64 →
    0 < T → 2 ≤ M → 0 < N → 0 < Q →
    0 < Jsep → (N:ℝ) ≤ M → Jsep ≤ M → Wmax*Jsep ≤ 1 →
    (∀ i∈S, i.1∈Icc (1:ℝ) 2) →
    (∀ i∈S, z i∈Icc M (2*M)) →
    (∀ i∈S, N ≤ Alen i ∧ Alen i ≤ 3*N ∧
      round (z i)+(Alen i:ℤ)=Z i.1+(N:ℤ)*i.2+2*(N:ℤ)) →
    (∀ i∈S, ∀ j∈S, i.1≠j.1 → 1 ≤ Jsep*|i.1-j.1|) →
    (∀ y∈S.image Prod.fst,
      0 ≤ rshift y ∧ 0 ≤ sshift y ∧ rshift y*sshift y=d*y ∧ rshift y+sshift y ≤ Wmax) →
    let Φ := fun y u =>
      (F u-F (u+rshift y)-F (u+sshift y)+F (u+rshift y+sshift y))/d
    let f := fun i : ℝ × ℤ => fun u => T*Φ i.1 (u/M)
    (∀ i∈S, iteratedDeriv 2 (f i) (z i)/2=(r i:ℝ)) →
    (∀ i∈S, (r i).den ≤ Q ∧ Q ≤ 2*(r i).den) →
    (∀ i∈S, ((r i).den:ℤ) ∣ (r i).num*v i-1) →
    let μ₀ := c*T/(12*M^3)
    let U₀ := U*T/(2*M^3)
    let q := fun i => (r i).den
    let μ := fun i => iteratedDeriv 3 (f i) (round (z i))/6
    let ℓ := fun i => deriv (f i) (round (z i))
    let b := fun i (p : Fin 2) => (⌊(q i:ℝ)*ℓ i⌋+(p:ℕ) : ℤ)
    let τ := fun i p => ((b i p:ℝ)-(q i:ℝ)*ℓ i)/2
    let K := fun i => -2*μ i*(Real.sqrt (2/(3*μ i*(q i:ℝ))))^3
    let x := fun i p =>
      (![-(v i:ℝ)*b i p/q i,-(v i:ℝ)/q i,K i,3*K i*τ i p/2] : Fin 4 → ℝ)
    let V := S ×ˢ (Finset.univ : Finset (Fin 2))
    let w := fun ip : (ℝ × ℤ) × Fin 2 =>
      (![Int.fract (x ip.1 ip.2 0),Int.fract (x ip.1 ip.2 1),
        x ip.1 ip.2 2/Real.sqrt K₀,x ip.1 ip.2 3/Real.sqrt K₀] : Fin 4 → ℝ)
    let radius : Fin 4 → ℝ :=
      ![1/(12*(K₀:ℝ)),1/(12*(K₀:ℝ)^2),(1/(K₀:ℝ)^2)/12,(1/(K₀:ℝ))/12]
    let P := (V ×ˢ V).filter (fun ij => ∀ d, |w ij.1 d-w ij.2 d| ≤ 2*radius d)
    let h := fun i => iteratedDeriv 2 (f i) (z i)/2
    let D := (Real.sqrt K₀/(9*(K₀:ℝ))+Real.sqrt K₀/(12*(K₀:ℝ)^2))*
      Real.sqrt (U₀*(Q:ℝ)^3)
    let δ := 1/(8*(L+3))
    let lambda := c*T/(2*M^2)
    let Hcurv := U*T/M^2
    let q₀ := (Q:ℝ)/2
    let p₀ := lambda*(Q:ℝ)/2
    let color := fun i => (⌊((r i).den:ℝ)/(δ*q₀)⌋,⌊((r i).num:ℝ)/(δ*p₀)⌋)
    let Cap := (4/δ+3)*(8*U/(c*δ)+3)
    ((S.image color).card:ℝ) ≤ Cap ∧
    (∀ coeff : (ℝ × ℤ) → ℂ, ‖∑ i∈S,coeff i‖^12 ≤ Cap^11*
      ∑ j∈S.image color, ‖∑ i∈S.filter (fun i => color i=j),coeff i‖^12) ∧
    ∃ A : (((ℝ × ℤ) × Fin 2) × ((ℝ × ℤ) × Fin 2)) → Fin 4 → ℤ,
      (∀ ij∈P,
        A ij 0*A ij 3-A ij 1*A ij 2=1 ∧
        let t := (A ij 2:ℝ)*h ij.1.1+A ij 3
        t=(q ij.2.1:ℝ)/q ij.1.1 ∧ (1:ℝ)/2 ≤ t ∧ t ≤ 2 ∧
        ((A ij 0:ℝ)*h ij.1.1+A ij 1)/t=h ij.2.1 ∧
        |(A ij 2:ℝ)| ≤ (Q:ℝ)^2/(6*(K₀:ℝ)^2) ∧
        |μ ij.2.1/μ ij.1.1*t^3-1| ≤
          (16*U₀/μ₀)*Real.sqrt (U₀*(Q:ℝ)^3)*Real.sqrt K₀/(6*(K₀:ℝ)^2) ∧
        |τ ij.1.1 ij.1.2-τ ij.2.1 ij.2.2| ≤ D ∧
        (∃ e₁ e₂ : ℤ,
          let F₁ := 2*(round (z ij.2.1):ℝ)-2*(A ij 3:ℝ)*(round (z ij.1.1):ℝ)-
            (A ij 2:ℝ)*ℓ ij.1.1
          let F₂ := ℓ ij.2.1-2*(A ij 1:ℝ)*(round (z ij.1.1):ℝ)-
            (A ij 0:ℝ)*ℓ ij.1.1
          |F₁-e₁| ≤ (q ij.2.1:ℝ)/(6*(K₀:ℝ))+|(A ij 2:ℝ)|/q ij.1.1 ∧
          |(F₂-e₂)-h ij.2.1*(F₁-e₁)| ≤ 2*D/q ij.2.1) ∧
        ((Q:ℝ)^2/(6*(K₀:ℝ)^2) < 1 →
          A ij 2=0 ∧ q ij.1.1=q ij.2.1 ∧
            (q ij.1.1:ℤ) ∣ (r ij.2.1).num-(r ij.1.1).num)) ∧
      (∀ ij∈P, color ij.1.1=color ij.2.1 →
        let t := (A ij 2:ℝ)*h ij.1.1+A ij 3
        |t-1| ≤ δ ∧
        |((A ij 0:ℝ)*h ij.1.1+A ij 1)/h ij.1.1-1| ≤ δ ∧
        ((A ij 0=1 ∧ A ij 1=0 ∧ A ij 2=0 ∧ A ij 3=1) ∨
         (A ij 0=1 ∧ A ij 3=1 ∧ A ij 2=0 ∧ A ij 1≠0 ∧ |(A ij 1:ℝ)| ≤ δ*Hcurv) ∨
         (A ij 0=1 ∧ A ij 3=1 ∧ A ij 1=0 ∧ A ij 2≠0 ∧ |(A ij 2:ℝ)| ≤ δ/lambda) ∨
         (A ij 1≠0 ∧ A ij 2≠0)) ∧
        (|(A ij 2:ℝ)| * Hcurv ≤ L →
          A ij 0+A ij 3=2 ∧ (A ij 0-1)^2= -A ij 1*A ij 2)) ∧
      let E := P.filter (fun ij =>
        color ij.1.1=color ij.2.1 ∧
        ((A ij 0=1 ∧ A ij 1=0 ∧ A ij 2=0 ∧ A ij 3=1) ∨
         (A ij 1≠0 ∧ A ij 2≠0 ∧ |(A ij 2:ℝ)| * Hcurv ≤ L)))
      let Δ := (16*U₀/μ₀)*Real.sqrt (U₀*(Q:ℝ)^3)*Real.sqrt K₀/(6*(K₀:ℝ)^2)
      (E.card:ℝ) ≤ Dtype*((S.image Prod.fst).card:ℝ)*(M/(N:ℝ))*(1+Δ*Jsep) :=
  @double_difference_colored_fourier_cloud_type_one c U L hc hU hL

/-- One SAME actual Fourier-cloud witness supplies both source counts.
This composes the checked Type-I bridge with elementary triangular
enumeration, without rebuilding the analytic source jets. -/
private theorem double_difference_colored_fourier_cloud_type_one_and_triangular
    {c U L : ℝ} (hc : 0 < c) (hU : 0 < U) (hL : 0 ≤ L) :
    ∃ Dtype : ℝ, 0 < Dtype ∧
    ∀ (S : Finset (ℝ × ℤ)) (F rshift sshift : ℝ → ℝ)
      (z : (ℝ × ℤ) → ℝ) (r : (ℝ × ℤ) → ℚ) (v : (ℝ × ℤ) → ℤ)
      (Alen : (ℝ × ℤ) → ℕ) (Z : ℝ → ℤ)
      (Q K₀ N : ℕ) [NeZero K₀] (d Wmax T M Jsep : ℝ),
    (∀ u, 0 < u → ContDiffAt ℝ ∞ F u) →
    (∀ u∈Icc (1/2:ℝ) 3, c ≤ iteratedDeriv 5 F u) →
    (∀ u∈Icc (1/2:ℝ) 3, ∀ n, 1 ≤ n → n ≤ 7 → |iteratedDeriv n F u| ≤ U) →
    (∀ u∈Icc (1/2:ℝ) 3,
      c ≤ |(iteratedDeriv 5 F u)^2-iteratedDeriv 4 F u*iteratedDeriv 6 F u|) →
    (∀ u∈Icc (1/2:ℝ) 3, iteratedDeriv 4 F u ≤ -c) →
    0 < d → 0 ≤ Wmax → Wmax ≤ 1/4 → 2*U*Wmax ≤ c/64 →
    0 < T → 2 ≤ M → 0 < N → 0 < Q →
    0 < Jsep → (N:ℝ) ≤ M → Jsep ≤ M → Wmax*Jsep ≤ 1 →
    (∀ i∈S, i.1∈Icc (1:ℝ) 2) →
    (∀ i∈S, z i∈Icc M (2*M)) →
    (∀ i∈S, N ≤ Alen i ∧ Alen i ≤ 3*N ∧
      round (z i)+(Alen i:ℤ)=Z i.1+(N:ℤ)*i.2+2*(N:ℤ)) →
    (∀ i∈S, ∀ j∈S, i.1≠j.1 → 1 ≤ Jsep*|i.1-j.1|) →
    (∀ y∈S.image Prod.fst,
      0 ≤ rshift y ∧ 0 ≤ sshift y ∧ rshift y*sshift y=d*y ∧ rshift y+sshift y ≤ Wmax) →
    let Φ := fun y u =>
      (F u-F (u+rshift y)-F (u+sshift y)+F (u+rshift y+sshift y))/d
    let f := fun i : ℝ × ℤ => fun u => T*Φ i.1 (u/M)
    (∀ i∈S, iteratedDeriv 2 (f i) (z i)/2=(r i:ℝ)) →
    (∀ i∈S, (r i).den ≤ Q ∧ Q ≤ 2*(r i).den) →
    (∀ i∈S, ((r i).den:ℤ) ∣ (r i).num*v i-1) →
    let μ₀ := c*T/(12*M^3)
    let U₀ := U*T/(2*M^3)
    let q := fun i => (r i).den
    let μ := fun i => iteratedDeriv 3 (f i) (round (z i))/6
    let ℓ := fun i => deriv (f i) (round (z i))
    let b := fun i (p : Fin 2) => (⌊(q i:ℝ)*ℓ i⌋+(p:ℕ) : ℤ)
    let τ := fun i p => ((b i p:ℝ)-(q i:ℝ)*ℓ i)/2
    let K := fun i => -2*μ i*(Real.sqrt (2/(3*μ i*(q i:ℝ))))^3
    let x := fun i p =>
      (![-(v i:ℝ)*b i p/q i,-(v i:ℝ)/q i,K i,3*K i*τ i p/2] : Fin 4 → ℝ)
    let V := S ×ˢ (Finset.univ : Finset (Fin 2))
    let w := fun ip : (ℝ × ℤ) × Fin 2 =>
      (![Int.fract (x ip.1 ip.2 0),Int.fract (x ip.1 ip.2 1),
        x ip.1 ip.2 2/Real.sqrt K₀,x ip.1 ip.2 3/Real.sqrt K₀] : Fin 4 → ℝ)
    let radius : Fin 4 → ℝ :=
      ![1/(12*(K₀:ℝ)),1/(12*(K₀:ℝ)^2),(1/(K₀:ℝ)^2)/12,(1/(K₀:ℝ))/12]
    let P := (V ×ˢ V).filter (fun ij => ∀ d, |w ij.1 d-w ij.2 d| ≤ 2*radius d)
    let h := fun i => iteratedDeriv 2 (f i) (z i)/2
    let D := (Real.sqrt K₀/(9*(K₀:ℝ))+Real.sqrt K₀/(12*(K₀:ℝ)^2))*
      Real.sqrt (U₀*(Q:ℝ)^3)
    let δ := 1/(8*(L+3))
    let lambda := c*T/(2*M^2)
    let Hcurv := U*T/M^2
    let q₀ := (Q:ℝ)/2
    let p₀ := lambda*(Q:ℝ)/2
    let color := fun i => (⌊((r i).den:ℝ)/(δ*q₀)⌋,⌊((r i).num:ℝ)/(δ*p₀)⌋)
    let Cap := (4/δ+3)*(8*U/(c*δ)+3)
    ((S.image color).card:ℝ) ≤ Cap ∧
    (∀ coeff : (ℝ × ℤ) → ℂ, ‖∑ i∈S,coeff i‖^12 ≤ Cap^11*
      ∑ j∈S.image color, ‖∑ i∈S.filter (fun i => color i=j),coeff i‖^12) ∧
    ∃ A : (((ℝ × ℤ) × Fin 2) × ((ℝ × ℤ) × Fin 2)) → Fin 4 → ℤ,
      (∀ ij∈P,
        A ij 0*A ij 3-A ij 1*A ij 2=1 ∧
        let t := (A ij 2:ℝ)*h ij.1.1+A ij 3
        t=(q ij.2.1:ℝ)/q ij.1.1 ∧ (1:ℝ)/2 ≤ t ∧ t ≤ 2 ∧
        ((A ij 0:ℝ)*h ij.1.1+A ij 1)/t=h ij.2.1 ∧
        |(A ij 2:ℝ)| ≤ (Q:ℝ)^2/(6*(K₀:ℝ)^2) ∧
        |μ ij.2.1/μ ij.1.1*t^3-1| ≤
          (16*U₀/μ₀)*Real.sqrt (U₀*(Q:ℝ)^3)*Real.sqrt K₀/(6*(K₀:ℝ)^2) ∧
        |τ ij.1.1 ij.1.2-τ ij.2.1 ij.2.2| ≤ D ∧
        (∃ e₁ e₂ : ℤ,
          let F₁ := 2*(round (z ij.2.1):ℝ)-2*(A ij 3:ℝ)*(round (z ij.1.1):ℝ)-
            (A ij 2:ℝ)*ℓ ij.1.1
          let F₂ := ℓ ij.2.1-2*(A ij 1:ℝ)*(round (z ij.1.1):ℝ)-
            (A ij 0:ℝ)*ℓ ij.1.1
          |F₁-e₁| ≤ (q ij.2.1:ℝ)/(6*(K₀:ℝ))+|(A ij 2:ℝ)|/q ij.1.1 ∧
          |(F₂-e₂)-h ij.2.1*(F₁-e₁)| ≤ 2*D/q ij.2.1) ∧
        ((Q:ℝ)^2/(6*(K₀:ℝ)^2) < 1 →
          A ij 2=0 ∧ q ij.1.1=q ij.2.1 ∧
            (q ij.1.1:ℤ) ∣ (r ij.2.1).num-(r ij.1.1).num)) ∧
      (∀ ij∈P, color ij.1.1=color ij.2.1 →
        let t := (A ij 2:ℝ)*h ij.1.1+A ij 3
        |t-1| ≤ δ ∧
        |((A ij 0:ℝ)*h ij.1.1+A ij 1)/h ij.1.1-1| ≤ δ ∧
        ((A ij 0=1 ∧ A ij 1=0 ∧ A ij 2=0 ∧ A ij 3=1) ∨
         (A ij 0=1 ∧ A ij 3=1 ∧ A ij 2=0 ∧ A ij 1≠0 ∧ |(A ij 1:ℝ)| ≤ δ*Hcurv) ∨
         (A ij 0=1 ∧ A ij 3=1 ∧ A ij 1=0 ∧ A ij 2≠0 ∧ |(A ij 2:ℝ)| ≤ δ/lambda) ∨
         (A ij 1≠0 ∧ A ij 2≠0)) ∧
        (|(A ij 2:ℝ)| * Hcurv ≤ L →
          A ij 0+A ij 3=2 ∧ (A ij 0-1)^2= -A ij 1*A ij 2)) ∧
      let E := P.filter (fun ij =>
        color ij.1.1=color ij.2.1 ∧
        ((A ij 0=1 ∧ A ij 1=0 ∧ A ij 2=0 ∧ A ij 3=1) ∨
         (A ij 1≠0 ∧ A ij 2≠0 ∧ |(A ij 2:ℝ)| * Hcurv ≤ L)))
      let Δ := (16*U₀/μ₀)*Real.sqrt (U₀*(Q:ℝ)^3)*Real.sqrt K₀/(6*(K₀:ℝ)^2)
      (E.card:ℝ) ≤ Dtype*((S.image Prod.fst).card:ℝ)*(M/(N:ℝ))*(1+Δ*Jsep) ∧
      let Etri := P.filter (fun ij =>
        color ij.1.1=color ij.2.1 ∧ (A ij 2=0 ∨ A ij 1=0))
      (Etri.card:ℝ) ≤ Dtype*(1+δ*(Hcurv+1/lambda))*
        ((S.image Prod.fst).card:ℝ)*(M/(N:ℝ))*(1+Δ*Jsep) := by
  obtain ⟨Dtype,hDtype,hsource⟩ := double_difference_colored_fourier_cloud_type_one hc hU hL
  obtain ⟨Dtri,hDtri,htri⟩ := double_difference_triangular_pair_source_scale hc hU
  have hDsmall : Dtype ≤ Dtype+Dtri := by linarith only [hDtri]
  have hDtrismall : Dtri ≤ Dtype+Dtri := by linarith only [hDtype]
  refine ⟨Dtype+Dtri,add_pos hDtype hDtri,?_⟩
  intro S F rshift sshift z r v Alen Z Q K₀ N instK d Wmax T M Jsep
    hf hlower hbound hdet hnegative hd hw hwcap hsmall hT hM hN hQ
    hJsep hNM hJM hwJ hy hz hgeometry hsep hshifts Φ f hlevel hden hinv
    μ₀ U₀ q μ ℓ b τ K x V w radius P h D δ lambda Hcurv q₀ p₀ color Cap
  classical
  have hMp : 0 < M := by linarith only [hM]
  have hδ : 0 < δ := by dsimp only [δ]; positivity
  have hlambda : 0 < lambda := by dsimp only [lambda]; positivity
  have hHcurv : 0 < Hcurv := by dsimp only [Hcurv]; positivity
  obtain ⟨hcard,hholder,A,hA,hclass,hTypeI⟩ :=
    hsource S F rshift sshift z r v Alen Z Q K₀ N d Wmax T M Jsep
      hf hlower hbound hdet hnegative hd hw hwcap hsmall hT hM hN hQ
      hJsep hNM hJM hwJ hy hz hgeometry hsep hshifts hlevel hden hinv
  refine ⟨hcard,hholder,A,hA,hclass,?_⟩
  intro E Δ
  have hΔ : 0 ≤ Δ := by dsimp only [Δ,U₀,μ₀]; positivity
  have hpoints ij (hij : ij∈P) : ij.1.1∈S ∧ ij.2.1∈S := by
    have hh := Finset.mem_product.mp (Finset.mem_filter.mp hij).1
    exact ⟨(Finset.mem_product.mp hh.1).1,(Finset.mem_product.mp hh.2).1⟩
  constructor
  · have hsize : (0:ℝ) ≤ (S.image Prod.fst).card := Nat.cast_nonneg _
    have hscale : 0 ≤ M/(N:ℝ) := div_nonneg hMp.le (Nat.cast_nonneg _)
    have hlast : 0 ≤ 1+Δ*Jsep := by positivity
    have hb := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hDsmall hsize) hscale) hlast
    exact hTypeI.trans hb
  · intro Etri
    have hmemtri ij (hij : ij∈Etri) :
        ij∈P ∧ color ij.1.1=color ij.2.1 ∧ (A ij 2=0 ∨ A ij 1=0) :=
      Finset.mem_filter.mp hij
    have hB : 0 ≤ δ*(Hcurv+1/lambda) := by positivity
    have hbupper : δ*Hcurv ≤ δ*(Hcurv+1/lambda) := by
      have hh : 0 ≤ δ/lambda := by positivity
      calc
        δ*Hcurv ≤ δ*Hcurv+δ/lambda := le_add_of_nonneg_right hh
        _ = _ := by ring
    have hblower : δ/lambda ≤ δ*(Hcurv+1/lambda) := by
      have hh : 0 ≤ δ*Hcurv := by positivity
      calc
        δ/lambda ≤ δ*Hcurv+δ/lambda := le_add_of_nonneg_left hh
        _ = _ := by ring
    have hbranches ij (hij : ij∈Etri) : A ij 0=1 ∧ A ij 3=1 ∧
        ((A ij 2=0 ∧ |(A ij 1:ℝ)| ≤ δ*(Hcurv+1/lambda)) ∨
         (A ij 1=0 ∧ |(A ij 2:ℝ)| ≤ δ*(Hcurv+1/lambda))) := by
      have hm := hmemtri ij hij
      have hc := (hclass ij hm.1 hm.2.1).2.2.1
      rcases hc with hi | hu | hl | hn
      · refine ⟨hi.1,hi.2.2.2,Or.inl ⟨hi.2.2.1,?_⟩⟩
        simpa only [hi.2.1,Int.cast_zero,abs_zero] using hB
      · exact ⟨hu.1,hu.2.1,Or.inl ⟨hu.2.2.1,hu.2.2.2.2.trans hbupper⟩⟩
      · exact ⟨hl.1,hl.2.1,Or.inr ⟨hl.2.2.1,hl.2.2.2.2.trans hblower⟩⟩
      · rcases hm.2.2 with he | he
        · exact False.elim (hn.2 he)
        · exact False.elim (hn.1 he)
    have hh := htri Etri A F rshift sshift (fun a k => z (a,k)) (fun a k => Alen (a,k))
      N Z d Wmax Δ Jsep T M (δ*(Hcurv+1/lambda)) hf hlower hbound hdet
      hd hw hwcap hsmall hT hM hN hΔ hJsep hNM hJM hwJ hB
      (by
        intro ij hij
        have hp := hpoints ij (hmemtri ij hij).1
        exact ⟨⟨hy _ hp.1,hz _ hp.1⟩,⟨hy _ hp.2,hz _ hp.2⟩⟩)
      (fun ij hij => hgeometry _ (hpoints ij (hmemtri ij hij).1).1)
      (fun ij hij => hgeometry _ (hpoints ij (hmemtri ij hij).1).2)
      (fun ij hij kl hkl hne =>
        hsep _ (hpoints ij (hmemtri ij hij).1).2 _ (hpoints kl (hmemtri kl hkl).1).2 hne)
      (by
        intro y hy'
        apply hshifts y
        rcases Finset.mem_union.mp hy' with hy' | hy'
        · obtain ⟨ij,hij,rfl⟩ := Finset.mem_image.mp hy'
          exact Finset.mem_image_of_mem Prod.fst (hpoints ij (hmemtri ij hij).1).1
        · obtain ⟨ij,hij,rfl⟩ := Finset.mem_image.mp hy'
          exact Finset.mem_image_of_mem Prod.fst (hpoints ij (hmemtri ij hij).1).2)
      hbranches
      (fun ij hij => ⟨(hA ij (hmemtri ij hij).1).2.2.1,(hA ij (hmemtri ij hij).1).2.2.2.1⟩)
      (fun ij hij => (hA ij (hmemtri ij hij).1).2.2.2.2.1)
      (fun ij hij => (hA ij (hmemtri ij hij).1).2.2.2.2.2.2.1)
    have hsub : Etri.image (fun ij => ij.1.1.1) ⊆ S.image Prod.fst := by
      intro a ha
      obtain ⟨ij,hij,rfl⟩ := Finset.mem_image.mp ha
      exact Finset.mem_image_of_mem Prod.fst (hpoints ij (hmemtri ij hij).1).1
    have hI : ((Etri.image (fun ij => ij.1.1.1)).card:ℝ) ≤ ((S.image Prod.fst).card:ℝ) := by
      exact_mod_cast Finset.card_le_card hsub
    have hfactor : 0 ≤ 1+δ*(Hcurv+1/lambda) := by positivity
    have hconst := mul_le_mul_of_nonneg_right hDtrismall hfactor
    have hprod := mul_le_mul hconst hI (Nat.cast_nonneg _) (by positivity)
    exact hh.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hprod (div_nonneg hMp.le (Nat.cast_nonneg _))) (by positivity))

#print axioms double_difference_colored_fourier_cloud_type_one_and_triangular

example
    {c U L : ℝ} (hc : 0 < c) (hU : 0 < U) (hL : 0 ≤ L) :
    ∃ Dtype : ℝ, 0 < Dtype ∧
    ∀ (S : Finset (ℝ × ℤ)) (F rshift sshift : ℝ → ℝ)
      (z : (ℝ × ℤ) → ℝ) (r : (ℝ × ℤ) → ℚ) (v : (ℝ × ℤ) → ℤ)
      (Alen : (ℝ × ℤ) → ℕ) (Z : ℝ → ℤ)
      (Q K₀ N : ℕ) [NeZero K₀] (d Wmax T M Jsep : ℝ),
    (∀ u, 0 < u → ContDiffAt ℝ ∞ F u) →
    (∀ u∈Icc (1/2:ℝ) 3, c ≤ iteratedDeriv 5 F u) →
    (∀ u∈Icc (1/2:ℝ) 3, ∀ n, 1 ≤ n → n ≤ 7 → |iteratedDeriv n F u| ≤ U) →
    (∀ u∈Icc (1/2:ℝ) 3,
      c ≤ |(iteratedDeriv 5 F u)^2-iteratedDeriv 4 F u*iteratedDeriv 6 F u|) →
    (∀ u∈Icc (1/2:ℝ) 3, iteratedDeriv 4 F u ≤ -c) →
    0 < d → 0 ≤ Wmax → Wmax ≤ 1/4 → 2*U*Wmax ≤ c/64 →
    0 < T → 2 ≤ M → 0 < N → 0 < Q →
    0 < Jsep → (N:ℝ) ≤ M → Jsep ≤ M → Wmax*Jsep ≤ 1 →
    (∀ i∈S, i.1∈Icc (1:ℝ) 2) →
    (∀ i∈S, z i∈Icc M (2*M)) →
    (∀ i∈S, N ≤ Alen i ∧ Alen i ≤ 3*N ∧
      round (z i)+(Alen i:ℤ)=Z i.1+(N:ℤ)*i.2+2*(N:ℤ)) →
    (∀ i∈S, ∀ j∈S, i.1≠j.1 → 1 ≤ Jsep*|i.1-j.1|) →
    (∀ y∈S.image Prod.fst,
      0 ≤ rshift y ∧ 0 ≤ sshift y ∧ rshift y*sshift y=d*y ∧ rshift y+sshift y ≤ Wmax) →
    let Φ := fun y u =>
      (F u-F (u+rshift y)-F (u+sshift y)+F (u+rshift y+sshift y))/d
    let f := fun i : ℝ × ℤ => fun u => T*Φ i.1 (u/M)
    (∀ i∈S, iteratedDeriv 2 (f i) (z i)/2=(r i:ℝ)) →
    (∀ i∈S, (r i).den ≤ Q ∧ Q ≤ 2*(r i).den) →
    (∀ i∈S, ((r i).den:ℤ) ∣ (r i).num*v i-1) →
    let μ₀ := c*T/(12*M^3)
    let U₀ := U*T/(2*M^3)
    let q := fun i => (r i).den
    let μ := fun i => iteratedDeriv 3 (f i) (round (z i))/6
    let ℓ := fun i => deriv (f i) (round (z i))
    let b := fun i (p : Fin 2) => (⌊(q i:ℝ)*ℓ i⌋+(p:ℕ) : ℤ)
    let τ := fun i p => ((b i p:ℝ)-(q i:ℝ)*ℓ i)/2
    let K := fun i => -2*μ i*(Real.sqrt (2/(3*μ i*(q i:ℝ))))^3
    let x := fun i p =>
      (![-(v i:ℝ)*b i p/q i,-(v i:ℝ)/q i,K i,3*K i*τ i p/2] : Fin 4 → ℝ)
    let V := S ×ˢ (Finset.univ : Finset (Fin 2))
    let w := fun ip : (ℝ × ℤ) × Fin 2 =>
      (![Int.fract (x ip.1 ip.2 0),Int.fract (x ip.1 ip.2 1),
        x ip.1 ip.2 2/Real.sqrt K₀,x ip.1 ip.2 3/Real.sqrt K₀] : Fin 4 → ℝ)
    let radius : Fin 4 → ℝ :=
      ![1/(12*(K₀:ℝ)),1/(12*(K₀:ℝ)^2),(1/(K₀:ℝ)^2)/12,(1/(K₀:ℝ))/12]
    let P := (V ×ˢ V).filter (fun ij => ∀ d, |w ij.1 d-w ij.2 d| ≤ 2*radius d)
    let h := fun i => iteratedDeriv 2 (f i) (z i)/2
    let D := (Real.sqrt K₀/(9*(K₀:ℝ))+Real.sqrt K₀/(12*(K₀:ℝ)^2))*
      Real.sqrt (U₀*(Q:ℝ)^3)
    let δ := 1/(8*(L+3))
    let lambda := c*T/(2*M^2)
    let Hcurv := U*T/M^2
    let q₀ := (Q:ℝ)/2
    let p₀ := lambda*(Q:ℝ)/2
    let color := fun i => (⌊((r i).den:ℝ)/(δ*q₀)⌋,⌊((r i).num:ℝ)/(δ*p₀)⌋)
    let Cap := (4/δ+3)*(8*U/(c*δ)+3)
    ((S.image color).card:ℝ) ≤ Cap ∧
    (∀ coeff : (ℝ × ℤ) → ℂ, ‖∑ i∈S,coeff i‖^12 ≤ Cap^11*
      ∑ j∈S.image color, ‖∑ i∈S.filter (fun i => color i=j),coeff i‖^12) ∧
    ∃ A : (((ℝ × ℤ) × Fin 2) × ((ℝ × ℤ) × Fin 2)) → Fin 4 → ℤ,
      (∀ ij∈P,
        A ij 0*A ij 3-A ij 1*A ij 2=1 ∧
        let t := (A ij 2:ℝ)*h ij.1.1+A ij 3
        t=(q ij.2.1:ℝ)/q ij.1.1 ∧ (1:ℝ)/2 ≤ t ∧ t ≤ 2 ∧
        ((A ij 0:ℝ)*h ij.1.1+A ij 1)/t=h ij.2.1 ∧
        |(A ij 2:ℝ)| ≤ (Q:ℝ)^2/(6*(K₀:ℝ)^2) ∧
        |μ ij.2.1/μ ij.1.1*t^3-1| ≤
          (16*U₀/μ₀)*Real.sqrt (U₀*(Q:ℝ)^3)*Real.sqrt K₀/(6*(K₀:ℝ)^2) ∧
        |τ ij.1.1 ij.1.2-τ ij.2.1 ij.2.2| ≤ D ∧
        (∃ e₁ e₂ : ℤ,
          let F₁ := 2*(round (z ij.2.1):ℝ)-2*(A ij 3:ℝ)*(round (z ij.1.1):ℝ)-
            (A ij 2:ℝ)*ℓ ij.1.1
          let F₂ := ℓ ij.2.1-2*(A ij 1:ℝ)*(round (z ij.1.1):ℝ)-
            (A ij 0:ℝ)*ℓ ij.1.1
          |F₁-e₁| ≤ (q ij.2.1:ℝ)/(6*(K₀:ℝ))+|(A ij 2:ℝ)|/q ij.1.1 ∧
          |(F₂-e₂)-h ij.2.1*(F₁-e₁)| ≤ 2*D/q ij.2.1) ∧
        ((Q:ℝ)^2/(6*(K₀:ℝ)^2) < 1 →
          A ij 2=0 ∧ q ij.1.1=q ij.2.1 ∧
            (q ij.1.1:ℤ) ∣ (r ij.2.1).num-(r ij.1.1).num)) ∧
      (∀ ij∈P, color ij.1.1=color ij.2.1 →
        let t := (A ij 2:ℝ)*h ij.1.1+A ij 3
        |t-1| ≤ δ ∧
        |((A ij 0:ℝ)*h ij.1.1+A ij 1)/h ij.1.1-1| ≤ δ ∧
        ((A ij 0=1 ∧ A ij 1=0 ∧ A ij 2=0 ∧ A ij 3=1) ∨
         (A ij 0=1 ∧ A ij 3=1 ∧ A ij 2=0 ∧ A ij 1≠0 ∧ |(A ij 1:ℝ)| ≤ δ*Hcurv) ∨
         (A ij 0=1 ∧ A ij 3=1 ∧ A ij 1=0 ∧ A ij 2≠0 ∧ |(A ij 2:ℝ)| ≤ δ/lambda) ∨
         (A ij 1≠0 ∧ A ij 2≠0)) ∧
        (|(A ij 2:ℝ)| * Hcurv ≤ L →
          A ij 0+A ij 3=2 ∧ (A ij 0-1)^2= -A ij 1*A ij 2)) ∧
      let E := P.filter (fun ij =>
        color ij.1.1=color ij.2.1 ∧
        ((A ij 0=1 ∧ A ij 1=0 ∧ A ij 2=0 ∧ A ij 3=1) ∨
         (A ij 1≠0 ∧ A ij 2≠0 ∧ |(A ij 2:ℝ)| * Hcurv ≤ L)))
      let Δ := (16*U₀/μ₀)*Real.sqrt (U₀*(Q:ℝ)^3)*Real.sqrt K₀/(6*(K₀:ℝ)^2)
      (E.card:ℝ) ≤ Dtype*((S.image Prod.fst).card:ℝ)*(M/(N:ℝ))*(1+Δ*Jsep) ∧
      let Etri := P.filter (fun ij =>
        color ij.1.1=color ij.2.1 ∧ (A ij 2=0 ∨ A ij 1=0))
      (Etri.card:ℝ) ≤ Dtype*(1+δ*(Hcurv+1/lambda))*
        ((S.image Prod.fst).card:ℝ)*(M/(N:ℝ))*(1+Δ*Jsep) :=
  @double_difference_colored_fourier_cloud_type_one_and_triangular c U L hc hU hL

/-- Exact all-product-block scale feasibility for elementary triangular
counting with clamped Fourier narrowing. The M^207 and M^268 terms
retain the extra source rescaling; this is NOT an analytic moment bound. -/
private theorem short_row_three_clamped_triangular_scales {α : ℝ}
    (hlo : (890:ℝ)/3277 ≤ α) (hhi : α ≤ (199:ℝ)/716) :
    let t := (α-(890:ℝ)/3277)/((199:ℝ)/716-(890:ℝ)/3277)
    let ν := (1-t)*(121373:ℝ)/1000000+t*(130455:ℝ)/1000000
    let h := (1-t)*(27201:ℝ)/1000000+t*(29341:ℝ)/1000000
    let β := (89+2243*α)/2706
    ∀ g : ℝ, g ≤ 3*h →
      1+g+1/10000 ≤ 4*α ∧
      1+g+2*ν+1/10000 ≤ 5*α ∧
      3+3*g+11*ν+1/10000 ≤ 17*α ∧
      7+7*g+27*ν+1/10000 ≤ 41*α ∧
      288*α-144*h+1/10000 ≤ 288*β ∧
      288*α-36*ν+72*g-216*h+1/10000 ≤ 288*β ∧
      648*α-72-216*h-216*ν+1/10000 ≤ 288*β ∧
      24+96*g-216*h+96*α+144*ν+1/10000 ≤ 288*β ∧
      21+87*g-216*h+177*α+33*ν+1/10000 ≤ 288*β ∧
      15+87*g-216*h+207*α+15*ν+1/10000 ≤ 288*β ∧
      12+78*g-216*h+216*α+24*ν+1/10000 ≤ 288*β ∧
      6+78*g-216*h+246*α+6*ν+1/10000 ≤ 288*β ∧
      4+76*g-216*h+268*α-24*ν+1/10000 ≤ 288*β ∧
      72*g-216*h+284*α-24*ν+1/10000 ≤ 288*β := by
  intro t ν h β g hg
  dsimp only [t,ν,h,β] at hg ⊢
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩ <;>
    norm_num at * <;> linarith only [hlo,hhi,hg]

#print axioms short_row_three_clamped_triangular_scales

example {α : ℝ}
    (hlo : (890:ℝ)/3277 ≤ α) (hhi : α ≤ (199:ℝ)/716) :
    let t := (α-(890:ℝ)/3277)/((199:ℝ)/716-(890:ℝ)/3277)
    let ν := (1-t)*(121373:ℝ)/1000000+t*(130455:ℝ)/1000000
    let h := (1-t)*(27201:ℝ)/1000000+t*(29341:ℝ)/1000000
    let β := (89+2243*α)/2706
    ∀ g : ℝ, g ≤ 3*h →
      1+g+1/10000 ≤ 4*α ∧
      1+g+2*ν+1/10000 ≤ 5*α ∧
      3+3*g+11*ν+1/10000 ≤ 17*α ∧
      7+7*g+27*ν+1/10000 ≤ 41*α ∧
      288*α-144*h+1/10000 ≤ 288*β ∧
      288*α-36*ν+72*g-216*h+1/10000 ≤ 288*β ∧
      648*α-72-216*h-216*ν+1/10000 ≤ 288*β ∧
      24+96*g-216*h+96*α+144*ν+1/10000 ≤ 288*β ∧
      21+87*g-216*h+177*α+33*ν+1/10000 ≤ 288*β ∧
      15+87*g-216*h+207*α+15*ν+1/10000 ≤ 288*β ∧
      12+78*g-216*h+216*α+24*ν+1/10000 ≤ 288*β ∧
      6+78*g-216*h+246*α+6*ν+1/10000 ≤ 288*β ∧
      4+76*g-216*h+268*α-24*ν+1/10000 ≤ 288*β ∧
      72*g-216*h+284*α-24*ν+1/10000 ≤ 288*β :=
  @short_row_three_clamped_triangular_scales α hlo hhi

/-- The clamped narrowing pays for elementary triangular enumeration
while retaining the existing large-entry V^(-5/3) decay. The large-sieve
factor V is INCLUDED; it is not silently discarded. -/
private theorem clamped_narrowing_source_costs
    {H N Q C a b Uref : ℝ}
    (hH : 0 < H) (hHcap : H ≤ 1) (hN : 0 < N) (hQ : 0 < Q)
    (hC : 0 ≤ C) (ha : 0 ≤ a) (hU : 0 < Uref) :
    let V := max 1 (H*N/Q)
    1 ≤ V ∧
      V*(1+C*(H+1/H)) ≤ (1+2*C)*(1/H+N/Q) ∧
      V*(a/V^((5:ℝ)/3)+b/(Uref*V)) ≤
        a*(Q/(H*N))^((2:ℝ)/3)+b/Uref := by
  intro V
  have hprod : 0 < H*N/Q := by positivity
  have hVone : 1 ≤ V := le_max_left _ _
  have hVprod : H*N/Q ≤ V := le_max_right _ _
  have hVp : 0 < V := zero_lt_one.trans_le hVone
  have hVupper : V ≤ 1+H*N/Q :=
    max_le (by linarith only [hprod]) (by linarith)
  have hInv : 1 ≤ 1/H := (le_div_iff₀ hH).mpr (by simpa only [one_mul] using hHcap)
  have hFactor : 1+C*(H+1/H) ≤ (1+2*C)/H := by
    have hh := mul_le_mul_of_nonneg_left (hHcap.trans hInv) hC
    calc
      _ ≤ 1+C*(1/H+1/H) := by linarith only [hh]
      _ ≤ 1/H+C*(1/H+1/H) := by linarith only [hInv]
      _ = _ := by ring
  refine ⟨hVone,?_,?_⟩
  · calc
      _ ≤ (1+H*N/Q)*((1+2*C)/H) :=
        mul_le_mul hVupper hFactor (by positivity) (by positivity)
      _ = _ := by field_simp
  · have he : V^((5:ℝ)/3)=V*V^((2:ℝ)/3) := by
      rw [show (5:ℝ)/3=1+2/3 by norm_num,Real.rpow_add hVp,Real.rpow_one]
    have hc : a/V^((2:ℝ)/3) ≤ a*(Q/(H*N))^((2:ℝ)/3) := by
      calc
        _ ≤ a/(H*N/Q)^((2:ℝ)/3) :=
          div_le_div_of_nonneg_left ha (Real.rpow_pos_of_pos hprod _)
            (Real.rpow_le_rpow hprod.le hVprod (by norm_num))
        _ = _ := by
          rw [div_eq_mul_inv,←Real.inv_rpow hprod.le,inv_div]
    calc
      _ = a/V^((2:ℝ)/3)+b/Uref := by rw [he]; field_simp
      _ ≤ _ := add_le_add hc le_rfl

#print axioms clamped_narrowing_source_costs

example
    {H N Q C a b Uref : ℝ}
    (hH : 0 < H) (hHcap : H ≤ 1) (hN : 0 < N) (hQ : 0 < Q)
    (hC : 0 ≤ C) (ha : 0 ≤ a) (hU : 0 < Uref) :
    let V := max 1 (H*N/Q)
    1 ≤ V ∧
      V*(1+C*(H+1/H)) ≤ (1+2*C)*(1/H+N/Q) ∧
      V*(a/V^((5:ℝ)/3)+b/(Uref*V)) ≤
        a*(Q/(H*N))^((2:ℝ)/3)+b/Uref :=
  @clamped_narrowing_source_costs H N Q C a b Uref hH hHcap hN hQ hC ha hU


/-! Reuse of four existing private budget proofs while testing the arbitrary-V
consumer. These copies are scratch-only; promotion must reuse the originals. -/
open HuxleyRationalPhase

private theorem eventually_reference_chart_majorants
    {Ch Cc ε : ℝ} (hCh : 1 ≤ Ch) (hCc : 1 ≤ Cc) (hε : 0 < ε) :
    ∀ᶠ T : ℝ in Filter.atTop,
    let Bmajor := 6+216*(⌊Real.logb 2 ((Ch*T^3)^2)⌋₊+1)
    let Cmajor := ⌊Real.logb (5/4) (Cc*T)⌋₊+1
    ((6+Cmajor*(105+544*Bmajor):ℕ):ℝ) ≤ T^ε := by
  let Kb : ℝ := 222+1728/Real.log 2
  let Kc : ℝ := 1+2/Real.log (5/4)
  let K : ℝ := 6+Kc*(105+544*Kb)
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlc : 0 < Real.log (5/4) := Real.log_pos (by norm_num)
  have hKb : 0 ≤ Kb := by dsimp only [Kb]; positivity
  have hKc : 0 ≤ Kc := by dsimp only [Kc]; positivity
  have hK : 0 ≤ K := by dsimp only [K]; positivity
  filter_upwards [eventually_const_log_pow_le_rpow K hK 2 hε,
    Filter.eventually_ge_atTop Ch, Filter.eventually_ge_atTop Cc,
    Filter.eventually_ge_atTop (1:ℝ),
    Real.tendsto_log_atTop.eventually_ge_atTop 1] with T hsmall hh hc hT hlogT
  dsimp only
  have hTp : 0 < T := zero_lt_one.trans_le hT
  have hheight1 : 1 ≤ Ch*T^3 := one_le_mul_of_one_le_of_one_le hCh (one_le_pow₀ hT)
  have hheight : (Ch*T^3)^2 ≤ T^8 := by
    calc
      _ ≤ (T*T^3)^2 := pow_le_pow_left₀ (by positivity)
        (mul_le_mul_of_nonneg_right hh (by positivity)) 2
      _ = _ := by ring
  have hlogh := Real.logb_le_logb_of_le (by norm_num : (1:ℝ)<2)
    (by positivity : 0 < (Ch*T^3)^2) hheight
  rw [Real.logb_pow 2 T 8] at hlogh
  have hfloorh := Nat.floor_le (Real.logb_nonneg (by norm_num : (1:ℝ)<2)
    (one_le_pow₀ hheight1 : 1 ≤ (Ch*T^3)^2))
  have hB : ((6+216*(⌊Real.logb 2 ((Ch*T^3)^2)⌋₊+1):ℕ):ℝ) ≤ Kb*Real.log T := by
    have he : Kb*Real.log T=222*Real.log T+216*(8*Real.logb 2 T) := by
      dsimp only [Kb,Real.logb]
      ring
    rw [he]
    push_cast
    norm_num only [Nat.cast_ofNat] at hlogh
    linarith only [hfloorh,hlogh,hlogT]
  have hchart1 : 1 ≤ Cc*T := one_le_mul_of_one_le_of_one_le hCc hT
  have hchart : Cc*T ≤ T^2 := by nlinarith only [mul_le_mul_of_nonneg_right hc hTp.le]
  have hlogc := Real.logb_le_logb_of_le (by norm_num : (1:ℝ)<5/4)
    (zero_lt_one.trans_le hchart1) hchart
  rw [Real.logb_pow] at hlogc
  have hfloorc := Nat.floor_le (Real.logb_nonneg (by norm_num : (1:ℝ)<5/4) hchart1)
  have hC : ((⌊Real.logb (5/4) (Cc*T)⌋₊+1:ℕ):ℝ) ≤ Kc*Real.log T := by
    have he : Kc*Real.log T=Real.log T+2*Real.logb (5/4) T := by
      dsimp only [Kc,Real.logb]
      ring
    rw [he]
    push_cast
    norm_num only [Nat.cast_ofNat] at hlogc
    linarith only [hfloorc,hlogc,hlogT]
  have hinner : 105+544*((6+216*(⌊Real.logb 2 ((Ch*T^3)^2)⌋₊+1):ℕ):ℝ) ≤
      (105+544*Kb)*Real.log T := by linarith only [hB,hlogT]
  have hmul := mul_le_mul hC hinner (by positivity) (mul_nonneg hKc (by linarith only [hlogT]))
  have hlogsq : 1 ≤ (Real.log T)^2 := one_le_pow₀ hlogT
  have hcost : ((6+(⌊Real.logb (5/4) (Cc*T)⌋₊+1)*
      (105+544*(6+216*(⌊Real.logb 2 ((Ch*T^3)^2)⌋₊+1))):ℕ):ℝ) ≤ K*(Real.log T)^2 := by
    push_cast
    dsimp only [K]
    push_cast at hmul
    nlinarith only [hmul,hlogsq]
  exact hcost.trans hsmall

private theorem physical_reference_chart_ratio
    {κ Cp R U d : ℝ} (hκ : 0 < κ) (hCp : 0 < Cp+2) (hR : 0 < R)
    (hd : d ≤ 7*U/(2*R^2)) :
    d/(12*(κ/(16*(Cp+2)*R^2))) ≤ ((14:ℝ)/3)*(Cp+2)/κ*U := by
  have hh := div_le_div_of_nonneg_right hd
    (by positivity : 0 ≤ 12*(κ/(16*(Cp+2)*R^2)))
  apply hh.trans_eq
  field_simp
  ring

private theorem physical_reference_radius_le_source
    {T M N R Q : ℝ} (hT : 0 < T) (hM : 0 < M) (hR : 1 ≤ R)
    (hRQ : R ≤ Q) (hQN : Q ≤ N) (hNM : N^2 ≤ M)
    (hscale : T*N*R^2=M^3) : R^2 ≤ T := by
  have hN : 1 ≤ N := hR.trans (hRQ.trans hQN)
  have hNM' : N ≤ M := (by nlinarith only [hN] : N ≤ N^2).trans hNM
  have hR₂ : R^2 ≤ M :=
    (pow_le_pow_left₀ (zero_le_one.trans hR) (hRQ.trans hQN) 2).trans hNM
  have hprod : N*R^2 ≤ M^2 := by
    calc
      _ ≤ M*M := mul_le_mul hNM' hR₂ (sq_nonneg R) hM.le
      _ = _ := by ring
  have hMT : M ≤ T := by
    apply (mul_le_mul_iff_left₀ (sq_pos_of_pos hM)).mp
    calc
      M*M^2 = M^3 := by ring
      _ = T*(N*R^2) := by nlinarith only [hscale]
      _ ≤ T*M^2 := mul_le_mul_of_nonneg_left hprod hT.le
  exact hR₂.trans hMT

/-- Common logarithmic budgets are constructed from the actual physical
reference labels and gap widths. The asymptotic threshold depends only
on the fixed model and height constants, not on the finite reference system. -/
private theorem eventually_physical_reference_chart_budgets
    {σ Jref εloss : ℝ} (hσ : 0 < σ) (hJref : 0 ≤ Jref) (hεloss : 0 < εloss) :
    ∀ᶠ T : ℝ in Filter.atTop, ∀
    (Gaps : Finset (ℝ × ℝ)) (e r v s : ℝ × ℝ → ℤ) (Q Uref : ℕ)
    {δ M N R : ℝ},
    0 ≤ δ → δ ≤ 1 → 0 < T → 0 < M → 1 ≤ R →
    R ≤ (Q:ℝ) → (Q:ℝ) ≤ N → N^2 ≤ M →
    1 ≤ Uref → (Uref:ℝ) ≤ R^2 → T*N*R^2=M^3 →
    (∀ ab∈Gaps, |((r ab):ℝ)| ≤ 4*R^2/(Uref:ℝ)) →
    (∀ ab∈Gaps, |((s ab):ℝ)| ≤ 4*R^2/(Uref:ℝ)) →
    (∀ ab∈Gaps, |((e ab):ℝ)| ≤
      (3*Jref*T/(2*σ*M^2)+1)*(4*R^2/(Uref:ℝ))) →
    (∀ ab∈Gaps, |((v ab):ℝ)| ≤
      (3*Jref*T/(2*σ*M^2)+1)*(4*R^2/(Uref:ℝ))) →
    (∀ ab∈Gaps, ab.1 < ab.2 ∧ ab.2-ab.1 ≤ 7*(Uref:ℝ)/(2*R^2)) →
    let Vheight := T*(modelPhaseJetCoefficient σ 1+δ)/(2*M^2)
    let P₁ := fun ab => 1+(|((v ab):ℝ)|+|((s ab):ℝ)| *Vheight)*(Q:ℝ)
    let P₂ := fun ab => 1+(|((r ab):ℝ)| *Vheight+|((e ab):ℝ)|)*(Q:ℝ)
    let εchart := modelPhaseThirdLower σ/(16*(σ*(σ+1)+1+2)*R^2)
    ∃ Bmajor Cmajor : ℕ,
      (∀ ab∈Gaps, 6+216*(⌊Real.logb 2 (P₁ ab*P₂ ab)⌋₊+1) ≤ Bmajor) ∧
      (∀ ab∈Gaps, ⌊Real.logb (5/4) ((ab.2-ab.1)/(12*εchart))⌋₊+1 ≤ Cmajor) ∧
      ((6+Cmajor*(105+544*Bmajor):ℕ):ℝ) ≤ T^εloss := by
  let Jv := modelPhaseJetCoefficient σ 1+1
  let Ch := 1+4*(3*Jref/(2*σ)+1+Jv/2)
  let κ := modelPhaseThirdLower σ
  let Cp := σ*(σ+1)+1
  let Cc := 1+((14:ℝ)/3)*(Cp+2)/κ
  have hJv : 0 ≤ Jv := add_nonneg (modelPhaseJetCoefficient_nonneg σ 1) zero_le_one
  have hκ : 0 < κ := modelPhaseThirdLower_pos hσ
  have hCp : 0 < Cp+2 := by dsimp only [Cp]; positivity
  have hCh : 1 ≤ Ch := by dsimp only [Ch]; exact le_add_of_nonneg_right (by positivity)
  have hCc : 1 ≤ Cc := by dsimp only [Cc]; exact le_add_of_nonneg_right (by positivity)
  filter_upwards [eventually_reference_chart_majorants hCh hCc hεloss,
    Filter.eventually_ge_atTop (1:ℝ)] with T hmajor hT1
  intro Gaps e r v s Q Uref δ M N R hδ₀ hδmax hT hM hR hRQ hQN hNM
    hU hUR hscale hr hs he hv hgap Vheight P₁ P₂ εchart
  let Bmajor := 6+216*(⌊Real.logb 2 ((Ch*T^3)^2)⌋₊+1)
  let Cmajor := ⌊Real.logb (5/4) (Cc*T)⌋₊+1
  have hRp : 0 < R := zero_lt_one.trans_le hR
  have hUr : (1:ℝ) ≤ Uref := by exact_mod_cast hU
  have hV₀ : 0 ≤ Vheight := div_nonneg
    (mul_nonneg hT.le (add_nonneg (modelPhaseJetCoefficient_nonneg σ 1) hδ₀)) (by positivity)
  have hVmax : Vheight ≤ Jv*T/(2*M^2) := by
    dsimp only [Vheight,Jv]
    rw [mul_comm (modelPhaseJetCoefficient σ 1+1) T]
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left (add_le_add le_rfl hδmax) hT.le) (by positivity)
  have hheight ab (hab : ab∈Gaps) :=
    source_reference_seed_height_polynomial hσ hJref hJv hT hM hR hRQ hQN hNM
      hUr hscale hV₀ hVmax (hr ab hab) (hs ab hab) (he ab hab) (hv ab hab)
  have hP₁ ab : 1 ≤ P₁ ab := le_add_of_nonneg_right
    (mul_nonneg (add_nonneg (abs_nonneg _) (mul_nonneg (abs_nonneg _) hV₀)) (Nat.cast_nonneg Q))
  have hP₂ ab : 1 ≤ P₂ ab := le_add_of_nonneg_right
    (mul_nonneg (add_nonneg (mul_nonneg (abs_nonneg _) hV₀) (abs_nonneg _)) (Nat.cast_nonneg Q))
  have hRT := physical_reference_radius_le_source hT hM hR hRQ hQN hNM hscale
  refine ⟨Bmajor,Cmajor,?_,?_,hmajor⟩
  · intro ab hab
    apply Nat.add_le_add_left
    apply Nat.mul_le_mul_left
    apply Nat.add_le_add_right
    apply Nat.floor_mono
    apply Real.logb_le_logb_of_le (by norm_num : (1:ℝ)<2)
      (mul_pos (zero_lt_one.trans_le (hP₁ ab)) (zero_lt_one.trans_le (hP₂ ab)))
    calc
      P₁ ab*P₂ ab ≤ (Ch*T^3)*(Ch*T^3) :=
        mul_le_mul (hheight ab hab).2.2.1 (hheight ab hab).2.2.2
          (zero_le_one.trans (hP₂ ab)) (by positivity)
      _ = _ := by ring
  · intro ab hab
    have hε : 0 < εchart := by change 0 < κ/(16*(Cp+2)*R^2); positivity
    have hratio := physical_reference_chart_ratio hκ hCp hRp (hgap ab hab).2
    have hratio' : (ab.2-ab.1)/(12*εchart) ≤ Cc*T := by
      apply hratio.trans
      calc
        ((14:ℝ)/3)*(Cp+2)/κ*(Uref:ℝ) ≤ ((14:ℝ)/3)*(Cp+2)/κ*T :=
          mul_le_mul_of_nonneg_left (hUR.trans hRT) (by positivity)
        _ ≤ Cc*T := mul_le_mul_of_nonneg_right
          (le_add_of_nonneg_left zero_le_one) hT.le
    apply Nat.add_le_add_right
    apply Nat.floor_mono
    exact Real.logb_le_logb_of_le (by norm_num : (1:ℝ)<5/4)
      (div_pos (sub_pos.mpr (hgap ab hab).1) (by positivity)) hratio'



example
    {Ch Cc ε : ℝ} (hCh : 1 ≤ Ch) (hCc : 1 ≤ Cc) (hε : 0 < ε) :
    ∀ᶠ T : ℝ in Filter.atTop,
    let Bmajor := 6+216*(⌊Real.logb 2 ((Ch*T^3)^2)⌋₊+1)
    let Cmajor := ⌊Real.logb (5/4) (Cc*T)⌋₊+1
    ((6+Cmajor*(105+544*Bmajor):ℕ):ℝ) ≤ T^ε := by
  exact eventually_reference_chart_majorants hCh hCc hε

#print axioms eventually_reference_chart_majorants

example
    {κ Cp R U d : ℝ} (hκ : 0 < κ) (hCp : 0 < Cp+2) (hR : 0 < R)
    (hd : d ≤ 7*U/(2*R^2)) :
    d/(12*(κ/(16*(Cp+2)*R^2))) ≤ ((14:ℝ)/3)*(Cp+2)/κ*U := by
  exact physical_reference_chart_ratio hκ hCp hR hd

#print axioms physical_reference_chart_ratio

example
    {T M N R Q : ℝ} (hT : 0 < T) (hM : 0 < M) (hR : 1 ≤ R)
    (hRQ : R ≤ Q) (hQN : Q ≤ N) (hNM : N^2 ≤ M)
    (hscale : T*N*R^2=M^3) : R^2 ≤ T := by
  exact physical_reference_radius_le_source hT hM hR hRQ hQN hNM hscale

#print axioms physical_reference_radius_le_source

example
    {σ Jref εloss : ℝ} (hσ : 0 < σ) (hJref : 0 ≤ Jref) (hεloss : 0 < εloss) :
    ∀ᶠ T : ℝ in Filter.atTop, ∀
    (Gaps : Finset (ℝ × ℝ)) (e r v s : ℝ × ℝ → ℤ) (Q Uref : ℕ)
    {δ M N R : ℝ},
    0 ≤ δ → δ ≤ 1 → 0 < T → 0 < M → 1 ≤ R →
    R ≤ (Q:ℝ) → (Q:ℝ) ≤ N → N^2 ≤ M →
    1 ≤ Uref → (Uref:ℝ) ≤ R^2 → T*N*R^2=M^3 →
    (∀ ab∈Gaps, |((r ab):ℝ)| ≤ 4*R^2/(Uref:ℝ)) →
    (∀ ab∈Gaps, |((s ab):ℝ)| ≤ 4*R^2/(Uref:ℝ)) →
    (∀ ab∈Gaps, |((e ab):ℝ)| ≤
      (3*Jref*T/(2*σ*M^2)+1)*(4*R^2/(Uref:ℝ))) →
    (∀ ab∈Gaps, |((v ab):ℝ)| ≤
      (3*Jref*T/(2*σ*M^2)+1)*(4*R^2/(Uref:ℝ))) →
    (∀ ab∈Gaps, ab.1 < ab.2 ∧ ab.2-ab.1 ≤ 7*(Uref:ℝ)/(2*R^2)) →
    let Vheight := T*(modelPhaseJetCoefficient σ 1+δ)/(2*M^2)
    let P₁ := fun ab => 1+(|((v ab):ℝ)|+|((s ab):ℝ)| *Vheight)*(Q:ℝ)
    let P₂ := fun ab => 1+(|((r ab):ℝ)| *Vheight+|((e ab):ℝ)|)*(Q:ℝ)
    let εchart := modelPhaseThirdLower σ/(16*(σ*(σ+1)+1+2)*R^2)
    ∃ Bmajor Cmajor : ℕ,
      (∀ ab∈Gaps, 6+216*(⌊Real.logb 2 (P₁ ab*P₂ ab)⌋₊+1) ≤ Bmajor) ∧
      (∀ ab∈Gaps, ⌊Real.logb (5/4) ((ab.2-ab.1)/(12*εchart))⌋₊+1 ≤ Cmajor) ∧
      ((6+Cmajor*(105+544*Bmajor):ℕ):ℝ) ≤ T^εloss := by
  exact eventually_physical_reference_chart_budgets hσ hJref hεloss

#print axioms eventually_physical_reference_chart_budgets

/-- The polynomial label-height bound only needs direct source-window
bounds. It does not require the stronger block restriction N^2<=M. -/
private theorem source_reference_seed_height_polynomial_window
    {σ J Jv T M R Q U V e r v s : ℝ}
    (hσ : 0 < σ) (hJ : 0 ≤ J) (hJv : 0 ≤ Jv)
    (hT1 : 1 ≤ T) (hM1 : 1 ≤ M) (hQ₀ : 0 ≤ Q)
    (hQT : Q ≤ T) (hRT : R^2 ≤ T)
    (hU : 1 ≤ U)
    (hV₀ : 0 ≤ V) (hV : V ≤ Jv*T/(2*M^2))
    (hr : |r| ≤ 4*R^2/U) (hs : |s| ≤ 4*R^2/U)
    (he : |e| ≤ (3*J*T/(2*σ*M^2)+1)*(4*R^2/U))
    (hv : |v| ≤ (3*J*T/(2*σ*M^2)+1)*(4*R^2/U)) :
    let C := 1+4*(3*J/(2*σ)+1+Jv/2)
    1 ≤ C ∧ 1+(|v|+|s| *V)*Q ≤ C*T^3 ∧
      1+(|r| *V+|e|)*Q ≤ C*T^3 := by
  intro C
  have hT : 0 < T := zero_lt_one.trans_le hT1
  have hM₂ : 1 ≤ M^2 := one_le_pow₀ hM1
  have hK : 4*R^2/U ≤ 4*T :=
    (div_le_self (by positivity) hU).trans (mul_le_mul_of_nonneg_left hRT (by norm_num))
  let c := 3*J/(2*σ)
  have hc : 0 ≤ c := by dsimp only [c]; positivity
  have hcurv : 3*J*T/(2*σ*M^2) ≤ c*T := by
    calc
      _ = c*T/M^2 := by dsimp only [c]; ring
      _ ≤ c*T := div_le_self (mul_nonneg hc hT.le) hM₂
  have hV' : V ≤ (Jv/2)*T := hV.trans (by
    calc
      Jv*T/(2*M^2) = ((Jv/2)*T)/M^2 := by ring
      _ ≤ (Jv/2)*T := div_le_self (by positivity) hM₂)
  have hlabel {z : ℝ}
      (hz : |z| ≤ (3*J*T/(2*σ*M^2)+1)*(4*R^2/U)) :
      |z| ≤ 4*(c+1)*T^2 := by
    have htop : 3*J*T/(2*σ*M^2)+1 ≤ (c+1)*T := by nlinarith only [hcurv,hT1]
    apply hz.trans
    calc
      _ ≤ ((c+1)*T)*(4*T) :=
        mul_le_mul htop hK (by positivity) (by positivity)
      _ = _ := by ring
  have hr' : |r| ≤ 4*T := hr.trans hK
  have hs' : |s| ≤ 4*T := hs.trans hK
  have he' := hlabel he
  have hv' := hlabel hv
  have hvV : |s| *V ≤ 2*Jv*T^2 := by
    calc
      _ ≤ (4*T)*((Jv/2)*T) := mul_le_mul hs' hV' hV₀ (by positivity)
      _ = _ := by ring
  have hrV : |r| *V ≤ 2*Jv*T^2 := by
    calc
      _ ≤ (4*T)*((Jv/2)*T) := mul_le_mul hr' hV' hV₀ (by positivity)
      _ = _ := by ring
  have hC : 1 ≤ C := by
    change 1 ≤ 1+4*(c+1+Jv/2)
    exact le_add_of_nonneg_right (by positivity)
  have hpow : 1 ≤ T^3 := one_le_pow₀ hT1
  refine ⟨hC,?_,?_⟩
  · have hsum : |v|+|s| *V ≤ (4*(c+1)+2*Jv)*T^2 := by linarith only [hv',hvV]
    have hh := mul_le_mul hsum hQT hQ₀ (by positivity : 0 ≤ (4*(c+1)+2*Jv)*T^2)
    change 1+(|v|+|s| *V)*Q ≤ (1+4*(c+1+Jv/2))*T^3
    nlinarith only [hh,hpow]
  · have hsum : |r| *V+|e| ≤ (4*(c+1)+2*Jv)*T^2 := by linarith only [he',hrV]
    have hh := mul_le_mul hsum hQT hQ₀ (by positivity : 0 ≤ (4*(c+1)+2*Jv)*T^2)
    change 1+(|r| *V+|e|)*Q ≤ (1+4*(c+1+Jv/2))*T^3
    nlinarith only [hh,hpow]

example
    {σ J Jv T M R Q U V e r v s : ℝ}
    (hσ : 0 < σ) (hJ : 0 ≤ J) (hJv : 0 ≤ Jv)
    (hT1 : 1 ≤ T) (hM1 : 1 ≤ M) (hQ₀ : 0 ≤ Q)
    (hQT : Q ≤ T) (hRT : R^2 ≤ T)
    (hU : 1 ≤ U)
    (hV₀ : 0 ≤ V) (hV : V ≤ Jv*T/(2*M^2))
    (hr : |r| ≤ 4*R^2/U) (hs : |s| ≤ 4*R^2/U)
    (he : |e| ≤ (3*J*T/(2*σ*M^2)+1)*(4*R^2/U))
    (hv : |v| ≤ (3*J*T/(2*σ*M^2)+1)*(4*R^2/U)) :
    let C := 1+4*(3*J/(2*σ)+1+Jv/2)
    1 ≤ C ∧ 1+(|v|+|s| *V)*Q ≤ C*T^3 ∧
      1+(|r| *V+|e|)*Q ≤ C*T^3 := by
  exact source_reference_seed_height_polynomial_window hσ hJ hJv hT1 hM1 hQ₀ hQT hRT hU hV₀ hV hr hs he hv

#print axioms source_reference_seed_height_polynomial_window

/-- Uniform logarithmic chart budgets under the direct source window;
the old N^2<=M route remains separately available without alteration. -/
private theorem eventually_physical_reference_chart_budgets_window
    {σ Jref εloss : ℝ} (hσ : 0 < σ) (hJref : 0 ≤ Jref) (hεloss : 0 < εloss) :
    ∀ᶠ T : ℝ in Filter.atTop, ∀
    (Gaps : Finset (ℝ × ℝ)) (e r v s : ℝ × ℝ → ℤ) (Q Uref : ℕ)
    {δ M R : ℝ},
    0 ≤ δ → δ ≤ 1 → 1 ≤ M → 1 ≤ R →
    (Q:ℝ) ≤ T → R^2 ≤ T →
    1 ≤ Uref → (Uref:ℝ) ≤ R^2 →
    (∀ ab∈Gaps, |((r ab):ℝ)| ≤ 4*R^2/(Uref:ℝ)) →
    (∀ ab∈Gaps, |((s ab):ℝ)| ≤ 4*R^2/(Uref:ℝ)) →
    (∀ ab∈Gaps, |((e ab):ℝ)| ≤
      (3*Jref*T/(2*σ*M^2)+1)*(4*R^2/(Uref:ℝ))) →
    (∀ ab∈Gaps, |((v ab):ℝ)| ≤
      (3*Jref*T/(2*σ*M^2)+1)*(4*R^2/(Uref:ℝ))) →
    (∀ ab∈Gaps, ab.1 < ab.2 ∧ ab.2-ab.1 ≤ 7*(Uref:ℝ)/(2*R^2)) →
    let Vheight := T*(modelPhaseJetCoefficient σ 1+δ)/(2*M^2)
    let P₁ := fun ab => 1+(|((v ab):ℝ)|+|((s ab):ℝ)| *Vheight)*(Q:ℝ)
    let P₂ := fun ab => 1+(|((r ab):ℝ)| *Vheight+|((e ab):ℝ)|)*(Q:ℝ)
    let εchart := modelPhaseThirdLower σ/(16*(σ*(σ+1)+1+2)*R^2)
    ∃ Bmajor Cmajor : ℕ,
      (∀ ab∈Gaps, 6+216*(⌊Real.logb 2 (P₁ ab*P₂ ab)⌋₊+1) ≤ Bmajor) ∧
      (∀ ab∈Gaps, ⌊Real.logb (5/4) ((ab.2-ab.1)/(12*εchart))⌋₊+1 ≤ Cmajor) ∧
      ((6+Cmajor*(105+544*Bmajor):ℕ):ℝ) ≤ T^εloss := by
  let Jv := modelPhaseJetCoefficient σ 1+1
  let Ch := 1+4*(3*Jref/(2*σ)+1+Jv/2)
  let κ := modelPhaseThirdLower σ
  let Cp := σ*(σ+1)+1
  let Cc := 1+((14:ℝ)/3)*(Cp+2)/κ
  have hJv : 0 ≤ Jv := add_nonneg (modelPhaseJetCoefficient_nonneg σ 1) zero_le_one
  have hκ : 0 < κ := modelPhaseThirdLower_pos hσ
  have hCp : 0 < Cp+2 := by dsimp only [Cp]; positivity
  have hCh : 1 ≤ Ch := by dsimp only [Ch]; exact le_add_of_nonneg_right (by positivity)
  have hCc : 1 ≤ Cc := by dsimp only [Cc]; exact le_add_of_nonneg_right (by positivity)
  filter_upwards [eventually_reference_chart_majorants hCh hCc hεloss,
    Filter.eventually_ge_atTop (1:ℝ)] with T hmajor hT1
  intro Gaps e r v s Q Uref δ M R hδ₀ hδmax hM1 hR hQT hRT
    hU hUR hr hs he hv hgap Vheight P₁ P₂ εchart
  have hT : 0 < T := zero_lt_one.trans_le hT1
  let Bmajor := 6+216*(⌊Real.logb 2 ((Ch*T^3)^2)⌋₊+1)
  let Cmajor := ⌊Real.logb (5/4) (Cc*T)⌋₊+1
  have hRp : 0 < R := zero_lt_one.trans_le hR
  have hUr : (1:ℝ) ≤ Uref := by exact_mod_cast hU
  have hV₀ : 0 ≤ Vheight := div_nonneg
    (mul_nonneg hT.le (add_nonneg (modelPhaseJetCoefficient_nonneg σ 1) hδ₀)) (by positivity)
  have hVmax : Vheight ≤ Jv*T/(2*M^2) := by
    dsimp only [Vheight,Jv]
    rw [mul_comm (modelPhaseJetCoefficient σ 1+1) T]
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left (add_le_add le_rfl hδmax) hT.le) (by positivity)
  have hheight ab (hab : ab∈Gaps) :=
    source_reference_seed_height_polynomial_window hσ hJref hJv hT1 hM1
      (Nat.cast_nonneg Q) hQT hRT hUr hV₀ hVmax
      (hr ab hab) (hs ab hab) (he ab hab) (hv ab hab)
  have hP₁ ab : 1 ≤ P₁ ab := le_add_of_nonneg_right
    (mul_nonneg (add_nonneg (abs_nonneg _) (mul_nonneg (abs_nonneg _) hV₀)) (Nat.cast_nonneg Q))
  have hP₂ ab : 1 ≤ P₂ ab := le_add_of_nonneg_right
    (mul_nonneg (add_nonneg (mul_nonneg (abs_nonneg _) hV₀) (abs_nonneg _)) (Nat.cast_nonneg Q))
  refine ⟨Bmajor,Cmajor,?_,?_,hmajor⟩
  · intro ab hab
    apply Nat.add_le_add_left
    apply Nat.mul_le_mul_left
    apply Nat.add_le_add_right
    apply Nat.floor_mono
    apply Real.logb_le_logb_of_le (by norm_num : (1:ℝ)<2)
      (mul_pos (zero_lt_one.trans_le (hP₁ ab)) (zero_lt_one.trans_le (hP₂ ab)))
    calc
      P₁ ab*P₂ ab ≤ (Ch*T^3)*(Ch*T^3) :=
        mul_le_mul (hheight ab hab).2.1 (hheight ab hab).2.2
          (zero_le_one.trans (hP₂ ab)) (by positivity)
      _ = _ := by ring
  · intro ab hab
    have hε : 0 < εchart := by change 0 < κ/(16*(Cp+2)*R^2); positivity
    have hratio := physical_reference_chart_ratio hκ hCp hRp (hgap ab hab).2
    have hratio' : (ab.2-ab.1)/(12*εchart) ≤ Cc*T := by
      apply hratio.trans
      calc
        ((14:ℝ)/3)*(Cp+2)/κ*(Uref:ℝ) ≤ ((14:ℝ)/3)*(Cp+2)/κ*T :=
          mul_le_mul_of_nonneg_left (hUR.trans hRT) (by positivity)
        _ ≤ Cc*T := mul_le_mul_of_nonneg_right
          (le_add_of_nonneg_left zero_le_one) hT.le
    apply Nat.add_le_add_right
    apply Nat.floor_mono
    exact Real.logb_le_logb_of_le (by norm_num : (1:ℝ)<5/4)
      (div_pos (sub_pos.mpr (hgap ab hab).1) (by positivity)) hratio'

example
    {σ Jref εloss : ℝ} (hσ : 0 < σ) (hJref : 0 ≤ Jref) (hεloss : 0 < εloss) :
    ∀ᶠ T : ℝ in Filter.atTop, ∀
    (Gaps : Finset (ℝ × ℝ)) (e r v s : ℝ × ℝ → ℤ) (Q Uref : ℕ)
    {δ M R : ℝ},
    0 ≤ δ → δ ≤ 1 → 1 ≤ M → 1 ≤ R →
    (Q:ℝ) ≤ T → R^2 ≤ T →
    1 ≤ Uref → (Uref:ℝ) ≤ R^2 →
    (∀ ab∈Gaps, |((r ab):ℝ)| ≤ 4*R^2/(Uref:ℝ)) →
    (∀ ab∈Gaps, |((s ab):ℝ)| ≤ 4*R^2/(Uref:ℝ)) →
    (∀ ab∈Gaps, |((e ab):ℝ)| ≤
      (3*Jref*T/(2*σ*M^2)+1)*(4*R^2/(Uref:ℝ))) →
    (∀ ab∈Gaps, |((v ab):ℝ)| ≤
      (3*Jref*T/(2*σ*M^2)+1)*(4*R^2/(Uref:ℝ))) →
    (∀ ab∈Gaps, ab.1 < ab.2 ∧ ab.2-ab.1 ≤ 7*(Uref:ℝ)/(2*R^2)) →
    let Vheight := T*(modelPhaseJetCoefficient σ 1+δ)/(2*M^2)
    let P₁ := fun ab => 1+(|((v ab):ℝ)|+|((s ab):ℝ)| *Vheight)*(Q:ℝ)
    let P₂ := fun ab => 1+(|((r ab):ℝ)| *Vheight+|((e ab):ℝ)|)*(Q:ℝ)
    let εchart := modelPhaseThirdLower σ/(16*(σ*(σ+1)+1+2)*R^2)
    ∃ Bmajor Cmajor : ℕ,
      (∀ ab∈Gaps, 6+216*(⌊Real.logb 2 (P₁ ab*P₂ ab)⌋₊+1) ≤ Bmajor) ∧
      (∀ ab∈Gaps, ⌊Real.logb (5/4) ((ab.2-ab.1)/(12*εchart))⌋₊+1 ≤ Cmajor) ∧
      ((6+Cmajor*(105+544*Bmajor):ℕ):ℝ) ≤ T^εloss := by
  exact eventually_physical_reference_chart_budgets_window hσ hJref hεloss

#print axioms eventually_physical_reference_chart_budgets_window

/-- Actual paired-model source mass with arbitrary narrowing V. The logarithmic
budgets are constructed uniformly; this is not a full double-shift family theorem. -/
private theorem eventually_physicalModelPhase_actual_fourier_original_pair_mass_raw
    {σ Jref εloss : ℝ} (hσ : 0 < σ) (hJref : 0 ≤ Jref) (hεloss : 0 < εloss) :
    ∀ᶠ T : ℝ in Filter.atTop, ∀
    (Uref : ℕ) (Refs : Finset ℝ) (Gaps : Finset (ℝ × ℝ)) {Bselect : ℝ}
    (P : Finset ((ℤ × Fin 2) × (ℤ × Fin 2))) (Mat : ((ℤ × Fin 2) × (ℤ × Fin 2)) → Fin 4 → ℤ)
    (gap : ((ℤ × Fin 2) × (ℤ × Fin 2)) → ℝ × ℝ)
    (Q K₀ : ℕ) [NeZero K₀]
    (N : ℕ) (za zb : ℤ → ℝ) (AlenA AlenB : ℤ → ℕ) (Za Zb : ℤ)
    (rat : ((ℤ × Fin 2) × (ℤ × Fin 2)) → Fin 2 → ℚ)
    (vinv : ((ℤ × Fin 2) × (ℤ × Fin 2)) → Fin 2 → ℤ)
    (parity : ((ℤ × Fin 2) × (ℤ × Fin 2)) → Fin 2 → Fin 2)
    (anchor : ((ℤ × Fin 2) × (ℤ × Fin 2)) → ℚ)
    (e r v s : ℝ × ℝ → ℤ)
    {δ M R base Bcut lambda Uband θ V : ℝ}
    {F : Fin 2 → ℝ → ℝ} {A W : Fin 2 → ℝ}
    {x : ((ℤ × Fin 2) × (ℤ × Fin 2)) → Fin 2 → ℝ},
    (∀ ij∈P, base ≤ za ij.1.1) →
    (∀ ij∈P, x ij 0=za ij.1.1) →
    (∀ ij∈P, x ij 1=zb ij.2.1) →
    (∀ ij∈P, gap ij∈Gaps) →
    (∀ ij∈P, N ≤ AlenA ij.1.1 ∧ AlenA ij.1.1 ≤ 3*N ∧
      round (za ij.1.1)+(AlenA ij.1.1:ℤ)=Za+(N:ℤ)*ij.1.1+2*(N:ℤ)) →
    (∀ ij∈P, N ≤ AlenB ij.2.1 ∧ AlenB ij.2.1 ≤ 3*N ∧
      round (zb ij.2.1)+(AlenB ij.2.1:ℤ)=Zb+(N:ℤ)*ij.2.1+2*(N:ℤ)) →
    (δ ≤ min (modelPhaseThirdLower σ) 1) →
    (∀ i, Expdb.IsApproximateModelPhaseFunction (F i) σ 4 δ) →
    (0 < T) →
    (0 < M) →
    (0 < (N:ℝ)) →
    (1 ≤ R) →
    (R ≤ M) →
    (0 < Q) →
    (T*(N:ℝ)*R^2=M^3) →
    ((Q:ℝ)*(N:ℝ) ≤ (K₀:ℝ)*R^2) →
    (∀ i, M ≤ A i) →
    (∀ i, A i+W i ≤ 2*M) →
    (∀ ij∈P, ∀ i, x ij i∈Ioo (1/2:ℝ) (W i-1/2)) →
    (∀ ij∈P, ∀ i, (rat ij i).den ≤ Q ∧ Q ≤ 2*(rat ij i).den) →
    (0 < lambda) →
    (0 ≤ Uband) →
    (0 < θ) →
    (θ ≤ 1/24) →
    (∀ ij∈P, ∀ i, lambda ≤ |(rat ij i:ℝ)| ∧ |(rat ij i:ℝ)| ≤ Uband) →
    (∀ ij∈P, ∀ i, ((rat ij i).den:ℤ) ∣ (rat ij i).num*vinv ij i-1) →
    (∀ ab∈Gaps, (v ab)*(r ab)-(e ab)*(s ab)=1) →
    (∀ ab∈Gaps, ((0:ℝ) < (r ab) ∧ ((e ab):ℝ)/(r ab)=ab.1) ∨
      (((r ab):ℝ) < 0 ∧ ((e ab):ℝ)/(r ab)=ab.2)) →
    (0 < Bcut) →
    (∀ ab∈Gaps, (s ab) ≠ 0) →
    (∀ ab∈Gaps, ((e ab):ℝ)/(r ab)∈Refs) →
    (∀ ab∈Gaps, ((v ab):ℝ)/(s ab)∈Refs) →
    (∀ a∈Refs, ∀ b∈Refs, a ≠ b → ((Uref:ℝ)/R^2)/4 < |a-b|) →
    (∀ ij∈P, ∀ i, x ij i-(56*(Uref:ℝ)/modelPhaseThirdLower σ)*(N:ℝ)∈Ioo (1/2:ℝ) (W i-1/2)) →
    (∀ ij∈P, ∀ i, x ij i+(56*(Uref:ℝ)/modelPhaseThirdLower σ)*(N:ℝ)∈Ioo (1/2:ℝ) (W i-1/2)) →
    (1 ≤ Uref) →
    (2+168/modelPhaseThirdLower σ ≤ Bselect) →
    (7*Bcut ≤ modelPhaseThirdLower σ*Bselect) →
    (Bselect^2*(Uref:ℝ)^3*R^2 ≤ (N:ℝ)^2) →
    (∀ ab∈Gaps, R^2 ≤ ((r ab):ℝ)^2*(Uref:ℝ)) →
    (∀ ab∈Gaps, ab.2-ab.1 ≤ 7*(Uref:ℝ)/(2*R^2)) →
    (R ≤ (Q:ℝ)) →
    ((Uref:ℝ) ≤ ((N:ℝ)/(Q:ℝ))^((2:ℝ)/3)/Bselect) →
    ((N:ℝ)^10 ≤ M^3*R^7) →
    (∀ ij∈P, (rat ij 0:ℝ)∈Icc (gap ij).1 (gap ij).2) →
    (∀ ij∈P, Mat ij 2 ≠ 0) →
    (∀ ij∈P, 64*(modelPhaseJetCoefficient σ 3+δ)*M^2 ≤
      |(Mat ij 2:ℝ)| *(modelPhaseThirdLower σ)^2*T) →
    (∀ ij∈P, 8*Uband ≤ |(Mat ij 2:ℝ)| *lambda^2) →
    (1 ≤ V) →
    (∀ ab∈Gaps, ab.1∈Refs ∧ ab.2∈Refs ∧ ab.1 < ab.2 ∧
      ∀ t∈Refs, ¬(ab.1 < t ∧ t < ab.2)) →
    (Q:ℝ) ≤ (N:ℝ) →
    ((N:ℝ)^2 ≤ M ∨ (1 ≤ M ∧ (N:ℝ) ≤ T ∧ R^2 ≤ T)) → (Uref:ℝ) ≤ R^2 →
    (∀ ab∈Gaps, |((r ab):ℝ)| ≤ 4*R^2/(Uref:ℝ)) →
    (∀ ab∈Gaps, |((s ab):ℝ)| ≤ 4*R^2/(Uref:ℝ)) →
    (∀ ab∈Gaps, |((e ab):ℝ)| ≤
      (3*Jref*T/(2*σ*M^2)+1)*(4*R^2/(Uref:ℝ))) →
    (∀ ab∈Gaps, |((v ab):ℝ)| ≤
      (3*Jref*T/(2*σ*M^2)+1)*(4*R^2/(Uref:ℝ))) →
    let ε := modelPhaseThirdLower σ/(16*(σ*(σ+1)+1+2)*R^2)
    let sourceColor := fun ij i => (⌊((rat ij i).den:ℝ)/(θ*((Q:ℝ)/2))⌋,
      ⌊((rat ij i).num:ℝ)/(θ*(lambda*(Q:ℝ)/2))⌋)
    (∀ ij∈P, sourceColor ij 0=sourceColor ij 1) →
    let f := fun i => heathBrownPhysicalPhase (F i) T M (A i) 1
    (∀ ij∈P, ∀ i, iteratedDeriv 2 (f i) (x ij i)/2=(rat ij i:ℝ)) →
    let q := fun ij i => (rat ij i).den
    let mu := fun ij i => iteratedDeriv 3 (f i) (round (x ij i))/6
    let ell := fun ij i => deriv (f i) (round (x ij i))
    let b := fun ij i => (⌊(q ij i:ℝ)*ell ij i⌋+(parity ij i:ℕ) : ℤ)
    let cround := fun ij i => round ((q ij i:ℝ)*ell ij i)
    let tau := fun ij i => ((b ij i:ℝ)-(q ij i:ℝ)*ell ij i)/2
    let dual := fun ij i => -2*mu ij i*(Real.sqrt (2/(3*mu ij i*(q ij i:ℝ))))^3
    let cloud := fun ij i => (![Int.fract (-(vinv ij i:ℝ)*b ij i/q ij i),
      Int.fract (-(vinv ij i:ℝ)/q ij i),dual ij i/Real.sqrt K₀,
      (3*dual ij i*tau ij i/2)/Real.sqrt K₀] : Fin 4 → ℝ)
    let radius : Fin 4 → ℝ := ![1/(12*(K₀:ℝ)),1/(12*(K₀:ℝ)^2),(1/(K₀:ℝ)^2)/12,(1/(K₀:ℝ))/12]
    (∀ ij∈P, b ij 0-cround ij 0=b ij 1-cround ij 1) →
    (∀ ij∈P, ∀ a, |cloud ij 0 a-cloud ij 1 a| ≤ 2*radius a) →
    (∀ ij∈P,
      |cloud ij 0 1-cloud ij 1 1| ≤ 1/(6*(K₀:ℝ)^2*V)) →
    let κ := modelPhaseThirdLower σ
    let Cphys := σ*(σ+1)+1
    let c := κ/6
    let J := Cphys/6
    let B := max 1 (max (2*Real.sqrt J) (8*J*Real.sqrt J/(3*c)))
    B*R^2/(N:ℝ)^2 ≤ 1/2 →
    (N:ℝ) ≤ R^2 →
    R ≤ (N:ℝ) →
    (N:ℝ)^3 ≤ M*R^2 →
    2*R^2 ≤ (Q:ℝ)*(N:ℝ) →
    (∀ ij∈P, Mat ij 0*Mat ij 3-Mat ij 1*Mat ij 2=1) →
    (∀ ij∈P, (Mat ij 2:ℝ)*(rat ij 0:ℝ)+Mat ij 3=(q ij 1:ℝ)/q ij 0) →
    (∀ ij∈P, ((Mat ij 0:ℝ)*(rat ij 0:ℝ)+Mat ij 1)/
      ((Mat ij 2:ℝ)*(rat ij 0:ℝ)+Mat ij 3)=(rat ij 1:ℝ)) →
    (∀ ij∈P, |(Mat ij 2:ℝ)| ≤ (Q:ℝ)^2/(6*(K₀:ℝ)^2)) →
    let H := (N:ℝ)/(Cphys+2)
    2 ≤ (N:ℝ) →
    (∀ ij∈P, ∀ i, x ij i-H∈Ioo (1/2:ℝ) (W i-1/2)) →
    (∀ ij∈P, ∀ i, x ij i+H∈Ioo (1/2:ℝ) (W i-1/2)) →
    (∀ ij∈P, |(anchor ij:ℝ)-(rat ij 0:ℝ)| ≤ ε) →
    (∀ ij∈P, 256*((anchor ij).den:ℝ) ≤ (Q:ℝ)/3) →
    (∀ ij∈P, 256 ≤ (2*ε)*((Q:ℝ)/3)*(anchor ij).den) →
    let C₂ := modelPhaseJetCoefficient σ 2+δ
    let C₃ := modelPhaseJetCoefficient σ 3+δ
    let Ct := C₂/2+5*C₃/12
    let Cc := C₂/κ+C₃/(2*κ)
    let Δ := (37*B/2+16*B*Cc+2*Ct+2*Cc)*(Q:ℝ)/(N:ℝ)
    let Ccurv := (4/κ)*(B+2*quarticReciprocalConstant σ δ)
    let D := Δ+quarticNonlinearResidualConstant σ δ*(2*(Q:ℝ))/(N:ℝ)
    let Kres := 4*(37*B/2+16*B*Cc+2*Ct+2*Cc+
      2*quarticNonlinearResidualConstant σ δ)/κ
    let Esize := κ/(16*(Cphys+2))
    let Dbase := 37*B/2+16*B*Cc+2*Ct+2*Cc+2*quarticNonlinearResidualConstant σ δ
    let Tbase := (2/κ)*(B+2*quarticReciprocalConstant σ δ)
    2*3840*128^2*105*(Dbase+64*Tbase*Esize^2) ≤ Bselect*Esize →
    D ≤ 1/2 → Δ < 1/2 → 61*Ccurv*Cphys ≤ Bcut →
    let Lunit := 2*κ/Cphys
    let Gamma := Cphys/κ
    let Cthird := Gamma*(32*Kres+9*quarticReciprocalConstant σ δ)
    let Cpack := 64*Cphys*(Gamma^2*Cthird+Gamma*(modelPhaseJetCoefficient σ 3+δ)/κ)/κ
    let Cfirst := 128*Cphys*(Gamma^2*Cthird+Gamma*(modelPhaseJetCoefficient σ 3+δ)/κ)/κ^2
    let Cgap := 64*Cphys*(Gamma^2*B+Gamma*(modelPhaseJetCoefficient σ 3+δ)/κ)/κ
    let Cmain := 4*(2*Cfirst/Lunit^3)^((3:ℝ)⁻¹)+2
    let Ctail := 4*Cpack/Lunit^2+Cgap
    (P.card:ℝ) ≤
      (60*588*(Uband/lambda)^2*Uband^2*(R^8/(N:ℝ)^4)*
        (Cmain/V^((5:ℝ)/3)+Ctail/((Uref:ℝ)*V)))*T^εloss := by
  filter_upwards [eventually_physical_reference_chart_budgets hσ hJref hεloss,
    eventually_physical_reference_chart_budgets_window hσ hJref hεloss] with T hbudgets hbudgetsWindow
  intro Uref Refs Gaps Bselect P Mat gap Q K₀ _ N za zb AlenA AlenB Za Zb
    rat vinv parity anchor e r v s δ M R base Bcut lambda Uband θ V F A W x
    hbase hxa hxb hgapMem hgeometryA hgeometryB hδ hF hT hM hN hR hRM hQ hscale hmesh hA hW hx hden hlambda hUband hθ hθmax hcurv hinv hchart horientation hBcut hs hrefSet hparentSet hsep hwideL hwideU hUref hBselectSize hcutMargin hselectedWrap hreferenceDen hgapWidth hRQ hselectedUpper hscaleTen hfamilyGap hc hlarge haction hV hgap
    hQN hNM hUR hrHeight hsHeight heHeight hvHeight
    ε sourceColor hsourceColor f hlevel q mu ell b cround tau dual cloud radius
    hcolor hnear hnearNarrow κ Cphys c J B hsmall hNR hRN hNcube hminscale
    hMatdet hMatt hMatmap hMatgamma H hNtwo hL hU hanchor hcut hcount
    C₂ C₃ Ct Cc Δ Ccurv D Kres Esize Dbase Tbase hsize hD hΔ hBsize
    Lunit Gamma Cthird Cpack Cfirst Cgap Cmain Ctail
  have hδ₀ := approximateModelPhase_tolerance_nonneg (hF 0)
  obtain ⟨Bmajor,Cmajor,hBmajor,hCmajor,hcost⟩ := hNM.elim
    (fun hNtwoM => hbudgets
      Gaps e r v s Q Uref hδ₀ (hδ.trans (min_le_right _ _)) hT hM hR hRQ hQN
      hNtwoM hUref hUR hscale hrHeight hsHeight heHeight hvHeight
      (fun ab hab => ⟨(hgap ab hab).2.2.1,hgapWidth ab hab⟩))
    (fun hwindow => hbudgetsWindow
      Gaps e r v s Q Uref hδ₀ (hδ.trans (min_le_right _ _)) hwindow.1 hR
      (hQN.trans hwindow.2.1) hwindow.2.2 hUref hUR
      hrHeight hsHeight heHeight hvHeight
      (fun ab hab => ⟨(hgap ab hab).2.2.1,hgapWidth ab hab⟩))
  have hh := physicalModelPhase_actual_fourier_original_pair_mass Uref Refs Gaps (Bselect:=Bselect) P Mat gap Bmajor Cmajor Q K₀ N za zb AlenA AlenB Za Zb rat vinv parity anchor e r v s (σ:=σ) (δ:=δ) (T:=T) (M:=M) (R:=R) (base:=base) (Bcut:=Bcut) (lambda:=lambda) (Uband:=Uband) (θ:=θ) (V:=V) (F:=F) (A:=A) (W:=W) (x:=x) hbase hxa hxb hgapMem hgeometryA hgeometryB hσ hδ hF hT hM hN hR hRM hQ hscale hmesh hA hW hx hden hlambda hUband hθ hθmax hcurv hinv hchart horientation hBcut hs hrefSet hparentSet hsep hwideL hwideU hUref hBselectSize hcutMargin hselectedWrap hreferenceDen hgapWidth hRQ hselectedUpper hscaleTen hfamilyGap hc hlarge haction hV hgap
    hsourceColor hlevel hcolor hnear hnearNarrow hsmall hNR hRN hNcube hminscale
    hMatdet hMatt hMatmap hMatgamma hNtwo hL hU hanchor hcut hcount
    hsize hD hΔ hBsize hBmajor hCmajor
  have hmass := hh.2.1
  let m0 := 6+Cmajor*(105+544*Bmajor)
  let Kbase := 60*588*(Uband/lambda)^2*Uband^2*(R^8/(N:ℝ)^4)*
    (Cmain/V^((5:ℝ)/3)+Ctail/((Uref:ℝ)*V))
  have hmass' : (P.card:ℝ) ≤ (m0:ℝ)*Kbase := by
    convert hmass using 1
    dsimp only [m0,Kbase]
    ring
  have hmpos : (0:ℝ) < m0 := by dsimp only [m0]; positivity
  have hknon : 0 ≤ Kbase := by
    have hnon : 0 ≤ (m0:ℝ)*Kbase :=
      (Nat.cast_nonneg P.card).trans hmass'
    nlinarith only [hnon,hmpos]
  exact hmass'.trans (by
    calc
      (m0:ℝ)*Kbase ≤ T^εloss*Kbase := mul_le_mul_of_nonneg_right hcost hknon
      _ = Kbase*T^εloss := mul_comm _ _)

example
    {σ Jref εloss : ℝ} (hσ : 0 < σ) (hJref : 0 ≤ Jref) (hεloss : 0 < εloss) :
    ∀ᶠ T : ℝ in Filter.atTop, ∀
    (Uref : ℕ) (Refs : Finset ℝ) (Gaps : Finset (ℝ × ℝ)) {Bselect : ℝ}
    (P : Finset ((ℤ × Fin 2) × (ℤ × Fin 2))) (Mat : ((ℤ × Fin 2) × (ℤ × Fin 2)) → Fin 4 → ℤ)
    (gap : ((ℤ × Fin 2) × (ℤ × Fin 2)) → ℝ × ℝ)
    (Q K₀ : ℕ) [NeZero K₀]
    (N : ℕ) (za zb : ℤ → ℝ) (AlenA AlenB : ℤ → ℕ) (Za Zb : ℤ)
    (rat : ((ℤ × Fin 2) × (ℤ × Fin 2)) → Fin 2 → ℚ)
    (vinv : ((ℤ × Fin 2) × (ℤ × Fin 2)) → Fin 2 → ℤ)
    (parity : ((ℤ × Fin 2) × (ℤ × Fin 2)) → Fin 2 → Fin 2)
    (anchor : ((ℤ × Fin 2) × (ℤ × Fin 2)) → ℚ)
    (e r v s : ℝ × ℝ → ℤ)
    {δ M R base Bcut lambda Uband θ V : ℝ}
    {F : Fin 2 → ℝ → ℝ} {A W : Fin 2 → ℝ}
    {x : ((ℤ × Fin 2) × (ℤ × Fin 2)) → Fin 2 → ℝ},
    (∀ ij∈P, base ≤ za ij.1.1) →
    (∀ ij∈P, x ij 0=za ij.1.1) →
    (∀ ij∈P, x ij 1=zb ij.2.1) →
    (∀ ij∈P, gap ij∈Gaps) →
    (∀ ij∈P, N ≤ AlenA ij.1.1 ∧ AlenA ij.1.1 ≤ 3*N ∧
      round (za ij.1.1)+(AlenA ij.1.1:ℤ)=Za+(N:ℤ)*ij.1.1+2*(N:ℤ)) →
    (∀ ij∈P, N ≤ AlenB ij.2.1 ∧ AlenB ij.2.1 ≤ 3*N ∧
      round (zb ij.2.1)+(AlenB ij.2.1:ℤ)=Zb+(N:ℤ)*ij.2.1+2*(N:ℤ)) →
    (δ ≤ min (modelPhaseThirdLower σ) 1) →
    (∀ i, Expdb.IsApproximateModelPhaseFunction (F i) σ 4 δ) →
    (0 < T) →
    (0 < M) →
    (0 < (N:ℝ)) →
    (1 ≤ R) →
    (R ≤ M) →
    (0 < Q) →
    (T*(N:ℝ)*R^2=M^3) →
    ((Q:ℝ)*(N:ℝ) ≤ (K₀:ℝ)*R^2) →
    (∀ i, M ≤ A i) →
    (∀ i, A i+W i ≤ 2*M) →
    (∀ ij∈P, ∀ i, x ij i∈Ioo (1/2:ℝ) (W i-1/2)) →
    (∀ ij∈P, ∀ i, (rat ij i).den ≤ Q ∧ Q ≤ 2*(rat ij i).den) →
    (0 < lambda) →
    (0 ≤ Uband) →
    (0 < θ) →
    (θ ≤ 1/24) →
    (∀ ij∈P, ∀ i, lambda ≤ |(rat ij i:ℝ)| ∧ |(rat ij i:ℝ)| ≤ Uband) →
    (∀ ij∈P, ∀ i, ((rat ij i).den:ℤ) ∣ (rat ij i).num*vinv ij i-1) →
    (∀ ab∈Gaps, (v ab)*(r ab)-(e ab)*(s ab)=1) →
    (∀ ab∈Gaps, ((0:ℝ) < (r ab) ∧ ((e ab):ℝ)/(r ab)=ab.1) ∨
      (((r ab):ℝ) < 0 ∧ ((e ab):ℝ)/(r ab)=ab.2)) →
    (0 < Bcut) →
    (∀ ab∈Gaps, (s ab) ≠ 0) →
    (∀ ab∈Gaps, ((e ab):ℝ)/(r ab)∈Refs) →
    (∀ ab∈Gaps, ((v ab):ℝ)/(s ab)∈Refs) →
    (∀ a∈Refs, ∀ b∈Refs, a ≠ b → ((Uref:ℝ)/R^2)/4 < |a-b|) →
    (∀ ij∈P, ∀ i, x ij i-(56*(Uref:ℝ)/modelPhaseThirdLower σ)*(N:ℝ)∈Ioo (1/2:ℝ) (W i-1/2)) →
    (∀ ij∈P, ∀ i, x ij i+(56*(Uref:ℝ)/modelPhaseThirdLower σ)*(N:ℝ)∈Ioo (1/2:ℝ) (W i-1/2)) →
    (1 ≤ Uref) →
    (2+168/modelPhaseThirdLower σ ≤ Bselect) →
    (7*Bcut ≤ modelPhaseThirdLower σ*Bselect) →
    (Bselect^2*(Uref:ℝ)^3*R^2 ≤ (N:ℝ)^2) →
    (∀ ab∈Gaps, R^2 ≤ ((r ab):ℝ)^2*(Uref:ℝ)) →
    (∀ ab∈Gaps, ab.2-ab.1 ≤ 7*(Uref:ℝ)/(2*R^2)) →
    (R ≤ (Q:ℝ)) →
    ((Uref:ℝ) ≤ ((N:ℝ)/(Q:ℝ))^((2:ℝ)/3)/Bselect) →
    ((N:ℝ)^10 ≤ M^3*R^7) →
    (∀ ij∈P, (rat ij 0:ℝ)∈Icc (gap ij).1 (gap ij).2) →
    (∀ ij∈P, Mat ij 2 ≠ 0) →
    (∀ ij∈P, 64*(modelPhaseJetCoefficient σ 3+δ)*M^2 ≤
      |(Mat ij 2:ℝ)| *(modelPhaseThirdLower σ)^2*T) →
    (∀ ij∈P, 8*Uband ≤ |(Mat ij 2:ℝ)| *lambda^2) →
    (1 ≤ V) →
    (∀ ab∈Gaps, ab.1∈Refs ∧ ab.2∈Refs ∧ ab.1 < ab.2 ∧
      ∀ t∈Refs, ¬(ab.1 < t ∧ t < ab.2)) →
    (Q:ℝ) ≤ (N:ℝ) →
    ((N:ℝ)^2 ≤ M ∨ (1 ≤ M ∧ (N:ℝ) ≤ T ∧ R^2 ≤ T)) → (Uref:ℝ) ≤ R^2 →
    (∀ ab∈Gaps, |((r ab):ℝ)| ≤ 4*R^2/(Uref:ℝ)) →
    (∀ ab∈Gaps, |((s ab):ℝ)| ≤ 4*R^2/(Uref:ℝ)) →
    (∀ ab∈Gaps, |((e ab):ℝ)| ≤
      (3*Jref*T/(2*σ*M^2)+1)*(4*R^2/(Uref:ℝ))) →
    (∀ ab∈Gaps, |((v ab):ℝ)| ≤
      (3*Jref*T/(2*σ*M^2)+1)*(4*R^2/(Uref:ℝ))) →
    let ε := modelPhaseThirdLower σ/(16*(σ*(σ+1)+1+2)*R^2)
    let sourceColor := fun ij i => (⌊((rat ij i).den:ℝ)/(θ*((Q:ℝ)/2))⌋,
      ⌊((rat ij i).num:ℝ)/(θ*(lambda*(Q:ℝ)/2))⌋)
    (∀ ij∈P, sourceColor ij 0=sourceColor ij 1) →
    let f := fun i => heathBrownPhysicalPhase (F i) T M (A i) 1
    (∀ ij∈P, ∀ i, iteratedDeriv 2 (f i) (x ij i)/2=(rat ij i:ℝ)) →
    let q := fun ij i => (rat ij i).den
    let mu := fun ij i => iteratedDeriv 3 (f i) (round (x ij i))/6
    let ell := fun ij i => deriv (f i) (round (x ij i))
    let b := fun ij i => (⌊(q ij i:ℝ)*ell ij i⌋+(parity ij i:ℕ) : ℤ)
    let cround := fun ij i => round ((q ij i:ℝ)*ell ij i)
    let tau := fun ij i => ((b ij i:ℝ)-(q ij i:ℝ)*ell ij i)/2
    let dual := fun ij i => -2*mu ij i*(Real.sqrt (2/(3*mu ij i*(q ij i:ℝ))))^3
    let cloud := fun ij i => (![Int.fract (-(vinv ij i:ℝ)*b ij i/q ij i),
      Int.fract (-(vinv ij i:ℝ)/q ij i),dual ij i/Real.sqrt K₀,
      (3*dual ij i*tau ij i/2)/Real.sqrt K₀] : Fin 4 → ℝ)
    let radius : Fin 4 → ℝ := ![1/(12*(K₀:ℝ)),1/(12*(K₀:ℝ)^2),(1/(K₀:ℝ)^2)/12,(1/(K₀:ℝ))/12]
    (∀ ij∈P, b ij 0-cround ij 0=b ij 1-cround ij 1) →
    (∀ ij∈P, ∀ a, |cloud ij 0 a-cloud ij 1 a| ≤ 2*radius a) →
    (∀ ij∈P,
      |cloud ij 0 1-cloud ij 1 1| ≤ 1/(6*(K₀:ℝ)^2*V)) →
    let κ := modelPhaseThirdLower σ
    let Cphys := σ*(σ+1)+1
    let c := κ/6
    let J := Cphys/6
    let B := max 1 (max (2*Real.sqrt J) (8*J*Real.sqrt J/(3*c)))
    B*R^2/(N:ℝ)^2 ≤ 1/2 →
    (N:ℝ) ≤ R^2 →
    R ≤ (N:ℝ) →
    (N:ℝ)^3 ≤ M*R^2 →
    2*R^2 ≤ (Q:ℝ)*(N:ℝ) →
    (∀ ij∈P, Mat ij 0*Mat ij 3-Mat ij 1*Mat ij 2=1) →
    (∀ ij∈P, (Mat ij 2:ℝ)*(rat ij 0:ℝ)+Mat ij 3=(q ij 1:ℝ)/q ij 0) →
    (∀ ij∈P, ((Mat ij 0:ℝ)*(rat ij 0:ℝ)+Mat ij 1)/
      ((Mat ij 2:ℝ)*(rat ij 0:ℝ)+Mat ij 3)=(rat ij 1:ℝ)) →
    (∀ ij∈P, |(Mat ij 2:ℝ)| ≤ (Q:ℝ)^2/(6*(K₀:ℝ)^2)) →
    let H := (N:ℝ)/(Cphys+2)
    2 ≤ (N:ℝ) →
    (∀ ij∈P, ∀ i, x ij i-H∈Ioo (1/2:ℝ) (W i-1/2)) →
    (∀ ij∈P, ∀ i, x ij i+H∈Ioo (1/2:ℝ) (W i-1/2)) →
    (∀ ij∈P, |(anchor ij:ℝ)-(rat ij 0:ℝ)| ≤ ε) →
    (∀ ij∈P, 256*((anchor ij).den:ℝ) ≤ (Q:ℝ)/3) →
    (∀ ij∈P, 256 ≤ (2*ε)*((Q:ℝ)/3)*(anchor ij).den) →
    let C₂ := modelPhaseJetCoefficient σ 2+δ
    let C₃ := modelPhaseJetCoefficient σ 3+δ
    let Ct := C₂/2+5*C₃/12
    let Cc := C₂/κ+C₃/(2*κ)
    let Δ := (37*B/2+16*B*Cc+2*Ct+2*Cc)*(Q:ℝ)/(N:ℝ)
    let Ccurv := (4/κ)*(B+2*quarticReciprocalConstant σ δ)
    let D := Δ+quarticNonlinearResidualConstant σ δ*(2*(Q:ℝ))/(N:ℝ)
    let Kres := 4*(37*B/2+16*B*Cc+2*Ct+2*Cc+
      2*quarticNonlinearResidualConstant σ δ)/κ
    let Esize := κ/(16*(Cphys+2))
    let Dbase := 37*B/2+16*B*Cc+2*Ct+2*Cc+2*quarticNonlinearResidualConstant σ δ
    let Tbase := (2/κ)*(B+2*quarticReciprocalConstant σ δ)
    2*3840*128^2*105*(Dbase+64*Tbase*Esize^2) ≤ Bselect*Esize →
    D ≤ 1/2 → Δ < 1/2 → 61*Ccurv*Cphys ≤ Bcut →
    let Lunit := 2*κ/Cphys
    let Gamma := Cphys/κ
    let Cthird := Gamma*(32*Kres+9*quarticReciprocalConstant σ δ)
    let Cpack := 64*Cphys*(Gamma^2*Cthird+Gamma*(modelPhaseJetCoefficient σ 3+δ)/κ)/κ
    let Cfirst := 128*Cphys*(Gamma^2*Cthird+Gamma*(modelPhaseJetCoefficient σ 3+δ)/κ)/κ^2
    let Cgap := 64*Cphys*(Gamma^2*B+Gamma*(modelPhaseJetCoefficient σ 3+δ)/κ)/κ
    let Cmain := 4*(2*Cfirst/Lunit^3)^((3:ℝ)⁻¹)+2
    let Ctail := 4*Cpack/Lunit^2+Cgap
    (P.card:ℝ) ≤
      (60*588*(Uband/lambda)^2*Uband^2*(R^8/(N:ℝ)^4)*
        (Cmain/V^((5:ℝ)/3)+Ctail/((Uref:ℝ)*V)))*T^εloss := by
  exact eventually_physicalModelPhase_actual_fourier_original_pair_mass_raw hσ hJref hεloss

#print axioms eventually_physicalModelPhase_actual_fourier_original_pair_mass_raw


private theorem eventually_model_global_large_entry_source_mass_raw
    {σ Jref εloss : ℝ} (hσ : 0 < σ) (hJref : 0 ≤ Jref) (hεloss : 0 < εloss) :
    ∀ᶠ T : ℝ in Filter.atTop, ∀ (F : Fin 2 → ℝ → ℝ)
    (Uref : ℕ) (Refs : Finset ℝ) (Gaps : Finset (ℝ × ℝ)) {Bselect : ℝ}
    (P : Finset ((ℤ × Fin 2) × (ℤ × Fin 2))) (Mat : ((ℤ × Fin 2) × (ℤ × Fin 2)) → Fin 4 → ℤ)
    (gap : ((ℤ × Fin 2) × (ℤ × Fin 2)) → ℝ × ℝ)
    (Q K₀ : ℕ) [NeZero K₀]
    (N : ℕ) (za zb : ℤ → ℝ) (AlenA AlenB : ℤ → ℕ) (Za Zb : ℤ)
    (rat : ((ℤ × Fin 2) × (ℤ × Fin 2)) → Fin 2 → ℚ)
    (vinv : ((ℤ × Fin 2) × (ℤ × Fin 2)) → Fin 2 → ℤ)
    (parity : ((ℤ × Fin 2) × (ℤ × Fin 2)) → Fin 2 → Fin 2)
    (anchor : ((ℤ × Fin 2) × (ℤ × Fin 2)) → ℚ)
    (e r v s : ℝ × ℝ → ℤ)
    {δ M R base Bcut lambda Uband θ V : ℝ}
    (A : Fin 2 → ℤ) {W : Fin 2 → ℝ},
    let x := fun ij : (ℤ × Fin 2) × (ℤ × Fin 2) => (![za ij.1.1,zb ij.2.1] : Fin 2 → ℝ)
    let xlocal := fun ij i => x ij i-(A i:ℝ)
    (∀ ij∈P, base ≤ za ij.1.1-(A 0:ℝ)) →
    (∀ ij∈P, gap ij∈Gaps) →
    (∀ ij∈P, N ≤ AlenA ij.1.1 ∧ AlenA ij.1.1 ≤ 3*N ∧
      round (za ij.1.1)+(AlenA ij.1.1:ℤ)=Za+(N:ℤ)*ij.1.1+2*(N:ℤ)) →
    (∀ ij∈P, N ≤ AlenB ij.2.1 ∧ AlenB ij.2.1 ≤ 3*N ∧
      round (zb ij.2.1)+(AlenB ij.2.1:ℤ)=Zb+(N:ℤ)*ij.2.1+2*(N:ℤ)) →
    (δ ≤ min (modelPhaseThirdLower σ) 1) →
    (∀ i, Expdb.IsApproximateModelPhaseFunction (F i) σ 4 δ) →
    (0 < T) →
    (0 < M) →
    (0 < (N:ℝ)) →
    (1 ≤ R) →
    (R ≤ M) →
    (0 < Q) →
    (T*(N:ℝ)*R^2=M^3) →
    ((Q:ℝ)*(N:ℝ) ≤ (K₀:ℝ)*R^2) →
    (∀ i, M ≤ (A i:ℝ)) →
    (∀ i, (A i:ℝ)+W i ≤ 2*M) →
    (∀ ij∈P, ∀ i, xlocal ij i∈Ioo (1/2:ℝ) (W i-1/2)) →
    (∀ ij∈P, ∀ i, (rat ij i).den ≤ Q ∧ Q ≤ 2*(rat ij i).den) →
    (0 < lambda) →
    (0 ≤ Uband) →
    (0 < θ) →
    (θ ≤ 1/24) →
    (∀ ij∈P, ∀ i, lambda ≤ |(rat ij i:ℝ)| ∧ |(rat ij i:ℝ)| ≤ Uband) →
    (∀ ij∈P, ∀ i, ((rat ij i).den:ℤ) ∣ (rat ij i).num*vinv ij i-1) →
    (∀ ab∈Gaps, (v ab)*(r ab)-(e ab)*(s ab)=1) →
    (∀ ab∈Gaps, ((0:ℝ) < (r ab) ∧ ((e ab):ℝ)/(r ab)=ab.1) ∨
      (((r ab):ℝ) < 0 ∧ ((e ab):ℝ)/(r ab)=ab.2)) →
    (0 < Bcut) →
    (∀ ab∈Gaps, (s ab) ≠ 0) →
    (∀ ab∈Gaps, ((e ab):ℝ)/(r ab)∈Refs) →
    (∀ ab∈Gaps, ((v ab):ℝ)/(s ab)∈Refs) →
    (∀ a∈Refs, ∀ b∈Refs, a ≠ b → ((Uref:ℝ)/R^2)/4 < |a-b|) →
    (∀ ij∈P, ∀ i, xlocal ij i-(56*(Uref:ℝ)/modelPhaseThirdLower σ)*(N:ℝ)∈Ioo (1/2:ℝ) (W i-1/2)) →
    (∀ ij∈P, ∀ i, xlocal ij i+(56*(Uref:ℝ)/modelPhaseThirdLower σ)*(N:ℝ)∈Ioo (1/2:ℝ) (W i-1/2)) →
    (1 ≤ Uref) →
    (2+168/modelPhaseThirdLower σ ≤ Bselect) →
    (7*Bcut ≤ modelPhaseThirdLower σ*Bselect) →
    (Bselect^2*(Uref:ℝ)^3*R^2 ≤ (N:ℝ)^2) →
    (∀ ab∈Gaps, R^2 ≤ ((r ab):ℝ)^2*(Uref:ℝ)) →
    (∀ ab∈Gaps, ab.2-ab.1 ≤ 7*(Uref:ℝ)/(2*R^2)) →
    (R ≤ (Q:ℝ)) →
    ((Uref:ℝ) ≤ ((N:ℝ)/(Q:ℝ))^((2:ℝ)/3)/Bselect) →
    ((N:ℝ)^10 ≤ M^3*R^7) →
    (∀ ij∈P, (rat ij 0:ℝ)∈Icc (gap ij).1 (gap ij).2) →
    (∀ ij∈P, Mat ij 2 ≠ 0) →
    (∀ ij∈P, 64*(modelPhaseJetCoefficient σ 3+δ)*M^2 ≤
      |(Mat ij 2:ℝ)| *(modelPhaseThirdLower σ)^2*T) →
    (∀ ij∈P, 8*Uband ≤ |(Mat ij 2:ℝ)| *lambda^2) →
    (1 ≤ V) →
    (∀ ab∈Gaps, ab.1∈Refs ∧ ab.2∈Refs ∧ ab.1 < ab.2 ∧
      ∀ t∈Refs, ¬(ab.1 < t ∧ t < ab.2)) →
    (Q:ℝ) ≤ (N:ℝ) →
    ((N:ℝ)^2 ≤ M ∨ (1 ≤ M ∧ (N:ℝ) ≤ T ∧ R^2 ≤ T)) → (Uref:ℝ) ≤ R^2 →
    (∀ ab∈Gaps, |((r ab):ℝ)| ≤ 4*R^2/(Uref:ℝ)) →
    (∀ ab∈Gaps, |((s ab):ℝ)| ≤ 4*R^2/(Uref:ℝ)) →
    (∀ ab∈Gaps, |((e ab):ℝ)| ≤
      (3*Jref*T/(2*σ*M^2)+1)*(4*R^2/(Uref:ℝ))) →
    (∀ ab∈Gaps, |((v ab):ℝ)| ≤
      (3*Jref*T/(2*σ*M^2)+1)*(4*R^2/(Uref:ℝ))) →
    let ε := modelPhaseThirdLower σ/(16*(σ*(σ+1)+1+2)*R^2)
    let sourceColor := fun ij i => (⌊((rat ij i).den:ℝ)/(θ*((Q:ℝ)/2))⌋,
      ⌊((rat ij i).num:ℝ)/(θ*(lambda*(Q:ℝ)/2))⌋)
    (∀ ij∈P, sourceColor ij 0=sourceColor ij 1) →
    let f := fun (i : Fin 2) w => T*F i (w/M)
    (∀ ij∈P, ∀ i, iteratedDeriv 2 (f i) (x ij i)/2=(rat ij i:ℝ)) →
    let q := fun ij i => (rat ij i).den
    let mu := fun ij i => iteratedDeriv 3 (f i) (round (x ij i))/6
    let ell := fun ij i => deriv (f i) (round (x ij i))
    let b := fun ij i => (⌊(q ij i:ℝ)*ell ij i⌋+(parity ij i:ℕ) : ℤ)
    let cround := fun ij i => round ((q ij i:ℝ)*ell ij i)
    let tau := fun ij i => ((b ij i:ℝ)-(q ij i:ℝ)*ell ij i)/2
    let dual := fun ij i => -2*mu ij i*(Real.sqrt (2/(3*mu ij i*(q ij i:ℝ))))^3
    let cloud := fun ij i => (![Int.fract (-(vinv ij i:ℝ)*b ij i/q ij i),
      Int.fract (-(vinv ij i:ℝ)/q ij i),dual ij i/Real.sqrt K₀,
      (3*dual ij i*tau ij i/2)/Real.sqrt K₀] : Fin 4 → ℝ)
    let radius : Fin 4 → ℝ := ![1/(12*(K₀:ℝ)),1/(12*(K₀:ℝ)^2),(1/(K₀:ℝ)^2)/12,(1/(K₀:ℝ))/12]
    (∀ ij∈P, b ij 0-cround ij 0=b ij 1-cround ij 1) →
    (∀ ij∈P, ∀ a, |cloud ij 0 a-cloud ij 1 a| ≤ 2*radius a) →
    (∀ ij∈P,
      |cloud ij 0 1-cloud ij 1 1| ≤ 1/(6*(K₀:ℝ)^2*V)) →
    let κ := modelPhaseThirdLower σ
    let Cphys := σ*(σ+1)+1
    let c := κ/6
    let J := Cphys/6
    let B := max 1 (max (2*Real.sqrt J) (8*J*Real.sqrt J/(3*c)))
    B*R^2/(N:ℝ)^2 ≤ 1/2 →
    (N:ℝ) ≤ R^2 →
    R ≤ (N:ℝ) →
    (N:ℝ)^3 ≤ M*R^2 →
    2*R^2 ≤ (Q:ℝ)*(N:ℝ) →
    (∀ ij∈P, Mat ij 0*Mat ij 3-Mat ij 1*Mat ij 2=1) →
    (∀ ij∈P, (Mat ij 2:ℝ)*(rat ij 0:ℝ)+Mat ij 3=(q ij 1:ℝ)/q ij 0) →
    (∀ ij∈P, ((Mat ij 0:ℝ)*(rat ij 0:ℝ)+Mat ij 1)/
      ((Mat ij 2:ℝ)*(rat ij 0:ℝ)+Mat ij 3)=(rat ij 1:ℝ)) →
    (∀ ij∈P, |(Mat ij 2:ℝ)| ≤ (Q:ℝ)^2/(6*(K₀:ℝ)^2)) →
    let H := (N:ℝ)/(Cphys+2)
    2 ≤ (N:ℝ) →
    (∀ ij∈P, ∀ i, xlocal ij i-H∈Ioo (1/2:ℝ) (W i-1/2)) →
    (∀ ij∈P, ∀ i, xlocal ij i+H∈Ioo (1/2:ℝ) (W i-1/2)) →
    (∀ ij∈P, |(anchor ij:ℝ)-(rat ij 0:ℝ)| ≤ ε) →
    (∀ ij∈P, 256*((anchor ij).den:ℝ) ≤ (Q:ℝ)/3) →
    (∀ ij∈P, 256 ≤ (2*ε)*((Q:ℝ)/3)*(anchor ij).den) →
    let C₂ := modelPhaseJetCoefficient σ 2+δ
    let C₃ := modelPhaseJetCoefficient σ 3+δ
    let Ct := C₂/2+5*C₃/12
    let Cc := C₂/κ+C₃/(2*κ)
    let Δ := (37*B/2+16*B*Cc+2*Ct+2*Cc)*(Q:ℝ)/(N:ℝ)
    let Ccurv := (4/κ)*(B+2*quarticReciprocalConstant σ δ)
    let D := Δ+quarticNonlinearResidualConstant σ δ*(2*(Q:ℝ))/(N:ℝ)
    let Kres := 4*(37*B/2+16*B*Cc+2*Ct+2*Cc+
      2*quarticNonlinearResidualConstant σ δ)/κ
    let Esize := κ/(16*(Cphys+2))
    let Dbase := 37*B/2+16*B*Cc+2*Ct+2*Cc+2*quarticNonlinearResidualConstant σ δ
    let Tbase := (2/κ)*(B+2*quarticReciprocalConstant σ δ)
    2*3840*128^2*105*(Dbase+64*Tbase*Esize^2) ≤ Bselect*Esize →
    D ≤ 1/2 → Δ < 1/2 → 61*Ccurv*Cphys ≤ Bcut →
    let Lunit := 2*κ/Cphys
    let Gamma := Cphys/κ
    let Cthird := Gamma*(32*Kres+9*quarticReciprocalConstant σ δ)
    let Cpack := 64*Cphys*(Gamma^2*Cthird+Gamma*(modelPhaseJetCoefficient σ 3+δ)/κ)/κ
    let Cfirst := 128*Cphys*(Gamma^2*Cthird+Gamma*(modelPhaseJetCoefficient σ 3+δ)/κ)/κ^2
    let Cgap := 64*Cphys*(Gamma^2*B+Gamma*(modelPhaseJetCoefficient σ 3+δ)/κ)/κ
    let Cmain := 4*(2*Cfirst/Lunit^3)^((3:ℝ)⁻¹)+2
    let Ctail := 4*Cpack/Lunit^2+Cgap
    (P.card:ℝ) ≤
      (60*588*(Uband/lambda)^2*Uband^2*(R^8/(N:ℝ)^4)*
        (Cmain/V^((5:ℝ)/3)+Ctail/((Uref:ℝ)*V)))*T^εloss := by
  filter_upwards [eventually_physicalModelPhase_actual_fourier_original_pair_mass_raw hσ hJref hεloss]
    with T hmass
  intro F Uref Refs Gaps Bselect P Mat gap Q K₀ _ N za zb AlenA AlenB Za Zb
    rat vinv parity anchor e r v s δ M R base Bcut lambda Uband θ V A W x xlocal
    hbase hgapMem hgeometryA hgeometryB hδ hF hT hM hN hR hRM hQ hscale hmesh hA hW hx hden hlambda hUband hθ hθmax hcurv hinv hchart horientation hBcut hs hrefSet hparentSet hsep hwideL hwideU hUref hBselectSize hcutMargin hselectedWrap hreferenceDen hgapWidth hRQ hselectedUpper hscaleTen hfamilyGap hc hlarge haction hV hgap
    hQN hNM hUR hrHeight hsHeight heHeight hvHeight
    ε sourceColor hsourceColor f hlevel q mu ell b cround tau dual cloud radius
    hcolor hnear hnearNarrow κ Cphys c J B hsmall hNR hRN hNcube hminscale
    hMatdet hMatt hMatmap hMatgamma H hNtwo hL hU hanchor hcut hcount
    C₂ C₃ Ct Cc Δ Ccurv D Kres Esize Dbase Tbase hsize hD hΔ hBsize
    Lunit Gamma Cthird Cpack Cfirst Cgap Cmain Ctail
  let flocal := fun i => heathBrownPhysicalPhase (F i) T M (A i) 1
  have hsource i : flocal i = fun w => f i ((A i:ℝ)+w) := by
    funext w
    simp only [flocal,heathBrownPhysicalPhase,f,one_mul]
  have hjet ij i k : iteratedDeriv k (flocal i) (xlocal ij i) =
      iteratedDeriv k (f i) (x ij i) := by
    rw [hsource,iteratedDeriv_comp_const_add]
    simp only [xlocal,add_sub_cancel]
  have hrjet ij i k : iteratedDeriv k (flocal i) (round (xlocal ij i)) =
      iteratedDeriv k (f i) (round (x ij i)) := by
    rw [hsource,iteratedDeriv_comp_const_add]
    simp only [xlocal,round_sub_intCast,Int.cast_sub,add_sub_cancel]
  have hrderiv ij i : deriv (flocal i) (round (xlocal ij i)) =
      deriv (f i) (round (x ij i)) := by
    simpa only [iteratedDeriv_one] using hrjet ij i 1
  let mulocal := fun ij i => iteratedDeriv 3 (flocal i) (round (xlocal ij i))/6
  let elllocal := fun ij i => deriv (flocal i) (round (xlocal ij i))
  let blocal := fun ij i => (⌊(q ij i:ℝ)*elllocal ij i⌋+(parity ij i:ℕ) : ℤ)
  let taulocal := fun ij i => ((blocal ij i:ℝ)-(q ij i:ℝ)*elllocal ij i)/2
  let duallocal := fun ij i => -2*mulocal ij i*(Real.sqrt (2/(3*mulocal ij i*(q ij i:ℝ))))^3
  let cloudlocal := fun ij i => (![Int.fract (-(vinv ij i:ℝ)*blocal ij i/q ij i),
    Int.fract (-(vinv ij i:ℝ)/q ij i),duallocal ij i/Real.sqrt K₀,
    (3*duallocal ij i*taulocal ij i/2)/Real.sqrt K₀] : Fin 4 → ℝ)
  have hcloud ij i : cloudlocal ij i=cloud ij i := by
    dsimp only [cloudlocal,duallocal,mulocal,taulocal,blocal,elllocal]
    simp only [hrjet,hrderiv]
    rfl
  have hgeomA ij (hij : ij∈P) :
      N ≤ AlenA ij.1.1 ∧ AlenA ij.1.1 ≤ 3*N ∧
        round (za ij.1.1-(A 0:ℝ))+(AlenA ij.1.1:ℤ)=
          (Za-A 0)+(N:ℤ)*ij.1.1+2*(N:ℤ) := by
    obtain ⟨hlo,hhi,he⟩ := hgeometryA ij hij
    refine ⟨hlo,hhi,?_⟩
    rw [round_sub_intCast]
    omega
  have hgeomB ij (hij : ij∈P) :
      N ≤ AlenB ij.2.1 ∧ AlenB ij.2.1 ≤ 3*N ∧
        round (zb ij.2.1-(A 1:ℝ))+(AlenB ij.2.1:ℤ)=
          (Zb-A 1)+(N:ℤ)*ij.2.1+2*(N:ℤ) := by
    obtain ⟨hlo,hhi,he⟩ := hgeometryB ij hij
    refine ⟨hlo,hhi,?_⟩
    rw [round_sub_intCast]
    omega
  apply hmass Uref Refs Gaps (Bselect:=Bselect) P Mat gap Q K₀ N
    (fun n => za n-(A 0:ℝ)) (fun n => zb n-(A 1:ℝ))
    AlenA AlenB (Za-A 0) (Zb-A 1) rat vinv parity anchor e r v s
    (δ:=δ) (M:=M) (R:=R) (base:=base) (Bcut:=Bcut)
    (lambda:=lambda) (Uband:=Uband) (θ:=θ) (V:=V) (F:=F)
    (A:=fun i => (A i:ℝ)) (W:=W) (x:=xlocal)
    hbase (by intro ij _; rfl) (by intro ij _; rfl) hgapMem hgeomA hgeomB
    hδ hF hT hM hN hR hRM hQ hscale hmesh hA hW hx hden hlambda hUband hθ hθmax hcurv
    hinv hchart horientation hBcut hs hrefSet hparentSet hsep hwideL hwideU hUref
    hBselectSize hcutMargin hselectedWrap hreferenceDen hgapWidth hRQ
    hselectedUpper hscaleTen hfamilyGap hc hlarge haction hV hgap
    hQN hNM hUR hrHeight hsHeight heHeight hvHeight hsourceColor
    (by intro ij hij i; rw [show iteratedDeriv 2 (heathBrownPhysicalPhase (F i) T M (A i) 1)
      (xlocal ij i)=iteratedDeriv 2 (f i) (x ij i) from hjet ij i 2]; exact hlevel ij hij i)
    (by
      intro ij hij
      change (⌊(q ij 0:ℝ)*deriv (flocal 0) (round (xlocal ij 0))⌋+(parity ij 0:ℕ):ℤ)-
          round ((q ij 0:ℝ)*deriv (flocal 0) (round (xlocal ij 0))) =
        (⌊(q ij 1:ℝ)*deriv (flocal 1) (round (xlocal ij 1))⌋+(parity ij 1:ℕ):ℤ)-
          round ((q ij 1:ℝ)*deriv (flocal 1) (round (xlocal ij 1)))
      rw [hrderiv,hrderiv]
      exact hcolor ij hij)
    (by
      intro ij hij d
      change |cloudlocal ij 0 d-cloudlocal ij 1 d| ≤ 2*radius d
      rw [hcloud,hcloud]
      exact hnear ij hij d)
    (by
      intro ij hij
      change |cloudlocal ij 0 1-cloudlocal ij 1 1| ≤ 1/(6*(K₀:ℝ)^2*V)
      rw [hcloud,hcloud]
      exact hnearNarrow ij hij)
    hsmall hNR hRN hNcube hminscale hMatdet hMatt hMatmap hMatgamma
    hNtwo hL hU hanchor hcut hcount hsize hD hΔ hBsize

example
    {σ Jref εloss : ℝ} (hσ : 0 < σ) (hJref : 0 ≤ Jref) (hεloss : 0 < εloss) :
    ∀ᶠ T : ℝ in Filter.atTop, ∀ (F : Fin 2 → ℝ → ℝ)
    (Uref : ℕ) (Refs : Finset ℝ) (Gaps : Finset (ℝ × ℝ)) {Bselect : ℝ}
    (P : Finset ((ℤ × Fin 2) × (ℤ × Fin 2))) (Mat : ((ℤ × Fin 2) × (ℤ × Fin 2)) → Fin 4 → ℤ)
    (gap : ((ℤ × Fin 2) × (ℤ × Fin 2)) → ℝ × ℝ)
    (Q K₀ : ℕ) [NeZero K₀]
    (N : ℕ) (za zb : ℤ → ℝ) (AlenA AlenB : ℤ → ℕ) (Za Zb : ℤ)
    (rat : ((ℤ × Fin 2) × (ℤ × Fin 2)) → Fin 2 → ℚ)
    (vinv : ((ℤ × Fin 2) × (ℤ × Fin 2)) → Fin 2 → ℤ)
    (parity : ((ℤ × Fin 2) × (ℤ × Fin 2)) → Fin 2 → Fin 2)
    (anchor : ((ℤ × Fin 2) × (ℤ × Fin 2)) → ℚ)
    (e r v s : ℝ × ℝ → ℤ)
    {δ M R base Bcut lambda Uband θ V : ℝ}
    (A : Fin 2 → ℤ) {W : Fin 2 → ℝ},
    let x := fun ij : (ℤ × Fin 2) × (ℤ × Fin 2) => (![za ij.1.1,zb ij.2.1] : Fin 2 → ℝ)
    let xlocal := fun ij i => x ij i-(A i:ℝ)
    (∀ ij∈P, base ≤ za ij.1.1-(A 0:ℝ)) →
    (∀ ij∈P, gap ij∈Gaps) →
    (∀ ij∈P, N ≤ AlenA ij.1.1 ∧ AlenA ij.1.1 ≤ 3*N ∧
      round (za ij.1.1)+(AlenA ij.1.1:ℤ)=Za+(N:ℤ)*ij.1.1+2*(N:ℤ)) →
    (∀ ij∈P, N ≤ AlenB ij.2.1 ∧ AlenB ij.2.1 ≤ 3*N ∧
      round (zb ij.2.1)+(AlenB ij.2.1:ℤ)=Zb+(N:ℤ)*ij.2.1+2*(N:ℤ)) →
    (δ ≤ min (modelPhaseThirdLower σ) 1) →
    (∀ i, Expdb.IsApproximateModelPhaseFunction (F i) σ 4 δ) →
    (0 < T) →
    (0 < M) →
    (0 < (N:ℝ)) →
    (1 ≤ R) →
    (R ≤ M) →
    (0 < Q) →
    (T*(N:ℝ)*R^2=M^3) →
    ((Q:ℝ)*(N:ℝ) ≤ (K₀:ℝ)*R^2) →
    (∀ i, M ≤ (A i:ℝ)) →
    (∀ i, (A i:ℝ)+W i ≤ 2*M) →
    (∀ ij∈P, ∀ i, xlocal ij i∈Ioo (1/2:ℝ) (W i-1/2)) →
    (∀ ij∈P, ∀ i, (rat ij i).den ≤ Q ∧ Q ≤ 2*(rat ij i).den) →
    (0 < lambda) →
    (0 ≤ Uband) →
    (0 < θ) →
    (θ ≤ 1/24) →
    (∀ ij∈P, ∀ i, lambda ≤ |(rat ij i:ℝ)| ∧ |(rat ij i:ℝ)| ≤ Uband) →
    (∀ ij∈P, ∀ i, ((rat ij i).den:ℤ) ∣ (rat ij i).num*vinv ij i-1) →
    (∀ ab∈Gaps, (v ab)*(r ab)-(e ab)*(s ab)=1) →
    (∀ ab∈Gaps, ((0:ℝ) < (r ab) ∧ ((e ab):ℝ)/(r ab)=ab.1) ∨
      (((r ab):ℝ) < 0 ∧ ((e ab):ℝ)/(r ab)=ab.2)) →
    (0 < Bcut) →
    (∀ ab∈Gaps, (s ab) ≠ 0) →
    (∀ ab∈Gaps, ((e ab):ℝ)/(r ab)∈Refs) →
    (∀ ab∈Gaps, ((v ab):ℝ)/(s ab)∈Refs) →
    (∀ a∈Refs, ∀ b∈Refs, a ≠ b → ((Uref:ℝ)/R^2)/4 < |a-b|) →
    (∀ ij∈P, ∀ i, xlocal ij i-(56*(Uref:ℝ)/modelPhaseThirdLower σ)*(N:ℝ)∈Ioo (1/2:ℝ) (W i-1/2)) →
    (∀ ij∈P, ∀ i, xlocal ij i+(56*(Uref:ℝ)/modelPhaseThirdLower σ)*(N:ℝ)∈Ioo (1/2:ℝ) (W i-1/2)) →
    (1 ≤ Uref) →
    (2+168/modelPhaseThirdLower σ ≤ Bselect) →
    (7*Bcut ≤ modelPhaseThirdLower σ*Bselect) →
    (Bselect^2*(Uref:ℝ)^3*R^2 ≤ (N:ℝ)^2) →
    (∀ ab∈Gaps, R^2 ≤ ((r ab):ℝ)^2*(Uref:ℝ)) →
    (∀ ab∈Gaps, ab.2-ab.1 ≤ 7*(Uref:ℝ)/(2*R^2)) →
    (R ≤ (Q:ℝ)) →
    ((Uref:ℝ) ≤ ((N:ℝ)/(Q:ℝ))^((2:ℝ)/3)/Bselect) →
    ((N:ℝ)^10 ≤ M^3*R^7) →
    (∀ ij∈P, (rat ij 0:ℝ)∈Icc (gap ij).1 (gap ij).2) →
    (∀ ij∈P, Mat ij 2 ≠ 0) →
    (∀ ij∈P, 64*(modelPhaseJetCoefficient σ 3+δ)*M^2 ≤
      |(Mat ij 2:ℝ)| *(modelPhaseThirdLower σ)^2*T) →
    (∀ ij∈P, 8*Uband ≤ |(Mat ij 2:ℝ)| *lambda^2) →
    (1 ≤ V) →
    (∀ ab∈Gaps, ab.1∈Refs ∧ ab.2∈Refs ∧ ab.1 < ab.2 ∧
      ∀ t∈Refs, ¬(ab.1 < t ∧ t < ab.2)) →
    (Q:ℝ) ≤ (N:ℝ) →
    ((N:ℝ)^2 ≤ M ∨ (1 ≤ M ∧ (N:ℝ) ≤ T ∧ R^2 ≤ T)) → (Uref:ℝ) ≤ R^2 →
    (∀ ab∈Gaps, |((r ab):ℝ)| ≤ 4*R^2/(Uref:ℝ)) →
    (∀ ab∈Gaps, |((s ab):ℝ)| ≤ 4*R^2/(Uref:ℝ)) →
    (∀ ab∈Gaps, |((e ab):ℝ)| ≤
      (3*Jref*T/(2*σ*M^2)+1)*(4*R^2/(Uref:ℝ))) →
    (∀ ab∈Gaps, |((v ab):ℝ)| ≤
      (3*Jref*T/(2*σ*M^2)+1)*(4*R^2/(Uref:ℝ))) →
    let ε := modelPhaseThirdLower σ/(16*(σ*(σ+1)+1+2)*R^2)
    let sourceColor := fun ij i => (⌊((rat ij i).den:ℝ)/(θ*((Q:ℝ)/2))⌋,
      ⌊((rat ij i).num:ℝ)/(θ*(lambda*(Q:ℝ)/2))⌋)
    (∀ ij∈P, sourceColor ij 0=sourceColor ij 1) →
    let f := fun (i : Fin 2) w => T*F i (w/M)
    (∀ ij∈P, ∀ i, iteratedDeriv 2 (f i) (x ij i)/2=(rat ij i:ℝ)) →
    let q := fun ij i => (rat ij i).den
    let mu := fun ij i => iteratedDeriv 3 (f i) (round (x ij i))/6
    let ell := fun ij i => deriv (f i) (round (x ij i))
    let b := fun ij i => (⌊(q ij i:ℝ)*ell ij i⌋+(parity ij i:ℕ) : ℤ)
    let cround := fun ij i => round ((q ij i:ℝ)*ell ij i)
    let tau := fun ij i => ((b ij i:ℝ)-(q ij i:ℝ)*ell ij i)/2
    let dual := fun ij i => -2*mu ij i*(Real.sqrt (2/(3*mu ij i*(q ij i:ℝ))))^3
    let cloud := fun ij i => (![Int.fract (-(vinv ij i:ℝ)*b ij i/q ij i),
      Int.fract (-(vinv ij i:ℝ)/q ij i),dual ij i/Real.sqrt K₀,
      (3*dual ij i*tau ij i/2)/Real.sqrt K₀] : Fin 4 → ℝ)
    let radius : Fin 4 → ℝ := ![1/(12*(K₀:ℝ)),1/(12*(K₀:ℝ)^2),(1/(K₀:ℝ)^2)/12,(1/(K₀:ℝ))/12]
    (∀ ij∈P, b ij 0-cround ij 0=b ij 1-cround ij 1) →
    (∀ ij∈P, ∀ a, |cloud ij 0 a-cloud ij 1 a| ≤ 2*radius a) →
    (∀ ij∈P,
      |cloud ij 0 1-cloud ij 1 1| ≤ 1/(6*(K₀:ℝ)^2*V)) →
    let κ := modelPhaseThirdLower σ
    let Cphys := σ*(σ+1)+1
    let c := κ/6
    let J := Cphys/6
    let B := max 1 (max (2*Real.sqrt J) (8*J*Real.sqrt J/(3*c)))
    B*R^2/(N:ℝ)^2 ≤ 1/2 →
    (N:ℝ) ≤ R^2 →
    R ≤ (N:ℝ) →
    (N:ℝ)^3 ≤ M*R^2 →
    2*R^2 ≤ (Q:ℝ)*(N:ℝ) →
    (∀ ij∈P, Mat ij 0*Mat ij 3-Mat ij 1*Mat ij 2=1) →
    (∀ ij∈P, (Mat ij 2:ℝ)*(rat ij 0:ℝ)+Mat ij 3=(q ij 1:ℝ)/q ij 0) →
    (∀ ij∈P, ((Mat ij 0:ℝ)*(rat ij 0:ℝ)+Mat ij 1)/
      ((Mat ij 2:ℝ)*(rat ij 0:ℝ)+Mat ij 3)=(rat ij 1:ℝ)) →
    (∀ ij∈P, |(Mat ij 2:ℝ)| ≤ (Q:ℝ)^2/(6*(K₀:ℝ)^2)) →
    let H := (N:ℝ)/(Cphys+2)
    2 ≤ (N:ℝ) →
    (∀ ij∈P, ∀ i, xlocal ij i-H∈Ioo (1/2:ℝ) (W i-1/2)) →
    (∀ ij∈P, ∀ i, xlocal ij i+H∈Ioo (1/2:ℝ) (W i-1/2)) →
    (∀ ij∈P, |(anchor ij:ℝ)-(rat ij 0:ℝ)| ≤ ε) →
    (∀ ij∈P, 256*((anchor ij).den:ℝ) ≤ (Q:ℝ)/3) →
    (∀ ij∈P, 256 ≤ (2*ε)*((Q:ℝ)/3)*(anchor ij).den) →
    let C₂ := modelPhaseJetCoefficient σ 2+δ
    let C₃ := modelPhaseJetCoefficient σ 3+δ
    let Ct := C₂/2+5*C₃/12
    let Cc := C₂/κ+C₃/(2*κ)
    let Δ := (37*B/2+16*B*Cc+2*Ct+2*Cc)*(Q:ℝ)/(N:ℝ)
    let Ccurv := (4/κ)*(B+2*quarticReciprocalConstant σ δ)
    let D := Δ+quarticNonlinearResidualConstant σ δ*(2*(Q:ℝ))/(N:ℝ)
    let Kres := 4*(37*B/2+16*B*Cc+2*Ct+2*Cc+
      2*quarticNonlinearResidualConstant σ δ)/κ
    let Esize := κ/(16*(Cphys+2))
    let Dbase := 37*B/2+16*B*Cc+2*Ct+2*Cc+2*quarticNonlinearResidualConstant σ δ
    let Tbase := (2/κ)*(B+2*quarticReciprocalConstant σ δ)
    2*3840*128^2*105*(Dbase+64*Tbase*Esize^2) ≤ Bselect*Esize →
    D ≤ 1/2 → Δ < 1/2 → 61*Ccurv*Cphys ≤ Bcut →
    let Lunit := 2*κ/Cphys
    let Gamma := Cphys/κ
    let Cthird := Gamma*(32*Kres+9*quarticReciprocalConstant σ δ)
    let Cpack := 64*Cphys*(Gamma^2*Cthird+Gamma*(modelPhaseJetCoefficient σ 3+δ)/κ)/κ
    let Cfirst := 128*Cphys*(Gamma^2*Cthird+Gamma*(modelPhaseJetCoefficient σ 3+δ)/κ)/κ^2
    let Cgap := 64*Cphys*(Gamma^2*B+Gamma*(modelPhaseJetCoefficient σ 3+δ)/κ)/κ
    let Cmain := 4*(2*Cfirst/Lunit^3)^((3:ℝ)⁻¹)+2
    let Ctail := 4*Cpack/Lunit^2+Cgap
    (P.card:ℝ) ≤
      (60*588*(Uband/lambda)^2*Uband^2*(R^8/(N:ℝ)^4)*
        (Cmain/V^((5:ℝ)/3)+Ctail/((Uref:ℝ)*V)))*T^εloss := by
  exact eventually_model_global_large_entry_source_mass_raw hσ hJref hεloss

#print axioms eventually_model_global_large_entry_source_mass_raw



/-! Existing private narrowed-sieve proofs copied solely for the scratch consumer.
No new production support modules: reuse originals when promoting. -/
universe huxleyNarrowV

private theorem huxley_narrowed_sieve_frequency_scale {N t η ζ Vscale : ℝ}
    (hN : 1≤N) (ht : t∈Icc 1 N) (hη : 0<η) (hζ : 0<ζ) (hV : 1≤Vscale) :
    let a : Fin 4 → ℝ := ![1/(12*N),1/(12*N^2*Vscale),η/12,ζ/12]
    let U : Fin 4 → ℝ := ![t,t^2,(1/η)*(t/N)^((3:ℝ)/2),(1/ζ)*Real.sqrt (t/N)]
    ∀ d, a d*|U d| ≤ 1/12 := by
  have hNp : 0<N := by linarith
  have hVp : 0<Vscale := zero_lt_one.trans_le hV
  have ht0 : 0≤t := by linarith [ht.1]
  have hv0 : 0≤t/N := div_nonneg ht0 hNp.le
  have hv1 : t/N≤1 := (div_le_one hNp).mpr ht.2
  have hp : (t/N)^((3:ℝ)/2) ≤ 1 := Real.rpow_le_one hv0 hv1 (by norm_num)
  have hroot : Real.sqrt (t/N) ≤ 1 := Real.sqrt_le_one.mpr hv1
  dsimp only
  intro d
  fin_cases d
  · change (1/(12*N))*|t|≤1/12
    rw [abs_of_nonneg ht0]
    have hh := mul_le_mul_of_nonneg_left ht.2 (by positivity : 0≤1/(12*N))
    exact hh.trans_eq (by field_simp)
  · change (1/(12*N^2*Vscale))*|t^2|≤1/12
    rw [abs_of_nonneg (sq_nonneg _)]
    have hsq : t^2≤N^2 := pow_le_pow_left₀ ht0 ht.2 2
    have hh := mul_le_mul_of_nonneg_left hsq (by positivity : 0≤1/(12*N^2*Vscale))
    calc
      _ ≤ (1/(12*N^2*Vscale))*N^2 := hh
      _ = 1/(12*Vscale) := by field_simp
      _ ≤ 1/12 := one_div_le_one_div_of_le (by norm_num) (by linarith)
  · change (η/12)*|(1/η)*(t/N)^((3:ℝ)/2)|≤1/12
    rw [abs_of_nonneg (by positivity)]
    calc
      _ = (1/12)*(t/N)^((3:ℝ)/2) := by field_simp
      _ ≤ _ := by nlinarith
  · change (ζ/12)*|(1/ζ)*Real.sqrt (t/N)|≤1/12
    rw [abs_of_nonneg (by positivity)]
    calc
      _ = (1/12)*Real.sqrt (t/N) := by field_simp
      _ ≤ _ := by nlinarith

private theorem huxley_narrowed_sieve_box_scale {N η ζ Vscale : ℝ}
    (hN : 1≤N) (hη : η∈Ioc 0 1) (hζ : ζ∈Ioc 0 1) (hV : 1≤Vscale) :
    let a : Fin 4 → ℝ := ![1/(12*N),1/(12*N^2*Vscale),η/12,ζ/12]
    let δ : Fin 4 → ℝ := ![1,1,2,2]
    (∀ d, 0<a d) ∧
    (∀ d, 1/(δ d+2*a d) ≤ (![1,1,1/2,1/2] : Fin 4 → ℝ) d) ∧
    16777216*(∏ d, (δ d+2*a d))/(∏ d, a d) ≤
      (16777216*36*12^4)*N^3*Vscale/(η*ζ) := by
  dsimp only
  let a : Fin 4 → ℝ := ![1/(12*N),1/(12*N^2*Vscale),η/12,ζ/12]
  let δ : Fin 4 → ℝ := ![1,1,2,2]
  have hNp : 0<N := by linarith
  have hVp : 0<Vscale := zero_lt_one.trans_le hV
  have hηp := hη.1
  have hζp := hζ.1
  have ha d : 0<a d := by
    fin_cases d <;> norm_num [a,Matrix.cons_val_succ] <;> positivity
  refine ⟨ha,?_,?_⟩
  · intro d
    have hb : 0 < δ d := by fin_cases d <;> norm_num [δ,Matrix.cons_val_succ]
    have hh : 1/(δ d+2*a d) ≤ 1/(δ d) :=
      one_div_le_one_div_of_le hb (by linarith [ha d])
    convert hh using 1
    fin_cases d <;> norm_num [δ,Matrix.cons_val_succ]
  · have ha1 d : a d≤1/12 := by
      fin_cases d
      · change 1/(12*N)≤1/12
        exact one_div_le_one_div_of_le (by norm_num) (by linarith)
      · change 1/(12*N^2*Vscale)≤1/12
        have hNsq : (1:ℝ) ≤ N^2 := by nlinarith
        have hNV : (1:ℝ) ≤ N^2*Vscale :=
          one_mul (1:ℝ) ▸ mul_le_mul hNsq hV zero_le_one (sq_nonneg N)
        exact one_div_le_one_div_of_le (by norm_num) (by nlinarith only [hNV])
      · change η/12≤1/12
        exact div_le_div_of_nonneg_right hη.2 (by norm_num)
      · change ζ/12≤1/12
        exact div_le_div_of_nonneg_right hζ.2 (by norm_num)
    have hD : (∏ d, (δ d+2*a d)) ≤ 36 := by
      have hb := Finset.prod_le_prod
        (fun d (_:d∈(Finset.univ:Finset (Fin 4))) => (by
          have hd : 0≤δ d := by fin_cases d <;> norm_num [δ,Matrix.cons_val_succ]
          linarith [ha d] : 0≤δ d+2*a d))
        (g := (![2,2,3,3] : Fin 4 → ℝ))
        (fun d _ => by
          have hh := ha1 d
          calc
            δ d+2*a d ≤ δ d+1 := by linarith
            _ ≤ _ := by fin_cases d <;> norm_num [δ,Matrix.cons_val_succ])
      norm_num [Fin.prod_univ_succ] at hb ⊢
      exact hb
    have hprod : (∏ d, a d) = η*ζ/(12^4*N^3*Vscale) := by
      norm_num [a,Fin.prod_univ_succ]
      field_simp
      ring
    have hp : 0<∏ d, a d := Finset.prod_pos (fun d _ => ha d)
    calc
      _ ≤ 16777216*36/(∏ d, a d) := div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hD (by norm_num)) hp.le
      _ = _ := by rw [hprod]; field_simp


private theorem huxley_narrowed_sieve_final_scale
    {N η ζ Vscale L C B a p ε : ℝ}
    (hN : 0<N) (hη : 0<η) (hζ : 0<ζ) :
    (a*p)*((L*N^3*Vscale/(η*ζ))*
      (C*η*ζ*N^((9:ℝ)+ε)*B^12)) =
    (L*C)*Vscale*N^((12:ℝ)+ε)*a*B^12*p := by
  have hpow : N^3*N^((9:ℝ)+ε)=N^((12:ℝ)+ε) := by
    rw [←Real.rpow_ofNat,←Real.rpow_add hN]
    congr 1
    ring
  rw [←hpow]
  field_simp

/-- Narrowing the inverse-coordinate tolerance by Vscale costs exactly one
factor Vscale in the source-sum twelfth-power bound. The original finite
arrays and all multiplicities are retained; first spacing is proved. -/
private theorem exists_huxleySourceCurve_narrowed_double_sieve {ε : ℝ} (hε : 0<ε) :
    ∃ C>(0:ℝ), ∀ (N : ℕ), 1≤N → ∀ (η ζ Vscale : ℝ),
      η∈Icc (1/(N:ℝ)^2) 1 → ζ∈Icc (1/(N:ℝ)) 1 → 1≤Vscale →
      ∀ (ι κ : Type huxleyNarrowV) (S : Finset ι) (T : Finset κ) (w : κ → ℂ)
        (m : κ → ℤ) (x : ι → Fin 4 → ℝ) (B : ℝ),
        0≤B → (∀ j∈T,1 ≤ m j ∧ m j≤N) →
        (∀ j∈T,‖w j‖≤1) →
        (∀ q : ℤ,((T.filter (fun j => m j=q)).card:ℝ)≤B) →
        (∀ i∈S,x i∈Icc ![0,0,-1,-1] (fun _ => 1)) →
        let U := fun j => ![(m j:ℝ),(m j:ℝ)^2,
          (1/η)*((m j:ℝ)/N)^((3:ℝ)/2),(1/ζ)*Real.sqrt ((m j:ℝ)/N)]
        let a : Fin 4 → ℝ := ![1/(12*(N:ℝ)),1/(12*(N:ℝ)^2*Vscale),η/12,ζ/12]
        (∑ i∈S,‖∑ j∈T,w j*GafniTao.fordAdditiveCharacter (∑ d,U j d*x i d)‖)^12 ≤
          C*Vscale*(N:ℝ)^((12:ℝ)+ε)*(S.card:ℝ)^10*B^12*
            (((S ×ˢ S).filter (fun ij => ∀ d, |x ij.1 d-x ij.2 d|≤2*a d)).card:ℝ) := by
  classical
  obtain ⟨C,hC,hcount⟩ := exists_bourgainSourceCurve_six_tuple_first_spacing.{huxleyNarrowV} hε
  let L : ℝ := 16777216*36*12^4
  refine ⟨L*C,by dsimp [L]; positivity,?_⟩
  intro N hN η ζ Vscale hη hζ hV ι κ S T w m x B hB hm hw hmass hx
  dsimp only
  have hNr : (1:ℝ)≤N := by exact_mod_cast hN
  have hNp : (0:ℝ)<N := by linarith
  have hηp : 0<η := lt_of_lt_of_le (by positivity) hη.1
  have hζp : 0<ζ := lt_of_lt_of_le (by positivity) hζ.1
  let a : Fin 4 → ℝ := ![1/(12*(N:ℝ)),1/(12*(N:ℝ)^2*Vscale),η/12,ζ/12]
  let D : Fin 4 → ℝ := ![1,1,2,2]
  let c : Fin 4 → ℝ := ![0,0,-1,-1]
  let U := fun j => ![(m j:ℝ),(m j:ℝ)^2,
    (1/η)*((m j:ℝ)/N)^((3:ℝ)/2),(1/ζ)*Real.sqrt ((m j:ℝ)/N)]
  let V := Fintype.piFinset (fun _ : Fin 6 => T)
  let y := fun (j : Fin 6 → κ) d => ∑ k, U (j k) d
  let P := (S ×ˢ S).filter (fun ij => ∀ d, |x ij.1 d-x ij.2 d|≤2*a d)
  let Q := (V ×ˢ V).filter (fun ij => ∀ d, |y ij.1 d-y ij.2 d|≤1/(D d+2*a d))
  let K := 16777216*(∏ d,(D d+2*a d))/(∏ d,a d)
  obtain ⟨ha,hthreshold,hscale⟩ :=
    huxley_narrowed_sieve_box_scale hNr ⟨hηp,hη.2⟩ ⟨hζp,hζ.2⟩ hV
  have hD d : 0<D d := by fin_cases d <;> norm_num [D,Matrix.cons_val_succ]
  have hU j (hj : j∈T) : ∀ d,a d*|U j d|≤1/12 :=
    huxley_narrowed_sieve_frequency_scale hNr
      (by exact ⟨by exact_mod_cast (hm j hj).1,by exact_mod_cast (hm j hj).2⟩) hηp hζp hV
  have hx' i (hi : i∈S) d : x i d∈Icc (c d) (c d+D d) := by
    refine ⟨(hx i hi).1 d,?_⟩
    have hh := (hx i hi).2 d
    fin_cases d <;> norm_num [c,D,Matrix.cons_val_succ] <;> exact hh
  have hs := bourgain_four_dimensional_sixth_power_sieve S T w x U ha hD hw hx' hU
  change (∑ i∈S,‖∑ j∈T,w j*GafniTao.fordAdditiveCharacter (∑ d,U j d*x i d)‖)^12 ≤
    (S.card:ℝ)^10*K*(P.card:ℝ)*(Q.card:ℝ) at hs
  have hfirst := hcount N hN η ζ hη hζ κ T m B hB hm hmass
  change (((V ×ˢ V).filter (fun ij => ∀ d,
      |y ij.1 d-y ij.2 d|≤(![1,1,1/2,1/2] : Fin 4 → ℝ) d)).card:ℝ) ≤
    C*η*ζ*(N:ℝ)^((9:ℝ)+ε)*B^12 at hfirst
  have hsub : Q ⊆ (V ×ˢ V).filter (fun ij => ∀ d,
      |y ij.1 d-y ij.2 d|≤(![1,1,1/2,1/2] : Fin 4 → ℝ) d) := by
    intro ij hij
    obtain ⟨hij,hnear⟩ := Finset.mem_filter.mp hij
    exact Finset.mem_filter.mpr ⟨hij,fun d => (hnear d).trans (hthreshold d)⟩
  have hQ : (Q.card:ℝ) ≤ C*η*ζ*(N:ℝ)^((9:ℝ)+ε)*B^12 :=
    (Nat.cast_le.mpr (Finset.card_le_card hsub)).trans hfirst
  have hK : 0≤K := by
    dsimp only [K]
    exact div_nonneg (mul_nonneg (by norm_num)
      (Finset.prod_nonneg (fun d _ => by linarith [hD d,ha d])))
      (Finset.prod_nonneg (fun d _ => (ha d).le))
  have hR : 0≤C*η*ζ*(N:ℝ)^((9:ℝ)+ε)*B^12 := by positivity
  have hCouter : 0≤(S.card:ℝ)^10*(P.card:ℝ) := by positivity
  have hbound := mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_right hscale hR) hCouter
  calc
    _ ≤ (S.card:ℝ)^10*K*(P.card:ℝ)*(C*η*ζ*(N:ℝ)^((9:ℝ)+ε)*B^12) :=
      hs.trans (mul_le_mul_of_nonneg_left hQ (by positivity))
    _ = ((S.card:ℝ)^10*(P.card:ℝ))*(K*(C*η*ζ*(N:ℝ)^((9:ℝ)+ε)*B^12)) := by ring
    _ ≤ ((S.card:ℝ)^10*(P.card:ℝ))*
        ((L*(N:ℝ)^3*Vscale/(η*ζ))*(C*η*ζ*(N:ℝ)^((9:ℝ)+ε)*B^12)) := hbound
    _ = _ := huxley_narrowed_sieve_final_scale hNp hηp hζp

private theorem huxley_completed_phase_normalize
    {M : ℕ} (hM : 0 < M) (x : Fin 4 → ℝ) (n : ℤ) (hn : 0 ≤ n) :
    GafniTao.fordAdditiveCharacter (∑ d,x d*
      (![(n:ℝ),(n:ℝ)^2,(n:ℝ)^((3:ℝ)/2),Real.sqrt (n:ℝ)] : Fin 4 → ℝ) d)=
    GafniTao.fordAdditiveCharacter (∑ d,
      (![(n:ℝ),(n:ℝ)^2,(M:ℝ)^2*((n:ℝ)/M)^((3:ℝ)/2),
        (M:ℝ)*Real.sqrt ((n:ℝ)/M)] : Fin 4 → ℝ) d*
      (![Int.fract (x 0),Int.fract (x 1),x 2/Real.sqrt M,x 3/Real.sqrt M] : Fin 4 → ℝ) d) := by
  have hMr : (0:ℝ) < M := Nat.cast_pos.mpr hM
  have hnr : (0:ℝ) ≤ n := by exact_mod_cast hn
  have hs : 0 < Real.sqrt M := Real.sqrt_pos.mpr hMr
  have hsq := Real.sq_sqrt hMr.le
  have hp : (M:ℝ)^((3:ℝ)/2)=(M:ℝ)*Real.sqrt M := by
    rw [show (3:ℝ)/2=1+1/2 by norm_num,Real.rpow_add hMr]
    simp only [Real.rpow_one,Real.sqrt_eq_rpow]
  have hthird : (M:ℝ)^2*((n:ℝ)/M)^((3:ℝ)/2)*(x 2/Real.sqrt M)=
      x 2*(n:ℝ)^((3:ℝ)/2) := by
    rw [Real.div_rpow hnr hMr.le,hp]
    field_simp
    rw [hsq]
    ring
  have hfourth : (M:ℝ)*Real.sqrt ((n:ℝ)/M)*(x 3/Real.sqrt M)=
      x 3*Real.sqrt (n:ℝ) := by
    rw [Real.sqrt_div hnr]
    field_simp
    rw [hsq]
    ring
  simp only [Fin.sum_univ_succ,Fin.sum_univ_zero,Matrix.cons_val_zero,
    Matrix.cons_val_succ,add_zero]
  rw [hthird,hfourth]
  simp only [GafniTao.fordAdditiveCharacter_add]
  have he1 : GafniTao.fordAdditiveCharacter (x 0*(n:ℝ))=
      GafniTao.fordAdditiveCharacter ((n:ℝ)*Int.fract (x 0)) := by
    simpa only [mul_comm] using (sargos_character_integer_fract n (x 0)).symm
  have he2 : GafniTao.fordAdditiveCharacter (x 1*(n:ℝ)^2)=
      GafniTao.fordAdditiveCharacter ((n:ℝ)^2*Int.fract (x 1)) := by
    have hh := sargos_character_integer_fract (n^2) (x 1)
    push_cast at hh
    simpa only [mul_comm] using hh.symm
  change GafniTao.fordAdditiveCharacter (x 0*(n:ℝ))*
      (GafniTao.fordAdditiveCharacter (x 1*(n:ℝ)^2)*
        (GafniTao.fordAdditiveCharacter (x 2*(n:ℝ)^((3:ℝ)/2))*
          GafniTao.fordAdditiveCharacter (x 3*Real.sqrt (n:ℝ))))=
    GafniTao.fordAdditiveCharacter ((n:ℝ)*Int.fract (x 0))*
      (GafniTao.fordAdditiveCharacter ((n:ℝ)^2*Int.fract (x 1))*
        (GafniTao.fordAdditiveCharacter (x 2*(n:ℝ)^((3:ℝ)/2))*
          GafniTao.fordAdditiveCharacter (x 3*Real.sqrt (n:ℝ))))
  rw [he1,he2]


private theorem huxley_completed_narrowed_source_sieve {ε : ℝ} (hε : 0 < ε) :
    ∃ C > (0:ℝ), ∀ (M : ℕ) [NeZero M] (Vscale : ℝ), 1≤Vscale → ∀ (ι : Type huxleyNarrowV) (S : Finset ι)
      (x : ι → Fin 4 → ℝ),
      (∀ i∈S, |x i 2| ≤ Real.sqrt M ∧ |x i 3| ≤ Real.sqrt M) →
      let y := fun i => (![Int.fract (x i 0),Int.fract (x i 1),
        x i 2/Real.sqrt M,x i 3/Real.sqrt M] : Fin 4 → ℝ)
      let a : Fin 4 → ℝ :=
        ![1/(12*(M:ℝ)),1/(12*(M:ℝ)^2*Vscale),(1/(M:ℝ)^2)/12,(1/(M:ℝ))/12]
      ∀ k : ZMod M,
      (∑ i∈S, ‖∑ j : ZMod M,ZMod.stdAddChar (-(j*k))*
        GafniTao.fordAdditiveCharacter (∑ d,x i d*
          (![(j.val+1:ℝ),(j.val+1:ℝ)^2,(j.val+1:ℝ)^((3:ℝ)/2),
            Real.sqrt (j.val+1:ℝ)] : Fin 4 → ℝ) d)‖)^12 ≤
        C*Vscale*(M:ℝ)^((12:ℝ)+ε)*(S.card:ℝ)^10*
          (((S ×ˢ S).filter (fun ij => ∀ d,|y ij.1 d-y ij.2 d| ≤ 2*a d)).card:ℝ) := by
  classical
  obtain ⟨C,hC,hsource⟩ := exists_huxleySourceCurve_narrowed_double_sieve.{huxleyNarrowV} hε
  refine ⟨C,hC,?_⟩
  intro M inst Vscale hV ι S x hx y a k
  have hM : 0 < M := Nat.pos_of_ne_zero (NeZero.ne M)
  have hMr : (0:ℝ) < M := Nat.cast_pos.mpr hM
  have hM1 : (1:ℝ) ≤ M := by exact_mod_cast hM
  have hsqrt : 0 < Real.sqrt M := Real.sqrt_pos.mpr hMr
  let T : Finset (ULift.{huxleyNarrowV} (ZMod M)) := Finset.univ
  let m := fun j : ULift.{huxleyNarrowV} (ZMod M) => (j.down.val:ℤ)+1
  let w := fun j : ULift.{huxleyNarrowV} (ZMod M) => ZMod.stdAddChar (-(j.down*k))
  have hm j (_hj : j∈T) : 1 ≤ m j ∧ m j ≤ M := by
    dsimp only [m]
    have hj := j.down.val_lt
    constructor <;> omega
  have hmass (q : ℤ) : (((T.filter (fun j => m j=q)).card):ℝ) ≤ 1 := by
    have hh : (T.filter (fun j => m j=q)).card ≤ 1 := by
      apply Finset.card_le_one.mpr
      intro j hj j' hj'
      apply ULift.ext
      apply ZMod.val_injective M
      have hjm := (Finset.mem_filter.mp hj).2
      have hjm' := (Finset.mem_filter.mp hj').2
      dsimp only [m] at hjm hjm'
      omega
    exact_mod_cast hh
  have hy i (hi : i∈S) : y i∈Icc ![0,0,-1,-1] (fun _ => 1) := by
    have h2 : |x i 2/Real.sqrt M| ≤ 1 := by
      rw [abs_div,abs_of_pos hsqrt]
      exact (div_le_one hsqrt).mpr (hx i hi).1
    have h3 : |x i 3/Real.sqrt M| ≤ 1 := by
      rw [abs_div,abs_of_pos hsqrt]
      exact (div_le_one hsqrt).mpr (hx i hi).2
    refine ⟨?_,?_⟩
    · intro d
      fin_cases d
      · exact Int.fract_nonneg _
      · exact Int.fract_nonneg _
      · exact (abs_le.mp h2).1
      · exact (abs_le.mp h3).1
    · intro d
      fin_cases d
      · exact (Int.fract_lt_one _).le
      · exact (Int.fract_lt_one _).le
      · exact (abs_le.mp h2).2
      · exact (abs_le.mp h3).2
  have hη : 1/(M:ℝ)^2∈Icc (1/(M:ℝ)^2) 1 := by
    refine ⟨le_rfl,?_⟩
    exact (div_le_one (by positivity)).mpr (by nlinarith only [hM1])
  have hζ : 1/(M:ℝ)∈Icc (1/(M:ℝ)) 1 := by
    exact ⟨le_rfl,(div_le_one hMr).mpr hM1⟩
  have hh := hsource M (by omega) (1/(M:ℝ)^2) (1/(M:ℝ))
    Vscale hη hζ hV ι (ULift.{huxleyNarrowV} (ZMod M)) S T w m y 1 (by norm_num) hm
    (fun j _ => (sargos_stdAddChar_norm _).le) hmass hy
  simp only [one_div_one_div,one_pow,mul_one] at hh
  let U := fun j : ULift.{huxleyNarrowV} (ZMod M) =>
    (![(m j:ℝ),(m j:ℝ)^2,(M:ℝ)^2*((m j:ℝ)/M)^((3:ℝ)/2),
      (M:ℝ)*Real.sqrt ((m j:ℝ)/M)] : Fin 4 → ℝ)
  have he :
      (∑ i∈S, ‖∑ j : ZMod M,ZMod.stdAddChar (-(j*k))*
        GafniTao.fordAdditiveCharacter (∑ d,x i d*
          (![(j.val+1:ℝ),(j.val+1:ℝ)^2,(j.val+1:ℝ)^((3:ℝ)/2),
            Real.sqrt (j.val+1:ℝ)] : Fin 4 → ℝ) d)‖)=
      ∑ i∈S, ‖∑ j∈T,w j*GafniTao.fordAdditiveCharacter (∑ d,U j d*y i d)‖ := by
    apply Finset.sum_congr rfl
    intro i _hi
    congr 1
    calc
      _ = ∑ j : ULift.{huxleyNarrowV} (ZMod M),w j*
          GafniTao.fordAdditiveCharacter (∑ d,x i d*
            (![(m j:ℝ),(m j:ℝ)^2,(m j:ℝ)^((3:ℝ)/2),
              Real.sqrt (m j:ℝ)] : Fin 4 → ℝ) d) := by
        apply Fintype.sum_equiv Equiv.ulift.symm
        intro j
        simp [w,m,Equiv.ulift]
      _ = _ := by
        apply Finset.sum_congr rfl
        intro j _hj
        congr 1
        exact huxley_completed_phase_normalize hM (x i) (m j) (by dsimp only [m]; omega)
  rw [he]
  exact hh


private theorem huxley_dual_physical_scale {μ q N : ℝ}
    (hμ : 0<μ) (hq : 0<q) (hN : 0<N) (hqN : q≤N)
    (hscale : 1≤μ*q^2*N) :
    1≤μ*q*N^2 ∧
    |-2*μ*(Real.sqrt (2/(3*μ*q)))^3|/Real.sqrt (μ*q*N^2) ≤ 2 := by
  have hA : 1≤μ*q*N^2 := by
    have hh := mul_le_mul_of_nonneg_left hqN (by positivity : 0≤μ*q*N)
    nlinarith
  refine ⟨hA,?_⟩
  have hs := Real.sq_sqrt (by positivity : 0≤2/(3*μ*q))
  have ht := Real.sq_sqrt (by positivity : 0≤μ*q*N^2)
  have hs0 := Real.sqrt_nonneg (2/(3*μ*q))
  have ht0 := Real.sqrt_pos.mpr (by positivity : 0<μ*q*N^2)
  have hden : 0<3*μ*q := by positivity
  have hs' : (Real.sqrt (2/(3*μ*q)))^2*(3*μ*q)=2 :=
    (eq_div_iff hden.ne').mp hs
  rw [abs_mul,abs_mul,abs_of_nonpos (by norm_num : (-2:ℝ)≤0),
    abs_of_pos hμ,abs_of_nonneg (by positivity)]
  apply (div_le_iff₀ ht0).mpr
  have hh : (μ*q^2*N)^2≥1 := by nlinarith
  have he : (μ*(Real.sqrt (2/(3*μ*q)))^3)^2*(27*μ*q^3)=8 := by
    nlinarith [show ((Real.sqrt (2/(3*μ*q)))^2*(3*μ*q))^3=8 by rw [hs']; norm_num]
  have hcomp : (μ*(Real.sqrt (2/(3*μ*q)))^3)^2 ≤ μ*q*N^2 := by
    apply (mul_le_mul_iff_left₀ (show 0<27*μ*q^3 by positivity)).mp
    rw [he]
    nlinarith
  nlinarith [show 0≤μ*(Real.sqrt (2/(3*μ*q)))^3 by positivity]

private theorem huxley_actual_dual_source_box
    {M q N : ℕ} [NeZero M] (hq : 0 < q) (hN : 1 ≤ N) (hqN : q ≤ N)
    {μ ℓ : ℝ} (hμ : 0 < μ) (hscale : 1 ≤ μ*(q:ℝ)^2*N)
    (hM : 7*(μ*(q:ℝ)*(N:ℝ)^2) ≤ M) (r : ℤ) (p : Fin 2) :
    let b : ℤ := ⌊(q:ℝ)*ℓ⌋+(p:ℕ)
    let τ := ((b:ℝ)-(q:ℝ)*ℓ)/2
    let K := -2*μ*(Real.sqrt (2/(3*μ*(q:ℝ))))^3
    let x : Fin 4 → ℝ := ![-(r:ℝ)*b/q,-(r:ℝ)/q,K,3*K*τ/2]
    |x 2| ≤ Real.sqrt M ∧ |x 3| ≤ Real.sqrt M := by
  intro b τ K x
  let A := μ*(q:ℝ)*(N:ℝ)^2
  have hqr : (0:ℝ) < q := Nat.cast_pos.mpr hq
  have hNr : (0:ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hqNr : (q:ℝ) ≤ N := by exact_mod_cast hqN
  obtain ⟨hA,hK⟩ := huxley_dual_physical_scale hμ hqr hNr hqNr hscale
  change 1 ≤ A at hA
  change |K|/Real.sqrt A ≤ 2 at hK
  have hA0 : 0 < A := by linarith only [hA]
  have hKA : |K| ≤ 2*Real.sqrt A := (div_le_iff₀ (Real.sqrt_pos.mpr hA0)).mp hK
  have hKA2 : |K|^2 ≤ 4*A := by
    nlinarith [Real.sq_sqrt hA0.le,Real.sqrt_nonneg A,abs_nonneg K]
  have hMr : (0:ℝ) ≤ M := Nat.cast_nonneg M
  have hKM : |K| ≤ Real.sqrt M := by
    change 7*A ≤ M at hM
    nlinarith [Real.sq_sqrt hMr,Real.sqrt_nonneg (M:ℝ),abs_nonneg K]
  have hp0 : (0:ℝ) ≤ p.val := Nat.cast_nonneg _
  have hp1 : (p.val:ℝ) ≤ 1 := by exact_mod_cast (by omega : p.val ≤ 1)
  have ht : |τ| ≤ 1/2 := by
    have hlo := Int.floor_le ((q:ℝ)*ℓ)
    have hhi := Int.lt_floor_add_one ((q:ℝ)*ℓ)
    dsimp only [τ,b]
    rw [Int.cast_add,Int.cast_natCast]
    exact abs_le.mpr ⟨by linarith,by linarith⟩
  constructor
  · exact hKM
  · change |3*K*τ/2| ≤ Real.sqrt M
    rw [abs_div,abs_mul,abs_mul]
    norm_num
    have hh := mul_le_mul_of_nonneg_left ht (abs_nonneg K)
    nlinarith [Real.sqrt_nonneg (M:ℝ)]

private theorem huxley_completed_colored_source_sieve {ε : ℝ} (hε : 0 < ε) :
    ∃ C > (0:ℝ), ∀ (K₀ : ℕ) [NeZero K₀] (Vscale : ℝ), 1 ≤ Vscale →
      ∀ (ι : Type huxleyNarrowV) (S : Finset ι) (x : ι → Fin 4 → ℝ)
      {κ : Type*} [DecidableEq κ] (color : ι → κ) (Cap : ℝ),
      (∀ i∈S, |x i 2| ≤ Real.sqrt K₀ ∧ |x i 3| ≤ Real.sqrt K₀) →
      ((S.image color).card:ℝ) ≤ Cap →
      let w := fun i => (![Int.fract (x i 0),Int.fract (x i 1),
        x i 2/Real.sqrt K₀,x i 3/Real.sqrt K₀] : Fin 4 → ℝ)
      let radius : Fin 4 → ℝ :=
        ![1/(12*(K₀:ℝ)),1/(12*(K₀:ℝ)^2*Vscale),(1/(K₀:ℝ)^2)/12,(1/(K₀:ℝ))/12]
      let Fiber := fun key => S.filter (fun i => color i=key)
      let P := fun key => ((Fiber key) ×ˢ (Fiber key)).filter
        (fun ij => ∀ d, |w ij.1 d-w ij.2 d| ≤ 2*radius d)
      ∀ k : ZMod K₀,
        (∑ i∈S, ‖∑ j : ZMod K₀,ZMod.stdAddChar (-(j*k))*
          GafniTao.fordAdditiveCharacter (∑ d,x i d*
            (![(j.val+1:ℝ),(j.val+1:ℝ)^2,(j.val+1:ℝ)^((3:ℝ)/2),
              Real.sqrt (j.val+1:ℝ)] : Fin 4 → ℝ) d)‖)^12 ≤
          C*Vscale*(K₀:ℝ)^((12:ℝ)+ε)*Cap^11*
            ∑ key∈S.image color,((Fiber key).card:ℝ)^10*((P key).card:ℝ) := by
  classical
  obtain ⟨C,hC,hsieve⟩ := huxley_completed_narrowed_source_sieve.{huxleyNarrowV} hε
  refine ⟨C,hC,?_⟩
  intro K₀ inst Vscale hV ι S x κ instKey color Cap hx hcap w radius Fiber P k
  let mass := fun i => ‖∑ j : ZMod K₀,ZMod.stdAddChar (-(j*k))*
    GafniTao.fordAdditiveCharacter (∑ d,x i d*
      (![(j.val+1:ℝ),(j.val+1:ℝ)^2,(j.val+1:ℝ)^((3:ℝ)/2),
        Real.sqrt (j.val+1:ℝ)] : Fin 4 → ℝ) d)‖
  let Keys := S.image color
  let g := fun key => ∑ i∈Fiber key,mass i
  have hmass i : 0 ≤ mass i := norm_nonneg _
  have hg key : 0 ≤ g key := Finset.sum_nonneg (fun i _ => hmass i)
  have he : (∑ key∈Keys,g key)=∑ i∈S,mass i :=
    Finset.sum_fiberwise_of_maps_to (fun i hi => Finset.mem_image_of_mem color hi) mass
  have hholder := Real.rpow_sum_le_const_mul_sum_rpow_of_nonneg Keys
    (f:=g) (p:=(12:ℝ)) (by norm_num) (fun key _ => hg key)
  have hh : (∑ key∈Keys,g key)^12 ≤
      (Keys.card:ℝ)^11*∑ key∈Keys,(g key)^12 := by
    simpa only [show (12:ℝ)-1=11 by norm_num,Real.rpow_ofNat] using hholder
  have hcost : (∑ i∈S,mass i)^12 ≤ Cap^11*∑ key∈Keys,(g key)^12 := by
    rw [←he]
    exact hh.trans (mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ (Nat.cast_nonneg _) hcap 11)
      (Finset.sum_nonneg (fun key _ => pow_nonneg (hg key) 12)))
  have hfiber key : (g key)^12 ≤
      C*Vscale*(K₀:ℝ)^((12:ℝ)+ε)*((Fiber key).card:ℝ)^10*((P key).card:ℝ) := by
    exact hsieve K₀ Vscale hV ι (Fiber key) x
      (fun i hi => hx i (Finset.mem_filter.mp hi).1) k
  have hCap : 0 ≤ Cap := (Nat.cast_nonneg (S.image color).card).trans hcap
  change (∑ i∈S,mass i)^12 ≤ _
  calc
    _ ≤ Cap^11*∑ key∈Keys,(g key)^12 := hcost
    _ ≤ Cap^11*∑ key∈Keys,
        (C*Vscale*(K₀:ℝ)^((12:ℝ)+ε)*((Fiber key).card:ℝ)^10*((P key).card:ℝ)) :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun key _ => hfiber key))
        (pow_nonneg hCap 11)
    _ = _ := by
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro key _
      ring


example {N t η ζ Vscale : ℝ}
    (hN : 1≤N) (ht : t∈Icc 1 N) (hη : 0<η) (hζ : 0<ζ) (hV : 1≤Vscale) :
    let a : Fin 4 → ℝ := ![1/(12*N),1/(12*N^2*Vscale),η/12,ζ/12]
    let U : Fin 4 → ℝ := ![t,t^2,(1/η)*(t/N)^((3:ℝ)/2),(1/ζ)*Real.sqrt (t/N)]
    ∀ d, a d*|U d| ≤ 1/12 := by
  exact huxley_narrowed_sieve_frequency_scale hN ht hη hζ hV

#print axioms huxley_narrowed_sieve_frequency_scale

example {N η ζ Vscale : ℝ}
    (hN : 1≤N) (hη : η∈Ioc 0 1) (hζ : ζ∈Ioc 0 1) (hV : 1≤Vscale) :
    let a : Fin 4 → ℝ := ![1/(12*N),1/(12*N^2*Vscale),η/12,ζ/12]
    let δ : Fin 4 → ℝ := ![1,1,2,2]
    (∀ d, 0<a d) ∧
    (∀ d, 1/(δ d+2*a d) ≤ (![1,1,1/2,1/2] : Fin 4 → ℝ) d) ∧
    16777216*(∏ d, (δ d+2*a d))/(∏ d, a d) ≤
      (16777216*36*12^4)*N^3*Vscale/(η*ζ) := by
  exact huxley_narrowed_sieve_box_scale hN hη hζ hV

#print axioms huxley_narrowed_sieve_box_scale

example
    {N η ζ Vscale L C B a p ε : ℝ}
    (hN : 0<N) (hη : 0<η) (hζ : 0<ζ) :
    (a*p)*((L*N^3*Vscale/(η*ζ))*
      (C*η*ζ*N^((9:ℝ)+ε)*B^12)) =
    (L*C)*Vscale*N^((12:ℝ)+ε)*a*B^12*p := by
  exact huxley_narrowed_sieve_final_scale hN hη hζ

#print axioms huxley_narrowed_sieve_final_scale

example {ε : ℝ} (hε : 0<ε) :
    ∃ C>(0:ℝ), ∀ (N : ℕ), 1≤N → ∀ (η ζ Vscale : ℝ),
      η∈Icc (1/(N:ℝ)^2) 1 → ζ∈Icc (1/(N:ℝ)) 1 → 1≤Vscale →
      ∀ (ι κ : Type huxleyNarrowV) (S : Finset ι) (T : Finset κ) (w : κ → ℂ)
        (m : κ → ℤ) (x : ι → Fin 4 → ℝ) (B : ℝ),
        0≤B → (∀ j∈T,1 ≤ m j ∧ m j≤N) →
        (∀ j∈T,‖w j‖≤1) →
        (∀ q : ℤ,((T.filter (fun j => m j=q)).card:ℝ)≤B) →
        (∀ i∈S,x i∈Icc ![0,0,-1,-1] (fun _ => 1)) →
        let U := fun j => ![(m j:ℝ),(m j:ℝ)^2,
          (1/η)*((m j:ℝ)/N)^((3:ℝ)/2),(1/ζ)*Real.sqrt ((m j:ℝ)/N)]
        let a : Fin 4 → ℝ := ![1/(12*(N:ℝ)),1/(12*(N:ℝ)^2*Vscale),η/12,ζ/12]
        (∑ i∈S,‖∑ j∈T,w j*GafniTao.fordAdditiveCharacter (∑ d,U j d*x i d)‖)^12 ≤
          C*Vscale*(N:ℝ)^((12:ℝ)+ε)*(S.card:ℝ)^10*B^12*
            (((S ×ˢ S).filter (fun ij => ∀ d, |x ij.1 d-x ij.2 d|≤2*a d)).card:ℝ) := by
  exact exists_huxleySourceCurve_narrowed_double_sieve hε

#print axioms exists_huxleySourceCurve_narrowed_double_sieve

example
    {M : ℕ} (hM : 0 < M) (x : Fin 4 → ℝ) (n : ℤ) (hn : 0 ≤ n) :
    GafniTao.fordAdditiveCharacter (∑ d,x d*
      (![(n:ℝ),(n:ℝ)^2,(n:ℝ)^((3:ℝ)/2),Real.sqrt (n:ℝ)] : Fin 4 → ℝ) d)=
    GafniTao.fordAdditiveCharacter (∑ d,
      (![(n:ℝ),(n:ℝ)^2,(M:ℝ)^2*((n:ℝ)/M)^((3:ℝ)/2),
        (M:ℝ)*Real.sqrt ((n:ℝ)/M)] : Fin 4 → ℝ) d*
      (![Int.fract (x 0),Int.fract (x 1),x 2/Real.sqrt M,x 3/Real.sqrt M] : Fin 4 → ℝ) d) := by
  exact huxley_completed_phase_normalize hM x n hn

#print axioms huxley_completed_phase_normalize

example {ε : ℝ} (hε : 0 < ε) :
    ∃ C > (0:ℝ), ∀ (M : ℕ) [NeZero M] (Vscale : ℝ), 1≤Vscale → ∀ (ι : Type huxleyNarrowV) (S : Finset ι)
      (x : ι → Fin 4 → ℝ),
      (∀ i∈S, |x i 2| ≤ Real.sqrt M ∧ |x i 3| ≤ Real.sqrt M) →
      let y := fun i => (![Int.fract (x i 0),Int.fract (x i 1),
        x i 2/Real.sqrt M,x i 3/Real.sqrt M] : Fin 4 → ℝ)
      let a : Fin 4 → ℝ :=
        ![1/(12*(M:ℝ)),1/(12*(M:ℝ)^2*Vscale),(1/(M:ℝ)^2)/12,(1/(M:ℝ))/12]
      ∀ k : ZMod M,
      (∑ i∈S, ‖∑ j : ZMod M,ZMod.stdAddChar (-(j*k))*
        GafniTao.fordAdditiveCharacter (∑ d,x i d*
          (![(j.val+1:ℝ),(j.val+1:ℝ)^2,(j.val+1:ℝ)^((3:ℝ)/2),
            Real.sqrt (j.val+1:ℝ)] : Fin 4 → ℝ) d)‖)^12 ≤
        C*Vscale*(M:ℝ)^((12:ℝ)+ε)*(S.card:ℝ)^10*
          (((S ×ˢ S).filter (fun ij => ∀ d,|y ij.1 d-y ij.2 d| ≤ 2*a d)).card:ℝ) := by
  exact huxley_completed_narrowed_source_sieve hε

#print axioms huxley_completed_narrowed_source_sieve

example {μ q N : ℝ}
    (hμ : 0<μ) (hq : 0<q) (hN : 0<N) (hqN : q≤N)
    (hscale : 1≤μ*q^2*N) :
    1≤μ*q*N^2 ∧
    |-2*μ*(Real.sqrt (2/(3*μ*q)))^3|/Real.sqrt (μ*q*N^2) ≤ 2 := by
  exact huxley_dual_physical_scale hμ hq hN hqN hscale

#print axioms huxley_dual_physical_scale

example
    {M q N : ℕ} [NeZero M] (hq : 0 < q) (hN : 1 ≤ N) (hqN : q ≤ N)
    {μ ℓ : ℝ} (hμ : 0 < μ) (hscale : 1 ≤ μ*(q:ℝ)^2*N)
    (hM : 7*(μ*(q:ℝ)*(N:ℝ)^2) ≤ M) (r : ℤ) (p : Fin 2) :
    let b : ℤ := ⌊(q:ℝ)*ℓ⌋+(p:ℕ)
    let τ := ((b:ℝ)-(q:ℝ)*ℓ)/2
    let K := -2*μ*(Real.sqrt (2/(3*μ*(q:ℝ))))^3
    let x : Fin 4 → ℝ := ![-(r:ℝ)*b/q,-(r:ℝ)/q,K,3*K*τ/2]
    |x 2| ≤ Real.sqrt M ∧ |x 3| ≤ Real.sqrt M := by
  exact huxley_actual_dual_source_box hq hN hqN hμ hscale hM r p

#print axioms huxley_actual_dual_source_box

example {ε : ℝ} (hε : 0 < ε) :
    ∃ C > (0:ℝ), ∀ (K₀ : ℕ) [NeZero K₀] (Vscale : ℝ), 1 ≤ Vscale →
      ∀ (ι : Type huxleyNarrowV) (S : Finset ι) (x : ι → Fin 4 → ℝ)
      {κ : Type*} [DecidableEq κ] (color : ι → κ) (Cap : ℝ),
      (∀ i∈S, |x i 2| ≤ Real.sqrt K₀ ∧ |x i 3| ≤ Real.sqrt K₀) →
      ((S.image color).card:ℝ) ≤ Cap →
      let w := fun i => (![Int.fract (x i 0),Int.fract (x i 1),
        x i 2/Real.sqrt K₀,x i 3/Real.sqrt K₀] : Fin 4 → ℝ)
      let radius : Fin 4 → ℝ :=
        ![1/(12*(K₀:ℝ)),1/(12*(K₀:ℝ)^2*Vscale),(1/(K₀:ℝ)^2)/12,(1/(K₀:ℝ))/12]
      let Fiber := fun key => S.filter (fun i => color i=key)
      let P := fun key => ((Fiber key) ×ˢ (Fiber key)).filter
        (fun ij => ∀ d, |w ij.1 d-w ij.2 d| ≤ 2*radius d)
      ∀ k : ZMod K₀,
        (∑ i∈S, ‖∑ j : ZMod K₀,ZMod.stdAddChar (-(j*k))*
          GafniTao.fordAdditiveCharacter (∑ d,x i d*
            (![(j.val+1:ℝ),(j.val+1:ℝ)^2,(j.val+1:ℝ)^((3:ℝ)/2),
              Real.sqrt (j.val+1:ℝ)] : Fin 4 → ℝ) d)‖)^12 ≤
          C*Vscale*(K₀:ℝ)^((12:ℝ)+ε)*Cap^11*
            ∑ key∈S.image color,((Fiber key).card:ℝ)^10*((P key).card:ℝ) := by
  exact huxley_completed_colored_source_sieve hε

#print axioms huxley_completed_colored_source_sieve


/-- The actual double-shift completed Fourier sums use a joint rational/parity
coloring and the SAME matrices as both elementary source counts. The narrowing
cost and original color-fiber multiplicities are retained exactly. -/
private theorem double_difference_actual_joint_narrowed_sieve
    {c U L εloss : ℝ} (hc : 0 < c) (hU : 0 < U) (hL : 0 ≤ L) (hεloss : 0 < εloss) :
    ∃ Dtype C : ℝ, 0 < Dtype ∧ 0 < C ∧
    ∀ (S : Finset (ℝ × ℤ)) (F rshift sshift : ℝ → ℝ)
      (z : (ℝ × ℤ) → ℝ) (r : (ℝ × ℤ) → ℚ) (v : (ℝ × ℤ) → ℤ)
      (Alen : (ℝ × ℤ) → ℕ) (Z : ℝ → ℤ)
      (Q K₀ N : ℕ) [NeZero K₀] (d Wmax T M Jsep : ℝ)
      (Nlen : (ℝ × ℤ) → ℕ) (Vscale Rphys : ℝ),
    (∀ u, 0 < u → ContDiffAt ℝ ∞ F u) →
    (∀ u∈Icc (1/2:ℝ) 3, c ≤ iteratedDeriv 5 F u) →
    (∀ u∈Icc (1/2:ℝ) 3, ∀ n, 1 ≤ n → n ≤ 7 → |iteratedDeriv n F u| ≤ U) →
    (∀ u∈Icc (1/2:ℝ) 3,
      c ≤ |(iteratedDeriv 5 F u)^2-iteratedDeriv 4 F u*iteratedDeriv 6 F u|) →
    (∀ u∈Icc (1/2:ℝ) 3, iteratedDeriv 4 F u ≤ -c) →
    0 < d → 0 ≤ Wmax → Wmax ≤ 1/4 → 2*U*Wmax ≤ c/64 →
    0 < T → 2 ≤ M → 0 < N → 0 < Q →
    0 < Jsep → (N:ℝ) ≤ M → Jsep ≤ M → Wmax*Jsep ≤ 1 →
    (∀ i∈S, i.1∈Icc (1:ℝ) 2) →
    (∀ i∈S, z i∈Icc M (2*M)) →
    (∀ i∈S, N ≤ Alen i ∧ Alen i ≤ 3*N ∧
      round (z i)+(Alen i:ℤ)=Z i.1+(N:ℤ)*i.2+2*(N:ℤ)) →
    (∀ i∈S, ∀ j∈S, i.1≠j.1 → 1 ≤ Jsep*|i.1-j.1|) →
    (∀ y∈S.image Prod.fst,
      0 ≤ rshift y ∧ 0 ≤ sshift y ∧ rshift y*sshift y=d*y ∧ rshift y+sshift y ≤ Wmax) →
    let Φ := fun y u =>
      (F u-F (u+rshift y)-F (u+sshift y)+F (u+rshift y+sshift y))/d
    let f := fun i : ℝ × ℤ => fun u => T*Φ i.1 (u/M)
    (∀ i∈S, iteratedDeriv 2 (f i) (z i)/2=(r i:ℝ)) →
    (∀ i∈S, (r i).den ≤ Q ∧ Q ≤ 2*(r i).den) →
    (∀ i∈S, ((r i).den:ℤ) ∣ (r i).num*v i-1) →
    let μ₀ := c*T/(12*M^3)
    let U₀ := U*T/(2*M^3)
    let q := fun i => (r i).den
    let μ := fun i => iteratedDeriv 3 (f i) (round (z i))/6
    1 ≤ Vscale → (Q:ℝ)*(N:ℝ) ≤ (K₀:ℝ)*Rphys^2 →
    (∀ i∈S, 1 ≤ Nlen i ∧ q i ≤ Nlen i ∧ 1 ≤ μ i*(q i:ℝ)^2*Nlen i) →
    (∀ i∈S, 7*(μ i*(q i:ℝ)*(Nlen i:ℝ)^2) ≤ K₀) →
    let ℓ := fun i => deriv (f i) (round (z i))
    let b := fun i (p : Fin 2) => (⌊(q i:ℝ)*ℓ i⌋+(p:ℕ) : ℤ)
    let τ := fun i p => ((b i p:ℝ)-(q i:ℝ)*ℓ i)/2
    let K := fun i => -2*μ i*(Real.sqrt (2/(3*μ i*(q i:ℝ))))^3
    let x := fun i p =>
      (![-(v i:ℝ)*b i p/q i,-(v i:ℝ)/q i,K i,3*K i*τ i p/2] : Fin 4 → ℝ)
    let V := S ×ˢ (Finset.univ : Finset (Fin 2))
    let w := fun ip : (ℝ × ℤ) × Fin 2 =>
      (![Int.fract (x ip.1 ip.2 0),Int.fract (x ip.1 ip.2 1),
        x ip.1 ip.2 2/Real.sqrt K₀,x ip.1 ip.2 3/Real.sqrt K₀] : Fin 4 → ℝ)
    let radius : Fin 4 → ℝ :=
      ![1/(12*(K₀:ℝ)),1/(12*(K₀:ℝ)^2),(1/(K₀:ℝ)^2)/12,(1/(K₀:ℝ))/12]
    let P := (V ×ˢ V).filter (fun ij => ∀ d, |w ij.1 d-w ij.2 d| ≤ 2*radius d)
    let h := fun i => iteratedDeriv 2 (f i) (z i)/2
    let D := (Real.sqrt K₀/(9*(K₀:ℝ))+Real.sqrt K₀/(12*(K₀:ℝ)^2))*
      Real.sqrt (U₀*(Q:ℝ)^3)
    let δ := 1/(8*(L+3))
    let lambda := c*T/(2*M^2)
    let Hcurv := U*T/M^2
    let q₀ := (Q:ℝ)/2
    let p₀ := lambda*(Q:ℝ)/2
    let color := fun i => (⌊((r i).den:ℝ)/(δ*q₀)⌋,⌊((r i).num:ℝ)/(δ*p₀)⌋)
    let Cap := (4/δ+3)*(8*U/(c*δ)+3)
    let offset := fun ip : (ℝ × ℤ) × Fin 2 => b ip.1 ip.2-round ((q ip.1:ℝ)*ℓ ip.1)
    let joint := fun ip : (ℝ × ℤ) × Fin 2 => (color ip.1,offset ip)
    let narrowRadius : Fin 4 → ℝ :=
      ![1/(12*(K₀:ℝ)),1/(12*(K₀:ℝ)^2*Vscale),(1/(K₀:ℝ)^2)/12,(1/(K₀:ℝ))/12]
    let Fiber := fun key => V.filter (fun ip => joint ip=key)
    let Pairs := fun key => ((Fiber key) ×ˢ (Fiber key)).filter
      (fun ij => ∀ a, |w ij.1 a-w ij.2 a| ≤ 2*narrowRadius a)
    let Pall := (V ×ˢ V).filter
      (fun ij => ∀ a, |w ij.1 a-w ij.2 a| ≤ 2*narrowRadius a)
    ((S.image color).card:ℝ) ≤ Cap ∧
    (∀ coeff : (ℝ × ℤ) → ℂ, ‖∑ i∈S,coeff i‖^12 ≤ Cap^11*
      ∑ j∈S.image color, ‖∑ i∈S.filter (fun i => color i=j),coeff i‖^12) ∧
    ∃ A : (((ℝ × ℤ) × Fin 2) × ((ℝ × ℤ) × Fin 2)) → Fin 4 → ℤ,
      (∀ ij∈P,
        A ij 0*A ij 3-A ij 1*A ij 2=1 ∧
        let t := (A ij 2:ℝ)*h ij.1.1+A ij 3
        t=(q ij.2.1:ℝ)/q ij.1.1 ∧ (1:ℝ)/2 ≤ t ∧ t ≤ 2 ∧
        ((A ij 0:ℝ)*h ij.1.1+A ij 1)/t=h ij.2.1 ∧
        |(A ij 2:ℝ)| ≤ (Q:ℝ)^2/(6*(K₀:ℝ)^2) ∧
        |μ ij.2.1/μ ij.1.1*t^3-1| ≤
          (16*U₀/μ₀)*Real.sqrt (U₀*(Q:ℝ)^3)*Real.sqrt K₀/(6*(K₀:ℝ)^2) ∧
        |τ ij.1.1 ij.1.2-τ ij.2.1 ij.2.2| ≤ D ∧
        (∃ e₁ e₂ : ℤ,
          let F₁ := 2*(round (z ij.2.1):ℝ)-2*(A ij 3:ℝ)*(round (z ij.1.1):ℝ)-
            (A ij 2:ℝ)*ℓ ij.1.1
          let F₂ := ℓ ij.2.1-2*(A ij 1:ℝ)*(round (z ij.1.1):ℝ)-
            (A ij 0:ℝ)*ℓ ij.1.1
          |F₁-e₁| ≤ (q ij.2.1:ℝ)/(6*(K₀:ℝ))+|(A ij 2:ℝ)|/q ij.1.1 ∧
          |(F₂-e₂)-h ij.2.1*(F₁-e₁)| ≤ 2*D/q ij.2.1) ∧
        ((Q:ℝ)^2/(6*(K₀:ℝ)^2) < 1 →
          A ij 2=0 ∧ q ij.1.1=q ij.2.1 ∧
            (q ij.1.1:ℤ) ∣ (r ij.2.1).num-(r ij.1.1).num)) ∧
      (∀ ij∈P, color ij.1.1=color ij.2.1 →
        let t := (A ij 2:ℝ)*h ij.1.1+A ij 3
        |t-1| ≤ δ ∧
        |((A ij 0:ℝ)*h ij.1.1+A ij 1)/h ij.1.1-1| ≤ δ ∧
        ((A ij 0=1 ∧ A ij 1=0 ∧ A ij 2=0 ∧ A ij 3=1) ∨
         (A ij 0=1 ∧ A ij 3=1 ∧ A ij 2=0 ∧ A ij 1≠0 ∧ |(A ij 1:ℝ)| ≤ δ*Hcurv) ∨
         (A ij 0=1 ∧ A ij 3=1 ∧ A ij 1=0 ∧ A ij 2≠0 ∧ |(A ij 2:ℝ)| ≤ δ/lambda) ∨
         (A ij 1≠0 ∧ A ij 2≠0)) ∧
        (|(A ij 2:ℝ)| * Hcurv ≤ L →
          A ij 0+A ij 3=2 ∧ (A ij 0-1)^2= -A ij 1*A ij 2)) ∧
      let E := P.filter (fun ij =>
        color ij.1.1=color ij.2.1 ∧
        ((A ij 0=1 ∧ A ij 1=0 ∧ A ij 2=0 ∧ A ij 3=1) ∨
         (A ij 1≠0 ∧ A ij 2≠0 ∧ |(A ij 2:ℝ)| * Hcurv ≤ L)))
      let Δ := (16*U₀/μ₀)*Real.sqrt (U₀*(Q:ℝ)^3)*Real.sqrt K₀/(6*(K₀:ℝ)^2)
      (E.card:ℝ) ≤ Dtype*((S.image Prod.fst).card:ℝ)*(M/(N:ℝ))*(1+Δ*Jsep) ∧
      let Etri := P.filter (fun ij =>
        color ij.1.1=color ij.2.1 ∧ (A ij 2=0 ∨ A ij 1=0))
      (Etri.card:ℝ) ≤ Dtype*(1+δ*(Hcurv+1/lambda))*
        ((S.image Prod.fst).card:ℝ)*(M/(N:ℝ))*(1+Δ*Jsep) ∧
      ((V.image joint).card:ℝ) ≤ 3*Cap ∧
      (∀ k : ZMod K₀,
        (∑ ip∈V, ‖∑ j : ZMod K₀,ZMod.stdAddChar (-(j*k))*
          GafniTao.fordAdditiveCharacter (∑ a,x ip.1 ip.2 a*
            (![(j.val+1:ℝ),(j.val+1:ℝ)^2,(j.val+1:ℝ)^((3:ℝ)/2),
              Real.sqrt (j.val+1:ℝ)] : Fin 4 → ℝ) a)‖)^12 ≤
          C*Vscale*(K₀:ℝ)^((12:ℝ)+εloss)*(3*Cap)^11*
            ∑ key∈V.image joint,((Fiber key).card:ℝ)^10*((Pairs key).card:ℝ)) ∧
      (∀ ij∈Pall, |(A ij 2:ℝ)| ≤ (Q:ℝ)^2/(6*(K₀:ℝ)^2*Vscale) ∧
        |(A ij 2:ℝ)| ≤ Rphys^4/(6*(N:ℝ)^2*Vscale)) := by
  classical
  obtain ⟨Dtype,hDtype,hsource⟩ :=
    double_difference_colored_fourier_cloud_type_one_and_triangular hc hU hL
  obtain ⟨C,hC,hcolored⟩ := huxley_completed_colored_source_sieve.{0} hεloss
  refine ⟨Dtype,C,hDtype,hC,?_⟩
  intro S F rshift sshift z r v Alen Z Q K₀ N instK d Wmax T M Jsep Nlen Vscale Rphys
    hf hlower hbound hdet hnegative hd hw hwcap hsmall hT hM hN hQ
    hJsep hNM hJM hwJ hy hz hgeometry hsep hshifts Φ f hlevel hden hinv
    μ₀ U₀ q μ hVscale hmesh hminor hcomplete
    ℓ b τ K x V w radius P h D δ lambda Hcurv q₀ p₀ color Cap
    offset joint narrowRadius Fiber Pairs Pall
  obtain ⟨hcard,hholder,A,hA,hclass,hTypeI,htri⟩ :=
    hsource S F rshift sshift z r v Alen Z Q K₀ N d Wmax T M Jsep
      hf hlower hbound hdet hnegative hd hw hwcap hsmall hT hM hN hQ
      hJsep hNM hJM hwJ hy hz hgeometry hsep hshifts hlevel hden hinv
  have hoffset : ((V.image offset).card:ℝ) ≤ 3 := by
    exact_mod_cast (fourier_parity_round_partition S (fun i => (q i:ℝ)*ℓ i)).2.1
  have hjointSub : V.image joint ⊆ (S.image color) ×ˢ (V.image offset) := by
    intro key hkey
    obtain ⟨ip,hip,rfl⟩ := Finset.mem_image.mp hkey
    exact Finset.mem_product.mpr
      ⟨Finset.mem_image_of_mem color (Finset.mem_product.mp hip).1,
        Finset.mem_image_of_mem offset hip⟩
  have hjoint : ((V.image joint).card:ℝ) ≤ 3*Cap := by
    have hh : ((V.image joint).card:ℝ) ≤
        ((S.image color).card:ℝ)*((V.image offset).card:ℝ) := by
      exact_mod_cast (Finset.card_le_card hjointSub).trans_eq (Finset.card_product _ _)
    have hcap : 0 ≤ Cap := (Nat.cast_nonneg _).trans hcard
    exact hh.trans ((mul_le_mul hcard hoffset (Nat.cast_nonneg _) hcap).trans_eq (mul_comm _ _))
  have hbox ip (hip : ip∈V) :
      |x ip.1 ip.2 2| ≤ Real.sqrt K₀ ∧ |x ip.1 ip.2 3| ≤ Real.sqrt K₀ := by
    have hi := (Finset.mem_product.mp hip).1
    have hqr : (0:ℝ) < q ip.1 := Nat.cast_pos.mpr (r ip.1).pos
    have hnr : (0:ℝ) < Nlen ip.1 := by exact_mod_cast (hminor ip.1 hi).1
    have hμ : 0 < μ ip.1 :=
      (mul_pos_iff_of_pos_right (sq_pos_of_pos hqr)).mp
        ((mul_pos_iff_of_pos_right hnr).mp (zero_lt_one.trans_le (hminor ip.1 hi).2.2))
    exact huxley_actual_dual_source_box (r ip.1).pos
      (hminor ip.1 hi).1 (hminor ip.1 hi).2.1 hμ (hminor ip.1 hi).2.2
      (hcomplete ip.1 hi) (v ip.1) ip.2
  have hKone : (1:ℝ) ≤ K₀ := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne K₀)
  have hNphys : (0:ℝ) < N := Nat.cast_pos.mpr hN
  have hrad : ∀ a, narrowRadius a ≤ radius a := by
    intro a
    fin_cases a
    · exact le_rfl
    · change 1/(12*(K₀:ℝ)^2*Vscale) ≤ 1/(12*(K₀:ℝ)^2)
      apply one_div_le_one_div_of_le (by positivity)
      exact le_mul_of_one_le_right (by positivity) hVscale
    · exact le_rfl
    · exact le_rfl
  have hsub : Pall ⊆ P := by
    intro ij hij
    have hh := Finset.mem_filter.mp hij
    exact Finset.mem_filter.mpr ⟨hh.1,fun a =>
      (hh.2 a).trans (mul_le_mul_of_nonneg_left (hrad a) (by norm_num))⟩
  refine ⟨hcard,hholder,A,hA,hclass,hTypeI,htri,hjoint,?_,?_⟩
  · intro k
    exact hcolored K₀ Vscale hVscale ((ℝ × ℤ) × Fin 2) V
      (fun ip => x ip.1 ip.2) joint (3*Cap) hbox hjoint k
  · intro ij hij
    have hp := Finset.mem_filter.mp hij
    have hi := (Finset.mem_product.mp (Finset.mem_product.mp hp.1).1).1
    have hj := (Finset.mem_product.mp (Finset.mem_product.mp hp.1).2).1
    let pr : Fin 2 → ℚ := ![r ij.1.1,r ij.2.1]
    let qi : Fin 2 → ℤ := ![(q ij.1.1:ℤ),(q ij.2.1:ℤ)]
    let ei : Fin 2 → ℤ := ![(r ij.1.1).num,(r ij.2.1).num]
    let vi : Fin 2 → ℤ := ![v ij.1.1,v ij.2.1]
    have hcast a : (ei a:ℝ)/qi a=(pr a:ℝ) := by
      fin_cases a
      · change ((r ij.1.1).num:ℝ)/(r ij.1.1).den=(r ij.1.1:ℝ)
        exact (Rat.cast_def _).symm
      · change ((r ij.2.1).num:ℝ)/(r ij.2.1).den=(r ij.2.1:ℝ)
        exact (Rat.cast_def _).symm
    have hband : ∀ a, (qi a:ℝ) ≤ (Q:ℝ) ∧ (Q:ℝ) ≤ 2*(qi a:ℝ) := by
      intro a
      fin_cases a
      · change ((r ij.1.1).den:ℝ) ≤ Q ∧ (Q:ℝ) ≤ 2*((r ij.1.1).den:ℝ)
        exact ⟨by exact_mod_cast (hden _ hi).1,by exact_mod_cast (hden _ hi).2⟩
      · change ((r ij.2.1).den:ℝ) ≤ Q ∧ (Q:ℝ) ≤ 2*((r ij.2.1).den:ℝ)
        exact ⟨by exact_mod_cast (hden _ hj).1,by exact_mod_cast (hden _ hj).2⟩
    obtain ⟨hdetA,ht,_htlo,_hthi,hmap,hgamma,_hrest⟩ := hA ij (hsub hij)
    have ht' : (A ij 2:ℝ)*((ei 0:ℝ)/qi 0)+A ij 3=(qi 1:ℝ)/qi 0 := by
      rw [hcast]
      change (A ij 2:ℝ)*(iteratedDeriv 2 (f ij.1.1) (z ij.1.1)/2)+A ij 3=
        (q ij.2.1:ℝ)/q ij.1.1 at ht
      rw [hlevel _ hi] at ht
      exact ht
    have hmap' : ((A ij 0:ℝ)*((ei 0:ℝ)/qi 0)+A ij 1)/
        ((A ij 2:ℝ)*((ei 0:ℝ)/qi 0)+A ij 3)=(ei 1:ℝ)/qi 1 := by
      rw [hcast,hcast]
      change ((A ij 0:ℝ)*(iteratedDeriv 2 (f ij.1.1) (z ij.1.1)/2)+A ij 1)/
        ((A ij 2:ℝ)*(iteratedDeriv 2 (f ij.1.1) (z ij.1.1)/2)+A ij 3)=
          iteratedDeriv 2 (f ij.2.1) (z ij.2.1)/2 at hmap
      rw [hlevel _ hi,hlevel _ hj] at hmap
      exact hmap
    have hnear : |Int.fract (-(vi 0:ℝ)/qi 0)-Int.fract (-(vi 1:ℝ)/qi 1)| ≤
        1/(6*(K₀:ℝ)^2*Vscale) := by
      have hn := hp.2 (1:Fin 4)
      change |Int.fract (-(vi 0:ℝ)/qi 0)-Int.fract (-(vi 1:ℝ)/qi 1)| ≤
        2*(1/(12*(K₀:ℝ)^2*Vscale)) at hn
      convert hn using 1
      field_simp
      norm_num
    exact fourier_matrix_narrowed_coordinate_entry_bound qi ei vi (A ij)
      (by
        intro a
        fin_cases a
        · change (0:ℤ) < (r ij.1.1).den
          exact_mod_cast (r ij.1.1).pos
        · change (0:ℤ) < (r ij.2.1).den
          exact_mod_cast (r ij.2.1).pos)
      hKone hVscale hNphys hmesh hband
      (by intro a; fin_cases a; exact hinv _ hi; exact hinv _ hj)
      hdetA ht' hmap' hgamma hnear

example
    {c U L εloss : ℝ} (hc : 0 < c) (hU : 0 < U) (hL : 0 ≤ L) (hεloss : 0 < εloss) :
    ∃ Dtype C : ℝ, 0 < Dtype ∧ 0 < C ∧
    ∀ (S : Finset (ℝ × ℤ)) (F rshift sshift : ℝ → ℝ)
      (z : (ℝ × ℤ) → ℝ) (r : (ℝ × ℤ) → ℚ) (v : (ℝ × ℤ) → ℤ)
      (Alen : (ℝ × ℤ) → ℕ) (Z : ℝ → ℤ)
      (Q K₀ N : ℕ) [NeZero K₀] (d Wmax T M Jsep : ℝ)
      (Nlen : (ℝ × ℤ) → ℕ) (Vscale Rphys : ℝ),
    (∀ u, 0 < u → ContDiffAt ℝ ∞ F u) →
    (∀ u∈Icc (1/2:ℝ) 3, c ≤ iteratedDeriv 5 F u) →
    (∀ u∈Icc (1/2:ℝ) 3, ∀ n, 1 ≤ n → n ≤ 7 → |iteratedDeriv n F u| ≤ U) →
    (∀ u∈Icc (1/2:ℝ) 3,
      c ≤ |(iteratedDeriv 5 F u)^2-iteratedDeriv 4 F u*iteratedDeriv 6 F u|) →
    (∀ u∈Icc (1/2:ℝ) 3, iteratedDeriv 4 F u ≤ -c) →
    0 < d → 0 ≤ Wmax → Wmax ≤ 1/4 → 2*U*Wmax ≤ c/64 →
    0 < T → 2 ≤ M → 0 < N → 0 < Q →
    0 < Jsep → (N:ℝ) ≤ M → Jsep ≤ M → Wmax*Jsep ≤ 1 →
    (∀ i∈S, i.1∈Icc (1:ℝ) 2) →
    (∀ i∈S, z i∈Icc M (2*M)) →
    (∀ i∈S, N ≤ Alen i ∧ Alen i ≤ 3*N ∧
      round (z i)+(Alen i:ℤ)=Z i.1+(N:ℤ)*i.2+2*(N:ℤ)) →
    (∀ i∈S, ∀ j∈S, i.1≠j.1 → 1 ≤ Jsep*|i.1-j.1|) →
    (∀ y∈S.image Prod.fst,
      0 ≤ rshift y ∧ 0 ≤ sshift y ∧ rshift y*sshift y=d*y ∧ rshift y+sshift y ≤ Wmax) →
    let Φ := fun y u =>
      (F u-F (u+rshift y)-F (u+sshift y)+F (u+rshift y+sshift y))/d
    let f := fun i : ℝ × ℤ => fun u => T*Φ i.1 (u/M)
    (∀ i∈S, iteratedDeriv 2 (f i) (z i)/2=(r i:ℝ)) →
    (∀ i∈S, (r i).den ≤ Q ∧ Q ≤ 2*(r i).den) →
    (∀ i∈S, ((r i).den:ℤ) ∣ (r i).num*v i-1) →
    let μ₀ := c*T/(12*M^3)
    let U₀ := U*T/(2*M^3)
    let q := fun i => (r i).den
    let μ := fun i => iteratedDeriv 3 (f i) (round (z i))/6
    1 ≤ Vscale → (Q:ℝ)*(N:ℝ) ≤ (K₀:ℝ)*Rphys^2 →
    (∀ i∈S, 1 ≤ Nlen i ∧ q i ≤ Nlen i ∧ 1 ≤ μ i*(q i:ℝ)^2*Nlen i) →
    (∀ i∈S, 7*(μ i*(q i:ℝ)*(Nlen i:ℝ)^2) ≤ K₀) →
    let ℓ := fun i => deriv (f i) (round (z i))
    let b := fun i (p : Fin 2) => (⌊(q i:ℝ)*ℓ i⌋+(p:ℕ) : ℤ)
    let τ := fun i p => ((b i p:ℝ)-(q i:ℝ)*ℓ i)/2
    let K := fun i => -2*μ i*(Real.sqrt (2/(3*μ i*(q i:ℝ))))^3
    let x := fun i p =>
      (![-(v i:ℝ)*b i p/q i,-(v i:ℝ)/q i,K i,3*K i*τ i p/2] : Fin 4 → ℝ)
    let V := S ×ˢ (Finset.univ : Finset (Fin 2))
    let w := fun ip : (ℝ × ℤ) × Fin 2 =>
      (![Int.fract (x ip.1 ip.2 0),Int.fract (x ip.1 ip.2 1),
        x ip.1 ip.2 2/Real.sqrt K₀,x ip.1 ip.2 3/Real.sqrt K₀] : Fin 4 → ℝ)
    let radius : Fin 4 → ℝ :=
      ![1/(12*(K₀:ℝ)),1/(12*(K₀:ℝ)^2),(1/(K₀:ℝ)^2)/12,(1/(K₀:ℝ))/12]
    let P := (V ×ˢ V).filter (fun ij => ∀ d, |w ij.1 d-w ij.2 d| ≤ 2*radius d)
    let h := fun i => iteratedDeriv 2 (f i) (z i)/2
    let D := (Real.sqrt K₀/(9*(K₀:ℝ))+Real.sqrt K₀/(12*(K₀:ℝ)^2))*
      Real.sqrt (U₀*(Q:ℝ)^3)
    let δ := 1/(8*(L+3))
    let lambda := c*T/(2*M^2)
    let Hcurv := U*T/M^2
    let q₀ := (Q:ℝ)/2
    let p₀ := lambda*(Q:ℝ)/2
    let color := fun i => (⌊((r i).den:ℝ)/(δ*q₀)⌋,⌊((r i).num:ℝ)/(δ*p₀)⌋)
    let Cap := (4/δ+3)*(8*U/(c*δ)+3)
    let offset := fun ip : (ℝ × ℤ) × Fin 2 => b ip.1 ip.2-round ((q ip.1:ℝ)*ℓ ip.1)
    let joint := fun ip : (ℝ × ℤ) × Fin 2 => (color ip.1,offset ip)
    let narrowRadius : Fin 4 → ℝ :=
      ![1/(12*(K₀:ℝ)),1/(12*(K₀:ℝ)^2*Vscale),(1/(K₀:ℝ)^2)/12,(1/(K₀:ℝ))/12]
    let Fiber := fun key => V.filter (fun ip => joint ip=key)
    let Pairs := fun key => ((Fiber key) ×ˢ (Fiber key)).filter
      (fun ij => ∀ a, |w ij.1 a-w ij.2 a| ≤ 2*narrowRadius a)
    let Pall := (V ×ˢ V).filter
      (fun ij => ∀ a, |w ij.1 a-w ij.2 a| ≤ 2*narrowRadius a)
    ((S.image color).card:ℝ) ≤ Cap ∧
    (∀ coeff : (ℝ × ℤ) → ℂ, ‖∑ i∈S,coeff i‖^12 ≤ Cap^11*
      ∑ j∈S.image color, ‖∑ i∈S.filter (fun i => color i=j),coeff i‖^12) ∧
    ∃ A : (((ℝ × ℤ) × Fin 2) × ((ℝ × ℤ) × Fin 2)) → Fin 4 → ℤ,
      (∀ ij∈P,
        A ij 0*A ij 3-A ij 1*A ij 2=1 ∧
        let t := (A ij 2:ℝ)*h ij.1.1+A ij 3
        t=(q ij.2.1:ℝ)/q ij.1.1 ∧ (1:ℝ)/2 ≤ t ∧ t ≤ 2 ∧
        ((A ij 0:ℝ)*h ij.1.1+A ij 1)/t=h ij.2.1 ∧
        |(A ij 2:ℝ)| ≤ (Q:ℝ)^2/(6*(K₀:ℝ)^2) ∧
        |μ ij.2.1/μ ij.1.1*t^3-1| ≤
          (16*U₀/μ₀)*Real.sqrt (U₀*(Q:ℝ)^3)*Real.sqrt K₀/(6*(K₀:ℝ)^2) ∧
        |τ ij.1.1 ij.1.2-τ ij.2.1 ij.2.2| ≤ D ∧
        (∃ e₁ e₂ : ℤ,
          let F₁ := 2*(round (z ij.2.1):ℝ)-2*(A ij 3:ℝ)*(round (z ij.1.1):ℝ)-
            (A ij 2:ℝ)*ℓ ij.1.1
          let F₂ := ℓ ij.2.1-2*(A ij 1:ℝ)*(round (z ij.1.1):ℝ)-
            (A ij 0:ℝ)*ℓ ij.1.1
          |F₁-e₁| ≤ (q ij.2.1:ℝ)/(6*(K₀:ℝ))+|(A ij 2:ℝ)|/q ij.1.1 ∧
          |(F₂-e₂)-h ij.2.1*(F₁-e₁)| ≤ 2*D/q ij.2.1) ∧
        ((Q:ℝ)^2/(6*(K₀:ℝ)^2) < 1 →
          A ij 2=0 ∧ q ij.1.1=q ij.2.1 ∧
            (q ij.1.1:ℤ) ∣ (r ij.2.1).num-(r ij.1.1).num)) ∧
      (∀ ij∈P, color ij.1.1=color ij.2.1 →
        let t := (A ij 2:ℝ)*h ij.1.1+A ij 3
        |t-1| ≤ δ ∧
        |((A ij 0:ℝ)*h ij.1.1+A ij 1)/h ij.1.1-1| ≤ δ ∧
        ((A ij 0=1 ∧ A ij 1=0 ∧ A ij 2=0 ∧ A ij 3=1) ∨
         (A ij 0=1 ∧ A ij 3=1 ∧ A ij 2=0 ∧ A ij 1≠0 ∧ |(A ij 1:ℝ)| ≤ δ*Hcurv) ∨
         (A ij 0=1 ∧ A ij 3=1 ∧ A ij 1=0 ∧ A ij 2≠0 ∧ |(A ij 2:ℝ)| ≤ δ/lambda) ∨
         (A ij 1≠0 ∧ A ij 2≠0)) ∧
        (|(A ij 2:ℝ)| * Hcurv ≤ L →
          A ij 0+A ij 3=2 ∧ (A ij 0-1)^2= -A ij 1*A ij 2)) ∧
      let E := P.filter (fun ij =>
        color ij.1.1=color ij.2.1 ∧
        ((A ij 0=1 ∧ A ij 1=0 ∧ A ij 2=0 ∧ A ij 3=1) ∨
         (A ij 1≠0 ∧ A ij 2≠0 ∧ |(A ij 2:ℝ)| * Hcurv ≤ L)))
      let Δ := (16*U₀/μ₀)*Real.sqrt (U₀*(Q:ℝ)^3)*Real.sqrt K₀/(6*(K₀:ℝ)^2)
      (E.card:ℝ) ≤ Dtype*((S.image Prod.fst).card:ℝ)*(M/(N:ℝ))*(1+Δ*Jsep) ∧
      let Etri := P.filter (fun ij =>
        color ij.1.1=color ij.2.1 ∧ (A ij 2=0 ∨ A ij 1=0))
      (Etri.card:ℝ) ≤ Dtype*(1+δ*(Hcurv+1/lambda))*
        ((S.image Prod.fst).card:ℝ)*(M/(N:ℝ))*(1+Δ*Jsep) ∧
      ((V.image joint).card:ℝ) ≤ 3*Cap ∧
      (∀ k : ZMod K₀,
        (∑ ip∈V, ‖∑ j : ZMod K₀,ZMod.stdAddChar (-(j*k))*
          GafniTao.fordAdditiveCharacter (∑ a,x ip.1 ip.2 a*
            (![(j.val+1:ℝ),(j.val+1:ℝ)^2,(j.val+1:ℝ)^((3:ℝ)/2),
              Real.sqrt (j.val+1:ℝ)] : Fin 4 → ℝ) a)‖)^12 ≤
          C*Vscale*(K₀:ℝ)^((12:ℝ)+εloss)*(3*Cap)^11*
            ∑ key∈V.image joint,((Fiber key).card:ℝ)^10*((Pairs key).card:ℝ)) ∧
      (∀ ij∈Pall, |(A ij 2:ℝ)| ≤ (Q:ℝ)^2/(6*(K₀:ℝ)^2*Vscale) ∧
        |(A ij 2:ℝ)| ≤ Rphys^4/(6*(N:ℝ)^2*Vscale)) := by
  exact double_difference_actual_joint_narrowed_sieve hc hU hL hεloss

#print axioms double_difference_actual_joint_narrowed_sieve


private theorem model_source_large_entry_main_coefficient_nonneg {σ δ : ℝ} (hσ : 0 < σ) (hδ₀ : 0 ≤ δ) :
    let κ := modelPhaseThirdLower σ
    let Cphys := σ*(σ+1)+1
    let c := κ/6
    let J := Cphys/6
    let B := max 1 (max (2*Real.sqrt J) (8*J*Real.sqrt J/(3*c)))
    let C₂ := modelPhaseJetCoefficient σ 2+δ
    let C₃ := modelPhaseJetCoefficient σ 3+δ
    let Ct := C₂/2+5*C₃/12
    let Cc := C₂/κ+C₃/(2*κ)
    let Kres := 4*(37*B/2+16*B*Cc+2*Ct+2*Cc+
      2*quarticNonlinearResidualConstant σ δ)/κ
    let Lunit := 2*κ/Cphys
    let Gamma := Cphys/κ
    let Cthird := Gamma*(32*Kres+9*quarticReciprocalConstant σ δ)
    let Cfirst := 128*Cphys*(Gamma^2*Cthird+Gamma*(modelPhaseJetCoefficient σ 3+δ)/κ)/κ^2
    let Cmain := 4*(2*Cfirst/Lunit^3)^((3:ℝ)⁻¹)+2
    0 ≤ Cmain := by
  intro κ Cphys c J B C₂ C₃ Ct Cc Kres Lunit Gamma Cthird Cfirst Cmain
  have hκ : 0 < κ := modelPhaseThirdLower_pos hσ
  have hCphys : 0 < Cphys := by dsimp only [Cphys]; positivity
  have hC₂ : 0 ≤ C₂ := add_nonneg (modelPhaseJetCoefficient_nonneg σ 2) hδ₀
  have hC₃ : 0 ≤ C₃ := add_nonneg (modelPhaseJetCoefficient_nonneg σ 3) hδ₀
  have hC₄ : 0 ≤ modelPhaseJetCoefficient σ 4+δ :=
    add_nonneg (modelPhaseJetCoefficient_nonneg σ 4) hδ₀
  have hRes : 0 ≤ quarticNonlinearResidualConstant σ δ := by
    dsimp only [quarticNonlinearResidualConstant]
    positivity
  have hRecip : 0 ≤ quarticReciprocalConstant σ δ := by
    dsimp only [quarticReciprocalConstant]
    positivity
  have hB : 0 ≤ B := zero_le_one.trans (le_max_left _ _)
  have hCt : 0 ≤ Ct := by dsimp only [Ct]; positivity
  have hCc : 0 ≤ Cc := by dsimp only [Cc]; positivity
  have hKres : 0 ≤ Kres := by dsimp only [Kres]; positivity
  have hLunit : 0 < Lunit := by dsimp only [Lunit]; positivity
  have hGamma : 0 ≤ Gamma := by dsimp only [Gamma]; positivity
  have hCthird : 0 ≤ Cthird := by dsimp only [Cthird]; positivity
  have hCfirst : 0 ≤ Cfirst := by dsimp only [Cfirst]; positivity
  have hCmain : 0 ≤ Cmain := by dsimp only [Cmain]; positivity
  exact hCmain

example {σ δ : ℝ} (hσ : 0 < σ) (hδ₀ : 0 ≤ δ) :
    let κ := modelPhaseThirdLower σ
    let Cphys := σ*(σ+1)+1
    let c := κ/6
    let J := Cphys/6
    let B := max 1 (max (2*Real.sqrt J) (8*J*Real.sqrt J/(3*c)))
    let C₂ := modelPhaseJetCoefficient σ 2+δ
    let C₃ := modelPhaseJetCoefficient σ 3+δ
    let Ct := C₂/2+5*C₃/12
    let Cc := C₂/κ+C₃/(2*κ)
    let Kres := 4*(37*B/2+16*B*Cc+2*Ct+2*Cc+
      2*quarticNonlinearResidualConstant σ δ)/κ
    let Lunit := 2*κ/Cphys
    let Gamma := Cphys/κ
    let Cthird := Gamma*(32*Kres+9*quarticReciprocalConstant σ δ)
    let Cfirst := 128*Cphys*(Gamma^2*Cthird+Gamma*(modelPhaseJetCoefficient σ 3+δ)/κ)/κ^2
    let Cmain := 4*(2*Cfirst/Lunit^3)^((3:ℝ)⁻¹)+2
    0 ≤ Cmain := by
  exact model_source_large_entry_main_coefficient_nonneg hσ hδ₀

#print axioms model_source_large_entry_main_coefficient_nonneg


private theorem eventually_model_global_large_entry_source_mass_clamped
    {σ Jref εloss : ℝ} (hσ : 0 < σ) (hJref : 0 ≤ Jref) (hεloss : 0 < εloss) :
    ∀ᶠ T : ℝ in Filter.atTop, ∀ (F : Fin 2 → ℝ → ℝ)
    (Uref : ℕ) (Refs : Finset ℝ) (Gaps : Finset (ℝ × ℝ)) {Bselect : ℝ}
    (P : Finset ((ℤ × Fin 2) × (ℤ × Fin 2))) (Mat : ((ℤ × Fin 2) × (ℤ × Fin 2)) → Fin 4 → ℤ)
    (gap : ((ℤ × Fin 2) × (ℤ × Fin 2)) → ℝ × ℝ)
    (Q K₀ : ℕ) [NeZero K₀]
    (N : ℕ) (za zb : ℤ → ℝ) (AlenA AlenB : ℤ → ℕ) (Za Zb : ℤ)
    (rat : ((ℤ × Fin 2) × (ℤ × Fin 2)) → Fin 2 → ℚ)
    (vinv : ((ℤ × Fin 2) × (ℤ × Fin 2)) → Fin 2 → ℤ)
    (parity : ((ℤ × Fin 2) × (ℤ × Fin 2)) → Fin 2 → Fin 2)
    (anchor : ((ℤ × Fin 2) × (ℤ × Fin 2)) → ℚ)
    (e r v s : ℝ × ℝ → ℤ)
    {δ M R base Bcut lambda Uband θ : ℝ}
    (A : Fin 2 → ℤ) {W : Fin 2 → ℝ},
    let V := max 1 (Uband*(N:ℝ)/(Q:ℝ))
    let x := fun ij : (ℤ × Fin 2) × (ℤ × Fin 2) => (![za ij.1.1,zb ij.2.1] : Fin 2 → ℝ)
    let xlocal := fun ij i => x ij i-(A i:ℝ)
    (∀ ij∈P, base ≤ za ij.1.1-(A 0:ℝ)) →
    (∀ ij∈P, gap ij∈Gaps) →
    (∀ ij∈P, N ≤ AlenA ij.1.1 ∧ AlenA ij.1.1 ≤ 3*N ∧
      round (za ij.1.1)+(AlenA ij.1.1:ℤ)=Za+(N:ℤ)*ij.1.1+2*(N:ℤ)) →
    (∀ ij∈P, N ≤ AlenB ij.2.1 ∧ AlenB ij.2.1 ≤ 3*N ∧
      round (zb ij.2.1)+(AlenB ij.2.1:ℤ)=Zb+(N:ℤ)*ij.2.1+2*(N:ℤ)) →
    (δ ≤ min (modelPhaseThirdLower σ) 1) →
    (∀ i, Expdb.IsApproximateModelPhaseFunction (F i) σ 4 δ) →
    (0 < T) →
    (0 < M) →
    (0 < (N:ℝ)) →
    (1 ≤ R) →
    (R ≤ M) →
    (0 < Q) →
    (T*(N:ℝ)*R^2=M^3) →
    ((Q:ℝ)*(N:ℝ) ≤ (K₀:ℝ)*R^2) →
    (∀ i, M ≤ (A i:ℝ)) →
    (∀ i, (A i:ℝ)+W i ≤ 2*M) →
    (∀ ij∈P, ∀ i, xlocal ij i∈Ioo (1/2:ℝ) (W i-1/2)) →
    (∀ ij∈P, ∀ i, (rat ij i).den ≤ Q ∧ Q ≤ 2*(rat ij i).den) →
    (0 < lambda) →
    (0 < Uband) → (Uband ≤ 1) →
    (0 < θ) →
    (θ ≤ 1/24) →
    (∀ ij∈P, ∀ i, lambda ≤ |(rat ij i:ℝ)| ∧ |(rat ij i:ℝ)| ≤ Uband) →
    (∀ ij∈P, ∀ i, ((rat ij i).den:ℤ) ∣ (rat ij i).num*vinv ij i-1) →
    (∀ ab∈Gaps, (v ab)*(r ab)-(e ab)*(s ab)=1) →
    (∀ ab∈Gaps, ((0:ℝ) < (r ab) ∧ ((e ab):ℝ)/(r ab)=ab.1) ∨
      (((r ab):ℝ) < 0 ∧ ((e ab):ℝ)/(r ab)=ab.2)) →
    (0 < Bcut) →
    (∀ ab∈Gaps, (s ab) ≠ 0) →
    (∀ ab∈Gaps, ((e ab):ℝ)/(r ab)∈Refs) →
    (∀ ab∈Gaps, ((v ab):ℝ)/(s ab)∈Refs) →
    (∀ a∈Refs, ∀ b∈Refs, a ≠ b → ((Uref:ℝ)/R^2)/4 < |a-b|) →
    (∀ ij∈P, ∀ i, xlocal ij i-(56*(Uref:ℝ)/modelPhaseThirdLower σ)*(N:ℝ)∈Ioo (1/2:ℝ) (W i-1/2)) →
    (∀ ij∈P, ∀ i, xlocal ij i+(56*(Uref:ℝ)/modelPhaseThirdLower σ)*(N:ℝ)∈Ioo (1/2:ℝ) (W i-1/2)) →
    (1 ≤ Uref) →
    (2+168/modelPhaseThirdLower σ ≤ Bselect) →
    (7*Bcut ≤ modelPhaseThirdLower σ*Bselect) →
    (Bselect^2*(Uref:ℝ)^3*R^2 ≤ (N:ℝ)^2) →
    (∀ ab∈Gaps, R^2 ≤ ((r ab):ℝ)^2*(Uref:ℝ)) →
    (∀ ab∈Gaps, ab.2-ab.1 ≤ 7*(Uref:ℝ)/(2*R^2)) →
    (R ≤ (Q:ℝ)) →
    ((Uref:ℝ) ≤ ((N:ℝ)/(Q:ℝ))^((2:ℝ)/3)/Bselect) →
    ((N:ℝ)^10 ≤ M^3*R^7) →
    (∀ ij∈P, (rat ij 0:ℝ)∈Icc (gap ij).1 (gap ij).2) →
    (∀ ij∈P, Mat ij 2 ≠ 0) →
    (∀ ij∈P, 64*(modelPhaseJetCoefficient σ 3+δ)*M^2 ≤
      |(Mat ij 2:ℝ)| *(modelPhaseThirdLower σ)^2*T) →
    (∀ ij∈P, 8*Uband ≤ |(Mat ij 2:ℝ)| *lambda^2) →
    (∀ ab∈Gaps, ab.1∈Refs ∧ ab.2∈Refs ∧ ab.1 < ab.2 ∧
      ∀ t∈Refs, ¬(ab.1 < t ∧ t < ab.2)) →
    (Q:ℝ) ≤ (N:ℝ) →
    ((N:ℝ)^2 ≤ M ∨ (1 ≤ M ∧ (N:ℝ) ≤ T ∧ R^2 ≤ T)) → (Uref:ℝ) ≤ R^2 →
    (∀ ab∈Gaps, |((r ab):ℝ)| ≤ 4*R^2/(Uref:ℝ)) →
    (∀ ab∈Gaps, |((s ab):ℝ)| ≤ 4*R^2/(Uref:ℝ)) →
    (∀ ab∈Gaps, |((e ab):ℝ)| ≤
      (3*Jref*T/(2*σ*M^2)+1)*(4*R^2/(Uref:ℝ))) →
    (∀ ab∈Gaps, |((v ab):ℝ)| ≤
      (3*Jref*T/(2*σ*M^2)+1)*(4*R^2/(Uref:ℝ))) →
    let ε := modelPhaseThirdLower σ/(16*(σ*(σ+1)+1+2)*R^2)
    let sourceColor := fun ij i => (⌊((rat ij i).den:ℝ)/(θ*((Q:ℝ)/2))⌋,
      ⌊((rat ij i).num:ℝ)/(θ*(lambda*(Q:ℝ)/2))⌋)
    (∀ ij∈P, sourceColor ij 0=sourceColor ij 1) →
    let f := fun (i : Fin 2) w => T*F i (w/M)
    (∀ ij∈P, ∀ i, iteratedDeriv 2 (f i) (x ij i)/2=(rat ij i:ℝ)) →
    let q := fun ij i => (rat ij i).den
    let mu := fun ij i => iteratedDeriv 3 (f i) (round (x ij i))/6
    let ell := fun ij i => deriv (f i) (round (x ij i))
    let b := fun ij i => (⌊(q ij i:ℝ)*ell ij i⌋+(parity ij i:ℕ) : ℤ)
    let cround := fun ij i => round ((q ij i:ℝ)*ell ij i)
    let tau := fun ij i => ((b ij i:ℝ)-(q ij i:ℝ)*ell ij i)/2
    let dual := fun ij i => -2*mu ij i*(Real.sqrt (2/(3*mu ij i*(q ij i:ℝ))))^3
    let cloud := fun ij i => (![Int.fract (-(vinv ij i:ℝ)*b ij i/q ij i),
      Int.fract (-(vinv ij i:ℝ)/q ij i),dual ij i/Real.sqrt K₀,
      (3*dual ij i*tau ij i/2)/Real.sqrt K₀] : Fin 4 → ℝ)
    let radius : Fin 4 → ℝ := ![1/(12*(K₀:ℝ)),1/(12*(K₀:ℝ)^2),(1/(K₀:ℝ)^2)/12,(1/(K₀:ℝ))/12]
    (∀ ij∈P, b ij 0-cround ij 0=b ij 1-cround ij 1) →
    (∀ ij∈P, ∀ a, |cloud ij 0 a-cloud ij 1 a| ≤ 2*radius a) →
    (∀ ij∈P,
      |cloud ij 0 1-cloud ij 1 1| ≤ 1/(6*(K₀:ℝ)^2*V)) →
    let κ := modelPhaseThirdLower σ
    let Cphys := σ*(σ+1)+1
    let c := κ/6
    let J := Cphys/6
    let B := max 1 (max (2*Real.sqrt J) (8*J*Real.sqrt J/(3*c)))
    B*R^2/(N:ℝ)^2 ≤ 1/2 →
    (N:ℝ) ≤ R^2 →
    R ≤ (N:ℝ) →
    (N:ℝ)^3 ≤ M*R^2 →
    2*R^2 ≤ (Q:ℝ)*(N:ℝ) →
    (∀ ij∈P, Mat ij 0*Mat ij 3-Mat ij 1*Mat ij 2=1) →
    (∀ ij∈P, (Mat ij 2:ℝ)*(rat ij 0:ℝ)+Mat ij 3=(q ij 1:ℝ)/q ij 0) →
    (∀ ij∈P, ((Mat ij 0:ℝ)*(rat ij 0:ℝ)+Mat ij 1)/
      ((Mat ij 2:ℝ)*(rat ij 0:ℝ)+Mat ij 3)=(rat ij 1:ℝ)) →
    (∀ ij∈P, |(Mat ij 2:ℝ)| ≤ (Q:ℝ)^2/(6*(K₀:ℝ)^2)) →
    let H := (N:ℝ)/(Cphys+2)
    2 ≤ (N:ℝ) →
    (∀ ij∈P, ∀ i, xlocal ij i-H∈Ioo (1/2:ℝ) (W i-1/2)) →
    (∀ ij∈P, ∀ i, xlocal ij i+H∈Ioo (1/2:ℝ) (W i-1/2)) →
    (∀ ij∈P, |(anchor ij:ℝ)-(rat ij 0:ℝ)| ≤ ε) →
    (∀ ij∈P, 256*((anchor ij).den:ℝ) ≤ (Q:ℝ)/3) →
    (∀ ij∈P, 256 ≤ (2*ε)*((Q:ℝ)/3)*(anchor ij).den) →
    let C₂ := modelPhaseJetCoefficient σ 2+δ
    let C₃ := modelPhaseJetCoefficient σ 3+δ
    let Ct := C₂/2+5*C₃/12
    let Cc := C₂/κ+C₃/(2*κ)
    let Δ := (37*B/2+16*B*Cc+2*Ct+2*Cc)*(Q:ℝ)/(N:ℝ)
    let Ccurv := (4/κ)*(B+2*quarticReciprocalConstant σ δ)
    let D := Δ+quarticNonlinearResidualConstant σ δ*(2*(Q:ℝ))/(N:ℝ)
    let Kres := 4*(37*B/2+16*B*Cc+2*Ct+2*Cc+
      2*quarticNonlinearResidualConstant σ δ)/κ
    let Esize := κ/(16*(Cphys+2))
    let Dbase := 37*B/2+16*B*Cc+2*Ct+2*Cc+2*quarticNonlinearResidualConstant σ δ
    let Tbase := (2/κ)*(B+2*quarticReciprocalConstant σ δ)
    2*3840*128^2*105*(Dbase+64*Tbase*Esize^2) ≤ Bselect*Esize →
    D ≤ 1/2 → Δ < 1/2 → 61*Ccurv*Cphys ≤ Bcut →
    let Lunit := 2*κ/Cphys
    let Gamma := Cphys/κ
    let Cthird := Gamma*(32*Kres+9*quarticReciprocalConstant σ δ)
    let Cpack := 64*Cphys*(Gamma^2*Cthird+Gamma*(modelPhaseJetCoefficient σ 3+δ)/κ)/κ
    let Cfirst := 128*Cphys*(Gamma^2*Cthird+Gamma*(modelPhaseJetCoefficient σ 3+δ)/κ)/κ^2
    let Cgap := 64*Cphys*(Gamma^2*B+Gamma*(modelPhaseJetCoefficient σ 3+δ)/κ)/κ
    let Cmain := 4*(2*Cfirst/Lunit^3)^((3:ℝ)⁻¹)+2
    let Ctail := 4*Cpack/Lunit^2+Cgap
    V*(P.card:ℝ) ≤
      (60*588*(Uband/lambda)^2*Uband^2*(R^8/(N:ℝ)^4)*
        (Cmain*((Q:ℝ)/(Uband*(N:ℝ)))^((2:ℝ)/3)+Ctail/(Uref:ℝ)))*T^εloss := by
  filter_upwards [eventually_model_global_large_entry_source_mass_raw hσ hJref hεloss]
    with T hraw
  intro F Uref Refs Gaps Bselect P Mat gap Q K₀ inst N za zb AlenA AlenB Za Zb
    rat vinv parity anchor e r v s δ M R base Bcut lambda Uband θ A W V x xlocal
    hbase hgapMem hgeometryA hgeometryB hδ hF hT hM hN hR hRM hQ hscale hmesh hA hW hx hden hlambda hUband hUbandCap hθ hθmax hcurv hinv hchart horientation hBcut hs hrefSet hparentSet hsep hwideL hwideU hUref hBselectSize hcutMargin hselectedWrap hreferenceDen hgapWidth hRQ hselectedUpper hscaleTen hfamilyGap hc hlarge haction hgap
    hQN hNM hUR hrHeight hsHeight heHeight hvHeight
    ε sourceColor hsourceColor f hlevel q mu ell b cround tau dual cloud radius
    hcolor hnear hnearNarrow κ Cphys c J B hsmall hNR hRN hNcube hminscale
    hMatdet hMatt hMatmap hMatgamma H hNtwo hL hU hanchor hcut hcount
    C₂ C₃ Ct Cc Δ Ccurv D Kres Esize Dbase Tbase hsize hD hΔ hBsize
    Lunit Gamma Cthird Cpack Cfirst Cgap Cmain Ctail
  have hV : 1 ≤ V := le_max_left _ _
  have hmass := hraw F Uref Refs Gaps (Bselect:=Bselect) P Mat gap Q K₀ N
    za zb AlenA AlenB Za Zb rat vinv parity anchor e r v s
    (δ:=δ) (M:=M) (R:=R) (base:=base) (Bcut:=Bcut)
    (lambda:=lambda) (Uband:=Uband) (θ:=θ) (V:=V) A (W:=W)
    hbase hgapMem hgeometryA hgeometryB hδ hF hT hM hN hR hRM hQ hscale hmesh
    hA hW hx hden hlambda hUband.le hθ hθmax hcurv hinv hchart horientation hBcut hs
    hrefSet hparentSet hsep hwideL hwideU hUref hBselectSize hcutMargin hselectedWrap
    hreferenceDen hgapWidth hRQ hselectedUpper hscaleTen hfamilyGap hc hlarge haction hV hgap
    hQN hNM hUR hrHeight hsHeight heHeight hvHeight hsourceColor hlevel hcolor hnear
    hnearNarrow hsmall hNR hRN hNcube hminscale hMatdet hMatt hMatmap hMatgamma
    hNtwo hL hU hanchor hcut hcount hsize hD hΔ hBsize
  have hδ₀ := approximateModelPhase_tolerance_nonneg (hF 0)
  have hCmain : 0 ≤ Cmain := model_source_large_entry_main_coefficient_nonneg hσ hδ₀
  have hUp : (0:ℝ) < Uref := Nat.cast_pos.mpr (by omega)
  have hclamp := (clamped_narrowing_source_costs
    (H:=Uband) (N:=(N:ℝ)) (Q:=(Q:ℝ)) (C:=0) (a:=Cmain) (b:=Ctail) (Uref:=(Uref:ℝ))
    hUband hUbandCap hN (Nat.cast_pos.mpr hQ) (by norm_num) hCmain hUp).2.2
  let Kbase := 60*588*(Uband/lambda)^2*Uband^2*(R^8/(N:ℝ)^4)
  have hKbase : 0 ≤ Kbase := by dsimp only [Kbase]; positivity
  have hbound : V*(P.card:ℝ) ≤
      Kbase*(V*(Cmain/V^((5:ℝ)/3)+Ctail/((Uref:ℝ)*V)))*T^εloss := by
    have hh := mul_le_mul_of_nonneg_left hmass (zero_le_one.trans hV)
    convert hh using 1
    dsimp only [Kbase]
    ring
  exact hbound.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hclamp hKbase) (Real.rpow_nonneg hT.le _))

example
    {σ Jref εloss : ℝ} (hσ : 0 < σ) (hJref : 0 ≤ Jref) (hεloss : 0 < εloss) :
    ∀ᶠ T : ℝ in Filter.atTop, ∀ (F : Fin 2 → ℝ → ℝ)
    (Uref : ℕ) (Refs : Finset ℝ) (Gaps : Finset (ℝ × ℝ)) {Bselect : ℝ}
    (P : Finset ((ℤ × Fin 2) × (ℤ × Fin 2))) (Mat : ((ℤ × Fin 2) × (ℤ × Fin 2)) → Fin 4 → ℤ)
    (gap : ((ℤ × Fin 2) × (ℤ × Fin 2)) → ℝ × ℝ)
    (Q K₀ : ℕ) [NeZero K₀]
    (N : ℕ) (za zb : ℤ → ℝ) (AlenA AlenB : ℤ → ℕ) (Za Zb : ℤ)
    (rat : ((ℤ × Fin 2) × (ℤ × Fin 2)) → Fin 2 → ℚ)
    (vinv : ((ℤ × Fin 2) × (ℤ × Fin 2)) → Fin 2 → ℤ)
    (parity : ((ℤ × Fin 2) × (ℤ × Fin 2)) → Fin 2 → Fin 2)
    (anchor : ((ℤ × Fin 2) × (ℤ × Fin 2)) → ℚ)
    (e r v s : ℝ × ℝ → ℤ)
    {δ M R base Bcut lambda Uband θ : ℝ}
    (A : Fin 2 → ℤ) {W : Fin 2 → ℝ},
    let V := max 1 (Uband*(N:ℝ)/(Q:ℝ))
    let x := fun ij : (ℤ × Fin 2) × (ℤ × Fin 2) => (![za ij.1.1,zb ij.2.1] : Fin 2 → ℝ)
    let xlocal := fun ij i => x ij i-(A i:ℝ)
    (∀ ij∈P, base ≤ za ij.1.1-(A 0:ℝ)) →
    (∀ ij∈P, gap ij∈Gaps) →
    (∀ ij∈P, N ≤ AlenA ij.1.1 ∧ AlenA ij.1.1 ≤ 3*N ∧
      round (za ij.1.1)+(AlenA ij.1.1:ℤ)=Za+(N:ℤ)*ij.1.1+2*(N:ℤ)) →
    (∀ ij∈P, N ≤ AlenB ij.2.1 ∧ AlenB ij.2.1 ≤ 3*N ∧
      round (zb ij.2.1)+(AlenB ij.2.1:ℤ)=Zb+(N:ℤ)*ij.2.1+2*(N:ℤ)) →
    (δ ≤ min (modelPhaseThirdLower σ) 1) →
    (∀ i, Expdb.IsApproximateModelPhaseFunction (F i) σ 4 δ) →
    (0 < T) →
    (0 < M) →
    (0 < (N:ℝ)) →
    (1 ≤ R) →
    (R ≤ M) →
    (0 < Q) →
    (T*(N:ℝ)*R^2=M^3) →
    ((Q:ℝ)*(N:ℝ) ≤ (K₀:ℝ)*R^2) →
    (∀ i, M ≤ (A i:ℝ)) →
    (∀ i, (A i:ℝ)+W i ≤ 2*M) →
    (∀ ij∈P, ∀ i, xlocal ij i∈Ioo (1/2:ℝ) (W i-1/2)) →
    (∀ ij∈P, ∀ i, (rat ij i).den ≤ Q ∧ Q ≤ 2*(rat ij i).den) →
    (0 < lambda) →
    (0 < Uband) → (Uband ≤ 1) →
    (0 < θ) →
    (θ ≤ 1/24) →
    (∀ ij∈P, ∀ i, lambda ≤ |(rat ij i:ℝ)| ∧ |(rat ij i:ℝ)| ≤ Uband) →
    (∀ ij∈P, ∀ i, ((rat ij i).den:ℤ) ∣ (rat ij i).num*vinv ij i-1) →
    (∀ ab∈Gaps, (v ab)*(r ab)-(e ab)*(s ab)=1) →
    (∀ ab∈Gaps, ((0:ℝ) < (r ab) ∧ ((e ab):ℝ)/(r ab)=ab.1) ∨
      (((r ab):ℝ) < 0 ∧ ((e ab):ℝ)/(r ab)=ab.2)) →
    (0 < Bcut) →
    (∀ ab∈Gaps, (s ab) ≠ 0) →
    (∀ ab∈Gaps, ((e ab):ℝ)/(r ab)∈Refs) →
    (∀ ab∈Gaps, ((v ab):ℝ)/(s ab)∈Refs) →
    (∀ a∈Refs, ∀ b∈Refs, a ≠ b → ((Uref:ℝ)/R^2)/4 < |a-b|) →
    (∀ ij∈P, ∀ i, xlocal ij i-(56*(Uref:ℝ)/modelPhaseThirdLower σ)*(N:ℝ)∈Ioo (1/2:ℝ) (W i-1/2)) →
    (∀ ij∈P, ∀ i, xlocal ij i+(56*(Uref:ℝ)/modelPhaseThirdLower σ)*(N:ℝ)∈Ioo (1/2:ℝ) (W i-1/2)) →
    (1 ≤ Uref) →
    (2+168/modelPhaseThirdLower σ ≤ Bselect) →
    (7*Bcut ≤ modelPhaseThirdLower σ*Bselect) →
    (Bselect^2*(Uref:ℝ)^3*R^2 ≤ (N:ℝ)^2) →
    (∀ ab∈Gaps, R^2 ≤ ((r ab):ℝ)^2*(Uref:ℝ)) →
    (∀ ab∈Gaps, ab.2-ab.1 ≤ 7*(Uref:ℝ)/(2*R^2)) →
    (R ≤ (Q:ℝ)) →
    ((Uref:ℝ) ≤ ((N:ℝ)/(Q:ℝ))^((2:ℝ)/3)/Bselect) →
    ((N:ℝ)^10 ≤ M^3*R^7) →
    (∀ ij∈P, (rat ij 0:ℝ)∈Icc (gap ij).1 (gap ij).2) →
    (∀ ij∈P, Mat ij 2 ≠ 0) →
    (∀ ij∈P, 64*(modelPhaseJetCoefficient σ 3+δ)*M^2 ≤
      |(Mat ij 2:ℝ)| *(modelPhaseThirdLower σ)^2*T) →
    (∀ ij∈P, 8*Uband ≤ |(Mat ij 2:ℝ)| *lambda^2) →
    (∀ ab∈Gaps, ab.1∈Refs ∧ ab.2∈Refs ∧ ab.1 < ab.2 ∧
      ∀ t∈Refs, ¬(ab.1 < t ∧ t < ab.2)) →
    (Q:ℝ) ≤ (N:ℝ) →
    ((N:ℝ)^2 ≤ M ∨ (1 ≤ M ∧ (N:ℝ) ≤ T ∧ R^2 ≤ T)) → (Uref:ℝ) ≤ R^2 →
    (∀ ab∈Gaps, |((r ab):ℝ)| ≤ 4*R^2/(Uref:ℝ)) →
    (∀ ab∈Gaps, |((s ab):ℝ)| ≤ 4*R^2/(Uref:ℝ)) →
    (∀ ab∈Gaps, |((e ab):ℝ)| ≤
      (3*Jref*T/(2*σ*M^2)+1)*(4*R^2/(Uref:ℝ))) →
    (∀ ab∈Gaps, |((v ab):ℝ)| ≤
      (3*Jref*T/(2*σ*M^2)+1)*(4*R^2/(Uref:ℝ))) →
    let ε := modelPhaseThirdLower σ/(16*(σ*(σ+1)+1+2)*R^2)
    let sourceColor := fun ij i => (⌊((rat ij i).den:ℝ)/(θ*((Q:ℝ)/2))⌋,
      ⌊((rat ij i).num:ℝ)/(θ*(lambda*(Q:ℝ)/2))⌋)
    (∀ ij∈P, sourceColor ij 0=sourceColor ij 1) →
    let f := fun (i : Fin 2) w => T*F i (w/M)
    (∀ ij∈P, ∀ i, iteratedDeriv 2 (f i) (x ij i)/2=(rat ij i:ℝ)) →
    let q := fun ij i => (rat ij i).den
    let mu := fun ij i => iteratedDeriv 3 (f i) (round (x ij i))/6
    let ell := fun ij i => deriv (f i) (round (x ij i))
    let b := fun ij i => (⌊(q ij i:ℝ)*ell ij i⌋+(parity ij i:ℕ) : ℤ)
    let cround := fun ij i => round ((q ij i:ℝ)*ell ij i)
    let tau := fun ij i => ((b ij i:ℝ)-(q ij i:ℝ)*ell ij i)/2
    let dual := fun ij i => -2*mu ij i*(Real.sqrt (2/(3*mu ij i*(q ij i:ℝ))))^3
    let cloud := fun ij i => (![Int.fract (-(vinv ij i:ℝ)*b ij i/q ij i),
      Int.fract (-(vinv ij i:ℝ)/q ij i),dual ij i/Real.sqrt K₀,
      (3*dual ij i*tau ij i/2)/Real.sqrt K₀] : Fin 4 → ℝ)
    let radius : Fin 4 → ℝ := ![1/(12*(K₀:ℝ)),1/(12*(K₀:ℝ)^2),(1/(K₀:ℝ)^2)/12,(1/(K₀:ℝ))/12]
    (∀ ij∈P, b ij 0-cround ij 0=b ij 1-cround ij 1) →
    (∀ ij∈P, ∀ a, |cloud ij 0 a-cloud ij 1 a| ≤ 2*radius a) →
    (∀ ij∈P,
      |cloud ij 0 1-cloud ij 1 1| ≤ 1/(6*(K₀:ℝ)^2*V)) →
    let κ := modelPhaseThirdLower σ
    let Cphys := σ*(σ+1)+1
    let c := κ/6
    let J := Cphys/6
    let B := max 1 (max (2*Real.sqrt J) (8*J*Real.sqrt J/(3*c)))
    B*R^2/(N:ℝ)^2 ≤ 1/2 →
    (N:ℝ) ≤ R^2 →
    R ≤ (N:ℝ) →
    (N:ℝ)^3 ≤ M*R^2 →
    2*R^2 ≤ (Q:ℝ)*(N:ℝ) →
    (∀ ij∈P, Mat ij 0*Mat ij 3-Mat ij 1*Mat ij 2=1) →
    (∀ ij∈P, (Mat ij 2:ℝ)*(rat ij 0:ℝ)+Mat ij 3=(q ij 1:ℝ)/q ij 0) →
    (∀ ij∈P, ((Mat ij 0:ℝ)*(rat ij 0:ℝ)+Mat ij 1)/
      ((Mat ij 2:ℝ)*(rat ij 0:ℝ)+Mat ij 3)=(rat ij 1:ℝ)) →
    (∀ ij∈P, |(Mat ij 2:ℝ)| ≤ (Q:ℝ)^2/(6*(K₀:ℝ)^2)) →
    let H := (N:ℝ)/(Cphys+2)
    2 ≤ (N:ℝ) →
    (∀ ij∈P, ∀ i, xlocal ij i-H∈Ioo (1/2:ℝ) (W i-1/2)) →
    (∀ ij∈P, ∀ i, xlocal ij i+H∈Ioo (1/2:ℝ) (W i-1/2)) →
    (∀ ij∈P, |(anchor ij:ℝ)-(rat ij 0:ℝ)| ≤ ε) →
    (∀ ij∈P, 256*((anchor ij).den:ℝ) ≤ (Q:ℝ)/3) →
    (∀ ij∈P, 256 ≤ (2*ε)*((Q:ℝ)/3)*(anchor ij).den) →
    let C₂ := modelPhaseJetCoefficient σ 2+δ
    let C₃ := modelPhaseJetCoefficient σ 3+δ
    let Ct := C₂/2+5*C₃/12
    let Cc := C₂/κ+C₃/(2*κ)
    let Δ := (37*B/2+16*B*Cc+2*Ct+2*Cc)*(Q:ℝ)/(N:ℝ)
    let Ccurv := (4/κ)*(B+2*quarticReciprocalConstant σ δ)
    let D := Δ+quarticNonlinearResidualConstant σ δ*(2*(Q:ℝ))/(N:ℝ)
    let Kres := 4*(37*B/2+16*B*Cc+2*Ct+2*Cc+
      2*quarticNonlinearResidualConstant σ δ)/κ
    let Esize := κ/(16*(Cphys+2))
    let Dbase := 37*B/2+16*B*Cc+2*Ct+2*Cc+2*quarticNonlinearResidualConstant σ δ
    let Tbase := (2/κ)*(B+2*quarticReciprocalConstant σ δ)
    2*3840*128^2*105*(Dbase+64*Tbase*Esize^2) ≤ Bselect*Esize →
    D ≤ 1/2 → Δ < 1/2 → 61*Ccurv*Cphys ≤ Bcut →
    let Lunit := 2*κ/Cphys
    let Gamma := Cphys/κ
    let Cthird := Gamma*(32*Kres+9*quarticReciprocalConstant σ δ)
    let Cpack := 64*Cphys*(Gamma^2*Cthird+Gamma*(modelPhaseJetCoefficient σ 3+δ)/κ)/κ
    let Cfirst := 128*Cphys*(Gamma^2*Cthird+Gamma*(modelPhaseJetCoefficient σ 3+δ)/κ)/κ^2
    let Cgap := 64*Cphys*(Gamma^2*B+Gamma*(modelPhaseJetCoefficient σ 3+δ)/κ)/κ
    let Cmain := 4*(2*Cfirst/Lunit^3)^((3:ℝ)⁻¹)+2
    let Ctail := 4*Cpack/Lunit^2+Cgap
    V*(P.card:ℝ) ≤
      (60*588*(Uband/lambda)^2*Uband^2*(R^8/(N:ℝ)^4)*
        (Cmain*((Q:ℝ)/(Uband*(N:ℝ)))^((2:ℝ)/3)+Ctail/(Uref:ℝ)))*T^εloss := by
  exact eventually_model_global_large_entry_source_mass_clamped hσ hJref hεloss

#print axioms eventually_model_global_large_entry_source_mass_clamped


private theorem eventually_model_tagged_large_entry_source_mass_clamped
    {σ Jref εloss : ℝ} (hσ : 0 < σ) (hJref : 0 ≤ Jref) (hεloss : 0 < εloss) :
    ∀ᶠ T : ℝ in Filter.atTop, ∀ (F : Fin 2 → ℝ → ℝ) (ya yb : ℝ)
    (Uref : ℕ) (Refs : Finset ℝ) (Gaps : Finset (ℝ × ℝ)) {Bselect : ℝ}
    (P : Finset (((ℝ × ℤ) × Fin 2) × ((ℝ × ℤ) × Fin 2))) (Mat : (((ℝ × ℤ) × Fin 2) × ((ℝ × ℤ) × Fin 2)) → Fin 4 → ℤ)
    (gap : (((ℝ × ℤ) × Fin 2) × ((ℝ × ℤ) × Fin 2)) → ℝ × ℝ)
    (Q K₀ : ℕ) [NeZero K₀]
    (N : ℕ) (za zb : ℤ → ℝ) (AlenA AlenB : ℤ → ℕ) (Za Zb : ℤ)
    (rat : (((ℝ × ℤ) × Fin 2) × ((ℝ × ℤ) × Fin 2)) → Fin 2 → ℚ)
    (vinv : (((ℝ × ℤ) × Fin 2) × ((ℝ × ℤ) × Fin 2)) → Fin 2 → ℤ)
    (parity : (((ℝ × ℤ) × Fin 2) × ((ℝ × ℤ) × Fin 2)) → Fin 2 → Fin 2)
    (anchor : (((ℝ × ℤ) × Fin 2) × ((ℝ × ℤ) × Fin 2)) → ℚ)
    (e r v s : ℝ × ℝ → ℤ)
    {δ M R base Bcut lambda Uband θ : ℝ}
    (A : Fin 2 → ℤ) {W : Fin 2 → ℝ},
    let V := max 1 (Uband*(N:ℝ)/(Q:ℝ))
    let x := fun ij : ((ℝ × ℤ) × Fin 2) × ((ℝ × ℤ) × Fin 2) => (![za ij.1.1.2,zb ij.2.1.2] : Fin 2 → ℝ)
    let xlocal := fun ij i => x ij i-(A i:ℝ)
    (∀ ij∈P, ij.1.1.1=ya ∧ ij.2.1.1=yb) →
    (∀ ij∈P, base ≤ za ij.1.1.2-(A 0:ℝ)) →
    (∀ ij∈P, gap ij∈Gaps) →
    (∀ ij∈P, N ≤ AlenA ij.1.1.2 ∧ AlenA ij.1.1.2 ≤ 3*N ∧
      round (za ij.1.1.2)+(AlenA ij.1.1.2:ℤ)=Za+(N:ℤ)*ij.1.1.2+2*(N:ℤ)) →
    (∀ ij∈P, N ≤ AlenB ij.2.1.2 ∧ AlenB ij.2.1.2 ≤ 3*N ∧
      round (zb ij.2.1.2)+(AlenB ij.2.1.2:ℤ)=Zb+(N:ℤ)*ij.2.1.2+2*(N:ℤ)) →
    (δ ≤ min (modelPhaseThirdLower σ) 1) →
    (∀ i, Expdb.IsApproximateModelPhaseFunction (F i) σ 4 δ) →
    (0 < T) →
    (0 < M) →
    (0 < (N:ℝ)) →
    (1 ≤ R) →
    (R ≤ M) →
    (0 < Q) →
    (T*(N:ℝ)*R^2=M^3) →
    ((Q:ℝ)*(N:ℝ) ≤ (K₀:ℝ)*R^2) →
    (∀ i, M ≤ (A i:ℝ)) →
    (∀ i, (A i:ℝ)+W i ≤ 2*M) →
    (∀ ij∈P, ∀ i, xlocal ij i∈Ioo (1/2:ℝ) (W i-1/2)) →
    (∀ ij∈P, ∀ i, (rat ij i).den ≤ Q ∧ Q ≤ 2*(rat ij i).den) →
    (0 < lambda) →
    (0 < Uband) → (Uband ≤ 1) →
    (0 < θ) →
    (θ ≤ 1/24) →
    (∀ ij∈P, ∀ i, lambda ≤ |(rat ij i:ℝ)| ∧ |(rat ij i:ℝ)| ≤ Uband) →
    (∀ ij∈P, ∀ i, ((rat ij i).den:ℤ) ∣ (rat ij i).num*vinv ij i-1) →
    (∀ ab∈Gaps, (v ab)*(r ab)-(e ab)*(s ab)=1) →
    (∀ ab∈Gaps, ((0:ℝ) < (r ab) ∧ ((e ab):ℝ)/(r ab)=ab.1) ∨
      (((r ab):ℝ) < 0 ∧ ((e ab):ℝ)/(r ab)=ab.2)) →
    (0 < Bcut) →
    (∀ ab∈Gaps, (s ab) ≠ 0) →
    (∀ ab∈Gaps, ((e ab):ℝ)/(r ab)∈Refs) →
    (∀ ab∈Gaps, ((v ab):ℝ)/(s ab)∈Refs) →
    (∀ a∈Refs, ∀ b∈Refs, a ≠ b → ((Uref:ℝ)/R^2)/4 < |a-b|) →
    (∀ ij∈P, ∀ i, xlocal ij i-(56*(Uref:ℝ)/modelPhaseThirdLower σ)*(N:ℝ)∈Ioo (1/2:ℝ) (W i-1/2)) →
    (∀ ij∈P, ∀ i, xlocal ij i+(56*(Uref:ℝ)/modelPhaseThirdLower σ)*(N:ℝ)∈Ioo (1/2:ℝ) (W i-1/2)) →
    (1 ≤ Uref) →
    (2+168/modelPhaseThirdLower σ ≤ Bselect) →
    (7*Bcut ≤ modelPhaseThirdLower σ*Bselect) →
    (Bselect^2*(Uref:ℝ)^3*R^2 ≤ (N:ℝ)^2) →
    (∀ ab∈Gaps, R^2 ≤ ((r ab):ℝ)^2*(Uref:ℝ)) →
    (∀ ab∈Gaps, ab.2-ab.1 ≤ 7*(Uref:ℝ)/(2*R^2)) →
    (R ≤ (Q:ℝ)) →
    ((Uref:ℝ) ≤ ((N:ℝ)/(Q:ℝ))^((2:ℝ)/3)/Bselect) →
    ((N:ℝ)^10 ≤ M^3*R^7) →
    (∀ ij∈P, (rat ij 0:ℝ)∈Icc (gap ij).1 (gap ij).2) →
    (∀ ij∈P, Mat ij 2 ≠ 0) →
    (∀ ij∈P, 64*(modelPhaseJetCoefficient σ 3+δ)*M^2 ≤
      |(Mat ij 2:ℝ)| *(modelPhaseThirdLower σ)^2*T) →
    (∀ ij∈P, 8*Uband ≤ |(Mat ij 2:ℝ)| *lambda^2) →
    (∀ ab∈Gaps, ab.1∈Refs ∧ ab.2∈Refs ∧ ab.1 < ab.2 ∧
      ∀ t∈Refs, ¬(ab.1 < t ∧ t < ab.2)) →
    (Q:ℝ) ≤ (N:ℝ) →
    ((N:ℝ)^2 ≤ M ∨ (1 ≤ M ∧ (N:ℝ) ≤ T ∧ R^2 ≤ T)) → (Uref:ℝ) ≤ R^2 →
    (∀ ab∈Gaps, |((r ab):ℝ)| ≤ 4*R^2/(Uref:ℝ)) →
    (∀ ab∈Gaps, |((s ab):ℝ)| ≤ 4*R^2/(Uref:ℝ)) →
    (∀ ab∈Gaps, |((e ab):ℝ)| ≤
      (3*Jref*T/(2*σ*M^2)+1)*(4*R^2/(Uref:ℝ))) →
    (∀ ab∈Gaps, |((v ab):ℝ)| ≤
      (3*Jref*T/(2*σ*M^2)+1)*(4*R^2/(Uref:ℝ))) →
    let ε := modelPhaseThirdLower σ/(16*(σ*(σ+1)+1+2)*R^2)
    let sourceColor := fun ij i => (⌊((rat ij i).den:ℝ)/(θ*((Q:ℝ)/2))⌋,
      ⌊((rat ij i).num:ℝ)/(θ*(lambda*(Q:ℝ)/2))⌋)
    (∀ ij∈P, sourceColor ij 0=sourceColor ij 1) →
    let f := fun (i : Fin 2) w => T*F i (w/M)
    (∀ ij∈P, ∀ i, iteratedDeriv 2 (f i) (x ij i)/2=(rat ij i:ℝ)) →
    let q := fun ij i => (rat ij i).den
    let mu := fun ij i => iteratedDeriv 3 (f i) (round (x ij i))/6
    let ell := fun ij i => deriv (f i) (round (x ij i))
    let b := fun ij i => (⌊(q ij i:ℝ)*ell ij i⌋+(parity ij i:ℕ) : ℤ)
    let cround := fun ij i => round ((q ij i:ℝ)*ell ij i)
    let tau := fun ij i => ((b ij i:ℝ)-(q ij i:ℝ)*ell ij i)/2
    let dual := fun ij i => -2*mu ij i*(Real.sqrt (2/(3*mu ij i*(q ij i:ℝ))))^3
    let cloud := fun ij i => (![Int.fract (-(vinv ij i:ℝ)*b ij i/q ij i),
      Int.fract (-(vinv ij i:ℝ)/q ij i),dual ij i/Real.sqrt K₀,
      (3*dual ij i*tau ij i/2)/Real.sqrt K₀] : Fin 4 → ℝ)
    let radius : Fin 4 → ℝ := ![1/(12*(K₀:ℝ)),1/(12*(K₀:ℝ)^2),(1/(K₀:ℝ)^2)/12,(1/(K₀:ℝ))/12]
    (∀ ij∈P, b ij 0-cround ij 0=b ij 1-cround ij 1) →
    (∀ ij∈P, ∀ a, |cloud ij 0 a-cloud ij 1 a| ≤ 2*radius a) →
    (∀ ij∈P,
      |cloud ij 0 1-cloud ij 1 1| ≤ 1/(6*(K₀:ℝ)^2*V)) →
    let κ := modelPhaseThirdLower σ
    let Cphys := σ*(σ+1)+1
    let c := κ/6
    let J := Cphys/6
    let B := max 1 (max (2*Real.sqrt J) (8*J*Real.sqrt J/(3*c)))
    B*R^2/(N:ℝ)^2 ≤ 1/2 →
    (N:ℝ) ≤ R^2 →
    R ≤ (N:ℝ) →
    (N:ℝ)^3 ≤ M*R^2 →
    2*R^2 ≤ (Q:ℝ)*(N:ℝ) →
    (∀ ij∈P, Mat ij 0*Mat ij 3-Mat ij 1*Mat ij 2=1) →
    (∀ ij∈P, (Mat ij 2:ℝ)*(rat ij 0:ℝ)+Mat ij 3=(q ij 1:ℝ)/q ij 0) →
    (∀ ij∈P, ((Mat ij 0:ℝ)*(rat ij 0:ℝ)+Mat ij 1)/
      ((Mat ij 2:ℝ)*(rat ij 0:ℝ)+Mat ij 3)=(rat ij 1:ℝ)) →
    (∀ ij∈P, |(Mat ij 2:ℝ)| ≤ (Q:ℝ)^2/(6*(K₀:ℝ)^2)) →
    let H := (N:ℝ)/(Cphys+2)
    2 ≤ (N:ℝ) →
    (∀ ij∈P, ∀ i, xlocal ij i-H∈Ioo (1/2:ℝ) (W i-1/2)) →
    (∀ ij∈P, ∀ i, xlocal ij i+H∈Ioo (1/2:ℝ) (W i-1/2)) →
    (∀ ij∈P, |(anchor ij:ℝ)-(rat ij 0:ℝ)| ≤ ε) →
    (∀ ij∈P, 256*((anchor ij).den:ℝ) ≤ (Q:ℝ)/3) →
    (∀ ij∈P, 256 ≤ (2*ε)*((Q:ℝ)/3)*(anchor ij).den) →
    let C₂ := modelPhaseJetCoefficient σ 2+δ
    let C₃ := modelPhaseJetCoefficient σ 3+δ
    let Ct := C₂/2+5*C₃/12
    let Cc := C₂/κ+C₃/(2*κ)
    let Δ := (37*B/2+16*B*Cc+2*Ct+2*Cc)*(Q:ℝ)/(N:ℝ)
    let Ccurv := (4/κ)*(B+2*quarticReciprocalConstant σ δ)
    let D := Δ+quarticNonlinearResidualConstant σ δ*(2*(Q:ℝ))/(N:ℝ)
    let Kres := 4*(37*B/2+16*B*Cc+2*Ct+2*Cc+
      2*quarticNonlinearResidualConstant σ δ)/κ
    let Esize := κ/(16*(Cphys+2))
    let Dbase := 37*B/2+16*B*Cc+2*Ct+2*Cc+2*quarticNonlinearResidualConstant σ δ
    let Tbase := (2/κ)*(B+2*quarticReciprocalConstant σ δ)
    2*3840*128^2*105*(Dbase+64*Tbase*Esize^2) ≤ Bselect*Esize →
    D ≤ 1/2 → Δ < 1/2 → 61*Ccurv*Cphys ≤ Bcut →
    let Lunit := 2*κ/Cphys
    let Gamma := Cphys/κ
    let Cthird := Gamma*(32*Kres+9*quarticReciprocalConstant σ δ)
    let Cpack := 64*Cphys*(Gamma^2*Cthird+Gamma*(modelPhaseJetCoefficient σ 3+δ)/κ)/κ
    let Cfirst := 128*Cphys*(Gamma^2*Cthird+Gamma*(modelPhaseJetCoefficient σ 3+δ)/κ)/κ^2
    let Cgap := 64*Cphys*(Gamma^2*B+Gamma*(modelPhaseJetCoefficient σ 3+δ)/κ)/κ
    let Cmain := 4*(2*Cfirst/Lunit^3)^((3:ℝ)⁻¹)+2
    let Ctail := 4*Cpack/Lunit^2+Cgap
    V*(P.card:ℝ) ≤
      (60*588*(Uband/lambda)^2*Uband^2*(R^8/(N:ℝ)^4)*
        (Cmain*((Q:ℝ)/(Uband*(N:ℝ)))^((2:ℝ)/3)+Ctail/(Uref:ℝ)))*T^εloss := by
  classical
  filter_upwards [eventually_model_global_large_entry_source_mass_clamped hσ hJref hεloss]
    with T hraw
  intro F ya yb Uref Refs Gaps Bselect P Mat gap Q K₀ inst N za zb AlenA AlenB Za Zb
    rat vinv parity anchor e r v s δ M R base Bcut lambda Uband θ A W V x xlocal
    hphase hbase hgapMem hgeometryA hgeometryB hδ hF hT hM hN hR hRM hQ hscale hmesh hA hW hx hden hlambda hUband hUbandCap hθ hθmax hcurv hinv hchart horientation hBcut hs hrefSet hparentSet hsep hwideL hwideU hUref hBselectSize hcutMargin hselectedWrap hreferenceDen hgapWidth hRQ hselectedUpper hscaleTen hfamilyGap hc hlarge haction hgap
    hQN hNM hUR hrHeight hsHeight heHeight hvHeight
    ε sourceColor hsourceColor f hlevel q mu ell b cround tau dual cloud radius
    hcolor hnear hnearNarrow κ Cphys c J B hsmall hNR hRN hNcube hminscale
    hMatdet hMatt hMatmap hMatgamma H hNtwo hL hU hanchor hcut hcount
    C₂ C₃ Ct Cc Δ Ccurv D Kres Esize Dbase Tbase hsize hD hΔ hBsize
    Lunit Gamma Cthird Cpack Cfirst Cgap Cmain Ctail

  let forget := fun ij : ((ℝ × ℤ) × Fin 2) × ((ℝ × ℤ) × Fin 2) =>
    ((ij.1.1.2,ij.1.2),(ij.2.1.2,ij.2.2))
  let embed := fun ij : (ℤ × Fin 2) × (ℤ × Fin 2) =>
    (((ya,ij.1.1),ij.1.2),((yb,ij.2.1),ij.2.2))
  let Pbar := P.image forget
  have hback ij (hij : ij∈P) : embed (forget ij)=ij := by
    rcases ij with ⟨⟨⟨a,n⟩,pa⟩,⟨⟨b,m⟩,pb⟩⟩
    have he := hphase _ hij
    dsimp only at he
    rcases he with ⟨rfl,rfl⟩
    rfl
  have hcard : Pbar.card=P.card := by
    apply Finset.card_image_of_injOn
    intro ij hij kl hkl he
    exact (hback ij hij).symm.trans ((congrArg embed he).trans (hback kl hkl))
  have hmem ij (hij : ij∈Pbar) : embed ij∈P := by
    obtain ⟨kl,hkl,rfl⟩ := Finset.mem_image.mp hij
    rw [hback kl hkl]
    exact hkl
  have hh := hraw F Uref Refs Gaps (Bselect:=Bselect)
    Pbar (fun ij => Mat (embed ij)) (fun ij => gap (embed ij)) Q K₀ N
    za zb AlenA AlenB Za Zb (fun ij => rat (embed ij)) (fun ij => vinv (embed ij))
    (fun ij => parity (embed ij)) (fun ij => anchor (embed ij)) e r v s
    (δ:=δ) (M:=M) (R:=R) (base:=base) (Bcut:=Bcut)
    (lambda:=lambda) (Uband:=Uband) (θ:=θ) A (W:=W)
    (fun ij hij => hbase (embed ij) (hmem ij hij))
    (fun ij hij => hgapMem (embed ij) (hmem ij hij))
    (fun ij hij => hgeometryA (embed ij) (hmem ij hij))
    (fun ij hij => hgeometryB (embed ij) (hmem ij hij))
    hδ hF hT hM hN hR hRM hQ hscale hmesh hA hW
    (fun ij hij => hx (embed ij) (hmem ij hij))
    (fun ij hij => hden (embed ij) (hmem ij hij))
    hlambda hUband hUbandCap hθ hθmax
    (fun ij hij => hcurv (embed ij) (hmem ij hij))
    (fun ij hij => hinv (embed ij) (hmem ij hij))
    hchart horientation hBcut hs hrefSet hparentSet hsep
    (fun ij hij => hwideL (embed ij) (hmem ij hij))
    (fun ij hij => hwideU (embed ij) (hmem ij hij))
    hUref hBselectSize hcutMargin hselectedWrap hreferenceDen hgapWidth hRQ hselectedUpper
    hscaleTen
    (fun ij hij => hfamilyGap (embed ij) (hmem ij hij))
    (fun ij hij => hc (embed ij) (hmem ij hij))
    (fun ij hij => hlarge (embed ij) (hmem ij hij))
    (fun ij hij => haction (embed ij) (hmem ij hij))
    hgap hQN hNM hUR hrHeight hsHeight heHeight hvHeight
    (fun ij hij => hsourceColor (embed ij) (hmem ij hij))
    (fun ij hij => hlevel (embed ij) (hmem ij hij))
    (fun ij hij => hcolor (embed ij) (hmem ij hij))
    (fun ij hij => hnear (embed ij) (hmem ij hij))
    (fun ij hij => hnearNarrow (embed ij) (hmem ij hij))
    hsmall hNR hRN hNcube hminscale
    (fun ij hij => hMatdet (embed ij) (hmem ij hij))
    (fun ij hij => hMatt (embed ij) (hmem ij hij))
    (fun ij hij => hMatmap (embed ij) (hmem ij hij))
    (fun ij hij => hMatgamma (embed ij) (hmem ij hij))
    hNtwo
    (fun ij hij => hL (embed ij) (hmem ij hij))
    (fun ij hij => hU (embed ij) (hmem ij hij))
    (fun ij hij => hanchor (embed ij) (hmem ij hij))
    (fun ij hij => hcut (embed ij) (hmem ij hij))
    (fun ij hij => hcount (embed ij) (hmem ij hij))
    hsize hD hΔ hBsize
  simpa only [hcard] using hh

example
    {σ Jref εloss : ℝ} (hσ : 0 < σ) (hJref : 0 ≤ Jref) (hεloss : 0 < εloss) :
    ∀ᶠ T : ℝ in Filter.atTop, ∀ (F : Fin 2 → ℝ → ℝ) (ya yb : ℝ)
    (Uref : ℕ) (Refs : Finset ℝ) (Gaps : Finset (ℝ × ℝ)) {Bselect : ℝ}
    (P : Finset (((ℝ × ℤ) × Fin 2) × ((ℝ × ℤ) × Fin 2))) (Mat : (((ℝ × ℤ) × Fin 2) × ((ℝ × ℤ) × Fin 2)) → Fin 4 → ℤ)
    (gap : (((ℝ × ℤ) × Fin 2) × ((ℝ × ℤ) × Fin 2)) → ℝ × ℝ)
    (Q K₀ : ℕ) [NeZero K₀]
    (N : ℕ) (za zb : ℤ → ℝ) (AlenA AlenB : ℤ → ℕ) (Za Zb : ℤ)
    (rat : (((ℝ × ℤ) × Fin 2) × ((ℝ × ℤ) × Fin 2)) → Fin 2 → ℚ)
    (vinv : (((ℝ × ℤ) × Fin 2) × ((ℝ × ℤ) × Fin 2)) → Fin 2 → ℤ)
    (parity : (((ℝ × ℤ) × Fin 2) × ((ℝ × ℤ) × Fin 2)) → Fin 2 → Fin 2)
    (anchor : (((ℝ × ℤ) × Fin 2) × ((ℝ × ℤ) × Fin 2)) → ℚ)
    (e r v s : ℝ × ℝ → ℤ)
    {δ M R base Bcut lambda Uband θ : ℝ}
    (A : Fin 2 → ℤ) {W : Fin 2 → ℝ},
    let V := max 1 (Uband*(N:ℝ)/(Q:ℝ))
    let x := fun ij : ((ℝ × ℤ) × Fin 2) × ((ℝ × ℤ) × Fin 2) => (![za ij.1.1.2,zb ij.2.1.2] : Fin 2 → ℝ)
    let xlocal := fun ij i => x ij i-(A i:ℝ)
    (∀ ij∈P, ij.1.1.1=ya ∧ ij.2.1.1=yb) →
    (∀ ij∈P, base ≤ za ij.1.1.2-(A 0:ℝ)) →
    (∀ ij∈P, gap ij∈Gaps) →
    (∀ ij∈P, N ≤ AlenA ij.1.1.2 ∧ AlenA ij.1.1.2 ≤ 3*N ∧
      round (za ij.1.1.2)+(AlenA ij.1.1.2:ℤ)=Za+(N:ℤ)*ij.1.1.2+2*(N:ℤ)) →
    (∀ ij∈P, N ≤ AlenB ij.2.1.2 ∧ AlenB ij.2.1.2 ≤ 3*N ∧
      round (zb ij.2.1.2)+(AlenB ij.2.1.2:ℤ)=Zb+(N:ℤ)*ij.2.1.2+2*(N:ℤ)) →
    (δ ≤ min (modelPhaseThirdLower σ) 1) →
    (∀ i, Expdb.IsApproximateModelPhaseFunction (F i) σ 4 δ) →
    (0 < T) →
    (0 < M) →
    (0 < (N:ℝ)) →
    (1 ≤ R) →
    (R ≤ M) →
    (0 < Q) →
    (T*(N:ℝ)*R^2=M^3) →
    ((Q:ℝ)*(N:ℝ) ≤ (K₀:ℝ)*R^2) →
    (∀ i, M ≤ (A i:ℝ)) →
    (∀ i, (A i:ℝ)+W i ≤ 2*M) →
    (∀ ij∈P, ∀ i, xlocal ij i∈Ioo (1/2:ℝ) (W i-1/2)) →
    (∀ ij∈P, ∀ i, (rat ij i).den ≤ Q ∧ Q ≤ 2*(rat ij i).den) →
    (0 < lambda) →
    (0 < Uband) → (Uband ≤ 1) →
    (0 < θ) →
    (θ ≤ 1/24) →
    (∀ ij∈P, ∀ i, lambda ≤ |(rat ij i:ℝ)| ∧ |(rat ij i:ℝ)| ≤ Uband) →
    (∀ ij∈P, ∀ i, ((rat ij i).den:ℤ) ∣ (rat ij i).num*vinv ij i-1) →
    (∀ ab∈Gaps, (v ab)*(r ab)-(e ab)*(s ab)=1) →
    (∀ ab∈Gaps, ((0:ℝ) < (r ab) ∧ ((e ab):ℝ)/(r ab)=ab.1) ∨
      (((r ab):ℝ) < 0 ∧ ((e ab):ℝ)/(r ab)=ab.2)) →
    (0 < Bcut) →
    (∀ ab∈Gaps, (s ab) ≠ 0) →
    (∀ ab∈Gaps, ((e ab):ℝ)/(r ab)∈Refs) →
    (∀ ab∈Gaps, ((v ab):ℝ)/(s ab)∈Refs) →
    (∀ a∈Refs, ∀ b∈Refs, a ≠ b → ((Uref:ℝ)/R^2)/4 < |a-b|) →
    (∀ ij∈P, ∀ i, xlocal ij i-(56*(Uref:ℝ)/modelPhaseThirdLower σ)*(N:ℝ)∈Ioo (1/2:ℝ) (W i-1/2)) →
    (∀ ij∈P, ∀ i, xlocal ij i+(56*(Uref:ℝ)/modelPhaseThirdLower σ)*(N:ℝ)∈Ioo (1/2:ℝ) (W i-1/2)) →
    (1 ≤ Uref) →
    (2+168/modelPhaseThirdLower σ ≤ Bselect) →
    (7*Bcut ≤ modelPhaseThirdLower σ*Bselect) →
    (Bselect^2*(Uref:ℝ)^3*R^2 ≤ (N:ℝ)^2) →
    (∀ ab∈Gaps, R^2 ≤ ((r ab):ℝ)^2*(Uref:ℝ)) →
    (∀ ab∈Gaps, ab.2-ab.1 ≤ 7*(Uref:ℝ)/(2*R^2)) →
    (R ≤ (Q:ℝ)) →
    ((Uref:ℝ) ≤ ((N:ℝ)/(Q:ℝ))^((2:ℝ)/3)/Bselect) →
    ((N:ℝ)^10 ≤ M^3*R^7) →
    (∀ ij∈P, (rat ij 0:ℝ)∈Icc (gap ij).1 (gap ij).2) →
    (∀ ij∈P, Mat ij 2 ≠ 0) →
    (∀ ij∈P, 64*(modelPhaseJetCoefficient σ 3+δ)*M^2 ≤
      |(Mat ij 2:ℝ)| *(modelPhaseThirdLower σ)^2*T) →
    (∀ ij∈P, 8*Uband ≤ |(Mat ij 2:ℝ)| *lambda^2) →
    (∀ ab∈Gaps, ab.1∈Refs ∧ ab.2∈Refs ∧ ab.1 < ab.2 ∧
      ∀ t∈Refs, ¬(ab.1 < t ∧ t < ab.2)) →
    (Q:ℝ) ≤ (N:ℝ) →
    ((N:ℝ)^2 ≤ M ∨ (1 ≤ M ∧ (N:ℝ) ≤ T ∧ R^2 ≤ T)) → (Uref:ℝ) ≤ R^2 →
    (∀ ab∈Gaps, |((r ab):ℝ)| ≤ 4*R^2/(Uref:ℝ)) →
    (∀ ab∈Gaps, |((s ab):ℝ)| ≤ 4*R^2/(Uref:ℝ)) →
    (∀ ab∈Gaps, |((e ab):ℝ)| ≤
      (3*Jref*T/(2*σ*M^2)+1)*(4*R^2/(Uref:ℝ))) →
    (∀ ab∈Gaps, |((v ab):ℝ)| ≤
      (3*Jref*T/(2*σ*M^2)+1)*(4*R^2/(Uref:ℝ))) →
    let ε := modelPhaseThirdLower σ/(16*(σ*(σ+1)+1+2)*R^2)
    let sourceColor := fun ij i => (⌊((rat ij i).den:ℝ)/(θ*((Q:ℝ)/2))⌋,
      ⌊((rat ij i).num:ℝ)/(θ*(lambda*(Q:ℝ)/2))⌋)
    (∀ ij∈P, sourceColor ij 0=sourceColor ij 1) →
    let f := fun (i : Fin 2) w => T*F i (w/M)
    (∀ ij∈P, ∀ i, iteratedDeriv 2 (f i) (x ij i)/2=(rat ij i:ℝ)) →
    let q := fun ij i => (rat ij i).den
    let mu := fun ij i => iteratedDeriv 3 (f i) (round (x ij i))/6
    let ell := fun ij i => deriv (f i) (round (x ij i))
    let b := fun ij i => (⌊(q ij i:ℝ)*ell ij i⌋+(parity ij i:ℕ) : ℤ)
    let cround := fun ij i => round ((q ij i:ℝ)*ell ij i)
    let tau := fun ij i => ((b ij i:ℝ)-(q ij i:ℝ)*ell ij i)/2
    let dual := fun ij i => -2*mu ij i*(Real.sqrt (2/(3*mu ij i*(q ij i:ℝ))))^3
    let cloud := fun ij i => (![Int.fract (-(vinv ij i:ℝ)*b ij i/q ij i),
      Int.fract (-(vinv ij i:ℝ)/q ij i),dual ij i/Real.sqrt K₀,
      (3*dual ij i*tau ij i/2)/Real.sqrt K₀] : Fin 4 → ℝ)
    let radius : Fin 4 → ℝ := ![1/(12*(K₀:ℝ)),1/(12*(K₀:ℝ)^2),(1/(K₀:ℝ)^2)/12,(1/(K₀:ℝ))/12]
    (∀ ij∈P, b ij 0-cround ij 0=b ij 1-cround ij 1) →
    (∀ ij∈P, ∀ a, |cloud ij 0 a-cloud ij 1 a| ≤ 2*radius a) →
    (∀ ij∈P,
      |cloud ij 0 1-cloud ij 1 1| ≤ 1/(6*(K₀:ℝ)^2*V)) →
    let κ := modelPhaseThirdLower σ
    let Cphys := σ*(σ+1)+1
    let c := κ/6
    let J := Cphys/6
    let B := max 1 (max (2*Real.sqrt J) (8*J*Real.sqrt J/(3*c)))
    B*R^2/(N:ℝ)^2 ≤ 1/2 →
    (N:ℝ) ≤ R^2 →
    R ≤ (N:ℝ) →
    (N:ℝ)^3 ≤ M*R^2 →
    2*R^2 ≤ (Q:ℝ)*(N:ℝ) →
    (∀ ij∈P, Mat ij 0*Mat ij 3-Mat ij 1*Mat ij 2=1) →
    (∀ ij∈P, (Mat ij 2:ℝ)*(rat ij 0:ℝ)+Mat ij 3=(q ij 1:ℝ)/q ij 0) →
    (∀ ij∈P, ((Mat ij 0:ℝ)*(rat ij 0:ℝ)+Mat ij 1)/
      ((Mat ij 2:ℝ)*(rat ij 0:ℝ)+Mat ij 3)=(rat ij 1:ℝ)) →
    (∀ ij∈P, |(Mat ij 2:ℝ)| ≤ (Q:ℝ)^2/(6*(K₀:ℝ)^2)) →
    let H := (N:ℝ)/(Cphys+2)
    2 ≤ (N:ℝ) →
    (∀ ij∈P, ∀ i, xlocal ij i-H∈Ioo (1/2:ℝ) (W i-1/2)) →
    (∀ ij∈P, ∀ i, xlocal ij i+H∈Ioo (1/2:ℝ) (W i-1/2)) →
    (∀ ij∈P, |(anchor ij:ℝ)-(rat ij 0:ℝ)| ≤ ε) →
    (∀ ij∈P, 256*((anchor ij).den:ℝ) ≤ (Q:ℝ)/3) →
    (∀ ij∈P, 256 ≤ (2*ε)*((Q:ℝ)/3)*(anchor ij).den) →
    let C₂ := modelPhaseJetCoefficient σ 2+δ
    let C₃ := modelPhaseJetCoefficient σ 3+δ
    let Ct := C₂/2+5*C₃/12
    let Cc := C₂/κ+C₃/(2*κ)
    let Δ := (37*B/2+16*B*Cc+2*Ct+2*Cc)*(Q:ℝ)/(N:ℝ)
    let Ccurv := (4/κ)*(B+2*quarticReciprocalConstant σ δ)
    let D := Δ+quarticNonlinearResidualConstant σ δ*(2*(Q:ℝ))/(N:ℝ)
    let Kres := 4*(37*B/2+16*B*Cc+2*Ct+2*Cc+
      2*quarticNonlinearResidualConstant σ δ)/κ
    let Esize := κ/(16*(Cphys+2))
    let Dbase := 37*B/2+16*B*Cc+2*Ct+2*Cc+2*quarticNonlinearResidualConstant σ δ
    let Tbase := (2/κ)*(B+2*quarticReciprocalConstant σ δ)
    2*3840*128^2*105*(Dbase+64*Tbase*Esize^2) ≤ Bselect*Esize →
    D ≤ 1/2 → Δ < 1/2 → 61*Ccurv*Cphys ≤ Bcut →
    let Lunit := 2*κ/Cphys
    let Gamma := Cphys/κ
    let Cthird := Gamma*(32*Kres+9*quarticReciprocalConstant σ δ)
    let Cpack := 64*Cphys*(Gamma^2*Cthird+Gamma*(modelPhaseJetCoefficient σ 3+δ)/κ)/κ
    let Cfirst := 128*Cphys*(Gamma^2*Cthird+Gamma*(modelPhaseJetCoefficient σ 3+δ)/κ)/κ^2
    let Cgap := 64*Cphys*(Gamma^2*B+Gamma*(modelPhaseJetCoefficient σ 3+δ)/κ)/κ
    let Cmain := 4*(2*Cfirst/Lunit^3)^((3:ℝ)⁻¹)+2
    let Ctail := 4*Cpack/Lunit^2+Cgap
    V*(P.card:ℝ) ≤
      (60*588*(Uband/lambda)^2*Uband^2*(R^8/(N:ℝ)^4)*
        (Cmain*((Q:ℝ)/(Uband*(N:ℝ)))^((2:ℝ)/3)+Ctail/(Uref:ℝ)))*T^εloss := by
  exact eventually_model_tagged_large_entry_source_mass_clamped hσ hJref hεloss

#print axioms eventually_model_tagged_large_entry_source_mass_clamped


private theorem double_difference_source_large_action_threshold
    {σ c U E : ℝ} (hσ : 0 < σ) (hc : 0 < c) (hU : 0 < U) (hE : 0 < E) :
    let κ := modelPhaseThirdLower σ
    let L := max (32*U^2/c^2) (64*(modelPhaseJetCoefficient σ 3+1)*U*E/κ^2)
    0 ≤ L ∧ ∀ {Tsrc T M δ γ : ℝ}, 0 < Tsrc → 0 < T → 0 < M →
      Tsrc ≤ E*T → δ ≤ 1 →
      let lambda := c*Tsrc/(2*M^2)
      let Hcurv := U*Tsrc/M^2
      L < |γ| *Hcurv →
        γ ≠ 0 ∧ 8*Hcurv ≤ |γ| *lambda^2 ∧
          64*(modelPhaseJetCoefficient σ 3+δ)*M^2 ≤ |γ| *κ^2*T := by
  intro κ L
  have hκ : 0 < κ := modelPhaseThirdLower_pos hσ
  have hL : 0 ≤ L := (by positivity : (0:ℝ) ≤ 32*U^2/c^2).trans (le_max_left _ _)
  refine ⟨hL,?_⟩
  intro Tsrc T M δ γ hTsrc _hT hM hsource hδ lambda Hcurv hlarge
  have hH : 0 < Hcurv := by dsimp only [Hcurv]; positivity
  have hγ : γ ≠ 0 := by
    intro he
    rw [he,abs_zero,zero_mul] at hlarge
    exact (not_lt_of_ge hL) hlarge
  have hratio := (le_max_left (32*U^2/c^2)
    (64*(modelPhaseJetCoefficient σ 3+1)*U*E/κ^2)).trans hlarge.le
  have hcoef := (le_max_right (32*U^2/c^2)
    (64*(modelPhaseJetCoefficient σ 3+1)*U*E/κ^2)).trans hlarge.le
  have hratioId : (32*U^2/c^2)*lambda^2=8*Hcurv^2 := by
    dsimp only [lambda,Hcurv]
    field_simp
    ring
  have haction : 8*Hcurv ≤ |γ| *lambda^2 := by
    apply (mul_le_mul_iff_right₀ hH).mp
    have hh := mul_le_mul_of_nonneg_right hratio (sq_nonneg lambda)
    rw [hratioId] at hh
    nlinarith only [hh]
  have hcoe : 64*(modelPhaseJetCoefficient σ 3+1)*U*E ≤ (|γ| *Hcurv)*κ^2 :=
    (div_le_iff₀ (sq_pos_of_pos hκ)).mp hcoef
  have hbudget : 64*(modelPhaseJetCoefficient σ 3+1)*U*E*M^2 ≤
      |γ| *U*Tsrc*κ^2 := by
    have hh := mul_le_mul_of_nonneg_right hcoe (sq_nonneg M)
    have he : (|γ| *Hcurv)*κ^2*M^2=|γ| *U*Tsrc*κ^2 := by
      dsimp only [Hcurv]
      field_simp
    simpa only [he] using hh
  have hnormalized : 64*(modelPhaseJetCoefficient σ 3+1)*M^2 ≤ |γ| *κ^2*T := by
    apply (mul_le_mul_iff_right₀ (mul_pos hU hE)).mp
    have hh := mul_le_mul_of_nonneg_left hsource
      (show 0 ≤ |γ| *U*κ^2 by positivity)
    nlinarith only [hbudget,hh]
  refine ⟨hγ,haction,?_⟩
  exact (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (add_le_add le_rfl hδ) (by norm_num : (0:ℝ) ≤ 64))
    (sq_nonneg M)).trans hnormalized

example
    {σ c U E : ℝ} (hσ : 0 < σ) (hc : 0 < c) (hU : 0 < U) (hE : 0 < E) :
    let κ := modelPhaseThirdLower σ
    let L := max (32*U^2/c^2) (64*(modelPhaseJetCoefficient σ 3+1)*U*E/κ^2)
    0 ≤ L ∧ ∀ {Tsrc T M δ γ : ℝ}, 0 < Tsrc → 0 < T → 0 < M →
      Tsrc ≤ E*T → δ ≤ 1 →
      let lambda := c*Tsrc/(2*M^2)
      let Hcurv := U*Tsrc/M^2
      L < |γ| *Hcurv →
        γ ≠ 0 ∧ 8*Hcurv ≤ |γ| *lambda^2 ∧
          64*(modelPhaseJetCoefficient σ 3+δ)*M^2 ≤ |γ| *κ^2*T := by
  exact double_difference_source_large_action_threshold hσ hc hU hE

#print axioms double_difference_source_large_action_threshold


/-- The physical rational-curvature band is derived from the source
fourth derivative and the exact double shift, not supplied as a family input. -/
private theorem double_difference_physical_curvature_band
    (F : ℝ → ℝ) {z r s d y c U T M : ℝ}
    (hz : z∈Icc M (2*M)) (hy : y∈Icc (1:ℝ) 2)
    (hr : 0 < r) (hs : 0 < s) (hd : 0 < d)
    (hc : 0 < c) (hU : 0 < U) (hT : 0 < T) (hM : 0 < M)
    (hprod : r*s=d*y) (hshift : r+s ≤ 1/4)
    (hf : ∀ u, 0 < u → ContDiffAt ℝ ∞ F u)
    (hneg : ∀ u∈Icc (1/2:ℝ) 3, iteratedDeriv 4 F u ≤ -c)
    (hbound : ∀ u∈Icc (1/2:ℝ) 3, |iteratedDeriv 4 F u| ≤ U) :
    let Q := fun u => (F u-F (u+r)-F (u+s)+F (u+r+s))/d
    let f := fun w => T*Q (w/M)
    c*T/(2*M^2) ≤ |iteratedDeriv 2 f z/2| ∧
      |iteratedDeriv 2 f z/2| ≤ U*T/M^2 := by
  intro Q f
  have hzpos : 0 < z := hM.trans_le hz.1
  have hx : z/M∈Icc (3/4:ℝ) (9/4) := by
    constructor
    · apply (le_div_iff₀ hM).mpr
      linarith only [hz.1,hM]
    · apply (div_le_iff₀ hM).mpr
      linarith only [hz.2,hM]
  have hreg u (hu : 0 < u) : ContDiffAt ℝ ∞ Q u :=
    ((((hf u hu).sub ((hf (u+r) (by positivity)).comp u
      (contDiffAt_id.add contDiffAt_const))).sub
        ((hf (u+s) (by positivity)).comp u (contDiffAt_id.add contDiffAt_const))).add
          ((hf (u+r+s) (by positivity)).comp u
            ((contDiffAt_id.add contDiffAt_const).add contDiffAt_const))).div_const d
  have hphysical : iteratedDeriv 2 f z=T/M^2*iteratedDeriv 2 Q (z/M) := by
    have ha := sargos_iteratedDeriv_comp_affine_local (f:=Q)
      (l:=0) (r:=z+1) (c:=M⁻¹) (d:=0)
      (fun v hv => hreg _ (by
        simpa only [add_zero] using mul_pos (inv_pos.mpr hM) hv.1))
      (show z∈Ioo (0:ℝ) (z+1) from ⟨hzpos,by linarith⟩) 2
    change iteratedDeriv 2 (fun w => T*Q (w/M)) z=_
    rw [iteratedDeriv_const_mul_field]
    have he : (fun w => Q (w/M))=(fun w => Q (M⁻¹*w+0)) := by
      funext w
      congr 1
      ring
    rw [he,ha]
    simp only [add_zero,inv_pow]
    rw [show M⁻¹*z=z/M by ring]
    ring
  have hband : -2*U ≤ iteratedDeriv 2 Q (z/M) ∧
      iteratedDeriv 2 Q (z/M) ≤ -c :=
    double_difference_exact_curvature_band F hx hy hr hs hd hc hU hprod hshift hf hneg hbound
  have hsign : iteratedDeriv 2 Q (z/M) < 0 := by
    linarith only [hband.2,hc]
  rw [hphysical,abs_div,abs_mul,
    abs_of_pos (div_pos hT (pow_pos hM 2)),abs_of_neg hsign,
    abs_of_pos (by norm_num : (0:ℝ) < 2)]
  constructor
  · calc
      c*T/(2*M^2) = (T/M^2)*c/2 := by ring
      _ ≤ _ := div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left (by linarith only [hband.2]) (by positivity)) (by norm_num)
  · calc
      _ ≤ (T/M^2)*(2*U)/2 := div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left (by linarith only [hband.1]) (by positivity)) (by norm_num)
      _ = U*T/M^2 := by ring

example
    (F : ℝ → ℝ) {z r s d y c U T M : ℝ}
    (hz : z∈Icc M (2*M)) (hy : y∈Icc (1:ℝ) 2)
    (hr : 0 < r) (hs : 0 < s) (hd : 0 < d)
    (hc : 0 < c) (hU : 0 < U) (hT : 0 < T) (hM : 0 < M)
    (hprod : r*s=d*y) (hshift : r+s ≤ 1/4)
    (hf : ∀ u, 0 < u → ContDiffAt ℝ ∞ F u)
    (hneg : ∀ u∈Icc (1/2:ℝ) 3, iteratedDeriv 4 F u ≤ -c)
    (hbound : ∀ u∈Icc (1/2:ℝ) 3, |iteratedDeriv 4 F u| ≤ U) :
    let Q := fun u => (F u-F (u+r)-F (u+s)+F (u+r+s))/d
    let f := fun w => T*Q (w/M)
    c*T/(2*M^2) ≤ |iteratedDeriv 2 f z/2| ∧
      |iteratedDeriv 2 f z/2| ≤ U*T/M^2 := by
  exact double_difference_physical_curvature_band F hz hy hr hs hd hc hU hT hM hprod hshift hf hneg hbound

#print axioms double_difference_physical_curvature_band

/-- Same-matrix double-shift family source consumer. Reference/model/point
geometry remains explicit upstream data; the curvature band is derived.
No analytic count, matrix family, or moment certificate is assumed. -/
private theorem eventually_double_difference_actual_family_source_sieve
    {csrc Usrc E σ εloss : ℝ}
    (hcsrc : 0 < csrc) (hUsrc : 0 < Usrc)
    (hE : 0 < E) (hσ : 0 < σ) (hεloss : 0 < εloss) :
    let κ := modelPhaseThirdLower σ
    let L := max (32*Usrc^2/csrc^2)
      (64*(modelPhaseJetCoefficient σ 3+1)*Usrc*E/κ^2)
    let θ := 1/(8*(L+3))
    ∃ C Dtype : ℝ, 0 < C ∧ 0 < Dtype ∧
    ∀ {Jref : ℝ}, 0 ≤ Jref →
    ∀ᶠ T : ℝ in Filter.atTop, ∀ (S : Finset (ℝ × ℤ)) (Fsrc rshift sshift : ℝ → ℝ)
    (z : (ℝ × ℤ) → ℝ) (rat : (ℝ × ℤ) → ℚ) (v : (ℝ × ℤ) → ℤ) (Nlen : (ℝ × ℤ) → ℕ)
    (Q K₀ N : ℕ) [NeZero K₀] (R Jsep : ℝ) (Z : ℝ → ℤ)
    {d Wmax Tsrc M δ Bcut Bselect : ℝ}
    (Uref : ℕ) (Refs : Finset ℝ) (Gaps : Finset (ℝ × ℝ))
    (A : ℝ → ℤ) (W : ℝ → ℝ) (gap : (ℝ × ℤ) → ℝ × ℝ)
    (anchor : (ℝ × ℤ) → ℚ) (e r vRef s : ℝ × ℝ → ℤ),
    let lambda := csrc*Tsrc/(2*M^2)
    let Uband := Usrc*Tsrc/M^2
    let Vscale := max 1 (Uband*(N:ℝ)/(Q:ℝ))
    (0 < d) → (0 ≤ Wmax) → (Wmax ≤ 1/4) → (2*Usrc*Wmax ≤ csrc/64) →
    (0 < Tsrc) →
    (0 < T) →
    (0 < M) →
    (δ ≤ min (modelPhaseThirdLower σ) 1) →
    (Tsrc ≤ E*T) →
    (0 < Q) → (Uband ≤ 1) →
    (∀ i∈S, i.1∈Icc (1:ℝ) 2) →
    (∀ i∈S, z i∈Icc M (2*M)) →
    (∀ w, 0 < w → ContDiffAt ℝ ∞ Fsrc w) →
    (∀ w∈Icc (1/2:ℝ) 3, csrc ≤ iteratedDeriv 5 Fsrc w) →
    (∀ w∈Icc (1/2:ℝ) 3, ∀ n, 1 ≤ n → n ≤ 7 → |iteratedDeriv n Fsrc w| ≤ Usrc) →
    (∀ w∈Icc (1/2:ℝ) 3,
      csrc ≤ |(iteratedDeriv 5 Fsrc w)^2-iteratedDeriv 4 Fsrc w*iteratedDeriv 6 Fsrc w|) →
    (∀ i∈S, (rat i).den ≤ Q ∧ Q ≤ 2*(rat i).den) →
    (∀ i∈S, ((rat i).den:ℤ) ∣ (rat i).num*v i-1) →
    (∀ w∈Icc (1/2:ℝ) 3, iteratedDeriv 4 Fsrc w ≤ -csrc) →
    (2 ≤ M) →
    (0 < N) →
    (0 < Jsep) → (Jsep ≤ M) → ((N:ℝ) ≤ M) → (Wmax*Jsep ≤ 1) →
    ((Q:ℝ)*(N:ℝ) ≤ (K₀:ℝ)*R^2) →
    (∀ i∈S, N ≤ Nlen i ∧ Nlen i ≤ 3*N ∧
      round (z i)+(Nlen i:ℤ)=Z i.1+(N:ℤ)*i.2+2*(N:ℤ)) →
    (∀ i∈S, ∀ j∈S, i.1≠j.1 → 1 ≤ Jsep*|i.1-j.1|) →
    (∀ y∈S.image Prod.fst,
      0 ≤ rshift y ∧ 0 ≤ sshift y ∧ rshift y*sshift y=d*y ∧ rshift y+sshift y ≤ Wmax) →
    let Φ := fun y u =>
      (Fsrc u-Fsrc (u+rshift y)-Fsrc (u+sshift y)+Fsrc (u+rshift y+sshift y))/d
    let Fmodel := fun (i : ℝ × ℤ) u => (Tsrc/T)*Φ i.1 u
    (∀ i∈S, Expdb.IsApproximateModelPhaseFunction (Fmodel i) σ 4 δ) →
    let f := fun p w => Tsrc*Φ p (w/M)
    (∀ i∈S, iteratedDeriv 2 (f (i.1)) (z i)/2=(rat i:ℝ)) →
    (∀ i∈S, 1 ≤ Nlen i ∧ (rat i).den ≤ Nlen i ∧
      1 ≤ (iteratedDeriv 3 (f (i.1)) (round (z i))/6)*((rat i).den:ℝ)^2*Nlen i) →
    (∀ i∈S, 7*((iteratedDeriv 3 (f (i.1)) (round (z i))/6)*
      ((rat i).den:ℝ)*(Nlen i:ℝ)^2) ≤ K₀) →

    (1 ≤ R) → (R ≤ M) → (T*(N:ℝ)*R^2=M^3) →
    (∀ i∈S, M ≤ A i.1) → (∀ i∈S, A i.1+W i.1 ≤ 2*M) →
    let xlocal := fun i : ℝ × ℤ => z i-(A i.1:ℝ)
    (∀ i∈S, xlocal i∈Ioo (1/2:ℝ) (W i.1-1/2)) →
    (∀ i∈S, gap i∈Gaps) →
    (∀ ab∈Gaps, (vRef ab)*(r ab)-(e ab)*(s ab)=1) →
    (∀ ab∈Gaps, ((0:ℝ) < (r ab) ∧ ((e ab):ℝ)/(r ab)=ab.1) ∨
      (((r ab):ℝ) < 0 ∧ ((e ab):ℝ)/(r ab)=ab.2)) →
    (0 < Bcut) → (∀ ab∈Gaps, (s ab) ≠ 0) →
    (∀ ab∈Gaps, ((e ab):ℝ)/(r ab)∈Refs) →
    (∀ ab∈Gaps, ((vRef ab):ℝ)/(s ab)∈Refs) →
    (∀ a∈Refs, ∀ b∈Refs, a ≠ b → ((Uref:ℝ)/R^2)/4 < |a-b|) →
    (∀ i∈S, xlocal i-(56*(Uref:ℝ)/κ)*(N:ℝ)∈Ioo (1/2:ℝ) (W i.1-1/2)) →
    (∀ i∈S, xlocal i+(56*(Uref:ℝ)/κ)*(N:ℝ)∈Ioo (1/2:ℝ) (W i.1-1/2)) →
    (1 ≤ Uref) →
    (2+168/κ ≤ Bselect) → (7*Bcut ≤ κ*Bselect) →
    (Bselect^2*(Uref:ℝ)^3*R^2 ≤ (N:ℝ)^2) →
    (∀ ab∈Gaps, R^2 ≤ ((r ab):ℝ)^2*(Uref:ℝ)) →
    (∀ ab∈Gaps, ab.2-ab.1 ≤ 7*(Uref:ℝ)/(2*R^2)) →
    (R ≤ (Q:ℝ)) →
    ((Uref:ℝ) ≤ ((N:ℝ)/(Q:ℝ))^((2:ℝ)/3)/Bselect) →
    ((N:ℝ)^10 ≤ M^3*R^7) →
    (∀ i∈S, (rat i:ℝ)∈Icc (gap i).1 (gap i).2) →
    (∀ ab∈Gaps, ab.1∈Refs ∧ ab.2∈Refs ∧ ab.1 < ab.2 ∧
      ∀ t∈Refs, ¬(ab.1 < t ∧ t < ab.2)) →
    (Q:ℝ) ≤ (N:ℝ) →
    ((N:ℝ)^2 ≤ M ∨ (1 ≤ M ∧ (N:ℝ) ≤ T ∧ R^2 ≤ T)) → (Uref:ℝ) ≤ R^2 →
    (∀ ab∈Gaps, |((r ab):ℝ)| ≤ 4*R^2/(Uref:ℝ)) →
    (∀ ab∈Gaps, |((s ab):ℝ)| ≤ 4*R^2/(Uref:ℝ)) →
    (∀ ab∈Gaps, |((e ab):ℝ)| ≤
      (3*Jref*T/(2*σ*M^2)+1)*(4*R^2/(Uref:ℝ))) →
    (∀ ab∈Gaps, |((vRef ab):ℝ)| ≤
      (3*Jref*T/(2*σ*M^2)+1)*(4*R^2/(Uref:ℝ))) →
    let Cphys := σ*(σ+1)+1
    let c := κ/6
    let J := Cphys/6
    let B := max 1 (max (2*Real.sqrt J) (8*J*Real.sqrt J/(3*c)))
    B*R^2/(N:ℝ)^2 ≤ 1/2 →
    (N:ℝ) ≤ R^2 → R ≤ (N:ℝ) → (N:ℝ)^3 ≤ M*R^2 →
    2*R^2 ≤ (Q:ℝ)*(N:ℝ) →
    let H := (N:ℝ)/(Cphys+2)
    2 ≤ (N:ℝ) →
    (∀ i∈S, xlocal i-H∈Ioo (1/2:ℝ) (W i.1-1/2)) →
    (∀ i∈S, xlocal i+H∈Ioo (1/2:ℝ) (W i.1-1/2)) →
    let ε := κ/(16*(Cphys+2)*R^2)
    (∀ i∈S, |(anchor i:ℝ)-(rat i:ℝ)| ≤ ε) →
    (∀ i∈S, 256*((anchor i).den:ℝ) ≤ (Q:ℝ)/3) →
    (∀ i∈S, 256 ≤ (2*ε)*((Q:ℝ)/3)*(anchor i).den) →
    let narrow := fun (i : ℝ × ℤ) =>
      (⌊((rat i).den:ℝ)/(θ*((Q:ℝ)/2))⌋,
       ⌊((rat i).num:ℝ)/(θ*(lambda*(Q:ℝ)/2))⌋)
    let qell := fun (i : ℝ × ℤ) => ((rat i).den:ℝ)*deriv (f (i.1)) (round (z i))
    let V := S ×ˢ (Finset.univ : Finset (Fin 2))
    let offset := fun ip : (ℝ × ℤ) × Fin 2 => ⌊qell ip.1⌋+(ip.2:ℕ)-round (qell ip.1)
    let color := fun ip : (ℝ × ℤ) × Fin 2 => (narrow ip.1,offset ip)
    let NarrowCap := (4/θ+3)*(8*Usrc/(csrc*θ)+3)
    let Cap := 3*NarrowCap

    let q := fun (i : ℝ × ℤ) => (rat i).den
    let μ := fun (i : ℝ × ℤ) => iteratedDeriv 3 (f (i.1)) (round (z i))/6
    let b := fun ip : (ℝ × ℤ) × Fin 2 => (⌊qell ip.1⌋+(ip.2:ℕ) : ℤ)
    let tau := fun ip : (ℝ × ℤ) × Fin 2 => ((b ip:ℝ)-qell ip.1)/2
    let dual := fun (i : ℝ × ℤ) => -2*μ i*(Real.sqrt (2/(3*μ i*(q i:ℝ))))^3
    let x := fun ip : (ℝ × ℤ) × Fin 2 =>
      (![-(v ip.1:ℝ)*b ip/q ip.1,-(v ip.1:ℝ)/q ip.1,
        dual ip.1,3*dual ip.1*tau ip/2] : Fin 4 → ℝ)
    let Fiber := fun key => V.filter (fun ip => color ip=key)
    let μ₀ := csrc*Tsrc/(12*M^3)
    let U₀ := Usrc*Tsrc/(2*M^3)
    let Δtype := (16*U₀/μ₀)*Real.sqrt (U₀*(Q:ℝ)^3)*Real.sqrt K₀/(6*(K₀:ℝ)^2)
    let C₂ := modelPhaseJetCoefficient σ 2+δ
    let C₃ := modelPhaseJetCoefficient σ 3+δ
    let Ct := C₂/2+5*C₃/12
    let Cc := C₂/κ+C₃/(2*κ)
    let Δ := (37*B/2+16*B*Cc+2*Ct+2*Cc)*(Q:ℝ)/(N:ℝ)
    let Ccurv := (4/κ)*(B+2*quarticReciprocalConstant σ δ)
    let D := Δ+quarticNonlinearResidualConstant σ δ*(2*(Q:ℝ))/(N:ℝ)
    let Kres := 4*(37*B/2+16*B*Cc+2*Ct+2*Cc+
      2*quarticNonlinearResidualConstant σ δ)/κ
    let Esize := κ/(16*(Cphys+2))
    let Dbase := 37*B/2+16*B*Cc+2*Ct+2*Cc+2*quarticNonlinearResidualConstant σ δ
    let Tbase := (2/κ)*(B+2*quarticReciprocalConstant σ δ)
    2*3840*128^2*105*(Dbase+64*Tbase*Esize^2) ≤ Bselect*Esize →
    D ≤ 1/2 → Δ < 1/2 → 61*Ccurv*Cphys ≤ Bcut →
    let Lunit := 2*κ/Cphys
    let Gamma := Cphys/κ
    let Cthird := Gamma*(32*Kres+9*quarticReciprocalConstant σ δ)
    let Cpack := 64*Cphys*(Gamma^2*Cthird+Gamma*(modelPhaseJetCoefficient σ 3+δ)/κ)/κ
    let Cfirst := 128*Cphys*(Gamma^2*Cthird+Gamma*(modelPhaseJetCoefficient σ 3+δ)/κ)/κ^2
    let Cgap := 64*Cphys*(Gamma^2*B+Gamma*(modelPhaseJetCoefficient σ 3+δ)/κ)/κ
    let Cmain := 4*(2*Cfirst/Lunit^3)^((3:ℝ)⁻¹)+2
    let Ctail := 4*Cpack/Lunit^2+Cgap
    let Klarge := 60*588*(Uband/lambda)^2*Uband^2*(R^8/(N:ℝ)^4)*
      (Cmain*((Q:ℝ)/(Uband*(N:ℝ)))^((2:ℝ)/3)+Ctail/(Uref:ℝ))
    let Y := S.image Prod.fst
    ((V.image color).card:ℝ) ≤ Cap ∧
    ∀ k : ZMod K₀,
      (∑ ip∈V, ‖∑ j : ZMod K₀, ZMod.stdAddChar (-(j*k))*
        GafniTao.fordAdditiveCharacter (∑ d,x ip d*
          (![(j.val+1:ℝ),(j.val+1:ℝ)^2,(j.val+1:ℝ)^((3:ℝ)/2),
            Real.sqrt (j.val+1:ℝ)] : Fin 4 → ℝ) d)‖)^12 ≤
        C*(K₀:ℝ)^((12:ℝ)+εloss)*Cap^11*
          ∑ key∈V.image color, ((Fiber key).card:ℝ)^10*
            (Vscale*Dtype*(2+θ*(Uband+1/lambda))*(Y.card:ℝ)*(M/(N:ℝ))*(1+Δtype*Jsep)+
              (Y.card:ℝ)^2*Klarge*T^εloss) := by
  classical
  intro κ L θ
  have hL : 0 ≤ L := (double_difference_source_large_action_threshold hσ hcsrc hUsrc hE).1
  have hθ : 0 < θ := by dsimp only [θ]; positivity
  have hθmax : θ ≤ 1/24 := by
    dsimp only [θ]
    apply (div_le_iff₀ (by positivity)).mpr
    linarith only [hL]
  obtain ⟨Dtype,C,hDtype,hC,hsource⟩ :=
    double_difference_actual_joint_narrowed_sieve hcsrc hUsrc hL hεloss
  refine ⟨C,Dtype,hC,hDtype,?_⟩
  intro Jref hJref
  filter_upwards [eventually_model_tagged_large_entry_source_mass_clamped hσ hJref hεloss]
    with T hboundFn
  intro S Fsrc rshift sshift z rat v Nlen Q K₀ N instK R Jsep Z
    d Wmax Tsrc M δ Bcut Bselect Uref Refs Gaps A W gap anchor e r vRef s
    lambda Uband Vscale hd hw hwcap hsmallShift hTsrc hT hM hδ hsourceScale hQ hUbandCap
    hy hz hreg hlower hjets htests hden hinv hnegative hMtwo hN
    hJsep hJM hNM hwJ hmesh hgeometry hseparation hshifts Φ Fmodel hmodel f hlevel hminor hcomplete
    hR hRM hscale hA hW xlocal hx hgapMem
    hchart horientation hBcut hs hrefSet hparentSet hsep hwideL hwideU hUref
    hBselectSize hcutMargin hselectedWrap hreferenceDen hgapWidth hRQ
    hselectedUpper hscaleTen hfamilyGap hgap hQN hNsqM hUR
    hrHeight hsHeight heHeight hvHeight Cphys c J B hsmall hNR hRN hNcube hminscale
    H hNtwo hLeft hRight ε hanchor hcut hcount
    narrow qell V offset color NarrowCap Cap q μ b tau dual x Fiber μ₀ U₀ Δtype
    C₂ C₃ Ct Cc Δ Ccurv D Kres Esize Dbase Tbase hsize hD hΔ hBsize
    Lunit Gamma Cthird Cpack Cfirst Cgap Cmain Ctail Klarge Y
  have hVscale : 1 ≤ Vscale := le_max_left _ _
  have hlambda : 0 < lambda := by dsimp only [lambda]; positivity
  have hUband : 0 < Uband := by dsimp only [Uband]; positivity
  have hcurv i (hi : i∈S) : lambda ≤ |(rat i:ℝ)| ∧ |(rat i:ℝ)| ≤ Uband := by
    have hsdata := hshifts i.1 (Finset.mem_image_of_mem Prod.fst hi)
    have hpar := hy i hi
    have hprodpos : 0 < rshift i.1*sshift i.1 := by
      rw [hsdata.2.2.1]
      exact mul_pos hd (by linarith only [hpar.1])
    have hrp : 0 < rshift i.1 := by nlinarith only [hsdata.1,hsdata.2.1,hprodpos]
    have hsp : 0 < sshift i.1 := by nlinarith only [hsdata.1,hsdata.2.1,hprodpos]
    rw [←hlevel i hi]
    exact double_difference_physical_curvature_band Fsrc (hz i hi) hpar hrp hsp
      hd hcsrc hUsrc hTsrc hM hsdata.2.2.1 (hsdata.2.2.2.trans hwcap)
      hreg hnegative (fun u hu => hjets u hu 4 (by norm_num) (by norm_num))
  obtain ⟨_hNarrowCard,_hHolder,Mat,hglobal,_hclass,htype,htri,hcard,hfourier,_hnarrow⟩ :=
    hsource S Fsrc rshift sshift z rat v Nlen Z Q K₀ N d Wmax Tsrc M Jsep Nlen Vscale R
      hreg hlower hjets htests hnegative hd hw hwcap hsmallShift hTsrc hMtwo hN hQ
      hJsep hNM hJM hwJ hy hz hgeometry hseparation hshifts hlevel hden hinv
      hVscale hmesh hminor hcomplete
  let cloud := fun ip => (![Int.fract (x ip 0),Int.fract (x ip 1),
    x ip 2/Real.sqrt K₀,x ip 3/Real.sqrt K₀] : Fin 4 → ℝ)
  let radius : Fin 4 → ℝ :=
    ![1/(12*(K₀:ℝ)),1/(12*(K₀:ℝ)^2*Vscale),(1/(K₀:ℝ)^2)/12,(1/(K₀:ℝ))/12]
  let wideRadius : Fin 4 → ℝ :=
    ![1/(12*(K₀:ℝ)),1/(12*(K₀:ℝ)^2),(1/(K₀:ℝ)^2)/12,(1/(K₀:ℝ))/12]
  let Pall := (V ×ˢ V).filter (fun ij => ∀ a, |cloud ij.1 a-cloud ij.2 a| ≤ 2*radius a)
  let Pwide := (V ×ˢ V).filter (fun ij => ∀ a, |cloud ij.1 a-cloud ij.2 a| ≤ 2*wideRadius a)
  let Pairs := fun key => ((Fiber key) ×ˢ (Fiber key)).filter
    (fun ij => ∀ a, |cloud ij.1 a-cloud ij.2 a| ≤ 2*radius a)
  let Etype := Pwide.filter (fun ij =>
    narrow ij.1.1=narrow ij.2.1 ∧
      ((Mat ij 0=1 ∧ Mat ij 1=0 ∧ Mat ij 2=0 ∧ Mat ij 3=1) ∨
       (Mat ij 1≠0 ∧ Mat ij 2≠0 ∧ |(Mat ij 2:ℝ)| *Uband ≤ L)))
  let Etri := Pwide.filter (fun ij =>
    narrow ij.1.1=narrow ij.2.1 ∧ (Mat ij 2=0 ∨ Mat ij 1=0))
  let Large := fun key => (Pairs key).filter (fun ij =>
    Mat ij 1≠0 ∧ Mat ij 2≠0 ∧ L < |(Mat ij 2:ℝ)| *Uband)
  let phaseFiber := fun key (ab : ℝ × ℝ) =>
    (Large key).filter (fun ij => ij.1.1.1=ab.1 ∧ ij.2.1.1=ab.2)
  have hRadius a : radius a ≤ wideRadius a := by
    have hKpos : (0:ℝ) < K₀ := by exact_mod_cast NeZero.pos K₀
    fin_cases a
    · exact le_rfl
    · change 1/(12*(K₀:ℝ)^2*Vscale) ≤ 1/(12*(K₀:ℝ)^2)
      apply one_div_le_one_div_of_le (by positivity)
      exact le_mul_of_one_le_right (by positivity) hVscale
    · exact le_rfl
    · exact le_rfl
  have hsub : Pall ⊆ Pwide := by
    intro ij hij
    obtain ⟨hh,hn⟩ := Finset.mem_filter.mp hij
    exact Finset.mem_filter.mpr ⟨hh,fun a => (hn a).trans
      (mul_le_mul_of_nonneg_left (hRadius a) (by norm_num))⟩
  have hPairData key ij (hij : ij∈Pairs key) :
      ij.1∈V ∧ ij.2∈V ∧ color ij.1=key ∧ color ij.2=key ∧ ij∈Pall := by
    have hp := Finset.mem_product.mp (Finset.mem_filter.mp hij).1
    have h1 := Finset.mem_filter.mp hp.1
    have h2 := Finset.mem_filter.mp hp.2
    exact ⟨h1.1,h2.1,h1.2,h2.2,
      Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨h1.1,h2.1⟩,
        (Finset.mem_filter.mp hij).2⟩⟩
  have hMatData ij (hij : ij∈Pall) :
      Mat ij 0*Mat ij 3-Mat ij 1*Mat ij 2=1 ∧
      (Mat ij 2:ℝ)*(rat ij.1.1:ℝ)+Mat ij 3=(q ij.2.1:ℝ)/q ij.1.1 ∧
      ((Mat ij 0:ℝ)*(rat ij.1.1:ℝ)+Mat ij 1)/
        ((Mat ij 2:ℝ)*(rat ij.1.1:ℝ)+Mat ij 3)=(rat ij.2.1:ℝ) ∧
      |(Mat ij 2:ℝ)| ≤ (Q:ℝ)^2/(6*(K₀:ℝ)^2) := by
    have hg := hglobal ij (hsub hij)
    have hp := Finset.mem_product.mp (Finset.mem_filter.mp hij).1
    have hl1 := hlevel ij.1.1 (Finset.mem_product.mp hp.1).1
    have hl2 := hlevel ij.2.1 (Finset.mem_product.mp hp.2).1
    have ht : (Mat ij 2:ℝ)*(iteratedDeriv 2 (f ij.1.1.1) (z ij.1.1)/2)+Mat ij 3=
        (q ij.2.1:ℝ)/q ij.1.1 := hg.2.1
    have hm : ((Mat ij 0:ℝ)*(iteratedDeriv 2 (f ij.1.1.1) (z ij.1.1)/2)+Mat ij 1)/
        ((Mat ij 2:ℝ)*(iteratedDeriv 2 (f ij.1.1.1) (z ij.1.1)/2)+Mat ij 3)=
        iteratedDeriv 2 (f ij.2.1.1) (z ij.2.1)/2 := hg.2.2.2.2.1
    rw [hl1] at ht
    rw [hl1,hl2] at hm
    exact ⟨hg.1,ht,hm,hg.2.2.2.2.2.1⟩
  have hY y (hym : y∈Y) :
      y∈Icc (1:ℝ) 2 ∧ M ≤ A y ∧ A y+W y ≤ 2*M ∧
      Expdb.IsApproximateModelPhaseFunction (fun u => (Tsrc/T)*Φ y u) σ 4 δ := by
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hym
    exact ⟨hy i hi,hA i hi,hW i hi,hmodel i hi⟩
  have hLargeData key ij (hij : ij∈Large key) :
      Mat ij 2≠0 ∧ 8*Uband ≤ |(Mat ij 2:ℝ)| *lambda^2 ∧
        64*(modelPhaseJetCoefficient σ 3+δ)*M^2 ≤ |(Mat ij 2:ℝ)| *κ^2*T := by
    have hd := (Finset.mem_filter.mp hij).2
    have hb := (double_difference_source_large_action_threshold hσ hcsrc hUsrc hE).2
      hTsrc hT hM hsourceScale (hδ.trans (min_le_right _ _)) hd.2.2
    exact ⟨hd.2.1,hb.2.1,hb.2.2⟩
  have hphaseBound key ab (hab : ab∈Y ×ˢ Y) :
      Vscale*((phaseFiber key ab).card:ℝ) ≤ Klarge*T^εloss := by
    let P := phaseFiber key ab
    let yp : Fin 2 → ℝ := ![ab.1,ab.2]
    let ip := fun p : ((ℝ × ℤ) × Fin 2) × ((ℝ × ℤ) × Fin 2) =>
      (![p.1,p.2] : Fin 2 → (ℝ × ℤ) × Fin 2)
    let xp := fun p : ((ℝ × ℤ) × Fin 2) × ((ℝ × ℤ) × Fin 2) =>
      (![z (ab.1,p.1.1.2),z (ab.2,p.2.1.2)] : Fin 2 → ℝ)
    let fp := fun i => f (yp i)
    let Ap := fun i => A (yp i)
    let Wp := fun i => W (yp i)
    let rp := fun p i => rat (ip p i).1
    let vp := fun p i => v (ip p i).1
    let pp := fun p i => (ip p i).2
    let qp := fun p i => (rp p i).den
    let mup := fun p i => iteratedDeriv 3 (fp i) (round (xp p i))/6
    let ellp := fun p i => deriv (fp i) (round (xp p i))
    let bp := fun p i => (⌊(qp p i:ℝ)*ellp p i⌋+(pp p i:ℕ) : ℤ)
    let crp := fun p i => round ((qp p i:ℝ)*ellp p i)
    let taup := fun p i => ((bp p i:ℝ)-(qp p i:ℝ)*ellp p i)/2
    let dualp := fun p i => -2*mup p i*(Real.sqrt (2/(3*mup p i*(qp p i:ℝ))))^3
    let cloudp := fun p i => (![Int.fract (-(vp p i:ℝ)*bp p i/qp p i),
      Int.fract (-(vp p i:ℝ)/qp p i),dualp p i/Real.sqrt K₀,
      (3*dualp p i*taup p i/2)/Real.sqrt K₀] : Fin 4 → ℝ)
    have hLarge p (hp : p∈P) : p∈Large key := (Finset.mem_filter.mp hp).1
    have hPairs p (hp : p∈P) : p∈Pairs key := (Finset.mem_filter.mp (hLarge p hp)).1
    have hPhase p (hp : p∈P) : p.1.1.1=ab.1 ∧ p.2.1.1=ab.2 :=
      (Finset.mem_filter.mp hp).2
    have hSlot p (hp : p∈P) i : ip p i∈V := by
      fin_cases i
      · exact (hPairData key p (hPairs p hp)).1
      · exact (hPairData key p (hPairs p hp)).2.1
    have hS p (hp : p∈P) i : (ip p i).1∈S :=
      (Finset.mem_product.mp (hSlot p hp i)).1
    have hColor p (hp : p∈P) i : color (ip p i)=key := by
      fin_cases i
      · exact (hPairData key p (hPairs p hp)).2.2.1
      · exact (hPairData key p (hPairs p hp)).2.2.2.1
    have hYP p (hp : p∈P) i : yp i=(ip p i).1.1 := by
      fin_cases i
      · exact (hPhase p hp).1.symm
      · exact (hPhase p hp).2.symm
    have hPointA p (hp : p∈P) : (ab.1,p.1.1.2)=p.1.1 :=
      Prod.ext (hPhase p hp).1.symm rfl
    have hPointB p (hp : p∈P) : (ab.2,p.2.1.2)=p.2.1 :=
      Prod.ext (hPhase p hp).2.symm rfl
    have hData p (hp : p∈P) i :
        xp p i=z (ip p i).1 ∧
        (∀ n, iteratedDeriv n (fp i) (xp p i)=
          iteratedDeriv n (f (ip p i).1.1) (z (ip p i).1)) ∧
        bp p i-crp p i = offset (ip p i) ∧ cloudp p i=cloud (ip p i) := by
      rcases p with ⟨⟨⟨ya,n⟩,pa⟩,⟨⟨yb,m⟩,pb⟩⟩
      have he := hPhase _ hp
      dsimp only at he
      rcases he with ⟨rfl,rfl⟩
      fin_cases i <;> exact ⟨rfl,fun _ => rfl,rfl,rfl⟩
    have hLoc p (hp : p∈P) i : xp p i-(Ap i:ℝ)=xlocal (ip p i).1 := by
      change xp p i-(A (yp i):ℝ)=z (ip p i).1-(A (ip p i).1.1:ℝ)
      rw [(hData p hp i).1,hYP p hp i]
    have hWp p (hp : p∈P) i : Wp i=W (ip p i).1.1 :=
      congrArg W (hYP p hp i)
    have hNear p (hp : p∈P) d :
        |cloudp p 0 d-cloudp p 1 d| ≤ 2*wideRadius d := by
      rw [(hData p hp 0).2.2.2,(hData p hp 1).2.2.2]
      exact ((Finset.mem_filter.mp (hPairs p hp)).2 d).trans
        (mul_le_mul_of_nonneg_left (hRadius d) (by norm_num))
    have hNearNarrow p (hp : p∈P) :
        |cloudp p 0 1-cloudp p 1 1| ≤ 1/(6*(K₀:ℝ)^2*Vscale) := by
      rw [(hData p hp 0).2.2.2,(hData p hp 1).2.2.2]
      have hn := (Finset.mem_filter.mp (hPairs p hp)).2 (1 : Fin 4)
      change |cloud p.1 1-cloud p.2 1| ≤ 2*(1/(12*(K₀:ℝ)^2*Vscale)) at hn
      convert hn using 1
      ring
    have hYa := hY ab.1 (Finset.mem_product.mp hab).1
    have hYb := hY ab.2 (Finset.mem_product.mp hab).2
    have hAp i : M ≤ Ap i := by
      fin_cases i
      · exact hYa.2.1
      · exact hYb.2.1
    have hWpair i : (Ap i:ℝ)+Wp i ≤ 2*M := by
      fin_cases i
      · exact hYa.2.2.1
      · exact hYb.2.2.1
    let Fp := fun i u => (Tsrc/T)*Φ (yp i) u
    have hFp i : Expdb.IsApproximateModelPhaseFunction (Fp i) σ 4 δ := by
      fin_cases i
      · exact hYa.2.2.2
      · exact hYb.2.2.2
    have hFpEq i : (fun w => T*Fp i (w/M))=fp i := by
      funext w
      dsimp only [Fp,fp,f]
      field_simp
    have hGeoA p (hp : p∈P) :
        N ≤ Nlen (ab.1,p.1.1.2) ∧ Nlen (ab.1,p.1.1.2) ≤ 3*N ∧
        round (z (ab.1,p.1.1.2))+(Nlen (ab.1,p.1.1.2):ℤ)=
          Z ab.1+(N:ℤ)*p.1.1.2+2*(N:ℤ) := by
      have hh := hgeometry p.1.1 (hS p hp 0)
      rw [←hPointA p hp] at hh
      exact hh
    have hGeoB p (hp : p∈P) :
        N ≤ Nlen (ab.2,p.2.1.2) ∧ Nlen (ab.2,p.2.1.2) ≤ 3*N ∧
        round (z (ab.2,p.2.1.2))+(Nlen (ab.2,p.2.1.2):ℤ)=
          Z ab.2+(N:ℤ)*p.2.1.2+2*(N:ℤ) := by
      have hh := hgeometry p.2.1 (hS p hp 1)
      rw [←hPointB p hp] at hh
      exact hh

    have hh := hboundFn Fp ab.1 ab.2 Uref Refs Gaps (Bselect:=Bselect)
      P Mat (fun p => gap p.1.1) Q K₀ N
      (fun n => z (ab.1,n)) (fun n => z (ab.2,n))
      (fun n => Nlen (ab.1,n)) (fun n => Nlen (ab.2,n)) (Z ab.1) (Z ab.2)
      rp vp pp (fun p => anchor p.1.1) e r vRef s
      (δ:=δ) (M:=M) (R:=R) (base:=0) (Bcut:=Bcut)
      (lambda:=lambda) (Uband:=Uband) (θ:=θ) Ap (W:=Wp)
      hPhase
      (fun p hp => by
        change 0 ≤ xp p 0-(Ap 0:ℝ)
        rw [hLoc p hp 0]
        exact le_of_lt (lt_trans (by norm_num) (hx _ (hS p hp 0)).1))
      (fun p hp => hgapMem _ (hS p hp 0))
      hGeoA hGeoB hδ hFp hT hM
      (Nat.cast_pos.mpr hN) hR hRM hQ hscale hmesh hAp hWpair
      (fun p hp i => by
        change xp p i-(Ap i:ℝ)∈Ioo (1/2:ℝ) (Wp i-1/2)
        rw [hLoc p hp i,hWp p hp i]
        exact hx _ (hS p hp i))
      (fun p hp i => hden _ (hS p hp i))
      hlambda hUband hUbandCap hθ hθmax
      (fun p hp i => hcurv _ (hS p hp i))
      (fun p hp i => hinv _ (hS p hp i))
      hchart horientation hBcut hs hrefSet hparentSet hsep
      (fun p hp i => by
        change xp p i-(Ap i:ℝ)-(56*(Uref:ℝ)/κ)*(N:ℝ)∈Ioo (1/2:ℝ) (Wp i-1/2)
        rw [hLoc p hp i,hWp p hp i]
        exact hwideL _ (hS p hp i))
      (fun p hp i => by
        change xp p i-(Ap i:ℝ)+(56*(Uref:ℝ)/κ)*(N:ℝ)∈Ioo (1/2:ℝ) (Wp i-1/2)
        rw [hLoc p hp i,hWp p hp i]
        exact hwideU _ (hS p hp i))
      hUref hBselectSize hcutMargin hselectedWrap hreferenceDen hgapWidth hRQ
      hselectedUpper hscaleTen (fun p hp => hfamilyGap _ (hS p hp 0))
      (fun p hp => (hLargeData key p (hLarge p hp)).1)
      (fun p hp => (hLargeData key p (hLarge p hp)).2.2)
      (fun p hp => (hLargeData key p (hLarge p hp)).2.1)
      hgap hQN hNsqM hUR hrHeight hsHeight heHeight hvHeight
      (fun p hp => by
        have he := congrArg Prod.fst ((hColor p hp 0).trans (hColor p hp 1).symm)
        change (⌊((rp p 0).den:ℝ)/(θ*((Q:ℝ)/2))⌋,
            ⌊((rp p 0).num:ℝ)/(θ*(lambda*(Q:ℝ)/2))⌋)=
          (⌊((rp p 1).den:ℝ)/(θ*((Q:ℝ)/2))⌋,
            ⌊((rp p 1).num:ℝ)/(θ*(lambda*(Q:ℝ)/2))⌋) at he
        simpa only [mul_div_assoc] using he)
      (fun p hp i => by
        change iteratedDeriv 2 (fun w => T*Fp i (w/M)) (xp p i)/2=(rp p i:ℝ)
        rw [hFpEq]
        rw [(hData p hp i).2.1 2]
        exact hlevel _ (hS p hp i))
      (fun p hp => by
        simp only [hFpEq]
        change bp p 0-crp p 0=bp p 1-crp p 1
        rw [(hData p hp 0).2.2.1,(hData p hp 1).2.2.1]
        exact congrArg Prod.snd ((hColor p hp 0).trans (hColor p hp 1).symm))
      (fun p hp a => by simpa only [hFpEq] using hNear p hp a)
      (fun p hp => by simpa only [hFpEq] using hNearNarrow p hp)
      hsmall hNR hRN hNcube hminscale
      (fun p hp => (hMatData p (hPairData key p (hPairs p hp)).2.2.2.2).1)
      (fun p hp => (hMatData p (hPairData key p (hPairs p hp)).2.2.2.2).2.1)
      (fun p hp => (hMatData p (hPairData key p (hPairs p hp)).2.2.2.2).2.2.1)
      (fun p hp => (hMatData p (hPairData key p (hPairs p hp)).2.2.2.2).2.2.2)
      hNtwo
      (fun p hp i => by
        change xp p i-(Ap i:ℝ)-H∈Ioo (1/2:ℝ) (Wp i-1/2)
        rw [hLoc p hp i,hWp p hp i]
        exact hLeft _ (hS p hp i))
      (fun p hp i => by
        change xp p i-(Ap i:ℝ)+H∈Ioo (1/2:ℝ) (Wp i-1/2)
        rw [hLoc p hp i,hWp p hp i]
        exact hRight _ (hS p hp i))
      (fun p hp => hanchor _ (hS p hp 0))
      (fun p hp => hcut _ (hS p hp 0))
      (fun p hp => hcount _ (hS p hp 0))
      hsize hD hΔ hBsize
    exact hh
  have hLargeMass key : Vscale*((Large key).card:ℝ) ≤ (Y.card:ℝ)^2*Klarge*T^εloss := by
    let phase := fun ij : ((ℝ × ℤ) × Fin 2) × ((ℝ × ℤ) × Fin 2) =>
      (ij.1.1.1,ij.2.1.1)
    have hmaps : Set.MapsTo phase (Large key : Set _) (Y ×ˢ Y : Finset _) := by
      intro ij hij
      have hd := hPairData key ij (Finset.mem_filter.mp hij).1
      exact Finset.mem_product.mpr
        ⟨Finset.mem_image_of_mem Prod.fst (Finset.mem_product.mp hd.1).1,
          Finset.mem_image_of_mem Prod.fst (Finset.mem_product.mp hd.2.1).1⟩
    have heq ab : (Large key).filter (fun ij => phase ij=ab)=phaseFiber key ab := by
      rcases ab with ⟨a,b⟩
      ext ij
      simp only [phaseFiber,Finset.mem_filter,phase,Prod.mk.injEq]
    have hcards : ((Large key).card:ℝ)=
        ∑ ab∈Y ×ˢ Y, ((phaseFiber key ab).card:ℝ) := by
      have hh := Finset.card_eq_sum_card_fiberwise hmaps
      simp only [heq] at hh
      exact_mod_cast hh
    rw [hcards,Finset.mul_sum]
    calc
      _ ≤ ∑ _ab∈Y ×ˢ Y, Klarge*T^εloss :=
        Finset.sum_le_sum (fun ab hab => hphaseBound key ab hab)
      _ = _ := by
        simp only [Finset.sum_const,Finset.card_product,nsmul_eq_mul,Nat.cast_mul]
        ring
  let smallMass := Dtype*(2+θ*(Uband+1/lambda))*(Y.card:ℝ)*(M/(N:ℝ))*(1+Δtype*Jsep)
  have hPairCard key : ((Pairs key).card:ℝ) ≤ smallMass+((Large key).card:ℝ) := by
    have hcover : Pairs key ⊆ (Etype ∪ Etri) ∪ Large key := by
      intro ij hij
      have hp := hPairData key ij hij
      have hkey : narrow ij.1.1=narrow ij.2.1 :=
        congrArg Prod.fst (hp.2.2.1.trans hp.2.2.2.1.symm)
      by_cases htr : Mat ij 2=0 ∨ Mat ij 1=0
      · exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_filter.mpr
          ⟨hsub hp.2.2.2.2,hkey,htr⟩))
      · have hn : Mat ij 1≠0 ∧ Mat ij 2≠0 := by tauto
        by_cases hact : |(Mat ij 2:ℝ)| *Uband ≤ L
        · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_filter.mpr
            ⟨hsub hp.2.2.2.2,hkey,Or.inr ⟨hn.1,hn.2,hact⟩⟩))
        · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hij,hn.1,hn.2,lt_of_not_ge hact⟩)
    have hh : ((Pairs key).card:ℝ) ≤ (Etype.card:ℝ)+(Etri.card:ℝ)+((Large key).card:ℝ) := by
      exact_mod_cast (Finset.card_le_card hcover).trans
        ((Finset.card_union_le _ _).trans (Nat.add_le_add_right (Finset.card_union_le _ _) _))
    have ht : (Etype.card:ℝ) ≤ Dtype*(Y.card:ℝ)*(M/(N:ℝ))*(1+Δtype*Jsep) := htype
    have hu : (Etri.card:ℝ) ≤
        Dtype*(1+θ*(Uband+1/lambda))*(Y.card:ℝ)*(M/(N:ℝ))*(1+Δtype*Jsep) := htri
    have hm : Dtype*(Y.card:ℝ)*(M/(N:ℝ))*(1+Δtype*Jsep)+
        Dtype*(1+θ*(Uband+1/lambda))*(Y.card:ℝ)*(M/(N:ℝ))*(1+Δtype*Jsep)=smallMass := by
      dsimp only [smallMass]
      ring
    exact hh.trans ((add_le_add (add_le_add ht hu) le_rfl).trans_eq (by rw [hm]))
  have hPairMass key : Vscale*((Pairs key).card:ℝ) ≤
      Vscale*smallMass+(Y.card:ℝ)^2*Klarge*T^εloss := by
    calc
      _ ≤ Vscale*(smallMass+((Large key).card:ℝ)) :=
        mul_le_mul_of_nonneg_left (hPairCard key) (zero_le_one.trans hVscale)
      _ = Vscale*smallMass+Vscale*((Large key).card:ℝ) := by ring
      _ ≤ _ := add_le_add le_rfl (hLargeMass key)
  have hCap : 0 ≤ Cap := (Nat.cast_nonneg _).trans hcard
  refine ⟨hcard,?_⟩
  intro k
  calc
    _ ≤ C*Vscale*(K₀:ℝ)^((12:ℝ)+εloss)*Cap^11*
        ∑ key∈V.image color, ((Fiber key).card:ℝ)^10*((Pairs key).card:ℝ) := hfourier k
    _ = C*(K₀:ℝ)^((12:ℝ)+εloss)*Cap^11*
        ∑ key∈V.image color, ((Fiber key).card:ℝ)^10*(Vscale*((Pairs key).card:ℝ)) := by
      rw [show C*Vscale*(K₀:ℝ)^((12:ℝ)+εloss)*Cap^11=
        C*(K₀:ℝ)^((12:ℝ)+εloss)*Cap^11*Vscale by ring,mul_assoc,Finset.mul_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro key _
      ring
    _ ≤ C*(K₀:ℝ)^((12:ℝ)+εloss)*Cap^11*
        ∑ key∈V.image color, ((Fiber key).card:ℝ)^10*
          (Vscale*smallMass+(Y.card:ℝ)^2*Klarge*T^εloss) :=
      mul_le_mul_of_nonneg_left
        (Finset.sum_le_sum (fun key _ =>
          mul_le_mul_of_nonneg_left (hPairMass key) (pow_nonneg (Nat.cast_nonneg _) 10)))
        (mul_nonneg (mul_nonneg hC.le (Real.rpow_nonneg (Nat.cast_nonneg _) _)) (pow_nonneg hCap 11))
    _ = _ := by
      dsimp only [smallMass]
      simp only [mul_assoc]

example
    {csrc Usrc E σ εloss : ℝ}
    (hcsrc : 0 < csrc) (hUsrc : 0 < Usrc)
    (hE : 0 < E) (hσ : 0 < σ) (hεloss : 0 < εloss) :
    let κ := modelPhaseThirdLower σ
    let L := max (32*Usrc^2/csrc^2)
      (64*(modelPhaseJetCoefficient σ 3+1)*Usrc*E/κ^2)
    let θ := 1/(8*(L+3))
    ∃ C Dtype : ℝ, 0 < C ∧ 0 < Dtype ∧
    ∀ {Jref : ℝ}, 0 ≤ Jref →
    ∀ᶠ T : ℝ in Filter.atTop, ∀ (S : Finset (ℝ × ℤ)) (Fsrc rshift sshift : ℝ → ℝ)
    (z : (ℝ × ℤ) → ℝ) (rat : (ℝ × ℤ) → ℚ) (v : (ℝ × ℤ) → ℤ) (Nlen : (ℝ × ℤ) → ℕ)
    (Q K₀ N : ℕ) [NeZero K₀] (R Jsep : ℝ) (Z : ℝ → ℤ)
    {d Wmax Tsrc M δ Bcut Bselect : ℝ}
    (Uref : ℕ) (Refs : Finset ℝ) (Gaps : Finset (ℝ × ℝ))
    (A : ℝ → ℤ) (W : ℝ → ℝ) (gap : (ℝ × ℤ) → ℝ × ℝ)
    (anchor : (ℝ × ℤ) → ℚ) (e r vRef s : ℝ × ℝ → ℤ),
    let lambda := csrc*Tsrc/(2*M^2)
    let Uband := Usrc*Tsrc/M^2
    let Vscale := max 1 (Uband*(N:ℝ)/(Q:ℝ))
    (0 < d) → (0 ≤ Wmax) → (Wmax ≤ 1/4) → (2*Usrc*Wmax ≤ csrc/64) →
    (0 < Tsrc) →
    (0 < T) →
    (0 < M) →
    (δ ≤ min (modelPhaseThirdLower σ) 1) →
    (Tsrc ≤ E*T) →
    (0 < Q) → (Uband ≤ 1) →
    (∀ i∈S, i.1∈Icc (1:ℝ) 2) →
    (∀ i∈S, z i∈Icc M (2*M)) →
    (∀ w, 0 < w → ContDiffAt ℝ ∞ Fsrc w) →
    (∀ w∈Icc (1/2:ℝ) 3, csrc ≤ iteratedDeriv 5 Fsrc w) →
    (∀ w∈Icc (1/2:ℝ) 3, ∀ n, 1 ≤ n → n ≤ 7 → |iteratedDeriv n Fsrc w| ≤ Usrc) →
    (∀ w∈Icc (1/2:ℝ) 3,
      csrc ≤ |(iteratedDeriv 5 Fsrc w)^2-iteratedDeriv 4 Fsrc w*iteratedDeriv 6 Fsrc w|) →
    (∀ i∈S, (rat i).den ≤ Q ∧ Q ≤ 2*(rat i).den) →
    (∀ i∈S, ((rat i).den:ℤ) ∣ (rat i).num*v i-1) →
    (∀ w∈Icc (1/2:ℝ) 3, iteratedDeriv 4 Fsrc w ≤ -csrc) →
    (2 ≤ M) →
    (0 < N) →
    (0 < Jsep) → (Jsep ≤ M) → ((N:ℝ) ≤ M) → (Wmax*Jsep ≤ 1) →
    ((Q:ℝ)*(N:ℝ) ≤ (K₀:ℝ)*R^2) →
    (∀ i∈S, N ≤ Nlen i ∧ Nlen i ≤ 3*N ∧
      round (z i)+(Nlen i:ℤ)=Z i.1+(N:ℤ)*i.2+2*(N:ℤ)) →
    (∀ i∈S, ∀ j∈S, i.1≠j.1 → 1 ≤ Jsep*|i.1-j.1|) →
    (∀ y∈S.image Prod.fst,
      0 ≤ rshift y ∧ 0 ≤ sshift y ∧ rshift y*sshift y=d*y ∧ rshift y+sshift y ≤ Wmax) →
    let Φ := fun y u =>
      (Fsrc u-Fsrc (u+rshift y)-Fsrc (u+sshift y)+Fsrc (u+rshift y+sshift y))/d
    let Fmodel := fun (i : ℝ × ℤ) u => (Tsrc/T)*Φ i.1 u
    (∀ i∈S, Expdb.IsApproximateModelPhaseFunction (Fmodel i) σ 4 δ) →
    let f := fun p w => Tsrc*Φ p (w/M)
    (∀ i∈S, iteratedDeriv 2 (f (i.1)) (z i)/2=(rat i:ℝ)) →
    (∀ i∈S, 1 ≤ Nlen i ∧ (rat i).den ≤ Nlen i ∧
      1 ≤ (iteratedDeriv 3 (f (i.1)) (round (z i))/6)*((rat i).den:ℝ)^2*Nlen i) →
    (∀ i∈S, 7*((iteratedDeriv 3 (f (i.1)) (round (z i))/6)*
      ((rat i).den:ℝ)*(Nlen i:ℝ)^2) ≤ K₀) →

    (1 ≤ R) → (R ≤ M) → (T*(N:ℝ)*R^2=M^3) →
    (∀ i∈S, M ≤ A i.1) → (∀ i∈S, A i.1+W i.1 ≤ 2*M) →
    let xlocal := fun i : ℝ × ℤ => z i-(A i.1:ℝ)
    (∀ i∈S, xlocal i∈Ioo (1/2:ℝ) (W i.1-1/2)) →
    (∀ i∈S, gap i∈Gaps) →
    (∀ ab∈Gaps, (vRef ab)*(r ab)-(e ab)*(s ab)=1) →
    (∀ ab∈Gaps, ((0:ℝ) < (r ab) ∧ ((e ab):ℝ)/(r ab)=ab.1) ∨
      (((r ab):ℝ) < 0 ∧ ((e ab):ℝ)/(r ab)=ab.2)) →
    (0 < Bcut) → (∀ ab∈Gaps, (s ab) ≠ 0) →
    (∀ ab∈Gaps, ((e ab):ℝ)/(r ab)∈Refs) →
    (∀ ab∈Gaps, ((vRef ab):ℝ)/(s ab)∈Refs) →
    (∀ a∈Refs, ∀ b∈Refs, a ≠ b → ((Uref:ℝ)/R^2)/4 < |a-b|) →
    (∀ i∈S, xlocal i-(56*(Uref:ℝ)/κ)*(N:ℝ)∈Ioo (1/2:ℝ) (W i.1-1/2)) →
    (∀ i∈S, xlocal i+(56*(Uref:ℝ)/κ)*(N:ℝ)∈Ioo (1/2:ℝ) (W i.1-1/2)) →
    (1 ≤ Uref) →
    (2+168/κ ≤ Bselect) → (7*Bcut ≤ κ*Bselect) →
    (Bselect^2*(Uref:ℝ)^3*R^2 ≤ (N:ℝ)^2) →
    (∀ ab∈Gaps, R^2 ≤ ((r ab):ℝ)^2*(Uref:ℝ)) →
    (∀ ab∈Gaps, ab.2-ab.1 ≤ 7*(Uref:ℝ)/(2*R^2)) →
    (R ≤ (Q:ℝ)) →
    ((Uref:ℝ) ≤ ((N:ℝ)/(Q:ℝ))^((2:ℝ)/3)/Bselect) →
    ((N:ℝ)^10 ≤ M^3*R^7) →
    (∀ i∈S, (rat i:ℝ)∈Icc (gap i).1 (gap i).2) →
    (∀ ab∈Gaps, ab.1∈Refs ∧ ab.2∈Refs ∧ ab.1 < ab.2 ∧
      ∀ t∈Refs, ¬(ab.1 < t ∧ t < ab.2)) →
    (Q:ℝ) ≤ (N:ℝ) →
    ((N:ℝ)^2 ≤ M ∨ (1 ≤ M ∧ (N:ℝ) ≤ T ∧ R^2 ≤ T)) → (Uref:ℝ) ≤ R^2 →
    (∀ ab∈Gaps, |((r ab):ℝ)| ≤ 4*R^2/(Uref:ℝ)) →
    (∀ ab∈Gaps, |((s ab):ℝ)| ≤ 4*R^2/(Uref:ℝ)) →
    (∀ ab∈Gaps, |((e ab):ℝ)| ≤
      (3*Jref*T/(2*σ*M^2)+1)*(4*R^2/(Uref:ℝ))) →
    (∀ ab∈Gaps, |((vRef ab):ℝ)| ≤
      (3*Jref*T/(2*σ*M^2)+1)*(4*R^2/(Uref:ℝ))) →
    let Cphys := σ*(σ+1)+1
    let c := κ/6
    let J := Cphys/6
    let B := max 1 (max (2*Real.sqrt J) (8*J*Real.sqrt J/(3*c)))
    B*R^2/(N:ℝ)^2 ≤ 1/2 →
    (N:ℝ) ≤ R^2 → R ≤ (N:ℝ) → (N:ℝ)^3 ≤ M*R^2 →
    2*R^2 ≤ (Q:ℝ)*(N:ℝ) →
    let H := (N:ℝ)/(Cphys+2)
    2 ≤ (N:ℝ) →
    (∀ i∈S, xlocal i-H∈Ioo (1/2:ℝ) (W i.1-1/2)) →
    (∀ i∈S, xlocal i+H∈Ioo (1/2:ℝ) (W i.1-1/2)) →
    let ε := κ/(16*(Cphys+2)*R^2)
    (∀ i∈S, |(anchor i:ℝ)-(rat i:ℝ)| ≤ ε) →
    (∀ i∈S, 256*((anchor i).den:ℝ) ≤ (Q:ℝ)/3) →
    (∀ i∈S, 256 ≤ (2*ε)*((Q:ℝ)/3)*(anchor i).den) →
    let narrow := fun (i : ℝ × ℤ) =>
      (⌊((rat i).den:ℝ)/(θ*((Q:ℝ)/2))⌋,
       ⌊((rat i).num:ℝ)/(θ*(lambda*(Q:ℝ)/2))⌋)
    let qell := fun (i : ℝ × ℤ) => ((rat i).den:ℝ)*deriv (f (i.1)) (round (z i))
    let V := S ×ˢ (Finset.univ : Finset (Fin 2))
    let offset := fun ip : (ℝ × ℤ) × Fin 2 => ⌊qell ip.1⌋+(ip.2:ℕ)-round (qell ip.1)
    let color := fun ip : (ℝ × ℤ) × Fin 2 => (narrow ip.1,offset ip)
    let NarrowCap := (4/θ+3)*(8*Usrc/(csrc*θ)+3)
    let Cap := 3*NarrowCap

    let q := fun (i : ℝ × ℤ) => (rat i).den
    let μ := fun (i : ℝ × ℤ) => iteratedDeriv 3 (f (i.1)) (round (z i))/6
    let b := fun ip : (ℝ × ℤ) × Fin 2 => (⌊qell ip.1⌋+(ip.2:ℕ) : ℤ)
    let tau := fun ip : (ℝ × ℤ) × Fin 2 => ((b ip:ℝ)-qell ip.1)/2
    let dual := fun (i : ℝ × ℤ) => -2*μ i*(Real.sqrt (2/(3*μ i*(q i:ℝ))))^3
    let x := fun ip : (ℝ × ℤ) × Fin 2 =>
      (![-(v ip.1:ℝ)*b ip/q ip.1,-(v ip.1:ℝ)/q ip.1,
        dual ip.1,3*dual ip.1*tau ip/2] : Fin 4 → ℝ)
    let Fiber := fun key => V.filter (fun ip => color ip=key)
    let μ₀ := csrc*Tsrc/(12*M^3)
    let U₀ := Usrc*Tsrc/(2*M^3)
    let Δtype := (16*U₀/μ₀)*Real.sqrt (U₀*(Q:ℝ)^3)*Real.sqrt K₀/(6*(K₀:ℝ)^2)
    let C₂ := modelPhaseJetCoefficient σ 2+δ
    let C₃ := modelPhaseJetCoefficient σ 3+δ
    let Ct := C₂/2+5*C₃/12
    let Cc := C₂/κ+C₃/(2*κ)
    let Δ := (37*B/2+16*B*Cc+2*Ct+2*Cc)*(Q:ℝ)/(N:ℝ)
    let Ccurv := (4/κ)*(B+2*quarticReciprocalConstant σ δ)
    let D := Δ+quarticNonlinearResidualConstant σ δ*(2*(Q:ℝ))/(N:ℝ)
    let Kres := 4*(37*B/2+16*B*Cc+2*Ct+2*Cc+
      2*quarticNonlinearResidualConstant σ δ)/κ
    let Esize := κ/(16*(Cphys+2))
    let Dbase := 37*B/2+16*B*Cc+2*Ct+2*Cc+2*quarticNonlinearResidualConstant σ δ
    let Tbase := (2/κ)*(B+2*quarticReciprocalConstant σ δ)
    2*3840*128^2*105*(Dbase+64*Tbase*Esize^2) ≤ Bselect*Esize →
    D ≤ 1/2 → Δ < 1/2 → 61*Ccurv*Cphys ≤ Bcut →
    let Lunit := 2*κ/Cphys
    let Gamma := Cphys/κ
    let Cthird := Gamma*(32*Kres+9*quarticReciprocalConstant σ δ)
    let Cpack := 64*Cphys*(Gamma^2*Cthird+Gamma*(modelPhaseJetCoefficient σ 3+δ)/κ)/κ
    let Cfirst := 128*Cphys*(Gamma^2*Cthird+Gamma*(modelPhaseJetCoefficient σ 3+δ)/κ)/κ^2
    let Cgap := 64*Cphys*(Gamma^2*B+Gamma*(modelPhaseJetCoefficient σ 3+δ)/κ)/κ
    let Cmain := 4*(2*Cfirst/Lunit^3)^((3:ℝ)⁻¹)+2
    let Ctail := 4*Cpack/Lunit^2+Cgap
    let Klarge := 60*588*(Uband/lambda)^2*Uband^2*(R^8/(N:ℝ)^4)*
      (Cmain*((Q:ℝ)/(Uband*(N:ℝ)))^((2:ℝ)/3)+Ctail/(Uref:ℝ))
    let Y := S.image Prod.fst
    ((V.image color).card:ℝ) ≤ Cap ∧
    ∀ k : ZMod K₀,
      (∑ ip∈V, ‖∑ j : ZMod K₀, ZMod.stdAddChar (-(j*k))*
        GafniTao.fordAdditiveCharacter (∑ d,x ip d*
          (![(j.val+1:ℝ),(j.val+1:ℝ)^2,(j.val+1:ℝ)^((3:ℝ)/2),
            Real.sqrt (j.val+1:ℝ)] : Fin 4 → ℝ) d)‖)^12 ≤
        C*(K₀:ℝ)^((12:ℝ)+εloss)*Cap^11*
          ∑ key∈V.image color, ((Fiber key).card:ℝ)^10*
            (Vscale*Dtype*(2+θ*(Uband+1/lambda))*(Y.card:ℝ)*(M/(N:ℝ))*(1+Δtype*Jsep)+
              (Y.card:ℝ)^2*Klarge*T^εloss) := by
  exact eventually_double_difference_actual_family_source_sieve hcsrc hUsrc hE hσ hεloss

#print axioms eventually_double_difference_actual_family_source_sieve


/-- The actual rounded cubic completion weight has its physical source
bound. The comparison between source and model amplitudes is derived from
the same double-phase jets, not assumed. -/
private theorem double_difference_source_completion_weight
    (Fsrc : ℝ → ℝ) {r s d y w c U σ δ Tsrc T M N R Q q A z : ℝ}
    (hr : 0 ≤ r) (hs : 0 ≤ s) (hd : 0 < d)
    (hy : y∈Icc (1:ℝ) 2) (hprod : r*s=d*y)
    (hshift : r+s ≤ w) (hw : w ≤ 1/4) (hsmall : 2*U*w ≤ c/64)
    (hc : 0 < c) (hU : 0 < U) (hσ : 0 < σ)
    (hTsrc : 0 < Tsrc) (hT : 0 < T) (hMtwo : 2 ≤ M)
    (hN : 0 < N) (hR : 0 < R) (hQ : 0 < Q)
    (hQq : Q ≤ 2*q) (hNA : N ≤ A) (hz : z∈Icc M (2*M))
    (hscale : T*N*R^2=M^3)
    (hδ : δ ≤ min (modelPhaseThirdLower σ) 1)
    (hf : ∀ u, 0 < u → ContDiffAt ℝ ∞ Fsrc u)
    (hlower : ∀ u∈Icc (1/2:ℝ) 3, c ≤ iteratedDeriv 5 Fsrc u)
    (hjets : ∀ u∈Icc (1/2:ℝ) 3, ∀ n, 1 ≤ n → n ≤ 7 →
      |iteratedDeriv n Fsrc u| ≤ U) :
    let Φ := fun u => (Fsrc u-Fsrc (u+r)-Fsrc (u+s)+Fsrc (u+r+s))/d
    Expdb.IsApproximateModelPhaseFunction (fun u => (Tsrc/T)*Φ u) σ 2 δ →
    let f := fun v => Tsrc*Φ (v/M)
    let μ := iteratedDeriv 3 f (round z)/6
    0 < μ ∧
      c*modelPhaseThirdLower σ/(36*U*N*R^2) ≤ μ ∧
      Real.sqrt (2*q)/(q*Real.sqrt (μ*A)) ≤
        Real.sqrt ((144*U/(c*modelPhaseThirdLower σ))*(R^2/Q)) := by
  intro Φ hmodel f μ
  have hM : 0 < M := by linarith only [hMtwo]
  have hκ : 0 < modelPhaseThirdLower σ := modelPhaseThirdLower_pos hσ
  have hjet u (hu : u∈Icc (3/4:ℝ) (9/4)) :=
    double_difference_cubic_jet_bounds Fsrc hu hy hr hs hd hU hc
      hprod hshift hw hsmall hf hlower hjets
  have hreg u (hu : 0 < u) : ContDiffAt ℝ ∞ Φ u :=
    (hjet 1 (by norm_num)).1 u hu
  have hAmp : modelPhaseThirdLower σ*T/(3*U) ≤ Tsrc := by
    have hlow : modelPhaseThirdLower σ ≤
        iteratedDeriv 3 (fun u => (Tsrc/T)*Φ u) (3/2) := by
      simpa only [iteratedDeriv_succ,iteratedDeriv_zero] using
        (approximateModelPhase_thirdDeriv_bounds hσ hδ hmodel
          (by norm_num : (3/2:ℝ)∈Ioo (1:ℝ) 2)).1
    have hu : |iteratedDeriv 3 Φ (3/2)| ≤ 3*U :=
      (hjet (3/2) (by norm_num)).2.2.1
    rw [iteratedDeriv_const_mul_field] at hlow
    have hb := hlow.trans (mul_le_mul_of_nonneg_left
      ((le_abs_self _).trans hu) (div_pos hTsrc hT).le)
    have hh : modelPhaseThirdLower σ*T ≤ Tsrc*(3*U) := by
      have he : (Tsrc/T)*(3*U)=Tsrc*(3*U)/T := by ring
      rw [he] at hb
      exact (le_div_iff₀ hT).mp hb
    exact (div_le_iff₀ (mul_pos (by norm_num : (0:ℝ) < 3) hU)).mpr hh
  have hround := abs_le.mp (abs_sub_round z)
  have hzround : (0:ℝ) < round z := by linarith only [hround.2,hz.1,hMtwo]
  have hnorm : (round z:ℝ)/M∈Icc (3/4:ℝ) (9/4) := by
    constructor
    · apply (le_div_iff₀ hM).mpr
      linarith only [hround.2,hz.1,hMtwo]
    · apply (div_le_iff₀ hM).mpr
      linarith only [hround.1,hz.2,hMtwo]
  have hphysical : iteratedDeriv 3 f (round z)=
      Tsrc/M^3*iteratedDeriv 3 Φ ((round z:ℝ)/M) := by
    have ha := sargos_iteratedDeriv_comp_affine_local (f:=Φ)
      (l:=0) (r:=(round z:ℝ)+1) (c:=M⁻¹) (d:=0)
      (fun v hv => hreg _ (by
        simpa only [add_zero] using mul_pos (inv_pos.mpr hM) hv.1))
      (show (round z:ℝ)∈Ioo (0:ℝ) ((round z:ℝ)+1) from ⟨hzround,by linarith⟩) 3
    change iteratedDeriv 3 (fun v => Tsrc*Φ (v/M)) (round z)=_
    rw [iteratedDeriv_const_mul_field]
    have he : (fun v => Φ (v/M))=(fun v => Φ (M⁻¹*v+0)) := by
      funext v
      congr 1
      ring
    rw [he,ha]
    simp only [add_zero,inv_pow]
    rw [show M⁻¹*(round z:ℝ)=(round z:ℝ)/M by ring]
    ring
  let μ₀ := c*Tsrc/(12*M^3)
  have hμ₀ : 0 < μ₀ := by dsimp only [μ₀]; positivity
  have hμ : μ₀ ≤ μ := by
    calc
      μ₀ = (Tsrc/M^3)*(c/2)/6 := by dsimp only [μ₀]; ring
      _ ≤ (Tsrc/M^3)*iteratedDeriv 3 Φ ((round z:ℝ)/M)/6 :=
        div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left (hjet _ hnorm).2.1 (by positivity)) (by norm_num)
      _ = μ := by dsimp only [μ]; rw [hphysical]
  have hμp : 0 < μ := hμ₀.trans_le hμ
  have hμphysical : c*modelPhaseThirdLower σ/(36*U*R^2) ≤ μ₀*N := by
    calc
      c*modelPhaseThirdLower σ/(36*U*R^2)=
          (c*N/(12*M^3))*(modelPhaseThirdLower σ*T/(3*U)) := by
        rw [←hscale]
        field_simp
        ring
      _ ≤ (c*N/(12*M^3))*Tsrc := mul_le_mul_of_nonneg_left hAmp (by positivity)
      _ = μ₀*N := by dsimp only [μ₀]; ring
  have hq : 0 < q := by linarith only [hQ,hQq]
  have hAp : 0 < A := hN.trans_le hNA
  have hμA : 0 < μ*A := mul_pos hμp hAp
  have hμN : μ₀*N ≤ μ*A := mul_le_mul hμ hNA hN.le hμp.le
  have hden := mul_pos hQ (mul_pos hμ₀ hN)
  have hright : 0 ≤ 4/(Q*(μ₀*N)) := div_nonneg (by norm_num) hden.le
  have hweight : Real.sqrt (2*q)/(q*Real.sqrt (μ*A)) ≤ Real.sqrt (4/(Q*(μ₀*N))) := by
    apply (sq_le_sq₀
      (div_nonneg (Real.sqrt_nonneg _) (mul_nonneg hq.le (Real.sqrt_nonneg _)))
      (Real.sqrt_nonneg _)).mp
    rw [div_pow,mul_pow,Real.sq_sqrt (by positivity : 0 ≤ 2*q),
      Real.sq_sqrt hμA.le,Real.sq_sqrt hright]
    apply (div_le_div_iff₀ (mul_pos (pow_pos hq 2) hμA) hden).mpr
    have hm := mul_le_mul hQq hμN (mul_nonneg hμ₀.le hN.le) (by positivity : 0 ≤ 2*q)
    have hh := mul_le_mul_of_nonneg_left hm (by positivity : 0 ≤ 2*q)
    nlinarith only [hh]
  have hμlower : c*modelPhaseThirdLower σ/(36*U*N*R^2) ≤ μ := by
    calc
      _ = (c*modelPhaseThirdLower σ/(36*U*R^2))/N := by ring
      _ ≤ (μ₀*N)/N := div_le_div_of_nonneg_right hμphysical hN.le
      _ = μ₀ := by field_simp
      _ ≤ μ := hμ
  refine ⟨hμp,hμlower,hweight.trans (Real.sqrt_le_sqrt ?_)⟩
  have hi := one_div_le_one_div_of_le
    (by positivity : 0 < c*modelPhaseThirdLower σ/(36*U*R^2)) hμphysical
  calc
    _ = (4/Q)*(1/(μ₀*N)) := by ring
    _ ≤ (4/Q)*(1/(c*modelPhaseThirdLower σ/(36*U*R^2))) :=
      mul_le_mul_of_nonneg_left hi (by positivity)
    _ = _ := by field_simp; ring

example
    (Fsrc : ℝ → ℝ) {r s d y w c U σ δ Tsrc T M N R Q q A z : ℝ}
    (hr : 0 ≤ r) (hs : 0 ≤ s) (hd : 0 < d)
    (hy : y∈Icc (1:ℝ) 2) (hprod : r*s=d*y)
    (hshift : r+s ≤ w) (hw : w ≤ 1/4) (hsmall : 2*U*w ≤ c/64)
    (hc : 0 < c) (hU : 0 < U) (hσ : 0 < σ)
    (hTsrc : 0 < Tsrc) (hT : 0 < T) (hMtwo : 2 ≤ M)
    (hN : 0 < N) (hR : 0 < R) (hQ : 0 < Q)
    (hQq : Q ≤ 2*q) (hNA : N ≤ A) (hz : z∈Icc M (2*M))
    (hscale : T*N*R^2=M^3)
    (hδ : δ ≤ min (modelPhaseThirdLower σ) 1)
    (hf : ∀ u, 0 < u → ContDiffAt ℝ ∞ Fsrc u)
    (hlower : ∀ u∈Icc (1/2:ℝ) 3, c ≤ iteratedDeriv 5 Fsrc u)
    (hjets : ∀ u∈Icc (1/2:ℝ) 3, ∀ n, 1 ≤ n → n ≤ 7 →
      |iteratedDeriv n Fsrc u| ≤ U) :
    let Φ := fun u => (Fsrc u-Fsrc (u+r)-Fsrc (u+s)+Fsrc (u+r+s))/d
    Expdb.IsApproximateModelPhaseFunction (fun u => (Tsrc/T)*Φ u) σ 2 δ →
    let f := fun v => Tsrc*Φ (v/M)
    let μ := iteratedDeriv 3 f (round z)/6
    0 < μ ∧
      c*modelPhaseThirdLower σ/(36*U*N*R^2) ≤ μ ∧
      Real.sqrt (2*q)/(q*Real.sqrt (μ*A)) ≤
        Real.sqrt ((144*U/(c*modelPhaseThirdLower σ))*(R^2/Q)) := by
  exact double_difference_source_completion_weight Fsrc hr hs hd hy hprod hshift hw hsmall
    hc hU hσ hTsrc hT hMtwo hN hR hQ hQq hNA hz hscale hδ hf hlower hjets

#print axioms double_difference_source_completion_weight

/-- Physical-size consumer of the actual same-matrix double-shift family:
joint-color weights are absorbed using the literal rounded original grid. -/
private theorem eventually_double_difference_actual_family_physical_sieve
    {csrc Usrc E σ εloss : ℝ}
    (hcsrc : 0 < csrc) (hUsrc : 0 < Usrc)
    (hE : 0 < E) (hσ : 0 < σ) (hεloss : 0 < εloss) :
    let κ := modelPhaseThirdLower σ
    let L := max (32*Usrc^2/csrc^2)
      (64*(modelPhaseJetCoefficient σ 3+1)*Usrc*E/κ^2)
    let θ := 1/(8*(L+3))
    ∃ C Dtype : ℝ, 0 < C ∧ 0 < Dtype ∧
    ∀ {Jref : ℝ}, 0 ≤ Jref →
    ∀ᶠ T : ℝ in Filter.atTop, ∀ (S : Finset (ℝ × ℤ)) (Fsrc rshift sshift : ℝ → ℝ)
    (z : (ℝ × ℤ) → ℝ) (rat : (ℝ × ℤ) → ℚ) (v : (ℝ × ℤ) → ℤ) (Nlen : (ℝ × ℤ) → ℕ)
    (Q K₀ N : ℕ) [NeZero K₀] (R Jsep : ℝ) (Z : ℝ → ℤ)
    {d Wmax Tsrc M δ Bcut Bselect : ℝ}
    (Uref : ℕ) (Refs : Finset ℝ) (Gaps : Finset (ℝ × ℝ))
    (A : ℝ → ℤ) (W : ℝ → ℝ) (gap : (ℝ × ℤ) → ℝ × ℝ)
    (anchor : (ℝ × ℤ) → ℚ) (e r vRef s : ℝ × ℝ → ℤ),
    let lambda := csrc*Tsrc/(2*M^2)
    let Uband := Usrc*Tsrc/M^2
    let Vscale := max 1 (Uband*(N:ℝ)/(Q:ℝ))
    (0 < d) → (0 ≤ Wmax) → (Wmax ≤ 1/4) → (2*Usrc*Wmax ≤ csrc/64) →
    (0 < Tsrc) →
    (0 < T) →
    (0 < M) →
    (δ ≤ min (modelPhaseThirdLower σ) 1) →
    (Tsrc ≤ E*T) →
    (0 < Q) → (Uband ≤ 1) →
    (∀ i∈S, i.1∈Icc (1:ℝ) 2) →
    (∀ i∈S, z i∈Icc M (2*M)) →
    (∀ w, 0 < w → ContDiffAt ℝ ∞ Fsrc w) →
    (∀ w∈Icc (1/2:ℝ) 3, csrc ≤ iteratedDeriv 5 Fsrc w) →
    (∀ w∈Icc (1/2:ℝ) 3, ∀ n, 1 ≤ n → n ≤ 7 → |iteratedDeriv n Fsrc w| ≤ Usrc) →
    (∀ w∈Icc (1/2:ℝ) 3,
      csrc ≤ |(iteratedDeriv 5 Fsrc w)^2-iteratedDeriv 4 Fsrc w*iteratedDeriv 6 Fsrc w|) →
    (∀ i∈S, (rat i).den ≤ Q ∧ Q ≤ 2*(rat i).den) →
    (∀ i∈S, ((rat i).den:ℤ) ∣ (rat i).num*v i-1) →
    (∀ w∈Icc (1/2:ℝ) 3, iteratedDeriv 4 Fsrc w ≤ -csrc) →
    (2 ≤ M) →
    (0 < N) →
    (0 < Jsep) → (Jsep ≤ M) → ((N:ℝ) ≤ M) → (Wmax*Jsep ≤ 1) →
    ((Q:ℝ)*(N:ℝ) ≤ (K₀:ℝ)*R^2) →
    (∀ i∈S, N ≤ Nlen i ∧ Nlen i ≤ 3*N ∧
      round (z i)+(Nlen i:ℤ)=Z i.1+(N:ℤ)*i.2+2*(N:ℤ)) →
    (∀ i∈S, ∀ j∈S, i.1≠j.1 → 1 ≤ Jsep*|i.1-j.1|) →
    (∀ y∈S.image Prod.fst,
      0 ≤ rshift y ∧ 0 ≤ sshift y ∧ rshift y*sshift y=d*y ∧ rshift y+sshift y ≤ Wmax) →
    let Φ := fun y u =>
      (Fsrc u-Fsrc (u+rshift y)-Fsrc (u+sshift y)+Fsrc (u+rshift y+sshift y))/d
    let Fmodel := fun (i : ℝ × ℤ) u => (Tsrc/T)*Φ i.1 u
    (∀ i∈S, Expdb.IsApproximateModelPhaseFunction (Fmodel i) σ 4 δ) →
    let f := fun p w => Tsrc*Φ p (w/M)
    (∀ i∈S, iteratedDeriv 2 (f (i.1)) (z i)/2=(rat i:ℝ)) →
    (∀ i∈S, 1 ≤ Nlen i ∧ (rat i).den ≤ Nlen i ∧
      1 ≤ (iteratedDeriv 3 (f (i.1)) (round (z i))/6)*((rat i).den:ℝ)^2*Nlen i) →
    (∀ i∈S, 7*((iteratedDeriv 3 (f (i.1)) (round (z i))/6)*
      ((rat i).den:ℝ)*(Nlen i:ℝ)^2) ≤ K₀) →

    (1 ≤ R) → (R ≤ M) → (T*(N:ℝ)*R^2=M^3) →
    (∀ i∈S, M ≤ A i.1) → (∀ i∈S, A i.1+W i.1 ≤ 2*M) →
    let xlocal := fun i : ℝ × ℤ => z i-(A i.1:ℝ)
    (∀ i∈S, xlocal i∈Ioo (1/2:ℝ) (W i.1-1/2)) →
    (∀ i∈S, gap i∈Gaps) →
    (∀ ab∈Gaps, (vRef ab)*(r ab)-(e ab)*(s ab)=1) →
    (∀ ab∈Gaps, ((0:ℝ) < (r ab) ∧ ((e ab):ℝ)/(r ab)=ab.1) ∨
      (((r ab):ℝ) < 0 ∧ ((e ab):ℝ)/(r ab)=ab.2)) →
    (0 < Bcut) → (∀ ab∈Gaps, (s ab) ≠ 0) →
    (∀ ab∈Gaps, ((e ab):ℝ)/(r ab)∈Refs) →
    (∀ ab∈Gaps, ((vRef ab):ℝ)/(s ab)∈Refs) →
    (∀ a∈Refs, ∀ b∈Refs, a ≠ b → ((Uref:ℝ)/R^2)/4 < |a-b|) →
    (∀ i∈S, xlocal i-(56*(Uref:ℝ)/κ)*(N:ℝ)∈Ioo (1/2:ℝ) (W i.1-1/2)) →
    (∀ i∈S, xlocal i+(56*(Uref:ℝ)/κ)*(N:ℝ)∈Ioo (1/2:ℝ) (W i.1-1/2)) →
    (1 ≤ Uref) →
    (2+168/κ ≤ Bselect) → (7*Bcut ≤ κ*Bselect) →
    (Bselect^2*(Uref:ℝ)^3*R^2 ≤ (N:ℝ)^2) →
    (∀ ab∈Gaps, R^2 ≤ ((r ab):ℝ)^2*(Uref:ℝ)) →
    (∀ ab∈Gaps, ab.2-ab.1 ≤ 7*(Uref:ℝ)/(2*R^2)) →
    (R ≤ (Q:ℝ)) →
    ((Uref:ℝ) ≤ ((N:ℝ)/(Q:ℝ))^((2:ℝ)/3)/Bselect) →
    ((N:ℝ)^10 ≤ M^3*R^7) →
    (∀ i∈S, (rat i:ℝ)∈Icc (gap i).1 (gap i).2) →
    (∀ ab∈Gaps, ab.1∈Refs ∧ ab.2∈Refs ∧ ab.1 < ab.2 ∧
      ∀ t∈Refs, ¬(ab.1 < t ∧ t < ab.2)) →
    (Q:ℝ) ≤ (N:ℝ) →
    ((N:ℝ)^2 ≤ M ∨ (1 ≤ M ∧ (N:ℝ) ≤ T ∧ R^2 ≤ T)) → (Uref:ℝ) ≤ R^2 →
    (∀ ab∈Gaps, |((r ab):ℝ)| ≤ 4*R^2/(Uref:ℝ)) →
    (∀ ab∈Gaps, |((s ab):ℝ)| ≤ 4*R^2/(Uref:ℝ)) →
    (∀ ab∈Gaps, |((e ab):ℝ)| ≤
      (3*Jref*T/(2*σ*M^2)+1)*(4*R^2/(Uref:ℝ))) →
    (∀ ab∈Gaps, |((vRef ab):ℝ)| ≤
      (3*Jref*T/(2*σ*M^2)+1)*(4*R^2/(Uref:ℝ))) →
    let Cphys := σ*(σ+1)+1
    let c := κ/6
    let J := Cphys/6
    let B := max 1 (max (2*Real.sqrt J) (8*J*Real.sqrt J/(3*c)))
    B*R^2/(N:ℝ)^2 ≤ 1/2 →
    (N:ℝ) ≤ R^2 → R ≤ (N:ℝ) → (N:ℝ)^3 ≤ M*R^2 →
    2*R^2 ≤ (Q:ℝ)*(N:ℝ) →
    let H := (N:ℝ)/(Cphys+2)
    2 ≤ (N:ℝ) →
    (∀ i∈S, xlocal i-H∈Ioo (1/2:ℝ) (W i.1-1/2)) →
    (∀ i∈S, xlocal i+H∈Ioo (1/2:ℝ) (W i.1-1/2)) →
    let ε := κ/(16*(Cphys+2)*R^2)
    (∀ i∈S, |(anchor i:ℝ)-(rat i:ℝ)| ≤ ε) →
    (∀ i∈S, 256*((anchor i).den:ℝ) ≤ (Q:ℝ)/3) →
    (∀ i∈S, 256 ≤ (2*ε)*((Q:ℝ)/3)*(anchor i).den) →
    let narrow := fun (i : ℝ × ℤ) =>
      (⌊((rat i).den:ℝ)/(θ*((Q:ℝ)/2))⌋,
       ⌊((rat i).num:ℝ)/(θ*(lambda*(Q:ℝ)/2))⌋)
    let qell := fun (i : ℝ × ℤ) => ((rat i).den:ℝ)*deriv (f (i.1)) (round (z i))
    let V := S ×ˢ (Finset.univ : Finset (Fin 2))
    let offset := fun ip : (ℝ × ℤ) × Fin 2 => ⌊qell ip.1⌋+(ip.2:ℕ)-round (qell ip.1)
    let color := fun ip : (ℝ × ℤ) × Fin 2 => (narrow ip.1,offset ip)
    let NarrowCap := (4/θ+3)*(8*Usrc/(csrc*θ)+3)
    let Cap := 3*NarrowCap

    let q := fun (i : ℝ × ℤ) => (rat i).den
    let μ := fun (i : ℝ × ℤ) => iteratedDeriv 3 (f (i.1)) (round (z i))/6
    let b := fun ip : (ℝ × ℤ) × Fin 2 => (⌊qell ip.1⌋+(ip.2:ℕ) : ℤ)
    let tau := fun ip : (ℝ × ℤ) × Fin 2 => ((b ip:ℝ)-qell ip.1)/2
    let dual := fun (i : ℝ × ℤ) => -2*μ i*(Real.sqrt (2/(3*μ i*(q i:ℝ))))^3
    let x := fun ip : (ℝ × ℤ) × Fin 2 =>
      (![-(v ip.1:ℝ)*b ip/q ip.1,-(v ip.1:ℝ)/q ip.1,
        dual ip.1,3*dual ip.1*tau ip/2] : Fin 4 → ℝ)
    let Fiber := fun key => V.filter (fun ip => color ip=key)
    let μ₀ := csrc*Tsrc/(12*M^3)
    let U₀ := Usrc*Tsrc/(2*M^3)
    let Δtype := (16*U₀/μ₀)*Real.sqrt (U₀*(Q:ℝ)^3)*Real.sqrt K₀/(6*(K₀:ℝ)^2)
    let C₂ := modelPhaseJetCoefficient σ 2+δ
    let C₃ := modelPhaseJetCoefficient σ 3+δ
    let Ct := C₂/2+5*C₃/12
    let Cc := C₂/κ+C₃/(2*κ)
    let Δ := (37*B/2+16*B*Cc+2*Ct+2*Cc)*(Q:ℝ)/(N:ℝ)
    let Ccurv := (4/κ)*(B+2*quarticReciprocalConstant σ δ)
    let D := Δ+quarticNonlinearResidualConstant σ δ*(2*(Q:ℝ))/(N:ℝ)
    let Kres := 4*(37*B/2+16*B*Cc+2*Ct+2*Cc+
      2*quarticNonlinearResidualConstant σ δ)/κ
    let Esize := κ/(16*(Cphys+2))
    let Dbase := 37*B/2+16*B*Cc+2*Ct+2*Cc+2*quarticNonlinearResidualConstant σ δ
    let Tbase := (2/κ)*(B+2*quarticReciprocalConstant σ δ)
    2*3840*128^2*105*(Dbase+64*Tbase*Esize^2) ≤ Bselect*Esize →
    D ≤ 1/2 → Δ < 1/2 → 61*Ccurv*Cphys ≤ Bcut →
    let Lunit := 2*κ/Cphys
    let Gamma := Cphys/κ
    let Cthird := Gamma*(32*Kres+9*quarticReciprocalConstant σ δ)
    let Cpack := 64*Cphys*(Gamma^2*Cthird+Gamma*(modelPhaseJetCoefficient σ 3+δ)/κ)/κ
    let Cfirst := 128*Cphys*(Gamma^2*Cthird+Gamma*(modelPhaseJetCoefficient σ 3+δ)/κ)/κ^2
    let Cgap := 64*Cphys*(Gamma^2*B+Gamma*(modelPhaseJetCoefficient σ 3+δ)/κ)/κ
    let Cmain := 4*(2*Cfirst/Lunit^3)^((3:ℝ)⁻¹)+2
    let Ctail := 4*Cpack/Lunit^2+Cgap
    let Klarge := 60*588*(Uband/lambda)^2*Uband^2*(R^8/(N:ℝ)^4)*
      (Cmain*((Q:ℝ)/(Uband*(N:ℝ)))^((2:ℝ)/3)+Ctail/(Uref:ℝ))
    let Y := S.image Prod.fst
    let Values := fun k : ZMod K₀ =>
      ∑ ip∈V, ‖∑ j : ZMod K₀, ZMod.stdAddChar (-(j*k))*
        GafniTao.fordAdditiveCharacter (∑ d,x ip d*
          (![(j.val+1:ℝ),(j.val+1:ℝ)^2,(j.val+1:ℝ)^((3:ℝ)/2),
            Real.sqrt (j.val+1:ℝ)] : Fin 4 → ℝ) d)‖
    let Wphys := (144*Usrc/(csrc*κ))*(R^2/(Q:ℝ))
    let WeightedValues := fun k : ZMod K₀ =>
      ∑ ip∈V, (Real.sqrt (2*(q ip.1:ℝ))/((q ip.1:ℝ)*Real.sqrt (μ ip.1*(Nlen ip.1:ℝ))))*
        ‖∑ j : ZMod K₀, ZMod.stdAddChar (-(j*k))*
          GafniTao.fordAdditiveCharacter (∑ d,x ip d*
            (![(j.val+1:ℝ),(j.val+1:ℝ)^2,(j.val+1:ℝ)^((3:ℝ)/2),
              Real.sqrt (j.val+1:ℝ)] : Fin 4 → ℝ) d)‖
    let Mass := Vscale*Dtype*(2+θ*(Uband+1/lambda))*(Y.card:ℝ)*(M/(N:ℝ))*(1+Δtype*Jsep)+
      (Y.card:ℝ)^2*Klarge*T^εloss
    ((V.image color).card:ℝ) ≤ Cap ∧
      (∀ k, (Values k)^12 ≤ C*(K₀:ℝ)^((12:ℝ)+εloss)*Cap^11*
        ∑ key∈V.image color, ((Fiber key).card:ℝ)^10*Mass) ∧
      (V.card:ℝ) ≤ 10*(Y.card:ℝ)*(M/(N:ℝ)) ∧
      (∀ k, (Values k)^12 ≤ C*(K₀:ℝ)^((12:ℝ)+εloss)*Cap^11*
        (10*(Y.card:ℝ)*(M/(N:ℝ)))^10*Mass) ∧
      ∀ k, ((WeightedValues k)^12 ≤ Wphys^6*
        (C*(K₀:ℝ)^((12:ℝ)+εloss)*Cap^11*(V.card:ℝ)^10*Mass)) ∧
        (WeightedValues k)^12 ≤ Wphys^6*
          (C*(K₀:ℝ)^((12:ℝ)+εloss)*Cap^11*(10*(Y.card:ℝ)*(M/(N:ℝ)))^10*Mass) := by
  classical
  intro κ L θ
  obtain ⟨C,Dtype,hC,hDtype,hsource⟩ :=
    eventually_double_difference_actual_family_source_sieve hcsrc hUsrc hE hσ hεloss
  refine ⟨C,Dtype,hC,hDtype,?_⟩
  intro Jref hJref
  filter_upwards [hsource hJref] with T hfamily
  intro S Fsrc rshift sshift z rat v Nlen Q K₀ N instK R Jsep Z
    d Wmax Tsrc M δ Bcut Bselect Uref Refs Gaps A W gap anchor e r vRef s
    lambda Uband Vscale hd hw hwcap hsmallShift hTsrc hT hM hδ hsourceScale hQ hUbandCap
    hy hz hreg hlower hjets htests hden hinv hnegative hMtwo hN
    hJsep hJM hNM hwJ hmesh hgeometry hseparation hshifts Φ Fmodel hmodel f hlevel hminor hcomplete
    hR hRM hscale hA hW xlocal hx hgapMem
    hchart horientation hBcut hs hrefSet hparentSet hsep hwideL hwideU hUref
    hBselectSize hcutMargin hselectedWrap hreferenceDen hgapWidth hRQ
    hselectedUpper hscaleTen hfamilyGap hgap hQN hNsqM hUR
    hrHeight hsHeight heHeight hvHeight Cphys c J B hsmall hNR hRN hNcube hminscale
    H hNtwo hLeft hRight ε hanchor hcut hcount
    narrow qell V offset color NarrowCap Cap q μ b tau dual x Fiber μ₀ U₀ Δtype
    C₂ C₃ Ct Cc Δ Ccurv D Kres Esize Dbase Tbase hsize hD hΔ hBsize
    Lunit Gamma Cthird Cpack Cfirst Cgap Cmain Ctail Klarge Y Values Wphys WeightedValues Mass

  obtain ⟨hcard,hweighted⟩ := hfamily S Fsrc rshift sshift z rat v Nlen Q K₀ N R Jsep Z
    (d:=d) (Wmax:=Wmax) (Tsrc:=Tsrc) (M:=M) (δ:=δ) (Bcut:=Bcut) (Bselect:=Bselect)
    Uref Refs Gaps A W gap anchor e r vRef s
    hd hw hwcap hsmallShift hTsrc hT hM hδ hsourceScale hQ hUbandCap
    hy hz hreg hlower hjets htests hden hinv hnegative hMtwo hN
    hJsep hJM hNM hwJ hmesh hgeometry hseparation hshifts hmodel hlevel hminor hcomplete
    hR hRM hscale hA hW hx hgapMem
    hchart horientation hBcut hs hrefSet hparentSet hsep hwideL hwideU hUref
    hBselectSize hcutMargin hselectedWrap hreferenceDen hgapWidth hRQ
    hselectedUpper hscaleTen hfamilyGap hgap hQN hNsqM hUR
    hrHeight hsHeight heHeight hvHeight hsmall hNR hRN hNcube hminscale
    hNtwo hLeft hRight hanchor hcut hcount hsize hD hΔ hBsize
  let Scale := C*(K₀:ℝ)^((12:ℝ)+εloss)*Cap^11
  change ∀ k, (Values k)^12 ≤ Scale*
    (∑ key∈V.image color, ((Fiber key).card:ℝ)^10*Mass) at hweighted
  have hYimage : V.image (fun ip => ip.1.1)=Y := by
    ext y
    constructor
    · intro hym
      obtain ⟨ip,hip,rfl⟩ := Finset.mem_image.mp hym
      exact Finset.mem_image_of_mem Prod.fst (Finset.mem_product.mp hip).1
    · intro hym
      obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hym
      exact Finset.mem_image.mpr ⟨(i,0),Finset.mem_product.mpr ⟨hi,Finset.mem_univ _⟩,rfl⟩
  have hpoints := rounded_offset_family_point_count V (fun y n => z (y,n))
    (fun y n => Nlen (y,n)) N Z hM.le hN
    (fun ip hip => hz ip.1 (Finset.mem_product.mp hip).1)
    (fun ip hip => hgeometry ip.1 (Finset.mem_product.mp hip).1)
  rw [hYimage] at hpoints
  have hNpos : (0:ℝ) < N := Nat.cast_pos.mpr hN
  have hratio : 1 ≤ M/(N:ℝ) := (le_div_iff₀ hNpos).mpr (by simpa only [one_mul] using hNM)
  have hphysical : (V.card:ℝ) ≤ 10*(Y.card:ℝ)*(M/(N:ℝ)) := by
    calc
      _ ≤ 2*(4+M/(N:ℝ))*(Y.card:ℝ) := hpoints
      _ ≤ (10*(M/(N:ℝ)))*(Y.card:ℝ) :=
        mul_le_mul_of_nonneg_right (by linarith only [hratio]) (Nat.cast_nonneg _)
      _ = _ := by ring
  have hweightCard : (∑ key∈V.image color, ((Fiber key).card:ℝ))=(V.card:ℝ) := by
    exact_mod_cast (Finset.card_eq_sum_card_image color V).symm
  have hweights : (∑ key∈V.image color, ((Fiber key).card:ℝ)^10) ≤ (V.card:ℝ)^10 := by
    calc
      _ = ∑ key∈V.image color, ((Fiber key).card:ℝ)*((Fiber key).card:ℝ)^9 := by
        apply Finset.sum_congr rfl
        intro key _
        rw [pow_succ']
      _ ≤ ∑ key∈V.image color, ((Fiber key).card:ℝ)*(V.card:ℝ)^9 := by
        apply Finset.sum_le_sum
        intro key _
        apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
        apply pow_le_pow_left₀ (Nat.cast_nonneg _)
        exact_mod_cast Finset.card_filter_le V (fun ip => color ip=key)
      _ = (V.card:ℝ)^10 := by
        rw [←Finset.sum_mul,hweightCard]
        ring
  have hplainCap (Bcard : ℝ) (hVcard : (V.card:ℝ) ≤ Bcard) (k : ZMod K₀) : (Values k)^12 ≤
      Scale*Bcard^10*Mass := by
    by_cases hV : V=∅
    · have hY : Y=∅ := by rw [←hYimage,hV,Finset.image_empty]
      have hh := hweighted k
      simpa only [Values,Mass,hV,hY,Finset.sum_empty,Finset.image_empty,Finset.card_empty,
        Nat.cast_zero,mul_zero,zero_mul,zero_pow (by decide : (10:ℕ)≠0),
        zero_pow (by decide : (2:ℕ)≠0),add_zero] using hh
    · obtain ⟨i,hi⟩ := Finset.nonempty_iff_ne_empty.mpr hV
      have hf : 0 < (Fiber (color i)).card :=
        Finset.card_pos.mpr ⟨i,Finset.mem_filter.mpr ⟨hi,rfl⟩⟩
      have hweight : 0 < ∑ key∈V.image color, ((Fiber key).card:ℝ)^10 :=
        lt_of_lt_of_le (pow_pos (Nat.cast_pos.mpr hf) 10)
          (Finset.single_le_sum (f:=fun key => ((Fiber key).card:ℝ)^10)
            (fun key _ => pow_nonneg (Nat.cast_nonneg _) 10)
            (Finset.mem_image_of_mem color hi))
      have hb : (Values k)^12 ≤ (Scale*Mass)*
          (∑ key∈V.image color, ((Fiber key).card:ℝ)^10) := by
        calc
          _ ≤ _ := hweighted k
          _ = _ := by rw [←Finset.sum_mul]; ac_rfl
      have hSM : 0 ≤ Scale*Mass := nonneg_of_mul_nonneg_left
        ((pow_nonneg (Finset.sum_nonneg (fun _ _ => norm_nonneg _)) 12).trans hb) hweight
      calc
        (Values k)^12 ≤ (Scale*Mass)*(∑ key∈V.image color, ((Fiber key).card:ℝ)^10) := hb
        _ ≤ (Scale*Mass)*Bcard^10 :=
          mul_le_mul_of_nonneg_left
            (hweights.trans (pow_le_pow_left₀ (Nat.cast_nonneg _) hVcard 10)) hSM
        _ = _ := mul_right_comm Scale Mass _
  have hplain (k : ZMod K₀) : (Values k)^12 ≤
      Scale*(10*(Y.card:ℝ)*(M/(N:ℝ)))^10*Mass :=
    hplainCap _ hphysical k
  refine ⟨hcard,hweighted,hphysical,hplain,?_⟩
  intro k
  have hκ : 0 < κ := modelPhaseThirdLower_pos hσ
  have hWphys : 0 ≤ Wphys := by dsimp only [Wphys]; positivity
  let weight := fun ip : (ℝ × ℤ) × Fin 2 =>
    Real.sqrt (2*(q ip.1:ℝ))/((q ip.1:ℝ)*Real.sqrt (μ ip.1*(Nlen ip.1:ℝ)))
  let val := fun ip : (ℝ × ℤ) × Fin 2 =>
    ∑ j : ZMod K₀, ZMod.stdAddChar (-(j*k))*
      GafniTao.fordAdditiveCharacter (∑ d,x ip d*
        (![(j.val+1:ℝ),(j.val+1:ℝ)^2,(j.val+1:ℝ)^((3:ℝ)/2),
          Real.sqrt (j.val+1:ℝ)] : Fin 4 → ℝ) d)
  have hweight ip (hip : ip∈V) : weight ip ≤ Real.sqrt Wphys := by
    have hi := (Finset.mem_product.mp hip).1
    have hsdata := hshifts ip.1.1 (Finset.mem_image_of_mem Prod.fst hi)
    have hh := double_difference_source_completion_weight Fsrc
      hsdata.1 hsdata.2.1 hd (hy ip.1 hi) hsdata.2.2.1 hsdata.2.2.2 hwcap hsmallShift
      hcsrc hUsrc hσ hTsrc hT hMtwo hNpos (zero_lt_one.trans_le hR)
      (Nat.cast_pos.mpr hQ)
      (show (Q:ℝ) ≤ 2*((rat ip.1).den:ℝ) by exact_mod_cast (hden ip.1 hi).2)
      (show (N:ℝ) ≤ (Nlen ip.1:ℝ) by exact_mod_cast (hgeometry ip.1 hi).1)
      (hz ip.1 hi) hscale hδ hreg hlower hjets
      (approximateModelPhase_mono (hmodel ip.1 hi) (by norm_num : 2 ≤ 4) le_rfl)
    exact hh.2.2
  have hweight0 ip : 0 ≤ weight ip :=
    div_nonneg (Real.sqrt_nonneg _)
      (mul_nonneg (Nat.cast_nonneg _) (Real.sqrt_nonneg _))
  have hs0 : 0 ≤ ∑ ip∈V, weight ip*‖val ip‖ :=
    Finset.sum_nonneg (fun ip _ => mul_nonneg (hweight0 ip) (norm_nonneg _))
  have hsum : (∑ ip∈V, weight ip*‖val ip‖) ≤ Real.sqrt Wphys*(Values k) := by
    change (∑ ip∈V, weight ip*‖val ip‖) ≤ Real.sqrt Wphys*(∑ ip∈V, ‖val ip‖)
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun ip hip =>
      mul_le_mul_of_nonneg_right (hweight ip hip) (norm_nonneg _))
  have hp := pow_le_pow_left₀ hs0 hsum 12
  have hsqrt : (Real.sqrt Wphys)^12=Wphys^6 := by
    rw [show (12:ℕ)=2*6 by norm_num,pow_mul,Real.sq_sqrt hWphys]
  rw [mul_pow,hsqrt] at hp
  constructor
  · exact hp.trans (mul_le_mul_of_nonneg_left (hplainCap _ le_rfl k) (pow_nonneg hWphys 6))
  · exact hp.trans (mul_le_mul_of_nonneg_left (hplain k) (pow_nonneg hWphys 6))

example
    {csrc Usrc E σ εloss : ℝ}
    (hcsrc : 0 < csrc) (hUsrc : 0 < Usrc)
    (hE : 0 < E) (hσ : 0 < σ) (hεloss : 0 < εloss) :
    let κ := modelPhaseThirdLower σ
    let L := max (32*Usrc^2/csrc^2)
      (64*(modelPhaseJetCoefficient σ 3+1)*Usrc*E/κ^2)
    let θ := 1/(8*(L+3))
    ∃ C Dtype : ℝ, 0 < C ∧ 0 < Dtype ∧
    ∀ {Jref : ℝ}, 0 ≤ Jref →
    ∀ᶠ T : ℝ in Filter.atTop, ∀ (S : Finset (ℝ × ℤ)) (Fsrc rshift sshift : ℝ → ℝ)
    (z : (ℝ × ℤ) → ℝ) (rat : (ℝ × ℤ) → ℚ) (v : (ℝ × ℤ) → ℤ) (Nlen : (ℝ × ℤ) → ℕ)
    (Q K₀ N : ℕ) [NeZero K₀] (R Jsep : ℝ) (Z : ℝ → ℤ)
    {d Wmax Tsrc M δ Bcut Bselect : ℝ}
    (Uref : ℕ) (Refs : Finset ℝ) (Gaps : Finset (ℝ × ℝ))
    (A : ℝ → ℤ) (W : ℝ → ℝ) (gap : (ℝ × ℤ) → ℝ × ℝ)
    (anchor : (ℝ × ℤ) → ℚ) (e r vRef s : ℝ × ℝ → ℤ),
    let lambda := csrc*Tsrc/(2*M^2)
    let Uband := Usrc*Tsrc/M^2
    let Vscale := max 1 (Uband*(N:ℝ)/(Q:ℝ))
    (0 < d) → (0 ≤ Wmax) → (Wmax ≤ 1/4) → (2*Usrc*Wmax ≤ csrc/64) →
    (0 < Tsrc) →
    (0 < T) →
    (0 < M) →
    (δ ≤ min (modelPhaseThirdLower σ) 1) →
    (Tsrc ≤ E*T) →
    (0 < Q) → (Uband ≤ 1) →
    (∀ i∈S, i.1∈Icc (1:ℝ) 2) →
    (∀ i∈S, z i∈Icc M (2*M)) →
    (∀ w, 0 < w → ContDiffAt ℝ ∞ Fsrc w) →
    (∀ w∈Icc (1/2:ℝ) 3, csrc ≤ iteratedDeriv 5 Fsrc w) →
    (∀ w∈Icc (1/2:ℝ) 3, ∀ n, 1 ≤ n → n ≤ 7 → |iteratedDeriv n Fsrc w| ≤ Usrc) →
    (∀ w∈Icc (1/2:ℝ) 3,
      csrc ≤ |(iteratedDeriv 5 Fsrc w)^2-iteratedDeriv 4 Fsrc w*iteratedDeriv 6 Fsrc w|) →
    (∀ i∈S, (rat i).den ≤ Q ∧ Q ≤ 2*(rat i).den) →
    (∀ i∈S, ((rat i).den:ℤ) ∣ (rat i).num*v i-1) →
    (∀ w∈Icc (1/2:ℝ) 3, iteratedDeriv 4 Fsrc w ≤ -csrc) →
    (2 ≤ M) →
    (0 < N) →
    (0 < Jsep) → (Jsep ≤ M) → ((N:ℝ) ≤ M) → (Wmax*Jsep ≤ 1) →
    ((Q:ℝ)*(N:ℝ) ≤ (K₀:ℝ)*R^2) →
    (∀ i∈S, N ≤ Nlen i ∧ Nlen i ≤ 3*N ∧
      round (z i)+(Nlen i:ℤ)=Z i.1+(N:ℤ)*i.2+2*(N:ℤ)) →
    (∀ i∈S, ∀ j∈S, i.1≠j.1 → 1 ≤ Jsep*|i.1-j.1|) →
    (∀ y∈S.image Prod.fst,
      0 ≤ rshift y ∧ 0 ≤ sshift y ∧ rshift y*sshift y=d*y ∧ rshift y+sshift y ≤ Wmax) →
    let Φ := fun y u =>
      (Fsrc u-Fsrc (u+rshift y)-Fsrc (u+sshift y)+Fsrc (u+rshift y+sshift y))/d
    let Fmodel := fun (i : ℝ × ℤ) u => (Tsrc/T)*Φ i.1 u
    (∀ i∈S, Expdb.IsApproximateModelPhaseFunction (Fmodel i) σ 4 δ) →
    let f := fun p w => Tsrc*Φ p (w/M)
    (∀ i∈S, iteratedDeriv 2 (f (i.1)) (z i)/2=(rat i:ℝ)) →
    (∀ i∈S, 1 ≤ Nlen i ∧ (rat i).den ≤ Nlen i ∧
      1 ≤ (iteratedDeriv 3 (f (i.1)) (round (z i))/6)*((rat i).den:ℝ)^2*Nlen i) →
    (∀ i∈S, 7*((iteratedDeriv 3 (f (i.1)) (round (z i))/6)*
      ((rat i).den:ℝ)*(Nlen i:ℝ)^2) ≤ K₀) →

    (1 ≤ R) → (R ≤ M) → (T*(N:ℝ)*R^2=M^3) →
    (∀ i∈S, M ≤ A i.1) → (∀ i∈S, A i.1+W i.1 ≤ 2*M) →
    let xlocal := fun i : ℝ × ℤ => z i-(A i.1:ℝ)
    (∀ i∈S, xlocal i∈Ioo (1/2:ℝ) (W i.1-1/2)) →
    (∀ i∈S, gap i∈Gaps) →
    (∀ ab∈Gaps, (vRef ab)*(r ab)-(e ab)*(s ab)=1) →
    (∀ ab∈Gaps, ((0:ℝ) < (r ab) ∧ ((e ab):ℝ)/(r ab)=ab.1) ∨
      (((r ab):ℝ) < 0 ∧ ((e ab):ℝ)/(r ab)=ab.2)) →
    (0 < Bcut) → (∀ ab∈Gaps, (s ab) ≠ 0) →
    (∀ ab∈Gaps, ((e ab):ℝ)/(r ab)∈Refs) →
    (∀ ab∈Gaps, ((vRef ab):ℝ)/(s ab)∈Refs) →
    (∀ a∈Refs, ∀ b∈Refs, a ≠ b → ((Uref:ℝ)/R^2)/4 < |a-b|) →
    (∀ i∈S, xlocal i-(56*(Uref:ℝ)/κ)*(N:ℝ)∈Ioo (1/2:ℝ) (W i.1-1/2)) →
    (∀ i∈S, xlocal i+(56*(Uref:ℝ)/κ)*(N:ℝ)∈Ioo (1/2:ℝ) (W i.1-1/2)) →
    (1 ≤ Uref) →
    (2+168/κ ≤ Bselect) → (7*Bcut ≤ κ*Bselect) →
    (Bselect^2*(Uref:ℝ)^3*R^2 ≤ (N:ℝ)^2) →
    (∀ ab∈Gaps, R^2 ≤ ((r ab):ℝ)^2*(Uref:ℝ)) →
    (∀ ab∈Gaps, ab.2-ab.1 ≤ 7*(Uref:ℝ)/(2*R^2)) →
    (R ≤ (Q:ℝ)) →
    ((Uref:ℝ) ≤ ((N:ℝ)/(Q:ℝ))^((2:ℝ)/3)/Bselect) →
    ((N:ℝ)^10 ≤ M^3*R^7) →
    (∀ i∈S, (rat i:ℝ)∈Icc (gap i).1 (gap i).2) →
    (∀ ab∈Gaps, ab.1∈Refs ∧ ab.2∈Refs ∧ ab.1 < ab.2 ∧
      ∀ t∈Refs, ¬(ab.1 < t ∧ t < ab.2)) →
    (Q:ℝ) ≤ (N:ℝ) →
    ((N:ℝ)^2 ≤ M ∨ (1 ≤ M ∧ (N:ℝ) ≤ T ∧ R^2 ≤ T)) → (Uref:ℝ) ≤ R^2 →
    (∀ ab∈Gaps, |((r ab):ℝ)| ≤ 4*R^2/(Uref:ℝ)) →
    (∀ ab∈Gaps, |((s ab):ℝ)| ≤ 4*R^2/(Uref:ℝ)) →
    (∀ ab∈Gaps, |((e ab):ℝ)| ≤
      (3*Jref*T/(2*σ*M^2)+1)*(4*R^2/(Uref:ℝ))) →
    (∀ ab∈Gaps, |((vRef ab):ℝ)| ≤
      (3*Jref*T/(2*σ*M^2)+1)*(4*R^2/(Uref:ℝ))) →
    let Cphys := σ*(σ+1)+1
    let c := κ/6
    let J := Cphys/6
    let B := max 1 (max (2*Real.sqrt J) (8*J*Real.sqrt J/(3*c)))
    B*R^2/(N:ℝ)^2 ≤ 1/2 →
    (N:ℝ) ≤ R^2 → R ≤ (N:ℝ) → (N:ℝ)^3 ≤ M*R^2 →
    2*R^2 ≤ (Q:ℝ)*(N:ℝ) →
    let H := (N:ℝ)/(Cphys+2)
    2 ≤ (N:ℝ) →
    (∀ i∈S, xlocal i-H∈Ioo (1/2:ℝ) (W i.1-1/2)) →
    (∀ i∈S, xlocal i+H∈Ioo (1/2:ℝ) (W i.1-1/2)) →
    let ε := κ/(16*(Cphys+2)*R^2)
    (∀ i∈S, |(anchor i:ℝ)-(rat i:ℝ)| ≤ ε) →
    (∀ i∈S, 256*((anchor i).den:ℝ) ≤ (Q:ℝ)/3) →
    (∀ i∈S, 256 ≤ (2*ε)*((Q:ℝ)/3)*(anchor i).den) →
    let narrow := fun (i : ℝ × ℤ) =>
      (⌊((rat i).den:ℝ)/(θ*((Q:ℝ)/2))⌋,
       ⌊((rat i).num:ℝ)/(θ*(lambda*(Q:ℝ)/2))⌋)
    let qell := fun (i : ℝ × ℤ) => ((rat i).den:ℝ)*deriv (f (i.1)) (round (z i))
    let V := S ×ˢ (Finset.univ : Finset (Fin 2))
    let offset := fun ip : (ℝ × ℤ) × Fin 2 => ⌊qell ip.1⌋+(ip.2:ℕ)-round (qell ip.1)
    let color := fun ip : (ℝ × ℤ) × Fin 2 => (narrow ip.1,offset ip)
    let NarrowCap := (4/θ+3)*(8*Usrc/(csrc*θ)+3)
    let Cap := 3*NarrowCap

    let q := fun (i : ℝ × ℤ) => (rat i).den
    let μ := fun (i : ℝ × ℤ) => iteratedDeriv 3 (f (i.1)) (round (z i))/6
    let b := fun ip : (ℝ × ℤ) × Fin 2 => (⌊qell ip.1⌋+(ip.2:ℕ) : ℤ)
    let tau := fun ip : (ℝ × ℤ) × Fin 2 => ((b ip:ℝ)-qell ip.1)/2
    let dual := fun (i : ℝ × ℤ) => -2*μ i*(Real.sqrt (2/(3*μ i*(q i:ℝ))))^3
    let x := fun ip : (ℝ × ℤ) × Fin 2 =>
      (![-(v ip.1:ℝ)*b ip/q ip.1,-(v ip.1:ℝ)/q ip.1,
        dual ip.1,3*dual ip.1*tau ip/2] : Fin 4 → ℝ)
    let Fiber := fun key => V.filter (fun ip => color ip=key)
    let μ₀ := csrc*Tsrc/(12*M^3)
    let U₀ := Usrc*Tsrc/(2*M^3)
    let Δtype := (16*U₀/μ₀)*Real.sqrt (U₀*(Q:ℝ)^3)*Real.sqrt K₀/(6*(K₀:ℝ)^2)
    let C₂ := modelPhaseJetCoefficient σ 2+δ
    let C₃ := modelPhaseJetCoefficient σ 3+δ
    let Ct := C₂/2+5*C₃/12
    let Cc := C₂/κ+C₃/(2*κ)
    let Δ := (37*B/2+16*B*Cc+2*Ct+2*Cc)*(Q:ℝ)/(N:ℝ)
    let Ccurv := (4/κ)*(B+2*quarticReciprocalConstant σ δ)
    let D := Δ+quarticNonlinearResidualConstant σ δ*(2*(Q:ℝ))/(N:ℝ)
    let Kres := 4*(37*B/2+16*B*Cc+2*Ct+2*Cc+
      2*quarticNonlinearResidualConstant σ δ)/κ
    let Esize := κ/(16*(Cphys+2))
    let Dbase := 37*B/2+16*B*Cc+2*Ct+2*Cc+2*quarticNonlinearResidualConstant σ δ
    let Tbase := (2/κ)*(B+2*quarticReciprocalConstant σ δ)
    2*3840*128^2*105*(Dbase+64*Tbase*Esize^2) ≤ Bselect*Esize →
    D ≤ 1/2 → Δ < 1/2 → 61*Ccurv*Cphys ≤ Bcut →
    let Lunit := 2*κ/Cphys
    let Gamma := Cphys/κ
    let Cthird := Gamma*(32*Kres+9*quarticReciprocalConstant σ δ)
    let Cpack := 64*Cphys*(Gamma^2*Cthird+Gamma*(modelPhaseJetCoefficient σ 3+δ)/κ)/κ
    let Cfirst := 128*Cphys*(Gamma^2*Cthird+Gamma*(modelPhaseJetCoefficient σ 3+δ)/κ)/κ^2
    let Cgap := 64*Cphys*(Gamma^2*B+Gamma*(modelPhaseJetCoefficient σ 3+δ)/κ)/κ
    let Cmain := 4*(2*Cfirst/Lunit^3)^((3:ℝ)⁻¹)+2
    let Ctail := 4*Cpack/Lunit^2+Cgap
    let Klarge := 60*588*(Uband/lambda)^2*Uband^2*(R^8/(N:ℝ)^4)*
      (Cmain*((Q:ℝ)/(Uband*(N:ℝ)))^((2:ℝ)/3)+Ctail/(Uref:ℝ))
    let Y := S.image Prod.fst
    let Values := fun k : ZMod K₀ =>
      ∑ ip∈V, ‖∑ j : ZMod K₀, ZMod.stdAddChar (-(j*k))*
        GafniTao.fordAdditiveCharacter (∑ d,x ip d*
          (![(j.val+1:ℝ),(j.val+1:ℝ)^2,(j.val+1:ℝ)^((3:ℝ)/2),
            Real.sqrt (j.val+1:ℝ)] : Fin 4 → ℝ) d)‖
    let Wphys := (144*Usrc/(csrc*κ))*(R^2/(Q:ℝ))
    let WeightedValues := fun k : ZMod K₀ =>
      ∑ ip∈V, (Real.sqrt (2*(q ip.1:ℝ))/((q ip.1:ℝ)*Real.sqrt (μ ip.1*(Nlen ip.1:ℝ))))*
        ‖∑ j : ZMod K₀, ZMod.stdAddChar (-(j*k))*
          GafniTao.fordAdditiveCharacter (∑ d,x ip d*
            (![(j.val+1:ℝ),(j.val+1:ℝ)^2,(j.val+1:ℝ)^((3:ℝ)/2),
              Real.sqrt (j.val+1:ℝ)] : Fin 4 → ℝ) d)‖
    let Mass := Vscale*Dtype*(2+θ*(Uband+1/lambda))*(Y.card:ℝ)*(M/(N:ℝ))*(1+Δtype*Jsep)+
      (Y.card:ℝ)^2*Klarge*T^εloss
    ((V.image color).card:ℝ) ≤ Cap ∧
      (∀ k, (Values k)^12 ≤ C*(K₀:ℝ)^((12:ℝ)+εloss)*Cap^11*
        ∑ key∈V.image color, ((Fiber key).card:ℝ)^10*Mass) ∧
      (V.card:ℝ) ≤ 10*(Y.card:ℝ)*(M/(N:ℝ)) ∧
      (∀ k, (Values k)^12 ≤ C*(K₀:ℝ)^((12:ℝ)+εloss)*Cap^11*
        (10*(Y.card:ℝ)*(M/(N:ℝ)))^10*Mass) ∧
      ∀ k, ((WeightedValues k)^12 ≤ Wphys^6*
        (C*(K₀:ℝ)^((12:ℝ)+εloss)*Cap^11*(V.card:ℝ)^10*Mass)) ∧
        (WeightedValues k)^12 ≤ Wphys^6*
          (C*(K₀:ℝ)^((12:ℝ)+εloss)*Cap^11*(10*(Y.card:ℝ)*(M/(N:ℝ)))^10*Mass) := by
  exact eventually_double_difference_actual_family_physical_sieve hcsrc hUsrc hE hσ hεloss

#print axioms eventually_double_difference_actual_family_physical_sieve


/-- Source-derived curvature growth on the enlarged physical interval.
This is the entry needed to construct the actual reference/anchor roots. -/
private theorem double_difference_physical_curvature_growth
    (F : ℝ → ℝ) {r s d y w c U T M x z : ℝ}
    (hr : 0 ≤ r) (hs : 0 ≤ s) (hd : 0 < d)
    (hy : y∈Icc (1:ℝ) 2) (hprod : r*s=d*y)
    (hshift : r+s ≤ w) (hw : w ≤ 1/4) (hsmall : 2*U*w ≤ c/64)
    (hc : 0 < c) (hU : 0 < U) (hT : 0 < T) (hM : 0 < M)
    (hx : x∈Icc (3*M/4) (9*M/4)) (hz : z∈Icc (3*M/4) (9*M/4)) (hxz : x ≤ z)
    (hf : ∀ u, 0 < u → ContDiffAt ℝ ∞ F u)
    (hlower : ∀ u∈Icc (1/2:ℝ) 3, c ≤ iteratedDeriv 5 F u)
    (hjets : ∀ u∈Icc (1/2:ℝ) 3, ∀ n, 1 ≤ n → n ≤ 7 → |iteratedDeriv n F u| ≤ U) :
    let Φ := fun u => (F u-F (u+r)-F (u+s)+F (u+r+s))/d
    let f := fun v => T*Φ (v/M)
    c*T/(4*M^3)*(z-x) ≤ iteratedDeriv 2 f z/2-iteratedDeriv 2 f x/2 := by
  intro Φ f
  let h := fun v => iteratedDeriv 2 f v/2
  have hjet u (hu : u∈Icc (3/4:ℝ) (9/4)) :=
    double_difference_cubic_jet_bounds F hu hy hr hs hd hU hc
      hprod hshift hw hsmall hf hlower hjets
  have hreg u (hu : 0 < u) : ContDiffAt ℝ ∞ Φ u :=
    (hjet 1 (by norm_num)).1 u hu
  have hnorm v (hv : v∈Icc (3*M/4) (9*M/4)) :
      v/M∈Icc (3/4:ℝ) (9/4) := by
    constructor
    · apply (le_div_iff₀ hM).mpr
      linarith only [hv.1]
    · apply (div_le_iff₀ hM).mpr
      linarith only [hv.2]
  have hvpos v (hv : v∈Icc (3*M/4) (9*M/4)) : 0 < v := by
    linarith only [hv.1,hM]
  have hdcurv v (hv : v∈Icc (3*M/4) (9*M/4)) :
      HasDerivAt h (iteratedDeriv 3 f v/2) v := by
    have hcf : ContDiffAt ℝ ∞ f v :=
      contDiffAt_const.mul ((hreg (v/M) (div_pos (hvpos v hv) hM)).comp v
        (contDiffAt_id.div_const M))
    have hh : HasDerivAt (iteratedDeriv 2 f) (iteratedDeriv 3 f v) v := by
      simpa only [iteratedDeriv_succ] using
        ((contDiffAt_iteratedDeriv_infty hcf 2).differentiableAt (by simp)).hasDerivAt
    exact hh.div_const 2
  have hb v (hv : v∈Icc (3*M/4) (9*M/4)) : c*T/(4*M^3) ≤ deriv h v := by
    have ha := sargos_iteratedDeriv_comp_affine_local (f:=Φ)
      (l:=0) (r:=v+1) (c:=M⁻¹) (d:=0)
      (fun u hu => hreg _ (by
        simpa only [add_zero] using mul_pos (inv_pos.mpr hM) hu.1))
      (show v∈Ioo (0:ℝ) (v+1) from ⟨hvpos v hv,by linarith⟩) 3
    have hphysical : iteratedDeriv 3 f v=T/M^3*iteratedDeriv 3 Φ (v/M) := by
      change iteratedDeriv 3 (fun u => T*Φ (u/M)) v=_
      rw [iteratedDeriv_const_mul_field]
      have he : (fun u => Φ (u/M))=(fun u => Φ (M⁻¹*u+0)) := by
        funext u
        congr 1
        ring
      rw [he,ha]
      simp only [add_zero,inv_pow]
      rw [show M⁻¹*v=v/M by ring]
      ring
    rw [(hdcurv v hv).deriv,hphysical]
    calc
      c*T/(4*M^3) = (T/M^3)*(c/2)/2 := by ring
      _ ≤ _ := div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left (hjet _ (hnorm v hv)).2.1 (by positivity)) (by norm_num)
  exact (convex_Icc (3*M/4) (9*M/4)).mul_sub_le_image_sub_of_le_deriv
    (fun v hv => (hdcurv v hv).continuousAt.continuousWithinAt)
    (fun v hv => (hdcurv v (interior_subset hv)).differentiableAt.differentiableWithinAt)
    (fun v hv => hb v (interior_subset hv)) x hx z hz hxz

example
    (F : ℝ → ℝ) {r s d y w c U T M x z : ℝ}
    (hr : 0 ≤ r) (hs : 0 ≤ s) (hd : 0 < d)
    (hy : y∈Icc (1:ℝ) 2) (hprod : r*s=d*y)
    (hshift : r+s ≤ w) (hw : w ≤ 1/4) (hsmall : 2*U*w ≤ c/64)
    (hc : 0 < c) (hU : 0 < U) (hT : 0 < T) (hM : 0 < M)
    (hx : x∈Icc (3*M/4) (9*M/4)) (hz : z∈Icc (3*M/4) (9*M/4)) (hxz : x ≤ z)
    (hf : ∀ u, 0 < u → ContDiffAt ℝ ∞ F u)
    (hlower : ∀ u∈Icc (1/2:ℝ) 3, c ≤ iteratedDeriv 5 F u)
    (hjets : ∀ u∈Icc (1/2:ℝ) 3, ∀ n, 1 ≤ n → n ≤ 7 → |iteratedDeriv n F u| ≤ U) :
    let Φ := fun u => (F u-F (u+r)-F (u+s)+F (u+r+s))/d
    let f := fun v => T*Φ (v/M)
    c*T/(4*M^3)*(z-x) ≤ iteratedDeriv 2 f z/2-iteratedDeriv 2 f x/2 := by
  exact double_difference_physical_curvature_growth F hr hs hd hy hprod hshift hw hsmall hc hU hT hM hx hz hxz
    hf hlower hjets

#print axioms double_difference_physical_curvature_growth

/-- One bounded reference system for the actual selected double phases.
Curvature coverage, roots and gap preimage widths are all source-derived;
the retained rational hull, parents and labels come from the existing
bounded reference construction. -/
private theorem double_difference_constructed_reference_system_bounded
    (F rshift sshift : ℝ → ℝ) (Y : Finset ℝ) {c J d w T M N R U : ℝ}
    (hc : 0 < c) (hJ : 0 < J) (hd : 0 < d)
    (hw : w ≤ 1/4) (hsmallShift : 2*J*w ≤ c/64)
    (hy : ∀ y∈Y, y∈Icc (1:ℝ) 2)
    (hshifts : ∀ y∈Y, 0 ≤ rshift y ∧ 0 ≤ sshift y ∧
      rshift y*sshift y=d*y ∧ rshift y+sshift y ≤ w)
    (hf : ∀ u, 0 < u → ContDiffAt ℝ ∞ F u)
    (hlower : ∀ u∈Icc (1/2:ℝ) 3, c ≤ iteratedDeriv 5 F u)
    (hbound : ∀ u∈Icc (1/2:ℝ) 3, ∀ n, 1 ≤ n → n ≤ 7 → |iteratedDeriv n F u| ≤ J)
    (hnegative : ∀ u∈Icc (1/2:ℝ) 3, iteratedDeriv 4 F u ≤ -c)
    (hT : 0 < T) (hM : 0 < M) (hN : 0 < N) (hR : 0 < R)
    (hU : 0 < U) (hUmax : U ≤ R^2) (hphase : T*N*R^2=M^3) :
    let Φ := fun y u => (F u-F (u+rshift y)-F (u+sshift y)+F (u+rshift y+sshift y))/d
    let f := fun y v => T*Φ y (v/M)
    let h := fun y w => iteratedDeriv 2 (f y) w/2
    let curvatureScale := J*T/M^2
    ∃ H : ℤ, 2 ≤ H ∧ (H:ℝ)<4*R^2/U ∧ ∃ S : Finset ℝ,
      (∀ q : ℚ, (q.den:ℤ) ≤ H → |(q:ℝ)| ≤ curvatureScale → (q:ℝ) ∈ S) ∧
      (∀ a ∈ S, ∀ b ∈ S, ∀ q : ℚ, (q.den:ℤ) ≤ H →
        (q:ℝ) ∈ Icc a b → (q:ℝ) ∈ S) ∧
      (∃ l ∈ S, ∃ u ∈ S, l ≤ -curvatureScale ∧ curvatureScale ≤ u) ∧
      (∀ z ∈ S, |z| ≤ curvatureScale+1) ∧
      (∀ z∈S, ∃ a b : ℤ, z=(a:ℝ)/b ∧ IsCoprime a b ∧ 0 < b ∧
        (b:ℝ)<4*R^2/U ∧ |(a:ℝ)| ≤ (curvatureScale+1)*(4*R^2/U)) ∧
      (∀ y∈Y, ∀ x ∈ Icc M (2*M), |h y x| ≤ curvatureScale) ∧
      (∀ z ∈ S,
        (∃ q : ℚ, z=(q:ℝ) ∧ (q.den:ℤ) ≤ H) ∨
        (∃ m n u v : ℤ, z=(m:ℝ)/n ∧ IsCoprime m n ∧ 0 < n ∧
          R^2 ≤ U*(n:ℝ)^2 ∧ 0 < v ∧ v ≤ H ∧ (u:ℝ)/v ∈ S ∧ |m*v-u*n|=1)) ∧
      (∀ x ∈ S, ∀ z ∈ S, x ≠ z → U/(4*R^2) < |x-z|) ∧
      (∀ y∈Y, ∀ x ∈ Icc M (2*M),
        ∃ q ∈ S, |h y x-q| ≤ 7*U/(4*R^2)) ∧
      (∀ y∈Y, ∀ q ∈ S,
        q ∈ Icc (h y M) (h y (2*M)) →
        ∃ x ∈ Icc M (2*M), h y x=q) ∧
      (∀ a ∈ S, ∀ b ∈ S, a < b →
        (∀ z ∈ S, ¬ (a < z ∧ z < b)) →
        U/(4*R^2) < b-a ∧ b-a ≤ 7*U/(2*R^2) ∧
        (∃ m n u v : ℤ, a=(m:ℝ)/n ∧ b=(u:ℝ)/v ∧
          IsCoprime m n ∧ IsCoprime u v ∧ 0 < n ∧ 0 < v ∧
          R^2 ≤ U*((max n v:ℤ):ℝ)^2) ∧
        (∀ y∈Y, ∀ x ∈ Icc M (2*M), ∀ z ∈ Icc M (2*M),
          h y x=a → h y z=b → |z-x| ≤ (14/c)*U*N)) := by
  intro Φ f h curvatureScale
  let δ := U/R^2
  have hδ : 0 < δ := div_pos hU (sq_pos_of_pos hR)
  have hδmax : δ ≤ 1 := (div_le_one (sq_pos_of_pos hR)).mpr hUmax
  have hcurvpos : 0 ≤ curvatureScale := by dsimp only [curvatureScale]; positivity
  let L : ℤ := Int.floor (-curvatureScale)
  let V : ℤ := Int.floor curvatureScale
  have hLV : L ≤ V := Int.floor_mono (by linarith only [hcurvpos])
  obtain ⟨H,hH,hHbound,hbuild⟩ := exists_source_interval_reference_system_bounded hδ hδmax
  obtain ⟨S,hseed,hpoints,hlabels,hsep,hcover,hgaps,hheight⟩ := hbuild L V hLV
  have hinside x (hx : |x| ≤ curvatureScale) : x ∈ Icc (L:ℝ) ((V:ℝ)+1) := by
    have hxI := abs_le.mp hx
    have hL := Int.floor_le (-curvatureScale)
    have hV := Int.lt_floor_add_one curvatureScale
    change ((L:ℝ) ≤ x ∧ x ≤ (V:ℝ)+1)
    dsimp only [L,V]
    constructor <;> linarith only [hxI.1,hxI.2,hL,hV]
  have houtside x (hx : x ∈ Icc (L:ℝ) ((V:ℝ)+1)) : |x| ≤ curvatureScale+1 := by
    have hL := Int.lt_floor_add_one (-curvatureScale)
    have hV := Int.floor_le curvatureScale
    apply abs_le.mpr
    dsimp only [L,V] at hx
    constructor <;> linarith only [hx.1,hx.2,hL,hV]
  have hheightScale : 4/δ=4*R^2/U := by
    dsimp only [δ]
    rw [div_div_eq_mul_div]
  have hHbound' : (H:ℝ)<4*R^2/U := by simpa only [hheightScale] using hHbound
  have hheight' z (hz : z∈S) :
      ∃ a b : ℤ, z=(a:ℝ)/b ∧ IsCoprime a b ∧ 0 < b ∧
        (b:ℝ)<4*R^2/U ∧ |(a:ℝ)| ≤ (curvatureScale+1)*(4*R^2/U) := by
    obtain ⟨a,b,hval,hcop,hb,hbb,_hnum⟩ := hheight z hz
    have hbR : (0:ℝ) < b := by exact_mod_cast hb
    have hbb' : (b:ℝ)<4*R^2/U := by simpa only [hheightScale] using hbb
    refine ⟨a,b,hval,hcop,hb,hbb',?_⟩
    have hnum : (a:ℝ)=z*(b:ℝ) := (div_eq_iff hbR.ne').mp hval.symm
    rw [hnum,abs_mul,abs_of_pos hbR]
    exact mul_le_mul (houtside z (hpoints z hz)) hbb'.le hbR.le
      (add_nonneg hcurvpos zero_le_one)
  have hscaled (n : ℤ) (hn : 1 ≤ δ*(n:ℝ)^2) : R^2 ≤ U*(n:ℝ)^2 := by
    have hh : 1 ≤ U*(n:ℝ)^2/R^2 := by dsimp only [δ] at hn; convert hn using 1; ring
    simpa only [one_mul] using (le_div_iff₀ (sq_pos_of_pos hR)).mp hh
  have hregQ y (hyY : y∈Y) u (hu : 0 < u) : ContDiffAt ℝ ∞ (Φ y) u := by
    have hsdata := hshifts y hyY
    exact (double_difference_cubic_jet_bounds F
      (by norm_num : (1:ℝ)∈Icc (3/4:ℝ) (9/4)) (hy y hyY)
      hsdata.1 hsdata.2.1 hd hJ hc hsdata.2.2.1 hsdata.2.2.2 hw hsmallShift
      hf hlower hbound).1 u hu
  have hcurv y x (hyY : y∈Y) (hx : x∈Icc M (2*M)) : |h y x| ≤ curvatureScale := by
    have hsdata := hshifts y hyY
    have hpar := hy y hyY
    have hprodpos : 0 < rshift y*sshift y := by
      rw [hsdata.2.2.1]
      exact mul_pos hd (by linarith only [hpar.1])
    have hrp : 0 < rshift y := by nlinarith only [hsdata.1,hsdata.2.1,hprodpos]
    have hsp : 0 < sshift y := by nlinarith only [hsdata.1,hsdata.2.1,hprodpos]
    exact (double_difference_physical_curvature_band F hx hpar hrp hsp hd hc hJ hT hM
      hsdata.2.2.1 (hsdata.2.2.2.trans hw) hf hnegative
      (fun u hu => hbound u hu 4 (by norm_num) (by norm_num))).2
  have hgrow y (hyY : y∈Y) x z (hx : x∈Icc M (2*M)) (hz : z∈Icc M (2*M))
      (hxz : x ≤ z) : c*T/(4*M^3)*(z-x) ≤ h y z-h y x := by
    have hsdata := hshifts y hyY
    apply double_difference_physical_curvature_growth F
      hsdata.1 hsdata.2.1 hd (hy y hyY) hsdata.2.2.1 hsdata.2.2.2 hw hsmallShift
      hc hJ hT hM _ _ hxz hf hlower hbound
    · constructor <;> linarith only [hx.1,hx.2,hM]
    · constructor <;> linarith only [hz.1,hz.2,hM]
  have hLmem : (L:ℝ) ∈ S := by
    have hq := hseed (L:ℚ) (by norm_num; omega)
      (show ((L:ℚ):ℝ) ∈ Icc (L:ℝ) ((V:ℝ)+1) by
        simp only [Rat.cast_intCast]
        have hh : (L:ℝ) ≤ V := by exact_mod_cast hLV
        exact ⟨le_rfl,by linarith only [hh]⟩)
    simpa only [Rat.cast_intCast] using hq
  have hVmem : (V:ℝ)+1 ∈ S := by
    have hq := hseed ((V+1:ℤ):ℚ) (by norm_num; omega)
      (show (((V+1:ℤ):ℚ):ℝ) ∈ Icc (L:ℝ) ((V:ℝ)+1) by
        push_cast
        have hh : (L:ℝ) ≤ V := by exact_mod_cast hLV
        exact ⟨by linarith only [hh],le_rfl⟩)
    simpa using hq
  have hgapLower : δ/4=U/(4*R^2) := by dsimp only [δ]; ring
  have hgapCover : 7*δ/4=7*U/(4*R^2) := by dsimp only [δ]; ring
  have hgapUpper : 7*δ/2=7*U/(2*R^2) := by dsimp only [δ]; ring
  refine ⟨H,hH,hHbound',S,(fun q hqH hq => hseed q hqH (hinside q hq)),
    (fun a ha b hb q hqH hqI => hseed q hqH
      ⟨(hpoints a ha).1.trans hqI.1,hqI.2.trans (hpoints b hb).2⟩),
    ⟨L,hLmem,(V:ℝ)+1,hVmem,Int.floor_le (-curvatureScale),(Int.lt_floor_add_one curvatureScale).le⟩,
    (fun z hz => houtside z (hpoints z hz)),hheight',
    (fun y hy x hx => hcurv y x hy hx),?_,?_,?_,?_,?_⟩
  · intro z hz
    rcases hlabels z hz with hsmall | ⟨m,n,u,v,hval,hcop,hn,hnscale,hv,hvH,huI,hdet⟩
    · exact Or.inl hsmall
    · right
      have hneighbor : (u:ℝ)/v ∈ S := by
        have hq := hseed (Rat.divInt u v)
          ((Int.le_of_dvd hv (Rat.den_dvd u v)).trans hvH)
          (by simpa only [Rat.cast_divInt] using huI)
        simpa only [Rat.cast_divInt] using hq
      exact ⟨m,n,u,v,hval,hcop,hn,hscaled n hnscale,hv,hvH,hneighbor,hdet⟩
  · intro x hx z hz hne
    simpa only [hgapLower] using hsep x hx z hz hne
  · intro y hy x hx
    obtain ⟨q,hq,hnear⟩ := hcover (h y x) (hinside _ (hcurv y x hy hx))
    exact ⟨q,hq,by simpa only [hgapCover] using hnear⟩
  · intro y hy q _hq hqI
    have hcont : ContinuousOn (h y) (Icc M (2*M)) := by
      intro x hx
      have hx0 : 0 < x/M := div_pos (hM.trans_le hx.1) hM
      have hcf : ContDiffAt ℝ 3 (f y) x :=
        (contDiffAt_const.mul ((hregQ y hy (x/M) hx0).comp x
          (contDiffAt_id.div_const M))).of_le
          (ENat.natCast_le_of_coe_top_le_withTop le_rfl 3)
      exact ((hasDerivAt_iteratedDeriv_finite (by norm_num : 2 < 3) hcf).div_const 2).continuousAt.continuousWithinAt
    exact intermediate_value_Icc (by linarith only [hM] : M ≤ 2*M) hcont hqI
  · intro a ha b hb hab hadj
    obtain ⟨hlow,hupp,m,n,u,v,haval,hbval,hcopn,hcopv,hn,hv,hmax⟩ :=
      hgaps a ha b hb hab hadj
    refine ⟨by simpa only [hgapLower] using hlow,by simpa only [hgapUpper] using hupp,
      ⟨m,n,u,v,haval,hbval,hcopn,hcopv,hn,hv,hscaled (max n v) hmax⟩,?_⟩
    intro y hy x hx z hz hxa hzb
    have hxz : x < z := by
      by_contra hn
      have hh := hgrow y hy z x hz hx (le_of_not_gt hn)
      rw [hxa,hzb] at hh
      have hnonneg : 0 ≤ c*T/(4*M^3)*(x-z) :=
        mul_nonneg (by positivity) (sub_nonneg.mpr (le_of_not_gt hn))
      linarith only [hh,hnonneg,hab]
    have hh := hgrow y hy x z hx hz hxz.le
    rw [hxa,hzb] at hh
    have hrate : c*T/(4*M^3)=c/(4*N*R^2) := by
      rw [←hphase]
      field_simp
    have hratepos : 0 < c/(4*N*R^2) := by positivity
    rw [hrate] at hh
    rw [abs_of_pos (sub_pos.mpr hxz)]
    calc
      z-x ≤ (b-a)/(c/(4*N*R^2)) :=
        (le_div_iff₀ hratepos).mpr (by simpa only [mul_comm] using hh)
      _ ≤ (7*U/(2*R^2))/(c/(4*N*R^2)) :=
        div_le_div_of_nonneg_right (by simpa only [hgapUpper] using hupp) hratepos.le
      _ = (14/c)*U*N := by field_simp; ring

example
    (F rshift sshift : ℝ → ℝ) (Y : Finset ℝ) {c J d w T M N R U : ℝ}
    (hc : 0 < c) (hJ : 0 < J) (hd : 0 < d)
    (hw : w ≤ 1/4) (hsmallShift : 2*J*w ≤ c/64)
    (hy : ∀ y∈Y, y∈Icc (1:ℝ) 2)
    (hshifts : ∀ y∈Y, 0 ≤ rshift y ∧ 0 ≤ sshift y ∧
      rshift y*sshift y=d*y ∧ rshift y+sshift y ≤ w)
    (hf : ∀ u, 0 < u → ContDiffAt ℝ ∞ F u)
    (hlower : ∀ u∈Icc (1/2:ℝ) 3, c ≤ iteratedDeriv 5 F u)
    (hbound : ∀ u∈Icc (1/2:ℝ) 3, ∀ n, 1 ≤ n → n ≤ 7 → |iteratedDeriv n F u| ≤ J)
    (hnegative : ∀ u∈Icc (1/2:ℝ) 3, iteratedDeriv 4 F u ≤ -c)
    (hT : 0 < T) (hM : 0 < M) (hN : 0 < N) (hR : 0 < R)
    (hU : 0 < U) (hUmax : U ≤ R^2) (hphase : T*N*R^2=M^3) :
    let Φ := fun y u => (F u-F (u+rshift y)-F (u+sshift y)+F (u+rshift y+sshift y))/d
    let f := fun y v => T*Φ y (v/M)
    let h := fun y w => iteratedDeriv 2 (f y) w/2
    let curvatureScale := J*T/M^2
    ∃ H : ℤ, 2 ≤ H ∧ (H:ℝ)<4*R^2/U ∧ ∃ S : Finset ℝ,
      (∀ q : ℚ, (q.den:ℤ) ≤ H → |(q:ℝ)| ≤ curvatureScale → (q:ℝ) ∈ S) ∧
      (∀ a ∈ S, ∀ b ∈ S, ∀ q : ℚ, (q.den:ℤ) ≤ H →
        (q:ℝ) ∈ Icc a b → (q:ℝ) ∈ S) ∧
      (∃ l ∈ S, ∃ u ∈ S, l ≤ -curvatureScale ∧ curvatureScale ≤ u) ∧
      (∀ z ∈ S, |z| ≤ curvatureScale+1) ∧
      (∀ z∈S, ∃ a b : ℤ, z=(a:ℝ)/b ∧ IsCoprime a b ∧ 0 < b ∧
        (b:ℝ)<4*R^2/U ∧ |(a:ℝ)| ≤ (curvatureScale+1)*(4*R^2/U)) ∧
      (∀ y∈Y, ∀ x ∈ Icc M (2*M), |h y x| ≤ curvatureScale) ∧
      (∀ z ∈ S,
        (∃ q : ℚ, z=(q:ℝ) ∧ (q.den:ℤ) ≤ H) ∨
        (∃ m n u v : ℤ, z=(m:ℝ)/n ∧ IsCoprime m n ∧ 0 < n ∧
          R^2 ≤ U*(n:ℝ)^2 ∧ 0 < v ∧ v ≤ H ∧ (u:ℝ)/v ∈ S ∧ |m*v-u*n|=1)) ∧
      (∀ x ∈ S, ∀ z ∈ S, x ≠ z → U/(4*R^2) < |x-z|) ∧
      (∀ y∈Y, ∀ x ∈ Icc M (2*M),
        ∃ q ∈ S, |h y x-q| ≤ 7*U/(4*R^2)) ∧
      (∀ y∈Y, ∀ q ∈ S,
        q ∈ Icc (h y M) (h y (2*M)) →
        ∃ x ∈ Icc M (2*M), h y x=q) ∧
      (∀ a ∈ S, ∀ b ∈ S, a < b →
        (∀ z ∈ S, ¬ (a < z ∧ z < b)) →
        U/(4*R^2) < b-a ∧ b-a ≤ 7*U/(2*R^2) ∧
        (∃ m n u v : ℤ, a=(m:ℝ)/n ∧ b=(u:ℝ)/v ∧
          IsCoprime m n ∧ IsCoprime u v ∧ 0 < n ∧ 0 < v ∧
          R^2 ≤ U*((max n v:ℤ):ℝ)^2) ∧
        (∀ y∈Y, ∀ x ∈ Icc M (2*M), ∀ z ∈ Icc M (2*M),
          h y x=a → h y z=b → |z-x| ≤ (14/c)*U*N)) := by
  exact double_difference_constructed_reference_system_bounded F rshift sshift Y hc hJ hd hw hsmallShift hy hshifts
    hf hlower hbound hnegative hT hM hN hR hU hUmax hphase

#print axioms double_difference_constructed_reference_system_bounded

/-- Exact all-product arithmetic for the fourth pair's own beta line,
using the direct source-window chart budget. This is not an analytic
moment theorem and does not assert the sharper printed row-four bound. -/
private theorem fourth_pair_direct_clamped_source_window_scales
    {t u : ℝ} (ht : t∈Icc (0:ℝ) 1) (hu : u∈Icc (0:ℝ) 1) :
    let α := (1-t)*(890/3277)+t*(17604372/60424193)
    let h := ((1-t)*2749411+t*3296917)/100000000
    let g₀ := ((1-t)*16756+t*5579)/100000000
    let ν₀ := ((1-t)*11931645+t*15224403)/100000000
    let ν₁ := ((1-t)*11969967+t*14925729)/100000000
    let g := (1-u)*g₀+u*(3*h)
    let ν := (1-u)*ν₀+u*ν₁
    let β := 89/3478+(7441/8695)*α
    1/100000 ≤ g₀ ∧ g₀+1/100000 ≤ 3*h ∧ 1/100000 ≤ h ∧
      8*h+1/100000 ≤ α ∧
      2*α+1/2+(3/2)*g₀-3*h+1/100000 ≤ 4*β ∧
      5*α-1/2+g₀/2-3*h+1/100000 ≤ 4*β ∧
      1/100000 ≤ ν ∧ ν+1/100000 ≤ α ∧
      3*α+1/100000 ≤ 1+g ∧ 7*α+1/100000 ≤ 2+2*g+ν ∧
      5*α-1-g+1/100000 ≤ 3*ν ∧
      4*ν+1/100000 ≤ 6*α-1-g ∧
      1+g+1/100000 ≤ 4*α ∧
      1+g+2*ν+1/100000 ≤ 5*α ∧
      3+3*g+11*ν+1/100000 ≤ 17*α ∧
      7+7*g+27*ν+1/100000 ≤ 41*α ∧
      288*α-144*h+1/10000 ≤ 288*β ∧
      288*α-36*ν+72*g-216*h+1/10000 ≤ 288*β ∧
      648*α-72-216*h-216*ν+1/10000 ≤ 288*β ∧
      24+96*g-216*h+96*α+144*ν+1/10000 ≤ 288*β ∧
      21+87*g-216*h+177*α+33*ν+1/10000 ≤ 288*β ∧
      15+87*g-216*h+207*α+15*ν+1/10000 ≤ 288*β ∧
      12+78*g-216*h+216*α+24*ν+1/10000 ≤ 288*β ∧
      6+78*g-216*h+246*α+6*ν+1/10000 ≤ 288*β ∧
      4+76*g-216*h+268*α-24*ν+1/10000 ≤ 288*β ∧
      72*g-216*h+284*α-24*ν+1/10000 ≤ 288*β := by
  intro α h g₀ ν₀ ν₁ g ν β
  have ht0 := ht.1
  have ht1 := ht.2
  have hu0 := hu.1
  have hu1 := hu.2
  have h00 := mul_nonneg (sub_nonneg.mpr ht1) (sub_nonneg.mpr hu1)
  have h01 := mul_nonneg (sub_nonneg.mpr ht1) hu0
  have h10 := mul_nonneg ht0 (sub_nonneg.mpr hu1)
  have h11 := mul_nonneg ht0 hu0
  dsimp only [α,h,g₀,ν₀,ν₁,g,ν,β]
  repeat' constructor
  all_goals nlinarith only [ht0,ht1,hu0,hu1,h00,h01,h10,h11]

example
    {t u : ℝ} (ht : t∈Icc (0:ℝ) 1) (hu : u∈Icc (0:ℝ) 1) :
    let α := (1-t)*(890/3277)+t*(17604372/60424193)
    let h := ((1-t)*2749411+t*3296917)/100000000
    let g₀ := ((1-t)*16756+t*5579)/100000000
    let ν₀ := ((1-t)*11931645+t*15224403)/100000000
    let ν₁ := ((1-t)*11969967+t*14925729)/100000000
    let g := (1-u)*g₀+u*(3*h)
    let ν := (1-u)*ν₀+u*ν₁
    let β := 89/3478+(7441/8695)*α
    1/100000 ≤ g₀ ∧ g₀+1/100000 ≤ 3*h ∧ 1/100000 ≤ h ∧
      8*h+1/100000 ≤ α ∧
      2*α+1/2+(3/2)*g₀-3*h+1/100000 ≤ 4*β ∧
      5*α-1/2+g₀/2-3*h+1/100000 ≤ 4*β ∧
      1/100000 ≤ ν ∧ ν+1/100000 ≤ α ∧
      3*α+1/100000 ≤ 1+g ∧ 7*α+1/100000 ≤ 2+2*g+ν ∧
      5*α-1-g+1/100000 ≤ 3*ν ∧
      4*ν+1/100000 ≤ 6*α-1-g ∧
      1+g+1/100000 ≤ 4*α ∧
      1+g+2*ν+1/100000 ≤ 5*α ∧
      3+3*g+11*ν+1/100000 ≤ 17*α ∧
      7+7*g+27*ν+1/100000 ≤ 41*α ∧
      288*α-144*h+1/10000 ≤ 288*β ∧
      288*α-36*ν+72*g-216*h+1/10000 ≤ 288*β ∧
      648*α-72-216*h-216*ν+1/10000 ≤ 288*β ∧
      24+96*g-216*h+96*α+144*ν+1/10000 ≤ 288*β ∧
      21+87*g-216*h+177*α+33*ν+1/10000 ≤ 288*β ∧
      15+87*g-216*h+207*α+15*ν+1/10000 ≤ 288*β ∧
      12+78*g-216*h+216*α+24*ν+1/10000 ≤ 288*β ∧
      6+78*g-216*h+246*α+6*ν+1/10000 ≤ 288*β ∧
      4+76*g-216*h+268*α-24*ν+1/10000 ≤ 288*β ∧
      72*g-216*h+284*α-24*ν+1/10000 ≤ 288*β := by
  exact fourth_pair_direct_clamped_source_window_scales ht hu

#print axioms fourth_pair_direct_clamped_source_window_scales


/-- Actual double-phase physical jets for the existing cubic source completion. -/
private theorem double_difference_physical_source_jets
    (F : ℝ → ℝ) {r s d y w c U T M x : ℝ}
    (hr : 0 ≤ r) (hs : 0 ≤ s) (hd : 0 < d)
    (hy : y∈Icc (1:ℝ) 2) (hprod : r*s=d*y)
    (hshift : r+s ≤ w) (hw : w ≤ 1/4) (hsmall : 2*U*w ≤ c/64)
    (hc : 0 < c) (hU : 0 < U) (hT : 0 < T) (hM : 0 < M)
    (hx : x∈Icc (3*M/4) (9*M/4))
    (hf : ∀ u, 0 < u → ContDiffAt ℝ ∞ F u)
    (hlower : ∀ u∈Icc (1/2:ℝ) 3, c ≤ iteratedDeriv 5 F u)
    (hjets : ∀ u∈Icc (1/2:ℝ) 3, ∀ n, 1 ≤ n → n ≤ 7 → |iteratedDeriv n F u| ≤ U) :
    let Φ := fun u => (F u-F (u+r)-F (u+s)+F (u+r+s))/d
    let f := fun v => T*Φ (v/M)
    (∀ v, 0 < v → ContDiffAt ℝ ∞ f v) ∧
      c*T/(2*M^3) ≤ iteratedDeriv 3 f x ∧
      |iteratedDeriv 3 f x| ≤ 3*U*T/M^3 ∧
      |iteratedDeriv 4 f x| ≤ 3*U*T/M^4 := by
  intro Φ f
  have hnorm : x/M∈Icc (3/4:ℝ) (9/4) := by
    constructor
    · apply (le_div_iff₀ hM).mpr
      linarith only [hx.1]
    · apply (div_le_iff₀ hM).mpr
      linarith only [hx.2]
  have hj := double_difference_cubic_jet_bounds F hnorm hy hr hs hd hU hc
    hprod hshift hw hsmall hf hlower hjets
  have hreg v (hv : 0 < v) : ContDiffAt ℝ ∞ f v :=
    contDiffAt_const.mul ((hj.1 (v/M) (div_pos hv hM)).comp v
      (contDiffAt_id.div_const M))
  have hxp : 0 < x := by linarith only [hx.1,hM]
  have hphysical n : iteratedDeriv n f x=T/M^n*iteratedDeriv n Φ (x/M) := by
    have ha := sargos_iteratedDeriv_comp_affine_local (f:=Φ)
      (l:=0) (r:=x+1) (c:=M⁻¹) (d:=0)
      (fun u hu => hj.1 _ (by
        simpa only [add_zero] using mul_pos (inv_pos.mpr hM) hu.1))
      (show x∈Ioo (0:ℝ) (x+1) from ⟨hxp,by linarith⟩) n
    change iteratedDeriv n (fun v => T*Φ (v/M)) x=_
    rw [iteratedDeriv_const_mul_field]
    have he : (fun v => Φ (v/M))=(fun v => Φ (M⁻¹*v+0)) := by
      funext v
      congr 1
      ring
    rw [he,ha]
    simp only [add_zero,inv_pow]
    rw [show M⁻¹*x=x/M by ring]
    ring
  refine ⟨hreg,?_,?_,?_⟩
  · rw [hphysical]
    have hh := mul_le_mul_of_nonneg_left hj.2.1 (show 0 ≤ T/M^3 by positivity)
    convert hh using 1
    ring
  · rw [hphysical,abs_mul,abs_of_pos (show 0 < T/M^3 by positivity)]
    have hh := mul_le_mul_of_nonneg_left hj.2.2.1 (show 0 ≤ T/M^3 by positivity)
    convert hh using 1
    ring
  · rw [hphysical,abs_mul,abs_of_pos (show 0 < T/M^4 by positivity)]
    have hh := mul_le_mul_of_nonneg_left hj.2.2.2 (show 0 ≤ T/M^4 by positivity)
    convert hh using 1
    ring

example
    (F : ℝ → ℝ) {r s d y w c U T M x : ℝ}
    (hr : 0 ≤ r) (hs : 0 ≤ s) (hd : 0 < d)
    (hy : y∈Icc (1:ℝ) 2) (hprod : r*s=d*y)
    (hshift : r+s ≤ w) (hw : w ≤ 1/4) (hsmall : 2*U*w ≤ c/64)
    (hc : 0 < c) (hU : 0 < U) (hT : 0 < T) (hM : 0 < M)
    (hx : x∈Icc (3*M/4) (9*M/4))
    (hf : ∀ u, 0 < u → ContDiffAt ℝ ∞ F u)
    (hlower : ∀ u∈Icc (1/2:ℝ) 3, c ≤ iteratedDeriv 5 F u)
    (hjets : ∀ u∈Icc (1/2:ℝ) 3, ∀ n, 1 ≤ n → n ≤ 7 → |iteratedDeriv n F u| ≤ U) :
    let Φ := fun u => (F u-F (u+r)-F (u+s)+F (u+r+s))/d
    let f := fun v => T*Φ (v/M)
    (∀ v, 0 < v → ContDiffAt ℝ ∞ f v) ∧
      c*T/(2*M^3) ≤ iteratedDeriv 3 f x ∧
      |iteratedDeriv 3 f x| ≤ 3*U*T/M^3 ∧
      |iteratedDeriv 4 f x| ≤ 3*U*T/M^4 := by
  exact double_difference_physical_source_jets F hr hs hd hy hprod hshift hw hsmall hc hU hT hM hx
    hf hlower hjets

#print axioms double_difference_physical_source_jets


/-- Complete the actual selected double-phase source blocks at the SAME supplied
curvature roots; the explicit bad-block sum is retained. This consumes the
existing generic cubic-completion theorem, not a new Fourier framework. -/
private theorem double_difference_chosen_arcs_band_fourier
    {c J : ℝ} (hc : 0 < c) (hJ : 0 < J) :
    ∃ C ≥ (1:ℝ), ∀ (ι : Type*) (S : Finset ι) (F : ℝ → ℝ)
      (y rshift sshift : ι → ℝ) (L : ι → ℤ) (H : ι → ℕ) (r : ι → ℚ) (z : ι → ℝ)
      (N : ℕ) (d w T M R : ℝ),
      1 ≤ N → (∀ i∈S, H i ≤ N) →
      0 < d → w ≤ 1/4 → 2*J*w ≤ c/64 → 0 < T → 0 < M → 0 < R →
      (∀ i∈S, y i∈Icc (1:ℝ) 2) →
      (∀ i∈S, 0 ≤ rshift i ∧ 0 ≤ sshift i ∧
        rshift i*sshift i=d*y i ∧ rshift i+sshift i ≤ w) →
      (∀ i∈S, (L i:ℝ)-2*(N:ℝ)∈Icc M (2*M)) →
      (∀ w, 0 < w → ContDiffAt ℝ ∞ F w) →
      (∀ u∈Icc (1/2:ℝ) 3, ∀ n, 1 ≤ n → n ≤ 7 → |iteratedDeriv n F u| ≤ J) →
      (∀ u∈Icc (1/2:ℝ) 3, c ≤ iteratedDeriv 5 F u) →
      T*(N:ℝ)*R^2=M^3 →
      7*(N:ℝ)+2 ≤ M/4 →
      (3*J)*(6*(N:ℝ)+1)^4 ≤ M*(N:ℝ)*R^2 →
      (3*J/4)*(6*(N:ℝ)+1)^2 ≤ (N:ℝ)*R^2 →
      let f := fun i v => T*((F (v/M)-F (v/M+rshift i)-F (v/M+sshift i)+
        F (v/M+rshift i+sshift i))/d)
      (∀ i∈S, z i∈Ioo ((L i:ℝ)-2*(N:ℝ)-(N:ℝ)/4)
        ((L i:ℝ)-2*(N:ℝ)+(N:ℝ)/4) ∧
        iteratedDeriv 2 (f i) (z i)/2=(r i:ℝ)) →
      let m := fun i => round (z i)
      let A := fun i => (L i-m i).toNat
      let q := fun i => (r i).den
      let μ := fun i => iteratedDeriv 3 (f i) (m i)/6
      let ℓ := fun i => deriv (f i) (m i)
      let lambda := c/(12*(N:ℝ)*R^2)
      let U₃ := J/(2*(N:ℝ)*R^2)
      let G := S.filter (fun i => q i ≤ N ∧ 1 ≤ lambda*(q i:ℝ)^2*N)
      (∀ i∈S, |z i-(m i:ℝ)| ≤ 1/2 ∧
        N ≤ A i ∧ A i ≤ 3*N ∧ m i+(A i:ℤ)=L i) ∧
      (∀ i∈G, 1 ≤ A i ∧ q i ≤ A i ∧ 1 ≤ μ i*(q i:ℝ)^2*A i) ∧
      ∀ Q₀ : ℕ, (∀ i∈G, q i ≤ Q₀) →
      ∀ (K₀ : ℕ) [NeZero K₀], 63*U₃*(Q₀:ℝ)*(N:ℝ)^2 ≤ K₀ →
      (∀ i∈G, 7*(μ i*(q i:ℝ)*(A i:ℝ)^2) ≤ K₀) ∧
      ∃ v : ι → ℤ, (∀ i∈G, (q i:ℤ) ∣ (r i).num*v i-1) ∧
      let b := fun i (p : Fin 2) => (⌊(q i:ℝ)*ℓ i⌋+(p:ℕ) : ℤ)
      let τ := fun i p => ((b i p:ℝ)-(q i:ℝ)*ℓ i)/2
      let s := fun i => Real.sqrt (2/(3*μ i*(q i:ℝ)))
      let K := fun i => -2*μ i*(s i)^3
      let x := fun i p =>
        (![-(v i:ℝ)*b i p/q i,-(v i:ℝ)/q i,K i,3*K i*τ i p/2] : Fin 4 → ℝ)
      ∃ k : ZMod K₀,
        (∑ i∈S, ‖∑ n∈Finset.Ioc (L i) (L i+H i),(𝐞 (f i n):ℂ)‖) ≤
          C*((∑ i∈S.filter (fun i => ¬ (q i ≤ N ∧ 1 ≤ lambda*(q i:ℝ)^2*N)),(H i:ℝ))+
            (1+Real.log K₀)*
            (∑ i∈G, ∑ p : Fin 2,
              (Real.sqrt (2*(q i:ℝ))/((q i:ℝ)*Real.sqrt (μ i*A i)))*
              ‖∑ j : ZMod K₀,ZMod.stdAddChar (-(j*k))*
                GafniTao.fordAdditiveCharacter (∑ d,x i p d*
                  (![(j.val+1:ℝ),(j.val+1:ℝ)^2,(j.val+1:ℝ)^((3:ℝ)/2),
                    Real.sqrt (j.val+1:ℝ)] : Fin 4 → ℝ) d)‖)+
            ∑ i∈G, (Real.sqrt (A i)*Real.log (2*(A i:ℝ))+1/(μ i*(A i:ℝ)^2))) := by
  classical
  obtain ⟨C,hC,hentry⟩ := TaoTrudgianYang2025.exists_bourgain_C4_variable_source_common_fourier
  refine ⟨C,hC,?_⟩
  intro ι S F y rshift sshift L H r z N d w T M R hN hH hd hw hsmall hT hM hR hy hshifts
    hbase hf hbound hlower hphase hbuffer hfourBudget hquadBudget f hroots m A q μ ℓ lambda U₃ G
  have hNp : (0:ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hlambda : 0 < lambda := by dsimp only [lambda]; positivity
  have hU₃ : 0 < U₃ := by dsimp only [U₃]; positivity
  let beta := 3*J/(M*(N:ℝ)*R^2)
  have hbeta : 0 ≤ beta := by dsimp only [beta]; positivity
  have hdata i (hi : i∈S) v (hv : v∈Icc (3*M/4) (9*M/4)) :=
    double_difference_physical_source_jets F (hshifts i hi).1 (hshifts i hi).2.1 hd
      (hy i hi) (hshifts i hi).2.2.1 (hshifts i hi).2.2.2 hw hsmall
      hc hJ hT hM hv hf hlower hbound
  have hcf i (hi : i∈S) v (hv : v∈Icc (3*M/4) (9*M/4)) :
      ContDiffAt ℝ ∞ (f i) v :=
    (hdata i hi v hv).1 v (by linarith only [hv.1,hM])
  have hscale3 : T/M^3=1/((N:ℝ)*R^2) := by
    apply (div_eq_div_iff (by positivity) (by positivity)).mpr
    nlinarith only [hphase]
  have hscale4 : T/M^4=1/(M*(N:ℝ)*R^2) := by
    apply (div_eq_div_iff (by positivity) (by positivity)).mpr
    calc
      T*(M*(N:ℝ)*R^2)=M*(T*(N:ℝ)*R^2) := by ring
      _ = M*M^3 := by rw [hphase]
      _ = 1*M^4 := by ring
  have hthree i (hi : i∈S) v (hv : v∈Icc (3*M/4) (9*M/4)) :
      6*lambda ≤ iteratedDeriv 3 (f i) v ∧ iteratedDeriv 3 (f i) v ≤ 6*U₃ := by
    have hh := hdata i hi v hv
    constructor
    · calc
        6*lambda = (c/2)*(T/M^3) := by rw [hscale3]; dsimp only [lambda]; ring
        _ = c*T/(2*M^3) := by ring
        _ ≤ _ := hh.2.1
    · calc
        _ ≤ |iteratedDeriv 3 (f i) v| := le_abs_self _
        _ ≤ 3*J*T/M^3 := hh.2.2.1
        _ = 3*J*(T/M^3) := by ring
        _ = 6*U₃ := by rw [hscale3]; dsimp only [U₃]; ring
  have hfour i (hi : i∈S) v (hv : v∈Icc (3*M/4) (9*M/4)) :
      |iteratedDeriv 4 (f i) v| ≤ beta := by
    calc
      _ ≤ 3*J*T/M^4 := (hdata i hi v hv).2.2.2
      _ = 3*J*(T/M^4) := by ring
      _ = beta := by rw [hscale4]; dsimp only [beta]; ring
  have hgeo i (hi : i∈S) :
      z i∈Ioo (3*M/4) (9*M/4) ∧ |z i-(m i:ℝ)| ≤ 1/2 ∧
      ((N:ℤ) ≤ L i-m i ∧ L i-m i ≤ 3*(N:ℤ)) ∧
      Icc ((m i:ℝ)-(6*(N:ℝ)+1)) ((m i:ℝ)+(6*(N:ℝ)+1)) ⊆ Icc (3*M/4) (9*M/4) := by
    apply TaoTrudgianYang2025.bourgain_minimal_arc_rounded_source_geometry
      (show 0 < N by omega) (by ring) (hroots i hi).1
    intro w hw
    have hb := hbase i hi
    constructor <;> linarith only [hb.1,hb.2,hw.1,hw.2,hbuffer]
  have hA i (hi : i∈S) : N ≤ A i ∧ A i ≤ 3*N ∧ m i+(A i:ℤ)=L i := by
    have hg := (hgeo i hi).2.2.1
    have hnonneg : 0 ≤ L i-m i := (Int.natCast_nonneg N).trans hg.1
    have he : (A i:ℤ)=L i-m i := Int.toNat_of_nonneg hnonneg
    refine ⟨?_,?_,?_⟩
    · exact_mod_cast (show (N:ℤ) ≤ (A i:ℤ) by rw [he]; exact hg.1)
    · exact_mod_cast (show (A i:ℤ) ≤ 3*(N:ℤ) by rw [he]; exact hg.2)
    · omega
  have hm i (hi : i∈S) : (m i:ℝ)∈Icc (3*M/4) (9*M/4) :=
    (hgeo i hi).2.2.2 ⟨by linarith only [hNp],by linarith only [hNp]⟩
  have hmu i (hi : i∈S) : 0 < μ i ∧ lambda ≤ μ i ∧ μ i ≤ U₃ := by
    have hh := hthree i hi (m i) (hm i hi)
    change 0 < iteratedDeriv 3 (f i) (m i)/6 ∧
      lambda ≤ iteratedDeriv 3 (f i) (m i)/6 ∧ iteratedDeriv 3 (f i) (m i)/6 ≤ U₃
    constructor
    · linarith only [hh.1,hlambda]
    · constructor <;> linarith only [hh.1,hh.2]
  have hsmall i (hi : i∈S) :
      beta*(2*(A i:ℝ)+1)^4 ≤ 1 ∧ (3*U₃/2)*(2*(A i:ℝ)+1)^2 ≤ 1 := by
    have hAr : (A i:ℝ) ≤ 3*(N:ℝ) := by exact_mod_cast (hA i hi).2.1
    have ha : 2*(A i:ℝ)+1 ≤ 6*(N:ℝ)+1 := by linarith only [hAr]
    have hb : beta*(6*(N:ℝ)+1)^4 ≤ 1 := by
      have hh := (div_le_one (show 0 < M*(N:ℝ)*R^2 by positivity)).mpr hfourBudget
      convert hh using 1
      dsimp only [beta]
      ring
    have hd : (3*U₃/2)*(6*(N:ℝ)+1)^2 ≤ 1 := by
      have hh := (div_le_one (show 0 < (N:ℝ)*R^2 by positivity)).mpr hquadBudget
      convert hh using 1
      dsimp only [U₃]
      ring
    exact ⟨(mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) ha 4) hbeta).trans hb,
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) ha 2) (by positivity)).trans hd⟩
  have hsub i (hi : i∈S) :
      Icc ((m i:ℝ)-(2*(A i:ℝ)+1)) ((m i:ℝ)+(2*(A i:ℝ)+1)) ⊆ Icc (3*M/4) (9*M/4) := by
    intro w hw
    apply (hgeo i hi).2.2.2
    have ha : (A i:ℝ) ≤ 3*(N:ℝ) := by exact_mod_cast (hA i hi).2.1
    constructor <;> linarith only [hw.1,hw.2,ha]
  have hcurv i (hi : i∈S) :
      |iteratedDeriv 2 (f i) (m i)/2-((r i).num:ℝ)/(q i:ℝ)| ≤ 3*U₃/2 := by
    have hh := TaoTrudgianYang2025.bourgain_curvature_level_difference (f i)
      (fun w hw => (hcf i hi w hw).of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 4))
      (fun w hw => ⟨(by linarith only [(hthree i hi w hw).1,hlambda]),(hthree i hi w hw).2⟩)
      (hm i hi) ⟨(hgeo i hi).1.1.le,(hgeo i hi).1.2.le⟩
    rw [(hroots i hi).2] at hh
    have hr := mul_le_mul_of_nonneg_left (hgeo i hi).2.1 (show 0 ≤ 3*U₃ by positivity)
    have he : (r i:ℝ)=((r i).num:ℝ)/(q i:ℝ) := by rw [Rat.cast_def]
    rw [he,abs_sub_comm (m i:ℝ) (z i)] at hh
    exact hh.trans (by linarith only [hr])
  have hGS : G ⊆ S := fun i hi => (Finset.mem_filter.mp hi).1
  have hscale i (hi : i∈G) :
      0 < q i ∧ q i ≤ A i ∧ IsCoprime (r i).num (q i:ℤ) ∧
      0 < μ i ∧ μ i*(A i:ℝ)^2 ≤ 1 ∧ 1 ≤ μ i*(q i:ℝ)^2*A i := by
    have hiS := hGS hi
    have hd := (Finset.mem_filter.mp hi).2
    have hmu' := hmu i hiS
    refine ⟨(r i).pos,hd.1.trans (hA i hiS).1,(r i).isCoprime_num_den,hmu'.1,?_,?_⟩
    · calc
        _ ≤ U₃*(2*(A i:ℝ)+1)^2 :=
          mul_le_mul hmu'.2.2
            (pow_le_pow_left₀ (show (0:ℝ) ≤ A i from Nat.cast_nonneg _)
              (show (A i:ℝ) ≤ 2*(A i:ℝ)+1 by linarith [show (0:ℝ) ≤ A i from Nat.cast_nonneg _]) 2)
            (sq_nonneg _) hU₃.le
        _ ≤ (3*U₃/2)*(2*(A i:ℝ)+1)^2 := by gcongr; linarith only [hU₃]
        _ ≤ _ := (hsmall i hiS).2
    · have hAr : (N:ℝ) ≤ A i := by exact_mod_cast (hA i hiS).1
      exact hd.2.trans (mul_le_mul
        (mul_le_mul_of_nonneg_right hmu'.2.1 (sq_nonneg (q i:ℝ))) hAr hNp.le
        (mul_nonneg hmu'.1.le (sq_nonneg _)))
  refine ⟨(fun i hi => ⟨(hgeo i hi).2.1,hA i hi⟩),
    (fun i hi => ⟨hN.trans (hA i (hGS hi)).1,(hscale i hi).2.1,
      (hscale i hi).2.2.2.2.2⟩),?_⟩
  intro Q₀ hQ₀ K₀ inst hK₀
  have hKG i (hi : i∈G) : 7*(μ i*(q i:ℝ)*(A i:ℝ)^2) ≤ K₀ := by
    have hiS := hGS hi
    have hAr : (A i:ℝ) ≤ 3*(N:ℝ) := by exact_mod_cast (hA i hiS).2.1
    have hqr : (q i:ℝ) ≤ Q₀ := by exact_mod_cast hQ₀ i hi
    calc
      _ ≤ 7*(U₃*(Q₀:ℝ)*(3*(N:ℝ))^2) := by gcongr; exact (hmu i hiS).2.2
      _ = 63*U₃*(Q₀:ℝ)*(N:ℝ)^2 := by ring
      _ ≤ _ := hK₀
  refine ⟨hKG,?_⟩
  obtain ⟨v,hv,hfourier⟩ := hentry ι G f (fun i => (m i:ℝ)) (fun i => (r i).num) q A H
    (fun i hi => hN.trans (hA i (hGS hi)).1)
    (fun i hi => (hH i (hGS hi)).trans (hA i (hGS hi)).1)
    beta (3*U₃/2) hbeta (by positivity)
    (fun i hi => (hsmall i (hGS hi)).1) (fun i hi => (hsmall i (hGS hi)).2)
    (fun i hi w hw => (hcf i (hGS hi) w (hsub i (hGS hi) hw)).of_le
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl 4))
    (fun i hi v hv => hfour i (hGS hi) v (hsub i (hGS hi) hv))
    (fun i hi => hcurv i (hGS hi)) hscale K₀ hKG
  refine ⟨v,hv,?_⟩
  intro b τ s K x
  obtain ⟨k,hk⟩ := hfourier
  refine ⟨k,?_⟩
  let Src := fun i => ‖∑ n∈Finset.Ioc (L i) (L i+H i),(𝐞 (f i n):ℂ)‖
  have hsrc :
      (∑ i∈G,Src i) =
        ∑ i∈G, ‖∑ n∈Finset.Ioc (A i:ℤ) ((A i:ℤ)+H i),(𝐞 (f i ((m i:ℝ)+n)):ℂ)‖ := by
    apply Finset.sum_congr rfl
    intro i hi
    dsimp only [Src]
    rw [←(hA i (hGS hi)).2.2,TaoTrudgianYang2025.bourgain_integer_source_translation]
  rw [←hsrc] at hk
  let Bad := S.filter (fun i => ¬ (q i ≤ N ∧ 1 ≤ lambda*(q i:ℝ)^2*N))
  have hbad : (∑ i∈Bad,Src i) ≤ ∑ i∈Bad,(H i:ℝ) := by
    apply Finset.sum_le_sum
    intro i _hi
    dsimp only [Src]
    apply (norm_sum_le _ _).trans_eq
    simp
  have hbad0 : 0 ≤ ∑ i∈Bad,(H i:ℝ) :=
    Finset.sum_nonneg (fun i _ => Nat.cast_nonneg (H i))
  have hbadC := mul_le_mul_of_nonneg_right hC hbad0
  simp only [one_mul] at hbadC
  have hsplit : (∑ i∈S,Src i)=(∑ i∈G,Src i)+(∑ i∈Bad,Src i) :=
    (Finset.sum_filter_add_sum_filter_not S
      (fun i => q i ≤ N ∧ 1 ≤ lambda*(q i:ℝ)^2*N) Src).symm
  change (∑ i∈S,Src i) ≤ _
  rw [hsplit]
  have hh := add_le_add hk (hbad.trans hbadC)
  convert hh using 1
  dsimp only [Bad]
  ring

example
    {c J : ℝ} (hc : 0 < c) (hJ : 0 < J) :
    ∃ C ≥ (1:ℝ), ∀ (ι : Type*) (S : Finset ι) (F : ℝ → ℝ)
      (y rshift sshift : ι → ℝ) (L : ι → ℤ) (H : ι → ℕ) (r : ι → ℚ) (z : ι → ℝ)
      (N : ℕ) (d w T M R : ℝ),
      1 ≤ N → (∀ i∈S, H i ≤ N) →
      0 < d → w ≤ 1/4 → 2*J*w ≤ c/64 → 0 < T → 0 < M → 0 < R →
      (∀ i∈S, y i∈Icc (1:ℝ) 2) →
      (∀ i∈S, 0 ≤ rshift i ∧ 0 ≤ sshift i ∧
        rshift i*sshift i=d*y i ∧ rshift i+sshift i ≤ w) →
      (∀ i∈S, (L i:ℝ)-2*(N:ℝ)∈Icc M (2*M)) →
      (∀ w, 0 < w → ContDiffAt ℝ ∞ F w) →
      (∀ u∈Icc (1/2:ℝ) 3, ∀ n, 1 ≤ n → n ≤ 7 → |iteratedDeriv n F u| ≤ J) →
      (∀ u∈Icc (1/2:ℝ) 3, c ≤ iteratedDeriv 5 F u) →
      T*(N:ℝ)*R^2=M^3 →
      7*(N:ℝ)+2 ≤ M/4 →
      (3*J)*(6*(N:ℝ)+1)^4 ≤ M*(N:ℝ)*R^2 →
      (3*J/4)*(6*(N:ℝ)+1)^2 ≤ (N:ℝ)*R^2 →
      let f := fun i v => T*((F (v/M)-F (v/M+rshift i)-F (v/M+sshift i)+
        F (v/M+rshift i+sshift i))/d)
      (∀ i∈S, z i∈Ioo ((L i:ℝ)-2*(N:ℝ)-(N:ℝ)/4)
        ((L i:ℝ)-2*(N:ℝ)+(N:ℝ)/4) ∧
        iteratedDeriv 2 (f i) (z i)/2=(r i:ℝ)) →
      let m := fun i => round (z i)
      let A := fun i => (L i-m i).toNat
      let q := fun i => (r i).den
      let μ := fun i => iteratedDeriv 3 (f i) (m i)/6
      let ℓ := fun i => deriv (f i) (m i)
      let lambda := c/(12*(N:ℝ)*R^2)
      let U₃ := J/(2*(N:ℝ)*R^2)
      let G := S.filter (fun i => q i ≤ N ∧ 1 ≤ lambda*(q i:ℝ)^2*N)
      (∀ i∈S, |z i-(m i:ℝ)| ≤ 1/2 ∧
        N ≤ A i ∧ A i ≤ 3*N ∧ m i+(A i:ℤ)=L i) ∧
      (∀ i∈G, 1 ≤ A i ∧ q i ≤ A i ∧ 1 ≤ μ i*(q i:ℝ)^2*A i) ∧
      ∀ Q₀ : ℕ, (∀ i∈G, q i ≤ Q₀) →
      ∀ (K₀ : ℕ) [NeZero K₀], 63*U₃*(Q₀:ℝ)*(N:ℝ)^2 ≤ K₀ →
      (∀ i∈G, 7*(μ i*(q i:ℝ)*(A i:ℝ)^2) ≤ K₀) ∧
      ∃ v : ι → ℤ, (∀ i∈G, (q i:ℤ) ∣ (r i).num*v i-1) ∧
      let b := fun i (p : Fin 2) => (⌊(q i:ℝ)*ℓ i⌋+(p:ℕ) : ℤ)
      let τ := fun i p => ((b i p:ℝ)-(q i:ℝ)*ℓ i)/2
      let s := fun i => Real.sqrt (2/(3*μ i*(q i:ℝ)))
      let K := fun i => -2*μ i*(s i)^3
      let x := fun i p =>
        (![-(v i:ℝ)*b i p/q i,-(v i:ℝ)/q i,K i,3*K i*τ i p/2] : Fin 4 → ℝ)
      ∃ k : ZMod K₀,
        (∑ i∈S, ‖∑ n∈Finset.Ioc (L i) (L i+H i),(𝐞 (f i n):ℂ)‖) ≤
          C*((∑ i∈S.filter (fun i => ¬ (q i ≤ N ∧ 1 ≤ lambda*(q i:ℝ)^2*N)),(H i:ℝ))+
            (1+Real.log K₀)*
            (∑ i∈G, ∑ p : Fin 2,
              (Real.sqrt (2*(q i:ℝ))/((q i:ℝ)*Real.sqrt (μ i*A i)))*
              ‖∑ j : ZMod K₀,ZMod.stdAddChar (-(j*k))*
                GafniTao.fordAdditiveCharacter (∑ d,x i p d*
                  (![(j.val+1:ℝ),(j.val+1:ℝ)^2,(j.val+1:ℝ)^((3:ℝ)/2),
                    Real.sqrt (j.val+1:ℝ)] : Fin 4 → ℝ) d)‖)+
            ∑ i∈G, (Real.sqrt (A i)*Real.log (2*(A i:ℝ))+1/(μ i*(A i:ℝ)^2))) := by
  exact double_difference_chosen_arcs_band_fourier hc hJ

#print axioms double_difference_chosen_arcs_band_fourier


/-- A dyadic rational centre for the SAME actual double phase, with derived N/16 displacement. -/
private theorem double_difference_dyadic_anchor_center
    (F : ℝ → ℝ) {Q : ℕ} {a : ℚ} {r s d y w c U T M N R x : ℝ}
    (hr : 0 ≤ r) (hs : 0 ≤ s) (hd : 0 < d)
    (hy : y∈Icc (1:ℝ) 2) (hprod : r*s=d*y)
    (hshift : r+s ≤ w) (hw : w ≤ 1/4) (hsmall : 2*U*w ≤ c/64)
    (hc : 0 < c) (hU : 0 < U) (hT : 0 < T) (hM : 0 < M)
    (hN : 0 < N) (hR : 0 < R) (hNM : N ≤ M)
    (hphase : T*N*R^2=M^3)
    (hx : x∈Icc (7*M/8) (17*M/8))
    (hf : ∀ u, 0 < u → ContDiffAt ℝ ∞ F u)
    (hlower : ∀ u∈Icc (1/2:ℝ) 3, c ≤ iteratedDeriv 5 F u)
    (hjets : ∀ u∈Icc (1/2:ℝ) 3, ∀ n, 1 ≤ n → n ≤ 7 → |iteratedDeriv n F u| ≤ U)
    (hcut : 2*a.den ≤ Q) (hmajor : 128*R^2 ≤ c*(Q:ℝ)*a.den) :
    let Φ := fun u => (F u-F (u+r)-F (u+s)+F (u+r+s))/d
    let f := fun v => T*Φ (v/M)
    iteratedDeriv 2 f x/2=(a:ℝ) →
    ∃ b : ℚ, b.den ≤ Q ∧ Q ≤ 2*b.den ∧
      (a:ℝ) < b ∧ |(b:ℝ)-(a:ℝ)| ≤ c/(64*R^2) ∧
      ∃ z∈Icc x (x+N/16), iteratedDeriv 2 f z/2=(b:ℝ) := by
  intro Φ f hlevel
  let ε := c/(32*R^2)
  have hε : 0 < ε := by dsimp only [ε]; positivity
  have hmajor' : 4 ≤ ε*(Q:ℝ)*a.den := by
    dsimp only [ε]
    rw [div_mul_eq_mul_div,div_mul_eq_mul_div]
    apply (le_div_iff₀ (by positivity : 0 < 32*R^2)).mpr
    nlinarith only [hmajor]
  obtain ⟨b,hb,hbhalf,hab,hclose,_⟩ := exists_dyadic_rational_near_anchor hcut hmajor'
  have hclose' : |(b:ℝ)-(a:ℝ)| ≤ c/(64*R^2) := by
    convert hclose using 1
    dsimp only [ε]
    ring
  let g := fun v => iteratedDeriv 2 f v/2
  have hxwide : x∈Icc (3*M/4) (9*M/4) := by
    constructor <;> linarith only [hx.1,hx.2,hM]
  have hUwide : x+N/16∈Icc (3*M/4) (9*M/4) := by
    constructor <;> linarith only [hx.1,hx.2,hM,hN,hNM]
  have hinc := double_difference_physical_curvature_growth F hr hs hd hy hprod
    hshift hw hsmall hc hU hT hM hxwide hUwide
    (show x ≤ x+N/16 by linarith only [hN]) hf hlower hjets
  have hrate : (c*T/(4*M^3))*(N/16)=c/(64*R^2) := by
    rw [←hphase]
    field_simp
    ring
  rw [add_sub_cancel_left,hrate] at hinc
  have hsub : Icc x (x+N/16) ⊆ Icc (3*M/4) (9*M/4) :=
    Icc_subset_Icc hxwide.1 hUwide.2
  have htarget : (b:ℝ)∈Icc (g x) (g (x+N/16)) := by
    change (b:ℝ)∈Icc (iteratedDeriv 2 f x/2) (g (x+N/16))
    rw [hlevel]
    refine ⟨hab.le,?_⟩
    change c/(64*R^2) ≤ g (x+N/16)-iteratedDeriv 2 f x/2 at hinc
    rw [hlevel] at hinc
    linarith only [hinc,(abs_le.mp hclose').2]
  have hreg := (double_difference_physical_source_jets F hr hs hd hy hprod
    hshift hw hsmall hc hU hT hM hxwide hf hlower hjets).1
  have hcont : ContinuousOn g (Icc x (x+N/16)) := by
    intro v hv
    have hv0 : 0 < v := by linarith only [(hsub hv).1,hM]
    exact ((contDiffAt_iteratedDeriv_infty (hreg v hv0) 2).continuousAt.div_const 2).continuousWithinAt
  obtain ⟨z,hz,hzlevel⟩ := intermediate_value_Icc
    (show x ≤ x+N/16 by linarith only [hN]) hcont htarget
  exact ⟨b,hb,hbhalf,hab,hclose',z,hz,hzlevel⟩

example
    (F : ℝ → ℝ) {Q : ℕ} {a : ℚ} {r s d y w c U T M N R x : ℝ}
    (hr : 0 ≤ r) (hs : 0 ≤ s) (hd : 0 < d)
    (hy : y∈Icc (1:ℝ) 2) (hprod : r*s=d*y)
    (hshift : r+s ≤ w) (hw : w ≤ 1/4) (hsmall : 2*U*w ≤ c/64)
    (hc : 0 < c) (hU : 0 < U) (hT : 0 < T) (hM : 0 < M)
    (hN : 0 < N) (hR : 0 < R) (hNM : N ≤ M)
    (hphase : T*N*R^2=M^3)
    (hx : x∈Icc (7*M/8) (17*M/8))
    (hf : ∀ u, 0 < u → ContDiffAt ℝ ∞ F u)
    (hlower : ∀ u∈Icc (1/2:ℝ) 3, c ≤ iteratedDeriv 5 F u)
    (hjets : ∀ u∈Icc (1/2:ℝ) 3, ∀ n, 1 ≤ n → n ≤ 7 → |iteratedDeriv n F u| ≤ U)
    (hcut : 2*a.den ≤ Q) (hmajor : 128*R^2 ≤ c*(Q:ℝ)*a.den) :
    let Φ := fun u => (F u-F (u+r)-F (u+s)+F (u+r+s))/d
    let f := fun v => T*Φ (v/M)
    iteratedDeriv 2 f x/2=(a:ℝ) →
    ∃ b : ℚ, b.den ≤ Q ∧ Q ≤ 2*b.den ∧
      (a:ℝ) < b ∧ |(b:ℝ)-(a:ℝ)| ≤ c/(64*R^2) ∧
      ∃ z∈Icc x (x+N/16), iteratedDeriv 2 f z/2=(b:ℝ) := by
  exact double_difference_dyadic_anchor_center F hr hs hd hy hprod hshift hw hsmall hc hU hT hM
    hN hR hNM hphase hx hf hlower hjets hcut hmajor

#print axioms double_difference_dyadic_anchor_center

/-- Construct dyadic centres and complete the SAME actual double-phase family;
all selected blocks meet the analytic minor-arc conditions, derived from source scales. -/
private theorem double_difference_dyadic_anchor_source_fourier
    {c J : ℝ} (hc : 0 < c) (hJ : 0 < J) :
    ∃ C ≥ (1:ℝ), ∀ (ι : Type*) (S : Finset ι) (F : ℝ → ℝ)
      (y rshift sshift : ι → ℝ) (L : ι → ℤ) (H : ι → ℕ) (anchor : ι → ℚ) (za : ι → ℝ)
      (N Q : ℕ) (d w T M R : ℝ),
      1 ≤ N → (∀ i∈S, H i ≤ N) →
      0 < d → w ≤ 1/4 → 2*J*w ≤ c/64 → 0 < T → 0 < M → 0 < R →
      (∀ i∈S, y i∈Icc (1:ℝ) 2) →
      (∀ i∈S, 0 ≤ rshift i ∧ 0 ≤ sshift i ∧
        rshift i*sshift i=d*y i ∧ rshift i+sshift i ≤ w) →
      (∀ i∈S, (L i:ℝ)-2*(N:ℝ)∈Icc M (2*M)) →
      (∀ w, 0 < w → ContDiffAt ℝ ∞ F w) →
      (∀ u∈Icc (1/2:ℝ) 3, ∀ n, 1 ≤ n → n ≤ 7 → |iteratedDeriv n F u| ≤ J) →
      (∀ u∈Icc (1/2:ℝ) 3, c ≤ iteratedDeriv 5 F u) →
      T*(N:ℝ)*R^2=M^3 →
      7*(N:ℝ)+2 ≤ M/4 →
      (3*J)*(6*(N:ℝ)+1)^4 ≤ M*(N:ℝ)*R^2 →
      (3*J/4)*(6*(N:ℝ)+1)^2 ≤ (N:ℝ)*R^2 →
      Q ≤ N → (∀ i∈S, 2*(anchor i).den ≤ Q) →
      (∀ i∈S, 128*R^2 ≤ c*(Q:ℝ)*(anchor i).den) →
      let f := fun i v => T*((F (v/M)-F (v/M+rshift i)-F (v/M+sshift i)+
        F (v/M+rshift i+sshift i))/d)
      (∀ i∈S, za i∈Ioo ((L i:ℝ)-2*(N:ℝ)-(N:ℝ)/8)
        ((L i:ℝ)-2*(N:ℝ)+(N:ℝ)/8) ∧
        iteratedDeriv 2 (f i) (za i)/2=(anchor i:ℝ)) →
      ∃ (r : ι → ℚ) (z : ι → ℝ),
      (∀ i∈S, (r i).den ≤ Q ∧ Q ≤ 2*(r i).den ∧
        (anchor i:ℝ) < r i ∧ |(r i:ℝ)-(anchor i:ℝ)| ≤ c/(64*R^2) ∧
        z i∈Icc (za i) (za i+(N:ℝ)/16) ∧
        iteratedDeriv 2 (f i) (z i)/2=(r i:ℝ)) ∧
      let m := fun i => round (z i)
      let A := fun i => (L i-m i).toNat
      let q := fun i => (r i).den
      let μ := fun i => iteratedDeriv 3 (f i) (m i)/6
      let ℓ := fun i => deriv (f i) (m i)
      let U₃ := J/(2*(N:ℝ)*R^2)
      (∀ i∈S, |z i-(m i:ℝ)| ≤ 1/2 ∧
        N ≤ A i ∧ A i ≤ 3*N ∧ m i+(A i:ℤ)=L i) ∧
      (∀ i∈S, 1 ≤ A i ∧ q i ≤ A i ∧ 1 ≤ μ i*(q i:ℝ)^2*A i) ∧
      ∀ (K₀ : ℕ) [NeZero K₀], 63*U₃*(Q:ℝ)*(N:ℝ)^2 ≤ K₀ →
      (∀ i∈S, 7*(μ i*(q i:ℝ)*(A i:ℝ)^2) ≤ K₀) ∧
      ∃ v : ι → ℤ, (∀ i∈S, (q i:ℤ) ∣ (r i).num*v i-1) ∧
      let b := fun i (p : Fin 2) => (⌊(q i:ℝ)*ℓ i⌋+(p:ℕ) : ℤ)
      let τ := fun i p => ((b i p:ℝ)-(q i:ℝ)*ℓ i)/2
      let s := fun i => Real.sqrt (2/(3*μ i*(q i:ℝ)))
      let K := fun i => -2*μ i*(s i)^3
      let x := fun i p =>
        (![-(v i:ℝ)*b i p/q i,-(v i:ℝ)/q i,K i,3*K i*τ i p/2] : Fin 4 → ℝ)
      ∃ k : ZMod K₀,
        (∑ i∈S, ‖∑ n∈Finset.Ioc (L i) (L i+H i),(𝐞 (f i n):ℂ)‖) ≤
          C*((1+Real.log K₀)*
            (∑ i∈S, ∑ p : Fin 2,
              (Real.sqrt (2*(q i:ℝ))/((q i:ℝ)*Real.sqrt (μ i*A i)))*
              ‖∑ j : ZMod K₀,ZMod.stdAddChar (-(j*k))*
                GafniTao.fordAdditiveCharacter (∑ d,x i p d*
                  (![(j.val+1:ℝ),(j.val+1:ℝ)^2,(j.val+1:ℝ)^((3:ℝ)/2),
                    Real.sqrt (j.val+1:ℝ)] : Fin 4 → ℝ) d)‖)+
            ∑ i∈S, (Real.sqrt (A i)*Real.log (2*(A i:ℝ))+1/(μ i*(A i:ℝ)^2))) := by
  classical
  obtain ⟨C,hC,hentry⟩ := double_difference_chosen_arcs_band_fourier hc hJ
  refine ⟨C,hC,?_⟩
  intro ι S F y rshift sshift L H anchor za N Q d w T M R hN hH hd hw hsmall hT hM hR
    hy hshifts hbase hf hbound hlower hphase hbuffer hfourBudget hquadBudget
    hQN hcut hmajor f hanchors
  have hNp : (0:ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hNM : (N:ℝ) ≤ M := by linarith only [hbuffer,hNp]
  have hex i : ∃ b : ℚ, ∃ z : ℝ, i∈S →
      b.den ≤ Q ∧ Q ≤ 2*b.den ∧ (anchor i:ℝ) < b ∧
      |(b:ℝ)-(anchor i:ℝ)| ≤ c/(64*R^2) ∧
      z∈Icc (za i) (za i+(N:ℝ)/16) ∧
      iteratedDeriv 2 (f i) z/2=(b:ℝ) := by
    by_cases hi : i∈S
    · have hx : za i∈Icc (7*M/8) (17*M/8) := by
        have hh := (hanchors i hi).1
        have hb := hbase i hi
        constructor <;> linarith only [hh.1,hh.2,hb.1,hb.2,hNM]
      obtain ⟨b,hb,hhalf,hab,hclose,z,hz,he⟩ :=
        double_difference_dyadic_anchor_center F (hshifts i hi).1 (hshifts i hi).2.1 hd
          (hy i hi) (hshifts i hi).2.2.1 (hshifts i hi).2.2.2 hw hsmall hc hJ
          hT hM hNp hR hNM hphase hx hf hlower hbound (hcut i hi) (hmajor i hi) (hanchors i hi).2
      exact ⟨b,z,fun _ => ⟨hb,hhalf,hab,hclose,hz,he⟩⟩
    · exact ⟨anchor i,za i,fun h => (hi h).elim⟩
  choose r z hr using hex
  refine ⟨r,z,hr,?_⟩
  intro m A q μ ℓ U₃
  have hroots i (hi : i∈S) :
      z i∈Ioo ((L i:ℝ)-2*(N:ℝ)-(N:ℝ)/4)
        ((L i:ℝ)-2*(N:ℝ)+(N:ℝ)/4) ∧
      iteratedDeriv 2 (f i) (z i)/2=(r i:ℝ) := by
    have hz := (hr i hi).2.2.2.2.1
    have ha := (hanchors i hi).1
    exact ⟨⟨by linarith only [hz.1,ha.1,hNp],
      by linarith only [hz.2,ha.2,hNp]⟩,(hr i hi).2.2.2.2.2⟩
  obtain ⟨hgeo,hminor,hcomplete⟩ := hentry ι S F y rshift sshift L H r z N d w T M R
    hN hH hd hw hsmall hT hM hR hy hshifts hbase hf hbound hlower
    hphase hbuffer hfourBudget hquadBudget hroots
  let lambda := c/(12*(N:ℝ)*R^2)
  have hgood i (hi : i∈S) : q i ≤ N ∧ 1 ≤ lambda*(q i:ℝ)^2*N := by
    refine ⟨(hr i hi).1.trans hQN,?_⟩
    have hcutR : 2*((anchor i).den:ℝ) ≤ Q := by exact_mod_cast hcut i hi
    have hqR : (Q:ℝ) ≤ 2*(q i:ℝ) := by exact_mod_cast (hr i hi).2.1
    have haQ : ((anchor i).den:ℝ) ≤ (q i:ℝ) := by linarith only [hcutR,hqR]
    have hprod : c*(Q:ℝ)*(anchor i).den ≤ 2*c*(q i:ℝ)^2 := by
      calc
        _ ≤ c*(2*(q i:ℝ))*(q i:ℝ) := by gcongr
        _ = _ := by ring
    have hbudget : 12*R^2 ≤ c*(q i:ℝ)^2 := by
      have hpositive : 0 < R^2 := by positivity
      nlinarith only [hmajor i hi,hprod,hpositive]
    have heq : lambda*(q i:ℝ)^2*N=c*(q i:ℝ)^2/(12*R^2) := by
      dsimp only [lambda]
      field_simp
    rw [heq]
    exact (one_le_div (by positivity : 0 < 12*R^2)).mpr hbudget
  have hGS : S.filter (fun i => q i ≤ N ∧ 1 ≤ lambda*(q i:ℝ)^2*N)=S :=
    Finset.filter_eq_self.mpr hgood
  have hBad : S.filter (fun i => ¬ (q i ≤ N ∧ 1 ≤ lambda*(q i:ℝ)^2*N))=∅ := by
    apply Finset.filter_eq_empty_iff.mpr
    intro i hi hn
    exact hn (hgood i hi)
  dsimp only [q,lambda] at hGS hBad
  have hminor' : ∀ i∈S, 1 ≤ A i ∧ q i ≤ A i ∧ 1 ≤ μ i*(q i:ℝ)^2*A i := by
    simpa only [hGS] using hminor
  refine ⟨hgeo,hminor',?_⟩
  intro K₀ inst hK₀
  have hqG i (hi : i∈S.filter (fun i => q i ≤ N ∧ 1 ≤ lambda*(q i:ℝ)^2*N)) :
      q i ≤ Q := (hr i (Finset.mem_filter.mp hi).1).1
  obtain ⟨hmesh,v,hv,hout⟩ := hcomplete Q hqG K₀ hK₀
  refine ⟨?_,v,?_,?_⟩
  · simpa only [hGS] using hmesh
  · simpa only [hGS] using hv
  · intro b τ s K x
    simpa only [hGS,hBad,Finset.sum_empty,zero_add] using hout

example
    {c J : ℝ} (hc : 0 < c) (hJ : 0 < J) :
    ∃ C ≥ (1:ℝ), ∀ (ι : Type*) (S : Finset ι) (F : ℝ → ℝ)
      (y rshift sshift : ι → ℝ) (L : ι → ℤ) (H : ι → ℕ) (anchor : ι → ℚ) (za : ι → ℝ)
      (N Q : ℕ) (d w T M R : ℝ),
      1 ≤ N → (∀ i∈S, H i ≤ N) →
      0 < d → w ≤ 1/4 → 2*J*w ≤ c/64 → 0 < T → 0 < M → 0 < R →
      (∀ i∈S, y i∈Icc (1:ℝ) 2) →
      (∀ i∈S, 0 ≤ rshift i ∧ 0 ≤ sshift i ∧
        rshift i*sshift i=d*y i ∧ rshift i+sshift i ≤ w) →
      (∀ i∈S, (L i:ℝ)-2*(N:ℝ)∈Icc M (2*M)) →
      (∀ w, 0 < w → ContDiffAt ℝ ∞ F w) →
      (∀ u∈Icc (1/2:ℝ) 3, ∀ n, 1 ≤ n → n ≤ 7 → |iteratedDeriv n F u| ≤ J) →
      (∀ u∈Icc (1/2:ℝ) 3, c ≤ iteratedDeriv 5 F u) →
      T*(N:ℝ)*R^2=M^3 →
      7*(N:ℝ)+2 ≤ M/4 →
      (3*J)*(6*(N:ℝ)+1)^4 ≤ M*(N:ℝ)*R^2 →
      (3*J/4)*(6*(N:ℝ)+1)^2 ≤ (N:ℝ)*R^2 →
      Q ≤ N → (∀ i∈S, 2*(anchor i).den ≤ Q) →
      (∀ i∈S, 128*R^2 ≤ c*(Q:ℝ)*(anchor i).den) →
      let f := fun i v => T*((F (v/M)-F (v/M+rshift i)-F (v/M+sshift i)+
        F (v/M+rshift i+sshift i))/d)
      (∀ i∈S, za i∈Ioo ((L i:ℝ)-2*(N:ℝ)-(N:ℝ)/8)
        ((L i:ℝ)-2*(N:ℝ)+(N:ℝ)/8) ∧
        iteratedDeriv 2 (f i) (za i)/2=(anchor i:ℝ)) →
      ∃ (r : ι → ℚ) (z : ι → ℝ),
      (∀ i∈S, (r i).den ≤ Q ∧ Q ≤ 2*(r i).den ∧
        (anchor i:ℝ) < r i ∧ |(r i:ℝ)-(anchor i:ℝ)| ≤ c/(64*R^2) ∧
        z i∈Icc (za i) (za i+(N:ℝ)/16) ∧
        iteratedDeriv 2 (f i) (z i)/2=(r i:ℝ)) ∧
      let m := fun i => round (z i)
      let A := fun i => (L i-m i).toNat
      let q := fun i => (r i).den
      let μ := fun i => iteratedDeriv 3 (f i) (m i)/6
      let ℓ := fun i => deriv (f i) (m i)
      let U₃ := J/(2*(N:ℝ)*R^2)
      (∀ i∈S, |z i-(m i:ℝ)| ≤ 1/2 ∧
        N ≤ A i ∧ A i ≤ 3*N ∧ m i+(A i:ℤ)=L i) ∧
      (∀ i∈S, 1 ≤ A i ∧ q i ≤ A i ∧ 1 ≤ μ i*(q i:ℝ)^2*A i) ∧
      ∀ (K₀ : ℕ) [NeZero K₀], 63*U₃*(Q:ℝ)*(N:ℝ)^2 ≤ K₀ →
      (∀ i∈S, 7*(μ i*(q i:ℝ)*(A i:ℝ)^2) ≤ K₀) ∧
      ∃ v : ι → ℤ, (∀ i∈S, (q i:ℤ) ∣ (r i).num*v i-1) ∧
      let b := fun i (p : Fin 2) => (⌊(q i:ℝ)*ℓ i⌋+(p:ℕ) : ℤ)
      let τ := fun i p => ((b i p:ℝ)-(q i:ℝ)*ℓ i)/2
      let s := fun i => Real.sqrt (2/(3*μ i*(q i:ℝ)))
      let K := fun i => -2*μ i*(s i)^3
      let x := fun i p =>
        (![-(v i:ℝ)*b i p/q i,-(v i:ℝ)/q i,K i,3*K i*τ i p/2] : Fin 4 → ℝ)
      ∃ k : ZMod K₀,
        (∑ i∈S, ‖∑ n∈Finset.Ioc (L i) (L i+H i),(𝐞 (f i n):ℂ)‖) ≤
          C*((1+Real.log K₀)*
            (∑ i∈S, ∑ p : Fin 2,
              (Real.sqrt (2*(q i:ℝ))/((q i:ℝ)*Real.sqrt (μ i*A i)))*
              ‖∑ j : ZMod K₀,ZMod.stdAddChar (-(j*k))*
                GafniTao.fordAdditiveCharacter (∑ d,x i p d*
                  (![(j.val+1:ℝ),(j.val+1:ℝ)^2,(j.val+1:ℝ)^((3:ℝ)/2),
                    Real.sqrt (j.val+1:ℝ)] : Fin 4 → ℝ) d)‖)+
            ∑ i∈S, (Real.sqrt (A i)*Real.log (2*(A i:ℝ))+1/(μ i*(A i:ℝ)^2))) := by
  exact double_difference_dyadic_anchor_source_fourier hc hJ

#print axioms double_difference_dyadic_anchor_source_fourier


/-- Source-derived minimum-denominator anchors, SAME curvature roots, injectivity
and the sharp high-denominator tail on the actual physical grid. -/
private theorem double_difference_minimal_anchor_roots_sharp_tail
    (S : Finset ℤ) (F : ℝ → ℝ) (N : ℕ) (base : ℝ)
    {r s d y w c U T M R : ℝ}
    (hr : 0 ≤ r) (hs : 0 ≤ s) (hd : 0 < d)
    (hy : y∈Icc (1:ℝ) 2) (hprod : r*s=d*y)
    (hshift : r+s ≤ w) (hw : w ≤ 1/4) (hsmall : 2*U*w ≤ c/64)
    (hc : 0 < c) (hU : 0 < U) (hT : 0 < T) (hM : 0 < M)
    (hN : 0 < N) (hR : 0 < R) (hNM : (N:ℝ) ≤ M)
    (hphase : T*(N:ℝ)*R^2=M^3)
    (hf : ∀ u, 0 < u → ContDiffAt ℝ ∞ F u)
    (hlower : ∀ u∈Icc (1/2:ℝ) 3, c ≤ iteratedDeriv 5 F u)
    (hjets : ∀ u∈Icc (1/2:ℝ) 3, ∀ n, 1 ≤ n → n ≤ 7 → |iteratedDeriv n F u| ≤ U)
    (hnegative : ∀ u∈Icc (1/2:ℝ) 3, iteratedDeriv 4 F u ≤ -c)
    (hpoints : ∀ j∈S, base+(N:ℝ)*j∈Icc (M+(N:ℝ)/4) (2*M-(N:ℝ)/4)) :
    let Φ := fun u => (F u-F (u+r)-F (u+s)+F (u+r+s))/d
    let f := fun v => T*Φ (v/M)
    let h := fun v => iteratedDeriv 2 f v/2
    let t := fun j : ℤ => base+(N:ℝ)*j
    let delta := c/(64*R^2)
    let X := U*M/((N:ℝ)*R^2)
    ∃ (anchor : ℤ → ℚ) (za : ℤ → ℝ),
      (∀ j∈S, (anchor j:ℝ)∈Ioo (h (t j)-delta) (h (t j)+delta) ∧
        ∀ q : ℚ, (q:ℝ)∈Ioo (h (t j)-delta) (h (t j)+delta) → (anchor j).den ≤ q.den) ∧
      (∀ j∈S, h (za j)=(anchor j:ℝ) ∧ |za j-t j| ≤ (N:ℝ)/16 ∧ za j∈Icc M (2*M)) ∧
      Set.InjOn anchor (S : Set ℤ) ∧
      (∀ j∈S, |(anchor j:ℝ)| ≤ X+delta) ∧
      ∀ Q : ℕ, 2 ≤ Q →
        let D := 64*R^2/(c*(Q:ℝ))
        (((S.filter (fun j => Q ≤ (anchor j).den)).card:ℝ)) ≤
          4*X*D^2+3*D*(2+Real.log (D+1)) := by
  classical
  intro Φ f h t delta X
  have hNp : (0:ℝ) < N := Nat.cast_pos.mpr hN
  have hdelta : 0 < delta := by dsimp only [delta]; positivity
  have hXp : 0 ≤ X := by dsimp only [X]; positivity
  have hplain j (hj : j∈S) : t j∈Icc M (2*M) := by
    have hh := hpoints j hj
    constructor <;> linarith only [hh.1,hh.2,hNp]
  have hdata x (hx : x∈Icc (3*M/4) (9*M/4)) :=
    double_difference_physical_source_jets F hr hs hd hy hprod hshift hw hsmall hc hU hT hM
      hx hf hlower hjets
  have hcf x (hx : x∈Icc (3*M/4) (9*M/4)) : ContDiffAt ℝ 3 f x :=
    ((hdata x hx).1 x (by linarith only [hx.1,hM])).of_le
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl 3)
  let L := c*T/(8*M^3)
  have hL : 0 < L := by dsimp only [L]; positivity
  have hthree x (hx : x∈Icc (3*M/4) (9*M/4)) : L ≤ iteratedDeriv 3 f x := by
    have hh := (hdata x hx).2.1
    have he : c*T/(2*M^3)=4*L := by dsimp only [L]; ring
    rw [he] at hh
    linarith only [hh,hL]
  have hcurv j (hj : j∈S) : |h (t j)| ≤ X := by
    have hprodpos : 0 < r*s := by rw [hprod]; exact mul_pos hd (by linarith only [hy.1])
    have hrp : 0 < r := by nlinarith only [hr,hs,hprodpos]
    have hsp : 0 < s := by nlinarith only [hr,hs,hprodpos]
    have hh := (double_difference_physical_curvature_band F (hplain j hj) hy hrp hsp hd
      hc hU hT hM hprod (hshift.trans hw) hf hnegative
      (fun u hu => hjets u hu 4 (by norm_num) (by norm_num))).2
    have he : U*T/M^2=X := by
      dsimp only [X]
      apply (div_eq_div_iff (by positivity) (by positivity)).mpr
      calc
        U*T*((N:ℝ)*R^2)=U*(T*(N:ℝ)*R^2) := by ring
        _ = U*M^3 := by rw [hphase]
        _ = U*M*M^2 := by ring
    exact hh.trans_eq he
  have hmul j : (S.filter (fun k => id k=j)).card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro i hi k hk
    exact ((Finset.mem_filter.mp hi).2).trans ((Finset.mem_filter.mp hk).2).symm
  obtain ⟨anchor,za,hanchors,_hweak⟩ :=
    TaoTrudgianYang2025.exists_bourgain_C3_minimal_curvature_arc_count S f id N 1 base
      hN hL hXp hcf hthree hmul
      (by
        intro j hj v hv
        have hp := hplain j hj
        change t j-(N:ℝ)/4 ≤ v ∧ v ≤ t j+(N:ℝ)/4 at hv
        constructor <;> linarith only [hp.1,hp.2,hv.1,hv.2,hNM])
      hcurv
  have hdeltaEq : L*(N:ℝ)/8=delta := by
    dsimp only [L,delta]
    rw [←hphase]
    field_simp
    ring
  have hanchors' j (hj : j∈S) :
      za j∈Ioo (t j-(N:ℝ)/4) (t j+(N:ℝ)/4) ∧
      h (za j)=(anchor j:ℝ) ∧
      (anchor j:ℝ)∈Ioo (h (t j)-delta) (h (t j)+delta) ∧
      ∀ q : ℚ, (q:ℝ)∈Ioo (h (t j)-delta) (h (t j)+delta) → (anchor j).den ≤ q.den := by
    simpa only [hdeltaEq] using hanchors j hj
  let eta := c/(4*R^2)
  have heta : 0 < eta := by dsimp only [eta]; positivity
  have hgrow x z (hx : x∈Icc M (2*M)) (hz : z∈Icc M (2*M)) (hxz : x ≤ z) :
      c*T/(4*M^3)*(z-x) ≤ h z-h x := by
    apply double_difference_physical_curvature_growth F hr hs hd hy hprod hshift hw hsmall
      hc hU hT hM _ _ hxz hf hlower hjets
    · constructor <;> linarith only [hx.1,hx.2,hM]
    · constructor <;> linarith only [hz.1,hz.2,hM]
  have hsepOrdered i (hi : i∈S) j (hj : j∈S) (hij : t i ≤ t j) :
      eta*|(i:ℝ)-j| ≤ |h (t i)-h (t j)| := by
    have hiR : (i:ℝ) ≤ j := by
      apply (mul_le_mul_iff_right₀ hNp).mp
      dsimp only [t] at hij
      linarith only [hij]
    calc
      _ = (c*T/(4*M^3))*(t j-t i) := by
        rw [abs_of_nonpos (sub_nonpos.mpr hiR)]
        dsimp only [eta,t]
        rw [←hphase]
        field_simp
        ring
      _ ≤ h (t j)-h (t i) := hgrow _ _ (hplain i hi) (hplain j hj) hij
      _ ≤ |h (t j)-h (t i)| := le_abs_self _
      _ = _ := abs_sub_comm _ _
  have hsep i (hi : i∈S) j (hj : j∈S) : eta*|(i:ℝ)-j| ≤ |h (t i)-h (t j)| := by
    rcases le_total (t i) (t j) with hij | hji
    · exact hsepOrdered i hi j hj hij
    · simpa only [abs_sub_comm] using hsepOrdered j hj i hi hji
  have hnear j (hj : j∈S) : |(anchor j:ℝ)-h (t j)| ≤ delta := by
    have hh := (hanchors' j hj).2.2.1
    exact abs_le.mpr ⟨by linarith only [hh.1],by linarith only [hh.2]⟩
  have hroots j (hj : j∈S) :
      h (za j)=(anchor j:ℝ) ∧ |za j-t j| ≤ (N:ℝ)/16 ∧ za j∈Icc M (2*M) := by
    have hh := hanchors' j hj
    have hp := hpoints j hj
    have hz : za j∈Icc M (2*M) := by
      constructor <;> linarith only [hh.1.1,hh.1.2,hp.1,hp.2]
    have hrate : c*T/(4*M^3)*((N:ℝ)/16)=delta := by
      dsimp only [delta]
      rw [←hphase]
      field_simp
      ring
    refine ⟨hh.2.1,?_,hz⟩
    have hn := hnear j hj
    rw [←hh.2.1] at hn
    rcases le_total (t j) (za j) with hle | hle
    · have hg := hgrow _ _ (hplain j hj) hz hle
      rw [abs_of_nonneg (sub_nonneg.mpr hle)]
      apply (mul_le_mul_iff_right₀ (show 0 < c*T/(4*M^3) by positivity)).mp
      rw [hrate]
      exact hg.trans ((le_abs_self _).trans hn)
    · have hg := hgrow _ _ hz (hplain j hj) hle
      rw [abs_of_nonpos (sub_nonpos.mpr hle),neg_sub]
      apply (mul_le_mul_iff_right₀ (show 0 < c*T/(4*M^3) by positivity)).mp
      rw [hrate]
      rw [abs_sub_comm] at hn
      exact hg.trans ((le_abs_self _).trans hn)
  have hinj : Set.InjOn anchor (S : Set ℤ) := by
    intro i hi j hj he
    have hh := hsep i hi j hj
    have hdiff : |h (t i)-h (t j)| ≤ 2*delta := by
      calc
        _ = |(h (t i)-(anchor i:ℝ))+((anchor j:ℝ)-h (t j))| := by rw [he]; congr 1; ring
        _ ≤ |h (t i)-(anchor i:ℝ)|+|(anchor j:ℝ)-h (t j)| := abs_add_le _ _
        _ ≤ delta+delta := by rw [abs_sub_comm (h (t i))]; exact add_le_add (hnear i hi) (hnear j hj)
        _ = _ := by ring
    have he : 2*delta=eta/8 := by dsimp only [delta,eta]; ring
    rw [he] at hdiff
    have hiR : |(i:ℝ)-j| < 1 := by nlinarith only [hh,hdiff,heta]
    have hiZ : |i-j| < 1 := by exact_mod_cast hiR
    exact sub_eq_zero.mp (Int.abs_lt_one_iff.mp hiZ)
  refine ⟨anchor,za,(fun j hj => (hanchors' j hj).2.2),hroots,hinj,?_,?_⟩
  · intro j hj
    calc
      |(anchor j:ℝ)| = |((anchor j:ℝ)-h (t j))+h (t j)| := by rw [sub_add_cancel]
      _ ≤ |(anchor j:ℝ)-h (t j)|+|h (t j)| := abs_add_le _ _
      _ ≤ delta+X := add_le_add (hnear j hj) (hcurv j hj)
      _ = _ := by ring
  · intro Q hQ D
    have hwidth : 4*delta ≤ eta := by
      have he : 4*delta=eta/4 := by dsimp only [delta,eta]; ring
      rw [he]
      linarith only [heta]
    have hh := TaoTrudgianYang2025.bourgain_actual_minimal_arc_sharp_tail S id (fun j => h (t j))
      anchor 1 heta hdelta hXp hwidth hmul hsep hcurv
      (fun j hj => (hanchors' j hj).2.2.2) Q hQ
    have he : 1/(delta*(Q:ℝ))=D := by dsimp only [delta,D]; field_simp
    simpa only [he,Nat.cast_one,one_mul] using hh

example
    (S : Finset ℤ) (F : ℝ → ℝ) (N : ℕ) (base : ℝ)
    {r s d y w c U T M R : ℝ}
    (hr : 0 ≤ r) (hs : 0 ≤ s) (hd : 0 < d)
    (hy : y∈Icc (1:ℝ) 2) (hprod : r*s=d*y)
    (hshift : r+s ≤ w) (hw : w ≤ 1/4) (hsmall : 2*U*w ≤ c/64)
    (hc : 0 < c) (hU : 0 < U) (hT : 0 < T) (hM : 0 < M)
    (hN : 0 < N) (hR : 0 < R) (hNM : (N:ℝ) ≤ M)
    (hphase : T*(N:ℝ)*R^2=M^3)
    (hf : ∀ u, 0 < u → ContDiffAt ℝ ∞ F u)
    (hlower : ∀ u∈Icc (1/2:ℝ) 3, c ≤ iteratedDeriv 5 F u)
    (hjets : ∀ u∈Icc (1/2:ℝ) 3, ∀ n, 1 ≤ n → n ≤ 7 → |iteratedDeriv n F u| ≤ U)
    (hnegative : ∀ u∈Icc (1/2:ℝ) 3, iteratedDeriv 4 F u ≤ -c)
    (hpoints : ∀ j∈S, base+(N:ℝ)*j∈Icc (M+(N:ℝ)/4) (2*M-(N:ℝ)/4)) :
    let Φ := fun u => (F u-F (u+r)-F (u+s)+F (u+r+s))/d
    let f := fun v => T*Φ (v/M)
    let h := fun v => iteratedDeriv 2 f v/2
    let t := fun j : ℤ => base+(N:ℝ)*j
    let delta := c/(64*R^2)
    let X := U*M/((N:ℝ)*R^2)
    ∃ (anchor : ℤ → ℚ) (za : ℤ → ℝ),
      (∀ j∈S, (anchor j:ℝ)∈Ioo (h (t j)-delta) (h (t j)+delta) ∧
        ∀ q : ℚ, (q:ℝ)∈Ioo (h (t j)-delta) (h (t j)+delta) → (anchor j).den ≤ q.den) ∧
      (∀ j∈S, h (za j)=(anchor j:ℝ) ∧ |za j-t j| ≤ (N:ℝ)/16 ∧ za j∈Icc M (2*M)) ∧
      Set.InjOn anchor (S : Set ℤ) ∧
      (∀ j∈S, |(anchor j:ℝ)| ≤ X+delta) ∧
      ∀ Q : ℕ, 2 ≤ Q →
        let D := 64*R^2/(c*(Q:ℝ))
        (((S.filter (fun j => Q ≤ (anchor j).den)).card:ℝ)) ≤
          4*X*D^2+3*D*(2+Real.log (D+1)) := by
  exact double_difference_minimal_anchor_roots_sharp_tail S F N base hr hs hd hy hprod
    hshift hw hsmall hc hU hT hM hN hR hNM hphase hf hlower hjets hnegative hpoints

#print axioms double_difference_minimal_anchor_roots_sharp_tail


/-- The actual minimum anchors control BOTH failures of the selected minor-arc
regime, including the literal discarded source lengths. -/
private theorem double_difference_minimal_anchor_complement

    (S : Finset ℤ) (F : ℝ → ℝ) (N : ℕ) (base : ℝ)
    {r s d y w c U T M R : ℝ}
    (hr : 0 ≤ r) (hs : 0 ≤ s) (hd : 0 < d)
    (hy : y∈Icc (1:ℝ) 2) (hprod : r*s=d*y)
    (hshift : r+s ≤ w) (hw : w ≤ 1/4) (hsmall : 2*U*w ≤ c/64)
    (hc : 0 < c) (hU : 0 < U) (hT : 0 < T) (hM : 0 < M)
    (hN : 0 < N) (hR : 0 < R) (hNM : (N:ℝ) ≤ M)
    (hphase : T*(N:ℝ)*R^2=M^3)
    (hf : ∀ u, 0 < u → ContDiffAt ℝ ∞ F u)
    (hlower : ∀ u∈Icc (1/2:ℝ) 3, c ≤ iteratedDeriv 5 F u)
    (hjets : ∀ u∈Icc (1/2:ℝ) 3, ∀ n, 1 ≤ n → n ≤ 7 → |iteratedDeriv n F u| ≤ U)
    (hnegative : ∀ u∈Icc (1/2:ℝ) 3, iteratedDeriv 4 F u ≤ -c)
    (hpoints : ∀ j∈S, base+(N:ℝ)*j∈Icc (M+(N:ℝ)/4) (2*M-(N:ℝ)/4)) :
    let Φ := fun u => (F u-F (u+r)-F (u+s)+F (u+r+s))/d
    let f := fun v => T*Φ (v/M)
    let h := fun v => iteratedDeriv 2 f v/2
    let t := fun j : ℤ => base+(N:ℝ)*j
    let delta := c/(64*R^2)
    let X := U*M/((N:ℝ)*R^2)
    ∃ (anchor : ℤ → ℚ) (za : ℤ → ℝ),
      (∀ j∈S, (anchor j:ℝ)∈Ioo (h (t j)-delta) (h (t j)+delta) ∧
        ∀ q : ℚ, (q:ℝ)∈Ioo (h (t j)-delta) (h (t j)+delta) → (anchor j).den ≤ q.den) ∧
      (∀ j∈S, h (za j)=(anchor j:ℝ) ∧ |za j-t j| ≤ (N:ℝ)/16 ∧ za j∈Icc M (2*M)) ∧
      ∀ (Q Acut : ℕ) (Bmajor : ℝ), 2 ≤ Acut → Acut ≤ Q → 0 ≤ Bmajor →
    let Bad := S.filter (fun i => ¬ (Acut*(anchor i).den ≤ Q ∧
      Bmajor*R^2 ≤ c*(Q:ℝ)*(anchor i).den))
    let Dlow := Bmajor*R^2/(c*(Q:ℝ))
    let Khigh := Q/Acut+1
    let Dhigh := 64*R^2/(c*(Khigh:ℝ))
    let Cost := 4*X*Dhigh^2+3*Dhigh*(2+Real.log (Dhigh+1))+
      Dlow*(2*(X+delta)*Dlow+1)
    (Bad.card:ℝ) ≤ Cost ∧
      ∀ H : ℤ → ℕ, (∀ i∈S, H i ≤ N) →
        (∑ i∈Bad,(H i:ℝ)) ≤ (N:ℝ)*Cost := by
  classical
  intro Φ f h t delta X
  obtain ⟨anchor,za,hanchor,hroots,hinj,hvalues,hhighAll⟩ :=
    double_difference_minimal_anchor_roots_sharp_tail S F N base hr hs hd hy hprod
      hshift hw hsmall hc hU hT hM hN hR hNM hphase hf hlower hjets hnegative hpoints
  refine ⟨anchor,za,hanchor,hroots,?_⟩
  intro Q Acut Bmajor hAcut hAQ hBmajor Bad Dlow Khigh Dhigh Cost
  have hNp : (0:ℝ) < N := Nat.cast_pos.mpr hN
  have hQ : 0 < Q := by omega
  have hQr : (0:ℝ) < Q := Nat.cast_pos.mpr hQ
  have hApos : 0 < Acut := by omega
  have hdelta : 0 < delta := by dsimp only [delta]; positivity
  have hV : 0 ≤ X := by dsimp only [X]; positivity
  have hDlow : 0 ≤ Dlow := by dsimp only [Dlow]; positivity
  have hK : 2 ≤ Khigh := by
    have hh : 1 ≤ Q/Acut := (Nat.le_div_iff_mul_le hApos).mpr (by simpa only [one_mul] using hAQ)
    dsimp only [Khigh]
    omega
  let High := S.filter (fun i => Khigh ≤ (anchor i).den)
  have hhigh : (High.card:ℝ) ≤ 4*X*Dhigh^2+3*Dhigh*(2+Real.log (Dhigh+1)) :=
    hhighAll Khigh hK
  let Low := S.filter (fun i => c*(Q:ℝ)*(anchor i).den < Bmajor*R^2)
  have hlowden i (hi : i∈Low) : (anchor i).den ≤ ⌊Dlow⌋₊ := by
    apply Nat.le_floor
    apply (le_div_iff₀ (mul_pos hc hQr)).mpr
    have hh := (Finset.mem_filter.mp hi).2
    nlinarith only [hh]
  have hlow : (Low.card:ℝ) ≤ Dlow*(2*(X+delta)*Dlow+1) := by
    have hcount := bourgain_bounded_denominator_count Low anchor ⌊Dlow⌋₊ 1
      (add_nonneg hV hdelta.le) (fun i hi => hvalues i (Finset.mem_filter.mp hi).1) hlowden
      (by
        intro a
        apply Finset.card_le_one.mpr
        intro i hi j hj
        obtain ⟨hiL,hia⟩ := Finset.mem_filter.mp hi
        obtain ⟨hjL,hja⟩ := Finset.mem_filter.mp hj
        exact hinj (Finset.mem_filter.mp hiL).1 (Finset.mem_filter.mp hjL).1 (hia.trans hja.symm))
    simp only [Nat.cast_one,one_mul] at hcount
    apply hcount.trans
    have hfloor : (⌊Dlow⌋₊:ℝ) ≤ Dlow := Nat.floor_le hDlow
    gcongr
  have hsub : Bad⊆High∪Low := by
    intro i hi
    obtain ⟨hiS,hbad⟩ := Finset.mem_filter.mp hi
    rcases not_and_or.mp hbad with hlarge | hsmall
    · apply Finset.mem_union_left
      apply Finset.mem_filter.mpr
      refine ⟨hiS,?_⟩
      have hh : Q/Acut < (anchor i).den :=
        (Nat.div_lt_iff_lt_mul hApos).mpr (by simpa only [mul_comm] using lt_of_not_ge hlarge)
      exact Nat.succ_le_of_lt hh
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hiS,lt_of_not_ge hsmall⟩)
  have hcard : (Bad.card:ℝ) ≤ Cost := by
    have hh : (Bad.card:ℝ) ≤ (High.card:ℝ)+(Low.card:ℝ) := by
      exact_mod_cast (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
    exact hh.trans (add_le_add hhigh hlow)
  refine ⟨hcard,?_⟩
  intro H hH
  calc
    (∑ i∈Bad,(H i:ℝ)) ≤ ∑ _i∈Bad,(N:ℝ) := Finset.sum_le_sum (fun i hi =>
      Nat.cast_le.mpr (hH i (Finset.mem_filter.mp hi).1))
    _ = (N:ℝ)*(Bad.card:ℝ) := by simp only [Finset.sum_const,nsmul_eq_mul,mul_comm]
    _ ≤ (N:ℝ)*Cost := mul_le_mul_of_nonneg_left hcard hNp.le

example

    (S : Finset ℤ) (F : ℝ → ℝ) (N : ℕ) (base : ℝ)
    {r s d y w c U T M R : ℝ}
    (hr : 0 ≤ r) (hs : 0 ≤ s) (hd : 0 < d)
    (hy : y∈Icc (1:ℝ) 2) (hprod : r*s=d*y)
    (hshift : r+s ≤ w) (hw : w ≤ 1/4) (hsmall : 2*U*w ≤ c/64)
    (hc : 0 < c) (hU : 0 < U) (hT : 0 < T) (hM : 0 < M)
    (hN : 0 < N) (hR : 0 < R) (hNM : (N:ℝ) ≤ M)
    (hphase : T*(N:ℝ)*R^2=M^3)
    (hf : ∀ u, 0 < u → ContDiffAt ℝ ∞ F u)
    (hlower : ∀ u∈Icc (1/2:ℝ) 3, c ≤ iteratedDeriv 5 F u)
    (hjets : ∀ u∈Icc (1/2:ℝ) 3, ∀ n, 1 ≤ n → n ≤ 7 → |iteratedDeriv n F u| ≤ U)
    (hnegative : ∀ u∈Icc (1/2:ℝ) 3, iteratedDeriv 4 F u ≤ -c)
    (hpoints : ∀ j∈S, base+(N:ℝ)*j∈Icc (M+(N:ℝ)/4) (2*M-(N:ℝ)/4)) :
    let Φ := fun u => (F u-F (u+r)-F (u+s)+F (u+r+s))/d
    let f := fun v => T*Φ (v/M)
    let h := fun v => iteratedDeriv 2 f v/2
    let t := fun j : ℤ => base+(N:ℝ)*j
    let delta := c/(64*R^2)
    let X := U*M/((N:ℝ)*R^2)
    ∃ (anchor : ℤ → ℚ) (za : ℤ → ℝ),
      (∀ j∈S, (anchor j:ℝ)∈Ioo (h (t j)-delta) (h (t j)+delta) ∧
        ∀ q : ℚ, (q:ℝ)∈Ioo (h (t j)-delta) (h (t j)+delta) → (anchor j).den ≤ q.den) ∧
      (∀ j∈S, h (za j)=(anchor j:ℝ) ∧ |za j-t j| ≤ (N:ℝ)/16 ∧ za j∈Icc M (2*M)) ∧
      ∀ (Q Acut : ℕ) (Bmajor : ℝ), 2 ≤ Acut → Acut ≤ Q → 0 ≤ Bmajor →
    let Bad := S.filter (fun i => ¬ (Acut*(anchor i).den ≤ Q ∧
      Bmajor*R^2 ≤ c*(Q:ℝ)*(anchor i).den))
    let Dlow := Bmajor*R^2/(c*(Q:ℝ))
    let Khigh := Q/Acut+1
    let Dhigh := 64*R^2/(c*(Khigh:ℝ))
    let Cost := 4*X*Dhigh^2+3*Dhigh*(2+Real.log (Dhigh+1))+
      Dlow*(2*(X+delta)*Dlow+1)
    (Bad.card:ℝ) ≤ Cost ∧
      ∀ H : ℤ → ℕ, (∀ i∈S, H i ≤ N) →
        (∑ i∈Bad,(H i:ℝ)) ≤ (N:ℝ)*Cost := by
  exact double_difference_minimal_anchor_complement S F N base hr hs hd hy hprod
    hshift hw hsmall hc hU hT hM hN hR hNM hphase hf hlower hjets hnegative hpoints

#print axioms double_difference_minimal_anchor_complement


/-- Witness-first minimum anchors and least dyadic band, with actual roots
and derived occupied-band/terminal cardinalities for the SAME two probes. -/
private theorem double_difference_two_probe_dyadic_band_card
    (S : Finset ℤ) (F : ℝ → ℝ) (N Qbase kmax Acut : ℕ) (base : Fin 2 → ℝ) (Bmajor : ℝ)
    {r s d y w c U T M R : ℝ}
    (hr : 0 ≤ r) (hs : 0 ≤ s) (hd : 0 < d)
    (hy : y∈Icc (1:ℝ) 2) (hprod : r*s=d*y)
    (hshift : r+s ≤ w) (hw : w ≤ 1/4) (hsmall : 2*U*w ≤ c/64)
    (hc : 0 < c) (hU : 0 < U) (hT : 0 < T) (hM : 0 < M)
    (hN : 0 < N) (hR : 0 < R) (hNM : (N:ℝ) ≤ M)
    (hphase : T*(N:ℝ)*R^2=M^3)
    (hf : ∀ u, 0 < u → ContDiffAt ℝ ∞ F u)
    (hlower : ∀ u∈Icc (1/2:ℝ) 3, c ≤ iteratedDeriv 5 F u)
    (hjets : ∀ u∈Icc (1/2:ℝ) 3, ∀ n, 1 ≤ n → n ≤ 7 → |iteratedDeriv n F u| ≤ U)
    (hnegative : ∀ u∈Icc (1/2:ℝ) 3, iteratedDeriv 4 F u ≤ -c)
    (hAcut : 2 ≤ Acut) (hAQ : Acut ≤ Qbase) (hBmajor : 0 ≤ Bmajor)
    (hpoints : ∀ j∈S, ∀ i, base i+(N:ℝ)*j∈Icc (M+(N:ℝ)/4) (2*M-(N:ℝ)/4)) :
    let f := fun v => T*((F (v/M)-F (v/M+r)-F (v/M+s)+F (v/M+r+s))/d)
    let h := fun w => iteratedDeriv 2 f w/2
    let t := fun (j : ℤ) (i : Fin 2) => base i+(N:ℝ)*j
    let delta := c/(64*R^2)
    let Q := fun k : ℕ => Qbase*2^k
    let Vbound := U*M/((N:ℝ)*R^2)
    let Cost := fun q : ℕ =>
      let Dlow := Bmajor*R^2/(c*(q:ℝ))
      let Dhigh := 64*R^2/(c*((q/Acut+1:ℕ):ℝ))
      4*Vbound*Dhigh^2+3*Dhigh*(2+Real.log (Dhigh+1))+
        Dlow*(2*(Vbound+delta)*Dlow+1)
    ∃ (anchor : ℤ → Fin 2 → ℚ) (band : ℤ → Option ℕ) (za : ℤ → Fin 2 → ℝ),
      (∀ j∈S, ∀ i, (anchor j i:ℝ)∈Ioo (h (t j i)-delta) (h (t j i)+delta) ∧
        ∀ q : ℚ, (q:ℝ)∈Ioo (h (t j i)-delta) (h (t j i)+delta) →
          (anchor j i).den ≤ q.den) ∧
      (∀ j∈S, ∀ i, h (za j i)=(anchor j i:ℝ) ∧
        |za j i-t j i| ≤ (N:ℝ)/16 ∧ za j i∈Icc M (2*M)) ∧
      let Good := fun j k (i : Fin 2) =>
        Acut*(anchor j i).den ≤ Q k ∧
          Bmajor*R^2 ≤ c*(Q k:ℝ)*(anchor j i).den
      (∀ j, match band j with
        | none => ∃ i, ¬Good j kmax i
        | some k => k ≤ kmax ∧ (∀ i, Good j k i) ∧
            (k=0 ∨ ∃ i, ¬Good j (k-1) i)) ∧
      (∀ j∈S, ∀ k, band j=some k → ∀ i, ∀ q : ℚ,
        (q:ℝ)∈Ioo (h (t j i)-delta) (h (t j i)+delta) →
        (∀ r : ℚ, (r:ℝ)∈Ioo (h (t j i)-delta) (h (t j i)+delta) →
          q.den ≤ r.den) →
        Acut*q.den ≤ Q k ∧ Bmajor*R^2 ≤ c*(Q k:ℝ)*q.den) ∧
      (∀ k, ((S.filter (fun j => band j=some (k+1))).card:ℝ) ≤ 2*Cost (Q k)) ∧
      ((S.filter (fun j => band j=none)).card:ℝ) ≤ 2*Cost (Q kmax) := by
  classical
  intro f h t delta Q Vbound Cost
  choose a z ha hz hcomplement using
    fun i => double_difference_minimal_anchor_complement S F N (base i) hr hs hd hy hprod
      hshift hw hsmall hc hU hT hM hN hR hNM hphase hf hlower hjets hnegative
      (fun j hj => hpoints j hj i)
  let anchor := fun j i => a i j
  let za := fun j i => z i j
  have hanchor j (hj : j∈S) i :
      (anchor j i:ℝ)∈Ioo (h (t j i)-delta) (h (t j i)+delta) ∧
        ∀ q : ℚ, (q:ℝ)∈Ioo (h (t j i)-delta) (h (t j i)+delta) →
          (anchor j i).den ≤ q.den := ha i j hj
  have hroots j (hj : j∈S) i : h (za j i)=(anchor j i:ℝ) ∧
      |za j i-t j i| ≤ (N:ℝ)/16 ∧ za j i∈Icc M (2*M) := hz i j hj
  let Good := fun (j : ℤ) (k : ℕ) (i : Fin 2) =>
    Acut*(anchor j i).den ≤ Q k ∧
      Bmajor*R^2 ≤ c*(Q k:ℝ)*(anchor j i).den
  have hchoose j : ∃ label : Option ℕ, match label with
      | none => ∃ i, ¬Good j kmax i
      | some k => k ≤ kmax ∧ (∀ i, Good j k i) ∧
          (k=0 ∨ ∃ i, ¬Good j (k-1) i) := by
    by_cases hlast : ∀ i, Good j kmax i
    · have he : ∃ k : ℕ, k ≤ kmax ∧ ∀ i, Good j k i :=
        ⟨kmax,le_rfl,hlast⟩
      let k := Nat.find he
      have hk : k ≤ kmax ∧ ∀ i, Good j k i := Nat.find_spec he
      refine ⟨some k,hk.1,hk.2,?_⟩
      by_cases hz : k=0
      · exact Or.inl hz
      · right
        by_contra hno
        have hall : ∀ i, Good j (k-1) i := not_exists_not.mp hno
        exact Nat.find_min he (show k-1 < k by omega)
          ⟨(Nat.sub_le k 1).trans hk.1,hall⟩
    · exact ⟨none,not_forall.mp hlast⟩
  choose band hband using hchoose
  have hqA k : Acut ≤ Q k :=
    hAQ.trans (Nat.le_mul_of_pos_right Qbase (pow_pos (by decide : 0 < (2:ℕ)) k))
  have hbadcard k :
      ((S.filter (fun j => ∃ i, ¬Good j k i)).card:ℝ) ≤ 2*Cost (Q k) := by
    let Bad := fun i : Fin 2 => S.filter (fun j => ¬Good j k i)
    have hone (i : Fin 2) : ((Bad i).card:ℝ) ≤ Cost (Q k) :=
      (hcomplement i (Q k) Acut Bmajor hAcut (hqA k) hBmajor).1
    have hsub : S.filter (fun j => ∃ i, ¬Good j k i) ⊆ Bad 0 ∪ Bad 1 := by
      intro j hj
      obtain ⟨hjS,i,hi⟩ := Finset.mem_filter.mp hj
      fin_cases i
      · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hjS,hi⟩)
      · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hjS,hi⟩)
    have hh : ((S.filter (fun j => ∃ i, ¬Good j k i)).card:ℝ) ≤
        ((Bad 0).card:ℝ)+((Bad 1).card:ℝ) := by
      exact_mod_cast (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
    have hzero := hone 0
    have hone' := hone 1
    linarith only [hh,hzero,hone']
  refine ⟨anchor,band,za,hanchor,hroots,?_⟩
  change (∀ j, match band j with
    | none => ∃ i, ¬Good j kmax i
    | some k => k ≤ kmax ∧ (∀ i, Good j k i) ∧
      (k=0 ∨ ∃ i, ¬Good j (k-1) i)) ∧ _
  refine ⟨hband,?_,?_,?_⟩
  · intro j hjS k hj i q hq hmin
    have hd := hband j
    rw [hj] at hd
    have hsame : q.den=(anchor j i).den :=
      Nat.le_antisymm (hmin _ (hanchor j hjS i).1) ((hanchor j hjS i).2 q hq)
    rw [hsame]
    exact hd.2.1 i
  · intro k
    have hsub : S.filter (fun j => band j=some (k+1)) ⊆
        S.filter (fun j => ∃ i, ¬Good j k i) := by
      intro j hj
      obtain ⟨hjS,hjband⟩ := Finset.mem_filter.mp hj
      have hd := hband j
      rw [hjband] at hd
      refine Finset.mem_filter.mpr ⟨hjS,?_⟩
      rcases hd.2.2 with hz | hprev
      · omega
      · simpa only [Nat.add_sub_cancel] using hprev
    exact (show ((S.filter (fun j => band j=some (k+1))).card:ℝ) ≤
      ((S.filter (fun j => ∃ i, ¬Good j k i)).card:ℝ) by
        exact_mod_cast Finset.card_le_card hsub).trans (hbadcard k)
  · have hsub : S.filter (fun j => band j=none) ⊆
        S.filter (fun j => ∃ i, ¬Good j kmax i) := by
      intro j hj
      obtain ⟨hjS,hjband⟩ := Finset.mem_filter.mp hj
      have hd := hband j
      rw [hjband] at hd
      exact Finset.mem_filter.mpr ⟨hjS,hd⟩
    exact (show ((S.filter (fun j => band j=none)).card:ℝ) ≤
      ((S.filter (fun j => ∃ i, ¬Good j kmax i)).card:ℝ) by
        exact_mod_cast Finset.card_le_card hsub).trans (hbadcard kmax)

example
    (S : Finset ℤ) (F : ℝ → ℝ) (N Qbase kmax Acut : ℕ) (base : Fin 2 → ℝ) (Bmajor : ℝ)
    {r s d y w c U T M R : ℝ}
    (hr : 0 ≤ r) (hs : 0 ≤ s) (hd : 0 < d)
    (hy : y∈Icc (1:ℝ) 2) (hprod : r*s=d*y)
    (hshift : r+s ≤ w) (hw : w ≤ 1/4) (hsmall : 2*U*w ≤ c/64)
    (hc : 0 < c) (hU : 0 < U) (hT : 0 < T) (hM : 0 < M)
    (hN : 0 < N) (hR : 0 < R) (hNM : (N:ℝ) ≤ M)
    (hphase : T*(N:ℝ)*R^2=M^3)
    (hf : ∀ u, 0 < u → ContDiffAt ℝ ∞ F u)
    (hlower : ∀ u∈Icc (1/2:ℝ) 3, c ≤ iteratedDeriv 5 F u)
    (hjets : ∀ u∈Icc (1/2:ℝ) 3, ∀ n, 1 ≤ n → n ≤ 7 → |iteratedDeriv n F u| ≤ U)
    (hnegative : ∀ u∈Icc (1/2:ℝ) 3, iteratedDeriv 4 F u ≤ -c)
    (hAcut : 2 ≤ Acut) (hAQ : Acut ≤ Qbase) (hBmajor : 0 ≤ Bmajor)
    (hpoints : ∀ j∈S, ∀ i, base i+(N:ℝ)*j∈Icc (M+(N:ℝ)/4) (2*M-(N:ℝ)/4)) :
    let f := fun v => T*((F (v/M)-F (v/M+r)-F (v/M+s)+F (v/M+r+s))/d)
    let h := fun w => iteratedDeriv 2 f w/2
    let t := fun (j : ℤ) (i : Fin 2) => base i+(N:ℝ)*j
    let delta := c/(64*R^2)
    let Q := fun k : ℕ => Qbase*2^k
    let Vbound := U*M/((N:ℝ)*R^2)
    let Cost := fun q : ℕ =>
      let Dlow := Bmajor*R^2/(c*(q:ℝ))
      let Dhigh := 64*R^2/(c*((q/Acut+1:ℕ):ℝ))
      4*Vbound*Dhigh^2+3*Dhigh*(2+Real.log (Dhigh+1))+
        Dlow*(2*(Vbound+delta)*Dlow+1)
    ∃ (anchor : ℤ → Fin 2 → ℚ) (band : ℤ → Option ℕ) (za : ℤ → Fin 2 → ℝ),
      (∀ j∈S, ∀ i, (anchor j i:ℝ)∈Ioo (h (t j i)-delta) (h (t j i)+delta) ∧
        ∀ q : ℚ, (q:ℝ)∈Ioo (h (t j i)-delta) (h (t j i)+delta) →
          (anchor j i).den ≤ q.den) ∧
      (∀ j∈S, ∀ i, h (za j i)=(anchor j i:ℝ) ∧
        |za j i-t j i| ≤ (N:ℝ)/16 ∧ za j i∈Icc M (2*M)) ∧
      let Good := fun j k (i : Fin 2) =>
        Acut*(anchor j i).den ≤ Q k ∧
          Bmajor*R^2 ≤ c*(Q k:ℝ)*(anchor j i).den
      (∀ j, match band j with
        | none => ∃ i, ¬Good j kmax i
        | some k => k ≤ kmax ∧ (∀ i, Good j k i) ∧
            (k=0 ∨ ∃ i, ¬Good j (k-1) i)) ∧
      (∀ j∈S, ∀ k, band j=some k → ∀ i, ∀ q : ℚ,
        (q:ℝ)∈Ioo (h (t j i)-delta) (h (t j i)+delta) →
        (∀ r : ℚ, (r:ℝ)∈Ioo (h (t j i)-delta) (h (t j i)+delta) →
          q.den ≤ r.den) →
        Acut*q.den ≤ Q k ∧ Bmajor*R^2 ≤ c*(Q k:ℝ)*q.den) ∧
      (∀ k, ((S.filter (fun j => band j=some (k+1))).card:ℝ) ≤ 2*Cost (Q k)) ∧
      ((S.filter (fun j => band j=none)).card:ℝ) ≤ 2*Cost (Q kmax) := by
  exact double_difference_two_probe_dyadic_band_card S F N Qbase kmax Acut base Bmajor
    hr hs hd hy hprod hshift hw hsmall hc hU hT hM hN hR hNM hphase hf hlower hjets
    hnegative hAcut hAQ hBmajor hpoints

#print axioms double_difference_two_probe_dyadic_band_card

/-- Unchanged existing private arithmetic proof copied for scratch access;
promotion reuses the original declaration. -/
private theorem huxley_sharp_tail_quadratic_density_scale
    {σ c J M N R Q : ℝ}
    (hσ : 0 < σ) (hc : 0 < c) (hJ : 0 < J)
    (hM : 0 < M) (hN : 0 < N) (hR : 0 < R) (hQ : 0 < Q)
    (hNQ : N*Q ≤ M) :
    let Vcurv := 3*J*M/(2*σ*N*R^2)
    let D := 64*σ*R^2/(c*Q)
    let C := (6*J/σ)*(64*σ/c)^2+192*σ/c
    4*Vcurv*D^2+3*D*(2+Real.log (D+1)) ≤
      C*(M*R^2/(N*Q^2))*(2+Real.log (D+1)) := by
  intro Vcurv D C
  let A := 64*σ/c
  let K := M*R^2/(N*Q^2)
  let L := 2+Real.log (D+1)
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  have hK : 0 ≤ K := by dsimp only [K]; positivity
  have hD : 0 ≤ D := by dsimp only [D]; positivity
  have hL : 1 ≤ L := by
    have hh := Real.log_nonneg (show 1 ≤ D+1 by linarith only [hD])
    dsimp only [L]
    linarith only [hh]
  have hbase : R^2/Q ≤ K := by
    apply (div_le_div_iff₀ hQ (by positivity : 0 < N*Q^2)).mpr
    nlinarith only [mul_le_mul_of_nonneg_right hNQ (show 0 ≤ R^2*Q by positivity)]
  have hfirst : 4*Vcurv*D^2 ≤ (6*J/σ)*A^2*K*L := by
    have he : 4*Vcurv*D^2 = (6*J/σ)*A^2*K := by
      dsimp only [Vcurv,D,A,K]
      field_simp
      ring
    rw [he]
    exact le_mul_of_one_le_right (by positivity) hL
  have hsecond : 3*D*L ≤ 3*A*K*L := by
    have he : D=A*(R^2/Q) := by dsimp only [D,A]; ring
    rw [he,←mul_assoc (3:ℝ) A]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hbase (by positivity)) (by linarith only [hL])
  have hh := add_le_add hfirst hsecond
  convert hh using 1
  dsimp only [C,A]
  ring

example
    {σ c J M N R Q : ℝ}
    (hσ : 0 < σ) (hc : 0 < c) (hJ : 0 < J)
    (hM : 0 < M) (hN : 0 < N) (hR : 0 < R) (hQ : 0 < Q)
    (hNQ : N*Q ≤ M) :
    let Vcurv := 3*J*M/(2*σ*N*R^2)
    let D := 64*σ*R^2/(c*Q)
    let C := (6*J/σ)*(64*σ/c)^2+192*σ/c
    4*Vcurv*D^2+3*D*(2+Real.log (D+1)) ≤
      C*(M*R^2/(N*Q^2))*(2+Real.log (D+1)) := by
  exact huxley_sharp_tail_quadratic_density_scale hσ hc hJ hM hN hR hQ hNQ

#print axioms huxley_sharp_tail_quadratic_density_scale

/-- Unchanged existing private arithmetic proof copied for scratch access;
promotion reuses the original declaration. -/
private theorem huxley_anchor_complement_quadratic_density_scale
    (Q Acut : ℕ) {σ c J M N R B : ℝ}
    (hσ : 0 < σ) (hc : 0 < c) (hJ : 0 < J)
    (hM : 0 < M) (hN : 0 < N) (hR : 0 < R)
    (hA : 2 ≤ Acut) (hAQ : Acut ≤ Q) (hB : 0 ≤ B)
    (hNQ : N*(Q:ℝ) ≤ M) :
    let Vcurv := 3*J*M/(2*σ*N*R^2)
    let delta := c/(64*σ*R^2)
    let Dlow := B*R^2/(c*(Q:ℝ))
    let Dhigh := 64*σ*R^2/(c*((Q/Acut+1:ℕ):ℝ))
    let Dupper := 64*σ*R^2/(c*((Q:ℝ)/Acut))
    let Ctail := (6*J/σ)*(64*σ/c)^2+192*σ/c
    let Clow := (3*J/σ+c/(32*σ))*(B/c)^2+B/c
    (4*Vcurv*Dhigh^2+3*Dhigh*(2+Real.log (Dhigh+1)))+
      Dlow*(2*(Vcurv+delta)*Dlow+1) ≤
        ((Acut:ℝ)^2*Ctail+Clow)*(M*R^2/(N*(Q:ℝ)^2))*
          (2+Real.log (Dupper+1)) := by
  intro Vcurv delta Dlow Dhigh Dupper Ctail Clow
  have hAp : 0 < Acut := by omega
  have hQp : 0 < Q := by omega
  have hAr : (0:ℝ) < Acut := Nat.cast_pos.mpr hAp
  have hQr : (0:ℝ) < Q := Nat.cast_pos.mpr hQp
  have hA1 : (1:ℝ) ≤ Acut := by exact_mod_cast (show 1 ≤ Acut by omega)
  have hQ1 : (1:ℝ) ≤ Q := by exact_mod_cast hQp
  have hNM : N ≤ M := by
    have hh : N ≤ N*(Q:ℝ) := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hQ1 hN.le
    exact hh.trans hNQ
  have hthreshold : (Q:ℝ)/Acut ≤ (Q/Acut+1:ℕ) := by
    apply (div_le_iff₀ hAr).mpr
    have hh : Q < Acut*(Q/Acut+1) := Nat.lt_mul_div_succ Q hAp
    have hr : (Q:ℝ) < (Acut:ℝ)*((Q/Acut+1:ℕ):ℝ) := by exact_mod_cast hh
    simpa only [mul_comm] using hr.le
  have hDhigh : 0 ≤ Dhigh := by dsimp only [Dhigh]; positivity
  have hDupper : 0 ≤ Dupper := by dsimp only [Dupper]; positivity
  have hDle : Dhigh ≤ Dupper :=
    div_le_div_of_nonneg_left (by positivity)
      (mul_pos hc (div_pos hQr hAr)) (mul_le_mul_of_nonneg_left hthreshold hc.le)
  have hlog : 1 ≤ 2+Real.log (Dupper+1) := by
    have hh := Real.log_nonneg (show 1 ≤ Dupper+1 by linarith only [hDupper])
    linarith only [hh]
  have hNQeff : N*((Q:ℝ)/Acut) ≤ M :=
    (mul_le_mul_of_nonneg_left (div_le_self hQr.le hA1) hN.le).trans hNQ
  have hhigh :
      4*Vcurv*Dhigh^2+3*Dhigh*(2+Real.log (Dhigh+1)) ≤
        (Acut:ℝ)^2*Ctail*(M*R^2/(N*(Q:ℝ)^2))*(2+Real.log (Dupper+1)) := by
    have hmono :
        4*Vcurv*Dhigh^2+3*Dhigh*(2+Real.log (Dhigh+1)) ≤
          4*Vcurv*Dupper^2+3*Dupper*(2+Real.log (Dupper+1)) := by
      have hX : 0 ≤ Vcurv := by dsimp only [Vcurv]; positivity
      have hlogHigh : 0 ≤ Real.log (Dhigh+1) :=
        Real.log_nonneg (by linarith only [hDhigh])
      gcongr
    have hh := hmono.trans
      (huxley_sharp_tail_quadratic_density_scale hσ hc hJ hM hN hR
        (div_pos hQr hAr) hNQeff)
    change _ ≤ Ctail*(M*R^2/(N*((Q:ℝ)/Acut)^2))*(2+Real.log (Dupper+1)) at hh
    convert hh using 1
    field_simp
  let E := B/c
  let K := M*R^2/(N*(Q:ℝ)^2)
  have hE : 0 ≤ E := by dsimp only [E]; positivity
  have hK : 0 ≤ K := by dsimp only [K]; positivity
  have hbase : R^2/(Q:ℝ) ≤ K := by
    apply (div_le_div_iff₀ hQr (by positivity : 0 < N*(Q:ℝ)^2)).mpr
    nlinarith only [mul_le_mul_of_nonneg_right hNQ
      (show 0 ≤ R^2*(Q:ℝ) by positivity)]
  have hsquare : R^2/(Q:ℝ)^2 ≤ K := by
    apply (div_le_div_iff₀ (sq_pos_of_pos hQr)
      (by positivity : 0 < N*(Q:ℝ)^2)).mpr
    nlinarith only [mul_le_mul_of_nonneg_right hNM
      (show 0 ≤ R^2*(Q:ℝ)^2 by positivity)]
  have hlowRaw : Dlow*(2*(Vcurv+delta)*Dlow+1) ≤ Clow*K := by
    have hsecond : ((c/(32*σ))*E^2)*(R^2/(Q:ℝ)^2) ≤ ((c/(32*σ))*E^2)*K :=
      mul_le_mul_of_nonneg_left hsquare (by positivity)
    have hthird : E*(R^2/(Q:ℝ)) ≤ E*K := mul_le_mul_of_nonneg_left hbase hE
    calc
      _ = ((3*J/σ)*E^2*K)+((c/(32*σ))*E^2)*(R^2/(Q:ℝ)^2)+
          E*(R^2/(Q:ℝ)) := by
        dsimp only [Vcurv,delta,Dlow,E,K]
        field_simp
        ring
      _ ≤ ((3*J/σ)*E^2*K)+((c/(32*σ))*E^2)*K+E*K :=
        add_le_add (add_le_add le_rfl hsecond) hthird
      _ = _ := by dsimp only [Clow,E]; ring
  have hlow : Dlow*(2*(Vcurv+delta)*Dlow+1) ≤
      Clow*K*(2+Real.log (Dupper+1)) := by
    apply hlowRaw.trans
    exact le_mul_of_one_le_right (by dsimp only [Clow]; positivity) hlog
  convert add_le_add hhigh hlow using 1
  dsimp only [K]
  ring

example
    (Q Acut : ℕ) {σ c J M N R B : ℝ}
    (hσ : 0 < σ) (hc : 0 < c) (hJ : 0 < J)
    (hM : 0 < M) (hN : 0 < N) (hR : 0 < R)
    (hA : 2 ≤ Acut) (hAQ : Acut ≤ Q) (hB : 0 ≤ B)
    (hNQ : N*(Q:ℝ) ≤ M) :
    let Vcurv := 3*J*M/(2*σ*N*R^2)
    let delta := c/(64*σ*R^2)
    let Dlow := B*R^2/(c*(Q:ℝ))
    let Dhigh := 64*σ*R^2/(c*((Q/Acut+1:ℕ):ℝ))
    let Dupper := 64*σ*R^2/(c*((Q:ℝ)/Acut))
    let Ctail := (6*J/σ)*(64*σ/c)^2+192*σ/c
    let Clow := (3*J/σ+c/(32*σ))*(B/c)^2+B/c
    (4*Vcurv*Dhigh^2+3*Dhigh*(2+Real.log (Dhigh+1)))+
      Dlow*(2*(Vcurv+delta)*Dlow+1) ≤
        ((Acut:ℝ)^2*Ctail+Clow)*(M*R^2/(N*(Q:ℝ)^2))*
          (2+Real.log (Dupper+1)) := by
  exact huxley_anchor_complement_quadratic_density_scale Q Acut hσ hc hJ hM hN hR hA hAQ hB hNQ

#print axioms huxley_anchor_complement_quadratic_density_scale


/-- The SAME least-band/root family has source-scale quadratic density,
using the existing arithmetic bounds rather than new counting assumptions. -/
private theorem double_difference_two_probe_dyadic_quadratic_density
    (S : Finset ℤ) (F : ℝ → ℝ) (N Qbase kmax Acut : ℕ) (base : Fin 2 → ℝ) (Bmajor : ℝ)
    {r s d y w c U T M R : ℝ}
    (hr : 0 ≤ r) (hs : 0 ≤ s) (hd : 0 < d)
    (hy : y∈Icc (1:ℝ) 2) (hprod : r*s=d*y)
    (hshift : r+s ≤ w) (hw : w ≤ 1/4) (hsmall : 2*U*w ≤ c/64)
    (hc : 0 < c) (hU : 0 < U) (hT : 0 < T) (hM : 0 < M)
    (hN : 0 < N) (hR : 0 < R)
    (hphase : T*(N:ℝ)*R^2=M^3)
    (hf : ∀ u, 0 < u → ContDiffAt ℝ ∞ F u)
    (hlower : ∀ u∈Icc (1/2:ℝ) 3, c ≤ iteratedDeriv 5 F u)
    (hjets : ∀ u∈Icc (1/2:ℝ) 3, ∀ n, 1 ≤ n → n ≤ 7 → |iteratedDeriv n F u| ≤ U)
    (hnegative : ∀ u∈Icc (1/2:ℝ) 3, iteratedDeriv 4 F u ≤ -c)
    (hAcut : 2 ≤ Acut) (hAQ : Acut ≤ Qbase) (hBmajor : 0 ≤ Bmajor)
    (hpoints : ∀ j∈S, ∀ i, base i+(N:ℝ)*j∈Icc (M+(N:ℝ)/4) (2*M-(N:ℝ)/4))
    (hNQmax : (N:ℝ)*(Qbase*2^kmax:ℕ) ≤ M) :
    let f := fun v => T*((F (v/M)-F (v/M+r)-F (v/M+s)+F (v/M+r+s))/d)
    let h := fun w => iteratedDeriv 2 f w/2
    let t := fun (j : ℤ) (i : Fin 2) => base i+(N:ℝ)*j
    let delta := c/(64*R^2)
    let Q := fun k : ℕ => Qbase*2^k
    let Ctail := 4*U*(64/c)^2+192/c
    let Clow := (2*U+c/32)*(Bmajor/c)^2+Bmajor/c
    let Cerror := (Acut:ℝ)^2*Ctail+Clow
    let Density := fun k => 2*Cerror*(M*R^2/((N:ℝ)*(Q k:ℝ)^2))*
      (2+Real.log (64*R^2/(c*((Q k:ℝ)/Acut))+1))
    ∃ (anchor : ℤ → Fin 2 → ℚ) (band : ℤ → Option ℕ) (za : ℤ → Fin 2 → ℝ),
      (∀ j∈S, ∀ i, (anchor j i:ℝ)∈Ioo (h (t j i)-delta) (h (t j i)+delta) ∧
        ∀ q : ℚ, (q:ℝ)∈Ioo (h (t j i)-delta) (h (t j i)+delta) →
          (anchor j i).den ≤ q.den) ∧
      (∀ j∈S, ∀ i, h (za j i)=(anchor j i:ℝ) ∧
        |za j i-t j i| ≤ (N:ℝ)/16 ∧ za j i∈Icc M (2*M)) ∧
      let Good := fun j k (i : Fin 2) =>
        Acut*(anchor j i).den ≤ Q k ∧
          Bmajor*R^2 ≤ c*(Q k:ℝ)*(anchor j i).den
      (∀ j, match band j with
        | none => ∃ i, ¬Good j kmax i
        | some k => k ≤ kmax ∧ (∀ i, Good j k i) ∧
            (k=0 ∨ ∃ i, ¬Good j (k-1) i)) ∧
      (∀ j∈S, ∀ k, band j=some k → ∀ i, ∀ q : ℚ,
        (q:ℝ)∈Ioo (h (t j i)-delta) (h (t j i)+delta) →
        (∀ r : ℚ, (r:ℝ)∈Ioo (h (t j i)-delta) (h (t j i)+delta) →
          q.den ≤ r.den) →
        Acut*q.den ≤ Q k ∧ Bmajor*R^2 ≤ c*(Q k:ℝ)*q.den) ∧
      (∀ k ≤ kmax, ((S.filter (fun j => band j=some (k+1))).card:ℝ) ≤ Density k) ∧
      ((S.filter (fun j => band j=none)).card:ℝ) ≤ Density kmax := by
  classical
  intro f h t delta Q Ctail Clow Cerror Density
  have hNp : (0:ℝ) < N := Nat.cast_pos.mpr hN
  have hqbase : 1 ≤ Qbase := by omega
  have hqmax : 1 ≤ Qbase*2^kmax :=
    hqbase.trans (Nat.le_mul_of_pos_right Qbase (pow_pos (by decide) kmax))
  have hqmaxR : (1:ℝ) ≤ (Qbase*2^kmax:ℕ) := by exact_mod_cast hqmax
  have hNM : (N:ℝ) ≤ M := by nlinarith only [hNQmax,hqmaxR,hNp]
  obtain ⟨anchor,band,za,hanchor,hroots,hband,htransfer,hcounts,htail⟩ :=
    double_difference_two_probe_dyadic_band_card S F N Qbase kmax Acut base Bmajor
      hr hs hd hy hprod hshift hw hsmall hc hU hT hM hN hR hNM hphase hf hlower hjets
      hnegative hAcut hAQ hBmajor hpoints
  let Vbound := U*M/((N:ℝ)*R^2)
  let Cost := fun q : ℕ =>
    let Dlow := Bmajor*R^2/(c*(q:ℝ))
    let Dhigh := 64*R^2/(c*((q/Acut+1:ℕ):ℝ))
    4*Vbound*Dhigh^2+3*Dhigh*(2+Real.log (Dhigh+1))+
      Dlow*(2*(Vbound+delta)*Dlow+1)
  have hcost k (hk : k ≤ kmax) : 2*Cost (Q k) ≤ Density k := by
    have hqA : Acut ≤ Q k :=
      hAQ.trans (Nat.le_mul_of_pos_right Qbase (pow_pos (by decide : 0 < (2:ℕ)) k))
    have hqmax : Q k ≤ Q kmax :=
      Nat.mul_le_mul_left Qbase (Nat.pow_le_pow_right (by decide : 0 < (2:ℕ)) hk)
    have hNQ : (N:ℝ)*(Q k:ℝ) ≤ M :=
      (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr hqmax) (Nat.cast_nonneg N)).trans hNQmax
    have hh := huxley_anchor_complement_quadratic_density_scale (Q k) Acut
      (σ:=1) (J:=2*U/3) (by norm_num) hc (by positivity) hM hNp hR hAcut hqA hBmajor hNQ
    have hthree : 3*(2*U/3)=2*U := by ring
    have hsix : 6*(2*U/3)=4*U := by ring
    have hV : 2*U*M/(2*(N:ℝ)*R^2)=Vbound := by dsimp only [Vbound]; ring
    have hbound : Cost (Q k) ≤ Cerror*(M*R^2/((N:ℝ)*(Q k:ℝ)^2))*
        (2+Real.log (64*R^2/(c*((Q k:ℝ)/Acut))+1)) := by
      simpa only [mul_one,one_mul,div_one,hthree,hsix,hV] using hh
    calc
      _ ≤ 2*(Cerror*(M*R^2/((N:ℝ)*(Q k:ℝ)^2))*
          (2+Real.log (64*R^2/(c*((Q k:ℝ)/Acut))+1))) :=
        mul_le_mul_of_nonneg_left hbound (by norm_num)
      _ = _ := by dsimp only [Density]; ring
  refine ⟨anchor,band,za,hanchor,hroots,?_⟩
  intro Good
  exact ⟨hband,htransfer,fun k hk => (hcounts k).trans (hcost k hk),
    htail.trans (hcost kmax le_rfl)⟩

example
    (S : Finset ℤ) (F : ℝ → ℝ) (N Qbase kmax Acut : ℕ) (base : Fin 2 → ℝ) (Bmajor : ℝ)
    {r s d y w c U T M R : ℝ}
    (hr : 0 ≤ r) (hs : 0 ≤ s) (hd : 0 < d)
    (hy : y∈Icc (1:ℝ) 2) (hprod : r*s=d*y)
    (hshift : r+s ≤ w) (hw : w ≤ 1/4) (hsmall : 2*U*w ≤ c/64)
    (hc : 0 < c) (hU : 0 < U) (hT : 0 < T) (hM : 0 < M)
    (hN : 0 < N) (hR : 0 < R)
    (hphase : T*(N:ℝ)*R^2=M^3)
    (hf : ∀ u, 0 < u → ContDiffAt ℝ ∞ F u)
    (hlower : ∀ u∈Icc (1/2:ℝ) 3, c ≤ iteratedDeriv 5 F u)
    (hjets : ∀ u∈Icc (1/2:ℝ) 3, ∀ n, 1 ≤ n → n ≤ 7 → |iteratedDeriv n F u| ≤ U)
    (hnegative : ∀ u∈Icc (1/2:ℝ) 3, iteratedDeriv 4 F u ≤ -c)
    (hAcut : 2 ≤ Acut) (hAQ : Acut ≤ Qbase) (hBmajor : 0 ≤ Bmajor)
    (hpoints : ∀ j∈S, ∀ i, base i+(N:ℝ)*j∈Icc (M+(N:ℝ)/4) (2*M-(N:ℝ)/4))
    (hNQmax : (N:ℝ)*(Qbase*2^kmax:ℕ) ≤ M) :
    let f := fun v => T*((F (v/M)-F (v/M+r)-F (v/M+s)+F (v/M+r+s))/d)
    let h := fun w => iteratedDeriv 2 f w/2
    let t := fun (j : ℤ) (i : Fin 2) => base i+(N:ℝ)*j
    let delta := c/(64*R^2)
    let Q := fun k : ℕ => Qbase*2^k
    let Ctail := 4*U*(64/c)^2+192/c
    let Clow := (2*U+c/32)*(Bmajor/c)^2+Bmajor/c
    let Cerror := (Acut:ℝ)^2*Ctail+Clow
    let Density := fun k => 2*Cerror*(M*R^2/((N:ℝ)*(Q k:ℝ)^2))*
      (2+Real.log (64*R^2/(c*((Q k:ℝ)/Acut))+1))
    ∃ (anchor : ℤ → Fin 2 → ℚ) (band : ℤ → Option ℕ) (za : ℤ → Fin 2 → ℝ),
      (∀ j∈S, ∀ i, (anchor j i:ℝ)∈Ioo (h (t j i)-delta) (h (t j i)+delta) ∧
        ∀ q : ℚ, (q:ℝ)∈Ioo (h (t j i)-delta) (h (t j i)+delta) →
          (anchor j i).den ≤ q.den) ∧
      (∀ j∈S, ∀ i, h (za j i)=(anchor j i:ℝ) ∧
        |za j i-t j i| ≤ (N:ℝ)/16 ∧ za j i∈Icc M (2*M)) ∧
      let Good := fun j k (i : Fin 2) =>
        Acut*(anchor j i).den ≤ Q k ∧
          Bmajor*R^2 ≤ c*(Q k:ℝ)*(anchor j i).den
      (∀ j, match band j with
        | none => ∃ i, ¬Good j kmax i
        | some k => k ≤ kmax ∧ (∀ i, Good j k i) ∧
            (k=0 ∨ ∃ i, ¬Good j (k-1) i)) ∧
      (∀ j∈S, ∀ k, band j=some k → ∀ i, ∀ q : ℚ,
        (q:ℝ)∈Ioo (h (t j i)-delta) (h (t j i)+delta) →
        (∀ r : ℚ, (r:ℝ)∈Ioo (h (t j i)-delta) (h (t j i)+delta) →
          q.den ≤ r.den) →
        Acut*q.den ≤ Q k ∧ Bmajor*R^2 ≤ c*(Q k:ℝ)*q.den) ∧
      (∀ k ≤ kmax, ((S.filter (fun j => band j=some (k+1))).card:ℝ) ≤ Density k) ∧
      ((S.filter (fun j => band j=none)).card:ℝ) ≤ Density kmax := by
  exact double_difference_two_probe_dyadic_quadratic_density S F N Qbase kmax Acut base Bmajor
    hr hs hd hy hprod hshift hw hsmall hc hU hT hM hN hR hphase hf hlower hjets
    hnegative hAcut hAQ hBmajor hpoints hNQmax

#print axioms double_difference_two_probe_dyadic_quadratic_density

/-- The actual selected double-phase factory: source-derived anchors, least
bands and quadratic counts are chosen BEFORE each selected family; that SAME
family is completed at constructed roots with one common Fourier mode. -/
private theorem double_difference_selected_dyadic_family_fourier
    {c U : ℝ} (hc : 0 < c) (hU : 0 < U) :
    ∃ C ≥ (1:ℝ), ∀ (ι : Type*) (S : ι → Finset ℤ) (F : ℝ → ℝ)
      (y rshift sshift : ι → ℝ) (base : Fin 2 → ℤ) (N Qbase kmax Acut : ℕ)
      (Bmajor d w T M R : ℝ),
      0 < N → 0 < d → w ≤ 1/4 → 2*U*w ≤ c/64 → (∀ i, y i∈Icc (1:ℝ) 2) →
      (∀ i, 0 ≤ rshift i ∧ 0 ≤ sshift i ∧
        rshift i*sshift i=d*y i ∧ rshift i+sshift i ≤ w) →
      0 < T → 0 < M → 0 < R →
      (∀ w, 0 < w → ContDiffAt ℝ ∞ F w) →
      (∀ u∈Icc (1/2:ℝ) 3, ∀ n, 1 ≤ n → n ≤ 7 → |iteratedDeriv n F u| ≤ U) →
      (∀ u∈Icc (1/2:ℝ) 3, c ≤ iteratedDeriv 5 F u) →
      (∀ w∈Icc (1/2:ℝ) 3, iteratedDeriv 4 F w ≤ -c) →
      T*(N:ℝ)*R^2=M^3 → 2 ≤ Acut → Acut ≤ Qbase → 128 ≤ Bmajor →
      (∀ i, ∀ j∈S i, ∀ p,
        (base p:ℝ)+(N:ℝ)*j∈Icc (M+(N:ℝ)/4) (2*M-(N:ℝ)/4)) →
      (N:ℝ)*(Qbase*2^kmax:ℕ) ≤ M →
      7*(N:ℝ)+2 ≤ M/4 →
      (3*U)*(6*(N:ℝ)+1)^4 ≤ M*(N:ℝ)*R^2 →
      (3*U/4)*(6*(N:ℝ)+1)^2 ≤ (N:ℝ)*R^2 →
      let f := fun i v => T*((F (v/M)-F (v/M+rshift i)-F (v/M+sshift i)+
        F (v/M+rshift i+sshift i))/d)
      let h := fun i w => iteratedDeriv 2 (f i) w/2
      let t := fun (j : ℤ) (p : Fin 2) => (base p:ℝ)+(N:ℝ)*j
      let L := fun (j : ℤ) (p : Fin 2) => base p+(N:ℤ)*j+2*(N:ℤ)
      let delta := c/(64*R^2)
      let Q := fun k : ℕ => Qbase*2^k
      let Ctail := 4*U*(64/c)^2+192/c
      let Clow := (2*U+c/32)*(Bmajor/c)^2+Bmajor/c
      let Cerror := (Acut:ℝ)^2*Ctail+Clow
      let Density := fun k => 2*Cerror*(M*R^2/((N:ℝ)*(Q k:ℝ)^2))*
        (2+Real.log (64*R^2/(c*((Q k:ℝ)/Acut))+1))
      ∃ (anchor : ι → ℤ → Fin 2 → ℚ) (band : ι → ℤ → Option ℕ)
        (za : ι → ℤ → Fin 2 → ℝ),
        (∀ i, ∀ j∈S i, ∀ p,
          (anchor i j p:ℝ)∈Ioo (h i (t j p)-delta) (h i (t j p)+delta) ∧
          ∀ q : ℚ, (q:ℝ)∈Ioo (h i (t j p)-delta) (h i (t j p)+delta) →
            (anchor i j p).den ≤ q.den) ∧
        (∀ i, ∀ j∈S i, ∀ p, h i (za i j p)=(anchor i j p:ℝ) ∧
          |za i j p-t j p| ≤ (N:ℝ)/16 ∧ za i j p∈Icc M (2*M)) ∧
        let Good := fun i j k (p : Fin 2) =>
          Acut*(anchor i j p).den ≤ Q k ∧
            Bmajor*R^2 ≤ c*(Q k:ℝ)*(anchor i j p).den
        (∀ i, ∀ j∈S i, match band i j with
          | none => ∃ p, ¬Good i j kmax p
          | some k => k ≤ kmax ∧ (∀ p, Good i j k p) ∧
              (k=0 ∨ ∃ p, ¬Good i j (k-1) p)) ∧
        (∀ i, ∀ k ≤ kmax,
          (((S i).filter (fun j => band i j=some (k+1))).card:ℝ) ≤ Density k) ∧
        (∀ i, (((S i).filter (fun j => band i j=none)).card:ℝ) ≤ Density kmax) ∧
        ∀ k : ℕ, Q k ≤ N →
        ∀ (E : Finset (ι × (ℤ × Fin 2))) (H : ι × (ℤ × Fin 2) → ℕ),
        (∀ i∈E, i.2.1∈S i.1 ∧ band i.1 i.2.1=some k) →
        (∀ i∈E, H i ≤ N) →
        ∃ (r : ι × (ℤ × Fin 2) → ℚ) (z : ι × (ℤ × Fin 2) → ℝ),
        (∀ i∈E, (r i).den ≤ Q k ∧ Q k ≤ 2*(r i).den ∧
          (anchor i.1 i.2.1 i.2.2:ℝ) < r i ∧
          |(r i:ℝ)-(anchor i.1 i.2.1 i.2.2:ℝ)| ≤ delta ∧
          z i∈Icc (za i.1 i.2.1 i.2.2) (za i.1 i.2.1 i.2.2+(N:ℝ)/16) ∧
          h i.1 (z i)=(r i:ℝ)) ∧
        (∀ i∈E, |z i-t i.2.1 i.2.2| ≤ (N:ℝ)/8 ∧
          ∀ a b : ℝ, a+(N:ℝ)/4 ≤ t i.2.1 i.2.2 →
            t i.2.1 i.2.2 ≤ b-(N:ℝ)/4 → z i∈Ioo a b) ∧
        let m := fun i => round (z i)
        let A := fun i => (L i.2.1 i.2.2-m i).toNat
        let q := fun i => (r i).den
        let μ := fun i => iteratedDeriv 3 (f i.1) (m i)/6
        let ell := fun i => deriv (f i.1) (m i)
        let U₃ := U/(2*(N:ℝ)*R^2)
        (∀ i∈E, |z i-(m i:ℝ)| ≤ 1/2 ∧
          N ≤ A i ∧ A i ≤ 3*N ∧ m i+(A i:ℤ)=L i.2.1 i.2.2) ∧
        (∀ i∈E, 1 ≤ A i ∧ q i ≤ A i ∧ 1 ≤ μ i*(q i:ℝ)^2*A i) ∧
        ∀ (K₀ : ℕ) [NeZero K₀], 63*U₃*(Q k:ℝ)*(N:ℝ)^2 ≤ K₀ →
        (∀ i∈E, 7*(μ i*(q i:ℝ)*(A i:ℝ)^2) ≤ K₀) ∧
        ∃ v : ι × (ℤ × Fin 2) → ℤ, (∀ i∈E, (q i:ℤ) ∣ (r i).num*v i-1) ∧
        let b := fun i (p : Fin 2) => (⌊(q i:ℝ)*ell i⌋+(p:ℕ) : ℤ)
        let tau := fun i p => ((b i p:ℝ)-(q i:ℝ)*ell i)/2
        let s := fun i => Real.sqrt (2/(3*μ i*(q i:ℝ)))
        let K := fun i => -2*μ i*(s i)^3
        let x := fun i p =>
          (![-(v i:ℝ)*b i p/q i,-(v i:ℝ)/q i,K i,3*K i*tau i p/2] : Fin 4 → ℝ)
        ∃ mode : ZMod K₀,
          (∑ i∈E, ‖∑ n∈Finset.Ioc (L i.2.1 i.2.2) (L i.2.1 i.2.2+H i),
            (𝐞 (f i.1 n):ℂ)‖) ≤
            C*((1+Real.log K₀)*
              (∑ i∈E, ∑ p : Fin 2,
                (Real.sqrt (2*(q i:ℝ))/((q i:ℝ)*Real.sqrt (μ i*A i)))*
                ‖∑ j : ZMod K₀,ZMod.stdAddChar (-(j*mode))*
                  GafniTao.fordAdditiveCharacter (∑ d,x i p d*
                    (![(j.val+1:ℝ),(j.val+1:ℝ)^2,(j.val+1:ℝ)^((3:ℝ)/2),
                      Real.sqrt (j.val+1:ℝ)] : Fin 4 → ℝ) d)‖)+
              ∑ i∈E, (Real.sqrt (A i)*Real.log (2*(A i:ℝ))+1/(μ i*(A i:ℝ)^2))) := by
  classical
  obtain ⟨C,hC,hfourier⟩ := double_difference_dyadic_anchor_source_fourier hc hU
  refine ⟨C,hC,?_⟩
  intro ι S F y rshift sshift base N Qbase kmax Acut Bmajor d w T M R
    hN hd hw hsmall hy hshifts hT hM hR hreg hbound hlower hnegative hscale
    hAcut hAQ hBmajor hpoints hNQmax hbuffer hfourBudget hquadBudget
    f h t L delta Q Ctail Clow Cerror Density
  have hNp : (0:ℝ) < N := Nat.cast_pos.mpr hN
  have hB : 0 ≤ Bmajor := le_trans (by positivity : (0:ℝ) ≤ 128) hBmajor
  choose anchor band za hanchor hroots hbandAll _htransfer hcounts htail using
    fun i => double_difference_two_probe_dyadic_quadratic_density (S i) F
      N Qbase kmax Acut (fun p => (base p:ℝ)) Bmajor
      (hshifts i).1 (hshifts i).2.1 hd (hy i) (hshifts i).2.2.1
      (hshifts i).2.2.2 hw hsmall hc hU hT hM hN hR hscale hreg hlower hbound
      hnegative hAcut hAQ hB (hpoints i) hNQmax
  have hband i j (_hj : j∈S i) := hbandAll i j
  refine ⟨anchor,band,za,hanchor,hroots,?_⟩
  intro Good
  refine ⟨hband,hcounts,htail,?_⟩
  intro k hQN E H hE hH
  have hgood i (hi : i∈E) : Good i.1 i.2.1 k i.2.2 := by
    have hh := hband i.1 i.2.1 (hE i hi).1
    rw [(hE i hi).2] at hh
    exact hh.2.1 i.2.2
  have hL j p : (L j p:ℝ)-2*(N:ℝ)=t j p := by
    dsimp only [L,t]
    push_cast
    ring
  have hbase i (hi : i∈E) :
      (L i.2.1 i.2.2:ℝ)-2*(N:ℝ)∈Icc M (2*M) := by
    rw [hL]
    have hh := hpoints i.1 i.2.1 (hE i hi).1 i.2.2
    change M+(N:ℝ)/4 ≤ t i.2.1 i.2.2 ∧
      t i.2.1 i.2.2 ≤ 2*M-(N:ℝ)/4 at hh
    constructor <;> linarith only [hh.1,hh.2,hNp]
  have haroot i (hi : i∈E) :
      za i.1 i.2.1 i.2.2∈Ioo ((L i.2.1 i.2.2:ℝ)-2*(N:ℝ)-(N:ℝ)/8)
        ((L i.2.1 i.2.2:ℝ)-2*(N:ℝ)+(N:ℝ)/8) ∧
      h i.1 (za i.1 i.2.1 i.2.2)=(anchor i.1 i.2.1 i.2.2:ℝ) := by
    have hh := hroots i.1 i.2.1 (hE i hi).1 i.2.2
    refine ⟨?_,hh.1⟩
    rw [hL]
    have hb := abs_le.mp hh.2.1
    constructor <;> linarith only [hb.1,hb.2,hNp]
  obtain ⟨r,z,hr,hout⟩ := hfourier (ι × (ℤ × Fin 2)) E F
    (fun i => y i.1) (fun i => rshift i.1) (fun i => sshift i.1) (fun i => L i.2.1 i.2.2) H
    (fun i => anchor i.1 i.2.1 i.2.2) (fun i => za i.1 i.2.1 i.2.2)
    N (Q k) d w T M R (by omega) hH hd hw hsmall hT hM hR
    (fun i _ => hy i.1) (fun i _ => hshifts i.1) hbase hreg hbound hlower hscale
    hbuffer hfourBudget hquadBudget hQN
    (fun i hi => (Nat.mul_le_mul_right _ hAcut).trans (hgood i hi).1)
    (fun i hi => (mul_le_mul_of_nonneg_right hBmajor (sq_nonneg R)).trans (hgood i hi).2)
    haroot
  refine ⟨r,z,hr,?_,hout⟩
  intro i hi
  have ha := abs_le.mp (hroots i.1 i.2.1 (hE i hi).1 i.2.2).2.1
  have hz := (hr i hi).2.2.2.2.1
  have hdist : |z i-t i.2.1 i.2.2| ≤ (N:ℝ)/8 := by
    apply abs_le.mpr
    constructor <;> linarith only [ha.1,ha.2,hz.1,hz.2,hNp]
  refine ⟨hdist,?_⟩
  intro a b hleft hright
  have hd := abs_le.mp hdist
  constructor <;> linarith only [hd.1,hd.2,hleft,hright,hNp]

example
    {c U : ℝ} (hc : 0 < c) (hU : 0 < U) :
    ∃ C ≥ (1:ℝ), ∀ (ι : Type*) (S : ι → Finset ℤ) (F : ℝ → ℝ)
      (y rshift sshift : ι → ℝ) (base : Fin 2 → ℤ) (N Qbase kmax Acut : ℕ)
      (Bmajor d w T M R : ℝ),
      0 < N → 0 < d → w ≤ 1/4 → 2*U*w ≤ c/64 → (∀ i, y i∈Icc (1:ℝ) 2) →
      (∀ i, 0 ≤ rshift i ∧ 0 ≤ sshift i ∧
        rshift i*sshift i=d*y i ∧ rshift i+sshift i ≤ w) →
      0 < T → 0 < M → 0 < R →
      (∀ w, 0 < w → ContDiffAt ℝ ∞ F w) →
      (∀ u∈Icc (1/2:ℝ) 3, ∀ n, 1 ≤ n → n ≤ 7 → |iteratedDeriv n F u| ≤ U) →
      (∀ u∈Icc (1/2:ℝ) 3, c ≤ iteratedDeriv 5 F u) →
      (∀ w∈Icc (1/2:ℝ) 3, iteratedDeriv 4 F w ≤ -c) →
      T*(N:ℝ)*R^2=M^3 → 2 ≤ Acut → Acut ≤ Qbase → 128 ≤ Bmajor →
      (∀ i, ∀ j∈S i, ∀ p,
        (base p:ℝ)+(N:ℝ)*j∈Icc (M+(N:ℝ)/4) (2*M-(N:ℝ)/4)) →
      (N:ℝ)*(Qbase*2^kmax:ℕ) ≤ M →
      7*(N:ℝ)+2 ≤ M/4 →
      (3*U)*(6*(N:ℝ)+1)^4 ≤ M*(N:ℝ)*R^2 →
      (3*U/4)*(6*(N:ℝ)+1)^2 ≤ (N:ℝ)*R^2 →
      let f := fun i v => T*((F (v/M)-F (v/M+rshift i)-F (v/M+sshift i)+
        F (v/M+rshift i+sshift i))/d)
      let h := fun i w => iteratedDeriv 2 (f i) w/2
      let t := fun (j : ℤ) (p : Fin 2) => (base p:ℝ)+(N:ℝ)*j
      let L := fun (j : ℤ) (p : Fin 2) => base p+(N:ℤ)*j+2*(N:ℤ)
      let delta := c/(64*R^2)
      let Q := fun k : ℕ => Qbase*2^k
      let Ctail := 4*U*(64/c)^2+192/c
      let Clow := (2*U+c/32)*(Bmajor/c)^2+Bmajor/c
      let Cerror := (Acut:ℝ)^2*Ctail+Clow
      let Density := fun k => 2*Cerror*(M*R^2/((N:ℝ)*(Q k:ℝ)^2))*
        (2+Real.log (64*R^2/(c*((Q k:ℝ)/Acut))+1))
      ∃ (anchor : ι → ℤ → Fin 2 → ℚ) (band : ι → ℤ → Option ℕ)
        (za : ι → ℤ → Fin 2 → ℝ),
        (∀ i, ∀ j∈S i, ∀ p,
          (anchor i j p:ℝ)∈Ioo (h i (t j p)-delta) (h i (t j p)+delta) ∧
          ∀ q : ℚ, (q:ℝ)∈Ioo (h i (t j p)-delta) (h i (t j p)+delta) →
            (anchor i j p).den ≤ q.den) ∧
        (∀ i, ∀ j∈S i, ∀ p, h i (za i j p)=(anchor i j p:ℝ) ∧
          |za i j p-t j p| ≤ (N:ℝ)/16 ∧ za i j p∈Icc M (2*M)) ∧
        let Good := fun i j k (p : Fin 2) =>
          Acut*(anchor i j p).den ≤ Q k ∧
            Bmajor*R^2 ≤ c*(Q k:ℝ)*(anchor i j p).den
        (∀ i, ∀ j∈S i, match band i j with
          | none => ∃ p, ¬Good i j kmax p
          | some k => k ≤ kmax ∧ (∀ p, Good i j k p) ∧
              (k=0 ∨ ∃ p, ¬Good i j (k-1) p)) ∧
        (∀ i, ∀ k ≤ kmax,
          (((S i).filter (fun j => band i j=some (k+1))).card:ℝ) ≤ Density k) ∧
        (∀ i, (((S i).filter (fun j => band i j=none)).card:ℝ) ≤ Density kmax) ∧
        ∀ k : ℕ, Q k ≤ N →
        ∀ (E : Finset (ι × (ℤ × Fin 2))) (H : ι × (ℤ × Fin 2) → ℕ),
        (∀ i∈E, i.2.1∈S i.1 ∧ band i.1 i.2.1=some k) →
        (∀ i∈E, H i ≤ N) →
        ∃ (r : ι × (ℤ × Fin 2) → ℚ) (z : ι × (ℤ × Fin 2) → ℝ),
        (∀ i∈E, (r i).den ≤ Q k ∧ Q k ≤ 2*(r i).den ∧
          (anchor i.1 i.2.1 i.2.2:ℝ) < r i ∧
          |(r i:ℝ)-(anchor i.1 i.2.1 i.2.2:ℝ)| ≤ delta ∧
          z i∈Icc (za i.1 i.2.1 i.2.2) (za i.1 i.2.1 i.2.2+(N:ℝ)/16) ∧
          h i.1 (z i)=(r i:ℝ)) ∧
        (∀ i∈E, |z i-t i.2.1 i.2.2| ≤ (N:ℝ)/8 ∧
          ∀ a b : ℝ, a+(N:ℝ)/4 ≤ t i.2.1 i.2.2 →
            t i.2.1 i.2.2 ≤ b-(N:ℝ)/4 → z i∈Ioo a b) ∧
        let m := fun i => round (z i)
        let A := fun i => (L i.2.1 i.2.2-m i).toNat
        let q := fun i => (r i).den
        let μ := fun i => iteratedDeriv 3 (f i.1) (m i)/6
        let ell := fun i => deriv (f i.1) (m i)
        let U₃ := U/(2*(N:ℝ)*R^2)
        (∀ i∈E, |z i-(m i:ℝ)| ≤ 1/2 ∧
          N ≤ A i ∧ A i ≤ 3*N ∧ m i+(A i:ℤ)=L i.2.1 i.2.2) ∧
        (∀ i∈E, 1 ≤ A i ∧ q i ≤ A i ∧ 1 ≤ μ i*(q i:ℝ)^2*A i) ∧
        ∀ (K₀ : ℕ) [NeZero K₀], 63*U₃*(Q k:ℝ)*(N:ℝ)^2 ≤ K₀ →
        (∀ i∈E, 7*(μ i*(q i:ℝ)*(A i:ℝ)^2) ≤ K₀) ∧
        ∃ v : ι × (ℤ × Fin 2) → ℤ, (∀ i∈E, (q i:ℤ) ∣ (r i).num*v i-1) ∧
        let b := fun i (p : Fin 2) => (⌊(q i:ℝ)*ell i⌋+(p:ℕ) : ℤ)
        let tau := fun i p => ((b i p:ℝ)-(q i:ℝ)*ell i)/2
        let s := fun i => Real.sqrt (2/(3*μ i*(q i:ℝ)))
        let K := fun i => -2*μ i*(s i)^3
        let x := fun i p =>
          (![-(v i:ℝ)*b i p/q i,-(v i:ℝ)/q i,K i,3*K i*tau i p/2] : Fin 4 → ℝ)
        ∃ mode : ZMod K₀,
          (∑ i∈E, ‖∑ n∈Finset.Ioc (L i.2.1 i.2.2) (L i.2.1 i.2.2+H i),
            (𝐞 (f i.1 n):ℂ)‖) ≤
            C*((1+Real.log K₀)*
              (∑ i∈E, ∑ p : Fin 2,
                (Real.sqrt (2*(q i:ℝ))/((q i:ℝ)*Real.sqrt (μ i*A i)))*
                ‖∑ j : ZMod K₀,ZMod.stdAddChar (-(j*mode))*
                  GafniTao.fordAdditiveCharacter (∑ d,x i p d*
                    (![(j.val+1:ℝ),(j.val+1:ℝ)^2,(j.val+1:ℝ)^((3:ℝ)/2),
                      Real.sqrt (j.val+1:ℝ)] : Fin 4 → ℝ) d)‖)+
              ∑ i∈E, (Real.sqrt (A i)*Real.log (2*(A i:ℝ))+1/(μ i*(A i:ℝ)^2))) := by
  exact double_difference_selected_dyadic_family_fourier hc hU

#print axioms double_difference_selected_dyadic_family_fourier


/-- Unchanged existing private chart proof copied for scratch access;
promotion reuses the original declaration. -/
private theorem actual_reference_gap_oriented_chart
    (S : Finset ℝ) {H : ℤ} {R U scale a b : ℝ}
    (hR : 0 < R) (hU : 0 < U) (hscale : 0 ≤ scale)
    (hhull : ∀ x∈S, ∀ y∈S, ∀ q : ℚ, (q.den:ℤ) ≤ H →
      (q:ℝ)∈Icc x y → (q:ℝ)∈S)
    (hpoints : ∀ z∈S, |z| ≤ scale+1)
    (hlabels : ∀ z∈S,
      (∃ q : ℚ, z=(q:ℝ) ∧ (q.den:ℤ) ≤ H) ∨
      (∃ m n u v : ℤ, z=(m:ℝ)/n ∧ IsCoprime m n ∧ 0 < n ∧
        0 < v ∧ v ≤ H ∧ (u:ℝ)/v∈S ∧ |m*v-u*n|=1))
    (hsep : ∀ x∈S, ∀ y∈S, x≠y → U/(4*R^2) < |x-y|)
    (ha : a∈S) (hb : b∈S) (hab : a < b)
    (hadj : ∀ z∈S, ¬(a < z ∧ z < b))
    (hends : ∃ m n p q : ℤ, a=(m:ℝ)/n ∧ b=(p:ℝ)/q ∧
      IsCoprime m n ∧ IsCoprime p q ∧ 0 < n ∧ 0 < q ∧
      R^2 ≤ U*((max n q:ℤ):ℝ)^2) :
    ∃ e r v s : ℤ, v*r-e*s=1 ∧
      ((0 < r ∧ (e:ℝ)/r=a) ∨ (r < 0 ∧ (e:ℝ)/r=b)) ∧
      s≠0 ∧ (e:ℝ)/r∈S ∧ (v:ℝ)/s∈S ∧ R^2 ≤ (r:ℝ)^2*U ∧
      |(r:ℝ)| < 4*R^2/U ∧ |(s:ℝ)| < 4*R^2/U ∧
      |(e:ℝ)| ≤ (scale+1)*(4*R^2/U) ∧
      |(v:ℝ)| ≤ (scale+1)*(4*R^2/U) := by
  obtain ⟨m,n,p,q,haval,hbval,hcopn,hcopq,hn,hq,hmax⟩ := hends
  obtain ⟨e,r,f,s,hwhich,hrmax,_hcop,hr,hs,hsr,_hsH,hfS,hdet⟩ :=
    reference_max_denominator_neighbor S (L:=a) (U:=b)
      (fun q hqH hqI => hhull a ha b hb q hqH hqI) hlabels hn hq hcopn hcopq
      (by simpa only [←haval] using ha) (by simpa only [←hbval] using hb)
      (by rw [←haval]; exact ⟨le_rfl,hab.le⟩)
      (by rw [←hbval]; exact ⟨hab.le,le_rfl⟩)
      (by simpa only [←haval,←hbval] using hab)
      (by simpa only [←haval,←hbval] using hadj)
  have heval : (e:ℝ)/r=a ∨ (e:ℝ)/r=b := by
    rcases hwhich with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · exact Or.inl haval.symm
    · exact Or.inr hbval.symm
  have heS : (e:ℝ)/r∈S := heval.elim (fun he => he ▸ ha) (fun he => he ▸ hb)
  have hrR : (0:ℝ) < r := by exact_mod_cast hr
  have hsR : (0:ℝ) < s := by exact_mod_cast hs
  have hsep' : ∀ x∈S, ∀ y∈S, x≠y → (U/R^2)/4 < |x-y| := by
    intro x hx y hy hne
    convert hsep x hx y hy hne using 1
    ring
  have hheight := (separated_reference_parent_denominator_bound S
    (div_pos hU (sq_pos_of_pos hR)) hr hs heS hfS hdet hsep').2
  have hbudget : 4/(U/R^2)=4*R^2/U := by field_simp
  rw [hbudget] at hheight
  have hsheight : (s:ℝ) < 4*R^2/U :=
    (show (s:ℝ) ≤ r by exact_mod_cast hsr).trans_lt hheight
  have hrscale : R^2 ≤ (r:ℝ)^2*U := by simpa only [hrmax,mul_comm U] using hmax
  have hsigned : ∃ e' r' : ℤ,
      ((0 < r' ∧ (e':ℝ)/r'=a) ∨ (r' < 0 ∧ (e':ℝ)/r'=b)) ∧
      (e':ℝ)/r'∈S ∧ R^2 ≤ (r':ℝ)^2*U ∧
      |(r':ℝ)| < 4*R^2/U ∧ |e'*s-f*r'|=1 := by
    rcases heval with he | he
    · exact ⟨e,r,Or.inl ⟨hr,he⟩,heS,hrscale,
        by simpa only [abs_of_pos hrR] using hheight,hdet⟩
    · refine ⟨-e,-r,Or.inr ⟨neg_neg_of_pos hr,?_⟩,?_,?_,?_,?_⟩
      · simpa only [Int.cast_neg,neg_div_neg_eq] using he
      · simpa only [Int.cast_neg,neg_div_neg_eq] using heS
      · simpa only [Int.cast_neg,neg_sq] using hrscale
      · simpa only [Int.cast_neg,abs_neg,abs_of_pos hrR] using hheight
      · have heq : -e*s-f*(-r)= -(e*s-f*r) := by ring
        rw [heq,abs_neg,hdet]
  obtain ⟨e',r',horient,he'S,hr'scale,hr'height,hdet'⟩ := hsigned
  let d : ℤ := f*r'-e'*s
  have hdabs : |d|=1 := by simpa only [d,abs_sub_comm] using hdet'
  have hdne : d≠0 := by intro hd; norm_num [hd] at hdabs
  have hdsq : d^2=1 := by
    calc
      _ = |d|^2 := (sq_abs d).symm
      _ = 1 := by rw [hdabs]; norm_num
  have hdR : (d:ℝ)≠0 := by exact_mod_cast hdne
  have hdabsR : |(d:ℝ)|=1 := by exact_mod_cast hdabs
  have hneighbor : ((d*f:ℤ):ℝ)/(d*s:ℤ)=(f:ℝ)/s := by
    push_cast
    field_simp
  have hsheights : |((d*s:ℤ):ℝ)| < 4*R^2/U := by
    rw [Int.cast_mul,abs_mul,hdabsR,one_mul,abs_of_pos hsR]
    exact hsheight
  have hnum (u v : ℤ) (huS : (u:ℝ)/v∈S) (hvheight : |(v:ℝ)| < 4*R^2/U)
      (hv : v≠0) : |(u:ℝ)| ≤ (scale+1)*(4*R^2/U) := by
    have hvR : (v:ℝ)≠0 := by exact_mod_cast hv
    have heq : (u:ℝ)=((u:ℝ)/v)*v := (div_mul_cancel₀ _ hvR).symm
    rw [heq,abs_mul]
    exact mul_le_mul (hpoints _ huS) hvheight.le (abs_nonneg _) (by linarith only [hscale])
  have hr'ne : r'≠0 := horient.elim (fun h => h.1.ne') (fun h => h.1.ne)
  have hdsne : d*s≠0 := mul_ne_zero hdne hs.ne'
  have hdsS : ((d*f:ℤ):ℝ)/(d*s:ℤ)∈S := hneighbor ▸ hfS
  refine ⟨e',r',d*f,d*s,?_,horient,hdsne,he'S,hdsS,hr'scale,hr'height,hsheights,
    hnum e' r' he'S hr'height hr'ne,hnum (d*f) (d*s) hdsS hsheights hdsne⟩
  calc
    d*f*r'-e'*(d*s) = d^2 := by dsimp only [d]; ring
    _ = 1 := hdsq

example
    (S : Finset ℝ) {H : ℤ} {R U scale a b : ℝ}
    (hR : 0 < R) (hU : 0 < U) (hscale : 0 ≤ scale)
    (hhull : ∀ x∈S, ∀ y∈S, ∀ q : ℚ, (q.den:ℤ) ≤ H →
      (q:ℝ)∈Icc x y → (q:ℝ)∈S)
    (hpoints : ∀ z∈S, |z| ≤ scale+1)
    (hlabels : ∀ z∈S,
      (∃ q : ℚ, z=(q:ℝ) ∧ (q.den:ℤ) ≤ H) ∨
      (∃ m n u v : ℤ, z=(m:ℝ)/n ∧ IsCoprime m n ∧ 0 < n ∧
        0 < v ∧ v ≤ H ∧ (u:ℝ)/v∈S ∧ |m*v-u*n|=1))
    (hsep : ∀ x∈S, ∀ y∈S, x≠y → U/(4*R^2) < |x-y|)
    (ha : a∈S) (hb : b∈S) (hab : a < b)
    (hadj : ∀ z∈S, ¬(a < z ∧ z < b))
    (hends : ∃ m n p q : ℤ, a=(m:ℝ)/n ∧ b=(p:ℝ)/q ∧
      IsCoprime m n ∧ IsCoprime p q ∧ 0 < n ∧ 0 < q ∧
      R^2 ≤ U*((max n q:ℤ):ℝ)^2) :
    ∃ e r v s : ℤ, v*r-e*s=1 ∧
      ((0 < r ∧ (e:ℝ)/r=a) ∨ (r < 0 ∧ (e:ℝ)/r=b)) ∧
      s≠0 ∧ (e:ℝ)/r∈S ∧ (v:ℝ)/s∈S ∧ R^2 ≤ (r:ℝ)^2*U ∧
      |(r:ℝ)| < 4*R^2/U ∧ |(s:ℝ)| < 4*R^2/U ∧
      |(e:ℝ)| ≤ (scale+1)*(4*R^2/U) ∧
      |(v:ℝ)| ≤ (scale+1)*(4*R^2/U) := by
  exact actual_reference_gap_oriented_chart S hR hU hscale hhull hpoints hlabels hsep ha hb hab hadj hends

#print axioms actual_reference_gap_oriented_chart

/-- The source-derived bounded reference system supplies oriented determinant-one
charts and all label-height budgets for EVERY adjacent gap. No chart is assumed. -/
private theorem double_difference_constructed_reference_system_charts
    (F rshift sshift : ℝ → ℝ) (Y : Finset ℝ) {c J d w T M N R U : ℝ}
    (hc : 0 < c) (hJ : 0 < J) (hd : 0 < d)
    (hw : w ≤ 1/4) (hsmallShift : 2*J*w ≤ c/64)
    (hy : ∀ y∈Y, y∈Icc (1:ℝ) 2)
    (hshifts : ∀ y∈Y, 0 ≤ rshift y ∧ 0 ≤ sshift y ∧
      rshift y*sshift y=d*y ∧ rshift y+sshift y ≤ w)
    (hf : ∀ u, 0 < u → ContDiffAt ℝ ∞ F u)
    (hlower : ∀ u∈Icc (1/2:ℝ) 3, c ≤ iteratedDeriv 5 F u)
    (hbound : ∀ u∈Icc (1/2:ℝ) 3, ∀ n, 1 ≤ n → n ≤ 7 → |iteratedDeriv n F u| ≤ J)
    (hnegative : ∀ u∈Icc (1/2:ℝ) 3, iteratedDeriv 4 F u ≤ -c)
    (hT : 0 < T) (hM : 0 < M) (hN : 0 < N) (hR : 0 < R)
    (hU : 0 < U) (hUmax : U ≤ R^2) (hphase : T*N*R^2=M^3) :
    let Φ := fun y u => (F u-F (u+rshift y)-F (u+sshift y)+F (u+rshift y+sshift y))/d
    let f := fun y v => T*Φ y (v/M)
    let h := fun y w => iteratedDeriv 2 (f y) w/2
    let curvatureScale := J*T/M^2
    ∃ H : ℤ, 2 ≤ H ∧ (H:ℝ)<4*R^2/U ∧ ∃ S : Finset ℝ,
      (∀ q : ℚ, (q.den:ℤ) ≤ H → |(q:ℝ)| ≤ curvatureScale → (q:ℝ) ∈ S) ∧
      (∀ a ∈ S, ∀ b ∈ S, ∀ q : ℚ, (q.den:ℤ) ≤ H →
        (q:ℝ) ∈ Icc a b → (q:ℝ) ∈ S) ∧
      (∃ l ∈ S, ∃ u ∈ S, l ≤ -curvatureScale ∧ curvatureScale ≤ u) ∧
      (∀ z ∈ S, |z| ≤ curvatureScale+1) ∧
      (∀ z∈S, ∃ a b : ℤ, z=(a:ℝ)/b ∧ IsCoprime a b ∧ 0 < b ∧
        (b:ℝ)<4*R^2/U ∧ |(a:ℝ)| ≤ (curvatureScale+1)*(4*R^2/U)) ∧
      (∀ y∈Y, ∀ x ∈ Icc M (2*M), |h y x| ≤ curvatureScale) ∧
      (∀ z ∈ S,
        (∃ q : ℚ, z=(q:ℝ) ∧ (q.den:ℤ) ≤ H) ∨
        (∃ m n u v : ℤ, z=(m:ℝ)/n ∧ IsCoprime m n ∧ 0 < n ∧
          R^2 ≤ U*(n:ℝ)^2 ∧ 0 < v ∧ v ≤ H ∧ (u:ℝ)/v ∈ S ∧ |m*v-u*n|=1)) ∧
      (∀ x ∈ S, ∀ z ∈ S, x ≠ z → U/(4*R^2) < |x-z|) ∧
      (∀ y∈Y, ∀ x ∈ Icc M (2*M),
        ∃ q ∈ S, |h y x-q| ≤ 7*U/(4*R^2)) ∧
      (∀ y∈Y, ∀ q ∈ S,
        q ∈ Icc (h y M) (h y (2*M)) →
        ∃ x ∈ Icc M (2*M), h y x=q) ∧
      (∀ a ∈ S, ∀ b ∈ S, a < b →
        (∀ z ∈ S, ¬ (a < z ∧ z < b)) →
        U/(4*R^2) < b-a ∧ b-a ≤ 7*U/(2*R^2) ∧
        (∃ m n u v : ℤ, a=(m:ℝ)/n ∧ b=(u:ℝ)/v ∧
          IsCoprime m n ∧ IsCoprime u v ∧ 0 < n ∧ 0 < v ∧
          R^2 ≤ U*((max n v:ℤ):ℝ)^2) ∧
        (∀ y∈Y, ∀ x ∈ Icc M (2*M), ∀ z ∈ Icc M (2*M),
          h y x=a → h y z=b → |z-x| ≤ (14/c)*U*N)) ∧
      (∀ a∈S, ∀ b∈S, a < b → (∀ z∈S, ¬(a < z ∧ z < b)) →
        ∃ e r v s : ℤ, v*r-e*s=1 ∧
          ((0 < r ∧ (e:ℝ)/r=a) ∨ (r < 0 ∧ (e:ℝ)/r=b)) ∧
          s≠0 ∧ (e:ℝ)/r∈S ∧ (v:ℝ)/s∈S ∧ R^2 ≤ (r:ℝ)^2*U ∧
          |(r:ℝ)| < 4*R^2/U ∧ |(s:ℝ)| < 4*R^2/U ∧
          |(e:ℝ)| ≤ (curvatureScale+1)*(4*R^2/U) ∧
          |(v:ℝ)| ≤ (curvatureScale+1)*(4*R^2/U)) := by
  intro Φ f h curvatureScale
  obtain ⟨H,hH,hHeight,S,hseed,hhull,henclose,hpoints,hheights,hcurv,hlabels,hsep,hcover,hroots,hgaps⟩ :=
    double_difference_constructed_reference_system_bounded F rshift sshift Y hc hJ hd hw hsmallShift
      hy hshifts hf hlower hbound hnegative hT hM hN hR hU hUmax hphase
  refine ⟨H,hH,hHeight,S,hseed,hhull,henclose,hpoints,hheights,hcurv,hlabels,hsep,hcover,hroots,hgaps,?_⟩
  intro a ha b hb hab hadj
  apply actual_reference_gap_oriented_chart S hR hU
    (show 0 ≤ curvatureScale by dsimp only [curvatureScale]; positivity)
    hhull hpoints _ hsep ha hb hab hadj (hgaps a ha b hb hab hadj).2.2.1
  intro z hz
  rcases hlabels z hz with hsmall | ⟨m,n,u,v,hval,hcop,hn,_hlarge,hv,hvH,hparent,hdet⟩
  · exact Or.inl hsmall
  · exact Or.inr ⟨m,n,u,v,hval,hcop,hn,hv,hvH,hparent,hdet⟩

example
    (F rshift sshift : ℝ → ℝ) (Y : Finset ℝ) {c J d w T M N R U : ℝ}
    (hc : 0 < c) (hJ : 0 < J) (hd : 0 < d)
    (hw : w ≤ 1/4) (hsmallShift : 2*J*w ≤ c/64)
    (hy : ∀ y∈Y, y∈Icc (1:ℝ) 2)
    (hshifts : ∀ y∈Y, 0 ≤ rshift y ∧ 0 ≤ sshift y ∧
      rshift y*sshift y=d*y ∧ rshift y+sshift y ≤ w)
    (hf : ∀ u, 0 < u → ContDiffAt ℝ ∞ F u)
    (hlower : ∀ u∈Icc (1/2:ℝ) 3, c ≤ iteratedDeriv 5 F u)
    (hbound : ∀ u∈Icc (1/2:ℝ) 3, ∀ n, 1 ≤ n → n ≤ 7 → |iteratedDeriv n F u| ≤ J)
    (hnegative : ∀ u∈Icc (1/2:ℝ) 3, iteratedDeriv 4 F u ≤ -c)
    (hT : 0 < T) (hM : 0 < M) (hN : 0 < N) (hR : 0 < R)
    (hU : 0 < U) (hUmax : U ≤ R^2) (hphase : T*N*R^2=M^3) :
    let Φ := fun y u => (F u-F (u+rshift y)-F (u+sshift y)+F (u+rshift y+sshift y))/d
    let f := fun y v => T*Φ y (v/M)
    let h := fun y w => iteratedDeriv 2 (f y) w/2
    let curvatureScale := J*T/M^2
    ∃ H : ℤ, 2 ≤ H ∧ (H:ℝ)<4*R^2/U ∧ ∃ S : Finset ℝ,
      (∀ q : ℚ, (q.den:ℤ) ≤ H → |(q:ℝ)| ≤ curvatureScale → (q:ℝ) ∈ S) ∧
      (∀ a ∈ S, ∀ b ∈ S, ∀ q : ℚ, (q.den:ℤ) ≤ H →
        (q:ℝ) ∈ Icc a b → (q:ℝ) ∈ S) ∧
      (∃ l ∈ S, ∃ u ∈ S, l ≤ -curvatureScale ∧ curvatureScale ≤ u) ∧
      (∀ z ∈ S, |z| ≤ curvatureScale+1) ∧
      (∀ z∈S, ∃ a b : ℤ, z=(a:ℝ)/b ∧ IsCoprime a b ∧ 0 < b ∧
        (b:ℝ)<4*R^2/U ∧ |(a:ℝ)| ≤ (curvatureScale+1)*(4*R^2/U)) ∧
      (∀ y∈Y, ∀ x ∈ Icc M (2*M), |h y x| ≤ curvatureScale) ∧
      (∀ z ∈ S,
        (∃ q : ℚ, z=(q:ℝ) ∧ (q.den:ℤ) ≤ H) ∨
        (∃ m n u v : ℤ, z=(m:ℝ)/n ∧ IsCoprime m n ∧ 0 < n ∧
          R^2 ≤ U*(n:ℝ)^2 ∧ 0 < v ∧ v ≤ H ∧ (u:ℝ)/v ∈ S ∧ |m*v-u*n|=1)) ∧
      (∀ x ∈ S, ∀ z ∈ S, x ≠ z → U/(4*R^2) < |x-z|) ∧
      (∀ y∈Y, ∀ x ∈ Icc M (2*M),
        ∃ q ∈ S, |h y x-q| ≤ 7*U/(4*R^2)) ∧
      (∀ y∈Y, ∀ q ∈ S,
        q ∈ Icc (h y M) (h y (2*M)) →
        ∃ x ∈ Icc M (2*M), h y x=q) ∧
      (∀ a ∈ S, ∀ b ∈ S, a < b →
        (∀ z ∈ S, ¬ (a < z ∧ z < b)) →
        U/(4*R^2) < b-a ∧ b-a ≤ 7*U/(2*R^2) ∧
        (∃ m n u v : ℤ, a=(m:ℝ)/n ∧ b=(u:ℝ)/v ∧
          IsCoprime m n ∧ IsCoprime u v ∧ 0 < n ∧ 0 < v ∧
          R^2 ≤ U*((max n v:ℤ):ℝ)^2) ∧
        (∀ y∈Y, ∀ x ∈ Icc M (2*M), ∀ z ∈ Icc M (2*M),
          h y x=a → h y z=b → |z-x| ≤ (14/c)*U*N)) ∧
      (∀ a∈S, ∀ b∈S, a < b → (∀ z∈S, ¬(a < z ∧ z < b)) →
        ∃ e r v s : ℤ, v*r-e*s=1 ∧
          ((0 < r ∧ (e:ℝ)/r=a) ∨ (r < 0 ∧ (e:ℝ)/r=b)) ∧
          s≠0 ∧ (e:ℝ)/r∈S ∧ (v:ℝ)/s∈S ∧ R^2 ≤ (r:ℝ)^2*U ∧
          |(r:ℝ)| < 4*R^2/U ∧ |(s:ℝ)| < 4*R^2/U ∧
          |(e:ℝ)| ≤ (curvatureScale+1)*(4*R^2/U) ∧
          |(v:ℝ)| ≤ (curvatureScale+1)*(4*R^2/U)) := by
  exact double_difference_constructed_reference_system_charts F rshift sshift Y hc hJ hd hw hsmallShift
    hy hshifts hf hlower hbound hnegative hT hM hN hR hU hUmax hphase

#print axioms double_difference_constructed_reference_system_charts


/-- Unchanged existing private finite closed-bracket proof copied for scratch access;
promotion reuses the original declaration. -/
private theorem finite_reference_closed_bracket (S : Finset ℝ) {l u lo hi x : ℝ}
    (hl : l ∈ S) (hu : u ∈ S) (hlo : l ≤ lo) (hhi : hi ≤ u)
    (hwidth : lo < hi) (hx : x ∈ Icc lo hi) :
    ∃ a ∈ S, ∃ b ∈ S, a < b ∧ a ≤ x ∧ x ≤ b ∧
      (∀ z ∈ S, ¬ (a < z ∧ z < b)) ∧ a < hi ∧ lo < b := by
  classical
  by_cases htop : x < hi
  · let A := S.filter (fun z => z ≤ x)
    let B := S.filter (fun z => x < z)
    have hA : A.Nonempty := ⟨l,Finset.mem_filter.mpr ⟨hl,hlo.trans hx.1⟩⟩
    have hB : B.Nonempty := ⟨u,Finset.mem_filter.mpr ⟨hu,htop.trans_le hhi⟩⟩
    let a := A.max' hA
    let b := B.min' hB
    have ha := Finset.mem_filter.mp (Finset.max'_mem A hA)
    have hb := Finset.mem_filter.mp (Finset.min'_mem B hB)
    refine ⟨a,ha.1,b,hb.1,ha.2.trans_lt hb.2,ha.2,hb.2.le,?_,
      ha.2.trans_lt htop,hx.1.trans_lt hb.2⟩
    intro z hz hzab
    by_cases hzx : z ≤ x
    · have hzA : z ∈ A := Finset.mem_filter.mpr ⟨hz,hzx⟩
      exact (not_lt_of_ge (Finset.le_max' A z hzA)) hzab.1
    · have hzB : z ∈ B := Finset.mem_filter.mpr ⟨hz,lt_of_not_ge hzx⟩
      exact (not_lt_of_ge (Finset.min'_le B z hzB)) hzab.2
  · have hxe : x = hi := le_antisymm hx.2 (le_of_not_gt htop)
    let A := S.filter (fun z => z < x)
    let B := S.filter (fun z => x ≤ z)
    have hA : A.Nonempty := ⟨l,Finset.mem_filter.mpr ⟨hl,by linarith⟩⟩
    have hB : B.Nonempty := ⟨u,Finset.mem_filter.mpr ⟨hu,by linarith⟩⟩
    let a := A.max' hA
    let b := B.min' hB
    have ha := Finset.mem_filter.mp (Finset.max'_mem A hA)
    have hb := Finset.mem_filter.mp (Finset.min'_mem B hB)
    refine ⟨a,ha.1,b,hb.1,ha.2.trans_le hb.2,ha.2.le,hb.2,?_,
      by simpa only [hxe] using ha.2,by linarith only [hwidth,hxe,hb.2]⟩
    intro z hz hzab
    by_cases hzx : z < x
    · have hzA : z ∈ A := Finset.mem_filter.mpr ⟨hz,hzx⟩
      exact (not_lt_of_ge (Finset.le_max' A z hzA)) hzab.1
    · have hzB : z ∈ B := Finset.mem_filter.mpr ⟨hz,le_of_not_gt hzx⟩
      exact (not_lt_of_ge (Finset.min'_le B z hzB)) hzab.2

example
    (S : Finset ℝ) {l u lo hi x : ℝ}
    (hl : l ∈ S) (hu : u ∈ S) (hlo : l ≤ lo) (hhi : hi ≤ u)
    (hwidth : lo < hi) (hx : x ∈ Icc lo hi) :
    ∃ a ∈ S, ∃ b ∈ S, a < b ∧ a ≤ x ∧ x ≤ b ∧
      (∀ z ∈ S, ¬ (a < z ∧ z < b)) ∧ a < hi ∧ lo < b := by
  exact finite_reference_closed_bracket S hl hu hlo hhi hwidth hx

#print axioms finite_reference_closed_bracket

/-- Source-derived bounded charts cover every actual double-phase curvature value.
The reference radius is arbitrary: the source amplitude is NOT identified with
any normalized model amplitude or its block scale. -/
private theorem double_difference_constructed_reference_gap_factory
    (F rshift sshift : ℝ → ℝ) (Y : Finset ℝ) {c J d w T M R U : ℝ}
    (hc : 0 < c) (hJ : 0 < J) (hd : 0 < d)
    (hw : w ≤ 1/4) (hsmallShift : 2*J*w ≤ c/64)
    (hy : ∀ y∈Y, y∈Icc (1:ℝ) 2)
    (hshifts : ∀ y∈Y, 0 ≤ rshift y ∧ 0 ≤ sshift y ∧
      rshift y*sshift y=d*y ∧ rshift y+sshift y ≤ w)
    (hf : ∀ u, 0 < u → ContDiffAt ℝ ∞ F u)
    (hlower : ∀ u∈Icc (1/2:ℝ) 3, c ≤ iteratedDeriv 5 F u)
    (hbound : ∀ u∈Icc (1/2:ℝ) 3, ∀ n, 1 ≤ n → n ≤ 7 → |iteratedDeriv n F u| ≤ J)
    (hnegative : ∀ u∈Icc (1/2:ℝ) 3, iteratedDeriv 4 F u ≤ -c)
    (hT : 0 < T) (hM : 0 < M) (hR : 0 < R)
    (hU : 0 < U) (hUmax : U ≤ R^2) :
    let Φ := fun y u => (F u-F (u+rshift y)-F (u+sshift y)+F (u+rshift y+sshift y))/d
    let f := fun y v => T*Φ y (v/M)
    let h := fun y z => iteratedDeriv 2 (f y) z/2
    let curvatureScale := J*T/M^2
    ∃ (Refs : Finset ℝ) (Gaps : Finset (ℝ × ℝ)) (e r v s : ℝ × ℝ → ℤ),
      (∀ a∈Refs, ∀ b∈Refs, a≠b → U/(4*R^2) < |a-b|) ∧
      (∀ ab∈Gaps, ab.1∈Refs ∧ ab.2∈Refs ∧ ab.1 < ab.2 ∧
        ∀ z∈Refs, ¬(ab.1 < z ∧ z < ab.2)) ∧
      (∀ ab∈Gaps, v ab*r ab-e ab*s ab=1) ∧
      (∀ ab∈Gaps, (((0:ℝ) < r ab ∧ (e ab:ℝ)/r ab=ab.1) ∨
        ((r ab:ℝ) < 0 ∧ (e ab:ℝ)/r ab=ab.2))) ∧
      (∀ ab∈Gaps, s ab≠0) ∧
      (∀ ab∈Gaps, (e ab:ℝ)/r ab∈Refs) ∧
      (∀ ab∈Gaps, (v ab:ℝ)/s ab∈Refs) ∧
      (∀ ab∈Gaps, R^2 ≤ (r ab:ℝ)^2*U) ∧
      (∀ ab∈Gaps, ab.2-ab.1 ≤ 7*U/(2*R^2)) ∧
      (∀ ab∈Gaps, |(r ab:ℝ)| ≤ 4*R^2/U) ∧
      (∀ ab∈Gaps, |(s ab:ℝ)| ≤ 4*R^2/U) ∧
      (∀ ab∈Gaps, |(e ab:ℝ)| ≤ (curvatureScale+1)*(4*R^2/U)) ∧
      (∀ ab∈Gaps, |(v ab:ℝ)| ≤ (curvatureScale+1)*(4*R^2/U)) ∧
      ∀ y∈Y, ∀ z∈Icc M (2*M), ∃ ab∈Gaps, h y z∈Icc ab.1 ab.2 := by
  classical
  intro Φ f h curvatureScale
  let Nref := M^3/(T*R^2)
  have hNref : 0 < Nref := by dsimp only [Nref]; positivity
  have hphase : T*Nref*R^2=M^3 := by dsimp only [Nref]; field_simp
  obtain ⟨H,_hH,_hHeight,Refs,_hseed,_hhull,henclose,_hpoints,_hheights,hcurv,
      _hlabels,hsep,_hcover,_hroots,hgaps,hcharts⟩ :=
    double_difference_constructed_reference_system_charts F rshift sshift Y hc hJ hd hw hsmallShift
      hy hshifts hf hlower hbound hnegative hT hM hNref hR hU hUmax hphase
  let Gaps := (Refs ×ˢ Refs).filter (fun ab => ab.1 < ab.2 ∧ ∀ z∈Refs, ¬(ab.1 < z ∧ z < ab.2))
  have hgap ab (hab : ab∈Gaps) : ab.1∈Refs ∧ ab.2∈Refs ∧ ab.1 < ab.2 ∧
      ∀ z∈Refs, ¬(ab.1 < z ∧ z < ab.2) := by
    obtain ⟨hp,hl,hadj⟩ := Finset.mem_filter.mp hab
    obtain ⟨ha,hb⟩ := Finset.mem_product.mp hp
    exact ⟨ha,hb,hl,hadj⟩
  have hex (ab : ℝ × ℝ) : ∃ e r v s : ℤ, ab∈Gaps →
      v*r-e*s=1 ∧ ((0 < r ∧ (e:ℝ)/r=ab.1) ∨ (r < 0 ∧ (e:ℝ)/r=ab.2)) ∧
      s≠0 ∧ (e:ℝ)/r∈Refs ∧ (v:ℝ)/s∈Refs ∧ R^2 ≤ (r:ℝ)^2*U ∧
      |(r:ℝ)| < 4*R^2/U ∧ |(s:ℝ)| < 4*R^2/U ∧
      |(e:ℝ)| ≤ (curvatureScale+1)*(4*R^2/U) ∧
      |(v:ℝ)| ≤ (curvatureScale+1)*(4*R^2/U) := by
    by_cases hab : ab∈Gaps
    · have hg := hgap ab hab
      obtain ⟨e,r,v,s,hout⟩ := hcharts ab.1 hg.1 ab.2 hg.2.1 hg.2.2.1 hg.2.2.2
      exact ⟨e,r,v,s,fun _ => hout⟩
    · exact ⟨0,0,0,0,fun hh => (hab hh).elim⟩
  choose e r v s hdata using hex
  refine ⟨Refs,Gaps,e,r,v,s,hsep,hgap,(fun ab hab => (hdata ab hab).1),?_,
    (fun ab hab => (hdata ab hab).2.2.1),
    (fun ab hab => (hdata ab hab).2.2.2.1),
    (fun ab hab => (hdata ab hab).2.2.2.2.1),
    (fun ab hab => (hdata ab hab).2.2.2.2.2.1),?_,
    (fun ab hab => (hdata ab hab).2.2.2.2.2.2.1.le),
    (fun ab hab => (hdata ab hab).2.2.2.2.2.2.2.1.le),
    (fun ab hab => (hdata ab hab).2.2.2.2.2.2.2.2.1),
    (fun ab hab => (hdata ab hab).2.2.2.2.2.2.2.2.2),?_⟩
  · intro ab hab
    rcases (hdata ab hab).2.1 with hleft | hright
    · exact Or.inl ⟨by exact_mod_cast hleft.1,hleft.2⟩
    · exact Or.inr ⟨by exact_mod_cast hright.1,hright.2⟩
  · intro ab hab
    have hg := hgap ab hab
    exact (hgaps ab.1 hg.1 ab.2 hg.2.1 hg.2.2.1 hg.2.2.2).2.1
  · intro y hyY z hz
    obtain ⟨l,hl,u,hu,hlo,hhi⟩ := henclose
    have hscale : 0 < curvatureScale := by dsimp only [curvatureScale]; positivity
    obtain ⟨a,ha,b,hb,hab,hax,hxb,hadj,_hal,_hub⟩ :=
      finite_reference_closed_bracket Refs hl hu hlo hhi
        (show -curvatureScale < curvatureScale by linarith only [hscale])
        (abs_le.mp (hcurv y hyY z hz))
    exact ⟨(a,b),Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨ha,hb⟩,hab,hadj⟩,hax,hxb⟩

example
    (F rshift sshift : ℝ → ℝ) (Y : Finset ℝ) {c J d w T M R U : ℝ}
    (hc : 0 < c) (hJ : 0 < J) (hd : 0 < d)
    (hw : w ≤ 1/4) (hsmallShift : 2*J*w ≤ c/64)
    (hy : ∀ y∈Y, y∈Icc (1:ℝ) 2)
    (hshifts : ∀ y∈Y, 0 ≤ rshift y ∧ 0 ≤ sshift y ∧
      rshift y*sshift y=d*y ∧ rshift y+sshift y ≤ w)
    (hf : ∀ u, 0 < u → ContDiffAt ℝ ∞ F u)
    (hlower : ∀ u∈Icc (1/2:ℝ) 3, c ≤ iteratedDeriv 5 F u)
    (hbound : ∀ u∈Icc (1/2:ℝ) 3, ∀ n, 1 ≤ n → n ≤ 7 → |iteratedDeriv n F u| ≤ J)
    (hnegative : ∀ u∈Icc (1/2:ℝ) 3, iteratedDeriv 4 F u ≤ -c)
    (hT : 0 < T) (hM : 0 < M) (hR : 0 < R)
    (hU : 0 < U) (hUmax : U ≤ R^2) :
    let Φ := fun y u => (F u-F (u+rshift y)-F (u+sshift y)+F (u+rshift y+sshift y))/d
    let f := fun y v => T*Φ y (v/M)
    let h := fun y z => iteratedDeriv 2 (f y) z/2
    let curvatureScale := J*T/M^2
    ∃ (Refs : Finset ℝ) (Gaps : Finset (ℝ × ℝ)) (e r v s : ℝ × ℝ → ℤ),
      (∀ a∈Refs, ∀ b∈Refs, a≠b → U/(4*R^2) < |a-b|) ∧
      (∀ ab∈Gaps, ab.1∈Refs ∧ ab.2∈Refs ∧ ab.1 < ab.2 ∧
        ∀ z∈Refs, ¬(ab.1 < z ∧ z < ab.2)) ∧
      (∀ ab∈Gaps, v ab*r ab-e ab*s ab=1) ∧
      (∀ ab∈Gaps, (((0:ℝ) < r ab ∧ (e ab:ℝ)/r ab=ab.1) ∨
        ((r ab:ℝ) < 0 ∧ (e ab:ℝ)/r ab=ab.2))) ∧
      (∀ ab∈Gaps, s ab≠0) ∧
      (∀ ab∈Gaps, (e ab:ℝ)/r ab∈Refs) ∧
      (∀ ab∈Gaps, (v ab:ℝ)/s ab∈Refs) ∧
      (∀ ab∈Gaps, R^2 ≤ (r ab:ℝ)^2*U) ∧
      (∀ ab∈Gaps, ab.2-ab.1 ≤ 7*U/(2*R^2)) ∧
      (∀ ab∈Gaps, |(r ab:ℝ)| ≤ 4*R^2/U) ∧
      (∀ ab∈Gaps, |(s ab:ℝ)| ≤ 4*R^2/U) ∧
      (∀ ab∈Gaps, |(e ab:ℝ)| ≤ (curvatureScale+1)*(4*R^2/U)) ∧
      (∀ ab∈Gaps, |(v ab:ℝ)| ≤ (curvatureScale+1)*(4*R^2/U)) ∧
      ∀ y∈Y, ∀ z∈Icc M (2*M), ∃ ab∈Gaps, h y z∈Icc ab.1 ab.2 := by
  exact double_difference_constructed_reference_gap_factory F rshift sshift Y hc hJ hd hw hsmallShift
    hy hshifts hf hlower hbound hnegative hT hM hR hU hUmax

#print axioms double_difference_constructed_reference_gap_factory


/-- Consume the actual double-phase weighted sieve with INTERNALLY constructed
reference gaps, oriented charts, label heights and global integer windows.
The two amplitudes remain distinct; only the explicit upstream source/model
and scalar regime conditions remain. No reference or count certificate is assumed. -/
private theorem eventually_double_difference_constructed_reference_weighted_sieve
    {csrc Usrc E σ εloss : ℝ}
    (hcsrc : 0 < csrc) (hUsrc : 0 < Usrc)
    (hE : 0 < E) (hσ : 0 < σ) (hεloss : 0 < εloss) :
    let κ := modelPhaseThirdLower σ
    let L := max (32*Usrc^2/csrc^2)
      (64*(modelPhaseJetCoefficient σ 3+1)*Usrc*E/κ^2)
    let θ := 1/(8*(L+3))
    ∃ C Dtype : ℝ, 0 < C ∧ 0 < Dtype ∧
    ∀ᶠ T : ℝ in Filter.atTop, ∀ (S : Finset (ℝ × ℤ)) (Fsrc rshift sshift : ℝ → ℝ)
    (z : (ℝ × ℤ) → ℝ) (rat : (ℝ × ℤ) → ℚ) (v : (ℝ × ℤ) → ℤ) (Nlen : (ℝ × ℤ) → ℕ)
    (Q K₀ N : ℕ) [NeZero K₀] (R Jsep : ℝ) (Z : ℝ → ℤ)
    {d Wmax Tsrc M δ Bcut Bselect : ℝ}
    (Uref : ℕ) (anchor : (ℝ × ℤ) → ℚ),
    let lambda := csrc*Tsrc/(2*M^2)
    let Uband := Usrc*Tsrc/M^2
    let Vscale := max 1 (Uband*(N:ℝ)/(Q:ℝ))
    let Buffer := (56*(Uref:ℝ)/κ)*(N:ℝ)+(N:ℝ)/(σ*(σ+1)+3)+2
    (0 < d) → (0 ≤ Wmax) → (Wmax ≤ 1/4) → (2*Usrc*Wmax ≤ csrc/64) →
    (0 < Tsrc) →
    (0 < T) →
    (0 < M) →
    (δ ≤ min (modelPhaseThirdLower σ) 1) →
    (Tsrc ≤ E*T) →
    (0 < Q) → (Uband ≤ 1) →
    (∀ i∈S, i.1∈Icc (1:ℝ) 2) →
    (∀ i∈S, z i∈Ioo (M+Buffer) (2*M-Buffer)) →
    (∀ w, 0 < w → ContDiffAt ℝ ∞ Fsrc w) →
    (∀ w∈Icc (1/2:ℝ) 3, csrc ≤ iteratedDeriv 5 Fsrc w) →
    (∀ w∈Icc (1/2:ℝ) 3, ∀ n, 1 ≤ n → n ≤ 7 → |iteratedDeriv n Fsrc w| ≤ Usrc) →
    (∀ w∈Icc (1/2:ℝ) 3,
      csrc ≤ |(iteratedDeriv 5 Fsrc w)^2-iteratedDeriv 4 Fsrc w*iteratedDeriv 6 Fsrc w|) →
    (∀ i∈S, (rat i).den ≤ Q ∧ Q ≤ 2*(rat i).den) →
    (∀ i∈S, ((rat i).den:ℤ) ∣ (rat i).num*v i-1) →
    (∀ w∈Icc (1/2:ℝ) 3, iteratedDeriv 4 Fsrc w ≤ -csrc) →
    (2 ≤ M) →
    (0 < N) →
    (0 < Jsep) → (Jsep ≤ M) → ((N:ℝ) ≤ M) → (Wmax*Jsep ≤ 1) →
    ((Q:ℝ)*(N:ℝ) ≤ (K₀:ℝ)*R^2) →
    (∀ i∈S, N ≤ Nlen i ∧ Nlen i ≤ 3*N ∧
      round (z i)+(Nlen i:ℤ)=Z i.1+(N:ℤ)*i.2+2*(N:ℤ)) →
    (∀ i∈S, ∀ j∈S, i.1≠j.1 → 1 ≤ Jsep*|i.1-j.1|) →
    (∀ y∈S.image Prod.fst,
      0 ≤ rshift y ∧ 0 ≤ sshift y ∧ rshift y*sshift y=d*y ∧ rshift y+sshift y ≤ Wmax) →
    let Φ := fun y u =>
      (Fsrc u-Fsrc (u+rshift y)-Fsrc (u+sshift y)+Fsrc (u+rshift y+sshift y))/d
    let Fmodel := fun (i : ℝ × ℤ) u => (Tsrc/T)*Φ i.1 u
    (∀ i∈S, Expdb.IsApproximateModelPhaseFunction (Fmodel i) σ 4 δ) →
    let f := fun p w => Tsrc*Φ p (w/M)
    (∀ i∈S, iteratedDeriv 2 (f (i.1)) (z i)/2=(rat i:ℝ)) →
    (∀ i∈S, 1 ≤ Nlen i ∧ (rat i).den ≤ Nlen i ∧
      1 ≤ (iteratedDeriv 3 (f (i.1)) (round (z i))/6)*((rat i).den:ℝ)^2*Nlen i) →
    (∀ i∈S, 7*((iteratedDeriv 3 (f (i.1)) (round (z i))/6)*
      ((rat i).den:ℝ)*(Nlen i:ℝ)^2) ≤ K₀) →

    (1 ≤ R) → (R ≤ M) → (T*(N:ℝ)*R^2=M^3) →
    (0 < Bcut) →
    (1 ≤ Uref) →
    (2+168/κ ≤ Bselect) → (7*Bcut ≤ κ*Bselect) →
    (Bselect^2*(Uref:ℝ)^3*R^2 ≤ (N:ℝ)^2) →
    (R ≤ (Q:ℝ)) →
    ((Uref:ℝ) ≤ ((N:ℝ)/(Q:ℝ))^((2:ℝ)/3)/Bselect) →
    ((N:ℝ)^10 ≤ M^3*R^7) →
    (Q:ℝ) ≤ (N:ℝ) →
    ((N:ℝ)^2 ≤ M ∨ (1 ≤ M ∧ (N:ℝ) ≤ T ∧ R^2 ≤ T)) → (Uref:ℝ) ≤ R^2 →
    let Cphys := σ*(σ+1)+1
    let c := κ/6
    let J := Cphys/6
    let B := max 1 (max (2*Real.sqrt J) (8*J*Real.sqrt J/(3*c)))
    B*R^2/(N:ℝ)^2 ≤ 1/2 →
    (N:ℝ) ≤ R^2 → R ≤ (N:ℝ) → (N:ℝ)^3 ≤ M*R^2 →
    2*R^2 ≤ (Q:ℝ)*(N:ℝ) →
    2 ≤ (N:ℝ) →
    let ε := κ/(16*(Cphys+2)*R^2)
    (∀ i∈S, |(anchor i:ℝ)-(rat i:ℝ)| ≤ ε) →
    (∀ i∈S, 256*((anchor i).den:ℝ) ≤ (Q:ℝ)/3) →
    (∀ i∈S, 256 ≤ (2*ε)*((Q:ℝ)/3)*(anchor i).den) →
    let narrow := fun (i : ℝ × ℤ) =>
      (⌊((rat i).den:ℝ)/(θ*((Q:ℝ)/2))⌋,
       ⌊((rat i).num:ℝ)/(θ*(lambda*(Q:ℝ)/2))⌋)
    let qell := fun (i : ℝ × ℤ) => ((rat i).den:ℝ)*deriv (f (i.1)) (round (z i))
    let V := S ×ˢ (Finset.univ : Finset (Fin 2))
    let offset := fun ip : (ℝ × ℤ) × Fin 2 => ⌊qell ip.1⌋+(ip.2:ℕ)-round (qell ip.1)
    let color := fun ip : (ℝ × ℤ) × Fin 2 => (narrow ip.1,offset ip)
    let NarrowCap := (4/θ+3)*(8*Usrc/(csrc*θ)+3)
    let Cap := 3*NarrowCap

    let q := fun (i : ℝ × ℤ) => (rat i).den
    let μ := fun (i : ℝ × ℤ) => iteratedDeriv 3 (f (i.1)) (round (z i))/6
    let b := fun ip : (ℝ × ℤ) × Fin 2 => (⌊qell ip.1⌋+(ip.2:ℕ) : ℤ)
    let tau := fun ip : (ℝ × ℤ) × Fin 2 => ((b ip:ℝ)-qell ip.1)/2
    let dual := fun (i : ℝ × ℤ) => -2*μ i*(Real.sqrt (2/(3*μ i*(q i:ℝ))))^3
    let x := fun ip : (ℝ × ℤ) × Fin 2 =>
      (![-(v ip.1:ℝ)*b ip/q ip.1,-(v ip.1:ℝ)/q ip.1,
        dual ip.1,3*dual ip.1*tau ip/2] : Fin 4 → ℝ)
    let Fiber := fun key => V.filter (fun ip => color ip=key)
    let μ₀ := csrc*Tsrc/(12*M^3)
    let U₀ := Usrc*Tsrc/(2*M^3)
    let Δtype := (16*U₀/μ₀)*Real.sqrt (U₀*(Q:ℝ)^3)*Real.sqrt K₀/(6*(K₀:ℝ)^2)
    let C₂ := modelPhaseJetCoefficient σ 2+δ
    let C₃ := modelPhaseJetCoefficient σ 3+δ
    let Ct := C₂/2+5*C₃/12
    let Cc := C₂/κ+C₃/(2*κ)
    let Δ := (37*B/2+16*B*Cc+2*Ct+2*Cc)*(Q:ℝ)/(N:ℝ)
    let Ccurv := (4/κ)*(B+2*quarticReciprocalConstant σ δ)
    let D := Δ+quarticNonlinearResidualConstant σ δ*(2*(Q:ℝ))/(N:ℝ)
    let Kres := 4*(37*B/2+16*B*Cc+2*Ct+2*Cc+
      2*quarticNonlinearResidualConstant σ δ)/κ
    let Esize := κ/(16*(Cphys+2))
    let Dbase := 37*B/2+16*B*Cc+2*Ct+2*Cc+2*quarticNonlinearResidualConstant σ δ
    let Tbase := (2/κ)*(B+2*quarticReciprocalConstant σ δ)
    2*3840*128^2*105*(Dbase+64*Tbase*Esize^2) ≤ Bselect*Esize →
    D ≤ 1/2 → Δ < 1/2 → 61*Ccurv*Cphys ≤ Bcut →
    let Lunit := 2*κ/Cphys
    let Gamma := Cphys/κ
    let Cthird := Gamma*(32*Kres+9*quarticReciprocalConstant σ δ)
    let Cpack := 64*Cphys*(Gamma^2*Cthird+Gamma*(modelPhaseJetCoefficient σ 3+δ)/κ)/κ
    let Cfirst := 128*Cphys*(Gamma^2*Cthird+Gamma*(modelPhaseJetCoefficient σ 3+δ)/κ)/κ^2
    let Cgap := 64*Cphys*(Gamma^2*B+Gamma*(modelPhaseJetCoefficient σ 3+δ)/κ)/κ
    let Cmain := 4*(2*Cfirst/Lunit^3)^((3:ℝ)⁻¹)+2
    let Ctail := 4*Cpack/Lunit^2+Cgap
    let Klarge := 60*588*(Uband/lambda)^2*Uband^2*(R^8/(N:ℝ)^4)*
      (Cmain*((Q:ℝ)/(Uband*(N:ℝ)))^((2:ℝ)/3)+Ctail/(Uref:ℝ))
    let Y := S.image Prod.fst
    let Values := fun k : ZMod K₀ =>
      ∑ ip∈V, ‖∑ j : ZMod K₀, ZMod.stdAddChar (-(j*k))*
        GafniTao.fordAdditiveCharacter (∑ d,x ip d*
          (![(j.val+1:ℝ),(j.val+1:ℝ)^2,(j.val+1:ℝ)^((3:ℝ)/2),
            Real.sqrt (j.val+1:ℝ)] : Fin 4 → ℝ) d)‖
    let Wphys := (144*Usrc/(csrc*κ))*(R^2/(Q:ℝ))
    let WeightedValues := fun k : ZMod K₀ =>
      ∑ ip∈V, (Real.sqrt (2*(q ip.1:ℝ))/((q ip.1:ℝ)*Real.sqrt (μ ip.1*(Nlen ip.1:ℝ))))*
        ‖∑ j : ZMod K₀, ZMod.stdAddChar (-(j*k))*
          GafniTao.fordAdditiveCharacter (∑ d,x ip d*
            (![(j.val+1:ℝ),(j.val+1:ℝ)^2,(j.val+1:ℝ)^((3:ℝ)/2),
              Real.sqrt (j.val+1:ℝ)] : Fin 4 → ℝ) d)‖
    let Mass := Vscale*Dtype*(2+θ*(Uband+1/lambda))*(Y.card:ℝ)*(M/(N:ℝ))*(1+Δtype*Jsep)+
      (Y.card:ℝ)^2*Klarge*T^εloss
    ((V.image color).card:ℝ) ≤ Cap ∧
      (∀ k, (Values k)^12 ≤ C*(K₀:ℝ)^((12:ℝ)+εloss)*Cap^11*
        ∑ key∈V.image color, ((Fiber key).card:ℝ)^10*Mass) ∧
      (V.card:ℝ) ≤ 10*(Y.card:ℝ)*(M/(N:ℝ)) ∧
      (∀ k, (Values k)^12 ≤ C*(K₀:ℝ)^((12:ℝ)+εloss)*Cap^11*
        (10*(Y.card:ℝ)*(M/(N:ℝ)))^10*Mass) ∧
      ∀ k, ((WeightedValues k)^12 ≤ Wphys^6*
        (C*(K₀:ℝ)^((12:ℝ)+εloss)*Cap^11*(V.card:ℝ)^10*Mass)) ∧
        (WeightedValues k)^12 ≤ Wphys^6*
          (C*(K₀:ℝ)^((12:ℝ)+εloss)*Cap^11*(10*(Y.card:ℝ)*(M/(N:ℝ)))^10*Mass) := by
  classical
  intro κ L θ
  obtain ⟨C,Dtype,hC,hDtype,hsource⟩ :=
    eventually_double_difference_actual_family_physical_sieve hcsrc hUsrc hE hσ hεloss
  let Jref := 2*σ*Usrc*E/3
  have hJref : 0 ≤ Jref := by dsimp only [Jref]; positivity
  refine ⟨C,Dtype,hC,hDtype,?_⟩
  filter_upwards [hsource hJref] with T hfamily
  intro S Fsrc rshift sshift z rat v Nlen Q K₀ N instK R Jsep Z
    d Wmax Tsrc M δ Bcut Bselect Uref anchor
    lambda Uband Vscale Buffer hd hw hwcap hsmallShift hTsrc hT hM hδ hsourceScale hQ hUbandCap
    hy hz hreg hlower hjets htests hden hinv hnegative hMtwo hN
    hJsep hJM hNM hwJ hmesh hgeometry hseparation hshifts Φ Fmodel hmodel f hlevel hminor hcomplete
    hR hRM hscale hBcut hUref hBselectSize hcutMargin hselectedWrap hRQ
    hselectedUpper hscaleTen hQN hNsqM hUR
    Cphys c J B hsmall hNR hRN hNcube hminscale hNtwo ε hanchor hcut hcount
    narrow qell V offset color NarrowCap Cap q μ b tau dual x Fiber μ₀ U₀ Δtype
    C₂ C₃ Ct Cc Δ Ccurv D Kres Esize Dbase Tbase hsize hD hΔ hBsize
    Lunit Gamma Cthird Cpack Cfirst Cgap Cmain Ctail Klarge Y Values Wphys WeightedValues Mass
  have hκ : 0 < κ := modelPhaseThirdLower_pos hσ
  have hNp : (0:ℝ) < N := Nat.cast_pos.mpr hN
  have hRp : 0 < R := zero_lt_one.trans_le hR
  have hUp : (0:ℝ) < Uref := by exact_mod_cast (show 0 < Uref by omega)
  have hdenom : 0 < σ*(σ+1)+3 := by positivity
  have hBuffer : 0 ≤ Buffer := by dsimp only [Buffer]; positivity
  have hzFull i (hi : i∈S) : z i∈Icc M (2*M) := by
    have hh := hz i hi
    constructor <;> linarith only [hh.1,hh.2,hBuffer]
  have hY y (hyY : y∈Y) : y∈Icc (1:ℝ) 2 := by
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hyY
    exact hy i hi
  obtain ⟨Refs,Gaps,e,r,vRef,s,hsep0,hgap,hchart,horientation,hs,hrefSet,hparentSet,
      hreferenceDen,hgapWidth,hrHeight,hsHeight,heHeight0,hvHeight0,hcover⟩ :=
    double_difference_constructed_reference_gap_factory Fsrc rshift sshift Y
      hcsrc hUsrc hd hwcap hsmallShift hY hshifts hreg hlower hjets hnegative
      hTsrc hM hRp hUp hUR
  have hex (i : ℝ × ℤ) : ∃ ab : ℝ × ℝ, i∈S → ab∈Gaps ∧ (rat i:ℝ)∈Icc ab.1 ab.2 := by
    by_cases hi : i∈S
    · obtain ⟨ab,hab,hval⟩ := hcover i.1 (Finset.mem_image_of_mem Prod.fst hi) (z i) (hzFull i hi)
      change iteratedDeriv 2 (f i.1) (z i)/2∈Icc ab.1 ab.2 at hval
      rw [hlevel i hi] at hval
      exact ⟨ab,fun _ => ⟨hab,hval⟩⟩
    · exact ⟨(0,0),fun hh => (hi hh).elim⟩
  choose gap hgapData using hex
  have hsep a (ha : a∈Refs) b (hb : b∈Refs) (hab : a≠b) :
      ((Uref:ℝ)/R^2)/4 < |a-b| := by
    convert hsep0 a ha b hb hab using 1
    ring
  have hcurvScale : Usrc*Tsrc/M^2 ≤ 3*Jref*T/(2*σ*M^2) := by
    calc
      _ ≤ Usrc*(E*T)/M^2 := div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hsourceScale hUsrc.le) (sq_nonneg M)
      _ = _ := by dsimp only [Jref]; field_simp
  have hheight : (Usrc*Tsrc/M^2+1)*(4*R^2/(Uref:ℝ)) ≤
      (3*Jref*T/(2*σ*M^2)+1)*(4*R^2/(Uref:ℝ)) :=
    mul_le_mul_of_nonneg_right (add_le_add hcurvScale le_rfl) (by positivity)
  have heHeight ab (hab : ab∈Gaps) :
      |(e ab:ℝ)| ≤ (3*Jref*T/(2*σ*M^2)+1)*(4*R^2/(Uref:ℝ)) :=
    (heHeight0 ab hab).trans hheight
  have hvHeight ab (hab : ab∈Gaps) :
      |(vRef ab:ℝ)| ≤ (3*Jref*T/(2*σ*M^2)+1)*(4*R^2/(Uref:ℝ)) :=
    (hvHeight0 ab hab).trans hheight
  let A := fun _ : ℝ => ⌈M⌉
  let W := fun _ : ℝ => 2*M-(⌈M⌉:ℝ)
  let Dpad := (56*(Uref:ℝ)/κ)*(N:ℝ)
  let Hphys := (N:ℝ)/(σ*(σ+1)+3)
  have hDpad : 0 ≤ Dpad := by dsimp only [Dpad]; positivity
  have hHphys : 0 ≤ Hphys := by dsimp only [Hphys]; positivity
  have hHeq : (N:ℝ)/(Cphys+2)=Hphys := by dsimp only [Cphys,Hphys]; ring
  have hBufferEq : Buffer=Dpad+Hphys+2 := rfl
  have hwindow i (hi : i∈S) t (ht : |t| ≤ Dpad+Hphys) :
      z i-(A i.1:ℝ)+t∈Ioo (1/2:ℝ) (W i.1-1/2) := by
    have hzz := hz i hi
    rw [hBufferEq] at hzz
    have hceil := Int.ceil_lt_add_one M
    have htb := abs_le.mp ht
    change (1/2:ℝ) < z i-(⌈M⌉:ℝ)+t ∧ z i-(⌈M⌉:ℝ)+t < 2*M-(⌈M⌉:ℝ)-1/2
    constructor <;> linarith only [hzz.1,hzz.2,hceil,htb.1,htb.2]
  have hx i (hi : i∈S) : z i-(A i.1:ℝ)∈Ioo (1/2:ℝ) (W i.1-1/2) := by
    simpa only [add_zero] using hwindow i hi 0 (by rw [abs_zero]; positivity)
  have hwideL i (hi : i∈S) : z i-(A i.1:ℝ)-Dpad∈Ioo (1/2:ℝ) (W i.1-1/2) := by
    simpa only [sub_eq_add_neg] using hwindow i hi (-Dpad)
      (by rw [abs_neg,abs_of_nonneg hDpad]; linarith only [hHphys])
  have hwideU i (hi : i∈S) : z i-(A i.1:ℝ)+Dpad∈Ioo (1/2:ℝ) (W i.1-1/2) :=
    hwindow i hi Dpad (by rw [abs_of_nonneg hDpad]; linarith only [hHphys])
  have hLeft i (hi : i∈S) : z i-(A i.1:ℝ)-(N:ℝ)/(Cphys+2)∈Ioo (1/2:ℝ) (W i.1-1/2) := by
    rw [hHeq]
    simpa only [sub_eq_add_neg] using hwindow i hi (-Hphys)
      (by rw [abs_neg,abs_of_nonneg hHphys]; linarith only [hDpad])
  have hRight i (hi : i∈S) : z i-(A i.1:ℝ)+(N:ℝ)/(Cphys+2)∈Ioo (1/2:ℝ) (W i.1-1/2) := by
    rw [hHeq]
    exact hwindow i hi Hphys (by rw [abs_of_nonneg hHphys]; linarith only [hDpad])
  exact hfamily S Fsrc rshift sshift z rat v Nlen Q K₀ N R Jsep Z
    (d:=d) (Wmax:=Wmax) (Tsrc:=Tsrc) (M:=M) (δ:=δ) (Bcut:=Bcut) (Bselect:=Bselect)
    Uref Refs Gaps A W gap anchor e r vRef s
    hd hw hwcap hsmallShift hTsrc hT hM hδ hsourceScale hQ hUbandCap
    hy hzFull hreg hlower hjets htests hden hinv hnegative hMtwo hN
    hJsep hJM hNM hwJ hmesh hgeometry hseparation hshifts hmodel hlevel hminor hcomplete
    hR hRM hscale (fun _ _ => Int.le_ceil M)
    (fun _ _ => by dsimp only [A,W]; linarith) hx (fun i hi => (hgapData i hi).1)
    hchart horientation hBcut hs hrefSet hparentSet hsep hwideL hwideU hUref
    hBselectSize hcutMargin hselectedWrap hreferenceDen hgapWidth hRQ
    hselectedUpper hscaleTen (fun i hi => (hgapData i hi).2) hgap hQN hNsqM hUR
    hrHeight hsHeight heHeight hvHeight hsmall hNR hRN hNcube hminscale
    hNtwo hLeft hRight hanchor hcut hcount hsize hD hΔ hBsize

example
    {csrc Usrc E σ εloss : ℝ}
    (hcsrc : 0 < csrc) (hUsrc : 0 < Usrc)
    (hE : 0 < E) (hσ : 0 < σ) (hεloss : 0 < εloss) :
    let κ := modelPhaseThirdLower σ
    let L := max (32*Usrc^2/csrc^2)
      (64*(modelPhaseJetCoefficient σ 3+1)*Usrc*E/κ^2)
    let θ := 1/(8*(L+3))
    ∃ C Dtype : ℝ, 0 < C ∧ 0 < Dtype ∧
    ∀ᶠ T : ℝ in Filter.atTop, ∀ (S : Finset (ℝ × ℤ)) (Fsrc rshift sshift : ℝ → ℝ)
    (z : (ℝ × ℤ) → ℝ) (rat : (ℝ × ℤ) → ℚ) (v : (ℝ × ℤ) → ℤ) (Nlen : (ℝ × ℤ) → ℕ)
    (Q K₀ N : ℕ) [NeZero K₀] (R Jsep : ℝ) (Z : ℝ → ℤ)
    {d Wmax Tsrc M δ Bcut Bselect : ℝ}
    (Uref : ℕ) (anchor : (ℝ × ℤ) → ℚ),
    let lambda := csrc*Tsrc/(2*M^2)
    let Uband := Usrc*Tsrc/M^2
    let Vscale := max 1 (Uband*(N:ℝ)/(Q:ℝ))
    let Buffer := (56*(Uref:ℝ)/κ)*(N:ℝ)+(N:ℝ)/(σ*(σ+1)+3)+2
    (0 < d) → (0 ≤ Wmax) → (Wmax ≤ 1/4) → (2*Usrc*Wmax ≤ csrc/64) →
    (0 < Tsrc) →
    (0 < T) →
    (0 < M) →
    (δ ≤ min (modelPhaseThirdLower σ) 1) →
    (Tsrc ≤ E*T) →
    (0 < Q) → (Uband ≤ 1) →
    (∀ i∈S, i.1∈Icc (1:ℝ) 2) →
    (∀ i∈S, z i∈Ioo (M+Buffer) (2*M-Buffer)) →
    (∀ w, 0 < w → ContDiffAt ℝ ∞ Fsrc w) →
    (∀ w∈Icc (1/2:ℝ) 3, csrc ≤ iteratedDeriv 5 Fsrc w) →
    (∀ w∈Icc (1/2:ℝ) 3, ∀ n, 1 ≤ n → n ≤ 7 → |iteratedDeriv n Fsrc w| ≤ Usrc) →
    (∀ w∈Icc (1/2:ℝ) 3,
      csrc ≤ |(iteratedDeriv 5 Fsrc w)^2-iteratedDeriv 4 Fsrc w*iteratedDeriv 6 Fsrc w|) →
    (∀ i∈S, (rat i).den ≤ Q ∧ Q ≤ 2*(rat i).den) →
    (∀ i∈S, ((rat i).den:ℤ) ∣ (rat i).num*v i-1) →
    (∀ w∈Icc (1/2:ℝ) 3, iteratedDeriv 4 Fsrc w ≤ -csrc) →
    (2 ≤ M) →
    (0 < N) →
    (0 < Jsep) → (Jsep ≤ M) → ((N:ℝ) ≤ M) → (Wmax*Jsep ≤ 1) →
    ((Q:ℝ)*(N:ℝ) ≤ (K₀:ℝ)*R^2) →
    (∀ i∈S, N ≤ Nlen i ∧ Nlen i ≤ 3*N ∧
      round (z i)+(Nlen i:ℤ)=Z i.1+(N:ℤ)*i.2+2*(N:ℤ)) →
    (∀ i∈S, ∀ j∈S, i.1≠j.1 → 1 ≤ Jsep*|i.1-j.1|) →
    (∀ y∈S.image Prod.fst,
      0 ≤ rshift y ∧ 0 ≤ sshift y ∧ rshift y*sshift y=d*y ∧ rshift y+sshift y ≤ Wmax) →
    let Φ := fun y u =>
      (Fsrc u-Fsrc (u+rshift y)-Fsrc (u+sshift y)+Fsrc (u+rshift y+sshift y))/d
    let Fmodel := fun (i : ℝ × ℤ) u => (Tsrc/T)*Φ i.1 u
    (∀ i∈S, Expdb.IsApproximateModelPhaseFunction (Fmodel i) σ 4 δ) →
    let f := fun p w => Tsrc*Φ p (w/M)
    (∀ i∈S, iteratedDeriv 2 (f (i.1)) (z i)/2=(rat i:ℝ)) →
    (∀ i∈S, 1 ≤ Nlen i ∧ (rat i).den ≤ Nlen i ∧
      1 ≤ (iteratedDeriv 3 (f (i.1)) (round (z i))/6)*((rat i).den:ℝ)^2*Nlen i) →
    (∀ i∈S, 7*((iteratedDeriv 3 (f (i.1)) (round (z i))/6)*
      ((rat i).den:ℝ)*(Nlen i:ℝ)^2) ≤ K₀) →

    (1 ≤ R) → (R ≤ M) → (T*(N:ℝ)*R^2=M^3) →
    (0 < Bcut) →
    (1 ≤ Uref) →
    (2+168/κ ≤ Bselect) → (7*Bcut ≤ κ*Bselect) →
    (Bselect^2*(Uref:ℝ)^3*R^2 ≤ (N:ℝ)^2) →
    (R ≤ (Q:ℝ)) →
    ((Uref:ℝ) ≤ ((N:ℝ)/(Q:ℝ))^((2:ℝ)/3)/Bselect) →
    ((N:ℝ)^10 ≤ M^3*R^7) →
    (Q:ℝ) ≤ (N:ℝ) →
    ((N:ℝ)^2 ≤ M ∨ (1 ≤ M ∧ (N:ℝ) ≤ T ∧ R^2 ≤ T)) → (Uref:ℝ) ≤ R^2 →
    let Cphys := σ*(σ+1)+1
    let c := κ/6
    let J := Cphys/6
    let B := max 1 (max (2*Real.sqrt J) (8*J*Real.sqrt J/(3*c)))
    B*R^2/(N:ℝ)^2 ≤ 1/2 →
    (N:ℝ) ≤ R^2 → R ≤ (N:ℝ) → (N:ℝ)^3 ≤ M*R^2 →
    2*R^2 ≤ (Q:ℝ)*(N:ℝ) →
    2 ≤ (N:ℝ) →
    let ε := κ/(16*(Cphys+2)*R^2)
    (∀ i∈S, |(anchor i:ℝ)-(rat i:ℝ)| ≤ ε) →
    (∀ i∈S, 256*((anchor i).den:ℝ) ≤ (Q:ℝ)/3) →
    (∀ i∈S, 256 ≤ (2*ε)*((Q:ℝ)/3)*(anchor i).den) →
    let narrow := fun (i : ℝ × ℤ) =>
      (⌊((rat i).den:ℝ)/(θ*((Q:ℝ)/2))⌋,
       ⌊((rat i).num:ℝ)/(θ*(lambda*(Q:ℝ)/2))⌋)
    let qell := fun (i : ℝ × ℤ) => ((rat i).den:ℝ)*deriv (f (i.1)) (round (z i))
    let V := S ×ˢ (Finset.univ : Finset (Fin 2))
    let offset := fun ip : (ℝ × ℤ) × Fin 2 => ⌊qell ip.1⌋+(ip.2:ℕ)-round (qell ip.1)
    let color := fun ip : (ℝ × ℤ) × Fin 2 => (narrow ip.1,offset ip)
    let NarrowCap := (4/θ+3)*(8*Usrc/(csrc*θ)+3)
    let Cap := 3*NarrowCap

    let q := fun (i : ℝ × ℤ) => (rat i).den
    let μ := fun (i : ℝ × ℤ) => iteratedDeriv 3 (f (i.1)) (round (z i))/6
    let b := fun ip : (ℝ × ℤ) × Fin 2 => (⌊qell ip.1⌋+(ip.2:ℕ) : ℤ)
    let tau := fun ip : (ℝ × ℤ) × Fin 2 => ((b ip:ℝ)-qell ip.1)/2
    let dual := fun (i : ℝ × ℤ) => -2*μ i*(Real.sqrt (2/(3*μ i*(q i:ℝ))))^3
    let x := fun ip : (ℝ × ℤ) × Fin 2 =>
      (![-(v ip.1:ℝ)*b ip/q ip.1,-(v ip.1:ℝ)/q ip.1,
        dual ip.1,3*dual ip.1*tau ip/2] : Fin 4 → ℝ)
    let Fiber := fun key => V.filter (fun ip => color ip=key)
    let μ₀ := csrc*Tsrc/(12*M^3)
    let U₀ := Usrc*Tsrc/(2*M^3)
    let Δtype := (16*U₀/μ₀)*Real.sqrt (U₀*(Q:ℝ)^3)*Real.sqrt K₀/(6*(K₀:ℝ)^2)
    let C₂ := modelPhaseJetCoefficient σ 2+δ
    let C₃ := modelPhaseJetCoefficient σ 3+δ
    let Ct := C₂/2+5*C₃/12
    let Cc := C₂/κ+C₃/(2*κ)
    let Δ := (37*B/2+16*B*Cc+2*Ct+2*Cc)*(Q:ℝ)/(N:ℝ)
    let Ccurv := (4/κ)*(B+2*quarticReciprocalConstant σ δ)
    let D := Δ+quarticNonlinearResidualConstant σ δ*(2*(Q:ℝ))/(N:ℝ)
    let Kres := 4*(37*B/2+16*B*Cc+2*Ct+2*Cc+
      2*quarticNonlinearResidualConstant σ δ)/κ
    let Esize := κ/(16*(Cphys+2))
    let Dbase := 37*B/2+16*B*Cc+2*Ct+2*Cc+2*quarticNonlinearResidualConstant σ δ
    let Tbase := (2/κ)*(B+2*quarticReciprocalConstant σ δ)
    2*3840*128^2*105*(Dbase+64*Tbase*Esize^2) ≤ Bselect*Esize →
    D ≤ 1/2 → Δ < 1/2 → 61*Ccurv*Cphys ≤ Bcut →
    let Lunit := 2*κ/Cphys
    let Gamma := Cphys/κ
    let Cthird := Gamma*(32*Kres+9*quarticReciprocalConstant σ δ)
    let Cpack := 64*Cphys*(Gamma^2*Cthird+Gamma*(modelPhaseJetCoefficient σ 3+δ)/κ)/κ
    let Cfirst := 128*Cphys*(Gamma^2*Cthird+Gamma*(modelPhaseJetCoefficient σ 3+δ)/κ)/κ^2
    let Cgap := 64*Cphys*(Gamma^2*B+Gamma*(modelPhaseJetCoefficient σ 3+δ)/κ)/κ
    let Cmain := 4*(2*Cfirst/Lunit^3)^((3:ℝ)⁻¹)+2
    let Ctail := 4*Cpack/Lunit^2+Cgap
    let Klarge := 60*588*(Uband/lambda)^2*Uband^2*(R^8/(N:ℝ)^4)*
      (Cmain*((Q:ℝ)/(Uband*(N:ℝ)))^((2:ℝ)/3)+Ctail/(Uref:ℝ))
    let Y := S.image Prod.fst
    let Values := fun k : ZMod K₀ =>
      ∑ ip∈V, ‖∑ j : ZMod K₀, ZMod.stdAddChar (-(j*k))*
        GafniTao.fordAdditiveCharacter (∑ d,x ip d*
          (![(j.val+1:ℝ),(j.val+1:ℝ)^2,(j.val+1:ℝ)^((3:ℝ)/2),
            Real.sqrt (j.val+1:ℝ)] : Fin 4 → ℝ) d)‖
    let Wphys := (144*Usrc/(csrc*κ))*(R^2/(Q:ℝ))
    let WeightedValues := fun k : ZMod K₀ =>
      ∑ ip∈V, (Real.sqrt (2*(q ip.1:ℝ))/((q ip.1:ℝ)*Real.sqrt (μ ip.1*(Nlen ip.1:ℝ))))*
        ‖∑ j : ZMod K₀, ZMod.stdAddChar (-(j*k))*
          GafniTao.fordAdditiveCharacter (∑ d,x ip d*
            (![(j.val+1:ℝ),(j.val+1:ℝ)^2,(j.val+1:ℝ)^((3:ℝ)/2),
              Real.sqrt (j.val+1:ℝ)] : Fin 4 → ℝ) d)‖
    let Mass := Vscale*Dtype*(2+θ*(Uband+1/lambda))*(Y.card:ℝ)*(M/(N:ℝ))*(1+Δtype*Jsep)+
      (Y.card:ℝ)^2*Klarge*T^εloss
    ((V.image color).card:ℝ) ≤ Cap ∧
      (∀ k, (Values k)^12 ≤ C*(K₀:ℝ)^((12:ℝ)+εloss)*Cap^11*
        ∑ key∈V.image color, ((Fiber key).card:ℝ)^10*Mass) ∧
      (V.card:ℝ) ≤ 10*(Y.card:ℝ)*(M/(N:ℝ)) ∧
      (∀ k, (Values k)^12 ≤ C*(K₀:ℝ)^((12:ℝ)+εloss)*Cap^11*
        (10*(Y.card:ℝ)*(M/(N:ℝ)))^10*Mass) ∧
      ∀ k, ((WeightedValues k)^12 ≤ Wphys^6*
        (C*(K₀:ℝ)^((12:ℝ)+εloss)*Cap^11*(V.card:ℝ)^10*Mass)) ∧
        (WeightedValues k)^12 ≤ Wphys^6*
          (C*(K₀:ℝ)^((12:ℝ)+εloss)*Cap^11*(10*(Y.card:ℝ)*(M/(N:ℝ)))^10*Mass) := by
  exact eventually_double_difference_constructed_reference_weighted_sieve hcsrc hUsrc hE hσ hεloss

#print axioms eventually_double_difference_constructed_reference_weighted_sieve

/-- Unchanged existing private completion-error proof, copied only for scratch access. -/
private theorem cubic_completion_point_error
    {σ c N R A μ : ℝ} (hσ : 0 < σ) (hc : 0 < c) (hN : 1 ≤ N) (hR : 0 < R)
    (hAlow : N ≤ A) (hAhigh : A ≤ 3*N)
    (hμ : c/(12*σ*N*R^2) ≤ μ) :
    Real.sqrt A*Real.log (2*A)+1/(μ*A^2) ≤
      Real.sqrt (3*N)*Real.log (6*N)+12*σ*R^2/(c*N) := by
  have hNp : 0 < N := zero_lt_one.trans_le hN
  have hAp : 0 < A := hNp.trans_le hAlow
  have hμp : 0 < μ := (div_pos hc (by positivity)).trans_le hμ
  have hlog : Real.sqrt A*Real.log (2*A) ≤ Real.sqrt (3*N)*Real.log (6*N) := by
    apply mul_le_mul (Real.sqrt_le_sqrt hAhigh)
      (Real.log_le_log (by positivity) (by linarith only [hAhigh]))
      (Real.log_nonneg (by linarith only [hAlow,hN])) (Real.sqrt_nonneg _)
  have hden : c*N/(12*σ*R^2) ≤ μ*A^2 := by
    calc
      _ = (c/(12*σ*N*R^2))*N^2 := by field_simp
      _ ≤ _ := mul_le_mul hμ (pow_le_pow_left₀ hNp.le hAlow 2) (sq_nonneg _) hμp.le
  have hrecip := one_div_le_one_div_of_le (show 0 < c*N/(12*σ*R^2) by positivity) hden
  have he : 1/(c*N/(12*σ*R^2)) = 12*σ*R^2/(c*N) := by field_simp
  rw [he] at hrecip
  exact add_le_add hlog hrecip

example
    {σ c N R A μ : ℝ} (hσ : 0 < σ) (hc : 0 < c) (hN : 1 ≤ N) (hR : 0 < R)
    (hAlow : N ≤ A) (hAhigh : A ≤ 3*N)
    (hμ : c/(12*σ*N*R^2) ≤ μ) :
    Real.sqrt A*Real.log (2*A)+1/(μ*A^2) ≤
      Real.sqrt (3*N)*Real.log (6*N)+12*σ*R^2/(c*N) := by
  exact cubic_completion_point_error hσ hc hN hR hAlow hAhigh hμ

#print axioms cubic_completion_point_error

/-- Original selected double-phase block sums consume the SAME constructed Fourier
centres and weighted sieve. This common-amplitude consumer derives the completion
error; source-only constants precede all phases and physical scales. Actual
minimum-anchor/root selection and common source normalization remain upstream. -/
private theorem eventually_double_difference_original_selected_block_moment
    {csrc Usrc σ εloss : ℝ}
    (hcsrc : 0 < csrc) (hUsrc : 0 < Usrc)
    (hσ : 0 < σ) (hεloss : 0 < εloss) :
    let κ := modelPhaseThirdLower σ
    let L := max (32*Usrc^2/csrc^2)
      (64*(modelPhaseJetCoefficient σ 3+1)*Usrc/κ^2)
    let θ := 1/(8*(L+3))
    ∃ CF C Dtype : ℝ, 1 ≤ CF ∧ 0 < C ∧ 0 < Dtype ∧
    ∀ᶠ T : ℝ in Filter.atTop, ∀ (S : Finset (ℝ × ℤ)) (Fsrc rshift sshift : ℝ → ℝ)
    (H : (ℝ × ℤ) → ℕ) (za : (ℝ × ℤ) → ℝ)
    (Q K₀ N : ℕ) [NeZero K₀] (R Jsep : ℝ) (Z : ℝ → ℤ)
    {d Wmax M δ Bcut Bselect : ℝ}
    (Uref : ℕ) (anchor : (ℝ × ℤ) → ℚ),
    let lambda := csrc*T/(2*M^2)
    let Uband := Usrc*T/M^2
    let Vscale := max 1 (Uband*(N:ℝ)/(Q:ℝ))
    let Lsrc := fun i : ℝ × ℤ => Z i.1+(N:ℤ)*i.2+2*(N:ℤ)
    let Buffer := (56*(Uref:ℝ)/κ)*(N:ℝ)+(N:ℝ)/(σ*(σ+1)+3)+2
    (0 < d) → (0 ≤ Wmax) → (Wmax ≤ 1/4) → (2*Usrc*Wmax ≤ csrc/64) →
    (0 < T) →
    (0 < M) →
    (δ ≤ min (modelPhaseThirdLower σ) 1) →
    (0 < Q) → (Uband ≤ 1) →
    (∀ i∈S, i.1∈Icc (1:ℝ) 2) →
    (∀ i∈S, (Lsrc i:ℝ)-2*(N:ℝ)∈Ioo (M+Buffer+(N:ℝ)) (2*M-Buffer-(N:ℝ))) →
    (∀ w, 0 < w → ContDiffAt ℝ ∞ Fsrc w) →
    (∀ w∈Icc (1/2:ℝ) 3, csrc ≤ iteratedDeriv 5 Fsrc w) →
    (∀ w∈Icc (1/2:ℝ) 3, ∀ n, 1 ≤ n → n ≤ 7 → |iteratedDeriv n Fsrc w| ≤ Usrc) →
    (∀ w∈Icc (1/2:ℝ) 3,
      csrc ≤ |(iteratedDeriv 5 Fsrc w)^2-iteratedDeriv 4 Fsrc w*iteratedDeriv 6 Fsrc w|) →
    (∀ w∈Icc (1/2:ℝ) 3, iteratedDeriv 4 Fsrc w ≤ -csrc) →
    (2 ≤ M) →
    (0 < N) →
    (0 < Jsep) → (Jsep ≤ M) → ((N:ℝ) ≤ M) → (Wmax*Jsep ≤ 1) →
    ((Q:ℝ)*(N:ℝ) ≤ (K₀:ℝ)*R^2) →
    (∀ i∈S, H i ≤ N) →
    7*(N:ℝ)+2 ≤ M/4 →
    (3*Usrc)*(6*(N:ℝ)+1)^4 ≤ M*(N:ℝ)*R^2 →
    (3*Usrc/4)*(6*(N:ℝ)+1)^2 ≤ (N:ℝ)*R^2 →
    63*(Usrc/(2*(N:ℝ)*R^2))*(Q:ℝ)*(N:ℝ)^2 ≤ K₀ →
    (∀ i∈S, 2*(anchor i).den ≤ Q) →
    (∀ i∈S, 128*R^2 ≤ csrc*(Q:ℝ)*(anchor i).den) →
    (∀ i∈S, ∀ j∈S, i.1≠j.1 → 1 ≤ Jsep*|i.1-j.1|) →
    (∀ y∈S.image Prod.fst,
      0 ≤ rshift y ∧ 0 ≤ sshift y ∧ rshift y*sshift y=d*y ∧ rshift y+sshift y ≤ Wmax) →
    let Φ := fun y u =>
      (Fsrc u-Fsrc (u+rshift y)-Fsrc (u+sshift y)+Fsrc (u+rshift y+sshift y))/d
    let Fmodel := fun (i : ℝ × ℤ) u => Φ i.1 u
    (∀ i∈S, Expdb.IsApproximateModelPhaseFunction (Fmodel i) σ 4 δ) →
    let f := fun p w => T*Φ p (w/M)
    (∀ i∈S, za i∈Ioo ((Lsrc i:ℝ)-2*(N:ℝ)-(N:ℝ)/8)
      ((Lsrc i:ℝ)-2*(N:ℝ)+(N:ℝ)/8) ∧
      iteratedDeriv 2 (f i.1) (za i)/2=(anchor i:ℝ)) →

    (1 ≤ R) → (R ≤ M) → (T*(N:ℝ)*R^2=M^3) →
    (0 < Bcut) →
    (1 ≤ Uref) →
    (2+168/κ ≤ Bselect) → (7*Bcut ≤ κ*Bselect) →
    (Bselect^2*(Uref:ℝ)^3*R^2 ≤ (N:ℝ)^2) →
    (R ≤ (Q:ℝ)) →
    ((Uref:ℝ) ≤ ((N:ℝ)/(Q:ℝ))^((2:ℝ)/3)/Bselect) →
    ((N:ℝ)^10 ≤ M^3*R^7) →
    (Q:ℝ) ≤ (N:ℝ) →
    ((N:ℝ)^2 ≤ M ∨ (1 ≤ M ∧ (N:ℝ) ≤ T ∧ R^2 ≤ T)) → (Uref:ℝ) ≤ R^2 →
    let Cphys := σ*(σ+1)+1
    let c := κ/6
    let J := Cphys/6
    let B := max 1 (max (2*Real.sqrt J) (8*J*Real.sqrt J/(3*c)))
    B*R^2/(N:ℝ)^2 ≤ 1/2 →
    (N:ℝ) ≤ R^2 → R ≤ (N:ℝ) → (N:ℝ)^3 ≤ M*R^2 →
    2*R^2 ≤ (Q:ℝ)*(N:ℝ) →
    2 ≤ (N:ℝ) →
    let ε := κ/(16*(Cphys+2)*R^2)
    csrc ≤ 4*κ/(Cphys+2) →
    (∀ i∈S, 256*((anchor i).den:ℝ) ≤ (Q:ℝ)/3) →
    (∀ i∈S, 256 ≤ (2*ε)*((Q:ℝ)/3)*(anchor i).den) →
    let NarrowCap := (4/θ+3)*(8*Usrc/(csrc*θ)+3)
    let Cap := 3*NarrowCap
    let μ₀ := csrc*T/(12*M^3)
    let U₀ := Usrc*T/(2*M^3)
    let Δtype := (16*U₀/μ₀)*Real.sqrt (U₀*(Q:ℝ)^3)*Real.sqrt K₀/(6*(K₀:ℝ)^2)
    let C₂ := modelPhaseJetCoefficient σ 2+δ
    let C₃ := modelPhaseJetCoefficient σ 3+δ
    let Ct := C₂/2+5*C₃/12
    let Cc := C₂/κ+C₃/(2*κ)
    let Δ := (37*B/2+16*B*Cc+2*Ct+2*Cc)*(Q:ℝ)/(N:ℝ)
    let Ccurv := (4/κ)*(B+2*quarticReciprocalConstant σ δ)
    let D := Δ+quarticNonlinearResidualConstant σ δ*(2*(Q:ℝ))/(N:ℝ)
    let Kres := 4*(37*B/2+16*B*Cc+2*Ct+2*Cc+
      2*quarticNonlinearResidualConstant σ δ)/κ
    let Esize := κ/(16*(Cphys+2))
    let Dbase := 37*B/2+16*B*Cc+2*Ct+2*Cc+2*quarticNonlinearResidualConstant σ δ
    let Tbase := (2/κ)*(B+2*quarticReciprocalConstant σ δ)
    2*3840*128^2*105*(Dbase+64*Tbase*Esize^2) ≤ Bselect*Esize →
    D ≤ 1/2 → Δ < 1/2 → 61*Ccurv*Cphys ≤ Bcut →
    let Lunit := 2*κ/Cphys
    let Gamma := Cphys/κ
    let Cthird := Gamma*(32*Kres+9*quarticReciprocalConstant σ δ)
    let Cpack := 64*Cphys*(Gamma^2*Cthird+Gamma*(modelPhaseJetCoefficient σ 3+δ)/κ)/κ
    let Cfirst := 128*Cphys*(Gamma^2*Cthird+Gamma*(modelPhaseJetCoefficient σ 3+δ)/κ)/κ^2
    let Cgap := 64*Cphys*(Gamma^2*B+Gamma*(modelPhaseJetCoefficient σ 3+δ)/κ)/κ
    let Cmain := 4*(2*Cfirst/Lunit^3)^((3:ℝ)⁻¹)+2
    let Ctail := 4*Cpack/Lunit^2+Cgap
    let Klarge := 60*588*(Uband/lambda)^2*Uband^2*(R^8/(N:ℝ)^4)*
      (Cmain*((Q:ℝ)/(Uband*(N:ℝ)))^((2:ℝ)/3)+Ctail/(Uref:ℝ))
    let Y := S.image Prod.fst
    let Wphys := (144*Usrc/(csrc*κ))*(R^2/(Q:ℝ))
    let Mass := Vscale*Dtype*(2+θ*(Uband+1/lambda))*(Y.card:ℝ)*(M/(N:ℝ))*(1+Δtype*Jsep)+
      (Y.card:ℝ)^2*Klarge*T^εloss
    let Error := (S.card:ℝ)*
      (Real.sqrt (3*(N:ℝ))*Real.log (6*(N:ℝ))+36*Usrc*R^2/(csrc*κ*(N:ℝ)))
    (∑ i∈S, ‖∑ n∈Finset.Ioc (Lsrc i) (Lsrc i+H i),(𝐞 (f i.1 n):ℂ)‖)^12 ≤
      CF^12*2^11*((1+Real.log K₀)^12*Wphys^6*
        (C*(K₀:ℝ)^((12:ℝ)+εloss)*Cap^11*(2*(S.card:ℝ))^10*Mass)+Error^12) := by
  classical
  intro κ L θ
  obtain ⟨CF,hCF,hentry⟩ := double_difference_dyadic_anchor_source_fourier hcsrc hUsrc
  have hsource₀ := eventually_double_difference_constructed_reference_weighted_sieve
    hcsrc hUsrc (by norm_num : (0:ℝ) < 1) hσ hεloss
  simp only [mul_one] at hsource₀
  obtain ⟨C,Dtype,hC,hDtype,hsource⟩ := hsource₀
  refine ⟨CF,C,Dtype,hCF,hC,hDtype,?_⟩
  filter_upwards [hsource] with T hfamily
  intro S Fsrc rshift sshift H za Q K₀ N instK R Jsep Z
    d Wmax M δ Bcut Bselect Uref anchor
    lambda Uband Vscale Lsrc Buffer hd hw hwcap hsmallShift hT hM hδ hQ hUbandCap
    hy hbuffer hreg hlower hjets htests hnegative hMtwo hN
    hJsep hJM hNM hwJ hmesh hH hfourBuffer hfourBudget hquadBudget hfullmesh hsmallDen hmajor
    hseparation hshifts Φ Fmodel hmodel f hanchors
    hR hRM hscale hBcut hUref hBselectSize hcutMargin hselectedWrap hRQ
    hselectedUpper hscaleTen hQN hNsqM hUR
    Cphys c J B hsmall hNR hRN hNcube hminscale hNtwo ε hanchorBudget hcut hcount
    NarrowCap Cap μ₀ U₀ Δtype C₂ C₃ Ct Cc Δ Ccurv D Kres Esize Dbase Tbase
    hsize hD hΔ hBsize Lunit Gamma Cthird Cpack Cfirst Cgap Cmain Ctail Klarge Y Wphys Mass Error
  have hκ : 0 < κ := modelPhaseThirdLower_pos hσ
  have hNp : (0:ℝ) < N := Nat.cast_pos.mpr hN
  have hRp : 0 < R := zero_lt_one.trans_le hR
  have hBuffer : 0 ≤ Buffer := by dsimp only [Buffer]; positivity
  have hbase i (hi : i∈S) : (Lsrc i:ℝ)-2*(N:ℝ)∈Icc M (2*M) := by
    have hb := hbuffer i hi
    exact ⟨by linarith only [hb.1,hBuffer,hNp],
      by linarith only [hb.2,hBuffer,hNp]⟩
  have hshift i (hi : i∈S) :=
    hshifts i.1 (Finset.mem_image_of_mem Prod.fst hi)
  obtain ⟨rat,z,hrat,hgeo,hminor,hfour⟩ :=
    hentry (ℝ × ℤ) S Fsrc Prod.fst (fun i => rshift i.1) (fun i => sshift i.1)
      Lsrc H anchor za N Q d Wmax T M R
      (by omega) hH hd hwcap hsmallShift hT hM hRp hy hshift hbase
      hreg hjets hlower hscale hfourBuffer hfourBudget hquadBudget
      (by exact_mod_cast hQN) hsmallDen hmajor hanchors
  let Nlen := fun i : ℝ × ℤ => (Lsrc i-round (z i)).toNat
  let q := fun i : ℝ × ℤ => (rat i).den
  let μ := fun i : ℝ × ℤ => iteratedDeriv 3 (f i.1) (round (z i))/6
  obtain ⟨hcomplete,v,hinv,k,hfourier⟩ := hfour K₀ hfullmesh
  have hz i (hi : i∈S) : z i∈Ioo (M+Buffer) (2*M-Buffer) := by
    have hb := hbuffer i hi
    have ha := (hanchors i hi).1
    have hh := (hrat i hi).2.2.2.2.1
    exact ⟨by linarith only [hb.1,ha.1,hh.1,hNp],
      by linarith only [hb.2,ha.2,hh.2,hNp]⟩
  have hzFull i (hi : i∈S) : z i∈Icc M (2*M) := by
    have hh := hz i hi
    exact ⟨by linarith only [hh.1,hBuffer],by linarith only [hh.2,hBuffer]⟩
  have hden i (hi : i∈S) : (rat i).den ≤ Q ∧ Q ≤ 2*(rat i).den :=
    ⟨(hrat i hi).1,(hrat i hi).2.1⟩
  have hlevel i (hi : i∈S) : iteratedDeriv 2 (f i.1) (z i)/2=(rat i:ℝ) :=
    (hrat i hi).2.2.2.2.2
  have hgeometry i (hi : i∈S) : N ≤ Nlen i ∧ Nlen i ≤ 3*N ∧
      round (z i)+(Nlen i:ℤ)=Z i.1+(N:ℤ)*i.2+2*(N:ℤ) :=
    (hgeo i hi).2
  have htol : csrc/(64*R^2) ≤ ε := by
    calc
      _ ≤ (4*κ/(Cphys+2))/(64*R^2) :=
        div_le_div_of_nonneg_right hanchorBudget (by positivity)
      _ = ε := by dsimp only [ε]; field_simp; ring
  have hanchor i (hi : i∈S) : |(anchor i:ℝ)-(rat i:ℝ)| ≤ ε := by
    rw [abs_sub_comm]
    exact ((hrat i hi).2.2.2.1).trans htol
  have hmodel' i (hi : i∈S) : Expdb.IsApproximateModelPhaseFunction
      (fun u => (T/T)*Φ i.1 u) σ 4 δ := by
    simpa only [div_self hT.ne',one_mul] using hmodel i hi
  have hsieve := hfamily S Fsrc rshift sshift z rat v Nlen Q K₀ N R Jsep Z
    (d:=d) (Wmax:=Wmax) (Tsrc:=T) (M:=M) (δ:=δ) (Bcut:=Bcut) (Bselect:=Bselect)
    Uref anchor hd hw hwcap hsmallShift hT hT hM hδ (by simp) hQ hUbandCap
    hy hz hreg hlower hjets htests hden hinv hnegative hMtwo hN
    hJsep hJM hNM hwJ hmesh hgeometry hseparation hshifts hmodel' hlevel hminor hcomplete
    hR hRM hscale hBcut hUref hBselectSize hcutMargin hselectedWrap hRQ
    hselectedUpper hscaleTen hQN hNsqM hUR hsmall hNR hRN hNcube hminscale
    hNtwo hanchor hcut hcount hsize hD hΔ hBsize
  let b := fun i (p : Fin 2) => (⌊(q i:ℝ)*deriv (f i.1) (round (z i))⌋+(p:ℕ) : ℤ)
  let tau := fun i p => ((b i p:ℝ)-(q i:ℝ)*deriv (f i.1) (round (z i)))/2
  let dual := fun i => -2*μ i*(Real.sqrt (2/(3*μ i*(q i:ℝ))))^3
  let x := fun i p =>
    (![-(v i:ℝ)*b i p/q i,-(v i:ℝ)/q i,dual i,3*dual i*tau i p/2] : Fin 4 → ℝ)
  let val := fun i p =>
    ‖∑ j : ZMod K₀,ZMod.stdAddChar (-(j*k))*
      GafniTao.fordAdditiveCharacter (∑ d,x i p d*
        (![(j.val+1:ℝ),(j.val+1:ℝ)^2,(j.val+1:ℝ)^((3:ℝ)/2),
          Real.sqrt (j.val+1:ℝ)] : Fin 4 → ℝ) d)‖
  let weight := fun i => Real.sqrt (2*(q i:ℝ))/((q i:ℝ)*Real.sqrt (μ i*(Nlen i:ℝ)))
  let Wsum := ∑ i∈S, ∑ p : Fin 2,weight i*val i p
  let FamilyBound := Wphys^6*
    (C*(K₀:ℝ)^((12:ℝ)+εloss)*Cap^11*(2*(S.card:ℝ))^10*Mass)
  have hW12 : Wsum^12 ≤ FamilyBound := by
    have hh := (hsieve.2.2.2.2 k).1
    simpa only [Finset.sum_product,Finset.card_product,Finset.card_univ,Fintype.card_fin,
      Nat.cast_mul,Nat.cast_ofNat,mul_comm (S.card:ℝ) 2] using hh
  have hW0 : 0 ≤ Wsum := by
    apply Finset.sum_nonneg
    intro i _
    exact Finset.sum_nonneg (fun p _ =>
      mul_nonneg (div_nonneg (Real.sqrt_nonneg _)
        (mul_nonneg (Nat.cast_nonneg _) (Real.sqrt_nonneg _))) (norm_nonneg _))
  let PointError := Real.sqrt (3*(N:ℝ))*Real.log (6*(N:ℝ))+
    36*Usrc*R^2/(csrc*κ*(N:ℝ))
  have hPointError : 0 ≤ PointError := by
    dsimp only [PointError]
    exact add_nonneg (mul_nonneg (Real.sqrt_nonneg _)
      (Real.log_nonneg (by linarith only [hNtwo]))) (by positivity)
  have hpoint i (hi : i∈S) :
      Real.sqrt (Nlen i)*Real.log (2*(Nlen i:ℝ))+1/(μ i*(Nlen i:ℝ)^2) ≤ PointError := by
    have hh := double_difference_source_completion_weight Fsrc (q:=(q i:ℝ)) (A:=(Nlen i:ℝ))
      (hshift i hi).1 (hshift i hi).2.1 hd (hy i hi)
      (hshift i hi).2.2.1 (hshift i hi).2.2.2 hwcap hsmallShift
      hcsrc hUsrc hσ hT hT hMtwo hNp hRp (Nat.cast_pos.mpr hQ)
      (by exact_mod_cast (hden i hi).2)
      (by exact_mod_cast (hgeometry i hi).1)
      (hzFull i hi) hscale hδ hreg hlower hjets
      (approximateModelPhase_mono (hmodel' i hi) (by norm_num : 2 ≤ 4) le_rfl)
    have hlo : csrc/(12*(3*Usrc/κ)*(N:ℝ)*R^2) ≤ μ i := by
      calc
        _ = csrc*κ/(36*Usrc*(N:ℝ)*R^2) := by field_simp; ring
        _ ≤ μ i := hh.2.1
    have herr := cubic_completion_point_error (σ:=3*Usrc/κ) (A:=(Nlen i:ℝ)) (by positivity)
      hcsrc (by linarith only [hNtwo] : (1:ℝ) ≤ N) hRp
      (by exact_mod_cast (hgeometry i hi).1)
      (by exact_mod_cast (hgeometry i hi).2.1) hlo
    convert herr using 1
    dsimp only [PointError]
    congr 1
    ring
  have herror : (∑ i∈S, (Real.sqrt (Nlen i)*Real.log (2*(Nlen i:ℝ))+
      1/(μ i*(Nlen i:ℝ)^2))) ≤ Error := by
    calc
      _ ≤ ∑ _i∈S,PointError := Finset.sum_le_sum hpoint
      _ = Error := by rw [Finset.sum_const,nsmul_eq_mul]
  have hError : 0 ≤ Error := mul_nonneg (Nat.cast_nonneg _) hPointError
  have hlog : 0 ≤ 1+Real.log K₀ := by
    have hkpos : 0 < K₀ := NeZero.pos K₀
    have hkone : (1:ℝ) ≤ K₀ := by exact_mod_cast (show 1 ≤ K₀ by omega)
    linarith only [Real.log_nonneg hkone]
  let Total := ∑ i∈S, ‖∑ n∈Finset.Ioc (Lsrc i) (Lsrc i+H i),(𝐞 (f i.1 n):ℂ)‖
  have hTotal : 0 ≤ Total := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  have hfourier' : Total ≤ CF*((1+Real.log K₀)*Wsum+Error) := by
    exact hfourier.trans (mul_le_mul_of_nonneg_left (add_le_add le_rfl herror)
      (zero_le_one.trans hCF))
  have hpow := pow_le_pow_left₀ hTotal hfourier' 12
  rw [mul_pow] at hpow
  have hsplit := add_pow_le (mul_nonneg hlog hW0) hError 12
  rw [mul_pow] at hsplit
  calc
    Total^12 ≤ CF^12*((1+Real.log K₀)*Wsum+Error)^12 := hpow
    _ ≤ CF^12*(2^11*((1+Real.log K₀)^12*Wsum^12+Error^12)) :=
      mul_le_mul_of_nonneg_left hsplit (pow_nonneg (zero_le_one.trans hCF) _)
    _ ≤ CF^12*(2^11*((1+Real.log K₀)^12*FamilyBound+Error^12)) := by
      gcongr
    _ = _ := by
      dsimp only [FamilyBound]
      simp only [mul_assoc]

example
    {csrc Usrc σ εloss : ℝ}
    (hcsrc : 0 < csrc) (hUsrc : 0 < Usrc)
    (hσ : 0 < σ) (hεloss : 0 < εloss) :
    let κ := modelPhaseThirdLower σ
    let L := max (32*Usrc^2/csrc^2)
      (64*(modelPhaseJetCoefficient σ 3+1)*Usrc/κ^2)
    let θ := 1/(8*(L+3))
    ∃ CF C Dtype : ℝ, 1 ≤ CF ∧ 0 < C ∧ 0 < Dtype ∧
    ∀ᶠ T : ℝ in Filter.atTop, ∀ (S : Finset (ℝ × ℤ)) (Fsrc rshift sshift : ℝ → ℝ)
    (H : (ℝ × ℤ) → ℕ) (za : (ℝ × ℤ) → ℝ)
    (Q K₀ N : ℕ) [NeZero K₀] (R Jsep : ℝ) (Z : ℝ → ℤ)
    {d Wmax M δ Bcut Bselect : ℝ}
    (Uref : ℕ) (anchor : (ℝ × ℤ) → ℚ),
    let lambda := csrc*T/(2*M^2)
    let Uband := Usrc*T/M^2
    let Vscale := max 1 (Uband*(N:ℝ)/(Q:ℝ))
    let Lsrc := fun i : ℝ × ℤ => Z i.1+(N:ℤ)*i.2+2*(N:ℤ)
    let Buffer := (56*(Uref:ℝ)/κ)*(N:ℝ)+(N:ℝ)/(σ*(σ+1)+3)+2
    (0 < d) → (0 ≤ Wmax) → (Wmax ≤ 1/4) → (2*Usrc*Wmax ≤ csrc/64) →
    (0 < T) →
    (0 < M) →
    (δ ≤ min (modelPhaseThirdLower σ) 1) →
    (0 < Q) → (Uband ≤ 1) →
    (∀ i∈S, i.1∈Icc (1:ℝ) 2) →
    (∀ i∈S, (Lsrc i:ℝ)-2*(N:ℝ)∈Ioo (M+Buffer+(N:ℝ)) (2*M-Buffer-(N:ℝ))) →
    (∀ w, 0 < w → ContDiffAt ℝ ∞ Fsrc w) →
    (∀ w∈Icc (1/2:ℝ) 3, csrc ≤ iteratedDeriv 5 Fsrc w) →
    (∀ w∈Icc (1/2:ℝ) 3, ∀ n, 1 ≤ n → n ≤ 7 → |iteratedDeriv n Fsrc w| ≤ Usrc) →
    (∀ w∈Icc (1/2:ℝ) 3,
      csrc ≤ |(iteratedDeriv 5 Fsrc w)^2-iteratedDeriv 4 Fsrc w*iteratedDeriv 6 Fsrc w|) →
    (∀ w∈Icc (1/2:ℝ) 3, iteratedDeriv 4 Fsrc w ≤ -csrc) →
    (2 ≤ M) →
    (0 < N) →
    (0 < Jsep) → (Jsep ≤ M) → ((N:ℝ) ≤ M) → (Wmax*Jsep ≤ 1) →
    ((Q:ℝ)*(N:ℝ) ≤ (K₀:ℝ)*R^2) →
    (∀ i∈S, H i ≤ N) →
    7*(N:ℝ)+2 ≤ M/4 →
    (3*Usrc)*(6*(N:ℝ)+1)^4 ≤ M*(N:ℝ)*R^2 →
    (3*Usrc/4)*(6*(N:ℝ)+1)^2 ≤ (N:ℝ)*R^2 →
    63*(Usrc/(2*(N:ℝ)*R^2))*(Q:ℝ)*(N:ℝ)^2 ≤ K₀ →
    (∀ i∈S, 2*(anchor i).den ≤ Q) →
    (∀ i∈S, 128*R^2 ≤ csrc*(Q:ℝ)*(anchor i).den) →
    (∀ i∈S, ∀ j∈S, i.1≠j.1 → 1 ≤ Jsep*|i.1-j.1|) →
    (∀ y∈S.image Prod.fst,
      0 ≤ rshift y ∧ 0 ≤ sshift y ∧ rshift y*sshift y=d*y ∧ rshift y+sshift y ≤ Wmax) →
    let Φ := fun y u =>
      (Fsrc u-Fsrc (u+rshift y)-Fsrc (u+sshift y)+Fsrc (u+rshift y+sshift y))/d
    let Fmodel := fun (i : ℝ × ℤ) u => Φ i.1 u
    (∀ i∈S, Expdb.IsApproximateModelPhaseFunction (Fmodel i) σ 4 δ) →
    let f := fun p w => T*Φ p (w/M)
    (∀ i∈S, za i∈Ioo ((Lsrc i:ℝ)-2*(N:ℝ)-(N:ℝ)/8)
      ((Lsrc i:ℝ)-2*(N:ℝ)+(N:ℝ)/8) ∧
      iteratedDeriv 2 (f i.1) (za i)/2=(anchor i:ℝ)) →

    (1 ≤ R) → (R ≤ M) → (T*(N:ℝ)*R^2=M^3) →
    (0 < Bcut) →
    (1 ≤ Uref) →
    (2+168/κ ≤ Bselect) → (7*Bcut ≤ κ*Bselect) →
    (Bselect^2*(Uref:ℝ)^3*R^2 ≤ (N:ℝ)^2) →
    (R ≤ (Q:ℝ)) →
    ((Uref:ℝ) ≤ ((N:ℝ)/(Q:ℝ))^((2:ℝ)/3)/Bselect) →
    ((N:ℝ)^10 ≤ M^3*R^7) →
    (Q:ℝ) ≤ (N:ℝ) →
    ((N:ℝ)^2 ≤ M ∨ (1 ≤ M ∧ (N:ℝ) ≤ T ∧ R^2 ≤ T)) → (Uref:ℝ) ≤ R^2 →
    let Cphys := σ*(σ+1)+1
    let c := κ/6
    let J := Cphys/6
    let B := max 1 (max (2*Real.sqrt J) (8*J*Real.sqrt J/(3*c)))
    B*R^2/(N:ℝ)^2 ≤ 1/2 →
    (N:ℝ) ≤ R^2 → R ≤ (N:ℝ) → (N:ℝ)^3 ≤ M*R^2 →
    2*R^2 ≤ (Q:ℝ)*(N:ℝ) →
    2 ≤ (N:ℝ) →
    let ε := κ/(16*(Cphys+2)*R^2)
    csrc ≤ 4*κ/(Cphys+2) →
    (∀ i∈S, 256*((anchor i).den:ℝ) ≤ (Q:ℝ)/3) →
    (∀ i∈S, 256 ≤ (2*ε)*((Q:ℝ)/3)*(anchor i).den) →
    let NarrowCap := (4/θ+3)*(8*Usrc/(csrc*θ)+3)
    let Cap := 3*NarrowCap
    let μ₀ := csrc*T/(12*M^3)
    let U₀ := Usrc*T/(2*M^3)
    let Δtype := (16*U₀/μ₀)*Real.sqrt (U₀*(Q:ℝ)^3)*Real.sqrt K₀/(6*(K₀:ℝ)^2)
    let C₂ := modelPhaseJetCoefficient σ 2+δ
    let C₃ := modelPhaseJetCoefficient σ 3+δ
    let Ct := C₂/2+5*C₃/12
    let Cc := C₂/κ+C₃/(2*κ)
    let Δ := (37*B/2+16*B*Cc+2*Ct+2*Cc)*(Q:ℝ)/(N:ℝ)
    let Ccurv := (4/κ)*(B+2*quarticReciprocalConstant σ δ)
    let D := Δ+quarticNonlinearResidualConstant σ δ*(2*(Q:ℝ))/(N:ℝ)
    let Kres := 4*(37*B/2+16*B*Cc+2*Ct+2*Cc+
      2*quarticNonlinearResidualConstant σ δ)/κ
    let Esize := κ/(16*(Cphys+2))
    let Dbase := 37*B/2+16*B*Cc+2*Ct+2*Cc+2*quarticNonlinearResidualConstant σ δ
    let Tbase := (2/κ)*(B+2*quarticReciprocalConstant σ δ)
    2*3840*128^2*105*(Dbase+64*Tbase*Esize^2) ≤ Bselect*Esize →
    D ≤ 1/2 → Δ < 1/2 → 61*Ccurv*Cphys ≤ Bcut →
    let Lunit := 2*κ/Cphys
    let Gamma := Cphys/κ
    let Cthird := Gamma*(32*Kres+9*quarticReciprocalConstant σ δ)
    let Cpack := 64*Cphys*(Gamma^2*Cthird+Gamma*(modelPhaseJetCoefficient σ 3+δ)/κ)/κ
    let Cfirst := 128*Cphys*(Gamma^2*Cthird+Gamma*(modelPhaseJetCoefficient σ 3+δ)/κ)/κ^2
    let Cgap := 64*Cphys*(Gamma^2*B+Gamma*(modelPhaseJetCoefficient σ 3+δ)/κ)/κ
    let Cmain := 4*(2*Cfirst/Lunit^3)^((3:ℝ)⁻¹)+2
    let Ctail := 4*Cpack/Lunit^2+Cgap
    let Klarge := 60*588*(Uband/lambda)^2*Uband^2*(R^8/(N:ℝ)^4)*
      (Cmain*((Q:ℝ)/(Uband*(N:ℝ)))^((2:ℝ)/3)+Ctail/(Uref:ℝ))
    let Y := S.image Prod.fst
    let Wphys := (144*Usrc/(csrc*κ))*(R^2/(Q:ℝ))
    let Mass := Vscale*Dtype*(2+θ*(Uband+1/lambda))*(Y.card:ℝ)*(M/(N:ℝ))*(1+Δtype*Jsep)+
      (Y.card:ℝ)^2*Klarge*T^εloss
    let Error := (S.card:ℝ)*
      (Real.sqrt (3*(N:ℝ))*Real.log (6*(N:ℝ))+36*Usrc*R^2/(csrc*κ*(N:ℝ)))
    (∑ i∈S, ‖∑ n∈Finset.Ioc (Lsrc i) (Lsrc i+H i),(𝐞 (f i.1 n):ℂ)‖)^12 ≤
      CF^12*2^11*((1+Real.log K₀)^12*Wphys^6*
        (C*(K₀:ℝ)^((12:ℝ)+εloss)*Cap^11*(2*(S.card:ℝ))^10*Mass)+Error^12) := by
  exact eventually_double_difference_original_selected_block_moment hcsrc hUsrc hσ hεloss

#print axioms eventually_double_difference_original_selected_block_moment

/-- Uniform positive rescaling preserves the actual fifth-derivative,
determinant and signed fourth-derivative tests and the literal double phase.
This is the narrow double-difference counterpart of the existing single-source
normalization; no all-seven-test premise is introduced. -/
private theorem double_difference_uniform_source_normalization
    (F : ℝ → ℝ) {c U lo hi : ℝ}
    (hc : 0 < c) (hU : 0 < U) (hlo : 0 < lo) (hhi : 0 < hi)
    (hreg : ∀ u, 0 < u → ContDiffAt ℝ ∞ F u)
    (hjets : ∀ u∈Icc (1/2:ℝ) 3, ∀ n, 1 ≤ n → n ≤ 7 →
      |iteratedDeriv n F u| ≤ U)
    (hlower : ∀ u∈Icc (1/2:ℝ) 3, c ≤ iteratedDeriv 5 F u)
    (hdet : ∀ u∈Icc (1/2:ℝ) 3,
      c ≤ |(iteratedDeriv 5 F u)^2-iteratedDeriv 4 F u*iteratedDeriv 6 F u|)
    (hnegative : ∀ u∈Icc (1/2:ℝ) 3, iteratedDeriv 4 F u ≤ -c) :
    let cnew := c*min lo (lo^2)
    let Unew := hi*U
    0 < cnew ∧ 0 < Unew ∧
    ∀ ampl : ℝ, lo ≤ ampl → ampl ≤ hi →
    let Fscaled := fun u => ampl*F u
    (∀ u, 0 < u → ContDiffAt ℝ ∞ Fscaled u) ∧
    (∀ u∈Icc (1/2:ℝ) 3, ∀ n, 1 ≤ n → n ≤ 7 →
      |iteratedDeriv n Fscaled u| ≤ Unew) ∧
    (∀ u∈Icc (1/2:ℝ) 3, cnew ≤ iteratedDeriv 5 Fscaled u) ∧
    (∀ u∈Icc (1/2:ℝ) 3,
      cnew ≤ |(iteratedDeriv 5 Fscaled u)^2-
        iteratedDeriv 4 Fscaled u*iteratedDeriv 6 Fscaled u|) ∧
    (∀ u∈Icc (1/2:ℝ) 3, iteratedDeriv 4 Fscaled u ≤ -cnew) ∧
    ∀ Traw Tmodel d r s M v : ℝ, Tmodel*ampl=Traw →
      Tmodel*(Fscaled (v/M)-Fscaled (v/M+r)-Fscaled (v/M+s)+Fscaled (v/M+r+s))/d=
        Traw*(F (v/M)-F (v/M+r)-F (v/M+s)+F (v/M+r+s))/d := by
  intro cnew Unew
  refine ⟨mul_pos hc (lt_min hlo (pow_pos hlo 2)),mul_pos hhi hU,?_⟩
  intro ampl hampl hamplhi Fscaled
  have hamplpos := hlo.trans_le hampl
  have hderiv n u : iteratedDeriv n Fscaled u=ampl*iteratedDeriv n F u :=
    iteratedDeriv_const_mul_field ampl F
  have hlc : cnew ≤ ampl*c := by
    calc
      cnew ≤ c*lo := mul_le_mul_of_nonneg_left (min_le_left _ _) hc.le
      _ ≤ c*ampl := mul_le_mul_of_nonneg_left hampl hc.le
      _ = ampl*c := mul_comm _ _
  have hlc2 : cnew ≤ ampl^2*c := by
    calc
      cnew ≤ c*lo^2 := mul_le_mul_of_nonneg_left (min_le_right _ _) hc.le
      _ ≤ c*ampl^2 := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hlo.le hampl 2) hc.le
      _ = ampl^2*c := mul_comm _ _
  refine ⟨fun u hu => contDiffAt_const.mul (hreg u hu),?_,?_,?_,?_,?_⟩
  · intro u hu n hn hn'
    rw [hderiv,abs_mul,abs_of_pos hamplpos]
    exact mul_le_mul hamplhi (hjets u hu n hn hn') (abs_nonneg _) hhi.le
  · intro u hu
    rw [hderiv]
    exact hlc.trans (mul_le_mul_of_nonneg_left (hlower u hu) hamplpos.le)
  · intro u hu
    rw [hderiv,hderiv,hderiv]
    have he : (ampl*iteratedDeriv 5 F u)^2-
        (ampl*iteratedDeriv 4 F u)*(ampl*iteratedDeriv 6 F u)=
        ampl^2*((iteratedDeriv 5 F u)^2-iteratedDeriv 4 F u*iteratedDeriv 6 F u) := by ring
    rw [he,abs_mul,abs_of_nonneg (sq_nonneg ampl)]
    exact hlc2.trans (mul_le_mul_of_nonneg_left (hdet u hu) (sq_nonneg ampl))
  · intro u hu
    rw [hderiv]
    have hh := mul_le_mul_of_nonneg_left (hnegative u hu) hamplpos.le
    linarith only [hh,hlc]
  · intro Traw Tmodel d r s M v hT
    change Tmodel*(ampl*F (v/M)-ampl*F (v/M+r)-ampl*F (v/M+s)+ampl*F (v/M+r+s))/d=_
    calc
      _ = (Tmodel*ampl)*(F (v/M)-F (v/M+r)-F (v/M+s)+F (v/M+r+s))/d := by ring
      _ = _ := by rw [hT]

example
    (F : ℝ → ℝ) {c U lo hi : ℝ}
    (hc : 0 < c) (hU : 0 < U) (hlo : 0 < lo) (hhi : 0 < hi)
    (hreg : ∀ u, 0 < u → ContDiffAt ℝ ∞ F u)
    (hjets : ∀ u∈Icc (1/2:ℝ) 3, ∀ n, 1 ≤ n → n ≤ 7 →
      |iteratedDeriv n F u| ≤ U)
    (hlower : ∀ u∈Icc (1/2:ℝ) 3, c ≤ iteratedDeriv 5 F u)
    (hdet : ∀ u∈Icc (1/2:ℝ) 3,
      c ≤ |(iteratedDeriv 5 F u)^2-iteratedDeriv 4 F u*iteratedDeriv 6 F u|)
    (hnegative : ∀ u∈Icc (1/2:ℝ) 3, iteratedDeriv 4 F u ≤ -c) :
    let cnew := c*min lo (lo^2)
    let Unew := hi*U
    0 < cnew ∧ 0 < Unew ∧
    ∀ ampl : ℝ, lo ≤ ampl → ampl ≤ hi →
    let Fscaled := fun u => ampl*F u
    (∀ u, 0 < u → ContDiffAt ℝ ∞ Fscaled u) ∧
    (∀ u∈Icc (1/2:ℝ) 3, ∀ n, 1 ≤ n → n ≤ 7 →
      |iteratedDeriv n Fscaled u| ≤ Unew) ∧
    (∀ u∈Icc (1/2:ℝ) 3, cnew ≤ iteratedDeriv 5 Fscaled u) ∧
    (∀ u∈Icc (1/2:ℝ) 3,
      cnew ≤ |(iteratedDeriv 5 Fscaled u)^2-
        iteratedDeriv 4 Fscaled u*iteratedDeriv 6 Fscaled u|) ∧
    (∀ u∈Icc (1/2:ℝ) 3, iteratedDeriv 4 Fscaled u ≤ -cnew) ∧
    ∀ Traw Tmodel d r s M v : ℝ, Tmodel*ampl=Traw →
      Tmodel*(Fscaled (v/M)-Fscaled (v/M+r)-Fscaled (v/M+s)+Fscaled (v/M+r+s))/d=
        Traw*(F (v/M)-F (v/M+r)-F (v/M+s)+F (v/M+r+s))/d := by
  exact double_difference_uniform_source_normalization F hc hU hlo hhi hreg hjets hlower hdet hnegative

#print axioms double_difference_uniform_source_normalization

/-- Actual product colors share one normalized source with uniform genuine
tests and small-shift budget. The phase amplitude and radius are rescaled
by exact identities, and the existing full finite-color moment loss is kept. -/
private theorem double_difference_colored_common_scale_source
    {σ ε : ℝ} (hσ : 0 < σ) (hε : 0 < ε) :
    ∃ e : ℝ, 0 < e ∧
      ∀ {c U : ℝ}, 0 < c → 0 < U →
    ∃ w₀ a cnew Unew : ℝ,
      0 < w₀ ∧ w₀ ≤ 1/4 ∧ 0 < a ∧ 0 < cnew ∧ 0 < Unew ∧
      2*Unew*w₀ ≤ cnew/64 ∧
      cnew ≤ 4*modelPhaseThirdLower (σ+2)/((σ+2)*(σ+3)+3) ∧
      ∀ (F : ℝ → ℝ),
        (∀ u, 0 < u → ContDiffAt ℝ ∞ F u) →
        (∀ u∈Icc (1/2:ℝ) 3, ∀ p≤6,
          |iteratedDeriv (p+1) F u-iteratedDeriv p (Expdb.modelPhase σ) u| ≤ e) →
        (∀ u∈Icc (1/2:ℝ) 3, ∀ n, 1 ≤ n → n ≤ 7 → |iteratedDeriv n F u| ≤ U) →
        (∀ u∈Icc (1/2:ℝ) 3, c ≤ iteratedDeriv 5 F u) →
        (∀ u∈Icc (1/2:ℝ) 3,
          c ≤ |(iteratedDeriv 5 F u)^2-iteratedDeriv 4 F u*iteratedDeriv 6 F u|) →
        (∀ u∈Icc (1/2:ℝ) 3, iteratedDeriv 4 F u ≤ -c) →
        ∀ {ι : Type*} (S : Finset ι) (y r s : ι → ℝ) (d : ℝ),
          0 < d →
          (∀ i∈S, y i∈Icc (1:ℝ) 2) →
          (∀ i∈S, 0 < r i ∧ 0 < s i ∧ r i+s i ≤ w₀ ∧ r i*s i=d*y i) →
          let color := fun i => ⌊y i/a⌋
          let Cap := 4/a+3
          ((S.image color).card:ℝ) ≤ Cap ∧
          (∀ z : ι → ℂ, ‖∑ i∈S,z i‖^12 ≤
            Cap^11*∑ j∈S.image color, ‖∑ i∈S.filter (fun i => color i=j),z i‖^12) ∧
          ∀ j∈S.image color, ∃ i₀∈S, color i₀=j ∧
            let ampl := 1/(σ*(σ+1)*y i₀)
            let Fsrc := fun u => ampl*F u
            (∀ u, 0 < u → ContDiffAt ℝ ∞ Fsrc u) ∧
            (∀ u∈Icc (1/2:ℝ) 3, ∀ n, 1 ≤ n → n ≤ 7 →
              |iteratedDeriv n Fsrc u| ≤ Unew) ∧
            (∀ u∈Icc (1/2:ℝ) 3, cnew ≤ iteratedDeriv 5 Fsrc u) ∧
            (∀ u∈Icc (1/2:ℝ) 3,
              cnew ≤ |(iteratedDeriv 5 Fsrc u)^2-
                iteratedDeriv 4 Fsrc u*iteratedDeriv 6 Fsrc u|) ∧
            (∀ u∈Icc (1/2:ℝ) 3, iteratedDeriv 4 Fsrc u ≤ -cnew) ∧
            ∀ T N R M : ℝ, 0 < T → 0 < R → T*N*R^2=M^3 →
              let Tnew := T*σ*(σ+1)*y i₀
              let Rnew := R*Real.sqrt ampl
              0 < Tnew ∧ 0 < Rnew ∧
                Rnew^2=R^2*ampl ∧ Tnew*N*Rnew^2=M^3 ∧
              ∀ i∈S, color i=j →
                let G := fun u =>
                  (Fsrc u-Fsrc (u+r i)-Fsrc (u+s i)+Fsrc (u+r i+s i))/d
                Expdb.IsApproximateModelPhaseFunction G (σ+2) 4 ε ∧
                  ∀ v : ℝ, Tnew*G (v/M)=
                    T*(F (v/M)-F (v/M+r i)-F (v/M+s i)+F (v/M+r i+s i))/d := by
  classical
  obtain ⟨e,w,a,he,hw,hwcap,ha,hmodels⟩ := double_difference_colored_common_models hσ 4 hε
  refine ⟨e,he,?_⟩
  intro c U hc hU
  let lo := 1/(2*σ*(σ+1))
  let hi := 1/(σ*(σ+1))
  let cpre := c*min lo (lo^2)
  let Unew := hi*U
  let cnew := min cpre (4*modelPhaseThirdLower (σ+2)/((σ+2)*(σ+3)+3))
  let w₀ := min w (cnew/(128*Unew))
  have hlo : 0 < lo := by dsimp only [lo]; positivity
  have hhi : 0 < hi := by dsimp only [hi]; positivity
  have hcpre : 0 < cpre := mul_pos hc (lt_min hlo (pow_pos hlo 2))
  have hUnew : 0 < Unew := mul_pos hhi hU
  have hcnew : 0 < cnew := lt_min hcpre (div_pos
    (mul_pos (by norm_num) (modelPhaseThirdLower_pos (by positivity))) (by positivity))
  have hw₀ : 0 < w₀ := lt_min hw (div_pos hcnew (by positivity))
  have hsmall : 2*Unew*w₀ ≤ cnew/64 := by
    calc
      _ ≤ 2*Unew*(cnew/(128*Unew)) :=
        mul_le_mul_of_nonneg_left (min_le_right _ _) (by positivity)
      _ = cnew/64 := by field_simp; ring
  refine ⟨w₀,a,cnew,Unew,hw₀,(min_le_left _ _).trans hwcap,ha,hcnew,hUnew,
    hsmall,min_le_right _ _,?_⟩
  intro F hreg happrox hjets hlower hdet hnegative ι S y r s d hd hy hshifts color Cap
  have hshiftsOld i (hiS : i∈S) : 0 < r i ∧ 0 < s i ∧ r i+s i ≤ w ∧ r i*s i=d*y i :=
    ⟨(hshifts i hiS).1,(hshifts i hiS).2.1,
      (hshifts i hiS).2.2.1.trans (min_le_left _ _),(hshifts i hiS).2.2.2⟩
  obtain ⟨hcard,hmoment,hcolored⟩ := hmodels F hreg happrox S y r s d hd hy hshiftsOld
  refine ⟨hcard,hmoment,?_⟩
  intro j hj
  obtain ⟨i₀,hi₀,hcolor₀,hmodel⟩ := hcolored j hj
  refine ⟨i₀,hi₀,hcolor₀,?_⟩
  intro ampl Fsrc
  have hy₀ := hy i₀ hi₀
  have hypos : 0 < y i₀ := zero_lt_one.trans_le hy₀.1
  have hσ₁ : 0 < σ+1 := by positivity
  have hamp : 0 < ampl := by dsimp only [ampl]; positivity
  have hampLow : lo ≤ ampl := by
    apply one_div_le_one_div_of_le (by positivity : 0 < σ*(σ+1)*y i₀)
    nlinarith only [mul_le_mul_of_nonneg_left hy₀.2 (mul_pos hσ hσ₁).le]
  have hampHigh : ampl ≤ hi := by
    apply one_div_le_one_div_of_le (mul_pos hσ hσ₁)
    nlinarith only [mul_le_mul_of_nonneg_left hy₀.1 (mul_pos hσ hσ₁).le]
  obtain ⟨hsrcReg,hsrcJets,hsrcLower,hsrcDet,hsrcNegative,hphase⟩ :=
    (double_difference_uniform_source_normalization F hc hU hlo hhi
      hreg hjets hlower hdet hnegative).2.2 ampl hampLow hampHigh
  have hcc : cnew ≤ cpre := min_le_left _ _
  refine ⟨hsrcReg,hsrcJets,(fun u hu => hcc.trans (hsrcLower u hu)),
    (fun u hu => hcc.trans (hsrcDet u hu)),
    (fun u hu => (hsrcNegative u hu).trans (neg_le_neg hcc)),?_⟩
  intro T N R M hT hR hscale Tnew Rnew
  have hTnew : 0 < Tnew := by dsimp only [Tnew]; positivity
  have hRnew : 0 < Rnew := mul_pos hR (Real.sqrt_pos.mpr hamp)
  have hRsq : Rnew^2=R^2*ampl := by
    dsimp only [Rnew]
    rw [mul_pow,Real.sq_sqrt hamp.le]
  have hTamp : Tnew*ampl=T := by
    dsimp only [Tnew,ampl]
    field_simp
  have hscaleNew : Tnew*N*Rnew^2=M^3 := by
    calc
      _ = (Tnew*ampl)*N*R^2 := by rw [hRsq]; ring
      _ = M^3 := by rw [hTamp,hscale]
  refine ⟨hTnew,hRnew,hRsq,hscaleNew,?_⟩
  intro i hiS hcolor G
  let Graw := fun u => (F u-F (u+r i)-F (u+s i)+F (u+r i+s i))/(σ*(σ+1)*d*y i₀)
  have hGeq : G=Graw := by
    funext u
    dsimp only [G,Graw,Fsrc,ampl]
    field_simp
  refine ⟨?_,?_⟩
  · rw [hGeq]
    exact (hmodel i hiS hcolor).1
  · intro v
    change Tnew*((Fsrc (v/M)-Fsrc (v/M+r i)-Fsrc (v/M+s i)+Fsrc (v/M+r i+s i))/d)=_
    rw [←mul_div_assoc]
    exact hphase T Tnew d (r i) (s i) M v hTamp

example
    {σ ε : ℝ} (hσ : 0 < σ) (hε : 0 < ε) :
    ∃ e : ℝ, 0 < e ∧
      ∀ {c U : ℝ}, 0 < c → 0 < U →
    ∃ w₀ a cnew Unew : ℝ,
      0 < w₀ ∧ w₀ ≤ 1/4 ∧ 0 < a ∧ 0 < cnew ∧ 0 < Unew ∧
      2*Unew*w₀ ≤ cnew/64 ∧
      cnew ≤ 4*modelPhaseThirdLower (σ+2)/((σ+2)*(σ+3)+3) ∧
      ∀ (F : ℝ → ℝ),
        (∀ u, 0 < u → ContDiffAt ℝ ∞ F u) →
        (∀ u∈Icc (1/2:ℝ) 3, ∀ p≤6,
          |iteratedDeriv (p+1) F u-iteratedDeriv p (Expdb.modelPhase σ) u| ≤ e) →
        (∀ u∈Icc (1/2:ℝ) 3, ∀ n, 1 ≤ n → n ≤ 7 → |iteratedDeriv n F u| ≤ U) →
        (∀ u∈Icc (1/2:ℝ) 3, c ≤ iteratedDeriv 5 F u) →
        (∀ u∈Icc (1/2:ℝ) 3,
          c ≤ |(iteratedDeriv 5 F u)^2-iteratedDeriv 4 F u*iteratedDeriv 6 F u|) →
        (∀ u∈Icc (1/2:ℝ) 3, iteratedDeriv 4 F u ≤ -c) →
        ∀ {ι : Type*} (S : Finset ι) (y r s : ι → ℝ) (d : ℝ),
          0 < d →
          (∀ i∈S, y i∈Icc (1:ℝ) 2) →
          (∀ i∈S, 0 < r i ∧ 0 < s i ∧ r i+s i ≤ w₀ ∧ r i*s i=d*y i) →
          let color := fun i => ⌊y i/a⌋
          let Cap := 4/a+3
          ((S.image color).card:ℝ) ≤ Cap ∧
          (∀ z : ι → ℂ, ‖∑ i∈S,z i‖^12 ≤
            Cap^11*∑ j∈S.image color, ‖∑ i∈S.filter (fun i => color i=j),z i‖^12) ∧
          ∀ j∈S.image color, ∃ i₀∈S, color i₀=j ∧
            let ampl := 1/(σ*(σ+1)*y i₀)
            let Fsrc := fun u => ampl*F u
            (∀ u, 0 < u → ContDiffAt ℝ ∞ Fsrc u) ∧
            (∀ u∈Icc (1/2:ℝ) 3, ∀ n, 1 ≤ n → n ≤ 7 →
              |iteratedDeriv n Fsrc u| ≤ Unew) ∧
            (∀ u∈Icc (1/2:ℝ) 3, cnew ≤ iteratedDeriv 5 Fsrc u) ∧
            (∀ u∈Icc (1/2:ℝ) 3,
              cnew ≤ |(iteratedDeriv 5 Fsrc u)^2-
                iteratedDeriv 4 Fsrc u*iteratedDeriv 6 Fsrc u|) ∧
            (∀ u∈Icc (1/2:ℝ) 3, iteratedDeriv 4 Fsrc u ≤ -cnew) ∧
            ∀ T N R M : ℝ, 0 < T → 0 < R → T*N*R^2=M^3 →
              let Tnew := T*σ*(σ+1)*y i₀
              let Rnew := R*Real.sqrt ampl
              0 < Tnew ∧ 0 < Rnew ∧
                Rnew^2=R^2*ampl ∧ Tnew*N*Rnew^2=M^3 ∧
              ∀ i∈S, color i=j →
                let G := fun u =>
                  (Fsrc u-Fsrc (u+r i)-Fsrc (u+s i)+Fsrc (u+r i+s i))/d
                Expdb.IsApproximateModelPhaseFunction G (σ+2) 4 ε ∧
                  ∀ v : ℝ, Tnew*G (v/M)=
                    T*(F (v/M)-F (v/M+r i)-F (v/M+s i)+F (v/M+r i+s i))/d := by
  exact double_difference_colored_common_scale_source hσ hε

#print axioms double_difference_colored_common_scale_source

/-- Source-entry consumer: one sharp extension of the ORIGINAL approximate
model supplies the actual double-difference colors, signed source tests,
common normalized amplitudes/radii and exact physical phase identities.
The tolerance is chosen before extension constants, avoiding circular choices. -/
private theorem approximateModelPhase_enlarged_double_common_scale_source
    {σ ε : ℝ} (hσ : 0 < σ) (hε : 0 < ε) :
    ∃ δ w₀ a c U : ℝ,
      0 < δ ∧ 0 < w₀ ∧ w₀ ≤ 1/4 ∧ 0 < a ∧ 0 < c ∧ 0 < U ∧
      2*U*w₀ ≤ c/64 ∧
      c ≤ 4*modelPhaseThirdLower (σ+2)/((σ+2)*(σ+3)+3) ∧
      ∀ (M : ℝ) (F : ℝ → ℝ), 1 ≤ M →
        Expdb.IsApproximateModelPhaseFunction F σ 7 δ →
      ∃ Fext : ℝ → ℝ,
        (∀ u, 0 < u → ContDiffAt ℝ ∞ Fext u) ∧
        (∀ (T : ℝ) (m n : ℕ), M ≤ (m:ℝ) → (n:ℝ) ≤ 2*M →
          ‖Expdb.exponentialSumAt F T M m n-Expdb.exponentialSumAt Fext T M m n‖ ≤ 6) ∧
        ∀ {ι : Type*} (S : Finset ι) (y r s : ι → ℝ) (d : ℝ),
          0 < d →
          (∀ i∈S, y i∈Icc (1:ℝ) 2) →
          (∀ i∈S, 0 < r i ∧ 0 < s i ∧ r i+s i ≤ w₀ ∧ r i*s i=d*y i) →
          let color := fun i => ⌊y i/a⌋
          let Cap := 4/a+3
          ((S.image color).card:ℝ) ≤ Cap ∧
          (∀ z : ι → ℂ, ‖∑ i∈S,z i‖^12 ≤
            Cap^11*∑ j∈S.image color, ‖∑ i∈S.filter (fun i => color i=j),z i‖^12) ∧
          ∀ j∈S.image color, ∃ i₀∈S, color i₀=j ∧
            let ampl := 1/(σ*(σ+1)*y i₀)
            let Fsrc := fun u => ampl*Fext u
            (∀ u, 0 < u → ContDiffAt ℝ ∞ Fsrc u) ∧
            (∀ u∈Icc (1/2:ℝ) 3, ∀ n, 1 ≤ n → n ≤ 7 →
              |iteratedDeriv n Fsrc u| ≤ U) ∧
            (∀ u∈Icc (1/2:ℝ) 3, c ≤ iteratedDeriv 5 Fsrc u) ∧
            (∀ u∈Icc (1/2:ℝ) 3,
              c ≤ |(iteratedDeriv 5 Fsrc u)^2-
                iteratedDeriv 4 Fsrc u*iteratedDeriv 6 Fsrc u|) ∧
            (∀ u∈Icc (1/2:ℝ) 3, iteratedDeriv 4 Fsrc u ≤ -c) ∧
            ∀ T N R M : ℝ, 0 < T → 0 < R → T*N*R^2=M^3 →
              let Tnew := T*σ*(σ+1)*y i₀
              let Rnew := R*Real.sqrt ampl
              0 < Tnew ∧ 0 < Rnew ∧
                Rnew^2=R^2*ampl ∧ Tnew*N*Rnew^2=M^3 ∧
              ∀ i∈S, color i=j →
                let G := fun u =>
                  (Fsrc u-Fsrc (u+r i)-Fsrc (u+s i)+Fsrc (u+r i+s i))/d
                Expdb.IsApproximateModelPhaseFunction G (σ+2) 4 ε ∧
                  ∀ v : ℝ, Tnew*G (v/M)=
                    T*(Fext (v/M)-Fext (v/M+r i)-Fext (v/M+s i)+Fext (v/M+r i+s i))/d := by
  obtain ⟨e,he,hcommon⟩ := double_difference_colored_common_scale_source hσ hε
  obtain ⟨δ,c₀,U₀,_K,_D,hδ,hc₀,hU₀,_hK,_hD,hbuild⟩ :=
    approximateModelPhase_enlarged_double_difference_count hσ he
  obtain ⟨w₀,a,c,U,hw₀,hwcap,ha,hc,hU,hsmall,hanchor,hcolors⟩ := hcommon hc₀ hU₀
  refine ⟨δ,w₀,a,c,U,hδ,hw₀,hwcap,ha,hc,hU,hsmall,hanchor,?_⟩
  intro M F hM hF
  obtain ⟨Fext,hreg,hjets,hbound,hlower,htests,hnegative,hsharp,_hcount⟩ := hbuild M F hM hF
  have hdet : ∀ u∈Icc (1/2:ℝ) 3,
      c₀ ≤ |(iteratedDeriv 5 Fext u)^2-iteratedDeriv 4 Fext u*iteratedDeriv 6 Fext u| := by
    intro u hu
    have hh := htests u hu (4:Fin 7)
    simpa [HuxleyModel.tests,abs_sub_comm] using hh
  exact ⟨Fext,hreg,hsharp,hcolors Fext hreg hjets hbound hlower hdet hnegative⟩

example
    {σ ε : ℝ} (hσ : 0 < σ) (hε : 0 < ε) :
    ∃ δ w₀ a c U : ℝ,
      0 < δ ∧ 0 < w₀ ∧ w₀ ≤ 1/4 ∧ 0 < a ∧ 0 < c ∧ 0 < U ∧
      2*U*w₀ ≤ c/64 ∧
      c ≤ 4*modelPhaseThirdLower (σ+2)/((σ+2)*(σ+3)+3) ∧
      ∀ (M : ℝ) (F : ℝ → ℝ), 1 ≤ M →
        Expdb.IsApproximateModelPhaseFunction F σ 7 δ →
      ∃ Fext : ℝ → ℝ,
        (∀ u, 0 < u → ContDiffAt ℝ ∞ Fext u) ∧
        (∀ (T : ℝ) (m n : ℕ), M ≤ (m:ℝ) → (n:ℝ) ≤ 2*M →
          ‖Expdb.exponentialSumAt F T M m n-Expdb.exponentialSumAt Fext T M m n‖ ≤ 6) ∧
        ∀ {ι : Type*} (S : Finset ι) (y r s : ι → ℝ) (d : ℝ),
          0 < d →
          (∀ i∈S, y i∈Icc (1:ℝ) 2) →
          (∀ i∈S, 0 < r i ∧ 0 < s i ∧ r i+s i ≤ w₀ ∧ r i*s i=d*y i) →
          let color := fun i => ⌊y i/a⌋
          let Cap := 4/a+3
          ((S.image color).card:ℝ) ≤ Cap ∧
          (∀ z : ι → ℂ, ‖∑ i∈S,z i‖^12 ≤
            Cap^11*∑ j∈S.image color, ‖∑ i∈S.filter (fun i => color i=j),z i‖^12) ∧
          ∀ j∈S.image color, ∃ i₀∈S, color i₀=j ∧
            let ampl := 1/(σ*(σ+1)*y i₀)
            let Fsrc := fun u => ampl*Fext u
            (∀ u, 0 < u → ContDiffAt ℝ ∞ Fsrc u) ∧
            (∀ u∈Icc (1/2:ℝ) 3, ∀ n, 1 ≤ n → n ≤ 7 →
              |iteratedDeriv n Fsrc u| ≤ U) ∧
            (∀ u∈Icc (1/2:ℝ) 3, c ≤ iteratedDeriv 5 Fsrc u) ∧
            (∀ u∈Icc (1/2:ℝ) 3,
              c ≤ |(iteratedDeriv 5 Fsrc u)^2-
                iteratedDeriv 4 Fsrc u*iteratedDeriv 6 Fsrc u|) ∧
            (∀ u∈Icc (1/2:ℝ) 3, iteratedDeriv 4 Fsrc u ≤ -c) ∧
            ∀ T N R M : ℝ, 0 < T → 0 < R → T*N*R^2=M^3 →
              let Tnew := T*σ*(σ+1)*y i₀
              let Rnew := R*Real.sqrt ampl
              0 < Tnew ∧ 0 < Rnew ∧
                Rnew^2=R^2*ampl ∧ Tnew*N*Rnew^2=M^3 ∧
              ∀ i∈S, color i=j →
                let G := fun u =>
                  (Fsrc u-Fsrc (u+r i)-Fsrc (u+s i)+Fsrc (u+r i+s i))/d
                Expdb.IsApproximateModelPhaseFunction G (σ+2) 4 ε ∧
                  ∀ v : ℝ, Tnew*G (v/M)=
                    T*(Fext (v/M)-Fext (v/M+r i)-Fext (v/M+s i)+Fext (v/M+r i+s i))/d := by
  exact approximateModelPhase_enlarged_double_common_scale_source hσ hε

#print axioms approximateModelPhase_enlarged_double_common_scale_source

/-- Nonzero rational curvature values have a quadratic denominator count
without the spurious zero-numerator column. This removes the linear denominator
term responsible for the provisional N*Qmax <= M low-band restriction. -/
private theorem nonzero_rational_bounded_denominator_count
    {ι : Type*} [DecidableEq ι] (S : Finset ι) (r : ι → ℚ)
    (Q B : ℕ) {X : ℝ} (hX : 0 ≤ X)
    (hlevel : ∀ i∈S, |(r i:ℝ)| ≤ X)
    (hden : ∀ i∈S, (r i).den ≤ Q)
    (hne : ∀ i∈S, r i ≠ 0)
    (hmul : ∀ a : ℚ, (S.filter (fun i => r i=a)).card ≤ B) :
    (S.card:ℝ) ≤ 2*(B:ℝ)*X*(Q:ℝ)^2 := by
  classical
  have hnum i (hi : i∈S) : |((r i).num:ℝ)| ≤ X*Q := by
    have hd : (0:ℝ) < (r i).den := Nat.cast_pos.mpr (r i).pos
    have hv := hlevel i hi
    rw [Rat.cast_def,abs_div,abs_of_pos hd] at hv
    exact ((div_le_iff₀ hd).mp hv).trans
      (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr (hden i hi)) hX)
  have hfiber (q : ℕ) :
      ((S.filter (fun i => (r i).den=q)).card:ℝ) ≤ (2*X*Q)*B := by
    let T := S.filter (fun i => (r i).den=q)
    let W := T.image (fun i => (r i).num)
    let Z := (Finset.Icc (-⌊X*(Q:ℝ)⌋) ⌊X*(Q:ℝ)⌋).erase 0
    have hn : 0 ≤ ⌊X*(Q:ℝ)⌋ := Int.floor_nonneg.mpr (by positivity)
    have hz : (0:ℤ)∈Finset.Icc (-⌊X*(Q:ℝ)⌋) ⌊X*(Q:ℝ)⌋ :=
      Finset.mem_Icc.mpr ⟨neg_nonpos.mpr hn,hn⟩
    have hZcard : Z.card=(2*⌊X*(Q:ℝ)⌋).toNat := by
      dsimp only [Z]
      rw [Finset.card_erase_of_mem hz,Int.card_Icc]
      omega
    have hZint : (Z.card:ℤ)=2*⌊X*(Q:ℝ)⌋ := by
      rw [hZcard,Int.toNat_of_nonneg (by omega)]
    have hZreal : (Z.card:ℝ)=2*(⌊X*(Q:ℝ)⌋:ℝ) := by exact_mod_cast hZint
    have hWZ : W⊆Z := by
      intro p hp
      obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hp
      have hiS := (Finset.mem_filter.mp hi).1
      have hh : |(r i).num| ≤ ⌊X*(Q:ℝ)⌋ := Int.le_floor.mpr (by
        simpa only [Int.cast_abs] using hnum i hiS)
      exact Finset.mem_erase.mpr ⟨Rat.num_ne_zero.mpr (hne i hiS),
        Finset.mem_Icc.mpr (abs_le.mp hh)⟩
    have hW : (W.card:ℝ) ≤ 2*X*Q := by
      calc
        _ ≤ (Z.card:ℝ) := Nat.cast_le.mpr (Finset.card_le_card hWZ)
        _ = 2*(⌊X*(Q:ℝ)⌋:ℝ) := hZreal
        _ ≤ 2*(X*Q) := mul_le_mul_of_nonneg_left (Int.floor_le _) (by norm_num)
        _ = _ := by ring
    have hpcount p : (T.filter (fun i => (r i).num=p)).card ≤ B := by
      apply (Finset.card_le_card (show T.filter (fun i => (r i).num=p) ⊆
        S.filter (fun i => r i=(p:ℚ)/q) from ?_)).trans (hmul ((p:ℚ)/q))
      intro i hi
      obtain ⟨hiT,hn⟩ := Finset.mem_filter.mp hi
      obtain ⟨hiS,hd⟩ := Finset.mem_filter.mp hiT
      refine Finset.mem_filter.mpr ⟨hiS,?_⟩
      rw [←Rat.num_div_den (r i),hn,hd]
    calc
      _ = ∑ p∈W,((T.filter (fun i => (r i).num=p)).card:ℝ) := by
        exact_mod_cast Finset.card_eq_sum_card_image (fun i => (r i).num) T
      _ ≤ ∑ _p∈W,(B:ℝ) := Finset.sum_le_sum (fun p _ => Nat.cast_le.mpr (hpcount p))
      _ = (W.card:ℝ)*B := by simp only [Finset.sum_const,nsmul_eq_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_right hW (Nat.cast_nonneg B)
  have hcard : S.card=∑ q∈Finset.Icc 1 Q,(S.filter (fun i => (r i).den=q)).card :=
    Finset.card_eq_sum_card_fiberwise (fun i hi =>
      Finset.mem_Icc.mpr ⟨(r i).pos,hden i hi⟩)
  calc
    _ = ∑ q∈Finset.Icc 1 Q,((S.filter (fun i => (r i).den=q)).card:ℝ) := by
      exact_mod_cast hcard
    _ ≤ ∑ _q∈Finset.Icc 1 Q,(2*X*Q)*(B:ℝ) := Finset.sum_le_sum (fun q _ => hfiber q)
    _ = _ := by
      simp only [Finset.sum_const,nsmul_eq_mul,Nat.card_Icc,Nat.add_sub_cancel]
      ring

example
    {ι : Type*} [DecidableEq ι] (S : Finset ι) (r : ι → ℚ)
    (Q B : ℕ) {X : ℝ} (hX : 0 ≤ X)
    (hlevel : ∀ i∈S, |(r i:ℝ)| ≤ X)
    (hden : ∀ i∈S, (r i).den ≤ Q)
    (hne : ∀ i∈S, r i ≠ 0)
    (hmul : ∀ a : ℚ, (S.filter (fun i => r i=a)).card ≤ B) :
    (S.card:ℝ) ≤ 2*(B:ℝ)*X*(Q:ℝ)^2 := by
  exact nonzero_rational_bounded_denominator_count S r Q B hX hlevel hden hne hmul

#print axioms nonzero_rational_bounded_denominator_count

/-- Actual SAME-phase minimum anchors exclude zero by the proved physical
curvature lower bound. Their low-denominator count is purely quadratic;
the high-denominator term is retained without a claimed improvement. -/
private theorem double_difference_nonzero_anchor_complement

    (S : Finset ℤ) (F : ℝ → ℝ) (N : ℕ) (base : ℝ)
    {r s d y w c U T M R : ℝ}
    (hr : 0 ≤ r) (hs : 0 ≤ s) (hd : 0 < d)
    (hy : y∈Icc (1:ℝ) 2) (hprod : r*s=d*y)
    (hshift : r+s ≤ w) (hw : w ≤ 1/4) (hsmall : 2*U*w ≤ c/64)
    (hc : 0 < c) (hU : 0 < U) (hT : 0 < T) (hM : 0 < M)
    (hN : 0 < N) (hR : 0 < R) (hNM : (N:ℝ) ≤ M)
    (hphase : T*(N:ℝ)*R^2=M^3)
    (hf : ∀ u, 0 < u → ContDiffAt ℝ ∞ F u)
    (hlower : ∀ u∈Icc (1/2:ℝ) 3, c ≤ iteratedDeriv 5 F u)
    (hjets : ∀ u∈Icc (1/2:ℝ) 3, ∀ n, 1 ≤ n → n ≤ 7 → |iteratedDeriv n F u| ≤ U)
    (hnegative : ∀ u∈Icc (1/2:ℝ) 3, iteratedDeriv 4 F u ≤ -c)
    (hpoints : ∀ j∈S, base+(N:ℝ)*j∈Icc (M+(N:ℝ)/4) (2*M-(N:ℝ)/4)) :
    let Φ := fun u => (F u-F (u+r)-F (u+s)+F (u+r+s))/d
    let f := fun v => T*Φ (v/M)
    let h := fun v => iteratedDeriv 2 f v/2
    let t := fun j : ℤ => base+(N:ℝ)*j
    let delta := c/(64*R^2)
    let X := U*M/((N:ℝ)*R^2)
    ∃ (anchor : ℤ → ℚ) (za : ℤ → ℝ),
      (∀ j∈S, (anchor j:ℝ)∈Ioo (h (t j)-delta) (h (t j)+delta) ∧
        ∀ q : ℚ, (q:ℝ)∈Ioo (h (t j)-delta) (h (t j)+delta) → (anchor j).den ≤ q.den) ∧
      (∀ j∈S, h (za j)=(anchor j:ℝ) ∧ |za j-t j| ≤ (N:ℝ)/16 ∧ za j∈Icc M (2*M)) ∧
      ∀ (Q Acut : ℕ) (Bmajor : ℝ), 2 ≤ Acut → Acut ≤ Q → 0 ≤ Bmajor →
    let Bad := S.filter (fun i => ¬ (Acut*(anchor i).den ≤ Q ∧
      Bmajor*R^2 ≤ c*(Q:ℝ)*(anchor i).den))
    let Dlow := Bmajor*R^2/(c*(Q:ℝ))
    let Khigh := Q/Acut+1
    let Dhigh := 64*R^2/(c*(Khigh:ℝ))
    let Cost := 4*X*Dhigh^2+3*Dhigh*(2+Real.log (Dhigh+1))+
      2*X*Dlow^2
    (Bad.card:ℝ) ≤ Cost ∧
      ∀ H : ℤ → ℕ, (∀ i∈S, H i ≤ N) →
        (∑ i∈Bad,(H i:ℝ)) ≤ (N:ℝ)*Cost := by
  classical
  intro Φ f h t delta X
  obtain ⟨anchor,za,hanchor,hroots,hinj,_hvalues,hhighAll⟩ :=
    double_difference_minimal_anchor_roots_sharp_tail S F N base hr hs hd hy hprod
      hshift hw hsmall hc hU hT hM hN hR hNM hphase hf hlower hjets hnegative hpoints
  have hNp : (0:ℝ) < N := Nat.cast_pos.mpr hN
  have hprodpos : 0 < r*s := by rw [hprod]; exact mul_pos hd (zero_lt_one.trans_le hy.1)
  have hrp : 0 < r := by nlinarith only [hr,hs,hprodpos]
  have hsp : 0 < s := by nlinarith only [hr,hs,hprodpos]
  have hXeq : U*T/M^2=X := by
    calc
      _ = U*(T*(N:ℝ)*R^2)/(M^2*((N:ℝ)*R^2)) := by field_simp
      _ = U*M^3/(M^2*((N:ℝ)*R^2)) := by rw [hphase]
      _ = X := by dsimp only [X]; field_simp
  have hanchorBounds j (hj : j∈S) : |(anchor j:ℝ)| ≤ X ∧ anchor j ≠ 0 := by
    have hh := double_difference_physical_curvature_band F (hroots j hj).2.2 hy
      hrp hsp hd hc hU hT hM hprod (hshift.trans hw) hf hnegative
      (fun u hu => hjets u hu 4 (by norm_num) (by norm_num))
    change c*T/(2*M^2) ≤ |h (za j)| ∧ |h (za j)| ≤ U*T/M^2 at hh
    have hroot : h (za j)=(anchor j:ℝ) := (hroots j hj).1
    rw [hroot] at hh
    refine ⟨hh.2.trans_eq hXeq,?_⟩
    intro he
    rw [he,Rat.cast_zero,abs_zero] at hh
    exact (not_lt_of_ge hh.1) (by positivity)
  refine ⟨anchor,za,hanchor,hroots,?_⟩
  intro Q Acut Bmajor hAcut hAQ hBmajor Bad Dlow Khigh Dhigh Cost
  have hQ : 0 < Q := by omega
  have hQr : (0:ℝ) < Q := Nat.cast_pos.mpr hQ
  have hApos : 0 < Acut := by omega
  have hV : 0 ≤ X := by dsimp only [X]; positivity
  have hDlow : 0 ≤ Dlow := by dsimp only [Dlow]; positivity
  have hK : 2 ≤ Khigh := by
    have hh : 1 ≤ Q/Acut := (Nat.le_div_iff_mul_le hApos).mpr (by simpa only [one_mul] using hAQ)
    dsimp only [Khigh]
    omega
  let High := S.filter (fun i => Khigh ≤ (anchor i).den)
  have hhigh : (High.card:ℝ) ≤ 4*X*Dhigh^2+3*Dhigh*(2+Real.log (Dhigh+1)) :=
    hhighAll Khigh hK
  let Low := S.filter (fun i => c*(Q:ℝ)*(anchor i).den < Bmajor*R^2)
  have hlowden i (hi : i∈Low) : (anchor i).den ≤ ⌊Dlow⌋₊ := by
    apply Nat.le_floor
    apply (le_div_iff₀ (mul_pos hc hQr)).mpr
    have hh := (Finset.mem_filter.mp hi).2
    nlinarith only [hh]
  have hlow : (Low.card:ℝ) ≤ 2*X*Dlow^2 := by
    have hcount := nonzero_rational_bounded_denominator_count Low anchor ⌊Dlow⌋₊ 1
      hV (fun i hi => (hanchorBounds i (Finset.mem_filter.mp hi).1).1) hlowden
      (fun i hi => (hanchorBounds i (Finset.mem_filter.mp hi).1).2)
      (by
        intro a
        apply Finset.card_le_one.mpr
        intro i hi j hj
        obtain ⟨hiL,hia⟩ := Finset.mem_filter.mp hi
        obtain ⟨hjL,hja⟩ := Finset.mem_filter.mp hj
        exact hinj (Finset.mem_filter.mp hiL).1 (Finset.mem_filter.mp hjL).1 (hia.trans hja.symm))
    simp only [Nat.cast_one,mul_one] at hcount
    apply hcount.trans
    have hfloor : (⌊Dlow⌋₊:ℝ) ≤ Dlow := Nat.floor_le hDlow
    gcongr
  have hsub : Bad⊆High∪Low := by
    intro i hi
    obtain ⟨hiS,hbad⟩ := Finset.mem_filter.mp hi
    rcases not_and_or.mp hbad with hlarge | hsmall
    · apply Finset.mem_union_left
      apply Finset.mem_filter.mpr
      refine ⟨hiS,?_⟩
      have hh : Q/Acut < (anchor i).den :=
        (Nat.div_lt_iff_lt_mul hApos).mpr (by simpa only [mul_comm] using lt_of_not_ge hlarge)
      exact Nat.succ_le_of_lt hh
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hiS,lt_of_not_ge hsmall⟩)
  have hcard : (Bad.card:ℝ) ≤ Cost := by
    have hh : (Bad.card:ℝ) ≤ (High.card:ℝ)+(Low.card:ℝ) := by
      exact_mod_cast (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
    exact hh.trans (add_le_add hhigh hlow)
  refine ⟨hcard,?_⟩
  intro H hH
  calc
    (∑ i∈Bad,(H i:ℝ)) ≤ ∑ _i∈Bad,(N:ℝ) := Finset.sum_le_sum (fun i hi =>
      Nat.cast_le.mpr (hH i (Finset.mem_filter.mp hi).1))
    _ = (N:ℝ)*(Bad.card:ℝ) := by simp only [Finset.sum_const,nsmul_eq_mul,mul_comm]
    _ ≤ (N:ℝ)*Cost := mul_le_mul_of_nonneg_left hcard hNp.le

example

    (S : Finset ℤ) (F : ℝ → ℝ) (N : ℕ) (base : ℝ)
    {r s d y w c U T M R : ℝ}
    (hr : 0 ≤ r) (hs : 0 ≤ s) (hd : 0 < d)
    (hy : y∈Icc (1:ℝ) 2) (hprod : r*s=d*y)
    (hshift : r+s ≤ w) (hw : w ≤ 1/4) (hsmall : 2*U*w ≤ c/64)
    (hc : 0 < c) (hU : 0 < U) (hT : 0 < T) (hM : 0 < M)
    (hN : 0 < N) (hR : 0 < R) (hNM : (N:ℝ) ≤ M)
    (hphase : T*(N:ℝ)*R^2=M^3)
    (hf : ∀ u, 0 < u → ContDiffAt ℝ ∞ F u)
    (hlower : ∀ u∈Icc (1/2:ℝ) 3, c ≤ iteratedDeriv 5 F u)
    (hjets : ∀ u∈Icc (1/2:ℝ) 3, ∀ n, 1 ≤ n → n ≤ 7 → |iteratedDeriv n F u| ≤ U)
    (hnegative : ∀ u∈Icc (1/2:ℝ) 3, iteratedDeriv 4 F u ≤ -c)
    (hpoints : ∀ j∈S, base+(N:ℝ)*j∈Icc (M+(N:ℝ)/4) (2*M-(N:ℝ)/4)) :
    let Φ := fun u => (F u-F (u+r)-F (u+s)+F (u+r+s))/d
    let f := fun v => T*Φ (v/M)
    let h := fun v => iteratedDeriv 2 f v/2
    let t := fun j : ℤ => base+(N:ℝ)*j
    let delta := c/(64*R^2)
    let X := U*M/((N:ℝ)*R^2)
    ∃ (anchor : ℤ → ℚ) (za : ℤ → ℝ),
      (∀ j∈S, (anchor j:ℝ)∈Ioo (h (t j)-delta) (h (t j)+delta) ∧
        ∀ q : ℚ, (q:ℝ)∈Ioo (h (t j)-delta) (h (t j)+delta) → (anchor j).den ≤ q.den) ∧
      (∀ j∈S, h (za j)=(anchor j:ℝ) ∧ |za j-t j| ≤ (N:ℝ)/16 ∧ za j∈Icc M (2*M)) ∧
      ∀ (Q Acut : ℕ) (Bmajor : ℝ), 2 ≤ Acut → Acut ≤ Q → 0 ≤ Bmajor →
    let Bad := S.filter (fun i => ¬ (Acut*(anchor i).den ≤ Q ∧
      Bmajor*R^2 ≤ c*(Q:ℝ)*(anchor i).den))
    let Dlow := Bmajor*R^2/(c*(Q:ℝ))
    let Khigh := Q/Acut+1
    let Dhigh := 64*R^2/(c*(Khigh:ℝ))
    let Cost := 4*X*Dhigh^2+3*Dhigh*(2+Real.log (Dhigh+1))+
      2*X*Dlow^2
    (Bad.card:ℝ) ≤ Cost ∧
      ∀ H : ℤ → ℕ, (∀ i∈S, H i ≤ N) →
        (∑ i∈Bad,(H i:ℝ)) ≤ (N:ℝ)*Cost := by
  exact double_difference_nonzero_anchor_complement S F N base hr hs hd hy hprod
    hshift hw hsmall hc hU hT hM hN hR hNM hphase hf hlower hjets hnegative hpoints

#print axioms double_difference_nonzero_anchor_complement

/-- Exact alternative fourth-pair worksheet with a larger small-product
cutoff, anchor/nonempty-band scale inequalities, and the extra terminal
monomial for a denominator cap min(N,M/N). This is arithmetic only;
it does not assert an analytic all-band assembly. -/
private theorem fourth_pair_capped_terminal_source_window_scales
    {t u : ℝ} (ht : t∈Icc (0:ℝ) 1) (hu : u∈Icc (0:ℝ) 1) :
    let α := (1-t)*(890/3277)+t*(17604372/60424193)
    let h := ((1-t)*2749411+t*3296917)/100000000
    let g₀ := ((1-t)*16756+t*1976824)/100000000
    let ν₀ := ((1-t)*11931645+t*14567321)/100000000
    let ν₁ := ((1-t)*11969967+t*14925729)/100000000
    let g := (1-u)*g₀+u*(3*h)
    let ν := (1-u)*ν₀+u*ν₁
    let β := 89/3478+(7441/8695)*α
    1/100000 ≤ g₀ ∧ g₀+1/100000 ≤ 3*h ∧ 1/100000 ≤ h ∧
      8*h+1/100000 ≤ α ∧
      2*α+1/2+(3/2)*g₀-3*h+1/100000 ≤ 4*β ∧
      5*α-1/2+g₀/2-3*h+1/100000 ≤ 4*β ∧
      1/100000 ≤ ν ∧ ν+1/100000 ≤ α ∧
      4*α-1-g+1/100000 ≤ ν ∧ ν+3*α+1/100000 ≤ 1+g ∧
      3*α+1/100000 ≤ 1+g ∧ 7*α+1/100000 ≤ 2+2*g+ν ∧
      5*α-1-g+1/100000 ≤ 3*ν ∧
      4*ν+1/100000 ≤ 6*α-1-g ∧
      1+g+1/100000 ≤ 4*α ∧
      1+g+2*ν+1/100000 ≤ 5*α ∧
      3+3*g+11*ν+1/100000 ≤ 17*α ∧
      7+7*g+27*ν+1/100000 ≤ 41*α ∧
      288*α-144*h+1/10000 ≤ 288*β ∧
      288*α-36*ν+72*g-216*h+1/10000 ≤ 288*β ∧
      648*α-72-216*h-216*ν+1/10000 ≤ 288*β ∧
      24+96*g-216*h+96*α+144*ν+1/10000 ≤ 288*β ∧
      21+87*g-216*h+177*α+33*ν+1/10000 ≤ 288*β ∧
      15+87*g-216*h+207*α+15*ν+1/10000 ≤ 288*β ∧
      12+78*g-216*h+216*α+24*ν+1/10000 ≤ 288*β ∧
      6+78*g-216*h+246*α+6*ν+1/10000 ≤ 288*β ∧
      4+76*g-216*h+268*α-24*ν+1/10000 ≤ 288*β ∧
      72*g-216*h+284*α-24*ν+1/10000 ≤ 288*β ∧
      504*α-72-216*h+72*ν+1/10000 ≤ 288*β := by
  intro α h g₀ ν₀ ν₁ g ν β
  have ht0 := ht.1
  have ht1 := ht.2
  have hu0 := hu.1
  have hu1 := hu.2
  have h00 := mul_nonneg (sub_nonneg.mpr ht1) (sub_nonneg.mpr hu1)
  have h01 := mul_nonneg (sub_nonneg.mpr ht1) hu0
  have h10 := mul_nonneg ht0 (sub_nonneg.mpr hu1)
  have h11 := mul_nonneg ht0 hu0
  dsimp only [α,h,g₀,ν₀,ν₁,g,ν,β]
  repeat' constructor
  all_goals nlinarith only [ht0,ht1,hu0,hu1,h00,h01,h10,h11]


example
    {t u : ℝ} (ht : t∈Icc (0:ℝ) 1) (hu : u∈Icc (0:ℝ) 1) :
    let α := (1-t)*(890/3277)+t*(17604372/60424193)
    let h := ((1-t)*2749411+t*3296917)/100000000
    let g₀ := ((1-t)*16756+t*1976824)/100000000
    let ν₀ := ((1-t)*11931645+t*14567321)/100000000
    let ν₁ := ((1-t)*11969967+t*14925729)/100000000
    let g := (1-u)*g₀+u*(3*h)
    let ν := (1-u)*ν₀+u*ν₁
    let β := 89/3478+(7441/8695)*α
    1/100000 ≤ g₀ ∧ g₀+1/100000 ≤ 3*h ∧ 1/100000 ≤ h ∧
      8*h+1/100000 ≤ α ∧
      2*α+1/2+(3/2)*g₀-3*h+1/100000 ≤ 4*β ∧
      5*α-1/2+g₀/2-3*h+1/100000 ≤ 4*β ∧
      1/100000 ≤ ν ∧ ν+1/100000 ≤ α ∧
      4*α-1-g+1/100000 ≤ ν ∧ ν+3*α+1/100000 ≤ 1+g ∧
      3*α+1/100000 ≤ 1+g ∧ 7*α+1/100000 ≤ 2+2*g+ν ∧
      5*α-1-g+1/100000 ≤ 3*ν ∧
      4*ν+1/100000 ≤ 6*α-1-g ∧
      1+g+1/100000 ≤ 4*α ∧
      1+g+2*ν+1/100000 ≤ 5*α ∧
      3+3*g+11*ν+1/100000 ≤ 17*α ∧
      7+7*g+27*ν+1/100000 ≤ 41*α ∧
      288*α-144*h+1/10000 ≤ 288*β ∧
      288*α-36*ν+72*g-216*h+1/10000 ≤ 288*β ∧
      648*α-72-216*h-216*ν+1/10000 ≤ 288*β ∧
      24+96*g-216*h+96*α+144*ν+1/10000 ≤ 288*β ∧
      21+87*g-216*h+177*α+33*ν+1/10000 ≤ 288*β ∧
      15+87*g-216*h+207*α+15*ν+1/10000 ≤ 288*β ∧
      12+78*g-216*h+216*α+24*ν+1/10000 ≤ 288*β ∧
      6+78*g-216*h+246*α+6*ν+1/10000 ≤ 288*β ∧
      4+76*g-216*h+268*α-24*ν+1/10000 ≤ 288*β ∧
      72*g-216*h+284*α-24*ν+1/10000 ≤ 288*β ∧
      504*α-72-216*h+72*ν+1/10000 ≤ 288*β := by
  exact fourth_pair_capped_terminal_source_window_scales ht hu

#print axioms fourth_pair_capped_terminal_source_window_scales

/-- The actual capped denominator lower bound controls its terminal
physical error by two monomials. This retains the extra M/N-cap contribution,
rather than replacing the cap by N when N squared exceeds M. -/
private theorem capped_terminal_physical_error
    {M N R Q qcap : ℝ}
    (hM : 0 < M) (hN : 0 < N) (hcap : 0 < qcap)
    (hQ : qcap*min N (M/N) ≤ Q) :
    M*R^2/Q^2 ≤ (1/qcap^2)*(M*R^2/N^2+N^2*R^2/M) := by
  have hnum : 0 ≤ M*R^2 := mul_nonneg hM.le (sq_nonneg R)
  rcases le_total N (M/N) with hn | hn
  · rw [min_eq_left hn] at hQ
    calc
      _ ≤ M*R^2/(qcap*N)^2 := div_le_div_of_nonneg_left hnum
        (sq_pos_of_pos (mul_pos hcap hN)) (pow_le_pow_left₀ (mul_pos hcap hN).le hQ 2)
      _ = (1/qcap^2)*(M*R^2/N^2) := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (le_add_of_nonneg_right (by positivity)) (by positivity)
  · rw [min_eq_right hn] at hQ
    calc
      _ ≤ M*R^2/(qcap*(M/N))^2 := div_le_div_of_nonneg_left hnum
        (sq_pos_of_pos (mul_pos hcap (div_pos hM hN)))
        (pow_le_pow_left₀ (mul_pos hcap (div_pos hM hN)).le hQ 2)
      _ = (1/qcap^2)*(N^2*R^2/M) := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (le_add_of_nonneg_left (by positivity)) (by positivity)

example
    {M N R Q qcap : ℝ}
    (hM : 0 < M) (hN : 0 < N) (hcap : 0 < qcap)
    (hQ : qcap*min N (M/N) ≤ Q) :
    M*R^2/Q^2 ≤ (1/qcap^2)*(M*R^2/N^2+N^2*R^2/M) := by
  exact capped_terminal_physical_error hM hN hcap hQ

#print axioms capped_terminal_physical_error

/-- Unchanged existing private scale proof, copied only for scratch access;
promotion reuses its original declaration. -/
private theorem reference_floor_physical_budgets
    {N R Q B L : ℝ} (hR : 1 ≤ R) (hRQ : R ≤ Q) (hQN : Q ≤ N)
    (hNR : N ≤ R^2) (hB : 1 ≤ B) (hL : 1 ≤ L)
    (hlarge : 2*B*L ≤ (N/Q)^((2:ℝ)/3)) :
    let U : ℕ := ⌊(N/Q)^((2:ℝ)/3)/B⌋₊
    1 ≤ U ∧ L ≤ (U:ℝ) ∧
      (N/Q)^((2:ℝ)/3)/(2*B) ≤ (U:ℝ) ∧
      (U:ℝ) ≤ (N/Q)^((2:ℝ)/3)/B ∧
      B^2*(U:ℝ)^3*R^2 ≤ N^2 ∧
      (U:ℝ) ≤ R^2 := by
  intro U
  have hRp : 0 < R := zero_lt_one.trans_le hR
  have hQ : 0 < Q := hRp.trans_le hRQ
  have hN : 0 < N := hQ.trans_le hQN
  have hBp : 0 < B := zero_lt_one.trans_le hB
  let scale := (N/Q)^((2:ℝ)/3)/B
  have hX2L : 2*L ≤ scale := (le_div_iff₀ hBp).mpr (by nlinarith only [hlarge])
  have hX2 : 2 ≤ scale := by linarith only [hX2L,hL]
  have hU : 1 ≤ U := (Nat.one_le_floor_iff scale).mpr (by linarith only [hX2])
  have hUle : (U:ℝ) ≤ scale := Nat.floor_le (by linarith only [hX2])
  have hUlower : scale/2 ≤ (U:ℝ) := by
    have hh := Nat.lt_floor_add_one scale
    change scale < (U:ℝ)+1 at hh
    linarith only [hh,hX2]
  have hUL : L ≤ (U:ℝ) := by linarith only [hX2L,hUlower]
  have hpow : ((N/Q)^((2:ℝ)/3))^3=(N/Q)^2 := by
    rw [←Real.rpow_natCast,←Real.rpow_mul (div_pos hN hQ).le]
    norm_num
  have hcube : B^3*(U:ℝ)^3*Q^2 ≤ N^2 := by
    have hh := mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (Nat.cast_nonneg U) hUle 3)
      (show 0 ≤ B^3*Q^2 by positivity)
    have he : (B^3*Q^2)*scale^3=N^2 := by
      dsimp only [scale]
      rw [div_pow,hpow,div_pow]
      field_simp
    rw [he] at hh
    nlinarith only [hh]
  have hlinear : B*(U:ℝ)*Q ≤ N := by
    have hratio : 1 ≤ N/Q := (one_le_div hQ).mpr hQN
    have hp := Real.rpow_le_self_of_one_le hratio (by norm_num : (2:ℝ)/3 ≤ 1)
    have hh := mul_le_mul_of_nonneg_left hUle hBp.le
    have he : B*scale=(N/Q)^((2:ℝ)/3) := by dsimp only [scale]; field_simp
    rw [he] at hh
    exact (le_div_iff₀ hQ).mp (hh.trans hp)
  have hnowrap : B^2*(U:ℝ)^3*R^2 ≤ N^2 := by
    have hBpow : B^2 ≤ B^3 := by
      have hh := mul_le_mul_of_nonneg_left hB (sq_nonneg B)
      nlinarith only [hh]
    calc
      _ ≤ B^3*(U:ℝ)^3*Q^2 := by gcongr
      _ ≤ _ := hcube
  have hUN : (U:ℝ) ≤ N := by
    calc
      (U:ℝ) = 1*(U:ℝ)*1 := by ring
      _ ≤ B*(U:ℝ)*Q := by gcongr; exact hR.trans hRQ
      _ ≤ N := hlinear
  refine ⟨hU,hUL,?_,hUle,hnowrap,hUN.trans hNR⟩
  convert hUlower using 1
  dsimp only [scale]
  ring

example
    {N R Q B L : ℝ} (hR : 1 ≤ R) (hRQ : R ≤ Q) (hQN : Q ≤ N)
    (hNR : N ≤ R^2) (hB : 1 ≤ B) (hL : 1 ≤ L)
    (hlarge : 2*B*L ≤ (N/Q)^((2:ℝ)/3)) :
    let U : ℕ := ⌊(N/Q)^((2:ℝ)/3)/B⌋₊
    1 ≤ U ∧ L ≤ (U:ℝ) ∧
      (N/Q)^((2:ℝ)/3)/(2*B) ≤ (U:ℝ) ∧
      (U:ℝ) ≤ (N/Q)^((2:ℝ)/3)/B ∧
      B^2*(U:ℝ)^3*R^2 ≤ N^2 ∧
      (U:ℝ) ≤ R^2 := by
  exact reference_floor_physical_budgets hR hRQ hQN hNR hB hL hlarge

#print axioms reference_floor_physical_budgets

/-- Unchanged existing private scale proof, copied only for scratch access;
promotion reuses its original declaration. -/
private theorem dyadic_band_integer_physical_selection
    (N : ℕ) {σ J R B L Cbase qcap Dcap : ℝ}
    (hσ : 0 < σ) (hR : 1 ≤ R) (hRN : R ≤ N) (hNR : (N:ℝ) ≤ R^2)
    (hB : 1 ≤ B) (hL : 1 ≤ L) (hCbase : 768 ≤ Cbase)
    (hcap : 0 < qcap) (hcapOne : qcap ≤ 1)
    (hlarge : qcap*(2*B*L)^((3:ℝ)/2) ≤ 1)
    (hDcap : 0 ≤ Dcap) (hsmall : 4*Dcap*qcap ≤ 1)
    (hroom : 2*Cbase*R ≤ qcap*(N:ℝ)) :
    ∃ (Qbase kmax : ℕ) (Kmesh Usel : ℕ → ℕ),
      let Q := fun k : ℕ => Qbase*2^k
      Cbase*R ≤ Qbase ∧ (Qbase:ℝ) ≤ 2*Cbase*R ∧
      qcap*(N:ℝ)/2 ≤ Q kmax ∧ (Q kmax:ℝ) ≤ qcap*(N:ℝ) ∧
      (kmax:ℝ) ≤ Real.log N/Real.log 2 ∧
      (∀ k, 0 < Kmesh k) ∧
      (∀ k ≤ kmax,
        L ≤ (Usel k:ℝ) ∧
        63*(J/(2*σ*(N:ℝ)*R^2))*(Q k:ℝ)*(N:ℝ)^2 ≤ Kmesh k ∧
        (Q k:ℝ)*(N:ℝ) ≤ (Kmesh k:ℝ)*R^2 ∧
        (Kmesh k:ℝ) ≤ 2*(max 1 (63*J/(2*σ)))*(Q k:ℝ)*(N:ℝ)/R^2 ∧
        1 ≤ Usel k ∧
        B^2*(Usel k:ℝ)^3*R^2 ≤ (N:ℝ)^2 ∧
        (Usel k:ℝ) ≤ ((N:ℝ)/(Q k:ℝ))^((2:ℝ)/3)/B ∧
        ((N:ℝ)/(Q k:ℝ))^((2:ℝ)/3)/(2*B) ≤ (Usel k:ℝ) ∧
        Q k ≤ N ∧ (Usel k:ℝ) ≤ R^2 ∧
        768*R ≤ (Q k:ℝ) ∧ 2*R^2 ≤ (Q k:ℝ)*(N:ℝ) ∧
        Dcap*(Q k:ℝ)/(N:ℝ) ≤ 1/4) ∧
      (∀ k, Usel k ≤ Usel 0) := by
  classical
  have hRp : 0 < R := zero_lt_one.trans_le hR
  have hNp : (0:ℝ) < N := hRp.trans_le hRN
  have hCp : 0 < Cbase := by linarith only [hCbase]
  have hCR : 1 ≤ Cbase*R := by nlinarith only [hCbase,hR]
  let Qbase : ℕ := ⌈Cbase*R⌉₊
  have hQlo : Cbase*R ≤ (Qbase:ℝ) := Nat.le_ceil _
  have hQhi : (Qbase:ℝ) ≤ 2*Cbase*R := by
    have hh := Nat.ceil_lt_add_one (mul_pos hCp hRp).le
    change (Qbase:ℝ) < Cbase*R+1 at hh
    linarith only [hh,hCR]
  have hQp : (0:ℝ) < Qbase := (mul_pos hCp hRp).trans_le hQlo
  have hratio : 1 ≤ qcap*(N:ℝ)/(Qbase:ℝ) :=
    (le_div_iff₀ hQp).mpr (by simpa only [one_mul] using hQhi.trans hroom)
  obtain ⟨kmax,hklo,hkhi⟩ := exists_nat_pow_near hratio (by norm_num : (1:ℝ) < 2)
  let Q := fun k : ℕ => Qbase*2^k
  have hQcast k : (Q k:ℝ)=(Qbase:ℝ)*(2:ℝ)^k := by simp only [Q,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat]
  have hQbase k : (Qbase:ℝ) ≤ Q k := by
    rw [hQcast]
    exact le_mul_of_one_le_right hQp.le (one_le_pow₀ (by norm_num))
  have hQpos k : (0:ℝ) < Q k := hQp.trans_le (hQbase k)
  have hQupper : (Q kmax:ℝ) ≤ qcap*(N:ℝ) := by
    rw [hQcast]
    have hh := (le_div_iff₀ hQp).mp hklo
    simpa only [mul_comm] using hh
  have hQlower : qcap*(N:ℝ)/2 ≤ Q kmax := by
    have hh := (div_lt_iff₀ hQp).mp hkhi
    rw [pow_succ] at hh
    rw [hQcast]
    nlinarith only [hh]
  have hQmono k (hk : k ≤ kmax) : Q k ≤ Q kmax := by
    exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by decide) hk)
  have hQN k (hk : k ≤ kmax) : Q k ≤ N := by
    have hh : (Q k:ℝ) ≤ N :=
      (by exact_mod_cast hQmono k hk : (Q k:ℝ) ≤ Q kmax).trans (hQupper.trans (by
        simpa only [one_mul] using mul_le_mul_of_nonneg_right hcapOne hNp.le))
    exact_mod_cast hh
  have hstrong k : 768*R ≤ (Q k:ℝ) :=
    (mul_le_mul_of_nonneg_right hCbase hRp.le).trans (hQlo.trans (hQbase k))
  have hRQ k : R ≤ (Q k:ℝ) := by
    have hh := hstrong k
    linarith only [hh,hRp]
  have hminscale k : 2*R^2 ≤ (Q k:ℝ)*(N:ℝ) := by
    have hh := mul_le_mul (hstrong k) hRN hRp.le (hQpos k).le
    nlinarith only [hh,sq_nonneg R]
  have hmesh k := exists_positive_difference_source_fourier_mesh
    (J:=J) hσ hNp hRp (hQpos k) (by
      have hh := hminscale k
      linarith only [hh,sq_nonneg R])
  choose Kmesh hK hSource hMesh hMeshUpper using hmesh
  let Usel := fun k => ⌊((N:ℝ)/(Q k:ℝ))^((2:ℝ)/3)/B⌋₊
  have hUdata k (hk : k ≤ kmax) :=
    reference_floor_physical_budgets (N:=(N:ℝ)) (B:=B) (L:=L)
      hR (hRQ k) (by exact_mod_cast hQN k hk) hNR hB hL (by
        have hqcap : (Q k:ℝ) ≤ qcap*(N:ℝ) :=
          (by exact_mod_cast hQmono k hk : (Q k:ℝ) ≤ Q kmax).trans hQupper
        have hratioLower : 1/qcap ≤ (N:ℝ)/(Q k:ℝ) := by
          apply (div_le_div_iff₀ hcap (hQpos k)).mpr
          nlinarith only [hqcap]
        have hpowle : (2*B*L)^((3:ℝ)/2) ≤ (N:ℝ)/(Q k:ℝ) :=
          ((le_div_iff₀ hcap).mpr (by nlinarith only [hlarge])).trans hratioLower
        have hh := (Real.le_rpow_inv_iff_of_pos
          (by positivity : (0:ℝ) ≤ 2*B*L)
          (div_pos hNp (hQpos k)).le (by norm_num : (0:ℝ) < 3/2)).mpr hpowle
        norm_num only [show ((3:ℝ)/2)⁻¹=2/3 by norm_num] at hh
        exact hh)
  have hUmono k : Usel k ≤ Usel 0 := by
    apply Nat.floor_mono
    apply div_le_div_of_nonneg_right _ (zero_le_one.trans hB)
    apply Real.rpow_le_rpow (by positivity) _ (by norm_num)
    apply div_le_div_of_nonneg_left hNp.le (hQpos 0)
    simpa only [Q,pow_zero,mul_one] using hQbase k
  have hklog : (kmax:ℝ) ≤ Real.log N/Real.log 2 := by
    have hQone : (1:ℝ) ≤ Qbase := hCR.trans hQlo
    have hpowN : (2:ℝ)^kmax ≤ N := by
      have hh : (2:ℝ)^kmax ≤ (Q kmax:ℝ) := by
        rw [hQcast]
        exact le_mul_of_one_le_left (by positivity) hQone
      exact hh.trans (by exact_mod_cast hQN kmax le_rfl)
    have hh := Real.log_le_log (by positivity : (0:ℝ) < (2:ℝ)^kmax) hpowN
    rw [Real.log_pow] at hh
    exact (le_div_iff₀ (Real.log_pos (by norm_num : (1:ℝ) < 2))).mpr hh
  refine ⟨Qbase,kmax,Kmesh,Usel,hQlo,hQhi,hQlower,hQupper,hklog,hK,?_,hUmono⟩
  intro k hk
  obtain ⟨hU,hUL,hUlower,hUupper,hwrap,hUR⟩ := hUdata k hk
  refine ⟨hUL,hSource k,hMesh k,hMeshUpper k,hU,hwrap,hUupper,hUlower,
    hQN k hk,hUR,hstrong k,hminscale k,?_⟩
  have hqcap : (Q k:ℝ) ≤ qcap*(N:ℝ) :=
    (by exact_mod_cast hQmono k hk : (Q k:ℝ) ≤ Q kmax).trans hQupper
  apply (div_le_iff₀ hNp).mpr
  have hh := mul_le_mul_of_nonneg_left hqcap hDcap
  have hs := mul_le_mul_of_nonneg_right hsmall hNp.le
  nlinarith only [hh,hs]

example
    (N : ℕ) {σ J R B L Cbase qcap Dcap : ℝ}
    (hσ : 0 < σ) (hR : 1 ≤ R) (hRN : R ≤ N) (hNR : (N:ℝ) ≤ R^2)
    (hB : 1 ≤ B) (hL : 1 ≤ L) (hCbase : 768 ≤ Cbase)
    (hcap : 0 < qcap) (hcapOne : qcap ≤ 1)
    (hlarge : qcap*(2*B*L)^((3:ℝ)/2) ≤ 1)
    (hDcap : 0 ≤ Dcap) (hsmall : 4*Dcap*qcap ≤ 1)
    (hroom : 2*Cbase*R ≤ qcap*(N:ℝ)) :
    ∃ (Qbase kmax : ℕ) (Kmesh Usel : ℕ → ℕ),
      let Q := fun k : ℕ => Qbase*2^k
      Cbase*R ≤ Qbase ∧ (Qbase:ℝ) ≤ 2*Cbase*R ∧
      qcap*(N:ℝ)/2 ≤ Q kmax ∧ (Q kmax:ℝ) ≤ qcap*(N:ℝ) ∧
      (kmax:ℝ) ≤ Real.log N/Real.log 2 ∧
      (∀ k, 0 < Kmesh k) ∧
      (∀ k ≤ kmax,
        L ≤ (Usel k:ℝ) ∧
        63*(J/(2*σ*(N:ℝ)*R^2))*(Q k:ℝ)*(N:ℝ)^2 ≤ Kmesh k ∧
        (Q k:ℝ)*(N:ℝ) ≤ (Kmesh k:ℝ)*R^2 ∧
        (Kmesh k:ℝ) ≤ 2*(max 1 (63*J/(2*σ)))*(Q k:ℝ)*(N:ℝ)/R^2 ∧
        1 ≤ Usel k ∧
        B^2*(Usel k:ℝ)^3*R^2 ≤ (N:ℝ)^2 ∧
        (Usel k:ℝ) ≤ ((N:ℝ)/(Q k:ℝ))^((2:ℝ)/3)/B ∧
        ((N:ℝ)/(Q k:ℝ))^((2:ℝ)/3)/(2*B) ≤ (Usel k:ℝ) ∧
        Q k ≤ N ∧ (Usel k:ℝ) ≤ R^2 ∧
        768*R ≤ (Q k:ℝ) ∧ 2*R^2 ≤ (Q k:ℝ)*(N:ℝ) ∧
        Dcap*(Q k:ℝ)/(N:ℝ) ≤ 1/4) ∧
      (∀ k, Usel k ≤ Usel 0) := by
  exact dyadic_band_integer_physical_selection N hσ hR hRN hNR hB hL hCbase hcap hcapOne hlarge hDcap hsmall hroom

#print axioms dyadic_band_integer_physical_selection

/-- Reuse the actual integer dyadic selector with the effective cap
qcap*min(1,M/N^2). It constructs all Fourier meshes and reference cutoffs,
retains their original budgets, and derives N*Qmax <= M and BOTH terminal
error monomials from the SAME selected terminal denominator. -/
private theorem capped_dyadic_band_integer_physical_selection
    (N : ℕ) {σ J M R B L Cbase qcap Dcap : ℝ}
    (hσ : 0 < σ) (hM : 0 < M) (hR : 1 ≤ R) (hRN : R ≤ N) (hNR : (N:ℝ) ≤ R^2)
    (hB : 1 ≤ B) (hL : 1 ≤ L) (hCbase : 768 ≤ Cbase)
    (hcap : 0 < qcap) (hcapOne : qcap ≤ 1)
    (hlarge : qcap*(2*B*L)^((3:ℝ)/2) ≤ 1)
    (hDcap : 0 ≤ Dcap) (hsmall : 4*Dcap*qcap ≤ 1)
    (hroom : 2*Cbase*R ≤ qcap*min (N:ℝ) (M/(N:ℝ))) :
    ∃ (Qbase kmax : ℕ) (Kmesh Usel : ℕ → ℕ),
      let Q := fun k : ℕ => Qbase*2^k
      Cbase*R ≤ Qbase ∧ (Qbase:ℝ) ≤ 2*Cbase*R ∧
      qcap*min (N:ℝ) (M/(N:ℝ))/2 ≤ Q kmax ∧
      (Q kmax:ℝ) ≤ qcap*min (N:ℝ) (M/(N:ℝ)) ∧
      (N:ℝ)*(Q kmax:ℝ) ≤ M ∧
      M*R^2/(Q kmax:ℝ)^2 ≤ (4/qcap^2)*
        (M*R^2/(N:ℝ)^2+(N:ℝ)^2*R^2/M) ∧
      (kmax:ℝ) ≤ Real.log N/Real.log 2 ∧
      (∀ k, 0 < Kmesh k) ∧
      (∀ k ≤ kmax,
        L ≤ (Usel k:ℝ) ∧
        63*(J/(2*σ*(N:ℝ)*R^2))*(Q k:ℝ)*(N:ℝ)^2 ≤ Kmesh k ∧
        (Q k:ℝ)*(N:ℝ) ≤ (Kmesh k:ℝ)*R^2 ∧
        (Kmesh k:ℝ) ≤ 2*(max 1 (63*J/(2*σ)))*(Q k:ℝ)*(N:ℝ)/R^2 ∧
        1 ≤ Usel k ∧
        B^2*(Usel k:ℝ)^3*R^2 ≤ (N:ℝ)^2 ∧
        (Usel k:ℝ) ≤ ((N:ℝ)/(Q k:ℝ))^((2:ℝ)/3)/B ∧
        ((N:ℝ)/(Q k:ℝ))^((2:ℝ)/3)/(2*B) ≤ (Usel k:ℝ) ∧
        Q k ≤ N ∧ (Usel k:ℝ) ≤ R^2 ∧
        768*R ≤ (Q k:ℝ) ∧ 2*R^2 ≤ (Q k:ℝ)*(N:ℝ) ∧
        Dcap*(Q k:ℝ)/(N:ℝ) ≤ 1/4) ∧
      (∀ k, Usel k ≤ Usel 0) := by
  have hNp : (0:ℝ) < N := (zero_lt_one.trans_le hR).trans_le hRN
  let qcap' := qcap*min 1 (M/(N:ℝ)^2)
  have hp : 0 < qcap' := mul_pos hcap (lt_min (by norm_num) (div_pos hM (sq_pos_of_pos hNp)))
  have hle : qcap' ≤ qcap := by
    calc
      _ ≤ qcap*1 := mul_le_mul_of_nonneg_left (min_le_left _ _) hcap.le
      _ = qcap := mul_one _
  have hid : qcap'*(N:ℝ)=qcap*min (N:ℝ) (M/(N:ℝ)) := by
    dsimp only [qcap']
    rw [mul_assoc,min_mul_of_nonneg _ _ hNp.le,one_mul]
    have he : (M/(N:ℝ)^2)*(N:ℝ)=M/(N:ℝ) := by field_simp
    rw [he]
  have hlarge' : qcap'*(2*B*L)^((3:ℝ)/2) ≤ 1 :=
    (mul_le_mul_of_nonneg_right hle (Real.rpow_nonneg (by positivity) _)).trans hlarge
  have hsmall' : 4*Dcap*qcap' ≤ 1 :=
    (mul_le_mul_of_nonneg_left hle (by positivity)).trans hsmall
  have hroom' : 2*Cbase*R ≤ qcap'*(N:ℝ) := by rw [hid]; exact hroom
  obtain ⟨Qbase,kmax,Kmesh,Usel,hlo,hhi,hqlo,hqhi,hlog,hK,hbudgets,hmono⟩ :=
    dyadic_band_integer_physical_selection N (J:=J) hσ hR hRN hNR hB hL hCbase hp
      (hle.trans hcapOne) hlarge' hDcap hsmall' hroom'
  let Q := fun k : ℕ => Qbase*2^k
  have hlow : qcap*min (N:ℝ) (M/(N:ℝ))/2 ≤ (Q kmax:ℝ) := by
    simpa only [hid] using hqlo
  have hupp : (Q kmax:ℝ) ≤ qcap*min (N:ℝ) (M/(N:ℝ)) := by
    simpa only [hid] using hqhi
  have hmax : (Q kmax:ℝ) ≤ M/(N:ℝ) := by
    calc
      _ ≤ qcap*min (N:ℝ) (M/(N:ℝ)) := hupp
      _ ≤ 1*min (N:ℝ) (M/(N:ℝ)) := mul_le_mul_of_nonneg_right hcapOne
        (le_min hNp.le (div_pos hM hNp).le)
      _ ≤ M/(N:ℝ) := by simpa only [one_mul] using min_le_right (N:ℝ) (M/(N:ℝ))
  have hNQ : (N:ℝ)*(Q kmax:ℝ) ≤ M := by
    have hh := (le_div_iff₀ hNp).mp hmax
    simpa only [mul_comm] using hh
  have herror : M*R^2/(Q kmax:ℝ)^2 ≤ (4/qcap^2)*
      (M*R^2/(N:ℝ)^2+(N:ℝ)^2*R^2/M) := by
    have hh := capped_terminal_physical_error (R:=R) hM hNp (show 0 < qcap/2 by positivity)
      (show (qcap/2)*min (N:ℝ) (M/(N:ℝ)) ≤ (Q kmax:ℝ) from
        (by simpa only [div_mul_eq_mul_div] using hlow))
    convert hh using 1
    congr 1
    field_simp
    norm_num
  exact ⟨Qbase,kmax,Kmesh,Usel,hlo,hhi,hlow,hupp,hNQ,herror,hlog,hK,hbudgets,hmono⟩

example
    (N : ℕ) {σ J M R B L Cbase qcap Dcap : ℝ}
    (hσ : 0 < σ) (hM : 0 < M) (hR : 1 ≤ R) (hRN : R ≤ N) (hNR : (N:ℝ) ≤ R^2)
    (hB : 1 ≤ B) (hL : 1 ≤ L) (hCbase : 768 ≤ Cbase)
    (hcap : 0 < qcap) (hcapOne : qcap ≤ 1)
    (hlarge : qcap*(2*B*L)^((3:ℝ)/2) ≤ 1)
    (hDcap : 0 ≤ Dcap) (hsmall : 4*Dcap*qcap ≤ 1)
    (hroom : 2*Cbase*R ≤ qcap*min (N:ℝ) (M/(N:ℝ))) :
    ∃ (Qbase kmax : ℕ) (Kmesh Usel : ℕ → ℕ),
      let Q := fun k : ℕ => Qbase*2^k
      Cbase*R ≤ Qbase ∧ (Qbase:ℝ) ≤ 2*Cbase*R ∧
      qcap*min (N:ℝ) (M/(N:ℝ))/2 ≤ Q kmax ∧
      (Q kmax:ℝ) ≤ qcap*min (N:ℝ) (M/(N:ℝ)) ∧
      (N:ℝ)*(Q kmax:ℝ) ≤ M ∧
      M*R^2/(Q kmax:ℝ)^2 ≤ (4/qcap^2)*
        (M*R^2/(N:ℝ)^2+(N:ℝ)^2*R^2/M) ∧
      (kmax:ℝ) ≤ Real.log N/Real.log 2 ∧
      (∀ k, 0 < Kmesh k) ∧
      (∀ k ≤ kmax,
        L ≤ (Usel k:ℝ) ∧
        63*(J/(2*σ*(N:ℝ)*R^2))*(Q k:ℝ)*(N:ℝ)^2 ≤ Kmesh k ∧
        (Q k:ℝ)*(N:ℝ) ≤ (Kmesh k:ℝ)*R^2 ∧
        (Kmesh k:ℝ) ≤ 2*(max 1 (63*J/(2*σ)))*(Q k:ℝ)*(N:ℝ)/R^2 ∧
        1 ≤ Usel k ∧
        B^2*(Usel k:ℝ)^3*R^2 ≤ (N:ℝ)^2 ∧
        (Usel k:ℝ) ≤ ((N:ℝ)/(Q k:ℝ))^((2:ℝ)/3)/B ∧
        ((N:ℝ)/(Q k:ℝ))^((2:ℝ)/3)/(2*B) ≤ (Usel k:ℝ) ∧
        Q k ≤ N ∧ (Usel k:ℝ) ≤ R^2 ∧
        768*R ≤ (Q k:ℝ) ∧ 2*R^2 ≤ (Q k:ℝ)*(N:ℝ) ∧
        Dcap*(Q k:ℝ)/(N:ℝ) ≤ 1/4) ∧
      (∀ k, Usel k ≤ Usel 0) := by
  exact capped_dyadic_band_integer_physical_selection N hσ hM hR hRN hNR hB hL hCbase hcap hcapOne hlarge hDcap hsmall hroom

#print axioms capped_dyadic_band_integer_physical_selection

/-- Actual double-difference chunks choose SAME-phase two-probe least
bands on the fine n-grid. Their roots, occupied bands and terminal counts
are derived from the existing source factory and summed over actual phases. -/
private theorem double_difference_chunk_grid_dyadic_bands
    (Chunks : Finset (ℝ × ℤ)) (Y : Finset ℝ) (F rshift sshift : ℝ → ℝ)
    (n N Qbase kmax : ℕ) (hNlink : N=8*n)
    {c U d w T M R : ℝ}
    (hc : 0 < c) (hU : 0 < U)
    (hn : 0 < n) (hd : 0 < d) (hw : w ≤ 1/4) (hsmall : 2*U*w ≤ c/64)
    (hshifts : ∀ y∈Y, 0 ≤ rshift y ∧ 0 ≤ sshift y ∧
      rshift y*sshift y=d*y ∧ rshift y+sshift y ≤ w)
    (hy : ∀ y∈Y, y∈Icc (1:ℝ) 2) (hphase : ∀ p∈Chunks, p.1∈Y)
    (hT : 0 < T) (hM : 0 < M) (hR : 0 < R)
    (hreg : ∀ w, 0 < w → ContDiffAt ℝ ∞ F w)
    (hbound : ∀ u∈Icc (1/2:ℝ) 3, ∀ j, 1 ≤ j → j ≤ 7 → |iteratedDeriv j F u| ≤ U)
    (hlower : ∀ u∈Icc (1/2:ℝ) 3, c ≤ iteratedDeriv 5 F u)
    (hnegative : ∀ w∈Icc (1/2:ℝ) 3, iteratedDeriv 4 F w ≤ -c)
    (hscale : T*(N:ℝ)*R^2=M^3)
    (hQbase : 768 ≤ Qbase)
    (hQmax : (N:ℝ)*(Qbase*2^kmax:ℕ) ≤ M) :
    let f := fun y v => T*((F (v/M)-F (v/M+rshift y)-F (v/M+sshift y)+
      F (v/M+rshift y+sshift y))/d)
    let h := fun y w => iteratedDeriv 2 (f y) w/2
    let probe := fun (p : ℝ × ℤ) (i : Fin 2) =>
      if i=0 then (n:ℝ)*p.2-2*(N:ℝ) else (n:ℝ)*p.2-11*(N:ℝ)/4
    (∀ p∈Chunks, ∀ i, probe p i∈Icc (M+(N:ℝ)/4) (2*M-(N:ℝ)/4)) →
    let Q := fun k : ℕ => Qbase*2^k
    let Ctail := 4*U*(64/c)^2+192/c
    let Clow := (2*U+c/32)*(3072/c)^2+3072/c
    let Cerror := (768:ℝ)^2*Ctail+Clow
    let Density := fun k => 128*Cerror*(M*R^2/((N:ℝ)*(Q k:ℝ)^2))*
      (2+Real.log (512*R^2/(c*((Q k:ℝ)/768))+1))
    ∃ (anchor : (ℝ × ℤ) → Fin 2 → ℚ)
      (band : (ℝ × ℤ) → Option ℕ) (za : (ℝ × ℤ) → Fin 2 → ℝ),
      (∀ p∈Chunks, ∀ i,
        h p.1 (za p i)=(anchor p i:ℝ) ∧
        |za p i-probe p i| ≤ (N:ℝ)/16 ∧ za p i∈Icc M (2*M)) ∧
      (∀ p∈Chunks, match band p with
        | none => ∃ i, ¬(768*(anchor p i).den ≤ Q kmax ∧
            24576*R^2 ≤ c*(Q kmax:ℝ)*(anchor p i).den)
        | some k => k ≤ kmax ∧
            (∀ i, 768*(anchor p i).den ≤ Q k ∧
              24576*R^2 ≤ c*(Q k:ℝ)*(anchor p i).den)) ∧
      (∀ k ≤ kmax, ((Chunks.filter (fun p => band p=some (k+1))).card:ℝ) ≤
        (Y.card:ℝ)*Density k) ∧
      ((Chunks.filter (fun p => band p=none)).card:ℝ) ≤
        (Y.card:ℝ)*Density kmax := by
  classical
  intro f h probe hpoints Q Ctail Clow Cerror Density
  have hnp : (0:ℝ) < n := Nat.cast_pos.mpr hn
  have hNreal : (N:ℝ)=8*(n:ℝ) := by exact_mod_cast hNlink
  have hnN : (n:ℝ) ≤ N := by rw [hNreal]; linarith only [hnp]
  let Rfine := Real.sqrt 8*R
  have hRfine : 0 < Rfine := mul_pos (Real.sqrt_pos.mpr (by norm_num)) hR
  have hRsq : Rfine^2=8*R^2 := by
    dsimp only [Rfine]
    rw [mul_pow,Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 8)]
  have hscaleFine : T*(n:ℝ)*Rfine^2=M^3 := by
    rw [hRsq]
    rw [hNreal] at hscale
    nlinarith only [hscale]
  have hQfine : (n:ℝ)*(Qbase*2^kmax:ℕ) ≤ M :=
    (mul_le_mul_of_nonneg_right hnN (Nat.cast_nonneg _)).trans hQmax
  let Sy := fun y => (Chunks.filter (fun p => p.1=y)).image Prod.snd
  have hSy y j : j∈Sy y ↔ (y,j)∈Chunks := by
    constructor
    · intro hj
      obtain ⟨p,hp,hpj⟩ := Finset.mem_image.mp hj
      have heq : p=(y,j) := Prod.ext (Finset.mem_filter.mp hp).2 hpj
      exact heq ▸ (Finset.mem_filter.mp hp).1
    · intro hj
      exact Finset.mem_image.mpr ⟨(y,j),Finset.mem_filter.mpr ⟨hj,rfl⟩,rfl⟩
  let base := fun i : Fin 2 => if i=0 then -2*(N:ℝ) else -11*(N:ℝ)/4
  have hprobe y j i : base i+(n:ℝ)*j=probe (y,j) i := by
    dsimp only [base,probe]
    split_ifs <;> ring
  let FineDensity := fun k => 2*Cerror*(M*Rfine^2/((n:ℝ)*(Q k:ℝ)^2))*
    (2+Real.log (64*Rfine^2/(c*((Q k:ℝ)/768))+1))
  have hDensity k : FineDensity k=Density k := by
    dsimp only [FineDensity,Density]
    rw [hRsq,hNreal]
    have he : 64*(8*R^2)=512*R^2 := by ring
    rw [he]
    ring
  have hex (y : ℝ) : ∃ (a : ℤ → Fin 2 → ℚ) (b : ℤ → Option ℕ)
      (z : ℤ → Fin 2 → ℝ), y∈Y →
      (∀ j∈Sy y, ∀ i, h y (z j i)=(a j i:ℝ) ∧
        |z j i-probe (y,j) i| ≤ (N:ℝ)/16 ∧ z j i∈Icc M (2*M)) ∧
      (∀ j∈Sy y, match b j with
        | none => ∃ i, ¬(768*(a j i).den ≤ Q kmax ∧
            24576*R^2 ≤ c*(Q kmax:ℝ)*(a j i).den)
        | some k => k ≤ kmax ∧
            (∀ i, 768*(a j i).den ≤ Q k ∧
              24576*R^2 ≤ c*(Q k:ℝ)*(a j i).den)) ∧
      (∀ k ≤ kmax, (((Sy y).filter (fun j => b j=some (k+1))).card:ℝ) ≤ Density k) ∧
      (((Sy y).filter (fun j => b j=none)).card:ℝ) ≤ Density kmax := by
    by_cases hyY : y∈Y
    · have hpointsFine j (hj : j∈Sy y) i :
          base i+(n:ℝ)*j∈Icc (M+(n:ℝ)/4) (2*M-(n:ℝ)/4) := by
        rw [hprobe y j i]
        have hh := hpoints (y,j) ((hSy y j).mp hj) i
        constructor <;> linarith only [hh.1,hh.2,hnN]
      obtain ⟨a,b,z,_hminimal,hroots,hband,_htransfer,hcounts,htail⟩ :=
        double_difference_two_probe_dyadic_quadratic_density (Sy y) F n Qbase kmax 768 base 3072
          (hshifts y hyY).1 (hshifts y hyY).2.1 hd (hy y hyY)
          (hshifts y hyY).2.2.1 (hshifts y hyY).2.2.2 hw hsmall
          hc hU hT hM hn hRfine hscaleFine hreg hlower hbound hnegative
          (by norm_num) hQbase (by norm_num) hpointsFine hQfine
      refine ⟨a,b,z,fun _ => ⟨?_,?_,?_,?_⟩⟩
      · intro j hj i
        have hh := hroots j hj i
        change h y (z j i)=(a j i:ℝ) ∧
          |z j i-(base i+(n:ℝ)*j)| ≤ (n:ℝ)/16 ∧ z j i∈Icc M (2*M) at hh
        rw [hprobe y j i] at hh
        exact ⟨hh.1,hh.2.1.trans (div_le_div_of_nonneg_right hnN (by norm_num)),hh.2.2⟩
      · intro j _hj
        have hh := hband j
        have hB : (3072:ℝ)*Rfine^2=24576*R^2 := by rw [hRsq]; ring
        dsimp only at hh
        rw [hB] at hh
        cases hb : b j with
        | none => simpa only [hb] using hh
        | some k =>
          rw [hb] at hh
          exact ⟨hh.1,hh.2.1⟩
      · intro k hk
        have hh := hcounts k hk
        change _ ≤ FineDensity k at hh
        exact hh.trans_eq (hDensity k)
      · change _ ≤ FineDensity kmax at htail
        exact htail.trans_eq (hDensity kmax)
    · exact ⟨fun _ _ => 0,fun _ => none,fun _ _ => 0,fun hh => (hyY hh).elim⟩
  choose a b z hdata using hex
  let anchor := fun p : ℝ × ℤ => a p.1 p.2
  let band := fun p : ℝ × ℤ => b p.1 p.2
  let za := fun p : ℝ × ℤ => z p.1 p.2
  have hcount (label : Option ℕ) (Bound : ℝ)
      (hlocal : ∀ y∈Y, (((Sy y).filter (fun j => b y j=label)).card:ℝ) ≤ Bound) :
      ((Chunks.filter (fun p => band p=label)).card:ℝ) ≤ (Y.card:ℝ)*Bound := by
    let E := Chunks.filter (fun p => band p=label)
    let Ey := fun y => (E.filter (fun p => p.1=y)).image Prod.snd
    have hEq y : Ey y=(Sy y).filter (fun j => b y j=label) := by
      ext j
      constructor
      · intro hj
        obtain ⟨p,hp,hpj⟩ := Finset.mem_image.mp hj
        obtain ⟨hpE,hpy⟩ := Finset.mem_filter.mp hp
        obtain ⟨hpC,hpb⟩ := Finset.mem_filter.mp hpE
        have heq : p=(y,j) := Prod.ext hpy hpj
        subst p
        exact Finset.mem_filter.mpr ⟨(hSy y j).mpr hpC,hpb⟩
      · intro hj
        obtain ⟨hjS,hjb⟩ := Finset.mem_filter.mp hj
        exact Finset.mem_image.mpr ⟨(y,j),
          Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨(hSy y j).mp hjS,hjb⟩,rfl⟩,rfl⟩
    have hcard y : (Ey y).card=(E.filter (fun p => p.1=y)).card := by
      apply Finset.card_image_of_injOn
      intro p hp q hq hpq
      exact Prod.ext ((Finset.mem_filter.mp hp).2.trans
        (Finset.mem_filter.mp hq).2.symm) hpq
    have hmaps : ∀ p∈E, p.1∈Y := fun p hp => hphase p (Finset.mem_filter.mp hp).1
    have hsum : (∑ y∈Y,((Ey y).card:ℝ))=E.card := by
      simp_rw [hcard]
      have hh := Finset.sum_fiberwise_of_maps_to hmaps (fun _ => (1:ℝ))
      simpa only [Finset.sum_const,nsmul_eq_mul,mul_one] using hh
    change (E.card:ℝ) ≤ _
    rw [←hsum]
    calc
      _ ≤ ∑ _y∈Y,Bound := Finset.sum_le_sum (fun y hyY => by rw [hEq]; exact hlocal y hyY)
      _ = _ := by simp only [Finset.sum_const,nsmul_eq_mul]
  refine ⟨anchor,band,za,?_,?_,?_,?_⟩
  · intro p hp i
    exact (hdata p.1 (hphase p hp)).1 p.2 ((hSy p.1 p.2).mpr hp) i
  · intro p hp
    exact (hdata p.1 (hphase p hp)).2.1 p.2 ((hSy p.1 p.2).mpr hp)
  · intro k hk
    exact hcount (some (k+1)) (Density k) (fun y hyY => (hdata y hyY).2.2.1 k hk)
  · exact hcount none (Density kmax) (fun y hyY => (hdata y hyY).2.2.2)

example
    (Chunks : Finset (ℝ × ℤ)) (Y : Finset ℝ) (F rshift sshift : ℝ → ℝ)
    (n N Qbase kmax : ℕ) (hNlink : N=8*n)
    {c U d w T M R : ℝ}
    (hc : 0 < c) (hU : 0 < U)
    (hn : 0 < n) (hd : 0 < d) (hw : w ≤ 1/4) (hsmall : 2*U*w ≤ c/64)
    (hshifts : ∀ y∈Y, 0 ≤ rshift y ∧ 0 ≤ sshift y ∧
      rshift y*sshift y=d*y ∧ rshift y+sshift y ≤ w)
    (hy : ∀ y∈Y, y∈Icc (1:ℝ) 2) (hphase : ∀ p∈Chunks, p.1∈Y)
    (hT : 0 < T) (hM : 0 < M) (hR : 0 < R)
    (hreg : ∀ w, 0 < w → ContDiffAt ℝ ∞ F w)
    (hbound : ∀ u∈Icc (1/2:ℝ) 3, ∀ j, 1 ≤ j → j ≤ 7 → |iteratedDeriv j F u| ≤ U)
    (hlower : ∀ u∈Icc (1/2:ℝ) 3, c ≤ iteratedDeriv 5 F u)
    (hnegative : ∀ w∈Icc (1/2:ℝ) 3, iteratedDeriv 4 F w ≤ -c)
    (hscale : T*(N:ℝ)*R^2=M^3)
    (hQbase : 768 ≤ Qbase)
    (hQmax : (N:ℝ)*(Qbase*2^kmax:ℕ) ≤ M) :
    let f := fun y v => T*((F (v/M)-F (v/M+rshift y)-F (v/M+sshift y)+
      F (v/M+rshift y+sshift y))/d)
    let h := fun y w => iteratedDeriv 2 (f y) w/2
    let probe := fun (p : ℝ × ℤ) (i : Fin 2) =>
      if i=0 then (n:ℝ)*p.2-2*(N:ℝ) else (n:ℝ)*p.2-11*(N:ℝ)/4
    (∀ p∈Chunks, ∀ i, probe p i∈Icc (M+(N:ℝ)/4) (2*M-(N:ℝ)/4)) →
    let Q := fun k : ℕ => Qbase*2^k
    let Ctail := 4*U*(64/c)^2+192/c
    let Clow := (2*U+c/32)*(3072/c)^2+3072/c
    let Cerror := (768:ℝ)^2*Ctail+Clow
    let Density := fun k => 128*Cerror*(M*R^2/((N:ℝ)*(Q k:ℝ)^2))*
      (2+Real.log (512*R^2/(c*((Q k:ℝ)/768))+1))
    ∃ (anchor : (ℝ × ℤ) → Fin 2 → ℚ)
      (band : (ℝ × ℤ) → Option ℕ) (za : (ℝ × ℤ) → Fin 2 → ℝ),
      (∀ p∈Chunks, ∀ i,
        h p.1 (za p i)=(anchor p i:ℝ) ∧
        |za p i-probe p i| ≤ (N:ℝ)/16 ∧ za p i∈Icc M (2*M)) ∧
      (∀ p∈Chunks, match band p with
        | none => ∃ i, ¬(768*(anchor p i).den ≤ Q kmax ∧
            24576*R^2 ≤ c*(Q kmax:ℝ)*(anchor p i).den)
        | some k => k ≤ kmax ∧
            (∀ i, 768*(anchor p i).den ≤ Q k ∧
              24576*R^2 ≤ c*(Q k:ℝ)*(anchor p i).den)) ∧
      (∀ k ≤ kmax, ((Chunks.filter (fun p => band p=some (k+1))).card:ℝ) ≤
        (Y.card:ℝ)*Density k) ∧
      ((Chunks.filter (fun p => band p=none)).card:ℝ) ≤
        (Y.card:ℝ)*Density kmax := by
  exact double_difference_chunk_grid_dyadic_bands Chunks Y F rshift sshift n N Qbase kmax hNlink
    hc hU hn hd hw hsmall hshifts hy hphase hT hM hR hreg hbound hlower hnegative hscale hQbase hQmax

#print axioms double_difference_chunk_grid_dyadic_bands

open scoped Classical

/-- Unchanged existing private finite decomposition proof, copied only for scratch access;
promotion reuses its original declaration. -/
private theorem eight_grid_sum_reindex {α : Type*}
    (D : Finset (α × ℤ)) (w : α × ℤ → ℝ) :
    (∑ p ∈ D, w p) =
      ∑ r ∈ Finset.Ico (0:ℤ) 8,
        ∑ p ∈ (D.filter (fun p => p.2%8 = r)).image (fun p => (p.1,p.2/8-2)),
          w (p.1,r+8*p.2+16) := by
  classical
  have hmaps : ∀ p ∈ D, p.2%8 ∈ Finset.Ico (0:ℤ) 8 := by
    intro p _
    simp only [Finset.mem_Ico]
    exact ⟨Int.emod_nonneg _ (by norm_num),Int.emod_lt_of_pos _ (by norm_num)⟩
  rw [← Finset.sum_fiberwise_of_maps_to hmaps w]
  apply Finset.sum_congr rfl
  intro r _
  have hinj : Set.InjOn (fun p : α × ℤ => (p.1,p.2/8-2))
      ↑(D.filter (fun p => p.2%8 = r)) := by
    intro p hp q hq heq
    have hpmod := (Finset.mem_filter.mp hp).2
    have hqmod := (Finset.mem_filter.mp hq).2
    have hf := congrArg Prod.fst heq
    have hs := congrArg Prod.snd heq
    change p.1 = q.1 at hf
    change p.2/8-2 = q.2/8-2 at hs
    apply Prod.ext hf
    omega
  rw [Finset.sum_image hinj]
  apply Finset.sum_congr rfl
  intro p hp
  have hpmod := (Finset.mem_filter.mp hp).2
  have heq : r+8*(p.2/8-2)+16 = p.2 := by omega
  dsimp only
  rw [heq]

example {α : Type*}
    (D : Finset (α × ℤ)) (w : α × ℤ → ℝ) :
    (∑ p ∈ D, w p) =
      ∑ r ∈ Finset.Ico (0:ℤ) 8,
        ∑ p ∈ (D.filter (fun p => p.2%8 = r)).image (fun p => (p.1,p.2/8-2)),
          w (p.1,r+8*p.2+16) := by
  exact eight_grid_sum_reindex D w

#print axioms eight_grid_sum_reindex

/-- Unchanged existing private finite decomposition proof, copied only for scratch access;
promotion reuses its original declaration. -/
private theorem integer_chunk_partition (v : ℤ → ℂ) (n : ℕ)
    {a b : ℤ} (hab : a ≤ b) :
    (∑ m ∈ Finset.Ico a b, ∑ k ∈ Finset.Ioc ((n:ℤ)*m) ((n:ℤ)*(m+1)), v k) =
      ∑ k ∈ Finset.Ioc ((n:ℤ)*a) ((n:ℤ)*b), v k := by
  induction b, hab using Int.leInduction with
  | base => simp
  | succ b hab ih =>
    rw [← Finset.sum_Ico_add_eq_sum_Ico_add_one hab,ih]
    have hn : (0:ℤ) ≤ n := Int.natCast_nonneg n
    have h₁ : (n:ℤ)*a ≤ (n:ℤ)*b := mul_le_mul_of_nonneg_left hab hn
    have h₂ : (n:ℤ)*b ≤ (n:ℤ)*(b+1) := by nlinarith only [hn]
    have hdis : Disjoint (Finset.Ioc ((n:ℤ)*a) ((n:ℤ)*b))
        (Finset.Ioc ((n:ℤ)*b) ((n:ℤ)*(b+1))) := by
      apply Finset.disjoint_left.mpr
      intro k hk hl
      have hx := (Finset.mem_Ioc.mp hk).2
      have hy := (Finset.mem_Ioc.mp hl).1
      omega
    rw [← Finset.sum_union hdis,Finset.Ioc_union_Ioc_eq_Ioc h₁ h₂]

example (v : ℤ → ℂ) (n : ℕ)
    {a b : ℤ} (hab : a ≤ b) :
    (∑ m ∈ Finset.Ico a b, ∑ k ∈ Finset.Ioc ((n:ℤ)*m) ((n:ℤ)*(m+1)), v k) =
      ∑ k ∈ Finset.Ioc ((n:ℤ)*a) ((n:ℤ)*b), v k := by
  exact integer_chunk_partition v n hab

#print axioms integer_chunk_partition

/-- Unchanged existing private finite decomposition proof, copied only for scratch access;
promotion reuses its original declaration. -/
private theorem integer_whole_sum_le_chunks_and_endpoints
    (v : ℤ → ℂ) (n : ℕ) {A B a b : ℤ}
    (ha : A ≤ (n:ℤ)*a) (hab : a ≤ b) (hb : (n:ℤ)*b ≤ B)
    (hv : ∀ k ∈ Finset.Ioc A B, ‖v k‖ ≤ 1) :
    ‖∑ k ∈ Finset.Ioc A B, v k‖ ≤
      (∑ m ∈ Finset.Ico a b, ‖∑ k ∈ Finset.Ioc ((n:ℤ)*m) ((n:ℤ)*(m+1)), v k‖)+
        (((n:ℤ)*a-A:ℤ):ℝ)+((B-(n:ℤ)*b:ℤ):ℝ) := by
  have hmiddle : (n:ℤ)*a ≤ (n:ℤ)*b :=
    mul_le_mul_of_nonneg_left hab (Int.natCast_nonneg n)
  have hsub : Finset.Ioc ((n:ℤ)*a) ((n:ℤ)*b) ⊆ Finset.Ioc A B := by
    intro k hk
    obtain ⟨hk₁,hk₂⟩ := Finset.mem_Ioc.mp hk
    exact Finset.mem_Ioc.mpr ⟨ha.trans_lt hk₁,hk₂.trans hb⟩
  let S := Finset.Ioc A B \ Finset.Ioc ((n:ℤ)*a) ((n:ℤ)*b)
  have hsum := Finset.sum_sdiff (f:=v) hsub
  have hnorm : ‖∑ k ∈ S, v k‖ ≤ (S.card:ℝ) := by
    apply (norm_sum_le _ _).trans
    calc
      (∑ k ∈ S, ‖v k‖) ≤ ∑ _k ∈ S, (1:ℝ) := Finset.sum_le_sum
        (fun k hk => hv k (Finset.mem_sdiff.mp hk).1)
      _ = (S.card:ℝ) := by simp
  have hcount := Finset.card_sdiff_of_subset hsub
  have hcountZ : (S.card:ℤ) = ((n:ℤ)*a-A)+(B-(n:ℤ)*b) := by
    dsimp only [S]
    rw [hcount,Int.card_Ioc,Int.card_Ioc]
    omega
  have hcountR : (S.card:ℝ) = (((n:ℤ)*a-A:ℤ):ℝ)+((B-(n:ℤ)*b:ℤ):ℝ) := by
    exact_mod_cast hcountZ
  have hinner : ‖∑ k ∈ Finset.Ioc ((n:ℤ)*a) ((n:ℤ)*b), v k‖ ≤
      ∑ m ∈ Finset.Ico a b, ‖∑ k ∈ Finset.Ioc ((n:ℤ)*m) ((n:ℤ)*(m+1)), v k‖ := by
    rw [← integer_chunk_partition v n hab]
    exact norm_sum_le _ _
  rw [← hsum]
  have htriangle := norm_add_le (∑ k ∈ S,v k)
    (∑ k ∈ Finset.Ioc ((n:ℤ)*a) ((n:ℤ)*b),v k)
  rw [hcountR] at hnorm
  linarith only [htriangle,hnorm,hinner]

example
    (v : ℤ → ℂ) (n : ℕ) {A B a b : ℤ}
    (ha : A ≤ (n:ℤ)*a) (hab : a ≤ b) (hb : (n:ℤ)*b ≤ B)
    (hv : ∀ k ∈ Finset.Ioc A B, ‖v k‖ ≤ 1) :
    ‖∑ k ∈ Finset.Ioc A B, v k‖ ≤
      (∑ m ∈ Finset.Ico a b, ‖∑ k ∈ Finset.Ioc ((n:ℤ)*m) ((n:ℤ)*(m+1)), v k‖)+
        (((n:ℤ)*a-A:ℤ):ℝ)+((B-(n:ℤ)*b:ℤ):ℝ) := by
  exact integer_whole_sum_le_chunks_and_endpoints v n ha hab hb hv

#print axioms integer_whole_sum_le_chunks_and_endpoints

/-- Unchanged existing private finite decomposition proof, copied only for scratch access;
promotion reuses its original declaration. -/
private theorem eight_grid_endpoint_selection (n : ℕ) (hn : 0 < n)
    {M Buffer Width : ℝ} (hBuffer : 0 ≤ Buffer) (hWidth : 0 ≤ Width)
    (hroom : 2*(Buffer+Width)+6*(8*(n:ℝ)) ≤ M) :
    let N : ℝ := 8*n
    ∃ a b : ℤ,
      ⌈M⌉ ≤ (n:ℤ)*a ∧ a ≤ b ∧ (n:ℤ)*b ≤ ⌊2*M⌋ ∧
      (∀ m ∈ Finset.Ico a b, (n:ℝ)*m ∈
        Icc (M+Buffer+Width+4*N) (2*M-Buffer-Width-N)) ∧
      ((((n:ℤ)*a-⌈M⌉:ℤ):ℝ)+((⌊2*M⌋-(n:ℤ)*b:ℤ):ℝ)) ≤
        2*Buffer+2*Width+6*N := by
  intro N
  have hnp : (0:ℝ) < n := Nat.cast_pos.mpr hn
  let L := M+Buffer+Width+4*N
  let R := 2*M-Buffer-Width-N
  let a : ℤ := ⌈L/(n:ℝ)⌉
  let b : ℤ := ⌊R/(n:ℝ)⌋
  have haL : L ≤ (n:ℝ)*a := by
    have hh := Int.le_ceil (L/(n:ℝ))
    exact (div_le_iff₀ hnp).mp hh |>.trans_eq (mul_comm _ _)
  have haU : (n:ℝ)*a < L+(n:ℝ) := by
    have hh := mul_lt_mul_of_pos_left (Int.ceil_lt_add_one (L/(n:ℝ))) hnp
    change (n:ℝ)*a < (n:ℝ)*(L/(n:ℝ)+1) at hh
    convert hh using 1
    field_simp
  have hbL : R-(n:ℝ) < (n:ℝ)*b := by
    have hh := mul_lt_mul_of_pos_left (Int.sub_one_lt_floor (R/(n:ℝ))) hnp
    change (n:ℝ)*(R/(n:ℝ)-1) < (n:ℝ)*b at hh
    convert hh using 1
    field_simp
  have hbU : (n:ℝ)*b ≤ R := by
    have hh := (le_div_iff₀ hnp).mp (Int.floor_le (R/(n:ℝ)))
    exact (mul_comm _ _).le.trans hh
  have hLroom : L+2*(n:ℝ) ≤ R := by
    dsimp only [L,R,N]
    linarith only [hroom,hnp]
  have habR : (a:ℝ) ≤ b :=
    le_of_mul_le_mul_left
      (show (n:ℝ)*(a:ℝ) ≤ (n:ℝ)*b by linarith only [haU,hbL,hLroom]) hnp
  have hab : a ≤ b := by exact_mod_cast habR
  have haM : M ≤ (n:ℝ)*a := by
    dsimp only [L,N] at haL
    linarith only [haL,hBuffer,hWidth,hnp]
  have hbM : (n:ℝ)*b ≤ 2*M := by
    dsimp only [R,N] at hbU
    linarith only [hbU,hBuffer,hWidth,hnp]
  refine ⟨a,b,?_,hab,?_,?_,?_⟩
  · apply Int.ceil_le.mpr
    simpa only [Int.cast_mul,Int.cast_natCast] using haM
  · apply Int.le_floor.mpr
    simpa only [Int.cast_mul,Int.cast_natCast] using hbM
  · intro m hm
    obtain ⟨ham,hmb⟩ := Finset.mem_Ico.mp hm
    have hmL := mul_le_mul_of_nonneg_left (show (a:ℝ) ≤ m by exact_mod_cast ham) hnp.le
    have hmR := mul_le_mul_of_nonneg_left (show (m:ℝ) ≤ b by exact_mod_cast hmb.le) hnp.le
    exact ⟨haL.trans hmL,hmR.trans hbU⟩
  · have hceil := Int.le_ceil M
    have hfloor := Int.floor_le (2*M)
    push_cast
    dsimp only [L,R,N] at haU hbL ⊢
    linarith only [haU,hbL,hceil,hfloor,hnp]

example (n : ℕ) (hn : 0 < n)
    {M Buffer Width : ℝ} (hBuffer : 0 ≤ Buffer) (hWidth : 0 ≤ Width)
    (hroom : 2*(Buffer+Width)+6*(8*(n:ℝ)) ≤ M) :
    let N : ℝ := 8*n
    ∃ a b : ℤ,
      ⌈M⌉ ≤ (n:ℤ)*a ∧ a ≤ b ∧ (n:ℤ)*b ≤ ⌊2*M⌋ ∧
      (∀ m ∈ Finset.Ico a b, (n:ℝ)*m ∈
        Icc (M+Buffer+Width+4*N) (2*M-Buffer-Width-N)) ∧
      ((((n:ℤ)*a-⌈M⌉:ℤ):ℝ)+((⌊2*M⌋-(n:ℤ)*b:ℤ):ℝ)) ≤
        2*Buffer+2*Width+6*N := by
  exact eight_grid_endpoint_selection n hn hBuffer hWidth hroom

#print axioms eight_grid_endpoint_selection

/-- Unchanged existing private finite decomposition proof, copied only for scratch access;
promotion reuses its original declaration. -/
private theorem integer_chunk_dyadic_band_power
    {α : Type*} (Chunks : Finset (α × ℤ)) (v : α → ℤ → ℂ)
    (n kmax : ℕ) (band : (α × ℤ) → Option ℕ)
    (hv : ∀ y k, ‖v y k‖ ≤ 1)
    (hband : ∀ p∈Chunks, ∀ k, band p=some k → k ≤ kmax) :
    (∑ p∈Chunks, ‖∑ j∈Finset.Ioc ((n:ℤ)*p.2) ((n:ℤ)*(p.2+1)),v p.1 j‖)^12 ≤
      ((kmax:ℝ)+2)^11*
        (((n:ℝ)*((Chunks.filter (fun p => band p=none)).card:ℝ))^12+
          ∑ k∈Finset.range (kmax+1),
            (∑ p∈Chunks.filter (fun p => band p=some k),
              ‖∑ j∈Finset.Ioc ((n:ℤ)*p.2) ((n:ℤ)*(p.2+1)),v p.1 j‖)^12) := by
  classical
  let Labels := insert none ((Finset.range (kmax+1)).image some)
  let Chunk := fun p : α × ℤ =>
    ‖∑ j∈Finset.Ioc ((n:ℤ)*p.2) ((n:ℤ)*(p.2+1)),v p.1 j‖
  let W := fun label => ∑ p∈Chunks.filter (fun p => band p=label),Chunk p
  have hW label : 0 ≤ W label := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  have hmaps : ∀ p∈Chunks, band p∈Labels := by
    intro p hp
    cases hb : band p with
    | none => exact Finset.mem_insert_self _ _
    | some k =>
      apply Finset.mem_insert_of_mem
      exact Finset.mem_image.mpr ⟨k,Finset.mem_range.mpr (by
        have hh := hband p hp k hb
        omega),rfl⟩
  have hsum : (∑ label∈Labels,W label)=∑ p∈Chunks,Chunk p :=
    Finset.sum_fiberwise_of_maps_to hmaps Chunk
  have hcardLabels : Labels.card=kmax+2 := by
    have hnone : (none : Option ℕ)∉(Finset.range (kmax+1)).image some := by simp
    change (insert none ((Finset.range (kmax+1)).image some)).card=kmax+2
    rw [Finset.card_insert_of_notMem hnone,
      Finset.card_image_of_injective _ (Option.some_injective _),Finset.card_range]
  have hholder := Real.rpow_sum_le_const_mul_sum_rpow_of_nonneg Labels
    (f:=W) (p:=(12:ℝ)) (by norm_num) (fun label _ => hW label)
  have hpower : (∑ p∈Chunks,Chunk p)^12 ≤
      ((kmax:ℝ)+2)^11*∑ label∈Labels,(W label)^12 := by
    simpa only [hsum,hcardLabels,Nat.cast_add,Nat.cast_ofNat,
      show (12:ℝ)-1=11 by norm_num,Real.rpow_ofNat] using hholder
  have hchunk p : Chunk p ≤ (n:ℝ) := by
    have hcard : (Finset.Ioc ((n:ℤ)*p.2) ((n:ℤ)*(p.2+1))).card=n := by
      rw [Int.card_Ioc,show (n:ℤ)*(p.2+1)-(n:ℤ)*p.2=(n:ℤ) by ring]
      simp only [Int.toNat_natCast]
    calc
      Chunk p ≤ ∑ j∈Finset.Ioc ((n:ℤ)*p.2) ((n:ℤ)*(p.2+1)),‖v p.1 j‖ :=
        norm_sum_le _ _
      _ ≤ ∑ _j∈Finset.Ioc ((n:ℤ)*p.2) ((n:ℤ)*(p.2+1)),(1:ℝ) :=
        Finset.sum_le_sum (fun j _ => hv p.1 j)
      _ = _ := by simp only [Finset.sum_const,hcard,nsmul_eq_mul,mul_one]
  have hterminal : W none ≤ (n:ℝ)*((Chunks.filter (fun p => band p=none)).card:ℝ) := by
    calc
      W none ≤ ∑ _p∈Chunks.filter (fun p => band p=none),(n:ℝ) :=
        Finset.sum_le_sum (fun p _ => hchunk p)
      _ = _ := by simp only [Finset.sum_const,nsmul_eq_mul]; ring
  have hlabelSum : (∑ label∈Labels,(W label)^12)=
      (W none)^12+∑ k∈Finset.range (kmax+1),(W (some k))^12 := by
    rw [Finset.sum_insert (by simp)]
    rw [Finset.sum_image]
    intro a _ b _ hab
    exact Option.some_injective _ hab
  calc
    _ ≤ ((kmax:ℝ)+2)^11*∑ label∈Labels,(W label)^12 := hpower
    _ = ((kmax:ℝ)+2)^11*((W none)^12+
        ∑ k∈Finset.range (kmax+1),(W (some k))^12) := by rw [hlabelSum]
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (add_le_add (pow_le_pow_left₀ (hW none) hterminal 12) le_rfl) (by positivity)

example
    {α : Type*} (Chunks : Finset (α × ℤ)) (v : α → ℤ → ℂ)
    (n kmax : ℕ) (band : (α × ℤ) → Option ℕ)
    (hv : ∀ y k, ‖v y k‖ ≤ 1)
    (hband : ∀ p∈Chunks, ∀ k, band p=some k → k ≤ kmax) :
    (∑ p∈Chunks, ‖∑ j∈Finset.Ioc ((n:ℤ)*p.2) ((n:ℤ)*(p.2+1)),v p.1 j‖)^12 ≤
      ((kmax:ℝ)+2)^11*
        (((n:ℝ)*((Chunks.filter (fun p => band p=none)).card:ℝ))^12+
          ∑ k∈Finset.range (kmax+1),
            (∑ p∈Chunks.filter (fun p => band p=some k),
              ‖∑ j∈Finset.Ioc ((n:ℤ)*p.2) ((n:ℤ)*(p.2+1)),v p.1 j‖)^12) := by
  exact integer_chunk_dyadic_band_power Chunks v n kmax band hv hband

#print axioms integer_chunk_dyadic_band_power

/-- Unchanged existing private finite decomposition proof, copied only for scratch access;
promotion reuses its original declaration. -/
private theorem integer_subinterval_trimmed_chunk_selection
    (n : ℕ) (hn : 0 < n) {A₀ B₀ a₀ b₀ A B : ℤ}
    (ha₀ : A₀ ≤ (n:ℤ)*a₀) (hb₀ : (n:ℤ)*b₀ ≤ B₀)
    (hA : A₀ ≤ A) (hB : B ≤ B₀) :
    let Budget : ℤ := ((n:ℤ)*a₀-A₀)+(B₀-(n:ℤ)*b₀)+2*(n:ℤ)
    B-A ≤ Budget ∨
      ∃ a b : ℤ, a₀ ≤ a ∧ b ≤ b₀ ∧ A ≤ (n:ℤ)*a ∧ a ≤ b ∧
        (n:ℤ)*b ≤ B ∧ ((n:ℤ)*a-A)+(B-(n:ℤ)*b) ≤ Budget := by
  intro Budget
  have hnz : (0:ℤ) < n := by exact_mod_cast hn
  have hceil : A < (n:ℤ)*(A/(n:ℤ)+1) ∧ (n:ℤ)*(A/(n:ℤ)+1) ≤ A+n := by
    have hzero := Int.emod_nonneg A hnz.ne'
    have hupper := Int.emod_lt_of_pos A hnz
    have heq := Int.mul_ediv_add_emod A (n:ℤ)
    constructor <;> nlinarith only [hzero,hupper,heq]
  have hfloor : (n:ℤ)*(B/(n:ℤ)) ≤ B ∧ B ≤ (n:ℤ)*(B/(n:ℤ))+n := by
    have hzero := Int.emod_nonneg B hnz.ne'
    have hupper := Int.emod_lt_of_pos B hnz
    have heq := Int.mul_ediv_add_emod B (n:ℤ)
    constructor <;> linarith only [hzero,hupper,heq]
  let a := max a₀ (A/(n:ℤ)+1)
  let b := min b₀ (B/(n:ℤ))
  have ha : A ≤ (n:ℤ)*a :=
    hceil.1.le.trans (mul_le_mul_of_nonneg_left (le_max_right _ _) hnz.le)
  have hb : (n:ℤ)*b ≤ B :=
    (mul_le_mul_of_nonneg_left (min_le_right _ _) hnz.le).trans hfloor.1
  have hleft : (n:ℤ)*a-A ≤ (n:ℤ)*a₀-A₀+n := by
    rcases le_total a₀ (A/(n:ℤ)+1) with hh | hh
    · rw [show a=A/(n:ℤ)+1 from max_eq_right hh]
      linarith only [hceil.2,ha₀]
    · rw [show a=a₀ from max_eq_left hh]
      linarith only [hA,hnz]
  have hright : B-(n:ℤ)*b ≤ B₀-(n:ℤ)*b₀+n := by
    rcases le_total b₀ (B/(n:ℤ)) with hh | hh
    · rw [show b=b₀ from min_eq_left hh]
      linarith only [hB,hnz]
    · rw [show b=B/(n:ℤ) from min_eq_right hh]
      linarith only [hfloor.2,hb₀]
  have hbudget : ((n:ℤ)*a-A)+(B-(n:ℤ)*b) ≤ Budget := by
    dsimp only [Budget]
    linarith only [hleft,hright]
  by_cases hab : a ≤ b
  · exact Or.inr ⟨a,b,le_max_left _ _,min_le_left _ _,ha,hab,hb,hbudget⟩
  · left
    have horder : (n:ℤ)*b ≤ (n:ℤ)*a :=
      mul_le_mul_of_nonneg_left (le_of_not_ge hab) hnz.le
    linarith only [hbudget,horder]

example
    (n : ℕ) (hn : 0 < n) {A₀ B₀ a₀ b₀ A B : ℤ}
    (ha₀ : A₀ ≤ (n:ℤ)*a₀) (hb₀ : (n:ℤ)*b₀ ≤ B₀)
    (hA : A₀ ≤ A) (hB : B ≤ B₀) :
    let Budget : ℤ := ((n:ℤ)*a₀-A₀)+(B₀-(n:ℤ)*b₀)+2*(n:ℤ)
    B-A ≤ Budget ∨
      ∃ a b : ℤ, a₀ ≤ a ∧ b ≤ b₀ ∧ A ≤ (n:ℤ)*a ∧ a ≤ b ∧
        (n:ℤ)*b ≤ B ∧ ((n:ℤ)*a-A)+(B-(n:ℤ)*b) ≤ Budget := by
  exact integer_subinterval_trimmed_chunk_selection n hn ha₀ hb₀ hA hB

#print axioms integer_subinterval_trimmed_chunk_selection

/-- Unchanged existing private finite decomposition proof, copied only for scratch access;
promotion reuses its original declaration. -/
private theorem integer_subinterval_trimmed_chunks {α : Type*}
    (Y : Finset α) (v : α → ℤ → ℂ) (n : ℕ) (hn : 0 < n)
    {A₀ B₀ a₀ b₀ A B : ℤ}
    (ha₀ : A₀ ≤ (n:ℤ)*a₀) (hb₀ : (n:ℤ)*b₀ ≤ B₀)
    (hA : A₀ ≤ A) (hB : B ≤ B₀) (hab : A ≤ B)
    (hv : ∀ y∈Y, ∀ j∈Finset.Ioc A B, ‖v y j‖ ≤ 1) :
    let Budget : ℤ := ((n:ℤ)*a₀-A₀)+(B₀-(n:ℤ)*b₀)+2*(n:ℤ)
    ∃ Chunks : Finset (α × ℤ), Chunks ⊆ Y ×ˢ Finset.Ico a₀ b₀ ∧
      (∑ y∈Y, ‖∑ j∈Finset.Ioc A B,v y j‖) ≤
        (∑ p∈Chunks, ‖∑ j∈Finset.Ioc ((n:ℤ)*p.2) ((n:ℤ)*(p.2+1)),v p.1 j‖)+
          (Y.card:ℝ)*(Budget:ℝ) := by
  classical
  intro Budget
  rcases integer_subinterval_trimmed_chunk_selection n hn ha₀ hb₀ hA hB with
    hshort | ⟨a,b,haa,hbb,ha,hab',hb,hcost⟩
  · refine ⟨∅,Finset.empty_subset _,?_⟩
    have hcard : ((Finset.Ioc A B).card:ℝ)=((B-A:ℤ):ℝ) := by
      exact_mod_cast (show ((Finset.Ioc A B).card:ℤ)=B-A by
        rw [Int.card_Ioc,Int.toNat_of_nonneg (sub_nonneg.mpr hab)])
    have hone y (hyY : y∈Y) : ‖∑ j∈Finset.Ioc A B,v y j‖ ≤ (Budget:ℝ) := by
      calc
        _ ≤ ∑ j∈Finset.Ioc A B,‖v y j‖ := norm_sum_le _ _
        _ ≤ ∑ _j∈Finset.Ioc A B,(1:ℝ) := Finset.sum_le_sum (fun j hj => hv y hyY j hj)
        _ = ((B-A:ℤ):ℝ) := by simp only [Finset.sum_const,nsmul_eq_mul,mul_one,hcard]
        _ ≤ (Budget:ℝ) := by exact_mod_cast hshort
    have hh := Finset.sum_le_sum hone
    simpa only [Finset.sum_empty,zero_add,Finset.sum_const,nsmul_eq_mul] using hh
  · let Chunks := Y ×ˢ Finset.Ico a b
    refine ⟨Chunks,?_,?_⟩
    · intro p hp
      obtain ⟨hpY,hpI⟩ := Finset.mem_product.mp hp
      obtain ⟨hpa,hpb⟩ := Finset.mem_Ico.mp hpI
      exact Finset.mem_product.mpr ⟨hpY,Finset.mem_Ico.mpr
        ⟨haa.trans hpa,hpb.trans_le hbb⟩⟩
    · have hh := Finset.sum_le_sum (fun y hyY =>
        integer_whole_sum_le_chunks_and_endpoints (v y) n ha hab' hb (hv y hyY))
      have hmid : (∑ y∈Y, ‖∑ j∈Finset.Ioc A B,v y j‖) ≤
          (∑ p∈Chunks, ‖∑ j∈Finset.Ioc ((n:ℤ)*p.2) ((n:ℤ)*(p.2+1)),v p.1 j‖)+
            (Y.card:ℝ)*((((n:ℤ)*a-A)+(B-(n:ℤ)*b):ℤ):ℝ) := by
        convert hh using 1
        simp only [Chunks,Finset.sum_product,Finset.sum_add_distrib,Finset.sum_const,
          nsmul_eq_mul,Int.cast_add]
        ring
      exact hmid.trans (add_le_add le_rfl
        (mul_le_mul_of_nonneg_left (by exact_mod_cast hcost) (Nat.cast_nonneg _)))

example {α : Type*}
    (Y : Finset α) (v : α → ℤ → ℂ) (n : ℕ) (hn : 0 < n)
    {A₀ B₀ a₀ b₀ A B : ℤ}
    (ha₀ : A₀ ≤ (n:ℤ)*a₀) (hb₀ : (n:ℤ)*b₀ ≤ B₀)
    (hA : A₀ ≤ A) (hB : B ≤ B₀) (hab : A ≤ B)
    (hv : ∀ y∈Y, ∀ j∈Finset.Ioc A B, ‖v y j‖ ≤ 1) :
    let Budget : ℤ := ((n:ℤ)*a₀-A₀)+(B₀-(n:ℤ)*b₀)+2*(n:ℤ)
    ∃ Chunks : Finset (α × ℤ), Chunks ⊆ Y ×ˢ Finset.Ico a₀ b₀ ∧
      (∑ y∈Y, ‖∑ j∈Finset.Ioc A B,v y j‖) ≤
        (∑ p∈Chunks, ‖∑ j∈Finset.Ioc ((n:ℤ)*p.2) ((n:ℤ)*(p.2+1)),v p.1 j‖)+
          (Y.card:ℝ)*(Budget:ℝ) := by
  exact integer_subinterval_trimmed_chunks Y v n hn ha₀ hb₀ hA hB hab hv

#print axioms integer_subinterval_trimmed_chunks

/-- Unchanged existing private finite decomposition proof, copied only for scratch access;
promotion reuses its original declaration. -/
private theorem integer_phase_subinterval_trimmed_chunks {α : Type*}
    (Y : Finset α) (v : α → ℤ → ℂ) (n : ℕ) (hn : 0 < n)
    {A₀ B₀ a₀ b₀ : ℤ} (A B : α → ℤ)
    (ha₀ : A₀ ≤ (n:ℤ)*a₀) (hb₀ : (n:ℤ)*b₀ ≤ B₀)
    (hA : ∀ y∈Y, A₀ ≤ A y) (hB : ∀ y∈Y, B y ≤ B₀)
    (hab : ∀ y∈Y, A y ≤ B y)
    (hv : ∀ y∈Y, ∀ j∈Finset.Ioc (A y) (B y), ‖v y j‖ ≤ 1) :
    let Budget : ℤ := ((n:ℤ)*a₀-A₀)+(B₀-(n:ℤ)*b₀)+2*(n:ℤ)
    ∃ Chunks : Finset (α × ℤ), Chunks ⊆ Y ×ˢ Finset.Ico a₀ b₀ ∧
      (∑ y∈Y, ‖∑ j∈Finset.Ioc (A y) (B y),v y j‖) ≤
        (∑ p∈Chunks, ‖∑ j∈Finset.Ioc ((n:ℤ)*p.2) ((n:ℤ)*(p.2+1)),v p.1 j‖)+
          (Y.card:ℝ)*(Budget:ℝ) := by
  classical
  intro Budget
  let Chunk := fun p : α × ℤ =>
    ‖∑ j∈Finset.Ioc ((n:ℤ)*p.2) ((n:ℤ)*(p.2+1)),v p.1 j‖
  have hex (y : α) : ∃ Cy : Finset (α × ℤ), y∈Y →
      Cy ⊆ {y} ×ˢ Finset.Ico a₀ b₀ ∧
      ‖∑ j∈Finset.Ioc (A y) (B y),v y j‖ ≤ (∑ p∈Cy,Chunk p)+(Budget:ℝ) := by
    by_cases hy : y∈Y
    · obtain ⟨Cy,hCy,hbound⟩ :=
        integer_subinterval_trimmed_chunks {y} v n hn ha₀ hb₀
          (hA y hy) (hB y hy) (hab y hy) (by
            intro z hz j hj
            have heq : z=y := Finset.mem_singleton.mp hz
            subst z
            exact hv y hy j hj)
      exact ⟨Cy,fun _ => ⟨hCy,by
        simpa only [Finset.sum_singleton,Finset.card_singleton,Nat.cast_one,one_mul]
          using hbound⟩⟩
    · exact ⟨∅,fun hh => (hy hh).elim⟩
  choose Cy hCy using hex
  have hphase y (hy : y∈Y) p (hp : p∈Cy y) : p.1=y :=
    Finset.mem_singleton.mp (Finset.mem_product.mp ((hCy y hy).1 hp)).1
  have hdisj : ∀ y∈Y, ∀ z∈Y, y≠z → Disjoint (Cy y) (Cy z) := by
    intro y hy z hz hyz
    apply Finset.disjoint_left.mpr
    intro p hp hq
    exact hyz ((hphase y hy p hp).symm.trans (hphase z hz p hq))
  refine ⟨Y.biUnion Cy,?_,?_⟩
  · intro p hp
    obtain ⟨y,hy,hpy⟩ := Finset.mem_biUnion.mp hp
    obtain ⟨hfirst,hsecond⟩ := Finset.mem_product.mp ((hCy y hy).1 hpy)
    exact Finset.mem_product.mpr
      ⟨(Finset.mem_singleton.mp hfirst).symm ▸ hy,hsecond⟩
  · have hh := Finset.sum_le_sum (fun y hy => (hCy y hy).2)
    rw [Finset.sum_add_distrib,Finset.sum_const,nsmul_eq_mul] at hh
    rw [Finset.sum_biUnion hdisj]
    exact hh

example {α : Type*}
    (Y : Finset α) (v : α → ℤ → ℂ) (n : ℕ) (hn : 0 < n)
    {A₀ B₀ a₀ b₀ : ℤ} (A B : α → ℤ)
    (ha₀ : A₀ ≤ (n:ℤ)*a₀) (hb₀ : (n:ℤ)*b₀ ≤ B₀)
    (hA : ∀ y∈Y, A₀ ≤ A y) (hB : ∀ y∈Y, B y ≤ B₀)
    (hab : ∀ y∈Y, A y ≤ B y)
    (hv : ∀ y∈Y, ∀ j∈Finset.Ioc (A y) (B y), ‖v y j‖ ≤ 1) :
    let Budget : ℤ := ((n:ℤ)*a₀-A₀)+(B₀-(n:ℤ)*b₀)+2*(n:ℤ)
    ∃ Chunks : Finset (α × ℤ), Chunks ⊆ Y ×ˢ Finset.Ico a₀ b₀ ∧
      (∑ y∈Y, ‖∑ j∈Finset.Ioc (A y) (B y),v y j‖) ≤
        (∑ p∈Chunks, ‖∑ j∈Finset.Ioc ((n:ℤ)*p.2) ((n:ℤ)*(p.2+1)),v p.1 j‖)+
          (Y.card:ℝ)*(Budget:ℝ) := by
  exact integer_phase_subinterval_trimmed_chunks Y v n hn A B ha₀ hb₀ hA hB hab hv

#print axioms integer_phase_subinterval_trimmed_chunks

/-- The actual double-difference phase-dependent subinterval sums consume the
constructed least bands, terminal counts and original integer endpoint budget.
Selected-band moments remain explicit in the conclusion, not assumed inputs. -/
private theorem double_difference_phase_subinterval_dyadic_band_reduction
    (Y : Finset ℝ) (F rshift sshift : ℝ → ℝ) (n N Qbase kmax : ℕ) (hNlink : N=8*n)
    {c U d w T M R Buffer Width : ℝ}
    (hc : 0 < c) (hU : 0 < U)
    (hn : 0 < n) (hd : 0 < d) (hw : w ≤ 1/4) (hsmall : 2*U*w ≤ c/64)
    (hshifts : ∀ y∈Y, 0 ≤ rshift y ∧ 0 ≤ sshift y ∧
      rshift y*sshift y=d*y ∧ rshift y+sshift y ≤ w)
    (hy : ∀ y∈Y, y∈Icc (1:ℝ) 2)
    (hT : 0 < T) (hM : 0 < M) (hR : 0 < R)
    (hreg : ∀ w, 0 < w → ContDiffAt ℝ ∞ F w)
    (hbound : ∀ u∈Icc (1/2:ℝ) 3, ∀ j, 1 ≤ j → j ≤ 7 → |iteratedDeriv j F u| ≤ U)
    (hlower : ∀ u∈Icc (1/2:ℝ) 3, c ≤ iteratedDeriv 5 F u)
    (hnegative : ∀ w∈Icc (1/2:ℝ) 3, iteratedDeriv 4 F w ≤ -c)
    (hscale : T*(N:ℝ)*R^2=M^3)
    (hQbase : 768 ≤ Qbase) (hQmax : (N:ℝ)*(Qbase*2^kmax:ℕ) ≤ M)
    (hBuffer : 0 ≤ Buffer) (hWidth : 0 ≤ Width)
    (hroom : 2*(Buffer+Width)+6*(N:ℝ) ≤ M)
    (A B : ℝ → ℤ) (hA : ∀ y∈Y, ⌈M⌉ ≤ A y)
    (hab : ∀ y∈Y, A y ≤ B y) (hB : ∀ y∈Y, B y ≤ ⌊2*M⌋) :
    let f := fun y v => T*((F (v/M)-F (v/M+rshift y)-F (v/M+sshift y)+
      F (v/M+rshift y+sshift y))/d)
    let h := fun y w => iteratedDeriv 2 (f y) w/2
    let probe := fun (p : ℝ × ℤ) (i : Fin 2) =>
      if i=0 then (n:ℝ)*p.2-2*(N:ℝ) else (n:ℝ)*p.2-11*(N:ℝ)/4
    let Q := fun k : ℕ => Qbase*2^k
    let Ctail := 4*U*(64/c)^2+192/c
    let Clow := (2*U+c/32)*(3072/c)^2+3072/c
    let Cerror := (768:ℝ)^2*Ctail+Clow
    let Density := fun k => 128*Cerror*(M*R^2/((N:ℝ)*(Q k:ℝ)^2))*
      (2+Real.log (512*R^2/(c*((Q k:ℝ)/768))+1))
    let Endpoint := (Y.card:ℝ)*(2*Buffer+2*Width+6*(N:ℝ)+2*(n:ℝ))
    ∃ (Chunks : Finset (ℝ × ℤ)) (anchor : (ℝ × ℤ) → Fin 2 → ℚ)
      (band : (ℝ × ℤ) → Option ℕ) (za : (ℝ × ℤ) → Fin 2 → ℝ),
      (∀ p∈Chunks, p.1∈Y) ∧
      (∀ p∈Chunks, (n:ℝ)*p.2∈
        Icc (M+Buffer+Width+4*(N:ℝ)) (2*M-Buffer-Width-(N:ℝ))) ∧
      (Chunks.card:ℝ) ≤ (Y.card:ℝ)*(8*M/(N:ℝ)) ∧
      (∀ p∈Chunks, ∀ i,
        h p.1 (za p i)=(anchor p i:ℝ) ∧
        |za p i-probe p i| ≤ (N:ℝ)/16 ∧ za p i∈Icc M (2*M)) ∧
      (∀ p∈Chunks, match band p with
        | none => ∃ i, ¬(768*(anchor p i).den ≤ Q kmax ∧
            24576*R^2 ≤ c*(Q kmax:ℝ)*(anchor p i).den)
        | some k => k ≤ kmax ∧
            (∀ i, 768*(anchor p i).den ≤ Q k ∧
              24576*R^2 ≤ c*(Q k:ℝ)*(anchor p i).den)) ∧
      (∀ k ≤ kmax, ((Chunks.filter (fun p => band p=some (k+1))).card:ℝ) ≤
        (Y.card:ℝ)*Density k) ∧
      ((Chunks.filter (fun p => band p=none)).card:ℝ) ≤ (Y.card:ℝ)*Density kmax ∧
      (∑ y∈Y, ‖∑ j∈Finset.Ioc (A y) (B y),(𝐞 (f y j):ℂ)‖)^12 ≤
        2^11*(((kmax:ℝ)+2)^11*
          (((n:ℝ)*(Y.card:ℝ)*Density kmax)^12+
            ∑ k∈Finset.range (kmax+1),
              (∑ p∈Chunks.filter (fun p => band p=some k),
                ‖∑ j∈Finset.Ioc ((n:ℤ)*p.2) ((n:ℤ)*(p.2+1)),
                  (𝐞 (f p.1 j):ℂ)‖)^12)+Endpoint^12) := by
  classical
  intro f h probe Q Ctail Clow Cerror Density Endpoint
  have hnp : (0:ℝ) < n := Nat.cast_pos.mpr hn
  have hNreal : (N:ℝ)=8*(n:ℝ) := by exact_mod_cast hNlink
  have hNp : (0:ℝ) < N := by rw [hNreal]; positivity
  obtain ⟨a₀,b₀,ha₀,hab₀,hb₀,hdeep₀,hend₀⟩ :=
    eight_grid_endpoint_selection n hn hBuffer hWidth (by
      simpa only [←hNreal] using hroom)
  let v := fun y j : ℝ => (𝐞 (f y j):ℂ)
  obtain ⟨Chunks,hChunks,hwhole⟩ :=
    integer_phase_subinterval_trimmed_chunks Y (fun y j => v y j) n hn A B ha₀ hb₀ hA hB hab
      (fun _ _ _ _ => by simp [v])
  have hphase p (hp : p∈Chunks) : p.1∈Y := (Finset.mem_product.mp (hChunks hp)).1
  have hdeep p (hp : p∈Chunks) : (n:ℝ)*p.2∈
      Icc (M+Buffer+Width+4*(N:ℝ)) (2*M-Buffer-Width-(N:ℝ)) := by
    simpa only [←hNreal] using hdeep₀ p.2 (Finset.mem_product.mp (hChunks hp)).2
  have hpoints p (hp : p∈Chunks) i :
      probe p i∈Icc (M+(N:ℝ)/4) (2*M-(N:ℝ)/4) := by
    have hh := hdeep p hp
    dsimp only [probe]
    split_ifs <;> constructor <;> linarith only [hh.1,hh.2,hBuffer,hWidth,hNp]
  obtain ⟨anchor,band,za,hroots,hbands,hcounts,htail⟩ :=
    double_difference_chunk_grid_dyadic_bands Chunks Y F rshift sshift n N Qbase kmax hNlink
      hc hU hn hd hw hsmall hshifts hy hphase hT hM hR hreg hbound hlower hnegative
      hscale hQbase hQmax hpoints
  have hleft : M ≤ (n:ℝ)*a₀ :=
    (Int.le_ceil M).trans (by exact_mod_cast ha₀)
  have hright : (n:ℝ)*b₀ ≤ 2*M :=
    (by exact_mod_cast hb₀ : (n:ℝ)*b₀ ≤ (⌊2*M⌋:ℤ)).trans (Int.floor_le (2*M))
  have hcardI : ((Finset.Ico a₀ b₀).card:ℝ)=((b₀-a₀:ℤ):ℝ) := by
    exact_mod_cast (show ((Finset.Ico a₀ b₀).card:ℤ)=b₀-a₀ by
      rw [Int.card_Ico,Int.toNat_of_nonneg (sub_nonneg.mpr hab₀)])
  have hcardIle : ((Finset.Ico a₀ b₀).card:ℝ) ≤ 8*M/(N:ℝ) := by
    apply (le_div_iff₀ hNp).mpr
    rw [hcardI,hNreal]
    push_cast
    nlinarith only [hleft,hright]
  have hcardChunks : (Chunks.card:ℝ) ≤ (Y.card:ℝ)*(8*M/(N:ℝ)) := by
    have hh : (Chunks.card:ℝ) ≤ (Y.card:ℝ)*((Finset.Ico a₀ b₀).card:ℝ) := by
      exact_mod_cast (show Chunks.card ≤ Y.card*(Finset.Ico a₀ b₀).card by
        simpa only [Finset.card_product] using Finset.card_le_card hChunks)
    exact hh.trans (mul_le_mul_of_nonneg_left hcardIle (Nat.cast_nonneg _))
  refine ⟨Chunks,anchor,band,za,hphase,hdeep,hcardChunks,hroots,hbands,hcounts,htail,?_⟩
  have hbudget :
      ((((n:ℤ)*a₀-⌈M⌉)+(⌊2*M⌋-(n:ℤ)*b₀)+2*(n:ℤ):ℤ):ℝ) ≤
        2*Buffer+2*Width+6*(N:ℝ)+2*(n:ℝ) := by
    have hh := hend₀
    rw [←hNreal] at hh
    push_cast at hh ⊢
    linarith only [hh]
  let Mass := ∑ p∈Chunks,
    ‖∑ j∈Finset.Ioc ((n:ℤ)*p.2) ((n:ℤ)*(p.2+1)),(𝐞 (f p.1 j):ℂ)‖
  have hmass : 0 ≤ Mass := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  have hEndpoint : 0 ≤ Endpoint := by dsimp only [Endpoint]; positivity
  have hwhole' : (∑ y∈Y, ‖∑ j∈Finset.Ioc (A y) (B y),(𝐞 (f y j):ℂ)‖) ≤ Mass+Endpoint :=
    hwhole.trans (add_le_add le_rfl
      (mul_le_mul_of_nonneg_left hbudget (Nat.cast_nonneg _)))
  have hbandMax p (hp : p∈Chunks) k (hk : band p=some k) : k ≤ kmax := by
    have hh := hbands p hp
    rw [hk] at hh
    exact hh.1
  have hpower := integer_chunk_dyadic_band_power Chunks (fun y j => v y j) n kmax band
    (fun _ _ => by simp [v]) hbandMax
  have htailLe : (n:ℝ)*((Chunks.filter (fun p => band p=none)).card:ℝ) ≤
      (n:ℝ)*(Y.card:ℝ)*Density kmax := by
    have htail' : ((Chunks.filter (fun p => band p=none)).card:ℝ) ≤
        (Y.card:ℝ)*Density kmax := htail
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left htail' hnp.le
  have hpower' : Mass^12 ≤ ((kmax:ℝ)+2)^11*
      (((n:ℝ)*(Y.card:ℝ)*Density kmax)^12+
        ∑ k∈Finset.range (kmax+1),
          (∑ p∈Chunks.filter (fun p => band p=some k),
            ‖∑ j∈Finset.Ioc ((n:ℤ)*p.2) ((n:ℤ)*(p.2+1)),(𝐞 (f p.1 j):ℂ)‖)^12) :=
    hpower.trans (mul_le_mul_of_nonneg_left
      (add_le_add (pow_le_pow_left₀ (by positivity) htailLe 12) le_rfl) (by positivity))
  calc
    _ ≤ (Mass+Endpoint)^12 :=
      pow_le_pow_left₀ (Finset.sum_nonneg (fun _ _ => norm_nonneg _)) hwhole' 12
    _ ≤ 2^11*(Mass^12+Endpoint^12) := add_pow_le hmass hEndpoint 12
    _ ≤ _ := mul_le_mul_of_nonneg_left (add_le_add hpower' le_rfl) (by norm_num)

example
    (Y : Finset ℝ) (F rshift sshift : ℝ → ℝ) (n N Qbase kmax : ℕ) (hNlink : N=8*n)
    {c U d w T M R Buffer Width : ℝ}
    (hc : 0 < c) (hU : 0 < U)
    (hn : 0 < n) (hd : 0 < d) (hw : w ≤ 1/4) (hsmall : 2*U*w ≤ c/64)
    (hshifts : ∀ y∈Y, 0 ≤ rshift y ∧ 0 ≤ sshift y ∧
      rshift y*sshift y=d*y ∧ rshift y+sshift y ≤ w)
    (hy : ∀ y∈Y, y∈Icc (1:ℝ) 2)
    (hT : 0 < T) (hM : 0 < M) (hR : 0 < R)
    (hreg : ∀ w, 0 < w → ContDiffAt ℝ ∞ F w)
    (hbound : ∀ u∈Icc (1/2:ℝ) 3, ∀ j, 1 ≤ j → j ≤ 7 → |iteratedDeriv j F u| ≤ U)
    (hlower : ∀ u∈Icc (1/2:ℝ) 3, c ≤ iteratedDeriv 5 F u)
    (hnegative : ∀ w∈Icc (1/2:ℝ) 3, iteratedDeriv 4 F w ≤ -c)
    (hscale : T*(N:ℝ)*R^2=M^3)
    (hQbase : 768 ≤ Qbase) (hQmax : (N:ℝ)*(Qbase*2^kmax:ℕ) ≤ M)
    (hBuffer : 0 ≤ Buffer) (hWidth : 0 ≤ Width)
    (hroom : 2*(Buffer+Width)+6*(N:ℝ) ≤ M)
    (A B : ℝ → ℤ) (hA : ∀ y∈Y, ⌈M⌉ ≤ A y)
    (hab : ∀ y∈Y, A y ≤ B y) (hB : ∀ y∈Y, B y ≤ ⌊2*M⌋) :
    let f := fun y v => T*((F (v/M)-F (v/M+rshift y)-F (v/M+sshift y)+
      F (v/M+rshift y+sshift y))/d)
    let h := fun y w => iteratedDeriv 2 (f y) w/2
    let probe := fun (p : ℝ × ℤ) (i : Fin 2) =>
      if i=0 then (n:ℝ)*p.2-2*(N:ℝ) else (n:ℝ)*p.2-11*(N:ℝ)/4
    let Q := fun k : ℕ => Qbase*2^k
    let Ctail := 4*U*(64/c)^2+192/c
    let Clow := (2*U+c/32)*(3072/c)^2+3072/c
    let Cerror := (768:ℝ)^2*Ctail+Clow
    let Density := fun k => 128*Cerror*(M*R^2/((N:ℝ)*(Q k:ℝ)^2))*
      (2+Real.log (512*R^2/(c*((Q k:ℝ)/768))+1))
    let Endpoint := (Y.card:ℝ)*(2*Buffer+2*Width+6*(N:ℝ)+2*(n:ℝ))
    ∃ (Chunks : Finset (ℝ × ℤ)) (anchor : (ℝ × ℤ) → Fin 2 → ℚ)
      (band : (ℝ × ℤ) → Option ℕ) (za : (ℝ × ℤ) → Fin 2 → ℝ),
      (∀ p∈Chunks, p.1∈Y) ∧
      (∀ p∈Chunks, (n:ℝ)*p.2∈
        Icc (M+Buffer+Width+4*(N:ℝ)) (2*M-Buffer-Width-(N:ℝ))) ∧
      (Chunks.card:ℝ) ≤ (Y.card:ℝ)*(8*M/(N:ℝ)) ∧
      (∀ p∈Chunks, ∀ i,
        h p.1 (za p i)=(anchor p i:ℝ) ∧
        |za p i-probe p i| ≤ (N:ℝ)/16 ∧ za p i∈Icc M (2*M)) ∧
      (∀ p∈Chunks, match band p with
        | none => ∃ i, ¬(768*(anchor p i).den ≤ Q kmax ∧
            24576*R^2 ≤ c*(Q kmax:ℝ)*(anchor p i).den)
        | some k => k ≤ kmax ∧
            (∀ i, 768*(anchor p i).den ≤ Q k ∧
              24576*R^2 ≤ c*(Q k:ℝ)*(anchor p i).den)) ∧
      (∀ k ≤ kmax, ((Chunks.filter (fun p => band p=some (k+1))).card:ℝ) ≤
        (Y.card:ℝ)*Density k) ∧
      ((Chunks.filter (fun p => band p=none)).card:ℝ) ≤ (Y.card:ℝ)*Density kmax ∧
      (∑ y∈Y, ‖∑ j∈Finset.Ioc (A y) (B y),(𝐞 (f y j):ℂ)‖)^12 ≤
        2^11*(((kmax:ℝ)+2)^11*
          (((n:ℝ)*(Y.card:ℝ)*Density kmax)^12+
            ∑ k∈Finset.range (kmax+1),
              (∑ p∈Chunks.filter (fun p => band p=some k),
                ‖∑ j∈Finset.Ioc ((n:ℤ)*p.2) ((n:ℤ)*(p.2+1)),
                  (𝐞 (f p.1 j):ℂ)‖)^12)+Endpoint^12) := by
  exact double_difference_phase_subinterval_dyadic_band_reduction Y F rshift sshift n N Qbase kmax hNlink hc hU hn hd hw hsmall hshifts hy
    hT hM hR hreg hbound hlower hnegative hscale hQbase hQmax hBuffer hWidth hroom A B hA hab hB

#print axioms double_difference_phase_subinterval_dyadic_band_reduction

/-- Direct residue-grid transport keeps every original chunk and its selected
anchor. The existing constructed-reference sieve needs no shifted-cover enlargement. -/
private theorem eight_grid_exact_selected_transport
    (Chunks : Finset (ℝ × ℤ)) (Y : Finset ℝ) (n N Q : ℕ)
    (hNlink : N=8*n) (hN : 0 < N) (h : ℝ → ℝ → ℝ) (v : ℝ → ℤ → ℂ)
    {M Buffer c R : ℝ} (anchor : (ℝ × ℤ) → ℚ) (za : (ℝ × ℤ) → ℝ)
    (hphase : ∀ p∈Chunks, p.1∈Y)
    (hdeep : ∀ p∈Chunks, (n:ℝ)*p.2∈
      Icc (M+Buffer+4*(N:ℝ)) (2*M-Buffer-(N:ℝ)))
    (hanchors : ∀ p∈Chunks,
      |za p-((n:ℝ)*p.2-2*(N:ℝ))| ≤ (N:ℝ)/16 ∧
      h p.1 (za p)=(anchor p:ℝ) ∧
      768*(anchor p).den ≤ Q ∧
      24576*R^2 ≤ c*(Q:ℝ)*(anchor p).den) :
    let Grid := fun r : ℤ =>
      (Chunks.filter (fun p => p.2%8=r)).image (fun p => (p.1,p.2/8-2))
    let Point := fun (r : ℤ) (p : ℝ × ℤ) => (p.1,r+8*p.2+16)
    let Lsrc := fun (r : ℤ) (p : ℝ × ℤ) =>
      r*(n:ℤ)+(N:ℤ)*p.2+2*(N:ℤ)
    (∀ r, (Grid r).card ≤ Chunks.card ∧ (Grid r).image Prod.fst ⊆ Y ∧
      ∀ p∈Grid r,
        Point r p∈Chunks ∧ Lsrc r p=(n:ℤ)*(Point r p).2 ∧
        (Lsrc r p:ℝ)-2*(N:ℝ)∈
          Ioo (M+Buffer+(N:ℝ)) (2*M-Buffer-(N:ℝ)) ∧
        za (Point r p)∈Ioo ((Lsrc r p:ℝ)-2*(N:ℝ)-(N:ℝ)/8)
          ((Lsrc r p:ℝ)-2*(N:ℝ)+(N:ℝ)/8) ∧
        h p.1 (za (Point r p))=(anchor (Point r p):ℝ) ∧
        768*(anchor (Point r p)).den ≤ Q ∧
        24576*R^2 ≤ c*(Q:ℝ)*(anchor (Point r p)).den) ∧
    (∑ p∈Chunks, ‖∑ j∈Finset.Ioc ((n:ℤ)*p.2) ((n:ℤ)*(p.2+1)),v p.1 j‖)=
      ∑ r∈Finset.Ico (0:ℤ) 8,
        ∑ p∈Grid r, ‖∑ j∈Finset.Ioc (Lsrc r p) (Lsrc r p+n),v p.1 j‖ := by
  classical
  intro Grid Point Lsrc
  have hNp : (0:ℝ) < N := Nat.cast_pos.mpr hN
  have hNz : (N:ℤ)=8*(n:ℤ) := by exact_mod_cast hNlink
  have hstart r p : Lsrc r p=(n:ℤ)*(Point r p).2 := by
    dsimp only [Lsrc,Point]
    rw [hNz]
    ring
  have hstartR r p : (Lsrc r p:ℝ)=(n:ℝ)*(Point r p).2 := by
    exact_mod_cast hstart r p
  have hpoint r p (hp : p∈Grid r) : Point r p∈Chunks := by
    obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨hqC,hqmod⟩ := Finset.mem_filter.mp hq
    have heq : r+8*(q.2/8-2)+16=q.2 := by omega
    change (q.1,r+8*(q.2/8-2)+16)∈Chunks
    rw [heq]
    exact hqC
  refine ⟨?_,?_⟩
  · intro r
    refine ⟨Finset.card_image_le.trans (Finset.card_filter_le _ _),?_,?_⟩
    · intro y hy
      obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hy
      exact hphase (Point r p) (hpoint r p hp)
    · intro p hp
      have hq := hpoint r p hp
      have hd := hdeep (Point r p) hq
      have ha := hanchors (Point r p) hq
      rw [←hstartR r p] at hd ha
      refine ⟨hq,hstart r p,?_,?_,ha.2.1,ha.2.2.1,ha.2.2.2⟩
      · constructor <;> linarith only [hd.1,hd.2,hNp]
      · have hh := abs_le.mp ha.1
        constructor <;> linarith only [hh.1,hh.2,hNp]
  · rw [eight_grid_sum_reindex Chunks]
    apply Finset.sum_congr rfl
    intro r _
    apply Finset.sum_congr rfl
    intro p _
    have he : (n:ℤ)*((Point r p).2+1)=Lsrc r p+n := by rw [hstart]; ring
    change ‖∑ j∈Finset.Ioc ((n:ℤ)*(Point r p).2)
      ((n:ℤ)*((Point r p).2+1)),v p.1 j‖=_
    rw [he,←hstart]

example
    (Chunks : Finset (ℝ × ℤ)) (Y : Finset ℝ) (n N Q : ℕ)
    (hNlink : N=8*n) (hN : 0 < N) (h : ℝ → ℝ → ℝ) (v : ℝ → ℤ → ℂ)
    {M Buffer c R : ℝ} (anchor : (ℝ × ℤ) → ℚ) (za : (ℝ × ℤ) → ℝ)
    (hphase : ∀ p∈Chunks, p.1∈Y)
    (hdeep : ∀ p∈Chunks, (n:ℝ)*p.2∈
      Icc (M+Buffer+4*(N:ℝ)) (2*M-Buffer-(N:ℝ)))
    (hanchors : ∀ p∈Chunks,
      |za p-((n:ℝ)*p.2-2*(N:ℝ))| ≤ (N:ℝ)/16 ∧
      h p.1 (za p)=(anchor p:ℝ) ∧
      768*(anchor p).den ≤ Q ∧
      24576*R^2 ≤ c*(Q:ℝ)*(anchor p).den) :
    let Grid := fun r : ℤ =>
      (Chunks.filter (fun p => p.2%8=r)).image (fun p => (p.1,p.2/8-2))
    let Point := fun (r : ℤ) (p : ℝ × ℤ) => (p.1,r+8*p.2+16)
    let Lsrc := fun (r : ℤ) (p : ℝ × ℤ) =>
      r*(n:ℤ)+(N:ℤ)*p.2+2*(N:ℤ)
    (∀ r, (Grid r).card ≤ Chunks.card ∧ (Grid r).image Prod.fst ⊆ Y ∧
      ∀ p∈Grid r,
        Point r p∈Chunks ∧ Lsrc r p=(n:ℤ)*(Point r p).2 ∧
        (Lsrc r p:ℝ)-2*(N:ℝ)∈
          Ioo (M+Buffer+(N:ℝ)) (2*M-Buffer-(N:ℝ)) ∧
        za (Point r p)∈Ioo ((Lsrc r p:ℝ)-2*(N:ℝ)-(N:ℝ)/8)
          ((Lsrc r p:ℝ)-2*(N:ℝ)+(N:ℝ)/8) ∧
        h p.1 (za (Point r p))=(anchor (Point r p):ℝ) ∧
        768*(anchor (Point r p)).den ≤ Q ∧
        24576*R^2 ≤ c*(Q:ℝ)*(anchor (Point r p)).den) ∧
    (∑ p∈Chunks, ‖∑ j∈Finset.Ioc ((n:ℤ)*p.2) ((n:ℤ)*(p.2+1)),v p.1 j‖)=
      ∑ r∈Finset.Ico (0:ℤ) 8,
        ∑ p∈Grid r, ‖∑ j∈Finset.Ioc (Lsrc r p) (Lsrc r p+n),v p.1 j‖ := by
  exact eight_grid_exact_selected_transport Chunks Y n N Q hNlink hN h v anchor za hphase hdeep hanchors

#print axioms eight_grid_exact_selected_transport

/-- The actual selected chunks feed the original completed block estimate through
the direct residue grid. All anchor, root, interval and Fourier-cutoff inputs of
that estimate are derived from the same selected chunks; their cardinality is kept. -/
private theorem eventually_double_difference_direct_residue_grid_moment
    {csrc Usrc σ εloss : ℝ}
    (hcsrc : 0 < csrc) (hUsrc : 0 < Usrc)
    (hσ : 0 < σ) (hεloss : 0 < εloss) :
    let κ := modelPhaseThirdLower σ
    let L := max (32*Usrc^2/csrc^2)
      (64*(modelPhaseJetCoefficient σ 3+1)*Usrc/κ^2)
    let θ := 1/(8*(L+3))
    ∃ CF C Dtype : ℝ, 1 ≤ CF ∧ 0 < C ∧ 0 < Dtype ∧
    ∀ᶠ T : ℝ in Filter.atTop, ∀ (Chunks : Finset (ℝ × ℤ)) (Fsrc rshift sshift : ℝ → ℝ)
    (zaC : (ℝ × ℤ) → ℝ)
    (n Q K₀ N : ℕ) [NeZero K₀] (R Jsep : ℝ) (r : ℤ)
    {d Wmax M δ Bcut Bselect : ℝ}
    (Uref : ℕ) (anchorC : (ℝ × ℤ) → ℚ),
    N=8*n →
    let S := (Chunks.filter (fun p => p.2%8=r)).image (fun p => (p.1,p.2/8-2))
    let Z := fun _ : ℝ => r*(n:ℤ)
    let H := fun _ : ℝ × ℤ => n
    let lambda := csrc*T/(2*M^2)
    let Uband := Usrc*T/M^2
    let Vscale := max 1 (Uband*(N:ℝ)/(Q:ℝ))
    let Lsrc := fun i : ℝ × ℤ => Z i.1+(N:ℤ)*i.2+2*(N:ℤ)
    let Buffer := (56*(Uref:ℝ)/κ)*(N:ℝ)+(N:ℝ)/(σ*(σ+1)+3)+2
    (0 < d) → (0 ≤ Wmax) → (Wmax ≤ 1/4) → (2*Usrc*Wmax ≤ csrc/64) →
    (0 < T) →
    (0 < M) →
    (δ ≤ min (modelPhaseThirdLower σ) 1) →
    (0 < Q) → (Uband ≤ 1) →
    (∀ i∈Chunks, i.1∈Icc (1:ℝ) 2) →
    (∀ i∈Chunks, (n:ℝ)*i.2∈Icc (M+Buffer+4*(N:ℝ)) (2*M-Buffer-(N:ℝ))) →
    (∀ w, 0 < w → ContDiffAt ℝ ∞ Fsrc w) →
    (∀ w∈Icc (1/2:ℝ) 3, csrc ≤ iteratedDeriv 5 Fsrc w) →
    (∀ w∈Icc (1/2:ℝ) 3, ∀ n, 1 ≤ n → n ≤ 7 → |iteratedDeriv n Fsrc w| ≤ Usrc) →
    (∀ w∈Icc (1/2:ℝ) 3,
      csrc ≤ |(iteratedDeriv 5 Fsrc w)^2-iteratedDeriv 4 Fsrc w*iteratedDeriv 6 Fsrc w|) →
    (∀ w∈Icc (1/2:ℝ) 3, iteratedDeriv 4 Fsrc w ≤ -csrc) →
    (2 ≤ M) →
    (0 < N) →
    (0 < Jsep) → (Jsep ≤ M) → ((N:ℝ) ≤ M) → (Wmax*Jsep ≤ 1) →
    ((Q:ℝ)*(N:ℝ) ≤ (K₀:ℝ)*R^2) →
    7*(N:ℝ)+2 ≤ M/4 →
    (3*Usrc)*(6*(N:ℝ)+1)^4 ≤ M*(N:ℝ)*R^2 →
    (3*Usrc/4)*(6*(N:ℝ)+1)^2 ≤ (N:ℝ)*R^2 →
    63*(Usrc/(2*(N:ℝ)*R^2))*(Q:ℝ)*(N:ℝ)^2 ≤ K₀ →
    (∀ i∈Chunks, ∀ j∈Chunks, i.1≠j.1 → 1 ≤ Jsep*|i.1-j.1|) →
    (∀ y∈Chunks.image Prod.fst,
      0 ≤ rshift y ∧ 0 ≤ sshift y ∧ rshift y*sshift y=d*y ∧ rshift y+sshift y ≤ Wmax) →
    let Φ := fun y u =>
      (Fsrc u-Fsrc (u+rshift y)-Fsrc (u+sshift y)+Fsrc (u+rshift y+sshift y))/d
    (∀ i∈Chunks, Expdb.IsApproximateModelPhaseFunction (Φ i.1) σ 4 δ) →
    let f := fun p w => T*Φ p (w/M)
    (∀ i∈Chunks,
      |zaC i-((n:ℝ)*i.2-2*(N:ℝ))| ≤ (N:ℝ)/16 ∧
      iteratedDeriv 2 (f i.1) (zaC i)/2=(anchorC i:ℝ) ∧
      768*(anchorC i).den ≤ Q ∧
      24576*R^2 ≤ csrc*(Q:ℝ)*(anchorC i).den) →

    (1 ≤ R) → (R ≤ M) → (T*(N:ℝ)*R^2=M^3) →
    (0 < Bcut) →
    (1 ≤ Uref) →
    (2+168/κ ≤ Bselect) → (7*Bcut ≤ κ*Bselect) →
    (Bselect^2*(Uref:ℝ)^3*R^2 ≤ (N:ℝ)^2) →
    (R ≤ (Q:ℝ)) →
    ((Uref:ℝ) ≤ ((N:ℝ)/(Q:ℝ))^((2:ℝ)/3)/Bselect) →
    ((N:ℝ)^10 ≤ M^3*R^7) →
    (Q:ℝ) ≤ (N:ℝ) →
    ((N:ℝ)^2 ≤ M ∨ (1 ≤ M ∧ (N:ℝ) ≤ T ∧ R^2 ≤ T)) → (Uref:ℝ) ≤ R^2 →
    let Cphys := σ*(σ+1)+1
    let c := κ/6
    let J := Cphys/6
    let B := max 1 (max (2*Real.sqrt J) (8*J*Real.sqrt J/(3*c)))
    B*R^2/(N:ℝ)^2 ≤ 1/2 →
    (N:ℝ) ≤ R^2 → R ≤ (N:ℝ) → (N:ℝ)^3 ≤ M*R^2 →
    2*R^2 ≤ (Q:ℝ)*(N:ℝ) →
    2 ≤ (N:ℝ) →
    csrc ≤ 4*κ/(Cphys+2) →
    let NarrowCap := (4/θ+3)*(8*Usrc/(csrc*θ)+3)
    let Cap := 3*NarrowCap
    let μ₀ := csrc*T/(12*M^3)
    let U₀ := Usrc*T/(2*M^3)
    let Δtype := (16*U₀/μ₀)*Real.sqrt (U₀*(Q:ℝ)^3)*Real.sqrt K₀/(6*(K₀:ℝ)^2)
    let C₂ := modelPhaseJetCoefficient σ 2+δ
    let C₃ := modelPhaseJetCoefficient σ 3+δ
    let Ct := C₂/2+5*C₃/12
    let Cc := C₂/κ+C₃/(2*κ)
    let Δ := (37*B/2+16*B*Cc+2*Ct+2*Cc)*(Q:ℝ)/(N:ℝ)
    let Ccurv := (4/κ)*(B+2*quarticReciprocalConstant σ δ)
    let D := Δ+quarticNonlinearResidualConstant σ δ*(2*(Q:ℝ))/(N:ℝ)
    let Kres := 4*(37*B/2+16*B*Cc+2*Ct+2*Cc+
      2*quarticNonlinearResidualConstant σ δ)/κ
    let Esize := κ/(16*(Cphys+2))
    let Dbase := 37*B/2+16*B*Cc+2*Ct+2*Cc+2*quarticNonlinearResidualConstant σ δ
    let Tbase := (2/κ)*(B+2*quarticReciprocalConstant σ δ)
    2*3840*128^2*105*(Dbase+64*Tbase*Esize^2) ≤ Bselect*Esize →
    D ≤ 1/2 → Δ < 1/2 → 61*Ccurv*Cphys ≤ Bcut →
    let Lunit := 2*κ/Cphys
    let Gamma := Cphys/κ
    let Cthird := Gamma*(32*Kres+9*quarticReciprocalConstant σ δ)
    let Cpack := 64*Cphys*(Gamma^2*Cthird+Gamma*(modelPhaseJetCoefficient σ 3+δ)/κ)/κ
    let Cfirst := 128*Cphys*(Gamma^2*Cthird+Gamma*(modelPhaseJetCoefficient σ 3+δ)/κ)/κ^2
    let Cgap := 64*Cphys*(Gamma^2*B+Gamma*(modelPhaseJetCoefficient σ 3+δ)/κ)/κ
    let Cmain := 4*(2*Cfirst/Lunit^3)^((3:ℝ)⁻¹)+2
    let Ctail := 4*Cpack/Lunit^2+Cgap
    let Klarge := 60*588*(Uband/lambda)^2*Uband^2*(R^8/(N:ℝ)^4)*
      (Cmain*((Q:ℝ)/(Uband*(N:ℝ)))^((2:ℝ)/3)+Ctail/(Uref:ℝ))
    let Y := S.image Prod.fst
    let Wphys := (144*Usrc/(csrc*κ))*(R^2/(Q:ℝ))
    let Mass := Vscale*Dtype*(2+θ*(Uband+1/lambda))*(Y.card:ℝ)*(M/(N:ℝ))*(1+Δtype*Jsep)+
      (Y.card:ℝ)^2*Klarge*T^εloss
    let Error := (S.card:ℝ)*
      (Real.sqrt (3*(N:ℝ))*Real.log (6*(N:ℝ))+36*Usrc*R^2/(csrc*κ*(N:ℝ)))
    (∑ i∈S, ‖∑ n∈Finset.Ioc (Lsrc i) (Lsrc i+H i),(𝐞 (f i.1 n):ℂ)‖)^12 ≤
      CF^12*2^11*((1+Real.log K₀)^12*Wphys^6*
        (C*(K₀:ℝ)^((12:ℝ)+εloss)*Cap^11*(2*(S.card:ℝ))^10*Mass)+Error^12) := by
  classical
  intro κ L θ
  obtain ⟨CF,C,Dtype,hCF,hC,hDtype,hsource⟩ :=
    eventually_double_difference_original_selected_block_moment hcsrc hUsrc hσ hεloss
  refine ⟨CF,C,Dtype,hCF,hC,hDtype,?_⟩
  filter_upwards [hsource] with T hfamily
  intro Chunks Fsrc rshift sshift zaC n Q K₀ N instK R Jsep r
    d Wmax M δ Bcut Bselect Uref anchorC hNlink S Z H
    lambda Uband Vscale Lsrc Buffer hd hw hwcap hsmallShift hT hM hδ hQ hUbandCap
    hy hdeep hreg hlower hjets htests hnegative hMtwo hN
    hJsep hJM hNM hwJ hmesh hfourBuffer hfourBudget hquadBudget hfullmesh
    hseparation hshifts Φ hmodel f hanchors
    hR hRM hscale hBcut hUref hBselectSize hcutMargin hselectedWrap hRQ
    hselectedUpper hscaleTen hQN hNsqM hUR
    Cphys c J B hsmall hNR hRN hNcube hminscale hNtwo hanchorBudget
    NarrowCap Cap μ₀ U₀ Δtype C₂ C₃ Ct Cc Δ Ccurv D Kres Esize Dbase Tbase
    hsize hD hΔ hBsize Lunit Gamma Cthird Cpack Cfirst Cgap Cmain Ctail Klarge Y Wphys Mass Error
  let Point := fun p : ℝ × ℤ => (p.1,r+8*p.2+16)
  let za := fun p => zaC (Point p)
  let anchor := fun p => anchorC (Point p)
  let Fmodel := fun (i : ℝ × ℤ) u => Φ i.1 u
  let ε := κ/(16*(Cphys+2)*R^2)
  have hκ : 0 < κ := modelPhaseThirdLower_pos hσ
  have hCp : 0 < Cphys+2 := by dsimp only [Cphys]; positivity
  have hRp : 0 < R := zero_lt_one.trans_le hR
  obtain ⟨hgrids,_⟩ := eight_grid_exact_selected_transport Chunks
    (Chunks.image Prod.fst) n N Q hNlink hN
    (fun y w => iteratedDeriv 2 (f y) w/2) (fun y j => (𝐞 (f y j):ℂ))
    anchorC zaC (fun p hp => Finset.mem_image_of_mem Prod.fst hp) hdeep hanchors
  have hg := hgrids r
  have hmem i (hi : i∈S) : Point i∈Chunks := (hg.2.2 i hi).1
  have hbuffer i (hi : i∈S) :
      (Lsrc i:ℝ)-2*(N:ℝ)∈Ioo (M+Buffer+(N:ℝ)) (2*M-Buffer-(N:ℝ)) :=
    (hg.2.2 i hi).2.2.1
  have ha i (hi : i∈S) :
      za i∈Ioo ((Lsrc i:ℝ)-2*(N:ℝ)-(N:ℝ)/8)
        ((Lsrc i:ℝ)-2*(N:ℝ)+(N:ℝ)/8) ∧
      iteratedDeriv 2 (f i.1) (za i)/2=(anchor i:ℝ) ∧
      768*(anchor i).den ≤ Q ∧
      24576*R^2 ≤ csrc*(Q:ℝ)*(anchor i).den := (hg.2.2 i hi).2.2.2
  have hyS i (hi : i∈S) : i.1∈Icc (1:ℝ) 2 := hy (Point i) (hmem i hi)
  have hHS i (_hi : i∈S) : H i ≤ N := by dsimp only [H]; omega
  have hden i (hi : i∈S) : 2*(anchor i).den ≤ Q := by
    have hh := (ha i hi).2.2.1
    omega
  have hmajor i (hi : i∈S) : 128*R^2 ≤ csrc*(Q:ℝ)*(anchor i).den := by
    have hh := (ha i hi).2.2.2
    nlinarith only [hh,sq_nonneg R]
  have hsep i (hi : i∈S) j (hj : j∈S) (hne : i.1≠j.1) :
      1 ≤ Jsep*|i.1-j.1| := hseparation (Point i) (hmem i hi) (Point j) (hmem j hj) hne
  have hshift y (hyY : y∈S.image Prod.fst) :
      0 ≤ rshift y ∧ 0 ≤ sshift y ∧ rshift y*sshift y=d*y ∧ rshift y+sshift y ≤ Wmax :=
    hshifts y (hg.2.1 hyY)
  have hmodels i (hi : i∈S) : Expdb.IsApproximateModelPhaseFunction (Fmodel i) σ 4 δ :=
    hmodel (Point i) (hmem i hi)
  have haroot i (hi : i∈S) :
      za i∈Ioo ((Lsrc i:ℝ)-2*(N:ℝ)-(N:ℝ)/8)
        ((Lsrc i:ℝ)-2*(N:ℝ)+(N:ℝ)/8) ∧
      iteratedDeriv 2 (f i.1) (za i)/2=(anchor i:ℝ) :=
    ⟨(ha i hi).1,(ha i hi).2.1⟩
  have hcut i (hi : i∈S) : 256*((anchor i).den:ℝ) ≤ (Q:ℝ)/3 := by
    have hh : (768:ℝ)*((anchor i).den:ℝ) ≤ Q := by exact_mod_cast (ha i hi).2.2.1
    linarith only [hh]
  have hcount i (hi : i∈S) : 256 ≤ (2*ε)*((Q:ℝ)/3)*(anchor i).den := by
    have hm := (ha i hi).2.2.2
    have hb : csrc*(Cphys+2) ≤ 4*κ := (le_div_iff₀ hCp).mp hanchorBudget
    have hh := mul_le_mul_of_nonneg_right hm hCp.le
    have hb' := mul_le_mul_of_nonneg_right hb
      (show 0 ≤ (Q:ℝ)*((anchor i).den:ℝ) by positivity)
    have he : (2*ε)*((Q:ℝ)/3)*(anchor i).den =
        κ*(Q:ℝ)*(anchor i).den/(24*(Cphys+2)*R^2) := by
      dsimp only [ε]
      field_simp
      ring
    rw [he]
    apply (le_div_iff₀ (show 0 < 24*(Cphys+2)*R^2 by positivity)).mpr
    nlinarith only [hh,hb']
  exact hfamily S Fsrc rshift sshift H za Q K₀ N R Jsep Z
    (d:=d) (Wmax:=Wmax) (M:=M) (δ:=δ) (Bcut:=Bcut) (Bselect:=Bselect)
    Uref anchor hd hw hwcap hsmallShift hT hM hδ hQ hUbandCap
    hyS hbuffer hreg hlower hjets htests hnegative hMtwo hN
    hJsep hJM hNM hwJ hmesh hHS hfourBuffer hfourBudget hquadBudget hfullmesh hden hmajor
    hsep hshift hmodels haroot
    hR hRM hscale hBcut hUref hBselectSize hcutMargin hselectedWrap hRQ
    hselectedUpper hscaleTen hQN hNsqM hUR
    hsmall hNR hRN hNcube hminscale hNtwo hanchorBudget hcut hcount
    hsize hD hΔ hBsize

example
    {csrc Usrc σ εloss : ℝ}
    (hcsrc : 0 < csrc) (hUsrc : 0 < Usrc)
    (hσ : 0 < σ) (hεloss : 0 < εloss) :
    let κ := modelPhaseThirdLower σ
    let L := max (32*Usrc^2/csrc^2)
      (64*(modelPhaseJetCoefficient σ 3+1)*Usrc/κ^2)
    let θ := 1/(8*(L+3))
    ∃ CF C Dtype : ℝ, 1 ≤ CF ∧ 0 < C ∧ 0 < Dtype ∧
    ∀ᶠ T : ℝ in Filter.atTop, ∀ (Chunks : Finset (ℝ × ℤ)) (Fsrc rshift sshift : ℝ → ℝ)
    (zaC : (ℝ × ℤ) → ℝ)
    (n Q K₀ N : ℕ) [NeZero K₀] (R Jsep : ℝ) (r : ℤ)
    {d Wmax M δ Bcut Bselect : ℝ}
    (Uref : ℕ) (anchorC : (ℝ × ℤ) → ℚ),
    N=8*n →
    let S := (Chunks.filter (fun p => p.2%8=r)).image (fun p => (p.1,p.2/8-2))
    let Z := fun _ : ℝ => r*(n:ℤ)
    let H := fun _ : ℝ × ℤ => n
    let lambda := csrc*T/(2*M^2)
    let Uband := Usrc*T/M^2
    let Vscale := max 1 (Uband*(N:ℝ)/(Q:ℝ))
    let Lsrc := fun i : ℝ × ℤ => Z i.1+(N:ℤ)*i.2+2*(N:ℤ)
    let Buffer := (56*(Uref:ℝ)/κ)*(N:ℝ)+(N:ℝ)/(σ*(σ+1)+3)+2
    (0 < d) → (0 ≤ Wmax) → (Wmax ≤ 1/4) → (2*Usrc*Wmax ≤ csrc/64) →
    (0 < T) →
    (0 < M) →
    (δ ≤ min (modelPhaseThirdLower σ) 1) →
    (0 < Q) → (Uband ≤ 1) →
    (∀ i∈Chunks, i.1∈Icc (1:ℝ) 2) →
    (∀ i∈Chunks, (n:ℝ)*i.2∈Icc (M+Buffer+4*(N:ℝ)) (2*M-Buffer-(N:ℝ))) →
    (∀ w, 0 < w → ContDiffAt ℝ ∞ Fsrc w) →
    (∀ w∈Icc (1/2:ℝ) 3, csrc ≤ iteratedDeriv 5 Fsrc w) →
    (∀ w∈Icc (1/2:ℝ) 3, ∀ n, 1 ≤ n → n ≤ 7 → |iteratedDeriv n Fsrc w| ≤ Usrc) →
    (∀ w∈Icc (1/2:ℝ) 3,
      csrc ≤ |(iteratedDeriv 5 Fsrc w)^2-iteratedDeriv 4 Fsrc w*iteratedDeriv 6 Fsrc w|) →
    (∀ w∈Icc (1/2:ℝ) 3, iteratedDeriv 4 Fsrc w ≤ -csrc) →
    (2 ≤ M) →
    (0 < N) →
    (0 < Jsep) → (Jsep ≤ M) → ((N:ℝ) ≤ M) → (Wmax*Jsep ≤ 1) →
    ((Q:ℝ)*(N:ℝ) ≤ (K₀:ℝ)*R^2) →
    7*(N:ℝ)+2 ≤ M/4 →
    (3*Usrc)*(6*(N:ℝ)+1)^4 ≤ M*(N:ℝ)*R^2 →
    (3*Usrc/4)*(6*(N:ℝ)+1)^2 ≤ (N:ℝ)*R^2 →
    63*(Usrc/(2*(N:ℝ)*R^2))*(Q:ℝ)*(N:ℝ)^2 ≤ K₀ →
    (∀ i∈Chunks, ∀ j∈Chunks, i.1≠j.1 → 1 ≤ Jsep*|i.1-j.1|) →
    (∀ y∈Chunks.image Prod.fst,
      0 ≤ rshift y ∧ 0 ≤ sshift y ∧ rshift y*sshift y=d*y ∧ rshift y+sshift y ≤ Wmax) →
    let Φ := fun y u =>
      (Fsrc u-Fsrc (u+rshift y)-Fsrc (u+sshift y)+Fsrc (u+rshift y+sshift y))/d
    (∀ i∈Chunks, Expdb.IsApproximateModelPhaseFunction (Φ i.1) σ 4 δ) →
    let f := fun p w => T*Φ p (w/M)
    (∀ i∈Chunks,
      |zaC i-((n:ℝ)*i.2-2*(N:ℝ))| ≤ (N:ℝ)/16 ∧
      iteratedDeriv 2 (f i.1) (zaC i)/2=(anchorC i:ℝ) ∧
      768*(anchorC i).den ≤ Q ∧
      24576*R^2 ≤ csrc*(Q:ℝ)*(anchorC i).den) →

    (1 ≤ R) → (R ≤ M) → (T*(N:ℝ)*R^2=M^3) →
    (0 < Bcut) →
    (1 ≤ Uref) →
    (2+168/κ ≤ Bselect) → (7*Bcut ≤ κ*Bselect) →
    (Bselect^2*(Uref:ℝ)^3*R^2 ≤ (N:ℝ)^2) →
    (R ≤ (Q:ℝ)) →
    ((Uref:ℝ) ≤ ((N:ℝ)/(Q:ℝ))^((2:ℝ)/3)/Bselect) →
    ((N:ℝ)^10 ≤ M^3*R^7) →
    (Q:ℝ) ≤ (N:ℝ) →
    ((N:ℝ)^2 ≤ M ∨ (1 ≤ M ∧ (N:ℝ) ≤ T ∧ R^2 ≤ T)) → (Uref:ℝ) ≤ R^2 →
    let Cphys := σ*(σ+1)+1
    let c := κ/6
    let J := Cphys/6
    let B := max 1 (max (2*Real.sqrt J) (8*J*Real.sqrt J/(3*c)))
    B*R^2/(N:ℝ)^2 ≤ 1/2 →
    (N:ℝ) ≤ R^2 → R ≤ (N:ℝ) → (N:ℝ)^3 ≤ M*R^2 →
    2*R^2 ≤ (Q:ℝ)*(N:ℝ) →
    2 ≤ (N:ℝ) →
    csrc ≤ 4*κ/(Cphys+2) →
    let NarrowCap := (4/θ+3)*(8*Usrc/(csrc*θ)+3)
    let Cap := 3*NarrowCap
    let μ₀ := csrc*T/(12*M^3)
    let U₀ := Usrc*T/(2*M^3)
    let Δtype := (16*U₀/μ₀)*Real.sqrt (U₀*(Q:ℝ)^3)*Real.sqrt K₀/(6*(K₀:ℝ)^2)
    let C₂ := modelPhaseJetCoefficient σ 2+δ
    let C₃ := modelPhaseJetCoefficient σ 3+δ
    let Ct := C₂/2+5*C₃/12
    let Cc := C₂/κ+C₃/(2*κ)
    let Δ := (37*B/2+16*B*Cc+2*Ct+2*Cc)*(Q:ℝ)/(N:ℝ)
    let Ccurv := (4/κ)*(B+2*quarticReciprocalConstant σ δ)
    let D := Δ+quarticNonlinearResidualConstant σ δ*(2*(Q:ℝ))/(N:ℝ)
    let Kres := 4*(37*B/2+16*B*Cc+2*Ct+2*Cc+
      2*quarticNonlinearResidualConstant σ δ)/κ
    let Esize := κ/(16*(Cphys+2))
    let Dbase := 37*B/2+16*B*Cc+2*Ct+2*Cc+2*quarticNonlinearResidualConstant σ δ
    let Tbase := (2/κ)*(B+2*quarticReciprocalConstant σ δ)
    2*3840*128^2*105*(Dbase+64*Tbase*Esize^2) ≤ Bselect*Esize →
    D ≤ 1/2 → Δ < 1/2 → 61*Ccurv*Cphys ≤ Bcut →
    let Lunit := 2*κ/Cphys
    let Gamma := Cphys/κ
    let Cthird := Gamma*(32*Kres+9*quarticReciprocalConstant σ δ)
    let Cpack := 64*Cphys*(Gamma^2*Cthird+Gamma*(modelPhaseJetCoefficient σ 3+δ)/κ)/κ
    let Cfirst := 128*Cphys*(Gamma^2*Cthird+Gamma*(modelPhaseJetCoefficient σ 3+δ)/κ)/κ^2
    let Cgap := 64*Cphys*(Gamma^2*B+Gamma*(modelPhaseJetCoefficient σ 3+δ)/κ)/κ
    let Cmain := 4*(2*Cfirst/Lunit^3)^((3:ℝ)⁻¹)+2
    let Ctail := 4*Cpack/Lunit^2+Cgap
    let Klarge := 60*588*(Uband/lambda)^2*Uband^2*(R^8/(N:ℝ)^4)*
      (Cmain*((Q:ℝ)/(Uband*(N:ℝ)))^((2:ℝ)/3)+Ctail/(Uref:ℝ))
    let Y := S.image Prod.fst
    let Wphys := (144*Usrc/(csrc*κ))*(R^2/(Q:ℝ))
    let Mass := Vscale*Dtype*(2+θ*(Uband+1/lambda))*(Y.card:ℝ)*(M/(N:ℝ))*(1+Δtype*Jsep)+
      (Y.card:ℝ)^2*Klarge*T^εloss
    let Error := (S.card:ℝ)*
      (Real.sqrt (3*(N:ℝ))*Real.log (6*(N:ℝ))+36*Usrc*R^2/(csrc*κ*(N:ℝ)))
    (∑ i∈S, ‖∑ n∈Finset.Ioc (Lsrc i) (Lsrc i+H i),(𝐞 (f i.1 n):ℂ)‖)^12 ≤
      CF^12*2^11*((1+Real.log K₀)^12*Wphys^6*
        (C*(K₀:ℝ)^((12:ℝ)+εloss)*Cap^11*(2*(S.card:ℝ))^10*Mass)+Error^12) := by
  exact eventually_double_difference_direct_residue_grid_moment hcsrc hUsrc hσ hεloss

#print axioms eventually_double_difference_direct_residue_grid_moment

/-- Original phase-dependent subinterval sums consume the SAME constructed least
bands, roots, direct residue grids and completed-block moments. The final inequality
retains actual grid cardinalities, terminal mass and both endpoint strips. -/
private theorem eventually_double_difference_all_band_subinterval_moment
    {csrc Usrc σ εloss : ℝ}
    (hcsrc : 0 < csrc) (hUsrc : 0 < Usrc)
    (hσ : 0 < σ) (hεloss : 0 < εloss) :
    let κ := modelPhaseThirdLower σ
    let L := max (32*Usrc^2/csrc^2)
      (64*(modelPhaseJetCoefficient σ 3+1)*Usrc/κ^2)
    let θ := 1/(8*(L+3))
    ∃ CF C Dtype : ℝ, 1 ≤ CF ∧ 0 < C ∧ 0 < Dtype ∧
    ∀ᶠ T : ℝ in Filter.atTop, ∀ (Fsrc rshift sshift : ℝ → ℝ) (Y : Finset ℝ)
    (n N Qbase kmax : ℕ) (Kmesh Usel : ℕ → ℕ) (R Jsep : ℝ)
    {d Wmax M δ Bcut Bselect : ℝ},
    (∀ k, 0 < Kmesh k) → N=8*n →
    0 < d → 0 ≤ Wmax → Wmax ≤ 1/4 → 2*Usrc*Wmax ≤ csrc/64 →
    0 < T → 2 ≤ M → 0 < N → δ ≤ min κ 1 →
    1 ≤ R → R ≤ M → 0 < Jsep → Jsep ≤ M → (N:ℝ) ≤ M → Wmax*Jsep ≤ 1 →
    (∀ y∈Y, y∈Icc (1:ℝ) 2) →
    (∀ y∈Y, ∀ z∈Y, y≠z → 1 ≤ Jsep*|y-z|) →
    (∀ y∈Y, 0 ≤ rshift y ∧ 0 ≤ sshift y ∧
      rshift y*sshift y=d*y ∧ rshift y+sshift y ≤ Wmax) →
    (∀ w, 0 < w → ContDiffAt ℝ ∞ Fsrc w) →
    (∀ w∈Icc (1/2:ℝ) 3, csrc ≤ iteratedDeriv 5 Fsrc w) →
    (∀ w∈Icc (1/2:ℝ) 3, ∀ j, 1 ≤ j → j ≤ 7 → |iteratedDeriv j Fsrc w| ≤ Usrc) →
    (∀ w∈Icc (1/2:ℝ) 3,
      csrc ≤ |(iteratedDeriv 5 Fsrc w)^2-iteratedDeriv 4 Fsrc w*iteratedDeriv 6 Fsrc w|) →
    (∀ w∈Icc (1/2:ℝ) 3, iteratedDeriv 4 Fsrc w ≤ -csrc) →
    let Φ := fun y u =>
      (Fsrc u-Fsrc (u+rshift y)-Fsrc (u+sshift y)+Fsrc (u+rshift y+sshift y))/d
    (∀ y∈Y, Expdb.IsApproximateModelPhaseFunction (Φ y) σ 4 δ) →
    T*(N:ℝ)*R^2=M^3 →
    7*(N:ℝ)+2 ≤ M/4 →
    (3*Usrc)*(6*(N:ℝ)+1)^4 ≤ M*(N:ℝ)*R^2 →
    (3*Usrc/4)*(6*(N:ℝ)+1)^2 ≤ (N:ℝ)*R^2 →
    0 < Bcut → 2+168/κ ≤ Bselect → 7*Bcut ≤ κ*Bselect →
    (N:ℝ)^10 ≤ M^3*R^7 →
    ((N:ℝ)^2 ≤ M ∨ (1 ≤ M ∧ (N:ℝ) ≤ T ∧ R^2 ≤ T)) →
    let Q := fun k : ℕ => Qbase*2^k
    768 ≤ Qbase → (N:ℝ)*(Q kmax:ℝ) ≤ M →
    let Cphys := σ*(σ+1)+1
    let c := κ/6
    let J := Cphys/6
    let B := max 1 (max (2*Real.sqrt J) (8*J*Real.sqrt J/(3*c)))
    B*R^2/(N:ℝ)^2 ≤ 1/2 →
    (N:ℝ) ≤ R^2 → R ≤ (N:ℝ) → (N:ℝ)^3 ≤ M*R^2 →
    2 ≤ (N:ℝ) → csrc ≤ 4*κ/(Cphys+2) →
    let lambda := csrc*T/(2*M^2)
    let Uband := Usrc*T/M^2
    Uband ≤ 1 →
    let NarrowCap := (4/θ+3)*(8*Usrc/(csrc*θ)+3)
    let Cap := 3*NarrowCap
    let μ₀ := csrc*T/(12*M^3)
    let U₀ := Usrc*T/(2*M^3)
    let C₂ := modelPhaseJetCoefficient σ 2+δ
    let C₃ := modelPhaseJetCoefficient σ 3+δ
    let Ct := C₂/2+5*C₃/12
    let Cc := C₂/κ+C₃/(2*κ)
    let Ccurv := (4/κ)*(B+2*quarticReciprocalConstant σ δ)
    let Kres := 4*(37*B/2+16*B*Cc+2*Ct+2*Cc+
      2*quarticNonlinearResidualConstant σ δ)/κ
    let Esize := κ/(16*(Cphys+2))
    let Dbase := 37*B/2+16*B*Cc+2*Ct+2*Cc+2*quarticNonlinearResidualConstant σ δ
    let Tbase := (2/κ)*(B+2*quarticReciprocalConstant σ δ)
    2*3840*128^2*105*(Dbase+64*Tbase*Esize^2) ≤ Bselect*Esize →
    61*Ccurv*Cphys ≤ Bcut →
    let Lunit := 2*κ/Cphys
    let Gamma := Cphys/κ
    let Cthird := Gamma*(32*Kres+9*quarticReciprocalConstant σ δ)
    let Cpack := 64*Cphys*(Gamma^2*Cthird+Gamma*(modelPhaseJetCoefficient σ 3+δ)/κ)/κ
    let Cfirst := 128*Cphys*(Gamma^2*Cthird+Gamma*(modelPhaseJetCoefficient σ 3+δ)/κ)/κ^2
    let Cgap := 64*Cphys*(Gamma^2*B+Gamma*(modelPhaseJetCoefficient σ 3+δ)/κ)/κ
    let Cmain := 4*(2*Cfirst/Lunit^3)^((3:ℝ)⁻¹)+2
    let Ctail := 4*Cpack/Lunit^2+Cgap
    let Δtype := fun k : ℕ =>
      (16*U₀/μ₀)*Real.sqrt (U₀*(Q k:ℝ)^3)*Real.sqrt (Kmesh k)/(6*(Kmesh k:ℝ)^2)
    let Δ := fun k : ℕ => (37*B/2+16*B*Cc+2*Ct+2*Cc)*(Q k:ℝ)/(N:ℝ)
    let D := fun k : ℕ => Δ k+quarticNonlinearResidualConstant σ δ*(2*(Q k:ℝ))/(N:ℝ)
    let Buffer := fun k : ℕ => (56*(Usel k:ℝ)/κ)*(N:ℝ)+(N:ℝ)/(Cphys+2)+2
    (∀ k ≤ kmax,
      63*(Usrc/(2*(N:ℝ)*R^2))*(Q k:ℝ)*(N:ℝ)^2 ≤ Kmesh k ∧
      (Q k:ℝ)*(N:ℝ) ≤ (Kmesh k:ℝ)*R^2 ∧
      1 ≤ Usel k ∧ Bselect^2*(Usel k:ℝ)^3*R^2 ≤ (N:ℝ)^2 ∧
      R ≤ (Q k:ℝ) ∧
      (Usel k:ℝ) ≤ ((N:ℝ)/(Q k:ℝ))^((2:ℝ)/3)/Bselect ∧
      (Q k:ℝ) ≤ (N:ℝ) ∧ (Usel k:ℝ) ≤ R^2 ∧
      2*R^2 ≤ (Q k:ℝ)*(N:ℝ) ∧ D k ≤ 1/2 ∧ Δ k < 1/2) →
    (∀ k ≤ kmax, Usel k ≤ Usel 0) →
    2*Buffer 0+6*(N:ℝ) ≤ M →
    let f := fun y w => T*Φ y (w/M)
    let Vscale := fun k : ℕ => max 1 (Uband*(N:ℝ)/(Q k:ℝ))
    let Klarge := fun k : ℕ => 60*588*(Uband/lambda)^2*Uband^2*(R^8/(N:ℝ)^4)*
      (Cmain*((Q k:ℝ)/(Uband*(N:ℝ)))^((2:ℝ)/3)+Ctail/(Usel k:ℝ))
    let Wphys := fun k : ℕ => (144*Usrc/(csrc*κ))*(R^2/(Q k:ℝ))
    let PointError := Real.sqrt (3*(N:ℝ))*Real.log (6*(N:ℝ))+
      36*Usrc*R^2/(csrc*κ*(N:ℝ))
    let FamilyBound := fun (k : ℕ) (P : Finset (ℝ × ℤ)) =>
      let YP := P.image Prod.fst
      let Mass := Vscale k*Dtype*(2+θ*(Uband+1/lambda))*(YP.card:ℝ)*(M/(N:ℝ))*
        (1+Δtype k*Jsep)+(YP.card:ℝ)^2*Klarge k*T^εloss
      CF^12*2^11*((1+Real.log (Kmesh k))^12*Wphys k^6*
        (C*(Kmesh k:ℝ)^((12:ℝ)+εloss)*Cap^11*(2*(P.card:ℝ))^10*Mass)+
        ((P.card:ℝ)*PointError)^12)
    let CtailBand := 4*Usrc*(64/csrc)^2+192/csrc
    let ClowBand := (2*Usrc+csrc/32)*(3072/csrc)^2+3072/csrc
    let CerrorBand := (768:ℝ)^2*CtailBand+ClowBand
    let Density := fun k => 128*CerrorBand*(M*R^2/((N:ℝ)*(Q k:ℝ)^2))*
      (2+Real.log (512*R^2/(csrc*((Q k:ℝ)/768))+1))
    let Endpoint := (Y.card:ℝ)*(2*Buffer 0+6*(N:ℝ)+2*(n:ℝ))
    ∀ A Bint : ℝ → ℤ, (∀ y∈Y, ⌈M⌉ ≤ A y) →
    (∀ y∈Y, A y ≤ Bint y) → (∀ y∈Y, Bint y ≤ ⌊2*M⌋) →
    ∃ (Chunks : Finset (ℝ × ℤ)) (band : (ℝ × ℤ) → Option ℕ),
      (Chunks.card:ℝ) ≤ (Y.card:ℝ)*(8*M/(N:ℝ)) ∧
      (∀ k ≤ kmax, ((Chunks.filter (fun p => band p=some (k+1))).card:ℝ) ≤
        (Y.card:ℝ)*Density k) ∧
      ((Chunks.filter (fun p => band p=none)).card:ℝ) ≤ (Y.card:ℝ)*Density kmax ∧
      let Selected := fun k => Chunks.filter (fun p => band p=some k)
      let Grid := fun (k : ℕ) (r : ℤ) =>
        ((Selected k).filter (fun p => p.2%8=r)).image (fun p => (p.1,p.2/8-2))
      (∀ k r, (Grid k r).card ≤ (Selected k).card ∧ (Grid k r).image Prod.fst ⊆ Y) ∧
      (∑ y∈Y, ‖∑ j∈Finset.Ioc (A y) (Bint y),(𝐞 (f y j):ℂ)‖)^12 ≤
        2^11*(((kmax:ℝ)+2)^11*
          (((n:ℝ)*(Y.card:ℝ)*Density kmax)^12+
            (8:ℝ)^11*∑ k∈Finset.range (kmax+1),
              ∑ r∈Finset.Ico (0:ℤ) 8, FamilyBound k (Grid k r))+
            Endpoint^12)
 := by
  classical
  intro κ L θ
  obtain ⟨CF,C,Dtype,hCF,hC,hDtype,hcore⟩ :=
    eventually_double_difference_direct_residue_grid_moment hcsrc hUsrc hσ hεloss
  refine ⟨CF,C,Dtype,hCF,hC,hDtype,?_⟩
  filter_upwards [hcore] with T hcoreT
  intro Fsrc rshift sshift Y n N Qbase kmax Kmesh Usel R Jsep d Wmax M δ Bcut Bselect
    hK hNlink hd hw hwcap hsmallShift hT hMtwo hN hδ hR hRM hJsep hJM hNM hwJ
    hy hsepY hshifts hreg hlower hjets htests hnegative Φ hmodels
    hscale hfourBuffer hfourBudget hquadBudget hBcut hBselectSize hcutMargin hscaleTen hNsqM
    Q hQbase hQmax Cphys c J B hsmall hNR hRN hNcube hNtwo hanchorBudget
    lambda Uband hUbandCap NarrowCap Cap μ₀ U₀ C₂ C₃ Ct Cc Ccurv Kres Esize Dbase Tbase
    hsize hBsize Lunit Gamma Cthird Cpack Cfirst Cgap Cmain Ctail
    Δtype Δ D Buffer hvalid hUmax hroom f Vscale Klarge Wphys PointError FamilyBound
    CtailBand ClowBand CerrorBand Density Endpoint A Bint hA hab hB
  have hn : 0 < n := by omega
  have hM : 0 < M := by linarith only [hMtwo]
  have hRp : 0 < R := zero_lt_one.trans_le hR
  have hκ : 0 < κ := modelPhaseThirdLower_pos hσ
  have hBuffer0 : 0 ≤ Buffer 0 := by dsimp only [Buffer]; positivity
  obtain ⟨Chunks,anchor,band,za,hphase,hdeep₀,hcardChunks,hroots,hbands,hcounts,htail,
      hReduction₀⟩ :=
    double_difference_phase_subinterval_dyadic_band_reduction Y Fsrc rshift sshift
      n N Qbase kmax hNlink hcsrc hUsrc hn hd hwcap hsmallShift hshifts hy hT hM hRp
      hreg hjets hlower hnegative hscale hQbase hQmax hBuffer0
      (show (0:ℝ) ≤ 0 by rfl) (by simpa only [add_zero] using hroom)
      A Bint hA hab hB
  have hdeep p (hp : p∈Chunks) :
      (n:ℝ)*p.2∈Icc (M+Buffer 0+4*(N:ℝ)) (2*M-Buffer 0-(N:ℝ)) := by
    simpa only [add_zero,sub_zero] using hdeep₀ p hp
  let Selected := fun k => Chunks.filter (fun p => band p=some k)
  let Grid := fun (k : ℕ) (r : ℤ) =>
    ((Selected k).filter (fun p => p.2%8=r)).image (fun p => (p.1,p.2/8-2))
  let BandSum := fun k => ∑ p∈Selected k,
    ‖∑ j∈Finset.Ioc ((n:ℤ)*p.2) ((n:ℤ)*(p.2+1)),(𝐞 (f p.1 j):ℂ)‖
  have hBufferMono k (hk : k ≤ kmax) : Buffer k ≤ Buffer 0 := by
    have hu : (Usel k:ℝ) ≤ Usel 0 := by exact_mod_cast hUmax k hk
    exact add_le_add (add_le_add
      (mul_le_mul_of_nonneg_right
        (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hu (by norm_num)) hκ.le)
        (Nat.cast_nonneg _)) le_rfl) le_rfl
  have hGridCard k r : (Grid k r).card ≤ (Selected k).card :=
    Finset.card_image_le.trans (Finset.card_filter_le _ _)
  have hGridPhase k r : (Grid k r).image Prod.fst ⊆ Y := by
    intro y hyGrid
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hyGrid
    obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hp
    exact hphase q (Finset.mem_filter.mp (Finset.mem_filter.mp hq).1).1
  have hBand k (hk : k ≤ kmax) :
      (BandSum k)^12 ≤ (8:ℝ)^11*∑ r∈Finset.Ico (0:ℤ) 8,FamilyBound k (Grid k r) := by
    obtain ⟨hfullmesh,hmesh,hUref,hselectedWrap,hRQ,hselectedUpper,hQN,hUR,
      hminscale,hD,hΔ⟩ := hvalid k hk
    have hQp : 0 < Q k := by
      dsimp only [Q]
      exact Nat.mul_pos (by omega) (by positivity)
    letI : NeZero (Kmesh k) := ⟨Nat.ne_of_gt (hK k)⟩
    have hSelY p (hp : p∈Selected k) : p.1∈Y := hphase p (Finset.mem_filter.mp hp).1
    have hSelDeep p (hp : p∈Selected k) :
        (n:ℝ)*p.2∈Icc (M+Buffer k+4*(N:ℝ)) (2*M-Buffer k-(N:ℝ)) := by
      have hh := hdeep p (Finset.mem_filter.mp hp).1
      have hb := hBufferMono k hk
      constructor <;> linarith only [hh.1,hh.2,hb]
    have hSelAnchors p (hp : p∈Selected k) :
        |za p 0-((n:ℝ)*p.2-2*(N:ℝ))| ≤ (N:ℝ)/16 ∧
        iteratedDeriv 2 (f p.1) (za p 0)/2=(anchor p 0:ℝ) ∧
        768*(anchor p 0).den ≤ Q k ∧
        24576*R^2 ≤ csrc*(Q k:ℝ)*(anchor p 0).den := by
      obtain ⟨hpC,hpk⟩ := Finset.mem_filter.mp hp
      have hr := hroots p hpC 0
      have hb := hbands p hpC
      rw [hpk] at hb
      exact ⟨by simpa only [ite_true] using hr.2.1,hr.1,(hb.2 0).1,(hb.2 0).2⟩
    let Lsrc := fun (r : ℤ) (p : ℝ × ℤ) => r*(n:ℤ)+(N:ℤ)*p.2+2*(N:ℤ)
    let W := fun r : ℤ => ∑ p∈Grid k r,
      ‖∑ j∈Finset.Ioc (Lsrc r p) (Lsrc r p+n),(𝐞 (f p.1 j):ℂ)‖
    have hW r : 0 ≤ W r := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
    have hgridMoment r : (W r)^12 ≤ FamilyBound k (Grid k r) := by
      exact hcoreT (Selected k) Fsrc rshift sshift (fun p => za p 0)
        n (Q k) (Kmesh k) N R Jsep r
        (d:=d) (Wmax:=Wmax) (M:=M) (δ:=δ) (Bcut:=Bcut) (Bselect:=Bselect)
        (Usel k) (fun p => anchor p 0) hNlink
        hd hw hwcap hsmallShift hT hM hδ hQp hUbandCap
        (fun p hp => hy p.1 (hSelY p hp))
        (by simpa only [Buffer,Cphys,show σ*(σ+1)+1+2=σ*(σ+1)+3 by ring] using hSelDeep)
        hreg hlower hjets htests hnegative hMtwo hN
        hJsep hJM hNM hwJ hmesh hfourBuffer hfourBudget hquadBudget hfullmesh
        (fun p hp q hq hne => hsepY p.1 (hSelY p hp) q.1 (hSelY q hq) hne)
        (by
          intro y hySel
          obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hySel
          exact hshifts p.1 (hSelY p hp))
        (fun p hp => hmodels p.1 (hSelY p hp)) hSelAnchors
        hR hRM hscale hBcut hUref hBselectSize hcutMargin hselectedWrap hRQ
        hselectedUpper hscaleTen hQN hNsqM hUR
        hsmall hNR hRN hNcube hminscale hNtwo hanchorBudget hsize hD hΔ hBsize
    have hsum := (eight_grid_exact_selected_transport (Selected k) Y n N (Q k) hNlink hN
      (fun y w => iteratedDeriv 2 (f y) w/2) (fun y j => (𝐞 (f y j):ℂ))
      (fun p => anchor p 0) (fun p => za p 0) hSelY hSelDeep hSelAnchors).2
    have hsum' : BandSum k=∑ r∈Finset.Ico (0:ℤ) 8,W r := hsum
    have hholder := Real.rpow_sum_le_const_mul_sum_rpow_of_nonneg (Finset.Ico (0:ℤ) 8)
      (f:=W) (p:=(12:ℝ)) (by norm_num) (fun r _ => hW r)
    have hp : (BandSum k)^12 ≤ (8:ℝ)^11*∑ r∈Finset.Ico (0:ℤ) 8,(W r)^12 := by
      rw [hsum']
      norm_num only [Int.card_Ico,Int.reduceSub,Int.reduceToNat,Nat.cast_ofNat,
        show (12:ℝ)-1=11 by norm_num,Real.rpow_ofNat] at hholder
      exact hholder
    exact hp.trans (mul_le_mul_of_nonneg_left
      (Finset.sum_le_sum (fun r _ => hgridMoment r)) (by norm_num))
  refine ⟨Chunks,band,hcardChunks,hcounts,htail,?_⟩
  intro SelectedOut GridOut
  refine ⟨fun k r => ⟨hGridCard k r,hGridPhase k r⟩,?_⟩
  have hsum : (∑ k∈Finset.range (kmax+1),(BandSum k)^12) ≤
      (8:ℝ)^11*∑ k∈Finset.range (kmax+1),
        ∑ r∈Finset.Ico (0:ℤ) 8,FamilyBound k (Grid k r) := by
    calc
      _ ≤ ∑ k∈Finset.range (kmax+1),(8:ℝ)^11*
          ∑ r∈Finset.Ico (0:ℤ) 8,FamilyBound k (Grid k r) :=
        Finset.sum_le_sum (fun k hk => hBand k (by
          have hh := Finset.mem_range.mp hk
          omega))
      _ = _ := by rw [Finset.mul_sum]
  have hReduction :
      (∑ y∈Y, ‖∑ j∈Finset.Ioc (A y) (Bint y),(𝐞 (f y j):ℂ)‖)^12 ≤
        2^11*(((kmax:ℝ)+2)^11*
          (((n:ℝ)*(Y.card:ℝ)*Density kmax)^12+
            ∑ k∈Finset.range (kmax+1),(BandSum k)^12)+Endpoint^12) := by
    simpa only [mul_zero,add_zero] using hReduction₀
  exact hReduction.trans (mul_le_mul_of_nonneg_left
    (add_le_add (mul_le_mul_of_nonneg_left (add_le_add le_rfl hsum) (by positivity))
      le_rfl) (by norm_num))

example
    {csrc Usrc σ εloss : ℝ}
    (hcsrc : 0 < csrc) (hUsrc : 0 < Usrc)
    (hσ : 0 < σ) (hεloss : 0 < εloss) :
    let κ := modelPhaseThirdLower σ
    let L := max (32*Usrc^2/csrc^2)
      (64*(modelPhaseJetCoefficient σ 3+1)*Usrc/κ^2)
    let θ := 1/(8*(L+3))
    ∃ CF C Dtype : ℝ, 1 ≤ CF ∧ 0 < C ∧ 0 < Dtype ∧
    ∀ᶠ T : ℝ in Filter.atTop, ∀ (Fsrc rshift sshift : ℝ → ℝ) (Y : Finset ℝ)
    (n N Qbase kmax : ℕ) (Kmesh Usel : ℕ → ℕ) (R Jsep : ℝ)
    {d Wmax M δ Bcut Bselect : ℝ},
    (∀ k, 0 < Kmesh k) → N=8*n →
    0 < d → 0 ≤ Wmax → Wmax ≤ 1/4 → 2*Usrc*Wmax ≤ csrc/64 →
    0 < T → 2 ≤ M → 0 < N → δ ≤ min κ 1 →
    1 ≤ R → R ≤ M → 0 < Jsep → Jsep ≤ M → (N:ℝ) ≤ M → Wmax*Jsep ≤ 1 →
    (∀ y∈Y, y∈Icc (1:ℝ) 2) →
    (∀ y∈Y, ∀ z∈Y, y≠z → 1 ≤ Jsep*|y-z|) →
    (∀ y∈Y, 0 ≤ rshift y ∧ 0 ≤ sshift y ∧
      rshift y*sshift y=d*y ∧ rshift y+sshift y ≤ Wmax) →
    (∀ w, 0 < w → ContDiffAt ℝ ∞ Fsrc w) →
    (∀ w∈Icc (1/2:ℝ) 3, csrc ≤ iteratedDeriv 5 Fsrc w) →
    (∀ w∈Icc (1/2:ℝ) 3, ∀ j, 1 ≤ j → j ≤ 7 → |iteratedDeriv j Fsrc w| ≤ Usrc) →
    (∀ w∈Icc (1/2:ℝ) 3,
      csrc ≤ |(iteratedDeriv 5 Fsrc w)^2-iteratedDeriv 4 Fsrc w*iteratedDeriv 6 Fsrc w|) →
    (∀ w∈Icc (1/2:ℝ) 3, iteratedDeriv 4 Fsrc w ≤ -csrc) →
    let Φ := fun y u =>
      (Fsrc u-Fsrc (u+rshift y)-Fsrc (u+sshift y)+Fsrc (u+rshift y+sshift y))/d
    (∀ y∈Y, Expdb.IsApproximateModelPhaseFunction (Φ y) σ 4 δ) →
    T*(N:ℝ)*R^2=M^3 →
    7*(N:ℝ)+2 ≤ M/4 →
    (3*Usrc)*(6*(N:ℝ)+1)^4 ≤ M*(N:ℝ)*R^2 →
    (3*Usrc/4)*(6*(N:ℝ)+1)^2 ≤ (N:ℝ)*R^2 →
    0 < Bcut → 2+168/κ ≤ Bselect → 7*Bcut ≤ κ*Bselect →
    (N:ℝ)^10 ≤ M^3*R^7 →
    ((N:ℝ)^2 ≤ M ∨ (1 ≤ M ∧ (N:ℝ) ≤ T ∧ R^2 ≤ T)) →
    let Q := fun k : ℕ => Qbase*2^k
    768 ≤ Qbase → (N:ℝ)*(Q kmax:ℝ) ≤ M →
    let Cphys := σ*(σ+1)+1
    let c := κ/6
    let J := Cphys/6
    let B := max 1 (max (2*Real.sqrt J) (8*J*Real.sqrt J/(3*c)))
    B*R^2/(N:ℝ)^2 ≤ 1/2 →
    (N:ℝ) ≤ R^2 → R ≤ (N:ℝ) → (N:ℝ)^3 ≤ M*R^2 →
    2 ≤ (N:ℝ) → csrc ≤ 4*κ/(Cphys+2) →
    let lambda := csrc*T/(2*M^2)
    let Uband := Usrc*T/M^2
    Uband ≤ 1 →
    let NarrowCap := (4/θ+3)*(8*Usrc/(csrc*θ)+3)
    let Cap := 3*NarrowCap
    let μ₀ := csrc*T/(12*M^3)
    let U₀ := Usrc*T/(2*M^3)
    let C₂ := modelPhaseJetCoefficient σ 2+δ
    let C₃ := modelPhaseJetCoefficient σ 3+δ
    let Ct := C₂/2+5*C₃/12
    let Cc := C₂/κ+C₃/(2*κ)
    let Ccurv := (4/κ)*(B+2*quarticReciprocalConstant σ δ)
    let Kres := 4*(37*B/2+16*B*Cc+2*Ct+2*Cc+
      2*quarticNonlinearResidualConstant σ δ)/κ
    let Esize := κ/(16*(Cphys+2))
    let Dbase := 37*B/2+16*B*Cc+2*Ct+2*Cc+2*quarticNonlinearResidualConstant σ δ
    let Tbase := (2/κ)*(B+2*quarticReciprocalConstant σ δ)
    2*3840*128^2*105*(Dbase+64*Tbase*Esize^2) ≤ Bselect*Esize →
    61*Ccurv*Cphys ≤ Bcut →
    let Lunit := 2*κ/Cphys
    let Gamma := Cphys/κ
    let Cthird := Gamma*(32*Kres+9*quarticReciprocalConstant σ δ)
    let Cpack := 64*Cphys*(Gamma^2*Cthird+Gamma*(modelPhaseJetCoefficient σ 3+δ)/κ)/κ
    let Cfirst := 128*Cphys*(Gamma^2*Cthird+Gamma*(modelPhaseJetCoefficient σ 3+δ)/κ)/κ^2
    let Cgap := 64*Cphys*(Gamma^2*B+Gamma*(modelPhaseJetCoefficient σ 3+δ)/κ)/κ
    let Cmain := 4*(2*Cfirst/Lunit^3)^((3:ℝ)⁻¹)+2
    let Ctail := 4*Cpack/Lunit^2+Cgap
    let Δtype := fun k : ℕ =>
      (16*U₀/μ₀)*Real.sqrt (U₀*(Q k:ℝ)^3)*Real.sqrt (Kmesh k)/(6*(Kmesh k:ℝ)^2)
    let Δ := fun k : ℕ => (37*B/2+16*B*Cc+2*Ct+2*Cc)*(Q k:ℝ)/(N:ℝ)
    let D := fun k : ℕ => Δ k+quarticNonlinearResidualConstant σ δ*(2*(Q k:ℝ))/(N:ℝ)
    let Buffer := fun k : ℕ => (56*(Usel k:ℝ)/κ)*(N:ℝ)+(N:ℝ)/(Cphys+2)+2
    (∀ k ≤ kmax,
      63*(Usrc/(2*(N:ℝ)*R^2))*(Q k:ℝ)*(N:ℝ)^2 ≤ Kmesh k ∧
      (Q k:ℝ)*(N:ℝ) ≤ (Kmesh k:ℝ)*R^2 ∧
      1 ≤ Usel k ∧ Bselect^2*(Usel k:ℝ)^3*R^2 ≤ (N:ℝ)^2 ∧
      R ≤ (Q k:ℝ) ∧
      (Usel k:ℝ) ≤ ((N:ℝ)/(Q k:ℝ))^((2:ℝ)/3)/Bselect ∧
      (Q k:ℝ) ≤ (N:ℝ) ∧ (Usel k:ℝ) ≤ R^2 ∧
      2*R^2 ≤ (Q k:ℝ)*(N:ℝ) ∧ D k ≤ 1/2 ∧ Δ k < 1/2) →
    (∀ k ≤ kmax, Usel k ≤ Usel 0) →
    2*Buffer 0+6*(N:ℝ) ≤ M →
    let f := fun y w => T*Φ y (w/M)
    let Vscale := fun k : ℕ => max 1 (Uband*(N:ℝ)/(Q k:ℝ))
    let Klarge := fun k : ℕ => 60*588*(Uband/lambda)^2*Uband^2*(R^8/(N:ℝ)^4)*
      (Cmain*((Q k:ℝ)/(Uband*(N:ℝ)))^((2:ℝ)/3)+Ctail/(Usel k:ℝ))
    let Wphys := fun k : ℕ => (144*Usrc/(csrc*κ))*(R^2/(Q k:ℝ))
    let PointError := Real.sqrt (3*(N:ℝ))*Real.log (6*(N:ℝ))+
      36*Usrc*R^2/(csrc*κ*(N:ℝ))
    let FamilyBound := fun (k : ℕ) (P : Finset (ℝ × ℤ)) =>
      let YP := P.image Prod.fst
      let Mass := Vscale k*Dtype*(2+θ*(Uband+1/lambda))*(YP.card:ℝ)*(M/(N:ℝ))*
        (1+Δtype k*Jsep)+(YP.card:ℝ)^2*Klarge k*T^εloss
      CF^12*2^11*((1+Real.log (Kmesh k))^12*Wphys k^6*
        (C*(Kmesh k:ℝ)^((12:ℝ)+εloss)*Cap^11*(2*(P.card:ℝ))^10*Mass)+
        ((P.card:ℝ)*PointError)^12)
    let CtailBand := 4*Usrc*(64/csrc)^2+192/csrc
    let ClowBand := (2*Usrc+csrc/32)*(3072/csrc)^2+3072/csrc
    let CerrorBand := (768:ℝ)^2*CtailBand+ClowBand
    let Density := fun k => 128*CerrorBand*(M*R^2/((N:ℝ)*(Q k:ℝ)^2))*
      (2+Real.log (512*R^2/(csrc*((Q k:ℝ)/768))+1))
    let Endpoint := (Y.card:ℝ)*(2*Buffer 0+6*(N:ℝ)+2*(n:ℝ))
    ∀ A Bint : ℝ → ℤ, (∀ y∈Y, ⌈M⌉ ≤ A y) →
    (∀ y∈Y, A y ≤ Bint y) → (∀ y∈Y, Bint y ≤ ⌊2*M⌋) →
    ∃ (Chunks : Finset (ℝ × ℤ)) (band : (ℝ × ℤ) → Option ℕ),
      (Chunks.card:ℝ) ≤ (Y.card:ℝ)*(8*M/(N:ℝ)) ∧
      (∀ k ≤ kmax, ((Chunks.filter (fun p => band p=some (k+1))).card:ℝ) ≤
        (Y.card:ℝ)*Density k) ∧
      ((Chunks.filter (fun p => band p=none)).card:ℝ) ≤ (Y.card:ℝ)*Density kmax ∧
      let Selected := fun k => Chunks.filter (fun p => band p=some k)
      let Grid := fun (k : ℕ) (r : ℤ) =>
        ((Selected k).filter (fun p => p.2%8=r)).image (fun p => (p.1,p.2/8-2))
      (∀ k r, (Grid k r).card ≤ (Selected k).card ∧ (Grid k r).image Prod.fst ⊆ Y) ∧
      (∑ y∈Y, ‖∑ j∈Finset.Ioc (A y) (Bint y),(𝐞 (f y j):ℂ)‖)^12 ≤
        2^11*(((kmax:ℝ)+2)^11*
          (((n:ℝ)*(Y.card:ℝ)*Density kmax)^12+
            (8:ℝ)^11*∑ k∈Finset.range (kmax+1),
              ∑ r∈Finset.Ico (0:ℤ) 8, FamilyBound k (Grid k r))+
            Endpoint^12)
 := by
  exact eventually_double_difference_all_band_subinterval_moment hcsrc hUsrc hσ hεloss

#print axioms eventually_double_difference_all_band_subinterval_moment

/-- Unchanged existing private physical decay proof, copied only for scratch access;
promotion reuses its original declaration. -/
private theorem physical_denominator_rpow_decay
    {R Q N s : ℝ} (p : ℕ)
    (hR : 0 < R) (hRQ : R ≤ Q) (hN : 0 < N) (hs : s ≤ p) :
    (Q/N)^s/Q^p ≤ (R/N)^s/R^p := by
  have hQ : 0 < Q := hR.trans_le hRQ
  have hh := Real.rpow_le_rpow_of_nonpos hR hRQ (sub_nonpos.mpr hs)
  rw [Real.rpow_sub_natCast hQ.ne',Real.rpow_sub_natCast hR.ne'] at hh
  calc
    _ = (Q^s/Q^p)/N^s := by
      rw [Real.div_rpow hQ.le hN.le]
      ring
    _ ≤ (R^s/R^p)/N^s :=
      div_le_div_of_nonneg_right hh (Real.rpow_nonneg hN.le _)
    _ = _ := by
      rw [Real.div_rpow hR.le hN.le]
      ring

example
    {R Q N s : ℝ} (p : ℕ)
    (hR : 0 < R) (hRQ : R ≤ Q) (hN : 0 < N) (hs : s ≤ p) :
    (Q/N)^s/Q^p ≤ (R/N)^s/R^p := by
  exact physical_denominator_rpow_decay p hR hRQ hN hs

#print axioms physical_denominator_rpow_decay

/-- Unchanged existing private physical decay proof, copied only for scratch access;
promotion reuses its original declaration. -/
private theorem physical_reference_reciprocal_bound
    {N Q B U : ℝ} (hN : 0 < N) (hQ : 0 < Q) (hB : 0 < B)
    (hU : (N/Q)^((2:ℝ)/3)/(2*B) ≤ U) :
    0 < U ∧ 1/U ≤ 2*B*(Q/N)^((2:ℝ)/3) := by
  have hlow : 0 < (N/Q)^((2:ℝ)/3)/(2*B) := by positivity
  refine ⟨hlow.trans_le hU,?_⟩
  calc
    _ ≤ 1/((N/Q)^((2:ℝ)/3)/(2*B)) :=
      one_div_le_one_div_of_le hlow hU
    _ = _ := by
      rw [Real.div_rpow hN.le hQ.le,Real.div_rpow hQ.le hN.le]
      field_simp

example
    {N Q B U : ℝ} (hN : 0 < N) (hQ : 0 < Q) (hB : 0 < B)
    (hU : (N/Q)^((2:ℝ)/3)/(2*B) ≤ U) :
    0 < U ∧ 1/U ≤ 2*B*(Q/N)^((2:ℝ)/3) := by
  exact physical_reference_reciprocal_bound hN hQ hB hU

#print axioms physical_reference_reciprocal_bound

/-- The actual clamped triangular factor gives four physical monomials after
the selected-cardinality/mesh prefactor; the curvature scales remain linked. -/
private theorem double_difference_clamped_triangular_monomials
    {Y M N R Q Jsep c U θ D Cdelta delta : ℝ}
    (hY : 0 ≤ Y) (hM : 0 < M) (hN : 0 < N) (hR : 0 < R) (hRQ : R ≤ Q)
    (hJ : 0 ≤ Jsep) (hc : 0 < c) (hU : 0 < U) (hθ : 0 ≤ θ)
    (hD : 0 ≤ D) (hCd : 0 ≤ Cdelta) (hd : 0 ≤ delta)
    (hdelta : delta ≤ Cdelta*R^2/N^2)
    (hband : U*M/(N*R^2) ≤ 1) :
    let H := U*M/(N*R^2)
    let lambda := c*M/(2*N*R^2)
    let V := max 1 (H*N/Q)
    let Ctri := 2+θ*(1+2*U/c)
    (Y^10*M^10*N^2*R^8/Q^14)*
      (V*D*(2+θ*(H+1/lambda))*Y*(M/N)*(1+delta*Jsep)) ≤
      Ctri*D*(Y^11*M^10*N^2/(U*R^4)+Y^11*M^11*N^2/R^7+
        Cdelta*Y^11*Jsep*M^10/(U*R^2)+Cdelta*Y^11*Jsep*M^11/R^5) := by
  intro H lambda V Ctri
  have hQ : 0 < Q := hR.trans_le hRQ
  have hH : 0 < H := by dsimp only [H]; positivity
  have hLam : 0 < lambda := by dsimp only [lambda]; positivity
  have hCtri : 0 ≤ Ctri := by dsimp only [Ctri]; positivity
  have hV : 0 ≤ V := zero_le_one.trans (le_max_left _ _)
  have hprod : 0 ≤ H*N/Q := by positivity
  have hVupper : V ≤ 1+H*N/Q := max_le (by linarith only [hprod]) (by linarith)
  have hrecip : 1/lambda=(2*U/c)/H := by dsimp only [lambda,H]; field_simp
  have hInv : 1 ≤ 1/H := (le_div_iff₀ hH).mpr (by simpa only [one_mul] using hband)
  have hFactor : 2+θ*(H+1/lambda) ≤ Ctri/H := by
    rw [hrecip]
    calc
      _ ≤ 2/H+θ*(1/H+(2*U/c)/H) :=
        add_le_add ((le_div_iff₀ hH).mpr (by nlinarith only [show H ≤ 1 from hband]))
          (mul_le_mul_of_nonneg_left (add_le_add (hband.trans hInv) le_rfl) hθ)
      _ = _ := by dsimp only [Ctri]; ring
  have hCost : V*(2+θ*(H+1/lambda)) ≤ Ctri*(1/H+N/Q) := by
    calc
      _ ≤ (1+H*N/Q)*(Ctri/H) :=
        mul_le_mul hVupper hFactor (by positivity) (by positivity)
      _ = _ := by field_simp
  let Coeff := Ctri*D
  have hCoeff : 0 ≤ Coeff := mul_nonneg hCtri hD
  have hdecay (p : ℕ) : 1/Q^p ≤ 1/R^p :=
    one_div_le_one_div_of_le (pow_pos hR p) (pow_le_pow_left₀ hR.le hRQ p)
  have h0 : R^10/Q^14 ≤ 1/R^4 := by
    calc
      _ = R^10*(1/Q^14) := by ring
      _ ≤ R^10*(1/R^14) := mul_le_mul_of_nonneg_left (hdecay 14) (by positivity)
      _ = _ := by field_simp
  have h1 : R^8/Q^15 ≤ 1/R^7 := by
    calc
      _ = R^8*(1/Q^15) := by ring
      _ ≤ R^8*(1/R^15) := mul_le_mul_of_nonneg_left (hdecay 15) (by positivity)
      _ = _ := by field_simp
  have h2 : R^12/Q^14 ≤ 1/R^2 := by
    calc
      _ = R^12*(1/Q^14) := by ring
      _ ≤ R^12*(1/R^14) := mul_le_mul_of_nonneg_left (hdecay 14) (by positivity)
      _ = _ := by field_simp
  have h3 : R^10/Q^15 ≤ 1/R^5 := by
    calc
      _ = R^10*(1/Q^15) := by ring
      _ ≤ R^10*(1/R^15) := mul_le_mul_of_nonneg_left (hdecay 15) (by positivity)
      _ = _ := by field_simp

  let A₀ := Coeff*Y^11*M^10*N^2/U
  let A₁ := Coeff*Y^11*M^11*N^2
  let A₂ := Coeff*Cdelta*Y^11*Jsep*M^10/U
  let A₃ := Coeff*Cdelta*Y^11*Jsep*M^11
  have hA₀ : 0 ≤ A₀ := by dsimp only [A₀]; positivity
  have hA₁ : 0 ≤ A₁ := by dsimp only [A₁]; positivity
  have hA₂ : 0 ≤ A₂ := by dsimp only [A₂]; positivity
  have hA₃ : 0 ≤ A₃ := by dsimp only [A₃]; positivity
  calc
    _ = (Y^10*M^10*N^2*R^8/Q^14)*
        ((V*(2+θ*(H+1/lambda)))*D*Y*(M/N)*(1+delta*Jsep)) := by ring
    _ ≤ (Y^10*M^10*N^2*R^8/Q^14)*
        ((Ctri*(1/H+N/Q))*D*Y*(M/N)*(1+(Cdelta*R^2/N^2)*Jsep)) := by
      gcongr
    _ = A₀*(R^10/Q^14)+A₁*(R^8/Q^15)+A₂*(R^12/Q^14)+A₃*(R^10/Q^15) := by
      dsimp only [A₀,A₁,A₂,A₃,Coeff,H]
      field_simp
      ring
    _ ≤ A₀*(1/R^4)+A₁*(1/R^7)+A₂*(1/R^2)+A₃*(1/R^5) :=
      add_le_add (add_le_add (add_le_add
        (mul_le_mul_of_nonneg_left h0 hA₀)
        (mul_le_mul_of_nonneg_left h1 hA₁))
        (mul_le_mul_of_nonneg_left h2 hA₂))
        (mul_le_mul_of_nonneg_left h3 hA₃)
    _ = _ := by dsimp only [A₀,A₁,A₂,A₃,Coeff]; ring

example
    {Y M N R Q Jsep c U θ D Cdelta delta : ℝ}
    (hY : 0 ≤ Y) (hM : 0 < M) (hN : 0 < N) (hR : 0 < R) (hRQ : R ≤ Q)
    (hJ : 0 ≤ Jsep) (hc : 0 < c) (hU : 0 < U) (hθ : 0 ≤ θ)
    (hD : 0 ≤ D) (hCd : 0 ≤ Cdelta) (hd : 0 ≤ delta)
    (hdelta : delta ≤ Cdelta*R^2/N^2)
    (hband : U*M/(N*R^2) ≤ 1) :
    let H := U*M/(N*R^2)
    let lambda := c*M/(2*N*R^2)
    let V := max 1 (H*N/Q)
    let Ctri := 2+θ*(1+2*U/c)
    (Y^10*M^10*N^2*R^8/Q^14)*
      (V*D*(2+θ*(H+1/lambda))*Y*(M/N)*(1+delta*Jsep)) ≤
      Ctri*D*(Y^11*M^10*N^2/(U*R^4)+Y^11*M^11*N^2/R^7+
        Cdelta*Y^11*Jsep*M^10/(U*R^2)+Cdelta*Y^11*Jsep*M^11/R^5) := by
  exact double_difference_clamped_triangular_monomials hY hM hN hR hRQ hJ hc hU hθ hD hCd hd hdelta hband

#print axioms double_difference_clamped_triangular_monomials

/-- The already-clamped actual large-entry mass has one dominant physical
monomial. The smaller curvature-power term is absorbed using H <= 1. -/
private theorem double_difference_clamped_large_monomial
    {Y M N R Q H Uref C₀ Cmain Ctail B : ℝ}
    (hN : 0 < N) (hR : 0 < R) (hRQ : R ≤ Q)
    (hH : 0 < H) (hHcap : H ≤ 1) (hC : 0 ≤ C₀)
    (hmain : 0 ≤ Cmain) (htail : 0 ≤ Ctail) (hB : 0 < B)
    (hUlower : (N/Q)^((2:ℝ)/3)/(2*B) ≤ Uref) :
    (Y^10*M^10*N^2*R^8/Q^14)*
      (Y^2*(C₀*H^2*(R^8/N^4)*
        (Cmain*(Q/(H*N))^((2:ℝ)/3)+Ctail/Uref))) ≤
      C₀*(Cmain+2*B*Ctail)*(Y^12*M^10*R^2/N^2)*
        (R/N)^((2:ℝ)/3)*H^((4:ℝ)/3) := by
  have hQ : 0 < Q := hR.trans_le hRQ
  obtain ⟨hU,hUinv⟩ := physical_reference_reciprocal_bound hN hQ hB hUlower
  have hHpow : H^2 ≤ H^((4:ℝ)/3) := by
    simpa only [Real.rpow_ofNat] using
      Real.rpow_le_rpow_of_exponent_ge hH hHcap (by norm_num : (4:ℝ)/3 ≤ 2)
  have hcancel : H^2*(Q/(H*N))^((2:ℝ)/3)=
      H^((4:ℝ)/3)*(Q/N)^((2:ℝ)/3) := by
    have hsum : H^2=H^((4:ℝ)/3)*H^((2:ℝ)/3) := by
      rw [←Real.rpow_add hH]
      norm_num
    rw [show Q/(H*N)=(Q/N)/H by ring,Real.div_rpow (by positivity) hH.le,hsum]
    field_simp
  have hCost : H^2*(Cmain*(Q/(H*N))^((2:ℝ)/3)+Ctail/Uref) ≤
      (Cmain+2*B*Ctail)*H^((4:ℝ)/3)*(Q/N)^((2:ℝ)/3) := by
    have htailInv : Ctail/Uref ≤ Ctail*(2*B*(Q/N)^((2:ℝ)/3)) := by
      simpa only [div_eq_mul_inv,one_div,one_mul] using mul_le_mul_of_nonneg_left hUinv htail
    calc
      _ = Cmain*(H^2*(Q/(H*N))^((2:ℝ)/3))+H^2*(Ctail/Uref) := by ring
      _ ≤ Cmain*(H^((4:ℝ)/3)*(Q/N)^((2:ℝ)/3))+
          H^((4:ℝ)/3)*(Ctail*(2*B*(Q/N)^((2:ℝ)/3))) := by
        rw [hcancel]
        exact add_le_add le_rfl (mul_le_mul hHpow htailInv (by positivity) (by positivity))
      _ = _ := by ring
  have hdecay : R^16*(Q/N)^((2:ℝ)/3)/Q^14 ≤ R^2*(R/N)^((2:ℝ)/3) := by
    calc
      _ = R^16*((Q/N)^((2:ℝ)/3)/Q^14) := by ring
      _ ≤ R^16*((R/N)^((2:ℝ)/3)/R^14) :=
        mul_le_mul_of_nonneg_left
          (physical_denominator_rpow_decay 14 hR hRQ hN (by norm_num)) (by positivity)
      _ = _ := by field_simp

  let A := C₀*(Cmain+2*B*Ctail)*(Y^12*M^10/N^2)*H^((4:ℝ)/3)
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  calc
    _ = (C₀*Y^12*M^10*R^16/(N^2*Q^14))*
        (H^2*(Cmain*(Q/(H*N))^((2:ℝ)/3)+Ctail/Uref)) := by
      field_simp
    _ ≤ (C₀*Y^12*M^10*R^16/(N^2*Q^14))*
        ((Cmain+2*B*Ctail)*H^((4:ℝ)/3)*(Q/N)^((2:ℝ)/3)) :=
      mul_le_mul_of_nonneg_left hCost (by positivity)
    _ = A*(R^16*(Q/N)^((2:ℝ)/3)/Q^14) := by dsimp only [A]; ring
    _ ≤ A*(R^2*(R/N)^((2:ℝ)/3)) := mul_le_mul_of_nonneg_left hdecay hA
    _ = _ := by dsimp only [A]; ring

example
    {Y M N R Q H Uref C₀ Cmain Ctail B : ℝ}
    (hN : 0 < N) (hR : 0 < R) (hRQ : R ≤ Q)
    (hH : 0 < H) (hHcap : H ≤ 1) (hC : 0 ≤ C₀)
    (hmain : 0 ≤ Cmain) (htail : 0 ≤ Ctail) (hB : 0 < B)
    (hUlower : (N/Q)^((2:ℝ)/3)/(2*B) ≤ Uref) :
    (Y^10*M^10*N^2*R^8/Q^14)*
      (Y^2*(C₀*H^2*(R^8/N^4)*
        (Cmain*(Q/(H*N))^((2:ℝ)/3)+Ctail/Uref))) ≤
      C₀*(Cmain+2*B*Ctail)*(Y^12*M^10*R^2/N^2)*
        (R/N)^((2:ℝ)/3)*H^((4:ℝ)/3) := by
  exact double_difference_clamped_large_monomial (Y:=Y) (M:=M) hN hR hRQ hH hHcap hC hmain htail hB hUlower

#print axioms double_difference_clamped_large_monomial

/-- Unchanged existing private selected-mesh proof, copied only for scratch access;
promotion reuses its original declaration. -/
private theorem selected_band_prefactor_identity
    {R Q N M Cmesh Ccard Y : ℝ}
    (hR : R ≠ 0) (hQ : Q ≠ 0) (hN : N ≠ 0) :
    (R^2/Q)^6*(Cmesh*Q*N/R^2)^12*(Ccard*Y*M*R^2/(N*Q^2))^10 =
      Cmesh^12*Ccard^10*Y^10*M^10*N^2*R^8/Q^14 := by
  field_simp

example
    {R Q N M Cmesh Ccard Y : ℝ}
    (hR : R ≠ 0) (hQ : Q ≠ 0) (hN : N ≠ 0) :
    (R^2/Q)^6*(Cmesh*Q*N/R^2)^12*(Ccard*Y*M*R^2/(N*Q^2))^10 =
      Cmesh^12*Ccard^10*Y^10*M^10*N^2*R^8/Q^14 := by
  exact selected_band_prefactor_identity hR hQ hN

#print axioms selected_band_prefactor_identity

/-- Unchanged existing private selected-mesh proof, copied only for scratch access;
promotion reuses its original declaration. -/
private theorem selected_band_mesh_cardinality_prefactor_bound
    {Y M N R Q K P Cmesh Ccard L T ε : ℝ}
    (hN : 0 < N) (hR : 0 < R)
    (hQ : 0 < Q) (hK : 0 < K) (hP : 0 ≤ P)
    (hCm : 0 < Cmesh) (hε : 0 ≤ ε)
    (hQN : Q ≤ N) (hNR : N ≤ R^2) (hNT : N ≤ T)
    (hmesh : K ≤ Cmesh*Q*N/R^2)
    (hcard : P ≤ Ccard*Y*M*R^2/(N*Q^2)*L) :
    (R^2/Q)^6*K^((12:ℝ)+ε)*(2*P)^10 ≤
      (Cmesh^12*Cmesh^ε*(2*Ccard)^10)*T^ε*L^10*
        (Y^10*M^10*N^2*R^8/Q^14) := by
  have hT : 0 < T := hN.trans_le hNT
  have hKT : K ≤ Cmesh*T := by
    calc
      _ ≤ Cmesh*Q*N/R^2 := hmesh
      _ ≤ Cmesh*Q := (div_le_iff₀ (sq_pos_of_pos hR)).mpr
        (mul_le_mul_of_nonneg_left hNR (by positivity))
      _ ≤ Cmesh*T := mul_le_mul_of_nonneg_left (hQN.trans hNT) hCm.le
  have hKpow : K^((12:ℝ)+ε) ≤
      (Cmesh*Q*N/R^2)^12*Cmesh^ε*T^ε := by
    calc
      _ = K^12*K^ε := by norm_num [Real.rpow_add hK]
      _ ≤ (Cmesh*Q*N/R^2)^12*(Cmesh*T)^ε := by gcongr
      _ = _ := by rw [Real.mul_rpow hCm.le hT.le]; ring
  have hPbound : 2*P ≤ (2*Ccard)*Y*M*R^2/(N*Q^2)*L := by
    calc
      _ ≤ 2*(Ccard*Y*M*R^2/(N*Q^2)*L) :=
        mul_le_mul_of_nonneg_left hcard (by norm_num)
      _ = _ := by ring
  calc
    _ ≤ (R^2/Q)^6*((Cmesh*Q*N/R^2)^12*Cmesh^ε*T^ε)*
        ((2*Ccard)*Y*M*R^2/(N*Q^2)*L)^10 := by gcongr
    _ = (Cmesh^ε*T^ε*L^10)*
        ((R^2/Q)^6*(Cmesh*Q*N/R^2)^12*((2*Ccard)*Y*M*R^2/(N*Q^2))^10) := by
      rw [mul_pow]
      ring
    _ = _ := by
      rw [selected_band_prefactor_identity hR.ne' hQ.ne' hN.ne']
      ring

example
    {Y M N R Q K P Cmesh Ccard L T ε : ℝ}
    (hN : 0 < N) (hR : 0 < R)
    (hQ : 0 < Q) (hK : 0 < K) (hP : 0 ≤ P)
    (hCm : 0 < Cmesh) (hε : 0 ≤ ε)
    (hQN : Q ≤ N) (hNR : N ≤ R^2) (hNT : N ≤ T)
    (hmesh : K ≤ Cmesh*Q*N/R^2)
    (hcard : P ≤ Ccard*Y*M*R^2/(N*Q^2)*L) :
    (R^2/Q)^6*K^((12:ℝ)+ε)*(2*P)^10 ≤
      (Cmesh^12*Cmesh^ε*(2*Ccard)^10)*T^ε*L^10*
        (Y^10*M^10*N^2*R^8/Q^14) := by
  exact selected_band_mesh_cardinality_prefactor_bound hN hR hQ hK hP hCm hε hQN hNR hNT hmesh hcard

#print axioms selected_band_mesh_cardinality_prefactor_bound

/-- The selected-grid prefactor consumes the linked clamped triangular and
large-entry masses, retaining the actual card/mesh bounds and all scale factors. -/
private theorem double_difference_selected_grid_family_monomials
    {Y Z P M N R Q K Uref Jsep c U θ D Cdelta delta C₀ Cmain Ctail B Cmesh Ccard L T ε : ℝ}
    (hY : 0 ≤ Y) (hZ : 0 ≤ Z) (hZY : Z ≤ Y) (hP : 0 ≤ P)
    (hM : 0 < M) (hN : 0 < N) (hR : 0 < R) (hRQ : R ≤ Q) (hK : 0 < K)
    (hJ : 0 ≤ Jsep) (hc : 0 < c) (hU : 0 < U) (hθ : 0 ≤ θ)
    (hD : 0 ≤ D) (hCd : 0 ≤ Cdelta) (hd : 0 ≤ delta)
    (hC : 0 ≤ C₀) (hmain : 0 ≤ Cmain) (htail : 0 ≤ Ctail) (hB : 0 < B)
    (hCm : 0 < Cmesh) (hT : 1 ≤ T) (hε : 0 ≤ ε)
    (hQN : Q ≤ N) (hNR : N ≤ R^2) (hNT : N ≤ T)
    (hmesh : K ≤ Cmesh*Q*N/R^2)
    (hcard : P ≤ Ccard*Y*M*R^2/(N*Q^2)*L)
    (hdelta : delta ≤ Cdelta*R^2/N^2)
    (hband : U*M/(N*R^2) ≤ 1)
    (hUlower : (N/Q)^((2:ℝ)/3)/(2*B) ≤ Uref) :
    let H := U*M/(N*R^2)
    let lambda := c*M/(2*N*R^2)
    let V := max 1 (H*N/Q)
    let Ctri := 2+θ*(1+2*U/c)
    (R^2/Q)^6*K^((12:ℝ)+ε)*(2*P)^10*
      (V*D*(2+θ*(H+1/lambda))*Z*(M/N)*(1+delta*Jsep)+
        Z^2*(C₀*H^2*(R^8/N^4)*
          (Cmain*(Q/(H*N))^((2:ℝ)/3)+Ctail/Uref))*T^ε) ≤
      (Cmesh^12*Cmesh^ε*(2*Ccard)^10)*T^(2*ε)*L^10*
        (Ctri*D*(Y^11*M^10*N^2/(U*R^4)+Y^11*M^11*N^2/R^7+
          Cdelta*Y^11*Jsep*M^10/(U*R^2)+Cdelta*Y^11*Jsep*M^11/R^5)+
          C₀*(Cmain+2*B*Ctail)*(Y^12*M^10*R^2/N^2)*
            (R/N)^((2:ℝ)/3)*H^((4:ℝ)/3)) := by
  intro H lambda V Ctri
  have hQ := hR.trans_le hRQ
  have hH : 0 < H := by dsimp only [H]; positivity
  have hLam : 0 < lambda := by dsimp only [lambda]; positivity
  have hV : 0 ≤ V := zero_le_one.trans (le_max_left _ _)
  have hUref := (physical_reference_reciprocal_bound hN hQ hB hUlower).1
  have hTp := zero_lt_one.trans_le hT
  have hTpow : 1 ≤ T^ε := Real.one_le_rpow hT hε
  let Tri := V*D*(2+θ*(H+1/lambda))*Y*(M/N)*(1+delta*Jsep)
  let Pair := Y^2*(C₀*H^2*(R^8/N^4)*
    (Cmain*(Q/(H*N))^((2:ℝ)/3)+Ctail/Uref))
  let Cpref := Cmesh^12*Cmesh^ε*(2*Ccard)^10
  let Physical := Y^10*M^10*N^2*R^8/Q^14
  have hTri : 0 ≤ Tri := by dsimp only [Tri]; positivity
  have hPair : 0 ≤ Pair := by dsimp only [Pair]; positivity
  have hCpref : 0 ≤ Cpref := by dsimp only [Cpref]; positivity
  have hPhysical : 0 ≤ Physical := by dsimp only [Physical]; positivity
  have hmass :
      V*D*(2+θ*(H+1/lambda))*Z*(M/N)*(1+delta*Jsep)+
        Z^2*(C₀*H^2*(R^8/N^4)*
          (Cmain*(Q/(H*N))^((2:ℝ)/3)+Ctail/Uref))*T^ε ≤ (Tri+Pair)*T^ε := by
    calc
      _ ≤ Tri+Pair*T^ε := by dsimp only [Tri,Pair]; gcongr
      _ ≤ Tri*T^ε+Pair*T^ε :=
        add_le_add (le_mul_of_one_le_right hTri hTpow) le_rfl
      _ = _ := (add_mul _ _ _).symm
  have hpref := selected_band_mesh_cardinality_prefactor_bound
    hN hR hQ hK hP hCm hε hQN hNR hNT hmesh hcard
  have htri := double_difference_clamped_triangular_monomials
    hY hM hN hR hRQ hJ hc hU hθ hD hCd hd hdelta hband
  have hlarge := double_difference_clamped_large_monomial
    (Y:=Y) (M:=M) hN hR hRQ hH hband hC hmain htail hB hUlower
  have hmonomial :
      Physical*(Tri+Pair) ≤
        Ctri*D*(Y^11*M^10*N^2/(U*R^4)+Y^11*M^11*N^2/R^7+
          Cdelta*Y^11*Jsep*M^10/(U*R^2)+Cdelta*Y^11*Jsep*M^11/R^5)+
          C₀*(Cmain+2*B*Ctail)*(Y^12*M^10*R^2/N^2)*
            (R/N)^((2:ℝ)/3)*H^((4:ℝ)/3) := by
    rw [mul_add]
    exact add_le_add htri hlarge
  have hTproduct : T^ε*T^ε=T^(2*ε) := by
    rw [←Real.rpow_add hTp]
    apply congrArg (fun x : ℝ => T^x)
    ring
  calc
    _ ≤ (Cpref*T^ε*L^10*Physical)*((Tri+Pair)*T^ε) :=
      mul_le_mul hpref hmass (by positivity) (by positivity)
    _ = Cpref*T^(2*ε)*L^10*(Physical*(Tri+Pair)) := by
      calc
        _ = Cpref*(T^ε*T^ε)*L^10*(Physical*(Tri+Pair)) := by ring
        _ = _ := by rw [hTproduct]
    _ ≤ _ := mul_le_mul_of_nonneg_left hmonomial (by positivity)

example
    {Y Z P M N R Q K Uref Jsep c U θ D Cdelta delta C₀ Cmain Ctail B Cmesh Ccard L T ε : ℝ}
    (hY : 0 ≤ Y) (hZ : 0 ≤ Z) (hZY : Z ≤ Y) (hP : 0 ≤ P)
    (hM : 0 < M) (hN : 0 < N) (hR : 0 < R) (hRQ : R ≤ Q) (hK : 0 < K)
    (hJ : 0 ≤ Jsep) (hc : 0 < c) (hU : 0 < U) (hθ : 0 ≤ θ)
    (hD : 0 ≤ D) (hCd : 0 ≤ Cdelta) (hd : 0 ≤ delta)
    (hC : 0 ≤ C₀) (hmain : 0 ≤ Cmain) (htail : 0 ≤ Ctail) (hB : 0 < B)
    (hCm : 0 < Cmesh) (hT : 1 ≤ T) (hε : 0 ≤ ε)
    (hQN : Q ≤ N) (hNR : N ≤ R^2) (hNT : N ≤ T)
    (hmesh : K ≤ Cmesh*Q*N/R^2)
    (hcard : P ≤ Ccard*Y*M*R^2/(N*Q^2)*L)
    (hdelta : delta ≤ Cdelta*R^2/N^2)
    (hband : U*M/(N*R^2) ≤ 1)
    (hUlower : (N/Q)^((2:ℝ)/3)/(2*B) ≤ Uref) :
    let H := U*M/(N*R^2)
    let lambda := c*M/(2*N*R^2)
    let V := max 1 (H*N/Q)
    let Ctri := 2+θ*(1+2*U/c)
    (R^2/Q)^6*K^((12:ℝ)+ε)*(2*P)^10*
      (V*D*(2+θ*(H+1/lambda))*Z*(M/N)*(1+delta*Jsep)+
        Z^2*(C₀*H^2*(R^8/N^4)*
          (Cmain*(Q/(H*N))^((2:ℝ)/3)+Ctail/Uref))*T^ε) ≤
      (Cmesh^12*Cmesh^ε*(2*Ccard)^10)*T^(2*ε)*L^10*
        (Ctri*D*(Y^11*M^10*N^2/(U*R^4)+Y^11*M^11*N^2/R^7+
          Cdelta*Y^11*Jsep*M^10/(U*R^2)+Cdelta*Y^11*Jsep*M^11/R^5)+
          C₀*(Cmain+2*B*Ctail)*(Y^12*M^10*R^2/N^2)*
            (R/N)^((2:ℝ)/3)*H^((4:ℝ)/3)) := by
  exact double_difference_selected_grid_family_monomials hY hZ hZY hP hM hN hR hRQ hK hJ hc hU hθ hD hCd hd
    hC hmain htail hB hCm hT hε hQN hNR hNT hmesh hcard hdelta hband hUlower

#print axioms double_difference_selected_grid_family_monomials

/-- Unchanged existing private occupied-band count proof, copied only for scratch access;
promotion reuses its original declaration. -/
private theorem selected_band_grid_cardinality_bound
    (Chunks : Finset (ℝ × ℤ)) (band : (ℝ × ℤ) → Option ℕ)
    (Grid : ℕ → ℤ → Finset (ℝ × ℤ)) (Qbase kmax : ℕ)
    {Y M N R Cbase Cdensity L : ℝ}
    (hQbase : 0 < Qbase) (hY : 0 ≤ Y) (hM : 0 ≤ M) (hN : 0 < N)
    (hCd : 0 ≤ Cdensity) (hL : 1 ≤ L)
    (hbase : (Qbase:ℝ) ≤ Cbase*R)
    (hchunks : (Chunks.card:ℝ) ≤ Y*(8*M/N)) :
    let Q := fun k : ℕ => Qbase*2^k
    (∀ j ≤ kmax, ((Chunks.filter (fun p => band p=some (j+1))).card:ℝ) ≤
      Y*(Cdensity*M*R^2/(N*(Q j:ℝ)^2)*L)) →
    (∀ k ≤ kmax, ∀ r : ℤ,
      (Grid k r).card ≤ 2*(Chunks.filter (fun p => band p=some k)).card) →
    ∀ k ≤ kmax, ∀ r : ℤ,
      ((Grid k r).card:ℝ) ≤
        (16*Cbase^2+8*Cdensity)*Y*M*R^2/(N*(Q k:ℝ)^2)*L := by
  classical
  intro Q hbands hgrids k hk r
  have hQpos (j : ℕ) : (0:ℝ) < Q j := by
    exact_mod_cast Nat.mul_pos hQbase (by positivity : 0 < 2^j)
  have hLp : 0 ≤ L := zero_le_one.trans hL
  have hgrid : ((Grid k r).card:ℝ) ≤
      2*((Chunks.filter (fun p => band p=some k)).card:ℝ) := by
    exact_mod_cast hgrids k hk r
  cases k with
  | zero =>
    have hsub : ((Chunks.filter (fun p => band p=some 0)).card:ℝ) ≤ Chunks.card := by
      exact_mod_cast Finset.card_filter_le (s:=Chunks) (p:=fun p => band p=some 0)
    have hQsq : (Q 0:ℝ)^2 ≤ Cbase^2*R^2 := by
      simpa only [Q,pow_zero,Nat.mul_one,mul_pow] using
        pow_le_pow_left₀ (Nat.cast_nonneg Qbase) hbase 2
    have hcoef : 16*Cbase^2 ≤ (16*Cbase^2+8*Cdensity)*L := by
      calc
        _ ≤ 16*Cbase^2+8*Cdensity := by linarith only [hCd]
        _ ≤ _ := le_mul_of_one_le_right (by positivity) hL
    calc
      _ ≤ 2*((Chunks.filter (fun p => band p=some 0)).card:ℝ) := hgrid
      _ ≤ 2*(Y*(8*M/N)) :=
        mul_le_mul_of_nonneg_left (hsub.trans hchunks) (by norm_num)
      _ = (16*Y*M/(N*(Q 0:ℝ)^2))*(Q 0:ℝ)^2 := by
        field_simp [(hQpos 0).ne']
        ring
      _ ≤ (16*Y*M/(N*(Q 0:ℝ)^2))*(Cbase^2*R^2) :=
        mul_le_mul_of_nonneg_left hQsq (by positivity)
      _ = (16*Cbase^2)*(Y*M*R^2/(N*(Q 0:ℝ)^2)) := by ring
      _ ≤ ((16*Cbase^2+8*Cdensity)*L)*(Y*M*R^2/(N*(Q 0:ℝ)^2)) :=
        mul_le_mul_of_nonneg_right hcoef (by positivity)
      _ = _ := by ring
  | succ j =>
    have hj : j ≤ kmax := (Nat.le_succ j).trans hk
    have hstep : (Q (j+1):ℝ)=2*(Q j:ℝ) := by
      simp only [Q,pow_succ,Nat.cast_mul,Nat.cast_ofNat]
      ring
    have hcoef : 8*Cdensity ≤ 16*Cbase^2+8*Cdensity := by
      nlinarith only [sq_nonneg Cbase]
    calc
      _ ≤ 2*((Chunks.filter (fun p => band p=some (j+1))).card:ℝ) := hgrid
      _ ≤ 2*(Y*(Cdensity*M*R^2/(N*(Q j:ℝ)^2)*L)) :=
        mul_le_mul_of_nonneg_left (hbands j hj) (by norm_num)
      _ = (8*Cdensity)*(Y*M*R^2/(N*(Q (j+1):ℝ)^2))*L := by
        rw [hstep]
        field_simp
        ring
      _ ≤ (16*Cbase^2+8*Cdensity)*(Y*M*R^2/(N*(Q (j+1):ℝ)^2))*L :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hcoef (by positivity)) hLp
      _ = _ := by ring

example
    (Chunks : Finset (ℝ × ℤ)) (band : (ℝ × ℤ) → Option ℕ)
    (Grid : ℕ → ℤ → Finset (ℝ × ℤ)) (Qbase kmax : ℕ)
    {Y M N R Cbase Cdensity L : ℝ}
    (hQbase : 0 < Qbase) (hY : 0 ≤ Y) (hM : 0 ≤ M) (hN : 0 < N)
    (hCd : 0 ≤ Cdensity) (hL : 1 ≤ L)
    (hbase : (Qbase:ℝ) ≤ Cbase*R)
    (hchunks : (Chunks.card:ℝ) ≤ Y*(8*M/N)) :
    let Q := fun k : ℕ => Qbase*2^k
    (∀ j ≤ kmax, ((Chunks.filter (fun p => band p=some (j+1))).card:ℝ) ≤
      Y*(Cdensity*M*R^2/(N*(Q j:ℝ)^2)*L)) →
    (∀ k ≤ kmax, ∀ r : ℤ,
      (Grid k r).card ≤ 2*(Chunks.filter (fun p => band p=some k)).card) →
    ∀ k ≤ kmax, ∀ r : ℤ,
      ((Grid k r).card:ℝ) ≤
        (16*Cbase^2+8*Cdensity)*Y*M*R^2/(N*(Q k:ℝ)^2)*L := by
  exact selected_band_grid_cardinality_bound Chunks band Grid Qbase kmax hQbase hY hM hN hCd hL hbase hchunks

#print axioms selected_band_grid_cardinality_bound

/-- The actual selected-grid cardinality and actual phase image consume the
occupied-band counts inside the physical twelfth-moment summand. No substitute
family or assumed family-moment estimate is introduced. -/
private theorem double_difference_actual_selected_grid_family_monomials
    (Chunks : Finset (ℝ × ℤ)) (Y : Finset ℝ)
    (band : (ℝ × ℤ) → Option ℕ) (Qbase kmax : ℕ)
    (Kmesh Usel : ℕ → ℕ) (delta : ℕ → ℝ)
    {M N R Jsep c U θ D Cdelta C₀ Cmain Ctail B Cmesh Cbase Cdensity L T ε : ℝ}
    (hQbase : 0 < Qbase) (hM : 0 < M) (hN : 0 < N) (hR : 0 < R)
    (hJ : 0 ≤ Jsep) (hc : 0 < c) (hU : 0 < U) (hθ : 0 ≤ θ)
    (hD : 0 ≤ D) (hCd : 0 ≤ Cdelta) (hC : 0 ≤ C₀)
    (hmain : 0 ≤ Cmain) (htail : 0 ≤ Ctail) (hB : 0 < B)
    (hCm : 0 < Cmesh) (hDensity : 0 ≤ Cdensity) (hL : 1 ≤ L)
    (hT : 1 ≤ T) (hε : 0 ≤ ε) (hNR : N ≤ R^2) (hNT : N ≤ T)
    (hbase : (Qbase:ℝ) ≤ Cbase*R)
    (hchunks : (Chunks.card:ℝ) ≤ (Y.card:ℝ)*(8*M/N))
    (hband : U*M/(N*R^2) ≤ 1) :
    let Q := fun k : ℕ => Qbase*2^k
    let Selected := fun k => Chunks.filter (fun p => band p=some k)
    let Grid := fun (k : ℕ) (r : ℤ) =>
      ((Selected k).filter (fun p => p.2%8=r)).image (fun p => (p.1,p.2/8-2))
    (∀ j ≤ kmax, ((Chunks.filter (fun p => band p=some (j+1))).card:ℝ) ≤
      (Y.card:ℝ)*(Cdensity*M*R^2/(N*(Q j:ℝ)^2)*L)) →
    (∀ k r, (Grid k r).image Prod.fst ⊆ Y) →
    (∀ k ≤ kmax, 0 < Kmesh k ∧ R ≤ (Q k:ℝ) ∧ (Q k:ℝ) ≤ N ∧
      (Kmesh k:ℝ) ≤ Cmesh*(Q k:ℝ)*N/R^2 ∧
      0 ≤ delta k ∧ delta k ≤ Cdelta*R^2/N^2 ∧
      (N/(Q k:ℝ))^((2:ℝ)/3)/(2*B) ≤ (Usel k:ℝ)) →
    let H := U*M/(N*R^2)
    let lambda := c*M/(2*N*R^2)
    let Ctri := 2+θ*(1+2*U/c)
    let Ccard := 16*Cbase^2+8*Cdensity
    ∀ k ≤ kmax, ∀ r : ℤ,
      let Z := (((Grid k r).image Prod.fst).card:ℝ)
      let P := ((Grid k r).card:ℝ)
      let V := max 1 (H*N/(Q k:ℝ))
      (R^2/(Q k:ℝ))^6*(Kmesh k:ℝ)^((12:ℝ)+ε)*(2*P)^10*
        (V*D*(2+θ*(H+1/lambda))*Z*(M/N)*(1+delta k*Jsep)+
          Z^2*(C₀*H^2*(R^8/N^4)*
            (Cmain*((Q k:ℝ)/(H*N))^((2:ℝ)/3)+Ctail/(Usel k:ℝ)))*T^ε) ≤
        (Cmesh^12*Cmesh^ε*(2*Ccard)^10)*T^(2*ε)*L^10*
          (Ctri*D*((Y.card:ℝ)^11*M^10*N^2/(U*R^4)+(Y.card:ℝ)^11*M^11*N^2/R^7+
            Cdelta*(Y.card:ℝ)^11*Jsep*M^10/(U*R^2)+
              Cdelta*(Y.card:ℝ)^11*Jsep*M^11/R^5)+
            C₀*(Cmain+2*B*Ctail)*((Y.card:ℝ)^12*M^10*R^2/N^2)*
              (R/N)^((2:ℝ)/3)*H^((4:ℝ)/3))
 := by
  classical
  intro Q Selected Grid hbands hphase hvalid H lambda Ctri Ccard k hk r Z P V
  have hgrid j (_hj : j ≤ kmax) s :
      (Grid j s).card ≤ 2*(Chunks.filter (fun p => band p=some j)).card := by
    have hh : (Grid j s).card ≤ (Selected j).card :=
      Finset.card_image_le.trans (Finset.card_filter_le _ _)
    change (Grid j s).card ≤ 2*(Selected j).card
    omega
  have hcount := selected_band_grid_cardinality_bound Chunks band Grid Qbase kmax
    hQbase (Nat.cast_nonneg Y.card) hM.le hN hDensity hL hbase hchunks hbands hgrid k hk r
  have hZ : 0 ≤ Z := Nat.cast_nonneg _
  have hP : 0 ≤ P := Nat.cast_nonneg _
  have hZY : Z ≤ Y.card := by
    dsimp only [Z]
    exact_mod_cast Finset.card_le_card (hphase k r)
  obtain ⟨hK,hRQ,hQN,hmesh,hd,hdelta,hUlower⟩ := hvalid k hk
  exact double_difference_selected_grid_family_monomials
    (Nat.cast_nonneg Y.card) hZ hZY hP hM hN hR hRQ (by exact_mod_cast hK)
    hJ hc hU hθ hD hCd hd hC hmain htail hB hCm hT hε hQN hNR hNT
    hmesh hcount hdelta hband hUlower

example
    (Chunks : Finset (ℝ × ℤ)) (Y : Finset ℝ)
    (band : (ℝ × ℤ) → Option ℕ) (Qbase kmax : ℕ)
    (Kmesh Usel : ℕ → ℕ) (delta : ℕ → ℝ)
    {M N R Jsep c U θ D Cdelta C₀ Cmain Ctail B Cmesh Cbase Cdensity L T ε : ℝ}
    (hQbase : 0 < Qbase) (hM : 0 < M) (hN : 0 < N) (hR : 0 < R)
    (hJ : 0 ≤ Jsep) (hc : 0 < c) (hU : 0 < U) (hθ : 0 ≤ θ)
    (hD : 0 ≤ D) (hCd : 0 ≤ Cdelta) (hC : 0 ≤ C₀)
    (hmain : 0 ≤ Cmain) (htail : 0 ≤ Ctail) (hB : 0 < B)
    (hCm : 0 < Cmesh) (hDensity : 0 ≤ Cdensity) (hL : 1 ≤ L)
    (hT : 1 ≤ T) (hε : 0 ≤ ε) (hNR : N ≤ R^2) (hNT : N ≤ T)
    (hbase : (Qbase:ℝ) ≤ Cbase*R)
    (hchunks : (Chunks.card:ℝ) ≤ (Y.card:ℝ)*(8*M/N))
    (hband : U*M/(N*R^2) ≤ 1) :
    let Q := fun k : ℕ => Qbase*2^k
    let Selected := fun k => Chunks.filter (fun p => band p=some k)
    let Grid := fun (k : ℕ) (r : ℤ) =>
      ((Selected k).filter (fun p => p.2%8=r)).image (fun p => (p.1,p.2/8-2))
    (∀ j ≤ kmax, ((Chunks.filter (fun p => band p=some (j+1))).card:ℝ) ≤
      (Y.card:ℝ)*(Cdensity*M*R^2/(N*(Q j:ℝ)^2)*L)) →
    (∀ k r, (Grid k r).image Prod.fst ⊆ Y) →
    (∀ k ≤ kmax, 0 < Kmesh k ∧ R ≤ (Q k:ℝ) ∧ (Q k:ℝ) ≤ N ∧
      (Kmesh k:ℝ) ≤ Cmesh*(Q k:ℝ)*N/R^2 ∧
      0 ≤ delta k ∧ delta k ≤ Cdelta*R^2/N^2 ∧
      (N/(Q k:ℝ))^((2:ℝ)/3)/(2*B) ≤ (Usel k:ℝ)) →
    let H := U*M/(N*R^2)
    let lambda := c*M/(2*N*R^2)
    let Ctri := 2+θ*(1+2*U/c)
    let Ccard := 16*Cbase^2+8*Cdensity
    ∀ k ≤ kmax, ∀ r : ℤ,
      let Z := (((Grid k r).image Prod.fst).card:ℝ)
      let P := ((Grid k r).card:ℝ)
      let V := max 1 (H*N/(Q k:ℝ))
      (R^2/(Q k:ℝ))^6*(Kmesh k:ℝ)^((12:ℝ)+ε)*(2*P)^10*
        (V*D*(2+θ*(H+1/lambda))*Z*(M/N)*(1+delta k*Jsep)+
          Z^2*(C₀*H^2*(R^8/N^4)*
            (Cmain*((Q k:ℝ)/(H*N))^((2:ℝ)/3)+Ctail/(Usel k:ℝ)))*T^ε) ≤
        (Cmesh^12*Cmesh^ε*(2*Ccard)^10)*T^(2*ε)*L^10*
          (Ctri*D*((Y.card:ℝ)^11*M^10*N^2/(U*R^4)+(Y.card:ℝ)^11*M^11*N^2/R^7+
            Cdelta*(Y.card:ℝ)^11*Jsep*M^10/(U*R^2)+
              Cdelta*(Y.card:ℝ)^11*Jsep*M^11/R^5)+
            C₀*(Cmain+2*B*Ctail)*((Y.card:ℝ)^12*M^10*R^2/N^2)*
              (R/N)^((2:ℝ)/3)*H^((4:ℝ)/3))
 := by
  exact double_difference_actual_selected_grid_family_monomials Chunks Y band Qbase kmax Kmesh Usel delta hQbase hM hN hR hJ hc hU hθ
    hD hCd hC hmain htail hB hCm hDensity hL hT hε hNR hNT hbase hchunks hband

#print axioms double_difference_actual_selected_grid_family_monomials

/-- Unchanged existing private physical spacing proof, copied only for scratch access;
promotion reuses its original declaration. -/
private theorem physical_mesh_type_spacing_bound
    {α Cmesh N R Q K : ℝ}
    (hα : 0 ≤ α) (hC : 0 ≤ Cmesh) (hN : 0 < N)
    (hR : 0 < R) (hQ : 0 < Q) (hK : 0 < K)
    (hmesh : Q*N ≤ K*R^2)
    (hupper : K ≤ Cmesh*Q*N/R^2) :
    Real.sqrt ((α/(N*R^2))*Q^3)*Real.sqrt K/K^2 ≤
      Real.sqrt (α*Cmesh)*R^2/N^2 := by
  have hprod : (α/(N*R^2))*Q^3*K ≤ α*Cmesh*(Q^2/R^2)^2 := by
    calc
      _ ≤ (α/(N*R^2))*Q^3*(Cmesh*Q*N/R^2) :=
        mul_le_mul_of_nonneg_left hupper (by positivity)
      _ = _ := by field_simp
  have hroot :
      Real.sqrt ((α/(N*R^2))*Q^3)*Real.sqrt K ≤
        Real.sqrt (α*Cmesh)*(Q^2/R^2) := by
    rw [←Real.sqrt_mul (by positivity : 0 ≤ (α/(N*R^2))*Q^3)]
    calc
      _ ≤ Real.sqrt (α*Cmesh*(Q^2/R^2)^2) := Real.sqrt_le_sqrt hprod
      _ = _ := by
        rw [Real.sqrt_mul (mul_nonneg hα hC),
          Real.sqrt_sq (by positivity : 0 ≤ Q^2/R^2)]
  have hsq := pow_le_pow_left₀ (mul_pos hQ hN).le hmesh 2
  have hquot : Q^2/R^2/K^2 ≤ R^2/N^2 := by
    apply (div_le_div_iff₀ (sq_pos_of_pos hK) (sq_pos_of_pos hN)).mpr
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ (sq_pos_of_pos hR)).mpr
    convert hsq using 1 <;> ring
  calc
    _ ≤ (Real.sqrt (α*Cmesh)*(Q^2/R^2))/K^2 :=
      div_le_div_of_nonneg_right hroot (sq_nonneg K)
    _ = Real.sqrt (α*Cmesh)*(Q^2/R^2/K^2) := by ring
    _ ≤ Real.sqrt (α*Cmesh)*(R^2/N^2) :=
      mul_le_mul_of_nonneg_left hquot (Real.sqrt_nonneg _)
    _ = _ := by ring

example
    {α Cmesh N R Q K : ℝ}
    (hα : 0 ≤ α) (hC : 0 ≤ Cmesh) (hN : 0 < N)
    (hR : 0 < R) (hQ : 0 < Q) (hK : 0 < K)
    (hmesh : Q*N ≤ K*R^2)
    (hupper : K ≤ Cmesh*Q*N/R^2) :
    Real.sqrt ((α/(N*R^2))*Q^3)*Real.sqrt K/K^2 ≤
      Real.sqrt (α*Cmesh)*R^2/N^2 := by
  exact physical_mesh_type_spacing_bound hα hC hN hR hQ hK hmesh hupper

#print axioms physical_mesh_type_spacing_bound

/-- Unchanged existing private physical spacing proof, copied only for scratch access;
promotion reuses its original declaration. -/
private theorem positive_difference_source_type_spacing_bound
    {σ c J T M N R Q K Cmesh : ℝ}
    (hσ : 0 < σ) (hc : 0 < c) (hJ : 0 ≤ J)
    (hT : 0 < T) (hM : 0 < M) (hN : 0 < N)
    (hR : 0 < R) (hQ : 0 < Q) (hK : 0 < K) (hC : 0 ≤ Cmesh)
    (hscale : T*N*R^2=M^3)
    (hmesh : Q*N ≤ K*R^2) (hupper : K ≤ Cmesh*Q*N/R^2) :
    let μ₀ := c*T/(12*σ*M^3)
    let U₀ := J*T/(2*σ*M^3)
    (16*U₀/μ₀)*Real.sqrt (U₀*Q^3)*Real.sqrt K/(6*K^2) ≤
      (16*J/c)*Real.sqrt ((J/(2*σ))*Cmesh)*R^2/N^2 := by
  intro μ₀ U₀
  have hU : U₀=(J/(2*σ))/(N*R^2) := by
    dsimp only [U₀]
    rw [←hscale]
    field_simp
  have hratio : 16*U₀/μ₀=96*J/c := by
    dsimp only [U₀,μ₀]
    field_simp
    ring
  have hh := physical_mesh_type_spacing_bound
    (show 0 ≤ J/(2*σ) by positivity) hC hN hR hQ hK hmesh hupper
  calc
    _ = (16*J/c)*(Real.sqrt (((J/(2*σ))/(N*R^2))*Q^3)*Real.sqrt K/K^2) := by
      rw [hratio,hU]
      ring
    _ ≤ (16*J/c)*(Real.sqrt ((J/(2*σ))*Cmesh)*R^2/N^2) :=
      mul_le_mul_of_nonneg_left hh (by positivity)
    _ = _ := by ring

example
    {σ c J T M N R Q K Cmesh : ℝ}
    (hσ : 0 < σ) (hc : 0 < c) (hJ : 0 ≤ J)
    (hT : 0 < T) (hM : 0 < M) (hN : 0 < N)
    (hR : 0 < R) (hQ : 0 < Q) (hK : 0 < K) (hC : 0 ≤ Cmesh)
    (hscale : T*N*R^2=M^3)
    (hmesh : Q*N ≤ K*R^2) (hupper : K ≤ Cmesh*Q*N/R^2) :
    let μ₀ := c*T/(12*σ*M^3)
    let U₀ := J*T/(2*σ*M^3)
    (16*U₀/μ₀)*Real.sqrt (U₀*Q^3)*Real.sqrt K/(6*K^2) ≤
      (16*J/c)*Real.sqrt ((J/(2*σ))*Cmesh)*R^2/N^2 := by
  exact positive_difference_source_type_spacing_bound hσ hc hJ hT hM hN hR hQ hK hC hscale hmesh hupper

#print axioms positive_difference_source_type_spacing_bound


/-- The same occupied-grid estimate now consumes the actual source curvature and
actual Fourier Type-I spacing. Their physical identities and spacing bound follow
from T*N*R^2=M^3 and the chosen mesh, not from independent exponent assumptions. -/
private theorem double_difference_actual_source_grid_monomials
    (Chunks : Finset (ℝ × ℤ)) (Y : Finset ℝ)
    (band : (ℝ × ℤ) → Option ℕ) (Qbase kmax : ℕ)
    (Kmesh Usel : ℕ → ℕ)
    {M N R Jsep c U θ D Cmain Ctail B Cmesh Cbase Cdensity L T ε : ℝ}
    (hQbase : 0 < Qbase) (hM : 0 < M) (hN : 0 < N) (hR : 0 < R)
    (hJ : 0 ≤ Jsep) (hc : 0 < c) (hU : 0 < U) (hθ : 0 ≤ θ)
    (hD : 0 ≤ D)
    (hmain : 0 ≤ Cmain) (htail : 0 ≤ Ctail) (hB : 0 < B)
    (hCm : 0 < Cmesh) (hDensity : 0 ≤ Cdensity) (hL : 1 ≤ L)
    (hT : 1 ≤ T) (hε : 0 ≤ ε) (hNR : N ≤ R^2) (hNT : N ≤ T)
    (hbase : (Qbase:ℝ) ≤ Cbase*R)
    (hchunks : (Chunks.card:ℝ) ≤ (Y.card:ℝ)*(8*M/N))
    (hscale : T*N*R^2=M^3) (hband : U*T/M^2 ≤ 1) :
    let Q := fun k : ℕ => Qbase*2^k
    let Selected := fun k => Chunks.filter (fun p => band p=some k)
    let Grid := fun (k : ℕ) (r : ℤ) =>
      ((Selected k).filter (fun p => p.2%8=r)).image (fun p => (p.1,p.2/8-2))
    (∀ j ≤ kmax, ((Chunks.filter (fun p => band p=some (j+1))).card:ℝ) ≤
      (Y.card:ℝ)*(Cdensity*M*R^2/(N*(Q j:ℝ)^2)*L)) →
    (∀ k r, (Grid k r).image Prod.fst ⊆ Y) →
    (∀ k ≤ kmax, 0 < Kmesh k ∧ R ≤ (Q k:ℝ) ∧ (Q k:ℝ) ≤ N ∧
      (Q k:ℝ)*N ≤ (Kmesh k:ℝ)*R^2 ∧
      (Kmesh k:ℝ) ≤ Cmesh*(Q k:ℝ)*N/R^2 ∧
      (N/(Q k:ℝ))^((2:ℝ)/3)/(2*B) ≤ (Usel k:ℝ)) →
    let H := U*T/M^2
    let lambda := c*T/(2*M^2)
    let μ₀ := c*T/(12*M^3)
    let U₀ := U*T/(2*M^3)
    let delta := fun k : ℕ =>
      (16*U₀/μ₀)*Real.sqrt (U₀*(Q k:ℝ)^3)*Real.sqrt (Kmesh k)/(6*(Kmesh k:ℝ)^2)
    let Cdelta := (16*U/c)*Real.sqrt ((U/2)*Cmesh)
    let C₀ := 60*588*(2*U/c)^2
    let Ctri := 2+θ*(1+2*U/c)
    let Ccard := 16*Cbase^2+8*Cdensity
    ∀ k ≤ kmax, ∀ r : ℤ,
      let Z := (((Grid k r).image Prod.fst).card:ℝ)
      let P := ((Grid k r).card:ℝ)
      let V := max 1 (H*N/(Q k:ℝ))
      (R^2/(Q k:ℝ))^6*(Kmesh k:ℝ)^((12:ℝ)+ε)*(2*P)^10*
        (V*D*(2+θ*(H+1/lambda))*Z*(M/N)*(1+delta k*Jsep)+
          Z^2*(60*588*(H/lambda)^2*H^2*(R^8/N^4)*
            (Cmain*((Q k:ℝ)/(H*N))^((2:ℝ)/3)+Ctail/(Usel k:ℝ)))*T^ε) ≤
        (Cmesh^12*Cmesh^ε*(2*Ccard)^10)*T^(2*ε)*L^10*
          (Ctri*D*((Y.card:ℝ)^11*M^10*N^2/(U*R^4)+(Y.card:ℝ)^11*M^11*N^2/R^7+
            Cdelta*(Y.card:ℝ)^11*Jsep*M^10/(U*R^2)+
              Cdelta*(Y.card:ℝ)^11*Jsep*M^11/R^5)+
            C₀*(Cmain+2*B*Ctail)*((Y.card:ℝ)^12*M^10*R^2/N^2)*
              (R/N)^((2:ℝ)/3)*H^((4:ℝ)/3))
 := by
  classical
  intro Q Selected Grid hbands hphase hvalid H lambda μ₀ U₀ delta Cdelta C₀ Ctri Ccard k hk r Z P V
  have hTp : 0 < T := zero_lt_one.trans_le hT
  have hTidentity : T=M^3/(N*R^2) :=
    (eq_div_iff (show N*R^2 ≠ 0 by positivity)).mpr (by nlinarith only [hscale])
  have hH : H=U*M/(N*R^2) := by
    dsimp only [H]
    rw [hTidentity]
    field_simp
  have hLam : lambda=c*M/(2*N*R^2) := by
    dsimp only [lambda]
    rw [hTidentity]
    field_simp
  have hratio : H/lambda=2*U/c := by
    dsimp only [H,lambda]
    field_simp
  have hCd : 0 ≤ Cdelta := by dsimp only [Cdelta]; positivity
  have hC : 0 ≤ C₀ := by dsimp only [C₀]; positivity
  have hvalid' j (hj : j ≤ kmax) :
      0 < Kmesh j ∧ R ≤ (Q j:ℝ) ∧ (Q j:ℝ) ≤ N ∧
      (Kmesh j:ℝ) ≤ Cmesh*(Q j:ℝ)*N/R^2 ∧
      0 ≤ delta j ∧ delta j ≤ Cdelta*R^2/N^2 ∧
      (N/(Q j:ℝ))^((2:ℝ)/3)/(2*B) ≤ (Usel j:ℝ) := by
    obtain ⟨hK,hRQ,hQN,hmesh,hupper,hUlower⟩ := hvalid j hj
    have hKp : (0:ℝ) < Kmesh j := by exact_mod_cast hK
    have hd : 0 ≤ delta j := by dsimp only [delta,μ₀,U₀]; positivity
    have hdelta := positive_difference_source_type_spacing_bound
      (σ:=(1:ℝ)) (c:=c) (J:=U)
      (by norm_num) hc hU.le hTp hM hN hR (hR.trans_le hRQ) hKp hCm.le
      hscale hmesh hupper
    refine ⟨hK,hRQ,hQN,hupper,hd,?_,hUlower⟩
    simpa only [mul_one,one_mul] using hdelta
  have hband' : U*M/(N*R^2) ≤ 1 := by rw [←hH]; exact hband
  have hh := double_difference_actual_selected_grid_family_monomials
    Chunks Y band Qbase kmax Kmesh Usel delta
    hQbase hM hN hR hJ hc hU hθ hD hCd hC hmain htail hB hCm hDensity hL
    hT hε hNR hNT hbase hchunks hband' hbands hphase hvalid' k hk r
  rw [hratio]
  simpa only [←hH,←hLam] using hh

example
    (Chunks : Finset (ℝ × ℤ)) (Y : Finset ℝ)
    (band : (ℝ × ℤ) → Option ℕ) (Qbase kmax : ℕ)
    (Kmesh Usel : ℕ → ℕ)
    {M N R Jsep c U θ D Cmain Ctail B Cmesh Cbase Cdensity L T ε : ℝ}
    (hQbase : 0 < Qbase) (hM : 0 < M) (hN : 0 < N) (hR : 0 < R)
    (hJ : 0 ≤ Jsep) (hc : 0 < c) (hU : 0 < U) (hθ : 0 ≤ θ)
    (hD : 0 ≤ D)
    (hmain : 0 ≤ Cmain) (htail : 0 ≤ Ctail) (hB : 0 < B)
    (hCm : 0 < Cmesh) (hDensity : 0 ≤ Cdensity) (hL : 1 ≤ L)
    (hT : 1 ≤ T) (hε : 0 ≤ ε) (hNR : N ≤ R^2) (hNT : N ≤ T)
    (hbase : (Qbase:ℝ) ≤ Cbase*R)
    (hchunks : (Chunks.card:ℝ) ≤ (Y.card:ℝ)*(8*M/N))
    (hscale : T*N*R^2=M^3) (hband : U*T/M^2 ≤ 1) :
    let Q := fun k : ℕ => Qbase*2^k
    let Selected := fun k => Chunks.filter (fun p => band p=some k)
    let Grid := fun (k : ℕ) (r : ℤ) =>
      ((Selected k).filter (fun p => p.2%8=r)).image (fun p => (p.1,p.2/8-2))
    (∀ j ≤ kmax, ((Chunks.filter (fun p => band p=some (j+1))).card:ℝ) ≤
      (Y.card:ℝ)*(Cdensity*M*R^2/(N*(Q j:ℝ)^2)*L)) →
    (∀ k r, (Grid k r).image Prod.fst ⊆ Y) →
    (∀ k ≤ kmax, 0 < Kmesh k ∧ R ≤ (Q k:ℝ) ∧ (Q k:ℝ) ≤ N ∧
      (Q k:ℝ)*N ≤ (Kmesh k:ℝ)*R^2 ∧
      (Kmesh k:ℝ) ≤ Cmesh*(Q k:ℝ)*N/R^2 ∧
      (N/(Q k:ℝ))^((2:ℝ)/3)/(2*B) ≤ (Usel k:ℝ)) →
    let H := U*T/M^2
    let lambda := c*T/(2*M^2)
    let μ₀ := c*T/(12*M^3)
    let U₀ := U*T/(2*M^3)
    let delta := fun k : ℕ =>
      (16*U₀/μ₀)*Real.sqrt (U₀*(Q k:ℝ)^3)*Real.sqrt (Kmesh k)/(6*(Kmesh k:ℝ)^2)
    let Cdelta := (16*U/c)*Real.sqrt ((U/2)*Cmesh)
    let C₀ := 60*588*(2*U/c)^2
    let Ctri := 2+θ*(1+2*U/c)
    let Ccard := 16*Cbase^2+8*Cdensity
    ∀ k ≤ kmax, ∀ r : ℤ,
      let Z := (((Grid k r).image Prod.fst).card:ℝ)
      let P := ((Grid k r).card:ℝ)
      let V := max 1 (H*N/(Q k:ℝ))
      (R^2/(Q k:ℝ))^6*(Kmesh k:ℝ)^((12:ℝ)+ε)*(2*P)^10*
        (V*D*(2+θ*(H+1/lambda))*Z*(M/N)*(1+delta k*Jsep)+
          Z^2*(60*588*(H/lambda)^2*H^2*(R^8/N^4)*
            (Cmain*((Q k:ℝ)/(H*N))^((2:ℝ)/3)+Ctail/(Usel k:ℝ)))*T^ε) ≤
        (Cmesh^12*Cmesh^ε*(2*Ccard)^10)*T^(2*ε)*L^10*
          (Ctri*D*((Y.card:ℝ)^11*M^10*N^2/(U*R^4)+(Y.card:ℝ)^11*M^11*N^2/R^7+
            Cdelta*(Y.card:ℝ)^11*Jsep*M^10/(U*R^2)+
              Cdelta*(Y.card:ℝ)^11*Jsep*M^11/R^5)+
            C₀*(Cmain+2*B*Ctail)*((Y.card:ℝ)^12*M^10*R^2/N^2)*
              (R/N)^((2:ℝ)/3)*H^((4:ℝ)/3))
 := by
  exact double_difference_actual_source_grid_monomials Chunks Y band Qbase kmax Kmesh Usel hQbase hM hN hR hJ hc hU hθ
    hD hmain htail hB hCm hDensity hL hT hε hNR hNT hbase hchunks hscale hband

#print axioms double_difference_actual_source_grid_monomials

/-- Unchanged existing private source-error/logarithm proof; promotion reuses the original. -/
private theorem physical_band_logarithmic_bounds
    {Carg Cmesh T N R Q K kmax : ℝ}
    (hCarg : 0 ≤ Carg) (hCmesh : 1 ≤ Cmesh)
    (hT : 1 ≤ T) (hR : 1 ≤ R) (hRQ : R ≤ Q)
    (hQN : Q ≤ N) (hNR : N ≤ R^2) (hNT : N ≤ T)
    (hK : 0 < K) (hKupper : K ≤ Cmesh*Q*N/R^2)
    (hkmax : kmax ≤ Real.log N/Real.log 2) :
    2+Real.log (Carg*R^2/Q+1) ≤ (3+Real.log (Carg+1))*(1+Real.log T) ∧
    1+Real.log K ≤ (3+Real.log (Cmesh+1))*(1+Real.log T) ∧
    kmax+2 ≤ (2+1/Real.log 2)*(1+Real.log T) := by
  have hRp : 0 < R := zero_lt_one.trans_le hR
  have hQ : 0 < Q := hRp.trans_le hRQ
  have hN : 0 < N := hQ.trans_le hQN
  have hTp : 0 < T := zero_lt_one.trans_le hT
  have hlogT : 0 ≤ Real.log T := Real.log_nonneg hT
  have hlinear (C z : ℝ) (hC : 0 ≤ C) (hz : 0 ≤ z) (hzT : z ≤ C*T) :
      2+Real.log (z+1) ≤ (3+Real.log (C+1))*(1+Real.log T) := by
    have hCp : 0 < C+1 := by linarith only [hC]
    have hbound : z+1 ≤ (C+1)*T := by nlinarith only [hzT,hT]
    have hh := Real.log_le_log (by linarith only [hz] : 0 < z+1) hbound
    rw [Real.log_mul hCp.ne' hTp.ne'] at hh
    have hlogC : 0 ≤ Real.log (C+1) := Real.log_nonneg (by linarith only [hC])
    nlinarith only [hh,hlogC,hlogT,mul_nonneg hlogC hlogT]
  have hRT : R ≤ T := hRQ.trans (hQN.trans hNT)
  have hRquot : R^2/Q ≤ R := (div_le_iff₀ hQ).mpr (by
    nlinarith only [mul_le_mul_of_nonneg_left hRQ hRp.le])
  have harg : Carg*R^2/Q ≤ Carg*T := by
    calc
      _ = Carg*(R^2/Q) := by ring
      _ ≤ Carg*T := mul_le_mul_of_nonneg_left (hRquot.trans hRT) hCarg
  have hKT : K ≤ Cmesh*T := by
    calc
      _ ≤ Cmesh*Q*N/R^2 := hKupper
      _ ≤ Cmesh*Q := (div_le_iff₀ (sq_pos_of_pos hRp)).mpr
        (mul_le_mul_of_nonneg_left hNR (by positivity))
      _ ≤ Cmesh*T := mul_le_mul_of_nonneg_left (hQN.trans hNT) (by positivity)
  refine ⟨hlinear Carg _ hCarg (by positivity) harg,?_,?_⟩
  · have hh := hlinear Cmesh K (by positivity) hK.le hKT
    have hlogK := Real.log_le_log hK (by linarith : K ≤ K+1)
    linarith only [hh,hlogK]
  · have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hlogN := Real.log_le_log hN hNT
    have hq := div_le_div_of_nonneg_right hlogN hlog2.le
    have hh := hkmax.trans hq
    have he : (2+1/Real.log 2)*(1+Real.log T) =
        2+Real.log T/Real.log 2+2*Real.log T+1/Real.log 2 := by ring
    rw [he]
    nlinarith only [hh,hlogT,one_div_pos.mpr hlog2]

example
    {Carg Cmesh T N R Q K kmax : ℝ}
    (hCarg : 0 ≤ Carg) (hCmesh : 1 ≤ Cmesh)
    (hT : 1 ≤ T) (hR : 1 ≤ R) (hRQ : R ≤ Q)
    (hQN : Q ≤ N) (hNR : N ≤ R^2) (hNT : N ≤ T)
    (hK : 0 < K) (hKupper : K ≤ Cmesh*Q*N/R^2)
    (hkmax : kmax ≤ Real.log N/Real.log 2) :
    2+Real.log (Carg*R^2/Q+1) ≤ (3+Real.log (Carg+1))*(1+Real.log T) ∧
    1+Real.log K ≤ (3+Real.log (Cmesh+1))*(1+Real.log T) ∧
    kmax+2 ≤ (2+1/Real.log 2)*(1+Real.log T) := by
  exact physical_band_logarithmic_bounds hCarg hCmesh hT hR hRQ hQN hNR hNT hK hKupper hkmax

#print axioms physical_band_logarithmic_bounds

/-- Unchanged existing private source-error/logarithm proof; promotion reuses the original. -/
private theorem positive_difference_completion_error_physical_bound
    {Y M N R T C : ℝ} (hY : 0 ≤ Y) (hN : 1 ≤ N)
    (hNM : N ≤ M) (hMT : M ≤ T) (hC : 0 ≤ C) :
    Y*(M/N+1)*(Real.sqrt (3*N)*Real.log (6*N)+C*R^2/N) ≤
      (2*Real.sqrt 3*(1+Real.log 6)+2*C)*
        (Y*M/Real.sqrt N+Y*M*R^2/N^2)*(1+Real.log T) := by
  have hNp : 0 < N := zero_lt_one.trans_le hN
  have hMp : 0 < M := hNp.trans_le hNM
  have hT : 1 ≤ T := hN.trans (hNM.trans hMT)
  have hlogT : 0 ≤ Real.log T := Real.log_nonneg hT
  have hlog6 : 0 ≤ Real.log 6 := Real.log_nonneg (by norm_num)
  have hlogN := Real.log_le_log hNp (hNM.trans hMT)
  have hlog : Real.log (6*N) ≤ (1+Real.log 6)*(1+Real.log T) := by
    rw [Real.log_mul (by norm_num : (6:ℝ) ≠ 0) hNp.ne']
    nlinarith only [hlogN,hlog6,hlogT,mul_nonneg hlog6 hlogT]
  have hlogPos : 0 ≤ Real.log (6*N) := Real.log_nonneg (by linarith only [hN])
  have hL : 1 ≤ 1+Real.log T := by linarith only [hlogT]
  have hratio : 1 ≤ M/N := (le_div_iff₀ hNp).mpr (by simpa only [one_mul] using hNM)
  have hfront : M/N+1 ≤ 2*M/N := by
    calc
      _ ≤ M/N+M/N := add_le_add le_rfl hratio
      _ = _ := by ring
  have hsum : Real.sqrt (3*N)*Real.log (6*N)+C*R^2/N ≤
      (Real.sqrt 3*Real.sqrt N*(1+Real.log 6)+C*R^2/N)*(1+Real.log T) := by
    have hc := le_mul_of_one_le_right (by positivity : 0 ≤ C*R^2/N) hL
    calc
      _ = Real.sqrt 3*Real.sqrt N*Real.log (6*N)+C*R^2/N := by
        rw [Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 3)]
      _ ≤ Real.sqrt 3*Real.sqrt N*((1+Real.log 6)*(1+Real.log T))+
          (C*R^2/N)*(1+Real.log T) :=
        add_le_add (mul_le_mul_of_nonneg_left hlog (by positivity)) hc
      _ = _ := by ring
  have hcancel : M/N*Real.sqrt N=M/Real.sqrt N := by
    calc
      _ = M*(Real.sqrt N/N) := by ring
      _ = _ := by rw [Real.sqrt_div_self']; ring
  let A := 2*Real.sqrt 3*(1+Real.log 6)
  let E₁ := Y*M/Real.sqrt N
  let E₂ := Y*M*R^2/N^2
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  have hE₁ : 0 ≤ E₁ := by dsimp only [E₁]; positivity
  have hE₂ : 0 ≤ E₂ := by dsimp only [E₂]; positivity
  calc
    _ ≤ Y*(2*M/N)*
        ((Real.sqrt 3*Real.sqrt N*(1+Real.log 6)+C*R^2/N)*(1+Real.log T)) := by
      gcongr
    _ = (A*(Y*(M/N*Real.sqrt N))+2*C*E₂)*(1+Real.log T) := by
      dsimp only [A,E₂]
      ring
    _ = (A*E₁+2*C*E₂)*(1+Real.log T) := by
      rw [hcancel]
      dsimp only [E₁]
      ring
    _ ≤ ((A+2*C)*(E₁+E₂))*(1+Real.log T) := by
      apply mul_le_mul_of_nonneg_right _ (by linarith only [hlogT])
      nlinarith only [mul_nonneg hA hE₂,mul_nonneg hC hE₁]
    _ = _ := rfl

example
    {Y M N R T C : ℝ} (hY : 0 ≤ Y) (hN : 1 ≤ N)
    (hNM : N ≤ M) (hMT : M ≤ T) (hC : 0 ≤ C) :
    Y*(M/N+1)*(Real.sqrt (3*N)*Real.log (6*N)+C*R^2/N) ≤
      (2*Real.sqrt 3*(1+Real.log 6)+2*C)*
        (Y*M/Real.sqrt N+Y*M*R^2/N^2)*(1+Real.log T) := by
  exact positive_difference_completion_error_physical_bound hY hN hNM hMT hC

#print axioms positive_difference_completion_error_physical_bound

/-- Unchanged existing private source-error/logarithm proof; promotion reuses the original. -/
private theorem positive_difference_endpoint_error_physical_bound
    {Y N n R Q U κ σ c Cphys B : ℝ}
    (hY : 0 ≤ Y) (hN : 1 ≤ N) (hR : 0 < R) (hRQ : R ≤ Q) (hQN : Q ≤ N)
    (hκ : 0 < κ) (hσ : 0 ≤ σ) (hc : 0 < c) (hCphys : 0 ≤ Cphys)
    (hB : 1 ≤ B) (hscale : N=8*n)
    (hUupper : U ≤ (N/Q)^((2:ℝ)/3)/B) :
    Y*(2*((56*U/κ)*N+N/(Cphys+2)+2)+
        2*((14*σ/c)*U*N)+6*N+2*n) ≤
      (112/κ+28*σ/c+2/(Cphys+2)+41/4)*
        (Y*N*(N/R)^((2:ℝ)/3)) := by
  have hNp : 0 < N := zero_lt_one.trans_le hN
  have hQ : 0 < Q := hR.trans_le hRQ
  let X := (N/R)^((2:ℝ)/3)
  let A := 112/κ+28*σ/c
  let E := 2/(Cphys+2)+25/4
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  have hE : 0 ≤ E := by dsimp only [E]; positivity
  have hn : n=N/8 := by linarith only [hscale]
  have hUX : U ≤ X := by
    calc
      _ ≤ (N/Q)^((2:ℝ)/3)/B := hUupper
      _ ≤ (N/Q)^((2:ℝ)/3) := div_le_self (by positivity) hB
      _ ≤ (N/R)^((2:ℝ)/3) := Real.rpow_le_rpow (by positivity)
        (div_le_div_of_nonneg_left hNp.le hR hRQ) (by norm_num)
  have hX : 1 ≤ X := Real.one_le_rpow
    ((le_div_iff₀ hR).mpr (by simpa only [one_mul] using hRQ.trans hQN)) (by norm_num)
  have hNX : N ≤ X*N := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hX hNp.le
  have hXN : 1 ≤ X*N := hN.trans hNX
  calc
    _ = Y*(A*(U*N)+E*N+4) := by
      dsimp only [A,E]
      rw [hn]
      ring
    _ ≤ Y*(A*(X*N)+E*(X*N)+4*(X*N)) := by
      apply mul_le_mul_of_nonneg_left _ hY
      exact add_le_add
        (add_le_add
          (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hUX hNp.le) hA)
          (mul_le_mul_of_nonneg_left hNX hE))
        (by nlinarith only [hXN])
    _ = _ := by
      dsimp only [A,E,X]
      ring

example
    {Y N n R Q U κ σ c Cphys B : ℝ}
    (hY : 0 ≤ Y) (hN : 1 ≤ N) (hR : 0 < R) (hRQ : R ≤ Q) (hQN : Q ≤ N)
    (hκ : 0 < κ) (hσ : 0 ≤ σ) (hc : 0 < c) (hCphys : 0 ≤ Cphys)
    (hB : 1 ≤ B) (hscale : N=8*n)
    (hUupper : U ≤ (N/Q)^((2:ℝ)/3)/B) :
    Y*(2*((56*U/κ)*N+N/(Cphys+2)+2)+
        2*((14*σ/c)*U*N)+6*N+2*n) ≤
      (112/κ+28*σ/c+2/(Cphys+2)+41/4)*
        (Y*N*(N/R)^((2:ℝ)/3)) := by
  exact positive_difference_endpoint_error_physical_bound hY hN hR hRQ hQN hκ hσ hc hCphys hB hscale hUupper

#print axioms positive_difference_endpoint_error_physical_bound

/-- The two actual source coefficients are nonnegative; the main coefficient
reuses the existing proof and the tail uses the same explicit source constants. -/
private theorem model_source_large_entry_coefficients_nonneg
    {σ δ : ℝ} (hσ : 0 < σ) (hδ₀ : 0 ≤ δ) :
    let κ := modelPhaseThirdLower σ
    let Cphys := σ*(σ+1)+1
    let c := κ/6
    let J := Cphys/6
    let B := max 1 (max (2*Real.sqrt J) (8*J*Real.sqrt J/(3*c)))
    let C₂ := modelPhaseJetCoefficient σ 2+δ
    let C₃ := modelPhaseJetCoefficient σ 3+δ
    let Ct := C₂/2+5*C₃/12
    let Cc := C₂/κ+C₃/(2*κ)
    let Kres := 4*(37*B/2+16*B*Cc+2*Ct+2*Cc+
      2*quarticNonlinearResidualConstant σ δ)/κ
    let Lunit := 2*κ/Cphys
    let Gamma := Cphys/κ
    let Cthird := Gamma*(32*Kres+9*quarticReciprocalConstant σ δ)
    let Cpack := 64*Cphys*(Gamma^2*Cthird+Gamma*(modelPhaseJetCoefficient σ 3+δ)/κ)/κ
    let Cfirst := 128*Cphys*(Gamma^2*Cthird+Gamma*(modelPhaseJetCoefficient σ 3+δ)/κ)/κ^2
    let Cgap := 64*Cphys*(Gamma^2*B+Gamma*(modelPhaseJetCoefficient σ 3+δ)/κ)/κ
    let Cmain := 4*(2*Cfirst/Lunit^3)^((3:ℝ)⁻¹)+2
    let Ctail := 4*Cpack/Lunit^2+Cgap
    0 ≤ Cmain ∧ 0 ≤ Ctail
 := by
  intro κ Cphys c J B C₂ C₃ Ct Cc Kres Lunit Gamma Cthird Cpack Cfirst Cgap Cmain Ctail
  have hκ : 0 < κ := modelPhaseThirdLower_pos hσ
  have hCphys : 0 < Cphys := by dsimp only [Cphys]; positivity
  have hC₂ : 0 ≤ C₂ := add_nonneg (modelPhaseJetCoefficient_nonneg σ 2) hδ₀
  have hC₃ : 0 ≤ C₃ := add_nonneg (modelPhaseJetCoefficient_nonneg σ 3) hδ₀
  have hC₄ : 0 ≤ modelPhaseJetCoefficient σ 4+δ :=
    add_nonneg (modelPhaseJetCoefficient_nonneg σ 4) hδ₀
  have hRes : 0 ≤ quarticNonlinearResidualConstant σ δ := by
    dsimp only [quarticNonlinearResidualConstant]
    positivity
  have hRecip : 0 ≤ quarticReciprocalConstant σ δ := by
    dsimp only [quarticReciprocalConstant]
    positivity
  have hB : 0 ≤ B := zero_le_one.trans (le_max_left _ _)
  have hCt : 0 ≤ Ct := by dsimp only [Ct]; positivity
  have hCc : 0 ≤ Cc := by dsimp only [Cc]; positivity
  have hKres : 0 ≤ Kres := by dsimp only [Kres]; positivity
  have hLunit : 0 < Lunit := by dsimp only [Lunit]; positivity
  have hGamma : 0 ≤ Gamma := by dsimp only [Gamma]; positivity
  have hCthird : 0 ≤ Cthird := by dsimp only [Cthird]; positivity
  have hCpack : 0 ≤ Cpack := by dsimp only [Cpack]; positivity
  have hCgap : 0 ≤ Cgap := by dsimp only [Cgap]; positivity
  exact ⟨model_source_large_entry_main_coefficient_nonneg hσ hδ₀,
    by dsimp only [Ctail]; positivity⟩

example
    {σ δ : ℝ} (hσ : 0 < σ) (hδ₀ : 0 ≤ δ) :
    let κ := modelPhaseThirdLower σ
    let Cphys := σ*(σ+1)+1
    let c := κ/6
    let J := Cphys/6
    let B := max 1 (max (2*Real.sqrt J) (8*J*Real.sqrt J/(3*c)))
    let C₂ := modelPhaseJetCoefficient σ 2+δ
    let C₃ := modelPhaseJetCoefficient σ 3+δ
    let Ct := C₂/2+5*C₃/12
    let Cc := C₂/κ+C₃/(2*κ)
    let Kres := 4*(37*B/2+16*B*Cc+2*Ct+2*Cc+
      2*quarticNonlinearResidualConstant σ δ)/κ
    let Lunit := 2*κ/Cphys
    let Gamma := Cphys/κ
    let Cthird := Gamma*(32*Kres+9*quarticReciprocalConstant σ δ)
    let Cpack := 64*Cphys*(Gamma^2*Cthird+Gamma*(modelPhaseJetCoefficient σ 3+δ)/κ)/κ
    let Cfirst := 128*Cphys*(Gamma^2*Cthird+Gamma*(modelPhaseJetCoefficient σ 3+δ)/κ)/κ^2
    let Cgap := 64*Cphys*(Gamma^2*B+Gamma*(modelPhaseJetCoefficient σ 3+δ)/κ)/κ
    let Cmain := 4*(2*Cfirst/Lunit^3)^((3:ℝ)⁻¹)+2
    let Ctail := 4*Cpack/Lunit^2+Cgap
    0 ≤ Cmain ∧ 0 ≤ Ctail
 := by
  exact model_source_large_entry_coefficients_nonneg hσ hδ₀

#print axioms model_source_large_entry_coefficients_nonneg

/-- Numerical completion/logarithm composition, with no analytic conclusion assumed. -/
private theorem completed_family_logarithmic_power_bound
    {CF C Cap W Cpref CK Ce Tp L Main E Perror Qpref Klog : ℝ}
    (hC : 0 ≤ C) (hCap : 0 ≤ Cap) (hPref : 0 ≤ Cpref)
    (hTp : 1 ≤ Tp) (hL : 1 ≤ L)
    (hMain : 0 ≤ Main) (hPerror : 0 ≤ Perror)
    (hKlog : 0 ≤ Klog) (hlog : Klog ≤ CK*L)
    (hnum : Qpref ≤ Cpref*Tp*L^10*Main)
    (herror : Perror ≤ Ce*E*L) :
    CF^12*2^11*(Klog^12*W^6*(C*Cap^11*Qpref)+Perror^12) ≤
      (CF^12*2^11*(C*Cap^11*W^6*CK^12*Cpref+Ce^12))*
        Tp*L^22*(Main+E^12)
 := by
  have hTnon : 0 ≤ Tp := zero_le_one.trans hTp
  have hLnon : 0 ≤ L := zero_le_one.trans hL
  have hlogPow : Klog^12 ≤ CK^12*L^12 := by
    simpa only [mul_pow] using pow_le_pow_left₀ hKlog hlog 12
  let A := C*Cap^11*W^6*CK^12*Cpref
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  have hmainBound : Klog^12*W^6*(C*Cap^11*Qpref) ≤
      A*Tp*L^22*Main := by
    calc
      _ = (C*Cap^11*W^6)*Klog^12*Qpref := by ring
      _ ≤ (C*Cap^11*W^6)*Klog^12*(Cpref*Tp*L^10*Main) :=
        mul_le_mul_of_nonneg_left hnum (by positivity)
      _ ≤ (C*Cap^11*W^6)*(CK^12*L^12)*(Cpref*Tp*L^10*Main) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hlogPow (by positivity)) (by positivity)
      _ = _ := by dsimp only [A]; ring
  have herrorBound : Perror^12 ≤ Ce^12*Tp*L^22*E^12 := by
    calc
      _ ≤ (Ce*E*L)^12 := pow_le_pow_left₀ hPerror herror 12
      _ = Ce^12*L^12*E^12 := by ring
      _ ≤ Ce^12*(Tp*L^22)*E^12 := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact (pow_le_pow_right₀ hL (show 12 ≤ 22 by omega)).trans
          (le_mul_of_one_le_left (by positivity) hTp)
      _ = _ := by ring
  calc
    _ ≤ CF^12*2^11*(A*Tp*L^22*Main+Ce^12*Tp*L^22*E^12) :=
      mul_le_mul_of_nonneg_left (add_le_add hmainBound herrorBound) (by positivity)
    _ ≤ CF^12*2^11*(A*Tp*L^22*(Main+E^12)+Ce^12*Tp*L^22*(Main+E^12)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact add_le_add
        (mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (by positivity)) (by positivity))
        (mul_le_mul_of_nonneg_left (le_add_of_nonneg_left hMain) (by positivity))
    _ = _ := by dsimp only [A]; ring


example
    {CF C Cap W Cpref CK Ce Tp L Main E Perror Qpref Klog : ℝ}
    (hC : 0 ≤ C) (hCap : 0 ≤ Cap) (hPref : 0 ≤ Cpref)
    (hTp : 1 ≤ Tp) (hL : 1 ≤ L)
    (hMain : 0 ≤ Main) (hPerror : 0 ≤ Perror)
    (hKlog : 0 ≤ Klog) (hlog : Klog ≤ CK*L)
    (hnum : Qpref ≤ Cpref*Tp*L^10*Main)
    (herror : Perror ≤ Ce*E*L) :
    CF^12*2^11*(Klog^12*W^6*(C*Cap^11*Qpref)+Perror^12) ≤
      (CF^12*2^11*(C*Cap^11*W^6*CK^12*Cpref+Ce^12))*
        Tp*L^22*(Main+E^12)
 := by
  exact completed_family_logarithmic_power_bound hC hCap hPref hTp hL hMain hPerror hKlog hlog hnum herror

#print axioms completed_family_logarithmic_power_bound

/-- Exact finite aggregation of the eight residue grids and all denominator bands,
including terminal and endpoint errors, within a single logarithmic power. -/
private theorem all_band_logarithmic_power_aggregation
    (kmax : ℕ) (Family : ℕ → ℤ → ℝ)
    {Cband Cfamily Cterminal Cendpoint Tp L Main E Term Endpoint X : ℝ}
    (hCband : 0 ≤ Cband) (hFamily : 0 ≤ Cfamily)
    (hMass : 0 ≤ Main) (hError : 0 ≤ E)
    (hLlog : 1 ≤ L) (hTpow : 1 ≤ Tp)
    (hTerm : 0 ≤ Term) (hEndpointNon : 0 ≤ Endpoint)
    (hbandCount : (kmax:ℝ)+2 ≤ Cband*L)
    (hfamily : ∀ k ≤ kmax, ∀ r : ℤ,
      Family k r ≤ Cfamily*Tp*L^22*(Main+E^12))
    (hterminal : Term ≤ Cterminal*E*L)
    (hendpoint : Endpoint ≤ Cendpoint*E) :
    X^12 ≤ 2^11*(((kmax:ℝ)+2)^11*
      (Term^12+(8:ℝ)^11*∑ k∈Finset.range (kmax+1),
        ∑ r∈Finset.Ico (0:ℤ) 8,Family k r)+Endpoint^12) →
    X^12 ≤ (2:ℝ)^11*
      (Cband^11*(Cterminal^12+(8:ℝ)^12*Cband*Cfamily)+Cendpoint^12)*
        Tp*L^36*(Main+E^12)
 := by
  classical
  have hTpowNon : 0 ≤ Tp := zero_le_one.trans hTpow
  have hLnon : 0 ≤ L := zero_le_one.trans hLlog
  let S := Main+E^12
  have hS : 0 ≤ S := add_nonneg hMass (pow_nonneg hError 12)
  have hES : E^12 ≤ S := le_add_of_nonneg_left hMass
  have hsum :
      (∑ k∈Finset.range (kmax+1),
        ∑ r∈Finset.Ico (0:ℤ) 8,Family k r) ≤
          (8*Cband*Cfamily)*Tp*L^23*S := by
    calc
      _ ≤ ∑ k∈Finset.range (kmax+1),∑ _r∈Finset.Ico (0:ℤ) 8,
          Cfamily*Tp*L^22*S :=
        Finset.sum_le_sum (fun k hk => Finset.sum_le_sum (fun r _ =>
          hfamily k (by have hh := Finset.mem_range.mp hk; omega) r))
      _ = ((kmax:ℝ)+1)*8*(Cfamily*Tp*L^22*S) := by
        simp only [Finset.sum_const,Finset.card_range,Int.card_Ico,Int.reduceSub,
          Int.reduceToNat,nsmul_eq_mul,Nat.cast_add,Nat.cast_one,Nat.cast_ofNat]
        ring
      _ ≤ (Cband*L)*8*(Cfamily*Tp*L^22*S) := by
        gcongr
        linarith only [hbandCount]
      _ = _ := by ring
  have hterminalPow :
      (Term)^12 ≤
        Cterminal^12*Tp*L^23*S := by
    calc
      _ ≤ (Cterminal*E*L)^12 :=
        pow_le_pow_left₀ (by positivity) hterminal 12
      _ = Cterminal^12*L^12*E^12 := by ring
      _ ≤ Cterminal^12*(Tp*L^23)*S := by
        apply mul_le_mul
        · apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact (pow_le_pow_right₀ hLlog (show 12 ≤ 23 by omega)).trans
            (le_mul_of_one_le_left (by positivity) hTpow)
        · exact hES
        · positivity
        · positivity
      _ = _ := by ring
  have hinside :
      (Term)^12+
        (8:ℝ)^11*∑ k∈Finset.range (kmax+1),
          ∑ r∈Finset.Ico (0:ℤ) 8,Family k r ≤
        (Cterminal^12+(8:ℝ)^12*Cband*Cfamily)*Tp*L^23*S := by
    calc
      _ ≤ Cterminal^12*Tp*L^23*S+
          (8:ℝ)^11*((8*Cband*Cfamily)*Tp*L^23*S) :=
        add_le_add hterminalPow (mul_le_mul_of_nonneg_left hsum (by norm_num))
      _ = _ := by ring
  have houter :
      ((kmax:ℝ)+2)^11*
        ((Term)^12+
          (8:ℝ)^11*∑ k∈Finset.range (kmax+1),
            ∑ r∈Finset.Ico (0:ℤ) 8,Family k r) ≤
        (Cband^11*(Cterminal^12+(8:ℝ)^12*Cband*Cfamily))*
          Tp*L^36*S := by
    calc
      _ ≤ (Cband*L)^11*
          ((Cterminal^12+(8:ℝ)^12*Cband*Cfamily)*Tp*L^23*S) := by
        exact (mul_le_mul_of_nonneg_left hinside (by positivity)).trans
          (mul_le_mul_of_nonneg_right
            (pow_le_pow_left₀ (by positivity) hbandCount 11) (by positivity))
      _ = (Cband^11*(Cterminal^12+(8:ℝ)^12*Cband*Cfamily))*
          Tp*L^34*S := by ring
      _ ≤ _ := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left
            (pow_le_pow_right₀ hLlog (show 34 ≤ 36 by norm_num)) (by positivity)) hS
  have hendpointPow : Endpoint^12 ≤
      Cendpoint^12*Tp*L^36*S := by
    calc
      _ ≤ (Cendpoint*E)^12 :=
        pow_le_pow_left₀ hEndpointNon hendpoint 12
      _ = Cendpoint^12*E^12 := by ring
      _ ≤ (Cendpoint^12*(Tp*L^36))*S := by
        apply mul_le_mul
        · exact le_mul_of_one_le_right (by positivity)
            (one_le_mul_of_one_le_of_one_le hTpow (one_le_pow₀ hLlog))
        · exact hES
        · positivity
        · positivity
      _ = _ := by ring
  intro hwhole
  calc
    _ ≤ 2^11*(((kmax:ℝ)+2)^11*
        ((Term)^12+
          (8:ℝ)^11*∑ k∈Finset.range (kmax+1),
            ∑ r∈Finset.Ico (0:ℤ) 8,Family k r)+Endpoint^12) := hwhole
    _ ≤ 2^11*((Cband^11*(Cterminal^12+(8:ℝ)^12*Cband*Cfamily))*
        Tp*L^36*S+Cendpoint^12*Tp*L^36*S) :=
      mul_le_mul_of_nonneg_left (add_le_add houter hendpointPow) (by norm_num)
    _ = _ := by dsimp only [S]; ring


example
    (kmax : ℕ) (Family : ℕ → ℤ → ℝ)
    {Cband Cfamily Cterminal Cendpoint Tp L Main E Term Endpoint X : ℝ}
    (hCband : 0 ≤ Cband) (hFamily : 0 ≤ Cfamily)
    (hMass : 0 ≤ Main) (hError : 0 ≤ E)
    (hLlog : 1 ≤ L) (hTpow : 1 ≤ Tp)
    (hTerm : 0 ≤ Term) (hEndpointNon : 0 ≤ Endpoint)
    (hbandCount : (kmax:ℝ)+2 ≤ Cband*L)
    (hfamily : ∀ k ≤ kmax, ∀ r : ℤ,
      Family k r ≤ Cfamily*Tp*L^22*(Main+E^12))
    (hterminal : Term ≤ Cterminal*E*L)
    (hendpoint : Endpoint ≤ Cendpoint*E) :
    X^12 ≤ 2^11*(((kmax:ℝ)+2)^11*
      (Term^12+(8:ℝ)^11*∑ k∈Finset.range (kmax+1),
        ∑ r∈Finset.Ico (0:ℤ) 8,Family k r)+Endpoint^12) →
    X^12 ≤ (2:ℝ)^11*
      (Cband^11*(Cterminal^12+(8:ℝ)^12*Cband*Cfamily)+Cendpoint^12)*
        Tp*L^36*(Main+E^12)
 := by
  exact all_band_logarithmic_power_aggregation kmax Family hCband hFamily hMass hError hLlog hTpow
    hTerm hEndpointNon hbandCount hfamily hterminal hendpoint

#print axioms all_band_logarithmic_power_aggregation

/-- The capped terminal column retains both reciprocal-scale error terms. -/
private theorem capped_terminal_density_error
    {M N R q Q n Y A L E Density : ℝ}
    (hM : 0 < M) (hN : 0 < N) (hq : 0 < q)
    (hY : 0 ≤ Y) (hA : 0 ≤ A) (hL : 0 ≤ L)
    (hn : N=8*n) (hcap : (q/2)*min N (M/N) ≤ Q)
    (hDensity : Density ≤ A*M*R^2/(N*Q^2)*L)
    (hError : Y*M*R^2/N^2+Y*N^2*R^2/M ≤ E) :
    n*Y*Density ≤ (A/(2*q^2))*E*L := by
  have hnval : n=N/8 := by linarith only [hn]
  have hnnon : 0 ≤ n := by rw [hnval]; positivity
  have hQ : 0 < Q :=
    lt_of_lt_of_le (mul_pos (by positivity) (lt_min hN (div_pos hM hN))) hcap
  have hphysical := capped_terminal_physical_error (R:=R) hM hN
    (show 0 < q/2 by positivity) hcap
  calc
    _ ≤ n*Y*(A*M*R^2/(N*Q^2)*L) :=
      mul_le_mul_of_nonneg_left hDensity (mul_nonneg hnnon hY)
    _ = (A*Y/8)*(M*R^2/Q^2)*L := by rw [hnval]; field_simp
    _ ≤ (A*Y/8)*((1/(q/2)^2)*(M*R^2/N^2+N^2*R^2/M))*L :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hphysical (by positivity)) hL
    _ = (A/(2*q^2))*(Y*M*R^2/N^2+Y*N^2*R^2/M)*L := by
      field_simp
      ring
    _ ≤ (A/(2*q^2))*E*L :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hError (by positivity)) hL

example
    {M N R q Q n Y A L E Density : ℝ}
    (hM : 0 < M) (hN : 0 < N) (hq : 0 < q)
    (hY : 0 ≤ Y) (hA : 0 ≤ A) (hL : 0 ≤ L)
    (hn : N=8*n) (hcap : (q/2)*min N (M/N) ≤ Q)
    (hDensity : Density ≤ A*M*R^2/(N*Q^2)*L)
    (hError : Y*M*R^2/N^2+Y*N^2*R^2/M ≤ E) :
    n*Y*Density ≤ (A/(2*q^2))*E*L := by
  exact capped_terminal_density_error hM hN hq hY hA hL hn hcap hDensity hError

#print axioms capped_terminal_density_error

/-- Finite numerical consequence of the actual occupied-band moment. The input
is the unsimplified upstream selected-family expression; the analytic consumer
below constructs that expression from the original source. -/
private theorem double_difference_finite_source_power_bound
    {csrc Usrc κ θ Cphys εloss CF C Dtype Cmain Ctail Cap Bselect : ℝ}
    (hcsrc : 0 < csrc) (hUsrc : 0 < Usrc) (hκ : 0 < κ)
    (hθ : 0 ≤ θ) (hCphys : 0 ≤ Cphys) (hεloss : 0 ≤ εloss)
    (hC : 0 ≤ C) (hDtype : 0 ≤ Dtype) (hmain : 0 ≤ Cmain) (htail : 0 ≤ Ctail)
    (hCap : 0 ≤ Cap) (hBselect : 1 ≤ Bselect)
    (Chunks : Finset (ℝ × ℤ)) (Y : Finset ℝ) (band : (ℝ × ℤ) → Option ℕ)
    (n N Qbase kmax : ℕ) (Kmesh Usel : ℕ → ℕ)
    {R Jsep M T Cbase Cmesh qcap X : ℝ}
    (hK : ∀ k, 0 < Kmesh k) (hNlink : N=8*n) (hNone : (1:ℝ) ≤ N)
    (hR : 1 ≤ R) (hJsep : 0 ≤ Jsep) (hNM : (N:ℝ) ≤ M)
    (hscale : T*(N:ℝ)*R^2=M^3) (hNR : (N:ℝ) ≤ R^2)
    (hUbandCap : Usrc*T/M^2 ≤ 1) (hTone : 1 ≤ T) (hMT : M ≤ T)
    (hQbase : 0 < Qbase) (hCm : 1 ≤ Cmesh) (hbase : (Qbase:ℝ) ≤ Cbase*R)
    (hklog : (kmax:ℝ) ≤ Real.log (N:ℝ)/Real.log 2) (hqcap : 0 < qcap) :
    let Q := fun k : ℕ => Qbase*2^k
    (qcap/2)*min (N:ℝ) (M/(N:ℝ)) ≤ (Q kmax:ℝ) →
    (∀ k ≤ kmax, R ≤ (Q k:ℝ) ∧ (Q k:ℝ) ≤ N ∧
      (Q k:ℝ)*(N:ℝ) ≤ (Kmesh k:ℝ)*R^2 ∧
      (Kmesh k:ℝ) ≤ Cmesh*(Q k:ℝ)*(N:ℝ)/R^2 ∧
      (Usel k:ℝ) ≤ ((N:ℝ)/(Q k:ℝ))^((2:ℝ)/3)/Bselect ∧
      ((N:ℝ)/(Q k:ℝ))^((2:ℝ)/3)/(2*Bselect) ≤ (Usel k:ℝ)) →
    let Selected := fun k => Chunks.filter (fun p => band p=some k)
    let Grid := fun (k : ℕ) (r : ℤ) =>
      ((Selected k).filter (fun p => p.2%8=r)).image (fun p => (p.1,p.2/8-2))
    let Uband := Usrc*T/M^2
    let CtailBand := 4*Usrc*(64/csrc)^2+192/csrc
    let ClowBand := (2*Usrc+csrc/32)*(3072/csrc)^2+3072/csrc
    let CerrorBand := (768:ℝ)^2*CtailBand+ClowBand
    let Carg := 512*768/csrc
    let Cdensity := 128*CerrorBand*(3+Real.log (Carg+1))
    let Ccard := 16*Cbase^2+8*Cdensity
    let Cdelta := (16*Usrc/csrc)*Real.sqrt ((Usrc/2)*Cmesh)
    let Ctri := 2+θ*(1+2*Usrc/csrc)
    let C₀ := 60*588*(2*Usrc/csrc)^2
    let MassPower := Ctri*Dtype*
      ((Y.card:ℝ)^11*M^10*(N:ℝ)^2/(Usrc*R^4)+
        (Y.card:ℝ)^11*M^11*(N:ℝ)^2/R^7+
        Cdelta*(Y.card:ℝ)^11*Jsep*M^10/(Usrc*R^2)+
        Cdelta*(Y.card:ℝ)^11*Jsep*M^11/R^5)+
      C₀*(Cmain+2*Bselect*Ctail)*((Y.card:ℝ)^12*M^10*R^2/(N:ℝ)^2)*
        (R/(N:ℝ))^((2:ℝ)/3)*Uband^((4:ℝ)/3)
    let ErrorPower := (Y.card:ℝ)*M/Real.sqrt (N:ℝ)+
      (Y.card:ℝ)*M*R^2/(N:ℝ)^2+(Y.card:ℝ)*(N:ℝ)^2*R^2/M+
      (Y.card:ℝ)*(N:ℝ)*((N:ℝ)/R)^((2:ℝ)/3)
    let Cpref := Cmesh^12*Cmesh^εloss*(2*Ccard)^10
    let Wconst := 144*Usrc/(csrc*κ)
    let CKlog := 3+Real.log (Cmesh+1)
    let Cerror := 8*(2*Real.sqrt 3*(1+Real.log 6)+72*Usrc/(csrc*κ))
    let Cfamily := CF^12*2^11*(C*Cap^11*Wconst^6*CKlog^12*Cpref+Cerror^12)
    let Cband := 2+1/Real.log 2
    let Cterminal := Cdensity/(2*qcap^2)
    let Cendpoint := 112/κ+2/(Cphys+2)+41/4
    let Ctotal := (2:ℝ)^11*
      (Cband^11*(Cterminal^12+(8:ℝ)^12*Cband*Cfamily)+Cendpoint^12)
    let lambda := csrc*T/(2*M^2)
    let μ₀ := csrc*T/(12*M^3)
    let U₀ := Usrc*T/(2*M^3)
    let Δtype := fun k : ℕ =>
      (16*U₀/μ₀)*Real.sqrt (U₀*(Q k:ℝ)^3)*Real.sqrt (Kmesh k)/(6*(Kmesh k:ℝ)^2)
    let Vscale := fun k : ℕ => max 1 (Uband*(N:ℝ)/(Q k:ℝ))
    let Klarge := fun k : ℕ => 60*588*(Uband/lambda)^2*Uband^2*(R^8/(N:ℝ)^4)*
      (Cmain*((Q k:ℝ)/(Uband*(N:ℝ)))^((2:ℝ)/3)+Ctail/(Usel k:ℝ))
    let PointError := Real.sqrt (3*(N:ℝ))*Real.log (6*(N:ℝ))+
      36*Usrc*R^2/(csrc*κ*(N:ℝ))
    let FamilyBound := fun (k : ℕ) (P : Finset (ℝ × ℤ)) =>
      let YP := P.image Prod.fst
      let Mass := Vscale k*Dtype*(2+θ*(Uband+1/lambda))*(YP.card:ℝ)*(M/(N:ℝ))*
        (1+Δtype k*Jsep)+(YP.card:ℝ)^2*Klarge k*T^εloss
      CF^12*2^11*((1+Real.log (Kmesh k))^12*(Wconst*(R^2/(Q k:ℝ)))^6*
        (C*(Kmesh k:ℝ)^((12:ℝ)+εloss)*Cap^11*(2*(P.card:ℝ))^10*Mass)+
        ((P.card:ℝ)*PointError)^12)
    let Density := fun k => 128*CerrorBand*(M*R^2/((N:ℝ)*(Q k:ℝ)^2))*
      (2+Real.log (512*R^2/(csrc*((Q k:ℝ)/768))+1))
    let Buffer := fun k : ℕ => (56*(Usel k:ℝ)/κ)*(N:ℝ)+(N:ℝ)/(Cphys+2)+2
    let Endpoint := (Y.card:ℝ)*(2*Buffer 0+6*(N:ℝ)+2*(n:ℝ))
    (Chunks.card:ℝ) ≤ (Y.card:ℝ)*(8*M/(N:ℝ)) →
    (∀ k ≤ kmax, ((Chunks.filter (fun p => band p=some (k+1))).card:ℝ) ≤
      (Y.card:ℝ)*Density k) →
    (∀ k r, (Grid k r).image Prod.fst ⊆ Y) →
    X^12 ≤ 2^11*(((kmax:ℝ)+2)^11*(((n:ℝ)*(Y.card:ℝ)*Density kmax)^12+
      (8:ℝ)^11*∑ k∈Finset.range (kmax+1),
        ∑ r∈Finset.Ico (0:ℤ) 8,FamilyBound k (Grid k r))+Endpoint^12) →
    X^12 ≤ Ctotal*T^(2*εloss)*(1+Real.log T)^36*(MassPower+ErrorPower^12)
 := by
  classical
  intro Q hQcap hvalid Selected Grid Uband
    CtailBand ClowBand CerrorBand Carg Cdensity Ccard Cdelta Ctri C₀
    MassPower ErrorPower Cpref Wconst CKlog Cerror Cfamily Cband Cterminal Cendpoint Ctotal
    lambda μ₀ U₀ Δtype Vscale Klarge PointError FamilyBound Density Buffer Endpoint
    hchunks hbands hphase
  have hNp : (0:ℝ) < N := zero_lt_one.trans_le hNone
  have hM : 0 < M := hNp.trans_le hNM
  have hRp : 0 < R := zero_lt_one.trans_le hR
  have hT : 0 < T := zero_lt_one.trans_le hTone
  have hBp : 0 < Bselect := zero_lt_one.trans_le hBselect
  have hQp k : (0:ℝ) < Q k := by
    exact_mod_cast Nat.mul_pos hQbase (by positivity : 0 < 2^k)
  have hgrids k r : (Grid k r).card ≤ (Selected k).card ∧
      (Grid k r).image Prod.fst ⊆ Y :=
    ⟨Finset.card_image_le.trans (Finset.card_filter_le _ _),hphase k r⟩
  have hCarg : 0 ≤ Carg := by clear * - hcsrc; dsimp only [Carg]; positivity
  have hlogArg : 0 ≤ Real.log (Carg+1) := Real.log_nonneg (by linarith only [hCarg])
  have hDensity : 0 ≤ Cdensity := by
    clear * - hcsrc hUsrc hlogArg
    dsimp only [Cdensity,CerrorBand,CtailBand,ClowBand]
    positivity
  have hCKlog : 0 ≤ CKlog := by
    clear * - hCm
    have hh : 0 ≤ Real.log (Cmesh+1) := Real.log_nonneg (by linarith only [hCm])
    dsimp only [CKlog]
    positivity
  have hCband : 0 ≤ Cband := by
    clear * - hκ
    have hh : 0 < Real.log 2 := Real.log_pos (by norm_num)
    dsimp only [Cband]
    positivity
  have hCerror : 0 ≤ Cerror := by
    clear * - hUsrc hcsrc hκ
    have hh : 0 ≤ Real.log 6 := Real.log_nonneg (by norm_num)
    dsimp only [Cerror]
    positivity
  have hCterminal : 0 ≤ Cterminal := by clear * - hDensity hqcap; dsimp only [Cterminal]; positivity
  have hCendpoint : 0 ≤ Cendpoint := by clear * - hκ hCphys; dsimp only [Cendpoint]; positivity
  have hWconst : 0 ≤ Wconst := by clear * - hUsrc hcsrc hκ; dsimp only [Wconst]; positivity
  have hCpref : 0 ≤ Cpref := by clear * - hCm; dsimp only [Cpref]; positivity
  have hFamily : 0 ≤ Cfamily := by clear * - hC hCap hWconst hCpref; dsimp only [Cfamily]; positivity
  have hMass : 0 ≤ MassPower := by
    clear * - hDtype hθ hUsrc hcsrc hmain htail hBp hNp hRp hM hJsep hT
    dsimp only [MassPower,Ctri,Cdelta,C₀,Uband]
    positivity
  have hError : 0 ≤ ErrorPower := by clear * - hM hNp hRp; dsimp only [ErrorPower]; positivity
  let Llog := 1+Real.log T
  have hLlog : 1 ≤ Llog := by
    have hh := Real.log_nonneg hTone
    dsimp only [Llog]
    linarith only [hh]
  have hLnon : 0 ≤ Llog := zero_le_one.trans hLlog
  have hTpow : 1 ≤ T^(2*εloss) := Real.one_le_rpow hTone (by positivity)
  have hTpowNon : 0 ≤ T^(2*εloss) := zero_le_one.trans hTpow
  have hlogs k (hk : k ≤ kmax) :
      2+Real.log (Carg*R^2/(Q k:ℝ)+1) ≤
        (3+Real.log (Carg+1))*Llog ∧
      1+Real.log (Kmesh k) ≤ CKlog*Llog ∧
      (kmax:ℝ)+2 ≤ Cband*Llog := by
    obtain ⟨hRQ,hQN,_,hupper,_,_⟩ := hvalid k hk
    exact physical_band_logarithmic_bounds hCarg hCm hTone hR hRQ hQN hNR
      (hNM.trans hMT) (by exact_mod_cast hK k) hupper hklog
  have hDensityBound k (hk : k ≤ kmax) :
      Density k ≤ Cdensity*M*R^2/((N:ℝ)*(Q k:ℝ)^2)*Llog := by
    have harg : 512*R^2/(csrc*((Q k:ℝ)/768))=Carg*R^2/(Q k:ℝ) := by
      dsimp only [Carg]
      field_simp
    dsimp only [Density]
    rw [harg]
    calc
      _ ≤ 128*CerrorBand*(M*R^2/((N:ℝ)*(Q k:ℝ)^2))*
          ((3+Real.log (Carg+1))*Llog) :=
        mul_le_mul_of_nonneg_left (hlogs k hk).1 (by
          dsimp only [CerrorBand,CtailBand,ClowBand]
          positivity)
      _ = _ := by dsimp only [Cdensity]; ring
  have hcounts k (hk : k ≤ kmax) :
      ((Chunks.filter (fun p => band p=some (k+1))).card:ℝ) ≤
        (Y.card:ℝ)*(Cdensity*M*R^2/((N:ℝ)*(Q k:ℝ)^2)*Llog) :=
    (hbands k hk).trans (mul_le_mul_of_nonneg_left
      (hDensityBound k hk) (Nat.cast_nonneg _))
  have hErrorSmall :
      (Y.card:ℝ)*M/Real.sqrt (N:ℝ)+(Y.card:ℝ)*M*R^2/(N:ℝ)^2 ≤ ErrorPower := by
    clear * - hM hNp hRp
    dsimp only [ErrorPower]
    exact (le_add_of_nonneg_right (by positivity)).trans
      (le_add_of_nonneg_right (by positivity))
  have hErrorTerminal :
      (Y.card:ℝ)*M*R^2/(N:ℝ)^2+(Y.card:ℝ)*(N:ℝ)^2*R^2/M ≤ ErrorPower := by
    clear * - hM hNp hRp
    dsimp only [ErrorPower]
    linarith only [show 0 ≤ (Y.card:ℝ)*M/Real.sqrt (N:ℝ) by positivity,
      show 0 ≤ (Y.card:ℝ)*(N:ℝ)*((N:ℝ)/R)^((2:ℝ)/3) by positivity]
  have hErrorEndpoint :
      (Y.card:ℝ)*(N:ℝ)*((N:ℝ)/R)^((2:ℝ)/3) ≤ ErrorPower := by
    clear * - hM hNp hRp
    dsimp only [ErrorPower]
    exact le_add_of_nonneg_left (by positivity)
  have hsumMass : 0 ≤ MassPower+ErrorPower^12 := add_nonneg hMass (pow_nonneg hError 12)
  have hfamily k (hk : k ≤ kmax) (r : ℤ) :
      FamilyBound k (Grid k r) ≤
        Cfamily*T^(2*εloss)*Llog^22*(MassPower+ErrorPower^12) := by
    let P := ((Grid k r).card:ℝ)
    let Z := (((Grid k r).image Prod.fst).card:ℝ)
    let Mass := Vscale k*Dtype*(2+θ*(Uband+1/lambda))*Z*(M/(N:ℝ))*
      (1+Δtype k*Jsep)+Z^2*Klarge k*T^εloss
    have hactual :=
      double_difference_actual_source_grid_monomials
        Chunks Y band Qbase kmax Kmesh Usel
        (by omega : 0 < Qbase) hM hNp hRp hJsep hcsrc hUsrc hθ hDtype
        hmain htail hBp (zero_lt_one.trans_le hCm) hDensity hLlog hTone
        hεloss hNR (hNM.trans hMT) hbase hchunks hscale hUbandCap
        hcounts (fun k r => (hgrids k r).2)
        (by
          intro j hj
          obtain ⟨hRQ,hQN,hmesh,hupper,_,hlower⟩ := hvalid j hj
          exact ⟨hK j,hRQ,hQN,hmesh,hupper,hlower⟩) k hk r
    have hnum :
        (R^2/(Q k:ℝ))^6*(Kmesh k:ℝ)^((12:ℝ)+εloss)*(2*P)^10*Mass ≤
          Cpref*T^(2*εloss)*Llog^10*MassPower := hactual
    clear hactual
    have hP : 0 ≤ P := Nat.cast_nonneg _
    have hPC : P ≤ (Chunks.card:ℝ) := by
      dsimp only [P]
      exact_mod_cast (hgrids k r).1.trans (Finset.card_filter_le _ _)
    have hpoint : 0 ≤ PointError := by
      have hh : 0 ≤ Real.log (6*(N:ℝ)) := Real.log_nonneg (by linarith only [hNone])
      dsimp only [PointError]
      positivity
    have hpe : P*PointError ≤ Cerror*ErrorPower*Llog := by
      have hh := positive_difference_completion_error_physical_bound
        (Y:=(Y.card:ℝ)) (R:=R) (C:=36*Usrc/(csrc*κ))
        (Nat.cast_nonneg _) hNone hNM hMT (by positivity)
      calc
        _ ≤ (8*((Y.card:ℝ)*(M/(N:ℝ)+1)))*PointError := by
          apply mul_le_mul_of_nonneg_right _ hpoint
          have hh := hPC.trans hchunks
          calc
            _ ≤ (Y.card:ℝ)*(8*M/(N:ℝ)) := hh
            _ = (8*(Y.card:ℝ))*(M/(N:ℝ)) := by ring
            _ ≤ (8*(Y.card:ℝ))*(M/(N:ℝ)+1) :=
              mul_le_mul_of_nonneg_left (le_add_of_nonneg_right zero_le_one) (by positivity)
            _ = _ := by ring
        _ = 8*((Y.card:ℝ)*(M/(N:ℝ)+1)*
            (Real.sqrt (3*(N:ℝ))*Real.log (6*(N:ℝ))+
              (36*Usrc/(csrc*κ))*R^2/(N:ℝ))) := by
          dsimp only [PointError]
          ring
        _ ≤ 8*((2*Real.sqrt 3*(1+Real.log 6)+2*(36*Usrc/(csrc*κ)))*
            ((Y.card:ℝ)*M/Real.sqrt (N:ℝ)+(Y.card:ℝ)*M*R^2/(N:ℝ)^2)*Llog) :=
          mul_le_mul_of_nonneg_left hh (by norm_num)
        _ = Cerror*((Y.card:ℝ)*M/Real.sqrt (N:ℝ)+
            (Y.card:ℝ)*M*R^2/(N:ℝ)^2)*Llog := by dsimp only [Cerror]; ring
        _ ≤ Cerror*ErrorPower*Llog := by gcongr
    have hlogK : 0 ≤ 1+Real.log (Kmesh k) := by
      have hh : (1:ℝ) ≤ Kmesh k := by
        exact_mod_cast (show 1 ≤ Kmesh k by have hh := hK k; omega)
      have hl := Real.log_nonneg hh
      linarith only [hl]
    have hh := completed_family_logarithmic_power_bound
      (CF:=CF) (W:=Wconst) hC hCap hCpref hTpow hLlog hMass
      (mul_nonneg hP hpoint) hlogK (hlogs k hk).2.1 hnum hpe
    calc
      _ = CF^12*2^11*((1+Real.log (Kmesh k))^12*Wconst^6*
          (C*Cap^11*((R^2/(Q k:ℝ))^6*
            (Kmesh k:ℝ)^((12:ℝ)+εloss)*(2*P)^10*Mass))+(P*PointError)^12) := by
        change CF^12*2^11*((1+Real.log (Kmesh k))^12*(Wconst*(R^2/(Q k:ℝ)))^6*
          (C*(Kmesh k:ℝ)^((12:ℝ)+εloss)*Cap^11*(2*P)^10*Mass)+(P*PointError)^12)=_
        ring
      _ ≤ _ := hh
  have hnReal : (N:ℝ)=8*(n:ℝ) := by exact_mod_cast hNlink
  have hterminal :
      (n:ℝ)*(Y.card:ℝ)*Density kmax ≤ Cterminal*ErrorPower*Llog :=
    capped_terminal_density_error hM hNp hqcap (Nat.cast_nonneg _) hDensity hLnon
      hnReal hQcap (hDensityBound kmax le_rfl) hErrorTerminal
  have hendpoint : Endpoint ≤ Cendpoint*ErrorPower := by
    obtain ⟨hRQ,hQN,_,_,hupper,_⟩ := hvalid 0 (Nat.zero_le _)
    have hh := positive_difference_endpoint_error_physical_bound
      (Y:=(Y.card:ℝ)) (σ:=0) (c:=1) (Nat.cast_nonneg _) hNone hRp hRQ hQN
      hκ (by rfl) (by norm_num) hCphys hBselect hnReal hupper
    have hh' : Endpoint ≤ Cendpoint*((Y.card:ℝ)*(N:ℝ)*((N:ℝ)/R)^((2:ℝ)/3)) := by
      simpa only [mul_zero,zero_mul,zero_div,add_zero,div_one] using hh
    exact hh'.trans (mul_le_mul_of_nonneg_left hErrorEndpoint hCendpoint)
  have hDensityNon : 0 ≤ Density kmax := by
    clear * - hcsrc hUsrc hM hNp hRp hQp
    have hh : 0 ≤ Real.log (512*R^2/(csrc*((Q kmax:ℝ)/768))+1) :=
      Real.log_nonneg (by
        have hh : 0 ≤ 512*R^2/(csrc*((Q kmax:ℝ)/768)) := by positivity
        linarith only [hh])
    dsimp only [Density,CerrorBand,CtailBand,ClowBand]
    positivity
  have hEndpointNon : 0 ≤ Endpoint := by
    clear * - hκ hCphys
    dsimp only [Endpoint,Buffer]
    positivity
  exact all_band_logarithmic_power_aggregation kmax (fun k r => FamilyBound k (Grid k r))
    hCband hFamily hMass hError hLlog hTpow
    (by positivity) hEndpointNon (hlogs 0 (Nat.zero_le _)).2.2 hfamily hterminal hendpoint


example
    {csrc Usrc κ θ Cphys εloss CF C Dtype Cmain Ctail Cap Bselect : ℝ}
    (hcsrc : 0 < csrc) (hUsrc : 0 < Usrc) (hκ : 0 < κ)
    (hθ : 0 ≤ θ) (hCphys : 0 ≤ Cphys) (hεloss : 0 ≤ εloss)
    (hC : 0 ≤ C) (hDtype : 0 ≤ Dtype) (hmain : 0 ≤ Cmain) (htail : 0 ≤ Ctail)
    (hCap : 0 ≤ Cap) (hBselect : 1 ≤ Bselect)
    (Chunks : Finset (ℝ × ℤ)) (Y : Finset ℝ) (band : (ℝ × ℤ) → Option ℕ)
    (n N Qbase kmax : ℕ) (Kmesh Usel : ℕ → ℕ)
    {R Jsep M T Cbase Cmesh qcap X : ℝ}
    (hK : ∀ k, 0 < Kmesh k) (hNlink : N=8*n) (hNone : (1:ℝ) ≤ N)
    (hR : 1 ≤ R) (hJsep : 0 ≤ Jsep) (hNM : (N:ℝ) ≤ M)
    (hscale : T*(N:ℝ)*R^2=M^3) (hNR : (N:ℝ) ≤ R^2)
    (hUbandCap : Usrc*T/M^2 ≤ 1) (hTone : 1 ≤ T) (hMT : M ≤ T)
    (hQbase : 0 < Qbase) (hCm : 1 ≤ Cmesh) (hbase : (Qbase:ℝ) ≤ Cbase*R)
    (hklog : (kmax:ℝ) ≤ Real.log (N:ℝ)/Real.log 2) (hqcap : 0 < qcap) :
    let Q := fun k : ℕ => Qbase*2^k
    (qcap/2)*min (N:ℝ) (M/(N:ℝ)) ≤ (Q kmax:ℝ) →
    (∀ k ≤ kmax, R ≤ (Q k:ℝ) ∧ (Q k:ℝ) ≤ N ∧
      (Q k:ℝ)*(N:ℝ) ≤ (Kmesh k:ℝ)*R^2 ∧
      (Kmesh k:ℝ) ≤ Cmesh*(Q k:ℝ)*(N:ℝ)/R^2 ∧
      (Usel k:ℝ) ≤ ((N:ℝ)/(Q k:ℝ))^((2:ℝ)/3)/Bselect ∧
      ((N:ℝ)/(Q k:ℝ))^((2:ℝ)/3)/(2*Bselect) ≤ (Usel k:ℝ)) →
    let Selected := fun k => Chunks.filter (fun p => band p=some k)
    let Grid := fun (k : ℕ) (r : ℤ) =>
      ((Selected k).filter (fun p => p.2%8=r)).image (fun p => (p.1,p.2/8-2))
    let Uband := Usrc*T/M^2
    let CtailBand := 4*Usrc*(64/csrc)^2+192/csrc
    let ClowBand := (2*Usrc+csrc/32)*(3072/csrc)^2+3072/csrc
    let CerrorBand := (768:ℝ)^2*CtailBand+ClowBand
    let Carg := 512*768/csrc
    let Cdensity := 128*CerrorBand*(3+Real.log (Carg+1))
    let Ccard := 16*Cbase^2+8*Cdensity
    let Cdelta := (16*Usrc/csrc)*Real.sqrt ((Usrc/2)*Cmesh)
    let Ctri := 2+θ*(1+2*Usrc/csrc)
    let C₀ := 60*588*(2*Usrc/csrc)^2
    let MassPower := Ctri*Dtype*
      ((Y.card:ℝ)^11*M^10*(N:ℝ)^2/(Usrc*R^4)+
        (Y.card:ℝ)^11*M^11*(N:ℝ)^2/R^7+
        Cdelta*(Y.card:ℝ)^11*Jsep*M^10/(Usrc*R^2)+
        Cdelta*(Y.card:ℝ)^11*Jsep*M^11/R^5)+
      C₀*(Cmain+2*Bselect*Ctail)*((Y.card:ℝ)^12*M^10*R^2/(N:ℝ)^2)*
        (R/(N:ℝ))^((2:ℝ)/3)*Uband^((4:ℝ)/3)
    let ErrorPower := (Y.card:ℝ)*M/Real.sqrt (N:ℝ)+
      (Y.card:ℝ)*M*R^2/(N:ℝ)^2+(Y.card:ℝ)*(N:ℝ)^2*R^2/M+
      (Y.card:ℝ)*(N:ℝ)*((N:ℝ)/R)^((2:ℝ)/3)
    let Cpref := Cmesh^12*Cmesh^εloss*(2*Ccard)^10
    let Wconst := 144*Usrc/(csrc*κ)
    let CKlog := 3+Real.log (Cmesh+1)
    let Cerror := 8*(2*Real.sqrt 3*(1+Real.log 6)+72*Usrc/(csrc*κ))
    let Cfamily := CF^12*2^11*(C*Cap^11*Wconst^6*CKlog^12*Cpref+Cerror^12)
    let Cband := 2+1/Real.log 2
    let Cterminal := Cdensity/(2*qcap^2)
    let Cendpoint := 112/κ+2/(Cphys+2)+41/4
    let Ctotal := (2:ℝ)^11*
      (Cband^11*(Cterminal^12+(8:ℝ)^12*Cband*Cfamily)+Cendpoint^12)
    let lambda := csrc*T/(2*M^2)
    let μ₀ := csrc*T/(12*M^3)
    let U₀ := Usrc*T/(2*M^3)
    let Δtype := fun k : ℕ =>
      (16*U₀/μ₀)*Real.sqrt (U₀*(Q k:ℝ)^3)*Real.sqrt (Kmesh k)/(6*(Kmesh k:ℝ)^2)
    let Vscale := fun k : ℕ => max 1 (Uband*(N:ℝ)/(Q k:ℝ))
    let Klarge := fun k : ℕ => 60*588*(Uband/lambda)^2*Uband^2*(R^8/(N:ℝ)^4)*
      (Cmain*((Q k:ℝ)/(Uband*(N:ℝ)))^((2:ℝ)/3)+Ctail/(Usel k:ℝ))
    let PointError := Real.sqrt (3*(N:ℝ))*Real.log (6*(N:ℝ))+
      36*Usrc*R^2/(csrc*κ*(N:ℝ))
    let FamilyBound := fun (k : ℕ) (P : Finset (ℝ × ℤ)) =>
      let YP := P.image Prod.fst
      let Mass := Vscale k*Dtype*(2+θ*(Uband+1/lambda))*(YP.card:ℝ)*(M/(N:ℝ))*
        (1+Δtype k*Jsep)+(YP.card:ℝ)^2*Klarge k*T^εloss
      CF^12*2^11*((1+Real.log (Kmesh k))^12*(Wconst*(R^2/(Q k:ℝ)))^6*
        (C*(Kmesh k:ℝ)^((12:ℝ)+εloss)*Cap^11*(2*(P.card:ℝ))^10*Mass)+
        ((P.card:ℝ)*PointError)^12)
    let Density := fun k => 128*CerrorBand*(M*R^2/((N:ℝ)*(Q k:ℝ)^2))*
      (2+Real.log (512*R^2/(csrc*((Q k:ℝ)/768))+1))
    let Buffer := fun k : ℕ => (56*(Usel k:ℝ)/κ)*(N:ℝ)+(N:ℝ)/(Cphys+2)+2
    let Endpoint := (Y.card:ℝ)*(2*Buffer 0+6*(N:ℝ)+2*(n:ℝ))
    (Chunks.card:ℝ) ≤ (Y.card:ℝ)*(8*M/(N:ℝ)) →
    (∀ k ≤ kmax, ((Chunks.filter (fun p => band p=some (k+1))).card:ℝ) ≤
      (Y.card:ℝ)*Density k) →
    (∀ k r, (Grid k r).image Prod.fst ⊆ Y) →
    X^12 ≤ 2^11*(((kmax:ℝ)+2)^11*(((n:ℝ)*(Y.card:ℝ)*Density kmax)^12+
      (8:ℝ)^11*∑ k∈Finset.range (kmax+1),
        ∑ r∈Finset.Ico (0:ℤ) 8,FamilyBound k (Grid k r))+Endpoint^12) →
    X^12 ≤ Ctotal*T^(2*εloss)*(1+Real.log T)^36*(MassPower+ErrorPower^12)
 := by
  exact double_difference_finite_source_power_bound hcsrc hUsrc hκ hθ hCphys hεloss hC hDtype hmain htail hCap hBselect
    Chunks Y band n N Qbase kmax Kmesh Usel hK hNlink hNone hR hJsep hNM
    hscale hNR hUbandCap hTone hMT hQbase hCm hbase hklog hqcap

#print axioms double_difference_finite_source_power_bound

/-- Actual source-family twelfth moment: constructs its own bands and residue grids,
uses their physical spacing and occupied counts, and retains both capped terminal errors.
Only source jets/models and explicit scalar budgets remain for scale assembly. -/
private theorem eventually_double_difference_all_source_physical_powers
    {csrc Usrc σ εloss : ℝ}
    (hcsrc : 0 < csrc) (hUsrc : 0 < Usrc)
    (hσ : 0 < σ) (hεloss : 0 < εloss) :
    let κ := modelPhaseThirdLower σ
    let L := max (32*Usrc^2/csrc^2)
      (64*(modelPhaseJetCoefficient σ 3+1)*Usrc/κ^2)
    let θ := 1/(8*(L+3))
    ∃ CF C Dtype : ℝ, 1 ≤ CF ∧ 0 < C ∧ 0 < Dtype ∧
    ∀ᶠ T : ℝ in Filter.atTop, ∀ (Fsrc rshift sshift : ℝ → ℝ) (Y : Finset ℝ)
    (n N Qbase kmax : ℕ) (Kmesh Usel : ℕ → ℕ) (R Jsep : ℝ)
    {d Wmax M δ Bcut Bselect Cbase Cmesh qcap : ℝ},
    (∀ k, 0 < Kmesh k) → N=8*n →
    0 < d → 0 ≤ Wmax → Wmax ≤ 1/4 → 2*Usrc*Wmax ≤ csrc/64 →
    0 < T → 2 ≤ M → 0 < N → δ ≤ min κ 1 →
    1 ≤ R → R ≤ M → 0 < Jsep → Jsep ≤ M → (N:ℝ) ≤ M → Wmax*Jsep ≤ 1 →
    (∀ y∈Y, y∈Icc (1:ℝ) 2) →
    (∀ y∈Y, ∀ z∈Y, y≠z → 1 ≤ Jsep*|y-z|) →
    (∀ y∈Y, 0 ≤ rshift y ∧ 0 ≤ sshift y ∧
      rshift y*sshift y=d*y ∧ rshift y+sshift y ≤ Wmax) →
    (∀ w, 0 < w → ContDiffAt ℝ ∞ Fsrc w) →
    (∀ w∈Icc (1/2:ℝ) 3, csrc ≤ iteratedDeriv 5 Fsrc w) →
    (∀ w∈Icc (1/2:ℝ) 3, ∀ j, 1 ≤ j → j ≤ 7 → |iteratedDeriv j Fsrc w| ≤ Usrc) →
    (∀ w∈Icc (1/2:ℝ) 3,
      csrc ≤ |(iteratedDeriv 5 Fsrc w)^2-iteratedDeriv 4 Fsrc w*iteratedDeriv 6 Fsrc w|) →
    (∀ w∈Icc (1/2:ℝ) 3, iteratedDeriv 4 Fsrc w ≤ -csrc) →
    let Φ := fun y u =>
      (Fsrc u-Fsrc (u+rshift y)-Fsrc (u+sshift y)+Fsrc (u+rshift y+sshift y))/d
    (∀ y∈Y, Expdb.IsApproximateModelPhaseFunction (Φ y) σ 4 δ) →
    T*(N:ℝ)*R^2=M^3 →
    7*(N:ℝ)+2 ≤ M/4 →
    (3*Usrc)*(6*(N:ℝ)+1)^4 ≤ M*(N:ℝ)*R^2 →
    (3*Usrc/4)*(6*(N:ℝ)+1)^2 ≤ (N:ℝ)*R^2 →
    0 < Bcut → 2+168/κ ≤ Bselect → 7*Bcut ≤ κ*Bselect →
    (N:ℝ)^10 ≤ M^3*R^7 →
    ((N:ℝ)^2 ≤ M ∨ (1 ≤ M ∧ (N:ℝ) ≤ T ∧ R^2 ≤ T)) →
    let Q := fun k : ℕ => Qbase*2^k
    768 ≤ Qbase → (N:ℝ)*(Q kmax:ℝ) ≤ M →
    let Cphys := σ*(σ+1)+1
    let c := κ/6
    let J := Cphys/6
    let B := max 1 (max (2*Real.sqrt J) (8*J*Real.sqrt J/(3*c)))
    B*R^2/(N:ℝ)^2 ≤ 1/2 →
    (N:ℝ) ≤ R^2 → R ≤ (N:ℝ) → (N:ℝ)^3 ≤ M*R^2 →
    2 ≤ (N:ℝ) → csrc ≤ 4*κ/(Cphys+2) →
    let Uband := Usrc*T/M^2
    Uband ≤ 1 →
    let NarrowCap := (4/θ+3)*(8*Usrc/(csrc*θ)+3)
    let Cap := 3*NarrowCap
    let C₂ := modelPhaseJetCoefficient σ 2+δ
    let C₃ := modelPhaseJetCoefficient σ 3+δ
    let Ct := C₂/2+5*C₃/12
    let Cc := C₂/κ+C₃/(2*κ)
    let Ccurv := (4/κ)*(B+2*quarticReciprocalConstant σ δ)
    let Kres := 4*(37*B/2+16*B*Cc+2*Ct+2*Cc+
      2*quarticNonlinearResidualConstant σ δ)/κ
    let Esize := κ/(16*(Cphys+2))
    let Dbase := 37*B/2+16*B*Cc+2*Ct+2*Cc+2*quarticNonlinearResidualConstant σ δ
    let Tbase := (2/κ)*(B+2*quarticReciprocalConstant σ δ)
    2*3840*128^2*105*(Dbase+64*Tbase*Esize^2) ≤ Bselect*Esize →
    61*Ccurv*Cphys ≤ Bcut →
    let Lunit := 2*κ/Cphys
    let Gamma := Cphys/κ
    let Cthird := Gamma*(32*Kres+9*quarticReciprocalConstant σ δ)
    let Cpack := 64*Cphys*(Gamma^2*Cthird+Gamma*(modelPhaseJetCoefficient σ 3+δ)/κ)/κ
    let Cfirst := 128*Cphys*(Gamma^2*Cthird+Gamma*(modelPhaseJetCoefficient σ 3+δ)/κ)/κ^2
    let Cgap := 64*Cphys*(Gamma^2*B+Gamma*(modelPhaseJetCoefficient σ 3+δ)/κ)/κ
    let Cmain := 4*(2*Cfirst/Lunit^3)^((3:ℝ)⁻¹)+2
    let Ctail := 4*Cpack/Lunit^2+Cgap
    let Δ := fun k : ℕ => (37*B/2+16*B*Cc+2*Ct+2*Cc)*(Q k:ℝ)/(N:ℝ)
    let D := fun k : ℕ => Δ k+quarticNonlinearResidualConstant σ δ*(2*(Q k:ℝ))/(N:ℝ)
    let Buffer := fun k : ℕ => (56*(Usel k:ℝ)/κ)*(N:ℝ)+(N:ℝ)/(Cphys+2)+2
    (∀ k ≤ kmax,
      63*(Usrc/(2*(N:ℝ)*R^2))*(Q k:ℝ)*(N:ℝ)^2 ≤ Kmesh k ∧
      (Q k:ℝ)*(N:ℝ) ≤ (Kmesh k:ℝ)*R^2 ∧
      1 ≤ Usel k ∧ Bselect^2*(Usel k:ℝ)^3*R^2 ≤ (N:ℝ)^2 ∧
      R ≤ (Q k:ℝ) ∧
      (Usel k:ℝ) ≤ ((N:ℝ)/(Q k:ℝ))^((2:ℝ)/3)/Bselect ∧
      (Q k:ℝ) ≤ (N:ℝ) ∧ (Usel k:ℝ) ≤ R^2 ∧
      2*R^2 ≤ (Q k:ℝ)*(N:ℝ) ∧ D k ≤ 1/2 ∧ Δ k < 1/2) →
    (∀ k ≤ kmax, Usel k ≤ Usel 0) →
    2*Buffer 0+6*(N:ℝ) ≤ M →
    1 ≤ T → M ≤ T → 0 ≤ δ → 1 ≤ Cmesh →
    (Qbase:ℝ) ≤ Cbase*R → (kmax:ℝ) ≤ Real.log (N:ℝ)/Real.log 2 →
    0 < qcap → (qcap/2)*min (N:ℝ) (M/(N:ℝ)) ≤ (Q kmax:ℝ) →
    (∀ k ≤ kmax, (Kmesh k:ℝ) ≤ Cmesh*(Q k:ℝ)*(N:ℝ)/R^2 ∧
      ((N:ℝ)/(Q k:ℝ))^((2:ℝ)/3)/(2*Bselect) ≤ (Usel k:ℝ)) →
    let f := fun y w => T*Φ y (w/M)
    let CtailBand := 4*Usrc*(64/csrc)^2+192/csrc
    let ClowBand := (2*Usrc+csrc/32)*(3072/csrc)^2+3072/csrc
    let CerrorBand := (768:ℝ)^2*CtailBand+ClowBand
    let Carg := 512*768/csrc
    let Cdensity := 128*CerrorBand*(3+Real.log (Carg+1))
    let Ccard := 16*Cbase^2+8*Cdensity
    let Cdelta := (16*Usrc/csrc)*Real.sqrt ((Usrc/2)*Cmesh)
    let Ctri := 2+θ*(1+2*Usrc/csrc)
    let C₀ := 60*588*(2*Usrc/csrc)^2
    let MassPower := Ctri*Dtype*
      ((Y.card:ℝ)^11*M^10*(N:ℝ)^2/(Usrc*R^4)+
        (Y.card:ℝ)^11*M^11*(N:ℝ)^2/R^7+
        Cdelta*(Y.card:ℝ)^11*Jsep*M^10/(Usrc*R^2)+
        Cdelta*(Y.card:ℝ)^11*Jsep*M^11/R^5)+
      C₀*(Cmain+2*Bselect*Ctail)*((Y.card:ℝ)^12*M^10*R^2/(N:ℝ)^2)*
        (R/(N:ℝ))^((2:ℝ)/3)*Uband^((4:ℝ)/3)
    let ErrorPower := (Y.card:ℝ)*M/Real.sqrt (N:ℝ)+
      (Y.card:ℝ)*M*R^2/(N:ℝ)^2+(Y.card:ℝ)*(N:ℝ)^2*R^2/M+
      (Y.card:ℝ)*(N:ℝ)*((N:ℝ)/R)^((2:ℝ)/3)
    let Cpref := Cmesh^12*Cmesh^εloss*(2*Ccard)^10
    let Wconst := 144*Usrc/(csrc*κ)
    let CKlog := 3+Real.log (Cmesh+1)
    let Cerror := 8*(2*Real.sqrt 3*(1+Real.log 6)+72*Usrc/(csrc*κ))
    let Cfamily := CF^12*2^11*(C*Cap^11*Wconst^6*CKlog^12*Cpref+Cerror^12)
    let Cband := 2+1/Real.log 2
    let Cterminal := Cdensity/(2*qcap^2)
    let Cendpoint := 112/κ+2/(Cphys+2)+41/4
    let Ctotal := (2:ℝ)^11*
      (Cband^11*(Cterminal^12+(8:ℝ)^12*Cband*Cfamily)+Cendpoint^12)
    ∀ A Bint : ℝ → ℤ, (∀ y∈Y, ⌈M⌉ ≤ A y) →
    (∀ y∈Y, A y ≤ Bint y) → (∀ y∈Y, Bint y ≤ ⌊2*M⌋) →
      (∑ y∈Y, ‖∑ j∈Finset.Ioc (A y) (Bint y),(𝐞 (f y j):ℂ)‖)^12 ≤
        Ctotal*T^(2*εloss)*(1+Real.log T)^36*(MassPower+ErrorPower^12)
 := by
  classical
  intro κ L θ
  obtain ⟨CF,C,Dtype,hCF,hC,hDtype,hcore⟩ :=
    eventually_double_difference_all_band_subinterval_moment hcsrc hUsrc hσ hεloss
  refine ⟨CF,C,Dtype,hCF,hC,hDtype,?_⟩
  filter_upwards [hcore] with T hcoreT
  clear hcore
  intro Fsrc rshift sshift Y n N Qbase kmax Kmesh Usel R Jsep
    d Wmax M δ Bcut Bselect Cbase Cmesh qcap
    hK hNlink hd hw hwcap hsmallShift hT hMtwo hN hδ hR hRM hJsep hJM hNM hwJ
    hy hsepY hshifts hreg hlower hjets htests hnegative Φ hmodels
    hscale hfourBuffer hfourBudget hquadBudget hBcut hBselectSize hcutMargin hscaleTen hNsqM
    Q hQbase hQmax Cphys c J B hsmall hNR hRN hNcube hNtwo hanchorBudget
    Uband hUbandCap NarrowCap Cap C₂ C₃ Ct Cc Ccurv Kres Esize Dbase Tbase
    hsize hBsize Lunit Gamma Cthird Cpack Cfirst Cgap Cmain Ctail
    Δ D Buffer hvalid hUmax hroom
    hTone hMT hδ₀ hCm hbase hklog hqcap hQcap hmore
    f CtailBand ClowBand CerrorBand Carg Cdensity Ccard Cdelta Ctri C₀
    MassPower ErrorPower Cpref Wconst CKlog Cerror Cfamily Cband Cterminal Cendpoint Ctotal
    A Bint hA hab hB
  have hκ : 0 < κ := modelPhaseThirdLower_pos hσ
  have hθ : 0 < θ := by
    clear * - hUsrc hcsrc hκ
    dsimp only [θ,L]
    positivity
  have hCphys : 0 ≤ Cphys := by
    clear * - hσ
    dsimp only [Cphys]
    positivity
  have hCap : 0 ≤ Cap := by
    clear * - hθ hcsrc hUsrc
    dsimp only [Cap,NarrowCap]
    positivity
  have hBselect : 1 ≤ Bselect := by
    have hh : 0 < 168/κ := by positivity
    linarith only [hBselectSize,hh]
  obtain ⟨hmain,htail⟩ : 0 ≤ Cmain ∧ 0 ≤ Ctail :=
    model_source_large_entry_coefficients_nonneg hσ hδ₀
  obtain ⟨Chunks,band,hchunks,hbands,_htail,hgrids,hwhole⟩ :=
    hcoreT Fsrc rshift sshift Y n N Qbase kmax Kmesh Usel R Jsep
      (d:=d) (Wmax:=Wmax) (M:=M) (δ:=δ) (Bcut:=Bcut) (Bselect:=Bselect)
      hK hNlink hd hw hwcap hsmallShift hT hMtwo hN hδ hR hRM hJsep hJM hNM hwJ
      hy hsepY hshifts hreg hlower hjets htests hnegative hmodels
      hscale hfourBuffer hfourBudget hquadBudget hBcut hBselectSize hcutMargin
      hscaleTen hNsqM hQbase hQmax hsmall hNR hRN hNcube hNtwo hanchorBudget
      hUbandCap hsize hBsize hvalid hUmax hroom A Bint hA hab hB
  exact double_difference_finite_source_power_bound
    hcsrc hUsrc hκ hθ.le hCphys hεloss.le hC.le hDtype.le hmain htail hCap hBselect
    Chunks Y band n N Qbase kmax Kmesh Usel
    hK hNlink (by linarith only [hNtwo]) hR hJsep.le hNM
    hscale hNR hUbandCap hTone hMT (by omega) hCm hbase hklog hqcap hQcap
    (by
      intro k hk
      obtain ⟨_,hmesh,_,_,hRQ,hupper,hQN,_,_,_,_⟩ := hvalid k hk
      exact ⟨hRQ,hQN,hmesh,(hmore k hk).1,hupper,(hmore k hk).2⟩)
    hchunks hbands (fun k r => (hgrids k r).2) hwhole


example
    {csrc Usrc σ εloss : ℝ}
    (hcsrc : 0 < csrc) (hUsrc : 0 < Usrc)
    (hσ : 0 < σ) (hεloss : 0 < εloss) :
    let κ := modelPhaseThirdLower σ
    let L := max (32*Usrc^2/csrc^2)
      (64*(modelPhaseJetCoefficient σ 3+1)*Usrc/κ^2)
    let θ := 1/(8*(L+3))
    ∃ CF C Dtype : ℝ, 1 ≤ CF ∧ 0 < C ∧ 0 < Dtype ∧
    ∀ᶠ T : ℝ in Filter.atTop, ∀ (Fsrc rshift sshift : ℝ → ℝ) (Y : Finset ℝ)
    (n N Qbase kmax : ℕ) (Kmesh Usel : ℕ → ℕ) (R Jsep : ℝ)
    {d Wmax M δ Bcut Bselect Cbase Cmesh qcap : ℝ},
    (∀ k, 0 < Kmesh k) → N=8*n →
    0 < d → 0 ≤ Wmax → Wmax ≤ 1/4 → 2*Usrc*Wmax ≤ csrc/64 →
    0 < T → 2 ≤ M → 0 < N → δ ≤ min κ 1 →
    1 ≤ R → R ≤ M → 0 < Jsep → Jsep ≤ M → (N:ℝ) ≤ M → Wmax*Jsep ≤ 1 →
    (∀ y∈Y, y∈Icc (1:ℝ) 2) →
    (∀ y∈Y, ∀ z∈Y, y≠z → 1 ≤ Jsep*|y-z|) →
    (∀ y∈Y, 0 ≤ rshift y ∧ 0 ≤ sshift y ∧
      rshift y*sshift y=d*y ∧ rshift y+sshift y ≤ Wmax) →
    (∀ w, 0 < w → ContDiffAt ℝ ∞ Fsrc w) →
    (∀ w∈Icc (1/2:ℝ) 3, csrc ≤ iteratedDeriv 5 Fsrc w) →
    (∀ w∈Icc (1/2:ℝ) 3, ∀ j, 1 ≤ j → j ≤ 7 → |iteratedDeriv j Fsrc w| ≤ Usrc) →
    (∀ w∈Icc (1/2:ℝ) 3,
      csrc ≤ |(iteratedDeriv 5 Fsrc w)^2-iteratedDeriv 4 Fsrc w*iteratedDeriv 6 Fsrc w|) →
    (∀ w∈Icc (1/2:ℝ) 3, iteratedDeriv 4 Fsrc w ≤ -csrc) →
    let Φ := fun y u =>
      (Fsrc u-Fsrc (u+rshift y)-Fsrc (u+sshift y)+Fsrc (u+rshift y+sshift y))/d
    (∀ y∈Y, Expdb.IsApproximateModelPhaseFunction (Φ y) σ 4 δ) →
    T*(N:ℝ)*R^2=M^3 →
    7*(N:ℝ)+2 ≤ M/4 →
    (3*Usrc)*(6*(N:ℝ)+1)^4 ≤ M*(N:ℝ)*R^2 →
    (3*Usrc/4)*(6*(N:ℝ)+1)^2 ≤ (N:ℝ)*R^2 →
    0 < Bcut → 2+168/κ ≤ Bselect → 7*Bcut ≤ κ*Bselect →
    (N:ℝ)^10 ≤ M^3*R^7 →
    ((N:ℝ)^2 ≤ M ∨ (1 ≤ M ∧ (N:ℝ) ≤ T ∧ R^2 ≤ T)) →
    let Q := fun k : ℕ => Qbase*2^k
    768 ≤ Qbase → (N:ℝ)*(Q kmax:ℝ) ≤ M →
    let Cphys := σ*(σ+1)+1
    let c := κ/6
    let J := Cphys/6
    let B := max 1 (max (2*Real.sqrt J) (8*J*Real.sqrt J/(3*c)))
    B*R^2/(N:ℝ)^2 ≤ 1/2 →
    (N:ℝ) ≤ R^2 → R ≤ (N:ℝ) → (N:ℝ)^3 ≤ M*R^2 →
    2 ≤ (N:ℝ) → csrc ≤ 4*κ/(Cphys+2) →
    let Uband := Usrc*T/M^2
    Uband ≤ 1 →
    let NarrowCap := (4/θ+3)*(8*Usrc/(csrc*θ)+3)
    let Cap := 3*NarrowCap
    let C₂ := modelPhaseJetCoefficient σ 2+δ
    let C₃ := modelPhaseJetCoefficient σ 3+δ
    let Ct := C₂/2+5*C₃/12
    let Cc := C₂/κ+C₃/(2*κ)
    let Ccurv := (4/κ)*(B+2*quarticReciprocalConstant σ δ)
    let Kres := 4*(37*B/2+16*B*Cc+2*Ct+2*Cc+
      2*quarticNonlinearResidualConstant σ δ)/κ
    let Esize := κ/(16*(Cphys+2))
    let Dbase := 37*B/2+16*B*Cc+2*Ct+2*Cc+2*quarticNonlinearResidualConstant σ δ
    let Tbase := (2/κ)*(B+2*quarticReciprocalConstant σ δ)
    2*3840*128^2*105*(Dbase+64*Tbase*Esize^2) ≤ Bselect*Esize →
    61*Ccurv*Cphys ≤ Bcut →
    let Lunit := 2*κ/Cphys
    let Gamma := Cphys/κ
    let Cthird := Gamma*(32*Kres+9*quarticReciprocalConstant σ δ)
    let Cpack := 64*Cphys*(Gamma^2*Cthird+Gamma*(modelPhaseJetCoefficient σ 3+δ)/κ)/κ
    let Cfirst := 128*Cphys*(Gamma^2*Cthird+Gamma*(modelPhaseJetCoefficient σ 3+δ)/κ)/κ^2
    let Cgap := 64*Cphys*(Gamma^2*B+Gamma*(modelPhaseJetCoefficient σ 3+δ)/κ)/κ
    let Cmain := 4*(2*Cfirst/Lunit^3)^((3:ℝ)⁻¹)+2
    let Ctail := 4*Cpack/Lunit^2+Cgap
    let Δ := fun k : ℕ => (37*B/2+16*B*Cc+2*Ct+2*Cc)*(Q k:ℝ)/(N:ℝ)
    let D := fun k : ℕ => Δ k+quarticNonlinearResidualConstant σ δ*(2*(Q k:ℝ))/(N:ℝ)
    let Buffer := fun k : ℕ => (56*(Usel k:ℝ)/κ)*(N:ℝ)+(N:ℝ)/(Cphys+2)+2
    (∀ k ≤ kmax,
      63*(Usrc/(2*(N:ℝ)*R^2))*(Q k:ℝ)*(N:ℝ)^2 ≤ Kmesh k ∧
      (Q k:ℝ)*(N:ℝ) ≤ (Kmesh k:ℝ)*R^2 ∧
      1 ≤ Usel k ∧ Bselect^2*(Usel k:ℝ)^3*R^2 ≤ (N:ℝ)^2 ∧
      R ≤ (Q k:ℝ) ∧
      (Usel k:ℝ) ≤ ((N:ℝ)/(Q k:ℝ))^((2:ℝ)/3)/Bselect ∧
      (Q k:ℝ) ≤ (N:ℝ) ∧ (Usel k:ℝ) ≤ R^2 ∧
      2*R^2 ≤ (Q k:ℝ)*(N:ℝ) ∧ D k ≤ 1/2 ∧ Δ k < 1/2) →
    (∀ k ≤ kmax, Usel k ≤ Usel 0) →
    2*Buffer 0+6*(N:ℝ) ≤ M →
    1 ≤ T → M ≤ T → 0 ≤ δ → 1 ≤ Cmesh →
    (Qbase:ℝ) ≤ Cbase*R → (kmax:ℝ) ≤ Real.log (N:ℝ)/Real.log 2 →
    0 < qcap → (qcap/2)*min (N:ℝ) (M/(N:ℝ)) ≤ (Q kmax:ℝ) →
    (∀ k ≤ kmax, (Kmesh k:ℝ) ≤ Cmesh*(Q k:ℝ)*(N:ℝ)/R^2 ∧
      ((N:ℝ)/(Q k:ℝ))^((2:ℝ)/3)/(2*Bselect) ≤ (Usel k:ℝ)) →
    let f := fun y w => T*Φ y (w/M)
    let CtailBand := 4*Usrc*(64/csrc)^2+192/csrc
    let ClowBand := (2*Usrc+csrc/32)*(3072/csrc)^2+3072/csrc
    let CerrorBand := (768:ℝ)^2*CtailBand+ClowBand
    let Carg := 512*768/csrc
    let Cdensity := 128*CerrorBand*(3+Real.log (Carg+1))
    let Ccard := 16*Cbase^2+8*Cdensity
    let Cdelta := (16*Usrc/csrc)*Real.sqrt ((Usrc/2)*Cmesh)
    let Ctri := 2+θ*(1+2*Usrc/csrc)
    let C₀ := 60*588*(2*Usrc/csrc)^2
    let MassPower := Ctri*Dtype*
      ((Y.card:ℝ)^11*M^10*(N:ℝ)^2/(Usrc*R^4)+
        (Y.card:ℝ)^11*M^11*(N:ℝ)^2/R^7+
        Cdelta*(Y.card:ℝ)^11*Jsep*M^10/(Usrc*R^2)+
        Cdelta*(Y.card:ℝ)^11*Jsep*M^11/R^5)+
      C₀*(Cmain+2*Bselect*Ctail)*((Y.card:ℝ)^12*M^10*R^2/(N:ℝ)^2)*
        (R/(N:ℝ))^((2:ℝ)/3)*Uband^((4:ℝ)/3)
    let ErrorPower := (Y.card:ℝ)*M/Real.sqrt (N:ℝ)+
      (Y.card:ℝ)*M*R^2/(N:ℝ)^2+(Y.card:ℝ)*(N:ℝ)^2*R^2/M+
      (Y.card:ℝ)*(N:ℝ)*((N:ℝ)/R)^((2:ℝ)/3)
    let Cpref := Cmesh^12*Cmesh^εloss*(2*Ccard)^10
    let Wconst := 144*Usrc/(csrc*κ)
    let CKlog := 3+Real.log (Cmesh+1)
    let Cerror := 8*(2*Real.sqrt 3*(1+Real.log 6)+72*Usrc/(csrc*κ))
    let Cfamily := CF^12*2^11*(C*Cap^11*Wconst^6*CKlog^12*Cpref+Cerror^12)
    let Cband := 2+1/Real.log 2
    let Cterminal := Cdensity/(2*qcap^2)
    let Cendpoint := 112/κ+2/(Cphys+2)+41/4
    let Ctotal := (2:ℝ)^11*
      (Cband^11*(Cterminal^12+(8:ℝ)^12*Cband*Cfamily)+Cendpoint^12)
    ∀ A Bint : ℝ → ℤ, (∀ y∈Y, ⌈M⌉ ≤ A y) →
    (∀ y∈Y, A y ≤ Bint y) → (∀ y∈Y, Bint y ≤ ⌊2*M⌋) →
      (∑ y∈Y, ‖∑ j∈Finset.Ioc (A y) (Bint y),(𝐞 (f y j):ℂ)‖)^12 ≤
        Ctotal*T^(2*εloss)*(1+Real.log T)^36*(MassPower+ErrorPower^12)
 := by
  exact eventually_double_difference_all_source_physical_powers hcsrc hUsrc hσ hεloss

#print axioms eventually_double_difference_all_source_physical_powers

/-- Source buffer/jet budgets from N^3 relative to M*R^2 and N relative to M;
no N^2 <= M restriction is introduced. -/
private theorem exists_capped_source_physical_budget
    {Ccap A₄ A₂ B Cbuffer Clinear : ℝ}
    (hcap : 0 ≤ Ccap) (hA₄ : 0 ≤ A₄) (hA₂ : 0 ≤ A₂)
    (hB : 0 ≤ B) (hbuffer : 0 ≤ Cbuffer) (hlinear : 0 ≤ Clinear) :
    ∃ Cbudget : ℝ, 1 ≤ Cbudget ∧ Ccap ≤ Cbudget ∧
      ∀ (N R M U : ℝ), 1 ≤ N → 1 ≤ R →
      Cbudget*R ≤ N → Cbudget*N ≤ R^2 → Cbudget*N ≤ M →
      Cbudget*N^3 ≤ M*R^2 → Cbudget*N*R ≤ M →
      U ≤ (N/R)^((2:ℝ)/3) →
      0 < M ∧ R ≤ N ∧ N ≤ R^2 ∧ N ≤ M ∧ R ≤ M ∧
      N^3 ≤ M*R^2 ∧ Ccap*R ≤ N ∧ Ccap*N*R ≤ M ∧
      7*N+2 ≤ M/4 ∧
      A₄*(6*N+1)^4 ≤ M*N*R^2 ∧
      A₂*(6*N+1)^2 ≤ N*R^2 ∧
      B*R^2/N^2 ≤ 1/2 ∧
      2*(Cbuffer*U*N+Clinear*N+2)+6*N ≤ M
 := by
  let Cbudget := 37+Ccap+2401*A₄+49*A₂+2*B+2*Cbuffer+2*Clinear
  have hbounds : 1 ≤ Cbudget ∧ Ccap ≤ Cbudget ∧ 36 ≤ Cbudget ∧
      2401*A₄ ≤ Cbudget ∧ 49*A₂ ≤ Cbudget ∧ 2*B+1 ≤ Cbudget ∧
      2*Cbuffer+2*Clinear+10 ≤ Cbudget := by
    dsimp only [Cbudget]
    refine ⟨?_,?_,?_,?_,?_,?_,?_⟩ <;> linarith only [hcap,hA₄,hA₂,hB,hbuffer,hlinear]
  obtain ⟨hC,hCap,h36,h4,h2,hBsize,hroomSize⟩ := hbounds
  have hCp : 0 < Cbudget := zero_lt_one.trans_le hC
  refine ⟨Cbudget,hC,hCap,?_⟩
  intro N R M U hN hR hsep hrad hlength hcubic hcapRoom hU
  have hNp : 0 < N := zero_lt_one.trans_le hN
  have hRp : 0 < R := zero_lt_one.trans_le hR
  have hRN : R ≤ N := (le_mul_of_one_le_left hRp.le hC).trans hsep
  have hNR : N ≤ R^2 := (le_mul_of_one_le_left hNp.le hC).trans hrad
  have hNM : N ≤ M := (le_mul_of_one_le_left hNp.le hC).trans hlength
  have hMp : 0 < M := hNp.trans_le hNM
  have hNcube : N^3 ≤ M*R^2 :=
    (le_mul_of_one_le_left (by positivity) hC).trans hcubic
  have hN7 : 6*N+1 ≤ 7*N := by linarith only [hN]
  have hpad : 7*N+2 ≤ M/4 := by
    have hh := (mul_le_mul_of_nonneg_right h36 hNp.le).trans hlength
    linarith only [hh,hN]
  have hquartic : A₄*(6*N+1)^4 ≤ M*N*R^2 := by
    calc
      _ ≤ A₄*(7*N)^4 := mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (by positivity) hN7 4) hA₄
      _ = (2401*A₄)*N^4 := by ring
      _ ≤ Cbudget*N^4 := mul_le_mul_of_nonneg_right h4 (by positivity)
      _ = (Cbudget*N^3)*N := by ring
      _ ≤ (M*R^2)*N := mul_le_mul_of_nonneg_right hcubic hNp.le
      _ = _ := by ring
  have hquadratic : A₂*(6*N+1)^2 ≤ N*R^2 := by
    calc
      _ ≤ A₂*(7*N)^2 := mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (by positivity) hN7 2) hA₂
      _ = (49*A₂)*N^2 := by ring
      _ ≤ Cbudget*N^2 := mul_le_mul_of_nonneg_right h2 (by positivity)
      _ = N*(Cbudget*N) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hrad hNp.le
  have hsmall : B*R^2/N^2 ≤ 1/2 := by
    have hCsq : 2*B ≤ Cbudget^2 := by nlinarith only [hBsize,hC]
    have hh := pow_le_pow_left₀ (mul_pos hCp hRp).le hsep 2
    have hi := mul_le_mul_of_nonneg_right hCsq (sq_nonneg R)
    apply (div_le_iff₀ (sq_pos_of_pos hNp)).mpr
    nlinarith only [hh,hi]
  let X := N*(N/R)^((2:ℝ)/3)
  have hXnon : 0 ≤ X := by dsimp only [X]; positivity
  have hXcube : X^3=N^5/R^2 := by
    dsimp only [X]
    have hh : ((N/R)^((2:ℝ)/3))^3=(N/R)^2 := by
      rw [←Real.rpow_natCast,←Real.rpow_mul (div_pos hNp hRp).le]
      norm_num
    rw [mul_pow,hh]
    field_simp
  have hCcube : (Cbudget*X)^3 ≤ M^3 := by
    rw [mul_pow,hXcube]
    calc
      _ = (Cbudget*N^3)*((Cbudget*N)^2)/R^2 := by ring
      _ ≤ (M*R^2)*(M^2)/R^2 := by
        apply div_le_div_of_nonneg_right _ (sq_nonneg R)
        exact mul_le_mul hcubic (pow_le_pow_left₀ (mul_pos hCp hNp).le hlength 2)
          (by positivity) (by positivity)
      _ = M^3 := by field_simp
  have hCX : Cbudget*X ≤ M :=
    (pow_le_pow_iff_left₀ (mul_nonneg hCp.le hXnon) hMp.le (by norm_num : (3:ℕ) ≠ 0)).mp hCcube
  have hNX : N ≤ X := by
    have hh : 1 ≤ (N/R)^((2:ℝ)/3) := Real.one_le_rpow
      ((le_div_iff₀ hRp).mpr (by simpa only [one_mul] using hRN)) (by norm_num)
    exact le_mul_of_one_le_right hNp.le hh
  have hXone : 1 ≤ X := hN.trans hNX
  have hUN : U*N ≤ X := by
    simpa only [X,mul_comm] using mul_le_mul_of_nonneg_right hU hNp.le
  have hroom : 2*(Cbuffer*U*N+Clinear*N+2)+6*N ≤ M := by
    calc
      _ ≤ (2*Cbuffer+2*Clinear+10)*X := by
        nlinarith only [
          mul_le_mul_of_nonneg_left hUN hbuffer,
          mul_le_mul_of_nonneg_left hNX hlinear,hNX,hXone]
      _ ≤ Cbudget*X := mul_le_mul_of_nonneg_right hroomSize hXnon
      _ ≤ M := hCX
  exact ⟨hMp,hRN,hNR,hNM,hRN.trans hNM,hNcube,
    (mul_le_mul_of_nonneg_right hCap hRp.le).trans hsep,
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCap hNp.le) hRp.le).trans hcapRoom,
    hpad,hquartic,hquadratic,hsmall,hroom⟩


example
    {Ccap A₄ A₂ B Cbuffer Clinear : ℝ}
    (hcap : 0 ≤ Ccap) (hA₄ : 0 ≤ A₄) (hA₂ : 0 ≤ A₂)
    (hB : 0 ≤ B) (hbuffer : 0 ≤ Cbuffer) (hlinear : 0 ≤ Clinear) :
    ∃ Cbudget : ℝ, 1 ≤ Cbudget ∧ Ccap ≤ Cbudget ∧
      ∀ (N R M U : ℝ), 1 ≤ N → 1 ≤ R →
      Cbudget*R ≤ N → Cbudget*N ≤ R^2 → Cbudget*N ≤ M →
      Cbudget*N^3 ≤ M*R^2 → Cbudget*N*R ≤ M →
      U ≤ (N/R)^((2:ℝ)/3) →
      0 < M ∧ R ≤ N ∧ N ≤ R^2 ∧ N ≤ M ∧ R ≤ M ∧
      N^3 ≤ M*R^2 ∧ Ccap*R ≤ N ∧ Ccap*N*R ≤ M ∧
      7*N+2 ≤ M/4 ∧
      A₄*(6*N+1)^4 ≤ M*N*R^2 ∧
      A₂*(6*N+1)^2 ≤ N*R^2 ∧
      B*R^2/N^2 ≤ 1/2 ∧
      2*(Cbuffer*U*N+Clinear*N+2)+6*N ≤ M
 := by
  exact exists_capped_source_physical_budget hcap hA₄ hA₂ hB hbuffer hlinear

#print axioms exists_capped_source_physical_budget

/-- Actual capped mesh and reference choices consume the source physical budget.
The source coefficients may have either sign; their absolute-value majorant is
used only for finite cutoff selection. No N^2 <= M condition is assumed. -/
private theorem exists_capped_source_discrete_budget
    {Usrc κ Cphys B Bselect Dbase Δbase : ℝ}
    (hUsrc : 0 < Usrc) (hκ : 0 < κ) (hCphys : 0 ≤ Cphys)
    (hB : 0 ≤ B) (hBselect : 1 ≤ Bselect) :
    ∃ Cbudget qcap : ℝ, 1 ≤ Cbudget ∧ Usrc ≤ Cbudget ∧ 0 < qcap ∧
    ∀ (N : ℕ) (M R : ℝ), (1:ℝ) ≤ N → 1 ≤ R →
      Cbudget*R ≤ N → Cbudget*(N:ℝ) ≤ R^2 → Cbudget*(N:ℝ) ≤ M →
      Cbudget*(N:ℝ)^3 ≤ M*R^2 → Cbudget*(N:ℝ)*R ≤ M →
    ∃ (Qbase kmax : ℕ) (Kmesh Usel : ℕ → ℕ),
      let Q := fun k : ℕ => Qbase*2^k
      0 < M ∧ R ≤ (N:ℝ) ∧ (N:ℝ) ≤ R^2 ∧ (N:ℝ) ≤ M ∧ R ≤ M ∧
      (N:ℝ)^3 ≤ M*R^2 ∧
      7*(N:ℝ)+2 ≤ M/4 ∧
      (3*Usrc)*(6*(N:ℝ)+1)^4 ≤ M*(N:ℝ)*R^2 ∧
      (3*Usrc/4)*(6*(N:ℝ)+1)^2 ≤ (N:ℝ)*R^2 ∧
      B*R^2/(N:ℝ)^2 ≤ 1/2 ∧
      768 ≤ Qbase ∧ (Qbase:ℝ) ≤ 1536*R ∧
      (N:ℝ)*(Q kmax:ℝ) ≤ M ∧
      (qcap/2)*min (N:ℝ) (M/(N:ℝ)) ≤ (Q kmax:ℝ) ∧
      (kmax:ℝ) ≤ Real.log (N:ℝ)/Real.log 2 ∧
      (∀ k, 0 < Kmesh k) ∧
      (∀ k ≤ kmax,
        63*(Usrc/(2*(N:ℝ)*R^2))*(Q k:ℝ)*(N:ℝ)^2 ≤ Kmesh k ∧
        (Q k:ℝ)*(N:ℝ) ≤ (Kmesh k:ℝ)*R^2 ∧
        1 ≤ Usel k ∧ Bselect^2*(Usel k:ℝ)^3*R^2 ≤ (N:ℝ)^2 ∧
        R ≤ (Q k:ℝ) ∧
        (Usel k:ℝ) ≤ ((N:ℝ)/(Q k:ℝ))^((2:ℝ)/3)/Bselect ∧
        (Q k:ℝ) ≤ N ∧ (Usel k:ℝ) ≤ R^2 ∧
        2*R^2 ≤ (Q k:ℝ)*(N:ℝ) ∧
        Dbase*(Q k:ℝ)/(N:ℝ) ≤ 1/2 ∧ Δbase*(Q k:ℝ)/(N:ℝ) < 1/2) ∧
      (∀ k, Usel k ≤ Usel 0) ∧
      2*((56*(Usel 0:ℝ)/κ)*(N:ℝ)+(N:ℝ)/(Cphys+2)+2)+6*(N:ℝ) ≤ M ∧
      (∀ k ≤ kmax,
        (Kmesh k:ℝ) ≤ (2*max 1 (63*Usrc/2))*(Q k:ℝ)*(N:ℝ)/R^2 ∧
        ((N:ℝ)/(Q k:ℝ))^((2:ℝ)/3)/(2*Bselect) ≤ (Usel k:ℝ)) := by
  let Dcap := |Dbase|+|Δbase|+1
  have hDcap : 0 ≤ Dcap := by dsimp only [Dcap]; positivity
  have hDb : Dbase ≤ Dcap := by
    dsimp only [Dcap]
    linarith only [le_abs_self Dbase,abs_nonneg Δbase]
  have hΔb : Δbase ≤ Dcap := by
    dsimp only [Dcap]
    linarith only [le_abs_self Δbase,abs_nonneg Dbase]
  let H := (2*Bselect)^((3:ℝ)/2)
  have hH : 0 ≤ H := by dsimp only [H]; positivity
  let qcap := 1/(1+H+4*Dcap)
  have hden : 0 < 1+H+4*Dcap := by positivity
  have hq : 0 < qcap := by dsimp only [qcap]; positivity
  have hqone : qcap ≤ 1 := by
    dsimp only [qcap]
    apply (div_le_iff₀ hden).mpr
    linarith only [hH,hDcap]
  have hqH : qcap*(2*Bselect*1)^((3:ℝ)/2) ≤ 1 := by
    simp only [mul_one]
    change (1/(1+H+4*Dcap))*H ≤ 1
    rw [one_div_mul_eq_div]
    apply (div_le_iff₀ hden).mpr
    linarith only [hDcap]
  have hqD : 4*Dcap*qcap ≤ 1 := by
    change 4*Dcap*(1/(1+H+4*Dcap)) ≤ 1
    rw [mul_one_div]
    apply (div_le_iff₀ hden).mpr
    linarith only [hH]
  obtain ⟨C₀,hC₀,hCcap,hbudget⟩ := exists_capped_source_physical_budget
    (Ccap:=1536/qcap) (A₄:=3*Usrc) (A₂:=3*Usrc/4)
    (Cbuffer:=56/κ) (Clinear:=1/(Cphys+2))
    (by positivity) (by positivity) (by positivity) hB (by positivity) (by positivity)
  let Cbudget := max C₀ Usrc
  have hC : C₀ ≤ Cbudget := le_max_left _ _
  refine ⟨Cbudget,qcap,hC₀.trans hC,le_max_right _ _,hq,?_⟩
  intro N M R hN hR hsep hrad hlength hcubic hcapRoom
  have hNp : (0:ℝ) < N := zero_lt_one.trans_le hN
  have hRp : 0 < R := zero_lt_one.trans_le hR
  have hsep₀ : C₀*R ≤ N := (mul_le_mul_of_nonneg_right hC hRp.le).trans hsep
  have hrad₀ : C₀*(N:ℝ) ≤ R^2 := (mul_le_mul_of_nonneg_right hC hNp.le).trans hrad
  have hlength₀ : C₀*(N:ℝ) ≤ M := (mul_le_mul_of_nonneg_right hC hNp.le).trans hlength
  have hcubic₀ : C₀*(N:ℝ)^3 ≤ M*R^2 :=
    (mul_le_mul_of_nonneg_right hC (by positivity)).trans hcubic
  have hcap₀ : C₀*(N:ℝ)*R ≤ M :=
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hC hNp.le) hRp.le).trans hcapRoom
  obtain ⟨hM,hRN,hNR,hNM,hRM,hNcube,hcapN,hcapM,hpad,hquartic,hquadratic,hsmall,_⟩ :=
    hbudget (N:ℝ) R M 0 hN hR hsep₀ hrad₀ hlength₀ hcubic₀ hcap₀ (by positivity)
  have hroom : 2*768*R ≤ qcap*min (N:ℝ) (M/(N:ℝ)) := by
    rw [mul_min_of_nonneg _ _ hq.le]
    apply le_min
    · have hh := mul_le_mul_of_nonneg_left hcapN hq.le
      calc
        _ = qcap*((1536/qcap)*R) := by field_simp; norm_num
        _ ≤ _ := hh
    · rw [←mul_div_assoc]
      apply (le_div_iff₀ hNp).mpr
      have hh := mul_le_mul_of_nonneg_left hcapM hq.le
      calc
        (2*768*R)*(N:ℝ) = qcap*((1536/qcap)*(N:ℝ)*R) := by field_simp; ring
        _ ≤ _ := hh
  obtain ⟨Qbase,kmax,Kmesh,Usel,hBaseLo,hBaseHi,hEndLo,_hEndHi,hNQ,_hError,
    hkmax,hK,hvalid,hmono⟩ :=
    capped_dyadic_band_integer_physical_selection N (σ:=1) (J:=Usrc) (L:=1)
      (Cbase:=768) (Dcap:=Dcap) (by norm_num) hM hR hRN hNR hBselect (by norm_num)
      (by norm_num) hq hqone hqH hDcap hqD hroom
  let Q := fun k : ℕ => Qbase*2^k
  have hUzero : (Usel 0:ℝ) ≤ ((N:ℝ)/R)^((2:ℝ)/3) := by
    obtain ⟨_,_,_,_,_,_,hupper,_,_,_,hstrong,_,_⟩ := hvalid 0 (Nat.zero_le _)
    have hRQ : R ≤ (Q 0:ℝ) := by linarith only [hstrong,hRp]
    calc
      _ ≤ ((N:ℝ)/(Q 0:ℝ))^((2:ℝ)/3)/Bselect := hupper
      _ ≤ ((N:ℝ)/(Q 0:ℝ))^((2:ℝ)/3) := div_le_self (by positivity) hBselect
      _ ≤ _ := Real.rpow_le_rpow (by positivity)
        (div_le_div_of_nonneg_left hNp.le hRp hRQ) (by norm_num)
  have hbuffer := (hbudget (N:ℝ) R M (Usel 0:ℝ) hN hR
    hsep₀ hrad₀ hlength₀ hcubic₀ hcap₀ hUzero).2.2.2.2.2.2.2.2.2.2.2.2
  have hbase : 768 ≤ Qbase := by
    have hh : (768:ℝ) ≤ Qbase :=
      (le_mul_of_one_le_right (by norm_num) hR).trans hBaseLo
    exact_mod_cast hh
  refine ⟨Qbase,kmax,Kmesh,Usel,hM,hRN,hNR,hNM,hRM,hNcube,hpad,hquartic,
    hquadratic,hsmall,hbase,?_,hNQ,?_,hkmax,hK,?_,hmono,?_,?_⟩
  · simpa only [show (2:ℝ)*768=1536 by norm_num] using hBaseHi
  · simpa only [div_mul_eq_mul_div] using hEndLo
  · intro k hk
    obtain ⟨_,hsource,hmesh,_,hU,hwrap,hupper,_,hQN,hUR,hstrong,hmin,hD⟩ := hvalid k hk
    have hD' : Dbase*(Q k:ℝ)/(N:ℝ) ≤ 1/4 :=
      (div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right hDb (Nat.cast_nonneg _)) hNp.le).trans hD
    have hΔ' : Δbase*(Q k:ℝ)/(N:ℝ) ≤ 1/4 :=
      (div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right hΔb (Nat.cast_nonneg _)) hNp.le).trans hD
    refine ⟨?_,hmesh,hU,hwrap,?_,hupper,?_,hUR,hmin,?_,?_⟩
    · simpa only [mul_one] using hsource
    · linarith only [hstrong,hRp]
    · exact_mod_cast hQN
    · exact hD'.trans (by norm_num)
    · exact hΔ'.trans_lt (by norm_num)
  · convert hbuffer using 1
    ring
  · intro k hk
    obtain ⟨_,_,_,hupper,_,_,_,hlower,_⟩ := hvalid k hk
    exact ⟨by simpa only [mul_one] using hupper,hlower⟩


example
    {Usrc κ Cphys B Bselect Dbase Δbase : ℝ}
    (hUsrc : 0 < Usrc) (hκ : 0 < κ) (hCphys : 0 ≤ Cphys)
    (hB : 0 ≤ B) (hBselect : 1 ≤ Bselect) :
    ∃ Cbudget qcap : ℝ, 1 ≤ Cbudget ∧ Usrc ≤ Cbudget ∧ 0 < qcap ∧
    ∀ (N : ℕ) (M R : ℝ), (1:ℝ) ≤ N → 1 ≤ R →
      Cbudget*R ≤ N → Cbudget*(N:ℝ) ≤ R^2 → Cbudget*(N:ℝ) ≤ M →
      Cbudget*(N:ℝ)^3 ≤ M*R^2 → Cbudget*(N:ℝ)*R ≤ M →
    ∃ (Qbase kmax : ℕ) (Kmesh Usel : ℕ → ℕ),
      let Q := fun k : ℕ => Qbase*2^k
      0 < M ∧ R ≤ (N:ℝ) ∧ (N:ℝ) ≤ R^2 ∧ (N:ℝ) ≤ M ∧ R ≤ M ∧
      (N:ℝ)^3 ≤ M*R^2 ∧
      7*(N:ℝ)+2 ≤ M/4 ∧
      (3*Usrc)*(6*(N:ℝ)+1)^4 ≤ M*(N:ℝ)*R^2 ∧
      (3*Usrc/4)*(6*(N:ℝ)+1)^2 ≤ (N:ℝ)*R^2 ∧
      B*R^2/(N:ℝ)^2 ≤ 1/2 ∧
      768 ≤ Qbase ∧ (Qbase:ℝ) ≤ 1536*R ∧
      (N:ℝ)*(Q kmax:ℝ) ≤ M ∧
      (qcap/2)*min (N:ℝ) (M/(N:ℝ)) ≤ (Q kmax:ℝ) ∧
      (kmax:ℝ) ≤ Real.log (N:ℝ)/Real.log 2 ∧
      (∀ k, 0 < Kmesh k) ∧
      (∀ k ≤ kmax,
        63*(Usrc/(2*(N:ℝ)*R^2))*(Q k:ℝ)*(N:ℝ)^2 ≤ Kmesh k ∧
        (Q k:ℝ)*(N:ℝ) ≤ (Kmesh k:ℝ)*R^2 ∧
        1 ≤ Usel k ∧ Bselect^2*(Usel k:ℝ)^3*R^2 ≤ (N:ℝ)^2 ∧
        R ≤ (Q k:ℝ) ∧
        (Usel k:ℝ) ≤ ((N:ℝ)/(Q k:ℝ))^((2:ℝ)/3)/Bselect ∧
        (Q k:ℝ) ≤ N ∧ (Usel k:ℝ) ≤ R^2 ∧
        2*R^2 ≤ (Q k:ℝ)*(N:ℝ) ∧
        Dbase*(Q k:ℝ)/(N:ℝ) ≤ 1/2 ∧ Δbase*(Q k:ℝ)/(N:ℝ) < 1/2) ∧
      (∀ k, Usel k ≤ Usel 0) ∧
      2*((56*(Usel 0:ℝ)/κ)*(N:ℝ)+(N:ℝ)/(Cphys+2)+2)+6*(N:ℝ) ≤ M ∧
      (∀ k ≤ kmax,
        (Kmesh k:ℝ) ≤ (2*max 1 (63*Usrc/2))*(Q k:ℝ)*(N:ℝ)/R^2 ∧
        ((N:ℝ)/(Q k:ℝ))^((2:ℝ)/3)/(2*Bselect) ≤ (Usel k:ℝ)) := by
  exact exists_capped_source_discrete_budget hUsrc hκ hCphys hB hBselect

#print axioms exists_capped_source_discrete_budget

/-- Unchanged existing private source-constant/absorption proof; promotion reuses the original. -/
private theorem exists_source_cutoff_margins
    {κ Ccurv Cphys Sector Esize : ℝ}
    (hκ : 0 < κ) (hCcurv : 0 ≤ Ccurv) (hCphys : 0 ≤ Cphys)
    (hEsize : 0 < Esize) :
    ∃ Bcut Bselect : ℝ, 0 < Bcut ∧ 1 ≤ Bselect ∧
      2+168/κ ≤ Bselect ∧ 7*Bcut ≤ κ*Bselect ∧
      Sector ≤ Bselect*Esize ∧ 61*Ccurv*Cphys ≤ Bcut := by
  let Bcut := 1+61*Ccurv*Cphys
  let Bselect := max 1 (max (2+168/κ) (max (7*Bcut/κ) (Sector/Esize)))
  have hBcut : 0 < Bcut := by dsimp only [Bcut]; positivity
  have hBs : 1 ≤ Bselect := le_max_left _ _
  have hSize : 2+168/κ ≤ Bselect := (le_max_left _ _).trans (le_max_right _ _)
  have hCut : 7*Bcut/κ ≤ Bselect :=
    (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have hSec : Sector/Esize ≤ Bselect :=
    (le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  refine ⟨Bcut,Bselect,hBcut,hBs,hSize,?_,(div_le_iff₀ hEsize).mp hSec,?_⟩
  · calc
      7*Bcut ≤ Bselect*κ := (div_le_iff₀ hκ).mp hCut
      _ = κ*Bselect := mul_comm _ _
  · dsimp only [Bcut]
    linarith

example
    {κ Ccurv Cphys Sector Esize : ℝ}
    (hκ : 0 < κ) (hCcurv : 0 ≤ Ccurv) (hCphys : 0 ≤ Cphys)
    (hEsize : 0 < Esize) :
    ∃ Bcut Bselect : ℝ, 0 < Bcut ∧ 1 ≤ Bselect ∧
      2+168/κ ≤ Bselect ∧ 7*Bcut ≤ κ*Bselect ∧
      Sector ≤ Bselect*Esize ∧ 61*Ccurv*Cphys ≤ Bcut := by
  exact exists_source_cutoff_margins hκ hCcurv hCphys hEsize

#print axioms exists_source_cutoff_margins

/-- Unchanged existing private source-constant/absorption proof; promotion reuses the original. -/
private theorem eventually_selected_band_logarithmic_absorption
    {C ε : ℝ} (hC : 0 ≤ C) (hε : 0 < ε) :
    ∀ᶠ T : ℝ in Filter.atTop, 0 < T ∧ 1 ≤ Real.log T ∧
      C*T^(ε/2)*(1+Real.log T)^36 ≤ T^ε := by
  filter_upwards [
    TaoTrudgianYang2025.eventually_const_log_pow_le_rpow (C*2^36) (by positivity) 36
      (show 0 < ε/2 by linarith only [hε]),
    Real.tendsto_log_atTop.eventually_ge_atTop 1,
    Filter.eventually_ge_atTop (1:ℝ)] with T hsmall hlog hT
  have hTp : 0 < T := zero_lt_one.trans_le hT
  have hpoly : C*(1+Real.log T)^36 ≤ T^(ε/2) := by
    calc
      _ ≤ C*(2*Real.log T)^36 := by gcongr; linarith only [hlog]
      _ = (C*2^36)*(Real.log T)^36 := by rw [mul_pow]; ring
      _ ≤ _ := hsmall
  refine ⟨hTp,hlog,?_⟩
  calc
    _ = (C*(1+Real.log T)^36)*T^(ε/2) := by ring
    _ ≤ T^(ε/2)*T^(ε/2) := mul_le_mul_of_nonneg_right hpoly (by positivity)
    _ = _ := by rw [←Real.rpow_add hTp]; congr 1; ring

example
    {C ε : ℝ} (hC : 0 ≤ C) (hε : 0 < ε) :
    ∀ᶠ T : ℝ in Filter.atTop, 0 < T ∧ 1 ≤ Real.log T ∧
      C*T^(ε/2)*(1+Real.log T)^36 ≤ T^ε := by
  exact eventually_selected_band_logarithmic_absorption hC hε

#print axioms eventually_selected_band_logarithmic_absorption
/-- The fixed five source weights and logarithms are absorbed numerically.
The analytic consumer below supplies the actual unsimplified moment. -/
private theorem double_difference_five_monomial_absorption
    {Usrc Ctri Dtype Cdelta C₀ Cmain Bselect Ctail Ctotal ε Y M N R Jsep T X : ℝ}
    (hUsrc : 0 < Usrc) (hY : 0 ≤ Y) (hM : 0 < M) (hNp : 0 < N) (hRp : 0 < R)
    (hJsep : 0 ≤ Jsep) (hT : 0 < T) (hTotal : 0 ≤ Ctotal) :
    let a₁ := Ctri*Dtype/Usrc
    let a₂ := Ctri*Dtype
    let a₃ := Ctri*Dtype*Cdelta/Usrc
    let a₄ := Ctri*Dtype*Cdelta
    let a₅ := C₀*(Cmain+2*Bselect*Ctail)*Usrc^((4:ℝ)/3)
    let Cmass := 1+|a₁|+|a₂|+|a₃|+|a₄|+|a₅|
    |Ctotal| *Cmass*T^(ε/2)*(1+Real.log T)^36 ≤ T^ε →
    let ErrorTotal := Y*M/Real.sqrt N+Y*M*R^2/N^2+
      Y*N^2*R^2/M+Y*N*(N/R)^((2:ℝ)/3)
    let Main := Y^11*M^10*N^2/R^4+Y^11*M^11*N^2/R^7+
      Y^11*Jsep*M^10/R^2+Y^11*Jsep*M^11/R^5+
      Y^12*M^10*R^2/N^2*(R/N)^((2:ℝ)/3)*(T/M^2)^((4:ℝ)/3)
    let MassPower := Ctri*Dtype*
      (Y^11*M^10*N^2/(Usrc*R^4)+Y^11*M^11*N^2/R^7+
        Cdelta*Y^11*Jsep*M^10/(Usrc*R^2)+Cdelta*Y^11*Jsep*M^11/R^5)+
      C₀*(Cmain+2*Bselect*Ctail)*(Y^12*M^10*R^2/N^2)*
        (R/N)^((2:ℝ)/3)*(Usrc*T/M^2)^((4:ℝ)/3)
    X ≤ Ctotal*T^(ε/2)*(1+Real.log T)^36*(MassPower+ErrorTotal^12) →
    X ≤ T^ε*(Main+ErrorTotal^12) := by
  intro a₁ a₂ a₃ a₄ a₅ Cmass habsorb ErrorTotal Main MassPower
  have hCmass : 1 ≤ Cmass := by
    dsimp only [Cmass]
    linarith only [abs_nonneg a₁,abs_nonneg a₂,abs_nonneg a₃,abs_nonneg a₄,abs_nonneg a₅]
  let P₁ := Y^11*M^10*N^2/R^4
  let P₂ := Y^11*M^11*N^2/R^7
  let P₃ := Y^11*Jsep*M^10/R^2
  let P₄ := Y^11*Jsep*M^11/R^5
  let P₅ := Y^12*M^10*R^2/N^2*
    (R/N)^((2:ℝ)/3)*(T/M^2)^((4:ℝ)/3)
  have hP₁ : 0 ≤ P₁ := by clear * - hY hM hNp hRp; dsimp only [P₁]; positivity
  have hP₂ : 0 ≤ P₂ := by clear * - hY hM hNp hRp; dsimp only [P₂]; positivity
  have hP₃ : 0 ≤ P₃ := by clear * - hY hM hNp hRp hJsep; dsimp only [P₃]; positivity
  have hP₄ : 0 ≤ P₄ := by clear * - hY hM hNp hRp hJsep; dsimp only [P₄]; positivity
  have hP₅ : 0 ≤ P₅ := by clear * - hY hM hNp hRp hT; dsimp only [P₅]; positivity
  have hMain : 0 ≤ Main := by change 0 ≤ P₁+P₂+P₃+P₄+P₅; positivity
  have hMassEq : MassPower=a₁*P₁+a₂*P₂+a₃*P₃+a₄*P₄+a₅*P₅ := by
    have hp : (Usrc*T/M^2)^((4:ℝ)/3)=
        Usrc^((4:ℝ)/3)*(T/M^2)^((4:ℝ)/3) := by
      rw [mul_div_assoc,Real.mul_rpow hUsrc.le (by positivity)]
    dsimp only [MassPower,P₁,P₂,P₃,P₄,P₅,a₁,a₂,a₃,a₄,a₅]
    rw [hp]
    ring
  have hweighted (a b c d e x y z u v : ℝ)
      (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) (hu : 0 ≤ u) (hv : 0 ≤ v) :
      a*x+b*y+c*z+d*u+e*v ≤
        (1+|a|+|b|+|c|+|d|+|e|)*(x+y+z+u+v) := by
    clear * - hx hy hz hu hv
    have ha := mul_le_mul (le_abs_self a)
      (show x ≤ x+y+z+u+v by linarith only [hy,hz,hu,hv]) hx (abs_nonneg a)
    have hb := mul_le_mul (le_abs_self b)
      (show y ≤ x+y+z+u+v by linarith only [hx,hz,hu,hv]) hy (abs_nonneg b)
    have hc := mul_le_mul (le_abs_self c)
      (show z ≤ x+y+z+u+v by linarith only [hx,hy,hu,hv]) hz (abs_nonneg c)
    have hd := mul_le_mul (le_abs_self d)
      (show u ≤ x+y+z+u+v by linarith only [hx,hy,hz,hv]) hu (abs_nonneg d)
    have he := mul_le_mul (le_abs_self e)
      (show v ≤ x+y+z+u+v by linarith only [hx,hy,hz,hu]) hv (abs_nonneg e)
    nlinarith only [ha,hb,hc,hd,he,hx,hy,hz,hu,hv]
  have hMass : MassPower ≤ Cmass*Main := by
    rw [hMassEq]
    exact hweighted a₁ a₂ a₃ a₄ a₅ P₁ P₂ P₃ P₄ P₅ hP₁ hP₂ hP₃ hP₄ hP₅
  have hEM : 0 ≤ Main+ErrorTotal^12 := add_nonneg hMain (by positivity)
  have hMassTotal : MassPower+ErrorTotal^12 ≤ Cmass*(Main+ErrorTotal^12) := by
    calc
      _ ≤ Cmass*Main+Cmass*ErrorTotal^12 :=
        add_le_add hMass (le_mul_of_one_le_left (by positivity) hCmass)
      _ = _ := (mul_add _ _ _).symm

  intro hraw
  calc
    _ ≤ Ctotal*T^(ε/2)*(1+Real.log T)^36*(MassPower+ErrorTotal^12) := hraw
    _ ≤ Ctotal*T^(ε/2)*(1+Real.log T)^36*(Cmass*(Main+ErrorTotal^12)) :=
      mul_le_mul_of_nonneg_left hMassTotal (by positivity)
    _ ≤ |Ctotal| *T^(ε/2)*(1+Real.log T)^36*(Cmass*(Main+ErrorTotal^12)) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (le_abs_self Ctotal) (by positivity)) (by positivity))
        (mul_nonneg (zero_le_one.trans hCmass) hEM)
    _ = (|Ctotal| *Cmass*T^(ε/2)*(1+Real.log T)^36)*(Main+ErrorTotal^12) := by ac_rfl
    _ ≤ _ := mul_le_mul_of_nonneg_right habsorb hEM


example
    {Usrc Ctri Dtype Cdelta C₀ Cmain Bselect Ctail Ctotal ε Y M N R Jsep T X : ℝ}
    (hUsrc : 0 < Usrc) (hY : 0 ≤ Y) (hM : 0 < M) (hNp : 0 < N) (hRp : 0 < R)
    (hJsep : 0 ≤ Jsep) (hT : 0 < T) (hTotal : 0 ≤ Ctotal) :
    let a₁ := Ctri*Dtype/Usrc
    let a₂ := Ctri*Dtype
    let a₃ := Ctri*Dtype*Cdelta/Usrc
    let a₄ := Ctri*Dtype*Cdelta
    let a₅ := C₀*(Cmain+2*Bselect*Ctail)*Usrc^((4:ℝ)/3)
    let Cmass := 1+|a₁|+|a₂|+|a₃|+|a₄|+|a₅|
    |Ctotal| *Cmass*T^(ε/2)*(1+Real.log T)^36 ≤ T^ε →
    let ErrorTotal := Y*M/Real.sqrt N+Y*M*R^2/N^2+
      Y*N^2*R^2/M+Y*N*(N/R)^((2:ℝ)/3)
    let Main := Y^11*M^10*N^2/R^4+Y^11*M^11*N^2/R^7+
      Y^11*Jsep*M^10/R^2+Y^11*Jsep*M^11/R^5+
      Y^12*M^10*R^2/N^2*(R/N)^((2:ℝ)/3)*(T/M^2)^((4:ℝ)/3)
    let MassPower := Ctri*Dtype*
      (Y^11*M^10*N^2/(Usrc*R^4)+Y^11*M^11*N^2/R^7+
        Cdelta*Y^11*Jsep*M^10/(Usrc*R^2)+Cdelta*Y^11*Jsep*M^11/R^5)+
      C₀*(Cmain+2*Bselect*Ctail)*(Y^12*M^10*R^2/N^2)*
        (R/N)^((2:ℝ)/3)*(Usrc*T/M^2)^((4:ℝ)/3)
    X ≤ Ctotal*T^(ε/2)*(1+Real.log T)^36*(MassPower+ErrorTotal^12) →
    X ≤ T^ε*(Main+ErrorTotal^12) := by
  exact double_difference_five_monomial_absorption hUsrc hY hM hNp hRp hJsep hT hTotal

#print axioms double_difference_five_monomial_absorption

/-- Source-uniform capped double-difference estimate. The discrete band,
mesh and reference scales are constructed from physical room, and all fixed
constants and logarithms are absorbed. Both capped terminal errors are retained. -/
private theorem eventually_double_difference_uniform_capped_source_bound
    {csrc Usrc σ δ ε : ℝ}
    (hcsrc : 0 < csrc) (hUsrc : 0 < Usrc) (hσ : 0 < σ)
    (hδzero : 0 ≤ δ) (hδ : δ ≤ min (modelPhaseThirdLower σ) 1)
    (hε : 0 < ε)
    (hanchor : csrc ≤ 4*modelPhaseThirdLower σ/(σ*(σ+1)+3)) :
    ∃ Cbudget w₀ : ℝ, 1 ≤ Cbudget ∧ 0 < w₀ ∧ w₀ ≤ 1/4 ∧
    ∀ᶠ T : ℝ in Filter.atTop, ∀ (Fsrc rshift sshift : ℝ → ℝ) (Y : Finset ℝ)
      (n N : ℕ) (R Jsep : ℝ) {d Wmax M : ℝ},
      N=8*n → 2 ≤ N → 1 ≤ R → 0 < d → 0 ≤ Wmax → Wmax ≤ w₀ →
      0 < Jsep → Jsep ≤ M → Wmax*Jsep ≤ 1 →
      (∀ y∈Y, y∈Icc (1:ℝ) 2) →
      (∀ y∈Y, ∀ z∈Y, y≠z → 1 ≤ Jsep*|y-z|) →
      (∀ y∈Y, 0 ≤ rshift y ∧ 0 ≤ sshift y ∧
        rshift y*sshift y=d*y ∧ rshift y+sshift y ≤ Wmax) →
      (∀ w, 0 < w → ContDiffAt ℝ ∞ Fsrc w) →
      (∀ w∈Icc (1/2:ℝ) 3, csrc ≤ iteratedDeriv 5 Fsrc w) →
      (∀ w∈Icc (1/2:ℝ) 3, ∀ j, 1 ≤ j → j ≤ 7 → |iteratedDeriv j Fsrc w| ≤ Usrc) →
      (∀ w∈Icc (1/2:ℝ) 3,
        csrc ≤ |(iteratedDeriv 5 Fsrc w)^2-iteratedDeriv 4 Fsrc w*iteratedDeriv 6 Fsrc w|) →
      (∀ w∈Icc (1/2:ℝ) 3, iteratedDeriv 4 Fsrc w ≤ -csrc) →
      let Φ := fun y u =>
        (Fsrc u-Fsrc (u+rshift y)-Fsrc (u+sshift y)+Fsrc (u+rshift y+sshift y))/d
      (∀ y∈Y, Expdb.IsApproximateModelPhaseFunction (Φ y) σ 4 δ) →
      T*(N:ℝ)*R^2=M^3 →
      Cbudget*R ≤ N → Cbudget*(N:ℝ) ≤ R^2 → Cbudget*(N:ℝ) ≤ M →
      Cbudget*(N:ℝ)^3 ≤ M*R^2 → Cbudget*(N:ℝ)*R ≤ M →
      Cbudget*M ≤ (N:ℝ)*R^2 → M ≤ T → R^2 ≤ T →
      (N:ℝ)^10 ≤ M^3*R^7 →
      ∀ A Bint : ℝ → ℤ, (∀ y∈Y, ⌈M⌉ ≤ A y) →
      (∀ y∈Y, A y ≤ Bint y) → (∀ y∈Y, Bint y ≤ ⌊2*M⌋) →
      let Yc := (Y.card:ℝ)
      let ErrorTotal := Yc*M/Real.sqrt (N:ℝ)+Yc*M*R^2/(N:ℝ)^2+
        Yc*(N:ℝ)^2*R^2/M+Yc*(N:ℝ)*((N:ℝ)/R)^((2:ℝ)/3)
      let Main := Yc^11*M^10*(N:ℝ)^2/R^4+Yc^11*M^11*(N:ℝ)^2/R^7+
        Yc^11*Jsep*M^10/R^2+Yc^11*Jsep*M^11/R^5+
        Yc^12*M^10*R^2/(N:ℝ)^2*(R/(N:ℝ))^((2:ℝ)/3)*(T/M^2)^((4:ℝ)/3)
      (∑ y∈Y, ‖∑ j∈Finset.Ioc (A y) (Bint y),(𝐞 (T*Φ y ((j:ℝ)/M)):ℂ)‖)^12 ≤
        T^ε*(Main+ErrorTotal^12) := by
  classical
  let εloss := ε/4
  have hεloss : 0 < εloss := by dsimp only [εloss]; linarith only [hε]
  let κ := modelPhaseThirdLower σ
  let L := max (32*Usrc^2/csrc^2)
    (64*(modelPhaseJetCoefficient σ 3+1)*Usrc/κ^2)
  let θ := 1/(8*(L+3))
  have hκ : 0 < κ := modelPhaseThirdLower_pos hσ
  obtain ⟨CF,C,Dtype,_hCF,hC,_hDtype,hfinite⟩ :=
    eventually_double_difference_all_source_physical_powers hcsrc hUsrc hσ hεloss
  let Cphys := σ*(σ+1)+1
  let c := κ/6
  let J := Cphys/6
  let B := max 1 (max (2*Real.sqrt J) (8*J*Real.sqrt J/(3*c)))
  let NarrowCap := (4/θ+3)*(8*Usrc/(csrc*θ)+3)
  let Cap := 3*NarrowCap
  let C₂ := modelPhaseJetCoefficient σ 2+δ
  let C₃ := modelPhaseJetCoefficient σ 3+δ
  let Ct := C₂/2+5*C₃/12
  let Cc := C₂/κ+C₃/(2*κ)
  let Ccurv := (4/κ)*(B+2*quarticReciprocalConstant σ δ)
  let Kres := 4*(37*B/2+16*B*Cc+2*Ct+2*Cc+
    2*quarticNonlinearResidualConstant σ δ)/κ
  let Esize := κ/(16*(Cphys+2))
  let Dbase := 37*B/2+16*B*Cc+2*Ct+2*Cc+2*quarticNonlinearResidualConstant σ δ
  let Tbase := (2/κ)*(B+2*quarticReciprocalConstant σ δ)
  let Lunit := 2*κ/Cphys
  let Gamma := Cphys/κ
  let Cthird := Gamma*(32*Kres+9*quarticReciprocalConstant σ δ)
  let Cpack := 64*Cphys*(Gamma^2*Cthird+Gamma*(modelPhaseJetCoefficient σ 3+δ)/κ)/κ
  let Cfirst := 128*Cphys*(Gamma^2*Cthird+Gamma*(modelPhaseJetCoefficient σ 3+δ)/κ)/κ^2
  let Cgap := 64*Cphys*(Gamma^2*B+Gamma*(modelPhaseJetCoefficient σ 3+δ)/κ)/κ
  let Cmain := 4*(2*Cfirst/Lunit^3)^((3:ℝ)⁻¹)+2
  let Ctail := 4*Cpack/Lunit^2+Cgap
  have hCphys : 0 ≤ Cphys := by clear * - hσ; dsimp only [Cphys]; positivity
  have hB : 0 ≤ B := zero_le_one.trans (le_max_left _ _)
  have hEsize : 0 < Esize := by clear * - hκ hCphys; dsimp only [Esize]; positivity
  let Δbase := 37*B/2+16*B*Cc+2*Ct+2*Cc
  let Sector := 2*3840*128^2*105*(Dbase+64*Tbase*Esize^2)
  obtain ⟨Bcut,Bselect,hBcut,hBs,hBsSize,hcutMargin,hsize,hcurvAbs⟩ :=
    exists_source_cutoff_margins (Sector:=Sector) hκ (abs_nonneg Ccurv) hCphys hEsize
  have hcurv : 61*Ccurv*Cphys ≤ Bcut :=
    (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (le_abs_self Ccurv) (by norm_num)) hCphys).trans hcurvAbs
  obtain ⟨Cbudget,qcap,hCbudget,hUbudget,hqcap,hselect⟩ :=
    exists_capped_source_discrete_budget (Dbase:=Dbase) (Δbase:=Δbase)
      hUsrc hκ hCphys hB hBs
  let w₀ := min (1/4:ℝ) (csrc/(128*Usrc))
  have hw₀ : 0 < w₀ := lt_min (by norm_num) (by positivity)
  have hwcap : w₀ ≤ 1/4 := min_le_left _ _
  have hwsmall : 2*Usrc*w₀ ≤ csrc/64 := by
    calc
      _ ≤ 2*Usrc*(csrc/(128*Usrc)) :=
        mul_le_mul_of_nonneg_left (min_le_right _ _) (by positivity)
      _ = _ := by field_simp; norm_num
  let Cbase := (1536:ℝ)
  let Cmesh := 2*max 1 (63*Usrc/2)
  have hCm : 1 ≤ Cmesh := by
    have hh := le_max_left (1:ℝ) (63*Usrc/2)
    dsimp only [Cmesh]
    linarith only [hh]
  let CtailBand := 4*Usrc*(64/csrc)^2+192/csrc
  let ClowBand := (2*Usrc+csrc/32)*(3072/csrc)^2+3072/csrc
  let CerrorBand := (768:ℝ)^2*CtailBand+ClowBand
  let Carg := 512*768/csrc
  let Cdensity := 128*CerrorBand*(3+Real.log (Carg+1))
  let Ccard := 16*Cbase^2+8*Cdensity
  let Cdelta := (16*Usrc/csrc)*Real.sqrt ((Usrc/2)*Cmesh)
  let Ctri := 2+θ*(1+2*Usrc/csrc)
  let C₀ := 60*588*(2*Usrc/csrc)^2
  let Cpref := Cmesh^12*Cmesh^εloss*(2*Ccard)^10
  let Wconst := 144*Usrc/(csrc*κ)
  let CKlog := 3+Real.log (Cmesh+1)
  let Cerror := 8*(2*Real.sqrt 3*(1+Real.log 6)+72*Usrc/(csrc*κ))
  let Cfamily := CF^12*2^11*(C*Cap^11*Wconst^6*CKlog^12*Cpref+Cerror^12)
  let Cband := 2+1/Real.log 2
  let Cterminal := Cdensity/(2*qcap^2)
  let Cendpoint := 112/κ+2/(Cphys+2)+41/4
  let Ctotal := (2:ℝ)^11*
    (Cband^11*(Cterminal^12+(8:ℝ)^12*Cband*Cfamily)+Cendpoint^12)
  have hθ : 0 < θ := by
    clear * - hUsrc hcsrc hκ
    dsimp only [θ,L]
    positivity
  have hCap : 0 ≤ Cap := by
    clear * - hθ hUsrc hcsrc
    dsimp only [Cap,NarrowCap]
    positivity
  have hTotal : 0 ≤ Ctotal := by
    clear * - hC hCap hCm
    have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
    dsimp only [Ctotal,Cband,Cfamily,Cpref]
    positivity
  let a₁ := Ctri*Dtype/Usrc
  let a₂ := Ctri*Dtype
  let a₃ := Ctri*Dtype*Cdelta/Usrc
  let a₄ := Ctri*Dtype*Cdelta
  let a₅ := C₀*(Cmain+2*Bselect*Ctail)*Usrc^((4:ℝ)/3)
  let Cmass := 1+|a₁|+|a₂|+|a₃|+|a₄|+|a₅|
  have hCmass : 1 ≤ Cmass := by
    dsimp only [Cmass]
    linarith only [abs_nonneg a₁,abs_nonneg a₂,abs_nonneg a₃,abs_nonneg a₄,abs_nonneg a₅]
  have hAbsorb := eventually_selected_band_logarithmic_absorption
    (C:=|Ctotal| *Cmass) (mul_nonneg (abs_nonneg _) (zero_le_one.trans hCmass)) hε
  refine ⟨Cbudget,w₀,hCbudget,hw₀,hwcap,?_⟩
  filter_upwards [hfinite,hAbsorb,Filter.eventually_ge_atTop (1:ℝ)] with T hfiniteT habsorb hTone
  clear hfinite hAbsorb
  intro Fsrc rshift sshift Y n N R Jsep d Wmax M
    hNlink hNtwo hR hd hW hWsmall hJsep hJM hWJ hy hsepY hshifts
    hreg hlower hjets htests hnegative Φ hmodels hscale
    hsep hrad hlength hcubic hcapRoom hHeight hMT hRT hNten A Bint hA hab hBint
    Yc ErrorTotal Main
  have hT : 0 < T := zero_lt_one.trans_le hTone
  have hNreal : (2:ℝ) ≤ N := by exact_mod_cast hNtwo
  have hNp : (0:ℝ) < N := by linarith only [hNreal]
  have hNOne : (1:ℝ) ≤ N := by linarith only [hNreal]
  have hRp : 0 < R := zero_lt_one.trans_le hR
  obtain ⟨Qbase,kmax,Kmesh,Usel,hM,hRN,hNR,hNM,hRM,hNcube,hpad,hquartic,hquadratic,
    hsmall,hQbase,hBaseHi,hNQ,hQcap,hkmax,hK,hvalid,hmono,hbuffer,hmore⟩ :=
    hselect N M R hNOne hR hsep hrad hlength hcubic hcapRoom
  clear hselect
  let Q := fun k : ℕ => Qbase*2^k
  have hMtwo : 2 ≤ M := hNreal.trans hNM
  have hNpos : 0 < N := by omega
  have hUband : Usrc*T/M^2 ≤ 1 := by
    apply (div_le_iff₀ (sq_pos_of_pos hM)).mpr
    simp only [one_mul]
    apply (mul_le_mul_iff_left₀ hM).mp
    calc
      (Usrc*T)*M = (Usrc*M)*T := by ring
      _ ≤ (Cbudget*M)*T :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hUbudget hM.le) hT.le
      _ ≤ ((N:ℝ)*R^2)*T := mul_le_mul_of_nonneg_right hHeight hT.le
      _ = M^2*M := by nlinarith only [hscale]
  have hvalidSource : ∀ k ≤ kmax,
      63*(Usrc/(2*(N:ℝ)*R^2))*(Q k:ℝ)*(N:ℝ)^2 ≤ Kmesh k ∧
      (Q k:ℝ)*(N:ℝ) ≤ (Kmesh k:ℝ)*R^2 ∧
      1 ≤ Usel k ∧ Bselect^2*(Usel k:ℝ)^3*R^2 ≤ (N:ℝ)^2 ∧
      R ≤ (Q k:ℝ) ∧ (Usel k:ℝ) ≤ ((N:ℝ)/(Q k:ℝ))^((2:ℝ)/3)/Bselect ∧
      (Q k:ℝ) ≤ N ∧ (Usel k:ℝ) ≤ R^2 ∧ 2*R^2 ≤ (Q k:ℝ)*(N:ℝ) ∧
      Δbase*(Q k:ℝ)/(N:ℝ)+
        quarticNonlinearResidualConstant σ δ*(2*(Q k:ℝ))/(N:ℝ) ≤ 1/2 ∧
      Δbase*(Q k:ℝ)/(N:ℝ) < 1/2 := by
    intro k hk
    obtain ⟨hsource,hmesh,hU,hwrap,hRQ,hupper,hQN,hUR,hmin,hD,hDelta⟩ := hvalid k hk
    refine ⟨hsource,hmesh,hU,hwrap,hRQ,hupper,hQN,hUR,hmin,?_,hDelta⟩
    convert hD using 1
    dsimp only [Dbase,Δbase]
    ring
  have hraw :=
    hfiniteT Fsrc rshift sshift Y n N Qbase kmax Kmesh Usel R Jsep
      (d:=d) (Wmax:=Wmax) (M:=M) (δ:=δ) (Bcut:=Bcut) (Bselect:=Bselect)
      (Cbase:=Cbase) (Cmesh:=Cmesh) (qcap:=qcap)
      hK hNlink hd hW (hWsmall.trans hwcap)
      ((mul_le_mul_of_nonneg_left hWsmall (by positivity)).trans hwsmall)
      hT hMtwo hNpos hδ hR hRM hJsep hJM hNM hWJ
      hy hsepY hshifts hreg hlower hjets htests hnegative hmodels
      hscale hpad hquartic hquadratic hBcut hBsSize hcutMargin hNten
      (Or.inr ⟨by linarith only [hMtwo],hNM.trans hMT,hRT⟩)
      hQbase hNQ hsmall hNR hRN hNcube hNreal
      (by simpa only [Cphys,add_assoc,show (1:ℝ)+2=3 by norm_num] using hanchor)
      hUband hsize hcurv hvalidSource (fun k _ => hmono k) hbuffer
      hTone hMT hδzero hCm hBaseHi hkmax hqcap hQcap hmore A Bint hA hab hBint
  clear hfiniteT
  have heps : 2*εloss=ε/2 := by dsimp only [εloss]; ring
  exact double_difference_five_monomial_absorption
    (Ctri:=Ctri) (Dtype:=Dtype) (Cdelta:=Cdelta) (C₀:=C₀)
    (Cmain:=Cmain) (Bselect:=Bselect) (Ctail:=Ctail) (Ctotal:=Ctotal) (ε:=ε)
    hUsrc (Nat.cast_nonneg _) hM hNp hRp hJsep.le hT hTotal habsorb.2.2
    (by simpa only [heps] using hraw)


example
    {csrc Usrc σ δ ε : ℝ}
    (hcsrc : 0 < csrc) (hUsrc : 0 < Usrc) (hσ : 0 < σ)
    (hδzero : 0 ≤ δ) (hδ : δ ≤ min (modelPhaseThirdLower σ) 1)
    (hε : 0 < ε)
    (hanchor : csrc ≤ 4*modelPhaseThirdLower σ/(σ*(σ+1)+3)) :
    ∃ Cbudget w₀ : ℝ, 1 ≤ Cbudget ∧ 0 < w₀ ∧ w₀ ≤ 1/4 ∧
    ∀ᶠ T : ℝ in Filter.atTop, ∀ (Fsrc rshift sshift : ℝ → ℝ) (Y : Finset ℝ)
      (n N : ℕ) (R Jsep : ℝ) {d Wmax M : ℝ},
      N=8*n → 2 ≤ N → 1 ≤ R → 0 < d → 0 ≤ Wmax → Wmax ≤ w₀ →
      0 < Jsep → Jsep ≤ M → Wmax*Jsep ≤ 1 →
      (∀ y∈Y, y∈Icc (1:ℝ) 2) →
      (∀ y∈Y, ∀ z∈Y, y≠z → 1 ≤ Jsep*|y-z|) →
      (∀ y∈Y, 0 ≤ rshift y ∧ 0 ≤ sshift y ∧
        rshift y*sshift y=d*y ∧ rshift y+sshift y ≤ Wmax) →
      (∀ w, 0 < w → ContDiffAt ℝ ∞ Fsrc w) →
      (∀ w∈Icc (1/2:ℝ) 3, csrc ≤ iteratedDeriv 5 Fsrc w) →
      (∀ w∈Icc (1/2:ℝ) 3, ∀ j, 1 ≤ j → j ≤ 7 → |iteratedDeriv j Fsrc w| ≤ Usrc) →
      (∀ w∈Icc (1/2:ℝ) 3,
        csrc ≤ |(iteratedDeriv 5 Fsrc w)^2-iteratedDeriv 4 Fsrc w*iteratedDeriv 6 Fsrc w|) →
      (∀ w∈Icc (1/2:ℝ) 3, iteratedDeriv 4 Fsrc w ≤ -csrc) →
      let Φ := fun y u =>
        (Fsrc u-Fsrc (u+rshift y)-Fsrc (u+sshift y)+Fsrc (u+rshift y+sshift y))/d
      (∀ y∈Y, Expdb.IsApproximateModelPhaseFunction (Φ y) σ 4 δ) →
      T*(N:ℝ)*R^2=M^3 →
      Cbudget*R ≤ N → Cbudget*(N:ℝ) ≤ R^2 → Cbudget*(N:ℝ) ≤ M →
      Cbudget*(N:ℝ)^3 ≤ M*R^2 → Cbudget*(N:ℝ)*R ≤ M →
      Cbudget*M ≤ (N:ℝ)*R^2 → M ≤ T → R^2 ≤ T →
      (N:ℝ)^10 ≤ M^3*R^7 →
      ∀ A Bint : ℝ → ℤ, (∀ y∈Y, ⌈M⌉ ≤ A y) →
      (∀ y∈Y, A y ≤ Bint y) → (∀ y∈Y, Bint y ≤ ⌊2*M⌋) →
      let Yc := (Y.card:ℝ)
      let ErrorTotal := Yc*M/Real.sqrt (N:ℝ)+Yc*M*R^2/(N:ℝ)^2+
        Yc*(N:ℝ)^2*R^2/M+Yc*(N:ℝ)*((N:ℝ)/R)^((2:ℝ)/3)
      let Main := Yc^11*M^10*(N:ℝ)^2/R^4+Yc^11*M^11*(N:ℝ)^2/R^7+
        Yc^11*Jsep*M^10/R^2+Yc^11*Jsep*M^11/R^5+
        Yc^12*M^10*R^2/(N:ℝ)^2*(R/(N:ℝ))^((2:ℝ)/3)*(T/M^2)^((4:ℝ)/3)
      (∑ y∈Y, ‖∑ j∈Finset.Ioc (A y) (Bint y),(𝐞 (T*Φ y ((j:ℝ)/M)):ℂ)‖)^12 ≤
        T^ε*(Main+ErrorTotal^12) := by
  exact eventually_double_difference_uniform_capped_source_bound
    hcsrc hUsrc hσ hδzero hδ hε hanchor

#print axioms eventually_double_difference_uniform_capped_source_bound


/-- Unchanged existing private radius-comparison proof; promotion reuses the original. -/
private theorem upperOriginal_comparable_radius_powers
    {N R S D : ℝ} (hN : 0<N) (hR : 0<R) (hS : 0<S) (hD : 1≤D)
    (hSR : S≤D*R) (hRS : R≤D*S) :
    S^2≤D^2*R^2 ∧ 1/S^2≤D^2/R^2 ∧
      (N/S)^((2:ℝ)/3)≤D*(N/R)^((2:ℝ)/3) ∧
      (S/N)^((2:ℝ)/3)≤D*(R/N)^((2:ℝ)/3) := by
  have hD0 : 0≤D := zero_le_one.trans hD
  have hDs : D^((2:ℝ)/3)≤D := by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le hD (by norm_num : (2:ℝ)/3≤1)
  have hpow {x y : ℝ} (hx : 0≤x) (hy : 0≤y) (hxy : x≤D*y) :
      x^((2:ℝ)/3)≤D*y^((2:ℝ)/3) := by
    calc
      _ ≤ (D*y)^((2:ℝ)/3) := Real.rpow_le_rpow hx hxy (by norm_num)
      _ = D^((2:ℝ)/3)*y^((2:ℝ)/3) := Real.mul_rpow hD0 hy
      _ ≤ _ := mul_le_mul_of_nonneg_right hDs (Real.rpow_nonneg hy _)
  refine ⟨?_,?_,?_,?_⟩
  · simpa only [mul_pow] using pow_le_pow_left₀ hS.le hSR 2
  · apply (div_le_div_iff₀ (sq_pos_of_pos hS) (sq_pos_of_pos hR)).mpr
    simpa only [one_mul,mul_pow] using pow_le_pow_left₀ hR.le hRS 2
  · apply hpow (div_nonneg hN.le hS.le) (div_nonneg hN.le hR.le)
    calc
      _ ≤ (D*N)/R := (div_le_div_iff₀ hS hR).mpr (by
        nlinarith only [mul_le_mul_of_nonneg_left hRS hN.le])
      _ = _ := by ring
  · apply hpow (div_nonneg hS.le hN.le) (div_nonneg hR.le hN.le)
    calc
      _ ≤ (D*R)/N := div_le_div_of_nonneg_right hSR hN.le
      _ = _ := by ring

example
    {N R S D : ℝ} (hN : 0<N) (hR : 0<R) (hS : 0<S) (hD : 1≤D)
    (hSR : S≤D*R) (hRS : R≤D*S) :
    S^2≤D^2*R^2 ∧ 1/S^2≤D^2/R^2 ∧
      (N/S)^((2:ℝ)/3)≤D*(N/R)^((2:ℝ)/3) ∧
      (S/N)^((2:ℝ)/3)≤D*(R/N)^((2:ℝ)/3) := by
  exact upperOriginal_comparable_radius_powers hN hR hS hD hSR hRS

#print axioms upperOriginal_comparable_radius_powers

/-- Unchanged existing private radius-comparison proof; promotion reuses the original. -/
private theorem upperOriginal_upper_radius_error_bound
    {Ysmall Y M N R S D : ℝ}
    (hYsmall : 0≤Ysmall) (hY : Ysmall≤Y) (hM : 0<M) (hN : 0<N)
    (hR : 0<R) (hS : 0<S) (hD : 1≤D) (hSR : S≤D*R) (hRS : R≤D*S) :
    Ysmall*M/Real.sqrt N+Ysmall*M*S^2/N^2+Ysmall*N*(N/S)^((2:ℝ)/3) ≤
      D^2*(Y*M/Real.sqrt N+Y*M*R^2/N^2+Y*N*(N/R)^((2:ℝ)/3)) := by
  have hY0 := hYsmall.trans hY
  have hD0 := zero_le_one.trans hD
  have hD2 : 1≤D^2 := by nlinarith only [hD,sq_nonneg (D-1)]
  have hDD2 : D≤D^2 := by nlinarith only [hD,sq_nonneg (D-1)]
  obtain ⟨hSq,_,hInv,_⟩ := upperOriginal_comparable_radius_powers hN hR hS hD hSR hRS
  have h₁ : Ysmall*M/Real.sqrt N≤D^2*(Y*M/Real.sqrt N) := by
    calc
      _ ≤ Y*M/Real.sqrt N := by gcongr
      _ ≤ _ := le_mul_of_one_le_left (by positivity) hD2
  have h₂ : Ysmall*M*S^2/N^2≤D^2*(Y*M*R^2/N^2) := by
    calc
      _ ≤ Y*M*(D^2*R^2)/N^2 := by gcongr
      _ = _ := by ring
  have h₃ : Ysmall*N*(N/S)^((2:ℝ)/3)≤D^2*(Y*N*(N/R)^((2:ℝ)/3)) := by
    calc
      _ ≤ Y*N*(D*(N/R)^((2:ℝ)/3)) := by gcongr
      _ = D*(Y*N*(N/R)^((2:ℝ)/3)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hDD2 (by positivity)
  calc
    _ ≤ D^2*(Y*M/Real.sqrt N)+D^2*(Y*M*R^2/N^2)+
        D^2*(Y*N*(N/R)^((2:ℝ)/3)) := add_le_add (add_le_add h₁ h₂) h₃
    _ = _ := by ring

example
    {Ysmall Y M N R S D : ℝ}
    (hYsmall : 0≤Ysmall) (hY : Ysmall≤Y) (hM : 0<M) (hN : 0<N)
    (hR : 0<R) (hS : 0<S) (hD : 1≤D) (hSR : S≤D*R) (hRS : R≤D*S) :
    Ysmall*M/Real.sqrt N+Ysmall*M*S^2/N^2+Ysmall*N*(N/S)^((2:ℝ)/3) ≤
      D^2*(Y*M/Real.sqrt N+Y*M*R^2/N^2+Y*N*(N/R)^((2:ℝ)/3)) := by
  exact upperOriginal_upper_radius_error_bound hYsmall hY hM hN hR hS hD hSR hRS

#print axioms upperOriginal_upper_radius_error_bound

/-- Unchanged existing private radius-comparison proof; promotion reuses the original. -/
private theorem upperOriginal_normalized_radius_comparable
    {γ R S D : ℝ} (hR : 0<R) (hS : 0<S) (hD : 1≤D)
    (hγD : γ≤D) (hDγ : 1≤D*γ) (hlink : γ*S^2=R^2) :
    S≤D*R ∧ R≤D*S := by
  have hD0 := zero_le_one.trans hD
  have hDD2 : D≤D^2 := by nlinarith only [hD,sq_nonneg (D-1)]
  constructor
  · apply (sq_le_sq₀ hS.le (mul_nonneg hD0 hR.le)).mp
    calc
      _ ≤ (D*γ)*S^2 := le_mul_of_one_le_left (sq_nonneg S) hDγ
      _ = D*R^2 := by rw [mul_assoc,hlink]
      _ ≤ D^2*R^2 := mul_le_mul_of_nonneg_right hDD2 (sq_nonneg R)
      _ = _ := (mul_pow D R 2).symm
  · apply (sq_le_sq₀ hR.le (mul_nonneg hD0 hS.le)).mp
    calc
      _ = γ*S^2 := hlink.symm
      _ ≤ D*S^2 := mul_le_mul_of_nonneg_right hγD (sq_nonneg S)
      _ ≤ D^2*S^2 := mul_le_mul_of_nonneg_right hDD2 (sq_nonneg S)
      _ = _ := (mul_pow D S 2).symm

example
    {γ R S D : ℝ} (hR : 0<R) (hS : 0<S) (hD : 1≤D)
    (hγD : γ≤D) (hDγ : 1≤D*γ) (hlink : γ*S^2=R^2) :
    S≤D*R ∧ R≤D*S := by
  exact upperOriginal_normalized_radius_comparable hR hS hD hγD hDγ hlink

#print axioms upperOriginal_normalized_radius_comparable

/-- Capped physical budgets survive the SAME source amplitude/radius normalization.
Unlike the older single-difference budget transport, this retains the cubic and
height budgets and introduces no N^2 <= M restriction. -/
private theorem double_difference_capped_comparable_radius_budgets
    {M N R S T V D C : ℝ} (hM : 0 < M) (hN : 0 < N)
    (hR : 0 < R) (hD : 1 ≤ D) (hC : 1 ≤ C)
    (hSR : S ≤ D*R) (hRS : R ≤ D*S) (hTV : T ≤ D*V)
    (hRlow : C*D^7 ≤ R)
    (hRN : (C*D^7)*R ≤ N) (hNR : (C*D^7)*N ≤ R^2)
    (hNM : (C*D^7)*N ≤ M) (hCubic : (C*D^7)*N^3 ≤ M*R^2)
    (hCap : (C*D^7)*N*R ≤ M) (hHeight : (C*D^7)*M ≤ N*R^2)
    (hMT : (C*D^7)*M ≤ T) (hRT : (C*D^7)*R^2 ≤ T)
    (hTen : (C*D^7)*N^10 ≤ M^3*R^7) :
    1 ≤ S ∧ C*S ≤ N ∧ C*N ≤ S^2 ∧ C*N ≤ M ∧
      C*N^3 ≤ M*S^2 ∧ C*N*S ≤ M ∧ C*M ≤ N*S^2 ∧
      M ≤ V ∧ S^2 ≤ V ∧ N^10 ≤ M^3*S^7 := by
  have hDp := zero_lt_one.trans_le hD
  have hCp := zero_lt_one.trans_le hC
  have hpow (i : ℕ) (hi : i ≤ 7) : C*D^i ≤ C*D^7 :=
    mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hD hi) hCp.le
  have hplain (i : ℕ) (hi : i ≤ 7) : D^i ≤ C*D^7 :=
    (le_mul_of_one_le_left (pow_nonneg hDp.le i) hC).trans (hpow i hi)
  have hB : C ≤ C*D^7 := by simpa only [pow_zero,mul_one] using hpow 0 (by omega)
  have hDb : D ≤ C*D^7 := by simpa only [pow_one] using hplain 1 (by omega)
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · have hh := hDb.trans (hRlow.trans hRS)
    nlinarith only [hh,hDp]
  · calc
      _ ≤ C*(D*R) := mul_le_mul_of_nonneg_left hSR hCp.le
      _ = (C*D^1)*R := by ring
      _ ≤ (C*D^7)*R := mul_le_mul_of_nonneg_right (hpow 1 (by omega)) hR.le
      _ ≤ N := hRN
  · apply (mul_le_mul_iff_right₀ (sq_pos_of_pos hDp)).mp
    calc
      _ = (C*D^2)*N := by ring
      _ ≤ (C*D^7)*N := mul_le_mul_of_nonneg_right (hpow 2 (by omega)) hN.le
      _ ≤ R^2 := hNR
      _ ≤ (D*S)^2 := pow_le_pow_left₀ hR.le hRS 2
      _ = _ := by ring
  · exact (mul_le_mul_of_nonneg_right hB hN.le).trans hNM
  · apply (mul_le_mul_iff_right₀ (sq_pos_of_pos hDp)).mp
    calc
      _ = (C*D^2)*N^3 := by ring
      _ ≤ (C*D^7)*N^3 := mul_le_mul_of_nonneg_right (hpow 2 (by omega)) (by positivity)
      _ ≤ M*R^2 := hCubic
      _ ≤ M*(D*S)^2 := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hR.le hRS 2) hM.le
      _ = _ := by ring
  · calc
      _ ≤ C*N*(D*R) := mul_le_mul_of_nonneg_left hSR (by positivity)
      _ = (C*D^1)*N*R := by ring
      _ ≤ (C*D^7)*N*R :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (hpow 1 (by omega)) hN.le) hR.le
      _ ≤ M := hCap
  · apply (mul_le_mul_iff_right₀ (sq_pos_of_pos hDp)).mp
    calc
      _ = (C*D^2)*M := by ring
      _ ≤ (C*D^7)*M := mul_le_mul_of_nonneg_right (hpow 2 (by omega)) hM.le
      _ ≤ N*R^2 := hHeight
      _ ≤ N*(D*S)^2 := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hR.le hRS 2) hN.le
      _ = _ := by ring
  · apply (mul_le_mul_iff_right₀ hDp).mp
    exact ((mul_le_mul_of_nonneg_right hDb hM.le).trans hMT).trans hTV
  · apply (mul_le_mul_iff_right₀ hDp).mp
    have hSnon : 0 ≤ S := by
      have hh : 0 < D*S := hR.trans_le hRS
      exact (pos_of_mul_pos_right hh hDp.le).le
    calc
      _ ≤ D*(D*R)^2 := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hSnon hSR 2) hDp.le
      _ = D^3*R^2 := by ring
      _ ≤ (C*D^7)*R^2 := mul_le_mul_of_nonneg_right (hplain 3 (by omega)) (sq_nonneg R)
      _ ≤ T := hRT
      _ ≤ D*V := hTV
  · apply (mul_le_mul_iff_right₀ (pow_pos hDp 7)).mp
    calc
      _ ≤ (C*D^7)*N^10 :=
        mul_le_mul_of_nonneg_right (hplain 7 le_rfl) (pow_nonneg hN.le 10)
      _ ≤ M^3*R^7 := hTen
      _ ≤ M^3*(D*S)^7 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hR.le hRS 7) (pow_nonneg hM.le 3)
      _ = _ := by ring


example
    {M N R S T V D C : ℝ} (hM : 0 < M) (hN : 0 < N)
    (hR : 0 < R) (hD : 1 ≤ D) (hC : 1 ≤ C)
    (hSR : S ≤ D*R) (hRS : R ≤ D*S) (hTV : T ≤ D*V)
    (hRlow : C*D^7 ≤ R)
    (hRN : (C*D^7)*R ≤ N) (hNR : (C*D^7)*N ≤ R^2)
    (hNM : (C*D^7)*N ≤ M) (hCubic : (C*D^7)*N^3 ≤ M*R^2)
    (hCap : (C*D^7)*N*R ≤ M) (hHeight : (C*D^7)*M ≤ N*R^2)
    (hMT : (C*D^7)*M ≤ T) (hRT : (C*D^7)*R^2 ≤ T)
    (hTen : (C*D^7)*N^10 ≤ M^3*R^7) :
    1 ≤ S ∧ C*S ≤ N ∧ C*N ≤ S^2 ∧ C*N ≤ M ∧
      C*N^3 ≤ M*S^2 ∧ C*N*S ≤ M ∧ C*M ≤ N*S^2 ∧
      M ≤ V ∧ S^2 ≤ V ∧ N^10 ≤ M^3*S^7 := by
  exact double_difference_capped_comparable_radius_budgets hM hN hR hD hC hSR hRS hTV
    hRlow hRN hNR hNM hCubic hCap hHeight hMT hRT hTen

#print axioms double_difference_capped_comparable_radius_budgets

/-- Radius comparison retains the extra capped terminal error. -/
private theorem double_difference_capped_radius_error_bound
    {Ysmall Y M N R S D : ℝ}
    (hYsmall : 0 ≤ Ysmall) (hY : Ysmall ≤ Y) (hM : 0 < M) (hN : 0 < N)
    (hR : 0 < R) (hS : 0 < S) (hD : 1 ≤ D) (hSR : S ≤ D*R) (hRS : R ≤ D*S) :
    Ysmall*M/Real.sqrt N+Ysmall*M*S^2/N^2+
      Ysmall*N^2*S^2/M+Ysmall*N*(N/S)^((2:ℝ)/3) ≤
    D^2*(Y*M/Real.sqrt N+Y*M*R^2/N^2+
      Y*N^2*R^2/M+Y*N*(N/R)^((2:ℝ)/3)) := by
  have hY0 := hYsmall.trans hY
  have hbase := upperOriginal_upper_radius_error_bound hYsmall hY hM hN hR hS hD hSR hRS
  have hSq := (upperOriginal_comparable_radius_powers hN hR hS hD hSR hRS).1
  have hnew : Ysmall*N^2*S^2/M ≤ D^2*(Y*N^2*R^2/M) := by
    calc
      _ ≤ Y*N^2*(D^2*R^2)/M := by gcongr
      _ = _ := by ring
  nlinarith only [hbase,hnew]


example
    {Ysmall Y M N R S D : ℝ}
    (hYsmall : 0 ≤ Ysmall) (hY : Ysmall ≤ Y) (hM : 0 < M) (hN : 0 < N)
    (hR : 0 < R) (hS : 0 < S) (hD : 1 ≤ D) (hSR : S ≤ D*R) (hRS : R ≤ D*S) :
    Ysmall*M/Real.sqrt N+Ysmall*M*S^2/N^2+
      Ysmall*N^2*S^2/M+Ysmall*N*(N/S)^((2:ℝ)/3) ≤
    D^2*(Y*M/Real.sqrt N+Y*M*R^2/N^2+
      Y*N^2*R^2/M+Y*N*(N/R)^((2:ℝ)/3)) := by
  exact double_difference_capped_radius_error_bound hYsmall hY hM hN hR hS hD hSR hRS

#print axioms double_difference_capped_radius_error_bound

/-- The five actual physical main terms are uniform under common height/radius normalization. -/
private theorem double_difference_capped_radius_main_bound
    {Ysmall Y M N R S D J T V : ℝ}
    (hYsmall : 0 ≤ Ysmall) (hY : Ysmall ≤ Y) (hM : 0 < M) (hN : 0 < N)
    (hR : 0 < R) (hS : 0 < S) (hD : 1 ≤ D) (hJ : 0 ≤ J)
    (hT : 0 < T) (hV : 0 < V)
    (hSR : S ≤ D*R) (hRS : R ≤ D*S) (hVT : V ≤ D*T) :
    Ysmall^11*M^10*N^2/S^4+Ysmall^11*M^11*N^2/S^7+
      Ysmall^11*J*M^10/S^2+Ysmall^11*J*M^11/S^5+
      Ysmall^12*M^10*S^2/N^2*(S/N)^((2:ℝ)/3)*(V/M^2)^((4:ℝ)/3) ≤
    D^8*(Y^11*M^10*N^2/R^4+Y^11*M^11*N^2/R^7+
      Y^11*J*M^10/R^2+Y^11*J*M^11/R^5+
      Y^12*M^10*R^2/N^2*(R/N)^((2:ℝ)/3)*(T/M^2)^((4:ℝ)/3)) := by
  have hY0 := hYsmall.trans hY
  have hD0 := zero_le_one.trans hD
  have hInv (j : ℕ) : 1/S^j ≤ D^j/R^j := by
    apply (div_le_div_iff₀ (pow_pos hS j) (pow_pos hR j)).mpr
    simpa only [one_mul,mul_pow] using pow_le_pow_left₀ hR.le hRS j
  have hi₄ := hInv 4
  have hi₇ := hInv 7
  have hi₂ := hInv 2
  have hi₅ := hInv 5
  obtain ⟨hSq,_,_,hFor⟩ := upperOriginal_comparable_radius_powers hN hR hS hD hSR hRS
  have hD48 : D^4 ≤ D^8 := pow_le_pow_right₀ hD (by norm_num)
  have hD78 : D^7 ≤ D^8 := pow_le_pow_right₀ hD (by norm_num)
  have hD28 : D^2 ≤ D^8 := pow_le_pow_right₀ hD (by norm_num)
  have hD58 : D^5 ≤ D^8 := pow_le_pow_right₀ hD (by norm_num)
  have hTr : (V/M^2)^((4:ℝ)/3) ≤ D^2*(T/M^2)^((4:ℝ)/3) := by
    have hDe : D^((4:ℝ)/3) ≤ D^2 := by
      rw [←Real.rpow_natCast D 2]
      exact Real.rpow_le_rpow_of_exponent_le hD (by norm_num)
    calc
      _ ≤ (D*(T/M^2))^((4:ℝ)/3) := by
        apply Real.rpow_le_rpow (by positivity) _ (by norm_num)
        simpa only [mul_div_assoc] using div_le_div_of_nonneg_right hVT (sq_nonneg M)
      _ = D^((4:ℝ)/3)*(T/M^2)^((4:ℝ)/3) := Real.mul_rpow hD0 (by positivity)
      _ ≤ _ := mul_le_mul_of_nonneg_right hDe (by positivity)
  have h₁ : Ysmall^11*M^10*N^2/S^4 ≤ D^8*(Y^11*M^10*N^2/R^4) := by
    calc
      _ = (Ysmall^11*M^10*N^2)*(1/S^4) := by ring
      _ ≤ (Y^11*M^10*N^2)*(D^4/R^4) := by gcongr
      _ = D^4*(Y^11*M^10*N^2/R^4) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hD48 (by positivity)
  have h₂ : Ysmall^11*M^11*N^2/S^7 ≤ D^8*(Y^11*M^11*N^2/R^7) := by
    calc
      _ = (Ysmall^11*M^11*N^2)*(1/S^7) := by ring
      _ ≤ (Y^11*M^11*N^2)*(D^7/R^7) := by gcongr
      _ = D^7*(Y^11*M^11*N^2/R^7) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hD78 (by positivity)
  have h₃ : Ysmall^11*J*M^10/S^2 ≤ D^8*(Y^11*J*M^10/R^2) := by
    calc
      _ = (Ysmall^11*J*M^10)*(1/S^2) := by ring
      _ ≤ (Y^11*J*M^10)*(D^2/R^2) := by gcongr
      _ = D^2*(Y^11*J*M^10/R^2) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hD28 (by positivity)
  have h₄ : Ysmall^11*J*M^11/S^5 ≤ D^8*(Y^11*J*M^11/R^5) := by
    calc
      _ = (Ysmall^11*J*M^11)*(1/S^5) := by ring
      _ ≤ (Y^11*J*M^11)*(D^5/R^5) := by gcongr
      _ = D^5*(Y^11*J*M^11/R^5) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hD58 (by positivity)
  have h₅ :
      Ysmall^12*M^10*S^2/N^2*(S/N)^((2:ℝ)/3)*(V/M^2)^((4:ℝ)/3) ≤
      D^8*(Y^12*M^10*R^2/N^2*(R/N)^((2:ℝ)/3)*(T/M^2)^((4:ℝ)/3)) := by
    calc
      _ ≤ (Y^12*M^10*(D^2*R^2)/N^2)*
          (D*(R/N)^((2:ℝ)/3))*(D^2*(T/M^2)^((4:ℝ)/3)) := by gcongr
      _ = D^5*(Y^12*M^10*R^2/N^2*(R/N)^((2:ℝ)/3)*(T/M^2)^((4:ℝ)/3)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hD58 (by positivity)
  calc
    _ ≤ D^8*(Y^11*M^10*N^2/R^4)+D^8*(Y^11*M^11*N^2/R^7)+
        D^8*(Y^11*J*M^10/R^2)+D^8*(Y^11*J*M^11/R^5)+
        D^8*(Y^12*M^10*R^2/N^2*(R/N)^((2:ℝ)/3)*(T/M^2)^((4:ℝ)/3)) :=
      add_le_add (add_le_add (add_le_add (add_le_add h₁ h₂) h₃) h₄) h₅
    _ = _ := by ring


example
    {Ysmall Y M N R S D J T V : ℝ}
    (hYsmall : 0 ≤ Ysmall) (hY : Ysmall ≤ Y) (hM : 0 < M) (hN : 0 < N)
    (hR : 0 < R) (hS : 0 < S) (hD : 1 ≤ D) (hJ : 0 ≤ J)
    (hT : 0 < T) (hV : 0 < V)
    (hSR : S ≤ D*R) (hRS : R ≤ D*S) (hVT : V ≤ D*T) :
    Ysmall^11*M^10*N^2/S^4+Ysmall^11*M^11*N^2/S^7+
      Ysmall^11*J*M^10/S^2+Ysmall^11*J*M^11/S^5+
      Ysmall^12*M^10*S^2/N^2*(S/N)^((2:ℝ)/3)*(V/M^2)^((4:ℝ)/3) ≤
    D^8*(Y^11*M^10*N^2/R^4+Y^11*M^11*N^2/R^7+
      Y^11*J*M^10/R^2+Y^11*J*M^11/R^5+
      Y^12*M^10*R^2/N^2*(R/N)^((2:ℝ)/3)*(T/M^2)^((4:ℝ)/3)) := by
  exact double_difference_capped_radius_main_bound hYsmall hY hM hN hR hS hD hJ hT hV hSR hRS hVT

#print axioms double_difference_capped_radius_main_bound

/-- The SAME sharp extension of the original model supplies every normalized
double-difference family. This consumes the constructed capped source estimate,
with all physical budgets transported and the literal phase sums preserved. -/
private theorem approximateModelPhase_enlarged_double_capped_quantitative
    {σ ε : ℝ} (hσ : 0 < σ) (hε : 0 < ε) :
    ∃ δ w₀ B C : ℝ, 0 < δ ∧ 0 < w₀ ∧ w₀ ≤ 1/4 ∧ 1 ≤ B ∧ 1 ≤ C ∧
      ∀ (M : ℝ) (F : ℝ → ℝ), 1 ≤ M →
        Expdb.IsApproximateModelPhaseFunction F σ 7 δ →
      ∃ Fext : ℝ → ℝ,
        (∀ (X : ℝ) (a b : ℕ), M ≤ (a:ℝ) → (b:ℝ) ≤ 2*M →
          ‖Expdb.exponentialSumAt F X M a b-
            Expdb.exponentialSumAt Fext X M a b‖ ≤ 6) ∧
        ∀ (T : ℝ) (Y : Finset ℝ) (rshift sshift : ℝ → ℝ) (n N : ℕ)
          (R Jsep d Wmax : ℝ),
          C ≤ T → N=8*n → 2 ≤ N → B ≤ R →
          0 < d → 0 ≤ Wmax → Wmax ≤ w₀ → 0 < Jsep → Jsep ≤ M → Wmax*Jsep ≤ 1 →
          (∀ y∈Y, y∈Icc (1:ℝ) 2) →
          (∀ y∈Y, ∀ z∈Y, y≠z → 1 ≤ Jsep*|y-z|) →
          (∀ y∈Y, 0 < rshift y ∧ 0 < sshift y ∧
            rshift y*sshift y=d*y ∧ rshift y+sshift y ≤ Wmax) →
          T*(N:ℝ)*R^2=M^3 →
          B*R ≤ N → B*(N:ℝ) ≤ R^2 → B*(N:ℝ) ≤ M →
          B*(N:ℝ)^3 ≤ M*R^2 → B*(N:ℝ)*R ≤ M →
          B*M ≤ (N:ℝ)*R^2 → B*M ≤ T → B*R^2 ≤ T →
          B*(N:ℝ)^10 ≤ M^3*R^7 →
          ∀ A Bint : ℝ → ℤ, (∀ y∈Y, ⌈M⌉ ≤ A y) →
          (∀ y∈Y, A y ≤ Bint y) → (∀ y∈Y, Bint y ≤ ⌊2*M⌋) →
          let Yc := (Y.card:ℝ)
          let ErrorTotal := Yc*M/Real.sqrt (N:ℝ)+Yc*M*R^2/(N:ℝ)^2+
            Yc*(N:ℝ)^2*R^2/M+Yc*(N:ℝ)*((N:ℝ)/R)^((2:ℝ)/3)
          let Main := Yc^11*M^10*(N:ℝ)^2/R^4+Yc^11*M^11*(N:ℝ)^2/R^7+
            Yc^11*Jsep*M^10/R^2+Yc^11*Jsep*M^11/R^5+
            Yc^12*M^10*R^2/(N:ℝ)^2*(R/(N:ℝ))^((2:ℝ)/3)*(T/M^2)^((4:ℝ)/3)
          (∑ y∈Y, ‖∑ j∈Finset.Ioc (A y) (Bint y),
            (𝐞 (T*(Fext ((j:ℝ)/M)-Fext ((j:ℝ)/M+rshift y)-
              Fext ((j:ℝ)/M+sshift y)+Fext ((j:ℝ)/M+rshift y+sshift y))/d):ℂ)‖)^12 ≤
            C*T^ε*(Main+ErrorTotal^12) := by
  classical
  have hσtwo : 0 < σ+2 := by linarith only [hσ]
  let δmodel := min (modelPhaseThirdLower (σ+2)) 1/2
  have hmin : 0 < min (modelPhaseThirdLower (σ+2)) 1 :=
    lt_min (modelPhaseThirdLower_pos hσtwo) zero_lt_one
  have hδmodel : 0 < δmodel := half_pos hmin
  have hδmodelCap : δmodel ≤ min (modelPhaseThirdLower (σ+2)) 1 := by
    dsimp only [δmodel]
    linarith only [hmin]
  obtain ⟨δ,wsrc,a,c,U,hδ,hwsrc,hwsrcCap,ha,hc,hU,_hsmall,hanchor,hsource⟩ :=
    approximateModelPhase_enlarged_double_common_scale_source hσ hδmodel
  have hanchor' : c ≤ 4*modelPhaseThirdLower (σ+2)/((σ+2)*((σ+2)+1)+3) := by
    simpa only [add_assoc,show (2:ℝ)+1=3 by norm_num] using hanchor
  obtain ⟨Cbudget,wquant,hCbudget,hwquant,_hwquantCap,hquant⟩ :=
    eventually_double_difference_uniform_capped_source_bound
      hc hU hσtwo hδmodel.le hδmodelCap hε hanchor'
  obtain ⟨Tcut,hTcut⟩ := Filter.eventually_atTop.mp hquant
  let G := σ*(σ+1)
  have hG : 0 < G := by dsimp only [G]; positivity
  let D := 2+2*G+1/G
  have hD : 1 ≤ D := by
    dsimp only [D]
    have hi : 0 < 1/G := by positivity
    linarith only [hG,hi]
  have hDp := zero_lt_one.trans_le hD
  have hDG : 1 ≤ D*G := by
    have hi : (1/G)*G=1 := div_mul_cancel₀ 1 hG.ne'
    dsimp only [D]
    nlinarith only [hi,hG,sq_nonneg G]
  have hGD : 2*G ≤ D := by
    dsimp only [D]
    have hi : 0 < 1/G := by positivity
    linarith only [hi]
  let B := Cbudget*D^7
  have hB : 1 ≤ B := one_le_mul_of_one_le_of_one_le hCbudget (one_le_pow₀ hD)
  let Cap := 4/a+3
  have hCap : 1 ≤ Cap := by
    dsimp only [Cap]
    have hh : 0 < 4/a := by positivity
    linarith only [hh]
  let K := (2*G)^ε*D^24
  have hK : 0 ≤ K := by dsimp only [K]; positivity
  let C := max 1 (max (Tcut/G) (Cap^12*K))
  have hC : 1 ≤ C := le_max_left _ _
  have hCcut : Tcut/G ≤ C := (le_max_left _ _).trans (le_max_right _ _)
  have hCK : Cap^12*K ≤ C := (le_max_right _ _).trans (le_max_right _ _)
  refine ⟨δ,min wsrc wquant,B,C,hδ,lt_min hwsrc hwquant,
    (min_le_left _ _).trans hwsrcCap,hB,hC,?_⟩
  intro M F hM hF
  obtain ⟨Fext,_hreg,hsharp,hcolors⟩ := hsource M F hM hF
  refine ⟨Fext,hsharp,?_⟩
  intro T Y rshift sshift n N R Jsep d Wmax
    hThreshold hN8 hN2 hRlow hd hW hWcap hJsep hJM hWJ hy hsep hshifts
    hphase hRN hNR hNM hCubic hCapRoom hHeight hMT hRT hTen
    A Bint hA hab hBint Yc ErrorTotal Main
  have hMp : 0 < M := zero_lt_one.trans_le hM
  have hNp : (0:ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hRp : 0 < R := zero_lt_one.trans_le (hB.trans hRlow)
  have hTp : 0 < T := zero_lt_one.trans_le (hC.trans hThreshold)
  have hYc : 0 ≤ Yc := Nat.cast_nonneg _
  have hMain : 0 ≤ Main := by
    dsimp only [Main]
    clear * - hYc hMp hNp hRp hJsep hTp
    positivity
  have hError : 0 ≤ ErrorTotal := by
    dsimp only [ErrorTotal]
    clear * - hYc hMp hNp hRp
    positivity
  have hMass : 0 ≤ Main+ErrorTotal^12 := add_nonneg hMain (pow_nonneg hError 12)
  let color := fun y : ℝ => ⌊y/a⌋
  let z := fun y : ℝ => (‖∑ l∈Finset.Ioc (A y) (Bint y),
    (𝐞 (T*(Fext ((l:ℝ)/M)-Fext ((l:ℝ)/M+rshift y)-
      Fext ((l:ℝ)/M+sshift y)+Fext ((l:ℝ)/M+rshift y+sshift y))/d):ℂ)‖:ℂ)
  have hzNorm (V : Finset ℝ) :
      ‖∑ y∈V,z y‖ = ∑ y∈V,‖∑ l∈Finset.Ioc (A y) (Bint y),
        (𝐞 (T*(Fext ((l:ℝ)/M)-Fext ((l:ℝ)/M+rshift y)-
          Fext ((l:ℝ)/M+sshift y)+Fext ((l:ℝ)/M+rshift y+sshift y))/d):ℂ)‖ := by
    dsimp only [z]
    rw [←Complex.ofReal_sum]
    exact Complex.norm_of_nonneg (Finset.sum_nonneg (fun _ _ => norm_nonneg _))
  obtain ⟨hcard,hmoment,hclasses⟩ := hcolors Y id rshift sshift d hd hy (by
    intro y hy'
    obtain ⟨hr,hs,hproduct,hsum⟩ := hshifts y hy'
    exact ⟨hr,hs,hsum.trans (hWcap.trans (min_le_left _ _)),hproduct⟩)
  have hlocal (j : ℤ) (hj : j∈Y.image color) :
      ‖∑ y∈Y.filter (fun y => color y=j),z y‖^12 ≤
        K*T^ε*(Main+ErrorTotal^12) := by
    obtain ⟨y₀,hy₀,_hcolor,hreg,hjets,hlower,htests,hnegative,hscaled⟩ := hclasses j hj
    let γ := G*y₀
    have hy₀range := hy y₀ hy₀
    have hy₀p : 0 < y₀ := zero_lt_one.trans_le hy₀range.1
    have hγ : 0 < γ := mul_pos hG hy₀p
    have hγlo : G ≤ γ := le_mul_of_one_le_right hG.le hy₀range.1
    have hγhi : γ ≤ 2*G := by dsimp only [γ]; nlinarith only [hy₀range.2,hG]
    have hγD := hγhi.trans hGD
    have hDγ : 1 ≤ D*γ := hDG.trans (mul_le_mul_of_nonneg_left hγlo hDp.le)
    let Fsrc := fun w => (1/(σ*(σ+1)*y₀))*Fext w
    let Tnew := T*σ*(σ+1)*y₀
    let Rnew := R*Real.sqrt (1/(σ*(σ+1)*y₀))
    obtain ⟨hTnew,hRnew,hRsq,hnewphase,hmodels⟩ :=
      hscaled T (N:ℝ) R M hTp hRp hphase
    have hTnewEq : Tnew=T*γ := by dsimp only [Tnew,γ,G]; ring
    have hRnewSq : Rnew^2=R^2/γ := by
      simpa only [γ,G,mul_one_div] using hRsq
    have hRg : γ*Rnew^2=R^2 := by rw [hRnewSq]; field_simp
    obtain ⟨hSle,hRle⟩ := upperOriginal_normalized_radius_comparable hRp hRnew hD hγD hDγ hRg
    have hTV : T ≤ D*Tnew := by
      rw [hTnewEq]
      calc
        _ ≤ (D*γ)*T := le_mul_of_one_le_left hTp.le hDγ
        _ = _ := by ring
    have hVT : Tnew ≤ D*T := by
      rw [hTnewEq]
      simpa only [mul_comm] using mul_le_mul_of_nonneg_right hγD hTp.le
    obtain ⟨hRnew1,hnewRN,hnewNR,hnewNM,hnewCubic,hnewCap,hnewHeight,hnewMT,hnewRT,hnewTen⟩ :=
      double_difference_capped_comparable_radius_budgets
        hMp hNp hRp hD hCbudget hSle hRle hTV hRlow
        hRN hNR hNM hCubic hCapRoom hHeight hMT hRT hTen
    have hTnewCut : Tcut ≤ Tnew := by
      rw [hTnewEq]
      exact ((div_le_iff₀ hG).mp (hCcut.trans hThreshold)).trans
        (mul_le_mul_of_nonneg_left hγlo hTp.le)
    let Yj := Y.filter (fun y => color y=j)
    have hYj (y : ℝ) (hy' : y∈Yj) : y∈Y := (Finset.mem_filter.mp hy').1
    have hYjColor (y : ℝ) (hy' : y∈Yj) : color y=j := (Finset.mem_filter.mp hy').2
    let Φ := fun y u =>
      (Fsrc u-Fsrc (u+rshift y)-Fsrc (u+sshift y)+Fsrc (u+rshift y+sshift y))/d
    have hmod (y : ℝ) (hy' : y∈Yj) :
        Expdb.IsApproximateModelPhaseFunction (Φ y) (σ+2) 4 δmodel :=
      (hmodels y (hYj y hy') (hYjColor y hy')).1
    have hq := hTcut Tnew hTnewCut Fsrc rshift sshift Yj n N Rnew Jsep
      (d:=d) (Wmax:=Wmax) (M:=M) hN8 hN2 hRnew1 hd hW (hWcap.trans (min_le_right _ _)) hJsep hJM hWJ
      (fun y hy' => hy y (hYj y hy'))
      (fun y hy' v hv hne => hsep y (hYj y hy') v (hYj v hv) hne)
      (by
        intro y hy'
        obtain ⟨hr,hs,hprod,hsum⟩ := hshifts y (hYj y hy')
        exact ⟨hr.le,hs.le,hprod,hsum⟩)
      hreg hlower hjets htests hnegative hmod hnewphase hnewRN hnewNR hnewNM
      hnewCubic hnewCap hnewHeight hnewMT hnewRT hnewTen A Bint
      (fun y hy' => hA y (hYj y hy')) (fun y hy' => hab y (hYj y hy'))
      (fun y hy' => hBint y (hYj y hy'))
    have hYj0 : (0:ℝ) ≤ Yj.card := Nat.cast_nonneg _
    have hYjCard : (Yj.card:ℝ) ≤ Yc := by
      change ((Y.filter (fun y => color y=j)).card:ℝ) ≤ (Y.card:ℝ)
      exact_mod_cast (Finset.card_filter_le Y (fun y => color y=j))
    let Enew := (Yj.card:ℝ)*M/Real.sqrt (N:ℝ)+
      (Yj.card:ℝ)*M*Rnew^2/(N:ℝ)^2+
      (Yj.card:ℝ)*(N:ℝ)^2*Rnew^2/M+
      (Yj.card:ℝ)*(N:ℝ)*((N:ℝ)/Rnew)^((2:ℝ)/3)
    let MainNew := (Yj.card:ℝ)^11*M^10*(N:ℝ)^2/Rnew^4+
      (Yj.card:ℝ)^11*M^11*(N:ℝ)^2/Rnew^7+
      (Yj.card:ℝ)^11*Jsep*M^10/Rnew^2+(Yj.card:ℝ)^11*Jsep*M^11/Rnew^5+
      (Yj.card:ℝ)^12*M^10*Rnew^2/(N:ℝ)^2*
        (Rnew/(N:ℝ))^((2:ℝ)/3)*(Tnew/M^2)^((4:ℝ)/3)
    have hEnew : Enew ≤ D^2*ErrorTotal :=
      double_difference_capped_radius_error_bound hYj0 hYjCard hMp hNp hRp hRnew hD hSle hRle
    have hMainNew : MainNew ≤ D^8*Main :=
      double_difference_capped_radius_main_bound
        hYj0 hYjCard hMp hNp hRp hRnew hD hJsep.le hTp hTnew hSle hRle hVT
    have hEnew0 : 0 ≤ Enew := by
      dsimp only [Enew]
      clear * - hYj0 hMp hNp hRnew
      positivity
    have hMainNew0 : 0 ≤ MainNew := by
      dsimp only [MainNew]
      clear * - hYj0 hMp hNp hRnew hJsep hTnew
      positivity
    have hEpow : Enew^12 ≤ D^24*ErrorTotal^12 := by
      calc
        _ ≤ (D^2*ErrorTotal)^12 := pow_le_pow_left₀ hEnew0 hEnew 12
        _ = _ := by rw [mul_pow,←pow_mul]
    have hMainPow : MainNew ≤ D^24*Main :=
      hMainNew.trans (mul_le_mul_of_nonneg_right
        (pow_le_pow_right₀ hD (by norm_num : 8 ≤ 24)) hMain)
    have hTotal : MainNew+Enew^12 ≤ D^24*(Main+ErrorTotal^12) := by
      calc
        _ ≤ D^24*Main+D^24*ErrorTotal^12 := add_le_add hMainPow hEpow
        _ = _ := (mul_add _ _ _).symm
    have hTpow : Tnew^ε ≤ (2*G)^ε*T^ε := by
      rw [hTnewEq,Real.mul_rpow hTp.le hγ.le]
      calc
        _ ≤ T^ε*(2*G)^ε :=
          mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hγ.le hγhi hε.le)
            (Real.rpow_nonneg hTp.le _)
        _ = _ := mul_comm _ _
    rw [hzNorm]
    calc
      _ = (∑ y∈Yj, ‖∑ l∈Finset.Ioc (A y) (Bint y),
          (𝐞 (Tnew*Φ y ((l:ℝ)/M)):ℂ)‖)^12 := by
        congr 1
        apply Finset.sum_congr rfl
        intro y hy'
        congr 1
        apply Finset.sum_congr rfl
        intro l _
        apply congrArg (fun x : ℝ => (𝐞 x:ℂ))
        exact ((hmodels y (hYj y hy') (hYjColor y hy')).2 (l:ℝ)).symm
      _ ≤ Tnew^ε*(MainNew+Enew^12) := hq
      _ ≤ ((2*G)^ε*T^ε)*(D^24*(Main+ErrorTotal^12)) :=
        mul_le_mul hTpow hTotal (add_nonneg hMainNew0 (pow_nonneg hEnew0 12))
          (mul_nonneg (Real.rpow_nonneg (by positivity) ε) (Real.rpow_nonneg hTp.le ε))
      _ = _ := by dsimp only [K]; ac_rfl
  have hKmass : 0 ≤ K*T^ε*(Main+ErrorTotal^12) :=
    mul_nonneg (mul_nonneg hK (Real.rpow_nonneg hTp.le ε)) hMass
  have hcolorSum :
      (∑ j∈Y.image color, ‖∑ y∈Y.filter (fun y => color y=j),z y‖^12) ≤
        Cap*(K*T^ε*(Main+ErrorTotal^12)) := by
    calc
      _ ≤ ∑ _j∈Y.image color,K*T^ε*(Main+ErrorTotal^12) := Finset.sum_le_sum hlocal
      _ = ((Y.image color).card:ℝ)*(K*T^ε*(Main+ErrorTotal^12)) := by
        rw [Finset.sum_const,nsmul_eq_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_right hcard hKmass
  calc
    _ = ‖∑ y∈Y,z y‖^12 := congrArg (fun x : ℝ => x^12) (hzNorm Y).symm
    _ ≤ Cap^11*∑ j∈Y.image color,‖∑ y∈Y.filter (fun y => color y=j),z y‖^12 := hmoment z
    _ ≤ Cap^11*(Cap*(K*T^ε*(Main+ErrorTotal^12))) :=
      mul_le_mul_of_nonneg_left hcolorSum (pow_nonneg (zero_le_one.trans hCap) 11)
    _ = (Cap^12*K)*(T^ε*(Main+ErrorTotal^12)) := by
      rw [show Cap^12=Cap^11*Cap from pow_succ Cap 11]
      ac_rfl
    _ ≤ C*(T^ε*(Main+ErrorTotal^12)) :=
      mul_le_mul_of_nonneg_right hCK (mul_nonneg (Real.rpow_nonneg hTp.le ε) hMass)
    _ = _ := (mul_assoc _ _ _).symm


example
    {σ ε : ℝ} (hσ : 0 < σ) (hε : 0 < ε) :
    ∃ δ w₀ B C : ℝ, 0 < δ ∧ 0 < w₀ ∧ w₀ ≤ 1/4 ∧ 1 ≤ B ∧ 1 ≤ C ∧
      ∀ (M : ℝ) (F : ℝ → ℝ), 1 ≤ M →
        Expdb.IsApproximateModelPhaseFunction F σ 7 δ →
      ∃ Fext : ℝ → ℝ,
        (∀ (X : ℝ) (a b : ℕ), M ≤ (a:ℝ) → (b:ℝ) ≤ 2*M →
          ‖Expdb.exponentialSumAt F X M a b-
            Expdb.exponentialSumAt Fext X M a b‖ ≤ 6) ∧
        ∀ (T : ℝ) (Y : Finset ℝ) (rshift sshift : ℝ → ℝ) (n N : ℕ)
          (R Jsep d Wmax : ℝ),
          C ≤ T → N=8*n → 2 ≤ N → B ≤ R →
          0 < d → 0 ≤ Wmax → Wmax ≤ w₀ → 0 < Jsep → Jsep ≤ M → Wmax*Jsep ≤ 1 →
          (∀ y∈Y, y∈Icc (1:ℝ) 2) →
          (∀ y∈Y, ∀ z∈Y, y≠z → 1 ≤ Jsep*|y-z|) →
          (∀ y∈Y, 0 < rshift y ∧ 0 < sshift y ∧
            rshift y*sshift y=d*y ∧ rshift y+sshift y ≤ Wmax) →
          T*(N:ℝ)*R^2=M^3 →
          B*R ≤ N → B*(N:ℝ) ≤ R^2 → B*(N:ℝ) ≤ M →
          B*(N:ℝ)^3 ≤ M*R^2 → B*(N:ℝ)*R ≤ M →
          B*M ≤ (N:ℝ)*R^2 → B*M ≤ T → B*R^2 ≤ T →
          B*(N:ℝ)^10 ≤ M^3*R^7 →
          ∀ A Bint : ℝ → ℤ, (∀ y∈Y, ⌈M⌉ ≤ A y) →
          (∀ y∈Y, A y ≤ Bint y) → (∀ y∈Y, Bint y ≤ ⌊2*M⌋) →
          let Yc := (Y.card:ℝ)
          let ErrorTotal := Yc*M/Real.sqrt (N:ℝ)+Yc*M*R^2/(N:ℝ)^2+
            Yc*(N:ℝ)^2*R^2/M+Yc*(N:ℝ)*((N:ℝ)/R)^((2:ℝ)/3)
          let Main := Yc^11*M^10*(N:ℝ)^2/R^4+Yc^11*M^11*(N:ℝ)^2/R^7+
            Yc^11*Jsep*M^10/R^2+Yc^11*Jsep*M^11/R^5+
            Yc^12*M^10*R^2/(N:ℝ)^2*(R/(N:ℝ))^((2:ℝ)/3)*(T/M^2)^((4:ℝ)/3)
          (∑ y∈Y, ‖∑ j∈Finset.Ioc (A y) (Bint y),
            (𝐞 (T*(Fext ((j:ℝ)/M)-Fext ((j:ℝ)/M+rshift y)-
              Fext ((j:ℝ)/M+sshift y)+Fext ((j:ℝ)/M+rshift y+sshift y))/d):ℂ)‖)^12 ≤
            C*T^ε*(Main+ErrorTotal^12) := by
  exact approximateModelPhase_enlarged_double_capped_quantitative hσ hε

#print axioms approximateModelPhase_enlarged_double_capped_quantitative


private theorem upperOriginal_exponentialSumAt_eq_int_Icc
    (F : ℝ → ℝ) (X M : ℝ) (a b : ℕ) :
    Expdb.exponentialSumAt F X M a b =
      ∑ j∈Finset.Icc (a:ℤ) (b:ℤ),Expdb.oscillatory F X M j := by
  unfold Expdb.exponentialSumAt
  apply Finset.sum_bij (fun (n:ℕ) _ => (n:ℤ))
  case hi =>
    intro n hn
    have hn' := Finset.mem_Icc.mp hn
    exact Finset.mem_Icc.mpr ⟨by exact_mod_cast hn'.1,by exact_mod_cast hn'.2⟩
  case i_inj =>
    intro n _ m _ hnm
    exact_mod_cast hnm
  case i_surj =>
    intro z hz
    have hz' := Finset.mem_Icc.mp hz
    have hz0 : 0≤z := (Int.natCast_nonneg a).trans hz'.1
    refine ⟨z.toNat,Finset.mem_Icc.mpr ⟨?_,?_⟩,Int.toNat_of_nonneg hz0⟩
    · omega
    · omega
  case h =>
    intro n _
    simp only [Int.cast_natCast]

private theorem upperOriginal_norm_exponentialSumAt_le_int_Ioc
    (F : ℝ → ℝ) (X M : ℝ) (a b : ℕ) (hab : a≤b) :
    ‖Expdb.exponentialSumAt F X M a b‖ ≤
      1+‖∑ j∈Finset.Ioc (a:ℤ) (b:ℤ),Expdb.oscillatory F X M j‖ := by
  rw [upperOriginal_exponentialSumAt_eq_int_Icc,
    Finset.Icc_eq_cons_Ioc (by exact_mod_cast hab : (a:ℤ)≤b),Finset.sum_cons]
  simpa only [Expdb.norm_oscillatory] using
    norm_add_le (Expdb.oscillatory F X M (a:ℤ))
      (∑ j∈Finset.Ioc (a:ℤ) (b:ℤ),Expdb.oscillatory F X M j)

example (F : ℝ → ℝ) (X M : ℝ) (a b : ℕ) :
    Expdb.exponentialSumAt F X M a b =
      ∑ j∈Finset.Icc (a:ℤ) (b:ℤ),Expdb.oscillatory F X M j := by
  exact upperOriginal_exponentialSumAt_eq_int_Icc F X M a b

#print axioms upperOriginal_exponentialSumAt_eq_int_Icc

example (F : ℝ → ℝ) (X M : ℝ) (a b : ℕ) (hab : a≤b) :
    ‖Expdb.exponentialSumAt F X M a b‖ ≤
      1+‖∑ j∈Finset.Ioc (a:ℤ) (b:ℤ),Expdb.oscillatory F X M j‖ := by
  exact upperOriginal_norm_exponentialSumAt_le_int_Ioc F X M a b hab

#print axioms upperOriginal_norm_exponentialSumAt_le_int_Ioc

/-- The literal double-shift correlation enters the source interval with
exactly one endpoint term. No shifted phase or analytic estimate is assumed. -/
private theorem double_difference_actual_range_le_int_Ioc
    (F : ℝ → ℝ) (X : ℝ) {M : ℝ} (hM : M≠0)
    (a L r s k : ℕ) (hk : 0<k) (hrs : r+s≤L) :
    ‖∑ j∈Finset.range (L+1-r-s),
      (𝐞 (X*(F (((a:ℝ)+j)/M)-F (((a:ℝ)+j+r)/M)-
        F (((a:ℝ)+j+s)/M)+F (((a:ℝ)+j+r+s)/M))):ℂ)‖ ≤
      1+‖∑ j∈Finset.Ioc (a:ℤ) ((a+(L-r-s):ℕ):ℤ),
        (𝐞 ((X*k/M^2)*(F ((j:ℝ)/M)-F ((j:ℝ)/M+(r:ℝ)/M)-
          F ((j:ℝ)/M+(s:ℝ)/M)+F ((j:ℝ)/M+(r:ℝ)/M+(s:ℝ)/M))/
            ((k:ℝ)/M^2)):ℂ)‖ := by
  have hkR : (k:ℝ)≠0 := by exact_mod_cast hk.ne'
  have hd : (k:ℝ)/M^2≠0 := div_ne_zero hkR (pow_ne_zero 2 hM)
  have hcoeff (q : ℝ) : (X*k/M^2)*(q/((k:ℝ)/M^2))=X*q := by
    calc
      _ = X*((q/((k:ℝ)/M^2))*((k:ℝ)/M^2)) := by ring
      _ = _ := by rw [div_mul_cancel₀ q hd]
  let Φ := fun u => (F u-F (u+(r:ℝ)/M)-F (u+(s:ℝ)/M)+
    F (u+(r:ℝ)/M+(s:ℝ)/M))/((k:ℝ)/M^2)
  have heq :
      (∑ j∈Finset.range (L+1-r-s),
        (𝐞 (X*(F (((a:ℝ)+j)/M)-F (((a:ℝ)+j+r)/M)-
          F (((a:ℝ)+j+s)/M)+F (((a:ℝ)+j+r+s)/M))):ℂ)) =
        Expdb.exponentialSumAt Φ (X*k/M^2) M a (a+(L-r-s)) := by
    rw [exponentialSumAt_eq_range,show L-r-s+1=L+1-r-s by omega]
    apply Finset.sum_congr rfl
    intro j _
    apply congrArg (fun t : ℝ => (𝐞 t:ℂ))
    dsimp only [Φ]
    rw [hcoeff]
    simp only [add_div]
  rw [heq]
  calc
    _ ≤ 1+‖∑ j∈Finset.Ioc (a:ℤ) ((a+(L-r-s):ℕ):ℤ),
        Expdb.oscillatory Φ (X*k/M^2) M j‖ :=
      upperOriginal_norm_exponentialSumAt_le_int_Ioc Φ (X*k/M^2) M
        a (a+(L-r-s)) (Nat.le_add_right _ _)
    _ = _ := by
      apply congrArg (fun z : ℂ => 1+‖z‖)
      apply Finset.sum_congr rfl
      intro j _
      unfold Expdb.oscillatory
      apply congrArg (fun t : ℝ => (𝐞 t:ℂ))
      exact (mul_div_assoc _ _ _).symm

example
    (F : ℝ → ℝ) (X : ℝ) {M : ℝ} (hM : M≠0)
    (a L r s k : ℕ) (hk : 0<k) (hrs : r+s≤L) :
    ‖∑ j∈Finset.range (L+1-r-s),
      (𝐞 (X*(F (((a:ℝ)+j)/M)-F (((a:ℝ)+j+r)/M)-
        F (((a:ℝ)+j+s)/M)+F (((a:ℝ)+j+r+s)/M))):ℂ)‖ ≤
      1+‖∑ j∈Finset.Ioc (a:ℤ) ((a+(L-r-s):ℕ):ℤ),
        (𝐞 ((X*k/M^2)*(F ((j:ℝ)/M)-F ((j:ℝ)/M+(r:ℝ)/M)-
          F ((j:ℝ)/M+(s:ℝ)/M)+F ((j:ℝ)/M+(r:ℝ)/M+(s:ℝ)/M))/
            ((k:ℝ)/M^2)):ℂ)‖ := by
  exact double_difference_actual_range_le_int_Ioc F X hM a L r s k hk hrs

#print axioms double_difference_actual_range_le_int_Ioc

/-- Every occupied product block supplies an actual separated double-shift
family with its actual intervals. Empty correlations are removed, and the
one-term endpoint loss is retained explicitly. -/
private theorem double_difference_product_dyadic_actual_family
    (F : ℝ → ℝ) (X : ℝ) {M : ℝ} (hM : 0<M)
    (a L H K k : ℕ) (hk : 0<k) (ha : M≤(a:ℝ)) (hb : ((a+L:ℕ):ℝ)≤2*M) :
    let Pairs := (Finset.Icc 1 (H-1)) ×ˢ (Finset.Icc 1 (K-1))
    let Products := Pairs.image (fun p => p.1*p.2)
    ∀ pick : ℕ → ℕ × ℕ,
      (∀ l∈Products, pick l∈Pairs ∧ (pick l).1*(pick l).2=l) →
    let Block := (Finset.Ico k (2*k)).filter (fun l => l∈Products)
    let Kept := Block.filter (fun l => (pick l).1+(pick l).2≤L)
    let Y := Kept.image (fun l : ℕ => (l:ℝ)/(k:ℝ))
    let rshift := fun y : ℝ => ((pick ⌊(k:ℝ)*y⌋₊).1:ℝ)/M
    let sshift := fun y : ℝ => ((pick ⌊(k:ℝ)*y⌋₊).2:ℝ)/M
    let Bint := fun y : ℝ =>
      ((a+(L-(pick ⌊(k:ℝ)*y⌋₊).1-(pick ⌊(k:ℝ)*y⌋₊).2):ℕ):ℤ)
    Y.card≤k ∧
      (∀ y∈Y, y∈Icc (1:ℝ) 2) ∧
      (∀ y∈Y, ∀ z∈Y, y≠z → 1≤(k:ℝ)*|y-z|) ∧
      (∀ y∈Y, 0<rshift y ∧ 0<sshift y ∧
        rshift y*sshift y=((k:ℝ)/M^2)*y ∧ rshift y+sshift y≤((H:ℝ)+K)/M) ∧
      ⌈M⌉≤(a:ℤ) ∧ (∀ y∈Y, (a:ℤ)≤Bint y) ∧
      (∀ y∈Y, Bint y≤⌊2*M⌋) ∧
      (∑ l∈Block,‖∑ j∈Finset.range (L+1-(pick l).1-(pick l).2),
        (𝐞 (X*(F (((a:ℝ)+j)/M)-F (((a:ℝ)+j+(pick l).1)/M)-
          F (((a:ℝ)+j+(pick l).2)/M)+
          F (((a:ℝ)+j+(pick l).1+(pick l).2)/M))):ℂ)‖) ≤
        (Y.card:ℝ)+∑ y∈Y,‖∑ j∈Finset.Ioc (a:ℤ) (Bint y),
          (𝐞 ((X*k/M^2)*(F ((j:ℝ)/M)-F ((j:ℝ)/M+rshift y)-
            F ((j:ℝ)/M+sshift y)+F ((j:ℝ)/M+rshift y+sshift y))/
              ((k:ℝ)/M^2)):ℂ)‖ := by
  classical
  intro Pairs Products pick hpick Block Kept Y rshift sshift Bint
  have hkR : (0:ℝ)<k := by exact_mod_cast hk
  have hinj : Function.Injective (fun l : ℕ => (l:ℝ)/(k:ℝ)) := by
    intro l m hlm
    exact_mod_cast (div_left_inj' hkR.ne').mp hlm
  have hcard : Y.card=Kept.card := Finset.card_image_of_injOn hinj.injOn
  have hcardK : Kept.card≤k := by
    calc
      _ ≤ Block.card := Finset.card_filter_le _ _
      _ ≤ (Finset.Ico k (2*k)).card := Finset.card_filter_le _ _
      _ = k := by rw [Nat.card_Ico]; omega
  have hfloor (l : ℕ) : ⌊(k:ℝ)*((l:ℝ)/(k:ℝ))⌋₊=l := by
    rw [show (k:ℝ)*((l:ℝ)/(k:ℝ))=(l:ℝ) by field_simp]
    exact Nat.floor_natCast l
  have hKept (l : ℕ) (hl : l∈Kept) :
      l∈Finset.Ico k (2*k) ∧ l∈Products ∧ (pick l).1+(pick l).2≤L := by
    have hh := Finset.mem_filter.mp hl
    have hh' := Finset.mem_filter.mp hh.1
    exact ⟨hh'.1,hh'.2,hh.2⟩
  have hgeom := HuxleyRationalPhase.difference_family_dyadic_parameter_geometry hkR
  refine ⟨hcard.trans_le hcardK,?_,?_,?_,?_,?_,?_,?_⟩
  · intro y hy
    obtain ⟨l,hl,rfl⟩ := Finset.mem_image.mp hy
    have hl' := Finset.mem_Ico.mp (hKept l hl).1
    have hh := hgeom.1 l (by exact_mod_cast hl'.1) (by exact_mod_cast hl'.2.le)
    constructor <;> linarith only [hh.1,hh.2]
  · intro y hy z hz hyz
    obtain ⟨l,_hl,rfl⟩ := Finset.mem_image.mp hy
    obtain ⟨m,_hm,rfl⟩ := Finset.mem_image.mp hz
    have hlm : l≠m := fun he => hyz (congrArg (fun n : ℕ => (n:ℝ)/(k:ℝ)) he)
    have hh := hgeom.2 l m hlm
    rw [show (l:ℝ)/(k:ℝ)-1-((m:ℝ)/(k:ℝ)-1)=
      (l:ℝ)/(k:ℝ)-(m:ℝ)/(k:ℝ) by ring] at hh
    exact hh
  · intro y hy
    obtain ⟨l,hl,rfl⟩ := Finset.mem_image.mp hy
    obtain ⟨hpair,hprod⟩ := hpick l (hKept l hl).2.1
    obtain ⟨hr,hs⟩ := Finset.mem_product.mp hpair
    obtain ⟨hr1,hrH⟩ := Finset.mem_Icc.mp hr
    obtain ⟨hs1,hsK⟩ := Finset.mem_Icc.mp hs
    have hrp : (0:ℝ)<(pick l).1 := by exact_mod_cast (show 0<(pick l).1 by omega)
    have hsp : (0:ℝ)<(pick l).2 := by exact_mod_cast (show 0<(pick l).2 by omega)
    dsimp only [rshift,sshift]
    rw [hfloor]
    refine ⟨div_pos hrp hM,div_pos hsp hM,?_,?_⟩
    · have hh : ((pick l).1:ℝ)*(pick l).2=(l:ℝ) := by exact_mod_cast hprod
      field_simp
      nlinarith only [hh]
    · rw [←add_div]
      apply (div_le_div_iff_of_pos_right hM).mpr
      have hrr : ((pick l).1:ℝ)≤H := by exact_mod_cast (show (pick l).1≤H by omega)
      have hss : ((pick l).2:ℝ)≤K := by exact_mod_cast (show (pick l).2≤K by omega)
      exact add_le_add hrr hss
  · apply Int.ceil_le.mpr
    simpa only [Int.cast_natCast] using ha
  · intro y _
    dsimp only [Bint]
    exact_mod_cast (Nat.le_add_right a (L-(pick ⌊(k:ℝ)*y⌋₊).1-(pick ⌊(k:ℝ)*y⌋₊).2))
  · intro y _
    apply Int.le_floor.mpr
    have hh : ((a+(L-(pick ⌊(k:ℝ)*y⌋₊).1-(pick ⌊(k:ℝ)*y⌋₊).2):ℕ):ℝ)≤
        ((a+L:ℕ):ℝ) := by
      exact_mod_cast (show a+(L-(pick ⌊(k:ℝ)*y⌋₊).1-(pick ⌊(k:ℝ)*y⌋₊).2)≤a+L by omega)
    exact hh.trans hb
  · let f := fun l : ℕ => ‖∑ j∈Finset.range (L+1-(pick l).1-(pick l).2),
        (𝐞 (X*(F (((a:ℝ)+j)/M)-F (((a:ℝ)+j+(pick l).1)/M)-
          F (((a:ℝ)+j+(pick l).2)/M)+
          F (((a:ℝ)+j+(pick l).1+(pick l).2)/M))):ℂ)‖
    have hFilter : (∑ l∈Kept,f l)=∑ l∈Block,f l := by
      apply Finset.sum_filter_of_ne
      intro l _ hne
      by_contra hn
      exact hne (by
        dsimp only [f]
        rw [show L+1-(pick l).1-(pick l).2=0 by omega]
        simp only [Finset.range_zero,Finset.sum_empty,norm_zero])
    change (∑ l∈Block,f l)≤_
    rw [←hFilter,hcard,Finset.sum_image hinj.injOn]
    calc
      _ ≤ ∑ l∈Kept,(1+‖∑ j∈Finset.Ioc (a:ℤ) (Bint ((l:ℝ)/(k:ℝ))),
          (𝐞 ((X*k/M^2)*(F ((j:ℝ)/M)-F ((j:ℝ)/M+rshift ((l:ℝ)/(k:ℝ)))-
            F ((j:ℝ)/M+sshift ((l:ℝ)/(k:ℝ)))+
            F ((j:ℝ)/M+rshift ((l:ℝ)/(k:ℝ))+sshift ((l:ℝ)/(k:ℝ))))/
              ((k:ℝ)/M^2)):ℂ)‖) := by
        apply Finset.sum_le_sum
        intro l hl
        dsimp only [f,Bint,rshift,sshift]
        rw [hfloor]
        exact double_difference_actual_range_le_int_Ioc F X hM.ne'
          a L (pick l).1 (pick l).2 k hk (hKept l hl).2.2
      _ = _ := by rw [Finset.sum_add_distrib,Finset.sum_const,nsmul_eq_mul,mul_one]

example
    (F : ℝ → ℝ) (X : ℝ) {M : ℝ} (hM : 0<M)
    (a L H K k : ℕ) (hk : 0<k) (ha : M≤(a:ℝ)) (hb : ((a+L:ℕ):ℝ)≤2*M) :
    let Pairs := (Finset.Icc 1 (H-1)) ×ˢ (Finset.Icc 1 (K-1))
    let Products := Pairs.image (fun p => p.1*p.2)
    ∀ pick : ℕ → ℕ × ℕ,
      (∀ l∈Products, pick l∈Pairs ∧ (pick l).1*(pick l).2=l) →
    let Block := (Finset.Ico k (2*k)).filter (fun l => l∈Products)
    let Kept := Block.filter (fun l => (pick l).1+(pick l).2≤L)
    let Y := Kept.image (fun l : ℕ => (l:ℝ)/(k:ℝ))
    let rshift := fun y : ℝ => ((pick ⌊(k:ℝ)*y⌋₊).1:ℝ)/M
    let sshift := fun y : ℝ => ((pick ⌊(k:ℝ)*y⌋₊).2:ℝ)/M
    let Bint := fun y : ℝ =>
      ((a+(L-(pick ⌊(k:ℝ)*y⌋₊).1-(pick ⌊(k:ℝ)*y⌋₊).2):ℕ):ℤ)
    Y.card≤k ∧
      (∀ y∈Y, y∈Icc (1:ℝ) 2) ∧
      (∀ y∈Y, ∀ z∈Y, y≠z → 1≤(k:ℝ)*|y-z|) ∧
      (∀ y∈Y, 0<rshift y ∧ 0<sshift y ∧
        rshift y*sshift y=((k:ℝ)/M^2)*y ∧ rshift y+sshift y≤((H:ℝ)+K)/M) ∧
      ⌈M⌉≤(a:ℤ) ∧ (∀ y∈Y, (a:ℤ)≤Bint y) ∧
      (∀ y∈Y, Bint y≤⌊2*M⌋) ∧
      (∑ l∈Block,‖∑ j∈Finset.range (L+1-(pick l).1-(pick l).2),
        (𝐞 (X*(F (((a:ℝ)+j)/M)-F (((a:ℝ)+j+(pick l).1)/M)-
          F (((a:ℝ)+j+(pick l).2)/M)+
          F (((a:ℝ)+j+(pick l).1+(pick l).2)/M))):ℂ)‖) ≤
        (Y.card:ℝ)+∑ y∈Y,‖∑ j∈Finset.Ioc (a:ℤ) (Bint y),
          (𝐞 ((X*k/M^2)*(F ((j:ℝ)/M)-F ((j:ℝ)/M+rshift y)-
            F ((j:ℝ)/M+sshift y)+F ((j:ℝ)/M+rshift y+sshift y))/
              ((k:ℝ)/M^2)):ℂ)‖ := by
  exact double_difference_product_dyadic_actual_family F X hM a L H K k hk ha hb

#print axioms double_difference_product_dyadic_actual_family

/-- The SAME original-model extension supplies the literal product-block
twelfth moment. The actual family and intervals are constructed internally,
and their endpoint loss is absorbed by the existing physical error terms. -/
private theorem approximateModelPhase_enlarged_double_product_correlation_moment
    {σ ε : ℝ} (hσ : 0<σ) (hε : 0<ε) :
    ∃ δ w₀ B C : ℝ, 0<δ ∧ 0<w₀ ∧ w₀≤1/4 ∧ 1≤B ∧ 1≤C ∧
      ∀ (M : ℝ) (F : ℝ → ℝ), 1≤M →
        Expdb.IsApproximateModelPhaseFunction F σ 7 δ →
      ∃ Fext : ℝ → ℝ,
        (∀ (X : ℝ) (a b : ℕ), M≤(a:ℝ) → (b:ℝ)≤2*M →
          ‖Expdb.exponentialSumAt F X M a b-
            Expdb.exponentialSumAt Fext X M a b‖≤6) ∧
        ∀ (X : ℝ) (n N a L H K k : ℕ) (R : ℝ),
          C≤X*k/M^2 → N=8*n → 2≤N → B≤R → 0<k →
          ((H:ℝ)+K)/M≤w₀ → (k:ℝ)≤M → (((H:ℝ)+K)/M)*(k:ℝ)≤1 →
          M≤(a:ℝ) → ((a+L:ℕ):ℝ)≤2*M →
          (X*k/M^2)*(N:ℝ)*R^2=M^3 →
          B*R≤N → B*(N:ℝ)≤R^2 → B*(N:ℝ)≤M →
          B*(N:ℝ)^3≤M*R^2 → B*(N:ℝ)*R≤M →
          B*M≤(N:ℝ)*R^2 → B*M≤X*k/M^2 → B*R^2≤X*k/M^2 →
          B*(N:ℝ)^10≤M^3*R^7 →
          let Pairs := (Finset.Icc 1 (H-1)) ×ˢ (Finset.Icc 1 (K-1))
          let Products := Pairs.image (fun p => p.1*p.2)
          ∀ pick : ℕ → ℕ × ℕ,
            (∀ l∈Products, pick l∈Pairs ∧ (pick l).1*(pick l).2=l) →
          let J := (k:ℝ)
          let E := J*M/Real.sqrt (N:ℝ)+J*M*R^2/(N:ℝ)^2+
            J*(N:ℝ)^2*R^2/M+J*(N:ℝ)*((N:ℝ)/R)^((2:ℝ)/3)
          let Main := J^11*M^10*(N:ℝ)^2/R^4+J^11*M^11*(N:ℝ)^2/R^7+
            J^11*J*M^10/R^2+J^11*J*M^11/R^5+
            J^12*M^10*R^2/(N:ℝ)^2*(R/(N:ℝ))^((2:ℝ)/3)*
              ((X*k/M^2)/M^2)^((4:ℝ)/3)
          (∑ l∈(Finset.Ico k (2*k)).filter (fun l => l∈Products),
            ‖∑ j∈Finset.range (L+1-(pick l).1-(pick l).2),
              (𝐞 (X*(Fext (((a:ℝ)+j)/M)-Fext (((a:ℝ)+j+(pick l).1)/M)-
                Fext (((a:ℝ)+j+(pick l).2)/M)+
                Fext (((a:ℝ)+j+(pick l).1+(pick l).2)/M))):ℂ)‖)^12 ≤
            C*(X*k/M^2)^ε*(Main+E^12) := by
  classical
  obtain ⟨δ,w₀,B,C₀,hδ,hw₀,hwcap,hB,hC₀,hsource⟩ :=
    approximateModelPhase_enlarged_double_capped_quantitative hσ hε
  let C := (2:ℝ)^12*C₀
  have hCC₀ : C₀≤C := le_mul_of_one_le_left (zero_le_one.trans hC₀) (by norm_num)
  have hC : 1≤C := hC₀.trans hCC₀
  refine ⟨δ,w₀,B,C,hδ,hw₀,hwcap,hB,hC,?_⟩
  intro M F hM hF
  obtain ⟨Fext,hsharp,hupper⟩ := hsource M F hM hF
  refine ⟨Fext,hsharp,?_⟩
  intro X n N a L H K k R hT hN8 hN2 hR hk hWcap hJM hWJ ha hb hphase
    hRN hNR hNM hCubic hCap hHeight hMT hRT hTen Pairs Products pick hpick J E Main
  have hMp := zero_lt_one.trans_le hM
  have hNp : (0:ℝ)<N := by exact_mod_cast (show 0<N by omega)
  have hN1 : (1:ℝ)≤N := by exact_mod_cast (show 1≤N by omega)
  have hRp := zero_lt_one.trans_le (hB.trans hR)
  have hJp : 0<J := by
    change (0:ℝ)<k
    exact_mod_cast hk
  let T := X*k/M^2
  have hT1 : 1≤T := hC.trans hT
  have hTp := zero_lt_one.trans_le hT1
  let Block := (Finset.Ico k (2*k)).filter (fun l => l∈Products)
  let Kept := Block.filter (fun l => (pick l).1+(pick l).2≤L)
  let Y := Kept.image (fun l : ℕ => (l:ℝ)/(k:ℝ))
  let rshift := fun y : ℝ => ((pick ⌊(k:ℝ)*y⌋₊).1:ℝ)/M
  let sshift := fun y : ℝ => ((pick ⌊(k:ℝ)*y⌋₊).2:ℝ)/M
  let Bint := fun y : ℝ =>
    ((a+(L-(pick ⌊(k:ℝ)*y⌋₊).1-(pick ⌊(k:ℝ)*y⌋₊).2):ℕ):ℤ)
  obtain ⟨hcard,hY,hsep,hshifts,hA,hAB,hBint,hcorr⟩ :=
    double_difference_product_dyadic_actual_family Fext X hMp a L H K k hk ha hb pick hpick
  have hY0 : (0:ℝ)≤Y.card := Nat.cast_nonneg _
  have hYJ : (Y.card:ℝ)≤J := by
    change (Y.card:ℝ)≤(k:ℝ)
    exact_mod_cast hcard
  let EY := (Y.card:ℝ)*M/Real.sqrt (N:ℝ)+(Y.card:ℝ)*M*R^2/(N:ℝ)^2+
    (Y.card:ℝ)*(N:ℝ)^2*R^2/M+(Y.card:ℝ)*(N:ℝ)*((N:ℝ)/R)^((2:ℝ)/3)
  let MainY := (Y.card:ℝ)^11*M^10*(N:ℝ)^2/R^4+
    (Y.card:ℝ)^11*M^11*(N:ℝ)^2/R^7+
    (Y.card:ℝ)^11*J*M^10/R^2+(Y.card:ℝ)^11*J*M^11/R^5+
    (Y.card:ℝ)^12*M^10*R^2/(N:ℝ)^2*(R/(N:ℝ))^((2:ℝ)/3)*(T/M^2)^((4:ℝ)/3)
  have hEY : EY≤E := by
    have hh := double_difference_capped_radius_error_bound hY0 hYJ hMp hNp hRp hRp
      (show (1:ℝ)≤1 from le_rfl) (by rw [one_mul]) (by rw [one_mul])
    simpa only [one_pow,one_mul] using hh
  have hMY : MainY≤Main := by
    have hh := double_difference_capped_radius_main_bound hY0 hYJ hMp hNp hRp hRp
      (show (1:ℝ)≤1 from le_rfl) hJp.le hTp hTp
      (by rw [one_mul]) (by rw [one_mul]) (by rw [one_mul])
    simpa only [one_pow,one_mul] using hh
  have hEY0 : 0≤EY := by
    dsimp only [EY]
    clear * - hY0 hMp hNp hRp
    positivity
  have hE0 : 0≤E := by
    dsimp only [E]
    clear * - hJp hMp hNp hRp
    positivity
  have hMain0 : 0≤Main := by
    dsimp only [Main]
    change 0≤J^11*M^10*(N:ℝ)^2/R^4+J^11*M^11*(N:ℝ)^2/R^7+
      J^11*J*M^10/R^2+J^11*J*M^11/R^5+
      J^12*M^10*R^2/(N:ℝ)^2*(R/(N:ℝ))^((2:ℝ)/3)*(T/M^2)^((4:ℝ)/3)
    clear * - hJp hMp hNp hRp hTp
    positivity
  have hMass0 : 0≤Main+E^12 := add_nonneg hMain0 (pow_nonneg hE0 12)
  have hMass : MainY+EY^12≤Main+E^12 :=
    add_le_add hMY (pow_le_pow_left₀ hEY0 hEY 12)
  let Z := ∑ y∈Y,‖∑ j∈Finset.Ioc (a:ℤ) (Bint y),
    (𝐞 (T*(Fext ((j:ℝ)/M)-Fext ((j:ℝ)/M+rshift y)-
      Fext ((j:ℝ)/M+sshift y)+Fext ((j:ℝ)/M+rshift y+sshift y))/
        ((k:ℝ)/M^2)):ℂ)‖
  have hZ0 : 0≤Z := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  have hZ : Z^12≤C₀*T^ε*(Main+E^12) := by
    have hW : 0≤((H:ℝ)+K)/M := div_nonneg (by positivity) hMp.le
    have hu := hupper T Y rshift sshift n N R J ((k:ℝ)/M^2) (((H:ℝ)+K)/M)
      (hCC₀.trans hT) hN8 hN2 hR (div_pos hJp (sq_pos_of_pos hMp)) hW hWcap hJp hJM hWJ
      hY hsep hshifts hphase hRN hNR hNM hCubic hCap hHeight hMT hRT hTen
      (fun _ => (a:ℤ)) Bint (fun _ _ => hA) hAB hBint
    exact hu.trans (mul_le_mul_of_nonneg_left hMass
      (mul_nonneg (zero_le_one.trans hC₀) (Real.rpow_nonneg hTp.le ε)))
  have hQ : 1≤C₀*T^ε := by
    calc
      _ = (1:ℝ)*1 := by norm_num
      _ ≤ _ := mul_le_mul hC₀ (Real.one_le_rpow hT1 hε.le)
        zero_le_one (zero_le_one.trans hC₀)
  have hRleN : R≤(N:ℝ) := (le_mul_of_one_le_left hRp.le hB).trans hRN
  have hJE : J≤E := by
    have hratio : 1≤(N:ℝ)/R := (one_le_div hRp).mpr hRleN
    have hp : 1≤((N:ℝ)/R)^((2:ℝ)/3) := Real.one_le_rpow hratio (by norm_num)
    have hu : 1≤(N:ℝ)*((N:ℝ)/R)^((2:ℝ)/3) := one_le_mul_of_one_le_of_one_le hN1 hp
    have hlast : J≤J*(N:ℝ)*((N:ℝ)/R)^((2:ℝ)/3) := by
      simpa only [mul_assoc] using le_mul_of_one_le_right hJp.le hu
    have hother : 0≤J*M/Real.sqrt (N:ℝ)+J*M*R^2/(N:ℝ)^2+
        J*(N:ℝ)^2*R^2/M := by
      clear * - hJp hMp hNp hRp
      positivity
    exact hlast.trans (le_add_of_nonneg_left hother)
  have hJpow : J^12≤C₀*T^ε*(Main+E^12) :=
    ((pow_le_pow_left₀ hJp.le hJE 12).trans (le_add_of_nonneg_left hMain0)).trans
      (le_mul_of_one_le_left hMass0 hQ)
  have hCorr :
      (∑ l∈Block,‖∑ j∈Finset.range (L+1-(pick l).1-(pick l).2),
        (𝐞 (X*(Fext (((a:ℝ)+j)/M)-Fext (((a:ℝ)+j+(pick l).1)/M)-
          Fext (((a:ℝ)+j+(pick l).2)/M)+
          Fext (((a:ℝ)+j+(pick l).1+(pick l).2)/M))):ℂ)‖)≤J+Z :=
    hcorr.trans (add_le_add hYJ le_rfl)
  calc
    _ ≤ (J+Z)^12 :=
      pow_le_pow_left₀ (Finset.sum_nonneg (fun _ _ => norm_nonneg _)) hCorr 12
    _ ≤ (2:ℝ)^11*(J^12+Z^12) := add_pow_le hJp.le hZ0 12
    _ ≤ (2:ℝ)^11*(C₀*T^ε*(Main+E^12)+C₀*T^ε*(Main+E^12)) :=
      mul_le_mul_of_nonneg_left (add_le_add hJpow hZ) (by norm_num)
    _ = _ := by
      rw [←two_mul]
      dsimp only [C]
      rw [show (2:ℝ)^12=2^11*2 from pow_succ 2 11]
      ac_rfl

example
    {σ ε : ℝ} (hσ : 0<σ) (hε : 0<ε) :
    ∃ δ w₀ B C : ℝ, 0<δ ∧ 0<w₀ ∧ w₀≤1/4 ∧ 1≤B ∧ 1≤C ∧
      ∀ (M : ℝ) (F : ℝ → ℝ), 1≤M →
        Expdb.IsApproximateModelPhaseFunction F σ 7 δ →
      ∃ Fext : ℝ → ℝ,
        (∀ (X : ℝ) (a b : ℕ), M≤(a:ℝ) → (b:ℝ)≤2*M →
          ‖Expdb.exponentialSumAt F X M a b-
            Expdb.exponentialSumAt Fext X M a b‖≤6) ∧
        ∀ (X : ℝ) (n N a L H K k : ℕ) (R : ℝ),
          C≤X*k/M^2 → N=8*n → 2≤N → B≤R → 0<k →
          ((H:ℝ)+K)/M≤w₀ → (k:ℝ)≤M → (((H:ℝ)+K)/M)*(k:ℝ)≤1 →
          M≤(a:ℝ) → ((a+L:ℕ):ℝ)≤2*M →
          (X*k/M^2)*(N:ℝ)*R^2=M^3 →
          B*R≤N → B*(N:ℝ)≤R^2 → B*(N:ℝ)≤M →
          B*(N:ℝ)^3≤M*R^2 → B*(N:ℝ)*R≤M →
          B*M≤(N:ℝ)*R^2 → B*M≤X*k/M^2 → B*R^2≤X*k/M^2 →
          B*(N:ℝ)^10≤M^3*R^7 →
          let Pairs := (Finset.Icc 1 (H-1)) ×ˢ (Finset.Icc 1 (K-1))
          let Products := Pairs.image (fun p => p.1*p.2)
          ∀ pick : ℕ → ℕ × ℕ,
            (∀ l∈Products, pick l∈Pairs ∧ (pick l).1*(pick l).2=l) →
          let J := (k:ℝ)
          let E := J*M/Real.sqrt (N:ℝ)+J*M*R^2/(N:ℝ)^2+
            J*(N:ℝ)^2*R^2/M+J*(N:ℝ)*((N:ℝ)/R)^((2:ℝ)/3)
          let Main := J^11*M^10*(N:ℝ)^2/R^4+J^11*M^11*(N:ℝ)^2/R^7+
            J^11*J*M^10/R^2+J^11*J*M^11/R^5+
            J^12*M^10*R^2/(N:ℝ)^2*(R/(N:ℝ))^((2:ℝ)/3)*
              ((X*k/M^2)/M^2)^((4:ℝ)/3)
          (∑ l∈(Finset.Ico k (2*k)).filter (fun l => l∈Products),
            ‖∑ j∈Finset.range (L+1-(pick l).1-(pick l).2),
              (𝐞 (X*(Fext (((a:ℝ)+j)/M)-Fext (((a:ℝ)+j+(pick l).1)/M)-
                Fext (((a:ℝ)+j+(pick l).2)/M)+
                Fext (((a:ℝ)+j+(pick l).1+(pick l).2)/M))):ℂ)‖)^12 ≤
            C*(X*k/M^2)^ε*(Main+E^12) := by
  exact approximateModelPhase_enlarged_double_product_correlation_moment hσ hε

#print axioms approximateModelPhase_enlarged_double_product_correlation_moment

/-- Exact scale-linked integer powers for all five main terms and all four
errors. The physical relation includes the actual double-shift height X*J/M^2. -/
private theorem double_difference_capped_integer_moments
    {X M N J R : ℝ} (hX : 0<X) (hM : 0<M) (hN : 0<N)
    (hJ : 0<J) (hR : 0<R) (hscale : (X*J/M^2)*N*R^2=M^3) :
    (J*M/Real.sqrt N)^72=J^72*M^72/N^36 ∧
    (J*M*R^2/N^2)^72=M^432/(X^72*N^216) ∧
    (J*N^2*R^2/M)^72=M^288*N^72/X^72 ∧
    (J*N*(N/R)^((2:ℝ)/3))^72=X^24*J^96*N^144/M^120 ∧
    (J^11*M^10*N^2/R^4)^6=X^12*J^78*N^24 ∧
    (J^11*M^11*N^2/R^7)^6=X^21*J^87*N^33/M^39 ∧
    (J^11*J*M^10/R^2)^6=X^6*J^78*M^30*N^6 ∧
    (J^11*J*M^11/R^5)^6=X^15*J^87*N^15/M^9 ∧
    (J^12*M^10*R^2/N^2*(R/N)^((2:ℝ)/3)*
      ((X*J/M^2)/M^2)^((4:ℝ)/3))^6=J^72*M^68/N^24 := by
  have hR2 : R^2=M^5/(X*J*N) := by
    apply (eq_div_iff (mul_ne_zero (mul_ne_zero hX.ne' hJ.ne') hN.ne')).mpr
    have hs := hscale
    field_simp at hs
    nlinarith only [hs]
  have hSecond : J*M*R^2/N^2=M^6/(X*N^3) := by
    rw [hR2]
    field_simp
  have hThird : J*N^2*R^2/M=M^4*N/X := by
    rw [hR2]
    field_simp
  have hFrac : ((R/N)^((2:ℝ)/3))^6=(R/N)^4 := by
    rw [←Real.rpow_mul_natCast (div_nonneg hR.le hN.le)]
    norm_num
  have hTime : (((X*J/M^2)/M^2)^((4:ℝ)/3))^6=((X*J/M^2)/M^2)^8 := by
    rw [←Real.rpow_mul_natCast (by positivity : 0≤(X*J/M^2)/M^2)]
    norm_num
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · have hsqrt : (Real.sqrt N)^72=N^36 := by
      calc
        _ = ((Real.sqrt N)^2)^36 := by rw [←pow_mul]
        _ = N^36 := by rw [Real.sq_sqrt hN.le]
    rw [div_pow,mul_pow,hsqrt]
  · rw [hSecond]
    simp only [div_pow,mul_pow,←pow_mul]
  · rw [hThird]
    simp only [div_pow,mul_pow,←pow_mul]
  · rw [mul_pow,mul_pow,←Real.rpow_mul_natCast (div_nonneg hN.le hR.le),
      show ((2:ℝ)/3)*((72:ℕ):ℝ)=((48:ℕ):ℝ) by norm_num,
      Real.rpow_natCast,div_pow]
    rw [show R^48=(R^2)^24 by rw [←pow_mul],hR2]
    field_simp
  · simp only [mul_pow,div_pow,←pow_mul]
    rw [show R^24=(R^2)^12 by rw [←pow_mul],hR2]
    field_simp
    ac_rfl
  · simp only [mul_pow,div_pow,←pow_mul]
    rw [show R^42=(R^2)^21 by rw [←pow_mul],hR2]
    field_simp
    ac_rfl
  · simp only [mul_pow,div_pow,←pow_mul]
    rw [show R^12=(R^2)^6 by rw [←pow_mul],hR2]
    field_simp
  · simp only [mul_pow,div_pow,←pow_mul]
    rw [show R^30=(R^2)^15 by rw [←pow_mul],hR2]
    field_simp
  · rw [mul_pow,mul_pow,hFrac,hTime]
    simp only [mul_pow,div_pow,←pow_mul]
    rw [show R^12=(R^2)^6 by rw [←pow_mul],
      show R^4=(R^2)^2 by rw [←pow_mul],hR2]
    field_simp
    ring

example
    {X M N J R : ℝ} (hX : 0<X) (hM : 0<M) (hN : 0<N)
    (hJ : 0<J) (hR : 0<R) (hscale : (X*J/M^2)*N*R^2=M^3) :
    (J*M/Real.sqrt N)^72=J^72*M^72/N^36 ∧
    (J*M*R^2/N^2)^72=M^432/(X^72*N^216) ∧
    (J*N^2*R^2/M)^72=M^288*N^72/X^72 ∧
    (J*N*(N/R)^((2:ℝ)/3))^72=X^24*J^96*N^144/M^120 ∧
    (J^11*M^10*N^2/R^4)^6=X^12*J^78*N^24 ∧
    (J^11*M^11*N^2/R^7)^6=X^21*J^87*N^33/M^39 ∧
    (J^11*J*M^10/R^2)^6=X^6*J^78*M^30*N^6 ∧
    (J^11*J*M^11/R^5)^6=X^15*J^87*N^15/M^9 ∧
    (J^12*M^10*R^2/N^2*(R/N)^((2:ℝ)/3)*
      ((X*J/M^2)/M^2)^((4:ℝ)/3))^6=J^72*M^68/N^24 := by
  exact double_difference_capped_integer_moments hX hM hN hJ hR hscale

#print axioms double_difference_capped_integer_moments

private theorem upperOriginal_three_term_power_bound
    {a b c : ℝ} (ha : 0≤a) (hb : 0≤b) (hc : 0≤c) (n : ℕ) :
    (a+b+c)^n≤(2:ℝ)^(2*n)*(a^n+b^n+c^n) := by
  let D := (2:ℝ)^(n-1)
  have hD : 1≤D := one_le_pow₀ (by norm_num)
  have hD0 := zero_le_one.trans hD
  have hDpow : D^2≤(2:ℝ)^(2*n) := by
    dsimp only [D]
    rw [←pow_mul]
    exact pow_le_pow_right₀ (by norm_num) (by omega)
  calc
    _ ≤ D*((a+b)^n+c^n) := add_pow_le (add_nonneg ha hb) hc n
    _ ≤ D*(D*(a^n+b^n)+D*c^n) :=
      mul_le_mul_of_nonneg_left
        (add_le_add (add_pow_le ha hb n)
          (le_mul_of_one_le_left (pow_nonneg hc n) hD)) hD0
    _ = D^2*(a^n+b^n+c^n) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hDpow
      (add_nonneg (add_nonneg (pow_nonneg ha n) (pow_nonneg hb n)) (pow_nonneg hc n))

example
    {a b c : ℝ} (ha : 0≤a) (hb : 0≤b) (hc : 0≤c) (n : ℕ) :
    (a+b+c)^n≤(2:ℝ)^(2*n)*(a^n+b^n+c^n) := by
  exact upperOriginal_three_term_power_bound ha hb hc n

#print axioms upperOriginal_three_term_power_bound

private theorem middleOriginal_five_term_power_bound
    {a b c d e : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hd : 0 ≤ d) (he : 0 ≤ e) (n : ℕ) :
    (a+b+c+d+e)^n ≤ (2:ℝ)^(4*n)*(a^n+b^n+c^n+d^n+e^n) := by
  let D := (2:ℝ)^(2*n)
  have hD : 1 ≤ D := one_le_pow₀ (by norm_num)
  have hD0 := zero_le_one.trans hD
  have habc := upperOriginal_three_term_power_bound ha hb hc n
  have habc0 : 0 ≤ a+b+c := add_nonneg (add_nonneg ha hb) hc
  calc
    _ ≤ D*((a+b+c)^n+d^n+e^n) := upperOriginal_three_term_power_bound habc0 hd he n
    _ ≤ D*(D*(a^n+b^n+c^n)+D*d^n+D*e^n) :=
      mul_le_mul_of_nonneg_left
        (add_le_add
          (add_le_add habc (le_mul_of_one_le_left (pow_nonneg hd n) hD))
          (le_mul_of_one_le_left (pow_nonneg he n) hD)) hD0
    _ = (D*D)*(a^n+b^n+c^n+d^n+e^n) := by ring
    _ = _ := by
      dsimp only [D]
      rw [←pow_add]
      congr 2
      omega

example
    {a b c d e : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hd : 0 ≤ d) (he : 0 ≤ e) (n : ℕ) :
    (a+b+c+d+e)^n ≤ (2:ℝ)^(4*n)*(a^n+b^n+c^n+d^n+e^n) := by
  exact middleOriginal_five_term_power_bound ha hb hc hd he n

#print axioms middleOriginal_five_term_power_bound

private theorem upperOriginal_nonnegative_doubled_block_selection
    (f : ℕ → ℝ) (H : ℕ) (hH : 2 ≤ H) (hf₀ : f 0=0)
    (hf : ∀ n, 0 ≤ f n) {A : ℝ} (hA : 0 ≤ A)
    (hcap : ∀ n < H, f n ≤ A) :
    ∃ k : ℕ, 0 < k ∧ 2*k ≤ H ∧
      (∑ n∈Finset.range H,f n) ≤
        (Nat.clog 2 H:ℝ)*(A+∑ j∈Finset.range k,f (k+j)) := by
  classical
  obtain ⟨k,hk,hmax⟩ := (Finset.Icc 1 (H/2)).exists_max_image
    (fun k => ∑ j∈Finset.range k,f (k+j))
    (by exact ⟨1,Finset.mem_Icc.mpr ⟨le_rfl,by omega⟩⟩)
  have hk' := Finset.mem_Icc.mp hk
  have hnorm (s : Finset ℕ) (g : ℕ → ℕ) :
      ‖∑ j∈s,(f (g j):ℂ)‖=∑ j∈s,f (g j) := by
    rw [←Complex.ofReal_sum]
    exact Complex.norm_of_nonneg (Finset.sum_nonneg (fun j _ => hf (g j)))
  have hbound := norm_prefix_le_doubled_blocks
    (fun n => (f n:ℂ)) H (Nat.clog 2 H) H
    (congrArg (fun x : ℝ => (x:ℂ)) hf₀) le_rfl (Nat.le_pow_clog (by norm_num) H)
    A (∑ j∈Finset.range k,f (k+j)) hA
    (Finset.sum_nonneg (fun j _ => hf (k+j)))
    (fun n hn => (Complex.norm_of_nonneg (hf n)).le.trans (hcap n hn))
    (fun l hl hlH => by
      rw [hnorm (Finset.range l) (fun j => l+j)]
      exact hmax l (Finset.mem_Icc.mpr ⟨by omega,by omega⟩))
  have he : ‖∑ n∈Finset.range H,(f n:ℂ)‖ = ∑ n∈Finset.range H,f n :=
    hnorm (Finset.range H) id
  rw [he] at hbound
  exact ⟨k,by omega,by omega,hbound⟩

example
    (f : ℕ → ℝ) (H : ℕ) (hH : 2 ≤ H) (hf₀ : f 0=0)
    (hf : ∀ n, 0 ≤ f n) {A : ℝ} (hA : 0 ≤ A)
    (hcap : ∀ n < H, f n ≤ A) :
    ∃ k : ℕ, 0 < k ∧ 2*k ≤ H ∧
      (∑ n∈Finset.range H,f n) ≤
        (Nat.clog 2 H:ℝ)*(A+∑ j∈Finset.range k,f (k+j)) := by
  exact upperOriginal_nonnegative_doubled_block_selection f H hH hf₀ hf hA hcap

#print axioms upperOriginal_nonnegative_doubled_block_selection


/-- The ACTUAL two-step Weyl reduction chooses a product block without
identifying phases in a fiber. The block is the same one accepted by the
source-derived product-family twelfth-moment consumer. -/
private theorem source_product_twice_weyl_doubled_block
    {ε : ℝ} (hε : 0<ε) :
    ∃ D : ℝ, 0<D ∧
      ∀ (F : ℝ → ℝ) (σ X M : ℝ) (a L H K : ℕ),
        0<σ → 2≤H → 2≤K → H+K≤a →
        H≤L+1 → K≤L+1 → (H:ℝ)+K<M →
        let Pairs := (Finset.Icc 1 (H-1)) ×ˢ (Finset.Icc 1 (K-1))
        let Products := Pairs.image (fun p => p.1*p.2)
        let W := fun p : ℕ × ℕ => ∑ j∈Finset.range (L+1-p.1-p.2),
          (𝐞 (X*(F (((a:ℝ)+j)/M)-F (((a:ℝ)+j+p.1)/M)-
            F (((a:ℝ)+j+p.2)/M)+F (((a:ℝ)+j+p.1+p.2)/M))):ℂ)
        ∃ (pick : ℕ → ℕ × ℕ) (k : ℕ), 0<k ∧ 2*k≤H*K ∧
          (∀ l∈Products, pick l∈Pairs ∧ (pick l).1*(pick l).2=l ∧
            ∀ p∈Pairs, p.1*p.2=l → ‖W p‖≤‖W (pick l)‖) ∧
          (H:ℝ)^2*K*‖Expdb.exponentialSumAt F X M a (a+L)‖^4 ≤
            8*K*((L:ℝ)+1)^4+64*(H:ℝ)^2*((L:ℝ)+1)^4+
              128*H*((L:ℝ)+1)^3*
                (D*((H:ℝ)*K)^ε*((Nat.clog 2 (H*K):ℝ)*
                  ((L:ℝ)+1+∑ l∈(Finset.Ico k (2*k)).filter (fun l => l∈Products),
                    ‖W (pick l)‖))) := by
  classical
  obtain ⟨D,hD,hsource⟩ := source_product_twice_weyl hε
  refine ⟨D,hD,?_⟩
  intro F σ X M a L H K hσ hH hK hHa hHL hKL hM Pairs Products W
  obtain ⟨pick,hpick,hweyl⟩ := hsource F σ X M a L H K hσ
    (by omega) (by omega) hHa hHL hKL hM
  have hbounds (p : ℕ × ℕ) (hp : p∈Pairs) :
      0<p.1 ∧ p.1<H ∧ 0<p.2 ∧ p.2<K := by
    obtain ⟨hr,hs⟩ := Finset.mem_product.mp hp
    obtain ⟨hr1,hrH⟩ := Finset.mem_Icc.mp hr
    obtain ⟨hs1,hsK⟩ := Finset.mem_Icc.mp hs
    omega
  have hproduct (l : ℕ) (hl : l∈Products) : 0<l ∧ l<H*K := by
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hl
    obtain ⟨hr,hrH,hs,hsK⟩ := hbounds p hp
    refine ⟨Nat.mul_pos hr hs,?_⟩
    exact (Nat.mul_lt_mul_of_pos_right hrH hs).trans_le (Nat.mul_le_mul_left H hsK.le)
  have hWcap (p : ℕ × ℕ) : ‖W p‖≤(L:ℝ)+1 := by
    calc
      _ ≤ ∑ j∈Finset.range (L+1-p.1-p.2),
          ‖(𝐞 (X*(F (((a:ℝ)+j)/M)-F (((a:ℝ)+j+p.1)/M)-
            F (((a:ℝ)+j+p.2)/M)+F (((a:ℝ)+j+p.1+p.2)/M))):ℂ)‖ := norm_sum_le _ _
      _ = (L+1-p.1-p.2:ℕ) := by simp
      _ ≤ (L:ℝ)+1 := by exact_mod_cast (show L+1-p.1-p.2≤L+1 by omega)
  let f := fun l => if l∈Products then ‖W (pick l)‖ else 0
  have hf0 : f 0=0 := if_neg (by
    intro hh
    exact (Nat.lt_irrefl 0) (hproduct 0 hh).1)
  have hf (l : ℕ) : 0≤f l := by
    dsimp only [f]
    split_ifs
    · exact norm_nonneg _
    · exact le_rfl
  have hfCap (l : ℕ) : f l≤(L:ℝ)+1 := by
    dsimp only [f]
    split_ifs
    · exact hWcap _
    · positivity
  have hHK : 2≤H*K := by nlinarith only [hH,hK]
  obtain ⟨k,hk,hkHK,hselected⟩ :=
    upperOriginal_nonnegative_doubled_block_selection f (H*K) hHK hf0 hf
      (by positivity : 0≤(L:ℝ)+1) (fun l _ => hfCap l)
  have hFilter : (Finset.range (H*K)).filter (fun l => l∈Products)=Products := by
    ext l
    simp only [Finset.mem_filter,Finset.mem_range]
    exact ⟨fun hh => hh.2,fun hl => ⟨(hproduct l hl).2,hl⟩⟩
  have hAll : (∑ l∈Products,‖W (pick l)‖)=∑ l∈Finset.range (H*K),f l := by
    calc
      _ = ∑ l∈(Finset.range (H*K)).filter (fun l => l∈Products),‖W (pick l)‖ :=
        congrArg (fun S : Finset ℕ => ∑ l∈S,‖W (pick l)‖) hFilter.symm
      _ = _ := by rw [Finset.sum_filter]
  have hRange :
      (∑ j∈Finset.range k,f (k+j))=∑ l∈Finset.Ico k (2*k),f l := by
    apply Finset.sum_bij (fun (j:ℕ) _ => k+j)
    case hi =>
      intro j hj
      have hj' := Finset.mem_range.mp hj
      exact Finset.mem_Ico.mpr ⟨by omega,by omega⟩
    case i_inj =>
      intro j _ l _ hjl
      omega
    case i_surj =>
      intro l hl
      have hl' := Finset.mem_Ico.mp hl
      exact ⟨l-k,Finset.mem_range.mpr (by omega),by omega⟩
    case h =>
      intro j _
      rfl
  have hBlock :
      (∑ j∈Finset.range k,f (k+j))=
        ∑ l∈(Finset.Ico k (2*k)).filter (fun l => l∈Products),‖W (pick l)‖ := by
    rw [hRange,Finset.sum_filter]
  rw [←hAll,hBlock] at hselected
  refine ⟨pick,k,hk,hkHK,hpick,?_⟩
  exact hweyl.trans (add_le_add le_rfl
    (mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left hselected
        (mul_nonneg hD.le (Real.rpow_nonneg (by positivity) ε)))
      (by positivity)))

example
    {ε : ℝ} (hε : 0<ε) :
    ∃ D : ℝ, 0<D ∧
      ∀ (F : ℝ → ℝ) (σ X M : ℝ) (a L H K : ℕ),
        0<σ → 2≤H → 2≤K → H+K≤a →
        H≤L+1 → K≤L+1 → (H:ℝ)+K<M →
        let Pairs := (Finset.Icc 1 (H-1)) ×ˢ (Finset.Icc 1 (K-1))
        let Products := Pairs.image (fun p => p.1*p.2)
        let W := fun p : ℕ × ℕ => ∑ j∈Finset.range (L+1-p.1-p.2),
          (𝐞 (X*(F (((a:ℝ)+j)/M)-F (((a:ℝ)+j+p.1)/M)-
            F (((a:ℝ)+j+p.2)/M)+F (((a:ℝ)+j+p.1+p.2)/M))):ℂ)
        ∃ (pick : ℕ → ℕ × ℕ) (k : ℕ), 0<k ∧ 2*k≤H*K ∧
          (∀ l∈Products, pick l∈Pairs ∧ (pick l).1*(pick l).2=l ∧
            ∀ p∈Pairs, p.1*p.2=l → ‖W p‖≤‖W (pick l)‖) ∧
          (H:ℝ)^2*K*‖Expdb.exponentialSumAt F X M a (a+L)‖^4 ≤
            8*K*((L:ℝ)+1)^4+64*(H:ℝ)^2*((L:ℝ)+1)^4+
              128*H*((L:ℝ)+1)^3*
                (D*((H:ℝ)*K)^ε*((Nat.clog 2 (H*K):ℝ)*
                  ((L:ℝ)+1+∑ l∈(Finset.Ico k (2*k)).filter (fun l => l∈Products),
                    ‖W (pick l)‖))) := by
  exact source_product_twice_weyl_doubled_block hε

#print axioms source_product_twice_weyl_doubled_block

/-- The actual physical nine-term moment becomes the nine scale-linked
monomials used in the fourth-pair worksheet, with the two-step Weyl weight. -/
private theorem double_difference_weighted_capped_integer_moments
    {X M N J H R : ℝ} (hX : 0<X) (hM : 0<M) (hN : 0<N)
    (hJ : 0<J) (hH : 0<H) (hR : 0<R) (hscale : (X*J/M^2)*N*R^2=M^3) :
    let E := J*M/Real.sqrt N+J*M*R^2/N^2+J*N^2*R^2/M+
      J*N*(N/R)^((2:ℝ)/3)
    let Main := J^11*M^10*N^2/R^4+J^11*M^11*N^2/R^7+
      J^11*J*M^10/R^2+J^11*J*M^11/R^5+
      J^12*M^10*R^2/N^2*(R/N)^((2:ℝ)/3)*((X*J/M^2)/M^2)^((4:ℝ)/3)
    (M^3/H^3)^72*(E^72+Main^6) ≤ (2:ℝ)^288*
      ((J^72*M^288/(H^216*N^36)+M^648/(X^72*H^216*N^216)+
        M^504*N^72/(X^72*H^216)+X^24*J^96*M^96*N^144/H^216)+
        (X^12*J^78*M^216*N^24/H^216+X^21*J^87*M^177*N^33/H^216+
          X^6*J^78*M^246*N^6/H^216+X^15*J^87*M^207*N^15/H^216+
          J^72*M^284/(H^216*N^24))) := by
  intro E Main
  let e₁ := J*M/Real.sqrt N
  let e₂ := J*M*R^2/N^2
  let e₃ := J*N^2*R^2/M
  let e₄ := J*N*(N/R)^((2:ℝ)/3)
  let a₁ := J^11*M^10*N^2/R^4
  let a₂ := J^11*M^11*N^2/R^7
  let a₃ := J^11*J*M^10/R^2
  let a₄ := J^11*J*M^11/R^5
  let a₅ := J^12*M^10*R^2/N^2*(R/N)^((2:ℝ)/3)*((X*J/M^2)/M^2)^((4:ℝ)/3)
  have he₁ : 0≤e₁ := by dsimp only [e₁]; positivity
  have he₂ : 0≤e₂ := by dsimp only [e₂]; positivity
  have he₃ : 0≤e₃ := by dsimp only [e₃]; positivity
  have he₄ : 0≤e₄ := by dsimp only [e₄]; positivity
  have ha₁ : 0≤a₁ := by dsimp only [a₁]; positivity
  have ha₂ : 0≤a₂ := by dsimp only [a₂]; positivity
  have ha₃ : 0≤a₃ := by dsimp only [a₃]; positivity
  have ha₄ : 0≤a₄ := by dsimp only [a₄]; positivity
  have ha₅ : 0≤a₅ := by dsimp only [a₅]; positivity
  have hE : E^72≤(2:ℝ)^288*(e₁^72+e₂^72+e₃^72+e₄^72) := by
    have hh := middleOriginal_five_term_power_bound he₁ he₂ he₃ he₄ (le_refl (0:ℝ)) 72
    rw [add_zero,show (0:ℝ)^72=0 by norm_num,add_zero] at hh
    exact hh
  have hMain : Main^6≤(2:ℝ)^288*(a₁^6+a₂^6+a₃^6+a₄^6+a₅^6) := by
    exact (middleOriginal_five_term_power_bound ha₁ ha₂ ha₃ ha₄ ha₅ 6).trans
      (mul_le_mul_of_nonneg_right
        (pow_le_pow_right₀ (by norm_num : (1:ℝ)≤2) (by norm_num : 4*6≤288))
        (by positivity))
  obtain ⟨h₁,h₂,h₃,h₄,h₅,h₆,h₇,h₈,h₉⟩ :=
    double_difference_capped_integer_moments hX hM hN hJ hR hscale
  have hW : 0≤(M^3/H^3)^72 := pow_nonneg (div_nonneg (pow_nonneg hM.le 3) (pow_nonneg hH.le 3)) 72
  calc
    _ ≤ (M^3/H^3)^72*((2:ℝ)^288*(e₁^72+e₂^72+e₃^72+e₄^72)+
        (2:ℝ)^288*(a₁^6+a₂^6+a₃^6+a₄^6+a₅^6)) :=
      mul_le_mul_of_nonneg_left (add_le_add hE hMain) hW
    _ = (2:ℝ)^288*((M^3/H^3)^72*
        ((e₁^72+e₂^72+e₃^72+e₄^72)+(a₁^6+a₂^6+a₃^6+a₄^6+a₅^6))) := by
      rw [←mul_add]
      ac_rfl
    _ = _ := by
      apply congrArg (fun q : ℝ => (2:ℝ)^288*q)
      dsimp only [e₁,e₂,e₃,e₄,a₁,a₂,a₃,a₄,a₅]
      rw [h₁,h₂,h₃,h₄,h₅,h₆,h₇,h₈,h₉]
      simp only [div_pow,←pow_mul,mul_add]
      field_simp
      ring

example
    {X M N J H R : ℝ} (hX : 0<X) (hM : 0<M) (hN : 0<N)
    (hJ : 0<J) (hH : 0<H) (hR : 0<R) (hscale : (X*J/M^2)*N*R^2=M^3) :
    let E := J*M/Real.sqrt N+J*M*R^2/N^2+J*N^2*R^2/M+
      J*N*(N/R)^((2:ℝ)/3)
    let Main := J^11*M^10*N^2/R^4+J^11*M^11*N^2/R^7+
      J^11*J*M^10/R^2+J^11*J*M^11/R^5+
      J^12*M^10*R^2/N^2*(R/N)^((2:ℝ)/3)*((X*J/M^2)/M^2)^((4:ℝ)/3)
    (M^3/H^3)^72*(E^72+Main^6) ≤ (2:ℝ)^288*
      ((J^72*M^288/(H^216*N^36)+M^648/(X^72*H^216*N^216)+
        M^504*N^72/(X^72*H^216)+X^24*J^96*M^96*N^144/H^216)+
        (X^12*J^78*M^216*N^24/H^216+X^21*J^87*M^177*N^33/H^216+
          X^6*J^78*M^246*N^6/H^216+X^15*J^87*M^207*N^15/H^216+
          J^72*M^284/(H^216*N^24))) := by
  exact double_difference_weighted_capped_integer_moments hX hM hN hJ hH hR hscale

#print axioms double_difference_weighted_capped_integer_moments

/-- A single power-window comparison for the actual source polynomial
budgets and the nine two-step Weyl monomials; both floor losses are explicit. -/
private theorem double_difference_monomial_power_window
    {X M N H J ℓ u ν h g : ℝ} (hX : 1≤X)
    (hMl : X^ℓ≤M) (hMu : M≤X^u)
    (hNl : X^ν/2≤N) (hNu : N≤X^ν)
    (hHl : X^h/2≤H) (hJ : J=X^g)
    (p q r s x t v w z : ℕ) :
    X^p*J^q*M^r*N^s/(X^x*H^t*N^v*M^w*J^z) ≤
      (2:ℝ)^(t+v)*X^((p:ℝ)+q*g+r*u+s*ν-x-t*h-v*ν-w*ℓ-z*g) := by
  have hXp := zero_lt_one.trans_le hX
  have hMp : 0<M := (Real.rpow_pos_of_pos hXp ℓ).trans_le hMl
  have hNp : 0<N := (div_pos (Real.rpow_pos_of_pos hXp ν) (by norm_num)).trans_le hNl
  have hHp : 0<H := (div_pos (Real.rpow_pos_of_pos hXp h) (by norm_num)).trans_le hHl
  rw [hJ]
  calc
    _ ≤ X^p*(X^g)^q*(X^u)^r*(X^ν)^s/
        (X^x*(X^h/2)^t*(X^ν/2)^v*(X^ℓ)^w*(X^g)^z) := by
      gcongr
    _ = (2:ℝ)^(t+v)*(X^p*(X^g)^q*(X^u)^r*(X^ν)^s/
        (X^x*(X^h)^t*(X^ν)^v*(X^ℓ)^w*(X^g)^z)) := by
      rw [div_pow,div_pow,pow_add]
      field_simp
    _ = _ := by
      rw [←Real.rpow_natCast X p,←Real.rpow_natCast X x]
      simp only [←Real.rpow_mul_natCast hXp.le,←Real.rpow_add hXp,←Real.rpow_sub hXp]
      apply congrArg (fun a : ℝ => (2:ℝ)^(t+v)*X^a)
      ring

example
    {X M N H J ℓ u ν h g : ℝ} (hX : 1≤X)
    (hMl : X^ℓ≤M) (hMu : M≤X^u)
    (hNl : X^ν/2≤N) (hNu : N≤X^ν)
    (hHl : X^h/2≤H) (hJ : J=X^g)
    (p q r s x t v w z : ℕ) :
    X^p*J^q*M^r*N^s/(X^x*H^t*N^v*M^w*J^z) ≤
      (2:ℝ)^(t+v)*X^((p:ℝ)+q*g+r*u+s*ν-x-t*h-v*ν-w*ℓ-z*g) := by
  exact double_difference_monomial_power_window hX hMl hMu hNl hNu hHl hJ p q r s x t v w z

#print axioms double_difference_monomial_power_window

/-- The existing exact fourth-pair scale certificate remains strict throughout
a genuine two-sided M power window. This also proves the small-product trivial
bound and short-interval bound required by the actual Weyl reduction. -/
private theorem fourth_pair_capped_full_window_margins
    {t u : ℝ} (ht : t∈Icc (0:ℝ) 1) (hu : u∈Icc (0:ℝ) 1) :
    let α := (1-t)*(890/3277)+t*(17604372/60424193)
    let h := ((1-t)*2749411+t*3296917)/100000000
    let g₀ := ((1-t)*16756+t*1976824)/100000000
    let ν₀ := ((1-t)*11931645+t*14567321)/100000000
    let ν₁ := ((1-t)*11969967+t*14925729)/100000000
    let g := (1-u)*g₀+u*(3*h)
    let ν := (1-u)*ν₀+u*ν₁
    let β := 89/3478+(7441/8695)*α
    let ℓ := α-1/10000000000
    let v := α+1/10000000000
    let μ := (1:ℝ)/1000000
    μ≤ℓ ∧
      v+μ≤1 ∧
      μ≤h ∧
      μ≤ν ∧
      μ≤g₀ ∧
      5*h+μ≤ℓ ∧
      g₀+μ≤3*h ∧
      ν+μ≤ℓ ∧
      5*v-1-g+μ≤3*ν ∧
      1+g+2*ν+μ≤5*ℓ ∧
      4*ν+1+g+μ≤6*ℓ ∧
      ν+3*v+μ≤1+g ∧
      1+g+μ≤4*ℓ ∧
      3*v+μ≤1+g ∧
      7*v+μ≤2+2*g+ν ∧
      7+7*g+27*ν+μ≤41*ℓ ∧
      2*h+μ≤β ∧
      4*v+g₀-3*h+μ≤4*β ∧
      288*v-144*h+μ≤288*β ∧
      288*v-36*ν+72*g-216*h+μ≤288*β ∧
      648*v-72-216*h-216*ν+μ≤288*β ∧
      24+96*g-216*h+96*v+144*ν+μ≤288*β ∧
      21+87*g-216*h+177*v+33*ν+μ≤288*β ∧
      15+87*g-216*h+207*v+15*ν+μ≤288*β ∧
      12+78*g-216*h+216*v+24*ν+μ≤288*β ∧
      6+78*g-216*h+246*v+6*ν+μ≤288*β ∧
      72*g-216*h+284*v-24*ν+μ≤288*β ∧
      504*v-72-216*h+72*ν+μ≤288*β := by
  intro α h g₀ ν₀ ν₁ g ν β ℓ v μ
  have ht0 := ht.1
  have ht1 := ht.2
  have hraw := fourth_pair_capped_terminal_source_window_scales ht hu
  dsimp only at hraw
  obtain ⟨h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11,h12,h13,h14,h15,h16,h17,h18,h19,h20,h21,h22,h23,h24,h25,h26,h27,h28,h29⟩ := hraw
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · dsimp only [α,h,g₀,ν₀,ν₁,g,ν,β,ℓ,v,μ]
    nlinarith only [ht0,ht1]
  · dsimp only [α,h,g₀,ν₀,ν₁,g,ν,β,ℓ,v,μ]
    nlinarith only [ht0,ht1]
  · dsimp only [α,h,g₀,ν₀,ν₁,g,ν,β,ℓ,v,μ]
    nlinarith only [h3]
  · dsimp only [α,h,g₀,ν₀,ν₁,g,ν,β,ℓ,v,μ]
    nlinarith only [h7]
  · dsimp only [α,h,g₀,ν₀,ν₁,g,ν,β,ℓ,v,μ]
    nlinarith only [h1]
  · dsimp only [α,h,g₀,ν₀,ν₁,g,ν,β,ℓ,v,μ]
    nlinarith only [h4,h3]
  · dsimp only [α,h,g₀,ν₀,ν₁,g,ν,β,ℓ,v,μ]
    nlinarith only [h2]
  · dsimp only [α,h,g₀,ν₀,ν₁,g,ν,β,ℓ,v,μ]
    nlinarith only [h8]
  · dsimp only [α,h,g₀,ν₀,ν₁,g,ν,β,ℓ,v,μ]
    nlinarith only [h13]
  · dsimp only [α,h,g₀,ν₀,ν₁,g,ν,β,ℓ,v,μ]
    nlinarith only [h16]
  · dsimp only [α,h,g₀,ν₀,ν₁,g,ν,β,ℓ,v,μ]
    nlinarith only [h14]
  · dsimp only [α,h,g₀,ν₀,ν₁,g,ν,β,ℓ,v,μ]
    nlinarith only [h10]
  · dsimp only [α,h,g₀,ν₀,ν₁,g,ν,β,ℓ,v,μ]
    nlinarith only [h15]
  · dsimp only [α,h,g₀,ν₀,ν₁,g,ν,β,ℓ,v,μ]
    nlinarith only [h11]
  · dsimp only [α,h,g₀,ν₀,ν₁,g,ν,β,ℓ,v,μ]
    nlinarith only [h12]
  · dsimp only [α,h,g₀,ν₀,ν₁,g,ν,β,ℓ,v,μ]
    nlinarith only [h18]
  · dsimp only [α,h,g₀,ν₀,ν₁,g,ν,β,ℓ,v,μ]
    nlinarith only [ht0,ht1]
  · dsimp only [α,h,g₀,ν₀,ν₁,g,ν,β,ℓ,v,μ]
    nlinarith only [ht0,ht1]
  · dsimp only [α,h,g₀,ν₀,ν₁,g,ν,β,ℓ,v,μ]
    nlinarith only [h19]
  · dsimp only [α,h,g₀,ν₀,ν₁,g,ν,β,ℓ,v,μ]
    nlinarith only [h20]
  · dsimp only [α,h,g₀,ν₀,ν₁,g,ν,β,ℓ,v,μ]
    nlinarith only [h21]
  · dsimp only [α,h,g₀,ν₀,ν₁,g,ν,β,ℓ,v,μ]
    nlinarith only [h22]
  · dsimp only [α,h,g₀,ν₀,ν₁,g,ν,β,ℓ,v,μ]
    nlinarith only [h23]
  · dsimp only [α,h,g₀,ν₀,ν₁,g,ν,β,ℓ,v,μ]
    nlinarith only [h24]
  · dsimp only [α,h,g₀,ν₀,ν₁,g,ν,β,ℓ,v,μ]
    nlinarith only [h25]
  · dsimp only [α,h,g₀,ν₀,ν₁,g,ν,β,ℓ,v,μ]
    nlinarith only [h26]
  · dsimp only [α,h,g₀,ν₀,ν₁,g,ν,β,ℓ,v,μ]
    nlinarith only [h28]
  · dsimp only [α,h,g₀,ν₀,ν₁,g,ν,β,ℓ,v,μ]
    nlinarith only [h29]

example
    {t u : ℝ} (ht : t∈Icc (0:ℝ) 1) (hu : u∈Icc (0:ℝ) 1) :
    let α := (1-t)*(890/3277)+t*(17604372/60424193)
    let h := ((1-t)*2749411+t*3296917)/100000000
    let g₀ := ((1-t)*16756+t*1976824)/100000000
    let ν₀ := ((1-t)*11931645+t*14567321)/100000000
    let ν₁ := ((1-t)*11969967+t*14925729)/100000000
    let g := (1-u)*g₀+u*(3*h)
    let ν := (1-u)*ν₀+u*ν₁
    let β := 89/3478+(7441/8695)*α
    let ℓ := α-1/10000000000
    let v := α+1/10000000000
    let μ := (1:ℝ)/1000000
    μ≤ℓ ∧
      v+μ≤1 ∧
      μ≤h ∧
      μ≤ν ∧
      μ≤g₀ ∧
      5*h+μ≤ℓ ∧
      g₀+μ≤3*h ∧
      ν+μ≤ℓ ∧
      5*v-1-g+μ≤3*ν ∧
      1+g+2*ν+μ≤5*ℓ ∧
      4*ν+1+g+μ≤6*ℓ ∧
      ν+3*v+μ≤1+g ∧
      1+g+μ≤4*ℓ ∧
      3*v+μ≤1+g ∧
      7*v+μ≤2+2*g+ν ∧
      7+7*g+27*ν+μ≤41*ℓ ∧
      2*h+μ≤β ∧
      4*v+g₀-3*h+μ≤4*β ∧
      288*v-144*h+μ≤288*β ∧
      288*v-36*ν+72*g-216*h+μ≤288*β ∧
      648*v-72-216*h-216*ν+μ≤288*β ∧
      24+96*g-216*h+96*v+144*ν+μ≤288*β ∧
      21+87*g-216*h+177*v+33*ν+μ≤288*β ∧
      15+87*g-216*h+207*v+15*ν+μ≤288*β ∧
      12+78*g-216*h+216*v+24*ν+μ≤288*β ∧
      6+78*g-216*h+246*v+6*ν+μ≤288*β ∧
      72*g-216*h+284*v-24*ν+μ≤288*β ∧
      504*v-72-216*h+72*ν+μ≤288*β := by
  exact fourth_pair_capped_full_window_margins ht hu

#print axioms fourth_pair_capped_full_window_margins

/-- The selected double-shift radius converts the polynomial power-window
inequalities into every actual capped source budget. No N^2≤M is imposed. -/
private theorem double_difference_capped_polynomial_source_budgets
    {X M N J R B : ℝ} (hX : 0<X) (hM : 0<M) (hN : 0<N)
    (hJ : 0<J) (hR : 0<R) (hB : 1≤B) (hBN : B≤N)
    (hscale : (X*J/M^2)*N*R^2=M^3)
    (hRN : B^2*M^5≤X*J*N^3) (hNR : B*X*J*N^2≤M^5)
    (hNM : B*N≤M) (hCubic : B*X*J*N^4≤M^6)
    (hCap : B^2*N*M^3≤X*J) (hHeight : B*X*J≤M^4)
    (hMT : B*M^3≤X*J) (hRT : B*M^7≤X^2*J^2*N)
    (hTen : B^2*X^7*J^7*N^27≤M^41) :
    B≤R ∧ B*R≤N ∧ B*N≤R^2 ∧ B*N≤M ∧
      B*N^3≤M*R^2 ∧ B*N*R≤M ∧ B*M≤N*R^2 ∧
      B*M≤X*J/M^2 ∧ B*R^2≤X*J/M^2 ∧ B*N^10≤M^3*R^7 := by
  have hBp := zero_lt_one.trans_le hB
  have hDen : 0<X*J*N := mul_pos (mul_pos hX hJ) hN
  have hR2 : R^2=M^5/(X*J*N) := by
    apply (eq_div_iff hDen.ne').mpr
    have hs := hscale
    field_simp at hs
    nlinarith only [hs]
  have hNR' : B*N≤R^2 := by
    rw [hR2]
    apply (le_div_iff₀ hDen).mpr
    convert hNR using 1
    ring
  refine ⟨?_,?_,hNR',hNM,?_,?_,?_,?_,?_,?_⟩
  · apply (sq_le_sq₀ hBp.le hR.le).mp
    calc
      B^2 = B*B := pow_two B
      _ ≤ B*N := mul_le_mul_of_nonneg_left hBN hBp.le
      _ ≤ R^2 := hNR'
  · apply (sq_le_sq₀ (mul_nonneg hBp.le hR.le) hN.le).mp
    rw [mul_pow,hR2,←mul_div_assoc]
    apply (div_le_iff₀ hDen).mpr
    convert hRN using 1
    ring
  · rw [hR2,←mul_div_assoc]
    apply (le_div_iff₀ hDen).mpr
    convert hCubic using 1 <;> ring
  · apply (sq_le_sq₀ (mul_nonneg (mul_nonneg hBp.le hN.le) hR.le) hM.le).mp
    simp only [mul_pow]
    rw [hR2,←mul_div_assoc]
    apply (div_le_iff₀ hDen).mpr
    have hh := mul_le_mul_of_nonneg_right hCap (mul_nonneg hN.le (sq_nonneg M))
    convert hh using 1 <;> ring
  · rw [hR2,←mul_div_assoc]
    apply (le_div_iff₀ hDen).mpr
    have hh := mul_le_mul_of_nonneg_right hHeight (mul_nonneg hM.le hN.le)
    convert hh using 1 <;> ring
  · apply (le_div_iff₀ (sq_pos_of_pos hM)).mpr
    convert hMT using 1
    ring
  · rw [hR2,←mul_div_assoc]
    apply (div_le_div_iff₀ hDen (sq_pos_of_pos hM)).mpr
    convert hRT using 1 <;> ring
  · apply (sq_le_sq₀ (mul_nonneg hBp.le (pow_nonneg hN.le 10))
      (mul_nonneg (pow_nonneg hM.le 3) (pow_nonneg hR.le 7))).mp
    simp only [mul_pow,←pow_mul]
    rw [show R^14=(R^2)^7 by rw [←pow_mul],hR2,div_pow,←mul_div_assoc]
    apply (le_div_iff₀ (pow_pos hDen 7)).mpr
    convert hTen using 1 <;> ring

example
    {X M N J R B : ℝ} (hX : 0<X) (hM : 0<M) (hN : 0<N)
    (hJ : 0<J) (hR : 0<R) (hB : 1≤B) (hBN : B≤N)
    (hscale : (X*J/M^2)*N*R^2=M^3)
    (hRN : B^2*M^5≤X*J*N^3) (hNR : B*X*J*N^2≤M^5)
    (hNM : B*N≤M) (hCubic : B*X*J*N^4≤M^6)
    (hCap : B^2*N*M^3≤X*J) (hHeight : B*X*J≤M^4)
    (hMT : B*M^3≤X*J) (hRT : B*M^7≤X^2*J^2*N)
    (hTen : B^2*X^7*J^7*N^27≤M^41) :
    B≤R ∧ B*R≤N ∧ B*N≤R^2 ∧ B*N≤M ∧
      B*N^3≤M*R^2 ∧ B*N*R≤M ∧ B*M≤N*R^2 ∧
      B*M≤X*J/M^2 ∧ B*R^2≤X*J/M^2 ∧ B*N^10≤M^3*R^7 := by
  exact double_difference_capped_polynomial_source_budgets hX hM hN hJ hR hB hBN
    hscale hRN hNR hNM hCubic hCap hHeight hMT hRT hTen

#print axioms double_difference_capped_polynomial_source_budgets

/-- The linked ten-monomial two-step Weyl majorant is bounded over a full
power window, retaining both floor losses and the constant extension term. -/
private theorem double_difference_ten_monomials_power_window
    {X M N H J ℓ u ν h g ξ : ℝ} (hX : 1≤X) (hξ : 0≤ξ)
    (hMl : X^ℓ≤M) (hMu : M≤X^u)
    (hNl : X^ν/2≤N) (hNu : N≤X^ν) (hHl : X^h/2≤H) (hJ : J=X^g)
    (hDiag : 288*u-144*h≤ξ)
    (hSqrt : 288*u-36*ν+72*g-216*h≤ξ)
    (hSecond : 648*u-72-216*h-216*ν≤ξ)
    (hThird : 504*u-72-216*h+72*ν≤ξ)
    (hFourth : 24+96*g-216*h+96*u+144*ν≤ξ)
    (hFirstMain : 12+78*g-216*h+216*u+24*ν≤ξ)
    (hSecondMain : 21+87*g-216*h+177*u+33*ν≤ξ)
    (hThirdMain : 6+78*g-216*h+246*u+6*ν≤ξ)
    (hFourthMain : 15+87*g-216*h+207*u+15*ν≤ξ)
    (hFifthMain : 72*g-216*h+284*u-24*ν≤ξ) :
    1+(M^288/H^144+
        ((J^72*M^288/(H^216*N^36)+M^648/(X^72*H^216*N^216)+
          M^504*N^72/(X^72*H^216)+X^24*J^96*M^96*N^144/H^216)+
          (X^12*J^78*M^216*N^24/H^216+X^21*J^87*M^177*N^33/H^216+
            X^6*J^78*M^246*N^6/H^216+X^15*J^87*M^207*N^15/H^216+
            J^72*M^284/(H^216*N^24)))) ≤ (11*(2:ℝ)^432)*X^ξ := by
  have hXp := zero_lt_one.trans_le hX
  have hbound (k : ℕ) (e : ℝ) (hk : k≤432) (he : e≤ξ) :
      (2:ℝ)^k*X^e≤(2:ℝ)^432*X^ξ :=
    mul_le_mul (pow_le_pow_right₀ (by norm_num) hk)
      (Real.rpow_le_rpow_of_exponent_le hX he)
      (Real.rpow_nonneg hXp.le _) (by norm_num)
  have h₀ : 1≤(2:ℝ)^432*X^ξ :=
    one_le_mul_of_one_le_of_one_le (one_le_pow₀ (by norm_num)) (Real.one_le_rpow hX hξ)
  have hb1 : M^288/H^144≤(2:ℝ)^432*X^ξ := by
    have hh := double_difference_monomial_power_window hX hMl hMu hNl hNu hHl hJ
      0 0 288 0 0 144 0 0 0
    have heq : (0:ℝ)+0*g+288*u+0*ν-0-144*h-0*ν-0*ℓ-0*g =
        288*u-144*h := by ring
    simp only [Nat.cast_zero,Nat.cast_ofNat,pow_zero,one_mul,mul_one,
      heq] at hh
    exact hh.trans (hbound 144 _ (by norm_num) hDiag)
  have hb2 : J^72*M^288/(H^216*N^36)≤(2:ℝ)^432*X^ξ := by
    have hh := double_difference_monomial_power_window hX hMl hMu hNl hNu hHl hJ
      0 72 288 0 0 216 36 0 0
    have heq : (0:ℝ)+72*g+288*u+0*ν-0-216*h-36*ν-0*ℓ-0*g =
        288*u-36*ν+72*g-216*h := by ring
    simp only [Nat.cast_zero,Nat.cast_ofNat,pow_zero,one_mul,mul_one,
      heq] at hh
    exact hh.trans (hbound 252 _ (by norm_num) hSqrt)
  have hb3 : M^648/(X^72*H^216*N^216)≤(2:ℝ)^432*X^ξ := by
    have hh := double_difference_monomial_power_window hX hMl hMu hNl hNu hHl hJ
      0 0 648 0 72 216 216 0 0
    have heq : (0:ℝ)+0*g+648*u+0*ν-72-216*h-216*ν-0*ℓ-0*g =
        648*u-72-216*h-216*ν := by ring
    simp only [Nat.cast_zero,Nat.cast_ofNat,pow_zero,one_mul,mul_one,
      heq] at hh
    exact hh.trans (hbound 432 _ (by norm_num) hSecond)
  have hb4 : M^504*N^72/(X^72*H^216)≤(2:ℝ)^432*X^ξ := by
    have hh := double_difference_monomial_power_window hX hMl hMu hNl hNu hHl hJ
      0 0 504 72 72 216 0 0 0
    have heq : (0:ℝ)+0*g+504*u+72*ν-72-216*h-0*ν-0*ℓ-0*g =
        504*u-72-216*h+72*ν := by ring
    simp only [Nat.cast_zero,Nat.cast_ofNat,pow_zero,one_mul,mul_one,
      heq] at hh
    exact hh.trans (hbound 216 _ (by norm_num) hThird)
  have hb5 : X^24*J^96*M^96*N^144/H^216≤(2:ℝ)^432*X^ξ := by
    have hh := double_difference_monomial_power_window hX hMl hMu hNl hNu hHl hJ
      24 96 96 144 0 216 0 0 0
    have heq : (24:ℝ)+96*g+96*u+144*ν-0-216*h-0*ν-0*ℓ-0*g =
        24+96*g-216*h+96*u+144*ν := by ring
    simp only [Nat.cast_zero,Nat.cast_ofNat,pow_zero,one_mul,mul_one,
      heq] at hh
    exact hh.trans (hbound 216 _ (by norm_num) hFourth)
  have hb6 : X^12*J^78*M^216*N^24/H^216≤(2:ℝ)^432*X^ξ := by
    have hh := double_difference_monomial_power_window hX hMl hMu hNl hNu hHl hJ
      12 78 216 24 0 216 0 0 0
    have heq : (12:ℝ)+78*g+216*u+24*ν-0-216*h-0*ν-0*ℓ-0*g =
        12+78*g-216*h+216*u+24*ν := by ring
    simp only [Nat.cast_zero,Nat.cast_ofNat,pow_zero,one_mul,mul_one,
      heq] at hh
    exact hh.trans (hbound 216 _ (by norm_num) hFirstMain)
  have hb7 : X^21*J^87*M^177*N^33/H^216≤(2:ℝ)^432*X^ξ := by
    have hh := double_difference_monomial_power_window hX hMl hMu hNl hNu hHl hJ
      21 87 177 33 0 216 0 0 0
    have heq : (21:ℝ)+87*g+177*u+33*ν-0-216*h-0*ν-0*ℓ-0*g =
        21+87*g-216*h+177*u+33*ν := by ring
    simp only [Nat.cast_zero,Nat.cast_ofNat,pow_zero,one_mul,mul_one,
      heq] at hh
    exact hh.trans (hbound 216 _ (by norm_num) hSecondMain)
  have hb8 : X^6*J^78*M^246*N^6/H^216≤(2:ℝ)^432*X^ξ := by
    have hh := double_difference_monomial_power_window hX hMl hMu hNl hNu hHl hJ
      6 78 246 6 0 216 0 0 0
    have heq : (6:ℝ)+78*g+246*u+6*ν-0-216*h-0*ν-0*ℓ-0*g =
        6+78*g-216*h+246*u+6*ν := by ring
    simp only [Nat.cast_zero,Nat.cast_ofNat,pow_zero,one_mul,mul_one,
      heq] at hh
    exact hh.trans (hbound 216 _ (by norm_num) hThirdMain)
  have hb9 : X^15*J^87*M^207*N^15/H^216≤(2:ℝ)^432*X^ξ := by
    have hh := double_difference_monomial_power_window hX hMl hMu hNl hNu hHl hJ
      15 87 207 15 0 216 0 0 0
    have heq : (15:ℝ)+87*g+207*u+15*ν-0-216*h-0*ν-0*ℓ-0*g =
        15+87*g-216*h+207*u+15*ν := by ring
    simp only [Nat.cast_zero,Nat.cast_ofNat,pow_zero,one_mul,mul_one,
      heq] at hh
    exact hh.trans (hbound 216 _ (by norm_num) hFourthMain)
  have hb10 : J^72*M^284/(H^216*N^24)≤(2:ℝ)^432*X^ξ := by
    have hh := double_difference_monomial_power_window hX hMl hMu hNl hNu hHl hJ
      0 72 284 0 0 216 24 0 0
    have heq : (0:ℝ)+72*g+284*u+0*ν-0-216*h-24*ν-0*ℓ-0*g =
        72*g-216*h+284*u-24*ν := by ring
    simp only [Nat.cast_zero,Nat.cast_ofNat,pow_zero,one_mul,mul_one,
      heq] at hh
    exact hh.trans (hbound 240 _ (by norm_num) hFifthMain)
  have hSum (d : ℝ) : d+(d+((d+d+d+d)+(d+d+d+d+d)))=11*d := by ring
  calc
    _ ≤ (2:ℝ)^432*X^ξ+((2:ℝ)^432*X^ξ+
        (((2:ℝ)^432*X^ξ+(2:ℝ)^432*X^ξ+(2:ℝ)^432*X^ξ+(2:ℝ)^432*X^ξ)+
          ((2:ℝ)^432*X^ξ+(2:ℝ)^432*X^ξ+(2:ℝ)^432*X^ξ+
            (2:ℝ)^432*X^ξ+(2:ℝ)^432*X^ξ))) :=
      add_le_add h₀ (add_le_add hb1
        (add_le_add (add_le_add (add_le_add (add_le_add hb2 hb3) hb4) hb5)
          (add_le_add (add_le_add (add_le_add (add_le_add hb6 hb7) hb8) hb9) hb10)))
    _ = 11*((2:ℝ)^432*X^ξ) := hSum _
    _ = _ := (mul_assoc _ _ _).symm

example
    {X M N H J ℓ u ν h g ξ : ℝ} (hX : 1≤X) (hξ : 0≤ξ)
    (hMl : X^ℓ≤M) (hMu : M≤X^u)
    (hNl : X^ν/2≤N) (hNu : N≤X^ν) (hHl : X^h/2≤H) (hJ : J=X^g)
    (hDiag : 288*u-144*h≤ξ)
    (hSqrt : 288*u-36*ν+72*g-216*h≤ξ)
    (hSecond : 648*u-72-216*h-216*ν≤ξ)
    (hThird : 504*u-72-216*h+72*ν≤ξ)
    (hFourth : 24+96*g-216*h+96*u+144*ν≤ξ)
    (hFirstMain : 12+78*g-216*h+216*u+24*ν≤ξ)
    (hSecondMain : 21+87*g-216*h+177*u+33*ν≤ξ)
    (hThirdMain : 6+78*g-216*h+246*u+6*ν≤ξ)
    (hFourthMain : 15+87*g-216*h+207*u+15*ν≤ξ)
    (hFifthMain : 72*g-216*h+284*u-24*ν≤ξ) :
    1+(M^288/H^144+
        ((J^72*M^288/(H^216*N^36)+M^648/(X^72*H^216*N^216)+
          M^504*N^72/(X^72*H^216)+X^24*J^96*M^96*N^144/H^216)+
          (X^12*J^78*M^216*N^24/H^216+X^21*J^87*M^177*N^33/H^216+
            X^6*J^78*M^246*N^6/H^216+X^15*J^87*M^207*N^15/H^216+
            J^72*M^284/(H^216*N^24)))) ≤ (11*(2:ℝ)^432)*X^ξ := by
  exact double_difference_ten_monomials_power_window hX hξ hMl hMu hNl hNu hHl hJ
    hDiag hSqrt hSecond hThird hFourth hFirstMain hSecondMain hThirdMain hFourthMain hFifthMain

#print axioms double_difference_ten_monomials_power_window

private theorem upperOriginal_floor_power_scales
    {U V : ℝ} (hU : 32≤U) (hV : 4≤V) :
    let n := ⌊U/8⌋₊
    let N := 8*n
    let H := ⌊V⌋₊
    2≤N ∧ 2≤H ∧ U/2≤(N:ℝ) ∧ (N:ℝ)≤U ∧
      V/2≤(H:ℝ) ∧ (H:ℝ)≤V := by
  intro n N H
  have hn4 : 4≤n := Nat.le_floor (by linarith only [hU] : (4:ℝ)≤U/8)
  have hH4 : 4≤H := Nat.le_floor hV
  have hNcast : (N:ℝ)=8*(n:ℝ) := by simp only [N,Nat.cast_mul,Nat.cast_ofNat]
  have hnlo : U/8<(n:ℝ)+1 := Nat.lt_floor_add_one (U/8)
  have hnhi : (n:ℝ)≤U/8 := Nat.floor_le (by linarith only [hU])
  have hHlo : V<(H:ℝ)+1 := Nat.lt_floor_add_one V
  have hHhi : (H:ℝ)≤V := Nat.floor_le (by linarith only [hV])
  refine ⟨by dsimp only [N]; omega,by omega,?_,?_,?_,hHhi⟩
  · rw [hNcast]
    linarith only [hnlo,hU]
  · rw [hNcast]
    linarith only [hnhi]
  · linarith only [hHlo,hV]

example
    {U V : ℝ} (hU : 32≤U) (hV : 4≤V) :
    let n := ⌊U/8⌋₊
    let N := 8*n
    let H := ⌊V⌋₊
    2≤N ∧ 2≤H ∧ U/2≤(N:ℝ) ∧ (N:ℝ)≤U ∧
      V/2≤(H:ℝ) ∧ (H:ℝ)≤V := by
  exact upperOriginal_floor_power_scales hU hV

#print axioms upperOriginal_floor_power_scales

/-- Uniformly construct the actual integer scales and radius for the capped
Huxley source from strict power-window margins. The threshold precedes all
product exponents and all actual product-block families. -/
private theorem eventually_double_difference_capped_physical_window
    {B C w₀ μ ℓ v h : ℝ} (hB : 1≤B) (hC : 1≤C) (hw₀ : 0<w₀)
    (hμ : 0<μ) (hμℓ : μ≤ℓ) (hℓv : ℓ≤v) (hμh : μ≤h)
    (hWidth : 5*h+μ≤ℓ) :
    ∀ᶠ X : ℝ in Filter.atTop, 2≤X ∧
      ∀ M J g ν : ℝ, X^ℓ≤M → M≤X^v → J=X^g →
        0≤g → g≤3*h → μ≤ν → ν+μ≤ℓ →
        5*v-1-g+μ≤3*ν → 1+g+2*ν+μ≤5*ℓ →
        4*ν+1+g+μ≤6*ℓ → ν+3*v+μ≤1+g →
        1+g+μ≤4*ℓ → 3*v+μ≤1+g →
        7*v+μ≤2+2*g+ν → 7+7*g+27*ν+μ≤41*ℓ →
        let n := ⌊X^ν/8⌋₊
        let N := 8*n
        let H := ⌊X^h⌋₊
        let R := Real.sqrt (M^5/(X*J*(N:ℝ)))
        let T := X*J/M^2
        let W := ((H:ℝ)+(H:ℝ)^2)/M
        1≤M ∧ 2≤N ∧ 2≤H ∧
          X^ν/2≤(N:ℝ) ∧ (N:ℝ)≤X^ν ∧ X^h/2≤(H:ℝ) ∧ (H:ℝ)≤X^h ∧
          1≤J ∧ 0<R ∧ T*(N:ℝ)*R^2=M^3 ∧ C≤T ∧
          W≤w₀ ∧ J≤M ∧ W*J≤1 ∧
          B≤R ∧ B*R≤N ∧ B*(N:ℝ)≤R^2 ∧ B*(N:ℝ)≤M ∧
          B*(N:ℝ)^3≤M*R^2 ∧ B*(N:ℝ)*R≤M ∧ B*M≤(N:ℝ)*R^2 ∧
          B*M≤T ∧ B*R^2≤T ∧ B*(N:ℝ)^10≤M^3*R^7 := by
  have hB0 := zero_le_one.trans hB
  have hC0 := zero_le_one.trans hC
  have hℓp := hμ.trans_le hμℓ
  have hv0 := (hℓp.trans_le hℓv).le
  have hhp := hμ.trans_le hμh
  let D := 32+8*B^2+2*B+C+2/w₀
  have hInv : 0<2/w₀ := div_pos (by norm_num) hw₀
  have hD32 : 32≤D := by dsimp only [D]; nlinarith only [sq_nonneg B,hB0,hC0,hInv]
  have hDB : 2*B≤D := by dsimp only [D]; nlinarith only [sq_nonneg B,hC0,hInv]
  have hDBsq : 8*B^2≤D := by dsimp only [D]; linarith only [hB0,hC0,hInv]
  have hDC : C≤D := by dsimp only [D]; nlinarith only [sq_nonneg B,hB0,hInv]
  have hDW : 2/w₀≤D := by dsimp only [D]; nlinarith only [sq_nonneg B,hB0,hC0]
  have hD1 : 1≤D := (by norm_num : (1:ℝ)≤32).trans hD32
  have hDB1 : B≤D := (by linarith only [hB0] : B≤2*B).trans hDB
  have hDBsq1 : B^2≤D := (by nlinarith only [sq_nonneg B] : B^2≤8*B^2).trans hDBsq
  have hD2 : 2≤D := (by norm_num : (2:ℝ)≤32).trans hD32
  filter_upwards [(tendsto_rpow_atTop hμ).eventually_ge_atTop D,
    Filter.eventually_ge_atTop (2:ℝ)] with X hXD hX2
  have hX : 1≤X := (by norm_num : (1:ℝ)≤2).trans hX2
  have hXp := zero_lt_one.trans_le hX
  have hdom (A e : ℝ) (hAD : A≤D) (he : e+μ≤0) : A*X^e≤1 := by
    calc
      _ ≤ X^μ*X^e := mul_le_mul_of_nonneg_right (hAD.trans hXD) (Real.rpow_nonneg hXp.le _)
      _ = X^(μ+e) := (Real.rpow_add hXp _ _).symm
      _ ≤ X^(0:ℝ) := Real.rpow_le_rpow_of_exponent_le hX (by linarith only [he])
      _ = 1 := Real.rpow_zero X
  refine ⟨hX2,?_⟩
  intro M J g ν hMl hMu hJ hg0 hgh hμν hνM hRN hNR hCubic hCap hHeight hMT hRT hTen
    n N H R T W
  have hM1 : 1≤M := (Real.one_le_rpow hX hℓp.le).trans hMl
  have hMp := zero_lt_one.trans_le hM1
  have hJ1 : 1≤J := by rw [hJ]; exact Real.one_le_rpow hX hg0
  have hJp := zero_lt_one.trans_le hJ1
  have hNU : 32≤X^ν := hD32.trans (hXD.trans (Real.rpow_le_rpow_of_exponent_le hX hμν))
  have hHU : 4≤X^h :=
    (by norm_num : (4:ℝ)≤32).trans (hD32.trans (hXD.trans (Real.rpow_le_rpow_of_exponent_le hX hμh)))
  obtain ⟨hN2,hH2,hNl,hNu,hHl,hHu⟩ := upperOriginal_floor_power_scales hNU hHU
  have hNp : (0:ℝ)<N := by exact_mod_cast (show 0<N by omega)
  have hH1 : (1:ℝ)≤H := by exact_mod_cast (show 1≤H by omega)
  have hBN : B≤(N:ℝ) := by
    have hh := hDB.trans (hXD.trans (Real.rpow_le_rpow_of_exponent_le hX hμν))
    linarith only [hh,hNl]
  have hratio (A : ℝ) (p q r s x t vN w z : ℕ)
      (hA : 0≤A) (hAD : A*(2:ℝ)^(t+vN)≤D)
      (he : (p:ℝ)+q*g+r*v+s*ν-x-t*h-vN*ν-w*ℓ-z*g+μ≤0) :
      A*(X^p*J^q*M^r*(N:ℝ)^s/(X^x*(H:ℝ)^t*(N:ℝ)^vN*M^w*J^z))≤1 := by
    calc
      _ ≤ A*((2:ℝ)^(t+vN)*X^((p:ℝ)+q*g+r*v+s*ν-x-t*h-vN*ν-w*ℓ-z*g)) :=
        mul_le_mul_of_nonneg_left
          (double_difference_monomial_power_window hX hMl hMu hNl hNu hHl hJ p q r s x t vN w z) hA
      _ = (A*(2:ℝ)^(t+vN))*X^((p:ℝ)+q*g+r*v+s*ν-x-t*h-vN*ν-w*ℓ-z*g) :=
        (mul_assoc _ _ _).symm
      _ ≤ 1 := hdom _ _ hAD he

  have hpoly {a b c : ℝ} (hb : 0<b) (hh : c*(a/b)≤1) : c*a≤b := by
    rw [←mul_div_assoc] at hh
    simpa only [one_mul] using (div_le_iff₀ hb).mp hh
  have pRN : B^2*M^5≤X*J*(N:ℝ)^3 := by
    have hh := hratio (B^2) 0 0 5 0 1 0 3 0 1 (sq_nonneg B)
      (by norm_num; nlinarith only [hDBsq])
      (by norm_num; linarith only [hRN])
    simp only [pow_zero,pow_one,one_mul,mul_one] at hh
    have hh' := hpoly (by positivity) hh
    convert hh' using 1
    ring
  have pNR : B*X*J*(N:ℝ)^2≤M^5 := by
    have hh := hratio (B) 1 1 0 2 0 0 0 5 0 (hB0)
      (by norm_num; nlinarith only [hDB1])
      (by norm_num; linarith only [hNR])
    simp only [pow_zero,pow_one,one_mul,mul_one] at hh
    have hh' := hpoly (by positivity) hh
    convert hh' using 1
    ring
  have pNM : B*(N:ℝ)≤M := by
    have hh := hratio (B) 0 0 0 1 0 0 0 1 0 (hB0)
      (by norm_num; nlinarith only [hDB1])
      (by norm_num; linarith only [hνM])
    simp only [pow_zero,pow_one,one_mul,mul_one] at hh
    have hh' := hpoly (by positivity) hh
    exact hh'
  have pCubic : B*X*J*(N:ℝ)^4≤M^6 := by
    have hh := hratio (B) 1 1 0 4 0 0 0 6 0 (hB0)
      (by norm_num; nlinarith only [hDB1])
      (by norm_num; linarith only [hCubic])
    simp only [pow_zero,pow_one,one_mul,mul_one] at hh
    have hh' := hpoly (by positivity) hh
    convert hh' using 1
    ring
  have pCap : B^2*(N:ℝ)*M^3≤X*J := by
    have hh := hratio (B^2) 0 0 3 1 1 0 0 0 1 (sq_nonneg B)
      (by norm_num; nlinarith only [hDBsq1])
      (by norm_num; linarith only [hCap])
    simp only [pow_zero,pow_one,one_mul,mul_one] at hh
    have hh' := hpoly (by positivity) hh
    convert hh' using 1
    ring
  have pHeight : B*X*J≤M^4 := by
    have hh := hratio (B) 1 1 0 0 0 0 0 4 0 (hB0)
      (by norm_num; nlinarith only [hDB1])
      (by norm_num; linarith only [hHeight])
    simp only [pow_zero,pow_one,one_mul,mul_one] at hh
    have hh' := hpoly (by positivity) hh
    convert hh' using 1
    ring
  have pMT : B*M^3≤X*J := by
    have hh := hratio (B) 0 0 3 0 1 0 0 0 1 (hB0)
      (by norm_num; nlinarith only [hDB1])
      (by norm_num; linarith only [hMT])
    simp only [pow_zero,pow_one,one_mul,mul_one] at hh
    have hh' := hpoly (by positivity) hh
    exact hh'
  have pRT : B*M^7≤X^2*J^2*(N:ℝ) := by
    have hh := hratio (B) 0 0 7 0 2 0 1 0 2 (hB0)
      (by norm_num; nlinarith only [hDB])
      (by norm_num; linarith only [hRT])
    simp only [pow_zero,pow_one,one_mul,mul_one] at hh
    have hh' := hpoly (by positivity) hh
    convert hh' using 1
    ring
  have pTen : B^2*X^7*J^7*(N:ℝ)^27≤M^41 := by
    have hh := hratio (B^2) 7 7 0 27 0 0 0 41 0 (sq_nonneg B)
      (by norm_num; nlinarith only [hDBsq1])
      (by norm_num; linarith only [hTen])
    simp only [pow_zero,one_mul,mul_one] at hh
    have hh' := hpoly (by positivity) hh
    convert hh' using 1
    ring
  have pThreshold : C*M^2≤X*J := by
    have hh := hratio (C) 0 0 2 0 1 0 0 0 1 (hC0)
      (by norm_num; nlinarith only [hDC])
      (by norm_num; linarith only [hMT,hv0])
    simp only [pow_zero,pow_one,one_mul,mul_one] at hh
    have hh' := hpoly (by positivity) hh
    exact hh'
  have pJ : J≤M := by
    have hh := hratio (1) 0 1 0 0 0 0 0 1 0 (zero_le_one)
      (by norm_num; nlinarith only [hD1])
      (by norm_num; linarith only [hgh,hWidth,hhp])
    simp only [pow_zero,pow_one,one_mul,mul_one] at hh
    exact (div_le_one hMp).mp hh

  have hThreshold : C≤T := (le_div_iff₀ (sq_pos_of_pos hMp)).mpr pThreshold
  have hWbound : W≤2*X^(2*h-ℓ) := by
    have hHsq : (H:ℝ)^2≤(X^h)^2 := by gcongr
    have hnumer : (H:ℝ)+(H:ℝ)^2≤2*(X^h)^2 := by
      nlinarith only [hH1,hHsq]
    calc
      W ≤ 2*(X^h)^2/X^ℓ :=
        div_le_div₀ (by positivity) hnumer (Real.rpow_pos_of_pos hXp _) hMl
      _ = 2*X^(2*h-ℓ) := by
        have hp : X^(h*2)=(X^h)^2 := by
          simpa only [Nat.cast_ofNat] using Real.rpow_mul_natCast hXp.le h 2
        rw [Real.rpow_sub hXp,show 2*h=h*2 by ring,hp]
        ring
  have hW : W≤w₀ := by
    have hh := hdom (2/w₀) (2*h-ℓ) hDW (by linarith only [hWidth,hhp])
    have hh' := mul_le_mul_of_nonneg_right hh hw₀.le
    have heq : (2/w₀*X^(2*h-ℓ))*w₀=2*X^(2*h-ℓ) := by
      field_simp
    rw [heq,one_mul] at hh'
    exact hWbound.trans hh'
  have hWJ : W*J≤1 := by
    calc
      W*J ≤ (2*X^(2*h-ℓ))*J := mul_le_mul_of_nonneg_right hWbound hJp.le
      _ = 2*X^(2*h-ℓ+g) := by rw [hJ,mul_assoc,←Real.rpow_add hXp]
      _ ≤ 1 := hdom 2 _ hD2 (by linarith only [hgh,hWidth])
  have hRad : 0<M^5/(X*J*(N:ℝ)) := by positivity
  have hRp : 0<R := Real.sqrt_pos.2 hRad
  have hR2 : R^2=M^5/(X*J*(N:ℝ)) := Real.sq_sqrt hRad.le
  have hscale : T*(N:ℝ)*R^2=M^3 := by
    rw [hR2]
    dsimp only [T]
    field_simp
  have hbudgets := double_difference_capped_polynomial_source_budgets hXp hMp hNp hJp hRp
    hB hBN hscale pRN pNR pNM pCubic pCap pHeight pMT pRT pTen
  exact ⟨hM1,hN2,hH2,hNl,hNu,hHl,hHu,hJ1,hRp,hscale,hThreshold,hW,pJ,hWJ,hbudgets⟩

example
    {B C w₀ μ ℓ v h : ℝ} (hB : 1≤B) (hC : 1≤C) (hw₀ : 0<w₀)
    (hμ : 0<μ) (hμℓ : μ≤ℓ) (hℓv : ℓ≤v) (hμh : μ≤h)
    (hWidth : 5*h+μ≤ℓ) :
    ∀ᶠ X : ℝ in Filter.atTop, 2≤X ∧
      ∀ M J g ν : ℝ, X^ℓ≤M → M≤X^v → J=X^g →
        0≤g → g≤3*h → μ≤ν → ν+μ≤ℓ →
        5*v-1-g+μ≤3*ν → 1+g+2*ν+μ≤5*ℓ →
        4*ν+1+g+μ≤6*ℓ → ν+3*v+μ≤1+g →
        1+g+μ≤4*ℓ → 3*v+μ≤1+g →
        7*v+μ≤2+2*g+ν → 7+7*g+27*ν+μ≤41*ℓ →
        let n := ⌊X^ν/8⌋₊
        let N := 8*n
        let H := ⌊X^h⌋₊
        let R := Real.sqrt (M^5/(X*J*(N:ℝ)))
        let T := X*J/M^2
        let W := ((H:ℝ)+(H:ℝ)^2)/M
        1≤M ∧ 2≤N ∧ 2≤H ∧
          X^ν/2≤(N:ℝ) ∧ (N:ℝ)≤X^ν ∧ X^h/2≤(H:ℝ) ∧ (H:ℝ)≤X^h ∧
          1≤J ∧ 0<R ∧ T*(N:ℝ)*R^2=M^3 ∧ C≤T ∧
          W≤w₀ ∧ J≤M ∧ W*J≤1 ∧
          B≤R ∧ B*R≤N ∧ B*(N:ℝ)≤R^2 ∧ B*(N:ℝ)≤M ∧
          B*(N:ℝ)^3≤M*R^2 ∧ B*(N:ℝ)*R≤M ∧ B*M≤(N:ℝ)*R^2 ∧
          B*M≤T ∧ B*R^2≤T ∧ B*(N:ℝ)^10≤M^3*R^7 := by
  exact eventually_double_difference_capped_physical_window hB hC hw₀ hμ hμℓ hℓv hμh hWidth

#print axioms eventually_double_difference_capped_physical_window

/-- Normalize the ACTUAL selected product block from two-step Weyl with
K=H². The selected maximum phases and all endpoint terms are retained. -/
private theorem source_product_twice_weyl_normalized_block
    {ε : ℝ} (hε : 0<ε) :
    ∃ A : ℝ, 1≤A ∧
      ∀ (F : ℝ → ℝ) (σ X M : ℝ) (a L H : ℕ),
        0<σ → 1≤X → 1≤M → 2≤H → H^2≤L+1 →
        (H:ℝ)^3≤X → ((H:ℝ)+(H:ℝ)^2)/M≤1/4 →
        M≤(a:ℝ) → ((a+L:ℕ):ℝ)≤2*M →
        let Pairs := (Finset.Icc 1 (H-1)) ×ˢ (Finset.Icc 1 (H^2-1))
        let Products := Pairs.image (fun p => p.1*p.2)
        let W := fun p : ℕ × ℕ => ∑ j∈Finset.range (L+1-p.1-p.2),
          (𝐞 (X*(F (((a:ℝ)+j)/M)-F (((a:ℝ)+j+p.1)/M)-
            F (((a:ℝ)+j+p.2)/M)+F (((a:ℝ)+j+p.1+p.2)/M))):ℂ)
        ∃ (pick : ℕ → ℕ × ℕ) (k : ℕ), 0<k ∧ 2*k≤H^3 ∧
          (∀ l∈Products, pick l∈Pairs ∧ (pick l).1*(pick l).2=l ∧
            ∀ p∈Pairs, p.1*p.2=l → ‖W p‖≤‖W (pick l)‖) ∧
          (∑ l∈(Finset.Ico k (2*k)).filter (fun l => l∈Products),‖W (pick l)‖)≤2*M*k ∧
          ‖Expdb.exponentialSumAt F X M a (a+L)‖^4 ≤
            A*X^ε*(1+(Nat.clog 2 (H^3):ℝ))*
              (M^4/(H:ℝ)^2+(M^3/(H:ℝ)^3)*
                (∑ l∈(Finset.Ico k (2*k)).filter (fun l => l∈Products),‖W (pick l)‖)) := by
  classical
  obtain ⟨D,hD,hsource⟩ := source_product_twice_weyl_doubled_block hε
  let A := 4096*max 1 D
  have hA : 1≤A := by
    dsimp only [A]
    linarith only [le_max_left (1:ℝ) D]
  refine ⟨A,hA,?_⟩
  intro F σ X M a L H hσ hX hM hH hHL hHX hWidth ha hb Pairs Products W
  have hMp := zero_lt_one.trans_le hM
  have hH1 : (1:ℝ)≤H := by exact_mod_cast (show 1≤H by omega)
  have hHp := zero_lt_one.trans_le hH1
  have hK2 : 2≤H^2 := by nlinarith only [hH]
  have hHK : (H:ℝ)+(H:ℝ)^2<M := by
    have hh := (div_le_iff₀ hMp).mp hWidth
    linarith only [hh,hMp]
  have hHKnat : H+H^2≤a := by
    exact_mod_cast (show (H:ℝ)+(H:ℝ)^2≤(a:ℝ) from hHK.le.trans ha)
  have hHshort : H≤L+1 := (by nlinarith only [hH] : H≤H^2).trans hHL
  have hCube : H*H^2=H^3 := by ring
  obtain ⟨pick,k,hk,hkH,hpick,hweyl⟩ :=
    hsource F σ X M a L H (H^2) hσ hH hK2 hHKnat hHshort hHL
      (by exact_mod_cast hHK)
  rw [hCube] at hkH hweyl
  simp only [Nat.cast_pow] at hweyl
  rw [show (H:ℝ)^2*(H:ℝ)^2=(H:ℝ)^4 by ring,
    show (H:ℝ)*(H:ℝ)^2=(H:ℝ)^3 by ring] at hweyl
  let Z := ∑ l∈(Finset.Ico k (2*k)).filter (fun l => l∈Products),‖W (pick l)‖
  have hZ : 0≤Z := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  let Log := 1+(Nat.clog 2 (H^3):ℝ)
  let U := max 1 D*X^ε*Log
  have hLog : 1≤Log := by dsimp only [Log]; exact le_add_of_nonneg_right (Nat.cast_nonneg _)
  have hXpow : 1≤X^ε := Real.one_le_rpow hX hε.le
  have hU : 1≤U := one_le_mul_of_one_le_of_one_le
    (one_le_mul_of_one_le_of_one_le (le_max_left _ _) hXpow) hLog
  have hLcap : (L:ℝ)+1≤2*M := by
    have hb' : (a:ℝ)+(L:ℝ)≤2*M := by simpa only [Nat.cast_add] using hb
    linarith only [ha,hb',hM]
  have hZcap : Z≤2*M*k := by
    have hWcap (p : ℕ × ℕ) : ‖W p‖≤2*M := by
      calc
        _ ≤ ∑ j∈Finset.range (L+1-p.1-p.2),
            ‖(𝐞 (X*(F (((a:ℝ)+j)/M)-F (((a:ℝ)+j+p.1)/M)-
              F (((a:ℝ)+j+p.2)/M)+F (((a:ℝ)+j+p.1+p.2)/M))):ℂ)‖ := norm_sum_le _ _
        _ = (L+1-p.1-p.2:ℕ) := by simp
        _ ≤ (L:ℝ)+1 := by exact_mod_cast (show L+1-p.1-p.2≤L+1 by omega)
        _ ≤ 2*M := hLcap
    have hCard : ((Finset.Ico k (2*k)).filter (fun l => l∈Products)).card≤k := by
      calc
        _ ≤ (Finset.Ico k (2*k)).card := Finset.card_filter_le _ _
        _ = k := by rw [Nat.card_Ico]; omega
    calc
      _ ≤ ∑ l∈(Finset.Ico k (2*k)).filter (fun l => l∈Products), (2*M) :=
        Finset.sum_le_sum (fun l _ => hWcap (pick l))
      _ = (((Finset.Ico k (2*k)).filter (fun l => l∈Products)).card:ℝ)*(2*M) := by simp
      _ ≤ (k:ℝ)*(2*M) := mul_le_mul_of_nonneg_right (by exact_mod_cast hCard) (by positivity)
      _ = _ := by ring
  have hweight : D*((H:ℝ)^3)^ε*(Nat.clog 2 (H^3):ℝ)≤U := by
    dsimp only [U,Log]
    gcongr
    · exact le_max_right _ _
    · linarith
  have hraw :
      (H:ℝ)^4*‖Expdb.exponentialSumAt F X M a (a+L)‖^4 ≤
        1152*(H:ℝ)^2*M^4+1024*H*M^3*U*(2*M+Z) := by
    calc
      _ ≤ 8*(H:ℝ)^2*((L:ℝ)+1)^4+64*(H:ℝ)^2*((L:ℝ)+1)^4+
          128*H*((L:ℝ)+1)^3*(D*((H:ℝ)^3)^ε*((Nat.clog 2 (H^3):ℝ)*((L:ℝ)+1+Z))) :=
        hweyl
      _ = 72*(H:ℝ)^2*((L:ℝ)+1)^4+
          128*H*((L:ℝ)+1)^3*(D*((H:ℝ)^3)^ε*(Nat.clog 2 (H^3):ℝ))*((L:ℝ)+1+Z) := by ring
      _ ≤ 72*(H:ℝ)^2*(2*M)^4+128*H*(2*M)^3*U*(2*M+Z) := by gcongr
      _ = _ := by ring
  have hDen : (H:ℝ)^2≤(H:ℝ)^3 := by
    calc
      _ = 1*(H:ℝ)^2 := (one_mul _).symm
      _ ≤ (H:ℝ)*(H:ℝ)^2 := mul_le_mul_of_nonneg_right hH1 (sq_nonneg _)
      _ = _ := by ring
  have hRatio : M^4/(H:ℝ)^3≤M^4/(H:ℝ)^2 :=
    div_le_div_of_nonneg_left (pow_nonneg hMp.le 4) (sq_pos_of_pos hHp) hDen
  have hDiag0 : 0≤M^4/(H:ℝ)^2 := by positivity
  have hCorr0 : 0≤(M^3/(H:ℝ)^3)*Z := mul_nonneg (by positivity) hZ
  refine ⟨pick,k,hk,hkH,hpick,hZcap,?_⟩
  calc
    _ ≤ (1152*(H:ℝ)^2*M^4+1024*H*M^3*U*(2*M+Z))/(H:ℝ)^4 :=
      (le_div_iff₀ (pow_pos hHp 4)).mpr ((mul_comm _ _).trans_le hraw)
    _ = 1152*(M^4/(H:ℝ)^2)+2048*U*(M^4/(H:ℝ)^3)+
        1024*U*((M^3/(H:ℝ)^3)*Z) := by field_simp; ring
    _ ≤ 1152*(M^4/(H:ℝ)^2)+2048*U*(M^4/(H:ℝ)^2)+
        1024*U*((M^3/(H:ℝ)^3)*Z) := by gcongr
    _ ≤ 4096*U*(M^4/(H:ℝ)^2+(M^3/(H:ℝ)^3)*Z) := by
      nlinarith only [hDiag0,hCorr0,
        mul_le_mul_of_nonneg_right hU hDiag0,mul_nonneg (zero_le_one.trans hU) hCorr0]
    _ = _ := by
      dsimp only [A,U]
      ring

example
    {ε : ℝ} (hε : 0<ε) :
    ∃ A : ℝ, 1≤A ∧
      ∀ (F : ℝ → ℝ) (σ X M : ℝ) (a L H : ℕ),
        0<σ → 1≤X → 1≤M → 2≤H → H^2≤L+1 →
        (H:ℝ)^3≤X → ((H:ℝ)+(H:ℝ)^2)/M≤1/4 →
        M≤(a:ℝ) → ((a+L:ℕ):ℝ)≤2*M →
        let Pairs := (Finset.Icc 1 (H-1)) ×ˢ (Finset.Icc 1 (H^2-1))
        let Products := Pairs.image (fun p => p.1*p.2)
        let W := fun p : ℕ × ℕ => ∑ j∈Finset.range (L+1-p.1-p.2),
          (𝐞 (X*(F (((a:ℝ)+j)/M)-F (((a:ℝ)+j+p.1)/M)-
            F (((a:ℝ)+j+p.2)/M)+F (((a:ℝ)+j+p.1+p.2)/M))):ℂ)
        ∃ (pick : ℕ → ℕ × ℕ) (k : ℕ), 0<k ∧ 2*k≤H^3 ∧
          (∀ l∈Products, pick l∈Pairs ∧ (pick l).1*(pick l).2=l ∧
            ∀ p∈Pairs, p.1*p.2=l → ‖W p‖≤‖W (pick l)‖) ∧
          (∑ l∈(Finset.Ico k (2*k)).filter (fun l => l∈Products),‖W (pick l)‖)≤2*M*k ∧
          ‖Expdb.exponentialSumAt F X M a (a+L)‖^4 ≤
            A*X^ε*(1+(Nat.clog 2 (H^3):ℝ))*
              (M^4/(H:ℝ)^2+(M^3/(H:ℝ)^3)*
                (∑ l∈(Finset.Ico k (2*k)).filter (fun l => l∈Products),‖W (pick l)‖)) := by
  exact source_product_twice_weyl_normalized_block hε

#print axioms source_product_twice_weyl_normalized_block

/-- Combine the two-step fourth-power bound with the actual family's
twelfth moment and its weighted physical monomials. These explicit
upstream inequalities are consumed, not packaged as the final bound. -/
private theorem double_difference_fourth_twelfth_moment_assembly
    {S Z d w Main E V C X ε Q : ℝ}
    (hS : 0≤S) (hZ : 0≤Z) (hd : 0≤d) (hw : 0≤w)
    (hMain : 0≤Main) (hE : 0≤E) (hC : 1≤C) (hX : 1≤X)
    (hε : 0≤ε) (hQ : 0≤Q)
    (hWeyl : S^4≤Q*(d+w*Z))
    (hMoment : Z^12≤C*X^ε*(Main+E^12))
    (hWeighted : w^72*(E^72+Main^6)≤(2:ℝ)^288*V) :
    S^288≤(2:ℝ)^364*Q^72*C^6*X^(6*ε)*(d^72+V) := by
  have hXp := zero_lt_one.trans_le hX
  have hC0 := zero_le_one.trans hC
  have hPower : 1≤X^(6*ε) := Real.one_le_rpow hX (by positivity)
  have hCoeff : 1≤(2:ℝ)^293*C^6*X^(6*ε) :=
    one_le_mul_of_one_le_of_one_le
      (one_le_mul_of_one_le_of_one_le (one_le_pow₀ (by norm_num : (1:ℝ)≤2))
        (one_le_pow₀ hC)) hPower
  have hZ72 : Z^72≤32*C^6*X^(6*ε)*(Main^6+E^72) := by
    calc
      _ = (Z^12)^6 := by rw [←pow_mul]
      _ ≤ (C*X^ε*(Main+E^12))^6 :=
        pow_le_pow_left₀ (pow_nonneg hZ 12) hMoment 6
      _ = C^6*X^(6*ε)*(Main+E^12)^6 := by
        rw [mul_pow,mul_pow]
        have hp : (X^ε)^6=X^(6*ε) := by
          simpa only [Nat.cast_ofNat,mul_comm] using (Real.rpow_mul_natCast hXp.le ε 6).symm
        rw [hp]
      _ ≤ C^6*X^(6*ε)*((2:ℝ)^5*(Main^6+(E^12)^6)) :=
        mul_le_mul_of_nonneg_left (add_pow_le hMain (pow_nonneg hE 12) 6) (by positivity)
      _ = _ := by rw [←pow_mul]; norm_num; ring
  have hZweighted : w^72*Z^72≤(2:ℝ)^293*C^6*X^(6*ε)*V := by
    calc
      _ ≤ w^72*(32*C^6*X^(6*ε)*(Main^6+E^72)) :=
        mul_le_mul_of_nonneg_left hZ72 (pow_nonneg hw 72)
      _ = 32*C^6*X^(6*ε)*(w^72*(E^72+Main^6)) := by ring
      _ ≤ 32*C^6*X^(6*ε)*((2:ℝ)^288*V) :=
        mul_le_mul_of_nonneg_left hWeighted (by positivity)
      _ = _ := by
        rw [show (2:ℝ)^293=32*2^288 by
          rw [show (293:ℕ)=5+288 by rfl,pow_add,show (2:ℝ)^5=32 by norm_num]]
        have heq (a b c d : ℝ) : 32*a*b*(c*d)=(32*c)*a*b*d := by ring
        exact heq _ _ _ _
  have hDiag : d^72≤(2:ℝ)^293*C^6*X^(6*ε)*d^72 :=
    le_mul_of_one_le_left (pow_nonneg hd 72) hCoeff
  calc
    _ = (S^4)^72 := by rw [←pow_mul]
    _ ≤ (Q*(d+w*Z))^72 := pow_le_pow_left₀ (pow_nonneg hS 4) hWeyl 72
    _ = Q^72*(d+w*Z)^72 := mul_pow _ _ _
    _ ≤ Q^72*((2:ℝ)^71*(d^72+(w*Z)^72)) :=
      mul_le_mul_of_nonneg_left (add_pow_le hd (mul_nonneg hw hZ) 72) (pow_nonneg hQ 72)
    _ = (2:ℝ)^71*Q^72*(d^72+w^72*Z^72) := by
      rw [mul_pow]
      exact (mul_left_comm _ _ _).trans (mul_assoc _ _ _).symm
    _ ≤ (2:ℝ)^71*Q^72*((2:ℝ)^293*C^6*X^(6*ε)*d^72+
        (2:ℝ)^293*C^6*X^(6*ε)*V) :=
      mul_le_mul_of_nonneg_left (add_le_add hDiag hZweighted)
        (mul_nonneg (pow_nonneg (by norm_num : (0:ℝ)≤2) 71) (pow_nonneg hQ 72))
    _ = _ := by
      rw [show (2:ℝ)^364=2^71*2^293 by rw [←pow_add]]
      have heq (a b c d e f g : ℝ) :
          a*b*(c*d*e*f+c*d*e*g)=(a*c)*b*d*e*(f+g) := by ring
      exact heq _ _ _ _ _ _ _

example
    {S Z d w Main E V C X ε Q : ℝ}
    (hS : 0≤S) (hZ : 0≤Z) (hd : 0≤d) (hw : 0≤w)
    (hMain : 0≤Main) (hE : 0≤E) (hC : 1≤C) (hX : 1≤X)
    (hε : 0≤ε) (hQ : 0≤Q)
    (hWeyl : S^4≤Q*(d+w*Z))
    (hMoment : Z^12≤C*X^ε*(Main+E^12))
    (hWeighted : w^72*(E^72+Main^6)≤(2:ℝ)^288*V) :
    S^288≤(2:ℝ)^364*Q^72*C^6*X^(6*ε)*(d^72+V) := by
  exact double_difference_fourth_twelfth_moment_assembly hS hZ hd hw hMain hE hC hX hε hQ
    hWeyl hMoment hWeighted

#print axioms double_difference_fourth_twelfth_moment_assembly

private theorem middleOriginal_eventually_uniform_clog_power_loss_72
    {C ζ : ℝ} (hC : 0≤C) (hζ : 0<ζ) :
    ∀ᶠ X : ℝ in Filter.atTop, ∀ H : ℕ, 2≤H → (H:ℝ)≤X →
      C*(1+(Nat.clog 2 H:ℝ))^72≤X^ζ := by
  have hlog2 : 0<Real.log 2 := Real.log_pos (by norm_num)
  let D := 1+2/Real.log 2
  have hD : 0≤D := by dsimp only [D]; positivity
  have hLoss := eventually_const_log_pow_le_rpow
    (C*D^72) (mul_nonneg hC (pow_nonneg hD 72)) 72 hζ
  filter_upwards [hLoss,Real.tendsto_log_atTop.eventually_ge_atTop 1,
    Filter.eventually_ge_atTop (1:ℝ)] with X hLossX hlogX hX
  intro H hH hHX
  have hHp : (0:ℝ)<H := by exact_mod_cast (show 0<H by omega)
  have hlogHX := Real.log_le_log hHp hHX
  have hc : (Nat.clog 2 H:ℝ)≤(2/Real.log 2)*Real.log X := by
    calc
      _ ≤ 2*(Real.log H/Real.log 2) := nat_clog_two_le_twice_log H hH
      _ ≤ 2*(Real.log X/Real.log 2) := mul_le_mul_of_nonneg_left
        (div_le_div_of_nonneg_right hlogHX hlog2.le) (by norm_num)
      _ = _ := by ring
  have hplus : 1+(Nat.clog 2 H:ℝ)≤D*Real.log X := by
    dsimp only [D]
    nlinarith only [hc,hlogX]
  calc
    _ ≤ C*(D*Real.log X)^72 := mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (by positivity) hplus 72) hC
    _ = (C*D^72)*(Real.log X)^72 := by rw [mul_pow,mul_assoc]
    _ ≤ X^ζ := hLossX

example
    {C ζ : ℝ} (hC : 0≤C) (hζ : 0<ζ) :
    ∀ᶠ X : ℝ in Filter.atTop, ∀ H : ℕ, 2≤H → (H:ℝ)≤X →
      C*(1+(Nat.clog 2 H:ℝ))^72≤X^ζ := by
  exact middleOriginal_eventually_uniform_clog_power_loss_72 hC hζ

#print axioms middleOriginal_eventually_uniform_clog_power_loss_72

open scoped NNReal

/-- The original approximate-model sum on the fourth-pair supporting-line
interval, with a genuine two-sided M window, all selected product blocks,
the sharp extension loss and every source logarithm discharged. -/
private theorem fourth_pair_capped_short_nonAsymptotic
    {α : ℝ≥0} {t : ℝ} (ht : t∈Icc (0:ℝ) 1)
    (hα : (α:ℝ)=(1-t)*(890/3277)+t*(17604372/60424193)) :
    Expdb.IsExponentSumBoundNonAsymptotic α (89/3478+(7441/8695)*(α:ℝ)) := by
  let h := ((1-t)*2749411+t*3296917)/100000000
  let g₀ := ((1-t)*16756+t*1976824)/100000000
  let ν₀ := ((1-t)*11931645+t*14567321)/100000000
  let ν₁ := ((1-t)*11969967+t*14925729)/100000000
  let g := fun u : ℝ => (1-u)*g₀+u*(3*h)
  let ν := fun u : ℝ => (1-u)*ν₀+u*ν₁
  let β := 89/3478+(7441/8695)*(α:ℝ)
  let δw := (1:ℝ)/10000000000
  let ℓ := (α:ℝ)-δw
  let v := (α:ℝ)+δw
  let μ := (1:ℝ)/1000000
  let εs := μ/1000
  let ζ := μ/2
  let ξ := 288*β-μ
  have hμ : 0<μ := by norm_num [μ]
  have hεs : 0<εs := by dsimp only [εs]; positivity
  have hζ : 0<ζ := by dsimp only [ζ]; positivity
  have hδw : 0<δw := by norm_num [δw]
  have hMargins (u : ℝ) (hu : u∈Icc (0:ℝ) 1) :
      μ≤ℓ ∧
        v+μ≤1 ∧
        μ≤h ∧
        μ≤(ν u) ∧
        μ≤g₀ ∧
        5*h+μ≤ℓ ∧
        g₀+μ≤3*h ∧
        (ν u)+μ≤ℓ ∧
        5*v-1-(g u)+μ≤3*(ν u) ∧
        1+(g u)+2*(ν u)+μ≤5*ℓ ∧
        4*(ν u)+1+(g u)+μ≤6*ℓ ∧
        (ν u)+3*v+μ≤1+(g u) ∧
        1+(g u)+μ≤4*ℓ ∧
        3*v+μ≤1+(g u) ∧
        7*v+μ≤2+2*(g u)+(ν u) ∧
        7+7*(g u)+27*(ν u)+μ≤41*ℓ ∧
        2*h+μ≤β ∧
        4*v+g₀-3*h+μ≤4*β ∧
        288*v-144*h+μ≤288*β ∧
        288*v-36*(ν u)+72*(g u)-216*h+μ≤288*β ∧
        648*v-72-216*h-216*(ν u)+μ≤288*β ∧
        24+96*(g u)-216*h+96*v+144*(ν u)+μ≤288*β ∧
        21+87*(g u)-216*h+177*v+33*(ν u)+μ≤288*β ∧
        15+87*(g u)-216*h+207*v+15*(ν u)+μ≤288*β ∧
        12+78*(g u)-216*h+216*v+24*(ν u)+μ≤288*β ∧
        6+78*(g u)-216*h+246*v+6*(ν u)+μ≤288*β ∧
        72*(g u)-216*h+284*v-24*(ν u)+μ≤288*β ∧
        504*v-72-216*h+72*(ν u)+μ≤288*β := by
    have hh := fourth_pair_capped_full_window_margins ht hu
    dsimp only at hh
    rw [←hα] at hh
    exact hh
  have hzero := hMargins 0 (by norm_num)
  simp only [g,ν,sub_zero,zero_mul,one_mul,add_zero] at hzero
  obtain ⟨hμℓ,hv,hμh,hμν₀,hμg₀,hWidth,hg₀h,hν₀M,hRN₀,hNR₀,hCubic₀,hCap₀,
    hHeight₀,hMT₀,hRT₀,hTen₀,hShort,hSmall,hDiag,hSqrt₀,hSecond₀,hFourth₀,
    hSecondMain₀,hFourthMain₀,hFirstMain₀,hThirdMain₀,hFifthMain₀,hThird₀⟩ := hzero
  have hℓv : ℓ≤v := by dsimp only [ℓ,v]; linarith only [hδw]
  have hhp := hμ.trans_le hμh
  have hℓp := hμ.trans_le hμℓ
  have hg₀p := hμ.trans_le hμg₀
  have hβ : 0<β := by linarith only [hShort,hhp,hμ]
  have hξ : 0≤ξ := by dsimp only [ξ]; linarith only [hShort,hhp,hμ]
  have hh3 : 3*h≤1 := by linarith only [hWidth,hℓv,hv,hhp,hμ]
  intro ε hε σ hσ
  obtain ⟨δsrc,w₀,B,Csrc,hδsrc,hw₀,hw₀cap,hB,hCsrc,hSource⟩ :=
    approximateModelPhase_enlarged_double_product_correlation_moment hσ hεs
  obtain ⟨A,hA,hWeylSource⟩ := source_product_twice_weyl_normalized_block hεs
  let Clarge := (2:ℝ)^364*A^72*Csrc^6*(11*2^432)
  let Csmall := (20*A)^72
  let D := 1+Clarge+Csmall
  let Ctotal := (2:ℝ)^287*((6:ℝ)^288+D)
  have hA0 := zero_le_one.trans hA
  have hCsrc0 := zero_le_one.trans hCsrc
  have hClarge : 0≤Clarge := by
    dsimp only [Clarge]
    clear * - hA0 hCsrc0
    positivity
  have hCsmall : 0≤Csmall := by
    dsimp only [Csmall]
    clear * - hA0
    positivity
  have hD : 1≤D := (le_add_of_nonneg_right hClarge).trans (le_add_of_nonneg_right hCsmall)
  have hLargeD : Clarge≤D :=
    (le_add_of_nonneg_left (by norm_num : (0:ℝ)≤1)).trans (le_add_of_nonneg_right hCsmall)
  have hSmallD : Csmall≤D := le_add_of_nonneg_left (add_nonneg zero_le_one hClarge)
  have hCtotal : 0≤Ctotal := by
    dsimp only [Ctotal]
    exact mul_nonneg (pow_nonneg (by norm_num : (0:ℝ)≤2) 287)
      (add_nonneg (pow_nonneg (by norm_num : (0:ℝ)≤6) 288) (zero_le_one.trans hD))
  have hPhys := eventually_double_difference_capped_physical_window
    hB hCsrc hw₀ hμ hμℓ hℓv hμh hWidth
  have hLog := middleOriginal_eventually_uniform_clog_power_loss_72 hCtotal hζ
  obtain ⟨X₀,hX₀⟩ := Filter.eventually_atTop.mp (hPhys.and hLog)
  let δ := min δsrc δw
  let C := max 1 X₀
  have hC : 1≤C := le_max_left _ _
  refine ⟨δ,lt_min hδsrc hδw,7,by norm_num,C,hC,?_⟩
  intro X M F a b setup
  have hTogether := hX₀ X ((le_max_right 1 X₀).trans setup.threshold_le_param)
  have hX2 := hTogether.1.1
  have hX : 1≤X := (by norm_num : (1:ℝ)≤2).trans hX2
  have hXp := zero_lt_one.trans_le hX
  have hMl : X^ℓ≤M :=
    (Real.rpow_le_rpow_of_exponent_le hX
      (sub_le_sub_left (min_le_right δsrc δw) _)).trans setup.rpow_sub_le_scale
  have hMu : M≤X^v := setup.scale_le_rpow_add.trans
    (Real.rpow_le_rpow_of_exponent_le hX (add_le_add le_rfl (min_le_right δsrc δw)))
  have hF := approximateModelPhase_mono setup.isApproximateModelPhase le_rfl (min_le_left δsrc δw)
  have hBasePhys := hTogether.1.2 M (X^g₀) g₀ ν₀ hMl hMu rfl hg₀p.le
    (by linarith only [hg₀h,hμ]) hμν₀ hν₀M hRN₀ hNR₀ hCubic₀ hCap₀ hHeight₀ hMT₀ hRT₀ hTen₀
  let H := ⌊X^h⌋₊
  obtain ⟨hM,hN₀2,hH2,hN₀l,hN₀u,hHl,hHu,hJ₀,hR₀,hscale₀,hThreshold₀,hW,
    hJ₀M,hWJ₀,hR₀B,hR₀N,hN₀R,hN₀M,hCubicBudget₀,hCapBudget₀,hHeightBudget₀,
    hMTBudget₀,hRTBudget₀,hTenBudget₀⟩ := hBasePhys
  have hMp := zero_lt_one.trans_le hM
  have hHp : (0:ℝ)<H := by exact_mod_cast (show 0<H by omega)
  have hH1 : (1:ℝ)≤H := by exact_mod_cast (show 1≤H by omega)
  have hHcube : (H:ℝ)^3≤X := by
    calc
      _ ≤ (X^h)^3 := pow_le_pow_left₀ hHp.le hHu 3
      _ = X^(3*h) := by
        simpa only [Nat.cast_ofNat,mul_comm] using (Real.rpow_mul_natCast hXp.le h 3).symm
      _ ≤ X := by simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hX hh3
  suffices hResult : ‖Expdb.exponentialSumAt F X M a b‖≤X^β by
    calc
      _ ≤ X^β := hResult
      _ ≤ X^(β+ε) := Real.rpow_le_rpow_of_exponent_le hX (le_add_of_nonneg_right hε.le)
      _ ≤ C*X^(β+ε) := le_mul_of_one_le_left (Real.rpow_nonneg hXp.le _) hC
  by_cases hba : b<a
  · rw [Expdb.exponentialSumAt_of_lt hba,norm_zero]
    exact Real.rpow_nonneg hXp.le _
  have hab : a≤b := Nat.le_of_not_gt hba
  let L := b-a
  have hEnd : a+L=b := Nat.add_sub_of_le hab
  have ha := setup.scale_le_start
  have hb : ((a+L:ℕ):ℝ)≤2*M := by rw [hEnd]; exact setup.end_le_two_mul_scale
  by_cases hShortL : L+1<H^2
  · calc
      _ ≤ ((Finset.Icc a b).card:ℝ) := Expdb.norm_exponentialSumAt_le_card F X M a b
      _ = (L:ℝ)+1 := by
        have hc : (Finset.Icc a b).card=L+1 := by rw [Nat.card_Icc]; dsimp only [L]; omega
        exact_mod_cast hc
      _ ≤ (H:ℝ)^2 := by exact_mod_cast hShortL.le
      _ ≤ (X^h)^2 := pow_le_pow_left₀ hHp.le hHu 2
      _ = X^(2*h) := by
        simpa only [Nat.cast_ofNat,mul_comm] using (Real.rpow_mul_natCast hXp.le h 2).symm
      _ ≤ X^β := Real.rpow_le_rpow_of_exponent_le hX (by linarith only [hShort,hμ])
  have hLong : H^2≤L+1 := Nat.le_of_not_gt hShortL
  obtain ⟨Fext,hSharp,hFamily⟩ := hSource M F hM hF
  obtain ⟨pick,k,hk,hkH,hpick,hZcap,hWeyl⟩ :=
    hWeylSource Fext σ X M a L H hσ hX hM hH2 hLong hHcube (hW.trans hw₀cap) ha hb
  let J := (k:ℝ)
  let Pairs := (Finset.Icc 1 (H-1)) ×ˢ (Finset.Icc 1 (H^2-1))
  let Products := Pairs.image (fun p => p.1*p.2)
  let W := fun p : ℕ × ℕ => ∑ j∈Finset.range (L+1-p.1-p.2),
    (𝐞 (X*(Fext (((a:ℝ)+j)/M)-Fext (((a:ℝ)+j+p.1)/M)-
      Fext (((a:ℝ)+j+p.2)/M)+Fext (((a:ℝ)+j+p.1+p.2)/M))):ℂ)
  let Z := ∑ l∈(Finset.Ico k (2*k)).filter (fun l => l∈Products),‖W (pick l)‖
  let Log := 1+(Nat.clog 2 (H^3):ℝ)
  have hZ0 : 0≤Z := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  have hLog1 : 1≤Log := le_add_of_nonneg_right (Nat.cast_nonneg _)
  have hLog0 := zero_le_one.trans hLog1
  have hLog72 : 1≤Log^72 := one_le_pow₀ hLog1
  have hJp : 0<J := by change (0:ℝ)<k; exact_mod_cast hk
  have hJH : J≤(H:ℝ)^3 := by
    change (k:ℝ)≤(H:ℝ)^3
    exact_mod_cast (show k≤H^3 by omega)
  have hQ : 0≤A*X^εs*Log :=
    mul_nonneg (mul_nonneg hA0 (Real.rpow_nonneg hXp.le _)) hLog0
  have hξPower : 1≤X^ξ := Real.one_le_rpow hX hξ
  have hLossPower : 1≤X^(78*εs) := Real.one_le_rpow hX (by positivity)
  have hCommon :
      ‖Expdb.exponentialSumAt Fext X M a (a+L)‖^288 ≤ D*Log^72*X^(78*εs)*X^ξ := by
    by_cases hSmallJ : J≤X^g₀
    · have hdPower : M^4/(H:ℝ)^2≤4*X^(ξ/72) := by
        have hh := double_difference_monomial_power_window hX hMl hMu hN₀l hN₀u hHl
          (rfl : X^g₀=X^g₀) 0 0 4 0 0 2 0 0 0
        norm_num only [Nat.cast_zero,Nat.cast_ofNat,pow_zero,pow_one,zero_mul,one_mul,
          mul_one,zero_add,add_zero,sub_zero] at hh
        have hexp : 4*v-2*h≤ξ/72 := by
          apply (le_div_iff₀ (by norm_num : (0:ℝ)<72)).mpr
          calc
            (4*v-2*h)*72 = 288*v-144*h := by ring
            _ ≤ 288*β-μ := (le_sub_iff_add_le).mpr hDiag
        exact hh.trans (mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_exponent_le hX hexp)
          (by norm_num))
      have hSmallPower : M^4*J/(H:ℝ)^3≤8*X^(ξ/72) := by
        have hh := double_difference_monomial_power_window hX hMl hMu hN₀l hN₀u hHl
          (rfl : X^g₀=X^g₀) 0 1 4 0 0 3 0 0 0
        norm_num only [Nat.cast_zero,Nat.cast_ofNat,pow_zero,pow_one,zero_mul,one_mul,
          mul_one,zero_add,add_zero,sub_zero] at hh
        calc
          _ ≤ M^4*(X^g₀)/(H:ℝ)^3 := by gcongr
          _ = (X^g₀)*M^4/(H:ℝ)^3 := by rw [mul_comm (M^4)]
          _ ≤ 8*X^(g₀+4*v-3*h) := hh
          _ ≤ 8*X^(ξ/72) := mul_le_mul_of_nonneg_left
            (Real.rpow_le_rpow_of_exponent_le hX (by
              apply (le_div_iff₀ (by norm_num : (0:ℝ)<72)).mpr
              calc
                (g₀+4*v-3*h)*72 = (4*v+g₀-3*h)*72 := by ring
                _ ≤ (4*β-μ)*72 := mul_le_mul_of_nonneg_right
                  ((le_sub_iff_add_le).mpr hSmall) (by norm_num)
                _ ≤ 288*β-μ := by nlinarith only [hμ])) (by norm_num)
      have hCorr : (M^3/(H:ℝ)^3)*Z≤16*X^(ξ/72) := by
        calc
          _ ≤ (M^3/(H:ℝ)^3)*(2*M*J) := mul_le_mul_of_nonneg_left hZcap (by positivity)
          _ = 2*(M^4*J/(H:ℝ)^3) := by ring
          _ ≤ 2*(8*X^(ξ/72)) := mul_le_mul_of_nonneg_left hSmallPower (by norm_num)
          _ = _ := by ring
      have hFourth :
          ‖Expdb.exponentialSumAt Fext X M a (a+L)‖^4≤
            (20*A)*Log*X^εs*X^(ξ/72) := by
        calc
          _ ≤ A*X^εs*Log*(M^4/(H:ℝ)^2+(M^3/(H:ℝ)^3)*Z) := hWeyl
          _ ≤ A*X^εs*Log*(4*X^(ξ/72)+16*X^(ξ/72)) :=
            mul_le_mul_of_nonneg_left (add_le_add hdPower hCorr) hQ
          _ = _ := by ring
      have hpε : (X^εs)^72=X^(72*εs) := by
        simpa only [Nat.cast_ofNat,mul_comm] using (Real.rpow_mul_natCast hXp.le εs 72).symm
      have hpξ : (X^(ξ/72))^72=X^ξ := by
        have hh := (Real.rpow_mul_natCast hXp.le (ξ/72) 72).symm
        norm_num only [Nat.cast_ofNat,div_mul_cancel₀ _ (by norm_num : (72:ℝ)≠0)] at hh
        exact hh
      calc
        _ = (‖Expdb.exponentialSumAt Fext X M a (a+L)‖^4)^72 := by rw [←pow_mul]
        _ ≤ ((20*A)*Log*X^εs*X^(ξ/72))^72 :=
          pow_le_pow_left₀ (pow_nonneg (norm_nonneg _) 4) hFourth 72
        _ = Csmall*Log^72*X^(72*εs)*X^ξ := by
          simp only [mul_pow,hpε,hpξ,Csmall]
        _ ≤ D*Log^72*X^(78*εs)*X^ξ := by
          gcongr
          norm_num
    · let γ := Real.logb X J
      have hXgt : 1<X := by linarith only [hX2]
      have hJpow : J=X^γ := (Real.rpow_logb hXp hXgt.ne' hJp).symm
      have hγlo : g₀≤γ :=
        (Real.le_logb_iff_rpow_le hXgt hJp).mpr (le_of_not_ge hSmallJ)
      have hγhi : γ≤3*h := by
        apply (Real.logb_le_iff_le_rpow hXgt hJp).mpr
        calc
          J ≤ (H:ℝ)^3 := hJH
          _ ≤ (X^h)^3 := pow_le_pow_left₀ hHp.le hHu 3
          _ = X^(3*h) := by
            simpa only [Nat.cast_ofNat,mul_comm] using (Real.rpow_mul_natCast hXp.le h 3).symm
      have hDen : 0<3*h-g₀ := by linarith only [hg₀h,hμ]
      let u := (γ-g₀)/(3*h-g₀)
      have hu : u∈Icc (0:ℝ) 1 := by
        refine ⟨div_nonneg (sub_nonneg.mpr hγlo) hDen.le,?_⟩
        exact (div_le_one hDen).mpr (by linarith only [hγhi])
      have hgu : g u=γ := by
        dsimp only [g,u]
        field_simp
        ring
      have hm := hMargins u hu
      rw [hgu] at hm
      obtain ⟨_,_,_,hμν,_,_,_,hνM,hRN,hNR,hCubic,hCap,hHeight,hMT,hRT,hTen,
        _,_,hDiag',hSqrt,hSecond,hFourth,hSecondMain,hFourthMain,hFirstMain,hThirdMain,hFifthMain,hThird⟩ := hm
      let n := ⌊X^(ν u)/8⌋₊
      let N := 8*n
      let R := Real.sqrt (M^5/(X*J*(N:ℝ)))
      let T := X*J/M^2
      have hPhysical := hTogether.1.2 M J γ (ν u) hMl hMu hJpow
        (hg₀p.le.trans hγlo) hγhi hμν hνM hRN hNR hCubic hCap hHeight hMT hRT hTen
      obtain ⟨_,hN2,_,hNl,hNu,_,_,hJ1,hRp,hscale,hThreshold,hWidthJ,hJM,hWJ,
        hBR,hRNbudget,hNRbudget,hNMbudget,hCubicBudget,hCapBudget,hHeightBudget,
        hMTbudget,hRTbudget,hTenBudget⟩ := hPhysical
      have hNp : (0:ℝ)<N := by exact_mod_cast (show 0<N by omega)
      have hTp : 0<T := by dsimp only [T]; positivity
      have hTX : T≤X := by
        apply (div_le_iff₀ (sq_pos_of_pos hMp)).mpr
        have hJM2 : J≤M^2 := hJM.trans (by nlinarith only [hM])
        nlinarith only [mul_le_mul_of_nonneg_left hJM2 hXp.le]
      let E := J*M/Real.sqrt (N:ℝ)+J*M*R^2/(N:ℝ)^2+J*(N:ℝ)^2*R^2/M+
        J*(N:ℝ)*((N:ℝ)/R)^((2:ℝ)/3)
      let Main := J^11*M^10*(N:ℝ)^2/R^4+J^11*M^11*(N:ℝ)^2/R^7+
        J^11*J*M^10/R^2+J^11*J*M^11/R^5+
        J^12*M^10*R^2/(N:ℝ)^2*(R/(N:ℝ))^((2:ℝ)/3)*((X*J/M^2)/M^2)^((4:ℝ)/3)
      let V :=
        (J^72*M^288/((H:ℝ)^216*(N:ℝ)^36)+M^648/(X^72*(H:ℝ)^216*(N:ℝ)^216)+
          M^504*(N:ℝ)^72/(X^72*(H:ℝ)^216)+X^24*J^96*M^96*(N:ℝ)^144/(H:ℝ)^216)+
        (X^12*J^78*M^216*(N:ℝ)^24/(H:ℝ)^216+X^21*J^87*M^177*(N:ℝ)^33/(H:ℝ)^216+
          X^6*J^78*M^246*(N:ℝ)^6/(H:ℝ)^216+X^15*J^87*M^207*(N:ℝ)^15/(H:ℝ)^216+
          J^72*M^284/((H:ℝ)^216*(N:ℝ)^24))
      have hE0 : 0≤E := by
        dsimp only [E]
        clear * - hJp hMp hNp hRp
        positivity
      have hMain0 : 0≤Main := by
        dsimp only [Main]
        clear * - hJp hMp hNp hRp hXp
        positivity
      have hFamilyMoment : Z^12≤Csrc*T^εs*(Main+E^12) := by
        exact hFamily X n N a L H (H^2) k R hThreshold rfl hN2 hBR hk
          (by simpa only [Nat.cast_pow] using hWidthJ) hJM
          (by simpa only [Nat.cast_pow] using hWJ) ha hb hscale
          hRNbudget hNRbudget hNMbudget hCubicBudget hCapBudget hHeightBudget
          hMTbudget hRTbudget hTenBudget pick (fun l hl => ⟨(hpick l hl).1,(hpick l hl).2.1⟩)
      have hMoment : Z^12≤Csrc*X^εs*(Main+E^12) := hFamilyMoment.trans
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hTp.le hTX hεs.le) hCsrc0)
          (add_nonneg hMain0 (pow_nonneg hE0 12)))
      have hWeighted : (M^3/(H:ℝ)^3)^72*(E^72+Main^6)≤(2:ℝ)^288*V :=
        double_difference_weighted_capped_integer_moments hXp hMp hNp hJp hHp hRp hscale
      have hPower := double_difference_fourth_twelfth_moment_assembly
        (norm_nonneg _) hZ0 (div_nonneg (pow_nonneg hMp.le 4) (pow_nonneg hHp.le 2))
        (div_nonneg (pow_nonneg hMp.le 3) (pow_nonneg hHp.le 3)) hMain0 hE0 hCsrc hX hεs.le hQ
        hWeyl hMoment hWeighted
      have hPoly : 1+(M^288/(H:ℝ)^144+V)≤(11*(2:ℝ)^432)*X^ξ :=
        double_difference_ten_monomials_power_window hX hξ hMl hMu hNl hNu hHl hJpow
          (by dsimp only [ξ]; linarith only [hDiag'])
          (by dsimp only [ξ]; linarith only [hSqrt])
          (by dsimp only [ξ]; linarith only [hSecond])
          (by dsimp only [ξ]; linarith only [hThird])
          (by dsimp only [ξ]; linarith only [hFourth])
          (by dsimp only [ξ]; linarith only [hFirstMain])
          (by dsimp only [ξ]; linarith only [hSecondMain])
          (by dsimp only [ξ]; linarith only [hThirdMain])
          (by dsimp only [ξ]; linarith only [hFourthMain])
          (by dsimp only [ξ]; linarith only [hFifthMain])
      have hPoly' : M^288/(H:ℝ)^144+V≤(11*(2:ℝ)^432)*X^ξ :=
        (le_add_of_nonneg_left (by norm_num : (0:ℝ)≤1)).trans hPoly
      have hPowers :
          (2:ℝ)^364*(A*X^εs*Log)^72*Csrc^6*X^(6*εs)*
              ((M^4/(H:ℝ)^2)^72+V)=
            ((2:ℝ)^364*A^72*Csrc^6)*Log^72*X^(78*εs)*(M^288/(H:ℝ)^144+V) := by
        simp only [mul_pow,div_pow,←pow_mul]
        have hεpower : (X^εs)^72=X^(72*εs) := by
          simpa only [Nat.cast_ofNat,mul_comm] using (Real.rpow_mul_natCast hXp.le εs 72).symm
        rw [hεpower]
        have hcombine : X^(72*εs)*X^(6*εs)=X^(78*εs) := by
          rw [←Real.rpow_add hXp]
          congr 1
          ring
        have heq (a b c d e f z : ℝ) : a*(b*c*d)*e*f*z=(a*b*e)*d*(c*f)*z := by ring
        rw [heq,hcombine]
      calc
        _ ≤ ((2:ℝ)^364*A^72*Csrc^6)*Log^72*X^(78*εs)*(M^288/(H:ℝ)^144+V) :=
          hPower.trans_eq hPowers
        _ ≤ ((2:ℝ)^364*A^72*Csrc^6)*Log^72*X^(78*εs)*((11*(2:ℝ)^432)*X^ξ) :=
          mul_le_mul_of_nonneg_left hPoly' (by
            clear * - hA0 hCsrc0 hLog0 hXp
            positivity)
        _ = Clarge*Log^72*X^(78*εs)*X^ξ := by
          dsimp only [Clarge]
          have heq (a b c d e f z : ℝ) : (a*b*c)*d*e*(f*z)=(a*b*c*f)*d*e*z := by ring
          exact heq _ _ _ _ _ _ _
        _ ≤ D*Log^72*X^(78*εs)*X^ξ := by gcongr
  have hSharp' := hSharp X a (a+L) ha hb
  have hOriginal : ‖Expdb.exponentialSumAt F X M a (a+L)‖≤
      6+‖Expdb.exponentialSumAt Fext X M a (a+L)‖ :=
    (norm_le_norm_sub_add _ _).trans (add_le_add hSharp' le_rfl)
  have hY : 1≤Log^72*X^(78*εs)*X^ξ :=
    one_le_mul_of_one_le_of_one_le
      (one_le_mul_of_one_le_of_one_le hLog72 hLossPower) hξPower
  have hSix : (6:ℝ)^288≤(6:ℝ)^288*(Log^72*X^(78*εs)*X^ξ) :=
    le_mul_of_one_le_right (pow_nonneg (by norm_num : (0:ℝ)≤6) 288) hY
  have hFinalPower : ‖Expdb.exponentialSumAt F X M a (a+L)‖^288≤X^(288*β) := by
    have hLogLoss : Ctotal*Log^72≤X^ζ :=
      hTogether.2 (H^3)
        ((by norm_num : (2:ℕ)≤2^3).trans (Nat.pow_le_pow_left (show 2≤H from hH2) 3))
        (by exact_mod_cast hHcube)
    calc
      _ ≤ (6+‖Expdb.exponentialSumAt Fext X M a (a+L)‖)^288 :=
        pow_le_pow_left₀ (norm_nonneg _) hOriginal 288
      _ ≤ (2:ℝ)^287*((6:ℝ)^288+‖Expdb.exponentialSumAt Fext X M a (a+L)‖^288) :=
        add_pow_le (by norm_num : (0:ℝ)≤6) (norm_nonneg _) 288
      _ ≤ (2:ℝ)^287*((6:ℝ)^288*(Log^72*X^(78*εs)*X^ξ)+
          D*Log^72*X^(78*εs)*X^ξ) :=
        mul_le_mul_of_nonneg_left (add_le_add hSix hCommon)
          (pow_nonneg (by norm_num : (0:ℝ)≤2) 287)
      _ = (Ctotal*Log^72)*X^(78*εs)*X^ξ := by
        dsimp only [Ctotal]
        have heq (a b c d e f : ℝ) : a*(b*(d*e*f)+c*d*e*f)=((a*(b+c))*d)*e*f := by ring
        exact heq _ _ _ _ _ _
      _ ≤ X^ζ*X^(78*εs)*X^ξ :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hLogLoss (Real.rpow_nonneg hXp.le _))
          (Real.rpow_nonneg hXp.le _)
      _ = X^(ζ+78*εs+ξ) := by rw [←Real.rpow_add hXp,←Real.rpow_add hXp]
      _ ≤ X^(288*β) := Real.rpow_le_rpow_of_exponent_le hX (by
        dsimp only [ζ,εs,ξ]
        linarith only [hμ])
  have hRootPower : (X^β)^288=X^(288*β) := by
    simpa only [Nat.cast_ofNat,mul_comm] using (Real.rpow_mul_natCast hXp.le β 288).symm
  rw [←hEnd]
  exact le_of_pow_le_pow_left₀ (by norm_num : (288:ℕ)≠0)
    (Real.rpow_nonneg hXp.le _) (hFinalPower.trans_eq hRootPower.symm)

example
    {α : ℝ≥0} {t : ℝ} (ht : t∈Icc (0:ℝ) 1)
    (hα : (α:ℝ)=(1-t)*(890/3277)+t*(17604372/60424193)) :
    Expdb.IsExponentSumBoundNonAsymptotic α (89/3478+(7441/8695)*(α:ℝ)) := by
  exact fourth_pair_capped_short_nonAsymptotic ht hα

#print axioms fourth_pair_capped_short_nonAsymptotic

/-- Closed half-interval coverage for the fourth pair, reusing the native
Heath--Brown derivative bounds and the already proved sixth row outside
the actual double-shift short-range interval. -/
private theorem fourth_pair_full_half_beta
    {α : ℝ≥0} (hhalf : (α:ℝ)≤1/2) :
    Expdb.exponentSumGrowthExponent α≤89/3478+(7441/8695)*(α:ℝ) := by
  by_cases hpos : 0<(α:ℝ)
  swap
  · have hz : α=0 := NNReal.coe_injective (le_antisymm (le_of_not_gt hpos) α.coe_nonneg)
    subst α
    rw [exponentSumGrowthExponent_zero]
    norm_num
  by_cases h7 : (α:ℝ)≤1/6
  · have hh := exponentSumGrowthExponent_le_heathBrown_of_derivative
      GafniTao.heathBrownKthDerivativeTheorem_native (by norm_num : 3≤(7:ℕ)) hpos
    apply hh.trans
    rw [heathBrownBetaBound_eq_max (by norm_num : 3≤(7:ℕ))]
    norm_num [heathBrownDerivativeExponent,heathBrownInverseExponent]
    refine ⟨?_,?_,?_⟩ <;> linarith only [h7,α.coe_nonneg]
  by_cases h6 : (α:ℝ)≤3/13
  · have hh := exponentSumGrowthExponent_le_heathBrown_of_derivative
      GafniTao.heathBrownKthDerivativeTheorem_native (by norm_num : 3≤(6:ℕ)) hpos
    apply hh.trans
    rw [heathBrownBetaBound_eq_max (by norm_num : 3≤(6:ℕ))]
    norm_num [heathBrownDerivativeExponent,heathBrownInverseExponent]
    refine ⟨?_,?_,?_⟩ <;> linarith only [lt_of_not_ge h7,h6]
  by_cases h5 : (α:ℝ)≤1/4
  · have hh := exponentSumGrowthExponent_le_heathBrown_firstRow h5
    linarith only [hh,lt_of_not_ge h6]
  by_cases hlo : (α:ℝ)≤890/3277
  · have hh := exponentSumGrowthExponent_le_heathBrown_secondRow (le_of_not_ge h5) hlo
    linarith only [hh,hlo]
  by_cases hhi : (α:ℝ)≤17604372/60424193
  · let t := ((α:ℝ)-(890:ℝ)/3277)/((17604372:ℝ)/60424193-(890:ℝ)/3277)
    have hden : 0<(17604372:ℝ)/60424193-(890:ℝ)/3277 := by norm_num
    have ht : t∈Icc (0:ℝ) 1 := by
      refine ⟨div_nonneg (by linarith only [lt_of_not_ge hlo]) hden.le,?_⟩
      exact (div_le_one hden).mpr (by linarith only [hhi])
    have hα : (α:ℝ)=(1-t)*(890/3277)+t*(17604372/60424193) := by
      dsimp only [t]
      ring
    exact Expdb.exponentSumGrowthExponent_le_iff_nonAsymptotic.mpr
      (fourth_pair_capped_short_nonAsymptotic ht hα)
  have hh := CubicJointCount.exponentSumGrowthExponent_le_trudgianYang_sixthRow
    (α:=α) (by linarith only [hhalf])
  linarith only [hh,lt_of_not_ge hhi]

example
    {α : ℝ≥0} (hhalf : (α:ℝ)≤1/2) :
    Expdb.exponentSumGrowthExponent α≤89/3478+(7441/8695)*(α:ℝ) := by
  exact fourth_pair_full_half_beta hhalf

#print axioms fourth_pair_full_half_beta

/-- The fourth new analytic exponent pair, obtained from complete beta
coverage, not from a rational triangle certificate or an assumed pair. -/
private theorem fourth_pair_analytic :
    ExponentPair (89/3478) (15327/17390) := by
  apply exponentPair_of_beta_bound_half
    (by norm_num [InExponentPairTriangle]) (by norm_num)
  intro α hhalf
  have hh := fourth_pair_full_half_beta hhalf
  unfold exponentPairLine
  linarith only [hh]

example : ExponentPair (89/3478) (15327/17390) := fourth_pair_analytic

#print axioms fourth_pair_analytic

end HuxleyDoubleShiftScratch
