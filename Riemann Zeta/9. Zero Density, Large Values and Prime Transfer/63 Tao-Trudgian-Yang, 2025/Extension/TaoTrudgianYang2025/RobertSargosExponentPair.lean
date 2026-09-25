import TaoTrudgianYang2025.RobertSargosPhysicalSieve
import TaoTrudgianYang2025.HeathBrownSourceTail
import TaoTrudgianYang2025.SargosQuarticPoisson
import TaoTrudgianYang2025.BetaHalfDuality
import TaoTrudgianYang2025.ClassicalSecondDerivativePair
import TaoTrudgianYang2025.ExponentPairAProcess
import TaoTrudgianYang2025.ExponentPairBProcess
import TaoTrudgianYang2025.ZetaGrowthBridge
import TaoTrudgianYang2025.HeathBrownDensityRange

/-!
# Robert--Sargos analytic exponent pair and the old-pair cascade

The proved long-range fourth-derivative theorem is applied to the actual
approximate model phase. Short intervals are differences of long sums;
the two possible boundary terms are charged explicitly. The power window
is derived uniformly, and the existing classical pair covers its complement.
No Watt pair, derivative estimate, or exponential-sum bound is assumed.
-/

noncomputable section
open Expdb Set GafniTao Filter
open scoped FourierTransform BigOperators ContDiff NNReal
namespace TaoTrudgianYang2025

theorem norm_sum_Ico_le_of_long_intervals (g : ℕ → ℂ) {A B a b : ℕ} {K : ℝ}
    (hK : 0 ≤ K) (hAa : A ≤ a) (hab : a ≤ b) (hbB : b ≤ B)
    (hlong : ∀ u v : ℕ, A ≤ u → u ≤ v → v ≤ B →
      (B-A:ℕ) ≤ 2*(v-u) → ‖∑ n ∈ Finset.Ico u v, g n‖ ≤ K) :
    ‖∑ n ∈ Finset.Ico a b, g n‖ ≤ 4*K := by
  have hAB : A ≤ B := hAa.trans (hab.trans hbB)
  have hfull := hlong A B le_rfl hAB le_rfl (by omega)
  have hprefix (t : ℕ) (hAt : A ≤ t) (htB : t ≤ B) :
      ‖∑ n ∈ Finset.Ico A t, g n‖ ≤ 2*K := by
    by_cases hlen : B-A ≤ 2*(t-A)
    · have h := hlong A t le_rfl hAt htB hlen
      linarith
    · have htail := hlong t B hAt htB le_rfl (by omega)
      have he := Finset.sum_Ico_consecutive g hAt htB
      have he' : ∑ n ∈ Finset.Ico A t, g n =
          (∑ n ∈ Finset.Ico A B, g n)-(∑ n ∈ Finset.Ico t B, g n) := by
        linear_combination he
      rw [he']
      exact (norm_sub_le _ _).trans (by linarith)
  have ha := hprefix a hAa (hab.trans hbB)
  have hb := hprefix b (hAa.trans hab) hbB
  have he := Finset.sum_Ico_consecutive g hAa hab
  have he' : ∑ n ∈ Finset.Ico a b, g n =
      (∑ n ∈ Finset.Ico A b, g n)-(∑ n ∈ Finset.Ico A a, g n) := by
    linear_combination he
  rw [he']
  exact (norm_sub_le _ _).trans (by linarith)

theorem heathBrownCharacterSum_eq_integer_sum (L : ℕ) (f : ℝ → ℝ) :
    heathBrownCharacterSum L f =
      ∑ n ∈ Finset.Icc (1:ℤ) L, fordAdditiveCharacter (f n) := by
  unfold heathBrownCharacterSum
  apply Finset.sum_bij (fun (n:ℕ) _ => (n:ℤ))
  · intro n hn
    simp only [Finset.mem_Icc] at hn ⊢
    exact ⟨by exact_mod_cast hn.1,by exact_mod_cast hn.2⟩
  · intro n hn m hm h
    exact_mod_cast h
  · intro n hn
    simp only [Finset.mem_Icc] at hn
    refine ⟨n.toNat,?_,Int.toNat_of_nonneg (by omega)⟩
    simp only [Finset.mem_Icc]
    omega
  · intro n hn
    rw [Int.cast_natCast]
    exact (sargos_ford_character_eq_fourier _).symm

theorem exists_robertSargos_model_tail_bound {σ η : ℝ} (hσ : 0 < σ) (hη : 0 < η) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ K : ℝ, 0 < K ∧
      ∀ (F : ℝ → ℝ) (T N : ℝ) (a L : ℕ),
      0 < T → 0 < N → N ≤ (a:ℝ) → (a:ℝ)+(L:ℝ) < 2*N →
      IsApproximateModelPhaseFunction F σ 3 δ →
      (modelPhaseJetLower σ 3*T/N^4)^(-(8:ℝ)/13) ≤ L →
      ‖heathBrownSourceTail F T N a L‖ ≤
        K*N^(1+η)*(modelPhaseJetLower σ 3*T/N^4)^((1:ℝ)/13) := by
  let c := modelPhaseJetLower σ 3
  have hc : 0 < c := modelPhaseJetLower_pos hσ 3
  let C := max 1 ((modelPhaseJetCoefficient σ 3+1)/c)
  have hC : 1 ≤ C := le_max_left _ _
  obtain ⟨K,hK,hsource⟩ := exists_robertSargos_fourth_derivative_long_range η hη C hC
  refine ⟨min c 1,lt_min hc (by norm_num),K,hK,?_⟩
  intro F T N a L hT hN ha hb hF hlen
  let f := heathBrownPhysicalPhase F T N a (modelPhaseJetSign σ 3)
  let lam := c*T/N^4
  have hlam : 0 < lam := by dsimp only [lam]; positivity
  have hLp : (0:ℝ) < L := (Real.rpow_pos_of_pos hlam _).trans_le hlen
  have hLN : (L:ℝ) ≤ N := by linarith
  have hupper : (a:ℝ)+(2*N-(a:ℝ)) ≤ 2*N := by linarith
  have hfd := heathBrownPhysicalPhase_contDiffOn hF.1 hN ha hupper T (modelPhaseJetSign σ 3)
  have hint (x : ℝ) (hx : x ∈ Icc (1:ℝ) L) :
      x ∈ Ioo (0:ℝ) (2*N-(a:ℝ)) := by constructor <;> linarith [hx.1,hx.2]
  have hf : ∀ x ∈ Icc (1:ℝ) L, ContDiffAt ℝ 4 f x := by
    intro x hx
    exact ((hfd.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 4))
      x ⟨(hint x hx).1.le,(hint x hx).2.le⟩).contDiffAt
      (mem_of_superset (isOpen_Ioo.mem_nhds (hint x hx)) Ioo_subset_Icc_self)
  have hj (x : ℝ) (hx : x ∈ Icc (1:ℝ) L) :
      lam ≤ iteratedDeriv 4 f x ∧ iteratedDeriv 4 f x ≤ C*lam := by
    have h := heathBrownPhysicalPhase_signed_derivative_bounds hσ hT hN ha hupper
      hF (hint x hx) 3 le_rfl le_rfl
    refine ⟨h.1, h.2.trans ?_⟩
    have he : (modelPhaseJetCoefficient σ 3+1)*T/N^4 =
        ((modelPhaseJetCoefficient σ 3+1)/c)*lam := by
      dsimp only [lam]
      field_simp
    rw [he]
    exact mul_le_mul_of_nonneg_right (le_max_right _ _) hlam.le
  rw [norm_heathBrownSourceTail_eq_signed_characterSum F T N σ a L 3,
    heathBrownCharacterSum_eq_integer_sum]
  apply (hsource f L lam hlam hlen hf (fun x hx => (hj x hx).1)
    (fun x hx => (hj x hx).2)).trans
  gcongr
theorem heathBrownSourceTail_eq_Ico (F : ℝ → ℝ) (T N : ℝ) {u v : ℕ}
    (hu : 1 ≤ u) (huv : u ≤ v) :
    heathBrownSourceTail F T N (u-1) (v-u) =
      ∑ n ∈ Finset.Ico u v, oscillatory F T N n := by
  unfold heathBrownSourceTail
  apply Finset.sum_bij (fun n _ => u-1+n)
  · intro n hn
    simp only [Finset.mem_Icc] at hn
    simp only [Finset.mem_Ico]
    omega
  · intro n hn m hm he
    omega
  · intro n hn
    simp only [Finset.mem_Ico] at hn
    refine ⟨n-(u-1),?_,by omega⟩
    simp only [Finset.mem_Icc]
    omega
  · intro n hn
    simp only [Nat.cast_add]

theorem exists_robertSargos_model_sum_bound {σ η : ℝ} (hσ : 0 < σ) (hη : 0 < η) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ K : ℝ, 0 < K ∧
      ∀ (F : ℝ → ℝ) (T N : ℝ) (a b : ℕ),
      0 < T → 8 ≤ N → N ≤ (a:ℝ) → (b:ℝ) ≤ 2*N →
      IsApproximateModelPhaseFunction F σ 3 δ →
      (modelPhaseJetLower σ 3*T/N^4)^(-(8:ℝ)/13) ≤ N/8 →
      ‖exponentialSumAt F T N a b‖ ≤
        2+4*K*N^(1+η)*(modelPhaseJetLower σ 3*T/N^4)^((1:ℝ)/13) := by
  obtain ⟨δ,hδ,K,hK,hsource⟩ := exists_robertSargos_model_tail_bound hσ hη
  refine ⟨δ,hδ,K,hK,?_⟩
  intro F T N a b hT hN ha hb hF hlen
  have hNp : 0 < N := by linarith
  let A := ⌈N⌉₊+1
  let B := ⌊2*N⌋₊
  have hceil : N ≤ (⌈N⌉₊:ℝ) := Nat.le_ceil N
  have hceilUpper : (⌈N⌉₊:ℝ) < N+1 := Nat.ceil_lt_add_one hNp.le
  have hfloor : (B:ℝ) ≤ 2*N := Nat.floor_le (by positivity)
  have hfloorLower : 2*N < (B:ℝ)+1 := Nat.lt_floor_add_one (2*N)
  have hAre : (A:ℝ) = (⌈N⌉₊:ℝ)+1 := by simp only [A,Nat.cast_add,Nat.cast_one]
  have hAB : A ≤ B := by
    have : (A:ℝ) ≤ B := by linarith
    exact_mod_cast this
  have hlenAB : N/4 ≤ ((B-A:ℕ):ℝ)/2 := by
    rw [Nat.cast_sub hAB]
    linarith
  let U := K*N^(1+η)*(modelPhaseJetLower σ 3*T/N^4)^((1:ℝ)/13)
  have hc := modelPhaseJetLower_pos hσ 3
  have hU : 0 ≤ U := by dsimp only [U]; positivity
  have hlong (u v : ℕ) (hu : A ≤ u) (huv : u ≤ v) (hv : v ≤ B)
      (hl : B-A ≤ 2*(v-u)) :
      ‖∑ n ∈ Finset.Ico u v, oscillatory F T N n‖ ≤ U := by
    have hu1 : 1 ≤ u := by dsimp only [A] at hu; omega
    have hua : N ≤ ((u-1:ℕ):ℝ) := by
      have hcast : (A:ℝ) ≤ u := by exact_mod_cast hu
      rw [Nat.cast_sub hu1]
      push_cast
      linarith
    have huvReal : ((u-1:ℕ):ℝ)+((v-u:ℕ):ℝ) < 2*N := by
      have hvReal : (v:ℝ) ≤ B := by exact_mod_cast hv
      rw [Nat.cast_sub hu1,Nat.cast_sub huv]
      push_cast
      linarith
    have hlReal : ((B-A:ℕ):ℝ) ≤ 2*((v-u:ℕ):ℝ) := by exact_mod_cast hl
    have hlen' : (modelPhaseJetLower σ 3*T/N^4)^(-(8:ℝ)/13) ≤ (v-u:ℕ) := by
      linarith
    rw [← heathBrownSourceTail_eq_Ico F T N hu1 huv]
    exact hsource F T N (u-1) (v-u) hT hNp hua huvReal hF hlen'
  let S := Finset.Icc a b
  let I := Finset.Ico A B
  have hinter : S ∩ I = Finset.Ico (max a A) (min (b+1) B) := by
    ext n
    simp only [S,I,Finset.mem_inter,Finset.mem_Icc,Finset.mem_Ico,
      max_le_iff,lt_min_iff]
    omega
  have hcore : ‖∑ n ∈ S ∩ I, oscillatory F T N n‖ ≤ 4*U := by
    rw [hinter]
    by_cases hc : max a A ≤ min (b+1) B
    · exact norm_sum_Ico_le_of_long_intervals _ hU (le_max_right _ _) hc
        (min_le_right _ _) hlong
    · rw [Finset.Ico_eq_empty_of_le (by omega)]
      simp only [Finset.sum_empty,norm_zero]
      positivity
  have hsmall : S \ I ⊆ {⌈N⌉₊,B} := by
    intro n hn
    have hn' := Finset.mem_sdiff.mp hn
    have hns := Finset.mem_Icc.mp hn'.1
    have hni : ¬ (A ≤ n ∧ n < B) := by simpa only [I,Finset.mem_Ico] using hn'.2
    have hna : ⌈N⌉₊ ≤ n := (Nat.ceil_le.mpr ha).trans hns.1
    have hnb : n ≤ B := hns.2.trans (Nat.le_floor hb)
    simp only [Finset.mem_insert,Finset.mem_singleton,A] at *
    omega
  have hcard : (S \ I).card ≤ 2 :=
    (Finset.card_le_card hsmall).trans Finset.card_le_two
  have hboundary : ‖∑ n ∈ S \ I, oscillatory F T N n‖ ≤ 2 := by
    apply (norm_sum_le _ _).trans
    simp only [norm_oscillatory,Finset.sum_const,nsmul_eq_mul,mul_one]
    exact_mod_cast hcard
  have he := Finset.sum_inter_add_sum_diff S I (fun n => oscillatory F T N n)
  change ‖∑ n ∈ S, oscillatory F T N n‖ ≤ _
  rw [← he]
  have hn := (norm_add_le _ _).trans (add_le_add hcore hboundary)
  dsimp only [U] at hn
  nlinarith only [hn]

theorem robertSargos_model_main_power {c T N η : ℝ}
    (hc : 0 < c) (hT : 0 < T) (hN : 0 < N) :
    N^(1+η)*(c*T/N^4)^((1:ℝ)/13) =
      c^((1:ℝ)/13)*T^((1:ℝ)/13)*N^(9/13+η) := by
  rw [Real.div_rpow (mul_nonneg hc.le hT.le) (pow_nonneg hN.le _),
    Real.mul_rpow hc.le hT.le,← Real.rpow_natCast N 4,
    ← Real.rpow_mul hN.le]
  norm_num only [Nat.cast_ofNat]
  rw [div_eq_mul_inv,← Real.rpow_neg hN.le]
  calc
    _ = c^((1:ℝ)/13)*T^((1:ℝ)/13)*(N^(1+η)*N^(-((4:ℝ)*(1/13)))) := by ring_nf
    _ = _ := by rw [← Real.rpow_add hN]; congr 2; ring

theorem robertSargos_model_length_power {c T N : ℝ}
    (hc : 0 < c) (hT : 0 < T) (hN : 0 < N) :
    (c*T/N^4)^(-(8:ℝ)/13)/N =
      c^(-(8:ℝ)/13)*T^(-(8:ℝ)/13)*N^((19:ℝ)/13) := by
  rw [Real.div_rpow (mul_nonneg hc.le hT.le) (pow_nonneg hN.le _),
    Real.mul_rpow hc.le hT.le,← Real.rpow_natCast N 4,
    ← Real.rpow_mul hN.le]
  norm_num only [Nat.cast_ofNat]
  rw [div_eq_mul_inv,div_eq_mul_inv,← Real.rpow_neg hN.le,
    ← Real.rpow_neg_one]
  calc
    _ = c^(-(8:ℝ)/13)*T^(-(8:ℝ)/13)*(N^(-(4*(-(8:ℝ)/13)))*N^(-(1:ℝ))) := by ring_nf
    _ = _ := by rw [← Real.rpow_add hN]; norm_num

theorem eventually_robertSargos_model_length {c a : ℝ}
    (hc : 0 < c) (ha : a < 8/19) :
    ∀ᶠ T : ℝ in atTop, ∀ N : ℝ, 0 < N → N ≤ T^a →
      (c*T/N^4)^(-(8:ℝ)/13) ≤ N/8 := by
  have he := eventually_const_mul_rpow_le_rpow
    (D := 8*c^(-(8:ℝ)/13)) (a := a*(19/13)) (b := 8/13) (by nlinarith)
  filter_upwards [he,eventually_gt_atTop (0:ℝ)] with T hbudget hT
  intro N hN hupper
  have hn := Real.rpow_le_rpow hN.le hupper (by norm_num : (0:ℝ) ≤ 19/13)
  rw [← Real.rpow_mul hT.le] at hn
  have hpow : T^(-(8:ℝ)/13)*T^((8:ℝ)/13) = 1 := by
    rw [← Real.rpow_add hT]
    norm_num
  have hscale := mul_le_mul_of_nonneg_left hbudget
    (Real.rpow_nonneg hT.le (-(8:ℝ)/13))
  have hmono := mul_le_mul_of_nonneg_left hn
    (show 0 ≤ 8*c^(-(8:ℝ)/13)*T^(-(8:ℝ)/13) by positivity)
  have hratio : (c*T/N^4)^(-(8:ℝ)/13)/N ≤ 1/8 := by
    rw [robertSargos_model_length_power hc hT hN]
    nlinarith only [hscale,hmono,hpow]
  have h := (div_le_iff₀ hN).mp hratio
  linarith

theorem isExponentSumBoundNonAsymptotic_robertSargos
    {α : ℝ≥0} (hα : 0 < (α:ℝ)) (hαupper : (α:ℝ) < 8/19) :
    IsExponentSumBoundNonAsymptotic α ((1:ℝ)/13+(9/13)*(α:ℝ)) := by
  intro ε hε σ hσ
  let η := min 1 (ε/4)
  have hη : 0 < η := lt_min (by norm_num) (by positivity)
  have hη1 : η ≤ 1 := min_le_left _ _
  have hηε : η ≤ ε/4 := min_le_right _ _
  obtain ⟨δ₀,hδ₀,K,hK,hsource⟩ := exists_robertSargos_model_sum_bound hσ hη
  let δ := min δ₀ (min ((α:ℝ)/2) (min ((8/19-(α:ℝ))/2) (ε/8)))
  have hδ : 0 < δ := lt_min hδ₀ (lt_min (by positivity)
    (lt_min (by positivity) (by positivity)))
  have hδ₀le : δ ≤ δ₀ := min_le_left _ _
  have hδα : δ ≤ (α:ℝ)/2 := (min_le_right _ _).trans (min_le_left _ _)
  have hδgap : δ ≤ (8/19-(α:ℝ))/2 :=
    ((min_le_right _ _).trans (min_le_right _ _)).trans (min_le_left _ _)
  have hδε : δ ≤ ε/8 :=
    ((min_le_right _ _).trans (min_le_right _ _)).trans (min_le_right _ _)
  let c := modelPhaseJetLower σ 3
  have hc : 0 < c := modelPhaseJetLower_pos hσ 3
  obtain ⟨M,hM⟩ := eventually_atTop.mp
    ((eventually_robertSargos_model_length hc (show (α:ℝ)+δ < 8/19 by linarith)).and
      ((tendsto_rpow_atTop (show 0 < (α:ℝ)/2 by positivity)).eventually
        (eventually_ge_atTop (8:ℝ))))
  let C := max 1 (max M (2+4*K*c^((1:ℝ)/13)))
  have hC : 1 ≤ C := le_max_left _ _
  have hMC : M ≤ C := (le_max_left _ _).trans (le_max_right _ _)
  have hKC : 2+4*K*c^((1:ℝ)/13) ≤ C :=
    (le_max_right _ _).trans (le_max_right _ _)
  refine ⟨δ,hδ,3,by norm_num,C,hC,?_⟩
  intro T N F a b hs
  have hT : 1 ≤ T := hC.trans hs.threshold_le_param
  have hTp : 0 < T := zero_lt_one.trans_le hT
  obtain ⟨hphysical,hlarge⟩ := hM T (hMC.trans hs.threshold_le_param)
  have hN8 : 8 ≤ N := hlarge.trans
    ((Real.rpow_le_rpow_of_exponent_le hT (show (α:ℝ)/2 ≤ (α:ℝ)-δ by linarith)).trans
      hs.rpow_sub_le_scale)
  have hNp : 0 < N := by linarith
  have hbound := hsource F T N a b hTp hN8 hs.scale_le_start hs.end_le_two_mul_scale
    (approximateModelPhase_mono hs.isApproximateModelPhase le_rfl hδ₀le)
    (hphysical N hNp hs.scale_le_rpow_add)
  have hpower : N^(1+η)*(c*T/N^4)^((1:ℝ)/13) ≤
      c^((1:ℝ)/13)*T^((1:ℝ)/13+(9/13)*(α:ℝ)+ε) := by
    rw [robertSargos_model_main_power hc hTp hNp]
    have hNpow := Real.rpow_le_rpow hNp.le hs.scale_le_rpow_add
      (show 0 ≤ 9/13+η by linarith)
    rw [← Real.rpow_mul hTp.le] at hNpow
    have hηα := mul_le_mul_of_nonneg_right (show (α:ℝ) ≤ 1 by linarith) hη.le
    have hδmul := mul_le_mul_of_nonneg_left (show 9/13+η ≤ 2 by linarith) hδ.le
    have hexp : (1:ℝ)/13+((α:ℝ)+δ)*(9/13+η) ≤
        (1:ℝ)/13+(9/13)*(α:ℝ)+ε := by nlinarith
    calc
      _ ≤ c^((1:ℝ)/13)*T^((1:ℝ)/13)*T^(((α:ℝ)+δ)*(9/13+η)) :=
        mul_le_mul_of_nonneg_left hNpow (by positivity)
      _ = c^((1:ℝ)/13)*T^((1:ℝ)/13+((α:ℝ)+δ)*(9/13+η)) := by
        rw [mul_assoc,← Real.rpow_add hTp]
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hT hexp) (by positivity)
  have hone : 1 ≤ T^((1:ℝ)/13+(9/13)*(α:ℝ)+ε) :=
    Real.one_le_rpow hT (by positivity)
  have hscaled := mul_le_mul_of_nonneg_left hpower (show 0 ≤ 4*K by positivity)
  have hconstant := mul_le_mul_of_nonneg_right hKC
    (Real.rpow_nonneg hTp.le ((1:ℝ)/13+(9/13)*(α:ℝ)+ε))
  dsimp only [c] at hscaled hconstant
  nlinarith only [hbound,hscaled,hconstant,hone]

theorem exponentPair_robertSargos : ExponentPair (1/13) (10/13) := by
  apply exponentPair_of_beta_bound_half (by norm_num [InExponentPairTriangle])
    (by norm_num)
  intro α hαhalf
  by_cases hα : 0 < (α:ℝ)
  · by_cases hshort : (α:ℝ) < 8/19
    · have h := exponentSumGrowthExponent_le_iff_nonAsymptotic.mpr
        (isExponentSumBoundNonAsymptotic_robertSargos hα hshort)
      convert h using 1
      simp only [exponentPairLine]
      ring
    · have hclassical := exponentPair_half_half.aProcess.aProcess.bProcess.aProcess
      norm_num at hclassical
      have h := exponentSumGrowthExponent_le_exponentPairLine_closed hclassical α (by linarith)
      apply h.trans
      unfold exponentPairLine
      linarith
  · have hz : α = 0 := NNReal.coe_injective (le_antisymm (le_of_not_gt hα) α.coe_nonneg)
    subst α
    rw [exponentSumGrowthExponent_zero]
    norm_num [exponentPairLine]

theorem exponentPair_three_fortieths : ExponentPair (3/40) (31/40) := by
  have hclassical := exponentPair_half_half.aProcess.aProcess
  have hmix := exponentPair_robertSargos.convexCombination hclassical
    (by norm_num : (0:ℝ) ≤ 7/20) (by norm_num : (7/20:ℝ) ≤ 1)
  norm_num at hmix
  exact hmix

theorem old_pair_zetaGrowthBound : IsZetaGrowthBound (7/10) (3/40) := by
  have h := exponentPair_three_fortieths.isZetaGrowthBound
  norm_num at h
  exact h

theorem old_pair_zetaGrowthExponent :
    zetaGrowthExponent (7/10) ≤ ((3/40:ℝ):EReal) :=
  zetaGrowthExponent_le_of_bound old_pair_zetaGrowthBound

theorem improved_heathBrown_zeroDensity {σ : ℝ}
    (hσ : 7/10 < σ) (hσ1 : σ ≤ 1) :
    zeroDensityExponent σ ≤ ((3/(10*σ-7):ℝ):EReal) :=
  exponentPair_three_fortieths.heathBrown_density_of_old_pair hσ hσ1

end TaoTrudgianYang2025
