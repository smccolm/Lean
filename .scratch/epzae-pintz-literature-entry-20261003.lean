import TaoTrudgianYang2025.BourgainOptimizedTransfer
import TaoTrudgianYang2025.ExponentPairLargeValues
import TaoTrudgianYang2025.ZeroDensityTransferCorollaries
import TaoTrudgianYang2025.ZetaPairNonexistence
import TaoTrudgianYang2025.HeathBrownDerivative

noncomputable section
namespace PintzLiteratureScratch
open TaoTrudgianYang2025

theorem first_montgomery {σ τ : ℝ}
    (hσ : 23/24 ≤ σ) (hτ : 0 ≤ τ) (hτhi : τ ≤ 25*σ-21) :
    IsLargeValueBound σ τ (2-2*σ) := by
  apply exponentPair_taoTrudgianYang_firstNew.local_largeValueBound hτ
  linarith only [hσ,hτhi]

theorem first_zeta {σ τ : ℝ}
    (hσ : 23/24 ≤ σ) (hτ : 2 ≤ τ) (hτhi : τ < 4*(24*σ-20)/3) :
    zetaLargeValueExponent σ τ = ⊥ := by
  apply exponentPair_taoTrudgianYang_fourthNew.zetaLargeValueExponent_eq_bot_of_one_le_tau
    (by linarith only [hσ]) (by linarith only [hτ])
  linarith only [hσ,hτhi]

theorem first_density {σ : ℝ} (hσ : 23/24 ≤ σ) (hσ1 : σ < 1) :
    zeroDensityExponent σ ≤ ((3/(24*σ-20):ℝ):EReal) := by
  apply zeroDensityExponent_le_three_div_of_montgomery_range σ (24*σ-20)
    (by linarith only [hσ]) hσ1 (by linarith only [hσ])
  · intro τ hτ
    rw [first_zeta hσ hτ.1 hτ.2]
    exact bot_le
  · intro τ hτ
    exact largeValueExponent_le_of_bound (first_montgomery hσ hτ.1 (by linarith only [hτ.2]))

example {σ τ : ℝ} (hσ : 23/24 ≤ σ) (hτ : 0 ≤ τ) (hτhi : τ ≤ 25*σ-21) :
    IsLargeValueBound σ τ (2-2*σ) :=
  first_montgomery hσ hτ hτhi

example {σ τ : ℝ} (hσ : 23/24 ≤ σ) (hτ : 2 ≤ τ)
    (hτhi : τ < 4*(24*σ-20)/3) :
    zetaLargeValueExponent σ τ = ⊥ :=
  first_zeta hσ hτ hτhi

example {σ : ℝ} (hσ : 23/24 ≤ σ) (hσ1 : σ < 1) :
    zeroDensityExponent σ ≤ ((3/(24*σ-20):ℝ):EReal) :=
  first_density hσ hσ1

example : zeroDensityExponent (23/24) ≤ ((3/(24*(23/24)-20):ℝ):EReal) :=
  first_density (by norm_num) (by norm_num)

example : zeroDensityExponent (2211487/2274732) ≤
    ((3/(24*(2211487/2274732)-20):ℝ):EReal) :=
  first_density (by norm_num) (by norm_num)

#print axioms first_montgomery
#print axioms first_zeta
#print axioms first_density

theorem heathBrown_logarithmic_sum_bound {k : ℕ} (hk : 3 ≤ k)
    {η : ℝ} (hη : 0 < η) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (t N : ℝ) (a b : ℕ),
      0 < t → 1 ≤ N → N ≤ (a : ℝ) → (b : ℝ) ≤ 2*N →
      ‖∑ n ∈ Finset.Icc a b, (n : ℂ)^(-((t : ℂ)*Complex.I))‖ ≤
        C*heathBrownPowerMajorant k η t N := by
  obtain ⟨δ,hδ,P,_hP,C,hC,hsource⟩ :=
    source_exponentialSum_heathBrown_bound hk (by norm_num : (0:ℝ) < 1) hη
  let p : ℝ := 2*Real.pi
  let d := heathBrownDerivativeExponent k
  let e := heathBrownInverseExponent k
  have hp : 1 ≤ p := by dsimp [p]; linarith only [Real.pi_gt_three]
  have hpp : 0 < p := zero_lt_one.trans_le hp
  have hd : 0 < d := (heathBrownDerivativeExponent_bounds hk).1
  have he : 0 < e := heathBrownInverseExponent_pos hk
  have hpone : 1 ≤ p^e := Real.one_le_rpow hp he.le
  refine ⟨C*p^e,one_le_mul_of_one_le_of_one_le hC hpone,?_⟩
  intro t N a b ht hN ha hb
  have hNp := zero_lt_one.trans_le hN
  by_cases hab : a ≤ b
  · have hsum := hsource Real.log (t/p) N a (b-a) (by positivity) hN ha
      (by simpa only [Nat.add_sub_of_le hab] using hb)
      (log_approximateModel P hδ.le)
    rw [Nat.add_sub_of_le hab] at hsum
    rw [norm_sum_cpow_neg_im_eq_logModel hNp a b ha t]
    change ‖Expdb.exponentialSumAt Real.log (t/p) N a b‖ ≤ _
    have hfirst : (t/p)^d ≤ p^e*t^d := by
      apply (Real.rpow_le_rpow (by positivity) (div_le_self ht.le hp) hd.le).trans
      exact le_mul_of_one_le_left (Real.rpow_nonneg ht.le _) hpone
    have hthird : (t/p)^(-e) = p^e*t^(-e) := by
      rw [Real.div_rpow ht.le hpp.le,Real.rpow_neg hpp.le,div_inv_eq_mul,mul_comm]
    have hmaj : heathBrownPowerMajorant k η (t/p) N ≤
        p^e*heathBrownPowerMajorant k η t N := by
      unfold heathBrownPowerMajorant
      change N^η*((t/p)^d*N^(1-(k:ℝ)*d)+N^(1-d)+N*(t/p)^(-e)) ≤
        p^e*(N^η*(t^d*N^(1-(k:ℝ)*d)+N^(1-d)+N*t^(-e)))
      rw [hthird]
      have h₁ := mul_le_mul_of_nonneg_right hfirst
        (Real.rpow_nonneg hNp.le (1-(k:ℝ)*d))
      have h₂ : N^(1-d) ≤ p^e*N^(1-d) :=
        le_mul_of_one_le_left (Real.rpow_nonneg hNp.le _) hpone
      have hinner : (t/p)^d*N^(1-(k:ℝ)*d)+N^(1-d)+N*(p^e*t^(-e)) ≤
          p^e*(t^d*N^(1-(k:ℝ)*d)+N^(1-d)+N*t^(-e)) := by
        nlinarith only [h₁,h₂]
      have hmul := mul_le_mul_of_nonneg_left hinner (Real.rpow_nonneg hNp.le η)
      nlinarith only [hmul]
    have hh := hsum.trans (mul_le_mul_of_nonneg_left hmaj (zero_le_one.trans hC))
    convert hh using 1
    ring
  · rw [Finset.Icc_eq_empty_of_lt (by omega : b < a),Finset.sum_empty,norm_zero]
    unfold heathBrownPowerMajorant
    positivity

example {k : ℕ} (hk : 3 ≤ k) {η : ℝ} (hη : 0 < η) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (t N : ℝ) (a b : ℕ),
      0 < t → 1 ≤ N → N ≤ (a : ℝ) → (b : ℝ) ≤ 2*N →
      ‖∑ n ∈ Finset.Icc a b, (n : ℂ)^(-((t : ℂ)*Complex.I))‖ ≤
        C*heathBrownPowerMajorant k η t N :=
  heathBrown_logarithmic_sum_bound hk hη

#print axioms heathBrown_logarithmic_sum_bound


theorem heathBrown_window_majorant {k : ℕ} (hk : 3 ≤ k)
    {N t η τ δ B : ℝ} (hN : 1 ≤ N)
    (htlo : N^(τ-δ) ≤ t) (hthi : t ≤ N^(τ+δ))
    (hfirst : 1+(τ+δ-(k:ℝ))*heathBrownDerivativeExponent k ≤ B)
    (hsecond : 1-heathBrownDerivativeExponent k ≤ B)
    (hthird : 1-(τ-δ)*heathBrownInverseExponent k ≤ B) :
    heathBrownPowerMajorant k η t N ≤ 3*N^(η+B) := by
  have hNp := zero_lt_one.trans_le hN
  have htp := (Real.rpow_pos_of_pos hNp (τ-δ)).trans_le htlo
  let d := heathBrownDerivativeExponent k
  let e := heathBrownInverseExponent k
  have hd : 0 < d := (heathBrownDerivativeExponent_bounds hk).1
  have he : 0 < e := heathBrownInverseExponent_pos hk
  have h₁ : t^d*N^(1-(k:ℝ)*d) ≤ N^B := by
    calc
      _ ≤ (N^(τ+δ))^d*N^(1-(k:ℝ)*d) :=
        mul_le_mul_of_nonneg_right (Real.rpow_le_rpow htp.le hthi hd.le)
          (Real.rpow_nonneg hNp.le _)
      _ = N^(1+(τ+δ-(k:ℝ))*d) := by
        rw [← Real.rpow_mul hNp.le,← Real.rpow_add hNp]
        congr 1
        ring
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hN hfirst
  have h₂ : N^(1-d) ≤ N^B :=
    Real.rpow_le_rpow_of_exponent_le hN hsecond
  have h₃ : N*t^(-e) ≤ N^B := by
    calc
      _ ≤ N*(N^(τ-δ))^(-e) :=
        mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_nonpos (Real.rpow_pos_of_pos hNp _) htlo (by linarith)) hNp.le
      _ = N^(1-(τ-δ)*e) := by
        rw [← Real.rpow_mul hNp.le,
          show 1-(τ-δ)*e = 1+(τ-δ)*(-e) by ring,
          Real.rpow_add hNp,Real.rpow_one]
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hN hthird
  have hsum : t^d*N^(1-(k:ℝ)*d)+N^(1-d)+N*t^(-e) ≤ 3*N^B := by
    linarith only [h₁,h₂,h₃]
  have hh := mul_le_mul_of_nonneg_left hsum (Real.rpow_nonneg hNp.le η)
  unfold heathBrownPowerMajorant
  rw [Real.rpow_add hNp]
  dsimp only [d,e] at hh
  nlinarith only [hh]

example {k : ℕ} (hk : 3 ≤ k)
    {N t η τ δ B : ℝ} (hN : 1 ≤ N)
    (htlo : N^(τ-δ) ≤ t) (hthi : t ≤ N^(τ+δ))
    (hfirst : 1+(τ+δ-(k:ℝ))*heathBrownDerivativeExponent k ≤ B)
    (hsecond : 1-heathBrownDerivativeExponent k ≤ B)
    (hthird : 1-(τ-δ)*heathBrownInverseExponent k ≤ B) :
    heathBrownPowerMajorant k η t N ≤ 3*N^(η+B) :=
  heathBrown_window_majorant hk hN htlo hthi hfirst hsecond hthird

#print axioms heathBrown_window_majorant


theorem heathBrown_zeta_nonexistence {k : ℕ} (hk : 3 ≤ k)
    {σ τ : ℝ}
    (hfirst : 1+(τ-(k:ℝ))*heathBrownDerivativeExponent k < σ)
    (hsecond : 1-heathBrownDerivativeExponent k < σ)
    (hthird : 1-τ*heathBrownInverseExponent k < σ) :
    zetaLargeValueExponent σ τ = ⊥ := by
  let d := heathBrownDerivativeExponent k
  let e := heathBrownInverseExponent k
  let g := min (σ-(1+(τ-(k:ℝ))*d))
    (min (σ-(1-d)) (σ-(1-τ*e)))
  have hd : 0 < d := (heathBrownDerivativeExponent_bounds hk).1
  have he : 0 < e := heathBrownInverseExponent_pos hk
  have hg : 0 < g := lt_min (sub_pos.mpr hfirst)
    (lt_min (sub_pos.mpr hsecond) (sub_pos.mpr hthird))
  have hg₁ : g ≤ σ-(1+(τ-(k:ℝ))*d) := min_le_left _ _
  have hg₂ : g ≤ σ-(1-d) := (min_le_right _ _).trans (min_le_left _ _)
  have hg₃ : g ≤ σ-(1-τ*e) := (min_le_right _ _).trans (min_le_right _ _)
  let η := g/8
  let δ := min (g/8) (g/(8*(d+e+1)))
  have hη : 0 < η := by dsimp [η]; positivity
  have hδ : 0 < δ := lt_min (by positivity) (by positivity)
  have hδg : δ ≤ g/8 := min_le_left _ _
  have hδde : δ*(d+e+1) ≤ g/8 := by
    have hh := (le_div_iff₀ (by positivity : 0 < 8*(d+e+1))).mp
      (show δ ≤ g/(8*(d+e+1)) from min_le_right _ _)
    nlinarith only [hh]
  have hδd : δ*d ≤ g/8 := by
    nlinarith only [hδde,mul_nonneg hδ.le he.le,hδ.le]
  have hδe : δ*e ≤ g/8 := by
    nlinarith only [hδde,mul_nonneg hδ.le hd.le,hδ.le]
  obtain ⟨C,hC,hbound⟩ := heathBrown_logarithmic_sum_bound hk hη
  have hev : ∀ᶠ N : ℝ in Filter.atTop, 3*C ≤ N^η :=
    (tendsto_rpow_atTop hη).eventually (Filter.eventually_ge_atTop _)
  obtain ⟨N₀,hN₀⟩ := Filter.eventually_atTop.mp hev
  apply zetaLargeValueExponent_eq_bot_of_pointwise_powerSaving
  refine ⟨max 2 N₀,δ,by have := le_max_left (2:ℝ) N₀; linarith,hδ,?_⟩
  intro N I t hNC hI hsub htlo hthi
  have hN2 : (2:ℝ) ≤ N := (le_max_left _ _).trans hNC
  have hN1 : (1:ℝ) < N := by linarith only [hN2]
  have hNp : (0:ℝ) < N := zero_lt_one.trans hN1
  have htp := (Real.rpow_pos_of_pos hNp (τ-δ)).trans_le htlo
  have hconstant := hN₀ (N:ℝ) ((le_max_right _ _).trans hNC)
  by_cases hempty : I = ∅
  · subst I
    simpa only [Finset.sum_empty,norm_zero] using
      Real.rpow_pos_of_pos hNp (σ-δ)
  obtain ⟨a,b,rfl⟩ := hI
  have hab : a ≤ b := Finset.nonempty_Icc.mp (Finset.nonempty_iff_ne_empty.mpr hempty)
  have ha : N ≤ a := (Finset.mem_Icc.mp (hsub (Finset.mem_Icc.mpr ⟨le_rfl,hab⟩))).1
  have hb : b ≤ 2*N := (Finset.mem_Icc.mp (hsub (Finset.mem_Icc.mpr ⟨hab,le_rfl⟩))).2
  have hsum := hbound t N a b htp hN1.le
    (by exact_mod_cast ha) (by exact_mod_cast hb)
  have hmajor := heathBrown_window_majorant (η:=η) (B:=σ-g/2) hk hN1.le htlo hthi
    (by change 1+(τ+δ-(k:ℝ))*d ≤ σ-g/2; nlinarith only [hg₁,hδd,hg.le])
    (by change 1-d ≤ σ-g/2; linarith only [hg₂,hg.le])
    (by change 1-(τ-δ)*e ≤ σ-g/2; nlinarith only [hg₃,hδe,hg.le])
  have hphase : (∑ n ∈ Finset.Icc a b, dirichletPhase n t) =
      ∑ n ∈ Finset.Icc a b, (n:ℂ)^(-((t:ℂ)*Complex.I)) := by
    apply Finset.sum_congr rfl
    intro n _
    simp only [dirichletPhase,mul_comm Complex.I (t:ℂ)]
    rfl
  rw [hphase]
  calc
    _ ≤ C*(3*(N:ℝ)^(η+(σ-g/2))) :=
      hsum.trans (mul_le_mul_of_nonneg_left hmajor (zero_le_one.trans hC))
    _ = (3*C)*(N:ℝ)^(η+(σ-g/2)) := by ring
    _ ≤ (N:ℝ)^η*(N:ℝ)^(η+(σ-g/2)) :=
      mul_le_mul_of_nonneg_right hconstant (Real.rpow_nonneg hNp.le _)
    _ = (N:ℝ)^(η+(η+(σ-g/2))) := (Real.rpow_add hNp _ _).symm
    _ < (N:ℝ)^(σ-δ) :=
      Real.rpow_lt_rpow_of_exponent_lt hN1 (by dsimp [η]; linarith only [hδg,hg])

example {k : ℕ} (hk : 3 ≤ k) {σ τ : ℝ}
    (hfirst : 1+(τ-(k:ℝ))*heathBrownDerivativeExponent k < σ)
    (hsecond : 1-heathBrownDerivativeExponent k < σ)
    (hthird : 1-τ*heathBrownInverseExponent k < σ) :
    zetaLargeValueExponent σ τ = ⊥ :=
  heathBrown_zeta_nonexistence hk hfirst hsecond hthird

#print axioms heathBrown_zeta_nonexistence


theorem second_zeta {σ τ : ℝ}
    (hσ : 39/40 ≤ σ) (hτ : 2 ≤ τ) (hτhi : τ < 30*σ-24) :
    zetaLargeValueExponent σ τ = ⊥ := by
  by_cases ht : τ ≤ 5/2
  · exact zetaLargeValueExponent_eq_bot_of_classical_pair
      (by linarith only [hσ]) (by linarith only [hτ])
      (by linarith only [ht,hσ])
  · apply heathBrown_zeta_nonexistence (k:=6) (by norm_num)
    · norm_num [heathBrownDerivativeExponent]
      linarith only [hτhi]
    · norm_num [heathBrownDerivativeExponent]
      linarith only [hσ]
    · norm_num [heathBrownInverseExponent]
      linarith only [ht,hσ]

example {σ τ : ℝ} (hσ : 39/40 ≤ σ) (hτ : 2 ≤ τ) (hτhi : τ < 30*σ-24) :
    zetaLargeValueExponent σ τ = ⊥ := second_zeta hσ hτ hτhi

#print axioms second_zeta


theorem fifth_correlation_bound {η : ℝ} (hη : 0 < η) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (v t N : ℝ) (a b : ℕ),
      0 < t → 1 ≤ N → N ≤ (a : ℝ) → (b : ℝ) ≤ 2*N → t ≤ N^v →
      ‖∑ n ∈ Finset.Icc a b, (n:ℂ)^(-((t:ℂ)*Complex.I))‖ ≤
        C*(N^(max (19/20) (3/4+v/20)+3*η)+2*Real.pi*N/t) := by
  obtain ⟨C₁,hC₁,hpair⟩ := exponentPair_half_half.aProcess.logarithmic_sum_bound hη
  obtain ⟨C₂,hC₂,hHB⟩ := heathBrown_logarithmic_sum_bound (k:=5) (by norm_num) hη
  let C := max C₁ (3*C₂)
  have hC : 1 ≤ C := hC₁.trans (le_max_left _ _)
  refine ⟨C,hC,?_⟩
  intro v t N a b ht hN ha hb htupper
  have hNp := zero_lt_one.trans_le hN
  let B := max (19/20:ℝ) (3/4+v/20)
  have hB₁ : 19/20 ≤ B := le_max_left _ _
  have hB₂ : 3/4+v/20 ≤ B := le_max_right _ _
  by_cases hlow : t ≤ N^(8/3:ℝ)
  · have hp := hpair t N a b ht hN ha hb
    norm_num only at hp
    have hmain : (t/N)^(1/6+η)*N^(2/3+η) ≤ N^(B+3*η) := by
      have hid : (t/N)^(1/6+η)*N^(2/3+η) = t^(1/6+η)*N^(1/2:ℝ) := by
        rw [Real.div_rpow ht.le hNp.le]
        calc
          _ = t^(1/6+η)*(N^(2/3+η)/N^(1/6+η)) := by ring
          _ = t^(1/6+η)*N^((2/3+η)-(1/6+η)) := by rw [Real.rpow_sub hNp]
          _ = _ := by congr 2; ring
      rw [hid]
      calc
        _ ≤ (N^(8/3:ℝ))^(1/6+η)*N^(1/2:ℝ) :=
          mul_le_mul_of_nonneg_right
            (Real.rpow_le_rpow ht.le hlow (by linarith only [hη]))
            (Real.rpow_nonneg hNp.le _)
        _ = N^((8/3)*(1/6+η)+1/2) := by
          rw [← Real.rpow_mul hNp.le,← Real.rpow_add hNp]
        _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hN (by linarith only [hB₁,hη])
    have hh := hp.trans (mul_le_mul_of_nonneg_left (add_le_add hmain le_rfl)
      (zero_le_one.trans hC₁))
    exact hh.trans (mul_le_mul_of_nonneg_right (le_max_left C₁ (3*C₂)) (by positivity))
  · have hlo : N^((v+8/3)/2-(v-8/3)/2) ≤ t := by
      convert (le_of_not_ge hlow) using 1
      congr 1
      ring
    have hhi : t ≤ N^((v+8/3)/2+(v-8/3)/2) := by
      convert htupper using 1
      congr 1
      ring
    have hm := heathBrown_window_majorant (k:=5) (η:=η) (B:=B) (by norm_num)
      hN hlo hhi
      (by norm_num [heathBrownDerivativeExponent]; linarith only [hB₂])
      (by norm_num [heathBrownDerivativeExponent]; exact hB₁)
      (by norm_num [heathBrownInverseExponent]; linarith only [hB₁])
    have hs := (hHB t N a b ht hN ha hb).trans
      (mul_le_mul_of_nonneg_left hm (zero_le_one.trans hC₂))
    have hexp : N^(η+B) ≤ N^(B+3*η) :=
      Real.rpow_le_rpow_of_exponent_le hN (by linarith only [hη])
    calc
      _ ≤ C₂*(3*N^(η+B)) := hs
      _ = (3*C₂)*N^(η+B) := by ring
      _ ≤ C*N^(B+3*η) := mul_le_mul (le_max_right C₁ (3*C₂)) hexp
        (Real.rpow_nonneg hNp.le _) (zero_le_one.trans hC)
      _ ≤ C*(N^(B+3*η)+2*Real.pi*N/t) :=
        mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (by positivity))
          (zero_le_one.trans hC)

example {η : ℝ} (hη : 0 < η) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (v t N : ℝ) (a b : ℕ),
      0 < t → 1 ≤ N → N ≤ (a : ℝ) → (b : ℝ) ≤ 2*N → t ≤ N^v →
      ‖∑ n ∈ Finset.Icc a b, (n:ℂ)^(-((t:ℂ)*Complex.I))‖ ≤
        C*(N^(max (19/20) (3/4+v/20)+3*η)+2*Real.pi*N/t) :=
  fifth_correlation_bound hη

#print axioms fifth_correlation_bound


theorem sharp_gram_cardinality_of_correlation (P : LargeValuePattern)
    {C X : ℝ} (hC : 1 ≤ C) (hX : 0 ≤ X)
    (hcorr : ∀ t : ℝ, 0 < t → t ≤ P.T →
      ‖∑ n ∈ P.indices, dirichletPhase n t‖ ≤
        C*(X+2*Real.pi*P.N/t))
    (hvalue : 4*C*P.N*X ≤ P.V^2) :
    (P.ordinates.card:ℝ)*P.V^2 ≤
      4*P.N*(2*P.N+4*Real.pi*C*P.N*(harmonic (Nat.ceil P.T):ℝ)) := by
  classical
  have hNp : 0 < P.N := zero_lt_one.trans P.one_lt_N
  have hC0 : 0 ≤ C := zero_le_one.trans hC
  have hharm : (0:ℝ) ≤ harmonic (Nat.ceil P.T) := by
    exact_mod_cast (Finset.sum_nonneg (fun i _ =>
      inv_nonneg.mpr (Nat.cast_nonneg (i+1))) : (0:ℚ) ≤ harmonic (Nat.ceil P.T))
  by_cases hempty : P.ordinates = ∅
  · simpa only [hempty,Finset.card_empty,Nat.cast_zero,zero_mul] using
      (show 0 ≤ 4*P.N*(2*P.N+4*Real.pi*C*P.N*(harmonic (Nat.ceil P.T):ℝ)) by positivity)
  obtain ⟨t,ht,hgram⟩ := P.exists_large_sharp_gram_row (Finset.nonempty_iff_ne_empty.mpr hempty)
  let S := P.ordinates.erase t
  have hSW : S ⊆ P.ordinates := Finset.erase_subset _ _
  have hnear (u : ℝ) (hu : u ∈ S) : u ≠ t ∧ |u-t| ≤ P.T :=
    ⟨(Finset.mem_erase.mp hu).1,P.ordinate_gap_le_height ht (hSW hu)⟩
  have hpoint (u : ℝ) (hu : u ∈ S) :
      ‖∑ n ∈ P.indices, dirichletPhase n (u-t)‖ ≤
        C*X+(2*Real.pi*C*P.N)*(1/|u-t|) := by
    have hd := hnear u hu
    have hone : 1 ≤ |u-t| := P.ordinates_oneSeparated u (hSW hu) t ht hd.1
    have hh := hcorr |u-t| (by linarith only [hone]) hd.2
    rw [norm_sum_dirichletPhase_abs P.indices (fun n hn => P.index_pos hn) (u-t)] at hh
    convert hh using 1
    ring
  have hrecip : (∑ u ∈ S,1/|u-t|) ≤ 2*(harmonic (Nat.ceil P.T):ℝ) := by
    simpa only [div_one] using atkinson_sum_inv_gap_le_harmonic_ceil
      (G:=1) (by norm_num) P.ordinates_oneSeparated ht hSW hnear
  have hcard : (S.card:ℝ) ≤ P.ordinates.card := by
    exact_mod_cast Finset.card_le_card hSW
  have hsum : (∑ u ∈ S,‖∑ n ∈ P.indices,dirichletPhase n (u-t)‖) ≤
      C*(P.ordinates.card:ℝ)*X+4*Real.pi*C*P.N*(harmonic (Nat.ceil P.T):ℝ) := by
    calc
      _ ≤ ∑ u ∈ S,(C*X+(2*Real.pi*C*P.N)*(1/|u-t|)) := Finset.sum_le_sum hpoint
      _ = (S.card:ℝ)*(C*X)+(2*Real.pi*C*P.N)*(∑ u ∈ S,1/|u-t|) := by
        simp only [Finset.sum_add_distrib,Finset.sum_const,nsmul_eq_mul,Finset.mul_sum]
      _ ≤ (P.ordinates.card:ℝ)*(C*X)+
          (2*Real.pi*C*P.N)*(2*(harmonic (Nat.ceil P.T):ℝ)) :=
        add_le_add (mul_le_mul_of_nonneg_right hcard (by positivity))
          (mul_le_mul_of_nonneg_left hrecip (by positivity))
      _ = _ := by ring
  have hdiag : ‖∑ n ∈ P.indices,dirichletPhase n (t-t)‖ ≤ 2*P.N := by
    simpa only [sub_self,dirichletPhase_zero,Finset.sum_const,nsmul_eq_mul,mul_one,
      Complex.norm_natCast] using P.indices_card_cast_le_two_mul_N
  have hrow : (∑ u ∈ P.ordinates,‖∑ n ∈ P.indices,dirichletPhase n (u-t)‖) ≤
      2*P.N+C*(P.ordinates.card:ℝ)*X+
        4*Real.pi*C*P.N*(harmonic (Nat.ceil P.T):ℝ) := by
    rw [← Finset.sum_erase_add _ _ ht]
    change (∑ u ∈ S,‖∑ n ∈ P.indices,dirichletPhase n (u-t)‖)+
      ‖∑ n ∈ P.indices,dirichletPhase n (t-t)‖ ≤ _
    linarith only [hsum,hdiag]
  have hupper := hgram.trans (mul_le_mul_of_nonneg_left hrow (by positivity))
  have habsorb := mul_le_mul_of_nonneg_left hvalue (Nat.cast_nonneg P.ordinates.card)
  nlinarith only [hupper,habsorb]

example (P : LargeValuePattern) {C X : ℝ} (hC : 1 ≤ C) (hX : 0 ≤ X)
    (hcorr : ∀ t : ℝ, 0 < t → t ≤ P.T →
      ‖∑ n ∈ P.indices, dirichletPhase n t‖ ≤ C*(X+2*Real.pi*P.N/t))
    (hvalue : 4*C*P.N*X ≤ P.V^2) :
    (P.ordinates.card:ℝ)*P.V^2 ≤
      4*P.N*(2*P.N+4*Real.pi*C*P.N*(harmonic (Nat.ceil P.T):ℝ)) :=
  sharp_gram_cardinality_of_correlation P hC hX hcorr hvalue

#print axioms sharp_gram_cardinality_of_correlation


theorem fifth_local_largeValueBound {σ τ : ℝ}
    (hσ : 39/40 < σ) (hτ : 0 ≤ τ) (hτhi : τ < 40*σ-35) :
    IsLargeValueBound σ τ (2-2*σ) := by
  intro ε hε
  let g := min (2*σ-39/20) (2*σ-7/4-τ/20)
  have hg : 0 < g := lt_min (by linarith only [hσ]) (by linarith only [hτhi])
  have hg₁ : g ≤ 2*σ-39/20 := min_le_left _ _
  have hg₂ : g ≤ 2*σ-7/4-τ/20 := min_le_right _ _
  let η := g/32
  let δ := min 1 (min (ε/8) (g/32))
  have hη : 0 < η := by dsimp [η]; positivity
  have hδ : 0 < δ := lt_min (by norm_num) (lt_min (by positivity) (by positivity))
  have hδ1 : δ ≤ 1 := min_le_left _ _
  have hδε : δ ≤ ε/8 := (min_le_right _ _).trans (min_le_left _ _)
  have hδg : δ ≤ g/32 := (min_le_right _ _).trans (min_le_right _ _)
  let B := max (19/20:ℝ) (3/4+(τ+δ)/20)
  have hB : B ≤ 2*σ-2*δ-1-4*η := by
    apply max_le
    · dsimp only [η]
      linarith only [hg₁,hδg,hg]
    · dsimp only [η]
      linarith only [hg₂,hδg,hg]
  obtain ⟨C,hC,hbound⟩ := fifth_correlation_bound hη
  have hev : ∀ᶠ N : ℝ in Filter.atTop, 4*C ≤ N^η :=
    (tendsto_rpow_atTop hη).eventually (Filter.eventually_ge_atTop _)
  obtain ⟨Na,hNa⟩ := Filter.eventually_atTop.mp hev
  obtain ⟨Nd,hNd⟩ := Filter.eventually_atTop.mp
    (eventually_exponentPair_gram_diagonal hC hτ (show 0 < ε/2 by linarith only [hε]))
  let K := max 1 (max Na Nd)
  have hK : 1 ≤ K := le_max_left _ _
  have hKA : Na ≤ K := (le_max_left _ _).trans (le_max_right _ _)
  have hKD : Nd ≤ K := (le_max_right _ _).trans (le_max_right _ _)
  refine ⟨K,hK,δ,hδ,?_⟩
  intro P hN _ hTu hVl _
  have hNp : 0 < P.N := zero_lt_one.trans P.one_lt_N
  have hconstant := hNa P.N (hKA.trans hN)
  have hVpow : P.N^((σ-δ)*(2:ℝ)) ≤ P.V^2 := by
    rw [Real.rpow_mul hNp.le,Real.rpow_two]
    exact pow_le_pow_left₀ (Real.rpow_nonneg hNp.le _) hVl 2
  have hvalue : 4*C*P.N*P.N^(B+3*η) ≤ P.V^2 := by
    calc
      _ ≤ P.N^η*P.N*P.N^(B+3*η) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hconstant hNp.le)
          (Real.rpow_nonneg hNp.le _)
      _ = P.N^(η+1+(B+3*η)) := by
        rw [show P.N^η*P.N = P.N^(η+1) by rw [Real.rpow_add hNp,Real.rpow_one],
          ← Real.rpow_add hNp]
      _ ≤ P.N^((σ-δ)*2) :=
        Real.rpow_le_rpow_of_exponent_le P.one_lt_N.le (by linarith only [hB])
      _ ≤ P.V^2 := hVpow
  have hcorr : ∀ t : ℝ, 0 < t → t ≤ P.T →
      ‖∑ n ∈ P.indices,dirichletPhase n t‖ ≤ C*(P.N^(B+3*η)+2*Real.pi*P.N/t) := by
    intro t ht htT
    have hh := hbound (τ+δ) t P.N P.scale (2*P.scale) ht P.one_lt_N.le P.N_eq_scale.le
      (by rw [Nat.cast_mul,Nat.cast_ofNat,← P.N_eq_scale]) (htT.trans hTu)
    have heq : (∑ n ∈ P.indices,dirichletPhase n t) =
        ∑ n ∈ Finset.Icc P.scale (2*P.scale),(n:ℂ)^(-((t:ℂ)*Complex.I)) := by
      rw [P.indices_eq_dyadicInterval]
      apply Finset.sum_congr rfl
      intro n _
      simp only [dirichletPhase,mul_comm Complex.I (t:ℂ)]
      rfl
    rw [heq]
    exact hh
  have hfinite := sharp_gram_cardinality_of_correlation P hC
    (Real.rpow_nonneg hNp.le (B+3*η)) hcorr hvalue
  have hTpower : P.T ≤ P.N^(τ+1) :=
    hTu.trans (Real.rpow_le_rpow_of_exponent_le P.one_lt_N.le (by linarith only [hδ1]))
  have hdiag := hfinite.trans (hNd P.N (hKD.trans hN) P.T P.T_pos hTpower)
  have hr : (P.ordinates.card:ℝ) ≤ P.N^((2+ε/2)-(σ-δ)*2) := by
    rw [Real.rpow_sub hNp]
    apply (le_div_iff₀ (Real.rpow_pos_of_pos hNp _)).mpr
    exact (mul_le_mul_of_nonneg_left hVpow (Nat.cast_nonneg _)).trans hdiag
  calc
    _ ≤ P.N^((2+ε/2)-(σ-δ)*2) := hr
    _ ≤ P.N^(2-2*σ+ε) :=
      Real.rpow_le_rpow_of_exponent_le P.one_lt_N.le (by linarith only [hδε,hε])
    _ ≤ K*P.N^(2-2*σ+ε) :=
      le_mul_of_one_le_left (Real.rpow_nonneg hNp.le _) hK

example {σ τ : ℝ} (hσ : 39/40 < σ) (hτ : 0 ≤ τ) (hτhi : τ < 40*σ-35) :
    IsLargeValueBound σ τ (2-2*σ) := fifth_local_largeValueBound hσ hτ hτhi

#print axioms fifth_local_largeValueBound


theorem second_density_interior {σ : ℝ} (hσ : 39/40 < σ) (hσ1 : σ < 1) :
    zeroDensityExponent σ ≤ ((2/(15*σ-12):ℝ):EReal) := by
  have hh : zeroDensityExponent σ ≤ ((3/((45*σ-36)/2):ℝ):EReal) := by
    apply zeroDensityExponent_le_three_div_of_montgomery_range σ ((45*σ-36)/2)
      (by linarith only [hσ]) hσ1 (by linarith only [hσ])
    · intro τ hτ
      rw [second_zeta hσ.le hτ.1 (by linarith only [hτ.2])]
      exact bot_le
    · intro τ hτ
      exact largeValueExponent_le_of_bound (fifth_local_largeValueBound hσ hτ.1
        (by linarith only [hσ,hτ.2]))
  have he : (45*σ-36)/2 = (3/2)*(15*σ-12) := by ring
  simpa only [he,div_mul_eq_div_div,show (3:ℝ)/(3/2)=2 by norm_num] using hh

theorem third_zeta_interior {σ τ : ℝ}
    (hσ : 41/42 < σ) (hσ1 : σ < 1)
    (hτ : 2 ≤ τ) (hτhi : τ < 4*(40*σ-35)/3) :
    zetaLargeValueExponent σ τ = ⊥ := by
  by_cases ht : τ ≤ 4
  · exact second_zeta (by linarith only [hσ]) hτ
      (by linarith only [hσ,ht])
  · apply heathBrown_zeta_nonexistence (k:=7) (by norm_num)
    · norm_num [heathBrownDerivativeExponent]
      linarith only [hτhi,hσ1]
    · norm_num [heathBrownDerivativeExponent]
      exact hσ
    · norm_num [heathBrownInverseExponent]
      linarith only [ht,hσ]

theorem third_density_interior {σ : ℝ} (hσ : 41/42 < σ) (hσ1 : σ < 1) :
    zeroDensityExponent σ ≤ ((3/(40*σ-35):ℝ):EReal) := by
  apply zeroDensityExponent_le_three_div_of_montgomery_range σ (40*σ-35)
    (by linarith only [hσ]) hσ1 (by linarith only [hσ])
  · intro τ hτ
    rw [third_zeta_interior hσ hσ1 hτ.1 hτ.2]
    exact bot_le
  · intro τ hτ
    exact largeValueExponent_le_of_bound (fifth_local_largeValueBound
      (by linarith only [hσ]) hτ.1 (by linarith only [hτ.2,hσ1]))

example {σ : ℝ} (hσ : 39/40 < σ) (hσ1 : σ < 1) :
    zeroDensityExponent σ ≤ ((2/(15*σ-12):ℝ):EReal) :=
  second_density_interior hσ hσ1

example {σ τ : ℝ} (hσ : 41/42 < σ) (hσ1 : σ < 1)
    (hτ : 2 ≤ τ) (hτhi : τ < 4*(40*σ-35)/3) :
    zetaLargeValueExponent σ τ = ⊥ := third_zeta_interior hσ hσ1 hτ hτhi

example {σ : ℝ} (hσ : 41/42 < σ) (hσ1 : σ < 1) :
    zeroDensityExponent σ ≤ ((3/(40*σ-35):ℝ):EReal) :=
  third_density_interior hσ hσ1

example : zeroDensityExponent (1951/2000) ≤ ((2/(15*(1951/2000)-12):ℝ):EReal) :=
  second_density_interior (by norm_num) (by norm_num)

example : zeroDensityExponent (41/42) ≤ ((2/(15*(41/42)-12):ℝ):EReal) :=
  second_density_interior (by norm_num) (by norm_num)

example : zeroDensityExponent (49/50) ≤ ((3/(40*(49/50)-35):ℝ):EReal) :=
  third_density_interior (by norm_num) (by norm_num)

example : zeroDensityExponent (59/60) ≤ ((3/(40*(59/60)-35):ℝ):EReal) :=
  third_density_interior (by norm_num) (by norm_num)

#print axioms second_density_interior
#print axioms third_zeta_interior
#print axioms third_density_interior


theorem exists_heathBrown_order_for_cell {n : ℕ} (hn : 3 ≤ n)
    {γ s : ℝ} (hγ : 0 ≤ γ) (hγhi : γ ≤ 1/24)
    (hcell : 2*γ*(n:ℝ)*((n:ℝ)-1) ≤ 1)
    (hs : 1 ≤ s) (hupper : s ≤ (n:ℝ)*(1-2*((n:ℝ)-1)*γ)) :
    ∃ j : ℕ, 3 ≤ j ∧ j ≤ n ∧
      1+(s-(j:ℝ))*heathBrownDerivativeExponent j ≤ 1-2*γ ∧
      1-heathBrownDerivativeExponent j ≤ 1-2*γ ∧
      1-s*heathBrownInverseExponent j ≤ 1-2*γ := by
  classical
  have hex : ∃ j : ℕ, 3 ≤ j ∧ j ≤ n ∧
      s ≤ (j:ℝ)*(1-2*((j:ℝ)-1)*γ) := ⟨n,hn,le_rfl,hupper⟩
  let j := Nat.find hex
  obtain ⟨hj,hjn,huj⟩ := Nat.find_spec hex
  change 3 ≤ j at hj
  change j ≤ n at hjn
  change s ≤ (j:ℝ)*(1-2*((j:ℝ)-1)*γ) at huj
  have hjr : (3:ℝ) ≤ j := by exact_mod_cast hj
  have hjnr : (j:ℝ) ≤ n := by exact_mod_cast hjn
  have hprod : (j:ℝ)*((j:ℝ)-1) ≤ (n:ℝ)*((n:ℝ)-1) :=
    mul_le_mul hjnr (sub_le_sub_right hjnr 1) (by linarith only [hjr]) (Nat.cast_nonneg n)
  have hjcell : 2*γ*(j:ℝ)*((j:ℝ)-1) ≤ 1 := by
    have hh := mul_le_mul_of_nonneg_left hprod (show 0 ≤ 2*γ by positivity)
    nlinarith only [hh,hcell]
  have hlow : γ*(j:ℝ)^2*((j:ℝ)-1) ≤ s := by
    by_cases hj3 : j = 3
    · norm_num only [hj3,Nat.cast_ofNat]
      linarith only [hγhi,hs]
    · have hj4 : 4 ≤ j := by omega
      have hprev := Nat.find_min hex (show j-1 < Nat.find hex by change j-1 < j; omega)
      have hprevUpper : ((j-1:ℕ):ℝ)*(1-2*(((j-1:ℕ):ℝ)-1)*γ) < s := by
        apply lt_of_not_ge
        intro h
        exact hprev ⟨by omega,by omega,h⟩
      have hcast : ((j-1:ℕ):ℝ) = (j:ℝ)-1 := by
        rw [Nat.cast_sub (by omega : 1 ≤ j)]
        norm_num
      rw [hcast] at hprevUpper
      have hbudget : γ*((j:ℝ)^2+2*(j:ℝ)-4) ≤ 1 := by
        nlinarith only [hjcell,mul_nonneg hγ (sq_nonneg ((j:ℝ)-2))]
      have hm := mul_le_mul_of_nonneg_right hbudget
        (show 0 ≤ (j:ℝ)-1 by linarith only [hjr])
      nlinarith only [hm,hprevUpper]
  have hd : 0 < (j:ℝ)*((j:ℝ)-1) := by
    apply mul_pos <;> linarith only [hjr]
  have he : 0 < (j:ℝ)^2*((j:ℝ)-1) := by
    have hjp : 0 < (j:ℝ) := by linarith only [hjr]
    exact mul_pos (pow_pos hjp 2) (by linarith only [hjr])
  refine ⟨j,hj,hjn,?_,?_,?_⟩
  · have hh : (s-(j:ℝ))/((j:ℝ)*((j:ℝ)-1)) ≤ -2*γ := by
      apply (div_le_iff₀ hd).mpr
      nlinarith only [huj]
    unfold heathBrownDerivativeExponent
    rw [mul_one_div]
    linarith only [hh]
  · have hh : 2*γ ≤ 1/((j:ℝ)*((j:ℝ)-1)) := by
      apply (le_div_iff₀ hd).mpr
      nlinarith only [hjcell]
    unfold heathBrownDerivativeExponent
    linarith only [hh]
  · have hh : 2*γ ≤ 2*s/((j:ℝ)^2*((j:ℝ)-1)) := by
      apply (le_div_iff₀ he).mpr
      nlinarith only [hlow]
    unfold heathBrownInverseExponent
    rw [show s*(2/((j:ℝ)^2*((j:ℝ)-1))) = 2*s/((j:ℝ)^2*((j:ℝ)-1)) by ring]
    linarith only [hh]

example {n : ℕ} (hn : 3 ≤ n) {γ s : ℝ} (hγ : 0 ≤ γ) (hγhi : γ ≤ 1/24)
    (hcell : 2*γ*(n:ℝ)*((n:ℝ)-1) ≤ 1)
    (hs : 1 ≤ s) (hupper : s ≤ (n:ℝ)*(1-2*((n:ℝ)-1)*γ)) :
    ∃ j : ℕ, 3 ≤ j ∧ j ≤ n ∧
      1+(s-(j:ℝ))*heathBrownDerivativeExponent j ≤ 1-2*γ ∧
      1-heathBrownDerivativeExponent j ≤ 1-2*γ ∧
      1-s*heathBrownInverseExponent j ≤ 1-2*γ :=
  exists_heathBrown_order_for_cell hn hγ hγhi hcell hs hupper

#print axioms exists_heathBrown_order_for_cell


theorem cell_correlation_bound {n : ℕ} (hn : 3 ≤ n)
    {γ η : ℝ} (hγ : 0 ≤ γ) (hγhi : γ ≤ 1/24)
    (hcell : 2*γ*(n:ℝ)*((n:ℝ)-1) ≤ 1) (hη : 0 < η) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (v t N : ℝ) (a b : ℕ),
      v ≤ (n:ℝ)*(1-2*((n:ℝ)-1)*γ) →
      0 < t → 1 < N → N ≤ (a:ℝ) → (b:ℝ) ≤ 2*N → t ≤ N^v →
      ‖∑ m ∈ Finset.Icc a b,(m:ℂ)^(-((t:ℂ)*Complex.I))‖ ≤
        C*(N^(1-2*γ+3*η)+2*Real.pi*N/t) := by
  classical
  let J := {j : ℕ // j ∈ Finset.Icc 3 n}
  letI : Fintype J := Finset.fintypeCoeSort (Finset.Icc 3 n)
  have hex : ∀ j : J, ∃ C : ℝ, 1 ≤ C ∧ ∀ (t N : ℝ) (a b : ℕ),
      0 < t → 1 ≤ N → N ≤ (a:ℝ) → (b:ℝ) ≤ 2*N →
      ‖∑ m ∈ Finset.Icc a b,(m:ℂ)^(-((t:ℂ)*Complex.I))‖ ≤
        C*heathBrownPowerMajorant j.val η t N := by
    intro j
    exact heathBrown_logarithmic_sum_bound (Finset.mem_Icc.mp j.property).1 hη
  choose Cj hCj hBj using hex
  let D := ∑ j : J,Cj j
  have hjD (j : J) : Cj j ≤ D :=
    Finset.single_le_sum (fun i _ => zero_le_one.trans (hCj i)) (Finset.mem_univ j)
  obtain ⟨C₁,hC₁,hpair⟩ := exponentPair_half_half.aProcess.logarithmic_sum_bound hη
  let C := max C₁ (3*D)
  have hC : 1 ≤ C := hC₁.trans (le_max_left _ _)
  refine ⟨C,hC,?_⟩
  intro v t N a b hv ht hN ha hb htv
  have hNp : 0 < N := zero_lt_one.trans hN
  by_cases hlow : t ≤ N
  · have hp := hpair t N a b ht hN.le ha hb
    norm_num only at hp
    have hmain : (t/N)^(1/6+η)*N^(2/3+η) ≤ N^(1-2*γ+3*η) := by
      have hratio : (t/N)^(1/6+η) ≤ 1 := by
        apply Real.rpow_le_one (by positivity) ((div_le_one hNp).mpr hlow)
        linarith only [hη]
      calc
        _ ≤ 1*N^(2/3+η) := mul_le_mul_of_nonneg_right hratio (Real.rpow_nonneg hNp.le _)
        _ = N^(2/3+η) := one_mul _
        _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hN.le (by linarith only [hγhi,hη])
    have hh := hp.trans (mul_le_mul_of_nonneg_left (add_le_add hmain le_rfl)
      (zero_le_one.trans hC₁))
    exact hh.trans (mul_le_mul_of_nonneg_right (le_max_left C₁ (3*D)) (by positivity))
  · let s := Real.logb N t
    have hs : 1 ≤ s := by
      have hh := Real.logb_le_logb_of_le hN hNp (le_of_not_ge hlow)
      simpa only [Real.logb_self_eq_one hN] using hh
    have hsv : s ≤ v := (Real.logb_le_iff_le_rpow hN ht).mpr htv
    obtain ⟨j,hj,hjn,hfirst,hsecond,hthird⟩ :=
      exists_heathBrown_order_for_cell hn hγ hγhi hcell hs (hsv.trans hv)
    let j₀ : J := ⟨j,Finset.mem_Icc.mpr ⟨hj,hjn⟩⟩
    have hpow : N^s = t := Real.rpow_logb hNp (ne_of_gt hN) ht
    have hm := heathBrown_window_majorant (k:=j) (η:=η) (τ:=s) (δ:=0)
      (B:=1-2*γ) hj hN.le (by simpa only [sub_zero] using hpow.le)
      (by simpa only [add_zero] using hpow.ge)
      (by simpa only [add_zero] using hfirst) hsecond
      (by simpa only [sub_zero] using hthird)
    have hh := (hBj j₀ t N a b ht hN.le ha hb).trans
      (mul_le_mul_of_nonneg_left hm (zero_le_one.trans (hCj j₀)))
    have hconst : 3*Cj j₀ ≤ C :=
      (mul_le_mul_of_nonneg_left (hjD j₀) (by norm_num : (0:ℝ) ≤ 3)).trans
        (le_max_right C₁ (3*D))
    have he : N^(η+(1-2*γ)) ≤ N^(1-2*γ+3*η) :=
      Real.rpow_le_rpow_of_exponent_le hN.le (by linarith only [hη])
    calc
      _ ≤ Cj j₀*(3*N^(η+(1-2*γ))) := hh
      _ = (3*Cj j₀)*N^(η+(1-2*γ)) := by ring
      _ ≤ C*N^(1-2*γ+3*η) := mul_le_mul hconst he
        (Real.rpow_nonneg hNp.le _) (zero_le_one.trans hC)
      _ ≤ C*(N^(1-2*γ+3*η)+2*Real.pi*N/t) :=
        mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (by positivity))
          (zero_le_one.trans hC)

example {n : ℕ} (hn : 3 ≤ n) {γ η : ℝ} (hγ : 0 ≤ γ) (hγhi : γ ≤ 1/24)
    (hcell : 2*γ*(n:ℝ)*((n:ℝ)-1) ≤ 1) (hη : 0 < η) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (v t N : ℝ) (a b : ℕ),
      v ≤ (n:ℝ)*(1-2*((n:ℝ)-1)*γ) →
      0 < t → 1 < N → N ≤ (a:ℝ) → (b:ℝ) ≤ 2*N → t ≤ N^v →
      ‖∑ m ∈ Finset.Icc a b,(m:ℂ)^(-((t:ℂ)*Complex.I))‖ ≤
        C*(N^(1-2*γ+3*η)+2*Real.pi*N/t) :=
  cell_correlation_bound hn hγ hγhi hcell hη

#print axioms cell_correlation_bound


theorem cell_local_largeValueBound {n : ℕ} (hn : 3 ≤ n)
    {γ σ τ : ℝ} (hγ : 0 ≤ γ) (hγhi : γ ≤ 1/24)
    (hcell : 2*γ*(n:ℝ)*((n:ℝ)-1) ≤ 1)
    (hσ : 1-γ < σ) (hτ : 0 ≤ τ)
    (hτhi : τ < (n:ℝ)*(1-2*((n:ℝ)-1)*γ)) :
    IsLargeValueBound σ τ (2-2*σ) := by
  intro ε hε
  let g := σ-(1-γ)
  let h := (n:ℝ)*(1-2*((n:ℝ)-1)*γ)-τ
  have hg : 0 < g := sub_pos.mpr hσ
  have hheight : 0 < h := sub_pos.mpr hτhi
  let η := g/32
  let δ := min 1 (min (ε/8) (min (g/8) (h/2)))
  have hη : 0 < η := by dsimp [η]; positivity
  have hδ : 0 < δ := lt_min (by norm_num)
    (lt_min (by positivity) (lt_min (by positivity) (by positivity)))
  have hδ1 : δ ≤ 1 := min_le_left _ _
  have hδε : δ ≤ ε/8 := (min_le_right _ _).trans (min_le_left _ _)
  have hδtail : δ ≤ min (g/8) (h/2) :=
    (min_le_right _ _).trans (min_le_right _ _)
  have hδg : δ ≤ g/8 := hδtail.trans (min_le_left _ _)
  have hδh : δ ≤ h/2 := hδtail.trans (min_le_right _ _)
  let B := 1-2*γ
  have hB : B ≤ 2*σ-2*δ-1-4*η := by
    dsimp only [B,η,g] at hg hδg ⊢
    linarith only [hg,hδg]
  obtain ⟨C,hC,hbound⟩ := cell_correlation_bound hn hγ hγhi hcell hη
  have hev : ∀ᶠ N : ℝ in Filter.atTop, 4*C ≤ N^η :=
    (tendsto_rpow_atTop hη).eventually (Filter.eventually_ge_atTop _)
  obtain ⟨Na,hNa⟩ := Filter.eventually_atTop.mp hev
  obtain ⟨Nd,hNd⟩ := Filter.eventually_atTop.mp
    (eventually_exponentPair_gram_diagonal hC hτ (show 0 < ε/2 by linarith only [hε]))
  let K := max 1 (max Na Nd)
  have hK : 1 ≤ K := le_max_left _ _
  have hKA : Na ≤ K := (le_max_left _ _).trans (le_max_right _ _)
  have hKD : Nd ≤ K := (le_max_right _ _).trans (le_max_right _ _)
  refine ⟨K,hK,δ,hδ,?_⟩
  intro P hN _ hTu hVl _
  have hNp : 0 < P.N := zero_lt_one.trans P.one_lt_N
  have hconstant := hNa P.N (hKA.trans hN)
  have hVpow : P.N^((σ-δ)*(2:ℝ)) ≤ P.V^2 := by
    rw [Real.rpow_mul hNp.le,Real.rpow_two]
    exact pow_le_pow_left₀ (Real.rpow_nonneg hNp.le _) hVl 2
  have hvalue : 4*C*P.N*P.N^(B+3*η) ≤ P.V^2 := by
    calc
      _ ≤ P.N^η*P.N*P.N^(B+3*η) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hconstant hNp.le)
          (Real.rpow_nonneg hNp.le _)
      _ = P.N^(η+1+(B+3*η)) := by
        rw [show P.N^η*P.N = P.N^(η+1) by rw [Real.rpow_add hNp,Real.rpow_one],
          ← Real.rpow_add hNp]
      _ ≤ P.N^((σ-δ)*2) :=
        Real.rpow_le_rpow_of_exponent_le P.one_lt_N.le (by linarith only [hB])
      _ ≤ P.V^2 := hVpow
  have hcorr : ∀ t : ℝ, 0 < t → t ≤ P.T →
      ‖∑ n ∈ P.indices,dirichletPhase n t‖ ≤ C*(P.N^(B+3*η)+2*Real.pi*P.N/t) := by
    intro t ht htT
    have hh := hbound (τ+δ) t P.N P.scale (2*P.scale)
      (by dsimp only [h] at hδh; linarith only [hδh,hheight]) ht P.one_lt_N P.N_eq_scale.le
      (by rw [Nat.cast_mul,Nat.cast_ofNat,← P.N_eq_scale]) (htT.trans hTu)
    have heq : (∑ n ∈ P.indices,dirichletPhase n t) =
        ∑ n ∈ Finset.Icc P.scale (2*P.scale),(n:ℂ)^(-((t:ℂ)*Complex.I)) := by
      rw [P.indices_eq_dyadicInterval]
      apply Finset.sum_congr rfl
      intro n _
      simp only [dirichletPhase,mul_comm Complex.I (t:ℂ)]
      rfl
    rw [heq]
    exact hh
  have hfinite := sharp_gram_cardinality_of_correlation P hC
    (Real.rpow_nonneg hNp.le (B+3*η)) hcorr hvalue
  have hTpower : P.T ≤ P.N^(τ+1) :=
    hTu.trans (Real.rpow_le_rpow_of_exponent_le P.one_lt_N.le (by linarith only [hδ1]))
  have hdiag := hfinite.trans (hNd P.N (hKD.trans hN) P.T P.T_pos hTpower)
  have hr : (P.ordinates.card:ℝ) ≤ P.N^((2+ε/2)-(σ-δ)*2) := by
    rw [Real.rpow_sub hNp]
    apply (le_div_iff₀ (Real.rpow_pos_of_pos hNp _)).mpr
    exact (mul_le_mul_of_nonneg_left hVpow (Nat.cast_nonneg _)).trans hdiag
  calc
    _ ≤ P.N^((2+ε/2)-(σ-δ)*2) := hr
    _ ≤ P.N^(2-2*σ+ε) :=
      Real.rpow_le_rpow_of_exponent_le P.one_lt_N.le (by linarith only [hδε,hε])
    _ ≤ K*P.N^(2-2*σ+ε) :=
      le_mul_of_one_le_left (Real.rpow_nonneg hNp.le _) hK

example {n : ℕ} (hn : 3 ≤ n) {γ σ τ : ℝ} (hγ : 0 ≤ γ) (hγhi : γ ≤ 1/24)
    (hcell : 2*γ*(n:ℝ)*((n:ℝ)-1) ≤ 1) (hσ : 1-γ < σ) (hτ : 0 ≤ τ)
    (hτhi : τ < (n:ℝ)*(1-2*((n:ℝ)-1)*γ)) :
    IsLargeValueBound σ τ (2-2*σ) :=
  cell_local_largeValueBound hn hγ hγhi hcell hσ hτ hτhi

#print axioms cell_local_largeValueBound


theorem exists_strict_cell_margin {n : ℕ} (hn : 4 ≤ n)
    {γ₀ τ : ℝ} (hγ₀ : 0 ≤ γ₀)
    (hcell : 2*γ₀*(n:ℝ)*((n:ℝ)-1) < 1)
    (hτ : τ < (n:ℝ)*(1-2*((n:ℝ)-1)*γ₀)) :
    ∃ γ : ℝ, γ₀ < γ ∧ 0 ≤ γ ∧ γ ≤ 1/24 ∧
      2*γ*(n:ℝ)*((n:ℝ)-1) ≤ 1 ∧
      τ < (n:ℝ)*(1-2*((n:ℝ)-1)*γ) := by
  have hnr : (4:ℝ) ≤ n := by exact_mod_cast hn
  let P := (n:ℝ)*((n:ℝ)-1)
  have hP : 12 ≤ P := by dsimp [P]; nlinarith only [hnr]
  have hPpos : 0 < P := by linarith only [hP]
  have hcellP : 2*γ₀*P < 1 := by dsimp only [P]; nlinarith only [hcell]
  let H := (n:ℝ)*(1-2*((n:ℝ)-1)*γ₀)-τ
  have hH : 0 < H := sub_pos.mpr hτ
  let a := min ((1-2*γ₀*P)/(4*P)) (H/(4*P))
  have ha : 0 < a := lt_min (div_pos (by linarith only [hcellP]) (by positivity))
    (div_pos hH (by positivity))
  have haC : 4*P*a ≤ 1-2*γ₀*P := by
    have hh := (le_div_iff₀ (by positivity : 0 < 4*P)).mp
      (show a ≤ (1-2*γ₀*P)/(4*P) from min_le_left _ _)
    nlinarith only [hh]
  have haH : 4*P*a ≤ H := by
    have hh := (le_div_iff₀ (by positivity : 0 < 4*P)).mp
      (show a ≤ H/(4*P) from min_le_right _ _)
    nlinarith only [hh]
  have hγ : 0 ≤ γ₀+a := add_nonneg hγ₀ ha.le
  have hγP : 2*(γ₀+a)*P ≤ 1 := by
    nlinarith only [haC,hcellP]
  have hγhi : γ₀+a ≤ 1/24 := by
    have hm := mul_le_mul_of_nonneg_left hP (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) hγ)
    nlinarith only [hm,hγP]
  refine ⟨γ₀+a,by linarith only [ha],hγ,hγhi,?_,?_⟩
  · dsimp only [P] at hγP
    nlinarith only [hγP]
  · dsimp only [P,H] at haH hH
    nlinarith only [haH,hH]

example {n : ℕ} (hn : 4 ≤ n) {γ₀ τ : ℝ} (hγ₀ : 0 ≤ γ₀)
    (hcell : 2*γ₀*(n:ℝ)*((n:ℝ)-1) < 1)
    (hτ : τ < (n:ℝ)*(1-2*((n:ℝ)-1)*γ₀)) :
    ∃ γ : ℝ, γ₀ < γ ∧ 0 ≤ γ ∧ γ ≤ 1/24 ∧
      2*γ*(n:ℝ)*((n:ℝ)-1) ≤ 1 ∧
      τ < (n:ℝ)*(1-2*((n:ℝ)-1)*γ) :=
  exists_strict_cell_margin hn hγ₀ hcell hτ

#print axioms exists_strict_cell_margin

theorem heathBrown_cell_montgomery {n : ℕ} (hn : 4 ≤ n)
    {σ τ : ℝ} (hσ1 : σ ≤ 1)
    (hcell : 2*(1-σ)*(n:ℝ)*((n:ℝ)-1) < 1)
    (hτ : 0 ≤ τ) (hτhi : τ < (n:ℝ)*(1-2*((n:ℝ)-1)*(1-σ))) :
    IsLargeValueBound σ τ (2-2*σ) := by
  obtain ⟨γ,hγgap,hγ,hγhi,hγcell,hγτ⟩ :=
    exists_strict_cell_margin hn (sub_nonneg.mpr hσ1) hcell hτhi
  exact cell_local_largeValueBound (by omega) hγ hγhi hγcell
    (by linarith only [hγgap]) hτ hγτ

example {n : ℕ} (hn : 4 ≤ n) {σ τ : ℝ} (hσ1 : σ ≤ 1)
    (hcell : 2*(1-σ)*(n:ℝ)*((n:ℝ)-1) < 1)
    (hτ : 0 ≤ τ) (hτhi : τ < (n:ℝ)*(1-2*((n:ℝ)-1)*(1-σ))) :
    IsLargeValueBound σ τ (2-2*σ) :=
  heathBrown_cell_montgomery hn hσ1 hcell hτ hτhi

#print axioms heathBrown_cell_montgomery

theorem heathBrown_cell_zeta {n : ℕ} (hn : 4 ≤ n)
    {σ τ : ℝ} (hσ1 : σ ≤ 1)
    (hcell : (1-σ)*(n:ℝ)*((n:ℝ)-1) < 1)
    (hτ : 1 ≤ τ) (hτhi : τ < (n:ℝ)*(1-((n:ℝ)-1)*(1-σ))) :
    zetaLargeValueExponent σ τ = ⊥ := by
  obtain ⟨γ,hγgap,hγ,hγhi,hγcell,hγτ⟩ :=
    exists_strict_cell_margin (γ₀:=(1-σ)/2) (τ:=τ) hn (by linarith only [hσ1])
      (by nlinarith only [hcell]) (by nlinarith only [hτhi])
  obtain ⟨j,hj,_hjn,hfirst,hsecond,hthird⟩ :=
    exists_heathBrown_order_for_cell (by omega) hγ hγhi hγcell hτ hγτ.le
  apply heathBrown_zeta_nonexistence hj
  · linarith only [hfirst,hγgap]
  · linarith only [hsecond,hγgap]
  · linarith only [hthird,hγgap]

example {n : ℕ} (hn : 4 ≤ n) {σ τ : ℝ} (hσ1 : σ ≤ 1)
    (hcell : (1-σ)*(n:ℝ)*((n:ℝ)-1) < 1)
    (hτ : 1 ≤ τ) (hτhi : τ < (n:ℝ)*(1-((n:ℝ)-1)*(1-σ))) :
    zetaLargeValueExponent σ τ = ⊥ :=
  heathBrown_cell_zeta hn hσ1 hcell hτ hτhi

#print axioms heathBrown_cell_zeta

theorem exists_pintz_tail_zeta_order {n : ℕ} (hn : 6 ≤ n)
    {η : ℝ} (hη : 0 ≤ η)
    (hupper : 2*η*(n:ℝ)*((n:ℝ)-1) < 1)
    (hlower : 1 ≤ 2*η*(n:ℝ)*((n:ℝ)+1)) :
    ∃ m : ℕ, 4 ≤ m ∧ η*(m:ℝ)*((m:ℝ)-1) < 1 ∧
      4*((n:ℝ)*(1-2*((n:ℝ)-1)*η))/3 ≤
        (m:ℝ)*(1-((m:ℝ)-1)*η) := by
  let m := (4*n+1)/3
  have hm : 4 ≤ m := by dsimp only [m]; omega
  have hmlo : 4*n ≤ 3*m+1 := by dsimp only [m]; omega
  have hmhi : 3*m ≤ 4*n+1 := by dsimp only [m]; omega
  have hnr : (6:ℝ) ≤ n := by exact_mod_cast hn
  have hmr : (4:ℝ) ≤ m := by exact_mod_cast hm
  have hmlor : 4*(n:ℝ) ≤ 3*(m:ℝ)+1 := by exact_mod_cast hmlo
  have hmhir : 3*(m:ℝ) ≤ 4*(n:ℝ)+1 := by exact_mod_cast hmhi
  have hprod : (m:ℝ)*((m:ℝ)-1) ≤ 2*(n:ℝ)*((n:ℝ)-1) := by
    by_cases hn6 : n = 6
    · norm_num [m,hn6]
    · have hn7 : (7:ℝ) ≤ n := by exact_mod_cast (show 7 ≤ n by omega)
      have hsq : (3*(m:ℝ))^2 ≤ (4*(n:ℝ)+1)^2 :=
        sq_le_sq₀ (by positivity) (by positivity) |>.2 hmhir
      have hdiff := mul_nonneg (show 0 ≤ (n:ℝ)-7 by linarith only [hn7])
        (show 0 ≤ (n:ℝ) by positivity)
      nlinarith only [hsq,hmhir,hmr,hdiff,hmlor]
  have hcell : η*(m:ℝ)*((m:ℝ)-1) < 1 := by
    have hh := mul_le_mul_of_nonneg_left hprod hη
    nlinarith only [hh,hupper]
  let B := 8*(n:ℝ)*((n:ℝ)-1)/3-(m:ℝ)*((m:ℝ)-1)
  have hB : 0 ≤ B := by dsimp only [B]; nlinarith only [hprod,hnr]
  refine ⟨m,hm,hcell,?_⟩
  by_cases hhigh : 4*n ≤ 3*m
  · have hh : 4*(n:ℝ) ≤ 3*(m:ℝ) := by exact_mod_cast hhigh
    have hhB := mul_nonneg hη hB
    dsimp only [B] at hhB
    nlinarith only [hh,hhB]
  · have he : 3*m+1 = 4*n := by omega
    have her : 3*(m:ℝ)+1 = 4*(n:ℝ) := by exact_mod_cast he
    have hBstrong : 2*(n:ℝ)*((n:ℝ)+1)/3 ≤ B := by
      have hdiff := mul_nonneg (show 0 ≤ (n:ℝ)-6 by linarith only [hnr])
        (show 0 ≤ (n:ℝ) by positivity)
      dsimp only [B]
      nlinarith only [her,hdiff,hnr,sq_nonneg (3*(m:ℝ)+1-4*(n:ℝ))]
    have hh := mul_le_mul_of_nonneg_left hBstrong hη
    dsimp only [B] at hh
    nlinarith only [hh,hlower,her]

example {n : ℕ} (hn : 6 ≤ n) {η : ℝ} (hη : 0 ≤ η)
    (hupper : 2*η*(n:ℝ)*((n:ℝ)-1) < 1)
    (hlower : 1 ≤ 2*η*(n:ℝ)*((n:ℝ)+1)) :
    ∃ m : ℕ, 4 ≤ m ∧ η*(m:ℝ)*((m:ℝ)-1) < 1 ∧
      4*((n:ℝ)*(1-2*((n:ℝ)-1)*η))/3 ≤
        (m:ℝ)*(1-((m:ℝ)-1)*η) :=
  exists_pintz_tail_zeta_order hn hη hupper hlower

#print axioms exists_pintz_tail_zeta_order

theorem tail_density_interior {n : ℕ} (hn : 6 ≤ n) {σ : ℝ}
    (hσlo : 1-1/(2*(n:ℝ)*((n:ℝ)-1)) < σ)
    (hσhi : σ ≤ 1-1/(2*(n:ℝ)*((n:ℝ)+1))) :
    zeroDensityExponent σ ≤
      ((3/((n:ℝ)*(1-2*((n:ℝ)-1)*(1-σ))):ℝ):EReal) := by
  have hnr : (6:ℝ) ≤ n := by exact_mod_cast hn
  have hD : 0 < 2*(n:ℝ)*((n:ℝ)-1) := by
    apply mul_pos <;> linarith only [hnr]
  have hD' : 0 < 2*(n:ℝ)*((n:ℝ)+1) := by positivity
  have hσ1 : σ < 1 := by
    have hh := one_div_pos.mpr hD'
    linarith only [hσhi,hh]
  have hη : 0 ≤ 1-σ := sub_nonneg.mpr hσ1.le
  have hupper : 2*(1-σ)*(n:ℝ)*((n:ℝ)-1) < 1 := by
    have hh := (lt_div_iff₀ hD).mp
      (show 1-σ < 1/(2*(n:ℝ)*((n:ℝ)-1)) by linarith only [hσlo])
    nlinarith only [hh]
  have hlower : 1 ≤ 2*(1-σ)*(n:ℝ)*((n:ℝ)+1) := by
    have hh := (div_le_iff₀ hD').mp
      (show 1/(2*(n:ℝ)*((n:ℝ)+1)) ≤ 1-σ by linarith only [hσhi])
    nlinarith only [hh]
  have hσhalf : 1/2 < σ := by
    have hprod : (30:ℝ) ≤ (n:ℝ)*((n:ℝ)-1) := by nlinarith only [hnr]
    have hh := mul_le_mul_of_nonneg_left hprod (show 0 ≤ 2*(1-σ) by positivity)
    nlinarith only [hh,hupper]
  have hcut : 0 < (n:ℝ)*(1-2*((n:ℝ)-1)*(1-σ)) := by
    nlinarith only [hupper,hnr]
  obtain ⟨m,hm,hmcell,hmrange⟩ := exists_pintz_tail_zeta_order hn hη hupper hlower
  apply zeroDensityExponent_le_three_div_of_montgomery_range σ
    ((n:ℝ)*(1-2*((n:ℝ)-1)*(1-σ))) hσhalf hσ1 hcut
  · intro τ hτ
    rw [heathBrown_cell_zeta hm hσ1.le hmcell (by linarith only [hτ.1])
      (hτ.2.trans_le hmrange)]
    exact bot_le
  · intro τ hτ
    exact largeValueExponent_le_of_bound (heathBrown_cell_montgomery
      (by omega : 4 ≤ n) hσ1.le hupper hτ.1 (by linarith only [hτ.2,hσ1]))

example {n : ℕ} (hn : 6 ≤ n) {σ : ℝ}
    (hσlo : 1-1/(2*(n:ℝ)*((n:ℝ)-1)) < σ)
    (hσhi : σ ≤ 1-1/(2*(n:ℝ)*((n:ℝ)+1))) :
    zeroDensityExponent σ ≤
      ((3/((n:ℝ)*(1-2*((n:ℝ)-1)*(1-σ))):ℝ):EReal) :=
  tail_density_interior hn hσlo hσhi

example : zeroDensityExponent (99/100) ≤
    ((3/((7:ℝ)*(1-2*(7-1)*(1-99/100)))):EReal) :=
  tail_density_interior (n:=7) (by norm_num) (by norm_num) (by norm_num)

example : zeroDensityExponent (83/84) ≤
    ((3/((6:ℝ)*(1-2*(6-1)*(1-83/84)))):EReal) :=
  tail_density_interior (n:=6) (by norm_num) (by norm_num) (by norm_num)

#print axioms tail_density_interior

end PintzLiteratureScratch
