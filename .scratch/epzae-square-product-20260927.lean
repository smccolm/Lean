import TaoTrudgianYang2025.LogarithmicSixthMoment
import TaoTrudgianYang2025.SargosDualTentWindow

/-! Actual mixed logarithmic moments for the signed square/product count.
The full signed count and cubic eighth moment are not yet claimed. -/

noncomputable section
open Set MeasureTheory GafniTao
open scoped BigOperators
namespace TaoTrudgianYang2025.SquareProductPrototype
open LogarithmicSixth

def logSum (S : Finset ℕ) (p : ℝ × ℝ) : ℂ :=
  ∑ n∈S, fordAdditiveCharacter (p.1*(n:ℝ)^2+p.2*Real.log (n:ℝ))

theorem continuous_logSum (S : Finset ℕ) : Continuous (logSum S) := by
  unfold logSum fordAdditiveCharacter
  fun_prop

theorem logSum_sixth_eq (S : Finset ℕ) (T : ℝ) :
    (∫ p : ℝ × ℝ in Icc (0:ℝ) 1 ×ˢ Icc (-T) T, ‖logSum S p‖^6) =
      logarithmicSixMoment T S (fun _ => 1) (fun n => (n:ℤ)) := by
  have hc : Continuous (fun p => ‖logSum S p‖^6) := (continuous_logSum S).norm.pow 6
  have hi := hc.continuousOn.integrableOn_compact (μ:=volume)
    (isCompact_Icc.prod isCompact_Icc : IsCompact (Icc (0:ℝ) 1 ×ˢ Icc (-T) T))
  rw [IntegrableOn,Measure.volume_eq_prod,←Measure.prod_restrict] at hi
  have hh := integral_prod_symm (fun p => ‖logSum S p‖^6) hi
  rw [Measure.prod_restrict,←Measure.volume_eq_prod] at hh
  simpa only [logSum,logarithmicSixMoment,one_mul,Int.cast_natCast] using hh

theorem three_mul_prod_le_sum_cube (a : Fin 3 → ℝ) (ha : ∀j, 0 ≤ a j) :
    3*(∏j, a j) ≤ ∑j, (a j)^3 := by
  have hp := mul_nonneg (add_nonneg (add_nonneg (ha 0) (ha 1)) (ha 2))
    (add_nonneg (add_nonneg (sq_nonneg (a 0-a 1)) (sq_nonneg (a 1-a 2)))
      (sq_nonneg (a 2-a 0)))
  simp only [Fin.sum_univ_succ,Fin.prod_univ_succ,
    Fin.sum_univ_zero,Fin.prod_univ_zero,add_zero,mul_one]
  change 3*(a 0*(a 1*a 2)) ≤ a 0^3+(a 1^3+a 2^3)
  nlinarith only [hp]

theorem normalized_triple_bound (a A : Fin 3 → ℝ) (hA : ∀j, 0 < A j) :
    (∏j, a j^2) ≤ (∏j, A j)/3*∑j, a j^6/(A j)^3 := by
  have hh := three_mul_prod_le_sum_cube (fun j => a j^2/A j)
    (fun j => div_nonneg (sq_nonneg _) (hA j).le)
  have hc (j : Fin 3) : (a j^2/A j)^3=a j^6/(A j)^3 := by ring
  simp only [hc,Finset.prod_div_distrib] at hh
  have hpos : 0 < ∏j, A j := Finset.prod_pos (fun j _ => hA j)
  have he : 3*((∏j, a j^2)/(∏j, A j))=(3*(∏j, a j^2))/(∏j, A j) := by ring
  rw [he] at hh
  have hmul := (div_le_iff₀ hpos).mp hh
  nlinarith only [hmul]

/-- Three independently truncated positive-frequency sums, with one constant
before all lengths and source sets. No mixed-moment estimate is assumed. -/
theorem exists_mixed_logarithmic_sixth {ε : ℝ} (hε : 0 < ε) :
    ∃ C > (0:ℝ), ∀ (N : ℕ), 1 ≤ N → ∀ (T : ℝ), 0 ≤ T →
      ∀ (M : Fin 3 → ℕ), (∀j, 1 ≤ M j ∧ M j ≤ N) →
      ∀ (S : Fin 3 → Finset ℕ), (∀j, ∀n∈S j, 1 ≤ n ∧ n ≤ M j) →
      (∫ p : ℝ × ℝ in Icc (0:ℝ) 1 ×ˢ Icc (-T) T,
        ∏j, ‖logSum (S j) p‖^2) ≤
        C*(T+N)*(∏j, (M j:ℝ))^((1:ℝ)+ε) := by
  classical
  obtain ⟨C,hC,h⟩ := exists_logarithmic_sixth (ε:=3*ε) (by positivity)
  refine ⟨C,hC,?_⟩
  intro N _hN T hT M hM S hS
  let R := Icc (0:ℝ) 1 ×ˢ Icc (-T) T
  let A := fun j => (M j:ℝ)^((1:ℝ)+ε)
  have hM₀ (j : Fin 3) : (0:ℝ) < M j := by exact_mod_cast (by have := (hM j).1; omega : 0 < M j)
  have hA (j : Fin 3) : 0 < A j := Real.rpow_pos_of_pos (hM₀ j) _
  have hAcube (j : Fin 3) : (A j)^3=(M j:ℝ)^((3:ℝ)+3*ε) := by
    dsimp only [A]
    rw [←Real.rpow_mul_natCast (hM₀ j).le]
    congr 1
    ring
  have hint (j : Fin 3) : IntegrableOn (fun p => ‖logSum (S j) p‖^6) R :=
    ((continuous_logSum (S j)).norm.pow 6).continuousOn.integrableOn_compact
      (isCompact_Icc.prod isCompact_Icc)
  have hsingle (j : Fin 3) :
      (∫ p in R, ‖logSum (S j) p‖^6/(A j)^3) ≤ C*(T+N) := by
    have hm (n : ℕ) (hn : n∈S j) : (1:ℤ) ≤ n ∧ (n:ℤ) ≤ M j := by
      exact_mod_cast hS j n hn
    have hz (k : ℤ) :
        (∑ _n∈(S j).filter (fun n : ℕ => (n:ℤ)=k), ‖(1:ℂ)‖) ≤ (1:ℝ) := by
      simp only [norm_one,Finset.sum_const,nsmul_eq_mul,mul_one]
      have hc : ((S j).filter (fun n : ℕ => (n:ℤ)=k)).card ≤ 1 := by
        apply Finset.card_le_one.mpr
        intro a ha b hb
        have he := (Finset.mem_filter.mp ha).2.trans (Finset.mem_filter.mp hb).2.symm
        exact_mod_cast he
      exact_mod_cast hc
    have hh := h (M j) (hM j).1 T hT ℕ (S j) (fun _ => 1) (fun n => (n:ℤ)) 1
      (by norm_num) hm hz
    simp only [one_pow,mul_one] at hh
    rw [integral_div,logSum_sixth_eq]
    apply (div_le_iff₀ (pow_pos (hA j) 3)).mpr
    rw [hAcube]
    apply hh.trans
    have hMN : (M j:ℝ) ≤ N := by exact_mod_cast (hM j).2
    gcongr
  have hpoint (p : ℝ × ℝ) :
      (∏j, ‖logSum (S j) p‖^2) ≤
        (∏j, A j)/3*∑j, ‖logSum (S j) p‖^6/(A j)^3 :=
    normalized_triple_bound _ A hA
  have hiSum : IntegrableOn
      (fun p => (∏j, A j)/3*∑j, ‖logSum (S j) p‖^6/(A j)^3) R :=
    (integrable_finsetSum _ (fun j _ => (hint j).div_const _)).const_mul _
  have hmain := integral_mono_of_nonneg
    (Filter.Eventually.of_forall (fun p => Finset.prod_nonneg
      (fun j (_hj : j∈Finset.univ) => sq_nonneg ‖logSum (S j) p‖))) hiSum
    (Filter.Eventually.of_forall hpoint)
  rw [integral_const_mul,integral_finsetSum _ (fun j _ => (hint j).div_const _)] at hmain
  have hsum := Finset.sum_le_sum (fun j (_hj : j∈Finset.univ) => hsingle j)
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at hsum
  have hprod : (∏j, A j)=(∏j, (M j:ℝ))^((1:ℝ)+ε) := by
    dsimp only [A]
    exact Real.finsetProd_rpow _ _ (fun j _ => (hM₀ j).le) _
  have hbound := hmain.trans (mul_le_mul_of_nonneg_left hsum
    (div_nonneg (Finset.prod_nonneg (fun j _ => (hA j).le)) (by norm_num)))
  rw [hprod] at hbound
  exact hbound.trans_eq (by ring)

def logBoxSquare (q : ℤ) (n : Fin 3 → ℕ) : ℝ := (q:ℝ)+∑j, (n j:ℝ)^2

def logBoxLog (n : Fin 3 → ℕ) : ℝ := ∑j, Real.log (n j:ℝ)

def logBoxSum (q : ℤ) (S : Fin 3 → Finset ℕ) (p : ℝ × ℝ) : ℂ :=
  sargosPlanarSum (Fintype.piFinset S) (fun _ => 1) (logBoxSquare q) logBoxLog p.1 p.2

theorem logBoxSum_eq_product (q : ℤ) (S : Fin 3 → Finset ℕ) (p : ℝ × ℝ) :
    logBoxSum q S p=fordAdditiveCharacter ((q:ℝ)*p.1)*∏j, logSum (S j) p := by
  classical
  unfold logBoxSum sargosPlanarSum logSum
  rw [Finset.prod_univ_sum,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n _hn
  rw [sargos_character_finset_prod,←fordAdditiveCharacter_add]
  simp only [one_mul,logBoxSquare,logBoxLog,Finset.sum_add_distrib,
    ←Finset.mul_sum]
  congr 1
  ring

theorem logBoxSum_norm_sq (q : ℤ) (S : Fin 3 → Finset ℕ) (p : ℝ × ℝ) :
    ‖logBoxSum q S p‖^2=∏j, ‖logSum (S j) p‖^2 := by
  rw [logBoxSum_eq_product,norm_mul,sargos_character_norm,one_mul,norm_prod,Finset.prod_pow]

theorem logSum_periodic (S : Finset ℕ) (t : ℝ) :
    Function.Periodic (fun α => logSum S (α,t)) 1 := by
  intro α
  unfold logSum
  apply Finset.sum_congr rfl
  intro n _hn
  have hk : fordAdditiveCharacter ((n^2:ℕ):ℝ)=1 := by
    unfold fordAdditiveCharacter
    have he : 2*Real.pi*Complex.I*((n^2:ℕ):ℂ)=((n^2:ℕ):ℂ)*(2*Real.pi*Complex.I) := by ring
    rw [Complex.ofReal_natCast,he,Complex.exp_nat_mul_two_pi_mul_I]
  have he : (α+1)*(n:ℝ)^2+t*Real.log (n:ℝ)=
      (α*(n:ℝ)^2+t*Real.log (n:ℝ))+((n^2:ℕ):ℝ) := by push_cast; ring
  rw [he,fordAdditiveCharacter_add,hk,mul_one]

theorem periodic_integral_two (f : ℝ → ℝ) (hf : Continuous f)
    (hp : Function.Periodic f 1) :
    (∫ α : ℝ in Icc (-1:ℝ) 1, f α)=2*∫ α : ℝ in Icc (0:ℝ) 1, f α := by
  rw [integral_Icc_eq_integral_Ioc,
    ←intervalIntegral.integral_of_le (by norm_num : (-1:ℝ) ≤ 1)]
  have hh := hp.intervalIntegral_add_zsmul_eq (2:ℤ) (-1)
    (fun a b => hf.intervalIntegrable a b)
  rw [hp.intervalIntegral_add_eq (-1) 0] at hh
  norm_num only [zsmul_eq_mul,Int.cast_ofNat,mul_one,zero_add,neg_add_cancel] at hh
  rw [hh,intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1),
    ←integral_Icc_eq_integral_Ioc]

theorem logBoxSum_central_integral (q : ℤ) (S : Fin 3 → Finset ℕ) (T : ℝ) :
    (∫ α : ℝ in Icc (-1:ℝ) 1, ∫ t : ℝ in Icc (-T) T,
      ‖logBoxSum q S (α,t)‖^2)=
      2*(∫ p : ℝ × ℝ in Icc (0:ℝ) 1 ×ˢ Icc (-T) T,
        ∏j, ‖logSum (S j) p‖^2) := by
  let F := fun p : ℝ × ℝ => ∏j, ‖logSum (S j) p‖^2
  have hc : Continuous F := by unfold F logSum fordAdditiveCharacter; fun_prop
  have hi (a b : ℝ) : Integrable F
      ((volume.restrict (Icc a b)).prod (volume.restrict (Icc (-T) T))) := by
    have hh := hc.continuousOn.integrableOn_compact (μ:=volume)
      (isCompact_Icc.prod isCompact_Icc : IsCompact (Icc a b ×ˢ Icc (-T) T))
    rwa [IntegrableOn,Measure.volume_eq_prod,←Measure.prod_restrict] at hh
  have hp (t : ℝ) : Function.Periodic (fun α => F (α,t)) 1 := by
    intro α
    apply Finset.prod_congr rfl
    intro j _hj
    have he := logSum_periodic (S j) t α
    change logSum (S j) (α+1,t)=logSum (S j) (α,t) at he
    rw [he]
  have hinner (t : ℝ) : (∫ α : ℝ in Icc (-1:ℝ) 1, F (α,t))=
      2*∫ α : ℝ in Icc (0:ℝ) 1, F (α,t) :=
    periodic_integral_two _ (hc.comp (continuous_id.prodMk continuous_const)) (hp t)
  simp_rw [logBoxSum_norm_sq]
  change (∫ α : ℝ in Icc (-1:ℝ) 1, ∫ t : ℝ in Icc (-T) T, F (α,t))=_
  rw [←integral_prod _ (hi (-1) 1),integral_prod_symm _ (hi (-1) 1)]
  simp_rw [hinner]
  rw [integral_const_mul,←integral_prod_symm _ (hi 0 1),Measure.prod_restrict,
    ←Measure.volume_eq_prod]

def logBoxFamily (S : Fin 2 → Fin 3 → Finset ℕ) : Finset ((_j : Fin 2) × (Fin 3 → ℕ)) :=
  Finset.univ.sigma (fun j => Fintype.piFinset (S j))

def logBoxFamilySquare (q : Fin 2 → ℤ) (v : (_j : Fin 2) × (Fin 3 → ℕ)) : ℝ :=
  logBoxSquare (q v.1) v.2

def logBoxFamilyLog (v : (_j : Fin 2) × (Fin 3 → ℕ)) : ℝ := logBoxLog v.2

theorem logBoxFamily_sum (q : Fin 2 → ℤ) (S : Fin 2 → Fin 3 → Finset ℕ) (p : ℝ × ℝ) :
    sargosPlanarSum (logBoxFamily S) (fun _ => 1) (logBoxFamilySquare q) logBoxFamilyLog p.1 p.2=
      ∑j, logBoxSum (q j) (S j) p := by
  simp only [logBoxFamily,logBoxFamilySquare,logBoxFamilyLog,logBoxSum,
    sargosPlanarSum,Finset.sum_sigma]

theorem logBoxFamily_norm_sq_le (q : Fin 2 → ℤ) (S : Fin 2 → Fin 3 → Finset ℕ) (p : ℝ × ℝ) :
    ‖sargosPlanarSum (logBoxFamily S) (fun _ => 1) (logBoxFamilySquare q) logBoxFamilyLog p.1 p.2‖^2 ≤
      2*∑j, ‖logBoxSum (q j) (S j) p‖^2 := by
  rw [logBoxFamily_sum]
  have hn := pow_le_pow_left₀ (norm_nonneg (∑j, logBoxSum (q j) (S j) p))
    (norm_sum_le Finset.univ (fun j => logBoxSum (q j) (S j) p)) 2
  have hh := pow_sum_le_card_mul_sum_pow (s:=Finset.univ)
    (f:=fun j => ‖logBoxSum (q j) (S j) p‖) (fun _ _ => norm_nonneg _) 1
  norm_num only [Finset.card_univ,Fintype.card_fin,Nat.cast_ofNat,pow_one,Nat.reduceAdd] at hh
  exact hn.trans hh

theorem continuous_logBoxSum (q : ℤ) (S : Fin 3 → Finset ℕ) :
    Continuous (logBoxSum q S) := by
  have he : logBoxSum q S = fun p => fordAdditiveCharacter ((q:ℝ)*p.1)*∏j, logSum (S j) p :=
    funext (logBoxSum_eq_product q S)
  rw [he]
  apply Continuous.mul
  · unfold fordAdditiveCharacter
    fun_prop
  · exact continuous_finsetProd _ (fun j _ => continuous_logSum (S j))

theorem logBoxFamily_central_le (q : Fin 2 → ℤ)
    (S : Fin 2 → Fin 3 → Finset ℕ) (T : ℝ) :
    (∫ α : ℝ in Icc (-1:ℝ) 1, ∫ t : ℝ in Icc (-T) T,
      ‖sargosPlanarSum (logBoxFamily S) (fun _ => 1)
        (logBoxFamilySquare q) logBoxFamilyLog α t‖^2) ≤
      2*∑j, (∫ α : ℝ in Icc (-1:ℝ) 1, ∫ t : ℝ in Icc (-T) T,
        ‖logBoxSum (q j) (S j) (α,t)‖^2) := by
  let R := Icc (-1:ℝ) 1 ×ˢ Icc (-T) T
  let F := fun p : ℝ × ℝ =>
    ‖sargosPlanarSum (logBoxFamily S) (fun _ => 1)
      (logBoxFamilySquare q) logBoxFamilyLog p.1 p.2‖^2
  let H := fun (j : Fin 2) (p : ℝ × ℝ) => ‖logBoxSum (q j) (S j) p‖^2
  have hFc : Continuous F := by
    have he : F=fun p => ‖∑j, logBoxSum (q j) (S j) p‖^2 := by
      funext p
      dsimp only [F]
      rw [logBoxFamily_sum]
    rw [he]
    exact (continuous_finsetSum _ (fun j _ => continuous_logBoxSum (q j) (S j))).norm.pow 2
  have hFi : IntegrableOn F R := hFc.continuousOn.integrableOn_compact
    (isCompact_Icc.prod isCompact_Icc)
  have hHi (j : Fin 2) : IntegrableOn (H j) R :=
    ((continuous_logBoxSum (q j) (S j)).norm.pow 2).continuousOn.integrableOn_compact
      (isCompact_Icc.prod isCompact_Icc)
  have hprodF := setIntegral_prod F (s:=Icc (-1:ℝ) 1) (t:=Icc (-T) T) (μ:=volume) (ν:=volume)
    (by simpa only [Measure.volume_eq_prod] using hFi)
  rw [←Measure.volume_eq_prod] at hprodF
  have hprodH (j : Fin 2) := setIntegral_prod (H j) (s:=Icc (-1:ℝ) 1) (t:=Icc (-T) T) (μ:=volume) (ν:=volume)
    (by simpa only [Measure.volume_eq_prod] using hHi j)
  simp only [←Measure.volume_eq_prod] at hprodH
  have himajor : IntegrableOn (fun p => 2*∑j, H j p) R :=
    (integrable_finsetSum _ (fun j _ => hHi j)).const_mul 2
  have hmain : (∫ p in R, F p) ≤ ∫ p in R, 2*∑j, H j p := integral_mono_of_nonneg
    (Filter.Eventually.of_forall (fun p => sq_nonneg
      ‖sargosPlanarSum (logBoxFamily S) (fun _ => 1)
        (logBoxFamilySquare q) logBoxFamilyLog p.1 p.2‖)) himajor
    (Filter.Eventually.of_forall (logBoxFamily_norm_sq_le q S))
  rw [integral_const_mul,integral_finsetSum _ (fun j _ => hHi j)] at hmain
  rw [hprodF] at hmain
  dsimp only [R] at hmain
  simp_rw [hprodH] at hmain
  exact hmain

theorem exists_two_box_central_moment {ε : ℝ} (hε : 0 < ε) :
    ∃ C > (0:ℝ), ∀ (N : ℕ), 1 ≤ N → ∀ (T : ℝ), 0 ≤ T →
      ∀ (M : Fin 2 → Fin 3 → ℕ), (∀j r, 1 ≤ M j r ∧ M j r ≤ N) →
      ∀ (S : Fin 2 → Fin 3 → Finset ℕ), (∀j r, ∀n∈S j r, 1 ≤ n ∧ n ≤ M j r) →
      ∀ (q : Fin 2 → ℤ),
      (∫ α : ℝ in Icc (-1:ℝ) 1, ∫ t : ℝ in Icc (-T) T,
        ‖sargosPlanarSum (logBoxFamily S) (fun _ => 1)
          (logBoxFamilySquare q) logBoxFamilyLog α t‖^2) ≤
        C*(T+N)*∑j, (∏r, (M j r:ℝ))^((1:ℝ)+ε) := by
  obtain ⟨C,hC,h⟩ := exists_mixed_logarithmic_sixth hε
  refine ⟨4*C,by positivity,?_⟩
  intro N hN T hT M hM S hS q
  have hbox (j : Fin 2) :
      (∫ α : ℝ in Icc (-1:ℝ) 1, ∫ t : ℝ in Icc (-T) T,
        ‖logBoxSum (q j) (S j) (α,t)‖^2) ≤
        2*C*(T+N)*(∏r, (M j r:ℝ))^((1:ℝ)+ε) := by
    rw [logBoxSum_central_integral]
    exact (mul_le_mul_of_nonneg_left (h N hN T hT (M j) (hM j) (S j) (hS j))
      (by norm_num : (0:ℝ) ≤ 2)).trans_eq (by ring)
  have hsum := Finset.sum_le_sum (fun j (_hj : j∈Finset.univ) => hbox j)
  rw [←Finset.mul_sum] at hsum
  exact ((logBoxFamily_central_le q S T).trans
    (mul_le_mul_of_nonneg_left hsum (by norm_num))).trans_eq (by ring)

/-- A literal two-box near-pair count. Integer square-frequency offsets
allow later zero-coordinate substitutions; no near-pair bound is assumed. -/
theorem exists_two_box_log_near_count {ε : ℝ} (hε : 0 < ε) :
    ∃ C > (0:ℝ), ∀ (N : ℕ), 1 ≤ N → ∀ (T : ℝ), 0 < T →
      ∀ (M : Fin 2 → Fin 3 → ℕ), (∀j r, 1 ≤ M j r ∧ M j r ≤ N) →
      ∀ (S : Fin 2 → Fin 3 → Finset ℕ), (∀j r, ∀n∈S j r, 1 ≤ n ∧ n ≤ M j r) →
      ∀ (q : Fin 2 → ℤ),
      ((sargosNearPairs (logBoxFamily S) (logBoxFamilySquare q) logBoxFamilyLog
        (1/2) (1/(2*T))).card : ℝ) ≤
        C*(1+N/T)*∑j, (∏r, (M j r:ℝ))^((1:ℝ)+ε) := by
  obtain ⟨C,hC,h⟩ := exists_two_box_central_moment hε
  refine ⟨16*C,by positivity,?_⟩
  intro N hN T hT M hM S hS q
  have hmom := h N hN T hT.le M hM S hS q
  have hk := sargosNearPairs_card_le_central (logBoxFamily S)
    (logBoxFamilySquare q) logBoxFamilyLog (Δ:=2) (μ:=2*T) (by norm_num) (by positivity)
  norm_num only [show (2:ℝ)/2=1 by norm_num,show 2*T/2=T by ring] at hk
  have hcoef : 64/((2:ℝ)*(2*T))=16/T := by field_simp; ring
  rw [hcoef] at hk
  apply hk.trans ((mul_le_mul_of_nonneg_left hmom (by positivity : 0 ≤ 16/T)).trans_eq ?_)
  field_simp

def logCrossPairs (S : Fin 2 → Fin 3 → Finset ℕ) (q : Fin 2 → ℤ)
    (δ : ℝ) : Finset ((Fin 3 → ℕ) × (Fin 3 → ℕ)) := by
  classical
  exact ((Fintype.piFinset (S 0)) ×ˢ (Fintype.piFinset (S 1))).filter
    (fun p => logBoxSquare (q 0) p.1=logBoxSquare (q 1) p.2 ∧
      |logBoxLog p.1-logBoxLog p.2| ≤ δ)

theorem logCrossPairs_card_le_near (S : Fin 2 → Fin 3 → Finset ℕ)
    (q : Fin 2 → ℤ) (δ : ℝ) :
    (logCrossPairs S q δ).card ≤
      (sargosNearPairs (logBoxFamily S) (logBoxFamilySquare q) logBoxFamilyLog (1/2) δ).card := by
  classical
  let f := fun p : (Fin 3 → ℕ) × (Fin 3 → ℕ) =>
    ((⟨(0:Fin 2),p.1⟩ : (_j : Fin 2) × (Fin 3 → ℕ)),
      (⟨(1:Fin 2),p.2⟩ : (_j : Fin 2) × (Fin 3 → ℕ)))
  apply Finset.card_le_card_of_injOn f
  · intro p hp
    obtain ⟨hp,he,hlog⟩ := Finset.mem_filter.mp hp
    obtain ⟨hleft,hright⟩ := Finset.mem_product.mp hp
    apply Finset.mem_filter.mpr
    constructor
    · apply Finset.mem_product.mpr
      constructor
      · exact Finset.mem_sigma.mpr ⟨Finset.mem_univ _,hleft⟩
      · exact Finset.mem_sigma.mpr ⟨Finset.mem_univ _,hright⟩
    · constructor
      · change |logBoxSquare (q 0) p.1-logBoxSquare (q 1) p.2| ≤ (1/2:ℝ)
        rw [he,sub_self,abs_zero]
        norm_num
      · exact hlog
  · intro p _hp r _hr he
    have ha := congrArg (fun v => v.1.2) he
    have hb := congrArg (fun v => v.2.2) he
    exact Prod.ext ha hb

theorem exists_logCrossPairs_bound {ε : ℝ} (hε : 0 < ε) :
    ∃ C > (0:ℝ), ∀ (N : ℕ), 1 ≤ N → ∀ (δ : ℝ), 0 < δ →
      ∀ (M : Fin 2 → Fin 3 → ℕ), (∀j r, 1 ≤ M j r ∧ M j r ≤ N) →
      ∀ (S : Fin 2 → Fin 3 → Finset ℕ), (∀j r, ∀n∈S j r, 1 ≤ n ∧ n ≤ M j r) →
      ∀ (q : Fin 2 → ℤ),
      ((logCrossPairs S q δ).card : ℝ) ≤
        C*(1+N*δ)*∑j, (∏r, (M j r:ℝ))^((1:ℝ)+ε) := by
  obtain ⟨C,hC,h⟩ := exists_two_box_log_near_count hε
  refine ⟨2*C,by positivity,?_⟩
  intro N hN δ hδ M hM S hS q
  have hh := h N hN (1/(2*δ)) (by positivity) M hM S hS q
  have htol : 1/(2*(1/(2*δ)))=δ := by field_simp
  rw [htol] at hh
  have hcard : ((logCrossPairs S q δ).card : ℝ) ≤
      (sargosNearPairs (logBoxFamily S) (logBoxFamilySquare q) logBoxFamilyLog (1/2) δ).card := by
    exact_mod_cast logCrossPairs_card_le_near S q δ
  apply (hcard.trans hh).trans
  have hsum : 0 ≤ ∑j, (∏r, (M j r:ℝ))^((1:ℝ)+ε) :=
    Finset.sum_nonneg (fun j _ => Real.rpow_nonneg (Finset.prod_nonneg (fun r _ => Nat.cast_nonneg _)) _)
  have he : 1+(N:ℝ)/(1/(2*δ))=1+2*N*δ := by field_simp
  rw [he]
  apply mul_le_mul_of_nonneg_right _ hsum
  nlinarith only [hC]

theorem logBoxLog_eq_log_product (n : Fin 3 → ℕ) (hn : ∀j, 1 ≤ n j) :
    logBoxLog n=Real.log (∏j, (n j:ℝ)) := by
  exact (Real.log_prod (fun j _ => (show (0:ℝ) < n j by exact_mod_cast (hn j)).ne')).symm

theorem abs_log_sub_le_gap {a b L P : ℝ} (hL : 0 < L)
    (ha : L ≤ a) (hb : L ≤ b) (hd : |a-b| ≤ P) :
    |Real.log a-Real.log b| ≤ P/L := by
  have ha₀ := hL.trans_le ha
  have hb₀ := hL.trans_le hb
  have hP : 0 ≤ P := (abs_nonneg _).trans hd
  have hside {x y : ℝ} (hx : 0 < x) (hy : L ≤ y) (hdiff : |x-y| ≤ P) :
      Real.log x-Real.log y ≤ P/L := by
    have hy₀ := hL.trans_le hy
    calc
      _ = Real.log (x/y) := (Real.log_div hx.ne' hy₀.ne').symm
      _ ≤ x/y-1 := Real.log_le_sub_one_of_pos (div_pos hx hy₀)
      _ = (x-y)/y := by field_simp
      _ ≤ |x-y|/y := div_le_div_of_nonneg_right (le_abs_self _) hy₀.le
      _ ≤ P/L := by gcongr
  have hab := hside ha₀ hb hd
  have hba := hside hb₀ ha (by simpa only [abs_sub_comm] using hd)
  exact abs_le.mpr ⟨by linarith,hab⟩

theorem logBoxLog_difference_le {a b : Fin 3 → ℕ} (ha : ∀j, 1 ≤ a j)
    (hb : ∀j, 1 ≤ b j) {L P : ℝ} (hL : 0 < L)
    (hpa : L ≤ ∏j, (a j:ℝ)) (hpb : L ≤ ∏j, (b j:ℝ))
    (hd : |(∏j, (a j:ℝ))-(∏j, (b j:ℝ))| ≤ P) :
    |logBoxLog a-logBoxLog b| ≤ P/L := by
  rw [logBoxLog_eq_log_product a ha,logBoxLog_eq_log_product b hb]
  exact abs_log_sub_le_gap hL hpa hpb hd

theorem logBoxLog_mem {N : ℕ} {n : Fin 3 → ℕ}
    (hn : ∀j, 1 ≤ n j ∧ n j ≤ N) : logBoxLog n∈Icc 0 (3*Real.log N) := by
  have hlow (j : Fin 3) : 0 ≤ Real.log (n j:ℝ) :=
    Real.log_nonneg (by exact_mod_cast (hn j).1)
  have hhigh (j : Fin 3) : Real.log (n j:ℝ) ≤ Real.log N :=
    Real.log_le_log (by exact_mod_cast (hn j).1) (by exact_mod_cast (hn j).2)
  constructor
  · exact Finset.sum_nonneg (fun j _ => hlow j)
  · have hh := Finset.sum_le_sum (fun j (_hj : j∈Finset.univ) => hhigh j)
    simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_ofNat] using hh

theorem logBoxLog_difference_le_global {N : ℕ} {a b : Fin 3 → ℕ}
    (ha : ∀j, 1 ≤ a j ∧ a j ≤ N) (hb : ∀j, 1 ≤ b j ∧ b j ≤ N) :
    |logBoxLog a-logBoxLog b| ≤ 3*Real.log N := by
  have hA := logBoxLog_mem ha
  have hB := logBoxLog_mem hb
  exact abs_le.mpr ⟨by linarith [hA.1,hB.2],by linarith [hA.2,hB.1]⟩

def boxProduct (n : Fin 3 → ℕ) : ℝ := ∏j, (n j:ℝ)

theorem boxProduct_pos {n : Fin 3 → ℕ} (hn : ∀j, 1 ≤ n j) : 0 < boxProduct n :=
  Finset.prod_pos (fun j _ => by exact_mod_cast hn j)

theorem boxProduct_le_cube {N : ℕ} {n : Fin 3 → ℕ} (hn : ∀j, n j ≤ N) :
    boxProduct n ≤ (N:ℝ)^3 := by
  have hh := Finset.prod_le_prod (s:=Finset.univ)
    (f:=fun j => (n j:ℝ)) (g:=fun _ => (N:ℝ))
    (fun j _ => Nat.cast_nonneg _) (fun j _ => by change (n j:ℝ) ≤ N; exact_mod_cast hn j)
  simpa only [Finset.prod_const,Finset.card_univ,Fintype.card_fin] using hh

theorem boxProduct_le_square_of_one {N : ℕ} {n : Fin 3 → ℕ}
    (hn : ∀j, n j ≤ N) (hone : ∃j, n j=1) : boxProduct n ≤ (N:ℝ)^2 := by
  obtain ⟨j,hj⟩ := hone
  have hn₀ : (n 0:ℝ) ≤ N := by exact_mod_cast hn 0
  have hn₁ : (n 1:ℝ) ≤ N := by exact_mod_cast hn 1
  have hn₂ : (n 2:ℝ) ≤ N := by exact_mod_cast hn 2
  have hbound {a b : ℝ} (ha₀ : 0 ≤ a) (hb₀ : 0 ≤ b) (ha : a ≤ N) (hb : b ≤ N) :
      a*b ≤ (N:ℝ)^2 := by nlinarith [mul_le_mul ha hb hb₀ (Nat.cast_nonneg N)]
  fin_cases j
  · change n 0=1 at hj
    simp only [boxProduct,Fin.prod_univ_succ,Fin.prod_univ_zero,mul_one]
    change (n 0:ℝ)*((n 1:ℝ)*(n 2:ℝ)) ≤ _
    rw [hj,Nat.cast_one,one_mul]
    exact hbound (Nat.cast_nonneg _) (Nat.cast_nonneg _) hn₁ hn₂
  · change n 1=1 at hj
    simp only [boxProduct,Fin.prod_univ_succ,Fin.prod_univ_zero,mul_one]
    change (n 0:ℝ)*((n 1:ℝ)*(n 2:ℝ)) ≤ _
    rw [hj,Nat.cast_one,one_mul]
    exact hbound (Nat.cast_nonneg _) (Nat.cast_nonneg _) hn₀ hn₂
  · change n 2=1 at hj
    simp only [boxProduct,Fin.prod_univ_succ,Fin.prod_univ_zero,mul_one]
    change (n 0:ℝ)*((n 1:ℝ)*(n 2:ℝ)) ≤ _
    rw [hj,Nat.cast_one,mul_one]
    exact hbound (Nat.cast_nonneg _) (Nat.cast_nonneg _) hn₀ hn₁

theorem boxProduct_comparison {M n : Fin 3 → ℕ}
    (hlow : ∀j, (M j:ℝ) ≤ 2*(n j:ℝ)) (hhigh : ∀j, n j ≤ M j) :
    boxProduct M ≤ 8*boxProduct n ∧ boxProduct n ≤ boxProduct M := by
  constructor
  · have hh := Finset.prod_le_prod (s:=Finset.univ)
      (f:=fun j => (M j:ℝ)) (g:=fun j => 2*(n j:ℝ))
      (fun j _ => Nat.cast_nonneg _) (fun j _ => hlow j)
    rw [Finset.prod_mul_distrib] at hh
    norm_num only [Finset.prod_const,Finset.card_univ,Fintype.card_fin,show (2:ℝ)^3=8 by norm_num] at hh
    exact hh
  · exact Finset.prod_le_prod (fun j _ => Nat.cast_nonneg _) (fun j _ => by exact_mod_cast hhigh j)

def zeroAdjustedProduct (z : Bool) (n : Fin 3 → ℕ) : ℝ := if z then 0 else boxProduct n

def zeroAdjustedPairs (S : Fin 2 → Fin 3 → Finset ℕ) (q : Fin 2 → ℤ)
    (z : Fin 2 → Bool) (P : ℝ) : Finset ((Fin 3 → ℕ) × (Fin 3 → ℕ)) := by
  classical
  exact ((Fintype.piFinset (S 0)) ×ˢ (Fintype.piFinset (S 1))).filter
    (fun p => logBoxSquare (q 0) p.1=logBoxSquare (q 1) p.2 ∧
      |zeroAdjustedProduct (z 0) p.1-zeroAdjustedProduct (z 1) p.2| ≤ P)

theorem zeroAdjustedPairs_subset_global (S : Fin 2 → Fin 3 → Finset ℕ)
    (q : Fin 2 → ℤ) (z : Fin 2 → Bool) (P : ℝ) {N : ℕ}
    (hS : ∀j r, ∀n∈S j r, 1 ≤ n ∧ n ≤ N) :
    zeroAdjustedPairs S q z P ⊆ logCrossPairs S q (1+3*Real.log N) := by
  intro p hp
  obtain ⟨hp,hsq,_hprod⟩ := Finset.mem_filter.mp hp
  have hmem := Finset.mem_product.mp hp
  have ha (r : Fin 3) := hS 0 r (p.1 r) (Fintype.mem_piFinset.mp hmem.1 r)
  have hb (r : Fin 3) := hS 1 r (p.2 r) (Fintype.mem_piFinset.mp hmem.2 r)
  exact Finset.mem_filter.mpr ⟨hp,hsq,(logBoxLog_difference_le_global ha hb).trans (by linarith)⟩

theorem positive_products_high_log {M : Fin 2 → Fin 3 → ℕ} {a b : Fin 3 → ℕ}
    (ha : ∀r, 1 ≤ a r) (hb : ∀r, 1 ≤ b r)
    (hMa : boxProduct (M 0) ≤ 8*boxProduct a) (hMb : boxProduct (M 1) ≤ 8*boxProduct b)
    {U P : ℝ} (hU : U=max (boxProduct (M 0)) (boxProduct (M 1)))
    (hP : 0 ≤ P) (hlarge : 16*(P+1) < U) (hd : |boxProduct a-boxProduct b| ≤ P) :
    |logBoxLog a-logBoxLog b| ≤ 16*(P+1)/U := by
  have hU₀ : 0 < U := by linarith
  have hab := abs_le.mp hd
  have hmin : U/16 ≤ boxProduct a ∧ U/16 ≤ boxProduct b := by
    rcases le_total (boxProduct (M 0)) (boxProduct (M 1)) with h | h
    · rw [max_eq_right h] at hU
      constructor <;> linarith
    · rw [max_eq_left h] at hU
      constructor <;> linarith
  have hh := logBoxLog_difference_le ha hb (show 0 < U/16 by positivity) hmin.1 hmin.2 hd
  have he : P/(U/16)=16*P/U := by ring
  rw [he] at hh
  apply hh.trans
  apply div_le_div_of_nonneg_right _ hU₀.le
  linarith

theorem zero_product_upper {z₀ z₁ : Bool} {U₀ U₁ A B V P : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hV : 0 ≤ V) (hP : 0 ≤ P)
    (hU₀ : U₀ ≤ 8*A) (hU₁ : U₁ ≤ 8*B)
    (hz₀ : z₀=true → U₀ ≤ V) (hz₁ : z₁=true → U₁ ≤ V)
    (hz : z₀=true ∨ z₁=true)
    (hd : |(if z₀ then 0 else A)-(if z₁ then 0 else B)| ≤ P) :
    max U₀ U₁ ≤ V+8*P := by
  cases z₀ <;> cases z₁
  · simp at hz
  · have hu := hz₁ rfl
    have ha : A ≤ P := by simpa only [Bool.false_eq_true,if_false,if_true,sub_zero,abs_of_nonneg hA] using hd
    exact max_le (by linarith) (by linarith)
  · have hu := hz₀ rfl
    have hb : B ≤ P := by simpa only [Bool.false_eq_true,if_false,if_true,zero_sub,abs_neg,abs_of_nonneg hB] using hd
    exact max_le (by linarith) (by linarith)
  · have hu := hz₀ rfl
    have hv := hz₁ rfl
    exact max_le (by linarith) (by linarith)

theorem zeroAdjustedPairs_subset_high
    (S : Fin 2 → Fin 3 → Finset ℕ) (q : Fin 2 → ℤ) (z : Fin 2 → Bool)
    {M : Fin 2 → Fin 3 → ℕ} {N : ℕ} {P U : ℝ} (hP : 0 ≤ P)
    (hM : ∀j r, M j r ≤ N)
    (hzero : ∀j, z j=true → ∃r, M j r=1)
    (hS : ∀j r, ∀n∈S j r, 1 ≤ n ∧ n ≤ M j r ∧ (M j r:ℝ) ≤ 2*n)
    (hU : U=max (boxProduct (M 0)) (boxProduct (M 1)))
    (hlarge : 16*((N:ℝ)^2+P+1) < U) :
    zeroAdjustedPairs S q z P ⊆ logCrossPairs S q (16*(P+1)/U) := by
  intro p hp
  obtain ⟨hp,hsq,hprod⟩ := Finset.mem_filter.mp hp
  have hmem := Finset.mem_product.mp hp
  have ha (r : Fin 3) := hS 0 r (p.1 r) (Fintype.mem_piFinset.mp hmem.1 r)
  have hb (r : Fin 3) := hS 1 r (p.2 r) (Fintype.mem_piFinset.mp hmem.2 r)
  have hMa := (boxProduct_comparison (fun r => (ha r).2.2) (fun r => (ha r).2.1)).1
  have hMb := (boxProduct_comparison (fun r => (hb r).2.2) (fun r => (hb r).2.1)).1
  have hfalse : z 0=false ∧ z 1=false := by
    have hnot : ¬(z 0=true ∨ z 1=true) := by
      intro hz
      have hu := zero_product_upper (boxProduct_pos (fun r => (ha r).1)).le
        (boxProduct_pos (fun r => (hb r).1)).le (sq_nonneg (N:ℝ)) hP hMa hMb
        (fun h => boxProduct_le_square_of_one (hM 0) (hzero 0 h))
        (fun h => boxProduct_le_square_of_one (hM 1) (hzero 1 h)) hz hprod
      rw [←hU] at hu
      nlinarith [sq_nonneg (N:ℝ)]
    constructor <;> apply Bool.eq_false_iff.mpr
    · exact fun h => hnot (Or.inl h)
    · exact fun h => hnot (Or.inr h)
  have hd : |boxProduct p.1-boxProduct p.2| ≤ P := by
    simpa only [zeroAdjustedProduct,hfalse.1,hfalse.2,Bool.false_eq_true,if_false] using hprod
  have hh := positive_products_high_log (fun r => (ha r).1) (fun r => (hb r).1)
    hMa hMb hU hP (by nlinarith [sq_nonneg (N:ℝ)]) hd
  exact Finset.mem_filter.mpr ⟨hp,hsq,hh⟩

theorem boxProduct_rpow_budget {N : ℕ} {M : Fin 2 → Fin 3 → ℕ}
    (hM : ∀j r, 1 ≤ M j r ∧ M j r ≤ N) {η : ℝ} (hη : 0 ≤ η)
    {U : ℝ} (hU : U=max (boxProduct (M 0)) (boxProduct (M 1))) :
    (∑j, (boxProduct (M j))^((1:ℝ)+η)) ≤ 2*U*(N:ℝ)^(3*η) := by
  have hupper (j : Fin 2) : boxProduct (M j) ≤ U := by
    rw [hU]
    fin_cases j
    · exact le_max_left _ _
    · exact le_max_right _ _
  have hterm (j : Fin 2) : (boxProduct (M j))^((1:ℝ)+η) ≤ U*(N:ℝ)^(3*η) := by
    have hp := boxProduct_pos (fun r => (hM j r).1)
    have hc := boxProduct_le_cube (fun r => (hM j r).2)
    have hpow := Real.rpow_le_rpow hp.le hc hη
    rw [←Real.rpow_natCast_mul (Nat.cast_nonneg N) 3 η] at hpow
    norm_num only [Nat.cast_ofNat] at hpow
    rw [Real.rpow_add hp,Real.rpow_one]
    exact mul_le_mul (hupper j) hpow (Real.rpow_nonneg hp.le _) (hp.le.trans (hupper j))
  have hh := Finset.sum_le_sum (fun j (_hj : j∈Finset.univ) => hterm j)
  norm_num only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_ofNat] at hh
  exact hh.trans_eq (by ring)

/-- Uniform square/product box bound with zero-product sectors retained.
Only coordinate geometry and literal zero-coordinate data are hypotheses;
the analytic cardinality estimate is derived. -/
theorem exists_zeroAdjustedPairs_box_bound {ε : ℝ} (hε : 0 < ε) :
    ∃ C > (0:ℝ), ∀ (N : ℕ), 1 ≤ N → ∀ (P : ℝ), 0 ≤ P →
      ∀ (M : Fin 2 → Fin 3 → ℕ), (∀j r, 1 ≤ M j r ∧ M j r ≤ N) →
      ∀ (S : Fin 2 → Fin 3 → Finset ℕ),
        (∀j r, ∀n∈S j r, 1 ≤ n ∧ n ≤ M j r ∧ (M j r:ℝ) ≤ 2*n) →
      ∀ (q : Fin 2 → ℤ) (z : Fin 2 → Bool),
        (∀j, z j=true → ∃r, M j r=1) →
      ((zeroAdjustedPairs S q z P).card : ℝ) ≤
        C*((N:ℝ)^2+P+1)*(N:ℝ)^((1:ℝ)+ε)*(1+Real.log N) := by
  obtain ⟨C,hC,h⟩ := exists_logCrossPairs_bound (ε:=ε/3) (by positivity)
  refine ⟨96*C,by positivity,?_⟩
  intro N hN P hP M hM S hS q z hzero
  let U := max (boxProduct (M 0)) (boxProduct (M 1))
  let D := (N:ℝ)^2+P+1
  let K := (N:ℝ)^ε
  let L := 1+Real.log N
  have hN₁ : (1:ℝ) ≤ N := by exact_mod_cast hN
  have hN₀ : (0:ℝ) < N := by linarith
  have hlog : 0 ≤ Real.log N := Real.log_nonneg hN₁
  have hL : 1 ≤ L := by dsimp [L]; linarith
  have hD : 0 < D := by dsimp [D]; positivity
  have hK : 0 ≤ K := Real.rpow_nonneg hN₀.le _
  have hU : 0 < U := (boxProduct_pos (fun r => (hM 0 r).1)).trans_le (le_max_left _ _)
  have hUcube : U ≤ (N:ℝ)^3 := max_le
    (boxProduct_le_cube (fun r => (hM 0 r).2)) (boxProduct_le_cube (fun r => (hM 1 r).2))
  have hSbasic (j : Fin 2) (r : Fin 3) (n : ℕ) (hn : n∈S j r) : 1 ≤ n ∧ n ≤ M j r :=
    ⟨(hS j r n hn).1,(hS j r n hn).2.1⟩
  have hsum : (∑j, (∏r, (M j r:ℝ))^((1:ℝ)+ε/3)) ≤ 2*U*K := by
    have hh := boxProduct_rpow_budget hM (show 0 ≤ ε/3 by positivity) (U:=U) rfl
    norm_num only [show (3:ℝ)*(ε/3)=ε by ring] at hh
    exact hh
  have hcommon : ((zeroAdjustedPairs S q z P).card : ℝ) ≤ 96*C*D*N*K*L := by
    by_cases hsmall : U ≤ 16*D
    · let δ := 1+3*Real.log N
      have hδ : 0 < δ := by dsimp [δ]; linarith
      have hsubset := zeroAdjustedPairs_subset_global S q z P
        (fun j r n hn => ⟨(hSbasic j r n hn).1,(hSbasic j r n hn).2.trans (hM j r).2⟩)
      have hc : ((zeroAdjustedPairs S q z P).card : ℝ) ≤ (logCrossPairs S q δ).card := by
        exact_mod_cast Finset.card_le_card hsubset
      have hh := h N hN δ hδ M hM S hSbasic q
      have hb := (hc.trans hh).trans
        (mul_le_mul_of_nonneg_left hsum (by positivity : 0 ≤ C*(1+N*δ)))
      have hlength : 1+(N:ℝ)*δ ≤ 3*N*L := by dsimp [δ,L]; nlinarith
      have hnum : (1+(N:ℝ)*δ)*(2*U) ≤ (3*N*L)*(32*D) :=
        mul_le_mul hlength (by linarith) (by positivity) (by positivity)
      have hbudget := mul_le_mul_of_nonneg_left hnum (mul_nonneg hC.le hK)
      exact hb.trans (by nlinarith only [hbudget])
    · let δ := 16*(P+1)/U
      have hδ : 0 < δ := by dsimp [δ]; positivity
      have hsubset := zeroAdjustedPairs_subset_high S q z hP (fun j r => (hM j r).2)
        hzero hS (U:=U) rfl (lt_of_not_ge hsmall)
      have hc : ((zeroAdjustedPairs S q z P).card : ℝ) ≤ (logCrossPairs S q δ).card := by
        exact_mod_cast Finset.card_le_card hsubset
      have hh := h N hN δ hδ M hM S hSbasic q
      have hb := (hc.trans hh).trans
        (mul_le_mul_of_nonneg_left hsum (by positivity : 0 ≤ C*(1+N*δ)))
      have he : C*(1+(N:ℝ)*δ)*(2*U*K)=2*C*(U+16*N*(P+1))*K := by
        dsimp [δ]
        field_simp
      rw [he] at hb
      have hpoly : U+16*(N:ℝ)*(P+1) ≤ 16*D*N := by
        dsimp [D]
        nlinarith [pow_nonneg hN₀.le 3]
      have hb' := hb.trans (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hpoly (by positivity : 0 ≤ 2*C)) hK)
      have hbudget : (2*C*(16*D*N))*K ≤ 96*C*D*N*K*L := by
        have hh := mul_le_mul_of_nonneg_left hL (show 0 ≤ 96*C*D*N*K by positivity)
        nlinarith only [hh,mul_nonneg (show 0 ≤ C*D*N by positivity) hK]
      exact hb'.trans hbudget
  have he : (N:ℝ)^((1:ℝ)+ε)=(N:ℝ)*K := by rw [Real.rpow_add hN₀,Real.rpow_one]
  rw [he]
  exact hcommon.trans_eq (by dsimp [D,L]; ring)

def positiveCode (a : ℤ) : ℕ := if a=0 then 1 else a.natAbs

theorem positiveCode_pos (a : ℤ) : 1 ≤ positiveCode a := by
  by_cases h : a=0
  · simp [positiveCode,h]
  · have ha : 0 < a.natAbs := Int.natAbs_pos.mpr h
    simp only [positiveCode,h,if_false]
    omega

theorem positiveCode_le {N : ℕ} (hN : 1 ≤ N) {a : ℤ} (ha : |a| ≤ N) :
    positiveCode a ≤ N := by
  by_cases h : a=0
  · simpa only [positiveCode,h,if_true] using hN
  · simp only [positiveCode,h,if_false]
    exact_mod_cast (show (a.natAbs:ℤ) ≤ N by rwa [Int.natCast_natAbs])

theorem positiveCode_reconstruct (a : ℤ) :
    a = if a=0 then 0 else if a<0 then -(positiveCode a:ℤ) else (positiveCode a:ℤ) := by
  by_cases h : a=0
  · simp [h]
  · by_cases hs : a<0
    · simp [positiveCode,h,hs,abs_of_neg hs]
    · simp [positiveCode,h,hs,abs_of_nonneg (le_of_not_gt hs)]

theorem positiveCode_square (a : ℤ) :
    (a:ℝ)^2=(positiveCode a:ℝ)^2-(if a=0 then 1 else 0) := by
  by_cases h : a=0
  · simp [positiveCode,h]
  · simp only [positiveCode,h,if_false,sub_zero]
    have he : (a.natAbs:ℝ)=|(a:ℝ)| := by rw [Nat.cast_natAbs,Int.cast_abs]
    rw [he,sq_abs]

abbrev SignedBoxLabel (N : ℕ) := Bool × Bool × Fin (Nat.log 2 N+1)

def signedBoxLabel (N : ℕ) (a : ℤ) : SignedBoxLabel N :=
  (decide (a=0),decide (a<0),⟨min (Nat.log 2 (positiveCode a)) (Nat.log 2 N),
    (min_le_right _ _).trans_lt (Nat.lt_succ_self _)⟩)

def signedBoxLength (N : ℕ) (l : SignedBoxLabel N) : ℕ :=
  if l.1 then 1 else min N (2^((l.2.2:ℕ)+1))

def signedBoxSet (N : ℕ) (l : SignedBoxLabel N) : Finset ℕ := by
  classical
  exact (Finset.Icc 1 (signedBoxLength N l)).filter (fun n => signedBoxLength N l ≤ 2*n)

theorem signedBoxLength_bounds {N : ℕ} (hN : 1 ≤ N) (l : SignedBoxLabel N) :
    1 ≤ signedBoxLength N l ∧ signedBoxLength N l ≤ N := by
  unfold signedBoxLength
  split_ifs
  · exact ⟨le_rfl,hN⟩
  · have hp : 0 < (2:ℕ)^((l.2.2:ℕ)+1) := pow_pos (by norm_num) _
    exact ⟨le_min hN (by omega),min_le_left _ _⟩

theorem signedBoxSet_range {N : ℕ} {l : SignedBoxLabel N} {n : ℕ}
    (hn : n∈signedBoxSet N l) :
    1 ≤ n ∧ n ≤ signedBoxLength N l ∧ (signedBoxLength N l:ℝ) ≤ 2*n := by
  obtain ⟨hn,hh⟩ := Finset.mem_filter.mp hn
  obtain ⟨hlo,hhi⟩ := Finset.mem_Icc.mp hn
  exact ⟨hlo,hhi,by exact_mod_cast hh⟩

theorem positiveCode_mem_signedBox {N : ℕ} (hN : 1 ≤ N) {a : ℤ} (ha : |a| ≤ N) :
    positiveCode a ∈ signedBoxSet N (signedBoxLabel N a) := by
  have hc := positiveCode_pos a
  have hcN := positiveCode_le hN ha
  apply Finset.mem_filter.mpr
  constructor
  · apply Finset.mem_Icc.mpr
    refine ⟨hc,?_⟩
    by_cases hz : a=0
    · simp [signedBoxLength,signedBoxLabel,positiveCode,hz]
    · have hh := Nat.lt_pow_succ_log_self (by norm_num : 1 < (2:ℕ)) (positiveCode a)
      simp only [signedBoxLength,signedBoxLabel,hz,decide_false]
      rw [min_eq_left (Nat.log_mono_right hcN)]
      exact le_min hcN hh.le
  · by_cases hz : a=0
    · simp [signedBoxLength,signedBoxLabel,positiveCode,hz]
    · have hh := Nat.pow_log_le_self 2 (by omega : positiveCode a ≠ 0)
      have hm : signedBoxLength N (signedBoxLabel N a) ≤ 2^(Nat.log 2 (positiveCode a)+1) := by
        unfold signedBoxLength
        simp only [signedBoxLabel,hz,decide_false]
        rw [min_eq_left (Nat.log_mono_right hcN)]
        exact min_le_right _ _
      rw [pow_succ] at hm
      omega

theorem positiveCode_inj_of_label {N : ℕ} {a b : ℤ}
    (hl : signedBoxLabel N a=signedBoxLabel N b) (hc : positiveCode a=positiveCode b) : a=b := by
  have hz : (a=0) ↔ (b=0) := by
    have hh := congrArg (fun l : SignedBoxLabel N => l.1) hl
    simpa only [signedBoxLabel,decide_eq_decide] using hh
  have hs : (a<0) ↔ (b<0) := by
    have hh := congrArg (fun l : SignedBoxLabel N => l.2.1) hl
    simpa only [signedBoxLabel,decide_eq_decide] using hh
  calc
    a = if a=0 then 0 else if a<0 then -(positiveCode a:ℤ) else (positiveCode a:ℤ) := positiveCode_reconstruct a
    _ = if b=0 then 0 else if b<0 then -(positiveCode b:ℤ) else (positiveCode b:ℤ) := by simp only [hz,hs,hc]
    _ = b := (positiveCode_reconstruct b).symm

def signedBoxShift {N : ℕ} (l : Fin 3 → SignedBoxLabel N) : ℤ :=
  -(∑r, if (l r).1 then 1 else 0)

def signedBoxZero {N : ℕ} (l : Fin 3 → SignedBoxLabel N) : Bool :=
  decide (∃r, (l r).1=true)

def positiveTriple (a : Fin 3 → ℤ) : Fin 3 → ℕ := fun r => positiveCode (a r)

theorem signedBoxShift_square {N : ℕ} {a : Fin 3 → ℤ} {l : Fin 3 → SignedBoxLabel N}
    (hl : ∀r, signedBoxLabel N (a r)=l r) :
    logBoxSquare (signedBoxShift l) (positiveTriple a)=∑r, (a r:ℝ)^2 := by
  have hz (r : Fin 3) : (l r).1=decide (a r=0) :=
    (congrArg (fun v : SignedBoxLabel N => v.1) (hl r)).symm
  have hshift : (signedBoxShift l:ℝ)=-(∑r, if a r=0 then (1:ℝ) else 0) := by
    simp [signedBoxShift,hz]
  have hs : (∑r, (a r:ℝ)^2)=(∑r, (positiveCode (a r):ℝ)^2)-
      ∑r, if a r=0 then (1:ℝ) else 0 := by
    simp_rw [positiveCode_square]
    rw [Finset.sum_sub_distrib]
  rw [hs]
  unfold logBoxSquare positiveTriple
  rw [hshift]
  ring

theorem signedBoxZero_product {N : ℕ} {a : Fin 3 → ℤ} {l : Fin 3 → SignedBoxLabel N}
    (hl : ∀r, signedBoxLabel N (a r)=l r) :
    zeroAdjustedProduct (signedBoxZero l) (positiveTriple a)=|∏r, (a r:ℝ)| := by
  have hz (r : Fin 3) : (l r).1=decide (a r=0) :=
    (congrArg (fun v : SignedBoxLabel N => v.1) (hl r)).symm
  by_cases h : ∃r, a r=0
  · have hflag : signedBoxZero l=true := by simp [signedBoxZero,hz,h]
    obtain ⟨r,hr⟩ := h
    have hp : (∏r, (a r:ℝ))=0 := Finset.prod_eq_zero (Finset.mem_univ r) (by rw [hr]; norm_num)
    simp only [zeroAdjustedProduct,hflag,if_true,hp,abs_zero]
  · have hn (r : Fin 3) : a r ≠ 0 := fun he => h ⟨r,he⟩
    have hflag : signedBoxZero l=false := by simp [signedBoxZero,hz,h]
    simp only [zeroAdjustedProduct,hflag,Bool.false_eq_true,if_false,boxProduct,positiveTriple]
    rw [Finset.abs_prod]
    apply Finset.prod_congr rfl
    intro r _hr
    simp only [positiveCode,hn r,if_false,Nat.cast_natAbs,Int.cast_abs]

theorem signedBoxZero_has_unit {N : ℕ} {l : Fin 3 → SignedBoxLabel N}
    (hz : signedBoxZero l=true) : ∃r, signedBoxLength N (l r)=1 := by
  obtain ⟨r,hr⟩ := of_decide_eq_true hz
  exact ⟨r,by simp only [signedBoxLength,hr,if_true]⟩

abbrev SignedPair := (Fin 3 → ℤ) × (Fin 3 → ℤ)
abbrev SignedPairLabel (N : ℕ) := (Fin 3 → SignedBoxLabel N) × (Fin 3 → SignedBoxLabel N)

def signedPairLabel (N : ℕ) (p : SignedPair) : SignedPairLabel N :=
  (fun r => signedBoxLabel N (p.1 r),fun r => signedBoxLabel N (p.2 r))

def positivePair (p : SignedPair) : (Fin 3 → ℕ) × (Fin 3 → ℕ) :=
  (positiveTriple p.1,positiveTriple p.2)

def signedLabelRow {N : ℕ} (l : SignedPairLabel N) : Fin 2 → Fin 3 → SignedBoxLabel N := ![l.1,l.2]

theorem positivePair_mem_box {N : ℕ} (hN : 1 ≤ N) {P : ℝ}
    {p : SignedPair} {l : SignedPairLabel N} (hl : signedPairLabel N p=l)
    (hbox : ∀r, |p.1 r| ≤ N ∧ |p.2 r| ≤ N)
    (hsq : (∑r, (p.1 r:ℝ)^2)=(∑r, (p.2 r:ℝ)^2))
    (hprod : |(∏r, (p.1 r:ℝ))-(∏r, (p.2 r:ℝ))| ≤ P) :
    positivePair p ∈ zeroAdjustedPairs
      (fun j r => signedBoxSet N (signedLabelRow l j r))
      (fun j => signedBoxShift (signedLabelRow l j))
      (fun j => signedBoxZero (signedLabelRow l j)) P := by
  have hl₀ (r : Fin 3) : signedBoxLabel N (p.1 r)=l.1 r :=
    congrFun (congrArg Prod.fst hl) r
  have hl₁ (r : Fin 3) : signedBoxLabel N (p.2 r)=l.2 r :=
    congrFun (congrArg Prod.snd hl) r
  apply Finset.mem_filter.mpr
  constructor
  · apply Finset.mem_product.mpr
    constructor
    · apply Fintype.mem_piFinset.mpr
      intro r
      have hh := positiveCode_mem_signedBox hN (hbox r).1
      rw [hl₀ r] at hh
      exact hh
    · apply Fintype.mem_piFinset.mpr
      intro r
      have hh := positiveCode_mem_signedBox hN (hbox r).2
      rw [hl₁ r] at hh
      exact hh
  · constructor
    · change logBoxSquare (signedBoxShift l.1) (positiveTriple p.1)=
        logBoxSquare (signedBoxShift l.2) (positiveTriple p.2)
      rw [signedBoxShift_square hl₀,signedBoxShift_square hl₁]
      exact hsq
    · change |zeroAdjustedProduct (signedBoxZero l.1) (positiveTriple p.1)-
        zeroAdjustedProduct (signedBoxZero l.2) (positiveTriple p.2)| ≤ P
      rw [signedBoxZero_product hl₀,signedBoxZero_product hl₁]
      exact (abs_abs_sub_abs_le_abs_sub _ _).trans hprod

theorem positivePair_inj_of_label {N : ℕ} {p r : SignedPair}
    (hl : signedPairLabel N p=signedPairLabel N r) (hc : positivePair p=positivePair r) : p=r := by
  apply Prod.ext
  · funext i
    exact positiveCode_inj_of_label (congrFun (congrArg Prod.fst hl) i)
      (congrFun (congrArg Prod.fst hc) i)
  · funext i
    exact positiveCode_inj_of_label (congrFun (congrArg Prod.snd hl) i)
      (congrFun (congrArg Prod.snd hc) i)

theorem signed_fiber_card_le_box {N : ℕ} (hN : 1 ≤ N) {P : ℝ}
    (Q : Finset SignedPair) (l : SignedPairLabel N)
    (hbox : ∀p∈Q, ∀r, |p.1 r| ≤ N ∧ |p.2 r| ≤ N)
    (hsq : ∀p∈Q, (∑r, (p.1 r:ℝ)^2)=(∑r, (p.2 r:ℝ)^2))
    (hprod : ∀p∈Q, |(∏r, (p.1 r:ℝ))-(∏r, (p.2 r:ℝ))| ≤ P) :
    (Q.filter (fun p => signedPairLabel N p=l)).card ≤
      (zeroAdjustedPairs (fun j r => signedBoxSet N (signedLabelRow l j r))
        (fun j => signedBoxShift (signedLabelRow l j))
        (fun j => signedBoxZero (signedLabelRow l j)) P).card := by
  classical
  apply Finset.card_le_card_of_injOn positivePair
  · intro p hp
    obtain ⟨hp,hl⟩ := Finset.mem_filter.mp hp
    exact positivePair_mem_box hN hl (hbox p hp) (hsq p hp) (hprod p hp)
  · intro p hp r hr he
    have hl := (Finset.mem_filter.mp hp).2.trans (Finset.mem_filter.mp hr).2.symm
    exact positivePair_inj_of_label hl he

theorem signedPairLabel_card (N : ℕ) :
    Fintype.card (SignedPairLabel N)=(4*(Nat.log 2 N+1))^6 := by
  simp only [SignedPairLabel,SignedBoxLabel,Fintype.card_prod,Fintype.card_fun,
    Fintype.card_bool,Fintype.card_fin]
  ring

theorem exists_signed_square_product_count_log_loss {ε : ℝ} (hε : 0 < ε) :
    ∃ C > (0:ℝ), ∀ (N : ℕ), 1 ≤ N → ∀ (P : ℝ), 0 ≤ P →
      ∀ (Q : Finset SignedPair),
        (∀p∈Q, ∀r, |p.1 r| ≤ N ∧ |p.2 r| ≤ N) →
        (∀p∈Q, (∑r, (p.1 r:ℝ)^2)=(∑r, (p.2 r:ℝ)^2)) →
        (∀p∈Q, |(∏r, (p.1 r:ℝ))-(∏r, (p.2 r:ℝ))| ≤ P) →
      (Q.card:ℝ) ≤ C*((4*(Nat.log 2 N+1):ℕ):ℝ)^6*
        ((N:ℝ)^2+P+1)*(N:ℝ)^((1:ℝ)+ε)*(1+Real.log N) := by
  classical
  obtain ⟨C,hC,h⟩ := exists_zeroAdjustedPairs_box_bound hε
  refine ⟨C,hC,?_⟩
  intro N hN P hP Q hbox hsq hprod
  have hcell (l : SignedPairLabel N) :
      ((Q.filter (fun p => signedPairLabel N p=l)).card : ℝ) ≤
        C*((N:ℝ)^2+P+1)*(N:ℝ)^((1:ℝ)+ε)*(1+Real.log N) := by
    have hc : ((Q.filter (fun p => signedPairLabel N p=l)).card : ℝ) ≤
        (zeroAdjustedPairs (fun j r => signedBoxSet N (signedLabelRow l j r))
          (fun j => signedBoxShift (signedLabelRow l j))
          (fun j => signedBoxZero (signedLabelRow l j)) P).card := by
      exact_mod_cast signed_fiber_card_le_box hN Q l hbox hsq hprod
    apply hc.trans
    exact h N hN P hP (fun j r => signedBoxLength N (signedLabelRow l j r))
      (fun j r => signedBoxLength_bounds hN _) _ (fun _ _ _ hn => signedBoxSet_range hn)
      _ _ (fun _ hz => signedBoxZero_has_unit hz)
  have he := Finset.card_eq_sum_card_fiberwise (s:=Q) (t:=Finset.univ)
    (f:=signedPairLabel N) (fun p (_hp : p∈Q) => Finset.mem_univ _)
  have her : (Q.card:ℝ)=∑l : SignedPairLabel N, ((Q.filter (fun p => signedPairLabel N p=l)).card : ℝ) := by
    exact_mod_cast he
  rw [her]
  have hh := Finset.sum_le_sum (fun l (_hl : l∈Finset.univ) => hcell l)
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,signedPairLabel_card,Nat.cast_pow] at hh
  exact hh.trans_eq (by ring)

theorem signed_label_log_budget {η : ℝ} (hη : 0 < η) {N : ℕ} (hN : 1 ≤ N) :
    (((4*(Nat.log 2 N+1):ℕ):ℝ))^6*(1+Real.log N) ≤
      (8:ℝ)^6*(1+7/η)^7*(N:ℝ)^η := by
  have hN₁ : (1:ℝ) ≤ N := by exact_mod_cast hN
  have hN₀ : (0:ℝ) < N := by linarith
  have hL : 0 ≤ 1+Real.log N := by linarith [Real.log_nonneg hN₁]
  have hlogtwo : (1/2:ℝ) ≤ Real.log 2 := by
    have hh := Real.one_sub_inv_le_log_of_pos (by norm_num : (0:ℝ) < 2)
    norm_num at hh ⊢
    exact hh
  have hn := Real.natLog_le_logb N 2
  norm_num only [Nat.cast_ofNat,Real.logb] at hn
  have hh := (le_div_iff₀ (Real.log_pos (by norm_num : (1:ℝ) < 2))).mp hn
  have hmul := mul_le_mul_of_nonneg_left hlogtwo (Nat.cast_nonneg (Nat.log 2 N))
  have hc : ((4*(Nat.log 2 N+1):ℕ):ℝ) ≤ 8*(1+Real.log N) := by
    push_cast
    nlinarith only [hh,hmul]
  have hp := pow_le_pow_left₀ (Nat.cast_nonneg (4*(Nat.log 2 N+1))) hc 6
  have hfirst : (((4*(Nat.log 2 N+1):ℕ):ℝ))^6*(1+Real.log N) ≤
      (8:ℝ)^6*(1+Real.log N)^7 :=
    (mul_le_mul_of_nonneg_right hp hL).trans_eq (by ring)
  have hl := one_add_log_le_rpow_budget hN₁ (show 0 < η/7 by positivity)
  have he : 1/(η/7)=7/η := by field_simp
  rw [he] at hl
  have hraised := pow_le_pow_left₀ hL hl 7
  rw [mul_pow,←Real.rpow_mul_natCast hN₀.le] at hraised
  norm_num only [Nat.cast_ofNat,show η/7*7=η by ring] at hraised
  exact hfirst.trans ((mul_le_mul_of_nonneg_left hraised
    (by positivity : (0:ℝ) ≤ 8^6)).trans_eq (by ring))

/-- The full signed six-variable square/product count. All zero coordinates,
signs, endpoints and actual source pairs are retained. -/
theorem exists_signed_square_product_count {ε : ℝ} (hε : 0 < ε) :
    ∃ C > (0:ℝ), ∀ (N : ℕ), 1 ≤ N → ∀ (P : ℝ), 0 ≤ P →
      ∀ (Q : Finset SignedPair),
        (∀p∈Q, ∀r, |p.1 r| ≤ N ∧ |p.2 r| ≤ N) →
        (∀p∈Q, (∑r, (p.1 r:ℝ)^2)=(∑r, (p.2 r:ℝ)^2)) →
        (∀p∈Q, |(∏r, (p.1 r:ℝ))-(∏r, (p.2 r:ℝ))| ≤ P) →
      (Q.card:ℝ) ≤ C*((N:ℝ)^2+P)*(N:ℝ)^((1:ℝ)+ε) := by
  obtain ⟨C,hC,h⟩ := exists_signed_square_product_count_log_loss (ε:=ε/2) (by positivity)
  let D := (8:ℝ)^6*(1+7/(ε/2))^7
  have hD : 0 < D := by dsimp [D]; positivity
  refine ⟨2*C*D,by positivity,?_⟩
  intro N hN P hP Q hbox hsq hprod
  have hN₁ : (1:ℝ) ≤ N := by exact_mod_cast hN
  have hN₀ : (0:ℝ) < N := by linarith
  have hh := h N hN P hP Q hbox hsq hprod
  have hbudget := signed_label_log_budget (show 0 < ε/2 by positivity) hN
  change (((4*(Nat.log 2 N+1):ℕ):ℝ))^6*(1+Real.log N) ≤ D*(N:ℝ)^(ε/2) at hbudget
  have he : C*((4*(Nat.log 2 N+1):ℕ):ℝ)^6*((N:ℝ)^2+P+1)*(N:ℝ)^((1:ℝ)+ε/2)*(1+Real.log N)=
      (C*((N:ℝ)^2+P+1)*(N:ℝ)^((1:ℝ)+ε/2))*
        (((4*(Nat.log 2 N+1):ℕ):ℝ)^6*(1+Real.log N)) := by ring
  rw [he] at hh
  have hm := hh.trans (mul_le_mul_of_nonneg_left hbudget (by positivity))
  have hpow : (N:ℝ)^((1:ℝ)+ε/2)*(N:ℝ)^(ε/2)=(N:ℝ)^((1:ℝ)+ε) := by
    rw [←Real.rpow_add hN₀]
    congr 1
    ring
  have he' : (C*((N:ℝ)^2+P+1)*(N:ℝ)^((1:ℝ)+ε/2))*(D*(N:ℝ)^(ε/2))=
      C*D*((N:ℝ)^2+P+1)*(N:ℝ)^((1:ℝ)+ε) := by
    calc
      _ = C*D*((N:ℝ)^2+P+1)*((N:ℝ)^((1:ℝ)+ε/2)*(N:ℝ)^(ε/2)) := by ring
      _ = _ := by rw [hpow]
  rw [he'] at hm
  have hscale : (N:ℝ)^2+P+1 ≤ 2*((N:ℝ)^2+P) := by nlinarith
  apply hm.trans
  have hs := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hscale (by positivity : 0 ≤ C*D))
    (Real.rpow_nonneg hN₀.le ((1:ℝ)+ε))
  exact hs.trans_eq (by ring)

namespace CubicEight

def hadamardFour (x : Fin 4 → ℤ) : Fin 4 → ℤ :=
  ![x 0+x 1+x 2+x 3, x 0+x 1-x 2-x 3,
    x 0-x 1+x 2-x 3, x 0-x 1-x 2+x 3]

/-- The actual integral coordinate change, with its scale and all four
inverse coordinates retained. No invertibility is postulated. -/
theorem hadamardFour_involution (x : Fin 4 → ℤ) :
    hadamardFour (hadamardFour x) = fun i => 4*x i := by
  funext i
  fin_cases i <;> simp [hadamardFour] <;> ring

theorem hadamardFour_injective : Function.Injective hadamardFour := by
  intro x y hxy
  have he := congrArg hadamardFour hxy
  rw [hadamardFour_involution,hadamardFour_involution] at he
  funext i
  have hi := congrFun he i
  omega

/-- The first three power sums in the literal four-coordinate transform. -/
theorem hadamardFour_power_sums (x : Fin 4 → ℤ) :
    (∑ i, x i)=hadamardFour x 0 ∧
      4*(∑ i, (x i)^2)=(hadamardFour x 0)^2+(hadamardFour x 1)^2+
        (hadamardFour x 2)^2+(hadamardFour x 3)^2 ∧
      16*(∑ i, (x i)^3)=(hadamardFour x 0)^3+
        3*hadamardFour x 0*((hadamardFour x 1)^2+
          (hadamardFour x 2)^2+(hadamardFour x 3)^2)+
        6*hadamardFour x 1*hadamardFour x 2*hadamardFour x 3 := by
  refine ⟨?_,?_,?_⟩ <;> simp [Fin.sum_univ_succ,hadamardFour] <;> ring

/-- Equal first and second moments turn the cubic difference into an exact
triple-product difference, with the correct factor 3/8. -/
theorem hadamardFour_cubic_resonance (x y : Fin 4 → ℤ)
    (hfirst : (∑ i, x i)=∑ i, y i)
    (hsecond : (∑ i, (x i)^2)=∑ i, (y i)^2) :
    hadamardFour x 0=hadamardFour y 0 ∧
      (hadamardFour x 1)^2+(hadamardFour x 2)^2+(hadamardFour x 3)^2 =
        (hadamardFour y 1)^2+(hadamardFour y 2)^2+(hadamardFour y 3)^2 ∧
      3*(hadamardFour x 1*hadamardFour x 2*hadamardFour x 3-
        hadamardFour y 1*hadamardFour y 2*hadamardFour y 3) =
        8*((∑ i, (x i)^3)-∑ i, (y i)^3) := by
  obtain ⟨hx₁,hx₂,hx₃⟩ := hadamardFour_power_sums x
  obtain ⟨hy₁,hy₂,hy₃⟩ := hadamardFour_power_sums y
  have hzero : hadamardFour x 0=hadamardFour y 0 := by omega
  have hsq : (hadamardFour x 1)^2+(hadamardFour x 2)^2+(hadamardFour x 3)^2 =
      (hadamardFour y 1)^2+(hadamardFour y 2)^2+(hadamardFour y 3)^2 := by
    rw [hzero,hsecond] at hx₂
    linarith only [hx₂,hy₂]
  refine ⟨hzero,hsq,?_⟩
  rw [hzero,hsq] at hx₃
  linarith only [hx₃,hy₃]

/-- The finite near-cubic condition transfers without treating an
approximate moment equality as an exact one. -/
theorem hadamardFour_near_product (x y : Fin 4 → ℤ) {P : ℤ}
    (hfirst : (∑ i, x i)=∑ i, y i)
    (hsecond : (∑ i, (x i)^2)=∑ i, (y i)^2)
    (hthird : |(∑ i, (x i)^3)-∑ i, (y i)^3| ≤ P) :
    3*|hadamardFour x 1*hadamardFour x 2*hadamardFour x 3-
      hadamardFour y 1*hadamardFour y 2*hadamardFour y 3| ≤ 8*P := by
  have he := congrArg abs (hadamardFour_cubic_resonance x y hfirst hsecond).2.2
  simp only [abs_mul,show |(3:ℤ)|=3 by norm_num,show |(8:ℤ)|=8 by norm_num] at he
  linarith only [he,hthird]

/-- Every transformed integer remains in the literal enlarged box. -/
theorem hadamardFour_abs_le (x : Fin 4 → ℤ) {N : ℤ}
    (hx : ∀ i, |x i| ≤ N) (i : Fin 4) : |hadamardFour x i| ≤ 4*N := by
  have h0 := abs_le.mp (hx 0)
  have h1 := abs_le.mp (hx 1)
  have h2 := abs_le.mp (hx 2)
  have h3 := abs_le.mp (hx 3)
  fin_cases i <;> simp [hadamardFour,abs_le] <;> omega

def sixSquareProductSolutions (N P : ℕ) :
    Finset ((Fin 3 → ℤ) × (Fin 3 → ℤ)) := by
  classical
  let box := Fintype.piFinset (fun _ : Fin 3 => Finset.Icc (-(N:ℤ)) N)
  exact (box ×ˢ box).filter (fun p => (∑ i, (p.1 i)^2)=∑ i, (p.2 i)^2 ∧
    |p.1 0*p.1 1*p.1 2-p.2 0*p.2 1*p.2 2| ≤ (P:ℤ))

def cubicEightCode (p : (Fin 4 → ℤ) × (Fin 4 → ℤ)) :
    ℤ × ((Fin 3 → ℤ) × (Fin 3 → ℤ)) :=
  (hadamardFour p.1 0,(fun i => hadamardFour p.1 i.succ,
    fun i => hadamardFour p.2 i.succ))

/-- The common first moment plus the six transformed coordinates determines
the original eight integers; there is no lost source multiplicity. -/
theorem cubicEightCode_injOn :
    Set.InjOn cubicEightCode {p | (∑ i, p.1 i)=∑ i, p.2 i} := by
  intro p hp q hq he
  have h0 := congrArg (fun z => z.1) he
  have h1 := congrArg (fun z => z.2.1) he
  have h2 := congrArg (fun z => z.2.2) he
  have hp₀ : hadamardFour p.1 0=hadamardFour p.2 0 :=
    (hadamardFour_power_sums p.1).1.symm.trans (hp.trans (hadamardFour_power_sums p.2).1)
  have hq₀ : hadamardFour q.1 0=hadamardFour q.2 0 :=
    (hadamardFour_power_sums q.1).1.symm.trans (hq.trans (hadamardFour_power_sums q.2).1)
  apply Prod.ext
  · apply hadamardFour_injective
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact h0
    · exact congrFun h1 j
  · apply hadamardFour_injective
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact hp₀.symm.trans (h0.trans hq₀)
    · exact congrFun h2 j

/-- Literal cardinality reduction of the cubic eight-variable source to
the six-variable square/product system, with all box and fiber losses proved.
The analytic square/product bound is supplied by the enclosing module. -/
theorem cubic_eight_count_le_six (N P : ℕ)
    (S : Finset ((Fin 4 → ℤ) × (Fin 4 → ℤ)))
    (hbox : ∀ p∈S, (∀ i, |p.1 i| ≤ (N:ℤ)) ∧ ∀ i, |p.2 i| ≤ (N:ℤ))
    (hfirst : ∀ p∈S, (∑ i, p.1 i)=∑ i, p.2 i)
    (hsecond : ∀ p∈S, (∑ i, (p.1 i)^2)=∑ i, (p.2 i)^2)
    (hthird : ∀ p∈S, |(∑ i, (p.1 i)^3)-∑ i, (p.2 i)^3| ≤ (P:ℤ)) :
    S.card ≤ (8*N+1)*(sixSquareProductSolutions (4*N) (8*P)).card := by
  classical
  let T := Finset.Icc (-4*(N:ℤ)) (4*N) ×ˢ sixSquareProductSolutions (4*N) (8*P)
  have hmaps : Set.MapsTo cubicEightCode S T := by
    intro p hp
    apply Finset.mem_product.mpr
    constructor
    · exact Finset.mem_Icc.mpr (abs_le.mp (hadamardFour_abs_le p.1 (hbox p hp).1 0))
    · apply Finset.mem_filter.mpr
      constructor
      · apply Finset.mem_product.mpr
        constructor
        · apply Fintype.mem_piFinset.mpr
          intro i
          have hh := abs_le.mp (hadamardFour_abs_le p.1 (hbox p hp).1 i.succ)
          simpa only [cubicEightCode,Nat.cast_mul,Nat.cast_ofNat,neg_mul] using
            (Finset.mem_Icc.mpr hh)
        · apply Fintype.mem_piFinset.mpr
          intro i
          have hh := abs_le.mp (hadamardFour_abs_le p.2 (hbox p hp).2 i.succ)
          simpa only [cubicEightCode,Nat.cast_mul,Nat.cast_ofNat,neg_mul] using
            (Finset.mem_Icc.mpr hh)
      · constructor
        · have hh := (hadamardFour_cubic_resonance p.1 p.2
            (hfirst p hp) (hsecond p hp)).2.1
          simpa [cubicEightCode,Fin.sum_univ_succ,←add_assoc] using hh
        · have hh := hadamardFour_near_product p.1 p.2
            (hfirst p hp) (hsecond p hp) (hthird p hp)
          change |hadamardFour p.1 1*hadamardFour p.1 2*hadamardFour p.1 3-
            hadamardFour p.2 1*hadamardFour p.2 2*hadamardFour p.2 3| ≤ ((8*P:ℕ):ℤ)
          push_cast
          linarith [abs_nonneg (hadamardFour p.1 1*hadamardFour p.1 2*hadamardFour p.1 3-
            hadamardFour p.2 1*hadamardFour p.2 2*hadamardFour p.2 3)]
  have hc := Finset.card_le_card_of_injOn cubicEightCode hmaps
    (fun p hp q hq he => cubicEightCode_injOn (hfirst p hp) (hfirst q hq) he)
  have hcard : (Finset.Icc (-4*(N:ℤ)) (4*N)).card=8*N+1 := by
    rw [Int.card_Icc]
    omega
  simpa only [T,Finset.card_product,hcard] using hc

#print axioms hadamardFour_involution
#print axioms hadamardFour_injective
#print axioms hadamardFour_power_sums
#print axioms hadamardFour_cubic_resonance
#print axioms hadamardFour_near_product
#print axioms hadamardFour_abs_le
#print axioms cubicEightCode_injOn
#print axioms cubic_eight_count_le_six

-- Equal first two moments do not make the cubic difference vanish.
example :
    (∑ i : Fin 4, (![0,3,5,6] : Fin 4 → ℤ) i)=
      ∑ i : Fin 4, (![1,2,4,7] : Fin 4 → ℤ) i ∧
    (∑ i : Fin 4, ((![0,3,5,6] : Fin 4 → ℤ) i)^2)=
      ∑ i : Fin 4, ((![1,2,4,7] : Fin 4 → ℤ) i)^2 ∧
    (∑ i : Fin 4, ((![0,3,5,6] : Fin 4 → ℤ) i)^3)-
      (∑ i : Fin 4, ((![1,2,4,7] : Fin 4 → ℤ) i)^3) = -48 := by
  norm_num [Fin.sum_univ_succ]

-- The exact nonzero product difference is -128, not the cubic difference.
example :
    let x : Fin 4 → ℤ := ![0,3,5,6]
    let y : Fin 4 → ℤ := ![1,2,4,7]
    hadamardFour x 1*hadamardFour x 2*hadamardFour x 3-
      hadamardFour y 1*hadamardFour y 2*hadamardFour y 3 = -128 := by
  decide

-- The finite reduction retains the all-zero source and its enlarged-box boundary.
example : (sixSquareProductSolutions 0 0).card=1 := by
  simp [sixSquareProductSolutions,Finset.filter_singleton]

theorem exists_sixSquareProductSolutions_bound {ε : ℝ} (hε : 0 < ε) :
    ∃ C > (0:ℝ), ∀ (N : ℕ), 1 ≤ N → ∀ (P : ℕ),
      ((sixSquareProductSolutions N P).card : ℝ) ≤
        C*((N:ℝ)^2+P)*(N:ℝ)^((1:ℝ)+ε) := by
  obtain ⟨C,hC,h⟩ := exists_signed_square_product_count hε
  refine ⟨C,hC,?_⟩
  intro N hN P
  apply h N hN P (Nat.cast_nonneg _) (sixSquareProductSolutions N P)
  · intro p hp r
    have hmem := Finset.mem_product.mp (Finset.mem_filter.mp hp).1
    exact ⟨abs_le.mpr (Finset.mem_Icc.mp (Fintype.mem_piFinset.mp hmem.1 r)),
      abs_le.mpr (Finset.mem_Icc.mp (Fintype.mem_piFinset.mp hmem.2 r))⟩
  · intro p hp
    exact_mod_cast (Finset.mem_filter.mp hp).2.1
  · intro p hp
    have hh := (Finset.mem_filter.mp hp).2.2
    have hi : |(∏r, p.1 r)-(∏r, p.2 r)| ≤ (P:ℤ) := by
      simpa only [Fin.prod_univ_succ,Fin.prod_univ_zero,mul_one,mul_assoc] using hh
    exact_mod_cast hi

/-- The full finite cubic eighth-moment resonance count, with signed source
coordinates and all near-cubic differences retained. -/
theorem exists_cubic_eight_count {ε : ℝ} (hε : 0 < ε) :
    ∃ C > (0:ℝ), ∀ (N : ℕ), 1 ≤ N → ∀ (P : ℕ),
      ∀ (S : Finset ((Fin 4 → ℤ) × (Fin 4 → ℤ))),
        (∀p∈S, (∀r, |p.1 r| ≤ (N:ℤ)) ∧ ∀r, |p.2 r| ≤ (N:ℤ)) →
        (∀p∈S, (∑r, p.1 r)=∑r, p.2 r) →
        (∀p∈S, (∑r, (p.1 r)^2)=∑r, (p.2 r)^2) →
        (∀p∈S, |(∑r, (p.1 r)^3)-∑r, (p.2 r)^3| ≤ (P:ℤ)) →
      (S.card:ℝ) ≤ C*((N:ℝ)^2+P)*(N:ℝ)^((2:ℝ)+ε) := by
  obtain ⟨C,hC,h⟩ := exists_sixSquareProductSolutions_bound hε
  refine ⟨144*C*(4:ℝ)^((1:ℝ)+ε),by positivity,?_⟩
  intro N hN P S hbox hfirst hsecond hthird
  have hN₁ : (1:ℝ) ≤ N := by exact_mod_cast hN
  have hN₀ : (0:ℝ) < N := by linarith
  have hc : (S.card:ℝ) ≤ (8*N+1)*((sixSquareProductSolutions (4*N) (8*P)).card:ℝ) := by
    exact_mod_cast cubic_eight_count_le_six N P S hbox hfirst hsecond hthird
  have hh := h (4*N) (by omega) (8*P)
  norm_num only [Nat.cast_mul,Nat.cast_ofNat] at hh
  have hm := hc.trans (mul_le_mul_of_nonneg_left hh (by positivity))
  rw [Real.mul_rpow (by norm_num) hN₀.le] at hm
  have hscale : (4*(N:ℝ))^2+8*P ≤ 16*((N:ℝ)^2+P) := by
    nlinarith [(Nat.cast_nonneg P : (0:ℝ) ≤ P)]
  have hlen : 8*(N:ℝ)+1 ≤ 9*N := by linarith
  have hbound : (8*(N:ℝ)+1)*(C*((4*N)^2+8*P)*((4:ℝ)^((1:ℝ)+ε)*(N:ℝ)^((1:ℝ)+ε))) ≤
      (9*N)*(C*(16*((N:ℝ)^2+P))*((4:ℝ)^((1:ℝ)+ε)*(N:ℝ)^((1:ℝ)+ε))) := by gcongr
  apply hm.trans (hbound.trans_eq ?_)
  have he : (N:ℝ)^((2:ℝ)+ε)=(N:ℝ)*(N:ℝ)^((1:ℝ)+ε) := by
    rw [show (2:ℝ)+ε=1+(1+ε) by ring,Real.rpow_add hN₀,Real.rpow_one]
  rw [he]
  ring

#print axioms exists_sixSquareProductSolutions_bound
#print axioms exists_cubic_eight_count

end CubicEight

-- A zero-frequency correction keeps the original square sum literal.
example : logBoxSquare (-2) ![1,1,5]=25 ∧ logBoxSquare (-1) ![1,3,4]=25 := by
  norm_num [logBoxSquare,Fin.sum_univ_succ]

example : (logCrossPairs (fun _ _ => {1}) (fun _ => -1) 0).card=1 := by
  simp [logCrossPairs,Fintype.piFinset_singleton,logBoxSquare,logBoxLog,Finset.filter_singleton]

#print axioms boxProduct_pos
#print axioms signedPairLabel_card
#print axioms exists_signed_square_product_count_log_loss
#print axioms signed_label_log_budget
#print axioms exists_signed_square_product_count
#print axioms signedBoxShift_square
#print axioms signedBoxZero_product
#print axioms signedBoxZero_has_unit
#print axioms positivePair_mem_box
#print axioms positivePair_inj_of_label
#print axioms signed_fiber_card_le_box
#print axioms positiveCode_pos
#print axioms positiveCode_le
#print axioms positiveCode_reconstruct
#print axioms positiveCode_square
#print axioms signedBoxLength_bounds
#print axioms signedBoxSet_range
#print axioms positiveCode_mem_signedBox
#print axioms positiveCode_inj_of_label
#print axioms boxProduct_rpow_budget
#print axioms exists_zeroAdjustedPairs_box_bound
#print axioms zero_product_upper
#print axioms zeroAdjustedPairs_subset_high
#print axioms boxProduct_le_cube
#print axioms boxProduct_le_square_of_one
#print axioms boxProduct_comparison
#print axioms zeroAdjustedPairs_subset_global
#print axioms positive_products_high_log
#print axioms logBoxLog_eq_log_product
#print axioms abs_log_sub_le_gap
#print axioms logBoxLog_difference_le
#print axioms logBoxLog_mem
#print axioms logBoxLog_difference_le_global
#print axioms logCrossPairs_card_le_near
#print axioms exists_logCrossPairs_bound
#print axioms continuous_logBoxSum
#print axioms logBoxFamily_central_le
#print axioms exists_two_box_central_moment

#print axioms exists_two_box_log_near_count
#print axioms logBoxSum_eq_product
#print axioms logBoxSum_norm_sq
#print axioms logSum_periodic
#print axioms periodic_integral_two
#print axioms logBoxSum_central_integral
#print axioms logBoxFamily_sum
#print axioms logBoxFamily_norm_sq_le
#print axioms continuous_logSum
#print axioms logSum_sixth_eq
#print axioms three_mul_prod_le_sum_cube
#print axioms normalized_triple_bound
#print axioms exists_mixed_logarithmic_sixth

end TaoTrudgianYang2025.SquareProductPrototype
