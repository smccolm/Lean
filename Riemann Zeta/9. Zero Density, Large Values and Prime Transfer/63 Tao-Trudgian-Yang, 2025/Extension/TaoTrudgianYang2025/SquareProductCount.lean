import TaoTrudgianYang2025.LogarithmicSixthMoment
import TaoTrudgianYang2025.SargosDualTentWindow
import TaoTrudgianYang2025.BetaCanonicalTaylorLegendre
import TaoTrudgianYang2025.ExponentPairShiftUniformity
import TaoTrudgianYang2025.SargosWithinDerivativeCalculus
import TaoTrudgianYang2025.ExponentPairAllHeights
import TaoTrudgianYang2025.PositiveSlopeCharts
import TaoTrudgianYang2025.BourgainDyadicBands
import TaoTrudgianYang2025.DyadicMomentCutoff
import TaoTrudgianYang2025.SargosDProcessGeometry
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! The full signed square/product count from the actual logarithmic sixth moment.

The public endpoint `exists_signed_square_product_count` proves
C_epsilon (N^2+P) N^(1+epsilon), uniformly for N>=1 and P>=0.
All coordinate signs, zeros, closed box endpoints and source multiplicities
are retained through an injective finite dyadic cover. The actual two-box
moment and existing tent-count kernel provide the analytic estimate.

The nested `CubicEight.exists_cubic_eight_count` consumes the exact
eight-to-six Hadamard injection and proves the sharp finite cubic resonance
count C_epsilon (N^2+P) N^(2+epsilon). The nested `CubicMoment` now derives
the literal weighted cubic eighth-moment integral on the physical window
[0,1/P], using exact integer orthogonality and the existing rectangular-window
estimate. The nested `CubicSource` then uses the existing four-dimensional sieve
and common-prefix Taylor theorem to reduce the literal original C4 sum to its
actual joint derivative-pair count, retaining the averaging boundary term.
The sharp derivative-pair estimate is proved in `CubicJointCount`; its
literal closed-source eighth-power consumer derives every derivative and
endpoint hypothesis. Final Sargos D physical-scale assembly remains open. -/

noncomputable section
open Set MeasureTheory GafniTao
open scoped BigOperators FourierTransform
namespace TaoTrudgianYang2025.SquareProductCount
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


end CubicEight

namespace CubicMoment
open CubicEight
open scoped ComplexConjugate

theorem integral_integer_character (n : ℤ) :
    (∫ x : ℝ in Icc (0:ℝ) 1, fordAdditiveCharacter ((n:ℝ)*x))=
      if n=0 then (1:ℂ) else 0 := by
  by_cases hn : n=0
  · simp [hn,fordAdditiveCharacter]
  rw [if_neg hn,integral_Icc_eq_integral_Ioc,
    ←intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1)]
  let c : ℂ := (n:ℂ)*(2*Real.pi*Complex.I)
  have hc : c ≠ 0 := by
    dsimp [c]
    exact mul_ne_zero (by exact_mod_cast hn)
      (mul_ne_zero (mul_ne_zero (by norm_num) (by exact_mod_cast Real.pi_ne_zero)) Complex.I_ne_zero)
  have he (x : ℝ) : fordAdditiveCharacter ((n:ℝ)*x)=Complex.exp (c*x) := by
    unfold fordAdditiveCharacter c
    push_cast
    congr 1
    ring
  simp_rw [he]
  rw [integral_exp_mul_complex hc]
  simp only [Complex.ofReal_one,Complex.ofReal_zero,mul_one,mul_zero,Complex.exp_zero]
  have hexp : Complex.exp c=1 := Complex.exp_int_mul_two_pi_mul_I n
  rw [hexp,sub_self,zero_div]

theorem integral_integer_planar_character (n m : ℤ) :
    (∫ α : ℝ in Icc (0:ℝ) 1, ∫ β : ℝ in Icc (0:ℝ) 1,
      fordAdditiveCharacter ((n:ℝ)*α+(m:ℝ)*β))=
        if n=0 ∧ m=0 then (1:ℂ) else 0 := by
  simp_rw [fordAdditiveCharacter_add,integral_const_mul,integral_integer_character,
    integral_mul_const,integral_integer_character]
  by_cases hn : n=0 <;> by_cases hm : m=0 <;> simp [hn,hm]

theorem integer_planar_inner (n m : ℤ) (c : ℂ) (α : ℝ) :
    (∫ β : ℝ in Icc (0:ℝ) 1,
      c*fordAdditiveCharacter ((n:ℝ)*α+(m:ℝ)*β))=
      (c*fordAdditiveCharacter ((n:ℝ)*α))*(if m=0 then 1 else 0) := by
  simp_rw [fordAdditiveCharacter_add,←mul_assoc,integral_const_mul,integral_integer_character]

theorem integer_planar_norm_sq_integral {ι : Type*} (S : Finset ι)
    (z : ι → ℂ) (u v : ι → ℤ) :
    ((∫ α : ℝ in Icc (0:ℝ) 1, ∫ β : ℝ in Icc (0:ℝ) 1,
      ‖sargosPlanarSum S z (fun i => (u i:ℝ)) (fun i => (v i:ℝ)) α β‖^2 : ℝ):ℂ)=
      ∑p∈S ×ˢ S, if u p.1=u p.2 ∧ v p.1=v p.2 then z p.1*conj (z p.2) else 0 := by
  classical
  let A := fun (p : ι × ι) (α β : ℝ) => (z p.1*conj (z p.2))*
    fordAdditiveCharacter (((u p.1-u p.2:ℤ):ℝ)*α+((v p.1-v p.2:ℤ):ℝ)*β)
  have hi (p : ι × ι) (α : ℝ) : IntegrableOn (A p α) (Icc (0:ℝ) 1) := by
    have hc : Continuous (A p α) := by unfold A fordAdditiveCharacter; fun_prop
    exact hc.continuousOn.integrableOn_compact isCompact_Icc
  have he (p : ι × ι) (α : ℝ) : (∫ β : ℝ in Icc (0:ℝ) 1, A p α β)=
      (z p.1*conj (z p.2))*fordAdditiveCharacter (((u p.1-u p.2:ℤ):ℝ)*α)*
        (if v p.1-v p.2=0 then 1 else 0) :=
    integer_planar_inner _ _ _ α
  have ho (p : ι × ι) : IntegrableOn (fun α => ∫ β : ℝ in Icc (0:ℝ) 1, A p α β) (Icc (0:ℝ) 1) := by
    simp_rw [he]
    have hc : Continuous (fun α =>
        (z p.1*conj (z p.2))*fordAdditiveCharacter (((u p.1-u p.2:ℤ):ℝ)*α)*
          (if v p.1-v p.2=0 then 1 else 0)) := by unfold fordAdditiveCharacter; fun_prop
    exact hc.continuousOn.integrableOn_compact isCompact_Icc
  rw [←integral_complex_ofReal]
  simp_rw [←integral_complex_ofReal,sargosPlanarSum_norm_sq]
  have hA : (fun (α β : ℝ) => ∑p∈S ×ˢ S,
      z p.1*conj (z p.2)*fordAdditiveCharacter
        (((u p.1:ℝ)-(u p.2:ℝ))*α+((v p.1:ℝ)-(v p.2:ℝ))*β))=
      fun α β => ∑p∈S ×ˢ S, A p α β := by simp only [A,Int.cast_sub]
  change (∫ α : ℝ in Icc (0:ℝ) 1, ∫ β : ℝ in Icc (0:ℝ) 1,
    (fun α β => ∑p∈S ×ˢ S, z p.1*conj (z p.2)*fordAdditiveCharacter
      (((u p.1:ℝ)-(u p.2:ℝ))*α+((v p.1:ℝ)-(v p.2:ℝ))*β)) α β)=_
  rw [hA]
  simp_rw [integral_finsetSum _ (fun p _ => hi p _)]
  rw [integral_finsetSum _ (fun p _ => ho p)]
  apply Finset.sum_congr rfl
  intro p _hp
  simp_rw [he,integral_mul_const,integral_const_mul,integral_integer_character]
  by_cases hu : u p.1=u p.2 <;> by_cases hv : v p.1=v p.2 <;> simp [sub_eq_zero,hu,hv]

theorem integer_planar_collision_compression {ι : Type*} (S : Finset ι)
    (z : ι → ℂ) (u v w : ι → ℤ)
    (hw : ∀i∈S, ∀j∈S, w i=w j ↔ u i=u j ∧ v i=v j) :
    (∫ α : ℝ in Icc (0:ℝ) 1, ∫ β : ℝ in Icc (0:ℝ) 1,
      ‖sargosPlanarSum S z (fun i => (u i:ℝ)) (fun i => (v i:ℝ)) α β‖^2)=
      ∫ x : ℝ in Icc (0:ℝ) 1,
        ‖sargosPlanarSum S z (fun i => (w i:ℝ)) (fun _ => 0) x 0‖^2 := by
  have hzero (x y : ℝ) :
      sargosPlanarSum S z (fun i => (w i:ℝ)) (fun _ => 0) x y=
        sargosPlanarSum S z (fun i => (w i:ℝ)) (fun _ => 0) x 0 := by
    simp only [sargosPlanarSum,zero_mul,add_zero]
  have he : (∫ x : ℝ in Icc (0:ℝ) 1, ∫ y : ℝ in Icc (0:ℝ) 1,
      ‖sargosPlanarSum S z (fun i => (w i:ℝ)) (fun _ => 0) x y‖^2)=
      ∫ x : ℝ in Icc (0:ℝ) 1,
        ‖sargosPlanarSum S z (fun i => (w i:ℝ)) (fun _ => 0) x 0‖^2 := by
    simp_rw [hzero]
    simp only [setIntegral_const,smul_eq_mul,Real.volume_real_Icc_of_le (by norm_num : (0:ℝ) ≤ 1),
      sub_zero,one_mul]
  rw [←he]
  apply Complex.ofReal_injective
  have hwgram := integer_planar_norm_sq_integral S z w (fun _ => 0)
  simp only [Int.cast_zero] at hwgram
  rw [integer_planar_norm_sq_integral,hwgram]
  apply Finset.sum_congr rfl
  intro p hp
  obtain ⟨hi,hj⟩ := Finset.mem_product.mp hp
  simp only [and_true,hw p.1 hi p.2 hj]

theorem integer_carry_separation {a b c d B : ℤ} (hB : 0 < B)
    (hab : |a-b| < B) : a+B*c=b+B*d ↔ a=b ∧ c=d := by
  constructor
  · intro h
    have he : a-b=-(B*(c-d)) := by linarith only [h]
    have ha := congrArg abs he
    rw [abs_neg,abs_mul,abs_of_pos hB] at ha
    have hcd : c=d := by
      by_contra hn
      have hg : 1 ≤ |c-d| := by
        have hp := abs_pos.mpr (sub_ne_zero.mpr hn)
        omega
      have hm := mul_le_mul_of_nonneg_left hg hB.le
      omega
    exact ⟨by rw [hcd] at h; omega,hcd⟩
  · rintro ⟨rfl,rfl⟩
    rfl

def cubicTupleSet (N : ℕ) : Finset (Fin 4 → ℤ) :=
  Fintype.piFinset (fun _ => Finset.Icc (1:ℤ) N)

def cubicFirst (n : Fin 4 → ℤ) : ℤ := ∑r, n r
def cubicSecond (n : Fin 4 → ℤ) : ℤ := ∑r, (n r)^2
def cubicThird (n : Fin 4 → ℤ) : ℤ := ∑r, (n r)^3
def cubicCombined (N : ℕ) (n : Fin 4 → ℤ) : ℤ := cubicFirst n+(8*(N:ℤ)+1)*cubicSecond n

theorem cubicTuple_abs {N : ℕ} {n : Fin 4 → ℤ} (hn : n∈cubicTupleSet N) (r : Fin 4) :
    |n r| ≤ (N:ℤ) := by
  have hh := Finset.mem_Icc.mp (Fintype.mem_piFinset.mp hn r)
  rw [abs_of_nonneg (by omega)]
  exact hh.2

theorem cubicFirst_abs {N : ℕ} {n : Fin 4 → ℤ} (hn : n∈cubicTupleSet N) :
    |cubicFirst n| ≤ 4*(N:ℤ) := by
  have hh := (Finset.abs_sum_le_sum_abs (s:=Finset.univ) (f:=n)).trans
    (Finset.sum_le_sum (fun r (_hr : r∈Finset.univ) => cubicTuple_abs hn r))
  simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] using hh

theorem cubicCombined_collision {N : ℕ} {n m : Fin 4 → ℤ}
    (hn : n∈cubicTupleSet N) (hm : m∈cubicTupleSet N) :
    cubicCombined N n=cubicCombined N m ↔ cubicFirst n=cubicFirst m ∧ cubicSecond n=cubicSecond m := by
  have ha := (abs_sub_le (cubicFirst n) 0 (cubicFirst m)).trans
    (add_le_add (by simpa using cubicFirst_abs hn) (by simpa using cubicFirst_abs hm))
  have hb : 0 < 8*(N:ℤ)+1 := by positivity
  exact integer_carry_separation hb (by linarith only [ha])

def cubicSourceSum (N : ℕ) (z : ℤ → ℂ) (α β γ : ℝ) : ℂ :=
  ∑ n∈Finset.Icc (1:ℤ) N,
    z n*fordAdditiveCharacter ((n:ℝ)*α+(n:ℝ)^2*β+(n:ℝ)^3*γ)

def cubicTupleCoefficient (z : ℤ → ℂ) (n : Fin 4 → ℤ) : ℂ := ∏r, z (n r)

theorem cubicSourceSum_fourth (N : ℕ) (z : ℤ → ℂ) (α β γ : ℝ) :
    (cubicSourceSum N z α β γ)^4=
      sargosPlanarSum (cubicTupleSet N)
        (fun n => cubicTupleCoefficient z n*fordAdditiveCharacter ((cubicThird n:ℝ)*γ))
        (fun n => (cubicFirst n:ℝ)) (fun n => (cubicSecond n:ℝ)) α β := by
  classical
  have hp : (cubicSourceSum N z α β γ)^4=∏ _r : Fin 4, cubicSourceSum N z α β γ := by simp
  rw [hp]
  unfold cubicSourceSum
  rw [Finset.prod_univ_sum]
  unfold sargosPlanarSum cubicTupleSet
  apply Finset.sum_congr rfl
  intro n _hn
  rw [Finset.prod_mul_distrib,sargos_character_finset_prod]
  unfold cubicTupleCoefficient
  rw [mul_assoc,←fordAdditiveCharacter_add]
  congr 2
  unfold cubicFirst cubicSecond cubicThird
  push_cast
  rw [Finset.sum_add_distrib,Finset.sum_add_distrib,←Finset.sum_mul,←Finset.sum_mul,←Finset.sum_mul]
  ring

theorem cubicSourceSum_eighth (N : ℕ) (z : ℤ → ℂ) (α β γ : ℝ) :
    ‖cubicSourceSum N z α β γ‖^8=
      ‖sargosPlanarSum (cubicTupleSet N)
        (fun n => cubicTupleCoefficient z n*fordAdditiveCharacter ((cubicThird n:ℝ)*γ))
        (fun n => (cubicFirst n:ℝ)) (fun n => (cubicSecond n:ℝ)) α β‖^2 := by
  rw [←cubicSourceSum_fourth,norm_pow,←pow_mul]

theorem cubic_modulation_sum (N : ℕ) (z : ℤ → ℂ) (x γ : ℝ) :
    sargosPlanarSum (cubicTupleSet N)
      (fun n => cubicTupleCoefficient z n*fordAdditiveCharacter ((cubicThird n:ℝ)*γ))
      (fun n => (cubicCombined N n:ℝ)) (fun _ => 0) x 0=
      sargosPlanarSum (cubicTupleSet N) (cubicTupleCoefficient z)
        (fun n => (cubicCombined N n:ℝ)) (fun n => (cubicThird n:ℝ)) x γ := by
  unfold sargosPlanarSum
  apply Finset.sum_congr rfl
  intro n _hn
  rw [mul_assoc,←fordAdditiveCharacter_add]
  simp only [zero_mul,add_zero]
  congr 2
  ring

theorem cubic_eighth_torus_eq_combined (N : ℕ) (z : ℤ → ℂ) (γ : ℝ) :
    (∫ α : ℝ in Icc (0:ℝ) 1, ∫ β : ℝ in Icc (0:ℝ) 1,
      ‖cubicSourceSum N z α β γ‖^8)=
      ∫ x : ℝ in Icc (0:ℝ) 1,
        ‖sargosPlanarSum (cubicTupleSet N) (cubicTupleCoefficient z)
          (fun n => (cubicCombined N n:ℝ)) (fun n => (cubicThird n:ℝ)) x γ‖^2 := by
  simp_rw [cubicSourceSum_eighth]
  rw [integer_planar_collision_compression (cubicTupleSet N) _ cubicFirst cubicSecond (cubicCombined N)
    (fun _ hn _ hm => cubicCombined_collision hn hm)]
  simp_rw [cubic_modulation_sum]

theorem cubicTupleCoefficient_norm {N : ℕ} {z : ℤ → ℂ}
    (hz : ∀n∈Finset.Icc (1:ℤ) N, ‖z n‖ ≤ 1) {n : Fin 4 → ℤ} (hn : n∈cubicTupleSet N) :
    ‖cubicTupleCoefficient z n‖ ≤ 1 := by
  unfold cubicTupleCoefficient
  rw [norm_prod]
  have hh := Finset.prod_le_prod (s:=Finset.univ) (f:=fun r => ‖z (n r)‖) (g:=fun _ => (1:ℝ))
    (fun r _ => norm_nonneg _) (fun r _ => hz _ (Fintype.mem_piFinset.mp hn r))
  simpa only [Finset.prod_const_one] using hh

theorem int_eq_of_real_half_gap {a b : ℤ} (h : |(a:ℝ)-(b:ℝ)| ≤ 1/2) : a=b := by
  have hh : |(a:ℝ)-(b:ℝ)| < 1 := lt_of_le_of_lt h (by norm_num)
  have hi : |a-b| < 1 := by exact_mod_cast hh
  exact sub_eq_zero.mp (abs_eq_zero.mp (le_antisymm (by omega) (abs_nonneg _)))

theorem exists_cubic_combined_near_count {ε : ℝ} (hε : 0 < ε) :
    ∃ C > (0:ℝ), ∀ (N : ℕ), 1 ≤ N → ∀ (P : ℝ), 0 ≤ P →
      ((sargosNearPairs (cubicTupleSet N) (fun n => (cubicCombined N n:ℝ))
        (fun n => (cubicThird n:ℝ)) (1/2) P).card:ℝ) ≤
        C*((N:ℝ)^2+P)*(N:ℝ)^((2:ℝ)+ε) := by
  obtain ⟨C,hC,h⟩ := exists_cubic_eight_count hε
  refine ⟨2*C,by positivity,?_⟩
  intro N hN P hP
  let S := sargosNearPairs (cubicTupleSet N) (fun n => (cubicCombined N n:ℝ))
    (fun n => (cubicThird n:ℝ)) (1/2) P
  have hbox (p : (Fin 4 → ℤ) × (Fin 4 → ℤ)) (hp : p∈S) :
      (∀r, |p.1 r| ≤ (N:ℤ)) ∧ ∀r, |p.2 r| ≤ (N:ℤ) := by
    have hh := Finset.mem_product.mp (Finset.mem_filter.mp hp).1
    exact ⟨cubicTuple_abs hh.1,cubicTuple_abs hh.2⟩
  have hcollision (p : (Fin 4 → ℤ) × (Fin 4 → ℤ)) (hp : p∈S) :
      cubicFirst p.1=cubicFirst p.2 ∧ cubicSecond p.1=cubicSecond p.2 := by
    obtain ⟨hp,hfirst,_hthird⟩ := Finset.mem_filter.mp hp
    have hh := Finset.mem_product.mp hp
    exact (cubicCombined_collision hh.1 hh.2).mp (int_eq_of_real_half_gap hfirst)
  have hthird (p : (Fin 4 → ℤ) × (Fin 4 → ℤ)) (hp : p∈S) :
      |(∑r, (p.1 r)^3)-∑r, (p.2 r)^3| ≤ (⌈P⌉₊:ℤ) := by
    have hh := (Finset.mem_filter.mp hp).2.2
    have hb : |(cubicThird p.1:ℝ)-(cubicThird p.2:ℝ)| ≤ (⌈P⌉₊:ℝ) :=
      hh.trans (Nat.le_ceil P)
    exact_mod_cast hb
  have hh := h N hN ⌈P⌉₊ S hbox (fun p hp => (hcollision p hp).1)
    (fun p hp => (hcollision p hp).2) hthird
  have hN₁ : (1:ℝ) ≤ N := by exact_mod_cast hN
  have hceil : (⌈P⌉₊:ℝ) ≤ P+1 := (Nat.ceil_lt_add_one hP).le
  have hscale : (N:ℝ)^2+⌈P⌉₊ ≤ 2*((N:ℝ)^2+P) := by nlinarith
  apply hh.trans
  have hs := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hscale hC.le)
    (Real.rpow_nonneg (Nat.cast_nonneg N) ((2:ℝ)+ε))
  exact hs.trans_eq (by ring)

def cubicEighthMoment (N : ℕ) (z : ℤ → ℂ) (P : ℝ) : ℝ :=
  ∫ γ : ℝ in Icc (0:ℝ) (1/P), ∫ α : ℝ in Icc (0:ℝ) 1,
    ∫ β : ℝ in Icc (0:ℝ) 1, ‖cubicSourceSum N z α β γ‖^8

theorem cubicEighthMoment_le_count (N : ℕ) (z : ℤ → ℂ)
    (hz : ∀n∈Finset.Icc (1:ℤ) N, ‖z n‖ ≤ 1) {P : ℝ} (hP : 0 < P) :
    P*cubicEighthMoment N z P ≤
      32*((sargosNearPairs (cubicTupleSet N) (fun n => (cubicCombined N n:ℝ))
        (fun n => (cubicThird n:ℝ)) (1/2) P).card:ℝ) := by
  let S := cubicTupleSet N
  let Z := cubicTupleCoefficient z
  let u := fun n => (cubicCombined N n:ℝ)
  let v := fun n => (cubicThird n:ℝ)
  let F := fun p : ℝ × ℝ => ‖sargosPlanarSum S Z u v p.1 p.2‖^2
  have hwindow : 0 < 1/P := by positivity
  have hi := integrable_sargosPlanarNormSq_rectangle S Z u v 0 1 0 (1/P)
  simp only [zero_add] at hi
  have he : cubicEighthMoment N z P=
      ∫ x : ℝ in Icc (0:ℝ) 1, ∫ γ : ℝ in Icc (0:ℝ) (1/P), F (x,γ) := by
    unfold cubicEighthMoment
    simp_rw [cubic_eighth_torus_eq_combined]
    exact (integral_prod_symm F hi).symm.trans (integral_prod F hi)
  have houter := integrable_sargosPlanarNormSq_window_outer S Z u v 0 2 0 (1/P)
  simp only [zero_add] at houter
  have hsubset : Icc (0:ℝ) 1 ⊆ Icc (0:ℝ) 2 := Icc_subset_Icc_right (by norm_num)
  have hmono : (∫ x : ℝ in Icc (0:ℝ) 1, ∫ γ : ℝ in Icc (0:ℝ) (1/P), F (x,γ)) ≤
      ∫ x : ℝ in Icc (0:ℝ) 2, ∫ γ : ℝ in Icc (0:ℝ) (1/P), F (x,γ) := by
    apply setIntegral_mono_set houter
      (Filter.Eventually.of_forall (fun x => integral_nonneg (fun γ => sq_nonneg _)))
    exact Filter.Eventually.of_forall (fun x hx => hsubset hx)
  have hz' (n : Fin 4 → ℤ) (hn : n∈S) : ‖Z n‖ ≤ 1 := cubicTupleCoefficient_norm hz hn
  have hw := sargosPlanar_window_le_nearPairs S Z u v hz' (δ:=2) (lambda:=1/P)
    (by norm_num) hwindow 0 0
  norm_num only [zero_add,show (16:ℝ)*2=32 by norm_num,one_div_one_div] at hw
  have hh := hmono.trans hw
  rw [he]
  have hp := mul_le_mul_of_nonneg_left hh hP.le
  apply hp.trans_eq
  field_simp
  rfl

/-- The literal weighted cubic eighth moment, in the original physical
window and normalized additive-character convention. -/
theorem exists_cubic_eighth_moment {ε : ℝ} (hε : 0 < ε) :
    ∃ C > (0:ℝ), ∀ (N : ℕ), 1 ≤ N → ∀ (P : ℝ), 0 < P →
      ∀ (z : ℤ → ℂ), (∀n∈Finset.Icc (1:ℤ) N, ‖z n‖ ≤ 1) →
      P*cubicEighthMoment N z P ≤ C*((N:ℝ)^2+P)*(N:ℝ)^((2:ℝ)+ε) := by
  obtain ⟨C,hC,h⟩ := exists_cubic_combined_near_count hε
  refine ⟨32*C,by positivity,?_⟩
  intro N hN P hP z hz
  have hh := (cubicEighthMoment_le_count N z hz hP).trans
    (mul_le_mul_of_nonneg_left (h N hN P hP.le) (by norm_num : (0:ℝ) ≤ 32))
  exact hh.trans_eq (by ring)

/-- Explicit unweighted original finite sum; the constant is independent
of both the length and the reciprocal cubic window. -/
theorem exists_cubic_eighth_moment_unweighted {ε : ℝ} (hε : 0 < ε) :
    ∃ C > (0:ℝ), ∀ (N : ℕ), 1 ≤ N → ∀ (P : ℝ), 0 < P →
      P*(∫ γ : ℝ in Icc (0:ℝ) (1/P), ∫ α : ℝ in Icc (0:ℝ) 1,
        ∫ β : ℝ in Icc (0:ℝ) 1,
          ‖∑ n∈Finset.Icc (1:ℤ) N,
            fordAdditiveCharacter ((n:ℝ)*α+(n:ℝ)^2*β+(n:ℝ)^3*γ)‖^8) ≤
        C*((N:ℝ)^2+P)*(N:ℝ)^((2:ℝ)+ε) := by
  obtain ⟨C,hC,h⟩ := exists_cubic_eighth_moment hε
  refine ⟨C,hC,?_⟩
  intro N hN P hP
  simpa only [cubicEighthMoment,cubicSourceSum,one_mul] using
    h N hN P hP (fun _ => 1) (fun _ _ => by norm_num)

end CubicMoment

namespace CubicSource
open CubicMoment

def cubicTuplePoint (n : Fin 4 → ℤ) : Fin 4 → ℝ :=
  ![(cubicFirst n:ℝ),(cubicSecond n:ℝ),(cubicThird n:ℝ),0]

def cubicSamplePoint (α β γ : ℝ) : Fin 4 → ℝ := ![α,β,γ,0]

theorem cubicSourceSum_fourth_four (N : ℕ) (z : ℤ → ℂ) (α β γ : ℝ) :
    (cubicSourceSum N z α β γ)^4=
      ∑ n∈cubicTupleSet N, cubicTupleCoefficient z n*
        fordAdditiveCharacter (∑ d, cubicTuplePoint n d*cubicSamplePoint α β γ d) := by
  rw [cubicSourceSum_fourth]
  unfold sargosPlanarSum
  apply Finset.sum_congr rfl
  intro n _hn
  rw [mul_assoc,←fordAdditiveCharacter_add]
  congr 2
  simp [cubicTuplePoint,cubicSamplePoint,Fin.sum_univ_succ]
  ring

theorem cubicSourceSum_fract (N : ℕ) (z : ℤ → ℂ) (α β γ : ℝ) :
    cubicSourceSum N z (Int.fract α) (Int.fract β) γ=cubicSourceSum N z α β γ := by
  unfold cubicSourceSum
  apply Finset.sum_congr rfl
  intro n _hn
  simp only [fordAdditiveCharacter_add]
  rw [sargos_character_integer_fract]
  have hs := sargos_character_integer_fract (n^2) β
  push_cast at hs
  rw [hs]

theorem cubic_sample_eighth_sieve {ι : Type*}
    (S : Finset ι) (N : ℕ) (z : ℤ → ℂ) (α β γ : ι → ℝ)
    {a c δ : Fin 4 → ℝ} (ha : ∀ d, 0 < a d) (hδ : ∀ d, 0 < δ d)
    (hz : ∀ n∈Finset.Icc (1:ℤ) N, ‖z n‖ ≤ 1)
    (hx : ∀ i∈S, ∀ d, cubicSamplePoint (α i) (β i) (γ i) d∈Icc (c d) (c d+δ d))
    (hu : ∀ n∈cubicTupleSet N, ∀ d, a d*|cubicTuplePoint n d| ≤ 1/2) :
    (∑ i∈S, ‖cubicSourceSum N z (α i) (β i) (γ i)‖)^8 ≤
      (S.card:ℝ)^6*(16777216*(∏ d, (δ d+2*a d))/(∏ d, a d))*
        (((S ×ˢ S).filter (fun ij => ∀ d,
          |cubicSamplePoint (α ij.1) (β ij.1) (γ ij.1) d-
            cubicSamplePoint (α ij.2) (β ij.2) (γ ij.2) d| ≤ 2*a d)).card:ℝ)*
        ((((cubicTupleSet N) ×ˢ (cubicTupleSet N)).filter (fun ij => ∀ d,
          |cubicTuplePoint ij.1 d-cubicTuplePoint ij.2 d| ≤ 1/(δ d+2*a d))).card:ℝ) := by
  classical
  let A := fun i => cubicSourceSum N z (α i) (β i) (γ i)
  have hs := bourgain_four_dimensional_double_large_sieve_sum_norm S (cubicTupleSet N)
    (cubicTupleCoefficient z) (fun i => cubicSamplePoint (α i) (β i) (γ i))
    cubicTuplePoint ha hδ (fun _ hn => cubicTupleCoefficient_norm hz hn) hx hu
  have he (i : ι) : ‖∑ n∈cubicTupleSet N, cubicTupleCoefficient z n*
      fordAdditiveCharacter (∑ d, cubicTuplePoint n d*cubicSamplePoint (α i) (β i) (γ i) d)‖=
      ‖A i‖^4 := by rw [←cubicSourceSum_fourth_four,norm_pow]
  simp_rw [he] at hs
  have hj := pow_sum_le_card_mul_sum_pow (s:=S)
    (f:=fun i => ‖A i‖) (fun _ _ => norm_nonneg _) 3
  have hsq := pow_le_pow_left₀
    (pow_nonneg (Finset.sum_nonneg (fun _ _ => norm_nonneg _)) 4) hj 2
  have hm := mul_le_mul_of_nonneg_left hs (pow_nonneg (Nat.cast_nonneg S.card) 6)
  calc
    _ = ((∑ i∈S, ‖A i‖)^4)^2 := by ring
    _ ≤ ((S.card:ℝ)^3*(∑ i∈S, ‖A i‖^4))^2 := hsq
    _ = (S.card:ℝ)^6*(∑ i∈S, ‖A i‖^4)^2 := by ring
    _ ≤ _ := hm.trans_eq (by ring)

theorem cubic_frequency_pairs_subset (N : ℕ) {a δ : Fin 4 → ℝ}
    (ha : ∀ d, 0 < a d)
    (hδ₀ : 2 ≤ δ 0) (hδ₁ : 2 ≤ δ 1) :
    (((cubicTupleSet N) ×ˢ (cubicTupleSet N)).filter (fun ij => ∀ d,
      |cubicTuplePoint ij.1 d-cubicTuplePoint ij.2 d| ≤ 1/(δ d+2*a d))) ⊆
      sargosNearPairs (cubicTupleSet N) (fun n => (cubicCombined N n:ℝ))
        (fun n => (cubicThird n:ℝ)) (1/2) (1/(δ 2+2*a 2)) := by
  intro p hp
  obtain ⟨hp,hnear⟩ := Finset.mem_filter.mp hp
  have htol (d : Fin 4) (hd : 2 ≤ δ d) : 1/(δ d+2*a d) ≤ (1/2:ℝ) := by
    apply one_div_le_one_div_of_le (by norm_num)
    linarith [ha d]
  have hfirst : cubicFirst p.1=cubicFirst p.2 :=
    int_eq_of_real_half_gap ((hnear 0).trans (htol 0 hδ₀))
  have hsecond : cubicSecond p.1=cubicSecond p.2 :=
    int_eq_of_real_half_gap ((hnear 1).trans (htol 1 hδ₁))
  have hcombined : cubicCombined N p.1=cubicCombined N p.2 := by
    simp only [cubicCombined,hfirst,hsecond]
  apply Finset.mem_filter.mpr
  refine ⟨hp,?_,hnear 2⟩
  simpa only [hcombined,sub_self,abs_zero] using (by norm_num : (0:ℝ) ≤ 1/2)

theorem exists_cubic_frequency_pair_bound {ε : ℝ} (hε : 0 < ε) :
    ∃ C > (0:ℝ), ∀ N : ℕ, 1 ≤ N → ∀ a δ : Fin 4 → ℝ,
      (∀ d, 0 < a d) → (∀ d, 0 < δ d) → 2 ≤ δ 0 → 2 ≤ δ 1 →
      ((((cubicTupleSet N) ×ˢ (cubicTupleSet N)).filter (fun ij => ∀ d,
        |cubicTuplePoint ij.1 d-cubicTuplePoint ij.2 d| ≤ 1/(δ d+2*a d))).card:ℝ) ≤
        C*((N:ℝ)^2+1/(δ 2+2*a 2))*(N:ℝ)^((2:ℝ)+ε) := by
  obtain ⟨C,hC,h⟩ := exists_cubic_combined_near_count hε
  refine ⟨C,hC,?_⟩
  intro N hN a δ ha hδ hδ₀ hδ₁
  have hc := Finset.card_le_card (cubic_frequency_pairs_subset N ha hδ₀ hδ₁)
  have hwidth : 0 < δ 2+2*a 2 := by linarith [hδ 2,ha 2]
  have hh := h N hN (1/(δ 2+2*a 2)) (by positivity)
  exact (show _ ≤ _ by exact_mod_cast hc).trans hh

theorem cubicTuple_power_abs {N : ℕ} {n : Fin 4 → ℤ}
    (hn : n∈cubicTupleSet N) (k : ℕ) :
    |∑r, (n r:ℝ)^k| ≤ 4*(N:ℝ)^k := by
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  have hb (r : Fin 4) : |(n r:ℝ)| ≤ (N:ℝ) := by
    exact_mod_cast cubicTuple_abs hn r
  have hh := Finset.sum_le_sum (s:=(Finset.univ:Finset (Fin 4)))
    (fun r _ => (show |(n r:ℝ)^k| ≤ (N:ℝ)^k by
      rw [abs_pow]
      exact pow_le_pow_left₀ (abs_nonneg _) (hb r) k))
  simpa using hh

def cubicSamplingScale (N : ℕ) : Fin 4 → ℝ :=
  ![1/(8*(N:ℝ)),1/(8*(N:ℝ)^2),1/(8*(N:ℝ)^3),1]

def cubicSamplingWidth (μ : ℝ) : Fin 4 → ℝ := ![2,2,μ,1]

theorem cubicSamplingScale_pos {N : ℕ} (hN : 1 ≤ N) (d : Fin 4) :
    0 < cubicSamplingScale N d := by
  have hN₀ : (0:ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  fin_cases d
  · change 0 < 1/(8*(N:ℝ))
    positivity
  · change 0 < 1/(8*(N:ℝ)^2)
    positivity
  · change 0 < 1/(8*(N:ℝ)^3)
    positivity
  · norm_num [cubicSamplingScale]

theorem cubicSamplingWidth_pos {μ : ℝ} (hμ : 0 < μ) (d : Fin 4) :
    0 < cubicSamplingWidth μ d := by
  fin_cases d <;> norm_num [cubicSamplingWidth]
  exact hμ

theorem cubicTuplePoint_scale {N : ℕ} (hN : 1 ≤ N)
    {n : Fin 4 → ℤ} (hn : n∈cubicTupleSet N) (d : Fin 4) :
    cubicSamplingScale N d*|cubicTuplePoint n d| ≤ 1/2 := by
  have hN₀ : (0:ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have h₁ : |(cubicFirst n:ℝ)| ≤ 4*(N:ℝ) := by
    simpa [cubicFirst] using cubicTuple_power_abs hn 1
  have h₂ : |(cubicSecond n:ℝ)| ≤ 4*(N:ℝ)^2 := by
    simpa [cubicSecond] using cubicTuple_power_abs hn 2
  have h₃ : |(cubicThird n:ℝ)| ≤ 4*(N:ℝ)^3 := by
    simpa [cubicThird] using cubicTuple_power_abs hn 3
  fin_cases d
  · change 1/(8*(N:ℝ))*|(cubicFirst n:ℝ)| ≤ 1/2
    rw [one_div_mul_eq_div]
    apply (div_le_iff₀ (by positivity)).mpr
    nlinarith
  · change 1/(8*(N:ℝ)^2)*|(cubicSecond n:ℝ)| ≤ 1/2
    rw [one_div_mul_eq_div]
    apply (div_le_iff₀ (by positivity)).mpr
    nlinarith
  · change 1/(8*(N:ℝ)^3)*|(cubicThird n:ℝ)| ≤ 1/2
    rw [one_div_mul_eq_div]
    apply (div_le_iff₀ (by positivity)).mpr
    nlinarith
  · norm_num [cubicSamplingScale,cubicTuplePoint]

theorem cubic_sampling_box_factor {N : ℕ} (hN : 1 ≤ N) {μ : ℝ} (hμ : 0 < μ) :
    ((∏ d, (cubicSamplingWidth μ d+2*cubicSamplingScale N d))/
      (∏ d, cubicSamplingScale N d)) ≤
      7776*(μ+1/(4*(N:ℝ)^3))*(N:ℝ)^6 := by
  have hN₁ : (1:ℝ) ≤ N := by exact_mod_cast hN
  have hN₀ : (0:ℝ) < N := by linarith
  have he : ((∏ d, (cubicSamplingWidth μ d+2*cubicSamplingScale N d))/
      (∏ d, cubicSamplingScale N d)) =
      (16*(N:ℝ)+2)*(16*(N:ℝ)^2+2)*(8*(μ+1/(4*(N:ℝ)^3))*(N:ℝ)^3)*3 := by
    simp only [cubicSamplingWidth,cubicSamplingScale,Fin.prod_univ_succ,
      Matrix.cons_val_zero,Matrix.cons_val_succ,Fin.prod_univ_zero,mul_one]
    field_simp
    ring
  rw [he]
  have h₁ : 16*(N:ℝ)+2 ≤ 18*(N:ℝ) := by linarith
  have h₂ : 16*(N:ℝ)^2+2 ≤ 18*(N:ℝ)^2 := by nlinarith
  have hh :
      (16*(N:ℝ)+2)*(16*(N:ℝ)^2+2)*(8*(μ+1/(4*(N:ℝ)^3))*(N:ℝ)^3)*3 ≤
      (18*(N:ℝ))*(18*(N:ℝ)^2)*(8*(μ+1/(4*(N:ℝ)^3))*(N:ℝ)^3)*3 := by
    gcongr
  exact hh.trans_eq (by ring)

theorem cubic_sampling_moment_factor {N : ℕ} (hN : 1 ≤ N) {μ ε : ℝ} (hμ : 0 < μ) :
    (μ+1/(4*(N:ℝ)^3))*(N:ℝ)^6*((N:ℝ)^2+1/(μ+1/(4*(N:ℝ)^3)))*
      (N:ℝ)^((2:ℝ)+ε) ≤ 2*(1+μ*(N:ℝ)^2)*(N:ℝ)^((8:ℝ)+ε) := by
  have hN₁ : (1:ℝ) ≤ N := by exact_mod_cast hN
  have hN₀ : (0:ℝ) < N := by linarith
  have hW : 0 < μ+1/(4*(N:ℝ)^3) := by positivity
  have he : (μ+1/(4*(N:ℝ)^3))*((N:ℝ)^2+1/(μ+1/(4*(N:ℝ)^3)))=
      1+μ*(N:ℝ)^2+1/(4*(N:ℝ)) := by field_simp; ring
  have hn : (N:ℝ)^6*(N:ℝ)^((2:ℝ)+ε)=(N:ℝ)^((8:ℝ)+ε) := by
    rw [←Real.rpow_natCast,←Real.rpow_add hN₀]
    congr 1
    ring
  have hsmall : 1/(4*(N:ℝ)) ≤ 1 := by
    apply (div_le_one (by positivity)).mpr
    linarith
  calc
    _ = ((μ+1/(4*(N:ℝ)^3))*((N:ℝ)^2+1/(μ+1/(4*(N:ℝ)^3))))*
        ((N:ℝ)^6*(N:ℝ)^((2:ℝ)+ε)) := by ring
    _ = (1+μ*(N:ℝ)^2+1/(4*(N:ℝ)))*(N:ℝ)^((8:ℝ)+ε) := by rw [he,hn]
    _ ≤ _ := mul_le_mul_of_nonneg_right (by nlinarith) (Real.rpow_nonneg (Nat.cast_nonneg N) _)

def cubicSamplePairs {ι : Type*} (S : Finset ι) (N : ℕ) (α β γ : ι → ℝ) :
    Finset (ι × ι) := by
  classical
  exact (S ×ˢ S).filter (fun ij => ∀ d,
    |cubicSamplePoint (α ij.1) (β ij.1) (γ ij.1) d-
      cubicSamplePoint (α ij.2) (β ij.2) (γ ij.2) d| ≤ 2*cubicSamplingScale N d)

theorem exists_cubic_sample_bound {ε : ℝ} (hε : 0 < ε) :
    ∃ C > (0:ℝ), ∀ (ι : Type) (S : Finset ι) (N : ℕ), 1 ≤ N →
      ∀ (z : ℤ → ℂ) (α β γ : ι → ℝ) (c μ : ℝ), 0 < μ →
      (∀ n∈Finset.Icc (1:ℤ) N, ‖z n‖ ≤ 1) →
      (∀ i∈S, α i∈Icc (0:ℝ) 1 ∧ β i∈Icc (0:ℝ) 1 ∧ γ i∈Icc c (c+μ)) →
      (∑ i∈S, ‖cubicSourceSum N z (α i) (β i) (γ i)‖)^8 ≤
        C*(S.card:ℝ)^6*(cubicSamplePairs S N α β γ).card*
          (1+μ*(N:ℝ)^2)*(N:ℝ)^((8:ℝ)+ε) := by
  obtain ⟨C,hC,hcount⟩ := exists_cubic_frequency_pair_bound hε
  refine ⟨16777216*15552*C,by positivity,?_⟩
  intro ι S N hN z α β γ c μ hμ hz hx
  let a := cubicSamplingScale N
  let δ := cubicSamplingWidth μ
  let W := μ+1/(4*(N:ℝ)^3)
  have hN₀ : (0:ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hW : 0 < W := by dsimp only [W]; positivity
  have ha : ∀ d, 0 < a d := cubicSamplingScale_pos hN
  have hδ : ∀ d, 0 < δ d := cubicSamplingWidth_pos hμ
  have hsource : ∀ i∈S, ∀ d,
      cubicSamplePoint (α i) (β i) (γ i) d∈Icc (![0,0,c,0] d) (![0,0,c,0] d+δ d) := by
    intro i hi d
    obtain ⟨hα,hβ,hγ⟩ := hx i hi
    fin_cases d
    · change α i∈Icc (0:ℝ) (0+2)
      exact ⟨hα.1,by linarith [hα.2]⟩
    · change β i∈Icc (0:ℝ) (0+2)
      exact ⟨hβ.1,by linarith [hβ.2]⟩
    · exact hγ
    · norm_num [cubicSamplePoint,δ,cubicSamplingWidth]
  have hs := cubic_sample_eighth_sieve S N z α β γ ha hδ hz hsource
    (fun _ hn d => cubicTuplePoint_scale hN hn d)
  have hwidth : δ 2+2*a 2=W := by
    change μ+2*(1/(8*(N:ℝ)^3))=μ+1/(4*(N:ℝ)^3)
    ring
  have hc := hcount N hN a δ ha hδ (by norm_num [δ,cubicSamplingWidth])
    (by norm_num [δ,cubicSamplingWidth])
  rw [hwidth] at hc
  have hf := cubic_sampling_box_factor hN hμ
  change (∏ d, (δ d+2*a d))/(∏ d, a d) ≤ 7776*W*(N:ℝ)^6 at hf
  have hf' : 16777216*(∏ d, (δ d+2*a d))/(∏ d, a d) ≤
      16777216*7776*W*(N:ℝ)^6 := by
    have hh := mul_le_mul_of_nonneg_left hf (by norm_num : (0:ℝ) ≤ 16777216)
    exact (by convert hh using 1 <;> ring)
  have hmain :
      (∑ i∈S, ‖cubicSourceSum N z (α i) (β i) (γ i)‖)^8 ≤
      (S.card:ℝ)^6*(16777216*7776*W*(N:ℝ)^6)*(cubicSamplePairs S N α β γ).card*
        (C*((N:ℝ)^2+1/W)*(N:ℝ)^((2:ℝ)+ε)) := by
    apply hs.trans
    change (S.card:ℝ)^6*(16777216*(∏ d, (δ d+2*a d))/(∏ d, a d))*
      (cubicSamplePairs S N α β γ).card*_ ≤ _
    gcongr
  have hm := cubic_sampling_moment_factor (ε:=ε) hN hμ
  change W*(N:ℝ)^6*((N:ℝ)^2+1/W)*(N:ℝ)^((2:ℝ)+ε) ≤ _ at hm
  calc
    _ ≤ _ := hmain
    _ = (16777216*7776*C)*(S.card:ℝ)^6*(cubicSamplePairs S N α β γ).card*
        (W*(N:ℝ)^6*((N:ℝ)^2+1/W)*(N:ℝ)^((2:ℝ)+ε)) := by ring
    _ ≤ (16777216*7776*C)*(S.card:ℝ)^6*(cubicSamplePairs S N α β γ).card*
        (2*(1+μ*(N:ℝ)^2)*(N:ℝ)^((8:ℝ)+ε)) :=
      mul_le_mul_of_nonneg_left hm (by positivity)
    _ = _ := by ring

theorem exists_cubic_sample_bound_fract {ε : ℝ} (hε : 0 < ε) :
    ∃ C > (0:ℝ), ∀ (ι : Type) (S : Finset ι) (N : ℕ), 1 ≤ N →
      ∀ (z : ℤ → ℂ) (α β γ : ι → ℝ) (c μ : ℝ), 0 < μ →
      (∀ n∈Finset.Icc (1:ℤ) N, ‖z n‖ ≤ 1) →
      (∀ i∈S, γ i∈Icc c (c+μ)) →
      (∑ i∈S, ‖cubicSourceSum N z (α i) (β i) (γ i)‖)^8 ≤
        C*(S.card:ℝ)^6*(cubicSamplePairs S N (fun i => Int.fract (α i))
          (fun i => Int.fract (β i)) γ).card*(1+μ*(N:ℝ)^2)*(N:ℝ)^((8:ℝ)+ε) := by
  obtain ⟨C,hC,h⟩ := exists_cubic_sample_bound hε
  refine ⟨C,hC,?_⟩
  intro ι S N hN z α β γ c μ hμ hz hγ
  have hh := h ι S N hN z (fun i => Int.fract (α i)) (fun i => Int.fract (β i)) γ c μ hμ hz
    (fun i hi => ⟨⟨Int.fract_nonneg _,(Int.fract_lt_one _).le⟩,
      ⟨Int.fract_nonneg _,(Int.fract_lt_one _).le⟩,hγ i hi⟩)
  simpa only [cubicSourceSum_fract] using hh

def cubicPrefixCoefficient (J : ℕ) (n : ℤ) : ℂ := if n ≤ J then 1 else 0

theorem cubicPrefixCoefficient_norm (J : ℕ) (n : ℤ) : ‖cubicPrefixCoefficient J n‖ ≤ 1 := by
  unfold cubicPrefixCoefficient
  split_ifs <;> norm_num

theorem cubicSourceSum_prefix {J N : ℕ} (hJN : J ≤ N) (α β γ : ℝ) :
    cubicSourceSum N (cubicPrefixCoefficient J) α β γ=
      ∑ j∈Finset.range J, fordAdditiveCharacter
        (γ*(1+(j:ℝ))^3+β*(1+(j:ℝ))^2+α*(1+(j:ℝ))) := by
  classical
  unfold cubicSourceSum cubicPrefixCoefficient
  simp only [ite_mul,one_mul,zero_mul,←Finset.sum_filter]
  have hset : (Finset.Icc (1:ℤ) N).filter (fun n => n ≤ (J:ℤ))=
      Finset.Ioc (0:ℤ) (0+(J:ℤ)) := by
    ext n
    simp only [Finset.mem_filter,Finset.mem_Icc,Finset.mem_Ioc]
    omega
  rw [hset]
  have ht := sargos_sum_Ioc_eq_range 0 J (fun n : ℤ =>
    fordAdditiveCharacter ((n:ℝ)*α+(n:ℝ)^2*β+(n:ℝ)^3*γ))
  simp only [Nat.cast_zero] at ht
  rw [ht]
  apply Finset.sum_congr rfl
  intro j _hj
  congr 1
  push_cast
  ring

/-- The existing common-prefix theorem consumes the actual C4 family.
Only the literal joint derivative near-pair count remains on the right. -/
theorem exists_C4_cubic_sample_bound {ε : ℝ} (hε : 0 < ε) :
    ∃ C > (0:ℝ), ∀ (ι : Type) (S : Finset ι) (f : ι → ℝ → ℝ)
      (m : ι → ℝ) (H : ℕ), 1 ≤ H → ∀ (B c μ : ℝ), 0 ≤ B → 0 < μ →
      B*((H:ℝ)+1)^4 ≤ 1 →
      (∀ i∈S, ∀ y∈Icc (m i-((H:ℝ)+1)) (m i+((H:ℝ)+1)), ContDiffAt ℝ 4 (f i) y) →
      (∀ i∈S, ∀ y∈Icc (m i-((H:ℝ)+1)) (m i+((H:ℝ)+1)), |iteratedDeriv 4 (f i) y| ≤ B) →
      (∀ i∈S, iteratedDeriv 3 (f i) (m i)/6∈Icc c (c+μ)) →
      (∑ i∈S, ‖∑ j∈Finset.range H,
        fordAdditiveCharacter (f i (m i+(1+(j:ℝ))))‖)^8 ≤
      C*(S.card:ℝ)^6*(cubicSamplePairs S H
        (fun i => Int.fract (deriv (f i) (m i)))
        (fun i => Int.fract (iteratedDeriv 2 (f i) (m i)/2))
        (fun i => iteratedDeriv 3 (f i) (m i)/6)).card*
        (1+μ*(H:ℝ)^2)*(H:ℝ)^((8:ℝ)+ε) := by
  obtain ⟨C,hC,h⟩ := exists_cubic_sample_bound_fract hε
  let K := 1+2*Real.pi
  have hK : 0 < K := by dsimp only [K]; positivity
  refine ⟨K^8*C,by positivity,?_⟩
  intro ι S f m H hH B c μ hB hμ hsmall hf hfour hγ
  let L := (H:ℝ)+1
  have hL : 0 ≤ L := by dsimp only [L]; positivity
  have hRange : ∀ x∈Icc (1:ℝ) (1+H), |x| ≤ L := by
    intro x hx
    rw [abs_of_nonneg (by linarith [hx.1] : 0 ≤ x)]
    dsimp only [L]
    linarith [hx.2]
  obtain ⟨J,hJ,hprefix⟩ := bourgain_cubic_taylor_common_prefix S f m
    (fun i => iteratedDeriv 2 (f i) (m i)/2) 1 H hL hB (le_refl (0:ℝ))
    hRange hf hfour (fun _ _ => by simp)
  have hcost : 1+2*Real.pi*H*(B*L^3+2*0*L) ≤ K := by
    have hHL : (H:ℝ) ≤ L := by dsimp only [L]; linarith
    have hm := mul_le_mul_of_nonneg_right hHL (show 0 ≤ B*L^3 by positivity)
    have hb : (H:ℝ)*(B*L^3) ≤ 1 := by
      change B*L^4 ≤ 1 at hsmall
      nlinarith
    dsimp only [K]
    nlinarith [Real.pi_pos]
  let A := fun i => cubicSourceSum H (cubicPrefixCoefficient J)
    (deriv (f i) (m i)) (iteratedDeriv 2 (f i) (m i)/2) (iteratedDeriv 3 (f i) (m i)/6)
  have he (i : ι) : (∑ j∈Finset.range J,
      (𝐞 ((iteratedDeriv 3 (f i) (m i)/6)*(1+(j:ℝ))^3+
        (iteratedDeriv 2 (f i) (m i)/2)*(1+(j:ℝ))^2+
          deriv (f i) (m i)*(1+(j:ℝ))) : ℂ))=A i := by
    dsimp only [A]
    rw [cubicSourceSum_prefix hJ]
    simp only [sargos_ford_character_eq_fourier]
  have hsource : (∑ i∈S, ‖∑ j∈Finset.range H,
      fordAdditiveCharacter (f i (m i+(1+(j:ℝ))))‖) ≤ K*∑ i∈S, ‖A i‖ := by
    simp_rw [he] at hprefix
    simp only [←sargos_ford_character_eq_fourier] at hprefix
    exact hprefix.trans (mul_le_mul_of_nonneg_right hcost (Finset.sum_nonneg (fun _ _ => norm_nonneg _)))
  have hs := h ι S H hH (cubicPrefixCoefficient J)
    (fun i => deriv (f i) (m i)) (fun i => iteratedDeriv 2 (f i) (m i)/2)
    (fun i => iteratedDeriv 3 (f i) (m i)/6) c μ hμ
    (fun n _hn => cubicPrefixCoefficient_norm J n) hγ
  have hp := pow_le_pow_left₀ (Finset.sum_nonneg (fun _ _ => norm_nonneg _)) hsource 8
  rw [mul_pow] at hp
  apply hp.trans
  have hh := mul_le_mul_of_nonneg_left hs (pow_nonneg hK.le 8)
  exact hh.trans_eq (by ring)

theorem norm_range_sum_shift_sub (w : ℕ → ℂ) (M n : ℕ)
    (hw : ∀ k, ‖w k‖ ≤ 1) :
    ‖(∑ m∈Finset.range M, w m)-(∑ m∈Finset.range M, w (n+m))‖ ≤ 2*(n:ℝ) := by
  have h₁ := Finset.sum_range_add w M n
  have h₂ := Finset.sum_range_add w n M
  rw [Nat.add_comm n M] at h₂
  have he : (∑ m∈Finset.range M, w m)-(∑ m∈Finset.range M, w (n+m))=
      (∑ k∈Finset.range n, w k)-(∑ k∈Finset.range n, w (M+k)) := by
    linear_combination h₂-h₁
  have hb (b : ℕ) : ‖∑ k∈Finset.range n, w (b+k)‖ ≤ (n:ℝ) := by
    apply (norm_sum_le _ _).trans
    have hh := Finset.sum_le_sum (s:=Finset.range n) (fun k _ => hw (b+k))
    simpa using hh
  rw [he]
  have hzero := hb 0
  simp only [zero_add] at hzero
  exact (norm_sub_le _ _).trans (by linarith [hb M])

theorem source_shift_average_norm (w : ℕ → ℂ) (M H : ℕ)
    (hw : ∀ k, ‖w k‖ ≤ 1) :
    (H:ℝ)*‖∑ m∈Finset.range M, w m‖ ≤
      (∑ m∈Finset.range M, ‖∑ j∈Finset.range H, w (m+(j+1))‖)+2*(H:ℝ)^2 := by
  let A := ∑ m∈Finset.range M, w m
  let Z := ∑ j∈Finset.range H, ∑ m∈Finset.range M, w ((j+1)+m)
  have he : (H:ℂ)*A-Z=
      ∑ j∈Finset.range H, (A-∑ m∈Finset.range M, w ((j+1)+m)) := by
    simp only [Finset.sum_sub_distrib,Finset.sum_const,Finset.card_range,nsmul_eq_mul,Z]
  have herr : ‖(H:ℂ)*A-Z‖ ≤ 2*(H:ℝ)^2 := by
    rw [he]
    apply (norm_sum_le _ _).trans
    have hb : (∑ j∈Finset.range H, ‖A-∑ m∈Finset.range M, w ((j+1)+m)‖) ≤
        ∑ _j∈Finset.range H, 2*(H:ℝ) := by
      apply Finset.sum_le_sum
      intro j hj
      have hh := norm_range_sum_shift_sub w M (j+1) hw
      have hjH : ((j+1:ℕ):ℝ) ≤ H := by exact_mod_cast (Finset.mem_range.mp hj)
      exact hh.trans (by linarith)
    simpa [pow_two,mul_left_comm] using hb
  have hz : ‖Z‖ ≤ ∑ m∈Finset.range M, ‖∑ j∈Finset.range H, w (m+(j+1))‖ := by
    dsimp only [Z]
    rw [Finset.sum_comm]
    simpa only [Nat.add_comm] using norm_sum_le (Finset.range M)
      (fun m => ∑ j∈Finset.range H, w ((j+1)+m))
  have ht := (norm_sub_le ((H:ℂ)*A-Z) (-Z)).trans (add_le_add herr (by simpa using hz))
  simp only [sub_neg_eq_add,sub_add_cancel,norm_mul,Complex.norm_natCast] at ht
  change (H:ℝ)*‖A‖ ≤ _
  linarith

def cubicDerivativePairs (f : ℝ → ℝ) (M H : ℕ) : Finset (ℕ × ℕ) :=
  cubicSamplePairs (Finset.range M) H
    (fun m => Int.fract (deriv f ((m:ℝ)+1)))
    (fun m => Int.fract (iteratedDeriv 2 f ((m:ℝ)+1)/2))
    (fun m => iteratedDeriv 3 f ((m:ℝ)+1)/6)

/-- The literal original C4 sum, with averaging endpoints and every scale
retained. The unresolved arithmetic input is its actual derivative-pair count. -/
theorem exists_C4_source_eighth_reduction {ε : ℝ} (hε : 0 < ε) :
    ∃ C > (0:ℝ), ∀ (f : ℝ → ℝ) (M H : ℕ), 1 ≤ H →
      ∀ B c μ : ℝ, 0 ≤ B → 0 < μ → B*((H:ℝ)+1)^4 ≤ 1 →
      (∀ m∈Finset.range M, ∀ y∈Icc ((m:ℝ)-H) ((m:ℝ)+H+2), ContDiffAt ℝ 4 f y) →
      (∀ m∈Finset.range M, ∀ y∈Icc ((m:ℝ)-H) ((m:ℝ)+H+2), |iteratedDeriv 4 f y| ≤ B) →
      (∀ m∈Finset.range M, iteratedDeriv 3 f ((m:ℝ)+1)/6∈Icc c (c+μ)) →
      ‖∑ m∈Finset.range M, fordAdditiveCharacter (f ((m:ℝ)+1))‖^8 ≤
        C*((M:ℝ)^6*(cubicDerivativePairs f M H).card*(1+μ*(H:ℝ)^2)*(H:ℝ)^ε+(H:ℝ)^8) := by
  obtain ⟨C,hC,hfamily⟩ := exists_C4_cubic_sample_bound hε
  refine ⟨128*C+32768,by positivity,?_⟩
  intro f M H hH B c μ hB hμ hsmall hf hfour hγ
  have hH₀ : (0:ℝ) < H := by exact_mod_cast (show 0 < H by omega)
  let A := ‖∑ m∈Finset.range M, fordAdditiveCharacter (f ((m:ℝ)+1))‖
  let F := ∑ m∈Finset.range M, ‖∑ j∈Finset.range H,
    fordAdditiveCharacter (f ((m:ℝ)+1+(1+(j:ℝ))))‖
  let R := (M:ℝ)^6*(cubicDerivativePairs f M H).card*(1+μ*(H:ℝ)^2)*(H:ℝ)^ε
  have hR : 0 ≤ R := by dsimp only [R]; positivity
  have hF : 0 ≤ F := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  have hshift : (H:ℝ)*A ≤ F+2*(H:ℝ)^2 := by
    have hh := source_shift_average_norm
      (fun n => fordAdditiveCharacter (f ((n:ℝ)+1))) M H
      (fun _ => le_of_eq (sargos_character_norm _))
    have he (m j : ℕ) : (((m+(j+1):ℕ):ℝ)+1)=(m:ℝ)+1+(1+(j:ℝ)) := by push_cast; ring
    simpa only [he] using hh
  have hseg (m : ℕ) (y : ℝ)
      (hy : y∈Icc ((m:ℝ)+1-((H:ℝ)+1)) ((m:ℝ)+1+((H:ℝ)+1))) :
      y∈Icc ((m:ℝ)-H) ((m:ℝ)+H+2) := by
    constructor <;> linarith [hy.1,hy.2]
  have hh := hfamily ℕ (Finset.range M) (fun _ => f) (fun m => (m:ℝ)+1)
    H hH B c μ hB hμ hsmall
    (fun m hm y hy => hf m hm y (hseg m y hy))
    (fun m hm y hy => hfour m hm y (hseg m y hy)) hγ
  have he : (H:ℝ)^((8:ℝ)+ε)=(H:ℝ)^8*(H:ℝ)^ε := by
    rw [Real.rpow_add hH₀]
    norm_num
  have hmain : F^8 ≤ C*(H:ℝ)^8*R := by
    simp only [Finset.card_range] at hh
    change F^8 ≤ C*(M:ℝ)^6*(cubicDerivativePairs f M H).card*
      (1+μ*(H:ℝ)^2)*(H:ℝ)^((8:ℝ)+ε) at hh
    rw [he] at hh
    exact hh.trans_eq (by dsimp only [R]; ring)
  have hp := pow_le_pow_left₀ (mul_nonneg hH₀.le (norm_nonneg _)) hshift 8
  have ha := add_pow_le hF (show 0 ≤ 2*(H:ℝ)^2 by positivity) 8
  have hall : (H:ℝ)^8*A^8 ≤ 128*(C*(H:ℝ)^8*R+(2*(H:ℝ)^2)^8) := by
    rw [mul_pow] at hp
    apply hp.trans (ha.trans ?_)
    norm_num only at ⊢
    gcongr
  have hbound : A^8 ≤ 128*C*R+32768*(H:ℝ)^8 := by
    apply (mul_le_mul_iff_right₀ (show 0 < (H:ℝ)^8 by positivity)).mp
    exact hall.trans_eq (by ring)
  change A^8 ≤ (128*C+32768)*(R+(H:ℝ)^8)
  apply hbound.trans
  nlinarith [mul_nonneg hC.le (pow_nonneg hH₀.le 8)]

end CubicSource

end TaoTrudgianYang2025.SquareProductCount


namespace TaoTrudgianYang2025.CubicJointCount

open Set MeasureTheory Expdb Filter GafniTao
open SquareProductCount.CubicSource
open scoped Topology ContDiff BigOperators NNReal

/-! The actual original-source joint derivative count. The analytic chain
uses the existing double Legendre extension, exponent-pair estimate and
Fourier kernel. Both finite chart covers, every integer level and source
multiplicity, short displacements, the freely chosen Fourier width and
dyadic recombination are proved. The endpoint consumes the literal pair
set of `CubicSource.exists_C4_source_eighth_reduction`. Source trimming
and D-process scale/epsilon assembly remain separate obligations. -/

theorem negative_first_derivative_model
    {σ δ : ℝ} {P : ℕ} {F : ℝ → ℝ} (hσ : 0 < σ)
    (hF : IsApproximateModelPhaseFunction F σ (P+1) δ) :
    IsApproximateModelPhaseFunction
      (fun u => -σ⁻¹*iteratedDerivWithin 1 F phaseInterval u)
      (σ+1) P (δ/σ) := by
  refine ⟨contDiffOn_const.mul
    (sargos_contDiffOn_iteratedDerivWithin hF.1 uniqueDiffOn_phaseInterval 1),?_⟩
  intro p hp u
  have hu : 0 < (u:ℝ) := lt_of_lt_of_le zero_lt_one u.property.1
  have hw (τ : ℝ) (n : ℕ) :
      iteratedDerivWithin n (modelPhase τ) phaseInterval u =
        iteratedDeriv n (modelPhase τ) u :=
    iteratedDerivWithin_eq_iteratedDeriv uniqueDiffOn_phaseInterval
      (Real.contDiffAt_rpow_const_of_ne hu.ne') u.property
  have hm : -σ⁻¹*iteratedDerivWithin (p+1) (modelPhase σ) phaseInterval u =
      iteratedDerivWithin p (modelPhase (σ+1)) phaseInterval u := by
    rw [hw,hw,modelPhase_iteratedDeriv_succ_parameter σ hu]
    field_simp
  have he : modelPhaseErrorAt
      (fun u => -σ⁻¹*iteratedDerivWithin 1 F phaseInterval u) (σ+1) p u =
      -σ⁻¹*modelPhaseErrorAt F σ (p+1) u := by
    rw [modelPhaseErrorAt,iteratedDerivWithin_const_mul_field,
      sargos_iteratedDerivWithin_comp_order,← hm,← mul_sub]
    rfl
  rw [he,norm_mul,Real.norm_eq_abs,abs_neg,
    abs_of_pos (inv_pos.mpr hσ)]
  have h := mul_le_mul_of_nonneg_left (hF.2 (p+1) (by omega) u)
    (inv_nonneg.mpr hσ.le)
  simpa only [div_eq_mul_inv,mul_comm] using h

theorem inverse_slope_shift_stationary_identity
    {σ δ k u : ℝ} {F : ℝ → ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hF : IsApproximateModelPhaseFunction F σ 1 δ)
    (hu : u∈modelPhaseSlopeRange F) (huk : u+k∈modelPhaseSlopeRange F) :
    let c := modelPhaseInverseSlope F
    let K := fun v => modelPhaseLegendreDual F v-modelPhaseLegendreDual F (v+k)
    let d := c u-c (u+k)
    HasDerivAt K d u ∧
      2*(F (c (u+k))-F (c u)-k*c (u+k)) = -2*(d*u-K u) := by
  intro c K d
  have hleft := modelPhaseLegendreDual_hasDerivAt hσ hδ hF hu
  have hright := (modelPhaseLegendreDual_hasDerivAt hσ hδ hF huk).comp u
    ((hasDerivAt_id u).add_const k)
  refine ⟨?_,?_⟩
  · simpa only [mul_one] using hleft.sub hright
  · dsimp only [c,K,d,modelPhaseLegendreDual]
    ring

theorem double_dual_physical_scales
    {P V A B τ θ η : ℝ} (hP : 0 < P) (hV : 0 < V)
    (hA : 0 < A) (hB : 0 < B) (hτ : 0 < τ) (hη : 0 < η) (hηone : η < 1) :
    let s := A^(τ-1)/(τ*η)
    let M := B*P/(s*A*(1-η))
    let H := 2*V/(s*B^(θ-1))
    let K := V*A*η/P
    0 < M ∧ 0 < H ∧ 0 < K ∧
      H/M=(2*V/P)*A*(1-η)*B^(-θ) ∧
      M=(B*τ/(A^(τ+1)*(1-η)))*(P^2/V)*K ∧
      ∀ d:ℝ, (s*A*(1-η)*(d/P))/B=d/M ∧
        2*V*(A*η)*(d/P)=2*K*d := by
  intro s M H K
  have hs : 0 < s := by dsimp [s]; positivity
  have h1 : 0 < 1-η := by linarith
  have hM : 0 < M := by dsimp [M]; positivity
  have hH : 0 < H := by dsimp [H]; positivity
  have hK : 0 < K := by dsimp [K]; positivity
  have hE : B^(θ-1)*B=B^θ := by
    calc
      _ = B^(θ-1)*B^(1:ℝ) := by rw [Real.rpow_one]
      _ = B^((θ-1)+1) := (Real.rpow_add hB _ _).symm
      _ = _ := by congr 1; ring
  have hAexp : A^(τ-1)*A^2=A^(τ+1) := by
    calc
      _ = A^(τ-1)*A^(2:ℝ) := by rw [Real.rpow_two]
      _ = A^((τ-1)+2) := (Real.rpow_add hA _ _).symm
      _ = _ := by congr 1; ring
  refine ⟨hM,hH,hK,?_,?_,?_⟩
  · rw [Real.rpow_neg hB.le]
    dsimp [H,M]
    field_simp
    nlinarith only [hE]
  · rw [← hAexp]
    dsimp [M,K,s]
    field_simp
  · intro d
    dsimp [M,K]
    constructor <;> field_simp

theorem finite_slope_values_retained
    {ι : Type*} (S : Finset ι) {lo hi : ℝ} (hlohi : lo < hi)
    (v : ι → ℝ) (hv : ∀ i∈S, v i ∈ Ioo lo hi) :
    ∃ h : ℝ, 0 < h ∧ h ≤ 1 ∧ lo+4*h < hi ∧
      ∀ i∈S, v i ∈ Icc (lo+2*h) (hi-2*h) := by
  classical
  let t := S.image (fun i => min (v i-lo) (hi-v i))
  let b := min 1 (hi-lo)
  have hb : 0 < b := lt_min zero_lt_one (sub_pos.mpr hlohi)
  let m := (insert b t).min' (Finset.insert_nonempty b t)
  have hm : 0 < m := by
    have hx : m ∈ insert b t := Finset.min'_mem _ _
    rcases Finset.mem_insert.mp hx with hx | hx
    · rw [hx]
      exact hb
    · obtain ⟨i,hiS,he⟩ := Finset.mem_image.mp hx
      rw [← he]
      exact lt_min (sub_pos.mpr (hv i hiS).1) (sub_pos.mpr (hv i hiS).2)
  have hmb : m ≤ b := Finset.min'_le _ _ (Finset.mem_insert_self _ _)
  have hm₁ : m ≤ 1 := hmb.trans (min_le_left _ _)
  have hmspan : m ≤ hi-lo := hmb.trans (min_le_right _ _)
  refine ⟨m/8,by positivity,by linarith,by linarith,?_⟩
  intro i hiS
  have hmi : m ≤ min (v i-lo) (hi-v i) :=
    Finset.min'_le _ _ (Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨i,hiS,rfl⟩))
  have hl := hmi.trans (min_le_left _ _)
  have hr := hmi.trans (min_le_right _ _)
  constructor <;> linarith

theorem moving_legendre_hasDerivAt
    {σ δ A a v h : ℝ} {F : ℝ → ℝ} (Q : ℕ)
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hF : IsApproximateModelPhaseFunction F σ 1 δ)
    (hA : 0 < A) (ha : 0 < a) (hv : 0 < v) (hh : 0 < h)
    (hret : v ∈ Ioo (modelPhaseClosedSlope F 2+2*h)
      (modelPhaseClosedSlope F 1-2*h)) :
    HasDerivAt (canonicalTaylorLegendrePhase F σ A Q a h)
      (A^(σ⁻¹-1)*modelPhaseInverseSlope F v*A) (v/A) := by
  have hvwin : v ∈ modelPhaseSlopeRange F := by
    rw [modelPhaseSlopeRange_eq_endpoint_Ioo hσ hδ hF]
    constructor <;> linarith [hret.1,hret.2]
  have he : canonicalTaylorLegendrePhase F σ A Q a h =ᶠ[𝓝 (v/A)]
      fun x => A^(σ⁻¹-1)*(modelPhaseLegendreDual F (A*x)-modelPhaseLegendreDual F a)+
        referenceModelPrimitive σ⁻¹ (a/A) := by
    have hc : ContinuousAt (fun x:ℝ => A*x) (v/A) := by fun_prop
    have hn : Ioo (max 0 (modelPhaseClosedSlope F 2+2*h))
        (modelPhaseClosedSlope F 1-2*h) ∈ 𝓝 (A*(v/A)) := by
      rw [mul_div_cancel₀ _ hA.ne']
      exact isOpen_Ioo.mem_nhds ⟨max_lt hv hret.1,hret.2⟩
    filter_upwards [hc.preimage_mem_nhds hn] with x hx
    have hpos : 0 < A*x := lt_of_le_of_lt (le_max_left _ _) hx.1
    have hlow := lt_of_le_of_lt (le_max_right _ _) hx.1
    have hval := canonicalTaylorLegendrePhase_agrees (σ:=σ) Q hA ha hpos hh
      ⟨hlow.le,hx.2.le⟩
    simpa only [mul_div_cancel_left₀ _ hA.ne'] using hval
  have hd₀ : HasDerivAt (modelPhaseLegendreDual F) (modelPhaseInverseSlope F v)
      (A*(v/A)) := by
    simpa only [mul_div_cancel₀ _ hA.ne'] using
      modelPhaseLegendreDual_hasDerivAt hσ hδ hF hvwin
  have hd := hd₀.comp (v/A) ((hasDerivAt_id (v/A)).const_mul A)
  simp only [mul_one] at hd
  convert (((hd.sub_const (modelPhaseLegendreDual F a)).const_mul
    (A^(σ⁻¹-1))).add_const (referenceModelPrimitive σ⁻¹ (a/A))).congr_of_eventuallyEq
      he using 1
  ring

theorem moving_shift_displacement
    {σ δ A a h η y : ℝ} {F : ℝ → ℝ} (Q : ℕ)
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hF : IsApproximateModelPhaseFunction F σ 1 δ)
    (hA : 0 < A) (ha : 0 < a) (hh : 0 < h)
    (hu : 0 < A*aProcessShiftPoint η 0 y)
    (huk : 0 < A*aProcessShiftPoint η 1 y)
    (hret₀ : A*aProcessShiftPoint η 0 y ∈
      Ioo (modelPhaseClosedSlope F 2+2*h) (modelPhaseClosedSlope F 1-2*h))
    (hret₁ : A*aProcessShiftPoint η 1 y ∈
      Ioo (modelPhaseClosedSlope F 2+2*h) (modelPhaseClosedSlope F 1-2*h)) :
    let u := A*aProcessShiftPoint η 0 y
    let k := A*η
    let d := modelPhaseInverseSlope F u-modelPhaseInverseSlope F (u+k)
    let s := A^(σ⁻¹-1)/(σ⁻¹*η)
    let J := aProcessShiftPhase (canonicalTaylorLegendrePhase F σ A Q a h) σ⁻¹ η
    J y=s*(modelPhaseLegendreDual F u-modelPhaseLegendreDual F (u+k)) ∧
      HasDerivAt J (s*A*(1-η)*d) y := by
  intro u k d s J
  have hcoords : A*aProcessShiftPoint η 1 y = u+k := by
    dsimp [u,k,aProcessShiftPoint]
    ring
  have h0 := canonicalTaylorLegendrePhase_agrees (σ:=σ) Q hA ha hu hh
    ⟨hret₀.1.le,hret₀.2.le⟩
  have h1 := canonicalTaylorLegendrePhase_agrees (σ:=σ) Q hA ha huk hh
    ⟨hret₁.1.le,hret₁.2.le⟩
  simp only [mul_div_cancel_left₀ _ hA.ne'] at h0 h1
  constructor
  · dsimp only [J,aProcessShiftPhase]
    rw [h0,h1,hcoords]
    dsimp [s,u]
    ring
  · have hd (t:ℝ) (ht:0 < A*aProcessShiftPoint η t y)
        (hr:A*aProcessShiftPoint η t y ∈
          Ioo (modelPhaseClosedSlope F 2+2*h) (modelPhaseClosedSlope F 1-2*h)) :
        HasDerivAt
          (fun x => canonicalTaylorLegendrePhase F σ A Q a h (aProcessShiftPoint η t x))
          (A^(σ⁻¹-1)*modelPhaseInverseSlope F (A*aProcessShiftPoint η t y)*A*(1-η)) y := by
      have hv := moving_legendre_hasDerivAt Q hσ hδ hF hA ha ht hh hr
      rw [mul_div_cancel_left₀ _ hA.ne'] at hv
      convert hv.comp y
        (((hasDerivAt_id y).const_mul (1-η)).add_const ((1+t)*η)) using 1
      simp
    have hj := ((hd 0 hu hret₀).sub (hd 1 huk hret₁)).div_const (σ⁻¹*η)
    rw [hcoords] at hj
    convert hj using 1
    dsimp [J,aProcessShiftPhase,aProcessShiftPoint,s,d,u]
    ring

theorem moving_double_dual_resonance
    {σ δ δJ A B a c h g η y : ℝ} {F : ℝ → ℝ} (Q₁ Q₂ : ℕ)
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hδJ : δJ ≤ min (modelPhaseCurvatureLower (σ⁻¹+1)) 1)
    (hF : IsApproximateModelPhaseFunction F σ 1 δ)
    (hA : 0 < A) (hB : 0 < B) (ha : 0 < a) (hc : 0 < c)
    (hh : 0 < h) (hg : 0 < g) (hy : y ∈ Ioo (1:ℝ) 2)
    (hu : 0 < A*aProcessShiftPoint η 0 y)
    (huk : 0 < A*aProcessShiftPoint η 1 y)
    (hret₀ : A*aProcessShiftPoint η 0 y ∈
      Ioo (modelPhaseClosedSlope F 2+2*h) (modelPhaseClosedSlope F 1-2*h))
    (hret₁ : A*aProcessShiftPoint η 1 y ∈
      Ioo (modelPhaseClosedSlope F 2+2*h) (modelPhaseClosedSlope F 1-2*h)) :
    let u := A*aProcessShiftPoint η 0 y
    let k := A*η
    let d := modelPhaseInverseSlope F u-modelPhaseInverseSlope F (u+k)
    let s := A^(σ⁻¹-1)/(σ⁻¹*η)
    let J := aProcessShiftPhase (canonicalTaylorLegendrePhase F σ A Q₁ a h) σ⁻¹ η
    let w := s*A*(1-η)*d
    let R := 2*(F (modelPhaseInverseSlope F (u+k))-F (modelPhaseInverseSlope F u)-
      k*modelPhaseInverseSlope F (u+k))
    IsApproximateModelPhaseFunction J (σ⁻¹+1) 1 δJ → 0 < w →
      w ∈ Icc (modelPhaseClosedSlope J 2+2*g) (modelPhaseClosedSlope J 1-2*g) →
      canonicalTaylorLegendrePhase J (σ⁻¹+1) B Q₂ c g (w/B) =
        B^((σ⁻¹+1)⁻¹-1)*(-s/2*R-s*k*d-modelPhaseLegendreDual J c)+
          referenceModelPrimitive (σ⁻¹+1)⁻¹ (c/B) := by
  intro u k d s J w R hJ hw hwret
  have hcoords : A*aProcessShiftPoint η 1 y=u+k := by
    dsimp [u,k,aProcessShiftPoint]
    ring
  obtain ⟨hval,hderiv⟩ := moving_shift_displacement Q₁ hσ hδ hF hA ha hh
    hu huk hret₀ hret₁
  change J y=s*(modelPhaseLegendreDual F u-modelPhaseLegendreDual F (u+k)) at hval
  change HasDerivAt J w y at hderiv
  have hinv : modelPhaseInverseSlope J w=y := by
    rw [← hderiv.deriv]
    exact modelPhaseInverseSlope_deriv (by positivity) hδJ hJ hy
  have huwin : u ∈ modelPhaseSlopeRange F := by
    rw [modelPhaseSlopeRange_eq_endpoint_Ioo hσ hδ hF]
    constructor <;> linarith [hret₀.1,hret₀.2]
  have hukwin : u+k ∈ modelPhaseSlopeRange F := by
    rw [← hcoords,modelPhaseSlopeRange_eq_endpoint_Ioo hσ hδ hF]
    constructor <;> linarith [hret₁.1,hret₁.2]
  have hR := (inverse_slope_shift_stationary_identity hσ hδ hF huwin hukwin).2
  change R = -2*(d*u-(modelPhaseLegendreDual F u-modelPhaseLegendreDual F (u+k))) at hR
  have hdual : modelPhaseLegendreDual J w = -s/2*R-s*k*d := by
    rw [modelPhaseLegendreDual,hinv,hval,hR]
    dsimp [w,u,k,aProcessShiftPoint]
    ring
  rw [canonicalTaylorLegendrePhase_agrees Q₂ hB hc hw hg hwret,hdual]

theorem finite_moving_double_dual_realization
    {σ A B : ℝ} (hσ : 0 < σ) (hA : 0 < A) (hA₂ : A ≤ 2)
    (hB : 0 < B) (hB₂ : B ≤ 2) (Q : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ η₀ : ℝ, 0 < δ ∧ 0 < η₀ ∧ η₀ ≤ 1/2 ∧
      ∃ P Q₁ : ℕ, 1 ≤ P ∧
        ∀ (F : ℝ → ℝ) (η : ℝ), IsApproximateModelPhaseFunction F σ P δ →
          0 < η → η ≤ η₀ → ∀ (ι : Type*) (S : Finset ι) (y : ι → ℝ),
          (∀ i∈S, y i ∈ Ioo (1:ℝ) 2) →
          (∀ i∈S, A*aProcessShiftPoint η 0 (y i) ∈ modelPhaseSlopeRange F) →
          (∀ i∈S, A*aProcessShiftPoint η 1 (y i) ∈ modelPhaseSlopeRange F) →
          let u := fun i => A*aProcessShiftPoint η 0 (y i)
          let k := A*η
          let d := fun i => modelPhaseInverseSlope F (u i)-modelPhaseInverseSlope F (u i+k)
          let s := A^(σ⁻¹-1)/(σ⁻¹*η)
          let R := fun i => 2*(F (modelPhaseInverseSlope F (u i+k))-
            F (modelPhaseInverseSlope F (u i))-k*modelPhaseInverseSlope F (u i+k))
          ∃ h g : ℝ, 0 < h ∧ h ≤ 1 ∧ 0 < g ∧ g ≤ 1 ∧
            let L := canonicalTaylorLegendrePhase F σ A Q₁ (deriv F (3/2)) h
            let J := aProcessShiftPhase L σ⁻¹ η
            let c := deriv J (3/2)
            let G := canonicalTaylorLegendrePhase J (σ⁻¹+1) B Q c g
            IsApproximateModelPhaseFunction G (σ⁻¹+1)⁻¹ Q ε ∧
              (∀ i∈S, s*A*(1-η)*d i∈Icc ((2:ℝ)^(-(σ⁻¹+1))/2) 2) ∧
              ∀ i∈S, G (s*A*(1-η)*d i/B) =
                B^((σ⁻¹+1)⁻¹-1)*(-s/2*R i-s*k*d i-modelPhaseLegendreDual J c)+
                  referenceModelPrimitive (σ⁻¹+1)⁻¹ (c/B) := by
  classical
  have hτ : 0 < σ⁻¹+1 := by positivity
  obtain ⟨δ₂,hδ₂,hsmall₂,hpos₂,hsecond⟩ :=
    canonicalTaylorLegendrePhase_uniformity hτ hB hB₂ Q hε
  let QJ := max 1 (legendreFiniteInputOrder (Q+2))
  obtain ⟨δ₁,η₀,hδ₁,hη₀,hηhalf,hshift⟩ :=
    aProcessShiftPhase_uniform_model (inv_pos.mpr hσ) QJ hδ₂
  obtain ⟨δ,hδ,hsmall,hpos,hfirst⟩ :=
    canonicalTaylorLegendrePhase_uniformity hσ hA hA₂ (QJ+1) hδ₁
  let P := max 1 (legendreFiniteInputOrder ((QJ+1)+2))
  refine ⟨δ,η₀,hδ,hη₀,hηhalf,P,QJ+1,le_max_left _ _,?_⟩
  intro F η hF hη hηle ι S y hy hu huk u k d s R
  have hF₁ := approximateModelPhase_mono hF (le_max_left _ _) le_rfl
  have hFQ := approximateModelPhase_mono hF (le_max_right _ _) le_rfl
  have hwin := modelPhaseSlopeRange_eq_endpoint_Ioo hσ hsmall hF₁
  have hpositive {v:ℝ} (hv:v∈modelPhaseSlopeRange F) : 0 < v :=
    lt_of_lt_of_le (by positivity : (0:ℝ) < (2:ℝ)^(-σ)/2)
      (modelPhaseSlopeRange_positive_window hσ hpos hF hv).1
  have ha : deriv F (3/2) ∈ modelPhaseSlopeRange F := ⟨3/2,by norm_num,rfl⟩
  have hai := ha
  rw [hwin] at hai
  let U := S.image u ∪ S.image (fun i => A*aProcessShiftPoint η 1 (y i))
  have hU : ∀ v∈U, v ∈ Ioo (modelPhaseClosedSlope F 2) (modelPhaseClosedSlope F 1) := by
    intro v hv
    rcases Finset.mem_union.mp hv with hv | hv
    · obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hv
      simpa only [hwin] using hu i hi
    · obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hv
      simpa only [hwin] using huk i hi
  obtain ⟨b,hb,hb₁,hgap,hvalues⟩ := finite_slope_values_retained U
    (lt_trans hai.1 hai.2) id hU
  have hh : 0 < b/2 := by positivity
  have hh₁ : b/2 ≤ 1 := by linarith
  have hhgap : modelPhaseClosedSlope F 2+4*(b/2) < modelPhaseClosedSlope F 1 := by
    linarith
  have hret₀ (i:ι) (hi:i∈S) : A*aProcessShiftPoint η 0 (y i) ∈
      Ioo (modelPhaseClosedSlope F 2+2*(b/2)) (modelPhaseClosedSlope F 1-2*(b/2)) := by
    have hv := hvalues (u i) (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨i,hi,rfl⟩))
    change modelPhaseClosedSlope F 2+2*b ≤ u i ∧ u i ≤ modelPhaseClosedSlope F 1-2*b at hv
    change modelPhaseClosedSlope F 2+2*(b/2) < u i ∧ u i < modelPhaseClosedSlope F 1-2*(b/2)
    constructor <;> linarith [hv.1,hv.2]
  have hret₁ (i:ι) (hi:i∈S) : A*aProcessShiftPoint η 1 (y i) ∈
      Ioo (modelPhaseClosedSlope F 2+2*(b/2)) (modelPhaseClosedSlope F 1-2*(b/2)) := by
    have hv := hvalues _ (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨i,hi,rfl⟩))
    change modelPhaseClosedSlope F 2+2*b ≤ A*aProcessShiftPoint η 1 (y i) ∧
      A*aProcessShiftPoint η 1 (y i) ≤ modelPhaseClosedSlope F 1-2*b at hv
    constructor <;> linarith [hv.1,hv.2]
  let L := canonicalTaylorLegendrePhase F σ A (QJ+1) (deriv F (3/2)) (b/2)
  let J := aProcessShiftPhase L σ⁻¹ η
  have hL := hfirst F hFQ _ ha (b/2) hh hh₁ hhgap
  have hJ := hshift L η hL hη hηle
  have hJ₁ := approximateModelPhase_mono hJ (le_max_left _ _) le_rfl
  have hJQ := approximateModelPhase_mono hJ (le_max_right _ _) le_rfl
  let w := fun i => s*A*(1-η)*d i
  have hw (i:ι) (hi:i∈S) : w i ∈ modelPhaseSlopeRange J := by
    have hd := (moving_shift_displacement (QJ+1) hσ hsmall hF₁ hA
      (hpositive ha) hh (hpositive (hu i hi)) (hpositive (huk i hi))
      (hret₀ i hi) (hret₁ i hi)).2
    exact ⟨y i,hy i hi,hd.deriv⟩
  let c := deriv J (3/2)
  have hc : c ∈ modelPhaseSlopeRange J := ⟨3/2,by norm_num,rfl⟩
  have hwinJ := modelPhaseSlopeRange_eq_endpoint_Ioo hτ hsmall₂ hJ₁
  change modelPhaseSlopeRange J = Ioo (modelPhaseClosedSlope J 2)
    (modelPhaseClosedSlope J 1) at hwinJ
  have hci := hc
  rw [hwinJ] at hci
  have hpositiveJ {v:ℝ} (hv:v∈modelPhaseSlopeRange J) : 0 < v :=
    lt_of_lt_of_le (by positivity : (0:ℝ) < (2:ℝ)^(-(σ⁻¹+1))/2)
      (modelPhaseSlopeRange_positive_window hτ hpos₂ hJ hv).1
  obtain ⟨g,hg,hg₁,hgapJ,hvaluesJ⟩ := finite_slope_values_retained S
    (lt_trans hci.1 hci.2) w (fun i hi => by simpa only [hwinJ] using hw i hi)
  refine ⟨b/2,g,hh,hh₁,hg,hg₁,?_,?_,?_⟩
  · exact hsecond J hJQ c hc g hg hg₁ hgapJ
  · intro i hi
    exact modelPhaseSlopeRange_positive_window hτ hpos₂ hJ (hw i hi)
  · intro i hi
    exact moving_double_dual_resonance (QJ+1) Q hσ hsmall hsmall₂ hF₁
      hA hB (hpositive ha) (hpositiveJ hc) hh hg (hy i hi)
      (hpositive (hu i hi)) (hpositive (huk i hi)) (hret₀ i hi) (hret₁ i hi)
      hJ₁ (hpositiveJ (hw i hi)) (hvaluesJ i hi)

theorem actual_displacement_interval_exponent_pair_bound
    {σ A B k₀ l₀ ε : ℝ} (hσ : 0 < σ)
    (hA : 0 < A) (hA₂ : A ≤ 2) (hB : 0 < B) (hB₂ : B ≤ 2)
    (hpair : ExponentPair k₀ l₀) (hε : 0 < ε) :
    ∃ δ η₀ : ℝ, 0 < δ ∧ 0 < η₀ ∧ η₀ ≤ 1/2 ∧
      ∃ Q : ℕ, 1 ≤ Q ∧ ∃ C : ℝ, 1 ≤ C ∧
        ∀ (F : ℝ → ℝ) (η P V : ℝ) (a b : ℕ) (K : ℤ) (y : ℕ → ℝ),
          IsApproximateModelPhaseFunction F σ Q δ → 0 < η → η ≤ η₀ →
          0 < P → 0 < V →
          (∀ n∈Finset.Icc a b, y n ∈ Ioo (1:ℝ) 2) →
          (∀ n∈Finset.Icc a b, A*aProcessShiftPoint η 0 (y n) ∈ modelPhaseSlopeRange F) →
          (∀ n∈Finset.Icc a b, A*aProcessShiftPoint η 1 (y n) ∈ modelPhaseSlopeRange F) →
          let u := fun n => A*aProcessShiftPoint η 0 (y n)
          let k := A*η
          let d := fun n => modelPhaseInverseSlope F (u n)-modelPhaseInverseSlope F (u n+k)
          let s := A^(σ⁻¹-1)/(σ⁻¹*η)
          let θ := (σ⁻¹+1)⁻¹
          let M := B*P/(s*A*(1-η))
          let H := 2*V/(s*B^(θ-1))
          let R := fun n => 2*(F (modelPhaseInverseSlope F (u n+k))-
            F (modelPhaseInverseSlope F (u n))-k*modelPhaseInverseSlope F (u n+k))
          1 ≤ M → M ≤ (a:ℝ) → (b:ℝ) ≤ 2*M → V*k/P=(K:ℝ) →
          (∀ n∈Finset.Icc a b, P*d n=(n:ℝ)) →
          ∀ r : ℤ, r ≠ 0 →
            ‖∑ n∈Finset.Icc a b, fordAdditiveCharacter ((r:ℝ)*V*R n)‖ ≤
              C*(((|(r:ℝ)| * H)/M)^(k₀+ε)*M^(l₀+ε)+M/(|(r:ℝ)| * H)) := by
  have hθ : 0 < (σ⁻¹+1)⁻¹ := by positivity
  obtain ⟨δG,hδG,QG,_hQG,C,hC,hbound⟩ := hpair.allPositiveHeight_bound hθ hε
  obtain ⟨δ,η₀,hδ,hη₀,hηhalf,Q,Q₁,hQ,hrealize⟩ :=
    finite_moving_double_dual_realization hσ hA hA₂ hB hB₂ QG hδG
  refine ⟨δ,η₀,hδ,hη₀,hηhalf,Q,hQ,C,hC,?_⟩
  intro F η P V a b K y hF hη hηle hP hV hy hu huk u k d s θ M H R
    hM ha hb hK hn
  obtain ⟨h,g,_hh,_hh₁,_hg,_hg₁,hG,_hwindow,hvalues⟩ :=
    hrealize F η hF hη hηle ℕ (Finset.Icc a b) y hy hu huk
  let J := aProcessShiftPhase
    (canonicalTaylorLegendrePhase F σ A Q₁ (deriv F (3/2)) h) σ⁻¹ η
  let c := deriv J (3/2)
  let G := canonicalTaylorLegendrePhase J (σ⁻¹+1) B QG c g
  let C₀ := -2*V/s*modelPhaseLegendreDual J c+H*referenceModelPrimitive θ (c/B)
  have hs : 0 < s := by dsimp [s]; positivity
  have hz : 0 < B^(θ-1) := Real.rpow_pos_of_pos hB _
  have hH : 0 < H := by dsimp [H]; positivity
  have hηone : η < 1 := by linarith
  have hscales := double_dual_physical_scales (θ:=θ) hP hV hA hB
    (inv_pos.mpr hσ) hη hηone
  have hphase (n:ℕ) (hni:n∈Finset.Icc a b) :
      V*R n=C₀-H*G ((n:ℝ)/M)-2*(K:ℝ)*(n:ℝ) := by
    have hd : d n=(n:ℝ)/P := by
      apply (eq_div_iff hP.ne').mpr
      nlinarith only [hn n hni]
    have hv := hvalues n hni
    change G (s*A*(1-η)*d n/B)=
      B^(θ-1)*(-s/2*R n-s*k*d n-modelPhaseLegendreDual J c)+
        referenceModelPrimitive θ (c/B) at hv
    have harg := (hscales.2.2.2.2.2 (n:ℝ)).1
    change s*A*(1-η)*((n:ℝ)/P)/B=(n:ℝ)/M at harg
    rw [hd,harg] at hv
    rw [hv,← hK]
    dsimp only [H,C₀]
    field_simp
    ring
  have hint (z:ℤ) : fordAdditiveCharacter (z:ℝ)=1 := by
    unfold fordAdditiveCharacter
    have he : 2*Real.pi*Complex.I*((z:ℝ):ℂ) =
        (z:ℂ)*(2*Real.pi*Complex.I) := by push_cast; ring
    rw [he,Complex.exp_int_mul_two_pi_mul_I]
  intro r hr
  have hchar (n:ℕ) (hni:n∈Finset.Icc a b) :
      fordAdditiveCharacter ((r:ℝ)*V*R n) =
        fordAdditiveCharacter ((r:ℝ)*C₀)*
          star (fordAdditiveCharacter ((r:ℝ)*H*G ((n:ℝ)/M))) := by
    have he : (r:ℝ)*V*R n =
        ((r:ℝ)*C₀+-((r:ℝ)*H*G ((n:ℝ)/M)))+
          ((-2*r*K*(n:ℤ):ℤ):ℝ) := by
      push_cast
      rw [mul_assoc,hphase n hni]
      ring
    rw [he,fordAdditiveCharacter_add,hint,mul_one,
      fordAdditiveCharacter_add,← conj_fordAdditiveCharacter]
    rfl
  have hsum : (∑ n∈Finset.Icc a b, fordAdditiveCharacter ((r:ℝ)*V*R n)) =
      fordAdditiveCharacter ((r:ℝ)*C₀)*star (exponentialSumAt G ((r:ℝ)*H) M a b) := by
    rw [exponentialSumAt,star_sum,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n hni
    simp only [hchar n hni,sargos_ford_character_eq_fourier,oscillatory]
  rw [hsum,norm_mul,sargos_character_norm,one_mul,norm_star]
  have hnormheight : ‖exponentialSumAt G ((r:ℝ)*H) M a b‖ =
      ‖exponentialSumAt G (|(r:ℝ)| * H) M a b‖ := by
    by_cases hrpos : 0 ≤ (r:ℝ)
    · rw [abs_of_nonneg hrpos]
    · have hrneg : (r:ℝ) < 0 := lt_of_not_ge hrpos
      have he : exponentialSumAt G ((r:ℝ)*H) M a b =
          star (exponentialSumAt G (|(r:ℝ)| * H) M a b) := by
        simp only [exponentialSumAt,star_sum]
        apply Finset.sum_congr rfl
        intro n _hn
        simp only [oscillatory,←sargos_ford_character_eq_fourier,abs_of_neg hrneg]
        have harg : (r:ℝ)*H*G ((n:ℝ)/M) = -(-(r:ℝ)*H*G ((n:ℝ)/M)) := by ring
        rw [harg,←conj_fordAdditiveCharacter]
        rfl
      rw [he,norm_star]
  rw [hnormheight]
  exact hbound (|(r:ℝ)| * H) M G a b
    (mul_pos (abs_pos.mpr (Int.cast_ne_zero.mpr hr)) hH)
    hM ha hb hG

theorem positive_slope_chart_compressed_coordinate
    {d v k : ℝ} (hd : 0 < d) (hv : v ∈ Icc (4*d) 2)
    (hk : 0 ≤ k) (hkd : k ≤ d) :
    let j := positiveSlopeChartIndex d v
    let A := positiveSlopeChartScale d j
    let η := k/A
    let y := (v/A-η)/(1-η)
    j ∈ positiveSlopeChartIndices d ∧ 0 < A ∧ A ≤ 3/2 ∧
      0 ≤ η ∧ η ≤ 1/3 ∧ y ∈ Ioo (1:ℝ) 2 ∧
        A*aProcessShiftPoint η 0 y=v ∧ A*aProcessShiftPoint η 1 y=v+k := by
  intro j A η y
  have hj : j ∈ positiveSlopeChartIndices d := positiveSlopeChartIndex_mem hd hv
  obtain ⟨hA,hA₂⟩ := positiveSlopeChartScale_bounds hd hj
  have hj₄ : (4:ℝ) ≤ j := by exact_mod_cast (Finset.mem_Icc.mp hj).1
  have hjd := mul_le_mul_of_nonneg_right hj₄ hd.le
  have hAd : 3*d ≤ A := by dsimp [A,positiveSlopeChartScale]; nlinarith only [hjd]
  have hη : 0 ≤ η := div_nonneg hk hA.le
  have hη₁ : η ≤ 1/3 := by
    apply (div_le_iff₀ hA).mpr
    linarith only [hkd,hAd]
  have hden : 0 < 1-η := by linarith
  have hvpos : 0 ≤ v := (by positivity : (0:ℝ) ≤ 4*d).trans hv.1
  have hcell := (positiveSlopeChartIndex_eq_iff hd hvpos j).mp (show _=j from rfl)
  have hcoord := positiveSlopeChart_coordinate hd (Finset.mem_Icc.mp hj).1 hcell
  have hupper : v+k < 2*A := by
    dsimp [A,positiveSlopeChartScale]
    nlinarith only [hcell.2,hkd,hjd]
  have hy : y ∈ Ioo (1:ℝ) 2 := by
    constructor
    · apply (one_lt_div hden).mpr
      linarith only [hcoord.1]
    · apply (div_lt_iff₀ hden).mpr
      have hdiv : v/A+η < 2 := by
        dsimp only [η]
        rw [← add_div]
        exact (div_lt_iff₀ hA).mpr hupper
      linarith only [hdiv]
  have hzero : A*aProcessShiftPoint η 0 y=v := by
    dsimp only [aProcessShiftPoint,y]
    field_simp [show A ≠ 0 from hA.ne',hden.ne']
    ring
  refine ⟨hj,hA,hA₂,hη,hη₁,hy,hzero,?_⟩
  have hkA : A*η=k := mul_div_cancel₀ k (show A ≠ 0 from hA.ne')
  calc
    A*aProcessShiftPoint η 1 y=A*aProcessShiftPoint η 0 y+A*η := by
      dsimp [aProcessShiftPoint]
      ring
    _ = v+k := by rw [hzero,hkA]

theorem actual_displacement_interval_near_count
    {σ A B k₀ l₀ ε : ℝ} (hσ : 0 < σ)
    (hA : 0 < A) (hA₂ : A ≤ 2) (hB : 0 < B) (hB₂ : B ≤ 2)
    (hpair : ExponentPair k₀ l₀) (hε : 0 < ε) (hp : k₀+ε < 1) :
    ∃ δ η₀ : ℝ, 0 < δ ∧ 0 < η₀ ∧ η₀ ≤ 1/2 ∧
      ∃ Q : ℕ, 1 ≤ Q ∧ ∃ C : ℝ, 1 ≤ C ∧
        ∀ (F : ℝ → ℝ) (η P V : ℝ) (a b : ℕ) (K : ℤ) (y : ℕ → ℝ),
          IsApproximateModelPhaseFunction F σ Q δ → 0 < η → η ≤ η₀ →
          0 < P → 0 < V →
          (∀ n∈Finset.Icc a b, y n ∈ Ioo (1:ℝ) 2) →
          (∀ n∈Finset.Icc a b, A*aProcessShiftPoint η 0 (y n) ∈ modelPhaseSlopeRange F) →
          (∀ n∈Finset.Icc a b, A*aProcessShiftPoint η 1 (y n) ∈ modelPhaseSlopeRange F) →
          let u := fun n => A*aProcessShiftPoint η 0 (y n)
          let k := A*η
          let d := fun n => modelPhaseInverseSlope F (u n)-modelPhaseInverseSlope F (u n+k)
          let s := A^(σ⁻¹-1)/(σ⁻¹*η)
          let θ := (σ⁻¹+1)⁻¹
          let M := B*P/(s*A*(1-η))
          let H := 2*V/(s*B^(θ-1))
          let R := fun n => 2*(F (modelPhaseInverseSlope F (u n+k))-
            F (modelPhaseInverseSlope F (u n))-k*modelPhaseInverseSlope F (u n+k))
          1 ≤ M → M ≤ (a:ℝ) → (b:ℝ) ≤ 2*M → V*k/P=(K:ℝ) →
          (∀ n∈Finset.Icc a b, P*d n=(n:ℝ)) →
          ∀ (W : ℝ), 0 < W → W ≤ 1/2 →
          ∀ (I : Finset ℕ), I ⊆ Finset.Icc a b →
          (∀ n∈I, ∃ e : ℤ, |V*R n-(e:ℝ)| ≤ W/2) →
            (I.card:ℝ) ≤ 2*W*(Finset.Icc a b).card+
              (4+4/(1-(k₀+ε)))*(C*(H/M)^(k₀+ε)*M^(l₀+ε))*W^(-(k₀+ε))+
              2*(C*M/H) := by
  obtain ⟨δ,η₀,hδ,hη₀,hηhalf,Q,hQ,C,hC,hbound⟩ :=
    actual_displacement_interval_exponent_pair_bound hσ hA hA₂ hB hB₂ hpair hε
  refine ⟨δ,η₀,hδ,hη₀,hηhalf,Q,hQ,C,hC,?_⟩
  intro F η P V a b K y hF hη hηle hP hV hy hu huk u k d s θ M H R
    hM ha hb hK hn W hW hWhalf I hI hnear
  have hηone : η < 1 := by linarith
  have hs : 0 < s := by dsimp [s]; positivity
  have hH : 0 < H := by dsimp [H]; positivity
  have hMpos : 0 < M := lt_of_lt_of_le zero_lt_one hM
  have hCpos : 0 < C := zero_lt_one.trans_le hC
  have hp0 : 0 ≤ k₀+ε := by linarith [hpair.1.1]
  have hfreq (r:ℤ) (hr : r ≠ 0) :
      ‖∑ n∈Finset.Icc a b, fordAdditiveCharacter ((r:ℝ)*(V*R n))‖ ≤
        (C*(H/M)^(k₀+ε)*M^(l₀+ε))*|(r:ℝ)|^(k₀+ε)+C*M/H := by
    have hh := hbound F η P V a b K y hF hη hηle hP hV hy hu huk
      hM ha hb hK hn r hr
    change ‖∑ n∈Finset.Icc a b, fordAdditiveCharacter ((r:ℝ)*V*R n)‖ ≤
      C*(((|(r:ℝ)| * H)/M)^(k₀+ε)*M^(l₀+ε)+M/(|(r:ℝ)| * H)) at hh
    have hr1 : 1 ≤ |(r:ℝ)| := by exact_mod_cast Int.one_le_abs hr
    have htail : M/(|(r:ℝ)| * H) ≤ M/H :=
      div_le_div_of_nonneg_left hMpos.le hH (by nlinarith)
    have he : ((|(r:ℝ)| * H)/M)^(k₀+ε)=
        |(r:ℝ)|^(k₀+ε)*(H/M)^(k₀+ε) := by
      rw [show |(r:ℝ)| * H/M=|(r:ℝ)| * (H/M) by ring,
        Real.mul_rpow (abs_nonneg _) (div_nonneg hH.le hMpos.le)]
    simp only [mul_assoc] at hh ⊢
    rw [he] at hh
    calc
      _ ≤ C*(|(r:ℝ)|^(k₀+ε)*(H/M)^(k₀+ε)*M^(l₀+ε)+M/(|(r:ℝ)| * H)) := hh
      _ ≤ C*(|(r:ℝ)|^(k₀+ε)*(H/M)^(k₀+ε)*M^(l₀+ε)+M/H) := by gcongr
      _ = _ := by ring
  exact CubicNearCurve.cubic_near_integer_count_power
    (Finset.Icc a b) I (fun n => V*R n) hW hWhalf
    (by positivity) (by positivity) hp0 hp hI hnear hfreq

theorem finite_actual_displacement_interval_completion
    {σ δ A η P : ℝ} {F : ℝ → ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hF : IsApproximateModelPhaseFunction F σ 1 δ)
    (hA : 0 < A) (hη : η < 1)
    (S : Finset ℕ) (hne : S.Nonempty) (y : ℕ → ℝ)
    (hy : ∀ n∈S, y n∈Ioo (1:ℝ) 2)
    (hu : ∀ n∈S, A*aProcessShiftPoint η 0 (y n)∈modelPhaseSlopeRange F)
    (huk : ∀ n∈S, A*aProcessShiftPoint η 1 (y n)∈modelPhaseSlopeRange F)
    (hn : ∀ n∈S, P*(modelPhaseInverseSlope F (A*aProcessShiftPoint η 0 (y n))-
      modelPhaseInverseSlope F (A*aProcessShiftPoint η 1 (y n)))=(n:ℝ)) :
    ∃ z : ℕ → ℝ,
      (∀ n∈S, z n=y n) ∧
      ∀ n∈Finset.Icc (S.min' hne) (S.max' hne),
        z n∈Ioo (1:ℝ) 2 ∧
        A*aProcessShiftPoint η 0 (z n)∈modelPhaseSlopeRange F ∧
        A*aProcessShiftPoint η 1 (z n)∈modelPhaseSlopeRange F ∧
        P*(modelPhaseInverseSlope F (A*aProcessShiftPoint η 0 (z n))-
          modelPhaseInverseSlope F (A*aProcessShiftPoint η 1 (z n)))=(n:ℝ) := by
  classical
  let a := S.min' hne
  let b := S.max' hne
  have ha : a∈S := Finset.min'_mem S hne
  have hb : b∈S := Finset.max'_mem S hne
  let U := fun t v => A*aProcessShiftPoint η t v
  let D := fun v => P*(modelPhaseInverseSlope F (U 0 v)-modelPhaseInverseSlope F (U 1 v))
  have hmono (t : ℝ) : Monotone (U t) := by
    intro v w hvw
    dsimp [U,aProcessShiftPoint]
    gcongr
  have hpoint (v : ℝ) (hv : v∈uIcc (y a) (y b)) :
      v∈Ioo (1:ℝ) 2 ∧ U 0 v∈modelPhaseSlopeRange F ∧ U 1 v∈modelPhaseSlopeRange F := by
    have hconv : Set.OrdConnected (modelPhaseSlopeRange F) := by
      rw [modelPhaseSlopeRange_eq_endpoint_Ioo hσ hδ hF]
      exact (convex_Ioo _ _).ordConnected
    refine ⟨(convex_Ioo (1:ℝ) 2).ordConnected.uIcc_subset (hy a ha) (hy b hb) hv,?_,?_⟩
    · exact hconv.uIcc_subset (hu a ha) (hu b hb) ((hmono 0).image_uIcc_subset ⟨v,hv,rfl⟩)
    · exact hconv.uIcc_subset (huk a ha) (huk b hb) ((hmono 1).image_uIcc_subset ⟨v,hv,rfl⟩)
  have hD : ContinuousOn D (uIcc (y a) (y b)) := by
    intro v hv
    have hc (t : ℝ) (ht : U t v∈modelPhaseSlopeRange F) :
        ContinuousAt (fun w => modelPhaseInverseSlope F (U t w)) v := by
      exact ((modelPhaseInverseSlope_contDiffAt hσ hδ hF ht).continuousAt).comp
        (by dsimp [U,aProcessShiftPoint]; fun_prop)
    exact ((hc 0 (hpoint v hv).2.1).sub (hc 1 (hpoint v hv).2.2)).const_mul P
      |>.continuousWithinAt
  have hex (n : ℕ) (hni : n∈Finset.Icc a b) :
      ∃ v : ℝ, v∈Ioo (1:ℝ) 2 ∧ U 0 v∈modelPhaseSlopeRange F ∧
        U 1 v∈modelPhaseSlopeRange F ∧ D v=(n:ℝ) ∧ (n∈S → v=y n) := by
    by_cases hns : n∈S
    · exact ⟨y n,hy n hns,hu n hns,huk n hns,hn n hns,fun _ => rfl⟩
    have hna : a ≤ n := (Finset.mem_Icc.mp hni).1
    have hnb : n ≤ b := (Finset.mem_Icc.mp hni).2
    have hab : (a:ℝ) ≤ b := by exact_mod_cast hna.trans hnb
    have htarget : (n:ℝ)∈uIcc (D (y a)) (D (y b)) := by
      change (n:ℝ)∈uIcc (P*(_-_)) (P*(_-_))
      rw [hn a ha,hn b hb,uIcc_of_le hab]
      exact ⟨by exact_mod_cast hna,by exact_mod_cast hnb⟩
    obtain ⟨v,hv,he⟩ := intermediate_value_uIcc hD htarget
    exact ⟨v,(hpoint v hv).1,(hpoint v hv).2.1,(hpoint v hv).2.2,he,
      fun hh => False.elim (hns hh)⟩
  let z := fun n => if hni : n∈Finset.Icc a b then Classical.choose (hex n hni) else y n
  refine ⟨z,?_,?_⟩
  · intro n hns
    have hni : n∈Finset.Icc a b := Finset.mem_Icc.mpr
      ⟨Finset.min'_le S n hns,Finset.le_max' S n hns⟩
    simp only [z,dif_pos hni]
    exact (Classical.choose_spec (hex n hni)).2.2.2.2 hns
  · intro n hni
    change n∈Finset.Icc a b at hni
    simp only [z,dif_pos hni]
    have hh := Classical.choose_spec (hex n hni)
    exact ⟨hh.1,hh.2.1,hh.2.2.1,hh.2.2.2.1⟩

theorem actual_displacement_finite_near_count
    {σ A B k₀ l₀ ε : ℝ} (hσ : 0 < σ)
    (hA : 0 < A) (hA₂ : A ≤ 2) (hB : 0 < B) (hB₂ : B ≤ 2)
    (hpair : ExponentPair k₀ l₀) (hε : 0 < ε) (hp : k₀+ε < 1) :
    ∃ δ η₀ : ℝ, 0 < δ ∧ 0 < η₀ ∧ η₀ ≤ 1/2 ∧
      ∃ Q : ℕ, 1 ≤ Q ∧ ∃ C : ℝ, 1 ≤ C ∧
        ∀ (F : ℝ → ℝ) (η P V : ℝ) (K : ℤ) (S : Finset ℕ) (y : ℕ → ℝ),
          IsApproximateModelPhaseFunction F σ Q δ → 0 < η → η ≤ η₀ →
          0 < P → 0 < V →
          (∀ n∈S, y n ∈ Ioo (1:ℝ) 2) →
          (∀ n∈S, A*aProcessShiftPoint η 0 (y n) ∈ modelPhaseSlopeRange F) →
          (∀ n∈S, A*aProcessShiftPoint η 1 (y n) ∈ modelPhaseSlopeRange F) →
          let u := fun n => A*aProcessShiftPoint η 0 (y n)
          let k := A*η
          let d := fun n => modelPhaseInverseSlope F (u n)-modelPhaseInverseSlope F (u n+k)
          let s := A^(σ⁻¹-1)/(σ⁻¹*η)
          let θ := (σ⁻¹+1)⁻¹
          let M := B*P/(s*A*(1-η))
          let H := 2*V/(s*B^(θ-1))
          let R := fun n => 2*(F (modelPhaseInverseSlope F (u n+k))-
            F (modelPhaseInverseSlope F (u n))-k*modelPhaseInverseSlope F (u n+k))
          1 ≤ M → (∀ n∈S, M ≤ (n:ℝ) ∧ (n:ℝ) ≤ 2*M) → V*k/P=(K:ℝ) →
          (∀ n∈S, P*d n=(n:ℝ)) →
          ∀ (W : ℝ), 0 < W → W ≤ 1/2 →
          (∀ n∈S, ∃ e : ℤ, |V*R n-(e:ℝ)| ≤ W/2) →
            (S.card:ℝ) ≤ 4*W*M+
              (4+4/(1-(k₀+ε)))*(C*(H/M)^(k₀+ε)*M^(l₀+ε))*W^(-(k₀+ε))+
              2*(C*M/H) := by
  obtain ⟨δ₀,η₀,hδ₀,hη₀,hηhalf,Q,hQ,C,hC,hbound⟩ :=
    actual_displacement_interval_near_count hσ hA hA₂ hB hB₂ hpair hε hp
  let δ := min δ₀ (min (modelPhaseCurvatureLower σ) 1)
  have hδ : 0 < δ := lt_min hδ₀ (lt_min (modelPhaseCurvatureLower_pos hσ) zero_lt_one)
  refine ⟨δ,η₀,hδ,hη₀,hηhalf,Q,hQ,C,hC,?_⟩
  intro F η P V K S y hF hη hηle hP hV hy hu huk u k d s θ M H R
    hM hbox hK hn W hW hWhalf hnear
  have hs : 0 < s := by dsimp [s]; positivity
  have hH : 0 < H := by dsimp [H]; positivity
  have hMpos : 0 < M := zero_lt_one.trans_le hM
  have hCpos : 0 < C := zero_lt_one.trans_le hC
  have hFlarge := approximateModelPhase_mono hF (le_refl Q) (min_le_left δ₀ _)
  have hFone := approximateModelPhase_mono hF hQ (le_refl δ)
  have hshift (v : ℝ) : A*aProcessShiftPoint η 1 v=A*aProcessShiftPoint η 0 v+k := by
    dsimp [aProcessShiftPoint,k]
    ring
  by_cases hne : S.Nonempty
  · obtain ⟨z,hagree,hcomplete⟩ := finite_actual_displacement_interval_completion
      hσ (min_le_right δ₀ _) hFone hA (by linarith) S hne y hy hu huk
      (by intro n hni; rw [hshift]; exact hn n hni)
    let a := S.min' hne
    let b := S.max' hne
    have ha : a∈S := Finset.min'_mem S hne
    have hb : b∈S := Finset.max'_mem S hne
    have hab : a ≤ b := Finset.min'_le S b hb
    have hsubset : S ⊆ Finset.Icc a b := fun n hni => Finset.mem_Icc.mpr
      ⟨Finset.min'_le S n hni,Finset.le_max' S n hni⟩
    have hMa : M ≤ (a:ℝ) := (hbox a ha).1
    have hbM : (b:ℝ) ≤ 2*M := (hbox b hb).2
    have hz₀ : ∀ n∈Finset.Icc a b, z n∈Ioo (1:ℝ) 2 :=
      fun n hni => (hcomplete n hni).1
    have hz₁ : ∀ n∈Finset.Icc a b, A*aProcessShiftPoint η 0 (z n)∈modelPhaseSlopeRange F :=
      fun n hni => (hcomplete n hni).2.1
    have hz₂ : ∀ n∈Finset.Icc a b, A*aProcessShiftPoint η 1 (z n)∈modelPhaseSlopeRange F :=
      fun n hni => (hcomplete n hni).2.2.1
    have hz₃ : ∀ n∈Finset.Icc a b,
        P*(modelPhaseInverseSlope F (A*aProcessShiftPoint η 0 (z n))-
          modelPhaseInverseSlope F (A*aProcessShiftPoint η 0 (z n)+k))=(n:ℝ) := by
      intro n hni
      have hh := (hcomplete n hni).2.2.2
      rwa [hshift] at hh
    let Rz := fun n => 2*(F (modelPhaseInverseSlope F (A*aProcessShiftPoint η 0 (z n)+k))-
      F (modelPhaseInverseSlope F (A*aProcessShiftPoint η 0 (z n)))-
      k*modelPhaseInverseSlope F (A*aProcessShiftPoint η 0 (z n)+k))
    have hznear : ∀ n∈S, ∃ e : ℤ, |V*Rz n-(e:ℝ)| ≤ W/2 := by
      intro n hni
      have he : Rz n=R n := by
        dsimp only [Rz,R,u]
        rw [hagree n hni]
      rw [he]
      exact hnear n hni
    have hh := hbound F η P V a b K z hFlarge hη hηle hP hV hz₀ hz₁ hz₂
      hM hMa hbM hK hz₃ W hW hWhalf S hsubset hznear
    change (S.card:ℝ) ≤ 2*W*(Finset.Icc a b).card+
      (4+4/(1-(k₀+ε)))*(C*(H/M)^(k₀+ε)*M^(l₀+ε))*W^(-(k₀+ε))+
      2*(C*M/H) at hh
    have hcard : ((Finset.Icc a b).card:ℝ) ≤ 2*M := by
      rw [Nat.card_Icc,Nat.cast_sub (by omega : a ≤ b+1),Nat.cast_add,Nat.cast_one]
      linarith
    calc
      _ ≤ _ := hh
      _ ≤ 2*W*(2*M)+(4+4/(1-(k₀+ε)))*(C*(H/M)^(k₀+ε)*M^(l₀+ε))*W^(-(k₀+ε))+
          2*(C*M/H) := by gcongr
      _ = _ := by ring
  · have he : S=∅ := Finset.not_nonempty_iff_eq_empty.mp hne
    simp only [he,Finset.card_empty,Nat.cast_zero]
    positivity

theorem finite_moving_displacement_window
    {σ A : ℝ} (hσ : 0 < σ) (hA : 0 < A) (hA₂ : A ≤ 2) :
    ∃ δ η₀ : ℝ, 0 < δ ∧ 0 < η₀ ∧ η₀ ≤ 1/2 ∧
      ∃ Q : ℕ, 1 ≤ Q ∧
        ∀ (F : ℝ → ℝ) (η : ℝ), IsApproximateModelPhaseFunction F σ Q δ →
          0 < η → η ≤ η₀ → ∀ (ι : Type*) (S : Finset ι) (y : ι → ℝ),
          (∀ i∈S, y i∈Ioo (1:ℝ) 2) →
          (∀ i∈S, A*aProcessShiftPoint η 0 (y i)∈modelPhaseSlopeRange F) →
          (∀ i∈S, A*aProcessShiftPoint η 1 (y i)∈modelPhaseSlopeRange F) →
          let u := fun i => A*aProcessShiftPoint η 0 (y i)
          let k := A*η
          let d := fun i => modelPhaseInverseSlope F (u i)-modelPhaseInverseSlope F (u i+k)
          let s := A^(σ⁻¹-1)/(σ⁻¹*η)
          ∀ i∈S, s*A*(1-η)*d i∈Icc ((2:ℝ)^(-(σ⁻¹+1))/2) 2 := by
  obtain ⟨δ,η₀,hδ,hη₀,hηhalf,Q,Q₁,hQ,hrealize⟩ :=
    finite_moving_double_dual_realization hσ hA hA₂ (by norm_num : (0:ℝ)<1)
      (by norm_num : (1:ℝ)≤2) 0 (by norm_num : (0:ℝ)<1)
  refine ⟨δ,η₀,hδ,hη₀,hηhalf,Q,hQ,?_⟩
  intro F η hF hη hηle ι S y hy hu huk u k d s
  obtain ⟨h,g,_hh,_hh1,_hg,_hg1,_hG,hwindow,_hvalues⟩ :=
    hrealize F η hF hη hηle ι S y hy hu huk
  exact hwindow

theorem displacement_second_chart_geometry
    {mesh w L P n : ℝ} (hd : 0 < mesh) (hL : 0 < L) (hP : 0 < P)
    (hw : w∈Icc (4*mesh) 2) (hn : 2 ≤ n) (he : w=L*n/P) :
    let j := positiveSlopeChartIndex mesh w
    let B := positiveSlopeChartScale mesh j
    let M := B*P/L
    j∈positiveSlopeChartIndices mesh ∧ 0 < B ∧ B ≤ 3/2 ∧
      1 ≤ M ∧ M ≤ n ∧ n ≤ 2*M := by
  intro j B M
  have hj := positiveSlopeChartIndex_mem hd hw
  have hBj := positiveSlopeChartScale_bounds hd hj
  have hw0 : 0 ≤ w := (by positivity : (0:ℝ) ≤ 4*mesh).trans hw.1
  have hcell := (positiveSlopeChartIndex_eq_iff hd hw0 j).mp (show _=j from rfl)
  have hc := positiveSlopeChart_coordinate hd (Finset.mem_Icc.mp hj).1 hcell
  have hB : 0 < B := hBj.1
  have hM : 0 < M := by dsimp [M]; positivity
  have harg : w/B=n/M := by
    rw [he]
    dsimp only [M]
    field_simp
  change w/B∈Ioo (1:ℝ) 2 at hc
  rw [harg] at hc
  have hlo : M < n := (one_lt_div hM).mp hc.1
  have hhi : n < 2*M := (div_lt_iff₀ hM).mp hc.2
  exact ⟨hj,hB,hBj.2,by linarith,hlo.le,hhi.le⟩

theorem actual_displacement_physical_chart_count
    {σ A B k₀ l₀ ε : ℝ} (hσ : 0 < σ)
    (hA : 0 < A) (hA₂ : A ≤ 2) (hB : 0 < B) (hB₂ : B ≤ 2)
    (hpair : ExponentPair k₀ l₀) (hε : 0 < ε) (hp : k₀+ε < 1) :
    ∃ δ η₀ : ℝ, 0 < δ ∧ 0 < η₀ ∧ η₀ ≤ 1/2 ∧
      ∃ Q : ℕ, 1 ≤ Q ∧ ∃ C : ℝ, 1 ≤ C ∧
        ∀ (F : ℝ → ℝ) (η P V N : ℝ) (K : ℤ) (S : Finset ℕ) (y : ℕ → ℝ),
          IsApproximateModelPhaseFunction F σ Q δ → 0 < η → η ≤ η₀ →
          0 < P → 0 < V → 0 < N →
          (∀ n∈S, y n ∈ Ioo (1:ℝ) 2) →
          (∀ n∈S, A*aProcessShiftPoint η 0 (y n) ∈ modelPhaseSlopeRange F) →
          (∀ n∈S, A*aProcessShiftPoint η 1 (y n) ∈ modelPhaseSlopeRange F) →
          let u := fun n => A*aProcessShiftPoint η 0 (y n)
          let k := A*η
          let d := fun n => modelPhaseInverseSlope F (u n)-modelPhaseInverseSlope F (u n+k)
          let s := A^(σ⁻¹-1)/(σ⁻¹*η)
          let M := B*P/(s*A*(1-η))
          let R := fun n => 2*(F (modelPhaseInverseSlope F (u n+k))-
            F (modelPhaseInverseSlope F (u n))-k*modelPhaseInverseSlope F (u n+k))
          1 ≤ M → (∀ n∈S, M ≤ (n:ℝ) ∧ (n:ℝ) ≤ 2*M) →
          (∀ n∈S, (n:ℝ) ≤ 2*N) → V*k/P=(K:ℝ) →
          (∀ n∈S, P*d n=(n:ℝ)) →
          ∀ (W : ℝ), 0 < W → W ≤ 1/2 →
          (∀ n∈S, ∃ e : ℤ, |V*R n-(e:ℝ)| ≤ W/2) →
            (S.card:ℝ) ≤ C*(W*N+(V/P)^(k₀+ε)*N^(l₀+ε)*W^(-(k₀+ε))+P/V) := by
  obtain ⟨δ,η₀,hδ,hη₀,hηhalf,Q,hQ,C₀,hC₀,hcount⟩ :=
    actual_displacement_finite_near_count hσ hA hA₂ hB hB₂ hpair hε hp
  let p := k₀+ε
  let q := l₀+ε
  let θ := (σ⁻¹+1)⁻¹
  let c := A*B^(-θ)
  let D := (4+4/(1-p))*C₀*(2*c)^p*(2:ℝ)^q
  let E := 2*C₀/c
  let C := 8+D+E
  have hp₀ : 0 ≤ p := by dsimp [p]; linarith [hpair.1.1]
  have hq₀ : 0 ≤ q := by dsimp [q]; linarith [hpair.1.2.2.1]
  have hc : 0 < c := by dsimp [c]; positivity
  have hD : 0 ≤ D := by dsimp [D,p]; positivity
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have hC : 1 ≤ C := by dsimp [C]; linarith
  refine ⟨δ,η₀,hδ,hη₀,hηhalf,Q,hQ,C,hC,?_⟩
  intro F η P V N K S y hF hη hηle hP hV hN hy hu huk u k d s M R
    hM hbox hNbox hK hn W hW hWhalf hnear
  let H := 2*V/(s*B^(θ-1))
  have hηh : η ≤ 1/2 := hηle.trans hηhalf
  have hηone : η < 1 := by linarith
  have hscales := double_dual_physical_scales (θ:=θ) hP hV hA hB
    (inv_pos.mpr hσ) hη hηone
  have hMpos : 0 < M := hscales.1
  have hH : 0 < H := hscales.2.1
  have heq : H/M=2*c*(1-η)*(V/P) := by
    calc
      _ = (2*V/P)*A*(1-η)*B^(-θ) := hscales.2.2.2.1
      _ = _ := by dsimp [c]; ring
  have hlo : c*(V/P) ≤ H/M := by rw [heq]; nlinarith [mul_pos hc (div_pos hV hP)]
  have hhi : H/M ≤ (2*c)*(V/P) := by rw [heq]; nlinarith [mul_pos hc (div_pos hV hP)]
  have htail : M/H ≤ (1/c)*(P/V) := by
    have hh := one_div_le_one_div_of_le (mul_pos hc (div_pos hV hP)) hlo
    convert hh using 1 <;> field_simp
  by_cases hne : S.Nonempty
  · obtain ⟨n,hns⟩ := hne
    have hMN : M ≤ 2*N := (hbox n hns).1.trans (hNbox n hns)
    have hfreq : (H/M)^p ≤ (2*c)^p*(V/P)^p := by
      rw [← Real.mul_rpow (by positivity : 0 ≤ 2*c) (div_nonneg hV.le hP.le)]
      exact Real.rpow_le_rpow (div_nonneg hH.le hMpos.le) hhi hp₀
    have hlength : M^q ≤ (2:ℝ)^q*N^q := by
      rw [← Real.mul_rpow (by norm_num : (0:ℝ) ≤ 2) hN.le]
      exact Real.rpow_le_rpow hMpos.le hMN hq₀
    have hh := hcount F η P V K S y hF hη hηle hP hV hy hu huk
      hM hbox hK hn W hW hWhalf hnear
    change (S.card:ℝ) ≤ 4*W*M+
      (4+4/(1-p))*(C₀*(H/M)^p*M^q)*W^(-p)+2*(C₀*M/H) at hh
    have hmain : (4+4/(1-p))*(C₀*(H/M)^p*M^q)*W^(-p) ≤
        D*((V/P)^p*N^q*W^(-p)) := by
      calc
        _ ≤ (4+4/(1-p))*(C₀*((2*c)^p*(V/P)^p)*((2:ℝ)^q*N^q))*W^(-p) := by
          gcongr
        _ = _ := by dsimp [D]; ring
    have htail' : 2*(C₀*M/H) ≤ E*(P/V) := by
      calc
        _ = 2*C₀*(M/H) := by ring
        _ ≤ 2*C₀*((1/c)*(P/V)) := by gcongr
        _ = _ := by dsimp [E]; ring
    have hvolume : 4*W*M ≤ 8*(W*N) := by nlinarith [mul_le_mul_of_nonneg_left hMN hW.le]
    have hbig₀ : 8 ≤ C := by dsimp [C]; linarith
    have hbig₁ : D ≤ C := by dsimp [C]; linarith
    have hbig₂ : E ≤ C := by dsimp [C]; linarith
    calc
      _ ≤ 8*(W*N)+D*((V/P)^p*N^q*W^(-p))+E*(P/V) := by linarith
      _ ≤ C*(W*N)+C*((V/P)^p*N^q*W^(-p))+C*(P/V) := by gcongr
      _ = _ := by dsimp [p,q]; ring
  · have he : S=∅ := Finset.not_nonempty_iff_eq_empty.mp hne
    simp only [he,Finset.card_empty,Nat.cast_zero]
    positivity

theorem actual_displacement_first_chart_count
    {σ A k₀ l₀ ε : ℝ} (hσ : 0 < σ)
    (hA : 0 < A) (hA₂ : A ≤ 2)
    (hpair : ExponentPair k₀ l₀) (hε : 0 < ε) (hp : k₀+ε < 1) :
    ∃ δ η₀ : ℝ, 0 < δ ∧ 0 < η₀ ∧ η₀ ≤ 1/2 ∧
      ∃ Q : ℕ, 1 ≤ Q ∧ ∃ C : ℝ, 1 ≤ C ∧
        ∀ (F : ℝ → ℝ) (η P V N : ℝ) (K : ℤ) (S : Finset ℕ) (y : ℕ → ℝ),
          IsApproximateModelPhaseFunction F σ Q δ → 0 < η → η ≤ η₀ →
          0 < P → 0 < V → 0 < N →
          (∀ n∈S, y n ∈ Ioo (1:ℝ) 2) →
          (∀ n∈S, A*aProcessShiftPoint η 0 (y n) ∈ modelPhaseSlopeRange F) →
          (∀ n∈S, A*aProcessShiftPoint η 1 (y n) ∈ modelPhaseSlopeRange F) →
          let u := fun n => A*aProcessShiftPoint η 0 (y n)
          let k := A*η
          let d := fun n => modelPhaseInverseSlope F (u n)-modelPhaseInverseSlope F (u n+k)
          let R := fun n => 2*(F (modelPhaseInverseSlope F (u n+k))-
            F (modelPhaseInverseSlope F (u n))-k*modelPhaseInverseSlope F (u n+k))
          (∀ n∈S, 2 ≤ (n:ℝ) ∧ (n:ℝ) ≤ 2*N) → V*k/P=(K:ℝ) →
          (∀ n∈S, P*d n=(n:ℝ)) →
          ∀ (W : ℝ), 0 < W → W ≤ 1/2 →
          (∀ n∈S, ∃ e : ℤ, |V*R n-(e:ℝ)| ≤ W/2) →
            (S.card:ℝ) ≤ C*(W*N+(V/P)^(k₀+ε)*N^(l₀+ε)*W^(-(k₀+ε))+P/V) := by
  classical
  let mesh := (2:ℝ)^(-(σ⁻¹+1))/8
  have hmesh : 0 < mesh := by dsimp [mesh]; positivity
  have hmesh₂ : 4*mesh ≤ 2 := by
    have hh : (2:ℝ)^(-(σ⁻¹+1)) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by have := inv_pos.mpr hσ; linarith)
    dsimp [mesh]
    linarith
  let J := positiveSlopeChartIndices mesh
  have hJ : J.Nonempty := ⟨positiveSlopeChartIndex mesh (4*mesh),
    positiveSlopeChartIndex_mem hmesh ⟨le_rfl,hmesh₂⟩⟩
  have ht : J.attach.Nonempty := hJ.attach
  let B := fun j : {j // j∈J} => positiveSlopeChartScale mesh j.val
  have hBj (j : {j // j∈J}) : 0 < B j ∧ B j ≤ 2 := by
    have hh := positiveSlopeChartScale_bounds hmesh j.property
    exact ⟨hh.1,hh.2.trans (by norm_num)⟩
  have hlocal (j : {j // j∈J}) := actual_displacement_physical_chart_count
    hσ hA hA₂ (hBj j).1 (hBj j).2 hpair hε hp
  choose δj ηj hδj hηj hηhalfj Qj hQj Cj hCj hcount using hlocal
  obtain ⟨δw,ηw,hδw,hηw,hηhalfw,Qw,hQw,hwindow⟩ :=
    finite_moving_displacement_window hσ hA hA₂
  let δ := min δw (J.attach.inf' ht δj)
  let η₀ := min ηw (J.attach.inf' ht ηj)
  let Q := max Qw (J.attach.sup Qj)
  let C := 1+∑ j∈J.attach, Cj j
  have hδ : 0 < δ := lt_min hδw ((Finset.lt_inf'_iff ht).mpr (fun j _ => hδj j))
  have hη₀ : 0 < η₀ := lt_min hηw ((Finset.lt_inf'_iff ht).mpr (fun j _ => hηj j))
  have hηhalf : η₀ ≤ 1/2 := (min_le_left _ _).trans hηhalfw
  have hQ : 1 ≤ Q := hQw.trans (le_max_left _ _)
  have hC : 1 ≤ C := by
    have hh : 0 ≤ ∑ j∈J.attach, Cj j := Finset.sum_nonneg (fun j _ => by linarith [hCj j])
    dsimp [C]
    linarith
  refine ⟨δ,η₀,hδ,hη₀,hηhalf,Q,hQ,C,hC,?_⟩
  intro F η P V N K S y hF hη hηle hP hV hN hy hu huk u k d R hbox hK hn W hW hWhalf hnear
  let s := A^(σ⁻¹-1)/(σ⁻¹*η)
  let L := s*A*(1-η)
  let w := fun n => L*d n
  have hηwle : η ≤ ηw := hηle.trans (min_le_left _ _)
  have hηone : η < 1 := by linarith [hηwle,hηhalfw]
  have hL : 0 < L := by dsimp [L,s]; positivity
  have hFwindow := approximateModelPhase_mono hF (le_max_left _ _) (min_le_left _ _)
  have hw₀ := hwindow F η hFwindow hη hηwle ℕ S y hy hu huk
  have hw (n : ℕ) (hns : n∈S) : w n∈Icc (4*mesh) 2 := by
    have hh := hw₀ n hns
    change L*d n ∈ Icc ((2:ℝ)^(-(σ⁻¹+1))/2) 2 at hh
    change L*d n∈Icc (4*mesh) 2
    rw [show 4*mesh=(2:ℝ)^(-(σ⁻¹+1))/2 by dsimp [mesh]; ring]
    exact hh
  let label := fun n => positiveSlopeChartIndex mesh (w n)
  have hlabel : ∀ n∈S, label n∈J := fun n hns => positiveSlopeChartIndex_mem hmesh (hw n hns)
  let cell := fun j : {j // j∈J} => S.filter (fun n => label n=j.val)
  have hcell (j : {j // j∈J}) :
      ((cell j).card:ℝ) ≤ Cj j*(W*N+(V/P)^(k₀+ε)*N^(l₀+ε)*W^(-(k₀+ε))+P/V) := by
    let M := B j*P/L
    have hgeom (n : ℕ) (hni : n∈cell j) : 1 ≤ M ∧ M ≤ (n:ℝ) ∧ (n:ℝ) ≤ 2*M := by
      have hns := (Finset.mem_filter.mp hni).1
      have he : w n=L*(n:ℝ)/P := by
        dsimp only [w]
        have hd : d n=(n:ℝ)/P := by
          apply (eq_div_iff hP.ne').mpr
          simpa [mul_comm] using hn n hns
        rw [hd]
        ring
      have hh := displacement_second_chart_geometry hmesh hL hP (hw n hns) (hbox n hns).1 he
      change label n∈J ∧ 0 < positiveSlopeChartScale mesh (label n) ∧
        positiveSlopeChartScale mesh (label n) ≤ 3/2 ∧
        1 ≤ positiveSlopeChartScale mesh (label n)*P/L ∧
        positiveSlopeChartScale mesh (label n)*P/L ≤ (n:ℝ) ∧
        (n:ℝ) ≤ 2*(positiveSlopeChartScale mesh (label n)*P/L) at hh
      rw [(Finset.mem_filter.mp hni).2] at hh
      exact hh.2.2.2
    by_cases hne : (cell j).Nonempty
    · obtain ⟨n,hni⟩ := hne
      have hFj := approximateModelPhase_mono hF
        ((Finset.le_sup (Finset.mem_attach J j)).trans (le_max_right _ _))
        ((min_le_right _ _).trans (Finset.inf'_le δj (Finset.mem_attach J j)))
      have hηjle : η ≤ ηj j := hηle.trans
        ((min_le_right _ _).trans (Finset.inf'_le ηj (Finset.mem_attach J j)))
      exact hcount j F η P V N K (cell j) y hFj hη hηjle hP hV hN
        (fun n hn => hy n (Finset.mem_filter.mp hn).1)
        (fun n hn => hu n (Finset.mem_filter.mp hn).1)
        (fun n hn => huk n (Finset.mem_filter.mp hn).1)
        (hgeom n hni).1 (fun n hn => (hgeom n hn).2)
        (fun n hn => (hbox n (Finset.mem_filter.mp hn).1).2) hK
        (fun n hni => hn n (Finset.mem_filter.mp hni).1) W hW hWhalf
        (fun n hn => hnear n (Finset.mem_filter.mp hn).1)
    · have he : cell j=∅ := Finset.not_nonempty_iff_eq_empty.mp hne
      rw [he,Finset.card_empty,Nat.cast_zero]
      have hCj₀ : 0 ≤ Cj j := (by norm_num : (0:ℝ)≤1).trans (hCj j)
      positivity
  have hcard : (S.card:ℝ)=∑ j∈J.attach, ((cell j).card:ℝ) := by
    dsimp only [cell]
    rw [Finset.sum_attach J (fun j : ℕ => ((S.filter (fun n => label n=j)).card:ℝ))]
    exact_mod_cast Finset.card_eq_sum_card_fiberwise hlabel
  let X := W*N+(V/P)^(k₀+ε)*N^(l₀+ε)*W^(-(k₀+ε))+P/V
  have hX : 0 ≤ X := by dsimp [X]; positivity
  calc
    _ = ∑ j∈J.attach, ((cell j).card:ℝ) := hcard
    _ ≤ ∑ j∈J.attach, Cj j*X := Finset.sum_le_sum (fun j _ => hcell j)
    _ = (∑ j∈J.attach, Cj j)*X := (Finset.sum_mul _ _ _).symm
    _ ≤ C*X := by dsimp only [C]; nlinarith

theorem actual_displacement_near_curve_count
    {σ k₀ l₀ ε : ℝ} (hσ : 0 < σ)
    (hpair : ExponentPair k₀ l₀) (hε : 0 < ε) (hp : k₀+ε < 1) :
    ∃ δ κ₀ : ℝ, 0 < δ ∧ 0 < κ₀ ∧
      ∃ Q : ℕ, 1 ≤ Q ∧ ∃ C : ℝ, 1 ≤ C ∧
        ∀ (F : ℝ → ℝ) (κ P V N : ℝ) (K : ℤ) (S : Finset ℕ) (u : ℕ → ℝ),
          IsApproximateModelPhaseFunction F σ Q δ → 0 < κ → κ ≤ κ₀ →
          0 < P → 0 < V → 0 < N →
          (∀ n∈S, u n ∈ modelPhaseSlopeRange F) →
          (∀ n∈S, u n+κ ∈ modelPhaseSlopeRange F) →
          let d := fun n => modelPhaseInverseSlope F (u n)-modelPhaseInverseSlope F (u n+κ)
          let R := fun n => 2*(F (modelPhaseInverseSlope F (u n+κ))-
            F (modelPhaseInverseSlope F (u n))-κ*modelPhaseInverseSlope F (u n+κ))
          (∀ n∈S, 2 ≤ (n:ℝ) ∧ (n:ℝ) ≤ 2*N) → V*κ/P=(K:ℝ) →
          (∀ n∈S, P*d n=(n:ℝ)) →
          ∀ (W : ℝ), 0 < W → W ≤ 1/2 →
          (∀ n∈S, ∃ e : ℤ, |V*R n-(e:ℝ)| ≤ W/2) →
            (S.card:ℝ) ≤ C*(W*N+(V/P)^(k₀+ε)*N^(l₀+ε)*W^(-(k₀+ε))+P/V) := by
  classical
  let mesh := (2:ℝ)^(-σ)/8
  have hmesh : 0 < mesh := by dsimp [mesh]; positivity
  have hmesh₂ : 4*mesh ≤ 2 := by
    have hh : (2:ℝ)^(-σ) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by linarith)
    dsimp [mesh]
    linarith
  let J := positiveSlopeChartIndices mesh
  have hJ : J.Nonempty := ⟨positiveSlopeChartIndex mesh (4*mesh),
    positiveSlopeChartIndex_mem hmesh ⟨le_rfl,hmesh₂⟩⟩
  have ht : J.attach.Nonempty := hJ.attach
  let A := fun j : {j // j∈J} => positiveSlopeChartScale mesh j.val
  have hAj (j : {j // j∈J}) : 0 < A j ∧ A j ≤ 2 := by
    have hh := positiveSlopeChartScale_bounds hmesh j.property
    exact ⟨hh.1,hh.2.trans (by norm_num)⟩
  have hlocal (j : {j // j∈J}) := actual_displacement_first_chart_count
    hσ (hAj j).1 (hAj j).2 hpair hε hp
  choose δj ηj hδj hηj hηhalfj Qj hQj Cj hCj hcount using hlocal
  let δ := min (min ((2:ℝ)^(-σ)/2) 1) (J.attach.inf' ht δj)
  let ηmin := J.attach.inf' ht ηj
  let κ₀ := min mesh (3*mesh*ηmin)
  let Q := max 1 (J.attach.sup Qj)
  let C := 1+∑ j∈J.attach, Cj j
  have hδ : 0 < δ := lt_min (lt_min (by positivity) zero_lt_one)
    ((Finset.lt_inf'_iff ht).mpr (fun j _ => hδj j))
  have hηmin : 0 < ηmin := (Finset.lt_inf'_iff ht).mpr (fun j _ => hηj j)
  have hκ₀ : 0 < κ₀ := lt_min hmesh (by positivity)
  have hQ : 1 ≤ Q := le_max_left _ _
  have hC : 1 ≤ C := by
    have hh : 0 ≤ ∑ j∈J.attach, Cj j := Finset.sum_nonneg (fun j _ => by linarith [hCj j])
    dsimp [C]
    linarith
  refine ⟨δ,κ₀,hδ,hκ₀,Q,hQ,C,hC,?_⟩
  intro F κ P V N K S u hF hκ hκle hP hV hN hu huk d R hbox hK hn W hW hWhalf hnear
  have hκmesh : κ ≤ mesh := hκle.trans (min_le_left _ _)
  have hw (n : ℕ) (hns : n∈S) : u n∈Icc (4*mesh) 2 := by
    rw [show 4*mesh=(2:ℝ)^(-σ)/2 by dsimp [mesh]; ring]
    exact modelPhaseSlopeRange_positive_window hσ (min_le_left _ _) hF (hu n hns)
  let label := fun n => positiveSlopeChartIndex mesh (u n)
  have hlabel : ∀ n∈S, label n∈J := fun n hns => positiveSlopeChartIndex_mem hmesh (hw n hns)
  let cell := fun j : {j // j∈J} => S.filter (fun n => label n=j.val)
  have hcell (j : {j // j∈J}) :
      ((cell j).card:ℝ) ≤ Cj j*(W*N+(V/P)^(k₀+ε)*N^(l₀+ε)*W^(-(k₀+ε))+P/V) := by
    let η := κ/A j
    let y := fun n => (u n/A j-η)/(1-η)
    have hη : 0 < η := div_pos hκ (hAj j).1
    have hk : A j*η=κ := mul_div_cancel₀ κ (hAj j).1.ne'
    have hηle : η ≤ ηj j := by
      have hAmesh : 3*mesh ≤ A j := by
        have hj4 : (4:ℝ) ≤ j.val := by exact_mod_cast (Finset.mem_Icc.mp j.property).1
        dsimp [A,positiveSlopeChartScale]
        nlinarith [mul_le_mul_of_nonneg_right hj4 hmesh.le]
      have hcap : κ ≤ 3*mesh*ηmin := hκle.trans (min_le_right _ _)
      have hmin : ηmin ≤ ηj j := Finset.inf'_le ηj (Finset.mem_attach J j)
      apply (div_le_iff₀ (hAj j).1).mpr
      calc
        κ ≤ 3*mesh*ηmin := hcap
        _ ≤ A j*ηj j := mul_le_mul hAmesh hmin hηmin.le (hAj j).1.le
        _ = ηj j*A j := by ring
    have hgeom (n : ℕ) (hni : n∈cell j) :
        y n∈Ioo (1:ℝ) 2 ∧
          A j*aProcessShiftPoint η 0 (y n)=u n ∧
          A j*aProcessShiftPoint η 1 (y n)=u n+κ := by
      have hns := (Finset.mem_filter.mp hni).1
      have hh := positive_slope_chart_compressed_coordinate hmesh (hw n hns) hκ.le hκmesh
      dsimp only at hh
      have he : positiveSlopeChartIndex mesh (u n)=j.val := (Finset.mem_filter.mp hni).2
      rw [he] at hh
      exact hh.2.2.2.2.2
    have hFj := approximateModelPhase_mono hF
      ((Finset.le_sup (Finset.mem_attach J j)).trans (le_max_right _ _))
      ((min_le_right _ _).trans (Finset.inf'_le δj (Finset.mem_attach J j)))
    have huj : ∀ n∈cell j, A j*aProcessShiftPoint η 0 (y n)∈modelPhaseSlopeRange F := by
      intro n hni
      rw [(hgeom n hni).2.1]
      exact hu n (Finset.mem_filter.mp hni).1
    have hukj : ∀ n∈cell j, A j*aProcessShiftPoint η 1 (y n)∈modelPhaseSlopeRange F := by
      intro n hni
      rw [(hgeom n hni).2.2]
      exact huk n (Finset.mem_filter.mp hni).1
    have hnj : ∀ n∈cell j, P*(modelPhaseInverseSlope F (A j*aProcessShiftPoint η 0 (y n))-
        modelPhaseInverseSlope F (A j*aProcessShiftPoint η 0 (y n)+A j*η))=(n:ℝ) := by
      intro n hni
      rw [(hgeom n hni).2.1,hk]
      exact hn n (Finset.mem_filter.mp hni).1
    have hnearj : ∀ n∈cell j, ∃ e : ℤ,
        |V*(2*(F (modelPhaseInverseSlope F (A j*aProcessShiftPoint η 0 (y n)+A j*η))-
          F (modelPhaseInverseSlope F (A j*aProcessShiftPoint η 0 (y n)))-
          (A j*η)*modelPhaseInverseSlope F (A j*aProcessShiftPoint η 0 (y n)+A j*η)))-(e:ℝ)| ≤ W/2 := by
      intro n hni
      rw [(hgeom n hni).2.1,hk]
      exact hnear n (Finset.mem_filter.mp hni).1
    exact hcount j F η P V N K (cell j) y hFj hη hηle hP hV hN
      (fun n hn => (hgeom n hn).1) huj hukj
      (fun n hn => hbox n (Finset.mem_filter.mp hn).1)
      (by rw [hk]; exact hK) hnj W hW hWhalf hnearj
  have hcard : (S.card:ℝ)=∑ j∈J.attach, ((cell j).card:ℝ) := by
    dsimp only [cell]
    rw [Finset.sum_attach J (fun j : ℕ => ((S.filter (fun n => label n=j)).card:ℝ))]
    exact_mod_cast Finset.card_eq_sum_card_fiberwise hlabel
  let X := W*N+(V/P)^(k₀+ε)*N^(l₀+ε)*W^(-(k₀+ε))+P/V
  have hX : 0 ≤ X := by dsimp [X]; positivity
  calc
    _ = ∑ j∈J.attach, ((cell j).card:ℝ) := hcard
    _ ≤ ∑ j∈J.attach, Cj j*X := Finset.sum_le_sum (fun j _ => hcell j)
    _ = (∑ j∈J.attach, Cj j)*X := (Finset.sum_mul _ _ _).symm
    _ ≤ C*X := by dsimp only [C]; nlinarith

theorem negative_first_derivative_point
    {σ δ z : ℝ} {P : ℕ} {F : ℝ → ℝ}
    (hF : IsApproximateModelPhaseFunction F σ P δ)
    (hz : z∈Ioo (1:ℝ) 2) :
    let G := fun u => -σ⁻¹*iteratedDerivWithin 1 F phaseInterval u
    G z=-σ⁻¹*deriv F z ∧ deriv G z=-σ⁻¹*deriv (deriv F) z := by
  intro G
  have he : G =ᶠ[𝓝 z] (fun u => -σ⁻¹*deriv F u) := by
    filter_upwards [isOpen_Ioo.mem_nhds hz] with u hu
    dsimp [G]
    rw [iteratedDerivWithin_one]
    have hd : derivWithin F phaseInterval u=deriv F u :=
      derivWithin_of_mem_nhds (Icc_mem_nhds hu.1 hu.2)
    rw [hd]
  refine ⟨he.eq_of_nhds,?_⟩
  rw [he.deriv_eq]
  exact ((approximateModelPhase_deriv_contDiffAt hF hz).differentiableAt
    (by simp : (∞ : WithTop ℕ∞) ≠ 0)).hasDerivAt.const_mul (-σ⁻¹) |>.deriv

theorem original_derivative_resonance_displacement
    {σ δ T N x q : ℝ} {P : ℕ} {F : ℝ → ℝ} {K : ℤ}
    (hσ : 0 < σ) (hT : 0 < T) (hN : 0 < N) (hP : 1 ≤ P)
    (hδ : δ/σ ≤ min (modelPhaseCurvatureLower (σ+1)) 1)
    (hF : IsApproximateModelPhaseFunction F σ (P+1) δ)
    (hx : x/N∈Ioo (1:ℝ) 2) (hxq : (x+q)/N∈Ioo (1:ℝ) 2) :
    let f := fun z => T*F (z/N)
    let G := fun u => -σ⁻¹*iteratedDerivWithin 1 F phaseInterval u
    let κ := 2*(K:ℝ)*N^2/(σ*T)
    let V := σ*T/(2*N)
    let u := deriv G ((x+q)/N)
    (iteratedDeriv 2 f (x+q)-iteratedDeriv 2 f x)/2=(K:ℝ) →
    u∈modelPhaseSlopeRange G ∧ u+κ∈modelPhaseSlopeRange G ∧
      modelPhaseInverseSlope G u=(x+q)/N ∧
      modelPhaseInverseSlope G (u+κ)=x/N ∧
      N*(modelPhaseInverseSlope G u-modelPhaseInverseSlope G (u+κ))=q ∧
      V*κ/N=(K:ℝ) ∧
      V*(2*(G (modelPhaseInverseSlope G (u+κ))-G (modelPhaseInverseSlope G u)-
          κ*modelPhaseInverseSlope G (u+κ)))=
        iteratedDeriv 1 f (x+q)-iteratedDeriv 1 f x-2*(K:ℝ)*x := by
  intro f G κ V u hlevel
  have hG := negative_first_derivative_model hσ hF
  have hG₁ := approximateModelPhase_mono hG hP (le_refl (δ/σ))
  have hσ₁ : 0 < σ+1 := by linarith
  have hf : modelPhaseFrequencyPhase F T N 0=f := by
    funext z
    simp [modelPhaseFrequencyPhase,f]
  have hd (z : ℝ) (hz : z/N∈Ioo (1:ℝ) 2) :
      iteratedDeriv 1 f z=T/N*deriv F (z/N) ∧
      iteratedDeriv 2 f z=T/N^2*deriv (deriv F) (z/N) := by
    constructor
    · simpa only [hf,iteratedDeriv_one,sub_zero] using
        (modelPhaseFrequencyPhase_hasDerivAt (T:=T) (r:=0) hF hz).deriv
    · simpa only [hf,
        iteratedDeriv_succ,iteratedDeriv_zero] using
        (modelPhaseFrequencyPhase_secondDeriv (T:=T) (r:=0) hF hz)
  have hκeq : u+κ=deriv G (x/N) := by
    dsimp only [u]
    rw [(negative_first_derivative_point hF hxq).2,(negative_first_derivative_point hF hx).2]
    rw [(hd (x+q) hxq).2,(hd x hx).2] at hlevel
    dsimp only [κ]
    field_simp [hσ.ne',hT.ne',hN.ne'] at hlevel ⊢
    nlinarith only [hlevel]
  have hu : u∈modelPhaseSlopeRange G := ⟨(x+q)/N,hxq,rfl⟩
  have huk : u+κ∈modelPhaseSlopeRange G := by rw [hκeq]; exact ⟨x/N,hx,rfl⟩
  have hi : modelPhaseInverseSlope G u=(x+q)/N :=
    modelPhaseInverseSlope_deriv hσ₁ hδ hG₁ hxq
  have hik : modelPhaseInverseSlope G (u+κ)=x/N := by
    rw [hκeq]
    exact modelPhaseInverseSlope_deriv hσ₁ hδ hG₁ hx
  refine ⟨hu,huk,hi,hik,?_,?_,?_⟩
  · rw [hi,hik]
    field_simp
    ring
  · dsimp [V,κ]
    field_simp
  · have hGx : G (x/N)=-σ⁻¹*deriv F (x/N) := (negative_first_derivative_point hF hx).1
    have hGxq : G ((x+q)/N)=-σ⁻¹*deriv F ((x+q)/N) :=
      (negative_first_derivative_point hF hxq).1
    rw [hi,hik,hGx,hGxq,(hd (x+q) hxq).1,(hd x hx).1]
    dsimp [V,κ]
    field_simp
    ring

theorem original_second_level_near_curve_count
    {σ k₀ l₀ ε : ℝ} (hσ : 0 < σ)
    (hpair : ExponentPair k₀ l₀) (hε : 0 < ε) (hp : k₀+ε < 1) :
    ∃ δ κ₀ : ℝ, 0 < δ ∧ 0 < κ₀ ∧
      ∃ Q : ℕ, 2 ≤ Q ∧ ∃ C : ℝ, 1 ≤ C ∧
        ∀ (F : ℝ → ℝ) (T N D : ℝ) (K : ℤ) (S : Finset ℕ) (x : ℕ → ℝ),
          IsApproximateModelPhaseFunction F σ Q δ →
          0 < T → 0 < N → 0 < D → 0 < K →
          2*(K:ℝ)*N^2/(σ*T) ≤ κ₀ →
          (∀ n∈S, x n/N ∈ Ioo (1:ℝ) 2) →
          (∀ n∈S, (x n+(n:ℝ))/N ∈ Ioo (1:ℝ) 2) →
          (∀ n∈S, 2 ≤ (n:ℝ) ∧ (n:ℝ) ≤ 2*D) →
          let f := fun z => T*F (z/N)
          (∀ n∈S, (iteratedDeriv 2 f (x n+(n:ℝ))-iteratedDeriv 2 f (x n))/2=(K:ℝ)) →
          ∀ (W : ℝ), 0 < W → W ≤ 1/2 →
          (∀ n∈S, ∃ e : ℤ,
            |iteratedDeriv 1 f (x n+(n:ℝ))-iteratedDeriv 1 f (x n)-
              2*(K:ℝ)*x n-(e:ℝ)| ≤ W/2) →
            (S.card:ℝ) ≤ C*(W*D+(T/N^2)^(k₀+ε)*D^(l₀+ε)*W^(-(k₀+ε))+N^2/T) := by
  have hσ₁ : 0 < σ+1 := by linarith
  obtain ⟨δ₀,κ₀,hδ₀,hκ₀,Q,hQ,C₀,hC₀,hcount⟩ :=
    actual_displacement_near_curve_count hσ₁ hpair hε hp
  let δg := min δ₀ (min (modelPhaseCurvatureLower (σ+1)) 1)
  let δ := σ*δg
  let p := k₀+ε
  let a := (σ/2)^p
  let b := 2/σ
  let L := 1+a+b
  let C := C₀*L
  have hδg : 0 < δg := lt_min hδ₀
    (lt_min (modelPhaseCurvatureLower_pos hσ₁) zero_lt_one)
  have hδ : 0 < δ := mul_pos hσ hδg
  have hquot : δ/σ=δg := by dsimp [δ]; field_simp
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have hb : 0 ≤ b := by dsimp [b]; positivity
  have hL : 1 ≤ L := by dsimp [L]; linarith
  have hC : 1 ≤ C := by
    dsimp [C]
    nlinarith [mul_nonneg (sub_nonneg.mpr hC₀) (sub_nonneg.mpr hL)]
  refine ⟨δ,κ₀,hδ,hκ₀,Q+1,by omega,C,hC,?_⟩
  intro F T N D K S x hF hT hN hD hK hκle hx hxq hbox f hlevel W hW hWhalf hnear
  let G := fun u => -σ⁻¹*iteratedDerivWithin 1 F phaseInterval u
  let κ := 2*(K:ℝ)*N^2/(σ*T)
  let V := σ*T/(2*N)
  let u := fun n => deriv G ((x n+(n:ℝ))/N)
  have hκ : 0 < κ := by
    have hKr : 0 < (K:ℝ) := by exact_mod_cast hK
    dsimp [κ]
    positivity
  have hV : 0 < V := by dsimp [V]; positivity
  have hG : IsApproximateModelPhaseFunction G (σ+1) Q δ₀ := by
    have hh := negative_first_derivative_model hσ hF
    rw [hquot] at hh
    exact approximateModelPhase_mono hh le_rfl (min_le_left _ _)
  have hgeom (n : ℕ) (hns : n∈S) :=
    original_derivative_resonance_displacement hσ hT hN hQ
      (by rw [hquot]; exact min_le_right _ _)
      hF (hx n hns) (hxq n hns) (hlevel n hns)
  have hu : ∀ n∈S, u n∈modelPhaseSlopeRange G := fun n hns => (hgeom n hns).1
  have huk : ∀ n∈S, u n+κ∈modelPhaseSlopeRange G := fun n hns => (hgeom n hns).2.1
  have hdis : ∀ n∈S, N*(modelPhaseInverseSlope G (u n)-modelPhaseInverseSlope G (u n+κ))=(n:ℝ) :=
    fun n hns => (hgeom n hns).2.2.2.2.1
  have hres : V*κ/N=(K:ℝ) := by dsimp [V,κ]; field_simp
  have hnear' : ∀ n∈S, ∃ e : ℤ,
      |V*(2*(G (modelPhaseInverseSlope G (u n+κ))-G (modelPhaseInverseSlope G (u n))-
          κ*modelPhaseInverseSlope G (u n+κ)))-(e:ℝ)| ≤ W/2 := by
    intro n hns
    have hh := (hgeom n hns).2.2.2.2.2.2
    change V*(2*(G (modelPhaseInverseSlope G (u n+κ))-G (modelPhaseInverseSlope G (u n))-
      κ*modelPhaseInverseSlope G (u n+κ)))=
        iteratedDeriv 1 f (x n+(n:ℝ))-iteratedDeriv 1 f (x n)-2*(K:ℝ)*x n at hh
    rw [hh]
    exact hnear n hns
  have hh := hcount G κ N V D K S u hG hκ hκle hN hV hD hu huk hbox hres hdis W hW hWhalf hnear'
  have hfreq : (V/N)^p=a*(T/N^2)^p := by
    have he : V/N=(σ/2)*(T/N^2) := by dsimp [V]; field_simp
    rw [he,Real.mul_rpow (by positivity : 0 ≤ σ/2) (by positivity : 0 ≤ T/N^2)]
  have htail : N/V=b*(N^2/T) := by dsimp [V,b]; field_simp
  change (S.card:ℝ) ≤ C₀*(W*D+(V/N)^p*D^(l₀+ε)*W^(-p)+N/V) at hh
  rw [hfreq,htail] at hh
  have haL : a ≤ L := by dsimp [L]; linarith
  have hbL : b ≤ L := by dsimp [L]; linarith
  have hv : W*D ≤ L*(W*D) := le_mul_of_one_le_left (by positivity) hL
  calc
    _ ≤ C₀*(W*D+a*((T/N^2)^p*D^(l₀+ε)*W^(-p))+b*(N^2/T)) := by
      convert hh using 1; ring
    _ ≤ C₀*(L*(W*D)+L*((T/N^2)^p*D^(l₀+ε)*W^(-p))+L*(N^2/T)) := by gcongr
    _ = _ := by dsimp [C,p]; ring

theorem cubic_second_difference_derivative
    (f : ℝ → ℝ) {x q B lam : ℝ} (hq : 0 < q)
    (hf : ∀ t∈Icc x (x+q), ContDiffAt ℝ 4 f t)
    (hfour : ∀ t∈Icc x (x+q),
      -B ≤ iteratedDeriv 4 f t ∧ iteratedDeriv 4 f t ≤ -lam) :
    HasDerivAt (fun t => (iteratedDeriv 2 f (t+q)-iteratedDeriv 2 f t)/2)
      ((iteratedDeriv 3 f (x+q)-iteratedDeriv 3 f x)/2) x ∧
    -(B*q/2) ≤ (iteratedDeriv 3 f (x+q)-iteratedDeriv 3 f x)/2 ∧
      (iteratedDeriv 3 f (x+q)-iteratedDeriv 3 f x)/2 ≤ -(lam*q/2) := by
  have hxx : x ≤ x+q := by linarith
  have hd (t : ℝ) (ht : t∈Icc x (x+q)) :
      HasDerivAt (iteratedDeriv 3 f) (iteratedDeriv 4 f t) t :=
    hasDerivAt_iteratedDeriv_finite (j:=3) (by norm_num : 3 < 4) (hf t ht)
  have hd₀ := hasDerivAt_iteratedDeriv_finite (j:=2) (by norm_num : 2 < 4)
    (hf x ⟨le_rfl,hxx⟩)
  have hd₁ := hasDerivAt_iteratedDeriv_finite (j:=2) (by norm_num : 2 < 4)
    (hf (x+q) ⟨hxx,le_rfl⟩)
  constructor
  · convert ((hd₁.comp x ((hasDerivAt_id x).add_const q)).sub hd₀).div_const 2 using 1; ring
  obtain ⟨t,ht,he⟩ := exists_hasDerivAt_eq_slope (iteratedDeriv 3 f)
    (iteratedDeriv 4 f) (show x < x+q by linarith)
    (fun t ht => (hd t ht).continuousAt.continuousWithinAt)
    (fun t ht => hd t ⟨ht.1.le,ht.2.le⟩)
  have he' : iteratedDeriv 4 f t*q=iteratedDeriv 3 f (x+q)-iteratedDeriv 3 f x := by
    have hh := (eq_div_iff (show x+q-x ≠ 0 by linarith)).mp he
    nlinarith only [hh]
  have hlo := mul_le_mul_of_nonneg_right (hfour t ⟨ht.1.le,ht.2.le⟩).1 hq.le
  have hhi := mul_le_mul_of_nonneg_right (hfour t ⟨ht.1.le,ht.2.le⟩).2 hq.le
  constructor <;> nlinarith only [he',hlo,hhi]

theorem cubic_exact_second_difference_level
    (f : ℝ → ℝ) {n q B lam R δ K : ℝ}
    (hq : 0 < q) (hR : 0 < R)
    (hbudget : δ ≤ lam*q*R/2)
    (hf : ∀ t∈Icc (n-R) (n+R+q), ContDiffAt ℝ 4 f t)
    (hfour : ∀ t∈Icc (n-R) (n+R+q),
      -B ≤ iteratedDeriv 4 f t ∧ iteratedDeriv 4 f t ≤ -lam)
    (hnear : |(iteratedDeriv 2 f (n+q)-iteratedDeriv 2 f n)/2-K| ≤ δ) :
    ∃ x∈Icc (n-R) (n+R),
      (iteratedDeriv 2 f (x+q)-iteratedDeriv 2 f x)/2=K ∧ |x-n| ≤ R := by
  let g := fun t => (iteratedDeriv 2 f (t+q)-iteratedDeriv 2 f t)/2
  let dg := fun t => (iteratedDeriv 3 f (t+q)-iteratedDeriv 3 f t)/2
  have hsub (x : ℝ) (hx : x∈Icc (n-R) (n+R)) :
      Icc x (x+q) ⊆ Icc (n-R) (n+R+q) := by
    intro t ht
    constructor <;> linarith [hx.1,hx.2,ht.1,ht.2]
  have hd (x : ℝ) (hx : x∈Icc (n-R) (n+R)) :
      HasDerivAt g (dg x) x ∧ dg x ≤ -(lam*q/2) := by
    have hh := cubic_second_difference_derivative f hq
      (fun t ht => hf t (hsub x hx ht)) (fun t ht => hfour t (hsub x hx ht))
    exact ⟨hh.1,hh.2.2⟩
  have hdec {a b : ℝ} (hab : a < b)
      (ha : n-R ≤ a) (hb : b ≤ n+R) :
      g b-g a ≤ -(lam*q/2)*(b-a) := by
    have hi (t : ℝ) (ht : t∈Icc a b) : t∈Icc (n-R) (n+R) :=
      ⟨ha.trans ht.1,ht.2.trans hb⟩
    obtain ⟨t,ht,he⟩ := exists_hasDerivAt_eq_slope g dg hab
      (fun t ht => (hd t (hi t ht)).1.continuousAt.continuousWithinAt)
      (fun t ht => (hd t (hi t ⟨ht.1.le,ht.2.le⟩)).1)
    have he' := (eq_div_iff (sub_pos.mpr hab).ne').mp he
    have hh := mul_le_mul_of_nonneg_right (hd t (hi t ⟨ht.1.le,ht.2.le⟩)).2
      (sub_nonneg.mpr hab.le)
    nlinarith only [he',hh]
  have hleft := hdec (a:=n-R) (b:=n) (by linarith) le_rfl (by linarith)
  have hright := hdec (a:=n) (b:=n+R) (by linarith) (by linarith) le_rfl
  have hnear' : |g n-K| ≤ δ := hnear
  have hK : K∈Icc (g (n+R)) (g (n-R)) := by
    have hh := abs_le.mp hnear'
    constructor <;> nlinarith only [hleft,hright,hbudget,hh.1,hh.2]
  obtain ⟨x,hx,he⟩ := intermediate_value_Icc' (by linarith : n-R ≤ n+R)
    (fun t ht => (hd t ht).1.continuousAt.continuousWithinAt) hK
  exact ⟨x,hx,he,abs_le.mpr ⟨by linarith [hx.1],by linarith [hx.2]⟩⟩

theorem cubic_stationary_curve_near_integer
    (f : ℝ → ℝ) (n K e : ℤ) {x q B lam R δ : ℝ}
    (hq : 0 < q) (hlam : 0 < lam) (hR : 0 ≤ R)
    (hx : x∈Icc ((n:ℝ)-R) ((n:ℝ)+R))
    (hf : ∀ t∈Icc ((n:ℝ)-R) ((n:ℝ)+R+q), ContDiffAt ℝ 4 f t)
    (hfour : ∀ t∈Icc ((n:ℝ)-R) ((n:ℝ)+R+q),
      -B ≤ iteratedDeriv 4 f t ∧ iteratedDeriv 4 f t ≤ -lam)
    (hlevel : (iteratedDeriv 2 f (x+q)-iteratedDeriv 2 f x)/2=(K:ℝ))
    (hnear : |iteratedDeriv 1 f ((n:ℝ)+q)-iteratedDeriv 1 f n-(e:ℝ)| ≤ δ) :
    |(iteratedDeriv 1 f (x+q)-iteratedDeriv 1 f x-2*(K:ℝ)*x)-
      ((e-2*K*n:ℤ):ℝ)| ≤ δ+B*q*R^2 := by
  let G := fun t => iteratedDeriv 1 f (t+q)-iteratedDeriv 1 f t-2*(K:ℝ)*t
  let G₁ := fun t => iteratedDeriv 2 f (t+q)-iteratedDeriv 2 f t-2*(K:ℝ)
  let G₂ := fun t => iteratedDeriv 3 f (t+q)-iteratedDeriv 3 f t
  have hsub (t : ℝ) (ht : t∈uIcc x (n:ℝ)) : t∈Icc ((n:ℝ)-R) ((n:ℝ)+R) :=
    (convex_Icc _ _).ordConnected.uIcc_subset hx ⟨by linarith,by linarith⟩ ht
  have hseg (t : ℝ) (ht : t∈uIcc x (n:ℝ)) :
      Icc t (t+q) ⊆ Icc ((n:ℝ)-R) ((n:ℝ)+R+q) := by
    intro z hz
    have hh := hsub t ht
    constructor <;> linarith [hh.1,hh.2,hz.1,hz.2]
  have hjets (t : ℝ) (ht : t∈uIcc x (n:ℝ)) :
      HasDerivAt G (G₁ t) t ∧ HasDerivAt G₁ (G₂ t) t ∧ |G₂ t| ≤ B*q := by
    have hI := hseg t ht
    have ht₀ := hf t (hI ⟨le_rfl,by linarith⟩)
    have ht₁ := hf (t+q) (hI ⟨by linarith,le_rfl⟩)
    have hd (j : ℕ) (hj : j < 4) :
        HasDerivAt (fun z => iteratedDeriv j f (z+q)-iteratedDeriv j f z)
          (iteratedDeriv (j+1) f (t+q)-iteratedDeriv (j+1) f t) t := by
      have h₀ := hasDerivAt_iteratedDeriv_finite hj ht₀
      have h₁ := hasDerivAt_iteratedDeriv_finite hj ht₁
      convert (h₁.comp t ((hasDerivAt_id t).add_const q)).sub h₀ using 1; ring
    constructor
    · convert (hd 1 (by norm_num)).sub ((hasDerivAt_id t).const_mul (2*(K:ℝ))) using 1; ring
    constructor
    · exact (hd 2 (by norm_num)).sub_const (2*(K:ℝ))
    · have hh := cubic_second_difference_derivative f hq
        (fun z hz => hf z (hI hz)) (fun z hz => hfour z (hI hz))
      dsimp only [G₂]
      apply abs_le.mpr
      constructor <;> nlinarith [hh.2.1,hh.2.2,mul_pos hlam hq]
  have hB : 0 ≤ B := by
    have hh := hfour n ⟨by linarith,by linarith⟩
    linarith [hh.1,hh.2]
  have hG₁x : G₁ x=0 := by dsimp only [G₁]; linarith only [hlevel]
  have hdist : |(n:ℝ)-x| ≤ R := by
    apply abs_le.mpr
    constructor <;> linarith [hx.1,hx.2]
  have hfirst (t : ℝ) (ht : t∈uIcc x (n:ℝ)) : |G₁ t| ≤ B*q*R := by
    have hh := (convex_uIcc x (n:ℝ)).norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun z hz => (hjets z hz).2.1.hasDerivWithinAt)
      (fun z hz => by simpa only [Real.norm_eq_abs] using (hjets z hz).2.2)
      left_mem_uIcc ht
    rw [hG₁x,sub_zero,Real.norm_eq_abs,Real.norm_eq_abs] at hh
    exact hh.trans (mul_le_mul_of_nonneg_left
      ((abs_sub_left_of_mem_uIcc ht).trans hdist) (mul_nonneg hB hq.le))
  have herror := (convex_uIcc x (n:ℝ)).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun z hz => (hjets z hz).1.hasDerivWithinAt)
    (fun z hz => by simpa only [Real.norm_eq_abs] using hfirst z hz)
    left_mem_uIcc right_mem_uIcc
  rw [Real.norm_eq_abs,Real.norm_eq_abs] at herror
  have herror' : |G x-G n| ≤ B*q*R^2 := by
    rw [abs_sub_comm]
    exact herror.trans ((mul_le_mul_of_nonneg_left hdist (by positivity : 0 ≤ B*q*R)).trans_eq (by ring))
  have hnear' : |G n-((e-2*K*n:ℤ):ℝ)| ≤ δ := by
    convert hnear using 1
    congr 1
    dsimp only [G]
    push_cast
    ring
  have hh := (abs_sub_le (G x) (G n) ((e-2*K*n:ℤ):ℝ)).trans (add_le_add herror' hnear')
  change |G x-((e-2*K*n:ℤ):ℝ)| ≤ _
  exact hh.trans_eq (by ring)

theorem cubicDerivativePairs_integer_resonances
    (f : ℝ → ℝ) {M H : ℕ} {p : ℕ × ℕ}
    (hp : p∈cubicDerivativePairs f M H) :
    p.1 < M ∧ p.2 < M ∧
    ∃ e K : ℤ,
      |iteratedDeriv 1 f ((p.2:ℝ)+1)-iteratedDeriv 1 f ((p.1:ℝ)+1)-(e:ℝ)| ≤ 1/(4*(H:ℝ)) ∧
      |(iteratedDeriv 2 f ((p.2:ℝ)+1)-iteratedDeriv 2 f ((p.1:ℝ)+1))/2-(K:ℝ)| ≤
        1/(4*(H:ℝ)^2) ∧
      |iteratedDeriv 3 f ((p.2:ℝ)+1)-iteratedDeriv 3 f ((p.1:ℝ)+1)| ≤
        3/(2*(H:ℝ)^3) := by
  obtain ⟨hmem,hnear⟩ := Finset.mem_filter.mp hp
  have hmem' := Finset.mem_product.mp hmem
  refine ⟨Finset.mem_range.mp hmem'.1,Finset.mem_range.mp hmem'.2,
    ⌊deriv f ((p.2:ℝ)+1)⌋-⌊deriv f ((p.1:ℝ)+1)⌋,
    ⌊iteratedDeriv 2 f ((p.2:ℝ)+1)/2⌋-⌊iteratedDeriv 2 f ((p.1:ℝ)+1)/2⌋,
    ?_,?_,?_⟩
  · have hh := hnear 0
    change |Int.fract (deriv f ((p.1:ℝ)+1))-Int.fract (deriv f ((p.2:ℝ)+1))| ≤
      2*(1/(8*(H:ℝ))) at hh
    rw [abs_sub_comm] at hh
    convert hh using 1
    · congr 1
      simp only [Int.fract,Int.cast_sub,iteratedDeriv_one]
      ring
    · ring
  · have hh := hnear 1
    change |Int.fract (iteratedDeriv 2 f ((p.1:ℝ)+1)/2)-
      Int.fract (iteratedDeriv 2 f ((p.2:ℝ)+1)/2)| ≤ 2*(1/(8*(H:ℝ)^2)) at hh
    rw [abs_sub_comm] at hh
    convert hh using 1
    · congr 1
      simp only [Int.fract,Int.cast_sub]
      ring
    · ring
  · have hh := hnear 2
    change |iteratedDeriv 3 f ((p.1:ℝ)+1)/6-iteratedDeriv 3 f ((p.2:ℝ)+1)/6| ≤
      2*(1/(8*(H:ℝ)^3)) at hh
    rw [abs_sub_comm,←sub_div,abs_div,abs_of_pos (by norm_num : (0:ℝ)<6)] at hh
    have he := (div_le_iff₀ (by norm_num : (0:ℝ)<6)).mp hh
    exact he.trans_eq (by ring)

theorem cubicDerivativePairs_displacement
    (f : ℝ → ℝ) {M H : ℕ} {p : ℕ × ℕ} {lam : ℝ}
    (hH : 1 ≤ H) (hlam : 0 < lam)
    (hp : p∈cubicDerivativePairs f M H) (hlt : p.1 < p.2)
    (hf : ∀ t∈Icc ((p.1:ℝ)+1) ((p.2:ℝ)+1), ContDiffAt ℝ 4 f t)
    (hfour : ∀ t∈Icc ((p.1:ℝ)+1) ((p.2:ℝ)+1), iteratedDeriv 4 f t ≤ -lam) :
    (p.2:ℝ)-p.1 ≤ 3/(2*lam*(H:ℝ)^3) := by
  obtain ⟨_,_,e,K,_hfirst,_hsecond,hthird⟩ := cubicDerivativePairs_integer_resonances f hp
  have hHpos : (0:ℝ) < H := by exact_mod_cast (show 0 < H by omega)
  have hxy : (p.1:ℝ)+1 < (p.2:ℝ)+1 := by exact_mod_cast Nat.add_lt_add_right hlt 1
  have hd (t : ℝ) (ht : t∈Icc ((p.1:ℝ)+1) ((p.2:ℝ)+1)) :
      HasDerivAt (iteratedDeriv 3 f) (iteratedDeriv 4 f t) t :=
    hasDerivAt_iteratedDeriv_finite (j:=3) (by norm_num : 3 < 4) (hf t ht)
  obtain ⟨t,ht,he⟩ := exists_hasDerivAt_eq_slope (iteratedDeriv 3 f)
    (iteratedDeriv 4 f) hxy
    (fun t ht => (hd t ht).continuousAt.continuousWithinAt)
    (fun t ht => hd t ⟨ht.1.le,ht.2.le⟩)
  have he' := (eq_div_iff (sub_pos.mpr hxy).ne').mp he
  have hlow := mul_le_mul_of_nonneg_right (hfour t ⟨ht.1.le,ht.2.le⟩) (sub_pos.mpr hxy).le
  have hprod : lam*((p.2:ℝ)-p.1) ≤ 3/(2*(H:ℝ)^3) := by
    have hab := abs_le.mp hthird
    nlinarith only [he',hlow,hab.1]
  have hh : (p.2:ℝ)-p.1 ≤ (3/(2*(H:ℝ)^3))/lam :=
    (le_div_iff₀ hlam).mpr (by nlinarith only [hprod])
  exact hh.trans_eq (by ring)

theorem cubic_second_difference_fiber_card
    (f : ℝ → ℝ) (S : Finset ℤ) {a b q B lam δ K : ℝ}
    (hq : 0 < q) (hlam : 0 < lam) (hδ : 0 ≤ δ)
    (hf : ∀ t∈Icc a (b+q), ContDiffAt ℝ 4 f t)
    (hfour : ∀ t∈Icc a (b+q),
      -B ≤ iteratedDeriv 4 f t ∧ iteratedDeriv 4 f t ≤ -lam)
    (hS : ∀ n∈S, (n:ℝ)∈Icc a b)
    (hnear : ∀ n∈S, |(iteratedDeriv 2 f ((n:ℝ)+q)-iteratedDeriv 2 f n)/2-K| ≤ δ) :
    (S.card:ℝ) ≤ 4*δ/(lam*q)+1 := by
  classical
  by_cases hne : S.Nonempty
  · let n₀ := S.min' hne
    have hn₀ : n₀∈S := Finset.min'_mem S hne
    let g := fun t => (iteratedDeriv 2 f (t+q)-iteratedDeriv 2 f t)/2
    let dg := fun t => (iteratedDeriv 3 f (t+q)-iteratedDeriv 3 f t)/2
    have hd (t : ℝ) (ht : t∈Icc a b) : HasDerivAt g (dg t) t ∧ dg t ≤ -(lam*q/2) := by
      have hsub : Icc t (t+q) ⊆ Icc a (b+q) := by
        intro z hz
        constructor <;> linarith [ht.1,ht.2,hz.1,hz.2]
      have hh := cubic_second_difference_derivative f hq
        (fun z hz => hf z (hsub hz)) (fun z hz => hfour z (hsub hz))
      exact ⟨hh.1,hh.2.2⟩
    have hbound (n : ℤ) (hn : n∈S) :
        (n₀:ℝ) ≤ n ∧ (n:ℝ) ≤ n₀+4*δ/(lam*q) := by
      have hle : n₀ ≤ n := Finset.min'_le S n hn
      have hleR : (n₀:ℝ) ≤ n := by exact_mod_cast hle
      refine ⟨hleR,?_⟩
      rcases eq_or_lt_of_le hleR with heq|hlt
      · rw [←heq]
        exact le_add_of_nonneg_right (by positivity)
      have hsub (t : ℝ) (ht : t∈Icc (n₀:ℝ) n) : t∈Icc a b :=
        ⟨(hS n₀ hn₀).1.trans ht.1,ht.2.trans (hS n hn).2⟩
      obtain ⟨t,ht,he⟩ := exists_hasDerivAt_eq_slope g dg hlt
        (fun t ht => (hd t (hsub t ht)).1.continuousAt.continuousWithinAt)
        (fun t ht => (hd t (hsub t ⟨ht.1.le,ht.2.le⟩)).1)
      have he' := (eq_div_iff (sub_pos.mpr hlt).ne').mp he
      have hdec := mul_le_mul_of_nonneg_right (hd t (hsub t ⟨ht.1.le,ht.2.le⟩)).2
        (sub_pos.mpr hlt).le
      have hnear₀ : |g n₀-K| ≤ δ := hnear n₀ hn₀
      have hnear₁ : |g n-K| ≤ δ := hnear n hn
      have hp : ((n:ℝ)-n₀)*(lam*q) ≤ 4*δ := by
        have hh₀ := abs_le.mp hnear₀
        have hh₁ := abs_le.mp hnear₁
        nlinarith only [he',hdec,hh₀.2,hh₁.1]
      have hh := (le_div_iff₀ (mul_pos hlam hq)).mpr hp
      linarith
    have hinterval : (n₀:ℝ) ≤ n₀+4*δ/(lam*q) :=
      le_add_of_nonneg_right (by positivity)
    have hcount := integer_card_le_interval_length_add_one S hinterval
      hbound
    exact hcount.trans_eq (by ring)
  · have he : S=∅ := Finset.not_nonempty_iff_eq_empty.mp hne
    simp only [he,Finset.card_empty,Nat.cast_zero]
    positivity

theorem cubic_second_level_positive
    (f : ℝ → ℝ) (K : ℤ) {n q L U δ : ℝ}
    (hq : 1 ≤ q) (hL : 0 < L)
    (hδL : δ ≤ L/4) (hδhalf : δ ≤ 1/2)
    (hf : ∀ t∈Icc n (n+q), ContDiffAt ℝ 3 f t)
    (hthree : ∀ t∈Icc n (n+q),
      L ≤ iteratedDeriv 3 f t ∧ iteratedDeriv 3 f t ≤ U)
    (hnear : |(iteratedDeriv 2 f (n+q)-iteratedDeriv 2 f n)/2-(K:ℝ)| ≤ δ) :
    0 < K ∧ 0 < U ∧ 1/U ≤ q ∧ (K:ℝ) ≤ U*q := by
  have hqpos : 0 < q := zero_lt_one.trans_le hq
  have hU : 0 < U := hL.trans_le ((hthree n ⟨le_rfl,by linarith⟩).1.trans
    (hthree n ⟨le_rfl,by linarith⟩).2)
  have hd (t : ℝ) (ht : t∈Icc n (n+q)) :
      HasDerivAt (iteratedDeriv 2 f) (iteratedDeriv 3 f t) t :=
    hasDerivAt_iteratedDeriv_finite (j:=2) (by norm_num : 2 < 3) (hf t ht)
  obtain ⟨t,ht,he⟩ := exists_hasDerivAt_eq_slope (iteratedDeriv 2 f)
    (iteratedDeriv 3 f) (show n < n+q by linarith)
    (fun t ht => (hd t ht).continuousAt.continuousWithinAt)
    (fun t ht => hd t ⟨ht.1.le,ht.2.le⟩)
  have he' := (eq_div_iff (show n+q-n ≠ 0 by linarith)).mp he
  have hlo := mul_le_mul_of_nonneg_right (hthree t ⟨ht.1.le,ht.2.le⟩).1 hqpos.le
  have hhi := mul_le_mul_of_nonneg_right (hthree t ⟨ht.1.le,ht.2.le⟩).2 hqpos.le
  have hab := abs_le.mp hnear
  have hLq : L ≤ L*q := by nlinarith only [mul_le_mul_of_nonneg_left hq hL.le]
  have hKpos : (0:ℝ) < K := by nlinarith only [he',hlo,hab.2,hδL,hLq,hL]
  have hKi : 0 < K := by exact_mod_cast hKpos
  have hK1 : (1:ℝ) ≤ K := by exact_mod_cast (show (1:ℤ) ≤ K by omega)
  refine ⟨hKi,hU,?_,?_⟩
  · apply (div_le_iff₀ hU).mpr
    nlinarith only [he',hhi,hab.1,hδhalf,hK1]
  · have hLU : L ≤ U := (hthree t ⟨ht.1.le,ht.2.le⟩).1.trans
      (hthree t ⟨ht.1.le,ht.2.le⟩).2
    have hUq : U ≤ U*q := by nlinarith only [mul_le_mul_of_nonneg_left hq hU.le]
    nlinarith only [he',hhi,hab.1,hδL,hLU,hUq,hU]

theorem original_joint_level_block_count
    {σ k₀ l₀ ε : ℝ} (hσ : 0 < σ)
    (hpair : ExponentPair k₀ l₀) (hε : 0 < ε) (hp : k₀+ε < 1) :
    ∃ δ κ₀ : ℝ, 0 < δ ∧ 0 < κ₀ ∧
      ∃ Q : ℕ, 2 ≤ Q ∧ ∃ C : ℝ, 1 ≤ C ∧
        ∀ (F : ℝ → ℝ) (T N D a b R B lam δ₁ δ₂ W : ℝ)
          (K : ℤ) (S : Finset (ℤ × ℕ)),
          IsApproximateModelPhaseFunction F σ Q δ →
          0 < T → 0 < N → 2 ≤ D → 0 < R → 0 ≤ B → 0 < lam → 0 ≤ δ₂ →
          N < a-R → b+R+2*D < 2*N →
          δ₂ ≤ lam*D*R/2 → δ₁+2*B*D*R^2 ≤ W/2 →
          0 < K → 2*(K:ℝ)*N^2/(σ*T) ≤ κ₀ → 0 < W → W ≤ 1/2 →
          let f := fun z => T*F (z/N)
          (∀ t∈Icc (a-R) (b+R+2*D),
            -B ≤ iteratedDeriv 4 f t ∧ iteratedDeriv 4 f t ≤ -lam) →
          (∀ p∈S, (p.1:ℝ)∈Icc a b ∧ (p.2:ℝ)∈Icc D (2*D)) →
          (∀ p∈S, |(iteratedDeriv 2 f ((p.1:ℝ)+(p.2:ℝ))-
            iteratedDeriv 2 f p.1)/2-(K:ℝ)| ≤ δ₂) →
          (∀ p∈S, ∃ e : ℤ, |iteratedDeriv 1 f ((p.1:ℝ)+(p.2:ℝ))-
            iteratedDeriv 1 f p.1-(e:ℝ)| ≤ δ₁) →
            (S.card:ℝ) ≤ (4*δ₂/(lam*D)+1)*
              (C*(W*D+(T/N^2)^(k₀+ε)*D^(l₀+ε)*W^(-(k₀+ε))+N^2/T)) := by
  classical
  obtain ⟨δ,κ₀,hδ,hκ₀,Q,hQ,C,hC,hcount⟩ :=
    original_second_level_near_curve_count hσ hpair hε hp
  refine ⟨δ,κ₀,hδ,hκ₀,Q,hQ,C,hC,?_⟩
  intro F T N D a b R B lam δ₁ δ₂ W K S hF hT hN hD hR hB hlam hδ₂
    hleft hright hbuffer hwidth hK hκle hW hWhalf f hfour hbox hsecond hfirst
  have hDpos : 0 < D := by linarith
  let J := S.image Prod.snd
  have hmem (q : ℕ) (hq : q∈J) : D ≤ (q:ℝ) ∧ (q:ℝ) ≤ 2*D := by
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hq
    exact (hbox p hp).2
  have hnorm (t : ℝ) (ht : t∈Icc (a-R) (b+R+2*D)) :
      t/N∈Ioo (1:ℝ) 2 := by
    constructor
    · apply (one_lt_div hN).mpr
      linarith [ht.1]
    · apply (div_lt_iff₀ hN).mpr
      linarith [ht.2]
  have hf (t : ℝ) (ht : t∈Icc (a-R) (b+R+2*D)) : ContDiffAt ℝ 4 f t := by
    have hc := (approximateModelPhase_contDiffAt hF (hnorm t ht)).comp t
      (show ContDiffAt ℝ ∞ (fun z : ℝ => z/N) t by fun_prop)
    exact (contDiffAt_const.mul hc).of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 4)
  have hex (q : ℕ) (hq : q∈J) :
      ∃ x : ℝ, x/N∈Ioo (1:ℝ) 2 ∧ (x+(q:ℝ))/N∈Ioo (1:ℝ) 2 ∧
        (iteratedDeriv 2 f (x+(q:ℝ))-iteratedDeriv 2 f x)/2=(K:ℝ) ∧
        ∃ e : ℤ, |iteratedDeriv 1 f (x+(q:ℝ))-iteratedDeriv 1 f x-
          2*(K:ℝ)*x-(e:ℝ)| ≤ W/2 := by
    obtain ⟨p,hps,hpq⟩ := Finset.mem_image.mp hq
    have hpos : 0 < (q:ℝ) := hDpos.trans_le (hmem q hq).1
    have hpab : (p.1:ℝ)∈Icc a b := (hbox p hps).1
    have hsub : Icc ((p.1:ℝ)-R) ((p.1:ℝ)+R+(q:ℝ)) ⊆ Icc (a-R) (b+R+2*D) := by
      intro t ht
      constructor <;> linarith [ht.1,ht.2,hpab.1,hpab.2,(hmem q hq).2]
    have hbudget : δ₂ ≤ lam*(q:ℝ)*R/2 := hbuffer.trans (by gcongr; exact (hmem q hq).1)
    have hnear₂ : |(iteratedDeriv 2 f ((p.1:ℝ)+(q:ℝ))-iteratedDeriv 2 f p.1)/2-(K:ℝ)| ≤ δ₂ := by
      simpa only [hpq] using hsecond p hps
    obtain ⟨x,hx,hlevel,_hdist⟩ := cubic_exact_second_difference_level
      f hpos hR hbudget (fun t ht => hf t (hsub ht))
      (fun t ht => hfour t (hsub ht)) hnear₂
    obtain ⟨e,he⟩ := hfirst p hps
    rw [hpq] at he
    have hnear := cubic_stationary_curve_near_integer
      f p.1 K e hpos hlam hR.le hx (fun t ht => hf t (hsub ht))
      (fun t ht => hfour t (hsub ht)) hlevel he
    have hxx : x∈Icc (a-R) (b+R+2*D) := hsub ⟨hx.1,by linarith [hx.2]⟩
    have hxxq : x+(q:ℝ)∈Icc (a-R) (b+R+2*D) :=
      hsub ⟨by linarith [hx.1],by linarith [hx.2]⟩
    refine ⟨x,hnorm x hxx,hnorm (x+q) hxxq,hlevel,e-2*K*p.1,?_⟩
    exact hnear.trans ((show δ₁+B*(q:ℝ)*R^2 ≤ δ₁+2*B*D*R^2 by
      nlinarith [mul_le_mul_of_nonneg_left (hmem q hq).2
        (mul_nonneg hB (sq_nonneg R))]).trans hwidth)
  let x := fun q => if hq : q∈J then Classical.choose (hex q hq) else 0
  have hx (q : ℕ) (hq : q∈J) :
      x q/N∈Ioo (1:ℝ) 2 ∧ (x q+(q:ℝ))/N∈Ioo (1:ℝ) 2 ∧
        (iteratedDeriv 2 f (x q+(q:ℝ))-iteratedDeriv 2 f (x q))/2=(K:ℝ) ∧
        ∃ e : ℤ, |iteratedDeriv 1 f (x q+(q:ℝ))-iteratedDeriv 1 f (x q)-
          2*(K:ℝ)*x q-(e:ℝ)| ≤ W/2 := by
    simp only [x,dif_pos hq]
    exact Classical.choose_spec (hex q hq)
  have hcountJ := hcount F T N D K J x hF hT hN hDpos hK hκle
    (fun q hq => (hx q hq).1) (fun q hq => (hx q hq).2.1)
    (fun q hq => ⟨hD.trans (hmem q hq).1,(hmem q hq).2⟩)
    (fun q hq => (hx q hq).2.2.1) W hW hWhalf (fun q hq => (hx q hq).2.2.2)
  have hfiber (q : ℕ) (hq : q∈J) :
      ((S.filter (fun p => p.2=q)).card:ℝ) ≤ 4*δ₂/(lam*D)+1 := by
    let U := S.filter (fun p => p.2=q)
    let Y := U.image Prod.fst
    have hinj : Set.InjOn (Prod.fst : ℤ × ℕ → ℤ) U := by
      intro p hp r hr he
      exact Prod.ext he ((Finset.mem_filter.mp hp).2.trans (Finset.mem_filter.mp hr).2.symm)
    have hcard : Y.card=U.card := Finset.card_image_of_injOn hinj
    have hsub : Icc a (b+(q:ℝ)) ⊆ Icc (a-R) (b+R+2*D) := by
      intro t ht
      constructor <;> linarith [ht.1,ht.2,(hmem q hq).2]
    have hY : ∀ n∈Y, (n:ℝ)∈Icc a b := by
      intro n hn
      obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hn
      exact (hbox p (Finset.mem_filter.mp hp).1).1
    have hnear : ∀ n∈Y,
        |(iteratedDeriv 2 f ((n:ℝ)+(q:ℝ))-iteratedDeriv 2 f n)/2-(K:ℝ)| ≤ δ₂ := by
      intro n hn
      obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hn
      simpa only [(Finset.mem_filter.mp hp).2] using hsecond p (Finset.mem_filter.mp hp).1
    have hh := cubic_second_difference_fiber_card f Y
      (hDpos.trans_le (hmem q hq).1) hlam hδ₂
      (fun t ht => hf t (hsub ht)) (fun t ht => hfour t (hsub ht)) hY hnear
    rw [hcard] at hh
    have hquot : 4*δ₂/(lam*(q:ℝ)) ≤ 4*δ₂/(lam*D) :=
      div_le_div_of_nonneg_left (by positivity) (mul_pos hlam hDpos)
        (mul_le_mul_of_nonneg_left (hmem q hq).1 hlam.le)
    linarith only [hh,hquot]
  have hmaps : Set.MapsTo (Prod.snd : ℤ × ℕ → ℕ) S J := by
    intro p hp
    exact Finset.mem_image.mpr ⟨p,hp,rfl⟩
  have hcard : (S.card:ℝ)=∑ q∈J, ((S.filter (fun p => p.2=q)).card:ℝ) := by
    exact_mod_cast Finset.card_eq_sum_card_fiberwise hmaps
  calc
    _ = _ := hcard
    _ ≤ ∑ _q∈J, (4*δ₂/(lam*D)+1) := Finset.sum_le_sum hfiber
    _ = (4*δ₂/(lam*D)+1)*(J.card:ℝ) := by
      simp only [Finset.sum_const,nsmul_eq_mul]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hcountJ (by positivity)

theorem original_joint_dyadic_block_count
    {σ k₀ l₀ ε : ℝ} (hσ : 0 < σ)
    (hpair : ExponentPair k₀ l₀) (hε : 0 < ε) (hp : k₀+ε < 1) :
    ∃ δ κ₀ : ℝ, 0 < δ ∧ 0 < κ₀ ∧
      ∃ Q : ℕ, 3 ≤ Q ∧ ∃ C : ℝ, 1 ≤ C ∧
        ∀ (F : ℝ → ℝ) (T N D a b R δ₁ δ₂ W : ℝ) (S : Finset (ℤ × ℕ)),
          IsApproximateModelPhaseFunction F σ Q δ →
          0 < T → 0 < N → 2 ≤ D → 0 < R → 0 ≤ δ₂ →
          N < a-R → b+R+2*D < 2*N →
          let lam := modelPhaseJetLower σ 3*T/N^4
          let B := (modelPhaseJetCoefficient σ 3+1)*T/N^4
          let L := modelPhaseJetLower σ 2*T/N^3
          let U := (modelPhaseJetCoefficient σ 2+1)*T/N^3
          δ₂ ≤ lam*D*R/2 → δ₁+2*B*D*R^2 ≤ W/2 →
          δ₂ ≤ L/4 → δ₂ ≤ 1/2 →
          4*U*D*N^2/(σ*T) ≤ κ₀ → 0 < W → W ≤ 1/2 →
          let f := fun z => T*F (z/N)
          (∀ p∈S, (p.1:ℝ)∈Icc a b ∧ (p.2:ℝ)∈Icc D (2*D)) →
          (∀ p∈S, ∃ K : ℤ, |(iteratedDeriv 2 f ((p.1:ℝ)+(p.2:ℝ))-
            iteratedDeriv 2 f p.1)/2-(K:ℝ)| ≤ δ₂) →
          (∀ p∈S, ∃ e : ℤ, |iteratedDeriv 1 f ((p.1:ℝ)+(p.2:ℝ))-
            iteratedDeriv 1 f p.1-(e:ℝ)| ≤ δ₁) →
            (S.card:ℝ) ≤ (2*U*D)*(4*δ₂/(lam*D)+1)*
              (C*(W*D+(T/N^2)^(k₀+ε)*D^(l₀+ε)*W^(-(k₀+ε))+N^2/T)) := by
  classical
  obtain ⟨δ₀,κ₀,hδ₀,hκ₀,Q₀,hQ₀,C,hC,hcount⟩ :=
    original_joint_level_block_count hσ hpair hε hp
  obtain ⟨δd,hδd,hdata⟩ := model_displacement_derivative_data hσ
  let δ := min δ₀ δd
  let Q := max Q₀ 3
  refine ⟨δ,κ₀,lt_min hδ₀ hδd,hκ₀,Q,le_max_right _ _,C,hC,?_⟩
  intro F T N D a b R δ₁ δ₂ W S hF hT hN hD hR hδ₂ hleft hright
    lam B L U hbuffer hwidth hδL hδhalf hshift hW hWhalf f hbox hsecond hfirst
  have hF₀ := approximateModelPhase_mono hF (le_max_left _ _) (min_le_left _ _)
  have hFd := approximateModelPhase_mono hF (le_max_right _ _) (min_le_right _ _)
  obtain ⟨hreg,hthree,hfour,_hsecondabs⟩ := hdata F T N hT hN hFd
  have hDpos : 0 < D := by linarith
  have hlam : 0 < lam := by dsimp [lam]; positivity [modelPhaseJetLower_pos hσ 3]
  have hL : 0 < L := by dsimp [L]; positivity [modelPhaseJetLower_pos hσ 2]
  have hU : 0 < U := by dsimp [U]; positivity [modelPhaseJetCoefficient_pos hσ 2]
  have hB : 0 ≤ B := by dsimp [B]; positivity [modelPhaseJetCoefficient_pos hσ 3]
  have hsegment : Icc (a-R) (b+R+2*D) ⊆ Ioo N (2*N) := by
    intro t ht
    constructor <;> linarith [ht.1,ht.2]
  let level := fun p => if hp : p∈S then Classical.choose (hsecond p hp) else 0
  have hlevel (p : ℤ × ℕ) (hps : p∈S) :
      |(iteratedDeriv 2 f ((p.1:ℝ)+(p.2:ℝ))-iteratedDeriv 2 f p.1)/2-(level p:ℝ)| ≤ δ₂ := by
    simp only [level,dif_pos hps]
    exact Classical.choose_spec (hsecond p hps)
  have hlevels (p : ℤ × ℕ) (hps : p∈S) :
      0 < level p ∧ (level p:ℝ) ≤ 2*U*D := by
    have hprange := hbox p hps
    have hq : 1 ≤ (p.2:ℝ) := by linarith [hprange.2.1]
    have hsub : Icc (p.1:ℝ) ((p.1:ℝ)+(p.2:ℝ)) ⊆ Ioo N (2*N) := by
      intro t ht
      apply hsegment
      constructor <;> linarith [ht.1,ht.2,hprange.1.1,hprange.1.2,hprange.2.2]
    have hh := cubic_second_level_positive f (level p) hq hL hδL hδhalf
      (fun t ht => (hreg t (hsub ht)).of_le (by norm_num))
      (fun t ht => hthree t (hsub ht)) (hlevel p hps)
    exact ⟨hh.1,hh.2.2.2.trans (by nlinarith [mul_le_mul_of_nonneg_left hprange.2.2 hU.le])⟩
  let J := S.image level
  have hJbound : (J.card:ℝ) ≤ 2*U*D := by
    by_cases hne : J.Nonempty
    · have hJ (K : ℤ) (hK : K∈J) : (1:ℝ) ≤ K ∧ (K:ℝ) ≤ 2*U*D := by
        obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hK
        have hh := hlevels p hp
        exact ⟨by exact_mod_cast (show (1:ℤ)≤level p by omega),hh.2⟩
      obtain ⟨K,hK⟩ := hne
      have hb := integer_card_le_interval_length_add_one J ((hJ K hK).1.trans (hJ K hK).2) hJ
      exact hb.trans_eq (by ring)
    · have he : J=∅ := Finset.not_nonempty_iff_eq_empty.mp hne
      simp only [he,Finset.card_empty,Nat.cast_zero]
      positivity
  let X := C*(W*D+(T/N^2)^(k₀+ε)*D^(l₀+ε)*W^(-(k₀+ε))+N^2/T)
  let Z := 4*δ₂/(lam*D)+1
  have hX : 0 ≤ X := by dsimp [X]; positivity
  have hZ : 0 ≤ Z := by dsimp [Z]; positivity
  have hcell (K : ℤ) (hK : K∈J) :
      ((S.filter (fun p => level p=K)).card:ℝ) ≤ Z*X := by
    obtain ⟨p,hps,hpK⟩ := Finset.mem_image.mp hK
    have hKpos : 0 < K := by rw [← hpK]; exact (hlevels p hps).1
    have hKbound : (K:ℝ) ≤ 2*U*D := by rw [← hpK]; exact (hlevels p hps).2
    have hκle : 2*(K:ℝ)*N^2/(σ*T) ≤ κ₀ := by
      calc
        _ ≤ 2*(2*U*D)*N^2/(σ*T) := by gcongr
        _ = 4*U*D*N^2/(σ*T) := by ring
        _ ≤ κ₀ := hshift
    have hsec : ∀ p∈S.filter (fun p => level p=K),
        |(iteratedDeriv 2 f ((p.1:ℝ)+(p.2:ℝ))-iteratedDeriv 2 f p.1)/2-(K:ℝ)| ≤ δ₂ := by
      intro p hp
      rw [← (Finset.mem_filter.mp hp).2]
      exact hlevel p (Finset.mem_filter.mp hp).1
    exact hcount F T N D a b R B lam δ₁ δ₂ W K (S.filter (fun p => level p=K))
      hF₀ hT hN hD hR hB hlam hδ₂ hleft hright hbuffer hwidth hKpos hκle hW hWhalf
      (fun t ht => hfour t (hsegment ht))
      (fun p hp => hbox p (Finset.mem_filter.mp hp).1) hsec
      (fun p hp => hfirst p (Finset.mem_filter.mp hp).1)
  have hmaps : Set.MapsTo level S J := by
    intro p hp
    exact Finset.mem_image.mpr ⟨p,hp,rfl⟩
  have hcard : (S.card:ℝ)=∑ K∈J, ((S.filter (fun p => level p=K)).card:ℝ) := by
    exact_mod_cast Finset.card_eq_sum_card_fiberwise hmaps
  calc
    _ = _ := hcard
    _ ≤ ∑ _K∈J, Z*X := Finset.sum_le_sum hcell
    _ = (J.card:ℝ)*(Z*X) := by simp only [Finset.sum_const,nsmul_eq_mul]
    _ ≤ (2*U*D)*(Z*X) := mul_le_mul_of_nonneg_right hJbound (mul_nonneg hZ hX)
    _ = _ := by dsimp [Z,X]; ring

theorem cubic_short_displacement_count
    (f : ℝ → ℝ) (S : Finset (ℤ × ℕ)) {a b D B lam L U δ : ℝ}
    (hD : 1 ≤ D) (hlam : 0 < lam) (hL : 0 < L) (hU : 0 < U) (hδ : 0 ≤ δ)
    (hδL : δ ≤ L/4) (hδhalf : δ ≤ 1/2)
    (hf : ∀ t∈Icc a (b+D), ContDiffAt ℝ 4 f t)
    (hthree : ∀ t∈Icc a (b+D), L ≤ iteratedDeriv 3 f t ∧ iteratedDeriv 3 f t ≤ U)
    (hfour : ∀ t∈Icc a (b+D), -B ≤ iteratedDeriv 4 f t ∧ iteratedDeriv 4 f t ≤ -lam)
    (hbox : ∀ p∈S, (p.1:ℝ)∈Icc a b ∧ (p.2:ℝ)∈Icc 1 D)
    (hsecond : ∀ p∈S, ∃ K : ℤ,
      |(iteratedDeriv 2 f ((p.1:ℝ)+(p.2:ℝ))-iteratedDeriv 2 f p.1)/2-(K:ℝ)| ≤ δ) :
    (S.card:ℝ) ≤ D*(4*U*δ/lam+U*D) := by
  classical
  let level := fun p => if hp : p∈S then Classical.choose (hsecond p hp) else 0
  have hlevel (p : ℤ × ℕ) (hps : p∈S) :
      |(iteratedDeriv 2 f ((p.1:ℝ)+(p.2:ℝ))-iteratedDeriv 2 f p.1)/2-(level p:ℝ)| ≤ δ := by
    simp only [level,dif_pos hps]
    exact Classical.choose_spec (hsecond p hps)
  have hlevels (p : ℤ × ℕ) (hps : p∈S) :
      0 < level p ∧ (level p:ℝ) ≤ U*(p.2:ℝ) := by
    have hb := hbox p hps
    have hsub : Icc (p.1:ℝ) ((p.1:ℝ)+(p.2:ℝ)) ⊆ Icc a (b+D) := by
      intro t ht
      constructor <;> linarith [hb.1.1,hb.1.2,hb.2.2,ht.1,ht.2]
    have hh := cubic_second_level_positive f (level p) hb.2.1 hL hδL hδhalf
      (fun t ht => (hf t (hsub ht)).of_le (by norm_num))
      (fun t ht => hthree t (hsub ht)) (hlevel p hps)
    exact ⟨hh.1,hh.2.2.2⟩
  let J := S.image Prod.snd
  have hqbox (q : ℕ) (hq : q∈J) : 1 ≤ (q:ℝ) ∧ (q:ℝ) ≤ D := by
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hq
    exact (hbox p hp).2
  have hJ : (J.card:ℝ) ≤ D := by
    let I := J.image (fun q : ℕ => (q:ℤ))
    have hcard : I.card=J.card := Finset.card_image_of_injective J Int.ofNat_injective
    have hh := integer_card_le_interval_length_add_one I hD (by
      intro z hz
      obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hz
      simpa only [Int.cast_natCast] using hqbox q hq)
    rw [hcard] at hh
    linarith
  have hfiber (q : ℕ) (hq : q∈J) :
      ((S.filter (fun p => p.2=q)).card:ℝ) ≤ 4*U*δ/lam+U*D := by
    let T := S.filter (fun p => p.2=q)
    let I := T.image level
    have hqpos : 0 < (q:ℝ) := zero_lt_one.trans_le (hqbox q hq).1
    have hI : (I.card:ℝ) ≤ U*(q:ℝ) := by
      by_cases hne : I.Nonempty
      · have hi (K : ℤ) (hK : K∈I) : (1:ℝ) ≤ K ∧ (K:ℝ) ≤ U*(q:ℝ) := by
          obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hK
          have hh := hlevels p (Finset.mem_filter.mp hp).1
          rw [(Finset.mem_filter.mp hp).2] at hh
          exact ⟨by exact_mod_cast (show (1:ℤ)≤level p by omega),hh.2⟩
        obtain ⟨K,hK⟩ := hne
        have hh := integer_card_le_interval_length_add_one I ((hi K hK).1.trans (hi K hK).2) hi
        exact hh.trans_eq (by ring)
      · have he : I=∅ := Finset.not_nonempty_iff_eq_empty.mp hne
        simp only [he,Finset.card_empty,Nat.cast_zero]
        positivity
    have hsub : Icc a (b+(q:ℝ)) ⊆ Icc a (b+D) := by
      intro t ht
      exact ⟨ht.1,ht.2.trans (by linarith [(hqbox q hq).2])⟩
    have hcell (K : ℤ) :
        ((T.filter (fun p => level p=K)).card:ℝ) ≤ 4*δ/(lam*(q:ℝ))+1 := by
      let Z := T.filter (fun p => level p=K)
      let Y := Z.image Prod.fst
      have hinj : Set.InjOn (Prod.fst : ℤ × ℕ → ℤ) Z := by
        intro p hp r hr he
        exact Prod.ext he ((Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).2.trans
          (Finset.mem_filter.mp (Finset.mem_filter.mp hr).1).2.symm)
      have hcard : Y.card=Z.card := Finset.card_image_of_injOn hinj
      have hY : ∀ n∈Y, (n:ℝ)∈Icc a b := by
        intro n hn
        obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hn
        exact (hbox p (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).1).1
      have hnear : ∀ n∈Y,
          |(iteratedDeriv 2 f ((n:ℝ)+(q:ℝ))-iteratedDeriv 2 f n)/2-(K:ℝ)| ≤ δ := by
        intro n hn
        obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hn
        have hh := hlevel p (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).1
        rwa [(Finset.mem_filter.mp hp).2,
          (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).2] at hh
      have hh := cubic_second_difference_fiber_card f Y hqpos hlam hδ
        (fun t ht => hf t (hsub ht)) (fun t ht => hfour t (hsub ht)) hY hnear
      rwa [hcard] at hh
    have hmaps : Set.MapsTo level T I := by
      intro p hp
      exact Finset.mem_image.mpr ⟨p,hp,rfl⟩
    have hcard : (T.card:ℝ)=∑ K∈I, ((T.filter (fun p => level p=K)).card:ℝ) := by
      exact_mod_cast Finset.card_eq_sum_card_fiberwise hmaps
    calc
      _ = _ := hcard
      _ ≤ ∑ _K∈I, (4*δ/(lam*(q:ℝ))+1) := Finset.sum_le_sum (fun K _ => hcell K)
      _ = (I.card:ℝ)*(4*δ/(lam*(q:ℝ))+1) := by simp only [Finset.sum_const,nsmul_eq_mul]
      _ ≤ (U*(q:ℝ))*(4*δ/(lam*(q:ℝ))+1) := mul_le_mul_of_nonneg_right hI (by positivity)
      _ = 4*U*δ/lam+U*(q:ℝ) := by field_simp
      _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_left (hqbox q hq).2 hU.le]
  have hmaps : Set.MapsTo (Prod.snd : ℤ × ℕ → ℕ) S J := by
    intro p hp
    exact Finset.mem_image.mpr ⟨p,hp,rfl⟩
  have hcard : (S.card:ℝ)=∑ q∈J, ((S.filter (fun p => p.2=q)).card:ℝ) := by
    exact_mod_cast Finset.card_eq_sum_card_fiberwise hmaps
  calc
    _ = _ := hcard
    _ ≤ ∑ _q∈J, (4*U*δ/lam+U*D) := Finset.sum_le_sum hfiber
    _ = (J.card:ℝ)*(4*U*δ/lam+U*D) := by simp only [Finset.sum_const,nsmul_eq_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_right hJ (by positivity)

theorem cubic_free_width_and_buffer
    {H Y lam B D : ℝ} (hH : 2 ≤ H) (hY : 2 ≤ Y)
    (hlam : 0 < lam) (hB : lam ≤ B) (hD : 2 ≤ D)
    (hthreshold : 4*B/(lam^2*H^4) ≤ D) :
    let R := 1/(2*lam*D*H^2)
    let W := max (1/(2*H)+B/(lam^2*D*H^4)) (1/Y)
    0 < R ∧ R ≤ H^2 ∧ 0 < W ∧ W ≤ 1/2 ∧
      1/(4*H^2)=lam*D*R/2 ∧
      1/(4*H)+2*B*D*R^2 ≤ W/2 ∧
      W*D ≤ D/(2*H)+B/(lam^2*H^4)+D/Y ∧
      ∀ p : ℝ, 0 ≤ p → W^(-p) ≤ Y^p := by
  intro R W
  have hHpos : 0 < H := by linarith
  have hYpos : 0 < Y := by linarith
  have hDpos : 0 < D := by linarith
  have hBpos : 0 < B := hlam.trans_le hB
  have hR : 0 < R := by dsimp [R]; positivity
  have hraw : 4*B ≤ D*(lam^2*H^4) :=
    (div_le_iff₀ (by positivity : 0 < lam^2*H^4)).mp hthreshold
  have hsize : 4 ≤ lam*D*H^4 := by
    apply (mul_le_mul_iff_right₀ hlam).mp
    nlinarith only [hraw,hB]
  have hRsmall : R ≤ H^2 := by
    apply (div_le_iff₀ (by positivity : 0 < 2*lam*D*H^2)).mpr
    nlinarith only [hsize]
  have hW : 0 < W := (one_div_pos.mpr hYpos).trans_le (le_max_right _ _)
  have hquarter : 1/(2*H) ≤ 1/4 := by
    apply (div_le_div_iff₀ (by positivity : 0 < 2*H) (by norm_num : (0:ℝ)<4)).mpr
    linarith
  have hother : B/(lam^2*D*H^4) ≤ 1/4 := by
    apply (div_le_div_iff₀ (by positivity : 0 < lam^2*D*H^4) (by norm_num : (0:ℝ)<4)).mpr
    nlinarith only [hraw]
  have hWhalf : W ≤ 1/2 := by
    apply max_le
    · linarith
    · exact one_div_le_one_div_of_le (by norm_num : (0:ℝ)<2) hY
  have hbuffer : 1/(4*H^2)=lam*D*R/2 := by dsimp [R]; field_simp; norm_num
  have hwidth : 1/(4*H)+2*B*D*R^2 ≤ W/2 := by
    have he : 1/(4*H)+2*B*D*R^2=(1/(2*H)+B/(lam^2*D*H^4))/2 := by
      dsimp [R]
      field_simp
      ring
    rw [he]
    exact div_le_div_of_nonneg_right (le_max_left _ _) (by norm_num)
  have hWD : W*D ≤ D/(2*H)+B/(lam^2*H^4)+D/Y := by
    have hsum : W ≤ (1/(2*H)+B/(lam^2*D*H^4))+1/Y := by
      apply max_le
      · linarith [one_div_pos.mpr hYpos]
      · have hpos : 0 ≤ 1/(2*H)+B/(lam^2*D*H^4) := by positivity
        linarith
    calc
      _ ≤ ((1/(2*H)+B/(lam^2*D*H^4))+1/Y)*D := mul_le_mul_of_nonneg_right hsum hDpos.le
      _ = _ := by field_simp
  refine ⟨hR,hRsmall,hW,hWhalf,hbuffer,hwidth,hWD,?_⟩
  intro p hp
  have hh := Real.rpow_le_rpow_of_nonpos (one_div_pos.mpr hYpos)
    (show 1/Y ≤ W from le_max_right _ _) (neg_nonpos.mpr hp)
  have he : (1/Y)^(-p)=Y^p := by
    rw [one_div,Real.inv_rpow hYpos.le,Real.rpow_neg hYpos.le,inv_inv]
  exact hh.trans_eq he

private theorem cubic_long_block_majorant
    {H Y lam B U D Qcut Freq Tail C p q : ℝ}
    (hH : 2 ≤ H) (hY : 2 ≤ Y) (hlam : 0 < lam) (hB : lam ≤ B)
    (hD : 2 ≤ D) (hthreshold : 4*B/(lam^2*H^4) ≤ D)
    (hU : 0 ≤ U) (hDQ : D ≤ Qcut) (hthin : lam*Qcut*H^2 ≤ 1)
    (hFreq : 0 ≤ Freq) (hTail : 0 ≤ Tail) (hC : 1 ≤ C) (hp : 0 ≤ p) (hq : 0 ≤ q) :
    let W := max (1/(2*H)+B/(lam^2*D*H^4)) (1/Y)
    (2*U*D)*(4*(1/(4*H^2))/(lam*D)+1)*
      (C*(W*D+Freq*D^q*W^(-p)+Tail)) ≤
      4*C*(U/(lam*H^2))*
        (1+B/(lam^2*H^4)+Qcut/H+Qcut/Y+Freq*Qcut^q*Y^p+Tail) := by
  intro W
  have hHpos : 0 < H := by linarith only [hH]
  have hYpos : 0 < Y := by linarith only [hY]
  have hDpos : 0 < D := by linarith only [hD]
  have hQpos : 0 < Qcut := hDpos.trans_le hDQ
  have hBpos : 0 < B := hlam.trans_le hB
  let V := U/(lam*H^2)
  let X := 1+B/(lam^2*H^4)+Qcut/H+Qcut/Y+Freq*Qcut^q*Y^p+Tail
  have hV : 0 ≤ V := by dsimp [V]; positivity
  have hX : 0 ≤ X := by dsimp [X]; positivity
  obtain ⟨_hR,_hRsmall,hW,_hWhalf,_hbuf,_hwidth,hWD,hWp⟩ :=
    cubic_free_width_and_buffer hH hY hlam hB hD hthreshold
  have hUQ : U*Qcut ≤ V := by
    apply (le_div_iff₀ (by positivity : 0 < lam*H^2)).mpr
    nlinarith only [mul_le_mul_of_nonneg_left hthin hU]
  have hfactorEq : (2*U*D)*(4*(1/(4*H^2))/(lam*D)+1)=2*V+2*U*D := by
    dsimp [V]
    field_simp
  have hfactor : (2*U*D)*(4*(1/(4*H^2))/(lam*D)+1) ≤ 4*V := by
    rw [hfactorEq]
    have hh := (mul_le_mul_of_nonneg_left hDQ hU).trans hUQ
    linarith only [hh]
  have hlen : D^q ≤ Qcut^q := Real.rpow_le_rpow hDpos.le hDQ hq
  have hosc : Freq*D^q*W^(-p) ≤ Freq*Qcut^q*Y^p := by
    gcongr
    exact hWp p hp
  have hvolume : W*D ≤ Qcut/H+B/(lam^2*H^4)+Qcut/Y := by
    calc
      _ ≤ D/(2*H)+B/(lam^2*H^4)+D/Y := hWD
      _ ≤ Qcut/(2*H)+B/(lam^2*H^4)+Qcut/Y := by gcongr
      _ ≤ _ := by
        have hh : Qcut/(2*H) ≤ Qcut/H :=
          div_le_div_of_nonneg_left hQpos.le hHpos (by linarith only [hHpos])
        linarith only [hh]
  have hinner : W*D+Freq*D^q*W^(-p)+Tail ≤ X := by
    dsimp [X]
    linarith only [hvolume,hosc]
  calc
    _ ≤ (4*V)*(C*X) := by gcongr
    _ = _ := by change (4*V)*(C*X)=4*C*V*X; ring

theorem original_full_joint_derivative_count
    {σ k₀ l₀ ε : ℝ} (hσ : 0 < σ)
    (hpair : ExponentPair k₀ l₀) (hε : 0 < ε) (hp : k₀+ε < 1) :
    ∃ δ κ₀ : ℝ, 0 < δ ∧ 0 < κ₀ ∧
      ∃ Q : ℕ, 3 ≤ Q ∧ ∃ C : ℝ, 1 ≤ C ∧
        ∀ (F : ℝ → ℝ) (T N H Y a b Qcut : ℝ) (M : ℕ) (S : Finset (ℤ × ℕ)),
          IsApproximateModelPhaseFunction F σ Q δ →
          0 < T → 0 < N → 2 ≤ H → 2 ≤ Y → 1 ≤ Qcut → Qcut ≤ (2:ℝ)^M →
          N < a-H^2 → b+H^2+2*Qcut < 2*N →
          let lam := modelPhaseJetLower σ 3*T/N^4
          let B := (modelPhaseJetCoefficient σ 3+1)*T/N^4
          let L := modelPhaseJetLower σ 2*T/N^3
          let U := (modelPhaseJetCoefficient σ 2+1)*T/N^3
          lam*Qcut*H^2 ≤ 1 → 1/(4*H^2) ≤ L/4 →
          4*U*Qcut*N^2/(σ*T) ≤ κ₀ →
          let f := fun z => T*F (z/N)
          (∀ p∈S, (p.1:ℝ)∈Icc a b ∧ (p.2:ℝ)∈Icc 1 Qcut) →
          (∀ p∈S, ∃ K : ℤ, |(iteratedDeriv 2 f ((p.1:ℝ)+(p.2:ℝ))-
            iteratedDeriv 2 f p.1)/2-(K:ℝ)| ≤ 1/(4*H^2)) →
          (∀ p∈S, ∃ e : ℤ, |iteratedDeriv 1 f ((p.1:ℝ)+(p.2:ℝ))-
            iteratedDeriv 1 f p.1-(e:ℝ)| ≤ 1/(4*H)) →
            (S.card:ℝ) ≤ C*((M:ℝ)+2)*(U/(lam*H^2))*
              (1+B/(lam^2*H^4)+Qcut/H+Qcut/Y+
                (T/N^2)^(k₀+ε)*Qcut^(l₀+ε)*Y^(k₀+ε)+N^2/T) := by
  classical
  obtain ⟨δ₀,κ₀,hδ₀,hκ₀,Q₀,hQ₀,C₀,hC₀,hcount⟩ :=
    original_joint_dyadic_block_count hσ hpair hε hp
  obtain ⟨δd,hδd,hdata⟩ := model_displacement_derivative_data hσ
  let δ := min δ₀ δd
  let Q := max Q₀ 3
  let C := 8+4*C₀
  have hC : 1 ≤ C := by dsimp [C]; linarith
  have hC8 : 8 ≤ C := by dsimp [C]; linarith
  have hC4 : 4*C₀ ≤ C := by dsimp [C]; linarith
  refine ⟨δ,κ₀,lt_min hδ₀ hδd,hκ₀,Q,le_max_right _ _,C,hC,?_⟩
  intro F T N H Y a b Qcut M S hF hT hN hH hY hQcut hQpow hleft hright
    lam B L U hthin hδL hshift f hbox hsecond hfirst
  have hF₀ := approximateModelPhase_mono hF (le_max_left _ _) (min_le_left _ _)
  have hFd := approximateModelPhase_mono hF (le_max_right _ _) (min_le_right _ _)
  obtain ⟨hreg,hthree,hfour,_hsecondabs⟩ := hdata F T N hT hN hFd
  have hHpos : 0 < H := by linarith
  have hYpos : 0 < Y := by linarith
  have hQpos : 0 < Qcut := zero_lt_one.trans_le hQcut
  have hlam : 0 < lam := by dsimp [lam]; positivity [modelPhaseJetLower_pos hσ 3]
  have hL : 0 < L := by dsimp [L]; positivity [modelPhaseJetLower_pos hσ 2]
  have hU : 0 < U := by dsimp [U]; positivity [modelPhaseJetCoefficient_pos hσ 2]
  have hBpos : 0 < B := by dsimp [B]; positivity [modelPhaseJetCoefficient_pos hσ 3]
  have hB : lam ≤ B := by
    have hh := modelPhase_signed_referenceJet_bounds hσ (by norm_num : (3/2:ℝ)∈Ioo 1 2) 3
    have hc : modelPhaseJetLower σ 3 ≤ modelPhaseJetCoefficient σ 3+1 := by
      linarith only [hh.1,hh.2,modelPhaseJetLower_pos hσ 3]
    dsimp [lam,B]
    gcongr
  have hδhalf : 1/(4*H^2) ≤ 1/2 := by
    apply (div_le_div_iff₀ (by positivity : 0 < 4*H^2) (by norm_num : (0:ℝ)<2)).mpr
    nlinarith only [hH]
  have hp₀ : 0 ≤ k₀+ε := by linarith [hpair.1.1]
  have hq₀ : 0 ≤ l₀+ε := by linarith [hpair.1.2.2.1]
  let V := U/(lam*H^2)
  let X := 1+B/(lam^2*H^4)+Qcut/H+Qcut/Y+
    (T/N^2)^(k₀+ε)*Qcut^(l₀+ε)*Y^(k₀+ε)+N^2/T
  let A := C*V*X
  let D₀ := 2+4*B/(lam^2*H^4)
  have hV : 0 < V := by dsimp [V]; positivity
  have hX : 0 < X := by dsimp [X]; positivity
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hD₀ : 2 ≤ D₀ := by
    have hh : 0 ≤ 4*B/(lam^2*H^4) := by positivity
    dsimp [D₀]
    linarith
  have hUQ : U*Qcut ≤ V := by
    apply (le_div_iff₀ (by positivity : 0 < lam*H^2)).mpr
    nlinarith only [mul_le_mul_of_nonneg_left hthin hU.le]
  have hsegment : Icc a (b+Qcut) ⊆ Ioo N (2*N) := by
    intro t ht
    constructor <;> linarith only [ht.1,ht.2,sq_nonneg H,hleft,hright,hQpos]
  let short := S.filter (fun p => (p.2:ℝ)<D₀)
  have hshort : (short.card:ℝ) ≤ A := by
    let d := min D₀ Qcut
    have hd : 1 ≤ d := le_min (by linarith) hQcut
    have hdQ : d ≤ Qcut := min_le_right _ _
    have hd₀ : d ≤ D₀ := min_le_left _ _
    have hsub : Icc a (b+d) ⊆ Ioo N (2*N) := by
      intro t ht
      exact hsegment ⟨ht.1,ht.2.trans (by linarith)⟩
    have hh := cubic_short_displacement_count f short hd hlam hL hU (by positivity)
      hδL hδhalf
      (fun t ht => (hreg t (hsub ht)).of_le (by norm_num))
      (fun t ht => hthree t (hsub ht)) (fun t ht => hfour t (hsub ht))
      (by
        intro p hp
        have hb := hbox p (Finset.mem_filter.mp hp).1
        exact ⟨hb.1,hb.2.1,le_min (Finset.mem_filter.mp hp).2.le hb.2.2⟩)
      (fun p hp => hsecond p (Finset.mem_filter.mp hp).1)
    have he : 4*U*(1/(4*H^2))/lam=V := by dsimp [V]; field_simp
    rw [he] at hh
    have hUd : U*d ≤ V := (mul_le_mul_of_nonneg_left hdQ hU.le).trans hUQ
    have hsmall : (short.card:ℝ) ≤ 2*D₀*V := by
      calc
        _ ≤ d*(V+U*d) := hh
        _ ≤ D₀*(V+V) := by gcongr
        _ = _ := by ring
    have hDX : 2*D₀ ≤ 8*X := by
      have hterms : 0 ≤ Qcut/H+Qcut/Y+
          (T/N^2)^(k₀+ε)*Qcut^(l₀+ε)*Y^(k₀+ε)+N^2/T := by positivity
      dsimp [D₀,X]
      ring_nf at hterms ⊢
      linarith only [hterms]
    calc
      _ ≤ 2*D₀*V := hsmall
      _ ≤ (8*X)*V := mul_le_mul_of_nonneg_right hDX hV.le
      _ ≤ (C*X)*V := by gcongr
      _ = A := by dsimp [A]; ring
  let scale := fun j : ℕ => D₀*(2:ℝ)^j
  let block := fun j : ℕ => S.filter (fun p => scale j ≤ (p.2:ℝ) ∧ (p.2:ℝ)<2*scale j)
  have hblock (j : ℕ) : ((block j).card:ℝ) ≤ A := by
    by_cases hne : (block j).Nonempty
    · obtain ⟨p,hps⟩ := hne
      let D := scale j
      have hDlow : D₀ ≤ D := by
        have hh : (1:ℝ) ≤ 2^j := one_le_pow₀ (by norm_num)
        dsimp [D,scale]
        simpa only [mul_one] using mul_le_mul_of_nonneg_left hh
          (show 0 ≤ D₀ by linarith only [hD₀])
      have hD : 2 ≤ D := hD₀.trans hDlow
      have hDpos : 0 < D := by linarith
      have hDQ : D ≤ Qcut := (Finset.mem_filter.mp hps).2.1.trans (hbox p (Finset.mem_filter.mp hps).1).2.2
      have hthreshold : 4*B/(lam^2*H^4) ≤ D := by
        dsimp [D₀] at hDlow
        linarith
      let R := 1/(2*lam*D*H^2)
      let W := max (1/(2*H)+B/(lam^2*D*H^4)) (1/Y)
      obtain ⟨hR,hRsmall,hW,hWhalf,hbuf,hwidth,_hWD,_hWp⟩ :=
        cubic_free_width_and_buffer hH hY hlam hB hD hthreshold
      have hshiftD : 4*U*D*N^2/(σ*T) ≤ κ₀ := by
        calc
          _ ≤ 4*U*Qcut*N^2/(σ*T) := by gcongr
          _ ≤ κ₀ := hshift
      have hh := hcount F T N D a b R (1/(4*H)) (1/(4*H^2)) W (block j)
        hF₀ hT hN hD hR (by positivity)
        (by linarith only [hleft,hRsmall])
        (by linarith only [hright,hRsmall,hDQ])
        hbuf.le hwidth hδL hδhalf hshiftD hW hWhalf
        (by
          intro p hp
          have hb := hbox p (Finset.mem_filter.mp hp).1
          exact ⟨hb.1,(Finset.mem_filter.mp hp).2.1,(Finset.mem_filter.mp hp).2.2.le⟩)
        (fun p hp => hsecond p (Finset.mem_filter.mp hp).1)
        (fun p hp => hfirst p (Finset.mem_filter.mp hp).1)
      have hmajor := cubic_long_block_majorant hH hY hlam hB hD hthreshold
        hU.le hDQ hthin (by positivity : 0 ≤ (T/N^2)^(k₀+ε))
        (by positivity : 0 ≤ N^2/T) hC₀ hp₀ hq₀
      have hbound : ((block j).card:ℝ) ≤ 4*C₀*V*X := hh.trans hmajor
      calc
        _ ≤ 4*C₀*V*X := hbound
        _ ≤ C*V*X := by gcongr
    · have he : block j=∅ := Finset.not_nonempty_iff_eq_empty.mp hne
      simp only [he,Finset.card_empty,Nat.cast_zero]
      exact hA
  have hcover : S ⊆ short ∪ (Finset.range (M+1)).biUnion block := by
    intro p hp
    by_cases hs : (p.2:ℝ)<D₀
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hp,hs⟩)
    have hterminal : (p.2:ℝ)<D₀*(2:ℝ)^(M+1) := by
      have hh := (hbox p hp).2.2.trans hQpow
      have hpowpos : (0:ℝ)<2^M := by positivity
      rw [pow_succ]
      nlinarith only [hh,hpowpos,hD₀]
    obtain ⟨j,hj,hlo,hhi⟩ := exists_bourgain_dyadic_amplitude (le_of_not_gt hs) hterminal
    exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr
      ⟨j,hj,Finset.mem_filter.mpr ⟨hp,hlo,hhi⟩⟩)
  have hcard : (S.card:ℝ) ≤ (short.card:ℝ)+∑ j∈Finset.range (M+1), ((block j).card:ℝ) := by
    have hh := (Finset.card_le_card hcover).trans
      ((Finset.card_union_le _ _).trans (Nat.add_le_add_left Finset.card_biUnion_le _))
    exact_mod_cast hh
  calc
    _ ≤ (short.card:ℝ)+∑ j∈Finset.range (M+1), ((block j).card:ℝ) := hcard
    _ ≤ A+∑ _j∈Finset.range (M+1), A := add_le_add hshort (Finset.sum_le_sum (fun j _ => hblock j))
    _ = _ := by
      simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul,Nat.cast_add,Nat.cast_one]
      dsimp only [A]
      ring

theorem cubicDerivativePairs_card_le_positive
    (f : ℝ → ℝ) (M H : ℕ) :
    (SquareProductCount.CubicSource.cubicDerivativePairs f M H).card ≤ M+
      2*((SquareProductCount.CubicSource.cubicDerivativePairs f M H).filter
        (fun p => p.1<p.2)).card := by
  classical
  let S := SquareProductCount.CubicSource.cubicDerivativePairs f M H
  let diag := S.filter (fun p => p.1=p.2)
  let up := S.filter (fun p => p.1<p.2)
  let down := S.filter (fun p => p.2<p.1)
  have hswap (p : ℕ × ℕ) (hp : p∈S) : p.swap∈S := by
    unfold S SquareProductCount.CubicSource.cubicDerivativePairs
      SquareProductCount.CubicSource.cubicSamplePairs at hp ⊢
    obtain ⟨hbox,hnear⟩ := Finset.mem_filter.mp hp
    refine Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
      ⟨(Finset.mem_product.mp hbox).2,(Finset.mem_product.mp hbox).1⟩,?_⟩
    intro d
    simpa only [Prod.swap,abs_sub_comm] using hnear d
  have hd : diag.card ≤ M := by
    have hinj : Set.InjOn (Prod.fst : ℕ × ℕ → ℕ) diag := by
      intro p hp q hq he
      exact Prod.ext he ((Finset.mem_filter.mp hp).2.symm.trans
        (he.trans (Finset.mem_filter.mp hq).2))
    have hsub : diag.image Prod.fst ⊆ Finset.range M := by
      intro n hn
      obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hn
      have hm := (cubicDerivativePairs_integer_resonances f
        (Finset.mem_filter.mp hp).1).1
      exact Finset.mem_range.mpr hm
    have hh := Finset.card_le_card hsub
    rwa [Finset.card_image_of_injOn hinj,Finset.card_range] at hh
  have hdown : down.card ≤ up.card := by
    have hsub : down.image Prod.swap ⊆ up := by
      intro p hp
      obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hp
      exact Finset.mem_filter.mpr ⟨hswap q (Finset.mem_filter.mp hq).1,(Finset.mem_filter.mp hq).2⟩
    have hh := Finset.card_le_card hsub
    rwa [Finset.card_image_of_injective down Prod.swap_injective] at hh
  have hcover : S ⊆ (diag∪up)∪down := by
    intro p hp
    rcases lt_trichotomy p.1 p.2 with hlt|heq|hgt
    · exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hp,hlt⟩))
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hp,heq⟩))
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hp,hgt⟩)
  have hh := (Finset.card_le_card hcover).trans ((Finset.card_union_le _ _).trans
    (Nat.add_le_add_right (Finset.card_union_le _ _) _))
  change S.card ≤ M+2*up.card
  omega

theorem cubic_shifted_positive_pair_resonances
    (f : ℝ → ℝ) (A : ℤ) {M H : ℕ} {p : ℕ × ℕ}
    (hp : p∈SquareProductCount.CubicSource.cubicDerivativePairs
      (fun x => f ((A:ℝ)+x)) M H) (hlt : p.1<p.2) :
    let n : ℤ := A+(p.1:ℤ)+1
    let q : ℕ := p.2-p.1
    (A:ℝ)+1 ≤ n ∧ (n:ℝ) ≤ (A:ℝ)+M ∧ 1 ≤ q ∧
      ∃ e K : ℤ,
        |iteratedDeriv 1 f ((n:ℝ)+(q:ℝ))-iteratedDeriv 1 f n-(e:ℝ)| ≤ 1/(4*(H:ℝ)) ∧
        |(iteratedDeriv 2 f ((n:ℝ)+(q:ℝ))-iteratedDeriv 2 f n)/2-(K:ℝ)| ≤ 1/(4*(H:ℝ)^2) := by
  intro n q
  obtain ⟨hm₀,_hm₁,e,K,hfirst,hsecond,_hthird⟩ :=
    cubicDerivativePairs_integer_resonances
      (fun x => f ((A:ℝ)+x)) hp
  have hder (j : ℕ) (x : ℝ) :
      iteratedDeriv j (fun y => f ((A:ℝ)+y)) x=iteratedDeriv j f ((A:ℝ)+x) :=
    congrFun (iteratedDeriv_comp_const_add j f (A:ℝ)) x
  have hn : (n:ℝ)=(A:ℝ)+(p.1:ℝ)+1 := by dsimp [n]; push_cast; ring
  have hq : (q:ℝ)=(p.2:ℝ)-(p.1:ℝ) := Nat.cast_sub hlt.le
  have he₀ : (A:ℝ)+((p.1:ℝ)+1)=(n:ℝ) := by rw [hn]; ring
  have he₁ : (A:ℝ)+((p.2:ℝ)+1)=(n:ℝ)+(q:ℝ) := by rw [hn,hq]; ring
  rw [hder,hder,he₀,he₁] at hfirst hsecond
  refine ⟨?_,?_,by dsimp [q]; omega,e,K,hfirst,hsecond⟩
  · rw [hn]
    have hh : (0:ℝ) ≤ p.1 := Nat.cast_nonneg _
    linarith only [hh]
  · rw [hn]
    have hh : (p.1:ℝ)+1 ≤ M := by exact_mod_cast (show p.1+1 ≤ M by omega)
    linarith only [hh]

theorem original_cubicDerivativePairs_count
    {σ k₀ l₀ ε : ℝ} (hσ : 0 < σ)
    (hpair : ExponentPair k₀ l₀) (hε : 0 < ε) (hp : k₀+ε < 1) :
    ∃ δ κ₀ : ℝ, 0 < δ ∧ 0 < κ₀ ∧
      ∃ Q : ℕ, 3 ≤ Q ∧ ∃ C : ℝ, 1 ≤ C ∧
        ∀ (F : ℝ → ℝ) (T N Y : ℝ) (A : ℤ) (M H J : ℕ),
          IsApproximateModelPhaseFunction F σ Q δ →
          0 < T → 0 < N → 2 ≤ H → 2 ≤ Y →
          let lam := modelPhaseJetLower σ 3*T/N^4
          let B := (modelPhaseJetCoefficient σ 3+1)*T/N^4
          let L := modelPhaseJetLower σ 2*T/N^3
          let U := (modelPhaseJetCoefficient σ 2+1)*T/N^3
          let Qcut := 3/(2*lam*(H:ℝ)^3)
          1 ≤ Qcut → Qcut ≤ (2:ℝ)^J →
          N < (A:ℝ)+1-(H:ℝ)^2 → (A:ℝ)+M+(H:ℝ)^2+2*Qcut < 2*N →
          1/(4*(H:ℝ)^2) ≤ L/4 → 4*U*Qcut*N^2/(σ*T) ≤ κ₀ →
          let g := fun x => T*F (((A:ℝ)+x)/N)
          ((SquareProductCount.CubicSource.cubicDerivativePairs g M H).card:ℝ) ≤
            M+2*(C*((J:ℝ)+2)*(U/(lam*(H:ℝ)^2))*
              (1+B/(lam^2*(H:ℝ)^4)+Qcut/(H:ℝ)+Qcut/Y+
                (T/N^2)^(k₀+ε)*Qcut^(l₀+ε)*Y^(k₀+ε)+N^2/T)) := by
  classical
  obtain ⟨δ₀,κ₀,hδ₀,hκ₀,Q₀,hQ₀,C,hC,hcount⟩ :=
    original_full_joint_derivative_count hσ hpair hε hp
  obtain ⟨δd,hδd,hdata⟩ := model_displacement_derivative_data hσ
  let δ := min δ₀ δd
  let Q := max Q₀ 3
  refine ⟨δ,κ₀,lt_min hδ₀ hδd,hκ₀,Q,le_max_right _ _,C,hC,?_⟩
  intro F T N Y A M H J hF hT hN hH hY lam B L U Qcut hQcut hQpow hleft hright hδL hshift g
  have hF₀ := approximateModelPhase_mono hF (le_max_left _ _) (min_le_left _ _)
  have hFd := approximateModelPhase_mono hF (le_max_right _ _) (min_le_right _ _)
  obtain ⟨hreg,_hthree,hfour,_hsecondabs⟩ := hdata F T N hT hN hFd
  let f := fun x => T*F (x/N)
  let pairs := SquareProductCount.CubicSource.cubicDerivativePairs g M H
  let up := pairs.filter (fun p => p.1<p.2)
  let label := fun p : ℕ × ℕ => (A+(p.1:ℤ)+1,p.2-p.1)
  let S := up.image label
  have hHr : (2:ℝ) ≤ H := by exact_mod_cast hH
  have hHpos : (0:ℝ) < H := by linarith only [hHr]
  have hlam : 0 < lam := by dsimp [lam]; positivity [modelPhaseJetLower_pos hσ 3]
  have hQpos : 0 < Qcut := zero_lt_one.trans_le hQcut
  have hder (j : ℕ) (x : ℝ) : iteratedDeriv j g x=iteratedDeriv j f ((A:ℝ)+x) :=
    congrFun (iteratedDeriv_comp_const_add j f (A:ℝ)) x
  have hphysical (x : ℝ) (hx : x∈Icc 1 (M:ℝ)) : (A:ℝ)+x∈Ioo N (2*N) := by
    constructor <;> linarith only [hx.1,hx.2,hleft,hright,sq_nonneg (H:ℝ),hQpos]
  have hdisp (p : ℕ × ℕ) (hps : p∈up) : ((p.2-p.1:ℕ):ℝ) ≤ Qcut := by
    have hpairs := (Finset.mem_filter.mp hps).1
    have hlt := (Finset.mem_filter.mp hps).2
    obtain ⟨hm₀,hm₁,_he,_hK,_hfirst,_hsecond,_hthird⟩ :=
      cubicDerivativePairs_integer_resonances g hpairs
    have hsub (x : ℝ) (hx : x∈Icc ((p.1:ℝ)+1) ((p.2:ℝ)+1)) : x∈Icc 1 (M:ℝ) := by
      have hm : (p.2:ℝ)+1 ≤ M := by exact_mod_cast (show p.2+1≤M by omega)
      have hp0 : (0:ℝ) ≤ p.1 := Nat.cast_nonneg _
      constructor <;> linarith only [hx.1,hx.2,hm,hp0]
    have hgc : ∀ x∈Icc ((p.1:ℝ)+1) ((p.2:ℝ)+1), ContDiffAt ℝ 4 g x := by
      intro x hx
      exact ((hreg ((A:ℝ)+x) (hphysical x (hsub x hx))).comp x
        (show ContDiffAt ℝ 5 (fun y : ℝ => (A:ℝ)+y) x by fun_prop)).of_le (by norm_num)
    have hgf : ∀ x∈Icc ((p.1:ℝ)+1) ((p.2:ℝ)+1), iteratedDeriv 4 g x ≤ -lam := by
      intro x hx
      rw [hder]
      exact (hfour ((A:ℝ)+x) (hphysical x (hsub x hx))).2
    rw [Nat.cast_sub hlt.le]
    exact cubicDerivativePairs_displacement g (by omega) hlam hpairs hlt hgc hgf
  have hinj : Set.InjOn label up := by
    intro p hp q hq he
    have hfst := congrArg Prod.fst he
    have hsnd := congrArg Prod.snd he
    dsimp only [label] at hfst hsnd
    have hp := (Finset.mem_filter.mp hp).2
    have hq := (Finset.mem_filter.mp hq).2
    have he₁ : p.1=q.1 := by omega
    exact Prod.ext he₁ (by omega)
  have hcard : S.card=up.card := Finset.card_image_of_injOn hinj
  have hboxS : ∀ p∈S, (p.1:ℝ)∈Icc ((A:ℝ)+1) ((A:ℝ)+M) ∧
      (p.2:ℝ)∈Icc 1 Qcut := by
    intro p hp
    obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hp
    have hh := cubic_shifted_positive_pair_resonances f A
      (Finset.mem_filter.mp hq).1 (Finset.mem_filter.mp hq).2
    exact ⟨⟨hh.1,hh.2.1⟩,by exact_mod_cast hh.2.2.1,hdisp q hq⟩
  have hsecondS : ∀ p∈S, ∃ K : ℤ,
      |(iteratedDeriv 2 f ((p.1:ℝ)+(p.2:ℝ))-iteratedDeriv 2 f p.1)/2-(K:ℝ)| ≤ 1/(4*(H:ℝ)^2) := by
    intro p hp
    obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨e,K,_hfirst,hsecond⟩ := (cubic_shifted_positive_pair_resonances f A
      (Finset.mem_filter.mp hq).1 (Finset.mem_filter.mp hq).2).2.2.2
    exact ⟨K,hsecond⟩
  have hfirstS : ∀ p∈S, ∃ e : ℤ,
      |iteratedDeriv 1 f ((p.1:ℝ)+(p.2:ℝ))-iteratedDeriv 1 f p.1-(e:ℝ)| ≤ 1/(4*(H:ℝ)) := by
    intro p hp
    obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨e,K,hfirst,_hsecond⟩ := (cubic_shifted_positive_pair_resonances f A
      (Finset.mem_filter.mp hq).1 (Finset.mem_filter.mp hq).2).2.2.2
    exact ⟨e,hfirst⟩
  have hthin : lam*Qcut*(H:ℝ)^2 ≤ 1 := by
    have he : lam*Qcut*(H:ℝ)^2=3/(2*(H:ℝ)) := by dsimp [Qcut]; field_simp
    rw [he]
    apply (div_le_iff₀ (by positivity : 0 < 2*(H:ℝ))).mpr
    linarith only [hHr]
  have hh := hcount F T N (H:ℝ) Y ((A:ℝ)+1) ((A:ℝ)+M) Qcut J S
    hF₀ hT hN hHr hY hQcut hQpow hleft hright hthin hδL hshift hboxS hsecondS hfirstS
  rw [hcard] at hh
  have hsplit : (pairs.card:ℝ) ≤ (M:ℝ)+2*(up.card:ℝ) := by
    exact_mod_cast cubicDerivativePairs_card_le_positive g M H
  exact hsplit.trans (by gcongr)

/-- Original-model eighth-power estimate from the literal C4 reduction
and the proved joint derivative count. Every C4/third-derivative hypothesis
is derived from the same original model phase. -/
theorem exists_original_cubic_eighth_estimate
    {σ k₀ l₀ ε : ℝ} (hσ : 0 < σ)
    (hpair : ExponentPair k₀ l₀) (hε : 0 < ε) (hp : k₀+ε < 1) :
    ∃ δ κ₀ : ℝ, 0 < δ ∧ 0 < κ₀ ∧
      ∃ Q : ℕ, 3 ≤ Q ∧ ∃ C : ℝ, 0 < C ∧
        ∀ (F : ℝ → ℝ) (T N Y : ℝ) (A : ℤ) (M H J : ℕ),
          IsApproximateModelPhaseFunction F σ Q δ →
          0 < T → 0 < N → 2 ≤ H → 2 ≤ Y →
          let lam := modelPhaseJetLower σ 3*T/N^4
          let B := (modelPhaseJetCoefficient σ 3+1)*T/N^4
          let L := modelPhaseJetLower σ 2*T/N^3
          let U := (modelPhaseJetCoefficient σ 2+1)*T/N^3
          let Qcut := 3/(2*lam*(H:ℝ)^3)
          1 ≤ Qcut → Qcut ≤ (2:ℝ)^J →
          N < (A:ℝ)+1-(H:ℝ)^2 → (A:ℝ)+M+(H:ℝ)^2+2*Qcut < 2*N →
          1/(4*(H:ℝ)^2) ≤ L/4 → 4*U*Qcut*N^2/(σ*T) ≤ κ₀ →
          B*((H:ℝ)+1)^4 ≤ 1 →
          let E := ((J:ℝ)+2)*(U/(lam*(H:ℝ)^2))*
            (1+B/(lam^2*(H:ℝ)^4)+Qcut/(H:ℝ)+Qcut/Y+
              (T/N^2)^(k₀+ε)*Qcut^(l₀+ε)*Y^(k₀+ε)+N^2/T)
          ‖∑ m∈Finset.range M,
            fordAdditiveCharacter (T*F (((A:ℝ)+(m:ℝ)+1)/N))‖^8 ≤
              C*((M:ℝ)^6*((M:ℝ)+E)*(1+U*(H:ℝ)^2)*(H:ℝ)^ε+(H:ℝ)^8) := by
  obtain ⟨δ₀,κ₀,hδ₀,hκ₀,Q₀,hQ₀,C₀,hC₀,hcount⟩ :=
    original_cubicDerivativePairs_count hσ hpair hε hp
  obtain ⟨δd,hδd,hdata⟩ := model_displacement_derivative_data hσ
  obtain ⟨C₁,hC₁,hsource⟩ := SquareProductCount.CubicSource.exists_C4_source_eighth_reduction hε
  let δ := min δ₀ δd
  let Q := max Q₀ 3
  let C := C₁*(1+2*C₀)
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨δ,κ₀,lt_min hδ₀ hδd,hκ₀,Q,le_max_right _ _,C,hC,?_⟩
  intro F T N Y A M H J hF hT hN hH hY lam B L U Qcut hQcut hQpow hleft hright hδL hshift hTaylor E
  have hF₀ := approximateModelPhase_mono hF (le_max_left _ _) (min_le_left _ _)
  have hFd := approximateModelPhase_mono hF (le_max_right _ _) (min_le_right _ _)
  obtain ⟨hreg,hthree,hfour,_hsecondabs⟩ := hdata F T N hT hN hFd
  let f := fun x => T*F (x/N)
  let g := fun x => f ((A:ℝ)+x)
  have hHr : (2:ℝ) ≤ H := by exact_mod_cast hH
  have hHpos : (0:ℝ) < H := by linarith only [hHr]
  have hlam : 0 < lam := by dsimp [lam]; positivity [modelPhaseJetLower_pos hσ 3]
  have hL : 0 < L := by dsimp [L]; positivity [modelPhaseJetLower_pos hσ 2]
  have hU : 0 < U := by dsimp [U]; positivity [modelPhaseJetCoefficient_pos hσ 2]
  have hB : 0 < B := by dsimp [B]; positivity [modelPhaseJetCoefficient_pos hσ 3]
  have hQpos : 0 < Qcut := zero_lt_one.trans_le hQcut
  have hder (j : ℕ) (x : ℝ) : iteratedDeriv j g x=iteratedDeriv j f ((A:ℝ)+x) :=
    congrFun (iteratedDeriv_comp_const_add j f (A:ℝ)) x
  have hHbuf : (H:ℝ)+1 ≤ (H:ℝ)^2 := by nlinarith only [hHr]
  have hpoint (m : ℕ) (hm : m∈Finset.range M) (y : ℝ)
      (hy : y∈Icc ((m:ℝ)-H) ((m:ℝ)+H+2)) : (A:ℝ)+y∈Ioo N (2*N) := by
    have hm0 : (0:ℝ) ≤ m := Nat.cast_nonneg _
    have hmM : (m:ℝ)+1 ≤ M := by
      exact_mod_cast (show m+1≤M by have := Finset.mem_range.mp hm; omega)
    constructor <;> linarith only [hy.1,hy.2,hm0,hmM,hHbuf,hleft,hright,hQpos]
  have hg (m : ℕ) (hm : m∈Finset.range M) (y : ℝ)
      (hy : y∈Icc ((m:ℝ)-H) ((m:ℝ)+H+2)) : ContDiffAt ℝ 4 g y := by
    exact ((hreg ((A:ℝ)+y) (hpoint m hm y hy)).comp y
      (show ContDiffAt ℝ 5 (fun z : ℝ => (A:ℝ)+z) y by fun_prop)).of_le (by norm_num)
  have hfour' (m : ℕ) (hm : m∈Finset.range M) (y : ℝ)
      (hy : y∈Icc ((m:ℝ)-H) ((m:ℝ)+H+2)) : |iteratedDeriv 4 g y| ≤ B := by
    rw [hder]
    have hh := hfour ((A:ℝ)+y) (hpoint m hm y hy)
    apply abs_le.mpr
    exact ⟨hh.1,by linarith only [hh.2,hlam,hB]⟩
  have hthree' (m : ℕ) (hm : m∈Finset.range M) :
      iteratedDeriv 3 g ((m:ℝ)+1)/6∈Icc (0:ℝ) (0+U/6) := by
    rw [hder]
    have hcenter : (m:ℝ)+1∈Icc ((m:ℝ)-H) ((m:ℝ)+H+2) := by
      constructor <;> linarith only [hHpos]
    have hh := hthree ((A:ℝ)+((m:ℝ)+1)) (hpoint m hm ((m:ℝ)+1) hcenter)
    constructor <;> linarith only [hh.1,hh.2,hL]
  have hnear := hcount F T N Y A M H J hF₀ hT hN hH hY hQcut hQpow hleft hright hδL hshift
  have hsum := hsource g M H (by omega) B 0 (U/6) hB.le (by positivity)
    hTaylor hg hfour' hthree'
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have hnear' : ((SquareProductCount.CubicSource.cubicDerivativePairs g M H).card:ℝ) ≤
      (1+2*C₀)*((M:ℝ)+E) := by
    have hh : ((SquareProductCount.CubicSource.cubicDerivativePairs g M H).card:ℝ) ≤
        (M:ℝ)+2*C₀*E := by
      convert hnear using 1
      dsimp [E]
      ring
    have hm : (0:ℝ) ≤ M := Nat.cast_nonneg _
    have hx : 0 ≤ 2*C₀*(M:ℝ) := by positivity
    nlinarith only [hh,hE,hx]
  have hUwidth : 1+(U/6)*(H:ℝ)^2 ≤ 1+U*(H:ℝ)^2 := by
    nlinarith only [mul_nonneg hU.le (sq_nonneg (H:ℝ))]
  have hb : ‖∑ m∈Finset.range M, fordAdditiveCharacter (g ((m:ℝ)+1))‖^8 ≤
      C*((M:ℝ)^6*((M:ℝ)+E)*(1+U*(H:ℝ)^2)*(H:ℝ)^ε+(H:ℝ)^8) := by
    calc
      _ ≤ C₁*((M:ℝ)^6*(SquareProductCount.CubicSource.cubicDerivativePairs g M H).card*
          (1+(U/6)*(H:ℝ)^2)*(H:ℝ)^ε+(H:ℝ)^8) := hsum
      _ ≤ C₁*((M:ℝ)^6*((1+2*C₀)*((M:ℝ)+E))*(1+U*(H:ℝ)^2)*(H:ℝ)^ε+(H:ℝ)^8) := by gcongr
      _ ≤ C₁*((1+2*C₀)*((M:ℝ)^6*((M:ℝ)+E)*(1+U*(H:ℝ)^2)*(H:ℝ)^ε+(H:ℝ)^8)) := by
        apply mul_le_mul_of_nonneg_left _ hC₁.le
        nlinarith only [mul_nonneg (show 0 ≤ 2*C₀ by positivity) (pow_nonneg hHpos.le 8)]
      _ = _ := by dsimp [C]; ring
  simpa only [g,f,add_assoc] using hb



/-- Trimming both ends of a literal source interval loses only its removed
unit-modulus terms, including the original closed left endpoint. -/
theorem cubic_source_trim
    (z : ℕ → ℂ) (hz : ∀ n, ‖z n‖ ≤ 1) (a b K : ℕ)
    (hab : a+2*K ≤ b) :
    ‖∑ n∈Finset.Icc a b, z n‖ ≤
      ‖∑ m∈Finset.range (b-a-2*K), z (a+K+m+1)‖+2*(K:ℝ)+1 := by
  let M := b-a-2*K
  have he : b-a+1=((K+1)+M)+K := by dsimp [M]; omega
  rw [RiemannZeta.GuthMaynard.sum_Icc_eq_shifted_range z a b (by omega),he,
    Finset.sum_range_add,Finset.sum_range_add]
  have hleft : ‖∑ i∈Finset.range (K+1), z (a+i)‖ ≤ (K:ℝ)+1 := by
    calc
      _ ≤ ∑ i∈Finset.range (K+1), ‖z (a+i)‖ := norm_sum_le _ _
      _ ≤ ∑ _i∈Finset.range (K+1), (1:ℝ) := Finset.sum_le_sum (fun i _ => hz (a+i))
      _ = _ := by simp
  have hright : ‖∑ i∈Finset.range K, z (a+((K+1)+M+i))‖ ≤ (K:ℝ) := by
    calc
      _ ≤ ∑ i∈Finset.range K, ‖z (a+((K+1)+M+i))‖ := norm_sum_le _ _
      _ ≤ ∑ _i∈Finset.range K, (1:ℝ) := Finset.sum_le_sum (fun i _ => hz _)
      _ = _ := by simp
  have hmid : (∑ i∈Finset.range M, z (a+(K+1+i))) =
      ∑ i∈Finset.range M, z (a+K+i+1) := by
    apply Finset.sum_congr rfl
    intro i _
    congr 1
    omega
  rw [hmid]
  have htriangle := norm_add_le
    ((∑ i∈Finset.range (K+1), z (a+i))+
      ∑ i∈Finset.range M, z (a+K+i+1))
    (∑ i∈Finset.range K, z (a+((K+1)+M+i)))
  have htriangle₂ := norm_add_le (∑ i∈Finset.range (K+1), z (a+i))
    (∑ i∈Finset.range M, z (a+K+i+1))
  dsimp [M] at htriangle
  dsimp [M] at htriangle₂
  linarith only [htriangle,htriangle₂,hleft,hright]


/-- The physical eighth-power bound for the complete closed source sum.
The discarded endpoints are chosen here, not supplied as an assumption. -/
theorem exists_complete_cubic_eighth_estimate
    {σ k₀ l₀ ε : ℝ} (hσ : 0 < σ)
    (hpair : ExponentPair k₀ l₀) (hε : 0 < ε) (hp : k₀+ε < 1) :
    ∃ δ κ₀ : ℝ, 0 < δ ∧ 0 < κ₀ ∧
      ∃ Q : ℕ, 3 ≤ Q ∧ ∃ C : ℝ, 0 < C ∧
        ∀ (F : ℝ → ℝ) (T N Y : ℝ) (a b H J : ℕ),
          IsApproximateModelPhaseFunction F σ Q δ →
          0 < T → 0 < N → 2 ≤ H → 2 ≤ Y →
          N ≤ a → (b:ℝ) ≤ 2*N →
          let lam := modelPhaseJetLower σ 3*T/N^4
          let B := (modelPhaseJetCoefficient σ 3+1)*T/N^4
          let L := modelPhaseJetLower σ 2*T/N^3
          let U := (modelPhaseJetCoefficient σ 2+1)*T/N^3
          let Qcut := 3/(2*lam*(H:ℝ)^3)
          1 ≤ Qcut → Qcut ≤ (2:ℝ)^J →
          1/(4*(H:ℝ)^2) ≤ L/4 → 4*U*Qcut*N^2/(σ*T) ≤ κ₀ →
          B*((H:ℝ)+1)^4 ≤ 1 →
          let E := ((J:ℝ)+2)*(U/(lam*(H:ℝ)^2))*
            (1+B/(lam^2*(H:ℝ)^4)+Qcut/(H:ℝ)+Qcut/Y+
              (T/N^2)^(k₀+ε)*Qcut^(l₀+ε)*Y^(k₀+ε)+N^2/T)
          ‖exponentialSumAt F T N a b‖^8 ≤
            C*(N^6*(N+E)*(1+U*(H:ℝ)^2)*(H:ℝ)^ε+
              (H:ℝ)^8+((H:ℝ)^2+Qcut+1)^8) := by
  classical
  obtain ⟨δ,κ₀,hδ,hκ₀,Q,hQ,C₀,hC₀,hsource⟩ :=
    exists_original_cubic_eighth_estimate hσ hpair hε hp
  let C := 128*(C₀+5^8+1)
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨δ,κ₀,hδ,hκ₀,Q,hQ,C,hC,?_⟩
  intro F T N Y a b H J hF hT hN hH hY ha hb lam B L U Qcut hQcut hQpow hδL hshift hTaylor E
  let R := (H:ℝ)^2+Qcut+1
  let K : ℕ := ⌈(H:ℝ)^2+2*Qcut+1⌉₊
  have hKlo : (H:ℝ)^2+2*Qcut+1 ≤ K := Nat.le_ceil _
  have hQpos : 0 < Qcut := zero_lt_one.trans_le hQcut
  have hKhi : (K:ℝ) < (H:ℝ)^2+2*Qcut+2 := by
    have hh := Nat.ceil_lt_add_one (show 0 ≤ (H:ℝ)^2+2*Qcut+1 by positivity)
    convert hh using 1
    ring
  have hR : 0 < R := by dsimp [R]; positivity
  have hboundary : 2*(K:ℝ)+1 ≤ 5*R := by
    dsimp [R]
    nlinarith only [hKhi,sq_nonneg (H:ℝ),hQpos]
  have hE : 0 ≤ E := by dsimp [E,U,lam,B]; positivity [modelPhaseJetLower_pos hσ 3,
    modelPhaseJetCoefficient_pos hσ 2,modelPhaseJetCoefficient_pos hσ 3]
  have hU : 0 < U := by dsimp [U]; positivity [modelPhaseJetCoefficient_pos hσ 2]
  let Z := N^6*(N+E)*(1+U*(H:ℝ)^2)*(H:ℝ)^ε+(H:ℝ)^8
  have hZ : 0 ≤ Z := by dsimp [Z]; positivity
  have hmajor : 128*(C₀*Z+5^8*R^8) ≤ C*(Z+R^8) := by
    dsimp [C]
    nlinarith only [hZ,pow_nonneg hR.le 8,
      mul_nonneg hC₀.le (pow_nonneg hR.le 8)]
  by_cases hab : a+2*K ≤ b
  · let M := b-a-2*K
    let A : ℤ := (a:ℤ)+(K:ℤ)
    have hAr : (A:ℝ)=(a:ℝ)+(K:ℝ) := by dsimp [A]; push_cast; rfl
    have hM : (M:ℝ)=(b:ℝ)-(a:ℝ)-2*(K:ℝ) := by
      dsimp [M]
      push_cast [Nat.cast_sub (show 2*K≤b-a by omega),Nat.cast_sub (show a≤b by omega)]
      ring
    have hMN : (M:ℝ) ≤ N := by
      rw [hM]
      linarith only [ha,hb,(Nat.cast_nonneg K : (0:ℝ) ≤ K)]
    have hleft : N < (A:ℝ)+1-(H:ℝ)^2 := by
      rw [hAr]
      linarith only [ha,hKlo,hQpos]
    have hright : (A:ℝ)+M+(H:ℝ)^2+2*Qcut < 2*N := by
      rw [hAr,hM]
      linarith only [hb,hKlo]
    have hc := hsource F T N Y A M H J hF hT hN hH hY hQcut hQpow
      hleft hright hδL hshift hTaylor
    let S := ∑ m∈Finset.range M, fordAdditiveCharacter (T*F (((A:ℝ)+(m:ℝ)+1)/N))
    have hc' : ‖S‖^8 ≤ C₀*Z := by
      refine hc.trans ?_
      dsimp [Z]
      gcongr
    have htrim := cubic_source_trim (fun n => oscillatory F T N n)
      (fun n => (norm_oscillatory F T N n).le) a b K hab
    have hmid : (∑ m∈Finset.range (b-a-2*K), oscillatory F T N ((a+K+m+1:ℕ):ℝ))=S := by
      apply Finset.sum_congr rfl
      intro m _
      simp only [sargos_ford_character_eq_fourier,oscillatory,Nat.cast_add,Nat.cast_one,hAr]
    have hnorm : ‖exponentialSumAt F T N a b‖ ≤ ‖S‖+5*R := by
      rw [hmid] at htrim
      change ‖exponentialSumAt F T N a b‖ ≤ _ at htrim
      linarith only [htrim,hboundary]
    have hpow := (pow_le_pow_left₀ (norm_nonneg _) hnorm 8).trans
      (add_pow_le (norm_nonneg S) (by positivity : 0 ≤ 5*R) 8)
    rw [mul_pow] at hpow
    change ‖exponentialSumAt F T N a b‖^8 ≤ C*(Z+R^8)
    exact (hpow.trans (by norm_num; gcongr)).trans hmajor
  · have hnorm : ‖exponentialSumAt F T N a b‖ ≤ 5*R := by
      have hh := norm_exponentialSumAt_le_card F T N a b
      have hcard : ((Finset.Icc a b).card:ℝ) ≤ 2*(K:ℝ)+1 := by
        have hn : (Finset.Icc a b).card ≤ 2*K+1 := by rw [Nat.card_Icc]; omega
        exact_mod_cast hn
      exact (hh.trans hcard).trans hboundary
    have hp := pow_le_pow_left₀ (norm_nonneg _) hnorm 8
    rw [mul_pow] at hp
    change ‖exponentialSumAt F T N a b‖^8 ≤ C*(Z+R^8)
    exact hp.trans ((by nlinarith only [mul_nonneg hC₀.le hZ,pow_nonneg hR.le 8] :
      5^8*R^8 ≤ 128*(C₀*Z+5^8*R^8)).trans hmajor)

/-- Fixed real powers preserve the already-proved ANTEDB scale semantics. -/
private theorem cubic_power_rpow
    {X T : VariableObject ℝ} {a : ℝ}
    (hX : IsPowerAsymptotic X T a) (hT : ∀ i, 1 ≤ T i) (p : ℝ) :
    IsPowerAsymptotic (fun i => (X i)^p) T (a*p) := by
  obtain ⟨e,he,hXe⟩ := hX
  refine ⟨fun i => e i*p,?_,?_⟩
  · convert he.const_smul p using 1
    · funext i
      exact mul_comm (e i) p
    · funext i
      exact mul_comm a p
  · filter_upwards [hXe] with i hi
    rw [hi,← Real.rpow_mul (zero_le_one.trans (hT i))]

private theorem cubic_power_natpow
    {X T : VariableObject ℝ} {a : ℝ}
    (hX : IsPowerAsymptotic X T a) (hT : ∀ i, 1 ≤ T i) (n : ℕ) :
    IsPowerAsymptotic (fun i => (X i)^n) T (a*(n:ℝ)) := by
  simpa only [Real.rpow_natCast] using cubic_power_rpow hX hT (n:ℝ)

private theorem cubic_power_const
    {T : VariableObject ℝ} (hT : ∀ i, 1 ≤ T i) (hTunbounded : T.IsUnbounded)
    {c : ℝ} (hc : 0 < c) :
    IsPowerAsymptotic (fun _ => c) T 0 := by
  have hTtop : Tendsto T atTop atTop :=
    (VariableObject.isUnbounded_iff_tendsto_atTop
      (fun i => zero_le_one.trans (hT i))).mp hTunbounded
  apply isPowerAsymptotic_of_logb_tendsto
    (hTtop.eventually (eventually_gt_atTop 1)) (Filter.Eventually.of_forall (fun _ => hc))
  simpa only [Real.logb] using
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => Real.log c) atTop (𝓝 (Real.log c))).div_atTop
      (Real.tendsto_log_atTop.comp hTtop)

private theorem cubic_power_eventually_le
    {X T : VariableObject ℝ} {a b : ℝ}
    (hX : IsPowerAsymptotic X T a) (hT : ∀ i, 1 ≤ T i) (hab : a < b) :
    ∀ᶠ i in atTop, X i ≤ (T i)^b := by
  have hh := hX.eventually_between (Filter.Eventually.of_forall hT)
    (sub_pos.mpr hab)
  filter_upwards [hh] with i hi
  convert hi.2 using 1
  congr 1
  ring

/-- The existing dyadic cutoff has subpower block-count cost; its actual
integer index remains linked to the physical cutoff. -/
private theorem cubic_dyadic_index_bound
    {T X : VariableObject ℝ} (hT : ∀ i, 1 ≤ T i) (hTunbounded : T.IsUnbounded)
    {q η : ℝ} (hq : 0 < q) (hη : 0 < η)
    (hX : ∀ᶠ i in atTop, 1 ≤ X i ∧ X i ≤ (T i)^q) :
    ∀ᶠ i in atTop, ∃ J : ℕ, X i ≤ (2:ℝ)^J ∧ (J:ℝ)+2 ≤ (T i)^η := by
  let γ := η/(2*q)
  have hγ : 0 < γ := by dsimp [γ]; positivity
  obtain ⟨D,hD,hcount⟩ := exists_dyadic_count_sq_le_rpow hγ
  have hTtop : Tendsto T atTop atTop :=
    (VariableObject.isUnbounded_iff_tendsto_atTop
      (fun i => zero_le_one.trans (hT i))).mp hTunbounded
  have hconstant := hTtop.eventually (eventually_const_mul_rpow_le_rpow
    (D := 2*D*(2:ℝ)^γ) (a := η/2) (b := η) (by linarith))
  filter_upwards [hX,hconstant] with i hi hconst
  obtain ⟨J,hJlo,hJhi⟩ := exists_dyadic_cutoff hi.1
  refine ⟨J,hJlo,?_⟩
  have hJ := hcount J
  have hj : (J:ℝ)+2 ≤ 2*((J:ℝ)+1)^2 := by
    nlinarith only [(Nat.cast_nonneg J : (0:ℝ) ≤ J),sq_nonneg (J:ℝ)]
  have hTp : 0 < T i := zero_lt_one.trans_le (hT i)
  calc
    _ ≤ 2*(D*((2:ℝ)^J)^γ) := hj.trans (by gcongr)
    _ ≤ 2*(D*(2*(T i)^q)^γ) := by gcongr; exact hJhi.trans (by gcongr; exact hi.2)
    _ = (2*D*2^γ)*(T i)^(η/2) := by
      rw [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 2) (by positivity),
        ← Real.rpow_mul hTp.le]
      have he : q*γ=η/2 := by dsimp [γ]; field_simp
      rw [he]
      ring
    _ ≤ _ := hconst

/-- Actual integer Taylor scales and physical Fourier scales satisfy every
remaining analytic side condition throughout the missing Bourgain interval. -/
theorem eventually_cubic_bourgain_parameters
    {T N : VariableObject ℝ} {α σ κ₀ η : ℝ}
    (hlo : 140/391 ≤ α) (hhi : α < 16/39) (hσ : 0 < σ)
    (hκ₀ : 0 < κ₀) (hη : 0 < η)
    (hT : ∀ i, 1 ≤ T i) (hTunbounded : T.IsUnbounded)
    (hNT : IsPowerAsymptotic N T α) :
    let h := (246*α-55)/398
    let r := (362*α-123)/398
    let H := floorRpow T h
    let Y := fun i => (T i)^r
    let lam := fun i => modelPhaseJetLower σ 3*T i/(N i)^4
    let B := fun i => (modelPhaseJetCoefficient σ 3+1)*T i/(N i)^4
    let L := fun i => modelPhaseJetLower σ 2*T i/(N i)^3
    let U := fun i => (modelPhaseJetCoefficient σ 2+1)*T i/(N i)^3
    let Qcut := fun i => 3/(2*lam i*(H i:ℝ)^3)
    ∀ᶠ i in atTop, 0 < N i ∧ 2 ≤ H i ∧ 2 ≤ Y i ∧
      ∃ J : ℕ, 1 ≤ Qcut i ∧ Qcut i ≤ (2:ℝ)^J ∧ (J:ℝ)+2 ≤ (T i)^η ∧
        1/(4*(H i:ℝ)^2) ≤ L i/4 ∧
        4*U i*Qcut i*(N i)^2/(σ*T i) ≤ κ₀ ∧
        B i*((H i:ℝ)+1)^4 ≤ 1 := by
  intro h r H Y lam B L U Qcut
  let q := 4*α-1-3*h
  have hh : 0 < h := by dsimp [h]; linarith only [hlo]
  have hr : 0 < r := by dsimp [r]; linarith only [hlo]
  have hq : 0 < q := by dsimp [q,h]; linarith only [hlo]
  have hTscale := isPowerAsymptotic_self T
  have hH : IsPowerAsymptotic (fun i => (H i:ℝ)) T h :=
    isPowerAsymptotic_floorRpow hh hT hTunbounded
  have hY : IsPowerAsymptotic Y T r := by
    simpa using cubic_power_rpow hTscale hT r
  have hc (c : ℝ) (hc : 0 < c) := cubic_power_const hT hTunbounded hc
  have hlam : IsPowerAsymptotic lam T (1-4*α) := by
    convert ((hc _ (modelPhaseJetLower_pos hσ 3)).mul hTscale hT).div
      (cubic_power_natpow hNT hT 4) hT using 1
    ring
  have hB : IsPowerAsymptotic B T (1-4*α) := by
    convert ((hc (modelPhaseJetCoefficient σ 3+1) (by positivity [modelPhaseJetCoefficient_pos hσ 3])).mul hTscale hT).div
      (cubic_power_natpow hNT hT 4) hT using 1
    ring
  have hL : IsPowerAsymptotic L T (1-3*α) := by
    convert ((hc _ (modelPhaseJetLower_pos hσ 2)).mul hTscale hT).div
      (cubic_power_natpow hNT hT 3) hT using 1
    ring
  have hU : IsPowerAsymptotic U T (1-3*α) := by
    convert ((hc (modelPhaseJetCoefficient σ 2+1) (by positivity [modelPhaseJetCoefficient_pos hσ 2])).mul hTscale hT).div
      (cubic_power_natpow hNT hT 3) hT using 1
    ring
  have hQ : IsPowerAsymptotic Qcut T q := by
    convert (hc 3 (by norm_num)).div
      (((hc 2 (by norm_num)).mul hlam hT).mul (cubic_power_natpow hH hT 3) hT) hT using 1
    dsimp [q]
    ring
  have hLH : IsPowerAsymptotic (fun i => L i*(H i:ℝ)^2) T (1-3*α+2*h) := by
    convert hL.mul (cubic_power_natpow hH hT 2) hT using 1
    ring
  have hshift : IsPowerAsymptotic (fun i => 4*U i*Qcut i*(N i)^2/(σ*T i)) T (q-α) := by
    convert ((((hc 4 (by norm_num)).mul hU hT).mul hQ hT).mul
      (cubic_power_natpow hNT hT 2) hT).div ((hc σ hσ).mul hTscale hT) hT using 1
    ring
  have htaylor : IsPowerAsymptotic (fun i => 16*B i*(H i:ℝ)^4) T (1-4*α+4*h) := by
    convert ((hc 16 (by norm_num)).mul hB hT).mul
      (cubic_power_natpow hH hT 4) hT using 1
    ring
  have hNlarge := (hNT.tendsto_atTop_of_pos
    (by linarith only [hlo] : 0 < α) hT hTunbounded).eventually (eventually_gt_atTop 0)
  have hHlarge := (hH.tendsto_atTop_of_pos hh hT hTunbounded).eventually
    (eventually_ge_atTop 2)
  have hYlarge := (hY.tendsto_atTop_of_pos hr hT hTunbounded).eventually
    (eventually_ge_atTop 2)
  have hQlarge := (hQ.tendsto_atTop_of_pos hq hT hTunbounded).eventually
    (eventually_ge_atTop 1)
  have hLHlarge := (hLH.tendsto_atTop_of_pos
    (by dsimp [h]; linarith only [hhi] : 0 < 1-3*α+2*h) hT hTunbounded).eventually
    (eventually_ge_atTop 1)
  have hshiftsmall := (hshift.tendsto_zero_of_neg
    (by dsimp [q,h]; linarith only [hhi] : q-α < 0) hT hTunbounded).eventually
    (eventually_lt_nhds hκ₀)
  have htaylorsmall := (htaylor.tendsto_zero_of_neg
    (by dsimp [h]; linarith only [hlo] : 1-4*α+4*h < 0) hT hTunbounded).eventually
    (eventually_lt_nhds (by norm_num : (0:ℝ) < 1))
  have hindex := cubic_dyadic_index_bound hT hTunbounded
    (by linarith only [hq] : 0 < q+1) hη
    (hQlarge.and (cubic_power_eventually_le hQ hT (by linarith : q<q+1)))
  filter_upwards [hNlarge,hHlarge,hYlarge,hLHlarge,hshiftsmall,htaylorsmall,hindex,hQlarge]
    with i hNi hHi hYi hLHi hsi hti hJi hQi
  obtain ⟨J,hJq,hJcount⟩ := hJi
  refine ⟨hNi,by exact_mod_cast hHi,hYi,J,hQi,hJq,hJcount,?_,hsi.le,?_⟩
  · have hHp : (0:ℝ) < H i := by linarith only [hHi]
    apply (div_le_iff₀ (by positivity : 0 < 4*(H i:ℝ)^2)).mpr
    nlinarith only [hLHi]
  · have hBp : 0 < B i := by
      dsimp [B]
      positivity [modelPhaseJetCoefficient_pos hσ 3,zero_lt_one.trans_le (hT i)]
    have hsum : (H i:ℝ)+1 ≤ 2*(H i:ℝ) := by linarith only [hHi]
    have hp := pow_le_pow_left₀ (by positivity : (0:ℝ) ≤ (H i:ℝ)+1) hsum 4
    have hm := mul_le_mul_of_nonneg_left hp hBp.le
    nlinarith only [hm,hti]


/-- The actual closed-source majorant has the D(Bourgain) exponent.
Both independent scales and the complete dyadic cost remain explicit. -/
theorem eventually_cubic_bourgain_cost
    {T N : VariableObject ℝ} {α σ η : ℝ}
    (hlo : 140/391 ≤ α) (hhi : α < 16/39) (hσ : 0 < σ) (hη : 0 < η)
    (hT : ∀ i, 1 ≤ T i) (hTunbounded : T.IsUnbounded)
    (hNT : IsPowerAsymptotic N T α) :
    let h := (246*α-55)/398
    let r := (362*α-123)/398
    let β := 18/199+(521/796)*α
    let H := floorRpow T h
    let Y := fun i => (T i)^r
    let lam := fun i => modelPhaseJetLower σ 3*T i/(N i)^4
    let B := fun i => (modelPhaseJetCoefficient σ 3+1)*T i/(N i)^4
    let U := fun i => (modelPhaseJetCoefficient σ 2+1)*T i/(N i)^3
    let Qcut := fun i => 3/(2*lam i*(H i:ℝ)^3)
    ∀ᶠ i in atTop, ∀ J : ℕ, (J:ℝ)+2 ≤ (T i)^η →
      let E := ((J:ℝ)+2)*(U i/(lam i*(H i:ℝ)^2))*
        (1+B i/((lam i)^2*(H i:ℝ)^4)+Qcut i/(H i:ℝ)+Qcut i/Y i+
          (T i/(N i)^2)^(13/84+η)*(Qcut i)^(55/84+η)*(Y i)^(13/84+η)+(N i)^2/T i)
      (N i)^6*(N i+E)*(1+U i*(H i:ℝ)^2)*(H i:ℝ)^η+
          (H i:ℝ)^8+((H i:ℝ)^2+Qcut i+1)^8 ≤
        (15+3^8)*(T i)^(8*β+5*η) := by
  intro h r β H Y lam B U Qcut
  let q := 4*α-1-3*h
  let V := fun i => U i/(lam i*(H i:ℝ)^2)
  let f₁ := fun i => V i/N i
  let f₂ := fun i => V i*(B i/((lam i)^2*(H i:ℝ)^4))/N i
  let f₃ := fun i => V i*(Qcut i/(H i:ℝ))/N i
  let f₄ := fun i => V i*(Qcut i/Y i)/N i
  let f₅ := fun i => V i*((T i/(N i)^2)^(13/84+η)*(Qcut i)^(55/84+η)*(Y i)^(13/84+η))/N i
  let f₆ := fun i => V i*((N i)^2/T i)/N i
  have hh : 0 < h := by dsimp [h]; linarith only [hlo]
  have hTscale := isPowerAsymptotic_self T
  have hH : IsPowerAsymptotic (fun i => (H i:ℝ)) T h :=
    isPowerAsymptotic_floorRpow hh hT hTunbounded
  have hY : IsPowerAsymptotic Y T r := by simpa using cubic_power_rpow hTscale hT r
  have hc (c : ℝ) (hc : 0 < c) := cubic_power_const hT hTunbounded hc
  have hlam : IsPowerAsymptotic lam T (1-4*α) := by
    convert ((hc _ (modelPhaseJetLower_pos hσ 3)).mul hTscale hT).div
      (cubic_power_natpow hNT hT 4) hT using 1
    ring
  have hB : IsPowerAsymptotic B T (1-4*α) := by
    convert ((hc (modelPhaseJetCoefficient σ 3+1)
      (by positivity [modelPhaseJetCoefficient_pos hσ 3])).mul hTscale hT).div
      (cubic_power_natpow hNT hT 4) hT using 1
    ring
  have hU : IsPowerAsymptotic U T (1-3*α) := by
    convert ((hc (modelPhaseJetCoefficient σ 2+1)
      (by positivity [modelPhaseJetCoefficient_pos hσ 2])).mul hTscale hT).div
      (cubic_power_natpow hNT hT 3) hT using 1
    ring
  have hQ : IsPowerAsymptotic Qcut T q := by
    convert (hc 3 (by norm_num)).div
      (((hc 2 (by norm_num)).mul hlam hT).mul (cubic_power_natpow hH hT 3) hT) hT using 1
    dsimp [q]
    ring
  have hV : IsPowerAsymptotic V T (α-2*h) := by
    convert hU.div (hlam.mul (cubic_power_natpow hH hT 2) hT) hT using 1
    ring
  have hf₁ : IsPowerAsymptotic f₁ T (-2*h) := by
    convert hV.div hNT hT using 1
    ring
  have hf₂ : IsPowerAsymptotic f₂ T (4*α-1-6*h) := by
    convert (hV.mul (hB.div ((cubic_power_natpow hlam hT 2).mul
      (cubic_power_natpow hH hT 4) hT) hT) hT).div hNT hT using 1
    ring
  have hf₃ : IsPowerAsymptotic f₃ T (4*α-1-6*h) := by
    convert (hV.mul (hQ.div hH hT) hT).div hNT hT using 1
    dsimp [q]
    ring
  have hf₄ : IsPowerAsymptotic f₄ T 0 := by
    convert (hV.mul (hQ.div hY hT) hT).div hNT hT using 1
    dsimp [q,h,r]
    ring
  have hf₅ : IsPowerAsymptotic f₅ T (η*(1-2*α+q+r)) := by
    convert (hV.mul (((cubic_power_rpow (hTscale.div
      (cubic_power_natpow hNT hT 2) hT) hT (13/84+η)).mul
        (cubic_power_rpow hQ hT (55/84+η)) hT).mul
          (cubic_power_rpow hY hT (13/84+η)) hT) hT).div hNT hT using 1
    dsimp [q,h,r]
    ring
  have hf₆ : IsPowerAsymptotic f₆ T (2*α-1-2*h) := by
    convert (hV.mul ((cubic_power_natpow hNT hT 2).div hTscale hT) hT).div hNT hT using 1
    ring
  have hmain : IsPowerAsymptotic
      (fun i => (N i)^7*U i*(H i:ℝ)^2*(H i:ℝ)^η) T (8*β+h*η) := by
    convert (((cubic_power_natpow hNT hT 7).mul hU hT).mul
      (cubic_power_natpow hH hT 2) hT).mul (cubic_power_rpow hH hT η) hT using 1
    dsimp [β,h]
    ring
  have hwidth : IsPowerAsymptotic (fun i => U i*(H i:ℝ)^2) T (1-3*α+2*h) := by
    convert hU.mul (cubic_power_natpow hH hT 2) hT using 1
    ring
  have hqβ : q < β := by dsimp [q,h,β]; linarith only [hlo,hhi]
  have h2hβ : 2*h < β := by dsimp [h,β]; linarith only [hlo,hhi]
  have hhβ : h < β := by linarith only [hh,h2hβ]
  have hβ : 0 < β := by linarith only [hh,hhβ]
  have he₂ : 4*α-1-6*h ≤ 0 := by dsimp [h]; linarith only [hhi]
  have he₆ : 2*α-1-2*h < 0 := by dsimp [h]; linarith only [hhi]
  have he₅ : 1-2*α+q+r < 1 := by dsimp [q,h,r]; linarith only [hhi]
  have hh1 : h < 1 := by dsimp [h]; linarith only [hhi]
  have hb₁ := cubic_power_eventually_le hf₁ hT (by linarith only [hh,hη] : -2*h<2*η)
  have hb₂ := cubic_power_eventually_le hf₂ hT (by linarith only [he₂,hη] : 4*α-1-6*h<2*η)
  have hb₃ := cubic_power_eventually_le hf₃ hT (by linarith only [he₂,hη] : 4*α-1-6*h<2*η)
  have hb₄ := cubic_power_eventually_le hf₄ hT (by linarith only [hη] : 0<2*η)
  have hb₅ := cubic_power_eventually_le hf₅ hT
    (by nlinarith only [he₅,hη] : η*(1-2*α+q+r)<2*η)
  have hb₆ := cubic_power_eventually_le hf₆ hT (by linarith only [he₆,hη] : 2*α-1-2*h<2*η)
  have hbmain := cubic_power_eventually_le hmain hT
    (by nlinarith only [hh1,hη] : 8*β+h*η<8*β+2*η)
  have hbH := cubic_power_eventually_le hH hT hhβ
  have hbH₂ := cubic_power_eventually_le (cubic_power_natpow hH hT 2) hT
    (by linarith only [h2hβ] : h*2<β)
  have hbQ := cubic_power_eventually_le hQ hT hqβ
  have hbwidth := (hwidth.tendsto_atTop_of_pos
    (by dsimp [h]; linarith only [hhi] : 0 < 1-3*α+2*h) hT hTunbounded).eventually
      (eventually_ge_atTop 1)
  have hNlarge := (hNT.tendsto_atTop_of_pos
    (by linarith only [hlo] : 0 < α) hT hTunbounded).eventually (eventually_gt_atTop 0)
  filter_upwards [hb₁,hb₂,hb₃,hb₄,hb₅,hb₆,hbmain,hbH,hbH₂,hbQ,hbwidth,hNlarge]
    with i h₁ h₂ h₃ h₄ h₅ h₆ hm hHi hH₂i hQi hwi hNi
  intro J hJ E
  have hTi : 0 < T i := zero_lt_one.trans_le (hT i)
  have hHp : (0:ℝ) < H i := by exact_mod_cast floorRpow_pos T h i
  have hUp : 0 < U i := by dsimp [U]; positivity [modelPhaseJetCoefficient_pos hσ 2]
  have hlampos : 0 < lam i := by dsimp [lam]; positivity [modelPhaseJetLower_pos hσ 3]
  have hQp : 0 < Qcut i := by dsimp [Qcut]; positivity
  have hVp : 0 < V i := by dsimp [V]; positivity
  have hsum : f₁ i+f₂ i+f₃ i+f₄ i+f₅ i+f₆ i ≤ 6*(T i)^(2*η) := by
    linarith only [h₁,h₂,h₃,h₄,h₅,h₆]
  have heq : E=((J:ℝ)+2)*N i*(f₁ i+f₂ i+f₃ i+f₄ i+f₅ i+f₆ i) := by
    dsimp [E,f₁,f₂,f₃,f₄,f₅,f₆,V]
    field_simp
  have hE : E ≤ 6*N i*(T i)^(3*η) := by
    rw [heq]
    calc
      _ ≤ ((J:ℝ)+2)*N i*(6*(T i)^(2*η)) := by gcongr
      _ ≤ (T i)^η*N i*(6*(T i)^(2*η)) := by gcongr
      _ = _ := by
        rw [show (T i)^η*N i*(6*(T i)^(2*η)) =
          6*N i*((T i)^η*(T i)^(2*η)) by ring,← Real.rpow_add hTi]
        congr 2
        ring
  have hone₃ : 1 ≤ (T i)^(3*η) := Real.one_le_rpow (hT i) (by positivity)
  have hNE : N i+E ≤ 7*N i*(T i)^(3*η) := by
    have hn := mul_le_mul_of_nonneg_left hone₃ hNi.le
    nlinarith only [hE,hn]
  have hUW : 1+U i*(H i:ℝ)^2 ≤ 2*U i*(H i:ℝ)^2 := by linarith only [hwi]
  have hcost : (N i)^6*(N i+E)*(1+U i*(H i:ℝ)^2)*(H i:ℝ)^η ≤
      14*(T i)^(8*β+5*η) := by
    calc
      _ ≤ (N i)^6*(7*N i*(T i)^(3*η))*(2*U i*(H i:ℝ)^2)*(H i:ℝ)^η := by gcongr
      _ = 14*((N i)^7*U i*(H i:ℝ)^2*(H i:ℝ)^η)*(T i)^(3*η) := by ring
      _ ≤ 14*(T i)^(8*β+2*η)*(T i)^(3*η) := by gcongr
      _ = _ := by rw [mul_assoc,← Real.rpow_add hTi]; congr 2; ring
  have honeβ : 1 ≤ (T i)^β := Real.one_le_rpow (hT i) hβ.le
  have hR : (H i:ℝ)^2+Qcut i+1 ≤ 3*(T i)^β := by
    linarith only [hH₂i,hQi,honeβ]
  have hH8 : (H i:ℝ)^8 ≤ (T i)^(8*β+5*η) := by
    calc
      _ ≤ ((T i)^β)^8 := pow_le_pow_left₀ hHp.le hHi 8
      _ = (T i)^(8*β) := by rw [← Real.rpow_mul_natCast hTi.le]; congr 1; ring
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (hT i) (by linarith only [hη])
  have hR8 : ((H i:ℝ)^2+Qcut i+1)^8 ≤ 3^8*(T i)^(8*β+5*η) := by
    calc
      _ ≤ (3*(T i)^β)^8 := pow_le_pow_left₀ (by positivity) hR 8
      _ = 3^8*(T i)^(8*β) := by
        rw [mul_pow,← Real.rpow_mul_natCast hTi.le]
        congr 2
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le (hT i) (by linarith only [hη])) (by norm_num)
  linarith only [hcost,hH8,hR8]


/-- Analytic closure of the missing D(Bourgain) interval. This consumes the
literal original sum, the proved Bourgain pair, and the linked physical
scales; no derivative-count or sum estimate is an input. -/
theorem isExponentSumBound_cubic_bourgain_gap
    {α : ℝ≥0} (hlo : 140/391 ≤ (α:ℝ)) (hhi : (α:ℝ) < 16/39) :
    IsExponentSumBound α (18/199+(521/796)*(α:ℝ)) := by
  intro N T F a b _hN hT hTunbounded hNT hF hab
  apply (isPowerBounded_iff_forall_pos
    (exponentialSum F T N a b) T (18/199+(521/796)*(α:ℝ)) hT hTunbounded).mpr
  intro ε hε
  let η := min ((1:ℝ)/100) ε
  have hη : 0 < η := lt_min (by norm_num) hε
  have hηε : η ≤ ε := min_le_right _ _
  have hηsmall : (13/84:ℝ)+η < 1 := by
    have hh : η ≤ (1:ℝ)/100 := min_le_left _ _
    linarith only [hh]
  obtain ⟨hphase,σ,hσ,herror⟩ := hF
  obtain ⟨δ,κ₀,hδ,hκ₀,Q,_hQ,C₀,hC₀,hsource⟩ :=
    TaoTrudgianYang2025.CubicJointCount.exists_complete_cubic_eighth_estimate
      hσ exponentPair_bourgain hη hηsmall
  have happrox := (IsModelPhaseFunctionWith.mk hphase herror).eventually_isApproximate Q hδ
  have hparameters := eventually_cubic_bourgain_parameters hlo hhi hσ hκ₀ hη hT hTunbounded hNT
  have hcost := eventually_cubic_bourgain_cost hlo hhi hσ hη hT hTunbounded hNT
  let β := 18/199+(521/796)*(α:ℝ)
  let C := max 1 (C₀*(15+3^8))
  have hC : 1 ≤ C := le_max_left _ _
  have hC₀C : C₀*(15+3^8) ≤ C := le_max_right _ _
  have hCpow : C ≤ C^8 := by
    calc
      C = C*1 := (mul_one C).symm
      _ ≤ C*C^7 := mul_le_mul_of_nonneg_left (one_le_pow₀ hC) (zero_le_one.trans hC)
      _ = _ := by ring
  refine Asymptotics.IsBigO.of_bound C ?_
  filter_upwards [happrox,hparameters,hcost] with i hFi hpi hci
  obtain ⟨hNi,hHi,hYi,J,hQi,hQJ,hJ,hcurv,hshift,hTaylor⟩ := hpi
  have hTi : 0 < T i := zero_lt_one.trans_le (hT i)
  have hs := hsource (F i) (T i) (N i)
    ((T i)^((362*(α:ℝ)-123)/398)) (a i) (b i)
    (floorRpow T ((246*(α:ℝ)-55)/398) i) J
    hFi hTi hNi hHi hYi (hab i).1 (hab i).2
    hQi hQJ hcurv hshift hTaylor
  have hmajor := mul_le_mul_of_nonneg_left (hci J hJ) hC₀.le
  have hbound : ‖exponentialSumAt (F i) (T i) (N i) (a i) (b i)‖^8 ≤
      C₀*(15+3^8)*(T i)^(8*β+5*η) := by
    exact hs.trans (by convert hmajor using 1; ring)
  have hexp : 8*β+5*η ≤ (β+ε)*8 := by linarith only [hηε,hε]
  have hp : ‖exponentialSumAt (F i) (T i) (N i) (a i) (b i)‖^8 ≤
      (C*(T i)^(β+ε))^8 := by
    calc
      _ ≤ C₀*(15+3^8)*(T i)^(8*β+5*η) := hbound
      _ ≤ C^8*(T i)^((β+ε)*8) :=
        mul_le_mul (hC₀C.trans hCpow) (Real.rpow_le_rpow_of_exponent_le (hT i) hexp)
          (Real.rpow_nonneg hTi.le _) (by positivity)
      _ = _ := by rw [mul_pow,← Real.rpow_mul_natCast hTi.le]; norm_num
  have hh := (pow_le_pow_iff_left₀ (norm_nonneg _)
    (by positivity : 0 ≤ C*(T i)^(β+ε)) (by norm_num : (8:ℕ)≠0)).mp hp
  simpa only [exponentialSum_apply,Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg hTi.le _)] using hh

theorem exponentSumGrowthExponent_le_cubic_bourgain_gap
    {α : ℝ≥0} (hlo : 140/391 ≤ (α:ℝ)) (hhi : (α:ℝ) < 16/39) :
    exponentSumGrowthExponent α ≤ 18/199+(521/796)*(α:ℝ) :=
  exponentSumGrowthExponent_le_iff.mpr (isExponentSumBound_cubic_bourgain_gap hlo hhi)

/-- The already proved analytic inputs cover the D(Bourgain) target outside
one exact open interval. No estimate on that remaining interval is assumed. -/
theorem bourgain_d_target_outside_gap
    {α : NNReal} (hhalf : (α:ℝ) ≤ 1/2)
    (hgap : (α:ℝ) ≤ 140/391 ∨ 16/39 ≤ (α:ℝ)) :
    exponentSumGrowthExponent α ≤ (18:ℝ)/199+521/796*(α:ℝ) := by
  rcases hgap with hlo | hhi
  · have h := exponentSumGrowthExponent_le_exponentPairLine_closed
      exponentPair_robertSargos α (by linarith only [hhalf])
    unfold exponentPairLine at h
    linarith only [h,hlo]
  · by_cases hfirst : (α:ℝ) ≤ 5/12
    · have h := TaoTrudgianYang2025.exponentSumGrowthExponent_le_bourgain_table_first
        (α:=α) (by linarith only [hhi]) hfirst
      linarith only [h,hhi]
    · by_cases hsecond : (α:ℝ) ≤ 3/7
      · have h := TaoTrudgianYang2025.exponentSumGrowthExponent_le_bourgain_table_second
          (α:=α) (le_of_not_ge hfirst) hsecond
        linarith only [h,hhalf]
      · have h := exponentSumGrowthExponent_le_bourgain_baseline
          (α:=α) (le_of_not_ge hsecond) hhalf
        have hα : (3:ℝ)/7 ≤ (α:ℝ) := le_of_not_ge hsecond
        linarith only [h,hα]

theorem exponentPair_sargosD_bourgain : ExponentPair (18/199) (593/796) := by
  apply exponentPair_of_beta_bound_half (by norm_num [InExponentPairTriangle]) (by norm_num)
  intro α hhalf
  have hbound : exponentSumGrowthExponent α ≤ 18/199+(521/796)*(α:ℝ) := by
    by_cases hlo : (α:ℝ) ≤ 140/391
    · exact bourgain_d_target_outside_gap hhalf (Or.inl hlo)
    · by_cases hhi : (α:ℝ) < 16/39
      · exact exponentSumGrowthExponent_le_cubic_bourgain_gap (le_of_not_ge hlo) hhi
      · exact bourgain_d_target_outside_gap hhalf (Or.inr (le_of_not_gt hhi))
  convert hbound using 1
  unfold exponentPairLine
  ring

theorem exponentPair_sargosAD_bourgain : ExponentPair (9/217) (1461/1736) := by
  have h := exponentPair_sargosD_bourgain.aProcess
  norm_num at h
  exact h

theorem exponentSumGrowthExponent_le_sargosD_bourgain
    {α : ℝ≥0} (hα : (α:ℝ) ≤ 1) :
    exponentSumGrowthExponent α ≤ 18/199+(521/796)*(α:ℝ) := by
  have h := exponentSumGrowthExponent_le_exponentPairLine_closed exponentPair_sargosD_bourgain α hα
  convert h using 1
  unfold exponentPairLine
  ring

theorem exponentSumGrowthExponent_le_sargosAD_bourgain
    {α : ℝ≥0} (hα : (α:ℝ) ≤ 1) :
    exponentSumGrowthExponent α ≤ 9/217+(1389/1736)*(α:ℝ) := by
  have h := exponentSumGrowthExponent_le_exponentPairLine_closed exponentPair_sargosAD_bourgain α hα
  convert h using 1
  unfold exponentPairLine
  ring

theorem original_joint_level_displacement_count
    {σ k₀ l₀ ε : ℝ} (hσ : 0 < σ)
    (hpair : ExponentPair k₀ l₀) (hε : 0 < ε) (hp : k₀+ε < 1) :
    ∃ δ κ₀ : ℝ, 0 < δ ∧ 0 < κ₀ ∧
      ∃ Q : ℕ, 2 ≤ Q ∧ ∃ C : ℝ, 1 ≤ C ∧
        ∀ (F : ℝ → ℝ) (T N d D a b R B lam δ₁ δ₂ W : ℝ)
          (K : ℤ) (S : Finset (ℤ × ℕ)),
          IsApproximateModelPhaseFunction F σ Q δ →
          0 < T → 0 < N → 2 ≤ d → 0 < D → 0 < R → 0 ≤ B → 0 < lam →
          N < a-R → b+R+2*D < 2*N →
          δ₂ ≤ lam*d*R/2 → δ₁+2*B*D*R^2 ≤ W/2 →
          0 < K → 2*(K:ℝ)*N^2/(σ*T) ≤ κ₀ → 0 < W → W ≤ 1/2 →
          let f := fun z => T*F (z/N)
          (∀ t∈Icc (a-R) (b+R+2*D),
            -B ≤ iteratedDeriv 4 f t ∧ iteratedDeriv 4 f t ≤ -lam) →
          (∀ p∈S, (p.1:ℝ)∈Icc a b ∧ (p.2:ℝ)∈Icc d (2*D)) →
          (∀ p∈S, |(iteratedDeriv 2 f ((p.1:ℝ)+(p.2:ℝ))-
            iteratedDeriv 2 f p.1)/2-(K:ℝ)| ≤ δ₂) →
          (∀ p∈S, ∃ e : ℤ, |iteratedDeriv 1 f ((p.1:ℝ)+(p.2:ℝ))-
            iteratedDeriv 1 f p.1-(e:ℝ)| ≤ δ₁) →
            ((S.image Prod.snd).card:ℝ) ≤
              C*(W*D+(T/N^2)^(k₀+ε)*D^(l₀+ε)*W^(-(k₀+ε))+N^2/T) := by
  classical
  obtain ⟨δ,κ₀,hδ,hκ₀,Q,hQ,C,hC,hcount⟩ :=
    original_second_level_near_curve_count hσ hpair hε hp
  refine ⟨δ,κ₀,hδ,hκ₀,Q,hQ,C,hC,?_⟩
  intro F T N d D a b R B lam δ₁ δ₂ W K S hF hT hN hd hDpos hR hB hlam
    hleft hright hbuffer hwidth hK hκle hW hWhalf f hfour hbox hsecond hfirst
  have hdpos : 0 < d := by linarith
  let J := S.image Prod.snd
  have hmem (q : ℕ) (hq : q∈J) : d ≤ (q:ℝ) ∧ (q:ℝ) ≤ 2*D := by
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hq
    exact (hbox p hp).2
  have hnorm (t : ℝ) (ht : t∈Icc (a-R) (b+R+2*D)) :
      t/N∈Ioo (1:ℝ) 2 := by
    constructor
    · apply (one_lt_div hN).mpr
      linarith [ht.1]
    · apply (div_lt_iff₀ hN).mpr
      linarith [ht.2]
  have hf (t : ℝ) (ht : t∈Icc (a-R) (b+R+2*D)) : ContDiffAt ℝ 4 f t := by
    have hc := (approximateModelPhase_contDiffAt hF (hnorm t ht)).comp t
      (show ContDiffAt ℝ ∞ (fun z : ℝ => z/N) t by fun_prop)
    exact (contDiffAt_const.mul hc).of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 4)
  have hex (q : ℕ) (hq : q∈J) :
      ∃ x : ℝ, x/N∈Ioo (1:ℝ) 2 ∧ (x+(q:ℝ))/N∈Ioo (1:ℝ) 2 ∧
        (iteratedDeriv 2 f (x+(q:ℝ))-iteratedDeriv 2 f x)/2=(K:ℝ) ∧
        ∃ e : ℤ, |iteratedDeriv 1 f (x+(q:ℝ))-iteratedDeriv 1 f x-
          2*(K:ℝ)*x-(e:ℝ)| ≤ W/2 := by
    obtain ⟨p,hps,hpq⟩ := Finset.mem_image.mp hq
    have hpos : 0 < (q:ℝ) := hdpos.trans_le (hmem q hq).1
    have hpab : (p.1:ℝ)∈Icc a b := (hbox p hps).1
    have hsub : Icc ((p.1:ℝ)-R) ((p.1:ℝ)+R+(q:ℝ)) ⊆ Icc (a-R) (b+R+2*D) := by
      intro t ht
      constructor <;> linarith [ht.1,ht.2,hpab.1,hpab.2,(hmem q hq).2]
    have hbudget : δ₂ ≤ lam*(q:ℝ)*R/2 := hbuffer.trans (by gcongr; exact (hmem q hq).1)
    have hnear₂ : |(iteratedDeriv 2 f ((p.1:ℝ)+(q:ℝ))-iteratedDeriv 2 f p.1)/2-(K:ℝ)| ≤ δ₂ := by
      simpa only [hpq] using hsecond p hps
    obtain ⟨x,hx,hlevel,_hdist⟩ := cubic_exact_second_difference_level
      f hpos hR hbudget (fun t ht => hf t (hsub ht))
      (fun t ht => hfour t (hsub ht)) hnear₂
    obtain ⟨e,he⟩ := hfirst p hps
    rw [hpq] at he
    have hnear := cubic_stationary_curve_near_integer
      f p.1 K e hpos hlam hR.le hx (fun t ht => hf t (hsub ht))
      (fun t ht => hfour t (hsub ht)) hlevel he
    have hxx : x∈Icc (a-R) (b+R+2*D) := hsub ⟨hx.1,by linarith [hx.2]⟩
    have hxxq : x+(q:ℝ)∈Icc (a-R) (b+R+2*D) :=
      hsub ⟨by linarith [hx.1],by linarith [hx.2]⟩
    refine ⟨x,hnorm x hxx,hnorm (x+q) hxxq,hlevel,e-2*K*p.1,?_⟩
    exact hnear.trans ((show δ₁+B*(q:ℝ)*R^2 ≤ δ₁+2*B*D*R^2 by
      nlinarith [mul_le_mul_of_nonneg_left (hmem q hq).2
        (mul_nonneg hB (sq_nonneg R))]).trans hwidth)
  let x := fun q => if hq : q∈J then Classical.choose (hex q hq) else 0
  have hx (q : ℕ) (hq : q∈J) :
      x q/N∈Ioo (1:ℝ) 2 ∧ (x q+(q:ℝ))/N∈Ioo (1:ℝ) 2 ∧
        (iteratedDeriv 2 f (x q+(q:ℝ))-iteratedDeriv 2 f (x q))/2=(K:ℝ) ∧
        ∃ e : ℤ, |iteratedDeriv 1 f (x q+(q:ℝ))-iteratedDeriv 1 f (x q)-
          2*(K:ℝ)*x q-(e:ℝ)| ≤ W/2 := by
    simp only [x,dif_pos hq]
    exact Classical.choose_spec (hex q hq)
  have hcountJ := hcount F T N D K J x hF hT hN hDpos hK hκle
    (fun q hq => (hx q hq).1) (fun q hq => (hx q hq).2.1)
    (fun q hq => ⟨hd.trans (hmem q hq).1,(hmem q hq).2⟩)
    (fun q hq => (hx q hq).2.2.1) W hW hWhalf (fun q hq => (hx q hq).2.2.2)
  exact hcountJ

/-- The original-model near-curve estimate applied to a labelled block source.
No cardinality estimate is an input; both the displacement image and its
source multiplicities are derived. -/
theorem original_model_block_source_pair_count
    {σ k₀ l₀ ε : ℝ} (hσ : 0 < σ)
    (hpair : ExponentPair k₀ l₀) (hε : 0 < ε) (hp : k₀+ε < 1) :
    ∃ δ κ₀ : ℝ, 0 < δ ∧ 0 < κ₀ ∧
      ∃ Q : ℕ, 2 ≤ Q ∧ ∃ C : ℝ, 1 ≤ C ∧
        ∀ {ι : Type*} [DecidableEq ι] (S : Finset ι) (V : Finset (ι × ι))
          (center block : ι → ℤ) (H Bmul : ℕ) (s K : ℤ)
          (F : ℝ → ℝ) (T N d D a b R B lam δ₁ δ₂ W : ℝ),
          IsApproximateModelPhaseFunction F σ Q δ →
          0 < T → 0 < N → 2 ≤ d → 0 < D → 0 < R → 0 ≤ B →
          0 < lam → 0 ≤ δ₂ → 0 < H →
          N < a-R → b+R+2*D < 2*N →
          δ₂ ≤ lam*d*R/2 → δ₁+2*B*D*R^2 ≤ W/2 →
          0 < K → 2*(K:ℝ)*N^2/(σ*T) ≤ κ₀ → 0 < W → W ≤ 1/2 →
          (∀ i∈S, (H:ℤ) ≤ s+(H:ℤ)*block i-center i ∧
            s+(H:ℤ)*block i-center i ≤ 3*(H:ℤ)) →
          (∀ j : ℤ, (S.filter (fun i => block i=j)).card ≤ Bmul) →
          (∀ i∈S, (center i:ℝ)∈Icc a b) →
          V ⊆ S ×ˢ S →
          (∀ p∈V, (center p.2:ℝ)-center p.1∈Icc d (2*D)) →
          let f := fun z => T*F (z/N)
          (∀ t∈Icc (a-R) (b+R+2*D),
            -B ≤ iteratedDeriv 4 f t ∧ iteratedDeriv 4 f t ≤ -lam) →
          (∀ p∈V, |(iteratedDeriv 2 f (center p.2)-
            iteratedDeriv 2 f (center p.1))/2-(K:ℝ)| ≤ δ₂) →
          (∀ p∈V, ∃ e : ℤ, |iteratedDeriv 1 f (center p.2)-
            iteratedDeriv 1 f (center p.1)-(e:ℝ)| ≤ δ₁) →
            (V.card:ℝ) ≤ (3*(Bmul:ℝ)^2*(3+8*δ₂/(lam*d*H)))*
              (C*(W*D+(T/N^2)^(k₀+ε)*D^(l₀+ε)*W^(-(k₀+ε))+N^2/T)) := by
  classical
  obtain ⟨δ,κ₀,hδ,hκ₀,Q,hQ,C,hC,hcount⟩ :=
    original_joint_level_displacement_count hσ hpair hε hp
  refine ⟨δ,κ₀,hδ,hκ₀,Q,hQ,C,hC,?_⟩
  intro ι _ S V center block H Bmul s K F T N d D a b R B lam δ₁ δ₂ W
    hF hT hN hd hD hR hB hlam hδ₂ hH hleft hright hbuffer hwidth hK hκle hW hWhalf
    hspan hmul hcenter hVS hdisp f hfour hsecond hfirst
  have hdp : 0 < d := by linarith
  have hHr : (0:ℝ) < H := by exact_mod_cast hH
  let n := fun p : ι × ι => (center p.2-center p.1).toNat
  let E := V.image (fun p => (center p.1,n p))
  let J := E.image Prod.snd
  have hn p (hp : p∈V) : (n p:ℝ)=(center p.2:ℝ)-center p.1 := by
    have hnn : 0 ≤ center p.2-center p.1 := by
      exact_mod_cast (hdp.le.trans (hdisp p hp).1)
    have he := Int.toNat_of_nonneg hnn
    exact_mod_cast he
  have hpoints p (hp : p∈V) : (center p.1:ℝ)+(n p:ℝ)=center p.2 := by
    rw [hn p hp]
    ring
  have hcountJ : (J.card:ℝ) ≤
      C*(W*D+(T/N^2)^(k₀+ε)*D^(l₀+ε)*W^(-(k₀+ε))+N^2/T) := by
    apply hcount F T N d D a b R B lam δ₁ δ₂ W K E hF hT hN hd hD hR hB hlam
      hleft hright hbuffer hwidth hK hκle hW hWhalf hfour
    · intro p hp
      obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hp
      exact ⟨hcenter _ (Finset.mem_product.mp (hVS hv)).1, by
        simpa only [hn v hv] using hdisp v hv⟩
    · intro p hp
      obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hp
      simpa only [hpoints v hv] using hsecond v hv
    · intro p hp
      obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hp
      simpa only [hpoints v hv] using hfirst v hv
  have hf t (ht : t∈Ioo (a-R) (b+R+2*D)) : ContDiffAt ℝ 4 f t := by
    have hnrm : t/N∈Ioo (1:ℝ) 2 := by
      constructor
      · apply (one_lt_div hN).mpr
        linarith [ht.1]
      · apply (div_lt_iff₀ hN).mpr
        linarith [ht.2]
    have hc := (approximateModelPhase_contDiffAt hF hnrm).comp t
      (show ContDiffAt ℝ ∞ (fun z : ℝ => z/N) t by fun_prop)
    exact (contDiffAt_const.mul hc).of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 4)
  have hcent i (hi : i∈S) : (center i:ℝ)∈Ioo (a-R) (b+R+2*D) := by
    constructor <;> linarith [(hcenter i hi).1,(hcenter i hi).2]
  let M := 3*(Bmul:ℝ)^2*(3+8*δ₂/(lam*d*H))
  have hM : 0 ≤ M := by dsimp only [M]; positivity
  have hfiber q : ((V.filter (fun p => n p=q)).card:ℝ) ≤ M := by
    let Vq := V.filter (fun p => n p=q)
    by_cases hvq : Vq.Nonempty
    · obtain ⟨v,hv⟩ := hvq
      obtain ⟨hv,he⟩ := Finset.mem_filter.mp hv
      have hqd : d ≤ (q:ℝ) := by rw [←he,hn v hv]; exact (hdisp v hv).1
      have hqp : (0:ℝ)<q := hdp.trans_le hqd
      have hb := fixed_displacement_source_pair_fibers S Vq center block H Bmul s f
        hH hlam hqp hδ₂ hspan hmul hf
        (fun t ht => (hfour t ⟨ht.1.le,ht.2.le⟩).2) hcent
        (fun p hp => hVS (Finset.mem_filter.mp hp).1)
        (fun p hp => by
          rw [←hn p (Finset.mem_filter.mp hp).1,(Finset.mem_filter.mp hp).2])
        (fun p hp => hsecond p (Finset.mem_filter.mp hp).1)
      have hfrac : 8*δ₂/(lam*(q:ℝ)*H) ≤ 8*δ₂/(lam*d*H) :=
        div_le_div_of_nonneg_left (by positivity) (by positivity)
          (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hqd hlam.le) hHr.le)
      exact hb.trans (mul_le_mul_of_nonneg_left (add_le_add le_rfl hfrac) (by positivity))
    · change (Vq.card:ℝ) ≤ M
      rw [Finset.not_nonempty_iff_eq_empty.mp hvq,Finset.card_empty,Nat.cast_zero]
      exact hM
  have hmap p (hp : p∈V) : n p∈J :=
    Finset.mem_image.mpr ⟨(center p.1,n p),Finset.mem_image_of_mem _ hp,rfl⟩
  have hc : (V.card:ℝ)=∑ q∈J,((V.filter (fun p => n p=q)).card:ℝ) := by
    exact_mod_cast Finset.card_eq_sum_card_fiberwise hmap
  calc
    _ = _ := hc
    _ ≤ ∑ _q∈J,M := Finset.sum_le_sum (fun q _ => hfiber q)
    _ = M*J.card := by simp [mul_comm]
    _ ≤ _ := mul_le_mul_of_nonneg_left hcountJ hM

/-- A positive curvature shift in the actual model, with the rounded source
multiplicity retained and all derivative assumptions derived from the model. -/
theorem original_model_rounded_shift_count
    {σ k₀ l₀ ε : ℝ} (hσ : 0 < σ)
    (hpair : ExponentPair k₀ l₀) (hε : 0 < ε) (hp : k₀+ε < 1) :
    ∃ δ κ₀ : ℝ, 0 < δ ∧ 0 < κ₀ ∧
      ∃ Q : ℕ, 3 ≤ Q ∧ ∃ C : ℝ, 1 ≤ C ∧
        ∀ {ι : Type*} [DecidableEq ι] (S : Finset ι) (V : Finset (ι × ι))
          (center block : ι → ℤ) (z : ι → ℝ) (H Bmul : ℕ) (s K : ℤ)
          (F : ℝ → ℝ) (T N a b R δ₁ W : ℝ),
          IsApproximateModelPhaseFunction F σ Q δ →
          0 < T → 0 < N → 0 < R → 0 < H → 0 < K →
          let L := modelPhaseJetLower σ 2*T/N^3
          let U := (modelPhaseJetCoefficient σ 2+1)*T/N^3
          let lam := modelPhaseJetLower σ 3*T/N^4
          let B := (modelPhaseJetCoefficient σ 3+1)*T/N^4
          let d := (K:ℝ)/(6*U)
          let D := (K:ℝ)/L+1
          12*U ≤ 1 → N < a-R → b+R+2*D < 2*N →
          3*U ≤ lam*d*R/2 → δ₁+2*B*D*R^2 ≤ W/2 →
          2*(K:ℝ)*N^2/(σ*T) ≤ κ₀ → 0 < W → W ≤ 1/2 →
          (∀ i∈S, (H:ℤ) ≤ s+(H:ℤ)*block i-center i ∧
            s+(H:ℤ)*block i-center i ≤ 3*(H:ℤ)) →
          (∀ j : ℤ, (S.filter (fun i => block i=j)).card ≤ Bmul) →
          (∀ i∈S, (center i:ℝ)∈Icc a b) →
          (∀ i∈S, z i∈Ioo N (2*N)) →
          (∀ i∈S, |(center i:ℝ)-z i| ≤ 1/2) →
          V ⊆ S ×ˢ S →
          let f := fun t => T*F (t/N)
          (∀ p∈V, iteratedDeriv 2 f (z p.2)/2-
            iteratedDeriv 2 f (z p.1)/2=(K:ℝ)) →
          (∀ p∈V, ∃ e : ℤ, |iteratedDeriv 1 f (center p.2)-
            iteratedDeriv 1 f (center p.1)-(e:ℝ)| ≤ δ₁) →
            (V.card:ℝ) ≤ (3*(Bmul:ℝ)^2*(3+144*U^2/(lam*(K:ℝ)*H)))*
              (C*(W*D+(T/N^2)^(k₀+ε)*D^(l₀+ε)*W^(-(k₀+ε))+N^2/T)) := by
  classical
  obtain ⟨δ₀,κ₀,hδ₀,hκ₀,Q₀,hQ₀,C,hC,hcount⟩ :=
    original_model_block_source_pair_count hσ hpair hε hp
  obtain ⟨δd,hδd,hdata⟩ := model_displacement_derivative_data hσ
  let δ := min δ₀ δd
  let Q := max Q₀ 3
  refine ⟨δ,κ₀,lt_min hδ₀ hδd,hκ₀,Q,le_max_right _ _,C,hC,?_⟩
  intro ι _ S V center block z H Bmul s K F T N a b R δ₁ W
    hF hT hN hR hH hK L U lam B d D hUsmall hleft hright hbuffer hwidth
    hκle hW hWhalf hspan hmul hcenter hz hround hVS f hlevel hfirst
  have hF₀ := approximateModelPhase_mono hF (le_max_left _ _) (min_le_left _ _)
  have hFd := approximateModelPhase_mono hF (le_max_right _ _) (min_le_right _ _)
  obtain ⟨hreg,hthree,hfour,_⟩ := hdata F T N hT hN hFd
  have hlam : 0 < lam := by dsimp only [lam]; positivity [modelPhaseJetLower_pos hσ 3]
  have hL : 0 < L := by dsimp only [L]; positivity [modelPhaseJetLower_pos hσ 2]
  have hU : 0 < U := by dsimp only [U]; positivity [modelPhaseJetCoefficient_pos hσ 2]
  have hB : 0 ≤ B := by dsimp only [B]; positivity [modelPhaseJetCoefficient_pos hσ 3]
  have hKr : (1:ℝ) ≤ K := by exact_mod_cast (show (1:ℤ) ≤ K by omega)
  have hKp : (0:ℝ) < K := zero_lt_one.trans_le hKr
  have hd : 2 ≤ d := by
    apply (le_div_iff₀ (by positivity : 0 < 6*U)).mpr
    linarith
  have hD : 0 < D := by dsimp only [D]; positivity
  have hsegment : Icc (a-R) (b+R+2*D) ⊆ Ioo N (2*N) := by
    intro t ht
    constructor <;> linarith [ht.1,ht.2]
  have hcent i (hi : i∈S) : (center i:ℝ)∈Ioo N (2*N) := by
    apply hsegment
    constructor <;> linarith [(hcenter i hi).1,(hcenter i hi).2]
  have hthree' t (ht : t∈Ioo N (2*N)) :
      L ≤ iteratedDeriv 3 f t ∧ iteratedDeriv 3 f t ≤ 6*U := by
    have hh := hthree t ht
    exact ⟨hh.1,by linarith [hh.2]⟩
  have hdisp p (hp : p∈V) : (center p.2:ℝ)-center p.1∈Icc d (2*D) := by
    have hpp := Finset.mem_product.mp (hVS hp)
    have hb := rounded_positive_curvature_shift_bounds f hL hU
      (by linarith only [hUsmall,hKr,hU] : 6*U ≤ (K:ℝ))
      (fun t ht => (hreg t ht).of_le (by norm_num)) hthree'
      (hz _ hpp.1) (hz _ hpp.2) (hround _ hpp.1) (hround _ hpp.2) (hlevel p hp)
    refine ⟨hb.1,?_⟩
    dsimp only [D]
    have hbhi : (center p.2:ℝ)-center p.1 ≤ 2*((K:ℝ)/L)+1 := by
      simpa only [mul_div_assoc] using hb.2
    linarith only [hbhi]
  have hsecond p (hp : p∈V) :
      |(iteratedDeriv 2 f (center p.2)-iteratedDeriv 2 f (center p.1))/2-(K:ℝ)| ≤ 3*U := by
    have hpp := Finset.mem_product.mp (hVS hp)
    have hseg : uIcc (z p.1) (center p.1:ℝ) ∪ uIcc (z p.2) (center p.2:ℝ) ⊆ Ioo N (2*N) :=
      union_subset ((convex_Ioo N (2*N)).ordConnected.uIcc_subset (hz _ hpp.1) (hcent _ hpp.1))
        ((convex_Ioo N (2*N)).ordConnected.uIcc_subset (hz _ hpp.2) (hcent _ hpp.2))
    apply rounded_curvature_difference_error f
      (fun t ht => (hreg t (hseg ht)).of_le (by norm_num)) ?_
      (hround _ hpp.1) (hround _ hpp.2) (hlevel p hp)
    intro t ht
    rw [abs_of_pos (hL.trans_le (hthree' t (hseg ht)).1)]
    exact (hthree' t (hseg ht)).2
  have hb := hcount S V center block H Bmul s K F T N d D a b R B lam δ₁ (3*U) W
    hF₀ hT hN hd hD hR hB hlam (by positivity) hH hleft hright hbuffer hwidth
    hK hκle hW hWhalf hspan hmul hcenter hVS hdisp
    (fun t ht => hfour t (hsegment ht)) hsecond hfirst
  have he : 8*(3*U)/(lam*d*H)=144*U^2/(lam*(K:ℝ)*H) := by
    dsimp only [d]
    field_simp
    ring
  rwa [he] at hb

/-- A free Fourier width absorbs the rounded-center lifting error uniformly
over positive curvature shifts, without changing the displacement multiplicity. -/
theorem rounded_shift_free_width
    {L U lam B K η w : ℝ}
    (hL : 0 < L) (hU : 0 < U) (hlam : 0 < lam) (hB : 0 ≤ B)
    (hK : 1 ≤ K) (hLK : L ≤ K) (hη : 0 ≤ η) (hw : 0 < w) (hwhalf : w ≤ 1/2)
    (hsmall : 2*η+10368*B*U^4/(lam^2*L) ≤ 1/2) :
    let d := K/(6*U)
    let D := K/L+1
    let R := 36*U^2/(lam*K)
    let W := max (2*η+4*B*D*R^2) w
    0 < R ∧ 0 < W ∧ W ≤ 1/2 ∧
      3*U=lam*d*R/2 ∧ η+2*B*D*R^2 ≤ W/2 ∧
      W*D ≤ (2*η+w)*D+20736*B*U^4/(lam^2*L^2) ∧
      ∀ p : ℝ, 0 ≤ p → W^(-p) ≤ w^(-p) := by
  intro d D R W
  have hKp : 0 < K := zero_lt_one.trans_le hK
  have hD : 0 < D := by dsimp only [D]; positivity
  have hR : 0 < R := by dsimp only [R]; positivity
  have hDup : D ≤ 2*K/L := by
    have h1 : 1 ≤ K/L := (one_le_div hL).mpr hLK
    dsimp only [D]
    rw [mul_div_assoc]
    linarith
  have hraw : 4*B*D*R^2 ≤ 10368*B*U^4/(lam^2*L) := by
    calc
      _ ≤ 4*B*(2*K/L)*R^2 := by gcongr
      _ = 10368*B*U^4/(lam^2*L*K) := by dsimp only [R]; field_simp; ring
      _ ≤ _ := div_le_div_of_nonneg_left (by positivity) (by positivity)
        (by nlinarith [mul_le_mul_of_nonneg_left hK (show 0 ≤ lam^2*L by positivity)])
  have hW : 0 < W := hw.trans_le (le_max_right _ _)
  have hwidth : η+2*B*D*R^2 ≤ W/2 := by
    have hh : 2*η+4*B*D*R^2 ≤ W := le_max_left _ _
    linarith
  have hbudget : 4*B*D^2*R^2 ≤ 20736*B*U^4/(lam^2*L^2) := by
    calc
      _ ≤ 4*B*(2*K/L)^2*R^2 := by gcongr
      _ = _ := by dsimp only [R]; field_simp; ring
  have hWD : W*D ≤ (2*η+w)*D+20736*B*U^4/(lam^2*L^2) := by
    have hsum : W ≤ 2*η+4*B*D*R^2+w := by
      apply max_le
      · linarith
      · have hh : 0 ≤ 2*η+4*B*D*R^2 := by positivity
        linarith
    calc
      _ ≤ (2*η+4*B*D*R^2+w)*D := mul_le_mul_of_nonneg_right hsum hD.le
      _ = (2*η+w)*D+4*B*D^2*R^2 := by ring
      _ ≤ _ := add_le_add le_rfl hbudget
  refine ⟨hR,hW,max_le (by linarith only [hraw,hsmall]) hwhalf,?_,hwidth,hWD,?_⟩
  · dsimp only [d,R]
    field_simp
    ring
  · intro p hp
    exact Real.rpow_le_rpow_of_nonpos hw (le_max_right _ _) (neg_nonpos.mpr hp)

/-- Uniform positive-shift estimate. The Fourier width is chosen inside the
proof, including the rounded-center lifting error; the shift weight is retained
for the subsequent harmonic sum. -/
theorem original_model_uniform_positive_shift_count
    {σ k₀ l₀ ε : ℝ} (hσ : 0 < σ)
    (hpair : ExponentPair k₀ l₀) (hε : 0 < ε) (hp : k₀+ε < 1) :
    ∃ δ κ₀ : ℝ, 0 < δ ∧ 0 < κ₀ ∧
      ∃ Q : ℕ, 3 ≤ Q ∧ ∃ C : ℝ, 1 ≤ C ∧
        ∀ {ι : Type*} [DecidableEq ι] (S : Finset ι) (V : Finset (ι × ι))
          (center block : ι → ℤ) (z : ι → ℝ) (H Bmul : ℕ) (s K : ℤ)
          (F : ℝ → ℝ) (T N a b Kmax η w : ℝ),
          IsApproximateModelPhaseFunction F σ Q δ →
          0 < T → 0 < N → 0 < H → 0 < K → (K:ℝ) ≤ Kmax →
          0 ≤ η → 0 < w → w ≤ 1/2 →
          let L := modelPhaseJetLower σ 2*T/N^3
          let U := (modelPhaseJetCoefficient σ 2+1)*T/N^3
          let lam := modelPhaseJetLower σ 3*T/N^4
          let B := (modelPhaseJetCoefficient σ 3+1)*T/N^4
          let Rmax := 36*U^2/lam
          let Dmax := Kmax/L+1
          12*U ≤ 1 → L ≤ 1 →
          2*η+10368*B*U^4/(lam^2*L) ≤ 1/2 →
          N < a-Rmax → b+Rmax+2*Dmax < 2*N →
          2*Kmax*N^2/(σ*T) ≤ κ₀ →
          (∀ i∈S, (H:ℤ) ≤ s+(H:ℤ)*block i-center i ∧
            s+(H:ℤ)*block i-center i ≤ 3*(H:ℤ)) →
          (∀ j : ℤ, (S.filter (fun i => block i=j)).card ≤ Bmul) →
          (∀ i∈S, (center i:ℝ)∈Icc a b) →
          (∀ i∈S, z i∈Ioo N (2*N)) →
          (∀ i∈S, |(center i:ℝ)-z i| ≤ 1/2) →
          V ⊆ S ×ˢ S →
          let f := fun t => T*F (t/N)
          (∀ p∈V, iteratedDeriv 2 f (z p.2)/2-
            iteratedDeriv 2 f (z p.1)/2=(K:ℝ)) →
          (∀ p∈V, ∃ e : ℤ, |iteratedDeriv 1 f (center p.2)-
            iteratedDeriv 1 f (center p.1)-(e:ℝ)| ≤ η) →
            (V.card:ℝ) ≤ (3*(Bmul:ℝ)^2*(3+144*U^2/(lam*(K:ℝ)*H)))*
              (C*((2*η+w)*Dmax+20736*B*U^4/(lam^2*L^2)+
                (T/N^2)^(k₀+ε)*Dmax^(l₀+ε)*w^(-(k₀+ε))+N^2/T)) := by
  classical
  obtain ⟨δ,κ₀,hδ,hκ₀,Q,hQ,C,hC,hcount⟩ :=
    original_model_rounded_shift_count hσ hpair hε hp
  refine ⟨δ,κ₀,hδ,hκ₀,Q,hQ,C,hC,?_⟩
  intro ι _ S V center block z H Bmul s K F T N a b Kmax η w
    hF hT hN hH hK hKmax hη hw hwhalf L U lam B Rmax Dmax hUsmall hLsmall
    hsmall hleft hright hκle hspan hmul hcenter hz hround hVS f hlevel hfirst
  have hlam : 0 < lam := by dsimp only [lam]; positivity [modelPhaseJetLower_pos hσ 3]
  have hL : 0 < L := by dsimp only [L]; positivity [modelPhaseJetLower_pos hσ 2]
  have hU : 0 < U := by dsimp only [U]; positivity [modelPhaseJetCoefficient_pos hσ 2]
  have hB : 0 ≤ B := by dsimp only [B]; positivity [modelPhaseJetCoefficient_pos hσ 3]
  have hKr : (1:ℝ) ≤ K := by exact_mod_cast (show (1:ℤ) ≤ K by omega)
  have hKp : (0:ℝ) < K := zero_lt_one.trans_le hKr
  let R := 36*U^2/(lam*(K:ℝ))
  let D := (K:ℝ)/L+1
  let W := max (2*η+4*B*D*R^2) w
  have hwidth := rounded_shift_free_width hL hU hlam hB hKr (hLsmall.trans hKr)
    hη hw hwhalf hsmall
  change 0 < R ∧ 0 < W ∧ W ≤ 1/2 ∧
    3*U=lam*((K:ℝ)/(6*U))*R/2 ∧ η+2*B*D*R^2 ≤ W/2 ∧
    W*D ≤ (2*η+w)*D+20736*B*U^4/(lam^2*L^2) ∧
    ∀ p : ℝ, 0 ≤ p → W^(-p) ≤ w^(-p) at hwidth
  have hRmax : R ≤ Rmax := by
    apply div_le_div_of_nonneg_left (by positivity) hlam
    nlinarith only [mul_le_mul_of_nonneg_left hKr hlam.le]
  have hDD : D ≤ Dmax := add_le_add
    (div_le_div_of_nonneg_right hKmax hL.le) le_rfl
  have hDp : 0 < D := by dsimp only [D]; positivity
  have hDmax : 0 < Dmax := hDp.trans_le hDD
  have hκ : 2*(K:ℝ)*N^2/(σ*T) ≤ κ₀ := le_trans
    (by gcongr) hκle
  have hb := hcount S V center block z H Bmul s K F T N a b R η W
    hF hT hN hwidth.1 hH hK hUsmall
    (by linarith only [hleft,hRmax])
    (by change b+R+2*D < 2*N; linarith only [hright,hRmax,hDD])
    hwidth.2.2.2.1.le hwidth.2.2.2.2.1 hκ hwidth.2.1 hwidth.2.2.1
    hspan hmul hcenter hz hround hVS hlevel hfirst
  have hp0 : 0 ≤ k₀+ε := by linarith [hpair.inTriangle.1]
  have hl0 : 0 ≤ l₀+ε := by linarith [hpair.inTriangle.2.2.1]
  have hfirstTerm : W*D ≤ (2*η+w)*Dmax+20736*B*U^4/(lam^2*L^2) :=
    hwidth.2.2.2.2.2.1.trans (add_le_add
      (mul_le_mul_of_nonneg_left hDD (by positivity)) le_rfl)
  have hosc : (T/N^2)^(k₀+ε)*D^(l₀+ε)*W^(-(k₀+ε)) ≤
      (T/N^2)^(k₀+ε)*Dmax^(l₀+ε)*w^(-(k₀+ε)) :=
    mul_le_mul
      (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hDp.le hDD hl0) (by positivity))
      (hwidth.2.2.2.2.2.2 _ hp0) (by positivity) (by positivity)
  exact hb.trans (mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_left (add_le_add (add_le_add hfirstTerm hosc) le_rfl)
      (zero_le_one.trans hC)) (by positivity))

/-- Both signs and the zero curvature shift for the actual model source.
The positive fibers use the analytic exponent-pair near-curve estimate. -/
theorem original_model_all_shifts_count
    {σ k₀ l₀ ε : ℝ} (hσ : 0 < σ)
    (hpair : ExponentPair k₀ l₀) (hε : 0 < ε) (hp : k₀+ε < 1) :
    ∃ δ κ₀ : ℝ, 0 < δ ∧ 0 < κ₀ ∧
      ∃ Q : ℕ, 3 ≤ Q ∧ ∃ C : ℝ, 1 ≤ C ∧
        ∀ {ι : Type*} [DecidableEq ι] (S : Finset ι) (R : Finset (ι × ι))
          (center block : ι → ℤ) (z : ι → ℝ) (H Bmul Kcut : ℕ) (s : ℤ)
          (F : ℝ → ℝ) (T N a b η w : ℝ),
          IsApproximateModelPhaseFunction F σ Q δ →
          0 < T → 0 < N → 0 < H → 0 ≤ η → 0 < w → w ≤ 1/2 →
          let L := modelPhaseJetLower σ 2*T/N^3
          let U := (modelPhaseJetCoefficient σ 2+1)*T/N^3
          let lam := modelPhaseJetLower σ 3*T/N^4
          let B := (modelPhaseJetCoefficient σ 3+1)*T/N^4
          let Rmax := 36*U^2/lam
          let Dmax := (Kcut:ℝ)/L+1
          12*U ≤ 1 → L ≤ 1 →
          2*η+10368*B*U^4/(lam^2*L) ≤ 1/2 →
          N < a-Rmax → b+Rmax+2*Dmax < 2*N →
          2*(Kcut:ℝ)*N^2/(σ*T) ≤ κ₀ →
          (∀ i∈S, (H:ℤ) ≤ s+(H:ℤ)*block i-center i ∧
            s+(H:ℤ)*block i-center i ≤ 3*(H:ℤ)) →
          (∀ j : ℤ, (S.filter (fun i => block i=j)).card ≤ Bmul) →
          (∀ i∈S, (center i:ℝ)∈Icc a b) →
          (∀ i∈S, z i∈Ioo N (2*N)) →
          (∀ i∈S, |(center i:ℝ)-z i| ≤ 1/2) →
          R ⊆ S ×ˢ S → (∀ p∈R, p.swap∈R) →
          let f := fun t => T*F (t/N)
          (∀ p∈R, ∃ k : ℤ, iteratedDeriv 2 f (z p.2)/2-
            iteratedDeriv 2 f (z p.1)/2=(k:ℝ) ∧ |(k:ℝ)| ≤ Kcut) →
          (∀ p∈R, ∃ e : ℤ, |iteratedDeriv 1 f (center p.2)-
            iteratedDeriv 1 f (center p.1)-(e:ℝ)| ≤ η) →
          let Count := C*((2*η+w)*Dmax+20736*B*U^4/(lam^2*L^2)+
                (T/N^2)^(k₀+ε)*Dmax^(l₀+ε)*w^(-(k₀+ε))+N^2/T)
          let Dweight := 144*U^2/(lam*H)
          (R.card:ℝ) ≤ 4*(Bmul:ℝ)*S.card+
            6*(Bmul:ℝ)^2*Count*(3*(Kcut:ℝ)+Dweight*(harmonic Kcut:ℝ)) := by
  classical
  obtain ⟨δ₀,κ₀,hδ₀,hκ₀,Q,hQ,C,hC,hcount⟩ :=
    original_model_uniform_positive_shift_count hσ hpair hε hp
  obtain ⟨δd,hδd,hdata⟩ := model_displacement_derivative_data hσ
  refine ⟨min δ₀ δd,κ₀,lt_min hδ₀ hδd,hκ₀,Q,hQ,C,hC,?_⟩
  intro ι _ S R center block z H Bmul Kcut s F T N a b η w
    hF hT hN hH hη hw hwhalf L U lam B Rmax Dmax hUsmall hLsmall
    hsmall hleft hright hκle hspan hmul hcenter hz hround hRS hsym f hshift hnear Count D
  have hF₀ := approximateModelPhase_mono hF le_rfl (min_le_left _ _)
  have hFd := approximateModelPhase_mono hF hQ (min_le_right _ _)
  obtain ⟨hreg,hthree,_,_⟩ := hdata F T N hT hN hFd
  have hlam : 0 < lam := by dsimp only [lam]; positivity [modelPhaseJetLower_pos hσ 3]
  have hL : 0 < L := by dsimp only [L]; positivity [modelPhaseJetLower_pos hσ 2]
  have hU : 0 < U := by dsimp only [U]; positivity [modelPhaseJetCoefficient_pos hσ 2]
  have hB : 0 ≤ B := by dsimp only [B]; positivity [modelPhaseJetCoefficient_pos hσ 3]
  have hDmax : 0 < Dmax := by dsimp only [Dmax]; positivity
  have hCount : 0 ≤ Count := by dsimp only [Count]; positivity
  have hD : 0 ≤ D := by dsimp only [D]; positivity
  let h := fun x => iteratedDeriv 2 f x/2
  let Z := R.filter (fun p => h (z p.1)=h (z p.2))
  let Rp := R.filter (fun p => h (z p.1)<h (z p.2))
  have hRmem p (hp : p∈R) : p.1∈S ∧ p.2∈S := Finset.mem_product.mp (hRS hp)
  have hpmem p (hp : p∈Rp) : p∈R ∧ h (z p.1)<h (z p.2) := Finset.mem_filter.mp hp
  have hRsplit : R ⊆ Z ∪ (Rp ∪ Rp.image Prod.swap) := by
    intro p hp
    rcases lt_trichotomy (h (z p.1)) (h (z p.2)) with hh | hh | hh
    · exact Finset.mem_union_right _ (Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hp,hh⟩))
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hp,hh⟩)
    · apply Finset.mem_union_right
      apply Finset.mem_union_right
      exact Finset.mem_image.mpr ⟨p.swap,Finset.mem_filter.mpr ⟨hsym p hp,hh⟩,Prod.swap_swap p⟩
  have hsplit : R.card ≤ Z.card+2*Rp.card := by
    have hh := (Finset.card_le_card hRsplit).trans (Finset.card_union_le _ _)
    have hh' := Finset.card_union_le Rp (Rp.image Prod.swap)
    have he : (Rp.image Prod.swap).card=Rp.card := Finset.card_image_of_injective _ Prod.swap_injective
    omega
  have hmulLevel := bourgain_curvature_level_block_multiplicity S f z center block H Bmul s
    hH hL (fun t ht => (hreg t ht).of_le (by norm_num)) (fun t ht => (hthree t ht).1)
    hz (fun i hi => by simpa only [abs_sub_comm] using hround i hi) hspan hmul
  have hZfiber i : (Z.filter (fun p => p.1=i)).card ≤ 4*Bmul := by
    have hsub : Z.filter (fun p => p.1=i) ⊆ {i} ×ˢ (S.filter (fun j => h (z j)=h (z i))) := by
      intro p hp
      obtain ⟨hp,he⟩ := Finset.mem_filter.mp hp
      obtain ⟨hp,hh⟩ := Finset.mem_filter.mp hp
      exact Finset.mem_product.mpr ⟨Finset.mem_singleton.mpr he,
        Finset.mem_filter.mpr ⟨(hRmem p hp).2,by rw [←he]; exact hh.symm⟩⟩
    calc
      _ ≤ _ := Finset.card_le_card hsub
      _ = (S.filter (fun j => h (z j)=h (z i))).card := by simp only [Finset.card_product,Finset.card_singleton,one_mul]
      _ ≤ _ := hmulLevel _
  have hZ : (Z.card:ℝ) ≤ 4*(Bmul:ℝ)*S.card := by
    have he : (Z.card:ℝ)=∑ i∈S,((Z.filter (fun p => p.1=i)).card:ℝ) := by
      exact_mod_cast Finset.card_eq_sum_card_fiberwise
        (fun (p : ι × ι) hp => (hRmem p (Finset.mem_filter.mp hp).1).1)
    rw [he]
    calc
      _ ≤ ∑ _i∈S,4*(Bmul:ℝ) := Finset.sum_le_sum (fun i _ => by exact_mod_cast hZfiber i)
      _ = _ := by simp only [Finset.sum_const,nsmul_eq_mul]; ring
  have hex (p : ι × ι) : ∃ d : ℕ, p∈Rp →
      0 < d ∧ h (z p.2)-h (z p.1)=(d:ℝ) ∧ d ≤ Kcut := by
    by_cases hp : p∈Rp
    · obtain ⟨d,he,hd⟩ := hshift p (hpmem p hp).1
      change h (z p.2)-h (z p.1)=(d:ℝ) at he
      have hdr : 0 < (d:ℝ) := by linarith only [he,(hpmem p hp).2]
      have hdi : 0 < d := by exact_mod_cast hdr
      have hdcast : (d.toNat:ℝ)=(d:ℝ) := by exact_mod_cast Int.toNat_of_nonneg hdi.le
      refine ⟨d.toNat,fun _ => ⟨by omega,by rw [hdcast]; exact he,?_⟩⟩
      have hh : (d.toNat:ℝ) ≤ Kcut := by rw [hdcast]; exact (le_abs_self _).trans hd
      exact_mod_cast hh
    · exact ⟨0,fun hh => False.elim (hp hh)⟩
  choose shift hshiftNat using hex
  let J := Finset.Icc 1 Kcut
  have hindex p (hp : p∈Rp) : shift p∈J :=
    Finset.mem_Icc.mpr ⟨(hshiftNat p hp).1,(hshiftNat p hp).2.2⟩
  have hfiber n (hn : n∈J) :
      ((Rp.filter (fun p => shift p=n)).card:ℝ) ≤
        3*(Bmul:ℝ)^2*Count*(3+D/n) := by
    let E := Rp.filter (fun p => shift p=n)
    have hnmem := Finset.mem_Icc.mp hn
    have hEmem p (hp : p∈E) : p∈Rp ∧ shift p=n := Finset.mem_filter.mp hp
    have hb := hcount S E center block z H Bmul s (n:ℤ) F T N a b Kcut η w
      hF₀ hT hN hH (by exact_mod_cast hnmem.1) (by exact_mod_cast hnmem.2)
      hη hw hwhalf hUsmall hLsmall hsmall hleft hright hκle hspan hmul hcenter hz hround
      (fun p hp => hRS (hpmem p (hEmem p hp).1).1)
      (by
        intro p hp
        have he := (hshiftNat p (hEmem p hp).1).2.1
        rw [(hEmem p hp).2] at he
        simpa only [Int.cast_natCast] using he)
      (fun p hp => hnear p (hpmem p (hEmem p hp).1).1)
    change (E.card:ℝ) ≤
      (3*(Bmul:ℝ)^2*(3+144*U^2/(lam*((n:ℤ):ℝ)*H)))*Count at hb
    have hDeq : 144*U^2/(lam*((n:ℤ):ℝ)*H)=D/n := by
      simp only [Int.cast_natCast]
      dsimp only [D]
      ring
    rw [hDeq] at hb
    exact hb.trans_eq (by ring)
  have hsum : (∑ n∈J,(3+D/(n:ℝ))) ≤ 3*(Kcut:ℝ)+D*(harmonic Kcut:ℝ) := by
    have hh := sum_positive_displacement_weight_le_harmonic (η:=0) (N:=Kcut) le_rfl
      (by positivity : 0 ≤ D/3)
    simp only [Real.rpow_zero,one_mul] at hh
    calc
      _ = 3*∑ n∈J,(1+(D/3)/(n:ℝ)) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro n _
        ring
      _ ≤ 3*((Kcut:ℝ)+(D/3)*(harmonic Kcut:ℝ)) :=
        mul_le_mul_of_nonneg_left hh (by norm_num)
      _ = _ := by ring
  have hRp : (Rp.card:ℝ) ≤ 3*(Bmul:ℝ)^2*Count*(3*(Kcut:ℝ)+D*(harmonic Kcut:ℝ)) := by
    have hc : (Rp.card:ℝ)=∑ n∈J,((Rp.filter (fun p => shift p=n)).card:ℝ) := by
      exact_mod_cast Finset.card_eq_sum_card_fiberwise hindex
    calc
      _ = _ := hc
      _ ≤ ∑ n∈J,3*(Bmul:ℝ)^2*Count*(3+D/(n:ℝ)) := Finset.sum_le_sum hfiber
      _ = (3*(Bmul:ℝ)^2*Count)*∑ n∈J,(3+D/(n:ℝ)) := (Finset.mul_sum _ _ _).symm
      _ ≤ _ := mul_le_mul_of_nonneg_left hsum (by positivity)
  have hsplitR : (R.card:ℝ) ≤ (Z.card:ℝ)+2*(Rp.card:ℝ) := by exact_mod_cast hsplit
  calc
    _ ≤ _ := hsplitR
    _ ≤ 4*(Bmul:ℝ)*S.card+2*(3*(Bmul:ℝ)^2*Count*(3*(Kcut:ℝ)+D*(harmonic Kcut:ℝ))) :=
      add_le_add hZ (mul_le_mul_of_nonneg_left hRp (by norm_num))
    _ = _ := by ring

/-- The literal four-coordinate second-spacing window, counted by an analytic
exponent pair. All rational labels, both parities, both shift signs, the
zero shift and the block multiplicities are preserved. -/
theorem original_model_four_coordinate_count
    {σ k₀ l₀ ε : ℝ} (hσ : 0 < σ)
    (hpair : ExponentPair k₀ l₀) (hε : 0 < ε) (hp : k₀+ε < 1) :
    ∃ δ κ₀ : ℝ, 0 < δ ∧ 0 < κ₀ ∧
      ∃ Q : ℕ, 3 ≤ Q ∧ ∃ C : ℝ, 1 ≤ C ∧
        ∀ {ι : Type*} [DecidableEq ι] (S : Finset ι)
          (center block label inverse : ι → ℤ) (z : ι → ℝ) (q : ι → ℕ)
          (parity : ι → Fin 2) (H Bmul M Qden : ℕ) [NeZero M] (s : ℤ)
          (F : ℝ → ℝ) (T N a₀ b₀ w : ℝ),
          IsApproximateModelPhaseFunction F σ Q δ →
          0 < T → 0 < N → 0 < H → 0 < Qden → 0 < w → w ≤ 1/2 →
          (Qden:ℝ)^2 < 6*(M:ℝ)^2 →
          let L := modelPhaseJetLower σ 2*T/N^3
          let U := (modelPhaseJetCoefficient σ 2+1)*T/N^3
          let lam := modelPhaseJetLower σ 3*T/N^4
          let B := (modelPhaseJetCoefficient σ 3+1)*T/N^4
          let f := fun t => T*F (t/N)
    let mu := fun i => iteratedDeriv 3 f (center i)/6
    let ell := fun i => iteratedDeriv 1 f (center i)
    let b := fun i => (⌊(q i:ℝ)*ell i⌋:ℤ)+(parity i:ℕ)
    let tau := fun i => ((b i:ℝ)-(q i:ℝ)*ell i)/2
    let coeff := fun i => -2*mu i*(Real.sqrt (2/(3*mu i*(q i:ℝ))))^3
    let Y := fun i => (![Int.fract (-(inverse i:ℝ)*b i/q i),Int.fract (-(inverse i:ℝ)/q i),
      coeff i/Real.sqrt M,(3*coeff i*tau i/2)/Real.sqrt M] : Fin 4 → ℝ)
    let window : Fin 4 → ℝ :=
      ![1/(12*(M:ℝ)),1/(12*(M:ℝ)^2),(1/(M:ℝ)^2)/12,(1/(M:ℝ))/12]
    let R := (S ×ˢ S).filter (fun ij => ∀ j, |Y ij.1 j-Y ij.2 j| ≤ 2*window j)
    let D₀ : ℝ := (Real.sqrt M/(9*(M:ℝ))+Real.sqrt M/(12*(M:ℝ)^2))*
      Real.sqrt (U*(Qden:ℝ)^3)
    let η : ℝ := 4*D₀/(Qden:ℝ)
    let rho := (12*U*Real.sqrt (U*(Qden:ℝ)^3)/lam)*(Real.sqrt M/(6*(M:ℝ)^2))
    let Kcut := ⌈3*U*(rho+1)⌉₊
    let Rmax := 36*U^2/lam
    let Dmax := (Kcut:ℝ)/L+1
    12*U ≤ 1 → L ≤ 1 →
    2*η+10368*B*U^4/(lam^2*L) ≤ 1/2 →
    N < a₀-Rmax → b₀+Rmax+2*Dmax < 2*N →
    2*(Kcut:ℝ)*N^2/(σ*T) ≤ κ₀ →
    (∀ i∈S, (H:ℤ) ≤ s+(H:ℤ)*block i-center i ∧
      s+(H:ℤ)*block i-center i ≤ 3*(H:ℤ)) →
    (∀ j : ℤ, (S.filter (fun i => block i=j)).card ≤ Bmul) →
    (∀ i∈S, (center i:ℝ)∈Icc a₀ b₀) →
    (∀ i∈S, z i∈Ioo N (2*N)) →
    (∀ i∈S, |(center i:ℝ)-z i| ≤ 1/2) →
    (∀ i∈S, 0 < q i ∧ q i ≤ Qden ∧ Qden ≤ 2*q i) →
    (∀ i∈S, (q i:ℤ) ∣ label i*inverse i-1) →
    (∀ i∈S, iteratedDeriv 2 f (z i)/2=(label i:ℝ)/q i) →
    let Count := C*((2*η+w)*Dmax+20736*B*U^4/(lam^2*L^2)+
      (T/N^2)^(k₀+ε)*Dmax^(l₀+ε)*w^(-(k₀+ε))+N^2/T)
    let Dweight := 144*U^2/(lam*H)
    (R.card:ℝ) ≤ 4*(Bmul:ℝ)*S.card+
      6*(Bmul:ℝ)^2*Count*(3*(Kcut:ℝ)+Dweight*(harmonic Kcut:ℝ)) := by
  classical
  obtain ⟨δ₀,κ₀,hδ₀,hκ₀,Q,hQ,C,hC,hcount⟩ :=
    original_model_all_shifts_count hσ hpair hε hp
  obtain ⟨δd,hδd,hdata⟩ := model_displacement_derivative_data hσ
  refine ⟨min δ₀ δd,κ₀,lt_min hδ₀ hδd,hκ₀,Q,hQ,C,hC,?_⟩
  intro ι _ S center block label inverse z q parity H Bmul M Qden _ s F T N a₀ b₀ w
    hF hT hN hH hQden hw hwhalf hthin L U lam B f
    mu ell b tau coeff Y window R D₀ η rho Kcut Rmax Dmax hUsmall hLsmall
    hsmall hleft hright hκle hspan hmul hcenter hz hround hq hinverse hlevel Count Dweight
  have hF₀ := approximateModelPhase_mono hF le_rfl (min_le_left _ _)
  have hFd := approximateModelPhase_mono hF hQ (min_le_right _ _)
  obtain ⟨hreg,hthree,hfour,_⟩ := hdata F T N hT hN hFd
  have hlam : 0 < lam := by dsimp only [lam]; positivity [modelPhaseJetLower_pos hσ 3]
  have hL : 0 < L := by dsimp only [L]; positivity [modelPhaseJetLower_pos hσ 2]
  have hU : 0 < U := by dsimp only [U]; positivity [modelPhaseJetCoefficient_pos hσ 2]
  have hRmax : 0 < Rmax := by dsimp only [Rmax]; positivity
  have hDmax : 0 < Dmax := by dsimp only [Dmax]; positivity
  have hcent i (hi : i∈S) : (center i:ℝ)∈Ioo N (2*N) := by
    have hh := hcenter i hi
    constructor <;> linarith [hh.1,hh.2]
  have hthreeUpper t (ht : t∈Ioo N (2*N)) :
      L ≤ iteratedDeriv 3 f t ∧ iteratedDeriv 3 f t ≤ 6*U := by
    have hh := hthree t ht
    exact ⟨hh.1,by linarith [hh.2]⟩
  have hQr : (0:ℝ) < Qden := by exact_mod_cast hQden
  have hD₀ : 0 ≤ D₀ := by dsimp only [D₀]; positivity
  have hη : 0 ≤ η := by dsimp only [η]; positivity
  have hRmem p (hp : p∈R) : p.1∈S ∧ p.2∈S :=
    Finset.mem_product.mp (Finset.mem_filter.mp hp).1
  have hRnear p (hp : p∈R) : ∀ j, |Y p.1 j-Y p.2 j| ≤ 2*window j :=
    (Finset.mem_filter.mp hp).2
  have hRsym p (hp : p∈R) : p.swap∈R := by
    refine Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨(hRmem p hp).2,(hRmem p hp).1⟩,?_⟩
    intro j
    change |Y p.2 j-Y p.1 j| ≤ 2*window j
    rw [abs_sub_comm]
    exact hRnear p hp j
  have hshift p (hp : p∈R) : ∃ k : ℤ,
      iteratedDeriv 2 f (z p.2)/2-iteratedDeriv 2 f (z p.1)/2=(k:ℝ) ∧ |(k:ℝ)| ≤ Kcut := by
    have hi := (hRmem p hp).1
    have hj := (hRmem p hp).2
    have hh := source_four_coordinate_integer_shift_bound f M (q p.1) (q p.2) Qden
      (label p.1) (label p.2) (inverse p.1) (inverse p.2) (center p.1) (center p.2)
      (hq _ hi).1 (hq _ hj).1 (hq _ hi).2.1 (hq _ hj).2.1 hthin hlam hU
      (fun t ht => (hreg t ht).of_le (by norm_num))
      (fun t ht => ⟨hL.trans_le (hthreeUpper t ht).1,(hthreeUpper t ht).2⟩)
      (fun t ht => by
        have hb := (hfour t ht).2
        rw [abs_of_neg (by linarith only [hb,hlam])]
        linarith only [hb])
      (hz _ hi) (hz _ hj) (hcent _ hi) (hcent _ hj)
      (by simpa only [abs_sub_comm] using hround _ hi)
      (by simpa only [abs_sub_comm] using hround _ hj)
      (hinverse _ hi) (hinverse _ hj) (hlevel _ hi) (hlevel _ hj)
      (by
        have hb := hRnear p hp 1
        change _ ≤ 2*(1/(12*(M:ℝ)^2)) at hb
        convert hb using 1
        ring)
      (by
        have hb := hRnear p hp 2
        change _ ≤ 2*((1/(M:ℝ)^2)/12) at hb
        convert hb using 1
        ring)
    obtain ⟨_,k,hk,hb⟩ := hh
    exact ⟨k,hk,hb.trans (Nat.le_ceil _)⟩
  have hnear p (hp : p∈R) : ∃ e : ℤ, |ell p.2-ell p.1-(e:ℝ)| ≤ η := by
    have hi := (hRmem p hp).1
    have hj := (hRmem p hp).2
    have hmui : 0 < mu p.1 := by
      dsimp only [mu]
      positivity [hL.trans_le (hthreeUpper _ (hcent _ hi)).1]
    have hmuj : 0 < mu p.2 := by
      dsimp only [mu]
      positivity [hL.trans_le (hthreeUpper _ (hcent _ hj)).1]
    have hmuiU : mu p.1 ≤ U := by
      dsimp only [mu]
      linarith only [(hthreeUpper _ (hcent _ hi)).2]
    obtain ⟨_,k,e,_hk,he⟩ := actual_source_triangular_derivative_resonance M (q p.1) (q p.2) Qden
      (label p.1) (label p.2) (inverse p.1) (inverse p.2)
      (hq _ hi).1 (hq _ hj).1 (hq _ hi).2.1 (hq _ hj).2.1 hthin
      (hinverse _ hi) (hinverse _ hj) hmui hmuj hmuiU (parity p.1) (parity p.2)
      (hRnear p hp)
    have hqr : (0:ℝ) < q p.1 := by exact_mod_cast (hq _ hi).1
    have hQq : (Qden:ℝ) ≤ 2*(q p.1:ℝ) := by exact_mod_cast (hq _ hi).2.2
    refine ⟨e,he.trans ?_⟩
    change 2*D₀/(q p.1:ℝ) ≤ 4*D₀/Qden
    apply (div_le_div_iff₀ hqr hQr).mpr
    nlinarith only [mul_le_mul_of_nonneg_left hQq hD₀]
  exact hcount S R center block z H Bmul Kcut s F T N a₀ b₀ η w
    hF₀ hT hN hH hη hw hwhalf hUsmall hLsmall hsmall hleft hright hκle
    hspan hmul hcenter hz hround (fun _ hp => (Finset.mem_filter.mp hp).1)
    hRsym hshift hnear

/-- The actual frozen C4 source sum with the refined exponent-pair spacing
count. The original model supplies all derivative data, and the real source
labels/parities are passed to the literal four-coordinate count. -/
theorem exists_model_refined_frozen_source
    {σ k₀ l₀ ε : ℝ} (hσ : 0 < σ)
    (hpair : ExponentPair k₀ l₀) (hε : 0 < ε) (hp : k₀+ε < 1) :
    ∃ δ κ₀ : ℝ, 0 < δ ∧ 0 < κ₀ ∧
      ∃ Qphase : ℕ, 3 ≤ Qphase ∧ ∃ C > (0:ℝ), ∃ Cp : ℝ, 1 ≤ Cp ∧
      ∀ (ι : Type*) [DecidableEq ι] (S : Finset ι)
      (G : ℝ → ℝ) (T P : ℝ) (r : ι → ℚ) (z : ι → ℝ) (m k : ι → ℤ)
      (H : ι → ℕ) (N Q Bmul : ℕ) (s : ℤ) (A B w : ℝ),
      IsApproximateModelPhaseFunction G σ Qphase δ →
      0 < T → 0 < P → 0 < N → 0 < Q → 0 < w → w ≤ 1/2 →
      let f := fun t => T*G (t/P)
      let L := modelPhaseJetLower σ 2*T/P^3
      let U := (modelPhaseJetCoefficient σ 2+1)*T/P^3
      let lam := modelPhaseJetLower σ 3*T/P^4
      let F := (modelPhaseJetCoefficient σ 3+1)*T/P^4
      12*U ≤ 1 → L ≤ 1 →
      F*(6*(N:ℝ)+1)^4 ≤ 1 → (3*U/2)*(6*(N:ℝ)+1)^2 ≤ 1 →
      (∀ i∈S, z i∈Ioo A B) →
      (∀ i∈S, Icc ((m i:ℝ)-(6*(N:ℝ)+1)) ((m i:ℝ)+(6*(N:ℝ)+1)) ⊆ Icc A B) →
      (∀ i∈S, |z i-m i| ≤ 1/2) →
      (∀ i∈S, (N:ℤ) ≤ s+(N:ℤ)*k i-m i ∧ s+(N:ℤ)*k i-m i ≤ 3*(N:ℤ)) →
      (∀ n : ℤ, (S.filter (fun i => k i=n)).card ≤ Bmul) →
      (∀ i∈S, H i ≤ N) →
      (∀ i∈S, (r i).den ≤ Q ∧ Q ≤ 2*(r i).den ∧ (r i).den ≤ N) →
      (∀ i∈S, iteratedDeriv 2 f (z i)/2=(r i:ℝ)) →
      12 ≤ L*(Q:ℝ)*(N:ℝ)^2 → 384 ≤ L^2*(Q:ℝ)^3*(N:ℝ)^3 →
      let Z := (S.card:ℝ)
      let M : ℕ := ⌈63*U*(Q:ℝ)*(N:ℝ)^2⌉₊+1
      let V := 756*U/L
      let Wloss := 1+32/(L*(Q:ℝ)^2*N)
      let d := L*(Q:ℝ)*N/12
      let D₀ := (Real.sqrt M/(9*(M:ℝ))+Real.sqrt M/(12*(M:ℝ)^2))*Real.sqrt (U*(Q:ℝ)^3)
      let η : ℝ := 4*D₀/(Q:ℝ)
      let rho := (12*U*Real.sqrt (U*(Q:ℝ)^3)/lam)*(Real.sqrt M/(6*(M:ℝ)^2))
      let K := ⌈3*U*(rho+1)⌉₊
      let Rmax := 36*U^2/lam
      let Dmax := (K:ℝ)/L+1
      let Dweight := 144*U^2/(lam*N)
      let Count := Cp*((2*η+w)*Dmax+20736*F*U^4/(lam^2*L^2)+
        (T/P^2)^(k₀+ε)*Dmax^(l₀+ε)*w^(-(k₀+ε))+P^2/T)
      let Pair := 4*(Bmul:ℝ)*Z+6*(Bmul:ℝ)^2*Count*(3*(K:ℝ)+Dweight*(harmonic K:ℝ))
      let Loss := (5*Wloss)^11*Wloss^2*(6*(3+8*Real.pi*V)*(1+Real.log M))^12*
        (2/d)^6*(M:ℝ)^((12:ℝ)+ε)
      let Err := Real.sqrt (3*(N:ℝ))*Real.log (6*(N:ℝ))+6/(L*(N:ℝ)^2)+
        Real.sqrt (12/(L*(N:ℝ)*Q))
      (Q:ℝ)^2 < 6*(M:ℝ)^2 →
      2*η+10368*F*U^4/(lam^2*L) ≤ 1/2 →
      P < A-Rmax → B+Rmax+2*Dmax < 2*P →
      2*(K:ℝ)*P^2/(σ*T) ≤ κ₀ →
      (∑ i∈S, ‖∑ n∈Finset.Ioc (s+(N:ℤ)*k i) (s+(N:ℤ)*k i+H i),(𝐞 (f n):ℂ)‖)^12 ≤
        C*(Loss*(2*Z)^10*Pair+(Z*Err)^12) := by
  classical
  obtain ⟨δ₀,κ₀,hδ₀,hκ₀,Qphase,hQphase,Cp,hCp,hcount⟩ :=
    original_model_four_coordinate_count hσ hpair hε hp
  obtain ⟨δd,hδd,hdata⟩ := model_displacement_derivative_data hσ
  obtain ⟨C,hC,hsource⟩ := exists_bourgain_C4_frozen_source_second_spacing_reduction hε
  refine ⟨min δ₀ δd,κ₀,lt_min hδ₀ hδd,hκ₀,Qphase,hQphase,4*C,by positivity,Cp,hCp,?_⟩
  intro ι instι S G T P r z m k H N Q Bmul s A B w
    hG hT hP hN hQ hw hwhalf f L U lam F hUsmall hLsmall hfourSmall hquadSmall
    hz hbuffer hround hspan hmul hH hq hlevel hdual hfrozen
    Z M V Wloss d D₀ η rho K Rmax Dmax Dweight Count Pair Loss Err hthin
    hliftSmall hleft hright hκle
  have hG₀ := approximateModelPhase_mono hG le_rfl (min_le_left _ _)
  have hGd := approximateModelPhase_mono hG hQphase (min_le_right _ _)
  obtain ⟨hreg,hthreeModel,hfourModel,_⟩ := hdata G T P hT hP hGd
  have hlam : 0 < lam := by dsimp only [lam]; positivity [modelPhaseJetLower_pos hσ 3]
  have hL : 0 < L := by dsimp only [L]; positivity [modelPhaseJetLower_pos hσ 2]
  have hU : 0 < U := by dsimp only [U]; positivity [modelPhaseJetCoefficient_pos hσ 2]
  have hF : 0 < F := by dsimp only [F]; positivity [modelPhaseJetCoefficient_pos hσ 3]
  have hRmax : 0 < Rmax := by dsimp only [Rmax]; positivity
  have hDmax : 0 < Dmax := by dsimp only [Dmax]; positivity
  have hdomain : Icc A B ⊆ Ioo P (2*P) := by
    intro x hx
    constructor <;> linarith [hx.1,hx.2]
  have hf x (hx : x∈Icc A B) : ContDiffAt ℝ 5 f x := hreg x (hdomain hx)
  have hthree x (hx : x∈Icc A B) :
      L ≤ iteratedDeriv 3 f x ∧ iteratedDeriv 3 f x ≤ 6*U := by
    have hh := hthreeModel x (hdomain hx)
    exact ⟨hh.1,by linarith [hh.2]⟩
  have hfour x (hx : x∈Icc A B) :
      -F ≤ iteratedDeriv 4 f x ∧ iteratedDeriv 4 f x ≤ -lam := hfourModel x (hdomain hx)
  have hf₄ x (hx : x∈Icc A B) : ContDiffAt ℝ 4 f x := (hf x hx).of_le (by norm_num)
  have hfourAbs x (hx : x∈Icc A B) : lam ≤ |iteratedDeriv 4 f x| ∧ |iteratedDeriv 4 f x| ≤ F := by
    have hh := hfour x hx
    rw [abs_of_neg (by linarith only [hh.2,hlam])]
    constructor <;> linarith only [hh.1,hh.2]
  let H₀ := L*(Q:ℝ)*(N:ℝ)^2/12
  have hNr : (0:ℝ) < N := Nat.cast_pos.mpr hN
  have hQr : (0:ℝ) < Q := Nat.cast_pos.mpr hQ
  have hcard : (S.card:ℝ) ≤ Z := le_rfl
  let W := fun i => (s+(N:ℤ)*k i-m i).toNat
  let mu := fun i => iteratedDeriv 3 f (m i)/6
  have hW i (hi : i∈S) : N ≤ W i ∧ W i ≤ 3*N ∧ m i+(W i:ℤ)=s+(N:ℤ)*k i := by
    have hh := hspan i hi
    dsimp only [W]
    constructor
    · omega
    · constructor <;> omega
  have hWp i (hi : i∈S) : 1 ≤ W i := (Nat.succ_le_iff.mpr hN).trans (hW i hi).1
  have hWr i (hi : i∈S) : (N:ℝ) ≤ W i ∧ (W i:ℝ) ≤ 3*(N:ℝ) := by
    constructor <;> exact_mod_cast (by first | exact (hW i hi).1 | exact (hW i hi).2.1)
  have hm i (hi : i∈S) : (m i:ℝ)∈Ioo A B := by
    have hrad : 0 < 6*(N:ℝ)+1 := by positivity
    have hlo := (hbuffer i hi (left_mem_Icc.mpr (by linarith only [hrad]))).1
    have hhi := (hbuffer i hi (right_mem_Icc.mpr (by linarith only [hrad]))).2
    constructor <;> linarith only [hlo,hhi,hrad]
  have hmu i (hi : i∈S) : 0 < mu i ∧ L/6 ≤ mu i ∧ mu i ≤ U := by
    have hh := hthree (m i) ⟨(hm i hi).1.le,(hm i hi).2.le⟩
    dsimp only [mu]
    constructor
    · linarith only [hh.1,hL]
    · constructor <;> linarith only [hh.1,hh.2]
  have hbuf i (hi : i∈S) :
      Icc ((m i:ℝ)-(2*(W i:ℝ)+1)) ((m i:ℝ)+(2*(W i:ℝ)+1)) ⊆ Icc A B := by
    intro x hx
    apply hbuffer i hi
    have hw := (hWr i hi).2
    constructor <;> linarith only [hx.1,hx.2,hw]
  have hsmall i (hi : i∈S) :
      F*(2*(W i:ℝ)+1)^4 ≤ 1 ∧ (3*U/2)*(2*(W i:ℝ)+1)^2 ≤ 1 := by
    have hw : 2*(W i:ℝ)+1 ≤ 6*(N:ℝ)+1 := by linarith only [(hWr i hi).2]
    constructor
    · exact (mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (by positivity) hw 4) hF.le).trans hfourSmall
    · exact (mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (by positivity) hw 2) (by positivity)).trans hquadSmall
  have hcurv i (hi : i∈S) :
      |iteratedDeriv 2 f (m i)/2-((r i).num:ℝ)/(r i).den| ≤ 3*U/2 := by
    have hh := bourgain_curvature_level_difference f hf₄
      (fun x hx => ⟨hL.le.trans (hthree x hx).1,(hthree x hx).2⟩)
      ⟨(hm i hi).1.le,(hm i hi).2.le⟩ ⟨(hz i hi).1.le,(hz i hi).2.le⟩
    rw [hlevel i hi,Rat.cast_def,abs_sub_comm (m i:ℝ) (z i)] at hh
    have hr := mul_le_mul_of_nonneg_left (hround i hi) (show 0 ≤ 3*U by positivity)
    exact hh.trans (by linarith only [hr])
  have hscale i (hi : i∈S) : mu i*(W i:ℝ)^2 ≤ 1 := by
    have ha : (W i:ℝ)^2 ≤ (2*(W i:ℝ)+1)^2 := by
      nlinarith only [show (0:ℝ) ≤ W i from Nat.cast_nonneg _]
    calc
      _ ≤ U*(2*(W i:ℝ)+1)^2 :=
        mul_le_mul (hmu i hi).2.2 ha (sq_nonneg _) hU.le
      _ ≤ (3*U/2)*(2*(W i:ℝ)+1)^2 := by gcongr; linarith only [hU]
      _ ≤ _ := (hsmall i hi).2

  letI : NeZero M := ⟨by dsimp only [M]; omega⟩
  have hM : 63*U*(Q:ℝ)*(N:ℝ)^2≤(M:ℝ) := by
    have hh := Nat.le_ceil (63*U*(Q:ℝ)*(N:ℝ)^2)
    dsimp only [M]
    push_cast
    linarith only [hh]
  have hV : 0≤V := by dsimp only [V]; positivity
  have hWloss : 1≤Wloss := by
    have hp : 0≤32/(L*(Q:ℝ)^2*N) := by positivity
    dsimp only [Wloss]
    linarith only [hp]
  have hd : 0<d := by dsimp only [d]; positivity
  have hphysical i (hi : i∈S) :
      1≤H₀ ∧ H₀≤ mu i*((r i).den:ℝ)*(W i:ℝ)^2 ∧
        7*(mu i*((r i).den:ℝ)*(W i:ℝ)^2)≤63*U*(Q:ℝ)*(N:ℝ)^2 ∧
        7*(mu i*((r i).den:ℝ)*(W i:ℝ)^2)≤V*H₀ ∧
        |-2*mu i*(Real.sqrt (2/(3*mu i*((r i).den:ℝ))))^3|≤H₀*Real.sqrt H₀ ∧
        |-2*mu i*(Real.sqrt (2/(3*mu i*((r i).den:ℝ))))^3|/Real.sqrt H₀≤Wloss := by
    have hQq : (Q:ℝ)/2≤(r i).den := by
      have hh : (Q:ℝ)≤2*((r i).den:ℝ) := by exact_mod_cast (hq i hi).2.1
      linarith only [hh]
    exact bourgain_frozen_physical_dual_scales hL hU hNr hQr (hmu i hi).2
      ⟨hQq,Nat.cast_le.mpr (hq i hi).1⟩ (hWr i hi) hdual hfrozen
  have hdscale i (hi : i∈S) : d≤ mu i*((r i).den:ℝ)*W i := by
    have hqr : (Q:ℝ)≤2*((r i).den:ℝ) := by exact_mod_cast (hq i hi).2.1
    calc
      d = (L/6)*((Q:ℝ)/2)*N := by dsimp only [d]; ring
      _ ≤ mu i*((r i).den:ℝ)*W i :=
        mul_le_mul (mul_le_mul (hmu i hi).2.1 (by linarith only [hqr])
          (by positivity) (hmu i hi).1.le)
          (hWr i hi).1 hNr.le (mul_nonneg (hmu i hi).1.le (Nat.cast_nonneg _))
  by_cases hS : S.Nonempty
  · obtain ⟨i₀,hi₀⟩ := hS
    have hH₀ := (hphysical i₀ hi₀).1
    have hH₀M : H₀≤(M:ℝ) := by
      have hlow := (hphysical i₀ hi₀).2.1
      have hhigh := (hphysical i₀ hi₀).2.2.1.trans hM
      linarith only [hlow,hhigh,hH₀]
    obtain ⟨rinv,hinv,hbound⟩ := hsource ι S (fun _ => f) (fun i => (m i:ℝ))
      (fun i => (r i).num) (fun i => (r i).den) W H hWp
      (fun i hi => (hH i hi).trans (hW i hi).1) F (3*U/2) hF.le (by positivity)
      (fun i hi => (hsmall i hi).1) (fun i hi => (hsmall i hi).2)
      (fun i hi x hx => hf₄ x (hbuf i hi hx))
      (fun i hi x hx => (hfourAbs x (hbuf i hi hx)).2) hcurv
      (fun i hi => ⟨(r i).pos,((hq i hi).2.2.trans (hW i hi).1),
        (r i).isCoprime_num_den,(hmu i hi).1,hscale i hi⟩)
      M H₀ V Wloss d hH₀ hH₀M hV hWloss hd
      (fun i hi => (hphysical i hi).2.1)
      (fun i hi => (hphysical i hi).2.2.2.2.1)
      (fun i hi => (hphysical i hi).2.2.2.2.2)
      (fun i hi => (hphysical i hi).2.2.1.trans hM)
      (fun i hi => (hphysical i hi).2.2.2.1) hdscale

    let S₂ := S ×ˢ (Finset.univ : Finset (Fin 2))
    have hmul₂ n : (S₂.filter (fun p => k p.1=n)).card ≤ 2*Bmul := by
      have he : S₂.filter (fun p => k p.1=n)=
          (S.filter (fun i => k i=n)) ×ˢ (Finset.univ : Finset (Fin 2)) := by
        ext p
        simp only [S₂,Finset.mem_filter,Finset.mem_product,Finset.mem_univ,and_true]
      rw [he,Finset.card_product,Finset.card_univ,Fintype.card_fin]
      have hh := hmul n
      omega
    have hc₀ := hcount S₂
      (fun p => m p.1) (fun p => k p.1) (fun p => (r p.1).num) (fun p => rinv p.1)
      (fun p => z p.1) (fun p => (r p.1).den) Prod.snd N (2*Bmul) M Q s G T P A B w
      hG₀ hT hP hN hQ hw hwhalf hthin hUsmall hLsmall hliftSmall hleft hright hκle
      (fun p hp => hspan _ (Finset.mem_product.mp hp).1) hmul₂
      (fun p hp => ⟨(hm _ (Finset.mem_product.mp hp).1).1.le,(hm _ (Finset.mem_product.mp hp).1).2.le⟩)
      (fun p hp => hdomain ⟨(hz _ (Finset.mem_product.mp hp).1).1.le,(hz _ (Finset.mem_product.mp hp).1).2.le⟩)
      (fun p hp => by simpa only [abs_sub_comm] using hround _ (Finset.mem_product.mp hp).1)
      (fun p hp => ⟨(r p.1).pos,(hq _ (Finset.mem_product.mp hp).1).1,
        (hq _ (Finset.mem_product.mp hp).1).2.1⟩)
      (fun p hp => hinv _ (Finset.mem_product.mp hp).1)
      (fun p hp => by simpa only [Rat.cast_def] using hlevel _ (Finset.mem_product.mp hp).1)
    dsimp only at hc₀
    have hPairRewrite : 4*((2*Bmul:ℕ):ℝ)*S₂.card+
        6*((2*Bmul:ℕ):ℝ)^2*Count*(3*(K:ℝ)+Dweight*(harmonic K:ℝ))=4*Pair := by
      dsimp only [Pair,Z,S₂]
      rw [Finset.card_product,Finset.card_univ,Fintype.card_fin]
      push_cast
      ring
    have hc := hc₀
    change _ ≤ 4*((2*Bmul:ℕ):ℝ)*S₂.card+
      6*((2*Bmul:ℕ):ℝ)^2*Count*(3*(K:ℝ)+Dweight*(harmonic K:ℝ)) at hc
    rw [hPairRewrite] at hc
    simp only [iteratedDeriv_one] at hc

    have hErr i (hi : i∈S) :
        Real.sqrt (W i)*Real.log (2*(W i:ℝ))+1/(mu i*(W i:ℝ)^2)+
          1/(Real.sqrt (mu i*(W i:ℝ))*Real.sqrt (r i).den) ≤ Err := by
      have hQq : (Q:ℝ)/2 ≤ (r i).den := by
        have hh : (Q:ℝ) ≤ 2*((r i).den:ℝ) := by exact_mod_cast (hq i hi).2.1
        linarith only [hh]
      exact displacement_prescribed_source_error hN hQ (r i).pos hL
        (hW i hi).1 (hW i hi).2.1 (hmu i hi).2.1 hQq

    have hlog : 0≤Real.log (6*(N:ℝ)) := by
      have hn : (1:ℝ)≤N := by exact_mod_cast hN
      exact Real.log_nonneg (by linarith only [hn])
    have hErr0 : 0≤Err := by dsimp only [Err]; positivity
    let ErrorSum := ∑ i∈S,(Real.sqrt (W i)*Real.log (2*(W i:ℝ))+1/(mu i*(W i:ℝ)^2)+
      1/(Real.sqrt (mu i*(W i:ℝ))*Real.sqrt (r i).den))
    have hErrorSum0 : 0≤ErrorSum := by
      apply Finset.sum_nonneg
      intro i hi
      have hw1 : (1:ℝ)≤W i := by exact_mod_cast hWp i hi
      have hl := Real.log_nonneg (by linarith only [hw1] : 1≤2*(W i:ℝ))
      have hmup := (hmu i hi).1
      positivity
    have herrorSum : ErrorSum≤Z*Err := by
      calc
        _ ≤ ∑ _i∈S,Err := Finset.sum_le_sum hErr
        _ = S.card*Err := by simp only [Finset.sum_const,nsmul_eq_mul]
        _ ≤ _ := mul_le_mul_of_nonneg_right hcard hErr0
    have hLoss : 0≤Loss := by dsimp only [Loss]; positivity
    have hsrc :
        (∑ i∈S, ‖∑ n∈Finset.Ioc (s+(N:ℤ)*k i) (s+(N:ℤ)*k i+H i),(𝐞 (f n):ℂ)‖)=
        ∑ i∈S, ‖∑ n∈Finset.Ioc (W i:ℤ) ((W i:ℤ)+H i),(𝐞 (f ((m i:ℝ)+n)):ℂ)‖ := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [←(hW i hi).2.2,bourgain_integer_source_translation]
    dsimp only at hbound hc
    rw [←hsrc] at hbound
    exact displacement_frozen_cardinality_absorption S hC.le hLoss hErr0
      hErrorSum0 herrorSum hc hbound
  · have hempty : S=∅ := Finset.not_nonempty_iff_eq_empty.mp hS
    have hZ : Z=0 := by simp only [Z,hempty,Finset.card_empty,Nat.cast_zero]
    have hsrcempty :
        (∑ i∈S, ‖∑ n∈Finset.Ioc (s+(N:ℤ)*k i) (s+(N:ℤ)*k i+H i),(𝐞 (f n):ℂ)‖)^12=0 := by
      rw [hempty]
      simp only [Finset.sum_empty,zero_pow (by norm_num : (12:ℕ)≠0)]
    rw [hsrcempty]
    exact displacement_empty_source_bound C Loss Pair Err Z hZ


/-- Exact balance for the exponent-pair replacement of the second-spacing
term. This is algebra only; the analytic beta consumer is a separate obligation. -/
theorem refined_spacing_exponent_balance {k l a : ℝ} (hk : 0 ≤ k) :
    let u := 1-3*a
    let z := a+u/2
    let v := a+u
    let w := (k*v+(l-1)*z)/(1+k)
    let c := (7*k+l+4)/(24*(1+k))
    let d := (5*k-l+10)/(24*(1+k))
    w+z=k*v+l*z-k*w ∧
      w+z=((2*k+l)/(1+k))*a+((3*k+l)/(2*(1+k)))*u ∧
      10*a+u/2+(a+3*u/2)+(w+z)=12*(c+d*a) := by
  intro u z v w c d
  have hd : (1+k) ≠ 0 := by positivity
  dsimp only [u,z,v,w,c,d]
  field_simp
  constructor
  · ring
  constructor <;> ring

/-- Physical strict inequalities for the prospective Bourgain-input refinement;
this statement does not assert the beta bound. -/
theorem refined_bourgain_scale_domain {a : ℝ} (ha : 2/5 < a) (hb : a < 3/7) :
    let u := 1-3*a
    let z := a+u/2
    let w := -(3+23*a)/194
    let β := max (1/12+2*a/3) (241/1164+425*a/1164)
    u<0 ∧ w<0 ∧ 2-5*a<0 ∧ 0<a+3*u/2 ∧ z<a ∧ z<β ∧
      2*a-1<0 ∧ 1/4+a/4≤β ∧
      ((13/84:ℝ)*(a+u)+(55/84-1)*z)/(1+13/84)=w ∧
      w+z=(47-60*a)/97 := by
  intro u z w β
  have hβ : 1/12+2*a/3 ≤ β := le_max_left _ _
  dsimp only [u,z,w] at *
  refine ⟨by linarith,by linarith,by linarith,by linarith,by linarith,
    by linarith,by linarith,by linarith,?_,?_⟩ <;> ring

/-- Uniform physical bound for the refined count before choosing the free
Fourier width. Constants precede all physical parameters. -/
theorem refined_count_physical_majorant
    {l a b u n p q : ℝ} (hl : 0<l) (ha : 0<a) (hb : 0≤b)
    (hu : 0<u) (hn : 0≤n) (hq : 0≤q) :
    ∃ C > (0:ℝ), ∀ P U K η w : ℝ,
      0<P → 0<U → U≤1 → 1≤P*U*Real.sqrt U →
      0≤K → K≤n*(P*U*Real.sqrt U) →
      0≤η → η≤4*Real.sqrt U → 0<w →
      let D := K/(l*U)+1
      (2*η+w)*D+20736*(b*U/P)*U^4/((a*U/P)^2*(l*U)^2)+
        (P*U/u)^p*D^q*w^(-p)+u/(P*U) ≤
      C*(P*U+w*(P*Real.sqrt U)+(P*U)^p*(P*Real.sqrt U)^q*w^(-p)+1/(P*U)) := by
  let d := n/l+1
  let c := 20736*b/(a^2*l^2)
  let e := (1/u)^p*d^q
  let C := 8*d+c+d+e+u
  have hd : 0<d := by dsimp only [d]; positivity
  have hc : 0≤c := by dsimp only [c]; positivity
  have he : 0≤e := by dsimp only [e]; positivity
  have hC : 0<C := by dsimp only [C]; positivity
  refine ⟨C,hC,?_⟩
  intro P U K η w hP hU hU1 hscale hK hKhi hη hηhi hw D
  have hs : 0<Real.sqrt U := Real.sqrt_pos.mpr hU
  have hPU : 0<P*U := mul_pos hP hU
  have hPS : 1≤P*Real.sqrt U := hscale.trans (by
    calc
      _ ≤ P*1*Real.sqrt U := by gcongr
      _ = _ := by ring)
  have hD : 0<D := by dsimp only [D]; positivity
  have hDu : D≤d*(P*Real.sqrt U) := by
    calc
      _ ≤ (n*(P*U*Real.sqrt U))/(l*U)+P*Real.sqrt U :=
        add_le_add (div_le_div_of_nonneg_right hKhi (by positivity)) hPS
      _ = _ := by dsimp only [d]; field_simp
  have hmain : (2*η+w)*D≤(8*d)*(P*U)+d*(w*(P*Real.sqrt U)) := by
    calc
      _ ≤ (8*Real.sqrt U+w)*(d*(P*Real.sqrt U)) :=
        mul_le_mul (by linarith only [hηhi]) hDu hD.le (by positivity)
      _ = (8*d*P)*(Real.sqrt U)^2+d*(w*(P*Real.sqrt U)) := by ring
      _ = _ := by rw [Real.sq_sqrt hU.le]; ring
  have hcorr : 20736*(b*U/P)*U^4/((a*U/P)^2*(l*U)^2)=c*(P*U) := by
    dsimp only [c]
    field_simp
  have hosc : (P*U/u)^p*D^q*w^(-p) ≤ e*((P*U)^p*(P*Real.sqrt U)^q*w^(-p)) := by
    calc
      _ ≤ (P*U/u)^p*(d*(P*Real.sqrt U))^q*w^(-p) := by gcongr
      _ = _ := by
        rw [show P*U/u=(P*U)*(1/u) by ring,
          Real.mul_rpow hPU.le (by positivity),
          Real.mul_rpow hd.le (by positivity)]
        dsimp only [e]
        ring
  have hC₁ : 8*d+c≤C := by dsimp only [C]; linarith
  have hC₂ : d≤C := by dsimp only [C]; linarith
  have hC₃ : e≤C := by dsimp only [C]; linarith
  have hC₄ : u≤C := by dsimp only [C]; linarith
  calc
    _ ≤ ((8*d)*(P*U)+d*(w*(P*Real.sqrt U)))+c*(P*U)+
        e*((P*U)^p*(P*Real.sqrt U)^q*w^(-p))+u/(P*U) := by
      rw [hcorr]
      exact add_le_add (add_le_add (add_le_add hmain le_rfl) hosc) le_rfl
    _ = (8*d+c)*(P*U)+d*(w*(P*Real.sqrt U))+
        e*((P*U)^p*(P*Real.sqrt U)^q*w^(-p))+u*(1/(P*U)) := by ring
    _ ≤ C*(P*U)+C*(w*(P*Real.sqrt U))+
        C*((P*U)^p*(P*Real.sqrt U)^q*w^(-p))+C*(1/(P*U)) := by gcongr
    _ = _ := by ring

/-- Minimal curvature arcs are constructed from the actual model and retained
through both the low-denominator source estimate and the refined frozen sieve.
No rational family, cardinality estimate or source bound is an input. -/
theorem exists_model_refined_source_bands
    {σ k₀ l₀ ε : ℝ} (hσ : 0 < σ)
    (hpair : ExponentPair k₀ l₀) (hε : 0 < ε) (hp : k₀+ε < 1) :
    ∃ δ κ₀ : ℝ, 0 < δ ∧ 0 < κ₀ ∧
      ∃ Qphase : ℕ, 3 ≤ Qphase ∧ ∃ Cd ≥ (1:ℝ), ∃ Cf > (0:ℝ),
      ∃ Cp : ℝ, 1 ≤ Cp ∧ ∀ (ι : Type*) [DecidableEq ι]
      (S : Finset ι) (F : ℝ → ℝ) (T P : ℝ) (k : ι → ℤ) (H : ι → ℕ)
      (N : ℕ) (s : ℤ) (A B w : ℝ),
      IsApproximateModelPhaseFunction F σ Qphase δ →
      0<T → 0<P → 0<N → 0<w → w≤1/2 → P<A → B<2*P →
      let f := fun t => T*F (t/P)
      let L := modelPhaseJetLower σ 2*T/P^3
      let U := (modelPhaseJetCoefficient σ 2+1)*T/P^3
      let lam := modelPhaseJetLower σ 3*T/P^4
      let F4 := (modelPhaseJetCoefficient σ 3+1)*T/P^4
      let X := (modelPhaseJetCoefficient σ 1+1)*T/P^2/2
      12*U≤1 → L≤1 →
      F4*(6*(N:ℝ)+1)^4≤1 → (3*U/2)*(6*(N:ℝ)+1)^2≤1 →
      (∀ j : ℤ, (S.filter (fun i => k i=j)).card ≤ 1) →
      (∀ i∈S, H i ≤ N) →
      let base := fun i => (s:ℝ)-2*(N:ℝ)+(N:ℝ)*(k i:ℝ)
      (∀ i∈S, Icc (base i-(7*(N:ℝ)+2)) (base i+(7*(N:ℝ)+2)) ⊆ Icc A B) →
      ∃ r : ι → ℚ,
        (∀ Q₀ : ℕ, 2 ≤ Q₀ →
          let D₀ := 8/(L*(N:ℝ)*(Q₀:ℝ))
          ((S.filter (fun i => Q₀ ≤ (r i).den)).card:ℝ) ≤
            4*(X+1)*D₀^2+D₀*(2+Real.log (D₀+1))) ∧
        (∀ j : ℕ,
          let Q : ℕ := 2^(j+1)
          let G := (S.filter (fun i => (r i).den ≤ N)).filter (fun i => Nat.log 2 (r i).den=j)
          let Z := (G.card:ℝ)
          let Zd := 4*(Q:ℝ)*(2*X*Q+1)
          let D := 16/(L*(N:ℝ)*(Q:ℝ))
          let Err := Real.sqrt (3*(N:ℝ))*Real.log (6*(N:ℝ))+6/(L*(N:ℝ)^2)+
            Real.sqrt (12/(L*(N:ℝ)*Q))
          Z ≤ Zd ∧
          (1 ≤ j → Z ≤ 4*(X+1)*D^2+D*(2+Real.log (D+1))) ∧
          (∑ i∈G, ‖∑ n∈Finset.Ioc (s+(N:ℤ)*k i) (s+(N:ℤ)*k i+H i),(𝐞 (f n):ℂ)‖) ≤
            Cd*Zd*(3*(N:ℝ)*Real.sqrt (3*U*(Q:ℝ)*N)+Err) ∧
          (12 ≤ L*(Q:ℝ)*(N:ℝ)^2 → 384 ≤ L^2*(Q:ℝ)^3*(N:ℝ)^3 →
            let M : ℕ := ⌈63*U*(Q:ℝ)*(N:ℝ)^2⌉₊+1
            let V := 756*U/L
            let W := 1+32/(L*(Q:ℝ)^2*N)
            let d := L*(Q:ℝ)*N/12
            let Loss := (5*W)^11*W^2*(6*(3+8*Real.pi*V)*(1+Real.log M))^12*
              (2/d)^6*(M:ℝ)^((12:ℝ)+ε)
            let D₀ := (Real.sqrt M/(9*(M:ℝ))+Real.sqrt M/(12*(M:ℝ)^2))*
              Real.sqrt (U*(Q:ℝ)^3)
            let η := 4*D₀/(Q:ℝ)
            let rho := (12*U*Real.sqrt (U*(Q:ℝ)^3)/lam)*(Real.sqrt M/(6*(M:ℝ)^2))
            let K := ⌈3*U*(rho+1)⌉₊
            let Rmax := 36*U^2/lam
            let Dmax := (K:ℝ)/L+1
            let Dweight := 144*U^2/(lam*N)
            let Count := Cp*((2*η+w)*Dmax+20736*F4*U^4/(lam^2*L^2)+
              (T/P^2)^(k₀+ε)*Dmax^(l₀+ε)*w^(-(k₀+ε))+P^2/T)
            let Pair := 4*Z+6*Count*(3*(K:ℝ)+Dweight*(harmonic K:ℝ))
            (Q:ℝ)^2 < 6*(M:ℝ)^2 →
            2*η+10368*F4*U^4/(lam^2*L) ≤ 1/2 →
            P < A-Rmax → B+Rmax+2*Dmax < 2*P →
            2*(K:ℝ)*P^2/(σ*T) ≤ κ₀ →
            (∑ i∈G, ‖∑ n∈Finset.Ioc (s+(N:ℤ)*k i) (s+(N:ℤ)*k i+H i),(𝐞 (f n):ℂ)‖)^12 ≤
              Cf*(Loss*(2*Z)^10*Pair+(Z*Err)^12))) := by
  classical
  obtain ⟨δ₀,κ₀,hδ₀,hκ₀,Qphase,hQphase,Cf,hCf,Cp,hCp,hfrozenSource⟩ :=
    exists_model_refined_frozen_source hσ hpair hε hp
  obtain ⟨δd,hδd,hdata⟩ := model_displacement_derivative_data hσ
  obtain ⟨Cd,hCd,hdirect⟩ := exists_bourgain_C4_low_denominator_source
  refine ⟨min δ₀ δd,κ₀,lt_min hδ₀ hδd,hκ₀,Qphase,hQphase,Cd,hCd,Cf,hCf,Cp,hCp,?_⟩
  intro ι _ S F T P k H N s A B w hF hT hP hN hw hwhalf hA hB
    f L U lam F4 X hUsmall hLsmall hfourSmall hquadSmall hmul hH base hbuffer
  have hF₀ := approximateModelPhase_mono hF le_rfl (min_le_left _ _)
  have hFd := approximateModelPhase_mono hF hQphase (min_le_right _ _)
  obtain ⟨hreg,hthreeModel,hfourModel,hcurvModel⟩ := hdata F T P hT hP hFd
  have hlam : 0 < lam := by dsimp only [lam]; positivity [modelPhaseJetLower_pos hσ 3]
  have hL : 0 < L := by dsimp only [L]; positivity [modelPhaseJetLower_pos hσ 2]
  have hU : 0 < U := by dsimp only [U]; positivity [modelPhaseJetCoefficient_pos hσ 2]
  have hF4 : 0 ≤ F4 := by dsimp only [F4]; positivity [modelPhaseJetCoefficient_pos hσ 3]
  have hX : 0 ≤ X := by dsimp only [X]; positivity [modelPhaseJetCoefficient_pos hσ 1]
  have hdomain : Icc A B ⊆ Ioo P (2*P) := by
    intro t ht
    exact ⟨hA.trans_le ht.1,ht.2.trans_lt hB⟩
  have hf₄ t (ht : t∈Icc A B) : ContDiffAt ℝ 4 f t :=
    (hreg t (hdomain ht)).of_le (by norm_num)
  have hthree t (ht : t∈Icc A B) :
      L ≤ iteratedDeriv 3 f t ∧ iteratedDeriv 3 f t ≤ 6*U := by
    have hh := hthreeModel t (hdomain ht)
    exact ⟨hh.1,by linarith [hh.2]⟩
  have hfourAbs t (ht : t∈Icc A B) : |iteratedDeriv 4 f t| ≤ F4 := by
    have hh := hfourModel t (hdomain ht)
    rw [abs_of_neg (by linarith only [hh.2,hlam])]
    linarith only [hh.1]
  have hcurv t (ht : t∈Icc A B) : |iteratedDeriv 2 f t/2| ≤ X :=
    hcurvModel t (hdomain ht)
  have hNr : (1:ℝ) ≤ N := by exact_mod_cast hN
  have ht i (hi : i∈S) : base i∈Icc A B :=
    hbuffer i hi ⟨by linarith only [hNr],by linarith only [hNr]⟩
  obtain ⟨r,z,hr,htail₀⟩ := exists_bourgain_C3_minimal_curvature_arc_count S f k N 1
    ((s:ℝ)-2*(N:ℝ)) hN hL hX
    (fun t ht => (hf₄ t ht).of_le (by norm_num)) (fun t ht => (hthree t ht).1) hmul
    (by
      intro i hi x hx
      apply hbuffer i hi
      change base i-(N:ℝ)/4 ≤ x ∧ x ≤ base i+(N:ℝ)/4 at hx
      constructor <;> linarith only [hx.1,hx.2,hNr])
    (fun i hi => hcurv _ (ht i hi))
  have hgeo i (hi : i∈S) : z i∈Ioo A B ∧ |z i-(round (z i):ℝ)| ≤ 1/2 ∧
      ((N:ℤ) ≤ s+(N:ℤ)*k i-round (z i) ∧
        s+(N:ℤ)*k i-round (z i) ≤ 3*(N:ℤ)) ∧
      Icc ((round (z i):ℝ)-(6*(N:ℝ)+1)) ((round (z i):ℝ)+(6*(N:ℝ)+1)) ⊆ Icc A B := by
    have hz := (hr i hi).1
    change z i∈Ioo (base i-(N:ℝ)/4) (base i+(N:ℝ)/4) at hz
    have hround : |z i-(round (z i):ℝ)| ≤ 1/2 := abs_sub_round (z i)
    have hround' := abs_le.mp hround
    have hlo := (hbuffer i hi (left_mem_Icc.mpr (by linarith only [hNr]))).1
    have hhi := (hbuffer i hi (right_mem_Icc.mpr (by linarith only [hNr]))).2
    have hstart : ((s+(N:ℤ)*k i:ℤ):ℝ)=base i+2*(N:ℝ) := by
      dsimp only [base]; push_cast; ring
    refine ⟨⟨by linarith only [hlo,hz.1,hNr],by linarith only [hhi,hz.2,hNr]⟩,hround,?_,?_⟩
    · have hlow : (N:ℝ) ≤ ((s+(N:ℤ)*k i:ℤ):ℝ)-(round (z i):ℝ) := by
        linarith only [hz.1,hz.2,hround'.1,hround'.2,hstart,hNr]
      have hhigh : ((s+(N:ℤ)*k i:ℤ):ℝ)-(round (z i):ℝ) ≤ 3*(N:ℝ) := by
        linarith only [hz.1,hz.2,hround'.1,hround'.2,hstart,hNr]
      constructor
      · exact_mod_cast hlow
      · exact_mod_cast hhigh
    · intro x hx
      apply hbuffer i hi
      constructor <;> linarith only [hx.1,hx.2,hz.1,hz.2,hround'.1,hround'.2,hNr]
  have hlevel i (hi : i∈S) : iteratedDeriv 2 f (z i)/2=(r i:ℝ) := (hr i hi).2.1
  have htail (Q₀ : ℕ) (hQ₀ : 2≤Q₀) :
      let D₀ := 8/(L*(N:ℝ)*(Q₀:ℝ))
      ((S.filter (fun i => Q₀ ≤ (r i).den)).card:ℝ) ≤
        4*(X+1)*D₀^2+D₀*(2+Real.log (D₀+1)) := by
    simpa only [Nat.cast_one,one_mul] using htail₀ Q₀ hQ₀
  refine ⟨r,htail,?_⟩
  intro j Q G Z Zd D Err
  have hQ : 0 < Q := by dsimp only [Q]; positivity
  have hGS : G ⊆ S := fun i hi =>
    (Finset.mem_filter.mp (Finset.mem_filter.mp hi).1).1
  have hmulG n : (G.filter (fun i => k i=n)).card ≤ 1 :=
    (Finset.card_le_card (Finset.filter_subset_filter _ hGS)).trans (hmul n)
  have hqdata i (hi : i∈G) :
      (r i).den ≤ Q ∧ Q ≤ 2*(r i).den ∧ (r i).den ≤ N := by
    obtain ⟨hi',hj⟩ := Finset.mem_filter.mp hi
    have hlo := Nat.pow_log_le_self 2 (r i).pos.ne'
    have hhi := Nat.lt_pow_succ_log_self (by norm_num : 1<(2:ℕ)) (r i).den
    rw [hj] at hlo hhi
    refine ⟨hhi.le,?_,(Finset.mem_filter.mp hi').2⟩
    calc
      Q=2*2^j := by dsimp only [Q]; rw [pow_succ,Nat.mul_comm]
      _ ≤ _ := Nat.mul_le_mul_left _ hlo
  have hdir := hdirect ι G f r z (fun i => round (z i)) k H N Q 1 s A B L F4 U X
    hN hQ hL hF4 hU hX hfourSmall hquadSmall hf₄ hthree hfourAbs
    (fun i hi => (hgeo i (hGS hi)).1)
    (fun i hi => (hgeo i (hGS hi)).2.2.2)
    (fun i hi => (hgeo i (hGS hi)).2.1)
    (fun i hi => (hgeo i (hGS hi)).2.2.1)
    hmulG (fun i hi => hH i (hGS hi)) hqdata
    (fun i hi => hlevel i (hGS hi))
    (fun i hi => hcurv _ ⟨(hgeo i (hGS hi)).1.1.le,(hgeo i (hGS hi)).1.2.le⟩)
  dsimp only at hdir
  simp only [Nat.cast_one,mul_one] at hdir
  refine ⟨hdir.1,?_,?_,?_⟩
  · intro hj
    have htwo : 2 ≤ 2^j := by simpa using Nat.pow_le_pow_right (by norm_num : 1 ≤ (2:ℕ)) hj
    have hsubset : G ⊆ S.filter (fun i => 2^j ≤ (r i).den) := by
      intro i hi
      apply Finset.mem_filter.mpr
      refine ⟨hGS hi,?_⟩
      have hh := Nat.pow_log_le_self 2 (r i).pos.ne'
      rw [(Finset.mem_filter.mp hi).2] at hh
      exact hh
    have hh := (Nat.cast_le.mpr (Finset.card_le_card hsubset)).trans (htail (2^j) htwo)
    have he : 8/(L*(N:ℝ)*(2^j:ℕ))=D := by
      dsimp only [D,Q]
      rw [pow_succ,Nat.cast_mul,Nat.cast_ofNat]
      ring
    simpa only [he] using hh
  · dsimp only [Err,Zd]
    convert hdir.2 using 1
    ring
  · intro hdual hfrozen M V Wloss d Loss D₀ η rho K Rmax Dmax Dweight Count Pair
      hthin hliftSmall hleft hright hκle
    have hs := hfrozenSource ι G F T P r z (fun i => round (z i)) k H N Q 1 s A B w
      hF₀ hT hP hN hQ hw hwhalf hUsmall hLsmall hfourSmall hquadSmall
      (fun i hi => (hgeo i (hGS hi)).1)
      (fun i hi => (hgeo i (hGS hi)).2.2.2)
      (fun i hi => (hgeo i (hGS hi)).2.1)
      (fun i hi => (hgeo i (hGS hi)).2.2.1)
      hmulG (fun i hi => hH i (hGS hi)) hqdata
      (fun i hi => hlevel i (hGS hi)) hdual hfrozen hthin hliftSmall hleft hright hκle
    simpa only [Nat.cast_one,mul_one,one_pow] using hs

/-- The source error and small-denominator bands fit the first refined
twelfth-moment term when the same lifting scale P*U^2 is small. -/
theorem refined_elementary_twelfth
    {P U Z C Log ε r : ℝ} (hP : 1≤P) (hU : 0<U) (hU1 : U≤1)
    (hZ : 0≤Z) (hC : 0≤C) (hLog : 1≤Log) (hε : 0≤ε)
    (hr : 1/4≤r) (hsmall : P*U^2≤1)
    (hbound : Z≤C*P*U^r*Log^2) :
    Z^12 ≤ C^12*P^ε*Log^24*(P^11*U) := by
  have hPp : 0<P := zero_lt_one.trans_le hP
  have hUquarter : U^r≤U^((1:ℝ)/4) :=
    Real.rpow_le_rpow_of_exponent_ge hU hU1 hr
  have hpower : (U^((1:ℝ)/4))^12=U^3 := by
    rw [←Real.rpow_mul_natCast hU.le]
    norm_num
  have hbase : P^12*U^3≤P^11*U := by
    have hh := mul_le_mul_of_nonneg_left hsmall (show 0≤P^11*U by positivity)
    nlinarith only [hh]
  have hPe : 1≤P^ε := Real.one_le_rpow hP hε
  calc
    _ ≤ (C*P*U^((1:ℝ)/4)*Log^2)^12 := by
      apply pow_le_pow_left₀ hZ
      exact hbound.trans (by gcongr)
    _ = C^12*Log^24*(P^12*U^3) := by
      rw [mul_pow,mul_pow,mul_pow,hpower]
      ring
    _ ≤ C^12*Log^24*(P^11*U) := mul_le_mul_of_nonneg_left hbase (by positivity)
    _ ≤ _ := by
      have hh := mul_le_mul_of_nonneg_left hPe (show 0≤C^12*Log^24*(P^11*U) by positivity)
      nlinarith only [hh]


theorem refined_spacing_physical_product
    {P U w p q : ℝ} (hP : 0<P) (hU : 0<U) :
    P^10*Real.sqrt U*(P*U*Real.sqrt U)*
      (P*U+w*(P*Real.sqrt U)+(P*U)^p*(P*Real.sqrt U)^q*w^(-p)+1/(P*U)) =
    P^12*U^3+w*P^12*U^((5:ℝ)/2)+
      P^(11+p+q)*U^(2+p+q/2)*w^(-p)+P^10*U := by
  have hbase : P^10*Real.sqrt U*(P*U*Real.sqrt U)=P^11*U^2 := by
    calc
      _ = P^11*U*(Real.sqrt U)^2 := by ring
      _ = _ := by rw [Real.sq_sqrt hU.le]; ring
  have hroot : U^2*Real.sqrt U=U^((5:ℝ)/2) := by
    rw [Real.sqrt_eq_rpow,←Real.rpow_natCast U 2,←Real.rpow_add hU]
    norm_num
  have hpowers : P^(11+p+q)=P^11*P^p*P^q := by
    rw [Real.rpow_add hP,Real.rpow_add hP]
    norm_num
  have hupowers : U^(2+p+q/2)=U^2*U^p*U^(q/2) := by
    rw [Real.rpow_add hU,Real.rpow_add hU]
    norm_num
  have hdensity : P^11*U^2*((P*U)^p*(P*Real.sqrt U)^q)=
      P^(11+p+q)*U^(2+p+q/2) := by
    rw [Real.mul_rpow hP.le hU.le,Real.mul_rpow hP.le (Real.sqrt_nonneg U),
      Real.sqrt_eq_rpow,←Real.rpow_mul hU.le,hpowers,hupowers]
    rw [show (1/2:ℝ)*q=q/2 by ring]
    ring
  have hinv : P^11*U^2*(1/(P*U))=P^10*U := by
    field_simp
  rw [hbase]
  calc
    _ = P^12*U^3+w*P^12*(U^2*Real.sqrt U)+
        (P^11*U^2*((P*U)^p*(P*Real.sqrt U)^q))*w^(-p)+P^11*U^2*(1/(P*U)) := by ring
    _ = _ := by rw [hroot,hdensity,hinv]

theorem refined_spacing_physical_product_bound
    {P U w p q : ℝ} (hP : 1≤P) (hU : 0<U) (hw : 0≤w) (hsmall : P*U^2≤1) :
    P^10*Real.sqrt U*(P*U*Real.sqrt U)*
      (P*U+w*(P*Real.sqrt U)+(P*U)^p*(P*Real.sqrt U)^q*w^(-p)+1/(P*U)) ≤
    2*(P^11*U+w*P^12*U^((5:ℝ)/2)+P^(11+p+q)*U^(2+p+q/2)*w^(-p)) := by
  have hPp : 0<P := zero_lt_one.trans_le hP
  rw [refined_spacing_physical_product hPp hU]
  have hfirst : P^12*U^3≤P^11*U := by
    have hh := mul_le_mul_of_nonneg_left hsmall (show 0≤P^11*U by positivity)
    nlinarith only [hh]
  have hlast : P^10*U≤P^11*U := by
    have hh := mul_le_mul_of_nonneg_left hP (show 0≤P^10*U by positivity)
    nlinarith only [hh]
  have hmid : 0≤w*P^12*U^((5:ℝ)/2) := by positivity
  have hdensity : 0≤P^(11+p+q)*U^(2+p+q/2)*w^(-p) := by positivity
  linarith only [hfirst,hlast,hmid,hdensity]
/-- Uniform denominator-free bound for the actual refined spacing cost.
The two elementary cardinality caps are consumed by the existing loss bound. -/
theorem exists_refined_uniform_frozen_rhs
    {l ε Cc p q : ℝ} (hl : 0<l) (hε : 0<ε) (hCc : 1≤Cc) :
    ∃ C > (0:ℝ), ∀ (P U Z w : ℝ) (Q : ℕ),
      0<P → 0<U → U≤1/3600 → 1≤P*U → P*U^2≤1 → 0≤Z → 0<w →
      0<Q → (Q:ℝ)≤P →
      Z≤Cc*P*U*(Q:ℝ)^2 → Z≤Cc*(P/(Q:ℝ)^2)*(1+Real.log P) →
      let N := ⌊1/(10*Real.sqrt U)⌋₊
      let L := l*U
      let M : ℕ := ⌈63*U*(Q:ℝ)*(N:ℝ)^2⌉₊+1
      let V := 756*U/L
      let W := 1+32/(L*(Q:ℝ)^2*N)
      let d := L*(Q:ℝ)*N/12
      let Loss := (5*W)^11*W^2*(6*(3+8*Real.pi*V)*(1+Real.log M))^12*
        (2/d)^6*(M:ℝ)^((12:ℝ)+ε)
      let Err := Real.sqrt (3*(N:ℝ))*Real.log (6*(N:ℝ))+6/(L*(N:ℝ)^2)+
        Real.sqrt (12/(L*(N:ℝ)*Q))
      let E := P*U+w*(P*Real.sqrt U)+(P*U)^p*(P*Real.sqrt U)^q*w^(-p)+1/(P*U)
      let R := Z+(P*U*Real.sqrt U)*E*(1+Real.log P)
      Loss*(2*Z)^10*R+(Z*Err)^12 ≤
        C*P^ε*(1+Real.log P)^24*
          (P^11*U+w*P^12*U^((5:ℝ)/2)+P^(11+p+q)*U^(2+p+q/2)*w^(-p)) := by
  obtain ⟨Cl,hCl,hloss⟩ := exists_displacement_frozen_loss_bound hl hε
  obtain ⟨Ce,hCe,herror⟩ := exists_displacement_frozen_error_majorant hl
  let C := Cl*Cc^10*(Cc+2)+(Cc*Ce)^12
  have hCcp : 0<Cc := zero_lt_one.trans_le hCc
  refine ⟨C,by dsimp only [C]; positivity,?_⟩
  intro P U Z w Q hP hU hUsmall hPU hsmall hZ hw hQ hQP hZlo hZhi
    N L M V W d Loss Err E R
  have hU1 : U≤1 := by linarith only [hUsmall]
  have hP1 : 1≤P := hPU.trans (by nlinarith only [mul_le_mul_of_nonneg_left hU1 hP.le])
  have hQr : (0:ℝ)<Q := Nat.cast_pos.mpr hQ
  have hQ1 : (1:ℝ)≤Q := by exact_mod_cast hQ
  let J := 1+Real.log P
  let B := Cc*P*J
  let Cost := P^11*U+w*P^12*U^((5:ℝ)/2)+P^(11+p+q)*U^(2+p+q/2)*w^(-p)
  have hlogP := Real.log_nonneg hP1
  have hJ1 : 1≤J := by dsimp only [J]; linarith only [hlogP]
  have hJ : 0<J := zero_lt_one.trans_le hJ1
  have hB : 0<B := by dsimp only [B]; positivity
  have hCost : 0≤Cost := by dsimp only [Cost]; positivity
  have hFirst : P^11*U≤Cost := by
    have hmid : 0≤w*P^12*U^((5:ℝ)/2) := by positivity
    have hlast : 0≤P^(11+p+q)*U^(2+p+q/2)*w^(-p) := by positivity
    dsimp only [Cost]
    linarith only [hmid,hlast]
  have hZlo' : Z ≤ B*U*(Q:ℝ)^2 := by
    calc
      _ ≤ Cc*P*U*(Q:ℝ)^2 := hZlo
      _ ≤ _ := by
        have hh := le_mul_of_one_le_right (show 0 ≤ Cc*P*U*(Q:ℝ)^2 by positivity) hJ1
        dsimp only [B]
        nlinarith only [hh]
  have hZhi' : Z*(Q:ℝ)^2 ≤ B := by
    have hh := mul_le_mul_of_nonneg_right hZhi (sq_nonneg (Q:ℝ))
    convert hh using 1
    dsimp only [B,J]
    field_simp
  have hZgeo : Z ≤ Cc*P*J*Real.sqrt U :=
    displacement_cardinality_geometric hU.le hQr hZ hZlo' hZhi'
  have hQpow : (Q:ℝ)^ε ≤ P^ε := Real.rpow_le_rpow hQr.le hQP hε.le
  have hlogQ : 0 ≤ 1+Real.log Q := by
    have hh := Real.log_nonneg hQ1
    positivity
  have hlogQP : 1+Real.log Q ≤ J := add_le_add_right (Real.log_le_log hQr hQP) 1
  have hLoss : Loss*(2*Z)^10 ≤ Cl*Cc^10*P^10*Real.sqrt U*P^ε*J^22 := by
    calc
      _ ≤ Cl*B^10*Real.sqrt U*(Q:ℝ)^ε*(1+Real.log Q)^12 :=
        hloss U B Z Q hU hUsmall hZ hQ hZlo' hZhi'
      _ ≤ Cl*B^10*Real.sqrt U*P^ε*J^12 := by gcongr
      _ = _ := by dsimp only [B]; ring
  have hZprod : P^10*Real.sqrt U*Z≤Cc*J*(P^11*U) := by
    calc
      _ ≤ P^10*Real.sqrt U*(Cc*P*J*Real.sqrt U) :=
        mul_le_mul_of_nonneg_left hZgeo (by positivity)
      _ = Cc*J*P^11*(Real.sqrt U)^2 := by ring
      _ = _ := by rw [Real.sq_sqrt hU.le]; ring
  have hprod := refined_spacing_physical_product_bound (p:=p) (q:=q) hP1 hU hw.le hsmall
  change P^10*Real.sqrt U*(P*U*Real.sqrt U)*E≤2*Cost at hprod
  have hRprod : P^10*Real.sqrt U*R≤(Cc+2)*J*Cost := by
    calc
      _ = P^10*Real.sqrt U*Z+(P^10*Real.sqrt U*(P*U*Real.sqrt U)*E)*J := by
        dsimp only [R,J]
        ring
      _ ≤ Cc*J*(P^11*U)+(2*Cost)*J :=
        add_le_add hZprod (mul_le_mul_of_nonneg_right hprod hJ.le)
      _ ≤ Cc*J*Cost+(2*Cost)*J := by gcongr
      _ = _ := by ring
  have hR : 0≤R := by dsimp only [R,E]; positivity
  have hmain : Loss*(2*Z)^10*R≤Cl*Cc^10*(Cc+2)*P^ε*J^24*Cost := by
    calc
      _ ≤ (Cl*Cc^10*P^10*Real.sqrt U*P^ε*J^22)*R :=
        mul_le_mul_of_nonneg_right hLoss hR
      _ = (Cl*Cc^10*P^ε*J^22)*(P^10*Real.sqrt U*R) := by ring
      _ ≤ (Cl*Cc^10*P^ε*J^22)*((Cc+2)*J*Cost) :=
        mul_le_mul_of_nonneg_left hRprod (by positivity)
      _ = Cl*Cc^10*(Cc+2)*P^ε*J^23*Cost := by ring
      _ ≤ _ := by gcongr; norm_num
  have hErr : Err ≤ Ce*U^(-(1:ℝ)/4)*J := herror P U Q hP hU hUsmall hPU hQ1
  have hErr0 : 0 ≤ Err := by
    have hN1 : (1:ℝ) ≤ N := by exact_mod_cast (displacement_block_scale hU hUsmall).1
    have hlogN := Real.log_nonneg (show 1 ≤ 6*(N:ℝ) by linarith only [hN1])
    dsimp only [Err,L]
    positivity
  have hquarter : Real.sqrt U*U^(-(1:ℝ)/4)=U^((1:ℝ)/4) := by
    rw [Real.sqrt_eq_rpow,←Real.rpow_add hU]
    norm_num
  have hZE : Z*Err ≤ Cc*Ce*P*U^((1:ℝ)/4)*J^2 := by
    calc
      _ ≤ (Cc*P*J*Real.sqrt U)*(Ce*U^(-(1:ℝ)/4)*J) :=
        mul_le_mul hZgeo hErr hErr0 (by positivity)
      _ = Cc*Ce*P*(Real.sqrt U*U^(-(1:ℝ)/4))*J^2 := by ring
      _ = _ := by rw [hquarter]
  have herror₀ := refined_elementary_twelfth hP1 hU hU1 (mul_nonneg hZ hErr0)
    (mul_nonneg hCcp.le hCe.le) hJ1 hε.le (le_refl ((1:ℝ)/4)) hsmall hZE
  have herror' : (Z*Err)^12≤(Cc*Ce)^12*P^ε*J^24*Cost :=
    herror₀.trans (mul_le_mul_of_nonneg_left hFirst (by positivity))
  calc
    _ ≤ Cl*Cc^10*(Cc+2)*P^ε*J^24*Cost+(Cc*Ce)^12*P^ε*J^24*Cost :=
      add_le_add hmain herror'
    _ = _ := by dsimp only [C,Cost]; ring


/-- Physical normalization of the refined count and its harmonic shift weight. -/
theorem exists_refined_physical_pair_bound
    {l a b u p q Cp : ℝ} (hl : 0<l) (ha : 0<a) (hb : 0≤b)
    (hu : 0<u) (hq : 0≤q) (hCp : 1≤Cp) :
    ∃ Ca ≥ (1:ℝ), ∀ P U M Q Z w : ℝ,
      0<P → 0<U → U≤1/3600 → 1≤P*U*Real.sqrt U →
      1≤M → 0<Q → Q≤4*M → 0≤Z → 0<w →
      let N := ⌊1/(10*Real.sqrt U)⌋₊
      let L := l*U
      let lam := a*U/P
      let D₀ := (Real.sqrt M/(9*M)+Real.sqrt M/(12*M^2))*Real.sqrt (U*Q^3)
      let η := 4*D₀/Q
      let rho := (12*U*Real.sqrt (U*Q^3)/lam)*(Real.sqrt M/(6*M^2))
      let K := ⌈3*U*(rho+1)⌉₊
      let Dmax := (K:ℝ)/L+1
      let Dweight := 144*U^2/(lam*N)
      let E := P*U+w*(P*Real.sqrt U)+(P*U)^p*(P*Real.sqrt U)^q*w^(-p)+1/(P*U)
      let Count := Cp*((2*η+w)*Dmax+20736*(b*U/P)*U^4/(lam^2*L^2)+
        (P*U/u)^p*Dmax^q*w^(-p)+u/(P*U))
      4*Z+6*Count*(3*(K:ℝ)+Dweight*(harmonic K:ℝ)) ≤
        Ca*(Z+(P*U*Real.sqrt U)*E*(1+Real.log P)) := by
  let n := 2+48/a
  have hn : 1≤n := by
    have hh : 0<48/a := by positivity
    dsimp only [n]
    linarith only [hh]
  obtain ⟨Ce,hCe,hcount⟩ := refined_count_physical_majorant
    (p:=p) hl ha hb hu (le_trans zero_le_one hn) hq
  let Ch := 3*n+(1728/a)*(1+Real.log n)
  have hCh : 0<Ch := by
    have hlogn := Real.log_nonneg hn
    dsimp only [Ch]
    positivity
  let Ca := 4+6*Cp*Ce*Ch
  have hCa : 1≤Ca := by
    have hh : 0≤6*Cp*Ce*Ch := by positivity
    dsimp only [Ca]
    linarith only [hh]
  refine ⟨Ca,hCa,?_⟩
  intro P U M Q Z w hP hU hUsmall hK hM hQ hQM hZ hw
    N L lam D₀ η rho K Dmax Dweight E Count
  have hU1 : U≤1 := by linarith only [hUsmall]
  have hscale := displacement_block_physical_scale hP hU hUsmall hK
  have hcut := displacement_physical_cutoff ha hP hU hUsmall hK hM hQ hQM
  change 1≤K ∧ (K:ℝ)≤n*(P*U*Real.sqrt U) ∧ η≤4*Real.sqrt U ∧
    Dweight≤(1728/a)*(P*U*Real.sqrt U) at hcut
  have hη : 0≤η := by dsimp only [η,D₀]; positivity
  have hN : (0:ℝ)<N := Nat.cast_pos.mpr (displacement_block_scale hU hUsmall).1
  have hlam : 0<lam := by dsimp only [lam]; positivity
  have hDweight : 0≤Dweight := by dsimp only [Dweight]; positivity
  have hcount' : Count≤(Cp*Ce)*E := by
    have hh := hcount P U K η w hP hU hU1 hK (Nat.cast_nonneg K) hcut.2.1 hη hcut.2.2.1 hw
    dsimp only [Count]
    calc
      _ ≤ Cp*(Ce*E) := mul_le_mul_of_nonneg_left hh (le_trans zero_le_one hCp)
      _ = _ := by ring
  have hweight := displacement_harmonic_weight hn hscale.2.1 hU hU1
    hcut.1 hcut.2.1 hDweight hcut.2.2.2
  change _≤Ch*(P*U*Real.sqrt U)*(1+Real.log P) at hweight
  have hharm : 0≤(harmonic K:ℝ) := by
    simp only [harmonic_eq_sum_Icc,Rat.cast_sum,Rat.cast_inv,Rat.cast_natCast]
    exact Finset.sum_nonneg (fun i _ => inv_nonneg.mpr (Nat.cast_nonneg i))
  have hweight0 : 0≤3*(K:ℝ)+Dweight*(harmonic K:ℝ) := by positivity
  have hlogP := Real.log_nonneg hscale.2.1
  have hE : 0≤E := by dsimp only [E]; positivity
  have hweighted : Count*(3*(K:ℝ)+Dweight*(harmonic K:ℝ))≤
      (Cp*Ce*Ch)*((P*U*Real.sqrt U)*E*(1+Real.log P)) := by
    calc
      _ ≤ ((Cp*Ce)*E)*(Ch*(P*U*Real.sqrt U)*(1+Real.log P)) :=
        mul_le_mul hcount' hweight hweight0 (by positivity)
      _ = _ := by ring
  have hc0 : 0≤Cp*Ce*Ch := by positivity
  have ht0 : 0≤(P*U*Real.sqrt U)*E*(1+Real.log P) := by positivity
  dsimp only [Ca]
  nlinarith only [hweighted,mul_nonneg hc0 hZ,ht0]

/-- The physical cutoff implies all lifting and interior-margin hypotheses. -/
theorem refined_physical_lifting_domain
    {σ l a b u n P T U η K κ₀ A B : ℝ}
    (hσ : 0<σ) (hl : 0<l) (ha : 0<a) (hn : 0≤n)
    (hP : 0<P) (hT : 0<T) (hU : 0<U) (hU1 : U≤1)
    (hUeq : U=u*T/P^3) (hK : 1≤P*U*Real.sqrt U)
    (hKhi : K≤n*(P*U*Real.sqrt U)) (hηhi : η≤4*Real.sqrt U)
    (hlift : 8*Real.sqrt U+(10368*b/(a^2*l))*(P*U^2)≤1/2)
    (hκ : (2*n*u/σ)*Real.sqrt U≤κ₀)
    (hA : P+(36/a+2*(n/l+1)+1)*(P*Real.sqrt U)<A)
    (hB : B+(36/a+2*(n/l+1)+1)*(P*Real.sqrt U)<2*P) :
    let L := l*U
    let lam := a*U/P
    let Rmax := 36*U^2/lam
    let Dmax := K/L+1
    2*η+10368*(b*U/P)*U^4/(lam^2*L)≤1/2 ∧
      P<A-Rmax ∧ B+Rmax+2*Dmax<2*P ∧ 2*K*P^2/(σ*T)≤κ₀ := by
  intro L lam Rmax Dmax
  let m := 36/a+2*(n/l+1)+1
  have hL : 0<L := by dsimp only [L]; positivity
  have hRmax : Rmax≤(36/a)*(P*Real.sqrt U) := by
    have hUsqrt : U≤Real.sqrt U := by
      nlinarith only [Real.sq_sqrt hU.le,Real.sqrt_le_one.mpr hU1,Real.sqrt_nonneg U]
    calc
      _ = (36/a)*(P*U) := by dsimp only [Rmax,lam]; field_simp
      _ ≤ _ := by gcongr
  have hPS : 1≤P*Real.sqrt U := hK.trans (by
    calc
      _ ≤ P*1*Real.sqrt U := by gcongr
      _ = _ := by ring)
  have hDmax : Dmax≤(n/l+1)*(P*Real.sqrt U) := by
    calc
      _ ≤ (n*(P*U*Real.sqrt U))/(l*U)+P*Real.sqrt U :=
        add_le_add (div_le_div_of_nonneg_right hKhi hL.le) hPS
      _ = _ := by field_simp
  have hlift' : 2*η+10368*(b*U/P)*U^4/(lam^2*L)≤1/2 := by
    have hid : 10368*(b*U/P)*U^4/(lam^2*L)=
        (10368*b/(a^2*l))*(P*U^2) := by dsimp only [lam,L]; field_simp
    rw [hid]
    linarith only [hηhi,hlift]
  have hleft : P<A-Rmax := by
    have hgap : Rmax < m*(P*Real.sqrt U) := by
      have hh : 0<(2*(n/l+1)+1)*(P*Real.sqrt U) := by positivity
      dsimp only [m]
      nlinarith only [hRmax,hh]
    linarith only [hA,hgap]
  have hright : B+Rmax+2*Dmax<2*P := by
    have hh : 0<P*Real.sqrt U := by positivity
    nlinarith only [hB,hRmax,hDmax,hh]
  have hκ' : 2*K*P^2/(σ*T)≤κ₀ := by
    calc
      _ ≤ 2*(n*(P*U*Real.sqrt U))*P^2/(σ*T) := by gcongr
      _ = (2*n*u/σ)*Real.sqrt U := by simp only [hUeq]; field_simp
      _ ≤ _ := hκ
  exact ⟨hlift',hleft,hright,hκ'⟩

/-- Uniform rational-band estimate for the actual model sum.  All analytic
constants precede the model and its physical scales; the remaining assumptions
are explicit smallness and interior-margin conditions, not source bounds. -/
theorem exists_model_uniform_refined_source_bands
    {σ k₀ l₀ ε : ℝ} (hσ : 0<σ)
    (hpair : ExponentPair k₀ l₀) (hε : 0<ε) (hp : k₀+ε<1) :
    let u := modelPhaseJetCoefficient σ 2+1
    let l := modelPhaseJetLower σ 2/u
    let a := modelPhaseJetLower σ 3/u
    let b := (modelPhaseJetCoefficient σ 3+1)/u
    let x := (modelPhaseJetCoefficient σ 1+1)/(2*u)
    let n := 2+48/a
    let m := 36/a+2*(n/l+1)+1
    ∃ δ κ₀ : ℝ, 0<δ ∧ 0<κ₀ ∧
      ∃ Qphase : ℕ, 3≤Qphase ∧ ∃ Cd ≥ (1:ℝ), ∃ C > (0:ℝ),
      ∀ (ι : Type*) [DecidableEq ι] (S : Finset ι) (F : ℝ→ℝ)
        (T P : ℝ) (k : ι→ℤ) (H : ι→ℕ) (s : ℤ) (A B w : ℝ),
      IsApproximateModelPhaseFunction F σ Qphase δ →
      0<T → 0<P → 0<w → w≤1/2 →
      let U := u*T/P^3
      let N := ⌊1/(10*Real.sqrt U)⌋₊
      let L := l*U
      let X := x*P*U
      U≤1/3600 → 1≤P*U*Real.sqrt U → b≤P*U → l*U≤1 →
      P*U^2≤1 → 8*Real.sqrt U+(10368*b/(a^2*l))*(P*U^2)≤1/2 →
      (2*n*u/σ)*Real.sqrt U≤κ₀ →
      P+m*(P*Real.sqrt U)<A → B+m*(P*Real.sqrt U)<2*P →
      (∀ j : ℤ, (S.filter (fun i => k i=j)).card≤1) →
      (∀ i∈S, H i≤N) →
      let base := fun i => (s:ℝ)-2*(N:ℝ)+(N:ℝ)*(k i:ℝ)
      (∀ i∈S, Icc (base i-(7*(N:ℝ)+2)) (base i+(7*(N:ℝ)+2))⊆Icc A B) →
      ∃ r : ι→ℚ,
        (∀ Q₀ : ℕ, 2≤Q₀ →
          let D₀ := 8/(L*(N:ℝ)*(Q₀:ℝ))
          ((S.filter (fun i => Q₀≤(r i).den)).card:ℝ)≤
            4*(X+1)*D₀^2+D₀*(2+Real.log (D₀+1))) ∧
        (∀ j : ℕ,
          let Q : ℕ := 2^(j+1)
          let G := (S.filter (fun i => (r i).den≤N)).filter (fun i => Nat.log 2 (r i).den=j)
          let Zd := 4*(Q:ℝ)*(2*X*Q+1)
          let Err := Real.sqrt (3*(N:ℝ))*Real.log (6*(N:ℝ))+6/(L*(N:ℝ)^2)+
            Real.sqrt (12/(L*(N:ℝ)*Q))
          (∑ i∈G, ‖∑ t∈Finset.Ioc (s+(N:ℤ)*k i) (s+(N:ℤ)*k i+H i),
            (𝐞 (T*F ((t:ℝ)/P)):ℂ)‖)≤
            Cd*Zd*(3*(N:ℝ)*Real.sqrt (3*U*(Q:ℝ)*N)+Err) ∧
          (1≤j → 12≤L*(Q:ℝ)*(N:ℝ)^2 → 384≤L^2*(Q:ℝ)^3*(N:ℝ)^3 →
            (∑ i∈G, ‖∑ t∈Finset.Ioc (s+(N:ℤ)*k i) (s+(N:ℤ)*k i+H i),
              (𝐞 (T*F ((t:ℝ)/P)):ℂ)‖)^12 ≤
              C*P^ε*(1+Real.log P)^24*
                (P^11*U+w*P^12*U^((5:ℝ)/2)+
                  P^(11+(k₀+ε)+(l₀+ε))*U^(2+(k₀+ε)+(l₀+ε)/2)*w^(-(k₀+ε))))) := by
  classical
  intro u l a b x n m
  have hu : 0<u := by dsimp only [u]; positivity [modelPhaseJetCoefficient_pos hσ 2]
  have hl : 0<l := by dsimp only [l]; positivity [modelPhaseJetLower_pos hσ 2]
  have ha : 0<a := by dsimp only [a]; positivity [modelPhaseJetLower_pos hσ 3]
  have hb : 0<b := by dsimp only [b]; positivity [modelPhaseJetCoefficient_pos hσ 3]
  have hx : 0≤x := by dsimp only [x]; positivity [modelPhaseJetCoefficient_pos hσ 1]
  have hn : 1≤n := by
    have hh : 0<48/a := by positivity
    dsimp only [n]
    linarith only [hh]
  have hm : 0 < m := by dsimp only [m]; positivity
  have hq : 0≤l₀+ε := by linarith [hpair.inTriangle.2.2.1]
  obtain ⟨δ,κ₀,hδ,hκ₀,Qphase,hQphase,Cd,hCd,Cf,hCf,Cp,hCp,hsource⟩ :=
    exists_model_refined_source_bands hσ hpair hε hp
  obtain ⟨Cc,hCc,hcard⟩ := exists_displacement_cardinality_majorants hl hx
  obtain ⟨Cr,hCr,hrhs⟩ := exists_refined_uniform_frozen_rhs
    (p:=k₀+ε) (q:=l₀+ε) hl hε hCc
  obtain ⟨Ca,hCa,hpairPhysical⟩ := exists_refined_physical_pair_bound
    (p:=k₀+ε) hl ha hb.le hu hq hCp
  refine ⟨δ,κ₀,hδ,hκ₀,Qphase,hQphase,Cd,hCd,Cf*Ca*Cr,by positivity,?_⟩
  intro ι _ S F T P k H s A B w hF hT hP hw hwhalf
    U N L X hUsmall hK hbPU hLsmall hsmall hlift hκ hA hB hmul hH base hbuffer
  have hU : 0<U := by dsimp only [U]; positivity
  have hU1 : U≤1 := by linarith only [hUsmall]
  have hscale := displacement_block_physical_scale hP hU hUsmall hK
  have hblock := displacement_block_scale hU hUsmall
  have hN : 0<N := hblock.1
  have hNr : (0:ℝ)<N := Nat.cast_pos.mpr hN
  have hL : 0<L := by dsimp only [L]; positivity
  have hmargin : 0 < m*(P*Real.sqrt U) := by positivity
  have hA₀ : P<A := by linarith only [hA,hmargin]
  have hB₀ : B<2*P := by linarith only [hB,hmargin]
  have hLeq : modelPhaseJetLower σ 2*T/P^3=L := by
    dsimp only [L,l,U]; field_simp
  have hlameq : modelPhaseJetLower σ 3*T/P^4=a*U/P := by
    dsimp only [a,U]; field_simp
  have hFeq : (modelPhaseJetCoefficient σ 3+1)*T/P^4=b*U/P := by
    dsimp only [b,U]; field_simp
  have hXeq : (modelPhaseJetCoefficient σ 1+1)*T/P^2/2=X := by
    dsimp only [X,x,U]; field_simp
  have htaylor := displacement_taylor_smallness hb hP hU hUsmall hbPU
  obtain ⟨r,htail,hbands⟩ := hsource ι S F T P k H N s A B w hF hT hP hN hw hwhalf
    hA₀ hB₀ (by change 12*U≤1; linarith only [hUsmall])
    (by rw [hLeq]; exact hLsmall)
    (by rw [hFeq]; exact htaylor.1) htaylor.2 hmul hH hbuffer
  clear hsource
  rw [hLeq,hXeq] at htail
  refine ⟨r,htail,?_⟩
  intro j Q G Zd Err
  have hband := hbands j
  clear hbands
  rw [hLeq,hlameq,hFeq,hXeq] at hband
  refine ⟨hband.2.2.1,?_⟩
  intro hj hdual hfrozen
  by_cases hempty : G=∅
  · simp only [hempty,Finset.sum_empty,zero_pow (by norm_num : (12:ℕ)≠0)]
    positivity
  have hQ : 0<Q := by dsimp only [Q]; positivity
  have hQr : (0:ℝ)<Q := Nat.cast_pos.mpr hQ
  have hQ1 : (1:ℝ)≤Q := by exact_mod_cast hQ
  obtain ⟨i,hi⟩ := Finset.nonempty_iff_ne_empty.mpr hempty
  obtain ⟨hi',hlog⟩ := Finset.mem_filter.mp hi
  have hiN := (Finset.mem_filter.mp hi').2
  have hpow := Nat.pow_log_le_self 2 (r i).pos.ne'
  rw [hlog] at hpow
  have hQN : (Q:ℝ)≤2*(N:ℝ) := by
    have hh : Q≤2*N := by
      calc
        Q=2*2^j := by dsimp only [Q]; rw [pow_succ,Nat.mul_comm]
        _≤2*N := Nat.mul_le_mul_left _ (hpow.trans hiN)
    exact_mod_cast hh
  have hc := hcard P U Q hP hU hUsmall hscale.1 hQ1 hQN
  clear hcard
  have hZlo : (G.card:ℝ)≤Cc*P*U*(Q:ℝ)^2 := hband.1.trans hc.1
  have hZhi : (G.card:ℝ)≤Cc*(P/(Q:ℝ)^2)*(1+Real.log P) :=
    (hband.2.1 hj).trans hc.2
  let M : ℕ := ⌈63*U*(Q:ℝ)*(N:ℝ)^2⌉₊+1
  let lam := a*U/P
  let D₀ := (Real.sqrt M/(9*(M:ℝ))+Real.sqrt M/(12*(M:ℝ)^2))*Real.sqrt (U*(Q:ℝ)^3)
  let η := 4*D₀/(Q:ℝ)
  let rho := (12*U*Real.sqrt (U*(Q:ℝ)^3)/lam)*(Real.sqrt M/(6*(M:ℝ)^2))
  let K := ⌈3*U*(rho+1)⌉₊
  let Rmax := 36*U^2/lam
  let Dmax := (K:ℝ)/L+1
  let Dweight := 144*U^2/(lam*N)
  let E := P*U+w*(P*Real.sqrt U)+(P*U)^(k₀+ε)*(P*Real.sqrt U)^(l₀+ε)*w^(-(k₀+ε))+1/(P*U)
  let Count := Cp*((2*η+w)*Dmax+20736*(b*U/P)*U^4/(lam^2*L^2)+
    (T/P^2)^(k₀+ε)*Dmax^(l₀+ε)*w^(-(k₀+ε))+P^2/T)
  let Weight := 3*(K:ℝ)+Dweight*(harmonic K:ℝ)
  let Pair := 4*(G.card:ℝ)+6*Count*Weight
  let R := (G.card:ℝ)+(P*U*Real.sqrt U)*E*(1+Real.log P)
  have hM1 : (1:ℝ)≤M := by
    have hh : 1≤M := by dsimp only [M]; omega
    exact_mod_cast hh
  have hMscale := hblock.2.2.2.2.2 Q hQ
  have hQM : (Q:ℝ)≤4*(M:ℝ) := by
    have hh := hMscale.1
    change (7/16:ℝ)*Q≤(M:ℝ) at hh
    linarith only [hh,hQr.le]
  have hthin : (Q:ℝ)^2<6*(M:ℝ)^2 := hMscale.2.2
  have hcut := displacement_physical_cutoff ha hP hU hUsmall hK hM1 hQr hQM
  change 1≤K ∧ (K:ℝ)≤n*(P*U*Real.sqrt U) ∧ η≤4*Real.sqrt U ∧
    Dweight≤(1728/a)*(P*U*Real.sqrt U) at hcut
  obtain ⟨hlift',hleft,hright,hκ'⟩ := refined_physical_lifting_domain
    hσ hl ha (le_trans zero_le_one hn) hP hT hU hU1 rfl hK
    hcut.2.1 hcut.2.2.1 hlift hκ hA hB
  have hPair : Pair≤Ca*R := by
    have hh := hpairPhysical P U M Q G.card w hP hU hUsmall hK
      hM1 hQr hQM (by positivity) hw
    have hTP : T/P^2=P*U/u := by dsimp only [U]; field_simp
    have hPT : P^2/T=u/(P*U) := by dsimp only [U]; field_simp
    dsimp only [Pair,Count,Weight,R]
    rw [hTP,hPT]
    exact hh
  have hs := hband.2.2.2 hdual hfrozen hthin hlift' hleft hright hκ'
  have hr := hrhs P U G.card w Q hP hU hUsmall hscale.1 hsmall
    (by positivity) hw hQ (hQN.trans hscale.2.2) hZlo hZhi
  clear hband hpairPhysical hrhs
  let V := 756*U/L
  let W := 1+32/(L*(Q:ℝ)^2*N)
  let d := L*(Q:ℝ)*N/12
  let Loss := (5*W)^11*W^2*(6*(3+8*Real.pi*V)*(1+Real.log M))^12*
    (2/d)^6*(M:ℝ)^((12:ℝ)+ε)
  change _ ≤ Cf*(Loss*(2*(G.card:ℝ))^10*Pair+((G.card:ℝ)*Err)^12) at hs
  change Loss*(2*(G.card:ℝ))^10*R+((G.card:ℝ)*Err)^12≤_ at hr
  have hW0 : 0≤W := by dsimp only [W]; positivity
  have hLoss0 : 0≤Loss*(2*(G.card:ℝ))^10 :=
    mul_nonneg
      (mul_nonneg
        (mul_nonneg
          (mul_nonneg (mul_nonneg (pow_nonneg (mul_nonneg (by norm_num) hW0) 11)
            (sq_nonneg W)) ((show Even (12:ℕ) from ⟨6,rfl⟩).pow_nonneg _))
          ((show Even (6:ℕ) from ⟨3,rfl⟩).pow_nonneg _))
        (Real.rpow_nonneg (Nat.cast_nonneg M) _))
      ((show Even (10:ℕ) from ⟨5,rfl⟩).pow_nonneg _)
  have he0 : 0≤((G.card:ℝ)*Err)^12 := (show Even (12:ℕ) from ⟨6,rfl⟩).pow_nonneg _
  have habsorb : Cf*(Loss*(2*(G.card:ℝ))^10*Pair+((G.card:ℝ)*Err)^12)≤
      (Cf*Ca)*(Loss*(2*(G.card:ℝ))^10*R+((G.card:ℝ)*Err)^12) := by
    have hh := mul_le_mul_of_nonneg_left hPair hLoss0
    rw [mul_left_comm (Loss*(2*(G.card:ℝ))^10) Ca R] at hh
    have he := le_mul_of_one_le_left he0 hCa
    calc
      _ ≤ Cf*(Ca*(Loss*(2*(G.card:ℝ))^10*R+((G.card:ℝ)*Err)^12)) :=
        mul_le_mul_of_nonneg_left
          ((add_le_add hh he).trans_eq (mul_add Ca _ _).symm) hCf.le
      _ = _ := (mul_assoc _ _ _).symm
  exact hs.trans (habsorb.trans (by
    have hh := mul_le_mul_of_nonneg_left hr (show 0≤Cf*Ca by positivity)
    simpa only [mul_assoc] using hh))

/-- Sum all constructed denominator bands and the tail, preserving the actual model source. -/
theorem exists_model_refined_source_global
    {σ k₀ l₀ ε : ℝ} (hσ : 0<σ)
    (hpair : ExponentPair k₀ l₀) (hε : 0<ε) (hp : k₀+ε<1) :
    let u := modelPhaseJetCoefficient σ 2+1
    let l := modelPhaseJetLower σ 2/u
    let a := modelPhaseJetLower σ 3/u
    let b := (modelPhaseJetCoefficient σ 3+1)/u
    let n := 2+48/a
    let m := 36/a+2*(n/l+1)+1
    ∃ δ κ₀ : ℝ, 0<δ ∧ 0<κ₀ ∧
      ∃ Qphase : ℕ, 3≤Qphase ∧ ∃ C > (0:ℝ),
      ∀ (ι : Type*) [DecidableEq ι] (S : Finset ι) (F : ℝ→ℝ)
        (T P : ℝ) (k : ι→ℤ) (H : ι→ℕ) (s : ℤ) (A B w : ℝ),
      IsApproximateModelPhaseFunction F σ Qphase δ →
      0<T → 0<P → 0<w → w≤1/2 →
      let U := u*T/P^3
      let N := ⌊1/(10*Real.sqrt U)⌋₊
      U≤1/3600 → 1≤P*U*Real.sqrt U → b≤P*U → l*U≤1 →
      P*U^2≤1 → 8*Real.sqrt U+(10368*b/(a^2*l))*(P*U^2)≤1/2 →
      (2*n*u/σ)*Real.sqrt U≤κ₀ →
      P+m*(P*Real.sqrt U)<A → B+m*(P*Real.sqrt U)<2*P →
      (∀ j : ℤ, (S.filter (fun i => k i=j)).card≤1) →
      (∀ i∈S, H i≤N) →
      let base := fun i => (s:ℝ)-2*(N:ℝ)+(N:ℝ)*(k i:ℝ)
      (∀ i∈S, Icc (base i-(7*(N:ℝ)+2)) (base i+(7*(N:ℝ)+2))⊆Icc A B) →
      (1+23*(N:ℝ)+∑ i∈S,
        ‖∑ t∈Finset.Ioc (s+(N:ℤ)*k i) (s+(N:ℤ)*k i+H i),
          (𝐞 (T*F ((t:ℝ)/P)):ℂ)‖)^12 ≤
        C*P^ε*(1+Real.log P)^36*(P^11*U+w*P^12*U^((5:ℝ)/2)+P^(11+(k₀+ε)+(l₀+ε))*U^(2+(k₀+ε)+(l₀+ε)/2)*w^(-(k₀+ε))) := by
  classical
  intro u l a b n m
  let x := (modelPhaseJetCoefficient σ 1+1)/(2*u)
  have hu : 0<u := by dsimp only [u]; positivity [modelPhaseJetCoefficient_pos hσ 2]
  have hl : 0<l := by dsimp only [l]; positivity [modelPhaseJetLower_pos hσ 2]
  have hx : 0≤x := by dsimp only [x]; positivity [modelPhaseJetCoefficient_pos hσ 1]
  obtain ⟨δ,κ₀,hδ,hκ₀,Qphase,hQphase,Cd,hCd,Cf,hCf,hsource⟩ :=
    exists_model_uniform_refined_source_bands hσ hpair hε hp
  obtain ⟨K,hK,hcutoff⟩ := exists_displacement_small_band_cutoff hl
  obtain ⟨Cs,hCs,hsmall⟩ := exists_displacement_small_band_majorant hl hx hK
  obtain ⟨Ct,hCt,htailSize⟩ := exists_displacement_tail_majorant hl hx
  let C₀ := (24:ℝ)^12+Ct^12+Cf+(Cd*Cs)^12
  have hC₀ : 0 < C₀ := by dsimp only [C₀]; positivity
  refine ⟨δ,κ₀,hδ,hκ₀,Qphase,hQphase,1000^12*C₀,by positivity,?_⟩
  intro ι _ S F T P k H s A B w hF hT hP hw₀ hwhalf U N
    hUsmall hKscale hbPU hLsmall hsmall₀ hlift hκ hA hB hmul hH base hbuffer
  let L := l*U
  let X := x*P*U
  let f := fun t => T*F (t/P)
  have hU : 0<U := by dsimp only [U]; positivity
  have hscale := displacement_block_physical_scale hP hU hUsmall hKscale
  have hU1 : U ≤ 1 := by linarith only [hUsmall]
  have hN := (displacement_block_scale hU hUsmall).1
  obtain ⟨r,htail,hband⟩ := hsource ι S F T P k H s A B w hF hT hP hw₀ hwhalf
    hUsmall hKscale hbPU hLsmall hsmall₀ hlift hκ hA hB hmul hH hbuffer
  let weight := fun i => ‖∑ n∈Finset.Ioc (s+(N:ℤ)*k i) (s+(N:ℤ)*k i+H i),(𝐞 (f n):ℂ)‖
  let R := S.filter (fun i => N+1 ≤ (r i).den)
  let g := fun j => ∑ i∈(S.filter (fun i => (r i).den ≤ N)).filter (fun i => Nat.log 2 (r i).den=j),weight i
  let J := Nat.log 2 N+1
  let Log := 1+Real.log P
  let E := P^11*U+w*P^12*U^((5:ℝ)/2)+P^(11+(k₀+ε)+(l₀+ε))*U^(2+(k₀+ε)+(l₀+ε)/2)*w^(-(k₀+ε))
  let Budget := C₀*P^ε*Log^24*E
  have hlog1 : 1 ≤ Log := by
    have hh := Real.log_nonneg hscale.2.1
    dsimp only [Log]
    linarith only [hh]
  have hLog : 0 < Log := lt_of_lt_of_le zero_lt_one hlog1
  have hE : 0 ≤ E := by dsimp only [E]; positivity
  have hFirst : P^11*U≤E := by
    have hmid : 0≤w*P^12*U^((5:ℝ)/2) := by positivity
    have hlast : 0≤P^(11+(k₀+ε)+(l₀+ε))*U^(2+(k₀+ε)+(l₀+ε)/2)*w^(-(k₀+ε)) := by positivity
    dsimp only [E]
    linarith only [hmid,hlast]
  have hbudget (c : ℝ) (hc : c ≤ C₀) : c*P^ε*Log^24*E ≤ Budget := by
    dsimp only [Budget]
    gcongr
  have hbaseBudget (c : ℝ) (hc0 : 0≤c) (hc : c≤C₀) :
      c*P^ε*Log^24*(P^11*U)≤Budget :=
    (mul_le_mul_of_nonneg_left hFirst (by positivity)).trans (hbudget c hc)
  have hCdp : 0 ≤ Cd := by linarith only [hCd]
  have hCf₀ : Cf ≤ C₀ := by
    dsimp only [C₀]
    linarith only [pow_nonneg hCt.le 12,pow_nonneg (mul_nonneg hCdp hCs.le) 12]
  have hCs₀ : (Cd*Cs)^12 ≤ C₀ := by
    dsimp only [C₀]
    linarith only [hCf.le,pow_nonneg hCt.le 12]
  have hCt₀ : Ct^12 ≤ C₀ := by
    dsimp only [C₀]
    linarith only [hCf.le,pow_nonneg (mul_nonneg hCdp hCs.le) 12]
  have hCb₀ : (24:ℝ)^12 ≤ C₀ := by
    dsimp only [C₀]
    linarith only [hCf.le,pow_nonneg hCt.le 12,pow_nonneg (mul_nonneg hCdp hCs.le) 12]
  have hw (i : ι) : 0 ≤ weight i := norm_nonneg _
  have hwH (i : ι) (hi : i∈S) : weight i ≤ N := by
    have hh := norm_sum_integer_Ioc_le (fun n => (𝐞 (f n):ℂ)) (by intro n; simp)
      (a:=s+(N:ℤ)*k i) (b:=s+(N:ℤ)*k i+H i) (by omega)
    have he : ((s+(N:ℤ)*k i+H i:ℤ):ℝ)-(s+(N:ℤ)*k i:ℤ)=H i := by push_cast; ring
    rw [he] at hh
    exact hh.trans (Nat.cast_le.mpr (hH i hi))
  have htail' : (∑ i∈R,weight i) ≤ Ct*P*Real.sqrt U := by
    have hq0 : 2 ≤ N+1 := by omega
    have hc := htail (N+1) hq0
    have hs : (∑ i∈R,weight i) ≤ (R.card:ℝ)*(N:ℝ) := by
      calc
        _ ≤ ∑ _i∈R,(N:ℝ) := Finset.sum_le_sum (fun i hi => hwH i (Finset.mem_filter.mp hi).1)
        _ = _ := by simp
    have hm := mul_le_mul_of_nonneg_left hc (show 0 ≤ (N:ℝ) by positivity)
    have hsize := (htailSize P U hP hU hUsmall hscale.1).2
    simp only [Nat.cast_add,Nat.cast_one] at hm
    change (N:ℝ)*(R.card:ℝ) ≤ _ at hm
    exact hs.trans (by
      calc
        _ = (N:ℝ)*(R.card:ℝ) := by ring
        _ ≤ _ := hm
        _ ≤ _ := hsize)
  have htailMoment : (∑ i∈R,weight i)^12 ≤ Budget := by
    have hh : (∑ i∈R,weight i) ≤ Ct*P*U^((1:ℝ)/2)*Log^2 := by
      rw [←Real.sqrt_eq_rpow]
      exact htail'.trans (le_mul_of_one_le_right (by positivity) (one_le_pow₀ hlog1))
    exact (refined_elementary_twelfth hscale.2.1 hU hU1 (Finset.sum_nonneg (fun i _ => hw i))
      hCt.le hlog1 hε.le (by norm_num : (1:ℝ)/4 ≤ 1/2) hsmall₀ hh).trans (hbaseBudget _ (by positivity) hCt₀)
  have hboundary : (1+23*(N:ℝ))^12 ≤ Budget := by
    have hh : 1+23*(N:ℝ) ≤ 24*P*U^((1:ℝ)/2)*Log^2 := by
      rw [←Real.sqrt_eq_rpow]
      exact (htailSize P U hP hU hUsmall hscale.1).1.trans
        (le_mul_of_one_le_right (by positivity) (one_le_pow₀ hlog1))
    exact (refined_elementary_twelfth hscale.2.1 hU hU1 (by positivity)
      (by norm_num : (0:ℝ)≤24) hlog1 hε.le (by norm_num : (1:ℝ)/4 ≤ 1/2) hsmall₀ hh).trans
        (hbaseBudget _ (by positivity) hCb₀)
  have hbands (j : ℕ) : (g j)^12 ≤ Budget := by
    let Q : ℕ := 2^(j+1)
    have hQ1 : (1:ℝ) ≤ Q := by dsimp only [Q]; exact_mod_cast (one_le_pow₀ (by norm_num : (1:ℕ) ≤ 2) : 1 ≤ 2^(j+1))
    have hQ : (0:ℝ) < Q := lt_of_lt_of_le zero_lt_one hQ1
    by_cases hlarge : 1 ≤ j ∧ 12 ≤ L*(Q:ℝ)*(N:ℝ)^2 ∧ 384 ≤ L^2*(Q:ℝ)^3*(N:ℝ)^3
    · exact ((hband j).2 hlarge.1 hlarge.2.1 hlarge.2.2).trans (hbudget _ hCf₀)
    have hcases : (Q:ℝ) ≤ 2 ∨ l*U*(Q:ℝ)*(N:ℝ)^2 < 12 ∨ (l*U)^2*(Q:ℝ)^3*(N:ℝ)^3 < 384 := by
      by_cases hj : 1 ≤ j
      · by_cases hd : 12 ≤ L*(Q:ℝ)*(N:ℝ)^2
        · exact Or.inr (Or.inr (lt_of_not_ge (fun hh => hlarge ⟨hj,hd,hh⟩)))
        · exact Or.inr (Or.inl (lt_of_not_ge hd))
      · have hj0 : j=0 := by omega
        left
        simp only [Q,hj0,zero_add,pow_one,Nat.cast_ofNat,le_refl]
    have hcut := hcutoff U Q hU hUsmall hQ hcases
    have hs := hsmall P U Q hP hU hUsmall hscale.1 hQ1 hcut
    have hm := mul_le_mul_of_nonneg_left hs (show 0 ≤ Cd by linarith only [hCd])
    have hg : g j ≤ (Cd*Cs)*P*U^((1:ℝ)/3)*Log := by
      calc
        _ ≤ _ := (hband j).1
        _ ≤ _ := by convert hm using 1 <;> ring
    have hg' : g j≤(Cd*Cs)*P*U^((1:ℝ)/3)*Log^2 :=
      hg.trans (by
        have hh : Log≤Log^2 := by nlinarith only [hlog1]
        gcongr)
    exact (refined_elementary_twelfth hscale.2.1 hU hU1 (Finset.sum_nonneg (fun i _ => hw i))
      (mul_nonneg hCdp hCs.le) hlog1 hε.le (by norm_num : (1:ℝ)/4 ≤ 1/3) hsmall₀ hg').trans
        (hbaseBudget _ (by positivity) hCs₀)
  have hfinite := displacement_finite_moment_budget g J (by positivity)
    (Finset.sum_nonneg (fun i _ => hw i)) (fun j => Finset.sum_nonneg (fun i _ => hw i))
    hboundary htailMoment (fun j _ => hbands j)
  have hJbound : (J:ℝ)+2 ≤ 1000*Log :=
    (physical_dyadic_geometry (by norm_num : (1000:ℝ) ≤ 1000) hscale.2.1 hN
      (by linarith only [hscale.2.2,show (0:ℝ) ≤ N by positivity])).1
  change (1+23*(N:ℝ)+∑ i∈S,weight i)^12 ≤ _
  rw [sum_by_denominator_bands S (fun i => (r i).den) weight N]
  change (1+23*(N:ℝ)+((∑ i∈R,weight i)+∑ j∈Finset.range J,g j))^12 ≤ _
  calc
    _ = (1+23*(N:ℝ)+(∑ i∈R,weight i)+∑ j∈Finset.range J,g j)^12 := by congr 1; ring
    _ ≤ ((J:ℝ)+2)^12*Budget := hfinite
    _ ≤ (1000*Log)^12*Budget := mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ (by positivity) hJbound 12) (by dsimp only [Budget]; positivity)
    _ = (1000^12*C₀)*P^ε*(1+Real.log P)^36*(P^11*U+w*P^12*U^((5:ℝ)/2)+P^(11+(k₀+ε)+(l₀+ε))*U^(2+(k₀+ε)+(l₀+ε)/2)*w^(-(k₀+ε))) := by
      change _ = (1000^12*C₀)*P^ε*Log^36*E
      dsimp only [Budget]
      ring

/-- Closed-source trimming preserves both endpoints and charges every removed term. -/
theorem refined_integer_source_trim
    (g : ℤ→ℂ) (hg : ∀ n, ‖g n‖≤1) {a b : ℤ} {K : ℕ}
    (hab : a+2*(K:ℤ)≤b) :
    ‖∑ n∈Finset.Icc a b,g n‖≤
      ‖∑ n∈Finset.Ioc (a+K) (b-K),g n‖+2*(K:ℝ)+1 := by
  have hlo : a≤a+K := by omega
  have hmid : a+(K:ℤ)≤b-K := by omega
  have hhi : b-(K:ℤ)≤b := by omega
  rw [←Finset.add_sum_Ioc_eq_sum_Icc (show a≤b by omega)]
  rw [sargos_integer_Ioc_sum_split g hlo (hmid.trans hhi),
    sargos_integer_Ioc_sum_split g hmid hhi]
  have hleft := norm_sum_integer_Ioc_le g hg hlo
  have hright := norm_sum_integer_Ioc_le g hg hhi
  have hnorm₁ := norm_add_le (g a)
    ((∑ n∈Finset.Ioc a (a+K),g n)+
      ((∑ n∈Finset.Ioc (a+K) (b-K),g n)+(∑ n∈Finset.Ioc (b-K) b,g n)))
  have hnorm₂ := norm_add_le (∑ n∈Finset.Ioc a (a+K),g n)
    ((∑ n∈Finset.Ioc (a+K) (b-K),g n)+(∑ n∈Finset.Ioc (b-K) b,g n))
  have hnorm₃ := norm_add_le (∑ n∈Finset.Ioc (a+K) (b-K),g n)
    (∑ n∈Finset.Ioc (b-K) b,g n)
  push_cast at hleft hright
  linarith only [hnorm₁,hnorm₂,hnorm₃,hleft,hright,hg a]

/-- The refined estimate reaches the literal closed original source sum.
Short intervals and the two removed endpoint strips are included. -/
theorem exists_model_refined_global_bound
    {σ k₀ l₀ ε : ℝ} (hσ : 0<σ)
    (hpair : ExponentPair k₀ l₀) (hε : 0<ε) (hp : k₀+ε<1) :
    let u := modelPhaseJetCoefficient σ 2+1
    let l := modelPhaseJetLower σ 2/u
    let a := modelPhaseJetLower σ 3/u
    let b := (modelPhaseJetCoefficient σ 3+1)/u
    let n := 2+48/a
    ∃ δ κ₀ : ℝ, 0<δ ∧ 0<κ₀ ∧
      ∃ Qphase : ℕ, 3≤Qphase ∧ ∃ C > (0:ℝ),
      ∀ (F : ℝ→ℝ) (T P : ℝ) (aa bb : ℕ) (w : ℝ),
      IsApproximateModelPhaseFunction F σ Qphase δ →
      0<T → 0<P → P≤aa → (bb:ℝ)≤2*P → 0<w → w≤1/2 →
      let U := u*T/P^3
      U≤1/3600 → 1≤P*U*Real.sqrt U → b≤P*U → l*U≤1 →
      P*U^2≤1 → 8*Real.sqrt U+(10368*b/(a^2*l))*(P*U^2)≤1/2 →
      (2*n*u/σ)*Real.sqrt U≤κ₀ →
      ‖exponentialSumAt F T P aa bb‖^12 ≤
        C*P^ε*(1+Real.log P)^36*
          (P^11*U+w*P^12*U^((5:ℝ)/2)+
            P^(11+(k₀+ε)+(l₀+ε))*U^(2+(k₀+ε)+(l₀+ε)/2)*w^(-(k₀+ε))) := by
  classical
  intro u l a b n
  let m := 36/a+2*(n/l+1)+1
  have hu : 0<u := by dsimp only [u]; positivity [modelPhaseJetCoefficient_pos hσ 2]
  have hl : 0<l := by dsimp only [l]; positivity [modelPhaseJetLower_pos hσ 2]
  have ha : 0<a := by dsimp only [a]; positivity [modelPhaseJetLower_pos hσ 3]
  have hn : 0<n := by dsimp only [n]; positivity
  have hm : 0 < m := by dsimp only [m]; positivity
  obtain ⟨δ,κ₀,hδ,hκ₀,Qphase,hQphase,Cf,hCf,hsource⟩ :=
    exists_model_refined_source_global hσ hpair hε hp
  let Ctrim := 2*m+3
  have hCtrim : 0<Ctrim := by dsimp only [Ctrim]; positivity
  let C := 2^11*(Cf+Ctrim^12)
  have hC : 0<C := by dsimp only [C]; positivity
  refine ⟨δ,κ₀,hδ,hκ₀,Qphase,hQphase,C,hC,?_⟩
  intro F T P aa bb w hF hT hP haa hbb hw hwhalf U
    hUsmall hKscale hbPU hLsmall hsmall hlift hκ
  have hU : 0<U := by dsimp only [U]; positivity
  have hU1 : U≤1 := by linarith only [hUsmall]
  have hscale := displacement_block_physical_scale hP hU hUsmall hKscale
  let N := ⌊1/(10*Real.sqrt U)⌋₊
  have hN : 0<N := (displacement_block_scale hU hUsmall).1
  let K := ⌈m*(P*Real.sqrt U)⌉₊
  let E := P^11*U+w*P^12*U^((5:ℝ)/2)+
    P^(11+(k₀+ε)+(l₀+ε))*U^(2+(k₀+ε)+(l₀+ε)/2)*w^(-(k₀+ε))
  let Log := 1+Real.log P
  let Budget := P^ε*Log^36*E
  have hLog1 : 1≤Log := by
    have hh := Real.log_nonneg hscale.2.1
    dsimp only [Log]
    linarith only [hh]
  have hLog : 0<Log := zero_lt_one.trans_le hLog1
  have hE : 0≤E := by dsimp only [E]; positivity
  have hBudget : 0≤Budget := by dsimp only [Budget]; positivity
  have hFirst : P^11*U≤E := by
    have hmid : 0≤w*P^12*U^((5:ℝ)/2) := by positivity
    have hlast : 0≤P^(11+(k₀+ε)+(l₀+ε))*U^(2+(k₀+ε)+(l₀+ε)/2)*w^(-(k₀+ε)) := by positivity
    dsimp only [E]
    linarith only [hmid,hlast]
  have hPS : 1≤P*Real.sqrt U := hKscale.trans (by
    calc
      _ ≤ P*1*Real.sqrt U := by gcongr
      _ = _ := by ring)
  have hKlo : m*(P*Real.sqrt U)≤(K:ℝ) := Nat.le_ceil _
  have hKhi : (K:ℝ) ≤ m*(P*Real.sqrt U)+1 :=
    (Nat.ceil_lt_add_one (show 0 ≤ m*(P*Real.sqrt U) by positivity)).le
  have htrimBound : 2*(K:ℝ)+1≤Ctrim*P*Real.sqrt U := by
    dsimp only [Ctrim]
    nlinarith only [hKhi,hPS]
  have htrimMoment : (2*(K:ℝ)+1)^12≤Ctrim^12*Budget := by
    have hh : 2*(K:ℝ)+1≤Ctrim*P*U^((1:ℝ)/2)*Log^2 := by
      rw [←Real.sqrt_eq_rpow]
      exact htrimBound.trans (le_mul_of_one_le_right (by positivity) (one_le_pow₀ hLog1))
    have he := refined_elementary_twelfth hscale.2.1 hU hU1 (by positivity)
      hCtrim.le hLog1 hε.le (by norm_num : (1:ℝ)/4≤1/2) hsmall hh
    calc
      _ ≤ Ctrim^12*P^ε*Log^24*(P^11*U) := he
      _ ≤ Ctrim^12*P^ε*Log^36*E := by gcongr; norm_num
      _ = _ := by simp only [Budget,mul_assoc]
  by_cases hlong : aa+2*K≤bb
  · let A : ℤ := (aa:ℤ)+K
    let B : ℤ := (bb:ℤ)-K
    let g := fun t : ℤ => (𝐞 (T*F ((t:ℝ)/P)):ℂ)
    have hg (t : ℤ) : ‖g t‖≤1 := by dsimp only [g]; simp
    have hAB : A≤B := by dsimp only [A,B]; omega
    obtain ⟨S,hbuffer,_,hblocks⟩ := exists_buffered_integer_source_blocks_interval g hg
      hAB (le_refl (A:ℝ)) (le_refl (B:ℝ)) N hN
    have hmul (j : ℤ) : (S.filter (fun k : ℕ => (k:ℤ)=j)).card≤1 := by
      apply Finset.card_le_one.mpr
      intro v hv z hz
      have hv' := (Finset.mem_filter.mp hv).2
      have hz' := (Finset.mem_filter.mp hz).2
      exact_mod_cast hv'.trans hz'.symm
    have hA : P+m*(P*Real.sqrt U)<(A:ℝ)+1/2 := by
      dsimp only [A]
      push_cast
      linarith only [haa,hKlo]
    have hB : (B:ℝ)-1/2+m*(P*Real.sqrt U)<2*P := by
      dsimp only [B]
      push_cast
      linarith only [hbb,hKlo]
    have hs := hsource ℕ S F T P (fun k => (k:ℤ)) (fun _ => N) A
      ((A:ℝ)+1/2) ((B:ℝ)-1/2) w hF hT hP hw hwhalf
      hUsmall hKscale hbPU hLsmall hsmall hlift hκ hA hB hmul (fun _ _ => le_rfl)
      (by simpa only [Int.cast_natCast] using hbuffer)
    let Core := 1+23*(N:ℝ)+∑ k∈S, ‖∑ t∈Finset.Ioc (A+(N:ℤ)*k) (A+(N:ℤ)*k+N),g t‖
    have hCore : 0≤Core := by dsimp only [Core]; positivity
    change Core^12≤Cf*P^ε*Log^36*E at hs
    have hs' : Core^12≤Cf*Budget := by simpa only [Budget,mul_assoc] using hs
    have ht := refined_integer_source_trim g hg (a:=(aa:ℤ)) (b:=(bb:ℤ)) (K:=K)
      (by exact_mod_cast hlong)
    have hnorm : ‖exponentialSumAt F T P aa bb‖≤Core+(2*(K:ℝ)+1) := by
      rw [exponentialSumAt_eq_int_sum]
      change ‖∑ t∈Finset.Icc (aa:ℤ) (bb:ℤ),g t‖≤_
      change ‖∑ t∈Finset.Icc (aa:ℤ) (bb:ℤ),g t‖≤‖∑ t∈Finset.Ioc A B,g t‖+2*(K:ℝ)+1 at ht
      dsimp only [Core]
      linarith only [ht,hblocks]
    have hp₀ := (pow_le_pow_left₀ (norm_nonneg _) hnorm 12).trans
      (add_pow_le hCore (by positivity : 0≤2*(K:ℝ)+1) 12)
    have hm := mul_le_mul_of_nonneg_left (add_le_add hs' htrimMoment)
      (show (0:ℝ)≤2^(12-1) by positivity)
    exact hp₀.trans (by
      rw [←add_mul,←mul_assoc] at hm
      simpa only [C,Budget,Log,E,mul_assoc,Nat.reduceSub] using hm)
  · have hnorm : ‖exponentialSumAt F T P aa bb‖≤2*(K:ℝ)+1 := by
      have hc : ((Finset.Icc aa bb).card:ℝ)≤2*(K:ℝ)+1 := by
        have hh : (Finset.Icc aa bb).card≤2*K+1 := by rw [Nat.card_Icc]; omega
        exact_mod_cast hh
      exact (norm_exponentialSumAt_le_card F T P aa bb).trans hc
    have hCtrimC : Ctrim^12≤C := by
      exact (le_add_of_nonneg_left hCf.le).trans
        (le_mul_of_one_le_left (by positivity) (by norm_num : (1:ℝ)≤2^11))
    exact ((pow_le_pow_left₀ (norm_nonneg _) hnorm 12).trans htrimMoment).trans
      (by
        simpa only [Budget,Log,E,mul_assoc] using mul_le_mul_of_nonneg_right hCtrimC hBudget)

/-- All physical smallness and lifting conditions follow on the strict refined range. -/
theorem eventually_refined_bourgain_parameters
    {T P : VariableObject ℝ} {α σ κ₀ : ℝ}
    (hlo : 2/5<α) (hhi : α<3/7) (hσ : 0<σ) (hκ₀ : 0<κ₀)
    (hT : ∀ i, 1≤T i) (hTunbounded : T.IsUnbounded)
    (hPT : IsPowerAsymptotic P T α) :
    let u := modelPhaseJetCoefficient σ 2+1
    let l := modelPhaseJetLower σ 2/u
    let a := modelPhaseJetLower σ 3/u
    let b := (modelPhaseJetCoefficient σ 3+1)/u
    let n := 2+48/a
    let U := fun i => u*T i/(P i)^3
    let w := fun i => (T i)^(-(3+23*α)/194)
    ∀ᶠ i in atTop, 0<P i ∧ 0<w i ∧ w i≤1/2 ∧ U i≤1/3600 ∧
      1≤P i*U i*Real.sqrt (U i) ∧ b≤P i*U i ∧ l*U i≤1 ∧
      P i*(U i)^2≤1 ∧
      8*Real.sqrt (U i)+(10368*b/(a^2*l))*(P i*(U i)^2)≤1/2 ∧
      (2*n*u/σ)*Real.sqrt (U i)≤κ₀ := by
  intro u l a b n U w
  have hu : 0<u := by dsimp only [u]; positivity [modelPhaseJetCoefficient_pos hσ 2]
  have hTscale := isPowerAsymptotic_self T
  have hc (c : ℝ) (hc : 0<c) := cubic_power_const hT hTunbounded hc
  let v := 1-3*α
  let omegaScale := -(3+23*α)/194
  have hv : v<0 := by dsimp only [v]; linarith only [hlo]
  have homegaScale : omegaScale<0 := by dsimp only [omegaScale]; linarith only [hlo]
  have hU : IsPowerAsymptotic U T v := by
    convert ((hc u hu).mul hTscale hT).div (cubic_power_natpow hPT hT 3) hT using 1
    ring
  have hroot : IsPowerAsymptotic (fun i => Real.sqrt (U i)) T (v/2) := by
    simpa only [Real.sqrt_eq_rpow,mul_one_div] using cubic_power_rpow hU hT ((1:ℝ)/2)
  have hPU : IsPowerAsymptotic (fun i => P i*U i) T (α+v) := hPT.mul hU hT
  have hcurve : IsPowerAsymptotic (fun i => P i*U i*Real.sqrt (U i)) T (α+v+v/2) :=
    hPU.mul hroot hT
  have hlifting : IsPowerAsymptotic (fun i => P i*(U i)^2) T (α+2*v) := by
    convert hPT.mul (cubic_power_natpow hU hT 2) hT using 1
    ring
  have hw : IsPowerAsymptotic w T omegaScale := by
    simpa using cubic_power_rpow hTscale hT omegaScale
  have hPpos := (hPT.tendsto_atTop_of_pos (by linarith only [hlo] : 0<α)
    hT hTunbounded).eventually (eventually_gt_atTop 0)
  have hUzero := hU.tendsto_zero_of_neg hv hT hTunbounded
  have hrootzero := hroot.tendsto_zero_of_neg (by linarith only [hv]) hT hTunbounded
  have hliftzero := hlifting.tendsto_zero_of_neg
    (by dsimp only [v]; linarith only [hlo] : α+2*v<0) hT hTunbounded
  have hsmall := hUzero.eventually (eventually_lt_nhds (by norm_num : (0:ℝ)<1/3600))
  have hwsmall := (hw.tendsto_zero_of_neg homegaScale hT hTunbounded).eventually
    (eventually_lt_nhds (by norm_num : (0:ℝ)<1/2))
  have hcurveLarge := (hcurve.tendsto_atTop_of_pos
    (by dsimp only [v]; linarith only [hhi] : 0<α+v+v/2) hT hTunbounded).eventually
    (eventually_ge_atTop 1)
  have hPULarge := (hPU.tendsto_atTop_of_pos
    (by dsimp only [v]; linarith only [hhi] : 0<α+v) hT hTunbounded).eventually
    (eventually_ge_atTop b)
  have hLsmall := (hUzero.const_mul l).eventually
    (by simpa using (eventually_lt_nhds (by norm_num : (0:ℝ)<1)))
  have hLiftSmall := hliftzero.eventually (eventually_lt_nhds (by norm_num : (0:ℝ)<1))
  have hsourceLift := ((hrootzero.const_mul 8).add
    (hliftzero.const_mul (10368*b/(a^2*l)))).eventually
      (by simpa using (eventually_lt_nhds (by norm_num : (0:ℝ)<1/2)))
  have hshift := (hrootzero.const_mul (2*n*u/σ)).eventually
    (by simpa using (eventually_lt_nhds hκ₀))
  filter_upwards [hPpos,hwsmall,hsmall,hcurveLarge,hPULarge,hLsmall,hLiftSmall,hsourceLift,hshift]
    with i hPi hwi hUi hci hpui hli hlifti hsi hki
  exact ⟨hPi,Real.rpow_pos_of_pos (zero_lt_one.trans_le (hT i)) _,
    hwi.le,hUi.le,hci,hpui,hli.le,hlifti.le,by simpa only [one_div] using hsi.le,hki.le⟩

/-- The exact refined physical cost has the claimed two-piece beta exponent. -/
theorem eventually_refined_bourgain_cost
    {T P : VariableObject ℝ} {α σ η : ℝ}
    (hlo : 2/5<α) (hhi : α<3/7) (hσ : 0<σ) (hη : 0<η)
    (hT : ∀ i, 1≤T i) (hTunbounded : T.IsUnbounded)
    (hPT : IsPowerAsymptotic P T α) :
    let u := modelPhaseJetCoefficient σ 2+1
    let U := fun i => u*T i/(P i)^3
    let w := fun i => (T i)^(-(3+23*α)/194)
    let β := max (1/12+2*α/3) (241/1164+425*α/1164)
    ∀ᶠ i in atTop,
      (P i)^η*(1+Real.log (P i))^36*
        ((P i)^11*U i+w i*(P i)^12*(U i)^((5:ℝ)/2)+
          (P i)^(11+(13/84+η)+(55/84+η))*
            (U i)^(2+(13/84+η)+(55/84+η)/2)*(w i)^(-(13/84+η))) ≤
        3*(T i)^(12*β+5*η) := by
  intro u U w β
  have hu : 0<u := by dsimp only [u]; positivity [modelPhaseJetCoefficient_pos hσ 2]
  let v := 1-3*α
  let omegaScale := -(3+23*α)/194
  let β₁ := 1/12+2*α/3
  let β₂ := 241/1164+425*α/1164
  have hβ₁ : β₁≤β := le_max_left _ _
  have hβ₂ : β₂≤β := le_max_right _ _
  have hα1 : α<1 := by linarith only [hhi]
  have hcoef : 3*α+3*v/2-omegaScale≤3 := by dsimp only [v,omegaScale]; linarith only [hlo,hhi]
  have hc (c : ℝ) (hc : 0<c) := cubic_power_const hT hTunbounded hc
  have hTscale := isPowerAsymptotic_self T
  have hU : IsPowerAsymptotic U T v := by
    convert ((hc u hu).mul hTscale hT).div (cubic_power_natpow hPT hT 3) hT using 1
    ring
  have hw : IsPowerAsymptotic w T omegaScale := by simpa using cubic_power_rpow hTscale hT omegaScale
  let g₁ := fun i => (P i)^η*((P i)^11*U i)
  let g₂ := fun i => (P i)^η*(w i*(P i)^12*(U i)^((5:ℝ)/2))
  let g₃ := fun i => (P i)^η*((P i)^(11+(13/84+η)+(55/84+η))*
    (U i)^(2+(13/84+η)+(55/84+η)/2)*(w i)^(-(13/84+η)))
  have hg₁ : IsPowerAsymptotic g₁ T (α*η+(α*11+v)) :=
    (cubic_power_rpow hPT hT η).mul ((cubic_power_natpow hPT hT 11).mul hU hT) hT
  have hg₂ : IsPowerAsymptotic g₂ T (α*η+(omegaScale+α*12+v*(5/2))) :=
    (cubic_power_rpow hPT hT η).mul
      ((hw.mul (cubic_power_natpow hPT hT 12) hT).mul (cubic_power_rpow hU hT (5/2)) hT) hT
  have hg₃ : IsPowerAsymptotic g₃ T
      (α*η+(α*(11+(13/84+η)+(55/84+η))+v*(2+(13/84+η)+(55/84+η)/2)+omegaScale*(-(13/84+η)))) :=
    (cubic_power_rpow hPT hT η).mul
      (((cubic_power_rpow hPT hT _).mul (cubic_power_rpow hU hT _) hT).mul
        (cubic_power_rpow hw hT _) hT) hT
  have hexp₁ : α*η+(α*11+v)<12*β+4*η := by
    have hid : α*η+(α*11+v)=12*β₁+η*α := by dsimp only [v,β₁]; ring
    rw [hid]
    have hh := mul_le_mul_of_nonneg_left hα1.le hη.le
    linarith only [hh,hβ₁,hη]
  have hexp₂ : α*η+(omegaScale+α*12+v*(5/2))<12*β+4*η := by
    have hid : α*η+(omegaScale+α*12+v*(5/2))=12*β₂+η*α := by dsimp only [v,omegaScale,β₂]; ring
    rw [hid]
    have hh := mul_le_mul_of_nonneg_left hα1.le hη.le
    linarith only [hh,hβ₂,hη]
  have hexp₃ :
      α*η+(α*(11+(13/84+η)+(55/84+η))+v*(2+(13/84+η)+(55/84+η)/2)+omegaScale*(-(13/84+η)))<
        12*β+4*η := by
    have hid : α*η+(α*(11+(13/84+η)+(55/84+η))+v*(2+(13/84+η)+(55/84+η)/2)+omegaScale*(-(13/84+η)))=
        12*β₂+η*(3*α+3*v/2-omegaScale) := by dsimp only [v,omegaScale,β₂]; ring
    rw [hid]
    have hh := mul_le_mul_of_nonneg_left hcoef hη.le
    linarith only [hh,hβ₂,hη]
  have hb₁ := cubic_power_eventually_le hg₁ hT hexp₁
  have hb₂ := cubic_power_eventually_le hg₂ hT hexp₂
  have hb₃ := cubic_power_eventually_le hg₃ hT hexp₃
  have hP1 := (hPT.tendsto_atTop_of_pos (by linarith only [hlo] : 0<α)
    hT hTunbounded).eventually (eventually_ge_atTop 1)
  have hPTle := cubic_power_eventually_le hPT hT hα1
  have hTtop : Tendsto T atTop atTop :=
    (VariableObject.isUnbounded_iff_tendsto_atTop (fun i => zero_le_one.trans (hT i))).mp hTunbounded
  have hlogT := (Real.tendsto_log_atTop.comp hTtop).eventually (eventually_ge_atTop 1)
  have hlogPower := hTtop.eventually
    (eventually_const_log_pow_le_rpow ((2:ℝ)^36) (by positivity) 36 hη)
  filter_upwards [hb₁,hb₂,hb₃,hP1,hPTle,hlogT,hlogPower] with i hi₁ hi₂ hi₃ hPi hPTi hlogi hlogPoweri
  have hTi : 0<T i := zero_lt_one.trans_le (hT i)
  have hPp : 0<P i := zero_lt_one.trans_le hPi
  have hlogP := Real.log_nonneg hPi
  change 1≤Real.log (T i) at hlogi
  have hlog : (1+Real.log (P i))^36≤(T i)^η := by
    have hlogPT : Real.log (P i)≤Real.log (T i) := by
      apply Real.log_le_log hPp
      simpa only [Real.rpow_one] using hPTi
    calc
      _ ≤ (2*Real.log (T i))^36 :=
        pow_le_pow_left₀ (by positivity) (by linarith only [hlogPT,hlogi]) 36
      _ = (2:ℝ)^36*(Real.log (T i))^36 := mul_pow _ _ _
      _ ≤ _ := hlogPoweri
  have hsum : g₁ i+g₂ i+g₃ i≤3*(T i)^(12*β+4*η) := by
    linarith only [hi₁,hi₂,hi₃]
  have hg0 : 0≤g₁ i+g₂ i+g₃ i := by dsimp only [g₁,g₂,g₃,U,w]; positivity
  calc
    _ = (1+Real.log (P i))^36*(g₁ i+g₂ i+g₃ i) := by dsimp only [g₁,g₂,g₃]; ring
    _ ≤ (T i)^η*(3*(T i)^(12*β+4*η)) := mul_le_mul hlog hsum hg0 (by positivity)
    _ = _ := by rw [mul_left_comm,←Real.rpow_add hTi]; congr 2; ring

/-- The exponent-pair refined spacing estimate gives the exact two-piece
analytic beta bound; every physical condition comes from the model sequence. -/
theorem isExponentSumBound_refined_bourgain
    {α : ℝ≥0} (hlo : 2/5<(α:ℝ)) (hhi : (α:ℝ)<3/7) :
    IsExponentSumBound α (max (1/12+2*(α:ℝ)/3) (241/1164+425*(α:ℝ)/1164)) := by
  intro P T F a b _hP hT hTunbounded hPT hF hab
  let β := max (1/12+2*(α:ℝ)/3) (241/1164+425*(α:ℝ)/1164)
  apply (isPowerBounded_iff_forall_pos (exponentialSum F T P a b) T β hT hTunbounded).mpr
  intro ε hε
  let η := min ((1:ℝ)/100) ε
  have hη : 0<η := lt_min (by norm_num) hε
  have hηε : η≤ε := min_le_right _ _
  have hηsmall : (13/84:ℝ)+η<1 := by
    have hh : η≤(1:ℝ)/100 := min_le_left _ _
    linarith only [hh]
  obtain ⟨hphase,σ,hσ,herror⟩ := hF
  obtain ⟨δ,κ₀,hδ,hκ₀,Q,_hQ,C₀,hC₀,hsource⟩ :=
    exists_model_refined_global_bound hσ exponentPair_bourgain hη hηsmall
  have happrox := (IsModelPhaseFunctionWith.mk hphase herror).eventually_isApproximate Q hδ
  have hparameters := eventually_refined_bourgain_parameters hlo hhi hσ hκ₀ hT hTunbounded hPT
  have hcost := eventually_refined_bourgain_cost hlo hhi hσ hη hT hTunbounded hPT
  let C := max 1 (3*C₀)
  have hC : 1≤C := le_max_left _ _
  have hC₀C : 3*C₀≤C := le_max_right _ _
  have hCpow : C≤C^12 := by
    calc
      C=C*1 := (mul_one C).symm
      _≤C*C^11 := mul_le_mul_of_nonneg_left (one_le_pow₀ hC) (zero_le_one.trans hC)
      _=C^12 := by ring
  refine Asymptotics.IsBigO.of_bound C ?_
  filter_upwards [happrox,hparameters,hcost] with i hFi hpi hci
  obtain ⟨hPi,hwi,hwhalf,hUsmall,hcurve,hPU,hLsmall,hliftSmall,hlift,hκ⟩ := hpi
  have hTi : 0<T i := zero_lt_one.trans_le (hT i)
  have hs := hsource (F i) (T i) (P i) (a i) (b i) ((T i)^(-(3+23*(α:ℝ))/194))
    hFi hTi hPi (hab i).1 (hab i).2 hwi hwhalf
    hUsmall hcurve hPU hLsmall hliftSmall hlift hκ
  have hmajor := mul_le_mul_of_nonneg_left hci hC₀.le
  have hbound : ‖exponentialSumAt (F i) (T i) (P i) (a i) (b i)‖^12≤
      (3*C₀)*(T i)^(12*β+5*η) := by
    apply hs.trans
    simpa only [mul_assoc,mul_left_comm C₀ 3] using hmajor
  have hexp : 12*β+5*η≤(β+ε)*12 := by linarith only [hηε,hε]
  have hp : ‖exponentialSumAt (F i) (T i) (P i) (a i) (b i)‖^12≤
      (C*(T i)^(β+ε))^12 := by
    calc
      _≤(3*C₀)*(T i)^(12*β+5*η) := hbound
      _≤C^12*(T i)^((β+ε)*12) :=
        mul_le_mul (hC₀C.trans hCpow) (Real.rpow_le_rpow_of_exponent_le (hT i) hexp)
          (Real.rpow_nonneg hTi.le _) (by positivity)
      _=_ := by rw [mul_pow,←Real.rpow_mul_natCast hTi.le]; norm_num
  have hh := (pow_le_pow_iff_left₀ (norm_nonneg _)
    (by positivity : 0≤C*(T i)^(β+ε)) (by norm_num : (12:ℕ)≠0)).mp hp
  simpa only [exponentialSum_apply,Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg hTi.le _)] using hh

/-- Public beta consumer of the complete refined original-source proof. -/
theorem exponentSumGrowthExponent_le_refined_bourgain
    {α : ℝ≥0} (hlo : 2/5<(α:ℝ)) (hhi : (α:ℝ)<3/7) :
    exponentSumGrowthExponent α ≤ max (1/12+2*(α:ℝ)/3) (241/1164+425*(α:ℝ)/1164) :=
  exponentSumGrowthExponent_le_iff.mpr (isExponentSumBound_refined_bourgain hlo hhi)

theorem sargosD_fallthrough_interval {a b : ℝ}
    (hsecondary : 1/12+2*a/3 ≤ b)
    (hRS : b < (1+9*a)/13)
    (hhigh : 5/12 ≤ a → b < 1/12+2*a/3) :
    1/4 < a ∧ a < 5/12 := by
  constructor
  · linarith only [hsecondary,hRS]
  · by_contra hh
    exact (not_lt_of_ge hsecondary) (hhigh (le_of_not_gt hh))

theorem sargosD_fallthrough_physical {a b h : ℝ}
    (ha : 1/4 < a) (ha' : a < 5/12)
    (hh : (4*a-1)/6 ≤ h) (hb : b=(4*a+1+2*h)/8)
    (hRS : b < (1+9*a)/13) :
    0<h ∧ h<1 ∧ 0<4*a-1-5*h ∧ 0<4*a-1-3*h ∧
      4*a-1-3*h<a ∧ 4*a-1-3*h<b ∧ 2*h<b ∧ b<a ∧
      1-4*a+4*h<0 ∧ 4*a-1-6*h≤0 ∧
      1-2*a+(4*a-1-3*h)+(4*a-1-5*h)<1 := by
  have hupper : h < (20*a-5)/26 := by linarith only [hb,hRS]
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩ <;>
    linarith only [ha,ha',hh,hb,hupper,hRS]

/-- The new analytic beta line removes the old curvature-sign obstruction.
The assumptions are only numerical fallthroughs from genuine proved beta
bounds and the actual D scale; no analytic conclusion is assumed. -/
theorem sargosD_refined_fallthrough_curvature
    {k l a b h : ℝ}
    (hk : 0≤k) (hl : 1/2≤l)
    (ha : 1/4<a) (ha' : a<5/12)
    (hh : (4*a-1)/6≤h) (hb : b=(4*a+1+2*h)/8)
    (hD : ((2*k+4*l)*a-l)/(2+5*k+3*l)≤h)
    (hP : b<k+(l-k)*a)
    (hB : b<l-1/2+(k-l+1)*a)
    (hnew : 2/5<a →
      b < max (1/12+2*a/3) (241/1164+425*a/1164)) :
    0<1-3*a+2*h := by
  have hd : 0<2+5*k+3*l := by linarith only [hk,hl]
  have hbudget := (div_le_iff₀ hd).mp hD
  have hs : 3/4+h/2<k+l := by rw [hb] at hP hB; linarith only [hP,hB]
  by_contra hbad
  have hmu : 1-3*a+2*h≤0 := le_of_not_gt hbad
  have ha40 : 2/5≤a := by linarith only [hh,hmu]
  have hh0 : 0≤h := by linarith only [hh,ha]
  have hcoef : 0<2*a-5*h := by linarith only [hmu,ha']
  have hdelta : 0≤2*a-1+2*h := by linarith only [hh,ha40]
  have hsum := mul_lt_mul_of_pos_left hs hcoef
  have hlower := mul_le_mul_of_nonneg_left hl hdelta
  have hpoly : (5/2)*a-1/2+(a-19/4)*h-(5/2)*h^2<0 := by
    nlinarith only [hbudget,hsum,hlower]
  have hlinear : a/2-3/32<h := by
    by_contra hn
    have hlin : h≤a/2-3/32 := le_of_not_gt hn
    have hlin0 : 0≤a/2-3/32 := hh0.trans hlin
    have hsq := pow_le_pow_left₀ hh0 hlin 2
    have hprod := mul_le_mul_of_nonpos_left hlin
      (show a-19/4≤0 by linarith only [ha'])
    have hupper : a≤5/12 := ha'.le
    have hasq := pow_le_pow_left₀ (show 0≤a by linarith only [ha40]) hupper 2
    nlinarith only [hpoly,hprod,hsq,hasq,ha40]
  have hanew : 2/5<a := by linarith only [hlinear,hmu]
  have hsecondary : 1/12+2*a/3≤b := by rw [hb]; linarith only [hh]
  have hline : b<241/1164+425*a/1164 := by
    have hhnew := hnew hanew
    rcases lt_max_iff.mp hhnew with hc|hc
    · exact False.elim ((not_lt_of_ge hsecondary) hc)
    · exact hc
  rw [hb] at hline
  linarith only [hline,hlinear,hmu]

theorem eventually_cubic_generic_parameters
    {T N : VariableObject ℝ} {α h σ κ₀ η : ℝ}
    (hlo : 1/4<α) (hhi : α<5/12)
    (hsecondary : (4*α-1)/6≤h)
    (hRS : (4*α+1+2*h)/8<(1+9*α)/13)
    (hcurvature : 0<1-3*α+2*h) (hσ : 0<σ)
    (hκ₀ : 0 < κ₀) (hη : 0 < η)
    (hT : ∀ i, 1 ≤ T i) (hTunbounded : T.IsUnbounded)
    (hNT : IsPowerAsymptotic N T α) :
    let r := 4*α-1-5*h
    let H := floorRpow T h
    let Y := fun i => (T i)^r
    let lam := fun i => modelPhaseJetLower σ 3*T i/(N i)^4
    let B := fun i => (modelPhaseJetCoefficient σ 3+1)*T i/(N i)^4
    let L := fun i => modelPhaseJetLower σ 2*T i/(N i)^3
    let U := fun i => (modelPhaseJetCoefficient σ 2+1)*T i/(N i)^3
    let Qcut := fun i => 3/(2*lam i*(H i:ℝ)^3)
    ∀ᶠ i in atTop, 0 < N i ∧ 2 ≤ H i ∧ 2 ≤ Y i ∧
      ∃ J : ℕ, 1 ≤ Qcut i ∧ Qcut i ≤ (2:ℝ)^J ∧ (J:ℝ)+2 ≤ (T i)^η ∧
        1/(4*(H i:ℝ)^2) ≤ L i/4 ∧
        4*U i*Qcut i*(N i)^2/(σ*T i) ≤ κ₀ ∧
        B i*((H i:ℝ)+1)^4 ≤ 1 := by
  intro r H Y lam B L U Qcut
  let q := 4*α-1-3*h
  obtain ⟨hh,_hh1,hr,hq,hqα,_hqβ,_h2hβ,_hβα,hTaylor,_he2,_he5⟩ :=
    sargosD_fallthrough_physical hlo hhi hsecondary rfl hRS
  have hTscale := isPowerAsymptotic_self T
  have hH : IsPowerAsymptotic (fun i => (H i:ℝ)) T h :=
    isPowerAsymptotic_floorRpow hh hT hTunbounded
  have hY : IsPowerAsymptotic Y T r := by
    simpa using cubic_power_rpow hTscale hT r
  have hc (c : ℝ) (hc : 0 < c) := cubic_power_const hT hTunbounded hc
  have hlam : IsPowerAsymptotic lam T (1-4*α) := by
    convert ((hc _ (modelPhaseJetLower_pos hσ 3)).mul hTscale hT).div
      (cubic_power_natpow hNT hT 4) hT using 1
    ring
  have hB : IsPowerAsymptotic B T (1-4*α) := by
    convert ((hc (modelPhaseJetCoefficient σ 3+1) (by positivity [modelPhaseJetCoefficient_pos hσ 3])).mul hTscale hT).div
      (cubic_power_natpow hNT hT 4) hT using 1
    ring
  have hL : IsPowerAsymptotic L T (1-3*α) := by
    convert ((hc _ (modelPhaseJetLower_pos hσ 2)).mul hTscale hT).div
      (cubic_power_natpow hNT hT 3) hT using 1
    ring
  have hU : IsPowerAsymptotic U T (1-3*α) := by
    convert ((hc (modelPhaseJetCoefficient σ 2+1) (by positivity [modelPhaseJetCoefficient_pos hσ 2])).mul hTscale hT).div
      (cubic_power_natpow hNT hT 3) hT using 1
    ring
  have hQ : IsPowerAsymptotic Qcut T q := by
    convert (hc 3 (by norm_num)).div
      (((hc 2 (by norm_num)).mul hlam hT).mul (cubic_power_natpow hH hT 3) hT) hT using 1
    dsimp [q]
    ring
  have hLH : IsPowerAsymptotic (fun i => L i*(H i:ℝ)^2) T (1-3*α+2*h) := by
    convert hL.mul (cubic_power_natpow hH hT 2) hT using 1
    ring
  have hshift : IsPowerAsymptotic (fun i => 4*U i*Qcut i*(N i)^2/(σ*T i)) T (q-α) := by
    convert ((((hc 4 (by norm_num)).mul hU hT).mul hQ hT).mul
      (cubic_power_natpow hNT hT 2) hT).div ((hc σ hσ).mul hTscale hT) hT using 1
    ring
  have htaylor : IsPowerAsymptotic (fun i => 16*B i*(H i:ℝ)^4) T (1-4*α+4*h) := by
    convert ((hc 16 (by norm_num)).mul hB hT).mul
      (cubic_power_natpow hH hT 4) hT using 1
    ring
  have hNlarge := (hNT.tendsto_atTop_of_pos
    (by linarith only [hlo] : 0 < α) hT hTunbounded).eventually (eventually_gt_atTop 0)
  have hHlarge := (hH.tendsto_atTop_of_pos hh hT hTunbounded).eventually
    (eventually_ge_atTop 2)
  have hYlarge := (hY.tendsto_atTop_of_pos hr hT hTunbounded).eventually
    (eventually_ge_atTop 2)
  have hQlarge := (hQ.tendsto_atTop_of_pos hq hT hTunbounded).eventually
    (eventually_ge_atTop 1)
  have hLHlarge := (hLH.tendsto_atTop_of_pos
    hcurvature hT hTunbounded).eventually
    (eventually_ge_atTop 1)
  have hshiftsmall := (hshift.tendsto_zero_of_neg
    (sub_neg.mpr hqα) hT hTunbounded).eventually
    (eventually_lt_nhds hκ₀)
  have htaylorsmall := (htaylor.tendsto_zero_of_neg
    hTaylor hT hTunbounded).eventually
    (eventually_lt_nhds (by norm_num : (0:ℝ) < 1))
  have hindex := cubic_dyadic_index_bound hT hTunbounded
    (by linarith only [hq] : 0 < q+1) hη
    (hQlarge.and (cubic_power_eventually_le hQ hT (by linarith : q<q+1)))
  filter_upwards [hNlarge,hHlarge,hYlarge,hLHlarge,hshiftsmall,htaylorsmall,hindex,hQlarge]
    with i hNi hHi hYi hLHi hsi hti hJi hQi
  obtain ⟨J,hJq,hJcount⟩ := hJi
  refine ⟨hNi,by exact_mod_cast hHi,hYi,J,hQi,hJq,hJcount,?_,hsi.le,?_⟩
  · have hHp : (0:ℝ) < H i := by linarith only [hHi]
    apply (div_le_iff₀ (by positivity : 0 < 4*(H i:ℝ)^2)).mpr
    nlinarith only [hLHi]
  · have hBp : 0 < B i := by
      dsimp [B]
      positivity [modelPhaseJetCoefficient_pos hσ 3,zero_lt_one.trans_le (hT i)]
    have hsum : (H i:ℝ)+1 ≤ 2*(H i:ℝ) := by linarith only [hHi]
    have hp := pow_le_pow_left₀ (by positivity : (0:ℝ) ≤ (H i:ℝ)+1) hsum 4
    have hm := mul_le_mul_of_nonneg_left hp hBp.le
    nlinarith only [hm,hti]

theorem eventually_cubic_generic_cost
    {T N : VariableObject ℝ} {k l α h σ η : ℝ}
    (hlo : 1/4<α) (hhi : α<5/12)
    (hsecondary : (4*α-1)/6≤h)
    (hRS : (4*α+1+2*h)/8<(1+9*α)/13)
    (hcurvature : 0<1-3*α+2*h)
    (hopt : (2*k+4*l)*α-l≤h*(2+5*k+3*l))
    (hσ : 0<σ) (hη : 0<η)
    (hT : ∀ i, 1 ≤ T i) (hTunbounded : T.IsUnbounded)
    (hNT : IsPowerAsymptotic N T α) :
    let r := 4*α-1-5*h
    let β := (4*α+1+2*h)/8
    let H := floorRpow T h
    let Y := fun i => (T i)^r
    let lam := fun i => modelPhaseJetLower σ 3*T i/(N i)^4
    let B := fun i => (modelPhaseJetCoefficient σ 3+1)*T i/(N i)^4
    let U := fun i => (modelPhaseJetCoefficient σ 2+1)*T i/(N i)^3
    let Qcut := fun i => 3/(2*lam i*(H i:ℝ)^3)
    ∀ᶠ i in atTop, ∀ J : ℕ, (J:ℝ)+2 ≤ (T i)^η →
      let E := ((J:ℝ)+2)*(U i/(lam i*(H i:ℝ)^2))*
        (1+B i/((lam i)^2*(H i:ℝ)^4)+Qcut i/(H i:ℝ)+Qcut i/Y i+
          (T i/(N i)^2)^(k+η)*(Qcut i)^(l+η)*(Y i)^(k+η)+(N i)^2/T i)
      (N i)^6*(N i+E)*(1+U i*(H i:ℝ)^2)*(H i:ℝ)^η+
          (H i:ℝ)^8+((H i:ℝ)^2+Qcut i+1)^8 ≤
        (15+3^8)*(T i)^(8*β+5*η) := by
  intro r β H Y lam B U Qcut
  let q := 4*α-1-3*h
  let V := fun i => U i/(lam i*(H i:ℝ)^2)
  let f₁ := fun i => V i/N i
  let f₂ := fun i => V i*(B i/((lam i)^2*(H i:ℝ)^4))/N i
  let f₃ := fun i => V i*(Qcut i/(H i:ℝ))/N i
  let f₄ := fun i => V i*(Qcut i/Y i)/N i
  let f₅ := fun i => V i*((T i/(N i)^2)^(k+η)*(Qcut i)^(l+η)*(Y i)^(k+η))/N i
  let f₆ := fun i => V i*((N i)^2/T i)/N i
  obtain ⟨hh,hh1,_hr,_hq,_hqα,hqβ,h2hβ,_hβα,_hTaylor,he₂,he₅⟩ :=
    sargosD_fallthrough_physical hlo hhi hsecondary rfl hRS
  change q<β at hqβ
  change 2*h<β at h2hβ
  change 1-2*α+q+r<1 at he₅
  have hTscale := isPowerAsymptotic_self T
  have hH : IsPowerAsymptotic (fun i => (H i:ℝ)) T h :=
    isPowerAsymptotic_floorRpow hh hT hTunbounded
  have hY : IsPowerAsymptotic Y T r := by simpa using cubic_power_rpow hTscale hT r
  have hc (c : ℝ) (hc : 0 < c) := cubic_power_const hT hTunbounded hc
  have hlam : IsPowerAsymptotic lam T (1-4*α) := by
    convert ((hc _ (modelPhaseJetLower_pos hσ 3)).mul hTscale hT).div
      (cubic_power_natpow hNT hT 4) hT using 1
    ring
  have hB : IsPowerAsymptotic B T (1-4*α) := by
    convert ((hc (modelPhaseJetCoefficient σ 3+1)
      (by positivity [modelPhaseJetCoefficient_pos hσ 3])).mul hTscale hT).div
      (cubic_power_natpow hNT hT 4) hT using 1
    ring
  have hU : IsPowerAsymptotic U T (1-3*α) := by
    convert ((hc (modelPhaseJetCoefficient σ 2+1)
      (by positivity [modelPhaseJetCoefficient_pos hσ 2])).mul hTscale hT).div
      (cubic_power_natpow hNT hT 3) hT using 1
    ring
  have hQ : IsPowerAsymptotic Qcut T q := by
    convert (hc 3 (by norm_num)).div
      (((hc 2 (by norm_num)).mul hlam hT).mul (cubic_power_natpow hH hT 3) hT) hT using 1
    dsimp [q]
    ring
  have hV : IsPowerAsymptotic V T (α-2*h) := by
    convert hU.div (hlam.mul (cubic_power_natpow hH hT 2) hT) hT using 1
    ring
  have hf₁ : IsPowerAsymptotic f₁ T (-2*h) := by
    convert hV.div hNT hT using 1
    ring
  have hf₂ : IsPowerAsymptotic f₂ T (4*α-1-6*h) := by
    convert (hV.mul (hB.div ((cubic_power_natpow hlam hT 2).mul
      (cubic_power_natpow hH hT 4) hT) hT) hT).div hNT hT using 1
    ring
  have hf₃ : IsPowerAsymptotic f₃ T (4*α-1-6*h) := by
    convert (hV.mul (hQ.div hH hT) hT).div hNT hT using 1
    dsimp [q]
    ring
  have hf₄ : IsPowerAsymptotic f₄ T 0 := by
    convert (hV.mul (hQ.div hY hT) hT).div hNT hT using 1
    dsimp [q,r]
    ring
  have hf₅ : IsPowerAsymptotic f₅ T ((2*k+4*l)*α-l-h*(2+5*k+3*l)+η*(1-2*α+q+r)) := by
    convert (hV.mul (((cubic_power_rpow (hTscale.div
      (cubic_power_natpow hNT hT 2) hT) hT (k+η)).mul
        (cubic_power_rpow hQ hT (l+η)) hT).mul
          (cubic_power_rpow hY hT (k+η)) hT) hT).div hNT hT using 1
    dsimp [q,r]
    ring
  have hf₆ : IsPowerAsymptotic f₆ T (2*α-1-2*h) := by
    convert (hV.mul ((cubic_power_natpow hNT hT 2).div hTscale hT) hT).div hNT hT using 1
    ring
  have hmain : IsPowerAsymptotic
      (fun i => (N i)^7*U i*(H i:ℝ)^2*(H i:ℝ)^η) T (8*β+h*η) := by
    convert (((cubic_power_natpow hNT hT 7).mul hU hT).mul
      (cubic_power_natpow hH hT 2) hT).mul (cubic_power_rpow hH hT η) hT using 1
    dsimp [β]
    ring
  have hwidth : IsPowerAsymptotic (fun i => U i*(H i:ℝ)^2) T (1-3*α+2*h) := by
    convert hU.mul (cubic_power_natpow hH hT 2) hT using 1
    ring
  have hhβ : h<β := by linarith only [hh,h2hβ]
  have hβ : 0<β := by linarith only [hh,hhβ]
  have he₆ : 2*α-1-2*h<0 := by linarith only [hhi,hh]
  have hb₁ := cubic_power_eventually_le hf₁ hT (by linarith only [hh,hη] : -2*h<2*η)
  have hb₂ := cubic_power_eventually_le hf₂ hT (by linarith only [he₂,hη] : 4*α-1-6*h<2*η)
  have hb₃ := cubic_power_eventually_le hf₃ hT (by linarith only [he₂,hη] : 4*α-1-6*h<2*η)
  have hb₄ := cubic_power_eventually_le hf₄ hT (by linarith only [hη] : 0<2*η)
  have hb₅ := cubic_power_eventually_le hf₅ hT
    (by
      have hh := mul_lt_mul_of_pos_left he₅ hη
      linarith only [hopt,hh,hη] :
        (2*k+4*l)*α-l-h*(2+5*k+3*l)+η*(1-2*α+q+r)<2*η)
  have hb₆ := cubic_power_eventually_le hf₆ hT (by linarith only [he₆,hη] : 2*α-1-2*h<2*η)
  have hbmain := cubic_power_eventually_le hmain hT
    (by nlinarith only [hh1,hη] : 8*β+h*η<8*β+2*η)
  have hbH := cubic_power_eventually_le hH hT hhβ
  have hbH₂ := cubic_power_eventually_le (cubic_power_natpow hH hT 2) hT
    (by linarith only [h2hβ] : h*2<β)
  have hbQ := cubic_power_eventually_le hQ hT hqβ
  have hbwidth := (hwidth.tendsto_atTop_of_pos
    hcurvature hT hTunbounded).eventually
      (eventually_ge_atTop 1)
  have hNlarge := (hNT.tendsto_atTop_of_pos
    (by linarith only [hlo] : 0 < α) hT hTunbounded).eventually (eventually_gt_atTop 0)
  filter_upwards [hb₁,hb₂,hb₃,hb₄,hb₅,hb₆,hbmain,hbH,hbH₂,hbQ,hbwidth,hNlarge]
    with i h₁ h₂ h₃ h₄ h₅ h₆ hm hHi hH₂i hQi hwi hNi
  intro J hJ E
  have hTi : 0 < T i := zero_lt_one.trans_le (hT i)
  have hHp : (0:ℝ) < H i := by exact_mod_cast floorRpow_pos T h i
  have hUp : 0 < U i := by dsimp [U]; positivity [modelPhaseJetCoefficient_pos hσ 2]
  have hlampos : 0 < lam i := by dsimp [lam]; positivity [modelPhaseJetLower_pos hσ 3]
  have hQp : 0 < Qcut i := by dsimp [Qcut]; positivity
  have hVp : 0 < V i := by dsimp [V]; positivity
  have hsum : f₁ i+f₂ i+f₃ i+f₄ i+f₅ i+f₆ i ≤ 6*(T i)^(2*η) := by
    linarith only [h₁,h₂,h₃,h₄,h₅,h₆]
  have heq : E=((J:ℝ)+2)*N i*(f₁ i+f₂ i+f₃ i+f₄ i+f₅ i+f₆ i) := by
    dsimp [E,f₁,f₂,f₃,f₄,f₅,f₆,V]
    field_simp
  have hE : E ≤ 6*N i*(T i)^(3*η) := by
    rw [heq]
    calc
      _ ≤ ((J:ℝ)+2)*N i*(6*(T i)^(2*η)) := by gcongr
      _ ≤ (T i)^η*N i*(6*(T i)^(2*η)) := by gcongr
      _ = _ := by
        rw [show (T i)^η*N i*(6*(T i)^(2*η)) =
          6*N i*((T i)^η*(T i)^(2*η)) by ring,← Real.rpow_add hTi]
        congr 2
        ring
  have hone₃ : 1 ≤ (T i)^(3*η) := Real.one_le_rpow (hT i) (by positivity)
  have hNE : N i+E ≤ 7*N i*(T i)^(3*η) := by
    have hn := mul_le_mul_of_nonneg_left hone₃ hNi.le
    nlinarith only [hE,hn]
  have hUW : 1+U i*(H i:ℝ)^2 ≤ 2*U i*(H i:ℝ)^2 := by linarith only [hwi]
  have hcost : (N i)^6*(N i+E)*(1+U i*(H i:ℝ)^2)*(H i:ℝ)^η ≤
      14*(T i)^(8*β+5*η) := by
    calc
      _ ≤ (N i)^6*(7*N i*(T i)^(3*η))*(2*U i*(H i:ℝ)^2)*(H i:ℝ)^η := by gcongr
      _ = 14*((N i)^7*U i*(H i:ℝ)^2*(H i:ℝ)^η)*(T i)^(3*η) := by ring
      _ ≤ 14*(T i)^(8*β+2*η)*(T i)^(3*η) := by gcongr
      _ = _ := by rw [mul_assoc,← Real.rpow_add hTi]; congr 2; ring
  have honeβ : 1 ≤ (T i)^β := Real.one_le_rpow (hT i) hβ.le
  have hR : (H i:ℝ)^2+Qcut i+1 ≤ 3*(T i)^β := by
    linarith only [hH₂i,hQi,honeβ]
  have hH8 : (H i:ℝ)^8 ≤ (T i)^(8*β+5*η) := by
    calc
      _ ≤ ((T i)^β)^8 := pow_le_pow_left₀ hHp.le hHi 8
      _ = (T i)^(8*β) := by rw [← Real.rpow_mul_natCast hTi.le]; congr 1; ring
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (hT i) (by linarith only [hη])
  have hR8 : ((H i:ℝ)^2+Qcut i+1)^8 ≤ 3^8*(T i)^(8*β+5*η) := by
    calc
      _ ≤ (3*(T i)^β)^8 := pow_le_pow_left₀ (by positivity) hR 8
      _ = 3^8*(T i)^(8*β) := by
        rw [mul_pow,← Real.rpow_mul_natCast hTi.le]
        congr 2
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le (hT i) (by linarith only [hη])) (by norm_num)
  linarith only [hcost,hH8,hR8]

theorem isExponentSumBound_cubic_generic
    {k l h : ℝ} {α : ℝ≥0} (hpair : ExponentPair k l)
    (hlo : 1/4<(α:ℝ)) (hhi : (α:ℝ)<5/12)
    (hsecondary : (4*(α:ℝ)-1)/6≤h)
    (hRS : (4*(α:ℝ)+1+2*h)/8<(1+9*(α:ℝ))/13)
    (hcurvature : 0<1-3*(α:ℝ)+2*h)
    (hopt : (2*k+4*l)*(α:ℝ)-l≤h*(2+5*k+3*l)) :
    IsExponentSumBound α ((4*(α:ℝ)+1+2*h)/8) := by
  intro N T F a b _hN hT hTunbounded hNT hF hab
  apply (isPowerBounded_iff_forall_pos
    (exponentialSum F T N a b) T ((4*(α:ℝ)+1+2*h)/8) hT hTunbounded).mpr
  intro ε hε
  let η := min ((1:ℝ)/100) ε
  have hη : 0 < η := lt_min (by norm_num) hε
  have hηε : η ≤ ε := min_le_right _ _
  have hηsmall : k+η < 1 := by
    have hh : η ≤ (1:ℝ)/100 := min_le_left _ _
    linarith [hpair.inTriangle.2.1]
  obtain ⟨hphase,σ,hσ,herror⟩ := hF
  obtain ⟨δ,κ₀,hδ,hκ₀,Q,_hQ,C₀,hC₀,hsource⟩ :=
    TaoTrudgianYang2025.CubicJointCount.exists_complete_cubic_eighth_estimate
      hσ hpair hη hηsmall
  have happrox := (IsModelPhaseFunctionWith.mk hphase herror).eventually_isApproximate Q hδ
  have hparameters := eventually_cubic_generic_parameters hlo hhi hsecondary hRS hcurvature hσ hκ₀ hη hT hTunbounded hNT
  have hcost := eventually_cubic_generic_cost hlo hhi hsecondary hRS hcurvature hopt hσ hη hT hTunbounded hNT
  let β := (4*(α:ℝ)+1+2*h)/8
  let C := max 1 (C₀*(15+3^8))
  have hC : 1 ≤ C := le_max_left _ _
  have hC₀C : C₀*(15+3^8) ≤ C := le_max_right _ _
  have hCpow : C ≤ C^8 := by
    calc
      C = C*1 := (mul_one C).symm
      _ ≤ C*C^7 := mul_le_mul_of_nonneg_left (one_le_pow₀ hC) (zero_le_one.trans hC)
      _ = _ := by ring
  refine Asymptotics.IsBigO.of_bound C ?_
  filter_upwards [happrox,hparameters,hcost] with i hFi hpi hci
  obtain ⟨hNi,hHi,hYi,J,hQi,hQJ,hJ,hcurv,hshift,hTaylor⟩ := hpi
  have hTi : 0 < T i := zero_lt_one.trans_le (hT i)
  have hs := hsource (F i) (T i) (N i)
    ((T i)^(4*(α:ℝ)-1-5*h)) (a i) (b i)
    (floorRpow T h i) J
    hFi hTi hNi hHi hYi (hab i).1 (hab i).2
    hQi hQJ hcurv hshift hTaylor
  have hmajor := mul_le_mul_of_nonneg_left (hci J hJ) hC₀.le
  have hbound : ‖exponentialSumAt (F i) (T i) (N i) (a i) (b i)‖^8 ≤
      C₀*(15+3^8)*(T i)^(8*β+5*η) := by
    exact hs.trans (by convert hmajor using 1; ring)
  have hexp : 8*β+5*η ≤ (β+ε)*8 := by linarith only [hηε,hε]
  have hp : ‖exponentialSumAt (F i) (T i) (N i) (a i) (b i)‖^8 ≤
      (C*(T i)^(β+ε))^8 := by
    calc
      _ ≤ C₀*(15+3^8)*(T i)^(8*β+5*η) := hbound
      _ ≤ C^8*(T i)^((β+ε)*8) :=
        mul_le_mul (hC₀C.trans hCpow) (Real.rpow_le_rpow_of_exponent_le (hT i) hexp)
          (Real.rpow_nonneg hTi.le _) (by positivity)
      _ = _ := by rw [mul_pow,← Real.rpow_mul_natCast hTi.le]; norm_num
  have hh := (pow_le_pow_iff_left₀ (norm_nonneg _)
    (by positivity : 0 ≤ C*(T i)^(β+ε)) (by norm_num : (8:ℕ)≠0)).mp hp
  simpa only [exponentialSum_apply,Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg hTi.le _)] using hh


/-- The exact max-balanced Taylor scale realizes the printed D beta line. -/
theorem sargosD_balanced_scale {k l a : ℝ} (hk : 0≤k) (hl : 0≤l) :
    let h := max (((2*k+4*l)*a-l)/(2+5*k+3*l)) ((4*a-1)/6)
    max (exponentPairLine (sargosDProcessK k l) (sargosDProcessL k l) a)
      (1/12+2*a/3) = (4*a+1+2*h)/8 := by
  intro h
  let hD := ((2*k+4*l)*a-l)/(2+5*k+3*l)
  have hd : 2+5*k+3*l≠0 := by positivity
  have hd' : 5*k+3*l+2≠0 := by positivity
  have hid : exponentPairLine (sargosDProcessK k l) (sargosDProcessL k l) a=
      (4*a+1+2*hD)/8 := by
    dsimp only [exponentPairLine,sargosDProcessK,sargosDProcessL,hD]
    field_simp
    ring
  rw [hid]
  have hDle : hD≤h := le_max_left _ _
  have hsle : (4*a-1)/6≤h := le_max_right _ _
  apply le_antisymm
  · apply max_le <;> linarith only [hDle,hsle]
  · rcases le_total hD ((4*a-1)/6) with hc|hc
    · have he : h=(4*a-1)/6 := max_eq_right hc
      rw [he]
      exact le_trans (by linarith) (le_max_right _ _)
    · have he : h=hD := max_eq_left hc
      rw [he]
      exact le_max_left _ _

/-- Unconditional half-interval Sargos D bound, using the actual input pair
and the refined beta theorem to discharge the curvature-sign fallthrough. -/
theorem exponentSumGrowthExponent_le_sargosD_half
    {k l : ℝ} (hpair : ExponentPair k l)
    {α : ℝ≥0} (hhalf : (α:ℝ)≤1/2) :
    exponentSumGrowthExponent α ≤
      max (exponentPairLine (sargosDProcessK k l) (sargosDProcessL k l) α)
        (1/12+2*(α:ℝ)/3) := by
  let β := max (exponentPairLine (sargosDProcessK k l) (sargosDProcessL k l) α)
    (1/12+2*(α:ℝ)/3)
  have hsec : 1/12+2*(α:ℝ)/3≤β := le_max_right _ _
  have hα1 : (α:ℝ)≤1 := by linarith only [hhalf]
  by_cases hPc : exponentPairLine k l α≤β
  · exact (exponentSumGrowthExponent_le_exponentPairLine_closed hpair α hα1).trans hPc
  have hP : β<k+(l-k)*(α:ℝ) := lt_of_not_ge hPc
  by_cases hBc : exponentPairLine (l-1/2) (k+1/2) α≤β
  · exact (exponentSumGrowthExponent_le_exponentPairLine_closed hpair.bProcess α hα1).trans hBc
  have hB : β<l-1/2+(k-l+1)*(α:ℝ) := by
    have hh := lt_of_not_ge hBc
    convert hh using 1
    unfold exponentPairLine
    ring
  have hRSbound : exponentSumGrowthExponent α≤(1+9*(α:ℝ))/13 := by
    have hh := exponentSumGrowthExponent_le_exponentPairLine_closed exponentPair_robertSargos α hα1
    convert hh using 1
    unfold exponentPairLine
    ring
  by_cases hRSc : (1+9*(α:ℝ))/13≤β
  · exact hRSbound.trans hRSc
  have hRS : β<(1+9*(α:ℝ))/13 := lt_of_not_ge hRSc
  by_cases hhigh : 5/12≤(α:ℝ)
  · have hbound : exponentSumGrowthExponent α≤1/12+2*(α:ℝ)/3 := by
      by_cases hm : (α:ℝ)≤3/7
      · have hh := exponentSumGrowthExponent_le_bourgain_table_second hhigh hm
        linarith only [hh]
      · have hh := exponentSumGrowthExponent_le_bourgain_baseline (le_of_not_ge hm) hhalf
        linarith only [hh,le_of_not_ge hm]
    exact hbound.trans hsec
  have hhi : (α:ℝ)<5/12 := lt_of_not_ge hhigh
  have hlo : 1/4<(α:ℝ) := by linarith only [hsec,hRS]
  by_cases hnewCover : 2/5<(α:ℝ) ∧
      max (1/12+2*(α:ℝ)/3) (241/1164+425*(α:ℝ)/1164)≤β
  · exact (exponentSumGrowthExponent_le_refined_bourgain hnewCover.1
      (by linarith only [hhi])).trans hnewCover.2
  have hnew : 2/5<(α:ℝ) →
      β < max (1/12+2*(α:ℝ)/3) (241/1164+425*(α:ℝ)/1164) := by
    intro ha
    exact lt_of_not_ge (fun hh => hnewCover ⟨ha,hh⟩)
  have hk : 0≤k := hpair.inTriangle.1
  have hl : 1/2≤l := hpair.inTriangle.2.2.1
  have hl0 : 0≤l := by linarith only [hl]
  let h := max (((2*k+4*l)*(α:ℝ)-l)/(2+5*k+3*l)) ((4*(α:ℝ)-1)/6)
  have hb : β=(4*(α:ℝ)+1+2*h)/8 := sargosD_balanced_scale hk hl0
  have hsecondary : (4*(α:ℝ)-1)/6≤h := le_max_right _ _
  have hD : ((2*k+4*l)*(α:ℝ)-l)/(2+5*k+3*l)≤h := le_max_left _ _
  have hcurvature := sargosD_refined_fallthrough_curvature hk hl hlo hhi
    hsecondary hb hD hP hB hnew
  have hden : 0<2+5*k+3*l := by positivity
  have hopt := (div_le_iff₀ hden).mp hD
  have hRS' : (4*(α:ℝ)+1+2*h)/8<(1+9*(α:ℝ))/13 := by rw [←hb]; exact hRS
  have hbound := isExponentSumBound_cubic_generic hpair hlo hhi hsecondary hRS' hcurvature hopt
  have hh := exponentSumGrowthExponent_le_iff.mpr hbound
  change exponentSumGrowthExponent α≤β
  simpa only [hb] using hh

/-- Exact printed D-process source contract on the full closed unit interval.
The upper half follows from the proved reflection of the actual beta function. -/
theorem exponentSumGrowthExponent_le_sargosD
    {k l : ℝ} (hpair : ExponentPair k l)
    {α : ℝ≥0} (hα : (α:ℝ)≤1) :
    exponentSumGrowthExponent α ≤
      max (exponentPairLine (sargosDProcessK k l) (sargosDProcessL k l) α)
        (1/12+2*(α:ℝ)/3) := by
  by_cases hhalf : (α:ℝ)≤1/2
  · exact exponentSumGrowthExponent_le_sargosD_half hpair hhalf
  have hαNN : α≤1 := by exact_mod_cast hα
  let γ : ℝ≥0 := 1-α
  have hγreal : (γ:ℝ)=1-(α:ℝ) := NNReal.coe_sub hαNN
  have hγhalf : (γ:ℝ)≤1/2 := by rw [hγreal]; linarith only [le_of_not_ge hhalf]
  have hγ : (γ:ℝ)≤1 := by linarith only [hγhalf]
  have hγNN : γ≤1 := by exact_mod_cast hγ
  have hdouble : (1-γ:ℝ≥0)=α := by
    apply NNReal.coe_injective
    rw [NNReal.coe_sub hγNN,hγreal]
    norm_num
  have hrefl := exponentSumGrowthExponent_reflection hγ
  rw [hdouble] at hrefl
  have hb := exponentSumGrowthExponent_le_sargosD_half hpair hγhalf
  have hk : 0≤k := hpair.inTriangle.1
  have hl : 0≤l := by linarith [hpair.inTriangle.2.2.1]
  calc
    _ = 1/2-(γ:ℝ)+exponentSumGrowthExponent γ := hrefl
    _ ≤ 1/2-(γ:ℝ)+max
        (exponentPairLine (sargosDProcessK k l) (sargosDProcessL k l) γ)
        (1/12+2*(γ:ℝ)/3) := add_le_add le_rfl hb
    _ ≤ _ := by
      rw [add_max,hγreal]
      apply max_le
      · exact (exponentPairLine_reflected_le (sargosDProcess_slope hk hl)
          (le_of_not_ge hhalf)).trans (le_max_left _ _)
      · have hh : 1/2-(1-(α:ℝ))+(1/12+2*(1-(α:ℝ))/3)≤1/12+2*(α:ℝ)/3 := by
          linarith only [le_of_not_ge hhalf]
        exact hh.trans (le_max_right _ _)

/-- Where the printed secondary line is dominated, the exact analytic
D beta contract yields the D-transformed exponent pair. -/
theorem exponentPair_sargosD {k l : ℝ}
    (hpair : ExponentPair k l) (hzero : 0≤5*k-3*l+2) (hhalf : 2≤k+3*l) :
    ExponentPair (sargosDProcessK k l) (sargosDProcessL k l) :=
  sargosDProcess_pair_of_beta_bound hpair.inTriangle.1
    (by linarith [hpair.inTriangle.2.2.1]) hzero hhalf
    (fun α hα => by
      have hh := exponentSumGrowthExponent_le_sargosD_half hpair hα
      convert hh using 1
      congr 1
      ring)

/-- Exact public table row from a stronger proved analytic beta bound. -/
theorem exponentSumGrowthExponent_le_huxley_thirteenthRow
    {α : ℝ≥0} (hlo : 62831/155153 ≤ (α:ℝ)) (hhi : (α:ℝ) ≤ 143/349) :
    exponentSumGrowthExponent α ≤ 569/2800+1053*(α:ℝ)/2800 := by
  have h := exponentSumGrowthExponent_le_refined_bourgain
    (by linarith only [hlo] : 2/5<(α:ℝ)) (by linarith only [hhi] : (α:ℝ)<3/7)
  apply h.trans
  apply max_le <;> linarith only [hlo,hhi]

/-- Exact public table row, including both endpoints, from the refined source. -/
theorem exponentSumGrowthExponent_le_huxley_fourteenthRow
    {α : ℝ≥0} (hlo : 143/349 ≤ (α:ℝ)) (hhi : (α:ℝ) ≤ 263/638) :
    exponentSumGrowthExponent α ≤ 491/5530+1812*(α:ℝ)/2765 := by
  have h := exponentSumGrowthExponent_le_refined_bourgain
    (by linarith only [hlo] : 2/5<(α:ℝ)) (by linarith only [hhi] : (α:ℝ)<3/7)
  apply h.trans
  apply max_le <;> linarith only [hlo,hhi]

/-- Exact public table row, including both endpoints, from the refined source. -/
theorem exponentSumGrowthExponent_le_huxley_fifteenthRow
    {α : ℝ≥0} (hlo : 263/638 ≤ (α:ℝ)) (hhi : (α:ℝ) ≤ 1673/4038) :
    exponentSumGrowthExponent α ≤ 113/1345+897*(α:ℝ)/1345 := by
  have h := exponentSumGrowthExponent_le_refined_bourgain
    (by linarith only [hlo] : 2/5<(α:ℝ)) (by linarith only [hhi] : (α:ℝ)<3/7)
  apply h.trans
  apply max_le <;> linarith only [hlo,hhi]

/-- The exact Trudgian--Yang input follows from the proved stronger refined
beta estimate, D(Bourgain), and Bourgain; no literature pair is postulated. -/
theorem exponentPair_trudgianYang_first :
    ExponentPair (4742/38463) (35731/51284) := by
  apply exponentPair_of_beta_bound_half
    (by norm_num [InExponentPairTriangle]) (by norm_num)
  intro α hhalf
  by_cases hlo : (α:ℝ)≤403/1000
  · have hh := exponentSumGrowthExponent_le_sargosD_bourgain
      (α:=α) (by linarith only [hhalf] : (α:ℝ)≤1)
    unfold exponentPairLine at hh ⊢
    linarith only [hh,hlo]
  by_cases hhi : (α:ℝ)<3/7
  · have hh := exponentSumGrowthExponent_le_refined_bourgain
      (by linarith only [lt_of_not_ge hlo] : 2/5<(α:ℝ)) hhi
    apply hh.trans
    unfold exponentPairLine
    apply max_le <;> linarith only [lt_of_not_ge hlo,hhi]
  · have hh := exponentSumGrowthExponent_le_exponentPairLine_closed
      exponentPair_bourgain α (by linarith only [hhalf] : (α:ℝ)≤1)
    unfold exponentPairLine at hh ⊢
    linarith only [hh,le_of_not_gt hhi]

/-- The exact A-image used by the sixth public beta-table row. -/
theorem exponentPair_aTrudgianYang_first :
    ExponentPair (2371/43205) (280013/345640) := by
  have h := exponentPair_trudgianYang_first.aProcess
  norm_num at h
  exact h

/-- The sixth table row holds on the whole closed unit interval. -/
theorem exponentSumGrowthExponent_le_trudgianYang_sixthRow
    {α : ℝ≥0} (hα : (α:ℝ)≤1) :
    exponentSumGrowthExponent α ≤ 2371/43205+52209*(α:ℝ)/69128 := by
  have h := exponentSumGrowthExponent_le_exponentPairLine_closed
    exponentPair_aTrudgianYang_first α hα
  convert h using 1
  unfold exponentPairLine
  ring

end TaoTrudgianYang2025.CubicJointCount
