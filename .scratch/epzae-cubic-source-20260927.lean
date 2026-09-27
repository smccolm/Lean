import TaoTrudgianYang2025.SquareProductCount

/-! Actual cubic samples through the already-proved four-dimensional sieve.
The fourth coordinate is identically zero; no new sieve kernel is built. -/

noncomputable section
open Set MeasureTheory GafniTao
open scoped BigOperators FourierTransform
namespace TaoTrudgianYang2025.CubicSourcePrototype
open SquareProductCount.CubicMoment

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

#print axioms exists_C4_source_eighth_reduction
#print axioms norm_range_sum_shift_sub
#print axioms source_shift_average_norm
#print axioms cubicPrefixCoefficient_norm
#print axioms cubicSourceSum_prefix
#print axioms exists_C4_cubic_sample_bound
#print axioms exists_cubic_sample_bound
#print axioms exists_cubic_sample_bound_fract
#print axioms cubicTuple_power_abs
#print axioms cubicSamplingScale_pos
#print axioms cubicSamplingWidth_pos
#print axioms cubicTuplePoint_scale
#print axioms cubic_sampling_box_factor
#print axioms cubic_sampling_moment_factor
#print axioms cubicSourceSum_fourth_four
#print axioms cubicSourceSum_fract
#print axioms cubic_sample_eighth_sieve
#print axioms cubic_frequency_pairs_subset
#print axioms exists_cubic_frequency_pair_bound

-- Exact source, empty common prefix, and a strict nonempty prefix.
example : cubicSourceSum 3 (fun _ => 1) 0 0 0=3 := by
  norm_num [cubicSourceSum,fordAdditiveCharacter,Finset.sum_const,Int.card_Icc]
  rfl

example : cubicSourceSum 8 (cubicPrefixCoefficient 0) 2 3 4=0 := by
  rw [cubicSourceSum_prefix (by omega : 0 ≤ 8)]
  simp

example : cubicSourceSum 3 (cubicPrefixCoefficient 2) 0 0 0=2 := by
  rw [cubicSourceSum_prefix (by omega : 2 ≤ 3)]
  norm_num [fordAdditiveCharacter]

-- Distinct source labels with identical coordinates retain all multiplicities.
example : (cubicSamplePairs (Finset.range 3) 2 (fun _ => 0) (fun _ => 0) (fun _ => 0)).card=9 := by
  have he : cubicSamplePairs (Finset.range 3) 2 (fun _ => 0) (fun _ => 0) (fun _ => 0)=
      Finset.range 3 ×ˢ Finset.range 3 := by
    unfold cubicSamplePairs
    apply Finset.filter_eq_self.mpr
    intro p _hp d
    have hd := cubicSamplingScale_pos (by norm_num : 1 ≤ 2) d
    simp only [sub_self,abs_zero]
    positivity
  rw [he]
  norm_num

-- The closed near-pair threshold is retained, while a larger gap is excluded.
example : (0,1)∈cubicSamplePairs (Finset.range 2) 1 (fun i => (i:ℝ)/4)
    (fun _ => 0) (fun _ => 0) := by
  norm_num [cubicSamplePairs,cubicSamplePoint,cubicSamplingScale,Fin.forall_fin_succ]

example : (0,1)∉cubicSamplePairs (Finset.range 2) 1 (fun i => (i:ℝ)/3)
    (fun _ => 0) (fun _ => 0) := by
  norm_num [cubicSamplePairs,cubicSamplePoint,cubicSamplingScale,Fin.forall_fin_succ]

example (w : ℕ → ℂ) (M H : ℕ) (hw : ∀ k, ‖w k‖ ≤ 1) :
    (H:ℝ)*‖∑ m∈Finset.range M, w m‖ ≤
      (∑ m∈Finset.range M, ‖∑ j∈Finset.range H, w (m+(j+1))‖)+2*(H:ℝ)^2 :=
  source_shift_average_norm w M H hw

example {ε : ℝ} (hε : 0 < ε) :
    ∃ C > (0:ℝ), ∀ (f : ℝ → ℝ) (M H : ℕ), 1 ≤ H →
      ∀ B c μ : ℝ, 0 ≤ B → 0 < μ → B*((H:ℝ)+1)^4 ≤ 1 →
      (∀ m∈Finset.range M, ∀ y∈Icc ((m:ℝ)-H) ((m:ℝ)+H+2), ContDiffAt ℝ 4 f y) →
      (∀ m∈Finset.range M, ∀ y∈Icc ((m:ℝ)-H) ((m:ℝ)+H+2), |iteratedDeriv 4 f y| ≤ B) →
      (∀ m∈Finset.range M, iteratedDeriv 3 f ((m:ℝ)+1)/6∈Icc c (c+μ)) →
      ‖∑ m∈Finset.range M, fordAdditiveCharacter (f ((m:ℝ)+1))‖^8 ≤
        C*((M:ℝ)^6*(cubicDerivativePairs f M H).card*(1+μ*(H:ℝ)^2)*(H:ℝ)^ε+(H:ℝ)^8) :=
  exists_C4_source_eighth_reduction hε

end TaoTrudgianYang2025.CubicSourcePrototype
