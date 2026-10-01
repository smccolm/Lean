import TaoTrudgianYang2025.HuxleyLinearForms

open Set TaoTrudgianYang2025 TaoTrudgianYang2025.HuxleyRationalPhase
open scoped BigOperators Classical ContDiff
namespace HuxleyActualFamilyPhysicalScratch


/-- The model third derivative prevents the actual normalized source
amplitude from degenerating. No lower comparison between Tsrc and T
is assumed. -/
private theorem positive_difference_approximate_model_source_amplitude
    (Fsrc : ℝ → ℝ) {σsrc Usrc η y Tsrc T σ δ : ℝ}
    (hσsrc : 0 < σsrc) (hUsrc : 0 < Usrc)
    (hη : 0 < η) (hηmax : η ≤ 1/8) (hy : y∈Icc (1:ℝ) 2)
    (hTsrc : 0 < Tsrc) (hT : 0 < T) (hσ : 0 < σ)
    (hδ : δ ≤ min (modelPhaseThirdLower σ) 1)
    (hreg : ∀ w, 0 < w → ContDiffAt ℝ ∞ Fsrc w)
    (hjets : ∀ w∈Icc (1/2:ℝ) 3, ∀ n ≤ 6, |iteratedDeriv (n+1) Fsrc w| ≤ Usrc) :
    let F := fun u => (Tsrc/T)*(Fsrc u-Fsrc (u+η*y))/(σsrc*η)
    Expdb.IsApproximateModelPhaseFunction F σ 2 δ →
      modelPhaseThirdLower σ*σsrc*T/(3*Usrc) ≤ Tsrc := by
  intro F hF
  let G := fun u => (Fsrc u-Fsrc (u+η*y))/(σsrc*η)
  have hFu : F=fun u => (Tsrc/T)*G u := by
    funext u
    dsimp only [F,G]
    ring
  have hd : iteratedDeriv 3 F (3/2)=
      (Tsrc/T)*iteratedDeriv 3 G (3/2) := by
    rw [hFu,iteratedDeriv_const_mul_field]
  have hlow : modelPhaseThirdLower σ ≤ iteratedDeriv 3 F (3/2) := by
    simpa only [iteratedDeriv_succ,iteratedDeriv_zero] using
      (approximateModelPhase_thirdDeriv_bounds hσ hδ hF
        (by norm_num : (3/2:ℝ)∈Ioo (1:ℝ) 2)).1
  have hu := positive_jets_difference_mixed_upper Fsrc hσsrc hUsrc hη hηmax
    (by norm_num : (3/2:ℝ)∈Icc (3/4:ℝ) (9/4))
    (show y∈Icc (1/2:ℝ) 3 from
      ⟨by linarith only [hy.1],by linarith only [hy.2]⟩)
    hreg hjets 3 0 (by norm_num) (by norm_num)
  simp only [iteratedDeriv_zero] at hu
  have hupper : |iteratedDeriv 3 F (3/2)| ≤ (Tsrc/T)*(3*Usrc/σsrc) := by
    rw [hd,abs_mul,abs_of_pos (div_pos hTsrc hT)]
    exact mul_le_mul_of_nonneg_left hu (div_pos hTsrc hT).le
  have hh := hlow.trans ((le_abs_self _).trans hupper)
  have he : (Tsrc/T)*(3*Usrc/σsrc)=3*Usrc*Tsrc/(σsrc*T) := by ring
  rw [he] at hh
  have hc := (le_div_iff₀ (mul_pos hσsrc hT)).mp hh
  apply (div_le_iff₀ (mul_pos (by norm_num : (0:ℝ) < 3) hUsrc)).mpr
  nlinarith only [hc]


private theorem actual_color_tenth_weight_bound
    {α β : Type*} [DecidableEq α] [DecidableEq β]
    (V : Finset α) (color : α → β) :
    (∑ key∈V.image color, ((V.filter (fun i => color i=key)).card:ℝ)^10) ≤
      (V.card:ℝ)^10 := by
  have hcard :
      (∑ key∈V.image color, ((V.filter (fun i => color i=key)).card:ℝ))=(V.card:ℝ) := by
    exact_mod_cast (Finset.card_eq_sum_card_image color V).symm
  calc
    _ = ∑ key∈V.image color,
        ((V.filter (fun i => color i=key)).card:ℝ)*
          ((V.filter (fun i => color i=key)).card:ℝ)^9 := by
      apply Finset.sum_congr rfl
      intro key _
      rw [pow_succ']
    _ ≤ ∑ key∈V.image color,
        ((V.filter (fun i => color i=key)).card:ℝ)*(V.card:ℝ)^9 := by
      apply Finset.sum_le_sum
      intro key _
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      apply pow_le_pow_left₀ (Nat.cast_nonneg _)
      exact_mod_cast Finset.card_filter_le V (fun i => color i=key)
    _ = (V.card:ℝ)^10 := by
      rw [←Finset.sum_mul,hcard]
      ring

private theorem actual_color_tenth_weight_absorption
    {α β : Type*} [DecidableEq α] [DecidableEq β]
    (V : Finset α) (color : α → β) {X C B : ℝ}
    (hX : 0 ≤ X)
    (hbound : X ≤ C*(∑ key∈V.image color,
      ((V.filter (fun i => color i=key)).card:ℝ)^10*B)) :
    X ≤ C*(V.card:ℝ)^10*B := by
  classical
  by_cases hV : V=∅
  · simpa only [hV,Finset.image_empty,Finset.sum_empty,Finset.card_empty,Nat.cast_zero,
      zero_pow (by decide : (10:ℕ)≠0),mul_zero,zero_mul] using hbound
  · obtain ⟨i,hi⟩ := Finset.nonempty_iff_ne_empty.mpr hV
    have hf : 0 < (V.filter (fun j => color j=color i)).card :=
      Finset.card_pos.mpr ⟨i,Finset.mem_filter.mpr ⟨hi,rfl⟩⟩
    have hweight : 0 < ∑ key∈V.image color,
        ((V.filter (fun j => color j=key)).card:ℝ)^10 :=
      lt_of_lt_of_le (pow_pos (Nat.cast_pos.mpr hf) 10)
        (Finset.single_le_sum
          (f:=fun key => ((V.filter (fun j => color j=key)).card:ℝ)^10)
          (fun key _ => pow_nonneg (Nat.cast_nonneg _) 10)
          (Finset.mem_image_of_mem color hi))
    have hbound' : X ≤ (C*B)*(∑ key∈V.image color,
        ((V.filter (fun i => color i=key)).card:ℝ)^10) := by
      calc
        X ≤ _ := hbound
        _ = _ := by rw [←Finset.sum_mul]; ac_rfl
    have hCB : 0 ≤ C*B := nonneg_of_mul_nonneg_left (hX.trans hbound') hweight
    calc
      X ≤ _ := hbound'
      _ ≤ (C*B)*(V.card:ℝ)^10 :=
        mul_le_mul_of_nonneg_left (actual_color_tenth_weight_bound V color) hCB
      _ = _ := by ac_rfl


private theorem cubic_completion_weight_bound
    {Q q μ₀ μ N A : ℝ}
    (hQ : 0 < Q) (hμ₀ : 0 < μ₀) (hN : 0 < N)
    (hQq : Q ≤ 2*q) (hμ : μ₀ ≤ μ) (hNA : N ≤ A) :
    Real.sqrt (2*q)/(q*Real.sqrt (μ*A)) ≤ Real.sqrt (4/(Q*(μ₀*N))) := by
  have hq : 0 < q := by linarith only [hQ,hQq]
  have hμp := hμ₀.trans_le hμ
  have hAp := hN.trans_le hNA
  have hμA := mul_pos hμp hAp
  have hμN : μ₀*N ≤ μ*A := mul_le_mul hμ hNA hN.le hμp.le
  have hden := mul_pos hQ (mul_pos hμ₀ hN)
  have hright : 0 ≤ 4/(Q*(μ₀*N)) := div_nonneg (by norm_num) hden.le
  apply (sq_le_sq₀ (div_nonneg (Real.sqrt_nonneg _) (mul_nonneg hq.le (Real.sqrt_nonneg _)))
    (Real.sqrt_nonneg _)).mp
  rw [div_pow,mul_pow,Real.sq_sqrt (by positivity : 0 ≤ 2*q),
    Real.sq_sqrt hμA.le,Real.sq_sqrt hright]
  apply (div_le_div_iff₀ (mul_pos (pow_pos hq 2) hμA) hden).mpr
  have hm := mul_le_mul hQq hμN (mul_nonneg hμ₀.le hN.le) (by positivity : 0 ≤ 2*q)
  have hh := mul_le_mul_of_nonneg_left hm (by positivity : 0 ≤ 2*q)
  nlinarith only [hh]

private theorem cubic_completion_weighted_twelfth
    {ι : Type*} (S : Finset ι) (q μ A : ι → ℝ) (z : ι → ℂ)
    {Q μ₀ N : ℝ} (hQ : 0 < Q) (hμ₀ : 0 < μ₀) (hN : 0 < N)
    (hQq : ∀ i∈S, Q ≤ 2*q i) (hμ : ∀ i∈S, μ₀ ≤ μ i)
    (hNA : ∀ i∈S, N ≤ A i) :
    (∑ i∈S, (Real.sqrt (2*q i)/(q i*Real.sqrt (μ i*A i)))*‖z i‖)^12 ≤
      (4/(Q*(μ₀*N)))^6*(∑ i∈S,‖z i‖)^12 := by
  let B := 4/(Q*(μ₀*N))
  have hB : 0 ≤ B := div_nonneg (by norm_num) (mul_nonneg hQ.le (mul_nonneg hμ₀.le hN.le))
  have hweight i (hi : i∈S) :
      Real.sqrt (2*q i)/(q i*Real.sqrt (μ i*A i)) ≤ Real.sqrt B :=
    cubic_completion_weight_bound hQ hμ₀ hN (hQq i hi) (hμ i hi) (hNA i hi)
  have hweightNonneg i (hi : i∈S) :
      0 ≤ Real.sqrt (2*q i)/(q i*Real.sqrt (μ i*A i)) := by
    have hq : 0 ≤ q i := by linarith only [hQ,hQq i hi]
    exact div_nonneg (Real.sqrt_nonneg _) (mul_nonneg hq (Real.sqrt_nonneg _))
  have hs : (∑ i∈S, (Real.sqrt (2*q i)/(q i*Real.sqrt (μ i*A i)))*‖z i‖) ≤
      Real.sqrt B*(∑ i∈S,‖z i‖) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i hi
    exact mul_le_mul_of_nonneg_right (hweight i hi) (norm_nonneg _)
  have hs0 : 0 ≤ ∑ i∈S, (Real.sqrt (2*q i)/(q i*Real.sqrt (μ i*A i)))*‖z i‖ :=
    Finset.sum_nonneg (fun i hi => mul_nonneg (hweightNonneg i hi) (norm_nonneg _))
  have hp := pow_le_pow_left₀ hs0 hs 12
  have hpow : (Real.sqrt B)^12=B^6 := by
    rw [show (12:ℕ)=2*6 by norm_num,pow_mul,Real.sq_sqrt hB]
  rw [mul_pow,hpow] at hp
  exact hp


/-- The actual source-family sieve with all joint-color weights absorbed and
its literal block/parity cardinality linked to the physical M/N scale. -/
theorem eventually_positive_difference_actual_family_physical_sieve
    {σsrc csrc Usrc E σ εloss : ℝ}
    (hσsrc : 0 < σsrc) (hcsrc : 0 < csrc) (hUsrc : 0 < Usrc)
    (hE : 0 < E) (hσ : 0 < σ) (hεloss : 0 < εloss) :
    let κ := modelPhaseThirdLower σ
    let Ratio := 18*Usrc^2*E/(σsrc*csrc*κ)
    let L := max (8*Ratio^2)
      (32*(modelPhaseJetCoefficient σ 3+1)*(3*Usrc/σsrc)*E/κ^2)
    ∃ η₀ a Cupper Clower Dupper Dlower C Dtype : ℝ,
      0 < η₀ ∧ η₀ ≤ 1/8 ∧ 0 < a ∧
      0 < Cupper ∧ 0 < Clower ∧ 0 < Dupper ∧ 0 < Dlower ∧ 0 < C ∧ 0 < Dtype ∧
    ∀ {Jref θ : ℝ}, 0 ≤ Jref → 0 < θ → θ ≤ 1/24 → θ ≤ 1/(8*(L+3)) →
    ∀ᶠ T : ℝ in Filter.atTop, ∀ (S : Finset (ℝ × ℤ)) (Fsrc : ℝ → ℝ)
    (z : (ℝ × ℤ) → ℝ) (rat : (ℝ × ℤ) → ℚ) (v : (ℝ × ℤ) → ℤ) (Nlen : (ℝ × ℤ) → ℕ)
    (Q K₀ N : ℕ) [NeZero K₀] (Vscale R Jsep : ℝ) (Z : ℝ → ℤ)
    {η Tsrc M δ Bcut Bselect : ℝ}
    (Uref : ℕ) (Refs : Finset ℝ) (Gaps : Finset (ℝ × ℝ))
    (A : ℝ → ℤ) (W : ℝ → ℝ) (gap : (ℝ × ℤ) → ℝ × ℝ)
    (anchor : (ℝ × ℤ) → ℚ) (e r vRef s : ℝ × ℝ → ℤ),
    (0 < η) →
    (η ≤ η₀) →
    (0 < Tsrc) →
    (0 < T) →
    (0 < M) →
    (δ ≤ min (modelPhaseThirdLower σ) 1) →
    (Tsrc ≤ E*T) →
    (0 < Q) →
    (∀ i∈S, i.1∈Icc (1:ℝ) 2) →
    (∀ i∈S, z i∈Icc M (2*M)) →
    (∀ w, 0 < w → ContDiffAt ℝ ∞ Fsrc w) →
    (∀ w∈Icc (1/2:ℝ) 3, ∀ n ≤ 6, |iteratedDeriv (n+1) Fsrc w| ≤ Usrc) →
    (∀ w∈Icc (1/2:ℝ) 3, ∀ j,
      csrc ≤ |HuxleyModel.tests (fun i : Fin 4 => iteratedDeriv (i.val+3) Fsrc w) j|) →
    (∀ i∈S, (rat i).den ≤ Q ∧ Q ≤ 2*(rat i).den) →
    (∀ i∈S, ((rat i).den:ℤ) ∣ (rat i).num*v i-1) →
    (∀ w∈Icc (1/2:ℝ) 3, iteratedDeriv 4 Fsrc w ≤ -csrc) →
    (2 ≤ M) →
    (1 ≤ Vscale) →
    (0 < N) →
    (0 < Jsep) → (Jsep ≤ M) → ((N:ℝ) ≤ M) →
    ((Q:ℝ)*(N:ℝ) ≤ (K₀:ℝ)*R^2) →
    (∀ i∈S, N ≤ Nlen i ∧ Nlen i ≤ 3*N ∧
      round (z i)+(Nlen i:ℤ)=Z i.1+(N:ℤ)*i.2+2*(N:ℤ)) →
    (∀ i∈S, ∀ j∈S, i.1≠j.1 → 1 ≤ Jsep*|i.1-j.1|) →
    let Fmodel := fun (i : ℝ × ℤ) u => (Tsrc/T)*(Fsrc u-Fsrc (u+η*i.1))/(σsrc*η)
    (∀ i∈S, Expdb.IsApproximateModelPhaseFunction (Fmodel i) σ 4 δ) →
    let f := fun p w => Tsrc*(Fsrc (w/M)-Fsrc (w/M+η*p))/(σsrc*η)
    (∀ i∈S, iteratedDeriv 2 (f (i.1)) (z i)/2=(rat i:ℝ)) →
    (∀ i∈S, 1 ≤ Nlen i ∧ (rat i).den ≤ Nlen i ∧
      1 ≤ (iteratedDeriv 3 (f (i.1)) (round (z i))/6)*((rat i).den:ℝ)^2*Nlen i) →
    (∀ i∈S, 7*((iteratedDeriv 3 (f (i.1)) (round (z i))/6)*
      ((rat i).den:ℝ)*(Nlen i:ℝ)^2) ≤ K₀) →

    (N:ℝ)^4 ≤ M*R^3*(Real.log T)^((3:ℝ)/2) →
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
    (Q:ℝ) ≤ (N:ℝ) → (N:ℝ)^2 ≤ M → (Uref:ℝ) ≤ R^2 →
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
    let lambda := csrc*modelPhaseThirdLower σ*T/(12*Usrc*M^2)
    let Uband := (3*Usrc/σsrc)*E*T/(2*M^2)
    let u := fun (i : ℝ × ℤ) => (2*M^2/Tsrc)*(rat i:ℝ)
    let w := fun (i : ℝ × ℤ) => (Tsrc/(2*M^2))*(rat i:ℝ)⁻¹
    let chart := fun (i : ℝ × ℤ) => (⌊i.1/a⌋,⌊u i/a⌋,⌊w i/a⌋)
    let narrow := fun (i : ℝ × ℤ) =>
      (⌊((rat i).den:ℝ)/(θ*((Q:ℝ)/2))⌋,
       ⌊((rat i).num:ℝ)/(θ*(lambda*(Q:ℝ)/2))⌋)
    let qell := fun (i : ℝ × ℤ) => ((rat i).den:ℝ)*deriv (f (i.1)) (round (z i))
    let V := S ×ˢ (Finset.univ : Finset (Fin 2))
    let offset := fun ip : (ℝ × ℤ) × Fin 2 => ⌊qell ip.1⌋+(ip.2:ℕ)-round (qell ip.1)
    let color := fun ip : (ℝ × ℤ) × Fin 2 => (chart ip.1,narrow ip.1,offset ip)
    let ChartCap := (4/a+3)*((6*Usrc/σsrc)/a+3)*((4*σsrc/csrc)/a+3)
    let NarrowCap := (4/θ+3)*(72*Usrc^2*E/(σsrc*csrc*modelPhaseThirdLower σ*θ)+3)
    let Cap := 3*ChartCap*NarrowCap

    let q := fun (i : ℝ × ℤ) => (rat i).den
    let μ := fun (i : ℝ × ℤ) => iteratedDeriv 3 (f (i.1)) (round (z i))/6
    let b := fun ip : (ℝ × ℤ) × Fin 2 => (⌊qell ip.1⌋+(ip.2:ℕ) : ℤ)
    let tau := fun ip : (ℝ × ℤ) × Fin 2 => ((b ip:ℝ)-qell ip.1)/2
    let dual := fun (i : ℝ × ℤ) => -2*μ i*(Real.sqrt (2/(3*μ i*(q i:ℝ))))^3
    let x := fun ip : (ℝ × ℤ) × Fin 2 =>
      (![-(v ip.1:ℝ)*b ip/q ip.1,-(v ip.1:ℝ)/q ip.1,
        dual ip.1,3*dual ip.1*tau ip/2] : Fin 4 → ℝ)
    let μ₀ := csrc*Tsrc/(12*σsrc*M^3)
    let U₀ := Usrc*Tsrc/(2*σsrc*M^3)
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
    let AupperConst := 2*Cupper*(Cthird+1)*E^2/(κ*Lunit^3)
    let BupperConst := Cupper*(Cthird+1)*E^2/Lunit^2+Dupper*(B+1)*E^2/4
    let AlowerConst := 8*Clower*(Cthird+1)/(κ*Lunit^3)
    let BlowerConst := 4*Clower*(Cthird+1)/Lunit^2+Dlower*(B+1)
    let DupperConst := θ*(3*Usrc/σsrc)*E/2
    let DlowerConst := 12*Usrc*θ/(csrc*κ)
    let CostUpper := M^2/((N:ℝ)^4*(Uref:ℝ))
    let CostLower := R^4/((N:ℝ)^2*(Uref:ℝ))
    let Cpack := 64*Cphys*(Gamma^2*Cthird+Gamma*(modelPhaseJetCoefficient σ 3+δ)/κ)/κ
    let Cfirst := 128*Cphys*(Gamma^2*Cthird+Gamma*(modelPhaseJetCoefficient σ 3+δ)/κ)/κ^2
    let Cgap := 64*Cphys*(Gamma^2*B+Gamma*(modelPhaseJetCoefficient σ 3+δ)/κ)/κ
    let Cmain := 4*(2*Cfirst/Lunit^3)^((3:ℝ)⁻¹)+2
    let Ctail := 4*Cpack/Lunit^2+Cgap
    let Kupper := 240*CostUpper*
      (9*(AupperConst*DupperConst^2)^((3:ℝ)⁻¹)+2*BupperConst+(3/2:ℝ)*DupperConst)
    let Klower := 240*CostLower*
      (9*(AlowerConst*DlowerConst^2)^((3:ℝ)⁻¹)+2*BlowerConst+(3/2:ℝ)*DlowerConst)
    let Klarge := 2*Bselect*60*588*(Uband/lambda)^2*Uband^2*(R^8/(N:ℝ)^4)*
      (Cmain+Ctail)*((Q:ℝ)/(N:ℝ))^((2:ℝ)/3)

    Vscale=(Uref:ℝ)^((3:ℝ)/2) →
    ((N:ℝ)/(Q:ℝ))^((2:ℝ)/3)/(2*Bselect) ≤ (Uref:ℝ) →
    let Y := S.image Prod.fst
    ((V.image color).card:ℝ) ≤ Cap ∧
    (V.card:ℝ) ≤ 10*(Y.card:ℝ)*(M/(N:ℝ)) ∧
    (∀ k : ZMod K₀,
      (∑ ip∈V, ‖∑ j : ZMod K₀, ZMod.stdAddChar (-(j*k))*
        GafniTao.fordAdditiveCharacter (∑ d,x ip d*
          (![(j.val+1:ℝ),(j.val+1:ℝ)^2,(j.val+1:ℝ)^((3:ℝ)/2),
            Real.sqrt (j.val+1:ℝ)] : Fin 4 → ℝ) d)‖)^12 ≤
        C*(K₀:ℝ)^((12:ℝ)+εloss)*Cap^11*
          (10*(Y.card:ℝ)*(M/(N:ℝ)))^10*
            (Vscale*Dtype*(Y.card:ℝ)*(M/(N:ℝ))*(1+Δtype*Jsep)+
              (Y.card:ℝ)^2*(Vscale*(Kupper+Klower)+Klarge)*T^εloss)) ∧
    ∀ k : ZMod K₀,
      (∑ ip∈V, (Real.sqrt (2*(q ip.1:ℝ))/
        ((q ip.1:ℝ)*Real.sqrt (μ ip.1*(Nlen ip.1:ℝ))))*
        ‖∑ j : ZMod K₀, ZMod.stdAddChar (-(j*k))*
          GafniTao.fordAdditiveCharacter (∑ d,x ip d*
            (![(j.val+1:ℝ),(j.val+1:ℝ)^2,(j.val+1:ℝ)^((3:ℝ)/2),
              Real.sqrt (j.val+1:ℝ)] : Fin 4 → ℝ) d)‖)^12 ≤
        (144*Usrc/(csrc*κ))^6*(R^2/(Q:ℝ))^6*
          C*(K₀:ℝ)^((12:ℝ)+εloss)*Cap^11*
          (10*(Y.card:ℝ)*(M/(N:ℝ)))^10*
            (Vscale*Dtype*(Y.card:ℝ)*(M/(N:ℝ))*(1+Δtype*Jsep)+
              (Y.card:ℝ)^2*(Vscale*(Kupper+Klower)+Klarge)*T^εloss)
 := by
  classical
  intro κ Ratio L
  obtain ⟨η₀,a,Cupper,Clower,Dupper,Dlower,C,Dtype,
      hη₀,hηcap,ha,hCU,hCL,hDU,hDL,hC,hDtype,hsource⟩ :=
    eventually_positive_difference_actual_family_source_sieve hσsrc hcsrc hUsrc hE hσ hεloss
  refine ⟨η₀,a,Cupper,Clower,Dupper,Dlower,C,Dtype,
    hη₀,hηcap,ha,hCU,hCL,hDU,hDL,hC,hDtype,?_⟩
  intro Jref θ hJref hθ hθmax hθaction
  filter_upwards [hsource hJref hθ hθmax hθaction] with T hfamily
  intro S Fsrc z rat v Nlen Q K₀ N instK Vscale R Jsep Z
    η Tsrc M δ Bcut Bselect Uref Refs Gaps A W gap anchor e r vRef s
    hη hηsmall hTsrc hT hM hδ hsourceScale hQ
    hy hz hreg hjets htests hden hinv hnegative hMtwo hVscale hN
    hJsep hJM hNM hmesh hgeometry hseparation Fmodel hmodel f hlevel hminor hcomplete
    hregime hR hRM hscale hA hW xlocal hx hgapMem
    hchart horientation hBcut hs hrefSet hparentSet hsep hwideL hwideU hUref
    hBselectSize hcutMargin hselectedWrap hreferenceDen hgapWidth hRQ
    hselectedUpper hscaleTen hfamilyGap hgap hQN hNsqM hUR
    hrHeight hsHeight heHeight hvHeight Cphys c J B hsmall hNR hRN hNcube hminscale
    H hNtwo hL hU ε hanchor hcut hcount
    lambda Uband u w chart narrow qell V offset color ChartCap NarrowCap Cap
    q μ b tau dual x μ₀ U₀ Δtype
    C₂ C₃ Ct Cc Δ Ccurv D Kres Esize Dbase Tbase hsize hD hΔ hBsize
    Lunit Gamma Cthird AupperConst BupperConst AlowerConst BlowerConst
    DupperConst DlowerConst CostUpper CostLower Cpack Cfirst Cgap Cmain Ctail
    Kupper Klower Klarge hvchoice hUlo Y

  obtain ⟨hcard,hweighted⟩ := hfamily S Fsrc z rat v Nlen Q K₀ N Vscale R Jsep Z
    (η:=η) (Tsrc:=Tsrc) (M:=M) (δ:=δ) (Bcut:=Bcut) (Bselect:=Bselect)
    Uref Refs Gaps A W gap anchor e r vRef s
    hη hηsmall hTsrc hT hM hδ hsourceScale hQ
    hy hz hreg hjets htests hden hinv hnegative hMtwo hVscale hN
    hJsep hJM hNM hmesh hgeometry hseparation hmodel hlevel hminor hcomplete
    hregime hR hRM hscale hA hW hx hgapMem
    hchart horientation hBcut hs hrefSet hparentSet hsep hwideL hwideU hUref
    hBselectSize hcutMargin hselectedWrap hreferenceDen hgapWidth hRQ
    hselectedUpper hscaleTen hfamilyGap hgap hQN hNsqM hUR
    hrHeight hsHeight heHeight hvHeight hsmall hNR hRN hNcube hminscale
    hNtwo hL hU hanchor hcut hcount hsize hD hΔ hBsize hvchoice hUlo
  let Values := fun k : ZMod K₀ =>
    ∑ ip∈V, ‖∑ j : ZMod K₀, ZMod.stdAddChar (-(j*k))*
      GafniTao.fordAdditiveCharacter (∑ d,x ip d*
        (![(j.val+1:ℝ),(j.val+1:ℝ)^2,(j.val+1:ℝ)^((3:ℝ)/2),
          Real.sqrt (j.val+1:ℝ)] : Fin 4 → ℝ) d)‖
  let Scale := C*(K₀:ℝ)^((12:ℝ)+εloss)*Cap^11
  let Mass := Vscale*Dtype*(Y.card:ℝ)*(M/(N:ℝ))*(1+Δtype*Jsep)+
    (Y.card:ℝ)^2*(Vscale*(Kupper+Klower)+Klarge)*T^εloss
  change ∀ k, (Values k)^12 ≤ Scale*(∑ key∈V.image color,
    ((V.filter (fun ip => color ip=key)).card:ℝ)^10*Mass) at hweighted
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
  have hplain k : (Values k)^12 ≤ Scale*(10*(Y.card:ℝ)*(M/(N:ℝ)))^10*Mass := by
    have hValues : 0 ≤ Values k := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
    have hu : (Values k)^12 ≤ Scale*(V.card:ℝ)^10*Mass :=
      actual_color_tenth_weight_absorption V color (pow_nonneg hValues 12) (hweighted k)
    change (Values k)^12 ≤ Scale*(10*(Y.card:ℝ)*(M/(N:ℝ)))^10*Mass
    by_cases hV : V=∅
    · have hY : Y=∅ := by rw [←hYimage,hV,Finset.image_empty]
      simpa only [hV,hY,Finset.card_empty,Nat.cast_zero,mul_zero,zero_mul,
        zero_pow (by decide : (10:ℕ)≠0)] using hu
    · have hVpos : (0:ℝ) < V.card :=
        Nat.cast_pos.mpr (Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hV))
      have hsign : 0 ≤ Scale*Mass := by
        have hn : 0 ≤ (Scale*Mass)*(V.card:ℝ)^10 := by
          calc
            0 ≤ (Values k)^12 := pow_nonneg hValues 12
            _ ≤ Scale*(V.card:ℝ)^10*Mass := hu
            _ = _ := by ac_rfl
        exact nonneg_of_mul_nonneg_left hn (pow_pos hVpos 10)
      calc
        (Values k)^12 ≤ Scale*(V.card:ℝ)^10*Mass := hu
        _ = (Scale*Mass)*(V.card:ℝ)^10 := by ac_rfl
        _ ≤ (Scale*Mass)*(10*(Y.card:ℝ)*(M/(N:ℝ)))^10 :=
          mul_le_mul_of_nonneg_left
            (pow_le_pow_left₀ (Nat.cast_nonneg _) hphysical 10) hsign
        _ = _ := by ac_rfl
  refine ⟨hcard,hphysical,hplain,?_⟩
  intro k
  by_cases hSnonempty : S.Nonempty
  · have hκ : 0 < κ := modelPhaseThirdLower_pos hσ
    have hRp : 0 < R := zero_lt_one.trans_le hR
    obtain ⟨i₀,hi₀⟩ := hSnonempty
    have hAmp := positive_difference_approximate_model_source_amplitude Fsrc
      hσsrc hUsrc hη (hηsmall.trans hηcap) (hy i₀ hi₀) hTsrc hT hσ hδ hreg hjets
      (approximateModelPhase_mono (hmodel i₀ hi₀) (by norm_num : 2 ≤ 4) le_rfl)
    have hμphysical : csrc*κ/(36*Usrc*R^2) ≤ μ₀*(N:ℝ) := by
      calc
        csrc*κ/(36*Usrc*R^2)=
            (csrc*(N:ℝ)/(12*σsrc*M^3))*(κ*σsrc*T/(3*Usrc)) := by
          rw [←hscale]
          field_simp
          norm_num
        _ ≤ (csrc*(N:ℝ)/(12*σsrc*M^3))*Tsrc :=
          mul_le_mul_of_nonneg_left hAmp (by positivity)
        _ = μ₀*(N:ℝ) := by dsimp only [μ₀]; ring
    let Wphys := (144*Usrc/(csrc*κ))*(R^2/(Q:ℝ))
    have hWphys : 0 ≤ Wphys := by dsimp only [Wphys]; positivity
    have hWeightScale : 4/((Q:ℝ)*(μ₀*(N:ℝ))) ≤ Wphys := by
      have hi := one_div_le_one_div_of_le
        (by positivity : 0 < csrc*κ/(36*Usrc*R^2)) hμphysical
      calc
        _ = (4/(Q:ℝ))*(1/(μ₀*(N:ℝ))) := by ring
        _ ≤ (4/(Q:ℝ))*(1/(csrc*κ/(36*Usrc*R^2))) :=
          mul_le_mul_of_nonneg_left hi (by positivity)
        _ = Wphys := by dsimp only [Wphys]; field_simp; ring
    have hμ₀ : 0 < μ₀ := by dsimp only [μ₀]; positivity
    have hμbounds i (hi : i∈S) : μ₀ ≤ μ i := by
      have hb := positive_difference_rounded_cubic_scales Fsrc (T:=Tsrc) (N:=M^3/Tsrc) (R:=1)
        hσsrc hcsrc hUsrc hη (hηsmall.trans hηcap) (hy i hi) hreg hjets hnegative hMtwo
        (by positivity) (by norm_num) (hz i hi) (by field_simp)
      have hlo : csrc/(12*σsrc*(M^3/Tsrc)*(1:ℝ)^2)=μ₀ := by
        dsimp only [μ₀]
        field_simp
      rw [hlo] at hb
      exact hb.1
    let dualValue := fun ip : (ℝ × ℤ) × Fin 2 =>
      ∑ j : ZMod K₀, ZMod.stdAddChar (-(j*k))*
        GafniTao.fordAdditiveCharacter (∑ d,x ip d*
          (![(j.val+1:ℝ),(j.val+1:ℝ)^2,(j.val+1:ℝ)^((3:ℝ)/2),
            Real.sqrt (j.val+1:ℝ)] : Fin 4 → ℝ) d)
    have hc := cubic_completion_weighted_twelfth V
      (fun ip => (q ip.1:ℝ)) (fun ip => μ ip.1) (fun ip => (Nlen ip.1:ℝ)) dualValue
      (Nat.cast_pos.mpr hQ) hμ₀ hNpos
      (fun ip hip => by
        change (Q:ℝ) ≤ 2*((rat ip.1).den:ℝ)
        exact_mod_cast (hden ip.1 (Finset.mem_product.mp hip).1).2)
      (fun ip hip => hμbounds ip.1 (Finset.mem_product.mp hip).1)
      (fun ip hip => by
        change (N:ℝ) ≤ (Nlen ip.1:ℝ)
        exact_mod_cast (hgeometry ip.1 (Finset.mem_product.mp hip).1).1)
    change (∑ ip∈V, (Real.sqrt (2*(q ip.1:ℝ))/
      ((q ip.1:ℝ)*Real.sqrt (μ ip.1*(Nlen ip.1:ℝ))))*‖dualValue ip‖)^12 ≤
        (4/((Q:ℝ)*(μ₀*(N:ℝ))))^6*(Values k)^12 at hc
    calc
      _ ≤ (4/((Q:ℝ)*(μ₀*(N:ℝ))))^6*(Values k)^12 := hc
      _ ≤ Wphys^6*(Values k)^12 :=
        mul_le_mul_of_nonneg_right
          (pow_le_pow_left₀ (by positivity) hWeightScale 6)
          (pow_nonneg (Finset.sum_nonneg (fun _ _ => norm_nonneg _)) 12)
      _ ≤ Wphys^6*(Scale*(10*(Y.card:ℝ)*(M/(N:ℝ)))^10*Mass) :=
        mul_le_mul_of_nonneg_left (hplain k) (pow_nonneg hWphys 6)
      _ = _ := by
        dsimp only [Wphys,Scale]
        rw [mul_pow]
        simp only [Mass,mul_assoc]
  · have hS : S=∅ := Finset.not_nonempty_iff_eq_empty.mp hSnonempty
    have hV : V=∅ := by simp only [V,hS,Finset.empty_product]
    have hY : Y=∅ := by simp only [Y,hS,Finset.image_empty]
    simp only [hV,hY,Finset.sum_empty,Finset.card_empty,Nat.cast_zero,
      mul_zero,zero_mul,zero_pow (by decide : (12:ℕ)≠0),zero_pow (by decide : (10:ℕ)≠0),le_refl]


example
    {σsrc csrc Usrc E σ εloss : ℝ}
    (hσsrc : 0 < σsrc) (hcsrc : 0 < csrc) (hUsrc : 0 < Usrc)
    (hE : 0 < E) (hσ : 0 < σ) (hεloss : 0 < εloss) :
    let κ := modelPhaseThirdLower σ
    let Ratio := 18*Usrc^2*E/(σsrc*csrc*κ)
    let L := max (8*Ratio^2)
      (32*(modelPhaseJetCoefficient σ 3+1)*(3*Usrc/σsrc)*E/κ^2)
    ∃ η₀ a Cupper Clower Dupper Dlower C Dtype : ℝ,
      0 < η₀ ∧ η₀ ≤ 1/8 ∧ 0 < a ∧
      0 < Cupper ∧ 0 < Clower ∧ 0 < Dupper ∧ 0 < Dlower ∧ 0 < C ∧ 0 < Dtype ∧
    ∀ {Jref θ : ℝ}, 0 ≤ Jref → 0 < θ → θ ≤ 1/24 → θ ≤ 1/(8*(L+3)) →
    ∀ᶠ T : ℝ in Filter.atTop, ∀ (S : Finset (ℝ × ℤ)) (Fsrc : ℝ → ℝ)
    (z : (ℝ × ℤ) → ℝ) (rat : (ℝ × ℤ) → ℚ) (v : (ℝ × ℤ) → ℤ) (Nlen : (ℝ × ℤ) → ℕ)
    (Q K₀ N : ℕ) [NeZero K₀] (Vscale R Jsep : ℝ) (Z : ℝ → ℤ)
    {η Tsrc M δ Bcut Bselect : ℝ}
    (Uref : ℕ) (Refs : Finset ℝ) (Gaps : Finset (ℝ × ℝ))
    (A : ℝ → ℤ) (W : ℝ → ℝ) (gap : (ℝ × ℤ) → ℝ × ℝ)
    (anchor : (ℝ × ℤ) → ℚ) (e r vRef s : ℝ × ℝ → ℤ),
    (0 < η) →
    (η ≤ η₀) →
    (0 < Tsrc) →
    (0 < T) →
    (0 < M) →
    (δ ≤ min (modelPhaseThirdLower σ) 1) →
    (Tsrc ≤ E*T) →
    (0 < Q) →
    (∀ i∈S, i.1∈Icc (1:ℝ) 2) →
    (∀ i∈S, z i∈Icc M (2*M)) →
    (∀ w, 0 < w → ContDiffAt ℝ ∞ Fsrc w) →
    (∀ w∈Icc (1/2:ℝ) 3, ∀ n ≤ 6, |iteratedDeriv (n+1) Fsrc w| ≤ Usrc) →
    (∀ w∈Icc (1/2:ℝ) 3, ∀ j,
      csrc ≤ |HuxleyModel.tests (fun i : Fin 4 => iteratedDeriv (i.val+3) Fsrc w) j|) →
    (∀ i∈S, (rat i).den ≤ Q ∧ Q ≤ 2*(rat i).den) →
    (∀ i∈S, ((rat i).den:ℤ) ∣ (rat i).num*v i-1) →
    (∀ w∈Icc (1/2:ℝ) 3, iteratedDeriv 4 Fsrc w ≤ -csrc) →
    (2 ≤ M) →
    (1 ≤ Vscale) →
    (0 < N) →
    (0 < Jsep) → (Jsep ≤ M) → ((N:ℝ) ≤ M) →
    ((Q:ℝ)*(N:ℝ) ≤ (K₀:ℝ)*R^2) →
    (∀ i∈S, N ≤ Nlen i ∧ Nlen i ≤ 3*N ∧
      round (z i)+(Nlen i:ℤ)=Z i.1+(N:ℤ)*i.2+2*(N:ℤ)) →
    (∀ i∈S, ∀ j∈S, i.1≠j.1 → 1 ≤ Jsep*|i.1-j.1|) →
    let Fmodel := fun (i : ℝ × ℤ) u => (Tsrc/T)*(Fsrc u-Fsrc (u+η*i.1))/(σsrc*η)
    (∀ i∈S, Expdb.IsApproximateModelPhaseFunction (Fmodel i) σ 4 δ) →
    let f := fun p w => Tsrc*(Fsrc (w/M)-Fsrc (w/M+η*p))/(σsrc*η)
    (∀ i∈S, iteratedDeriv 2 (f (i.1)) (z i)/2=(rat i:ℝ)) →
    (∀ i∈S, 1 ≤ Nlen i ∧ (rat i).den ≤ Nlen i ∧
      1 ≤ (iteratedDeriv 3 (f (i.1)) (round (z i))/6)*((rat i).den:ℝ)^2*Nlen i) →
    (∀ i∈S, 7*((iteratedDeriv 3 (f (i.1)) (round (z i))/6)*
      ((rat i).den:ℝ)*(Nlen i:ℝ)^2) ≤ K₀) →

    (N:ℝ)^4 ≤ M*R^3*(Real.log T)^((3:ℝ)/2) →
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
    (Q:ℝ) ≤ (N:ℝ) → (N:ℝ)^2 ≤ M → (Uref:ℝ) ≤ R^2 →
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
    let lambda := csrc*modelPhaseThirdLower σ*T/(12*Usrc*M^2)
    let Uband := (3*Usrc/σsrc)*E*T/(2*M^2)
    let u := fun (i : ℝ × ℤ) => (2*M^2/Tsrc)*(rat i:ℝ)
    let w := fun (i : ℝ × ℤ) => (Tsrc/(2*M^2))*(rat i:ℝ)⁻¹
    let chart := fun (i : ℝ × ℤ) => (⌊i.1/a⌋,⌊u i/a⌋,⌊w i/a⌋)
    let narrow := fun (i : ℝ × ℤ) =>
      (⌊((rat i).den:ℝ)/(θ*((Q:ℝ)/2))⌋,
       ⌊((rat i).num:ℝ)/(θ*(lambda*(Q:ℝ)/2))⌋)
    let qell := fun (i : ℝ × ℤ) => ((rat i).den:ℝ)*deriv (f (i.1)) (round (z i))
    let V := S ×ˢ (Finset.univ : Finset (Fin 2))
    let offset := fun ip : (ℝ × ℤ) × Fin 2 => ⌊qell ip.1⌋+(ip.2:ℕ)-round (qell ip.1)
    let color := fun ip : (ℝ × ℤ) × Fin 2 => (chart ip.1,narrow ip.1,offset ip)
    let ChartCap := (4/a+3)*((6*Usrc/σsrc)/a+3)*((4*σsrc/csrc)/a+3)
    let NarrowCap := (4/θ+3)*(72*Usrc^2*E/(σsrc*csrc*modelPhaseThirdLower σ*θ)+3)
    let Cap := 3*ChartCap*NarrowCap

    let q := fun (i : ℝ × ℤ) => (rat i).den
    let μ := fun (i : ℝ × ℤ) => iteratedDeriv 3 (f (i.1)) (round (z i))/6
    let b := fun ip : (ℝ × ℤ) × Fin 2 => (⌊qell ip.1⌋+(ip.2:ℕ) : ℤ)
    let tau := fun ip : (ℝ × ℤ) × Fin 2 => ((b ip:ℝ)-qell ip.1)/2
    let dual := fun (i : ℝ × ℤ) => -2*μ i*(Real.sqrt (2/(3*μ i*(q i:ℝ))))^3
    let x := fun ip : (ℝ × ℤ) × Fin 2 =>
      (![-(v ip.1:ℝ)*b ip/q ip.1,-(v ip.1:ℝ)/q ip.1,
        dual ip.1,3*dual ip.1*tau ip/2] : Fin 4 → ℝ)
    let μ₀ := csrc*Tsrc/(12*σsrc*M^3)
    let U₀ := Usrc*Tsrc/(2*σsrc*M^3)
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
    let AupperConst := 2*Cupper*(Cthird+1)*E^2/(κ*Lunit^3)
    let BupperConst := Cupper*(Cthird+1)*E^2/Lunit^2+Dupper*(B+1)*E^2/4
    let AlowerConst := 8*Clower*(Cthird+1)/(κ*Lunit^3)
    let BlowerConst := 4*Clower*(Cthird+1)/Lunit^2+Dlower*(B+1)
    let DupperConst := θ*(3*Usrc/σsrc)*E/2
    let DlowerConst := 12*Usrc*θ/(csrc*κ)
    let CostUpper := M^2/((N:ℝ)^4*(Uref:ℝ))
    let CostLower := R^4/((N:ℝ)^2*(Uref:ℝ))
    let Cpack := 64*Cphys*(Gamma^2*Cthird+Gamma*(modelPhaseJetCoefficient σ 3+δ)/κ)/κ
    let Cfirst := 128*Cphys*(Gamma^2*Cthird+Gamma*(modelPhaseJetCoefficient σ 3+δ)/κ)/κ^2
    let Cgap := 64*Cphys*(Gamma^2*B+Gamma*(modelPhaseJetCoefficient σ 3+δ)/κ)/κ
    let Cmain := 4*(2*Cfirst/Lunit^3)^((3:ℝ)⁻¹)+2
    let Ctail := 4*Cpack/Lunit^2+Cgap
    let Kupper := 240*CostUpper*
      (9*(AupperConst*DupperConst^2)^((3:ℝ)⁻¹)+2*BupperConst+(3/2:ℝ)*DupperConst)
    let Klower := 240*CostLower*
      (9*(AlowerConst*DlowerConst^2)^((3:ℝ)⁻¹)+2*BlowerConst+(3/2:ℝ)*DlowerConst)
    let Klarge := 2*Bselect*60*588*(Uband/lambda)^2*Uband^2*(R^8/(N:ℝ)^4)*
      (Cmain+Ctail)*((Q:ℝ)/(N:ℝ))^((2:ℝ)/3)

    Vscale=(Uref:ℝ)^((3:ℝ)/2) →
    ((N:ℝ)/(Q:ℝ))^((2:ℝ)/3)/(2*Bselect) ≤ (Uref:ℝ) →
    let Y := S.image Prod.fst
    ((V.image color).card:ℝ) ≤ Cap ∧
    (V.card:ℝ) ≤ 10*(Y.card:ℝ)*(M/(N:ℝ)) ∧
    (∀ k : ZMod K₀,
      (∑ ip∈V, ‖∑ j : ZMod K₀, ZMod.stdAddChar (-(j*k))*
        GafniTao.fordAdditiveCharacter (∑ d,x ip d*
          (![(j.val+1:ℝ),(j.val+1:ℝ)^2,(j.val+1:ℝ)^((3:ℝ)/2),
            Real.sqrt (j.val+1:ℝ)] : Fin 4 → ℝ) d)‖)^12 ≤
        C*(K₀:ℝ)^((12:ℝ)+εloss)*Cap^11*
          (10*(Y.card:ℝ)*(M/(N:ℝ)))^10*
            (Vscale*Dtype*(Y.card:ℝ)*(M/(N:ℝ))*(1+Δtype*Jsep)+
              (Y.card:ℝ)^2*(Vscale*(Kupper+Klower)+Klarge)*T^εloss)) ∧
    ∀ k : ZMod K₀,
      (∑ ip∈V, (Real.sqrt (2*(q ip.1:ℝ))/
        ((q ip.1:ℝ)*Real.sqrt (μ ip.1*(Nlen ip.1:ℝ))))*
        ‖∑ j : ZMod K₀, ZMod.stdAddChar (-(j*k))*
          GafniTao.fordAdditiveCharacter (∑ d,x ip d*
            (![(j.val+1:ℝ),(j.val+1:ℝ)^2,(j.val+1:ℝ)^((3:ℝ)/2),
              Real.sqrt (j.val+1:ℝ)] : Fin 4 → ℝ) d)‖)^12 ≤
        (144*Usrc/(csrc*κ))^6*(R^2/(Q:ℝ))^6*
          C*(K₀:ℝ)^((12:ℝ)+εloss)*Cap^11*
          (10*(Y.card:ℝ)*(M/(N:ℝ)))^10*
            (Vscale*Dtype*(Y.card:ℝ)*(M/(N:ℝ))*(1+Δtype*Jsep)+
              (Y.card:ℝ)^2*(Vscale*(Kupper+Klower)+Klarge)*T^εloss)
 :=
  HuxleyActualFamilyPhysicalScratch.eventually_positive_difference_actual_family_physical_sieve (σsrc:=σsrc) (csrc:=csrc) (Usrc:=Usrc) (E:=E) (σ:=σ) (εloss:=εloss) hσsrc hcsrc hUsrc hE hσ hεloss

#print axioms actual_color_tenth_weight_bound
#print axioms actual_color_tenth_weight_absorption
#print axioms cubic_completion_weight_bound
#print axioms cubic_completion_weighted_twelfth
#print axioms positive_difference_approximate_model_source_amplitude
#print axioms eventually_positive_difference_actual_family_physical_sieve
end HuxleyActualFamilyPhysicalScratch
