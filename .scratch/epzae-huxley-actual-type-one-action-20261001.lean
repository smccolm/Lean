import TaoTrudgianYang2025.HuxleyLinearForms

open Set TaoTrudgianYang2025 TaoTrudgianYang2025.HuxleyRationalPhase
open scoped BigOperators Classical ContDiff
namespace HuxleyActualTypeOneActionScratch

private theorem positive_difference_family_bounded_action_source_scale_at_action
    {σ c U L : ℝ} (hσ : 0 < σ) (hc : 0 < c) (hU : 0 < U) (hL : 0 ≤ L) :
    ∃ D : ℝ, 0 < D ∧
      ∀ (P : Finset (((ℝ × ℤ) × Fin 2) × ((ℝ × ℤ) × Fin 2)))
        (Mat : (((ℝ × ℤ) × Fin 2) × ((ℝ × ℤ) × Fin 2)) → Fin 4 → ℤ)
        (F : ℝ → ℝ) (z : ℝ → ℤ → ℝ) (Alen : ℝ → ℤ → ℕ)
        (N : ℕ) (Z : ℝ → ℤ) (η Δ J T M : ℝ),
      0 < η → η ≤ 1/8 →
      (∀ w, 0 < w → ContDiffAt ℝ ∞ F w) →
      (∀ w∈Icc (1/2:ℝ) 3, ∀ n ≤ 6, |iteratedDeriv (n+1) F w| ≤ U) →
      (∀ w∈Icc (1/2:ℝ) 3, ∀ j,
        c ≤ |TaoTrudgianYang2025.HuxleyModel.tests
          (fun i : Fin 4 => iteratedDeriv (i.val+3) F w) j|) →
      (∀ w∈Icc (1/2:ℝ) 3, iteratedDeriv 4 F w ≤ -c) →
      0 < T → 2 ≤ M → 0 < N → 0 ≤ Δ → 0 < J → (N:ℝ) ≤ M → J ≤ M →
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
      (∀ ij∈P, Mat ij 0*Mat ij 3-Mat ij 1*Mat ij 2=1) →
      (∀ ij∈P, Mat ij 1 ≠ 0 ∧ Mat ij 2 ≠ 0) →
      (∀ ij∈P, |(Mat ij 2:ℝ)| * ((3*U/σ)*T/(2*M^2)) ≤ L) →
      let f := fun y w => T*(F (w/M)-F (w/M+η*y))/(σ*η)
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
      (P.card:ℝ) ≤ D*((P.image (fun ij => ij.1.1.1)).card:ℝ)*
        (M/(N:ℝ))*(1+Δ*J) := by
  obtain ⟨K,C,hK,hC,hcount⟩ := positive_difference_family_bounded_action_pair_count hσ hc hU
  let B := max 1 (max (3*U/σ) (2*σ/c))
  let CMat := (2*(L+3)^2+1)*(2*L+5)^2*(L+3)^2
  have hB : 0 < B := zero_lt_one.trans_le (le_max_left _ _)
  have hCMat : 0 < CMat := by dsimp only [CMat]; positivity
  refine ⟨60*K*(1+40*C*B)*CMat,by positivity,?_⟩
  intro P Mat F z Alen N Z η Δ J T M hη hηmax hf hbound htests hnegative
    hT hM hN hΔ hJ hNM hJM hpoints hgeometryA hgeometryB hsep hdet hnontri haction
    f h μ t hmap hden hnum hthird
  classical
  have hMp : 0 < M := by linarith only [hM]
  have hNp : (0:ℝ) < N := by exact_mod_cast hN
  have hh := hcount P Mat F z Alen N Z η Δ J T M L hη hηmax hf hbound htests hnegative
    hT hM hN hΔ hJ hL hpoints hgeometryB hsep hdet hnontri haction hmap hden hnum hthird
  have hfirst := rounded_offset_family_point_count (P.image Prod.fst) z Alen N Z hMp.le hN
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
  have hJM' : J/M ≤ 1 := (div_le_iff₀ hMp).mpr (by simpa only [one_mul] using hJM)
  have hfactor : 1+8*C*B*(Δ+5/M)*J ≤ (1+40*C*B)*(1+Δ*J) := by
    calc
      _ = 1+8*C*B*(Δ*J+5*(J/M)) := by ring
      _ ≤ 1+8*C*B*(Δ*J+5) := by
        gcongr
        nlinarith only [hJM']
      _ ≤ _ := by
        have hp : 0 ≤ (32*C*B+1)*(Δ*J) := by positivity
        nlinarith only [hp]
  calc
    (P.card:ℝ) ≤ 6*K*(1+8*C*B*(Δ+5/M)*J)*CMat*((P.image Prod.fst).card:ℝ) := hh
    _ ≤ 6*K*((1+40*C*B)*(1+Δ*J))*CMat*(10*(M/(N:ℝ))*I) := by
      gcongr
    _ = _ := by ring

private theorem positive_difference_family_type_one_source_scale_at_action
    {σ c U L : ℝ} (hσ : 0 < σ) (hc : 0 < c) (hU : 0 < U) (hL : 0 ≤ L) :
    ∃ D : ℝ, 0 < D ∧
      ∀ (P : Finset (((ℝ × ℤ) × Fin 2) × ((ℝ × ℤ) × Fin 2)))
        (Mat : (((ℝ × ℤ) × Fin 2) × ((ℝ × ℤ) × Fin 2)) → Fin 4 → ℤ)
        (F : ℝ → ℝ) (z : ℝ → ℤ → ℝ) (Alen : ℝ → ℤ → ℕ)
        (N : ℕ) (Z : ℝ → ℤ) (η Δ J T M : ℝ),
      0 < η → η ≤ 1/8 →
      (∀ w, 0 < w → ContDiffAt ℝ ∞ F w) →
      (∀ w∈Icc (1/2:ℝ) 3, ∀ n ≤ 6, |iteratedDeriv (n+1) F w| ≤ U) →
      (∀ w∈Icc (1/2:ℝ) 3, ∀ j,
        c ≤ |TaoTrudgianYang2025.HuxleyModel.tests
          (fun i : Fin 4 => iteratedDeriv (i.val+3) F w) j|) →
      (∀ w∈Icc (1/2:ℝ) 3, iteratedDeriv 4 F w ≤ -c) →
      0 < T → 2 ≤ M → 0 < N → 0 ≤ Δ → 0 < J → (N:ℝ) ≤ M → J ≤ M →
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
      (∀ ij∈P, Mat ij 0*Mat ij 3-Mat ij 1*Mat ij 2=1) →
      (∀ ij∈P,
        (Mat ij 0=1 ∧ Mat ij 1=0 ∧ Mat ij 2=0 ∧ Mat ij 3=1) ∨
        (Mat ij 1≠0 ∧ Mat ij 2≠0 ∧ |(Mat ij 2:ℝ)| * ((3*U/σ)*T/(2*M^2)) ≤ L)) →
      let f := fun y w => T*(F (w/M)-F (w/M+η*y))/(σ*η)
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
      (P.card:ℝ) ≤ D*((P.image (fun ij => ij.1.1.1)).card:ℝ)*
        (M/(N:ℝ))*(1+Δ*J) := by
  obtain ⟨D₀,hD₀,hzero⟩ := positive_difference_family_identity_source_scale hσ hc hU
  obtain ⟨D₁,hD₁,hnonzero⟩ := positive_difference_family_bounded_action_source_scale_at_action hσ hc hU hL
  refine ⟨D₀+D₁,add_pos hD₀ hD₁,?_⟩
  intro P Mat F z Alen N Z η Δ J T M hη hηmax hf hbound htests hnegative
    hT hM hN hΔ hJ hNM hJM hpoints hgeometryA hgeometryB hsep hdet hbranch
    f h μ t hmap hden hnum hthird
  classical
  let P₀ := P.filter (fun ij => Mat ij 1=0)
  let P₁ := P.filter (fun ij => Mat ij 1≠0)
  have hlo ij (hij : ij∈P₀) : ij∈P ∧ Mat ij 1=0 := Finset.mem_filter.mp hij
  have hhi ij (hij : ij∈P₁) : ij∈P ∧ Mat ij 1≠0 := Finset.mem_filter.mp hij
  have hform ij (hij : ij∈P₀) :
      Mat ij 0=1 ∧ Mat ij 1=0 ∧ Mat ij 2=0 ∧ Mat ij 3=1 := by
    rcases hbranch ij (hlo ij hij).1 with ha | ha
    · exact ha
    · exact False.elim (ha.1 (hlo ij hij).2)
  have hnontri ij (hij : ij∈P₁) :
      Mat ij 1≠0 ∧ Mat ij 2≠0 ∧ |(Mat ij 2:ℝ)| * ((3*U/σ)*T/(2*M^2)) ≤ L :=
    (hbranch ij (hhi ij hij).1).resolve_left (fun ha => (hhi ij hij).2 ha.2.1)
  have h₀ := hzero P₀ F z Alen N Z η Δ J T M hη hηmax hf hbound htests hnegative
    hT hM hN hΔ hJ hNM hJM
    (fun ij hij => hpoints ij (hlo ij hij).1)
    (fun ij hij => hgeometryA ij (hlo ij hij).1)
    (fun ij hij => hgeometryB ij (hlo ij hij).1)
    (fun ij hij kl hkl hne => hsep ij (hlo ij hij).1 kl (hlo kl hkl).1 hne)
    (by
      intro ij hij
      have ha := hform ij hij
      have hh := (hmap ij (hlo ij hij).1).symm
      dsimp only [t] at hh
      simpa only [ha.1,ha.2.1,ha.2.2.1,ha.2.2.2,Int.cast_zero,Int.cast_one,
        zero_mul,one_mul,zero_add,add_zero,div_one] using hh)
    (by
      intro ij hij
      have ha := hform ij hij
      have hh := hthird ij (hlo ij hij).1
      dsimp only [t] at hh
      simpa only [ha.2.2.1,ha.2.2.2,Int.cast_zero,Int.cast_one,zero_mul,zero_add,one_pow,mul_one]
        using hh)
  have h₁ := hnonzero P₁ Mat F z Alen N Z η Δ J T M hη hηmax hf hbound htests hnegative
    hT hM hN hΔ hJ hNM hJM
    (fun ij hij => hpoints ij (hhi ij hij).1)
    (fun ij hij => hgeometryA ij (hhi ij hij).1)
    (fun ij hij => hgeometryB ij (hhi ij hij).1)
    (fun ij hij kl hkl hne => hsep ij (hhi ij hij).1 kl (hhi kl hkl).1 hne)
    (fun ij hij => hdet ij (hhi ij hij).1)
    (fun ij hij => ⟨(hnontri ij hij).1,(hnontri ij hij).2.1⟩)
    (fun ij hij => (hnontri ij hij).2.2)
    (fun ij hij => hmap ij (hhi ij hij).1)
    (fun ij hij => hden ij (hhi ij hij).1)
    (fun ij hij => hnum ij (hhi ij hij).1)
    (fun ij hij => hthird ij (hhi ij hij).1)
  have hI₀ : ((P₀.image (fun ij => ij.1.1.1)).card:ℝ) ≤
      ((P.image (fun ij => ij.1.1.1)).card:ℝ) := by
    exact_mod_cast Finset.card_le_card (Finset.image_subset_image
      (Finset.filter_subset (fun ij => Mat ij 1=0) P))
  have hI₁ : ((P₁.image (fun ij => ij.1.1.1)).card:ℝ) ≤
      ((P.image (fun ij => ij.1.1.1)).card:ℝ) := by
    exact_mod_cast Finset.card_le_card (Finset.image_subset_image
      (Finset.filter_subset (fun ij => Mat ij 1≠0) P))
  have hMp : 0 < M := by linarith only [hM]
  have hNp : (0:ℝ) < N := by exact_mod_cast hN
  have h₀' : (P₀.card:ℝ) ≤ D₀*((P.image (fun ij => ij.1.1.1)).card:ℝ)*
      (M/(N:ℝ))*(1+Δ*J) := h₀.trans (by gcongr)
  have h₁' : (P₁.card:ℝ) ≤ D₁*((P.image (fun ij => ij.1.1.1)).card:ℝ)*
      (M/(N:ℝ))*(1+Δ*J) := h₁.trans (by gcongr)
  have he : P.card=P₀.card+P₁.card := by
    exact (Finset.card_filter_add_card_filter_not (s:=P) (fun ij => Mat ij 1=0)).symm
  have heR : (P.card:ℝ)=(P₀.card:ℝ)+(P₁.card:ℝ) := by exact_mod_cast he
  rw [heR]
  calc
    _ ≤ D₀*((P.image (fun ij => ij.1.1.1)).card:ℝ)*(M/(N:ℝ))*(1+Δ*J)+
        D₁*((P.image (fun ij => ij.1.1.1)).card:ℝ)*(M/(N:ℝ))*(1+Δ*J) := add_le_add h₀' h₁'
    _ = _ := by ring

private theorem source_model_large_action_threshold
    {σsrc csrc Usrc E σ δ T M gamma : ℝ}
    (hσsrc : 0 < σsrc) (hcsrc : 0 < csrc) (hUsrc : 0 < Usrc)
    (hE : 0 < E) (hσ : 0 < σ) (hT : 0 < T) (hM : 0 < M)
    (hδ : δ ≤ 1) :
    let κ := modelPhaseThirdLower σ
    let lambda := csrc*κ*T/(12*Usrc*M^2)
    let Uband := (3*Usrc/σsrc)*E*T/(2*M^2)
    let Ratio := 18*Usrc^2*E/(σsrc*csrc*κ)
    let L := max (8*Ratio^2)
      (32*(modelPhaseJetCoefficient σ 3+1)*(3*Usrc/σsrc)*E/κ^2)
    0 ≤ L ∧
      (L < |gamma| *Uband →
        8*Uband ≤ |gamma| *lambda^2 ∧
        64*(modelPhaseJetCoefficient σ 3+δ)*M^2 ≤ |gamma| *κ^2*T) := by
  intro κ lambda Uband Ratio L
  have hκ : 0 < κ := modelPhaseThirdLower_pos hσ
  have hlambda : 0 < lambda := by dsimp only [lambda]; positivity
  have hUband : 0 < Uband := by dsimp only [Uband]; positivity
  have hratio : Uband/lambda=Ratio := by
    dsimp only [Uband,lambda,Ratio]
    field_simp
    ring
  have hfirst : 8*Uband^2/lambda^2 ≤ L := by
    calc
      _ = 8*Ratio^2 := by rw [←hratio]; ring
      _ ≤ _ := le_max_left _ _
  have hsecond : 64*(modelPhaseJetCoefficient σ 3+1)*M^2*Uband/(κ^2*T) ≤ L := by
    calc
      _ = 32*(modelPhaseJetCoefficient σ 3+1)*(3*Usrc/σsrc)*E/κ^2 := by
        dsimp only [Uband]
        field_simp
        ring
      _ ≤ _ := le_max_right _ _
  refine ⟨(by dsimp only [L]; exact (by positivity : (0:ℝ) ≤ 8*Ratio^2).trans (le_max_left _ _)),?_⟩
  intro hlarge
  constructor
  · have hh := (div_le_iff₀ (sq_pos_of_pos hlambda)).mp (hfirst.trans hlarge.le)
    apply (mul_le_mul_iff_right₀ hUband).mp
    nlinarith only [hh]
  · have hh := (div_le_iff₀ (by positivity : 0 < κ^2*T)).mp (hsecond.trans hlarge.le)
    have hbound : 64*(modelPhaseJetCoefficient σ 3+1)*M^2 ≤ |gamma| *κ^2*T := by
      apply (mul_le_mul_iff_right₀ hUband).mp
      nlinarith only [hh]
    apply le_trans _ hbound
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (add_le_add le_rfl hδ) (by norm_num : (0:ℝ) ≤ 64))
      (sq_nonneg M)


example
    {σ c U L : ℝ} (hσ : 0 < σ) (hc : 0 < c) (hU : 0 < U) (hL : 0 ≤ L) :
    ∃ D : ℝ, 0 < D ∧
      ∀ (P : Finset (((ℝ × ℤ) × Fin 2) × ((ℝ × ℤ) × Fin 2)))
        (Mat : (((ℝ × ℤ) × Fin 2) × ((ℝ × ℤ) × Fin 2)) → Fin 4 → ℤ)
        (F : ℝ → ℝ) (z : ℝ → ℤ → ℝ) (Alen : ℝ → ℤ → ℕ)
        (N : ℕ) (Z : ℝ → ℤ) (η Δ J T M : ℝ),
      0 < η → η ≤ 1/8 →
      (∀ w, 0 < w → ContDiffAt ℝ ∞ F w) →
      (∀ w∈Icc (1/2:ℝ) 3, ∀ n ≤ 6, |iteratedDeriv (n+1) F w| ≤ U) →
      (∀ w∈Icc (1/2:ℝ) 3, ∀ j,
        c ≤ |TaoTrudgianYang2025.HuxleyModel.tests
          (fun i : Fin 4 => iteratedDeriv (i.val+3) F w) j|) →
      (∀ w∈Icc (1/2:ℝ) 3, iteratedDeriv 4 F w ≤ -c) →
      0 < T → 2 ≤ M → 0 < N → 0 ≤ Δ → 0 < J → (N:ℝ) ≤ M → J ≤ M →
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
      (∀ ij∈P, Mat ij 0*Mat ij 3-Mat ij 1*Mat ij 2=1) →
      (∀ ij∈P, Mat ij 1 ≠ 0 ∧ Mat ij 2 ≠ 0) →
      (∀ ij∈P, |(Mat ij 2:ℝ)| * ((3*U/σ)*T/(2*M^2)) ≤ L) →
      let f := fun y w => T*(F (w/M)-F (w/M+η*y))/(σ*η)
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
      (P.card:ℝ) ≤ D*((P.image (fun ij => ij.1.1.1)).card:ℝ)*
        (M/(N:ℝ))*(1+Δ*J) :=
  HuxleyActualTypeOneActionScratch.positive_difference_family_bounded_action_source_scale_at_action (σ:=σ) (c:=c) (U:=U) (L:=L) hσ hc hU hL

example
    {σ c U L : ℝ} (hσ : 0 < σ) (hc : 0 < c) (hU : 0 < U) (hL : 0 ≤ L) :
    ∃ D : ℝ, 0 < D ∧
      ∀ (P : Finset (((ℝ × ℤ) × Fin 2) × ((ℝ × ℤ) × Fin 2)))
        (Mat : (((ℝ × ℤ) × Fin 2) × ((ℝ × ℤ) × Fin 2)) → Fin 4 → ℤ)
        (F : ℝ → ℝ) (z : ℝ → ℤ → ℝ) (Alen : ℝ → ℤ → ℕ)
        (N : ℕ) (Z : ℝ → ℤ) (η Δ J T M : ℝ),
      0 < η → η ≤ 1/8 →
      (∀ w, 0 < w → ContDiffAt ℝ ∞ F w) →
      (∀ w∈Icc (1/2:ℝ) 3, ∀ n ≤ 6, |iteratedDeriv (n+1) F w| ≤ U) →
      (∀ w∈Icc (1/2:ℝ) 3, ∀ j,
        c ≤ |TaoTrudgianYang2025.HuxleyModel.tests
          (fun i : Fin 4 => iteratedDeriv (i.val+3) F w) j|) →
      (∀ w∈Icc (1/2:ℝ) 3, iteratedDeriv 4 F w ≤ -c) →
      0 < T → 2 ≤ M → 0 < N → 0 ≤ Δ → 0 < J → (N:ℝ) ≤ M → J ≤ M →
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
      (∀ ij∈P, Mat ij 0*Mat ij 3-Mat ij 1*Mat ij 2=1) →
      (∀ ij∈P,
        (Mat ij 0=1 ∧ Mat ij 1=0 ∧ Mat ij 2=0 ∧ Mat ij 3=1) ∨
        (Mat ij 1≠0 ∧ Mat ij 2≠0 ∧ |(Mat ij 2:ℝ)| * ((3*U/σ)*T/(2*M^2)) ≤ L)) →
      let f := fun y w => T*(F (w/M)-F (w/M+η*y))/(σ*η)
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
      (P.card:ℝ) ≤ D*((P.image (fun ij => ij.1.1.1)).card:ℝ)*
        (M/(N:ℝ))*(1+Δ*J) :=
  HuxleyActualTypeOneActionScratch.positive_difference_family_type_one_source_scale_at_action (σ:=σ) (c:=c) (U:=U) (L:=L) hσ hc hU hL

example
    {σsrc csrc Usrc E σ δ T M gamma : ℝ}
    (hσsrc : 0 < σsrc) (hcsrc : 0 < csrc) (hUsrc : 0 < Usrc)
    (hE : 0 < E) (hσ : 0 < σ) (hT : 0 < T) (hM : 0 < M)
    (hδ : δ ≤ 1) :
    let κ := modelPhaseThirdLower σ
    let lambda := csrc*κ*T/(12*Usrc*M^2)
    let Uband := (3*Usrc/σsrc)*E*T/(2*M^2)
    let Ratio := 18*Usrc^2*E/(σsrc*csrc*κ)
    let L := max (8*Ratio^2)
      (32*(modelPhaseJetCoefficient σ 3+1)*(3*Usrc/σsrc)*E/κ^2)
    0 ≤ L ∧
      (L < |gamma| *Uband →
        8*Uband ≤ |gamma| *lambda^2 ∧
        64*(modelPhaseJetCoefficient σ 3+δ)*M^2 ≤ |gamma| *κ^2*T) :=
  HuxleyActualTypeOneActionScratch.source_model_large_action_threshold (σsrc:=σsrc) (csrc:=csrc) (Usrc:=Usrc) (E:=E) (σ:=σ) (δ:=δ) (T:=T) (M:=M) (gamma:=gamma) hσsrc hcsrc hUsrc hE hσ hT hM hδ


#print axioms source_model_large_action_threshold
#print axioms positive_difference_family_bounded_action_source_scale_at_action
#print axioms positive_difference_family_type_one_source_scale_at_action

end HuxleyActualTypeOneActionScratch
