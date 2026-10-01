import TaoTrudgianYang2025.HuxleyLinearForms
open Set TaoTrudgianYang2025 TaoTrudgianYang2025.HuxleyRationalPhase intervalIntegral
open scoped BigOperators Classical ContDiff
namespace HuxleyTriangularWeightScratch

private theorem inverse_cuberoot_nat_prefix (H : ℕ) :
    (∑ n∈Finset.range H, ((n:ℝ)+1)^(-(1:ℝ)/3)) ≤
      (3/2:ℝ)*((H:ℝ)+1)^((2:ℝ)/3) := by
  have hanti : AntitoneOn (fun x : ℝ => x^(-(1:ℝ)/3)) (Icc (1:ℝ) (1+H)) := by
    intro x hx y _hy hxy
    exact Real.rpow_le_rpow_of_nonpos (zero_lt_one.trans_le hx.1) hxy (by norm_num)
  have hh := hanti.sum_le_integral
  rw [integral_rpow (Or.inl (by norm_num : (-1:ℝ) < -(1:ℝ)/3))] at hh
  have hh' : (∑ n∈Finset.range H, ((n:ℝ)+1+1)^(-(1:ℝ)/3)) ≤
      (((H:ℝ)+1)^((2:ℝ)/3)-1)/((2:ℝ)/3) := by
    simpa only [Nat.cast_add,Nat.cast_one,show (-(1:ℝ)/3)+1=2/3 by norm_num,
      Real.one_rpow,add_comm (1:ℝ),add_assoc] using hh
  have hs := Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.range_mono (Nat.le_succ H))
    (fun n _ _ => Real.rpow_nonneg (by positivity : (0:ℝ) ≤ (n:ℝ)+1) (-(1:ℝ)/3))
  have hs' : (∑ n∈Finset.range H, ((n:ℝ)+1)^(-(1:ℝ)/3)) ≤
      (∑ n∈Finset.range H, ((n:ℝ)+1+1)^(-(1:ℝ)/3))+1 := by
    simpa only [Finset.sum_range_succ',Nat.cast_add,Nat.cast_one,Nat.cast_zero,
      zero_add,Real.one_rpow] using hs
  linarith only [hh',hs']

private theorem integer_inverse_cuberoot_sum
    (S : Finset ℤ) {D : ℝ} (hD : 0 ≤ D)
    (hS : ∀ b∈S, |(b:ℝ)| ≤ D) :
    (∑ b∈S, |(b:ℝ)|^(-(1:ℝ)/3)) ≤ 3*(D+2)^((2:ℝ)/3) := by
  classical
  let H := ⌈D⌉₊
  let f := fun b : ℤ => |(b:ℝ)|^(-(1:ℝ)/3)
  have hsub : S ⊆ Finset.Icc (-(H:ℤ)) (H:ℤ) := by
    intro b hb
    apply Finset.mem_Icc.mpr
    have hh := abs_le.mp ((hS b hb).trans (Nat.le_ceil D))
    constructor
    · exact_mod_cast hh.1
    · exact_mod_cast hh.2
  have heven : f.Even := by intro b; simp only [f,Int.cast_neg,abs_neg]
  calc
    _ ≤ ∑ b∈Finset.Icc (-(H:ℤ)) (H:ℤ),f b :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by dsimp only [f]; positivity)
    _ = 2*(∑ n∈Finset.range H, ((n:ℝ)+1)^(-(1:ℝ)/3)) := by
      rw [Finset.sum_Icc_of_even_eq_range heven,Finset.sum_range_succ']
      norm_num [f]
      apply Finset.sum_congr rfl
      intro n _
      rw [abs_of_pos (by positivity : (0:ℝ) < (n:ℝ)+1)]
    _ ≤ 3*((H:ℝ)+1)^((2:ℝ)/3) := by
      have hh := mul_le_mul_of_nonneg_left (inverse_cuberoot_nat_prefix H) (by norm_num : (0:ℝ) ≤ 2)
      linarith only [hh]
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num : (0:ℝ) ≤ 3)
      apply Real.rpow_le_rpow (by positivity) _ (by norm_num : (0:ℝ) ≤ 2/3)
      have hh : (H:ℝ) < D+1 := Nat.ceil_lt_add_one hD
      linarith only [hh]

private theorem integer_cubic_reciprocal_weight_sum
    (S : Finset ℤ) {D A B C : ℝ} (hD : 0 ≤ D)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C)
    (hS : ∀ b∈S, b ≠ 0 ∧ |(b:ℝ)| ≤ D) :
    (∑ b∈S, ((A/|(b:ℝ)|)^((3:ℝ)⁻¹)+B/|(b:ℝ)|+C)) ≤
      3*A^((3:ℝ)⁻¹)*(D+2)^((2:ℝ)/3)+
        2*B*(3+2*Real.log (D+2))+C*(2*D+1) := by
  classical
  let H := ⌈D⌉₊
  have hsub : S ⊆ (Finset.Icc (-(H:ℤ)) (H:ℤ)).erase 0 := by
    intro b hb
    apply Finset.mem_erase.mpr
    refine ⟨(hS b hb).1,Finset.mem_Icc.mpr ?_⟩
    have hh := abs_le.mp ((hS b hb).2.trans (Nat.le_ceil D))
    constructor
    · exact_mod_cast hh.1
    · exact_mod_cast hh.2
  have hrec : ∑ b∈S, 1/|(b:ℝ)| ≤ 2*(3+2*Real.log (D+2)) := by
    have hh := (Finset.sum_le_sum_of_subset_of_nonneg hsub
      (fun _ _ _ => by positivity : ∀ b∈(Finset.Icc (-(H:ℤ)) (H:ℤ)).erase 0,
        b∉S → (0:ℝ) ≤ 1/|(b:ℝ)|)).trans
      (TaoTrudgianYang2025.bourgain_integer_reciprocal_sum H)
    have hceil : (H:ℝ) < D+1 := Nat.ceil_lt_add_one hD
    have hlog : Real.log ((H:ℝ)+1) ≤ Real.log (D+2) :=
      Real.log_le_log (by positivity) (by linarith only [hceil])
    linarith only [hh,hlog]
  have hcard : (S.card:ℝ) ≤ 2*D+1 :=
    integer_card_le_of_abs_sub_le (a:=0) S hD
      (by intro b hb; simpa only [sub_zero] using (hS b hb).2)
  have hcube := integer_inverse_cuberoot_sum S hD (fun b hb => (hS b hb).2)
  have hfactor b :
      (A/|(b:ℝ)|)^((3:ℝ)⁻¹)=A^((3:ℝ)⁻¹)*|(b:ℝ)|^(-(1:ℝ)/3) := by
    rw [Real.div_rpow hA (abs_nonneg _)]
    rw [show -(1:ℝ)/3 = -((3:ℝ)⁻¹) by norm_num,Real.rpow_neg (abs_nonneg _)]
    exact div_eq_mul_inv _ _
  calc
    _ = A^((3:ℝ)⁻¹)*(∑ b∈S, |(b:ℝ)|^(-(1:ℝ)/3))+
        B*(∑ b∈S,1/|(b:ℝ)|)+C*(S.card:ℝ) := by
      simp_rw [hfactor]
      rw [Finset.sum_add_distrib,Finset.sum_add_distrib]
      simp only [Finset.mul_sum,Finset.sum_const,nsmul_eq_mul,mul_one_div]
      ring
    _ ≤ A^((3:ℝ)⁻¹)*(3*(D+2)^((2:ℝ)/3))+
        B*(2*(3+2*Real.log (D+2)))+C*(2*D+1) :=
      add_le_add (add_le_add
        (mul_le_mul_of_nonneg_left hcube (Real.rpow_nonneg hA _))
        (mul_le_mul_of_nonneg_left hrec hB))
        (mul_le_mul_of_nonneg_left hcard hC)
    _ = _ := by ring

private theorem triangular_weight_normalize (m X Y Z P Q R u b : ℝ) :
    4*m*((X/(P*b))^((3:ℝ)⁻¹)+Y/(Q*b*u))+
      m*(Z/(R*b*u)+2) =
    4*m*(((X/P)/b)^((3:ℝ)⁻¹)+(Y/(Q*u)+Z/(4*R*u))/b+1/2) := by
  rw [div_div]
  simp only [div_eq_mul_inv,mul_inv_rev]
  ring

private theorem physical_source_triangular_constants_nonneg
    {σ δ : ℝ} (hσ : 0 < σ) (hδ0 : 0 ≤ δ) :
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
    let Gamma := Cphys/κ
    let Cthird := Gamma*(32*Kres+9*quarticReciprocalConstant σ δ)
    0 ≤ B ∧ 0 ≤ Cthird := by
  intro κ Cphys c J B C₂ C₃ Ct Cc Kres Gamma Cthird
  have hκ : 0 < κ := modelPhaseThirdLower_pos hσ
  have hCphys : 0 < Cphys := by dsimp only [Cphys]; positivity
  have hC₂ := add_nonneg (modelPhaseJetCoefficient_nonneg σ 2) hδ0
  have hC₃ := add_nonneg (modelPhaseJetCoefficient_nonneg σ 3) hδ0
  have hC₄ := add_nonneg (modelPhaseJetCoefficient_nonneg σ 4) hδ0
  have hCR : 0 ≤ quarticReciprocalConstant σ δ := by
    dsimp only [quarticReciprocalConstant]; positivity
  have hCN : 0 ≤ quarticNonlinearResidualConstant σ δ := by
    dsimp only [quarticNonlinearResidualConstant]; positivity
  have hB : 0 ≤ B := zero_le_one.trans (le_max_left _ _)
  have hCt : 0 ≤ Ct := by dsimp only [Ct]; positivity
  have hCc : 0 ≤ Cc := by dsimp only [Cc]; positivity
  have hK : 0 ≤ Kres := div_nonneg (mul_nonneg (by norm_num)
    (add_nonneg (add_nonneg (add_nonneg
      (add_nonneg (div_nonneg (mul_nonneg (by norm_num) hB) (by norm_num))
        (mul_nonneg (mul_nonneg (by norm_num) hB) hCc))
      (mul_nonneg (by norm_num) hCt))
      (mul_nonneg (by norm_num) hCc))
      (mul_nonneg (by norm_num) hCN))) hκ.le
  have hΓ : 0 ≤ Gamma := div_nonneg hCphys.le hκ.le
  have hCthird : 0 ≤ Cthird :=
    mul_nonneg hΓ (add_nonneg (mul_nonneg (by norm_num) hK)
      (mul_nonneg (by norm_num) hCR))
  exact ⟨hB,hCthird⟩

/-- Sum the actual colored triangular Fourier families over nonzero
integer translations. Both the cubic-root and harmonic source terms,
and the complete short-family contribution, remain explicit. -/
theorem positive_difference_actual_fourier_charted_triangular_translation_sample_mass
    {σsrc csrc Usrc : ℝ} (hσsrc : 0 < σsrc) (hcsrc : 0 < csrc) (hUsrc : 0 < Usrc) :
    ∃ η₀ a Cupper Clower Dupper Dlower : ℝ, 0 < η₀ ∧ η₀ ≤ 1/8 ∧ 0 < a ∧
      0 < Cupper ∧ 0 < Clower ∧ 0 < Dupper ∧ 0 < Dlower ∧
    ∀ (Fsrc : ℝ → ℝ) (η ya yb Tsrc E Dtranslation : ℝ)
    (Translations : Finset ℤ) (chartKey : ℤ → ℤ × ℤ × ℤ)
    (Uref : ℕ) (Refs : Finset ℝ) (Gaps : ℤ → Finset (ℝ × ℝ)) {Bselect : ℝ}
    (Bmajor Cmajor : ℕ)
    (S : ℤ → ℝ × ℝ → Finset ℕ) (Q K₀ : ℕ) [NeZero K₀]
    (rat : ℤ → ℝ × ℝ → ℕ → Fin 2 → ℚ) (vinv : ℤ → ℝ × ℝ → ℕ → Fin 2 → ℤ)
    (parity : ℤ → ℝ × ℝ → ℕ → Fin 2 → Fin 2) (anchor : ℤ → ℝ × ℝ → ℕ → ℚ)
    (Mat : ℤ → Fin 4 → ℤ) (e r v s : ℤ → ℝ × ℝ → ℤ)
    {σ δ T M N R base Bcut lambda Uband θ : ℝ}
    (A : Fin 2 → ℤ) {W : Fin 2 → ℝ}
    {x : ℤ → ℝ × ℝ → ℕ → Fin 2 → ℝ},
    0 < η → η ≤ η₀ →
    ya∈Icc (1:ℝ) 2 → yb∈Icc (1:ℝ) 2 →
    (∀ w, 0 < w → ContDiffAt ℝ ∞ Fsrc w) →
    (∀ w∈Icc (1/2:ℝ) 3, ∀ n ≤ 6, |iteratedDeriv (n+1) Fsrc w| ≤ Usrc) →
    (∀ w∈Icc (1/2:ℝ) 3, ∀ j,
      csrc ≤ |HuxleyModel.tests (fun i : Fin 4 => iteratedDeriv (i.val+3) Fsrc w) j|) →
    0 < Tsrc → 2 ≤ M → Tsrc ≤ E*T →
    0 ≤ Dtranslation →
    (∀ t∈Translations, t≠0 ∧ |(t:ℝ)| ≤ Dtranslation) →
    let yp : Fin 2 → ℝ := ![ya,yb]
    let F := fun (i : Fin 2) u =>
      (Tsrc/T)*(Fsrc u-Fsrc (u+η*yp i))/(σsrc*η)
    let chartColor := fun (t : ℤ) ab j i =>
      (⌊yp i/a⌋,⌊((2*M^2/Tsrc)*(rat t ab j i:ℝ))/a⌋,
        ⌊((Tsrc/(2*M^2))*(rat t ab j i:ℝ)⁻¹)/a⌋)
    (∀ t∈Translations, ∀ ab∈Gaps t, ∀ j∈S t ab, ∀ i, chartColor t ab j i=chartKey t) →
    (0 < σ) →
    (δ ≤ min (modelPhaseThirdLower σ) 1) →
    (∀ i, Expdb.IsApproximateModelPhaseFunction (F i) σ 4 δ) →
    (0 < T) →
    (0 < M) →
    (0 < N) →
    (1 ≤ R) →
    (R ≤ M) →
    (0 < Q) →
    (T*N*R^2=M^3) →
    ((Q:ℝ)*N ≤ (K₀:ℝ)*R^2) →
    (∀ i, M ≤ A i) →
    (∀ i, A i+W i ≤ 2*M) →
    (∀ t∈Translations, ∀ ab∈Gaps t, ∀ j∈(S t ab), ∀ i, (x t ab) j i∈Ioo (1/2:ℝ) (W i-1/2)) →
    (∀ t∈Translations, ∀ ab∈Gaps t, ∀ j∈(S t ab), (x t ab) j 0∈Icc (base+N*(j:ℝ)) (base+N*((j:ℝ)+1))) →
    (∀ t∈Translations, ∀ ab∈Gaps t, ∀ j∈(S t ab), ∀ i, ((rat t ab) j i).den ≤ Q ∧ Q ≤ 2*((rat t ab) j i).den) →
    (0 < lambda) →
    (0 ≤ Uband) →
    (0 < θ) →
    (θ ≤ 1/24) →
    (∀ t∈Translations, ∀ ab∈Gaps t, ∀ j∈(S t ab), ∀ i, lambda ≤ |((rat t ab) j i:ℝ)| ∧ |((rat t ab) j i:ℝ)| ≤ Uband) →
    (∀ t∈Translations, ∀ ab∈Gaps t, ∀ j∈(S t ab), ∀ i, (((rat t ab) j i).den:ℤ) ∣ ((rat t ab) j i).num*(vinv t ab) j i-1) →
    (∀ t∈Translations, ∀ ab∈Gaps t, (v t ab)*(r t ab)-(e t ab)*(s t ab)=1) →
    (∀ t∈Translations, ∀ ab∈Gaps t, ((0:ℝ) < (r t ab) ∧ ((e t ab):ℝ)/(r t ab)=ab.1) ∨
      (((r t ab):ℝ) < 0 ∧ ((e t ab):ℝ)/(r t ab)=ab.2)) →
    (0 < Bcut) →
    (∀ t∈Translations, ∀ ab∈Gaps t, (s t ab) ≠ 0) →
    (∀ t∈Translations, ∀ ab∈Gaps t, ((e t ab):ℝ)/(r t ab)∈Refs) →
    (∀ t∈Translations, ∀ ab∈Gaps t, ((v t ab):ℝ)/(s t ab)∈Refs) →
    (∀ a∈Refs, ∀ b∈Refs, a ≠ b → ((Uref:ℝ)/R^2)/4 < |a-b|) →
    (∀ t∈Translations, ∀ ab∈Gaps t, ∀ j∈(S t ab), ∀ i, (x t ab) j i-(56*(Uref:ℝ)/modelPhaseThirdLower σ)*N∈Ioo (1/2:ℝ) (W i-1/2)) →
    (∀ t∈Translations, ∀ ab∈Gaps t, ∀ j∈(S t ab), ∀ i, (x t ab) j i+(56*(Uref:ℝ)/modelPhaseThirdLower σ)*N∈Ioo (1/2:ℝ) (W i-1/2)) →
    (1 ≤ Uref) →
    (2+168/modelPhaseThirdLower σ ≤ Bselect) →
    (7*Bcut ≤ modelPhaseThirdLower σ*Bselect) →
    (Bselect^2*(Uref:ℝ)^3*R^2 ≤ N^2) →
    (∀ t∈Translations, ∀ ab∈Gaps t, R^2 ≤ ((r t ab):ℝ)^2*(Uref:ℝ)) →
    (∀ t∈Translations, ∀ ab∈Gaps t, ab.2-ab.1 ≤ 7*(Uref:ℝ)/(2*R^2)) →
    (R ≤ (Q:ℝ)) →
    ((Uref:ℝ) ≤ (N/(Q:ℝ))^((2:ℝ)/3)/Bselect) →
    (N^10 ≤ M^3*R^7) →
    (∀ t∈Translations, ∀ ab∈Gaps t, ∀ j∈(S t ab), ((rat t ab) j 0:ℝ)∈Icc ab.1 ab.2) →
    (∀ t∈Translations, ∀ ab∈Gaps t, ab.1∈Refs ∧ ab.2∈Refs ∧ ab.1 < ab.2 ∧
      ∀ t∈Refs, ¬(ab.1 < t ∧ t < ab.2)) →
    let Vheight := T*(modelPhaseJetCoefficient σ 1+δ)/(2*M^2)
    let P₁ := fun (t : ℤ) (ab : ℝ × ℝ) => 1+(|((v t ab):ℝ)|+|((s t ab):ℝ)| *Vheight)*(Q:ℝ)
    let P₂ := fun (t : ℤ) (ab : ℝ × ℝ) => 1+(|((r t ab):ℝ)| *Vheight+|((e t ab):ℝ)|)*(Q:ℝ)
    let ε := modelPhaseThirdLower σ/(16*(σ*(σ+1)+1+2)*R^2)
    let Ccharts := fun (ab : ℝ × ℝ) => ⌊Real.logb (5/4) ((ab.2-ab.1)/(12*ε))⌋₊+1
    let sourceColor := fun (t : ℤ) (ab : ℝ × ℝ) => fun j i => (⌊(((rat t ab) j i).den:ℝ)/(θ*((Q:ℝ)/2))⌋,
      ⌊(((rat t ab) j i).num:ℝ)/(θ*(lambda*(Q:ℝ)/2))⌋)
    (∀ t∈Translations, ∀ ab∈Gaps t, ∀ j∈(S t ab), (sourceColor t ab) j 0=(sourceColor t ab) j 1) →
    let f := fun i => heathBrownPhysicalPhase (F i) T M (A i) 1
    (∀ t∈Translations, ∀ ab∈Gaps t, ∀ j∈(S t ab), ∀ i, iteratedDeriv 2 (f i) ((x t ab) j i)/2=((rat t ab) j i:ℝ)) →
    let q := fun (t : ℤ) (ab : ℝ × ℝ) => fun j i => ((rat t ab) j i).den
    let mu := fun (t : ℤ) (ab : ℝ × ℝ) => fun j i => iteratedDeriv 3 (f i) (round ((x t ab) j i))/6
    let ell := fun (t : ℤ) (ab : ℝ × ℝ) => fun j i => deriv (f i) (round ((x t ab) j i))
    let b := fun (t : ℤ) (ab : ℝ × ℝ) => fun j i => (⌊((q t ab) j i:ℝ)*(ell t ab) j i⌋+((parity t ab) j i:ℕ) : ℤ)
    let cround := fun (t : ℤ) (ab : ℝ × ℝ) => fun j i => round (((q t ab) j i:ℝ)*(ell t ab) j i)
    let tau := fun (t : ℤ) (ab : ℝ × ℝ) => fun j i => (((b t ab) j i:ℝ)-((q t ab) j i:ℝ)*(ell t ab) j i)/2
    let dual := fun (t : ℤ) (ab : ℝ × ℝ) => fun j i => -2*(mu t ab) j i*(Real.sqrt (2/(3*(mu t ab) j i*((q t ab) j i:ℝ))))^3
    let cloud := fun (t : ℤ) (ab : ℝ × ℝ) => fun j i => (![Int.fract (-((vinv t ab) j i:ℝ)*(b t ab) j i/(q t ab) j i),
      Int.fract (-((vinv t ab) j i:ℝ)/(q t ab) j i),(dual t ab) j i/Real.sqrt K₀,
      (3*(dual t ab) j i*(tau t ab) j i/2)/Real.sqrt K₀] : Fin 4 → ℝ)
    let radius : Fin 4 → ℝ := ![1/(12*(K₀:ℝ)),1/(12*(K₀:ℝ)^2),(1/(K₀:ℝ)^2)/12,(1/(K₀:ℝ))/12]
    (∀ t∈Translations, ∀ ab∈Gaps t, ∀ j∈(S t ab), (b t ab) j 0-(cround t ab) j 0=(b t ab) j 1-(cround t ab) j 1) →
    (∀ t∈Translations, ∀ ab∈Gaps t, ∀ j∈(S t ab), ∀ a, |(cloud t ab) j 0 a-(cloud t ab) j 1 a| ≤ 2*radius a) →
    let κ := modelPhaseThirdLower σ
    let Cphys := σ*(σ+1)+1
    let c := κ/6
    let J := Cphys/6
    let B := max 1 (max (2*Real.sqrt J) (8*J*Real.sqrt J/(3*c)))
    B*R^2/N^2 ≤ 1/2 →
    N ≤ R^2 →
    R ≤ N →
    N^3 ≤ M*R^2 →
    2*R^2 ≤ (Q:ℝ)*N →
    (∀ t∈Translations, Mat t 0*Mat t 3-Mat t 1*Mat t 2=1) →
    (∀ t∈Translations, ∀ ab∈Gaps t, ∀ j∈(S t ab), (Mat t 2:ℝ)*((rat t ab) j 0:ℝ)+Mat t 3=((q t ab) j 1:ℝ)/(q t ab) j 0) →
    (∀ t∈Translations, ∀ ab∈Gaps t, ∀ j∈(S t ab), ((Mat t 0:ℝ)*((rat t ab) j 0:ℝ)+Mat t 1)/
      ((Mat t 2:ℝ)*((rat t ab) j 0:ℝ)+Mat t 3)=((rat t ab) j 1:ℝ)) →
    (∀ t∈Translations, |(Mat t 2:ℝ)| ≤ (Q:ℝ)^2/(6*(K₀:ℝ)^2)) →
    let H := N/(Cphys+2)
    2 ≤ N →
    (∀ t∈Translations, ∀ ab∈Gaps t, ∀ j∈(S t ab), ∀ i, (x t ab) j i-H∈Ioo (1/2:ℝ) (W i-1/2)) →
    (∀ t∈Translations, ∀ ab∈Gaps t, ∀ j∈(S t ab), ∀ i, (x t ab) j i+H∈Ioo (1/2:ℝ) (W i-1/2)) →
    (∀ t∈Translations, ∀ ab∈Gaps t, ∀ j∈(S t ab), |((anchor t ab) j:ℝ)-((rat t ab) j 0:ℝ)| ≤ ε) →
    (∀ t∈Translations, ∀ ab∈Gaps t, ∀ j∈(S t ab), 256*(((anchor t ab) j).den:ℝ) ≤ (Q:ℝ)/3) →
    (∀ t∈Translations, ∀ ab∈Gaps t, ∀ j∈(S t ab), 256 ≤ (2*ε)*((Q:ℝ)/3)*((anchor t ab) j).den) →
    let C₂ := modelPhaseJetCoefficient σ 2+δ
    let C₃ := modelPhaseJetCoefficient σ 3+δ
    let Ct := C₂/2+5*C₃/12
    let Cc := C₂/κ+C₃/(2*κ)
    let Δ := (37*B/2+16*B*Cc+2*Ct+2*Cc)*(Q:ℝ)/N
    let Ccurv := (4/κ)*(B+2*quarticReciprocalConstant σ δ)
    let D := Δ+quarticNonlinearResidualConstant σ δ*(2*(Q:ℝ))/N
    let Kres := 4*(37*B/2+16*B*Cc+2*Ct+2*Cc+
      2*quarticNonlinearResidualConstant σ δ)/κ
    let Esize := κ/(16*(Cphys+2))
    let Dbase := 37*B/2+16*B*Cc+2*Ct+2*Cc+2*quarticNonlinearResidualConstant σ δ
    let Tbase := (2/κ)*(B+2*quarticReciprocalConstant σ δ)
    2*3840*128^2*105*(Dbase+64*Tbase*Esize^2) ≤ Bselect*Esize →
    D ≤ 1/2 → Δ < 1/2 → 61*Ccurv*Cphys ≤ Bcut →
    let Blabels := fun (t : ℤ) ab => 6+216*(⌊Real.logb 2 (P₁ t ab*P₂ t ab)⌋₊+1)
    let m0 := 6+Cmajor*(105+544*Bmajor)
    (∀ t∈Translations, ∀ ab∈Gaps t, Blabels t ab ≤ Bmajor) →
    (∀ t∈Translations, ∀ ab∈Gaps t, Ccharts ab ≤ Cmajor) →
    let Lunit := 2*κ/Cphys
    let Gamma := Cphys/κ
    let Cthird := Gamma*(32*Kres+9*quarticReciprocalConstant σ δ)
    let Aupper := 2*Cupper*(Cthird+1)*E^2*M^2/(κ*Lunit^3*N^4)
    let Bupper := Cupper*(Cthird+1)*E^2*M^2/(Lunit^2*N^4*(Uref:ℝ))+
      Dupper*(B+1)*E^2*M^2/(4*N^4*(Uref:ℝ))
    let Alower := 8*Clower*(Cthird+1)*R^4/(κ*Lunit^3*N^2)
    let Blower := 4*Clower*(Cthird+1)*R^4/(Lunit^2*N^2*(Uref:ℝ))+
      (4*Dlower*(B+1)*R^4)/(4*N^2*(Uref:ℝ))
    ((∀ t∈Translations, Mat t 0=1 ∧ Mat t 2=0 ∧ Mat t 3=1 ∧ Mat t 1=t) →
      (∑ t∈Translations, ∑ ab∈Gaps t, ((S t ab).card:ℝ)) ≤ 4*(m0:ℝ)*(3*Aupper^((3:ℝ)⁻¹)*(Dtranslation+2)^((2:ℝ)/3)+
        2*Bupper*(3+2*Real.log (Dtranslation+2))+(1/2:ℝ)*(2*Dtranslation+1))) ∧
    ((∀ t∈Translations, Mat t 0=1 ∧ Mat t 1=0 ∧ Mat t 3=1 ∧ Mat t 2=t) →
      (∑ t∈Translations, ∑ ab∈Gaps t, ((S t ab).card:ℝ)) ≤ 4*(m0:ℝ)*(3*Alower^((3:ℝ)⁻¹)*(Dtranslation+2)^((2:ℝ)/3)+
        2*Blower*(3+2*Real.log (Dtranslation+2))+(1/2:ℝ)*(2*Dtranslation+1))) := by
  classical
  obtain ⟨η₀,a,CU,CL,DU,DL,hη₀,hηcap,ha,hCU,hCL,hDU,hDL,hmassFn⟩ :=
    positive_difference_actual_fourier_charted_triangular_colored_sample_mass hσsrc hcsrc hUsrc
  refine ⟨η₀,a,CU,CL,DU,DL,hη₀,hηcap,ha,hCU,hCL,hDU,hDL,?_⟩
  intro Fsrc η ya yb Tsrc E Dtranslation Translations chartKey Uref Refs Gaps Bselect
    Bmajor Cmajor S Q K₀ inst rat vinv parity anchor Mat e r v s
    σ δ T M N R base Bcut lambda Uband θ A W x
    hη hηsmall hya hyb hreg hjets htests hTsrc hMtwo hsourceScale hDtranslation hTranslations
    yp F chartColor hchartColor
    hσ hδ hF hT hM hN hR hRM hQ hscale hmesh hA hW hx hwindow hden hlambda hUband hθ hθmax hcurv hinv hchart horientation hBcut hs hrefSet hparentSet hsep hwideL hwideU hUref hBselectSize hcutMargin hselectedWrap hreferenceDen hgapWidth hRQ hselectedUpper hscaleTen hfamilyGap hgap
    Vheight P₁ P₂ ε Ccharts sourceColor hsourceColor f hlevel
    q mu ell b cround tau dual cloud radius hcolor hnear
    κ Cphys c J B hsmall hNR hRN hNcube hminscale hMatdet hMatt hMatmap hMatgamma
    H hNtwo hL hU hanchor hcut hcount C₂ C₃ Ct Cc Δ
    Ccurv D Kres Esize Dbase Tbase hsize hD hΔ hBsize
    Blabels m0 hBmajor hCmajor Lunit Gamma Cthird Aupper Bupper Alower Blower
  have hper t (ht : t∈Translations) :
    ((Mat t 0=1 ∧ Mat t 2=0 ∧ Mat t 3=1) → Mat t 1≠0 →
      (∑ ab∈Gaps t, ((S t ab).card:ℝ)) ≤ 4*(m0:ℝ)*
        ((2*CU*(Cthird+1)*E^2*M^2/(κ*Lunit^3*N^4*|(Mat t 1:ℝ)|))^((3:ℝ)⁻¹)+
          CU*(Cthird+1)*E^2*M^2/(Lunit^2*N^4*|(Mat t 1:ℝ)| *(Uref:ℝ)))+
        (m0:ℝ)*(DU*(B+1)*E^2*M^2/(N^4*|(Mat t 1:ℝ)| *(Uref:ℝ))+2)) ∧
    ((Mat t 0=1 ∧ Mat t 1=0 ∧ Mat t 3=1) → Mat t 2≠0 →
      (∑ ab∈Gaps t, ((S t ab).card:ℝ)) ≤ 4*(m0:ℝ)*
        ((8*CL*(Cthird+1)*R^4/(κ*Lunit^3*N^2*|(Mat t 2:ℝ)|))^((3:ℝ)⁻¹)+
          4*CL*(Cthird+1)*R^4/(Lunit^2*N^2*|(Mat t 2:ℝ)| *(Uref:ℝ)))+
        (m0:ℝ)*(4*DL*(B+1)*R^4/(N^2*|(Mat t 2:ℝ)| *(Uref:ℝ))+2)) := by
    exact hmassFn Fsrc η ya yb Tsrc E (chartKey t) Uref Refs (Gaps t)
      (Bselect:=Bselect) Bmajor Cmajor (S t) Q K₀ (rat t) (vinv t) (parity t) (anchor t)
      (Mat t) (e t) (r t) (v t) (s t)
      (σ:=σ) (δ:=δ) (T:=T) (M:=M) (N:=N) (R:=R) (base:=base) (Bcut:=Bcut)
      (lambda:=lambda) (Uband:=Uband) (θ:=θ) A (W:=W) (x:=x t)
      hη hηsmall hya hyb hreg hjets htests hTsrc hMtwo hsourceScale (hchartColor t ht)
      hσ hδ hF hT hM hN hR hRM hQ hscale hmesh hA hW (hx t ht) (hwindow t ht) (hden t ht) hlambda hUband hθ hθmax (hcurv t ht) (hinv t ht) (hchart t ht) (horientation t ht) hBcut (hs t ht) (hrefSet t ht) (hparentSet t ht) hsep (hwideL t ht) (hwideU t ht) hUref hBselectSize hcutMargin hselectedWrap (hreferenceDen t ht) (hgapWidth t ht) hRQ hselectedUpper hscaleTen (hfamilyGap t ht) (hgap t ht)
      (hsourceColor t ht) (hlevel t ht) (hcolor t ht) (hnear t ht) hsmall hNR hRN hNcube hminscale (hMatdet t ht) (hMatt t ht) (hMatmap t ht) (hMatgamma t ht) hNtwo (hL t ht) (hU t ht) (hanchor t ht) (hcut t ht) (hcount t ht) hsize hD hΔ hBsize (hBmajor t ht) (hCmajor t ht)
  have hκ : 0 < κ := modelPhaseThirdLower_pos hσ
  have hCphys : 0 < Cphys := by dsimp only [Cphys]; positivity
  have hLunit : 0 < Lunit := by dsimp only [Lunit]; positivity
  have hUp : (0:ℝ) < Uref := by exact_mod_cast (show 0 < Uref by omega)
  have hδ0 := approximateModelPhase_tolerance_nonneg (hF 0)
  obtain ⟨hB,hCthird⟩ := physical_source_triangular_constants_nonneg hσ hδ0
  have hthird1 : 0 ≤ Cthird+1 := add_nonneg hCthird zero_le_one
  have hB1 : 0 ≤ B+1 := add_nonneg hB zero_le_one
  have hnumU : 0 ≤ CU*(Cthird+1)*E^2*M^2 :=
    mul_nonneg (mul_nonneg (mul_nonneg hCU.le hthird1) (sq_nonneg E)) (sq_nonneg M)
  have hnumDU : 0 ≤ DU*(B+1)*E^2*M^2 :=
    mul_nonneg (mul_nonneg (mul_nonneg hDU.le hB1) (sq_nonneg E)) (sq_nonneg M)
  have hnumL : 0 ≤ 4*CL*(Cthird+1)*R^4 :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hCL.le) hthird1) (by positivity)
  have hnumDL : 0 ≤ 4*DL*(B+1)*R^4 :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hDL.le) hB1) (by positivity)
  have hAU : 0 ≤ Aupper := div_nonneg
    (by nlinarith only [hnumU]) (by positivity)
  have hBU : 0 ≤ Bupper := add_nonneg
    (div_nonneg hnumU (by positivity)) (div_nonneg hnumDU (by positivity))
  have hAL : 0 ≤ Alower := div_nonneg
    (by nlinarith only [hnumL]) (by positivity)
  have hBL : 0 ≤ Blower := add_nonneg
    (div_nonneg hnumL (by positivity)) (div_nonneg hnumDL (by positivity))
  constructor
  · intro htri
    have hweight t (ht : t∈Translations) :
        (∑ ab∈Gaps t, ((S t ab).card:ℝ)) ≤
          4*(m0:ℝ)*((Aupper/|(t:ℝ)|)^((3:ℝ)⁻¹)+Bupper/|(t:ℝ)|+1/2) := by
      have hsides := htri t ht
      have hentry : Mat t 1≠0 := by rw [hsides.2.2.2]; exact (hTranslations t ht).1
      have hh := (hper t ht).1 ⟨hsides.1,hsides.2.1,hsides.2.2.1⟩ hentry
      rw [hsides.2.2.2] at hh
      exact hh.trans_eq (triangular_weight_normalize (m0:ℝ)
        (2*CU*(Cthird+1)*E^2*M^2) (CU*(Cthird+1)*E^2*M^2) (DU*(B+1)*E^2*M^2) (κ*Lunit^3*N^4)
        (Lunit^2*N^4) (N^4) (Uref:ℝ) |(t:ℝ)|)
    calc
      _ ≤ ∑ t∈Translations, 4*(m0:ℝ)*((Aupper/|(t:ℝ)|)^((3:ℝ)⁻¹)+Bupper/|(t:ℝ)|+1/2) :=
        Finset.sum_le_sum hweight
      _ = 4*(m0:ℝ)*(∑ t∈Translations, ((Aupper/|(t:ℝ)|)^((3:ℝ)⁻¹)+Bupper/|(t:ℝ)|+1/2)) :=
        (Finset.mul_sum _ _ _).symm
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (integer_cubic_reciprocal_weight_sum Translations hDtranslation
          hAU hBU (by norm_num : (0:ℝ) ≤ 1/2) hTranslations) (by positivity)
  · intro htri
    have hweight t (ht : t∈Translations) :
        (∑ ab∈Gaps t, ((S t ab).card:ℝ)) ≤
          4*(m0:ℝ)*((Alower/|(t:ℝ)|)^((3:ℝ)⁻¹)+Blower/|(t:ℝ)|+1/2) := by
      have hsides := htri t ht
      have hentry : Mat t 2≠0 := by rw [hsides.2.2.2]; exact (hTranslations t ht).1
      have hh := (hper t ht).2 ⟨hsides.1,hsides.2.1,hsides.2.2.1⟩ hentry
      rw [hsides.2.2.2] at hh
      exact hh.trans_eq (triangular_weight_normalize (m0:ℝ)
        (8*CL*(Cthird+1)*R^4) (4*CL*(Cthird+1)*R^4) (4*DL*(B+1)*R^4) (κ*Lunit^3*N^2)
        (Lunit^2*N^2) (N^2) (Uref:ℝ) |(t:ℝ)|)
    calc
      _ ≤ ∑ t∈Translations, 4*(m0:ℝ)*((Alower/|(t:ℝ)|)^((3:ℝ)⁻¹)+Blower/|(t:ℝ)|+1/2) :=
        Finset.sum_le_sum hweight
      _ = 4*(m0:ℝ)*(∑ t∈Translations, ((Alower/|(t:ℝ)|)^((3:ℝ)⁻¹)+Blower/|(t:ℝ)|+1/2)) :=
        (Finset.mul_sum _ _ _).symm
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (integer_cubic_reciprocal_weight_sum Translations hDtranslation
          hAL hBL (by norm_num : (0:ℝ) ≤ 1/2) hTranslations) (by positivity)

example
    {σsrc csrc Usrc : ℝ} (hσsrc : 0 < σsrc) (hcsrc : 0 < csrc) (hUsrc : 0 < Usrc) :
    ∃ η₀ a Cupper Clower Dupper Dlower : ℝ, 0 < η₀ ∧ η₀ ≤ 1/8 ∧ 0 < a ∧
      0 < Cupper ∧ 0 < Clower ∧ 0 < Dupper ∧ 0 < Dlower ∧
    ∀ (Fsrc : ℝ → ℝ) (η ya yb Tsrc E Dtranslation : ℝ)
    (Translations : Finset ℤ) (chartKey : ℤ → ℤ × ℤ × ℤ)
    (Uref : ℕ) (Refs : Finset ℝ) (Gaps : ℤ → Finset (ℝ × ℝ)) {Bselect : ℝ}
    (Bmajor Cmajor : ℕ)
    (S : ℤ → ℝ × ℝ → Finset ℕ) (Q K₀ : ℕ) [NeZero K₀]
    (rat : ℤ → ℝ × ℝ → ℕ → Fin 2 → ℚ) (vinv : ℤ → ℝ × ℝ → ℕ → Fin 2 → ℤ)
    (parity : ℤ → ℝ × ℝ → ℕ → Fin 2 → Fin 2) (anchor : ℤ → ℝ × ℝ → ℕ → ℚ)
    (Mat : ℤ → Fin 4 → ℤ) (e r v s : ℤ → ℝ × ℝ → ℤ)
    {σ δ T M N R base Bcut lambda Uband θ : ℝ}
    (A : Fin 2 → ℤ) {W : Fin 2 → ℝ}
    {x : ℤ → ℝ × ℝ → ℕ → Fin 2 → ℝ},
    0 < η → η ≤ η₀ →
    ya∈Icc (1:ℝ) 2 → yb∈Icc (1:ℝ) 2 →
    (∀ w, 0 < w → ContDiffAt ℝ ∞ Fsrc w) →
    (∀ w∈Icc (1/2:ℝ) 3, ∀ n ≤ 6, |iteratedDeriv (n+1) Fsrc w| ≤ Usrc) →
    (∀ w∈Icc (1/2:ℝ) 3, ∀ j,
      csrc ≤ |HuxleyModel.tests (fun i : Fin 4 => iteratedDeriv (i.val+3) Fsrc w) j|) →
    0 < Tsrc → 2 ≤ M → Tsrc ≤ E*T →
    0 ≤ Dtranslation →
    (∀ t∈Translations, t≠0 ∧ |(t:ℝ)| ≤ Dtranslation) →
    let yp : Fin 2 → ℝ := ![ya,yb]
    let F := fun (i : Fin 2) u =>
      (Tsrc/T)*(Fsrc u-Fsrc (u+η*yp i))/(σsrc*η)
    let chartColor := fun (t : ℤ) ab j i =>
      (⌊yp i/a⌋,⌊((2*M^2/Tsrc)*(rat t ab j i:ℝ))/a⌋,
        ⌊((Tsrc/(2*M^2))*(rat t ab j i:ℝ)⁻¹)/a⌋)
    (∀ t∈Translations, ∀ ab∈Gaps t, ∀ j∈S t ab, ∀ i, chartColor t ab j i=chartKey t) →
    (0 < σ) →
    (δ ≤ min (modelPhaseThirdLower σ) 1) →
    (∀ i, Expdb.IsApproximateModelPhaseFunction (F i) σ 4 δ) →
    (0 < T) →
    (0 < M) →
    (0 < N) →
    (1 ≤ R) →
    (R ≤ M) →
    (0 < Q) →
    (T*N*R^2=M^3) →
    ((Q:ℝ)*N ≤ (K₀:ℝ)*R^2) →
    (∀ i, M ≤ A i) →
    (∀ i, A i+W i ≤ 2*M) →
    (∀ t∈Translations, ∀ ab∈Gaps t, ∀ j∈(S t ab), ∀ i, (x t ab) j i∈Ioo (1/2:ℝ) (W i-1/2)) →
    (∀ t∈Translations, ∀ ab∈Gaps t, ∀ j∈(S t ab), (x t ab) j 0∈Icc (base+N*(j:ℝ)) (base+N*((j:ℝ)+1))) →
    (∀ t∈Translations, ∀ ab∈Gaps t, ∀ j∈(S t ab), ∀ i, ((rat t ab) j i).den ≤ Q ∧ Q ≤ 2*((rat t ab) j i).den) →
    (0 < lambda) →
    (0 ≤ Uband) →
    (0 < θ) →
    (θ ≤ 1/24) →
    (∀ t∈Translations, ∀ ab∈Gaps t, ∀ j∈(S t ab), ∀ i, lambda ≤ |((rat t ab) j i:ℝ)| ∧ |((rat t ab) j i:ℝ)| ≤ Uband) →
    (∀ t∈Translations, ∀ ab∈Gaps t, ∀ j∈(S t ab), ∀ i, (((rat t ab) j i).den:ℤ) ∣ ((rat t ab) j i).num*(vinv t ab) j i-1) →
    (∀ t∈Translations, ∀ ab∈Gaps t, (v t ab)*(r t ab)-(e t ab)*(s t ab)=1) →
    (∀ t∈Translations, ∀ ab∈Gaps t, ((0:ℝ) < (r t ab) ∧ ((e t ab):ℝ)/(r t ab)=ab.1) ∨
      (((r t ab):ℝ) < 0 ∧ ((e t ab):ℝ)/(r t ab)=ab.2)) →
    (0 < Bcut) →
    (∀ t∈Translations, ∀ ab∈Gaps t, (s t ab) ≠ 0) →
    (∀ t∈Translations, ∀ ab∈Gaps t, ((e t ab):ℝ)/(r t ab)∈Refs) →
    (∀ t∈Translations, ∀ ab∈Gaps t, ((v t ab):ℝ)/(s t ab)∈Refs) →
    (∀ a∈Refs, ∀ b∈Refs, a ≠ b → ((Uref:ℝ)/R^2)/4 < |a-b|) →
    (∀ t∈Translations, ∀ ab∈Gaps t, ∀ j∈(S t ab), ∀ i, (x t ab) j i-(56*(Uref:ℝ)/modelPhaseThirdLower σ)*N∈Ioo (1/2:ℝ) (W i-1/2)) →
    (∀ t∈Translations, ∀ ab∈Gaps t, ∀ j∈(S t ab), ∀ i, (x t ab) j i+(56*(Uref:ℝ)/modelPhaseThirdLower σ)*N∈Ioo (1/2:ℝ) (W i-1/2)) →
    (1 ≤ Uref) →
    (2+168/modelPhaseThirdLower σ ≤ Bselect) →
    (7*Bcut ≤ modelPhaseThirdLower σ*Bselect) →
    (Bselect^2*(Uref:ℝ)^3*R^2 ≤ N^2) →
    (∀ t∈Translations, ∀ ab∈Gaps t, R^2 ≤ ((r t ab):ℝ)^2*(Uref:ℝ)) →
    (∀ t∈Translations, ∀ ab∈Gaps t, ab.2-ab.1 ≤ 7*(Uref:ℝ)/(2*R^2)) →
    (R ≤ (Q:ℝ)) →
    ((Uref:ℝ) ≤ (N/(Q:ℝ))^((2:ℝ)/3)/Bselect) →
    (N^10 ≤ M^3*R^7) →
    (∀ t∈Translations, ∀ ab∈Gaps t, ∀ j∈(S t ab), ((rat t ab) j 0:ℝ)∈Icc ab.1 ab.2) →
    (∀ t∈Translations, ∀ ab∈Gaps t, ab.1∈Refs ∧ ab.2∈Refs ∧ ab.1 < ab.2 ∧
      ∀ t∈Refs, ¬(ab.1 < t ∧ t < ab.2)) →
    let Vheight := T*(modelPhaseJetCoefficient σ 1+δ)/(2*M^2)
    let P₁ := fun (t : ℤ) (ab : ℝ × ℝ) => 1+(|((v t ab):ℝ)|+|((s t ab):ℝ)| *Vheight)*(Q:ℝ)
    let P₂ := fun (t : ℤ) (ab : ℝ × ℝ) => 1+(|((r t ab):ℝ)| *Vheight+|((e t ab):ℝ)|)*(Q:ℝ)
    let ε := modelPhaseThirdLower σ/(16*(σ*(σ+1)+1+2)*R^2)
    let Ccharts := fun (ab : ℝ × ℝ) => ⌊Real.logb (5/4) ((ab.2-ab.1)/(12*ε))⌋₊+1
    let sourceColor := fun (t : ℤ) (ab : ℝ × ℝ) => fun j i => (⌊(((rat t ab) j i).den:ℝ)/(θ*((Q:ℝ)/2))⌋,
      ⌊(((rat t ab) j i).num:ℝ)/(θ*(lambda*(Q:ℝ)/2))⌋)
    (∀ t∈Translations, ∀ ab∈Gaps t, ∀ j∈(S t ab), (sourceColor t ab) j 0=(sourceColor t ab) j 1) →
    let f := fun i => heathBrownPhysicalPhase (F i) T M (A i) 1
    (∀ t∈Translations, ∀ ab∈Gaps t, ∀ j∈(S t ab), ∀ i, iteratedDeriv 2 (f i) ((x t ab) j i)/2=((rat t ab) j i:ℝ)) →
    let q := fun (t : ℤ) (ab : ℝ × ℝ) => fun j i => ((rat t ab) j i).den
    let mu := fun (t : ℤ) (ab : ℝ × ℝ) => fun j i => iteratedDeriv 3 (f i) (round ((x t ab) j i))/6
    let ell := fun (t : ℤ) (ab : ℝ × ℝ) => fun j i => deriv (f i) (round ((x t ab) j i))
    let b := fun (t : ℤ) (ab : ℝ × ℝ) => fun j i => (⌊((q t ab) j i:ℝ)*(ell t ab) j i⌋+((parity t ab) j i:ℕ) : ℤ)
    let cround := fun (t : ℤ) (ab : ℝ × ℝ) => fun j i => round (((q t ab) j i:ℝ)*(ell t ab) j i)
    let tau := fun (t : ℤ) (ab : ℝ × ℝ) => fun j i => (((b t ab) j i:ℝ)-((q t ab) j i:ℝ)*(ell t ab) j i)/2
    let dual := fun (t : ℤ) (ab : ℝ × ℝ) => fun j i => -2*(mu t ab) j i*(Real.sqrt (2/(3*(mu t ab) j i*((q t ab) j i:ℝ))))^3
    let cloud := fun (t : ℤ) (ab : ℝ × ℝ) => fun j i => (![Int.fract (-((vinv t ab) j i:ℝ)*(b t ab) j i/(q t ab) j i),
      Int.fract (-((vinv t ab) j i:ℝ)/(q t ab) j i),(dual t ab) j i/Real.sqrt K₀,
      (3*(dual t ab) j i*(tau t ab) j i/2)/Real.sqrt K₀] : Fin 4 → ℝ)
    let radius : Fin 4 → ℝ := ![1/(12*(K₀:ℝ)),1/(12*(K₀:ℝ)^2),(1/(K₀:ℝ)^2)/12,(1/(K₀:ℝ))/12]
    (∀ t∈Translations, ∀ ab∈Gaps t, ∀ j∈(S t ab), (b t ab) j 0-(cround t ab) j 0=(b t ab) j 1-(cround t ab) j 1) →
    (∀ t∈Translations, ∀ ab∈Gaps t, ∀ j∈(S t ab), ∀ a, |(cloud t ab) j 0 a-(cloud t ab) j 1 a| ≤ 2*radius a) →
    let κ := modelPhaseThirdLower σ
    let Cphys := σ*(σ+1)+1
    let c := κ/6
    let J := Cphys/6
    let B := max 1 (max (2*Real.sqrt J) (8*J*Real.sqrt J/(3*c)))
    B*R^2/N^2 ≤ 1/2 →
    N ≤ R^2 →
    R ≤ N →
    N^3 ≤ M*R^2 →
    2*R^2 ≤ (Q:ℝ)*N →
    (∀ t∈Translations, Mat t 0*Mat t 3-Mat t 1*Mat t 2=1) →
    (∀ t∈Translations, ∀ ab∈Gaps t, ∀ j∈(S t ab), (Mat t 2:ℝ)*((rat t ab) j 0:ℝ)+Mat t 3=((q t ab) j 1:ℝ)/(q t ab) j 0) →
    (∀ t∈Translations, ∀ ab∈Gaps t, ∀ j∈(S t ab), ((Mat t 0:ℝ)*((rat t ab) j 0:ℝ)+Mat t 1)/
      ((Mat t 2:ℝ)*((rat t ab) j 0:ℝ)+Mat t 3)=((rat t ab) j 1:ℝ)) →
    (∀ t∈Translations, |(Mat t 2:ℝ)| ≤ (Q:ℝ)^2/(6*(K₀:ℝ)^2)) →
    let H := N/(Cphys+2)
    2 ≤ N →
    (∀ t∈Translations, ∀ ab∈Gaps t, ∀ j∈(S t ab), ∀ i, (x t ab) j i-H∈Ioo (1/2:ℝ) (W i-1/2)) →
    (∀ t∈Translations, ∀ ab∈Gaps t, ∀ j∈(S t ab), ∀ i, (x t ab) j i+H∈Ioo (1/2:ℝ) (W i-1/2)) →
    (∀ t∈Translations, ∀ ab∈Gaps t, ∀ j∈(S t ab), |((anchor t ab) j:ℝ)-((rat t ab) j 0:ℝ)| ≤ ε) →
    (∀ t∈Translations, ∀ ab∈Gaps t, ∀ j∈(S t ab), 256*(((anchor t ab) j).den:ℝ) ≤ (Q:ℝ)/3) →
    (∀ t∈Translations, ∀ ab∈Gaps t, ∀ j∈(S t ab), 256 ≤ (2*ε)*((Q:ℝ)/3)*((anchor t ab) j).den) →
    let C₂ := modelPhaseJetCoefficient σ 2+δ
    let C₃ := modelPhaseJetCoefficient σ 3+δ
    let Ct := C₂/2+5*C₃/12
    let Cc := C₂/κ+C₃/(2*κ)
    let Δ := (37*B/2+16*B*Cc+2*Ct+2*Cc)*(Q:ℝ)/N
    let Ccurv := (4/κ)*(B+2*quarticReciprocalConstant σ δ)
    let D := Δ+quarticNonlinearResidualConstant σ δ*(2*(Q:ℝ))/N
    let Kres := 4*(37*B/2+16*B*Cc+2*Ct+2*Cc+
      2*quarticNonlinearResidualConstant σ δ)/κ
    let Esize := κ/(16*(Cphys+2))
    let Dbase := 37*B/2+16*B*Cc+2*Ct+2*Cc+2*quarticNonlinearResidualConstant σ δ
    let Tbase := (2/κ)*(B+2*quarticReciprocalConstant σ δ)
    2*3840*128^2*105*(Dbase+64*Tbase*Esize^2) ≤ Bselect*Esize →
    D ≤ 1/2 → Δ < 1/2 → 61*Ccurv*Cphys ≤ Bcut →
    let Blabels := fun (t : ℤ) ab => 6+216*(⌊Real.logb 2 (P₁ t ab*P₂ t ab)⌋₊+1)
    let m0 := 6+Cmajor*(105+544*Bmajor)
    (∀ t∈Translations, ∀ ab∈Gaps t, Blabels t ab ≤ Bmajor) →
    (∀ t∈Translations, ∀ ab∈Gaps t, Ccharts ab ≤ Cmajor) →
    let Lunit := 2*κ/Cphys
    let Gamma := Cphys/κ
    let Cthird := Gamma*(32*Kres+9*quarticReciprocalConstant σ δ)
    let Aupper := 2*Cupper*(Cthird+1)*E^2*M^2/(κ*Lunit^3*N^4)
    let Bupper := Cupper*(Cthird+1)*E^2*M^2/(Lunit^2*N^4*(Uref:ℝ))+
      Dupper*(B+1)*E^2*M^2/(4*N^4*(Uref:ℝ))
    let Alower := 8*Clower*(Cthird+1)*R^4/(κ*Lunit^3*N^2)
    let Blower := 4*Clower*(Cthird+1)*R^4/(Lunit^2*N^2*(Uref:ℝ))+
      (4*Dlower*(B+1)*R^4)/(4*N^2*(Uref:ℝ))
    ((∀ t∈Translations, Mat t 0=1 ∧ Mat t 2=0 ∧ Mat t 3=1 ∧ Mat t 1=t) →
      (∑ t∈Translations, ∑ ab∈Gaps t, ((S t ab).card:ℝ)) ≤ 4*(m0:ℝ)*(3*Aupper^((3:ℝ)⁻¹)*(Dtranslation+2)^((2:ℝ)/3)+
        2*Bupper*(3+2*Real.log (Dtranslation+2))+(1/2:ℝ)*(2*Dtranslation+1))) ∧
    ((∀ t∈Translations, Mat t 0=1 ∧ Mat t 1=0 ∧ Mat t 3=1 ∧ Mat t 2=t) →
      (∑ t∈Translations, ∑ ab∈Gaps t, ((S t ab).card:ℝ)) ≤ 4*(m0:ℝ)*(3*Alower^((3:ℝ)⁻¹)*(Dtranslation+2)^((2:ℝ)/3)+
        2*Blower*(3+2*Real.log (Dtranslation+2))+(1/2:ℝ)*(2*Dtranslation+1))) :=
  HuxleyTriangularWeightScratch.positive_difference_actual_fourier_charted_triangular_translation_sample_mass (σsrc:=σsrc) (csrc:=csrc) (Usrc:=Usrc) hσsrc hcsrc hUsrc


private theorem rational_narrow_triangular_translation_bounds
    (p : Fin 2 → ℚ) (Mat : Fin 4 → ℤ) (Q : ℕ)
    {lambda U θ : ℝ} (hQ : 0 < Q) (hlambda : 0 < lambda)
    (hU : 0 ≤ U) (hθ : 0 < θ)
    (hcurv : ∀ i, lambda ≤ |(p i:ℝ)| ∧ |(p i:ℝ)| ≤ U)
    (hden : ∀ i, (p i).den ≤ Q ∧ Q ≤ 2*(p i).den)
    (hcolor : (⌊((p 0).den:ℝ)/(θ*((Q:ℝ)/2))⌋,
      ⌊((p 0).num:ℝ)/(θ*(lambda*(Q:ℝ)/2))⌋)=
      (⌊((p 1).den:ℝ)/(θ*((Q:ℝ)/2))⌋,
      ⌊((p 1).num:ℝ)/(θ*(lambda*(Q:ℝ)/2))⌋))
    (hdenmap : (Mat 2:ℝ)*(p 0:ℝ)+Mat 3=((p 1).den:ℝ)/(p 0).den)
    (hmap : ((Mat 0:ℝ)*(p 0:ℝ)+Mat 1)/((Mat 2:ℝ)*(p 0:ℝ)+Mat 3)=(p 1:ℝ)) :
    ((Mat 0=1 ∧ Mat 2=0 ∧ Mat 3=1) → |(Mat 1:ℝ)| ≤ θ*U) ∧
    ((Mat 0=1 ∧ Mat 1=0 ∧ Mat 3=1) → |(Mat 2:ℝ)| ≤ θ/lambda) := by
  have hb := (rational_narrow_band_partition (Finset.univ : Finset (Fin 2)) p Q
    hQ hlambda hU hθ (fun i _ => hcurv i) (fun i _ => hden i)).2
    0 (Finset.mem_univ 0) 1 (Finset.mem_univ 1) hcolor
  have hxabs : 0 < |(p 0:ℝ)| := hlambda.trans_le (hcurv 0).1
  have hx : (p 0:ℝ)≠0 := abs_pos.mp hxabs
  have hdpos : (0:ℝ) < (Mat 2:ℝ)*(p 0:ℝ)+Mat 3 := by
    rw [hdenmap]
    exact div_pos (by exact_mod_cast (p 1).pos) (by exact_mod_cast (p 0).pos)
  have hnumeq : ((Mat 0:ℝ)*(p 0:ℝ)+Mat 1)/(p 0:ℝ)=
      ((p 1).num:ℝ)/(p 0).num := by
    rw [(div_eq_iff hdpos.ne').mp hmap,hdenmap]
    simp only [Rat.cast_def]
    field_simp
  constructor
  · intro htri
    have hh := hb.2
    rw [←hnumeq,htri.1,Int.cast_one,one_mul] at hh
    have he : ((p 0:ℝ)+Mat 1)/(p 0:ℝ)-1=(Mat 1:ℝ)/(p 0:ℝ) := by
      field_simp
      ring
    rw [he,abs_div] at hh
    exact ((div_le_iff₀ hxabs).mp hh).trans
      (mul_le_mul_of_nonneg_left (hcurv 0).2 hθ.le)
  · intro htri
    have hh := hb.1
    rw [←hdenmap,htri.2.2,Int.cast_one,add_sub_cancel_right,abs_mul] at hh
    apply (le_div_iff₀ hlambda).mpr
    exact (mul_le_mul_of_nonneg_left (hcurv 0).1 (abs_nonneg _)).trans hh

/-- The source rational colors derive the translation cutoffs, and
the finite occupied-family filter preserves the original cardinality sum.
No externally supplied translation range or counting estimate is used. -/
theorem positive_difference_actual_fourier_charted_triangular_source_cutoff_sample_mass
    {σsrc csrc Usrc : ℝ} (hσsrc : 0 < σsrc) (hcsrc : 0 < csrc) (hUsrc : 0 < Usrc) :
    ∃ η₀ a Cupper Clower Dupper Dlower : ℝ, 0 < η₀ ∧ η₀ ≤ 1/8 ∧ 0 < a ∧
      0 < Cupper ∧ 0 < Clower ∧ 0 < Dupper ∧ 0 < Dlower ∧
    ∀ (Fsrc : ℝ → ℝ) (η ya yb Tsrc E : ℝ)
    (Translations : Finset ℤ) (chartKey : ℤ → ℤ × ℤ × ℤ)
    (Uref : ℕ) (Refs : Finset ℝ) (Gaps : ℤ → Finset (ℝ × ℝ)) {Bselect : ℝ}
    (Bmajor Cmajor : ℕ)
    (S : ℤ → ℝ × ℝ → Finset ℕ) (Q K₀ : ℕ) [NeZero K₀]
    (rat : ℤ → ℝ × ℝ → ℕ → Fin 2 → ℚ) (vinv : ℤ → ℝ × ℝ → ℕ → Fin 2 → ℤ)
    (parity : ℤ → ℝ × ℝ → ℕ → Fin 2 → Fin 2) (anchor : ℤ → ℝ × ℝ → ℕ → ℚ)
    (Mat : ℤ → Fin 4 → ℤ) (e r v s : ℤ → ℝ × ℝ → ℤ)
    {σ δ T M N R base Bcut lambda Uband θ : ℝ}
    (A : Fin 2 → ℤ) {W : Fin 2 → ℝ}
    {x : ℤ → ℝ × ℝ → ℕ → Fin 2 → ℝ},
    0 < η → η ≤ η₀ →
    ya∈Icc (1:ℝ) 2 → yb∈Icc (1:ℝ) 2 →
    (∀ w, 0 < w → ContDiffAt ℝ ∞ Fsrc w) →
    (∀ w∈Icc (1/2:ℝ) 3, ∀ n ≤ 6, |iteratedDeriv (n+1) Fsrc w| ≤ Usrc) →
    (∀ w∈Icc (1/2:ℝ) 3, ∀ j,
      csrc ≤ |HuxleyModel.tests (fun i : Fin 4 => iteratedDeriv (i.val+3) Fsrc w) j|) →
    0 < Tsrc → 2 ≤ M → Tsrc ≤ E*T →
    (∀ t∈Translations, t≠0) →
    let yp : Fin 2 → ℝ := ![ya,yb]
    let F := fun (i : Fin 2) u =>
      (Tsrc/T)*(Fsrc u-Fsrc (u+η*yp i))/(σsrc*η)
    let chartColor := fun (t : ℤ) ab j i =>
      (⌊yp i/a⌋,⌊((2*M^2/Tsrc)*(rat t ab j i:ℝ))/a⌋,
        ⌊((Tsrc/(2*M^2))*(rat t ab j i:ℝ)⁻¹)/a⌋)
    (∀ t∈Translations, ∀ ab∈Gaps t, ∀ j∈S t ab, ∀ i, chartColor t ab j i=chartKey t) →
    (0 < σ) →
    (δ ≤ min (modelPhaseThirdLower σ) 1) →
    (∀ i, Expdb.IsApproximateModelPhaseFunction (F i) σ 4 δ) →
    (0 < T) →
    (0 < M) →
    (0 < N) →
    (1 ≤ R) →
    (R ≤ M) →
    (0 < Q) →
    (T*N*R^2=M^3) →
    ((Q:ℝ)*N ≤ (K₀:ℝ)*R^2) →
    (∀ i, M ≤ A i) →
    (∀ i, A i+W i ≤ 2*M) →
    (∀ t∈Translations, ∀ ab∈Gaps t, ∀ j∈(S t ab), ∀ i, (x t ab) j i∈Ioo (1/2:ℝ) (W i-1/2)) →
    (∀ t∈Translations, ∀ ab∈Gaps t, ∀ j∈(S t ab), (x t ab) j 0∈Icc (base+N*(j:ℝ)) (base+N*((j:ℝ)+1))) →
    (∀ t∈Translations, ∀ ab∈Gaps t, ∀ j∈(S t ab), ∀ i, ((rat t ab) j i).den ≤ Q ∧ Q ≤ 2*((rat t ab) j i).den) →
    (0 < lambda) →
    (0 ≤ Uband) →
    (0 < θ) →
    (θ ≤ 1/24) →
    (∀ t∈Translations, ∀ ab∈Gaps t, ∀ j∈(S t ab), ∀ i, lambda ≤ |((rat t ab) j i:ℝ)| ∧ |((rat t ab) j i:ℝ)| ≤ Uband) →
    (∀ t∈Translations, ∀ ab∈Gaps t, ∀ j∈(S t ab), ∀ i, (((rat t ab) j i).den:ℤ) ∣ ((rat t ab) j i).num*(vinv t ab) j i-1) →
    (∀ t∈Translations, ∀ ab∈Gaps t, (v t ab)*(r t ab)-(e t ab)*(s t ab)=1) →
    (∀ t∈Translations, ∀ ab∈Gaps t, ((0:ℝ) < (r t ab) ∧ ((e t ab):ℝ)/(r t ab)=ab.1) ∨
      (((r t ab):ℝ) < 0 ∧ ((e t ab):ℝ)/(r t ab)=ab.2)) →
    (0 < Bcut) →
    (∀ t∈Translations, ∀ ab∈Gaps t, (s t ab) ≠ 0) →
    (∀ t∈Translations, ∀ ab∈Gaps t, ((e t ab):ℝ)/(r t ab)∈Refs) →
    (∀ t∈Translations, ∀ ab∈Gaps t, ((v t ab):ℝ)/(s t ab)∈Refs) →
    (∀ a∈Refs, ∀ b∈Refs, a ≠ b → ((Uref:ℝ)/R^2)/4 < |a-b|) →
    (∀ t∈Translations, ∀ ab∈Gaps t, ∀ j∈(S t ab), ∀ i, (x t ab) j i-(56*(Uref:ℝ)/modelPhaseThirdLower σ)*N∈Ioo (1/2:ℝ) (W i-1/2)) →
    (∀ t∈Translations, ∀ ab∈Gaps t, ∀ j∈(S t ab), ∀ i, (x t ab) j i+(56*(Uref:ℝ)/modelPhaseThirdLower σ)*N∈Ioo (1/2:ℝ) (W i-1/2)) →
    (1 ≤ Uref) →
    (2+168/modelPhaseThirdLower σ ≤ Bselect) →
    (7*Bcut ≤ modelPhaseThirdLower σ*Bselect) →
    (Bselect^2*(Uref:ℝ)^3*R^2 ≤ N^2) →
    (∀ t∈Translations, ∀ ab∈Gaps t, R^2 ≤ ((r t ab):ℝ)^2*(Uref:ℝ)) →
    (∀ t∈Translations, ∀ ab∈Gaps t, ab.2-ab.1 ≤ 7*(Uref:ℝ)/(2*R^2)) →
    (R ≤ (Q:ℝ)) →
    ((Uref:ℝ) ≤ (N/(Q:ℝ))^((2:ℝ)/3)/Bselect) →
    (N^10 ≤ M^3*R^7) →
    (∀ t∈Translations, ∀ ab∈Gaps t, ∀ j∈(S t ab), ((rat t ab) j 0:ℝ)∈Icc ab.1 ab.2) →
    (∀ t∈Translations, ∀ ab∈Gaps t, ab.1∈Refs ∧ ab.2∈Refs ∧ ab.1 < ab.2 ∧
      ∀ t∈Refs, ¬(ab.1 < t ∧ t < ab.2)) →
    let Vheight := T*(modelPhaseJetCoefficient σ 1+δ)/(2*M^2)
    let P₁ := fun (t : ℤ) (ab : ℝ × ℝ) => 1+(|((v t ab):ℝ)|+|((s t ab):ℝ)| *Vheight)*(Q:ℝ)
    let P₂ := fun (t : ℤ) (ab : ℝ × ℝ) => 1+(|((r t ab):ℝ)| *Vheight+|((e t ab):ℝ)|)*(Q:ℝ)
    let ε := modelPhaseThirdLower σ/(16*(σ*(σ+1)+1+2)*R^2)
    let Ccharts := fun (ab : ℝ × ℝ) => ⌊Real.logb (5/4) ((ab.2-ab.1)/(12*ε))⌋₊+1
    let sourceColor := fun (t : ℤ) (ab : ℝ × ℝ) => fun j i => (⌊(((rat t ab) j i).den:ℝ)/(θ*((Q:ℝ)/2))⌋,
      ⌊(((rat t ab) j i).num:ℝ)/(θ*(lambda*(Q:ℝ)/2))⌋)
    (∀ t∈Translations, ∀ ab∈Gaps t, ∀ j∈(S t ab), (sourceColor t ab) j 0=(sourceColor t ab) j 1) →
    let f := fun i => heathBrownPhysicalPhase (F i) T M (A i) 1
    (∀ t∈Translations, ∀ ab∈Gaps t, ∀ j∈(S t ab), ∀ i, iteratedDeriv 2 (f i) ((x t ab) j i)/2=((rat t ab) j i:ℝ)) →
    let q := fun (t : ℤ) (ab : ℝ × ℝ) => fun j i => ((rat t ab) j i).den
    let mu := fun (t : ℤ) (ab : ℝ × ℝ) => fun j i => iteratedDeriv 3 (f i) (round ((x t ab) j i))/6
    let ell := fun (t : ℤ) (ab : ℝ × ℝ) => fun j i => deriv (f i) (round ((x t ab) j i))
    let b := fun (t : ℤ) (ab : ℝ × ℝ) => fun j i => (⌊((q t ab) j i:ℝ)*(ell t ab) j i⌋+((parity t ab) j i:ℕ) : ℤ)
    let cround := fun (t : ℤ) (ab : ℝ × ℝ) => fun j i => round (((q t ab) j i:ℝ)*(ell t ab) j i)
    let tau := fun (t : ℤ) (ab : ℝ × ℝ) => fun j i => (((b t ab) j i:ℝ)-((q t ab) j i:ℝ)*(ell t ab) j i)/2
    let dual := fun (t : ℤ) (ab : ℝ × ℝ) => fun j i => -2*(mu t ab) j i*(Real.sqrt (2/(3*(mu t ab) j i*((q t ab) j i:ℝ))))^3
    let cloud := fun (t : ℤ) (ab : ℝ × ℝ) => fun j i => (![Int.fract (-((vinv t ab) j i:ℝ)*(b t ab) j i/(q t ab) j i),
      Int.fract (-((vinv t ab) j i:ℝ)/(q t ab) j i),(dual t ab) j i/Real.sqrt K₀,
      (3*(dual t ab) j i*(tau t ab) j i/2)/Real.sqrt K₀] : Fin 4 → ℝ)
    let radius : Fin 4 → ℝ := ![1/(12*(K₀:ℝ)),1/(12*(K₀:ℝ)^2),(1/(K₀:ℝ)^2)/12,(1/(K₀:ℝ))/12]
    (∀ t∈Translations, ∀ ab∈Gaps t, ∀ j∈(S t ab), (b t ab) j 0-(cround t ab) j 0=(b t ab) j 1-(cround t ab) j 1) →
    (∀ t∈Translations, ∀ ab∈Gaps t, ∀ j∈(S t ab), ∀ a, |(cloud t ab) j 0 a-(cloud t ab) j 1 a| ≤ 2*radius a) →
    let κ := modelPhaseThirdLower σ
    let Cphys := σ*(σ+1)+1
    let c := κ/6
    let J := Cphys/6
    let B := max 1 (max (2*Real.sqrt J) (8*J*Real.sqrt J/(3*c)))
    B*R^2/N^2 ≤ 1/2 →
    N ≤ R^2 →
    R ≤ N →
    N^3 ≤ M*R^2 →
    2*R^2 ≤ (Q:ℝ)*N →
    (∀ t∈Translations, Mat t 0*Mat t 3-Mat t 1*Mat t 2=1) →
    (∀ t∈Translations, ∀ ab∈Gaps t, ∀ j∈(S t ab), (Mat t 2:ℝ)*((rat t ab) j 0:ℝ)+Mat t 3=((q t ab) j 1:ℝ)/(q t ab) j 0) →
    (∀ t∈Translations, ∀ ab∈Gaps t, ∀ j∈(S t ab), ((Mat t 0:ℝ)*((rat t ab) j 0:ℝ)+Mat t 1)/
      ((Mat t 2:ℝ)*((rat t ab) j 0:ℝ)+Mat t 3)=((rat t ab) j 1:ℝ)) →
    (∀ t∈Translations, |(Mat t 2:ℝ)| ≤ (Q:ℝ)^2/(6*(K₀:ℝ)^2)) →
    let H := N/(Cphys+2)
    2 ≤ N →
    (∀ t∈Translations, ∀ ab∈Gaps t, ∀ j∈(S t ab), ∀ i, (x t ab) j i-H∈Ioo (1/2:ℝ) (W i-1/2)) →
    (∀ t∈Translations, ∀ ab∈Gaps t, ∀ j∈(S t ab), ∀ i, (x t ab) j i+H∈Ioo (1/2:ℝ) (W i-1/2)) →
    (∀ t∈Translations, ∀ ab∈Gaps t, ∀ j∈(S t ab), |((anchor t ab) j:ℝ)-((rat t ab) j 0:ℝ)| ≤ ε) →
    (∀ t∈Translations, ∀ ab∈Gaps t, ∀ j∈(S t ab), 256*(((anchor t ab) j).den:ℝ) ≤ (Q:ℝ)/3) →
    (∀ t∈Translations, ∀ ab∈Gaps t, ∀ j∈(S t ab), 256 ≤ (2*ε)*((Q:ℝ)/3)*((anchor t ab) j).den) →
    let C₂ := modelPhaseJetCoefficient σ 2+δ
    let C₃ := modelPhaseJetCoefficient σ 3+δ
    let Ct := C₂/2+5*C₃/12
    let Cc := C₂/κ+C₃/(2*κ)
    let Δ := (37*B/2+16*B*Cc+2*Ct+2*Cc)*(Q:ℝ)/N
    let Ccurv := (4/κ)*(B+2*quarticReciprocalConstant σ δ)
    let D := Δ+quarticNonlinearResidualConstant σ δ*(2*(Q:ℝ))/N
    let Kres := 4*(37*B/2+16*B*Cc+2*Ct+2*Cc+
      2*quarticNonlinearResidualConstant σ δ)/κ
    let Esize := κ/(16*(Cphys+2))
    let Dbase := 37*B/2+16*B*Cc+2*Ct+2*Cc+2*quarticNonlinearResidualConstant σ δ
    let Tbase := (2/κ)*(B+2*quarticReciprocalConstant σ δ)
    2*3840*128^2*105*(Dbase+64*Tbase*Esize^2) ≤ Bselect*Esize →
    D ≤ 1/2 → Δ < 1/2 → 61*Ccurv*Cphys ≤ Bcut →
    let Blabels := fun (t : ℤ) ab => 6+216*(⌊Real.logb 2 (P₁ t ab*P₂ t ab)⌋₊+1)
    let m0 := 6+Cmajor*(105+544*Bmajor)
    (∀ t∈Translations, ∀ ab∈Gaps t, Blabels t ab ≤ Bmajor) →
    (∀ t∈Translations, ∀ ab∈Gaps t, Ccharts ab ≤ Cmajor) →
    let Lunit := 2*κ/Cphys
    let Gamma := Cphys/κ
    let Cthird := Gamma*(32*Kres+9*quarticReciprocalConstant σ δ)
    let Aupper := 2*Cupper*(Cthird+1)*E^2*M^2/(κ*Lunit^3*N^4)
    let Bupper := Cupper*(Cthird+1)*E^2*M^2/(Lunit^2*N^4*(Uref:ℝ))+
      Dupper*(B+1)*E^2*M^2/(4*N^4*(Uref:ℝ))
    let Alower := 8*Clower*(Cthird+1)*R^4/(κ*Lunit^3*N^2)
    let Blower := 4*Clower*(Cthird+1)*R^4/(Lunit^2*N^2*(Uref:ℝ))+
      (4*Dlower*(B+1)*R^4)/(4*N^2*(Uref:ℝ))
    let DupperCut := θ*Uband
    let DlowerCut := θ/lambda
    ((∀ t∈Translations, Mat t 0=1 ∧ Mat t 2=0 ∧ Mat t 3=1 ∧ Mat t 1=t) →
      (∑ t∈Translations, ∑ ab∈Gaps t, ((S t ab).card:ℝ)) ≤ 4*(m0:ℝ)*(3*Aupper^((3:ℝ)⁻¹)*(DupperCut+2)^((2:ℝ)/3)+
        2*Bupper*(3+2*Real.log (DupperCut+2))+(1/2:ℝ)*(2*DupperCut+1))) ∧
    ((∀ t∈Translations, Mat t 0=1 ∧ Mat t 1=0 ∧ Mat t 3=1 ∧ Mat t 2=t) →
      (∑ t∈Translations, ∑ ab∈Gaps t, ((S t ab).card:ℝ)) ≤ 4*(m0:ℝ)*(3*Alower^((3:ℝ)⁻¹)*(DlowerCut+2)^((2:ℝ)/3)+
        2*Blower*(3+2*Real.log (DlowerCut+2))+(1/2:ℝ)*(2*DlowerCut+1))) := by
  classical
  obtain ⟨η₀,a,CU,CL,DU,DL,hη₀,hηcap,ha,hCU,hCL,hDU,hDL,hmassFn⟩ :=
    positive_difference_actual_fourier_charted_triangular_translation_sample_mass hσsrc hcsrc hUsrc
  refine ⟨η₀,a,CU,CL,DU,DL,hη₀,hηcap,ha,hCU,hCL,hDU,hDL,?_⟩
  intro Fsrc η ya yb Tsrc E Translations chartKey Uref Refs Gaps Bselect
    Bmajor Cmajor S Q K₀ inst rat vinv parity anchor Mat e r v s
    σ δ T M N R base Bcut lambda Uband θ A W x
    hη hηsmall hya hyb hreg hjets htests hTsrc hMtwo hsourceScale hTranslations
    yp F chartColor hchartColor
    hσ hδ hF hT hM hN hR hRM hQ hscale hmesh hA hW hx hwindow hden hlambda hUband hθ hθmax hcurv hinv hchart horientation hBcut hs hrefSet hparentSet hsep hwideL hwideU hUref hBselectSize hcutMargin hselectedWrap hreferenceDen hgapWidth hRQ hselectedUpper hscaleTen hfamilyGap hgap
    Vheight P₁ P₂ ε Ccharts sourceColor hsourceColor f hlevel
    q mu ell b cround tau dual cloud radius hcolor hnear
    κ Cphys c J B hsmall hNR hRN hNcube hminscale hMatdet hMatt hMatmap hMatgamma
    H hNtwo hL hU hanchor hcut hcount C₂ C₃ Ct Cc Δ
    Ccurv D Kres Esize Dbase Tbase hsize hD hΔ hBsize
    Blabels m0 hBmajor hCmajor Lunit Gamma Cthird Aupper Bupper Alower Blower DupperCut DlowerCut
  let Occupied := Translations.filter (fun t => ∃ ab∈Gaps t, (S t ab).Nonempty)
  have hinOcc : Occupied ⊆ Translations := Finset.filter_subset _ _
  have hsum : (∑ t∈Translations, ∑ ab∈Gaps t, ((S t ab).card:ℝ)) =
      ∑ t∈Occupied, ∑ ab∈Gaps t, ((S t ab).card:ℝ) := by
    symm
    apply Finset.sum_subset hinOcc
    intro t ht hnot
    apply Finset.sum_eq_zero
    intro ab hab
    have he : ¬(S t ab).Nonempty := by
      intro hh
      exact hnot (Finset.mem_filter.mpr ⟨ht,ab,hab,hh⟩)
    simp only [Finset.not_nonempty_iff_eq_empty.mp he,Finset.card_empty,Nat.cast_zero]
  have hcuts t (ht : t∈Occupied) :
      ((Mat t 0=1 ∧ Mat t 2=0 ∧ Mat t 3=1) → |(Mat t 1:ℝ)| ≤ DupperCut) ∧
      ((Mat t 0=1 ∧ Mat t 1=0 ∧ Mat t 3=1) → |(Mat t 2:ℝ)| ≤ DlowerCut) := by
    obtain ⟨ab,hab,j,hj⟩ := (Finset.mem_filter.mp ht).2
    exact rational_narrow_triangular_translation_bounds (rat t ab j) (Mat t) Q
      hQ hlambda hUband hθ (hcurv t (hinOcc ht) ab hab j hj)
      (hden t (hinOcc ht) ab hab j hj) (hsourceColor t (hinOcc ht) ab hab j hj)
      (hMatt t (hinOcc ht) ab hab j hj) (hMatmap t (hinOcc ht) ab hab j hj)
  have hbound (Dlim : ℝ) (hDlim : 0 ≤ Dlim)
      (hcutoff : ∀ t∈Occupied, |(t:ℝ)| ≤ Dlim) :
    ((∀ t∈Occupied, Mat t 0=1 ∧ Mat t 2=0 ∧ Mat t 3=1 ∧ Mat t 1=t) →
      (∑ t∈Occupied, ∑ ab∈Gaps t, ((S t ab).card:ℝ)) ≤ 4*(m0:ℝ)*(3*Aupper^((3:ℝ)⁻¹)*(Dlim+2)^((2:ℝ)/3)+
        2*Bupper*(3+2*Real.log (Dlim+2))+(1/2:ℝ)*(2*Dlim+1))) ∧
    ((∀ t∈Occupied, Mat t 0=1 ∧ Mat t 1=0 ∧ Mat t 3=1 ∧ Mat t 2=t) →
      (∑ t∈Occupied, ∑ ab∈Gaps t, ((S t ab).card:ℝ)) ≤ 4*(m0:ℝ)*(3*Alower^((3:ℝ)⁻¹)*(Dlim+2)^((2:ℝ)/3)+
        2*Blower*(3+2*Real.log (Dlim+2))+(1/2:ℝ)*(2*Dlim+1))) := by
    exact hmassFn Fsrc η ya yb Tsrc E Dlim Occupied chartKey Uref Refs Gaps
      (Bselect:=Bselect) Bmajor Cmajor S Q K₀ rat vinv parity anchor Mat e r v s
      (σ:=σ) (δ:=δ) (T:=T) (M:=M) (N:=N) (R:=R) (base:=base) (Bcut:=Bcut)
      (lambda:=lambda) (Uband:=Uband) (θ:=θ) A (W:=W) (x:=x)
      hη hηsmall hya hyb hreg hjets htests hTsrc hMtwo hsourceScale hDlim
      (fun t ht => ⟨hTranslations t (hinOcc ht),hcutoff t ht⟩) (fun t ht => hchartColor t (hinOcc ht))
      hσ hδ hF hT hM hN hR hRM hQ hscale hmesh hA hW (fun t ht => hx t (hinOcc ht)) (fun t ht => hwindow t (hinOcc ht)) (fun t ht => hden t (hinOcc ht)) hlambda hUband hθ hθmax (fun t ht => hcurv t (hinOcc ht)) (fun t ht => hinv t (hinOcc ht)) (fun t ht => hchart t (hinOcc ht)) (fun t ht => horientation t (hinOcc ht)) hBcut (fun t ht => hs t (hinOcc ht)) (fun t ht => hrefSet t (hinOcc ht)) (fun t ht => hparentSet t (hinOcc ht)) hsep (fun t ht => hwideL t (hinOcc ht)) (fun t ht => hwideU t (hinOcc ht)) hUref hBselectSize hcutMargin hselectedWrap (fun t ht => hreferenceDen t (hinOcc ht)) (fun t ht => hgapWidth t (hinOcc ht)) hRQ hselectedUpper hscaleTen (fun t ht => hfamilyGap t (hinOcc ht)) (fun t ht => hgap t (hinOcc ht))
      (fun t ht => hsourceColor t (hinOcc ht)) (fun t ht => hlevel t (hinOcc ht)) (fun t ht => hcolor t (hinOcc ht)) (fun t ht => hnear t (hinOcc ht)) hsmall hNR hRN hNcube hminscale (fun t ht => hMatdet t (hinOcc ht)) (fun t ht => hMatt t (hinOcc ht)) (fun t ht => hMatmap t (hinOcc ht)) (fun t ht => hMatgamma t (hinOcc ht)) hNtwo (fun t ht => hL t (hinOcc ht)) (fun t ht => hU t (hinOcc ht)) (fun t ht => hanchor t (hinOcc ht)) (fun t ht => hcut t (hinOcc ht)) (fun t ht => hcount t (hinOcc ht)) hsize hD hΔ hBsize (fun t ht => hBmajor t (hinOcc ht)) (fun t ht => hCmajor t (hinOcc ht))
  constructor
  · intro htri
    have hrange : ∀ t∈Occupied, |(t:ℝ)| ≤ DupperCut := by
      intro t ht
      have hsides := htri t (hinOcc ht)
      have hh := (hcuts t ht).1 ⟨hsides.1,hsides.2.1,hsides.2.2.1⟩
      simpa only [hsides.2.2.2] using hh
    rw [hsum]
    exact (hbound DupperCut (mul_nonneg hθ.le hUband) hrange).1
      (fun t ht => htri t (hinOcc ht))
  · intro htri
    have hrange : ∀ t∈Occupied, |(t:ℝ)| ≤ DlowerCut := by
      intro t ht
      have hsides := htri t (hinOcc ht)
      have hh := (hcuts t ht).2 ⟨hsides.1,hsides.2.1,hsides.2.2.1⟩
      simpa only [hsides.2.2.2] using hh
    rw [hsum]
    exact (hbound DlowerCut (div_nonneg hθ.le hlambda.le) hrange).2
      (fun t ht => htri t (hinOcc ht))

example
    {σsrc csrc Usrc : ℝ} (hσsrc : 0 < σsrc) (hcsrc : 0 < csrc) (hUsrc : 0 < Usrc) :
    ∃ η₀ a Cupper Clower Dupper Dlower : ℝ, 0 < η₀ ∧ η₀ ≤ 1/8 ∧ 0 < a ∧
      0 < Cupper ∧ 0 < Clower ∧ 0 < Dupper ∧ 0 < Dlower ∧
    ∀ (Fsrc : ℝ → ℝ) (η ya yb Tsrc E : ℝ)
    (Translations : Finset ℤ) (chartKey : ℤ → ℤ × ℤ × ℤ)
    (Uref : ℕ) (Refs : Finset ℝ) (Gaps : ℤ → Finset (ℝ × ℝ)) {Bselect : ℝ}
    (Bmajor Cmajor : ℕ)
    (S : ℤ → ℝ × ℝ → Finset ℕ) (Q K₀ : ℕ) [NeZero K₀]
    (rat : ℤ → ℝ × ℝ → ℕ → Fin 2 → ℚ) (vinv : ℤ → ℝ × ℝ → ℕ → Fin 2 → ℤ)
    (parity : ℤ → ℝ × ℝ → ℕ → Fin 2 → Fin 2) (anchor : ℤ → ℝ × ℝ → ℕ → ℚ)
    (Mat : ℤ → Fin 4 → ℤ) (e r v s : ℤ → ℝ × ℝ → ℤ)
    {σ δ T M N R base Bcut lambda Uband θ : ℝ}
    (A : Fin 2 → ℤ) {W : Fin 2 → ℝ}
    {x : ℤ → ℝ × ℝ → ℕ → Fin 2 → ℝ},
    0 < η → η ≤ η₀ →
    ya∈Icc (1:ℝ) 2 → yb∈Icc (1:ℝ) 2 →
    (∀ w, 0 < w → ContDiffAt ℝ ∞ Fsrc w) →
    (∀ w∈Icc (1/2:ℝ) 3, ∀ n ≤ 6, |iteratedDeriv (n+1) Fsrc w| ≤ Usrc) →
    (∀ w∈Icc (1/2:ℝ) 3, ∀ j,
      csrc ≤ |HuxleyModel.tests (fun i : Fin 4 => iteratedDeriv (i.val+3) Fsrc w) j|) →
    0 < Tsrc → 2 ≤ M → Tsrc ≤ E*T →
    (∀ t∈Translations, t≠0) →
    let yp : Fin 2 → ℝ := ![ya,yb]
    let F := fun (i : Fin 2) u =>
      (Tsrc/T)*(Fsrc u-Fsrc (u+η*yp i))/(σsrc*η)
    let chartColor := fun (t : ℤ) ab j i =>
      (⌊yp i/a⌋,⌊((2*M^2/Tsrc)*(rat t ab j i:ℝ))/a⌋,
        ⌊((Tsrc/(2*M^2))*(rat t ab j i:ℝ)⁻¹)/a⌋)
    (∀ t∈Translations, ∀ ab∈Gaps t, ∀ j∈S t ab, ∀ i, chartColor t ab j i=chartKey t) →
    (0 < σ) →
    (δ ≤ min (modelPhaseThirdLower σ) 1) →
    (∀ i, Expdb.IsApproximateModelPhaseFunction (F i) σ 4 δ) →
    (0 < T) →
    (0 < M) →
    (0 < N) →
    (1 ≤ R) →
    (R ≤ M) →
    (0 < Q) →
    (T*N*R^2=M^3) →
    ((Q:ℝ)*N ≤ (K₀:ℝ)*R^2) →
    (∀ i, M ≤ A i) →
    (∀ i, A i+W i ≤ 2*M) →
    (∀ t∈Translations, ∀ ab∈Gaps t, ∀ j∈(S t ab), ∀ i, (x t ab) j i∈Ioo (1/2:ℝ) (W i-1/2)) →
    (∀ t∈Translations, ∀ ab∈Gaps t, ∀ j∈(S t ab), (x t ab) j 0∈Icc (base+N*(j:ℝ)) (base+N*((j:ℝ)+1))) →
    (∀ t∈Translations, ∀ ab∈Gaps t, ∀ j∈(S t ab), ∀ i, ((rat t ab) j i).den ≤ Q ∧ Q ≤ 2*((rat t ab) j i).den) →
    (0 < lambda) →
    (0 ≤ Uband) →
    (0 < θ) →
    (θ ≤ 1/24) →
    (∀ t∈Translations, ∀ ab∈Gaps t, ∀ j∈(S t ab), ∀ i, lambda ≤ |((rat t ab) j i:ℝ)| ∧ |((rat t ab) j i:ℝ)| ≤ Uband) →
    (∀ t∈Translations, ∀ ab∈Gaps t, ∀ j∈(S t ab), ∀ i, (((rat t ab) j i).den:ℤ) ∣ ((rat t ab) j i).num*(vinv t ab) j i-1) →
    (∀ t∈Translations, ∀ ab∈Gaps t, (v t ab)*(r t ab)-(e t ab)*(s t ab)=1) →
    (∀ t∈Translations, ∀ ab∈Gaps t, ((0:ℝ) < (r t ab) ∧ ((e t ab):ℝ)/(r t ab)=ab.1) ∨
      (((r t ab):ℝ) < 0 ∧ ((e t ab):ℝ)/(r t ab)=ab.2)) →
    (0 < Bcut) →
    (∀ t∈Translations, ∀ ab∈Gaps t, (s t ab) ≠ 0) →
    (∀ t∈Translations, ∀ ab∈Gaps t, ((e t ab):ℝ)/(r t ab)∈Refs) →
    (∀ t∈Translations, ∀ ab∈Gaps t, ((v t ab):ℝ)/(s t ab)∈Refs) →
    (∀ a∈Refs, ∀ b∈Refs, a ≠ b → ((Uref:ℝ)/R^2)/4 < |a-b|) →
    (∀ t∈Translations, ∀ ab∈Gaps t, ∀ j∈(S t ab), ∀ i, (x t ab) j i-(56*(Uref:ℝ)/modelPhaseThirdLower σ)*N∈Ioo (1/2:ℝ) (W i-1/2)) →
    (∀ t∈Translations, ∀ ab∈Gaps t, ∀ j∈(S t ab), ∀ i, (x t ab) j i+(56*(Uref:ℝ)/modelPhaseThirdLower σ)*N∈Ioo (1/2:ℝ) (W i-1/2)) →
    (1 ≤ Uref) →
    (2+168/modelPhaseThirdLower σ ≤ Bselect) →
    (7*Bcut ≤ modelPhaseThirdLower σ*Bselect) →
    (Bselect^2*(Uref:ℝ)^3*R^2 ≤ N^2) →
    (∀ t∈Translations, ∀ ab∈Gaps t, R^2 ≤ ((r t ab):ℝ)^2*(Uref:ℝ)) →
    (∀ t∈Translations, ∀ ab∈Gaps t, ab.2-ab.1 ≤ 7*(Uref:ℝ)/(2*R^2)) →
    (R ≤ (Q:ℝ)) →
    ((Uref:ℝ) ≤ (N/(Q:ℝ))^((2:ℝ)/3)/Bselect) →
    (N^10 ≤ M^3*R^7) →
    (∀ t∈Translations, ∀ ab∈Gaps t, ∀ j∈(S t ab), ((rat t ab) j 0:ℝ)∈Icc ab.1 ab.2) →
    (∀ t∈Translations, ∀ ab∈Gaps t, ab.1∈Refs ∧ ab.2∈Refs ∧ ab.1 < ab.2 ∧
      ∀ t∈Refs, ¬(ab.1 < t ∧ t < ab.2)) →
    let Vheight := T*(modelPhaseJetCoefficient σ 1+δ)/(2*M^2)
    let P₁ := fun (t : ℤ) (ab : ℝ × ℝ) => 1+(|((v t ab):ℝ)|+|((s t ab):ℝ)| *Vheight)*(Q:ℝ)
    let P₂ := fun (t : ℤ) (ab : ℝ × ℝ) => 1+(|((r t ab):ℝ)| *Vheight+|((e t ab):ℝ)|)*(Q:ℝ)
    let ε := modelPhaseThirdLower σ/(16*(σ*(σ+1)+1+2)*R^2)
    let Ccharts := fun (ab : ℝ × ℝ) => ⌊Real.logb (5/4) ((ab.2-ab.1)/(12*ε))⌋₊+1
    let sourceColor := fun (t : ℤ) (ab : ℝ × ℝ) => fun j i => (⌊(((rat t ab) j i).den:ℝ)/(θ*((Q:ℝ)/2))⌋,
      ⌊(((rat t ab) j i).num:ℝ)/(θ*(lambda*(Q:ℝ)/2))⌋)
    (∀ t∈Translations, ∀ ab∈Gaps t, ∀ j∈(S t ab), (sourceColor t ab) j 0=(sourceColor t ab) j 1) →
    let f := fun i => heathBrownPhysicalPhase (F i) T M (A i) 1
    (∀ t∈Translations, ∀ ab∈Gaps t, ∀ j∈(S t ab), ∀ i, iteratedDeriv 2 (f i) ((x t ab) j i)/2=((rat t ab) j i:ℝ)) →
    let q := fun (t : ℤ) (ab : ℝ × ℝ) => fun j i => ((rat t ab) j i).den
    let mu := fun (t : ℤ) (ab : ℝ × ℝ) => fun j i => iteratedDeriv 3 (f i) (round ((x t ab) j i))/6
    let ell := fun (t : ℤ) (ab : ℝ × ℝ) => fun j i => deriv (f i) (round ((x t ab) j i))
    let b := fun (t : ℤ) (ab : ℝ × ℝ) => fun j i => (⌊((q t ab) j i:ℝ)*(ell t ab) j i⌋+((parity t ab) j i:ℕ) : ℤ)
    let cround := fun (t : ℤ) (ab : ℝ × ℝ) => fun j i => round (((q t ab) j i:ℝ)*(ell t ab) j i)
    let tau := fun (t : ℤ) (ab : ℝ × ℝ) => fun j i => (((b t ab) j i:ℝ)-((q t ab) j i:ℝ)*(ell t ab) j i)/2
    let dual := fun (t : ℤ) (ab : ℝ × ℝ) => fun j i => -2*(mu t ab) j i*(Real.sqrt (2/(3*(mu t ab) j i*((q t ab) j i:ℝ))))^3
    let cloud := fun (t : ℤ) (ab : ℝ × ℝ) => fun j i => (![Int.fract (-((vinv t ab) j i:ℝ)*(b t ab) j i/(q t ab) j i),
      Int.fract (-((vinv t ab) j i:ℝ)/(q t ab) j i),(dual t ab) j i/Real.sqrt K₀,
      (3*(dual t ab) j i*(tau t ab) j i/2)/Real.sqrt K₀] : Fin 4 → ℝ)
    let radius : Fin 4 → ℝ := ![1/(12*(K₀:ℝ)),1/(12*(K₀:ℝ)^2),(1/(K₀:ℝ)^2)/12,(1/(K₀:ℝ))/12]
    (∀ t∈Translations, ∀ ab∈Gaps t, ∀ j∈(S t ab), (b t ab) j 0-(cround t ab) j 0=(b t ab) j 1-(cround t ab) j 1) →
    (∀ t∈Translations, ∀ ab∈Gaps t, ∀ j∈(S t ab), ∀ a, |(cloud t ab) j 0 a-(cloud t ab) j 1 a| ≤ 2*radius a) →
    let κ := modelPhaseThirdLower σ
    let Cphys := σ*(σ+1)+1
    let c := κ/6
    let J := Cphys/6
    let B := max 1 (max (2*Real.sqrt J) (8*J*Real.sqrt J/(3*c)))
    B*R^2/N^2 ≤ 1/2 →
    N ≤ R^2 →
    R ≤ N →
    N^3 ≤ M*R^2 →
    2*R^2 ≤ (Q:ℝ)*N →
    (∀ t∈Translations, Mat t 0*Mat t 3-Mat t 1*Mat t 2=1) →
    (∀ t∈Translations, ∀ ab∈Gaps t, ∀ j∈(S t ab), (Mat t 2:ℝ)*((rat t ab) j 0:ℝ)+Mat t 3=((q t ab) j 1:ℝ)/(q t ab) j 0) →
    (∀ t∈Translations, ∀ ab∈Gaps t, ∀ j∈(S t ab), ((Mat t 0:ℝ)*((rat t ab) j 0:ℝ)+Mat t 1)/
      ((Mat t 2:ℝ)*((rat t ab) j 0:ℝ)+Mat t 3)=((rat t ab) j 1:ℝ)) →
    (∀ t∈Translations, |(Mat t 2:ℝ)| ≤ (Q:ℝ)^2/(6*(K₀:ℝ)^2)) →
    let H := N/(Cphys+2)
    2 ≤ N →
    (∀ t∈Translations, ∀ ab∈Gaps t, ∀ j∈(S t ab), ∀ i, (x t ab) j i-H∈Ioo (1/2:ℝ) (W i-1/2)) →
    (∀ t∈Translations, ∀ ab∈Gaps t, ∀ j∈(S t ab), ∀ i, (x t ab) j i+H∈Ioo (1/2:ℝ) (W i-1/2)) →
    (∀ t∈Translations, ∀ ab∈Gaps t, ∀ j∈(S t ab), |((anchor t ab) j:ℝ)-((rat t ab) j 0:ℝ)| ≤ ε) →
    (∀ t∈Translations, ∀ ab∈Gaps t, ∀ j∈(S t ab), 256*(((anchor t ab) j).den:ℝ) ≤ (Q:ℝ)/3) →
    (∀ t∈Translations, ∀ ab∈Gaps t, ∀ j∈(S t ab), 256 ≤ (2*ε)*((Q:ℝ)/3)*((anchor t ab) j).den) →
    let C₂ := modelPhaseJetCoefficient σ 2+δ
    let C₃ := modelPhaseJetCoefficient σ 3+δ
    let Ct := C₂/2+5*C₃/12
    let Cc := C₂/κ+C₃/(2*κ)
    let Δ := (37*B/2+16*B*Cc+2*Ct+2*Cc)*(Q:ℝ)/N
    let Ccurv := (4/κ)*(B+2*quarticReciprocalConstant σ δ)
    let D := Δ+quarticNonlinearResidualConstant σ δ*(2*(Q:ℝ))/N
    let Kres := 4*(37*B/2+16*B*Cc+2*Ct+2*Cc+
      2*quarticNonlinearResidualConstant σ δ)/κ
    let Esize := κ/(16*(Cphys+2))
    let Dbase := 37*B/2+16*B*Cc+2*Ct+2*Cc+2*quarticNonlinearResidualConstant σ δ
    let Tbase := (2/κ)*(B+2*quarticReciprocalConstant σ δ)
    2*3840*128^2*105*(Dbase+64*Tbase*Esize^2) ≤ Bselect*Esize →
    D ≤ 1/2 → Δ < 1/2 → 61*Ccurv*Cphys ≤ Bcut →
    let Blabels := fun (t : ℤ) ab => 6+216*(⌊Real.logb 2 (P₁ t ab*P₂ t ab)⌋₊+1)
    let m0 := 6+Cmajor*(105+544*Bmajor)
    (∀ t∈Translations, ∀ ab∈Gaps t, Blabels t ab ≤ Bmajor) →
    (∀ t∈Translations, ∀ ab∈Gaps t, Ccharts ab ≤ Cmajor) →
    let Lunit := 2*κ/Cphys
    let Gamma := Cphys/κ
    let Cthird := Gamma*(32*Kres+9*quarticReciprocalConstant σ δ)
    let Aupper := 2*Cupper*(Cthird+1)*E^2*M^2/(κ*Lunit^3*N^4)
    let Bupper := Cupper*(Cthird+1)*E^2*M^2/(Lunit^2*N^4*(Uref:ℝ))+
      Dupper*(B+1)*E^2*M^2/(4*N^4*(Uref:ℝ))
    let Alower := 8*Clower*(Cthird+1)*R^4/(κ*Lunit^3*N^2)
    let Blower := 4*Clower*(Cthird+1)*R^4/(Lunit^2*N^2*(Uref:ℝ))+
      (4*Dlower*(B+1)*R^4)/(4*N^2*(Uref:ℝ))
    let DupperCut := θ*Uband
    let DlowerCut := θ/lambda
    ((∀ t∈Translations, Mat t 0=1 ∧ Mat t 2=0 ∧ Mat t 3=1 ∧ Mat t 1=t) →
      (∑ t∈Translations, ∑ ab∈Gaps t, ((S t ab).card:ℝ)) ≤ 4*(m0:ℝ)*(3*Aupper^((3:ℝ)⁻¹)*(DupperCut+2)^((2:ℝ)/3)+
        2*Bupper*(3+2*Real.log (DupperCut+2))+(1/2:ℝ)*(2*DupperCut+1))) ∧
    ((∀ t∈Translations, Mat t 0=1 ∧ Mat t 1=0 ∧ Mat t 3=1 ∧ Mat t 2=t) →
      (∑ t∈Translations, ∑ ab∈Gaps t, ((S t ab).card:ℝ)) ≤ 4*(m0:ℝ)*(3*Alower^((3:ℝ)⁻¹)*(DlowerCut+2)^((2:ℝ)/3)+
        2*Blower*(3+2*Real.log (DlowerCut+2))+(1/2:ℝ)*(2*DlowerCut+1))) :=
  HuxleyTriangularWeightScratch.positive_difference_actual_fourier_charted_triangular_source_cutoff_sample_mass (σsrc:=σsrc) (csrc:=csrc) (Usrc:=Usrc) hσsrc hcsrc hUsrc

end HuxleyTriangularWeightScratch
#print axioms HuxleyTriangularWeightScratch.inverse_cuberoot_nat_prefix
#print axioms HuxleyTriangularWeightScratch.integer_inverse_cuberoot_sum
#print axioms HuxleyTriangularWeightScratch.integer_cubic_reciprocal_weight_sum
#print axioms HuxleyTriangularWeightScratch.triangular_weight_normalize
#print axioms HuxleyTriangularWeightScratch.positive_difference_actual_fourier_charted_triangular_translation_sample_mass
#print axioms HuxleyTriangularWeightScratch.physical_source_triangular_constants_nonneg
#print axioms HuxleyTriangularWeightScratch.rational_narrow_triangular_translation_bounds
#print axioms HuxleyTriangularWeightScratch.positive_difference_actual_fourier_charted_triangular_source_cutoff_sample_mass
