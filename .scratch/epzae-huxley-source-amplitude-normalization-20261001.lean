import TaoTrudgianYang2025.HuxleyLinearForms
open Set TaoTrudgianYang2025 TaoTrudgianYang2025.HuxleyRationalPhase
open scoped BigOperators Classical ContDiff
namespace HuxleySourceAmplitudeNormalizationScratch
private theorem source_tests_const_mul (ampl : ℝ) (v : Fin 4 → ℝ) (j : Fin 7) :
    HuxleyModel.tests (fun i => ampl*v i) j=
      ampl^(![1,1,1,2,2,2,4] j)*HuxleyModel.tests v j := by
  fin_cases j <;> simp [HuxleyModel.tests,Matrix.det_fin_three] <;> ring

private theorem source_tests_uniform_positive_rescaling
    {c lo ampl : ℝ} (hc : 0 < c) (hlo : 0 < lo) (hampl : lo ≤ ampl)
    (v : Fin 4 → ℝ) (hv : ∀ j, c ≤ |HuxleyModel.tests v j|) :
    ∀ j, c*min lo (min (lo^2) (lo^4)) ≤
      |HuxleyModel.tests (fun i => ampl*v i) j| := by
  have hamplpos := hlo.trans_le hampl
  have h1 : min lo (min (lo^2) (lo^4)) ≤ ampl := (min_le_left _ _).trans hampl
  have h2 : min lo (min (lo^2) (lo^4)) ≤ ampl^2 :=
    ((min_le_right _ _).trans (min_le_left _ _)).trans (pow_le_pow_left₀ hlo.le hampl 2)
  have h4 : min lo (min (lo^2) (lo^4)) ≤ ampl^4 :=
    ((min_le_right _ _).trans (min_le_right _ _)).trans (pow_le_pow_left₀ hlo.le hampl 4)
  intro j
  rw [source_tests_const_mul,abs_mul,abs_of_nonneg (pow_nonneg hamplpos.le _)]
  have hd : min lo (min (lo^2) (lo^4)) ≤ ampl^(![1,1,1,2,2,2,4] j) := by
    fin_cases j <;> dsimp
    all_goals first | exact h2 | exact h4 | simpa only [pow_one] using h1
  calc
    c*min lo (min (lo^2) (lo^4))=min lo (min (lo^2) (lo^4))*c := mul_comm _ _
    _ ≤ _ := mul_le_mul hd (hv j) hc.le (pow_nonneg hamplpos.le _)

private theorem source_uniform_amplitude_normalization
    (F : ℝ → ℝ) {c U lo hi : ℝ}
    (hc : 0 < c) (hU : 0 < U) (hlo : 0 < lo) (hhi : 0 < hi)
    (hreg : ∀ w, 0 < w → ContDiffAt ℝ ∞ F w)
    (hjets : ∀ w∈Icc (1/2:ℝ) 3, ∀ n ≤ 6, |iteratedDeriv (n+1) F w| ≤ U)
    (htests : ∀ w∈Icc (1/2:ℝ) 3, ∀ j,
      c ≤ |HuxleyModel.tests (fun i : Fin 4 => iteratedDeriv (i.val+3) F w) j|)
    (hnegative : ∀ w∈Icc (1/2:ℝ) 3, iteratedDeriv 4 F w ≤ -c) :
    let cnew := c*min lo (min (lo^2) (lo^4))
    let Unew := hi*U
    0 < cnew ∧ 0 < Unew ∧
    ∀ ampl : ℝ, lo ≤ ampl → ampl ≤ hi →
    let Fscaled := fun w => ampl*F w
    (∀ w, 0 < w → ContDiffAt ℝ ∞ Fscaled w) ∧
    (∀ w∈Icc (1/2:ℝ) 3, ∀ n ≤ 6, |iteratedDeriv (n+1) Fscaled w| ≤ Unew) ∧
    (∀ w∈Icc (1/2:ℝ) 3, ∀ j,
      cnew ≤ |HuxleyModel.tests (fun i : Fin 4 => iteratedDeriv (i.val+3) Fscaled w) j|) ∧
    (∀ w∈Icc (1/2:ℝ) 3, iteratedDeriv 4 Fscaled w ≤ -cnew) ∧
    (∀ Traw Tmodel σsrc η y M w : ℝ, Tmodel*ampl=Traw →
      Tmodel*(Fscaled (w/M)-Fscaled (w/M+η*y))/(σsrc*η)=
        Traw*(F (w/M)-F (w/M+η*y))/(σsrc*η)) := by
  intro cnew Unew
  have hcnew : 0 < cnew :=
    mul_pos hc (lt_min hlo (lt_min (pow_pos hlo 2) (pow_pos hlo 4)))
  refine ⟨hcnew,mul_pos hhi hU,?_⟩
  intro ampl hampl hamplhi Fscaled
  have hamplpos := hlo.trans_le hampl
  have hderiv n w : iteratedDeriv n Fscaled w=ampl*iteratedDeriv n F w := by
    exact iteratedDeriv_const_mul_field ampl F
  refine ⟨fun w hw => contDiffAt_const.mul (hreg w hw),?_,?_,?_,?_⟩
  · intro w hw n hn
    rw [hderiv,abs_mul,abs_of_pos hamplpos]
    exact mul_le_mul hamplhi (hjets w hw n hn) (abs_nonneg _) hhi.le
  · intro w hw j
    have he : (fun i : Fin 4 => iteratedDeriv (i.val+3) Fscaled w)=
        (fun i : Fin 4 => ampl*iteratedDeriv (i.val+3) F w) := by
      funext i
      exact hderiv _ _
    rw [he]
    exact source_tests_uniform_positive_rescaling hc hlo hampl
      (fun i : Fin 4 => iteratedDeriv (i.val+3) F w) (htests w hw) j
  · intro w hw
    rw [hderiv]
    have hlc : cnew ≤ ampl*c := by
      calc
        cnew=c*min lo (min (lo^2) (lo^4)) := rfl
        _ ≤ c*lo := mul_le_mul_of_nonneg_left (min_le_left _ _) hc.le
        _ ≤ c*ampl := mul_le_mul_of_nonneg_left hampl hc.le
        _ = ampl*c := mul_comm _ _
    have hh := mul_le_mul_of_nonneg_left (hnegative w hw) hamplpos.le
    linarith only [hh,hlc]
  · intro Traw Tmodel σsrc η y M w hT
    change Tmodel*(ampl*F (w/M)-ampl*F (w/M+η*y))/(σsrc*η)=_
    calc
      _ = (Tmodel*ampl)*(F (w/M)-F (w/M+η*y))/(σsrc*η) := by ring
      _ = _ := by rw [hT]

example (ampl : ℝ) (v : Fin 4 → ℝ) (j : Fin 7) :
    HuxleyModel.tests (fun i => ampl*v i) j=
      ampl^(![1,1,1,2,2,2,4] j)*HuxleyModel.tests v j :=
  HuxleySourceAmplitudeNormalizationScratch.source_tests_const_mul ampl v j

example
    {c lo ampl : ℝ} (hc : 0 < c) (hlo : 0 < lo) (hampl : lo ≤ ampl)
    (v : Fin 4 → ℝ) (hv : ∀ j, c ≤ |HuxleyModel.tests v j|) :
    ∀ j, c*min lo (min (lo^2) (lo^4)) ≤
      |HuxleyModel.tests (fun i => ampl*v i) j| :=
  HuxleySourceAmplitudeNormalizationScratch.source_tests_uniform_positive_rescaling (c:=c) (lo:=lo) (ampl:=ampl) hc hlo hampl v hv

example
    (F : ℝ → ℝ) {c U lo hi : ℝ}
    (hc : 0 < c) (hU : 0 < U) (hlo : 0 < lo) (hhi : 0 < hi)
    (hreg : ∀ w, 0 < w → ContDiffAt ℝ ∞ F w)
    (hjets : ∀ w∈Icc (1/2:ℝ) 3, ∀ n ≤ 6, |iteratedDeriv (n+1) F w| ≤ U)
    (htests : ∀ w∈Icc (1/2:ℝ) 3, ∀ j,
      c ≤ |HuxleyModel.tests (fun i : Fin 4 => iteratedDeriv (i.val+3) F w) j|)
    (hnegative : ∀ w∈Icc (1/2:ℝ) 3, iteratedDeriv 4 F w ≤ -c) :
    let cnew := c*min lo (min (lo^2) (lo^4))
    let Unew := hi*U
    0 < cnew ∧ 0 < Unew ∧
    ∀ ampl : ℝ, lo ≤ ampl → ampl ≤ hi →
    let Fscaled := fun w => ampl*F w
    (∀ w, 0 < w → ContDiffAt ℝ ∞ Fscaled w) ∧
    (∀ w∈Icc (1/2:ℝ) 3, ∀ n ≤ 6, |iteratedDeriv (n+1) Fscaled w| ≤ Unew) ∧
    (∀ w∈Icc (1/2:ℝ) 3, ∀ j,
      cnew ≤ |HuxleyModel.tests (fun i : Fin 4 => iteratedDeriv (i.val+3) Fscaled w) j|) ∧
    (∀ w∈Icc (1/2:ℝ) 3, iteratedDeriv 4 Fscaled w ≤ -cnew) ∧
    (∀ Traw Tmodel σsrc η y M w : ℝ, Tmodel*ampl=Traw →
      Tmodel*(Fscaled (w/M)-Fscaled (w/M+η*y))/(σsrc*η)=
        Traw*(F (w/M)-F (w/M+η*y))/(σsrc*η)) :=
  HuxleySourceAmplitudeNormalizationScratch.source_uniform_amplitude_normalization F (c:=c) (U:=U) (lo:=lo) (hi:=hi) hc hU hlo hhi hreg hjets htests hnegative

/-- The actual colored extension is rescaled to a common normalized source
with constants chosen before the color center and all physical parameters.
Its source phase and approximate model now use the SAME Tnew and Rnew. -/
theorem approximateModelPhase_enlarged_colored_common_scale_source
    {σ ε xi : ℝ} (hσ : 0 < σ) (hε : 0 < ε) (hxi : 0 < xi)
    (P : ℕ) (hP : 5 ≤ P) :
    ∃ δ η₀ a c J : ℝ, 0 < δ ∧ 0 < η₀ ∧ η₀ ≤ 1/8 ∧ 0 < a ∧ 0 < c ∧ 0 < J ∧
      c ≤ 4*modelPhaseThirdLower (σ+1)*xi/((σ+1)*(σ+2)+3) ∧
      ∀ (M : ℝ) (F : ℝ → ℝ), 1 ≤ M →
      Expdb.IsApproximateModelPhaseFunction F σ (P+2) δ →
      ∃ Fext : ℝ → ℝ,
        (∀ w, 0 < w → ContDiffAt ℝ ∞ Fext w) ∧
        (∀ w∈Icc (1/2:ℝ) 3, ∀ p ≤ P+1,
          |iteratedDeriv (p+1) Fext w-iteratedDeriv p (Expdb.modelPhase σ) w| ≤ ε) ∧
        (∀ (T : ℝ) (m n : ℕ), M ≤ (m:ℝ) → (n:ℝ) ≤ 2*M →
          ‖Expdb.exponentialSumAt F T M m n-Expdb.exponentialSumAt Fext T M m n‖ ≤ 6) ∧
        ∀ {ι : Type*} (S : Finset ι) (y : ι → ℝ) (η : ℝ),
          (∀ i∈S, y i∈Icc (1:ℝ) 2) → 0 < η → η ≤ η₀ →
          let color := fun i => ⌊y i/a⌋
          let Cap := 4/a+3
          ((S.image color).card:ℝ) ≤ Cap ∧
          (∀ z : ι → ℂ, ‖∑ i∈S,z i‖^12 ≤
            Cap^11*∑ j∈S.image color, ‖∑ i∈S.filter (fun i => color i=j),z i‖^12) ∧
          ∀ j∈S.image color, ∃ i₀∈S, color i₀=j ∧
            let Fsrc := fun w => (xi/(σ*y i₀))*Fext w
            (∀ w, 0 < w → ContDiffAt ℝ ∞ Fsrc w) ∧
            (∀ w∈Icc (1/2:ℝ) 3, ∀ n ≤ 6, |iteratedDeriv (n+1) Fsrc w| ≤ J) ∧
            (∀ w∈Icc (1/2:ℝ) 3, ∀ j,
              c ≤ |HuxleyModel.tests (fun i : Fin 4 => iteratedDeriv (i.val+3) Fsrc w) j|) ∧
            (∀ w∈Icc (1/2:ℝ) 3, iteratedDeriv 4 Fsrc w ≤ -c) ∧
            ∀ T N R : ℝ, 0 < T → 0 < R → T*N*R^2=M^3 →
            let Tnew := T*σ*y i₀/xi
            let Rnew := R*Real.sqrt (xi/(σ*y i₀))
            0 < Tnew ∧ 0 < Rnew ∧ Rnew^2=R^2*xi/(σ*y i₀) ∧
              Tnew*N*Rnew^2=M^3 ∧
            ∀ i∈S, color i=j →
              let G := fun u => (Fsrc u-Fsrc (u+η*y i))/(xi*η)
              let f := fun w => Tnew*(Fsrc (w/M)-Fsrc (w/M+η*y i))/(xi*η)
              Expdb.IsApproximateModelPhaseFunction G (σ+1) P ε ∧
                (∀ w : ℝ, f w=T*(Fext (w/M)-Fext (w/M+η*y i))/(xi*η)) ∧
                (∀ A x : ℝ, heathBrownPhysicalPhase G Tnew M A 1 x=f (A+x)) ∧
                (∀ (A : ℤ) (w : ℝ) (k : ℕ),
                  iteratedDeriv k (heathBrownPhysicalPhase G Tnew M A 1) (round (w-A))=
                    iteratedDeriv k f (round w)) := by
  obtain ⟨δ,η₀,a,c₀,J₀,hδ,hη₀,hηcap,ha,hc₀,hJ₀,hsource⟩ :=
    approximateModelPhase_enlarged_colored_linked_source_tests hσ P hP hε
  let lo := xi/(2*σ)
  let hi := xi/σ
  let cpre := c₀*min lo (min (lo^2) (lo^4))
  let J := hi*J₀
  let κ := modelPhaseThirdLower (σ+1)
  let c := min cpre (4*κ*xi/((σ+1)*(σ+2)+3))
  have hlo : 0 < lo := div_pos hxi (mul_pos (by norm_num) hσ)
  have hhi : 0 < hi := div_pos hxi hσ
  have hcpre : 0 < cpre := mul_pos hc₀ (lt_min hlo (lt_min (pow_pos hlo 2) (pow_pos hlo 4)))
  have hκ : 0 < κ := modelPhaseThirdLower_pos (by linarith only [hσ])
  have hden : 0 < (σ+1)*(σ+2)+3 := by positivity
  have hc : 0 < c := lt_min hcpre (div_pos (mul_pos (mul_pos (by norm_num) hκ) hxi) hden)
  have hccpre : c ≤ cpre := min_le_left _ _
  refine ⟨δ,η₀,a,c,J,hδ,hη₀,hηcap,ha,hc,mul_pos hhi hJ₀,min_le_right _ _,?_⟩
  intro M F hM hF
  obtain ⟨Fext,hreg,hjets,hbound,htests,hnegative,hsharp,hcolors⟩ := hsource M F hM hF
  have hrescale := source_uniform_amplitude_normalization Fext hc₀ hJ₀ hlo hhi
    hreg hbound htests hnegative
  refine ⟨Fext,hreg,hjets,hsharp,?_⟩
  intro ι S y η hy hη hηmax color Cap
  obtain ⟨hcard,hmoment,hmodels⟩ := hcolors S y η hy hη hηmax
  refine ⟨hcard,hmoment,?_⟩
  intro j hj
  obtain ⟨i₀,hi₀,hcolor₀,hlinked⟩ := hmodels j hj
  refine ⟨i₀,hi₀,hcolor₀,?_⟩
  intro Fsrc
  have hy₀ := hy i₀ hi₀
  have hypos : 0 < y i₀ := zero_lt_one.trans_le hy₀.1
  have hσy : 0 < σ*y i₀ := mul_pos hσ hypos
  have hloamp : lo ≤ xi/(σ*y i₀) := by
    exact div_le_div_of_nonneg_left hxi.le hσy (by nlinarith only [hy₀.2,hσ])
  have hampHi : xi/(σ*y i₀) ≤ hi := by
    exact div_le_div_of_nonneg_left hxi.le hσ (by nlinarith only [hy₀.1,hσ])
  obtain ⟨hsrcReg,hsrcBound,hsrcTests,hsrcNegative,hphaseId⟩ :=
    hrescale.2.2 (xi/(σ*y i₀)) hloamp hampHi
  refine ⟨hsrcReg,hsrcBound,(fun w hw j => hccpre.trans (hsrcTests w hw j)),
    (fun w hw => (hsrcNegative w hw).trans (neg_le_neg hccpre)),?_⟩
  intro T N R hT hR hscale Tnew Rnew
  obtain ⟨hTnew,hRnew,hRsq,hlink,hmodels₀⟩ := hlinked xi T N R hxi hT hR hscale
  refine ⟨hTnew,hRnew,hRsq,hlink,?_⟩
  intro i hiS hcolori G f
  let Graw := fun u => (Fext u-Fext (u+η*y i))/(σ*η*y i₀)
  let fraw := fun w => T*(Fext (w/M)-Fext (w/M+η*y i))/(xi*η)
  have hGeq : G=Graw := by
    funext u
    dsimp only [G,Graw,Fsrc]
    field_simp
  have hTeq : Tnew*(xi/(σ*y i₀))=T := by
    dsimp only [Tnew]
    field_simp
  have hfeq : f=fraw := by
    funext w
    exact hphaseId T Tnew xi η (y i) M w hTeq
  obtain ⟨hG,hphysical,hrounded⟩ := hmodels₀ i hiS hcolori
  refine ⟨?_,?_,?_,?_⟩
  · rw [hGeq]
    exact hG
  · intro w
    exact congrFun hfeq w
  · rw [hGeq,hfeq]
    exact hphysical
  · rw [hGeq,hfeq]
    exact hrounded

example
    {σ ε xi : ℝ} (hσ : 0 < σ) (hε : 0 < ε) (hxi : 0 < xi)
    (P : ℕ) (hP : 5 ≤ P) :
    ∃ δ η₀ a c J : ℝ, 0 < δ ∧ 0 < η₀ ∧ η₀ ≤ 1/8 ∧ 0 < a ∧ 0 < c ∧ 0 < J ∧
      c ≤ 4*modelPhaseThirdLower (σ+1)*xi/((σ+1)*(σ+2)+3) ∧
      ∀ (M : ℝ) (F : ℝ → ℝ), 1 ≤ M →
      Expdb.IsApproximateModelPhaseFunction F σ (P+2) δ →
      ∃ Fext : ℝ → ℝ,
        (∀ w, 0 < w → ContDiffAt ℝ ∞ Fext w) ∧
        (∀ w∈Icc (1/2:ℝ) 3, ∀ p ≤ P+1,
          |iteratedDeriv (p+1) Fext w-iteratedDeriv p (Expdb.modelPhase σ) w| ≤ ε) ∧
        (∀ (T : ℝ) (m n : ℕ), M ≤ (m:ℝ) → (n:ℝ) ≤ 2*M →
          ‖Expdb.exponentialSumAt F T M m n-Expdb.exponentialSumAt Fext T M m n‖ ≤ 6) ∧
        ∀ {ι : Type*} (S : Finset ι) (y : ι → ℝ) (η : ℝ),
          (∀ i∈S, y i∈Icc (1:ℝ) 2) → 0 < η → η ≤ η₀ →
          let color := fun i => ⌊y i/a⌋
          let Cap := 4/a+3
          ((S.image color).card:ℝ) ≤ Cap ∧
          (∀ z : ι → ℂ, ‖∑ i∈S,z i‖^12 ≤
            Cap^11*∑ j∈S.image color, ‖∑ i∈S.filter (fun i => color i=j),z i‖^12) ∧
          ∀ j∈S.image color, ∃ i₀∈S, color i₀=j ∧
            let Fsrc := fun w => (xi/(σ*y i₀))*Fext w
            (∀ w, 0 < w → ContDiffAt ℝ ∞ Fsrc w) ∧
            (∀ w∈Icc (1/2:ℝ) 3, ∀ n ≤ 6, |iteratedDeriv (n+1) Fsrc w| ≤ J) ∧
            (∀ w∈Icc (1/2:ℝ) 3, ∀ j,
              c ≤ |HuxleyModel.tests (fun i : Fin 4 => iteratedDeriv (i.val+3) Fsrc w) j|) ∧
            (∀ w∈Icc (1/2:ℝ) 3, iteratedDeriv 4 Fsrc w ≤ -c) ∧
            ∀ T N R : ℝ, 0 < T → 0 < R → T*N*R^2=M^3 →
            let Tnew := T*σ*y i₀/xi
            let Rnew := R*Real.sqrt (xi/(σ*y i₀))
            0 < Tnew ∧ 0 < Rnew ∧ Rnew^2=R^2*xi/(σ*y i₀) ∧
              Tnew*N*Rnew^2=M^3 ∧
            ∀ i∈S, color i=j →
              let G := fun u => (Fsrc u-Fsrc (u+η*y i))/(xi*η)
              let f := fun w => Tnew*(Fsrc (w/M)-Fsrc (w/M+η*y i))/(xi*η)
              Expdb.IsApproximateModelPhaseFunction G (σ+1) P ε ∧
                (∀ w : ℝ, f w=T*(Fext (w/M)-Fext (w/M+η*y i))/(xi*η)) ∧
                (∀ A x : ℝ, heathBrownPhysicalPhase G Tnew M A 1 x=f (A+x)) ∧
                (∀ (A : ℤ) (w : ℝ) (k : ℕ),
                  iteratedDeriv k (heathBrownPhysicalPhase G Tnew M A 1) (round (w-A))=
                    iteratedDeriv k f (round w)) :=
  HuxleySourceAmplitudeNormalizationScratch.approximateModelPhase_enlarged_colored_common_scale_source (σ:=σ) (ε:=ε) (xi:=xi) hσ hε hxi P hP


#print axioms source_tests_const_mul
#print axioms source_tests_uniform_positive_rescaling
#print axioms source_uniform_amplitude_normalization
#print axioms approximateModelPhase_enlarged_colored_common_scale_source
end HuxleySourceAmplitudeNormalizationScratch
