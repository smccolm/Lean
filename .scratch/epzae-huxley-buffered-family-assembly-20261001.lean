import TaoTrudgianYang2025.HuxleyLinearForms
open Set TaoTrudgianYang2025 TaoTrudgianYang2025.HuxleyRationalPhase
open scoped BigOperators Classical ContDiff FourierTransform
namespace HuxleyBufferedFamilyAssemblyScratch
private theorem actual_source_index_transport
    (S : Finset ((ℝ × (ℝ × ℝ)) × ℤ))
    (hinj : Set.InjOn (fun i : (ℝ × (ℝ × ℝ)) × ℤ => (i.1.1,i.2)) (S : Set _)) :
    let tag := fun i : (ℝ × (ℝ × ℝ)) × ℤ => (i.1.1,i.2)
    let P := S.image tag
    ∃ pull : ℝ × ℤ → (ℝ × (ℝ × ℝ)) × ℤ,
      (∀ p ∈ P, pull p ∈ S ∧ tag (pull p) = p) ∧
      (∀ i ∈ S, pull (tag i) = i) ∧
      P.card = S.card ∧
      (∀ w : (ℝ × (ℝ × ℝ)) × ℤ → ℝ,
        (∑ p ∈ P,w (pull p)) = ∑ i ∈ S,w i) ∧
      ∀ w : ((ℝ × (ℝ × ℝ)) × ℤ) × Fin 2 → ℝ,
        (∑ ip ∈ P ×ˢ (Finset.univ : Finset (Fin 2)),w (pull ip.1,ip.2)) = 
          ∑ i ∈ S, ∑ p : Fin 2,w (i,p) := by
  classical
  intro tag P
  let pull := Function.invFunOn tag (S : Set _)
  have himage p (hp : p ∈ P) : p ∈ tag '' (S : Set _) := by
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hp
    exact ⟨i,hi,rfl⟩
  have hright p (hp : p ∈ P) : pull p ∈ S ∧ tag (pull p) = p :=
    ⟨Function.invFunOn_mem (himage p hp),Function.invFunOn_eq (himage p hp)⟩
  have hleft i (hi : i ∈ S) : pull (tag i) = i := by
    have hh := hright (tag i) (Finset.mem_image.mpr ⟨i,hi,rfl⟩)
    exact hinj hh.1 hi hh.2
  refine ⟨pull,hright,hleft,Finset.card_image_of_injOn hinj,?_,?_⟩
  · intro w
    rw [Finset.sum_image hinj]
    exact Finset.sum_congr rfl (fun i hi => congrArg w (hleft i hi))
  · intro w
    rw [Finset.sum_product,Finset.sum_image hinj]
    apply Finset.sum_congr rfl
    intro i hi
    change (∑ p : Fin 2,w (pull (tag i),p)) = ∑ p : Fin 2,w (i,p)
    rw [hleft i hi]

private theorem actual_source_dyadic_cubic_admissibility
    (F : ℝ → ℝ) {σ c J η y z T M R : ℝ} {N Q A K₀ : ℕ} {a r : ℚ}
    (hσ : 0 < σ) (hc : 0 < c) (hJ : 0 < J)
    (hη : 0 < η) (hηmax : η ≤ 1/8) (hy : y ∈ Icc (1:ℝ) 2)
    (hf : ∀ w, 0 < w → ContDiffAt ℝ ∞ F w)
    (hbound : ∀ w ∈ Icc (1/2:ℝ) 3, ∀ n ≤ 6, |iteratedDeriv (n+1) F w| ≤ J)
    (hnegative : ∀ w ∈ Icc (1/2:ℝ) 3, iteratedDeriv 4 F w ≤ -c)
    (hM : 2 ≤ M) (hN : 1 ≤ N) (hR : 0 < R) (hz : z ∈ Icc M (2*M))
    (hphase : T*(N:ℝ)*R^2 = M^3)
    (hQN : Q ≤ N) (hden : r.den ≤ Q) (hhalf : Q ≤ 2*r.den)
    (hcut : 2*a.den ≤ Q) (hmajor : 128*σ*R^2 ≤ c*(Q:ℝ)*a.den)
    (hAlow : N ≤ A) (hAhigh : A ≤ 3*N)
    (hmesh : 63*(J/(2*σ*(N:ℝ)*R^2))*(Q:ℝ)*(N:ℝ)^2 ≤ K₀) :
    let f := fun w => T*(F (w/M)-F (w/M+η*y))/(σ*η)
    let μ := iteratedDeriv 3 f (round z)/6
    1 ≤ A ∧ r.den ≤ A ∧ 1 ≤ μ*(r.den:ℝ)^2*A ∧
      7*(μ*(r.den:ℝ)*(A:ℝ)^2) ≤ K₀ := by
  intro f μ
  have hNp : (0:ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hμ := positive_difference_rounded_cubic_scales F hσ hc hJ hη hηmax hy
    hf hbound hnegative hM hNp hR hz hphase
  let lambda := c/(12*σ*(N:ℝ)*R^2)
  let U₃ := J/(2*σ*(N:ℝ)*R^2)
  have hμbounds : lambda ≤ μ ∧ μ ≤ U₃ := hμ
  have hlambda : 0 < lambda := by dsimp only [lambda]; positivity
  have hU₃ : 0 < U₃ := by dsimp only [U₃]; positivity
  have hcutR : 2*(a.den:ℝ) ≤ Q := by exact_mod_cast hcut
  have hqR : (Q:ℝ) ≤ 2*(r.den:ℝ) := by exact_mod_cast hhalf
  have haq : (a.den:ℝ) ≤ r.den := by linarith only [hcutR,hqR]
  have hprod : c*(Q:ℝ)*a.den ≤ 2*c*(r.den:ℝ)^2 := by
    calc
      _ ≤ c*(2*(r.den:ℝ))*(r.den:ℝ) := by gcongr
      _ = _ := by ring
  have hbudget : 12*σ*R^2 ≤ c*(r.den:ℝ)^2 := by
    have hpositive : 0 < σ*R^2 := by positivity
    nlinarith only [hmajor,hprod,hpositive]
  have hbase : 1 ≤ lambda*(r.den:ℝ)^2*N := by
    have heq : lambda*(r.den:ℝ)^2*N = c*(r.den:ℝ)^2/(12*σ*R^2) := by
      dsimp only [lambda]
      field_simp
    rw [heq]
    exact (one_le_div (by positivity : 0 < 12*σ*R^2)).mpr hbudget
  have hAlowR : (N:ℝ) ≤ A := by exact_mod_cast hAlow
  have hAhighR : (A:ℝ) ≤ 3*(N:ℝ) := by exact_mod_cast hAhigh
  have hdenR : (r.den:ℝ) ≤ Q := by exact_mod_cast hden
  have hμnonneg : 0 ≤ μ := hlambda.le.trans hμbounds.1
  refine ⟨hN.trans hAlow,hden.trans (hQN.trans hAlow),hbase.trans ?_,?_⟩
  · exact mul_le_mul (mul_le_mul_of_nonneg_right hμbounds.1 (sq_nonneg _))
      hAlowR hNp.le (mul_nonneg hμnonneg (sq_nonneg _))
  · calc
      7*(μ*(r.den:ℝ)*(A:ℝ)^2) ≤ 7*(U₃*(Q:ℝ)*(3*(N:ℝ))^2) := by
        gcongr
        exact hμbounds.2
      _ = 63*U₃*(Q:ℝ)*(N:ℝ)^2 := by ring
      _ ≤ K₀ := hmesh

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

private theorem actual_source_grid_completion_error
    (S : Finset (ℝ × ℤ)) (Y : Finset ℝ) (F : ℝ → ℝ)
    (z : ℝ × ℤ → ℝ) (A : ℝ × ℤ → ℕ)
    {σ c J η T M R s : ℝ} {N : ℕ}
    (hσ : 0 < σ) (hc : 0 < c) (hJ : 0 < J)
    (hη : 0 < η) (hηmax : η ≤ 1/8)
    (hN : 1 ≤ N) (hM : 2 ≤ M) (hR : 0 < R)
    (hphase : T*(N:ℝ)*R^2 = M^3)
    (hy : ∀ y ∈ Y, y ∈ Icc (1:ℝ) 2)
    (hlabels : ∀ i ∈ S, i.1 ∈ Y)
    (hgrid : ∀ i ∈ S, M ≤ s+(N:ℝ)*i.2 ∧ s+(N:ℝ)*i.2 ≤ 2*M)
    (hz : ∀ i ∈ S, z i ∈ Icc M (2*M))
    (hA : ∀ i ∈ S, N ≤ A i ∧ A i ≤ 3*N)
    (hf : ∀ w, 0 < w → ContDiffAt ℝ ∞ F w)
    (hbound : ∀ w ∈ Icc (1/2:ℝ) 3, ∀ n ≤ 6, |iteratedDeriv (n+1) F w| ≤ J)
    (hnegative : ∀ w ∈ Icc (1/2:ℝ) 3, iteratedDeriv 4 F w ≤ -c) :
    let f := fun i w => T*(F (w/M)-F (w/M+η*i.1))/(σ*η)
    let μ := fun i => iteratedDeriv 3 (f i) (round (z i))/6
    (S.card:ℝ) ≤ (Y.card:ℝ)*(M/(N:ℝ)+1) ∧
    (∑ i ∈ S, (Real.sqrt (A i)*Real.log (2*(A i:ℝ))+1/(μ i*(A i:ℝ)^2))) ≤ 
      (Y.card:ℝ)*(M/(N:ℝ)+1)*
        (Real.sqrt (3*(N:ℝ))*Real.log (6*(N:ℝ))+12*σ*R^2/(c*(N:ℝ))) := by
  classical
  intro f μ
  have hNp : (0:ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hNreal : (1:ℝ) ≤ N := by exact_mod_cast hN
  obtain ⟨I,hI,_hIlow,hIhigh⟩ := physical_grid_interval_card (N:=(N:ℝ)) (Z:=s)
    (x:=M) (z:=2*M) hNp (by linarith only [hM])
  have hsub : S⊆Y ×ˢ I := by
    intro i hi
    refine Finset.mem_product.mpr ⟨hlabels i hi,(hI i.2).mpr ?_⟩
    simpa only [mul_comm (i.2:ℝ) (N:ℝ)] using hgrid i hi
  have hcardRaw : (S.card:ℝ) ≤ (Y.card:ℝ)*(I.card:ℝ) := by
    exact_mod_cast (Finset.card_le_card hsub).trans_eq (Finset.card_product Y I)
  have hcard : (S.card:ℝ) ≤ (Y.card:ℝ)*(M/(N:ℝ)+1) := by
    have hIbound : (I.card:ℝ) ≤ M/(N:ℝ)+1 := by
      convert hIhigh using 1
      ring
    exact hcardRaw.trans (mul_le_mul_of_nonneg_left hIbound (Nat.cast_nonneg _))
  refine ⟨hcard,?_⟩
  let ErrorBound := Real.sqrt (3*(N:ℝ))*Real.log (6*(N:ℝ))+12*σ*R^2/(c*(N:ℝ))
  have hError : 0 ≤ ErrorBound := add_nonneg
    (mul_nonneg (Real.sqrt_nonneg _) (Real.log_nonneg (by linarith only [hNreal])))
    (by positivity)
  have hpoint i (hi : i ∈ S) :
      Real.sqrt (A i)*Real.log (2*(A i:ℝ))+1/(μ i*(A i:ℝ)^2) ≤ ErrorBound := by
    have hcubic := positive_difference_rounded_cubic_scales F hσ hc hJ hη hηmax
      (hy i.1 (hlabels i hi)) hf hbound hnegative hM hNp hR (hz i hi) hphase
    exact cubic_completion_point_error hσ hc hNreal hR
      (by exact_mod_cast (hA i hi).1) (by exact_mod_cast (hA i hi).2) hcubic.1
  calc
    _ ≤ ∑ _i ∈ S,ErrorBound := Finset.sum_le_sum hpoint
    _ = (S.card:ℝ)*ErrorBound := by rw [Finset.sum_const,nsmul_eq_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_right hcard hError

private theorem actual_source_family_card_bound_mono
    {σsrc csrc Usrc σ εloss θ a Cupper Clower Dupper Dlower C Dtype
      T M R Jsep δ Bselect : ℝ} (Q K₀ N Uref : ℕ)
    (hσsrc : 0 < σsrc) (hcsrc : 0 < csrc) (hUsrc : 0 < Usrc) (hσ : 0 < σ)
    (hθ : 0 < θ) (ha : 0 < a) (hCU : 0 < Cupper) (hCL : 0 < Clower)
    (hDU : 0 < Dupper) (hDL : 0 < Dlower) (hC : 0 < C) (hDtype : 0 < Dtype)
    (hT : 0 < T) (hM : 0 < M) (hNp : (0:ℝ) < N)
    (hJsep : 0 < Jsep) (hδzero : 0 ≤ δ) (hBselect : 0 < Bselect) :
    let κ := modelPhaseThirdLower σ
    let Cphys := σ*(σ+1)+1
    let c := κ/6
    let J := Cphys/6
    let B := max 1 (max (2*Real.sqrt J) (8*J*Real.sqrt J/(3*c)))
    let Vscale := (Uref:ℝ)^((3:ℝ)/2)
    let lambda := csrc*κ*T/(12*Usrc*M^2)
    let Uband := (3*Usrc/σsrc)*T/(2*M^2)
    let ChartCap := (4/a+3)*((6*Usrc/σsrc)/a+3)*((4*σsrc/csrc)/a+3)
    let NarrowCap := (4/θ+3)*(72*Usrc^2/(σsrc*csrc*κ*θ)+3)
    let Cap := 3*ChartCap*NarrowCap
    let μ₀ := csrc*T/(12*σsrc*M^3)
    let U₀ := Usrc*T/(2*σsrc*M^3)
    let Δtype := (16*U₀/μ₀)*Real.sqrt (U₀*(Q:ℝ)^3)*Real.sqrt K₀/(6*(K₀:ℝ)^2)
    let C₂ := modelPhaseJetCoefficient σ 2+δ
    let C₃ := modelPhaseJetCoefficient σ 3+δ
    let Ct := C₂/2+5*C₃/12
    let Cc := C₂/κ+C₃/(2*κ)
    let Kres := 4*(37*B/2+16*B*Cc+2*Ct+2*Cc+
      2*quarticNonlinearResidualConstant σ δ)/κ
    let Lunit := 2*κ/Cphys
    let Gamma := Cphys/κ
    let Cthird := Gamma*(32*Kres+9*quarticReciprocalConstant σ δ)
    let AupperConst := 2*Cupper*(Cthird+1)*1^2/(κ*Lunit^3)
    let BupperConst := Cupper*(Cthird+1)*1^2/Lunit^2+Dupper*(B+1)*1^2/4
    let AlowerConst := 8*Clower*(Cthird+1)/(κ*Lunit^3)
    let BlowerConst := 4*Clower*(Cthird+1)/Lunit^2+Dlower*(B+1)
    let DupperConst := θ*(3*Usrc/σsrc)*1/2
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
    let BoundCard := fun y : ℝ =>
      (144*Usrc/(csrc*κ))^6*(R^2/(Q:ℝ))^6*
        C*(K₀:ℝ)^((12:ℝ)+εloss)*Cap^11*(10*y*(M/(N:ℝ)))^10*
          (Vscale*Dtype*y*(M/(N:ℝ))*(1+Δtype*Jsep)+
            y^2*(Vscale*(Kupper+Klower)+Klarge)*T^εloss)
    ∀ {y₁ y₂ : ℝ}, 0 ≤ y₁ → y₁ ≤ y₂ → BoundCard y₁ ≤ BoundCard y₂ := by
  intro κ Cphys c J B Vscale lambda Uband ChartCap NarrowCap Cap μ₀ U₀ Δtype
    C₂ C₃ Ct Cc Kres Lunit Gamma Cthird AupperConst BupperConst AlowerConst BlowerConst
    DupperConst DlowerConst CostUpper CostLower Cpack Cfirst Cgap Cmain Ctail
    Kupper Klower Klarge BoundCard y₁ y₂ hy₁ hy₂
  have hκ : 0 < κ := modelPhaseThirdLower_pos hσ
  have hCphys : 0 < Cphys := by dsimp only [Cphys]; positivity
  have hVscale : 0 ≤ Vscale := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hjet2 : 0 ≤ modelPhaseJetCoefficient σ 2 := modelPhaseJetCoefficient_nonneg σ 2
  have hjet3 : 0 ≤ modelPhaseJetCoefficient σ 3 := modelPhaseJetCoefficient_nonneg σ 3
  have hjet4 : 0 ≤ modelPhaseJetCoefficient σ 4 := modelPhaseJetCoefficient_nonneg σ 4
  have hC₂ : 0 ≤ C₂ := add_nonneg hjet2 hδzero
  have hC₃ : 0 ≤ C₃ := add_nonneg hjet3 hδzero
  have hB : 0 < B := zero_lt_one.trans_le (le_max_left _ _)
  have hResidual : 0 ≤ quarticNonlinearResidualConstant σ δ := by
    clear * - hσ hδzero hκ hjet2 hjet3 hjet4
    dsimp only [quarticNonlinearResidualConstant]
    positivity
  have hReciprocal : 0 ≤ quarticReciprocalConstant σ δ := by
    clear * - hσ hδzero hκ hjet2 hjet3 hjet4
    dsimp only [quarticReciprocalConstant]
    positivity
  have hCt : 0 ≤ Ct := add_nonneg (div_nonneg hC₂ (by norm_num))
    (div_nonneg (mul_nonneg (by norm_num) hC₃) (by norm_num))
  have hCc : 0 ≤ Cc := add_nonneg (div_nonneg hC₂ hκ.le)
    (div_nonneg hC₃ (mul_nonneg zero_le_two hκ.le))
  have hKres : 0 ≤ Kres := div_nonneg (mul_nonneg (by norm_num)
    (add_nonneg (add_nonneg (add_nonneg
      (add_nonneg (div_nonneg (mul_nonneg (by norm_num) hB.le) (by norm_num))
        (mul_nonneg (mul_nonneg (by norm_num) hB.le) hCc))
      (mul_nonneg zero_le_two hCt)) (mul_nonneg zero_le_two hCc))
      (mul_nonneg zero_le_two hResidual))) hκ.le
  have hGamma : 0 ≤ Gamma := div_nonneg hCphys.le hκ.le
  have hCthird : 0 ≤ Cthird := mul_nonneg hGamma
    (add_nonneg (mul_nonneg (by norm_num) hKres) (mul_nonneg (by norm_num) hReciprocal))
  have hLunit : 0 < Lunit := div_pos (mul_pos zero_lt_two hκ) hCphys
  have hAu : 0 ≤ AupperConst := div_nonneg
    (mul_nonneg (mul_nonneg (mul_nonneg zero_le_two hCU.le)
      (add_nonneg hCthird zero_le_one)) (by norm_num))
    (mul_nonneg hκ.le (pow_nonneg hLunit.le 3))
  have hBu : 0 ≤ BupperConst := add_nonneg
    (div_nonneg (mul_nonneg (mul_nonneg hCU.le (add_nonneg hCthird zero_le_one))
      (by norm_num)) (sq_nonneg _))
    (div_nonneg (mul_nonneg (mul_nonneg hDU.le (add_nonneg hB.le zero_le_one))
      (by norm_num)) (by norm_num))
  have hAl : 0 ≤ AlowerConst := div_nonneg
    (mul_nonneg (mul_nonneg (by norm_num) hCL.le) (add_nonneg hCthird zero_le_one))
    (mul_nonneg hκ.le (pow_nonneg hLunit.le 3))
  have hBl : 0 ≤ BlowerConst := add_nonneg
    (div_nonneg (mul_nonneg (mul_nonneg (by norm_num) hCL.le)
      (add_nonneg hCthird zero_le_one)) (sq_nonneg _))
    (mul_nonneg hDL.le (add_nonneg hB.le zero_le_one))
  have hDu : 0 ≤ DupperConst := div_nonneg
    (mul_nonneg (mul_nonneg hθ.le (div_nonneg (mul_nonneg (by norm_num) hUsrc.le)
      hσsrc.le)) zero_le_one) zero_le_two
  have hDl : 0 ≤ DlowerConst := div_nonneg
    (mul_nonneg (mul_nonneg (by norm_num) hUsrc.le) hθ.le)
    (mul_nonneg hcsrc.le hκ.le)
  have hCostU : 0 ≤ CostUpper := div_nonneg (sq_nonneg _)
    (mul_nonneg (pow_nonneg (Nat.cast_nonneg _) 4) (Nat.cast_nonneg _))
  have hCostL : 0 ≤ CostLower := div_nonneg
    ((show Even 4 by decide).pow_nonneg R)
    (mul_nonneg (sq_nonneg _) (Nat.cast_nonneg _))
  have hKu : 0 ≤ Kupper := mul_nonneg (mul_nonneg (by norm_num) hCostU)
    (add_nonneg (add_nonneg (mul_nonneg (by norm_num)
      (Real.rpow_nonneg (mul_nonneg hAu (sq_nonneg _)) _))
      (mul_nonneg zero_le_two hBu)) (mul_nonneg (by norm_num) hDu))
  have hKl : 0 ≤ Klower := mul_nonneg (mul_nonneg (by norm_num) hCostL)
    (add_nonneg (add_nonneg (mul_nonneg (by norm_num)
      (Real.rpow_nonneg (mul_nonneg hAl (sq_nonneg _)) _))
      (mul_nonneg zero_le_two hBl)) (mul_nonneg (by norm_num) hDl))
  have hthirdTerm : 0 ≤ Gamma^2*Cthird+Gamma*(modelPhaseJetCoefficient σ 3+δ)/κ :=
    add_nonneg (mul_nonneg (sq_nonneg _) hCthird) (div_nonneg (mul_nonneg hGamma hC₃) hκ.le)
  have hgapTerm : 0 ≤ Gamma^2*B+Gamma*(modelPhaseJetCoefficient σ 3+δ)/κ :=
    add_nonneg (mul_nonneg (sq_nonneg _) hB.le) (div_nonneg (mul_nonneg hGamma hC₃) hκ.le)
  have hCpack : 0 ≤ Cpack := div_nonneg
    (mul_nonneg (mul_nonneg (by norm_num) hCphys.le) hthirdTerm) hκ.le
  have hCfirst : 0 ≤ Cfirst := div_nonneg
    (mul_nonneg (mul_nonneg (by norm_num) hCphys.le) hthirdTerm) (sq_nonneg _)
  have hCgap : 0 ≤ Cgap := div_nonneg
    (mul_nonneg (mul_nonneg (by norm_num) hCphys.le) hgapTerm) hκ.le
  have hCmain : 0 ≤ Cmain := add_nonneg
    (mul_nonneg (by norm_num) (Real.rpow_nonneg
      (div_nonneg (mul_nonneg zero_le_two hCfirst) (pow_nonneg hLunit.le 3)) _)) zero_le_two
  have hCtail : 0 ≤ Ctail := add_nonneg
    (div_nonneg (mul_nonneg (by norm_num) hCpack) (sq_nonneg _)) hCgap
  have hKlrg : 0 ≤ Klarge := mul_nonneg
    (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg
      (mul_nonneg (mul_nonneg (mul_nonneg zero_le_two hBselect.le) (by norm_num)) (by norm_num))
      (sq_nonneg _)) (sq_nonneg _))
      (div_nonneg ((show Even 8 by decide).pow_nonneg R) (pow_nonneg (Nat.cast_nonneg _) 4)))
      (add_nonneg hCmain hCtail))
    (Real.rpow_nonneg (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) _)
  have hΔtype : 0 ≤ Δtype := by
    clear * - hσsrc hcsrc hUsrc hT hM
    dsimp only [Δtype,μ₀,U₀]
    positivity
  have hChartCap : 0 < ChartCap := by
    clear * - ha hUsrc hσsrc hcsrc
    dsimp only [ChartCap]
    positivity
  have hNarrowCap : 0 < NarrowCap := by
    clear * - hθ hUsrc hσsrc hcsrc hκ
    dsimp only [NarrowCap]
    positivity
  have hCap : 0 ≤ Cap := mul_nonneg
    (mul_nonneg (by norm_num) hChartCap.le) hNarrowCap.le
  let Scale := (144*Usrc/(csrc*κ))^6*(R^2/(Q:ℝ))^6*
    C*(K₀:ℝ)^((12:ℝ)+εloss)*Cap^11
  have hScale : 0 ≤ Scale := mul_nonneg
    (mul_nonneg (mul_nonneg (mul_nonneg
      ((show Even 6 by decide).pow_nonneg _) ((show Even 6 by decide).pow_nonneg _)) hC.le)
      (Real.rpow_nonneg (Nat.cast_nonneg _) _)) (pow_nonneg hCap 11)
  have hratio : 0 ≤ M/(N:ℝ) := div_nonneg hM.le hNp.le
  have hDeltaFactor : 0 ≤ 1+Δtype*Jsep :=
    add_nonneg zero_le_one (mul_nonneg hΔtype hJsep.le)
  have hQuad : 0 ≤ Vscale*(Kupper+Klower)+Klarge :=
    add_nonneg (mul_nonneg hVscale (add_nonneg hKu hKl)) hKlrg
  let Mass := fun y : ℝ => Vscale*Dtype*y*(M/(N:ℝ))*(1+Δtype*Jsep)+
    y^2*(Vscale*(Kupper+Klower)+Klarge)*T^εloss
  have hMass : 0 ≤ Mass y₁ := add_nonneg
    (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hVscale hDtype.le) hy₁) hratio) hDeltaFactor)
    (mul_nonneg (mul_nonneg (sq_nonneg _) hQuad) (Real.rpow_nonneg hT.le _))
  have hMassLe : Mass y₁ ≤ Mass y₂ := add_le_add
    (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hy₂ (mul_nonneg hVscale hDtype.le)) hratio) hDeltaFactor)
    (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hy₁ hy₂ 2) hQuad) (Real.rpow_nonneg hT.le _))
  have hFactor : 0 ≤ 10*y₁*(M/(N:ℝ)) := mul_nonneg (mul_nonneg (by norm_num) hy₁) hratio
  have hFactorLe : 10*y₁*(M/(N:ℝ)) ≤ 10*y₂*(M/(N:ℝ)) :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hy₂ (by norm_num)) hratio
  exact mul_le_mul
    (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hFactor hFactorLe 10) hScale)
    hMassLe hMass (mul_nonneg hScale (pow_nonneg (hFactor.trans hFactorLe) 10))

/-- Direct source-family twelfth-power estimate: the reference charts,
interior windows, common mode, and weighted source data are constructed. -/
theorem eventually_positive_difference_buffered_source_physical_sieve
    {σsrc csrc Usrc σ εloss : ℝ}
    (hσsrc : 0 < σsrc) (hcsrc : 0 < csrc) (hUsrc : 0 < Usrc)
    (hσ : 0 < σ) (hεloss : 0 < εloss)
    (hanchorBudget : csrc ≤ 4*modelPhaseThirdLower σ*σsrc/(σ*(σ+1)+3)) :
    let κ := modelPhaseThirdLower σ
    let Ratio := 18*Usrc^2/(σsrc*csrc*κ)
    let L := max (8*Ratio^2)
      (32*(modelPhaseJetCoefficient σ 3+1)*(3*Usrc/σsrc)/κ^2)
    ∃ Csrc η₀ a Cupper Clower Dupper Dlower C Dtype : ℝ,
      1 ≤ Csrc ∧ 0 < η₀ ∧ η₀ ≤ 1/8 ∧ 0 < a ∧
      0 < Cupper ∧ 0 < Clower ∧ 0 < Dupper ∧ 0 < Dlower ∧ 0 < C ∧ 0 < Dtype ∧
    ∀ {θ : ℝ}, 0 < θ → θ ≤ 1/24 → θ ≤ 1/(8*(L+3)) →
    ∀ᶠ T : ℝ in Filter.atTop, ∀ (Fsrc : ℝ → ℝ) (Y : Finset ℝ)
      (Hlen : ℝ → ℤ → ℕ) (I : Finset ℤ) (Q K₀ N Uref : ℕ) [NeZero K₀]
      (sgrid : ℤ) (R Jsep : ℝ) {η M δ Bcut Bselect : ℝ},
    0 < η → η ≤ η₀ → 0 < T → 2 ≤ N →
    1 ≤ R → R ≤ M → 0 ≤ δ → δ ≤ min κ 1 →
    0 < Jsep → Jsep ≤ M →
    (∀ y ∈ Y, y ∈ Icc (1:ℝ) 2) →
    (∀ y ∈ Y, ∀ z ∈ Y, y ≠ z → 1 ≤ Jsep*|y-z|) →
    (∀ y ∈ Y, ∀ k, Hlen y k ≤ N) →
    (∀ k ∈ I, (sgrid:ℝ)+(N:ℝ)*k ∈ Icc M (2*M)) →
    (∀ w, 0 < w → ContDiffAt ℝ ∞ Fsrc w) →
    (∀ w ∈ Icc (1/2:ℝ) 3, ∀ n ≤ 6, |iteratedDeriv (n+1) Fsrc w| ≤ Usrc) →
    (∀ w ∈ Icc (1/2:ℝ) 3, ∀ j,
      csrc ≤ |HuxleyModel.tests (fun i : Fin 4 => iteratedDeriv (i.val+3) Fsrc w) j|) →
    (∀ w ∈ Icc (1/2:ℝ) 3, iteratedDeriv 4 Fsrc w ≤ -csrc) →
    (∀ y ∈ Y, Expdb.IsApproximateModelPhaseFunction
      (fun u => (Fsrc u-Fsrc (u+η*y))/(σsrc*η)) σ 4 δ) →
    T*(N:ℝ)*R^2 = M^3 →
    7*(N:ℝ)+2 ≤ M/4 →
    (3*Usrc/σsrc)*(6*(N:ℝ)+1)^4 ≤ M*(N:ℝ)*R^2 →
    (3*Usrc/(4*σsrc))*(6*(N:ℝ)+1)^2 ≤ (N:ℝ)*R^2 →
    3*Usrc ≤ σsrc*(Uref:ℝ) →
    63*(Usrc/(2*σsrc*(N:ℝ)*R^2))*(Q:ℝ)*(N:ℝ)^2 ≤ K₀ →
    (Q:ℝ)*(N:ℝ) ≤ (K₀:ℝ)*R^2 →
    (N:ℝ)^4 ≤ M*R^3*(Real.log T)^((3:ℝ)/2) →
    1 ≤ Uref → 0 < Bcut →
    2+168/κ ≤ Bselect → 7*Bcut ≤ κ*Bselect →
    Bselect^2*(Uref:ℝ)^3*R^2 ≤ (N:ℝ)^2 →
    (Uref:ℝ) ≤ ((N:ℝ)/(Q:ℝ))^((2:ℝ)/3)/Bselect →
    ((N:ℝ)/(Q:ℝ))^((2:ℝ)/3)/(2*Bselect) ≤ (Uref:ℝ) →
    (N:ℝ)^10 ≤ M^3*R^7 →
    Q ≤ N → (N:ℝ)^2 ≤ M → (Uref:ℝ) ≤ R^2 →
    768*R ≤ (Q:ℝ) → (N:ℝ)*R ≤ M →
    let Cphys := σ*(σ+1)+1
    let c := κ/6
    let J := Cphys/6
    let B := max 1 (max (2*Real.sqrt J) (8*J*Real.sqrt J/(3*c)))
    B*R^2/(N:ℝ)^2 ≤ 1/2 →
    (N:ℝ) ≤ R^2 → R ≤ (N:ℝ) → (N:ℝ)^3 ≤ M*R^2 →
    2*R^2 ≤ (Q:ℝ)*(N:ℝ) →
    let Vscale := (Uref:ℝ)^((3:ℝ)/2)
    let lambda := csrc*κ*T/(12*Usrc*M^2)
    let Uband := (3*Usrc/σsrc)*T/(2*M^2)
    let ChartCap := (4/a+3)*((6*Usrc/σsrc)/a+3)*((4*σsrc/csrc)/a+3)
    let NarrowCap := (4/θ+3)*(72*Usrc^2/(σsrc*csrc*κ*θ)+3)
    let Cap := 3*ChartCap*NarrowCap
    let μ₀ := csrc*T/(12*σsrc*M^3)
    let U₀ := Usrc*T/(2*σsrc*M^3)
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
    let AupperConst := 2*Cupper*(Cthird+1)*1^2/(κ*Lunit^3)
    let BupperConst := Cupper*(Cthird+1)*1^2/Lunit^2+Dupper*(B+1)*1^2/4
    let AlowerConst := 8*Clower*(Cthird+1)/(κ*Lunit^3)
    let BlowerConst := 4*Clower*(Cthird+1)/Lunit^2+Dlower*(B+1)
    let DupperConst := θ*(3*Usrc/σsrc)*1/2
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

    let Buffer := (56*(Uref:ℝ)/κ)*(N:ℝ)+(N:ℝ)/(Cphys+2)+2
    let Dlog := 64*σsrc*R^2/(csrc*((Q:ℝ)/768))
    let Cerror := (768:ℝ)*((6*Usrc/σsrc)*(64*σsrc/csrc)^2+192*σsrc/csrc)+
      ((3*Usrc/σsrc+csrc/(32*σsrc))*((24576*σsrc)/csrc)^2+(24576*σsrc)/csrc)
    let Major := (Y.card:ℝ)*Cerror*(M*R/(Q:ℝ))*(2+Real.log (Dlog+1))
    let Error := (Y.card:ℝ)*(M/(N:ℝ)+1)*
      (Real.sqrt (3*(N:ℝ))*Real.log (6*(N:ℝ))+12*σsrc*R^2/(csrc*(N:ℝ)))
    let Boundary := (Y.card:ℝ)*((24*Usrc/σsrc)*M/(Uref:ℝ)+
      (56*σsrc/csrc)*(N:ℝ)*(Uref:ℝ)+6*(N:ℝ)+2*Buffer)
    let FamilyBound := (144*Usrc/(csrc*κ))^6*(R^2/(Q:ℝ))^6*
      C*(K₀:ℝ)^((12:ℝ)+εloss)*Cap^11*(10*(Y.card:ℝ)*(M/(N:ℝ)))^10*
        (Vscale*Dtype*(Y.card:ℝ)*(M/(N:ℝ))*(1+Δtype*Jsep)+
          (Y.card:ℝ)^2*(Vscale*(Kupper+Klower)+Klarge)*T^εloss)
    let f := fun y w => T*(Fsrc (w/M)-Fsrc (w/M+η*y))/(σsrc*η)
    let Lgrid := fun k : ℤ => sgrid+(N:ℤ)*k+2*(N:ℤ)
    (∑ p ∈ Y ×ˢ I, ‖∑ n ∈ Finset.Ioc (Lgrid p.2) (Lgrid p.2+Hlen p.1 p.2),
      (𝐞 (f p.1 n):ℂ)‖)^12 ≤ 
      2^11*((Csrc*(Major+Error)+Boundary)^12+
        (Csrc*(1+Real.log K₀))^12*FamilyBound)
 := by
  classical
  intro κ Ratio L
  obtain ⟨Csrc,hCsrc,hsource⟩ :=
    positive_difference_constructed_reference_family_buffered_source_fourier hσsrc hcsrc hUsrc
  obtain ⟨η₀,a,Cupper,Clower,Dupper,Dlower,C,Dtype,
      hη₀,hηcap,ha,hCU,hCL,hDU,hDL,hC,hDtype,hphysical⟩ :=
    eventually_positive_difference_actual_family_physical_sieve
      hσsrc hcsrc hUsrc (by norm_num : (0:ℝ) < 1) hσ hεloss
  refine ⟨Csrc,η₀,a,Cupper,Clower,Dupper,Dlower,C,Dtype,
    hCsrc,hη₀,hηcap,ha,hCU,hCL,hDU,hDL,hC,hDtype,?_⟩
  intro θ hθ hθmax hθaction
  let Jref := σ*Usrc/σsrc
  have hJref : 0 ≤ Jref := by dsimp only [Jref]; positivity
  have hθaction' :
      θ ≤ 1/(8*((max (8*(18*Usrc^2*1/(σsrc*csrc*κ))^2)
        (32*(modelPhaseJetCoefficient σ 3+1)*(3*Usrc/σsrc)*1/κ^2))+3)) := by
    simpa only [mul_one] using hθaction
  filter_upwards [hphysical hJref hθ hθmax hθaction'] with T hfamily
  intro Fsrc Y Hlen I Q K₀ N Uref instK sgrid R Jsep η M δ Bcut Bselect
    hη hηsmall hT hNtwo hR hRM hδzero hδ hJsep hJM hy hsepY hHlen hI
    hreg hjets htests hnegative hmodels hscale hpad hquartic hquad hUlarge
    hsourceMesh hmesh hregime hUref hBcut hBselectSize hcutMargin hselectedWrap
    hselectedUpper hUlo hscaleTen hQN hNsqM hUR hstrongRQ hNRM
    Cphys c J B hsmall hNR hRN hNcube hminscale
    Vscale lambda Uband ChartCap NarrowCap Cap μ₀ U₀ Δtype
    C₂ C₃ Ct Cc Δ Ccurv D Kres Esize Dbase Tbase hsize hD hΔ hBsize
    Lunit Gamma Cthird AupperConst BupperConst AlowerConst BlowerConst
    DupperConst DlowerConst CostUpper CostLower Cpack Cfirst Cgap Cmain Ctail
    Kupper Klower Klarge Buffer Dlog Cerror Major Error Boundary FamilyBound f Lgrid
  have hκ : 0 < κ := modelPhaseThirdLower_pos hσ
  have hN : 0 < N := by omega
  have hNreal : (2:ℝ) ≤ N := by exact_mod_cast hNtwo
  have hNp : (0:ℝ) < N := Nat.cast_pos.mpr hN
  have hMtwo : 2 ≤ M := by nlinarith only [hNreal,hNsqM]
  have hM : 0 < M := by linarith only [hMtwo]
  have hNM : (N:ℝ) ≤ M := by nlinarith only [hNreal,hNsqM]
  have hRp : 0 < R := zero_lt_one.trans_le hR
  have hUp : (0:ℝ) < Uref := by exact_mod_cast (show 0 < Uref by omega)
  have hQbig : 768 ≤ Q := by
    have hh : (768:ℝ) ≤ Q := by linarith only [hR,hstrongRQ]
    exact_mod_cast hh
  have hQ : 0 < Q := by omega
  have hQtwo : 2 ≤ Q := by omega
  have hRQ : R ≤ (Q:ℝ) := by nlinarith only [hR,hstrongRQ]
  have hCphys : 0 < Cphys := by dsimp only [Cphys]; positivity
  have hBuffer : 0 ≤ Buffer := by dsimp only [Buffer]; positivity
  have hVscale : 1 ≤ Vscale :=
    Real.one_le_rpow (by exact_mod_cast hUref) (by norm_num)
  have hsourceData := hsource Fsrc Y N sgrid Hlen η T M R (Uref:ℝ)
    (by omega) hHlen hη (hηsmall.trans hηcap) hy hT hM hRp hUp hUR
    hreg hjets htests hnegative hscale hpad hquartic hquad hUlarge
  obtain ⟨Href,hHref,hHrefHeight,Refs,hseed,hhull,henclose,hpoints,hheights,
    hcurv,hlabels,hRefSep,hcover,hroots,hgaps,hcharts,hrest⟩ := hsourceData
  let h := fun y w => iteratedDeriv 2 (f y) w/2
  let Vref := (Y ×ˢ (Refs ×ˢ Refs)).filter (fun i =>
    i.2.1 < i.2.2 ∧ (∀ t ∈ Refs,¬(i.2.1 < t ∧ t < i.2.2)) ∧
      i.2.1 < h i.1 (2*M) ∧ h i.1 M < i.2.2)
  let Gref := Vref.filter (fun i => h i.1 M ≤ i.2.1 ∧ i.2.2 ≤ h i.1 (2*M))
  obtain ⟨hpack,hboundary,hphaseCount,x₁,x₂,hgeometry,hdisjoint,hgrid⟩ := hrest
  letI : DecidableEq (ℝ × (ℝ × ℝ)) := Classical.decEq _
  let Gcore := Gref.filter (fun i => M+Buffer ≤ x₁ i ∧ x₂ i ≤ 2*M-Buffer)
  obtain ⟨S0,anchor0,za0,hS0,hforQ⟩ := hgrid Buffer hBuffer
  let Sall := Gcore.biUnion (fun i => (S0 i).image (fun k => (i,k)))
  let Good := fun i : (ℝ × (ℝ × ℝ)) × ℤ =>
    768*(anchor0 i.1 i.2).den ≤ Q ∧
      (24576*σsrc)*R^2 ≤ csrc*(Q:ℝ)*(anchor0 i.1 i.2).den
  let Gtag := Sall.filter Good
  obtain ⟨hinj,ratz,z0,hrat,hzin,hbuffer,hlocal,hdense,hround,hmodes⟩ :=
    hforQ Q hQtwo hQN 768 (24576*σsrc) (by norm_num) hQbig
      (by linarith only [hσsrc])
  let Nlen0 := fun i => (Lgrid i.2-round (z0 i)).toNat
  obtain ⟨v0,hv0,k0,hraw,hnorm,hwhole⟩ := hmodes K₀ hsourceMesh
  have hmem i (hi : i ∈ Gtag) : i.1 ∈ Gcore ∧ i.2 ∈ S0 i.1 := by
    have hall : i ∈ Sall := (Finset.mem_filter.mp hi).1
    obtain ⟨j,hj,hiimage⟩ := Finset.mem_biUnion.mp hall
    obtain ⟨k,hk,he⟩ := Finset.mem_image.mp hiimage
    cases he
    exact ⟨hj,hk⟩
  have hfull i (hi : i ∈ Gtag) : i.1 ∈ Gref := (Finset.mem_filter.mp (hmem i hi).1).1
  have hdata i (hi : i ∈ Gtag) :
      i.1.1 ∈ Y ∧ i.1.2.1 ∈ Refs ∧ i.1.2.2 ∈ Refs ∧ i.1.2.1 < i.1.2.2 ∧
        ∀ t ∈ Refs,¬(i.1.2.1 < t ∧ t < i.1.2.2) := by
    have hv := Finset.mem_filter.mp (Finset.mem_filter.mp (hfull i hi)).1
    have hp := Finset.mem_product.mp hv.1
    exact ⟨hp.1,(Finset.mem_product.mp hp.2).1,
      (Finset.mem_product.mp hp.2).2,hv.2.1,hv.2.2.1⟩
  let tag := fun i : (ℝ × (ℝ × ℝ)) × ℤ => (i.1.1,i.2)
  let P := Gtag.image tag
  have hinjG : Set.InjOn tag (Gtag : Set _) :=
    hinj.mono (by intro i hi; exact (Finset.mem_filter.mp hi).1)
  obtain ⟨pull,hright,hleft,hcardP,hsumP,hsumParity⟩ :=
    actual_source_index_transport Gtag hinjG
  have hphase p (hp : p ∈ P) : (pull p).1.1 = p.1 :=
    congrArg (fun q : ℝ × ℤ => q.1) (hright p hp).2
  have hblock p (hp : p ∈ P) : (pull p).2 = p.2 :=
    congrArg (fun q : ℝ × ℤ => q.2) (hright p hp).2
  have hlabelsP p (hp : p ∈ P) : p.1 ∈ Y := by
    rw [←hphase p hp]
    exact (hdata (pull p) (hright p hp).1).1
  let z := fun p => z0 (pull p)
  let rat := fun p => ratz (pull p)
  let v := fun p => v0 (pull p)
  let Nlen := fun p => Nlen0 (pull p)
  let anchor := fun p => anchor0 (pull p).1 (pull p).2
  let gap := fun p => (pull p).1.2
  have hz p (hp : p ∈ P) : z p ∈ Icc M (2*M) := by
    have hh := hbuffer (pull p) (hright p hp).1
    exact ⟨by linarith only [hh.1,hBuffer],by linarith only [hh.2,hBuffer]⟩
  have hden p (hp : p ∈ P) : (rat p).den ≤ Q ∧ Q ≤ 2*(rat p).den :=
    ⟨(hrat (pull p) (hright p hp).1).1,(hrat (pull p) (hright p hp).1).2.1⟩
  have hinv p (hp : p ∈ P) : ((rat p).den:ℤ) ∣ (rat p).num*v p-1 :=
    hv0 (pull p) (hright p hp).1
  have hlevel p (hp : p ∈ P) : iteratedDeriv 2 (f p.1) (z p)/2 = (rat p:ℝ) := by
    rw [←hphase p hp]
    exact (hrat (pull p) (hright p hp).1).2.2.2.2.2
  have hgeomP p (hp : p ∈ P) :
      N ≤ Nlen p ∧ Nlen p ≤ 3*N ∧
        round (z p)+(Nlen p:ℤ) = sgrid+(N:ℤ)*p.2+2*(N:ℤ) := by
    have hh := hround (pull p) (hright p hp).1
    refine ⟨hh.2.1,hh.2.2.1,?_⟩
    change round (z0 (pull p))+(Nlen0 (pull p):ℤ) = Lgrid p.2
    rw [←hblock p hp]
    exact hh.2.2.2
  have hgridP p (hp : p ∈ P) :
      M ≤ (sgrid:ℝ)+(N:ℝ)*p.2 ∧ (sgrid:ℝ)+(N:ℝ)*p.2 ≤ 2*M := by
    have hm := hmem (pull p) (hright p hp).1
    have ht := ((hS0 (pull p).1 hm.1).1 _).mp hm.2
    have hg := hgeometry (pull p).1 (hfull (pull p) (hright p hp).1)
    rw [hblock p hp] at ht
    exact ⟨by linarith only [ht.1,hg.1.1,hNp],
      by linarith only [ht.2,hg.2.1.2,hNp]⟩
  have hminor p (hp : p ∈ P) :
      1 ≤ Nlen p ∧ (rat p).den ≤ Nlen p ∧
        1 ≤ (iteratedDeriv 3 (f p.1) (round (z p))/6)*((rat p).den:ℝ)^2*Nlen p ∧
      7*((iteratedDeriv 3 (f p.1) (round (z p))/6)*
        ((rat p).den:ℝ)*(Nlen p:ℝ)^2) ≤ K₀ := by
    have hg := (Finset.mem_filter.mp (hright p hp).1).2
    have hcut : 2*(anchor p).den ≤ Q :=
      (Nat.mul_le_mul_right _ (show 2 ≤ 768 by decide)).trans hg.1
    have hmajor : 128*σsrc*R^2 ≤ csrc*(Q:ℝ)*(anchor p).den := by
      have hh : 128*σsrc ≤ 24576*σsrc := by linarith only [hσsrc]
      exact (mul_le_mul_of_nonneg_right hh (sq_nonneg R)).trans hg.2
    exact actual_source_dyadic_cubic_admissibility Fsrc
      hσsrc hcsrc hUsrc hη (hηsmall.trans hηcap) (hy p.1 (hlabelsP p hp))
      hreg hjets hnegative hMtwo (by omega) hRp (hz p hp) hscale hQN
      (hden p hp).1 (hden p hp).2 hcut hmajor
      (hgeomP p hp).1 (hgeomP p hp).2.1 hsourceMesh

  let Gaps := (Refs ×ˢ Refs).filter (fun ab =>
    ab.1 < ab.2 ∧ ∀ t ∈ Refs,¬(ab.1 < t ∧ t < ab.2))
  have hgapData ab (hab : ab ∈ Gaps) :
      ab.1 ∈ Refs ∧ ab.2 ∈ Refs ∧ ab.1 < ab.2 ∧ ∀ t ∈ Refs,¬(ab.1 < t ∧ t < ab.2) := by
    have hh := Finset.mem_filter.mp hab
    exact ⟨(Finset.mem_product.mp hh.1).1,(Finset.mem_product.mp hh.1).2,hh.2⟩
  have hgapMem p (hp : p ∈ P) : gap p ∈ Gaps := by
    have hh := hdata (pull p) (hright p hp).1
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_product.mpr ⟨hh.2.1,hh.2.2.1⟩,hh.2.2.2⟩
  have hchartChoice (ab : ℝ × ℝ) : ∃ e r v s : ℤ, ab ∈ Gaps →
      v*r-e*s = 1 ∧ ((0 < r ∧ (e:ℝ)/r = ab.1) ∨ (r < 0 ∧ (e:ℝ)/r = ab.2)) ∧
      s ≠ 0 ∧ (e:ℝ)/r ∈ Refs ∧ (v:ℝ)/s ∈ Refs ∧ R^2 ≤ (r:ℝ)^2*(Uref:ℝ) ∧
      |(r:ℝ)| < 4*R^2/(Uref:ℝ) ∧ |(s:ℝ)| < 4*R^2/(Uref:ℝ) ∧
      |(e:ℝ)| ≤ (3*Usrc*T/(2*σsrc*M^2)+1)*(4*R^2/(Uref:ℝ)) ∧
      |(v:ℝ)| ≤ (3*Usrc*T/(2*σsrc*M^2)+1)*(4*R^2/(Uref:ℝ)) := by
    by_cases hab : ab ∈ Gaps
    · have hh := hgapData ab hab
      obtain ⟨e,r,v,s,he⟩ := hcharts ab.1 hh.1 ab.2 hh.2.1 hh.2.2.1 hh.2.2.2
      exact ⟨e,r,v,s,fun _ => he⟩
    · exact ⟨0,0,0,0,fun hh => (hab hh).elim⟩
  choose e rRef vRef sRef hchartData using hchartChoice
  have hchart ab (hab : ab ∈ Gaps) : vRef ab*rRef ab-e ab*sRef ab = 1 :=
    (hchartData ab hab).1
  have horientation ab (hab : ab ∈ Gaps) :
      ((0:ℝ) < rRef ab ∧ (e ab:ℝ)/rRef ab = ab.1) ∨
        ((rRef ab:ℝ) < 0 ∧ (e ab:ℝ)/rRef ab = ab.2) := by
    rcases (hchartData ab hab).2.1 with hh | hh
    · exact Or.inl ⟨by exact_mod_cast hh.1,hh.2⟩
    · exact Or.inr ⟨by exact_mod_cast hh.1,hh.2⟩
  have hs ab (hab : ab ∈ Gaps) : sRef ab ≠ 0 := (hchartData ab hab).2.2.1
  have hrefSet ab (hab : ab ∈ Gaps) : (e ab:ℝ)/rRef ab ∈ Refs :=
    (hchartData ab hab).2.2.2.1
  have hparentSet ab (hab : ab ∈ Gaps) : (vRef ab:ℝ)/sRef ab ∈ Refs :=
    (hchartData ab hab).2.2.2.2.1
  have hreferenceDen ab (hab : ab ∈ Gaps) : R^2 ≤ (rRef ab:ℝ)^2*(Uref:ℝ) :=
    (hchartData ab hab).2.2.2.2.2.1
  have hrHeight ab (hab : ab ∈ Gaps) : |(rRef ab:ℝ)| ≤ 4*R^2/(Uref:ℝ) :=
    (hchartData ab hab).2.2.2.2.2.2.1.le
  have hsHeight ab (hab : ab ∈ Gaps) : |(sRef ab:ℝ)| ≤ 4*R^2/(Uref:ℝ) :=
    (hchartData ab hab).2.2.2.2.2.2.2.1.le
  have hheightEq : 3*Usrc*T/(2*σsrc*M^2) = 3*Jref*T/(2*σ*M^2) := by
    dsimp only [Jref]
    field_simp
  have heHeight ab (hab : ab ∈ Gaps) :
      |(e ab:ℝ)| ≤ (3*Jref*T/(2*σ*M^2)+1)*(4*R^2/(Uref:ℝ)) := by
    rw [←hheightEq]
    exact (hchartData ab hab).2.2.2.2.2.2.2.2.1
  have hvHeight ab (hab : ab ∈ Gaps) :
      |(vRef ab:ℝ)| ≤ (3*Jref*T/(2*σ*M^2)+1)*(4*R^2/(Uref:ℝ)) := by
    rw [←hheightEq]
    exact (hchartData ab hab).2.2.2.2.2.2.2.2.2
  have hgapWidth ab (hab : ab ∈ Gaps) : ab.2-ab.1 ≤ 7*(Uref:ℝ)/(2*R^2) := by
    have hh := hgapData ab hab
    exact (hgaps ab.1 hh.1 ab.2 hh.2.1 hh.2.2.1 hh.2.2.2).2.1
  have hsep u (hu : u ∈ Refs) v (hv : v ∈ Refs) (huv : u ≠ v) :
      ((Uref:ℝ)/R^2)/4 < |u-v| := by
    convert hRefSep u hu v hv huv using 1
    ring
  have hwide w (hw : w ∈ Icc M (2*M)) : w ∈ Icc (3*M/4) (9*M/4) := by
    constructor <;> linarith only [hw.1,hw.2,hM]
  have hfamilyGap p (hp : p ∈ P) : (rat p:ℝ) ∈ Icc (gap p).1 (gap p).2 := by
    have hi := (hright p hp).1
    have hg := hgeometry (pull p).1 (hfull (pull p) hi)
    have hm := positive_difference_physical_curvature_strictMono Fsrc
      hσsrc hcsrc hη (hηsmall.trans hηcap) (hy p.1 (hlabelsP p hp))
      hreg hnegative hT hM
    have hl := hm (hwide _ hg.1) (hwide _ (hz p hp)) (hzin (pull p) hi).1
    have hu := hm (hwide _ (hz p hp)) (hwide _ hg.2.1) (hzin (pull p) hi).2
    change iteratedDeriv 2 (f p.1) (x₁ (pull p).1)/2 <
      iteratedDeriv 2 (f p.1) (z p)/2 at hl
    change iteratedDeriv 2 (f p.1) (z p)/2 <
      iteratedDeriv 2 (f p.1) (x₂ (pull p).1)/2 at hu
    rw [hlevel p hp] at hl hu
    have hleftLevel : iteratedDeriv 2 (f p.1) (x₁ (pull p).1)/2 = (gap p).1 := by
      rw [←hphase p hp]
      exact hg.2.2.2.1
    have hrightLevel : iteratedDeriv 2 (f p.1) (x₂ (pull p).1)/2 = (gap p).2 := by
      rw [←hphase p hp]
      exact hg.2.2.2.2.1
    rw [hleftLevel] at hl
    rw [hrightLevel] at hu
    exact ⟨hl.le,hu.le⟩
  let Aphase := fun _y : ℝ => (⌈M⌉:ℤ)
  let Wphase := fun _y : ℝ => 2*M-(⌈M⌉:ℤ)
  let xlocal := fun p : ℝ × ℤ => z p-(Aphase p.1:ℝ)
  let Wide := (56*(Uref:ℝ)/κ)*(N:ℝ)
  let Hshort := (N:ℝ)/(Cphys+2)
  have hWide : 0 ≤ Wide := by dsimp only [Wide]; positivity
  have hHshort : 0 ≤ Hshort := by dsimp only [Hshort]; positivity
  have hx p (hp : p ∈ P) : xlocal p ∈ Ioo (1/2:ℝ) (Wphase p.1-1/2) := by
    have hh := hlocal (pull p) (hright p hp).1 0 (by
      change |(0:ℝ)|+2 ≤ Wide+Hshort+2
      rw [abs_zero]
      linarith only [hWide,hHshort])
    simpa only [add_zero] using hh
  have hwideL p (hp : p ∈ P) : xlocal p-Wide ∈ Ioo (1/2:ℝ) (Wphase p.1-1/2) := by
    have hh := hlocal (pull p) (hright p hp).1 (-Wide) (by
      change |-Wide|+2 ≤ Wide+Hshort+2
      rw [abs_neg,abs_of_nonneg hWide]
      linarith only [hHshort])
    simpa only [sub_eq_add_neg] using hh
  have hwideU p (hp : p ∈ P) : xlocal p+Wide ∈ Ioo (1/2:ℝ) (Wphase p.1-1/2) :=
    hlocal (pull p) (hright p hp).1 Wide (by
      change |Wide|+2 ≤ Wide+Hshort+2
      rw [abs_of_nonneg hWide]
      linarith only [hHshort])
  have hL p (hp : p ∈ P) : xlocal p-Hshort ∈ Ioo (1/2:ℝ) (Wphase p.1-1/2) := by
    have hh := hlocal (pull p) (hright p hp).1 (-Hshort) (by
      change |-Hshort|+2 ≤ Wide+Hshort+2
      rw [abs_neg,abs_of_nonneg hHshort]
      linarith only [hWide])
    simpa only [sub_eq_add_neg] using hh
  have hU p (hp : p ∈ P) : xlocal p+Hshort ∈ Ioo (1/2:ℝ) (Wphase p.1-1/2) :=
    hlocal (pull p) (hright p hp).1 Hshort (by
      change |Hshort|+2 ≤ Wide+Hshort+2
      rw [abs_of_nonneg hHshort]
      linarith only [hWide])
  let ε := κ/(16*(Cphys+2)*R^2)
  have htol : csrc/(64*σsrc*R^2) ≤ ε := by
    have hb : csrc ≤ 4*κ*σsrc/(Cphys+2) := by
      convert hanchorBudget using 1
      dsimp only [Cphys]
      ring
    calc
      csrc/(64*σsrc*R^2) ≤ (4*κ*σsrc/(Cphys+2))/(64*σsrc*R^2) :=
        div_le_div_of_nonneg_right hb (by positivity)
      _ = ε := by dsimp only [ε]; field_simp; ring
  have hanchor p (hp : p ∈ P) : |(anchor p:ℝ)-(rat p:ℝ)| ≤ ε := by
    rw [abs_sub_comm]
    exact ((hrat (pull p) (hright p hp).1).2.2.2.1).trans htol
  have hcut p (hp : p ∈ P) : 256*((anchor p).den:ℝ) ≤ (Q:ℝ)/3 :=
    (hdense (by norm_num) le_rfl (pull p) (hright p hp).1).1
  have hcount p (hp : p ∈ P) : 256 ≤ 2*ε*((Q:ℝ)/3)*(anchor p).den :=
    (hdense (by norm_num) le_rfl (pull p) (hright p hp).1).2 ε htol
  have hmodel p (hp : p ∈ P) : Expdb.IsApproximateModelPhaseFunction
      (fun u => (T/T)*(Fsrc u-Fsrc (u+η*p.1))/(σsrc*η)) σ 4 δ := by
    simpa only [div_self hT.ne',one_mul] using hmodels p.1 (hlabelsP p hp)
  have hseparation p (hp : p ∈ P) q (hq : q ∈ P) (hpq : p.1 ≠ q.1) :
      1 ≤ Jsep*|p.1-q.1| := hsepY p.1 (hlabelsP p hp) q.1 (hlabelsP q hq) hpq
  obtain ⟨hcolor,hphysicalCount,hunweighted,hweighted⟩ :=
    hfamily P Fsrc z rat v Nlen Q K₀ N Vscale R Jsep (fun _ => sgrid)
      (η:=η) (Tsrc:=T) (M:=M) (δ:=δ) (Bcut:=Bcut) (Bselect:=Bselect)
      Uref Refs Gaps Aphase Wphase gap anchor e rRef vRef sRef
      hη hηsmall hT hT hM hδ (by simp only [one_mul,le_refl]) hQ
      (fun p hp => hy p.1 (hlabelsP p hp)) hz hreg hjets htests hden hinv hnegative
      hMtwo hVscale hN hJsep hJM hNM hmesh hgeomP hseparation hmodel hlevel
      (fun p hp => ⟨(hminor p hp).1,(hminor p hp).2.1,(hminor p hp).2.2.1⟩)
      (fun p hp => (hminor p hp).2.2.2)
      hregime hR hRM hscale (fun _ _ => Int.le_ceil M)
      (fun _ _ => by dsimp only [Aphase,Wphase]; linarith only)
      hx hgapMem hchart horientation hBcut hs hrefSet hparentSet hsep hwideL hwideU hUref
      hBselectSize hcutMargin hselectedWrap hreferenceDen hgapWidth hRQ
      hselectedUpper hscaleTen hfamilyGap hgapData (by exact_mod_cast hQN) hNsqM hUR
      hrHeight hsHeight heHeight hvHeight hsmall hNR hRN hNcube hminscale
      hNreal hL hU hanchor hcut hcount hsize hD hΔ hBsize rfl hUlo

  let q0 := fun i => (ratz i).den
  let mu0 := fun i => iteratedDeriv 3 (f i.1.1) (round (z0 i))/6
  let ell0 := fun i => deriv (f i.1.1) (round (z0 i))
  let b0 := fun i (p : Fin 2) => (⌊(q0 i:ℝ)*ell0 i⌋+(p:ℕ) : ℤ)
  let tau0 := fun i p => ((b0 i p:ℝ)-(q0 i:ℝ)*ell0 i)/2
  let dual0 := fun i => -2*mu0 i*(Real.sqrt (2/(3*mu0 i*(q0 i:ℝ))))^3
  let x0 := fun i p =>
    (![-(v0 i:ℝ)*b0 i p/q0 i,-(v0 i:ℝ)/q0 i,
      dual0 i,3*dual0 i*tau0 i p/2] : Fin 4 → ℝ)
  let FourierNorm := fun i p =>
    ‖∑ j : ZMod K₀, ZMod.stdAddChar (-(j*k0))*
      GafniTao.fordAdditiveCharacter (∑ d,x0 i p d*
        (![(j.val+1:ℝ),(j.val+1:ℝ)^2,(j.val+1:ℝ)^((3:ℝ)/2),
          Real.sqrt (j.val+1:ℝ)] : Fin 4 → ℝ) d)‖
  let Wpoint := fun i p => (Real.sqrt (2*(q0 i:ℝ))/
    ((q0 i:ℝ)*Real.sqrt (mu0 i*(Nlen0 i:ℝ))))*FourierNorm i p
  let Wsum := ∑ i ∈ Gtag, ∑ p : Fin 2,Wpoint i p
  let BoundCard := fun y : ℝ =>
    (144*Usrc/(csrc*κ))^6*(R^2/(Q:ℝ))^6*
      C*(K₀:ℝ)^((12:ℝ)+εloss)*Cap^11*(10*y*(M/(N:ℝ)))^10*
        (Vscale*Dtype*y*(M/(N:ℝ))*(1+Δtype*Jsep)+
          y^2*(Vscale*(Kupper+Klower)+Klarge)*T^εloss)
  have hweightedReindexed : Wsum^12 ≤ BoundCard ((P.image Prod.fst).card:ℝ) := by
    have hw := hweighted k0
    have hsum := hsumParity (fun ip => Wpoint ip.1 ip.2)
    change (∑ ip ∈ P ×ˢ (Finset.univ : Finset (Fin 2)),
      Wpoint (pull ip.1) ip.2) = Wsum at hsum
    rw [←hsum]
    convert hw using 1
    · congr 1
      apply Finset.sum_congr rfl
      intro ip hip
      have hp := hphase ip.1 (Finset.mem_product.mp hip).1
      dsimp only [Wpoint,FourierNorm,x0,dual0,tau0,b0,q0,mu0,ell0,z,rat,v,Nlen,Nlen0]
      rw [hp]
    · simp only [BoundCard,κ,Cphys,c,J,B,Vscale,lambda,Uband,ChartCap,NarrowCap,Cap,
        μ₀,U₀,Δtype,C₂,C₃,Ct,Cc,Kres,Lunit,Gamma,Cthird,AupperConst,BupperConst,
        AlowerConst,BlowerConst,DupperConst,DlowerConst,CostUpper,CostLower,
        Cpack,Cfirst,Cgap,Cmain,Ctail,Kupper,Klower,Klarge,mul_one,one_pow]
  have hBselect : 0 < Bselect := by
    have hh : 0 < 2+168/κ := by positivity
    exact hh.trans_le hBselectSize
  have hBoundMono {y₁ y₂ : ℝ} (hy₁ : 0 ≤ y₁) (hy₂ : y₁ ≤ y₂) :
      BoundCard y₁ ≤ BoundCard y₂ :=
    actual_source_family_card_bound_mono Q K₀ N Uref hσsrc hcsrc hUsrc hσ
      hθ ha hCU hCL hDU hDL hC hDtype hT hM hNp hJsep hδzero hBselect hy₁ hy₂
  have hphaseCard : ((P.image Prod.fst).card:ℝ) ≤ Y.card := by
    apply Nat.cast_le.mpr
    apply Finset.card_le_card
    intro y hym
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hym
    exact hlabelsP p hp
  have hW12 : Wsum^12 ≤ FamilyBound :=
    hweightedReindexed.trans (hBoundMono (Nat.cast_nonneg _) hphaseCard)
  let ErrPoint := fun i => Real.sqrt (Nlen0 i)*Real.log (2*(Nlen0 i:ℝ))+
    1/(mu0 i*(Nlen0 i:ℝ)^2)
  let RawError := ∑ i ∈ Gtag,ErrPoint i
  have hError : RawError ≤ Error := by
    have he := (actual_source_grid_completion_error P Y Fsrc z Nlen
      (s:=(sgrid:ℝ)) hσsrc hcsrc hUsrc hη (hηsmall.trans hηcap)
      (by omega) hMtwo hRp hscale hy hlabelsP hgridP hz
      (fun p hp => ⟨(hgeomP p hp).1,(hgeomP p hp).2.1⟩)
      hreg hjets hnegative).2
    have hsum := hsumP ErrPoint
    change (∑ p ∈ P,ErrPoint (pull p)) = RawError at hsum
    rw [←hsum]
    convert he using 1
    apply Finset.sum_congr rfl
    intro p hp
    dsimp only [ErrPoint,mu0,z,Nlen,Nlen0]
    rw [hphase p hp]
  have hCorePhase : ((Gcore.image Prod.fst).card:ℝ) ≤ Y.card := by
    have hs : Gcore⊆Gref := Finset.filter_subset _ _
    exact_mod_cast (Finset.card_le_card (Finset.image_subset_image hs)).trans hphaseCount
  have hDlog : 0 ≤ Dlog := by dsimp only [Dlog]; positivity
  have hCerror : 0 ≤ Cerror := by dsimp only [Cerror]; positivity
  have hlogD : 0 ≤ 2+Real.log (Dlog+1) :=
    add_nonneg (by norm_num) (Real.log_nonneg (by linarith only [hDlog]))
  have hMajor : ((Gcore.image Prod.fst).card:ℝ)*Cerror*(M*R/(Q:ℝ))*
      (2+Real.log (Dlog+1)) ≤ Major := by
    dsimp only [Major]
    gcongr
  have hKpos : 0 < K₀ := NeZero.pos K₀
  have hlogK : 0 ≤ 1+Real.log K₀ :=
    add_nonneg zero_le_one (Real.log_nonneg (by exact_mod_cast hKpos))
  have hWsum : 0 ≤ Wsum := by
    apply Finset.sum_nonneg
    intro i _hi
    apply Finset.sum_nonneg
    intro p _hp
    exact mul_nonneg (div_nonneg (Real.sqrt_nonneg _)
      (mul_nonneg (Nat.cast_nonneg _) (Real.sqrt_nonneg _))) (norm_nonneg _)
  have hCsrcpos : 0 ≤ Csrc := zero_le_one.trans hCsrc
  have hMajorNN : 0 ≤ Major := mul_nonneg
    (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) hCerror)
      (div_nonneg (mul_nonneg hM.le hRp.le) (Nat.cast_nonneg _))) hlogD
  have hErrorNN : 0 ≤ Error := by
    have hlogN : 0 ≤ Real.log (6*(N:ℝ)) :=
      Real.log_nonneg (by linarith only [hNreal])
    clear * - hM hNp hσsrc hcsrc hRp hlogN
    dsimp only [Error]
    positivity
  have hBoundary : 0 ≤ Boundary := by
    clear * - hUsrc hσsrc hM hUp hcsrc hNp hBuffer
    dsimp only [Boundary]
    positivity
  let Orig := ∑ p ∈ Y ×ˢ I, ‖∑ n ∈ Finset.Ioc (Lgrid p.2) (Lgrid p.2+Hlen p.1 p.2),
    (𝐞 (f p.1 n):ℂ)‖
  have hOrig : 0 ≤ Orig := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  have hsourceBound := (hwhole I hI).2 hstrongRQ hNRM
  change Orig ≤ Csrc*(((Gcore.image Prod.fst).card:ℝ)*Cerror*(M*R/(Q:ℝ))*
    (2+Real.log (Dlog+1))+((1+Real.log K₀)*Wsum+RawError))+Boundary at hsourceBound
  let Aterm := Csrc*(Major+Error)+Boundary
  let Bterm := (Csrc*(1+Real.log K₀))*Wsum
  have hAterm : 0 ≤ Aterm := add_nonneg
    (mul_nonneg hCsrcpos (add_nonneg hMajorNN hErrorNN)) hBoundary
  have hBterm : 0 ≤ Bterm := mul_nonneg (mul_nonneg hCsrcpos hlogK) hWsum
  have hOrigSum : Orig ≤ Aterm+Bterm := by
    calc
      Orig ≤ Csrc*(Major+((1+Real.log K₀)*Wsum+Error))+Boundary :=
        hsourceBound.trans (add_le_add
          (mul_le_mul_of_nonneg_left (add_le_add hMajor (add_le_add le_rfl hError)) hCsrcpos) le_rfl)
      _ = Aterm+Bterm := by dsimp only [Aterm,Bterm]; ring
  have hBpower : Bterm^12 ≤ (Csrc*(1+Real.log K₀))^12*FamilyBound := by
    dsimp only [Bterm]
    rw [mul_pow]
    exact mul_le_mul_of_nonneg_left hW12 (pow_nonneg (mul_nonneg hCsrcpos hlogK) 12)
  calc
    Orig^12 ≤ (Aterm+Bterm)^12 := pow_le_pow_left₀ hOrig hOrigSum 12
    _ ≤ 2^11*(Aterm^12+Bterm^12) := add_pow_le hAterm hBterm 12
    _ ≤ _ := mul_le_mul_of_nonneg_left (add_le_add le_rfl hBpower) (by norm_num)

example
    {σsrc csrc Usrc σ εloss : ℝ}
    (hσsrc : 0 < σsrc) (hcsrc : 0 < csrc) (hUsrc : 0 < Usrc)
    (hσ : 0 < σ) (hεloss : 0 < εloss)
    (hanchorBudget : csrc ≤ 4*modelPhaseThirdLower σ*σsrc/(σ*(σ+1)+3)) :
    let κ := modelPhaseThirdLower σ
    let Ratio := 18*Usrc^2/(σsrc*csrc*κ)
    let L := max (8*Ratio^2)
      (32*(modelPhaseJetCoefficient σ 3+1)*(3*Usrc/σsrc)/κ^2)
    ∃ Csrc η₀ a Cupper Clower Dupper Dlower C Dtype : ℝ,
      1 ≤ Csrc ∧ 0 < η₀ ∧ η₀ ≤ 1/8 ∧ 0 < a ∧
      0 < Cupper ∧ 0 < Clower ∧ 0 < Dupper ∧ 0 < Dlower ∧ 0 < C ∧ 0 < Dtype ∧
    ∀ {θ : ℝ}, 0 < θ → θ ≤ 1/24 → θ ≤ 1/(8*(L+3)) →
    ∀ᶠ T : ℝ in Filter.atTop, ∀ (Fsrc : ℝ → ℝ) (Y : Finset ℝ)
      (Hlen : ℝ → ℤ → ℕ) (I : Finset ℤ) (Q K₀ N Uref : ℕ) [NeZero K₀]
      (sgrid : ℤ) (R Jsep : ℝ) {η M δ Bcut Bselect : ℝ},
    0 < η → η ≤ η₀ → 0 < T → 2 ≤ N →
    1 ≤ R → R ≤ M → 0 ≤ δ → δ ≤ min κ 1 →
    0 < Jsep → Jsep ≤ M →
    (∀ y ∈ Y, y ∈ Icc (1:ℝ) 2) →
    (∀ y ∈ Y, ∀ z ∈ Y, y ≠ z → 1 ≤ Jsep*|y-z|) →
    (∀ y ∈ Y, ∀ k, Hlen y k ≤ N) →
    (∀ k ∈ I, (sgrid:ℝ)+(N:ℝ)*k ∈ Icc M (2*M)) →
    (∀ w, 0 < w → ContDiffAt ℝ ∞ Fsrc w) →
    (∀ w ∈ Icc (1/2:ℝ) 3, ∀ n ≤ 6, |iteratedDeriv (n+1) Fsrc w| ≤ Usrc) →
    (∀ w ∈ Icc (1/2:ℝ) 3, ∀ j,
      csrc ≤ |HuxleyModel.tests (fun i : Fin 4 => iteratedDeriv (i.val+3) Fsrc w) j|) →
    (∀ w ∈ Icc (1/2:ℝ) 3, iteratedDeriv 4 Fsrc w ≤ -csrc) →
    (∀ y ∈ Y, Expdb.IsApproximateModelPhaseFunction
      (fun u => (Fsrc u-Fsrc (u+η*y))/(σsrc*η)) σ 4 δ) →
    T*(N:ℝ)*R^2 = M^3 →
    7*(N:ℝ)+2 ≤ M/4 →
    (3*Usrc/σsrc)*(6*(N:ℝ)+1)^4 ≤ M*(N:ℝ)*R^2 →
    (3*Usrc/(4*σsrc))*(6*(N:ℝ)+1)^2 ≤ (N:ℝ)*R^2 →
    3*Usrc ≤ σsrc*(Uref:ℝ) →
    63*(Usrc/(2*σsrc*(N:ℝ)*R^2))*(Q:ℝ)*(N:ℝ)^2 ≤ K₀ →
    (Q:ℝ)*(N:ℝ) ≤ (K₀:ℝ)*R^2 →
    (N:ℝ)^4 ≤ M*R^3*(Real.log T)^((3:ℝ)/2) →
    1 ≤ Uref → 0 < Bcut →
    2+168/κ ≤ Bselect → 7*Bcut ≤ κ*Bselect →
    Bselect^2*(Uref:ℝ)^3*R^2 ≤ (N:ℝ)^2 →
    (Uref:ℝ) ≤ ((N:ℝ)/(Q:ℝ))^((2:ℝ)/3)/Bselect →
    ((N:ℝ)/(Q:ℝ))^((2:ℝ)/3)/(2*Bselect) ≤ (Uref:ℝ) →
    (N:ℝ)^10 ≤ M^3*R^7 →
    Q ≤ N → (N:ℝ)^2 ≤ M → (Uref:ℝ) ≤ R^2 →
    768*R ≤ (Q:ℝ) → (N:ℝ)*R ≤ M →
    let Cphys := σ*(σ+1)+1
    let c := κ/6
    let J := Cphys/6
    let B := max 1 (max (2*Real.sqrt J) (8*J*Real.sqrt J/(3*c)))
    B*R^2/(N:ℝ)^2 ≤ 1/2 →
    (N:ℝ) ≤ R^2 → R ≤ (N:ℝ) → (N:ℝ)^3 ≤ M*R^2 →
    2*R^2 ≤ (Q:ℝ)*(N:ℝ) →
    let Vscale := (Uref:ℝ)^((3:ℝ)/2)
    let lambda := csrc*κ*T/(12*Usrc*M^2)
    let Uband := (3*Usrc/σsrc)*T/(2*M^2)
    let ChartCap := (4/a+3)*((6*Usrc/σsrc)/a+3)*((4*σsrc/csrc)/a+3)
    let NarrowCap := (4/θ+3)*(72*Usrc^2/(σsrc*csrc*κ*θ)+3)
    let Cap := 3*ChartCap*NarrowCap
    let μ₀ := csrc*T/(12*σsrc*M^3)
    let U₀ := Usrc*T/(2*σsrc*M^3)
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
    let AupperConst := 2*Cupper*(Cthird+1)*1^2/(κ*Lunit^3)
    let BupperConst := Cupper*(Cthird+1)*1^2/Lunit^2+Dupper*(B+1)*1^2/4
    let AlowerConst := 8*Clower*(Cthird+1)/(κ*Lunit^3)
    let BlowerConst := 4*Clower*(Cthird+1)/Lunit^2+Dlower*(B+1)
    let DupperConst := θ*(3*Usrc/σsrc)*1/2
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

    let Buffer := (56*(Uref:ℝ)/κ)*(N:ℝ)+(N:ℝ)/(Cphys+2)+2
    let Dlog := 64*σsrc*R^2/(csrc*((Q:ℝ)/768))
    let Cerror := (768:ℝ)*((6*Usrc/σsrc)*(64*σsrc/csrc)^2+192*σsrc/csrc)+
      ((3*Usrc/σsrc+csrc/(32*σsrc))*((24576*σsrc)/csrc)^2+(24576*σsrc)/csrc)
    let Major := (Y.card:ℝ)*Cerror*(M*R/(Q:ℝ))*(2+Real.log (Dlog+1))
    let Error := (Y.card:ℝ)*(M/(N:ℝ)+1)*
      (Real.sqrt (3*(N:ℝ))*Real.log (6*(N:ℝ))+12*σsrc*R^2/(csrc*(N:ℝ)))
    let Boundary := (Y.card:ℝ)*((24*Usrc/σsrc)*M/(Uref:ℝ)+
      (56*σsrc/csrc)*(N:ℝ)*(Uref:ℝ)+6*(N:ℝ)+2*Buffer)
    let FamilyBound := (144*Usrc/(csrc*κ))^6*(R^2/(Q:ℝ))^6*
      C*(K₀:ℝ)^((12:ℝ)+εloss)*Cap^11*(10*(Y.card:ℝ)*(M/(N:ℝ)))^10*
        (Vscale*Dtype*(Y.card:ℝ)*(M/(N:ℝ))*(1+Δtype*Jsep)+
          (Y.card:ℝ)^2*(Vscale*(Kupper+Klower)+Klarge)*T^εloss)
    let f := fun y w => T*(Fsrc (w/M)-Fsrc (w/M+η*y))/(σsrc*η)
    let Lgrid := fun k : ℤ => sgrid+(N:ℤ)*k+2*(N:ℤ)
    (∑ p ∈ Y ×ˢ I, ‖∑ n ∈ Finset.Ioc (Lgrid p.2) (Lgrid p.2+Hlen p.1 p.2),
      (𝐞 (f p.1 n):ℂ)‖)^12 ≤ 
      2^11*((Csrc*(Major+Error)+Boundary)^12+
        (Csrc*(1+Real.log K₀))^12*FamilyBound)
 :=
  HuxleyBufferedFamilyAssemblyScratch.eventually_positive_difference_buffered_source_physical_sieve (σsrc:=σsrc) (csrc:=csrc) (Usrc:=Usrc) (σ:=σ) (εloss:=εloss) hσsrc hcsrc hUsrc hσ hεloss hanchorBudget


example
    (S : Finset ((ℝ × (ℝ × ℝ)) × ℤ))
    (hinj : Set.InjOn (fun i : (ℝ × (ℝ × ℝ)) × ℤ => (i.1.1,i.2)) (S : Set _)) :
    let tag := fun i : (ℝ × (ℝ × ℝ)) × ℤ => (i.1.1,i.2)
    let P := S.image tag
    ∃ pull : ℝ × ℤ → (ℝ × (ℝ × ℝ)) × ℤ,
      (∀ p ∈ P, pull p ∈ S ∧ tag (pull p) = p) ∧
      (∀ i ∈ S, pull (tag i) = i) ∧
      P.card = S.card ∧
      (∀ w : (ℝ × (ℝ × ℝ)) × ℤ → ℝ,
        (∑ p ∈ P,w (pull p)) = ∑ i ∈ S,w i) ∧
      ∀ w : ((ℝ × (ℝ × ℝ)) × ℤ) × Fin 2 → ℝ,
        (∑ ip ∈ P ×ˢ (Finset.univ : Finset (Fin 2)),w (pull ip.1,ip.2)) = 
          ∑ i ∈ S, ∑ p : Fin 2,w (i,p) :=
  HuxleyBufferedFamilyAssemblyScratch.actual_source_index_transport S hinj

example
    (F : ℝ → ℝ) {σ c J η y z T M R : ℝ} {N Q A K₀ : ℕ} {a r : ℚ}
    (hσ : 0 < σ) (hc : 0 < c) (hJ : 0 < J)
    (hη : 0 < η) (hηmax : η ≤ 1/8) (hy : y ∈ Icc (1:ℝ) 2)
    (hf : ∀ w, 0 < w → ContDiffAt ℝ ∞ F w)
    (hbound : ∀ w ∈ Icc (1/2:ℝ) 3, ∀ n ≤ 6, |iteratedDeriv (n+1) F w| ≤ J)
    (hnegative : ∀ w ∈ Icc (1/2:ℝ) 3, iteratedDeriv 4 F w ≤ -c)
    (hM : 2 ≤ M) (hN : 1 ≤ N) (hR : 0 < R) (hz : z ∈ Icc M (2*M))
    (hphase : T*(N:ℝ)*R^2 = M^3)
    (hQN : Q ≤ N) (hden : r.den ≤ Q) (hhalf : Q ≤ 2*r.den)
    (hcut : 2*a.den ≤ Q) (hmajor : 128*σ*R^2 ≤ c*(Q:ℝ)*a.den)
    (hAlow : N ≤ A) (hAhigh : A ≤ 3*N)
    (hmesh : 63*(J/(2*σ*(N:ℝ)*R^2))*(Q:ℝ)*(N:ℝ)^2 ≤ K₀) :
    let f := fun w => T*(F (w/M)-F (w/M+η*y))/(σ*η)
    let μ := iteratedDeriv 3 f (round z)/6
    1 ≤ A ∧ r.den ≤ A ∧ 1 ≤ μ*(r.den:ℝ)^2*A ∧
      7*(μ*(r.den:ℝ)*(A:ℝ)^2) ≤ K₀ :=
  HuxleyBufferedFamilyAssemblyScratch.actual_source_dyadic_cubic_admissibility F (σ:=σ) (c:=c) (J:=J) (η:=η) (y:=y) (z:=z) (T:=T) (M:=M) (R:=R) (N:=N) (Q:=Q) (A:=A) (K₀:=K₀) (a:=a) (r:=r) hσ hc hJ hη hηmax hy hf hbound hnegative hM hN hR hz hphase hQN hden hhalf hcut hmajor hAlow hAhigh hmesh

example
    {σ c N R A μ : ℝ} (hσ : 0 < σ) (hc : 0 < c) (hN : 1 ≤ N) (hR : 0 < R)
    (hAlow : N ≤ A) (hAhigh : A ≤ 3*N)
    (hμ : c/(12*σ*N*R^2) ≤ μ) :
    Real.sqrt A*Real.log (2*A)+1/(μ*A^2) ≤ 
      Real.sqrt (3*N)*Real.log (6*N)+12*σ*R^2/(c*N) :=
  HuxleyBufferedFamilyAssemblyScratch.cubic_completion_point_error (σ:=σ) (c:=c) (N:=N) (R:=R) (A:=A) (μ:=μ) hσ hc hN hR hAlow hAhigh hμ

example
    (S : Finset (ℝ × ℤ)) (Y : Finset ℝ) (F : ℝ → ℝ)
    (z : ℝ × ℤ → ℝ) (A : ℝ × ℤ → ℕ)
    {σ c J η T M R s : ℝ} {N : ℕ}
    (hσ : 0 < σ) (hc : 0 < c) (hJ : 0 < J)
    (hη : 0 < η) (hηmax : η ≤ 1/8)
    (hN : 1 ≤ N) (hM : 2 ≤ M) (hR : 0 < R)
    (hphase : T*(N:ℝ)*R^2 = M^3)
    (hy : ∀ y ∈ Y, y ∈ Icc (1:ℝ) 2)
    (hlabels : ∀ i ∈ S, i.1 ∈ Y)
    (hgrid : ∀ i ∈ S, M ≤ s+(N:ℝ)*i.2 ∧ s+(N:ℝ)*i.2 ≤ 2*M)
    (hz : ∀ i ∈ S, z i ∈ Icc M (2*M))
    (hA : ∀ i ∈ S, N ≤ A i ∧ A i ≤ 3*N)
    (hf : ∀ w, 0 < w → ContDiffAt ℝ ∞ F w)
    (hbound : ∀ w ∈ Icc (1/2:ℝ) 3, ∀ n ≤ 6, |iteratedDeriv (n+1) F w| ≤ J)
    (hnegative : ∀ w ∈ Icc (1/2:ℝ) 3, iteratedDeriv 4 F w ≤ -c) :
    let f := fun i w => T*(F (w/M)-F (w/M+η*i.1))/(σ*η)
    let μ := fun i => iteratedDeriv 3 (f i) (round (z i))/6
    (S.card:ℝ) ≤ (Y.card:ℝ)*(M/(N:ℝ)+1) ∧
    (∑ i ∈ S, (Real.sqrt (A i)*Real.log (2*(A i:ℝ))+1/(μ i*(A i:ℝ)^2))) ≤ 
      (Y.card:ℝ)*(M/(N:ℝ)+1)*
        (Real.sqrt (3*(N:ℝ))*Real.log (6*(N:ℝ))+12*σ*R^2/(c*(N:ℝ))) :=
  HuxleyBufferedFamilyAssemblyScratch.actual_source_grid_completion_error S Y F z A (σ:=σ) (c:=c) (J:=J) (η:=η) (T:=T) (M:=M) (R:=R) (s:=s) (N:=N) hσ hc hJ hη hηmax hN hM hR hphase hy hlabels hgrid hz hA hf hbound hnegative

example
    {σsrc csrc Usrc σ εloss θ a Cupper Clower Dupper Dlower C Dtype
      T M R Jsep δ Bselect : ℝ} (Q K₀ N Uref : ℕ)
    (hσsrc : 0 < σsrc) (hcsrc : 0 < csrc) (hUsrc : 0 < Usrc) (hσ : 0 < σ)
    (hθ : 0 < θ) (ha : 0 < a) (hCU : 0 < Cupper) (hCL : 0 < Clower)
    (hDU : 0 < Dupper) (hDL : 0 < Dlower) (hC : 0 < C) (hDtype : 0 < Dtype)
    (hT : 0 < T) (hM : 0 < M) (hNp : (0:ℝ) < N)
    (hJsep : 0 < Jsep) (hδzero : 0 ≤ δ) (hBselect : 0 < Bselect) :
    let κ := modelPhaseThirdLower σ
    let Cphys := σ*(σ+1)+1
    let c := κ/6
    let J := Cphys/6
    let B := max 1 (max (2*Real.sqrt J) (8*J*Real.sqrt J/(3*c)))
    let Vscale := (Uref:ℝ)^((3:ℝ)/2)
    let lambda := csrc*κ*T/(12*Usrc*M^2)
    let Uband := (3*Usrc/σsrc)*T/(2*M^2)
    let ChartCap := (4/a+3)*((6*Usrc/σsrc)/a+3)*((4*σsrc/csrc)/a+3)
    let NarrowCap := (4/θ+3)*(72*Usrc^2/(σsrc*csrc*κ*θ)+3)
    let Cap := 3*ChartCap*NarrowCap
    let μ₀ := csrc*T/(12*σsrc*M^3)
    let U₀ := Usrc*T/(2*σsrc*M^3)
    let Δtype := (16*U₀/μ₀)*Real.sqrt (U₀*(Q:ℝ)^3)*Real.sqrt K₀/(6*(K₀:ℝ)^2)
    let C₂ := modelPhaseJetCoefficient σ 2+δ
    let C₃ := modelPhaseJetCoefficient σ 3+δ
    let Ct := C₂/2+5*C₃/12
    let Cc := C₂/κ+C₃/(2*κ)
    let Kres := 4*(37*B/2+16*B*Cc+2*Ct+2*Cc+
      2*quarticNonlinearResidualConstant σ δ)/κ
    let Lunit := 2*κ/Cphys
    let Gamma := Cphys/κ
    let Cthird := Gamma*(32*Kres+9*quarticReciprocalConstant σ δ)
    let AupperConst := 2*Cupper*(Cthird+1)*1^2/(κ*Lunit^3)
    let BupperConst := Cupper*(Cthird+1)*1^2/Lunit^2+Dupper*(B+1)*1^2/4
    let AlowerConst := 8*Clower*(Cthird+1)/(κ*Lunit^3)
    let BlowerConst := 4*Clower*(Cthird+1)/Lunit^2+Dlower*(B+1)
    let DupperConst := θ*(3*Usrc/σsrc)*1/2
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
    let BoundCard := fun y : ℝ =>
      (144*Usrc/(csrc*κ))^6*(R^2/(Q:ℝ))^6*
        C*(K₀:ℝ)^((12:ℝ)+εloss)*Cap^11*(10*y*(M/(N:ℝ)))^10*
          (Vscale*Dtype*y*(M/(N:ℝ))*(1+Δtype*Jsep)+
            y^2*(Vscale*(Kupper+Klower)+Klarge)*T^εloss)
    ∀ {y₁ y₂ : ℝ}, 0 ≤ y₁ → y₁ ≤ y₂ → BoundCard y₁ ≤ BoundCard y₂ :=
  HuxleyBufferedFamilyAssemblyScratch.actual_source_family_card_bound_mono (σsrc:=σsrc) (csrc:=csrc) (Usrc:=Usrc) (σ:=σ) (εloss:=εloss) (θ:=θ) (a:=a) (Cupper:=Cupper) (Clower:=Clower) (Dupper:=Dupper) (Dlower:=Dlower) (C:=C) (Dtype:=Dtype) (T:=T) (M:=M) (R:=R) (Jsep:=Jsep) (δ:=δ) (Bselect:=Bselect) Q K₀ N Uref hσsrc hcsrc hUsrc hσ hθ ha hCU hCL hDU hDL hC hDtype hT hM hNp hJsep hδzero hBselect


private theorem actual_reference_hull_order_bound
    (S : Finset ℝ) {H : ℤ} {δ scale : ℝ}
    (hH : 1 ≤ H) (hδ : 0 < δ) (hscale : 0 < scale)
    (hhull : ∀ a∈S, ∀ b∈S, ∀ q : ℚ, (q.den:ℤ) ≤ H →
      (q:ℝ)∈Icc a b → (q:ℝ)∈S)
    (henclose : ∃ l∈S, ∃ u∈S, l ≤ -scale ∧ scale ≤ u)
    (hsep : ∀ x∈S, ∀ y∈S, x≠y → δ/4 < |x-y|) :
    (H:ℝ) < 4/δ := by
  obtain ⟨l,hl,u,hu,hlow,hupp⟩ := henclose
  have hup : 0 < u := hscale.trans_le hupp
  have hlneg : l < 0 := hlow.trans_lt (neg_neg_of_pos hscale)
  have hHp : 0 < H := lt_of_lt_of_le (by decide : (0:ℤ)<1) hH
  have hHR : (0:ℝ) < H := by exact_mod_cast hHp
  have hzero : (0:ℝ)∈S := by
    exact_mod_cast hhull l hl u hu 0
      (by simpa only [Rat.den_zero,Int.natCast_one] using hH)
      (by simpa only [Rat.cast_zero] using (show (0:ℝ)∈Icc l u from ⟨hlneg.le,hup.le⟩))
  have huwide : δ/4 < u := by
    simpa only [sub_zero,abs_of_pos hup] using hsep u hu 0 hzero hup.ne'
  by_contra hnot
  have hbig : 4/δ ≤ (H:ℝ) := le_of_not_gt hnot
  have hrecip : (1:ℝ)/H ≤ δ/4 := by
    have hh := (div_le_iff₀ hδ).mp hbig
    apply (div_le_iff₀ hHR).mpr
    nlinarith only [hh]
  have hunit : (1:ℝ)/H∈S := by
    have hq := hhull 0 hzero u hu (Rat.divInt 1 H)
      (Int.le_of_dvd hHp (Rat.den_dvd 1 H))
      (by
        rw [Rat.cast_divInt,Int.cast_one]
        exact ⟨(one_div_pos.mpr hHR).le,hrecip.trans huwide.le⟩)
    simpa only [Rat.cast_divInt,Int.cast_one] using hq
  have hsmall := hsep _ hunit _ hzero (one_div_ne_zero hHR.ne')
  rw [sub_zero,abs_of_pos (one_div_pos.mpr hHR)] at hsmall
  exact (not_lt_of_ge hrecip) hsmall

private theorem actual_reference_hull_label_heights
    (S : Finset ℝ) {H : ℤ} {δ scale : ℝ}
    (hH : 1 ≤ H) (hδ : 0 < δ) (hscale : 0 < scale)
    (hhull : ∀ a∈S, ∀ b∈S, ∀ q : ℚ, (q.den:ℤ) ≤ H →
      (q:ℝ)∈Icc a b → (q:ℝ)∈S)
    (henclose : ∃ l∈S, ∃ u∈S, l ≤ -scale ∧ scale ≤ u)
    (hpoints : ∀ z∈S, |z| ≤ scale+1)
    (hlabels : ∀ z∈S,
      (∃ q : ℚ, z=(q:ℝ) ∧ (q.den:ℤ) ≤ H) ∨
      (∃ m n u v : ℤ, z=(m:ℝ)/n ∧ IsCoprime m n ∧ 0 < n ∧
        0 < v ∧ (u:ℝ)/v∈S ∧ |m*v-u*n|=1))
    (hsep : ∀ x∈S, ∀ y∈S, x≠y → δ/4 < |x-y|) :
    (H:ℝ) < 4/δ ∧
    ∀ z∈S, ∃ a b : ℤ, z=(a:ℝ)/b ∧ IsCoprime a b ∧ 0 < b ∧
      (b:ℝ)<4/δ ∧ |(a:ℝ)| ≤ (scale+1)*(4/δ) := by
  have hHbound := actual_reference_hull_order_bound S hH hδ hscale hhull henclose hsep
  refine ⟨hHbound,?_⟩
  have hfinish (z : ℝ) (hz : z∈S) (m n : ℤ)
      (hval : z=(m:ℝ)/n) (hcop : IsCoprime m n) (hn : 0 < n)
      (hnb : (n:ℝ)<4/δ) :
      ∃ a b : ℤ, z=(a:ℝ)/b ∧ IsCoprime a b ∧ 0 < b ∧
        (b:ℝ)<4/δ ∧ |(a:ℝ)| ≤ (scale+1)*(4/δ) := by
    refine ⟨m,n,hval,hcop,hn,hnb,?_⟩
    have hnR : (0:ℝ) < n := by exact_mod_cast hn
    have hnum : (m:ℝ)=z*(n:ℝ) := (div_eq_iff hnR.ne').mp hval.symm
    rw [hnum,abs_mul,abs_of_pos hnR]
    exact mul_le_mul (hpoints z hz) hnb.le hnR.le (by linarith only [hscale])
  intro z hz
  rcases hlabels z hz with ⟨q,hval,hqH⟩ | ⟨m,n,u,v,hval,hcop,hn,hv,hu,hdet⟩
  · apply hfinish z hz q.num q.den
    · simpa only [Rat.cast_def,Int.cast_natCast] using hval
    · exact q.isCoprime_num_den
    · exact_mod_cast q.pos
    · exact (show (q.den:ℝ) ≤ H by exact_mod_cast hqH).trans_lt hHbound
  · exact hfinish z hz m n hval hcop hn
      (separated_reference_parent_denominator_bound S hδ hn hv
        (hval ▸ hz) hu hdet hsep).2

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

private theorem actual_tagged_grid_endpoint_trim
    {ι : Type*} (S : Finset (ι × ℤ)) (Y : Finset ℝ)
    (y x₁ x₂ : ι → ℝ) {M N s B C : ℝ}
    (hN : 0 < N) (hB : 0 ≤ B) (hC : 0 ≤ C)
    (hinj : Set.InjOn (fun i : ι × ℤ => (y i.1,i.2)) (S : Set _))
    (hy : ∀ i∈S, y i.1∈Y)
    (hgeometry : ∀ i∈S, M ≤ x₁ i.1 ∧ x₂ i.1 ≤ 2*M ∧
      x₂ i.1-x₁ i.1 ≤ C*N)
    (hwindow : ∀ i∈S, x₁ i.1 ≤ s+N*(i.2:ℝ) ∧ s+N*(i.2:ℝ) ≤ x₂ i.1) :
    let Inner := S.filter (fun i => M+B ≤ x₁ i.1 ∧ x₂ i.1 ≤ 2*M-B)
    ((S\Inner).card:ℝ) ≤ (Y.card:ℝ)*(2+2*(B+C*N)/N) ∧
    (∀ i∈Inner, M+B ≤ x₁ i.1 ∧ x₂ i.1 ≤ 2*M-B) ∧
    ∀ (w : ι × ℤ → ℝ), (∀ i∈S, w i ≤ N) →
      (∑ i∈S, w i) ≤ (∑ i∈Inner, w i)+(Y.card:ℝ)*(2*N+2*B+2*C*N) := by
  classical
  intro Inner
  have hwidth : 0 ≤ B+C*N := add_nonneg hB (mul_nonneg hC hN.le)
  obtain ⟨Ileft,hIl,_hIll,hIlu⟩ := physical_grid_interval_card
    (N:=N) (Z:=s) (x:=M) (z:=M+B+C*N) hN (by linarith only [hwidth])
  obtain ⟨Iright,hIr,_hIrl,hIru⟩ := physical_grid_interval_card
    (N:=N) (Z:=s) (x:=2*M-B-C*N) (z:=2*M) hN (by linarith only [hwidth])
  have hcover : (S\Inner).card ≤ (Y ×ˢ (Ileft ∪ Iright)).card := by
    apply Finset.card_le_card_of_injOn (fun i : ι × ℤ => (y i.1,i.2))
    · intro i hi
      obtain ⟨hiS,hiNot⟩ := Finset.mem_sdiff.mp hi
      refine Finset.mem_product.mpr ⟨hy i hiS,?_⟩
      have hbad : ¬(M+B ≤ x₁ i.1 ∧ x₂ i.1 ≤ 2*M-B) := by
        intro hgood
        exact hiNot (Finset.mem_filter.mpr ⟨hiS,hgood⟩)
      have hg := hgeometry i hiS
      have hw := hwindow i hiS
      by_cases hl : M+B ≤ x₁ i.1
      · apply Finset.mem_union.mpr
        right
        apply (hIr i.2).mpr
        have hr : 2*M-B < x₂ i.1 := lt_of_not_ge (fun hr => hbad ⟨hl,hr⟩)
        constructor <;> nlinarith only [hg.1,hg.2.1,hg.2.2,hw.1,hw.2,hr]
      · apply Finset.mem_union.mpr
        left
        apply (hIl i.2).mpr
        have hl' : x₁ i.1 < M+B := lt_of_not_ge hl
        constructor <;> nlinarith only [hg.1,hg.2.1,hg.2.2,hw.1,hw.2,hl']
    · intro i hi j hj he
      exact hinj (Finset.mem_sdiff.mp hi).1 (Finset.mem_sdiff.mp hj).1 he
  have hcount : ((S\Inner).card:ℝ) ≤ (Y.card:ℝ)*(2+2*(B+C*N)/N) := by
    have hc : ((S\Inner).card:ℝ) ≤ (Y.card:ℝ)*((Ileft.card:ℝ)+(Iright.card:ℝ)) := by
      exact_mod_cast hcover.trans
        ((Finset.card_product Y (Ileft ∪ Iright)).le.trans
          (Nat.mul_le_mul_left Y.card (Finset.card_union_le Ileft Iright)))
    have hinterval : (Ileft.card:ℝ)+(Iright.card:ℝ) ≤ 2+2*(B+C*N)/N := by
      have hh := add_le_add hIlu hIru
      convert hh using 1
      ring
    exact hc.trans (mul_le_mul_of_nonneg_left hinterval (Nat.cast_nonneg _))
  refine ⟨hcount,(fun i hi => (Finset.mem_filter.mp hi).2),?_⟩
  intro w hw
  have hcost : (∑ i∈S\Inner, w i) ≤ N*((S\Inner).card:ℝ) := by
    calc
      _ ≤ ∑ _i∈S\Inner, N := Finset.sum_le_sum (fun i hi => hw i (Finset.mem_sdiff.mp hi).1)
      _ = _ := by simp only [Finset.sum_const,nsmul_eq_mul,mul_comm]
  have hphysical : N*((S\Inner).card:ℝ) ≤ (Y.card:ℝ)*(2*N+2*B+2*C*N) := by
    have hh := mul_le_mul_of_nonneg_left hcount hN.le
    convert hh using 1
    field_simp
    ring
  have hsplit : (∑ i∈Inner,w i)+(∑ i∈S\Inner,w i)=∑ i∈S,w i :=
    by simpa only [add_comm] using Finset.sum_sdiff (f:=w) (Finset.filter_subset _ _)
  linarith only [hcost,hphysical,hsplit]

private theorem source_integer_window_of_endpoint_buffer
    {M B D z : ℝ} (hB : D+2 ≤ B) (hz : z∈Ioo (M+B) (2*M-B)) :
    let A : ℤ := ⌈M⌉
    let W := 2*M-(A:ℝ)
    M ≤ (A:ℝ) ∧ (A:ℝ)+W=2*M ∧
    ∀ d : ℝ, |d| ≤ D → z-(A:ℝ)+d∈Ioo (1/2:ℝ) (W-1/2) := by
  intro A W
  have hceilLow : M ≤ (A:ℝ) := Int.le_ceil M
  have hceilHigh : (A:ℝ) < M+1 := Int.ceil_lt_add_one M
  refine ⟨hceilLow,by dsimp only [W]; ring,?_⟩
  intro d hd
  have hdb := abs_le.mp hd
  change (1/2:ℝ) < z-(A:ℝ)+d ∧ z-(A:ℝ)+d < 2*M-(A:ℝ)-1/2
  constructor <;> linarith only [hz.1,hz.2,hB,hdb.1,hdb.2,hceilHigh]

private theorem source_buffered_boundary_cost
    {σ c J M N U Y Buffer : ℝ} (hσ : 0 < σ) (hN : 0 < N) (hc : 0 < c) (hU : 0 < U) :
    N*(Y*((24*J/σ)*M/(N*U)+28*σ*U/c+4))+
      Y*(2*N+2*Buffer+2*((14*σ/c)*U)*N) =
      Y*((24*J/σ)*M/U+(56*σ/c)*N*U+6*N+2*Buffer) := by
  field_simp
  ring


/-- One constructed reference system and its actual roots work for EVERY grid
origin and prefix-length family. The choice of references precedes those inputs. -/
theorem positive_difference_constructed_reference_family_uniform_grid_fourier
    {σ c J : ℝ} (hσ : 0 < σ) (hc : 0 < c) (hJ : 0 < J) :
    ∃ C ≥ (1:ℝ), ∀ (F : ℝ → ℝ) (Y : Finset ℝ)
      (N : ℕ) (η T M R U : ℝ),
      1 ≤ N →
      0 < η → η ≤ 1/8 → (∀ y∈Y, y∈Icc (1:ℝ) 2) →
      0 < T → 0 < M → 0 < R → 0 < U → U ≤ R^2 →
      (∀ w, 0 < w → ContDiffAt ℝ ∞ F w) →
      (∀ w∈Icc (1/2:ℝ) 3, ∀ n ≤ 6, |iteratedDeriv (n+1) F w| ≤ J) →
      (∀ w∈Icc (1/2:ℝ) 3, ∀ j,
        c ≤ |TaoTrudgianYang2025.HuxleyModel.tests
          (fun i : Fin 4 => iteratedDeriv (i.val+3) F w) j|) →
      (∀ w∈Icc (1/2:ℝ) 3, iteratedDeriv 4 F w ≤ -c) →
      T*(N:ℝ)*R^2=M^3 → 7*(N:ℝ)+2 ≤ M/4 →
      (3*J/σ)*(6*(N:ℝ)+1)^4 ≤ M*(N:ℝ)*R^2 →
      (3*J/(4*σ))*(6*(N:ℝ)+1)^2 ≤ (N:ℝ)*R^2 →
      3*J ≤ σ*U →
      let f := fun y w => T*(F (w/M)-F (w/M+η*y))/(σ*η)
      let h := fun y w => iteratedDeriv 2 (f y) w/2
    let curvatureScale := 3*J*T/(2*σ*M^2)
    ∃ Href : ℤ, 2 ≤ Href ∧ (Href:ℝ)<4*R^2/U ∧ ∃ Refs : Finset ℝ,
      (∀ q : ℚ, (q.den:ℤ) ≤ Href → |(q:ℝ)| ≤ curvatureScale → (q:ℝ) ∈ Refs) ∧
      (∀ a ∈ Refs, ∀ b ∈ Refs, ∀ q : ℚ, (q.den:ℤ) ≤ Href →
        (q:ℝ) ∈ Icc a b → (q:ℝ) ∈ Refs) ∧
      (∃ l ∈ Refs, ∃ u ∈ Refs, l ≤ -curvatureScale ∧ curvatureScale ≤ u) ∧
      (∀ z ∈ Refs, |z| ≤ curvatureScale+1) ∧
      (∀ z∈Refs, ∃ a b : ℤ, z=(a:ℝ)/b ∧ IsCoprime a b ∧ 0 < b ∧
        (b:ℝ)<4*R^2/U ∧ |(a:ℝ)| ≤ (curvatureScale+1)*(4*R^2/U)) ∧
      (∀ y ∈ Icc (1:ℝ) 2, ∀ x ∈ Icc M (2*M), |h y x| ≤ curvatureScale) ∧
      (∀ z ∈ Refs,
        (∃ q : ℚ, z=(q:ℝ) ∧ (q.den:ℤ) ≤ Href) ∨
        (∃ m n u v : ℤ, z=(m:ℝ)/n ∧ IsCoprime m n ∧ 0 < n ∧
          R^2 ≤ U*(n:ℝ)^2 ∧ 0 < v ∧ v ≤ Href ∧ (u:ℝ)/v ∈ Refs ∧ |m*v-u*n|=1)) ∧
      (∀ x ∈ Refs, ∀ z ∈ Refs, x ≠ z → U/(4*R^2) < |x-z|) ∧
      (∀ y ∈ Icc (1:ℝ) 2, ∀ x ∈ Icc M (2*M),
        ∃ q ∈ Refs, |h y x-q| ≤ 7*U/(4*R^2)) ∧
      (∀ y ∈ Icc (1:ℝ) 2, ∀ q ∈ Refs,
        q ∈ Icc (h y M) (h y (2*M)) →
        ∃ x ∈ Icc M (2*M), h y x=q) ∧
      (∀ a ∈ Refs, ∀ b ∈ Refs, a < b →
        (∀ z ∈ Refs, ¬ (a < z ∧ z < b)) →
        U/(4*R^2) < b-a ∧ b-a ≤ 7*U/(2*R^2) ∧
        (∃ m n u v : ℤ, a=(m:ℝ)/n ∧ b=(u:ℝ)/v ∧
          IsCoprime m n ∧ IsCoprime u v ∧ 0 < n ∧ 0 < v ∧
          R^2 ≤ U*((max n v:ℤ):ℝ)^2) ∧
        (∀ y ∈ Icc (1:ℝ) 2, ∀ x ∈ Icc M (2*M), ∀ z ∈ Icc M (2*M),
          h y x=a → h y z=b → |z-x| ≤ (14*σ/c)*U*N)) ∧
      (∀ a∈Refs, ∀ b∈Refs, a < b →
        (∀ z∈Refs, ¬(a < z ∧ z < b)) →
        ∃ e r v s : ℤ, v*r-e*s=1 ∧
          ((0 < r ∧ (e:ℝ)/r=a) ∨ (r < 0 ∧ (e:ℝ)/r=b)) ∧
          s≠0 ∧ (e:ℝ)/r∈Refs ∧ (v:ℝ)/s∈Refs ∧ R^2 ≤ (r:ℝ)^2*U ∧
          |(r:ℝ)| < 4*R^2/U ∧ |(s:ℝ)| < 4*R^2/U ∧
          |(e:ℝ)| ≤ (curvatureScale+1)*(4*R^2/U) ∧
          |(v:ℝ)| ≤ (curvatureScale+1)*(4*R^2/U)) ∧
    let V := (Y ×ˢ (Refs ×ˢ Refs)).filter (fun i =>
      i.2.1 < i.2.2 ∧ (∀ t∈Refs, ¬(i.2.1 < t ∧ t < i.2.2)) ∧
        i.2.1 < h i.1 (2*M) ∧ h i.1 M < i.2.2)
    let Gref := V.filter (fun i => h i.1 M ≤ i.2.1 ∧ i.2.2 ≤ h i.1 (2*M))
    (V.card:ℝ) ≤ ((12*J/σ)*M/(N*U)+2)*(Y.card:ℝ) ∧
    (V \ Gref).card ≤ 2*Y.card ∧ (Gref.image Prod.fst).card ≤ Y.card ∧
    ∃ x₁ x₂ : ℝ × (ℝ × ℝ) → ℝ,
      (∀ i∈Gref, x₁ i∈Icc M (2*M) ∧ x₂ i∈Icc M (2*M) ∧ x₁ i < x₂ i ∧
        h i.1 (x₁ i)=i.2.1 ∧ h i.1 (x₂ i)=i.2.2 ∧
        U/(4*R^2) ≤ h i.1 (x₂ i)-h i.1 (x₁ i) ∧
        h i.1 (x₂ i)-h i.1 (x₁ i) ≤ 7*U/(2*R^2)) ∧
      (∀ i∈Gref, ∀ j∈Gref, i≠j → i.1=j.1 → x₂ i ≤ x₁ j ∨ x₂ j ≤ x₁ i) ∧
      ∀ (s : ℤ) (H : ℝ → ℤ → ℕ), (∀ y∈Y, ∀ k, H y k ≤ N) →
      letI : DecidableEq (ℝ × (ℝ × ℝ)) := Classical.decEq _
      let t := fun k : ℤ => (s:ℝ)+(N:ℝ)*k
      let L := fun k : ℤ => s+(N:ℤ)*k+2*(N:ℤ)
      let delta := c/(64*σ*R^2)
      let Vbound := 3*J*M/(2*σ*(N:ℝ)*R^2)
      ∀ Buffer : ℝ, 0 ≤ Buffer →
      let Gcore := Gref.filter (fun i => M+Buffer ≤ x₁ i ∧ x₂ i ≤ 2*M-Buffer)
      ∃ (S : (ℝ × (ℝ × ℝ)) → Finset ℤ) (anchor : (ℝ × (ℝ × ℝ)) → ℤ → ℚ) (za : (ℝ × (ℝ × ℝ)) → ℤ → ℝ),
        (∀ i∈Gcore,
          (∀ k : ℤ, k∈(S i) ↔ (x₁ i)+(N:ℝ)/4 ≤ t k ∧ t k ≤ (x₂ i)-(N:ℝ)/4) ∧
        (∀ k∈(S i), (za i) k∈Ioo (x₁ i) (x₂ i) ∧ (h i.1) ((za i) k)=((anchor i) k:ℝ) ∧
          ((anchor i) k:ℝ)∈Ioo ((h i.1) (x₁ i)) ((h i.1) (x₂ i)) ∧
          ((anchor i) k:ℝ)∈Ioo ((h i.1) (t k)-delta) ((h i.1) (t k)+delta) ∧
          ∀ a : ℚ, (a:ℝ)∈Ioo ((h i.1) (t k)-delta) ((h i.1) (t k)+delta) → ((anchor i) k).den ≤ a.den) ∧
        (∀ k∈(S i), |(za i) k-t k| ≤ (N:ℝ)/16) ∧
        (σ/(6*J))*U-3/2 ≤ ((S i).card:ℝ) ∧ ((S i).card:ℝ) ≤ (56*σ/c)*U+1/2 ∧
        (∀ Q : ℕ, 2 ≤ Q →
          let D := 64*σ*R^2/(c*(Q:ℝ))
          (((S i).filter (fun k => Q ≤ ((anchor i) k).den)).card:ℝ) ≤
            4*(Vbound+1)*D^2+D*(2+Real.log (D+1)))) ∧
      ∀ Q : ℕ, 2 ≤ Q → Q ≤ N →
      ∀ (Acut : ℕ) (Bmajor : ℝ), 2 ≤ Acut → Acut ≤ Q → 128*σ ≤ Bmajor →
      let Sall := Gcore.biUnion (fun i => (S i).image (fun k => (i,k)))
      Set.InjOn (fun i : (ℝ × (ℝ × ℝ)) × ℤ => (i.1.1,i.2)) (Sall : Set _) ∧
      let Good := fun i => Acut*(anchor i.1 i.2).den ≤ Q ∧
        Bmajor*R^2 ≤ c*(Q:ℝ)*(anchor i.1 i.2).den
      let G := Sall.filter Good
      let Dlow := Bmajor*R^2/(c*(Q:ℝ))
      let Khigh := Q/Acut+1
      let Dhigh := 64*σ*R^2/(c*(Khigh:ℝ))
      let Dlog := 64*σ*R^2/(c*((Q:ℝ)/Acut))
      let Cost := 4*Vbound*Dhigh^2+3*Dhigh*(2+Real.log (Dhigh+1))+
        Dlow*(2*(Vbound+delta)*Dlow+1)
      ∃ (r : (ℝ × (ℝ × ℝ)) × ℤ → ℚ) (z : (ℝ × (ℝ × ℝ)) × ℤ → ℝ),
      (∀ i∈G, (r i).den ≤ Q ∧ Q ≤ 2*(r i).den ∧
        (anchor i.1 i.2:ℝ) < r i ∧ |(r i:ℝ)-(anchor i.1 i.2:ℝ)| ≤ c/(64*σ*R^2) ∧
        z i∈Icc (za i.1 i.2) (za i.1 i.2+(N:ℝ)/16) ∧
        iteratedDeriv 2 (f i.1.1) (z i)/2=(r i:ℝ)) ∧
      (∀ i∈G, z i∈Ioo (x₁ i.1) (x₂ i.1)) ∧
      (∀ i∈G, z i∈Ioo (M+Buffer) (2*M-Buffer)) ∧
      (∀ i∈G, ∀ d : ℝ, |d|+2 ≤ Buffer →
        z i-(⌈M⌉:ℤ)+d∈Ioo (1/2:ℝ) (2*M-(⌈M⌉:ℤ)-1/2)) ∧
      (768 ≤ Acut → 24576*σ ≤ Bmajor →
        ∀ i∈G, 256*((anchor i.1 i.2).den:ℝ) ≤ (Q:ℝ)/3 ∧
          ∀ eps : ℝ, delta ≤ eps → 256 ≤ 2*eps*((Q:ℝ)/3)*(anchor i.1 i.2).den) ∧
      let m := fun i => round (z i)
      let A := fun i => (L i.2-m i).toNat
      let q := fun i => (r i).den
      let μ := fun i => iteratedDeriv 3 (f i.1.1) (m i)/6
      let ℓ := fun i => deriv (f i.1.1) (m i)
      let U₃ := J/(2*σ*(N:ℝ)*R^2)
      (∀ i∈G, |z i-(m i:ℝ)| ≤ 1/2 ∧
        N ≤ A i ∧ A i ≤ 3*N ∧ m i+(A i:ℤ)=L i.2) ∧
      ∀ (K₀ : ℕ) [NeZero K₀], 63*U₃*(Q:ℝ)*(N:ℝ)^2 ≤ K₀ →
      ∃ v : (ℝ × (ℝ × ℝ)) × ℤ → ℤ, (∀ i∈G, (q i:ℤ) ∣ (r i).num*v i-1) ∧
      let b := fun i (p : Fin 2) => (⌊(q i:ℝ)*ℓ i⌋+(p:ℕ) : ℤ)
      let τ := fun i p => ((b i p:ℝ)-(q i:ℝ)*ℓ i)/2
      let s := fun i => Real.sqrt (2/(3*μ i*(q i:ℝ)))
      let K := fun i => -2*μ i*(s i)^3
      let x := fun i p =>
        (![-(v i:ℝ)*b i p/q i,-(v i:ℝ)/q i,K i,3*K i*τ i p/2] : Fin 4 → ℝ)
      ∃ k : ZMod K₀,
      let FourierCost :=
            (1+Real.log K₀)*
            (∑ i∈G, ∑ p : Fin 2,
              (Real.sqrt (2*(q i:ℝ))/((q i:ℝ)*Real.sqrt (μ i*A i)))*
              ‖∑ j : ZMod K₀,ZMod.stdAddChar (-(j*k))*
                GafniTao.fordAdditiveCharacter (∑ d,x i p d*
                  (![(j.val+1:ℝ),(j.val+1:ℝ)^2,(j.val+1:ℝ)^((3:ℝ)/2),
                    Real.sqrt (j.val+1:ℝ)] : Fin 4 → ℝ) d)‖)+
            ∑ i∈G, (Real.sqrt (A i)*Real.log (2*(A i:ℝ))+1/(μ i*(A i:ℝ)^2))
      let Cerror := (Acut:ℝ)*((6*J/σ)*(64*σ/c)^2+192*σ/c)+
        ((3*J/σ+c/(32*σ))*(Bmajor/c)^2+Bmajor/c)
      (∑ i∈Sall, ‖∑ n∈Finset.Ioc (L i.2) (L i.2+H i.1.1 i.2),(𝐞 (f i.1.1 n):ℂ)‖) ≤ C*(((Gcore.image Prod.fst).card:ℝ)*(N:ℝ)*Cost+FourierCost) ∧
      ((Acut:ℝ)*R ≤ (Q:ℝ) → (N:ℝ)*R ≤ M →
        (∑ i∈Sall, ‖∑ n∈Finset.Ioc (L i.2) (L i.2+H i.1.1 i.2),(𝐞 (f i.1.1 n):ℂ)‖) ≤
          C*(((Gcore.image Prod.fst).card:ℝ)*Cerror*(M*R/Q)*(2+Real.log (Dlog+1))+FourierCost)) ∧
      ∀ (I : Finset ℤ), (∀ j∈I, t j∈Icc M (2*M)) →
      let BoundaryCost := (Y.card:ℝ)*((24*J/σ)*M/U+(56*σ/c)*(N:ℝ)*U+6*(N:ℝ)+2*Buffer)
      (∑ p∈Y ×ˢ I, ‖∑ n∈Finset.Ioc (L p.2) (L p.2+H p.1 p.2),(𝐞 (f p.1 n):ℂ)‖) ≤
        C*(((Gcore.image Prod.fst).card:ℝ)*(N:ℝ)*Cost+FourierCost)+BoundaryCost ∧
      ((Acut:ℝ)*R ≤ (Q:ℝ) → (N:ℝ)*R ≤ M →
        (∑ p∈Y ×ˢ I, ‖∑ n∈Finset.Ioc (L p.2) (L p.2+H p.1 p.2),(𝐞 (f p.1 n):ℂ)‖) ≤
          C*(((Gcore.image Prod.fst).card:ℝ)*Cerror*(M*R/Q)*(2+Real.log (Dlog+1))+FourierCost)+BoundaryCost) := by
  classical
  obtain ⟨C,hC,hentry⟩ := positive_difference_tagged_gap_controlled_complement_fourier hσ hc hJ
  refine ⟨C,hC,?_⟩
  intro F Y N η T M R U hN hη hηmax hy hT hM hR hU hUmax
    hf hbound htests hnegative hphase hbuffer hfourBudget hquadBudget hUlarge
    f h curvatureScale
  have hNp : (0:ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  obtain ⟨Href,hHref,Refs,hseed,hhull,henclose,hpoints,hcurv,hlabels,hsep,hcover,hroots,hgaps⟩ :=
    positive_difference_constructed_reference_system F hσ hc hJ hη hηmax hf hbound htests
      hnegative hT hM hNp hR hU hUmax hphase
  have hscale : 0 < curvatureScale := by dsimp only [curvatureScale]; positivity
  have hsep' : ∀ x∈Refs, ∀ y∈Refs, x≠y → (U/R^2)/4 < |x-y| := by
    intro x hx y hy hne
    convert hsep x hx y hy hne using 1
    ring
  have hheights := actual_reference_hull_label_heights Refs
    (by omega : 1 ≤ Href) (div_pos hU (sq_pos_of_pos hR)) hscale hhull henclose hpoints
    (by
      intro z hz
      rcases hlabels z hz with hseed | ⟨m,n,u,v,hval,hcop,hn,_hnscale,hv,_hvH,hu,hdet⟩
      · exact Or.inl hseed
      · exact Or.inr ⟨m,n,u,v,hval,hcop,hn,hv,hu,hdet⟩)
    hsep'
  have hbudgetEq : 4/(U/R^2)=4*R^2/U := by field_simp
  rw [hbudgetEq] at hheights
  have hcharts : (∀ a∈Refs, ∀ b∈Refs, a < b →
        (∀ z∈Refs, ¬(a < z ∧ z < b)) →
        ∃ e r v s : ℤ, v*r-e*s=1 ∧
          ((0 < r ∧ (e:ℝ)/r=a) ∨ (r < 0 ∧ (e:ℝ)/r=b)) ∧
          s≠0 ∧ (e:ℝ)/r∈Refs ∧ (v:ℝ)/s∈Refs ∧ R^2 ≤ (r:ℝ)^2*U ∧
          |(r:ℝ)| < 4*R^2/U ∧ |(s:ℝ)| < 4*R^2/U ∧
          |(e:ℝ)| ≤ (curvatureScale+1)*(4*R^2/U) ∧
          |(v:ℝ)| ≤ (curvatureScale+1)*(4*R^2/U)) := by
    intro a ha b hb hab hadj
    apply actual_reference_gap_oriented_chart Refs hR hU hscale.le hhull hpoints
      (fun z hz => ?_) hsep ha hb hab hadj (hgaps a ha b hb hab hadj).2.2.1
    rcases hlabels z hz with hseed | ⟨m,n,u,v,hval,hcop,hn,_hnscale,hv,hvH,hu,hdet⟩
    · exact Or.inl hseed
    · exact Or.inr ⟨m,n,u,v,hval,hcop,hn,hv,hvH,hu,hdet⟩
  refine ⟨Href,hHref,hheights.1,Refs,hseed,hhull,henclose,hpoints,hheights.2,
    hcurv,hlabels,hsep,hcover,hroots,hgaps,hcharts,?_⟩
  intro V Gref
  obtain ⟨hpack,hboundary,hphaseCount,x₁,x₂,hgeometry,hdisjoint,hbudget⟩ :=
    positive_difference_reference_family_whole_grid_geometry F Y Refs
      hσ hc hJ hη hηmax hy hf hbound htests hnegative hT hM hNp hR hU hphase
      (fun a ha b hb hne => (hsep a ha b hb hne).le)
      (fun a ha b hb hab hadj => (hgaps a ha b hb hab hadj).2.1)
  refine ⟨hpack,hboundary,hphaseCount,x₁,x₂,hgeometry,hdisjoint,?_⟩
  intro s H hH
  letI : DecidableEq (ℝ × (ℝ × ℝ)) := Classical.decEq _
  intro t L delta Vbound Buffer hBuffer Gcore
  have hcore : Gcore⊆Gref := Finset.filter_subset _ _
  have hyG i (hi : i∈Gref) : i.1∈Y := by
    have hh := Finset.mem_filter.mp hi
    exact (Finset.mem_product.mp (Finset.mem_filter.mp hh.1).1).1
  obtain ⟨S,anchor,za,hS,hforQ⟩ := hentry (ℝ × (ℝ × ℝ)) Gcore F N s
    (fun i k => H i.1 k) η T M R U Prod.fst x₁ x₂
    hN (fun i hi => hH i.1 (hyG i (hcore hi))) hη hηmax (fun i hi => hy i.1 (hyG i (hcore hi)))
    hT hM hR hU hf hbound htests hnegative hphase hbuffer hfourBudget hquadBudget hUlarge
    (fun i hi => (hgeometry i (hcore hi)).1) (fun i hi => (hgeometry i (hcore hi)).2.1)
    (fun i hi j hj hne he => hdisjoint i (hcore hi) j (hcore hj) hne he)
    (fun i hi => (hgeometry i (hcore hi)).2.2.2.2.2)
  have hencloseCurv y (hyY : y∈Y) : ∃ l∈Refs, ∃ u∈Refs, l ≤ h y M ∧ h y (2*M) ≤ u := by
    obtain ⟨l,hl,u,hu,hlo,hhi⟩ := henclose
    have hleft := abs_le.mp (hcurv y (hy y hyY) M ⟨le_rfl,by linarith only [hM]⟩)
    have hright := abs_le.mp (hcurv y (hy y hyY) (2*M) ⟨by linarith only [hM],le_rfl⟩)
    exact ⟨l,hl,u,hu,hlo.trans hleft.1,hright.2.trans hhi⟩
  have hidentify (D : Finset ((ℝ × (ℝ × ℝ)) × ℤ))
      (hD : ∀ i∈D, i.1∈Gref ∧
        x₁ i.1+(N:ℝ)/4 ≤ t i.2 ∧ t i.2 ≤ x₂ i.1-(N:ℝ)/4) :
      Set.InjOn (fun i : (ℝ × (ℝ × ℝ)) × ℤ => (i.1.1,i.2)) (D : Set _) := by
    intro p hp q hq he
    have hpdata := hD p hp
    have hqdata := hD q hq
    have hk : p.2=q.2 := congrArg (fun i : ℝ × ℤ => i.2) he
    have hy : p.1.1=q.1.1 := congrArg (fun i : ℝ × ℤ => i.1) he
    by_cases hpq : p.1=q.1
    · exact Prod.ext hpq hk
    · have hd := hdisjoint p.1 hpdata.1 q.1 hqdata.1 hpq hy
      rw [hk] at hpdata
      rcases hd with hd | hd
      all_goals linarith only [hpdata.2.1,hpdata.2.2,hqdata.2.1,hqdata.2.2,hd,hNp]
  have hgapwidth i (hi : i∈Gref) : x₂ i-x₁ i ≤ ((14*σ/c)*U)*(N:ℝ) := by
    have hg := hgeometry i hi
    have hgap : U/(4*R^2) ≤ h i.1 (x₂ i)-h i.1 (x₁ i) ∧
        h i.1 (x₂ i)-h i.1 (x₁ i) ≤ 7*U/(2*R^2) := hg.2.2.2.2.2
    have hpos : 0 ≤ U/(4*R^2) := by positivity
    have hh := positive_difference_reference_preimage_width F hσ hc hη hηmax
      (hy i.1 (hyG i hi)) hf hnegative hT hM hNp hR hphase hg.1 hg.2.1
      (show |h i.1 (x₂ i)-h i.1 (x₁ i)| ≤ 7*U/(2*R^2) from
        (by rw [abs_of_nonneg (hpos.trans hgap.1)]; exact hgap.2))
    exact (le_abs_self _).trans hh
  refine ⟨S,anchor,za,hS,?_⟩
  intro Q hQ hQN Acut Bmajor hAcut hAQ hBmajor Sall
  have hmem p (hp : p∈Sall) : p.1∈Gcore ∧ p.2∈S p.1 := by
    obtain ⟨i,hi,hpi⟩ := Finset.mem_biUnion.mp hp
    obtain ⟨k,hk,rfl⟩ := Finset.mem_image.mp hpi
    exact ⟨hi,hk⟩
  refine ⟨hidentify Sall (fun i hi =>
    ⟨hcore (hmem i hi).1,((hS i.1 (hmem i hi).1).1 i.2).mp (hmem i hi).2⟩),?_⟩
  intro Good G Dlow Khigh Dhigh Dlog Cost
  have hfull (I : Finset ℤ) (hI : ∀ j∈I, t j∈Icc M (2*M)) :
      (∑ p∈Y ×ˢ I, ‖∑ n∈Finset.Ioc (L p.2) (L p.2+H p.1 p.2),(𝐞 (f p.1 n):ℂ)‖) ≤
      (∑ i∈Sall, ‖∑ n∈Finset.Ioc (L i.2) (L i.2+H i.1.1 i.2),(𝐞 (f i.1.1 n):ℂ)‖)+
        (Y.card:ℝ)*((24*J/σ)*M/U+(56*σ/c)*(N:ℝ)*U+6*(N:ℝ)+2*Buffer) := by
    let AllInner := (Gref ×ˢ I).filter (fun i =>
      x₁ i.1+(N:ℝ)/4 ≤ t i.2 ∧ t i.2 ≤ x₂ i.1-(N:ℝ)/4)
    let Retained := AllInner.filter (fun i => M+Buffer ≤ x₁ i.1 ∧ x₂ i.1 ≤ 2*M-Buffer)
    let w := fun i : (ℝ × (ℝ × ℝ)) × ℤ =>
      ‖∑ n∈Finset.Ioc (L i.2) (L i.2+H i.1.1 i.2),(𝐞 (f i.1.1 n):ℂ)‖
    have hdata i (hi : i∈AllInner) : i.1∈Gref ∧
        x₁ i.1+(N:ℝ)/4 ≤ t i.2 ∧ t i.2 ≤ x₂ i.1-(N:ℝ)/4 := by
      have hh := Finset.mem_filter.mp hi
      exact ⟨(Finset.mem_product.mp hh.1).1,hh.2⟩
    have htrim := (actual_tagged_grid_endpoint_trim AllInner Y Prod.fst x₁ x₂
      (M:=M) (N:=(N:ℝ)) (s:=(s:ℝ)) (B:=Buffer) (C:=(14*σ/c)*U)
      hNp hBuffer (by positivity) (hidentify AllInner hdata)
      (fun i hi => hyG i.1 (hdata i hi).1)
      (fun i hi => ⟨(hgeometry i.1 (hdata i hi).1).1.1,
        (hgeometry i.1 (hdata i hi).1).2.1.2,hgapwidth i.1 (hdata i hi).1⟩)
      (by
        intro i hi
        have hh := (hdata i hi).2
        change x₁ i.1 ≤ t i.2 ∧ t i.2 ≤ x₂ i.1
        constructor <;> linarith only [hh.1,hh.2,hNp])).2.2 w (by
          intro i hi
          have hsum : w i ≤ H i.1.1 i.2 := by
            apply (norm_sum_le _ _).trans_eq
            simp
          exact hsum.trans (Nat.cast_le.mpr (hH i.1.1 (hyG i.1 (hdata i hi).1) i.2)))
    have hsub : Retained⊆Sall := by
      intro i hi
      have hh := Finset.mem_filter.mp hi
      have hd := hdata i hh.1
      have hiCore : i.1∈Gcore := Finset.mem_filter.mpr ⟨hd.1,hh.2⟩
      exact Finset.mem_biUnion.mpr ⟨i.1,hiCore,
        Finset.mem_image.mpr ⟨i.2,((hS i.1 hiCore).1 i.2).mpr hd.2,rfl⟩⟩
    have hsum : (∑ i∈Retained,w i) ≤ ∑ i∈Sall,w i :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => norm_nonneg _)
    have hgs := (hbudget (s:ℝ) I hI hencloseCurv).2 L H
      (fun y hyY j _ => Nat.cast_le.mpr (hH y hyY j))
    have he := source_buffered_boundary_cost (σ:=σ) (J:=J) (M:=M)
      (Y:=(Y.card:ℝ)) (Buffer:=Buffer) hσ hNp hc hU
    change (∑ i∈AllInner,w i) ≤ (∑ i∈Retained,w i)+_ at htrim
    change (∑ p∈Y ×ˢ I, _) ≤ (∑ i∈AllInner,w i)+_ at hgs
    change (∑ p∈Y ×ˢ I, _) ≤ (∑ i∈Sall,w i)+_
    linarith only [hgs,htrim,hsum,he]
  obtain ⟨r,z,hr,hzin,hdense,hround,hmodes⟩ := hforQ Q hQ hQN Acut Bmajor hAcut hAQ hBmajor
  have hzBuffer i (hi : i∈G) : z i∈Ioo (M+Buffer) (2*M-Buffer) := by
    have hc := (Finset.mem_filter.mp (hmem i (Finset.mem_filter.mp hi).1).1).2
    have hz := hzin i hi
    exact ⟨hc.1.trans_lt hz.1,hz.2.trans_le hc.2⟩
  refine ⟨r,z,hr,hzin,hzBuffer,?_,hdense,?_⟩
  · intro i hi d hd
    exact (source_integer_window_of_endpoint_buffer hd (hzBuffer i hi)).2.2 d le_rfl
  intro m A q μ ℓ U₃
  refine ⟨hround,?_⟩
  intro K₀ inst hK₀
  obtain ⟨v,hv,k,hraw,hnorm⟩ := hmodes K₀ hK₀
  refine ⟨v,hv,?_⟩
  intro b τ sPhase K x
  refine ⟨k,?_⟩
  intro FourierCost Cerror
  refine ⟨hraw,hnorm,?_⟩
  intro I hI BoundaryCost
  have hs := hfull I hI
  refine ⟨hs.trans (add_le_add hraw le_rfl),?_⟩
  intro hRQ hNR
  exact hs.trans (add_le_add (hnorm hRQ hNR) le_rfl)

/-- One actual reference system controls every buffered good grid family.
The core twelfth-power estimate has no discarded-block M/U boundary charge. -/
theorem eventually_positive_difference_uniform_reference_core_physical_sieve
    {σsrc csrc Usrc σ εloss : ℝ}
    (hσsrc : 0 < σsrc) (hcsrc : 0 < csrc) (hUsrc : 0 < Usrc)
    (hσ : 0 < σ) (hεloss : 0 < εloss)
    (hanchorBudget : csrc ≤ 4*modelPhaseThirdLower σ*σsrc/(σ*(σ+1)+3)) :
    let κ := modelPhaseThirdLower σ
    let Ratio := 18*Usrc^2/(σsrc*csrc*κ)
    let L := max (8*Ratio^2)
      (32*(modelPhaseJetCoefficient σ 3+1)*(3*Usrc/σsrc)/κ^2)
    ∃ Csrc η₀ a Cupper Clower Dupper Dlower C Dtype : ℝ,
      1 ≤ Csrc ∧ 0 < η₀ ∧ η₀ ≤ 1/8 ∧ 0 < a ∧
      0 < Cupper ∧ 0 < Clower ∧ 0 < Dupper ∧ 0 < Dlower ∧ 0 < C ∧ 0 < Dtype ∧
    ∀ {θ : ℝ}, 0 < θ → θ ≤ 1/24 → θ ≤ 1/(8*(L+3)) →
    ∀ᶠ T : ℝ in Filter.atTop, ∀ (Fsrc : ℝ → ℝ) (Y : Finset ℝ)
      (Q K₀ N Uref : ℕ) [NeZero K₀] (R Jsep : ℝ) {η M δ Bcut Bselect : ℝ},
    0 < η → η ≤ η₀ → 0 < T → 2 ≤ N →
    1 ≤ R → R ≤ M → 0 ≤ δ → δ ≤ min κ 1 →
    0 < Jsep → Jsep ≤ M →
    (∀ y ∈ Y, y ∈ Icc (1:ℝ) 2) →
    (∀ y ∈ Y, ∀ z ∈ Y, y ≠ z → 1 ≤ Jsep*|y-z|) →
    (∀ w, 0 < w → ContDiffAt ℝ ∞ Fsrc w) →
    (∀ w ∈ Icc (1/2:ℝ) 3, ∀ n ≤ 6, |iteratedDeriv (n+1) Fsrc w| ≤ Usrc) →
    (∀ w ∈ Icc (1/2:ℝ) 3, ∀ j,
      csrc ≤ |HuxleyModel.tests (fun i : Fin 4 => iteratedDeriv (i.val+3) Fsrc w) j|) →
    (∀ w ∈ Icc (1/2:ℝ) 3, iteratedDeriv 4 Fsrc w ≤ -csrc) →
    (∀ y ∈ Y, Expdb.IsApproximateModelPhaseFunction
      (fun u => (Fsrc u-Fsrc (u+η*y))/(σsrc*η)) σ 4 δ) →
    T*(N:ℝ)*R^2 = M^3 →
    7*(N:ℝ)+2 ≤ M/4 →
    (3*Usrc/σsrc)*(6*(N:ℝ)+1)^4 ≤ M*(N:ℝ)*R^2 →
    (3*Usrc/(4*σsrc))*(6*(N:ℝ)+1)^2 ≤ (N:ℝ)*R^2 →
    3*Usrc ≤ σsrc*(Uref:ℝ) →
    63*(Usrc/(2*σsrc*(N:ℝ)*R^2))*(Q:ℝ)*(N:ℝ)^2 ≤ K₀ →
    (Q:ℝ)*(N:ℝ) ≤ (K₀:ℝ)*R^2 →
    (N:ℝ)^4 ≤ M*R^3*(Real.log T)^((3:ℝ)/2) →
    1 ≤ Uref → 0 < Bcut →
    2+168/κ ≤ Bselect → 7*Bcut ≤ κ*Bselect →
    Bselect^2*(Uref:ℝ)^3*R^2 ≤ (N:ℝ)^2 →
    (Uref:ℝ) ≤ ((N:ℝ)/(Q:ℝ))^((2:ℝ)/3)/Bselect →
    ((N:ℝ)/(Q:ℝ))^((2:ℝ)/3)/(2*Bselect) ≤ (Uref:ℝ) →
    (N:ℝ)^10 ≤ M^3*R^7 →
    Q ≤ N → (N:ℝ)^2 ≤ M → (Uref:ℝ) ≤ R^2 →
    768*R ≤ (Q:ℝ) → (N:ℝ)*R ≤ M →
    let Cphys := σ*(σ+1)+1
    let c := κ/6
    let J := Cphys/6
    let B := max 1 (max (2*Real.sqrt J) (8*J*Real.sqrt J/(3*c)))
    B*R^2/(N:ℝ)^2 ≤ 1/2 →
    (N:ℝ) ≤ R^2 → R ≤ (N:ℝ) → (N:ℝ)^3 ≤ M*R^2 →
    2*R^2 ≤ (Q:ℝ)*(N:ℝ) →
    let Vscale := (Uref:ℝ)^((3:ℝ)/2)
    let lambda := csrc*κ*T/(12*Usrc*M^2)
    let Uband := (3*Usrc/σsrc)*T/(2*M^2)
    let ChartCap := (4/a+3)*((6*Usrc/σsrc)/a+3)*((4*σsrc/csrc)/a+3)
    let NarrowCap := (4/θ+3)*(72*Usrc^2/(σsrc*csrc*κ*θ)+3)
    let Cap := 3*ChartCap*NarrowCap
    let μ₀ := csrc*T/(12*σsrc*M^3)
    let U₀ := Usrc*T/(2*σsrc*M^3)
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
    let AupperConst := 2*Cupper*(Cthird+1)*1^2/(κ*Lunit^3)
    let BupperConst := Cupper*(Cthird+1)*1^2/Lunit^2+Dupper*(B+1)*1^2/4
    let AlowerConst := 8*Clower*(Cthird+1)/(κ*Lunit^3)
    let BlowerConst := 4*Clower*(Cthird+1)/Lunit^2+Dlower*(B+1)
    let DupperConst := θ*(3*Usrc/σsrc)*1/2
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

    let Buffer := (56*(Uref:ℝ)/κ)*(N:ℝ)+(N:ℝ)/(Cphys+2)+2
    let Dlog := 64*σsrc*R^2/(csrc*((Q:ℝ)/768))
    let Cerror := (768:ℝ)*((6*Usrc/σsrc)*(64*σsrc/csrc)^2+192*σsrc/csrc)+
      ((3*Usrc/σsrc+csrc/(32*σsrc))*((24576*σsrc)/csrc)^2+(24576*σsrc)/csrc)
    let Major := (Y.card:ℝ)*Cerror*(M*R/(Q:ℝ))*(2+Real.log (Dlog+1))
    let Error := (Y.card:ℝ)*(M/(N:ℝ)+1)*
      (Real.sqrt (3*(N:ℝ))*Real.log (6*(N:ℝ))+12*σsrc*R^2/(csrc*(N:ℝ)))
    let FamilyBound := (144*Usrc/(csrc*κ))^6*(R^2/(Q:ℝ))^6*
      C*(K₀:ℝ)^((12:ℝ)+εloss)*Cap^11*(10*(Y.card:ℝ)*(M/(N:ℝ)))^10*
        (Vscale*Dtype*(Y.card:ℝ)*(M/(N:ℝ))*(1+Δtype*Jsep)+
          (Y.card:ℝ)^2*(Vscale*(Kupper+Klower)+Klarge)*T^εloss)
    let f := fun y w => T*(Fsrc (w/M)-Fsrc (w/M+η*y))/(σsrc*η)
    let h := fun y w => iteratedDeriv 2 (f y) w/2
    ∃ Refs : Finset ℝ,
      (∀ a ∈ Refs, ∀ b ∈ Refs, a ≠ b → (Uref:ℝ)/(4*R^2) ≤ |a-b|) ∧
      (∀ a ∈ Refs, ∀ b ∈ Refs, a < b → (∀ q ∈ Refs,¬(a < q ∧ q < b)) →
        b-a ≤ 7*(Uref:ℝ)/(2*R^2)) ∧
      (∀ y ∈ Y, ∃ l ∈ Refs, ∃ u ∈ Refs, l ≤ h y M ∧ h y (2*M) ≤ u) ∧
      (∀ y ∈ Y, ∀ q ∈ Refs, q ∈ Icc (h y M) (h y (2*M)) →
        ∃ z ∈ Icc M (2*M), h y z = q) ∧
      ∀ (sgrid : ℤ) (Hlen : ℝ → ℤ → ℕ), (∀ y ∈ Y, ∀ k, Hlen y k ≤ N) →
      let Lgrid := fun k : ℤ => sgrid+(N:ℤ)*k+2*(N:ℤ)
      let Good : ℝ × ℤ → Prop := fun p =>
        ∃ a ∈ Refs, ∃ b ∈ Refs, a < b ∧ (∀ q ∈ Refs,¬(a < q ∧ q < b)) ∧
          ∃ z₁ z₂ : ℝ, z₁ ∈ Icc M (2*M) ∧ z₂ ∈ Icc M (2*M) ∧
            h p.1 z₁ = a ∧ h p.1 z₂ = b ∧ M+Buffer ≤ z₁ ∧ z₂ ≤ 2*M-Buffer ∧
            z₁+(N:ℝ)/4 ≤ (sgrid:ℝ)+(N:ℝ)*p.2 ∧
              (sgrid:ℝ)+(N:ℝ)*p.2 ≤ z₂-(N:ℝ)/4
      ∀ Pcore : Finset (ℝ × ℤ), (∀ p ∈ Pcore, p.1 ∈ Y ∧ Good p) →
      (∑ p ∈ Pcore, ‖∑ n ∈ Finset.Ioc (Lgrid p.2) (Lgrid p.2+Hlen p.1 p.2),
        (𝐞 (f p.1 n):ℂ)‖)^12 ≤
        2^11*((Csrc*(Major+Error))^12+
          (Csrc*(1+Real.log K₀))^12*FamilyBound)
 := by
  classical
  intro κ Ratio L
  obtain ⟨Csrc,hCsrc,hsource⟩ :=
    positive_difference_constructed_reference_family_uniform_grid_fourier hσsrc hcsrc hUsrc
  obtain ⟨η₀,a,Cupper,Clower,Dupper,Dlower,C,Dtype,
      hη₀,hηcap,ha,hCU,hCL,hDU,hDL,hC,hDtype,hphysical⟩ :=
    eventually_positive_difference_actual_family_physical_sieve
      hσsrc hcsrc hUsrc (by norm_num : (0:ℝ) < 1) hσ hεloss
  refine ⟨Csrc,η₀,a,Cupper,Clower,Dupper,Dlower,C,Dtype,
    hCsrc,hη₀,hηcap,ha,hCU,hCL,hDU,hDL,hC,hDtype,?_⟩
  intro θ hθ hθmax hθaction
  let Jref := σ*Usrc/σsrc
  have hJref : 0 ≤ Jref := by dsimp only [Jref]; positivity
  have hθaction' :
      θ ≤ 1/(8*((max (8*(18*Usrc^2*1/(σsrc*csrc*κ))^2)
        (32*(modelPhaseJetCoefficient σ 3+1)*(3*Usrc/σsrc)*1/κ^2))+3)) := by
    simpa only [mul_one] using hθaction
  filter_upwards [hphysical hJref hθ hθmax hθaction'] with T hfamily
  intro Fsrc Y Q K₀ N Uref instK R Jsep η M δ Bcut Bselect
    hη hηsmall hT hNtwo hR hRM hδzero hδ hJsep hJM hy hsepY
    hreg hjets htests hnegative hmodels hscale hpad hquartic hquad hUlarge
    hsourceMesh hmesh hregime hUref hBcut hBselectSize hcutMargin hselectedWrap
    hselectedUpper hUlo hscaleTen hQN hNsqM hUR hstrongRQ hNRM
    Cphys c J B hsmall hNR hRN hNcube hminscale
    Vscale lambda Uband ChartCap NarrowCap Cap μ₀ U₀ Δtype
    C₂ C₃ Ct Cc Δ Ccurv D Kres Esize Dbase Tbase hsize hD hΔ hBsize
    Lunit Gamma Cthird AupperConst BupperConst AlowerConst BlowerConst
    DupperConst DlowerConst CostUpper CostLower Cpack Cfirst Cgap Cmain Ctail
    Kupper Klower Klarge Buffer Dlog Cerror Major Error FamilyBound f h
  have hκ : 0 < κ := modelPhaseThirdLower_pos hσ
  have hN : 0 < N := by omega
  have hNreal : (2:ℝ) ≤ N := by exact_mod_cast hNtwo
  have hNp : (0:ℝ) < N := Nat.cast_pos.mpr hN
  have hMtwo : 2 ≤ M := by nlinarith only [hNreal,hNsqM]
  have hM : 0 < M := by linarith only [hMtwo]
  have hNM : (N:ℝ) ≤ M := by nlinarith only [hNreal,hNsqM]
  have hRp : 0 < R := zero_lt_one.trans_le hR
  have hUp : (0:ℝ) < Uref := by exact_mod_cast (show 0 < Uref by omega)
  have hQbig : 768 ≤ Q := by
    have hh : (768:ℝ) ≤ Q := by linarith only [hR,hstrongRQ]
    exact_mod_cast hh
  have hQ : 0 < Q := by omega
  have hQtwo : 2 ≤ Q := by omega
  have hRQ : R ≤ (Q:ℝ) := by nlinarith only [hR,hstrongRQ]
  have hCphys : 0 < Cphys := by dsimp only [Cphys]; positivity
  have hBuffer : 0 ≤ Buffer := by dsimp only [Buffer]; positivity
  have hVscale : 1 ≤ Vscale :=
    Real.one_le_rpow (by exact_mod_cast hUref) (by norm_num)
  have hsourceData := hsource Fsrc Y N η T M R (Uref:ℝ)
    (by omega) hη (hηsmall.trans hηcap) hy hT hM hRp hUp hUR
    hreg hjets htests hnegative hscale hpad hquartic hquad hUlarge
  obtain ⟨Href,hHref,hHrefHeight,Refs,hseed,hhull,henclose,hpoints,hheights,
    hcurv,hlabels,hRefSep,hcover,hroots,hgaps,hcharts,hrest⟩ := hsourceData
  let Vref := (Y ×ˢ (Refs ×ˢ Refs)).filter (fun i =>
    i.2.1 < i.2.2 ∧ (∀ t ∈ Refs,¬(i.2.1 < t ∧ t < i.2.2)) ∧
      i.2.1 < h i.1 (2*M) ∧ h i.1 M < i.2.2)
  let Gref := Vref.filter (fun i => h i.1 M ≤ i.2.1 ∧ i.2.2 ≤ h i.1 (2*M))
  obtain ⟨hpack,hboundary,hphaseCount,x₁,x₂,hgeometry,hdisjoint,hgrid⟩ := hrest
  have hencloseCurv y (hyY : y ∈ Y) : ∃ l ∈ Refs, ∃ u ∈ Refs,
      l ≤ h y M ∧ h y (2*M) ≤ u := by
    obtain ⟨l,hl,u,hu,hlo,hhi⟩ := henclose
    have hleft := abs_le.mp (hcurv y (hy y hyY) M ⟨le_rfl,by linarith only [hM]⟩)
    have hright := abs_le.mp (hcurv y (hy y hyY) (2*M) ⟨by linarith only [hM],le_rfl⟩)
    exact ⟨l,hl,u,hu,hlo.trans hleft.1,hright.2.trans hhi⟩
  refine ⟨Refs,(fun a ha b hb hab => (hRefSep a ha b hb hab).le),
    (fun a ha b hb hab hadj => (hgaps a ha b hb hab hadj).2.1),
    hencloseCurv,(fun y hyY => hroots y (hy y hyY)),?_⟩
  intro sgrid Hlen hHlen Lgrid CoreGood Pcore hCoreData
  letI : DecidableEq (ℝ × (ℝ × ℝ)) := Classical.decEq _
  let Gcore := Gref.filter (fun i => M+Buffer ≤ x₁ i ∧ x₂ i ≤ 2*M-Buffer)
  obtain ⟨S0,anchor0,za0,hS0,hforQ⟩ := hgrid sgrid Hlen hHlen Buffer hBuffer
  let Sall := Gcore.biUnion (fun i => (S0 i).image (fun k => (i,k)))
  let Good := fun i : (ℝ × (ℝ × ℝ)) × ℤ =>
    768*(anchor0 i.1 i.2).den ≤ Q ∧
      (24576*σsrc)*R^2 ≤ csrc*(Q:ℝ)*(anchor0 i.1 i.2).den
  let Gtag := Sall.filter Good
  obtain ⟨hinj,ratz,z0,hrat,hzin,hbuffer,hlocal,hdense,hround,hmodes⟩ :=
    hforQ Q hQtwo hQN 768 (24576*σsrc) (by norm_num) hQbig
      (by linarith only [hσsrc])
  let Nlen0 := fun i => (Lgrid i.2-round (z0 i)).toNat
  obtain ⟨v0,hv0,k0,_hraw,hnorm,_hwhole⟩ := hmodes K₀ hsourceMesh
  have hmem i (hi : i ∈ Gtag) : i.1 ∈ Gcore ∧ i.2 ∈ S0 i.1 := by
    have hall : i ∈ Sall := (Finset.mem_filter.mp hi).1
    obtain ⟨j,hj,hiimage⟩ := Finset.mem_biUnion.mp hall
    obtain ⟨k,hk,he⟩ := Finset.mem_image.mp hiimage
    cases he
    exact ⟨hj,hk⟩
  have hfull i (hi : i ∈ Gtag) : i.1 ∈ Gref := (Finset.mem_filter.mp (hmem i hi).1).1
  have hdata i (hi : i ∈ Gtag) :
      i.1.1 ∈ Y ∧ i.1.2.1 ∈ Refs ∧ i.1.2.2 ∈ Refs ∧ i.1.2.1 < i.1.2.2 ∧
        ∀ t ∈ Refs,¬(i.1.2.1 < t ∧ t < i.1.2.2) := by
    have hv := Finset.mem_filter.mp (Finset.mem_filter.mp (hfull i hi)).1
    have hp := Finset.mem_product.mp hv.1
    exact ⟨hp.1,(Finset.mem_product.mp hp.2).1,
      (Finset.mem_product.mp hp.2).2,hv.2.1,hv.2.2.1⟩
  let tag := fun i : (ℝ × (ℝ × ℝ)) × ℤ => (i.1.1,i.2)
  let P := Gtag.image tag
  have hinjG : Set.InjOn tag (Gtag : Set _) :=
    hinj.mono (by intro i hi; exact (Finset.mem_filter.mp hi).1)
  obtain ⟨pull,hright,hleft,hcardP,hsumP,hsumParity⟩ :=
    actual_source_index_transport Gtag hinjG
  have hphase p (hp : p ∈ P) : (pull p).1.1 = p.1 :=
    congrArg (fun q : ℝ × ℤ => q.1) (hright p hp).2
  have hblock p (hp : p ∈ P) : (pull p).2 = p.2 :=
    congrArg (fun q : ℝ × ℤ => q.2) (hright p hp).2
  have hlabelsP p (hp : p ∈ P) : p.1 ∈ Y := by
    rw [←hphase p hp]
    exact (hdata (pull p) (hright p hp).1).1
  let z := fun p => z0 (pull p)
  let rat := fun p => ratz (pull p)
  let v := fun p => v0 (pull p)
  let Nlen := fun p => Nlen0 (pull p)
  let anchor := fun p => anchor0 (pull p).1 (pull p).2
  let gap := fun p => (pull p).1.2
  have hz p (hp : p ∈ P) : z p ∈ Icc M (2*M) := by
    have hh := hbuffer (pull p) (hright p hp).1
    exact ⟨by linarith only [hh.1,hBuffer],by linarith only [hh.2,hBuffer]⟩
  have hden p (hp : p ∈ P) : (rat p).den ≤ Q ∧ Q ≤ 2*(rat p).den :=
    ⟨(hrat (pull p) (hright p hp).1).1,(hrat (pull p) (hright p hp).1).2.1⟩
  have hinv p (hp : p ∈ P) : ((rat p).den:ℤ) ∣ (rat p).num*v p-1 :=
    hv0 (pull p) (hright p hp).1
  have hlevel p (hp : p ∈ P) : iteratedDeriv 2 (f p.1) (z p)/2 = (rat p:ℝ) := by
    rw [←hphase p hp]
    exact (hrat (pull p) (hright p hp).1).2.2.2.2.2
  have hgeomP p (hp : p ∈ P) :
      N ≤ Nlen p ∧ Nlen p ≤ 3*N ∧
        round (z p)+(Nlen p:ℤ) = sgrid+(N:ℤ)*p.2+2*(N:ℤ) := by
    have hh := hround (pull p) (hright p hp).1
    refine ⟨hh.2.1,hh.2.2.1,?_⟩
    change round (z0 (pull p))+(Nlen0 (pull p):ℤ) = Lgrid p.2
    rw [←hblock p hp]
    exact hh.2.2.2
  have hgridP p (hp : p ∈ P) :
      M ≤ (sgrid:ℝ)+(N:ℝ)*p.2 ∧ (sgrid:ℝ)+(N:ℝ)*p.2 ≤ 2*M := by
    have hm := hmem (pull p) (hright p hp).1
    have ht := ((hS0 (pull p).1 hm.1).1 _).mp hm.2
    have hg := hgeometry (pull p).1 (hfull (pull p) (hright p hp).1)
    rw [hblock p hp] at ht
    exact ⟨by linarith only [ht.1,hg.1.1,hNp],
      by linarith only [ht.2,hg.2.1.2,hNp]⟩
  have hminor p (hp : p ∈ P) :
      1 ≤ Nlen p ∧ (rat p).den ≤ Nlen p ∧
        1 ≤ (iteratedDeriv 3 (f p.1) (round (z p))/6)*((rat p).den:ℝ)^2*Nlen p ∧
      7*((iteratedDeriv 3 (f p.1) (round (z p))/6)*
        ((rat p).den:ℝ)*(Nlen p:ℝ)^2) ≤ K₀ := by
    have hg := (Finset.mem_filter.mp (hright p hp).1).2
    have hcut : 2*(anchor p).den ≤ Q :=
      (Nat.mul_le_mul_right _ (show 2 ≤ 768 by decide)).trans hg.1
    have hmajor : 128*σsrc*R^2 ≤ csrc*(Q:ℝ)*(anchor p).den := by
      have hh : 128*σsrc ≤ 24576*σsrc := by linarith only [hσsrc]
      exact (mul_le_mul_of_nonneg_right hh (sq_nonneg R)).trans hg.2
    exact actual_source_dyadic_cubic_admissibility Fsrc
      hσsrc hcsrc hUsrc hη (hηsmall.trans hηcap) (hy p.1 (hlabelsP p hp))
      hreg hjets hnegative hMtwo (by omega) hRp (hz p hp) hscale hQN
      (hden p hp).1 (hden p hp).2 hcut hmajor
      (hgeomP p hp).1 (hgeomP p hp).2.1 hsourceMesh

  let Gaps := (Refs ×ˢ Refs).filter (fun ab =>
    ab.1 < ab.2 ∧ ∀ t ∈ Refs,¬(ab.1 < t ∧ t < ab.2))
  have hgapData ab (hab : ab ∈ Gaps) :
      ab.1 ∈ Refs ∧ ab.2 ∈ Refs ∧ ab.1 < ab.2 ∧ ∀ t ∈ Refs,¬(ab.1 < t ∧ t < ab.2) := by
    have hh := Finset.mem_filter.mp hab
    exact ⟨(Finset.mem_product.mp hh.1).1,(Finset.mem_product.mp hh.1).2,hh.2⟩
  have hgapMem p (hp : p ∈ P) : gap p ∈ Gaps := by
    have hh := hdata (pull p) (hright p hp).1
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_product.mpr ⟨hh.2.1,hh.2.2.1⟩,hh.2.2.2⟩
  have hchartChoice (ab : ℝ × ℝ) : ∃ e r v s : ℤ, ab ∈ Gaps →
      v*r-e*s = 1 ∧ ((0 < r ∧ (e:ℝ)/r = ab.1) ∨ (r < 0 ∧ (e:ℝ)/r = ab.2)) ∧
      s ≠ 0 ∧ (e:ℝ)/r ∈ Refs ∧ (v:ℝ)/s ∈ Refs ∧ R^2 ≤ (r:ℝ)^2*(Uref:ℝ) ∧
      |(r:ℝ)| < 4*R^2/(Uref:ℝ) ∧ |(s:ℝ)| < 4*R^2/(Uref:ℝ) ∧
      |(e:ℝ)| ≤ (3*Usrc*T/(2*σsrc*M^2)+1)*(4*R^2/(Uref:ℝ)) ∧
      |(v:ℝ)| ≤ (3*Usrc*T/(2*σsrc*M^2)+1)*(4*R^2/(Uref:ℝ)) := by
    by_cases hab : ab ∈ Gaps
    · have hh := hgapData ab hab
      obtain ⟨e,r,v,s,he⟩ := hcharts ab.1 hh.1 ab.2 hh.2.1 hh.2.2.1 hh.2.2.2
      exact ⟨e,r,v,s,fun _ => he⟩
    · exact ⟨0,0,0,0,fun hh => (hab hh).elim⟩
  choose e rRef vRef sRef hchartData using hchartChoice
  have hchart ab (hab : ab ∈ Gaps) : vRef ab*rRef ab-e ab*sRef ab = 1 :=
    (hchartData ab hab).1
  have horientation ab (hab : ab ∈ Gaps) :
      ((0:ℝ) < rRef ab ∧ (e ab:ℝ)/rRef ab = ab.1) ∨
        ((rRef ab:ℝ) < 0 ∧ (e ab:ℝ)/rRef ab = ab.2) := by
    rcases (hchartData ab hab).2.1 with hh | hh
    · exact Or.inl ⟨by exact_mod_cast hh.1,hh.2⟩
    · exact Or.inr ⟨by exact_mod_cast hh.1,hh.2⟩
  have hs ab (hab : ab ∈ Gaps) : sRef ab ≠ 0 := (hchartData ab hab).2.2.1
  have hrefSet ab (hab : ab ∈ Gaps) : (e ab:ℝ)/rRef ab ∈ Refs :=
    (hchartData ab hab).2.2.2.1
  have hparentSet ab (hab : ab ∈ Gaps) : (vRef ab:ℝ)/sRef ab ∈ Refs :=
    (hchartData ab hab).2.2.2.2.1
  have hreferenceDen ab (hab : ab ∈ Gaps) : R^2 ≤ (rRef ab:ℝ)^2*(Uref:ℝ) :=
    (hchartData ab hab).2.2.2.2.2.1
  have hrHeight ab (hab : ab ∈ Gaps) : |(rRef ab:ℝ)| ≤ 4*R^2/(Uref:ℝ) :=
    (hchartData ab hab).2.2.2.2.2.2.1.le
  have hsHeight ab (hab : ab ∈ Gaps) : |(sRef ab:ℝ)| ≤ 4*R^2/(Uref:ℝ) :=
    (hchartData ab hab).2.2.2.2.2.2.2.1.le
  have hheightEq : 3*Usrc*T/(2*σsrc*M^2) = 3*Jref*T/(2*σ*M^2) := by
    dsimp only [Jref]
    field_simp
  have heHeight ab (hab : ab ∈ Gaps) :
      |(e ab:ℝ)| ≤ (3*Jref*T/(2*σ*M^2)+1)*(4*R^2/(Uref:ℝ)) := by
    rw [←hheightEq]
    exact (hchartData ab hab).2.2.2.2.2.2.2.2.1
  have hvHeight ab (hab : ab ∈ Gaps) :
      |(vRef ab:ℝ)| ≤ (3*Jref*T/(2*σ*M^2)+1)*(4*R^2/(Uref:ℝ)) := by
    rw [←hheightEq]
    exact (hchartData ab hab).2.2.2.2.2.2.2.2.2
  have hgapWidth ab (hab : ab ∈ Gaps) : ab.2-ab.1 ≤ 7*(Uref:ℝ)/(2*R^2) := by
    have hh := hgapData ab hab
    exact (hgaps ab.1 hh.1 ab.2 hh.2.1 hh.2.2.1 hh.2.2.2).2.1
  have hsep u (hu : u ∈ Refs) v (hv : v ∈ Refs) (huv : u ≠ v) :
      ((Uref:ℝ)/R^2)/4 < |u-v| := by
    convert hRefSep u hu v hv huv using 1
    ring
  have hwide w (hw : w ∈ Icc M (2*M)) : w ∈ Icc (3*M/4) (9*M/4) := by
    constructor <;> linarith only [hw.1,hw.2,hM]
  have hfamilyGap p (hp : p ∈ P) : (rat p:ℝ) ∈ Icc (gap p).1 (gap p).2 := by
    have hi := (hright p hp).1
    have hg := hgeometry (pull p).1 (hfull (pull p) hi)
    have hm := positive_difference_physical_curvature_strictMono Fsrc
      hσsrc hcsrc hη (hηsmall.trans hηcap) (hy p.1 (hlabelsP p hp))
      hreg hnegative hT hM
    have hl := hm (hwide _ hg.1) (hwide _ (hz p hp)) (hzin (pull p) hi).1
    have hu := hm (hwide _ (hz p hp)) (hwide _ hg.2.1) (hzin (pull p) hi).2
    change iteratedDeriv 2 (f p.1) (x₁ (pull p).1)/2 <
      iteratedDeriv 2 (f p.1) (z p)/2 at hl
    change iteratedDeriv 2 (f p.1) (z p)/2 <
      iteratedDeriv 2 (f p.1) (x₂ (pull p).1)/2 at hu
    rw [hlevel p hp] at hl hu
    have hleftLevel : iteratedDeriv 2 (f p.1) (x₁ (pull p).1)/2 = (gap p).1 := by
      rw [←hphase p hp]
      exact hg.2.2.2.1
    have hrightLevel : iteratedDeriv 2 (f p.1) (x₂ (pull p).1)/2 = (gap p).2 := by
      rw [←hphase p hp]
      exact hg.2.2.2.2.1
    rw [hleftLevel] at hl
    rw [hrightLevel] at hu
    exact ⟨hl.le,hu.le⟩
  let Aphase := fun _y : ℝ => (⌈M⌉:ℤ)
  let Wphase := fun _y : ℝ => 2*M-(⌈M⌉:ℤ)
  let xlocal := fun p : ℝ × ℤ => z p-(Aphase p.1:ℝ)
  let Wide := (56*(Uref:ℝ)/κ)*(N:ℝ)
  let Hshort := (N:ℝ)/(Cphys+2)
  have hWide : 0 ≤ Wide := by dsimp only [Wide]; positivity
  have hHshort : 0 ≤ Hshort := by dsimp only [Hshort]; positivity
  have hx p (hp : p ∈ P) : xlocal p ∈ Ioo (1/2:ℝ) (Wphase p.1-1/2) := by
    have hh := hlocal (pull p) (hright p hp).1 0 (by
      change |(0:ℝ)|+2 ≤ Wide+Hshort+2
      rw [abs_zero]
      linarith only [hWide,hHshort])
    simpa only [add_zero] using hh
  have hwideL p (hp : p ∈ P) : xlocal p-Wide ∈ Ioo (1/2:ℝ) (Wphase p.1-1/2) := by
    have hh := hlocal (pull p) (hright p hp).1 (-Wide) (by
      change |-Wide|+2 ≤ Wide+Hshort+2
      rw [abs_neg,abs_of_nonneg hWide]
      linarith only [hHshort])
    simpa only [sub_eq_add_neg] using hh
  have hwideU p (hp : p ∈ P) : xlocal p+Wide ∈ Ioo (1/2:ℝ) (Wphase p.1-1/2) :=
    hlocal (pull p) (hright p hp).1 Wide (by
      change |Wide|+2 ≤ Wide+Hshort+2
      rw [abs_of_nonneg hWide]
      linarith only [hHshort])
  have hL p (hp : p ∈ P) : xlocal p-Hshort ∈ Ioo (1/2:ℝ) (Wphase p.1-1/2) := by
    have hh := hlocal (pull p) (hright p hp).1 (-Hshort) (by
      change |-Hshort|+2 ≤ Wide+Hshort+2
      rw [abs_neg,abs_of_nonneg hHshort]
      linarith only [hWide])
    simpa only [sub_eq_add_neg] using hh
  have hU p (hp : p ∈ P) : xlocal p+Hshort ∈ Ioo (1/2:ℝ) (Wphase p.1-1/2) :=
    hlocal (pull p) (hright p hp).1 Hshort (by
      change |Hshort|+2 ≤ Wide+Hshort+2
      rw [abs_of_nonneg hHshort]
      linarith only [hWide])
  let ε := κ/(16*(Cphys+2)*R^2)
  have htol : csrc/(64*σsrc*R^2) ≤ ε := by
    have hb : csrc ≤ 4*κ*σsrc/(Cphys+2) := by
      convert hanchorBudget using 1
      dsimp only [Cphys]
      ring
    calc
      csrc/(64*σsrc*R^2) ≤ (4*κ*σsrc/(Cphys+2))/(64*σsrc*R^2) :=
        div_le_div_of_nonneg_right hb (by positivity)
      _ = ε := by dsimp only [ε]; field_simp; ring
  have hanchor p (hp : p ∈ P) : |(anchor p:ℝ)-(rat p:ℝ)| ≤ ε := by
    rw [abs_sub_comm]
    exact ((hrat (pull p) (hright p hp).1).2.2.2.1).trans htol
  have hcut p (hp : p ∈ P) : 256*((anchor p).den:ℝ) ≤ (Q:ℝ)/3 :=
    (hdense (by norm_num) le_rfl (pull p) (hright p hp).1).1
  have hcount p (hp : p ∈ P) : 256 ≤ 2*ε*((Q:ℝ)/3)*(anchor p).den :=
    (hdense (by norm_num) le_rfl (pull p) (hright p hp).1).2 ε htol
  have hmodel p (hp : p ∈ P) : Expdb.IsApproximateModelPhaseFunction
      (fun u => (T/T)*(Fsrc u-Fsrc (u+η*p.1))/(σsrc*η)) σ 4 δ := by
    simpa only [div_self hT.ne',one_mul] using hmodels p.1 (hlabelsP p hp)
  have hseparation p (hp : p ∈ P) q (hq : q ∈ P) (hpq : p.1 ≠ q.1) :
      1 ≤ Jsep*|p.1-q.1| := hsepY p.1 (hlabelsP p hp) q.1 (hlabelsP q hq) hpq
  obtain ⟨hcolor,hphysicalCount,hunweighted,hweighted⟩ :=
    hfamily P Fsrc z rat v Nlen Q K₀ N Vscale R Jsep (fun _ => sgrid)
      (η:=η) (Tsrc:=T) (M:=M) (δ:=δ) (Bcut:=Bcut) (Bselect:=Bselect)
      Uref Refs Gaps Aphase Wphase gap anchor e rRef vRef sRef
      hη hηsmall hT hT hM hδ (by simp only [one_mul,le_refl]) hQ
      (fun p hp => hy p.1 (hlabelsP p hp)) hz hreg hjets htests hden hinv hnegative
      hMtwo hVscale hN hJsep hJM hNM hmesh hgeomP hseparation hmodel hlevel
      (fun p hp => ⟨(hminor p hp).1,(hminor p hp).2.1,(hminor p hp).2.2.1⟩)
      (fun p hp => (hminor p hp).2.2.2)
      hregime hR hRM hscale (fun _ _ => Int.le_ceil M)
      (fun _ _ => by dsimp only [Aphase,Wphase]; linarith only)
      hx hgapMem hchart horientation hBcut hs hrefSet hparentSet hsep hwideL hwideU hUref
      hBselectSize hcutMargin hselectedWrap hreferenceDen hgapWidth hRQ
      hselectedUpper hscaleTen hfamilyGap hgapData (by exact_mod_cast hQN) hNsqM hUR
      hrHeight hsHeight heHeight hvHeight hsmall hNR hRN hNcube hminscale
      hNreal hL hU hanchor hcut hcount hsize hD hΔ hBsize rfl hUlo

  let q0 := fun i => (ratz i).den
  let mu0 := fun i => iteratedDeriv 3 (f i.1.1) (round (z0 i))/6
  let ell0 := fun i => deriv (f i.1.1) (round (z0 i))
  let b0 := fun i (p : Fin 2) => (⌊(q0 i:ℝ)*ell0 i⌋+(p:ℕ) : ℤ)
  let tau0 := fun i p => ((b0 i p:ℝ)-(q0 i:ℝ)*ell0 i)/2
  let dual0 := fun i => -2*mu0 i*(Real.sqrt (2/(3*mu0 i*(q0 i:ℝ))))^3
  let x0 := fun i p =>
    (![-(v0 i:ℝ)*b0 i p/q0 i,-(v0 i:ℝ)/q0 i,
      dual0 i,3*dual0 i*tau0 i p/2] : Fin 4 → ℝ)
  let FourierNorm := fun i p =>
    ‖∑ j : ZMod K₀, ZMod.stdAddChar (-(j*k0))*
      GafniTao.fordAdditiveCharacter (∑ d,x0 i p d*
        (![(j.val+1:ℝ),(j.val+1:ℝ)^2,(j.val+1:ℝ)^((3:ℝ)/2),
          Real.sqrt (j.val+1:ℝ)] : Fin 4 → ℝ) d)‖
  let Wpoint := fun i p => (Real.sqrt (2*(q0 i:ℝ))/
    ((q0 i:ℝ)*Real.sqrt (mu0 i*(Nlen0 i:ℝ))))*FourierNorm i p
  let Wsum := ∑ i ∈ Gtag, ∑ p : Fin 2,Wpoint i p
  let BoundCard := fun y : ℝ =>
    (144*Usrc/(csrc*κ))^6*(R^2/(Q:ℝ))^6*
      C*(K₀:ℝ)^((12:ℝ)+εloss)*Cap^11*(10*y*(M/(N:ℝ)))^10*
        (Vscale*Dtype*y*(M/(N:ℝ))*(1+Δtype*Jsep)+
          y^2*(Vscale*(Kupper+Klower)+Klarge)*T^εloss)
  have hweightedReindexed : Wsum^12 ≤ BoundCard ((P.image Prod.fst).card:ℝ) := by
    have hw := hweighted k0
    have hsum := hsumParity (fun ip => Wpoint ip.1 ip.2)
    change (∑ ip ∈ P ×ˢ (Finset.univ : Finset (Fin 2)),
      Wpoint (pull ip.1) ip.2) = Wsum at hsum
    rw [←hsum]
    convert hw using 1
    · congr 1
      apply Finset.sum_congr rfl
      intro ip hip
      have hp := hphase ip.1 (Finset.mem_product.mp hip).1
      dsimp only [Wpoint,FourierNorm,x0,dual0,tau0,b0,q0,mu0,ell0,z,rat,v,Nlen,Nlen0]
      rw [hp]
    · simp only [BoundCard,κ,Cphys,c,J,B,Vscale,lambda,Uband,ChartCap,NarrowCap,Cap,
        μ₀,U₀,Δtype,C₂,C₃,Ct,Cc,Kres,Lunit,Gamma,Cthird,AupperConst,BupperConst,
        AlowerConst,BlowerConst,DupperConst,DlowerConst,CostUpper,CostLower,
        Cpack,Cfirst,Cgap,Cmain,Ctail,Kupper,Klower,Klarge,mul_one,one_pow]
  have hBselect : 0 < Bselect := by
    have hh : 0 < 2+168/κ := by positivity
    exact hh.trans_le hBselectSize
  have hBoundMono {y₁ y₂ : ℝ} (hy₁ : 0 ≤ y₁) (hy₂ : y₁ ≤ y₂) :
      BoundCard y₁ ≤ BoundCard y₂ :=
    actual_source_family_card_bound_mono Q K₀ N Uref hσsrc hcsrc hUsrc hσ
      hθ ha hCU hCL hDU hDL hC hDtype hT hM hNp hJsep hδzero hBselect hy₁ hy₂
  have hphaseCard : ((P.image Prod.fst).card:ℝ) ≤ Y.card := by
    apply Nat.cast_le.mpr
    apply Finset.card_le_card
    intro y hym
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hym
    exact hlabelsP p hp
  have hW12 : Wsum^12 ≤ FamilyBound :=
    hweightedReindexed.trans (hBoundMono (Nat.cast_nonneg _) hphaseCard)
  let ErrPoint := fun i => Real.sqrt (Nlen0 i)*Real.log (2*(Nlen0 i:ℝ))+
    1/(mu0 i*(Nlen0 i:ℝ)^2)
  let RawError := ∑ i ∈ Gtag,ErrPoint i
  have hError : RawError ≤ Error := by
    have he := (actual_source_grid_completion_error P Y Fsrc z Nlen
      (s:=(sgrid:ℝ)) hσsrc hcsrc hUsrc hη (hηsmall.trans hηcap)
      (by omega) hMtwo hRp hscale hy hlabelsP hgridP hz
      (fun p hp => ⟨(hgeomP p hp).1,(hgeomP p hp).2.1⟩)
      hreg hjets hnegative).2
    have hsum := hsumP ErrPoint
    change (∑ p ∈ P,ErrPoint (pull p)) = RawError at hsum
    rw [←hsum]
    convert he using 1
    apply Finset.sum_congr rfl
    intro p hp
    dsimp only [ErrPoint,mu0,z,Nlen,Nlen0]
    rw [hphase p hp]
  have hCorePhase : ((Gcore.image Prod.fst).card:ℝ) ≤ Y.card := by
    have hs : Gcore⊆Gref := Finset.filter_subset _ _
    exact_mod_cast (Finset.card_le_card (Finset.image_subset_image hs)).trans hphaseCount
  have hDlog : 0 ≤ Dlog := by dsimp only [Dlog]; positivity
  have hCerror : 0 ≤ Cerror := by dsimp only [Cerror]; positivity
  have hlogD : 0 ≤ 2+Real.log (Dlog+1) :=
    add_nonneg (by norm_num) (Real.log_nonneg (by linarith only [hDlog]))
  have hMajor : ((Gcore.image Prod.fst).card:ℝ)*Cerror*(M*R/(Q:ℝ))*
      (2+Real.log (Dlog+1)) ≤ Major := by
    dsimp only [Major]
    gcongr
  have hKpos : 0 < K₀ := NeZero.pos K₀
  have hlogK : 0 ≤ 1+Real.log K₀ :=
    add_nonneg zero_le_one (Real.log_nonneg (by exact_mod_cast hKpos))
  have hWsum : 0 ≤ Wsum := by
    apply Finset.sum_nonneg
    intro i _hi
    apply Finset.sum_nonneg
    intro p _hp
    exact mul_nonneg (div_nonneg (Real.sqrt_nonneg _)
      (mul_nonneg (Nat.cast_nonneg _) (Real.sqrt_nonneg _))) (norm_nonneg _)
  have hCsrcpos : 0 ≤ Csrc := zero_le_one.trans hCsrc
  have hMajorNN : 0 ≤ Major := mul_nonneg
    (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) hCerror)
      (div_nonneg (mul_nonneg hM.le hRp.le) (Nat.cast_nonneg _))) hlogD
  have hErrorNN : 0 ≤ Error := by
    have hlogN : 0 ≤ Real.log (6*(N:ℝ)) :=
      Real.log_nonneg (by linarith only [hNreal])
    clear * - hM hNp hσsrc hcsrc hRp hlogN
    dsimp only [Error]
    positivity

  let Orig := ∑ p ∈ Pcore, ‖∑ n ∈ Finset.Ioc (Lgrid p.2) (Lgrid p.2+Hlen p.1 p.2),
    (𝐞 (f p.1 n):ℂ)‖
  have hOrig : 0 ≤ Orig := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  have hcoreSubset : Pcore ⊆ Sall.image tag := by
    intro p hp
    obtain ⟨hyp,a,ha,b,hb,hab,hadj,z₁,z₂,hz₁,hz₂,hza,hzb,hleft,hright,htleft,htright⟩ :=
      hCoreData p hp
    have hmono : StrictMonoOn (h p.1) (Icc M (2*M)) := by
      apply (positive_difference_physical_curvature_strictMono Fsrc hσsrc hcsrc hη
        (hηsmall.trans hηcap) (hy p.1 hyp) hreg hnegative hT hM).mono
      intro w hw
      constructor <;> linarith only [hw.1,hw.2,hM]
    have hma : h p.1 M ≤ a := by
      rw [←hza]
      exact hmono.monotoneOn ⟨le_rfl,by linarith only [hM]⟩ hz₁ hz₁.1
    have hbm : b ≤ h p.1 (2*M) := by
      rw [←hzb]
      exact hmono.monotoneOn hz₂ ⟨by linarith only [hM],le_rfl⟩ hz₂.2
    let i : ℝ × (ℝ × ℝ) := (p.1,a,b)
    have hi : i ∈ Gref := by
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_filter.mpr ⟨?_,hab,hadj,hab.trans_le hbm,hma.trans_lt hab⟩,
        hma,hbm⟩
      exact Finset.mem_product.mpr ⟨hyp,Finset.mem_product.mpr ⟨ha,hb⟩⟩
    have hg := hgeometry i hi
    have hxeq₁ : x₁ i = z₁ := hmono.injOn hg.1 hz₁ (hg.2.2.2.1.trans hza.symm)
    have hxeq₂ : x₂ i = z₂ := hmono.injOn hg.2.1 hz₂ (hg.2.2.2.2.1.trans hzb.symm)
    have hiCore : i ∈ Gcore := Finset.mem_filter.mpr
      ⟨hi,by rw [hxeq₁,hxeq₂]; exact ⟨hleft,hright⟩⟩
    have hk : p.2 ∈ S0 i := ((hS0 i hiCore).1 p.2).mpr
      (by rw [hxeq₁,hxeq₂]; exact ⟨htleft,htright⟩)
    have himem : (i,p.2) ∈ Sall :=
      Finset.mem_biUnion.mpr ⟨i,hiCore,Finset.mem_image.mpr ⟨p.2,hk,rfl⟩⟩
    exact Finset.mem_image.mpr ⟨(i,p.2),himem,rfl⟩
  have hOrigCore : Orig ≤ ∑ i ∈ Sall,
      ‖∑ n ∈ Finset.Ioc (Lgrid i.2) (Lgrid i.2+Hlen i.1.1 i.2),
        (𝐞 (f i.1.1 n):ℂ)‖ := by
    have hs := Finset.sum_le_sum_of_subset_of_nonneg hcoreSubset
      (f:=fun p => ‖∑ n ∈ Finset.Ioc (Lgrid p.2) (Lgrid p.2+Hlen p.1 p.2),
        (𝐞 (f p.1 n):ℂ)‖) (fun _ _ _ => norm_nonneg _)
    rw [Finset.sum_image hinj] at hs
    exact hs
  have hsourceBound := hOrigCore.trans (hnorm hstrongRQ hNRM)
  change Orig ≤ Csrc*(((Gcore.image Prod.fst).card:ℝ)*Cerror*(M*R/(Q:ℝ))*
    (2+Real.log (Dlog+1))+((1+Real.log K₀)*Wsum+RawError)) at hsourceBound
  let Aterm := Csrc*(Major+Error)
  let Bterm := (Csrc*(1+Real.log K₀))*Wsum
  have hAterm : 0 ≤ Aterm := mul_nonneg hCsrcpos (add_nonneg hMajorNN hErrorNN)
  have hBterm : 0 ≤ Bterm := mul_nonneg (mul_nonneg hCsrcpos hlogK) hWsum
  have hOrigSum : Orig ≤ Aterm+Bterm := by
    calc
      Orig ≤ Csrc*(Major+((1+Real.log K₀)*Wsum+Error)) :=
        hsourceBound.trans
          (mul_le_mul_of_nonneg_left (add_le_add hMajor (add_le_add le_rfl hError)) hCsrcpos)
      _ = Aterm+Bterm := by dsimp only [Aterm,Bterm]; ring
  have hBpower : Bterm^12 ≤ (Csrc*(1+Real.log K₀))^12*FamilyBound := by
    dsimp only [Bterm]
    rw [mul_pow]
    exact mul_le_mul_of_nonneg_left hW12 (pow_nonneg (mul_nonneg hCsrcpos hlogK) 12)
  calc
    Orig^12 ≤ (Aterm+Bterm)^12 := pow_le_pow_left₀ hOrig hOrigSum 12
    _ ≤ 2^11*(Aterm^12+Bterm^12) := add_pow_le hAterm hBterm 12
    _ ≤ _ := mul_le_mul_of_nonneg_left (add_le_add le_rfl hBpower) (by norm_num)

example
    {σ c J : ℝ} (hσ : 0 < σ) (hc : 0 < c) (hJ : 0 < J) :
    ∃ C ≥ (1:ℝ), ∀ (F : ℝ → ℝ) (Y : Finset ℝ)
      (N : ℕ) (η T M R U : ℝ),
      1 ≤ N →
      0 < η → η ≤ 1/8 → (∀ y∈Y, y∈Icc (1:ℝ) 2) →
      0 < T → 0 < M → 0 < R → 0 < U → U ≤ R^2 →
      (∀ w, 0 < w → ContDiffAt ℝ ∞ F w) →
      (∀ w∈Icc (1/2:ℝ) 3, ∀ n ≤ 6, |iteratedDeriv (n+1) F w| ≤ J) →
      (∀ w∈Icc (1/2:ℝ) 3, ∀ j,
        c ≤ |TaoTrudgianYang2025.HuxleyModel.tests
          (fun i : Fin 4 => iteratedDeriv (i.val+3) F w) j|) →
      (∀ w∈Icc (1/2:ℝ) 3, iteratedDeriv 4 F w ≤ -c) →
      T*(N:ℝ)*R^2=M^3 → 7*(N:ℝ)+2 ≤ M/4 →
      (3*J/σ)*(6*(N:ℝ)+1)^4 ≤ M*(N:ℝ)*R^2 →
      (3*J/(4*σ))*(6*(N:ℝ)+1)^2 ≤ (N:ℝ)*R^2 →
      3*J ≤ σ*U →
      let f := fun y w => T*(F (w/M)-F (w/M+η*y))/(σ*η)
      let h := fun y w => iteratedDeriv 2 (f y) w/2
    let curvatureScale := 3*J*T/(2*σ*M^2)
    ∃ Href : ℤ, 2 ≤ Href ∧ (Href:ℝ)<4*R^2/U ∧ ∃ Refs : Finset ℝ,
      (∀ q : ℚ, (q.den:ℤ) ≤ Href → |(q:ℝ)| ≤ curvatureScale → (q:ℝ) ∈ Refs) ∧
      (∀ a ∈ Refs, ∀ b ∈ Refs, ∀ q : ℚ, (q.den:ℤ) ≤ Href →
        (q:ℝ) ∈ Icc a b → (q:ℝ) ∈ Refs) ∧
      (∃ l ∈ Refs, ∃ u ∈ Refs, l ≤ -curvatureScale ∧ curvatureScale ≤ u) ∧
      (∀ z ∈ Refs, |z| ≤ curvatureScale+1) ∧
      (∀ z∈Refs, ∃ a b : ℤ, z=(a:ℝ)/b ∧ IsCoprime a b ∧ 0 < b ∧
        (b:ℝ)<4*R^2/U ∧ |(a:ℝ)| ≤ (curvatureScale+1)*(4*R^2/U)) ∧
      (∀ y ∈ Icc (1:ℝ) 2, ∀ x ∈ Icc M (2*M), |h y x| ≤ curvatureScale) ∧
      (∀ z ∈ Refs,
        (∃ q : ℚ, z=(q:ℝ) ∧ (q.den:ℤ) ≤ Href) ∨
        (∃ m n u v : ℤ, z=(m:ℝ)/n ∧ IsCoprime m n ∧ 0 < n ∧
          R^2 ≤ U*(n:ℝ)^2 ∧ 0 < v ∧ v ≤ Href ∧ (u:ℝ)/v ∈ Refs ∧ |m*v-u*n|=1)) ∧
      (∀ x ∈ Refs, ∀ z ∈ Refs, x ≠ z → U/(4*R^2) < |x-z|) ∧
      (∀ y ∈ Icc (1:ℝ) 2, ∀ x ∈ Icc M (2*M),
        ∃ q ∈ Refs, |h y x-q| ≤ 7*U/(4*R^2)) ∧
      (∀ y ∈ Icc (1:ℝ) 2, ∀ q ∈ Refs,
        q ∈ Icc (h y M) (h y (2*M)) →
        ∃ x ∈ Icc M (2*M), h y x=q) ∧
      (∀ a ∈ Refs, ∀ b ∈ Refs, a < b →
        (∀ z ∈ Refs, ¬ (a < z ∧ z < b)) →
        U/(4*R^2) < b-a ∧ b-a ≤ 7*U/(2*R^2) ∧
        (∃ m n u v : ℤ, a=(m:ℝ)/n ∧ b=(u:ℝ)/v ∧
          IsCoprime m n ∧ IsCoprime u v ∧ 0 < n ∧ 0 < v ∧
          R^2 ≤ U*((max n v:ℤ):ℝ)^2) ∧
        (∀ y ∈ Icc (1:ℝ) 2, ∀ x ∈ Icc M (2*M), ∀ z ∈ Icc M (2*M),
          h y x=a → h y z=b → |z-x| ≤ (14*σ/c)*U*N)) ∧
      (∀ a∈Refs, ∀ b∈Refs, a < b →
        (∀ z∈Refs, ¬(a < z ∧ z < b)) →
        ∃ e r v s : ℤ, v*r-e*s=1 ∧
          ((0 < r ∧ (e:ℝ)/r=a) ∨ (r < 0 ∧ (e:ℝ)/r=b)) ∧
          s≠0 ∧ (e:ℝ)/r∈Refs ∧ (v:ℝ)/s∈Refs ∧ R^2 ≤ (r:ℝ)^2*U ∧
          |(r:ℝ)| < 4*R^2/U ∧ |(s:ℝ)| < 4*R^2/U ∧
          |(e:ℝ)| ≤ (curvatureScale+1)*(4*R^2/U) ∧
          |(v:ℝ)| ≤ (curvatureScale+1)*(4*R^2/U)) ∧
    let V := (Y ×ˢ (Refs ×ˢ Refs)).filter (fun i =>
      i.2.1 < i.2.2 ∧ (∀ t∈Refs, ¬(i.2.1 < t ∧ t < i.2.2)) ∧
        i.2.1 < h i.1 (2*M) ∧ h i.1 M < i.2.2)
    let Gref := V.filter (fun i => h i.1 M ≤ i.2.1 ∧ i.2.2 ≤ h i.1 (2*M))
    (V.card:ℝ) ≤ ((12*J/σ)*M/(N*U)+2)*(Y.card:ℝ) ∧
    (V \ Gref).card ≤ 2*Y.card ∧ (Gref.image Prod.fst).card ≤ Y.card ∧
    ∃ x₁ x₂ : ℝ × (ℝ × ℝ) → ℝ,
      (∀ i∈Gref, x₁ i∈Icc M (2*M) ∧ x₂ i∈Icc M (2*M) ∧ x₁ i < x₂ i ∧
        h i.1 (x₁ i)=i.2.1 ∧ h i.1 (x₂ i)=i.2.2 ∧
        U/(4*R^2) ≤ h i.1 (x₂ i)-h i.1 (x₁ i) ∧
        h i.1 (x₂ i)-h i.1 (x₁ i) ≤ 7*U/(2*R^2)) ∧
      (∀ i∈Gref, ∀ j∈Gref, i≠j → i.1=j.1 → x₂ i ≤ x₁ j ∨ x₂ j ≤ x₁ i) ∧
      ∀ (s : ℤ) (H : ℝ → ℤ → ℕ), (∀ y∈Y, ∀ k, H y k ≤ N) →
      letI : DecidableEq (ℝ × (ℝ × ℝ)) := Classical.decEq _
      let t := fun k : ℤ => (s:ℝ)+(N:ℝ)*k
      let L := fun k : ℤ => s+(N:ℤ)*k+2*(N:ℤ)
      let delta := c/(64*σ*R^2)
      let Vbound := 3*J*M/(2*σ*(N:ℝ)*R^2)
      ∀ Buffer : ℝ, 0 ≤ Buffer →
      let Gcore := Gref.filter (fun i => M+Buffer ≤ x₁ i ∧ x₂ i ≤ 2*M-Buffer)
      ∃ (S : (ℝ × (ℝ × ℝ)) → Finset ℤ) (anchor : (ℝ × (ℝ × ℝ)) → ℤ → ℚ) (za : (ℝ × (ℝ × ℝ)) → ℤ → ℝ),
        (∀ i∈Gcore,
          (∀ k : ℤ, k∈(S i) ↔ (x₁ i)+(N:ℝ)/4 ≤ t k ∧ t k ≤ (x₂ i)-(N:ℝ)/4) ∧
        (∀ k∈(S i), (za i) k∈Ioo (x₁ i) (x₂ i) ∧ (h i.1) ((za i) k)=((anchor i) k:ℝ) ∧
          ((anchor i) k:ℝ)∈Ioo ((h i.1) (x₁ i)) ((h i.1) (x₂ i)) ∧
          ((anchor i) k:ℝ)∈Ioo ((h i.1) (t k)-delta) ((h i.1) (t k)+delta) ∧
          ∀ a : ℚ, (a:ℝ)∈Ioo ((h i.1) (t k)-delta) ((h i.1) (t k)+delta) → ((anchor i) k).den ≤ a.den) ∧
        (∀ k∈(S i), |(za i) k-t k| ≤ (N:ℝ)/16) ∧
        (σ/(6*J))*U-3/2 ≤ ((S i).card:ℝ) ∧ ((S i).card:ℝ) ≤ (56*σ/c)*U+1/2 ∧
        (∀ Q : ℕ, 2 ≤ Q →
          let D := 64*σ*R^2/(c*(Q:ℝ))
          (((S i).filter (fun k => Q ≤ ((anchor i) k).den)).card:ℝ) ≤
            4*(Vbound+1)*D^2+D*(2+Real.log (D+1)))) ∧
      ∀ Q : ℕ, 2 ≤ Q → Q ≤ N →
      ∀ (Acut : ℕ) (Bmajor : ℝ), 2 ≤ Acut → Acut ≤ Q → 128*σ ≤ Bmajor →
      let Sall := Gcore.biUnion (fun i => (S i).image (fun k => (i,k)))
      Set.InjOn (fun i : (ℝ × (ℝ × ℝ)) × ℤ => (i.1.1,i.2)) (Sall : Set _) ∧
      let Good := fun i => Acut*(anchor i.1 i.2).den ≤ Q ∧
        Bmajor*R^2 ≤ c*(Q:ℝ)*(anchor i.1 i.2).den
      let G := Sall.filter Good
      let Dlow := Bmajor*R^2/(c*(Q:ℝ))
      let Khigh := Q/Acut+1
      let Dhigh := 64*σ*R^2/(c*(Khigh:ℝ))
      let Dlog := 64*σ*R^2/(c*((Q:ℝ)/Acut))
      let Cost := 4*Vbound*Dhigh^2+3*Dhigh*(2+Real.log (Dhigh+1))+
        Dlow*(2*(Vbound+delta)*Dlow+1)
      ∃ (r : (ℝ × (ℝ × ℝ)) × ℤ → ℚ) (z : (ℝ × (ℝ × ℝ)) × ℤ → ℝ),
      (∀ i∈G, (r i).den ≤ Q ∧ Q ≤ 2*(r i).den ∧
        (anchor i.1 i.2:ℝ) < r i ∧ |(r i:ℝ)-(anchor i.1 i.2:ℝ)| ≤ c/(64*σ*R^2) ∧
        z i∈Icc (za i.1 i.2) (za i.1 i.2+(N:ℝ)/16) ∧
        iteratedDeriv 2 (f i.1.1) (z i)/2=(r i:ℝ)) ∧
      (∀ i∈G, z i∈Ioo (x₁ i.1) (x₂ i.1)) ∧
      (∀ i∈G, z i∈Ioo (M+Buffer) (2*M-Buffer)) ∧
      (∀ i∈G, ∀ d : ℝ, |d|+2 ≤ Buffer →
        z i-(⌈M⌉:ℤ)+d∈Ioo (1/2:ℝ) (2*M-(⌈M⌉:ℤ)-1/2)) ∧
      (768 ≤ Acut → 24576*σ ≤ Bmajor →
        ∀ i∈G, 256*((anchor i.1 i.2).den:ℝ) ≤ (Q:ℝ)/3 ∧
          ∀ eps : ℝ, delta ≤ eps → 256 ≤ 2*eps*((Q:ℝ)/3)*(anchor i.1 i.2).den) ∧
      let m := fun i => round (z i)
      let A := fun i => (L i.2-m i).toNat
      let q := fun i => (r i).den
      let μ := fun i => iteratedDeriv 3 (f i.1.1) (m i)/6
      let ℓ := fun i => deriv (f i.1.1) (m i)
      let U₃ := J/(2*σ*(N:ℝ)*R^2)
      (∀ i∈G, |z i-(m i:ℝ)| ≤ 1/2 ∧
        N ≤ A i ∧ A i ≤ 3*N ∧ m i+(A i:ℤ)=L i.2) ∧
      ∀ (K₀ : ℕ) [NeZero K₀], 63*U₃*(Q:ℝ)*(N:ℝ)^2 ≤ K₀ →
      ∃ v : (ℝ × (ℝ × ℝ)) × ℤ → ℤ, (∀ i∈G, (q i:ℤ) ∣ (r i).num*v i-1) ∧
      let b := fun i (p : Fin 2) => (⌊(q i:ℝ)*ℓ i⌋+(p:ℕ) : ℤ)
      let τ := fun i p => ((b i p:ℝ)-(q i:ℝ)*ℓ i)/2
      let s := fun i => Real.sqrt (2/(3*μ i*(q i:ℝ)))
      let K := fun i => -2*μ i*(s i)^3
      let x := fun i p =>
        (![-(v i:ℝ)*b i p/q i,-(v i:ℝ)/q i,K i,3*K i*τ i p/2] : Fin 4 → ℝ)
      ∃ k : ZMod K₀,
      let FourierCost :=
            (1+Real.log K₀)*
            (∑ i∈G, ∑ p : Fin 2,
              (Real.sqrt (2*(q i:ℝ))/((q i:ℝ)*Real.sqrt (μ i*A i)))*
              ‖∑ j : ZMod K₀,ZMod.stdAddChar (-(j*k))*
                GafniTao.fordAdditiveCharacter (∑ d,x i p d*
                  (![(j.val+1:ℝ),(j.val+1:ℝ)^2,(j.val+1:ℝ)^((3:ℝ)/2),
                    Real.sqrt (j.val+1:ℝ)] : Fin 4 → ℝ) d)‖)+
            ∑ i∈G, (Real.sqrt (A i)*Real.log (2*(A i:ℝ))+1/(μ i*(A i:ℝ)^2))
      let Cerror := (Acut:ℝ)*((6*J/σ)*(64*σ/c)^2+192*σ/c)+
        ((3*J/σ+c/(32*σ))*(Bmajor/c)^2+Bmajor/c)
      (∑ i∈Sall, ‖∑ n∈Finset.Ioc (L i.2) (L i.2+H i.1.1 i.2),(𝐞 (f i.1.1 n):ℂ)‖) ≤ C*(((Gcore.image Prod.fst).card:ℝ)*(N:ℝ)*Cost+FourierCost) ∧
      ((Acut:ℝ)*R ≤ (Q:ℝ) → (N:ℝ)*R ≤ M →
        (∑ i∈Sall, ‖∑ n∈Finset.Ioc (L i.2) (L i.2+H i.1.1 i.2),(𝐞 (f i.1.1 n):ℂ)‖) ≤
          C*(((Gcore.image Prod.fst).card:ℝ)*Cerror*(M*R/Q)*(2+Real.log (Dlog+1))+FourierCost)) ∧
      ∀ (I : Finset ℤ), (∀ j∈I, t j∈Icc M (2*M)) →
      let BoundaryCost := (Y.card:ℝ)*((24*J/σ)*M/U+(56*σ/c)*(N:ℝ)*U+6*(N:ℝ)+2*Buffer)
      (∑ p∈Y ×ˢ I, ‖∑ n∈Finset.Ioc (L p.2) (L p.2+H p.1 p.2),(𝐞 (f p.1 n):ℂ)‖) ≤
        C*(((Gcore.image Prod.fst).card:ℝ)*(N:ℝ)*Cost+FourierCost)+BoundaryCost ∧
      ((Acut:ℝ)*R ≤ (Q:ℝ) → (N:ℝ)*R ≤ M →
        (∑ p∈Y ×ˢ I, ‖∑ n∈Finset.Ioc (L p.2) (L p.2+H p.1 p.2),(𝐞 (f p.1 n):ℂ)‖) ≤
          C*(((Gcore.image Prod.fst).card:ℝ)*Cerror*(M*R/Q)*(2+Real.log (Dlog+1))+FourierCost)+BoundaryCost) :=
  HuxleyBufferedFamilyAssemblyScratch.positive_difference_constructed_reference_family_uniform_grid_fourier (σ:=σ) (c:=c) (J:=J) hσ hc hJ

example
    {σsrc csrc Usrc σ εloss : ℝ}
    (hσsrc : 0 < σsrc) (hcsrc : 0 < csrc) (hUsrc : 0 < Usrc)
    (hσ : 0 < σ) (hεloss : 0 < εloss)
    (hanchorBudget : csrc ≤ 4*modelPhaseThirdLower σ*σsrc/(σ*(σ+1)+3)) :
    let κ := modelPhaseThirdLower σ
    let Ratio := 18*Usrc^2/(σsrc*csrc*κ)
    let L := max (8*Ratio^2)
      (32*(modelPhaseJetCoefficient σ 3+1)*(3*Usrc/σsrc)/κ^2)
    ∃ Csrc η₀ a Cupper Clower Dupper Dlower C Dtype : ℝ,
      1 ≤ Csrc ∧ 0 < η₀ ∧ η₀ ≤ 1/8 ∧ 0 < a ∧
      0 < Cupper ∧ 0 < Clower ∧ 0 < Dupper ∧ 0 < Dlower ∧ 0 < C ∧ 0 < Dtype ∧
    ∀ {θ : ℝ}, 0 < θ → θ ≤ 1/24 → θ ≤ 1/(8*(L+3)) →
    ∀ᶠ T : ℝ in Filter.atTop, ∀ (Fsrc : ℝ → ℝ) (Y : Finset ℝ)
      (Q K₀ N Uref : ℕ) [NeZero K₀] (R Jsep : ℝ) {η M δ Bcut Bselect : ℝ},
    0 < η → η ≤ η₀ → 0 < T → 2 ≤ N →
    1 ≤ R → R ≤ M → 0 ≤ δ → δ ≤ min κ 1 →
    0 < Jsep → Jsep ≤ M →
    (∀ y ∈ Y, y ∈ Icc (1:ℝ) 2) →
    (∀ y ∈ Y, ∀ z ∈ Y, y ≠ z → 1 ≤ Jsep*|y-z|) →
    (∀ w, 0 < w → ContDiffAt ℝ ∞ Fsrc w) →
    (∀ w ∈ Icc (1/2:ℝ) 3, ∀ n ≤ 6, |iteratedDeriv (n+1) Fsrc w| ≤ Usrc) →
    (∀ w ∈ Icc (1/2:ℝ) 3, ∀ j,
      csrc ≤ |HuxleyModel.tests (fun i : Fin 4 => iteratedDeriv (i.val+3) Fsrc w) j|) →
    (∀ w ∈ Icc (1/2:ℝ) 3, iteratedDeriv 4 Fsrc w ≤ -csrc) →
    (∀ y ∈ Y, Expdb.IsApproximateModelPhaseFunction
      (fun u => (Fsrc u-Fsrc (u+η*y))/(σsrc*η)) σ 4 δ) →
    T*(N:ℝ)*R^2 = M^3 →
    7*(N:ℝ)+2 ≤ M/4 →
    (3*Usrc/σsrc)*(6*(N:ℝ)+1)^4 ≤ M*(N:ℝ)*R^2 →
    (3*Usrc/(4*σsrc))*(6*(N:ℝ)+1)^2 ≤ (N:ℝ)*R^2 →
    3*Usrc ≤ σsrc*(Uref:ℝ) →
    63*(Usrc/(2*σsrc*(N:ℝ)*R^2))*(Q:ℝ)*(N:ℝ)^2 ≤ K₀ →
    (Q:ℝ)*(N:ℝ) ≤ (K₀:ℝ)*R^2 →
    (N:ℝ)^4 ≤ M*R^3*(Real.log T)^((3:ℝ)/2) →
    1 ≤ Uref → 0 < Bcut →
    2+168/κ ≤ Bselect → 7*Bcut ≤ κ*Bselect →
    Bselect^2*(Uref:ℝ)^3*R^2 ≤ (N:ℝ)^2 →
    (Uref:ℝ) ≤ ((N:ℝ)/(Q:ℝ))^((2:ℝ)/3)/Bselect →
    ((N:ℝ)/(Q:ℝ))^((2:ℝ)/3)/(2*Bselect) ≤ (Uref:ℝ) →
    (N:ℝ)^10 ≤ M^3*R^7 →
    Q ≤ N → (N:ℝ)^2 ≤ M → (Uref:ℝ) ≤ R^2 →
    768*R ≤ (Q:ℝ) → (N:ℝ)*R ≤ M →
    let Cphys := σ*(σ+1)+1
    let c := κ/6
    let J := Cphys/6
    let B := max 1 (max (2*Real.sqrt J) (8*J*Real.sqrt J/(3*c)))
    B*R^2/(N:ℝ)^2 ≤ 1/2 →
    (N:ℝ) ≤ R^2 → R ≤ (N:ℝ) → (N:ℝ)^3 ≤ M*R^2 →
    2*R^2 ≤ (Q:ℝ)*(N:ℝ) →
    let Vscale := (Uref:ℝ)^((3:ℝ)/2)
    let lambda := csrc*κ*T/(12*Usrc*M^2)
    let Uband := (3*Usrc/σsrc)*T/(2*M^2)
    let ChartCap := (4/a+3)*((6*Usrc/σsrc)/a+3)*((4*σsrc/csrc)/a+3)
    let NarrowCap := (4/θ+3)*(72*Usrc^2/(σsrc*csrc*κ*θ)+3)
    let Cap := 3*ChartCap*NarrowCap
    let μ₀ := csrc*T/(12*σsrc*M^3)
    let U₀ := Usrc*T/(2*σsrc*M^3)
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
    let AupperConst := 2*Cupper*(Cthird+1)*1^2/(κ*Lunit^3)
    let BupperConst := Cupper*(Cthird+1)*1^2/Lunit^2+Dupper*(B+1)*1^2/4
    let AlowerConst := 8*Clower*(Cthird+1)/(κ*Lunit^3)
    let BlowerConst := 4*Clower*(Cthird+1)/Lunit^2+Dlower*(B+1)
    let DupperConst := θ*(3*Usrc/σsrc)*1/2
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

    let Buffer := (56*(Uref:ℝ)/κ)*(N:ℝ)+(N:ℝ)/(Cphys+2)+2
    let Dlog := 64*σsrc*R^2/(csrc*((Q:ℝ)/768))
    let Cerror := (768:ℝ)*((6*Usrc/σsrc)*(64*σsrc/csrc)^2+192*σsrc/csrc)+
      ((3*Usrc/σsrc+csrc/(32*σsrc))*((24576*σsrc)/csrc)^2+(24576*σsrc)/csrc)
    let Major := (Y.card:ℝ)*Cerror*(M*R/(Q:ℝ))*(2+Real.log (Dlog+1))
    let Error := (Y.card:ℝ)*(M/(N:ℝ)+1)*
      (Real.sqrt (3*(N:ℝ))*Real.log (6*(N:ℝ))+12*σsrc*R^2/(csrc*(N:ℝ)))
    let FamilyBound := (144*Usrc/(csrc*κ))^6*(R^2/(Q:ℝ))^6*
      C*(K₀:ℝ)^((12:ℝ)+εloss)*Cap^11*(10*(Y.card:ℝ)*(M/(N:ℝ)))^10*
        (Vscale*Dtype*(Y.card:ℝ)*(M/(N:ℝ))*(1+Δtype*Jsep)+
          (Y.card:ℝ)^2*(Vscale*(Kupper+Klower)+Klarge)*T^εloss)
    let f := fun y w => T*(Fsrc (w/M)-Fsrc (w/M+η*y))/(σsrc*η)
    let h := fun y w => iteratedDeriv 2 (f y) w/2
    ∃ Refs : Finset ℝ,
      (∀ a ∈ Refs, ∀ b ∈ Refs, a ≠ b → (Uref:ℝ)/(4*R^2) ≤ |a-b|) ∧
      (∀ a ∈ Refs, ∀ b ∈ Refs, a < b → (∀ q ∈ Refs,¬(a < q ∧ q < b)) →
        b-a ≤ 7*(Uref:ℝ)/(2*R^2)) ∧
      (∀ y ∈ Y, ∃ l ∈ Refs, ∃ u ∈ Refs, l ≤ h y M ∧ h y (2*M) ≤ u) ∧
      (∀ y ∈ Y, ∀ q ∈ Refs, q ∈ Icc (h y M) (h y (2*M)) →
        ∃ z ∈ Icc M (2*M), h y z = q) ∧
      ∀ (sgrid : ℤ) (Hlen : ℝ → ℤ → ℕ), (∀ y ∈ Y, ∀ k, Hlen y k ≤ N) →
      let Lgrid := fun k : ℤ => sgrid+(N:ℤ)*k+2*(N:ℤ)
      let Good : ℝ × ℤ → Prop := fun p =>
        ∃ a ∈ Refs, ∃ b ∈ Refs, a < b ∧ (∀ q ∈ Refs,¬(a < q ∧ q < b)) ∧
          ∃ z₁ z₂ : ℝ, z₁ ∈ Icc M (2*M) ∧ z₂ ∈ Icc M (2*M) ∧
            h p.1 z₁ = a ∧ h p.1 z₂ = b ∧ M+Buffer ≤ z₁ ∧ z₂ ≤ 2*M-Buffer ∧
            z₁+(N:ℝ)/4 ≤ (sgrid:ℝ)+(N:ℝ)*p.2 ∧
              (sgrid:ℝ)+(N:ℝ)*p.2 ≤ z₂-(N:ℝ)/4
      ∀ Pcore : Finset (ℝ × ℤ), (∀ p ∈ Pcore, p.1 ∈ Y ∧ Good p) →
      (∑ p ∈ Pcore, ‖∑ n ∈ Finset.Ioc (Lgrid p.2) (Lgrid p.2+Hlen p.1 p.2),
        (𝐞 (f p.1 n):ℂ)‖)^12 ≤
        2^11*((Csrc*(Major+Error))^12+
          (Csrc*(1+Real.log K₀))^12*FamilyBound)
 :=
  HuxleyBufferedFamilyAssemblyScratch.eventually_positive_difference_uniform_reference_core_physical_sieve (σsrc:=σsrc) (csrc:=csrc) (Usrc:=Usrc) (σ:=σ) (εloss:=εloss) hσsrc hcsrc hUsrc hσ hεloss hanchorBudget


#print axioms actual_reference_hull_order_bound
#print axioms actual_reference_hull_label_heights
#print axioms actual_reference_gap_oriented_chart
#print axioms actual_tagged_grid_endpoint_trim
#print axioms source_integer_window_of_endpoint_buffer
#print axioms source_buffered_boundary_cost
#print axioms positive_difference_constructed_reference_family_uniform_grid_fourier
#print axioms eventually_positive_difference_uniform_reference_core_physical_sieve

private theorem two_probes_avoid_separated_set
    (S : Set ℝ) {x y radius spacing : ℝ}
    (hsep : ∀ a ∈ S, ∀ b ∈ S, a ≠ b → spacing ≤ |a-b|)
    (hprobe : 2*radius < |x-y|)
    (hspan : |x-y|+2*radius < spacing) :
    (∀ a ∈ S, radius < |x-a|) ∨ (∀ a ∈ S, radius < |y-a|) := by
  classical
  by_contra hh
  obtain ⟨hx,hy⟩ := not_or.mp hh
  push Not at hx hy
  obtain ⟨a,ha,hxa⟩ := hx
  obtain ⟨b,hb,hyb⟩ := hy
  have hab : a = b := by
    by_contra hne
    have htriangle : |a-b| ≤ |x-a|+|x-y|+|y-b| := by
      calc
        |a-b| ≤ |a-x|+|x-b| := abs_sub_le _ _ _
        _ ≤ |a-x|+(|x-y|+|y-b|) := add_le_add le_rfl (abs_sub_le _ _ _)
        _ = _ := by rw [abs_sub_comm a x]; ring
    have hs := hsep a ha b hb hne
    linarith only [hs,htriangle,hxa,hyb,hspan]
  subst b
  have htriangle : |x-y| ≤ |x-a|+|y-a| := by
    simpa only [abs_sub_comm a y] using abs_sub_le x a y
  linarith only [htriangle,hprobe,hxa,hyb]


private theorem positive_difference_two_safe_block_starts
    (F : ℝ → ℝ) (Refs : Finset ℝ) {σ c J η y T M N R U x : ℝ}
    (hσ : 0 < σ) (hc : 0 < c) (hJ : 0 < J)
    (hη : 0 < η) (hηmax : η ≤ 1/8) (hy : y ∈ Icc (1:ℝ) 2)
    (hreg : ∀ w, 0 < w → ContDiffAt ℝ ∞ F w)
    (hbound : ∀ w ∈ Icc (1/2:ℝ) 3, ∀ n ≤ 6, |iteratedDeriv (n+1) F w| ≤ J)
    (hnegative : ∀ w ∈ Icc (1/2:ℝ) 3, iteratedDeriv 4 F w ≤ -c)
    (hT : 0 < T) (hM : 0 < M) (hN : 0 < N) (hR : 0 < R)
    (hscale : T*N*R^2 = M^3)
    (hsep : ∀ a ∈ Refs, ∀ b ∈ Refs, a ≠ b → U/(4*R^2) ≤ |a-b|)
    (hUlarge : 12*J ≤ σ*U) (hx : x ∈ Icc (M+3*N) (2*M)) :
    let f := fun w => T*(F (w/M)-F (w/M+η*y))/(σ*η)
    let h := fun w => iteratedDeriv 2 f w/2
    ((x-2*N) ∈ Icc M (2*M) ∧
      ∀ z ∈ Icc M (2*M), h z ∈ Refs → N/4 < |(x-2*N)-z|) ∨
    ((x-11*N/4) ∈ Icc M (2*M) ∧
      ∀ z ∈ Icc M (2*M), h z ∈ Refs → N/4 < |(x-11*N/4)-z|) := by
  intro f h
  have hwide w (hw : w ∈ Icc M (2*M)) : w ∈ Icc (3*M/4) (9*M/4) := by
    constructor <;> linarith only [hw.1,hw.2,hM]
  have hmono := positive_difference_physical_curvature_strictMono F
    hσ hc hη hηmax hy hreg hnegative hT hM
  change StrictMonoOn h (Icc (3*M/4) (9*M/4)) at hmono
  have hsize : 2 ≤ (σ/(6*J))*U := by
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by positivity : 0 < 6*J)).mpr
    linarith only [hUlarge]
  let Roots : Set ℝ := {z | z ∈ Icc M (2*M) ∧ h z ∈ Refs}
  have hrootSep a (ha : a ∈ Roots) b (hb : b ∈ Roots) (hab : a ≠ b) :
      2*N ≤ |a-b| := by
    have hne : h b ≠ h a := fun he =>
      hab (hmono.injOn (hwide _ ha.1) (hwide _ hb.1) he.symm)
    have hg := hsep (h b) hb.2 (h a) ha.2 hne
    have hw := positive_difference_reference_preimage_width_lower F
      hσ hJ hη hηmax hy hreg hbound hT hM hN hR hscale
      (hwide _ ha.1) (hwide _ hb.1) hg
    calc
      2*N ≤ ((σ/(6*J))*U)*N := mul_le_mul_of_nonneg_right hsize hN.le
      _ ≤ |b-a| := hw
      _ = |a-b| := abs_sub_comm _ _
  have hdist : |(x-2*N)-(x-11*N/4)| = 3*N/4 := by
    rw [show (x-2*N)-(x-11*N/4) = 3*N/4 by ring,abs_of_nonneg (by positivity)]
  have havoid := two_probes_avoid_separated_set Roots
    (x:=x-2*N) (y:=x-11*N/4) (radius:=N/4) (spacing:=2*N) hrootSep
    (by rw [hdist]; linarith only [hN]) (by rw [hdist]; linarith only [hN])
  rcases havoid with hleft | hright
  · exact Or.inl ⟨⟨by linarith only [hx.1,hN],by linarith only [hx.2,hN]⟩,
      fun z hz hzref => hleft z ⟨hz,hzref⟩⟩
  · exact Or.inr ⟨⟨by linarith only [hx.1,hN],by linarith only [hx.2,hN]⟩,
      fun z hz hzref => hright z ⟨hz,hzref⟩⟩


private theorem finite_reference_safe_start_buffered_bracket
    (S : Finset ℝ) (h : ℝ → ℝ) {M N Buffer D t : ℝ}
    (hM : 0 < M) (hN : 0 < N) (hBuffer : 0 ≤ Buffer) (hD : 0 ≤ D)
    (hmono : StrictMonoOn h (Icc M (2*M)))
    (henclose : ∃ l ∈ S, ∃ u ∈ S, l ≤ h M ∧ h (2*M) ≤ u)
    (hroots : ∀ q ∈ S, q ∈ Icc (h M) (h (2*M)) →
      ∃ z ∈ Icc M (2*M), h z = q)
    (hwidth : ∀ a ∈ S, ∀ b ∈ S, a < b → (∀ q ∈ S,¬(a < q ∧ q < b)) →
      ∀ x ∈ Icc M (2*M), ∀ z ∈ Icc M (2*M),
        h x ∈ Icc a b → h z ∈ Icc a b → |z-x| ≤ D)
    (ht : t ∈ Icc (M+Buffer+D+N) (2*M-Buffer-D-N))
    (hsafe : ∀ z ∈ Icc M (2*M), h z ∈ S → N/4 < |t-z|) :
    ∃ a ∈ S, ∃ b ∈ S, a < b ∧ (∀ q ∈ S,¬(a < q ∧ q < b)) ∧
      ∃ z₁ z₂ : ℝ, z₁ ∈ Icc M (2*M) ∧ z₂ ∈ Icc M (2*M) ∧
        h z₁ = a ∧ h z₂ = b ∧ M+Buffer ≤ z₁ ∧ z₂ ≤ 2*M-Buffer ∧
        z₁+N/4 ≤ t ∧ t ≤ z₂-N/4 := by
  have hleft : M ∈ Icc M (2*M) := ⟨le_rfl,by linarith only [hM]⟩
  have hright : 2*M ∈ Icc M (2*M) := ⟨by linarith only [hM],le_rfl⟩
  have htphys : t ∈ Icc M (2*M) :=
    ⟨by linarith only [ht.1,hBuffer,hD,hN],by linarith only [ht.2,hBuffer,hD,hN]⟩
  have hcurv : h t ∈ Icc (h M) (h (2*M)) :=
    ⟨hmono.monotoneOn hleft htphys htphys.1,hmono.monotoneOn htphys hright htphys.2⟩
  have htNot : h t∉S := by
    intro hh
    have hb := hsafe t htphys hh
    rw [sub_self,abs_zero] at hb
    linarith only [hb,hN]
  obtain ⟨l,hl,u,hu,hlo,hhi⟩ := henclose
  obtain ⟨a,ha,b,hb,hat,htb,hadj⟩ :=
    finite_reference_bracket S hl hu (hlo.trans hcurv.1) (hcurv.2.trans hhi) htNot
  have hab : a < b := hat.trans htb
  have haInner : h M ≤ a := by
    by_contra hnot
    have hma : a < h M := lt_of_not_ge hnot
    have hw := hwidth a ha b hb hab hadj M hleft t htphys
      ⟨hma.le,hcurv.1.trans htb.le⟩ ⟨hat.le,htb.le⟩
    have hx := (abs_le.mp hw).2
    linarith only [hx,ht.1,hBuffer,hN]
  have hbInner : b ≤ h (2*M) := by
    by_contra hnot
    have hmb : h (2*M) < b := lt_of_not_ge hnot
    have hw := hwidth a ha b hb hab hadj t htphys (2*M) hright
      ⟨hat.le,htb.le⟩ ⟨hat.le.trans hcurv.2,hmb.le⟩
    have hx := (abs_le.mp hw).2
    linarith only [hx,ht.2,hBuffer,hN]
  obtain ⟨z₁,hz₁,hza⟩ := hroots a ha ⟨haInner,hab.le.trans hbInner⟩
  obtain ⟨z₂,hz₂,hzb⟩ := hroots b hb ⟨haInner.trans hab.le,hbInner⟩
  have hz₁t : z₁ < t := by
    by_contra hnot
    have hh := hmono.monotoneOn htphys hz₁ (le_of_not_gt hnot)
    rw [hza] at hh
    exact (not_lt_of_ge hh) hat
  have htz₂ : t < z₂ := by
    by_contra hnot
    have hh := hmono.monotoneOn hz₂ htphys (le_of_not_gt hnot)
    rw [hzb] at hh
    exact (not_lt_of_ge hh) htb
  have hwleft := hwidth a ha b hb hab hadj z₁ hz₁ t htphys
    (by rw [hza]; exact ⟨le_rfl,hab.le⟩) ⟨hat.le,htb.le⟩
  have hwright := hwidth a ha b hb hab hadj t htphys z₂ hz₂
    ⟨hat.le,htb.le⟩ (by rw [hzb]; exact ⟨hab.le,le_rfl⟩)
  have hsleft := hsafe z₁ hz₁ (hza.symm ▸ ha)
  have hsright := hsafe z₂ hz₂ (hzb.symm ▸ hb)
  rw [abs_of_pos (sub_pos.mpr hz₁t)] at hsleft
  rw [abs_of_neg (sub_neg.mpr htz₂)] at hsright
  refine ⟨a,ha,b,hb,hab,hadj,z₁,z₂,hz₁,hz₂,hza,hzb,?_,?_,?_,?_⟩
  · have hh := (abs_le.mp hwleft).2
    linarith only [hh,ht.1,hN]
  · have hh := (abs_le.mp hwright).2
    linarith only [hh,ht.2,hN]
  · linarith only [hsleft]
  · linarith only [hsright]


private theorem positive_difference_two_buffered_block_starts
    (F : ℝ → ℝ) (Refs : Finset ℝ) {σ c J η y T M N R U Buffer x : ℝ}
    (hσ : 0 < σ) (hc : 0 < c) (hJ : 0 < J)
    (hη : 0 < η) (hηmax : η ≤ 1/8) (hy : y ∈ Icc (1:ℝ) 2)
    (hreg : ∀ w, 0 < w → ContDiffAt ℝ ∞ F w)
    (hbound : ∀ w ∈ Icc (1/2:ℝ) 3, ∀ n ≤ 6, |iteratedDeriv (n+1) F w| ≤ J)
    (hnegative : ∀ w ∈ Icc (1/2:ℝ) 3, iteratedDeriv 4 F w ≤ -c)
    (hT : 0 < T) (hM : 0 < M) (hN : 0 < N) (hR : 0 < R)
    (hscale : T*N*R^2 = M^3)
    (hsep : ∀ a ∈ Refs, ∀ b ∈ Refs, a ≠ b → U/(4*R^2) ≤ |a-b|)
    (hgap : ∀ a ∈ Refs, ∀ b ∈ Refs, a < b → (∀ q ∈ Refs,¬(a < q ∧ q < b)) →
      b-a ≤ 7*U/(2*R^2))
    (hUlarge : 12*J ≤ σ*U) (hBuffer : 0 ≤ Buffer) :
    let f := fun w => T*(F (w/M)-F (w/M+η*y))/(σ*η)
    let h := fun w => iteratedDeriv 2 f w/2
    let D := (14*σ/c)*U*N
    (∃ l ∈ Refs, ∃ u ∈ Refs, l ≤ h M ∧ h (2*M) ≤ u) →
    (∀ q ∈ Refs, q ∈ Icc (h M) (h (2*M)) → ∃ z ∈ Icc M (2*M), h z = q) →
    x ∈ Icc (M+Buffer+D+4*N) (2*M-Buffer-D-N) →
    ∃ t : ℝ, (t = x-2*N ∨ t = x-11*N/4) ∧
      ∃ a ∈ Refs, ∃ b ∈ Refs, a < b ∧ (∀ q ∈ Refs,¬(a < q ∧ q < b)) ∧
        ∃ z₁ z₂ : ℝ, z₁ ∈ Icc M (2*M) ∧ z₂ ∈ Icc M (2*M) ∧
          h z₁ = a ∧ h z₂ = b ∧ M+Buffer ≤ z₁ ∧ z₂ ≤ 2*M-Buffer ∧
          z₁+N/4 ≤ t ∧ t ≤ z₂-N/4 := by
  intro f h D henclose hroots hx
  have hU : 0 < U := (div_pos (by positivity : 0 < 12*J) hσ).trans_le
    ((div_le_iff₀ hσ).mpr (by simpa only [mul_comm] using hUlarge))
  have hD : 0 ≤ D := by dsimp only [D]; positivity
  have hmono : StrictMonoOn h (Icc M (2*M)) := by
    apply (positive_difference_physical_curvature_strictMono F hσ hc hη hηmax hy
      hreg hnegative hT hM).mono
    intro w hw
    constructor <;> linarith only [hw.1,hw.2,hM]
  have hwidth a (ha : a ∈ Refs) b (hb : b ∈ Refs) (hab : a < b)
      (hadj : ∀ q ∈ Refs,¬(a < q ∧ q < b))
      u (hu : u ∈ Icc M (2*M)) z (hz : z ∈ Icc M (2*M))
      (huc : h u ∈ Icc a b) (hzc : h z ∈ Icc a b) : |z-u| ≤ D := by
    apply positive_difference_reference_preimage_width F
      hσ hc hη hηmax hy hreg hnegative hT hM hN hR hscale hu hz
    change |h z-h u| ≤ 7*U/(2*R^2)
    apply (abs_le.mpr ?_).trans (hgap a ha b hb hab hadj)
    constructor <;> linarith only [huc.1,huc.2,hzc.1,hzc.2]
  have hsafe := positive_difference_two_safe_block_starts F Refs
    hσ hc hJ hη hηmax hy hreg hbound hnegative hT hM hN hR hscale hsep hUlarge
    (show x ∈ Icc (M+3*N) (2*M) from
      ⟨by linarith only [hx.1,hBuffer,hD,hN],by linarith only [hx.2,hBuffer,hD,hN]⟩)
  have hleft : x-2*N ∈ Icc (M+Buffer+D+N) (2*M-Buffer-D-N) :=
    ⟨by linarith only [hx.1,hN],by linarith only [hx.2,hN]⟩
  have hright : x-11*N/4 ∈ Icc (M+Buffer+D+N) (2*M-Buffer-D-N) :=
    ⟨by linarith only [hx.1,hN],by linarith only [hx.2,hN]⟩
  rcases hsafe with hgood | hgood
  · exact ⟨x-2*N,Or.inl rfl,
      finite_reference_safe_start_buffered_bracket Refs h hM hN hBuffer hD
        hmono henclose hroots hwidth hleft hgood.2⟩
  · exact ⟨x-11*N/4,Or.inr rfl,
      finite_reference_safe_start_buffered_bracket Refs h hM hN hBuffer hD
        hmono henclose hroots hwidth hright hgood.2⟩


private theorem finite_prefix_maximizers {α : Type*} (v : α → ℤ → ℂ) (N : ℕ) :
    ∃ H : α → ℤ → ℕ, ∀ y L, H y L ≤ N ∧
      ∀ h ≤ N, ‖∑ k ∈ Finset.Ioc L (L+(h:ℤ)), v y k‖ ≤
        ‖∑ k ∈ Finset.Ioc L (L+(H y L:ℤ)), v y k‖ := by
  classical
  have hex (y : α) (L : ℤ) : ∃ h ≤ N, ∀ t ≤ N,
      ‖∑ k ∈ Finset.Ioc L (L+(t:ℤ)), v y k‖ ≤
        ‖∑ k ∈ Finset.Ioc L (L+(h:ℤ)), v y k‖ := by
    obtain ⟨h,hh,hmax⟩ := (Finset.range (N+1)).exists_max_image
      (fun h => ‖∑ k ∈ Finset.Ioc L (L+(h:ℤ)), v y k‖)
      ⟨0,by simp⟩
    exact ⟨h,by simpa using hh,fun t ht => hmax t (by simpa using ht)⟩
  choose H hH using hex
  exact ⟨H,hH⟩


private theorem integer_subinterval_le_two_prefixes
    (v : ℤ → ℂ) {L A B : ℤ} {N : ℕ} {W : ℝ}
    (hLA : L ≤ A) (hAB : A ≤ B) (hBN : B ≤ L+(N:ℤ))
    (hprefix : ∀ h ≤ N, ‖∑ k ∈ Finset.Ioc L (L+(h:ℤ)), v k‖ ≤ W) :
    ‖∑ k ∈ Finset.Ioc A B, v k‖ ≤ 2*W := by
  have hsub : Finset.Ioc L A ⊆ Finset.Ioc L B := by
    intro k hk
    simp only [Finset.mem_Ioc] at hk ⊢
    exact ⟨hk.1,hk.2.trans hAB⟩
  have hdiff : Finset.Ioc L B \ Finset.Ioc L A = Finset.Ioc A B := by
    ext k
    simp only [Finset.mem_sdiff,Finset.mem_Ioc]
    omega
  have hsum := Finset.sum_sdiff (f:=v) hsub
  rw [hdiff] at hsum
  have heq : (∑ k ∈ Finset.Ioc A B, v k) =
      (∑ k ∈ Finset.Ioc L B, v k)-(∑ k ∈ Finset.Ioc L A, v k) := by
    exact eq_sub_iff_add_eq.mpr hsum
  have hA : (A-L).toNat ≤ N := by omega
  have hB : (B-L).toNat ≤ N := by omega
  have ha := hprefix (A-L).toNat hA
  have hb := hprefix (B-L).toNat hB
  have hcastA : L+((A-L).toNat:ℤ) = A := by omega
  have hcastB : L+((B-L).toNat:ℤ) = B := by omega
  rw [hcastA] at ha
  rw [hcastB] at hb
  rw [heq]
  exact (norm_sub_le _ _).trans (by linarith only [ha,hb])


private theorem two_start_chunk_cover {α : Type*}
    (v : α → ℤ → ℂ) (C D : Finset (α × ℤ)) (n : ℕ)
    (H : α → ℤ → ℕ)
    (hprefix : ∀ y L, ∀ h ≤ 8*n,
      ‖∑ k ∈ Finset.Ioc L (L+(h:ℤ)), v y k‖ ≤
        ‖∑ k ∈ Finset.Ioc L (L+(H y L:ℤ)), v y k‖)
    (hcover : ∀ p ∈ C, p ∈ D ∨ (p.1,p.2-6) ∈ D) :
    (∑ p ∈ C, ‖∑ k ∈ Finset.Ioc ((n:ℤ)*p.2) ((n:ℤ)*(p.2+1)), v p.1 k‖) ≤
      4*∑ p ∈ D, ‖∑ k ∈ Finset.Ioc ((n:ℤ)*p.2)
        ((n:ℤ)*p.2+(H p.1 ((n:ℤ)*p.2):ℤ)), v p.1 k‖ := by
  classical
  let w (p : α × ℤ) := ‖∑ k ∈ Finset.Ioc ((n:ℤ)*p.2)
    ((n:ℤ)*p.2+(H p.1 ((n:ℤ)*p.2):ℤ)), v p.1 k‖
  let f (p : α × ℤ) := ‖∑ k ∈ Finset.Ioc ((n:ℤ)*p.2)
    ((n:ℤ)*(p.2+1)), v p.1 k‖
  let shift (p : α × ℤ) := (p.1,p.2-6)
  have hn : (0:ℤ) ≤ n := Int.natCast_nonneg n
  have hleft (p : α × ℤ) : f p ≤ 2*w p := by
    apply integer_subinterval_le_two_prefixes (v p.1) (N:=8*n) le_rfl
      (by nlinarith only [hn]) (by push_cast; nlinarith only [hn])
    exact hprefix p.1 ((n:ℤ)*p.2)
  have hright (p : α × ℤ) : f p ≤ 2*w (shift p) := by
    apply integer_subinterval_le_two_prefixes (v p.1) (L:=(n:ℤ)*(p.2-6)) (N:=8*n)
      (by nlinarith only [hn])
      (by nlinarith only [hn])
      (by push_cast; nlinarith only [hn])
    exact hprefix p.1 ((n:ℤ)*(p.2-6))
  have hw (p : α × ℤ) : 0 ≤ w p := norm_nonneg _
  let C₀ := C.filter (fun p => p ∈ D)
  let C₁ := C.filter (fun p => p ∉ D)
  have hsub₀ : C₀ ⊆ D := fun p hp => (Finset.mem_filter.mp hp).2
  have hsub₁ : C₁.image shift ⊆ D := by
    intro p hp
    obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨hqC,hqD⟩ := Finset.mem_filter.mp hq
    exact (hcover q hqC).resolve_left hqD
  have hinj : Function.Injective shift := by
    intro p q heq
    have hfirst := congrArg Prod.fst heq
    have hsecond := congrArg Prod.snd heq
    change p.1 = q.1 at hfirst
    change p.2-6 = q.2-6 at hsecond
    apply Prod.ext hfirst
    omega
  have hs₀ : (∑ p ∈ C₀, w p) ≤ ∑ p ∈ D, w p :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub₀ (fun p _ _ => hw p)
  have hs₁ : (∑ p ∈ C₁, w (shift p)) ≤ ∑ p ∈ D, w p := by
    rw [← Finset.sum_image hinj.injOn]
    exact Finset.sum_le_sum_of_subset_of_nonneg hsub₁ (fun p _ _ => hw p)
  have hsum₀ := Finset.sum_le_sum (fun p (_ : p ∈ C₀) => hleft p)
  have hsum₁ := Finset.sum_le_sum (fun p (_ : p ∈ C₁) => hright p)
  rw [← Finset.mul_sum] at hsum₀ hsum₁
  have hsplit : (∑ p ∈ C₀, f p)+(∑ p ∈ C₁, f p) = ∑ p ∈ C, f p :=
    Finset.sum_filter_add_sum_filter_not C (fun p => p ∈ D) f
  change (∑ p ∈ C, f p) ≤ 4*∑ p ∈ D, w p
  linarith only [hs₀,hs₁,hsum₀,hsum₁,hsplit]


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


private theorem positive_difference_eight_grid_chunk_cover
    (F : ℝ → ℝ) (Y Refs : Finset ℝ) (n : ℕ)
    {σ c J η T M R U Buffer : ℝ}
    (hn : 0 < n) (hσ : 0 < σ) (hc : 0 < c) (hJ : 0 < J)
    (hη : 0 < η) (hηmax : η ≤ 1/8) (hy : ∀ y ∈ Y, y ∈ Icc (1:ℝ) 2)
    (hreg : ∀ w, 0 < w → ContDiffAt ℝ ∞ F w)
    (hbound : ∀ w ∈ Icc (1/2:ℝ) 3, ∀ k ≤ 6, |iteratedDeriv (k+1) F w| ≤ J)
    (hnegative : ∀ w ∈ Icc (1/2:ℝ) 3, iteratedDeriv 4 F w ≤ -c)
    (hT : 0 < T) (hM : 0 < M) (hR : 0 < R)
    (hscale : T*(8*(n:ℝ))*R^2 = M^3)
    (hsep : ∀ a ∈ Refs, ∀ b ∈ Refs, a ≠ b → U/(4*R^2) ≤ |a-b|)
    (hgap : ∀ a ∈ Refs, ∀ b ∈ Refs, a < b → (∀ q ∈ Refs,¬(a < q ∧ q < b)) →
      b-a ≤ 7*U/(2*R^2))
    (hUlarge : 12*J ≤ σ*U) (hBuffer : 0 ≤ Buffer) :
    let N : ℝ := 8*n
    let f := fun y w => T*(F (w/M)-F (w/M+η*y))/(σ*η)
    let h := fun y w => iteratedDeriv 2 (f y) w/2
    let Width := (14*σ/c)*U*N
    let Good : ℝ × ℤ → Prop := fun p =>
      ∃ a ∈ Refs, ∃ b ∈ Refs, a < b ∧ (∀ q ∈ Refs,¬(a < q ∧ q < b)) ∧
        ∃ z₁ z₂ : ℝ, z₁ ∈ Icc M (2*M) ∧ z₂ ∈ Icc M (2*M) ∧
          h p.1 z₁ = a ∧ h p.1 z₂ = b ∧ M+Buffer ≤ z₁ ∧ z₂ ≤ 2*M-Buffer ∧
          z₁+N/4 ≤ (n:ℝ)*p.2-2*N ∧ (n:ℝ)*p.2-2*N ≤ z₂-N/4
    (∀ y ∈ Y, ∃ l ∈ Refs, ∃ u ∈ Refs, l ≤ h y M ∧ h y (2*M) ≤ u) →
    (∀ y ∈ Y, ∀ q ∈ Refs, q ∈ Icc (h y M) (h y (2*M)) →
      ∃ z ∈ Icc M (2*M), h y z = q) →
    ∃ H : ℝ → ℤ → ℕ, (∀ y L, H y L ≤ 8*n) ∧
      ∀ C : Finset (ℝ × ℤ), (∀ p ∈ C, p.1 ∈ Y) →
        (∀ p ∈ C, (n:ℝ)*p.2 ∈ Icc (M+Buffer+Width+4*N) (2*M-Buffer-Width-N)) →
      ∃ D : Finset (ℝ × ℤ),
        D ⊆ C ∪ C.image (fun p => (p.1,p.2-6)) ∧
        (∀ p ∈ D, Good p) ∧
        (∑ p ∈ C, ‖∑ k ∈ Finset.Ioc ((n:ℤ)*p.2) ((n:ℤ)*(p.2+1)),
          (𝐞 (f p.1 k):ℂ)‖) ≤
        4*∑ r ∈ Finset.Ico (0:ℤ) 8,
          ∑ p ∈ (D.filter (fun p => p.2%8 = r)).image (fun p => (p.1,p.2/8-2)),
            ‖∑ k ∈ Finset.Ioc ((n:ℤ)*(r+8*p.2+16))
              ((n:ℤ)*(r+8*p.2+16)+(H p.1 ((n:ℤ)*(r+8*p.2+16)):ℤ)),
                (𝐞 (f p.1 k):ℂ)‖ := by
  classical
  intro N f h Width Good henclose hroots
  let v : ℝ → ℤ → ℂ := fun y k => 𝐞 (f y k)
  obtain ⟨H,hH⟩ := finite_prefix_maximizers v (8*n)
  refine ⟨H,fun y L => (hH y L).1,?_⟩
  intro C hCY hdeep
  let shift : ℝ × ℤ → ℝ × ℤ := fun p => (p.1,p.2-6)
  let D := (C ∪ C.image shift).filter Good
  have hNp : 0 < N := by dsimp only [N]; positivity
  have hsafe p (hp : p ∈ C) : Good p ∨ Good (shift p) := by
    obtain ⟨t,ht,hdata⟩ := positive_difference_two_buffered_block_starts F Refs
      hσ hc hJ hη hηmax (hy p.1 (hCY p hp)) hreg hbound hnegative
      hT hM hNp hR hscale hsep hgap hUlarge hBuffer
      (henclose p.1 (hCY p hp)) (hroots p.1 (hCY p hp)) (hdeep p hp)
    rcases ht with ht | ht
    · subst t
      exact Or.inl hdata
    · subst t
      right
      change ∃ a ∈ Refs, ∃ b ∈ Refs, a < b ∧ (∀ q ∈ Refs,¬(a < q ∧ q < b)) ∧
        ∃ z₁ z₂ : ℝ, z₁ ∈ Icc M (2*M) ∧ z₂ ∈ Icc M (2*M) ∧
          h p.1 z₁ = a ∧ h p.1 z₂ = b ∧ M+Buffer ≤ z₁ ∧ z₂ ≤ 2*M-Buffer ∧
          z₁+N/4 ≤ (n:ℝ)*(p.2-6:ℤ)-2*N ∧
            (n:ℝ)*(p.2-6:ℤ)-2*N ≤ z₂-N/4
      have hshift : (n:ℝ)*(p.2-6:ℤ)-2*N = (n:ℝ)*p.2-11*N/4 := by
        push_cast
        dsimp only [N]
        ring
      rw [hshift]
      exact hdata
  have hcover p (hp : p ∈ C) : p ∈ D ∨ (p.1,p.2-6) ∈ D := by
    rcases hsafe p hp with hh | hh
    · exact Or.inl (Finset.mem_filter.mpr ⟨Finset.mem_union_left _ hp,hh⟩)
    · exact Or.inr (Finset.mem_filter.mpr
        ⟨Finset.mem_union_right _ (Finset.mem_image.mpr ⟨p,hp,rfl⟩),hh⟩)
  refine ⟨D,Finset.filter_subset _ _,fun p hp => (Finset.mem_filter.mp hp).2,?_⟩
  have hsum := two_start_chunk_cover v C D n H (fun y L => (hH y L).2) hcover
  rw [eight_grid_sum_reindex D] at hsum
  exact hsum




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
        2*Buffer+2*Width+6*N :=
  HuxleyBufferedFamilyAssemblyScratch.eight_grid_endpoint_selection n hn (M:=M) (Buffer:=Buffer) (Width:=Width) hBuffer hWidth hroom


#print axioms eight_grid_endpoint_selection

/-- The original interval sum is covered by eight grids from ONE actual reference
system. Only the two global endpoint strips are charged. -/
theorem eventually_positive_difference_eight_grid_whole_sum_physical_sieve
    {σsrc csrc Usrc σ εloss : ℝ}
    (hσsrc : 0 < σsrc) (hcsrc : 0 < csrc) (hUsrc : 0 < Usrc)
    (hσ : 0 < σ) (hεloss : 0 < εloss)
    (hanchorBudget : csrc ≤ 4*modelPhaseThirdLower σ*σsrc/(σ*(σ+1)+3)) :
    let κ := modelPhaseThirdLower σ
    let Ratio := 18*Usrc^2/(σsrc*csrc*κ)
    let L := max (8*Ratio^2)
      (32*(modelPhaseJetCoefficient σ 3+1)*(3*Usrc/σsrc)/κ^2)
    ∃ Csrc η₀ a Cupper Clower Dupper Dlower C Dtype : ℝ,
      1 ≤ Csrc ∧ 0 < η₀ ∧ η₀ ≤ 1/8 ∧ 0 < a ∧
      0 < Cupper ∧ 0 < Clower ∧ 0 < Dupper ∧ 0 < Dlower ∧ 0 < C ∧ 0 < Dtype ∧
    ∀ {θ : ℝ}, 0 < θ → θ ≤ 1/24 → θ ≤ 1/(8*(L+3)) →
    ∀ᶠ T : ℝ in Filter.atTop, ∀ (Fsrc : ℝ → ℝ) (Y : Finset ℝ)
      (Q K₀ N Uref : ℕ) [NeZero K₀] (R Jsep : ℝ) {η M δ Bcut Bselect : ℝ},
    0 < η → η ≤ η₀ → 0 < T → 2 ≤ N →
    1 ≤ R → R ≤ M → 0 ≤ δ → δ ≤ min κ 1 →
    0 < Jsep → Jsep ≤ M →
    (∀ y ∈ Y, y ∈ Icc (1:ℝ) 2) →
    (∀ y ∈ Y, ∀ z ∈ Y, y ≠ z → 1 ≤ Jsep*|y-z|) →
    (∀ w, 0 < w → ContDiffAt ℝ ∞ Fsrc w) →
    (∀ w ∈ Icc (1/2:ℝ) 3, ∀ n ≤ 6, |iteratedDeriv (n+1) Fsrc w| ≤ Usrc) →
    (∀ w ∈ Icc (1/2:ℝ) 3, ∀ j,
      csrc ≤ |HuxleyModel.tests (fun i : Fin 4 => iteratedDeriv (i.val+3) Fsrc w) j|) →
    (∀ w ∈ Icc (1/2:ℝ) 3, iteratedDeriv 4 Fsrc w ≤ -csrc) →
    (∀ y ∈ Y, Expdb.IsApproximateModelPhaseFunction
      (fun u => (Fsrc u-Fsrc (u+η*y))/(σsrc*η)) σ 4 δ) →
    T*(N:ℝ)*R^2 = M^3 →
    7*(N:ℝ)+2 ≤ M/4 →
    (3*Usrc/σsrc)*(6*(N:ℝ)+1)^4 ≤ M*(N:ℝ)*R^2 →
    (3*Usrc/(4*σsrc))*(6*(N:ℝ)+1)^2 ≤ (N:ℝ)*R^2 →
    12*Usrc ≤ σsrc*(Uref:ℝ) →
    63*(Usrc/(2*σsrc*(N:ℝ)*R^2))*(Q:ℝ)*(N:ℝ)^2 ≤ K₀ →
    (Q:ℝ)*(N:ℝ) ≤ (K₀:ℝ)*R^2 →
    (N:ℝ)^4 ≤ M*R^3*(Real.log T)^((3:ℝ)/2) →
    1 ≤ Uref → 0 < Bcut →
    2+168/κ ≤ Bselect → 7*Bcut ≤ κ*Bselect →
    Bselect^2*(Uref:ℝ)^3*R^2 ≤ (N:ℝ)^2 →
    (Uref:ℝ) ≤ ((N:ℝ)/(Q:ℝ))^((2:ℝ)/3)/Bselect →
    ((N:ℝ)/(Q:ℝ))^((2:ℝ)/3)/(2*Bselect) ≤ (Uref:ℝ) →
    (N:ℝ)^10 ≤ M^3*R^7 →
    Q ≤ N → (N:ℝ)^2 ≤ M → (Uref:ℝ) ≤ R^2 →
    768*R ≤ (Q:ℝ) → (N:ℝ)*R ≤ M →
    let Cphys := σ*(σ+1)+1
    let c := κ/6
    let J := Cphys/6
    let B := max 1 (max (2*Real.sqrt J) (8*J*Real.sqrt J/(3*c)))
    B*R^2/(N:ℝ)^2 ≤ 1/2 →
    (N:ℝ) ≤ R^2 → R ≤ (N:ℝ) → (N:ℝ)^3 ≤ M*R^2 →
    2*R^2 ≤ (Q:ℝ)*(N:ℝ) →
    let Vscale := (Uref:ℝ)^((3:ℝ)/2)
    let lambda := csrc*κ*T/(12*Usrc*M^2)
    let Uband := (3*Usrc/σsrc)*T/(2*M^2)
    let ChartCap := (4/a+3)*((6*Usrc/σsrc)/a+3)*((4*σsrc/csrc)/a+3)
    let NarrowCap := (4/θ+3)*(72*Usrc^2/(σsrc*csrc*κ*θ)+3)
    let Cap := 3*ChartCap*NarrowCap
    let μ₀ := csrc*T/(12*σsrc*M^3)
    let U₀ := Usrc*T/(2*σsrc*M^3)
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
    let AupperConst := 2*Cupper*(Cthird+1)*1^2/(κ*Lunit^3)
    let BupperConst := Cupper*(Cthird+1)*1^2/Lunit^2+Dupper*(B+1)*1^2/4
    let AlowerConst := 8*Clower*(Cthird+1)/(κ*Lunit^3)
    let BlowerConst := 4*Clower*(Cthird+1)/Lunit^2+Dlower*(B+1)
    let DupperConst := θ*(3*Usrc/σsrc)*1/2
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

    let Buffer := (56*(Uref:ℝ)/κ)*(N:ℝ)+(N:ℝ)/(Cphys+2)+2
    let Dlog := 64*σsrc*R^2/(csrc*((Q:ℝ)/768))
    let Cerror := (768:ℝ)*((6*Usrc/σsrc)*(64*σsrc/csrc)^2+192*σsrc/csrc)+
      ((3*Usrc/σsrc+csrc/(32*σsrc))*((24576*σsrc)/csrc)^2+(24576*σsrc)/csrc)
    let Major := (Y.card:ℝ)*Cerror*(M*R/(Q:ℝ))*(2+Real.log (Dlog+1))
    let Error := (Y.card:ℝ)*(M/(N:ℝ)+1)*
      (Real.sqrt (3*(N:ℝ))*Real.log (6*(N:ℝ))+12*σsrc*R^2/(csrc*(N:ℝ)))
    let FamilyBound := (144*Usrc/(csrc*κ))^6*(R^2/(Q:ℝ))^6*
      C*(K₀:ℝ)^((12:ℝ)+εloss)*Cap^11*(10*(Y.card:ℝ)*(M/(N:ℝ)))^10*
        (Vscale*Dtype*(Y.card:ℝ)*(M/(N:ℝ))*(1+Δtype*Jsep)+
          (Y.card:ℝ)^2*(Vscale*(Kupper+Klower)+Klarge)*T^εloss)
    let f := fun y w => T*(Fsrc (w/M)-Fsrc (w/M+η*y))/(σsrc*η)
    ∀ n : ℕ, N = 8*n →
      2*(Buffer+(14*σsrc/csrc)*(Uref:ℝ)*(N:ℝ))+6*(N:ℝ) ≤ M →
      let Endpoint := (Y.card:ℝ)*
        (2*Buffer+2*((14*σsrc/csrc)*(Uref:ℝ)*(N:ℝ))+6*(N:ℝ))
      (∑ y ∈ Y, ‖∑ k ∈ Finset.Ioc ⌈M⌉ ⌊2*M⌋,(𝐞 (f y k):ℂ)‖)^12 ≤
        2^11*((32:ℝ)^12*
          (2^11*((Csrc*(Major+Error))^12+
            (Csrc*(1+Real.log K₀))^12*FamilyBound))+Endpoint^12)
 := by

  classical
  intro κ Ratio L
  obtain ⟨Csrc,η₀,aColor,Cupper,Clower,Dupper,Dlower,C,Dtype,
    hCsrc,hη₀,hηcap,haColor,hCU,hCL,hDU,hDL,hC,hDtype,hcore⟩ :=
    eventually_positive_difference_uniform_reference_core_physical_sieve
      hσsrc hcsrc hUsrc hσ hεloss hanchorBudget
  refine ⟨Csrc,η₀,aColor,Cupper,Clower,Dupper,Dlower,C,Dtype,
    hCsrc,hη₀,hηcap,haColor,hCU,hCL,hDU,hDL,hC,hDtype,?_⟩
  intro θ hθ hθmax hθaction
  filter_upwards [hcore hθ hθmax hθaction] with T hcoreT
  intro Fsrc Y Q K₀ N Uref instK R Jsep η M δ Bcut Bselect
    hη hηsmall hT hNtwo hR hRM hδzero hδ hJsep hJM hy hsepY
    hreg hjets htests hnegative hmodels hscale hpad hquartic hquad hUlarge
    hsourceMesh hmesh hregime hUref hBcut hBselectSize hcutMargin hselectedWrap
    hselectedUpper hUlo hscaleTen hQN hNsqM hUR hstrongRQ hNRM
    Cphys c J B hsmall hNR hRN hNcube hminscale
    Vscale lambda Uband ChartCap NarrowCap Cap μ₀ U₀ Δtype
    C₂ C₃ Ct Cc Δ Ccurv D Kres Esize Dbase Tbase hsize hD hΔ hBsize
    Lunit Gamma Cthird AupperConst BupperConst AlowerConst BlowerConst
    DupperConst DlowerConst CostUpper CostLower Cpack Cfirst Cgap Cmain Ctail
    Kupper Klower Klarge Buffer Dlog Cerror Major Error FamilyBound f
    n hNlink hroom EndpointBound
  have hUlarge₃ : 3*Usrc ≤ σsrc*(Uref:ℝ) := by linarith only [hUlarge,hUsrc]
  obtain ⟨Refs,hRefSep,hRefGap,henclose,hroots,hgrid⟩ :=
    hcoreT Fsrc Y Q K₀ N Uref R Jsep (η:=η) (M:=M) (δ:=δ)
      (Bcut:=Bcut) (Bselect:=Bselect)
      hη hηsmall hT hNtwo hR hRM hδzero hδ hJsep hJM hy hsepY
      hreg hjets htests hnegative hmodels hscale hpad hquartic hquad hUlarge₃
      hsourceMesh hmesh hregime hUref hBcut hBselectSize hcutMargin hselectedWrap
      hselectedUpper hUlo hscaleTen hQN hNsqM hUR hstrongRQ hNRM
      hsmall hNR hRN hNcube hminscale hsize hD hΔ hBsize
  have hn : 0 < n := by omega
  have hNreal : (N:ℝ) = 8*(n:ℝ) := by exact_mod_cast hNlink
  have hNint : (N:ℤ) = 8*(n:ℤ) := by exact_mod_cast hNlink
  have hNpos : (0:ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hM : 0 < M := by nlinarith only [hNpos,hNsqM]
  have hRpos : 0 < R := zero_lt_one.trans_le hR
  have hκ : 0 < κ := modelPhaseThirdLower_pos hσ
  have hCphys : 0 < Cphys := by dsimp only [Cphys]; positivity
  have hBuffer : 0 ≤ Buffer := by dsimp only [Buffer]; positivity
  let Width := (14*σsrc/csrc)*(Uref:ℝ)*(N:ℝ)
  have hWidth : 0 ≤ Width := by dsimp only [Width]; positivity
  have hroom' : 2*(Buffer+Width)+6*(8*(n:ℝ)) ≤ M := by
    rw [←hNreal]
    exact hroom
  obtain ⟨a,b,ha,hab,hb,hdeepRaw,hEndcost⟩ :=
    eight_grid_endpoint_selection n hn hBuffer hWidth hroom'
  have hdeep : ∀ m ∈ Finset.Ico a b, (n:ℝ)*m ∈
      Icc (M+Buffer+Width+4*(N:ℝ)) (2*M-Buffer-Width-(N:ℝ)) := by
    simpa only [←hNreal] using hdeepRaw
  have hEndcost' : ((((n:ℤ)*a-⌈M⌉:ℤ):ℝ)+((⌊2*M⌋-(n:ℤ)*b:ℤ):ℝ)) ≤
      2*Buffer+2*Width+6*(N:ℝ) := by
    simpa only [←hNreal] using hEndcost
  let A : ℤ := ⌈M⌉
  let Bleft : ℤ := ⌊2*M⌋
  let Endpoint := (Y.card:ℝ)*((((n:ℤ)*a-A:ℤ):ℝ)+((Bleft-(n:ℤ)*b:ℤ):ℝ))
  have hEndpointLe : Endpoint ≤ EndpointBound :=
    mul_le_mul_of_nonneg_left hEndcost' (Nat.cast_nonneg _)
  have hscale' : T*(8*(n:ℝ))*R^2 = M^3 := by rw [←hNreal]; exact hscale
  obtain ⟨H,hH,hcover⟩ := positive_difference_eight_grid_chunk_cover Fsrc Y Refs n
    hn hσsrc hcsrc hUsrc hη (hηsmall.trans hηcap) hy hreg hjets hnegative
    hT hM hRpos hscale' hRefSep hRefGap hUlarge hBuffer henclose hroots
  let Chunks := Y ×ˢ Finset.Ico a b
  have hChunks p (hp : p ∈ Chunks) : p.1 ∈ Y := (Finset.mem_product.mp hp).1
  have hDeep p (hp : p ∈ Chunks) : (n:ℝ)*p.2 ∈
      Icc (M+Buffer+(14*σsrc/csrc)*(Uref:ℝ)*(8*(n:ℝ))+4*(8*(n:ℝ)))
        (2*M-Buffer-(14*σsrc/csrc)*(Uref:ℝ)*(8*(n:ℝ))-(8*(n:ℝ))) := by
    rw [←hNreal]
    exact hdeep p.2 (Finset.mem_product.mp hp).2
  obtain ⟨Dcover,hDsub,hDgood,hChunksBound⟩ := hcover Chunks hChunks hDeep
  let Grid := fun r : ℤ =>
    (Dcover.filter (fun p => p.2%8 = r)).image (fun p => (p.1,p.2/8-2))
  let X := fun r : ℤ => ∑ p ∈ Grid r,
    ‖∑ k ∈ Finset.Ioc ((n:ℤ)*(r+8*p.2+16))
      ((n:ℤ)*(r+8*p.2+16)+(H p.1 ((n:ℤ)*(r+8*p.2+16)):ℤ)),
        (𝐞 (f p.1 k):ℂ)‖
  let CoreBound := 2^11*((Csrc*(Major+Error))^12+
    (Csrc*(1+Real.log K₀))^12*FamilyBound)
  have hDphase q (hq : q ∈ Dcover) : q.1 ∈ Y := by
    rcases Finset.mem_union.mp (hDsub hq) with hh | hh
    · exact hChunks q hh
    · obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hh
      exact hChunks p hp
  have hLgrid (r k : ℤ) :
      r*(n:ℤ)+(N:ℤ)*k+2*(N:ℤ) = (n:ℤ)*(r+8*k+16) := by
    rw [hNint]
    ring
  have hXbound (r : ℤ) : (X r)^12 ≤ CoreBound := by
    let Hgrid := fun y k => H y (r*(n:ℤ)+(N:ℤ)*k+2*(N:ℤ))
    have hHgrid y (_hy : y ∈ Y) k : Hgrid y k ≤ N := by
      rw [hNlink]
      exact hH y _
    have hx := hgrid (r*(n:ℤ)) Hgrid hHgrid (Grid r)
    have hGoodGrid : ∀ p ∈ Grid r, p.1 ∈ Y ∧
        ∃ a ∈ Refs, ∃ b ∈ Refs, a < b ∧ (∀ q ∈ Refs,¬(a < q ∧ q < b)) ∧
          ∃ z₁ z₂ : ℝ, z₁ ∈ Icc M (2*M) ∧ z₂ ∈ Icc M (2*M) ∧
            iteratedDeriv 2 (f p.1) z₁/2 = a ∧ iteratedDeriv 2 (f p.1) z₂/2 = b ∧
            M+Buffer ≤ z₁ ∧ z₂ ≤ 2*M-Buffer ∧
            z₁+(N:ℝ)/4 ≤ (r*(n:ℤ):ℤ)+(N:ℝ)*p.2 ∧
              (r*(n:ℤ):ℤ)+(N:ℝ)*p.2 ≤ z₂-(N:ℝ)/4 := by
      intro p hp
      obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hp
      obtain ⟨hqD,hqmod⟩ := Finset.mem_filter.mp hq
      refine ⟨hDphase q hqD,?_⟩
      have hdecomp : (q.2:ℝ) = (r:ℝ)+8*((q.2/8-2:ℤ):ℝ)+16 := by
        exact_mod_cast (show q.2 = r+8*(q.2/8-2)+16 by omega)
      have htEq : ((r*(n:ℤ):ℤ):ℝ)+(N:ℝ)*((q.2/8-2:ℤ):ℝ) =
          (n:ℝ)*q.2-2*(N:ℝ) := by
        rw [hNreal,hdecomp]
        push_cast
        ring
      dsimp only
      rw [htEq,hNreal]
      exact hDgood q hqD
    have hh := hx hGoodGrid
    change (∑ p ∈ Grid r,
      ‖∑ k ∈ Finset.Ioc (r*(n:ℤ)+(N:ℤ)*p.2+2*(N:ℤ))
        (r*(n:ℤ)+(N:ℤ)*p.2+2*(N:ℤ)+(Hgrid p.1 p.2:ℤ)),
        (𝐞 (f p.1 k):ℂ)‖)^12 ≤ CoreBound at hh
    simpa only [X,Hgrid,hLgrid] using hh
  have hXnonneg r : 0 ≤ X r := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  let Grids := Finset.Ico (0:ℤ) 8
  have hGridCard : Grids.card = 8 := by decide
  have hholder := Real.rpow_sum_le_const_mul_sum_rpow_of_nonneg Grids
    (f:=X) (p:=(12:ℝ)) (by norm_num) (fun r _ => hXnonneg r)
  have hh : (∑ r ∈ Grids,X r)^12 ≤ (8:ℝ)^11*∑ r ∈ Grids,(X r)^12 := by
    simpa only [hGridCard,Nat.cast_ofNat,
      show (12:ℝ)-1 = 11 by norm_num,Real.rpow_ofNat] using hholder
  have hs : (∑ r ∈ Grids,(X r)^12) ≤ 8*CoreBound := by
    calc
      _ ≤ ∑ _r ∈ Grids,CoreBound := Finset.sum_le_sum (fun r _ => hXbound r)
      _ = _ := by simp only [Finset.sum_const,hGridCard,nsmul_eq_mul,Nat.cast_ofNat]
  have hGridPower : (4*∑ r ∈ Grids,X r)^12 ≤ (32:ℝ)^12*CoreBound := by
    rw [mul_pow]
    calc
      _ ≤ (4:ℝ)^12*((8:ℝ)^11*(8*CoreBound)) :=
        mul_le_mul_of_nonneg_left
          (hh.trans (mul_le_mul_of_nonneg_left hs (by norm_num))) (by norm_num)
      _ = _ := by generalize CoreBound = Z; ring
  let Orig := ∑ y ∈ Y, ‖∑ k ∈ Finset.Ioc A Bleft,(𝐞 (f y k):ℂ)‖
  have hOrig : 0 ≤ Orig := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  have hEndpoint : 0 ≤ Endpoint := by
    apply mul_nonneg (Nat.cast_nonneg _)
    exact add_nonneg (by exact_mod_cast (sub_nonneg.mpr ha))
      (by exact_mod_cast (sub_nonneg.mpr hb))
  have hwhole : Orig ≤
      (∑ p ∈ Chunks, ‖∑ k ∈ Finset.Ioc ((n:ℤ)*p.2) ((n:ℤ)*(p.2+1)),
        (𝐞 (f p.1 k):ℂ)‖)+Endpoint := by
    have hs := Finset.sum_le_sum (fun y (_hy : y ∈ Y) =>
      integer_whole_sum_le_chunks_and_endpoints (fun k => (𝐞 (f y k):ℂ)) n
        ha hab hb (fun _ _ => by simp))
    change Orig ≤ _ at hs
    convert hs using 1
    simp only [Chunks,Endpoint,Finset.sum_product,Finset.sum_add_distrib,Finset.sum_const,
      nsmul_eq_mul]
    ring
  have hOrigGrid : Orig ≤ (4*∑ r ∈ Grids,X r)+Endpoint :=
    hwhole.trans (add_le_add hChunksBound le_rfl)
  have hGridNN : 0 ≤ 4*∑ r ∈ Grids,X r :=
    mul_nonneg (by norm_num) (Finset.sum_nonneg (fun r _ => hXnonneg r))
  calc
    Orig^12 ≤ ((4*∑ r ∈ Grids,X r)+Endpoint)^12 :=
      pow_le_pow_left₀ hOrig hOrigGrid 12
    _ ≤ 2^11*((4*∑ r ∈ Grids,X r)^12+Endpoint^12) :=
      add_pow_le hGridNN hEndpoint 12
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (add_le_add hGridPower (pow_le_pow_left₀ hEndpoint hEndpointLe 12)) (by norm_num)

example
    {σsrc csrc Usrc σ εloss : ℝ}
    (hσsrc : 0 < σsrc) (hcsrc : 0 < csrc) (hUsrc : 0 < Usrc)
    (hσ : 0 < σ) (hεloss : 0 < εloss)
    (hanchorBudget : csrc ≤ 4*modelPhaseThirdLower σ*σsrc/(σ*(σ+1)+3)) :
    let κ := modelPhaseThirdLower σ
    let Ratio := 18*Usrc^2/(σsrc*csrc*κ)
    let L := max (8*Ratio^2)
      (32*(modelPhaseJetCoefficient σ 3+1)*(3*Usrc/σsrc)/κ^2)
    ∃ Csrc η₀ a Cupper Clower Dupper Dlower C Dtype : ℝ,
      1 ≤ Csrc ∧ 0 < η₀ ∧ η₀ ≤ 1/8 ∧ 0 < a ∧
      0 < Cupper ∧ 0 < Clower ∧ 0 < Dupper ∧ 0 < Dlower ∧ 0 < C ∧ 0 < Dtype ∧
    ∀ {θ : ℝ}, 0 < θ → θ ≤ 1/24 → θ ≤ 1/(8*(L+3)) →
    ∀ᶠ T : ℝ in Filter.atTop, ∀ (Fsrc : ℝ → ℝ) (Y : Finset ℝ)
      (Q K₀ N Uref : ℕ) [NeZero K₀] (R Jsep : ℝ) {η M δ Bcut Bselect : ℝ},
    0 < η → η ≤ η₀ → 0 < T → 2 ≤ N →
    1 ≤ R → R ≤ M → 0 ≤ δ → δ ≤ min κ 1 →
    0 < Jsep → Jsep ≤ M →
    (∀ y ∈ Y, y ∈ Icc (1:ℝ) 2) →
    (∀ y ∈ Y, ∀ z ∈ Y, y ≠ z → 1 ≤ Jsep*|y-z|) →
    (∀ w, 0 < w → ContDiffAt ℝ ∞ Fsrc w) →
    (∀ w ∈ Icc (1/2:ℝ) 3, ∀ n ≤ 6, |iteratedDeriv (n+1) Fsrc w| ≤ Usrc) →
    (∀ w ∈ Icc (1/2:ℝ) 3, ∀ j,
      csrc ≤ |HuxleyModel.tests (fun i : Fin 4 => iteratedDeriv (i.val+3) Fsrc w) j|) →
    (∀ w ∈ Icc (1/2:ℝ) 3, iteratedDeriv 4 Fsrc w ≤ -csrc) →
    (∀ y ∈ Y, Expdb.IsApproximateModelPhaseFunction
      (fun u => (Fsrc u-Fsrc (u+η*y))/(σsrc*η)) σ 4 δ) →
    T*(N:ℝ)*R^2 = M^3 →
    7*(N:ℝ)+2 ≤ M/4 →
    (3*Usrc/σsrc)*(6*(N:ℝ)+1)^4 ≤ M*(N:ℝ)*R^2 →
    (3*Usrc/(4*σsrc))*(6*(N:ℝ)+1)^2 ≤ (N:ℝ)*R^2 →
    12*Usrc ≤ σsrc*(Uref:ℝ) →
    63*(Usrc/(2*σsrc*(N:ℝ)*R^2))*(Q:ℝ)*(N:ℝ)^2 ≤ K₀ →
    (Q:ℝ)*(N:ℝ) ≤ (K₀:ℝ)*R^2 →
    (N:ℝ)^4 ≤ M*R^3*(Real.log T)^((3:ℝ)/2) →
    1 ≤ Uref → 0 < Bcut →
    2+168/κ ≤ Bselect → 7*Bcut ≤ κ*Bselect →
    Bselect^2*(Uref:ℝ)^3*R^2 ≤ (N:ℝ)^2 →
    (Uref:ℝ) ≤ ((N:ℝ)/(Q:ℝ))^((2:ℝ)/3)/Bselect →
    ((N:ℝ)/(Q:ℝ))^((2:ℝ)/3)/(2*Bselect) ≤ (Uref:ℝ) →
    (N:ℝ)^10 ≤ M^3*R^7 →
    Q ≤ N → (N:ℝ)^2 ≤ M → (Uref:ℝ) ≤ R^2 →
    768*R ≤ (Q:ℝ) → (N:ℝ)*R ≤ M →
    let Cphys := σ*(σ+1)+1
    let c := κ/6
    let J := Cphys/6
    let B := max 1 (max (2*Real.sqrt J) (8*J*Real.sqrt J/(3*c)))
    B*R^2/(N:ℝ)^2 ≤ 1/2 →
    (N:ℝ) ≤ R^2 → R ≤ (N:ℝ) → (N:ℝ)^3 ≤ M*R^2 →
    2*R^2 ≤ (Q:ℝ)*(N:ℝ) →
    let Vscale := (Uref:ℝ)^((3:ℝ)/2)
    let lambda := csrc*κ*T/(12*Usrc*M^2)
    let Uband := (3*Usrc/σsrc)*T/(2*M^2)
    let ChartCap := (4/a+3)*((6*Usrc/σsrc)/a+3)*((4*σsrc/csrc)/a+3)
    let NarrowCap := (4/θ+3)*(72*Usrc^2/(σsrc*csrc*κ*θ)+3)
    let Cap := 3*ChartCap*NarrowCap
    let μ₀ := csrc*T/(12*σsrc*M^3)
    let U₀ := Usrc*T/(2*σsrc*M^3)
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
    let AupperConst := 2*Cupper*(Cthird+1)*1^2/(κ*Lunit^3)
    let BupperConst := Cupper*(Cthird+1)*1^2/Lunit^2+Dupper*(B+1)*1^2/4
    let AlowerConst := 8*Clower*(Cthird+1)/(κ*Lunit^3)
    let BlowerConst := 4*Clower*(Cthird+1)/Lunit^2+Dlower*(B+1)
    let DupperConst := θ*(3*Usrc/σsrc)*1/2
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

    let Buffer := (56*(Uref:ℝ)/κ)*(N:ℝ)+(N:ℝ)/(Cphys+2)+2
    let Dlog := 64*σsrc*R^2/(csrc*((Q:ℝ)/768))
    let Cerror := (768:ℝ)*((6*Usrc/σsrc)*(64*σsrc/csrc)^2+192*σsrc/csrc)+
      ((3*Usrc/σsrc+csrc/(32*σsrc))*((24576*σsrc)/csrc)^2+(24576*σsrc)/csrc)
    let Major := (Y.card:ℝ)*Cerror*(M*R/(Q:ℝ))*(2+Real.log (Dlog+1))
    let Error := (Y.card:ℝ)*(M/(N:ℝ)+1)*
      (Real.sqrt (3*(N:ℝ))*Real.log (6*(N:ℝ))+12*σsrc*R^2/(csrc*(N:ℝ)))
    let FamilyBound := (144*Usrc/(csrc*κ))^6*(R^2/(Q:ℝ))^6*
      C*(K₀:ℝ)^((12:ℝ)+εloss)*Cap^11*(10*(Y.card:ℝ)*(M/(N:ℝ)))^10*
        (Vscale*Dtype*(Y.card:ℝ)*(M/(N:ℝ))*(1+Δtype*Jsep)+
          (Y.card:ℝ)^2*(Vscale*(Kupper+Klower)+Klarge)*T^εloss)
    let f := fun y w => T*(Fsrc (w/M)-Fsrc (w/M+η*y))/(σsrc*η)
    ∀ n : ℕ, N = 8*n →
      2*(Buffer+(14*σsrc/csrc)*(Uref:ℝ)*(N:ℝ))+6*(N:ℝ) ≤ M →
      let Endpoint := (Y.card:ℝ)*
        (2*Buffer+2*((14*σsrc/csrc)*(Uref:ℝ)*(N:ℝ))+6*(N:ℝ))
      (∑ y ∈ Y, ‖∑ k ∈ Finset.Ioc ⌈M⌉ ⌊2*M⌋,(𝐞 (f y k):ℂ)‖)^12 ≤
        2^11*((32:ℝ)^12*
          (2^11*((Csrc*(Major+Error))^12+
            (Csrc*(1+Real.log K₀))^12*FamilyBound))+Endpoint^12)
 :=
  HuxleyBufferedFamilyAssemblyScratch.eventually_positive_difference_eight_grid_whole_sum_physical_sieve (σsrc:=σsrc) (csrc:=csrc) (Usrc:=Usrc) (σ:=σ) (εloss:=εloss) hσsrc hcsrc hUsrc hσ hεloss hanchorBudget


#print axioms two_probes_avoid_separated_set
#print axioms positive_difference_two_safe_block_starts
#print axioms finite_reference_safe_start_buffered_bracket
#print axioms positive_difference_two_buffered_block_starts
#print axioms finite_prefix_maximizers
#print axioms integer_subinterval_le_two_prefixes
#print axioms two_start_chunk_cover
#print axioms eight_grid_sum_reindex
#print axioms integer_chunk_partition
#print axioms integer_whole_sum_le_chunks_and_endpoints
#print axioms positive_difference_eight_grid_chunk_cover
#print axioms eventually_positive_difference_eight_grid_whole_sum_physical_sieve

end HuxleyBufferedFamilyAssemblyScratch
#print axioms HuxleyBufferedFamilyAssemblyScratch.eventually_positive_difference_buffered_source_physical_sieve

#print axioms HuxleyBufferedFamilyAssemblyScratch.actual_source_index_transport
#print axioms HuxleyBufferedFamilyAssemblyScratch.actual_source_dyadic_cubic_admissibility
#print axioms HuxleyBufferedFamilyAssemblyScratch.cubic_completion_point_error
#print axioms HuxleyBufferedFamilyAssemblyScratch.actual_source_grid_completion_error
#print axioms HuxleyBufferedFamilyAssemblyScratch.actual_source_family_card_bound_mono
