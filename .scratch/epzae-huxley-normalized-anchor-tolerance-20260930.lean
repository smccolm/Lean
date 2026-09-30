import TaoTrudgianYang2025.HuxleyLinearForms
open Set
open scoped ContDiff FourierTransform BigOperators
open TaoTrudgianYang2025
open TaoTrudgianYang2025.HuxleyRationalPhase
namespace HuxleyAnchorToleranceScratch

private theorem normalized_source_anchor_tolerance
    {σ xi y₀ R Rnew c Cphys κ : ℝ}
    (hσ : 0 < σ) (hxi : 0 < xi) (hy₀ : 1 ≤ y₀)
    (hR : 0 < R) (hC : 0 ≤ Cphys) (hκ : 0 < κ)
    (hsq : Rnew^2=R^2*xi/(σ*y₀))
    (hc : c ≤ 4*κ*σ/(Cphys+2)) :
    c/(64*xi*R^2) ≤ κ/(16*(Cphys+2)*Rnew^2) := by
  have hypos : 0 < y₀ := zero_lt_one.trans_le hy₀
  have hCp : 0 < Cphys+2 := by linarith only [hC]
  have hnum : c*(Cphys+2) ≤ 4*κ*σ*y₀ :=
    ((le_div_iff₀ hCp).mp hc).trans
      (by nlinarith only [mul_le_mul_of_nonneg_left hy₀ (show 0 ≤ 4*κ*σ by positivity)])
  calc
    c/(64*xi*R^2) = (c*(Cphys+2))/(64*xi*R^2*(Cphys+2)) := by field_simp
    _ ≤ (4*κ*σ*y₀)/(64*xi*R^2*(Cphys+2)) :=
      div_le_div_of_nonneg_right hnum (by positivity)
    _ = κ/(16*(Cphys+2)*Rnew^2) := by rw [hsq]; field_simp; norm_num

theorem approximateModelPhase_enlarged_colored_linked_chart_source_tests
    {σ ε : ℝ} (hσ : 0 < σ) (P : ℕ) (hP : 5 ≤ P) (hε : 0 < ε) :
    ∃ δ η₀ a c J : ℝ, 0 < δ ∧ 0 < η₀ ∧ η₀ ≤ 1/8 ∧ 0 < a ∧ 0 < c ∧ 0 < J ∧
      ∀ (M : ℝ) (F : ℝ → ℝ), 1 ≤ M →
      Expdb.IsApproximateModelPhaseFunction F σ (P+2) δ →
      ∃ Fext : ℝ → ℝ,
        (∀ w, 0 < w → ContDiffAt ℝ ∞ Fext w) ∧
        (∀ w∈Icc (1/2:ℝ) 3, ∀ p ≤ P+1,
          |iteratedDeriv (p+1) Fext w-iteratedDeriv p (Expdb.modelPhase σ) w| ≤ ε) ∧
        (∀ x ∈ Icc (1/2:ℝ) 3, ∀ n ≤ 6, |iteratedDeriv (n+1) Fext x| ≤ J) ∧
        (∀ x ∈ Icc (1/2:ℝ) 3, ∀ j,
          c ≤ |TaoTrudgianYang2025.HuxleyModel.tests
            (fun i : Fin 4 => iteratedDeriv (i.val+3) Fext x) j|) ∧
        (∀ x ∈ Icc (1/2:ℝ) 3, iteratedDeriv 4 Fext x ≤ -c) ∧
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
            ∀ xi T N R : ℝ, 0 < xi → 0 < T → 0 < R → T*N*R^2=M^3 →
            let Tnew := T*σ*y i₀/xi
            let Rnew := R*Real.sqrt (xi/(σ*y i₀))
            0 < Tnew ∧ 0 < Rnew ∧ Rnew^2=R^2*xi/(σ*y i₀) ∧
              Tnew*N*Rnew^2=M^3 ∧
            c/(64*xi*R^2) ≤ TaoTrudgianYang2025.modelPhaseThirdLower (σ+1)/
              (16*((σ+1)*(σ+2)+3)*Rnew^2) ∧
            ∀ i∈S, color i=j →
              let G := fun u => (Fext u-Fext (u+η*y i))/(σ*η*y i₀)
              let f := fun w => T*(Fext (w/M)-Fext (w/M+η*y i))/(xi*η)
              Expdb.IsApproximateModelPhaseFunction G (σ+1) P ε ∧
                (∀ A x : ℝ, heathBrownPhysicalPhase G Tnew M A 1 x=f (A+x)) ∧
                (∀ (A : ℤ) (w : ℝ) (k : ℕ),
                  iteratedDeriv k (heathBrownPhysicalPhase G Tnew M A 1) (round (w-A))=
                    iteratedDeriv k f (round w)) := by
  obtain ⟨δ,η₀,a,c₀,J,hδ,hη₀,hηcap,ha,hc₀,hJ,hsource⟩ :=
    approximateModelPhase_enlarged_colored_linked_source_tests hσ P hP hε
  let κ := TaoTrudgianYang2025.modelPhaseThirdLower (σ+1)
  let Cphys := (σ+1)*(σ+2)+1
  have hκ : 0 < κ := TaoTrudgianYang2025.modelPhaseThirdLower_pos (by linarith only [hσ])
  have hCp : 0 < Cphys+2 := by dsimp only [Cphys]; positivity
  let c := min c₀ (4*κ*σ/(Cphys+2))
  have hc : 0 < c := lt_min hc₀ (by positivity)
  have hcc₀ : c ≤ c₀ := min_le_left _ _
  have hcbudget : c ≤ 4*κ*σ/(Cphys+2) := min_le_right _ _
  refine ⟨δ,η₀,a,c,J,hδ,hη₀,hηcap,ha,hc,hJ,?_⟩
  intro M F hM hF
  obtain ⟨Fext,hreg,hjets,hbound,htests,hnegative,hsharp,hcolors⟩ := hsource M F hM hF
  refine ⟨Fext,hreg,hjets,hbound,
    fun x hx j => hcc₀.trans (htests x hx j),
    fun x hx => (hnegative x hx).trans (neg_le_neg hcc₀),hsharp,?_⟩
  intro ι S y η hy hη hηmax color Cap
  obtain ⟨hcard,hmoment,hmodels⟩ := hcolors S y η hy hη hηmax
  refine ⟨hcard,hmoment,?_⟩
  intro j hj
  obtain ⟨i₀,hi₀,hcolor₀,hlinked⟩ := hmodels j hj
  refine ⟨i₀,hi₀,hcolor₀,?_⟩
  intro xi T N R hxi hT hR hscale Tnew Rnew
  obtain ⟨hTnew,hRnew,hRsq,hlink,hmodels₀⟩ := hlinked xi T N R hxi hT hR hscale
  refine ⟨hTnew,hRnew,hRsq,hlink,?_,hmodels₀⟩
  have ht := normalized_source_anchor_tolerance hσ hxi (hy i₀ hi₀).1 hR
    (show 0 ≤ Cphys by dsimp only [Cphys]; positivity) hκ hRsq hcbudget
  convert ht using 1; dsimp only [Cphys,κ]; ring

example
    {σ ε : ℝ} (hσ : 0 < σ) (P : ℕ) (hP : 5 ≤ P) (hε : 0 < ε) :
    ∃ δ η₀ a c J : ℝ, 0 < δ ∧ 0 < η₀ ∧ η₀ ≤ 1/8 ∧ 0 < a ∧ 0 < c ∧ 0 < J ∧
      ∀ (M : ℝ) (F : ℝ → ℝ), 1 ≤ M →
      Expdb.IsApproximateModelPhaseFunction F σ (P+2) δ →
      ∃ Fext : ℝ → ℝ,
        (∀ w, 0 < w → ContDiffAt ℝ ∞ Fext w) ∧
        (∀ w∈Icc (1/2:ℝ) 3, ∀ p ≤ P+1,
          |iteratedDeriv (p+1) Fext w-iteratedDeriv p (Expdb.modelPhase σ) w| ≤ ε) ∧
        (∀ x ∈ Icc (1/2:ℝ) 3, ∀ n ≤ 6, |iteratedDeriv (n+1) Fext x| ≤ J) ∧
        (∀ x ∈ Icc (1/2:ℝ) 3, ∀ j,
          c ≤ |TaoTrudgianYang2025.HuxleyModel.tests
            (fun i : Fin 4 => iteratedDeriv (i.val+3) Fext x) j|) ∧
        (∀ x ∈ Icc (1/2:ℝ) 3, iteratedDeriv 4 Fext x ≤ -c) ∧
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
            ∀ xi T N R : ℝ, 0 < xi → 0 < T → 0 < R → T*N*R^2=M^3 →
            let Tnew := T*σ*y i₀/xi
            let Rnew := R*Real.sqrt (xi/(σ*y i₀))
            0 < Tnew ∧ 0 < Rnew ∧ Rnew^2=R^2*xi/(σ*y i₀) ∧
              Tnew*N*Rnew^2=M^3 ∧
            c/(64*xi*R^2) ≤ TaoTrudgianYang2025.modelPhaseThirdLower (σ+1)/
              (16*((σ+1)*(σ+2)+3)*Rnew^2) ∧
            ∀ i∈S, color i=j →
              let G := fun u => (Fext u-Fext (u+η*y i))/(σ*η*y i₀)
              let f := fun w => T*(Fext (w/M)-Fext (w/M+η*y i))/(xi*η)
              Expdb.IsApproximateModelPhaseFunction G (σ+1) P ε ∧
                (∀ A x : ℝ, heathBrownPhysicalPhase G Tnew M A 1 x=f (A+x)) ∧
                (∀ (A : ℤ) (w : ℝ) (k : ℕ),
                  iteratedDeriv k (heathBrownPhysicalPhase G Tnew M A 1) (round (w-A))=
                    iteratedDeriv k f (round w)) :=
  HuxleyAnchorToleranceScratch.approximateModelPhase_enlarged_colored_linked_chart_source_tests (σ:=σ) (ε:=ε) hσ P hP hε


#print axioms normalized_source_anchor_tolerance
#print axioms approximateModelPhase_enlarged_colored_linked_chart_source_tests
end HuxleyAnchorToleranceScratch
