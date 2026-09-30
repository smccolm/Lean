import TaoTrudgianYang2025.HuxleyLinearForms

open Set TaoTrudgianYang2025 TaoTrudgianYang2025.HuxleyRationalPhase
open scoped ContDiff BigOperators FourierTransform Classical

namespace HuxleyReferenceInteriorScratch

private theorem affine_endpoint_factor_two
    {r e q ε : ℝ} (hε : 0 ≤ ε)
    (hcentral : 3*|r| *ε < r*q-e) :
    0 < r*(q-ε)-e ∧ 0 < r*(q+ε)-e ∧
      max (r*(q-ε)-e) (r*(q+ε)-e) ≤
        2*min (r*(q-ε)-e) (r*(q+ε)-e) := by
  have hsmall : 0 ≤ |r| *ε := mul_nonneg (abs_nonneg r) hε
  have hlo := mul_le_mul_of_nonneg_right (neg_abs_le r) hε
  have hhi := mul_le_mul_of_nonneg_right (le_abs_self r) hε
  have hlow : 0 < r*(q-ε)-e := by nlinarith only [hcentral,hsmall,hhi]
  have hupp : 0 < r*(q+ε)-e := by nlinarith only [hcentral,hsmall,hlo]
  refine ⟨hlow,hupp,?_⟩
  rw [mul_min_of_nonneg _ _ (by norm_num : (0:ℝ) ≤ 2)]
  apply max_le
  · apply le_min
    · linarith only [hlow]
    · nlinarith only [hcentral,hlo]
  · apply le_min
    · nlinarith only [hcentral,hhi]
    · linarith only [hupp]

/-- Removing at most six actual physical windows near the two reference
endpoints produces interior inverse-Farey intervals with positive
denominators and factor-two denominator variation. These geometric
conditions are outputs of the actual model and reference orientation. -/
theorem physicalModelPhase_reference_gap_interior_chart_selection
    (S : Finset ℕ) (x : ℕ → ℝ)
    {σ δ T M A W N R base a b e r : ℝ} {F : ℝ → ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseThirdLower σ) 1)
    (hF : Expdb.IsApproximateModelPhaseFunction F σ 2 δ)
    (hT : 0 < T) (hM : 0 < M) (hN : 0 < N) (hR : 0 < R)
    (hA : M ≤ A) (hW : A+W ≤ 2*M)
    (hphase : T*N*R^2=M^3)
    (horientation : (0 < r ∧ e/r=a) ∨ (r < 0 ∧ e/r=b))
    (hx : ∀ j∈S, x j∈Ioo 0 W)
    (hwindow : ∀ j∈S, x j∈Icc (base+(j:ℝ)*N) (base+((j:ℝ)+1)*N)) :
    let ε := modelPhaseThirdLower σ/(16*(σ*(σ+1)+1+2)*R^2)
    let f := heathBrownPhysicalPhase F T M A 1
    let q := fun j => iteratedDeriv 2 f (x j)/2
    (∀ j∈S, q j∈Icc a b) →
    ∃ S₀ : Finset ℕ, S₀⊆S ∧ S.card ≤ 6+S₀.card ∧ ∀ j∈S₀,
      a+3*ε < q j ∧ q j < b-3*ε ∧
      0 < r*(q j-ε)-e ∧ 0 < r*(q j+ε)-e ∧
      max (r*(q j-ε)-e) (r*(q j+ε)-e) ≤
        2*min (r*(q j-ε)-e) (r*(q j+ε)-e) ∧
      Icc (q j-ε) (q j+ε) ⊆ Icc a b := by
  classical
  intro ε f q hgap
  have hκ : 0 < modelPhaseThirdLower σ := modelPhaseThirdLower_pos hσ
  have hC : 0 < σ*(σ+1)+3 := by positivity
  have hε : 0 ≤ ε := by dsimp only [ε]; positivity
  let badA := S.filter (fun j => |q j-a| ≤ 3*ε)
  let badB := S.filter (fun j => |q j-b| ≤ 3*ε)
  let bad := fun j => |q j-a| ≤ 3*ε ∨ |q j-b| ≤ 3*ε
  let good := S.filter (fun j => ¬ bad j)
  have hrad : 4*(3*ε)*R^2 ≤ modelPhaseThirdLower σ := by
    have he : 4*(3*ε)*R^2=3*modelPhaseThirdLower σ/(4*(σ*(σ+1)+3)) := by
      dsimp only [ε]
      field_simp
      ring
    rw [he]
    apply (div_le_iff₀ (mul_pos (by norm_num) hC)).mpr
    have hh : 0 ≤ (σ*(σ+1))*modelPhaseThirdLower σ := by positivity
    nlinarith only [hh,hκ]
  have hcountA : badA.card ≤ 3 :=
    physicalModelPhase_curvature_boundary_window_count badA x
      hσ hδ hF hT hM hN hR hA hW hphase hrad
      (fun j hj => hx j (Finset.mem_filter.mp hj).1)
      (fun j hj => hwindow j (Finset.mem_filter.mp hj).1)
      (fun j hj => (Finset.mem_filter.mp hj).2)
  have hcountB : badB.card ≤ 3 :=
    physicalModelPhase_curvature_boundary_window_count badB x
      hσ hδ hF hT hM hN hR hA hW hphase hrad
      (fun j hj => hx j (Finset.mem_filter.mp hj).1)
      (fun j hj => hwindow j (Finset.mem_filter.mp hj).1)
      (fun j hj => (Finset.mem_filter.mp hj).2)
  have he : S.filter bad=badA∪badB := by
    ext j
    simp only [Finset.mem_filter,Finset.mem_union,bad,badA,badB]
    tauto
  have hbad : (S.filter bad).card ≤ 6 := by
    rw [he]
    exact (Finset.card_union_le _ _).trans (by omega)
  refine ⟨good,Finset.filter_subset _ _,?_,?_⟩
  · have hh := Finset.card_filter_add_card_filter_not (s:=S) bad
    change (S.filter bad).card+good.card=S.card at hh
    omega
  · intro j hj
    obtain ⟨hjS,hgood⟩ := Finset.mem_filter.mp hj
    have hleft : 3*ε < q j-a := by
      have hh : ¬ |q j-a| ≤ 3*ε := fun h => hgood (Or.inl h)
      rw [abs_of_nonneg (sub_nonneg.mpr (hgap j hjS).1)] at hh
      exact lt_of_not_ge hh
    have hright : 3*ε < b-q j := by
      have hh : ¬ |q j-b| ≤ 3*ε := fun h => hgood (Or.inr h)
      rw [abs_of_nonpos (sub_nonpos.mpr (hgap j hjS).2)] at hh
      linarith only [lt_of_not_ge hh]
    have hcentral : 3*|r| *ε < r*q j-e := by
      rcases horientation with ⟨hr,href⟩ | ⟨hr,href⟩
      · have heq : e=a*r := (div_eq_iff hr.ne').mp href
        rw [abs_of_pos hr,heq]
        nlinarith only [mul_lt_mul_of_pos_left hleft hr]
      · have heq : e=b*r := (div_eq_iff hr.ne).mp href
        rw [abs_of_neg hr,heq]
        nlinarith only [mul_lt_mul_of_pos_left hright (neg_pos.mpr hr)]
    obtain ⟨hlo,hhi,hratio⟩ := affine_endpoint_factor_two hε hcentral
    refine ⟨by linarith only [hleft],by linarith only [hright],hlo,hhi,hratio,?_⟩
    intro z hz
    constructor <;> linarith only [hleft,hright,hε,hz.1,hz.2]

example
    (S : Finset ℕ) (x : ℕ → ℝ)
    {σ δ T M A W N R base a b e r : ℝ} {F : ℝ → ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseThirdLower σ) 1)
    (hF : Expdb.IsApproximateModelPhaseFunction F σ 2 δ)
    (hT : 0 < T) (hM : 0 < M) (hN : 0 < N) (hR : 0 < R)
    (hA : M ≤ A) (hW : A+W ≤ 2*M)
    (hphase : T*N*R^2=M^3)
    (horientation : (0 < r ∧ e/r=a) ∨ (r < 0 ∧ e/r=b))
    (hx : ∀ j∈S, x j∈Ioo 0 W)
    (hwindow : ∀ j∈S, x j∈Icc (base+(j:ℝ)*N) (base+((j:ℝ)+1)*N)) :
    let ε := modelPhaseThirdLower σ/(16*(σ*(σ+1)+1+2)*R^2)
    let f := heathBrownPhysicalPhase F T M A 1
    let q := fun j => iteratedDeriv 2 f (x j)/2
    (∀ j∈S, q j∈Icc a b) →
    ∃ S₀ : Finset ℕ, S₀⊆S ∧ S.card ≤ 6+S₀.card ∧ ∀ j∈S₀,
      a+3*ε < q j ∧ q j < b-3*ε ∧
      0 < r*(q j-ε)-e ∧ 0 < r*(q j+ε)-e ∧
      max (r*(q j-ε)-e) (r*(q j+ε)-e) ≤
        2*min (r*(q j-ε)-e) (r*(q j+ε)-e) ∧
      Icc (q j-ε) (q j+ε) ⊆ Icc a b :=
  HuxleyReferenceInteriorScratch.physicalModelPhase_reference_gap_interior_chart_selection S x (σ:=σ) (δ:=δ) (T:=T) (M:=M) (A:=A) (W:=W) (N:=N) (R:=R) (base:=base) (a:=a) (b:=b) (e:=e) (r:=r) (F:=F) hσ hδ hF hT hM hN hR hA hW hphase horientation hx hwindow


end HuxleyReferenceInteriorScratch

#print axioms HuxleyReferenceInteriorScratch.affine_endpoint_factor_two
#print axioms HuxleyReferenceInteriorScratch.physicalModelPhase_reference_gap_interior_chart_selection
