import TaoTrudgianYang2025.BetaCanonicalLegendre

/-!
# Finite canonical charts for arbitrary compact slope intervals

The ratio restriction is removed by a finite open cover of the original
compact slope interval. Every chart and its rescaling are chosen before
the derivative order, tolerance and source phase. A finite minimum gives
one positive source tolerance for all charts simultaneously.
-/

noncomputable section

open Set Expdb
open scoped ContDiff

namespace TaoTrudgianYang2025

def legendreWindowRadius (σ x : ℝ) : ℝ :=
  min ((x-(2 : ℝ)^(-σ))/4) (min ((1-x)/4) (x/4))

theorem legendreWindowRadius_properties {σ x : ℝ}
    (hx : x ∈ Ioo ((2 : ℝ)^(-σ)) 1) :
    0 < legendreWindowRadius σ x ∧
      (2 : ℝ)^(-σ) < x-legendreWindowRadius σ x ∧
      x+legendreWindowRadius σ x < 1 ∧
      x+legendreWindowRadius σ x < 2*(x-legendreWindowRadius σ x) := by
  have hx₀ : 0 < x :=
    (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) (-σ)).trans hx.1
  have hp : 0 < legendreWindowRadius σ x := by
    unfold legendreWindowRadius
    exact lt_min (by linarith [hx.1]) (lt_min (by linarith [hx.2]) (by linarith))
  have h₁ : legendreWindowRadius σ x ≤ (x-(2 : ℝ)^(-σ))/4 := min_le_left _ _
  have h₂ : legendreWindowRadius σ x ≤ (1-x)/4 :=
    (min_le_right _ _).trans (min_le_left _ _)
  have h₃ : legendreWindowRadius σ x ≤ x/4 :=
    (min_le_right _ _).trans (min_le_right _ _)
  exact ⟨hp,by linarith [hx.1],by linarith [hx.2],by linarith⟩

theorem modelPhaseLegendreDual_finite_canonical_cover
    {σ a b : ℝ} (hσ : 0 < σ)
    (ha : (2 : ℝ)^(-σ) < a) (hab : a ≤ b) (hb : b < 1) :
    ∃ S : Finset (Icc a b), S.Nonempty ∧
      ∃ l r A : Icc a b → ℝ, ∃ χ : Icc a b → ℝ → ℝ,
      (∀ i ∈ S, (2 : ℝ)^(-σ) < l i ∧ l i ≤ r i ∧ r i < 1 ∧
        0 < A i ∧ A i < l i ∧ r i < 2*A i ∧
        ContDiff ℝ ∞ (χ i) ∧ HasCompactSupport (χ i) ∧
        ∀ v ∈ Icc (l i) (r i), χ i v = 1) ∧
      (∀ v ∈ Icc a b, ∃ i ∈ S, v ∈ Ioo (l i) (r i)) ∧
      ∀ (Q : ℕ) (ε : ℝ), 0 < ε →
      ∃ δ : ℝ, 0 < δ ∧ δ ≤ min (modelPhaseCurvatureLower σ) 1 ∧
        ∀ F : ℝ → ℝ,
          IsApproximateModelPhaseFunction F σ (legendreFiniteInputOrder (Q+1)) δ →
        ∀ i ∈ S, Icc (l i) (r i) ⊆ modelPhaseSlopeRange F ∧
          IsApproximateModelPhaseFunction
            (canonicalLegendrePhase (χ i) F σ (A i) (l i)) σ⁻¹ Q ε ∧
          ∀ v ∈ Icc (l i) (r i), v/A i ∈ Ioo (1 : ℝ) 2 ∧
            canonicalLegendrePhase (χ i) F σ (A i) (l i) (v/A i) =
              (A i)^(σ⁻¹-1)*
                (modelPhaseLegendreDual F v-modelPhaseLegendreDual F (l i)) +
                referenceModelPrimitive σ⁻¹ (l i/A i) := by
  classical
  let l (i : Icc a b) := (i : ℝ)-legendreWindowRadius σ i
  let r (i : Icc a b) := (i : ℝ)+legendreWindowRadius σ i
  have hradius (i : Icc a b) := legendreWindowRadius_properties
    (show (i : ℝ) ∈ Ioo ((2 : ℝ)^(-σ)) 1 from
      ⟨ha.trans_le i.property.1,i.property.2.trans_lt hb⟩)
  have hl (i : Icc a b) : (2 : ℝ)^(-σ) < l i := (hradius i).2.1
  have hlr (i : Icc a b) : l i ≤ r i := by
    dsimp [l,r]
    linarith [(hradius i).1]
  have hr (i : Icc a b) : r i < 1 := (hradius i).2.2.1
  have hratio (i : Icc a b) : r i < 2*l i := (hradius i).2.2.2
  have hlocal (i : Icc a b) :=
    modelPhaseLegendreDual_canonical_extension hσ (hl i) (hlr i) (hr i) (hratio i)
  choose A hA hAl hrA χ hχ hcompact hplateau huniform using hlocal
  have hcover : Icc a b ⊆ ⋃ i : Icc a b, Ioo (l i) (r i) := by
    intro v hv
    refine mem_iUnion.mpr ⟨⟨v,hv⟩,?_⟩
    have hp := (hradius ⟨v,hv⟩).1
    change v-legendreWindowRadius σ v < v ∧ v < v+legendreWindowRadius σ v
    constructor <;> linarith
  obtain ⟨S,hS⟩ := isCompact_Icc.elim_finite_subcover
    (fun i => Ioo (l i) (r i)) (fun _ => isOpen_Ioo) hcover
  have hSne : S.Nonempty := by
    obtain ⟨i,hi,_⟩ := mem_iUnion₂.mp (hS (show a ∈ Icc a b from ⟨le_rfl,hab⟩))
    exact ⟨i,hi⟩
  refine ⟨S,hSne,l,r,A,χ,?_,?_,?_⟩
  · intro i _
    exact ⟨hl i,hlr i,hr i,hA i,hAl i,hrA i,hχ i,hcompact i,hplateau i⟩
  · intro v hv
    obtain ⟨i,hi,hv'⟩ := mem_iUnion₂.mp (hS hv)
    exact ⟨i,hi,hv'⟩
  · intro Q ε hε
    choose δ hδ hsmall hall using fun i => huniform i Q ε hε
    let δall := S.inf' hSne δ
    have hd : 0 < δall := (Finset.lt_inf'_iff hSne).mpr (fun i _ => hδ i)
    obtain ⟨i₀,hi₀⟩ := hSne
    have hsmallall : δall ≤ min (modelPhaseCurvatureLower σ) 1 :=
      (Finset.inf'_le δ hi₀).trans (hsmall i₀)
    refine ⟨δall,hd,hsmallall,?_⟩
    intro F hF i hi
    exact hall i F (approximateModelPhase_mono hF le_rfl (Finset.inf'_le δ hi))

end TaoTrudgianYang2025
