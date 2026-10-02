import TaoTrudgianYang2025.ExponentPairShiftUniformity
import TaoTrudgianYang2025.ExponentPairSourceWeyl
import GuthMaynard.ArithmeticCoefficients

/-! The actual two-step A-process phase entry. These are source bridges,
not a proof of the short-range Huxley table or of its family estimate. -/

noncomputable section
open Expdb TaoTrudgianYang2025
open scoped BigOperators
namespace HuxleyDoubleShiftScratch

private theorem twice_shift_uniform_model {σ ε : ℝ}
    (hσ : 0 < σ) (P : ℕ) (hε : 0 < ε) :
    ∃ δ η₀ : ℝ, 0 < δ ∧ 0 < η₀ ∧ η₀ ≤ 1/2 ∧
      ∀ (F : ℝ → ℝ) (η ξ : ℝ),
        IsApproximateModelPhaseFunction F σ (P+2) δ →
        0 < η → η ≤ η₀ → 0 < ξ → ξ ≤ η₀ →
        IsApproximateModelPhaseFunction
          (aProcessShiftPhase (aProcessShiftPhase F σ η) (σ+1) ξ)
          (σ+2) P ε := by
  obtain ⟨δ₂,η₂,hδ₂,hη₂,hη₂half,hmodel₂⟩ :=
    aProcessShiftPhase_uniform_model (by linarith : 0 < σ+1) P hε
  obtain ⟨δ₁,η₁,hδ₁,hη₁,hη₁half,hmodel₁⟩ :=
    aProcessShiftPhase_uniform_model hσ (P+1) hδ₂
  refine ⟨δ₁,min η₁ η₂,hδ₁,lt_min hη₁ hη₂,
    (min_le_left _ _).trans hη₁half,?_⟩
  intro F η ξ hF hη hηcap hξ hξcap
  have hfirst := hmodel₁ F η (by simpa only [Nat.add_assoc] using hF)
    hη (hηcap.trans (min_le_left _ _))
  have hsecond := hmodel₂ (aProcessShiftPhase F σ η) ξ hfirst
    hξ (hξcap.trans (min_le_right _ _))
  simpa only [show σ+1+1=σ+2 by ring] using hsecond

private theorem twice_shift_physical {F : ℝ → ℝ} {σ X M r s m : ℝ}
    (hM : M ≠ 0) (hMr : M-r ≠ 0) (hMrs : M-r-s ≠ 0)
    (hσ : σ ≠ 0) (hσ₁ : σ+1 ≠ 0) (hr : r ≠ 0) (hs : s ≠ 0) :
    ((σ+1)*(σ*X*r/M)*s/(M-r)) *
        aProcessShiftPhase (aProcessShiftPhase F σ (r/M)) (σ+1)
          (s/(M-r)) ((m-r-s)/(M-r-s)) =
      X*(F (m/M)-F ((m+r)/M)-F ((m+s)/M)+F ((m+r+s)/M)) := by
  have hsecond := aProcessShiftPhase_physical
    (F:=aProcessShiftPhase F σ (r/M)) (σ:=σ+1)
    (T:=σ*X*r/M) (N:=M-r) (r:=s) (m:=m-r) hMr hMrs hσ₁ hs
  have hfirst := aProcessShiftPhase_physical
    (F:=F) (σ:=σ) (T:=X) (N:=M) (r:=r) (m:=m) hM hMr hσ hr
  have hfirstShift := aProcessShiftPhase_physical
    (F:=F) (σ:=σ) (T:=X) (N:=M) (r:=r) (m:=m+s) hM hMr hσ hr
  rw [hsecond,mul_sub,hfirst]
  rw [show m-r+s=m+s-r by ring,hfirstShift]
  rw [show m+s+r=m+r+s by ring]
  ring

example {σ ε : ℝ}
    (hσ : 0 < σ) (P : ℕ) (hε : 0 < ε) :
    ∃ δ η₀ : ℝ, 0 < δ ∧ 0 < η₀ ∧ η₀ ≤ 1/2 ∧
      ∀ (F : ℝ → ℝ) (η ξ : ℝ),
        IsApproximateModelPhaseFunction F σ (P+2) δ →
        0 < η → η ≤ η₀ → 0 < ξ → ξ ≤ η₀ →
        IsApproximateModelPhaseFunction
          (aProcessShiftPhase (aProcessShiftPhase F σ η) (σ+1) ξ)
          (σ+2) P ε :=
  HuxleyDoubleShiftScratch.twice_shift_uniform_model (σ:=σ) (ε:=ε) hσ P hε

example {F : ℝ → ℝ} {σ X M r s m : ℝ}
    (hM : M ≠ 0) (hMr : M-r ≠ 0) (hMrs : M-r-s ≠ 0)
    (hσ : σ ≠ 0) (hσ₁ : σ+1 ≠ 0) (hr : r ≠ 0) (hs : s ≠ 0) :
    ((σ+1)*(σ*X*r/M)*s/(M-r)) *
        aProcessShiftPhase (aProcessShiftPhase F σ (r/M)) (σ+1)
          (s/(M-r)) ((m-r-s)/(M-r-s)) =
      X*(F (m/M)-F ((m+r)/M)-F ((m+s)/M)+F ((m+r+s)/M)) :=
  HuxleyDoubleShiftScratch.twice_shift_physical (F:=F) (σ:=σ) (X:=X) (M:=M) (r:=r) (s:=s) (m:=m) hM hMr hMrs hσ hσ₁ hr hs

#print axioms twice_shift_uniform_model
#print axioms twice_shift_physical

private theorem product_fiber_card_le_divisors (S : Finset (ℕ × ℕ))
    {l : ℕ} (hl : 0 < l) :
    (S.filter (fun p => p.1*p.2=l)).card ≤ l.divisors.card := by
  classical
  apply Finset.card_le_card_of_injOn (fun p : ℕ × ℕ => p.1)
  · intro p hp
    have he := (Finset.mem_filter.mp hp).2
    exact Nat.mem_divisors.mpr ⟨⟨p.2,he.symm⟩,hl.ne'⟩
  · intro p hp q hq he
    have hp' := (Finset.mem_filter.mp hp).2
    have hq' := (Finset.mem_filter.mp hq).2
    have hpp : 0 < p.1 := by
      by_contra h
      have hz : p.1=0 := by omega
      simp [hz] at hp'
      omega
    apply Prod.ext he
    apply Nat.mul_left_cancel hpp
    calc
      p.1*p.2=l := hp'
      _=q.1*q.2 := hq'.symm
      _=p.1*q.2 := by rw [he]

/-- Select an ACTUAL member of each product fiber. No identification of
different phases with the same product is used. The uniform divisor
constant precedes the finite family and its complex values. -/
private theorem product_fiber_actual_maximum {ε : ℝ} (hε : 0 < ε) :
    ∃ D : ℝ, 0 < D ∧
    ∀ (S : Finset (ℕ × ℕ)) (W : (ℕ × ℕ) → ℂ) (L : ℝ),
      (∀ p∈S, 0 < p.1 ∧ 0 < p.2) →
      (∀ p∈S, (p.1*p.2:ℕ) ≤ L) →
      ∃ pick : ℕ → ℕ × ℕ,
        (∀ l∈S.image (fun p => p.1*p.2),
          pick l∈S ∧ (pick l).1*(pick l).2=l ∧
          ∀ p∈S, p.1*p.2=l → ‖W p‖ ≤ ‖W (pick l)‖) ∧
        (∑ p∈S, ‖W p‖) ≤
          D*L^ε*(∑ l∈S.image (fun p => p.1*p.2), ‖W (pick l)‖) := by
  classical
  obtain ⟨D,hD,hdiv⟩ := RiemannZeta.GuthMaynard.divisorCountBound_native ε hε
  refine ⟨D,hD,?_⟩
  intro S W L hpos hcap
  let products := S.image (fun p => p.1*p.2)
  have hex (l : ℕ) : ∃ p : ℕ × ℕ, l∈products →
      p∈S ∧ p.1*p.2=l ∧ ∀ q∈S, q.1*q.2=l → ‖W q‖ ≤ ‖W p‖ := by
    by_cases hl : l∈products
    · obtain ⟨q,hq,heq⟩ := Finset.mem_image.mp hl
      have hn : (S.filter (fun p => p.1*p.2=l)).Nonempty :=
        ⟨q,Finset.mem_filter.mpr ⟨hq,heq⟩⟩
      obtain ⟨p,hp,hmax⟩ := Finset.exists_max_image _ (fun p => ‖W p‖) hn
      refine ⟨p,fun _ => ⟨(Finset.mem_filter.mp hp).1,
        (Finset.mem_filter.mp hp).2,?_⟩⟩
      intro q hq he
      exact hmax q (Finset.mem_filter.mpr ⟨hq,he⟩)
    · exact ⟨(1,1),fun h => (hl h).elim⟩
  choose pick hpick using hex
  refine ⟨pick,hpick,?_⟩
  have hfiber (l : ℕ) (hl : l∈products) :
      (∑ p∈S.filter (fun p => p.1*p.2=l), ‖W p‖) ≤
        D*L^ε*‖W (pick l)‖ := by
    obtain ⟨hp,he,hmax⟩ := hpick l hl
    have hpp := hpos (pick l) hp
    have hlpos : 0 < l := he ▸ Nat.mul_pos hpp.1 hpp.2
    have hlcap : (l:ℝ) ≤ L := by simpa only [he] using hcap (pick l) hp
    have hcard : ((S.filter (fun p => p.1*p.2=l)).card:ℝ) ≤ D*L^ε := by
      calc
        _ ≤ (l.divisors.card:ℝ) := by
          exact_mod_cast product_fiber_card_le_divisors S hlpos
        _ ≤ D*(l:ℝ)^ε := hdiv l hlpos
        _ ≤ D*L^ε := mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow (Nat.cast_nonneg _) hlcap hε.le) hD.le
    calc
      _ ≤ ∑ _p∈S.filter (fun p => p.1*p.2=l), ‖W (pick l)‖ := by
        apply Finset.sum_le_sum
        intro p hp
        exact hmax p (Finset.mem_filter.mp hp).1 (Finset.mem_filter.mp hp).2
      _ = ((S.filter (fun p => p.1*p.2=l)).card:ℝ)*‖W (pick l)‖ := by simp
      _ ≤ _ := mul_le_mul_of_nonneg_right hcard (norm_nonneg _)
  calc
    _ = ∑ l∈products, ∑ p∈S.filter (fun p => p.1*p.2=l), ‖W p‖ := by
      symm
      exact Finset.sum_fiberwise_of_maps_to
        (fun p hp => Finset.mem_image_of_mem (fun p => p.1*p.2) hp) _
    _ ≤ ∑ l∈products, D*L^ε*‖W (pick l)‖ := Finset.sum_le_sum hfiber
    _ = _ := by rw [Finset.mul_sum]

#print axioms product_fiber_card_le_divisors
#print axioms product_fiber_actual_maximum

end HuxleyDoubleShiftScratch
