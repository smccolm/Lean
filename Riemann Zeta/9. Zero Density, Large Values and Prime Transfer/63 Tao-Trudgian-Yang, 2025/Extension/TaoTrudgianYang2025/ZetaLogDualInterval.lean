import TaoTrudgianYang2025.ZetaSharpLogReflection
import TaoTrudgianYang2025.PositiveSlopeChartFibers

/-!
# The literal natural-number interval returned by logarithmic reflection

The retained stationary frequencies are positive and consecutive.
Reindexing them uses their actual integer-to-natural map, preserving
the reciprocal weights and both endpoints, including the empty case.
-/

noncomputable section
open Set Complex
open scoped BigOperators
namespace TaoTrudgianYang2025

def zetaLogDualInterval (T N : ℝ) (a b : ℕ) : Finset ℕ :=
  (modelPhaseSharpStationarySet Real.log T N a b).image Int.toNat

theorem zetaLogDualInterval_window {T N : ℝ} {a b n : ℕ}
    (hT : 0 < T) (hN : 0 < N) (ha : N ≤ (a : ℝ)) (hb : (b : ℝ) ≤ 2*N)
    (hn : n ∈ zetaLogDualInterval T N a b) :
    T/(2*N) < (n : ℝ) ∧ (n : ℝ) < T/N := by
  obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hn
  have hwindow := logarithmicSharpStationarySet_window hT hN ha hb hq
  have hqpos : 0 < q := by
    exact_mod_cast (div_pos hT (by positivity : 0 < 2*N)).trans hwindow.1
  have hcast : (q.toNat : ℤ) = q := Int.toNat_of_nonneg hqpos.le
  have hr : (q.toNat : ℝ) = (q : ℝ) := by exact_mod_cast hcast
  simpa only [hr] using hwindow

theorem zetaLogDualInterval_positive {T N : ℝ} {a b n : ℕ}
    (hT : 0 < T) (hN : 0 < N) (ha : N ≤ (a : ℝ)) (hb : (b : ℝ) ≤ 2*N)
    (hn : n ∈ zetaLogDualInterval T N a b) : 0 < n := by
  have hw := zetaLogDualInterval_window hT hN ha hb hn
  exact_mod_cast (div_pos hT (by positivity : 0 < 2*N)).trans hw.1

theorem zetaLogDualInterval_isIntegerInterval {T N : ℝ} {a b : ℕ}
    (hT : 0 < T) (hN : 0 < N) (ha : N ≤ (a : ℝ)) (hb : (b : ℝ) ≤ 2*N) :
    IsIntegerInterval (zetaLogDualInterval T N a b) := by
  classical
  let S := modelPhaseSharpStationarySet Real.log T N a b
  by_cases hne : S.Nonempty
  · have hmin := Finset.min'_mem S hne
    have hmax := Finset.max'_mem S hne
    have hminPos : 0 < S.min' hne := by
      exact_mod_cast (div_pos hT (by positivity : 0 < 2*N)).trans
        (logarithmicSharpStationarySet_window hT hN ha hb hmin).1
    have hlong : (a : ℝ)/N+4*(Real.sqrt T)⁻¹ < (b : ℝ)/N := by
      by_contra h
      have he := modelPhaseSharpStationarySet_of_short (F := Real.log) (le_of_not_gt h)
      change (modelPhaseSharpStationarySet Real.log T N a b).Nonempty at hne
      rw [he] at hne
      exact Finset.not_nonempty_empty hne
    have hinterval : S = Finset.Icc (S.min' hne) (S.max' hne) := by
      ext q
      constructor
      · intro hq
        exact Finset.mem_Icc.mpr ⟨Finset.min'_le S q hq,Finset.le_max' S q hq⟩
      · intro hq
        have hbounds := Finset.mem_Icc.mp hq
        have hlo := hmin
        have hhi := hmax
        change _ ∈ modelPhaseSharpStationarySet Real.log T N a b at hlo hhi ⊢
        rw [modelPhaseSharpStationarySet_of_long hlong] at hlo hhi ⊢
        exact Finset.mem_Ioo.mpr ⟨(Finset.mem_Ioo.mp hlo).1.trans_le hbounds.1,
          hbounds.2.trans_lt (Finset.mem_Ioo.mp hhi).2⟩
    have himage := hinterval.trans
      (int_Icc_eq_image_nat_Icc hminPos.le (Finset.min'_le_max' S hne))
    refine ⟨(S.min' hne).toNat,(S.max' hne).toNat,?_⟩
    change S.image Int.toNat = _
    have hmap := congrArg (fun s : Finset ℤ => s.image Int.toNat) himage
    simpa only [Finset.image_image,Function.comp_def,Int.toNat_natCast,Finset.image_id'] using hmap
  · have he : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
    have heJ : zetaLogDualInterval T N a b = ∅ := by
      change S.image Int.toNat = ∅
      rw [he,Finset.image_empty]
    rw [heJ]
    exact ⟨1,0,by simp⟩

theorem zetaLogDualInterval_weighted_sum {T N t : ℝ} {a b : ℕ}
    (hT : 0 < T) (hN : 0 < N) (ha : N ≤ (a : ℝ)) (hb : (b : ℝ) ≤ 2*N) :
    (∑ n ∈ zetaLogDualInterval T N a b, (n : ℂ)⁻¹*dirichletPhase n t) =
      ∑ q ∈ modelPhaseSharpStationarySet Real.log T N a b,
        (q : ℂ)⁻¹*(q : ℂ)^(-(I*(t : ℂ))) := by
  classical
  have hnonneg (q : ℤ) (hq : q ∈ modelPhaseSharpStationarySet Real.log T N a b) :
      0 ≤ q := by
    have hh := (div_pos hT (by positivity : 0 < 2*N)).trans
      (logarithmicSharpStationarySet_window hT hN ha hb hq).1
    exact le_of_lt (by exact_mod_cast hh)
  rw [zetaLogDualInterval,Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro q hq
    have hcast : (q.toNat : ℤ) = q := Int.toNat_of_nonneg (hnonneg q hq)
    have hc : (q.toNat : ℂ) = (q : ℂ) := by exact_mod_cast hcast
    simp only [dirichletPhase,hc]
    rfl
  · intro q hq r hr heq
    have hq0 := hnonneg q hq
    have hr0 := hnonneg r hr
    omega

theorem dirichletInterval_sharp_natural_reflection {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (N t : ℝ) (a b : ℕ),
      1 ≤ N → 2*Real.pi ≤ t → N ≤ (a : ℝ) → (b : ℝ) ≤ 2*N →
        ‖∑ n ∈ Finset.Icc a b, dirichletPhase n t‖ ≤
          Real.sqrt (t/(2*Real.pi))*
            ‖∑ n ∈ zetaLogDualInterval (t/(2*Real.pi)) N a b,
              (n : ℂ)⁻¹*dirichletPhase n t‖+
          C*(N/Real.sqrt (t/(2*Real.pi))+(t/(2*Real.pi))^ε) := by
  obtain ⟨C,hC,hbound⟩ := dirichletInterval_sharp_log_reflection hε
  refine ⟨C,hC,?_⟩
  intro N t a b hN ht ha hb
  have htp : 0 < t := (by positivity : 0 < 2*Real.pi).trans_le ht
  rw [zetaLogDualInterval_weighted_sum (div_pos htp (by positivity))
    (zero_lt_one.trans_le hN) ha hb]
  exact hbound N t a b hN ht ha hb

end TaoTrudgianYang2025
