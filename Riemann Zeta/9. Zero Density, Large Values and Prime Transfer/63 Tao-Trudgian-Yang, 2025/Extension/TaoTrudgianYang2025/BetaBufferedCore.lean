import TaoTrudgianYang2025.BetaBufferedFourierTail
import TaoTrudgianYang2025.BetaBufferedNonstationarySums
import TaoTrudgianYang2025.IntegerFourierWindows

/-!
# The original source reduced to its physical slope-envelope core

The omitted integer frequencies are partitioned exactly into two
nonstationary blocks and an actual infinite far tail. Both errors
are derived from the original model and controlled cutoff.
-/

noncomputable section

open Set Expdb
open scoped BigOperators

namespace TaoTrudgianYang2025

def modelPhaseCoreLower (σ δ T N : ℝ) : ℤ :=
  ⌊(T/N)*((2 : ℝ)^(-σ)-δ)⌋

def modelPhaseCoreUpper (δ T N : ℝ) : ℤ :=
  ⌈(T/N)*(1+δ)⌉

theorem modelPhaseCoreLower_le_upper
    {σ δ T N : ℝ} (hσ : 0 ≤ σ) (hδ : 0 ≤ δ) (hT : 0 ≤ T) (hN : 0 < N) :
    modelPhaseCoreLower σ δ T N ≤ modelPhaseCoreUpper δ T N := by
  have hp : (2 : ℝ)^(-σ) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by linarith)
  have he : (T/N)*((2 : ℝ)^(-σ)-δ) ≤ (T/N)*(1+δ) :=
    mul_le_mul_of_nonneg_left (by linarith) (div_nonneg hT hN.le)
  have hh := (Int.floor_le ((T/N)*((2 : ℝ)^(-σ)-δ))).trans
    (he.trans (Int.le_ceil ((T/N)*(1+δ))))
  exact_mod_cast hh

theorem modelPhase_buffered_poisson_core
    {σ : ℝ} (hσ : 0 < σ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (N η : ℝ) (a b : ℕ),
      0 < N → 0 < η → η ≤ 1 → N ≤ (a : ℝ) → (b : ℝ) ≤ 2*N →
      ∀ (F : ℝ → ℝ) (δ T : ℝ),
        δ ≤ min (modelPhaseCurvatureLower σ) 1 →
        IsApproximateModelPhaseFunction F σ 1 δ → 0 < T →
        ∀ R : ℕ, 0 < R →
          -(R : ℤ) ≤ modelPhaseCoreLower σ δ T N →
          modelPhaseCoreUpper δ T N ≤ (R : ℤ) →
          ‖exponentialSumAt F T N a b-
            ∑ q ∈ Finset.Icc (modelPhaseCoreLower σ δ T N) (modelPhaseCoreUpper δ T N),
              modelPhaseFourierMode
                (modelPhaseBufferedCutoff ((a : ℝ)/N) ((b : ℝ)/N) η) F T N q‖ ≤
            4*N*η+2+C*(η⁻¹)^2*(1+|T|)^2/(N*(R : ℝ))+
              (4/Real.pi)*(2+
                Real.log (((modelPhaseCoreLower σ δ T N+(R : ℤ)).toNat : ℕ) : ℝ)+
                Real.log ((((R : ℤ)-modelPhaseCoreUpper δ T N).toNat : ℕ) : ℝ)) := by
  obtain ⟨C,hC,htrunc⟩ := modelPhase_buffered_poisson_truncated hσ.le
  refine ⟨C,hC,?_⟩
  intro N η a b hN hη hη₁ ha hb F δ T hδ hF hT R hR hRA hBR
  let χ := modelPhaseBufferedCutoff ((a : ℝ)/N) ((b : ℝ)/N) η
  let A := modelPhaseCoreLower σ δ T N
  let B := modelPhaseCoreUpper δ T N
  let f : ℤ → ℂ := fun q => modelPhaseFourierMode χ F T N q
  have hAB : A ≤ B :=
    modelPhaseCoreLower_le_upper hσ.le (approximateModelPhase_tolerance_nonneg hF) hT.le hN
  have hsplit := sum_int_interval_three_parts f hRA hAB hBR
  rw [sum_int_Ico_eq_reverse_range f hRA,sum_int_Ioc_eq_forward_range f hBR] at hsplit
  have hext := norm_bufferedModes_exterior_blocks_le_log hσ hδ hF hT hN hη
    ((one_le_div hN).mpr ha) ((div_le_iff₀ hN).mpr hb)
    (A+(R : ℤ)).toNat ((R : ℤ)-B).toNat
  have hext' :
      ‖(∑ n ∈ Finset.range (A+(R : ℤ)).toNat, f (A-((n+1 : ℕ) : ℤ)))+
        (∑ n ∈ Finset.range ((R : ℤ)-B).toNat, f (B+((n+1 : ℕ) : ℤ)))‖ ≤
        (4/Real.pi)*(2+Real.log ((A+(R : ℤ)).toNat : ℝ)+
          Real.log (((R : ℤ)-B).toNat : ℝ)) := by
    simpa only [f,χ,A,B,modelPhaseCoreLower,modelPhaseCoreUpper,Int.cast_sub,
      Int.cast_add,Int.cast_natCast] using hext
  have hsource := htrunc N η a b hN hη hη₁ ha hb F δ T
    (hδ.trans (min_le_right _ _)) hF R hR
  have heq :
      exponentialSumAt F T N a b-(∑ q ∈ Finset.Icc A B, f q) =
        (exponentialSumAt F T N a b-(∑ q ∈ Finset.Icc (-(R : ℤ)) (R : ℤ), f q))+
          ((∑ n ∈ Finset.range (A+(R : ℤ)).toNat, f (A-((n+1 : ℕ) : ℤ)))+
            (∑ n ∈ Finset.range ((R : ℤ)-B).toNat, f (B+((n+1 : ℕ) : ℤ)))) := by
    rw [hsplit]
    simp only [sub_neg_eq_add]
    abel
  change ‖exponentialSumAt F T N a b-(∑ q ∈ Finset.Icc A B, f q)‖ ≤ _
  rw [heq]
  exact (norm_add_le _ _).trans (add_le_add hsource hext')

theorem modelPhase_buffered_poisson_core_precision
    {σ : ℝ} (hσ : 0 < σ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (N η : ℝ) (a b : ℕ),
      0 < N → 0 < η → η ≤ 1 → N ≤ (a : ℝ) → (b : ℝ) ≤ 2*N →
      ∀ (F : ℝ → ℝ) (δ T ε : ℝ),
        δ ≤ min (modelPhaseCurvatureLower σ) 1 →
        IsApproximateModelPhaseFunction F σ 1 δ → 0 < T → 0 < ε →
        let A := modelPhaseCoreLower σ δ T N
        let B := modelPhaseCoreUpper δ T N
        let R : ℕ := ⌈C*(η⁻¹)^2*(1+|T|)^2/(N*ε)⌉₊+A.natAbs+B.natAbs+1
        0 < R ∧ -(R : ℤ) ≤ A ∧ B ≤ (R : ℤ) ∧
          ‖exponentialSumAt F T N a b-
            ∑ q ∈ Finset.Icc A B,
              modelPhaseFourierMode
                (modelPhaseBufferedCutoff ((a : ℝ)/N) ((b : ℝ)/N) η) F T N q‖ ≤
            4*N*η+2+ε+(4/Real.pi)*(2+
              Real.log ((A+(R : ℤ)).toNat : ℝ)+Real.log (((R : ℤ)-B).toNat : ℝ)) := by
  obtain ⟨C,hC,hcore⟩ := modelPhase_buffered_poisson_core hσ
  refine ⟨C,hC,?_⟩
  intro N η a b hN hη hη₁ ha hb F δ T ε hδ hF hT hε A B R
  have hR : 0 < R := Nat.succ_pos _
  have hRA : -(R : ℤ) ≤ A := by dsimp [R]; omega
  have hBR : B ≤ (R : ℤ) := by dsimp [R]; omega
  refine ⟨hR,hRA,hBR,?_⟩
  have hR₀ : 0 < (R : ℝ) := by exact_mod_cast hR
  have hceil : C*(η⁻¹)^2*(1+|T|)^2/(N*ε) ≤ (R : ℝ) := by
    exact (Nat.le_ceil _).trans (by
      dsimp [R]
      push_cast
      linarith [Nat.cast_nonneg (α := ℝ) A.natAbs,Nat.cast_nonneg (α := ℝ) B.natAbs])
  have hbudget : C*(η⁻¹)^2*(1+|T|)^2/(N*(R : ℝ)) ≤ ε := by
    apply (div_le_iff₀ (mul_pos hN hR₀)).mpr
    have h := (div_le_iff₀ (mul_pos hN hε)).mp hceil
    nlinarith
  exact (hcore N η a b hN hη hη₁ ha hb F δ T hδ hF hT R hR hRA hBR).trans
    (add_le_add (add_le_add le_rfl hbudget) le_rfl)

end TaoTrudgianYang2025
