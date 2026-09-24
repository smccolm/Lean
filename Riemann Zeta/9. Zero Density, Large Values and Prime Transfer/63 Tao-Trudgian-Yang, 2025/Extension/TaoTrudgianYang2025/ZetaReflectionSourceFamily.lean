import TaoTrudgianYang2025.ZetaReflectionCommonFamily

/-! Actual zeta patterns produce actual separated reflected value families. -/

noncomputable section
open Complex Filter MeasureTheory Set
open scoped Classical Interval
namespace TaoTrudgianYang2025

def zetaReflectionValueFloor (P : ZetaLargeValuePattern) : ℝ :=
  P.V*Real.sqrt P.T/(8*zetaReflectionConvolutionConstant*P.N*zetaMomentLogLoss P.T)

theorem zetaReflectionValueFloor_pos (P : ZetaLargeValuePattern) :
    0 < zetaReflectionValueFloor P := by
  unfold zetaReflectionValueFloor
  have := P.V_pos
  have := P.T_pos
  have := zero_lt_one.trans P.one_lt_N
  have := zetaReflectionConvolutionConstant_pos
  have := zetaMomentLogLoss_pos P.T
  positivity

theorem exists_zetaReflection_value_family {τ : ℝ} (hτ : 1 < τ) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ N₀ : ℝ, 1 ≤ N₀ ∧
      ∀ P : ZetaLargeValuePattern, N₀ ≤ P.N →
        ∀ σ : ℝ, 1/2 ≤ σ →
          P.N^(τ-δ) ≤ P.T → P.T ≤ P.N^(τ+δ) → P.N^(σ-δ) ≤ P.V →
            P.ordinates.Nonempty →
              ∃ u ∈ Icc (-(2*P.T)) (2*P.T),
                ∃ j ∈ Finset.range (reflectionBandCount
                    (zetaReflectionCommonInterval P.T P.N) (zetaReflectionValueFloor P)),
                  ∃ U : Finset ℝ,
                    U.Nonempty ∧ U ⊆ P.ordinates.image (fun t => t+u) ∧ IsOneSeparated U ∧
                    (∀ v ∈ U, v ∈ Icc (P.T/2) (3*P.T)) ∧
                    (∀ v ∈ U,
                      zetaReflectionValueFloor P*(2 : ℝ)^j ≤
                        ‖∑ n ∈ zetaReflectionCommonInterval P.T P.N, dirichletPhase n v‖ ∧
                      ‖∑ n ∈ zetaReflectionCommonInterval P.T P.N, dirichletPhase n v‖ <
                        2*(zetaReflectionValueFloor P*(2 : ℝ)^j)) ∧
                    (P.ordinates.card : ℝ)*P.V*Real.sqrt P.T/
                        (8*zetaReflectionConvolutionConstant*P.N*zetaMomentLogLoss P.T*
                          (reflectionBandCount (zetaReflectionCommonInterval P.T P.N)
                            (zetaReflectionValueFloor P) : ℝ)) ≤
                      zetaReflectionValueFloor P*(2 : ℝ)^j*(U.card : ℝ) := by
  obtain ⟨δ,hδ,N₀,hN₀,hentry⟩ := exists_zetaReflectionConvolution_uniform_entry hτ
  refine ⟨δ,hδ,N₀,hN₀,?_⟩
  intro P hN σ hσ hTL hTU hV hne
  let S := zetaReflectionCommonInterval P.T P.N
  let D := P.V*Real.sqrt P.T/(zetaReflectionConvolutionConstant*P.N)
  let L := (P.ordinates.card : ℝ)*D
  have hNpos := zero_lt_one.trans P.one_lt_N
  have hTpos := P.T_pos
  have hVpos := P.V_pos
  have hK := zetaReflectionConvolutionConstant_pos
  have hlog := zetaMomentLogLoss_pos P.T
  have hcard : (0 : ℝ) < P.ordinates.card := by exact_mod_cast Finset.card_pos.mpr hne
  have hD : 0 < D := by dsimp [D]; positivity
  have hL : 0 < L := mul_pos hcard hD
  have hS : ∀ n ∈ S, n ≠ 0 := fun n hn =>
    ne_of_gt (zetaReflectionCommonInterval_positive P.T P.N hn)
  have hW : ∀ t ∈ P.ordinates, t ∈ Icc P.T (2*P.T) := by
    intro t ht
    simpa only [P.intervalLeft_eq,P.intervalRight_eq] using P.ordinates_in_interval t ht
  have hsingle (t : ℝ) (ht : t ∈ P.ordinates) :
      D ≤ zetaReflectionConvolution S P.T t := by
    have h := hentry P hN σ hσ hTL hTU hV t ht
    have he : D = (P.V*Real.sqrt P.T/P.N)/zetaReflectionConvolutionConstant := by
      dsimp [D]
      ring
    rw [he]
    apply (div_le_iff₀ hK).2
    simpa only [mul_comm] using h
  have hsum : L ≤ ∑ t ∈ P.ordinates, zetaReflectionConvolution S P.T t := by
    have h := Finset.sum_le_sum hsingle
    simpa only [Finset.sum_const,nsmul_eq_mul] using h
  have hfloor : 4*zetaReflectionValueFloor P*(P.ordinates.card : ℝ)*
      zetaMomentLogLoss P.T ≤ L := by
    have he : 4*zetaReflectionValueFloor P*(P.ordinates.card : ℝ)*
        zetaMomentLogLoss P.T = L/2 := by
      dsimp [zetaReflectionValueFloor,L,D]
      field_simp
      ring
    rw [he]
    linarith
  obtain ⟨u,hu,j,hj,U,hUne,hUsub,hUsep,hUtime,hUvalues,hUmass⟩ :=
    exists_reflection_common_value_family P.ordinates S hS P.ordinates_oneSeparated P.T_pos hL
      (zetaReflectionValueFloor_pos P) hW hsum hfloor
  refine ⟨u,hu,j,hj,U,hUne,hUsub,hUsep,hUtime,hUvalues,?_⟩
  convert hUmass using 1
  dsimp [L,D]
  field_simp
  ring

end TaoTrudgianYang2025
