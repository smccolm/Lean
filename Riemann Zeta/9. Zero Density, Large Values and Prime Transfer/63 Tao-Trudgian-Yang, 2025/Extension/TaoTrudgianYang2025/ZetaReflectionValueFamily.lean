import TaoTrudgianYang2025.ZetaReflectionShiftMean

/-! Actual common-shift value families with retained amplitude-cardinality mass. -/

noncomputable section
open Complex Filter MeasureTheory Set
open scoped Classical Interval
namespace TaoTrudgianYang2025

def reflectionBandCount (S : Finset ℕ) (a : ℝ) : ℕ :=
  Nat.clog 2 (Nat.ceil ((S.card : ℝ)/a))+1

theorem reflectionBandCount_pos (S : Finset ℕ) (a : ℝ) :
    0 < reflectionBandCount S a := Nat.succ_pos _

theorem reflectionBandCount_terminal (S : Finset ℕ) {a : ℝ} (ha : 0 < a) :
    (S.card : ℝ) < a*(2 : ℝ)^(reflectionBandCount S a) := by
  simpa [reflectionBandCount,bourgainZetaBandCount] using
    bourgainZetaBandCount_terminal (B := (S.card : ℝ)) (T := 0) ha

theorem exists_reflection_shifted_value_family (W : Finset ℝ) (S : Finset ℕ)
    (hS : ∀ n ∈ S, n ≠ 0) (hsep : IsOneSeparated W) (T u : ℝ)
    {a R : ℝ} (ha : 0 < a) (hR : 0 < R)
    (hlow : 2*a*(W.card : ℝ) ≤ R) (hmass : R ≤ reflectionShiftMass W S T u) :
    ∃ j ∈ Finset.range (reflectionBandCount S a), ∃ U : Finset ℝ,
      U.Nonempty ∧ U ⊆ W.image (fun t => t+u) ∧ IsOneSeparated U ∧
      (∀ v ∈ U, v ∈ Icc (T/2) (3*T)) ∧
      (∀ v ∈ U, a*(2 : ℝ)^j ≤ ‖∑ n ∈ S, dirichletPhase n v‖ ∧
        ‖∑ n ∈ S, dirichletPhase n v‖ < 2*(a*(2 : ℝ)^j)) ∧
      R/(4*(reflectionBandCount S a : ℝ)) ≤ a*(2 : ℝ)^j*(U.card : ℝ) := by
  let f : ℝ → ℝ := fun t => (zetaMellinSourceWindow T t).indicator
    (fun v => ‖∑ n ∈ S, dirichletPhase n (t+v)‖) u
  have hterminal (t : ℝ) (_ht : t ∈ W) : f t < a*(2 : ℝ)^(reflectionBandCount S a) := by
    have hbound : f t ≤ (S.card : ℝ) := by
      dsimp [f]
      by_cases hu : u ∈ zetaMellinSourceWindow T t
      · rw [Set.indicator_of_mem hu]
        exact reciprocalCompletion_phase_sum_norm_le_card S hS (t+u)
      · simp only [Set.indicator_of_notMem hu]
        positivity
    exact hbound.trans_lt (reflectionBandCount_terminal S ha)
  obtain ⟨j,hj,hne,hbound⟩ := exists_reflectionValueBand_mass W f ha hR
    (reflectionBandCount_pos S a) hterminal hlow hmass
  let U := (reflectionValueBand W f a j).image (fun t => t+u)
  have hcard : U.card = (reflectionValueBand W f a j).card := reflectionValueBand_shift_card W f a u j
  have hdata (v : ℝ) (hv : v ∈ U) :
      v ∈ Icc (T/2) (3*T) ∧
        a*(2 : ℝ)^j ≤ ‖∑ n ∈ S, dirichletPhase n v‖ ∧
        ‖∑ n ∈ S, dirichletPhase n v‖ < 2*(a*(2 : ℝ)^j) := by
    obtain ⟨t,ht,rfl⟩ := Finset.mem_image.mp hv
    obtain ⟨hlo,hhi⟩ := reflectionValueBand_values ht
    have hu : u ∈ zetaMellinSourceWindow T t := by
      by_contra hnot
      have hf : f t = 0 := Set.indicator_of_notMem hnot _
      rw [hf] at hlo
      exact (not_le_of_gt (by positivity : 0 < a*(2 : ℝ)^j)) hlo
    have htime : t+u ∈ Icc (T/2) (3*T) := by
      change T/2-t ≤ u ∧ u ≤ 3*T-t at hu
      constructor <;> linarith [hu.1,hu.2]
    have hf : f t = ‖∑ n ∈ S, dirichletPhase n (t+u)‖ := Set.indicator_of_mem hu _
    exact ⟨htime,hf ▸ hlo,hf ▸ hhi⟩
  refine ⟨j,hj,U,Finset.Nonempty.image hne _,
    Finset.image_subset_image (reflectionValueBand_subset W f a j),
    reflectionValueBand_shift_oneSeparated hsep f a u j,
    fun v hv => (hdata v hv).1,fun v hv => (hdata v hv).2,?_⟩
  simpa only [hcard] using hbound

end TaoTrudgianYang2025
