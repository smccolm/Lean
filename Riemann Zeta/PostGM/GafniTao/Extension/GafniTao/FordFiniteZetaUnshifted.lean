import GafniTao.FordRiemannDadaroTinyRemainder

/-!
# The unshifted finite zeta sum

Ford's finite Hurwitz estimate is uniform for `0 < u ≤ 1`.  Finite-sum
continuity supplies the exact `u = 0` endpoint needed by the ordinary zeta
formula, without adding an endpoint term to the source constant.
-/

open Complex Finset Filter Topology
open scoped BigOperators

namespace GafniTao

noncomputable section

theorem continuousAt_fordFiniteHurwitzTerm_zero
    {sigma t : ℝ} {n : ℕ} (hn : 0 < n) :
    ContinuousAt
      (fun u : ℝ => ((((n : ℝ) + u : ℝ) : ℂ) ^
        (-((sigma : ℂ) + (t : ℂ) * I)))) 0 := by
  have hbase : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hc := Complex.continuousAt_ofReal_cpow_const
    (n : ℝ) (-((sigma : ℂ) + (t : ℂ) * I)) (Or.inr hbase)
  exact hc.comp_of_eq (by fun_prop) (by simp)

theorem continuousAt_fordFiniteHurwitzSum_zero
    {sigma t : ℝ} (M : ℕ) :
    ContinuousAt (fun u : ℝ => fordFiniteHurwitzSum sigma M u t) 0 := by
  unfold fordFiniteHurwitzSum
  have hsum : ∀ s : Finset ℕ,
      (∀ n ∈ s, 0 < n) →
      ContinuousAt
        (fun u : ℝ => ∑ n ∈ s,
          ((((n : ℝ) + u : ℝ) : ℂ) ^
            (-((sigma : ℂ) + (t : ℂ) * I)))) 0 := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
        intro _h
        simpa using (continuousAt_const :
          ContinuousAt (fun _ : ℝ => (0 : ℂ)) 0)
    | @insert n s hn ih =>
        intro hpos
        simpa [Finset.sum_insert, hn] using
          (continuousAt_fordFiniteHurwitzTerm_zero (hpos n (by simp))).add
            (ih fun m hm => hpos m (by simp [hm]))
  exact hsum (Finset.Icc 1 M) fun n hn => by
    exact (Finset.mem_Icc.mp hn).1

theorem norm_fordFiniteHurwitzSum_floor_zero_le_source
    (hFord : FordTheorem2)
    {sigma t : ℝ}
    (hsigmaLower : 0 ≤ sigma) (hsigmaUpper : sigma ≤ 1)
    (ht : 1 < t) :
    ‖fordFiniteHurwitzSum sigma (fordFiniteEndpoint t) 0 t‖ ≤
      1 + 9.463 *
        (t ^ (fordSourceB 133.66 * (1 - sigma) ^ (3 / 2 : ℝ)) *
          (1 + 1.569 * 133.66 ^ ((1 : ℝ) / 3) *
            Real.log t ^ ((2 : ℝ) / 3))) := by
  let u : ℕ → ℝ := fun k => 1 / ((k : ℝ) + 1)
  have huLim : Tendsto u atTop (𝓝 0) := by
    simpa [u, Nat.cast_add, Nat.cast_one] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hsumLim : Tendsto
      (fun k => fordFiniteHurwitzSum sigma (fordFiniteEndpoint t) (u k) t)
        atTop
      (𝓝 (fordFiniteHurwitzSum sigma (fordFiniteEndpoint t) 0 t)) :=
    (continuousAt_fordFiniteHurwitzSum_zero
      (sigma := sigma) (t := t) (fordFiniteEndpoint t)).tendsto.comp huLim
  apply le_of_tendsto hsumLim.norm
  exact Filter.Eventually.of_forall fun k => by
    apply norm_fordFiniteHurwitzSum_floor_le_source hFord
      hsigmaLower hsigmaUpper
    · dsimp [u]
      positivity
    · dsimp [u]
      rw [div_le_one (by positivity)]
      norm_num
    · exact ht

theorem fordFiniteHurwitzSum_zero_eq_partialSum
    (sigma t : ℝ) :
    fordFiniteHurwitzSum sigma (fordFiniteEndpoint t) 0 t =
      ∑ n ∈ Finset.Icc 1 (fordFiniteEndpoint t),
        (n : ℂ) ^ (-fordComplexHeight sigma t) := by
  unfold fordFiniteHurwitzSum fordComplexHeight
  simp

theorem norm_fordPartialSum_le_source
    (hFord : FordTheorem2)
    {sigma t : ℝ}
    (hsigmaLower : 0 ≤ sigma) (hsigmaUpper : sigma ≤ 1)
    (ht : 1 < t) :
    ‖∑ n ∈ Finset.Icc 1 (fordFiniteEndpoint t),
        (n : ℂ) ^ (-fordComplexHeight sigma t)‖ ≤
      1 + 9.463 *
        (t ^ (fordSourceB 133.66 * (1 - sigma) ^ (3 / 2 : ℝ)) *
          (1 + 1.569 * 133.66 ^ ((1 : ℝ) / 3) *
            Real.log t ^ ((2 : ℝ) / 3))) := by
  rw [← fordFiniteHurwitzSum_zero_eq_partialSum]
  exact norm_fordFiniteHurwitzSum_floor_zero_le_source hFord
    hsigmaLower hsigmaUpper ht

#print axioms continuousAt_fordFiniteHurwitzSum_zero
#print axioms norm_fordFiniteHurwitzSum_floor_zero_le_source
#print axioms fordFiniteHurwitzSum_zero_eq_partialSum
#print axioms norm_fordPartialSum_le_source

end

end GafniTao
