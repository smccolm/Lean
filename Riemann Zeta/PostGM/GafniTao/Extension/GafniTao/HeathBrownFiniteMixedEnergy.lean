import GafniTao.HeathBrownFiniteEnergyRelation
import GafniTao.RealEnergyDiscretization

/-!
# Mixed finite Heath--Brown energy

The zero-energy shell decomposition selects four potentially different
Dirichlet polynomials.  This file combines the exact mixed-to-self energy
inequality with the finite Heath--Brown relation for each selected family.
-/

namespace GafniTao

noncomputable section

open RiemannZeta.GuthMaynard

/-- The right-hand side contributed by one selected large-value family. -/
noncomputable def heathBrownFiniteFamilyBound
    (epsilon C0 C2 C4 B V : Real) (M : Nat) (W : Finset Real) : Real :=
  (C0 * B ^ (epsilon / 2) *
      Real.sqrt (C2 * B ^ (epsilon / 2) *
        heathBrownSecondMomentShape B M W) *
      Real.sqrt (C4 * B ^ (epsilon / 2) *
        heathBrownFourthMomentShape B M W)) / V ^ 2

theorem heathBrownFiniteFamilyBound_nonneg
    {epsilon C0 C2 C4 B V : Real} {M : Nat} {W : Finset Real}
    (hC0 : 0 <= C0) (hB : 0 <= B) :
    0 <= heathBrownFiniteFamilyBound epsilon C0 C2 C4 B V M W := by
  unfold heathBrownFiniteFamilyBound
  have hPow : 0 <= B ^ (epsilon / 2) := Real.rpow_nonneg hB _
  have hSecond := heathBrownSecondMomentShape_nonneg B M W hB
  have hFourth := heathBrownFourthMomentShape_nonneg B M W hB
  positivity

/-- Four independent source families, with their exact thresholds and
lengths, consumed by the finite Heath--Brown relation. -/
theorem heathBrownFiniteMixedEnergyRelation_native :
    forall epsilon : Real, 0 < epsilon ->
      exists C0 C2 C4 T0 : Real,
        0 < C0 ∧ 0 < C2 ∧ 0 < C4 ∧ 1 <= T0 ∧
        forall (D : Real) (M : Fin 4 -> Nat) (B R V : Fin 4 -> Real)
            (W : Fin 4 -> Finset Real) (b : Fin 4 -> Nat -> Complex),
          (forall i, 0 < M i) ->
          (forall i, T0 <= B i) ->
          (forall i, (M i : Real) <= B i) ->
          (forall i, 0 < V i) ->
          (forall i, 2 * R i <= B i) ->
          (forall i, IsSeparated 1 (W i)) ->
          (forall i t, t ∈ W i -> -R i <= t ∧ t <= R i) ->
          (forall i, (W i).Nonempty ->
            forall n, n ∈ dyadicInterval (M i) -> ‖b i n‖ <= 1) ->
          (forall i t, t ∈ W i ->
            V i <= ‖sourceDirichletPoly (M i) (b i) t‖) ->
          4 * (MixedApproxAddEnergy D (W 0) (W 1) (W 2) (W 3) : Real) <=
            (doubleFloorDefectWindow D).card *
              ∑ i : Fin 4,
                heathBrownFiniteFamilyBound epsilon C0 C2 C4
                  (B i) (V i) (M i) (W i) := by
  intro epsilon hepsilon
  obtain ⟨C0, C2, C4, T0, hC0, hC2, hC4, hT0, hFamily⟩ :=
    heathBrownFiniteSymmetricEnergyRelation_native epsilon hepsilon
  refine ⟨C0, C2, C4, T0, hC0, hC2, hC4, hT0, ?_⟩
  intro D M B R V W b hM hB hMB hV hRB hSep hSymm hb hLarge
  have hEach : forall i : Fin 4,
      (ApproxAddEnergy 1 (W i) : Real) <=
        heathBrownFiniteFamilyBound epsilon C0 C2 C4
          (B i) (V i) (M i) (W i) := by
    intro i
    by_cases hWi : (W i).Nonempty
    · have hi := hFamily (M i) (B i) (R i) (V i) (W i) (b i)
        (hM i) (hB i) (hMB i) (hV i).le (hRB i) (hSep i)
        (hSymm i) (hb i hWi) (hLarge i)
      unfold heathBrownFiniteFamilyBound
      rw [le_div_iff₀ (sq_pos_of_pos (hV i))]
      exact hi
    · have hEmpty : W i = ∅ := Finset.not_nonempty_iff_eq_empty.mp hWi
      rw [hEmpty]
      simp only [ApproxAddEnergy, approximateAdditiveQuadruples,
        Finset.empty_product, Finset.filter_empty, Finset.card_empty,
        Nat.cast_zero]
      exact heathBrownFiniteFamilyBound_nonneg hC0.le
        (zero_le_one.trans (hT0.trans (hB i)))
  have hMixed := four_mul_mixedApproxAddEnergy_le_window_mul_sum_self
    (eta := D) (hSep 0) (hSep 1) (hSep 2) (hSep 3)
  calc
    4 * (MixedApproxAddEnergy D (W 0) (W 1) (W 2) (W 3) : Real) <=
        (doubleFloorDefectWindow D).card *
          ((ApproxAddEnergy 1 (W 0) : Real) +
            (ApproxAddEnergy 1 (W 1) : Real) +
            (ApproxAddEnergy 1 (W 2) : Real) +
            (ApproxAddEnergy 1 (W 3) : Real)) := hMixed
    _ <= (doubleFloorDefectWindow D).card *
        ∑ i : Fin 4,
          heathBrownFiniteFamilyBound epsilon C0 C2 C4
            (B i) (V i) (M i) (W i) := by
      rw [Fin.sum_univ_four]
      gcongr <;> apply hEach

#print axioms heathBrownFiniteFamilyBound_nonneg
#print axioms heathBrownFiniteMixedEnergyRelation_native

end

end GafniTao
