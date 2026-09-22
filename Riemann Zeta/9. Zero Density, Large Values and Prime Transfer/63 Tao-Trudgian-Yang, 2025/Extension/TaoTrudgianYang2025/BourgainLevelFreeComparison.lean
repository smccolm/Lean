import TaoTrudgianYang2025.BourgainCommonComparison
import TaoTrudgianYang2025.BourgainLevelElimination

/-!
# Level-free physical Bourgain comparison on the actual selected family

The two mixed coefficients no longer depend on the selected correlation or
relative-multiplicity levels. The component power sum is replaced by the
original retained union's cardinality, with the exact square-root bin loss.
-/

open MeasureTheory RiemannZeta.GuthMaynard
open scoped Interval Classical

noncomputable section

namespace TaoTrudgianYang2025

/-- Actual source consumer of parameter elimination and the finite bin inequality. -/
theorem bourgain_subdivided_level_free_comparison {σ τ η θ : ℝ}
    (hσ : 3/4 < σ) (hη : 0 < η) (hθ : 0 < θ) {ε : ℝ} (hε : 0 < ε) :
    ∃ B C δ M N₀ D E₀ : ℝ,
      0 < B ∧ 2 ≤ C ∧ 0 < δ ∧ δ ≤ 1 ∧ 0 < M ∧ 2 ≤ N₀ ∧ 0 < D ∧ 1 ≤ E₀ ∧
      ∀ (P : LargeValuePattern) (L : ℝ) (hL : 0 < L),
        C ≤ P.N → N₀ ≤ P.N → P.N ≤ L → L ≤ P.N^(τ+δ) → P.N^(σ-δ) ≤ P.V →
        ∃ W : ℕ → Finset ℝ,
          (∀ i : ℕ, W i ⊆ (P.localized L hL i).reflectedOrdinates ∧
            IsSeparated 2 (W i) ∧ InBaseInterval L (W i) ∧
            ((P.localized L hL i).ordinates.card : ℝ) ≤ C*P.N^ε*((W i).card : ℝ)) ∧
          ∀ α : ℝ,
            let I := Finset.range (Nat.floor (P.T/L)+1)
            let a := P.N^(-bourgainSharedFloorExponent α τ ε)
            let J := bourgainZetaBandCount B (L+P.N^(ε/8)+1) a
            let F := C*(P.N^(2-2*σ+ε)+P.N^(2*τ+4-8*σ+ε)+
              P.N^(-2*α+τ+12-16*σ+ε))
            ∃ q ∈ Finset.range J, ∃ p ∈ Finset.range (bourgainRelativeLevelCount P.N τ),
              ∃ k ∈ Finset.range (bourgainCorrelationLevelCount P.N B C α τ ε),
              ∃ A : Finset ℕ, A ⊆ I ∧
              ∃ j : ℕ → ℕ,
                (∀ i ∈ A, (F < ((P.localized L hL i).ordinates.card : ℝ) ∧
                  BourgainComponentBand P.N L B C τ α ε (W i) (j i) q ∧
                  (let d := bourgainRelativeLevel P.N τ p
                  0 < d ∧ d ≤ 1 ∧
                  d*((W i).card : ℝ) ≤ (2 : ℝ)^(j i) ∧
                  (2 : ℝ)^(j i) < 2*d*((W i).card : ℝ) ∧
                  (∀ ℓ ∈ bourgainDifferenceLevel (W i) (j i),
                    d*((W i).card : ℝ) ≤ (bourgainDifferenceCount (W i) ℓ : ℝ) ∧
                    (bourgainDifferenceCount (W i) ℓ : ℝ) < 4*d*((W i).card : ℝ)) ∧
                  d*((bourgainDifferenceLevel (W i) (j i)).card : ℝ) ≤ 2*((W i).card : ℝ)) ∧
                  let d := bourgainRelativeLevel P.N τ p
                  let r := bourgainZetaBandCorrelation
                    (bourgainDifferenceLevel (W i) (j i)) (P.N^(ε/8))
                    (L+P.N^(ε/8)+1) (a*(2 : ℝ)^q)
                  P.N^(-2*α)*P.N^τ <
                    1024*(Nat.log 2 (W i).card+1 : ℕ)^2*(J : ℝ)^2*
                      C*(L+P.N^(ε/8)+1)^(1+ε)*d*r^2) ∧
                  (let H := P.N^(ε/8)
                  let U := L+H+1
                  let D := bourgainDifferenceLevel (W i) (j i)
                  let V := a*(2 : ℝ)^q
                  let r := bourgainZetaBandCorrelation D H U V
                  let μ := volume.real (bourgainZetaBand U V)
                  let s := bourgainCorrelationLevel P.N B C α τ ε k
                  0 < s ∧ s ≤ r ∧ r < 2*s ∧ s ≤ 4*H ∧
                  s*Real.sqrt μ*Real.sqrt (D.card : ℝ) ≤ bourgainZetaBandMass D H U V ∧
                  bourgainZetaBandMass D H U V < 2*s*Real.sqrt μ*Real.sqrt (D.card : ℝ)) ∧
                  let d := bourgainRelativeLevel P.N τ p
                  let s := bourgainCorrelationLevel P.N B C α τ ε k
                  P.N^(-2*α)*P.N^τ <
                    4096*(Nat.log 2 (W i).card+1 : ℕ)^2*(J : ℝ)^2*
                      C*(L+P.N^(ε/8)+1)^(1+ε)*d*s^2) ∧
                let S := A.biUnion (fun i => (P.localized L hL i).retainedOriginal (W i))
                S ⊆ P.ordinates ∧ S.card = ∑ i ∈ A, (W i).card ∧
                IsSeparated 1 S ∧
                (∀ t ∈ S, P.V ≤ ‖∑ n ∈ P.indices, P.coeff n*dirichletPhase n t‖) ∧
                (∀ i ∈ A, ∀ ℓ : ℤ,
                  bourgainDifferenceCount ((P.localized L hL i).retainedOriginal (W i)) ℓ =
                    bourgainDifferenceCount (W i) ℓ) ∧
                (P.ordinates.card : ℝ) ≤
                  (I.card : ℝ)*F+C*P.N^ε*(J : ℝ)*(bourgainRelativeLevelCount P.N τ : ℝ)*
                    (bourgainCorrelationLevelCount P.N B C α τ ε : ℝ)*(S.card : ℝ) ∧
                ((P.ordinates.card : ℝ) ≤ (I.card : ℝ)*F ∨
                  let H := P.N^(ε/8)
                  let U := L+H+1
                  let V := a*(2 : ℝ)^q
                  S.Nonempty ∧
                  ∃ u ∈ Set.Ioc (-H) H,
                    (bourgainIntegerSlice H U V u).Nonempty ∧
                    ∀ E : ℝ, E₀ ≤ E → P.T ≤ E → 2*(U+H) ≤ E →
                    P.V^2*(bourgainEliminatedCardCoefficient P.N L B C τ α ε*
                        ((bourgainIntegerSlice H U V u).card : ℝ)*(S.card : ℝ)+
                      bourgainSliceSqrtCoefficient P.N L B C τ α ε 1*
                        Real.sqrt ((bourgainIntegerSlice H U V u).card : ℝ)*
                          ((S.card : ℝ)^(3/2 : ℝ)/Real.sqrt (I.card : ℝ))) <
                    M*P.N^η*(2*(1+2*Real.pi*P.N^η)*D*E^θ*
                      (Real.sqrt (bourgainSecondBudget P.N E (S.card : ℝ))*
                        Real.sqrt (bourgainSecondBudget P.N E
                          ((bourgainIntegerSlice H U V u).card : ℝ))))) := by
  obtain ⟨B, C, δ, M, N₀, D, E₀, hB, hC, hδ, hδ₁, hM, hN₀, hD, hE₀, hp⟩ :=
    bourgain_subdivided_mixed_comparison (τ := τ) hσ hη hθ hε
  refine ⟨B, C, δ, M, N₀, D, E₀, hB, hC, hδ, hδ₁, hM, hN₀, hD, hE₀, ?_⟩
  intro P L hL hN hNN₀ hNL hTu hVl
  obtain ⟨W, hlocal, hfamily⟩ := hp P L hL hN hNN₀ hNL hTu hVl
  refine ⟨W, hlocal, ?_⟩
  intro α
  obtain ⟨q, hq, p, hp, k, hk, A, hAI, j, hbands,
    hsource, hcard, hsep, hlarge, hdiff, hglobal, hbranch⟩ := hfamily α
  refine ⟨q, hq, p, hp, k, hk, A, hAI, j, hbands,
    hsource, hcard, hsep, hlarge, hdiff, hglobal, ?_⟩
  by_cases hempty : A = ∅
  · left
    simpa only [hempty, Finset.biUnion_empty, Finset.card_empty, Nat.cast_zero,
      mul_zero, add_zero] using hglobal
  obtain ⟨i₀, hi₀⟩ := Finset.nonempty_iff_ne_empty.mpr hempty
  let S := A.biUnion (fun i => (P.localized L hL i).retainedOriginal (W i))
  let I := Finset.range (Nat.floor (P.T/L)+1)
  let d := bourgainRelativeLevel P.N τ p
  let s := bourgainCorrelationLevel P.N B C α τ ε k
  let a₁ := bourgainEliminatedCardCoefficient P.N L B C τ α ε
  let b₁ := bourgainSliceSqrtCoefficient P.N L B C τ α ε 1
  have hCpos : 0 < C := by linarith
  have hd : 0 < d := (hbands i₀ hi₀).1.2.2.1.1
  have hfirst : a₁ < d*bourgainSliceCardCoefficient P.N ε s :=
    bourgain_component_card_coefficient P hL i₀ (W i₀) (hlocal i₀).1 hCpos hδ₁ hTu
      (hbands i₀ hi₀).1.2.1 hd (hbands i₀ hi₀).2.2
  have hb : 0 < b₁ := bourgainSliceSqrtCoefficient_one_pos P.one_lt_N.le hL hCpos
  have hcancel : d*bourgainSliceSqrtCoefficient P.N L B C τ α ε d = b₁ :=
    bourgain_slice_sqrt_coefficient_cancel _ _ _ _ _ _ _ _ hd.ne'
  have hR₀ : 0 < (W i₀).card :=
    (Nat.pow_pos (by norm_num : 0 < (2 : ℕ))).trans_le
      (hbands i₀ hi₀).1.2.1.2.2.1
  have hSpos : 0 < S.card := by
    change 0 < (A.biUnion (fun i => (P.localized L hL i).retainedOriginal (W i))).card
    rw [hcard]
    exact hR₀.trans_le (Finset.single_le_sum (fun i _ => Nat.zero_le (W i).card) hi₀)
  have hcardR : (S.card : ℝ) = ∑ i ∈ A, ((W i).card : ℝ) := by exact_mod_cast hcard
  have hI : (0 : ℝ) < I.card := by dsimp only [I]; simp only [Finset.card_range]; positivity
  have hmean := bourgain_sum_three_halves A I hAI
    (fun i => ((W i).card : ℝ)) (fun i _ => Nat.cast_nonneg _)
  rw [← hcardR] at hmean
  have hsum : (S.card : ℝ)^(3/2 : ℝ)/Real.sqrt (I.card : ℝ) ≤
      ∑ i ∈ A, ((W i).card : ℝ)^(3/2 : ℝ) :=
    (div_le_iff₀ (Real.sqrt_pos.mpr hI)).mpr (by simpa only [mul_comm] using hmean)
  rcases hbranch with hsmall | ⟨u, hu, hZ, hcomp⟩
  · exact Or.inl hsmall
  · right
    refine ⟨Finset.card_pos.mp hSpos, u, hu, hZ, ?_⟩
    intro E hE hPE hZE
    let K := ((bourgainIntegerSlice (P.N^(ε/8)) (L+P.N^(ε/8)+1)
      (P.N^(-bourgainSharedFloorExponent α τ ε)*(2 : ℝ)^q) u).card : ℝ)
    have hK : 0 ≤ K := Nat.cast_nonneg _
    have h₁ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hfirst.le hK) (Nat.cast_nonneg S.card)
    have h₂ := mul_le_mul_of_nonneg_left hsum
      (mul_nonneg hb.le (Real.sqrt_nonneg K))
    have hlower :
        P.V^2*(a₁*K*(S.card : ℝ)+b₁*Real.sqrt K*
          ((S.card : ℝ)^(3/2 : ℝ)/Real.sqrt (I.card : ℝ))) ≤
        P.V^2*d*(bourgainSliceCardCoefficient P.N ε s*K*(S.card : ℝ)+
          bourgainSliceSqrtCoefficient P.N L B C τ α ε d*Real.sqrt K*
            (∑ i ∈ A, ((W i).card : ℝ)^(3/2 : ℝ))) := by
      calc
        _ ≤ P.V^2*((d*bourgainSliceCardCoefficient P.N ε s)*K*(S.card : ℝ)+
            b₁*Real.sqrt K*(∑ i ∈ A, ((W i).card : ℝ)^(3/2 : ℝ))) :=
          mul_le_mul_of_nonneg_left (add_le_add h₁ h₂) (sq_nonneg _)
        _ = _ := by rw [← hcancel]; ring
    exact hlower.trans_lt (hcomp E hE hPE hZE)

end TaoTrudgianYang2025
