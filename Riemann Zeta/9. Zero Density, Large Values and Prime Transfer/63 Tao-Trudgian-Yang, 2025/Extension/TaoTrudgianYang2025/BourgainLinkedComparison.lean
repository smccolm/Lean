import TaoTrudgianYang2025.BourgainSubdivisionScale

/-!
# The actual source comparison at L=T/N^chi

Global and local logarithmic heights are linked by the physical subdivision.
The source small-component alternative, original retained union, full integer
slice and all finite selection costs survive this specialization.
-/

open MeasureTheory RiemannZeta.GuthMaynard
open scoped Interval Classical

noncomputable section

namespace TaoTrudgianYang2025

/-- A full selected-family consumer with the actual subdivision scale and bin
count, valid throughout the interior local-height range. -/
theorem bourgain_linked_subdivision_comparison {σ τ χ η θ : ℝ}
    (hσ : 3/4 < σ) (hχ : 0 ≤ χ) (hmargin : 1 < τ-χ)
    (hη : 0 < η) (hθ : 0 < θ) {ε : ℝ} (hε : 0 < ε) (hε₈ : ε ≤ 8) :
    ∃ B C δ M N₀ D : ℝ,
      0 < B ∧ 2 ≤ C ∧ 0 < δ ∧ δ ≤ 1 ∧ δ ≤ (τ-χ-1)/2 ∧ 0 < M ∧ 2 ≤ N₀ ∧ 0 < D ∧
      ∀ (P : LargeValuePattern) (L : ℝ) (hL : 0 < L),
        C ≤ P.N → N₀ ≤ P.N → L = P.T/P.N^χ →
        P.N^(τ-δ) ≤ P.T → P.T ≤ P.N^(τ+δ) → P.N^(σ-δ) ≤ P.V →
        ((Finset.range (Nat.floor (P.T/L)+1)).card : ℝ) ≤ 2*P.N^χ ∧
        ∃ W : ℕ → Finset ℝ,
          (∀ i : ℕ, W i ⊆ (P.localized L hL i).reflectedOrdinates ∧
            IsSeparated 2 (W i) ∧ InBaseInterval L (W i) ∧
            ((P.localized L hL i).ordinates.card : ℝ) ≤ C*P.N^ε*((W i).card : ℝ)) ∧
          ∀ α : ℝ,
            let I := Finset.range (Nat.floor (P.T/L)+1)
            let a := P.N^(-bourgainSharedFloorExponent α (τ-χ) ε)
            let J := bourgainZetaBandCount B (L+P.N^(ε/8)+1) a
            let F := C*(P.N^(2-2*σ+ε)+P.N^(2*(τ-χ)+4-8*σ+ε)+
              P.N^(-2*α+(τ-χ)+12-16*σ+ε))
            ∃ q ∈ Finset.range J, ∃ p ∈ Finset.range (bourgainRelativeLevelCount P.N (τ-χ)),
              ∃ k ∈ Finset.range (bourgainCorrelationLevelCount P.N B C α (τ-χ) ε),
              ∃ A : Finset ℕ, A ⊆ I ∧
              ∃ j : ℕ → ℕ,
                (∀ i ∈ A, (F < ((P.localized L hL i).ordinates.card : ℝ) ∧
                  BourgainComponentBand P.N L B C (τ-χ) α ε (W i) (j i) q ∧
                  (let d := bourgainRelativeLevel P.N (τ-χ) p
                  0 < d ∧ d ≤ 1 ∧
                  d*((W i).card : ℝ) ≤ (2 : ℝ)^(j i) ∧
                  (2 : ℝ)^(j i) < 2*d*((W i).card : ℝ) ∧
                  (∀ ℓ ∈ bourgainDifferenceLevel (W i) (j i),
                    d*((W i).card : ℝ) ≤ (bourgainDifferenceCount (W i) ℓ : ℝ) ∧
                    (bourgainDifferenceCount (W i) ℓ : ℝ) < 4*d*((W i).card : ℝ)) ∧
                  d*((bourgainDifferenceLevel (W i) (j i)).card : ℝ) ≤ 2*((W i).card : ℝ)) ∧
                  let d := bourgainRelativeLevel P.N (τ-χ) p
                  let r := bourgainZetaBandCorrelation
                    (bourgainDifferenceLevel (W i) (j i)) (P.N^(ε/8))
                    (L+P.N^(ε/8)+1) (a*(2 : ℝ)^q)
                  P.N^(-2*α)*P.N^(τ-χ) <
                    1024*(Nat.log 2 (W i).card+1 : ℕ)^2*(J : ℝ)^2*
                      C*(L+P.N^(ε/8)+1)^(1+ε)*d*r^2) ∧
                  (let H := P.N^(ε/8)
                  let U := L+H+1
                  let D := bourgainDifferenceLevel (W i) (j i)
                  let V := a*(2 : ℝ)^q
                  let r := bourgainZetaBandCorrelation D H U V
                  let μ := volume.real (bourgainZetaBand U V)
                  let s := bourgainCorrelationLevel P.N B C α (τ-χ) ε k
                  0 < s ∧ s ≤ r ∧ r < 2*s ∧ s ≤ 4*H ∧
                  s*Real.sqrt μ*Real.sqrt (D.card : ℝ) ≤ bourgainZetaBandMass D H U V ∧
                  bourgainZetaBandMass D H U V < 2*s*Real.sqrt μ*Real.sqrt (D.card : ℝ)) ∧
                  let d := bourgainRelativeLevel P.N (τ-χ) p
                  let s := bourgainCorrelationLevel P.N B C α (τ-χ) ε k
                  P.N^(-2*α)*P.N^(τ-χ) <
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
                  (I.card : ℝ)*F+C*P.N^ε*(J : ℝ)*(bourgainRelativeLevelCount P.N (τ-χ) : ℝ)*
                    (bourgainCorrelationLevelCount P.N B C α (τ-χ) ε : ℝ)*(S.card : ℝ) ∧
                ((P.ordinates.card : ℝ) ≤ (I.card : ℝ)*F ∨
                  let H := P.N^(ε/8)
                  let U := L+H+1
                  let V := a*(2 : ℝ)^q
                  S.Nonempty ∧
                  ∃ u ∈ Set.Ioc (-H) H,
                    (bourgainIntegerSlice H U V u).Nonempty ∧
                    P.V^2*(bourgainEliminatedCardCoefficient P.N L B C (τ-χ) α ε*
                        ((bourgainIntegerSlice H U V u).card : ℝ)*(S.card : ℝ)+
                      bourgainSliceSqrtCoefficient P.N L B C (τ-χ) α ε 1*
                        Real.sqrt ((bourgainIntegerSlice H U V u).card : ℝ)*
                          ((S.card : ℝ)^(3/2 : ℝ)/Real.sqrt (I.card : ℝ))) <
                    M*P.N^η*(2*(1+2*Real.pi*P.N^η)*D*P.T^θ*
                      (Real.sqrt (bourgainSecondBudget P.N P.T (S.card : ℝ))*
                        Real.sqrt (bourgainSecondBudget P.N P.T
                          ((bourgainIntegerSlice H U V u).card : ℝ))))) := by
  obtain ⟨B, C, δ₀, M, N₀, D, hB, hC, hδ₀, hδ₀₁, hM, hN₀, hD, hp⟩ :=
    bourgain_subdivided_physical_comparison (τ := τ-χ) hσ hη hθ hε hε₈
  let δ := min δ₀ ((τ-χ-1)/2)
  have hδ : 0 < δ := lt_min hδ₀ (by linarith)
  have hδold : δ ≤ δ₀ := min_le_left _ _
  have hδmargin : δ ≤ (τ-χ-1)/2 := min_le_right _ _
  refine ⟨B, C, δ, M, N₀, D, hB, hC, hδ, hδold.trans hδ₀₁,
    hδmargin, hM, hN₀, hD, ?_⟩
  intro P L hL hN hNN₀ hLeq hTlo hThi hVl
  have hscales := bourgain_subdivision_physical_scales P.one_lt_N hχ
    (by linarith : 1+δ ≤ τ-χ) hTlo hThi
  have hNL : P.N ≤ L := by simpa only [hLeq] using hscales.2.1
  have hLT : L ≤ P.T := by simpa only [hLeq] using hscales.2.2.1
  have hLu : L ≤ P.N^((τ-χ)+δ₀) := by
    calc
      L ≤ P.N^((τ-χ)+δ) := by simpa only [hLeq] using hscales.2.2.2.2
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le P.one_lt_N.le (by linarith)
  have hVold : P.N^(σ-δ₀) ≤ P.V :=
    (Real.rpow_le_rpow_of_exponent_le P.one_lt_N.le
      (by linarith : σ-δ₀ ≤ σ-δ)).trans hVl
  refine ⟨?_, hp P L hL hN hNN₀ hNL hLT hLu hVold⟩
  simpa only [hLeq] using bourgain_subdivision_bin_count P.one_lt_N.le P.T_pos hχ

/-- The ninth-row subdivision choice satisfies the actual physical comparison;
this supplies the source entry, not yet the limiting logarithmic dichotomy. -/
theorem bourgain_ninth_row_physical_comparison {σ τ η θ : ℝ}
    (hσ : 3/4 < σ) (hlower : 16*σ-11 ≤ τ) (hupper : 20*σ+τ/3 ≤ 16)
    (hη : 0 < η) (hθ : 0 < θ) {ε : ℝ} (hε : 0 < ε) (hε₈ : ε ≤ 8) :
    ∃ B C δ M N₀ D : ℝ,
      0 < B ∧ 2 ≤ C ∧ 0 < δ ∧ δ ≤ 1 ∧ δ ≤ (τ-(max 0 (4*σ+4*τ/3-5))-1)/2 ∧ 0 < M ∧ 2 ≤ N₀ ∧ 0 < D ∧
      ∀ (P : LargeValuePattern) (L : ℝ) (hL : 0 < L),
        C ≤ P.N → N₀ ≤ P.N → L = P.T/P.N^(max 0 (4*σ+4*τ/3-5)) →
        P.N^(τ-δ) ≤ P.T → P.T ≤ P.N^(τ+δ) → P.N^(σ-δ) ≤ P.V →
        ((Finset.range (Nat.floor (P.T/L)+1)).card : ℝ) ≤ 2*P.N^(max 0 (4*σ+4*τ/3-5)) ∧
        ∃ W : ℕ → Finset ℝ,
          (∀ i : ℕ, W i ⊆ (P.localized L hL i).reflectedOrdinates ∧
            IsSeparated 2 (W i) ∧ InBaseInterval L (W i) ∧
            ((P.localized L hL i).ordinates.card : ℝ) ≤ C*P.N^ε*((W i).card : ℝ)) ∧
          ∀ α : ℝ,
            let I := Finset.range (Nat.floor (P.T/L)+1)
            let a := P.N^(-bourgainSharedFloorExponent α (τ-(max 0 (4*σ+4*τ/3-5))) ε)
            let J := bourgainZetaBandCount B (L+P.N^(ε/8)+1) a
            let F := C*(P.N^(2-2*σ+ε)+P.N^(2*(τ-(max 0 (4*σ+4*τ/3-5)))+4-8*σ+ε)+
              P.N^(-2*α+(τ-(max 0 (4*σ+4*τ/3-5)))+12-16*σ+ε))
            ∃ q ∈ Finset.range J, ∃ p ∈ Finset.range (bourgainRelativeLevelCount P.N (τ-(max 0 (4*σ+4*τ/3-5)))),
              ∃ k ∈ Finset.range (bourgainCorrelationLevelCount P.N B C α (τ-(max 0 (4*σ+4*τ/3-5))) ε),
              ∃ A : Finset ℕ, A ⊆ I ∧
              ∃ j : ℕ → ℕ,
                (∀ i ∈ A, (F < ((P.localized L hL i).ordinates.card : ℝ) ∧
                  BourgainComponentBand P.N L B C (τ-(max 0 (4*σ+4*τ/3-5))) α ε (W i) (j i) q ∧
                  (let d := bourgainRelativeLevel P.N (τ-(max 0 (4*σ+4*τ/3-5))) p
                  0 < d ∧ d ≤ 1 ∧
                  d*((W i).card : ℝ) ≤ (2 : ℝ)^(j i) ∧
                  (2 : ℝ)^(j i) < 2*d*((W i).card : ℝ) ∧
                  (∀ ℓ ∈ bourgainDifferenceLevel (W i) (j i),
                    d*((W i).card : ℝ) ≤ (bourgainDifferenceCount (W i) ℓ : ℝ) ∧
                    (bourgainDifferenceCount (W i) ℓ : ℝ) < 4*d*((W i).card : ℝ)) ∧
                  d*((bourgainDifferenceLevel (W i) (j i)).card : ℝ) ≤ 2*((W i).card : ℝ)) ∧
                  let d := bourgainRelativeLevel P.N (τ-(max 0 (4*σ+4*τ/3-5))) p
                  let r := bourgainZetaBandCorrelation
                    (bourgainDifferenceLevel (W i) (j i)) (P.N^(ε/8))
                    (L+P.N^(ε/8)+1) (a*(2 : ℝ)^q)
                  P.N^(-2*α)*P.N^(τ-(max 0 (4*σ+4*τ/3-5))) <
                    1024*(Nat.log 2 (W i).card+1 : ℕ)^2*(J : ℝ)^2*
                      C*(L+P.N^(ε/8)+1)^(1+ε)*d*r^2) ∧
                  (let H := P.N^(ε/8)
                  let U := L+H+1
                  let D := bourgainDifferenceLevel (W i) (j i)
                  let V := a*(2 : ℝ)^q
                  let r := bourgainZetaBandCorrelation D H U V
                  let μ := volume.real (bourgainZetaBand U V)
                  let s := bourgainCorrelationLevel P.N B C α (τ-(max 0 (4*σ+4*τ/3-5))) ε k
                  0 < s ∧ s ≤ r ∧ r < 2*s ∧ s ≤ 4*H ∧
                  s*Real.sqrt μ*Real.sqrt (D.card : ℝ) ≤ bourgainZetaBandMass D H U V ∧
                  bourgainZetaBandMass D H U V < 2*s*Real.sqrt μ*Real.sqrt (D.card : ℝ)) ∧
                  let d := bourgainRelativeLevel P.N (τ-(max 0 (4*σ+4*τ/3-5))) p
                  let s := bourgainCorrelationLevel P.N B C α (τ-(max 0 (4*σ+4*τ/3-5))) ε k
                  P.N^(-2*α)*P.N^(τ-(max 0 (4*σ+4*τ/3-5))) <
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
                  (I.card : ℝ)*F+C*P.N^ε*(J : ℝ)*(bourgainRelativeLevelCount P.N (τ-(max 0 (4*σ+4*τ/3-5))) : ℝ)*
                    (bourgainCorrelationLevelCount P.N B C α (τ-(max 0 (4*σ+4*τ/3-5))) ε : ℝ)*(S.card : ℝ) ∧
                ((P.ordinates.card : ℝ) ≤ (I.card : ℝ)*F ∨
                  let H := P.N^(ε/8)
                  let U := L+H+1
                  let V := a*(2 : ℝ)^q
                  S.Nonempty ∧
                  ∃ u ∈ Set.Ioc (-H) H,
                    (bourgainIntegerSlice H U V u).Nonempty ∧
                    P.V^2*(bourgainEliminatedCardCoefficient P.N L B C (τ-(max 0 (4*σ+4*τ/3-5))) α ε*
                        ((bourgainIntegerSlice H U V u).card : ℝ)*(S.card : ℝ)+
                      bourgainSliceSqrtCoefficient P.N L B C (τ-(max 0 (4*σ+4*τ/3-5))) α ε 1*
                        Real.sqrt ((bourgainIntegerSlice H U V u).card : ℝ)*
                          ((S.card : ℝ)^(3/2 : ℝ)/Real.sqrt (I.card : ℝ))) <
                    M*P.N^η*(2*(1+2*Real.pi*P.N^η)*D*P.T^θ*
                      (Real.sqrt (bourgainSecondBudget P.N P.T (S.card : ℝ))*
                        Real.sqrt (bourgainSecondBudget P.N P.T
                          ((bourgainIntegerSlice H U V u).card : ℝ))))) := by
  obtain ⟨hχ, hmargin⟩ := bourgain_ninth_row_local_height_margin hσ hlower hupper
  exact bourgain_linked_subdivision_comparison hσ hχ hmargin hη hθ hε hε₈

end TaoTrudgianYang2025
