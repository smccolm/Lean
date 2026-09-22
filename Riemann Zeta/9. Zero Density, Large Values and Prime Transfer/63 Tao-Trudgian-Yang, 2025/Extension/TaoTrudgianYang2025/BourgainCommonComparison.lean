import TaoTrudgianYang2025.BourgainCommonMixed
import TaoTrudgianYang2025.BourgainMixedUpper

/-!
# The actual selected family consumes both mixed estimates

All three common levels and all original-source data are retained. The
Heath--Brown bound is proved for the selected union and complete integer slice,
rather than supplied as an independent analytic premise.
-/

open MeasureTheory RiemannZeta.GuthMaynard
open scoped Interval Classical

noncomputable section

namespace TaoTrudgianYang2025

/-- The full physical mixed comparison on the actual source-selected family. -/
theorem bourgain_subdivided_mixed_comparison {σ τ η θ : ℝ}
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
                  let d := bourgainRelativeLevel P.N τ p
                  let s := bourgainCorrelationLevel P.N B C α τ ε k
                  ∃ u ∈ Set.Ioc (-H) H,
                    (bourgainIntegerSlice H U V u).Nonempty ∧
                    ∀ E : ℝ, E₀ ≤ E → P.T ≤ E → 2*(U+H) ≤ E →
                    P.V^2*d*(bourgainSliceCardCoefficient P.N ε s*
                        ((bourgainIntegerSlice H U V u).card : ℝ)*(S.card : ℝ)+
                      bourgainSliceSqrtCoefficient P.N L B C τ α ε d*
                        Real.sqrt ((bourgainIntegerSlice H U V u).card : ℝ)*
                          (∑ i ∈ A, ((W i).card : ℝ)^(3/2 : ℝ))) <
                    M*P.N^η*(2*(1+2*Real.pi*P.N^η)*D*E^θ*
                      (Real.sqrt (bourgainSecondBudget P.N E (S.card : ℝ))*
                        Real.sqrt (bourgainSecondBudget P.N E
                          ((bourgainIntegerSlice H U V u).card : ℝ))))) := by
  obtain ⟨D, E₀, hD, hE₀, hupper⟩ := bourgain_actual_mixed_upper hθ
  obtain ⟨B, C, δ, M, N₀, hB, hC, hδ, hδ₁, hM, hN₀, hp⟩ :=
    bourgain_subdivided_mixed_lower (τ := τ) hσ hη hε
  refine ⟨B, C, δ, M, N₀, D, E₀, hB, hC, hδ, hδ₁, hM, hN₀, hD, hE₀, ?_⟩
  intro P L hL hN hNN₀ hNL hTu hVl
  obtain ⟨W, hlocal, hfamily⟩ := hp P L hL hN hNN₀ hNL hTu hVl
  refine ⟨W, hlocal, ?_⟩
  intro α
  obtain ⟨q, hq, p, hp, k, hk, A, hAI, j, hbands,
    hsource, hcard, hsep, hlarge, hdiff, hglobal, hbranch⟩ := hfamily α
  refine ⟨q, hq, p, hp, k, hk, A, hAI, j, hbands,
    hsource, hcard, hsep, hlarge, hdiff, hglobal, ?_⟩
  rcases hbranch with hsmall | ⟨u, hu, hZ, hlower⟩
  · exact Or.inl hsmall
  · right
    refine ⟨u, hu, hZ, ?_⟩
    intro E hE hPE hZE
    have hNpos : 0 < P.N := zero_lt_one.trans P.one_lt_N
    have hR : 0 ≤ 1+2*Real.pi*P.N^η := by positivity
    have hb := hupper P _ hsource (P.N^(ε/8)) (L+P.N^(ε/8)+1)
      (P.N^(-bourgainSharedFloorExponent α τ ε)*(2 : ℝ)^q) u
      (1+2*Real.pi*P.N^η) E ⟨hu.1.le, hu.2⟩ hR hE hPE hZE
    exact hlower.trans_le
      (mul_le_mul_of_nonneg_left hb (mul_nonneg hM.le (Real.rpow_nonneg hNpos.le η)))

end TaoTrudgianYang2025
