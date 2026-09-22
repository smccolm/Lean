import TaoTrudgianYang2025.BourgainMixedFamily

/-!
# The source pattern enters the full mixed-moment lower bound

The same retained local family precedes alpha. All common levels and
original-source data are preserved. An empty selected family returns the
actual small-component bound; otherwise both common-shift terms enter the
original polynomial's mixed local second moment. Small-power losses are
explicit and the Heath--Brown upper comparison remains downstream.
-/

open MeasureTheory RiemannZeta.GuthMaynard
open scoped Interval Classical

noncomputable section

namespace TaoTrudgianYang2025

/-- A source-pattern consumer of the two-term mixed lower estimate. -/
theorem bourgain_subdivided_mixed_lower {σ τ η : ℝ}
    (hσ : 3/4 < σ) (hη : 0 < η) {ε : ℝ} (hε : 0 < ε) :
    ∃ B C δ M N₀ : ℝ, 0 < B ∧ 2 ≤ C ∧ 0 < δ ∧ δ ≤ 1 ∧ 0 < M ∧ 2 ≤ N₀ ∧
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
                    P.V^2*d*(bourgainSliceCardCoefficient P.N ε s*
                        ((bourgainIntegerSlice H U V u).card : ℝ)*(S.card : ℝ)+
                      bourgainSliceSqrtCoefficient P.N L B C τ α ε d*
                        Real.sqrt ((bourgainIntegerSlice H U V u).card : ℝ)*
                          (∑ i ∈ A, ((W i).card : ℝ)^(3/2 : ℝ))) <
                    M*P.N^η*(∫ v in -(1+2*Real.pi*P.N^η)..(1+2*Real.pi*P.N^η),
                      ∑ t ∈ S, ∑ ℓ ∈ bourgainIntegerSlice H U V u,
                        ‖∑ n ∈ P.indices, P.coeff n*dirichletPhase n (t-(ℓ : ℝ)+v)‖^2)) := by
  obtain ⟨M, N₀, hM, hN₀, hmixed⟩ := bourgain_component_family_mixed_lower hη
  obtain ⟨B, C, δ, hB, hC, hδ, hδ₁, hp⟩ :=
    bourgain_subdivided_common_correlation (τ := τ) hσ hε
  refine ⟨B, C, δ, M, N₀, hB, hC, hδ, hδ₁, hM, hN₀, ?_⟩
  intro P L hL hN hNN₀ hNL hTu hVl
  obtain ⟨W, hlocal, hfamily⟩ := hp P L hL hN hNL hTu hVl
  refine ⟨W, hlocal, ?_⟩
  intro α
  obtain ⟨q, hq, p, hp, k, hk, A, hAI, j, hbands,
    hsource, hcard, hsep, hlarge, hdiff, hglobal⟩ := hfamily α
  refine ⟨q, hq, p, hp, k, hk, A, hAI, j, hbands,
    hsource, hcard, hsep, hlarge, hdiff, hglobal, ?_⟩
  by_cases hempty : A = ∅
  · left
    simpa only [hempty, Finset.biUnion_empty, Finset.card_empty, Nat.cast_zero,
      mul_zero, add_zero] using hglobal
  · right
    have hA := Finset.nonempty_iff_ne_empty.mpr hempty
    obtain ⟨i₀, hi₀⟩ := hA
    exact hmixed P hNN₀ σ δ (by linarith) hδ₁ hVl L hL A ⟨i₀, hi₀⟩ W j q
      B C τ α ε (bourgainCorrelationLevel P.N B C α τ ε k)
      (bourgainRelativeLevel P.N τ p)
      (fun i _ => (hlocal i).1) (fun i _ => (hlocal i).2.1) hTu
      (fun i hi => (hbands i hi).1.2.1)
      (hbands i₀ hi₀).2.1.1 (hbands i₀ hi₀).1.2.2.1.1
      (fun i hi => (hbands i hi).1.2.2.1.2.2.2.1.le)
      (fun i hi ℓ hℓ => ((hbands i hi).1.2.2.1.2.2.2.2.1 ℓ hℓ).1)
      (fun i hi => (hbands i hi).2.1.2.1)

end TaoTrudgianYang2025

