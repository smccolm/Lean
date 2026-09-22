import TaoTrudgianYang2025.BourgainRetainedPullback

/-!
# Actual subdivision with a shared zeta-amplitude grid

Every component is the existing localized source pattern. The theorem
constructs all retained subfamilies and pulls them back to one disjoint
union in the original source ordinates. Amplitude indices and normalized
parameters have not yet been made common across the large components.
-/

open MeasureTheory RiemannZeta.GuthMaynard
open scoped Interval Classical

noncomputable section

namespace TaoTrudgianYang2025

/-- The shared-grid alternative on every actual local component, together
with a globally separated original-source union and its exact packing cost. -/
theorem bourgain_subdivided_shared_grid {σ τ : ℝ}
    (hσ : 3/4 < σ) {ε : ℝ} (hε : 0 < ε) :
    ∃ B C δ : ℝ, 0 < B ∧ 2 ≤ C ∧ 0 < δ ∧ δ ≤ 1 ∧
      ∀ (P : LargeValuePattern) (L : ℝ) (hL : 0 < L),
        C ≤ P.N → P.N ≤ L → L ≤ P.N^(τ+δ) → P.N^(σ-δ) ≤ P.V →
        ∃ W : ℕ → Finset ℝ,
          (∀ i : ℕ, (W i) ⊆ (P.localized L hL i).reflectedOrdinates ∧ IsSeparated 2 (W i) ∧ InBaseInterval L (W i) ∧
          ((P.localized L hL i).ordinates.card : ℝ) ≤ C*P.N^ε*((W i).card : ℝ) ∧
          ∀ α : ℝ,
            ((P.localized L hL i).ordinates.card : ℝ) ≤ C *
              (P.N^(2-2*σ+ε)+P.N^(2*τ+4-8*σ+ε)+P.N^(-2*α+τ+12-16*σ+ε)) ∨
            ∃ j ∈ Finset.range (Nat.log 2 (W i).card+1),
              let D := bourgainDifferenceLevel (W i) j
              let H := P.N^(ε/8)
              let U := L+H+1
              let L := ∑ ℓ ∈ D, bourgainLocalZetaSquare H ℓ
              let A := bourgainSharedFloorExponent α τ ε
              let a := P.N^(-A)
              let J := bourgainZetaBandCount B U a
              D.Nonempty ∧ 2^j ≤ (W i).card ∧ 2^j*D.card ≤ 2*(W i).card^2 ∧
              ∃ q ∈ Finset.range J,
                let V := a*(2 : ℝ)^q
                let K := 2*(Nat.log 2 (W i).card+1 : ℕ)*(2 : ℝ)^(j+1)*(J : ℝ)*(2*V)^2
                let r := bourgainZetaBandCorrelation D H U V
                0 < L ∧ 0 < a ∧ 0 < V ∧ 0 < bourgainZetaBandMass D H U V ∧
                0 < volume.real (bourgainZetaBand U V) ∧
                P.N^(-α)*((W i).card : ℝ)^(3/2 : ℝ)*P.N^(τ/2) <
                  K*bourgainZetaBandMass D H U V ∧
                V^4*volume.real (bourgainZetaBand U V) ≤ C*U^(1+ε) ∧
                bourgainZetaBandMass D H U V ≤ 2*H*(D.card : ℝ) ∧
                bourgainZetaBandMass D H U V ≤
                  (2*Nat.ceil H+1 : ℕ)*volume.real (bourgainZetaBand U V) ∧
                0 < r ∧
                bourgainZetaBandMass D H U V =
                  r*Real.sqrt (volume.real (bourgainZetaBand U V))*Real.sqrt (D.card : ℝ) ∧
                r^2 ≤ 2*H*(2*Nat.ceil H+1 : ℕ) ∧
                r^2*volume.real (bourgainZetaBand U V) ≤ 4*H^2*(D.card : ℝ) ∧
                r^2*(D.card : ℝ) ≤ (2*Nat.ceil H+1 : ℕ)^2*volume.real (bourgainZetaBand U V) ∧
                (J : ℝ) ≤
                  2+(Real.log (4*B+1)+(|τ|+ε+1+A)*Real.log P.N)/Real.log 2 ∧
                ∃ u ∈ Set.Ioc (-H) H,
                  (D.filter fun ℓ : ℤ => (ℓ : ℝ)+u ∈ bourgainZetaBand U V).Nonempty ∧
                  P.N^(-α)*((W i).card : ℝ)^(3/2 : ℝ)*P.N^(τ/2) <
                    K*(2*H)*((D.filter fun ℓ : ℤ =>
                      (ℓ : ℝ)+u ∈ bourgainZetaBand U V).card : ℝ)) ∧
          let I := Finset.range (Nat.floor (P.T/L)+1)
          let S := I.biUnion (fun i => (P.localized L hL i).retainedOriginal (W i))
          S ⊆ P.ordinates ∧ S.card = ∑ i ∈ I, (W i).card ∧
          IsSeparated 1 S ∧
          (∀ t ∈ S, P.V ≤ ‖∑ n ∈ P.indices, P.coeff n * dirichletPhase n t‖) ∧
          (P.ordinates.card : ℝ) ≤ C*P.N^ε*(S.card : ℝ) ∧
          (∀ i : ℕ, ∀ ℓ : ℤ,
            bourgainDifferenceCount ((P.localized L hL i).retainedOriginal (W i)) ℓ =
              bourgainDifferenceCount (W i) ℓ) := by
  obtain ⟨B, C, δ, hB, hC, hδ, hδ₁, hp⟩ :=
    bourgain_retained_shared_grid_dichotomy (τ := τ) hσ hε
  refine ⟨B, C, δ, hB, hC, hδ, hδ₁, ?_⟩
  intro P L hL hN hNL hTu hVl
  have hlocal (i : ℕ) := hp (P.localized L hL i) hN hNL hTu hVl
  choose W hsub hsep hbase hpack halt using hlocal
  let I := Finset.range (Nat.floor (P.T/L)+1)
  let S := I.biUnion (fun i => (P.localized L hL i).retainedOriginal (W i))
  obtain ⟨hsource, hcard, hsepSource, hlarge⟩ :=
    P.localized_retainedOriginal_union hL I W (fun i _ => hsub i)
  refine ⟨W, (fun i => ⟨hsub i, hsep i, hbase i, hpack i, halt i⟩),
    hsource, hcard, hsepSource, hlarge, ?_,
    fun i ℓ => (P.localized L hL i).retainedOriginal_differenceCount (W i) ℓ⟩
  have hpartition : (P.ordinates.card : ℝ) =
      ∑ i ∈ I, ((P.localized L hL i).ordinates.card : ℝ) := by
    exact_mod_cast P.card_eq_sum_localized hL
  have hcount : (S.card : ℝ) = ∑ i ∈ I, ((W i).card : ℝ) := by exact_mod_cast hcard
  change (P.ordinates.card : ℝ) ≤ C*P.N^ε*(S.card : ℝ)
  rw [hpartition, hcount, Finset.mul_sum]
  exact Finset.sum_le_sum (fun i _ => hpack i)

end TaoTrudgianYang2025
