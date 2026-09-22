import TaoTrudgianYang2025.BourgainComponentSelection

/-!
# A common actual zeta-amplitude band on the large subdivision components

The predicate below records literal difference counts, zeta-band integrals
and measures. The consumer constructs its witnesses from the proved actual
subdivision theorem, then selects an actual fiber and its original-source union.
No common relative difference or correlation level is claimed here.
-/

open MeasureTheory RiemannZeta.GuthMaynard
open scoped Interval Classical

noncomputable section

namespace TaoTrudgianYang2025

/-- The full analytic data of one actual shared-grid component. This is
a named proposition, not an assumed analytic estimate. -/
def BourgainComponentBand (N T B C τ α ε : ℝ) (W : Finset ℝ) (j q : ℕ) : Prop :=
  j ∈ Finset.range (Nat.log 2 W.card+1) ∧
  let D := bourgainDifferenceLevel W j
  let H := N^(ε/8)
  let U := T+H+1
  let L := ∑ ℓ ∈ D, bourgainLocalZetaSquare H ℓ
  let A := bourgainSharedFloorExponent α τ ε
  let a := N^(-A)
  let J := bourgainZetaBandCount B U a
  D.Nonempty ∧ 2^j ≤ W.card ∧ 2^j*D.card ≤ 2*W.card^2 ∧
  q ∈ Finset.range J ∧
  let V := a*(2 : ℝ)^q
  let K := 2*(Nat.log 2 W.card+1 : ℕ)*(2 : ℝ)^(j+1)*(J : ℝ)*(2*V)^2
  let r := bourgainZetaBandCorrelation D H U V
  0 < L ∧ 0 < a ∧ 0 < V ∧ 0 < bourgainZetaBandMass D H U V ∧
  0 < volume.real (bourgainZetaBand U V) ∧
  N^(-α)*(W.card : ℝ)^(3/2 : ℝ)*N^(τ/2) <
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
  2+(Real.log (4*B+1)+(|τ|+ε+1+A)*Real.log N)/Real.log 2 ∧
  ∃ u ∈ Set.Ioc (-H) H,
  (D.filter fun ℓ : ℤ => (ℓ : ℝ)+u ∈ bourgainZetaBand U V).Nonempty ∧
  N^(-α)*(W.card : ℝ)^(3/2 : ℝ)*N^(τ/2) <
  K*(2*H)*((D.filter fun ℓ : ℤ =>
  (ℓ : ℝ)+u ∈ bourgainZetaBand U V).card : ℝ)

/-- Consume the actual subdivision, classify at its proved small bound,
and select one common amplitude band while retaining the original source
polynomial. The exact number of bins and amplitude bands are not absorbed. -/
theorem bourgain_subdivided_common_band {σ τ : ℝ}
    (hσ : 3/4 < σ) {ε : ℝ} (hε : 0 < ε) :
    ∃ B C δ : ℝ, 0 < B ∧ 2 ≤ C ∧ 0 < δ ∧ δ ≤ 1 ∧
      ∀ (P : LargeValuePattern) (L : ℝ) (hL : 0 < L),
        C ≤ P.N → P.N ≤ L → L ≤ P.N^(τ+δ) → P.N^(σ-δ) ≤ P.V →
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
            ∃ q ∈ Finset.range J, ∃ A : Finset ℕ, A ⊆ I ∧
              ∃ j : ℕ → ℕ,
                (∀ i ∈ A, F < ((P.localized L hL i).ordinates.card : ℝ) ∧
                  BourgainComponentBand P.N L B C τ α ε (W i) (j i) q) ∧
                let S := A.biUnion (fun i => (P.localized L hL i).retainedOriginal (W i))
                S ⊆ P.ordinates ∧ S.card = ∑ i ∈ A, (W i).card ∧
                IsSeparated 1 S ∧
                (∀ t ∈ S, P.V ≤ ‖∑ n ∈ P.indices, P.coeff n*dirichletPhase n t‖) ∧
                (∀ i ∈ A, ∀ ℓ : ℤ,
                  bourgainDifferenceCount ((P.localized L hL i).retainedOriginal (W i)) ℓ =
                    bourgainDifferenceCount (W i) ℓ) ∧
                (P.ordinates.card : ℝ) ≤
                  (I.card : ℝ)*F+C*P.N^ε*(J : ℝ)*(S.card : ℝ) := by
  obtain ⟨B, C, δ, hB, hC, hδ, hδ₁, hp⟩ :=
    bourgain_subdivided_shared_grid (τ := τ) hσ hε
  refine ⟨B, C, δ, hB, hC, hδ, hδ₁, ?_⟩
  intro P L hL hN hNL hTu hVl
  obtain ⟨W, hlocal, _⟩ := hp P L hL hN hNL hTu hVl
  refine ⟨W, (fun i => ⟨(hlocal i).1, (hlocal i).2.1,
    (hlocal i).2.2.1, (hlocal i).2.2.2.1⟩), ?_⟩
  intro α
  let I := Finset.range (Nat.floor (P.T/L)+1)
  let a := P.N^(-bourgainSharedFloorExponent α τ ε)
  let J := bourgainZetaBandCount B (L+P.N^(ε/8)+1) a
  let F := C*(P.N^(2-2*σ+ε)+P.N^(2*τ+4-8*σ+ε)+P.N^(-2*α+τ+12-16*σ+ε))
  have hex (i : ℕ) : ∃ j q : ℕ,
      F < ((P.localized L hL i).ordinates.card : ℝ) →
        BourgainComponentBand P.N L B C τ α ε (W i) j q := by
    by_cases h : F < ((P.localized L hL i).ordinates.card : ℝ)
    · rcases (hlocal i).2.2.2.2 α with hs | ⟨j, hj, hD, hpow, hsize, q, hq, hrest⟩
      · exact False.elim (not_lt_of_ge hs h)
      · exact ⟨j, q, fun _ => ⟨hj, hD, hpow, hsize, hq, hrest⟩⟩
    · exact ⟨0, 0, fun hi => False.elim (h hi)⟩
  choose j q hband using hex
  have hCp : 0 < C := by linarith
  have hNp : 0 < P.N := zero_lt_one.trans P.one_lt_N
  have hF : 0 ≤ F := by dsimp only [F]; positivity
  have hK : 0 ≤ C*P.N^ε := by positivity
  have hJ : 0 < J := bourgainZetaBandCount_pos _ _ _
  obtain ⟨q₀, hq₀, hbound⟩ := bourgain_small_large_component_selection I
    (fun i => ((P.localized L hL i).ordinates.card : ℝ))
    (fun i => ((W i).card : ℝ)) q hF hK hJ
    (fun i _ _ => (hlocal i).2.2.2.1)
    (fun i _ hi => (hband i hi).2.2.2.2.1)
  let A := I.filter (fun i => F < ((P.localized L hL i).ordinates.card : ℝ) ∧ q i = q₀)
  have hsubA : A ⊆ I := Finset.filter_subset _ _
  have hselected : ∀ i ∈ A,
      F < ((P.localized L hL i).ordinates.card : ℝ) ∧
        BourgainComponentBand P.N L B C τ α ε (W i) (j i) q₀ := by
    intro i hi
    obtain ⟨_, hlarge, hq⟩ := Finset.mem_filter.mp hi
    exact ⟨hlarge, hq ▸ hband i hlarge⟩
  obtain ⟨hsource, hcard, hsep, hlarge⟩ := P.localized_retainedOriginal_union hL A W
    (fun i _ => (hlocal i).1)
  refine ⟨q₀, hq₀, A, hsubA, j, hselected, hsource, hcard, hsep, hlarge,
    (fun i _ ℓ => (P.localized L hL i).retainedOriginal_differenceCount (W i) ℓ), ?_⟩
  have hpartition : (P.ordinates.card : ℝ) =
      ∑ i ∈ I, ((P.localized L hL i).ordinates.card : ℝ) := by
    exact_mod_cast P.card_eq_sum_localized hL
  have hcount : ((A.biUnion (fun i =>
      (P.localized L hL i).retainedOriginal (W i))).card : ℝ) =
        ∑ i ∈ A, ((W i).card : ℝ) := by exact_mod_cast hcard
  change (P.ordinates.card : ℝ) ≤ (I.card : ℝ)*F+
    C*P.N^ε*(J : ℝ)*((A.biUnion (fun i =>
      (P.localized L hL i).retainedOriginal (W i))).card : ℝ)
  rw [hpartition, hcount]
  exact hbound

end TaoTrudgianYang2025
