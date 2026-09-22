import TaoTrudgianYang2025.BourgainCorrelationProduct

/-!
# Common actual amplitude and relative multiplicity levels

Two proved finite selections retain an original-source union. The shared
relative band controls literal ordered difference counts within a factor
four. Correlation selection and the full mixed-moment comparison are left
for downstream consumers.
-/

open MeasureTheory RiemannZeta.GuthMaynard
open scoped Interval Classical

noncomputable section

namespace TaoTrudgianYang2025

/-- A common actual zeta band and relative difference scale across the
retained large components, with both finite selection losses explicit. -/
theorem bourgain_subdivided_common_levels {σ τ : ℝ}
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
            ∃ q ∈ Finset.range J, ∃ p ∈ Finset.range (bourgainRelativeLevelCount P.N τ),
              ∃ A : Finset ℕ, A ⊆ I ∧
              ∃ j : ℕ → ℕ,
                (∀ i ∈ A, F < ((P.localized L hL i).ordinates.card : ℝ) ∧
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
                let S := A.biUnion (fun i => (P.localized L hL i).retainedOriginal (W i))
                S ⊆ P.ordinates ∧ S.card = ∑ i ∈ A, (W i).card ∧
                IsSeparated 1 S ∧
                (∀ t ∈ S, P.V ≤ ‖∑ n ∈ P.indices, P.coeff n*dirichletPhase n t‖) ∧
                (∀ i ∈ A, ∀ ℓ : ℤ,
                  bourgainDifferenceCount ((P.localized L hL i).retainedOriginal (W i)) ℓ =
                    bourgainDifferenceCount (W i) ℓ) ∧
                (P.ordinates.card : ℝ) ≤
                  (I.card : ℝ)*F+C*P.N^ε*(J : ℝ)*(bourgainRelativeLevelCount P.N τ : ℝ)*(S.card : ℝ) := by
  obtain ⟨B, C, δ, hB, hC, hδ, hδ₁, hp⟩ :=
    bourgain_subdivided_common_band (τ := τ) hσ hε
  refine ⟨B, C, δ, hB, hC, hδ, hδ₁, ?_⟩
  intro P L hL hN hNL hTu hVl
  obtain ⟨W, hlocal, hfamily⟩ := hp P L hL hN hNL hTu hVl
  refine ⟨W, hlocal, ?_⟩
  intro α
  obtain ⟨q, hq, A, hAI, j, hbands, _, hcardA, _, _, _, hglobal⟩ := hfamily α
  let I := Finset.range (Nat.floor (P.T/L)+1)
  let a := P.N^(-bourgainSharedFloorExponent α τ ε)
  let J := bourgainZetaBandCount B (L+P.N^(ε/8)+1) a
  let F := C*(P.N^(2-2*σ+ε)+P.N^(2*τ+4-8*σ+ε)+P.N^(-2*α+τ+12-16*σ+ε))
  let Q := bourgainRelativeLevelCount P.N τ
  have hQ : 0 < Q := bourgainRelativeLevelCount_pos _ _
  have hN2 : 2 ≤ P.N := hC.trans hN
  have hex (i : ℕ) : ∃ p ∈ Finset.range Q, i ∈ A →
      let d := bourgainRelativeLevel P.N τ p
      0 < d ∧ d ≤ 1 ∧
      d*((W i).card : ℝ) ≤ (2 : ℝ)^(j i) ∧
      (2 : ℝ)^(j i) < 2*d*((W i).card : ℝ) ∧
      (∀ ℓ ∈ bourgainDifferenceLevel (W i) (j i),
        d*((W i).card : ℝ) ≤ (bourgainDifferenceCount (W i) ℓ : ℝ) ∧
        (bourgainDifferenceCount (W i) ℓ : ℝ) < 4*d*((W i).card : ℝ)) ∧
      d*((bourgainDifferenceLevel (W i) (j i)).card : ℝ) ≤ 2*((W i).card : ℝ) := by
    by_cases hi : i ∈ A
    · obtain ⟨p, hp, hrel⟩ := bourgain_retained_relative_level (P.localized L hL i)
        (hlocal i).1 (j i) (hbands i hi).2.2.2.1 hN2 hδ₁ hTu
      exact ⟨p, hp, fun _ => hrel⟩
    · exact ⟨0, Finset.mem_range.mpr hQ, fun h => False.elim (hi h)⟩
  choose p hp hrel using hex
  obtain ⟨p₀, hp₀, hheavy⟩ := bourgain_exists_heavy_component_fiber A
    (fun i => ((W i).card : ℝ)) p hQ (fun i _ => hp i)
  let A₀ := A.filter (fun i => p i = p₀)
  have hsub : A₀ ⊆ A := Finset.filter_subset _ _
  have hselected : ∀ i ∈ A₀,
      F < ((P.localized L hL i).ordinates.card : ℝ) ∧
      BourgainComponentBand P.N L B C τ α ε (W i) (j i) q ∧
      (let d := bourgainRelativeLevel P.N τ p₀
      0 < d ∧ d ≤ 1 ∧
      d*((W i).card : ℝ) ≤ (2 : ℝ)^(j i) ∧
      (2 : ℝ)^(j i) < 2*d*((W i).card : ℝ) ∧
      (∀ ℓ ∈ bourgainDifferenceLevel (W i) (j i),
        d*((W i).card : ℝ) ≤ (bourgainDifferenceCount (W i) ℓ : ℝ) ∧
        (bourgainDifferenceCount (W i) ℓ : ℝ) < 4*d*((W i).card : ℝ)) ∧
      d*((bourgainDifferenceLevel (W i) (j i)).card : ℝ) ≤ 2*((W i).card : ℝ)) ∧
      let d := bourgainRelativeLevel P.N τ p₀
      let r := bourgainZetaBandCorrelation
        (bourgainDifferenceLevel (W i) (j i)) (P.N^(ε/8))
        (L+P.N^(ε/8)+1) (a*(2 : ℝ)^q)
      P.N^(-2*α)*P.N^τ <
        1024*(Nat.log 2 (W i).card+1 : ℕ)^2*(J : ℝ)^2*
          C*(L+P.N^(ε/8)+1)^(1+ε)*d*r^2 := by
    intro i hi
    obtain ⟨hiA, heq⟩ := Finset.mem_filter.mp hi
    have hri := heq ▸ hrel i hiA
    have hproduct := (hbands i hiA).2.relative_correlation_lower
      (zero_lt_one.trans P.one_lt_N) hri.2.2.2.1.le
    exact ⟨(hbands i hiA).1, (hbands i hiA).2, hri, hproduct⟩
  obtain ⟨hsource, hcard, hsep, hlarge⟩ := P.localized_retainedOriginal_union hL A₀ W
    (fun i _ => (hlocal i).1)
  refine ⟨q, hq, p₀, hp₀, A₀, hsub.trans hAI, j, hselected,
    hsource, hcard, hsep, hlarge,
    (fun i _ ℓ => (P.localized L hL i).retainedOriginal_differenceCount (W i) ℓ), ?_⟩
  let S := A.biUnion (fun i => (P.localized L hL i).retainedOriginal (W i))
  let S₀ := A₀.biUnion (fun i => (P.localized L hL i).retainedOriginal (W i))
  have hcountA : (S.card : ℝ) = ∑ i ∈ A, ((W i).card : ℝ) := by
    exact_mod_cast hcardA
  have hcount : (S₀.card : ℝ) = ∑ i ∈ A₀, ((W i).card : ℝ) := by
    exact_mod_cast hcard
  have hsourceCount : (S.card : ℝ) ≤ (Q : ℝ)*(S₀.card : ℝ) := by
    rw [hcountA, hcount]
    exact hheavy
  have hCp : 0 < C := by linarith
  have hNp : 0 < P.N := zero_lt_one.trans P.one_lt_N
  have hK : 0 ≤ C*P.N^ε*(J : ℝ) := by positivity
  change (P.ordinates.card : ℝ) ≤
    (I.card : ℝ)*F+C*P.N^ε*(J : ℝ)*(Q : ℝ)*(S₀.card : ℝ)
  calc
    _ ≤ (I.card : ℝ)*F+C*P.N^ε*(J : ℝ)*(S.card : ℝ) := hglobal
    _ ≤ (I.card : ℝ)*F+C*P.N^ε*(J : ℝ)*((Q : ℝ)*(S₀.card : ℝ)) :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left hsourceCount hK)
    _ = _ := by ring

end TaoTrudgianYang2025
