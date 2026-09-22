import TaoTrudgianYang2025.BourgainCorrelationGrid

/-!
# Common actual amplitude, relative multiplicity and correlation levels

Three weighted finite selections construct one original-source family.
Every selected component retains the full actual analytic data and now
has common correlation bounds with a proved logarithmic selection count.
The complete integer-slice shift and mixed moment are separate obligations.
-/

open MeasureTheory RiemannZeta.GuthMaynard
open scoped Interval Classical

noncomputable section

namespace TaoTrudgianYang2025

/-- Consume the actual two-level family and select a common correlation
level without losing its original coefficient polynomial or count conventions. -/
theorem bourgain_subdivided_common_correlation {σ τ : ℝ}
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
                    (bourgainCorrelationLevelCount P.N B C α τ ε : ℝ)*(S.card : ℝ) := by
  obtain ⟨B, C, δ, hB, hC, hδ, hδ₁, hp⟩ :=
    bourgain_subdivided_common_levels (τ := τ) hσ hε
  refine ⟨B, C, δ, hB, hC, hδ, hδ₁, ?_⟩
  intro P L hL hN hNL hTu hVl
  obtain ⟨W, hlocal, hfamily⟩ := hp P L hL hN hNL hTu hVl
  refine ⟨W, hlocal, ?_⟩
  intro α
  obtain ⟨q, hq, p, hp, A, hAI, j, hbands, _, hcardA, _, _, _, hglobal⟩ := hfamily α
  let I := Finset.range (Nat.floor (P.T/L)+1)
  let a := P.N^(-bourgainSharedFloorExponent α τ ε)
  let J := bourgainZetaBandCount B (L+P.N^(ε/8)+1) a
  let F := C*(P.N^(2-2*σ+ε)+P.N^(2*τ+4-8*σ+ε)+P.N^(-2*α+τ+12-16*σ+ε))
  let Q := bourgainRelativeLevelCount P.N τ
  let K := bourgainCorrelationLevelCount P.N B C α τ ε
  have hK : 0 < K := bourgainCorrelationLevelCount_pos _ _ _ _ _ _
  have hCp : 0 < C := by linarith
  have hNp : 0 < P.N := zero_lt_one.trans P.one_lt_N
  have hex (i : ℕ) : ∃ k ∈ Finset.range K, i ∈ A →
      let H := P.N^(ε/8)
      let U := L+H+1
      let D := bourgainDifferenceLevel (W i) (j i)
      let V := a*(2 : ℝ)^q
      let r := bourgainZetaBandCorrelation D H U V
      let μ := volume.real (bourgainZetaBand U V)
      let s := bourgainCorrelationLevel P.N B C α τ ε k
      0 < s ∧ s ≤ r ∧ r < 2*s ∧ s ≤ 4*H ∧
      s*Real.sqrt μ*Real.sqrt (D.card : ℝ) ≤ bourgainZetaBandMass D H U V ∧
      bourgainZetaBandMass D H U V < 2*s*Real.sqrt μ*Real.sqrt (D.card : ℝ) := by
    by_cases hi : i ∈ A
    · obtain ⟨k, hk, hc⟩ := bourgain_component_correlation_grid (P.localized L hL i)
        (hlocal i).1 (hbands i hi).2.1 hB hCp hε.le hδ₁ hTu
      exact ⟨k, hk, fun _ => hc⟩
    · exact ⟨0, Finset.mem_range.mpr hK, fun h => False.elim (hi h)⟩
  choose k hk hc using hex
  obtain ⟨k₀, hk₀, hheavy⟩ := bourgain_exists_heavy_component_fiber A
    (fun i => ((W i).card : ℝ)) k hK (fun i _ => hk i)
  let A₀ := A.filter (fun i => k i = k₀)
  have hsub : A₀ ⊆ A := Finset.filter_subset _ _
  have hselected : ∀ i ∈ A₀,
      (F < ((P.localized L hL i).ordinates.card : ℝ) ∧
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
      let s := bourgainCorrelationLevel P.N B C α τ ε k₀
      0 < s ∧ s ≤ r ∧ r < 2*s ∧ s ≤ 4*H ∧
      s*Real.sqrt μ*Real.sqrt (D.card : ℝ) ≤ bourgainZetaBandMass D H U V ∧
      bourgainZetaBandMass D H U V < 2*s*Real.sqrt μ*Real.sqrt (D.card : ℝ)) ∧
      let d := bourgainRelativeLevel P.N τ p
      let s := bourgainCorrelationLevel P.N B C α τ ε k₀
      P.N^(-2*α)*P.N^τ <
        4096*(Nat.log 2 (W i).card+1 : ℕ)^2*(J : ℝ)^2*
          C*(L+P.N^(ε/8)+1)^(1+ε)*d*s^2 := by
    intro i hi
    obtain ⟨hiA, heq⟩ := Finset.mem_filter.mp hi
    have hci := heq ▸ hc i hiA
    refine ⟨hbands i hiA, hci, ?_⟩
    let d := bourgainRelativeLevel P.N τ p
    let s := bourgainCorrelationLevel P.N B C α τ ε k₀
    let r := bourgainZetaBandCorrelation (bourgainDifferenceLevel (W i) (j i))
      (P.N^(ε/8)) (L+P.N^(ε/8)+1) (a*(2 : ℝ)^q)
    have hd : 0 < d := (hbands i hiA).2.2.1.1
    have hr : 0 ≤ r := (hci.1.trans_le hci.2.1).le
    have hrsq : r^2 ≤ (2*s)^2 :=
      pow_le_pow_left₀ hr hci.2.2.1.le 2
    have hcoef : 0 ≤ 1024*(Nat.log 2 (W i).card+1 : ℕ)^2*(J : ℝ)^2*
        C*(L+P.N^(ε/8)+1)^(1+ε)*d := by positivity
    calc
      _ < 1024*(Nat.log 2 (W i).card+1 : ℕ)^2*(J : ℝ)^2*
          C*(L+P.N^(ε/8)+1)^(1+ε)*d*r^2 := (hbands i hiA).2.2.2
      _ ≤ 1024*(Nat.log 2 (W i).card+1 : ℕ)^2*(J : ℝ)^2*
          C*(L+P.N^(ε/8)+1)^(1+ε)*d*(2*s)^2 :=
        mul_le_mul_of_nonneg_left hrsq hcoef
      _ = _ := by ring
  obtain ⟨hsource, hcard, hsep, hlarge⟩ := P.localized_retainedOriginal_union hL A₀ W
    (fun i _ => (hlocal i).1)
  refine ⟨q, hq, p, hp, k₀, hk₀, A₀, hsub.trans hAI, j, hselected,
    hsource, hcard, hsep, hlarge,
    (fun i _ ℓ => (P.localized L hL i).retainedOriginal_differenceCount (W i) ℓ), ?_⟩
  let S := A.biUnion (fun i => (P.localized L hL i).retainedOriginal (W i))
  let S₀ := A₀.biUnion (fun i => (P.localized L hL i).retainedOriginal (W i))
  have hcountA : (S.card : ℝ) = ∑ i ∈ A, ((W i).card : ℝ) := by exact_mod_cast hcardA
  have hcount : (S₀.card : ℝ) = ∑ i ∈ A₀, ((W i).card : ℝ) := by exact_mod_cast hcard
  have hsourceCount : (S.card : ℝ) ≤ (K : ℝ)*(S₀.card : ℝ) := by
    rw [hcountA, hcount]
    exact hheavy
  have hcoef : 0 ≤ C*P.N^ε*(J : ℝ)*(Q : ℝ) := by positivity
  change (P.ordinates.card : ℝ) ≤
    (I.card : ℝ)*F+C*P.N^ε*(J : ℝ)*(Q : ℝ)*(K : ℝ)*(S₀.card : ℝ)
  calc
    _ ≤ (I.card : ℝ)*F+C*P.N^ε*(J : ℝ)*(Q : ℝ)*(S.card : ℝ) := hglobal
    _ ≤ (I.card : ℝ)*F+C*P.N^ε*(J : ℝ)*(Q : ℝ)*((K : ℝ)*(S₀.card : ℝ)) :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left hsourceCount hcoef)
    _ = _ := by ring

end TaoTrudgianYang2025
