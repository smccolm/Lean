import TaoTrudgianYang2025.BourgainMixedLower
import TaoTrudgianYang2025.BourgainSliceGeometry

/-!
# Mixed lower bounds on the actual original-source component union

The disjoint inverse reflections are retained throughout. Their strict ordered
difference counts feed the local second moment of the original polynomial,
then the full common-shift comparison supplies both source lower terms.
-/

open MeasureTheory RiemannZeta.GuthMaynard Set
open scoped Interval Classical

noncomputable section

namespace TaoTrudgianYang2025

/-- Sum actual local components without identifying distinct reflection origins. -/
theorem bourgain_subdivided_mixed_difference_counts {η : ℝ} (hη : 0 < η) :
    ∃ M N₀ : ℝ, 0 < M ∧ 2 ≤ N₀ ∧ ∀ P : LargeValuePattern,
      N₀ ≤ P.N → ∀ σ δ : ℝ, 0 ≤ σ → δ ≤ 1 → P.N^(σ-δ) ≤ P.V →
      ∀ (L : ℝ) (hL : 0 < L) (A : Finset ℕ) (W : ℕ → Finset ℝ),
        (∀ i ∈ A, W i ⊆ (P.localized L hL i).reflectedOrdinates) →
        (∀ i ∈ A, IsSeparated 2 (W i)) → ∀ D : Finset ℤ,
        let S := A.biUnion (fun i => (P.localized L hL i).retainedOriginal (W i))
        P.V^2*(∑ i ∈ A, ∑ ℓ ∈ D, (bourgainDifferenceCount (W i) ℓ : ℝ)) ≤
          M*P.N^η*
            (∫ u in -(1+2*Real.pi*P.N^η)..(1+2*Real.pi*P.N^η),
              ∑ t ∈ S, ∑ ℓ ∈ D,
                ‖∑ n ∈ P.indices, P.coeff n*dirichletPhase n (t-(ℓ : ℝ)+u)‖^2) := by
  obtain ⟨M, N₀, hM, hN₀, hm⟩ := bourgain_mixed_local_difference_counts hη
  refine ⟨M, N₀, hM, hN₀, ?_⟩
  intro P hN σ δ hσ hδ hV L hL A W hsub hsep D
  let O := fun i => (P.localized L hL i).retainedOriginal (W i)
  let R := 1+2*Real.pi*P.N^η
  let f := fun (t : ℝ) (u : ℝ) =>
    ∑ ℓ ∈ D, ‖∑ n ∈ P.indices, P.coeff n*dirichletPhase n (t-(ℓ : ℝ)+u)‖^2
  have hfc (t : ℝ) : Continuous (f t) := by
    apply continuous_finsetSum
    intro ℓ hℓ
    exact (P.polynomial_norm_continuous.comp (by fun_prop)).pow 2
  have hdis : (A : Set ℕ).PairwiseDisjoint O := by
    intro i hi j hj hij
    exact P.localized_retainedOriginal_disjoint hL hij (hsub i hi) (hsub j hj)
  have hi (i : ℕ) (hiA : i ∈ A) :
      P.V^2*(∑ ℓ ∈ D, (bourgainDifferenceCount (W i) ℓ : ℝ)) ≤
      M*P.N^η*(∫ u in -R..R, ∑ t ∈ O i, f t u) := by
    have hout := P.localized_retainedOriginal hL i (hsub i hiA) (hsep i hiA)
    have hb := hm P hN σ δ hσ hδ hV (O i) hout.2.1 hout.2.2.2.1 D
    simpa only [O, LargeValuePattern.retainedOriginal_differenceCount] using hb
  have hsum := Finset.sum_le_sum hi
  rw [← Finset.mul_sum] at hsum
  have hinter :
      (∫ u in -R..R, ∑ t ∈ A.biUnion O, f t u) =
        ∑ i ∈ A, ∫ u in -R..R, ∑ t ∈ O i, f t u := by
    simp_rw [Finset.sum_biUnion hdis]
    apply intervalIntegral.integral_finsetSum
    intro i hiA
    apply Continuous.intervalIntegrable
    exact continuous_finsetSum _ (fun t _ => hfc t)
  change P.V^2*(∑ i ∈ A, ∑ ℓ ∈ D, (bourgainDifferenceCount (W i) ℓ : ℝ)) ≤
    M*P.N^η*(∫ u in -R..R, ∑ t ∈ A.biUnion O, f t u)
  rw [hinter]
  calc
    _ ≤ ∑ i ∈ A, M*P.N^η*(∫ u in -R..R, ∑ t ∈ O i, f t u) := hsum
    _ = _ := by rw [Finset.mul_sum]

/-- Actual multiplicity lower bounds on selected difference sets survive
intersection with the complete integer slice and summation over components. -/
theorem bourgain_relative_slice_weight_le (A : Finset ℕ) (W : ℕ → Finset ℝ)
    (D : ℕ → Finset ℤ) (S : Finset ℤ) (d : ℝ)
    (hrel : ∀ i ∈ A, ∀ ℓ ∈ D i,
      d*((W i).card : ℝ) ≤ (bourgainDifferenceCount (W i) ℓ : ℝ)) :
    d*(∑ i ∈ A, ((W i).card : ℝ)*((D i ∩ S).card : ℝ)) ≤
      ∑ i ∈ A, ∑ ℓ ∈ S, (bourgainDifferenceCount (W i) ℓ : ℝ) := by
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i hi
  calc
    _ = ∑ _ℓ ∈ D i ∩ S, d*((W i).card : ℝ) := by
      simp only [Finset.sum_const, nsmul_eq_mul]
      ring
    _ ≤ ∑ ℓ ∈ D i ∩ S, (bourgainDifferenceCount (W i) ℓ : ℝ) :=
      Finset.sum_le_sum (fun ℓ hℓ => hrel i hi ℓ (Finset.mem_inter.mp hℓ).1)
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.inter_subset_right)
      (fun _ _ _ => Nat.cast_nonneg _)

/-- The full common-shift comparison enters the actual original polynomial's
mixed moment. The local mean is proved above, not assumed as a hypothesis. -/
theorem bourgain_component_family_mixed_lower {η : ℝ} (hη : 0 < η) :
    ∃ M N₀ : ℝ, 0 < M ∧ 2 ≤ N₀ ∧ ∀ P : LargeValuePattern,
      N₀ ≤ P.N → ∀ σ δ : ℝ, 0 ≤ σ → δ ≤ 1 → P.N^(σ-δ) ≤ P.V →
      ∀ (L : ℝ) (hL : 0 < L) (A : Finset ℕ), A.Nonempty →
      ∀ (W : ℕ → Finset ℝ) (j : ℕ → ℕ) (q : ℕ) (B C τ α ε s d : ℝ),
        (∀ i ∈ A, W i ⊆ (P.localized L hL i).reflectedOrdinates) →
        (∀ i ∈ A, IsSeparated 2 (W i)) → L ≤ P.N^(τ+δ) →
        (∀ i ∈ A, BourgainComponentBand P.N L B C τ α ε (W i) (j i) q) →
        0 < s → 0 < d →
        (∀ i ∈ A, (2 : ℝ)^(j i) ≤ 2*d*((W i).card : ℝ)) →
        (∀ i ∈ A, ∀ ℓ ∈ bourgainDifferenceLevel (W i) (j i),
          d*((W i).card : ℝ) ≤ (bourgainDifferenceCount (W i) ℓ : ℝ)) →
        (∀ i ∈ A, s ≤ bourgainZetaBandCorrelation
          (bourgainDifferenceLevel (W i) (j i)) (P.N^(ε/8)) (L+P.N^(ε/8)+1)
          (P.N^(-bourgainSharedFloorExponent α τ ε)*(2 : ℝ)^q)) →
        let H := P.N^(ε/8)
        let U := L+H+1
        let V := P.N^(-bourgainSharedFloorExponent α τ ε)*(2 : ℝ)^q
        let S := A.biUnion (fun i => (P.localized L hL i).retainedOriginal (W i))
        ∃ u ∈ Ioc (-H) H,
          (bourgainIntegerSlice H U V u).Nonempty ∧
          P.V^2*d*(bourgainSliceCardCoefficient P.N ε s*
              ((bourgainIntegerSlice H U V u).card : ℝ)*(S.card : ℝ)+
            bourgainSliceSqrtCoefficient P.N L B C τ α ε d*
              Real.sqrt ((bourgainIntegerSlice H U V u).card : ℝ)*
                (∑ i ∈ A, ((W i).card : ℝ)^(3/2 : ℝ))) <
          M*P.N^η*(∫ v in -(1+2*Real.pi*P.N^η)..(1+2*Real.pi*P.N^η),
            ∑ t ∈ S, ∑ ℓ ∈ bourgainIntegerSlice H U V u,
              ‖∑ n ∈ P.indices, P.coeff n*dirichletPhase n (t-(ℓ : ℝ)+v)‖^2) := by
  obtain ⟨M, N₀, hM, hN₀, hm⟩ := bourgain_subdivided_mixed_difference_counts hη
  refine ⟨M, N₀, hM, hN₀, ?_⟩
  intro P hN σ δ hσ hδ hV L hL A hA W j q B C τ α ε s d
    hsub hsep hT hband hs hd hrel hcounts hcorr
  obtain ⟨u, hu, hnonempty, hshift⟩ := bourgain_component_family_slice
    P hL A hA W j q hsub hδ hT hband hs hd hrel hcorr
  let H := P.N^(ε/8)
  let U := L+H+1
  let V := P.N^(-bourgainSharedFloorExponent α τ ε)*(2 : ℝ)^q
  let K := bourgainIntegerSlice H U V u
  let S := A.biUnion (fun i => (P.localized L hL i).retainedOriginal (W i))
  have hcard : (S.card : ℝ) = ∑ i ∈ A, ((W i).card : ℝ) := by
    exact_mod_cast (P.localized_retainedOriginal_union hL A W hsub).2.1
  have hweighted := bourgain_relative_slice_weight_le A W
    (fun i => bourgainDifferenceLevel (W i) (j i)) K d hcounts
  have hmoment := hm P hN σ δ hσ hδ hV L hL A W hsub hsep K
  refine ⟨u, hu, hnonempty, ?_⟩
  rw [hcard]
  have hleft := mul_lt_mul_of_pos_left hshift (mul_pos (pow_pos P.V_pos 2) hd)
  have hmiddle := mul_le_mul_of_nonneg_left hweighted (sq_nonneg P.V)
  have hcompare := hleft.trans_le (by
    convert hmiddle using 1
    ring)
  exact hcompare.trans_le hmoment

end TaoTrudgianYang2025
