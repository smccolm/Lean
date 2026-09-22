import TaoTrudgianYang2025.BourgainComparisonPowerBudget
import TaoTrudgianYang2025.BourgainSelectionLosses

/-!
# Actual linked comparison with all finite factors expressed as power losses

The retained source set and complete zeta slice come from the constructed
family. Alpha is fixed before the loss constants. This is a finite theorem;
no logarithmic limiting dichotomy or ninth-row conclusion is asserted.
-/

open RiemannZeta.GuthMaynard
open scoped Classical

noncomputable section

namespace TaoTrudgianYang2025

theorem bourgain_linked_power_loss_comparison {σ τ χ α η θ κ ζ : ℝ}
    (hσ : 3/4 < σ) (hχ : 0 ≤ χ) (hmargin : 1 < τ-χ)
    (hη : 0 < η) (hθ : 0 < θ) (hκ : 0 < κ) (hζ : 0 < ζ)
    {ε : ℝ} (hε : 0 < ε) (hε₈ : ε ≤ 8) :
    ∃ B C δ K G H N₀ : ℝ,
      0 < B ∧ 2 ≤ C ∧ 0 < δ ∧ δ ≤ 1 ∧ δ ≤ (τ-χ-1)/2 ∧
      δ ≤ ζ ∧ 0 < K ∧ 0 < G ∧ 1 ≤ H ∧ 2 ≤ N₀ ∧
      ∀ (P : LargeValuePattern) (L : ℝ),
        C ≤ P.N → N₀ ≤ P.N → L = P.T/P.N^χ →
        P.N^(τ-δ) ≤ P.T → P.T ≤ P.N^(τ+δ) → P.N^(σ-δ) ≤ P.V →
        let a := P.N^(-bourgainSharedFloorExponent α (τ-χ) ε)
        let J := bourgainZetaBandCount B (L+P.N^(ε/8)+1) a
        let F := C*(P.N^(2-2*σ+ε)+P.N^(2*(τ-χ)+4-8*σ+ε)+
          P.N^(-2*α+(τ-χ)+12-16*σ+ε))
        let E := bourgainComparisonLoss (τ-χ) ε δ κ
        ∃ S : Finset ℝ, S ⊆ P.ordinates ∧ IsSeparated 1 S ∧
          (∀ t ∈ S, P.V ≤ ‖∑ n ∈ P.indices, P.coeff n*dirichletPhase n t‖) ∧
          (P.ordinates.card : ℝ) ≤ 2*P.N^χ*F+C*H*P.N^(ε+κ)*(S.card : ℝ) ∧
          ((P.ordinates.card : ℝ) ≤ 2*P.N^χ*F ∨
            S.Nonempty ∧ ∃ q ∈ Finset.range J, ∃ u ∈ Set.Ioc (-(P.N^(ε/8))) (P.N^(ε/8)),
              (bourgainIntegerSlice (P.N^(ε/8)) (L+P.N^(ε/8)+1) (a*(2 : ℝ)^q) u).Nonempty ∧
              let x := ((bourgainIntegerSlice (P.N^(ε/8)) (L+P.N^(ε/8)+1)
                (a*(2 : ℝ)^q) u).card : ℝ)
              P.N^(2*σ-2*δ)*
                (P.N^(-2*α-E)/G*x*(S.card : ℝ)+
                  P.N^(-α-E/2-χ/2)/Real.sqrt (2*G)*
                    Real.sqrt x*(S.card : ℝ)^(3/2 : ℝ)) <
                K*P.N^(2*η+(τ+δ)*θ)*
                  (Real.sqrt (bourgainSecondBudget P.N P.T (S.card : ℝ))*
                    Real.sqrt (bourgainSecondBudget P.N P.T x))) := by
  obtain ⟨B, C, δ₀, M, N₁, D, hB, hC, hδ₀, hδ₀₁, hδ₀margin, hM, hN₁, hD, hp⟩ :=
    bourgain_linked_subdivision_comparison (τ := τ) hσ hχ hmargin hη hθ hε hε₈
  let δ := min δ₀ ζ
  have hδ : 0 < δ := lt_min hδ₀ hζ
  have hδold : δ ≤ δ₀ := min_le_left _ _
  have hδ₁ : δ ≤ 1 := hδold.trans hδ₀₁
  have hδmargin : δ ≤ (τ-χ-1)/2 := hδold.trans hδ₀margin
  have hCp : 0 < C := by linarith
  obtain ⟨G, N₂, hG, hN₂, hcoeff⟩ :=
    bourgain_comparison_coefficients_uniform_power (α := α) (τ := τ-χ)
      hB hCp hε.le hε₈ hκ
  obtain ⟨H, N₃, hH, hN₃, hcounts⟩ :=
    bourgain_selection_counts_uniform_power (α := α) (τ := τ-χ)
      hB hCp.le hε.le hκ
  let N₀ := max N₁ (max N₂ N₃)
  let K := 2*M*(1+2*Real.pi)*D
  have hK : 0 < K := by dsimp only [K]; positivity
  refine ⟨B, C, δ, K, G, H, N₀, hB, hC, hδ, hδ₁, hδmargin,
    min_le_right _ _, hK, hG, hH, hN₁.trans (le_max_left _ _), ?_⟩
  intro P L hNC hN hLeq hTlo hThi hVl
  have hN₁P : N₁ ≤ P.N := (le_max_left _ _).trans hN
  have hN₂P : N₂ ≤ P.N := ((le_max_left _ _).trans (le_max_right _ _)).trans hN
  have hN₃P : N₃ ≤ P.N := ((le_max_right _ _).trans (le_max_right _ _)).trans hN
  have hNp : 0 < P.N := zero_lt_one.trans P.one_lt_N
  have hL : 0 < L := by rw [hLeq]; exact div_pos P.T_pos (Real.rpow_pos_of_pos hNp _)
  have hscales := bourgain_subdivision_physical_scales P.one_lt_N hχ
    (by linarith : 1+δ ≤ τ-χ) hTlo hThi
  have hNL : P.N ≤ L := by simpa only [hLeq] using hscales.2.1
  have hLu : L ≤ P.N^((τ-χ)+δ) := by simpa only [hLeq] using hscales.2.2.2.2
  have hTlo₀ : P.N^(τ-δ₀) ≤ P.T :=
    (Real.rpow_le_rpow_of_exponent_le P.one_lt_N.le (by linarith)).trans hTlo
  have hThi₀ : P.T ≤ P.N^(τ+δ₀) :=
    hThi.trans (Real.rpow_le_rpow_of_exponent_le P.one_lt_N.le (by linarith))
  have hVl₀ : P.N^(σ-δ₀) ≤ P.V :=
    (Real.rpow_le_rpow_of_exponent_le P.one_lt_N.le (by linarith)).trans hVl
  obtain ⟨hbin, W, _, hfamily⟩ := hp P L hL hNC hN₁P hLeq hTlo₀ hThi₀ hVl₀
  obtain ⟨q, hq, p, _, k, _, A, _, j, _,
    hsource, _, hsep, hlarge, _, hglobal, hbranch⟩ := hfamily α
  let S := A.biUnion (fun i => (P.localized L hL i).retainedOriginal (W i))
  let I := Finset.range (Nat.floor (P.T/L)+1)
  let J := bourgainZetaBandCount B (L+P.N^(ε/8)+1)
    (P.N^(-bourgainSharedFloorExponent α (τ-χ) ε))
  let F := C*(P.N^(2-2*σ+ε)+P.N^(2*(τ-χ)+4-8*σ+ε)+
    P.N^(-2*α+(τ-χ)+12-16*σ+ε))
  let E := bourgainComparisonLoss (τ-χ) ε δ κ
  have hF : 0 ≤ F := by dsimp only [F]; positivity
  have hsmall : (I.card : ℝ)*F ≤ 2*P.N^χ*F :=
    mul_le_mul_of_nonneg_right hbin hF
  have hselection :
      (J : ℝ)*(bourgainRelativeLevelCount P.N (τ-χ) : ℝ)*
        (bourgainCorrelationLevelCount P.N B C α (τ-χ) ε : ℝ) ≤ H*P.N^κ :=
    hcounts (P.localized L hL 0) δ hδ₁ hN₃P hLu
  have hcost : C*P.N^ε*(J : ℝ)*(bourgainRelativeLevelCount P.N (τ-χ) : ℝ)*
      (bourgainCorrelationLevelCount P.N B C α (τ-χ) ε : ℝ)*(S.card : ℝ) ≤
        C*H*P.N^(ε+κ)*(S.card : ℝ) := by
    calc
      _ = (C*P.N^ε*(S.card : ℝ))*((J : ℝ)*
          (bourgainRelativeLevelCount P.N (τ-χ) : ℝ)*
          (bourgainCorrelationLevelCount P.N B C α (τ-χ) ε : ℝ)) := by ring
      _ ≤ (C*P.N^ε*(S.card : ℝ))*(H*P.N^κ) :=
        mul_le_mul_of_nonneg_left hselection (by positivity)
      _ = _ := by rw [Real.rpow_add hNp]; ring
  refine ⟨S, hsource, hsep, hlarge, hglobal.trans (add_le_add hsmall hcost), ?_⟩
  rcases hbranch with hsmallSource | ⟨hSne, u, hu, hZ, hcomp⟩
  · exact Or.inl (hsmallSource.trans hsmall)
  · right
    refine ⟨hSne, q, hq, u, hu, hZ, ?_⟩
    let x := ((bourgainIntegerSlice (P.N^(ε/8)) (L+P.N^(ε/8)+1)
      (P.N^(-bourgainSharedFloorExponent α (τ-χ) ε)*(2 : ℝ)^q) u).card : ℝ)
    let R := (S.card : ℝ)
    have hx : 0 ≤ x := Nat.cast_nonneg _
    have hR : 0 ≤ R := Nat.cast_nonneg _
    have hI : (0 : ℝ) < I.card := by
      dsimp only [I]
      simp only [Finset.card_range]
      positivity
    obtain ⟨hγ, hβ⟩ := hcoeff P.N L δ hN₂P hNL hδ₁ hLu
    have hb := bourgain_sqrt_bin_coefficient hNp hG hI hbin hβ
    have hV : P.N^(2*σ-2*δ) ≤ P.V^2 := by
      calc
        _ = (P.N^(σ-δ))^2 := by
          rw [← Real.rpow_mul_natCast hNp.le]
          congr 1
          ring
        _ ≤ _ := pow_le_pow_left₀ (by positivity) hVl 2
    have hterm :
        P.N^(-2*α-E)/G*x*R+
          P.N^(-α-E/2-χ/2)/Real.sqrt (2*G)*Real.sqrt x*R^(3/2 : ℝ) ≤
        bourgainEliminatedCardCoefficient P.N L B C (τ-χ) α ε*x*R+
          bourgainSliceSqrtCoefficient P.N L B C (τ-χ) α ε 1*
            Real.sqrt x*(R^(3/2 : ℝ)/Real.sqrt (I.card : ℝ)) := by
      calc
        _ ≤ bourgainEliminatedCardCoefficient P.N L B C (τ-χ) α ε*x*R+
            (bourgainSliceSqrtCoefficient P.N L B C (τ-χ) α ε 1/Real.sqrt (I.card : ℝ))*
              Real.sqrt x*R^(3/2 : ℝ) := by
          exact add_le_add
            (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hγ hx) hR)
            (mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right hb (Real.sqrt_nonneg x)) (Real.rpow_nonneg hR _))
        _ = _ := by ring
    have hleft :
        P.N^(2*σ-2*δ)*(P.N^(-2*α-E)/G*x*R+
          P.N^(-α-E/2-χ/2)/Real.sqrt (2*G)*Real.sqrt x*R^(3/2 : ℝ)) ≤
        P.V^2*(bourgainEliminatedCardCoefficient P.N L B C (τ-χ) α ε*x*R+
          bourgainSliceSqrtCoefficient P.N L B C (τ-χ) α ε 1*
            Real.sqrt x*(R^(3/2 : ℝ)/Real.sqrt (I.card : ℝ))) :=
      mul_le_mul hV hterm (by positivity) (sq_nonneg _)
    have hfactor := bourgain_integration_power_factor P.one_lt_N.le P.T_pos.le
      hη.le hθ.le hM.le hD.le hThi
    have hright :
        M*P.N^η*(2*(1+2*Real.pi*P.N^η)*D*P.T^θ*
          (Real.sqrt (bourgainSecondBudget P.N P.T R)*
            Real.sqrt (bourgainSecondBudget P.N P.T x))) ≤
        K*P.N^(2*η+(τ+δ)*θ)*
          (Real.sqrt (bourgainSecondBudget P.N P.T R)*
            Real.sqrt (bourgainSecondBudget P.N P.T x)) := by
      simpa only [K, mul_assoc] using mul_le_mul_of_nonneg_right hfactor
        (mul_nonneg (Real.sqrt_nonneg (bourgainSecondBudget P.N P.T R))
          (Real.sqrt_nonneg (bourgainSecondBudget P.N P.T x)))
    exact (hleft.trans_lt hcomp).trans_le hright

end TaoTrudgianYang2025
