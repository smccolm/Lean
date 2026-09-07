import PrimeShell.ExtendedFamilyHyps
import Zeta23.XiPrime.ExplicitFormula.XiEFAssembly

open scoped BigOperators ArithmeticFunction ComplexConjugate
open Complex MeasureTheory Set Filter Topology

noncomputable section

namespace Zeta23
namespace XiPrime

open Zeta23.WeilEF (Hfn)

/-- The ξ′ explicit-formula assembly in the full contour range `3λ < 4`.
This is the released `xiEF_of` proof with the exact wider-window estimate
`L ≤ λ log T`; the resulting extra factor `λ²` is retained in the
power/log absorption rather than discarded. -/
theorem extendedXiEF_of (hGB : GramBridgeFacts) (hCO : CoeffFacts)
    (Z : ZeroConfig) (hZ : Z.carrier = {ρ : ℂ | IsXiDerivZero ρ})
    (hm : ∀ ρ ∈ Z.carrier, Z.mult ρ = xiDerivMult ρ)
    (Pf : ℝ → Params) (hPf : PrimeShell.ExtendedFamilyHyps Pf)
    (hTW : TestWeightFacts Pf) : XiEF Z Pf := by
  obtain ⟨lam, Cφ, T₁, hlam0, hlam4, hCφ0, hT₁0, hper⟩ := hPf.perT
  obtain ⟨Cw, Tw, hCw0, htw⟩ := hTW
  obtain ⟨⟨R₀, hR₀0, hco⟩, hconj⟩ := hCO
  obtain ⟨K, TJ, hK0, hTJ8, hJ⟩ :=
    Jcorr_estimate xiDerivZerosInStrip_holds
  obtain ⟨Ca, Ta, hCa0, habs⟩ :=
    PrimeShell.pow_log_absorb_fullChain lam hlam4
      (A := lam ^ 2) (sq_nonneg lam)
  set δ : ℝ := (1 - 3 * lam / 4) / 2 with hδ
  have hδ0 : 0 < δ := by rw [hδ]; linarith
  set T₀ : ℝ :=
    max (max (max T₁ Tw) (max TJ Ta)) (Real.exp (2 * (R₀ + 1)))
  refine ⟨2 * K * Cw * Ca, δ, T₀, hδ0, fun T hT k l => ?_⟩
  have hT₁ : T₁ ≤ T :=
    le_trans (le_trans (le_trans (le_max_left _ _) (le_max_left _ _))
      (le_max_left _ _)) hT
  have hTw : Tw ≤ T :=
    le_trans (le_trans (le_trans (le_max_right _ _) (le_max_left _ _))
      (le_max_left _ _)) hT
  have hTJ : TJ ≤ T :=
    le_trans (le_trans (le_trans (le_max_left _ _) (le_max_right _ _))
      (le_max_left _ _)) hT
  have hTa : Ta ≤ T :=
    le_trans (le_trans (le_trans (le_max_right _ _) (le_max_right _ _))
      (le_max_left _ _)) hT
  have hTR : Real.exp (2 * (R₀ + 1)) ≤ T :=
    le_trans (le_max_right _ _) hT
  have hT8 : 8 ≤ T := le_trans hTJ8 hTJ
  have hT0 : 0 < T := by linarith
  obtain ⟨-, hL1, -, hX, hLlog, hX34, hφC2, hsupp, hL0, -, -, -⟩ :=
    hper T hT₁
  obtain ⟨hkcd, hkc, hks, hw1, hw2, hw1', hw2'⟩ :=
    htw T hTw (k : ℤ) (l : ℤ)
  set kf : ℝ → ℂ := kfun (Pf T) T k l
  set a : ℝ := (Pf T).tau T k
  set b : ℝ := (Pf T).tau T l
  have ha : T ≤ a := (hGB.tau_mem (Pf T) T hL0 hT0 k).1
  have hb : T ≤ b := (hGB.tau_mem (Pf T) T hL0 hT0 l).1
  have hτs : (Pf T).tauStar T k l = (a + b) / 2 := rfl
  set Λs : ℂ := Lstar ((a + b) / 2)
  have hΛR : R₀ ≤ ‖Λs‖ := by
    have h1 := norm_Lstar_ge' (τ := (a + b) / 2) (by linarith)
    have h2 : Real.log T ≤ Real.log ((a + b) / 2) :=
      Real.log_le_log hT0 (by linarith)
    have h3 : 2 * (R₀ + 1) ≤ Real.log T := by
      have hlog := Real.log_le_log (Real.exp_pos _) hTR
      rwa [Real.log_exp] at hlog
    change R₀ ≤ ‖Lstar ((a + b) / 2)‖
    linarith
  have hΛR' : R₀ ≤ ‖conj Λs‖ := by rwa [Complex.norm_conj]
  set cJ : ℕ → ℂ := xiCoeffJ' Λs
  obtain ⟨hcs, hC1⟩ := hco Λs hΛR
  obtain ⟨-, hC1c⟩ := hco (conj Λs) hΛR'
  have hcJconj : (fun N => conj (cJ N)) = xiCoeffJ' (conj Λs) := by
    funext N
    rw [show cJ N = xiCoeffJ' Λs N by rfl, hconj]
  have hC1' : ∀ t : ℝ,
      LSeries (fun N => conj (cJ N)) (((5 / 4 : ℝ) : ℂ) + t * I) =
        Dfro (conj Λs) t := by
    intro t
    rw [hcJconj]
    exact hC1c t
  set W : ℝ := Cw * (Pf T).X T ^ (3 / 4 : ℝ) * (Pf T).L T ^ 2
  set W' : ℝ := Cw * (Pf T).X T ^ (3 / 4 : ℝ) * (Pf T).L T
  have hXpos : 0 ≤ (Pf T).X T ^ (3 / 4 : ℝ) :=
    Real.rpow_nonneg (by rw [hX]; exact (Real.exp_pos _).le) _
  have hW0 : 0 ≤ W := by
    change 0 ≤ Cw * (Pf T).X T ^ (3 / 4 : ℝ) * (Pf T).L T ^ 2
    positivity
  have hW'0 : 0 ≤ W' := by
    change 0 ≤ Cw * (Pf T).X T ^ (3 / 4 : ℝ) * (Pf T).L T
    positivity
  have hJk := hJ hkcd hkc (T := T) (a := a) (b := b)
    (W := W) (W' := W') hTJ ha hb hW0 hW'0
    hw1 hw2 hw1' hw2' hcs hC1 hC1'
  obtain ⟨hsumρ, hlit⟩ := xiPrime_EF_lit_corr' hkcd hkc
  have hgam : ∀ ρ : ℂ, paperFT kf (gammaOf ρ) = Hfn kf ρ := fun _ => rfl
  simp_rw [hgam] at hsumρ hlit
  have hGz : Z.Gz (Pf T) T k l =
      Zeta23.EF.literatureRHS kf + Jcorr kf := by
    rw [hGB.gz_tsum Z hZ hm (Pf T) T hφC2 hsupp k l]
    exact hlit
  have hlitG : Zeta23.EF.literatureRHS kf =
      (((Pf T).Gentry T k l : ℝ) : ℂ) :=
    hGB.lit_eq_Gentry (Pf T) T hφC2 hsupp hL0 k l
  have hFk := Zeta23.EF.integrable_fourier_of_contDiff_two hkcd hkc
  have hS :
      (∑' N : ℕ, cJ N / ((Real.sqrt N : ℝ) : ℂ) * kf (Real.log N)) +
        (∑' N : ℕ, conj (cJ N) / ((Real.sqrt N : ℝ) : ℂ) *
          kf (-Real.log N)) =
        ∫ τ : ℝ, paperFT kf τ * ((Pc ((Pf T).X T) cJ τ : ℝ) : ℂ) := by
    have hsOne := summable_coeff_mul_k hks cJ true
    have hsTwo := summable_coeff_mul_k hks (fun N => conj (cJ N)) false
    simp only [ite_true] at hsOne
    simp only [Bool.false_eq_true, ite_false] at hsTwo
    rw [← Summable.tsum_add hsOne hsTwo, hX,
      ← prime_term_complex hkcd.continuous hks hFk cJ]
    refine tsum_congr fun N => ?_
    ring
  have hnuc : ∀ τ : ℝ,
      nuc ((Pf T).X T) (xiCoeff (Lstar ((Pf T).tauStar T k l))) τ =
        nuX ((Pf T).X T) τ + Pc ((Pf T).X T) cJ τ := by
    intro τ
    rw [hτs, nuc_xiCoeff_eq']
    rfl
  have hintPc : Integrable (fun τ : ℝ =>
      paperFT kf τ * ((Pc ((Pf T).X T) cJ τ : ℝ) : ℂ)) := by
    rw [hX]
    exact integrable_paperFT_mul_Pc ((Pf T).L T) hFk cJ
  have hG1 :=
    hGB.Gentry1_eq (Pf T) T hφC2 hsupp hL0 k l cJ hnuc hintPc
  have hdiff :
      Z.Gz (Pf T) T k l - (((Pf T).Gentry1 T k l : ℝ) : ℂ) =
        Jcorr kf -
          ((∑' N : ℕ, cJ N / ((Real.sqrt N : ℝ) : ℂ) * kf (Real.log N)) +
            ∑' N : ℕ, conj (cJ N) / ((Real.sqrt N : ℝ) : ℂ) *
              kf (-Real.log N)) := by
    rw [hGz, hlitG, hG1, hS]
    ring
  refine ⟨hGB.summable_of Z hZ hm (Pf T) T hφC2 hsupp k l hsumρ, ?_⟩
  rw [hdiff]
  refine hJk.trans ?_
  obtain ⟨habOne, habTwo⟩ := habs T hTa
  have hlogT : 0 < Real.log T := Real.log_pos (by linarith)
  have hXL :
      (Pf T).X T ^ (3 / 4 : ℝ) * (Pf T).L T ^ 2 ≤
        T ^ (3 * lam / 4) * (Real.log T ^ 2 * lam ^ 2) := by
    have hLsquared : (Pf T).L T ^ 2 ≤ (lam * Real.log T) ^ 2 :=
      pow_le_pow_left₀ hL0.le hLlog 2
    calc
      (Pf T).X T ^ (3 / 4 : ℝ) * (Pf T).L T ^ 2 ≤
          T ^ (3 * lam / 4) * (lam * Real.log T) ^ 2 :=
        mul_le_mul hX34 hLsquared (sq_nonneg _) (Real.rpow_nonneg hT0.le _)
      _ = T ^ (3 * lam / 4) * (Real.log T ^ 2 * lam ^ 2) := by ring
  have hWW : W + W' ≤
      2 * Cw * (T ^ (3 * lam / 4) * (Real.log T ^ 2 * lam ^ 2)) := by
    have hLL : (Pf T).L T ≤ (Pf T).L T ^ 2 := by nlinarith [hL1]
    have heq : W + W' =
        Cw * (Pf T).X T ^ (3 / 4 : ℝ) *
          ((Pf T).L T ^ 2 + (Pf T).L T) := by
      change
        Cw * (Pf T).X T ^ (3 / 4 : ℝ) * (Pf T).L T ^ 2 +
          Cw * (Pf T).X T ^ (3 / 4 : ℝ) * (Pf T).L T = _
      ring
    rw [heq]
    calc
      Cw * (Pf T).X T ^ (3 / 4 : ℝ) *
          ((Pf T).L T ^ 2 + (Pf T).L T) ≤
          Cw * (Pf T).X T ^ (3 / 4 : ℝ) *
            (2 * (Pf T).L T ^ 2) :=
        mul_le_mul_of_nonneg_left (by linarith) (mul_nonneg hCw0 hXpos)
      _ = 2 * Cw *
          ((Pf T).X T ^ (3 / 4 : ℝ) * (Pf T).L T ^ 2) := by ring
      _ ≤ 2 * Cw *
          (T ^ (3 * lam / 4) * (Real.log T ^ 2 * lam ^ 2)) :=
        mul_le_mul_of_nonneg_left hXL (by positivity)
  have hDenom : 0 < 4 + (a - b) ^ 2 := by positivity
  have hmax : 0 < max 1 ((a - b) ^ 2) :=
    lt_of_lt_of_le one_pos (le_max_left _ _)
  have hOne :
      (W + W') / (T * Real.log T) / (4 + (a - b) ^ 2) ≤
        2 * Cw * Ca * T ^ (-δ) *
          (1 / max 1 ((a - b) ^ 2)) := by
    have hbase : (W + W') / (T * Real.log T) ≤
        2 * Cw * Ca * T ^ (-δ) := by
      calc
        (W + W') / (T * Real.log T) ≤
            2 * Cw *
              (T ^ (3 * lam / 4) * (Real.log T ^ 2 * lam ^ 2)) /
                (T * Real.log T) :=
          div_le_div_of_nonneg_right hWW (by positivity)
        _ = 2 * Cw *
            (T ^ (3 * lam / 4) * Real.log T ^ 2 * lam ^ 2 /
              (T * Real.log T)) := by ring
        _ ≤ 2 * Cw *
            (Ca * T ^ (-((1 - 3 * lam / 4) / 2))) :=
          mul_le_mul_of_nonneg_left habOne (by positivity)
        _ = 2 * Cw * Ca * T ^ (-δ) := by rw [hδ]; ring
    have hrecip : 1 / (4 + (a - b) ^ 2) ≤
        1 / max 1 ((a - b) ^ 2) :=
      div_le_div_of_nonneg_left zero_le_one hmax (max_one_le_four_add _)
    calc
      (W + W') / (T * Real.log T) / (4 + (a - b) ^ 2) =
          (W + W') / (T * Real.log T) *
            (1 / (4 + (a - b) ^ 2)) := by ring
      _ ≤ 2 * Cw * Ca * T ^ (-δ) *
          (1 / max 1 ((a - b) ^ 2)) :=
        mul_le_mul hbase hrecip (by positivity) (by positivity)
  have hTwo : W / T ^ 2 ≤ Cw * Ca * T ^ (-δ) * (1 / T) := by
    have hWle : W ≤
        Cw * (T ^ (3 * lam / 4) * (Real.log T ^ 2 * lam ^ 2)) := by
      change Cw * (Pf T).X T ^ (3 / 4 : ℝ) * (Pf T).L T ^ 2 ≤ _
      rw [show Cw * (Pf T).X T ^ (3 / 4 : ℝ) * (Pf T).L T ^ 2 =
        Cw * ((Pf T).X T ^ (3 / 4 : ℝ) * (Pf T).L T ^ 2) by ring]
      exact mul_le_mul_of_nonneg_left hXL hCw0
    calc
      W / T ^ 2 ≤
          Cw * (T ^ (3 * lam / 4) *
            (Real.log T ^ 2 * lam ^ 2)) / T ^ 2 :=
        div_le_div_of_nonneg_right hWle (by positivity)
      _ = Cw *
          (T ^ (3 * lam / 4) * Real.log T ^ 2 * lam ^ 2 / T ^ 2) := by
        ring
      _ ≤ Cw *
          (Ca * T ^ (-((1 - 3 * lam / 4) / 2)) / T) :=
        mul_le_mul_of_nonneg_left habTwo hCw0
      _ = Cw * Ca * T ^ (-δ) * (1 / T) := by rw [hδ]; ring
  calc
    K * ((W + W') / (T * Real.log T) / (4 + (a - b) ^ 2) + W / T ^ 2) ≤
        K * (2 * Cw * Ca * T ^ (-δ) *
          (1 / max 1 ((a - b) ^ 2)) +
          Cw * Ca * T ^ (-δ) * (1 / T)) :=
      mul_le_mul_of_nonneg_left (add_le_add hOne hTwo) hK0
    _ ≤ 2 * K * Cw * Ca * T ^ (-δ) *
        (1 / max 1 ((a - b) ^ 2) + 1 / T) := by
      have hnonneg : 0 ≤ K * Cw * Ca * T ^ (-δ) * (1 / T) := by positivity
      have heq :
          2 * K * Cw * Ca * T ^ (-δ) *
              (1 / max 1 ((a - b) ^ 2) + 1 / T) =
            K * (2 * Cw * Ca * T ^ (-δ) *
                (1 / max 1 ((a - b) ^ 2)) +
              Cw * Ca * T ^ (-δ) * (1 / T)) +
              K * Cw * Ca * T ^ (-δ) * (1 / T) := by ring
      rw [heq]
      linarith

end XiPrime
end Zeta23
