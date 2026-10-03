import TaoTrudgianYang2025.JutilaWindowBound
import TaoTrudgianYang2025.ExponentPairLargeValues
import TaoTrudgianYang2025.ZeroDensityTransferCorollaries
import TaoTrudgianYang2025.ZetaTwelfthMoment
import TaoTrudgianYang2025.BourgainOptimizedTransfer
import TaoTrudgianYang2025.ZetaPairNonexistence
import TaoTrudgianYang2025.HeathBrownDerivative
import TaoTrudgianYang2025.BourgainRetainedPullback
import TaoTrudgianYang2025.BourgainMixedFamily
import TaoTrudgianYang2025.BourgainMixedUpper
import TaoTrudgianYang2025.BourgainPhysicalUpper
import TaoTrudgianYang2025.BourgainSliceSelection
import TaoTrudgianYang2025.BourgainBudgetLogarithm
import TaoTrudgianYang2025.BourgainLogPacking
import TaoTrudgianYang2025.ZetaTwelfthGlobal
import TaoTrudgianYang2025.BourgainSubdivisionScale
import TaoTrudgianYang2025.BourgainBandLogBounds
import TaoTrudgianYang2025.BourgainRegionRealization
import TaoTrudgianYang2025.ClassicalLargeValueRegions
import TaoTrudgianYang2025.LargeValueExponentAttainment
import TaoTrudgianYang2025.CDVMixedDensity
import TaoTrudgianYang2025.BourgainImprovedDensity
import TaoTrudgianYang2025.RobertSargosExponentPair
import TaoTrudgianYang2025.HeathBrownExponentPairs

/-!
# Proved consumers for the literature density table

The five Ivic-form bounds retain the genuine five-quarter term of the
already proved smoothed powered-Gram estimate. Their uniform constants
precede the actual patterns, and all physical scale and loss conditions
are discharged before the existing zero-density transfer is applied.

The critical-line endpoint extends the native Jensen argument to
Re(s) >= 49/100 inside the SAME pole-safe disks; the fixed shift 1/100
then supplies the paper's shifted, multiplicity-weighted convention.
The canonical Guth--Maynard foundation is unchanged.

The Pintz consumers prove the first row with its closed lower endpoint,
the next two rows on strict lower interiors, and every integer-indexed
tail cell on its strict lower interior (including its upper endpoint).
They use the proved first/fourth new pairs and genuine Heath--Brown
derivative bounds on all sharp logarithmic intervals, followed by actual
Gram-cardinality and zero-density transfer. The other printed closed
lower endpoints are NOT claimed. No source-contract repair is made here.

The Bourgain literature row now follows from the actual localized retained
Gram recurrence, a common weighted amplitude band, the existing mixed
Heath--Brown estimate, and the critical-line twelfth moment. All physical
losses are discharged before the zero-loss limit and density transfer.
No off-critical eighth moment or density conclusion is assumed.

These are identified table inputs, not a claim to the entire literature
envelope. The remaining Pintz lower endpoints and envelope stay open.
-/

noncomputable section
open Complex Finset Filter MeromorphicOn Topology
open RiemannZeta.GuthMaynard
open scoped ArithmeticFunction.Moebius BigOperators
namespace TaoTrudgianYang2025

private theorem quarter_moment_card_le (k Q : ℕ) (T D V H : ℝ) (W : Finset ℝ)
    (hV : 0 < V) (hH : 0 < H)
    (hdiag : 4*D*(Q:ℝ)^k ≤ V^(4*k))
    (hmain : 4*D*T^k ≤ H*V^(4*k))
    (hmixed : 4*D*T^(1/2:ℝ)*(Q:ℝ)^k ≤ H^(3/4:ℝ)*V^(4*k))
    (hrec : (W.card:ℝ)^2*V^(4*k) ≤ D*jutilaMomentCore k Q T W) :
    (W.card:ℝ) ≤ H := by
  by_contra hnot
  have hRH : H < (W.card:ℝ) := lt_of_not_ge hnot
  have hR : 0 < (W.card:ℝ) := hH.trans hRH
  have hVpow : 0 < V^(4*k) := pow_pos hV _
  have hpower : (W.card:ℝ)^(5/4:ℝ)*H^(3/4:ℝ) ≤ (W.card:ℝ)^2 := by
    calc
      _ ≤ (W.card:ℝ)^(5/4:ℝ)*(W.card:ℝ)^(3/4:ℝ) := by
        gcongr
      _ = _ := by rw [← Real.rpow_add hR]; norm_num
  have hd := mul_le_mul_of_nonneg_left hdiag (sq_nonneg (W.card:ℝ))
  have hm := mul_le_mul_of_nonneg_left hmain hR.le
  have hmainR : 4*D*(W.card:ℝ)*T^k ≤ (W.card:ℝ)^2*V^(4*k) := by
    have hh := mul_le_mul_of_nonneg_right hRH.le
      (mul_nonneg hR.le hVpow.le)
    nlinarith only [hm,hh]
  have hmixR : 4*D*(W.card:ℝ)^(5/4:ℝ)*T^(1/2:ℝ)*(Q:ℝ)^k ≤
      (W.card:ℝ)^2*V^(4*k) := by
    have hh := mul_le_mul_of_nonneg_left hmixed
      (Real.rpow_nonneg hR.le (5/4:ℝ))
    have hh' := mul_le_mul_of_nonneg_right hpower hVpow.le
    nlinarith only [hh,hh']
  unfold jutilaMomentCore at hrec
  have hpositive : 0 < (W.card:ℝ)^2*V^(4*k) := mul_pos (sq_pos_of_pos hR) hVpow
  nlinarith only [hd,hmainR,hmixR,hrec,hpositive]

private theorem local_loss_parameters (k : ℕ) (hk : 0 < k) {σ τ ε : ℝ}
    (hσ : 3/4 < σ) (hτ : 1 < τ) (hε : 0 < ε)
    (hfirst : (k:ℝ)*τ+2*k-4*k*σ ≤ 2-2*σ)
    (hsecond : 2*τ/3+4*k*(3-4*σ)/3 ≤ 2-2*σ) :
    ∃ δ ν : ℝ, 0 < δ ∧ 0 < ν ∧ δ ≤ 1 ∧ 1 ≤ τ-δ ∧
      0 ≤ σ-2*δ ∧
      ν*(τ+1)+3*k < 4*k*(σ-2*δ) ∧
      ν*(τ+1)+2*k+(τ+δ)*k < (2-2*σ+ε/2)+4*k*(σ-2*δ) ∧
      ν*(τ+1)+3*k+(τ+δ)/2 <
        (3/4)*(2-2*σ+ε/2)+4*k*(σ-2*δ) ∧
      2-2*(σ-2*δ) < 2-2*σ+ε/2 ∧
      ν*(τ+1)+(2-2*σ+ε/2) ≤ 2-2*σ+ε := by
  let g := σ-3/4
  let δ := min 1 (min ((τ-1)/2) (min (g/16) (ε/(100*(16*(k:ℝ)+1)))))
  let ν := min (ε/(100*(τ+1))) ((k:ℝ)*g/(τ+1))
  have hg : 0 < g := by dsimp [g]; linarith
  have hkp : (0:ℝ) < k := by exact_mod_cast hk
  have hd : 0 < δ := lt_min (by norm_num)
    (lt_min (by positivity) (lt_min (by positivity) (by positivity)))
  have hn : 0 < ν := lt_min (by positivity) (by positivity)
  have hd1 : δ ≤ 1 := min_le_left _ _
  have hdt : δ ≤ (τ-1)/2 := (min_le_right _ _).trans (min_le_left _ _)
  have hdg : δ ≤ g/16 := (min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_left _ _))
  have hde : δ ≤ ε/(100*(16*(k:ℝ)+1)) := (min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_right _ _))
  have hne : ν*(τ+1) ≤ ε/100 := by
    have hh := (le_div_iff₀ (by positivity : 0 < 100*(τ+1))).mp
      (show ν ≤ ε/(100*(τ+1)) from min_le_left _ _)
    nlinarith only [hh]
  have hng : ν*(τ+1) ≤ (k:ℝ)*g :=
    (le_div_iff₀ (by linarith : 0 < τ+1)).mp (min_le_right _ _)
  have hde' := (le_div_iff₀ (by positivity : 0 < 100*(16*(k:ℝ)+1))).mp hde
  have hkd := mul_le_mul_of_nonneg_left hdg hkp.le
  have hkg := mul_pos hkp hg
  have hkd0 := mul_nonneg hkp.le hd.le
  refine ⟨δ,ν,hd,hn,hd1,by linarith,?_,?_,?_,?_,?_,?_⟩
  · dsimp [g] at hdg
    linarith
  · dsimp [g] at hng hkd hkg
    nlinarith only [hng,hkd,hkg]
  · nlinarith only [hfirst,hne,hde',hε,hd,hkd0]
  · nlinarith only [hsecond,hne,hde',hε,hd,hkd0]
  · nlinarith only [hde',hε,hkd0]
  · linarith only [hne,hε]

theorem ivic_fiveQuarter_local_largeValueBound
    (k : ℕ) (hk : 0 < k) {σ τ : ℝ}
    (hσ : 3/4 < σ) (hτ : 1 < τ)
    (hfirst : (k:ℝ)*τ+2*k-4*k*σ ≤ 2-2*σ)
    (hsecond : 2*τ/3+4*k*(3-4*σ)/3 ≤ 2-2*σ) :
    IsLargeValueBound σ τ (2-2*σ) := by
  intro ε hε
  obtain ⟨δ,ν,hδ,hν,hδ1,hheight,hs,hgap0,hgap1,hgap2,hgap3,hloss⟩ :=
    local_loss_parameters k hk hσ hτ hε hfirst hsecond
  let s := σ-2*δ
  let r := 2-2*σ+ε/2
  let u := ν*(τ+1)
  obtain ⟨B,T₀,hB,hT₀,hsource⟩ := jutila_smoothed_pattern_bound
    (Classical.choice exists_gmSmoothCutoff) k hk hν
  let D₀ := B*(4:ℝ)^(2*k)*(3:ℝ)^(4*k)
  let A₀ := 4*D₀*(2:ℝ)^k
  have hD₀ : 0 < D₀ := by dsimp [D₀]; positivity
  obtain ⟨N₀,hN₀⟩ := eventually_atTop.mp
    (eventually_const_mul_rpow_le_rpow (D:=A₀) hgap0)
  obtain ⟨N₁,hN₁⟩ := eventually_atTop.mp
    (eventually_const_mul_rpow_le_rpow (D:=4*D₀) hgap1)
  obtain ⟨N₂,hN₂⟩ := eventually_atTop.mp
    (eventually_const_mul_rpow_le_rpow (D:=A₀) hgap2)
  obtain ⟨N₃,hN₃⟩ := eventually_atTop.mp
    (eventually_const_mul_rpow_le_rpow (D:=72) hgap3)
  obtain ⟨Nv,hNv⟩ := eventually_atTop.mp
    (eventually_rpow_add_one_le_rpow hs (by linarith : σ-2*δ < σ-δ))
  let C := max 30 (max T₀ (max N₀ (max N₁ (max N₂ (max N₃ (max Nv B))))))
  have h30 : (30:ℝ) ≤ C := le_max_left _ _
  have hC : 1 ≤ C := by linarith
  have hCT : T₀ ≤ C := (le_max_left _ _).trans (le_max_right _ _)
  have hC0 : N₀ ≤ C := (le_max_left _ _).trans
    ((le_max_right _ _).trans (le_max_right _ _))
  have hC1 : N₁ ≤ C := (le_max_left _ _).trans
    ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _)))
  have hC2 : N₂ ≤ C := (le_max_left _ _).trans
    ((le_max_right _ _).trans ((le_max_right _ _).trans
      ((le_max_right _ _).trans (le_max_right _ _))))
  have hC3 : N₃ ≤ C := (le_max_left _ _).trans
    ((le_max_right _ _).trans ((le_max_right _ _).trans
      ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _)))))
  have hCv : Nv ≤ C := (le_max_left _ _).trans
    ((le_max_right _ _).trans ((le_max_right _ _).trans
      ((le_max_right _ _).trans ((le_max_right _ _).trans
        ((le_max_right _ _).trans (le_max_right _ _))))))
  have hCB : B ≤ C := (le_max_right _ _).trans
    ((le_max_right _ _).trans ((le_max_right _ _).trans
      ((le_max_right _ _).trans ((le_max_right _ _).trans
        ((le_max_right _ _).trans (le_max_right _ _))))))
  refine ⟨C,hC,δ,hδ,?_⟩
  intro P hN hTl hTu hVl _
  have hNp : 0 < P.N := zero_lt_one.trans P.one_lt_N
  have hTp : 0 < P.T := P.T_pos
  have hN1 := P.one_lt_N.le
  have hNT : P.N ≤ P.T := by
    apply le_trans _ hTl
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le hN1 hheight
  have hscale : 30 ≤ P.scale := by
    have hh := h30.trans hN
    rw [P.N_eq_scale] at hh
    exact_mod_cast hh
  have hT : T₀ ≤ P.T := (hCT.trans hN).trans hNT
  have hV : P.N^s ≤ P.V-1 := by
    have hh := (hNv P.N (hCv.trans hN)).trans hVl
    dsimp [s]
    linarith
  have hVp : 0 < P.V-1 := (Real.rpow_pos_of_pos hNp s).trans_le hV
  have hTν : P.T^ν ≤ P.N^u := by
    calc
      _ ≤ (P.N^(τ+δ))^ν := Real.rpow_le_rpow P.T_pos.le hTu hν.le
      _ = P.N^((τ+δ)*ν) := (Real.rpow_mul hNp.le _ _).symm
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hN1 (by dsimp [u]; nlinarith)
  have hTk : P.T^k ≤ P.N^((τ+δ)*(k:ℝ)) := by
    have hh := pow_le_pow_left₀ P.T_pos.le hTu k
    rwa [← Real.rpow_mul_natCast hNp.le] at hh
  have hTh : P.T^(1/2:ℝ) ≤ P.N^((τ+δ)/2) := by
    have hh := Real.rpow_le_rpow P.T_pos.le hTu (by norm_num : (0:ℝ) ≤ 1/2)
    rw [← Real.rpow_mul hNp.le] at hh
    simpa only [mul_one_div] using hh
  obtain ⟨W,Q,_,hcard,_,_,hQ,_,_,hg⟩ :=
    hsource P hscale (by linarith) hT hNT
  have hQpow : (Q:ℝ)^k ≤ (2:ℝ)^k*P.N^k := by
    simpa only [mul_pow] using pow_le_pow_left₀ (Nat.cast_nonneg Q) hQ k
  have hW : (W.card:ℝ) ≤ P.N^r := by
    rcases hg with hsmall | hlarge
    · have hsmall' : (W.card:ℝ)*(P.V-1)^2 ≤ 18*(Q:ℝ)^2 := by
        rw [div_pow] at hsmall
        norm_num at hsmall
        nlinarith only [hsmall]
      have hq2 := pow_le_pow_left₀ (Nat.cast_nonneg Q) hQ 2
      calc
        _ ≤ 72*P.N^2/(P.V-1)^2 := by
          apply (le_div_iff₀ (sq_pos_of_pos hVp)).mpr
          nlinarith only [hsmall',hq2]
        _ ≤ 72*P.N^2/(P.N^s)^2 := by gcongr
        _ = 72*P.N^(2-2*s) := by
          rw [← Real.rpow_mul_natCast hNp.le,← Real.rpow_two,mul_div_assoc,
            ← Real.rpow_sub hNp]
          congr 2
          norm_num
          ring
        _ ≤ _ := hN₃ P.N (hC3.trans hN)
    · let D := B*P.T^ν*(4*P.N)^(2*k)*(3:ℝ)^(4*k)
      have hD : D ≤ D₀*P.N^(u+2*k) := by
        calc
          _ ≤ B*P.N^u*(4*P.N)^(2*k)*(3:ℝ)^(4*k) := by dsimp [D]; gcongr
          _ = _ := by
            rw [mul_pow,← Real.rpow_natCast P.N (2*k)]
            push_cast
            rw [Real.rpow_add hNp]
            dsimp [D₀]
            ring
      have hcore : 0 ≤ jutilaMomentCore k Q P.T W := by
        unfold jutilaMomentCore
        positivity
      have hlarge' : (W.card:ℝ)^2*((P.V-1)/3)^(4*k) ≤
          (B*P.T^ν*(4*P.N)^(2*k))*jutilaMomentCore k Q P.T W := by
        have hcoef : B*P.T^ν*(2*(Q:ℝ))^(2*k) ≤ B*P.T^ν*(4*P.N)^(2*k) :=
          mul_le_mul_of_nonneg_left
            (pow_le_pow_left₀ (by positivity) (by linarith only [hQ]) (2*k))
            (mul_nonneg hB.le (Real.rpow_nonneg hTp.le ν))
        exact hlarge.trans (mul_le_mul_of_nonneg_right hcoef hcore)
      have hrec : (W.card:ℝ)^2*(P.V-1)^(4*k) ≤
          D*jutilaMomentCore k Q P.T W := by
        have hh := (div_le_iff₀ (by positivity : (0:ℝ) < 3^(4*k))).mp
          (show (W.card:ℝ)^2*(P.V-1)^(4*k)/3^(4*k) ≤
            (B*P.T^ν*(4*P.N)^(2*k))*jutilaMomentCore k Q P.T W by
              simpa only [div_pow,mul_div_assoc] using hlarge')
        dsimp [D]
        nlinarith only [hh]
      have hv4 : P.N^(4*(k:ℝ)*s) ≤ (P.V-1)^(4*k) := by
        have hh := pow_le_pow_left₀ (Real.rpow_nonneg hNp.le s) hV (4*k)
        rw [← Real.rpow_mul_natCast hNp.le] at hh
        push_cast at hh
        simpa only [mul_assoc,mul_comm,mul_left_comm] using hh
      apply quarter_moment_card_le k Q P.T D (P.V-1) (P.N^r) W hVp
        (Real.rpow_pos_of_pos hNp r) ?_ ?_ ?_ hrec
      · calc
          _ ≤ 4*(D₀*P.N^(u+2*k))*((2:ℝ)^k*P.N^k) := by gcongr
          _ = A₀*P.N^(u+3*k) := by
            rw [← Real.rpow_natCast P.N k]
            dsimp [A₀]
            rw [show 4*(D₀*P.N^(u+2*k))*((2:ℝ)^k*P.N^(k:ℝ)) =
              (4*D₀*(2:ℝ)^k)*(P.N^(u+2*k)*P.N^(k:ℝ)) by ring,
              ← Real.rpow_add hNp]
            congr 2
            ring
          _ ≤ P.N^(4*(k:ℝ)*s) := hN₀ P.N (hC0.trans hN)
          _ ≤ _ := hv4
      · calc
          _ ≤ 4*(D₀*P.N^(u+2*k))*P.N^((τ+δ)*(k:ℝ)) := by gcongr
          _ = (4*D₀)*P.N^(u+2*k+(τ+δ)*k) := by
            rw [show 4*(D₀*P.N^(u+2*k))*P.N^((τ+δ)*(k:ℝ)) =
              (4*D₀)*(P.N^(u+2*k)*P.N^((τ+δ)*(k:ℝ))) by ring,
              ← Real.rpow_add hNp]
          _ ≤ P.N^(r+4*(k:ℝ)*s) := hN₁ P.N (hC1.trans hN)
          _ = P.N^r*P.N^(4*(k:ℝ)*s) := Real.rpow_add hNp _ _
          _ ≤ _ := mul_le_mul_of_nonneg_left hv4 (by positivity)
      · calc
          _ ≤ 4*(D₀*P.N^(u+2*k))*P.N^((τ+δ)/2)*((2:ℝ)^k*P.N^k) := by
            gcongr
          _ = A₀*P.N^(u+3*k+(τ+δ)/2) := by
            rw [← Real.rpow_natCast P.N k]
            dsimp [A₀]
            rw [show 4*(D₀*P.N^(u+2*k))*P.N^((τ+δ)/2)*((2:ℝ)^k*P.N^(k:ℝ)) =
              (4*D₀*(2:ℝ)^k)*(P.N^(u+2*k)*P.N^((τ+δ)/2)*P.N^(k:ℝ)) by ring,
              ← Real.rpow_add hNp,← Real.rpow_add hNp]
            congr 2
            ring
          _ ≤ P.N^((3/4)*r+4*(k:ℝ)*s) := hN₂ P.N (hC2.trans hN)
          _ = (P.N^r)^(3/4:ℝ)*P.N^(4*(k:ℝ)*s) := by
            rw [← Real.rpow_mul hNp.le,← Real.rpow_add hNp]
            congr 1
            ring
          _ ≤ _ := mul_le_mul_of_nonneg_left hv4 (by positivity)
  calc
    _ ≤ B*P.T^ν*(W.card:ℝ) := hcard
    _ ≤ B*P.N^u*P.N^r := by gcongr
    _ = B*P.N^(u+r) := by rw [mul_assoc,← Real.rpow_add hNp]
    _ ≤ C*P.N^((2-2*σ)+ε) :=
      mul_le_mul hCB (Real.rpow_le_rpow_of_exponent_le hN1 hloss)
        (by positivity) (zero_le_one.trans hC)

theorem zeroDensityExponent_le_ivic_of_cutoff (k : ℕ) (hk : 0 < k) {σ τ₀ : ℝ}
    (hσ : 3/4 < σ) (hσ₁ : σ < 1) (hlocal : 1 < τ₀+σ-1)
    (hfirst : (k:ℝ)*(τ₀+σ-1)+2*k-4*k*σ ≤ 2-2*σ)
    (hsecond : 2*(τ₀+σ-1)/3+4*k*(3-4*σ)/3 ≤ 2-2*σ)
    (hcut : τ₀ ≤ 3*(4*σ-1)/4) :
    zeroDensityExponent σ ≤ ((3/τ₀:ℝ):EReal) := by
  have hτ₀ : 0 < τ₀ := by linarith
  apply zeroDensityExponent_le_three_div_of_montgomery_range
    σ τ₀ (by linarith) hσ₁ hτ₀
  · intro τ ht
    apply (zetaLargeValueExponent_le_of_bound
      (zetaTwelfth_largeValueBound (by linarith : 1/2 ≤ σ) ht.1)).trans
    apply EReal.coe_le_coe_iff.mpr
    apply (le_div_iff₀ hτ₀).mpr
    have hc : 0 ≤ 2*τ₀-(3-3*σ) := by linarith
    have hh := mul_nonneg hc (show 0 ≤ 4*τ₀/3-τ by linarith [ht.2])
    have hg := mul_nonneg hτ₀.le (sub_nonneg.mpr hcut)
    nlinarith only [hh,hg]
  · intro τ ht
    exact largeValueExponent_le_of_bound
      ((ivic_fiveQuarter_local_largeValueBound k hk hσ hlocal hfirst hsecond).of_height_le ht.2)

theorem zeroDensityExponent_le_ivic_two {σ:ℝ} (hσ : 4/5 ≤ σ) (hσ₁ : σ < 1) :
    zeroDensityExponent σ ≤ ((3/(2*σ):ℝ):EReal) := by
  apply zeroDensityExponent_le_ivic_of_cutoff 2 (by omega) (by linarith) hσ₁
  · linarith
  · norm_num; linarith
  · norm_num; linarith
  · linarith

theorem zeroDensityExponent_le_ivic_three {σ:ℝ} (hσ : 41/53 ≤ σ) (hσ₁ : σ < 1) :
    zeroDensityExponent σ ≤ ((9/(7*σ-1):ℝ):EReal) := by
  have hh := zeroDensityExponent_le_ivic_of_cutoff 3 (by omega) (τ₀:=(7*σ-1)/3)
    (by linarith : 3/4 < σ) hσ₁ (by linarith)
    (by norm_num; linarith) (by norm_num; linarith) (by linarith)
  have hd : 7*σ-1 ≠ 0 := by linarith
  have he : (3:ℝ)/((7*σ-1)/3) = 9/(7*σ-1) := by field_simp; ring
  simpa only [he] using hh

theorem zeroDensityExponent_le_ivic_four {σ:ℝ} (hσ : 13/17 ≤ σ) (hσ₁ : σ < 1) :
    zeroDensityExponent σ ≤ ((6/(5*σ-1):ℝ):EReal) := by
  have hh := zeroDensityExponent_le_ivic_of_cutoff 4 (by omega) (τ₀:=(5*σ-1)/2)
    (by linarith : 3/4 < σ) hσ₁ (by linarith)
    (by norm_num; linarith) (by norm_num; linarith) (by linarith)
  have hd : 5*σ-1 ≠ 0 := by linarith
  have he : (3:ℝ)/((5*σ-1)/2) = 6/(5*σ-1) := by field_simp; ring
  simpa only [he] using hh

theorem zeroDensityExponent_le_ivic_five {σ:ℝ} (hσ : 127/167 ≤ σ) (hσ₁ : σ < 1) :
    zeroDensityExponent σ ≤ ((15/(13*σ-3):ℝ):EReal) := by
  have hh := zeroDensityExponent_le_ivic_of_cutoff 5 (by omega) (τ₀:=(13*σ-3)/5)
    (by linarith : 3/4 < σ) hσ₁ (by linarith)
    (by norm_num; linarith) (by norm_num; linarith) (by linarith)
  have hd : 13*σ-3 ≠ 0 := by linarith
  have he : (3:ℝ)/((13*σ-3)/5) = 15/(13*σ-3) := by field_simp; ring
  simpa only [he] using hh

theorem zeroDensityExponent_le_ivic_six {σ:ℝ} (hσ : 47/62 ≤ σ) (hσ₁ : σ < 1) :
    zeroDensityExponent σ ≤ ((9/(8*σ-2):ℝ):EReal) := by
  have hh := zeroDensityExponent_le_ivic_of_cutoff 6 (by omega) (τ₀:=(8*σ-2)/3)
    (by linarith : 3/4 < σ) hσ₁ (by linarith)
    (by norm_num; linarith) (by norm_num; linarith) (by linarith)
  have hd : 8*σ-2 ≠ 0 := by linarith
  have he : (3:ℝ)/((8*σ-2)/3) = 9/(8*σ-2) := by field_simp; ring
  simpa only [he] using hh

private theorem zeroUnitBin_multiplicity_le_jensen_left_margin (σ T : ℝ) (z : ℤ)
    (hσLower : 49 / 100 ≤ σ) (hT : 8 ≤ T) :
    ((∑ ρ ∈ zeroUnitBin σ T z,
        analyticVanishingOrder riemannZeta ρ : ℕ) : ℝ) ≤
      Real.log ((100 * T ^ (3 : ℝ)) / (0.6 : ℝ)) /
        Real.log ((7 / 4 : ℝ) / (8 / 5 : ℝ)) := by
  let S := zeroUnitBin σ T z
  by_cases hSEmpty : S = ∅
  · change ((∑ ρ ∈ S, analyticVanishingOrder riemannZeta ρ : ℕ) : ℝ) ≤ _
    rw [hSEmpty]
    simp only [Finset.sum_empty, Nat.cast_zero]
    have hLogDen : 0 < Real.log ((7 / 4 : ℝ) / (8 / 5 : ℝ)) := by
      apply Real.log_pos
      norm_num
    have hM : 1 ≤ 100 * T ^ (3 : ℝ) := by
      norm_num [Real.rpow_natCast]
      have hT2 : 1 ≤ T ^ (2 : ℕ) := by nlinarith
      calc
        1 ≤ 100 * T := by nlinarith
        _ ≤ 100 * T * T ^ (2 : ℕ) := by nlinarith
        _ = 100 * T ^ (3 : ℕ) := by ring
    have hRatio : 1 ≤ (100 * T ^ (3 : ℝ)) / (0.6 : ℝ) := by
      norm_num at hM ⊢
      nlinarith
    exact div_nonneg (Real.log_nonneg hRatio) hLogDen.le
  · have hSNonempty : S.Nonempty := Finset.nonempty_iff_ne_empty.mpr hSEmpty
    obtain ⟨ρ₀, hρ₀⟩ := hSNonempty
    have hρ₀Data := Finset.mem_filter.mp hρ₀
    have hρ₀Rect : ρ₀ ∈ zerosInRect σ 1 T (2 * T) := hρ₀Data.1
    rw [zerosInRect, Set.Finite.mem_toFinset, Set.mem_inter_iff,
      mem_ZeroRectangle] at hρ₀Rect
    have hzRange : (z : ℝ) ∈ Set.Icc (T - 1) (2 * T) := by
      constructor
      · linarith [hρ₀Rect.1.2.2.1, hρ₀Data.2.2]
      · linarith [hρ₀Rect.1.2.2.2, hρ₀Data.2.1]
    let c : ℂ := 2 + I * (((z : ℝ) + 1 / 2 : ℝ) : ℂ)
    let U : Set ℂ := Metric.closedBall c (7 / 4 : ℝ)
    have hUAnalytic : AnalyticOnNhd ℂ riemannZeta U := by
      apply analyticOn_riemannZeta.mono
      intro w hw
      have hwNorm : ‖w - c‖ ≤ 7 / 4 := by
        simpa [U, Metric.mem_closedBall, dist_eq_norm] using hw
      have hwImDiff : |w.im - ((z : ℝ) + 1 / 2)| ≤ 7 / 4 := by
        calc
          |w.im - ((z : ℝ) + 1 / 2)| = |(w - c).im| := by simp [c]
          _ ≤ ‖w - c‖ := abs_im_le_norm _
          _ ≤ 7 / 4 := hwNorm
      have hwIm : 1 < w.im := by
        have := (abs_le.mp hwImDiff).1
        linarith [hzRange.1]
      intro hwOne
      subst w
      norm_num at hwIm
    have hcLower : (0.6 : ℝ) ≤ ‖riemannZeta c‖ := by
      simpa [c] using euler_product_lower_bound_2 (z : ℝ)
    have hcNe : riemannZeta c ≠ 0 := by
      intro hcZero
      rw [hcZero, norm_zero] at hcLower
      norm_num at hcLower
    have hcOrder : analyticOrderAt riemannZeta c ≠ ⊤ := by
      rw [analyticOrderAt_eq_zero.mpr (Or.inr hcNe)]
      exact ENat.coe_ne_top 0
    have hSU : ∀ ρ ∈ S, ρ ∈ Metric.closedBall c (8 / 5 : ℝ) := by
      intro ρ hρ
      have hρData := Finset.mem_filter.mp hρ
      have hρRect : ρ ∈ zerosInRect σ 1 T (2 * T) := hρData.1
      rw [zerosInRect, Set.Finite.mem_toFinset, Set.mem_inter_iff,
        mem_ZeroRectangle] at hρRect
      rw [Metric.mem_closedBall, dist_eq_norm]
      have hreLower : -(151 / 100 : ℝ) ≤ (ρ - c).re := by
        norm_num [c]
        linarith [hσLower, hρRect.1.1]
      have hreUpper : (ρ - c).re ≤ -1 := by
        norm_num [c]
        linarith [hρRect.1.2.1]
      have himLower : -(1 / 2 : ℝ) ≤ (ρ - c).im := by
        norm_num [c]
        linarith [hρData.2.1]
      have himUpper : (ρ - c).im ≤ 1 / 2 := by
        norm_num [c]
        linarith [hρData.2.2]
      rw [mul_self_le_mul_self_iff (norm_nonneg _) (by norm_num)]
      rw [Complex.norm_mul_self_eq_normSq, normSq_apply]
      nlinarith [sq_nonneg ((ρ - c).re + 151 / 100),
        sq_nonneg ((ρ - c).im + 1 / 2),
        sq_nonneg ((ρ - c).im - 1 / 2)]
    let V : Set ℂ := Metric.closedBall c (8 / 5 : ℝ)
    have hVAnalytic : AnalyticOnNhd ℂ riemannZeta V :=
      hUAnalytic.mono
        (Metric.closedBall_subset_closedBall (by norm_num : (8 / 5 : ℝ) ≤ 7 / 4))
    have hBridge := finset_analyticVanishingOrder_le_finsum_divisor hVAnalytic
      (isCompact_closedBall c (8 / 5 : ℝ))
      (convex_closedBall c (8 / 5 : ℝ)).isPreconnected (by
        simp only [V, Metric.mem_closedBall, dist_self]
        norm_num) hcOrder S
      (by simpa [V] using hSU)
    have hM : 1 ≤ 100 * T ^ (3 : ℝ) := by
      norm_num [Real.rpow_natCast]
      have hT2 : 1 ≤ T ^ (2 : ℕ) := by nlinarith
      calc
        1 ≤ 100 * T := by nlinarith
        _ ≤ 100 * T * T ^ (2 : ℕ) := by nlinarith
        _ = 100 * T ^ (3 : ℕ) := by ring
    have hUAnalyticAbs : AnalyticOnNhd ℂ riemannZeta
        (Metric.closedBall c |(7 / 4 : ℝ)|) := by
      simpa [U, abs_of_pos (by norm_num : (0 : ℝ) < 7 / 4)] using hUAnalytic
    have hJensen := hUAnalyticAbs.sum_divisor_le
      (r := (8 / 5 : ℝ)) (R := (7 / 4 : ℝ))
      (M := 100 * T ^ (3 : ℝ)) (by norm_num) (by norm_num) hM hcNe (by
        intro w hw
        exact zeta_jensen_sphere_bound T (z : ℝ) hT hzRange w (by
          simpa [c, abs_of_pos (by norm_num : (0 : ℝ) < 7 / 4)] using hw))
    rw [abs_of_pos (by norm_num : (0 : ℝ) < 8 / 5)] at hJensen
    change ((∑ ρ ∈ S, analyticVanishingOrder riemannZeta ρ : ℕ) : ℝ) ≤ _
    refine hBridge.trans (le_trans (by simpa [c, V] using hJensen) ?_)
    have hLogDen : 0 < Real.log ((7 / 4 : ℝ) / (8 / 5 : ℝ)) := by
      apply Real.log_pos
      norm_num
    apply div_le_div_of_nonneg_right _ hLogDen.le
    have hMPos : 0 < 100 * T ^ (3 : ℕ) := by positivity
    have hcNormPos : 0 < ‖riemannZeta c‖ := norm_pos_iff.mpr hcNe
    have hRatioLe : (100 * T ^ (3 : ℕ)) / ‖riemannZeta c‖ ≤
        (100 * T ^ (3 : ℕ)) / (0.6 : ℝ) :=
      div_le_div_of_nonneg_left hMPos.le (by norm_num) hcLower
    exact Real.log_le_log
      (div_pos hMPos (by simpa [c] using hcNormPos)) (by simpa [c] using hRatioLe)

private theorem zeroCountRect_dyadic_le_jensen_left_margin (σ T : ℝ)
    (hσLower : 49 / 100 ≤ σ) (hT : 8 ≤ T) :
    (zeroCountRect σ 1 T (2 * T) : ℝ) ≤
      (T + 2) *
        (Real.log ((100 * T ^ (3 : ℝ)) / (0.6 : ℝ)) /
          Real.log ((7 / 4 : ℝ) / (8 / 5 : ℝ))) := by
  let S := zerosInRect σ 1 T (2 * T)
  let bins : Finset ℤ := Finset.Icc ⌊T⌋ ⌊2 * T⌋
  let floorIm : ℂ → ℤ := fun ρ => ⌊ρ.im⌋
  let mult : ℂ → ℕ := fun ρ => analyticVanishingOrder riemannZeta ρ
  have hFloorMem : ∀ ρ ∈ S, floorIm ρ ∈ bins := by
    intro ρ hρ
    change ρ ∈ zerosInRect σ 1 T (2 * T) at hρ
    rw [zerosInRect, Set.Finite.mem_toFinset, Set.mem_inter_iff,
      mem_ZeroRectangle] at hρ
    change floorIm ρ ∈ Finset.Icc ⌊T⌋ ⌊2 * T⌋
    rw [Finset.mem_Icc]
    exact ⟨Int.floor_mono hρ.1.2.2.1, Int.floor_mono hρ.1.2.2.2⟩
  have hAll : S.filter (fun ρ => floorIm ρ ∈ bins) = S :=
    Finset.filter_eq_self.mpr hFloorMem
  have hFiber := Finset.sum_fiberwise_eq_sum_filter S bins floorIm mult
  rw [hAll] at hFiber
  have hEach : ∀ z ∈ bins,
      ((∑ ρ ∈ S.filter (fun w => floorIm w = z), mult ρ : ℕ) : ℝ) ≤
        Real.log ((100 * T ^ (3 : ℝ)) / (0.6 : ℝ)) /
          Real.log ((7 / 4 : ℝ) / (8 / 5 : ℝ)) := by
    intro z _hz
    have hSubset : S.filter (fun w => floorIm w = z) ⊆ zeroUnitBin σ T z := by
      intro ρ hρ
      rw [Finset.mem_filter] at hρ
      rw [zeroUnitBin, Finset.mem_filter]
      refine ⟨by simpa [S] using hρ.1, ?_⟩
      have hFloorLe : ((⌊ρ.im⌋ : ℤ) : ℝ) ≤ ρ.im := Int.floor_le ρ.im
      have hLtFloor : ρ.im < ((⌊ρ.im⌋ : ℤ) : ℝ) + 1 := Int.lt_floor_add_one ρ.im
      change (z : ℝ) ≤ ρ.im ∧ ρ.im < (z : ℝ) + 1
      simpa [floorIm, hρ.2] using And.intro hFloorLe hLtFloor
    have hNat :
        ∑ ρ ∈ S.filter (fun w => floorIm w = z), mult ρ ≤
          ∑ ρ ∈ zeroUnitBin σ T z, mult ρ := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hSubset
      intro _ _ _
      exact Nat.zero_le _
    have hNatReal :
        ((∑ ρ ∈ S.filter (fun w => floorIm w = z), mult ρ : ℕ) : ℝ) ≤
          ((∑ ρ ∈ zeroUnitBin σ T z, mult ρ : ℕ) : ℝ) := by
      exact_mod_cast hNat
    exact hNatReal.trans (by
      simpa [mult] using zeroUnitBin_multiplicity_le_jensen_left_margin σ T z hσLower hT)
  have hSum :
      ∑ z ∈ bins,
          ((∑ ρ ∈ S.filter (fun w => floorIm w = z), mult ρ : ℕ) : ℝ) ≤
        ∑ _z ∈ bins,
          Real.log ((100 * T ^ (3 : ℝ)) / (0.6 : ℝ)) /
            Real.log ((7 / 4 : ℝ) / (8 / 5 : ℝ)) := by
    exact Finset.sum_le_sum hEach
  have hFiberReal := congrArg (fun n : ℕ => (n : ℝ)) hFiber
  simp only [Nat.cast_sum] at hFiberReal
  have hTotal : (zeroCountRect σ 1 T (2 * T) : ℝ) ≤
      (bins.card : ℝ) *
        (Real.log ((100 * T ^ (3 : ℝ)) / (0.6 : ℝ)) /
          Real.log ((7 / 4 : ℝ) / (8 / 5 : ℝ))) := by
    rw [zeroCountRect]
    change ((∑ ρ ∈ S, mult ρ : ℕ) : ℝ) ≤ _
    calc
      ((∑ ρ ∈ S, mult ρ : ℕ) : ℝ) =
          ∑ ρ ∈ S, (mult ρ : ℝ) := by simp
      _ = ∑ z ∈ bins, ∑ ρ ∈ S.filter (fun w => floorIm w = z),
          (mult ρ : ℝ) := hFiberReal.symm
      _ ≤ ∑ _z ∈ bins,
          Real.log ((100 * T ^ (3 : ℝ)) / (0.6 : ℝ)) /
            Real.log ((7 / 4 : ℝ) / (8 / 5 : ℝ)) := by
        simpa only [Nat.cast_sum] using hSum
      _ = (bins.card : ℝ) *
          (Real.log ((100 * T ^ (3 : ℝ)) / (0.6 : ℝ)) /
            Real.log ((7 / 4 : ℝ) / (8 / 5 : ℝ))) := by simp
  have hab : ⌊T⌋ ≤ ⌊2 * T⌋ + 1 := by
    have hmono : ⌊T⌋ ≤ ⌊2 * T⌋ := Int.floor_mono (by linarith)
    omega
  have hCardInt : (bins.card : ℤ) = ⌊2 * T⌋ + 1 - ⌊T⌋ := by
    simpa [bins] using Int.card_Icc_of_le ⌊T⌋ ⌊2 * T⌋ hab
  have hCardReal : (bins.card : ℝ) =
      (⌊2 * T⌋ : ℝ) + 1 - (⌊T⌋ : ℝ) := by
    exact_mod_cast hCardInt
  have hCard : (bins.card : ℝ) ≤ T + 2 := by
    rw [hCardReal]
    have hUpper : (⌊2 * T⌋ : ℝ) ≤ 2 * T := Int.floor_le (2 * T)
    have hLower : T - 1 < (⌊T⌋ : ℝ) := Int.sub_one_lt_floor T
    linarith
  have hLogDen : 0 < Real.log ((7 / 4 : ℝ) / (8 / 5 : ℝ)) := by
    apply Real.log_pos
    norm_num
  have hM : 1 ≤ (100 * T ^ (3 : ℝ)) / (0.6 : ℝ) := by
    have hTPos : 0 < T := by linarith
    have : 1 ≤ 100 * T ^ (3 : ℝ) := by
      norm_num [Real.rpow_natCast]
      nlinarith [sq_nonneg T]
    norm_num at this ⊢
    nlinarith
  have hJNonneg : 0 ≤
      Real.log ((100 * T ^ (3 : ℝ)) / (0.6 : ℝ)) /
        Real.log ((7 / 4 : ℝ) / (8 / 5 : ℝ)) :=
    div_nonneg (Real.log_nonneg hM) hLogDen.le
  exact hTotal.trans (mul_le_mul_of_nonneg_right hCard hJNonneg)

private theorem dyadic_zero_count_epsilon_one_left_margin (σ : ℝ) (hσLower : 49 / 100 ≤ σ) :
    EpsilonPowerBound
      (fun T => (zeroCountRect σ 1 T (2 * T) : ℝ))
      (fun T => T ^ (1 : ℝ)) := by
  intro ε hε
  let D : ℝ := Real.log ((7 / 4 : ℝ) / (8 / 5 : ℝ))
  let C : ℝ := 125 / (D * ε)
  have hD : 0 < D := by
    dsimp [D]
    apply Real.log_pos
    norm_num
  have hC : 0 < C := div_pos (by norm_num) (mul_pos hD hε)
  apply Asymptotics.IsBigO.of_bound C
  filter_upwards [Filter.eventually_ge_atTop (max (Real.exp 2) 8)] with T hT
  have hTEight : 8 ≤ T := (le_max_right _ _).trans hT
  have hTExp : Real.exp 2 ≤ T := (le_max_left _ _).trans hT
  have hTPos : 0 < T := by linarith
  have hTNonneg : 0 ≤ T := hTPos.le
  have hLogTwo : 2 ≤ Real.log T := by
    have := Real.log_le_log (Real.exp_pos 2) hTExp
    simpa using this
  have hNumerator :
      Real.log ((100 * T ^ (3 : ℝ)) / (0.6 : ℝ)) ≤ 100 * Real.log T := by
    have hConst := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 500 / 3 by norm_num)
    calc
      Real.log ((100 * T ^ (3 : ℝ)) / (0.6 : ℝ)) =
          Real.log ((500 / 3 : ℝ) * T ^ (3 : ℝ)) := by
        congr 1
        ring
      _ = Real.log (500 / 3 : ℝ) + Real.log (T ^ (3 : ℝ)) := by
        rw [Real.log_mul (by norm_num) (Real.rpow_pos_of_pos hTPos 3).ne']
      _ = Real.log (500 / 3 : ℝ) + 3 * Real.log T := by
        rw [Real.log_rpow hTPos]
      _ ≤ 100 * Real.log T := by nlinarith
  have hJensenBound :
      Real.log ((100 * T ^ (3 : ℝ)) / (0.6 : ℝ)) / D ≤
        100 * Real.log T / D :=
    div_le_div_of_nonneg_right hNumerator hD.le
  have hLogPow : Real.log T ≤ T ^ ε / ε :=
    Real.log_le_rpow_div hTNonneg hε
  have hRaw := zeroCountRect_dyadic_le_jensen_left_margin σ T hσLower hTEight
  have hCount : (zeroCountRect σ 1 T (2 * T) : ℝ) ≤
      C * (T ^ ε * T) := by
    calc
      (zeroCountRect σ 1 T (2 * T) : ℝ) ≤
          (T + 2) *
            (Real.log ((100 * T ^ (3 : ℝ)) / (0.6 : ℝ)) / D) := by
        simpa [D] using hRaw
      _ ≤ (T + 2) * (100 * Real.log T / D) := by
        exact mul_le_mul_of_nonneg_left hJensenBound (by linarith)
      _ ≤ ((5 / 4 : ℝ) * T) * (100 * (T ^ ε / ε) / D) := by
        gcongr
        · linarith
      _ = C * (T ^ ε * T) := by
        dsimp [C]
        field_simp [hD.ne', hε.ne']
        ring
  calc
    ‖|(zeroCountRect σ 1 T (2 * T) : ℝ)|‖ =
        (zeroCountRect σ 1 T (2 * T) : ℝ) := by
      simp
    _ ≤ C * (T ^ ε * T) := hCount
    _ = C * ‖T ^ ε * |T ^ (1 : ℝ)|‖ := by
      rw [Real.rpow_one, abs_of_nonneg hTNonneg, Real.norm_eq_abs,
        abs_of_nonneg (mul_nonneg (Real.rpow_nonneg hTNonneg ε) hTNonneg)]

private theorem global_zero_count_epsilon_one_left_margin (σ : ℝ) (hσLower : 49 / 100 ≤ σ) :
    EpsilonPowerBound (fun T => (N σ T : ℝ)) (fun T => T ^ (1 : ℝ)) :=
  dyadicToGlobalZeroCount σ 1 (by norm_num) (dyadic_zero_count_epsilon_one_left_margin σ hσLower)

theorem ingham_isZeroDensityBound_at_half :
    IsZeroDensityBound (1/2) 2 := by
  apply isZeroDensityBound_of_shiftedEpsilonPowerBound (q:=fun _ => 1)
  intro ε hε
  refine ⟨1/100,by norm_num,?_,?_⟩
  · convert global_zero_count_epsilon_one_left_margin (49/100) le_rfl using 1
    norm_num [paperZeroCount_eq_localN]
  · norm_num
    linarith

theorem ingham_isZeroDensityBound_closed {σ:ℝ}
    (hσ : 1/2 ≤ σ) (hσ₁ : σ ≤ 1) :
    IsZeroDensityBound σ (3/(2-σ)) := by
  rcases hσ.eq_or_lt with rfl | hσ
  · convert ingham_isZeroDensityBound_at_half using 1
    norm_num
  · exact ingham_isZeroDensityBound hσ hσ₁

theorem zeroDensityExponent_le_ingham_closed {σ:ℝ}
    (hσ : 1/2 ≤ σ) (hσ₁ : σ ≤ 1) :
    zeroDensityExponent σ ≤ ((3/(2-σ):ℝ):EReal) :=
  zeroDensityExponent_le_of_bound (ingham_isZeroDensityBound_closed hσ hσ₁)

private theorem pintz_first_montgomery {σ τ : ℝ}
    (hσ : 23/24 ≤ σ) (hτ : 0 ≤ τ) (hτhi : τ ≤ 25*σ-21) :
    IsLargeValueBound σ τ (2-2*σ) := by
  apply exponentPair_taoTrudgianYang_firstNew.local_largeValueBound hτ
  linarith only [hσ,hτhi]

private theorem pintz_first_zeta {σ τ : ℝ}
    (hσ : 23/24 ≤ σ) (hτ : 2 ≤ τ) (hτhi : τ < 4*(24*σ-20)/3) :
    zetaLargeValueExponent σ τ = ⊥ := by
  apply exponentPair_taoTrudgianYang_fourthNew.zetaLargeValueExponent_eq_bot_of_one_le_tau
    (by linarith only [hσ]) (by linarith only [hτ])
  linarith only [hσ,hτhi]

theorem zeroDensityExponent_le_pintz_first {σ : ℝ} (hσ : 23/24 ≤ σ) (hσ1 : σ < 1) :
    zeroDensityExponent σ ≤ ((3/(24*σ-20):ℝ):EReal) := by
  apply zeroDensityExponent_le_three_div_of_montgomery_range σ (24*σ-20)
    (by linarith only [hσ]) hσ1 (by linarith only [hσ])
  · intro τ hτ
    rw [pintz_first_zeta hσ hτ.1 hτ.2]
    exact bot_le
  · intro τ hτ
    exact largeValueExponent_le_of_bound (pintz_first_montgomery hσ hτ.1 (by linarith only [hτ.2]))

private theorem pintz_heathBrown_logarithmic_sum_bound {k : ℕ} (hk : 3 ≤ k)
    {η : ℝ} (hη : 0 < η) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (t N : ℝ) (a b : ℕ),
      0 < t → 1 ≤ N → N ≤ (a : ℝ) → (b : ℝ) ≤ 2*N →
      ‖∑ n ∈ Finset.Icc a b, (n : ℂ)^(-((t : ℂ)*Complex.I))‖ ≤
        C*heathBrownPowerMajorant k η t N := by
  obtain ⟨δ,hδ,P,_hP,C,hC,hsource⟩ :=
    source_exponentialSum_heathBrown_bound hk (by norm_num : (0:ℝ) < 1) hη
  let p : ℝ := 2*Real.pi
  let d := heathBrownDerivativeExponent k
  let e := heathBrownInverseExponent k
  have hp : 1 ≤ p := by dsimp [p]; linarith only [Real.pi_gt_three]
  have hpp : 0 < p := zero_lt_one.trans_le hp
  have hd : 0 < d := (heathBrownDerivativeExponent_bounds hk).1
  have he : 0 < e := heathBrownInverseExponent_pos hk
  have hpone : 1 ≤ p^e := Real.one_le_rpow hp he.le
  refine ⟨C*p^e,one_le_mul_of_one_le_of_one_le hC hpone,?_⟩
  intro t N a b ht hN ha hb
  have hNp := zero_lt_one.trans_le hN
  by_cases hab : a ≤ b
  · have hsum := hsource Real.log (t/p) N a (b-a) (by positivity) hN ha
      (by simpa only [Nat.add_sub_of_le hab] using hb)
      (log_approximateModel P hδ.le)
    rw [Nat.add_sub_of_le hab] at hsum
    rw [norm_sum_cpow_neg_im_eq_logModel hNp a b ha t]
    change ‖Expdb.exponentialSumAt Real.log (t/p) N a b‖ ≤ _
    have hfirst : (t/p)^d ≤ p^e*t^d := by
      apply (Real.rpow_le_rpow (by positivity) (div_le_self ht.le hp) hd.le).trans
      exact le_mul_of_one_le_left (Real.rpow_nonneg ht.le _) hpone
    have hthird : (t/p)^(-e) = p^e*t^(-e) := by
      rw [Real.div_rpow ht.le hpp.le,Real.rpow_neg hpp.le,div_inv_eq_mul,mul_comm]
    have hmaj : heathBrownPowerMajorant k η (t/p) N ≤
        p^e*heathBrownPowerMajorant k η t N := by
      unfold heathBrownPowerMajorant
      change N^η*((t/p)^d*N^(1-(k:ℝ)*d)+N^(1-d)+N*(t/p)^(-e)) ≤
        p^e*(N^η*(t^d*N^(1-(k:ℝ)*d)+N^(1-d)+N*t^(-e)))
      rw [hthird]
      have h₁ := mul_le_mul_of_nonneg_right hfirst
        (Real.rpow_nonneg hNp.le (1-(k:ℝ)*d))
      have h₂ : N^(1-d) ≤ p^e*N^(1-d) :=
        le_mul_of_one_le_left (Real.rpow_nonneg hNp.le _) hpone
      have hinner : (t/p)^d*N^(1-(k:ℝ)*d)+N^(1-d)+N*(p^e*t^(-e)) ≤
          p^e*(t^d*N^(1-(k:ℝ)*d)+N^(1-d)+N*t^(-e)) := by
        nlinarith only [h₁,h₂]
      have hmul := mul_le_mul_of_nonneg_left hinner (Real.rpow_nonneg hNp.le η)
      nlinarith only [hmul]
    have hh := hsum.trans (mul_le_mul_of_nonneg_left hmaj (zero_le_one.trans hC))
    convert hh using 1
    ring
  · rw [Finset.Icc_eq_empty_of_lt (by omega : b < a),Finset.sum_empty,norm_zero]
    unfold heathBrownPowerMajorant
    positivity

private theorem pintz_heathBrown_window_majorant {k : ℕ} (hk : 3 ≤ k)
    {N t η τ δ B : ℝ} (hN : 1 ≤ N)
    (htlo : N^(τ-δ) ≤ t) (hthi : t ≤ N^(τ+δ))
    (hfirst : 1+(τ+δ-(k:ℝ))*heathBrownDerivativeExponent k ≤ B)
    (hsecond : 1-heathBrownDerivativeExponent k ≤ B)
    (hthird : 1-(τ-δ)*heathBrownInverseExponent k ≤ B) :
    heathBrownPowerMajorant k η t N ≤ 3*N^(η+B) := by
  have hNp := zero_lt_one.trans_le hN
  have htp := (Real.rpow_pos_of_pos hNp (τ-δ)).trans_le htlo
  let d := heathBrownDerivativeExponent k
  let e := heathBrownInverseExponent k
  have hd : 0 < d := (heathBrownDerivativeExponent_bounds hk).1
  have he : 0 < e := heathBrownInverseExponent_pos hk
  have h₁ : t^d*N^(1-(k:ℝ)*d) ≤ N^B := by
    calc
      _ ≤ (N^(τ+δ))^d*N^(1-(k:ℝ)*d) :=
        mul_le_mul_of_nonneg_right (Real.rpow_le_rpow htp.le hthi hd.le)
          (Real.rpow_nonneg hNp.le _)
      _ = N^(1+(τ+δ-(k:ℝ))*d) := by
        rw [← Real.rpow_mul hNp.le,← Real.rpow_add hNp]
        congr 1
        ring
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hN hfirst
  have h₂ : N^(1-d) ≤ N^B :=
    Real.rpow_le_rpow_of_exponent_le hN hsecond
  have h₃ : N*t^(-e) ≤ N^B := by
    calc
      _ ≤ N*(N^(τ-δ))^(-e) :=
        mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_nonpos (Real.rpow_pos_of_pos hNp _) htlo (by linarith)) hNp.le
      _ = N^(1-(τ-δ)*e) := by
        rw [← Real.rpow_mul hNp.le,
          show 1-(τ-δ)*e = 1+(τ-δ)*(-e) by ring,
          Real.rpow_add hNp,Real.rpow_one]
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hN hthird
  have hsum : t^d*N^(1-(k:ℝ)*d)+N^(1-d)+N*t^(-e) ≤ 3*N^B := by
    linarith only [h₁,h₂,h₃]
  have hh := mul_le_mul_of_nonneg_left hsum (Real.rpow_nonneg hNp.le η)
  unfold heathBrownPowerMajorant
  rw [Real.rpow_add hNp]
  dsimp only [d,e] at hh
  nlinarith only [hh]

private theorem pintz_heathBrown_zeta_nonexistence {k : ℕ} (hk : 3 ≤ k)
    {σ τ : ℝ}
    (hfirst : 1+(τ-(k:ℝ))*heathBrownDerivativeExponent k < σ)
    (hsecond : 1-heathBrownDerivativeExponent k < σ)
    (hthird : 1-τ*heathBrownInverseExponent k < σ) :
    zetaLargeValueExponent σ τ = ⊥ := by
  let d := heathBrownDerivativeExponent k
  let e := heathBrownInverseExponent k
  let g := min (σ-(1+(τ-(k:ℝ))*d))
    (min (σ-(1-d)) (σ-(1-τ*e)))
  have hd : 0 < d := (heathBrownDerivativeExponent_bounds hk).1
  have he : 0 < e := heathBrownInverseExponent_pos hk
  have hg : 0 < g := lt_min (sub_pos.mpr hfirst)
    (lt_min (sub_pos.mpr hsecond) (sub_pos.mpr hthird))
  have hg₁ : g ≤ σ-(1+(τ-(k:ℝ))*d) := min_le_left _ _
  have hg₂ : g ≤ σ-(1-d) := (min_le_right _ _).trans (min_le_left _ _)
  have hg₃ : g ≤ σ-(1-τ*e) := (min_le_right _ _).trans (min_le_right _ _)
  let η := g/8
  let δ := min (g/8) (g/(8*(d+e+1)))
  have hη : 0 < η := by dsimp [η]; positivity
  have hδ : 0 < δ := lt_min (by positivity) (by positivity)
  have hδg : δ ≤ g/8 := min_le_left _ _
  have hδde : δ*(d+e+1) ≤ g/8 := by
    have hh := (le_div_iff₀ (by positivity : 0 < 8*(d+e+1))).mp
      (show δ ≤ g/(8*(d+e+1)) from min_le_right _ _)
    nlinarith only [hh]
  have hδd : δ*d ≤ g/8 := by
    nlinarith only [hδde,mul_nonneg hδ.le he.le,hδ.le]
  have hδe : δ*e ≤ g/8 := by
    nlinarith only [hδde,mul_nonneg hδ.le hd.le,hδ.le]
  obtain ⟨C,hC,hbound⟩ := pintz_heathBrown_logarithmic_sum_bound hk hη
  have hev : ∀ᶠ N : ℝ in Filter.atTop, 3*C ≤ N^η :=
    (tendsto_rpow_atTop hη).eventually (Filter.eventually_ge_atTop _)
  obtain ⟨N₀,hN₀⟩ := Filter.eventually_atTop.mp hev
  apply zetaLargeValueExponent_eq_bot_of_pointwise_powerSaving
  refine ⟨max 2 N₀,δ,by have := le_max_left (2:ℝ) N₀; linarith,hδ,?_⟩
  intro N I t hNC hI hsub htlo hthi
  have hN2 : (2:ℝ) ≤ N := (le_max_left _ _).trans hNC
  have hN1 : (1:ℝ) < N := by linarith only [hN2]
  have hNp : (0:ℝ) < N := zero_lt_one.trans hN1
  have htp := (Real.rpow_pos_of_pos hNp (τ-δ)).trans_le htlo
  have hconstant := hN₀ (N:ℝ) ((le_max_right _ _).trans hNC)
  by_cases hempty : I = ∅
  · subst I
    simpa only [Finset.sum_empty,norm_zero] using
      Real.rpow_pos_of_pos hNp (σ-δ)
  obtain ⟨a,b,rfl⟩ := hI
  have hab : a ≤ b := Finset.nonempty_Icc.mp (Finset.nonempty_iff_ne_empty.mpr hempty)
  have ha : N ≤ a := (Finset.mem_Icc.mp (hsub (Finset.mem_Icc.mpr ⟨le_rfl,hab⟩))).1
  have hb : b ≤ 2*N := (Finset.mem_Icc.mp (hsub (Finset.mem_Icc.mpr ⟨hab,le_rfl⟩))).2
  have hsum := hbound t N a b htp hN1.le
    (by exact_mod_cast ha) (by exact_mod_cast hb)
  have hmajor := pintz_heathBrown_window_majorant (η:=η) (B:=σ-g/2) hk hN1.le htlo hthi
    (by change 1+(τ+δ-(k:ℝ))*d ≤ σ-g/2; nlinarith only [hg₁,hδd,hg.le])
    (by change 1-d ≤ σ-g/2; linarith only [hg₂,hg.le])
    (by change 1-(τ-δ)*e ≤ σ-g/2; nlinarith only [hg₃,hδe,hg.le])
  have hphase : (∑ n ∈ Finset.Icc a b, dirichletPhase n t) =
      ∑ n ∈ Finset.Icc a b, (n:ℂ)^(-((t:ℂ)*Complex.I)) := by
    apply Finset.sum_congr rfl
    intro n _
    simp only [dirichletPhase,mul_comm Complex.I (t:ℂ)]
    rfl
  rw [hphase]
  calc
    _ ≤ C*(3*(N:ℝ)^(η+(σ-g/2))) :=
      hsum.trans (mul_le_mul_of_nonneg_left hmajor (zero_le_one.trans hC))
    _ = (3*C)*(N:ℝ)^(η+(σ-g/2)) := by ring
    _ ≤ (N:ℝ)^η*(N:ℝ)^(η+(σ-g/2)) :=
      mul_le_mul_of_nonneg_right hconstant (Real.rpow_nonneg hNp.le _)
    _ = (N:ℝ)^(η+(η+(σ-g/2))) := (Real.rpow_add hNp _ _).symm
    _ < (N:ℝ)^(σ-δ) :=
      Real.rpow_lt_rpow_of_exponent_lt hN1 (by dsimp [η]; linarith only [hδg,hg])

private theorem pintz_second_zeta {σ τ : ℝ}
    (hσ : 39/40 ≤ σ) (hτ : 2 ≤ τ) (hτhi : τ < 30*σ-24) :
    zetaLargeValueExponent σ τ = ⊥ := by
  by_cases ht : τ ≤ 5/2
  · exact zetaLargeValueExponent_eq_bot_of_classical_pair
      (by linarith only [hσ]) (by linarith only [hτ])
      (by linarith only [ht,hσ])
  · apply pintz_heathBrown_zeta_nonexistence (k:=6) (by norm_num)
    · norm_num [heathBrownDerivativeExponent]
      linarith only [hτhi]
    · norm_num [heathBrownDerivativeExponent]
      linarith only [hσ]
    · norm_num [heathBrownInverseExponent]
      linarith only [ht,hσ]

private theorem pintz_fifth_correlation_bound {η : ℝ} (hη : 0 < η) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (v t N : ℝ) (a b : ℕ),
      0 < t → 1 ≤ N → N ≤ (a : ℝ) → (b : ℝ) ≤ 2*N → t ≤ N^v →
      ‖∑ n ∈ Finset.Icc a b, (n:ℂ)^(-((t:ℂ)*Complex.I))‖ ≤
        C*(N^(max (19/20) (3/4+v/20)+3*η)+2*Real.pi*N/t) := by
  obtain ⟨C₁,hC₁,hpair⟩ := exponentPair_half_half.aProcess.logarithmic_sum_bound hη
  obtain ⟨C₂,hC₂,hHB⟩ := pintz_heathBrown_logarithmic_sum_bound (k:=5) (by norm_num) hη
  let C := max C₁ (3*C₂)
  have hC : 1 ≤ C := hC₁.trans (le_max_left _ _)
  refine ⟨C,hC,?_⟩
  intro v t N a b ht hN ha hb htupper
  have hNp := zero_lt_one.trans_le hN
  let B := max (19/20:ℝ) (3/4+v/20)
  have hB₁ : 19/20 ≤ B := le_max_left _ _
  have hB₂ : 3/4+v/20 ≤ B := le_max_right _ _
  by_cases hlow : t ≤ N^(8/3:ℝ)
  · have hp := hpair t N a b ht hN ha hb
    norm_num only at hp
    have hmain : (t/N)^(1/6+η)*N^(2/3+η) ≤ N^(B+3*η) := by
      have hid : (t/N)^(1/6+η)*N^(2/3+η) = t^(1/6+η)*N^(1/2:ℝ) := by
        rw [Real.div_rpow ht.le hNp.le]
        calc
          _ = t^(1/6+η)*(N^(2/3+η)/N^(1/6+η)) := by ring
          _ = t^(1/6+η)*N^((2/3+η)-(1/6+η)) := by rw [Real.rpow_sub hNp]
          _ = _ := by congr 2; ring
      rw [hid]
      calc
        _ ≤ (N^(8/3:ℝ))^(1/6+η)*N^(1/2:ℝ) :=
          mul_le_mul_of_nonneg_right
            (Real.rpow_le_rpow ht.le hlow (by linarith only [hη]))
            (Real.rpow_nonneg hNp.le _)
        _ = N^((8/3)*(1/6+η)+1/2) := by
          rw [← Real.rpow_mul hNp.le,← Real.rpow_add hNp]
        _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hN (by linarith only [hB₁,hη])
    have hh := hp.trans (mul_le_mul_of_nonneg_left (add_le_add hmain le_rfl)
      (zero_le_one.trans hC₁))
    exact hh.trans (mul_le_mul_of_nonneg_right (le_max_left C₁ (3*C₂)) (by positivity))
  · have hlo : N^((v+8/3)/2-(v-8/3)/2) ≤ t := by
      convert (le_of_not_ge hlow) using 1
      congr 1
      ring
    have hhi : t ≤ N^((v+8/3)/2+(v-8/3)/2) := by
      convert htupper using 1
      congr 1
      ring
    have hm := pintz_heathBrown_window_majorant (k:=5) (η:=η) (B:=B) (by norm_num)
      hN hlo hhi
      (by norm_num [heathBrownDerivativeExponent]; linarith only [hB₂])
      (by norm_num [heathBrownDerivativeExponent]; exact hB₁)
      (by norm_num [heathBrownInverseExponent]; linarith only [hB₁])
    have hs := (hHB t N a b ht hN ha hb).trans
      (mul_le_mul_of_nonneg_left hm (zero_le_one.trans hC₂))
    have hexp : N^(η+B) ≤ N^(B+3*η) :=
      Real.rpow_le_rpow_of_exponent_le hN (by linarith only [hη])
    calc
      _ ≤ C₂*(3*N^(η+B)) := hs
      _ = (3*C₂)*N^(η+B) := by ring
      _ ≤ C*N^(B+3*η) := mul_le_mul (le_max_right C₁ (3*C₂)) hexp
        (Real.rpow_nonneg hNp.le _) (zero_le_one.trans hC)
      _ ≤ C*(N^(B+3*η)+2*Real.pi*N/t) :=
        mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (by positivity))
          (zero_le_one.trans hC)

private theorem pintz_sharp_gram_cardinality_of_correlation (P : LargeValuePattern)
    {C X : ℝ} (hC : 1 ≤ C) (hX : 0 ≤ X)
    (hcorr : ∀ t : ℝ, 0 < t → t ≤ P.T →
      ‖∑ n ∈ P.indices, dirichletPhase n t‖ ≤
        C*(X+2*Real.pi*P.N/t))
    (hvalue : 4*C*P.N*X ≤ P.V^2) :
    (P.ordinates.card:ℝ)*P.V^2 ≤
      4*P.N*(2*P.N+4*Real.pi*C*P.N*(harmonic (Nat.ceil P.T):ℝ)) := by
  classical
  have hNp : 0 < P.N := zero_lt_one.trans P.one_lt_N
  have hC0 : 0 ≤ C := zero_le_one.trans hC
  have hharm : (0:ℝ) ≤ harmonic (Nat.ceil P.T) := by
    exact_mod_cast (Finset.sum_nonneg (fun i _ =>
      inv_nonneg.mpr (Nat.cast_nonneg (i+1))) : (0:ℚ) ≤ harmonic (Nat.ceil P.T))
  by_cases hempty : P.ordinates = ∅
  · simpa only [hempty,Finset.card_empty,Nat.cast_zero,zero_mul] using
      (show 0 ≤ 4*P.N*(2*P.N+4*Real.pi*C*P.N*(harmonic (Nat.ceil P.T):ℝ)) by positivity)
  obtain ⟨t,ht,hgram⟩ := P.exists_large_sharp_gram_row (Finset.nonempty_iff_ne_empty.mpr hempty)
  let S := P.ordinates.erase t
  have hSW : S ⊆ P.ordinates := Finset.erase_subset _ _
  have hnear (u : ℝ) (hu : u ∈ S) : u ≠ t ∧ |u-t| ≤ P.T :=
    ⟨(Finset.mem_erase.mp hu).1,P.ordinate_gap_le_height ht (hSW hu)⟩
  have hpoint (u : ℝ) (hu : u ∈ S) :
      ‖∑ n ∈ P.indices, dirichletPhase n (u-t)‖ ≤
        C*X+(2*Real.pi*C*P.N)*(1/|u-t|) := by
    have hd := hnear u hu
    have hone : 1 ≤ |u-t| := P.ordinates_oneSeparated u (hSW hu) t ht hd.1
    have hh := hcorr |u-t| (by linarith only [hone]) hd.2
    rw [norm_sum_dirichletPhase_abs P.indices (fun n hn => P.index_pos hn) (u-t)] at hh
    convert hh using 1
    ring
  have hrecip : (∑ u ∈ S,1/|u-t|) ≤ 2*(harmonic (Nat.ceil P.T):ℝ) := by
    simpa only [div_one] using atkinson_sum_inv_gap_le_harmonic_ceil
      (G:=1) (by norm_num) P.ordinates_oneSeparated ht hSW hnear
  have hcard : (S.card:ℝ) ≤ P.ordinates.card := by
    exact_mod_cast Finset.card_le_card hSW
  have hsum : (∑ u ∈ S,‖∑ n ∈ P.indices,dirichletPhase n (u-t)‖) ≤
      C*(P.ordinates.card:ℝ)*X+4*Real.pi*C*P.N*(harmonic (Nat.ceil P.T):ℝ) := by
    calc
      _ ≤ ∑ u ∈ S,(C*X+(2*Real.pi*C*P.N)*(1/|u-t|)) := Finset.sum_le_sum hpoint
      _ = (S.card:ℝ)*(C*X)+(2*Real.pi*C*P.N)*(∑ u ∈ S,1/|u-t|) := by
        simp only [Finset.sum_add_distrib,Finset.sum_const,nsmul_eq_mul,Finset.mul_sum]
      _ ≤ (P.ordinates.card:ℝ)*(C*X)+
          (2*Real.pi*C*P.N)*(2*(harmonic (Nat.ceil P.T):ℝ)) :=
        add_le_add (mul_le_mul_of_nonneg_right hcard (by positivity))
          (mul_le_mul_of_nonneg_left hrecip (by positivity))
      _ = _ := by ring
  have hdiag : ‖∑ n ∈ P.indices,dirichletPhase n (t-t)‖ ≤ 2*P.N := by
    simpa only [sub_self,dirichletPhase_zero,Finset.sum_const,nsmul_eq_mul,mul_one,
      Complex.norm_natCast] using P.indices_card_cast_le_two_mul_N
  have hrow : (∑ u ∈ P.ordinates,‖∑ n ∈ P.indices,dirichletPhase n (u-t)‖) ≤
      2*P.N+C*(P.ordinates.card:ℝ)*X+
        4*Real.pi*C*P.N*(harmonic (Nat.ceil P.T):ℝ) := by
    rw [← Finset.sum_erase_add _ _ ht]
    change (∑ u ∈ S,‖∑ n ∈ P.indices,dirichletPhase n (u-t)‖)+
      ‖∑ n ∈ P.indices,dirichletPhase n (t-t)‖ ≤ _
    linarith only [hsum,hdiag]
  have hupper := hgram.trans (mul_le_mul_of_nonneg_left hrow (by positivity))
  have habsorb := mul_le_mul_of_nonneg_left hvalue (Nat.cast_nonneg P.ordinates.card)
  nlinarith only [hupper,habsorb]

private theorem pintz_fifth_local_largeValueBound {σ τ : ℝ}
    (hσ : 39/40 < σ) (hτ : 0 ≤ τ) (hτhi : τ < 40*σ-35) :
    IsLargeValueBound σ τ (2-2*σ) := by
  intro ε hε
  let g := min (2*σ-39/20) (2*σ-7/4-τ/20)
  have hg : 0 < g := lt_min (by linarith only [hσ]) (by linarith only [hτhi])
  have hg₁ : g ≤ 2*σ-39/20 := min_le_left _ _
  have hg₂ : g ≤ 2*σ-7/4-τ/20 := min_le_right _ _
  let η := g/32
  let δ := min 1 (min (ε/8) (g/32))
  have hη : 0 < η := by dsimp [η]; positivity
  have hδ : 0 < δ := lt_min (by norm_num) (lt_min (by positivity) (by positivity))
  have hδ1 : δ ≤ 1 := min_le_left _ _
  have hδε : δ ≤ ε/8 := (min_le_right _ _).trans (min_le_left _ _)
  have hδg : δ ≤ g/32 := (min_le_right _ _).trans (min_le_right _ _)
  let B := max (19/20:ℝ) (3/4+(τ+δ)/20)
  have hB : B ≤ 2*σ-2*δ-1-4*η := by
    apply max_le
    · dsimp only [η]
      linarith only [hg₁,hδg,hg]
    · dsimp only [η]
      linarith only [hg₂,hδg,hg]
  obtain ⟨C,hC,hbound⟩ := pintz_fifth_correlation_bound hη
  have hev : ∀ᶠ N : ℝ in Filter.atTop, 4*C ≤ N^η :=
    (tendsto_rpow_atTop hη).eventually (Filter.eventually_ge_atTop _)
  obtain ⟨Na,hNa⟩ := Filter.eventually_atTop.mp hev
  obtain ⟨Nd,hNd⟩ := Filter.eventually_atTop.mp
    (eventually_exponentPair_gram_diagonal hC hτ (show 0 < ε/2 by linarith only [hε]))
  let K := max 1 (max Na Nd)
  have hK : 1 ≤ K := le_max_left _ _
  have hKA : Na ≤ K := (le_max_left _ _).trans (le_max_right _ _)
  have hKD : Nd ≤ K := (le_max_right _ _).trans (le_max_right _ _)
  refine ⟨K,hK,δ,hδ,?_⟩
  intro P hN _ hTu hVl _
  have hNp : 0 < P.N := zero_lt_one.trans P.one_lt_N
  have hconstant := hNa P.N (hKA.trans hN)
  have hVpow : P.N^((σ-δ)*(2:ℝ)) ≤ P.V^2 := by
    rw [Real.rpow_mul hNp.le,Real.rpow_two]
    exact pow_le_pow_left₀ (Real.rpow_nonneg hNp.le _) hVl 2
  have hvalue : 4*C*P.N*P.N^(B+3*η) ≤ P.V^2 := by
    calc
      _ ≤ P.N^η*P.N*P.N^(B+3*η) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hconstant hNp.le)
          (Real.rpow_nonneg hNp.le _)
      _ = P.N^(η+1+(B+3*η)) := by
        rw [show P.N^η*P.N = P.N^(η+1) by rw [Real.rpow_add hNp,Real.rpow_one],
          ← Real.rpow_add hNp]
      _ ≤ P.N^((σ-δ)*2) :=
        Real.rpow_le_rpow_of_exponent_le P.one_lt_N.le (by linarith only [hB])
      _ ≤ P.V^2 := hVpow
  have hcorr : ∀ t : ℝ, 0 < t → t ≤ P.T →
      ‖∑ n ∈ P.indices,dirichletPhase n t‖ ≤ C*(P.N^(B+3*η)+2*Real.pi*P.N/t) := by
    intro t ht htT
    have hh := hbound (τ+δ) t P.N P.scale (2*P.scale) ht P.one_lt_N.le P.N_eq_scale.le
      (by rw [Nat.cast_mul,Nat.cast_ofNat,← P.N_eq_scale]) (htT.trans hTu)
    have heq : (∑ n ∈ P.indices,dirichletPhase n t) =
        ∑ n ∈ Finset.Icc P.scale (2*P.scale),(n:ℂ)^(-((t:ℂ)*Complex.I)) := by
      rw [P.indices_eq_dyadicInterval]
      apply Finset.sum_congr rfl
      intro n _
      simp only [dirichletPhase,mul_comm Complex.I (t:ℂ)]
      rfl
    rw [heq]
    exact hh
  have hfinite := pintz_sharp_gram_cardinality_of_correlation P hC
    (Real.rpow_nonneg hNp.le (B+3*η)) hcorr hvalue
  have hTpower : P.T ≤ P.N^(τ+1) :=
    hTu.trans (Real.rpow_le_rpow_of_exponent_le P.one_lt_N.le (by linarith only [hδ1]))
  have hdiag := hfinite.trans (hNd P.N (hKD.trans hN) P.T P.T_pos hTpower)
  have hr : (P.ordinates.card:ℝ) ≤ P.N^((2+ε/2)-(σ-δ)*2) := by
    rw [Real.rpow_sub hNp]
    apply (le_div_iff₀ (Real.rpow_pos_of_pos hNp _)).mpr
    exact (mul_le_mul_of_nonneg_left hVpow (Nat.cast_nonneg _)).trans hdiag
  calc
    _ ≤ P.N^((2+ε/2)-(σ-δ)*2) := hr
    _ ≤ P.N^(2-2*σ+ε) :=
      Real.rpow_le_rpow_of_exponent_le P.one_lt_N.le (by linarith only [hδε,hε])
    _ ≤ K*P.N^(2-2*σ+ε) :=
      le_mul_of_one_le_left (Real.rpow_nonneg hNp.le _) hK

theorem zeroDensityExponent_le_pintz_second_interior {σ : ℝ} (hσ : 39/40 < σ) (hσ1 : σ < 1) :
    zeroDensityExponent σ ≤ ((2/(15*σ-12):ℝ):EReal) := by
  have hh : zeroDensityExponent σ ≤ ((3/((45*σ-36)/2):ℝ):EReal) := by
    apply zeroDensityExponent_le_three_div_of_montgomery_range σ ((45*σ-36)/2)
      (by linarith only [hσ]) hσ1 (by linarith only [hσ])
    · intro τ hτ
      rw [pintz_second_zeta hσ.le hτ.1 (by linarith only [hτ.2])]
      exact bot_le
    · intro τ hτ
      exact largeValueExponent_le_of_bound (pintz_fifth_local_largeValueBound hσ hτ.1
        (by linarith only [hσ,hτ.2]))
  have he : (45*σ-36)/2 = (3/2)*(15*σ-12) := by ring
  simpa only [he,div_mul_eq_div_div,show (3:ℝ)/(3/2)=2 by norm_num] using hh

private theorem pintz_third_zeta_interior {σ τ : ℝ}
    (hσ : 41/42 < σ) (hσ1 : σ < 1)
    (hτ : 2 ≤ τ) (hτhi : τ < 4*(40*σ-35)/3) :
    zetaLargeValueExponent σ τ = ⊥ := by
  by_cases ht : τ ≤ 4
  · exact pintz_second_zeta (by linarith only [hσ]) hτ
      (by linarith only [hσ,ht])
  · apply pintz_heathBrown_zeta_nonexistence (k:=7) (by norm_num)
    · norm_num [heathBrownDerivativeExponent]
      linarith only [hτhi,hσ1]
    · norm_num [heathBrownDerivativeExponent]
      exact hσ
    · norm_num [heathBrownInverseExponent]
      linarith only [ht,hσ]

theorem zeroDensityExponent_le_pintz_third_interior {σ : ℝ} (hσ : 41/42 < σ) (hσ1 : σ < 1) :
    zeroDensityExponent σ ≤ ((3/(40*σ-35):ℝ):EReal) := by
  apply zeroDensityExponent_le_three_div_of_montgomery_range σ (40*σ-35)
    (by linarith only [hσ]) hσ1 (by linarith only [hσ])
  · intro τ hτ
    rw [pintz_third_zeta_interior hσ hσ1 hτ.1 hτ.2]
    exact bot_le
  · intro τ hτ
    exact largeValueExponent_le_of_bound (pintz_fifth_local_largeValueBound
      (by linarith only [hσ]) hτ.1 (by linarith only [hτ.2,hσ1]))

private theorem pintz_exists_heathBrown_order_for_cell {n : ℕ} (hn : 3 ≤ n)
    {γ s : ℝ} (hγ : 0 ≤ γ) (hγhi : γ ≤ 1/24)
    (hcell : 2*γ*(n:ℝ)*((n:ℝ)-1) ≤ 1)
    (hs : 1 ≤ s) (hupper : s ≤ (n:ℝ)*(1-2*((n:ℝ)-1)*γ)) :
    ∃ j : ℕ, 3 ≤ j ∧ j ≤ n ∧
      1+(s-(j:ℝ))*heathBrownDerivativeExponent j ≤ 1-2*γ ∧
      1-heathBrownDerivativeExponent j ≤ 1-2*γ ∧
      1-s*heathBrownInverseExponent j ≤ 1-2*γ := by
  classical
  have hex : ∃ j : ℕ, 3 ≤ j ∧ j ≤ n ∧
      s ≤ (j:ℝ)*(1-2*((j:ℝ)-1)*γ) := ⟨n,hn,le_rfl,hupper⟩
  let j := Nat.find hex
  obtain ⟨hj,hjn,huj⟩ := Nat.find_spec hex
  change 3 ≤ j at hj
  change j ≤ n at hjn
  change s ≤ (j:ℝ)*(1-2*((j:ℝ)-1)*γ) at huj
  have hjr : (3:ℝ) ≤ j := by exact_mod_cast hj
  have hjnr : (j:ℝ) ≤ n := by exact_mod_cast hjn
  have hprod : (j:ℝ)*((j:ℝ)-1) ≤ (n:ℝ)*((n:ℝ)-1) :=
    mul_le_mul hjnr (sub_le_sub_right hjnr 1) (by linarith only [hjr]) (Nat.cast_nonneg n)
  have hjcell : 2*γ*(j:ℝ)*((j:ℝ)-1) ≤ 1 := by
    have hh := mul_le_mul_of_nonneg_left hprod (show 0 ≤ 2*γ by positivity)
    nlinarith only [hh,hcell]
  have hlow : γ*(j:ℝ)^2*((j:ℝ)-1) ≤ s := by
    by_cases hj3 : j = 3
    · norm_num only [hj3,Nat.cast_ofNat]
      linarith only [hγhi,hs]
    · have hj4 : 4 ≤ j := by omega
      have hprev := Nat.find_min hex (show j-1 < Nat.find hex by change j-1 < j; omega)
      have hprevUpper : ((j-1:ℕ):ℝ)*(1-2*(((j-1:ℕ):ℝ)-1)*γ) < s := by
        apply lt_of_not_ge
        intro h
        exact hprev ⟨by omega,by omega,h⟩
      have hcast : ((j-1:ℕ):ℝ) = (j:ℝ)-1 := by
        rw [Nat.cast_sub (by omega : 1 ≤ j)]
        norm_num
      rw [hcast] at hprevUpper
      have hbudget : γ*((j:ℝ)^2+2*(j:ℝ)-4) ≤ 1 := by
        nlinarith only [hjcell,mul_nonneg hγ (sq_nonneg ((j:ℝ)-2))]
      have hm := mul_le_mul_of_nonneg_right hbudget
        (show 0 ≤ (j:ℝ)-1 by linarith only [hjr])
      nlinarith only [hm,hprevUpper]
  have hd : 0 < (j:ℝ)*((j:ℝ)-1) := by
    apply mul_pos <;> linarith only [hjr]
  have he : 0 < (j:ℝ)^2*((j:ℝ)-1) := by
    have hjp : 0 < (j:ℝ) := by linarith only [hjr]
    exact mul_pos (pow_pos hjp 2) (by linarith only [hjr])
  refine ⟨j,hj,hjn,?_,?_,?_⟩
  · have hh : (s-(j:ℝ))/((j:ℝ)*((j:ℝ)-1)) ≤ -2*γ := by
      apply (div_le_iff₀ hd).mpr
      nlinarith only [huj]
    unfold heathBrownDerivativeExponent
    rw [mul_one_div]
    linarith only [hh]
  · have hh : 2*γ ≤ 1/((j:ℝ)*((j:ℝ)-1)) := by
      apply (le_div_iff₀ hd).mpr
      nlinarith only [hjcell]
    unfold heathBrownDerivativeExponent
    linarith only [hh]
  · have hh : 2*γ ≤ 2*s/((j:ℝ)^2*((j:ℝ)-1)) := by
      apply (le_div_iff₀ he).mpr
      nlinarith only [hlow]
    unfold heathBrownInverseExponent
    rw [show s*(2/((j:ℝ)^2*((j:ℝ)-1))) = 2*s/((j:ℝ)^2*((j:ℝ)-1)) by ring]
    linarith only [hh]

private theorem pintz_cell_correlation_bound {n : ℕ} (hn : 3 ≤ n)
    {γ η : ℝ} (hγ : 0 ≤ γ) (hγhi : γ ≤ 1/24)
    (hcell : 2*γ*(n:ℝ)*((n:ℝ)-1) ≤ 1) (hη : 0 < η) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (v t N : ℝ) (a b : ℕ),
      v ≤ (n:ℝ)*(1-2*((n:ℝ)-1)*γ) →
      0 < t → 1 < N → N ≤ (a:ℝ) → (b:ℝ) ≤ 2*N → t ≤ N^v →
      ‖∑ m ∈ Finset.Icc a b,(m:ℂ)^(-((t:ℂ)*Complex.I))‖ ≤
        C*(N^(1-2*γ+3*η)+2*Real.pi*N/t) := by
  classical
  let J := {j : ℕ // j ∈ Finset.Icc 3 n}
  letI : Fintype J := Finset.fintypeCoeSort (Finset.Icc 3 n)
  have hex : ∀ j : J, ∃ C : ℝ, 1 ≤ C ∧ ∀ (t N : ℝ) (a b : ℕ),
      0 < t → 1 ≤ N → N ≤ (a:ℝ) → (b:ℝ) ≤ 2*N →
      ‖∑ m ∈ Finset.Icc a b,(m:ℂ)^(-((t:ℂ)*Complex.I))‖ ≤
        C*heathBrownPowerMajorant j.val η t N := by
    intro j
    exact pintz_heathBrown_logarithmic_sum_bound (Finset.mem_Icc.mp j.property).1 hη
  choose Cj hCj hBj using hex
  let D := ∑ j : J,Cj j
  have hjD (j : J) : Cj j ≤ D :=
    Finset.single_le_sum (fun i _ => zero_le_one.trans (hCj i)) (Finset.mem_univ j)
  obtain ⟨C₁,hC₁,hpair⟩ := exponentPair_half_half.aProcess.logarithmic_sum_bound hη
  let C := max C₁ (3*D)
  have hC : 1 ≤ C := hC₁.trans (le_max_left _ _)
  refine ⟨C,hC,?_⟩
  intro v t N a b hv ht hN ha hb htv
  have hNp : 0 < N := zero_lt_one.trans hN
  by_cases hlow : t ≤ N
  · have hp := hpair t N a b ht hN.le ha hb
    norm_num only at hp
    have hmain : (t/N)^(1/6+η)*N^(2/3+η) ≤ N^(1-2*γ+3*η) := by
      have hratio : (t/N)^(1/6+η) ≤ 1 := by
        apply Real.rpow_le_one (by positivity) ((div_le_one hNp).mpr hlow)
        linarith only [hη]
      calc
        _ ≤ 1*N^(2/3+η) := mul_le_mul_of_nonneg_right hratio (Real.rpow_nonneg hNp.le _)
        _ = N^(2/3+η) := one_mul _
        _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hN.le (by linarith only [hγhi,hη])
    have hh := hp.trans (mul_le_mul_of_nonneg_left (add_le_add hmain le_rfl)
      (zero_le_one.trans hC₁))
    exact hh.trans (mul_le_mul_of_nonneg_right (le_max_left C₁ (3*D)) (by positivity))
  · let s := Real.logb N t
    have hs : 1 ≤ s := by
      have hh := Real.logb_le_logb_of_le hN hNp (le_of_not_ge hlow)
      simpa only [Real.logb_self_eq_one hN] using hh
    have hsv : s ≤ v := (Real.logb_le_iff_le_rpow hN ht).mpr htv
    obtain ⟨j,hj,hjn,hfirst,hsecond,hthird⟩ :=
      pintz_exists_heathBrown_order_for_cell hn hγ hγhi hcell hs (hsv.trans hv)
    let j₀ : J := ⟨j,Finset.mem_Icc.mpr ⟨hj,hjn⟩⟩
    have hpow : N^s = t := Real.rpow_logb hNp (ne_of_gt hN) ht
    have hm := pintz_heathBrown_window_majorant (k:=j) (η:=η) (τ:=s) (δ:=0)
      (B:=1-2*γ) hj hN.le (by simpa only [sub_zero] using hpow.le)
      (by simpa only [add_zero] using hpow.ge)
      (by simpa only [add_zero] using hfirst) hsecond
      (by simpa only [sub_zero] using hthird)
    have hh := (hBj j₀ t N a b ht hN.le ha hb).trans
      (mul_le_mul_of_nonneg_left hm (zero_le_one.trans (hCj j₀)))
    have hconst : 3*Cj j₀ ≤ C :=
      (mul_le_mul_of_nonneg_left (hjD j₀) (by norm_num : (0:ℝ) ≤ 3)).trans
        (le_max_right C₁ (3*D))
    have he : N^(η+(1-2*γ)) ≤ N^(1-2*γ+3*η) :=
      Real.rpow_le_rpow_of_exponent_le hN.le (by linarith only [hη])
    calc
      _ ≤ Cj j₀*(3*N^(η+(1-2*γ))) := hh
      _ = (3*Cj j₀)*N^(η+(1-2*γ)) := by ring
      _ ≤ C*N^(1-2*γ+3*η) := mul_le_mul hconst he
        (Real.rpow_nonneg hNp.le _) (zero_le_one.trans hC)
      _ ≤ C*(N^(1-2*γ+3*η)+2*Real.pi*N/t) :=
        mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (by positivity))
          (zero_le_one.trans hC)

private theorem pintz_cell_local_largeValueBound {n : ℕ} (hn : 3 ≤ n)
    {γ σ τ : ℝ} (hγ : 0 ≤ γ) (hγhi : γ ≤ 1/24)
    (hcell : 2*γ*(n:ℝ)*((n:ℝ)-1) ≤ 1)
    (hσ : 1-γ < σ) (hτ : 0 ≤ τ)
    (hτhi : τ < (n:ℝ)*(1-2*((n:ℝ)-1)*γ)) :
    IsLargeValueBound σ τ (2-2*σ) := by
  intro ε hε
  let g := σ-(1-γ)
  let h := (n:ℝ)*(1-2*((n:ℝ)-1)*γ)-τ
  have hg : 0 < g := sub_pos.mpr hσ
  have hheight : 0 < h := sub_pos.mpr hτhi
  let η := g/32
  let δ := min 1 (min (ε/8) (min (g/8) (h/2)))
  have hη : 0 < η := by dsimp [η]; positivity
  have hδ : 0 < δ := lt_min (by norm_num)
    (lt_min (by positivity) (lt_min (by positivity) (by positivity)))
  have hδ1 : δ ≤ 1 := min_le_left _ _
  have hδε : δ ≤ ε/8 := (min_le_right _ _).trans (min_le_left _ _)
  have hδtail : δ ≤ min (g/8) (h/2) :=
    (min_le_right _ _).trans (min_le_right _ _)
  have hδg : δ ≤ g/8 := hδtail.trans (min_le_left _ _)
  have hδh : δ ≤ h/2 := hδtail.trans (min_le_right _ _)
  let B := 1-2*γ
  have hB : B ≤ 2*σ-2*δ-1-4*η := by
    dsimp only [B,η,g] at hg hδg ⊢
    linarith only [hg,hδg]
  obtain ⟨C,hC,hbound⟩ := pintz_cell_correlation_bound hn hγ hγhi hcell hη
  have hev : ∀ᶠ N : ℝ in Filter.atTop, 4*C ≤ N^η :=
    (tendsto_rpow_atTop hη).eventually (Filter.eventually_ge_atTop _)
  obtain ⟨Na,hNa⟩ := Filter.eventually_atTop.mp hev
  obtain ⟨Nd,hNd⟩ := Filter.eventually_atTop.mp
    (eventually_exponentPair_gram_diagonal hC hτ (show 0 < ε/2 by linarith only [hε]))
  let K := max 1 (max Na Nd)
  have hK : 1 ≤ K := le_max_left _ _
  have hKA : Na ≤ K := (le_max_left _ _).trans (le_max_right _ _)
  have hKD : Nd ≤ K := (le_max_right _ _).trans (le_max_right _ _)
  refine ⟨K,hK,δ,hδ,?_⟩
  intro P hN _ hTu hVl _
  have hNp : 0 < P.N := zero_lt_one.trans P.one_lt_N
  have hconstant := hNa P.N (hKA.trans hN)
  have hVpow : P.N^((σ-δ)*(2:ℝ)) ≤ P.V^2 := by
    rw [Real.rpow_mul hNp.le,Real.rpow_two]
    exact pow_le_pow_left₀ (Real.rpow_nonneg hNp.le _) hVl 2
  have hvalue : 4*C*P.N*P.N^(B+3*η) ≤ P.V^2 := by
    calc
      _ ≤ P.N^η*P.N*P.N^(B+3*η) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hconstant hNp.le)
          (Real.rpow_nonneg hNp.le _)
      _ = P.N^(η+1+(B+3*η)) := by
        rw [show P.N^η*P.N = P.N^(η+1) by rw [Real.rpow_add hNp,Real.rpow_one],
          ← Real.rpow_add hNp]
      _ ≤ P.N^((σ-δ)*2) :=
        Real.rpow_le_rpow_of_exponent_le P.one_lt_N.le (by linarith only [hB])
      _ ≤ P.V^2 := hVpow
  have hcorr : ∀ t : ℝ, 0 < t → t ≤ P.T →
      ‖∑ n ∈ P.indices,dirichletPhase n t‖ ≤ C*(P.N^(B+3*η)+2*Real.pi*P.N/t) := by
    intro t ht htT
    have hh := hbound (τ+δ) t P.N P.scale (2*P.scale)
      (by dsimp only [h] at hδh; linarith only [hδh,hheight]) ht P.one_lt_N P.N_eq_scale.le
      (by rw [Nat.cast_mul,Nat.cast_ofNat,← P.N_eq_scale]) (htT.trans hTu)
    have heq : (∑ n ∈ P.indices,dirichletPhase n t) =
        ∑ n ∈ Finset.Icc P.scale (2*P.scale),(n:ℂ)^(-((t:ℂ)*Complex.I)) := by
      rw [P.indices_eq_dyadicInterval]
      apply Finset.sum_congr rfl
      intro n _
      simp only [dirichletPhase,mul_comm Complex.I (t:ℂ)]
      rfl
    rw [heq]
    exact hh
  have hfinite := pintz_sharp_gram_cardinality_of_correlation P hC
    (Real.rpow_nonneg hNp.le (B+3*η)) hcorr hvalue
  have hTpower : P.T ≤ P.N^(τ+1) :=
    hTu.trans (Real.rpow_le_rpow_of_exponent_le P.one_lt_N.le (by linarith only [hδ1]))
  have hdiag := hfinite.trans (hNd P.N (hKD.trans hN) P.T P.T_pos hTpower)
  have hr : (P.ordinates.card:ℝ) ≤ P.N^((2+ε/2)-(σ-δ)*2) := by
    rw [Real.rpow_sub hNp]
    apply (le_div_iff₀ (Real.rpow_pos_of_pos hNp _)).mpr
    exact (mul_le_mul_of_nonneg_left hVpow (Nat.cast_nonneg _)).trans hdiag
  calc
    _ ≤ P.N^((2+ε/2)-(σ-δ)*2) := hr
    _ ≤ P.N^(2-2*σ+ε) :=
      Real.rpow_le_rpow_of_exponent_le P.one_lt_N.le (by linarith only [hδε,hε])
    _ ≤ K*P.N^(2-2*σ+ε) :=
      le_mul_of_one_le_left (Real.rpow_nonneg hNp.le _) hK

private theorem pintz_exists_strict_cell_margin {n : ℕ} (hn : 4 ≤ n)
    {γ₀ τ : ℝ} (hγ₀ : 0 ≤ γ₀)
    (hcell : 2*γ₀*(n:ℝ)*((n:ℝ)-1) < 1)
    (hτ : τ < (n:ℝ)*(1-2*((n:ℝ)-1)*γ₀)) :
    ∃ γ : ℝ, γ₀ < γ ∧ 0 ≤ γ ∧ γ ≤ 1/24 ∧
      2*γ*(n:ℝ)*((n:ℝ)-1) ≤ 1 ∧
      τ < (n:ℝ)*(1-2*((n:ℝ)-1)*γ) := by
  have hnr : (4:ℝ) ≤ n := by exact_mod_cast hn
  let P := (n:ℝ)*((n:ℝ)-1)
  have hP : 12 ≤ P := by dsimp [P]; nlinarith only [hnr]
  have hPpos : 0 < P := by linarith only [hP]
  have hcellP : 2*γ₀*P < 1 := by dsimp only [P]; nlinarith only [hcell]
  let H := (n:ℝ)*(1-2*((n:ℝ)-1)*γ₀)-τ
  have hH : 0 < H := sub_pos.mpr hτ
  let a := min ((1-2*γ₀*P)/(4*P)) (H/(4*P))
  have ha : 0 < a := lt_min (div_pos (by linarith only [hcellP]) (by positivity))
    (div_pos hH (by positivity))
  have haC : 4*P*a ≤ 1-2*γ₀*P := by
    have hh := (le_div_iff₀ (by positivity : 0 < 4*P)).mp
      (show a ≤ (1-2*γ₀*P)/(4*P) from min_le_left _ _)
    nlinarith only [hh]
  have haH : 4*P*a ≤ H := by
    have hh := (le_div_iff₀ (by positivity : 0 < 4*P)).mp
      (show a ≤ H/(4*P) from min_le_right _ _)
    nlinarith only [hh]
  have hγ : 0 ≤ γ₀+a := add_nonneg hγ₀ ha.le
  have hγP : 2*(γ₀+a)*P ≤ 1 := by
    nlinarith only [haC,hcellP]
  have hγhi : γ₀+a ≤ 1/24 := by
    have hm := mul_le_mul_of_nonneg_left hP (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) hγ)
    nlinarith only [hm,hγP]
  refine ⟨γ₀+a,by linarith only [ha],hγ,hγhi,?_,?_⟩
  · dsimp only [P] at hγP
    nlinarith only [hγP]
  · dsimp only [P,H] at haH hH
    nlinarith only [haH,hH]

private theorem pintz_heathBrown_cell_montgomery {n : ℕ} (hn : 4 ≤ n)
    {σ τ : ℝ} (hσ1 : σ ≤ 1)
    (hcell : 2*(1-σ)*(n:ℝ)*((n:ℝ)-1) < 1)
    (hτ : 0 ≤ τ) (hτhi : τ < (n:ℝ)*(1-2*((n:ℝ)-1)*(1-σ))) :
    IsLargeValueBound σ τ (2-2*σ) := by
  obtain ⟨γ,hγgap,hγ,hγhi,hγcell,hγτ⟩ :=
    pintz_exists_strict_cell_margin hn (sub_nonneg.mpr hσ1) hcell hτhi
  exact pintz_cell_local_largeValueBound (by omega) hγ hγhi hγcell
    (by linarith only [hγgap]) hτ hγτ

private theorem pintz_heathBrown_cell_zeta {n : ℕ} (hn : 4 ≤ n)
    {σ τ : ℝ} (hσ1 : σ ≤ 1)
    (hcell : (1-σ)*(n:ℝ)*((n:ℝ)-1) < 1)
    (hτ : 1 ≤ τ) (hτhi : τ < (n:ℝ)*(1-((n:ℝ)-1)*(1-σ))) :
    zetaLargeValueExponent σ τ = ⊥ := by
  obtain ⟨γ,hγgap,hγ,hγhi,hγcell,hγτ⟩ :=
    pintz_exists_strict_cell_margin (γ₀:=(1-σ)/2) (τ:=τ) hn (by linarith only [hσ1])
      (by nlinarith only [hcell]) (by nlinarith only [hτhi])
  obtain ⟨j,hj,_hjn,hfirst,hsecond,hthird⟩ :=
    pintz_exists_heathBrown_order_for_cell (by omega) hγ hγhi hγcell hτ hγτ.le
  apply pintz_heathBrown_zeta_nonexistence hj
  · linarith only [hfirst,hγgap]
  · linarith only [hsecond,hγgap]
  · linarith only [hthird,hγgap]

private theorem pintz_exists_pintz_tail_zeta_order {n : ℕ} (hn : 6 ≤ n)
    {η : ℝ} (hη : 0 ≤ η)
    (hupper : 2*η*(n:ℝ)*((n:ℝ)-1) < 1)
    (hlower : 1 ≤ 2*η*(n:ℝ)*((n:ℝ)+1)) :
    ∃ m : ℕ, 4 ≤ m ∧ η*(m:ℝ)*((m:ℝ)-1) < 1 ∧
      4*((n:ℝ)*(1-2*((n:ℝ)-1)*η))/3 ≤
        (m:ℝ)*(1-((m:ℝ)-1)*η) := by
  let m := (4*n+1)/3
  have hm : 4 ≤ m := by dsimp only [m]; omega
  have hmlo : 4*n ≤ 3*m+1 := by dsimp only [m]; omega
  have hmhi : 3*m ≤ 4*n+1 := by dsimp only [m]; omega
  have hnr : (6:ℝ) ≤ n := by exact_mod_cast hn
  have hmr : (4:ℝ) ≤ m := by exact_mod_cast hm
  have hmlor : 4*(n:ℝ) ≤ 3*(m:ℝ)+1 := by exact_mod_cast hmlo
  have hmhir : 3*(m:ℝ) ≤ 4*(n:ℝ)+1 := by exact_mod_cast hmhi
  have hprod : (m:ℝ)*((m:ℝ)-1) ≤ 2*(n:ℝ)*((n:ℝ)-1) := by
    by_cases hn6 : n = 6
    · norm_num [m,hn6]
    · have hn7 : (7:ℝ) ≤ n := by exact_mod_cast (show 7 ≤ n by omega)
      have hsq : (3*(m:ℝ))^2 ≤ (4*(n:ℝ)+1)^2 :=
        sq_le_sq₀ (by positivity) (by positivity) |>.2 hmhir
      have hdiff := mul_nonneg (show 0 ≤ (n:ℝ)-7 by linarith only [hn7])
        (show 0 ≤ (n:ℝ) by positivity)
      nlinarith only [hsq,hmhir,hmr,hdiff,hmlor]
  have hcell : η*(m:ℝ)*((m:ℝ)-1) < 1 := by
    have hh := mul_le_mul_of_nonneg_left hprod hη
    nlinarith only [hh,hupper]
  let B := 8*(n:ℝ)*((n:ℝ)-1)/3-(m:ℝ)*((m:ℝ)-1)
  have hB : 0 ≤ B := by dsimp only [B]; nlinarith only [hprod,hnr]
  refine ⟨m,hm,hcell,?_⟩
  by_cases hhigh : 4*n ≤ 3*m
  · have hh : 4*(n:ℝ) ≤ 3*(m:ℝ) := by exact_mod_cast hhigh
    have hhB := mul_nonneg hη hB
    dsimp only [B] at hhB
    nlinarith only [hh,hhB]
  · have he : 3*m+1 = 4*n := by omega
    have her : 3*(m:ℝ)+1 = 4*(n:ℝ) := by exact_mod_cast he
    have hBstrong : 2*(n:ℝ)*((n:ℝ)+1)/3 ≤ B := by
      have hdiff := mul_nonneg (show 0 ≤ (n:ℝ)-6 by linarith only [hnr])
        (show 0 ≤ (n:ℝ) by positivity)
      dsimp only [B]
      nlinarith only [her,hdiff,hnr,sq_nonneg (3*(m:ℝ)+1-4*(n:ℝ))]
    have hh := mul_le_mul_of_nonneg_left hBstrong hη
    dsimp only [B] at hh
    nlinarith only [hh,hlower,her]

theorem zeroDensityExponent_le_pintz_tail_interior {n : ℕ} (hn : 6 ≤ n) {σ : ℝ}
    (hσlo : 1-1/(2*(n:ℝ)*((n:ℝ)-1)) < σ)
    (hσhi : σ ≤ 1-1/(2*(n:ℝ)*((n:ℝ)+1))) :
    zeroDensityExponent σ ≤
      ((3/((n:ℝ)*(1-2*((n:ℝ)-1)*(1-σ))):ℝ):EReal) := by
  have hnr : (6:ℝ) ≤ n := by exact_mod_cast hn
  have hD : 0 < 2*(n:ℝ)*((n:ℝ)-1) := by
    apply mul_pos <;> linarith only [hnr]
  have hD' : 0 < 2*(n:ℝ)*((n:ℝ)+1) := by positivity
  have hσ1 : σ < 1 := by
    have hh := one_div_pos.mpr hD'
    linarith only [hσhi,hh]
  have hη : 0 ≤ 1-σ := sub_nonneg.mpr hσ1.le
  have hupper : 2*(1-σ)*(n:ℝ)*((n:ℝ)-1) < 1 := by
    have hh := (lt_div_iff₀ hD).mp
      (show 1-σ < 1/(2*(n:ℝ)*((n:ℝ)-1)) by linarith only [hσlo])
    nlinarith only [hh]
  have hlower : 1 ≤ 2*(1-σ)*(n:ℝ)*((n:ℝ)+1) := by
    have hh := (div_le_iff₀ hD').mp
      (show 1/(2*(n:ℝ)*((n:ℝ)+1)) ≤ 1-σ by linarith only [hσhi])
    nlinarith only [hh]
  have hσhalf : 1/2 < σ := by
    have hprod : (30:ℝ) ≤ (n:ℝ)*((n:ℝ)-1) := by nlinarith only [hnr]
    have hh := mul_le_mul_of_nonneg_left hprod (show 0 ≤ 2*(1-σ) by positivity)
    nlinarith only [hh,hupper]
  have hcut : 0 < (n:ℝ)*(1-2*((n:ℝ)-1)*(1-σ)) := by
    nlinarith only [hupper,hnr]
  obtain ⟨m,hm,hmcell,hmrange⟩ := pintz_exists_pintz_tail_zeta_order hn hη hupper hlower
  apply zeroDensityExponent_le_three_div_of_montgomery_range σ
    ((n:ℝ)*(1-2*((n:ℝ)-1)*(1-σ))) hσhalf hσ1 hcut
  · intro τ hτ
    rw [pintz_heathBrown_cell_zeta hm hσ1.le hmcell (by linarith only [hτ.1])
      (hτ.2.trans_le hmrange)]
    exact bot_le
  · intro τ hτ
    exact largeValueExponent_le_of_bound (pintz_heathBrown_cell_montgomery
      (by omega : 4 ≤ n) hσ1.le hupper hτ.1 (by linarith only [hτ.2,hσ1]))

end TaoTrudgianYang2025

open MeasureTheory RiemannZeta.GuthMaynard Set
open scoped Interval Classical

namespace TaoTrudgianYang2025

private theorem literatureTwelfth_retained_quadratic {R a b M : ℝ}
    (hR : 0 ≤ R) (hM : 0 ≤ M) (h : R ≤ a+b*Real.sqrt M) :
    R^2 ≤ 2*a*R+b^2*M := by
  have hm := mul_le_mul_of_nonneg_right h hR
  have hs := sq_nonneg (R-b*Real.sqrt M)
  have he : (b*Real.sqrt M)^2 = b^2*M := by
    rw [mul_pow,Real.sq_sqrt hM]
  nlinarith only [hm,hs,he]

private theorem literatureTwelfth_localized_retained_quadratic {σ τ : ℝ}
    (hσ : 3/4 < σ) {ε : ℝ} (hε : 0 < ε) :
    ∃ C δ : ℝ, 1 ≤ C ∧ 0 < δ ∧
      ∀ (P : LargeValuePattern) (L : ℝ) (hL : 0 < L),
        C ≤ P.N → P.N ≤ L → L ≤ P.N^(τ+δ) → P.N^(σ-δ) ≤ P.V →
        ∃ W : ℕ → Finset ℝ,
          (∀ i : ℕ, W i ⊆ (P.localized L hL i).reflectedOrdinates ∧
            IsSeparated 2 (W i) ∧ InBaseInterval L (W i) ∧
            ((P.localized L hL i).ordinates.card:ℝ) ≤ C*P.N^ε*((W i).card:ℝ)) ∧
          let I := Finset.range (Nat.floor (P.T/L)+1)
          (∑ i ∈ I, ((P.localized L hL i).ordinates.card:ℝ)^2) ≤
            2*C*(P.N^(2-2*σ+ε)+P.N^(2*τ+4-8*σ+ε))*(P.ordinates.card:ℝ)+
            (C*P.N^(3-4*σ+ε))^2 *
              ∑ i ∈ I, bourgainZetaDifferenceMoment (W i) (P.N^ε) := by
  obtain ⟨C,δ,hC,hδ,hbound⟩ := bourgain_retained_source_power_bound (τ:=τ) hσ hε
  refine ⟨C,δ,hC,hδ,?_⟩
  intro P L hL hN hNL hTu hV
  have hNp : 0 < P.N := zero_lt_one.trans P.one_lt_N
  have hlocal (i : ℕ) := hbound (P.localized L hL i) hN hNL hTu hV
  choose W hsub hsep hbase hpack hrec using hlocal
  refine ⟨W,fun i => ⟨hsub i,hsep i,hbase i,hpack i⟩,?_⟩
  let I := Finset.range (Nat.floor (P.T/L)+1)
  have hquad (i : ℕ) :
      ((P.localized L hL i).ordinates.card:ℝ)^2 ≤
        2*(C*(P.N^(2-2*σ+ε)+P.N^(2*τ+4-8*σ+ε)))*
          ((P.localized L hL i).ordinates.card:ℝ)+
        (C*P.N^(3-4*σ+ε))^2*bourgainZetaDifferenceMoment (W i) (P.N^ε) := by
    apply literatureTwelfth_retained_quadratic (Nat.cast_nonneg _)
      (bourgainZetaDifferenceMoment_nonneg _ (by positivity))
    have hh := hrec i
    change ((P.localized L hL i).ordinates.card:ℝ) ≤
      C*(P.N^(2-2*σ+ε)+P.N^(2*τ+4-8*σ+ε)+
        P.N^(3-4*σ+ε)*Real.sqrt (bourgainZetaDifferenceMoment (W i) (P.N^ε))) at hh
    convert hh using 1
    ring
  have hsum := Finset.sum_le_sum (fun i (_hi : i ∈ I) => hquad i)
  have hpartition : (∑ i ∈ I,((P.localized L hL i).ordinates.card:ℝ)) =
      (P.ordinates.card:ℝ) := by
    exact_mod_cast (P.card_eq_sum_localized hL).symm
  rw [Finset.sum_add_distrib,← Finset.mul_sum,← Finset.mul_sum,hpartition] at hsum
  convert hsum using 1
  ring

private theorem literatureTwelfth_localized_square_mass (P : LargeValuePattern) {L : ℝ} (hL : 0 < L) :
    (P.ordinates.card:ℝ)^2 ≤
      ((Finset.range (Nat.floor (P.T/L)+1)).card:ℝ)*
        ∑ i ∈ Finset.range (Nat.floor (P.T/L)+1),
          ((P.localized L hL i).ordinates.card:ℝ)^2 := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq
    (Finset.range (Nat.floor (P.T/L)+1))
    (fun _ => (1:ℝ)) (fun i => ((P.localized L hL i).ordinates.card:ℝ))
  simp only [one_mul,one_pow,Finset.sum_const,nsmul_eq_mul,mul_one] at h
  have he : (∑ i ∈ Finset.range (Nat.floor (P.T/L)+1),
      ((P.localized L hL i).ordinates.card:ℝ)) = (P.ordinates.card:ℝ) := by
    exact_mod_cast (P.card_eq_sum_localized hL).symm
  simpa only [he] using h

private theorem literatureTwelfth_zeta_twelfth_symmetric {ε : ℝ} (hε : 0 < ε) :
    ∃ C T₀ : ℝ, 0 < C ∧ 1 ≤ T₀ ∧ ∀ T : ℝ, T₀ ≤ T →
      (∫ t in -T..T, zetaMomentCriticalNorm t^12) ≤ C*T^(2+ε) := by
  obtain ⟨C,T₀,hC,hT₀,hbound⟩ := zeta_twelfth_zero hε
  refine ⟨2*C,T₀,by positivity,hT₀,?_⟩
  intro T hT
  have hi (a b : ℝ) : IntervalIntegrable
      (fun t => zetaMomentCriticalNorm t^12) volume a b :=
    (continuous_zetaMomentCriticalNorm.pow 12).intervalIntegrable a b
  have heven : (∫ t in -T..0,zetaMomentCriticalNorm t^12) =
      ∫ t in 0..T,zetaMomentCriticalNorm t^12 := by
    have hs := intervalIntegral.integral_comp_neg
      (fun t => zetaMomentCriticalNorm t^12) (a:=(0:ℝ)) (b:=T)
    simpa only [zetaMomentCriticalNorm_neg,neg_zero] using hs.symm
  rw [← intervalIntegral.integral_add_adjacent_intervals (hi (-T) 0) (hi 0 T),heven]
  have h := hbound T hT
  nlinarith

private theorem literatureTwelfth_zeta_band_twelfth_bound {ε : ℝ} (hε : 0 < ε) :
    ∃ C T₀ : ℝ, 0 < C ∧ 1 ≤ T₀ ∧ ∀ T V : ℝ, T₀ ≤ T → 0 ≤ V →
      V^12*volume.real (bourgainZetaBand T V) ≤ C*T^(2+ε) := by
  obtain ⟨C,T₀,hC,hT₀,hbound⟩ := literatureTwelfth_zeta_twelfth_symmetric hε
  refine ⟨C,T₀,hC,hT₀,?_⟩
  intro T V hT hV
  have hi : IntegrableOn (fun t => zetaMomentCriticalNorm t^12) (Icc (-T) T) :=
    (continuous_zetaMomentCriticalNorm.pow 12).continuousOn.integrableOn_Icc
  have hc : IntegrableOn (fun _ : ℝ => V^12) (bourgainZetaBand T V) :=
    integrableOn_const (bourgainZetaBand_measure_lt_top T V).ne
  have hmass : V^12*volume.real (bourgainZetaBand T V) ≤
      ∫ t in -T..T,zetaMomentCriticalNorm t^12 := by
    rw [intervalIntegral.integral_of_le (by linarith),← integral_Icc_eq_integral_Ioc]
    calc
      _ = ∫ _ in bourgainZetaBand T V,V^12 := by simp [mul_comm]
      _ ≤ ∫ t in bourgainZetaBand T V,zetaMomentCriticalNorm t^12 :=
        setIntegral_mono_on hc (hi.mono_set (bourgainZetaBand_subset_Icc T V))
          (measurableSet_bourgainZetaBand T V) (fun t ht =>
            pow_le_pow_left₀ hV ((mem_bourgainZetaBand T V t).mp ht).2.2.1 12)
      _ ≤ _ := setIntegral_mono_set hi
        (Filter.Eventually.of_forall (fun _ => by positivity))
        (Filter.Eventually.of_forall (bourgainZetaBand_subset_Icc T V))
  exact hmass.trans (hbound T hT)

private theorem literatureTwelfth_candidate_budget {σ τ : ℝ}
    (hσ : 31/39 ≤ σ) (hσ1 : σ < 1)
    (hτlo : 4*σ/3 ≤ τ) (hτhi : τ ≤ 2*σ) :
    let χ := max 0 (τ+1-3*σ)
    max (2-2*σ+χ) (max (2*τ+4-8*σ-χ) ((40+2*τ-52*σ)/3)) ≤
      3*(1-σ)*τ/(2*σ) := by
  dsimp only
  have hσp : 0 < 2*σ := by linarith
  have h₁ : 2-2*σ+max 0 (τ+1-3*σ) ≤ 3*(1-σ)*τ/(2*σ) := by
    apply (le_div_iff₀ hσp).mpr
    by_cases hc : τ+1-3*σ ≤ 0
    · rw [max_eq_left hc]
      have hp := mul_nonneg (by linarith : 0 ≤ 1-σ) (by linarith : 0 ≤ 3*τ-4*σ)
      nlinarith
    · rw [max_eq_right (by linarith : 0 ≤ τ+1-3*σ)]
      have hp := mul_nonneg (by linarith : 0 ≤ 5*σ-3) (by linarith : 0 ≤ 2*σ-τ)
      nlinarith
  have h₂ : 2*τ+4-8*σ-max 0 (τ+1-3*σ) ≤ 2-2*σ+max 0 (τ+1-3*σ) := by
    have hc := le_max_right 0 (τ+1-3*σ)
    linarith
  have h₃ : (40+2*τ-52*σ)/3 ≤ 3*(1-σ)*τ/(2*σ) := by
    apply (le_div_iff₀ hσp).mpr
    have hp := mul_nonneg (by linarith : 0 ≤ 13*σ-9) (by linarith : 0 ≤ 2*σ-τ)
    have hq := mul_nonneg (by linarith : 0 ≤ 2*σ) (by linarith : 0 ≤ 39*σ-31)
    nlinarith
  exact max_le h₁ (max_le (h₂.trans h₁) h₃)

private theorem literatureTwelfth_candidate_scale_budgets {σ τ : ℝ}
    (hσ : 31/39 ≤ σ) (hσ1 : σ < 1)
    (hτlo : 4*σ/3 ≤ τ) (hτhi : τ ≤ 2*σ) :
    let χ := max 0 (τ+1-3*σ)
    0 ≤ χ ∧ 1 < τ-χ ∧ τ-χ < 24*σ-35/2 ∧ τ-χ < 12*σ-8 ∧
      max (2-2*σ) (τ+4-6*σ) ≤ min 1 (4-2*τ) := by
  dsimp only
  have hχ := le_max_left 0 (τ+1-3*σ)
  have hloc : τ-max 0 (τ+1-3*σ) ≤ 3*σ-1 := by
    have := le_max_right 0 (τ+1-3*σ)
    linarith
  have hmargin : 1 < τ-max 0 (τ+1-3*σ) := by
    by_cases hc : τ+1-3*σ ≤ 0
    · rw [max_eq_left hc]; linarith
    · rw [max_eq_right (by linarith : 0 ≤ τ+1-3*σ)]; linarith
  refine ⟨hχ,hmargin,by linarith,by linarith,?_⟩
  exact max_le (le_min (by linarith) (by linarith))
    (le_min (by linarith) (by linarith))


private theorem literatureTwelfth_fourth_root_young {N z : ℝ} (hN : 0 ≤ N) (hz : 0 ≤ z) :
    N^3*z ≤ N^4+z^4 := by
  rcases le_total z N with h | h
  · have hm := mul_le_mul_of_nonneg_left h (pow_nonneg hN 3)
    nlinarith only [hm,pow_nonneg hz 4]
  · have hp := pow_le_pow_left₀ hN h 3
    have hm := mul_le_mul_of_nonneg_right hp hz
    nlinarith only [hm,pow_nonneg hN 4]

private theorem literatureTwelfth_second_budget_sqrt_linear {N T R : ℝ}
    (hN : 0 < N) (hT : 0 ≤ T) (hR : 0 ≤ R) :
    Real.sqrt (bourgainSecondBudget N T R) ≤
      2*N*Real.sqrt R+(Real.sqrt N+T/N)*R := by
  rcases hR.eq_or_lt with he | hRp
  · subst R
    norm_num [bourgainSecondBudget]
  let z := R^(1/4:ℝ)*T^(1/2:ℝ)
  have hz : 0 ≤ z := by dsimp [z]; positivity
  have hz4 : z^4 = R*T^2 := by
    dsimp only [z]
    rw [mul_pow,← Real.rpow_mul_natCast hRp.le,← Real.rpow_mul_natCast hT]
    norm_num
  have hRpow : R^(5/4:ℝ) = R*R^(1/4:ℝ) := by
    rw [show (5/4:ℝ) = 1+1/4 by norm_num,Real.rpow_add hRp,Real.rpow_one]
  have hy := mul_le_mul_of_nonneg_right (literatureTwelfth_fourth_root_young hN.le hz) hRp.le
  rw [hz4] at hy
  have ht : R^(5/4:ℝ)*T^(1/2:ℝ)*N ≤ N^2*R+T^2*R^2/N^2 := by
    apply (mul_le_mul_iff_right₀ (sq_pos_of_pos hN)).mp
    have he : N^2*(N^2*R+T^2*R^2/N^2) = N^4*R+T^2*R^2 := by
      field_simp
    rw [he,hRpow]
    dsimp only [z] at hy
    nlinarith only [hy]
  let a := Real.sqrt N*R
  let b := N*Real.sqrt R
  let c := (T/N)*R
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have hb : 0 ≤ b := by dsimp [b]; positivity
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have ha2 : a^2 = N*R^2 := by
    dsimp only [a]; rw [mul_pow,Real.sq_sqrt hN.le]
  have hb2 : b^2 = N^2*R := by
    dsimp only [b]; rw [mul_pow,Real.sq_sqrt hRp.le]
  have hc2 : c^2 = T^2*R^2/N^2 := by
    dsimp only [c]; ring
  have hbudget : bourgainSecondBudget N T R ≤ a^2+2*b^2+c^2 := by
    rw [ha2,hb2,hc2]
    unfold bourgainSecondBudget
    linarith only [ht]
  have hroot : Real.sqrt (bourgainSecondBudget N T R) ≤ a+2*b+c := by
    apply Real.sqrt_le_iff.mpr
    refine ⟨by positivity,?_⟩
    nlinarith only [hbudget,sq_nonneg b,mul_nonneg ha hb,mul_nonneg ha hc,mul_nonneg hb hc]
  convert hroot using 1
  dsimp only [a,b,c]
  ring

private theorem literatureTwelfth_candidate_five_term_budget {σ τ : ℝ}
    (hσ : 31/39 ≤ σ) (hσ1 : σ < 1)
    (hτlo : 4*σ/3 ≤ τ) (hτhi : τ ≤ 2*σ) :
    let χ := max 0 (τ+1-3*σ)
    max (max (2-2*σ+χ) (max (2*τ+4-8*σ-χ) ((40+2*τ-52*σ)/3)))
      (max ((75+4*τ-2*χ-100*σ)/3) ((72+6*τ-2*χ-100*σ)/3)) ≤
      3*(1-σ)*τ/(2*σ) := by
  dsimp only
  have hmain := literatureTwelfth_candidate_budget hσ hσ1 hτlo hτhi
  have hχ := le_max_right 0 (τ+1-3*σ)
  have hc := mul_nonneg (by linarith : 0 ≤ 4*σ) (sub_nonneg.mpr hχ)
  have hσp : 0 < 2*σ := by linarith
  have h₁ : (75+4*τ-2*max 0 (τ+1-3*σ)-100*σ)/3 ≤ 3*(1-σ)*τ/(2*σ) := by
    apply (le_div_iff₀ hσp).mpr
    have hp := mul_nonneg (by linarith : 0 ≤ 13*σ-9) (by linarith : 0 ≤ 2*σ-τ)
    have hq := mul_nonneg (by linarith : 0 ≤ 2*σ) (by linarith : 0 ≤ 81*σ-64)
    nlinarith only [hc,hp,hq]
  have h₂ : (72+6*τ-2*max 0 (τ+1-3*σ)-100*σ)/3 ≤ 3*(1-σ)*τ/(2*σ) := by
    apply (le_div_iff₀ hσp).mpr
    have hp := mul_nonneg (by linarith : 0 ≤ 17*σ-9) (by linarith : 0 ≤ 2*σ-τ)
    have hq := mul_nonneg (by linarith : 0 ≤ 2*σ) (by linarith : 0 ≤ 77*σ-61)
    nlinarith only [hc,hp,hq]
  exact max_le hmain (max_le h₁ h₂)


private def literatureTwelfth_familyBandMass {ι : Type*} (A : Finset ι) (W : ι → Finset ℝ)
    (H T V : ℝ) : ℝ :=
  ∑ i ∈ A, ∑ ℓ ∈ bourgainDifferenceSupport (W i),
    (bourgainDifferenceCount (W i) ℓ:ℝ)*bourgainZetaBandMass {ℓ} H T V

private theorem literatureTwelfth_family_band_mass_bounds {ι : Type*} (A : Finset ι) (W : ι → Finset ℝ)
    {H : ℝ} (hH : 0 ≤ H) (T V : ℝ) :
    0 ≤ literatureTwelfth_familyBandMass A W H T V ∧
      literatureTwelfth_familyBandMass A W H T V ≤ 4*H*∑ i ∈ A,((W i).card:ℝ)^2 := by
  have hb (ℓ : ℤ) : 0 ≤ bourgainZetaBandMass {ℓ} H T V ∧
      bourgainZetaBandMass {ℓ} H T V ≤ 2*H := by
    simpa only [Finset.card_singleton,Nat.cast_one,mul_one] using
      bourgainZetaBandMass_bounds ({ℓ}:Finset ℤ) hH T V
  constructor
  · exact Finset.sum_nonneg (fun i _ => Finset.sum_nonneg
      (fun ℓ _ => mul_nonneg (Nat.cast_nonneg _) (hb ℓ).1))
  · have hcomp (i : ι) :
        (∑ ℓ ∈ bourgainDifferenceSupport (W i),
          (bourgainDifferenceCount (W i) ℓ:ℝ)*bourgainZetaBandMass {ℓ} H T V) ≤
            4*H*((W i).card:ℝ)^2 := by
      have hcount : (∑ ℓ ∈ bourgainDifferenceSupport (W i),
          (bourgainDifferenceCount (W i) ℓ:ℝ)) ≤ 2*((W i).card:ℝ)^2 := by
        exact_mod_cast bourgainDifferenceCount_sum_le (W i) (bourgainDifferenceSupport (W i))
      calc
        _ ≤ ∑ ℓ ∈ bourgainDifferenceSupport (W i),
            (bourgainDifferenceCount (W i) ℓ:ℝ)*(2*H) :=
          Finset.sum_le_sum (fun ℓ _ => mul_le_mul_of_nonneg_left (hb ℓ).2
            (Nat.cast_nonneg _))
        _ = (∑ ℓ ∈ bourgainDifferenceSupport (W i),
            (bourgainDifferenceCount (W i) ℓ:ℝ))*(2*H) :=
          (Finset.sum_mul _ _ _).symm
        _ ≤ (2*((W i).card:ℝ)^2)*(2*H) :=
          mul_le_mul_of_nonneg_right hcount (by positivity)
        _ = _ := by ring
    simpa only [literatureTwelfth_familyBandMass,Finset.mul_sum] using
      Finset.sum_le_sum (fun i (_hi : i ∈ A) => hcomp i)

private theorem literatureTwelfth_family_band_partition {ι : Type*} (A : Finset ι) (W : ι → Finset ℝ)
    {H T : ℝ} (hH : 0 ≤ H) {J : ℕ}
    (hrange : ∀ i ∈ A,∀ ℓ ∈ bourgainDifferenceSupport (W i),
      -T+H ≤ (ℓ:ℝ) ∧ (ℓ:ℝ) ≤ T-H)
    (hterminal : ∀ t ∈ Icc (-T) T,zetaMomentCriticalNorm t < (2:ℝ)^J) :
    (∑ i ∈ A,bourgainZetaDifferenceMoment (W i) H) ≤
      4*H*(∑ i ∈ A,((W i).card:ℝ)^2)+
        ∑ j ∈ Finset.range J,(2*(2:ℝ)^j)^2*literatureTwelfth_familyBandMass A W H T ((2:ℝ)^j) := by
  have hlocal (i : ι) (hi : i ∈ A) (ℓ : ℤ)
      (hℓ : ℓ ∈ bourgainDifferenceSupport (W i)) :
      bourgainLocalZetaSquare H ℓ ≤ 2*H+
        ∑ j ∈ Finset.range J,(2*(2:ℝ)^j)^2*
          bourgainZetaBandMass {ℓ} H T ((2:ℝ)^j) := by
    have h := bourgainZetaBand_mass_partition ({ℓ}:Finset ℤ) (a:=1) hH
      (fun m hm => by
        have he := Finset.mem_singleton.mp hm
        simpa only [he] using hrange i hi ℓ hℓ)
      (fun t ht => by simpa only [one_mul] using hterminal t ht)
    simpa only [Finset.sum_singleton,Finset.card_singleton,Nat.cast_one,
      one_pow,mul_one,one_mul] using h
  have hs := Finset.sum_le_sum (fun i hi => Finset.sum_le_sum (fun ℓ hℓ =>
    mul_le_mul_of_nonneg_left (hlocal i hi ℓ hℓ)
      (Nat.cast_nonneg (bourgainDifferenceCount (W i) ℓ))))
  have he :
      (∑ i ∈ A,∑ ℓ ∈ bourgainDifferenceSupport (W i),
        (bourgainDifferenceCount (W i) ℓ:ℝ)*(2*H+
          ∑ j ∈ Finset.range J,(2*(2:ℝ)^j)^2*
            bourgainZetaBandMass {ℓ} H T ((2:ℝ)^j))) =
      2*H*(∑ i ∈ A,∑ ℓ ∈ bourgainDifferenceSupport (W i),
        (bourgainDifferenceCount (W i) ℓ:ℝ))+
        ∑ j ∈ Finset.range J,(2*(2:ℝ)^j)^2*literatureTwelfth_familyBandMass A W H T ((2:ℝ)^j) := by
    simp only [mul_add,Finset.mul_sum,Finset.sum_add_distrib]
    congr 1
    · apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro ℓ hℓ
      ring
    · calc
        _ = ∑ i ∈ A,∑ j ∈ Finset.range J,∑ ℓ ∈ bourgainDifferenceSupport (W i),
            (bourgainDifferenceCount (W i) ℓ:ℝ)*
              ((2*(2:ℝ)^j)^2*bourgainZetaBandMass {ℓ} H T ((2:ℝ)^j)) := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [Finset.sum_comm]
        _ = ∑ j ∈ Finset.range J,∑ i ∈ A,∑ ℓ ∈ bourgainDifferenceSupport (W i),
            (bourgainDifferenceCount (W i) ℓ:ℝ)*
              ((2*(2:ℝ)^j)^2*bourgainZetaBandMass {ℓ} H T ((2:ℝ)^j)) := by
          rw [Finset.sum_comm]
        _ = _ := by
          simp only [literatureTwelfth_familyBandMass,Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro j hj
          apply Finset.sum_congr rfl
          intro i hi
          apply Finset.sum_congr rfl
          intro ℓ hℓ
          ring
  rw [he] at hs
  have hcount : (∑ i ∈ A,∑ ℓ ∈ bourgainDifferenceSupport (W i),
      (bourgainDifferenceCount (W i) ℓ:ℝ)) ≤ 2*∑ i ∈ A,((W i).card:ℝ)^2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i hi
    exact_mod_cast bourgainDifferenceCount_sum_le (W i) (bourgainDifferenceSupport (W i))
  apply hs.trans
  refine add_le_add ?_ le_rfl
  have hm := mul_le_mul_of_nonneg_left hcount (by positivity : 0 ≤ 2*H)
  convert hm using 1
  ring

private theorem literatureTwelfth_family_band_select :
    ∃ B : ℝ, 0 < B ∧ ∀ {ι : Type*} (A : Finset ι) (W : ι → Finset ℝ)
      (H T : ℝ), 0 ≤ H →
      (∀ i ∈ A,∀ ℓ ∈ bourgainDifferenceSupport (W i),
        -T+H ≤ (ℓ:ℝ) ∧ (ℓ:ℝ) ≤ T-H) →
      ∃ j ∈ Finset.range (bourgainZetaBandCount B T 1),
        (∑ i ∈ A,bourgainZetaDifferenceMoment (W i) H) ≤
          4*H*(∑ i ∈ A,((W i).card:ℝ)^2)+
            (bourgainZetaBandCount B T 1:ℝ)*(2*(2:ℝ)^j)^2*
              literatureTwelfth_familyBandMass A W H T ((2:ℝ)^j) := by
  obtain ⟨B,hB,hterminal⟩ := exists_bourgainZetaBand_terminal
  refine ⟨B,hB,?_⟩
  intro ι A W H T hH hrange
  let J := bourgainZetaBandCount B T 1
  let mass := fun j => (2*(2:ℝ)^j)^2*literatureTwelfth_familyBandMass A W H T ((2:ℝ)^j)
  obtain ⟨j,hj,hmax⟩ := Finset.exists_max_image (Finset.range J) mass
    (Finset.nonempty_range_iff.mpr (bourgainZetaBandCount_pos B T 1).ne')
  have hp := literatureTwelfth_family_band_partition A W hH hrange
    (fun t ht => by simpa only [one_mul] using hterminal T 1 (by norm_num) t ht)
  refine ⟨j,hj,hp.trans ?_⟩
  have hs : (∑ q ∈ Finset.range J,mass q) ≤ (J:ℝ)*mass j := by
    calc
      _ ≤ ∑ _q ∈ Finset.range J,mass j := Finset.sum_le_sum (fun q hq => hmax q hq)
      _ = _ := by simp
  exact add_le_add le_rfl (by simpa only [mass,mul_assoc] using hs)


private theorem literatureTwelfth_absorbed_band_bound {I K Z X A c d bandVolume Y : ℝ}
    (hI : 0 < I) (hK : 0 ≤ K) (hZ : 0 ≤ Z) (hA : 0 ≤ A)
    (hc : 0 ≤ c) (hd : 0 ≤ d) (hbandVolume : 0 ≤ bandVolume)
    (hgram : I ≤ K*Z*X) (hcap : X ≤ A*I)
    (hmixed : X ≤ c*bandVolume+d*Real.sqrt bandVolume) (hmoment : Z^6*bandVolume ≤ Y) :
    I ≤ K*(c*(K*A)^5*Y+d*(K*A)^2*Real.sqrt Y) := by
  have hprod : I ≤ (K*A*Z)*I := by
    have hh := hgram.trans (mul_le_mul_of_nonneg_left hcap (mul_nonneg hK hZ))
    convert hh using 1
    ring
  have hg : 1 ≤ K*A*Z :=
    (mul_le_mul_iff_of_pos_right hI).mp (by simpa only [one_mul] using hprod)
  have hg5 : 1 ≤ (K*A*Z)^5 := by
    simpa only [one_pow] using pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 1) hg 5
  have hg2 : 1 ≤ (K*A*Z)^2 := by
    simpa only [one_pow] using pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 1) hg 2
  have hfirst : Z*bandVolume ≤ (K*A)^5*Y := by
    calc
      _ ≤ (K*A*Z)^5*(Z*bandVolume) := by
        simpa only [one_mul] using mul_le_mul_of_nonneg_right hg5 (mul_nonneg hZ hbandVolume)
      _ = (K*A)^5*(Z^6*bandVolume) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hmoment (by positivity)
  have hsqrt : Z^3*Real.sqrt bandVolume ≤ Real.sqrt Y := by
    apply Real.le_sqrt_of_sq_le
    simpa only [mul_pow,← pow_mul,Real.sq_sqrt hbandVolume] using hmoment
  have hsecond : Z*Real.sqrt bandVolume ≤ (K*A)^2*Real.sqrt Y := by
    calc
      _ ≤ (K*A*Z)^2*(Z*Real.sqrt bandVolume) := by
        simpa only [one_mul] using mul_le_mul_of_nonneg_right hg2
          (mul_nonneg hZ (Real.sqrt_nonneg bandVolume))
      _ = (K*A)^2*(Z^3*Real.sqrt bandVolume) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hsqrt (sq_nonneg _)
  calc
    I ≤ K*Z*(c*bandVolume+d*Real.sqrt bandVolume) :=
      hgram.trans (mul_le_mul_of_nonneg_left hmixed (mul_nonneg hK hZ))
    _ = K*(c*(Z*bandVolume)+d*(Z*Real.sqrt bandVolume)) := by ring
    _ ≤ K*(c*((K*A)^5*Y)+d*((K*A)^2*Real.sqrt Y)) :=
      mul_le_mul_of_nonneg_left (add_le_add
        (mul_le_mul_of_nonneg_left hfirst hc)
        (mul_le_mul_of_nonneg_left hsecond hd)) hK
    _ = _ := by ring


private theorem literatureTwelfth_difference_count_singletons (W : Finset ℝ) (D : Finset ℤ) :
    (∑ ℓ ∈ bourgainDifferenceSupport W,(bourgainDifferenceCount W ℓ:ℝ)*
      (({ℓ} ∩ D).card:ℝ)) = ∑ ℓ ∈ D,(bourgainDifferenceCount W ℓ:ℝ) := by
  calc
    _ = ∑ ℓ ∈ (bourgainDifferenceSupport W).filter (fun ℓ => ℓ ∈ D),
        (bourgainDifferenceCount W ℓ:ℝ) := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro ℓ hℓ
      by_cases hm : ℓ ∈ D <;> simp [hm]
    _ = _ := by
      apply Finset.sum_subset
      · intro ℓ hℓ
        exact (Finset.mem_filter.mp hℓ).2
      · intro ℓ hℓ hn
        have hs : ℓ ∉ bourgainDifferenceSupport W := by
          intro hs
          exact hn (Finset.mem_filter.mpr ⟨hs,hℓ⟩)
        rw [bourgainDifferenceCount_eq_zero_of_not_mem W hs,Nat.cast_zero]

private theorem literatureTwelfth_family_band_common_shift {ι : Type*}
    (A : Finset ι) (W : ι → Finset ℝ)
    {H T V a b : ℝ} (hH : 0 < H) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hmass : a*(2*Nat.ceil H+1:ℕ)*volume.real (bourgainZetaBand T V)+
      b*Real.sqrt (2*H*(2*Nat.ceil H+1:ℕ)*volume.real (bourgainZetaBand T V)) <
        literatureTwelfth_familyBandMass A W H T V) :
    ∃ u ∈ Ioc (-H) H,(bourgainIntegerSlice H T V u).Nonempty ∧
      a*((bourgainIntegerSlice H T V u).card:ℝ)+
        b*Real.sqrt ((bourgainIntegerSlice H T V u).card:ℝ) <
          ∑ i ∈ A,∑ ℓ ∈ bourgainIntegerSlice H T V u,
            (bourgainDifferenceCount (W i) ℓ:ℝ) := by
  let E := A.sigma (fun i => bourgainDifferenceSupport (W i))
  let w := fun x : Σ _i : ι,ℤ => (bourgainDifferenceCount (W x.1) x.2:ℝ)
  let D := fun x : Σ _i : ι,ℤ => ({x.2}:Finset ℤ)
  have hm : a*(2*Nat.ceil H+1:ℕ)*volume.real (bourgainZetaBand T V)+
      b*Real.sqrt (2*H*(2*Nat.ceil H+1:ℕ)*volume.real (bourgainZetaBand T V)) <
        ∑ x ∈ E,w x*bourgainZetaBandMass (D x) H T V := by
    simpa only [E,w,D,Finset.sum_sigma,literatureTwelfth_familyBandMass] using hmass
  obtain ⟨u,hu,hne,hlower⟩ := bourgain_full_slice_common_shift E w D hH ha hb hm
  refine ⟨u,hu,hne,?_⟩
  simpa only [E,w,D,Finset.sum_sigma,literatureTwelfth_difference_count_singletons] using hlower

private theorem literatureTwelfth_physical_family_band_upper {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ K N₀ : ℝ, 0 < K ∧ 2 ≤ N₀ ∧ ∀ P : LargeValuePattern,
      N₀ ≤ P.N → ∀ σ δ : ℝ, 0 ≤ σ → δ ≤ 1 → P.N^(σ-δ) ≤ P.V →
      ∀ (L : ℝ) (hL : 0 < L), P.N ≤ L → L ≤ P.T →
      ∀ (A : Finset ℕ) (W : ℕ → Finset ℝ),
        (∀ i ∈ A,W i ⊆ (P.localized L hL i).reflectedOrdinates) →
        (∀ i ∈ A,IsSeparated 2 (W i)) → ∀ V : ℝ,
        let H := P.N^ε
        let U := L+H+1
        let bandVolume := volume.real (bourgainZetaBand U V)
        let Q := Real.sqrt (bourgainSecondBudget P.N P.T (P.ordinates.card:ℝ))
        literatureTwelfth_familyBandMass A W H U V ≤
          (K*P.N^ε*(1+2*Real.pi*P.N^ε)*P.T^ε*Q/P.V^2)*
            ((Real.sqrt P.N+P.T/P.N)*(2*Nat.ceil H+1:ℕ)*bandVolume+
              2*P.N*Real.sqrt (2*H*(2*Nat.ceil H+1:ℕ)*bandVolume)) := by
  obtain ⟨M,N₁,hM,hN₁,hlower⟩ := bourgain_subdivided_mixed_difference_counts hε
  obtain ⟨D,E₀,hD,hE₀,hupper⟩ := bourgain_physical_mixed_upper hε
  let K := 2*M*D
  refine ⟨K,max N₁ E₀,by dsimp [K]; positivity,hN₁.trans (le_max_left _ _),?_⟩
  intro P hN σ δ hσ hδ hV L hL hNL hLT A W hsub hsep V
  let H := P.N^ε
  let U := L+H+1
  let bandVolume := volume.real (bourgainZetaBand U V)
  let Q := Real.sqrt (bourgainSecondBudget P.N P.T (P.ordinates.card:ℝ))
  let coeff := K*P.N^ε*(1+2*Real.pi*P.N^ε)*P.T^ε*Q/P.V^2
  let a := coeff*(Real.sqrt P.N+P.T/P.N)
  let b := coeff*(2*P.N)
  have hNp : 0 < P.N := zero_lt_one.trans P.one_lt_N
  have hTp : 0 < P.T := P.T_pos
  have hVp : 0 < P.V := P.V_pos
  have hH : 0 < H := Real.rpow_pos_of_pos hNp ε
  have hcoeff : 0 ≤ coeff := by dsimp [coeff,K,Q]; positivity
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have hb : 0 ≤ b := by dsimp [b]; positivity
  by_contra hn
  have hmass : a*(2*Nat.ceil H+1:ℕ)*bandVolume+
      b*Real.sqrt (2*H*(2*Nat.ceil H+1:ℕ)*bandVolume) < literatureTwelfth_familyBandMass A W H U V := by
    have hh := lt_of_not_ge hn
    change coeff*((Real.sqrt P.N+P.T/P.N)*(2*Nat.ceil H+1:ℕ)*bandVolume+
      2*P.N*Real.sqrt (2*H*(2*Nat.ceil H+1:ℕ)*bandVolume)) < literatureTwelfth_familyBandMass A W H U V at hh
    convert hh using 1
    dsimp only [a,b]
    ring
  obtain ⟨u,hu,_hne,hshift⟩ := literatureTwelfth_family_band_common_shift A W hH ha hb hmass
  let S := A.biUnion (fun i => (P.localized L hL i).retainedOriginal (W i))
  let d := ((bourgainIntegerSlice H U V u).card:ℝ)
  let r := 1+2*Real.pi*P.N^ε
  have hsource : S ⊆ P.ordinates := (P.localized_retainedOriginal_union hL A W hsub).1
  have hcard : (S.card:ℝ) ≤ (P.ordinates.card:ℝ) := by
    exact_mod_cast Finset.card_le_card hsource
  have hq : Real.sqrt (bourgainSecondBudget P.N P.T (S.card:ℝ)) ≤ Q := by
    apply Real.sqrt_le_sqrt
    unfold bourgainSecondBudget
    gcongr
  have hd0 : 0 ≤ d := Nat.cast_nonneg _
  have hlinear := literatureTwelfth_second_budget_sqrt_linear hNp P.T_pos.le hd0
  have hl := hlower P ((le_max_left _ _).trans hN) σ δ hσ hδ hV L hL A W hsub hsep
    (bourgainIntegerSlice H U V u)
  have hupp : (∫ v in -r..r,∑ t ∈ S,∑ ℓ ∈ bourgainIntegerSlice H U V u,
      ‖∑ n ∈ P.indices,P.coeff n*dirichletPhase n (t-(ℓ:ℝ)+v)‖^2) ≤
      2*r*D*P.T^ε*(Real.sqrt (bourgainSecondBudget P.N P.T (S.card:ℝ))*
        Real.sqrt (bourgainSecondBudget P.N P.T d)) := by
    have hh := hupper P S hsource L (8*ε) V u r ((le_max_right _ _).trans hN)
      hNL hLT (by linarith : 8*ε ≤ 8)
      (by simpa only [show 8*ε/8 = ε by ring] using (show u ∈ Icc (-H) H from ⟨hu.1.le,hu.2⟩))
      (by dsimp [r]; positivity)
    simpa only [show 8*ε/8 = ε by ring,H,U,d] using hh
  have hprod := mul_le_mul hq hlinear (Real.sqrt_nonneg _)
    (Real.sqrt_nonneg (bourgainSecondBudget P.N P.T (P.ordinates.card:ℝ)))
  have hfin : P.V^2*(∑ i ∈ A,∑ ℓ ∈ bourgainIntegerSlice H U V u,
      (bourgainDifferenceCount (W i) ℓ:ℝ)) ≤
      K*P.N^ε*r*P.T^ε*Q*(2*P.N*Real.sqrt d+(Real.sqrt P.N+P.T/P.N)*d) := by
    have hh := hl.trans (mul_le_mul_of_nonneg_left hupp
      (by positivity : 0 ≤ M*P.N^ε))
    have hp := mul_le_mul_of_nonneg_left hprod
      (by dsimp [r]; positivity : 0 ≤ M*P.N^ε*(2*r*D*P.T^ε))
    apply hh.trans
    convert hp using 1 <;> dsimp only [K] <;> ring
  have hstrict := (mul_lt_mul_of_pos_left hshift (sq_pos_of_pos P.V_pos)).trans_le hfin
  have he : P.V^2*(a*d+b*Real.sqrt d) =
      K*P.N^ε*r*P.T^ε*Q*(2*P.N*Real.sqrt d+(Real.sqrt P.N+P.T/P.N)*d) := by
    dsimp only [a,b,coeff,r]
    field_simp [hNp.ne',hVp.ne']
    ring
  change P.V^2*(a*d+b*Real.sqrt d) < _ at hstrict
  rw [he] at hstrict
  exact (lt_irrefl _) hstrict


private theorem literatureTwelfth_localized_gram_band {σ τ ε : ℝ}
    (hσ : 3/4 < σ) (hε : 0 < ε) (hgap : 3*ε < 8*σ-6) :
    ∃ B C δ : ℝ, 0 < B ∧ 2 ≤ C ∧ 0 < δ ∧
      ∀ (P : LargeValuePattern) (L : ℝ) (hL : 0 < L),
        C ≤ P.N → P.N ≤ L → L ≤ P.N^(τ+δ) → P.N^(σ-δ) ≤ P.V →
        ∃ W : ℕ → Finset ℝ,
          (∀ i : ℕ,W i ⊆ (P.localized L hL i).reflectedOrdinates ∧
            IsSeparated 2 (W i) ∧ InBaseInterval L (W i)) ∧
          let I := Finset.range (Nat.floor (P.T/L)+1)
          let H := P.N^ε
          let U := L+H+1
          let J := bourgainZetaBandCount B U 1
          ∃ j ∈ Finset.range J,
            (∑ i ∈ I,((P.localized L hL i).ordinates.card:ℝ)^2) ≤
              4*C*(P.N^(2-2*σ+ε)+P.N^(2*τ+4-8*σ+ε))*(P.ordinates.card:ℝ)+
              8*(C*P.N^(3-4*σ+ε))^2*(J:ℝ)*((2:ℝ)^j)^2*
                literatureTwelfth_familyBandMass I W H U ((2:ℝ)^j) := by
  obtain ⟨C₀,δ,hC₀,hδ,hgram⟩ := literatureTwelfth_localized_retained_quadratic (τ:=τ) hσ hε
  obtain ⟨B,hB,hselect⟩ := literatureTwelfth_family_band_select
  let g := 8*σ-6-3*ε
  have hg : 0 < g := by dsimp [g]; linarith
  obtain ⟨N₁,hN₁⟩ := Filter.eventually_atTop.mp
    ((tendsto_rpow_atTop hg).eventually (Filter.eventually_ge_atTop (8*C₀^2)))
  let C := max 2 (max C₀ N₁)
  have hCC₀ : C₀ ≤ C := (le_max_left _ _).trans (le_max_right _ _)
  have hCN₁ : N₁ ≤ C := (le_max_right _ _).trans (le_max_right _ _)
  refine ⟨B,C,δ,hB,le_max_left _ _,hδ,?_⟩
  intro P L hL hN hNL hTu hV
  have hNp : 0 < P.N := zero_lt_one.trans P.one_lt_N
  obtain ⟨W,hW,hrec⟩ := hgram P L hL (hCC₀.trans hN) hNL hTu hV
  refine ⟨W,fun i => ⟨(hW i).1,(hW i).2.1,(hW i).2.2.1⟩,?_⟩
  let I := Finset.range (Nat.floor (P.T/L)+1)
  let H := P.N^ε
  let U := L+H+1
  let J := bourgainZetaBandCount B U 1
  let S := ∑ i ∈ I,((P.localized L hL i).ordinates.card:ℝ)^2
  let R := (P.ordinates.card:ℝ)
  let A := P.N^(2-2*σ+ε)+P.N^(2*τ+4-8*σ+ε)
  let D₀ := (C₀*P.N^(3-4*σ+ε))^2
  have hH : 0 ≤ H := Real.rpow_nonneg hNp.le ε
  have hS : 0 ≤ S := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hD₀ : 0 ≤ D₀ := sq_nonneg _
  have hsmall : 8*H*D₀ ≤ 1 := by
    have he : (8*H*D₀)*P.N^g = 8*C₀^2 := by
      dsimp only [H,D₀]
      rw [mul_pow,← Real.rpow_mul_natCast hNp.le]
      calc
        _ = 8*C₀^2*(P.N^ε*(P.N^((3-4*σ+ε)*2)*P.N^g)) := by ring_nf
        _ = 8*C₀^2*P.N^(ε+(3-4*σ+ε)*2+g) := by
          rw [Real.rpow_add hNp,Real.rpow_add hNp]
          ring
        _ = _ := by
          rw [show ε+(3-4*σ+ε)*2+g = 0 by dsimp only [g]; ring,
            Real.rpow_zero,mul_one]
    apply (mul_le_mul_iff_of_pos_right (Real.rpow_pos_of_pos hNp g)).mp
    rw [he,one_mul]
    exact hN₁ P.N (hCN₁.trans hN)
  obtain ⟨j,hj,hband⟩ := hselect I W H U hH (by
    intro i hi ℓ hℓ
    have hh := bourgainDifferenceSupport_bounds (hW i).2.2.1 hℓ
    dsimp only [U]
    constructor <;> linarith only [hh.1,hh.2])
  have hWcap : (∑ i ∈ I,((W i).card:ℝ)^2) ≤ S := by
    apply Finset.sum_le_sum
    intro i hi
    have hc : ((W i).card:ℝ) ≤ ((P.localized L hL i).ordinates.card:ℝ) := by
      exact_mod_cast (Finset.card_le_card (hW i).1).trans_eq
        (P.localized L hL i).reflectedOrdinates_card
    exact pow_le_pow_left₀ (Nat.cast_nonneg _) hc 2
  let V := (2:ℝ)^j
  let X := literatureTwelfth_familyBandMass I W H U V
  have hX : 0 ≤ X := (literatureTwelfth_family_band_mass_bounds I W hH U V).1
  have hb : (∑ i ∈ I,bourgainZetaDifferenceMoment (W i) H) ≤
      4*H*S+(J:ℝ)*(2*V)^2*X := by
    apply hband.trans
    exact add_le_add (mul_le_mul_of_nonneg_left hWcap (by positivity)) le_rfl
  change S ≤ 2*C₀*A*R+D₀*(∑ i ∈ I,bourgainZetaDifferenceMoment (W i) H) at hrec
  have hcombined := hrec.trans (add_le_add le_rfl
    (mul_le_mul_of_nonneg_left hb hD₀))
  have hcoef := mul_le_mul_of_nonneg_right hsmall hS
  have hfinal : S ≤ 4*C₀*A*R+8*D₀*(J:ℝ)*V^2*X := by
    nlinarith only [hcombined,hcoef]
  refine ⟨j,hj,?_⟩
  change S ≤ 4*C*A*R+8*(C*P.N^(3-4*σ+ε))^2*(J:ℝ)*V^2*X
  apply hfinal.trans
  dsimp only [D₀,A,R]
  gcongr


private theorem literatureTwelfth_physical_twelfth_family_estimate {σ τ ε : ℝ}
    (hσ : 3/4 < σ) (hε : 0 < ε) (hε1 : ε ≤ 1) (hgap : 3*ε < 8*σ-6) :
    ∃ B C K M δ : ℝ, 0 < B ∧ 2 ≤ C ∧ 0 < K ∧ 0 < M ∧ 0 < δ ∧ δ ≤ 1 ∧
      ∀ (P : LargeValuePattern) (L : ℝ), 0 < L →
        C ≤ P.N → P.N ≤ L → L ≤ P.T →
        L ≤ P.N^(τ+δ) → P.N^(σ-δ) ≤ P.V →
        let I := Finset.range (Nat.floor (P.T/L)+1)
        let H := P.N^ε
        let U := L+H+1
        let J := bourgainZetaBandCount B U 1
        let O := ((2*Nat.ceil H+1:ℕ):ℝ)
        let F := 16*(C*P.N^(3-4*σ+ε))^2*(J:ℝ)
        let G := F*(4*H)
        let Q := Real.sqrt (bourgainSecondBudget P.N P.T (P.ordinates.card:ℝ))
        let E := K*P.N^ε*(1+2*Real.pi*P.N^ε)*P.T^ε*Q/P.V^2
        let Y := M*U^(2+ε)
        (P.ordinates.card:ℝ)^2 ≤ (I.card:ℝ)*
          (8*C*(P.N^(2-2*σ+ε)+P.N^(2*τ+4-8*σ+ε))*(P.ordinates.card:ℝ)+
            F*E*((Real.sqrt P.N+P.T/P.N)*O*G^5*Y+
              2*P.N*Real.sqrt (2*H*O)*G^2*Real.sqrt Y)) := by
  obtain ⟨B,C₀,δ₀,hB,hC₀,hδ₀,hgram⟩ := literatureTwelfth_localized_gram_band (τ:=τ) hσ hε hgap
  obtain ⟨K,N₁,hK,hN₁,hmixed⟩ := literatureTwelfth_physical_family_band_upper hε hε1
  obtain ⟨M,T₀,hM,hT₀,hmoment⟩ := literatureTwelfth_zeta_band_twelfth_bound hε
  let C := max C₀ (max N₁ T₀)
  let δ := min δ₀ 1
  have hCC₀ : C₀ ≤ C := le_max_left _ _
  have hCN₁ : N₁ ≤ C := (le_max_left _ _).trans (le_max_right _ _)
  have hCT₀ : T₀ ≤ C := (le_max_right _ _).trans (le_max_right _ _)
  have hδ : 0 < δ := lt_min hδ₀ zero_lt_one
  have hδδ₀ : δ ≤ δ₀ := min_le_left _ _
  have hδ1 : δ ≤ 1 := min_le_right _ _
  refine ⟨B,C,K,M,δ,hB,hC₀.trans hCC₀,hK,hM,hδ,hδ1,?_⟩
  intro P L hL hN hNL hLT hTu hV
  have hNp : 0 < P.N := zero_lt_one.trans P.one_lt_N
  have hTp : 0 < P.T := P.T_pos
  have hCp : 0 < C := by linarith only [hC₀,hCC₀]
  have hTu₀ : L ≤ P.N^(τ+δ₀) := hTu.trans
    (Real.rpow_le_rpow_of_exponent_le P.one_lt_N.le (by linarith))
  have hV₀ : P.N^(σ-δ₀) ≤ P.V :=
    (Real.rpow_le_rpow_of_exponent_le P.one_lt_N.le (by linarith)).trans hV
  obtain ⟨W,hW,j,hj,hrec⟩ := hgram P L hL (hCC₀.trans hN) hNL hTu₀ hV₀
  let I := Finset.range (Nat.floor (P.T/L)+1)
  let H := P.N^ε
  let U := L+H+1
  let J := bourgainZetaBandCount B U 1
  let O : ℝ := (2*Nat.ceil H+1:ℕ)
  let F := 16*(C*P.N^(3-4*σ+ε))^2*(J:ℝ)
  let G := F*(4*H)
  let Q := Real.sqrt (bourgainSecondBudget P.N P.T (P.ordinates.card:ℝ))
  let E := K*P.N^ε*(1+2*Real.pi*P.N^ε)*P.T^ε*Q/P.V^2
  let Y := M*U^(2+ε)
  let S := ∑ i ∈ I,((P.localized L hL i).ordinates.card:ℝ)^2
  let small := 8*C*(P.N^(2-2*σ+ε)+P.N^(2*τ+4-8*σ+ε))*(P.ordinates.card:ℝ)
  let big := F*E*((Real.sqrt P.N+P.T/P.N)*O*G^5*Y+
    2*P.N*Real.sqrt (2*H*O)*G^2*Real.sqrt Y)
  let V := (2:ℝ)^j
  let bandVolume := volume.real (bourgainZetaBand U V)
  let X := literatureTwelfth_familyBandMass I W H U V
  have hH : 0 < H := Real.rpow_pos_of_pos hNp ε
  have hU : 0 < U := by dsimp [U]; positivity
  have hO : 0 ≤ O := Nat.cast_nonneg _
  have hF : 0 ≤ F := by dsimp [F]; positivity
  have hE : 0 ≤ E := by dsimp [E,Q]; positivity
  have hY : 0 ≤ Y := by dsimp [Y]; positivity
  have hbig : 0 ≤ big := by dsimp [big,G]; positivity
  have hsmall : 0 ≤ small := by dsimp [small]; positivity
  have hX : 0 ≤ X := (literatureTwelfth_family_band_mass_bounds I W hH.le U V).1
  have hWcap : (∑ i ∈ I,((W i).card:ℝ)^2) ≤ S := by
    apply Finset.sum_le_sum
    intro i hi
    have hc : ((W i).card:ℝ) ≤ ((P.localized L hL i).ordinates.card:ℝ) := by
      exact_mod_cast (Finset.card_le_card (hW i).1).trans_eq
        (P.localized L hL i).reflectedOrdinates_card
    exact pow_le_pow_left₀ (Nat.cast_nonneg _) hc 2
  have hcap : X ≤ (4*H)*S := (literatureTwelfth_family_band_mass_bounds I W hH.le U V).2.trans
    (mul_le_mul_of_nonneg_left hWcap (by positivity))
  have hrec' : S ≤ small/2+(F/2)*V^2*X := by
    change S ≤ 4*C₀*(P.N^(2-2*σ+ε)+P.N^(2*τ+4-8*σ+ε))*(P.ordinates.card:ℝ)+
      8*(C₀*P.N^(3-4*σ+ε))^2*(J:ℝ)*V^2*X at hrec
    have hh : S ≤ 4*C*(P.N^(2-2*σ+ε)+P.N^(2*τ+4-8*σ+ε))*(P.ordinates.card:ℝ)+
      8*(C*P.N^(3-4*σ+ε))^2*(J:ℝ)*V^2*X := hrec.trans (by gcongr)
    convert hh using 1
    dsimp only [small,F]
    ring
  have hmain : S ≤ small+big := by
    by_cases hs : S ≤ small
    · exact hs.trans (le_add_of_nonneg_right hbig)
    · have hS : 0 < S := hsmall.trans_lt (lt_of_not_ge hs)
      have hgram' : S ≤ F*(V^2)*X := by
        have hh := lt_of_not_ge hs
        nlinarith only [hrec',hh]
      let c := E*(Real.sqrt P.N+P.T/P.N)*O
      let d := E*(2*P.N)*Real.sqrt (2*H*O)
      have hc : 0 ≤ c := by dsimp [c]; positivity
      have hd : 0 ≤ d := by dsimp [d]; positivity
      have hmixed' : X ≤ c*bandVolume+d*Real.sqrt bandVolume := by
        have hm := hmixed P (hCN₁.trans hN) σ δ (by linarith only [hσ]) hδ1 hV
          L hL hNL hLT I W (fun i _ => (hW i).1) (fun i _ => (hW i).2.1) V
        change X ≤ E*((Real.sqrt P.N+P.T/P.N)*O*bandVolume+
          2*P.N*Real.sqrt ((2*H*O)*bandVolume)) at hm
        rw [Real.sqrt_mul (by positivity : 0 ≤ 2*H*O)] at hm
        convert hm using 1
        dsimp only [c,d]
        ring
      have hmoment' : (V^2)^6*bandVolume ≤ Y := by
        have hT : T₀ ≤ U := by
          have ht := (hCT₀.trans hN).trans hNL
          dsimp only [U]
          linarith only [ht,hH]
        simpa only [← pow_mul] using hmoment U V hT (by dsimp [V]; positivity)
      have hh := literatureTwelfth_absorbed_band_bound hS hF (sq_nonneg V) (by positivity : 0 ≤ 4*H)
        hc hd (measureReal_nonneg) hgram' hcap hmixed' hmoment'
      have hbigbound : S ≤ big := by
        convert hh using 1
        dsimp only [big,c,d,G]
        ring
      exact hbigbound.trans (le_add_of_nonneg_left hsmall)
  have hglobal := literatureTwelfth_localized_square_mass P hL
  change (P.ordinates.card:ℝ)^2 ≤ (I.card:ℝ)*(small+big)
  exact hglobal.trans (mul_le_mul_of_nonneg_left hmain (Nat.cast_nonneg _))


private theorem literatureTwelfth_physical_factor_log_bounds (P : LargeValuePattern) {L C K M σ u τ δ ε : ℝ}
    {J : ℕ} (hC : 0 < C) (hK : 0 < K) (hM : 0 < M)
    (hR : P.ordinates.Nonempty) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hδ : 0 ≤ δ) (hδε : δ ≤ ε) (huτ : u ≤ τ)
    (hNL : P.N ≤ L) (hL : L ≤ P.N^(u+δ))
    (hT : P.T ≤ P.N^(τ+δ)) (hV : P.N^(σ-δ) ≤ P.V)
    (hJ : 0 < J) (hlogJ : Real.logb P.N (J:ℝ) ≤ 2*ε)
    (hlogC : Real.logb P.N C ≤ ε) (hlogK : Real.logb P.N K ≤ ε)
    (hlogM : Real.logb P.N M ≤ ε) (hlog100 : Real.logb P.N 100 ≤ ε) :
    let H := P.N^ε
    let U := L+H+1
    let O := ((2*Nat.ceil H+1:ℕ):ℝ)
    let F := 16*(C*P.N^(3-4*σ+ε))^2*(J:ℝ)
    let G := F*(4*H)
    let Q := Real.sqrt (bourgainSecondBudget P.N P.T (P.ordinates.card:ℝ))
    let E := K*P.N^ε*(1+2*Real.pi*P.N^ε)*P.T^ε*Q/P.V^2
    let Y := M*U^(2+ε)
    Real.logb P.N F ≤ 6-8*σ+7*ε ∧
      Real.logb P.N G ≤ 6-8*σ+9*ε ∧
      Real.logb P.N E ≤
        heathBrownDoubleZetaExponent τ (Real.logb P.N (P.ordinates.card:ℝ))/2-
          2*σ+(τ+10)*ε ∧
      Real.logb P.N Y ≤ 2*u+(τ+7)*ε ∧
      Real.logb P.N O ≤ 2*ε ∧
      Real.logb P.N (Real.sqrt P.N+P.T/P.N) ≤ max (1/2) (τ-1)+2*ε ∧
      Real.logb P.N (Real.sqrt (2*H*O)) ≤ 2*ε := by
  have hN := P.one_lt_N
  have hNp : 0 < P.N := zero_lt_one.trans hN
  have hTp : 0 < P.T := P.T_pos
  have hVp : 0 < P.V := P.V_pos
  have hLp : 0 < L := hNp.trans_le hNL
  have hRp : (0:ℝ) < P.ordinates.card := by exact_mod_cast hR.card_pos
  have hJp : (0:ℝ) < J := by exact_mod_cast hJ
  let H := P.N^ε
  let U := L+H+1
  let O : ℝ := (2*Nat.ceil H+1:ℕ)
  let F := 16*(C*P.N^(3-4*σ+ε))^2*(J:ℝ)
  let G := F*(4*H)
  let Q := Real.sqrt (bourgainSecondBudget P.N P.T (P.ordinates.card:ℝ))
  let E := K*P.N^ε*(1+2*Real.pi*P.N^ε)*P.T^ε*Q/P.V^2
  let Y := M*U^(2+ε)
  have hH : 0 < H := Real.rpow_pos_of_pos hNp ε
  have hH1 : 1 ≤ H := Real.one_le_rpow hN.le hε.le
  have hHN : H ≤ P.N := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hN.le hε1
  have hU : 0 < U := by dsimp [U]; positivity
  have hO : 0 < O := by dsimp [O]; positivity
  have hF : 0 < F := by dsimp [F]; positivity
  have hbudget := bourgainSecondBudget_pos hNp hTp.le hRp
  have hQ : 0 < Q := Real.sqrt_pos.mpr hbudget
  have hconst (a : ℝ) (ha : 0 < a) (ha100 : a ≤ 100) :
      Real.logb P.N a ≤ ε :=
    (Real.logb_le_logb_of_le hN ha ha100).trans hlog100
  have hlogH : Real.logb P.N H = ε := Real.logb_rpow hNp hN.ne'
  have hlogT : Real.logb P.N P.T ≤ τ+δ :=
    (Real.logb_le_iff_le_rpow hN hTp).mpr hT
  have hlogL : Real.logb P.N L ≤ u+δ :=
    (Real.logb_le_iff_le_rpow hN hLp).mpr hL
  have hlogV : σ-δ ≤ Real.logb P.N P.V :=
    (Real.le_logb_iff_rpow_le hN hVp).mpr hV
  have hlogO : Real.logb P.N O ≤ 2*ε := by
    have hceil := Nat.ceil_lt_add_one hH.le
    have hOcap : O ≤ 5*H := by
      dsimp only [O]
      push_cast
      linarith only [hceil,hH1]
    have hh := Real.logb_le_logb_of_le hN hO hOcap
    rw [Real.logb_mul (by norm_num : (5:ℝ) ≠ 0) hH.ne',hlogH] at hh
    linarith only [hh,hconst 5 (by norm_num) (by norm_num)]
  have hlogF : Real.logb P.N F ≤ 6-8*σ+7*ε := by
    dsimp only [F]
    rw [Real.logb_mul (by positivity) hJp.ne',
      Real.logb_mul (by norm_num : (16:ℝ) ≠ 0) (by positivity),Real.logb_pow,
      Real.logb_mul hC.ne' (Real.rpow_pos_of_pos hNp _).ne',
      Real.logb_rpow hNp hN.ne']
    norm_num only [Nat.cast_ofNat]
    linarith only [hlogC,hlogJ,hconst 16 (by norm_num) (by norm_num)]
  have hlogG : Real.logb P.N G ≤ 6-8*σ+9*ε := by
    dsimp only [G]
    rw [Real.logb_mul hF.ne' (by positivity),
      Real.logb_mul (by norm_num : (4:ℝ) ≠ 0) hH.ne',hlogH]
    linarith only [hlogF,hconst 4 (by norm_num) (by norm_num)]
  have hlogQ : Real.logb P.N Q ≤
      heathBrownDoubleZetaExponent τ (Real.logb P.N (P.ordinates.card:ℝ))/2+ε := by
    have hb := bourgain_budget_log_bound hN hTp.le hRp hT
    have hd := bourgain_doubleZeta_height_slack (τ:=τ)
      (r:=Real.logb P.N (P.ordinates.card:ℝ)) hδ
    dsimp only [Q]
    rw [Real.sqrt_eq_rpow,Real.logb_rpow_eq_mul_logb_of_pos hbudget]
    linarith only [hb,hd,hδε,hε,hconst 3 (by norm_num) (by norm_num)]
  have hlogr : Real.logb P.N (1+2*Real.pi*P.N^ε) ≤ 2*ε := by
    have hp : 0 < 1+2*Real.pi*P.N^ε := by positivity
    have hb : 1+2*Real.pi*P.N^ε ≤ (1+2*Real.pi)*P.N^ε := by
      change 1+2*Real.pi*H ≤ (1+2*Real.pi)*H
      nlinarith only [hH1]
    have hh := Real.logb_le_logb_of_le hN hp hb
    rw [Real.logb_mul (by positivity) (Real.rpow_pos_of_pos hNp ε).ne',
      Real.logb_rpow hNp hN.ne'] at hh
    have hc := hconst (1+2*Real.pi) (by positivity)
      (by linarith only [Real.pi_lt_four])
    linarith only [hh,hc]
  have hlogE : Real.logb P.N E ≤
      heathBrownDoubleZetaExponent τ (Real.logb P.N (P.ordinates.card:ℝ))/2-
        2*σ+(τ+10)*ε := by
    dsimp only [E]
    rw [Real.logb_div (by positivity) (by positivity),Real.logb_pow,
      Real.logb_mul (by positivity) hQ.ne',
      Real.logb_mul (by positivity) (Real.rpow_pos_of_pos hTp ε).ne',
      Real.logb_mul (by positivity) (by positivity),
      Real.logb_mul hK.ne' (Real.rpow_pos_of_pos hNp ε).ne',
      Real.logb_rpow hNp hN.ne',Real.logb_rpow_eq_mul_logb_of_pos hTp]
    norm_num only [Nat.cast_ofNat]
    have ht := mul_le_mul_of_nonneg_left hlogT hε.le
    have he := mul_nonneg hε.le (sub_nonneg.mpr hε1)
    nlinarith only [hlogK,hlogr,hlogQ,hlogV,ht,he,hδε,hε]
  have hlogY : Real.logb P.N Y ≤ 2*u+(τ+7)*ε := by
    have hUcap : U ≤ 3*L := by dsimp only [U]; linarith only [hHN,hNL,hN]
    have hh := Real.logb_le_logb_of_le hN hU hUcap
    rw [Real.logb_mul (by norm_num : (3:ℝ) ≠ 0) hLp.ne'] at hh
    have hlogU : Real.logb P.N U ≤ ε+u+δ := by
      linarith only [hh,hlogL,hconst 3 (by norm_num) (by norm_num)]
    dsimp only [Y]
    rw [Real.logb_mul hM.ne' (Real.rpow_pos_of_pos hU _).ne',
      Real.logb_rpow_eq_mul_logb_of_pos hU]
    have hm := mul_le_mul_of_nonneg_left hlogU (by positivity : 0 ≤ 2+ε)
    have hd := mul_le_mul_of_nonneg_left hδε (by positivity : 0 ≤ 2+ε)
    have hu := mul_le_mul_of_nonneg_left huτ hε.le
    have he := mul_nonneg hε.le (sub_nonneg.mpr hε1)
    nlinarith only [hlogM,hm,hd,hu,he]
  have hplus : Real.logb P.N (Real.sqrt P.N+P.T/P.N) ≤ max (1/2) (τ-1)+2*ε := by
    let z := max (1/2:ℝ) (τ-1)+δ
    have hn : Real.sqrt P.N ≤ P.N^z := by
      rw [Real.sqrt_eq_rpow]
      apply Real.rpow_le_rpow_of_exponent_le hN.le
      dsimp only [z]
      linarith only [le_max_left (1/2:ℝ) (τ-1),hδ]
    have ht : P.T/P.N ≤ P.N^z := by
      calc
        _ ≤ P.N^(τ+δ)/P.N := div_le_div_of_nonneg_right hT hNp.le
        _ = P.N^(τ+δ-1) := by rw [Real.rpow_sub hNp,Real.rpow_one]
        _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hN.le (by
          dsimp only [z]
          linarith only [le_max_right (1/2:ℝ) (τ-1)])
    have hh := Real.logb_le_logb_of_le hN (by positivity : 0 < Real.sqrt P.N+P.T/P.N)
      (show Real.sqrt P.N+P.T/P.N ≤ 2*P.N^z by linarith only [hn,ht])
    rw [Real.logb_mul (by norm_num : (2:ℝ) ≠ 0) (Real.rpow_pos_of_pos hNp z).ne',
      Real.logb_rpow hNp hN.ne'] at hh
    dsimp only [z] at hh
    linarith only [hh,hδε,hconst 2 (by norm_num) (by norm_num)]
  have hsqrt : Real.logb P.N (Real.sqrt (2*H*O)) ≤ 2*ε := by
    rw [Real.sqrt_eq_rpow,Real.logb_rpow_eq_mul_logb_of_pos (by positivity : 0 < 2*H*O),
      Real.logb_mul (by positivity) hO.ne',
      Real.logb_mul (by norm_num : (2:ℝ) ≠ 0) hH.ne',hlogH]
    linarith only [hlogO,hconst 2 (by norm_num) (by norm_num)]
  exact ⟨hlogF,hlogG,hlogE,hlogY,hlogO,hplus,hsqrt⟩


private theorem literatureTwelfth_finite_logarithmic_comparison (P : LargeValuePattern)
    {L B C K M σ u τ χ δ ε : ℝ}
    (hC : 0 < C) (hK : 0 < K) (hM : 0 < M)
    (hR : P.ordinates.Nonempty) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hτ : 0 ≤ τ) (hδ : 0 ≤ δ) (hδε : δ ≤ ε) (huτ : u ≤ τ)
    (hNL : P.N ≤ L) (hL : L ≤ P.N^(u+δ))
    (hT : P.T ≤ P.N^(τ+δ)) (hV : P.N^(σ-δ) ≤ P.V)
    (hlogJ : Real.logb P.N
      (bourgainZetaBandCount B (L+P.N^ε+1) 1:ℝ) ≤ 2*ε)
    (hlogC : Real.logb P.N C ≤ ε) (hlogK : Real.logb P.N K ≤ ε)
    (hlogM : Real.logb P.N M ≤ ε) (hlog100 : Real.logb P.N 100 ≤ ε)
    (hbin : ((Finset.range (Nat.floor (P.T/L)+1)).card:ℝ) ≤ 2*P.N^χ)
    (hfinite :
      let I := Finset.range (Nat.floor (P.T/L)+1)
      let H := P.N^ε
      let U := L+H+1
      let J := bourgainZetaBandCount B U 1
      let O := ((2*Nat.ceil H+1:ℕ):ℝ)
      let F := 16*(C*P.N^(3-4*σ+ε))^2*(J:ℝ)
      let G := F*(4*H)
      let Q := Real.sqrt (bourgainSecondBudget P.N P.T (P.ordinates.card:ℝ))
      let E := K*P.N^ε*(1+2*Real.pi*P.N^ε)*P.T^ε*Q/P.V^2
      let Y := M*U^(2+ε)
      (P.ordinates.card:ℝ)^2 ≤ (I.card:ℝ)*
        (8*C*(P.N^(2-2*σ+ε)+P.N^(2*u+4-8*σ+ε))*(P.ordinates.card:ℝ)+
          F*E*((Real.sqrt P.N+P.T/P.N)*O*G^5*Y+
            2*P.N*Real.sqrt (2*H*O)*G^2*Real.sqrt Y))) :
    let r := Real.logb P.N (P.ordinates.card:ℝ)
    let g := heathBrownDoubleZetaExponent τ r/2
    2*r ≤ χ+
      max (max (2-2*σ+r) (2*u+4-8*σ+r))
        (max (36-50*σ+g+max (1/2) (τ-1)+2*u) (19-26*σ+g+u))+
      (80+3*τ)*ε := by
  have hN := P.one_lt_N
  have hNp : 0 < P.N := zero_lt_one.trans hN
  have hTp : 0 < P.T := P.T_pos
  have hVp : 0 < P.V := P.V_pos
  have hLp : 0 < L := hNp.trans_le hNL
  have hRp : (0:ℝ) < P.ordinates.card := by exact_mod_cast hR.card_pos
  let I := Finset.range (Nat.floor (P.T/L)+1)
  let H := P.N^ε
  let U := L+H+1
  let J := bourgainZetaBandCount B U 1
  let O : ℝ := (2*Nat.ceil H+1:ℕ)
  let F := 16*(C*P.N^(3-4*σ+ε))^2*(J:ℝ)
  let G := F*(4*H)
  let Q := Real.sqrt (bourgainSecondBudget P.N P.T (P.ordinates.card:ℝ))
  let E := K*P.N^ε*(1+2*Real.pi*P.N^ε)*P.T^ε*Q/P.V^2
  let Y := M*U^(2+ε)
  let r := Real.logb P.N (P.ordinates.card:ℝ)
  let g := heathBrownDoubleZetaExponent τ r/2
  let profile := max (max (2-2*σ+r) (2*u+4-8*σ+r))
    (max (36-50*σ+g+max (1/2) (τ-1)+2*u) (19-26*σ+g+u))
  let loss := (75+2*τ)*ε
  have hH : 0 < H := Real.rpow_pos_of_pos hNp ε
  have hU : 0 < U := by dsimp [U]; positivity
  have hJ : 0 < J := bourgainZetaBandCount_pos B U 1
  have hJp : (0:ℝ) < J := by exact_mod_cast hJ
  have hO : 0 < O := by dsimp [O]; positivity
  have hF : 0 < F := by dsimp [F]; positivity
  have hG : 0 < G := by dsimp [G]; positivity
  have hQ : 0 < Q := Real.sqrt_pos.mpr (bourgainSecondBudget_pos hNp hTp.le hRp)
  have hE : 0 < E := by dsimp [E]; positivity
  have hY : 0 < Y := by dsimp [Y]; positivity
  have hplus : 0 < Real.sqrt P.N+P.T/P.N := by positivity
  have hroot : 0 < Real.sqrt (2*H*O) := by positivity
  obtain ⟨hf,hg,he,hy,ho,hpluslog,hsqrt⟩ :=
    literatureTwelfth_physical_factor_log_bounds P hC hK hM hR hε hε1 hδ hδε huτ hNL hL hT hV
      hJ hlogJ hlogC hlogK hlogM hlog100
  change Real.logb P.N F ≤ 6-8*σ+7*ε at hf
  change Real.logb P.N G ≤ 6-8*σ+9*ε at hg
  change Real.logb P.N E ≤ g-2*σ+(τ+10)*ε at he
  change Real.logb P.N Y ≤ 2*u+(τ+7)*ε at hy
  change Real.logb P.N O ≤ 2*ε at ho
  change Real.logb P.N (Real.sqrt (2*H*O)) ≤ 2*ε at hsqrt
  have hconst (a : ℝ) (ha : 0 < a) (ha100 : a ≤ 100) :
      Real.logb P.N a ≤ ε :=
    (Real.logb_le_logb_of_le hN ha ha100).trans hlog100
  let a := 8*C*(P.N^(2-2*σ+ε)+P.N^(2*u+4-8*σ+ε))*(P.ordinates.card:ℝ)
  let b := F*E*((Real.sqrt P.N+P.T/P.N)*O*G^5*Y)
  let c := F*E*(2*P.N*Real.sqrt (2*H*O)*G^2*Real.sqrt Y)
  have ha : 0 < a := by dsimp [a]; positivity
  have hb : 0 < b := by dsimp [b]; positivity
  have hc : 0 < c := by dsimp [c]; positivity
  have hpa : max (2-2*σ+r) (2*u+4-8*σ+r) ≤ profile := le_max_left _ _
  have hpb : 36-50*σ+g+max (1/2) (τ-1)+2*u ≤ profile :=
    (le_max_left _ _).trans (le_max_right _ _)
  have hpc : 19-26*σ+g+u ≤ profile := (le_max_right _ _).trans (le_max_right _ _)
  have hτε := mul_nonneg hτ hε.le
  have halog : Real.logb P.N a ≤ profile+loss := by
    have hp := bourgain_logb_two_power_sum hN
      (by norm_num : (0:ℝ) < 1) (by norm_num : (0:ℝ) < 1)
      (2-2*σ+ε) (2*u+4-8*σ+ε)
    simp only [one_mul,show (1:ℝ)+1 = 2 by norm_num] at hp
    have hm : max (2-2*σ+ε) (2*u+4-8*σ+ε) ≤
        max (2-2*σ+r) (2*u+4-8*σ+r)-r+ε := by
      exact max_le
        (by linarith only [le_max_left (2-2*σ+r) (2*u+4-8*σ+r)])
        (by linarith only [le_max_right (2-2*σ+r) (2*u+4-8*σ+r)])
    dsimp only [a,loss]
    rw [Real.logb_mul (by positivity) hRp.ne',
      Real.logb_mul (by positivity) (by positivity),
      Real.logb_mul (by norm_num : (8:ℝ) ≠ 0) hC.ne']
    change Real.logb P.N 8+Real.logb P.N C+
      Real.logb P.N (P.N^(2-2*σ+ε)+P.N^(2*u+4-8*σ+ε))+r ≤ _
    nlinarith only [hp,hm,hpa,hlogC,hconst 8 (by norm_num) (by norm_num),
      hconst 2 (by norm_num) (by norm_num),hε,hτε]
  have hblog : Real.logb P.N b ≤ profile+loss := by
    dsimp only [b,loss]
    rw [Real.logb_mul (by positivity) (by positivity),Real.logb_mul hF.ne' hE.ne',
      Real.logb_mul (by positivity) hY.ne',
      Real.logb_mul (x:=(Real.sqrt P.N+P.T/P.N)*O) (y:=G^5) (by positivity) (by positivity),
      Real.logb_mul hplus.ne' hO.ne',Real.logb_pow]
    norm_num only [Nat.cast_ofNat]
    nlinarith only [hf,he,hpluslog,ho,hg,hy,hpb,hε]
  have hclog : Real.logb P.N c ≤ profile+loss := by
    dsimp only [c,loss]
    rw [Real.logb_mul (by positivity) (by positivity),Real.logb_mul hF.ne' hE.ne',
      Real.logb_mul (x:=2*P.N*Real.sqrt (2*H*O)*G^2) (y:=Real.sqrt Y) (by positivity) (by positivity),
      Real.logb_mul (x:=2*P.N*Real.sqrt (2*H*O)) (y:=G^2) (by positivity) (by positivity),
      Real.logb_mul (by positivity) hroot.ne',
      Real.logb_mul (by norm_num : (2:ℝ) ≠ 0) hNp.ne',
      Real.logb_pow,Real.logb_self_eq_one hN,
      Real.sqrt_eq_rpow (x:=Y),Real.logb_rpow_eq_mul_logb_of_pos hY]
    norm_num only [Nat.cast_ofNat]
    nlinarith only [hf,he,hsqrt,hg,hy,hpc,hconst 2 (by norm_num) (by norm_num),hε,hτε]
  have habc : a+b+c ≤ 3*P.N^(profile+loss) := by
    have ha' := (Real.logb_le_iff_le_rpow hN ha).mp halog
    have hb' := (Real.logb_le_iff_le_rpow hN hb).mp hblog
    have hc' := (Real.logb_le_iff_le_rpow hN hc).mp hclog
    linarith only [ha',hb',hc']
  have hcore : (P.ordinates.card:ℝ)^2 ≤ (I.card:ℝ)*(a+b+c) := by
    convert hfinite using 1
    dsimp only [a,b,c]
    ring
  have hpower : (P.ordinates.card:ℝ)^2 ≤ 6*P.N^(χ+profile+loss) := by
    calc
      _ ≤ (I.card:ℝ)*(a+b+c) := hcore
      _ ≤ (2*P.N^χ)*(3*P.N^(profile+loss)) :=
        mul_le_mul hbin habc (by positivity) (by positivity)
      _ = _ := by rw [Real.rpow_add hNp,Real.rpow_add hNp,Real.rpow_add hNp]; ring
  have hh := Real.logb_le_logb_of_le hN (sq_pos_of_pos hRp) hpower
  rw [Real.logb_pow,Real.logb_mul (by norm_num : (6:ℝ) ≠ 0)
    (Real.rpow_pos_of_pos hNp _).ne',Real.logb_rpow hNp hN.ne'] at hh
  norm_num only [Nat.cast_ofNat] at hh
  change 2*r ≤ χ+profile+(80+3*τ)*ε
  change 2*r ≤ Real.logb P.N 6+(χ+profile+loss) at hh
  dsimp only [loss] at hh
  nlinarith only [hh,hconst 6 (by norm_num) (by norm_num),hε,hτε]


private theorem literatureTwelfth_actual_uniform_logarithmic_comparison {σ τ χ ε : ℝ}
    (hσ : 3/4 < σ) (hχ : 0 ≤ χ) (hmargin : 1 < τ-χ)
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hgap : 3*ε < 8*σ-6) :
    ∃ δ N₀ : ℝ, 0 < δ ∧ δ ≤ ε ∧ 2 ≤ N₀ ∧
      ∀ P : LargeValuePattern, P.ordinates.Nonempty → N₀ ≤ P.N →
        P.N^(τ-δ) ≤ P.T → P.T ≤ P.N^(τ+δ) → P.N^(σ-δ) ≤ P.V →
        let r := Real.logb P.N (P.ordinates.card:ℝ)
        let g := heathBrownDoubleZetaExponent τ r/2
        2*r ≤ χ+
          max (max (2-2*σ+r) (2*(τ-χ)+4-8*σ+r))
            (max (36-50*σ+g+max (1/2) (τ-1)+2*(τ-χ))
              (19-26*σ+g+(τ-χ)))+(80+3*τ)*ε := by
  obtain ⟨B,C,K,M,δ₀,hB,hC,hK,hM,hδ₀,hδ₀1,hfinite⟩ :=
    literatureTwelfth_physical_twelfth_family_estimate (τ:=τ-χ) hσ hε hε1 hgap
  have hτ : 0 ≤ τ := by linarith only [hχ,hmargin]
  obtain ⟨D,Nj,hD,hNj,hbands⟩ :=
    bourgainZetaBandCount_uniform_power (A:=0) (u:=τ+1) hB le_rfl
      (by linarith only [hτ]) hε
  let A := max 100 (max C (max K (max M D)))
  let N₀ := max C (max Nj (Real.exp (|Real.log A|/ε+1)))
  let δ := min δ₀ (min ε ((τ-χ-1)/2))
  have hAp : 0 < A := (by norm_num : (0:ℝ) < 100).trans_le (le_max_left _ _)
  have hCA : C ≤ A := (le_max_left _ _).trans (le_max_right _ _)
  have hKA : K ≤ A := (le_max_left _ _).trans
    ((le_max_right _ _).trans (le_max_right _ _))
  have hMA : M ≤ A := (le_max_left _ _).trans
    ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _)))
  have hDA : D ≤ A := (le_max_right _ _).trans
    ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _)))
  have hδ : 0 < δ := lt_min hδ₀ (lt_min hε (by linarith only [hmargin]))
  have hδδ₀ : δ ≤ δ₀ := min_le_left _ _
  have hδε : δ ≤ ε := (min_le_right _ _).trans (min_le_left _ _)
  have hδmargin : 1+δ ≤ τ-χ := by
    have hh : δ ≤ (τ-χ-1)/2 := (min_le_right _ _).trans (min_le_right _ _)
    linarith only [hh,hmargin]
  have hδ1 : δ ≤ 1 := hδδ₀.trans hδ₀1
  refine ⟨δ,N₀,hδ,hδε,hC.trans (le_max_left _ _),?_⟩
  intro P hR hN₀ hTlo hThi hV
  have hN := P.one_lt_N
  have hNp : 0 < P.N := zero_lt_one.trans hN
  have hCN : C ≤ P.N := (le_max_left _ _).trans hN₀
  have hNjN : Nj ≤ P.N := ((le_max_left _ _).trans (le_max_right _ _)).trans hN₀
  have hscale : Real.exp (|Real.log A|/ε+1) ≤ P.N :=
    ((le_max_right _ _).trans (le_max_right _ _)).trans hN₀
  have hlogA : Real.logb P.N A ≤ ε :=
    (le_abs_self _).trans (bourgain_abs_logb_le_of_threshold hN hε hscale)
  have hlog (a : ℝ) (ha : 0 < a) (haA : a ≤ A) : Real.logb P.N a ≤ ε :=
    (Real.logb_le_logb_of_le hN ha haA).trans hlogA
  let L := P.T/P.N^χ
  obtain ⟨hLp,hNL,hLT,_hLlo,hLhi⟩ :=
    bourgain_subdivision_physical_scales hN hχ hδmargin hTlo hThi
  change 0 < L at hLp
  change P.N ≤ L at hNL
  change L ≤ P.T at hLT
  change L ≤ P.N^((τ-χ)+δ) at hLhi
  have hLhi₀ : L ≤ P.N^((τ-χ)+δ₀) := hLhi.trans
    (Real.rpow_le_rpow_of_exponent_le hN.le (by linarith only [hδδ₀]))
  have hV₀ : P.N^(σ-δ₀) ≤ P.V :=
    (Real.rpow_le_rpow_of_exponent_le hN.le (by linarith only [hδδ₀])).trans hV
  have hf := hfinite P L hLp hCN hNL hLT hLhi₀ hV₀
  have hH : 0 < P.N^ε := Real.rpow_pos_of_pos hNp ε
  have hHN : P.N^ε ≤ P.N := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hN.le hε1
  have hU : 0 < L+P.N^ε+1 := by positivity
  have hUcap : L+P.N^ε+1 ≤ 3*P.N^(τ+1) := by
    have hLcap : L ≤ P.N^(τ+1) := hLhi.trans
      (Real.rpow_le_rpow_of_exponent_le hN.le (by linarith only [hχ,hδ1]))
    linarith only [hHN,hNL,hN,hLcap]
  have hJcap : (bourgainZetaBandCount B (L+P.N^ε+1) 1:ℝ) ≤ D*P.N^ε := by
    simpa only [neg_zero,Real.rpow_zero] using
      hbands P.N (L+P.N^ε+1) hNjN hU.le hUcap
  have hJpos : (0:ℝ) < bourgainZetaBandCount B (L+P.N^ε+1) 1 := by
    exact_mod_cast bourgainZetaBandCount_pos B (L+P.N^ε+1) 1
  have hlogJ : Real.logb P.N (bourgainZetaBandCount B (L+P.N^ε+1) 1:ℝ) ≤ 2*ε := by
    have hh := Real.logb_le_logb_of_le hN hJpos hJcap
    rw [Real.logb_mul (by linarith only [hD] : D ≠ 0) hH.ne',
      Real.logb_rpow hNp hN.ne'] at hh
    linarith only [hh,hlog D (by linarith only [hD]) hDA]
  exact literatureTwelfth_finite_logarithmic_comparison P
    (by linarith only [hC]) hK hM hR hε hε1 hτ hδ.le hδε
    (by linarith only [hχ]) hNL hLhi hThi hV hlogJ
    (hlog C (by linarith only [hC]) hCA) (hlog K hK hKA) (hlog M hM hMA)
    (hlog 100 (by norm_num) (le_max_left _ _))
    (bourgain_subdivision_bin_count hN.le P.T_pos hχ) hf


private theorem literatureTwelfth_region_zero_loss_comparison {σ τ χ ρ energy : ℝ}
    (hregion : InCardinalityEnergyRegion σ τ ρ energy)
    (hσ : 3/4 < σ) (hχ : 0 ≤ χ) (hmargin : 1 < τ-χ) :
    let g := heathBrownDoubleZetaExponent τ ρ/2
    2*ρ ≤ χ+
      max (max (2-2*σ+ρ) (2*(τ-χ)+4-8*σ+ρ))
        (max (36-50*σ+g+max (1/2) (τ-1)+2*(τ-χ))
          (19-26*σ+g+(τ-χ))) := by
  let ε : ℕ → ℝ := fun n => min (poweringAccuracy n) ((8*σ-6)/6)
  have hε (n : ℕ) : 0 < ε n :=
    lt_min (poweringAccuracy_pos n) (by linarith only [hσ])
  have hεa (n : ℕ) : ε n ≤ poweringAccuracy n := min_le_left _ _
  have hε1 (n : ℕ) : ε n ≤ 1 :=
    (hεa n).trans ((poweringAccuracy_le n).trans (by norm_num))
  have hgap (n : ℕ) : 3*ε n < 8*σ-6 := by
    have hh : ε n ≤ (8*σ-6)/6 := min_le_right _ _
    linarith only [hh,hσ]
  have hεlim : Filter.Tendsto ε Filter.atTop (nhds 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds poweringAccuracy_tendsto
      (fun n => (hε n).le) hεa
  have hex (n : ℕ) := literatureTwelfth_actual_uniform_logarithmic_comparison
    hσ hχ hmargin (hε n) (hε1 n) (hgap n)
  choose δ N₀ hδ _hδε _hN₀ hf using hex
  obtain ⟨P,_hNtop,hr,hP⟩ := exists_bourgain_region_family hregion δ N₀ hδ
  let b : ℝ → ℝ := fun r =>
    let g := heathBrownDoubleZetaExponent τ r/2
    χ+max (max (2-2*σ+r) (2*(τ-χ)+4-8*σ+r))
      (max (36-50*σ+g+max (1/2) (τ-1)+2*(τ-χ))
        (19-26*σ+g+(τ-χ)))
  have hb : Continuous b := by
    dsimp only [b]
    unfold heathBrownDoubleZetaExponent
    fun_prop
  have hright : Filter.Tendsto
      (fun n => b (Real.logb (P n).N ((P n).ordinates.card:ℝ))+(80+3*τ)*ε n)
      Filter.atTop (nhds (b ρ)) := by
    simpa only [mul_zero,add_zero] using
      ((hb.tendsto ρ).comp hr).add (hεlim.const_mul (80+3*τ))
  exact le_of_tendsto_of_tendsto (hr.const_mul 2) hright
    (Filter.Eventually.of_forall (fun n =>
      hf n (P n) (hP n).2.2.2.2.2.1 (hP n).2.1
        (hP n).2.2.1 (hP n).2.2.2.1 (hP n).2.2.2.2.1))

private theorem literatureTwelfth_region_cardinality {σ τ ρ energy : ℝ}
    (hregion : InCardinalityEnergyRegion σ τ ρ energy)
    (hσ : 31/39 ≤ σ) (hσ1 : σ < 1)
    (hτlo : 4*σ/3 ≤ τ) (hτhi : τ ≤ 2*σ) :
    ρ ≤ 3*(1-σ)*τ/(2*σ) := by
  let χ := max 0 (τ+1-3*σ)
  let g := heathBrownDoubleZetaExponent τ ρ/2
  obtain ⟨hχ,hmargin,_hscale₁,_hscale₂,hclassical⟩ :=
    literatureTwelfth_candidate_scale_budgets hσ hσ1 hτlo hτhi
  have hρ : ρ ≤ max (2-2*σ) (τ+4-6*σ) := by
    simpa only [add_comm (4:ℝ) τ] using hregion.huxley_cardinality
  have hρ1 : ρ ≤ 1 := (hρ.trans hclassical).trans (min_le_left _ _)
  have hρτ : ρ ≤ 4-2*τ := (hρ.trans hclassical).trans (min_le_right _ _)
  have hg : g ≤ 1+ρ/2 := by
    apply (div_le_iff₀ (by norm_num : (0:ℝ) < 2)).mpr
    unfold heathBrownDoubleZetaExponent
    exact max_le (max_le (by linarith only [hρ1]) (by linarith))
      (by linarith only [hρτ])
  have hd := literatureTwelfth_region_zero_loss_comparison (χ:=χ) hregion
    (by linarith only [hσ]) hχ hmargin
  change 2*ρ ≤ χ+max (max (2-2*σ+ρ) (2*(τ-χ)+4-8*σ+ρ))
    (max (36-50*σ+g+max (1/2) (τ-1)+2*(τ-χ))
      (19-26*σ+g+(τ-χ))) at hd
  have hbudget := literatureTwelfth_candidate_five_term_budget hσ hσ1 hτlo hτhi
  change max (max (2-2*σ+χ) (max (2*τ+4-8*σ-χ) ((40+2*τ-52*σ)/3)))
    (max ((75+4*τ-2*χ-100*σ)/3) ((72+6*τ-2*χ-100*σ)/3)) ≤ _ at hbudget
  rcases max_le_iff.mp hbudget with ⟨habc,hde⟩
  rcases max_le_iff.mp habc with ⟨ha,hbc⟩
  rcases max_le_iff.mp hbc with ⟨hb,hc⟩
  rcases max_le_iff.mp hde with ⟨he,hd'⟩
  have hsplit : 2*ρ-χ ≤ max (max (2-2*σ+ρ) (2*(τ-χ)+4-8*σ+ρ))
      (max (36-50*σ+g+max (1/2) (τ-1)+2*(τ-χ))
        (19-26*σ+g+(τ-χ))) := by linarith only [hd]
  rcases le_max_iff.mp hsplit with hs | hl
  · rcases le_max_iff.mp hs with h₁ | h₂
    · linarith only [h₁,ha]
    · linarith only [h₂,hb]
  · rcases le_max_iff.mp hl with h₁ | h₂
    · rcases le_total (1/2:ℝ) (τ-1) with ht | ht
      · rw [max_eq_right ht] at h₁
        linarith only [h₁,hg,hd']
      · rw [max_eq_left ht] at h₁
        linarith only [h₁,hg,he]
    · linarith only [h₂,hg,hc]


theorem bourgain_twelfth_largeValueExponent_range {σ τ : ℝ}
    (hσ : 31/39 ≤ σ) (hσ1 : σ < 1)
    (hτ : τ ∈ Set.Icc (2*(2*σ)/3) (2*σ)) :
    largeValueExponent σ τ ≤ ((((3-3*σ)*τ/(2*σ)):ℝ):EReal) := by
  have hhalf : 1/2 ≤ σ := by linarith only [hσ]
  have hτ0 : 0 ≤ τ := by linarith only [hσ,hτ.1]
  have hcoe := largeValueExponent_coe_toReal hhalf hσ1.le hτ0
  obtain ⟨e,s,hm⟩ := exists_energyRegion_at_largeValueExponent hhalf hσ1.le hτ0
  have hh := literatureTwelfth_region_cardinality
    (show InCardinalityEnergyRegion σ τ (largeValueExponent σ τ).toReal e from ⟨s,hm⟩)
    hσ hσ1 (by linarith only [hτ.1]) hτ.2
  have he : 3*(1-σ)*τ/(2*σ) = (3-3*σ)*τ/(2*σ) := by ring
  rw [he] at hh
  rw [← hcoe]
  exact EReal.coe_le_coe_iff.mpr hh

theorem zeroDensityExponent_le_bourgain_twelfth {σ : ℝ}
    (hσ : 31/39 ≤ σ) (hσ1 : σ < 1) :
    TaoTrudgianYang2025.zeroDensityExponent σ ≤ ((3/(2*σ):ℝ):EReal) := by
  have hσp : 0 < 2*σ := by linarith only [hσ]
  apply zeroDensityExponent_le_three_div_of_largeValue_bounds
    σ (2*σ) (by linarith only [hσ]) hσ1 hσp
  · intro τ ht
    apply (zetaLargeValueExponent_le_of_bound
      (zetaTwelfth_largeValueBound (by linarith only [hσ]) ht.1)).trans
    apply EReal.coe_le_coe_iff.mpr
    apply (le_div_iff₀ hσp).mpr
    have hc : 0 ≤ 2*(2*σ)-(3-3*σ) := by linarith only [hσ]
    have hh := mul_nonneg hc (show 0 ≤ 4*(2*σ)/3-τ by linarith only [ht.2])
    have hg := mul_nonneg hσp.le
      (show 0 ≤ 3*(4*σ-1)/4-2*σ by linarith only [hσ])
    nlinarith only [hh,hg]
  · exact fun _ ht => bourgain_twelfth_largeValueExponent_range hσ hσ1 ht

/-- The literal Bourgain literature row, obtained by an alternate critical-line
twelfth-moment route, not by assuming the off-critical eighth moment. -/
theorem zeroDensityExponent_le_bourgain_literature {σ : ℝ}
    (hσ : 1867/2347 ≤ σ) (hσ1 : σ < 1) :
    TaoTrudgianYang2025.zeroDensityExponent σ ≤ ((3/(2*σ):ℝ):EReal) :=
  zeroDensityExponent_le_bourgain_twelfth (by linarith only [hσ]) hσ1


/-! Literal literature-table assembly away from the unresolved Pintz lower
endpoints, and explicit limitations of the raw derivative-majorant route.
These results neither repair the source contract nor close EPZAE-30. -/

namespace LiteratureTable

def printedFiniteDensityTable (σ : ℝ) : ℝ :=
  if σ ≤ 7/10 then 3/(2-σ) else
  if σ < 19/25 then 15/(3+5*σ) else
  if σ < 127/167 then 9/(8*σ-2) else
  if σ < 13/17 then 15/(13*σ-3) else
  if σ < 17/22 then 6/(5*σ-1) else
  if σ < 41/53 then 2/(9*σ-6) else
  if σ < 7/9 then 9/(7*σ-1) else
  if σ < 1867/2347 then 9/(8*(2*σ-1)) else
  if σ < 4/5 then 3/(2*σ) else
  if σ < 7/8 then 3/(2*σ) else
  if σ < 279/314 then 3/(10*σ-7) else
  if σ < 155/174 then 24/(30*σ-11) else
  if σ ≤ 9/10 then 24/(30*σ-11) else
  if σ ≤ 31/34 then 3/(10*σ-7) else
  if σ < 14/15 then 11/(48*σ-36) else
  if σ < 2841/3016 then 391/(2493*σ-2014) else
  if σ < 859/908 then 22232/(163248*σ-134765) else
  if σ < 23/24 then 356/(2742*σ-2279) else
  if σ < 2211487/2274732 then 3/(24*σ-20) else
  if σ < 39/40 then 86152/(1447460*σ-1311509) else
  if σ < 41/42 then 2/(15*σ-12) else
  3/(40*σ-35)

theorem zeroDensityExponent_le_printedFinite_regular {σ : ℝ}
    (hσ : 1/2 ≤ σ) (hσhi : σ < 59/60)
    (h39 : σ ≠ 39/40) (h41 : σ ≠ 41/42) :
    TaoTrudgianYang2025.zeroDensityExponent σ ≤ ((printedFiniteDensityTable σ):EReal) := by
  have hσ1 : σ < 1 := by linarith only [hσhi]
  unfold printedFiniteDensityTable
  by_cases h1 : σ ≤ 7/10
  · rw [if_pos h1]
    exact zeroDensityExponent_le_ingham_closed hσ hσ1.le
  rw [if_neg h1]
  by_cases h2 : σ < 19/25
  · rw [if_pos h2]
    exact zeroDensityExponent_le_guthMaynard (by linarith only [h1]) hσ1.le
  rw [if_neg h2]
  by_cases h3 : σ < 127/167
  · rw [if_pos h3]
    exact zeroDensityExponent_le_ivic_six (by linarith only [h2]) hσ1
  rw [if_neg h3]
  by_cases h4 : σ < 13/17
  · rw [if_pos h4]
    exact zeroDensityExponent_le_ivic_five (le_of_not_gt h3) hσ1
  rw [if_neg h4]
  by_cases h5 : σ < 17/22
  · rw [if_pos h5]
    exact zeroDensityExponent_le_ivic_four (le_of_not_gt h4) hσ1
  rw [if_neg h5]
  by_cases h6 : σ < 41/53
  · rw [if_pos h6]
    exact zeroDensityExponent_le_bourgain_improved_lower (le_of_not_gt h5)
      (by linarith only [h6])
  rw [if_neg h6]
  by_cases h7 : σ < 7/9
  · rw [if_pos h7]
    exact zeroDensityExponent_le_ivic_three (le_of_not_gt h6) hσ1
  rw [if_neg h7]
  by_cases h8 : σ < 1867/2347
  · rw [if_pos h8]
    exact zeroDensityExponent_le_bourgain_improved_upper
      (by linarith only [h7]) (by linarith only [h8])
  rw [if_neg h8]
  by_cases h9 : σ < 4/5
  · rw [if_pos h9]
    exact zeroDensityExponent_le_bourgain_literature (le_of_not_gt h8) hσ1
  rw [if_neg h9]
  by_cases h10 : σ < 7/8
  · rw [if_pos h10]
    exact zeroDensityExponent_le_ivic_two (le_of_not_gt h9) hσ1
  rw [if_neg h10]
  by_cases h11 : σ < 279/314
  · rw [if_pos h11]
    exact improved_heathBrown_zeroDensity (by linarith only [h10]) hσ1.le
  rw [if_neg h11]
  by_cases h12 : σ < 155/174
  · rw [if_pos h12]
    exact zeroDensityExponent_le_cdv_ivic (le_of_not_gt h11) (by linarith only [h12])
  rw [if_neg h12]
  by_cases h13 : σ ≤ 9/10
  · rw [if_pos h13]
    exact zeroDensityExponent_le_ivic_nineteenth (le_of_not_gt h12) (by linarith only [h13])
  rw [if_neg h13]
  by_cases h14 : σ ≤ 31/34
  · rw [if_pos h14]
    exact improved_heathBrown_zeroDensity (by linarith only [h13]) hσ1.le
  rw [if_neg h14]
  by_cases h15 : σ < 14/15
  · rw [if_pos h15]
    have hh := exponentPair_eleven_eightyFifths.bourgain_piece_1
      (by linarith only [h14]) hσ1.le
    simpa [bourgainPieceOne,generatedBourgainPiece1,RationalAffineFraction.eval] using hh
  rw [if_neg h15]
  by_cases h16 : σ < 2841/3016
  · rw [if_pos h16]
    by_cases he : σ = 14/15
    · subst σ
      have hh := exponentPair_eleven_eightyFifths.bourgain_piece_1
        (σ:=14/15) (by norm_num) (by norm_num)
      norm_num [bourgainPieceOne,generatedBourgainPiece1,RationalAffineFraction.eval] at hh ⊢
      exact hh
    · have hh := zeroDensityExponent_le_bourgain_piece_2
        (lt_of_le_of_ne (le_of_not_gt h15) (Ne.symm he)) hσ1.le
      simpa [bourgainPieceTwo,generatedBourgainPiece2,RationalAffineFraction.eval] using hh
  rw [if_neg h16]
  by_cases h17 : σ < 859/908
  · rw [if_pos h17]
    by_cases he : σ = 2841/3016
    · subst σ
      have hh := zeroDensityExponent_le_bourgain_piece_2
        (σ:=2841/3016) (by norm_num) (by norm_num)
      norm_num [bourgainPieceTwo,generatedBourgainPiece2,RationalAffineFraction.eval] at hh ⊢
      exact hh
    · have hh := zeroDensityExponent_le_bourgain_piece_3
        (lt_of_le_of_ne (le_of_not_gt h16) (Ne.symm he)) hσ1.le
      simpa [bourgainPieceThree,generatedBourgainPiece3,RationalAffineFraction.eval] using hh
  rw [if_neg h17]
  by_cases h18 : σ < 23/24
  · rw [if_pos h18]
    by_cases he : σ = 859/908
    · subst σ
      have hh := zeroDensityExponent_le_bourgain_piece_3
        (σ:=859/908) (by norm_num) (by norm_num)
      norm_num [bourgainPieceThree,generatedBourgainPiece3,RationalAffineFraction.eval] at hh ⊢
      exact hh
    · have hh := zeroDensityExponent_le_bourgain_piece_4
        (lt_of_le_of_ne (le_of_not_gt h17) (Ne.symm he)) hσ1.le
      simpa [bourgainPieceFour,generatedBourgainPiece4,RationalAffineFraction.eval] using hh
  rw [if_neg h18]
  by_cases h19 : σ < 2211487/2274732
  · rw [if_pos h19]
    exact zeroDensityExponent_le_pintz_first (le_of_not_gt h18) hσ1
  rw [if_neg h19]
  by_cases h20 : σ < 39/40
  · rw [if_pos h20]
    have hh := zeroDensityExponent_le_bourgain_piece_8
      (by linarith only [h19]) hσ1.le
    simpa [bourgainPieceEight,generatedBourgainPiece8,RationalAffineFraction.eval] using hh
  rw [if_neg h20]
  by_cases h21 : σ < 41/42
  · rw [if_pos h21]
    exact zeroDensityExponent_le_pintz_second_interior
      (lt_of_le_of_ne (le_of_not_gt h20) (Ne.symm h39)) hσ1
  rw [if_neg h21]
  exact zeroDensityExponent_le_pintz_third_interior
    (lt_of_le_of_ne (le_of_not_gt h21) (Ne.symm h41)) hσ1



/-- Every raw integer derivative majorant meets the Pintz plateau in this
height range. This is a limitation of these majorants, not a lower bound
for the true exponential sum or a counterexample to a density theorem. -/
theorem raw_derivative_plateau_all_orders {n r : ℕ}
    (hn : 4 ≤ n) (hr : 3 ≤ r) {τ : ℝ}
    (hτlo : (n:ℝ)-2+2/(n:ℝ) ≤ τ) :
    1-1/((n:ℝ)*((n:ℝ)-1)) ≤ τ*heathBrownBetaBound r (1/τ) := by
  have hnr : (4:ℝ) ≤ n := by exact_mod_cast hn
  have hrr : (3:ℝ) ≤ r := by exact_mod_cast hr
  have hnp : (0:ℝ) < n := by linarith only [hnr]
  have hDn : 0 < (n:ℝ)*((n:ℝ)-1) := mul_pos hnp (by linarith only [hnr])
  have hDr : 0 < (r:ℝ)*((r:ℝ)-1) := mul_pos
    (by linarith only [hrr]) (by linarith only [hrr])
  have hτ : 0 < τ := by
    have hp : 0 < 2/(n:ℝ) := div_pos (by norm_num) hnp
    linarith only [hnr,hτlo,hp]
  rw [heathBrownBetaBound_reciprocal_scale hr hτ (by field_simp)]
  by_cases hnr' : n ≤ r
  · have hnr'' : (n:ℝ) ≤ r := by exact_mod_cast hnr'
    have hD : (n:ℝ)*((n:ℝ)-1) ≤ (r:ℝ)*((r:ℝ)-1) := by
      gcongr
      linarith only [hnr]
    have hi : 1/((r:ℝ)*((r:ℝ)-1)) ≤ 1/((n:ℝ)*((n:ℝ)-1)) :=
      one_div_le_one_div_of_le hDn hD
    have hm : -1/((r:ℝ)*((r:ℝ)-1)) ≤
        max ((τ-(r:ℝ))/((r:ℝ)*((r:ℝ)-1)))
          (max (-1/((r:ℝ)*((r:ℝ)-1))) (-2*τ/((r:ℝ)^2*((r:ℝ)-1)))) :=
      (le_max_left _ _).trans (le_max_right _ _)
    simp only [neg_div] at hm ⊢
    linarith only [hi,hm]
  · have hrn : (r:ℝ) ≤ (n:ℝ)-1 := by
      have hh : r+1 ≤ n := by omega
      have hh' : (r:ℝ)+1 ≤ n := by exact_mod_cast hh
      linarith only [hh']
    have hfactor : 0 ≤ (n:ℝ)*((n:ℝ)-1)-(n:ℝ)-(r:ℝ)+2 := by
      nlinarith only [hnr,hrn,sq_nonneg ((n:ℝ)-2)]
    have hpoly := mul_nonneg
      (show 0 ≤ (n:ℝ)-1-(r:ℝ) by linarith only [hrn]) hfactor
    have ht := (div_le_iff₀ hnp).mp
      (show 2/(n:ℝ) ≤ τ-(n:ℝ)+2 by linarith only [hτlo])
    have hheight := mul_le_mul_of_nonneg_right ht
      (show 0 ≤ (n:ℝ)-1 by linarith only [hnr])
    have hfirst : -1/((n:ℝ)*((n:ℝ)-1)) ≤
        (τ-(r:ℝ))/((r:ℝ)*((r:ℝ)-1)) := by
      apply (div_le_div_iff₀ hDn hDr).mpr
      nlinarith only [hpoly,hheight]
    have hm := le_max_left ((τ-(r:ℝ))/((r:ℝ)*((r:ℝ)-1)))
      (max (-1/((r:ℝ)*((r:ℝ)-1))) (-2*τ/((r:ℝ)^2*((r:ℝ)-1))))
    simp only [neg_div] at hfirst
    linarith only [hfirst,hm]


/-- At the first missing endpoint, every raw integer derivative order fails
the strict ordinary Gram gap at a height inside the required interval. -/
theorem first_missing_endpoint_raw_obstruction {r : ℕ} (hr : 3 ≤ r) :
    (15/4:ℝ) ∈ Set.Icc (2*((45*(39/40)-36)/2)/3) ((45*(39/40)-36)/2) ∧
    ¬ ((15/4:ℝ)*heathBrownBetaBound r (4/15) < 2*(39/40)-1) := by
  refine ⟨by norm_num, ?_⟩
  have hh := raw_derivative_plateau_all_orders (n:=5) (by omega) hr
    (τ:=15/4) (by norm_num)
  norm_num at hh ⊢
  exact hh

/-- At the second missing endpoint, the analogous zeta gap fails for every
raw integer derivative order inside the required zeta height interval. -/
theorem second_missing_endpoint_raw_obstruction {r : ℕ} (hr : 3 ≤ r) :
    (16/3:ℝ) ∈ Set.Ico 2 (4*(40*(41/42)-35)/3) ∧
    ¬ ((16/3:ℝ)*heathBrownBetaBound r (3/16) < 41/42) := by
  refine ⟨by norm_num, ?_⟩
  have hh := raw_derivative_plateau_all_orders (n:=7) (by omega) hr
    (τ:=16/3) (by norm_num)
  norm_num at hh ⊢
  exact hh

/-- The same obstruction occurs at every printed lower endpoint of the
integer tail. This concerns the raw majorant, not the true beta function. -/
theorem tail_lower_endpoint_raw_obstruction {n r : ℕ}
    (hn : 6 ≤ n) (hr : 3 ≤ r) :
    let σ := 1-1/(2*(n:ℝ)*((n:ℝ)-1))
    let τ := (n:ℝ)-1-1/(2*(n:ℝ)*((n:ℝ)-1))
    τ ∈ Set.Icc (2*((n:ℝ)-1)/3) ((n:ℝ)-1) ∧
      ¬ (τ*heathBrownBetaBound r (1/τ) < 2*σ-1) := by
  dsimp only
  have hnr : (6:ℝ) ≤ n := by exact_mod_cast hn
  have hnp : (0:ℝ) < n := by linarith only [hnr]
  have hnm : (0:ℝ) < (n:ℝ)-1 := by linarith only [hnr]
  have hD : 0 < 2*(n:ℝ)*((n:ℝ)-1) := by positivity
  have hDlarge : (2:ℝ) ≤ 2*(n:ℝ)*((n:ℝ)-1) := by
    nlinarith only [hnr, sq_nonneg ((n:ℝ)-1)]
  have ha := one_div_le_one_div_of_le (by norm_num : (0:ℝ)<2) hDlarge
  have ha0 : 0 ≤ 1/(2*(n:ℝ)*((n:ℝ)-1)) := le_of_lt (one_div_pos.mpr hD)
  have hb : 2/(n:ℝ) ≤ 1/2 := (div_le_iff₀ hnp).mpr (by linarith only [hnr])
  have hh := raw_derivative_plateau_all_orders (n:=n) (by omega) hr
    (τ:=(n:ℝ)-1-1/(2*(n:ℝ)*((n:ℝ)-1))) (by linarith only [ha,hb])
  have he : 1-1/((n:ℝ)*((n:ℝ)-1)) =
      2*(1-1/(2*(n:ℝ)*((n:ℝ)-1)))-1 := by
    field_simp
    ring
  rw [he] at hh
  exact ⟨⟨by linarith only [hnr,ha], by linarith only [ha0]⟩, not_lt_of_ge hh⟩


/-- The half-open tail cells cover the entire printed near-one range.
This is interval selection only; it asserts no analytic endpoint bound. -/
theorem exists_printed_tail_cell {σ : ℝ} (hlo : 59/60 ≤ σ) (hhi : σ < 1) :
    ∃ n : ℕ, 6 ≤ n ∧
      1-1/(2*(n:ℝ)*((n:ℝ)-1)) ≤ σ ∧
      σ < 1-1/(2*(n:ℝ)*((n:ℝ)+1)) := by
  classical
  have hη : 0 < 1-σ := by linarith only [hhi]
  obtain ⟨m, hm⟩ := exists_nat_gt (1/(1-σ))
  have he : ∃ j : ℕ, σ < 1-1/(2*((j:ℝ)+6)*((j:ℝ)+7)) := by
    refine ⟨m, ?_⟩
    have hm0 : (0:ℝ) ≤ m := Nat.cast_nonneg m
    have hp : 0 < (m:ℝ)+6 := by linarith only [hm0]
    have hd : (m:ℝ)+6 ≤ 2*((m:ℝ)+6)*((m:ℝ)+7) := by
      nlinarith only [hm0, sq_nonneg (m:ℝ)]
    have hinv := one_div_le_one_div_of_le hp hd
    have hsmall : 1/((m:ℝ)+6) < 1-σ := by
      apply (div_lt_iff₀ hp).mpr
      have hh := (div_lt_iff₀ hη).mp hm
      nlinarith only [hh,hη]
    linarith only [hinv,hsmall]
  let j := Nat.find he
  have hj := Nat.find_spec he
  change σ < 1-1/(2*((j:ℝ)+6)*((j:ℝ)+7)) at hj
  refine ⟨j+6, by omega, ?_, ?_⟩
  · cases hj0 : j with
    | zero => norm_num [hj0] at *; exact hlo
    | succ k =>
      have hk : k < Nat.find he := by change k < j; omega
      have hh := le_of_not_gt (Nat.find_min he hk)
      convert hh using 1
      push_cast
      ring
  · convert hj using 1
    push_cast
    ring

/-- Every nonendpoint in the printed integer tail has the exact printed
bound, with its actual interval index chosen rather than assumed. -/
theorem exists_printed_tail_bound_regular {σ : ℝ}
    (hlo : 59/60 ≤ σ) (hhi : σ < 1)
    (hendpoint : ∀ n : ℕ, 6 ≤ n → σ ≠ 1-1/(2*(n:ℝ)*((n:ℝ)-1))) :
    ∃ n : ℕ, 6 ≤ n ∧
      1-1/(2*(n:ℝ)*((n:ℝ)-1)) ≤ σ ∧
      σ < 1-1/(2*(n:ℝ)*((n:ℝ)+1)) ∧
      TaoTrudgianYang2025.zeroDensityExponent σ ≤
        ((3/((n:ℝ)*(1-2*((n:ℝ)-1)*(1-σ))):ℝ):EReal) := by
  obtain ⟨n,hn,hleft,hright⟩ := exists_printed_tail_cell hlo hhi
  refine ⟨n,hn,hleft,hright,?_⟩
  exact zeroDensityExponent_le_pintz_tail_interior hn
    (lt_of_le_of_ne hleft (Ne.symm (hendpoint n hn))) hright.le

end LiteratureTable

end TaoTrudgianYang2025
