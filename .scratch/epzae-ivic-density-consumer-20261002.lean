import TaoTrudgianYang2025.JutilaWindowBound
import TaoTrudgianYang2025.ExponentPairLargeValues
import TaoTrudgianYang2025.ZeroDensityTransferCorollaries
import TaoTrudgianYang2025.ZetaTwelfthMoment

noncomputable section
open Filter RiemannZeta.GuthMaynard TaoTrudgianYang2025
namespace IvicDensityConsumerScratch

/-- Retain the actual five-quarter moment instead of weakening it to three halves. -/
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

example (k Q : ℕ) (T D V H : ℝ) (W : Finset ℝ)
    (hV : 0 < V) (hH : 0 < H)
    (hdiag : 4*D*(Q:ℝ)^k ≤ V^(4*k))
    (hmain : 4*D*T^k ≤ H*V^(4*k))
    (hmixed : 4*D*T^(1/2:ℝ)*(Q:ℝ)^k ≤ H^(3/4:ℝ)*V^(4*k))
    (hrec : (W.card:ℝ)^2*V^(4*k) ≤ D*jutilaMomentCore k Q T W) :
    (W.card:ℝ) ≤ H :=
  quarter_moment_card_le k Q T D V H W hV hH hdiag hmain hmixed hrec

#print axioms quarter_moment_card_le

/-- Strict margins for all three real physical powers and the thinning loss. -/
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

example (k : ℕ) (hk : 0 < k) {σ τ ε : ℝ}
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
      ν*(τ+1)+(2-2*σ+ε/2) ≤ 2-2*σ+ε :=
  local_loss_parameters k hk hσ hτ hε hfirst hsecond

#print axioms local_loss_parameters

/-- The existing smoothed source recurrence gives the stronger local
Montgomery range. All analytic inputs and loss thresholds are discharged. -/
private theorem ivic_local_largeValueBound
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

example (k : ℕ) (hk : 0 < k) {σ τ : ℝ}
    (hσ : 3/4 < σ) (hτ : 1 < τ)
    (hfirst : (k:ℝ)*τ+2*k-4*k*σ ≤ 2-2*σ)
    (hsecond : 2*τ/3+4*k*(3-4*σ)/3 ≤ 2-2*σ) :
    IsLargeValueBound σ τ (2-2*σ) :=
  ivic_local_largeValueBound k hk hσ hτ hfirst hsecond

#print axioms ivic_local_largeValueBound

/-- The exact two-thirds density transfer, with the stronger actual local
bound and the already proved twelfth-moment zeta input. -/
private theorem ivic_density_of_cutoff (k : ℕ) (hk : 0 < k) {σ τ₀ : ℝ}
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
      ((ivic_local_largeValueBound k hk hσ hlocal hfirst hsecond).of_height_le ht.2)

example (k : ℕ) (hk : 0 < k) {σ τ₀ : ℝ}
    (hσ : 3/4 < σ) (hσ₁ : σ < 1) (hlocal : 1 < τ₀+σ-1)
    (hfirst : (k:ℝ)*(τ₀+σ-1)+2*k-4*k*σ ≤ 2-2*σ)
    (hsecond : 2*(τ₀+σ-1)/3+4*k*(3-4*σ)/3 ≤ 2-2*σ)
    (hcut : τ₀ ≤ 3*(4*σ-1)/4) :
    zeroDensityExponent σ ≤ ((3/τ₀:ℝ):EReal) :=
  ivic_density_of_cutoff k hk hσ hσ₁ hlocal hfirst hsecond hcut

#print axioms ivic_density_of_cutoff

private theorem ivic_density_two {σ:ℝ} (hσ : 4/5 ≤ σ) (hσ₁ : σ < 1) :
    zeroDensityExponent σ ≤ ((3/(2*σ):ℝ):EReal) := by
  apply ivic_density_of_cutoff 2 (by omega) (by linarith) hσ₁
  · linarith
  · norm_num; linarith
  · norm_num; linarith
  · linarith

example {σ:ℝ} (hσ : 4/5 ≤ σ) (hσ₁ : σ < 1) :
    zeroDensityExponent σ ≤ ((3/(2*σ):ℝ):EReal) :=
  ivic_density_two hσ hσ₁

#print axioms ivic_density_two

private theorem ivic_density_three {σ:ℝ} (hσ : 41/53 ≤ σ) (hσ₁ : σ < 1) :
    zeroDensityExponent σ ≤ ((9/(7*σ-1):ℝ):EReal) := by
  have hh := ivic_density_of_cutoff 3 (by omega) (τ₀:=(7*σ-1)/3)
    (by linarith : 3/4 < σ) hσ₁ (by linarith)
    (by norm_num; linarith) (by norm_num; linarith) (by linarith)
  have hd : 7*σ-1 ≠ 0 := by linarith
  have he : (3:ℝ)/((7*σ-1)/3) = 9/(7*σ-1) := by field_simp; ring
  simpa only [he] using hh

example {σ:ℝ} (hσ : 41/53 ≤ σ) (hσ₁ : σ < 1) :
    zeroDensityExponent σ ≤ ((9/(7*σ-1):ℝ):EReal) :=
  ivic_density_three hσ hσ₁

#print axioms ivic_density_three

private theorem ivic_density_four {σ:ℝ} (hσ : 13/17 ≤ σ) (hσ₁ : σ < 1) :
    zeroDensityExponent σ ≤ ((6/(5*σ-1):ℝ):EReal) := by
  have hh := ivic_density_of_cutoff 4 (by omega) (τ₀:=(5*σ-1)/2)
    (by linarith : 3/4 < σ) hσ₁ (by linarith)
    (by norm_num; linarith) (by norm_num; linarith) (by linarith)
  have hd : 5*σ-1 ≠ 0 := by linarith
  have he : (3:ℝ)/((5*σ-1)/2) = 6/(5*σ-1) := by field_simp; ring
  simpa only [he] using hh

example {σ:ℝ} (hσ : 13/17 ≤ σ) (hσ₁ : σ < 1) :
    zeroDensityExponent σ ≤ ((6/(5*σ-1):ℝ):EReal) :=
  ivic_density_four hσ hσ₁

#print axioms ivic_density_four

private theorem ivic_density_five {σ:ℝ} (hσ : 127/167 ≤ σ) (hσ₁ : σ < 1) :
    zeroDensityExponent σ ≤ ((15/(13*σ-3):ℝ):EReal) := by
  have hh := ivic_density_of_cutoff 5 (by omega) (τ₀:=(13*σ-3)/5)
    (by linarith : 3/4 < σ) hσ₁ (by linarith)
    (by norm_num; linarith) (by norm_num; linarith) (by linarith)
  have hd : 13*σ-3 ≠ 0 := by linarith
  have he : (3:ℝ)/((13*σ-3)/5) = 15/(13*σ-3) := by field_simp; ring
  simpa only [he] using hh

example {σ:ℝ} (hσ : 127/167 ≤ σ) (hσ₁ : σ < 1) :
    zeroDensityExponent σ ≤ ((15/(13*σ-3):ℝ):EReal) :=
  ivic_density_five hσ hσ₁

#print axioms ivic_density_five

private theorem ivic_density_six {σ:ℝ} (hσ : 47/62 ≤ σ) (hσ₁ : σ < 1) :
    zeroDensityExponent σ ≤ ((9/(8*σ-2):ℝ):EReal) := by
  have hh := ivic_density_of_cutoff 6 (by omega) (τ₀:=(8*σ-2)/3)
    (by linarith : 3/4 < σ) hσ₁ (by linarith)
    (by norm_num; linarith) (by norm_num; linarith) (by linarith)
  have hd : 8*σ-2 ≠ 0 := by linarith
  have he : (3:ℝ)/((8*σ-2)/3) = 9/(8*σ-2) := by field_simp; ring
  simpa only [he] using hh

example {σ:ℝ} (hσ : 47/62 ≤ σ) (hσ₁ : σ < 1) :
    zeroDensityExponent σ ≤ ((9/(8*σ-2):ℝ):EReal) :=
  ivic_density_six hσ hσ₁

#print axioms ivic_density_six

end IvicDensityConsumerScratch
