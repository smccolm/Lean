import TaoTrudgianYang2025.BourgainRetainedPowerWindows

/-!
# Actual retained-zeta source entry above the three-quarter value exponent

The source value and height exponents are linked to the physical pattern.
The high-value threshold and endpoint subtraction are derived from a
positive exponent gap, not passed as analytic assumptions. N ≤ T is
still explicit; the unrestricted low-value source lemma is not claimed.
-/

open Filter Finset RiemannZeta.GuthMaynard

noncomputable section

namespace TaoTrudgianYang2025

/-- A uniform retained-zeta estimate on actual power-window patterns.
It includes the endpoint tau=1 whenever N ≤ T, without requiring a
strict height-exponent gap. All loss/radius choices precede the pattern. -/
theorem bourgain_retained_source_power_bound {σ τ : ℝ} (hσ : 3/4 < σ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C δ : ℝ, 1 ≤ C ∧ 0 < δ ∧
      ∀ P : LargeValuePattern,
        C ≤ P.N → P.N ≤ P.T → P.T ≤ P.N^(τ+δ) → P.N^(σ-δ) ≤ P.V →
        ∃ W : Finset ℝ,
          W ⊆ P.reflectedOrdinates ∧ IsSeparated 2 W ∧ InBaseInterval P.T W ∧
          (P.ordinates.card : ℝ) ≤ C*P.N^ε*(W.card : ℝ) ∧
          (P.ordinates.card : ℝ) ≤ C *
            (P.N^(2-2*σ+ε) + P.N^(2*τ+4-8*σ+ε) +
              P.N^(3-4*σ+ε)*Real.sqrt (bourgainZetaDifferenceMoment W (P.N^ε))) := by
  let g : ℝ := σ-3/4
  let K : ℝ := max 1 τ+1
  let δ : ℝ := min (g/8) (min 1 (ε/72))
  let η : ℝ := min (ε/(8*K)) (g/K)
  have hg : 0 < g := by dsimp [g]; linarith
  have hK : 1 ≤ K := by dsimp [K]; linarith [le_max_left (1 : ℝ) τ]
  have hKp : 0 < K := by linarith
  have hδ : 0 < δ := lt_min (by positivity) (lt_min zero_lt_one (by positivity))
  have hη : 0 < η := lt_min (by positivity) (by positivity)
  have hδg : δ ≤ g/8 := min_le_left _ _
  have hδ1 : δ ≤ 1 := (min_le_right _ _).trans (min_le_left _ _)
  have hδe : δ ≤ ε/72 := (min_le_right _ _).trans (min_le_right _ _)
  have hηe : K*η ≤ ε/8 := by
    have hh := (le_div_iff₀ (by positivity : (0 : ℝ) < 8*K)).mp
      (show η ≤ ε/(8*K) from min_le_left _ _)
    nlinarith
  have hηg : K*η ≤ g := by
    have hh := (le_div_iff₀ hKp).mp (show η ≤ g/K from min_le_right _ _)
    nlinarith
  have hexp : K*η+18*δ ≤ ε := by linarith
  have hradiusExp : K*η ≤ ε := by linarith
  have hvalueGap : K*η+6 < 8*(σ-2*δ) := by dsimp [g] at hg hηg hδg; linarith
  have hs : 0 ≤ σ-2*δ := by dsimp [g] at hδg; linarith
  obtain ⟨C₀,T₀,hC₀,hT₀,hp⟩ :=
    bourgain_retained_cardinality_uniform (Classical.choice exists_gmSmoothCutoff) hη
  obtain ⟨Na,hNa⟩ := eventually_atTop.mp
    (eventually_const_mul_rpow_le_rpow (D := C₀) hvalueGap)
  obtain ⟨Nv,hNv⟩ := eventually_atTop.mp
    (eventually_rpow_add_one_le_rpow hs (by linarith : σ-2*δ < σ-δ))
  let C : ℝ := max 30 (max T₀ (max Na (max Nv C₀)))
  have h30 : (30 : ℝ) ≤ C := le_max_left _ _
  have hC : 1 ≤ C := by linarith
  have hCT : T₀ ≤ C := (le_max_left _ _).trans (le_max_right _ _)
  have hCA : Na ≤ C := (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have hCV : Nv ≤ C := (le_max_left _ _).trans
    ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _)))
  have hCC : C₀ ≤ C := (le_max_right _ _).trans
    ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _)))
  refine ⟨C,δ,hC,hδ,?_⟩
  intro P hN hNT hTu hVl
  have hN1 : 1 ≤ P.N := P.one_lt_N.le
  have hNp : 0 < P.N := zero_lt_one.trans P.one_lt_N
  have hTp := P.T_pos
  have hscale : 30 ≤ P.scale := by
    have hh := h30.trans hN
    rw [P.N_eq_scale] at hh
    exact_mod_cast hh
  have hV : P.N^(σ-2*δ) ≤ P.V-1 := by
    have hh := (hNv P.N (hCV.trans hN)).trans hVl
    linarith
  have hVp : 1 < P.V := by
    have hh := Real.rpow_pos_of_pos hNp (σ-2*δ)
    linarith
  have hTK : P.T ≤ P.N^K := hTu.trans
    (Real.rpow_le_rpow_of_exponent_le hN1 (by dsimp [K]; linarith [le_max_right (1 : ℝ) τ]))
  have hTpow : P.T^η ≤ P.N^(K*η) := by
    calc
      _ ≤ (P.N^K)^η := Real.rpow_le_rpow P.T_pos.le hTK hη.le
      _ = _ := (Real.rpow_mul hNp.le _ _).symm
  have hRadius : P.T^η ≤ P.N^ε :=
    hTpow.trans (Real.rpow_le_rpow_of_exponent_le hN1 hradiusExp)
  have habs : C₀*P.T^η*P.N^6 ≤ (P.V-1)^8 := by
    calc
      _ ≤ C₀*P.N^(K*η)*P.N^6 := by gcongr
      _ = C₀*P.N^(K*η+6) := by rw [← Real.rpow_natCast P.N 6, mul_assoc, ← Real.rpow_add hNp]; norm_num
      _ ≤ P.N^(8*(σ-2*δ)) := hNa P.N (hCA.trans hN)
      _ = (P.N^(σ-2*δ))^8 := by rw [← Real.rpow_mul_natCast hNp.le]; norm_num; congr 1; ring
      _ ≤ (P.V-1)^8 := pow_le_pow_left₀ (by positivity) hV _
  obtain ⟨W,hsub,hsep,hbase,hcard,hbound⟩ :=
    hp P hscale hVp ((hCT.trans hN).trans hNT) hNT habs
  refine ⟨W,hsub,hsep,hbase,hcard.trans ?_,?_⟩
  · gcongr
  let M := bourgainZetaDifferenceMoment W (P.N^ε)
  have hmoment : bourgainZetaDifferenceMoment W (P.T^η) ≤ M :=
    bourgainZetaDifferenceMoment_mono W (by positivity) hRadius
  have hterms := bourgain_retained_power_terms_le (M := M) hN1 P.T_pos.le hTu hV
  have h1 : P.N^(K*η)*P.N^(2-2*σ+4*δ) ≤ P.N^(2-2*σ+ε) := by
    rw [← Real.rpow_add hNp]
    exact Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
  have h2 : P.N^(K*η)*P.N^(2*τ+4-8*σ+18*δ) ≤ P.N^(2*τ+4-8*σ+ε) := by
    rw [← Real.rpow_add hNp]
    exact Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
  have h3 : P.N^(K*η)*P.N^(3-4*σ+8*δ) ≤ P.N^(3-4*σ+ε) := by
    rw [← Real.rpow_add hNp]
    exact Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
  calc
    _ ≤ C₀*P.T^η*(P.N^2/(P.V-1)^2+P.T^2*P.N^4/(P.V-1)^8+
        P.N^3*Real.sqrt M/(P.V-1)^4) := hbound.trans (by gcongr)
    _ ≤ C₀*P.N^(K*η)*(P.N^(2-2*σ+4*δ)+P.N^(2*τ+4-8*σ+18*δ)+
        P.N^(3-4*σ+8*δ)*Real.sqrt M) := by gcongr
    _ = C₀*(P.N^(K*η)*P.N^(2-2*σ+4*δ)+P.N^(K*η)*P.N^(2*τ+4-8*σ+18*δ)+
        (P.N^(K*η)*P.N^(3-4*σ+8*δ))*Real.sqrt M) := by ring
    _ ≤ C₀*(P.N^(2-2*σ+ε)+P.N^(2*τ+4-8*σ+ε)+P.N^(3-4*σ+ε)*Real.sqrt M) := by gcongr
    _ ≤ _ := by gcongr

end TaoTrudgianYang2025
