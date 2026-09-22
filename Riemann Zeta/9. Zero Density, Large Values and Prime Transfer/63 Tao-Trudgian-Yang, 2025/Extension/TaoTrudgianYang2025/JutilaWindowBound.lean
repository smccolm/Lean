import TaoTrudgianYang2025.JutilaPowerWindows

/-!
# Uniform large-value bounds from a linked Jutila local exponent

The parameter ℓ is the exponent of the actual chosen height N^ℓ.
The physical value threshold is derived, not retained as a premise.
-/

open Filter

noncomputable section

namespace TaoTrudgianYang2025

/-- A valid local exponent gives the uniform global large-value bound.
Only the two algebraic optimization inequalities remain as parameters. -/
theorem jutila_largeValueBound_of_local_exponent
    (k : ℕ) (hk : 0 < k) {σ τ ℓ : ℝ}
    (hσ : 3/4 < σ) (hℓ : 1 ≤ ℓ)
    (hfirst : (k : ℝ)*ℓ+2*k-4*k*σ ≤ 2-2*σ)
    (hsecond : ℓ+6*k-8*k*σ ≤ 2-2*σ) :
    IsLargeValueBound σ τ (2-2*σ+max 0 (τ-ℓ)) := by
  intro ε hε
  let g : ℝ := σ-3/4
  let δ : ℝ := min (g/8) (ε/(4*(16*(k : ℝ)+1)))
  let η : ℝ := min (ε/(4*ℓ)) ((k : ℝ)*g/ℓ)
  have hgp : 0 < g := by dsimp [g]; linarith
  have hkp : (0 : ℝ) < k := by exact_mod_cast hk
  have hℓp : 0 < ℓ := by linarith
  have hδ : 0 < δ := lt_min (by positivity) (by positivity)
  have hη : 0 < η := lt_min (by positivity) (by positivity)
  have hδg : δ ≤ g/8 := min_le_left _ _
  have hδe : δ ≤ ε/(4*(16*(k : ℝ)+1)) := min_le_right _ _
  have hηe : η ≤ ε/(4*ℓ) := min_le_left _ _
  have hηg : η ≤ (k : ℝ)*g/ℓ := min_le_right _ _
  have hηLoss : ℓ*η ≤ ε/4 := by
    have hh := (le_div_iff₀ (by positivity : (0 : ℝ) < 4*ℓ)).mp hηe
    nlinarith
  have hδLoss : (16*(k : ℝ)+1)*δ ≤ ε/4 := by
    have hh := (le_div_iff₀ (by positivity : (0 : ℝ) < 4*(16*(k : ℝ)+1))).mp hδe
    nlinarith
  have hvalueGap : ℓ*η+3*k < 4*k*(σ-2*δ) := by
    have hh := (le_div_iff₀ hℓp).mp hηg
    have hd := mul_le_mul_of_nonneg_left hδg hkp.le
    have hkg := mul_pos hkp hgp
    dsimp [g] at hh hd hkg
    nlinarith
  have hs : 0 ≤ σ-2*δ := by dsimp [g] at hδg; linarith
  obtain ⟨C₀, T₀, hC₀, hT₀, hp⟩ := jutila_subdivided_cardinality_native k hk hη
  obtain ⟨Na, hNa⟩ := eventually_atTop.mp
    (eventually_const_mul_rpow_le_rpow (D := C₀) hvalueGap)
  obtain ⟨Nv, hNv⟩ := eventually_atTop.mp
    (eventually_rpow_add_one_le_rpow hs (by linarith : σ-2*δ < σ-δ))
  let C := max 30 (max T₀ (max Na (max Nv (6*C₀))))
  have h30 : (30 : ℝ) ≤ C := le_max_left _ _
  have hC : 1 ≤ C := by linarith
  have hCT : T₀ ≤ C := le_trans (le_max_left _ _) (le_max_right _ _)
  have hCA : Na ≤ C := le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_max_right _ _))
  have hCV : Nv ≤ C := le_trans (le_max_left _ _)
    (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _)))
  have hCC : 6*C₀ ≤ C := le_trans (le_max_right _ _)
    (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _)))
  refine ⟨C, hC, δ, hδ, ?_⟩
  intro P hN _ hTUpper hVLower _
  have hN1 : 1 ≤ P.N := P.one_lt_N.le
  have hNp : 0 < P.N := zero_lt_one.trans P.one_lt_N
  have hscale : 30 ≤ P.scale := by
    have hh := h30.trans hN
    rw [P.N_eq_scale] at hh
    exact_mod_cast hh
  have hlocal : P.N ≤ P.N^ℓ := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hN1 hℓ
  have hLT : T₀ ≤ P.N^ℓ := (hCT.trans hN).trans hlocal
  have hV : P.N^(σ-2*δ) ≤ P.V-1 := by
    have hh := (hNv P.N (hCV.trans hN)).trans hVLower
    linarith
  have hVp : 1 < P.V := by
    have hh := Real.rpow_pos_of_pos hNp (σ-2*δ)
    linarith
  have hLpow : (P.N^ℓ)^η = P.N^(ℓ*η) := (Real.rpow_mul hNp.le _ _).symm
  have habs : C₀*(P.N^ℓ)^η*P.N^(3*k) ≤ (P.V-1)^(4*k) := by
    calc
      _ = C₀*P.N^(ℓ*η+3*k) := by
        rw [hLpow, ← Real.rpow_natCast P.N (3*k), mul_assoc, ← Real.rpow_add hNp]
        congr 1
        push_cast
        rfl
      _ ≤ P.N^(4*k*(σ-2*δ)) := hNa P.N (hCA.trans hN)
      _ = (P.N^(σ-2*δ))^(4*k) := by
        rw [← Real.rpow_mul_natCast hNp.le]
        congr 1
        push_cast
        ring
      _ ≤ (P.V-1)^(4*k) := pow_le_pow_left₀ (by positivity) hV _
  have hc := hp P (P.N^ℓ) hscale hVp hLT hlocal habs
  have hterms :
      P.N^2/(P.V-1)^2+(P.N^ℓ)^k*P.N^(2*k)/(P.V-1)^(4*k)+
          P.N^ℓ*P.N^(6*k)/(P.V-1)^(8*k) ≤ 3*P.N^(2-2*σ+16*k*δ) := by
    calc
      _ ≤ P.N^2/(P.N^(σ-2*δ))^2+
          (P.N^ℓ)^k*P.N^(2*k)/(P.N^(σ-2*δ))^(4*k)+
          P.N^ℓ*P.N^(6*k)/(P.N^(σ-2*δ))^(8*k) := by gcongr
      _ ≤ _ := jutila_local_power_terms_le k hk hN1 hδ.le hfirst hsecond
  have hbin := jutila_subdivision_power_factor hN1 hTUpper hδ.le (ℓ := ℓ)
  have hExp : ℓ*η+(max 0 (τ-ℓ)+δ)+(2-2*σ+16*k*δ) ≤
      (2-2*σ+max 0 (τ-ℓ))+ε := by nlinarith
  calc
    _ ≤ C₀*(P.N^ℓ)^η*(1+P.T/P.N^ℓ)*
        (P.N^2/(P.V-1)^2+(P.N^ℓ)^k*P.N^(2*k)/(P.V-1)^(4*k)+
          P.N^ℓ*P.N^(6*k)/(P.V-1)^(8*k)) := hc
    _ ≤ C₀*P.N^(ℓ*η)*(2*P.N^(max 0 (τ-ℓ)+δ))*
        (3*P.N^(2-2*σ+16*k*δ)) := by rw [hLpow]; gcongr
    _ = (6*C₀)*P.N^(ℓ*η+(max 0 (τ-ℓ)+δ)+(2-2*σ+16*k*δ)) := by
      rw [show C₀*P.N^(ℓ*η)*(2*P.N^(max 0 (τ-ℓ)+δ))*
          (3*P.N^(2-2*σ+16*k*δ)) =
          (6*C₀)*(P.N^(ℓ*η)*P.N^(max 0 (τ-ℓ)+δ)*P.N^(2-2*σ+16*k*δ)) by ring,
        ← Real.rpow_add hNp, ← Real.rpow_add hNp]
    _ ≤ C*P.N^((2-2*σ+max 0 (τ-ℓ))+ε) :=
      mul_le_mul hCC (Real.rpow_le_rpow_of_exponent_le hN1 hExp)
        (by positivity) (zero_le_one.trans hC)

end TaoTrudgianYang2025
