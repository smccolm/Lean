import TaoTrudgianYang2025.SargosScaledRemainder
import TaoTrudgianYang2025.SargosSextupleEndpoints

/-! Moving source support normalized by the real phase scale, including the negative observation range. -/

noncomputable section

open Set

namespace TaoTrudgianYang2025

theorem sargosScaledRemainderWidth_bounds {N : ℝ} (hN : 1 ≤ N) :
    0 < sargosScaledRemainderWidth N ∧ sargosScaledRemainderWidth N ≤ 1 := by
  have hN0 : 0 < N := zero_lt_one.trans_le hN
  constructor
  · exact one_div_pos.mpr (by positivity)
  · exact (div_le_one (by positivity : (0:ℝ) < 8*N)).mpr (by linarith)

theorem sargosScaledRemainder_anchor_formulas {H : ℕ} {N : ℝ} (hN : 0 < N) (M : ℕ)
    (q : SargosInitialMomentTuple H 3 × SargosInitialMomentTuple H 3) :
    sargosScaledRemainderLeft N q+2*sargosScaledRemainderWidth N =
        ((sargosSextupleRadius q:ℝ)+5/4)/N ∧
      sargosScaledRemainderRight M N q-2*sargosScaledRemainderWidth N =
        ((M:ℝ)-(sargosSextupleRadius q:ℝ)-1/4)/N ∧
      sargosScaledRemainderLeft N q+4*sargosScaledRemainderWidth N =
        ((sargosSextupleRadius q:ℝ)+3/2)/N := by
  dsimp [sargosScaledRemainderLeft,sargosScaledRemainderRight,sargosScaledRemainderWidth]
  constructor
  · field_simp
    ring
  constructor <;> field_simp <;> ring

theorem sargosScaledRemainder_interval_geometry {H M : ℕ} {N : ℝ}
    (hN : 0 < N) (hMN : (M:ℝ) ≤ N)
    (q : SargosInitialMomentTuple H 3 × SargosInitialMomentTuple H 3)
    (hne : (sargosSextupleInterior M q).Nonempty) :
    0 ≤ sargosScaledRemainderLeft N q ∧ sargosScaledRemainderRight M N q ≤ 1 ∧
      sargosScaledRemainderLeft N q+4*sargosScaledRemainderWidth N <
        sargosScaledRemainderRight M N q := by
  have hr : (0:ℝ) ≤ sargosSextupleRadius q := by
    exact_mod_cast (show 0 ≤ sargosSextupleRadius q from le_trans (by norm_num)
      (sargosSextupleRadius_bounds q).1)
  obtain ⟨m,hm⟩ := hne
  have hm' := Finset.mem_Ioo.mp hm
  have hgapZ : sargosSextupleRadius q+3 ≤ (M:ℤ)-sargosSextupleRadius q := by omega
  have hgap : (sargosSextupleRadius q:ℝ)+3 ≤ (M:ℝ)-(sargosSextupleRadius q:ℝ) := by
    exact_mod_cast hgapZ
  refine ⟨div_nonneg (by linarith) hN.le,?_,?_⟩
  · exact (div_le_one hN).mpr (by linarith)
  · rw [(sargosScaledRemainder_anchor_formulas hN M q).2.2]
    apply (div_lt_div_iff_of_pos_right hN).mpr
    linarith

theorem sargosSextupleInterior_in_scaled_plateau {H M : ℕ} {N : ℝ}
    (hN : 0 < N)
    (q : SargosInitialMomentTuple H 3 × SargosInitialMomentTuple H 3)
    {m : ℤ} (hm : m ∈ sargosSextupleInterior M q) :
    (m:ℝ)/N ∈ Icc (sargosScaledRemainderLeft N q+2*sargosScaledRemainderWidth N)
      (sargosScaledRemainderRight M N q-2*sargosScaledRemainderWidth N) := by
  have hm' := Finset.mem_Ioo.mp hm
  have hL : (sargosSextupleRadius q:ℝ)+2 ≤ m := by
    exact_mod_cast (show sargosSextupleRadius q+2 ≤ m by omega)
  have hR : (m:ℝ)+1 ≤ (M:ℝ)-(sargosSextupleRadius q:ℝ) := by
    exact_mod_cast (show m+1 ≤ (M:ℤ)-sargosSextupleRadius q by omega)
  rw [(sargosScaledRemainder_anchor_formulas hN M q).1,
    (sargosScaledRemainder_anchor_formulas hN M q).2.1]
  constructor <;> apply (div_le_div_iff_of_pos_right hN).mpr <;> linarith

theorem sargosScaledRemainder_observation_distances {H M : ℕ} {N : ℝ}
    (hN : 0 < N) (hMN : (M:ℝ) ≤ N)
    (q : SargosInitialMomentTuple H 3 × SargosInitialMomentTuple H 3)
    (hne : (sargosSextupleInterior M q).Nonempty) {x : ℝ} (hx : x ∈ Icc (-1:ℝ) 1) :
    |x-(sargosScaledRemainderLeft N q+2*sargosScaledRemainderWidth N)| ≤ 2 ∧
      |x-(sargosScaledRemainderRight M N q-2*sargosScaledRemainderWidth N)| ≤ 2 := by
  obtain ⟨hl,hr,hgap⟩ := sargosScaledRemainder_interval_geometry hN hMN q hne
  have hh : 0 < sargosScaledRemainderWidth N := one_div_pos.mpr (by positivity)
  constructor <;> apply abs_le.mpr <;> constructor <;> linarith [hx.1,hx.2]

end TaoTrudgianYang2025
