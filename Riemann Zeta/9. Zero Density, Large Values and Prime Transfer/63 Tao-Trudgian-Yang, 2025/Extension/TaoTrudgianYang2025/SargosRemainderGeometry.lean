import TaoTrudgianYang2025.SargosNormalizedRemainder
import TaoTrudgianYang2025.SargosSextupleEndpoints

/-! Integer support gives a genuine agreement plateau for the moving Taylor extension. -/

noncomputable section

open Set

namespace TaoTrudgianYang2025

theorem sargosRemainderWidth_bounds {M : ℕ} (hM : 1 ≤ M) :
    0 < sargosRemainderWidth M ∧ sargosRemainderWidth M ≤ 1 := by
  have hM1 : (1:ℝ) ≤ M := by exact_mod_cast hM
  have hM0 : (0:ℝ) < M := by linarith
  constructor
  · exact one_div_pos.mpr (by positivity)
  · exact (div_le_one (by positivity : (0:ℝ) < 8*M)).mpr (by linarith)

theorem sargosRemainder_anchor_formulas {H M : ℕ} (hM : 1 ≤ M)
    (q : SargosInitialMomentTuple H 3 × SargosInitialMomentTuple H 3) :
    sargosRemainderLeft M q+2*sargosRemainderWidth M =
        ((sargosSextupleRadius q:ℝ)+5/4)/M ∧
      sargosRemainderRight M q-2*sargosRemainderWidth M =
        ((M:ℝ)-(sargosSextupleRadius q:ℝ)-1/4)/M ∧
      sargosRemainderLeft M q+4*sargosRemainderWidth M =
        ((sargosSextupleRadius q:ℝ)+3/2)/M := by
  have hM0 : (M:ℝ) ≠ 0 := by exact_mod_cast (show M ≠ 0 by omega)
  dsimp [sargosRemainderLeft,sargosRemainderRight,sargosRemainderWidth]
  constructor
  · field_simp
    ring
  constructor <;> field_simp <;> ring

theorem sargosSextupleInterior_real {H M : ℕ}
    (q : SargosInitialMomentTuple H 3 × SargosInitialMomentTuple H 3)
    {m : ℤ} (hm : m ∈ sargosSextupleInterior M q) :
    (m:ℝ) ∈ Ioo ((sargosSextupleRadius q:ℝ)+1)
      ((M:ℝ)-(sargosSextupleRadius q:ℝ)) := by
  have h := Finset.mem_Ioo.mp hm
  exact ⟨by exact_mod_cast h.1,by exact_mod_cast h.2⟩

theorem sargosRemainder_interval_geometry {H M : ℕ} (hM : 1 ≤ M)
    (q : SargosInitialMomentTuple H 3 × SargosInitialMomentTuple H 3)
    (hne : (sargosSextupleInterior M q).Nonempty) :
    0 ≤ sargosRemainderLeft M q ∧ sargosRemainderRight M q ≤ 1 ∧
      sargosRemainderLeft M q+4*sargosRemainderWidth M < sargosRemainderRight M q := by
  have hM0 : (0:ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  have hr : (0:ℝ) ≤ sargosSextupleRadius q := by
    exact_mod_cast (show 0 ≤ sargosSextupleRadius q from le_trans (by norm_num)
      (sargosSextupleRadius_bounds q).1)
  obtain ⟨m,hm⟩ := hne
  have hm' := Finset.mem_Ioo.mp hm
  have hgapZ : sargosSextupleRadius q+3 ≤ (M:ℤ)-sargosSextupleRadius q := by omega
  have hgap : (sargosSextupleRadius q:ℝ)+3 ≤ (M:ℝ)-(sargosSextupleRadius q:ℝ) := by
    exact_mod_cast hgapZ
  refine ⟨div_nonneg (by linarith) hM0.le,?_,?_⟩
  · exact (div_le_one hM0).mpr (by linarith)
  · rw [(sargosRemainder_anchor_formulas hM q).2.2]
    apply (div_lt_div_iff_of_pos_right hM0).mpr
    linarith

theorem sargosSextupleInterior_in_plateau {H M : ℕ} (hM : 1 ≤ M)
    (q : SargosInitialMomentTuple H 3 × SargosInitialMomentTuple H 3)
    {m : ℤ} (hm : m ∈ sargosSextupleInterior M q) :
    (m:ℝ)/M ∈ Icc (sargosRemainderLeft M q+2*sargosRemainderWidth M)
      (sargosRemainderRight M q-2*sargosRemainderWidth M) := by
  have hM0 : (0:ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  have hm' := Finset.mem_Ioo.mp hm
  have hL : (sargosSextupleRadius q:ℝ)+2 ≤ m := by
    exact_mod_cast (show sargosSextupleRadius q+2 ≤ m by omega)
  have hR : (m:ℝ)+1 ≤ (M:ℝ)-(sargosSextupleRadius q:ℝ) := by
    exact_mod_cast (show m+1 ≤ (M:ℤ)-sargosSextupleRadius q by omega)
  rw [(sargosRemainder_anchor_formulas hM q).1,
    (sargosRemainder_anchor_formulas hM q).2.1]
  constructor <;> apply (div_le_div_iff_of_pos_right hM0).mpr <;> linarith

theorem sargosRemainder_observation_distances {H M : ℕ} (hM : 1 ≤ M)
    (q : SargosInitialMomentTuple H 3 × SargosInitialMomentTuple H 3)
    (hne : (sargosSextupleInterior M q).Nonempty) {x : ℝ} (hx : x ∈ Icc (0:ℝ) 1) :
    |x-(sargosRemainderLeft M q+2*sargosRemainderWidth M)| ≤ 1 ∧
      |x-(sargosRemainderRight M q-2*sargosRemainderWidth M)| ≤ 1 := by
  obtain ⟨hl,hr,hgap⟩ := sargosRemainder_interval_geometry hM q hne
  have hh := (sargosRemainderWidth_bounds hM).1
  constructor <;> apply abs_le.mpr <;> constructor <;> linarith [hx.1,hx.2]

end TaoTrudgianYang2025
