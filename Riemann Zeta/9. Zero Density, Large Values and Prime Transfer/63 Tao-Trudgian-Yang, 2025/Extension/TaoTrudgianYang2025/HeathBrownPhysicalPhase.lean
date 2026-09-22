import TaoTrudgianYang2025.HeathBrownModelJets
import Expdb.Mathlib.IteratedDeriv

/-!
# Physical interval entry for Heath--Brown's derivative estimate

The original phase is translated from a subinterval of [N,2N] to [0,L].
All regularity and derivative bounds are derived from the closed model
interval. No regularity of the phase outside that interval is needed.
-/

noncomputable section

open Set Expdb Filter
open scoped ContDiff Topology

namespace TaoTrudgianYang2025

def heathBrownPhysicalPhase (F : ℝ → ℝ) (T N A s : ℝ) : ℝ → ℝ :=
  fun x => s*T*F ((A+x)/N)

theorem heathBrownPhysicalPoint_mem {N A L x : ℝ}
    (hN : 0 < N) (ha : N ≤ A) (hb : A+L ≤ 2*N) (hx : x ∈ Icc 0 L) :
    (A+x)/N ∈ phaseInterval := by
  constructor
  · apply (le_div_iff₀ hN).mpr
    linarith [hx.1]
  · apply (div_le_iff₀ hN).mpr
    linarith [hx.2]

theorem heathBrownPhysicalPoint_mem_interior {N A L x : ℝ}
    (hN : 0 < N) (ha : N ≤ A) (hb : A+L ≤ 2*N) (hx : x ∈ Ioo 0 L) :
    (A+x)/N ∈ Ioo (1 : ℝ) 2 := by
  constructor
  · apply (lt_div_iff₀ hN).mpr
    linarith [hx.1]
  · apply (div_lt_iff₀ hN).mpr
    linarith [hx.2]

theorem heathBrownPhysicalPhase_contDiffOn {F : ℝ → ℝ} {N A L : ℝ}
    (hF : ContDiffOn ℝ ∞ F phaseInterval)
    (hN : 0 < N) (ha : N ≤ A) (hb : A+L ≤ 2*N) (T s : ℝ) :
    ContDiffOn ℝ ∞ (heathBrownPhysicalPhase F T N A s) (Icc 0 L) := by
  have hc : ContDiffOn ℝ ∞ (fun x => F ((A+x)/N)) (Icc 0 L) :=
    hF.comp (by fun_prop) (fun _ hx => heathBrownPhysicalPoint_mem hN ha hb hx)
  exact contDiffOn_const.mul hc

theorem heathBrownPhysicalPhase_iteratedDeriv
    {F : ℝ → ℝ} {N A L x : ℝ}
    (hF : ContDiffOn ℝ ∞ F phaseInterval)
    (hN : 0 < N) (ha : N ≤ A) (hb : A+L ≤ 2*N)
    (hx : x ∈ Ioo 0 L) (T s : ℝ) (n : ℕ) :
    iteratedDeriv n (heathBrownPhysicalPhase F T N A s) x =
      (s*T)/(N^n)*iteratedDeriv n F ((A+x)/N) := by
  have hL : 0 < L := hx.1.trans hx.2
  have hsrc := heathBrownPhysicalPoint_mem_interior hN ha hb hx
  have hxc : x ∈ Icc (0 : ℝ) L := ⟨hx.1.le,hx.2.le⟩
  have hsrcC : (A+x)/N ∈ phaseInterval := ⟨hsrc.1.le,hsrc.2.le⟩
  have hf : ContDiffOn ℝ n F phaseInterval :=
    hF.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl n)
  have hg : ContDiffOn ℝ n (fun y => F ((A+y)/N)) (Icc (0 : ℝ) L) :=
    hf.comp (by fun_prop) (fun _ hy => heathBrownPhysicalPoint_mem hN ha hb hy)
  have hgAt : ContDiffAt ℝ n (fun y => F ((A+y)/N)) x :=
    (hg x hxc).contDiffAt
      (mem_of_superset (isOpen_Ioo.mem_nhds hx) Ioo_subset_Icc_self)
  have hfAt : ContDiffAt ℝ n F ((A+x)/N) :=
    (hf _ hsrcC).contDiffAt
      (mem_of_superset (isOpen_Ioo.mem_nhds hsrc) Ioo_subset_Icc_self)
  have hpoint (y : ℝ) : N⁻¹*y+A/N = (A+y)/N := by ring
  have hmap : MapsTo (fun y => N⁻¹*y+A/N) (Icc (0 : ℝ) L) phaseInterval := by
    intro y hy
    simpa only [hpoint] using heathBrownPhysicalPoint_mem hN ha hb hy
  have hd := iteratedDerivWithin_comp_affine_of_mapsTo hf
    (uniqueDiffOn_Icc hL) uniqueDiffOn_phaseInterval hxc hmap
  simp only [hpoint] at hd
  rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc hL) hgAt hxc,
    iteratedDerivWithin_eq_iteratedDeriv uniqueDiffOn_phaseInterval hfAt hsrcC] at hd
  unfold heathBrownPhysicalPhase
  rw [iteratedDeriv_const_mul_field,hd,inv_pow]
  ring

theorem heathBrownPhysicalPhase_signed_derivative_bounds
    {σ δ T N A L x : ℝ} {F : ℝ → ℝ} {P : ℕ}
    (hσ : 0 < σ) (hT : 0 < T) (hN : 0 < N)
    (ha : N ≤ A) (hb : A+L ≤ 2*N)
    (hF : IsApproximateModelPhaseFunction F σ P δ)
    (hx : x ∈ Ioo 0 L) (p : ℕ) (hp : p ≤ P)
    (hδ : δ ≤ min (modelPhaseJetLower σ p) 1) :
    modelPhaseJetLower σ p * T / N^(p+1) ≤
        iteratedDeriv (p+1)
          (heathBrownPhysicalPhase F T N A (modelPhaseJetSign σ p)) x ∧
      iteratedDeriv (p+1)
          (heathBrownPhysicalPhase F T N A (modelPhaseJetSign σ p)) x ≤
        (modelPhaseJetCoefficient σ p+1)*T/N^(p+1) := by
  have hs := approximateModelPhase_signedJet_bounds hσ hF
    (heathBrownPhysicalPoint_mem_interior hN ha hb hx) p hp hδ
  rw [heathBrownPhysicalPhase_iteratedDeriv hF.1 hN ha hb hx]
  have ht : 0 ≤ T/N^(p+1) := by positivity
  have hlo := mul_le_mul_of_nonneg_left hs.1 ht
  have hhi := mul_le_mul_of_nonneg_left hs.2 ht
  constructor
  · convert hlo using 1 <;> ring
  · convert hhi using 1 <;> ring

end TaoTrudgianYang2025
