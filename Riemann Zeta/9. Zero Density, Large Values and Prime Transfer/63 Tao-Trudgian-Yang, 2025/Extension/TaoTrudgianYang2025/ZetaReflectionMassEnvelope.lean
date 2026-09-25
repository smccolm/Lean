import TaoTrudgianYang2025.ZetaReflectionExponentWitness

/-! An actual pointwise-to-affine-supremum reflection comparison, retaining all EReal cases. -/

noncomputable section
open Complex Filter MeasureTheory Set Topology
namespace TaoTrudgianYang2025

def zetaReflectionMassEnvelope (σ τ : ℝ) : EReal :=
  ⨆ (v : ℝ) (_hv : v ∈ Icc (σ+τ/2-1) (τ-1)),
    ((τ-1 : ℝ) : EReal)*zetaLargeValueExponent (v/(τ-1)) (τ/(τ-1))+
      ((v-(σ+τ/2-1) : ℝ) : EReal)

theorem zetaLargeValueExponent_le_reflectionMassEnvelope {σ τ : ℝ}
    (hσ : 1/2 ≤ σ) (hτ : 1 < τ) :
    zetaLargeValueExponent σ τ ≤ zetaReflectionMassEnvelope σ τ := by
  by_contra hnot
  obtain ⟨B,hlo,hhi⟩ := EReal.exists_between_coe_real (lt_of_not_ge hnot)
  have hfail : ¬ IsZetaLargeValueBound σ τ B := by
    intro hb
    exact (not_le_of_gt hhi) (zetaLargeValueExponent_le_of_bound hb)
  obtain ⟨η,hη,v,hv,hw⟩ := exists_reflection_exponent_witness hσ hτ hfail
  let E := zetaLargeValueExponent (v/(τ-1)) (τ/(τ-1))
  have hκ : 0 < τ-1 := sub_pos.mpr hτ
  have hτp : 0 < τ := zero_lt_one.trans hτ
  have hupper : E ≤ ((τ/(τ-1) : ℝ) : EReal) :=
    zetaLargeValueExponent_le_tau _ (by positivity)
  have htop : E ≠ ⊤ := ne_of_lt (hupper.trans_lt (EReal.coe_lt_top _))
  have hbot : E ≠ ⊥ := by
    intro hb
    change (((B+η+(σ+τ/2-1)-v)/(τ-1) : ℝ) : EReal) ≤ E at hw
    rw [hb] at hw
    exact (not_le_of_gt (EReal.bot_lt_coe _)) hw
  have he := EReal.coe_toReal htop hbot
  have hw' : (B+η+(σ+τ/2-1)-v)/(τ-1) ≤ E.toReal := by
    apply EReal.coe_le_coe_iff.mp
    rw [he]
    exact hw
  have hr := (div_le_iff₀ hκ).mp hw'
  have hb : B < (τ-1)*E.toReal+v-(σ+τ/2-1) := by nlinarith
  have hterm : (((τ-1)*E.toReal+v-(σ+τ/2-1) : ℝ) : EReal) ≤
      zetaReflectionMassEnvelope σ τ := by
    calc
      _ = ((τ-1 : ℝ) : EReal)*(E.toReal : EReal)+((v-(σ+τ/2-1) : ℝ) : EReal) := by
        rw [← EReal.coe_mul,← EReal.coe_add]
        congr 1
        ring
      _ = ((τ-1 : ℝ) : EReal)*E+((v-(σ+τ/2-1) : ℝ) : EReal) := by rw [he]
      _ ≤ _ := by
        dsimp only [E,zetaReflectionMassEnvelope]
        exact le_iSup_of_le v (le_iSup_of_le hv le_rfl)
  have hB : (B : EReal) < zetaReflectionMassEnvelope σ τ :=
    (EReal.coe_lt_coe_iff.mpr hb).trans_le hterm
  exact (not_lt_of_gt hlo) hB

end TaoTrudgianYang2025
