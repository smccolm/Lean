import Dubon2026.SourceCellHorizontalSegmentShapes

/-! DUB-17/18 -> original Abel-Jacobi -> actual boundary pairing.
Opposite sides require a decreasing C1 reparametrization; square-to-window
sides require an increasing one before reciprocal reversal. Exact endpoint
and loop identities are retained for the lifted original-cell pairing.
The two external reparametrization files contain the same shared proof;
adapt it once, reusing the existing shifted tangent and cotangent lemmas.
Unused affine-transport generalizations are omitted.
Source: anthropics/fermats-last-theorem, Apache-2.0,
commit 6e837e75355538c7f80bab5b956861e86c4eacc2.
-/
namespace Dubon2026.SourceFunctionField.CellGeometry.SegmentTransport
noncomputable section
open scoped Real
open Set

theorem core_anti {R R' : RadialRegion} {k : Fin R.N} {k' : Fin R'.N} {P : ℝ → ℂ}
    (hP : Function.Injective P) {h h' g : ℝ → ℝ}
    (hL : ∀ s ∈ R.arcIcc k, R.loop s = P (h s))
    (hL' : ∀ t ∈ R'.arcIcc k', R'.loop t = P (h' t))
    (hgh : ∀ s ∈ R.arcIcc k, g (h s) = s) (hhg : ∀ y : ℝ, h (g y) = y)
    (hψ : StrictAntiOn (fun t => g (h' t)) (R'.arcIcc k'))
    (hψC : ContDiffOn ℝ 1 (fun t => g (h' t)) (R'.arcIcc k'))
    (h₁ : R.loop (R.φs k.castSucc) = R'.loop (R'.φs k'.succ))
    (h₂ : R.loop (R.φs k.succ) = R'.loop (R'.φs k'.castSucc)) :
    ∃ ψ : ℝ → ℝ, StrictAntiOn ψ (R'.arcIcc k') ∧ ContDiffOn ℝ 1 ψ (R'.arcIcc k') ∧
      ψ (R'.φs k'.castSucc) = R.φs k.succ ∧ ψ (R'.φs k'.succ) = R.φs k.castSucc ∧
      ∀ t ∈ R'.arcIcc k', R'.loop t = R.loop (ψ t) := by
  have hαβ : R.φs k.castSucc ≤ R.φs k.succ := (R.hmono Fin.castSucc_lt_succ).le
  have hαβ' : R'.φs k'.castSucc ≤ R'.φs k'.succ := (R'.hmono Fin.castSucc_lt_succ).le
  have hα : R.φs k.castSucc ∈ R.arcIcc k := Set.left_mem_Icc.mpr hαβ
  have hβ : R.φs k.succ ∈ R.arcIcc k := Set.right_mem_Icc.mpr hαβ
  have hα' : R'.φs k'.castSucc ∈ R'.arcIcc k' := Set.left_mem_Icc.mpr hαβ'
  have hβ' : R'.φs k'.succ ∈ R'.arcIcc k' := Set.right_mem_Icc.mpr hαβ'
  have e₁ : h' (R'.φs k'.succ) = h (R.φs k.castSucc) := by
    apply hP
    rw [← hL' _ hβ', ← hL _ hα]
    exact h₁.symm
  have e₂ : h' (R'.φs k'.castSucc) = h (R.φs k.succ) := by
    apply hP
    rw [← hL' _ hα', ← hL _ hβ]
    exact h₂.symm
  have hψα : g (h' (R'.φs k'.castSucc)) = R.φs k.succ := by
    rw [e₂, hgh _ hβ]
  have hψβ : g (h' (R'.φs k'.succ)) = R.φs k.castSucc := by
    rw [e₁, hgh _ hα]
  refine ⟨fun t => g (h' t), hψ, hψC, hψα, hψβ, fun t ht => ?_⟩
  have ht' : t ∈ Set.Icc (R'.φs k'.castSucc) (R'.φs k'.succ) := ht
  have hlo : g (h' (R'.φs k'.succ)) ≤ g (h' t) := hψ.antitoneOn ht hβ' ht'.2
  have hhi : g (h' t) ≤ g (h' (R'.φs k'.castSucc)) := hψ.antitoneOn hα' ht ht'.1
  rw [hψβ] at hlo
  rw [hψα] at hhi
  have hmem : g (h' t) ∈ R.arcIcc k := by
    rw [arcIcc_eq]
    exact ⟨hlo, hhi⟩
  show R'.loop t = R.loop (g (h' t))
  rw [hL' t ht, hL _ hmem, hhg]

theorem core_mono {R R' : RadialRegion} {k : Fin R.N} {k' : Fin R'.N} {P : ℝ → ℂ}
    (hP : Function.Injective P) {h h' g : ℝ → ℝ}
    (hL : ∀ s ∈ R.arcIcc k, R.loop s = P (h s))
    (hL' : ∀ t ∈ R'.arcIcc k', R'.loop t = P (h' t))
    (hgh : ∀ s ∈ R.arcIcc k, g (h s) = s) (hhg : ∀ y : ℝ, h (g y) = y)
    (hψ : StrictMonoOn (fun t => g (h' t)) (R'.arcIcc k'))
    (hψC : ContDiffOn ℝ 1 (fun t => g (h' t)) (R'.arcIcc k'))
    (h₁ : R.loop (R.φs k.castSucc) = R'.loop (R'.φs k'.castSucc))
    (h₂ : R.loop (R.φs k.succ) = R'.loop (R'.φs k'.succ)) :
    ∃ ψ : ℝ → ℝ, StrictMonoOn ψ (R'.arcIcc k') ∧ ContDiffOn ℝ 1 ψ (R'.arcIcc k') ∧
      ψ (R'.φs k'.castSucc) = R.φs k.castSucc ∧ ψ (R'.φs k'.succ) = R.φs k.succ ∧
      ∀ t ∈ R'.arcIcc k', R'.loop t = R.loop (ψ t) := by
  have hαβ : R.φs k.castSucc ≤ R.φs k.succ := (R.hmono Fin.castSucc_lt_succ).le
  have hαβ' : R'.φs k'.castSucc ≤ R'.φs k'.succ := (R'.hmono Fin.castSucc_lt_succ).le
  have hα : R.φs k.castSucc ∈ R.arcIcc k := Set.left_mem_Icc.mpr hαβ
  have hβ : R.φs k.succ ∈ R.arcIcc k := Set.right_mem_Icc.mpr hαβ
  have hα' : R'.φs k'.castSucc ∈ R'.arcIcc k' := Set.left_mem_Icc.mpr hαβ'
  have hβ' : R'.φs k'.succ ∈ R'.arcIcc k' := Set.right_mem_Icc.mpr hαβ'
  have e₁ : h' (R'.φs k'.castSucc) = h (R.φs k.castSucc) := by
    apply hP
    rw [← hL' _ hα', ← hL _ hα]
    exact h₁.symm
  have e₂ : h' (R'.φs k'.succ) = h (R.φs k.succ) := by
    apply hP
    rw [← hL' _ hβ', ← hL _ hβ]
    exact h₂.symm
  have hψα : g (h' (R'.φs k'.castSucc)) = R.φs k.castSucc := by
    rw [e₁, hgh _ hα]
  have hψβ : g (h' (R'.φs k'.succ)) = R.φs k.succ := by
    rw [e₂, hgh _ hβ]
  refine ⟨fun t => g (h' t), hψ, hψC, hψα, hψβ, fun t ht => ?_⟩
  have ht' : t ∈ Set.Icc (R'.φs k'.castSucc) (R'.φs k'.succ) := ht
  have hlo : g (h' (R'.φs k'.castSucc)) ≤ g (h' t) := hψ.monotoneOn hα' ht ht'.1
  have hhi : g (h' t) ≤ g (h' (R'.φs k'.succ)) := hψ.monotoneOn ht hβ' ht'.2
  rw [hψα] at hlo
  rw [hψβ] at hhi
  have hmem : g (h' t) ∈ R.arcIcc k := by
    rw [arcIcc_eq]
    exact ⟨hlo, hhi⟩
  show R'.loop t = R.loop (g (h' t))
  rw [hL' t ht, hL _ hmem, hhg]


end
end Dubon2026.SourceFunctionField.CellGeometry.SegmentTransport
