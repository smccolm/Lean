import Dubon2026.SourceCellNeighborArcIdentity

/-! DUB-17/18 -> original Abel-Jacobi -> actual paired cell dissection.
Use the exact six-arc square and refined-window outputs to identify the two
regions sharing each side, its orientation and C1 reversal, and the finite
intersection chains at every boundary point. These are the planar inputs
to pairing the constructed original-curve cells and to their Euler count.
Adapted from anthropics/fermats-last-theorem, Apache-2.0,
commit 6e837e75355538c7f80bab5b956861e86c4eacc2.
The existing rectangle and outer-window constructors provide the geometric
data; no new radial-region existence hypothesis is introduced by consumers.
-/
namespace Dubon2026.SourceFunctionField.CellGeometry.SideIdentity
noncomputable section
open scoped Real
open Set

theorem arcSet_shape {o hm : ℝ} {j k : ℤ} {c : ℂ} {yL : ℝ} {R : RadialRegion}
    (h : IsSquare o hm j k c yL R) (a : Fin R.N) :
    (∃ (m : ℤ) (lo hi : ℝ), (m = j ∨ m = j + 1) ∧ lo < hi ∧ o + k * hm ≤ lo ∧
      hi ≤ o + (k + 1) * hm ∧ R.arcSet a = vseg (o + m * hm) lo hi) ∨
    (∃ n : ℤ, (n = k ∨ n = k + 1) ∧ o + j * hm < o + (j + 1) * hm ∧
      R.arcSet a = hseg (o + n * hm) (o + j * hm) (o + (j + 1) * hm)) := by
  have D := arcData_of_isSquare h
  rcases D.arcSet_cases a with ⟨-, ea⟩ | ⟨-, ea⟩ | ⟨-, ea⟩ | ⟨-, ea⟩ | ⟨-, ea⟩ | ⟨-, ea⟩
  · exact Or.inl ⟨j + 1, c.im, o + (k + 1) * hm, Or.inr rfl, D.hc₁, D.hc₀.le, le_rfl,
      by exact_mod_cast ea⟩
  · exact Or.inr ⟨k + 1, Or.inr rfl, D.hx, by exact_mod_cast ea⟩
  · exact Or.inl ⟨j, yL, o + (k + 1) * hm, Or.inl rfl, D.hL₁, D.hL₀.le, le_rfl, ea⟩
  · exact Or.inl ⟨j, o + k * hm, yL, Or.inl rfl, D.hL₀, le_rfl, D.hL₁.le, ea⟩
  · exact Or.inr ⟨k, Or.inl rfl, D.hx, ea⟩
  · exact Or.inl ⟨j + 1, o + k * hm, c.im, Or.inr rfl, D.hc₀, le_rfl, D.hc₁.le,
      by exact_mod_cast ea⟩

theorem locality {o hm : ℝ} (hhm : 0 < hm) {j k j' k' : ℤ} {c c' : ℂ} {yL yL' : ℝ}
    {R R' : RadialRegion} (h : IsSquare o hm j k c yL R) (h' : IsSquare o hm j' k' c' yL' R')
    (a : Fin R.N) (a' : Fin R'.N) :
    R.arcSet a = R'.arcSet a' →
    (j' = j ∧ k' = k) ∨ (j' = j + 1 ∧ k' = k) ∨ (j = j' + 1 ∧ k' = k) ∨ (j' = j ∧ k' = k + 1) ∨ (j' = j ∧ k = k' + 1) := by
  intro heq
  rcases arcSet_shape h a with ⟨m, lo, hi, hmj, hlt, hlo, hhi, ea⟩ | ⟨n, hn, hxx, ea⟩
  · rcases arcSet_shape h' a' with ⟨m', lo', hi', hmj', -, hlo', hhi', ea'⟩ | ⟨_, -, -, ea'⟩
    · obtain ⟨e₁, e₂, e₃⟩ := vseg_eq_vseg hlt (ea.symm.trans (heq.trans ea'))
      have hmm := int_eq_of_grid₀₀ o hhm m m' e₁
      have hk₁ := int_lt_of_grid₀₁ o hhm k k' (by linarith)
      have hk₂ := int_lt_of_grid₀₁ o hhm k' k (by linarith)
      omega
    · exact absurd (ea.symm.trans (heq.trans ea')) (vseg_ne_hseg hlt)
  · rcases arcSet_shape h' a' with ⟨_, _, _, -, -, -, -, ea'⟩ | ⟨n', hn', -, ea'⟩
    · exact absurd (ea.symm.trans (heq.trans ea')) (hseg_ne_vseg hxx)
    · obtain ⟨e₁, e₂, -⟩ := hseg_eq_hseg hxx (ea.symm.trans (heq.trans ea'))
      have hnn := int_eq_of_grid₀₀ o hhm n n' e₁
      have hjj := int_eq_of_grid₀₀ o hhm j j' e₂
      omega

theorem rightUpper_of_arcSet_eq {o hm : ℝ} (hhm : 0 < hm) {j k : ℤ} {c : ℂ} {yL : ℝ}
    {R : RadialRegion} (h : IsSquare o hm j k c yL R) {J K : ℤ} (hj : j ≤ J) {y : ℝ} (a : Fin R.N)
    (ha : R.arcSet a = {z : ℂ | z.re = o + (J + 1) * hm ∧ z.im ∈ Icc y (o + (K + 1) * hm)}) :
    j = J ∧ k = K ∧ a.val = 0 ∧ c.im = y := by
  have D := arcData_of_isSquare h
  have ha' : R.arcSet a = vseg (o + (J + 1) * hm) y (o + (K + 1) * hm) := ha
  rcases D.arcSet_cases a with ⟨h0, ea⟩ | ⟨-, ea⟩ | ⟨-, ea⟩ | ⟨-, ea⟩ | ⟨-, ea⟩ | ⟨-, ea⟩
  · obtain ⟨e₁, e₂, e₃⟩ := vseg_eq_vseg D.hc₁ (ea.symm.trans ha')
    exact ⟨int_eq_of_grid₁₁ o hhm j J e₁, int_eq_of_grid₁₁ o hhm k K e₃, h0, e₂⟩
  · exact absurd (ea.symm.trans ha') (hseg_ne_vseg D.hx)
  · obtain ⟨e₁, -, -⟩ := vseg_eq_vseg D.hL₁ (ea.symm.trans ha')
    have := int_eq_of_grid₀₁ o hhm j J e₁
    exfalso; omega
  · obtain ⟨e₁, -, -⟩ := vseg_eq_vseg D.hL₀ (ea.symm.trans ha')
    have := int_eq_of_grid₀₁ o hhm j J e₁
    exfalso; omega
  · exact absurd (ea.symm.trans ha') (hseg_ne_vseg D.hx)
  · obtain ⟨-, -, e₃⟩ := vseg_eq_vseg D.hc₀ (ea.symm.trans ha')
    have h₁ := int_lt_of_grid₀₁ o hhm k K (by linarith [D.hc₀])
    have h₂ := int_lt_of_grid₁₁ o hhm K k (by linarith [D.hc₁])
    exfalso; omega

theorem rightLower_of_arcSet_eq {o hm : ℝ} (hhm : 0 < hm) {j k : ℤ} {c : ℂ} {yL : ℝ}
    {R : RadialRegion} (h : IsSquare o hm j k c yL R) {J K : ℤ} (hj : j ≤ J) {y : ℝ} (a : Fin R.N)
    (ha : R.arcSet a = {z : ℂ | z.re = o + (J + 1) * hm ∧ z.im ∈ Icc (o + K * hm) y}) :
    j = J ∧ k = K ∧ a.val = 5 ∧ c.im = y := by
  have D := arcData_of_isSquare h
  have ha' : R.arcSet a = vseg (o + (J + 1) * hm) (o + K * hm) y := ha
  rcases D.arcSet_cases a with ⟨-, ea⟩ | ⟨-, ea⟩ | ⟨-, ea⟩ | ⟨-, ea⟩ | ⟨-, ea⟩ | ⟨h5, ea⟩
  · obtain ⟨-, e₂, -⟩ := vseg_eq_vseg D.hc₁ (ea.symm.trans ha')
    have h₁ := int_lt_of_grid₀₀ o hhm k K (by linarith [D.hc₀])
    have h₂ := int_lt_of_grid₀₁ o hhm K k (by linarith [D.hc₁])
    exfalso; omega
  · exact absurd (ea.symm.trans ha') (hseg_ne_vseg D.hx)
  · obtain ⟨e₁, -, -⟩ := vseg_eq_vseg D.hL₁ (ea.symm.trans ha')
    have := int_eq_of_grid₀₁ o hhm j J e₁
    exfalso; omega
  · obtain ⟨e₁, -, -⟩ := vseg_eq_vseg D.hL₀ (ea.symm.trans ha')
    have := int_eq_of_grid₀₁ o hhm j J e₁
    exfalso; omega
  · exact absurd (ea.symm.trans ha') (hseg_ne_vseg D.hx)
  · obtain ⟨e₁, e₂, e₃⟩ := vseg_eq_vseg D.hc₀ (ea.symm.trans ha')
    exact ⟨int_eq_of_grid₁₁ o hhm j J e₁, int_eq_of_grid₀₀ o hhm k K e₂, h5, e₃⟩

theorem leftUpper_of_arcSet_eq {o hm : ℝ} (hhm : 0 < hm) {j k : ℤ} {c : ℂ} {yL : ℝ}
    {R : RadialRegion} (h : IsSquare o hm j k c yL R) {J K : ℤ} (hj : J ≤ j) {y : ℝ} (a : Fin R.N)
    (ha : R.arcSet a = {z : ℂ | z.re = o + J * hm ∧ z.im ∈ Icc y (o + (K + 1) * hm)}) :
    j = J ∧ k = K ∧ a.val = 2 ∧ yL = y := by
  have D := arcData_of_isSquare h
  have ha' : R.arcSet a = vseg (o + J * hm) y (o + (K + 1) * hm) := ha
  rcases D.arcSet_cases a with ⟨-, ea⟩ | ⟨-, ea⟩ | ⟨h2, ea⟩ | ⟨-, ea⟩ | ⟨-, ea⟩ | ⟨-, ea⟩
  · obtain ⟨e₁, -, -⟩ := vseg_eq_vseg D.hc₁ (ea.symm.trans ha')
    have := int_eq_of_grid₁₀ o hhm j J e₁
    exfalso; omega
  · exact absurd (ea.symm.trans ha') (hseg_ne_vseg D.hx)
  · obtain ⟨e₁, e₂, e₃⟩ := vseg_eq_vseg D.hL₁ (ea.symm.trans ha')
    exact ⟨int_eq_of_grid₀₀ o hhm j J e₁, int_eq_of_grid₁₁ o hhm k K e₃, h2, e₂⟩
  · obtain ⟨-, -, e₃⟩ := vseg_eq_vseg D.hL₀ (ea.symm.trans ha')
    have h₁ := int_lt_of_grid₀₁ o hhm k K (by linarith [D.hL₀])
    have h₂ := int_lt_of_grid₁₁ o hhm K k (by linarith [D.hL₁])
    exfalso; omega
  · exact absurd (ea.symm.trans ha') (hseg_ne_vseg D.hx)
  · obtain ⟨e₁, -, -⟩ := vseg_eq_vseg D.hc₀ (ea.symm.trans ha')
    have := int_eq_of_grid₁₀ o hhm j J e₁
    exfalso; omega

theorem leftLower_of_arcSet_eq {o hm : ℝ} (hhm : 0 < hm) {j k : ℤ} {c : ℂ} {yL : ℝ}
    {R : RadialRegion} (h : IsSquare o hm j k c yL R) {J K : ℤ} (hj : J ≤ j) {y : ℝ} (a : Fin R.N)
    (ha : R.arcSet a = {z : ℂ | z.re = o + J * hm ∧ z.im ∈ Icc (o + K * hm) y}) :
    j = J ∧ k = K ∧ a.val = 3 ∧ yL = y := by
  have D := arcData_of_isSquare h
  have ha' : R.arcSet a = vseg (o + J * hm) (o + K * hm) y := ha
  rcases D.arcSet_cases a with ⟨-, ea⟩ | ⟨-, ea⟩ | ⟨-, ea⟩ | ⟨h3, ea⟩ | ⟨-, ea⟩ | ⟨-, ea⟩
  · obtain ⟨e₁, -, -⟩ := vseg_eq_vseg D.hc₁ (ea.symm.trans ha')
    have := int_eq_of_grid₁₀ o hhm j J e₁
    exfalso; omega
  · exact absurd (ea.symm.trans ha') (hseg_ne_vseg D.hx)
  · obtain ⟨-, e₂, -⟩ := vseg_eq_vseg D.hL₁ (ea.symm.trans ha')
    have h₁ := int_lt_of_grid₀₀ o hhm k K (by linarith [D.hL₀])
    have h₂ := int_lt_of_grid₀₁ o hhm K k (by linarith [D.hL₁])
    exfalso; omega
  · obtain ⟨e₁, e₂, e₃⟩ := vseg_eq_vseg D.hL₀ (ea.symm.trans ha')
    exact ⟨int_eq_of_grid₀₀ o hhm j J e₁, int_eq_of_grid₀₀ o hhm k K e₂, h3, e₃⟩
  · exact absurd (ea.symm.trans ha') (hseg_ne_vseg D.hx)
  · obtain ⟨e₁, -, -⟩ := vseg_eq_vseg D.hc₀ (ea.symm.trans ha')
    have := int_eq_of_grid₁₀ o hhm j J e₁
    exfalso; omega

theorem bottom_of_arcSet_eq {o hm : ℝ} (hhm : 0 < hm) {j k : ℤ} {c : ℂ} {yL : ℝ}
    {R : RadialRegion} (h : IsSquare o hm j k c yL R) {J K : ℤ} (hk : K ≤ k) (a : Fin R.N)
    (ha : R.arcSet a = {z : ℂ | z.im = o + K * hm ∧ z.re ∈ Icc (o + J * hm) (o + (J + 1) * hm)}) :
    j = J ∧ k = K ∧ a.val = 4 := by
  have D := arcData_of_isSquare h
  have ha' : R.arcSet a = hseg (o + K * hm) (o + J * hm) (o + (J + 1) * hm) := ha
  rcases D.arcSet_cases a with ⟨-, ea⟩ | ⟨-, ea⟩ | ⟨-, ea⟩ | ⟨-, ea⟩ | ⟨h4, ea⟩ | ⟨-, ea⟩
  · exact absurd (ea.symm.trans ha') (vseg_ne_hseg D.hc₁)
  · obtain ⟨e₁, -, -⟩ := hseg_eq_hseg D.hx (ea.symm.trans ha')
    have := int_eq_of_grid₁₀ o hhm k K e₁
    exfalso; omega
  · exact absurd (ea.symm.trans ha') (vseg_ne_hseg D.hL₁)
  · exact absurd (ea.symm.trans ha') (vseg_ne_hseg D.hL₀)
  · obtain ⟨e₁, e₂, -⟩ := hseg_eq_hseg D.hx (ea.symm.trans ha')
    exact ⟨int_eq_of_grid₀₀ o hhm j J e₂, int_eq_of_grid₀₀ o hhm k K e₁, h4⟩
  · exact absurd (ea.symm.trans ha') (vseg_ne_hseg D.hc₀)

theorem top_of_arcSet_eq {o hm : ℝ} (hhm : 0 < hm) {j k : ℤ} {c : ℂ} {yL : ℝ}
    {R : RadialRegion} (h : IsSquare o hm j k c yL R) {J K : ℤ} (hk : k ≤ K) (a : Fin R.N)
    (ha : R.arcSet a = {z : ℂ | z.im = o + (K + 1) * hm ∧ z.re ∈ Icc (o + J * hm) (o + (J + 1) * hm)}) :
    j = J ∧ k = K ∧ a.val = 1 := by
  have D := arcData_of_isSquare h
  have ha' : R.arcSet a = hseg (o + (K + 1) * hm) (o + J * hm) (o + (J + 1) * hm) := ha
  rcases D.arcSet_cases a with ⟨-, ea⟩ | ⟨h1, ea⟩ | ⟨-, ea⟩ | ⟨-, ea⟩ | ⟨-, ea⟩ | ⟨-, ea⟩
  · exact absurd (ea.symm.trans ha') (vseg_ne_hseg D.hc₁)
  · obtain ⟨e₁, e₂, -⟩ := hseg_eq_hseg D.hx (ea.symm.trans ha')
    exact ⟨int_eq_of_grid₀₀ o hhm j J e₂, int_eq_of_grid₁₁ o hhm k K e₁, h1⟩
  · exact absurd (ea.symm.trans ha') (vseg_ne_hseg D.hL₁)
  · exact absurd (ea.symm.trans ha') (vseg_ne_hseg D.hL₀)
  · obtain ⟨e₁, -, -⟩ := hseg_eq_hseg D.hx (ea.symm.trans ha')
    have := int_eq_of_grid₀₁ o hhm k K e₁
    exfalso; omega
  · exact absurd (ea.symm.trans ha') (vseg_ne_hseg D.hc₀)


end
end Dubon2026.SourceFunctionField.CellGeometry.SideIdentity
