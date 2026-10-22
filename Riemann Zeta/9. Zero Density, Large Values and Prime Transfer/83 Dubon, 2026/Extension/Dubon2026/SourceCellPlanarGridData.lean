import Dubon2026.SourceOriginalGridWindow

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
namespace Dubon2026.SourceFunctionField.CellGeometry.PlanarRegions
noncomputable section
open scoped Real
open Set

/-- The exact constructed six-arc rectangle output. -/
abbrev RectClauses (x₀ x₁ y₀ y₁ : ℝ) (p : ℂ) (yL : ℝ) (R : RadialRegion) : Prop :=
  RectSixArcs.RectangleGeometry x₀ x₁ y₀ y₁ p yL R

/-- The exact constructed grid-window perimeter output. -/
abbrev WindowClauses (o hm : ℝ) (jlo jhi klo khi : ℤ) (cy : ℤ × ℤ → ℝ) (R : RadialRegion) : Prop :=
  R.q = 0 ∧
  R.K = {z : ℂ | z.re ∈ Icc (o + jlo * hm) (o + (jhi + 1) * hm) ∧
  z.im ∈ Icc (o + klo * hm) (o + (khi + 1) * hm)} ∧
  R.Kint = {z : ℂ | z.re ∈ Ioo (o + jlo * hm) (o + (jhi + 1) * hm) ∧
  z.im ∈ Ioo (o + klo * hm) (o + (khi + 1) * hm)} ∧
  R.N = 2 * (jhi - jlo + 1).toNat + 4 * (khi - klo + 1).toNat ∧
  (∀ k k' : Fin R.N, R.arcSet k = R.arcSet k' → k = k') ∧
  (∀ k : Fin R.N,
  (∃ j : ℤ, jlo ≤ j ∧ j ≤ jhi ∧
  R.arcSet k = {z : ℂ | z.im = o + klo * hm ∧ z.re ∈ Icc (o + j * hm) (o + (j + 1) * hm)} ∧
  R.loop (R.φs k.castSucc) = ⟨o + j * hm, o + klo * hm⟩ ∧
  R.loop (R.φs k.succ) = ⟨o + (j + 1) * hm, o + klo * hm⟩ ∧
  (∀ t ∈ R.arcIcc k, R.r t = (-Real.sin t / (-(o + klo * hm)))⁻¹) ∧
  R.arcIcc k ⊆ Ioo π (2 * π)) ∨
  (∃ j : ℤ, jlo ≤ j ∧ j ≤ jhi ∧
  R.arcSet k = {z : ℂ | z.im = o + (khi + 1) * hm ∧
  z.re ∈ Icc (o + j * hm) (o + (j + 1) * hm)} ∧
  R.loop (R.φs k.castSucc) = ⟨o + (j + 1) * hm, o + (khi + 1) * hm⟩ ∧
  R.loop (R.φs k.succ) = ⟨o + j * hm, o + (khi + 1) * hm⟩ ∧
  (∀ t ∈ R.arcIcc k, R.r t = (Real.sin t / (o + (khi + 1) * hm))⁻¹) ∧
  R.arcIcc k ⊆ Ioo 0 π) ∨
  (∃ k₀ : ℤ, klo ≤ k₀ ∧ k₀ ≤ khi ∧
  R.arcSet k = {z : ℂ | z.re = o + jlo * hm ∧ z.im ∈ Icc (cy (jlo, k₀)) (o + (k₀ + 1) * hm)} ∧
  R.loop (R.φs k.castSucc) = ⟨o + jlo * hm, o + (k₀ + 1) * hm⟩ ∧
  R.loop (R.φs k.succ) = ⟨o + jlo * hm, cy (jlo, k₀)⟩ ∧
  (∀ t ∈ R.arcIcc k, R.r t = (-Real.cos t / (-(o + jlo * hm)))⁻¹) ∧
  R.arcIcc k ⊆ Ioo (π / 2) (3 * π / 2)) ∨
  (∃ k₀ : ℤ, klo ≤ k₀ ∧ k₀ ≤ khi ∧
  R.arcSet k = {z : ℂ | z.re = o + jlo * hm ∧ z.im ∈ Icc (o + k₀ * hm) (cy (jlo, k₀))} ∧
  R.loop (R.φs k.castSucc) = ⟨o + jlo * hm, cy (jlo, k₀)⟩ ∧
  R.loop (R.φs k.succ) = ⟨o + jlo * hm, o + k₀ * hm⟩ ∧
  (∀ t ∈ R.arcIcc k, R.r t = (-Real.cos t / (-(o + jlo * hm)))⁻¹) ∧
  R.arcIcc k ⊆ Ioo (π / 2) (3 * π / 2)) ∨
  (∃ k₀ : ℤ, klo ≤ k₀ ∧ k₀ ≤ khi ∧
  R.arcSet k = {z : ℂ | z.re = o + (jhi + 1) * hm ∧ z.im ∈ Icc (o + k₀ * hm) (cy (jhi, k₀))} ∧
  R.loop (R.φs k.castSucc) = ⟨o + (jhi + 1) * hm, o + k₀ * hm⟩ ∧
  R.loop (R.φs k.succ) = ⟨o + (jhi + 1) * hm, cy (jhi, k₀)⟩ ∧
  (∀ t ∈ R.arcIcc k, R.r t = (Real.cos t / (o + (jhi + 1) * hm))⁻¹) ∧
  (R.arcIcc k ⊆ Ioo (-(π / 2)) (π / 2) ∨ R.arcIcc k ⊆ Ioo (3 * π / 2) (5 * π / 2))) ∨
  (∃ k₀ : ℤ, klo ≤ k₀ ∧ k₀ ≤ khi ∧
  R.arcSet k = {z : ℂ | z.re = o + (jhi + 1) * hm ∧
  z.im ∈ Icc (cy (jhi, k₀)) (o + (k₀ + 1) * hm)} ∧
  R.loop (R.φs k.castSucc) = ⟨o + (jhi + 1) * hm, cy (jhi, k₀)⟩ ∧
  R.loop (R.φs k.succ) = ⟨o + (jhi + 1) * hm, o + (k₀ + 1) * hm⟩ ∧
  (∀ t ∈ R.arcIcc k, R.r t = (Real.cos t / (o + (jhi + 1) * hm))⁻¹) ∧
  (R.arcIcc k ⊆ Ioo (-(π / 2)) (π / 2) ∨ R.arcIcc k ⊆ Ioo (3 * π / 2) (5 * π / 2)))) ∧
  (∀ j : ℤ, jlo ≤ j → j ≤ jhi → ∃ k : Fin R.N,
  R.arcSet k = {z : ℂ | z.im = o + klo * hm ∧ z.re ∈ Icc (o + j * hm) (o + (j + 1) * hm)}) ∧
  (∀ j : ℤ, jlo ≤ j → j ≤ jhi → ∃ k : Fin R.N,
  R.arcSet k = {z : ℂ | z.im = o + (khi + 1) * hm ∧ z.re ∈ Icc (o + j * hm) (o + (j + 1) * hm)}) ∧
  (∀ k₀ : ℤ, klo ≤ k₀ → k₀ ≤ khi → ∃ k : Fin R.N,
  R.arcSet k = {z : ℂ | z.re = o + jlo * hm ∧ z.im ∈ Icc (cy (jlo, k₀)) (o + (k₀ + 1) * hm)}) ∧
  (∀ k₀ : ℤ, klo ≤ k₀ → k₀ ≤ khi → ∃ k : Fin R.N,
  R.arcSet k = {z : ℂ | z.re = o + jlo * hm ∧ z.im ∈ Icc (o + k₀ * hm) (cy (jlo, k₀))}) ∧
  (∀ k₀ : ℤ, klo ≤ k₀ → k₀ ≤ khi → ∃ k : Fin R.N,
  R.arcSet k = {z : ℂ | z.re = o + (jhi + 1) * hm ∧ z.im ∈ Icc (o + k₀ * hm) (cy (jhi, k₀))}) ∧
  (∀ k₀ : ℤ, klo ≤ k₀ → k₀ ≤ khi → ∃ k : Fin R.N,
  R.arcSet k = {z : ℂ | z.re = o + (jhi + 1) * hm ∧
  z.im ∈ Icc (cy (jhi, k₀)) (o + (k₀ + 1) * hm)})

/-- The shared square rectangles and refined outer window for planar pairing. -/
structure GridData where
  /-- Common grid-line offset. -/
  o : ℝ
  /-- Positive mesh size. -/
  hm : ℝ
  hhm : 0 < hm
  /-- Leftmost square index. -/
  jlo : ℤ
  /-- Rightmost square index. -/
  jhi : ℤ
  /-- Lowest square index. -/
  klo : ℤ
  /-- Highest square index. -/
  khi : ℤ
  hjlt : jlo + 1 < jhi
  hklt : klo + 1 < khi
  /-- Prescribed centers of the square regions. -/
  ctr : ℤ × ℤ → ℂ
  hctr : ∀ p : ℤ × ℤ, (o + p.1 * hm < (ctr p).re ∧ (ctr p).re < o + (p.1 + 1) * hm) ∧
    (o + p.2 * hm < (ctr p).im ∧ (ctr p).im < o + (p.2 + 1) * hm)
  hzero : (o + jlo * hm < 0 ∧ 0 < o + (jhi + 1) * hm) ∧ (o + klo * hm < 0 ∧
    0 < o + (khi + 1) * hm)
  hcy0 : ∀ k : ℤ, o + k * hm < 0 → 0 < o + (k + 1) * hm → (ctr (jhi, k)).im = 0
  /-- Shared six-arc radial square regions. -/
  base : ℤ × ℤ → RadialRegion
  hbase : ∀ p : ℤ × ℤ,
      (base p).q = ctr p ∧ (base p).N = 6 ∧
      (base p).K = {z : ℂ | z.re ∈ Icc (o + p.1 * hm) (o + (p.1 + 1) * hm) ∧
        z.im ∈ Icc (o + p.2 * hm) (o + (p.2 + 1) * hm)} ∧
      (base p).Kint = {z : ℂ | z.re ∈ Ioo (o + p.1 * hm) (o + (p.1 + 1) * hm) ∧
        z.im ∈ Ioo (o + p.2 * hm) (o + (p.2 + 1) * hm)} ∧
      (∀ k : Fin (base p).N, k.val = 0 → (base p).arcSet k = {z : ℂ | z.re = (o + (p.1 + 1) * hm) ∧
        z.im ∈ Icc (ctr p).im (o + (p.2 + 1) * hm)}) ∧
      (∀ k : Fin (base p).N, k.val = 1 → (base p).arcSet k = {z : ℂ | z.im = (o + (p.2 + 1) * hm) ∧
        z.re ∈ Icc (o + p.1 * hm) (o + (p.1 + 1) * hm)}) ∧
      (∀ k : Fin (base p).N, k.val = 2 → (base p).arcSet k = {z : ℂ | z.re = (o + p.1 * hm) ∧
        z.im ∈ Icc (if p.1 = jlo then (ctr p).im else (ctr (p.1 - 1, p.2)).im)
          (o + (p.2 + 1) * hm)}) ∧
      (∀ k : Fin (base p).N, k.val = 3 → (base p).arcSet k = {z : ℂ | z.re = (o + p.1 * hm) ∧
        z.im ∈ Icc (o + p.2 * hm) (if p.1 = jlo then (ctr p).im else (ctr (p.1 - 1, p.2)).im)}) ∧
      (∀ k : Fin (base p).N, k.val = 4 → (base p).arcSet k = {z : ℂ | z.im = (o + p.2 * hm) ∧
        z.re ∈ Icc (o + p.1 * hm) (o + (p.1 + 1) * hm)}) ∧
      (∀ k : Fin (base p).N, k.val = 5 → (base p).arcSet k = {z : ℂ | z.re = (o + (p.1 + 1) * hm) ∧
        z.im ∈ Icc (o + p.2 * hm) (ctr p).im}) ∧
      (∀ k : Fin ((base p).N + 1), k.val = 0 →
        (base p).loop ((base p).φs k) = ⟨(o + (p.1 + 1) * hm), (ctr p).im⟩) ∧
      (∀ k : Fin ((base p).N + 1), k.val = 1 →
        (base p).loop ((base p).φs k) = ⟨(o + (p.1 + 1) * hm), (o + (p.2 + 1) * hm)⟩) ∧
      (∀ k : Fin ((base p).N + 1), k.val = 2 →
        (base p).loop ((base p).φs k) = ⟨(o + p.1 * hm), (o + (p.2 + 1) * hm)⟩) ∧
      (∀ k : Fin ((base p).N + 1), k.val = 3 →
        (base p).loop ((base p).φs k) = ⟨(o + p.1 * hm), (if p.1 = jlo then (ctr p).im else (ctr
          (p.1 - 1, p.2)).im)⟩) ∧
      (∀ k : Fin ((base p).N + 1), k.val = 4 →
        (base p).loop ((base p).φs k) = ⟨(o + p.1 * hm), (o + p.2 * hm)⟩) ∧
      (∀ k : Fin ((base p).N + 1), k.val = 5 →
        (base p).loop ((base p).φs k) = ⟨(o + (p.1 + 1) * hm), (o + p.2 * hm)⟩) ∧
      (∀ k : Fin ((base p).N + 1), k.val = 6 →
        (base p).loop ((base p).φs k) = ⟨(o + (p.1 + 1) * hm), (ctr p).im⟩) ∧
      (∀ k : Fin (base p).N, k.val = 0 ∨ k.val = 5 →
        (∀ t ∈ (base p).arcIcc k, (base p).r t = (Real.cos t / ((o + (p.1 + 1) * hm) - (ctr p).re))⁻¹)) ∧
      (∀ k : Fin (base p).N, k.val = 1 →
        ∀ t ∈ (base p).arcIcc k, (base p).r t = (Real.sin t / ((o + (p.2 + 1) * hm) - (ctr p).im))⁻¹) ∧
      (∀ k : Fin (base p).N, k.val = 2 ∨ k.val = 3 →
        (∀ t ∈ (base p).arcIcc k, (base p).r t = (-Real.cos t / ((ctr p).re - (o + p.1 * hm)))⁻¹)) ∧
      (∀ k : Fin (base p).N, k.val = 4 →
        ∀ t ∈ (base p).arcIcc k, (base p).r t = (-Real.sin t / ((ctr p).im - (o + p.2 * hm)))⁻¹) ∧
      (∀ k : Fin (base p).N, k.val = 0 → (base p).arcIcc k ⊆ Ico 0 (π / 2)) ∧
      (∀ k : Fin (base p).N, k.val = 1 → (base p).arcIcc k ⊆ Ioo 0 π) ∧
      (∀ k : Fin (base p).N, k.val = 2 ∨ k.val = 3 → (base p).arcIcc k ⊆ Ioo (π / 2) (3 * π / 2)) ∧
      (∀ k : Fin (base p).N, k.val = 4 → (base p).arcIcc k ⊆ Ioo π (2 * π)) ∧
      (∀ k : Fin (base p).N, k.val = 5 → (base p).arcIcc k ⊆ Ioc (3 * π / 2) (2 * π)) ∧
      (∀ z ∈ (base p).K, z ∉ (base p).Kint →
        (base p).loop (if Complex.arg (z - ctr p) < 0 then Complex.arg
          (z - ctr p) + 2 * π else Complex.arg (z - ctr p))
          = z) ∧
      (∀ (k : Fin (base p).N) (t₁ t₂ : ℝ), t₁ ∈ (base p).arcIcc k → t₂ ∈ (base p).arcIcc k →
        t₁ ≤ t₂ →
        (base p).loop '' Icc t₁ t₂ = segment ℝ ((base p).loop t₁) ((base p).loop t₂))
  /-- The outer region with its complete perimeter subdivision. -/
  winReg : RadialRegion
  hwin :
      winReg.q = 0 ∧
      winReg.K = {z : ℂ | z.re ∈ Icc (o + jlo * hm) (o + (jhi + 1) * hm) ∧
        z.im ∈ Icc (o + klo * hm) (o + (khi + 1) * hm)} ∧
      winReg.Kint = {z : ℂ | z.re ∈ Ioo (o + jlo * hm) (o + (jhi + 1) * hm) ∧
        z.im ∈ Ioo (o + klo * hm) (o + (khi + 1) * hm)} ∧
      winReg.N = 2 * (jhi - jlo + 1).toNat + 4 * (khi - klo + 1).toNat ∧
      (∀ k k' : Fin winReg.N, winReg.arcSet k = winReg.arcSet k' → k = k') ∧
      (∀ k : Fin winReg.N,
        (∃ j : ℤ, jlo ≤ j ∧ j ≤ jhi ∧
          winReg.arcSet k = {z : ℂ | z.im = o + klo * hm ∧
            z.re ∈ Icc (o + j * hm) (o + (j + 1) * hm)} ∧
          winReg.loop (winReg.φs k.castSucc) = ⟨o + j * hm, o + klo * hm⟩ ∧
          winReg.loop (winReg.φs k.succ) = ⟨o + (j + 1) * hm, o + klo * hm⟩ ∧
          (∀ t ∈ winReg.arcIcc k, winReg.r t = (-Real.sin t / (-(o + klo * hm)))⁻¹) ∧
          winReg.arcIcc k ⊆ Ioo π (2 * π)) ∨
        (∃ j : ℤ, jlo ≤ j ∧ j ≤ jhi ∧
          winReg.arcSet k = {z : ℂ | z.im = o + (khi + 1) * hm ∧
            z.re ∈ Icc (o + j * hm) (o + (j + 1) * hm)} ∧
          winReg.loop (winReg.φs k.castSucc) = ⟨o + (j + 1) * hm, o + (khi + 1) * hm⟩ ∧
          winReg.loop (winReg.φs k.succ) = ⟨o + j * hm, o + (khi + 1) * hm⟩ ∧
          (∀ t ∈ winReg.arcIcc k, winReg.r t = (Real.sin t / (o + (khi + 1) * hm))⁻¹) ∧
          winReg.arcIcc k ⊆ Ioo 0 π) ∨
        (∃ k₀ : ℤ, klo ≤ k₀ ∧ k₀ ≤ khi ∧
          winReg.arcSet k = {z : ℂ | z.re = o + jlo * hm ∧
            z.im ∈ Icc ((ctr (jlo, k₀)).im) (o + (k₀ + 1) * hm)} ∧
          winReg.loop (winReg.φs k.castSucc) = ⟨o + jlo * hm, o + (k₀ + 1) * hm⟩ ∧
          winReg.loop (winReg.φs k.succ) = ⟨o + jlo * hm, (ctr (jlo, k₀)).im⟩ ∧
          (∀ t ∈ winReg.arcIcc k, winReg.r t = (-Real.cos t / (-(o + jlo * hm)))⁻¹) ∧
          winReg.arcIcc k ⊆ Ioo (π / 2) (3 * π / 2)) ∨
        (∃ k₀ : ℤ, klo ≤ k₀ ∧ k₀ ≤ khi ∧
          winReg.arcSet k = {z : ℂ | z.re = o + jlo * hm ∧
            z.im ∈ Icc (o + k₀ * hm) ((ctr (jlo, k₀)).im)} ∧
          winReg.loop (winReg.φs k.castSucc) = ⟨o + jlo * hm, (ctr (jlo, k₀)).im⟩ ∧
          winReg.loop (winReg.φs k.succ) = ⟨o + jlo * hm, o + k₀ * hm⟩ ∧
          (∀ t ∈ winReg.arcIcc k, winReg.r t = (-Real.cos t / (-(o + jlo * hm)))⁻¹) ∧
          winReg.arcIcc k ⊆ Ioo (π / 2) (3 * π / 2)) ∨
        (∃ k₀ : ℤ, klo ≤ k₀ ∧ k₀ ≤ khi ∧
          winReg.arcSet k = {z : ℂ | z.re = o + (jhi + 1) * hm ∧
            z.im ∈ Icc (o + k₀ * hm) ((ctr (jhi, k₀)).im)} ∧
          winReg.loop (winReg.φs k.castSucc) = ⟨o + (jhi + 1) * hm, o + k₀ * hm⟩ ∧
          winReg.loop (winReg.φs k.succ) = ⟨o + (jhi + 1) * hm, (ctr (jhi, k₀)).im⟩ ∧
          (∀ t ∈ winReg.arcIcc k, winReg.r t = (Real.cos t / (o + (jhi + 1) * hm))⁻¹) ∧
          (winReg.arcIcc k ⊆ Ioo (-(π / 2)) (π / 2) ∨
            winReg.arcIcc k ⊆ Ioo (3 * π / 2) (5 * π / 2))) ∨
        (∃ k₀ : ℤ, klo ≤ k₀ ∧ k₀ ≤ khi ∧
          winReg.arcSet k = {z : ℂ | z.re = o + (jhi + 1) * hm ∧
            z.im ∈ Icc ((ctr (jhi, k₀)).im) (o + (k₀ + 1) * hm)} ∧
          winReg.loop (winReg.φs k.castSucc) = ⟨o + (jhi + 1) * hm, (ctr (jhi, k₀)).im⟩ ∧
          winReg.loop (winReg.φs k.succ) = ⟨o + (jhi + 1) * hm, o + (k₀ + 1) * hm⟩ ∧
          (∀ t ∈ winReg.arcIcc k, winReg.r t = (Real.cos t / (o + (jhi + 1) * hm))⁻¹) ∧
          (winReg.arcIcc k ⊆ Ioo (-(π / 2)) (π / 2) ∨
            winReg.arcIcc k ⊆ Ioo (3 * π / 2) (5 * π / 2)))) ∧
      (∀ j : ℤ, jlo ≤ j → j ≤ jhi → ∃ k : Fin winReg.N,
        winReg.arcSet k = {z : ℂ | z.im = o + klo * hm ∧
          z.re ∈ Icc (o + j * hm) (o + (j + 1) * hm)}) ∧
      (∀ j : ℤ, jlo ≤ j → j ≤ jhi → ∃ k : Fin winReg.N,
        winReg.arcSet k = {z : ℂ | z.im = o + (khi + 1) * hm ∧
          z.re ∈ Icc (o + j * hm) (o + (j + 1) * hm)}) ∧
      (∀ k₀ : ℤ, klo ≤ k₀ → k₀ ≤ khi → ∃ k : Fin winReg.N,
        winReg.arcSet k = {z : ℂ | z.re = o + jlo * hm ∧
          z.im ∈ Icc ((ctr (jlo, k₀)).im) (o + (k₀ + 1) * hm)}) ∧
      (∀ k₀ : ℤ, klo ≤ k₀ → k₀ ≤ khi → ∃ k : Fin winReg.N,
        winReg.arcSet k = {z : ℂ | z.re = o + jlo * hm ∧
          z.im ∈ Icc (o + k₀ * hm) ((ctr (jlo, k₀)).im)}) ∧
      (∀ k₀ : ℤ, klo ≤ k₀ → k₀ ≤ khi → ∃ k : Fin winReg.N,
        winReg.arcSet k = {z : ℂ | z.re = o + (jhi + 1) * hm ∧
          z.im ∈ Icc (o + k₀ * hm) ((ctr (jhi, k₀)).im)}) ∧
      (∀ k₀ : ℤ, klo ≤ k₀ → k₀ ≤ khi → ∃ k : Fin winReg.N,
        winReg.arcSet k = {z : ℂ | z.re = o + (jhi + 1) * hm ∧
          z.im ∈ Icc ((ctr (jhi, k₀)).im) (o + (k₀ + 1) * hm)})

namespace GridData

variable (M : GridData)

/-- Left side of a grid square. -/
def sx (p : ℤ × ℤ) : ℝ := M.o + p.1 * M.hm
/-- Right side of a grid square. -/
def sx' (p : ℤ × ℤ) : ℝ := M.o + (p.1 + 1) * M.hm
/-- Bottom side of a grid square. -/
def sy (p : ℤ × ℤ) : ℝ := M.o + p.2 * M.hm
/-- Top side of a grid square. -/
def sy' (p : ℤ × ℤ) : ℝ := M.o + (p.2 + 1) * M.hm

theorem ctr_mem (p : ℤ × ℤ) :
    (M.sx p < (M.ctr p).re ∧ (M.ctr p).re < M.sx' p) ∧
      (M.sy p < (M.ctr p).im ∧ (M.ctr p).im < M.sy' p) :=
  M.hctr p

/-- Source left-side split, using its own center at the outer boundary. -/
noncomputable def yL (p : ℤ × ℤ) : ℝ :=
  if p.1 = M.jlo then (M.ctr p).im else (M.ctr (p.1 - 1, p.2)).im

theorem yL_mem (p : ℤ × ℤ) : M.sy p < M.yL p ∧ M.yL p < M.sy' p := by
  unfold yL
  split_ifs
  · exact (M.ctr_mem p).2
  · have h := (M.ctr_mem (p.1 - 1, p.2)).2
    exact h

/-- Imaginary coordinate of the prescribed square center. -/
def cy (p : ℤ × ℤ) : ℝ := (M.ctr p).im

theorem cy_mem (p : ℤ × ℤ) : M.o + p.2 * M.hm < M.cy p ∧ M.cy p < M.o + (p.2 + 1) * M.hm :=
  (M.ctr_mem p).2

theorem zero_mem_window :
    (M.sx (M.jlo, M.klo) < 0 ∧ 0 < M.sx' (M.jhi, M.khi)) ∧
      (M.sy (M.jlo, M.klo) < 0 ∧ 0 < M.sy' (M.jhi, M.khi)) :=
  M.hzero

theorem cy_zero : ∀ k : ℤ, M.o + k * M.hm < 0 → 0 < M.o + (k + 1) * M.hm → M.cy (M.jhi, k) = 0 :=
  fun k h1 h2 => M.hcy0 k h1 h2

theorem jlo_le_jhi : M.jlo ≤ M.jhi := by have := M.hjlt; omega
theorem klo_le_khi : M.klo ≤ M.khi := by have := M.hklt; omega

theorem base_spec (p : ℤ × ℤ) :
    RectClauses (M.sx p) (M.sx' p) (M.sy p) (M.sy' p) (M.ctr p) (M.yL p)
      (M.base p) :=
  M.hbase p

theorem base_q (p : ℤ × ℤ) : (M.base p).q = M.ctr p := (M.base_spec p).1
theorem base_N (p : ℤ × ℤ) : (M.base p).N = 6 := (M.base_spec p).2.1

theorem winReg_spec :
    WindowClauses M.o M.hm M.jlo M.jhi M.klo M.khi M.cy M.winReg :=
  M.hwin

theorem winReg_q : M.winReg.q = 0 := M.winReg_spec.1
theorem winReg_Kint : M.winReg.Kint =
    {z : ℂ | z.re ∈ Ioo (M.sx (M.jlo, M.klo)) (M.sx' (M.jhi, M.khi)) ∧
      z.im ∈ Ioo (M.sy (M.jlo, M.klo)) (M.sy' (M.jhi, M.khi))} := M.winReg_spec.2.2.1
theorem winReg_N :
    M.winReg.N = 2 * (M.jhi - M.jlo + 1).toNat + 4 * (M.khi - M.klo + 1).toNat :=
  M.winReg_spec.2.2.2.1
theorem two_le_winReg_N : 2 ≤ M.winReg.N := by
  rw [winReg_N]
  have := M.hjlt
  omega

end GridData

end
end Dubon2026.SourceFunctionField.CellGeometry.PlanarRegions
