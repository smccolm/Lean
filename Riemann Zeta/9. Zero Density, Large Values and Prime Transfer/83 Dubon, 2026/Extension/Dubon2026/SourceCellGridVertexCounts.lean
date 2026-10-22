import Dubon2026.SourceCellGridVertexSets

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
namespace Dubon2026.SourceFunctionField.CellGeometry.GridVertices
noncomputable section
open scoped Real
open Set

variable {o hm : ℝ} {jlo jhi klo khi : ℤ} {ctr : ℤ × ℤ → ℂ}

theorem cornerPt_injective (hhm : 0 < hm) : Function.Injective (cornerPt o hm) := by
  rintro ⟨a, b⟩ ⟨a', b'⟩ h
  have h₁ : o + (a : ℝ) * hm = o + (a' : ℝ) * hm := congrArg Complex.re h
  have h₂ : o + (b : ℝ) * hm = o + (b' : ℝ) * hm := congrArg Complex.im h
  have ha : a = a' := SideIdentity.int_eq_of_grid₀₀ o hhm a a' h₁
  have hb : b = b' := SideIdentity.int_eq_of_grid₀₀ o hhm b b' h₂
  subst ha
  subst hb
  rfl

theorem rightPt_injective (hhm : 0 < hm)
    (hctr : ∀ p : ℤ × ℤ, (o + p.1 * hm < (ctr p).re ∧ (ctr p).re < o + (p.1 + 1) * hm) ∧
      (o + p.2 * hm < (ctr p).im ∧ (ctr p).im < o + (p.2 + 1) * hm)) :
    Function.Injective (rightPt o hm ctr) := by
  rintro ⟨a, b⟩ ⟨a', b'⟩ h
  have h' : (⟨o + ((a : ℝ) + 1) * hm, (ctr (a, b)).im⟩ : ℂ) = ⟨o + ((a' : ℝ) + 1) * hm, (ctr (a', b')).im⟩ := h
  obtain ⟨h₁, h₂⟩ := Complex.mk.inj h'
  have ha : a = a' := SideIdentity.int_eq_of_grid₁₁ o hhm a a' h₁
  have hb₀ : o + (b : ℝ) * hm < (ctr (a, b)).im := (hctr (a, b)).2.1
  have hb₁ : (ctr (a, b)).im < o + ((b : ℝ) + 1) * hm := (hctr (a, b)).2.2
  have hb₀' : o + (b' : ℝ) * hm < (ctr (a', b')).im := (hctr (a', b')).2.1
  have hb₁' : (ctr (a', b')).im < o + ((b' : ℝ) + 1) * hm := (hctr (a', b')).2.2
  have hb : b = b' := strip_eq_strip o hhm hb₀ hb₁ hb₀' hb₁' h₂
  subst ha
  subst hb
  rfl

theorem leftPt_injective (hhm : 0 < hm)
    (hctr : ∀ p : ℤ × ℤ, (o + p.1 * hm < (ctr p).re ∧ (ctr p).re < o + (p.1 + 1) * hm) ∧
      (o + p.2 * hm < (ctr p).im ∧ (ctr p).im < o + (p.2 + 1) * hm)) :
    Function.Injective (leftPt o hm jlo ctr) := by
  intro b b' h
  have h' : (⟨o + (jlo : ℝ) * hm, (ctr (jlo, b)).im⟩ : ℂ) = ⟨o + (jlo : ℝ) * hm, (ctr (jlo, b')).im⟩ := h
  obtain ⟨-, h₂⟩ := Complex.mk.inj h'
  have hb₀ : o + (b : ℝ) * hm < (ctr (jlo, b)).im := (hctr (jlo, b)).2.1
  have hb₁ : (ctr (jlo, b)).im < o + ((b : ℝ) + 1) * hm := (hctr (jlo, b)).2.2
  have hb₀' : o + (b' : ℝ) * hm < (ctr (jlo, b')).im := (hctr (jlo, b')).2.1
  have hb₁' : (ctr (jlo, b')).im < o + ((b' : ℝ) + 1) * hm := (hctr (jlo, b')).2.2
  exact strip_eq_strip o hhm hb₀ hb₁ hb₀' hb₁' h₂

theorem card_corners (hhm : 0 < hm) (hj : jlo ≤ jhi) (hk : klo ≤ khi) :
    (corners o hm jlo jhi klo khi).card = ((jhi - jlo + 1).toNat + 1) * ((khi - klo + 1).toNat + 1) := by
  have h₁ : (Finset.Icc jlo (jhi + 1)).card = (jhi - jlo + 1).toNat + 1 := by
    rw [Int.card_Icc]
    omega
  have h₂ : (Finset.Icc klo (khi + 1)).card = (khi - klo + 1).toNat + 1 := by
    rw [Int.card_Icc]
    omega
  unfold corners
  rw [Finset.card_image_of_injective _ (cornerPt_injective hhm), Finset.card_product, h₁, h₂]

theorem card_rights (hhm : 0 < hm)
    (hctr : ∀ p : ℤ × ℤ, (o + p.1 * hm < (ctr p).re ∧ (ctr p).re < o + (p.1 + 1) * hm) ∧
      (o + p.2 * hm < (ctr p).im ∧ (ctr p).im < o + (p.2 + 1) * hm)) :
    (rights o hm jlo jhi klo khi ctr).card = (jhi - jlo + 1).toNat * (khi - klo + 1).toNat := by
  have h₁ : (Finset.Icc jlo jhi).card = (jhi - jlo + 1).toNat := by
    rw [Int.card_Icc]
    omega
  have h₂ : (Finset.Icc klo khi).card = (khi - klo + 1).toNat := by
    rw [Int.card_Icc]
    omega
  unfold rights
  rw [Finset.card_image_of_injective _ (rightPt_injective hhm hctr), Finset.card_product, h₁, h₂]

theorem card_lefts (hhm : 0 < hm)
    (hctr : ∀ p : ℤ × ℤ, (o + p.1 * hm < (ctr p).re ∧ (ctr p).re < o + (p.1 + 1) * hm) ∧
      (o + p.2 * hm < (ctr p).im ∧ (ctr p).im < o + (p.2 + 1) * hm)) :
    (lefts o hm jlo klo khi ctr).card = (khi - klo + 1).toNat := by
  have h₁ : (Finset.Icc klo khi).card = (khi - klo + 1).toNat := by
    rw [Int.card_Icc]
    omega
  unfold lefts
  rw [Finset.card_image_of_injective _ (leftPt_injective hhm hctr), h₁]

theorem disjoint_corners_rights (hhm : 0 < hm)
    (hctr : ∀ p : ℤ × ℤ, (o + p.1 * hm < (ctr p).re ∧ (ctr p).re < o + (p.1 + 1) * hm) ∧
      (o + p.2 * hm < (ctr p).im ∧ (ctr p).im < o + (p.2 + 1) * hm)) :
    Disjoint (corners o hm jlo jhi klo khi) (rights o hm jlo jhi klo khi ctr) := by
  rw [Finset.disjoint_left]
  intro v hc hr
  obtain ⟨j, k, -, -, -, -, rfl⟩ := mem_corners.mp hc
  obtain ⟨j', k', -, -, -, -, he⟩ := mem_rights.mp hr
  have h₂ : o + (k : ℝ) * hm = (ctr (j', k')).im := congrArg Complex.im he
  have hk₀ : o + (k' : ℝ) * hm < (ctr (j', k')).im := (hctr (j', k')).2.1
  have hk₁ : (ctr (j', k')).im < o + ((k' : ℝ) + 1) * hm := (hctr (j', k')).2.2
  exact strip_ne_grid o hhm hk₀ hk₁ h₂.symm

theorem disjoint_corners_lefts (hhm : 0 < hm)
    (hctr : ∀ p : ℤ × ℤ, (o + p.1 * hm < (ctr p).re ∧ (ctr p).re < o + (p.1 + 1) * hm) ∧
      (o + p.2 * hm < (ctr p).im ∧ (ctr p).im < o + (p.2 + 1) * hm)) :
    Disjoint (corners o hm jlo jhi klo khi) (lefts o hm jlo klo khi ctr) := by
  rw [Finset.disjoint_left]
  intro v hc hl
  obtain ⟨j, k, -, -, -, -, rfl⟩ := mem_corners.mp hc
  obtain ⟨k', -, -, he⟩ := mem_lefts.mp hl
  have h₂ : o + (k : ℝ) * hm = (ctr (jlo, k')).im := congrArg Complex.im he
  have hk₀ : o + (k' : ℝ) * hm < (ctr (jlo, k')).im := (hctr (jlo, k')).2.1
  have hk₁ : (ctr (jlo, k')).im < o + ((k' : ℝ) + 1) * hm := (hctr (jlo, k')).2.2
  exact strip_ne_grid o hhm hk₀ hk₁ h₂.symm

theorem disjoint_rights_lefts (hhm : 0 < hm) :
    Disjoint (rights o hm jlo jhi klo khi ctr) (lefts o hm jlo klo khi ctr) := by
  rw [Finset.disjoint_left]
  intro v hr hl
  obtain ⟨j, k, hj₁, -, -, -, rfl⟩ := mem_rights.mp hr
  obtain ⟨k', -, -, he⟩ := mem_lefts.mp hl
  have h₁ : o + ((j : ℝ) + 1) * hm = o + (jlo : ℝ) * hm := congrArg Complex.re he
  have h₃ : j + 1 = jlo := SideIdentity.int_eq_of_grid₁₀ o hhm j jlo h₁
  omega

theorem card_B₀ (hhm : 0 < hm)
    (hctr : ∀ p : ℤ × ℤ, (o + p.1 * hm < (ctr p).re ∧ (ctr p).re < o + (p.1 + 1) * hm) ∧
      (o + p.2 * hm < (ctr p).im ∧ (ctr p).im < o + (p.2 + 1) * hm))
    (hj : jlo ≤ jhi) (hk : klo ≤ khi) :
    (B₀ o hm jlo jhi klo khi ctr).card =
      ((jhi - jlo + 1).toNat + 1) * ((khi - klo + 1).toNat + 1) +
        (jhi - jlo + 1).toNat * (khi - klo + 1).toNat + (khi - klo + 1).toNat := by
  have d₁ : Disjoint (corners o hm jlo jhi klo khi) (rights o hm jlo jhi klo khi ctr) :=
    disjoint_corners_rights hhm hctr
  have d₂ : Disjoint (corners o hm jlo jhi klo khi ∪ rights o hm jlo jhi klo khi ctr)
      (lefts o hm jlo klo khi ctr) :=
    Finset.disjoint_union_left.mpr ⟨disjoint_corners_lefts hhm hctr, disjoint_rights_lefts hhm⟩
  have c₁ := card_corners (o := o) hhm hj hk
  have c₂ := card_rights (jlo := jlo) (jhi := jhi) (klo := klo) (khi := khi) hhm hctr
  have c₃ := card_lefts (jlo := jlo) (klo := klo) (khi := khi) hhm hctr
  unfold B₀
  rw [Finset.card_union_of_disjoint d₂, Finset.card_union_of_disjoint d₁, c₁, c₂, c₃]


end
end Dubon2026.SourceFunctionField.CellGeometry.GridVertices
