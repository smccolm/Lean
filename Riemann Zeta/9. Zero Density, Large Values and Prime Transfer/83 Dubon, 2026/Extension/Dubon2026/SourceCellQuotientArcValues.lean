import Dubon2026.SourceOriginalWordPeriodMatrix

/-! DUB-17/18 -> original Abel-Jacobi -> meromorphic loop-period generation.
The residue-period quotient is an additive group, not a complex vector space.
This exact arc-value algebra is needed to apply the constructed polygon and
integer cycles to logarithmic primitives modulo residues. Reuse the existing
original dissection, polygon endpoints, word chains and integer word matrix.
Adapted from S_AlgebraicCurve_CellDissection_kirchhoff_and_jump_formula_of_arc_values,
anthropics/fermats-last-theorem, Apache-2.0,
commit 6e837e75355538c7f80bab5b956861e86c4eacc2.
-/
namespace Dubon2026.SourceFunctionField.CellGeometry.ArcPeriods
noncomputable section
open Set CellDissection DissectionPeriods
variable {N : ℕ} [NeZero N]

/-- The existing integer-cycle expansion for every circulation in the specified group. -/
def FlowDecomp (B : Type*) [AddCommGroup B] (𝒟 : CellDissection N)
    (T : Finset 𝒟.ιE) (Z : 𝒟.ιE → 𝒟.ιE → ℤ) : Prop :=
  ∀ f : 𝒟.ιE → B,
    (∀ w, (∑ e with (𝒟.ends e).2 = w, f e) = ∑ e with (𝒟.ends e).1 = w, f e) →
    ∀ e, f e = ∑ j ∈ Tᶜ, Z j e • f j

/-- The start vertex of an actual cell arc. -/
def sv (𝒟 : CellDissection N) (p : Σ C : 𝒟.ιC, Fin (𝒟.cell C).R.N) : 𝒟.ιV := DissectionPolygon.sV 𝒟 (𝒟.side p.1 p.2)

/-- The end vertex of an actual cell arc. -/
def ev (𝒟 : CellDissection N) (p : Σ C : 𝒟.ιC, Fin (𝒟.cell C).R.N) : 𝒟.ιV := DissectionPolygon.eV 𝒟 (𝒟.side p.1 p.2)

theorem sv_arcOf (𝒟 : CellDissection N) (q : 𝒟.ιE × Bool) : sv 𝒟 (arcOf 𝒟 q) = DissectionPolygon.sV 𝒟 q := by
  simp [sv, side_arcOf]

theorem ev_arcOf (𝒟 : CellDissection N) (q : 𝒟.ιE × Bool) : ev 𝒟 (arcOf 𝒟 q) = DissectionPolygon.eV 𝒟 q := by
  simp [ev, side_arcOf]

/-- Endpoint values, signed integrals and paired jumps in an additive group. -/
structure ArcValues (𝒟 : CellDissection N) {𝔸 : Type*} [AddCommGroup 𝔸] (A B : (Σ C : 𝒟.ιC, Fin (𝒟.cell C).R.N) → 𝔸) (I J : 𝒟.ιE → 𝔸)
    (rot : ∀ C : 𝒟.ιC, Fin (𝒟.cell C).R.N → Fin (𝒟.cell C).R.N) : Prop where
  hW : ∀ p, B p - A p = if (𝒟.side p.1 p.2).2 then I (𝒟.side p.1 p.2).1 else -I (𝒟.side p.1 p.2).1
  hbij : ∀ C, Function.Bijective (rot C)
  hrot : ∀ C k, ev 𝒟 ⟨C, k⟩ = sv 𝒟 ⟨C, rot C k⟩
  hC : ∀ C k, A ⟨C, rot C k⟩ = B ⟨C, k⟩
  hJ1 : ∀ e, J e = B (arcOf 𝒟 (e, true)) - A (arcOf 𝒟 (e, false))
  hJ2 : ∀ e, J e = A (arcOf 𝒟 (e, true)) - B (arcOf 𝒟 (e, false))
  hinj : ∀ C, Function.Injective fun k : Fin (𝒟.cell C).R.N => sv 𝒟 ⟨C, k⟩



theorem ArcValues.kirchhoff {𝒟 : CellDissection N} {𝔸 : Type*} [AddCommGroup 𝔸]
    {A B : (Σ C : 𝒟.ιC, Fin (𝒟.cell C).R.N) → 𝔸} {I J : 𝒟.ιE → 𝔸}
    {rot : ∀ C : 𝒟.ιC, Fin (𝒟.cell C).R.N → Fin (𝒟.cell C).R.N}
    (h : ArcValues 𝒟 A B I J rot) (v : 𝒟.ιV) :
    (∑ e with (𝒟.ends e).2 = v, J e) = ∑ e with (𝒟.ends e).1 = v, J e := by
  classical
  rw [← sub_eq_zero, Finset.sum_filter, Finset.sum_filter]

  have hl : (∑ e, if (𝒟.ends e).2 = v then J e else 0) - ∑ e, (if (𝒟.ends e).1 = v then J e else 0) =
      (∑ q : 𝒟.ιE × Bool, if DissectionPolygon.eV 𝒟 q = v then B (arcOf 𝒟 q) else 0) -
        ∑ q : 𝒟.ιE × Bool, if DissectionPolygon.sV 𝒟 q = v then A (arcOf 𝒟 q) else 0 := by
    rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
    simp only [Fintype.sum_bool, DissectionPolygon.eV, DissectionPolygon.sV, if_true, Bool.false_eq_true, if_false]
    rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun e _ => ?_
    by_cases h2 : (𝒟.ends e).2 = v <;> by_cases h1 : (𝒟.ends e).1 = v <;>
      simp only [h2, h1, if_true, if_false] <;>
      [rw [sub_self, show B (arcOf 𝒟 (e, true)) + B (arcOf 𝒟 (e, false)) -
            (A (arcOf 𝒟 (e, true)) + A (arcOf 𝒟 (e, false))) =
          (B (arcOf 𝒟 (e, true)) - A (arcOf 𝒟 (e, false))) -
            (A (arcOf 𝒟 (e, true)) - B (arcOf 𝒟 (e, false))) by abel, ← h.hJ1 e, ← h.hJ2 e,
          sub_self];
        (rw [h.hJ1 e]; abel); (rw [h.hJ2 e]; abel); abel]
  rw [hl]

  have hB : (∑ q : 𝒟.ιE × Bool, if DissectionPolygon.eV 𝒟 q = v then B (arcOf 𝒟 q) else 0) =
      ∑ p : (Σ C : 𝒟.ιC, Fin (𝒟.cell C).R.N), if ev 𝒟 p = v then B p else 0 := by
    rw [← Function.Bijective.sum_comp 𝒟.side_bij]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [arcOf_side]; rfl
  have hA : (∑ q : 𝒟.ιE × Bool, if DissectionPolygon.sV 𝒟 q = v then A (arcOf 𝒟 q) else 0) =
      ∑ p : (Σ C : 𝒟.ιC, Fin (𝒟.cell C).R.N), if sv 𝒟 p = v then A p else 0 := by
    rw [← Function.Bijective.sum_comp 𝒟.side_bij]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [arcOf_side]; rfl
  rw [hB, hA, Fintype.sum_sigma, Fintype.sum_sigma, ← Finset.sum_sub_distrib]
  refine Finset.sum_eq_zero fun C _ => ?_
  rw [sub_eq_zero]

  rw [← Function.Bijective.sum_comp (h.hbij C) (fun k => if sv 𝒟 ⟨C, k⟩ = v then A ⟨C, k⟩ else 0)]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [h.hrot C k, h.hC C k]


end
end Dubon2026.SourceFunctionField.CellGeometry.ArcPeriods
