import Dubon2026.SourceOriginalPolygonGluing
import Mathlib.Data.ZMod.Basic

/-! DUB-17/18 -> original Abel-Jacobi -> raw reciprocity -> polygon word.
Join actual analytic cells across the dual tree, retaining labeled oriented
edges, original vertex corners and cotree paths. Integer tree lemmas and
radial endpoint facts are reused from the preceding proved construction.
-/
namespace Dubon2026.SourceFunctionField.CellGeometry.DissectionPolygon
noncomputable section
open SourceCurve Set Real IntegerEdgeChains DissectionTrees CyclicBoundaryWords
attribute [local instance] OriginalChart.placeTopology OriginalChart.placeChartedSpace
variable {N : ℕ} [NeZero N] (𝒟 : CellDissection N)

theorem filter_indicator (P : 𝒟.ιE → Prop) [DecidablePred P] (x : 𝒟.ιE) (s : ℤ) :
    (∑ f with P f, s * (if x = f then (1 : ℤ) else 0)) = s * (if P x then 1 else 0) := by
  rw [Finset.sum_filter,
    Finset.sum_eq_single x (fun f _ hne => by rw [if_neg (Ne.symm hne), mul_zero, ite_self])
      (fun h => absurd (Finset.mem_univ x) h)]
  rw [if_pos rfl]
  split_ifs <;> ring

theorem letter_bd (q : 𝒟.ιE × Bool) (w : 𝒟.ιV) :
    (if q.2 then (1 : ℤ) else -1) * (if (𝒟.ends q.1).2 = w then 1 else 0) -
        (if q.2 then (1 : ℤ) else -1) * (if (𝒟.ends q.1).1 = w then 1 else 0) =
      (if eV 𝒟 q = w then 1 else 0) - (if sV 𝒟 q = w then 1 else 0) := by
  obtain ⟨e, σ⟩ := q
  cases σ <;> simp only [eV, sV, Bool.false_eq_true, if_false, if_true] <;> ring

theorem w3_of_w1 {𝒯s : Finset 𝒟.ιE} {m : ℕ} [NeZero m]
    (wd : ZMod m ≃ {q : 𝒟.ιE × Bool // q.1 ∉ 𝒯s})
    (hW1 : ∀ i : ZMod m, eV 𝒟 (wd i).1 = sV 𝒟 (wd (i + 1)).1)
    (e : 𝒟.ιE) (he : e ∉ 𝒯s) :
    let αe : ZMod m := wd.symm ⟨(e, true), he⟩
    let βe : ZMod m := wd.symm ⟨(e, false), he⟩
    let pe : 𝒟.ιE → ℤ := fun e' =>
      ∑ i ∈ Finset.univ.filter
          (fun i : ZMod m => i ≠ αe ∧ (i - αe).val < (βe - αe).val),
        (if (wd i).1.2 then (1 : ℤ) else (-1)) * (if (wd i).1.1 = e' then 1 else 0)
    ∀ w : 𝒟.ιV,
      (∑ f with (𝒟.ends f).2 = w, pe f) = (∑ f with (𝒟.ends f).1 = w, pe f) := by
  intro αe βe pe w
  classical
  set d : ℕ := (βe - αe).val with hd_def
  set S : Finset (ZMod m) :=
    Finset.univ.filter (fun i : ZMod m => i ≠ αe ∧ (i - αe).val < d) with hS_def

  have hcollapse : ∀ (P : 𝒟.ιE → Prop) [DecidablePred P],
      (∑ f with P f, pe f) =
        ∑ i ∈ S, (if (wd i).1.2 then (1 : ℤ) else -1) * (if P (wd i).1.1 then 1 else 0) := by
    intro P _
    simp only [pe]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    exact filter_indicator 𝒟 P _ _
  rw [hcollapse, hcollapse, ← sub_eq_zero, ← Finset.sum_sub_distrib]
  rw [Finset.sum_congr rfl (fun i _ => letter_bd 𝒟 (wd i).1 w)]

  have hαβ : αe ≠ βe := by
    intro h
    have := wd.symm.injective h
    simp at this
  have hd_pos : 0 < d := by
    rw [hd_def]
    exact Nat.pos_of_ne_zero (fun h0 => hαβ (by
      have := (ZMod.val_eq_zero _).1 h0
      exact (sub_eq_zero.1 this).symm))
  have hd_lt : d < m := ZMod.val_lt _
  have hαd : αe + (d : ZMod m) = βe := by
    rw [hd_def, ZMod.natCast_zmod_val, add_sub_cancel]
  have hS : S = (Finset.Ico 1 d).image (fun k : ℕ => αe + (k : ZMod m)) := by
    ext i
    simp only [hS_def, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image,
      Finset.mem_Ico]
    constructor
    · rintro ⟨hiα, hid⟩
      refine ⟨(i - αe).val, ⟨?_, hid⟩, ?_⟩
      · exact Nat.pos_of_ne_zero (fun h0 => hiα (sub_eq_zero.1 ((ZMod.val_eq_zero _).1 h0)))
      · rw [ZMod.natCast_zmod_val, add_sub_cancel]
    · rintro ⟨k, ⟨hk1, hkd⟩, rfl⟩
      have hkval : ((k : ZMod m) - 0).val = k := by
        rw [sub_zero, ZMod.val_cast_of_lt (hkd.trans hd_lt)]
      refine ⟨?_, ?_⟩
      · intro h
        have h' : (k : ZMod m) = 0 := by
          have := congrArg (fun z => z - αe) h
          simpa using this
        rw [h'] at hkval
        simp only [sub_zero, ZMod.val_zero] at hkval
        omega
      · rw [add_sub_cancel_left, ZMod.val_cast_of_lt (hkd.trans hd_lt)]
        exact hkd
  have hinj : Set.InjOn (fun k : ℕ => αe + (k : ZMod m)) ↑(Finset.Ico 1 d) := by
    intro k hk k' hk' hkk'
    simp only [Finset.coe_Ico, Set.mem_Ico] at hk hk'
    have h := add_left_cancel hkk'
    have := congrArg ZMod.val h
    rwa [ZMod.val_cast_of_lt (hk.2.trans hd_lt), ZMod.val_cast_of_lt (hk'.2.trans hd_lt)] at this
  rw [hS, Finset.sum_image hinj]

  set u : ℕ → ℤ := fun k => if eV 𝒟 (wd (αe + (k : ZMod m))).1 = w then 1 else 0 with hu_def
  have hterm : ∀ k ∈ Finset.Ico 1 d,
      ((if eV 𝒟 (wd (αe + (k : ZMod m))).1 = w then (1 : ℤ) else 0) -
        (if sV 𝒟 (wd (αe + (k : ZMod m))).1 = w then 1 else 0)) = u k - u (k - 1) := by
    intro k hk
    rw [Finset.mem_Ico] at hk
    have hk' : αe + (k : ZMod m) = αe + ((k - 1 : ℕ) : ZMod m) + 1 := by
      rw [add_assoc, ← Nat.cast_add_one, Nat.sub_add_cancel hk.1]
    have hsv : sV 𝒟 (wd (αe + (k : ZMod m))).1 = eV 𝒟 (wd (αe + ((k - 1 : ℕ) : ZMod m))).1 := by
      rw [hk', ← hW1]
    simp only [hu_def, hsv]
  rw [Finset.sum_congr rfl hterm, Finset.sum_Ico_eq_sum_range]
  have hshift : ∀ j ∈ Finset.range (d - 1), u (1 + j) - u (1 + j - 1) = u (j + 1) - u j := by
    intro j _
    rw [show 1 + j - 1 = j by omega, add_comm]
  rw [Finset.sum_congr rfl hshift, Finset.sum_range_sub]

  have hlast : u (d - 1) = if (𝒟.ends e).2 = w then 1 else 0 := by
    have h1 : αe + ((d - 1 : ℕ) : ZMod m) + 1 = βe := by
      rw [← hαd, add_assoc, ← Nat.cast_add_one, Nat.sub_add_cancel hd_pos]
    have h2 : eV 𝒟 (wd (αe + ((d - 1 : ℕ) : ZMod m))).1 = (𝒟.ends e).2 := by
      rw [hW1, h1]
      simp [βe, sV]
    show (if eV 𝒟 (wd (αe + ((d - 1 : ℕ) : ZMod m))).1 = w then (1 : ℤ) else 0) = _
    rw [h2]
  have hfirst : u 0 = if (𝒟.ends e).2 = w then 1 else 0 := by
    have h0 : eV 𝒟 (wd (αe + ((0 : ℕ) : ZMod m))).1 = (𝒟.ends e).2 := by
      simp [αe, eV]
    show (if eV 𝒟 (wd (αe + ((0 : ℕ) : ZMod m))).1 = w then (1 : ℤ) else 0) = _
    rw [h0]
  rw [hlast, hfirst, sub_self]

end
end Dubon2026.SourceFunctionField.CellGeometry.DissectionPolygon
