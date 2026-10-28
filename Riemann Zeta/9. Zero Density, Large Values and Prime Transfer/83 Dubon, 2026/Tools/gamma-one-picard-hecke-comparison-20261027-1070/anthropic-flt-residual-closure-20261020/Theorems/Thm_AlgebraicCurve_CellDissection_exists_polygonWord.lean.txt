import Definitions.Def_AlgebraicCurve_CellDissection
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_CellDissection_exists_polygonWord
attribute [-instance] AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue

open AlgebraicCurve

theorem AlgebraicCurve.CellDissection.exists_polygonWord
    {F : Type*} [Field F] [Algebra ℂ F]
    [TopologicalSpace (Place ℂ F)] [ChartedSpace ℂ (Place ℂ F)]
    (𝒟 : CellDissection F)
    (hvert : Function.Injective 𝒟.vert)
    (𝒯s : Finset 𝒟.ιE)
    (h𝒯s : let Cside : 𝒟.ιE → Bool → 𝒟.ιC :=
        fun e s => (Function.surjInv 𝒟.side_bij.surjective (e, s)).1
      ∀ C C' : 𝒟.ιC, ∃! c : 𝒟.ιE → ℤ, (∀ e ∉ 𝒯s, c e = 0) ∧
        ∀ D, (∑ e with Cside e true = D, c e) - (∑ e with Cside e false = D, c e) =
          (if D = C' then (1 : ℤ) else 0) - (if D = C then 1 else 0))
    (hL : ∃ e : 𝒟.ιE, e ∉ 𝒯s) :
    let Cside : 𝒟.ιE → Bool → 𝒟.ιC :=
      fun e s => (Function.surjInv 𝒟.side_bij.surjective (e, s)).1
    let startV : 𝒟.ιE × Bool → 𝒟.ιV := fun q => if q.2 then (𝒟.ends q.1).1 else (𝒟.ends q.1).2
    let endV : 𝒟.ιE × Bool → 𝒟.ιV := fun q => if q.2 then (𝒟.ends q.1).2 else (𝒟.ends q.1).1
    let L := {q : 𝒟.ιE × Bool // q.1 ∉ 𝒯s}
    let m := Fintype.card L
    ∃ (_ : NeZero m) (wd : ZMod m ≃ L),
      (∀ i : ZMod m, endV (wd i).1 = startV (wd (i + 1)).1 ∧
        ∃ cs : List 𝒟.ιC, cs.head? = some (Cside (wd i).1.1 (wd i).1.2) ∧
          cs.getLast? = some (Cside (wd (i + 1)).1.1 (wd (i + 1)).1.2) ∧
          cs.IsChain (fun D D' => ∃ g ∈ 𝒯s,
            ((Cside g true = D ∧ Cside g false = D') ∨
             (Cside g true = D' ∧ Cside g false = D)) ∧
            (endV (wd i).1 = (𝒟.ends g).1 ∨ endV (wd i).1 = (𝒟.ends g).2))) ∧
      ∀ (e : 𝒟.ιE) (he : e ∉ 𝒯s),
        let αe : ZMod m := wd.symm ⟨(e, true), he⟩
        let βe : ZMod m := wd.symm ⟨(e, false), he⟩
        let pe : 𝒟.ιE → ℤ := fun e' =>
          ∑ i ∈ Finset.univ.filter
              (fun i : ZMod m => i ≠ αe ∧ (i - αe).val < (βe - αe).val),
            (if (wd i).1.2 then (1 : ℤ) else (-1)) * (if (wd i).1.1 = e' then 1 else 0)
        ∀ w : 𝒟.ιV,
          (∑ f with (𝒟.ends f).2 = w, pe f) = (∑ f with (𝒟.ends f).1 = w, pe f) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_CellDissection_exists_polygonWord.solution
