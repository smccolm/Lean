import Definitions.Def_AlgebraicCurve_CellDissection
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_CellDissection_exists_tree_cotree
attribute [-instance] AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue

open AlgebraicCurve

theorem AlgebraicCurve.CellDissection.exists_tree_cotree
    {F : Type*} [Field F] [Algebra ℂ F]
    [TopologicalSpace (Place ℂ F)] [ChartedSpace ℂ (Place ℂ F)]
    (𝒟 : CellDissection F) [Nonempty 𝒟.ιC]
    (hvert : Function.Injective 𝒟.vert)
    (hends : ∀ v : 𝒟.ιV, ∃ e : 𝒟.ιE, (𝒟.ends e).1 = v ∨ (𝒟.ends e).2 = v)
    (hEuler : (Fintype.card 𝒟.ιV : ℤ) - (Fintype.card 𝒟.ιE : ℤ) + (Fintype.card 𝒟.ιC : ℤ)
      = 2 - 2 * (Module.finrank ℂ ↥(regularDifferentials ℂ F) : ℤ)) :
    let Cside : 𝒟.ιE → Bool → 𝒟.ιC :=
      fun e s => (Function.surjInv 𝒟.side_bij.surjective (e, s)).1
    ∃ (𝒯 𝒯s : Finset 𝒟.ιE),
      (∀ u v : 𝒟.ιV, ∃! c : 𝒟.ιE → ℤ, (∀ e ∉ 𝒯, c e = 0) ∧
        ∀ w, (∑ e with (𝒟.ends e).2 = w, c e) - (∑ e with (𝒟.ends e).1 = w, c e) =
          (if w = v then (1 : ℤ) else 0) - (if w = u then 1 else 0)) ∧
      (∀ C C' : 𝒟.ιC, ∃! c : 𝒟.ιE → ℤ, (∀ e ∉ 𝒯s, c e = 0) ∧
        ∀ D, (∑ e with Cside e true = D, c e) - (∑ e with Cside e false = D, c e) =
          (if D = C' then (1 : ℤ) else 0) - (if D = C then 1 else 0)) ∧
      Disjoint 𝒯 𝒯s ∧
      (𝒯 ∪ 𝒯s)ᶜ.card = 2 * Module.finrank ℂ ↥(regularDifferentials ℂ F) ∧
      ∀ u v : 𝒟.ιV, Relation.ReflTransGen
        (fun a b => ∃ e ∈ 𝒯, 𝒟.ends e = (a, b) ∨ 𝒟.ends e = (b, a)) u v := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_CellDissection_exists_tree_cotree.solution
