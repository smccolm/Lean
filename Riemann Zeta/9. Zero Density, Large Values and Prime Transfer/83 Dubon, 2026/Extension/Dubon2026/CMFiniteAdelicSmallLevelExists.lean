import Dubon2026.CMFiniteAdelicPrincipalLevel
import Dubon2026.NumberFieldLargeResiduePrime

/-! # Existence of actual compact open arithmetic small levels

For the specified definite CM form, a principal level with trivial
arithmetic stabilizers exists away from any finite list of rational
primes. This closes the basic level-existence obligation in DUB-17's
auxiliary module chain. Prescribed local splitting and form conditions,
parabolic refinements and finite arithmetic double cosets remain required.
-/

namespace Dubon2026

noncomputable section

open NumberField IsDedekindDomain
open scoped NumberField ComplexOrder

/-- The original definite CM unitary group has a compact open small principal level outside any finite prime list. -/
theorem cmFiniteAdelic_exists_principal_small_level
    (K : Type) [Field K] [NumberField K] [IsCMField K]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (H : Matrix ι ι K) (hH : ∀ φ : K →+* ℂ, (φ.mapMatrix H).PosDef)
    (T : Finset ℕ) :
    ∃ (v : HeightOneSpectrum (𝓞 K)) (p : ℕ), p.Prime ∧ p ∉ T ∧
      CharP (Valued.ResidueField (v.adicCompletion K)) p ∧
      Fintype.card ι * Module.finrank ℚ K < p - 1 ∧
      IsOpen (cmFiniteAdelicPrincipalLevel K H v : Set (cmFiniteAdelicUnitaryGroup K H)) ∧
      IsCompact (cmFiniteAdelicPrincipalLevel K H v : Set (cmFiniteAdelicUnitaryGroup K H)) ∧
      ∀ (g : cmFiniteAdelicUnitaryGroup K H) (u : cmFiniteAdelicPrincipalLevel K H v),
        g * u.val * g⁻¹ ∈ ((cmHermitianFiniteAdeleHom H).codRestrict
          (cmFiniteAdelicUnitaryGroup K H) (cmFiniteAdelicUnitaryGroup_principal K H)).range →
            u = 1 := by
  obtain ⟨v, p, hp, hlarge, hpT, hchar⟩ :=
    numberField_exists_large_residue_prime K (Fintype.card ι * Module.finrank ℚ K) T
  letI := hchar
  exact ⟨v, p, hp, hpT, hchar, hlarge, cmFiniteAdelicPrincipalLevel_isOpen K H v,
    cmFiniteAdelicPrincipalLevel_isCompact K H v,
    cmFiniteAdelicPrincipalLevel_small K H hH v p hp hlarge⟩

end
end Dubon2026
