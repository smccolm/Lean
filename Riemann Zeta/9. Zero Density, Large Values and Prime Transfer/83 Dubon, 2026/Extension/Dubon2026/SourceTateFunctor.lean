import Dubon2026.SourceTateModule
import Mathlib.LinearAlgebra.Basis.Defs

/-! DUB-17/18 -> original Tate comparison. Additive maps act on the actual
compatible torsion sequences. Injectivity and torsion preimages yield a p-adic
linear equivalence; the naturality identity retains the original actions.
-/
namespace Dubon2026.TateModule
noncomputable section
section Functorial

variable {p : ℕ} [Fact p.Prime] {M M' M'' : Type*} [AddCommGroup M] [AddCommGroup M']
  [AddCommGroup M'']

/-- Apply an additive homomorphism to every compatible torsion coordinate. -/
def tateMap (p : ℕ) [Fact p.Prime] (f : M →+ M') : TateModule p M →ₗ[ℤ_[p]] TateModule p M' where
  toFun x := ⟨fun n => f ((x : ℕ → M) n), fun n =>
    ⟨by rw [← map_zsmul, TateModule.torsion, map_zero],
     by rw [← map_zsmul, TateModule.compat]⟩⟩
  map_add' x y := Subtype.ext (funext fun n => by
    show f (((x + y : TateModule p M) : ℕ → M) n) = f ((x : ℕ → M) n) + f ((y : ℕ → M) n)
    rw [TateModule.coe_add, Pi.add_apply, map_add])
  map_smul' a x := Subtype.ext (funext fun n => by
    show f (((a • x : TateModule p M) : ℕ → M) n) =
      (((a • (⟨fun n => f ((x : ℕ → M) n), _⟩ : TateModule p M')) : TateModule p M') : ℕ → M') n
    rw [TateModule.smul_apply, TateModule.smul_apply, map_zsmul])

@[scoped simp] theorem coe_tateMap_apply (f : M →+ M') (x : TateModule p M) (n : ℕ) :
    ((tateMap p f x : TateModule p M') : ℕ → M') n = f ((x : ℕ → M) n) := rfl

theorem tateMap_comp_apply (f : M →+ M') (g : M' →+ M'') (x : TateModule p M) :
    tateMap p (g.comp f) x = tateMap p g (tateMap p f x) :=
  Subtype.ext (funext fun _ => rfl)

theorem tateMap_injective (f : M →+ M') (hf : Function.Injective f) :
    Function.Injective (tateMap p f) := by
  intro x y h
  refine Subtype.ext (funext fun n => hf ?_)
  exact congrArg (fun z : TateModule p M' => (z : ℕ → M') n) h

theorem tateMap_surjective (f : M →+ M') (hf : Function.Injective f)
    (hsurj : ∀ y : M', IsOfFinAddOrder y → y ∈ f.range) :
    Function.Surjective (tateMap p f) := by
  intro y
  have hfin : ∀ n, IsOfFinAddOrder ((y : ℕ → M') n) := fun n => by
    refine (isOfFinAddOrder_iff_nsmul_eq_zero).mpr ⟨p ^ n, pow_pos (Fact.out : p.Prime).pos n, ?_⟩
    rw [← Nat.cast_smul_eq_nsmul ℤ]
    exact TateModule.torsion y n
  choose x hx using fun n => (AddMonoidHom.mem_range).1 (hsurj _ (hfin n))
  refine ⟨⟨x, fun n => ⟨hf ?_, hf ?_⟩⟩, Subtype.ext (funext fun n => hx n)⟩
  · rw [map_zsmul, hx, map_zero, TateModule.torsion]
  · rw [map_zsmul, hx, hx, TateModule.compat]

/-- An injection containing every finite-order point induces a Tate equivalence. -/
def tateEquivOfInjective (f : M →+ M') (hf : Function.Injective f)
    (hsurj : ∀ y : M', IsOfFinAddOrder y → y ∈ f.range) :
    TateModule p M ≃ₗ[ℤ_[p]] TateModule p M' :=
  LinearEquiv.ofBijective (tateMap p f) ⟨tateMap_injective f hf, tateMap_surjective f hf hsurj⟩

@[scoped simp] theorem tateEquivOfInjective_apply (f : M →+ M') (hf : Function.Injective f)
    (hsurj : ∀ y : M', IsOfFinAddOrder y → y ∈ f.range) (x : TateModule p M) :
    tateEquivOfInjective f hf hsurj x = tateMap p f x := rfl

theorem tateMap_naturality (u : M →+ M') (S : M →+ M) (T : M' →+ M')
    (h : ∀ m, u (S m) = T (u m)) (x : TateModule p M) :
    tateMap p u (tateMap p S x) = tateMap p T (tateMap p u x) :=
  Subtype.ext (funext fun _ => h _)

end Functorial


end
end Dubon2026.TateModule
