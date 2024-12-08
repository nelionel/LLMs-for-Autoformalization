import Mathlib.Algebra.Group.Action.Defs
import Mathlib.Algebra.Group.Hom.Defs
assert_not_exists MonoidWithZero
open Function (Injective Surjective)
variable {M N α : Type*}
section
variable [Monoid M] [MulAction M α]
@[to_additive
"Push forward the action of `R` on `M` along a compatible surjective map `f : R →+ S`."]
abbrev Function.Surjective.mulActionLeft {R S M : Type*} [Monoid R] [MulAction R M] [Monoid S]
    [SMul S M] (f : R →* S) (hf : Surjective f) (hsmul : ∀ (c) (x : M), f c • x = c • x) :
    MulAction S M where
  smul := (· • ·)
  one_smul b := by rw [← f.map_one, hsmul, one_smul]
  mul_smul := hf.forall₂.mpr fun a b x ↦ by simp only [← f.map_mul, hsmul, mul_smul]
namespace MulAction
variable (α)
@[to_additive]
abbrev compHom [Monoid N] (g : N →* M) : MulAction N α where
  smul := SMul.comp.smul g
  one_smul _ := by simpa [(· • ·)] using MulAction.one_smul ..
  mul_smul _ _ _ := by simpa [(· • ·)] using MulAction.mul_smul ..
add_decl_doc AddAction.compHom
@[to_additive]
lemma compHom_smul_def
    {E F G : Type*} [Monoid E] [Monoid F] [MulAction F G] (f : E →* F) (a : E) (x : G) :
    letI : MulAction E G := MulAction.compHom _ f
    a • x = (f a) • x := rfl
end MulAction
end
section CompatibleScalar
@[to_additive (attr := simps)
"If the additive action of `M` on `N` is compatible with addition on `N`, then
`fun x ↦ x +ᵥ 0` is an additive monoid homomorphism from `M` to `N`."]
def MonoidHom.smulOneHom {M N} [Monoid M] [MulOneClass N] [MulAction M N] [IsScalarTower M N N] :
    M →* N where
  toFun x := x • (1 : N)
  map_one' := one_smul _ _
  map_mul' x y := by rw [smul_one_mul, smul_smul]
@[to_additive
"A monoid homomorphism between two additive monoids M and N can be equivalently
specified by an additive action of M on N that is compatible with the addition on N."]
def monoidHomEquivMulActionIsScalarTower (M N) [Monoid M] [Monoid N] :
    (M →* N) ≃ {_inst : MulAction M N // IsScalarTower M N N} where
  toFun f := ⟨MulAction.compHom N f, SMul.comp.isScalarTower _⟩
  invFun := fun ⟨_, _⟩ ↦ MonoidHom.smulOneHom
  left_inv f := MonoidHom.ext fun m ↦ mul_one (f m)
  right_inv := fun ⟨_, _⟩ ↦ Subtype.ext <| MulAction.ext <| funext₂ <| smul_one_smul N
end CompatibleScalar
variable (α)
protected def Function.End := α → α
instance : Monoid (Function.End α) where
  one := id
  mul := (· ∘ ·)
  mul_assoc _ _ _ := rfl
  mul_one _ := rfl
  one_mul _ := rfl
  npow n f := f^[n]
  npow_succ _ _ := Function.iterate_succ _ _
instance : Inhabited (Function.End α) := ⟨1⟩
variable {α}
instance Function.End.applyMulAction : MulAction (Function.End α) α where
  smul := (· <| ·)
  one_smul _ := rfl
  mul_smul _ _ _ := rfl
@[simp] lemma Function.End.smul_def (f : Function.End α) (a : α) : f • a = f a := rfl
lemma Function.End.mul_def (f g : Function.End α) : (f * g) = f ∘ g := rfl
lemma Function.End.one_def : (1 : Function.End α) = id := rfl
def MulAction.toEndHom [Monoid M] [MulAction M α] : M →* Function.End α where
  toFun := (· • ·)
  map_one' := funext (one_smul M)
  map_mul' x y := funext (mul_smul x y)
abbrev MulAction.ofEndHom [Monoid M] (f : M →* Function.End α) : MulAction M α :=
  MulAction.compHom α f