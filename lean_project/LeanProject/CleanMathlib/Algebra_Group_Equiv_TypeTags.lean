import Mathlib.Algebra.Group.Equiv.Basic
import Mathlib.Algebra.Group.Prod
import Mathlib.Algebra.Group.TypeTags.Hom
variable {ι G H : Type*}
@[simps]
def AddEquiv.toMultiplicative [AddZeroClass G] [AddZeroClass H] :
    G ≃+ H ≃ (Multiplicative G ≃* Multiplicative H) where
  toFun f :=
  { toFun := AddMonoidHom.toMultiplicative f.toAddMonoidHom
    invFun := AddMonoidHom.toMultiplicative f.symm.toAddMonoidHom
    left_inv := f.left_inv
    right_inv := f.right_inv
    map_mul' := map_add f }
  invFun f :=
  { toFun := AddMonoidHom.toMultiplicative.symm f.toMonoidHom
    invFun := AddMonoidHom.toMultiplicative.symm f.symm.toMonoidHom
    left_inv := f.left_inv
    right_inv := f.right_inv
    map_add' := map_mul f }
  left_inv x := by ext; rfl
  right_inv x := by ext; rfl
@[simps]
def MulEquiv.toAdditive [MulOneClass G] [MulOneClass H] :
    G ≃* H ≃ (Additive G ≃+ Additive H) where
  toFun f :=
  { toFun := MonoidHom.toAdditive f.toMonoidHom
    invFun := MonoidHom.toAdditive f.symm.toMonoidHom
    left_inv := f.left_inv
    right_inv := f.right_inv
    map_add' := map_mul f }
  invFun f :=
  { toFun := MonoidHom.toAdditive.symm f.toAddMonoidHom
    invFun := MonoidHom.toAdditive.symm f.symm.toAddMonoidHom
    left_inv := f.left_inv
    right_inv := f.right_inv
    map_mul' := map_add f }
  left_inv x := by ext; rfl
  right_inv x := by ext; rfl
@[simps]
def AddEquiv.toMultiplicative' [MulOneClass G] [AddZeroClass H] :
    Additive G ≃+ H ≃ (G ≃* Multiplicative H) where
  toFun f :=
  { toFun := AddMonoidHom.toMultiplicative' f.toAddMonoidHom
    invFun := AddMonoidHom.toMultiplicative'' f.symm.toAddMonoidHom
    left_inv := f.left_inv
    right_inv := f.right_inv
    map_mul' := map_add f }
  invFun f :=
  { toFun := AddMonoidHom.toMultiplicative'.symm f.toMonoidHom
    invFun := AddMonoidHom.toMultiplicative''.symm f.symm.toMonoidHom
    left_inv := f.left_inv
    right_inv := f.right_inv
    map_add' := map_mul f }
  left_inv x := by ext; rfl
  right_inv x := by ext; rfl
abbrev MulEquiv.toAdditive' [MulOneClass G] [AddZeroClass H] :
    G ≃* Multiplicative H ≃ (Additive G ≃+ H) :=
  AddEquiv.toMultiplicative'.symm
@[simps]
def AddEquiv.toMultiplicative'' [AddZeroClass G] [MulOneClass H] :
    G ≃+ Additive H ≃ (Multiplicative G ≃* H) where
  toFun f :=
  { toFun := AddMonoidHom.toMultiplicative'' f.toAddMonoidHom
    invFun := AddMonoidHom.toMultiplicative' f.symm.toAddMonoidHom
    left_inv := f.left_inv
    right_inv := f.right_inv
    map_mul' := map_add f }
  invFun f :=
  { toFun := AddMonoidHom.toMultiplicative''.symm f.toMonoidHom
    invFun := AddMonoidHom.toMultiplicative'.symm f.symm.toMonoidHom
    left_inv := f.left_inv
    right_inv := f.right_inv
    map_add' := map_mul f }
  left_inv x := by ext; rfl
  right_inv x := by ext; rfl
abbrev MulEquiv.toAdditive'' [AddZeroClass G] [MulOneClass H] :
    Multiplicative G ≃* H ≃ (G ≃+ Additive H) :=
  AddEquiv.toMultiplicative''.symm
@[simps!] def monoidEndToAdditive (M : Type*) [MulOneClass M] :
    Monoid.End M ≃* AddMonoid.End (Additive M) :=
  { MonoidHom.toAdditive with
    map_mul' := fun _ _ => rfl }
@[simps!] def addMonoidEndToMultiplicative (A : Type*) [AddZeroClass A] :
    AddMonoid.End A ≃* Monoid.End (Multiplicative A) :=
  { AddMonoidHom.toMultiplicative with
    map_mul' := fun _ _ => rfl }
@[simps]
def MulEquiv.piMultiplicative (K : ι → Type*) [∀ i, Add (K i)] :
    Multiplicative (∀ i : ι, K i) ≃* (∀ i : ι, Multiplicative (K i)) where
  toFun x := fun i ↦ Multiplicative.ofAdd <| x.toAdd i
  invFun x := Multiplicative.ofAdd fun i ↦ (x i).toAdd
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
variable (ι) (G) in
abbrev MulEquiv.funMultiplicative [Add G] :
    Multiplicative (ι → G) ≃* (ι → Multiplicative G) :=
  MulEquiv.piMultiplicative fun _ ↦ G
@[simps]
def AddEquiv.piAdditive (K : ι → Type*) [∀ i, Mul (K i)] :
    Additive (∀ i : ι, K i) ≃+ (∀ i : ι, Additive (K i)) where
  toFun x := fun i ↦ Additive.ofMul <| x.toMul i
  invFun x := Additive.ofMul fun i ↦ (x i).toMul
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
variable (ι) (G) in
abbrev AddEquiv.funAdditive [Mul G] :
    Additive (ι → G) ≃+ (ι → Additive G) :=
  AddEquiv.piAdditive fun _ ↦ G
section
variable (G) (H)
@[simps!]
def AddEquiv.additiveMultiplicative [AddZeroClass G] : Additive (Multiplicative G) ≃+ G :=
  MulEquiv.toAdditive' (MulEquiv.refl (Multiplicative G))
@[simps!]
def MulEquiv.multiplicativeAdditive [MulOneClass H] : Multiplicative (Additive H) ≃* H :=
  AddEquiv.toMultiplicative'' (AddEquiv.refl (Additive H))
@[simps]
def MulEquiv.prodMultiplicative [Add G] [Add H] :
    Multiplicative (G × H) ≃* Multiplicative G × Multiplicative H where
  toFun x := (Multiplicative.ofAdd x.toAdd.1,
    Multiplicative.ofAdd x.toAdd.2)
  invFun := fun (x, y) ↦ Multiplicative.ofAdd (x.toAdd, y.toAdd)
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
@[simps]
def AddEquiv.prodAdditive [Mul G] [Mul H] :
    Additive (G × H) ≃+ Additive G × Additive H where
  toFun x := (Additive.ofMul x.toMul.1,
    Additive.ofMul x.toMul.2)
  invFun := fun (x, y) ↦ Additive.ofMul (x.toMul, y.toMul)
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
end