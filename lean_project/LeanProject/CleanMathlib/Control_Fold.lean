import Mathlib.Algebra.Group.Opposite
import Mathlib.Algebra.FreeMonoid.Basic
import Mathlib.Control.Traversable.Instances
import Mathlib.Control.Traversable.Lemmas
import Mathlib.CategoryTheory.Endomorphism
import Mathlib.CategoryTheory.Types
import Mathlib.CategoryTheory.Category.KleisliCat
import Mathlib.Tactic.AdaptationNote
universe u v
open ULift CategoryTheory MulOpposite
namespace Monoid
variable {m : Type u → Type u} [Monad m]
variable {α β : Type u}
abbrev Foldl (α : Type u) : Type u :=
  (End α)ᵐᵒᵖ
def Foldl.mk (f : α → α) : Foldl α :=
  op f
def Foldl.get (x : Foldl α) : α → α :=
  unop x
@[simps]
def Foldl.ofFreeMonoid (f : β → α → β) : FreeMonoid α →* Monoid.Foldl β where
  toFun xs := op <| flip (List.foldl f) (FreeMonoid.toList xs)
  map_one' := rfl
  map_mul' := by
    intros
    #adaptation_note 
    simp only [FreeMonoid.toList_mul, unop_op, List.foldl_append, op_inj, Function.flip_def,
      List.foldl_append]
    rfl
abbrev Foldr (α : Type u) : Type u :=
  End α
def Foldr.mk (f : α → α) : Foldr α :=
  f
def Foldr.get (x : Foldr α) : α → α :=
  x
@[simps]
def Foldr.ofFreeMonoid (f : α → β → β) : FreeMonoid α →* Monoid.Foldr β where
  toFun xs := flip (List.foldr f) (FreeMonoid.toList xs)
  map_one' := rfl
  map_mul' _ _ := funext fun _ => List.foldr_append _ _ _ _
abbrev foldlM (m : Type u → Type u) [Monad m] (α : Type u) : Type u :=
  MulOpposite <| End <| KleisliCat.mk m α
def foldlM.mk (f : α → m α) : foldlM m α :=
  op f
def foldlM.get (x : foldlM m α) : α → m α :=
  unop x
@[simps]
def foldlM.ofFreeMonoid [LawfulMonad m] (f : β → α → m β) : FreeMonoid α →* Monoid.foldlM m β where
  toFun xs := op <| flip (List.foldlM f) (FreeMonoid.toList xs)
  map_one' := rfl
  map_mul' := by intros; apply unop_injective; funext; apply List.foldlM_append
abbrev foldrM (m : Type u → Type u) [Monad m] (α : Type u) : Type u :=
  End <| KleisliCat.mk m α
def foldrM.mk (f : α → m α) : foldrM m α :=
  f
def foldrM.get (x : foldrM m α) : α → m α :=
  x
@[simps]
def foldrM.ofFreeMonoid [LawfulMonad m] (f : α → β → m β) : FreeMonoid α →* Monoid.foldrM m β where
  toFun xs := flip (List.foldrM f) (FreeMonoid.toList xs)
  map_one' := rfl
  map_mul' := by intros; funext; apply List.foldrM_append
end Monoid
namespace Traversable
open Monoid Functor
section Defs
variable {α β : Type u} {t : Type u → Type u} [Traversable t]
def foldMap {α ω} [One ω] [Mul ω] (f : α → ω) : t α → ω :=
  traverse (Const.mk' ∘ f)
def foldl (f : α → β → α) (x : α) (xs : t β) : α :=
  (foldMap (Foldl.mk ∘ flip f) xs).get x
def foldr (f : α → β → β) (x : β) (xs : t α) : β :=
  (foldMap (Foldr.mk ∘ f) xs).get x
def toList : t α → List α :=
  List.reverse ∘ foldl (flip List.cons) []
def length (xs : t α) : ℕ :=
  down <| foldl (fun l _ => up <| l.down + 1) (up 0) xs
variable {m : Type u → Type u} [Monad m]
def foldlm (f : α → β → m α) (x : α) (xs : t β) : m α :=
  (foldMap (foldlM.mk ∘ flip f) xs).get x
def foldrm (f : α → β → m β) (x : β) (xs : t α) : m β :=
  (foldMap (foldrM.mk ∘ f) xs).get x
end Defs
section ApplicativeTransformation
variable {α β γ : Type u}
open Function hiding const
def mapFold [Monoid α] [Monoid β] (f : α →* β) : ApplicativeTransformation (Const α) (Const β) where
  app _ := f
  preserves_seq' := by intros; simp only [Seq.seq, map_mul]
  preserves_pure' := by intros; simp only [map_one, pure]
theorem Free.map_eq_map (f : α → β) (xs : List α) :
    f <$> xs = (FreeMonoid.toList (FreeMonoid.map f (FreeMonoid.ofList xs))) :=
  rfl
theorem foldl.unop_ofFreeMonoid (f : β → α → β) (xs : FreeMonoid α) (a : β) :
    unop (Foldl.ofFreeMonoid f xs) a = List.foldl f a (FreeMonoid.toList xs) :=
  rfl
variable {t : Type u → Type u} [Traversable t] [LawfulTraversable t]
open LawfulTraversable
theorem foldMap_hom [Monoid α] [Monoid β] (f : α →* β) (g : γ → α) (x : t γ) :
    f (foldMap g x) = foldMap (f ∘ g) x :=
  calc
    f (foldMap g x) = f (traverse (Const.mk' ∘ g) x) := rfl
    _ = (mapFold f).app _ (traverse (Const.mk' ∘ g) x) := rfl
    _ = traverse ((mapFold f).app _ ∘ Const.mk' ∘ g) x := naturality (mapFold f) _ _
    _ = foldMap (f ∘ g) x := rfl
theorem foldMap_hom_free [Monoid β] (f : FreeMonoid α →* β) (x : t α) :
    f (foldMap FreeMonoid.of x) = foldMap (f ∘ FreeMonoid.of) x :=
  foldMap_hom f _ x
end ApplicativeTransformation
section Equalities
open LawfulTraversable
open List (cons)
variable {α β γ : Type u}
variable {t : Type u → Type u} [Traversable t] [LawfulTraversable t]
@[simp]
theorem foldl.ofFreeMonoid_comp_of (f : α → β → α) :
    Foldl.ofFreeMonoid f ∘ FreeMonoid.of = Foldl.mk ∘ flip f :=
  rfl
@[simp]
theorem foldr.ofFreeMonoid_comp_of (f : β → α → α) :
    Foldr.ofFreeMonoid f ∘ FreeMonoid.of = Foldr.mk ∘ f :=
  rfl
@[simp]
theorem foldlm.ofFreeMonoid_comp_of {m} [Monad m] [LawfulMonad m] (f : α → β → m α) :
    foldlM.ofFreeMonoid f ∘ FreeMonoid.of = foldlM.mk ∘ flip f := by
  ext1 x
  #adaptation_note 
  simp only [foldlM.ofFreeMonoid, Function.flip_def, MonoidHom.coe_mk, OneHom.coe_mk,
    Function.comp_apply, FreeMonoid.toList_of, List.foldlM_cons, List.foldlM_nil, bind_pure,
    foldlM.mk, op_inj]
  rfl
@[simp]
theorem foldrm.ofFreeMonoid_comp_of {m} [Monad m] [LawfulMonad m] (f : β → α → m α) :
    foldrM.ofFreeMonoid f ∘ FreeMonoid.of = foldrM.mk ∘ f := by
  ext
  #adaptation_note 
  simp [(· ∘ ·), foldrM.ofFreeMonoid, foldrM.mk, Function.flip_def]
theorem toList_spec (xs : t α) : toList xs = FreeMonoid.toList (foldMap FreeMonoid.of xs) :=
  Eq.symm <|
    calc
      FreeMonoid.toList (foldMap FreeMonoid.of xs) =
          FreeMonoid.toList (foldMap FreeMonoid.of xs).reverse.reverse := by
          simp only [FreeMonoid.reverse_reverse]
      _ = (List.foldr cons [] (foldMap FreeMonoid.of xs).toList.reverse).reverse := by
          simp only [FreeMonoid.reverse_reverse, List.foldr_reverse, List.foldl_flip_cons_eq_append,
            List.append_nil, List.reverse_reverse]
      _ = (unop (Foldl.ofFreeMonoid (flip cons) (foldMap FreeMonoid.of xs)) []).reverse := by
            #adaptation_note 
            simp [Function.flip_def, List.foldr_reverse, Foldl.ofFreeMonoid, unop_op]
      _ = toList xs := by
            rw [foldMap_hom_free (Foldl.ofFreeMonoid (flip <| @cons α))]
            simp only [toList, foldl, List.reverse_inj, Foldl.get, foldl.ofFreeMonoid_comp_of,
              Function.comp_apply]
theorem foldMap_map [Monoid γ] (f : α → β) (g : β → γ) (xs : t α) :
    foldMap g (f <$> xs) = foldMap (g ∘ f) xs := by
  simp only [foldMap, traverse_map, Function.comp_def]
theorem foldl_toList (f : α → β → α) (xs : t β) (x : α) :
    foldl f x xs = List.foldl f x (toList xs) := by
  rw [← FreeMonoid.toList_ofList (toList xs), ← foldl.unop_ofFreeMonoid]
  simp only [foldl, toList_spec, foldMap_hom_free, foldl.ofFreeMonoid_comp_of, Foldl.get,
    FreeMonoid.ofList_toList]
theorem foldr_toList (f : α → β → β) (xs : t α) (x : β) :
    foldr f x xs = List.foldr f x (toList xs) := by
  change _ = Foldr.ofFreeMonoid _ (FreeMonoid.ofList <| toList xs) _
  rw [toList_spec, foldr, Foldr.get, FreeMonoid.ofList_toList, foldMap_hom_free,
    foldr.ofFreeMonoid_comp_of]
theorem toList_map (f : α → β) (xs : t α) : toList (f <$> xs) = f <$> toList xs := by
  simp only [toList_spec, Free.map_eq_map, foldMap_hom, foldMap_map, FreeMonoid.ofList_toList,
    FreeMonoid.map_of, Function.comp_def]
@[simp]
theorem foldl_map (g : β → γ) (f : α → γ → α) (a : α) (l : t β) :
    foldl f a (g <$> l) = foldl (fun x y => f x (g y)) a l := by
  #adaptation_note 
  simp only [foldl, foldMap_map, Function.comp_def, Function.flip_def]
@[simp]
theorem foldr_map (g : β → γ) (f : γ → α → α) (a : α) (l : t β) :
    foldr f a (g <$> l) = foldr (f ∘ g) a l := by
  simp only [foldr, foldMap_map, Function.comp_def, flip]
@[simp]
theorem toList_eq_self {xs : List α} : toList xs = xs := by
  simp only [toList_spec, foldMap, traverse]
  induction xs with
  | nil => rfl
  | cons _ _ ih => (conv_rhs => rw [← ih]); rfl
theorem length_toList {xs : t α} : length xs = List.length (toList xs) := by
  unfold length
  rw [foldl_toList]
  generalize toList xs = ys
  rw [← Nat.add_zero ys.length]
  generalize 0 = n
  induction ys generalizing n with
  | nil => simp
  | cons _ _ ih => simp_arith [ih]
variable {m : Type u → Type u} [Monad m] [LawfulMonad m]
theorem foldlm_toList {f : α → β → m α} {x : α} {xs : t β} :
    foldlm f x xs = List.foldlM f x (toList xs) :=
  calc foldlm f x xs
    _ = unop (foldlM.ofFreeMonoid f (FreeMonoid.ofList <| toList xs)) x := by
      simp only [foldlm, toList_spec, foldMap_hom_free (foldlM.ofFreeMonoid f),
        foldlm.ofFreeMonoid_comp_of, foldlM.get, FreeMonoid.ofList_toList]
    _ = List.foldlM f x (toList xs) := by simp [foldlM.ofFreeMonoid, unop_op, flip]
theorem foldrm_toList (f : α → β → m β) (x : β) (xs : t α) :
    foldrm f x xs = List.foldrM f x (toList xs) := by
  change _ = foldrM.ofFreeMonoid f (FreeMonoid.ofList <| toList xs) x
  simp only [foldrm, toList_spec, foldMap_hom_free (foldrM.ofFreeMonoid f),
    foldrm.ofFreeMonoid_comp_of, foldrM.get, FreeMonoid.ofList_toList]
@[simp]
theorem foldlm_map (g : β → γ) (f : α → γ → m α) (a : α) (l : t β) :
    foldlm f a (g <$> l) = foldlm (fun x y => f x (g y)) a l := by
  #adaptation_note 
  simp only [foldlm, foldMap_map, Function.comp_def, Function.flip_def]
@[simp]
theorem foldrm_map (g : β → γ) (f : γ → α → m α) (a : α) (l : t β) :
    foldrm f a (g <$> l) = foldrm (f ∘ g) a l := by
  simp only [foldrm, foldMap_map, Function.comp_def, flip]
end Equalities
end Traversable