import Mathlib.Combinatorics.Quiver.Path
import Mathlib.Combinatorics.Quiver.Push
universe v u w v'
namespace Quiver
def Symmetrify (V : Type*) := V
instance symmetrifyQuiver (V : Type u) [Quiver V] : Quiver (Symmetrify V) :=
  ⟨fun a b : V ↦ (a ⟶ b) ⊕ (b ⟶ a)⟩
variable (U V W : Type*) [Quiver.{u + 1} U] [Quiver.{v + 1} V] [Quiver.{w + 1} W]
class HasReverse where
  reverse' : ∀ {a b : V}, (a ⟶ b) → (b ⟶ a)
def reverse {V} [Quiver.{v + 1} V] [HasReverse V] {a b : V} : (a ⟶ b) → (b ⟶ a) :=
  HasReverse.reverse'
class HasInvolutiveReverse extends HasReverse V where
  inv' : ∀ {a b : V} (f : a ⟶ b), reverse (reverse f) = f
variable {U V W}
@[simp]
theorem reverse_reverse [h : HasInvolutiveReverse V] {a b : V} (f : a ⟶ b) :
    reverse (reverse f) = f := by apply h.inv'
@[simp]
theorem reverse_inj [h : HasInvolutiveReverse V] {a b : V}
    (f g : a ⟶ b) : reverse f = reverse g ↔ f = g := by
  constructor
  · rintro h
    simpa using congr_arg Quiver.reverse h
  · rintro h
    congr
theorem eq_reverse_iff [h : HasInvolutiveReverse V] {a b : V} (f : a ⟶ b)
    (g : b ⟶ a) : f = reverse g ↔ reverse f = g := by
  rw [← reverse_inj, reverse_reverse]
section MapReverse
variable [HasReverse U] [HasReverse V] [HasReverse W]
class _root_.Prefunctor.MapReverse (φ : U ⥤q V) : Prop where
  map_reverse' : ∀ {u v : U} (e : u ⟶ v), φ.map (reverse e) = reverse (φ.map e)
@[simp]
theorem _root_.Prefunctor.map_reverse (φ : U ⥤q V) [φ.MapReverse]
    {u v : U} (e : u ⟶ v) : φ.map (reverse e) = reverse (φ.map e) :=
  Prefunctor.MapReverse.map_reverse' e
instance _root_.Prefunctor.mapReverseComp
    (φ : U ⥤q V) (ψ : V ⥤q W) [φ.MapReverse] [ψ.MapReverse] :
    (φ ⋙q ψ).MapReverse where
  map_reverse' e := by
    simp only [Prefunctor.comp_map, Prefunctor.MapReverse.map_reverse']
instance _root_.Prefunctor.mapReverseId :
    (Prefunctor.id U).MapReverse where
  map_reverse' _ := rfl
end MapReverse
instance : HasReverse (Symmetrify V) :=
  ⟨fun e => e.swap⟩
instance :
    HasInvolutiveReverse
      (Symmetrify V) where
  toHasReverse := ⟨fun e ↦ e.swap⟩
  inv' e := congr_fun Sum.swap_swap_eq e
@[simp]
theorem symmetrify_reverse {a b : Symmetrify V} (e : a ⟶ b) : reverse e = e.swap :=
  rfl
section Paths
abbrev Hom.toPos {X Y : V} (f : X ⟶ Y) : (Quiver.symmetrifyQuiver V).Hom X Y :=
  Sum.inl f
abbrev Hom.toNeg {X Y : V} (f : X ⟶ Y) : (Quiver.symmetrifyQuiver V).Hom Y X :=
  Sum.inr f
@[simp]
def Path.reverse [HasReverse V] {a : V} : ∀ {b}, Path a b → Path b a
  | _, Path.nil => Path.nil
  | _, Path.cons p e => (Quiver.reverse e).toPath.comp p.reverse
@[simp]
theorem Path.reverse_toPath [HasReverse V] {a b : V} (f : a ⟶ b) :
    f.toPath.reverse = (Quiver.reverse f).toPath :=
  rfl
@[simp]
theorem Path.reverse_comp [HasReverse V] {a b c : V} (p : Path a b) (q : Path b c) :
    (p.comp q).reverse = q.reverse.comp p.reverse := by
  induction q with
  | nil => simp
  | cons _ _ h => simp [h]
@[simp]
theorem Path.reverse_reverse [h : HasInvolutiveReverse V] {a b : V} (p : Path a b) :
    p.reverse.reverse = p := by
  induction p with
  | nil => simp
  | cons _ _ h =>
    rw [Path.reverse, Path.reverse_comp, h, Path.reverse_toPath, Quiver.reverse_reverse]
    rfl
end Paths
namespace Symmetrify
def of : Prefunctor V (Symmetrify V) where
  obj := id
  map := Sum.inl
variable {V' : Type*} [Quiver.{v' + 1} V']
def lift [HasReverse V'] (φ : Prefunctor V V') :
    Prefunctor (Symmetrify V) V' where
  obj := φ.obj
  map f := match f with
  | Sum.inl g => φ.map g
  | Sum.inr g => reverse (φ.map g)
theorem lift_spec [HasReverse V'] (φ : Prefunctor V V') :
    Symmetrify.of.comp (Symmetrify.lift φ) = φ := by
  fapply Prefunctor.ext
  · rintro X
    rfl
  · rintro X Y f
    rfl
theorem lift_reverse [h : HasInvolutiveReverse V']
    (φ : Prefunctor V V') {X Y : Symmetrify V} (f : X ⟶ Y) :
    (Symmetrify.lift φ).map (Quiver.reverse f) = Quiver.reverse ((Symmetrify.lift φ).map f) := by
  dsimp [Symmetrify.lift]; cases f
  · simp only
    rfl
  · simp only [reverse_reverse]
    rfl
theorem lift_unique [HasReverse V'] (φ : V ⥤q V') (Φ : Symmetrify V ⥤q V') (hΦ : (of ⋙q Φ) = φ)
    (hΦinv : ∀ {X Y : Symmetrify V} (f : X ⟶ Y),
      Φ.map (Quiver.reverse f) = Quiver.reverse (Φ.map f)) :
    Φ = Symmetrify.lift φ := by
  subst_vars
  fapply Prefunctor.ext
  · rintro X
    rfl
  · rintro X Y f
    cases f
    · rfl
    · exact hΦinv (Sum.inl _)
@[simps]
def _root_.Prefunctor.symmetrify (φ : U ⥤q V) : Symmetrify U ⥤q Symmetrify V where
  obj := φ.obj
  map := Sum.map φ.map φ.map
instance _root_.Prefunctor.symmetrify_mapReverse (φ : U ⥤q V) :
    Prefunctor.MapReverse φ.symmetrify :=
  ⟨fun e => by cases e <;> rfl⟩
end Symmetrify
namespace Push
variable {V' : Type*} (σ : V → V')
instance [HasReverse V] : HasReverse (Quiver.Push σ) where
  reverse' := fun
              | PushQuiver.arrow f => PushQuiver.arrow (reverse f)
instance [h : HasInvolutiveReverse V] :
    HasInvolutiveReverse (Push σ) where
  reverse' := fun
  | PushQuiver.arrow f => PushQuiver.arrow (reverse f)
  inv' := fun
  | PushQuiver.arrow f => by dsimp [reverse]; congr; apply h.inv'
theorem of_reverse [HasInvolutiveReverse V] (X Y : V) (f : X ⟶ Y) :
    (reverse <| (Push.of σ).map f) = (Push.of σ).map (reverse f) :=
  rfl
instance ofMapReverse [h : HasInvolutiveReverse V] : (Push.of σ).MapReverse :=
  ⟨by simp [of_reverse]⟩
end Push
def IsPreconnected (V) [Quiver.{u + 1} V] :=
  ∀ X Y : V, Nonempty (Path X Y)
end Quiver