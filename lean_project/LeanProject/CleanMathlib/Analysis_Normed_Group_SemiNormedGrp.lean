import Mathlib.Analysis.Normed.Group.Constructions
import Mathlib.Analysis.Normed.Group.Hom
import Mathlib.CategoryTheory.Limits.Shapes.ZeroMorphisms
import Mathlib.CategoryTheory.ConcreteCategory.BundledHom
import Mathlib.CategoryTheory.Elementwise
noncomputable section
universe u
open CategoryTheory
def SemiNormedGrp : Type (u + 1) :=
  Bundled SeminormedAddCommGroup
namespace SemiNormedGrp
instance bundledHom : BundledHom @NormedAddGroupHom where
  toFun := @NormedAddGroupHom.toFun
  id := @NormedAddGroupHom.id
  comp := @NormedAddGroupHom.comp
deriving instance LargeCategory for SemiNormedGrp
instance : ConcreteCategory SemiNormedGrp := by
  dsimp [SemiNormedGrp]
  infer_instance
instance : CoeSort SemiNormedGrp Type* where
  coe X := X.α
def of (M : Type u) [SeminormedAddCommGroup M] : SemiNormedGrp :=
  Bundled.of M
instance (M : SemiNormedGrp) : SeminormedAddCommGroup M :=
  M.str
instance funLike {V W : SemiNormedGrp} : FunLike (V ⟶ W) V W where
  coe := (forget SemiNormedGrp).map
  coe_injective' f g h := by cases f; cases g; congr
instance toAddMonoidHomClass {V W : SemiNormedGrp} : AddMonoidHomClass (V ⟶ W) V W where
  map_add f := f.map_add'
  map_zero f := (AddMonoidHom.mk' f.toFun f.map_add').map_zero
@[ext]
lemma ext {M N : SemiNormedGrp} {f₁ f₂ : M ⟶ N} (h : ∀ (x : M), f₁ x = f₂ x) : f₁ = f₂ :=
  DFunLike.ext _ _ h
@[simp]
theorem coe_of (V : Type u) [SeminormedAddCommGroup V] : (SemiNormedGrp.of V : Type u) = V :=
  rfl
@[simp (high)]
theorem coe_id (V : SemiNormedGrp) : (𝟙 V : V → V) = id :=
  rfl
@[simp (high)]
theorem coe_comp {M N K : SemiNormedGrp} (f : M ⟶ N) (g : N ⟶ K) :
    (f ≫ g : M → K) = g ∘ f :=
  rfl
instance : Inhabited SemiNormedGrp :=
  ⟨of PUnit⟩
instance ofUnique (V : Type u) [SeminormedAddCommGroup V] [i : Unique V] :
    Unique (SemiNormedGrp.of V) :=
  i
instance {M N : SemiNormedGrp} : Zero (M ⟶ N) :=
  NormedAddGroupHom.zero
@[simp]
theorem zero_apply {V W : SemiNormedGrp} (x : V) : (0 : V ⟶ W) x = 0 :=
  rfl
instance : Limits.HasZeroMorphisms.{u, u + 1} SemiNormedGrp where
theorem isZero_of_subsingleton (V : SemiNormedGrp) [Subsingleton V] : Limits.IsZero V := by
  refine ⟨fun X => ⟨⟨⟨0⟩, fun f => ?_⟩⟩, fun X => ⟨⟨⟨0⟩, fun f => ?_⟩⟩⟩
  · ext x; have : x = 0 := Subsingleton.elim _ _; simp only [this, map_zero]
  · ext; apply Subsingleton.elim
instance hasZeroObject : Limits.HasZeroObject SemiNormedGrp.{u} :=
  ⟨⟨of PUnit, isZero_of_subsingleton _⟩⟩
theorem iso_isometry_of_normNoninc {V W : SemiNormedGrp} (i : V ≅ W) (h1 : i.hom.NormNoninc)
    (h2 : i.inv.NormNoninc) : Isometry i.hom := by
  apply AddMonoidHomClass.isometry_of_norm
  intro v
  apply le_antisymm (h1 v)
  calc
    ‖v‖ = ‖i.inv (i.hom v)‖ := by rw [Iso.hom_inv_id_apply]
    _ ≤ ‖i.hom v‖ := h2 _
end SemiNormedGrp
def SemiNormedGrp₁ : Type (u + 1) :=
  Bundled SeminormedAddCommGroup
namespace SemiNormedGrp₁
instance : CoeSort SemiNormedGrp₁ Type* where
  coe X := X.α
instance : LargeCategory.{u} SemiNormedGrp₁ where
  Hom X Y := { f : NormedAddGroupHom X Y // f.NormNoninc }
  id X := ⟨NormedAddGroupHom.id X, NormedAddGroupHom.NormNoninc.id⟩
  comp {_ _ _} f g := ⟨g.1.comp f.1, g.2.comp f.2⟩
instance instFunLike (X Y : SemiNormedGrp₁) : FunLike (X ⟶ Y) X Y where
  coe f := f.1.toFun
  coe_injective' _ _ h := Subtype.val_inj.mp (NormedAddGroupHom.coe_injective h)
@[ext]
theorem hom_ext {M N : SemiNormedGrp₁} (f g : M ⟶ N) (w : (f : M → N) = (g : M → N)) :
    f = g :=
  Subtype.eq (NormedAddGroupHom.ext (congr_fun w))
instance : ConcreteCategory.{u} SemiNormedGrp₁ where
  forget :=
    { obj := fun X => X
      map := fun f => f }
  forget_faithful := { }
instance toAddMonoidHomClass {V W : SemiNormedGrp₁} : AddMonoidHomClass (V ⟶ W) V W where
  map_add f := f.1.map_add'
  map_zero f := (AddMonoidHom.mk' f.1 f.1.map_add').map_zero
def of (M : Type u) [SeminormedAddCommGroup M] : SemiNormedGrp₁ :=
  Bundled.of M
instance (M : SemiNormedGrp₁) : SeminormedAddCommGroup M :=
  M.str
def mkHom {M N : SemiNormedGrp} (f : M ⟶ N) (i : f.NormNoninc) :
    SemiNormedGrp₁.of M ⟶ SemiNormedGrp₁.of N :=
  ⟨f, i⟩
theorem mkHom_apply {M N : SemiNormedGrp} (f : M ⟶ N) (i : f.NormNoninc) (x) :
    mkHom f i x = f x :=
  rfl
@[simps]
def mkIso {M N : SemiNormedGrp} (f : M ≅ N) (i : f.hom.NormNoninc) (i' : f.inv.NormNoninc) :
    SemiNormedGrp₁.of M ≅ SemiNormedGrp₁.of N where
  hom := mkHom f.hom i
  inv := mkHom f.inv i'
  hom_inv_id := by apply Subtype.eq; exact f.hom_inv_id
  inv_hom_id := by apply Subtype.eq; exact f.inv_hom_id
instance : HasForget₂ SemiNormedGrp₁ SemiNormedGrp where
  forget₂ :=
    { obj := fun X => X
      map := fun f => f.1 }
@[simp]
theorem coe_of (V : Type u) [SeminormedAddCommGroup V] : (SemiNormedGrp₁.of V : Type u) = V :=
  rfl
@[simp (high)]
theorem coe_id (V : SemiNormedGrp₁) : ⇑(𝟙 V) = id :=
  rfl
@[simp (high)]
theorem coe_comp {M N K : SemiNormedGrp₁} (f : M ⟶ N) (g : N ⟶ K) :
    (f ≫ g : M → K) = g ∘ f :=
  rfl
instance : Inhabited SemiNormedGrp₁ :=
  ⟨of PUnit⟩
instance ofUnique (V : Type u) [SeminormedAddCommGroup V] [i : Unique V] :
    Unique (SemiNormedGrp₁.of V) :=
  i
instance (X Y : SemiNormedGrp₁) : Zero (X ⟶ Y) where
  zero := ⟨0, NormedAddGroupHom.NormNoninc.zero⟩
@[simp]
theorem zero_apply {V W : SemiNormedGrp₁} (x : V) : (0 : V ⟶ W) x = 0 :=
  rfl
instance : Limits.HasZeroMorphisms.{u, u + 1} SemiNormedGrp₁ where
theorem isZero_of_subsingleton (V : SemiNormedGrp₁) [Subsingleton V] : Limits.IsZero V := by
  refine ⟨fun X => ⟨⟨⟨0⟩, fun f => ?_⟩⟩, fun X => ⟨⟨⟨0⟩, fun f => ?_⟩⟩⟩
  · ext x; have : x = 0 := Subsingleton.elim _ _; simp only [this, map_zero]
  · ext; apply Subsingleton.elim
instance hasZeroObject : Limits.HasZeroObject SemiNormedGrp₁.{u} :=
  ⟨⟨of PUnit, isZero_of_subsingleton _⟩⟩
theorem iso_isometry {V W : SemiNormedGrp₁} (i : V ≅ W) : Isometry i.hom := by
  change Isometry (⟨⟨i.hom, map_zero _⟩, fun _ _ => map_add _ _ _⟩ : V →+ W)
  refine AddMonoidHomClass.isometry_of_norm _ ?_
  intro v
  apply le_antisymm (i.hom.2 v)
  calc
    ‖v‖ = ‖i.inv (i.hom v)‖ := by erw [Iso.hom_inv_id_apply]
    _ ≤ ‖i.hom v‖ := i.inv.2 _
end SemiNormedGrp₁