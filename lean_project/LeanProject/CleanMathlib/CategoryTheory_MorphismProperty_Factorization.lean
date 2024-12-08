import Mathlib.CategoryTheory.MorphismProperty.Basic
namespace CategoryTheory
namespace MorphismProperty
variable {C : Type*} [Category C] (W₁ W₂ : MorphismProperty C)
structure MapFactorizationData {X Y : C} (f : X ⟶ Y) where
  Z : C
  i : X ⟶ Z
  p : Z ⟶ Y
  fac : i ≫ p = f := by aesop_cat
  hi : W₁ i
  hp : W₂ p
attribute [reassoc (attr := simp)] MapFactorizationData.fac
abbrev FactorizationData := ∀ {X Y : C} (f : X ⟶ Y), MapFactorizationData W₁ W₂ f
class HasFactorization : Prop where
  nonempty_mapFactorizationData {X Y : C} (f : X ⟶ Y) : Nonempty (MapFactorizationData W₁ W₂ f)
noncomputable def factorizationData [HasFactorization W₁ W₂] : FactorizationData W₁ W₂ :=
  fun _ => Nonempty.some (HasFactorization.nonempty_mapFactorizationData _)
def comp : MorphismProperty C := fun _ _ f => Nonempty (MapFactorizationData W₁ W₂ f)
lemma comp_eq_top_iff : W₁.comp W₂ = ⊤ ↔ HasFactorization W₁ W₂ := by
  constructor
  · intro h
    refine ⟨fun f => ?_⟩
    have : W₁.comp W₂ f := by simp only [h, top_apply]
    exact ⟨this.some⟩
  · intro
    ext X Y f
    simp only [top_apply, iff_true]
    exact ⟨factorizationData W₁ W₂ f⟩
structure FunctorialFactorizationData where
  Z : Arrow C ⥤ C
  i : Arrow.leftFunc ⟶ Z
  p : Z ⟶ Arrow.rightFunc
  fac : i ≫ p = Arrow.leftToRight := by aesop_cat
  hi (f : Arrow C) : W₁ (i.app f)
  hp (f : Arrow C) : W₂ (p.app f)
namespace FunctorialFactorizationData
variable {W₁ W₂}
variable (data : FunctorialFactorizationData W₁ W₂)
attribute [reassoc (attr := simp)] fac
@[reassoc (attr := simp)]
lemma fac_app {f : Arrow C} : data.i.app f ≫ data.p.app f = f.hom := by
  rw [← NatTrans.comp_app, fac,Arrow.leftToRight_app]
def ofLE {W₁' W₂' : MorphismProperty C} (le₁ : W₁ ≤ W₁') (le₂ : W₂ ≤ W₂') :
    FunctorialFactorizationData W₁' W₂' where
  Z := data.Z
  i := data.i
  p := data.p
  hi f := le₁ _ (data.hi f)
  hp f := le₂ _ (data.hp f)
def factorizationData : FactorizationData W₁ W₂ := fun f =>
  { i := data.i.app (Arrow.mk f)
    p := data.p.app (Arrow.mk f)
    hi := data.hi _
    hp := data.hp _ }
section
variable {X Y X' Y' : C} {f : X ⟶ Y} {g : X' ⟶ Y'} (φ : Arrow.mk f ⟶ Arrow.mk g)
def mapZ : (data.factorizationData f).Z ⟶ (data.factorizationData g).Z := data.Z.map φ
@[reassoc (attr := simp)]
lemma i_mapZ :
    (data.factorizationData f).i ≫ data.mapZ φ = φ.left ≫ (data.factorizationData g).i :=
  (data.i.naturality φ).symm
@[reassoc (attr := simp)]
lemma mapZ_p :
    data.mapZ φ ≫ (data.factorizationData g).p = (data.factorizationData f).p ≫ φ.right :=
  data.p.naturality φ
variable (f) in
@[simp]
lemma mapZ_id : data.mapZ (𝟙 (Arrow.mk f)) = 𝟙 _ :=
  data.Z.map_id _
@[reassoc, simp]
lemma mapZ_comp {X'' Y'' : C} {h : X'' ⟶ Y''} (ψ : Arrow.mk g ⟶ Arrow.mk h) :
    data.mapZ (φ ≫ ψ) = data.mapZ φ ≫ data.mapZ ψ :=
  data.Z.map_comp _ _
end
section
variable (J : Type*) [Category J]
@[simps]
def functorCategory.Z : Arrow (J ⥤ C) ⥤ J ⥤ C where
  obj f :=
    { obj := fun j => (data.factorizationData (f.hom.app j)).Z
      map := fun φ => data.mapZ
        { left := f.left.map φ
          right := f.right.map φ }
      map_id := fun j => by
        dsimp
        rw [← data.mapZ_id (f.hom.app j)]
        congr <;> simp
      map_comp := fun _ _ => by
        dsimp
        rw [← data.mapZ_comp]
        congr <;> simp }
  map τ :=
    { app := fun j => data.mapZ
        { left := τ.left.app j
          right := τ.right.app j
          w := congr_app τ.w j }
      naturality := fun _ _ α => by
        dsimp
        rw [← data.mapZ_comp, ← data.mapZ_comp]
        congr 1
        ext <;> simp }
  map_id f := by
    ext j
    dsimp
    rw [← data.mapZ_id]
    congr 1
  map_comp f g := by
    ext j
    dsimp
    rw [← data.mapZ_comp]
    congr 1
def functorCategory :
    FunctorialFactorizationData (W₁.functorCategory J) (W₂.functorCategory J) where
  Z := functorCategory.Z data J
  i := { app := fun f => { app := fun j => (data.factorizationData (f.hom.app j)).i } }
  p := { app := fun f => { app := fun j => (data.factorizationData (f.hom.app j)).p } }
  hi _ _ := data.hi _
  hp _ _ := data.hp _
end
end FunctorialFactorizationData
class HasFunctorialFactorization : Prop where
  nonempty_functorialFactorizationData : Nonempty (FunctorialFactorizationData W₁ W₂)
noncomputable def functorialFactorizationData [HasFunctorialFactorization W₁ W₂] :
    FunctorialFactorizationData W₁ W₂ :=
  Nonempty.some (HasFunctorialFactorization.nonempty_functorialFactorizationData)
instance [HasFunctorialFactorization W₁ W₂] : HasFactorization W₁ W₂ where
  nonempty_mapFactorizationData f := ⟨(functorialFactorizationData W₁ W₂).factorizationData f⟩
instance [HasFunctorialFactorization W₁ W₂] (J : Type*) [Category J] :
    HasFunctorialFactorization (W₁.functorCategory J) (W₂.functorCategory J) :=
  ⟨⟨(functorialFactorizationData W₁ W₂).functorCategory J⟩⟩
end MorphismProperty
end CategoryTheory