import Mathlib.CategoryTheory.ConcreteCategory.BundledHom
import Mathlib.Topology.ContinuousMap.Basic
open CategoryTheory TopologicalSpace Topology
universe u
@[to_additive existing TopCat]
def TopCat : Type (u + 1) :=
  Bundled TopologicalSpace
namespace TopCat
instance bundledHom : BundledHom @ContinuousMap where
  toFun := @ContinuousMap.toFun
  id := @ContinuousMap.id
  comp := @ContinuousMap.comp
deriving instance LargeCategory for TopCat
instance concreteCategory : ConcreteCategory TopCat :=
  inferInstanceAs <| ConcreteCategory (Bundled TopologicalSpace)
instance : CoeSort TopCat Type* where
  coe X := X.α
instance topologicalSpaceUnbundled (X : TopCat) : TopologicalSpace X :=
  X.str
instance instFunLike (X Y : TopCat) : FunLike (X ⟶ Y) X Y :=
  inferInstanceAs <| FunLike C(X, Y) X Y
instance instContinuousMapClass (X Y : TopCat) : ContinuousMapClass (X ⟶ Y) X Y :=
  inferInstanceAs <| ContinuousMapClass C(X, Y) X Y
@[simp]
theorem id_app (X : TopCat.{u}) (x : ↑X) : (𝟙 X : X ⟶ X) x = x := rfl
@[simp]
theorem comp_app {X Y Z : TopCat.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (x : X) :
    (f ≫ g : X → Z) x = g (f x) := rfl
@[simp] theorem coe_id (X : TopCat.{u}) : (𝟙 X : X → X) = id := rfl
@[simp] theorem coe_comp {X Y Z : TopCat.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g : X → Z) = g ∘ f := rfl
@[simp]
lemma hom_inv_id_apply {X Y : TopCat} (f : X ≅ Y) (x : X) : f.inv (f.hom x) = x :=
  DFunLike.congr_fun f.hom_inv_id x
@[simp]
lemma inv_hom_id_apply {X Y : TopCat} (f : X ≅ Y) (y : Y) : f.hom (f.inv y) = y :=
  DFunLike.congr_fun f.inv_hom_id y
def of (X : Type u) [TopologicalSpace X] : TopCat :=
  ⟨X, inferInstance⟩
instance topologicalSpace_coe (X : TopCat) : TopologicalSpace X :=
  X.str
@[instance] abbrev topologicalSpace_forget
    (X : TopCat) : TopologicalSpace <| (forget TopCat).obj X :=
  X.str
@[simp]
theorem coe_of (X : Type u) [TopologicalSpace X] : (of X : Type u) = X := rfl
@[simp] theorem coe_of_of {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    {f : C(X, Y)} {x} :
    @DFunLike.coe (TopCat.of X ⟶ TopCat.of Y) ((CategoryTheory.forget TopCat).obj (TopCat.of X))
      (fun _ ↦ (CategoryTheory.forget TopCat).obj (TopCat.of Y)) ConcreteCategory.instFunLike
      f x =
    @DFunLike.coe C(X, Y) X
      (fun _ ↦ Y) _
      f x :=
  rfl
instance inhabited : Inhabited TopCat :=
  ⟨TopCat.of Empty⟩
lemma hom_apply {X Y : TopCat} (f : X ⟶ Y) (x : X) : f x = ContinuousMap.toFun f x := rfl
def discrete : Type u ⥤ TopCat.{u} where
  obj X := ⟨X , ⊥⟩
  map f := @ContinuousMap.mk _ _ ⊥ ⊥ f continuous_bot
instance {X : Type u} : DiscreteTopology (discrete.obj X) :=
  ⟨rfl⟩
def trivial : Type u ⥤ TopCat.{u} where
  obj X := ⟨X, ⊤⟩
  map f := @ContinuousMap.mk _ _ ⊤ ⊤ f continuous_top
@[simps]
def isoOfHomeo {X Y : TopCat.{u}} (f : X ≃ₜ Y) : X ≅ Y where
  hom := (f : C(X, Y))
  inv := (f.symm : C(Y, X))
  hom_inv_id := by ext; exact f.symm_apply_apply _
  inv_hom_id := by ext; exact f.apply_symm_apply _
@[simps]
def homeoOfIso {X Y : TopCat.{u}} (f : X ≅ Y) : X ≃ₜ Y where
  toFun := f.hom
  invFun := f.inv
  left_inv x := by simp
  right_inv x := by simp
  continuous_toFun := f.hom.continuous
  continuous_invFun := f.inv.continuous
@[simp]
theorem of_isoOfHomeo {X Y : TopCat.{u}} (f : X ≃ₜ Y) : homeoOfIso (isoOfHomeo f) = f := by
  dsimp [homeoOfIso, isoOfHomeo]
  ext
  rfl
@[simp]
theorem of_homeoOfIso {X Y : TopCat.{u}} (f : X ≅ Y) : isoOfHomeo (homeoOfIso f) = f := by
  dsimp [homeoOfIso, isoOfHomeo]
  ext
  rfl
lemma isIso_of_bijective_of_isOpenMap {X Y : TopCat.{u}} (f : X ⟶ Y)
    (hfbij : Function.Bijective f) (hfcl : IsOpenMap f) : IsIso f :=
  let e : X ≃ₜ Y := Homeomorph.homeomorphOfContinuousOpen
    (Equiv.ofBijective f hfbij) f.continuous hfcl
  inferInstanceAs <| IsIso (TopCat.isoOfHomeo e).hom
lemma isIso_of_bijective_of_isClosedMap {X Y : TopCat.{u}} (f : X ⟶ Y)
    (hfbij : Function.Bijective f) (hfcl : IsClosedMap f) : IsIso f :=
  let e : X ≃ₜ Y := Homeomorph.homeomorphOfContinuousClosed
    (Equiv.ofBijective f hfbij) f.continuous hfcl
  inferInstanceAs <| IsIso (TopCat.isoOfHomeo e).hom
theorem isOpenEmbedding_iff_comp_isIso {X Y Z : TopCat} (f : X ⟶ Y) (g : Y ⟶ Z) [IsIso g] :
    IsOpenEmbedding (f ≫ g) ↔ IsOpenEmbedding f :=
  (TopCat.homeoOfIso (asIso g)).isOpenEmbedding.of_comp_iff f
@[deprecated (since := "2024-10-18")]
alias openEmbedding_iff_comp_isIso := isOpenEmbedding_iff_comp_isIso
@[simp]
theorem isOpenEmbedding_iff_comp_isIso' {X Y Z : TopCat} (f : X ⟶ Y) (g : Y ⟶ Z) [IsIso g] :
    IsOpenEmbedding ((forget TopCat).map f ≫ (forget TopCat).map g) ↔ IsOpenEmbedding f := by
  simp only [← Functor.map_comp]
  exact isOpenEmbedding_iff_comp_isIso f g
@[deprecated (since := "2024-10-18")]
alias openEmbedding_iff_comp_isIso' := isOpenEmbedding_iff_comp_isIso'
theorem isOpenEmbedding_iff_isIso_comp {X Y Z : TopCat} (f : X ⟶ Y) (g : Y ⟶ Z) [IsIso f] :
    IsOpenEmbedding (f ≫ g) ↔ IsOpenEmbedding g := by
  constructor
  · intro h
    convert h.comp (TopCat.homeoOfIso (asIso f).symm).isOpenEmbedding
    exact congrArg _ (IsIso.inv_hom_id_assoc f g).symm
  · exact fun h => h.comp (TopCat.homeoOfIso (asIso f)).isOpenEmbedding
@[deprecated (since := "2024-10-18")]
alias openEmbedding_iff_isIso_comp := isOpenEmbedding_iff_isIso_comp
@[simp]
theorem isOpenEmbedding_iff_isIso_comp' {X Y Z : TopCat} (f : X ⟶ Y) (g : Y ⟶ Z) [IsIso f] :
    IsOpenEmbedding ((forget TopCat).map f ≫ (forget TopCat).map g) ↔ IsOpenEmbedding g := by
  simp only [← Functor.map_comp]
  exact isOpenEmbedding_iff_isIso_comp f g
@[deprecated (since := "2024-10-18")]
alias openEmbedding_iff_isIso_comp' := isOpenEmbedding_iff_isIso_comp'
end TopCat