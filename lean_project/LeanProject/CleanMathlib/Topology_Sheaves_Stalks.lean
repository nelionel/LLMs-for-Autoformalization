import Mathlib.CategoryTheory.Sites.Pullback
import Mathlib.Topology.Category.TopCat.OpenNhds
import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing
assert_not_exists OrderedCommMonoid
noncomputable section
universe v u v' u'
open CategoryTheory
open TopCat
open CategoryTheory.Limits
open TopologicalSpace Topology
open Opposite
open scoped AlgebraicGeometry
variable {C : Type u} [Category.{v} C]
variable [HasColimits.{v} C]
variable {X Y Z : TopCat.{v}}
namespace TopCat.Presheaf
variable (C)
def stalkFunctor (x : X) : X.Presheaf C ⥤ C :=
  (whiskeringLeft _ _ C).obj (OpenNhds.inclusion x).op ⋙ colim
variable {C}
def stalk (ℱ : X.Presheaf C) (x : X) : C :=
  (stalkFunctor C x).obj ℱ
@[simp]
theorem stalkFunctor_obj (ℱ : X.Presheaf C) (x : X) : (stalkFunctor C x).obj ℱ = ℱ.stalk x :=
  rfl
def germ (F : X.Presheaf C) (U : Opens X) (x : X) (hx : x ∈ U) : F.obj (op U) ⟶ stalk F x :=
  colimit.ι ((OpenNhds.inclusion x).op ⋙ F) (op ⟨U, hx⟩)
def Γgerm (F : X.Presheaf C) (x : X) : F.obj (op ⊤) ⟶ stalk F x :=
  F.germ ⊤ x True.intro
@[reassoc]
theorem germ_res (F : X.Presheaf C) {U V : Opens X} (i : U ⟶ V) (x : X) (hx : x ∈ U) :
    F.map i.op ≫ F.germ U x hx = F.germ V x (i.le hx) :=
  let i' : (⟨U, hx⟩ : OpenNhds x) ⟶ ⟨V, i.le hx⟩ := i
  colimit.w ((OpenNhds.inclusion x).op ⋙ F) i'.op
@[reassoc (attr := simp)]
theorem germ_res' (F : X.Presheaf C) {U V : Opens X} (i : op V ⟶ op U) (x : X) (hx : x ∈ U) :
    F.map i ≫ F.germ U x hx = F.germ V x (i.unop.le hx) :=
  let i' : (⟨U, hx⟩ : OpenNhds x) ⟶ ⟨V, i.unop.le hx⟩ := i.unop
  colimit.w ((OpenNhds.inclusion x).op ⋙ F) i'.op
@[reassoc]
lemma map_germ_eq_Γgerm (F : X.Presheaf C) {U : Opens X} {i : U ⟶ ⊤} (x : X) (hx : x ∈ U) :
    F.map i.op ≫ F.germ U x hx = F.Γgerm x :=
  germ_res F i x hx
attribute [local instance] ConcreteCategory.instFunLike in
theorem germ_res_apply (F : X.Presheaf C)
    {U V : Opens X} (i : U ⟶ V) (x : X) (hx : x ∈ U) [ConcreteCategory C] (s) :
  F.germ U x hx (F.map i.op s) = F.germ V x (i.le hx) s := by rw [← comp_apply, germ_res]
attribute [local instance] ConcreteCategory.instFunLike in
theorem germ_res_apply' (F : X.Presheaf C)
    {U V : Opens X} (i : op V ⟶ op U) (x : X) (hx : x ∈ U) [ConcreteCategory C] (s) :
  F.germ U x hx (F.map i s) = F.germ V x (i.unop.le hx) s := by rw [← comp_apply, germ_res']
attribute [local instance] ConcreteCategory.instFunLike in
lemma Γgerm_res_apply (F : X.Presheaf C)
    {U : Opens X} {i : U ⟶ ⊤} (x : X) (hx : x ∈ U) [ConcreteCategory C] (s) :
  F.germ U x hx (F.map i.op s) = F.Γgerm x s := F.germ_res_apply i x hx s
@[ext]
theorem stalk_hom_ext (F : X.Presheaf C) {x} {Y : C} {f₁ f₂ : F.stalk x ⟶ Y}
    (ih : ∀ (U : Opens X) (hxU : x ∈ U), F.germ U x hxU ≫ f₁ = F.germ U x hxU ≫ f₂) : f₁ = f₂ :=
  colimit.hom_ext fun U => by
    induction' U using Opposite.rec with U; cases' U with U hxU; exact ih U hxU
@[reassoc (attr := simp)]
theorem stalkFunctor_map_germ {F G : X.Presheaf C} (U : Opens X) (x : X) (hx : x ∈ U) (f : F ⟶ G) :
    F.germ U x hx ≫ (stalkFunctor C x).map f = f.app (op U) ≫ G.germ U x hx :=
  colimit.ι_map (whiskerLeft (OpenNhds.inclusion x).op f) (op ⟨U, hx⟩)
attribute [local instance] ConcreteCategory.instFunLike in
theorem stalkFunctor_map_germ_apply [ConcreteCategory C]
    {F G : X.Presheaf C} (U : Opens X) (x : X) (hx : x ∈ U) (f : F ⟶ G) (s) :
    (stalkFunctor C x).map f (F.germ U x hx s) = G.germ U x hx (f.app (op U) s) := by
  rw [← comp_apply, ← stalkFunctor_map_germ]
  exact (comp_apply _ _ _).symm
attribute [local instance] ConcreteCategory.instFunLike in
@[simp]
theorem stalkFunctor_map_germ_apply' [ConcreteCategory C]
    {F G : X.Presheaf C} (U : Opens X) (x : X) (hx : x ∈ U) (f : F ⟶ G) (s) :
    DFunLike.coe (F := F.stalk x ⟶ G.stalk x) ((stalkFunctor C x).map f) (F.germ U x hx s) =
      G.germ U x hx (f.app (op U) s) :=
  stalkFunctor_map_germ_apply U x hx f s
variable (C)
def stalkPushforward (f : X ⟶ Y) (F : X.Presheaf C) (x : X) : (f _* F).stalk (f x) ⟶ F.stalk x := by
  refine ?_ ≫ colimit.pre _ (OpenNhds.map f x).op
  exact colim.map (whiskerRight (NatTrans.op (OpenNhds.inclusionMapIso f x).inv) F)
@[reassoc (attr := simp), elementwise (attr := simp)]
theorem stalkPushforward_germ (f : X ⟶ Y) (F : X.Presheaf C) (U : Opens Y)
    (x : X) (hx : f x ∈ U) :
      (f _* F).germ U (f x) hx ≫ F.stalkPushforward C f x = F.germ ((Opens.map f).obj U) x hx := by
  simp [germ, stalkPushforward]
namespace stalkPushforward
@[simp]
theorem id (ℱ : X.Presheaf C) (x : X) :
    ℱ.stalkPushforward C (𝟙 X) x = (stalkFunctor C x).map (Pushforward.id ℱ).hom := by
  ext
  simp only [stalkPushforward, germ, colim_map, ι_colimMap_assoc, whiskerRight_app]
  erw [CategoryTheory.Functor.map_id]
  simp [stalkFunctor]
@[simp]
theorem comp (ℱ : X.Presheaf C) (f : X ⟶ Y) (g : Y ⟶ Z) (x : X) :
    ℱ.stalkPushforward C (f ≫ g) x =
      (f _* ℱ).stalkPushforward C g (f x) ≫ ℱ.stalkPushforward C f x := by
  ext
  simp [germ, stalkPushforward]
theorem stalkPushforward_iso_of_isInducing {f : X ⟶ Y} (hf : IsInducing f)
    (F : X.Presheaf C) (x : X) : IsIso (F.stalkPushforward _ f x) := by
  haveI := Functor.initial_of_adjunction (hf.adjunctionNhds x)
  convert (Functor.Final.colimitIso (OpenNhds.map f x).op ((OpenNhds.inclusion x).op ⋙ F)).isIso_hom
  refine stalk_hom_ext _ fun U hU ↦ (stalkPushforward_germ _ f F _ x hU).trans ?_
  symm
  exact colimit.ι_pre ((OpenNhds.inclusion x).op ⋙ F) (OpenNhds.map f x).op _
@[deprecated (since := "2024-10-27")]
alias stalkPushforward_iso_of_isOpenEmbedding := stalkPushforward_iso_of_isInducing
@[deprecated (since := "2024-10-18")]
alias stalkPushforward_iso_of_openEmbedding := stalkPushforward_iso_of_isInducing
end stalkPushforward
section stalkPullback
def stalkPullbackHom (f : X ⟶ Y) (F : Y.Presheaf C) (x : X) :
    F.stalk (f x) ⟶ ((pullback C f).obj F).stalk x :=
  (stalkFunctor _ (f x)).map ((pushforwardPullbackAdjunction C f).unit.app F) ≫
    stalkPushforward _ _ _ x
@[reassoc (attr := simp)]
lemma germ_stalkPullbackHom
    (f : X ⟶ Y) (F : Y.Presheaf C) (x : X) (U : Opens Y) (hU : f x ∈ U) :
    F.germ U (f x) hU ≫ stalkPullbackHom C f F x =
      ((pushforwardPullbackAdjunction C f).unit.app F).app _ ≫
        ((pullback C f).obj F).germ ((Opens.map f).obj U) x hU := by
  simp [stalkPullbackHom, germ, stalkFunctor, stalkPushforward]
def germToPullbackStalk (f : X ⟶ Y) (F : Y.Presheaf C) (U : Opens X) (x : X) (hx : x ∈ U) :
    ((pullback C f).obj F).obj (op U) ⟶ F.stalk (f x) :=
  ((Opens.map f).op.isPointwiseLeftKanExtensionLeftKanExtensionUnit F (op U)).desc
    { pt := F.stalk ((f : X → Y) (x : X))
      ι :=
        { app := fun V => F.germ _ (f x) (V.hom.unop.le hx)
          naturality := fun _ _ i => by simp } }
variable {C} in
@[ext]
lemma pullback_obj_obj_ext {Z : C} {f : X ⟶ Y} {F : Y.Presheaf C} (U : (Opens X)ᵒᵖ)
    {φ ψ : ((pullback C f).obj F).obj U ⟶ Z}
    (h : ∀ (V : Opens Y) (hV : U.unop ≤ (Opens.map f).obj V),
      ((pushforwardPullbackAdjunction C f).unit.app F).app (op V) ≫
        ((pullback C f).obj F).map (homOfLE hV).op ≫ φ =
      ((pushforwardPullbackAdjunction C f).unit.app F).app (op V) ≫
        ((pullback C f).obj F).map (homOfLE hV).op ≫ ψ) : φ = ψ := by
  obtain ⟨U⟩ := U
  apply ((Opens.map f).op.isPointwiseLeftKanExtensionLeftKanExtensionUnit F _).hom_ext
  rintro ⟨⟨V⟩, ⟨⟩, ⟨b⟩⟩
  simpa [pushforwardPullbackAdjunction, Functor.lanAdjunction_unit]
    using h V (leOfHom b)
@[reassoc (attr := simp)]
lemma pushforwardPullbackAdjunction_unit_pullback_map_germToPullbackStalk
    (f : X ⟶ Y) (F : Y.Presheaf C) (U : Opens X) (x : X) (hx : x ∈ U) (V : Opens Y)
    (hV : U ≤ (Opens.map f).obj V) :
    ((pushforwardPullbackAdjunction C f).unit.app F).app (op V) ≫
      ((pullback C f).obj F).map (homOfLE hV).op ≫ germToPullbackStalk C f F U x hx  =
        F.germ _ (f x) (hV hx) := by
  simpa [pushforwardPullbackAdjunction] using
    ((Opens.map f).op.isPointwiseLeftKanExtensionLeftKanExtensionUnit F (op U)).fac _
      (CostructuredArrow.mk (homOfLE hV).op)
@[reassoc (attr := simp)]
lemma germToPullbackStalk_stalkPullbackHom
    (f : X ⟶ Y) (F : Y.Presheaf C) (U : Opens X) (x : X) (hx : x ∈ U) :
    germToPullbackStalk C f F U x hx ≫ stalkPullbackHom C f F x =
      ((pullback C f).obj F).germ _ x hx := by
  ext V hV
  dsimp
  simp only [pushforwardPullbackAdjunction_unit_pullback_map_germToPullbackStalk_assoc,
    germ_stalkPullbackHom, germ_res]
@[reassoc (attr := simp)]
lemma pushforwardPullbackAdjunction_unit_app_app_germToPullbackStalk
    (f : X ⟶ Y) (F : Y.Presheaf C) (V : (Opens Y)ᵒᵖ) (x : X) (hx : f x ∈ V.unop) :
    ((pushforwardPullbackAdjunction C f).unit.app F).app V ≫ germToPullbackStalk C f F _ x hx =
      F.germ _ (f x) hx := by
  simpa using pushforwardPullbackAdjunction_unit_pullback_map_germToPullbackStalk
    C f F ((Opens.map f).obj V.unop) x hx V.unop (by rfl)
def stalkPullbackInv (f : X ⟶ Y) (F : Y.Presheaf C) (x : X) :
    ((pullback C f).obj F).stalk x ⟶ F.stalk (f x) :=
  colimit.desc ((OpenNhds.inclusion x).op ⋙ (Presheaf.pullback C f).obj F)
    { pt := F.stalk (f x)
      ι :=
        { app := fun U => F.germToPullbackStalk _ f (unop U).1 x (unop U).2
          naturality := fun U V i => by
            dsimp
            ext W hW
            dsimp [OpenNhds.inclusion]
            rw [Category.comp_id, ← Functor.map_comp_assoc,
              pushforwardPullbackAdjunction_unit_pullback_map_germToPullbackStalk]
            erw [pushforwardPullbackAdjunction_unit_pullback_map_germToPullbackStalk] } }
@[reassoc (attr := simp)]
lemma germ_stalkPullbackInv (f : X ⟶ Y) (F : Y.Presheaf C) (x : X) (V : Opens X) (hV : x ∈ V) :
    ((pullback C f).obj F).germ _ x hV ≫ stalkPullbackInv C f F x =
    F.germToPullbackStalk _ f V x hV := by
  apply colimit.ι_desc
def stalkPullbackIso (f : X ⟶ Y) (F : Y.Presheaf C) (x : X) :
    F.stalk (f x) ≅ ((pullback C f).obj F).stalk x where
  hom := stalkPullbackHom _ _ _ _
  inv := stalkPullbackInv _ _ _ _
  hom_inv_id := by
    ext U hU
    dsimp
    rw [germ_stalkPullbackHom_assoc, germ_stalkPullbackInv, Category.comp_id,
      pushforwardPullbackAdjunction_unit_app_app_germToPullbackStalk]
  inv_hom_id := by
    ext V hV
    dsimp
    rw [germ_stalkPullbackInv_assoc, Category.comp_id, germToPullbackStalk_stalkPullbackHom]
end stalkPullback
section stalkSpecializes
variable {C}
noncomputable def stalkSpecializes (F : X.Presheaf C) {x y : X} (h : x ⤳ y) :
    F.stalk y ⟶ F.stalk x := by
  refine colimit.desc _ ⟨_, fun U => ?_, ?_⟩
  · exact
      colimit.ι ((OpenNhds.inclusion x).op ⋙ F)
        (op ⟨(unop U).1, (specializes_iff_forall_open.mp h _ (unop U).1.2 (unop U).2 : _)⟩)
  · intro U V i
    dsimp
    rw [Category.comp_id]
    let U' : OpenNhds x := ⟨_, (specializes_iff_forall_open.mp h _ (unop U).1.2 (unop U).2 : _)⟩
    let V' : OpenNhds x := ⟨_, (specializes_iff_forall_open.mp h _ (unop V).1.2 (unop V).2 : _)⟩
    exact colimit.w ((OpenNhds.inclusion x).op ⋙ F) (show V' ⟶ U' from i.unop).op
@[reassoc (attr := simp), elementwise nosimp]
theorem germ_stalkSpecializes (F : X.Presheaf C)
    {U : Opens X} {y : X} (hy : y ∈ U) {x : X} (h : x ⤳ y) :
    F.germ U y hy ≫ F.stalkSpecializes h = F.germ U x (h.mem_open U.isOpen hy) :=
  colimit.ι_desc _ _
@[deprecated (since := "2024-07-30")] alias germ_stalkSpecializes' := germ_stalkSpecializes
@[simp]
theorem stalkSpecializes_refl {C : Type*} [Category C] [Limits.HasColimits C] {X : TopCat}
    (F : X.Presheaf C) (x : X) : F.stalkSpecializes (specializes_refl x) = 𝟙 _ := by
  ext
  simp
@[reassoc (attr := simp), elementwise (attr := simp)]
theorem stalkSpecializes_comp {C : Type*} [Category C] [Limits.HasColimits C] {X : TopCat}
    (F : X.Presheaf C) {x y z : X} (h : x ⤳ y) (h' : y ⤳ z) :
    F.stalkSpecializes h' ≫ F.stalkSpecializes h = F.stalkSpecializes (h.trans h') := by
  ext
  simp
@[reassoc (attr := simp), elementwise (attr := simp)]
theorem stalkSpecializes_stalkFunctor_map {F G : X.Presheaf C} (f : F ⟶ G) {x y : X} (h : x ⤳ y) :
    F.stalkSpecializes h ≫ (stalkFunctor C x).map f =
      (stalkFunctor C y).map f ≫ G.stalkSpecializes h := by
  change (_ : colimit _ ⟶ _) = (_ : colimit _ ⟶ _)
  ext; delta stalkFunctor; simpa [stalkSpecializes] using by rfl
@[reassoc, elementwise, simp, nolint simpNF]
theorem stalkSpecializes_stalkPushforward (f : X ⟶ Y) (F : X.Presheaf C) {x y : X} (h : x ⤳ y) :
    (f _* F).stalkSpecializes (f.map_specializes h) ≫ F.stalkPushforward _ f x =
      F.stalkPushforward _ f y ≫ F.stalkSpecializes h := by
  change (_ : colimit _ ⟶ _) = (_ : colimit _ ⟶ _)
  ext; delta stalkPushforward
  simp only [stalkSpecializes, colimit.ι_desc_assoc, colimit.ι_map_assoc, colimit.ι_pre,
    Category.assoc, colimit.pre_desc, colimit.ι_desc]
  rfl
@[simps]
def stalkCongr {X : TopCat} {C : Type*} [Category C] [HasColimits C] (F : X.Presheaf C) {x y : X}
    (e : Inseparable x y) : F.stalk x ≅ F.stalk y :=
  ⟨F.stalkSpecializes e.ge, F.stalkSpecializes e.le, by simp, by simp⟩
end stalkSpecializes
section Concrete
variable {C}
variable [ConcreteCategory.{v} C]
attribute [local instance] ConcreteCategory.hasCoeToSort ConcreteCategory.instFunLike
theorem germ_ext (F : X.Presheaf C) {U V : Opens X} {x : X} {hxU : x ∈ U} {hxV : x ∈ V}
    (W : Opens X) (hxW : x ∈ W) (iWU : W ⟶ U) (iWV : W ⟶ V) {sU : F.obj (op U)} {sV : F.obj (op V)}
    (ih : F.map iWU.op sU = F.map iWV.op sV) :
      F.germ _ x hxU sU = F.germ _ x hxV sV := by
  rw [← F.germ_res iWU x hxW, ← F.germ_res iWV x hxW, comp_apply, comp_apply, ih]
variable [PreservesFilteredColimits (forget C)]
theorem germ_exist (F : X.Presheaf C) (x : X) (t : (stalk.{v, u} F x : Type v)) :
    ∃ (U : Opens X) (m : x ∈ U) (s : F.obj (op U)), F.germ _ x m s = t := by
  obtain ⟨U, s, e⟩ :=
    Types.jointly_surjective.{v, v} _ (isColimitOfPreserves (forget C) (colimit.isColimit _)) t
  revert s e
  induction U with | h U => ?_
  cases' U with V m
  intro s e
  exact ⟨V, m, s, e⟩
theorem germ_eq (F : X.Presheaf C) {U V : Opens X} (x : X) (mU : x ∈ U) (mV : x ∈ V)
    (s : F.obj (op U)) (t : F.obj (op V)) (h : F.germ U x mU s = F.germ V x mV t) :
    ∃ (W : Opens X) (_m : x ∈ W) (iU : W ⟶ U) (iV : W ⟶ V), F.map iU.op s = F.map iV.op t := by
  obtain ⟨W, iU, iV, e⟩ :=
    (Types.FilteredColimit.isColimit_eq_iff.{v, v} _
          (isColimitOfPreserves _ (colimit.isColimit ((OpenNhds.inclusion x).op ⋙ F)))).mp h
  exact ⟨(unop W).1, (unop W).2, iU.unop, iV.unop, e⟩
theorem stalkFunctor_map_injective_of_app_injective {F G : Presheaf C X} (f : F ⟶ G)
    (h : ∀ U : Opens X, Function.Injective (f.app (op U))) (x : X) :
    Function.Injective ((stalkFunctor C x).map f) := fun s t hst => by
  rcases germ_exist F x s with ⟨U₁, hxU₁, s, rfl⟩
  rcases germ_exist F x t with ⟨U₂, hxU₂, t, rfl⟩
  rw [stalkFunctor_map_germ_apply, stalkFunctor_map_germ_apply] at hst
  obtain ⟨W, hxW, iWU₁, iWU₂, heq⟩ := G.germ_eq x hxU₁ hxU₂ _ _ hst
  rw [← comp_apply, ← comp_apply, ← f.naturality, ← f.naturality, comp_apply, comp_apply] at heq
  replace heq := h W heq
  convert congr_arg (F.germ _ x hxW) heq using 1
  exacts [(F.germ_res_apply iWU₁ x hxW s).symm, (F.germ_res_apply iWU₂ x hxW t).symm]
variable [HasLimits C] [PreservesLimits (forget C)] [(forget C).ReflectsIsomorphisms]
theorem section_ext (F : Sheaf C X) (U : Opens X) (s t : F.1.obj (op U))
    (h : ∀ (x : X) (hx : x ∈ U), F.presheaf.germ U x hx s = F.presheaf.germ U x hx t) : s = t := by
  choose V m i₁ i₂ heq using fun x : U => F.presheaf.germ_eq x.1 x.2 x.2 s t (h x.1 x.2)
  apply F.eq_of_locally_eq' V U i₁
  · intro x hxU
    simp only [Opens.coe_iSup, Set.mem_iUnion, SetLike.mem_coe]
    exact ⟨⟨x, hxU⟩, m ⟨x, hxU⟩⟩
  · intro x
    rw [heq, Subsingleton.elim (i₁ x) (i₂ x)]
theorem app_injective_of_stalkFunctor_map_injective {F : Sheaf C X} {G : Presheaf C X} (f : F.1 ⟶ G)
    (U : Opens X) (h : ∀ x ∈ U, Function.Injective ((stalkFunctor C x).map f)) :
    Function.Injective (f.app (op U)) := fun s t hst =>
  section_ext F _ _ _ fun x hx =>
    h x hx <| by rw [stalkFunctor_map_germ_apply, stalkFunctor_map_germ_apply, hst]
theorem app_injective_iff_stalkFunctor_map_injective {F : Sheaf C X} {G : Presheaf C X}
    (f : F.1 ⟶ G) :
    (∀ x : X, Function.Injective ((stalkFunctor C x).map f)) ↔
      ∀ U : Opens X, Function.Injective (f.app (op U)) :=
  ⟨fun h U => app_injective_of_stalkFunctor_map_injective f U fun x _ => h x,
    stalkFunctor_map_injective_of_app_injective f⟩
instance stalkFunctor_preserves_mono (x : X) :
    Functor.PreservesMonomorphisms (Sheaf.forget C X ⋙ stalkFunctor C x) :=
  ⟨@fun _𝓐 _𝓑 f _ =>
    ConcreteCategory.mono_of_injective _ <|
      (app_injective_iff_stalkFunctor_map_injective f.1).mpr
        (fun c =>
          (ConcreteCategory.mono_iff_injective_of_preservesPullback (f.1.app (op c))).mp
            ((NatTrans.mono_iff_mono_app f.1).mp
                (CategoryTheory.presheaf_mono_of_mono ..) <|
              op c))
        x⟩
theorem stalk_mono_of_mono {F G : Sheaf C X} (f : F ⟶ G) [Mono f] :
    ∀ x, Mono <| (stalkFunctor C x).map f.1 :=
  fun x => Functor.map_mono (Sheaf.forget.{v} C X ⋙ stalkFunctor C x) f
theorem mono_of_stalk_mono {F G : Sheaf C X} (f : F ⟶ G) [∀ x, Mono <| (stalkFunctor C x).map f.1] :
    Mono f :=
  (Sheaf.Hom.mono_iff_presheaf_mono _ _ _).mpr <|
    (NatTrans.mono_iff_mono_app _).mpr fun U =>
      (ConcreteCategory.mono_iff_injective_of_preservesPullback _).mpr <|
        app_injective_of_stalkFunctor_map_injective f.1 U.unop fun _x _hx =>
          (ConcreteCategory.mono_iff_injective_of_preservesPullback _).mp <| inferInstance
theorem mono_iff_stalk_mono {F G : Sheaf C X} (f : F ⟶ G) :
    Mono f ↔ ∀ x, Mono ((stalkFunctor C x).map f.1) :=
  ⟨fun _ => stalk_mono_of_mono _, fun _ => mono_of_stalk_mono _⟩
theorem app_surjective_of_injective_of_locally_surjective {F G : Sheaf C X} (f : F ⟶ G)
    (U : Opens X) (hinj : ∀ x ∈ U, Function.Injective ((stalkFunctor C x).map f.1))
    (hsurj : ∀ (t x) (_ : x ∈ U), ∃ (V : Opens X) (_ : x ∈ V) (iVU : V ⟶ U) (s : F.1.obj (op V)),
          f.1.app (op V) s = G.1.map iVU.op t) :
    Function.Surjective (f.1.app (op U)) := by
  conv at hsurj =>
    enter [t]
    rw [Subtype.forall' (p := (· ∈ U))]
  intro t
  choose V mV iVU sf heq using hsurj t
  have V_cover : U ≤ iSup V := by
    intro x hxU
    simp only [Opens.coe_iSup, Set.mem_iUnion, SetLike.mem_coe]
    exact ⟨⟨x, hxU⟩, mV ⟨x, hxU⟩⟩
  suffices IsCompatible F.val V sf by
    obtain ⟨s, s_spec, -⟩ := F.existsUnique_gluing' V U iVU V_cover sf this
    · use s
      apply G.eq_of_locally_eq' V U iVU V_cover
      intro x
      rw [← comp_apply, ← f.1.naturality, comp_apply, s_spec, heq]
  intro x y
  apply section_ext
  intro z hz
  apply hinj z ((iVU x).le ((inf_le_left : V x ⊓ V y ≤ V x) hz))
  dsimp only
  rw [stalkFunctor_map_germ_apply, stalkFunctor_map_germ_apply]
  simp_rw [← comp_apply, f.1.naturality, comp_apply, heq, ← comp_apply, ← G.1.map_comp]
  rfl
theorem app_surjective_of_stalkFunctor_map_bijective {F G : Sheaf C X} (f : F ⟶ G) (U : Opens X)
    (h : ∀ x ∈ U, Function.Bijective ((stalkFunctor C x).map f.1)) :
    Function.Surjective (f.1.app (op U)) := by
  refine app_surjective_of_injective_of_locally_surjective f U (And.left <| h · ·) fun t x hx => ?_
  obtain ⟨s₀, hs₀⟩ := (h x hx).2 (G.presheaf.germ U x hx t)
  obtain ⟨V₁, hxV₁, s₁, hs₁⟩ := F.presheaf.germ_exist x s₀
  subst hs₁; rename' hs₀ => hs₁
  rw [stalkFunctor_map_germ_apply V₁ x hxV₁ f.1 s₁] at hs₁
  obtain ⟨V₂, hxV₂, iV₂V₁, iV₂U, heq⟩ := G.presheaf.germ_eq x hxV₁ hx _ _ hs₁
  use V₂, hxV₂, iV₂U, F.1.map iV₂V₁.op s₁
  rw [← comp_apply, f.1.naturality, comp_apply, heq]
theorem app_bijective_of_stalkFunctor_map_bijective {F G : Sheaf C X} (f : F ⟶ G) (U : Opens X)
    (h : ∀ x ∈ U, Function.Bijective ((stalkFunctor C x).map f.1)) :
    Function.Bijective (f.1.app (op U)) :=
  ⟨app_injective_of_stalkFunctor_map_injective f.1 U fun x hx => (h x hx).1,
    app_surjective_of_stalkFunctor_map_bijective f U h⟩
theorem app_isIso_of_stalkFunctor_map_iso {F G : Sheaf C X} (f : F ⟶ G) (U : Opens X)
    [∀ x : U, IsIso ((stalkFunctor C x.val).map f.1)] : IsIso (f.1.app (op U)) := by
  suffices IsIso ((forget C).map (f.1.app (op U))) by
    exact isIso_of_reflects_iso (f.1.app (op U)) (forget C)
  rw [isIso_iff_bijective]
  apply app_bijective_of_stalkFunctor_map_bijective
  intro x hx
  apply (isIso_iff_bijective _).mp
  exact Functor.map_isIso (forget C) ((stalkFunctor C (⟨x, hx⟩ : U).1).map f.1)
theorem isIso_of_stalkFunctor_map_iso {F G : Sheaf C X} (f : F ⟶ G)
    [∀ x : X, IsIso ((stalkFunctor C x).map f.1)] : IsIso f := by
  suffices IsIso ((Sheaf.forget C X).map f) by exact isIso_of_fully_faithful (Sheaf.forget C X) f
  suffices ∀ U : (Opens X)ᵒᵖ, IsIso (f.1.app U) by
    exact @NatIso.isIso_of_isIso_app _ _ _ _ F.1 G.1 f.1 this
  intro U; induction U
  apply app_isIso_of_stalkFunctor_map_iso
theorem isIso_iff_stalkFunctor_map_iso {F G : Sheaf C X} (f : F ⟶ G) :
    IsIso f ↔ ∀ x : X, IsIso ((stalkFunctor C x).map f.1) :=
  ⟨fun _ x =>
    @Functor.map_isIso _ _ _ _ _ _ (stalkFunctor C x) f.1 ((Sheaf.forget C X).map_isIso f),
   fun _ => isIso_of_stalkFunctor_map_iso f⟩
end Concrete
end TopCat.Presheaf