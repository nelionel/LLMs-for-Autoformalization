import Mathlib.CategoryTheory.Limits.IsLimit
import Mathlib.CategoryTheory.Category.ULift
import Mathlib.CategoryTheory.EssentiallySmall
import Mathlib.Logic.Equiv.Basic
noncomputable section
open CategoryTheory CategoryTheory.Category CategoryTheory.Functor Opposite
namespace CategoryTheory.Limits
universe v₁ u₁ v₂ u₂ v₃ u₃ v v' v'' u u' u''
variable {J : Type u₁} [Category.{v₁} J] {K : Type u₂} [Category.{v₂} K]
variable {C : Type u} [Category.{v} C]
variable {F : J ⥤ C}
section Limit
structure LimitCone (F : J ⥤ C) where
  cone : Cone F
  isLimit : IsLimit cone
class HasLimit (F : J ⥤ C) : Prop where mk' ::
  exists_limit : Nonempty (LimitCone F)
theorem HasLimit.mk {F : J ⥤ C} (d : LimitCone F) : HasLimit F :=
  ⟨Nonempty.intro d⟩
def getLimitCone (F : J ⥤ C) [HasLimit F] : LimitCone F :=
  Classical.choice <| HasLimit.exists_limit
variable (J C)
class HasLimitsOfShape : Prop where
  has_limit : ∀ F : J ⥤ C, HasLimit F := by infer_instance
@[pp_with_univ]
class HasLimitsOfSize (C : Type u) [Category.{v} C] : Prop where
  has_limits_of_shape : ∀ (J : Type u₁) [Category.{v₁} J], HasLimitsOfShape J C := by
    infer_instance
abbrev HasLimits (C : Type u) [Category.{v} C] : Prop :=
  HasLimitsOfSize.{v, v} C
theorem HasLimits.has_limits_of_shape {C : Type u} [Category.{v} C] [HasLimits C] (J : Type v)
    [Category.{v} J] : HasLimitsOfShape J C :=
  HasLimitsOfSize.has_limits_of_shape J
variable {J C}
instance (priority := 100) hasLimitOfHasLimitsOfShape {J : Type u₁} [Category.{v₁} J]
    [HasLimitsOfShape J C] (F : J ⥤ C) : HasLimit F :=
  HasLimitsOfShape.has_limit F
instance (priority := 100) hasLimitsOfShapeOfHasLimits {J : Type u₁} [Category.{v₁} J]
    [HasLimitsOfSize.{v₁, u₁} C] : HasLimitsOfShape J C :=
  HasLimitsOfSize.has_limits_of_shape J
def limit.cone (F : J ⥤ C) [HasLimit F] : Cone F :=
  (getLimitCone F).cone
def limit (F : J ⥤ C) [HasLimit F] :=
  (limit.cone F).pt
def limit.π (F : J ⥤ C) [HasLimit F] (j : J) : limit F ⟶ F.obj j :=
  (limit.cone F).π.app j
@[reassoc]
theorem limit.π_comp_eqToHom (F : J ⥤ C) [HasLimit F] {j j' : J} (hj : j = j') :
    limit.π F j ≫ eqToHom (by subst hj; rfl) = limit.π F j' := by
  subst hj
  simp
@[simp]
theorem limit.cone_x {F : J ⥤ C} [HasLimit F] : (limit.cone F).pt = limit F :=
  rfl
@[simp]
theorem limit.cone_π {F : J ⥤ C} [HasLimit F] : (limit.cone F).π.app = limit.π _ :=
  rfl
@[reassoc (attr := simp)]
theorem limit.w (F : J ⥤ C) [HasLimit F] {j j' : J} (f : j ⟶ j') :
    limit.π F j ≫ F.map f = limit.π F j' :=
  (limit.cone F).w f
def limit.isLimit (F : J ⥤ C) [HasLimit F] : IsLimit (limit.cone F) :=
  (getLimitCone F).isLimit
def limit.lift (F : J ⥤ C) [HasLimit F] (c : Cone F) : c.pt ⟶ limit F :=
  (limit.isLimit F).lift c
@[simp]
theorem limit.isLimit_lift {F : J ⥤ C} [HasLimit F] (c : Cone F) :
    (limit.isLimit F).lift c = limit.lift F c :=
  rfl
@[reassoc (attr := simp)]
theorem limit.lift_π {F : J ⥤ C} [HasLimit F] (c : Cone F) (j : J) :
    limit.lift F c ≫ limit.π F j = c.π.app j :=
  IsLimit.fac _ c j
def limMap {F G : J ⥤ C} [HasLimit F] [HasLimit G] (α : F ⟶ G) : limit F ⟶ limit G :=
  IsLimit.map _ (limit.isLimit G) α
@[reassoc (attr := simp)]
theorem limMap_π {F G : J ⥤ C} [HasLimit F] [HasLimit G] (α : F ⟶ G) (j : J) :
    limMap α ≫ limit.π G j = limit.π F j ≫ α.app j :=
  limit.lift_π _ j
def limit.coneMorphism {F : J ⥤ C} [HasLimit F] (c : Cone F) : c ⟶ limit.cone F :=
  (limit.isLimit F).liftConeMorphism c
@[simp]
theorem limit.coneMorphism_hom {F : J ⥤ C} [HasLimit F] (c : Cone F) :
    (limit.coneMorphism c).hom = limit.lift F c :=
  rfl
theorem limit.coneMorphism_π {F : J ⥤ C} [HasLimit F] (c : Cone F) (j : J) :
    (limit.coneMorphism c).hom ≫ limit.π F j = c.π.app j := by simp
@[reassoc (attr := simp)]
theorem limit.conePointUniqueUpToIso_hom_comp {F : J ⥤ C} [HasLimit F] {c : Cone F} (hc : IsLimit c)
    (j : J) : (IsLimit.conePointUniqueUpToIso hc (limit.isLimit _)).hom ≫ limit.π F j = c.π.app j :=
  IsLimit.conePointUniqueUpToIso_hom_comp _ _ _
@[reassoc (attr := simp)]
theorem limit.conePointUniqueUpToIso_inv_comp {F : J ⥤ C} [HasLimit F] {c : Cone F} (hc : IsLimit c)
    (j : J) : (IsLimit.conePointUniqueUpToIso (limit.isLimit _) hc).inv ≫ limit.π F j = c.π.app j :=
  IsLimit.conePointUniqueUpToIso_inv_comp _ _ _
theorem limit.existsUnique {F : J ⥤ C} [HasLimit F] (t : Cone F) :
    ∃! l : t.pt ⟶ limit F, ∀ j, l ≫ limit.π F j = t.π.app j :=
  (limit.isLimit F).existsUnique _
def limit.isoLimitCone {F : J ⥤ C} [HasLimit F] (t : LimitCone F) : limit F ≅ t.cone.pt :=
  IsLimit.conePointUniqueUpToIso (limit.isLimit F) t.isLimit
@[reassoc (attr := simp)]
theorem limit.isoLimitCone_hom_π {F : J ⥤ C} [HasLimit F] (t : LimitCone F) (j : J) :
    (limit.isoLimitCone t).hom ≫ t.cone.π.app j = limit.π F j := by
  dsimp [limit.isoLimitCone, IsLimit.conePointUniqueUpToIso]
  aesop_cat
@[reassoc (attr := simp)]
theorem limit.isoLimitCone_inv_π {F : J ⥤ C} [HasLimit F] (t : LimitCone F) (j : J) :
    (limit.isoLimitCone t).inv ≫ limit.π F j = t.cone.π.app j := by
  dsimp [limit.isoLimitCone, IsLimit.conePointUniqueUpToIso]
  aesop_cat
@[ext]
theorem limit.hom_ext {F : J ⥤ C} [HasLimit F] {X : C} {f f' : X ⟶ limit F}
    (w : ∀ j, f ≫ limit.π F j = f' ≫ limit.π F j) : f = f' :=
  (limit.isLimit F).hom_ext w
@[simp]
theorem limit.lift_map {F G : J ⥤ C} [HasLimit F] [HasLimit G] (c : Cone F) (α : F ⟶ G) :
    limit.lift F c ≫ limMap α = limit.lift G ((Cones.postcompose α).obj c) := by
  ext
  rw [assoc, limMap_π, limit.lift_π_assoc, limit.lift_π]
  rfl
@[simp]
theorem limit.lift_cone {F : J ⥤ C} [HasLimit F] : limit.lift F (limit.cone F) = 𝟙 (limit F) :=
  (limit.isLimit _).lift_self
def limit.homIso (F : J ⥤ C) [HasLimit F] (W : C) :
    ULift.{u₁} (W ⟶ limit F : Type v) ≅ F.cones.obj (op W) :=
  (limit.isLimit F).homIso W
@[simp]
theorem limit.homIso_hom (F : J ⥤ C) [HasLimit F] {W : C} (f : ULift (W ⟶ limit F)) :
    (limit.homIso F W).hom f = (const J).map f.down ≫ (limit.cone F).π :=
  (limit.isLimit F).homIso_hom f
def limit.homIso' (F : J ⥤ C) [HasLimit F] (W : C) :
    ULift.{u₁} (W ⟶ limit F : Type v) ≅
      { p : ∀ j, W ⟶ F.obj j // ∀ {j j' : J} (f : j ⟶ j'), p j ≫ F.map f = p j' } :=
  (limit.isLimit F).homIso' W
theorem limit.lift_extend {F : J ⥤ C} [HasLimit F] (c : Cone F) {X : C} (f : X ⟶ c.pt) :
    limit.lift F (c.extend f) = f ≫ limit.lift F c := by aesop_cat
theorem hasLimitOfIso {F G : J ⥤ C} [HasLimit F] (α : F ≅ G) : HasLimit G :=
  HasLimit.mk
    { cone := (Cones.postcompose α.hom).obj (limit.cone F)
      isLimit := (IsLimit.postcomposeHomEquiv _ _).symm (limit.isLimit F) }
theorem HasLimit.ofConesIso {J K : Type u₁} [Category.{v₁} J] [Category.{v₂} K] (F : J ⥤ C)
    (G : K ⥤ C) (h : F.cones ≅ G.cones) [HasLimit F] : HasLimit G :=
  HasLimit.mk ⟨_, IsLimit.ofNatIso (IsLimit.natIso (limit.isLimit F) ≪≫ h)⟩
def HasLimit.isoOfNatIso {F G : J ⥤ C} [HasLimit F] [HasLimit G] (w : F ≅ G) : limit F ≅ limit G :=
  IsLimit.conePointsIsoOfNatIso (limit.isLimit F) (limit.isLimit G) w
@[reassoc (attr := simp)]
theorem HasLimit.isoOfNatIso_hom_π {F G : J ⥤ C} [HasLimit F] [HasLimit G] (w : F ≅ G) (j : J) :
    (HasLimit.isoOfNatIso w).hom ≫ limit.π G j = limit.π F j ≫ w.hom.app j :=
  IsLimit.conePointsIsoOfNatIso_hom_comp _ _ _ _
@[reassoc (attr := simp)]
theorem HasLimit.isoOfNatIso_inv_π {F G : J ⥤ C} [HasLimit F] [HasLimit G] (w : F ≅ G) (j : J) :
    (HasLimit.isoOfNatIso w).inv ≫ limit.π F j = limit.π G j ≫ w.inv.app j :=
  IsLimit.conePointsIsoOfNatIso_inv_comp _ _ _ _
@[reassoc (attr := simp)]
theorem HasLimit.lift_isoOfNatIso_hom {F G : J ⥤ C} [HasLimit F] [HasLimit G] (t : Cone F)
    (w : F ≅ G) :
    limit.lift F t ≫ (HasLimit.isoOfNatIso w).hom =
      limit.lift G ((Cones.postcompose w.hom).obj _) :=
  IsLimit.lift_comp_conePointsIsoOfNatIso_hom _ _ _
@[reassoc (attr := simp)]
theorem HasLimit.lift_isoOfNatIso_inv {F G : J ⥤ C} [HasLimit F] [HasLimit G] (t : Cone G)
    (w : F ≅ G) :
    limit.lift G t ≫ (HasLimit.isoOfNatIso w).inv =
      limit.lift F ((Cones.postcompose w.inv).obj _) :=
  IsLimit.lift_comp_conePointsIsoOfNatIso_inv _ _ _
def HasLimit.isoOfEquivalence {F : J ⥤ C} [HasLimit F] {G : K ⥤ C} [HasLimit G] (e : J ≌ K)
    (w : e.functor ⋙ G ≅ F) : limit F ≅ limit G :=
  IsLimit.conePointsIsoOfEquivalence (limit.isLimit F) (limit.isLimit G) e w
@[simp]
theorem HasLimit.isoOfEquivalence_hom_π {F : J ⥤ C} [HasLimit F] {G : K ⥤ C} [HasLimit G]
    (e : J ≌ K) (w : e.functor ⋙ G ≅ F) (k : K) :
    (HasLimit.isoOfEquivalence e w).hom ≫ limit.π G k =
      limit.π F (e.inverse.obj k) ≫ w.inv.app (e.inverse.obj k) ≫ G.map (e.counit.app k) := by
  simp only [HasLimit.isoOfEquivalence, IsLimit.conePointsIsoOfEquivalence_hom]
  dsimp
  simp
@[simp]
theorem HasLimit.isoOfEquivalence_inv_π {F : J ⥤ C} [HasLimit F] {G : K ⥤ C} [HasLimit G]
    (e : J ≌ K) (w : e.functor ⋙ G ≅ F) (j : J) :
    (HasLimit.isoOfEquivalence e w).inv ≫ limit.π F j =
    limit.π G (e.functor.obj j) ≫ w.hom.app j := by
  simp only [HasLimit.isoOfEquivalence, IsLimit.conePointsIsoOfEquivalence_hom]
  dsimp
  simp
section Pre
variable (F)
variable [HasLimit F] (E : K ⥤ J) [HasLimit (E ⋙ F)]
def limit.pre : limit F ⟶ limit (E ⋙ F) :=
  limit.lift (E ⋙ F) ((limit.cone F).whisker E)
@[reassoc (attr := simp)]
theorem limit.pre_π (k : K) : limit.pre F E ≫ limit.π (E ⋙ F) k = limit.π F (E.obj k) := by
  erw [IsLimit.fac]
  rfl
@[simp]
theorem limit.lift_pre (c : Cone F) :
    limit.lift F c ≫ limit.pre F E = limit.lift (E ⋙ F) (c.whisker E) := by ext; simp
variable {L : Type u₃} [Category.{v₃} L]
variable (D : L ⥤ K)
@[simp]
theorem limit.pre_pre [h : HasLimit (D ⋙ E ⋙ F)] : haveI : HasLimit ((D ⋙ E) ⋙ F) := h
    limit.pre F E ≫ limit.pre (E ⋙ F) D = limit.pre F (D ⋙ E) := by
  haveI : HasLimit ((D ⋙ E) ⋙ F) := h
  ext j; erw [assoc, limit.pre_π, limit.pre_π, limit.pre_π]; rfl
variable {E F}
theorem limit.pre_eq (s : LimitCone (E ⋙ F)) (t : LimitCone F) :
    limit.pre F E = (limit.isoLimitCone t).hom ≫ s.isLimit.lift (t.cone.whisker E) ≫
      (limit.isoLimitCone s).inv := by aesop_cat
end Pre
section Post
variable {D : Type u'} [Category.{v'} D]
variable (F : J ⥤ C) [HasLimit F] (G : C ⥤ D) [HasLimit (F ⋙ G)]
def limit.post : G.obj (limit F) ⟶ limit (F ⋙ G) :=
  limit.lift (F ⋙ G) (G.mapCone (limit.cone F))
@[reassoc (attr := simp)]
theorem limit.post_π (j : J) : limit.post F G ≫ limit.π (F ⋙ G) j = G.map (limit.π F j) := by
  erw [IsLimit.fac]
  rfl
@[simp]
theorem limit.lift_post (c : Cone F) :
    G.map (limit.lift F c) ≫ limit.post F G = limit.lift (F ⋙ G) (G.mapCone c) := by
  ext
  rw [assoc, limit.post_π, ← G.map_comp, limit.lift_π, limit.lift_π]
  rfl
@[simp]
theorem limit.post_post {E : Type u''} [Category.{v''} E] (H : D ⥤ E) [h : HasLimit ((F ⋙ G) ⋙ H)] :
    haveI : HasLimit (F ⋙ G ⋙ H) := h
    H.map (limit.post F G) ≫ limit.post (F ⋙ G) H = limit.post F (G ⋙ H) := by
  haveI : HasLimit (F ⋙ G ⋙ H) := h
  ext; erw [assoc, limit.post_π, ← H.map_comp, limit.post_π, limit.post_π]; rfl
end Post
theorem limit.pre_post {D : Type u'} [Category.{v'} D] (E : K ⥤ J) (F : J ⥤ C) (G : C ⥤ D)
    [HasLimit F] [HasLimit (E ⋙ F)] [HasLimit (F ⋙ G)]
    [h : HasLimit ((E ⋙ F) ⋙ G)] :
    haveI : HasLimit (E ⋙ F ⋙ G) := h
    G.map (limit.pre F E) ≫ limit.post (E ⋙ F) G = limit.post F G ≫ limit.pre (F ⋙ G) E := by
  haveI : HasLimit (E ⋙ F ⋙ G) := h
  ext; erw [assoc, limit.post_π, ← G.map_comp, limit.pre_π, assoc, limit.pre_π, limit.post_π]
open CategoryTheory.Equivalence
instance hasLimitEquivalenceComp (e : K ≌ J) [HasLimit F] : HasLimit (e.functor ⋙ F) :=
  HasLimit.mk
    { cone := Cone.whisker e.functor (limit.cone F)
      isLimit := IsLimit.whiskerEquivalence (limit.isLimit F) e }
theorem hasLimitOfEquivalenceComp (e : K ≌ J) [HasLimit (e.functor ⋙ F)] : HasLimit F := by
  haveI : HasLimit (e.inverse ⋙ e.functor ⋙ F) := Limits.hasLimitEquivalenceComp e.symm
  apply hasLimitOfIso (e.invFunIdAssoc F)
section LimFunctor
variable [HasLimitsOfShape J C]
section
@[simps]
def lim : (J ⥤ C) ⥤ C where
  obj F := limit F
  map α := limMap α
  map_id F := by
    apply Limits.limit.hom_ext; intro j
    erw [limMap_π, Category.id_comp, Category.comp_id]
  map_comp α β := by
    apply Limits.limit.hom_ext; intro j
    erw [assoc, IsLimit.fac, IsLimit.fac, ← assoc, IsLimit.fac, assoc]; rfl
end
variable {G : J ⥤ C} (α : F ⟶ G)
theorem limit.map_pre [HasLimitsOfShape K C] (E : K ⥤ J) :
    lim.map α ≫ limit.pre G E = limit.pre F E ≫ lim.map (whiskerLeft E α) := by
  ext
  simp
theorem limit.map_pre' [HasLimitsOfShape K C] (F : J ⥤ C) {E₁ E₂ : K ⥤ J} (α : E₁ ⟶ E₂) :
    limit.pre F E₂ = limit.pre F E₁ ≫ lim.map (whiskerRight α F) := by
  ext1; simp [← category.assoc]
theorem limit.id_pre (F : J ⥤ C) : limit.pre F (𝟭 _) = lim.map (Functor.leftUnitor F).inv := by
  aesop_cat
theorem limit.map_post {D : Type u'} [Category.{v'} D] [HasLimitsOfShape J D] (H : C ⥤ D) :
    H.map (limMap α) ≫ limit.post G H = limit.post F H ≫ limMap (whiskerRight α H) := by
  ext
  simp only [whiskerRight_app, limMap_π, assoc, limit.post_π_assoc, limit.post_π, ← H.map_comp]
def limYoneda :
    lim ⋙ yoneda ⋙ (whiskeringRight _ _ _).obj uliftFunctor.{u₁} ≅ CategoryTheory.cones J C :=
  NatIso.ofComponents fun F => NatIso.ofComponents fun W => limit.homIso F (unop W)
def constLimAdj : (const J : C ⥤ J ⥤ C) ⊣ lim := Adjunction.mk' {
  homEquiv := fun c g ↦
    { toFun := fun f => limit.lift _ ⟨c, f⟩
      invFun := fun f =>
        { app := fun _ => f ≫ limit.π _ _ }
      left_inv := by aesop_cat
      right_inv := by aesop_cat }
  unit := { app := fun _ => limit.lift _ ⟨_, 𝟙 _⟩ }
  counit := { app := fun g => { app := limit.π _ } } }
instance : IsRightAdjoint (lim : (J ⥤ C) ⥤ C) :=
  ⟨_, ⟨constLimAdj⟩⟩
end LimFunctor
instance limMap_mono' {F G : J ⥤ C} [HasLimitsOfShape J C] (α : F ⟶ G) [Mono α] : Mono (limMap α) :=
  (lim : (J ⥤ C) ⥤ C).map_mono α
instance limMap_mono {F G : J ⥤ C} [HasLimit F] [HasLimit G] (α : F ⟶ G) [∀ j, Mono (α.app j)] :
    Mono (limMap α) :=
  ⟨fun {Z} u v h =>
    limit.hom_ext fun j => (cancel_mono (α.app j)).1 <| by simpa using h =≫ limit.π _ j⟩
section Adjunction
variable {L : (J ⥤ C) ⥤ C} (adj : Functor.const _ ⊣ L)
@[simps]
noncomputable def coneOfAdj (F : J ⥤ C) : Cone F where
  pt := L.obj F
  π := adj.counit.app F
@[simps]
def isLimitConeOfAdj (F : J ⥤ C) :
    IsLimit (coneOfAdj adj F) where
  lift s := adj.homEquiv _ _ s.π
  fac s j := by
    have eq := NatTrans.congr_app (adj.counit.naturality s.π) j
    have eq' := NatTrans.congr_app (adj.left_triangle_components s.pt) j
    dsimp at eq eq' ⊢
    rw [adj.homEquiv_unit, assoc, eq, reassoc_of% eq']
  uniq s m hm := (adj.homEquiv _ _).symm.injective (by ext j; simpa using hm j)
end Adjunction
theorem hasLimitsOfShape_of_equivalence {J' : Type u₂} [Category.{v₂} J'] (e : J ≌ J')
    [HasLimitsOfShape J C] : HasLimitsOfShape J' C := by
  constructor
  intro F
  apply hasLimitOfEquivalenceComp e
variable (C)
theorem hasLimitsOfSizeOfUnivLE [UnivLE.{v₂, v₁}] [UnivLE.{u₂, u₁}]
    [HasLimitsOfSize.{v₁, u₁} C] : HasLimitsOfSize.{v₂, u₂} C where
  has_limits_of_shape J {_} := hasLimitsOfShape_of_equivalence
    ((ShrinkHoms.equivalence J).trans <| Shrink.equivalence _).symm
theorem hasLimitsOfSizeShrink [HasLimitsOfSize.{max v₁ v₂, max u₁ u₂} C] :
    HasLimitsOfSize.{v₁, u₁} C := hasLimitsOfSizeOfUnivLE.{max v₁ v₂, max u₁ u₂} C
instance (priority := 100) hasSmallestLimitsOfHasLimits [HasLimits C] : HasLimitsOfSize.{0, 0} C :=
  hasLimitsOfSizeShrink.{0, 0} C
end Limit
section Colimit
structure ColimitCocone (F : J ⥤ C) where
  cocone : Cocone F
  isColimit : IsColimit cocone
class HasColimit (F : J ⥤ C) : Prop where mk' ::
  exists_colimit : Nonempty (ColimitCocone F)
theorem HasColimit.mk {F : J ⥤ C} (d : ColimitCocone F) : HasColimit F :=
  ⟨Nonempty.intro d⟩
def getColimitCocone (F : J ⥤ C) [HasColimit F] : ColimitCocone F :=
  Classical.choice <| HasColimit.exists_colimit
variable (J C)
class HasColimitsOfShape : Prop where
  has_colimit : ∀ F : J ⥤ C, HasColimit F := by infer_instance
@[pp_with_univ]
class HasColimitsOfSize (C : Type u) [Category.{v} C] : Prop where
  has_colimits_of_shape : ∀ (J : Type u₁) [Category.{v₁} J], HasColimitsOfShape J C := by
    infer_instance
abbrev HasColimits (C : Type u) [Category.{v} C] : Prop :=
  HasColimitsOfSize.{v, v} C
theorem HasColimits.hasColimitsOfShape {C : Type u} [Category.{v} C] [HasColimits C] (J : Type v)
    [Category.{v} J] : HasColimitsOfShape J C :=
  HasColimitsOfSize.has_colimits_of_shape J
variable {J C}
instance (priority := 100) hasColimitOfHasColimitsOfShape {J : Type u₁} [Category.{v₁} J]
    [HasColimitsOfShape J C] (F : J ⥤ C) : HasColimit F :=
  HasColimitsOfShape.has_colimit F
instance (priority := 100) hasColimitsOfShapeOfHasColimitsOfSize {J : Type u₁} [Category.{v₁} J]
    [HasColimitsOfSize.{v₁, u₁} C] : HasColimitsOfShape J C :=
  HasColimitsOfSize.has_colimits_of_shape J
def colimit.cocone (F : J ⥤ C) [HasColimit F] : Cocone F :=
  (getColimitCocone F).cocone
def colimit (F : J ⥤ C) [HasColimit F] :=
  (colimit.cocone F).pt
def colimit.ι (F : J ⥤ C) [HasColimit F] (j : J) : F.obj j ⟶ colimit F :=
  (colimit.cocone F).ι.app j
@[reassoc]
theorem colimit.eqToHom_comp_ι (F : J ⥤ C) [HasColimit F] {j j' : J} (hj : j = j') :
    eqToHom (by subst hj; rfl) ≫ colimit.ι F j = colimit.ι F j'  := by
  subst hj
  simp
@[simp]
theorem colimit.cocone_ι {F : J ⥤ C} [HasColimit F] (j : J) :
    (colimit.cocone F).ι.app j = colimit.ι _ j :=
  rfl
@[simp]
theorem colimit.cocone_x {F : J ⥤ C} [HasColimit F] : (colimit.cocone F).pt = colimit F :=
  rfl
@[reassoc (attr := simp)]
theorem colimit.w (F : J ⥤ C) [HasColimit F] {j j' : J} (f : j ⟶ j') :
    F.map f ≫ colimit.ι F j' = colimit.ι F j :=
  (colimit.cocone F).w f
def colimit.isColimit (F : J ⥤ C) [HasColimit F] : IsColimit (colimit.cocone F) :=
  (getColimitCocone F).isColimit
def colimit.desc (F : J ⥤ C) [HasColimit F] (c : Cocone F) : colimit F ⟶ c.pt :=
  (colimit.isColimit F).desc c
@[simp]
theorem colimit.isColimit_desc {F : J ⥤ C} [HasColimit F] (c : Cocone F) :
    (colimit.isColimit F).desc c = colimit.desc F c :=
  rfl
@[reassoc (attr := simp)]
theorem colimit.ι_desc {F : J ⥤ C} [HasColimit F] (c : Cocone F) (j : J) :
    colimit.ι F j ≫ colimit.desc F c = c.ι.app j :=
  IsColimit.fac _ c j
def colimMap {F G : J ⥤ C} [HasColimit F] [HasColimit G] (α : F ⟶ G) : colimit F ⟶ colimit G :=
  IsColimit.map (colimit.isColimit F) _ α
@[reassoc (attr := simp)]
theorem ι_colimMap {F G : J ⥤ C} [HasColimit F] [HasColimit G] (α : F ⟶ G) (j : J) :
    colimit.ι F j ≫ colimMap α = α.app j ≫ colimit.ι G j :=
  colimit.ι_desc _ j
def colimit.coconeMorphism {F : J ⥤ C} [HasColimit F] (c : Cocone F) : colimit.cocone F ⟶ c :=
  (colimit.isColimit F).descCoconeMorphism c
@[simp]
theorem colimit.coconeMorphism_hom {F : J ⥤ C} [HasColimit F] (c : Cocone F) :
    (colimit.coconeMorphism c).hom = colimit.desc F c :=
  rfl
theorem colimit.ι_coconeMorphism {F : J ⥤ C} [HasColimit F] (c : Cocone F) (j : J) :
    colimit.ι F j ≫ (colimit.coconeMorphism c).hom = c.ι.app j := by simp
@[reassoc (attr := simp)]
theorem colimit.comp_coconePointUniqueUpToIso_hom {F : J ⥤ C} [HasColimit F] {c : Cocone F}
    (hc : IsColimit c) (j : J) :
    colimit.ι F j ≫ (IsColimit.coconePointUniqueUpToIso (colimit.isColimit _) hc).hom = c.ι.app j :=
  IsColimit.comp_coconePointUniqueUpToIso_hom _ _ _
@[reassoc (attr := simp)]
theorem colimit.comp_coconePointUniqueUpToIso_inv {F : J ⥤ C} [HasColimit F] {c : Cocone F}
    (hc : IsColimit c) (j : J) :
    colimit.ι F j ≫ (IsColimit.coconePointUniqueUpToIso hc (colimit.isColimit _)).inv = c.ι.app j :=
  IsColimit.comp_coconePointUniqueUpToIso_inv _ _ _
theorem colimit.existsUnique {F : J ⥤ C} [HasColimit F] (t : Cocone F) :
    ∃! d : colimit F ⟶ t.pt, ∀ j, colimit.ι F j ≫ d = t.ι.app j :=
  (colimit.isColimit F).existsUnique _
def colimit.isoColimitCocone {F : J ⥤ C} [HasColimit F] (t : ColimitCocone F) :
    colimit F ≅ t.cocone.pt :=
  IsColimit.coconePointUniqueUpToIso (colimit.isColimit F) t.isColimit
@[reassoc (attr := simp)]
theorem colimit.isoColimitCocone_ι_hom {F : J ⥤ C} [HasColimit F] (t : ColimitCocone F) (j : J) :
    colimit.ι F j ≫ (colimit.isoColimitCocone t).hom = t.cocone.ι.app j := by
  dsimp [colimit.isoColimitCocone, IsColimit.coconePointUniqueUpToIso]
  aesop_cat
@[reassoc (attr := simp)]
theorem colimit.isoColimitCocone_ι_inv {F : J ⥤ C} [HasColimit F] (t : ColimitCocone F) (j : J) :
    t.cocone.ι.app j ≫ (colimit.isoColimitCocone t).inv = colimit.ι F j := by
  dsimp [colimit.isoColimitCocone, IsColimit.coconePointUniqueUpToIso]
  aesop_cat
@[ext]
theorem colimit.hom_ext {F : J ⥤ C} [HasColimit F] {X : C} {f f' : colimit F ⟶ X}
    (w : ∀ j, colimit.ι F j ≫ f = colimit.ι F j ≫ f') : f = f' :=
  (colimit.isColimit F).hom_ext w
@[simp]
theorem colimit.desc_cocone {F : J ⥤ C} [HasColimit F] :
    colimit.desc F (colimit.cocone F) = 𝟙 (colimit F) :=
  (colimit.isColimit _).desc_self
def colimit.homIso (F : J ⥤ C) [HasColimit F] (W : C) :
    ULift.{u₁} (colimit F ⟶ W : Type v) ≅ F.cocones.obj W :=
  (colimit.isColimit F).homIso W
@[simp]
theorem colimit.homIso_hom (F : J ⥤ C) [HasColimit F] {W : C} (f : ULift (colimit F ⟶ W)) :
    (colimit.homIso F W).hom f = (colimit.cocone F).ι ≫ (const J).map f.down :=
  (colimit.isColimit F).homIso_hom f
def colimit.homIso' (F : J ⥤ C) [HasColimit F] (W : C) :
    ULift.{u₁} (colimit F ⟶ W : Type v) ≅
      { p : ∀ j, F.obj j ⟶ W // ∀ {j j'} (f : j ⟶ j'), F.map f ≫ p j' = p j } :=
  (colimit.isColimit F).homIso' W
theorem colimit.desc_extend (F : J ⥤ C) [HasColimit F] (c : Cocone F) {X : C} (f : c.pt ⟶ X) :
    colimit.desc F (c.extend f) = colimit.desc F c ≫ f := by ext1; rw [← Category.assoc]; simp
theorem hasColimitOfIso {F G : J ⥤ C} [HasColimit F] (α : G ≅ F) : HasColimit G :=
  HasColimit.mk
    { cocone := (Cocones.precompose α.hom).obj (colimit.cocone F)
      isColimit := (IsColimit.precomposeHomEquiv _ _).symm (colimit.isColimit F) }
theorem HasColimit.ofCoconesIso {K : Type u₁} [Category.{v₂} K] (F : J ⥤ C) (G : K ⥤ C)
    (h : F.cocones ≅ G.cocones) [HasColimit F] : HasColimit G :=
  HasColimit.mk ⟨_, IsColimit.ofNatIso (IsColimit.natIso (colimit.isColimit F) ≪≫ h)⟩
def HasColimit.isoOfNatIso {F G : J ⥤ C} [HasColimit F] [HasColimit G] (w : F ≅ G) :
    colimit F ≅ colimit G :=
  IsColimit.coconePointsIsoOfNatIso (colimit.isColimit F) (colimit.isColimit G) w
@[reassoc (attr := simp)]
theorem HasColimit.isoOfNatIso_ι_hom {F G : J ⥤ C} [HasColimit F] [HasColimit G] (w : F ≅ G)
    (j : J) : colimit.ι F j ≫ (HasColimit.isoOfNatIso w).hom = w.hom.app j ≫ colimit.ι G j :=
  IsColimit.comp_coconePointsIsoOfNatIso_hom _ _ _ _
@[reassoc (attr := simp)]
theorem HasColimit.isoOfNatIso_ι_inv {F G : J ⥤ C} [HasColimit F] [HasColimit G] (w : F ≅ G)
    (j : J) : colimit.ι G j ≫ (HasColimit.isoOfNatIso w).inv = w.inv.app j ≫ colimit.ι F j :=
  IsColimit.comp_coconePointsIsoOfNatIso_inv _ _ _ _
@[reassoc (attr := simp)]
theorem HasColimit.isoOfNatIso_hom_desc {F G : J ⥤ C} [HasColimit F] [HasColimit G] (t : Cocone G)
    (w : F ≅ G) :
    (HasColimit.isoOfNatIso w).hom ≫ colimit.desc G t =
      colimit.desc F ((Cocones.precompose w.hom).obj _) :=
  IsColimit.coconePointsIsoOfNatIso_hom_desc _ _ _
@[reassoc (attr := simp)]
theorem HasColimit.isoOfNatIso_inv_desc {F G : J ⥤ C} [HasColimit F] [HasColimit G] (t : Cocone F)
    (w : F ≅ G) :
    (HasColimit.isoOfNatIso w).inv ≫ colimit.desc F t =
      colimit.desc G ((Cocones.precompose w.inv).obj _) :=
  IsColimit.coconePointsIsoOfNatIso_inv_desc _ _ _
def HasColimit.isoOfEquivalence {F : J ⥤ C} [HasColimit F] {G : K ⥤ C} [HasColimit G] (e : J ≌ K)
    (w : e.functor ⋙ G ≅ F) : colimit F ≅ colimit G :=
  IsColimit.coconePointsIsoOfEquivalence (colimit.isColimit F) (colimit.isColimit G) e w
@[simp]
theorem HasColimit.isoOfEquivalence_hom_π {F : J ⥤ C} [HasColimit F] {G : K ⥤ C} [HasColimit G]
    (e : J ≌ K) (w : e.functor ⋙ G ≅ F) (j : J) :
    colimit.ι F j ≫ (HasColimit.isoOfEquivalence e w).hom =
      F.map (e.unit.app j) ≫ w.inv.app _ ≫ colimit.ι G _ := by
  simp [HasColimit.isoOfEquivalence, IsColimit.coconePointsIsoOfEquivalence_inv]
@[simp]
theorem HasColimit.isoOfEquivalence_inv_π {F : J ⥤ C} [HasColimit F] {G : K ⥤ C} [HasColimit G]
    (e : J ≌ K) (w : e.functor ⋙ G ≅ F) (k : K) :
    colimit.ι G k ≫ (HasColimit.isoOfEquivalence e w).inv =
      G.map (e.counitInv.app k) ≫ w.hom.app (e.inverse.obj k) ≫ colimit.ι F (e.inverse.obj k) := by
  simp [HasColimit.isoOfEquivalence, IsColimit.coconePointsIsoOfEquivalence_inv]
section Pre
variable (F)
variable [HasColimit F] (E : K ⥤ J) [HasColimit (E ⋙ F)]
def colimit.pre : colimit (E ⋙ F) ⟶ colimit F :=
  colimit.desc (E ⋙ F) ((colimit.cocone F).whisker E)
@[reassoc (attr := simp)]
theorem colimit.ι_pre (k : K) : colimit.ι (E ⋙ F) k ≫ colimit.pre F E = colimit.ι F (E.obj k) := by
  erw [IsColimit.fac]
  rfl
@[reassoc (attr := simp)]
theorem colimit.ι_inv_pre [IsIso (pre F E)] (k : K) :
    colimit.ι F (E.obj k) ≫ inv (colimit.pre F E) = colimit.ι (E ⋙ F) k := by
  simp [IsIso.comp_inv_eq]
@[reassoc (attr := simp)]
theorem colimit.pre_desc (c : Cocone F) :
    colimit.pre F E ≫ colimit.desc F c = colimit.desc (E ⋙ F) (c.whisker E) := by
  ext; rw [← assoc, colimit.ι_pre]; simp
variable {L : Type u₃} [Category.{v₃} L]
variable (D : L ⥤ K)
@[simp]
theorem colimit.pre_pre [h : HasColimit (D ⋙ E ⋙ F)] :
    haveI : HasColimit ((D ⋙ E) ⋙ F) := h
    colimit.pre (E ⋙ F) D ≫ colimit.pre F E = colimit.pre F (D ⋙ E) := by
  ext j
  rw [← assoc, colimit.ι_pre, colimit.ι_pre]
  haveI : HasColimit ((D ⋙ E) ⋙ F) := h
  exact (colimit.ι_pre F (D ⋙ E) j).symm
variable {E F}
theorem colimit.pre_eq (s : ColimitCocone (E ⋙ F)) (t : ColimitCocone F) :
    colimit.pre F E =
      (colimit.isoColimitCocone s).hom ≫
        s.isColimit.desc (t.cocone.whisker E) ≫ (colimit.isoColimitCocone t).inv := by
  aesop_cat
end Pre
section Post
variable {D : Type u'} [Category.{v'} D]
variable (F)
variable [HasColimit F] (G : C ⥤ D) [HasColimit (F ⋙ G)]
def colimit.post : colimit (F ⋙ G) ⟶ G.obj (colimit F) :=
  colimit.desc (F ⋙ G) (G.mapCocone (colimit.cocone F))
@[reassoc (attr := simp)]
theorem colimit.ι_post (j : J) :
    colimit.ι (F ⋙ G) j ≫ colimit.post F G = G.map (colimit.ι F j) := by
  erw [IsColimit.fac]
  rfl
@[simp]
theorem colimit.post_desc (c : Cocone F) :
    colimit.post F G ≫ G.map (colimit.desc F c) = colimit.desc (F ⋙ G) (G.mapCocone c) := by
  ext
  rw [← assoc, colimit.ι_post, ← G.map_comp, colimit.ι_desc, colimit.ι_desc]
  rfl
@[simp]
theorem colimit.post_post {E : Type u''} [Category.{v''} E] (H : D ⥤ E)
    [h : HasColimit ((F ⋙ G) ⋙ H)] : haveI : HasColimit (F ⋙ G ⋙ H) := h
    colimit.post (F ⋙ G) H ≫ H.map (colimit.post F G) = colimit.post F (G ⋙ H) := by
  ext j
  rw [← assoc, colimit.ι_post, ← H.map_comp, colimit.ι_post]
  haveI : HasColimit (F ⋙ G ⋙ H) := h
  exact (colimit.ι_post F (G ⋙ H) j).symm
end Post
theorem colimit.pre_post {D : Type u'} [Category.{v'} D] (E : K ⥤ J) (F : J ⥤ C) (G : C ⥤ D)
    [HasColimit F] [HasColimit (E ⋙ F)] [HasColimit (F ⋙ G)] [h : HasColimit ((E ⋙ F) ⋙ G)] :
    haveI : HasColimit (E ⋙ F ⋙ G) := h
    colimit.post (E ⋙ F) G ≫ G.map (colimit.pre F E) =
      colimit.pre (F ⋙ G) E ≫ colimit.post F G := by
  ext j
  rw [← assoc, colimit.ι_post, ← G.map_comp, colimit.ι_pre, ← assoc]
  haveI : HasColimit (E ⋙ F ⋙ G) := h
  erw [colimit.ι_pre (F ⋙ G) E j, colimit.ι_post]
open CategoryTheory.Equivalence
instance hasColimit_equivalence_comp (e : K ≌ J) [HasColimit F] : HasColimit (e.functor ⋙ F) :=
  HasColimit.mk
    { cocone := Cocone.whisker e.functor (colimit.cocone F)
      isColimit := IsColimit.whiskerEquivalence (colimit.isColimit F) e }
theorem hasColimit_of_equivalence_comp (e : K ≌ J) [HasColimit (e.functor ⋙ F)] : HasColimit F := by
  haveI : HasColimit (e.inverse ⋙ e.functor ⋙ F) := Limits.hasColimit_equivalence_comp e.symm
  apply hasColimitOfIso (e.invFunIdAssoc F).symm
section ColimFunctor
variable [HasColimitsOfShape J C]
section
@[simps] 
def colim : (J ⥤ C) ⥤ C where
  obj F := colimit F
  map α := colimMap α
end
variable {G : J ⥤ C} (α : F ⟶ G)
@[reassoc]
theorem colimit.ι_map (j : J) : colimit.ι F j ≫ colim.map α = α.app j ≫ colimit.ι G j := by simp
@[simp] 
theorem colimit.map_desc (c : Cocone G) :
    colimMap α ≫ colimit.desc G c = colimit.desc F ((Cocones.precompose α).obj c) := by
  ext j
  simp [← assoc, colimit.ι_map, assoc, colimit.ι_desc, colimit.ι_desc]
theorem colimit.pre_map [HasColimitsOfShape K C] (E : K ⥤ J) :
    colimit.pre F E ≫ colim.map α = colim.map (whiskerLeft E α) ≫ colimit.pre G E := by
  ext
  rw [← assoc, colimit.ι_pre, colimit.ι_map, ← assoc, colimit.ι_map, assoc, colimit.ι_pre]
  rfl
theorem colimit.pre_map' [HasColimitsOfShape K C] (F : J ⥤ C) {E₁ E₂ : K ⥤ J} (α : E₁ ⟶ E₂) :
    colimit.pre F E₁ = colim.map (whiskerRight α F) ≫ colimit.pre F E₂ := by
  ext1
  simp [← assoc, assoc]
theorem colimit.pre_id (F : J ⥤ C) :
    colimit.pre F (𝟭 _) = colim.map (Functor.leftUnitor F).hom := by aesop_cat
theorem colimit.map_post {D : Type u'} [Category.{v'} D] [HasColimitsOfShape J D]
    (H : C ⥤ D) :
          colimit.post
          F H ≫
        H.map (colim.map α) =
      colim.map (whiskerRight α H) ≫ colimit.post G H := by
  ext
  rw [← assoc, colimit.ι_post, ← H.map_comp, colimit.ι_map, H.map_comp]
  rw [← assoc, colimit.ι_map, assoc, colimit.ι_post]
  rfl
def colimCoyoneda : colim.op ⋙ coyoneda ⋙ (whiskeringRight _ _ _).obj uliftFunctor.{u₁}
    ≅ CategoryTheory.cocones J C :=
  NatIso.ofComponents fun F => NatIso.ofComponents fun W => colimit.homIso (unop F) W
def colimConstAdj : (colim : (J ⥤ C) ⥤ C) ⊣ const J := Adjunction.mk' {
  homEquiv := fun f c ↦
    { toFun := fun g =>
        { app := fun _ => colimit.ι _ _ ≫ g }
      invFun := fun g => colimit.desc _ ⟨_, g⟩
      left_inv := by aesop_cat
      right_inv := by aesop_cat }
  unit := { app := fun g => { app := colimit.ι _ } }
  counit := { app := fun _ => colimit.desc _ ⟨_, 𝟙 _⟩ } }
instance : IsLeftAdjoint (colim : (J ⥤ C) ⥤ C) :=
  ⟨_, ⟨colimConstAdj⟩⟩
end ColimFunctor
instance colimMap_epi' {F G : J ⥤ C} [HasColimitsOfShape J C] (α : F ⟶ G) [Epi α] :
    Epi (colimMap α) :=
  (colim : (J ⥤ C) ⥤ C).map_epi α
instance colimMap_epi {F G : J ⥤ C} [HasColimit F] [HasColimit G] (α : F ⟶ G) [∀ j, Epi (α.app j)] :
    Epi (colimMap α) :=
  ⟨fun {Z} u v h =>
    colimit.hom_ext fun j => (cancel_epi (α.app j)).1 <| by simpa using colimit.ι _ j ≫= h⟩
theorem hasColimitsOfShape_of_equivalence {J' : Type u₂} [Category.{v₂} J'] (e : J ≌ J')
    [HasColimitsOfShape J C] : HasColimitsOfShape J' C := by
  constructor
  intro F
  apply hasColimit_of_equivalence_comp e
variable (C)
theorem hasColimitsOfSizeOfUnivLE [UnivLE.{v₂, v₁}] [UnivLE.{u₂, u₁}]
    [HasColimitsOfSize.{v₁, u₁} C] : HasColimitsOfSize.{v₂, u₂} C where
  has_colimits_of_shape J {_} := hasColimitsOfShape_of_equivalence
    ((ShrinkHoms.equivalence J).trans <| Shrink.equivalence _).symm
theorem hasColimitsOfSizeShrink [HasColimitsOfSize.{max v₁ v₂, max u₁ u₂} C] :
    HasColimitsOfSize.{v₁, u₁} C := hasColimitsOfSizeOfUnivLE.{max v₁ v₂, max u₁ u₂} C
instance (priority := 100) hasSmallestColimitsOfHasColimits [HasColimits C] :
    HasColimitsOfSize.{0, 0} C :=
  hasColimitsOfSizeShrink.{0, 0} C
end Colimit
section Opposite
def IsLimit.op {t : Cone F} (P : IsLimit t) : IsColimit t.op where
  desc s := (P.lift s.unop).op
  fac s j := congrArg Quiver.Hom.op (P.fac s.unop (unop j))
  uniq s m w := by
    dsimp
    rw [← P.uniq s.unop m.unop]
    · rfl
    · dsimp
      intro j
      rw [← w]
      rfl
def IsColimit.op {t : Cocone F} (P : IsColimit t) : IsLimit t.op where
  lift s := (P.desc s.unop).op
  fac s j := congrArg Quiver.Hom.op (P.fac s.unop (unop j))
  uniq s m w := by
    dsimp
    rw [← P.uniq s.unop m.unop]
    · rfl
    · dsimp
      intro j
      rw [← w]
      rfl
def IsLimit.unop {t : Cone F.op} (P : IsLimit t) : IsColimit t.unop where
  desc s := (P.lift s.op).unop
  fac s j := congrArg Quiver.Hom.unop (P.fac s.op (Opposite.op j))
  uniq s m w := by
    dsimp
    rw [← P.uniq s.op m.op]
    · rfl
    · dsimp
      intro j
      rw [← w]
      rfl
def IsColimit.unop {t : Cocone F.op} (P : IsColimit t) : IsLimit t.unop where
  lift s := (P.desc s.op).unop
  fac s j := congrArg Quiver.Hom.unop (P.fac s.op (Opposite.op j))
  uniq s m w := by
    dsimp
    rw [← P.uniq s.op m.op]
    · rfl
    · dsimp
      intro j
      rw [← w]
      rfl
def isLimitOfOp {t : Cone F} (P : IsColimit t.op) : IsLimit t :=
  P.unop
def isColimitOfOp {t : Cocone F} (P : IsLimit t.op) : IsColimit t :=
  P.unop
def isLimitOfUnop {t : Cone F.op} (P : IsColimit t.unop) : IsLimit t :=
  P.op
def isColimitOfUnop {t : Cocone F.op} (P : IsLimit t.unop) : IsColimit t :=
  P.op
def isLimitEquivIsColimitOp {t : Cone F} : IsLimit t ≃ IsColimit t.op :=
  equivOfSubsingletonOfSubsingleton IsLimit.op isLimitOfOp
def isColimitEquivIsLimitOp {t : Cocone F} : IsColimit t ≃ IsLimit t.op :=
  equivOfSubsingletonOfSubsingleton IsColimit.op isColimitOfOp
end Opposite
end Limits
end CategoryTheory