import Mathlib.CategoryTheory.Limits.Preserves.Basic
open CategoryTheory CategoryTheory.Limits
noncomputable section
namespace CategoryTheory
universe w' w v₁ v₂ v₃ u₁ u₂ u₃
variable {C : Type u₁} [Category.{v₁} C]
section Creates
variable {D : Type u₂} [Category.{v₂} D]
variable {J : Type w} [Category.{w'} J] {K : J ⥤ C}
structure LiftableCone (K : J ⥤ C) (F : C ⥤ D) (c : Cone (K ⋙ F)) where
  liftedCone : Cone K
  validLift : F.mapCone liftedCone ≅ c
structure LiftableCocone (K : J ⥤ C) (F : C ⥤ D) (c : Cocone (K ⋙ F)) where
  liftedCocone : Cocone K
  validLift : F.mapCocone liftedCocone ≅ c
class CreatesLimit (K : J ⥤ C) (F : C ⥤ D) extends ReflectsLimit K F where
  lifts : ∀ c, IsLimit c → LiftableCone K F c
class CreatesLimitsOfShape (J : Type w) [Category.{w'} J] (F : C ⥤ D) where
  CreatesLimit : ∀ {K : J ⥤ C}, CreatesLimit K F := by infer_instance
@[nolint checkUnivs, pp_with_univ]
class CreatesLimitsOfSize (F : C ⥤ D) where
  CreatesLimitsOfShape : ∀ {J : Type w} [Category.{w'} J], CreatesLimitsOfShape J F := by
    infer_instance
abbrev CreatesLimits (F : C ⥤ D) :=
  CreatesLimitsOfSize.{v₂, v₂} F
class CreatesColimit (K : J ⥤ C) (F : C ⥤ D) extends ReflectsColimit K F where
  lifts : ∀ c, IsColimit c → LiftableCocone K F c
class CreatesColimitsOfShape (J : Type w) [Category.{w'} J] (F : C ⥤ D) where
  CreatesColimit : ∀ {K : J ⥤ C}, CreatesColimit K F := by infer_instance
@[nolint checkUnivs, pp_with_univ]
class CreatesColimitsOfSize (F : C ⥤ D) where
  CreatesColimitsOfShape : ∀ {J : Type w} [Category.{w'} J], CreatesColimitsOfShape J F := by
    infer_instance
abbrev CreatesColimits (F : C ⥤ D) :=
  CreatesColimitsOfSize.{v₂, v₂} F
attribute [instance 100] CreatesLimitsOfShape.CreatesLimit CreatesLimitsOfSize.CreatesLimitsOfShape
  CreatesColimitsOfShape.CreatesColimit CreatesColimitsOfSize.CreatesColimitsOfShape
def liftLimit {K : J ⥤ C} {F : C ⥤ D} [CreatesLimit K F] {c : Cone (K ⋙ F)} (t : IsLimit c) :
    Cone K :=
  (CreatesLimit.lifts c t).liftedCone
def liftedLimitMapsToOriginal {K : J ⥤ C} {F : C ⥤ D} [CreatesLimit K F] {c : Cone (K ⋙ F)}
    (t : IsLimit c) : F.mapCone (liftLimit t) ≅ c :=
  (CreatesLimit.lifts c t).validLift
lemma liftedLimitMapsToOriginal_inv_map_π
    {K : J ⥤ C} {F : C ⥤ D} [CreatesLimit K F] {c : Cone (K ⋙ F)} (t : IsLimit c) (j : J) :
      (liftedLimitMapsToOriginal t).inv.hom ≫ F.map ((liftLimit t).π.app j) = c.π.app j := by
  rw [show F.map ((liftLimit t).π.app j) = (liftedLimitMapsToOriginal t).hom.hom ≫ c.π.app j
    from (by simp), ← Category.assoc, ← Cone.category_comp_hom]
  simp
def liftedLimitIsLimit {K : J ⥤ C} {F : C ⥤ D} [CreatesLimit K F] {c : Cone (K ⋙ F)}
    (t : IsLimit c) : IsLimit (liftLimit t) :=
  isLimitOfReflects _ (IsLimit.ofIsoLimit t (liftedLimitMapsToOriginal t).symm)
theorem hasLimit_of_created (K : J ⥤ C) (F : C ⥤ D) [HasLimit (K ⋙ F)] [CreatesLimit K F] :
    HasLimit K :=
  HasLimit.mk
    { cone := liftLimit (limit.isLimit (K ⋙ F))
      isLimit := liftedLimitIsLimit _ }
theorem hasLimitsOfShape_of_hasLimitsOfShape_createsLimitsOfShape (F : C ⥤ D) [HasLimitsOfShape J D]
    [CreatesLimitsOfShape J F] : HasLimitsOfShape J C :=
  ⟨fun G => hasLimit_of_created G F⟩
theorem hasLimits_of_hasLimits_createsLimits (F : C ⥤ D) [HasLimitsOfSize.{w, w'} D]
    [CreatesLimitsOfSize.{w, w'} F] : HasLimitsOfSize.{w, w'} C :=
  ⟨fun _ _ => hasLimitsOfShape_of_hasLimitsOfShape_createsLimitsOfShape F⟩
def liftColimit {K : J ⥤ C} {F : C ⥤ D} [CreatesColimit K F] {c : Cocone (K ⋙ F)}
    (t : IsColimit c) : Cocone K :=
  (CreatesColimit.lifts c t).liftedCocone
def liftedColimitMapsToOriginal {K : J ⥤ C} {F : C ⥤ D} [CreatesColimit K F] {c : Cocone (K ⋙ F)}
    (t : IsColimit c) : F.mapCocone (liftColimit t) ≅ c :=
  (CreatesColimit.lifts c t).validLift
def liftedColimitIsColimit {K : J ⥤ C} {F : C ⥤ D} [CreatesColimit K F] {c : Cocone (K ⋙ F)}
    (t : IsColimit c) : IsColimit (liftColimit t) :=
  isColimitOfReflects _ (IsColimit.ofIsoColimit t (liftedColimitMapsToOriginal t).symm)
theorem hasColimit_of_created (K : J ⥤ C) (F : C ⥤ D) [HasColimit (K ⋙ F)] [CreatesColimit K F] :
    HasColimit K :=
  HasColimit.mk
    { cocone := liftColimit (colimit.isColimit (K ⋙ F))
      isColimit := liftedColimitIsColimit _ }
theorem hasColimitsOfShape_of_hasColimitsOfShape_createsColimitsOfShape (F : C ⥤ D)
    [HasColimitsOfShape J D] [CreatesColimitsOfShape J F] : HasColimitsOfShape J C :=
  ⟨fun G => hasColimit_of_created G F⟩
theorem hasColimits_of_hasColimits_createsColimits (F : C ⥤ D) [HasColimitsOfSize.{w, w'} D]
    [CreatesColimitsOfSize.{w, w'} F] : HasColimitsOfSize.{w, w'} C :=
  ⟨fun _ _ => hasColimitsOfShape_of_hasColimitsOfShape_createsColimitsOfShape F⟩
instance (priority := 10) reflectsLimitsOfShapeOfCreatesLimitsOfShape (F : C ⥤ D)
    [CreatesLimitsOfShape J F] : ReflectsLimitsOfShape J F where
instance (priority := 10) reflectsLimitsOfCreatesLimits (F : C ⥤ D)
    [CreatesLimitsOfSize.{w, w'} F] : ReflectsLimitsOfSize.{w, w'} F where
instance (priority := 10) reflectsColimitsOfShapeOfCreatesColimitsOfShape (F : C ⥤ D)
    [CreatesColimitsOfShape J F] : ReflectsColimitsOfShape J F where
instance (priority := 10) reflectsColimitsOfCreatesColimits (F : C ⥤ D)
    [CreatesColimitsOfSize.{w, w'} F] : ReflectsColimitsOfSize.{w, w'} F where
structure LiftsToLimit (K : J ⥤ C) (F : C ⥤ D) (c : Cone (K ⋙ F)) (t : IsLimit c) extends
  LiftableCone K F c where
  makesLimit : IsLimit liftedCone
structure LiftsToColimit (K : J ⥤ C) (F : C ⥤ D) (c : Cocone (K ⋙ F)) (t : IsColimit c) extends
  LiftableCocone K F c where
  makesColimit : IsColimit liftedCocone
def createsLimitOfReflectsIso {K : J ⥤ C} {F : C ⥤ D} [F.ReflectsIsomorphisms]
    (h : ∀ c t, LiftsToLimit K F c t) : CreatesLimit K F where
  lifts c t := (h c t).toLiftableCone
  toReflectsLimit :=
    { reflects := fun {d} hd => ⟨by
        let d' : Cone K := (h (F.mapCone d) hd).toLiftableCone.liftedCone
        let i : F.mapCone d' ≅ F.mapCone d :=
          (h (F.mapCone d) hd).toLiftableCone.validLift
        let hd' : IsLimit d' := (h (F.mapCone d) hd).makesLimit
        let f : d ⟶ d' := hd'.liftConeMorphism d
        have : (Cones.functoriality K F).map f = i.inv :=
          (hd.ofIsoLimit i.symm).uniq_cone_morphism
        haveI : IsIso ((Cones.functoriality K F).map f) := by
          rw [this]
          infer_instance
        haveI : IsIso f := isIso_of_reflects_iso f (Cones.functoriality K F)
        exact IsLimit.ofIsoLimit hd' (asIso f).symm⟩ }
def createsLimitOfReflectsIso' {K : J ⥤ C} {F : C ⥤ D} [F.ReflectsIsomorphisms]
    {c : Cone (K ⋙ F)} (hc : IsLimit c) (h : LiftsToLimit K F c hc) : CreatesLimit K F :=
  createsLimitOfReflectsIso fun _ t =>
    { liftedCone := h.liftedCone
      validLift := h.validLift ≪≫ IsLimit.uniqueUpToIso hc t
      makesLimit := h.makesLimit }
def createsLimitOfFullyFaithfulOfLift' {K : J ⥤ C} {F : C ⥤ D} [F.Full] [F.Faithful]
    {l : Cone (K ⋙ F)} (hl : IsLimit l) (c : Cone K) (i : F.mapCone c ≅ l) :
    CreatesLimit K F :=
  createsLimitOfReflectsIso fun _ t =>
    { liftedCone := c
      validLift := i ≪≫ IsLimit.uniqueUpToIso hl t
      makesLimit :=
        IsLimit.ofFaithful F (IsLimit.ofIsoLimit hl i.symm) _ fun _ => F.map_preimage _ }
def createsLimitOfFullyFaithfulOfLift {K : J ⥤ C} {F : C ⥤ D} [F.Full] [F.Faithful]
    [HasLimit (K ⋙ F)] (c : Cone K) (i : F.mapCone c ≅ limit.cone (K ⋙ F)) :
    CreatesLimit K F :=
  createsLimitOfFullyFaithfulOfLift' (limit.isLimit _) c i
def createsLimitOfFullyFaithfulOfIso' {K : J ⥤ C} {F : C ⥤ D} [F.Full] [F.Faithful]
    {l : Cone (K ⋙ F)} (hl : IsLimit l) (X : C) (i : F.obj X ≅ l.pt) : CreatesLimit K F :=
  createsLimitOfFullyFaithfulOfLift' hl
    { pt := X
      π :=
        { app := fun j => F.preimage (i.hom ≫ l.π.app j)
          naturality := fun Y Z f =>
            F.map_injective <| by
              dsimp
              simpa using (l.w f).symm } }
    (Cones.ext i fun j => by simp only [Functor.map_preimage, Functor.mapCone_π_app])
def createsLimitOfFullyFaithfulOfIso {K : J ⥤ C} {F : C ⥤ D} [F.Full] [F.Faithful]
    [HasLimit (K ⋙ F)] (X : C) (i : F.obj X ≅ limit (K ⋙ F)) : CreatesLimit K F :=
  createsLimitOfFullyFaithfulOfIso' (limit.isLimit _) X i
def createsLimitOfFullyFaithfulOfPreserves {K : J ⥤ C} {F : C ⥤ D} [F.Full] [F.Faithful]
    [HasLimit K] [PreservesLimit K F] : CreatesLimit K F :=
  createsLimitOfFullyFaithfulOfLift' (isLimitOfPreserves _ (limit.isLimit K)) _ (Iso.refl _)
instance (priority := 100) preservesLimit_of_createsLimit_and_hasLimit (K : J ⥤ C) (F : C ⥤ D)
    [CreatesLimit K F] [HasLimit (K ⋙ F)] : PreservesLimit K F where
  preserves t := ⟨IsLimit.ofIsoLimit (limit.isLimit _)
    ((liftedLimitMapsToOriginal (limit.isLimit _)).symm ≪≫
      (Cones.functoriality K F).mapIso ((liftedLimitIsLimit (limit.isLimit _)).uniqueUpToIso t))⟩
@[deprecated "No deprecation message was provided." (since := "2024-11-19")]
lemma preservesLimitOfCreatesLimitAndHasLimit (K : J ⥤ C) (F : C ⥤ D)
    [CreatesLimit K F] [HasLimit (K ⋙ F)] : PreservesLimit K F :=
  preservesLimit_of_createsLimit_and_hasLimit _ _
instance (priority := 100) preservesLimitOfShape_of_createsLimitsOfShape_and_hasLimitsOfShape
    (F : C ⥤ D) [CreatesLimitsOfShape J F] [HasLimitsOfShape J D] : PreservesLimitsOfShape J F where
@[deprecated "No deprecation message was provided." (since := "2024-11-19")]
lemma preservesLimitOfShapeOfCreatesLimitsOfShapeAndHasLimitsOfShape
    (F : C ⥤ D) [CreatesLimitsOfShape J F] [HasLimitsOfShape J D] :
    PreservesLimitsOfShape J F :=
  preservesLimitOfShape_of_createsLimitsOfShape_and_hasLimitsOfShape _
instance (priority := 100) preservesLimits_of_createsLimits_and_hasLimits (F : C ⥤ D)
    [CreatesLimitsOfSize.{w, w'} F] [HasLimitsOfSize.{w, w'} D] :
    PreservesLimitsOfSize.{w, w'} F where
@[deprecated "No deprecation message was provided." (since := "2024-11-19")]
lemma preservesLimitsOfCreatesLimitsAndHasLimits (F : C ⥤ D)
    [CreatesLimitsOfSize.{w, w'} F] [HasLimitsOfSize.{w, w'} D] :
    PreservesLimitsOfSize.{w, w'} F :=
  preservesLimits_of_createsLimits_and_hasLimits _
def createsColimitOfReflectsIso {K : J ⥤ C} {F : C ⥤ D} [F.ReflectsIsomorphisms]
    (h : ∀ c t, LiftsToColimit K F c t) : CreatesColimit K F where
  lifts c t := (h c t).toLiftableCocone
  toReflectsColimit :=
    { reflects := fun {d} hd => ⟨by
        let d' : Cocone K := (h (F.mapCocone d) hd).toLiftableCocone.liftedCocone
        let i : F.mapCocone d' ≅ F.mapCocone d :=
          (h (F.mapCocone d) hd).toLiftableCocone.validLift
        let hd' : IsColimit d' := (h (F.mapCocone d) hd).makesColimit
        let f : d' ⟶ d := hd'.descCoconeMorphism d
        have : (Cocones.functoriality K F).map f = i.hom :=
          (hd.ofIsoColimit i.symm).uniq_cocone_morphism
        haveI : IsIso ((Cocones.functoriality K F).map f) := by
          rw [this]
          infer_instance
        haveI := isIso_of_reflects_iso f (Cocones.functoriality K F)
        exact IsColimit.ofIsoColimit hd' (asIso f)⟩ }
def createsColimitOfReflectsIso' {K : J ⥤ C} {F : C ⥤ D} [F.ReflectsIsomorphisms]
    {c : Cocone (K ⋙ F)} (hc : IsColimit c) (h : LiftsToColimit K F c hc) : CreatesColimit K F :=
  createsColimitOfReflectsIso fun _ t =>
    { liftedCocone := h.liftedCocone
      validLift := h.validLift ≪≫ IsColimit.uniqueUpToIso hc t
      makesColimit := h.makesColimit }
def createsColimitOfFullyFaithfulOfLift' {K : J ⥤ C} {F : C ⥤ D} [F.Full] [F.Faithful]
    {l : Cocone (K ⋙ F)} (hl : IsColimit l) (c : Cocone K) (i : F.mapCocone c ≅ l) :
    CreatesColimit K F :=
  createsColimitOfReflectsIso fun _ t =>
    { liftedCocone := c
      validLift := i ≪≫ IsColimit.uniqueUpToIso hl t
      makesColimit :=
        IsColimit.ofFaithful F (IsColimit.ofIsoColimit hl i.symm) _ fun _ => F.map_preimage _ }
def createsColimitOfFullyFaithfulOfLift {K : J ⥤ C} {F : C ⥤ D} [F.Full] [F.Faithful]
    [HasColimit (K ⋙ F)] (c : Cocone K) (i : F.mapCocone c ≅ colimit.cocone (K ⋙ F)) :
    CreatesColimit K F :=
  createsColimitOfFullyFaithfulOfLift' (colimit.isColimit _) c i
def createsColimitOfFullyFaithfulOfPreserves {K : J ⥤ C} {F : C ⥤ D} [F.Full] [F.Faithful]
    [HasColimit K] [PreservesColimit K F] : CreatesColimit K F :=
  createsColimitOfFullyFaithfulOfLift' (isColimitOfPreserves _ (colimit.isColimit K)) _
    (Iso.refl _)
def createsColimitOfFullyFaithfulOfIso' {K : J ⥤ C} {F : C ⥤ D} [F.Full] [F.Faithful]
    {l : Cocone (K ⋙ F)} (hl : IsColimit l) (X : C) (i : F.obj X ≅ l.pt) : CreatesColimit K F :=
  createsColimitOfFullyFaithfulOfLift' hl
    { pt := X
      ι :=
        { app := fun j => F.preimage (l.ι.app j ≫ i.inv)
          naturality := fun Y Z f =>
            F.map_injective <| by
              dsimp
              simpa [← cancel_mono i.hom] using l.w f } }
    (Cocones.ext i fun j => by simp)
def createsColimitOfFullyFaithfulOfIso {K : J ⥤ C} {F : C ⥤ D} [F.Full] [F.Faithful]
    [HasColimit (K ⋙ F)] (X : C) (i : F.obj X ≅ colimit (K ⋙ F)) : CreatesColimit K F :=
  createsColimitOfFullyFaithfulOfIso' (colimit.isColimit _) X i
instance (priority := 100) preservesColimit_of_createsColimit_and_hasColimit (K : J ⥤ C) (F : C ⥤ D)
    [CreatesColimit K F] [HasColimit (K ⋙ F)] : PreservesColimit K F where
  preserves t :=
    ⟨IsColimit.ofIsoColimit (colimit.isColimit _)
      ((liftedColimitMapsToOriginal (colimit.isColimit _)).symm ≪≫
        (Cocones.functoriality K F).mapIso
          ((liftedColimitIsColimit (colimit.isColimit _)).uniqueUpToIso t))⟩
@[deprecated "No deprecation message was provided." (since := "2024-11-19")]
lemma preservesColimitOfCreatesColimitAndHasColimit (K : J ⥤ C) (F : C ⥤ D)
    [CreatesColimit K F] [HasColimit (K ⋙ F)] : PreservesColimit K F :=
  preservesColimit_of_createsColimit_and_hasColimit _ _
instance (priority := 100) preservesColimitOfShape_of_createsColimitsOfShape_and_hasColimitsOfShape
    (F : C ⥤ D) [CreatesColimitsOfShape J F] [HasColimitsOfShape J D] :
    PreservesColimitsOfShape J F where
@[deprecated "No deprecation message was provided." (since := "2024-11-19")]
lemma preservesColimitOfShapeOfCreatesColimitsOfShapeAndHasColimitsOfShape
    (F : C ⥤ D) [CreatesColimitsOfShape J F] [HasColimitsOfShape J D] :
    PreservesColimitsOfShape J F :=
  preservesColimitOfShape_of_createsColimitsOfShape_and_hasColimitsOfShape _
instance (priority := 100) preservesColimits_of_createsColimits_and_hasColimits (F : C ⥤ D)
    [CreatesColimitsOfSize.{w, w'} F] [HasColimitsOfSize.{w, w'} D] :
    PreservesColimitsOfSize.{w, w'} F where
@[deprecated "No deprecation message was provided." (since := "2024-11-19")]
lemma preservesColimitsOfCreatesColimitsAndHasColimits (F : C ⥤ D)
    [CreatesColimitsOfSize.{w, w'} F] [HasColimitsOfSize.{w, w'} D] :
    PreservesColimitsOfSize.{w, w'} F :=
  preservesColimits_of_createsColimits_and_hasColimits _
def createsLimitOfIsoDiagram {K₁ K₂ : J ⥤ C} (F : C ⥤ D) (h : K₁ ≅ K₂) [CreatesLimit K₁ F] :
    CreatesLimit K₂ F :=
  { reflectsLimit_of_iso_diagram F h with
    lifts := fun c t =>
      let t' := (IsLimit.postcomposeInvEquiv (isoWhiskerRight h F : _) c).symm t
      { liftedCone := (Cones.postcompose h.hom).obj (liftLimit t')
        validLift :=
          Functor.mapConePostcompose F ≪≫
            (Cones.postcompose (isoWhiskerRight h F).hom).mapIso (liftedLimitMapsToOriginal t') ≪≫
              Cones.ext (Iso.refl _) fun j => by
                dsimp
                rw [Category.assoc, ← F.map_comp]
                simp } }
def createsLimitOfNatIso {F G : C ⥤ D} (h : F ≅ G) [CreatesLimit K F] : CreatesLimit K G where
  lifts c t :=
    { liftedCone := liftLimit ((IsLimit.postcomposeInvEquiv (isoWhiskerLeft K h : _) c).symm t)
      validLift := by
        refine (IsLimit.mapConeEquiv h ?_).uniqueUpToIso t
        apply IsLimit.ofIsoLimit _ (liftedLimitMapsToOriginal _).symm
        apply (IsLimit.postcomposeInvEquiv _ _).symm t }
  toReflectsLimit := reflectsLimit_of_natIso _ h
def createsLimitsOfShapeOfNatIso {F G : C ⥤ D} (h : F ≅ G) [CreatesLimitsOfShape J F] :
    CreatesLimitsOfShape J G where CreatesLimit := createsLimitOfNatIso h
def createsLimitsOfNatIso {F G : C ⥤ D} (h : F ≅ G) [CreatesLimitsOfSize.{w, w'} F] :
    CreatesLimitsOfSize.{w, w'} G where
  CreatesLimitsOfShape := createsLimitsOfShapeOfNatIso h
def createsColimitOfIsoDiagram {K₁ K₂ : J ⥤ C} (F : C ⥤ D) (h : K₁ ≅ K₂) [CreatesColimit K₁ F] :
    CreatesColimit K₂ F :=
  { reflectsColimit_of_iso_diagram F h with
    lifts := fun c t =>
      let t' := (IsColimit.precomposeHomEquiv (isoWhiskerRight h F : _) c).symm t
      { liftedCocone := (Cocones.precompose h.inv).obj (liftColimit t')
        validLift :=
          Functor.mapCoconePrecompose F ≪≫
            (Cocones.precompose (isoWhiskerRight h F).inv).mapIso
                (liftedColimitMapsToOriginal t') ≪≫
              Cocones.ext (Iso.refl _) fun j => by
                dsimp
                rw [← F.map_comp_assoc]
                simp } }
def createsColimitOfNatIso {F G : C ⥤ D} (h : F ≅ G) [CreatesColimit K F] : CreatesColimit K G where
  lifts c t :=
    { liftedCocone := liftColimit ((IsColimit.precomposeHomEquiv (isoWhiskerLeft K h : _) c).symm t)
      validLift := by
        refine (IsColimit.mapCoconeEquiv h ?_).uniqueUpToIso t
        apply IsColimit.ofIsoColimit _ (liftedColimitMapsToOriginal _).symm
        apply (IsColimit.precomposeHomEquiv _ _).symm t }
  toReflectsColimit := reflectsColimit_of_natIso _ h
def createsColimitsOfShapeOfNatIso {F G : C ⥤ D} (h : F ≅ G) [CreatesColimitsOfShape J F] :
    CreatesColimitsOfShape J G where CreatesColimit := createsColimitOfNatIso h
def createsColimitsOfNatIso {F G : C ⥤ D} (h : F ≅ G) [CreatesColimitsOfSize.{w, w'} F] :
    CreatesColimitsOfSize.{w, w'} G where
  CreatesColimitsOfShape := createsColimitsOfShapeOfNatIso h
def liftsToLimitOfCreates (K : J ⥤ C) (F : C ⥤ D) [CreatesLimit K F] (c : Cone (K ⋙ F))
    (t : IsLimit c) : LiftsToLimit K F c t where
  liftedCone := liftLimit t
  validLift := liftedLimitMapsToOriginal t
  makesLimit := liftedLimitIsLimit t
def liftsToColimitOfCreates (K : J ⥤ C) (F : C ⥤ D) [CreatesColimit K F] (c : Cocone (K ⋙ F))
    (t : IsColimit c) : LiftsToColimit K F c t where
  liftedCocone := liftColimit t
  validLift := liftedColimitMapsToOriginal t
  makesColimit := liftedColimitIsColimit t
def idLiftsCone (c : Cone (K ⋙ 𝟭 C)) : LiftableCone K (𝟭 C) c where
  liftedCone :=
    { pt := c.pt
      π := c.π ≫ K.rightUnitor.hom }
  validLift := Cones.ext (Iso.refl _)
instance idCreatesLimits : CreatesLimitsOfSize.{w, w'} (𝟭 C) where
  CreatesLimitsOfShape :=
    { CreatesLimit := { lifts := fun c _ => idLiftsCone c } }
def idLiftsCocone (c : Cocone (K ⋙ 𝟭 C)) : LiftableCocone K (𝟭 C) c where
  liftedCocone :=
    { pt := c.pt
      ι := K.rightUnitor.inv ≫ c.ι }
  validLift := Cocones.ext (Iso.refl _)
instance idCreatesColimits : CreatesColimitsOfSize.{w, w'} (𝟭 C) where
  CreatesColimitsOfShape :=
    { CreatesColimit := { lifts := fun c _ => idLiftsCocone c } }
instance inhabitedLiftableCone (c : Cone (K ⋙ 𝟭 C)) : Inhabited (LiftableCone K (𝟭 C) c) :=
  ⟨idLiftsCone c⟩
instance inhabitedLiftableCocone (c : Cocone (K ⋙ 𝟭 C)) : Inhabited (LiftableCocone K (𝟭 C) c) :=
  ⟨idLiftsCocone c⟩
instance inhabitedLiftsToLimit (K : J ⥤ C) (F : C ⥤ D) [CreatesLimit K F] (c : Cone (K ⋙ F))
    (t : IsLimit c) : Inhabited (LiftsToLimit _ _ _ t) :=
  ⟨liftsToLimitOfCreates K F c t⟩
instance inhabitedLiftsToColimit (K : J ⥤ C) (F : C ⥤ D) [CreatesColimit K F] (c : Cocone (K ⋙ F))
    (t : IsColimit c) : Inhabited (LiftsToColimit _ _ _ t) :=
  ⟨liftsToColimitOfCreates K F c t⟩
section Comp
variable {E : Type u₃} [ℰ : Category.{v₃} E]
variable (F : C ⥤ D) (G : D ⥤ E)
instance compCreatesLimit [CreatesLimit K F] [CreatesLimit (K ⋙ F) G] :
    CreatesLimit K (F ⋙ G) where
  lifts c t := by
    let c' : Cone ((K ⋙ F) ⋙ G) := c
    let t' : IsLimit c' := t
    exact
      { liftedCone := liftLimit (liftedLimitIsLimit t')
        validLift := (Cones.functoriality (K ⋙ F) G).mapIso
            (liftedLimitMapsToOriginal (liftedLimitIsLimit t')) ≪≫
          liftedLimitMapsToOriginal t' }
instance compCreatesLimitsOfShape [CreatesLimitsOfShape J F] [CreatesLimitsOfShape J G] :
    CreatesLimitsOfShape J (F ⋙ G) where CreatesLimit := inferInstance
instance compCreatesLimits [CreatesLimitsOfSize.{w, w'} F] [CreatesLimitsOfSize.{w, w'} G] :
    CreatesLimitsOfSize.{w, w'} (F ⋙ G) where CreatesLimitsOfShape := inferInstance
instance compCreatesColimit [CreatesColimit K F] [CreatesColimit (K ⋙ F) G] :
    CreatesColimit K (F ⋙ G) where
  lifts c t :=
    let c' : Cocone ((K ⋙ F) ⋙ G) := c
    let t' : IsColimit c' := t
    { liftedCocone := liftColimit (liftedColimitIsColimit t')
      validLift :=
        (Cocones.functoriality (K ⋙ F) G).mapIso
            (liftedColimitMapsToOriginal (liftedColimitIsColimit t')) ≪≫
          liftedColimitMapsToOriginal t' }
instance compCreatesColimitsOfShape [CreatesColimitsOfShape J F] [CreatesColimitsOfShape J G] :
    CreatesColimitsOfShape J (F ⋙ G) where CreatesColimit := inferInstance
instance compCreatesColimits [CreatesColimitsOfSize.{w, w'} F] [CreatesColimitsOfSize.{w, w'} G] :
    CreatesColimitsOfSize.{w, w'} (F ⋙ G) where CreatesColimitsOfShape := inferInstance
end Comp
end Creates
end CategoryTheory