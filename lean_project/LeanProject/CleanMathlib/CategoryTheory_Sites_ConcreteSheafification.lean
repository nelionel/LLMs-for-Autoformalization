import Mathlib.CategoryTheory.Sites.Plus
import Mathlib.CategoryTheory.Limits.Shapes.ConcreteCategory
namespace CategoryTheory
open CategoryTheory.Limits Opposite
universe w v u
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {D : Type w} [Category.{max v u} D]
section
variable [ConcreteCategory.{max v u} D]
attribute [local instance] ConcreteCategory.hasCoeToSort ConcreteCategory.instFunLike
def Meq {X : C} (P : Cᵒᵖ ⥤ D) (S : J.Cover X) :=
  { x : ∀ I : S.Arrow, P.obj (op I.Y) //
    ∀ I : S.Relation, P.map I.r.g₁.op (x I.fst) = P.map I.r.g₂.op (x I.snd) }
end
namespace Meq
variable [ConcreteCategory.{max v u} D]
attribute [local instance] ConcreteCategory.hasCoeToSort ConcreteCategory.instFunLike
instance {X} (P : Cᵒᵖ ⥤ D) (S : J.Cover X) :
    CoeFun (Meq P S) fun _ => ∀ I : S.Arrow, P.obj (op I.Y) :=
  ⟨fun x => x.1⟩
lemma congr_apply {X} {P : Cᵒᵖ ⥤ D} {S : J.Cover X} (x : Meq P S) {Y}
    {f g : Y ⟶ X} (h : f = g) (hf : S f) :
    x ⟨_, _, hf⟩ = x ⟨_, g, by simpa only [← h] using hf⟩ := by
  subst h
  rfl
@[ext]
theorem ext {X} {P : Cᵒᵖ ⥤ D} {S : J.Cover X} (x y : Meq P S) (h : ∀ I : S.Arrow, x I = y I) :
    x = y :=
  Subtype.ext <| funext <| h
theorem condition {X} {P : Cᵒᵖ ⥤ D} {S : J.Cover X} (x : Meq P S) (I : S.Relation) :
    P.map I.r.g₁.op (x ((S.index P).fstTo I)) = P.map I.r.g₂.op (x ((S.index P).sndTo I)) :=
  x.2 _
def refine {X : C} {P : Cᵒᵖ ⥤ D} {S T : J.Cover X} (x : Meq P T) (e : S ⟶ T) : Meq P S :=
  ⟨fun I => x ⟨I.Y, I.f, (leOfHom e) _ I.hf⟩, fun I =>
    x.condition (GrothendieckTopology.Cover.Relation.mk' (I.r.map e))⟩
@[simp]
theorem refine_apply {X : C} {P : Cᵒᵖ ⥤ D} {S T : J.Cover X} (x : Meq P T) (e : S ⟶ T)
    (I : S.Arrow) : x.refine e I = x ⟨I.Y, I.f, (leOfHom e) _ I.hf⟩ :=
  rfl
def pullback {Y X : C} {P : Cᵒᵖ ⥤ D} {S : J.Cover X} (x : Meq P S) (f : Y ⟶ X) :
    Meq P ((J.pullback f).obj S) :=
  ⟨fun I => x ⟨_, I.f ≫ f, I.hf⟩, fun I =>
    x.condition (GrothendieckTopology.Cover.Relation.mk' I.r.base)⟩
@[simp]
theorem pullback_apply {Y X : C} {P : Cᵒᵖ ⥤ D} {S : J.Cover X} (x : Meq P S) (f : Y ⟶ X)
    (I : ((J.pullback f).obj S).Arrow) : x.pullback f I = x ⟨_, I.f ≫ f, I.hf⟩ :=
  rfl
@[simp]
theorem pullback_refine {Y X : C} {P : Cᵒᵖ ⥤ D} {S T : J.Cover X} (h : S ⟶ T) (f : Y ⟶ X)
    (x : Meq P T) : (x.pullback f).refine ((J.pullback f).map h) = (refine x h).pullback _ :=
  rfl
def mk {X : C} {P : Cᵒᵖ ⥤ D} (S : J.Cover X) (x : P.obj (op X)) : Meq P S :=
  ⟨fun I => P.map I.f.op x, fun I => by
    dsimp
    simp only [← comp_apply, ← P.map_comp, ← op_comp, I.r.w]⟩
theorem mk_apply {X : C} {P : Cᵒᵖ ⥤ D} (S : J.Cover X) (x : P.obj (op X)) (I : S.Arrow) :
    mk S x I = P.map I.f.op x :=
  rfl
variable [PreservesLimits (forget D)]
noncomputable def equiv {X : C} (P : Cᵒᵖ ⥤ D) (S : J.Cover X) [HasMultiequalizer (S.index P)] :
    (multiequalizer (S.index P) : D) ≃ Meq P S :=
  Limits.Concrete.multiequalizerEquiv _
@[simp]
theorem equiv_apply {X : C} {P : Cᵒᵖ ⥤ D} {S : J.Cover X} [HasMultiequalizer (S.index P)]
    (x : (multiequalizer (S.index P) : D)) (I : S.Arrow) :
    equiv P S x I = Multiequalizer.ι (S.index P) I x :=
  rfl
theorem equiv_symm_eq_apply {X : C} {P : Cᵒᵖ ⥤ D} {S : J.Cover X} [HasMultiequalizer (S.index P)]
    (x : Meq P S) (I : S.Arrow) :
    Multiequalizer.ι (S.index P) I ((Meq.equiv P S).symm x) = x I := by
  rw [← equiv_apply]
  simp
end Meq
namespace GrothendieckTopology
namespace Plus
variable [ConcreteCategory.{max v u} D]
attribute [local instance] ConcreteCategory.hasCoeToSort ConcreteCategory.instFunLike
variable [PreservesLimits (forget D)]
variable [∀ X : C, HasColimitsOfShape (J.Cover X)ᵒᵖ D]
variable [∀ (P : Cᵒᵖ ⥤ D) (X : C) (S : J.Cover X), HasMultiequalizer (S.index P)]
noncomputable section
def mk {X : C} {P : Cᵒᵖ ⥤ D} {S : J.Cover X} (x : Meq P S) : (J.plusObj P).obj (op X) :=
  colimit.ι (J.diagram P X) (op S) ((Meq.equiv P S).symm x)
theorem res_mk_eq_mk_pullback {Y X : C} {P : Cᵒᵖ ⥤ D} {S : J.Cover X} (x : Meq P S) (f : Y ⟶ X) :
    (J.plusObj P).map f.op (mk x) = mk (x.pullback f) := by
  dsimp [mk, plusObj]
  rw [← comp_apply (x := (Meq.equiv P S).symm x), ι_colimMap_assoc, colimit.ι_pre,
    comp_apply (x := (Meq.equiv P S).symm x)]
  apply congr_arg
  apply (Meq.equiv P _).injective
  erw [Equiv.apply_symm_apply]
  ext i
  simp only [Functor.op_obj, unop_op, pullback_obj, diagram_obj, Functor.comp_obj,
    diagramPullback_app, Meq.equiv_apply, Meq.pullback_apply]
  rw [← comp_apply, Multiequalizer.lift_ι]
  erw [Meq.equiv_symm_eq_apply]
  cases i; rfl
theorem toPlus_mk {X : C} {P : Cᵒᵖ ⥤ D} (S : J.Cover X) (x : P.obj (op X)) :
    (J.toPlus P).app _ x = mk (Meq.mk S x) := by
  dsimp [mk, toPlus]
  let e : S ⟶ ⊤ := homOfLE (OrderTop.le_top _)
  rw [← colimit.w _ e.op]
  delta Cover.toMultiequalizer
  rw [comp_apply]
  erw [comp_apply]
  apply congr_arg
  dsimp [diagram]
  apply Concrete.multiequalizer_ext
  intro i
  simp only [← comp_apply, Category.assoc, Multiequalizer.lift_ι, Category.comp_id,
    Meq.equiv_symm_eq_apply]
  rfl
theorem toPlus_apply {X : C} {P : Cᵒᵖ ⥤ D} (S : J.Cover X) (x : Meq P S) (I : S.Arrow) :
    (J.toPlus P).app _ (x I) = (J.plusObj P).map I.f.op (mk x) := by
  dsimp only [toPlus, plusObj]
  delta Cover.toMultiequalizer
  dsimp [mk]
  erw [← comp_apply]
  rw [ι_colimMap_assoc, colimit.ι_pre, comp_apply, comp_apply]
  dsimp only [Functor.op]
  let e : (J.pullback I.f).obj (unop (op S)) ⟶ ⊤ := homOfLE (OrderTop.le_top _)
  rw [← colimit.w _ e.op]
  erw [comp_apply]
  apply congr_arg
  apply Concrete.multiequalizer_ext
  intro i
  dsimp
  erw [← comp_apply, ← comp_apply, ← comp_apply]
  rw [Multiequalizer.lift_ι, Multiequalizer.lift_ι, Multiequalizer.lift_ι]
  erw [Meq.equiv_symm_eq_apply]
  simpa using (x.condition (Cover.Relation.mk' (I.precompRelation i.f))).symm
theorem toPlus_eq_mk {X : C} {P : Cᵒᵖ ⥤ D} (x : P.obj (op X)) :
    (J.toPlus P).app _ x = mk (Meq.mk ⊤ x) := by
  dsimp [mk, toPlus]
  delta Cover.toMultiequalizer
  simp only [comp_apply]
  apply congr_arg
  apply (Meq.equiv P ⊤).injective
  ext i
  rw [Meq.equiv_apply, Equiv.apply_symm_apply, ← comp_apply, Multiequalizer.lift_ι]
  rfl
variable [∀ X : C, PreservesColimitsOfShape (J.Cover X)ᵒᵖ (forget D)]
theorem exists_rep {X : C} {P : Cᵒᵖ ⥤ D} (x : (J.plusObj P).obj (op X)) :
    ∃ (S : J.Cover X) (y : Meq P S), x = mk y := by
  obtain ⟨S, y, h⟩ := Concrete.colimit_exists_rep (J.diagram P X) x
  use S.unop, Meq.equiv _ _ y
  rw [← h]
  dsimp [mk]
  simp
theorem eq_mk_iff_exists {X : C} {P : Cᵒᵖ ⥤ D} {S T : J.Cover X} (x : Meq P S) (y : Meq P T) :
    mk x = mk y ↔ ∃ (W : J.Cover X) (h1 : W ⟶ S) (h2 : W ⟶ T), x.refine h1 = y.refine h2 := by
  constructor
  · intro h
    obtain ⟨W, h1, h2, hh⟩ := Concrete.colimit_exists_of_rep_eq.{u} _ _ _ h
    use W.unop, h1.unop, h2.unop
    ext I
    apply_fun Multiequalizer.ι (W.unop.index P) I at hh
    convert hh
    all_goals
      dsimp [diagram]
      erw [← comp_apply, Multiequalizer.lift_ι, Meq.equiv_symm_eq_apply]
      cases I; rfl
  · rintro ⟨S, h1, h2, e⟩
    apply Concrete.colimit_rep_eq_of_exists
    use op S, h1.op, h2.op
    apply Concrete.multiequalizer_ext
    intro i
    apply_fun fun ee => ee i at e
    convert e
    all_goals
      dsimp
      erw [← comp_apply, Multiequalizer.lift_ι]
      erw [Meq.equiv_symm_eq_apply]
      cases i; rfl
theorem sep {X : C} (P : Cᵒᵖ ⥤ D) (S : J.Cover X) (x y : (J.plusObj P).obj (op X))
    (h : ∀ I : S.Arrow, (J.plusObj P).map I.f.op x = (J.plusObj P).map I.f.op y) : x = y := by
  obtain ⟨Sx, x, rfl⟩ := exists_rep x
  obtain ⟨Sy, y, rfl⟩ := exists_rep y
  simp only [res_mk_eq_mk_pullback] at h
  choose W h1 h2 hh using fun I : S.Arrow => (eq_mk_iff_exists _ _).mp (h I)
  rw [eq_mk_iff_exists]
  let B : J.Cover X := S.bind W
  use B
  let ex : B ⟶ Sx :=
    homOfLE
      (by
        rintro Y f ⟨Z, e1, e2, he2, he1, hee⟩
        rw [← hee]
        apply leOfHom (h1 ⟨_, _, he2⟩)
        exact he1)
  let ey : B ⟶ Sy :=
    homOfLE
      (by
        rintro Y f ⟨Z, e1, e2, he2, he1, hee⟩
        rw [← hee]
        apply leOfHom (h2 ⟨_, _, he2⟩)
        exact he1)
  use ex, ey
  ext1 I
  let IS : S.Arrow := I.fromMiddle
  specialize hh IS
  let IW : (W IS).Arrow := I.toMiddle
  apply_fun fun e => e IW at hh
  convert hh using 1
  · exact x.congr_apply I.middle_spec.symm _
  · exact y.congr_apply I.middle_spec.symm _
theorem inj_of_sep (P : Cᵒᵖ ⥤ D)
    (hsep :
      ∀ (X : C) (S : J.Cover X) (x y : P.obj (op X)),
        (∀ I : S.Arrow, P.map I.f.op x = P.map I.f.op y) → x = y)
    (X : C) : Function.Injective ((J.toPlus P).app (op X)) := by
  intro x y h
  simp only [toPlus_eq_mk] at h
  rw [eq_mk_iff_exists] at h
  obtain ⟨W, h1, h2, hh⟩ := h
  apply hsep X W
  intro I
  apply_fun fun e => e I at hh
  exact hh
def meqOfSep (P : Cᵒᵖ ⥤ D)
    (hsep :
      ∀ (X : C) (S : J.Cover X) (x y : P.obj (op X)),
        (∀ I : S.Arrow, P.map I.f.op x = P.map I.f.op y) → x = y)
    (X : C) (S : J.Cover X) (s : Meq (J.plusObj P) S) (T : ∀ I : S.Arrow, J.Cover I.Y)
    (t : ∀ I : S.Arrow, Meq P (T I)) (ht : ∀ I : S.Arrow, s I = mk (t I)) : Meq P (S.bind T) where
  val I := t I.fromMiddle I.toMiddle
  property := by
    intro II
    apply inj_of_sep P hsep
    rw [← comp_apply, ← comp_apply, (J.toPlus P).naturality, (J.toPlus P).naturality, comp_apply,
      comp_apply]
    erw [toPlus_apply (T II.fst.fromMiddle) (t II.fst.fromMiddle) II.fst.toMiddle,
      toPlus_apply (T II.snd.fromMiddle) (t II.snd.fromMiddle) II.snd.toMiddle, ← ht, ← ht, ←
      comp_apply, ← comp_apply, ← (J.plusObj P).map_comp, ← (J.plusObj P).map_comp]
    rw [← op_comp, ← op_comp]
    exact s.condition
      (Cover.Relation.mk { hf := II.fst.from_middle_condition }
        { hf := II.snd.from_middle_condition }
        { g₁ := II.r.g₁ ≫ II.fst.toMiddleHom
          g₂ := II.r.g₂ ≫ II.snd.toMiddleHom
          w := by simpa only [Category.assoc, Cover.Arrow.middle_spec] using II.r.w })
theorem exists_of_sep (P : Cᵒᵖ ⥤ D)
    (hsep :
      ∀ (X : C) (S : J.Cover X) (x y : P.obj (op X)),
        (∀ I : S.Arrow, P.map I.f.op x = P.map I.f.op y) → x = y)
    (X : C) (S : J.Cover X) (s : Meq (J.plusObj P) S) :
    ∃ t : (J.plusObj P).obj (op X), Meq.mk S t = s := by
  have inj : ∀ X : C, Function.Injective ((J.toPlus P).app (op X)) := inj_of_sep _ hsep
  choose T t ht using fun I => exists_rep (s I)
  let B : J.Cover X := S.bind T
  choose Z e1 e2 he2 _ _ using fun I : B.Arrow => I.hf
  let w : Meq P B := meqOfSep P hsep X S s T t ht
  use mk w
  ext I
  dsimp [Meq.mk]
  rw [ht, res_mk_eq_mk_pullback]
  apply sep P (T I)
  intro II
  simp only [res_mk_eq_mk_pullback, eq_mk_iff_exists]
  use (J.pullback II.f).obj (T I)
  let e0 : (J.pullback II.f).obj (T I) ⟶ (J.pullback II.f).obj ((J.pullback I.f).obj B) :=
    homOfLE
      (by
        intro Y f hf
        apply Sieve.le_pullback_bind _ _ _ I.hf
        · cases I
          exact hf)
  use e0, 𝟙 _
  ext IV
  let IA : B.Arrow := ⟨_, (IV.f ≫ II.f) ≫ I.f,
    ⟨I.Y, _, _, I.hf, Sieve.downward_closed _ II.hf _, rfl⟩⟩
  let IB : S.Arrow := IA.fromMiddle
  let IC : (T IB).Arrow := IA.toMiddle
  let ID : (T I).Arrow := ⟨IV.Y, IV.f ≫ II.f, Sieve.downward_closed (T I).1 II.hf IV.f⟩
  change t IB IC = t I ID
  apply inj IV.Y
  erw [toPlus_apply (T I) (t I) ID, toPlus_apply (T IB) (t IB) IC, ← ht, ← ht]
  let IR : S.Relation := Cover.Relation.mk { hf := IB.hf } { hf := I.hf } { w := IA.middle_spec }
  exact s.condition IR
variable [(forget D).ReflectsIsomorphisms]
theorem isSheaf_of_sep (P : Cᵒᵖ ⥤ D)
    (hsep :
      ∀ (X : C) (S : J.Cover X) (x y : P.obj (op X)),
        (∀ I : S.Arrow, P.map I.f.op x = P.map I.f.op y) → x = y) :
    Presheaf.IsSheaf J (J.plusObj P) := by
  rw [Presheaf.isSheaf_iff_multiequalizer]
  intro X S
  apply @isIso_of_reflects_iso _ _ _ _ _ _ _ (forget D) ?_
  rw [isIso_iff_bijective]
  constructor
  · intro x y h
    apply sep P S _ _
    intro I
    apply_fun Meq.equiv _ _ at h
    apply_fun fun e => e I at h
    convert h <;> erw [Meq.equiv_apply, ← comp_apply, Multiequalizer.lift_ι] <;> rfl
  · rintro (x : (multiequalizer (S.index _) : D))
    obtain ⟨t, ht⟩ := exists_of_sep P hsep X S (Meq.equiv _ _ x)
    use t
    apply (Meq.equiv _ _).injective
    rw [← ht]
    ext i
    dsimp
    erw [← comp_apply]
    rw [Multiequalizer.lift_ι]
    rfl
variable (J)
theorem isSheaf_plus_plus (P : Cᵒᵖ ⥤ D) : Presheaf.IsSheaf J (J.plusObj (J.plusObj P)) := by
  apply isSheaf_of_sep
  intro X S x y
  apply sep
end
end Plus
variable (J)
variable [∀ (P : Cᵒᵖ ⥤ D) (X : C) (S : J.Cover X), HasMultiequalizer (S.index P)]
  [∀ X : C, HasColimitsOfShape (J.Cover X)ᵒᵖ D]
noncomputable def sheafify (P : Cᵒᵖ ⥤ D) : Cᵒᵖ ⥤ D :=
  J.plusObj (J.plusObj P)
noncomputable def toSheafify (P : Cᵒᵖ ⥤ D) : P ⟶ J.sheafify P :=
  J.toPlus P ≫ J.plusMap (J.toPlus P)
noncomputable def sheafifyMap {P Q : Cᵒᵖ ⥤ D} (η : P ⟶ Q) : J.sheafify P ⟶ J.sheafify Q :=
  J.plusMap <| J.plusMap η
@[simp]
theorem sheafifyMap_id (P : Cᵒᵖ ⥤ D) : J.sheafifyMap (𝟙 P) = 𝟙 (J.sheafify P) := by
  dsimp [sheafifyMap, sheafify]
  simp
@[simp]
theorem sheafifyMap_comp {P Q R : Cᵒᵖ ⥤ D} (η : P ⟶ Q) (γ : Q ⟶ R) :
    J.sheafifyMap (η ≫ γ) = J.sheafifyMap η ≫ J.sheafifyMap γ := by
  dsimp [sheafifyMap, sheafify]
  simp
@[reassoc (attr := simp)]
theorem toSheafify_naturality {P Q : Cᵒᵖ ⥤ D} (η : P ⟶ Q) :
    η ≫ J.toSheafify _ = J.toSheafify _ ≫ J.sheafifyMap η := by
  dsimp [sheafifyMap, sheafify, toSheafify]
  simp
variable (D)
noncomputable def sheafification : (Cᵒᵖ ⥤ D) ⥤ Cᵒᵖ ⥤ D :=
  J.plusFunctor D ⋙ J.plusFunctor D
@[simp]
theorem sheafification_obj (P : Cᵒᵖ ⥤ D) : (J.sheafification D).obj P = J.sheafify P :=
  rfl
@[simp]
theorem sheafification_map {P Q : Cᵒᵖ ⥤ D} (η : P ⟶ Q) :
    (J.sheafification D).map η = J.sheafifyMap η :=
  rfl
noncomputable def toSheafification : 𝟭 _ ⟶ sheafification J D :=
  J.toPlusNatTrans D ≫ whiskerRight (J.toPlusNatTrans D) (J.plusFunctor D)
@[simp]
theorem toSheafification_app (P : Cᵒᵖ ⥤ D) :
    (J.toSheafification D).app P = J.toSheafify P :=
  rfl
variable {D}
theorem isIso_toSheafify {P : Cᵒᵖ ⥤ D} (hP : Presheaf.IsSheaf J P) : IsIso (J.toSheafify P) := by
  dsimp [toSheafify]
  haveI := isIso_toPlus_of_isSheaf J P hP
  change (IsIso (toPlus J P ≫ (J.plusFunctor D).map (toPlus J P)))
  infer_instance
noncomputable def isoSheafify {P : Cᵒᵖ ⥤ D} (hP : Presheaf.IsSheaf J P) : P ≅ J.sheafify P :=
  letI := isIso_toSheafify J hP
  asIso (J.toSheafify P)
@[simp]
theorem isoSheafify_hom {P : Cᵒᵖ ⥤ D} (hP : Presheaf.IsSheaf J P) :
    (J.isoSheafify hP).hom = J.toSheafify P :=
  rfl
noncomputable def sheafifyLift {P Q : Cᵒᵖ ⥤ D} (η : P ⟶ Q) (hQ : Presheaf.IsSheaf J Q) :
    J.sheafify P ⟶ Q :=
  J.plusLift (J.plusLift η hQ) hQ
@[reassoc (attr := simp)]
theorem toSheafify_sheafifyLift {P Q : Cᵒᵖ ⥤ D} (η : P ⟶ Q) (hQ : Presheaf.IsSheaf J Q) :
    J.toSheafify P ≫ sheafifyLift J η hQ = η := by
  dsimp only [sheafifyLift, toSheafify]
  simp
theorem sheafifyLift_unique {P Q : Cᵒᵖ ⥤ D} (η : P ⟶ Q) (hQ : Presheaf.IsSheaf J Q)
    (γ : J.sheafify P ⟶ Q) : J.toSheafify P ≫ γ = η → γ = sheafifyLift J η hQ := by
  intro h
  apply plusLift_unique
  apply plusLift_unique
  rw [← Category.assoc, ← plusMap_toPlus]
  exact h
@[simp]
theorem isoSheafify_inv {P : Cᵒᵖ ⥤ D} (hP : Presheaf.IsSheaf J P) :
    (J.isoSheafify hP).inv = J.sheafifyLift (𝟙 _) hP := by
  apply J.sheafifyLift_unique
  simp [Iso.comp_inv_eq]
theorem sheafify_hom_ext {P Q : Cᵒᵖ ⥤ D} (η γ : J.sheafify P ⟶ Q) (hQ : Presheaf.IsSheaf J Q)
    (h : J.toSheafify P ≫ η = J.toSheafify P ≫ γ) : η = γ := by
  apply J.plus_hom_ext _ _ hQ
  apply J.plus_hom_ext _ _ hQ
  rw [← Category.assoc, ← Category.assoc, ← plusMap_toPlus]
  exact h
@[reassoc (attr := simp)]
theorem sheafifyMap_sheafifyLift {P Q R : Cᵒᵖ ⥤ D} (η : P ⟶ Q) (γ : Q ⟶ R)
    (hR : Presheaf.IsSheaf J R) :
    J.sheafifyMap η ≫ J.sheafifyLift γ hR = J.sheafifyLift (η ≫ γ) hR := by
  apply J.sheafifyLift_unique
  rw [← Category.assoc, ← J.toSheafify_naturality, Category.assoc, toSheafify_sheafifyLift]
end GrothendieckTopology
variable (J)
variable [ConcreteCategory.{max v u} D] [PreservesLimits (forget D)]
  [∀ (P : Cᵒᵖ ⥤ D) (X : C) (S : J.Cover X), HasMultiequalizer (S.index P)]
  [∀ X : C, HasColimitsOfShape (J.Cover X)ᵒᵖ D]
  [∀ X : C, PreservesColimitsOfShape (J.Cover X)ᵒᵖ (forget D)] [(forget D).ReflectsIsomorphisms]
theorem GrothendieckTopology.sheafify_isSheaf (P : Cᵒᵖ ⥤ D) : Presheaf.IsSheaf J (J.sheafify P) :=
  GrothendieckTopology.Plus.isSheaf_plus_plus _ _
variable (D)
@[simps]
noncomputable def plusPlusSheaf : (Cᵒᵖ ⥤ D) ⥤ Sheaf J D where
  obj P := ⟨J.sheafify P, J.sheafify_isSheaf P⟩
  map η := ⟨J.sheafifyMap η⟩
  map_id _ := Sheaf.Hom.ext <| J.sheafifyMap_id _
  map_comp _ _ := Sheaf.Hom.ext <| J.sheafifyMap_comp _ _
instance plusPlusSheaf_preservesZeroMorphisms [Preadditive D] :
    (plusPlusSheaf J D).PreservesZeroMorphisms where
  map_zero F G := by
    ext : 3
    refine colimit.hom_ext (fun j => ?_)
    erw [colimit.ι_map, comp_zero, J.plusMap_zero, J.diagramNatTrans_zero, zero_comp]
@[simps! unit_app counit_app_val]
noncomputable def plusPlusAdjunction : plusPlusSheaf J D ⊣ sheafToPresheaf J D :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun P Q =>
        { toFun := fun e => J.toSheafify P ≫ e.val
          invFun := fun e => ⟨J.sheafifyLift e Q.2⟩
          left_inv := fun _ => Sheaf.Hom.ext <| (J.sheafifyLift_unique _ _ _ rfl).symm
          right_inv := fun _ => J.toSheafify_sheafifyLift _ _ }
      homEquiv_naturality_left_symm := by
        intro P Q R η γ; ext1; dsimp; symm
        apply J.sheafifyMap_sheafifyLift
      homEquiv_naturality_right := fun η γ => by
        dsimp
        rw [Category.assoc] }
instance sheafToPresheaf_isRightAdjoint : (sheafToPresheaf J D).IsRightAdjoint  :=
  (plusPlusAdjunction J D).isRightAdjoint
instance presheaf_mono_of_mono {F G : Sheaf J D} (f : F ⟶ G) [Mono f] : Mono f.1 :=
  (sheafToPresheaf J D).map_mono _
theorem Sheaf.Hom.mono_iff_presheaf_mono {F G : Sheaf J D} (f : F ⟶ G) : Mono f ↔ Mono f.1 :=
  ⟨fun m => by infer_instance, fun m => by exact Sheaf.Hom.mono_of_presheaf_mono J D f⟩
end CategoryTheory