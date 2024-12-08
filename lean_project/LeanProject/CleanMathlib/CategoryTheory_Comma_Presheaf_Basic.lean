import Mathlib.CategoryTheory.HomCongr
import Mathlib.CategoryTheory.Comma.Over
import Mathlib.Tactic.CategoryTheory.Elementwise
namespace CategoryTheory
open Category Opposite
universe w v u
variable {C : Type u} [Category.{v} C] {A : Cᵒᵖ ⥤ Type v}
namespace OverPresheafAux
attribute [local simp] FunctorToTypes.naturality
structure MakesOverArrow {F : Cᵒᵖ ⥤ Type v} (η : F ⟶ A) {X : C} (s : yoneda.obj X ⟶ A)
    (u : F.obj (op X)) : Prop where
  app : η.app (op X) u = yonedaEquiv s
namespace MakesOverArrow
lemma map₁ {F G : Cᵒᵖ ⥤ Type v} {η : F ⟶ A} {μ : G ⟶ A} {ε : F ⟶ G}
    (hε : ε ≫ μ = η) {X : C} {s : yoneda.obj X ⟶ A} {u : F.obj (op X)}
    (h : MakesOverArrow η s u) : MakesOverArrow μ s (ε.app _ u) :=
  ⟨by rw [← elementwise_of% NatTrans.comp_app ε μ, hε, h.app]⟩
lemma map₂ {F : Cᵒᵖ ⥤ Type v} {η : F ⟶ A} {X Y : C} (f : X ⟶ Y)
    {s : yoneda.obj X ⟶ A} {t : yoneda.obj Y ⟶ A} (hst : yoneda.map f ≫ t = s)
    {u : F.obj (op Y)} (h : MakesOverArrow η t u) : MakesOverArrow η s (F.map f.op u) :=
  ⟨by rw [elementwise_of% η.naturality, h.app, yonedaEquiv_naturality, hst]⟩
lemma of_arrow {F : Cᵒᵖ ⥤ Type v} {η : F ⟶ A} {X : C} {s : yoneda.obj X ⟶ A}
    {f : yoneda.obj X ⟶ F} (hf : f ≫ η = s) : MakesOverArrow η s (yonedaEquiv f) :=
  ⟨hf ▸ rfl⟩
lemma of_yoneda_arrow {Y : C} {η : yoneda.obj Y ⟶ A} {X : C} {s : yoneda.obj X ⟶ A} {f : X ⟶ Y}
    (hf : yoneda.map f ≫ η = s) : MakesOverArrow η s f := by
  simpa only [yonedaEquiv_yoneda_map f] using of_arrow hf
end MakesOverArrow
def OverArrows {F : Cᵒᵖ ⥤ Type v} (η : F ⟶ A) {X : C} (s : yoneda.obj X ⟶ A) : Type v :=
  Subtype (MakesOverArrow η s)
namespace OverArrows
def val {F : Cᵒᵖ ⥤ Type v} {η : F ⟶ A} {X : C} {s : yoneda.obj X ⟶ A} :
    OverArrows η s → F.obj (op X) :=
  Subtype.val
@[simp]
lemma val_mk {F : Cᵒᵖ ⥤ Type v} (η : F ⟶ A) {X : C} (s : yoneda.obj X ⟶ A) (u : F.obj (op X))
    (h : MakesOverArrow η s u) : val ⟨u, h⟩ = u :=
  rfl
@[ext]
lemma ext {F : Cᵒᵖ ⥤ Type v} {η : F ⟶ A} {X : C} {s : yoneda.obj X ⟶ A}
    {u v : OverArrows η s} : u.val = v.val → u = v :=
  Subtype.ext
lemma app_val {F : Cᵒᵖ ⥤ Type v} {η : F ⟶ A} {X : C} {s : yoneda.obj X ⟶ A}
    (p : OverArrows η s) : η.app (op X) p.val = yonedaEquiv s :=
  p.prop.app
@[simp]
lemma map_val {Y : C} {η : yoneda.obj Y ⟶ A} {X : C} {s : yoneda.obj X ⟶ A}
    (p : OverArrows η s) : yoneda.map p.val ≫ η = s := by
  rw [← yonedaEquiv.injective.eq_iff, yonedaEquiv_comp, yonedaEquiv_yoneda_map]
  simp only [unop_op, p.app_val]
def map₁ {F G : Cᵒᵖ ⥤ Type v} {η : F ⟶ A} {μ : G ⟶ A} {X : C} {s : yoneda.obj X ⟶ A}
    (u : OverArrows η s) (ε : F ⟶ G) (hε : ε ≫ μ = η) : OverArrows μ s :=
  ⟨ε.app _ u.val, MakesOverArrow.map₁ hε u.2⟩
@[simp]
lemma map₁_val {F G : Cᵒᵖ ⥤ Type v} {η : F ⟶ A} {μ : G ⟶ A} {X : C}
    (s : yoneda.obj X ⟶ A) (u : OverArrows η s) (ε : F ⟶ G) (hε : ε ≫ μ = η) :
    (u.map₁ ε hε).val = ε.app _ u.val :=
  rfl
def map₂ {F : Cᵒᵖ ⥤ Type v} {η : F ⟶ A} {X Y : C} {s : yoneda.obj X ⟶ A}
    {t : yoneda.obj Y ⟶ A} (u : OverArrows η t) (f : X ⟶ Y) (hst : yoneda.map f ≫ t = s) :
    OverArrows η s :=
  ⟨F.map f.op u.val, MakesOverArrow.map₂ f hst u.2⟩
@[simp]
lemma map₂_val {F : Cᵒᵖ ⥤ Type v} {η : F ⟶ A} {X Y : C} (f : X ⟶ Y)
    {s : yoneda.obj X ⟶ A} {t : yoneda.obj Y ⟶ A} (hst : yoneda.map f ≫ t = s)
    (u : OverArrows η t) : (u.map₂ f hst).val = F.map f.op u.val :=
  rfl
@[simp]
lemma map₁_map₂ {F G : Cᵒᵖ ⥤ Type v} {η : F ⟶ A} {μ : G ⟶ A} (ε : F ⟶ G)
    (hε : ε ≫ μ = η) {X Y : C} {s : yoneda.obj X ⟶ A} {t : yoneda.obj Y ⟶ A} (f : X ⟶ Y)
    (hf : yoneda.map f ≫ t = s) (u : OverArrows η t) :
    (u.map₁ ε hε).map₂ f hf = (u.map₂ f hf).map₁ ε hε :=
  OverArrows.ext <| (elementwise_of% (ε.naturality f.op).symm) u.val
def yonedaArrow {Y : C} {η : yoneda.obj Y ⟶ A} {X : C} {s : yoneda.obj X ⟶ A} (f : X ⟶ Y)
    (hf : yoneda.map f ≫ η = s) : OverArrows η s :=
  ⟨f, .of_yoneda_arrow hf⟩
@[simp]
lemma yonedaArrow_val {Y : C} {η : yoneda.obj Y ⟶ A} {X : C} {s : yoneda.obj X ⟶ A} {f : X ⟶ Y}
    (hf : yoneda.map f ≫ η = s) : (yonedaArrow f hf).val = f :=
  rfl
def costructuredArrowIso (s t : CostructuredArrow yoneda A) : OverArrows s.hom t.hom ≅ t ⟶ s where
  hom p := CostructuredArrow.homMk p.val (by aesop_cat)
  inv f := yonedaArrow f.left f.w
end OverArrows
@[simps]
def restrictedYonedaObj {F : Cᵒᵖ ⥤ Type v} (η : F ⟶ A) :
    (CostructuredArrow yoneda A)ᵒᵖ ⥤ Type v where
  obj s := OverArrows η s.unop.hom
  map f u := u.map₂ f.unop.left f.unop.w
@[simps]
def restrictedYonedaObjMap₁ {F G : Cᵒᵖ ⥤ Type v} {η : F ⟶ A} {μ : G ⟶ A} (ε : F ⟶ G)
    (hε : ε ≫ μ = η) : restrictedYonedaObj η ⟶ restrictedYonedaObj μ where
  app _ u := u.map₁ ε hε
@[simps]
def restrictedYoneda (A : Cᵒᵖ ⥤ Type v) : Over A ⥤ (CostructuredArrow yoneda A)ᵒᵖ ⥤ Type v where
  obj η := restrictedYonedaObj η.hom
  map ε := restrictedYonedaObjMap₁ ε.left ε.w
def toOverYonedaCompRestrictedYoneda (A : Cᵒᵖ ⥤ Type v) :
    CostructuredArrow.toOver yoneda A ⋙ restrictedYoneda A ≅ yoneda :=
  NatIso.ofComponents
    (fun s => NatIso.ofComponents (fun _ => OverArrows.costructuredArrowIso _ _) (by aesop_cat))
    (by aesop_cat)
lemma map_mkPrecomp_eqToHom {F : (CostructuredArrow yoneda A)ᵒᵖ ⥤ Type v} {X Y : C} {f : X ⟶ Y}
    {g g' : yoneda.obj Y ⟶ A} (h : g = g') {x : F.obj (op (CostructuredArrow.mk g'))} :
    F.map (CostructuredArrow.mkPrecomp g f).op (F.map (eqToHom (by rw [h])) x) =
      F.map (eqToHom (by rw [h])) (F.map (CostructuredArrow.mkPrecomp g' f).op x) := by
  aesop_cat
attribute [local simp] map_mkPrecomp_eqToHom
def YonedaCollection (F : (CostructuredArrow yoneda A)ᵒᵖ ⥤ Type v) (X : C) : Type v :=
  Σ s : A.obj (op X), F.obj (op (CostructuredArrow.mk (yonedaEquiv.symm s)))
namespace YonedaCollection
variable {F : (CostructuredArrow yoneda A)ᵒᵖ ⥤ Type v} {X : C}
def mk (s : yoneda.obj X ⟶ A) (x : F.obj (op (CostructuredArrow.mk s))) : YonedaCollection F X :=
  ⟨yonedaEquiv s, F.map (eqToHom <| by rw [Equiv.symm_apply_apply]) x⟩
def fst (p : YonedaCollection F X) : yoneda.obj X ⟶ A :=
  yonedaEquiv.symm p.1
def snd (p : YonedaCollection F X) : F.obj (op (CostructuredArrow.mk p.fst)) :=
  p.2
def yonedaEquivFst (p : YonedaCollection F X) : A.obj (op X) :=
  yonedaEquiv p.fst
lemma yonedaEquivFst_eq (p : YonedaCollection F X) : p.yonedaEquivFst = yonedaEquiv p.fst :=
  rfl
@[simp]
lemma mk_fst (s : yoneda.obj X ⟶ A) (x : F.obj (op (CostructuredArrow.mk s))) : (mk s x).fst = s :=
  Equiv.apply_symm_apply _ _
@[simp]
lemma mk_snd (s : yoneda.obj X ⟶ A) (x : F.obj (op (CostructuredArrow.mk s))) :
    (mk s x).snd = F.map (eqToHom <| by rw [YonedaCollection.mk_fst]) x :=
  rfl
@[ext (iff := false)]
lemma ext {p q : YonedaCollection F X} (h : p.fst = q.fst)
    (h' : F.map (eqToHom <| by rw [h]) q.snd = p.snd) : p = q := by
  rcases p with ⟨p, p'⟩
  rcases q with ⟨q, q'⟩
  obtain rfl : p = q := yonedaEquiv.symm.injective h
  exact Sigma.ext rfl (by simpa [snd] using h'.symm)
def map₁ {G : (CostructuredArrow yoneda A)ᵒᵖ ⥤ Type v} (η : F ⟶ G) :
    YonedaCollection F X → YonedaCollection G X :=
  fun p => YonedaCollection.mk p.fst (η.app _ p.snd)
@[simp]
lemma map₁_fst {G : (CostructuredArrow yoneda A)ᵒᵖ ⥤ Type v} (η : F ⟶ G)
    (p : YonedaCollection F X) : (YonedaCollection.map₁ η p).fst = p.fst := by
  simp [map₁]
@[simp]
lemma map₁_yonedaEquivFst {G : (CostructuredArrow yoneda A)ᵒᵖ ⥤ Type v} (η : F ⟶ G)
    (p : YonedaCollection F X) :
    (YonedaCollection.map₁ η p).yonedaEquivFst = p.yonedaEquivFst := by
  simp only [YonedaCollection.yonedaEquivFst_eq, map₁_fst]
@[simp]
lemma map₁_snd {G : (CostructuredArrow yoneda A)ᵒᵖ ⥤ Type v} (η : F ⟶ G)
    (p : YonedaCollection F X) : (YonedaCollection.map₁ η p).snd =
      G.map (eqToHom (by rw [YonedaCollection.map₁_fst])) (η.app _ p.snd) := by
  simp [map₁]
def map₂ (F : (CostructuredArrow yoneda A)ᵒᵖ ⥤ Type v) {Y : C} (f : X ⟶ Y)
    (p : YonedaCollection F Y) : YonedaCollection F X :=
  YonedaCollection.mk (yoneda.map f ≫ p.fst) <| F.map (CostructuredArrow.mkPrecomp p.fst f).op p.snd
@[simp]
lemma map₂_fst {Y : C} (f : X ⟶ Y) (p : YonedaCollection F Y) :
    (YonedaCollection.map₂ F f p).fst = yoneda.map f ≫ p.fst := by
  simp [map₂]
@[simp]
lemma map₂_yonedaEquivFst {Y : C} (f : X ⟶ Y) (p : YonedaCollection F Y) :
    (YonedaCollection.map₂ F f p).yonedaEquivFst = A.map f.op p.yonedaEquivFst := by
  simp only [YonedaCollection.yonedaEquivFst_eq, map₂_fst, yonedaEquiv_naturality]
@[simp]
lemma map₂_snd {Y : C} (f : X ⟶ Y) (p : YonedaCollection F Y) :
    (YonedaCollection.map₂ F f p).snd = F.map ((CostructuredArrow.mkPrecomp p.fst f).op ≫
      eqToHom (by rw [YonedaCollection.map₂_fst f])) p.snd := by
  simp [map₂]
attribute [local simp] CostructuredArrow.mkPrecomp_id CostructuredArrow.mkPrecomp_comp
@[simp]
lemma map₁_id : YonedaCollection.map₁ (𝟙 F) (X := X) = id := by
  aesop_cat
@[simp]
lemma map₁_comp {G H : (CostructuredArrow yoneda A)ᵒᵖ ⥤ Type v} (η : F ⟶ G) (μ : G ⟶ H) :
    YonedaCollection.map₁ (η ≫ μ) (X := X) =
      YonedaCollection.map₁ μ (X := X) ∘ YonedaCollection.map₁ η (X := X) := by
  ext; all_goals simp
@[simp]
lemma map₂_id : YonedaCollection.map₂ F (𝟙 X) = id := by
  ext; all_goals simp
@[simp]
lemma map₂_comp {Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    YonedaCollection.map₂ F (f ≫ g) = YonedaCollection.map₂ F f ∘ YonedaCollection.map₂ F g := by
  ext; all_goals simp
@[simp]
lemma map₁_map₂ {G : (CostructuredArrow yoneda A)ᵒᵖ ⥤ Type v} (η : F ⟶ G) {Y : C} (f : X ⟶ Y)
    (p : YonedaCollection F Y) :
    YonedaCollection.map₂ G f (YonedaCollection.map₁ η p) =
      YonedaCollection.map₁ η (YonedaCollection.map₂ F f p) := by
  ext; all_goals simp
end YonedaCollection
@[simps]
def yonedaCollectionPresheaf (A : Cᵒᵖ ⥤ Type v) (F : (CostructuredArrow yoneda A)ᵒᵖ ⥤ Type v) :
    Cᵒᵖ ⥤ Type v where
  obj X := YonedaCollection F X.unop
  map f := YonedaCollection.map₂ F f.unop
@[simps]
def yonedaCollectionPresheafMap₁ {F G : (CostructuredArrow yoneda A)ᵒᵖ ⥤ Type v} (η : F ⟶ G) :
    yonedaCollectionPresheaf A F ⟶ yonedaCollectionPresheaf A G where
  app _ := YonedaCollection.map₁ η
  naturality := by
    intros
    ext
    simp
@[simps]
def yonedaCollectionFunctor (A : Cᵒᵖ ⥤ Type v) :
    ((CostructuredArrow yoneda A)ᵒᵖ ⥤ Type v) ⥤ Cᵒᵖ ⥤ Type v where
  obj := yonedaCollectionPresheaf A
  map η := yonedaCollectionPresheafMap₁ η
@[simps]
def yonedaCollectionPresheafToA (F : (CostructuredArrow yoneda A)ᵒᵖ ⥤ Type v) :
    yonedaCollectionPresheaf A F ⟶ A where
  app _ := YonedaCollection.yonedaEquivFst
@[simps! obj map]
def costructuredArrowPresheafToOver (A : Cᵒᵖ ⥤ Type v) :
    ((CostructuredArrow yoneda A)ᵒᵖ ⥤ Type v) ⥤ Over A :=
  (yonedaCollectionFunctor A).toOver _ (yonedaCollectionPresheafToA) (by aesop_cat)
section unit
def unitForward {F : Cᵒᵖ ⥤ Type v} (η : F ⟶ A) (X : C) :
    YonedaCollection (restrictedYonedaObj η) X → F.obj (op X) :=
  fun p => p.snd.val
@[simp]
lemma unitForward_naturality₁ {F G : Cᵒᵖ ⥤ Type v} {η : F ⟶ A} {μ : G ⟶ A} (ε : F ⟶ G)
    (hε : ε ≫ μ = η) (X : C) (p : YonedaCollection (restrictedYonedaObj η) X) :
    unitForward μ X (p.map₁ (restrictedYonedaObjMap₁ ε hε)) = ε.app _ (unitForward η X p) := by
  simp [unitForward]
@[simp]
lemma unitForward_naturality₂ {F : Cᵒᵖ ⥤ Type v} (η : F ⟶ A) (X Y : C) (f : X ⟶ Y)
    (p : YonedaCollection (restrictedYonedaObj η) Y) :
    unitForward η X (YonedaCollection.map₂ (restrictedYonedaObj η) f p) =
      F.map f.op (unitForward η Y p) := by
  simp [unitForward]
@[simp]
lemma app_unitForward {F : Cᵒᵖ ⥤ Type v} (η : F ⟶ A) (X : Cᵒᵖ)
    (p : YonedaCollection (restrictedYonedaObj η) X.unop) :
    η.app X (unitForward η X.unop p) = p.yonedaEquivFst := by
  simpa [unitForward] using p.snd.app_val
def unitBackward {F : Cᵒᵖ ⥤ Type v} (η : F ⟶ A) (X : C) :
    F.obj (op X) → YonedaCollection (restrictedYonedaObj η) X :=
  fun x => YonedaCollection.mk (yonedaEquiv.symm (η.app _ x)) ⟨x, ⟨by aesop_cat⟩⟩
lemma unitForward_unitBackward {F : Cᵒᵖ ⥤ Type v} (η : F ⟶ A) (X : C) :
    unitForward η X ∘ unitBackward η X = id :=
  funext fun x => by simp [unitForward, unitBackward]
lemma unitBackward_unitForward {F : Cᵒᵖ ⥤ Type v} (η : F ⟶ A) (X : C) :
    unitBackward η X ∘ unitForward η X = id := by
  refine funext fun p => YonedaCollection.ext ?_ (OverArrows.ext ?_)
  · simpa [unitForward, unitBackward] using congrArg yonedaEquiv.symm p.snd.app_val
  · simp [unitForward, unitBackward]
@[simps]
def unitAuxAuxAux {F : Cᵒᵖ ⥤ Type v} (η : F ⟶ A) (X : C) :
    YonedaCollection (restrictedYonedaObj η) X ≅ F.obj (op X) where
  hom := unitForward η X
  inv := unitBackward η X
  hom_inv_id := unitBackward_unitForward η X
  inv_hom_id := unitForward_unitBackward η X
@[simps!]
def unitAuxAux {F : Cᵒᵖ ⥤ Type v} (η : F ⟶ A) :
    yonedaCollectionPresheaf A (restrictedYonedaObj η) ≅ F :=
  NatIso.ofComponents (fun X => unitAuxAuxAux η X.unop) (by aesop_cat)
@[simps! hom]
def unitAux (η : Over A) : (restrictedYoneda A ⋙ costructuredArrowPresheafToOver A).obj η ≅ η :=
  Over.isoMk (unitAuxAux η.hom) (by aesop_cat)
def unit (A : Cᵒᵖ ⥤ Type v) : 𝟭 (Over A) ≅ restrictedYoneda A ⋙ costructuredArrowPresheafToOver A :=
  Iso.symm <| NatIso.ofComponents unitAux (by aesop_cat)
end unit
section counit
variable {F : (CostructuredArrow yoneda A)ᵒᵖ ⥤ Type v} {X : C}
@[simp]
lemma OverArrows.yonedaCollectionPresheafToA_val_fst (s : yoneda.obj X ⟶ A)
    (p : OverArrows (yonedaCollectionPresheafToA F) s) : p.val.fst = s := by
  simpa [YonedaCollection.yonedaEquivFst_eq] using p.app_val
def counitForward (F : (CostructuredArrow yoneda A)ᵒᵖ ⥤ Type v) (s : CostructuredArrow yoneda A) :
    F.obj (op s) → OverArrows (yonedaCollectionPresheafToA F) s.hom :=
  fun x => ⟨YonedaCollection.mk s.hom x, ⟨by simp [YonedaCollection.yonedaEquivFst_eq]⟩⟩
lemma counitForward_val_fst (s : CostructuredArrow yoneda A) (x : F.obj (op s)) :
    (counitForward F s x).val.fst = s.hom := by
  simp
@[simp]
lemma counitForward_val_snd (s : CostructuredArrow yoneda A) (x : F.obj (op s)) :
    (counitForward F s x).val.snd = F.map (eqToHom (by simp [← CostructuredArrow.eq_mk])) x :=
  YonedaCollection.mk_snd _ _
@[simp]
lemma counitForward_naturality₁ {G : (CostructuredArrow yoneda A)ᵒᵖ ⥤ Type v} (η : F ⟶ G)
    (s : (CostructuredArrow yoneda A)ᵒᵖ) (x : F.obj s) : counitForward G s.unop (η.app s x) =
      OverArrows.map₁ (counitForward F s.unop x) (yonedaCollectionPresheafMap₁ η) (by aesop_cat) :=
  OverArrows.ext <| YonedaCollection.ext (by simp) (by simp)
@[simp]
lemma counitForward_naturality₂ (s t : (CostructuredArrow yoneda A)ᵒᵖ) (f : t ⟶ s) (x : F.obj t) :
    counitForward F s.unop (F.map f x) =
      OverArrows.map₂ (counitForward F t.unop x) f.unop.left (by simp) := by
  refine OverArrows.ext <| YonedaCollection.ext (by simp) ?_
  have : (CostructuredArrow.mkPrecomp t.unop.hom f.unop.left).op =
      f ≫ eqToHom (by simp [← CostructuredArrow.eq_mk]) := by
    apply Quiver.Hom.unop_inj
    aesop_cat
  aesop_cat
def counitBackward (F : (CostructuredArrow yoneda A)ᵒᵖ ⥤ Type v) (s : CostructuredArrow yoneda A) :
    OverArrows (yonedaCollectionPresheafToA F) s.hom → F.obj (op s) :=
  fun p => F.map (eqToHom (by simp [← CostructuredArrow.eq_mk])) p.val.snd
lemma counitForward_counitBackward (F : (CostructuredArrow yoneda A)ᵒᵖ ⥤ Type v)
    (s : CostructuredArrow yoneda A) : counitForward F s ∘ counitBackward F s = id :=
  funext fun p => OverArrows.ext <| YonedaCollection.ext (by simp) (by simp [counitBackward])
lemma counitBackward_counitForward (F : (CostructuredArrow yoneda A)ᵒᵖ ⥤ Type v)
    (s : CostructuredArrow yoneda A) : counitBackward F s ∘ counitForward F s = id :=
  funext fun x => by simp [counitBackward]
@[simps]
def counitAuxAux (F : (CostructuredArrow yoneda A)ᵒᵖ ⥤ Type v) (s : CostructuredArrow yoneda A) :
    F.obj (op s) ≅ OverArrows (yonedaCollectionPresheafToA F) s.hom where
  hom := counitForward F s
  inv := counitBackward F s
  hom_inv_id := counitBackward_counitForward F s
  inv_hom_id := counitForward_counitBackward F s
@[simps! hom]
def counitAux (F : (CostructuredArrow yoneda A)ᵒᵖ ⥤ Type v) :
    F ≅ restrictedYonedaObj (yonedaCollectionPresheafToA F) :=
  NatIso.ofComponents (fun s => counitAuxAux F s.unop) (by aesop_cat)
def counit (A : Cᵒᵖ ⥤ Type v) : (costructuredArrowPresheafToOver A ⋙ restrictedYoneda A) ≅ 𝟭 _ :=
  Iso.symm <| NatIso.ofComponents counitAux (by aesop_cat)
end counit
end OverPresheafAux
open OverPresheafAux
def overEquivPresheafCostructuredArrow (A : Cᵒᵖ ⥤ Type v) :
    Over A ≌ ((CostructuredArrow yoneda A)ᵒᵖ ⥤ Type v) :=
  .mk (restrictedYoneda A) (costructuredArrowPresheafToOver A) (unit A) (counit A)
def CostructuredArrow.toOverCompOverEquivPresheafCostructuredArrow (A : Cᵒᵖ ⥤ Type v) :
    CostructuredArrow.toOver yoneda A ⋙ (overEquivPresheafCostructuredArrow A).functor ≅ yoneda :=
  toOverYonedaCompRestrictedYoneda A
def CostructuredArrow.toOverCompYoneda (A : Cᵒᵖ ⥤ Type v) (T : Over A) :
    (CostructuredArrow.toOver yoneda A).op ⋙ yoneda.obj T ≅
      yoneda.op ⋙ yoneda.obj ((overEquivPresheafCostructuredArrow A).functor.obj T) :=
  NatIso.ofComponents (fun X =>
    (overEquivPresheafCostructuredArrow A).fullyFaithfulFunctor.homEquiv.toIso ≪≫
      (Iso.homCongr
        ((CostructuredArrow.toOverCompOverEquivPresheafCostructuredArrow A).app X.unop)
        (Iso.refl _)).toIso)
    (by aesop_cat)
@[simp]
theorem CostructuredArrow.overEquivPresheafCostructuredArrow_inverse_map_toOverCompYoneda
    {A : Cᵒᵖ ⥤ Type v} {T : Over A} {X : CostructuredArrow yoneda A}
    (f : (CostructuredArrow.toOver yoneda A).obj X ⟶ T) :
    (overEquivPresheafCostructuredArrow A).inverse.map
      (((CostructuredArrow.toOverCompYoneda A T).hom.app (op X) f)) =
      (CostructuredArrow.toOverCompOverEquivPresheafCostructuredArrow A).isoCompInverse.inv.app X ≫
        f ≫ (overEquivPresheafCostructuredArrow A).unit.app T := by
  simp [CostructuredArrow.toOverCompYoneda]
@[simp]
theorem CostructuredArrow.overEquivPresheafCostructuredArrow_functor_map_toOverCompYoneda
    {A : Cᵒᵖ ⥤ Type v} {T : Over A} {X : CostructuredArrow yoneda A}
    (f : yoneda.obj X ⟶ (overEquivPresheafCostructuredArrow A).functor.obj T) :
    (overEquivPresheafCostructuredArrow A).functor.map
      (((CostructuredArrow.toOverCompYoneda A T).inv.app (op X) f)) =
      (CostructuredArrow.toOverCompOverEquivPresheafCostructuredArrow A).hom.app X ≫ f := by
  simp [CostructuredArrow.toOverCompYoneda]
def CostructuredArrow.toOverCompCoyoneda (A : Cᵒᵖ ⥤ Type v) :
    (CostructuredArrow.toOver yoneda A).op ⋙ coyoneda ≅
    yoneda.op ⋙ coyoneda ⋙
      (whiskeringLeft _ _ _).obj (overEquivPresheafCostructuredArrow A).functor :=
  NatIso.ofComponents (fun X => NatIso.ofComponents (fun Y =>
    (overEquivPresheafCostructuredArrow A).fullyFaithfulFunctor.homEquiv.toIso ≪≫
      (Iso.homCongr
        ((CostructuredArrow.toOverCompOverEquivPresheafCostructuredArrow A).app X.unop)
        (Iso.refl _)).toIso)) (by aesop_cat)
@[simp]
theorem CostructuredArrow.overEquivPresheafCostructuredArrow_inverse_map_toOverCompCoyoneda
    {A : Cᵒᵖ ⥤ Type v} {T : Over A} {X : CostructuredArrow yoneda A}
    (f : (CostructuredArrow.toOver yoneda A).obj X ⟶ T) :
    (overEquivPresheafCostructuredArrow A).inverse.map
      (((CostructuredArrow.toOverCompCoyoneda A).hom.app (op X)).app T f) =
      (CostructuredArrow.toOverCompOverEquivPresheafCostructuredArrow A).isoCompInverse.inv.app X ≫
        f ≫ (overEquivPresheafCostructuredArrow A).unit.app T := by
  simp [CostructuredArrow.toOverCompCoyoneda]
@[simp]
theorem CostructuredArrow.overEquivPresheafCostructuredArrow_functor_map_toOverCompCoyoneda
    {A : Cᵒᵖ ⥤ Type v} {T : Over A} {X : CostructuredArrow yoneda A}
    (f : yoneda.obj X ⟶ (overEquivPresheafCostructuredArrow A).functor.obj T) :
    (overEquivPresheafCostructuredArrow A).functor.map
      (((CostructuredArrow.toOverCompCoyoneda A).inv.app (op X)).app T f) =
      (CostructuredArrow.toOverCompOverEquivPresheafCostructuredArrow A).hom.app X ≫ f := by
  simp [CostructuredArrow.toOverCompCoyoneda]
end CategoryTheory