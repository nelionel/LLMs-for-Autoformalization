import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Equalizers
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import Mathlib.CategoryTheory.Limits.Yoneda
import Mathlib.CategoryTheory.Preadditive.FunctorCategory
import Mathlib.CategoryTheory.Sites.SheafOfTypes
import Mathlib.CategoryTheory.Sites.EqualizerSheafCondition
import Mathlib.CategoryTheory.Limits.Constructions.EpiMono
universe w v₁ v₂ v₃ u₁ u₂ u₃
noncomputable section
namespace CategoryTheory
open Opposite CategoryTheory Category Limits Sieve
namespace Presheaf
variable {C : Type u₁} [Category.{v₁} C]
variable {A : Type u₂} [Category.{v₂} A]
variable (J : GrothendieckTopology C)
def IsSheaf (P : Cᵒᵖ ⥤ A) : Prop :=
  ∀ E : A, Presieve.IsSheaf J (P ⋙ coyoneda.obj (op E))
attribute [local instance] ConcreteCategory.hasCoeToSort ConcreteCategory.instFunLike in
def IsSeparated (P : Cᵒᵖ ⥤ A) [ConcreteCategory A] : Prop :=
  ∀ (X : C) (S : Sieve X) (_ : S ∈ J X) (x y : P.obj (op X)),
    (∀ (Y : C) (f : Y ⟶ X) (_ : S f), P.map f.op x = P.map f.op y) → x = y
section LimitSheafCondition
open Presieve Presieve.FamilyOfElements Limits
variable (P : Cᵒᵖ ⥤ A) {X : C} (S : Sieve X) (R : Presieve X) (E : Aᵒᵖ)
@[simps]
def conesEquivSieveCompatibleFamily :
    (S.arrows.diagram.op ⋙ P).cones.obj E ≃
      { x : FamilyOfElements (P ⋙ coyoneda.obj E) (S : Presieve X) // x.SieveCompatible } where
  toFun π :=
    ⟨fun _ f h => π.app (op ⟨Over.mk f, h⟩), fun X Y f g hf => by
      apply (id_comp _).symm.trans
      dsimp
      exact π.naturality (Quiver.Hom.op (Over.homMk _ (by rfl)))⟩
  invFun x :=
    { app := fun f => x.1 f.unop.1.hom f.unop.2
      naturality := fun f f' g => by
        refine Eq.trans ?_ (x.2 f.unop.1.hom g.unop.left f.unop.2)
        dsimp
        rw [id_comp]
        convert rfl
        rw [Over.w] }
  left_inv _ := rfl
  right_inv _ := rfl
attribute [nolint simpNF] CategoryTheory.Presheaf.conesEquivSieveCompatibleFamily_apply_coe
  CategoryTheory.Presheaf.conesEquivSieveCompatibleFamily_symm_apply_app
variable {P S E}
variable {x : FamilyOfElements (P ⋙ coyoneda.obj E) S.arrows} (hx : SieveCompatible x)
@[simp]
def _root_.CategoryTheory.Presieve.FamilyOfElements.SieveCompatible.cone :
    Cone (S.arrows.diagram.op ⋙ P) where
  pt := E.unop
  π := (conesEquivSieveCompatibleFamily P S E).invFun ⟨x, hx⟩
def homEquivAmalgamation :
    (hx.cone ⟶ P.mapCone S.arrows.cocone.op) ≃ { t // x.IsAmalgamation t } where
  toFun l := ⟨l.hom, fun _ f hf => l.w (op ⟨Over.mk f, hf⟩)⟩
  invFun t := ⟨t.1, fun f => t.2 f.unop.1.hom f.unop.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
variable (P S)
theorem isLimit_iff_isSheafFor :
    Nonempty (IsLimit (P.mapCone S.arrows.cocone.op)) ↔
      ∀ E : Aᵒᵖ, IsSheafFor (P ⋙ coyoneda.obj E) S.arrows := by
  dsimp [IsSheafFor]; simp_rw [compatible_iff_sieveCompatible]
  rw [((Cone.isLimitEquivIsTerminal _).trans (isTerminalEquivUnique _ _)).nonempty_congr]
  rw [Classical.nonempty_pi]; constructor
  · intro hu E x hx
    specialize hu hx.cone
    rw [(homEquivAmalgamation hx).uniqueCongr.nonempty_congr] at hu
    exact (unique_subtype_iff_exists_unique _).1 hu
  · rintro h ⟨E, π⟩
    let eqv := conesEquivSieveCompatibleFamily P S (op E)
    rw [← eqv.left_inv π]
    erw [(homEquivAmalgamation (eqv π).2).uniqueCongr.nonempty_congr]
    rw [unique_subtype_iff_exists_unique]
    exact h _ _ (eqv π).2
theorem subsingleton_iff_isSeparatedFor :
    (∀ c, Subsingleton (c ⟶ P.mapCone S.arrows.cocone.op)) ↔
      ∀ E : Aᵒᵖ, IsSeparatedFor (P ⋙ coyoneda.obj E) S.arrows := by
  constructor
  · intro hs E x t₁ t₂ h₁ h₂
    have hx := is_compatible_of_exists_amalgamation x ⟨t₁, h₁⟩
    rw [compatible_iff_sieveCompatible] at hx
    specialize hs hx.cone
    rcases hs with ⟨hs⟩
    simpa only [Subtype.mk.injEq] using (show Subtype.mk t₁ h₁ = ⟨t₂, h₂⟩ from
      (homEquivAmalgamation hx).symm.injective (hs _ _))
  · rintro h ⟨E, π⟩
    let eqv := conesEquivSieveCompatibleFamily P S (op E)
    constructor
    rw [← eqv.left_inv π]
    intro f₁ f₂
    let eqv' := homEquivAmalgamation (eqv π).2
    apply eqv'.injective
    ext
    apply h _ (eqv π).1 <;> exact (eqv' _).2
theorem isSheaf_iff_isLimit :
    IsSheaf J P ↔
      ∀ ⦃X : C⦄ (S : Sieve X), S ∈ J X → Nonempty (IsLimit (P.mapCone S.arrows.cocone.op)) :=
  ⟨fun h _ S hS => (isLimit_iff_isSheafFor P S).2 fun E => h E.unop S hS, fun h E _ S hS =>
    (isLimit_iff_isSheafFor P S).1 (h S hS) (op E)⟩
theorem isSeparated_iff_subsingleton :
    (∀ E : A, Presieve.IsSeparated J (P ⋙ coyoneda.obj (op E))) ↔
      ∀ ⦃X : C⦄ (S : Sieve X), S ∈ J X → ∀ c, Subsingleton (c ⟶ P.mapCone S.arrows.cocone.op) :=
  ⟨fun h _ S hS => (subsingleton_iff_isSeparatedFor P S).2 fun E => h E.unop S hS, fun h E _ S hS =>
    (subsingleton_iff_isSeparatedFor P S).1 (h S hS) (op E)⟩
theorem isLimit_iff_isSheafFor_presieve :
    Nonempty (IsLimit (P.mapCone (generate R).arrows.cocone.op)) ↔
      ∀ E : Aᵒᵖ, IsSheafFor (P ⋙ coyoneda.obj E) R :=
  (isLimit_iff_isSheafFor P _).trans (forall_congr' fun _ => (isSheafFor_iff_generate _).symm)
theorem isSheaf_iff_isLimit_pretopology [HasPullbacks C] (K : Pretopology C) :
    IsSheaf (K.toGrothendieck C) P ↔
      ∀ ⦃X : C⦄ (R : Presieve X),
        R ∈ K X → Nonempty (IsLimit (P.mapCone (generate R).arrows.cocone.op)) := by
  dsimp [IsSheaf]
  simp_rw [isSheaf_pretopology]
  exact
    ⟨fun h X R hR => (isLimit_iff_isSheafFor_presieve P R).2 fun E => h E.unop R hR,
      fun h E X R hR => (isLimit_iff_isSheafFor_presieve P R).1 (h R hR) (op E)⟩
end LimitSheafCondition
variable {J}
def IsSheaf.amalgamate {A : Type u₂} [Category.{v₂} A] {E : A} {X : C} {P : Cᵒᵖ ⥤ A}
    (hP : Presheaf.IsSheaf J P) (S : J.Cover X) (x : ∀ I : S.Arrow, E ⟶ P.obj (op I.Y))
    (hx : ∀ ⦃I₁ I₂ : S.Arrow⦄ (r : I₁.Relation I₂),
       x I₁ ≫ P.map r.g₁.op = x I₂ ≫ P.map r.g₂.op) : E ⟶ P.obj (op X) :=
  (hP _ _ S.condition).amalgamate (fun Y f hf => x ⟨Y, f, hf⟩) fun _ _ _ _ _ _ _ h₁ h₂ w =>
    @hx { hf := h₁ } { hf := h₂ } { w := w }
@[reassoc (attr := simp)]
theorem IsSheaf.amalgamate_map {A : Type u₂} [Category.{v₂} A] {E : A} {X : C} {P : Cᵒᵖ ⥤ A}
    (hP : Presheaf.IsSheaf J P) (S : J.Cover X) (x : ∀ I : S.Arrow, E ⟶ P.obj (op I.Y))
    (hx : ∀ ⦃I₁ I₂ : S.Arrow⦄ (r : I₁.Relation I₂),
       x I₁ ≫ P.map r.g₁.op = x I₂ ≫ P.map r.g₂.op)
    (I : S.Arrow) :
    hP.amalgamate S x hx ≫ P.map I.f.op = x _ := by
  apply (hP _ _ S.condition).valid_glue
theorem IsSheaf.hom_ext {A : Type u₂} [Category.{v₂} A] {E : A} {X : C} {P : Cᵒᵖ ⥤ A}
    (hP : Presheaf.IsSheaf J P) (S : J.Cover X) (e₁ e₂ : E ⟶ P.obj (op X))
    (h : ∀ I : S.Arrow, e₁ ≫ P.map I.f.op = e₂ ≫ P.map I.f.op) : e₁ = e₂ :=
  (hP _ _ S.condition).isSeparatedFor.ext fun Y f hf => h ⟨Y, f, hf⟩
lemma IsSheaf.hom_ext_ofArrows
    {P : Cᵒᵖ ⥤ A} (hP : Presheaf.IsSheaf J P) {I : Type*} {S : C} {X : I → C}
    (f : ∀ i, X i ⟶ S) (hf : Sieve.ofArrows _ f ∈ J S) {E : A}
    {x y : E ⟶ P.obj (op S)} (h : ∀ i, x ≫ P.map (f i).op = y ≫ P.map (f i).op) :
    x = y := by
  apply hP.hom_ext ⟨_, hf⟩
  rintro ⟨Z, _, _, g, _, ⟨i⟩, rfl⟩
  dsimp
  rw [P.map_comp, reassoc_of% (h i)]
section
variable {P : Cᵒᵖ ⥤ A} (hP : Presheaf.IsSheaf J P) {I : Type*} {S : C} {X : I → C}
  (f : ∀ i, X i ⟶ S) (hf : Sieve.ofArrows _ f ∈ J S) {E : A}
  (x : ∀ i, E ⟶ P.obj (op (X i)))
  (hx : ∀ ⦃W : C⦄ ⦃i j : I⦄ (a : W ⟶ X i) (b : W ⟶ X j),
    a ≫ f i = b ≫ f j → x i ≫ P.map a.op = x j ≫ P.map b.op)
include hP hf hx
lemma IsSheaf.exists_unique_amalgamation_ofArrows :
    ∃! (g : E ⟶ P.obj (op S)), ∀ (i : I), g ≫ P.map (f i).op = x i :=
  (Presieve.isSheafFor_arrows_iff _ _).1
    ((Presieve.isSheafFor_iff_generate _).2 (hP E _ hf)) x (fun _ _ _ _ _ w => hx _ _ w)
def IsSheaf.amalgamateOfArrows : E ⟶ P.obj (op S) :=
  (hP.exists_unique_amalgamation_ofArrows f hf x hx).choose
@[reassoc (attr := simp)]
lemma IsSheaf.amalgamateOfArrows_map (i : I) :
    hP.amalgamateOfArrows f hf x hx ≫ P.map (f i).op = x i :=
  (hP.exists_unique_amalgamation_ofArrows f hf x hx).choose_spec.1 i
end
theorem isSheaf_of_iso_iff {P P' : Cᵒᵖ ⥤ A} (e : P ≅ P') : IsSheaf J P ↔ IsSheaf J P' :=
  forall_congr' fun _ =>
    ⟨Presieve.isSheaf_iso J (isoWhiskerRight e _),
      Presieve.isSheaf_iso J (isoWhiskerRight e.symm _)⟩
variable (J)
theorem isSheaf_of_isTerminal {X : A} (hX : IsTerminal X) :
    Presheaf.IsSheaf J ((CategoryTheory.Functor.const _).obj X) := fun _ _ _ _ _ _ =>
  ⟨hX.from _, fun _ _ _ => hX.hom_ext _ _, fun _ _ => hX.hom_ext _ _⟩
end Presheaf
variable {C : Type u₁} [Category.{v₁} C]
variable (J : GrothendieckTopology C)
variable (A : Type u₂) [Category.{v₂} A]
structure Sheaf where
  val : Cᵒᵖ ⥤ A
  cond : Presheaf.IsSheaf J val
namespace Sheaf
variable {J A}
@[ext]
structure Hom (X Y : Sheaf J A) where
  val : X.val ⟶ Y.val
@[simps id_val comp_val]
instance instCategorySheaf : Category (Sheaf J A) where
  Hom := Hom
  id _ := ⟨𝟙 _⟩
  comp f g := ⟨f.val ≫ g.val⟩
  id_comp _ := Hom.ext <| id_comp _
  comp_id _ := Hom.ext <| comp_id _
  assoc _ _ _ := Hom.ext <| assoc _ _ _
instance (X : Sheaf J A) : Inhabited (Hom X X) :=
  ⟨𝟙 X⟩
@[ext]
lemma hom_ext {X Y : Sheaf J A} (x y : X ⟶ Y) (h : x.val = y.val) : x = y :=
  Sheaf.Hom.ext h
end Sheaf
@[simps]
def sheafToPresheaf : Sheaf J A ⥤ Cᵒᵖ ⥤ A where
  obj := Sheaf.val
  map f := f.val
  map_id _ := rfl
  map_comp _ _ := rfl
abbrev sheafSections : Cᵒᵖ ⥤ Sheaf J A ⥤ A := (sheafToPresheaf J A).flip
@[simps]
def fullyFaithfulSheafToPresheaf : (sheafToPresheaf J A).FullyFaithful where
  preimage f := ⟨f⟩
variable {J A} in
abbrev Sheaf.homEquiv {X Y : Sheaf J A} : (X ⟶ Y) ≃ (X.val ⟶ Y.val) :=
  (fullyFaithfulSheafToPresheaf J A).homEquiv
instance : (sheafToPresheaf J A).Full :=
  (fullyFaithfulSheafToPresheaf J A).full
instance : (sheafToPresheaf J A).Faithful :=
  (fullyFaithfulSheafToPresheaf J A).faithful
instance : (sheafToPresheaf J A).ReflectsIsomorphisms :=
  (fullyFaithfulSheafToPresheaf J A).reflectsIsomorphisms
theorem Sheaf.Hom.mono_of_presheaf_mono {F G : Sheaf J A} (f : F ⟶ G) [h : Mono f.1] : Mono f :=
  (sheafToPresheaf J A).mono_of_mono_map h
instance Sheaf.Hom.epi_of_presheaf_epi {F G : Sheaf J A} (f : F ⟶ G) [h : Epi f.1] : Epi f :=
  (sheafToPresheaf J A).epi_of_epi_map h
theorem isSheaf_iff_isSheaf_of_type (P : Cᵒᵖ ⥤ Type w) :
    Presheaf.IsSheaf J P ↔ Presieve.IsSheaf J P := by
  constructor
  · intro hP
    refine Presieve.isSheaf_iso J ?_ (hP PUnit)
    exact isoWhiskerLeft _ Coyoneda.punitIso ≪≫ P.rightUnitor
  · intro hP X Y S hS z hz
    refine ⟨fun x => (hP S hS).amalgamate (fun Z f hf => z f hf x) ?_, ?_, ?_⟩
    · intro Y₁ Y₂ Z g₁ g₂ f₁ f₂ hf₁ hf₂ h
      exact congr_fun (hz g₁ g₂ hf₁ hf₂ h) x
    · intro Z f hf
      funext x
      apply Presieve.IsSheafFor.valid_glue
    · intro y hy
      funext x
      apply (hP S hS).isSeparatedFor.ext
      intro Y' f hf
      rw [Presieve.IsSheafFor.valid_glue _ _ _ hf, ← hy _ hf]
      rfl
@[simps]
def sheafOver {A : Type u₂} [Category.{v₂} A] {J : GrothendieckTopology C} (ℱ : Sheaf J A) (E : A) :
    Sheaf J (Type _) where
  val := ℱ.val ⋙ coyoneda.obj (op E)
  cond := by
    rw [isSheaf_iff_isSheaf_of_type]
    exact ℱ.cond E
variable {J} in
lemma Presheaf.IsSheaf.isSheafFor {P : Cᵒᵖ ⥤ Type w} (hP : Presheaf.IsSheaf J P)
    {X : C} (S : Sieve X) (hS : S ∈ J X) : Presieve.IsSheafFor P S.arrows := by
  rw [isSheaf_iff_isSheaf_of_type] at hP
  exact hP S hS
variable {A} in
lemma Presheaf.isSheaf_bot (P : Cᵒᵖ ⥤ A) : IsSheaf ⊥ P := fun _ ↦ Presieve.isSheaf_bot
@[simps]
def sheafBotEquivalence : Sheaf (⊥ : GrothendieckTopology C) A ≌ Cᵒᵖ ⥤ A where
  functor := sheafToPresheaf _ _
  inverse :=
    { obj := fun P => ⟨P, Presheaf.isSheaf_bot P⟩
      map := fun f => ⟨f⟩ }
  unitIso := Iso.refl _
  counitIso := Iso.refl _
instance : Inhabited (Sheaf (⊥ : GrothendieckTopology C) (Type w)) :=
  ⟨(sheafBotEquivalence _).inverse.obj ((Functor.const _).obj default)⟩
variable {J} {A}
def Sheaf.isTerminalOfBotCover (F : Sheaf J A) (X : C) (H : ⊥ ∈ J X) :
    IsTerminal (F.1.obj (op X)) := by
  refine @IsTerminal.ofUnique _ _ _ ?_
  intro Y
  choose t h using F.2 Y _ H (by tauto) (by tauto)
  exact ⟨⟨t⟩, fun a => h.2 a (by tauto)⟩
section Preadditive
open Preadditive
variable [Preadditive A] {P Q : Sheaf J A}
instance sheafHomHasZSMul : SMul ℤ (P ⟶ Q) where
  smul n f :=
    Sheaf.Hom.mk
      { app := fun U => n • f.1.app U
        naturality := fun U V i => by
          induction' n using Int.induction_on with n ih n ih
          · simp only [zero_smul, comp_zero, zero_comp]
          · simpa only [add_zsmul, one_zsmul, comp_add, NatTrans.naturality, add_comp,
              add_left_inj]
          · simpa only [sub_smul, one_zsmul, comp_sub, NatTrans.naturality, sub_comp,
              sub_left_inj] using ih }
instance : Sub (P ⟶ Q) where sub f g := Sheaf.Hom.mk <| f.1 - g.1
instance : Neg (P ⟶ Q) where neg f := Sheaf.Hom.mk <| -f.1
instance sheafHomHasNSMul : SMul ℕ (P ⟶ Q) where
  smul n f :=
    Sheaf.Hom.mk
      { app := fun U => n • f.1.app U
        naturality := fun U V i => by
          induction n with
          | zero => simp only [zero_smul, comp_zero, zero_comp]
          | succ n ih => simp only [Nat.succ_eq_add_one, add_smul, ih, one_nsmul, comp_add,
              NatTrans.naturality, add_comp] }
instance : Zero (P ⟶ Q) where zero := Sheaf.Hom.mk 0
instance : Add (P ⟶ Q) where add f g := Sheaf.Hom.mk <| f.1 + g.1
@[simp]
theorem Sheaf.Hom.add_app (f g : P ⟶ Q) (U) : (f + g).1.app U = f.1.app U + g.1.app U :=
  rfl
instance Sheaf.Hom.addCommGroup : AddCommGroup (P ⟶ Q) :=
  Function.Injective.addCommGroup (fun f : Sheaf.Hom P Q => f.1)
    (fun _ _ h => Sheaf.Hom.ext h) rfl (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl)
    (fun _ _ => by aesop_cat) (fun _ _ => by aesop_cat)
instance : Preadditive (Sheaf J A) where
  homGroup _ _ := Sheaf.Hom.addCommGroup
end Preadditive
end CategoryTheory
namespace CategoryTheory
open Opposite CategoryTheory Category Limits Sieve
namespace Presheaf
variable {C : Type u₁} [Category.{v₁} C]
variable {A : Type u₂} [Category.{v₂} A]
variable {A' : Type u₂} [Category.{max v₁ u₁} A']
variable {B : Type u₃} [Category.{v₃} B]
variable (J : GrothendieckTopology C)
variable {U : C} (R : Presieve U)
variable (P : Cᵒᵖ ⥤ A) (P' : Cᵒᵖ ⥤ A')
section MultiequalizerConditions
def isLimitOfIsSheaf {X : C} (S : J.Cover X) (hP : IsSheaf J P) : IsLimit (S.multifork P) where
  lift := fun E : Multifork _ => hP.amalgamate S (fun _ => E.ι _)
    (fun _ _ r => E.condition ⟨_, _, r⟩)
  fac := by
    rintro (E : Multifork _) (a | b)
    · apply hP.amalgamate_map
    · rw [← E.w (WalkingMulticospan.Hom.fst b),
        ← (S.multifork P).w (WalkingMulticospan.Hom.fst b), ← assoc]
      congr 1
      apply hP.amalgamate_map
  uniq := by
    rintro (E : Multifork _) m hm
    apply hP.hom_ext S
    intro I
    erw [hm (WalkingMulticospan.left I)]
    symm
    apply hP.amalgamate_map
theorem isSheaf_iff_multifork :
    IsSheaf J P ↔ ∀ (X : C) (S : J.Cover X), Nonempty (IsLimit (S.multifork P)) := by
  refine ⟨fun hP X S => ⟨isLimitOfIsSheaf _ _ _ hP⟩, ?_⟩
  intro h E X S hS x hx
  let T : J.Cover X := ⟨S, hS⟩
  obtain ⟨hh⟩ := h _ T
  let K : Multifork (T.index P) := Multifork.ofι _ E (fun I => x I.f I.hf)
    (fun I => hx _ _ _ _ I.r.w)
  use hh.lift K
  dsimp; constructor
  · intro Y f hf
    apply hh.fac K (WalkingMulticospan.left ⟨Y, f, hf⟩)
  · intro e he
    apply hh.uniq K
    rintro (a | b)
    · apply he
    · rw [← K.w (WalkingMulticospan.Hom.fst b), ←
        (T.multifork P).w (WalkingMulticospan.Hom.fst b), ← assoc]
      congr 1
      apply he
variable {J P} in
def IsSheaf.isLimitMultifork
    (hP : Presheaf.IsSheaf J P) {X : C} (S : J.Cover X) : IsLimit (S.multifork P) := by
  rw [Presheaf.isSheaf_iff_multifork] at hP
  exact (hP X S).some
theorem isSheaf_iff_multiequalizer [∀ (X : C) (S : J.Cover X), HasMultiequalizer (S.index P)] :
    IsSheaf J P ↔ ∀ (X : C) (S : J.Cover X), IsIso (S.toMultiequalizer P) := by
  rw [isSheaf_iff_multifork]
  refine forall₂_congr fun X S => ⟨?_, ?_⟩
  · rintro ⟨h⟩
    let e : P.obj (op X) ≅ multiequalizer (S.index P) :=
      h.conePointUniqueUpToIso (limit.isLimit _)
    exact (inferInstance : IsIso e.hom)
  · intro h
    refine ⟨IsLimit.ofIsoLimit (limit.isLimit _) (Cones.ext ?_ ?_)⟩
    · apply (@asIso _ _ _ _ _ h).symm
    · intro a
      symm
      erw [IsIso.inv_comp_eq]
      simp
end MultiequalizerConditions
section
variable [HasProducts.{max u₁ v₁} A]
variable [HasProducts.{max u₁ v₁} A']
def firstObj : A :=
  ∏ᶜ fun f : ΣV, { f : V ⟶ U // R f } => P.obj (op f.1)
def forkMap : P.obj (op U) ⟶ firstObj R P :=
  Pi.lift fun f => P.map f.2.1.op
variable [HasPullbacks C]
def secondObj : A :=
  ∏ᶜ fun fg : (ΣV, { f : V ⟶ U // R f }) × ΣW, { g : W ⟶ U // R g } =>
    P.obj (op (pullback fg.1.2.1 fg.2.2.1))
def firstMap : firstObj R P ⟶ secondObj R P :=
  Pi.lift fun _ => Pi.π _ _ ≫ P.map (pullback.fst _ _).op
def secondMap : firstObj R P ⟶ secondObj R P :=
  Pi.lift fun _ => Pi.π _ _ ≫ P.map (pullback.snd _ _).op
theorem w : forkMap R P ≫ firstMap R P = forkMap R P ≫ secondMap R P := by
  apply limit.hom_ext
  rintro ⟨⟨Y, f, hf⟩, ⟨Z, g, hg⟩⟩
  simp only [firstMap, secondMap, forkMap, limit.lift_π, limit.lift_π_assoc, assoc, Fan.mk_π_app,
    Subtype.coe_mk]
  rw [← P.map_comp, ← op_comp, pullback.condition]
  simp
def IsSheaf' (P : Cᵒᵖ ⥤ A) : Prop :=
  ∀ (U : C) (R : Presieve U) (_ : generate R ∈ J U), Nonempty (IsLimit (Fork.ofι _ (w R P)))
def isSheafForIsSheafFor' (P : Cᵒᵖ ⥤ A) (s : A ⥤ Type max v₁ u₁)
    [∀ J, PreservesLimitsOfShape (Discrete.{max v₁ u₁} J) s] (U : C) (R : Presieve U) :
    IsLimit (s.mapCone (Fork.ofι _ (w R P))) ≃
      IsLimit (Fork.ofι _ (Equalizer.Presieve.w (P ⋙ s) R)) := by
  let e : parallelPair (s.map (firstMap R P)) (s.map (secondMap R P)) ≅
    parallelPair (Equalizer.Presieve.firstMap (P ⋙ s) R)
      (Equalizer.Presieve.secondMap (P ⋙ s) R) := by
    refine parallelPair.ext (PreservesProduct.iso s _) ((PreservesProduct.iso s _))
      (limit.hom_ext (fun j => ?_)) (limit.hom_ext (fun j => ?_))
    · dsimp [Equalizer.Presieve.firstMap, firstMap]
      simp only [map_lift_piComparison, Functor.map_comp, limit.lift_π, Fan.mk_pt,
        Fan.mk_π_app, assoc, piComparison_comp_π_assoc]
    · dsimp [Equalizer.Presieve.secondMap, secondMap]
      simp only [map_lift_piComparison, Functor.map_comp, limit.lift_π, Fan.mk_pt,
        Fan.mk_π_app, assoc, piComparison_comp_π_assoc]
  refine Equiv.trans (isLimitMapConeForkEquiv _ _) ?_
  refine (IsLimit.postcomposeHomEquiv e _).symm.trans
    (IsLimit.equivIsoLimit (Fork.ext (Iso.refl _) ?_))
  dsimp [Equalizer.forkMap, forkMap, e, Fork.ι]
  simp only [id_comp, map_lift_piComparison]
theorem isSheaf_iff_isSheaf' : IsSheaf J P' ↔ IsSheaf' J P' := by
  constructor
  · intro h U R hR
    refine ⟨?_⟩
    apply coyonedaJointlyReflectsLimits
    intro X
    have q : Presieve.IsSheafFor (P' ⋙ coyoneda.obj X) _ := h X.unop _ hR
    rw [← Presieve.isSheafFor_iff_generate] at q
    rw [Equalizer.Presieve.sheaf_condition] at q
    replace q := Classical.choice q
    apply (isSheafForIsSheafFor' _ _ _ _).symm q
  · intro h U X S hS
    rw [Equalizer.Presieve.sheaf_condition]
    refine ⟨?_⟩
    refine isSheafForIsSheafFor' _ _ _ _ ?_
    letI := preservesSmallestLimits_of_preservesLimits (coyoneda.obj (op U))
    apply isLimitOfPreserves
    apply Classical.choice (h _ S.arrows _)
    simpa
end
section Concrete
theorem isSheaf_of_isSheaf_comp (s : A ⥤ B) [ReflectsLimitsOfSize.{v₁, max v₁ u₁} s]
    (h : IsSheaf J (P ⋙ s)) : IsSheaf J P := by
  rw [isSheaf_iff_isLimit] at h ⊢
  exact fun X S hS ↦ (h S hS).map fun t ↦ isLimitOfReflects s t
theorem isSheaf_comp_of_isSheaf (s : A ⥤ B) [PreservesLimitsOfSize.{v₁, max v₁ u₁} s]
    (h : IsSheaf J P) : IsSheaf J (P ⋙ s) := by
  rw [isSheaf_iff_isLimit] at h ⊢
  apply fun X S hS ↦ (h S hS).map fun t ↦ isLimitOfPreserves s t
theorem isSheaf_iff_isSheaf_comp (s : A ⥤ B) [HasLimitsOfSize.{v₁, max v₁ u₁} A]
    [PreservesLimitsOfSize.{v₁, max v₁ u₁} s] [s.ReflectsIsomorphisms] :
    IsSheaf J P ↔ IsSheaf J (P ⋙ s) := by
  letI : ReflectsLimitsOfSize s := reflectsLimits_of_reflectsIsomorphisms
  exact ⟨isSheaf_comp_of_isSheaf J P s, isSheaf_of_isSheaf_comp J P s⟩
theorem isSheaf_iff_isSheaf_forget (s : A' ⥤ Type max v₁ u₁) [HasLimits A'] [PreservesLimits s]
    [s.ReflectsIsomorphisms] : IsSheaf J P' ↔ IsSheaf J (P' ⋙ s) := by
  have : HasLimitsOfSize.{v₁, max v₁ u₁} A' := hasLimitsOfSizeShrink.{_, _, u₁, 0} A'
  have : PreservesLimitsOfSize.{v₁, max v₁ u₁} s := preservesLimitsOfSize_shrink.{_, 0, _, u₁} s
  apply isSheaf_iff_isSheaf_comp
end Concrete
end Presheaf
end CategoryTheory