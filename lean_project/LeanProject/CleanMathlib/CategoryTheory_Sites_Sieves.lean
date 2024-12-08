import Mathlib.Data.Set.Lattice
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
universe v₁ v₂ v₃ u₁ u₂ u₃
namespace CategoryTheory
open Category Limits
variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D] (F : C ⥤ D)
variable {X Y Z : C} (f : Y ⟶ X)
def Presieve (X : C) :=
  ∀ ⦃Y⦄, Set (Y ⟶ X)
instance : CompleteLattice (Presieve X) := by
  dsimp [Presieve]
  infer_instance
namespace Presieve
noncomputable instance : Inhabited (Presieve X) :=
  ⟨⊤⟩
abbrev category {X : C} (P : Presieve X) :=
  FullSubcategory fun f : Over X => P f.hom
abbrev categoryMk {X : C} (P : Presieve X) {Y : C} (f : Y ⟶ X) (hf : P f) : P.category :=
  ⟨Over.mk f, hf⟩
abbrev diagram (S : Presieve X) : S.category ⥤ C :=
  fullSubcategoryInclusion _ ⋙ Over.forget X
abbrev cocone (S : Presieve X) : Cocone S.diagram :=
  (Over.forgetCocone X).whisker (fullSubcategoryInclusion _)
def bind (S : Presieve X) (R : ∀ ⦃Y⦄ ⦃f : Y ⟶ X⦄, S f → Presieve Y) : Presieve X := fun Z h =>
  ∃ (Y : C) (g : Z ⟶ Y) (f : Y ⟶ X) (H : S f), R H g ∧ g ≫ f = h
@[simp]
theorem bind_comp {S : Presieve X} {R : ∀ ⦃Y : C⦄ ⦃f : Y ⟶ X⦄, S f → Presieve Y} {g : Z ⟶ Y}
    (h₁ : S f) (h₂ : R h₁ g) : bind S R (g ≫ f) :=
  ⟨_, _, _, h₁, h₂, rfl⟩
inductive singleton' : ⦃Y : C⦄ → (Y ⟶ X) → Prop
  | mk : singleton' f
def singleton : Presieve X := singleton' f
lemma singleton.mk {f : Y ⟶ X} : singleton f f := singleton'.mk
@[simp]
theorem singleton_eq_iff_domain (f g : Y ⟶ X) : singleton f g ↔ f = g := by
  constructor
  · rintro ⟨a, rfl⟩
    rfl
  · rintro rfl
    apply singleton.mk
theorem singleton_self : singleton f f :=
  singleton.mk
inductive pullbackArrows [HasPullbacks C] (R : Presieve X) : Presieve Y
  | mk (Z : C) (h : Z ⟶ X) : R h → pullbackArrows _ (pullback.snd h f)
theorem pullback_singleton [HasPullbacks C] (g : Z ⟶ X) :
    pullbackArrows f (singleton g) = singleton (pullback.snd g f) := by
  funext W
  ext h
  constructor
  · rintro ⟨W, _, _, _⟩
    exact singleton.mk
  · rintro ⟨_⟩
    exact pullbackArrows.mk Z g singleton.mk
inductive ofArrows {ι : Type*} (Y : ι → C) (f : ∀ i, Y i ⟶ X) : Presieve X
  | mk (i : ι) : ofArrows _ _ (f i)
theorem ofArrows_pUnit : (ofArrows _ fun _ : PUnit => f) = singleton f := by
  funext Y
  ext g
  constructor
  · rintro ⟨_⟩
    apply singleton.mk
  · rintro ⟨_⟩
    exact ofArrows.mk PUnit.unit
theorem ofArrows_pullback [HasPullbacks C] {ι : Type*} (Z : ι → C) (g : ∀ i : ι, Z i ⟶ X) :
    (ofArrows (fun i => pullback (g i) f) fun _ => pullback.snd _ _) =
      pullbackArrows f (ofArrows Z g) := by
  funext T
  ext h
  constructor
  · rintro ⟨hk⟩
    exact pullbackArrows.mk _ _ (ofArrows.mk hk)
  · rintro ⟨W, k, hk₁⟩
    cases' hk₁ with i hi
    apply ofArrows.mk
theorem ofArrows_bind {ι : Type*} (Z : ι → C) (g : ∀ i : ι, Z i ⟶ X)
    (j : ∀ ⦃Y⦄ (f : Y ⟶ X), ofArrows Z g f → Type*) (W : ∀ ⦃Y⦄ (f : Y ⟶ X) (H), j f H → C)
    (k : ∀ ⦃Y⦄ (f : Y ⟶ X) (H i), W f H i ⟶ Y) :
    ((ofArrows Z g).bind fun _ f H => ofArrows (W f H) (k f H)) =
      ofArrows (fun i : Σi, j _ (ofArrows.mk i) => W (g i.1) _ i.2) fun ij =>
        k (g ij.1) _ ij.2 ≫ g ij.1 := by
  funext Y
  ext f
  constructor
  · rintro ⟨_, _, _, ⟨i⟩, ⟨i'⟩, rfl⟩
    exact ofArrows.mk (Sigma.mk _ _)
  · rintro ⟨i⟩
    exact bind_comp _ (ofArrows.mk _) (ofArrows.mk _)
theorem ofArrows_surj {ι : Type*} {Y : ι → C} (f : ∀ i, Y i ⟶ X) {Z : C} (g : Z ⟶ X)
    (hg : ofArrows Y f g) : ∃ (i : ι) (h : Y i = Z),
    g = eqToHom h.symm ≫ f i := by
  cases' hg with i
  exact ⟨i, rfl, by simp only [eqToHom_refl, id_comp]⟩
def functorPullback (R : Presieve (F.obj X)) : Presieve X := fun _ f => R (F.map f)
@[simp]
theorem functorPullback_mem (R : Presieve (F.obj X)) {Y} (f : Y ⟶ X) :
    R.functorPullback F f ↔ R (F.map f) :=
  Iff.rfl
@[simp]
theorem functorPullback_id (R : Presieve X) : R.functorPullback (𝟭 _) = R :=
  rfl
class hasPullbacks (R : Presieve X) : Prop where
  has_pullbacks : ∀ {Y Z} {f : Y ⟶ X} (_ : R f) {g : Z ⟶ X} (_ : R g), HasPullback f g
instance (R : Presieve X) [HasPullbacks C] : R.hasPullbacks := ⟨fun _ _ ↦ inferInstance⟩
instance {α : Type v₂} {X : α → C} {B : C} (π : (a : α) → X a ⟶ B)
    [(Presieve.ofArrows X π).hasPullbacks] (a b : α) : HasPullback (π a) (π b) :=
  Presieve.hasPullbacks.has_pullbacks (Presieve.ofArrows.mk _) (Presieve.ofArrows.mk _)
section FunctorPushforward
variable {E : Type u₃} [Category.{v₃} E] (G : D ⥤ E)
def functorPushforward (S : Presieve X) : Presieve (F.obj X) := fun Y f =>
  ∃ (Z : C) (g : Z ⟶ X) (h : Y ⟶ F.obj Z), S g ∧ f = h ≫ F.map g
structure FunctorPushforwardStructure (S : Presieve X) {Y} (f : Y ⟶ F.obj X) where
  preobj : C
  premap : preobj ⟶ X
  lift : Y ⟶ F.obj preobj
  cover : S premap
  fac : f = lift ≫ F.map premap
noncomputable def getFunctorPushforwardStructure {F : C ⥤ D} {S : Presieve X} {Y : D}
    {f : Y ⟶ F.obj X} (h : S.functorPushforward F f) : FunctorPushforwardStructure F S f := by
  choose Z f' g h₁ h using h
  exact ⟨Z, f', g, h₁, h⟩
theorem functorPushforward_comp (R : Presieve X) :
    R.functorPushforward (F ⋙ G) = (R.functorPushforward F).functorPushforward G := by
  funext x
  ext f
  constructor
  · rintro ⟨X, f₁, g₁, h₁, rfl⟩
    exact ⟨F.obj X, F.map f₁, g₁, ⟨X, f₁, 𝟙 _, h₁, by simp⟩, rfl⟩
  · rintro ⟨X, f₁, g₁, ⟨X', f₂, g₂, h₁, rfl⟩, rfl⟩
    exact ⟨X', f₂, g₁ ≫ G.map g₂, h₁, by simp⟩
theorem image_mem_functorPushforward (R : Presieve X) {f : Y ⟶ X} (h : R f) :
    R.functorPushforward F (F.map f) :=
  ⟨Y, f, 𝟙 _, h, by simp⟩
end FunctorPushforward
end Presieve
structure Sieve {C : Type u₁} [Category.{v₁} C] (X : C) where
  arrows : Presieve X
  downward_closed : ∀ {Y Z f} (_ : arrows f) (g : Z ⟶ Y), arrows (g ≫ f)
namespace Sieve
instance : CoeFun (Sieve X) fun _ => Presieve X :=
  ⟨Sieve.arrows⟩
initialize_simps_projections Sieve (arrows → apply)
variable {S R : Sieve X}
attribute [simp] downward_closed
theorem arrows_ext : ∀ {R S : Sieve X}, R.arrows = S.arrows → R = S := by
  rintro ⟨_, _⟩ ⟨_, _⟩ rfl
  rfl
@[ext]
protected theorem ext {R S : Sieve X} (h : ∀ ⦃Y⦄ (f : Y ⟶ X), R f ↔ S f) : R = S :=
  arrows_ext <| funext fun _ => funext fun f => propext <| h f
open Lattice
protected def sup (𝒮 : Set (Sieve X)) : Sieve X where
  arrows _ := { f | ∃ S ∈ 𝒮, Sieve.arrows S f }
  downward_closed {_ _ f} hf _ := by
    obtain ⟨S, hS, hf⟩ := hf
    exact ⟨S, hS, S.downward_closed hf _⟩
protected def inf (𝒮 : Set (Sieve X)) : Sieve X where
  arrows _ := { f | ∀ S ∈ 𝒮, Sieve.arrows S f }
  downward_closed {_ _ _} hf g S H := S.downward_closed (hf S H) g
protected def union (S R : Sieve X) : Sieve X where
  arrows _ f := S f ∨ R f
  downward_closed := by rintro _ _ _ (h | h) g <;> simp [h]
protected def inter (S R : Sieve X) : Sieve X where
  arrows _ f := S f ∧ R f
  downward_closed := by
    rintro _ _ _ ⟨h₁, h₂⟩ g
    simp [h₁, h₂]
instance : CompleteLattice (Sieve X) where
  le S R := ∀ ⦃Y⦄ (f : Y ⟶ X), S f → R f
  le_refl _ _ _ := id
  le_trans _ _ _ S₁₂ S₂₃ _ _ h := S₂₃ _ (S₁₂ _ h)
  le_antisymm _ _ p q := Sieve.ext fun _ _ => ⟨p _, q _⟩
  top :=
    { arrows := fun _ => Set.univ
      downward_closed := fun _ _ => ⟨⟩ }
  bot :=
    { arrows := fun _ => ∅
      downward_closed := False.elim }
  sup := Sieve.union
  inf := Sieve.inter
  sSup := Sieve.sup
  sInf := Sieve.inf
  le_sSup _ S hS _ _ hf := ⟨S, hS, hf⟩
  sSup_le := fun _ _ ha _ _ ⟨b, hb, hf⟩ => (ha b hb) _ hf
  sInf_le _ _ hS _ _ h := h _ hS
  le_sInf _ _ hS _ _ hf _ hR := hS _ hR _ hf
  le_sup_left _ _ _ _ := Or.inl
  le_sup_right _ _ _ _ := Or.inr
  sup_le _ _ _ h₁ h₂ _ f := by
    rintro (hf | hf)
    · exact h₁ _ hf
    · exact h₂ _ hf
  inf_le_left _ _ _ _ := And.left
  inf_le_right _ _ _ _ := And.right
  le_inf _ _ _ p q _ _ z := ⟨p _ z, q _ z⟩
  le_top _ _ _ _ := trivial
  bot_le _ _ _ := False.elim
instance sieveInhabited : Inhabited (Sieve X) :=
  ⟨⊤⟩
@[simp]
theorem sInf_apply {Ss : Set (Sieve X)} {Y} (f : Y ⟶ X) :
    sInf Ss f ↔ ∀ (S : Sieve X) (_ : S ∈ Ss), S f :=
  Iff.rfl
@[simp]
theorem sSup_apply {Ss : Set (Sieve X)} {Y} (f : Y ⟶ X) :
    sSup Ss f ↔ ∃ (S : Sieve X) (_ : S ∈ Ss), S f := by
  simp [sSup, Sieve.sup, setOf]
@[simp]
theorem inter_apply {R S : Sieve X} {Y} (f : Y ⟶ X) : (R ⊓ S) f ↔ R f ∧ S f :=
  Iff.rfl
@[simp]
theorem union_apply {R S : Sieve X} {Y} (f : Y ⟶ X) : (R ⊔ S) f ↔ R f ∨ S f :=
  Iff.rfl
@[simp]
theorem top_apply (f : Y ⟶ X) : (⊤ : Sieve X) f :=
  trivial
@[simps]
def generate (R : Presieve X) : Sieve X where
  arrows Z f := ∃ (Y : _) (h : Z ⟶ Y) (g : Y ⟶ X), R g ∧ h ≫ g = f
  downward_closed := by
    rintro Y Z _ ⟨W, g, f, hf, rfl⟩ h
    exact ⟨_, h ≫ g, _, hf, by simp⟩
@[simps]
def bind (S : Presieve X) (R : ∀ ⦃Y⦄ ⦃f : Y ⟶ X⦄, S f → Sieve Y) : Sieve X where
  arrows := S.bind fun _ _ h => R h
  downward_closed := by
    rintro Y Z f ⟨W, f, h, hh, hf, rfl⟩ g
    exact ⟨_, g ≫ f, _, hh, by simp [hf]⟩
open Order Lattice
theorem generate_le_iff (R : Presieve X) (S : Sieve X) : generate R ≤ S ↔ R ≤ S :=
  ⟨fun H _ _ hg => H _ ⟨_, 𝟙 _, _, hg, id_comp _⟩, fun ss Y f => by
    rintro ⟨Z, f, g, hg, rfl⟩
    exact S.downward_closed (ss Z hg) f⟩
@[deprecated (since := "2024-07-13")] alias sets_iff_generate := generate_le_iff
def giGenerate : GaloisInsertion (generate : Presieve X → Sieve X) arrows where
  gc := generate_le_iff
  choice 𝒢 _ := generate 𝒢
  choice_eq _ _ := rfl
  le_l_u _ _ _ hf := ⟨_, 𝟙 _, _, hf, id_comp _⟩
theorem le_generate (R : Presieve X) : R ≤ generate R :=
  giGenerate.gc.le_u_l R
@[simp]
theorem generate_sieve (S : Sieve X) : generate S = S :=
  giGenerate.l_u_eq S
theorem id_mem_iff_eq_top : S (𝟙 X) ↔ S = ⊤ :=
  ⟨fun h => top_unique fun Y f _ => by simpa using downward_closed _ h f, fun h => h.symm ▸ trivial⟩
theorem generate_of_contains_isSplitEpi {R : Presieve X} (f : Y ⟶ X) [IsSplitEpi f] (hf : R f) :
    generate R = ⊤ := by
  rw [← id_mem_iff_eq_top]
  exact ⟨_, section_ f, f, hf, by simp⟩
@[simp]
theorem generate_of_singleton_isSplitEpi (f : Y ⟶ X) [IsSplitEpi f] :
    generate (Presieve.singleton f) = ⊤ :=
  generate_of_contains_isSplitEpi f (Presieve.singleton_self _)
@[simp]
theorem generate_top : generate (⊤ : Presieve X) = ⊤ :=
  generate_of_contains_isSplitEpi (𝟙 _) ⟨⟩
@[simp]
lemma comp_mem_iff (i : X ⟶ Y) (f : Y ⟶ Z) [IsIso i] (S : Sieve Z) :
    S (i ≫ f) ↔ S f := by
  refine ⟨fun H ↦ ?_, fun H ↦ S.downward_closed H _⟩
  convert S.downward_closed H (inv i)
  simp
abbrev ofArrows {I : Type*} {X : C} (Y : I → C) (f : ∀ i, Y i ⟶ X) :
    Sieve X :=
  generate (Presieve.ofArrows Y f)
lemma ofArrows_mk {I : Type*} {X : C} (Y : I → C) (f : ∀ i, Y i ⟶ X) (i : I) :
    ofArrows Y f (f i) :=
  ⟨_, 𝟙 _, _, ⟨i⟩, by simp⟩
lemma mem_ofArrows_iff {I : Type*} {X : C} (Y : I → C) (f : ∀ i, Y i ⟶ X)
    {W : C} (g : W ⟶ X) :
    ofArrows Y f g ↔ ∃ (i : I) (a : W ⟶ Y i), g = a ≫ f i := by
  constructor
  · rintro ⟨T, a, b, ⟨i⟩, rfl⟩
    exact ⟨i, a, rfl⟩
  · rintro ⟨i, a, rfl⟩
    apply downward_closed _ (ofArrows_mk Y f i)
abbrev ofTwoArrows {U V X : C} (i : U ⟶ X) (j : V ⟶ X) : Sieve X :=
  Sieve.ofArrows (Y := pairFunction U V) (fun k ↦ WalkingPair.casesOn k i j)
def ofObjects {I : Type*} (Y : I → C) (X : C) : Sieve X where
  arrows Z _ := ∃ (i : I), Nonempty (Z ⟶ Y i)
  downward_closed := by
    rintro Z₁ Z₂ p ⟨i, ⟨f⟩⟩ g
    exact ⟨i, ⟨g ≫ f⟩⟩
lemma mem_ofObjects_iff {I : Type*} (Y : I → C) {Z X : C} (g : Z ⟶ X) :
    ofObjects Y X g ↔ ∃ (i : I), Nonempty (Z ⟶ Y i) := by rfl
lemma ofArrows_le_ofObjects
    {I : Type*} (Y : I → C) {X : C} (f : ∀ i, Y i ⟶ X) :
    Sieve.ofArrows Y f ≤ Sieve.ofObjects Y X := by
  intro W g hg
  rw [mem_ofArrows_iff] at hg
  obtain ⟨i, a, rfl⟩ := hg
  exact ⟨i, ⟨a⟩⟩
lemma ofArrows_eq_ofObjects {X : C} (hX : IsTerminal X)
    {I : Type*} (Y : I → C) (f : ∀ i, Y i ⟶ X) :
    ofArrows Y f = ofObjects Y X := by
  refine le_antisymm (ofArrows_le_ofObjects Y f) (fun W g => ?_)
  rw [mem_ofArrows_iff, mem_ofObjects_iff]
  rintro ⟨i, ⟨h⟩⟩
  exact ⟨i, h, hX.hom_ext _ _⟩
@[simps]
def pullback (h : Y ⟶ X) (S : Sieve X) : Sieve Y where
  arrows _ sl := S (sl ≫ h)
  downward_closed g := by simp [g]
@[simp]
theorem pullback_id : S.pullback (𝟙 _) = S := by simp [Sieve.ext_iff]
@[simp]
theorem pullback_top {f : Y ⟶ X} : (⊤ : Sieve X).pullback f = ⊤ :=
  top_unique fun _ _ => id
theorem pullback_comp {f : Y ⟶ X} {g : Z ⟶ Y} (S : Sieve X) :
    S.pullback (g ≫ f) = (S.pullback f).pullback g := by simp [Sieve.ext_iff]
@[simp]
theorem pullback_inter {f : Y ⟶ X} (S R : Sieve X) :
    (S ⊓ R).pullback f = S.pullback f ⊓ R.pullback f := by simp [Sieve.ext_iff]
theorem pullback_eq_top_iff_mem (f : Y ⟶ X) : S f ↔ S.pullback f = ⊤ := by
  rw [← id_mem_iff_eq_top, pullback_apply, id_comp]
theorem pullback_eq_top_of_mem (S : Sieve X) {f : Y ⟶ X} : S f → S.pullback f = ⊤ :=
  (pullback_eq_top_iff_mem f).1
lemma pullback_ofObjects_eq_top
    {I : Type*} (Y : I → C) {X : C} {i : I} (g : X ⟶ Y i) :
    ofObjects Y X = ⊤ := by
  ext Z h
  simp only [top_apply, iff_true]
  rw [mem_ofObjects_iff ]
  exact ⟨i, ⟨h ≫ g⟩⟩
@[simps]
def pushforward (f : Y ⟶ X) (R : Sieve Y) : Sieve X where
  arrows _ gf := ∃ g, g ≫ f = gf ∧ R g
  downward_closed := fun ⟨j, k, z⟩ h => ⟨h ≫ j, by simp [k], by simp [z]⟩
theorem pushforward_apply_comp {R : Sieve Y} {Z : C} {g : Z ⟶ Y} (hg : R g) (f : Y ⟶ X) :
    R.pushforward f (g ≫ f) :=
  ⟨g, rfl, hg⟩
theorem pushforward_comp {f : Y ⟶ X} {g : Z ⟶ Y} (R : Sieve Z) :
    R.pushforward (g ≫ f) = (R.pushforward g).pushforward f :=
  Sieve.ext fun W h =>
    ⟨fun ⟨f₁, hq, hf₁⟩ => ⟨f₁ ≫ g, by simpa, f₁, rfl, hf₁⟩, fun ⟨y, hy, z, hR, hz⟩ =>
      ⟨z, by rw [← Category.assoc, hR]; tauto⟩⟩
theorem galoisConnection (f : Y ⟶ X) : GaloisConnection (Sieve.pushforward f) (Sieve.pullback f) :=
  fun _ _ => ⟨fun hR _ g hg => hR _ ⟨g, rfl, hg⟩, fun hS _ _ ⟨h, hg, hh⟩ => hg ▸ hS h hh⟩
theorem pullback_monotone (f : Y ⟶ X) : Monotone (Sieve.pullback f) :=
  (galoisConnection f).monotone_u
theorem pushforward_monotone (f : Y ⟶ X) : Monotone (Sieve.pushforward f) :=
  (galoisConnection f).monotone_l
theorem le_pushforward_pullback (f : Y ⟶ X) (R : Sieve Y) : R ≤ (R.pushforward f).pullback f :=
  (galoisConnection f).le_u_l _
theorem pullback_pushforward_le (f : Y ⟶ X) (R : Sieve X) : (R.pullback f).pushforward f ≤ R :=
  (galoisConnection f).l_u_le _
theorem pushforward_union {f : Y ⟶ X} (S R : Sieve Y) :
    (S ⊔ R).pushforward f = S.pushforward f ⊔ R.pushforward f :=
  (galoisConnection f).l_sup
theorem pushforward_le_bind_of_mem (S : Presieve X) (R : ∀ ⦃Y : C⦄ ⦃f : Y ⟶ X⦄, S f → Sieve Y)
    (f : Y ⟶ X) (h : S f) : (R h).pushforward f ≤ bind S R := by
  rintro Z _ ⟨g, rfl, hg⟩
  exact ⟨_, g, f, h, hg, rfl⟩
theorem le_pullback_bind (S : Presieve X) (R : ∀ ⦃Y : C⦄ ⦃f : Y ⟶ X⦄, S f → Sieve Y) (f : Y ⟶ X)
    (h : S f) : R h ≤ (bind S R).pullback f := by
  rw [← galoisConnection f]
  apply pushforward_le_bind_of_mem
def galoisCoinsertionOfMono (f : Y ⟶ X) [Mono f] :
    GaloisCoinsertion (Sieve.pushforward f) (Sieve.pullback f) := by
  apply (galoisConnection f).toGaloisCoinsertion
  rintro S Z g ⟨g₁, hf, hg₁⟩
  rw [cancel_mono f] at hf
  rwa [← hf]
def galoisInsertionOfIsSplitEpi (f : Y ⟶ X) [IsSplitEpi f] :
    GaloisInsertion (Sieve.pushforward f) (Sieve.pullback f) := by
  apply (galoisConnection f).toGaloisInsertion
  intro S Z g hg
  exact ⟨g ≫ section_ f, by simpa⟩
theorem pullbackArrows_comm [HasPullbacks C] {X Y : C} (f : Y ⟶ X) (R : Presieve X) :
    Sieve.generate (R.pullbackArrows f) = (Sieve.generate R).pullback f := by
  ext W g
  constructor
  · rintro ⟨_, h, k, hk, rfl⟩
    cases' hk with W g hg
    change (Sieve.generate R).pullback f (h ≫ pullback.snd g f)
    rw [Sieve.pullback_apply, assoc, ← pullback.condition, ← assoc]
    exact Sieve.downward_closed _ (by exact Sieve.le_generate R W hg) (h ≫ pullback.fst g f)
  · rintro ⟨W, h, k, hk, comm⟩
    exact ⟨_, _, _, Presieve.pullbackArrows.mk _ _ hk, pullback.lift_snd _ _ comm⟩
section Functor
variable {E : Type u₃} [Category.{v₃} E] (G : D ⥤ E)
@[simps]
def functorPullback (R : Sieve (F.obj X)) : Sieve X where
  arrows := Presieve.functorPullback F R
  downward_closed := by
    intro _ _ f hf g
    unfold Presieve.functorPullback
    rw [F.map_comp]
    exact R.downward_closed hf (F.map g)
@[simp]
theorem functorPullback_arrows (R : Sieve (F.obj X)) :
    (R.functorPullback F).arrows = R.arrows.functorPullback F :=
  rfl
@[simp]
theorem functorPullback_id (R : Sieve X) : R.functorPullback (𝟭 _) = R := by
  ext
  rfl
theorem functorPullback_comp (R : Sieve ((F ⋙ G).obj X)) :
    R.functorPullback (F ⋙ G) = (R.functorPullback G).functorPullback F := by
  ext
  rfl
theorem functorPushforward_extend_eq {R : Presieve X} :
    (generate R).arrows.functorPushforward F = R.functorPushforward F := by
  funext Y
  ext f
  constructor
  · rintro ⟨X', g, f', ⟨X'', g', f'', h₁, rfl⟩, rfl⟩
    exact ⟨X'', f'', f' ≫ F.map g', h₁, by simp⟩
  · rintro ⟨X', g, f', h₁, h₂⟩
    exact ⟨X', g, f', le_generate R _ h₁, h₂⟩
@[simps]
def functorPushforward (R : Sieve X) : Sieve (F.obj X) where
  arrows := R.arrows.functorPushforward F
  downward_closed := by
    intro _ _ f h g
    obtain ⟨X, α, β, hα, rfl⟩ := h
    exact ⟨X, α, g ≫ β, hα, by simp⟩
@[simp]
theorem functorPushforward_id (R : Sieve X) : R.functorPushforward (𝟭 _) = R := by
  ext X f
  constructor
  · intro hf
    obtain ⟨X, g, h, hg, rfl⟩ := hf
    exact R.downward_closed hg h
  · intro hf
    exact ⟨X, f, 𝟙 _, hf, by simp⟩
theorem functorPushforward_comp (R : Sieve X) :
    R.functorPushforward (F ⋙ G) = (R.functorPushforward F).functorPushforward G := by
  ext
  simp [R.arrows.functorPushforward_comp F G]
theorem functor_galoisConnection (X : C) :
    GaloisConnection (Sieve.functorPushforward F : Sieve X → Sieve (F.obj X))
      (Sieve.functorPullback F) := by
  intro R S
  constructor
  · intro hle X f hf
    apply hle
    refine ⟨X, f, 𝟙 _, hf, ?_⟩
    rw [id_comp]
  · rintro hle Y f ⟨X, g, h, hg, rfl⟩
    apply Sieve.downward_closed S
    exact hle g hg
theorem functorPullback_monotone (X : C) :
    Monotone (Sieve.functorPullback F : Sieve (F.obj X) → Sieve X) :=
  (functor_galoisConnection F X).monotone_u
theorem functorPushforward_monotone (X : C) :
    Monotone (Sieve.functorPushforward F : Sieve X → Sieve (F.obj X)) :=
  (functor_galoisConnection F X).monotone_l
theorem le_functorPushforward_pullback (R : Sieve X) :
    R ≤ (R.functorPushforward F).functorPullback F :=
  (functor_galoisConnection F X).le_u_l _
theorem functorPullback_pushforward_le (R : Sieve (F.obj X)) :
    (R.functorPullback F).functorPushforward F ≤ R :=
  (functor_galoisConnection F X).l_u_le _
theorem functorPushforward_union (S R : Sieve X) :
    (S ⊔ R).functorPushforward F = S.functorPushforward F ⊔ R.functorPushforward F :=
  (functor_galoisConnection F X).l_sup
theorem functorPullback_union (S R : Sieve (F.obj X)) :
    (S ⊔ R).functorPullback F = S.functorPullback F ⊔ R.functorPullback F :=
  rfl
theorem functorPullback_inter (S R : Sieve (F.obj X)) :
    (S ⊓ R).functorPullback F = S.functorPullback F ⊓ R.functorPullback F :=
  rfl
@[simp]
theorem functorPushforward_bot (F : C ⥤ D) (X : C) : (⊥ : Sieve X).functorPushforward F = ⊥ :=
  (functor_galoisConnection F X).l_bot
@[simp]
theorem functorPushforward_top (F : C ⥤ D) (X : C) : (⊤ : Sieve X).functorPushforward F = ⊤ := by
  refine (generate_sieve _).symm.trans ?_
  apply generate_of_contains_isSplitEpi (𝟙 (F.obj X))
  exact ⟨X, 𝟙 _, 𝟙 _, trivial, by simp⟩
@[simp]
theorem functorPullback_bot (F : C ⥤ D) (X : C) : (⊥ : Sieve (F.obj X)).functorPullback F = ⊥ :=
  rfl
@[simp]
theorem functorPullback_top (F : C ⥤ D) (X : C) : (⊤ : Sieve (F.obj X)).functorPullback F = ⊤ :=
  rfl
theorem image_mem_functorPushforward (R : Sieve X) {V} {f : V ⟶ X} (h : R f) :
    R.functorPushforward F (F.map f) :=
  ⟨V, f, 𝟙 _, h, by simp⟩
def essSurjFullFunctorGaloisInsertion [F.EssSurj] [F.Full] (X : C) :
    GaloisInsertion (Sieve.functorPushforward F : Sieve X → Sieve (F.obj X))
      (Sieve.functorPullback F) := by
  apply (functor_galoisConnection F X).toGaloisInsertion
  intro S Y f hf
  refine ⟨_, F.preimage ((F.objObjPreimageIso Y).hom ≫ f), (F.objObjPreimageIso Y).inv, ?_⟩
  simpa using hf
def fullyFaithfulFunctorGaloisCoinsertion [F.Full] [F.Faithful] (X : C) :
    GaloisCoinsertion (Sieve.functorPushforward F : Sieve X → Sieve (F.obj X))
      (Sieve.functorPullback F) := by
  apply (functor_galoisConnection F X).toGaloisCoinsertion
  rintro S Y f ⟨Z, g, h, h₁, h₂⟩
  rw [← F.map_preimage h, ← F.map_comp] at h₂
  rw [F.map_injective h₂]
  exact S.downward_closed h₁ _
lemma functorPushforward_functor (S : Sieve X) (e : C ≌ D) :
    S.functorPushforward e.functor = (S.pullback (e.unitInv.app X)).functorPullback e.inverse := by
  ext Y iYX
  constructor
  · rintro ⟨Z, iZX, iYZ, hiZX, rfl⟩
    simpa using S.downward_closed hiZX (e.inverse.map iYZ ≫ e.unitInv.app Z)
  · intro H
    exact ⟨_, e.inverse.map iYX ≫ e.unitInv.app X, e.counitInv.app Y, by simpa using H, by simp⟩
@[simp]
lemma mem_functorPushforward_functor {Y : D} {S : Sieve X} {e : C ≌ D} {f : Y ⟶ e.functor.obj X} :
    S.functorPushforward e.functor f ↔ S (e.inverse.map f ≫ e.unitInv.app X) :=
  congr($(S.functorPushforward_functor e).arrows f)
lemma functorPushforward_inverse {X : D} (S : Sieve X) (e : C ≌ D) :
    S.functorPushforward e.inverse = (S.pullback (e.counit.app X)).functorPullback e.functor :=
  Sieve.functorPushforward_functor S e.symm
@[simp]
lemma mem_functorPushforward_inverse {X : D} {S : Sieve X} {e : C ≌ D} {f : Y ⟶ e.inverse.obj X} :
    S.functorPushforward e.inverse f ↔ S (e.functor.map f ≫ e.counit.app X) :=
  congr($(S.functorPushforward_inverse e).arrows f)
variable (e : C ≌ D)
lemma functorPushforward_equivalence_eq_pullback {U : C} (S : Sieve U) :
    Sieve.functorPushforward e.inverse (Sieve.functorPushforward e.functor S) =
      Sieve.pullback (e.unitInv.app U) S := by ext; simp
lemma pullback_functorPushforward_equivalence_eq {X : C} (S : Sieve X) :
    Sieve.pullback (e.unit.app X) (Sieve.functorPushforward e.inverse
      (Sieve.functorPushforward e.functor S)) = S := by ext; simp
lemma mem_functorPushforward_iff_of_full [F.Full] {X Y : C} (R : Sieve X) (f : F.obj Y ⟶ F.obj X) :
    (R.arrows.functorPushforward F) f ↔ ∃ (g : Y ⟶ X), F.map g = f ∧ R g := by
  refine ⟨fun ⟨Z, g, h, hg, hcomp⟩ ↦ ?_, fun ⟨g, hcomp, hg⟩ ↦ ?_⟩
  · obtain ⟨h', hh'⟩ := F.map_surjective h
    use h' ≫ g
    simp only [Functor.map_comp, hh', hcomp, true_and]
    apply R.downward_closed hg
  · use Y, g, 𝟙 _, hg
    simp [hcomp]
lemma mem_functorPushforward_iff_of_full_of_faithful [F.Full] [F.Faithful]
    {X Y : C} (R : Sieve X) (f : Y ⟶ X) :
    (R.arrows.functorPushforward F) (F.map f) ↔ R f := by
  rw [Sieve.mem_functorPushforward_iff_of_full]
  refine ⟨fun ⟨g, hcomp, hg⟩ ↦ ?_, fun hf ↦ ⟨f, rfl, hf⟩⟩
  rwa [← F.map_injective hcomp]
end Functor
@[simps]
def functor (S : Sieve X) : Cᵒᵖ ⥤ Type v₁ where
  obj Y := { g : Y.unop ⟶ X // S g }
  map f g := ⟨f.unop ≫ g.1, downward_closed _ g.2 _⟩
@[simps]
def natTransOfLe {S T : Sieve X} (h : S ≤ T) : S.functor ⟶ T.functor where app _ f := ⟨f.1, h _ f.2⟩
@[simps]
def functorInclusion (S : Sieve X) : S.functor ⟶ yoneda.obj X where app _ f := f.1
theorem natTransOfLe_comm {S T : Sieve X} (h : S ≤ T) :
    natTransOfLe h ≫ functorInclusion _ = functorInclusion _ :=
  rfl
instance functorInclusion_is_mono : Mono S.functorInclusion :=
  ⟨fun f g h => by
    ext Y y
    simpa [Subtype.ext_iff_val] using congr_fun (NatTrans.congr_app h Y) y⟩
@[simps]
def sieveOfSubfunctor {R} (f : R ⟶ yoneda.obj X) : Sieve X where
  arrows Y g := ∃ t, f.app (Opposite.op Y) t = g
  downward_closed := by
    rintro Y Z _ ⟨t, rfl⟩ g
    refine ⟨R.map g.op t, ?_⟩
    rw [FunctorToTypes.naturality _ _ f]
    simp
theorem sieveOfSubfunctor_functorInclusion : sieveOfSubfunctor S.functorInclusion = S := by
  ext
  simp only [functorInclusion_app, sieveOfSubfunctor_apply]
  constructor
  · rintro ⟨⟨f, hf⟩, rfl⟩
    exact hf
  · intro hf
    exact ⟨⟨_, hf⟩, rfl⟩
instance functorInclusion_top_isIso : IsIso (⊤ : Sieve X).functorInclusion :=
  ⟨⟨{ app := fun _ a => ⟨a, ⟨⟩⟩ }, rfl, rfl⟩⟩
end Sieve
end CategoryTheory