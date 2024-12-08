import Mathlib.Data.List.Chain
import Mathlib.CategoryTheory.IsConnected
import Mathlib.CategoryTheory.Sigma.Basic
import Mathlib.CategoryTheory.FullSubcategory
universe v₁ v₂ v₃ u₁ u₂
noncomputable section
open CategoryTheory.Category
namespace CategoryTheory
attribute [instance 100] IsConnected.is_nonempty
variable {J : Type u₁} [Category.{v₁} J]
def ConnectedComponents (J : Type u₁) [Category.{v₁} J] : Type u₁ :=
  Quotient (Zigzag.setoid J)
def Functor.mapConnectedComponents {K : Type u₂} [Category.{v₂} K] (F : J ⥤ K)
    (x : ConnectedComponents J) : ConnectedComponents K :=
  x |> Quotient.lift (Quotient.mk (Zigzag.setoid _) ∘ F.obj)
    (fun _ _ ↦ Quot.sound ∘ zigzag_obj_of_zigzag F)
@[simp]
lemma Functor.mapConnectedComponents_mk {K : Type u₂} [Category.{v₂} K] (F : J ⥤ K) (j : J) :
    F.mapConnectedComponents (Quotient.mk _ j) = Quotient.mk _ (F.obj j) := rfl
instance [Inhabited J] : Inhabited (ConnectedComponents J) :=
  ⟨Quotient.mk'' default⟩
def ConnectedComponents.functorToDiscrete   (X : Type*)
    (f : ConnectedComponents J → X) : J ⥤ Discrete X where
  obj Y :=  Discrete.mk (f (Quotient.mk (Zigzag.setoid _) Y))
  map g := Discrete.eqToHom (congrArg f (Quotient.sound (Zigzag.of_hom g)))
def ConnectedComponents.liftFunctor (J) [Category J] {X : Type*} (F :J ⥤ Discrete X) :
    (ConnectedComponents J → X) :=
  Quotient.lift (fun c => (F.obj c).as)
    (fun _ _ h => eq_of_zigzag X (zigzag_obj_of_zigzag F h))
def ConnectedComponents.typeToCatHomEquiv (J) [Category J] (X : Type*) :
    (ConnectedComponents J → X) ≃ (J ⥤ Discrete X)   where
  toFun := ConnectedComponents.functorToDiscrete _
  invFun := ConnectedComponents.liftFunctor _
  left_inv := fun f ↦ funext fun x ↦ by
    obtain ⟨x, h⟩ := Quotient.exists_rep x
    rw [← h]
    rfl
  right_inv  := fun fctr ↦
    Functor.hext (fun _ ↦ rfl) (fun c d f ↦
      have : Subsingleton (fctr.obj c ⟶ fctr.obj d) := Discrete.instSubsingletonDiscreteHom _ _
      (Subsingleton.elim (fctr.map f) _).symm.heq)
def Component (j : ConnectedComponents J) : Type u₁ :=
  FullSubcategory fun k => Quotient.mk'' k = j
instance {j : ConnectedComponents J} : Category (Component j) :=
  FullSubcategory.category _
@[simps!]
def Component.ι (j : ConnectedComponents J) : Component j ⥤ J :=
  fullSubcategoryInclusion _
instance {j : ConnectedComponents J} : Functor.Full (Component.ι j) :=
  FullSubcategory.full _
instance {j : ConnectedComponents J} : Functor.Faithful (Component.ι j) :=
  FullSubcategory.faithful _
instance (j : ConnectedComponents J) : Nonempty (Component j) := by
  induction j using Quotient.inductionOn'
  exact ⟨⟨_, rfl⟩⟩
instance (j : ConnectedComponents J) : Inhabited (Component j) :=
  Classical.inhabited_of_nonempty'
instance (j : ConnectedComponents J) : IsConnected (Component j) := by
  apply isConnected_of_zigzag
  rintro ⟨j₁, hj₁⟩ ⟨j₂, rfl⟩
  have h₁₂ : Zigzag j₁ j₂ := Quotient.exact' hj₁
  rcases List.exists_chain_of_relationReflTransGen h₁₂ with ⟨l, hl₁, hl₂⟩
  let f : ∀ x, Zigzag x j₂ → Component (Quotient.mk'' j₂) := fun x h => ⟨x, Quotient.sound' h⟩
  have hf : ∀ a : J, a ∈ l → Zigzag a j₂ := by
    intro i hi
    apply hl₁.backwards_induction (fun t => Zigzag t j₂) _ hl₂ _ _ _ (List.mem_of_mem_tail hi)
    · intro j k
      apply Relation.ReflTransGen.head
    · apply Relation.ReflTransGen.refl
  refine ⟨l.pmap f hf, ?_, ?_⟩
  · refine @List.chain_pmap_of_chain _ _ _ _ _ f (fun x y _ _ h => ?_) _ _ hl₁ h₁₂ _
    exact zag_of_zag_obj (Component.ι _) h
  · erw [List.getLast_pmap f (j₁ :: l) (by simpa [h₁₂] using hf) (List.cons_ne_nil _ _)]
    exact FullSubcategory.ext hl₂
abbrev Decomposed (J : Type u₁) [Category.{v₁} J] :=
  Σj : ConnectedComponents J, Component j
abbrev inclusion (j : ConnectedComponents J) : Component j ⥤ Decomposed J :=
  Sigma.incl _
@[simps!]
def decomposedTo (J : Type u₁) [Category.{v₁} J] : Decomposed J ⥤ J :=
  Sigma.desc Component.ι
@[simp]
theorem inclusion_comp_decomposedTo (j : ConnectedComponents J) :
    inclusion j ⋙ decomposedTo J = Component.ι j :=
  rfl
instance : (decomposedTo J).Full where
  map_surjective := by
    rintro ⟨j', X, hX⟩ ⟨k', Y, hY⟩ f
    dsimp at f
    have : j' = k' := by
      rw [← hX, ← hY, Quotient.eq'']
      exact Relation.ReflTransGen.single (Or.inl ⟨f⟩)
    subst this
    exact ⟨Sigma.SigmaHom.mk f, rfl⟩
instance : (decomposedTo J).Faithful where
  map_injective := by
    rintro ⟨_, j, rfl⟩ ⟨_, k, hY⟩ ⟨f⟩ ⟨_⟩ rfl
    rfl
instance : (decomposedTo J).EssSurj where mem_essImage j := ⟨⟨_, j, rfl⟩, ⟨Iso.refl _⟩⟩
instance : (decomposedTo J).IsEquivalence where
@[simps! functor]
def decomposedEquiv : Decomposed J ≌ J :=
  (decomposedTo J).asEquivalence
end CategoryTheory