import Mathlib.Algebra.CharZero.Infinite
import Mathlib.Data.Rat.Encodable
import Mathlib.ModelTheory.Complexity
import Mathlib.ModelTheory.Fraisse
import Mathlib.Order.CountableDenseLinearOrder
universe u v w w'
namespace FirstOrder
namespace Language
open FirstOrder Structure
variable {L : Language.{u, v}} {α : Type w} {M : Type w'} {n : ℕ}
inductive orderRel : ℕ → Type
  | le : orderRel 2
  deriving DecidableEq
protected def order : Language := ⟨fun _ => Empty, orderRel⟩
  deriving IsRelational
namespace order
@[simp]
lemma forall_relations {P : ∀ (n) (_ : Language.order.Relations n), Prop} :
    (∀ {n} (R), P n R) ↔ P 2 .le := ⟨fun h => h _, fun h n R =>
      match n, R with
      | 2, .le => h⟩
instance instSubsingleton : Subsingleton (Language.order.Relations n) :=
  ⟨by rintro ⟨⟩ ⟨⟩; rfl⟩
instance : IsEmpty (Language.order.Relations 0) := ⟨fun x => by cases x⟩
instance : Unique (Σ n, Language.order.Relations n) :=
  ⟨⟨⟨2, .le⟩⟩, fun ⟨n, R⟩ =>
      match n, R with
      | 2, .le => rfl⟩
instance : Unique Language.order.Symbols := ⟨⟨Sum.inr default⟩, by
  have : IsEmpty (Σ n, Language.order.Functions n) := isEmpty_sigma.2 inferInstance
  simp only [Symbols, Sum.forall, reduceCtorEq, Sum.inr.injEq, IsEmpty.forall_iff, true_and]
  exact Unique.eq_default⟩
@[simp]
lemma card_eq_one : Language.order.card = 1 := by simp [card]
end order
class IsOrdered (L : Language.{u, v}) where
  leSymb : L.Relations 2
export IsOrdered (leSymb)
instance : IsOrdered Language.order :=
  ⟨.le⟩
lemma order.relation_eq_leSymb : (R : Language.order.Relations 2) → R = leSymb
  | .le => rfl
section IsOrdered
variable [IsOrdered L]
def Term.le (t₁ t₂ : L.Term (α ⊕ (Fin n))) : L.BoundedFormula α n :=
  leSymb.boundedFormula₂ t₁ t₂
def Term.lt (t₁ t₂ : L.Term (α ⊕ (Fin n))) : L.BoundedFormula α n :=
  t₁.le t₂ ⊓ ∼(t₂.le t₁)
variable (L)
@[simps] def orderLHom : Language.order →ᴸ L where
  onRelation | _, .le => leSymb
@[simp]
theorem orderLHom_leSymb :
    (orderLHom L).onRelation leSymb = (leSymb : L.Relations 2) :=
  rfl
@[simp]
theorem orderLHom_order : orderLHom Language.order = LHom.id Language.order :=
  LHom.funext (Subsingleton.elim _ _) (Subsingleton.elim _ _)
def preorderTheory : L.Theory :=
  {leSymb.reflexive, leSymb.transitive}
instance : Theory.IsUniversal L.preorderTheory := ⟨by
  simp only [preorderTheory, Set.mem_insert_iff, Set.mem_singleton_iff, forall_eq_or_imp, forall_eq]
  exact ⟨leSymb.isUniversal_reflexive, leSymb.isUniversal_transitive⟩⟩
def partialOrderTheory : L.Theory :=
  insert leSymb.antisymmetric L.preorderTheory
instance : Theory.IsUniversal L.partialOrderTheory :=
  Theory.IsUniversal.insert leSymb.isUniversal_antisymmetric
def linearOrderTheory : L.Theory :=
  insert leSymb.total L.partialOrderTheory
instance : Theory.IsUniversal L.linearOrderTheory :=
  Theory.IsUniversal.insert leSymb.isUniversal_total
example [L.Structure M] [M ⊨ L.linearOrderTheory] (S : L.Substructure M) :
    S ⊨ L.linearOrderTheory := inferInstance
def noTopOrderSentence : L.Sentence :=
  ∀'∃'∼((&1).le &0)
def noBotOrderSentence : L.Sentence :=
  ∀'∃'∼((&0).le &1)
def denselyOrderedSentence : L.Sentence :=
  ∀'∀'((&0).lt &1 ⟹ ∃'((&0).lt &2 ⊓ (&2).lt &1))
def dlo : L.Theory :=
  L.linearOrderTheory ∪ {L.noTopOrderSentence, L.noBotOrderSentence, L.denselyOrderedSentence}
variable [L.Structure M]
instance [h : M ⊨ L.dlo] : M ⊨ L.linearOrderTheory := h.mono Set.subset_union_left
instance [h : M ⊨ L.linearOrderTheory] : M ⊨ L.partialOrderTheory := h.mono (Set.subset_insert _ _)
instance [h : M ⊨ L.partialOrderTheory] : M ⊨ L.preorderTheory := h.mono (Set.subset_insert _ _)
end IsOrdered
instance sum.instIsOrdered : IsOrdered (L.sum Language.order) :=
  ⟨Sum.inr IsOrdered.leSymb⟩
variable (L M)
def orderStructure [LE M] : Language.order.Structure M where
  RelMap | .le => (fun x => x 0 ≤ x 1)
class OrderedStructure [L.IsOrdered] [LE M] [L.Structure M] : Prop where
  relMap_leSymb : ∀ (x : Fin 2 → M), RelMap (leSymb : L.Relations 2) x ↔ (x 0 ≤ x 1)
export OrderedStructure (relMap_leSymb)
attribute [simp] relMap_leSymb
variable {L M}
section order_to_structure
variable [IsOrdered L] [L.Structure M]
section LE
variable [LE M]
instance [Language.order.Structure M] [Language.order.OrderedStructure M]
    [(orderLHom L).IsExpansionOn M] : L.OrderedStructure M where
  relMap_leSymb x := by
    rw [← orderLHom_leSymb L, LHom.IsExpansionOn.map_onRelation, relMap_leSymb]
variable [L.OrderedStructure M]
instance [Language.order.Structure M] [Language.order.OrderedStructure M] :
    LHom.IsExpansionOn (orderLHom L) M where
  map_onRelation := by simp [order.relation_eq_leSymb]
instance (S : L.Substructure M) : L.OrderedStructure S := ⟨fun x => relMap_leSymb (S.subtype ∘ x)⟩
@[simp]
theorem Term.realize_le {t₁ t₂ : L.Term (α ⊕ (Fin n))} {v : α → M}
    {xs : Fin n → M} :
    (t₁.le t₂).Realize v xs ↔ t₁.realize (Sum.elim v xs) ≤ t₂.realize (Sum.elim v xs) := by
  simp [Term.le]
theorem realize_noTopOrder_iff : M ⊨ L.noTopOrderSentence ↔ NoTopOrder M := by
  simp only [noTopOrderSentence, Sentence.Realize, Formula.Realize, BoundedFormula.realize_all,
    BoundedFormula.realize_ex, BoundedFormula.realize_not, Term.realize, Term.realize_le,
    Sum.elim_inr]
  refine ⟨fun h => ⟨fun a => h a⟩, ?_⟩
  intro h a
  exact exists_not_le a
theorem realize_noBotOrder_iff : M ⊨ L.noBotOrderSentence ↔ NoBotOrder M := by
  simp only [noBotOrderSentence, Sentence.Realize, Formula.Realize, BoundedFormula.realize_all,
    BoundedFormula.realize_ex, BoundedFormula.realize_not, Term.realize, Term.realize_le,
    Sum.elim_inr]
  refine ⟨fun h => ⟨fun a => h a⟩, ?_⟩
  intro h a
  exact exists_not_ge a
variable (L M)
@[simp]
theorem realize_noTopOrder [h : NoTopOrder M] : M ⊨ L.noTopOrderSentence :=
  realize_noTopOrder_iff.2 h
@[simp]
theorem realize_noBotOrder [h : NoBotOrder M] : M ⊨ L.noBotOrderSentence :=
  realize_noBotOrder_iff.2 h
theorem noTopOrder_of_dlo [M ⊨ L.dlo] : NoTopOrder M :=
  realize_noTopOrder_iff.1 (L.dlo.realize_sentence_of_mem (by
    simp only [dlo, Set.union_insert, Set.union_singleton, Set.mem_insert_iff, true_or]))
theorem noBotOrder_of_dlo [M ⊨ L.dlo] : NoBotOrder M :=
  realize_noBotOrder_iff.1 (L.dlo.realize_sentence_of_mem (by
    simp only [dlo, Set.union_insert, Set.union_singleton, Set.mem_insert_iff, true_or, or_true]))
end LE
@[simp]
theorem orderedStructure_iff
    [LE M] [Language.order.Structure M] [Language.order.OrderedStructure M] :
    L.OrderedStructure M ↔ LHom.IsExpansionOn (orderLHom L) M :=
  ⟨fun _ => inferInstance, fun _ => inferInstance⟩
section Preorder
variable [Preorder M] [L.OrderedStructure M]
instance model_preorder : M ⊨ L.preorderTheory := by
  simp only [preorderTheory, Theory.model_insert_iff, Relations.realize_reflexive, relMap_leSymb,
    Theory.model_singleton_iff, Relations.realize_transitive]
  exact ⟨le_refl, fun _ _ _ => le_trans⟩
@[simp]
theorem Term.realize_lt {t₁ t₂ : L.Term (α ⊕ (Fin n))}
    {v : α → M} {xs : Fin n → M} :
    (t₁.lt t₂).Realize v xs ↔ t₁.realize (Sum.elim v xs) < t₂.realize (Sum.elim v xs) := by
  simp [Term.lt, lt_iff_le_not_le]
theorem realize_denselyOrdered_iff :
    M ⊨ L.denselyOrderedSentence ↔ DenselyOrdered M := by
  simp only [denselyOrderedSentence, Sentence.Realize, Formula.Realize,
    BoundedFormula.realize_imp, BoundedFormula.realize_all, Term.realize, Term.realize_lt,
    Sum.elim_inr, BoundedFormula.realize_ex, BoundedFormula.realize_inf]
  refine ⟨fun h => ⟨fun a b ab => h a b ab⟩, ?_⟩
  intro h a b ab
  exact exists_between ab
@[simp]
theorem realize_denselyOrdered [h : DenselyOrdered M] :
    M ⊨ L.denselyOrderedSentence :=
  realize_denselyOrdered_iff.2 h
variable (L) (M)
theorem denselyOrdered_of_dlo [M ⊨ L.dlo] : DenselyOrdered M :=
  realize_denselyOrdered_iff.1 (L.dlo.realize_sentence_of_mem (by
    simp only [dlo, Set.union_insert, Set.union_singleton, Set.mem_insert_iff, true_or, or_true]))
end Preorder
instance model_partialOrder [PartialOrder M] [L.OrderedStructure M] :
    M ⊨ L.partialOrderTheory := by
  simp only [partialOrderTheory, Theory.model_insert_iff, Relations.realize_antisymmetric,
    relMap_leSymb, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    model_preorder, and_true]
  exact fun _ _ => le_antisymm
section LinearOrder
variable [LinearOrder M] [L.OrderedStructure M]
instance model_linearOrder : M ⊨ L.linearOrderTheory := by
  simp only [linearOrderTheory, Theory.model_insert_iff, Relations.realize_total, relMap_leSymb,
    Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, model_partialOrder,
    and_true]
  exact le_total
instance model_dlo [DenselyOrdered M] [NoTopOrder M] [NoBotOrder M] :
    M ⊨ L.dlo := by
  simp [dlo, model_linearOrder, Theory.model_insert_iff]
end LinearOrder
end order_to_structure
section structure_to_order
variable (L) [IsOrdered L] (M) [L.Structure M]
def leOfStructure : LE M where
  le a b := Structure.RelMap (leSymb : L.Relations 2) ![a,b]
instance : @OrderedStructure L M _ (L.leOfStructure M) _ := by
  letI := L.leOfStructure M
  constructor
  simp only [Fin.forall_fin_succ_pi, Fin.cons_zero, Fin.forall_fin_zero_pi]
  intros
  rfl
@[local instance]
def decidableLEOfStructure
    [h : DecidableRel (fun (a b : M) => Structure.RelMap (leSymb : L.Relations 2) ![a,b])] :
    letI := L.leOfStructure M
    DecidableRel ((· : M) ≤ ·) := h
def preorderOfModels [h : M ⊨ L.preorderTheory] : Preorder M where
  __ := L.leOfStructure M
  le_refl := Relations.realize_reflexive.1 ((Theory.model_iff _).1 h _
    (by simp only [preorderTheory, Set.mem_insert_iff, Set.mem_singleton_iff, true_or]))
  le_trans := Relations.realize_transitive.1 ((Theory.model_iff _).1 h _
    (by simp only [preorderTheory, Set.mem_insert_iff, Set.mem_singleton_iff, or_true]))
def partialOrderOfModels [h : M ⊨ L.partialOrderTheory] : PartialOrder M where
  __ := L.preorderOfModels M
  le_antisymm := Relations.realize_antisymmetric.1 ((Theory.model_iff _).1 h _
    (by simp only [partialOrderTheory, Set.mem_insert_iff, Set.mem_singleton_iff, true_or]))
def linearOrderOfModels [h : M ⊨ L.linearOrderTheory]
    [DecidableRel (fun (a b : M) => Structure.RelMap (leSymb : L.Relations 2) ![a,b])] :
    LinearOrder M where
  __ := L.partialOrderOfModels M
  le_total := Relations.realize_total.1 ((Theory.model_iff _).1 h _
    (by simp only [linearOrderTheory, Set.mem_insert_iff, Set.mem_singleton_iff, true_or]))
  decidableLE := inferInstance
end structure_to_order
namespace order
variable [Language.order.Structure M] [LE M] [Language.order.OrderedStructure M]
  {N : Type*} [Language.order.Structure N] [LE N] [Language.order.OrderedStructure N]
  {F : Type*}
instance [FunLike F M N] [OrderHomClass F M N] : Language.order.HomClass F M N :=
  ⟨fun _ => isEmptyElim, by
    simp only [forall_relations, relation_eq_leSymb, relMap_leSymb, Fin.isValue,
      Function.comp_apply]
    exact fun φ x => map_rel φ⟩
instance : Language.order.StrongHomClass (M ↪o N) M N :=
  ⟨fun _ => isEmptyElim,
    by simp only [order.forall_relations, order.relation_eq_leSymb, relMap_leSymb, Fin.isValue,
    Function.comp_apply, RelEmbedding.map_rel_iff, implies_true]⟩
instance [EquivLike F M N] [OrderIsoClass F M N] : Language.order.StrongHomClass F M N :=
  ⟨fun _ => isEmptyElim,
    by simp only [order.forall_relations, order.relation_eq_leSymb, relMap_leSymb, Fin.isValue,
      Function.comp_apply, map_le_map_iff, implies_true]⟩
end order
namespace HomClass
variable [L.IsOrdered] [L.Structure M] {N : Type*} [L.Structure N]
  {F : Type*} [FunLike F M N] [L.HomClass F M N]
lemma monotone [Preorder M] [L.OrderedStructure M] [Preorder N] [L.OrderedStructure N] (f : F) :
    Monotone f := fun a b => by
  have h := HomClass.map_rel f leSymb ![a,b]
  simp only [relMap_leSymb, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Function.comp_apply] at h
  exact h
lemma strictMono [EmbeddingLike F M N] [PartialOrder M] [L.OrderedStructure M]
    [PartialOrder N] [L.OrderedStructure N] (f : F) :
    StrictMono f :=
  (HomClass.monotone f).strictMono_of_injective (EmbeddingLike.injective f)
end HomClass
lemma StrongHomClass.toOrderIsoClass
    (L : Language) [L.IsOrdered] (M : Type*) [L.Structure M] [LE M] [L.OrderedStructure M]
    (N : Type*) [L.Structure N] [LE N] [L.OrderedStructure N]
    (F : Type*) [EquivLike F M N] [L.StrongHomClass F M N] :
    OrderIsoClass F M N where
  map_le_map_iff f a b := by
    have h := StrongHomClass.map_rel f leSymb ![a,b]
    simp only [relMap_leSymb, Fin.isValue, Function.comp_apply, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons] at h
    exact h
section Fraisse
variable (M)
lemma dlo_isExtensionPair
    (M : Type w) [Language.order.Structure M] [M ⊨ Language.order.linearOrderTheory]
    (N : Type w') [Language.order.Structure N] [N ⊨ Language.order.dlo] [Nonempty N] :
    Language.order.IsExtensionPair M N := by
  classical
  rw [isExtensionPair_iff_exists_embedding_closure_singleton_sup]
  intro S S_fg f m
  letI := Language.order.linearOrderOfModels M
  letI := Language.order.linearOrderOfModels N
  have := Language.order.denselyOrdered_of_dlo N
  have := Language.order.noBotOrder_of_dlo N
  have := Language.order.noTopOrder_of_dlo N
  have := NoBotOrder.to_noMinOrder N
  have := NoTopOrder.to_noMaxOrder N
  have hS : Set.Finite (S : Set M) := (S.fg_iff_structure_fg.1 S_fg).finite
  obtain ⟨g, hg⟩ := Order.exists_orderEmbedding_insert hS.toFinset
    ((OrderIso.setCongr hS.toFinset (S : Set M) hS.coe_toFinset).toOrderEmbedding.trans
      (OrderEmbedding.ofStrictMono f (HomClass.strictMono f))) m
  let g' :
    ((Substructure.closure Language.order).toFun {m} ⊔ S : Language.order.Substructure M) ↪o N :=
    ((OrderIso.setCongr _ _ (by
      convert LowerAdjoint.closure_eq_self_of_mem_closed _
        (Substructure.mem_closed_of_isRelational Language.order
        ((insert m hS.toFinset : Finset M) : Set M))
      simp only [Finset.coe_insert, Set.Finite.coe_toFinset, Substructure.closure_insert,
        Substructure.closure_eq])).toOrderEmbedding.trans g)
  use StrongHomClass.toEmbedding g'
  ext ⟨x, xS⟩
  refine congr_fun hg.symm ⟨x, (?_ : x ∈ hS.toFinset)⟩
  simp only [Set.Finite.mem_toFinset, SetLike.mem_coe, xS]
instance (M : Type w) [Language.order.Structure M] [M ⊨ Language.order.dlo] [Nonempty M] :
    Infinite M := by
  letI := orderStructure ℚ
  obtain ⟨f, _⟩ := embedding_from_cg cg_of_countable default (dlo_isExtensionPair ℚ M)
  exact Infinite.of_injective f f.injective
lemma dlo_age [Language.order.Structure M] [Mdlo : M ⊨ Language.order.dlo] [Nonempty M] :
    Language.order.age M = {M : CategoryTheory.Bundled.{w'} Language.order.Structure |
      Finite M ∧ M ⊨ Language.order.linearOrderTheory} := by
  classical
  rw [age]
  ext N
  refine ⟨fun ⟨hF, h⟩ => ⟨hF.finite, Theory.IsUniversal.models_of_embedding h.some⟩,
    fun ⟨hF, h⟩ => ⟨FG.of_finite, ?_⟩⟩
  letI := Language.order.linearOrderOfModels M
  letI := Language.order.linearOrderOfModels N
  exact ⟨StrongHomClass.toEmbedding (nonempty_orderEmbedding_of_finite_infinite N M).some⟩
theorem isFraisseLimit_of_countable_nonempty_dlo (M : Type w)
    [Language.order.Structure M] [Countable M] [Nonempty M] [M ⊨ Language.order.dlo] :
    IsFraisseLimit {M : CategoryTheory.Bundled.{w} Language.order.Structure |
      Finite M ∧ M ⊨ Language.order.linearOrderTheory} M :=
  ⟨(isUltrahomogeneous_iff_IsExtensionPair cg_of_countable).2 (dlo_isExtensionPair M M), dlo_age M⟩
theorem isFraisse_finite_linear_order :
    IsFraisse {M : CategoryTheory.Bundled.{0} Language.order.Structure |
      Finite M ∧ M ⊨ Language.order.linearOrderTheory} := by
  letI : Language.order.Structure ℚ := orderStructure _
  exact (isFraisseLimit_of_countable_nonempty_dlo ℚ).isFraisse
open Cardinal
theorem aleph0_categorical_dlo : (ℵ₀).Categorical Language.order.dlo := fun M₁ M₂ h₁ h₂ => by
  obtain ⟨_⟩ := denumerable_iff.2 h₁
  obtain ⟨_⟩ := denumerable_iff.2 h₂
  exact (isFraisseLimit_of_countable_nonempty_dlo M₁).nonempty_equiv
    (isFraisseLimit_of_countable_nonempty_dlo M₂)
theorem dlo_isComplete : Language.order.dlo.IsComplete :=
  aleph0_categorical_dlo.{0}.isComplete ℵ₀ _ le_rfl (by simp [one_le_aleph0])
    ⟨by
      letI : Language.order.Structure ℚ := orderStructure ℚ
      exact Theory.ModelType.of _ ℚ⟩
    fun _ => inferInstance
end Fraisse
end Language
end FirstOrder
namespace Order
open FirstOrder FirstOrder.Language
example (α β : Type w') [LinearOrder α] [LinearOrder β]
    [Countable α] [DenselyOrdered α] [NoMinOrder α] [NoMaxOrder α]
    [Nonempty α] [Countable β] [DenselyOrdered β] [NoMinOrder β] [NoMaxOrder β] [Nonempty β] :
    Nonempty (α ≃o β) := by
  letI := orderStructure α
  letI := orderStructure β
  letI := StrongHomClass.toOrderIsoClass Language.order α β (α ≃[Language.order] β)
  exact ⟨(IsFraisseLimit.nonempty_equiv (isFraisseLimit_of_countable_nonempty_dlo α)
    (isFraisseLimit_of_countable_nonempty_dlo β)).some⟩
end Order