import Mathlib.Combinatorics.SimpleGraph.Dart
import Mathlib.Data.FunLike.Fintype
import Mathlib.Logic.Embedding.Set
open Function
namespace SimpleGraph
variable {V W X : Type*} (G : SimpleGraph V) (G' : SimpleGraph W) {u v : V}
protected def map (f : V ↪ W) (G : SimpleGraph V) : SimpleGraph W where
  Adj := Relation.Map G.Adj f f
  symm a b := by 
    rintro ⟨v, w, h, rfl, rfl⟩
    use w, v, h.symm, rfl
  loopless a := by 
    rintro ⟨v, w, h, rfl, h'⟩
    exact h.ne (f.injective h'.symm)
instance instDecidableMapAdj {f : V ↪ W} {a b} [Decidable (Relation.Map G.Adj f f a b)] :
    Decidable ((G.map f).Adj a b) := ‹Decidable (Relation.Map G.Adj f f a b)›
@[simp]
theorem map_adj (f : V ↪ W) (G : SimpleGraph V) (u v : W) :
    (G.map f).Adj u v ↔ ∃ u' v' : V, G.Adj u' v' ∧ f u' = u ∧ f v' = v :=
  Iff.rfl
lemma map_adj_apply {G : SimpleGraph V} {f : V ↪ W} {a b : V} :
    (G.map f).Adj (f a) (f b) ↔ G.Adj a b := by simp
theorem map_monotone (f : V ↪ W) : Monotone (SimpleGraph.map f) := by
  rintro G G' h _ _ ⟨u, v, ha, rfl, rfl⟩
  exact ⟨_, _, h ha, rfl, rfl⟩
@[simp] lemma map_id : G.map (Function.Embedding.refl _) = G :=
  SimpleGraph.ext <| Relation.map_id_id _
@[simp] lemma map_map (f : V ↪ W) (g : W ↪ X) : (G.map f).map g = G.map (f.trans g) :=
  SimpleGraph.ext <| Relation.map_map _ _ _ _ _
protected def comap (f : V → W) (G : SimpleGraph W) : SimpleGraph V where
  Adj u v := G.Adj (f u) (f v)
  symm _ _ h := h.symm
  loopless _ := G.loopless _
@[simp] lemma comap_adj {G : SimpleGraph W} {f : V → W} :
    (G.comap f).Adj u v ↔ G.Adj (f u) (f v) := Iff.rfl
@[simp] lemma comap_id {G : SimpleGraph V} : G.comap id = G := SimpleGraph.ext rfl
@[simp] lemma comap_comap {G : SimpleGraph X} (f : V → W) (g : W → X) :
  (G.comap g).comap f = G.comap (g ∘ f) := rfl
instance instDecidableComapAdj (f : V → W) (G : SimpleGraph W) [DecidableRel G.Adj] :
    DecidableRel (G.comap f).Adj := fun _ _ ↦ ‹DecidableRel G.Adj› _ _
lemma comap_symm (G : SimpleGraph V) (e : V ≃ W) :
    G.comap e.symm.toEmbedding = G.map e.toEmbedding := by
  ext; simp only [Equiv.apply_eq_iff_eq_symm_apply, comap_adj, map_adj, Equiv.toEmbedding_apply,
    exists_eq_right_right, exists_eq_right]
lemma map_symm (G : SimpleGraph W) (e : V ≃ W) :
    G.map e.symm.toEmbedding = G.comap e.toEmbedding := by rw [← comap_symm, e.symm_symm]
theorem comap_monotone (f : V ↪ W) : Monotone (SimpleGraph.comap f) := by
  intro G G' h _ _ ha
  exact h ha
@[simp]
theorem comap_map_eq (f : V ↪ W) (G : SimpleGraph V) : (G.map f).comap f = G := by
  ext
  simp
theorem leftInverse_comap_map (f : V ↪ W) :
    Function.LeftInverse (SimpleGraph.comap f) (SimpleGraph.map f) :=
  comap_map_eq f
theorem map_injective (f : V ↪ W) : Function.Injective (SimpleGraph.map f) :=
  (leftInverse_comap_map f).injective
theorem comap_surjective (f : V ↪ W) : Function.Surjective (SimpleGraph.comap f) :=
  (leftInverse_comap_map f).surjective
theorem map_le_iff_le_comap (f : V ↪ W) (G : SimpleGraph V) (G' : SimpleGraph W) :
    G.map f ≤ G' ↔ G ≤ G'.comap f :=
  ⟨fun h _ _ ha => h ⟨_, _, ha, rfl, rfl⟩, by
    rintro h _ _ ⟨u, v, ha, rfl, rfl⟩
    exact h ha⟩
theorem map_comap_le (f : V ↪ W) (G : SimpleGraph W) : (G.comap f).map f ≤ G := by
  rw [map_le_iff_le_comap]
lemma le_comap_of_subsingleton (f : V → W) [Subsingleton V] : G ≤ G'.comap f := by
  intros v w; simp [Subsingleton.elim v w]
lemma map_le_of_subsingleton (f : V ↪ W) [Subsingleton V] : G.map f ≤ G' := by
  rw [map_le_iff_le_comap]; apply le_comap_of_subsingleton
abbrev completeMultipartiteGraph {ι : Type*} (V : ι → Type*) : SimpleGraph (Σ i, V i) :=
  SimpleGraph.comap Sigma.fst ⊤
@[simps apply]
protected def _root_.Equiv.simpleGraph (e : V ≃ W) : SimpleGraph V ≃ SimpleGraph W where
  toFun := SimpleGraph.comap e.symm
  invFun := SimpleGraph.comap e
  left_inv _ := by simp
  right_inv _ := by simp
@[simp] lemma _root_.Equiv.simpleGraph_refl : (Equiv.refl V).simpleGraph = Equiv.refl _ := by
  ext; rfl
@[simp] lemma _root_.Equiv.simpleGraph_trans (e₁ : V ≃ W) (e₂ : W ≃ X) :
  (e₁.trans e₂).simpleGraph = e₁.simpleGraph.trans e₂.simpleGraph := rfl
@[simp]
lemma _root_.Equiv.symm_simpleGraph (e : V ≃ W) : e.simpleGraph.symm = e.symm.simpleGraph := rfl
abbrev induce (s : Set V) (G : SimpleGraph V) : SimpleGraph s :=
  G.comap (Function.Embedding.subtype _)
@[simp] lemma induce_singleton_eq_top (v : V) : G.induce {v} = ⊤ := by
  rw [eq_top_iff]; apply le_comap_of_subsingleton
abbrev spanningCoe {s : Set V} (G : SimpleGraph s) : SimpleGraph V :=
  G.map (Function.Embedding.subtype _)
theorem induce_spanningCoe {s : Set V} {G : SimpleGraph s} : G.spanningCoe.induce s = G :=
  comap_map_eq _ _
theorem spanningCoe_induce_le (s : Set V) : (G.induce s).spanningCoe ≤ G :=
  map_comap_le _ _
abbrev Hom :=
  RelHom G.Adj G'.Adj
abbrev Embedding :=
  RelEmbedding G.Adj G'.Adj
abbrev Iso :=
  RelIso G.Adj G'.Adj
@[inherit_doc] infixl:50 " →g " => Hom
@[inherit_doc] infixl:50 " ↪g " => Embedding
@[inherit_doc] infixl:50 " ≃g " => Iso
namespace Hom
variable {G G'} {G₁ G₂ : SimpleGraph V} {H : SimpleGraph W} (f : G →g G')
protected abbrev id : G →g G :=
  RelHom.id _
@[simp, norm_cast] lemma coe_id : ⇑(Hom.id : G →g G) = id := rfl
instance [Subsingleton (V → W)] : Subsingleton (G →g H) := DFunLike.coe_injective.subsingleton
instance [IsEmpty V] : Unique (G →g H) where
  default := ⟨isEmptyElim, fun {a} ↦ isEmptyElim a⟩
  uniq _ := Subsingleton.elim _ _
instance [Finite V] [Finite W] : Finite (G →g H) := DFunLike.finite _
theorem map_adj {v w : V} (h : G.Adj v w) : G'.Adj (f v) (f w) :=
  f.map_rel' h
theorem map_mem_edgeSet {e : Sym2 V} (h : e ∈ G.edgeSet) : e.map f ∈ G'.edgeSet :=
  Sym2.ind (fun _ _ => f.map_rel') e h
theorem apply_mem_neighborSet {v w : V} (h : w ∈ G.neighborSet v) : f w ∈ G'.neighborSet (f v) :=
  map_adj f h
@[simps]
def mapEdgeSet (e : G.edgeSet) : G'.edgeSet :=
  ⟨Sym2.map f e, f.map_mem_edgeSet e.property⟩
@[simps]
def mapNeighborSet (v : V) (w : G.neighborSet v) : G'.neighborSet (f v) :=
  ⟨f w, f.apply_mem_neighborSet w.property⟩
def mapDart (d : G.Dart) : G'.Dart :=
  ⟨d.1.map f f, f.map_adj d.2⟩
@[simp]
theorem mapDart_apply (d : G.Dart) : f.mapDart d = ⟨d.1.map f f, f.map_adj d.2⟩ :=
  rfl
@[simps]
def mapSpanningSubgraphs {G G' : SimpleGraph V} (h : G ≤ G') : G →g G' where
  toFun x := x
  map_rel' ha := h ha
theorem mapEdgeSet.injective (hinj : Function.Injective f) : Function.Injective f.mapEdgeSet := by
  rintro ⟨e₁, h₁⟩ ⟨e₂, h₂⟩
  dsimp [Hom.mapEdgeSet]
  repeat rw [Subtype.mk_eq_mk]
  apply Sym2.map.injective hinj
theorem injective_of_top_hom (f : (⊤ : SimpleGraph V) →g G') : Function.Injective f := by
  intro v w h
  contrapose! h
  exact G'.ne_of_adj (map_adj _ ((top_adj _ _).mpr h))
@[simps]
protected def comap (f : V → W) (G : SimpleGraph W) : G.comap f →g G where
  toFun := f
  map_rel' := by simp
variable {G'' : SimpleGraph X}
abbrev comp (f' : G' →g G'') (f : G →g G') : G →g G'' :=
  RelHom.comp f' f
@[simp]
theorem coe_comp (f' : G' →g G'') (f : G →g G') : ⇑(f'.comp f) = f' ∘ f :=
  rfl
def ofLE (h : G₁ ≤ G₂) : G₁ →g G₂ := ⟨id, @h⟩
@[simp, norm_cast] lemma coe_ofLE (h : G₁ ≤ G₂) : ⇑(ofLE h) = id := rfl
end Hom
namespace Embedding
variable {G G'} {H : SimpleGraph W} (f : G ↪g G')
abbrev refl : G ↪g G :=
  RelEmbedding.refl _
abbrev toHom : G →g G' :=
  f.toRelHom
@[simp] lemma coe_toHom (f : G ↪g H) : ⇑f.toHom = f := rfl
@[simp] theorem map_adj_iff {v w : V} : G'.Adj (f v) (f w) ↔ G.Adj v w :=
  f.map_rel_iff
theorem map_mem_edgeSet_iff {e : Sym2 V} : e.map f ∈ G'.edgeSet ↔ e ∈ G.edgeSet :=
  Sym2.ind (fun _ _ => f.map_adj_iff) e
theorem apply_mem_neighborSet_iff {v w : V} : f w ∈ G'.neighborSet (f v) ↔ w ∈ G.neighborSet v :=
  map_adj_iff f
@[simps]
def mapEdgeSet : G.edgeSet ↪ G'.edgeSet where
  toFun := Hom.mapEdgeSet f
  inj' := Hom.mapEdgeSet.injective f.toRelHom f.injective
@[simps]
def mapNeighborSet (v : V) : G.neighborSet v ↪ G'.neighborSet (f v) where
  toFun w := ⟨f w, f.apply_mem_neighborSet_iff.mpr w.2⟩
  inj' := by
    rintro ⟨w₁, h₁⟩ ⟨w₂, h₂⟩ h
    rw [Subtype.mk_eq_mk] at h ⊢
    exact f.inj' h
protected def comap (f : V ↪ W) (G : SimpleGraph W) : G.comap f ↪g G :=
  { f with map_rel_iff' := by simp }
@[simp]
theorem comap_apply (f : V ↪ W) (G : SimpleGraph W) (v : V) :
    SimpleGraph.Embedding.comap f G v = f v := rfl
protected def map (f : V ↪ W) (G : SimpleGraph V) : G ↪g G.map f :=
  { f with map_rel_iff' := by simp }
@[simp]
theorem map_apply (f : V ↪ W) (G : SimpleGraph V) (v : V) :
    SimpleGraph.Embedding.map f G v = f v := rfl
protected abbrev induce (s : Set V) : G.induce s ↪g G :=
  SimpleGraph.Embedding.comap (Function.Embedding.subtype _) G
protected abbrev spanningCoe {s : Set V} (G : SimpleGraph s) : G ↪g G.spanningCoe :=
  SimpleGraph.Embedding.map (Function.Embedding.subtype _) G
protected def completeGraph {α β : Type*} (f : α ↪ β) :
    (⊤ : SimpleGraph α) ↪g (⊤ : SimpleGraph β) :=
  { f with map_rel_iff' := by simp }
@[simp] lemma coe_completeGraph {α β : Type*} (f : α ↪ β) : ⇑(Embedding.completeGraph f) = f := rfl
variable {G'' : SimpleGraph X}
abbrev comp (f' : G' ↪g G'') (f : G ↪g G') : G ↪g G'' :=
  f.trans f'
@[simp]
theorem coe_comp (f' : G' ↪g G'') (f : G ↪g G') : ⇑(f'.comp f) = f' ∘ f :=
  rfl
end Embedding
section induceHom
variable {G G'} {G'' : SimpleGraph X} {s : Set V} {t : Set W} {r : Set X}
         (φ : G →g G') (φst : Set.MapsTo φ s t) (ψ : G' →g G'') (ψtr : Set.MapsTo ψ t r)
def induceHom : G.induce s →g G'.induce t where
  toFun := Set.MapsTo.restrict φ s t φst
  map_rel' := φ.map_rel'
@[simp, norm_cast] lemma coe_induceHom : ⇑(induceHom φ φst) = Set.MapsTo.restrict φ s t φst :=
  rfl
@[simp] lemma induceHom_id (G : SimpleGraph V) (s) :
    induceHom (Hom.id : G →g G) (Set.mapsTo_id s) = Hom.id := by
  ext x
  rfl
@[simp] lemma induceHom_comp :
    (induceHom ψ ψtr).comp (induceHom φ φst) = induceHom (ψ.comp φ) (ψtr.comp φst) := by
  ext x
  rfl
lemma induceHom_injective (hi : Set.InjOn φ s) :
    Function.Injective (induceHom φ φst) := by
  erw [Set.MapsTo.restrict_inj] <;> assumption
end induceHom
section induceHomLE
variable {s s' : Set V} (h : s ≤ s')
def induceHomOfLE (h : s ≤ s') : G.induce s ↪g G.induce s' where
  toEmbedding := Set.embeddingOfSubset s s' h
  map_rel_iff' := by simp
@[simp] lemma induceHomOfLE_apply (v : s) : (G.induceHomOfLE h) v = Set.inclusion h v := rfl
@[simp] lemma induceHomOfLE_toHom :
    (G.induceHomOfLE h).toHom = induceHom (.id : G →g G) ((Set.mapsTo_id s).mono_right h) := by
  ext; simp
end induceHomLE
namespace Iso
variable {G G'} (f : G ≃g G')
abbrev refl : G ≃g G :=
  RelIso.refl _
abbrev toEmbedding : G ↪g G' :=
  f.toRelEmbedding
abbrev toHom : G →g G' :=
  f.toEmbedding.toHom
abbrev symm : G' ≃g G :=
  RelIso.symm f
theorem map_adj_iff {v w : V} : G'.Adj (f v) (f w) ↔ G.Adj v w :=
  f.map_rel_iff
theorem map_mem_edgeSet_iff {e : Sym2 V} : e.map f ∈ G'.edgeSet ↔ e ∈ G.edgeSet :=
  Sym2.ind (fun _ _ => f.map_adj_iff) e
theorem apply_mem_neighborSet_iff {v w : V} : f w ∈ G'.neighborSet (f v) ↔ w ∈ G.neighborSet v :=
  map_adj_iff f
@[simp]
theorem symm_toHom_comp_toHom : f.symm.toHom.comp f.toHom = Hom.id := by
  ext v
  simp only [RelHom.comp_apply, RelEmbedding.coe_toRelHom, RelIso.coe_toRelEmbedding,
    RelIso.symm_apply_apply, RelHom.id_apply]
@[simp]
theorem toHom_comp_symm_toHom : f.toHom.comp f.symm.toHom = Hom.id := by
  ext v
  simp only [RelHom.comp_apply, RelEmbedding.coe_toRelHom, RelIso.coe_toRelEmbedding,
    RelIso.apply_symm_apply, RelHom.id_apply]
@[simps]
def mapEdgeSet : G.edgeSet ≃ G'.edgeSet where
  toFun := Hom.mapEdgeSet f
  invFun := Hom.mapEdgeSet f.symm
  left_inv := by
    rintro ⟨e, h⟩
    simp only [Hom.mapEdgeSet, RelEmbedding.toRelHom, Embedding.toFun_eq_coe,
      RelEmbedding.coe_toEmbedding, RelIso.coe_toRelEmbedding, Sym2.map_map, comp_apply,
      Subtype.mk.injEq]
    convert congr_fun Sym2.map_id e
    exact RelIso.symm_apply_apply _ _
  right_inv := by
    rintro ⟨e, h⟩
    simp only [Hom.mapEdgeSet, RelEmbedding.toRelHom, Embedding.toFun_eq_coe,
      RelEmbedding.coe_toEmbedding, RelIso.coe_toRelEmbedding, Sym2.map_map, comp_apply,
      Subtype.mk.injEq]
    convert congr_fun Sym2.map_id e
    exact RelIso.apply_symm_apply _ _
@[simps]
def mapNeighborSet (v : V) : G.neighborSet v ≃ G'.neighborSet (f v) where
  toFun w := ⟨f w, f.apply_mem_neighborSet_iff.mpr w.2⟩
  invFun w :=
    ⟨f.symm w, by
      simpa [RelIso.symm_apply_apply] using f.symm.apply_mem_neighborSet_iff.mpr w.2⟩
  left_inv w := by simp
  right_inv w := by simp
include f in
theorem card_eq [Fintype V] [Fintype W] : Fintype.card V = Fintype.card W := by
  rw [← Fintype.ofEquiv_card f.toEquiv]
  convert rfl
protected def comap (f : V ≃ W) (G : SimpleGraph W) : G.comap f.toEmbedding ≃g G :=
  { f with map_rel_iff' := by simp }
@[simp]
lemma comap_apply (f : V ≃ W) (G : SimpleGraph W) (v : V) :
    SimpleGraph.Iso.comap f G v = f v := rfl
@[simp]
lemma comap_symm_apply (f : V ≃ W) (G : SimpleGraph W) (w : W) :
    (SimpleGraph.Iso.comap f G).symm w = f.symm w := rfl
protected def map (f : V ≃ W) (G : SimpleGraph V) : G ≃g G.map f.toEmbedding :=
  { f with map_rel_iff' := by simp }
@[simp]
lemma map_apply (f : V ≃ W) (G : SimpleGraph V) (v : V) :
    SimpleGraph.Iso.map f G v = f v := rfl
@[simp]
lemma map_symm_apply (f : V ≃ W) (G : SimpleGraph V) (w : W) :
    (SimpleGraph.Iso.map f G).symm w = f.symm w := rfl
protected def completeGraph {α β : Type*} (f : α ≃ β) :
    (⊤ : SimpleGraph α) ≃g (⊤ : SimpleGraph β) :=
  { f with map_rel_iff' := by simp }
theorem toEmbedding_completeGraph {α β : Type*} (f : α ≃ β) :
    (Iso.completeGraph f).toEmbedding = Embedding.completeGraph f.toEmbedding :=
  rfl
variable {G'' : SimpleGraph X}
abbrev comp (f' : G' ≃g G'') (f : G ≃g G') : G ≃g G'' :=
  f.trans f'
@[simp]
theorem coe_comp (f' : G' ≃g G'') (f : G ≃g G') : ⇑(f'.comp f) = f' ∘ f :=
  rfl
end Iso
@[simps!]
def induceUnivIso (G : SimpleGraph V) : G.induce Set.univ ≃g G where
  toEquiv := Equiv.Set.univ V
  map_rel_iff' := by simp only [Equiv.Set.univ, Equiv.coe_fn_mk, comap_adj, Embedding.coe_subtype,
                                Subtype.forall, Set.mem_univ, forall_true_left, implies_true]
section Finite
variable [Fintype V] {n : ℕ}
def overFin (hc : Fintype.card V = n) : SimpleGraph (Fin n) where
  Adj x y := G.Adj ((Fintype.equivFinOfCardEq hc).symm x) ((Fintype.equivFinOfCardEq hc).symm y)
  symm x y := by simp_rw [adj_comm, imp_self]
noncomputable def overFinIso (hc : Fintype.card V = n) : G ≃g G.overFin hc := by
  use Fintype.equivFinOfCardEq hc; simp [overFin]
end Finite
end SimpleGraph