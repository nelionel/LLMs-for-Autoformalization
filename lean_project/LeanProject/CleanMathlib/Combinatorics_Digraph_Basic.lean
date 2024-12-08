import Mathlib.Order.CompleteBooleanAlgebra
import Mathlib.Data.Fintype.Pi
open Finset Function
@[ext]
structure Digraph (V : Type*) where
  Adj : V → V → Prop
@[simps]
def Digraph.mk' {V : Type*} : (V → V → Bool) ↪ Digraph V where
  toFun x := ⟨fun v w ↦ x v w⟩
  inj' adj adj' := by
    simp_rw [mk.injEq]
    intro h
    funext v w
    simpa only [eq_iff_iff, Bool.coe_iff_coe] using congr($h v w)
instance {V : Type*} (adj : V → V → Bool) : DecidableRel (Digraph.mk' adj).Adj :=
  inferInstanceAs <| DecidableRel (fun v w ↦ adj v w)
instance {V : Type*} [DecidableEq V] [Fintype V] : Fintype (Digraph V) :=
  Fintype.ofBijective Digraph.mk' <| by
    classical
    refine ⟨Embedding.injective _, ?_⟩
    intro G
    use fun v w ↦ G.Adj v w
    ext v w
    simp
namespace Digraph
protected def completeDigraph (V : Type*) : Digraph V where Adj := ⊤
protected def emptyDigraph (V : Type*) : Digraph V where Adj _ _ := False
@[simps]
def completeBipartiteGraph (V W : Type*) : Digraph (Sum V W) where
  Adj v w := v.isLeft ∧ w.isRight ∨ v.isRight ∧ w.isLeft
variable {ι : Sort*} {V : Type*} (G : Digraph V) {a b : V}
theorem adj_injective : Injective (Adj : Digraph V → V → V → Prop) := fun _ _ ↦ Digraph.ext
@[simp] theorem adj_inj {G H : Digraph V} : G.Adj = H.Adj ↔ G = H := Digraph.ext_iff.symm
section Order
protected def IsSubgraph (x y : Digraph V) : Prop :=
  ∀ ⦃v w : V⦄, x.Adj v w → y.Adj v w
instance : LE (Digraph V) := ⟨Digraph.IsSubgraph⟩
@[simp]
theorem isSubgraph_eq_le : (Digraph.IsSubgraph : Digraph V → Digraph V → Prop) = (· ≤ ·) := rfl
instance : Max (Digraph V) where
  max x y := { Adj := x.Adj ⊔ y.Adj }
@[simp]
theorem sup_adj (x y : Digraph V) (v w : V) : (x ⊔ y).Adj v w ↔ x.Adj v w ∨ y.Adj v w := Iff.rfl
instance : Min (Digraph V) where
  min x y := { Adj := x.Adj ⊓ y.Adj }
@[simp]
theorem inf_adj (x y : Digraph V) (v w : V) : (x ⊓ y).Adj v w ↔ x.Adj v w ∧ y.Adj v w := Iff.rfl
instance hasCompl : HasCompl (Digraph V) where
  compl G := { Adj := fun v w ↦ ¬G.Adj v w }
@[simp] theorem compl_adj (G : Digraph V) (v w : V) : Gᶜ.Adj v w ↔ ¬G.Adj v w := Iff.rfl
instance sdiff : SDiff (Digraph V) where
  sdiff x y := { Adj := x.Adj \ y.Adj }
@[simp]
theorem sdiff_adj (x y : Digraph V) (v w : V) : (x \ y).Adj v w ↔ x.Adj v w ∧ ¬y.Adj v w := Iff.rfl
instance supSet : SupSet (Digraph V) where
  sSup s := { Adj := fun a b ↦ ∃ G ∈ s, Adj G a b }
instance infSet : InfSet (Digraph V) where
  sInf s := { Adj := fun a b ↦ (∀ ⦃G⦄, G ∈ s → Adj G a b) }
@[simp]
theorem sSup_adj {s : Set (Digraph V)} : (sSup s).Adj a b ↔ ∃ G ∈ s, Adj G a b := Iff.rfl
@[simp]
theorem sInf_adj {s : Set (Digraph V)} : (sInf s).Adj a b ↔ ∀ G ∈ s, Adj G a b := Iff.rfl
@[simp]
theorem iSup_adj {f : ι → Digraph V} : (⨆ i, f i).Adj a b ↔ ∃ i, (f i).Adj a b := by simp [iSup]
@[simp]
theorem iInf_adj {f : ι → Digraph V} : (⨅ i, f i).Adj a b ↔ (∀ i, (f i).Adj a b) := by simp [iInf]
instance distribLattice : DistribLattice (Digraph V) :=
  { adj_injective.distribLattice Digraph.Adj (fun _ _ ↦ rfl) fun _ _ ↦ rfl with
    le := fun G H ↦ ∀ ⦃a b⦄, G.Adj a b → H.Adj a b }
instance completeAtomicBooleanAlgebra : CompleteAtomicBooleanAlgebra (Digraph V) :=
  { Digraph.distribLattice with
    le := (· ≤ ·)
    sup := (· ⊔ ·)
    inf := (· ⊓ ·)
    compl := HasCompl.compl
    sdiff := (· \ ·)
    top := Digraph.completeDigraph V
    bot := Digraph.emptyDigraph V
    le_top := fun _ _ _ _ ↦ trivial
    bot_le := fun _ _ _ h ↦ h.elim
    sdiff_eq := fun _ _ ↦ rfl
    inf_compl_le_bot := fun _ _ _ h ↦ absurd h.1 h.2
    top_le_sup_compl := fun G v w _ ↦ by tauto
    sSup := sSup
    le_sSup := fun _ G hG _ _ hab ↦ ⟨G, hG, hab⟩
    sSup_le := fun s G hG a b ↦ by
      rintro ⟨H, hH, hab⟩
      exact hG _ hH hab
    sInf := sInf
    sInf_le := fun _ _ hG _ _ hab ↦ hab hG
    le_sInf := fun _ _ hG _ _ hab ↦ fun _ hH ↦ hG _ hH hab
    iInf_iSup_eq := fun f ↦ by ext; simp [Classical.skolem] }
@[simp] theorem top_adj (v w : V) : (⊤ : Digraph V).Adj v w := trivial
@[simp] theorem bot_adj (v w : V) : (⊥ : Digraph V).Adj v w ↔ False := Iff.rfl
@[simp] theorem completeDigraph_eq_top (V : Type*) : Digraph.completeDigraph V = ⊤ := rfl
@[simp] theorem emptyDigraph_eq_bot (V : Type*) : Digraph.emptyDigraph V = ⊥ := rfl
@[simps] instance (V : Type*) : Inhabited (Digraph V) := ⟨⊥⟩
instance [IsEmpty V] : Unique (Digraph V) where
  default := ⊥
  uniq G := by ext1; congr!
instance [Nonempty V] : Nontrivial (Digraph V) := by
  use ⊥, ⊤
  have v := Classical.arbitrary V
  exact ne_of_apply_ne (·.Adj v v) (by simp)
section Decidable
variable (V) (H : Digraph V) [DecidableRel G.Adj] [DecidableRel H.Adj]
instance Bot.adjDecidable : DecidableRel (⊥ : Digraph V).Adj :=
  inferInstanceAs <| DecidableRel fun _ _ ↦ False
instance Sup.adjDecidable : DecidableRel (G ⊔ H).Adj :=
  inferInstanceAs <| DecidableRel fun v w ↦ G.Adj v w ∨ H.Adj v w
instance Inf.adjDecidable : DecidableRel (G ⊓ H).Adj :=
  inferInstanceAs <| DecidableRel fun v w ↦ G.Adj v w ∧ H.Adj v w
instance SDiff.adjDecidable : DecidableRel (G \ H).Adj :=
  inferInstanceAs <| DecidableRel fun v w ↦ G.Adj v w ∧ ¬H.Adj v w
instance Top.adjDecidable : DecidableRel (⊤ : Digraph V).Adj :=
  inferInstanceAs <| DecidableRel fun _ _ ↦ True
instance Compl.adjDecidable : DecidableRel (Gᶜ.Adj) :=
  inferInstanceAs <| DecidableRel fun v w ↦ ¬G.Adj v w
end Decidable
end Order
end Digraph