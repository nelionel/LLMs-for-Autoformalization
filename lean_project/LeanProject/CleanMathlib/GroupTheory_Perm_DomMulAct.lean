import Mathlib.Algebra.Group.Action.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Set.Card
import Mathlib.GroupTheory.GroupAction.Defs
import Mathlib.GroupTheory.GroupAction.DomAct.Basic
import Mathlib.SetTheory.Cardinal.Finite
variable {α ι : Type*} {f : α → ι}
open Equiv MulAction
namespace DomMulAct
lemma mem_stabilizer_iff {g : (Perm α)ᵈᵐᵃ} :
    g ∈ stabilizer (Perm α)ᵈᵐᵃ f ↔ f ∘ (mk.symm g :) = f := by
  simp only [MulAction.mem_stabilizer_iff]; rfl
def stabilizerEquiv_invFun (g : ∀ i, Perm {a // f a = i}) (a : α) : α := g (f a) ⟨a, rfl⟩
lemma stabilizerEquiv_invFun_eq (g : ∀ i, Perm {a // f a = i}) {a : α} {i : ι} (h : f a = i) :
    stabilizerEquiv_invFun g a = g i ⟨a, h⟩ := by subst h; rfl
lemma comp_stabilizerEquiv_invFun (g : ∀ i, Perm {a // f a = i}) (a : α) :
    f (stabilizerEquiv_invFun g a) = f a :=
  (g (f a) ⟨a, rfl⟩).prop
def stabilizerEquiv_invFun_aux (g : ∀ i, Perm {a // f a = i}) : Perm α where
  toFun := stabilizerEquiv_invFun g
  invFun := stabilizerEquiv_invFun (fun i ↦ (g i).symm)
  left_inv a := by
    rw [stabilizerEquiv_invFun_eq _ (comp_stabilizerEquiv_invFun g a)]
    exact congr_arg Subtype.val ((g <| f a).left_inv _)
  right_inv a := by
    rw [stabilizerEquiv_invFun_eq _ (comp_stabilizerEquiv_invFun _ a)]
    exact congr_arg Subtype.val ((g <| f a).right_inv _)
variable (f)
def stabilizerMulEquiv : (stabilizer (Perm α)ᵈᵐᵃ f)ᵐᵒᵖ ≃* (∀ i, Perm {a // f a = i}) where
  toFun g i := Perm.subtypePerm (mk.symm g.unop) fun a ↦ by
    rw [← Function.comp_apply (f := f), mem_stabilizer_iff.mp g.unop.prop]
  invFun g := ⟨mk (stabilizerEquiv_invFun_aux g), by
    ext a
    rw [smul_apply, symm_apply_apply, Perm.smul_def]
    apply comp_stabilizerEquiv_invFun⟩
  left_inv _ := rfl
  right_inv g := by ext i a; apply stabilizerEquiv_invFun_eq
  map_mul' _ _ := rfl
variable {f}
lemma stabilizerMulEquiv_apply (g : (stabilizer (Perm α)ᵈᵐᵃ f)ᵐᵒᵖ) {a : α} {i : ι} (h : f a = i) :
    ((stabilizerMulEquiv f)) g i ⟨a, h⟩ = (mk.symm g.unop : Equiv.Perm α) a := rfl
section Fintype
variable [Fintype α]
open Nat
variable (f)
theorem stabilizer_card [DecidableEq α] [DecidableEq ι] [Fintype ι] :
    Fintype.card {g : Perm α // f ∘ g = f} = ∏ i, (Fintype.card {a // f a = i})! := by
  rw [← Nat.card_eq_fintype_card,
    Nat.card_congr (subtypeEquiv mk fun _ ↦ ?_),
    Nat.card_congr MulOpposite.opEquiv,
    Nat.card_congr (DomMulAct.stabilizerMulEquiv f).toEquiv, Nat.card_pi]
  · exact Finset.prod_congr rfl fun i _ ↦ by rw [Nat.card_eq_fintype_card, Fintype.card_perm]
  · rfl
omit [Fintype α] in
theorem stabilizer_ncard [Finite α] [Fintype ι] :
    Set.ncard {g : Perm α | f ∘ g = f} = ∏ i, (Set.ncard {a | f a = i})! := by
  classical
  cases nonempty_fintype α
  simp only [← Set.Nat.card_coe_set_eq, Set.coe_setOf, card_eq_fintype_card]
  exact stabilizer_card f
variable [DecidableEq α] [DecidableEq ι]
theorem stabilizer_card':
    Fintype.card {g : Perm α // f ∘ g = f} =
      ∏ i in Finset.univ.image f, (Fintype.card ({a // f a = i}))! := by
  set φ : α → Finset.univ.image f :=
    Set.codRestrict f (Finset.univ.image f) (fun a => by simp)
  suffices ∀ g : Perm α, f ∘ g = f ↔ φ ∘ g = φ by
    simp only [this, stabilizer_card]
    apply Finset.prod_bij (fun g _ => g.val)
    · exact fun g _ => Finset.coe_mem g
    · exact fun g _ g' _ =>  SetCoe.ext
    · exact fun g hg => by
        rw [Finset.mem_image] at hg
        obtain ⟨a, _, rfl⟩ := hg
        use ⟨f a, by simp only [Finset.mem_image, Finset.mem_univ, true_and, exists_apply_eq_apply]⟩
        simp only [Finset.univ_eq_attach, Finset.mem_attach, exists_const]
    · intro i _
      apply congr_arg
      apply Fintype.card_congr
      apply Equiv.subtypeEquiv (Equiv.refl α)
      intro a
      rw [refl_apply, ← Subtype.coe_inj]
      simp only [φ, Set.val_codRestrict_apply]
  · intro g
    simp only [funext_iff]
    apply forall_congr'
    intro a
    simp only [Function.comp_apply, φ, ← Subtype.coe_inj, Set.val_codRestrict_apply]
end Fintype
end DomMulAct