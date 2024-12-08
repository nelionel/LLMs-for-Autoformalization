import Mathlib.Logic.Nontrivial.Defs
import Mathlib.Logic.Nonempty
open Function
variable {α β : Type*}
@[ext]
structure TwoPointing (α : Type*) extends α × α where
  fst_ne_snd : fst ≠ snd
  deriving DecidableEq
initialize_simps_projections TwoPointing (+toProd, -fst, -snd)
namespace TwoPointing
variable (p : TwoPointing α) (q : TwoPointing β)
theorem snd_ne_fst : p.snd ≠ p.fst :=
  p.fst_ne_snd.symm
@[simps]
def swap : TwoPointing α :=
  ⟨(p.snd, p.fst), p.snd_ne_fst⟩
theorem swap_fst : p.swap.fst = p.snd := rfl
theorem swap_snd : p.swap.snd = p.fst := rfl
@[simp]
theorem swap_swap : p.swap.swap = p := rfl
include p in
theorem to_nontrivial : Nontrivial α :=
  ⟨⟨p.fst, p.snd, p.fst_ne_snd⟩⟩
instance [Nontrivial α] : Nonempty (TwoPointing α) :=
  let ⟨a, b, h⟩ := exists_pair_ne α
  ⟨⟨(a, b), h⟩⟩
@[simp]
theorem nonempty_two_pointing_iff : Nonempty (TwoPointing α) ↔ Nontrivial α :=
  ⟨fun ⟨p⟩ ↦ p.to_nontrivial, fun _ => inferInstance⟩
section Pi
variable (α) [Nonempty α]
def pi : TwoPointing (α → β) where
  fst _ := q.fst
  snd _ := q.snd
  fst_ne_snd h := q.fst_ne_snd (congr_fun h (Classical.arbitrary α))
@[simp]
theorem pi_fst : (q.pi α).fst = const α q.fst :=
  rfl
@[simp]
theorem pi_snd : (q.pi α).snd = const α q.snd :=
  rfl
end Pi
def prod : TwoPointing (α × β) where
  fst := (p.fst, q.fst)
  snd := (p.snd, q.snd)
  fst_ne_snd h := p.fst_ne_snd (congr_arg Prod.fst h)
@[simp]
theorem prod_fst : (p.prod q).fst = (p.fst, q.fst) :=
  rfl
@[simp]
theorem prod_snd : (p.prod q).snd = (p.snd, q.snd) :=
  rfl
protected def sum : TwoPointing (α ⊕ β) :=
  ⟨(Sum.inl p.fst, Sum.inr q.snd), Sum.inl_ne_inr⟩
@[simp]
theorem sum_fst : (p.sum q).fst = Sum.inl p.fst :=
  rfl
@[simp]
theorem sum_snd : (p.sum q).snd = Sum.inr q.snd :=
  rfl
protected def bool : TwoPointing Bool :=
  ⟨(false, true), Bool.false_ne_true⟩
@[simp]
theorem bool_fst : TwoPointing.bool.fst = false := rfl
@[simp]
theorem bool_snd : TwoPointing.bool.snd = true := rfl
instance : Inhabited (TwoPointing Bool) :=
  ⟨TwoPointing.bool⟩
protected def prop : TwoPointing Prop :=
  ⟨(False, True), false_ne_true⟩
@[simp]
theorem prop_fst : TwoPointing.prop.fst = False :=
  rfl
@[simp]
theorem prop_snd : TwoPointing.prop.snd = True :=
  rfl
end TwoPointing