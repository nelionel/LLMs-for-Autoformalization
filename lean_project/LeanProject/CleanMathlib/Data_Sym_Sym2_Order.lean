import Mathlib.Data.Sym.Sym2
import Mathlib.Order.Lattice
namespace Sym2
variable {α}
def sup [SemilatticeSup α] (x : Sym2 α) : α := Sym2.lift ⟨(· ⊔ ·), sup_comm⟩ x
@[simp] theorem sup_mk [SemilatticeSup α] (a b : α) : s(a, b).sup = a ⊔ b := rfl
def inf [SemilatticeInf α] (x : Sym2 α) : α := Sym2.lift ⟨(· ⊓ ·), inf_comm⟩ x
@[simp] theorem inf_mk [SemilatticeInf α] (a b : α) : s(a, b).inf = a ⊓ b := rfl
protected theorem inf_le_sup [Lattice α] (s : Sym2 α) : s.inf ≤ s.sup := by
  cases s using Sym2.ind; simp [_root_.inf_le_sup]
@[simps!]
def sortEquiv [LinearOrder α] : Sym2 α ≃ { p : α × α // p.1 ≤ p.2 } where
  toFun s := ⟨(s.inf, s.sup), Sym2.inf_le_sup _⟩
  invFun p := Sym2.mk p
  left_inv := Sym2.ind fun a b => mk_eq_mk_iff.mpr <| by
    cases le_total a b with
    | inl h => simp [h]
    | inr h => simp [h]
  right_inv := Subtype.rec <| Prod.rec fun x y hxy =>
    Subtype.ext <| Prod.ext (by simp [hxy]) (by simp [hxy])
end Sym2