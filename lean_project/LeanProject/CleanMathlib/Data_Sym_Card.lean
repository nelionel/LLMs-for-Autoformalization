import Mathlib.Algebra.BigOperators.Group.Finset
import Mathlib.Data.Finset.Sym
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Fintype.Prod
open Finset Fintype Function Sum Nat
variable {α : Type*}
namespace Sym
section Sym
variable (α) (n : ℕ)
protected def e1 {n k : ℕ} : { s : Sym (Fin (n + 1)) (k + 1) // ↑0 ∈ s } ≃ Sym (Fin n.succ) k where
  toFun s := s.1.erase 0 s.2
  invFun s := ⟨cons 0 s, mem_cons_self 0 s⟩
  left_inv s := by simp
  right_inv s := by simp
protected def e2 {n k : ℕ} : { s : Sym (Fin n.succ.succ) k // ↑0 ∉ s } ≃ Sym (Fin n.succ) k where
  toFun s := map (Fin.predAbove 0) s.1
  invFun s :=
    ⟨map (Fin.succAbove 0) s,
      (mt mem_map.1) (not_exists.2 fun t => not_and.2 fun _ => Fin.succAbove_ne _ t)⟩
  left_inv s := by
    ext1
    simp only [map_map]
    refine (Sym.map_congr fun v hv ↦ ?_).trans (map_id' _)
    exact Fin.succAbove_predAbove (ne_of_mem_of_not_mem hv s.2)
  right_inv s := by
    simp only [map_map, comp_apply, ← Fin.castSucc_zero, Fin.predAbove_succAbove, map_id']
theorem card_sym_fin_eq_multichoose : ∀ n k : ℕ, card (Sym (Fin n) k) = multichoose n k
  | n, 0 => by simp
  | 0, k + 1 => by rw [multichoose_zero_succ]; exact card_eq_zero
  | 1, k + 1 => by simp
  | n + 2, k + 1 => by
    rw [multichoose_succ_succ, ← card_sym_fin_eq_multichoose (n + 1) (k + 1),
      ← card_sym_fin_eq_multichoose (n + 2) k, add_comm (Fintype.card _), ← card_sum]
    refine Fintype.card_congr (Equiv.symm ?_)
    apply (Sym.e1.symm.sumCongr Sym.e2.symm).trans
    apply Equiv.sumCompl
theorem card_sym_eq_multichoose (α : Type*) (k : ℕ) [Fintype α] [Fintype (Sym α k)] :
    card (Sym α k) = multichoose (card α) k := by
  rw [← card_sym_fin_eq_multichoose]
  exact Fintype.card_congr (equivCongr (equivFin α))
theorem card_sym_eq_choose {α : Type*} [Fintype α] (k : ℕ) [Fintype (Sym α k)] :
    card (Sym α k) = (card α + k - 1).choose k := by
  rw [card_sym_eq_multichoose, Nat.multichoose_eq]
end Sym
end Sym
namespace Sym2
variable [DecidableEq α]
theorem card_image_diag (s : Finset α) : #(s.diag.image Sym2.mk) = #s := by
  rw [card_image_of_injOn, diag_card]
  rintro ⟨x₀, x₁⟩ hx _ _ h
  cases Sym2.eq.1 h
  · rfl
  · simp only [mem_coe, mem_diag] at hx
    rw [hx.2]
lemma two_mul_card_image_offDiag (s : Finset α) : 2 * #(s.offDiag.image Sym2.mk) = #s.offDiag := by
  rw [card_eq_sum_card_image (Sym2.mk : α × α → _), sum_const_nat (Sym2.ind _), mul_comm]
  rintro x y hxy
  simp_rw [mem_image, mem_offDiag] at hxy
  obtain ⟨a, ⟨ha₁, ha₂, ha⟩, h⟩ := hxy
  replace h := Sym2.eq.1 h
  obtain ⟨hx, hy, hxy⟩ : x ∈ s ∧ y ∈ s ∧ x ≠ y := by
    cases h <;> refine ⟨‹_›, ‹_›, ?_⟩ <;> [exact ha; exact ha.symm]
  have hxy' : y ≠ x := hxy.symm
  have : {z ∈ s.offDiag | Sym2.mk z = s(x, y)} = {(x, y), (y, x)} := by
    ext ⟨x₁, y₁⟩
    rw [mem_filter, mem_insert, mem_singleton, Sym2.eq_iff, Prod.mk.inj_iff, Prod.mk.inj_iff,
      and_iff_right_iff_imp]
    rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;> rw [mem_offDiag] <;> exact ⟨‹_›, ‹_›, ‹_›⟩
  rw [this, card_insert_of_not_mem, card_singleton]
  simp only [not_and, Prod.mk.inj_iff, mem_singleton]
  exact fun _ => hxy'
theorem card_image_offDiag (s : Finset α) : #(s.offDiag.image Sym2.mk) = (#s).choose 2 := by
  rw [Nat.choose_two_right, Nat.mul_sub_left_distrib, mul_one, ← offDiag_card,
    Nat.div_eq_of_eq_mul_right Nat.zero_lt_two (two_mul_card_image_offDiag s).symm]
theorem card_subtype_diag [Fintype α] : card { a : Sym2 α // a.IsDiag } = card α := by
  convert card_image_diag (univ : Finset α)
  rw [← filter_image_mk_isDiag, Fintype.card_of_subtype]
  rintro x
  rw [mem_filter, univ_product_univ, mem_image]
  obtain ⟨a, ha⟩ := Quot.exists_rep x
  exact and_iff_right ⟨a, mem_univ _, ha⟩
theorem card_subtype_not_diag [Fintype α] :
    card { a : Sym2 α // ¬a.IsDiag } = (card α).choose 2 := by
  convert card_image_offDiag (univ : Finset α)
  rw [← filter_image_mk_not_isDiag, Fintype.card_of_subtype]
  rintro x
  rw [mem_filter, univ_product_univ, mem_image]
  obtain ⟨a, ha⟩ := Quot.exists_rep x
  exact and_iff_right ⟨a, mem_univ _, ha⟩
protected theorem card {α} [Fintype α] : card (Sym2 α) = Nat.choose (card α + 1) 2 :=
  Finset.card_sym2 _
end Sym2