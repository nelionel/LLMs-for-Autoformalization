import Mathlib.Algebra.Order.Monoid.Canonical.Defs
import Mathlib.Algebra.Order.Sub.Defs
import Mathlib.Data.Finset.Basic
import Mathlib.Order.Interval.Finset.Defs
open Function
namespace Finset
class HasAntidiagonal (A : Type*) [AddMonoid A] where
  antidiagonal : A → Finset (A × A)
  mem_antidiagonal {n} {a} : a ∈ antidiagonal n ↔ a.fst + a.snd = n
export HasAntidiagonal (antidiagonal mem_antidiagonal)
attribute [simp] mem_antidiagonal
variable {A : Type*}
instance [AddMonoid A] : Subsingleton (HasAntidiagonal A) where
  allEq := by
    rintro ⟨a, ha⟩ ⟨b, hb⟩
    congr with n xy
    rw [ha, hb]
lemma hasAntidiagonal_congr (A : Type*) [AddMonoid A]
    [H1 : HasAntidiagonal A] [H2 : HasAntidiagonal A] :
    H1.antidiagonal = H2.antidiagonal := by congr!; subsingleton
theorem swap_mem_antidiagonal [AddCommMonoid A] [HasAntidiagonal A] {n : A} {xy : A × A} :
    xy.swap ∈ antidiagonal n ↔ xy ∈ antidiagonal n := by
  simp [add_comm]
@[simp] theorem map_prodComm_antidiagonal [AddCommMonoid A] [HasAntidiagonal A] {n : A} :
    (antidiagonal n).map (Equiv.prodComm A A) = antidiagonal n :=
  Finset.ext fun ⟨a, b⟩ => by simp [add_comm]
@[simp] theorem map_swap_antidiagonal [AddCommMonoid A] [HasAntidiagonal A] {n : A} :
    (antidiagonal n).map ⟨Prod.swap, Prod.swap_injective⟩ = antidiagonal n :=
  map_prodComm_antidiagonal
section AddCancelMonoid
variable [AddCancelMonoid A] [HasAntidiagonal A] {p q : A × A} {n : A}
theorem antidiagonal_congr (hp : p ∈ antidiagonal n) (hq : q ∈ antidiagonal n) :
    p = q ↔ p.1 = q.1 := by
  refine ⟨congr_arg Prod.fst, fun h ↦ Prod.ext h ((add_right_inj q.fst).mp ?_)⟩
  rw [mem_antidiagonal] at hp hq
  rw [hq, ← h, hp]
@[ext] theorem antidiagonal_subtype_ext {p q : antidiagonal n} (h : p.val.1 = q.val.1) : p = q :=
  Subtype.ext ((antidiagonal_congr p.prop q.prop).mpr h)
end AddCancelMonoid
section AddCancelCommMonoid
variable [AddCancelCommMonoid A] [HasAntidiagonal A] {p q : A × A} {n : A}
lemma antidiagonal_congr' (hp : p ∈ antidiagonal n) (hq : q ∈ antidiagonal n) :
    p = q ↔ p.2 = q.2 := by
  rw [← Prod.swap_inj]
  exact antidiagonal_congr (swap_mem_antidiagonal.2 hp) (swap_mem_antidiagonal.2 hq)
end AddCancelCommMonoid
section CanonicallyOrderedAddCommMonoid
variable [CanonicallyOrderedAddCommMonoid A] [HasAntidiagonal A]
@[simp]
theorem antidiagonal_zero : antidiagonal (0 : A) = {(0, 0)} := by
  ext ⟨x, y⟩
  simp
theorem antidiagonal.fst_le {n : A} {kl : A × A} (hlk : kl ∈ antidiagonal n) : kl.1 ≤ n := by
  rw [le_iff_exists_add]
  use kl.2
  rwa [mem_antidiagonal, eq_comm] at hlk
theorem antidiagonal.snd_le {n : A} {kl : A × A} (hlk : kl ∈ antidiagonal n) : kl.2 ≤ n := by
  rw [le_iff_exists_add]
  use kl.1
  rwa [mem_antidiagonal, eq_comm, add_comm] at hlk
end CanonicallyOrderedAddCommMonoid
section OrderedSub
variable [CanonicallyOrderedAddCommMonoid A] [Sub A] [OrderedSub A]
variable [AddLeftReflectLE A]
variable [HasAntidiagonal A]
theorem filter_fst_eq_antidiagonal (n m : A) [DecidablePred (· = m)] [Decidable (m ≤ n)] :
    filter (fun x : A × A ↦ x.fst = m) (antidiagonal n) = if m ≤ n then {(m, n - m)} else ∅ := by
  ext ⟨a, b⟩
  suffices a = m → (a + b = n ↔ m ≤ n ∧ b = n - m) by
    rw [mem_filter, mem_antidiagonal, apply_ite (fun n ↦ (a, b) ∈ n), mem_singleton,
      Prod.mk.inj_iff, ite_prop_iff_or]
    simpa [← and_assoc, @and_right_comm _ (a = _), and_congr_left_iff]
  rintro rfl
  constructor
  · rintro rfl
    exact ⟨le_add_right le_rfl, (add_tsub_cancel_left _ _).symm⟩
  · rintro ⟨h, rfl⟩
    exact add_tsub_cancel_of_le h
theorem filter_snd_eq_antidiagonal (n m : A) [DecidablePred (· = m)] [Decidable (m ≤ n)] :
    filter (fun x : A × A ↦ x.snd = m) (antidiagonal n) = if m ≤ n then {(n - m, m)} else ∅ := by
  have : (fun x : A × A ↦ (x.snd = m)) ∘ Prod.swap = fun x : A × A ↦ x.fst = m := by
    ext; simp
  rw [← map_swap_antidiagonal, filter_map]
  simp [this, filter_fst_eq_antidiagonal, apply_ite (Finset.map _)]
end OrderedSub
@[simps]
def sigmaAntidiagonalEquivProd [AddMonoid A] [HasAntidiagonal A] :
    (Σ n : A, antidiagonal n) ≃ A × A where
  toFun x := x.2
  invFun x := ⟨x.1 + x.2, x, mem_antidiagonal.mpr rfl⟩
  left_inv := by
    rintro ⟨n, ⟨k, l⟩, h⟩
    rw [mem_antidiagonal] at h
    exact Sigma.subtype_ext h rfl
  right_inv _ := rfl
variable {A : Type*}
  [CanonicallyOrderedAddCommMonoid A]
  [LocallyFiniteOrder A] [DecidableEq A]
abbrev antidiagonalOfLocallyFinite : HasAntidiagonal A where
  antidiagonal n := Finset.filter (fun uv => uv.fst + uv.snd = n) (Finset.product (Iic n) (Iic n))
  mem_antidiagonal {n} {a} := by
    simp only [Prod.forall, mem_filter, and_iff_right_iff_imp]
    intro h; rw [← h]
    erw [mem_product, mem_Iic, mem_Iic]
    exact ⟨le_self_add, le_add_self⟩
end Finset