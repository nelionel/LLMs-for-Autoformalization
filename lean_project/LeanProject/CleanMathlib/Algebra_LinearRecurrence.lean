import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.LinearAlgebra.Dimension.Constructions
noncomputable section
open Finset
open Polynomial
structure LinearRecurrence (α : Type*) [CommSemiring α] where
  order : ℕ
  coeffs : Fin order → α
instance (α : Type*) [CommSemiring α] : Inhabited (LinearRecurrence α) :=
  ⟨⟨0, default⟩⟩
namespace LinearRecurrence
section CommSemiring
variable {α : Type*} [CommSemiring α] (E : LinearRecurrence α)
def IsSolution (u : ℕ → α) :=
  ∀ n, u (n + E.order) = ∑ i, E.coeffs i * u (n + i)
def mkSol (init : Fin E.order → α) : ℕ → α
  | n =>
    if h : n < E.order then init ⟨n, h⟩
    else
      ∑ k : Fin E.order,
        have _ : n - E.order + k < n := by
          rw [add_comm, ← add_tsub_assoc_of_le (not_lt.mp h), tsub_lt_iff_left]
          · exact add_lt_add_right k.is_lt n
          · convert add_le_add (zero_le (k : ℕ)) (not_lt.mp h)
            simp only [zero_add]
        E.coeffs k * mkSol init (n - E.order + k)
theorem is_sol_mkSol (init : Fin E.order → α) : E.IsSolution (E.mkSol init) := by
  intro n
  rw [mkSol]
  simp
theorem mkSol_eq_init (init : Fin E.order → α) : ∀ n : Fin E.order, E.mkSol init n = init n := by
  intro n
  rw [mkSol]
  simp only [n.is_lt, dif_pos, Fin.mk_val, Fin.eta]
theorem eq_mk_of_is_sol_of_eq_init {u : ℕ → α} {init : Fin E.order → α} (h : E.IsSolution u)
    (heq : ∀ n : Fin E.order, u n = init n) : ∀ n, u n = E.mkSol init n := by
  intro n
  rw [mkSol]
  split_ifs with h'
  · exact mod_cast heq ⟨n, h'⟩
  rw [← tsub_add_cancel_of_le (le_of_not_lt h'), h (n - E.order)]
  congr with k
  have : n - E.order + k < n := by
    rw [add_comm, ← add_tsub_assoc_of_le (not_lt.mp h'), tsub_lt_iff_left]
    · exact add_lt_add_right k.is_lt n
    · convert add_le_add (zero_le (k : ℕ)) (not_lt.mp h')
      simp only [zero_add]
  rw [eq_mk_of_is_sol_of_eq_init h heq (n - E.order + k)]
  simp
theorem eq_mk_of_is_sol_of_eq_init' {u : ℕ → α} {init : Fin E.order → α} (h : E.IsSolution u)
    (heq : ∀ n : Fin E.order, u n = init n) : u = E.mkSol init :=
  funext (E.eq_mk_of_is_sol_of_eq_init h heq)
def solSpace : Submodule α (ℕ → α) where
  carrier := { u | E.IsSolution u }
  zero_mem' n := by simp
  add_mem' {u v} hu hv n := by simp [mul_add, sum_add_distrib, hu n, hv n]
  smul_mem' a u hu n := by simp [hu n, mul_sum]; congr; ext; ac_rfl
theorem is_sol_iff_mem_solSpace (u : ℕ → α) : E.IsSolution u ↔ u ∈ E.solSpace :=
  Iff.rfl
def toInit : E.solSpace ≃ₗ[α] Fin E.order → α where
  toFun u x := (u : ℕ → α) x
  map_add' u v := by
    ext
    simp
  map_smul' a u := by
    ext
    simp
  invFun u := ⟨E.mkSol u, E.is_sol_mkSol u⟩
  left_inv u := by ext n; symm; apply E.eq_mk_of_is_sol_of_eq_init u.2; intro k; rfl
  right_inv u := funext_iff.mpr fun n ↦ E.mkSol_eq_init u n
theorem sol_eq_of_eq_init (u v : ℕ → α) (hu : E.IsSolution u) (hv : E.IsSolution v) :
    u = v ↔ Set.EqOn u v ↑(range E.order) := by
  refine Iff.intro (fun h x _ ↦ h ▸ rfl) ?_
  intro h
  set u' : ↥E.solSpace := ⟨u, hu⟩
  set v' : ↥E.solSpace := ⟨v, hv⟩
  change u'.val = v'.val
  suffices h' : u' = v' from h' ▸ rfl
  rw [← E.toInit.toEquiv.apply_eq_iff_eq, LinearEquiv.coe_toEquiv]
  ext x
  exact mod_cast h (mem_range.mpr x.2)
def tupleSucc : (Fin E.order → α) →ₗ[α] Fin E.order → α where
  toFun X i := if h : (i : ℕ) + 1 < E.order then X ⟨i + 1, h⟩ else ∑ i, E.coeffs i * X i
  map_add' x y := by
    ext i
    simp only
    split_ifs with h <;> simp [h, mul_add, sum_add_distrib]
  map_smul' x y := by
    ext i
    simp only
    split_ifs with h <;> simp [h, mul_sum]
    exact sum_congr rfl fun x _ ↦ by ac_rfl
end CommSemiring
section StrongRankCondition
variable {α : Type*} [CommRing α] [StrongRankCondition α] (E : LinearRecurrence α)
theorem solSpace_rank : Module.rank α E.solSpace = E.order :=
  letI := nontrivial_of_invariantBasisNumber α
  @rank_fin_fun α _ _ E.order ▸ E.toInit.rank_eq
end StrongRankCondition
section CommRing
variable {α : Type*} [CommRing α] (E : LinearRecurrence α)
def charPoly : α[X] :=
  Polynomial.monomial E.order 1 - ∑ i : Fin E.order, Polynomial.monomial i (E.coeffs i)
theorem geom_sol_iff_root_charPoly (q : α) :
    (E.IsSolution fun n ↦ q ^ n) ↔ E.charPoly.IsRoot q := by
  rw [charPoly, Polynomial.IsRoot.def, Polynomial.eval]
  simp only [Polynomial.eval₂_finset_sum, one_mul, RingHom.id_apply, Polynomial.eval₂_monomial,
    Polynomial.eval₂_sub]
  constructor
  · intro h
    simpa [sub_eq_zero] using h 0
  · intro h n
    simp only [pow_add, sub_eq_zero.mp h, mul_sum]
    exact sum_congr rfl fun _ _ ↦ by ring
end CommRing
end LinearRecurrence