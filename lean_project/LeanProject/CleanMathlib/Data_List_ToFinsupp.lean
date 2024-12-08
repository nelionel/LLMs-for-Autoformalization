import Mathlib.Data.Finsupp.Defs
import Mathlib.Data.List.GetD
namespace List
variable {M : Type*} [Zero M] (l : List M) [DecidablePred (getD l · 0 ≠ 0)] (n : ℕ)
def toFinsupp : ℕ →₀ M where
  toFun i := getD l i 0
  support := (Finset.range l.length).filter fun i => getD l i 0 ≠ 0
  mem_support_toFun n := by
    simp only [Ne, Finset.mem_filter, Finset.mem_range, and_iff_right_iff_imp]
    contrapose!
    exact getD_eq_default _ _
@[norm_cast]
theorem coe_toFinsupp : (l.toFinsupp : ℕ → M) = (l.getD · 0) :=
  rfl
@[simp, norm_cast]
theorem toFinsupp_apply (i : ℕ) : (l.toFinsupp : ℕ → M) i = l.getD i 0 :=
  rfl
theorem toFinsupp_support :
    l.toFinsupp.support = (Finset.range l.length).filter (getD l · 0 ≠ 0) :=
  rfl
theorem toFinsupp_apply_lt (hn : n < l.length) : l.toFinsupp n = l[n] :=
  getD_eq_getElem _ _ hn
theorem toFinsupp_apply_fin (n : Fin l.length) : l.toFinsupp n = l[n] :=
  getD_eq_getElem _ _ n.isLt
theorem toFinsupp_apply_le (hn : l.length ≤ n) : l.toFinsupp n = 0 :=
  getD_eq_default _ _ hn
@[simp]
theorem toFinsupp_nil [DecidablePred fun i => getD ([] : List M) i 0 ≠ 0] :
    toFinsupp ([] : List M) = 0 := by
  ext
  simp
theorem toFinsupp_singleton (x : M) [DecidablePred (getD [x] · 0 ≠ 0)] :
    toFinsupp [x] = Finsupp.single 0 x := by
  ext ⟨_ | i⟩ <;> simp [Finsupp.single_apply, (Nat.zero_lt_succ _).ne]
@[deprecated "This lemma is unused, and can be proved by `simp`." (since := "2024-06-12")]
theorem toFinsupp_cons_apply_zero (x : M) (xs : List M)
    [DecidablePred (getD (x::xs) · 0 ≠ 0)] : (x::xs).toFinsupp 0 = x :=
  rfl
@[deprecated "This lemma is unused, and can be proved by `simp`." (since := "2024-06-12")]
theorem toFinsupp_cons_apply_succ (x : M) (xs : List M) (n : ℕ)
    [DecidablePred (getD (x::xs) · 0 ≠ 0)] [DecidablePred (getD xs · 0 ≠ 0)] :
    (x::xs).toFinsupp n.succ = xs.toFinsupp n :=
  rfl
theorem toFinsupp_append {R : Type*} [AddZeroClass R] (l₁ l₂ : List R)
    [DecidablePred (getD (l₁ ++ l₂) · 0 ≠ 0)] [DecidablePred (getD l₁ · 0 ≠ 0)]
    [DecidablePred (getD l₂ · 0 ≠ 0)] :
    toFinsupp (l₁ ++ l₂) =
      toFinsupp l₁ + (toFinsupp l₂).embDomain (addLeftEmbedding l₁.length) := by
  ext n
  simp only [toFinsupp_apply, Finsupp.add_apply]
  cases lt_or_le n l₁.length with
  | inl h =>
    rw [getD_append _ _ _ _ h, Finsupp.embDomain_notin_range, add_zero]
    rintro ⟨k, rfl : length l₁ + k = n⟩
    omega
  | inr h =>
    rcases Nat.exists_eq_add_of_le h with ⟨k, rfl⟩
    rw [getD_append_right _ _ _ _ h, Nat.add_sub_cancel_left, getD_eq_default _ _ h, zero_add]
    exact Eq.symm (Finsupp.embDomain_apply _ _ _)
theorem toFinsupp_cons_eq_single_add_embDomain {R : Type*} [AddZeroClass R] (x : R) (xs : List R)
    [DecidablePred (getD (x::xs) · 0 ≠ 0)] [DecidablePred (getD xs · 0 ≠ 0)] :
    toFinsupp (x::xs) =
      Finsupp.single 0 x + (toFinsupp xs).embDomain ⟨Nat.succ, Nat.succ_injective⟩ := by
  classical
    convert toFinsupp_append [x] xs using 3
    · exact (toFinsupp_singleton x).symm
    · ext n
      exact add_comm n 1
theorem toFinsupp_concat_eq_toFinsupp_add_single {R : Type*} [AddZeroClass R] (x : R) (xs : List R)
    [DecidablePred fun i => getD (xs ++ [x]) i 0 ≠ 0] [DecidablePred fun i => getD xs i 0 ≠ 0] :
    toFinsupp (xs ++ [x]) = toFinsupp xs + Finsupp.single xs.length x := by
  classical rw [toFinsupp_append, toFinsupp_singleton, Finsupp.embDomain_single,
    addLeftEmbedding_apply, add_zero]
theorem toFinsupp_eq_sum_map_enum_single {R : Type*} [AddMonoid R] (l : List R)
    [DecidablePred (getD l · 0 ≠ 0)] :
    toFinsupp l = (l.enum.map fun nr : ℕ × R => Finsupp.single nr.1 nr.2).sum := by
  revert l; intro l
  induction l using List.reverseRecOn with
  | nil => exact toFinsupp_nil
  | append_singleton x xs ih =>
    classical simp [toFinsupp_concat_eq_toFinsupp_add_single, enum_append, ih]
end List