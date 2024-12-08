import Mathlib.Data.Nat.Find
import Mathlib.Data.PNat.Basic
namespace PNat
variable {p q : ℕ+ → Prop} [DecidablePred p] [DecidablePred q] (h : ∃ n, p n)
instance decidablePredExistsNat : DecidablePred fun n' : ℕ => ∃ (n : ℕ+) (_ : n' = n), p n :=
  fun n' =>
  decidable_of_iff' (∃ h : 0 < n', p ⟨n', h⟩) <|
    Subtype.exists.trans <| by
      simp_rw [mk_coe, @exists_comm (_ < _) (_ = _), exists_prop, exists_eq_left']
protected def findX : { n // p n ∧ ∀ m : ℕ+, m < n → ¬p m } := by
  have : ∃ (n' : ℕ) (n : ℕ+) (_ : n' = n), p n := Exists.elim h fun n hn => ⟨n, n, rfl, hn⟩
  have n := Nat.findX this
  refine ⟨⟨n, ?_⟩, ?_, fun m hm pm => ?_⟩
  · obtain ⟨n', hn', -⟩ := n.prop.1
    rw [hn']
    exact n'.prop
  · obtain ⟨n', hn', pn'⟩ := n.prop.1
    simpa [hn', Subtype.coe_eta] using pn'
  · exact n.prop.2 m hm ⟨m, rfl, pm⟩
protected def find : ℕ+ :=
  PNat.findX h
protected theorem find_spec : p (PNat.find h) :=
  (PNat.findX h).prop.left
protected theorem find_min : ∀ {m : ℕ+}, m < PNat.find h → ¬p m :=
  @(PNat.findX h).prop.right
protected theorem find_min' {m : ℕ+} (hm : p m) : PNat.find h ≤ m :=
  le_of_not_lt fun l => PNat.find_min h l hm
variable {n m : ℕ+}
theorem find_eq_iff : PNat.find h = m ↔ p m ∧ ∀ n < m, ¬p n := by
  constructor
  · rintro rfl
    exact ⟨PNat.find_spec h, fun _ => PNat.find_min h⟩
  · rintro ⟨hm, hlt⟩
    exact le_antisymm (PNat.find_min' h hm) (not_lt.1 <| imp_not_comm.1 (hlt _) <| PNat.find_spec h)
@[simp]
theorem find_lt_iff (n : ℕ+) : PNat.find h < n ↔ ∃ m < n, p m :=
  ⟨fun h2 => ⟨PNat.find h, h2, PNat.find_spec h⟩, fun ⟨_, hmn, hm⟩ =>
    (PNat.find_min' h hm).trans_lt hmn⟩
@[simp]
theorem find_le_iff (n : ℕ+) : PNat.find h ≤ n ↔ ∃ m ≤ n, p m := by
  simp only [exists_prop, ← lt_add_one_iff, find_lt_iff]
@[simp]
theorem le_find_iff (n : ℕ+) : n ≤ PNat.find h ↔ ∀ m < n, ¬p m := by
  simp only [← not_lt, find_lt_iff, not_exists, not_and]
@[simp]
theorem lt_find_iff (n : ℕ+) : n < PNat.find h ↔ ∀ m ≤ n, ¬p m := by
  simp only [← add_one_le_iff, le_find_iff, add_le_add_iff_right]
@[simp]
theorem find_eq_one : PNat.find h = 1 ↔ p 1 := by simp [find_eq_iff]
theorem one_le_find : 1 < PNat.find h ↔ ¬p 1 :=
  not_iff_not.mp <| by simp
theorem find_mono (h : ∀ n, q n → p n) {hp : ∃ n, p n} {hq : ∃ n, q n} :
    PNat.find hp ≤ PNat.find hq :=
  PNat.find_min' _ (h _ (PNat.find_spec hq))
theorem find_le {h : ∃ n, p n} (hn : p n) : PNat.find h ≤ n :=
  (PNat.find_le_iff _ _).2 ⟨n, le_rfl, hn⟩
theorem find_comp_succ (h : ∃ n, p n) (h₂ : ∃ n, p (n + 1)) (h1 : ¬p 1) :
    PNat.find h = PNat.find h₂ + 1 := by
  refine (find_eq_iff _).2 ⟨PNat.find_spec h₂, fun n => PNat.recOn n ?_ ?_⟩
  · simp [h1]
  intro m _ hm
  simp only [add_lt_add_iff_right, lt_find_iff] at hm
  exact hm _ le_rfl
end PNat