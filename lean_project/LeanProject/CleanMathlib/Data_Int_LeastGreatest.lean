import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Data.Nat.Find
namespace Int
def leastOfBdd {P : ℤ → Prop} [DecidablePred P] (b : ℤ) (Hb : ∀ z : ℤ, P z → b ≤ z)
    (Hinh : ∃ z : ℤ, P z) : { lb : ℤ // P lb ∧ ∀ z : ℤ, P z → lb ≤ z } :=
  have EX : ∃ n : ℕ, P (b + n) :=
    let ⟨elt, Helt⟩ := Hinh
    match elt, le.dest (Hb _ Helt), Helt with
    | _, ⟨n, rfl⟩, Hn => ⟨n, Hn⟩
  ⟨b + (Nat.find EX : ℤ), Nat.find_spec EX, fun z h =>
    match z, le.dest (Hb _ h), h with
    | _, ⟨_, rfl⟩, h => add_le_add_left (Int.ofNat_le.2 <| Nat.find_min' _ h) _⟩
theorem exists_least_of_bdd
    {P : ℤ → Prop}
    (Hbdd : ∃ b : ℤ , ∀ z : ℤ , P z → b ≤ z)
    (Hinh : ∃ z : ℤ , P z) : ∃ lb : ℤ , P lb ∧ ∀ z : ℤ , P z → lb ≤ z := by
  classical
  let ⟨b , Hb⟩ := Hbdd
  let ⟨lb , H⟩ := leastOfBdd b Hb Hinh
  exact ⟨lb , H⟩
theorem coe_leastOfBdd_eq {P : ℤ → Prop} [DecidablePred P] {b b' : ℤ} (Hb : ∀ z : ℤ, P z → b ≤ z)
    (Hb' : ∀ z : ℤ, P z → b' ≤ z) (Hinh : ∃ z : ℤ, P z) :
    (leastOfBdd b Hb Hinh : ℤ) = leastOfBdd b' Hb' Hinh := by
  rcases leastOfBdd b Hb Hinh with ⟨n, hn, h2n⟩
  rcases leastOfBdd b' Hb' Hinh with ⟨n', hn', h2n'⟩
  exact le_antisymm (h2n _ hn') (h2n' _ hn)
def greatestOfBdd {P : ℤ → Prop} [DecidablePred P] (b : ℤ) (Hb : ∀ z : ℤ, P z → z ≤ b)
    (Hinh : ∃ z : ℤ, P z) : { ub : ℤ // P ub ∧ ∀ z : ℤ, P z → z ≤ ub } :=
  have Hbdd' : ∀ z : ℤ, P (-z) → -b ≤ z := fun _ h => neg_le.1 (Hb _ h)
  have Hinh' : ∃ z : ℤ, P (-z) :=
    let ⟨elt, Helt⟩ := Hinh
    ⟨-elt, by rw [neg_neg]; exact Helt⟩
  let ⟨lb, Plb, al⟩ := leastOfBdd (-b) Hbdd' Hinh'
  ⟨-lb, Plb, fun z h => le_neg.1 <| al _ <| by rwa [neg_neg]⟩
theorem exists_greatest_of_bdd
    {P : ℤ → Prop}
    (Hbdd : ∃ b : ℤ , ∀ z : ℤ , P z → z ≤ b)
    (Hinh : ∃ z : ℤ , P z) : ∃ ub : ℤ , P ub ∧ ∀ z : ℤ , P z → z ≤ ub := by
  classical
  let ⟨b, Hb⟩ := Hbdd
  let ⟨lb, H⟩ := greatestOfBdd b Hb Hinh
  exact ⟨lb, H⟩
theorem coe_greatestOfBdd_eq {P : ℤ → Prop} [DecidablePred P] {b b' : ℤ}
    (Hb : ∀ z : ℤ, P z → z ≤ b) (Hb' : ∀ z : ℤ, P z → z ≤ b') (Hinh : ∃ z : ℤ, P z) :
    (greatestOfBdd b Hb Hinh : ℤ) = greatestOfBdd b' Hb' Hinh := by
  rcases greatestOfBdd b Hb Hinh with ⟨n, hn, h2n⟩
  rcases greatestOfBdd b' Hb' Hinh with ⟨n', hn', h2n'⟩
  exact le_antisymm (h2n' _ hn) (h2n _ hn')
end Int