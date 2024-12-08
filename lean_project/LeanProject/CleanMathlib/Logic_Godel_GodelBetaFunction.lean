import Mathlib.Data.Nat.ModEq
import Mathlib.Data.Nat.ChineseRemainder
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.Nat.Pairing
namespace Nat
lemma coprime_mul_succ {n m a} (h : n ≤ m) (ha : m - n ∣ a) : Coprime (n * a + 1) (m * a + 1) :=
  Nat.coprime_of_dvd fun p pp hn hm => by
    have : p ∣ (m - n) * a := by
      simpa [Nat.succ_sub_succ, ← Nat.mul_sub_right_distrib] using
        Nat.dvd_sub (Nat.succ_le_succ <| Nat.mul_le_mul_right a h) hm hn
    have : p ∣ a := by
      rcases (Nat.Prime.dvd_mul pp).mp this with (hp | hp)
      · exact Nat.dvd_trans hp ha
      · exact hp
    apply pp.ne_one
    simpa [Nat.add_sub_cancel_left] using Nat.dvd_sub (le_add_right _ _) hn (this.mul_left n)
variable {m : ℕ}
private def supOfSeq (a : Fin m → ℕ) : ℕ := max m (Finset.sup .univ a) + 1
private def coprimes (a : Fin m → ℕ) : Fin m → ℕ := fun i => (i + 1) * (supOfSeq a)! + 1
lemma coprimes_lt (a : Fin m → ℕ) (i) : a i < coprimes a i := by
  have h₁ : a i < supOfSeq a :=
    Nat.lt_add_one_iff.mpr (le_max_of_le_right <| Finset.le_sup (by simp))
  have h₂ : supOfSeq a ≤ (i + 1) * (supOfSeq a)! + 1 :=
    le_trans (self_le_factorial _) (le_trans (Nat.le_mul_of_pos_left (supOfSeq a)! (succ_pos i))
      (le_add_right _ _))
  simpa only [coprimes] using lt_of_lt_of_le h₁ h₂
private lemma pairwise_coprime_coprimes (a : Fin m → ℕ) : Pairwise (Coprime on coprimes a) := by
  intro i j hij
  wlog ltij : i < j
  · exact (this a hij.symm (lt_of_le_of_ne (Fin.not_lt.mp ltij) hij.symm)).symm
  unfold Function.onFun coprimes
  have hja : j < supOfSeq a := lt_of_lt_of_le j.prop (le_step (le_max_left _ _))
  exact coprime_mul_succ
    (Nat.succ_le_succ <| le_of_lt ltij)
    (Nat.dvd_factorial (by omega)
      (by simpa only [Nat.succ_sub_succ] using le_of_lt (lt_of_le_of_lt (sub_le j i) hja)))
def beta (n i : ℕ) : ℕ := n.unpair.1 % ((i + 1) * n.unpair.2 + 1)
def unbeta (l : List ℕ) : ℕ :=
  (chineseRemainderOfFinset l.get (coprimes l.get) Finset.univ
    (by simp [coprimes])
    (by simpa using Set.pairwise_univ.mpr (pairwise_coprime_coprimes _)) : ℕ).pair
  (supOfSeq l.get)!
lemma beta_unbeta_coe (l : List ℕ) (i : Fin l.length) : beta (unbeta l) i = l.get i := by
  simpa [beta, unbeta, coprimes] using mod_eq_of_modEq
    ((chineseRemainderOfFinset l.get (coprimes l.get) Finset.univ
      (by simp [coprimes])
      (by simpa using Set.pairwise_univ.mpr (pairwise_coprime_coprimes _))).prop i (by simp))
    (coprimes_lt l.get _)
end Nat