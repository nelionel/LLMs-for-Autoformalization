import Mathlib.Dynamics.BirkhoffSum.Basic
import Mathlib.Algebra.Module.Basic
open Finset
section birkhoffAverage
variable (R : Type*) {α M : Type*} [DivisionSemiring R] [AddCommMonoid M] [Module R M]
def birkhoffAverage (f : α → α) (g : α → M) (n : ℕ) (x : α) : M := (n : R)⁻¹ • birkhoffSum f g n x
theorem birkhoffAverage_zero (f : α → α) (g : α → M) (x : α) :
    birkhoffAverage R f g 0 x = 0 := by simp [birkhoffAverage]
@[simp] theorem birkhoffAverage_zero' (f : α → α) (g : α → M) : birkhoffAverage R f g 0 = 0 :=
  funext <| birkhoffAverage_zero _ _ _
theorem birkhoffAverage_one (f : α → α) (g : α → M) (x : α) :
    birkhoffAverage R f g 1 x = g x := by simp [birkhoffAverage]
@[simp]
theorem birkhoffAverage_one' (f : α → α) (g : α → M) : birkhoffAverage R f g 1 = g :=
  funext <| birkhoffAverage_one R f g
theorem map_birkhoffAverage (S : Type*) {F N : Type*}
    [DivisionSemiring S] [AddCommMonoid N] [Module S N] [FunLike F M N]
    [AddMonoidHomClass F M N] (g' : F) (f : α → α) (g : α → M) (n : ℕ) (x : α) :
    g' (birkhoffAverage R f g n x) = birkhoffAverage S f (g' ∘ g) n x := by
  simp only [birkhoffAverage, map_inv_natCast_smul g' R S, map_birkhoffSum]
theorem birkhoffAverage_congr_ring (S : Type*) [DivisionSemiring S] [Module S M]
    (f : α → α) (g : α → M) (n : ℕ) (x : α) :
    birkhoffAverage R f g n x = birkhoffAverage S f g n x :=
  map_birkhoffAverage R S (AddMonoidHom.id M) f g n x
theorem birkhoffAverage_congr_ring' (S : Type*) [DivisionSemiring S] [Module S M] :
    birkhoffAverage (α := α) (M := M) R = birkhoffAverage S := by
  ext; apply birkhoffAverage_congr_ring
theorem Function.IsFixedPt.birkhoffAverage_eq [CharZero R] {f : α → α} {x : α} (h : IsFixedPt f x)
    (g : α → M) {n : ℕ} (hn : n ≠ 0) : birkhoffAverage R f g n x = g x := by
  rw [birkhoffAverage, h.birkhoffSum_eq, ← Nat.cast_smul_eq_nsmul R, inv_smul_smul₀]
  rwa [Nat.cast_ne_zero]
end birkhoffAverage
theorem birkhoffAverage_apply_sub_birkhoffAverage {α M : Type*} (R : Type*) [DivisionRing R]
    [AddCommGroup M] [Module R M] (f : α → α) (g : α → M) (n : ℕ) (x : α) :
    birkhoffAverage R f g n (f x) - birkhoffAverage R f g n x =
      (n : R)⁻¹ • (g (f^[n] x) - g x) := by
  simp only [birkhoffAverage, birkhoffSum_apply_sub_birkhoffSum, ← smul_sub]