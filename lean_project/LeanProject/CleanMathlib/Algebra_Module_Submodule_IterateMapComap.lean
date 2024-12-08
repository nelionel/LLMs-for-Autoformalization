import Mathlib.Algebra.Module.Submodule.Ker
open Function Submodule
namespace LinearMap
variable {R N M : Type*} [Semiring R] [AddCommMonoid N] [Module R N]
  [AddCommMonoid M] [Module R M] (f i : N →ₗ[R] M)
def iterateMapComap (n : ℕ) := (fun K : Submodule R N ↦ (K.map i).comap f)^[n]
theorem iterateMapComap_le_succ (K : Submodule R N) (h : K.map f ≤ K.map i) (n : ℕ) :
    f.iterateMapComap i n K ≤ f.iterateMapComap i (n + 1) K := by
  nth_rw 2 [iterateMapComap]
  rw [iterate_succ', Function.comp_apply, ← iterateMapComap, ← map_le_iff_le_comap]
  induction n with
  | zero => exact h
  | succ n ih =>
    simp_rw [iterateMapComap, iterate_succ', Function.comp_apply]
    calc
      _ ≤ (f.iterateMapComap i n K).map i := map_comap_le _ _
      _ ≤ (((f.iterateMapComap i n K).map f).comap f).map i := map_mono (le_comap_map _ _)
      _ ≤ _ := map_mono (comap_mono ih)
theorem iterateMapComap_eq_succ (K : Submodule R N)
    (m : ℕ) (heq : f.iterateMapComap i m K = f.iterateMapComap i (m + 1) K)
    (hf : Surjective f) (hi : Injective i) (n : ℕ) :
    f.iterateMapComap i n K = f.iterateMapComap i (n + 1) K := by
  induction n with
  | zero =>
    contrapose! heq
    induction m with
    | zero => exact heq
    | succ m ih =>
      rw [iterateMapComap, iterateMapComap, iterate_succ', iterate_succ']
      exact fun H ↦ ih (map_injective_of_injective hi (comap_injective_of_surjective hf H))
  | succ n ih =>
    rw [iterateMapComap, iterateMapComap, iterate_succ', iterate_succ',
      Function.comp_apply, Function.comp_apply, ← iterateMapComap, ← iterateMapComap, ih]
theorem ker_le_of_iterateMapComap_eq_succ (K : Submodule R N)
    (m : ℕ) (heq : f.iterateMapComap i m K = f.iterateMapComap i (m + 1) K)
    (hf : Surjective f) (hi : Injective i) : LinearMap.ker f ≤ K := by
  rw [show K = _ from f.iterateMapComap_eq_succ i K m heq hf hi 0]
  exact f.ker_le_comap
end LinearMap