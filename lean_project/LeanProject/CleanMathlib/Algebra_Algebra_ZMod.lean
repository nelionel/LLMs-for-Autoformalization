import Mathlib.Algebra.Algebra.Defs
import Mathlib.Data.ZMod.Basic
namespace ZMod
variable (R : Type*) [Ring R]
instance (p : ℕ) : Subsingleton (Algebra (ZMod p) R) :=
  ⟨fun _ _ => Algebra.algebra_ext _ _ <| RingHom.congr_fun <| Subsingleton.elim _ _⟩
section
variable {n : ℕ} (m : ℕ) [CharP R m]
abbrev algebra' (h : m ∣ n) : Algebra (ZMod n) R :=
  { ZMod.castHom h R with
    smul := fun a r => cast a * r
    commutes' := fun a r =>
      show (cast a * r : R) = r * cast a by
        rcases ZMod.intCast_surjective a with ⟨k, rfl⟩
        show ZMod.castHom h R k * r = r * ZMod.castHom h R k
        rw [map_intCast, Int.cast_comm]
    smul_def' := fun _ _ => rfl }
end
abbrev algebra (p : ℕ) [CharP R p] : Algebra (ZMod p) R :=
  algebra' R p dvd_rfl
end ZMod