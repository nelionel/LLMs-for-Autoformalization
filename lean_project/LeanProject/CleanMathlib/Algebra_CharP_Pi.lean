import Mathlib.Algebra.CharP.Defs
import Mathlib.Algebra.Ring.Pi
universe u v
namespace CharP
instance pi (ι : Type u) [hi : Nonempty ι] (R : Type v) [Semiring R] (p : ℕ) [CharP R p] :
    CharP (ι → R) p :=
  ⟨fun x =>
    let ⟨i⟩ := hi
    Iff.symm <|
      (CharP.cast_eq_zero_iff R p x).symm.trans
        ⟨fun h =>
          funext fun j =>
            show Pi.evalRingHom (fun _ => R) j (↑x : ι → R) = 0 by rw [map_natCast, h],
          fun h => map_natCast (Pi.evalRingHom (fun _ : ι => R) i) x ▸ by rw [h, RingHom.map_zero]⟩⟩
instance pi' (ι : Type u) [Nonempty ι] (R : Type v) [CommRing R] (p : ℕ) [CharP R p] :
    CharP (ι → R) p :=
  CharP.pi ι R p
end CharP