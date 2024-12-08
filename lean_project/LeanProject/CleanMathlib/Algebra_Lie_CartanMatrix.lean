import Mathlib.Algebra.Lie.Free
import Mathlib.Algebra.Lie.Quotient
import Mathlib.Data.Matrix.Notation
universe u v w
noncomputable section
variable (R : Type u) {B : Type v} [CommRing R]
variable (A : Matrix B B ℤ)
namespace CartanMatrix
variable (B)
inductive Generators
  | H : B → Generators
  | E : B → Generators
  | F : B → Generators
instance [Inhabited B] : Inhabited (Generators B) :=
  ⟨Generators.H default⟩
variable {B}
namespace Relations
open Function
local notation "H" => FreeLieAlgebra.of R ∘ Generators.H
local notation "E" => FreeLieAlgebra.of R ∘ Generators.E
local notation "F" => FreeLieAlgebra.of R ∘ Generators.F
local notation "ad" => LieAlgebra.ad R (FreeLieAlgebra R (Generators B))
def HH : B × B → FreeLieAlgebra R (Generators B) :=
  uncurry fun i j => ⁅H i, H j⁆
def EF [DecidableEq B] : B × B → FreeLieAlgebra R (Generators B) :=
  uncurry fun i j => if i = j then ⁅E i, F i⁆ - H i else ⁅E i, F j⁆
def HE : B × B → FreeLieAlgebra R (Generators B) :=
  uncurry fun i j => ⁅H i, E j⁆ - A i j • E j
def HF : B × B → FreeLieAlgebra R (Generators B) :=
  uncurry fun i j => ⁅H i, F j⁆ + A i j • F j
def adE : B × B → FreeLieAlgebra R (Generators B) :=
  uncurry fun i j => ad (E i) ^ (-A i j).toNat <| ⁅E i, E j⁆
def adF : B × B → FreeLieAlgebra R (Generators B) :=
  uncurry fun i j => ad (F i) ^ (-A i j).toNat <| ⁅F i, F j⁆
private theorem adE_of_eq_eq_zero (i : B) (h : A i i = 2) : adE R A ⟨i, i⟩ = 0 := by
  have h' : (-2 : ℤ).toNat = 0 := rfl
  simp [adE, h, h']
private theorem adF_of_eq_eq_zero (i : B) (h : A i i = 2) : adF R A ⟨i, i⟩ = 0 := by
  have h' : (-2 : ℤ).toNat = 0 := rfl
  simp [adF, h, h']
def toSet [DecidableEq B] : Set (FreeLieAlgebra R (Generators B)) :=
  (Set.range <| HH R) ∪ (Set.range <| EF R) ∪ (Set.range <| HE R A) ∪ (Set.range <| HF R A) ∪
      (Set.range <| adE R A) ∪
    (Set.range <| adF R A)
def toIdeal [DecidableEq B] : LieIdeal R (FreeLieAlgebra R (Generators B)) :=
  LieSubmodule.lieSpan R _ <| toSet R A
end Relations
end CartanMatrix
variable [DecidableEq B]
def Matrix.ToLieAlgebra :=
  FreeLieAlgebra R _ ⧸ CartanMatrix.Relations.toIdeal R A
instance Matrix.ToLieAlgebra.instLieRing : LieRing (Matrix.ToLieAlgebra R A) :=
  inferInstanceAs (LieRing (FreeLieAlgebra R _ ⧸ CartanMatrix.Relations.toIdeal R A))
instance Matrix.ToLieAlgebra.instInhabited : Inhabited (Matrix.ToLieAlgebra R A) :=
  inferInstanceAs (Inhabited (FreeLieAlgebra R _ ⧸ CartanMatrix.Relations.toIdeal R A))
instance Matrix.ToLieAlgebra.instLieAlgebra : LieAlgebra R (Matrix.ToLieAlgebra R A) :=
  inferInstanceAs (LieAlgebra R (FreeLieAlgebra R _ ⧸ CartanMatrix.Relations.toIdeal R A))
namespace CartanMatrix
def E₆ : Matrix (Fin 6) (Fin 6) ℤ :=
  !![2, 0, -1, 0, 0, 0;
    0, 2, 0, -1, 0, 0;
    -1, 0, 2, -1, 0, 0;
    0, -1, -1, 2, -1, 0;
    0, 0, 0, -1, 2, -1;
    0, 0, 0, 0, -1, 2]
def E₇ : Matrix (Fin 7) (Fin 7) ℤ :=
  !![2, 0, -1, 0, 0, 0, 0;
    0, 2, 0, -1, 0, 0, 0;
    -1, 0, 2, -1, 0, 0, 0;
    0, -1, -1, 2, -1, 0, 0;
    0, 0, 0, -1, 2, -1, 0;
    0, 0, 0, 0, -1, 2, -1;
    0, 0, 0, 0, 0, -1, 2]
def E₈ : Matrix (Fin 8) (Fin 8) ℤ :=
  !![2, 0, -1, 0, 0, 0, 0, 0;
    0, 2, 0, -1, 0, 0, 0, 0;
    -1, 0, 2, -1, 0, 0, 0, 0;
    0, -1, -1, 2, -1, 0, 0, 0;
    0, 0, 0, -1, 2, -1, 0, 0;
    0, 0, 0, 0, -1, 2, -1, 0;
    0, 0, 0, 0, 0, -1, 2, -1;
    0, 0, 0, 0, 0, 0, -1, 2]
def F₄ : Matrix (Fin 4) (Fin 4) ℤ :=
  !![2, -1, 0, 0; -1, 2, -2, 0; 0, -1, 2, -1; 0, 0, -1, 2]
def G₂ : Matrix (Fin 2) (Fin 2) ℤ :=
  !![2, -3; -1, 2]
end CartanMatrix
namespace LieAlgebra
abbrev e₆ :=
  CartanMatrix.E₆.ToLieAlgebra R
abbrev e₇ :=
  CartanMatrix.E₇.ToLieAlgebra R
abbrev e₈ :=
  CartanMatrix.E₈.ToLieAlgebra R
abbrev f₄ :=
  CartanMatrix.F₄.ToLieAlgebra R
abbrev g₂ :=
  CartanMatrix.G₂.ToLieAlgebra R
end LieAlgebra