import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.CategoryTheory.Comma.OverClass
namespace AlgebraicGeometry.Scheme
universe u
open CategoryTheory
variable {X Y : Scheme.{u}} (f : X.Hom Y) (S S' : Scheme.{u})
protected abbrev Over (X S : Scheme.{u}) := OverClass X S
abbrev CanonicallyOver := CanonicallyOverClass X S
abbrev Hom.IsOver (f : X.Hom Y) (S : Scheme.{u}) [X.Over S] [Y.Over S] := HomIsOver f S
@[simp]
lemma Hom.isOver_iff [X.Over S] [Y.Over S] {f : X ⟶ Y} : f.IsOver S ↔ f ≫ Y ↘ S = X ↘ S :=
  ⟨fun H ↦ H.1, fun h ↦ ⟨h⟩⟩
abbrev asOver (X S : Scheme.{u}) [X.Over S] := OverClass.asOver X S
abbrev Hom.asOver (f : X.Hom Y) (S : Scheme.{u}) [X.Over S] [Y.Over S] [f.IsOver S] :=
  OverClass.asOverHom S f
end AlgebraicGeometry.Scheme