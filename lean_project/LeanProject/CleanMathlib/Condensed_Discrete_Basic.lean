import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.Condensed.Basic
import Mathlib.Condensed.Light.Basic
universe u v w
open CategoryTheory Limits Opposite GrothendieckTopology
namespace Condensed
variable (C : Type w) [Category.{u+1} C] [HasWeakSheafify (coherentTopology CompHaus.{u}) C]
@[simps!]
noncomputable def discrete : C ⥤ Condensed.{u} C := constantSheaf _ C
@[simps!]
noncomputable def underlying : Condensed.{u} C ⥤ C :=
  (sheafSections _ _).obj ⟨CompHaus.of PUnit.{u+1}⟩
noncomputable def discreteUnderlyingAdj : discrete C ⊣ underlying C :=
  constantSheafAdj _ _ CompHaus.isTerminalPUnit
end Condensed
namespace LightCondensed
variable (C : Type w) [Category.{u} C] [HasSheafify (coherentTopology LightProfinite.{u}) C]
@[simps!]
noncomputable def discrete : C ⥤ LightCondensed.{u} C := constantSheaf _ C
@[simps!]
noncomputable def underlying : LightCondensed.{u} C ⥤ C :=
  (sheafSections _ _).obj (op (LightProfinite.of PUnit))
noncomputable def discreteUnderlyingAdj : discrete C ⊣ underlying C :=
  constantSheafAdj _ _ CompHausLike.isTerminalPUnit
end LightCondensed
noncomputable abbrev LightCondSet.discrete := LightCondensed.discrete (Type u)
noncomputable abbrev LightCondSet.underlying := LightCondensed.underlying (Type u)
noncomputable abbrev LightCondSet.discreteUnderlyingAdj : discrete ⊣ underlying :=
  LightCondensed.discreteUnderlyingAdj _