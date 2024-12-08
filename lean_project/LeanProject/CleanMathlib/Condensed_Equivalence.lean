import Mathlib.Topology.Category.Profinite.EffectiveEpi
import Mathlib.Topology.Category.Stonean.EffectiveEpi
import Mathlib.Condensed.Basic
import Mathlib.CategoryTheory.Sites.Coherent.SheafComparison
universe u
open CategoryTheory Limits
namespace Condensed
namespace StoneanCompHaus
noncomputable
def equivalence (A : Type*) [Category A]
    [∀ X, HasLimitsOfShape (StructuredArrow X Stonean.toCompHaus.op) A] :
    Sheaf (coherentTopology Stonean) A ≌ Condensed.{u} A :=
  coherentTopology.equivalence' Stonean.toCompHaus A
end StoneanCompHaus
namespace StoneanProfinite
instance : Stonean.toProfinite.PreservesEffectiveEpis where
  preserves f h :=
    ((Profinite.effectiveEpi_tfae _).out 0 2).mpr (((Stonean.effectiveEpi_tfae _).out 0 2).mp h)
instance : Stonean.toProfinite.ReflectsEffectiveEpis where
  reflects f h :=
    ((Stonean.effectiveEpi_tfae f).out 0 2).mpr (((Profinite.effectiveEpi_tfae _).out 0 2).mp h)
noncomputable def stoneanToProfiniteEffectivePresentation (X : Profinite) :
    Stonean.toProfinite.EffectivePresentation X where
  p := X.presentation
  f := Profinite.presentation.π X
  effectiveEpi := ((Profinite.effectiveEpi_tfae _).out 0 1).mpr (inferInstance : Epi _)
instance : Stonean.toProfinite.EffectivelyEnough where
  presentation X := ⟨stoneanToProfiniteEffectivePresentation X⟩
noncomputable
def equivalence (A : Type*) [Category A]
    [∀ X, HasLimitsOfShape (StructuredArrow X Stonean.toProfinite.op) A] :
    Sheaf (coherentTopology Stonean) A ≌ Sheaf (coherentTopology Profinite) A :=
  coherentTopology.equivalence' Stonean.toProfinite A
end StoneanProfinite
namespace ProfiniteCompHaus
noncomputable
def equivalence (A : Type*) [Category A]
    [∀ X, HasLimitsOfShape (StructuredArrow X profiniteToCompHaus.op) A] :
    Sheaf (coherentTopology Profinite) A ≌ Condensed.{u} A :=
  coherentTopology.equivalence' profiniteToCompHaus A
end ProfiniteCompHaus
variable {A : Type*} [Category A] (X : Condensed.{u} A)
lemma isSheafProfinite
    [∀ Y, HasLimitsOfShape (StructuredArrow Y profiniteToCompHaus.{u}.op) A] :
    Presheaf.IsSheaf (coherentTopology Profinite)
    (profiniteToCompHaus.op ⋙ X.val) :=
  ((ProfiniteCompHaus.equivalence A).inverse.obj X).cond
lemma isSheafStonean
    [∀ Y, HasLimitsOfShape (StructuredArrow Y Stonean.toCompHaus.{u}.op) A] :
    Presheaf.IsSheaf (coherentTopology Stonean)
    (Stonean.toCompHaus.op ⋙ X.val) :=
  ((StoneanCompHaus.equivalence A).inverse.obj X).cond
end Condensed