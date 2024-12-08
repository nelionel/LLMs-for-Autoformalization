import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.CategoryTheory.MorphismProperty.Comma
universe t u
universe u₂ u₁ v₂ v₁
open CategoryTheory MorphismProperty
namespace AlgebraicGeometry
abbrev IsEtale {X Y : Scheme.{u}} (f : X ⟶ Y) := IsSmoothOfRelativeDimension 0 f
namespace IsEtale
variable {X : Scheme.{u}}
instance : IsStableUnderBaseChange @IsEtale :=
  isSmoothOfRelativeDimension_isStableUnderBaseChange 0
end IsEtale
def Etale (X : Scheme.{u}) : Type _ := MorphismProperty.Over @IsEtale ⊤ X
variable (X : Scheme.{u})
instance : Category (Etale X) :=
  inferInstanceAs <| Category (MorphismProperty.Over @IsEtale ⊤ X)
def Etale.forget : Etale X ⥤ Over X :=
  MorphismProperty.Over.forget @IsEtale ⊤ X
def Etale.forgetFullyFaithful : (Etale.forget X).FullyFaithful :=
  MorphismProperty.Comma.forgetFullyFaithful _ _ _
instance : (Etale.forget X).Full :=
  inferInstanceAs <| (MorphismProperty.Comma.forget _ _ _ _ _).Full
instance : (Etale.forget X).Faithful :=
  inferInstanceAs <| (MorphismProperty.Comma.forget _ _ _ _ _).Faithful
end AlgebraicGeometry