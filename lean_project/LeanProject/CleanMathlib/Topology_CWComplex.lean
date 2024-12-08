import Mathlib.Topology.Category.TopCat.Limits.Basic
import Mathlib.Topology.Category.TopCat.Sphere
import Mathlib.CategoryTheory.Limits.Shapes.Products
import Mathlib.CategoryTheory.Functor.OfSequence
open CategoryTheory TopCat
universe u
namespace RelativeCWComplex
def sphereInclusion (n : ℤ) : 𝕊 n ⟶ 𝔻 (n + 1) where
  toFun := fun ⟨p, hp⟩ ↦ ⟨p, le_of_eq hp⟩
  continuous_toFun := ⟨fun t ⟨s, ⟨r, hro, hrs⟩, hst⟩ ↦ by
    rw [isOpen_induced_iff, ← hst, ← hrs]
    tauto⟩
structure AttachGeneralizedCells {S D : TopCat.{u}} (f : S ⟶ D) (X X' : TopCat.{u}) where
  cells : Type u
  attachMaps : cells → (S ⟶ X)
  iso_pushout : X' ≅ Limits.pushout (Limits.Sigma.desc attachMaps) (Limits.Sigma.map fun _ ↦ f)
def AttachCells (n : ℤ) := AttachGeneralizedCells (sphereInclusion n)
end RelativeCWComplex
structure RelativeCWComplex where
  sk : ℕ → TopCat.{u}
  attachCells (n : ℕ) : RelativeCWComplex.AttachCells ((n : ℤ) - 1) (sk n) (sk (n + 1))
structure CWComplex extends RelativeCWComplex.{u} where
  isEmpty_sk_zero : IsEmpty (sk 0)
namespace RelativeCWComplex
noncomputable section Topology
def AttachGeneralizedCells.inclusion {S D : TopCat.{u}} {f : S ⟶ D} {X X' : TopCat.{u}}
    (att : AttachGeneralizedCells f X X') : X ⟶ X' :=
  Limits.pushout.inl _ _ ≫ att.iso_pushout.inv
def skInclusion (X : RelativeCWComplex.{u}) (n : ℕ) : X.sk n ⟶ X.sk (n + 1) :=
  (X.attachCells n).inclusion
def toTopCat (X : RelativeCWComplex.{u}) : TopCat.{u} :=
  Limits.colimit (Functor.ofSequence X.skInclusion)
instance : Coe RelativeCWComplex TopCat where coe X := toTopCat X
end Topology
end RelativeCWComplex