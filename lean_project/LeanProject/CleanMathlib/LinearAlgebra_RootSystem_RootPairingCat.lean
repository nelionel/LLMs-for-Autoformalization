import Mathlib.LinearAlgebra.RootSystem.Hom
import Mathlib.CategoryTheory.Category.Basic
open Set Function CategoryTheory
noncomputable section
universe v u
variable {R : Type u} [CommRing R]
structure RootPairingCat (R : Type u) [CommRing R] where
  weight : Type v
  [weightIsAddCommGroup : AddCommGroup weight]
  [weightIsModule : Module R weight]
  coweight : Type v
  [coweightIsAddCommGroup : AddCommGroup coweight]
  [coweightIsModule : Module R coweight]
  index : Type v
  pairing : RootPairing index R weight coweight
attribute [instance] RootPairingCat.weightIsAddCommGroup RootPairingCat.weightIsModule
attribute [instance] RootPairingCat.coweightIsAddCommGroup RootPairingCat.coweightIsModule
namespace RootPairingCat
instance category : Category.{v, max (v+1) u} (RootPairingCat.{v} R) where
  Hom P Q := RootPairing.Hom P.pairing Q.pairing
  id P := RootPairing.Hom.id P.pairing
  comp f g := RootPairing.Hom.comp g f
end RootPairingCat