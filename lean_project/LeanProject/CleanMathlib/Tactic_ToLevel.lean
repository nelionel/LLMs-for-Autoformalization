import Mathlib.Tactic.PPWithUniv
namespace Lean
@[pp_with_univ]
class ToLevel.{u} where
  toLevel : Level
  univ : Type u := Sort u
export ToLevel (toLevel)
attribute [pp_with_univ] toLevel
instance : ToLevel.{0} where
  toLevel := .zero
universe u v
instance [ToLevel.{u}] : ToLevel.{u+1} where
  toLevel := .succ toLevel.{u}
def ToLevel.max [ToLevel.{u}] [ToLevel.{v}] : ToLevel.{max u v} where
  toLevel := .max toLevel.{u} toLevel.{v}
def ToLevel.imax [ToLevel.{u}] [ToLevel.{v}] : ToLevel.{imax u v} where
  toLevel := .imax toLevel.{u} toLevel.{v}
end Lean