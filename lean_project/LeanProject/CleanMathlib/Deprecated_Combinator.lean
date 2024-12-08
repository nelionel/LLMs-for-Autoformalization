import Mathlib.Init
namespace Combinator
universe u v w
variable {α : Sort u} {β : Sort v} {γ : Sort w}
@[deprecated "No deprecation message was provided." (since := "2024-07-27")]
def I (a : α) := a
@[deprecated "No deprecation message was provided." (since := "2024-07-27")]
def K (a : α) (_b : β) := a
@[deprecated "No deprecation message was provided." (since := "2024-07-27")]
def S (x : α → β → γ) (y : α → β) (z : α) := x z (y z)
end Combinator