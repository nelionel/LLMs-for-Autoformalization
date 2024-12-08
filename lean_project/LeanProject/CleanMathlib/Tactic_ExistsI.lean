import Mathlib.Init
namespace Mathlib.Tactic
macro "existsi " es:term,+ : tactic =>
  `(tactic| refine ⟨$es,*, ?_⟩)
end Mathlib.Tactic