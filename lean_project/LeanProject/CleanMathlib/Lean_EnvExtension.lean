import Mathlib.Init
import Lean.ScopedEnvExtension
open Lean
instance {σ : Type} [Inhabited σ] : Inhabited (ScopedEnvExtension.State σ) := ⟨{state := default}⟩