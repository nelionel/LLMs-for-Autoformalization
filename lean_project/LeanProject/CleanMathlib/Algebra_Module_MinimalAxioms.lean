import Mathlib.Algebra.Module.Defs
universe u v
abbrev Module.ofMinimalAxioms {R : Type u} {M : Type v} [Semiring R] [AddCommGroup M] [SMul R M]
    (smul_add : ∀ (r : R) (x y : M), r • (x + y) = r • x + r • y)
    (add_smul : ∀ (r s : R) (x : M), (r + s) • x = r • x + s • x)
    (mul_smul : ∀ (r s : R) (x : M), (r * s) • x = r • s • x)
    (one_smul : ∀ x : M, (1 : R) • x = x) : Module R M :=
  { smul_add := smul_add,
    add_smul := add_smul,
    mul_smul := mul_smul,
    one_smul := one_smul,
    zero_smul := fun x =>
      (AddMonoidHom.mk' (· • x) fun r s => add_smul r s x).map_zero
    smul_zero := fun r => (AddMonoidHom.mk' (r • ·) (smul_add r)).map_zero }