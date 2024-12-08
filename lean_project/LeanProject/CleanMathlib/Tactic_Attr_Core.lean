import Mathlib.Tactic.Attr.Register
attribute [simp] id_map'
attribute [functor_norm, monad_norm] seq_assoc pure_seq pure_bind bind_assoc bind_pure map_pure
attribute [monad_norm] seq_eq_bind_map
attribute [mfld_simps] id and_true true_and Function.comp_apply and_self eq_self not_false
  true_or or_true heq_eq_eq forall_const and_imp
attribute [nontriviality] eq_iff_true_of_subsingleton