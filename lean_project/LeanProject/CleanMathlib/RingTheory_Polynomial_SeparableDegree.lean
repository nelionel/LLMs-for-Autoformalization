import Mathlib.Algebra.Algebra.Defs
import Mathlib.FieldTheory.Separable
noncomputable section
namespace Polynomial
open scoped Classical
open Polynomial
section CommSemiring
variable {F : Type*} [CommSemiring F] (q : ℕ)
def IsSeparableContraction (f : F[X]) (g : F[X]) : Prop :=
  g.Separable ∧ ∃ m : ℕ, expand F (q ^ m) g = f
def HasSeparableContraction (f : F[X]) : Prop :=
  ∃ g : F[X], IsSeparableContraction q f g
variable {q} {f : F[X]} (hf : HasSeparableContraction q f)
def HasSeparableContraction.contraction : F[X] :=
  Classical.choose hf
def HasSeparableContraction.degree : ℕ :=
  hf.contraction.natDegree
theorem HasSeparableContraction.isSeparableContraction :
    IsSeparableContraction q f hf.contraction := Classical.choose_spec hf
theorem IsSeparableContraction.dvd_degree' {g} (hf : IsSeparableContraction q f g) :
    ∃ m : ℕ, g.natDegree * q ^ m = f.natDegree := by
  obtain ⟨m, rfl⟩ := hf.2
  use m
  rw [natDegree_expand]
theorem HasSeparableContraction.dvd_degree' : ∃ m : ℕ, hf.degree * q ^ m = f.natDegree :=
  (Classical.choose_spec hf).dvd_degree'
theorem HasSeparableContraction.dvd_degree : hf.degree ∣ f.natDegree :=
  let ⟨a, ha⟩ := hf.dvd_degree'
  Dvd.intro (q ^ a) ha
theorem HasSeparableContraction.eq_degree {f : F[X]} (hf : HasSeparableContraction 1 f) :
    hf.degree = f.natDegree := by
  let ⟨a, ha⟩ := hf.dvd_degree'
  rw [← ha, one_pow a, mul_one]
end CommSemiring
section Field
variable {F : Type*} [Field F]
variable (q : ℕ) {f : F[X]} (hf : HasSeparableContraction q f)
@[stacks 09H0]
theorem _root_.Irreducible.hasSeparableContraction (q : ℕ) [hF : ExpChar F q] {f : F[X]}
    (irred : Irreducible f) : HasSeparableContraction q f := by
  cases hF
  · exact ⟨f, irred.separable, ⟨0, by rw [pow_zero, expand_one]⟩⟩
  · rcases exists_separable_of_irreducible q irred ‹q.Prime›.ne_zero with ⟨n, g, hgs, hge⟩
    exact ⟨g, hgs, n, hge⟩
theorem contraction_degree_eq_or_insep [hq : NeZero q] [CharP F q] (g g' : F[X]) (m m' : ℕ)
    (h_expand : expand F (q ^ m) g = expand F (q ^ m') g') (hg : g.Separable) (hg' : g'.Separable) :
    g.natDegree = g'.natDegree := by
  wlog hm : m ≤ m'
  · exact (this q g' g m' m h_expand.symm hg' hg (le_of_not_le hm)).symm
  obtain ⟨s, rfl⟩ := exists_add_of_le hm
  rw [pow_add, expand_mul, expand_inj (pow_pos (NeZero.pos q) m)] at h_expand
  subst h_expand
  rcases isUnit_or_eq_zero_of_separable_expand q s (NeZero.pos q) hg with (h | rfl)
  · rw [natDegree_expand, natDegree_eq_zero_of_isUnit h, zero_mul]
  · rw [natDegree_expand, pow_zero, mul_one]
theorem IsSeparableContraction.degree_eq [hF : ExpChar F q] (g : F[X])
    (hg : IsSeparableContraction q f g) : g.natDegree = hf.degree := by
  cases hF
  · rcases hg with ⟨_, m, hm⟩
    rw [one_pow, expand_one] at hm
    rw [hf.eq_degree, hm]
  · rcases hg with ⟨hg, m, hm⟩
    let g' := Classical.choose hf
    obtain ⟨hg', m', hm'⟩ := Classical.choose_spec hf
    haveI : Fact q.Prime := ⟨by assumption⟩
    refine contraction_degree_eq_or_insep q g g' m m' ?_ hg hg'
    rw [hm, hm']
end Field
end Polynomial