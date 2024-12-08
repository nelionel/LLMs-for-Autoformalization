import Mathlib.RingTheory.LocalProperties.Basic
theorem isReduced_localizationPreserves : LocalizationPreserves fun R _ => IsReduced R := by
  introv R _ _
  constructor
  rintro x ⟨_ | n, e⟩
  · simpa using congr_arg (· * x) e
  obtain ⟨⟨y, m⟩, hx⟩ := IsLocalization.surj M x
  dsimp only at hx
  let hx' := congr_arg (· ^ n.succ) hx
  simp only [mul_pow, e, zero_mul, ← RingHom.map_pow] at hx'
  rw [← (algebraMap R S).map_zero] at hx'
  obtain ⟨m', hm'⟩ := (IsLocalization.eq_iff_exists M S).mp hx'
  apply_fun (· * (m' : R) ^ n) at hm'
  simp only [mul_assoc, zero_mul, mul_zero] at hm'
  rw [← mul_left_comm, ← pow_succ', ← mul_pow] at hm'
  replace hm' := IsNilpotent.eq_zero ⟨_, hm'.symm⟩
  rw [← (IsLocalization.map_units S m).mul_left_inj, hx, zero_mul,
    IsLocalization.map_eq_zero_iff M]
  exact ⟨m', by rw [← hm', mul_comm]⟩
instance {R : Type*} [CommRing R] (M : Submonoid R) [IsReduced R] : IsReduced (Localization M) :=
  isReduced_localizationPreserves M _ inferInstance
theorem isReduced_ofLocalizationMaximal : OfLocalizationMaximal fun R _ => IsReduced R := by
  introv R h
  constructor
  intro x hx
  apply eq_zero_of_localization
  intro J hJ
  specialize h J hJ
  exact (hx.map <| algebraMap R <| Localization.AtPrime J).eq_zero