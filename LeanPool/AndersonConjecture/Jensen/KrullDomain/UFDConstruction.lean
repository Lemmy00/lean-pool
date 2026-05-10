/-
Copyright (c) 2026 FrenzyMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FrenzyMath
-/
import LeanPool.AndersonConjecture.Jensen.KrullDomain.LocUFD
import LeanPool.AndersonConjecture.Jensen.KrullDomain.Nagata
import LeanPool.AndersonConjecture.Jensen.KrullDomain.Prime
import Mathlib.Order.BourbakiWitt

/-!
# Krull domain construction: UFD proof

Shows the intersection subring S is a UFD. Primes of R lying in
the maximal ideal remain prime in S
the localisation of S away
from the product y_1 * y_2 is a UFD
Nagata's criterion then
gives that S itself is a UFD.
-/

noncomputable section

open Cardinal Ideal Polynomial Set Pointwise

variable {T : Type*} [CommRing T] [IsLocalRing T] [IsNoetherianRing T] [IsDomain T]

section MainTheorem

variable [IsAdicComplete (IsLocalRing.maximalIdeal T) T]

omit [IsAdicComplete (IsLocalRing.maximalIdeal T) T] in
/-- R-primes in the maximal ideal are prime in S_sub.
If p is prime in R with (p:T) ∈ M_T, then the image of p in S_sub is prime.
The proof uses denominator clearing in Rbar and coprime prime_in_adjoinLocSet. -/
theorem build_R_prime_in_S
    (R : NSubring T) (x₁ x₂ : T) (y₁ y₂ : R.carrier)
    (S_sub : Subring T) [IsDomain S_sub]
    (hR_le : R.carrier ≤ S_sub)
    (hx₁_trans : Transcendental R.carrier x₁)
    (hx₂_trans : Transcendental R.carrier x₂)
    (hcoprime : ∀ p : R.carrier, Prime p → ¬(p ∣ y₁ ∧ p ∣ y₂))
    (hS_sub_eq : (S_sub : Set T) =
      {t : T | ∃ (a : T) (b : T),
        a ∈ intersectionSet R x₁ x₂ y₁ y₂ ∧
        b ∈ intersectionSet R x₁ x₂ y₁ y₂ ∧
        b ∉ IsLocalRing.maximalIdeal T ∧ t * b = a})
    (hR_prime_div_Rbar : ∀ (p : R.carrier), Prime p → ∀ t ∈ intersectionSet R x₁ x₂ y₁ y₂,
      ∀ (d : T), t = (↑p : T) * d → d ∈ intersectionSet R x₁ x₂ y₁ y₂)
    (_hinv : ∀ (s : S_sub), (s : T) ∉ IsLocalRing.maximalIdeal T → IsUnit s)
    (p : R.carrier) (hp : Prime p)
    (hp_M : (↑p : T) ∈ IsLocalRing.maximalIdeal T) :
    Prime (⟨(↑p : T), hR_le p.2⟩ : S_sub) := by
  haveI : IsDomain R.carrier := NSubring.isDomain R
  haveI : UniqueFactorizationMonoid R.carrier := R.isUFD
  set Rbar := intersectionSet R x₁ x₂ y₁ y₂
  set S_carrier : Set T :=
    {t : T | ∃ (a : T) (b : T), a ∈ Rbar ∧ b ∈ Rbar ∧
      b ∉ IsLocalRing.maximalIdeal T ∧ t * b = a}
  have hS_sub_eq' : (S_sub : Set T) = S_carrier := hS_sub_eq
  have hunit : ∀ (a : T), a ∉ IsLocalRing.maximalIdeal T → IsUnit a :=
    fun a ha => IsLocalRing.notMem_maximalIdeal.mp ha
  have hRbar_one : (1 : T) ∈ Rbar :=
    ⟨⟨C 1, 0, by simp⟩, ⟨C 1, 0, by simp⟩⟩
  have hRbar_mul : ∀ t₁ t₂, t₁ ∈ Rbar → t₂ ∈ Rbar → t₁ * t₂ ∈ Rbar :=
    fun t₁ t₂ ⟨h₁₁, h₁₂⟩ ⟨h₂₁, h₂₂⟩ =>
      ⟨(fun x' y' t₁ t₂ ⟨f₁, n₁, hf₁⟩ ⟨f₂, n₂, hf₂⟩ =>
        ⟨f₁ * f₂, n₁ + n₂, by rw [map_mul, ← hf₁, ← hf₂, pow_add]
                              ring⟩) x₁ y₂ t₁ t₂ h₁₁ h₂₁,
       (fun x' y' t₁ t₂ ⟨f₁, n₁, hf₁⟩ ⟨f₂, n₂, hf₂⟩ =>
        ⟨f₁ * f₂, n₁ + n₂, by rw [map_mul, ← hf₁, ← hf₂, pow_add]
                              ring⟩) x₂ y₁ t₁ t₂ h₁₂ h₂₂⟩
  have hALS_mul : ∀ (x' : T) (y' : R.carrier) (t₁ t₂ : T),
      t₁ ∈ adjoinLocSetY R x' y' → t₂ ∈ adjoinLocSetY R x' y' →
      t₁ * t₂ ∈ adjoinLocSetY R x' y' := by
    intro x' y' t₁ t₂ ⟨f₁, n₁, hf₁⟩ ⟨f₂, n₂, hf₂⟩
    exact ⟨f₁ * f₂, n₁ + n₂, by rw [map_mul, ← hf₁, ← hf₂, pow_add]
                                ring⟩
  have hp_ne : (⟨(↑p : T), hR_le p.2⟩ : S_sub) ≠ 0 := by
    intro h
    exact hp.ne_zero (R.carrier.subtype_injective (congrArg Subtype.val h))
  have hp_nu : ¬ IsUnit (⟨(↑p : T), hR_le p.2⟩ : S_sub) := by
    intro hu
    exact (IsLocalRing.mem_maximalIdeal _).mp hp_M (hu.map S_sub.subtype)
  refine ⟨hp_ne, hp_nu, ?_⟩
  intro ⟨b, hb_mem⟩ ⟨c, hc_mem⟩ ⟨⟨d, hd_mem⟩, hbcpd⟩
  have hbc_T : b * c = (↑p : T) * d := congrArg Subtype.val hbcpd
  have hb_car : b ∈ S_carrier := by rw [← hS_sub_eq']
                                    exact hb_mem
  obtain ⟨ab, bb, hab_Rbar, hbb_Rbar, hbb_notM, hb_eq⟩ := hb_car
  have hc_car : c ∈ S_carrier := by rw [← hS_sub_eq']
                                    exact hc_mem
  obtain ⟨ac, bc, hac_Rbar, hbc_Rbar, hbc_notM, hc_eq⟩ := hc_car
  have hab_ac : ab * ac = (↑p : T) * (d * bb * bc) := by
    have : ab * ac = (b * bb) * (c * bc) := by rw [hb_eq, hc_eq]
    rw [this, show (b * bb) * (c * bc) = b * c * (bb * bc) from by ring,
      hbc_T, show (↑p : T) * d * (bb * bc) = (↑p : T) * (d * bb * bc) from by ring]
  have hab_ac_Rbar := hRbar_mul ab ac hab_Rbar hac_Rbar
  have hcop := hcoprime p hp
  suffices h : (∃ e₁ ∈ Rbar, ab = (↑p : T) * e₁) ∨ (∃ e₂ ∈ Rbar, ac = (↑p : T) * e₂) by
    rcases h with ⟨e₁, he₁_Rbar, hab_pe₁⟩ | ⟨e₂, he₂_Rbar, hac_pe₂⟩
    · left
      have hbb_unit := hunit bb hbb_notM
      obtain ⟨ubb, hubb⟩ := hbb_unit
      have hw_mem : e₁ * ↑ubb⁻¹ ∈ (S_sub : Set T) := by
        rw [hS_sub_eq']
        refine ⟨e₁, bb, he₁_Rbar, hbb_Rbar, hbb_notM, ?_⟩
        rw [← hubb, mul_assoc, ubb.inv_mul, mul_one]
      have hb_pe : b = (↑p : T) * (e₁ * ↑ubb⁻¹) := by
        have h1 : b * bb = (↑p : T) * e₁ := by rw [hb_eq, hab_pe₁]
        calc b = b * bb * ↑ubb⁻¹ := by rw [← hubb, mul_assoc, ubb.mul_inv, mul_one]
          _ = (↑p : T) * e₁ * ↑ubb⁻¹ := by rw [h1]
          _ = (↑p : T) * (e₁ * ↑ubb⁻¹) := by ring
      exact ⟨⟨e₁ * ↑ubb⁻¹, hw_mem⟩, Subtype.ext hb_pe⟩
    · right
      have hbc_unit := hunit bc hbc_notM
      obtain ⟨ubc, hubc⟩ := hbc_unit
      have hw_mem : e₂ * ↑ubc⁻¹ ∈ (S_sub : Set T) := by
        rw [hS_sub_eq']
        refine ⟨e₂, bc, he₂_Rbar, hbc_Rbar, hbc_notM, ?_⟩
        rw [← hubc, mul_assoc, ubc.inv_mul, mul_one]
      have hc_pe : c = (↑p : T) * (e₂ * ↑ubc⁻¹) := by
        have h1 : c * bc = (↑p : T) * e₂ := by rw [hc_eq, hac_pe₂]
        calc c = c * bc * ↑ubc⁻¹ := by rw [← hubc, mul_assoc, ubc.mul_inv, mul_one]
          _ = (↑p : T) * e₂ * ↑ubc⁻¹ := by rw [h1]
          _ = (↑p : T) * (e₂ * ↑ubc⁻¹) := by ring
      exact ⟨⟨e₂ * ↑ubc⁻¹, hw_mem⟩, Subtype.ext hc_pe⟩
  have hd_carrier : d ∈ S_carrier := hS_sub_eq' ▸ hd_mem
  obtain ⟨a_d, b_d, had_Rbar, hbd_Rbar, hbd_notM, hd_eq⟩ := hd_carrier
  have hcleared : ab * (ac * b_d) = (↑p : T) * (a_d * bb * bc) := by
    have h1 : ab * ac * b_d = (↑p : T) * (d * bb * bc) * b_d := by rw [hab_ac]
    have h2 : (↑p : T) * (d * bb * bc) * b_d = (↑p : T) * (d * b_d * (bb * bc)) := by ring
    rw [show ab * (ac * b_d) = ab * ac * b_d from by ring, h1, h2, hd_eq]
    ring
  have hacbd_Rbar : ac * b_d ∈ Rbar := hRbar_mul ac b_d hac_Rbar hbd_Rbar
  have hadbbbc_Rbar : a_d * bb * bc ∈ Rbar :=
    hRbar_mul _ _ (hRbar_mul a_d bb had_Rbar hbb_Rbar) hbc_Rbar
  push Not at hcop
  by_cases hpy₂ : p ∣ y₂
  · have hpy₁ : ¬ p ∣ y₁ := fun h => hcop h hpy₂
    have := prime_in_adjoinLocSet R x₂ y₁ p hx₂_trans hp hpy₁
      ab (ac * b_d) (a_d * bb * bc)
      hab_Rbar.2 (hALS_mul x₂ y₁ ac b_d hac_Rbar.2 hbd_Rbar.2)
      (hALS_mul x₂ y₁ _ _ (hALS_mul x₂ y₁ a_d bb had_Rbar.2 hbb_Rbar.2) hbc_Rbar.2)
      hcleared
    rcases this with ⟨e, he_A₂, hab_eq⟩ | ⟨e, he_A₂, hacbd_eq⟩
    · left
      exact ⟨e, hR_prime_div_Rbar p hp ab hab_Rbar e hab_eq, hab_eq⟩
    · have he_Rbar := hR_prime_div_Rbar p hp (ac * b_d) hacbd_Rbar e hacbd_eq
      obtain ⟨ubd, hubd⟩ := hunit b_d hbd_notM
      have hac_eq : ac = (↑p : T) * (e * ↑ubd⁻¹) := by
        calc ac = ac * b_d * ↑ubd⁻¹ := by rw [← hubd, mul_assoc, ubd.mul_inv, mul_one]
          _ = (↑p : T) * e * ↑ubd⁻¹ := by rw [hacbd_eq]
          _ = (↑p : T) * (e * ↑ubd⁻¹) := by ring
      right
      exact ⟨e * ↑ubd⁻¹, hR_prime_div_Rbar p hp ac hac_Rbar _ hac_eq, hac_eq⟩
  · have := prime_in_adjoinLocSet R x₁ y₂ p hx₁_trans hp hpy₂
      ab (ac * b_d) (a_d * bb * bc)
      hab_Rbar.1 (hALS_mul x₁ y₂ ac b_d hac_Rbar.1 hbd_Rbar.1)
      (hALS_mul x₁ y₂ _ _ (hALS_mul x₁ y₂ a_d bb had_Rbar.1 hbb_Rbar.1) hbc_Rbar.1)
      hcleared
    rcases this with ⟨e, he_A₁, hab_eq⟩ | ⟨e, he_A₁, hacbd_eq⟩
    · left
      exact ⟨e, hR_prime_div_Rbar p hp ab hab_Rbar e hab_eq, hab_eq⟩
    · have he_Rbar := hR_prime_div_Rbar p hp (ac * b_d) hacbd_Rbar e hacbd_eq
      obtain ⟨ubd', hubd'⟩ := hunit b_d hbd_notM
      have hac_eq : ac = (↑p : T) * (e * ↑ubd'⁻¹) := by
        calc ac = ac * b_d * ↑ubd'⁻¹ := by rw [← hubd', mul_assoc, ubd'.mul_inv, mul_one]
          _ = (↑p : T) * e * ↑ubd'⁻¹ := by rw [hacbd_eq]
          _ = (↑p : T) * (e * ↑ubd'⁻¹) := by ring
      right
      exact ⟨e * ↑ubd'⁻¹, hR_prime_div_Rbar p hp ac hac_Rbar _ hac_eq, hac_eq⟩



omit [IsAdicComplete (IsLocalRing.maximalIdeal T) T] in
theorem build_loc_away_ufd
    (R : NSubring T) (x₁ x₂ : T) (y₁ y₂ : R.carrier)
    (S_sub : Subring T) [IsDomain S_sub]
    (hR_le : R.carrier ≤ S_sub)
    (hy₁ : (↑y₁ : T) ≠ 0) (hy₂ : (↑y₂ : T) ≠ 0)
    (hx₁_trans : Transcendental R.carrier x₁)
    (hinv : ∀ (s : S_sub), (s : T) ∉ IsLocalRing.maximalIdeal T → IsUnit s)
    (hS_sub_eq : (S_sub : Set T) =
      {t : T | ∃ (a : T) (b : T),
        a ∈ intersectionSet R x₁ x₂ y₁ y₂ ∧
        b ∈ intersectionSet R x₁ x₂ y₁ y₂ ∧
        b ∉ IsLocalRing.maximalIdeal T ∧ t * b = a})
    (hRbar_le_S : ∀ t, t ∈ intersectionSet R x₁ x₂ y₁ y₂ → t ∈ (S_sub : Set T))
    (hx₁_Rbar : x₁ ∈ intersectionSet R x₁ x₂ y₁ y₂) :
    UniqueFactorizationMonoid
      (Localization.Away
        (Subring.inclusion hR_le y₁ *
          Subring.inclusion hR_le y₂)) := by
  haveI : IsDomain R.carrier := NSubring.isDomain R
  haveI : UniqueFactorizationMonoid R.carrier := R.isUFD
  set Rbar := intersectionSet R x₁ x₂ y₁ y₂
  set ι : R.carrier →+* S_sub := Subring.inclusion hR_le
  set s : S_sub := ι y₁ * ι y₂ with hs_def
  have hs_ne : s ≠ 0 := by
    rw [hs_def]
    intro h
    have := congrArg Subtype.val h
    simp only [Subring.coe_mul, ZeroMemClass.coe_zero] at this
    exact mul_ne_zero hy₁ hy₂ this
  have hpow_le :
      Submonoid.powers s ≤ nonZeroDivisors S_sub :=
    powers_le_nonZeroDivisors_of_noZeroDivisors hs_ne
  have hx₁_S : x₁ ∈ S_sub := hRbar_le_S _ hx₁_Rbar
  have hS_mem_rep :
      ∀ s' : S_sub, ∃ (a b : T),
        a ∈ Rbar ∧ b ∈ Rbar ∧
        b ∉ IsLocalRing.maximalIdeal T ∧
        (s' : T) * b = a := by
    intro s'
    have := s'.2
    change s'.1 ∈ (S_sub : Set T) at this
    rw [hS_sub_eq] at this
    exact this
  haveI : IsDomain (Localization.Away s) :=
    IsLocalization.isDomain_localization hpow_le
  have hinj_loc :=
    IsLocalization.injective (Localization.Away s) hpow_le
  have haeval_S :
      ∀ f : Polynomial R.carrier,
        (aeval x₁ f : T) ∈ S_sub := by
    intro f
    induction f using Polynomial.induction_on' with
    | add f g hf hg =>
      rw [map_add]
      exact S_sub.add_mem hf hg
    | monomial n a =>
      rw [Polynomial.aeval_monomial]
      simp only [
        show algebraMap R.carrier T =
          R.carrier.subtype from rfl,
        Subring.coe_subtype]
      exact S_sub.mul_mem (hR_le a.property)
        (S_sub.pow_mem hx₁_S n)
  let evalS : Polynomial R.carrier →+* S_sub :=
    RingHom.codRestrict
      (aeval (R := R.carrier) (A := T) x₁).toRingHom
      S_sub.toSubsemiring haeval_S
  have hevalS_val :
      ∀ f, (evalS f : T) = aeval x₁ f :=
    fun _ => rfl
  let φ :=
    (algebraMap S_sub (Localization.Away s)).comp
      evalS
  have hφ_inj : Function.Injective φ := by
    intro f g hfg
    have h1 : evalS f = evalS g := hinj_loc hfg
    have h2 : (evalS f : T) = (evalS g : T) :=
      congrArg Subtype.val h1
    rw [hevalS_val, hevalS_val] at h2
    exact
      (transcendental_iff_injective.mp hx₁_trans) h2
  have hevalS_C :
      ∀ r : R.carrier, evalS (C r) = ι r := by
    intro r
    apply Subtype.ext
    change aeval x₁ (C r) = (r : T)
    rw [Polynomial.aeval_C]
    simp [show algebraMap R.carrier T =
      R.carrier.subtype from rfl]
  have hevalS_s : evalS (C y₁ * C y₂) = s := by
    rw [map_mul, hevalS_C, hevalS_C]
  have hy₂_unit :
      IsUnit (algebraMap S_sub
        (Localization.Away s) (ι y₂)) := by
    have := IsLocalization.Away.algebraMap_isUnit
      (S := Localization.Away s) (x := s)
    rw [show s = ι y₁ * ι y₂ from rfl,
      map_mul] at this
    exact isUnit_of_mul_isUnit_right this
  have hy₁_unit :
      IsUnit (algebraMap S_sub
        (Localization.Away s) (ι y₁)) := by
    have := IsLocalization.Away.algebraMap_isUnit
      (S := Localization.Away s) (x := s)
    rw [show s = ι y₁ * ι y₂ from rfl,
      map_mul] at this
    exact isUnit_of_mul_isUnit_left this
  letI : Algebra (Polynomial R.carrier)
      (Localization.Away s) := φ.toAlgebra
  let M : Submonoid (Polynomial R.carrier) :=
    { carrier := {f | IsUnit (φ f)}
      one_mem' := by
        change IsUnit (φ 1)
        rw [map_one]
        exact isUnit_one
      mul_mem' := fun {a b} ha hb => by
        change IsUnit (φ (a * b))
        rw [map_mul]
        exact ha.mul hb }
  have hM_le :
      M ≤ nonZeroDivisors (Polynomial R.carrier) := by
    intro f hf
    have hφf_unit : IsUnit (φ f) := hf
    have hφf_ne : φ f ≠ 0 := hφf_unit.ne_zero
    refine ⟨fun g hfg => ?_, fun g hgf => ?_⟩
    · have h1 : φ f * φ g = 0 := by
        rw [← map_mul, hfg, map_zero]
      have : φ g = 0 :=
        Or.resolve_left (mul_eq_zero.mp h1)
          hφf_ne
      exact hφ_inj (by rw [this, map_zero])
    · have h1 : φ g * φ f = 0 := by
        rw [← map_mul, hgf, map_zero]
      have : φ g = 0 :=
        Or.resolve_right (mul_eq_zero.mp h1)
          hφf_ne
      exact hφ_inj (by rw [this, map_zero])
  haveI : IsLocalization M (Localization.Away s) := by
    rw [isLocalization_iff]
    refine ⟨fun ⟨f, hf⟩ => hf,
      fun z => ?_, fun {a b} hab => ?_⟩
    · obtain ⟨nn, w, hz⟩ :=
        IsLocalization.Away.surj (x := s) z
      obtain ⟨a', b', ha'_Rbar, hb'_Rbar,
        hb'_notM, hw_eq⟩ := hS_mem_rep w
      obtain ⟨fw, kw, hfw⟩ := ha'_Rbar.1
      obtain ⟨gw, jw, hgw⟩ := hb'_Rbar.1
      let a_poly : Polynomial R.carrier :=
        fw * C y₂ ^ jw
      let m_poly : Polynomial R.carrier :=
        (C y₁ * C y₂) ^ nn * gw * C y₂ ^ kw
      have hb'_S : b' ∈ (S_sub : Set T) :=
        hRbar_le_S _ hb'_Rbar
      have hevalS_gw_eq :
          evalS gw =
            ⟨b', hb'_S⟩ * (ι y₂) ^ jw := by
        apply Subtype.ext
        change aeval x₁ gw =
          (⟨b', hb'_S⟩ * (ι y₂) ^ jw : S_sub)
        rw [Subring.coe_mul, Subring.coe_pow,
          Subring.coe_inclusion]
        exact hgw.symm
      let A := algebraMap S_sub (Localization.Away s)
      have hA_s : IsUnit (A s) :=
        IsLocalization.Away.algebraMap_isUnit
          (S := Localization.Away s) (x := s)
      have hevalS_m_eq :
          evalS m_poly =
            s ^ nn * (⟨b', hb'_S⟩ *
              (ι y₂) ^ jw) * (ι y₂) ^ kw := by
        simp only [m_poly, map_mul, map_pow,
          hevalS_s, hevalS_C, hevalS_gw_eq]
      have hm_mem : m_poly ∈ M := by
        change IsUnit (φ m_poly)
        change IsUnit (A (evalS m_poly))
        rw [hevalS_m_eq]
        simp only [map_mul, map_pow]
        exact ((hA_s.pow nn).mul
          ((hinv ⟨b', hb'_S⟩ hb'_notM).map
            A |>.mul (hy₂_unit.pow jw))).mul
          (hy₂_unit.pow kw)
      refine ⟨⟨a_poly, ⟨m_poly, hm_mem⟩⟩, ?_⟩
      change z * φ m_poly = φ a_poly
      suffices hkey :
          w * evalS m_poly =
            evalS a_poly * s ^ nn by
        have hs_pow_unit :
            IsUnit (A (s ^ nn)) := by
          rw [map_pow]
          exact IsUnit.pow nn
            (IsLocalization.Away.algebraMap_isUnit
              (S := Localization.Away s) (x := s))
        change z * A (evalS m_poly) =
          A (evalS a_poly)
        have hz' : z * A (s ^ nn) = A w := by
          show z * A (s ^ nn) = A w
          rw [map_pow]
          exact hz
        apply hs_pow_unit.mul_right_cancel
        calc z * A (evalS m_poly) * A (s ^ nn)
            = z * A (s ^ nn) *
                A (evalS m_poly) := by ring
          _ = A w * A (evalS m_poly) := by
              rw [hz']
          _ = A (w * evalS m_poly) :=
              (map_mul A _ _).symm
          _ = A (evalS a_poly * s ^ nn) := by
              rw [hkey]
          _ = A (evalS a_poly) *
                A (s ^ nn) := map_mul A _ _
      apply Subtype.ext
      simp only [Subring.coe_mul,
        SubmonoidClass.coe_pow]
      conv_lhs =>
        rw [show (evalS m_poly : T) =
          aeval x₁ m_poly from rfl]
      conv_rhs =>
        rw [show (evalS a_poly : T) =
          aeval x₁ a_poly from rfl]
      simp only [m_poly, a_poly, map_mul,
        map_pow, Polynomial.aeval_C,
        show algebraMap R.carrier T =
          R.carrier.subtype from rfl,
        Subring.coe_subtype]
      have hs_T :
          (s : T) = (↑y₁ : T) * (↑y₂ : T) := by
        change (↑(ι y₁ * ι y₂) : T) =
          (↑y₁ : T) * (↑y₂ : T)
        rw [Subring.coe_mul,
          Subring.coe_inclusion,
          Subring.coe_inclusion]
      rw [hs_T]
      rw [show (aeval x₁ gw : T) =
            b' * (↑y₂ : T) ^ jw from hgw.symm,
          show (aeval x₁ fw : T) =
            a' * (↑y₂ : T) ^ kw from hfw.symm]
      linear_combination
        (↑y₁ * ↑y₂ : T) ^ nn *
          (↑y₂ : T) ^ jw *
          (↑y₂ : T) ^ kw * hw_eq
    · exact ⟨1, by rw [hφ_inj hab]⟩
  exact localization_submonoid_UFD hM_le

omit [IsAdicComplete (IsLocalRing.maximalIdeal T) T] in
/-- S_sub is a UFD via Kaplansky criterion. Uses the intersection construction
and Nagata-type arguments for the P∩R = ⊥ case. -/
theorem build_ufd_proof
    (R : NSubring T) (x₁ x₂ : T) (y₁ y₂ : R.carrier)
    (S_sub : Subring T) [IsDomain S_sub] [WfDvdMonoid S_sub]
    (hR_le : R.carrier ≤ S_sub)
    (_hcoprime : ∀ p : R.carrier, Prime p → ¬(p ∣ y₁ ∧ p ∣ y₂))
    (hy₁ : (↑y₁ : T) ≠ 0) (hy₂ : (↑y₂ : T) ≠ 0)
    (hx₁_trans : Transcendental R.carrier x₁)
    (_hx₂_trans : Transcendental R.carrier x₂)
    (_hx₁_mod_trans : ∀ (p : R.carrier), Prime p → ¬p ∣ y₂ →
      ∀ (f : Polynomial R.carrier),
        aeval x₁ f ∈ Ideal.span {(↑p : T)} → (C p : Polynomial R.carrier) ∣ f)
    (_hx₂_mod_trans : ∀ (p : R.carrier), Prime p → ¬p ∣ y₁ →
      ∀ (f : Polynomial R.carrier),
        aeval x₂ f ∈ Ideal.span {(↑p : T)} → (C p : Polynomial R.carrier) ∣ f)
    (hinv : ∀ (s : S_sub), (s : T) ∉ IsLocalRing.maximalIdeal T → IsUnit s)
    (hR_prime_in_S : ∀ (p : R.carrier), Prime p →
      (↑p : T) ∈ IsLocalRing.maximalIdeal T →
      Prime (⟨(↑p : T), hR_le p.2⟩ : S_sub))
    (hS_sub_eq : (S_sub : Set T) =
      {t : T | ∃ (a : T) (b : T),
        a ∈ intersectionSet R x₁ x₂ y₁ y₂ ∧
        b ∈ intersectionSet R x₁ x₂ y₁ y₂ ∧
        b ∉ IsLocalRing.maximalIdeal T ∧ t * b = a})
    (hRbar_le_S : ∀ t, t ∈ intersectionSet R x₁ x₂ y₁ y₂ → t ∈ (S_sub : Set T))
    (hx₁_Rbar : x₁ ∈ intersectionSet R x₁ x₂ y₁ y₂)
    (_hx₂_Rbar : x₂ ∈ intersectionSet R x₁ x₂ y₁ y₂) :
    UniqueFactorizationMonoid S_sub := by
  haveI : IsDomain R.carrier := NSubring.isDomain R
  haveI : UniqueFactorizationMonoid R.carrier := R.isUFD
  set Rbar := intersectionSet R x₁ x₂ y₁ y₂
  have hRbar_one : (1 : T) ∈ Rbar :=
    ⟨⟨C 1, 0, by simp⟩, ⟨C 1, 0, by simp⟩⟩
  have hRbar_add : ∀ t₁ t₂, t₁ ∈ Rbar → t₂ ∈ Rbar → t₁ + t₂ ∈ Rbar := by
    intro t₁ t₂ ⟨h₁₁, h₁₂⟩ ⟨h₂₁, h₂₂⟩
    constructor
    · obtain ⟨f₁, n₁, hf₁⟩ := h₁₁
      obtain ⟨f₂, n₂, hf₂⟩ := h₂₁
      refine ⟨f₁ * C (y₂ ^ n₂) + f₂ * C (y₂ ^ n₁), n₁ + n₂, ?_⟩
      have key : (t₁ + t₂) * (↑y₂ : T) ^ (n₁ + n₂) =
          t₁ * (↑y₂ : T) ^ n₁ * (↑y₂ : T) ^ n₂ +
          t₂ * (↑y₂ : T) ^ n₂ * (↑y₂ : T) ^ n₁ := by rw [pow_add]
                                                     ring
      rw [key, hf₁, hf₂, map_add, map_mul, map_mul, aeval_C, aeval_C]
      simp only [show algebraMap R.carrier T = R.carrier.subtype
        from rfl, Subring.coe_subtype, map_pow]
    · obtain ⟨f₁, n₁, hf₁⟩ := h₁₂
      obtain ⟨f₂, n₂, hf₂⟩ := h₂₂
      refine ⟨f₁ * C (y₁ ^ n₂) + f₂ * C (y₁ ^ n₁), n₁ + n₂, ?_⟩
      have key : (t₁ + t₂) * (↑y₁ : T) ^ (n₁ + n₂) =
          t₁ * (↑y₁ : T) ^ n₁ * (↑y₁ : T) ^ n₂ +
          t₂ * (↑y₁ : T) ^ n₂ * (↑y₁ : T) ^ n₁ := by rw [pow_add]
                                                     ring
      rw [key, hf₁, hf₂, map_add, map_mul, map_mul, aeval_C, aeval_C]
      simp only [show algebraMap R.carrier T = R.carrier.subtype
        from rfl, Subring.coe_subtype, map_pow]
  have hRbar_mul : ∀ t₁ t₂, t₁ ∈ Rbar → t₂ ∈ Rbar → t₁ * t₂ ∈ Rbar :=
    fun t₁ t₂ ⟨h₁₁, h₁₂⟩ ⟨h₂₁, h₂₂⟩ =>
      ⟨(fun x' y' t₁ t₂ ⟨f₁, n₁, hf₁⟩ ⟨f₂, n₂, hf₂⟩ =>
        ⟨f₁ * f₂, n₁ + n₂, by rw [map_mul, ← hf₁, ← hf₂, pow_add]
                              ring⟩) x₁ y₂ t₁ t₂ h₁₁ h₂₁,
       (fun x' y' t₁ t₂ ⟨f₁, n₁, hf₁⟩ ⟨f₂, n₂, hf₂⟩ =>
        ⟨f₁ * f₂, n₁ + n₂, by rw [map_mul, ← hf₁, ← hf₂, pow_add]
                              ring⟩) x₂ y₁ t₁ t₂ h₁₂ h₂₂⟩
  have hS_mem_rep : ∀ s : S_sub, ∃ (a b : T), a ∈ Rbar ∧ b ∈ Rbar ∧
      b ∉ IsLocalRing.maximalIdeal T ∧ (s : T) * b = a := by
    intro s
    have := s.2
    change s.1 ∈ (S_sub : Set T) at this
    rw [hS_sub_eq] at this
    exact this
  rw [UniqueFactorizationMonoid.iff_exists_prime_mem_of_isPrime]
  intro P hP_ne_bot hP_prime
  let ι : R.carrier →+* S_sub := Subring.inclusion hR_le
  have hPR_prime : (P.comap ι).IsPrime := Ideal.comap_isPrime ι P
  by_cases hPR_ne : P.comap ι = ⊥
  · -- Case P ∩ R = ⊥: Nagata pull-back via Localization.Away (ι y₁ * ι y₂)
    have hR_avoids_P : ∀ (r : R.carrier), r ≠ 0 → ι r ∉ P := by
      intro r hr hrP
      have : r ∈ P.comap ι := hrP
      rw [hPR_ne] at this
      exact hr (Ideal.mem_bot.mp this)
    have hy₁_ne : (y₁ : R.carrier) ≠ 0 := by
      intro h
      apply hy₁
      exact congrArg R.carrier.subtype h
    have hy₂_ne : (y₂ : R.carrier) ≠ 0 := by
      intro h
      apply hy₂
      exact congrArg R.carrier.subtype h
    set s : S_sub := ι y₁ * ι y₂ with hs_def
    have hs_ne : s ≠ 0 := by
      rw [hs_def]
      intro h
      have := congrArg Subtype.val h
      simp only [Subring.coe_mul, ZeroMemClass.coe_zero] at this
      exact mul_ne_zero hy₁ hy₂ this
    have hy₁_avoids : ι y₁ ∉ P := hR_avoids_P y₁ hy₁_ne
    have hy₂_avoids : ι y₂ ∉ P := hR_avoids_P y₂ hy₂_ne
    have hs_avoids : s ∉ P := by
      rw [hs_def]
      exact fun h => (hP_prime.mem_or_mem h).elim hy₁_avoids hy₂_avoids
    have hpow_le : Submonoid.powers s ≤ nonZeroDivisors S_sub :=
      powers_le_nonZeroDivisors_of_noZeroDivisors hs_ne
    have hdisj : Disjoint (Submonoid.powers s : Set S_sub) (P : Set S_sub) := by
      rw [Set.disjoint_left]
      rintro x ⟨n, rfl⟩ hxP
      exact hs_avoids (hP_prime.mem_of_pow_mem n hxP)
    haveI : IsDomain (Localization.Away s) :=
      IsLocalization.isDomain_localization hpow_le
    set Q := Ideal.map (algebraMap S_sub (Localization.Away s)) P with hQ_def
    have hQ_prime : Q.IsPrime :=
      IsLocalization.isPrime_of_isPrime_disjoint (Submonoid.powers s) _ P hP_prime hdisj
    have hinj_loc := IsLocalization.injective (Localization.Away s) hpow_le
    have hQ_ne_bot : Q ≠ ⊥ := by
      intro h
      apply hP_ne_bot
      rw [eq_bot_iff]
      intro x hx
      rw [Ideal.mem_bot]
      have : algebraMap S_sub (Localization.Away s) x ∈ Q := Ideal.mem_map_of_mem _ hx
      rw [h, Ideal.mem_bot] at this
      exact hinj_loc (by rw [this, map_zero])
    have hLoc_UFD : UniqueFactorizationMonoid (Localization.Away s) :=
      build_loc_away_ufd R x₁ x₂ y₁ y₂ S_sub hR_le hy₁ hy₂ hx₁_trans hinv hS_sub_eq
        hRbar_le_S hx₁_Rbar
    obtain ⟨q', hq'Q, hq'_prime⟩ :=
      (UniqueFactorizationMonoid.iff_exists_prime_mem_of_isPrime.mp hLoc_UFD) Q hQ_ne_bot hQ_prime
    obtain ⟨n, r, hq'_eq⟩ := IsLocalization.Away.surj (x := s) q'
    have hr_in_Q : algebraMap S_sub (Localization.Away s) r ∈ Q := by
      rw [← hq'_eq]
      exact Q.mul_mem_right _ hq'Q
    have hr_in_P : r ∈ P := by
      have := IsLocalization.comap_map_of_isPrime_disjoint
        (Submonoid.powers s) (Localization.Away s) hP_prime hdisj
      rw [← this]
      exact Ideal.mem_comap.mpr hr_in_Q
    have hr_ne : r ≠ 0 := by
      intro h
      rw [h, map_zero] at hq'_eq
      rcases mul_eq_zero.mp hq'_eq with h1 | h1
      · exact hq'_prime.ne_zero h1
      · exact (IsUnit.pow _ (IsLocalization.Away.algebraMap_isUnit
          (R := S_sub) (S := Localization.Away s) s)).ne_zero h1
    by_cases hs_unit : IsUnit s
    · have hr_not_unit : ¬IsUnit r := by
        intro hu
        exact hP_prime.ne_top (Ideal.eq_top_of_isUnit_mem P hr_in_P hu)
      have hr_prime_loc : Prime (algebraMap S_sub (Localization.Away s) r) := by
        have hassoc : Associated (algebraMap S_sub (Localization.Away s) r) q' := by
          have hpn_unit : IsUnit ((algebraMap S_sub (Localization.Away s) s) ^ n) :=
            IsUnit.pow _ (IsLocalization.Away.algebraMap_isUnit s)
          exact hq'_eq ▸ associated_mul_unit_left _ _ hpn_unit
        exact hassoc.prime_iff.mpr hq'_prime
      have hdvd_back : ∀ (x : S_sub),
          (algebraMap S_sub (Localization.Away s) r ∣ algebraMap S_sub _ x) →
          r ∣ x := by
        intro x hqx
        obtain ⟨z, hz⟩ := hqx
        obtain ⟨⟨c, ⟨_, m, rfl⟩⟩, hc⟩ :=
          IsLocalization.surj (Submonoid.powers s) z
        have key : x * s ^ m = r * c := by
          apply hinj_loc
          rw [map_mul, map_mul, map_pow]
          calc algebraMap S_sub _ x * (algebraMap S_sub _ s) ^ m
              = algebraMap S_sub _ r * (z * (algebraMap S_sub _ s) ^ m) := by
                rw [hz, mul_assoc]
            _ = algebraMap S_sub _ r * algebraMap S_sub _ c := by rw [← map_pow, hc]
        have hsm_unit : IsUnit (s ^ m) := IsUnit.pow m hs_unit
        have : r ∣ x * s ^ m := ⟨c, key⟩
        exact (hsm_unit.dvd_mul_right).mp this
      have hr_prime : Prime r := by
        refine ⟨hr_ne, hr_not_unit, fun a b hab => ?_⟩
        have hab_loc : algebraMap S_sub (Localization.Away s) r ∣
            algebraMap S_sub _ a * algebraMap S_sub _ b := by
          rw [← map_mul]
          exact map_dvd _ hab
        exact (hr_prime_loc.dvd_or_dvd hab_loc).imp (hdvd_back a) (hdvd_back b)
      exact ⟨r, hr_in_P, hr_prime⟩
    -- Case s is not a unit: factor y₁y₂ into primes in R and strip those factors from r
    · have hy₁y₂_ne : y₁ * y₂ ≠ (0 : R.carrier) := mul_ne_zero hy₁_ne hy₂_ne
      obtain ⟨factors, hfactors_prime, hfactors_assoc⟩ :=
        UniqueFactorizationMonoid.exists_prime_factors (y₁ * y₂) hy₁y₂_ne
      set pfactors : List R.carrier := factors.toList with hpfactors_def
      have hpfactors_prime : ∀ p ∈ pfactors, Prime p :=
        fun p hp => hfactors_prime p (Multiset.mem_toList.mp hp)
      have hpfactors_assoc : Associated (pfactors.map ι).prod s := by
        have h1 := hfactors_assoc.map ι
        rw [map_multiset_prod] at h1
        have h2 : (Multiset.map ι factors).prod = (pfactors.map ι).prod := by
          rw [show (factors : Multiset R.carrier) = ↑pfactors from
            (Multiset.coe_toList factors).symm, Multiset.map_coe, Multiset.prod_coe]
        rw [h2, show ι (y₁ * y₂) = ι y₁ * ι y₂ from map_mul ι y₁ y₂] at h1
        exact h1
      -- Each prime factor of y₁y₂ is either prime-and-avoiding-P or a unit in S_sub
      have hfactor_class : ∀ p ∈ pfactors,
          (Prime (ι p) ∧ ι p ∉ P) ∨ IsUnit (ι p) := by
        intro p hp
        have hp_prime := hpfactors_prime p hp
        by_cases hpM : (↑p : T) ∈ IsLocalRing.maximalIdeal T
        · left
          exact ⟨hR_prime_in_S p hp_prime hpM, hR_avoids_P p hp_prime.ne_zero⟩
        · right
          exact hinv (ι p) hpM
      -- Inductive stripping: remove all prime factors of s from r, preserving membership in P
      have fold_strip : ∀ (ps : List R.carrier) (a : S_sub),
          a ≠ 0 → a ∈ P →
          (∀ p ∈ ps, (Prime (ι p) ∧ ι p ∉ P) ∨ IsUnit (ι p)) →
          ∃ (a' : S_sub) (d : S_sub),
            a = d * a' ∧ a' ∈ P ∧ a' ≠ 0 ∧
            (∀ p ∈ ps, Prime (ι p) → ¬(ι p ∣ a')) := by
        intro ps
        induction ps with
        | nil =>
          intro a ha_ne ha_P _
          exact ⟨a, 1, by ring, ha_P, ha_ne, fun _ h _ => absurd h List.not_mem_nil⟩
        | cons q qs ih =>
          intro a ha_ne ha_P hclass
          have hqs_class : ∀ p ∈ qs, (Prime (ι p) ∧ ι p ∉ P) ∨ IsUnit (ι p) :=
            fun p hp => hclass p (List.mem_cons_of_mem q hp)
          rcases hclass q List.mem_cons_self with ⟨hq_prime, hq_avoid⟩ | hq_unit
          · obtain ⟨kq, a₁, hq_ndvd_a₁, ha_eq⟩ :=
              WfDvdMonoid.max_power_factor' ha_ne hq_prime.not_unit
            have ha₁_P : a₁ ∈ P := by
              rw [ha_eq] at ha_P
              exact (hP_prime.mem_or_mem ha_P).resolve_left
                (fun h => hq_avoid (hP_prime.mem_of_pow_mem kq h))
            have ha₁_ne : a₁ ≠ 0 := right_ne_zero_of_mul (ha_eq ▸ ha_ne)
            obtain ⟨a', d', ha₁_eq, ha'_P, ha'_ne, ha'_ndvd⟩ :=
              ih a₁ ha₁_ne ha₁_P hqs_class
            refine ⟨a', (ι q) ^ kq * d', ?_, ha'_P, ha'_ne, ?_⟩
            · rw [ha_eq, ha₁_eq]
              ring
            · intro p hp hp_prime
              rcases List.mem_cons.mp hp with rfl | hp'
              · intro h
                exact hq_ndvd_a₁ (dvd_trans h (Dvd.intro_left d' ha₁_eq.symm))
              · exact ha'_ndvd p hp' hp_prime
          · obtain ⟨a', d', ha_eq, ha'_P, ha'_ne, ha'_ndvd⟩ :=
              ih a ha_ne ha_P hqs_class
            refine ⟨a', d', ha_eq, ha'_P, ha'_ne, ?_⟩
            intro p hp hp_prime
            rcases List.mem_cons.mp hp with rfl | hp'
            · exact absurd hq_unit hp_prime.not_unit
            · exact ha'_ndvd p hp' hp_prime
      -- Apply the stripping lemma to get r' ∈ P with no prime factor of s dividing r'
      obtain ⟨r', d_strip, hr_eq_strip, hr'_in_P, hr'_ne, hr'_ndvd⟩ :=
        fold_strip pfactors r hr_ne hr_in_P hfactor_class
      -- Show r' maps to a prime in the localization
      have hr'_prime_loc : Prime (algebraMap S_sub (Localization.Away s) r') := by
        have h1 : algebraMap S_sub (Localization.Away s) r =
            algebraMap S_sub _ d_strip * algebraMap S_sub _ r' := by
          rw [hr_eq_strip, map_mul]
        have hprod_assoc : Associated (algebraMap S_sub _ d_strip * algebraMap S_sub _ r')
            q' := by
          rw [show algebraMap S_sub _ d_strip * algebraMap S_sub _ r' =
              q' * (algebraMap S_sub _ s) ^ n from by rw [← h1, hq'_eq]]
          exact associated_mul_unit_left _ _
            (IsUnit.pow _ (IsLocalization.Away.algebraMap_isUnit s))
        have hprod_prime : Prime (algebraMap S_sub _ d_strip * algebraMap S_sub _ r') :=
          hprod_assoc.prime_iff.mpr hq'_prime
        -- r' is not a unit in the localization (else r' | s^k, contradicting r' ∈ P)
        have hr'_loc_not_unit :
            ¬IsUnit (algebraMap S_sub (Localization.Away s) r') := by
          intro hu
          obtain ⟨k, hr'_dvd_sk⟩ :=
            (IsLocalization.Away.algebraMap_isUnit_iff s).mp hu
          obtain ⟨w, hw⟩ := hr'_dvd_sk
          have hsk_P : s ^ k ∈ P := hw ▸ P.mul_mem_right w hr'_in_P
          exact hs_avoids (hP_prime.mem_of_pow_mem k hsk_P)
        have hd_unit : IsUnit (algebraMap S_sub (Localization.Away s) d_strip) :=
          (hprod_prime.irreducible.isUnit_or_isUnit rfl).resolve_right hr'_loc_not_unit
        exact ((associated_unit_mul_right _ _ hd_unit).trans hprod_assoc).prime_iff.mpr
          hq'_prime
      -- Descend primality from the localization back to S_sub
      have hr'_prime : Prime r' := by
        refine ⟨hr'_ne, ?_, ?_⟩
        · intro hu
          exact hP_prime.ne_top (Ideal.eq_top_of_isUnit_mem P hr'_in_P hu)
        · intro a b hab
          have hab_loc : algebraMap S_sub (Localization.Away s) r' ∣
              algebraMap S_sub _ a * algebraMap S_sub _ b := by
            rw [← map_mul]
            exact map_dvd _ hab
          suffices hdvd_back : ∀ (x : S_sub),
              (algebraMap S_sub (Localization.Away s) r' ∣ algebraMap S_sub _ x) →
              r' ∣ x by
            exact (hr'_prime_loc.dvd_or_dvd hab_loc).imp (hdvd_back a) (hdvd_back b)
          intro x hqx
          obtain ⟨z, hz⟩ := hqx
          obtain ⟨⟨c, ⟨_, m, rfl⟩⟩, hc⟩ :=
            IsLocalization.surj (Submonoid.powers s) z
          have key : x * s ^ m = r' * c := by
            apply hinj_loc
            rw [map_mul, map_mul, map_pow]
            calc algebraMap S_sub _ x * (algebraMap S_sub _ s) ^ m
                = algebraMap S_sub _ r' * (z * (algebraMap S_sub _ s) ^ m) := by
                  rw [hz, mul_assoc]
              _ = algebraMap S_sub _ r' * algebraMap S_sub _ c := by
                  rw [← map_pow, hc]
          have hr'_dvd_xsm : r' ∣ x * s ^ m := ⟨c, key⟩
          obtain ⟨u_s, hu_s⟩ := hpfactors_assoc
          -- Key lemma: if r' | a * (prod of primes)^m and r' is coprime to each prime, then r' | a
          have strip_list_prod_pow : ∀ (ps : List R.carrier) (a : S_sub),
              (∀ p ∈ ps, (Prime (ι p) ∧ ι p ∉ P) ∨ IsUnit (ι p)) →
              (∀ p ∈ ps, Prime (ι p) → ¬(ι p ∣ r')) →
              r' ∣ a * (ps.map ι).prod ^ m → r' ∣ a := by
            intro ps
            induction ps with
            | nil => intro a _ _ h
                     simpa using h
            | cons p ps ih =>
              intro a hclass hndvd h
              have hclass' := fun q hq => hclass q (List.mem_cons_of_mem p hq)
              have hndvd' := fun q hq => hndvd q (List.mem_cons_of_mem p hq)
              simp only [List.map_cons, List.prod_cons] at h
              rcases hclass p List.mem_cons_self with ⟨hp_prime, _⟩ | hp_unit
              · have hp_ndvd := hndvd p List.mem_cons_self hp_prime
                have h1 : r' ∣ (a * (ps.map ι).prod ^ m) * (ι p) ^ m := by
                  rwa [show a * (ι p * (List.map ι ps).prod) ^ m =
                    (a * (List.map ι ps).prod ^ m) * (ι p) ^ m from by
                      rw [mul_pow]
                      ring] at h
                have h2 : r' ∣ a * (ps.map ι).prod ^ m :=
                  dvd_of_dvd_mul_prime_pow hp_prime hp_ndvd m h1
                exact ih a hclass' hndvd' h2
              · have hpm_unit : IsUnit ((ι p) ^ m) := hp_unit.pow m
                have h1 : r' ∣ (a * (ι p) ^ m) * (ps.map ι).prod ^ m := by
                  rwa [show a * (ι p * (List.map ι ps).prod) ^ m =
                    (a * (ι p) ^ m) * (List.map ι ps).prod ^ m from by
                      rw [mul_pow]
                      ring] at h
                have h2 : r' ∣ a * (ι p) ^ m :=
                  ih (a * (ι p) ^ m) hclass' hndvd' h1
                exact (hpm_unit.dvd_mul_right).mp h2
          -- Factor s^m = (prod of primes)^m * unit^m, strip primes, then cancel the unit
          have hr'_dvd_xU : r' ∣ x * ↑u_s ^ m := by
            have hsm_eq : s ^ m = (pfactors.map ι).prod ^ m * ↑u_s ^ m := by
              rw [← hu_s, mul_pow]
            have h1 : r' ∣ (x * ↑u_s ^ m) * (pfactors.map ι).prod ^ m := by
              rwa [show (x * ↑u_s ^ m) * (pfactors.map ι).prod ^ m =
                x * s ^ m from by rw [hsm_eq]
                                  ring]
            exact strip_list_prod_pow pfactors (x * ↑u_s ^ m)
              hfactor_class hr'_ndvd h1
          exact (u_s.isUnit.pow m).dvd_mul_right.mp hr'_dvd_xU
      exact ⟨r', hr'_in_P, hr'_prime⟩
  -- Case P ∩ R ≠ 0: R is a UFD, so P ∩ R contains a prime q of R; q maps to a prime in S_sub
  · obtain ⟨q, hq_mem, hq_prime⟩ :=
      (UniqueFactorizationMonoid.iff_exists_prime_mem_of_isPrime.mp
        ‹UniqueFactorizationMonoid R.carrier›) (P.comap ι) hPR_ne hPR_prime
    have hq_P : ι q ∈ P := Ideal.mem_comap.mp hq_mem
    -- q must lie in M_T: otherwise ι(q) is a unit and P = (1), contradicting P prime
    have hq_M : (↑q : T) ∈ IsLocalRing.maximalIdeal T := by
      by_contra h
      exact hP_prime.ne_top (Ideal.eq_top_of_isUnit_mem P hq_P (hinv (ι q) h))
    exact ⟨ι q, hq_P, by convert hR_prime_in_S q hq_prime hq_M using 1⟩

omit [IsAdicComplete (IsLocalRing.maximalIdeal T) T] in
/-- R-primes stay prime in S_sub: given the intersection subring construction,
every prime element of R maps to a prime element of S_sub. -/
theorem build_primes_preserved
    (R : NSubring T) (x₁ x₂ : T) (y₁ y₂ : R.carrier)
    (S_sub : Subring T) [IsDomain S_sub] [IsLocalRing S_sub] [UniqueFactorizationMonoid S_sub]
    (hR_le : R.carrier ≤ S_sub)
    (hx₁_trans : Transcendental R.carrier x₁)
    (hx₂_trans : Transcendental R.carrier x₂)
    (hcoprime : ∀ p : R.carrier, Prime p → ¬(p ∣ y₁ ∧ p ∣ y₂))
    (hmax_eq : IsLocalRing.maximalIdeal S_sub =
      (IsLocalRing.maximalIdeal T).comap S_sub.subtype)
    (hS_sub_eq : (S_sub : Set T) =
      {t : T | ∃ (a : T) (b : T),
        a ∈ intersectionSet R x₁ x₂ y₁ y₂ ∧
        b ∈ intersectionSet R x₁ x₂ y₁ y₂ ∧
        b ∉ IsLocalRing.maximalIdeal T ∧ t * b = a})
    (_hR_prime_div_Rbar : ∀ (p : R.carrier), Prime p → ∀ t ∈ intersectionSet R x₁ x₂ y₁ y₂,
      ∀ (d : T), t = (↑p : T) * d → d ∈ intersectionSet R x₁ x₂ y₁ y₂)
    (r : R.carrier) (hr : Prime r) :
    Prime (⟨(↑r : T), hR_le r.2⟩ : S_sub) := by
  haveI : IsDomain R.carrier := NSubring.isDomain R
  haveI : UniqueFactorizationMonoid R.carrier := R.isUFD
  set Rbar := intersectionSet R x₁ x₂ y₁ y₂
  set S_carrier : Set T :=
    {t : T | ∃ (a : T) (b : T), a ∈ Rbar ∧ b ∈ Rbar ∧
      b ∉ IsLocalRing.maximalIdeal T ∧ t * b = a}
  have hS_sub_eq' : (S_sub : Set T) = S_carrier := hS_sub_eq
  have hunit : ∀ (a : T), a ∉ IsLocalRing.maximalIdeal T → IsUnit a :=
    fun a ha => IsLocalRing.notMem_maximalIdeal.mp ha
  have hRbar_one : (1 : T) ∈ Rbar :=
    ⟨⟨C 1, 0, by simp⟩, ⟨C 1, 0, by simp⟩⟩
  have hRbar_mul : ∀ t₁ t₂, t₁ ∈ Rbar → t₂ ∈ Rbar → t₁ * t₂ ∈ Rbar :=
    fun t₁ t₂ ⟨h₁₁, h₁₂⟩ ⟨h₂₁, h₂₂⟩ =>
      ⟨(fun x' y' t₁ t₂ ⟨f₁, n₁, hf₁⟩ ⟨f₂, n₂, hf₂⟩ =>
        ⟨f₁ * f₂, n₁ + n₂, by rw [map_mul, ← hf₁, ← hf₂, pow_add]
                              ring⟩) x₁ y₂ t₁ t₂ h₁₁ h₂₁,
       (fun x' y' t₁ t₂ ⟨f₁, n₁, hf₁⟩ ⟨f₂, n₂, hf₂⟩ =>
        ⟨f₁ * f₂, n₁ + n₂, by rw [map_mul, ← hf₁, ← hf₂, pow_add]
                              ring⟩) x₂ y₁ t₁ t₂ h₁₂ h₂₂⟩
  have hALS_mul : ∀ (x' : T) (y' : R.carrier) (t₁ t₂ : T),
      t₁ ∈ adjoinLocSetY R x' y' → t₂ ∈ adjoinLocSetY R x' y' →
      t₁ * t₂ ∈ adjoinLocSetY R x' y' := by
    intro x' y' t₁ t₂ ⟨f₁, n₁, hf₁⟩ ⟨f₂, n₂, hf₂⟩
    exact ⟨f₁ * f₂, n₁ + n₂, by rw [map_mul, ← hf₁, ← hf₂, pow_add]
                                ring⟩
  set r' : S_sub := ⟨(r : T), hR_le r.2⟩ with hr'_def
  have hr'_ne : r' ≠ 0 := by
    intro h
    have h0 : (r : T) = (0 : T) := congrArg Subtype.val h
    exact hr.ne_zero (R.carrier.subtype_injective h0)
  have hr'_nu : ¬IsUnit r' := by
    intro hu
    have hr_M : (r : T) ∈ IsLocalRing.maximalIdeal T := by
      have hmem : r ∈ IsLocalRing.maximalIdeal R.carrier := by
        rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
        exact hr.not_unit
      rw [R.maximal_ideal_eq] at hmem
      exact Ideal.mem_comap.mp hmem
    have hunit_T : IsUnit (r' : T) := hu.map S_sub.subtype
    exact (IsLocalRing.notMem_maximalIdeal.mpr hunit_T) hr_M
  have hr'_irr : Irreducible r' := by
    constructor
    · exact hr'_nu
    · intro a b hab
      by_contra h_neither
      push Not at h_neither
      obtain ⟨ha_nu, hb_nu⟩ := h_neither
      have ha_M : (a : T) ∈ IsLocalRing.maximalIdeal T := by
        have := (IsLocalRing.mem_maximalIdeal (a : S_sub)).mpr ha_nu
        rw [hmax_eq, Ideal.mem_comap] at this
        exact this
      have hb_M : (b : T) ∈ IsLocalRing.maximalIdeal T := by
        have := (IsLocalRing.mem_maximalIdeal (b : S_sub)).mpr hb_nu
        rw [hmax_eq, Ideal.mem_comap] at this
        exact this
      have ha_sc : (a : T) ∈ S_carrier := hS_sub_eq' ▸ a.2
      have hb_sc : (b : T) ∈ S_carrier := hS_sub_eq' ▸ b.2
      obtain ⟨a₁, a₂, ha₁_Rbar, ha₂_Rbar, ha₂_nM, ha_eq⟩ := ha_sc
      obtain ⟨b₁, b₂, hb₁_Rbar, hb₂_Rbar, hb₂_nM, hb_eq⟩ := hb_sc
      have ha₂_unit : IsUnit a₂ := IsLocalRing.notMem_maximalIdeal.mp ha₂_nM
      have hb₂_unit : IsUnit b₂ := IsLocalRing.notMem_maximalIdeal.mp hb₂_nM
      have ha₁_M : a₁ ∈ IsLocalRing.maximalIdeal T :=
        ha_eq ▸ Ideal.mul_mem_right a₂ _ ha_M
      have heq_T : (r : T) = (a : T) * (b : T) := congrArg Subtype.val hab
      have hcleared : (r : T) * a₂ * b₂ = a₁ * b₁ := by
        calc (r : T) * a₂ * b₂
            = ((a : T) * (b : T)) * a₂ * b₂ := by rw [← heq_T]
          _ = ((a : T) * a₂) * ((b : T) * b₂) := by ring
          _ = a₁ * b₁ := by rw [ha_eq, hb_eq]
      have hry₂ : ¬ r ∣ y₂ ∨ ¬ r ∣ y₁ := by
        by_contra h
        push Not at h
        exact hcoprime r hr ⟨h.2, h.1⟩
      have hab₂_Rbar := hRbar_mul a₂ b₂ ha₂_Rbar hb₂_Rbar
      have hab₂_A₁ : a₂ * b₂ ∈ adjoinLocSetY R x₁ y₂ := hab₂_Rbar.1
      have hab₂_A₂ : a₂ * b₂ ∈ adjoinLocSetY R x₂ y₁ := hab₂_Rbar.2
      have hprod_eq : a₁ * b₁ = (r : T) * (a₂ * b₂) := by
        rw [← hcleared]
        ring
      have hr_M : (r : T) ∈ IsLocalRing.maximalIdeal T := by
        have hmem : r ∈ IsLocalRing.maximalIdeal R.carrier := by
          rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
          exact hr.not_unit
        rw [R.maximal_ideal_eq] at hmem
        exact Ideal.mem_comap.mp hmem
      have hr_ne : (r : T) ≠ 0 := by
        intro h
        exact hr.ne_zero (Subtype.ext h)
      suffices h_one_divides :
          (∃ d ∈ adjoinLocSetY R x₁ y₂, a₁ = (r : T) * d) ∨
          (∃ d ∈ adjoinLocSetY R x₁ y₂, b₁ = (r : T) * d) ∨
          (∃ d ∈ adjoinLocSetY R x₂ y₁, a₁ = (r : T) * d) ∨
          (∃ d ∈ adjoinLocSetY R x₂ y₁, b₁ = (r : T) * d) by
        have case_a₁ : ∀ d : T, a₁ = (r : T) * d → False := by
          intro d ha₁_eq
          have hdb₁ : d * b₁ = a₂ * b₂ :=
            mul_left_cancel₀ hr_ne (by
              calc (r : T) * (d * b₁) = (r : T) * d * b₁ := by ring
                _ = a₁ * b₁ := by rw [← ha₁_eq]
                _ = (r : T) * (a₂ * b₂) := hprod_eq)
          have hab₂_unit : IsUnit (a₂ * b₂) := ha₂_unit.mul hb₂_unit
          rw [← hdb₁] at hab₂_unit
          have hb₁_unit : IsUnit b₁ := isUnit_of_mul_isUnit_right hab₂_unit
          have hb_unit : IsUnit (b : T) :=
            isUnit_of_mul_isUnit_left (hb_eq ▸ hb₁_unit)
          exact absurd hb_M (IsLocalRing.notMem_maximalIdeal.mpr hb_unit)
        have case_b₁ : ∀ d : T, b₁ = (r : T) * d → False := by
          intro d hb₁_eq
          have hda₁ : a₁ * d = a₂ * b₂ :=
            mul_left_cancel₀ hr_ne (by
              calc (r : T) * (a₁ * d) = a₁ * ((r : T) * d) := by ring
                _ = a₁ * b₁ := by rw [← hb₁_eq]
                _ = (r : T) * (a₂ * b₂) := hprod_eq)
          have hab₂_unit : IsUnit (a₂ * b₂) := ha₂_unit.mul hb₂_unit
          rw [← hda₁] at hab₂_unit
          have ha₁_unit : IsUnit a₁ := isUnit_of_mul_isUnit_left hab₂_unit
          have ha_unit : IsUnit (a : T) :=
            isUnit_of_mul_isUnit_left (ha_eq ▸ ha₁_unit)
          exact absurd ha_M (IsLocalRing.notMem_maximalIdeal.mpr ha_unit)
        rcases h_one_divides with ⟨d, _, hd⟩ | ⟨d, _, hd⟩ |
          ⟨d, _, hd⟩ | ⟨d, _, hd⟩
        · exact (case_a₁ d hd).elim
        · exact (case_b₁ d hd).elim
        · exact (case_a₁ d hd).elim
        · exact (case_b₁ d hd).elim
      have hcoprime_r := hcoprime r hr
      by_cases hry₂' : r ∣ y₂
      · have hry₁' : ¬ r ∣ y₁ := fun h => hcoprime_r ⟨h, hry₂'⟩
        have := prime_in_adjoinLocSet R x₂ y₁ r hx₂_trans hr hry₁'
          a₁ b₁ (a₂ * b₂) ha₁_Rbar.2 hb₁_Rbar.2 hab₂_A₂ hprod_eq
        rcases this with h | h
        · exact Or.inr (Or.inr (Or.inl h))
        · exact Or.inr (Or.inr (Or.inr h))
      · have := prime_in_adjoinLocSet R x₁ y₂ r hx₁_trans hr hry₂'
          a₁ b₁ (a₂ * b₂) ha₁_Rbar.1 hb₁_Rbar.1 hab₂_A₁ hprod_eq
        rcases this with h | h
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
  exact hr'_irr.prime

end MainTheorem

end
