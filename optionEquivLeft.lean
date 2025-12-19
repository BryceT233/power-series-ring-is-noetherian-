/-
Copyright (c) 2025 . All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingyu Xia
-/

import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.RingTheory.PowerSeries.Inverse

suppress_compilation

open MvPowerSeries Finset Finsupp Option

variable (R S : Type*) [CommRing R]

-- define the canonical comap and map
private def someComap (x : Option S →₀ ℕ) : S →₀ ℕ :=
  comapDomain some x ((some_injective _).injOn)

private lemma someComap_zero : someComap S 0 = 0 := by simp [someComap]

private def someMap (x : S →₀ ℕ) : Option S →₀ ℕ := mapDomain some x

private lemma comap_comp_map (x : S →₀ ℕ) : someComap S (someMap S x) = x :=
  comapDomain_mapDomain _ (some_injective _) _

private lemma map_comp_comap (x : Option S →₀ ℕ) :
    someMap S (someComap S x) = x.erase none := by
  classical
  dsimp only [someMap, someComap]
  ext n; cases n
  · rw [erase_same, ← notMem_support_iff, mapDomain_support_of_injective (some_injective _)]
    simp
  simp [mapDomain_apply (some_injective _)]

-- the canonial comap and map induce functions between `MvPowerSeries (Option S) R` and
-- `MvPowerSeries S R`
private def rmdFun (f : MvPowerSeries (Option S) R) : MvPowerSeries S R :=
  fun x ↦ coeff (someMap S x) f

private lemma coeff_rmdFun_apply (f x) : coeff x (rmdFun R S f) = coeff (someMap S x) f := rfl

private def embFun (f : MvPowerSeries S R) : MvPowerSeries (Option S) R :=
  fun x ↦ if x none = 0 then coeff (someComap S x) f else 0

private lemma coeff_embFun_apply (f x) : coeff x (embFun R S f) =
    if x none = 0 then coeff (someComap S x) f else 0 := rfl

-- prove that `X none` divides `f - embFun R S (rmdFun R S f)` and
-- define the quotient to be `quotient_by_X_none`
private lemma X_none_dvd_sub_comp (f : MvPowerSeries (Option S) R) :
    X none ∣ f - embFun R S (rmdFun R S f) := by
  refine X_dvd_iff.mpr (fun x hx ↦ ?_)
  simp [coeff_embFun_apply, hx, coeff_rmdFun_apply, map_comp_comap]

private def quotient_by_X_none (f : MvPowerSeries (Option S) R) :=
  Exists.choose (X_none_dvd_sub_comp R S f)

private lemma rmd_add_X_mul_quotient (f : MvPowerSeries (Option S) R) :
    embFun R S (rmdFun R S f) + X none * quotient_by_X_none R S f = f := by
  grind [quotient_by_X_none, Exists.choose_spec (X_none_dvd_sub_comp R S f)]

-- define the euclidean algorithm of a power series `f` divided by `X none`
private def euclidean_alg (f : MvPowerSeries (Option S) R) :
    ℕ → MvPowerSeries S R × MvPowerSeries (Option S) R
  | 0 => (rmdFun R S f, quotient_by_X_none R S f)
  | k + 1 => (rmdFun R S (euclidean_alg f k).2, quotient_by_X_none R S ((euclidean_alg f k).2))

private lemma euclidean_alg_succ (f : MvPowerSeries (Option S) R) (k) :
    euclidean_alg R S f (k + 1) = euclidean_alg R S (quotient_by_X_none R S f) k := by
  induction k with
  | zero => simp [euclidean_alg]
  | succ k ih => rw [euclidean_alg.eq_2, ih, euclidean_alg.eq_2]

-- a helper lemma for proving the right inverse
private lemma aux_euclidean_alg (f : MvPowerSeries (Option S) R) (x : Option S →₀ ℕ) :
    (coeff (someComap S x)) (euclidean_alg R S f (x none)).1 = (coeff x) f := by
  classical
  generalize ht : x none = t
  revert f x; induction t with
  | zero =>
    intro _ x ht
    simp only [euclidean_alg, coeff_rmdFun_apply, map_comp_comap]
    congr
    simp [Finsupp.ext_iff, Finsupp.erase, ht]
  | succ t ih =>
    intro f x ht
    nth_rw 2 [← rmd_add_X_mul_quotient R S f]
    simp only [map_add, coeff_mul, coeff_X, ite_mul, one_mul, zero_mul, sum_ite, sum_const_zero,
      add_zero]
    have : filter (fun x ↦ x.1 = single none 1) (antidiagonal x) =
      {(single none 1, x - single none 1)} := by
      simp only [Finsupp.ext_iff, Finset.ext_iff, mem_filter, mem_antidiagonal, Finsupp.coe_add,
        Pi.add_apply, mem_singleton, Prod.forall, Prod.mk.injEq, coe_tsub, Pi.sub_apply]
      grind
    simp only [this, sum_singleton, coeff_embFun_apply]
    rw [ite_cond_eq_false, zero_add, ← ih]
    congr 2
    · simp [someComap, Finsupp.ext_iff]
    · apply euclidean_alg_succ
    all_goals simp [ht]

private def optionFunLeft (f : PowerSeries (MvPowerSeries S R)) : MvPowerSeries (Option S) R :=
  fun x ↦ coeff (someComap S x) (PowerSeries.coeff (x none) f)

private lemma coeff_optionFunLeft (f : PowerSeries (MvPowerSeries S R))
    (x : Option S →₀ ℕ) : coeff x (optionFunLeft R S f) =
      coeff (someComap S x) (PowerSeries.coeff (x none) f) := rfl

private def optionInvFunLeft (f : MvPowerSeries (Option S) R) :
    PowerSeries (MvPowerSeries S R) := PowerSeries.mk fun k => (euclidean_alg R S f k).1

private lemma coeff_optionInvFunLeft (f : MvPowerSeries (Option S) R) (k : ℕ) :
    PowerSeries.coeff k (optionInvFunLeft R S f) = (euclidean_alg R S f k).1 := by
  simp [optionInvFunLeft]

-- a helper lemma for proving the left inverse
private lemma euclidean_alg_optionFunLeft {k} (f : PowerSeries (MvPowerSeries S R)) :
    (euclidean_alg R S (optionFunLeft R S f) k).1 = (PowerSeries.coeff k) f := by
  classical
  revert f; induction k with
  | zero =>
    intro; ext
    simp only [euclidean_alg, coeff_rmdFun_apply, coeff_optionFunLeft, comap_comp_map]
    congr; dsimp only [someMap]
    rw [← notMem_support_iff, mapDomain_support_of_injective (some_injective _)]
    simp
  | succ k ih =>
    intro f
    rw [euclidean_alg_succ]
    have := PowerSeries.sub_const_eq_X_mul_shift f
    rw [sub_eq_iff_eq_add] at this
    nth_rw 2 [this]
    rw [map_add, PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_C, ite_cond_eq_false,
      add_zero, ← ih]
    congr
    replace this : X none ∈ nonZeroDivisors (MvPowerSeries (Option S) R) :=
      X_mem_nonzeroDivisors
    rw [← sub_eq_zero, ← mul_left_mem_nonZeroDivisors_eq_zero_iff this, mul_sub, sub_eq_zero]
    replace this := rmd_add_X_mul_quotient R S (optionFunLeft R S f)
    rw [← eq_sub_iff_add_eq'] at this
    rw [this]; ext x
    simp only [map_sub, coeff_optionFunLeft, coeff_embFun_apply, coeff_rmdFun_apply,
      map_comp_comap, erase_same, PowerSeries.coeff_zero_eq_constantCoeff, coeff_mul,
      coeff_X, PowerSeries.coeff_mk, ite_mul, one_mul, zero_mul, sum_ite, sum_const_zero, add_zero]
    split_ifs with h
    · have : filter (fun x ↦ x.1 = single none 1) (antidiagonal x) = ∅ := by
        simp only [Finsupp.ext_iff, Finset.ext_iff, mem_filter, mem_antidiagonal, Finsupp.coe_add,
          Pi.add_apply, notMem_empty, iff_false, not_and, not_forall, Prod.forall]
        grind
      simp [this, h]
    have : filter (fun x ↦ x.1 = single none 1) (antidiagonal x) =
      {(single none 1, x - single none 1)} := by
      simp only [Finsupp.ext_iff, Finset.ext_iff, mem_filter, mem_antidiagonal, Finsupp.coe_add,
        Pi.add_apply, mem_singleton, Prod.forall, Prod.mk.injEq, coe_tsub, Pi.sub_apply]
      grind
    simp only [sub_zero, this, sum_singleton, coe_tsub, Pi.sub_apply,
      single_eq_same]
    rw [Nat.sub_add_cancel (by omega)]
    congr 2
    simp [someComap, Finsupp.ext_iff]
    · simp

-- `optionFunLeft` commutes with the algebra structures
private lemma optionFunLeft_commute (r : R) :
    optionFunLeft R S ((algebraMap R (PowerSeries (MvPowerSeries S R))) r) =
      (algebraMap R (MvPowerSeries (Option S) R)) r := by
  classical
  rw [PowerSeries.algebraMap_apply]
  simp only [MvPowerSeries.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply,
    MvPowerSeries.ext_iff, coeff_optionFunLeft, PowerSeries.coeff_C, coeff_C]
  intro x
  split_ifs with _ h
  any_goals grind
  · simp [h, someComap_zero]
  · rw [coeff_C, ite_cond_eq_false]
    · simp only [Finsupp.ext_iff, Finsupp.coe_zero, Pi.ofNat_apply, not_forall, someComap,
        comapDomain_apply, eq_iff_iff, iff_false] at h ⊢
      rcases h with ⟨a, ha⟩
      cases a; contradiction
      grind

-- `optionFunLeft` is multiplicative
private lemma optionFunLeft_mul (f g : PowerSeries (MvPowerSeries S R)) :
    optionFunLeft R S (f * g) = optionFunLeft R S f * optionFunLeft R S g := by
  classical
  ext x
  simp only [coeff_optionFunLeft, PowerSeries.coeff_mul, map_sum, coeff_mul, ← sum_product']
  let e : ((Option S →₀ ℕ) × (Option S →₀ ℕ)) → (ℕ × ℕ) × (S →₀ ℕ) × (S →₀ ℕ) :=
    fun (x, y) ↦ ((x none, y none), someComap S x, someComap S y)
  have img_e : image e (antidiagonal x) = antidiagonal (x none) ×ˢ
    antidiagonal (someComap S x) := by
    simp only [someComap, Finset.ext_iff, mem_image, mem_antidiagonal, Finsupp.ext_iff,
      Finsupp.coe_add, Pi.add_apply, Prod.exists, mem_product, comapDomain_apply, Prod.forall,
      Prod.mk.injEq, e]
    intro u v a b
    constructor
    · grind
    rintro ⟨h1, h2⟩
    use mapDomain some a + single none u, mapDomain some b + single none v
    simp only [Finsupp.coe_add, Pi.add_apply, single_eq_same, Nat.add_eq_right, ne_eq, reduceCtorEq,
      not_false_eq_true, single_eq_of_ne, add_zero]
    refine ⟨fun y ↦ ?_, ?_, fun y ↦ ?_, fun y ↦ ?_⟩
    · cases y; simp [mapDomain, h1]
      rw [mapDomain_apply (some_injective _), mapDomain_apply (some_injective _)]
      grind
    · simp [mapDomain]
    all_goals rw [mapDomain_apply (some_injective _)]
  rw [← img_e, sum_image]
  · apply Function.Injective.injOn
    simp only [Function.Injective, someComap, Prod.mk.injEq, Finsupp.ext_iff, comapDomain_apply,
      and_imp, Prod.forall, e]
    refine fun _ _ _ _ _ _ _ _ ↦ ⟨fun i ↦ ?_, fun i ↦ ?_⟩
    all_goals cases i
    all_goals grind

-- use what we have proved so far to define an algebra isomorphism from
-- `PowerSeries (MvPowerSeries S R)` to `MvPowerSeries (Option S) R`
def optionEquivLeft : PowerSeries (MvPowerSeries S R) ≃ₐ[R] MvPowerSeries (Option S) R := {
  toFun := optionFunLeft R S
  invFun := optionInvFunLeft R S
  left_inv := by
    intro; ext
    rw [coeff_optionInvFunLeft, euclidean_alg_optionFunLeft]
  right_inv := by
    intro; ext
    rw [coeff_optionFunLeft, coeff_optionInvFunLeft, aux_euclidean_alg]
  map_mul' := optionFunLeft_mul R S
  map_add' := by simp [MvPowerSeries.ext_iff, coeff_optionFunLeft]
  commutes' := optionFunLeft_commute R S
}
