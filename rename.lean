/-
Copyright (c) 2025 . All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingyu Xia
-/

import Mathlib

noncomputable section

open MvPowerSeries Finset Finsupp Classical

variable {σ τ R : Type*} [CommSemiring R]
variable {e : σ → τ} (h : e.Injective)

namespace MvPowerSeries

def renameFun (f : MvPowerSeries σ R) : MvPowerSeries τ R :=
  fun x ↦ if SetLike.coe x.support ⊆ Set.range e then coeff (x.comapDomain e h.injOn) f else 0

theorem coeff_renameFun (f : MvPowerSeries σ R) (x : τ →₀ ℕ) :
    coeff x (renameFun h f) = if SetLike.coe x.support ⊆ Set.range e then
      coeff (x.comapDomain e h.injOn) f else 0 := rfl

theorem renameFun_zero : renameFun h (0 : MvPowerSeries σ R) = 0 := by
  simp [MvPowerSeries.ext_iff, coeff_renameFun]

theorem renameFun_one : renameFun h (1 : MvPowerSeries σ R) = 1 := by
  simp only [MvPowerSeries.ext_iff, coeff_renameFun, coeff_one, Finsupp.ext_iff, comapDomain_apply,
    Finsupp.coe_zero, Pi.zero_apply]
  intro x
  split_ifs with h
  any_goals grind
  simp only [Set.subset_def, SetLike.mem_coe, mem_support_iff, ne_eq, Set.mem_range] at h
  grind

theorem renameFun_mul (f g : MvPowerSeries σ R) :
    renameFun h (f * g) = renameFun h f * renameFun h g := by
  ext x
  simp only [coeff_renameFun, coeff_mul, mul_ite, ite_mul, zero_mul, mul_zero, sum_ite,
    sum_const_zero, add_zero, filter_filter]
  split_ifs with h'
  · have : filter (fun x ↦ SetLike.coe x.2.support ⊆ Set.range e ∧
      SetLike.coe x.1.support ⊆ Set.range e) (antidiagonal x) = antidiagonal x := by
      simp only [Set.subset_def, SetLike.mem_coe, mem_support_iff, ne_eq, Set.mem_range,
        Finset.ext_iff, mem_filter, mem_antidiagonal, Finsupp.ext_iff, Finsupp.coe_add,
        Pi.add_apply, and_iff_left_iff_imp, Prod.forall] at h' ⊢
      grind
    rw [this]
    replace this : antidiagonal (comapDomain e x h.injOn) = image (fun (x, y) ↦
      (comapDomain e x h.injOn, comapDomain e y h.injOn)) (antidiagonal x) := by
      simp only [Set.subset_def, SetLike.mem_coe, mem_support_iff, ne_eq, Set.mem_range,
        Finset.ext_iff, mem_antidiagonal, Finsupp.ext_iff, Finsupp.coe_add, Pi.add_apply,
        comapDomain_apply, mem_image, Prod.exists, Prod.forall, Prod.mk.injEq] at h' ⊢
      refine fun a b ↦ ⟨fun hab ↦ ?_, fun h' ↦ ?_⟩
      · use mapDomain e a, mapDomain e b
        simp only [mapDomain_apply h, implies_true, and_self, and_true]
        intro t
        by_cases! h'' : x t = 0
        · simp only [h'', Nat.add_eq_zero_iff]
          constructor; all_goals
          rw [← notMem_support_iff, mapDomain_support_of_injective h]
          simp only [mem_image, mem_support_iff, ne_eq, not_exists, not_and]
          grind
        obtain ⟨s, hs⟩ := h' _ h''
        simp [← hs, mapDomain_apply h, hab s]
      grind
    rw [this, sum_image]
    · simp only [Set.subset_def, SetLike.mem_coe, mem_support_iff, ne_eq, Set.mem_range, Set.InjOn,
        mem_antidiagonal, Finsupp.ext_iff, Finsupp.coe_add, Pi.add_apply, Prod.mk.injEq,
        comapDomain_apply, and_imp, Prod.forall] at h' ⊢
      grind
  have : filter (fun x ↦ SetLike.coe x.2.support ⊆ Set.range e ∧
    SetLike.coe x.1.support ⊆ Set.range e) (antidiagonal x) = ∅ := by
    simp only [Set.subset_def, SetLike.mem_coe, mem_support_iff, ne_eq, Set.mem_range,
      not_forall, not_exists, Finset.ext_iff, mem_filter, mem_antidiagonal, Finsupp.ext_iff,
      Finsupp.coe_add, Pi.add_apply, notMem_empty, iff_false, not_and, Prod.forall] at h' ⊢
    grind
  simp [this]

theorem renameFun_add (f g : MvPowerSeries σ R) :
    renameFun h (f + g) = renameFun h f + renameFun h g := by
  simp only [MvPowerSeries.ext_iff, coeff_renameFun, map_add]
  intro x
  split_ifs with h
  · rfl
  simp

theorem renameFun_commute (r : R) :
    renameFun h ((algebraMap R (MvPowerSeries σ R)) r) = (algebraMap R (MvPowerSeries τ R)) r := by
  simp only [algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply, MvPowerSeries.ext_iff,
    coeff_renameFun, Set.subset_def, SetLike.mem_coe, mem_support_iff, ne_eq, Set.mem_range,
    coeff_C, Finsupp.ext_iff, comapDomain_apply, Finsupp.coe_zero, Pi.zero_apply]
  grind

def rename : MvPowerSeries σ R →ₐ[R] MvPowerSeries τ R := {
  toFun := renameFun h
  map_one' := renameFun_one h
  map_mul' := renameFun_mul h
  map_zero' := renameFun_zero h
  map_add' := renameFun_add h
  commutes' := renameFun_commute h
}

@[simp]
theorem rename_apply {e : σ → τ} (h : e.Injective) {f : MvPowerSeries σ R} :
    rename h f = renameFun h f := rfl
