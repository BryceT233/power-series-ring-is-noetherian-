/-
Copyright (c) 2025 . All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingyu Xia
-/

import Mathlib

suppress_compilation

open MvPowerSeries Finset

variable {R : Type*} [CommRing R]
variable (n : ℕ)

/-- define `aux_init` to be the function of taking the first n components a monomial
`x : Fin (n + 1) →₀ ℕ` -/
private def aux_init (x : Fin (n + 1) →₀ ℕ) : Fin n →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (Fin.init x)

private lemma aux_init_zero : aux_init n 0 = 0 := by
  simp [Finsupp.ext_iff, aux_init, Fin.init]

/-- define `aux_snoc` to be the function of adding a 0 at the end of a monomial `x : Fin n →₀ ℕ` -/
private def aux_snoc (x : Fin n →₀ ℕ) : Fin (n + 1) →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (Fin.snoc x 0)

private lemma init_comp_snoc (x : Fin n →₀ ℕ) : (aux_init n) (aux_snoc n x) = x := by
  simp [aux_init, aux_snoc]

private lemma snoc_comp_init (x : Fin (n + 1) →₀ ℕ) :
    (aux_snoc n) (aux_init n x) = x.erase (Fin.last n) := by
  simp only [aux_snoc, aux_init, Finsupp.coe_equivFunOnFinite_symm, Finsupp.erase, Finsupp.ext_iff,
    Finsupp.equivFunOnFinite_symm_apply_toFun, Fin.snoc, Fin.castSucc_castLT, Fin.init, cast_eq,
    dite_eq_ite, Finsupp.coe_mk]
  grind

/-- `aux_snoc` induces a function `rmdPredFun` from `MvPowerSeries (Fin (n + 1)) R` to
`MvPowerSeries (Fin n) R`-/
private def rmdPredFun (f : MvPowerSeries (Fin (n + 1)) R) : MvPowerSeries (Fin n) R :=
  fun x ↦ coeff (aux_snoc n x) f

private lemma coeff_rmdPred_apply (f : MvPowerSeries (Fin (n + 1)) R) (x : Fin n →₀ ℕ) :
    coeff x (rmdPredFun n f) = coeff (aux_snoc n x) f := rfl

/-- `aux_init` induces a function `embSuccFun` from `MvPowerSeries (Fin n) R` to
`MvPowerSeries (Fin (n + 1)) R`-/
private def embSuccFun (f : MvPowerSeries (Fin n) R) : MvPowerSeries (Fin (n + 1)) R :=
  fun x ↦ if x (Fin.last n) = 0 then coeff (aux_init n x) f else 0

private lemma coeff_embSucc_apply (f : MvPowerSeries (Fin n) R) (x : Fin (n + 1) →₀ ℕ) :
    coeff x (embSuccFun n f) = if x (Fin.last n) = 0 then coeff (aux_init n x) f else 0 := rfl

/- prove that `X (Fin.last n)` divides `f - embSuccFun n (rmdPredFun n f)` and
define the quotient to be `quotient_by_X_last` -/
private lemma X_last_dvd_sub_comp (f : MvPowerSeries (Fin (n + 1)) R) :
    X (Fin.last n) ∣ f - embSuccFun n (rmdPredFun n f) := by
  refine X_dvd_iff.mpr (fun x hx ↦ ?_)
  simp only [map_sub, coeff_embSucc_apply, hx, ↓reduceIte, coeff_rmdPred_apply,
    snoc_comp_init]
  rw [coeff_apply, coeff_apply, sub_eq_zero]
  congr 1; grind

private def quotient_by_X_last (f : MvPowerSeries (Fin (n + 1)) R) :=
  Exists.choose (X_last_dvd_sub_comp n f)

private lemma rmd_add_X_last_mul_quotient (f : MvPowerSeries (Fin (n + 1)) R) :
    embSuccFun n (rmdPredFun n f) + X (Fin.last n) * quotient_by_X_last n f = f := by
  grind [quotient_by_X_last, Exists.choose_spec (X_last_dvd_sub_comp n f)]

private def euclidean_alg (f : MvPowerSeries (Fin (n + 1)) R) :
    ℕ → MvPowerSeries (Fin n) R × MvPowerSeries (Fin (n + 1)) R
  | 0 => (rmdPredFun n f, quotient_by_X_last n f)
  | k + 1 => (rmdPredFun n (euclidean_alg f k).2, quotient_by_X_last n ((euclidean_alg f k).2))

private lemma euclidean_alg_succ (f : MvPowerSeries (Fin (n + 1)) R) (k) :
    euclidean_alg n f (k + 1) = euclidean_alg n (quotient_by_X_last n f) k := by
  induction k with
  | zero => simp [euclidean_alg]
  | succ k ih => rw [euclidean_alg.eq_2, ih, euclidean_alg.eq_2]

/-- a helper lemma for proving the left inverse -/
private lemma aux_euclidean_alg (f : MvPowerSeries (Fin (n + 1)) R) (x : Fin (n + 1) →₀ ℕ) :
    (coeff (aux_init n x)) (euclidean_alg n f (x (Fin.last n))).1 = (coeff x) f := by
  generalize ht : x (Fin.last n) = t
  revert f x; induction t with
  | zero =>
    intro _ x ht
    simp only [euclidean_alg, coeff_rmdPred_apply, snoc_comp_init]
    congr
    simp [Finsupp.ext_iff, Finsupp.erase, ht]
  | succ t ih =>
    intro f x ht
    nth_rw 2 [← rmd_add_X_last_mul_quotient n f]
    simp [coeff_mul, coeff_X, sum_ite]
    have : filter (fun x ↦ x.1 = fun₀ | Fin.last n => 1) (antidiagonal x) =
      {(fun₀ | Fin.last n => 1, x - fun₀ | Fin.last n => 1)} := by
      simp only [Finsupp.ext_iff, Finset.ext_iff, mem_filter, mem_antidiagonal, Finsupp.coe_add,
        Pi.add_apply, mem_singleton, Prod.forall, Prod.mk.injEq, Finsupp.coe_tsub, Pi.sub_apply]
      grind
    simp only [this, sum_singleton, coeff_embSucc_apply]
    rw [ite_cond_eq_false, zero_add, ← ih]
    congr 2
    · simp [aux_init, funext_iff, Fin.init]
    · apply euclidean_alg_succ
    all_goals simp [ht]

private def finSuccFun (f : MvPowerSeries (Fin (n + 1)) R) :
    PowerSeries (MvPowerSeries (Fin n) R) := PowerSeries.mk fun k => (euclidean_alg n f k).1

private lemma coeff_finSuccFun_apply (f : MvPowerSeries (Fin (n + 1)) R) (k : ℕ) :
    PowerSeries.coeff k (finSuccFun n f) = (euclidean_alg n f k).1 := by simp [finSuccFun]

private def finSuccInvFun (f : PowerSeries (MvPowerSeries (Fin n) R)) :
    MvPowerSeries (Fin (n + 1)) R :=
  fun x ↦ coeff (aux_init n x) (PowerSeries.coeff (x (Fin.last n)) f)

private lemma coeff_finSuccInvFun_apply (f : PowerSeries (MvPowerSeries (Fin n) R))
    (x : Fin (n + 1) →₀ ℕ) : coeff x (finSuccInvFun n f) =
      coeff (aux_init n x) (PowerSeries.coeff (x (Fin.last n)) f) := rfl

/-- a helper lemma for proving the right inverse -/
private lemma euclidean_alg_finSuccInvFun {k} (f : PowerSeries (MvPowerSeries (Fin n) R)) :
    (euclidean_alg n (finSuccInvFun n f) k).1 = (PowerSeries.coeff k) f := by
  revert f; induction k with
  | zero =>
    intro f; ext x
    simp only [euclidean_alg, coeff_rmdPred_apply, coeff_finSuccInvFun_apply, init_comp_snoc]
    congr; simp [aux_snoc]
  | succ k ih =>
    intro f
    rw [euclidean_alg_succ]
    have := PowerSeries.sub_const_eq_X_mul_shift f
    rw [sub_eq_iff_eq_add] at this
    nth_rw 2 [this]
    rw [map_add, PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_C, ite_cond_eq_false,
      add_zero, ← ih]
    congr
    replace this : X (Fin.last n) ∈ nonZeroDivisors (MvPowerSeries (Fin (n + 1)) R) :=
      X_mem_nonzeroDivisors
    rw [← sub_eq_zero, ← mul_left_mem_nonZeroDivisors_eq_zero_iff this, mul_sub, sub_eq_zero]
    replace this := rmd_add_X_last_mul_quotient n (finSuccInvFun n f)
    rw [← eq_sub_iff_add_eq'] at this
    rw [this]
    ext x
    simp only [map_sub, coeff_finSuccInvFun_apply, coeff_embSucc_apply, coeff_rmdPred_apply,
      snoc_comp_init, Finsupp.erase_same, PowerSeries.coeff_zero_eq_constantCoeff, coeff_mul,
      coeff_X, PowerSeries.coeff_mk, ite_mul, one_mul, zero_mul, sum_ite, sum_const_zero, add_zero]
    split_ifs with h
    · have : filter (fun x ↦ x.1 = fun₀ | Fin.last n => 1) (antidiagonal x) = ∅ := by
        simp only [Finsupp.ext_iff, Finset.ext_iff, mem_filter, mem_antidiagonal, Finsupp.coe_add,
          Pi.add_apply, notMem_empty, iff_false, not_and, not_forall, Prod.forall]
        grind
      simp [this, h]
    have : filter (fun x ↦ x.1 = fun₀ | Fin.last n => 1) (antidiagonal x) =
      {(fun₀ | Fin.last n => 1, x - fun₀ | Fin.last n => 1)} := by
      simp only [Finsupp.ext_iff, Finset.ext_iff, mem_filter, mem_antidiagonal, Finsupp.coe_add,
        Pi.add_apply, mem_singleton, Prod.forall, Prod.mk.injEq, Finsupp.coe_tsub, Pi.sub_apply]
      grind
    simp only [sub_zero, this, sum_singleton, Finsupp.coe_tsub, Pi.sub_apply,
      Finsupp.single_eq_same]
    rw [Nat.sub_add_cancel (by omega)]
    congr 2
    simp [aux_init, funext_iff, Fin.init]
    · simp

private lemma finSuccInvFun_commute (r : R) :
    finSuccInvFun n ((algebraMap R (PowerSeries (MvPowerSeries (Fin n) R))) r) =
      (algebraMap R (MvPowerSeries (Fin (n + 1)) R)) r := by
  rw [PowerSeries.algebraMap_apply]
  simp only [MvPowerSeries.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply,
    MvPowerSeries.ext_iff, coeff_finSuccInvFun_apply, PowerSeries.coeff_C, coeff_C]
  intro x
  split_ifs with h h' h''
  any_goals grind
  · simp [h', aux_init_zero]
  · rw [coeff_C, ite_cond_eq_false]
    · simp only [Finsupp.ext_iff, Finsupp.coe_zero, Pi.zero_apply, not_forall, aux_init,
        Finsupp.equivFunOnFinite_symm_apply_toFun, Fin.init, Fin.castSucc, Fin.castAdd, Fin.castLE,
        eq_iff_iff, iff_false] at h' ⊢
      rcases h' with ⟨i, _⟩
      have : i.1 ≠ n := by grind
      use ⟨i.1, by omega⟩

private lemma finSuccInvFun_mul (f g : PowerSeries (MvPowerSeries (Fin n) R)) :
    finSuccInvFun n (f * g) = finSuccInvFun n f * finSuccInvFun n g := by
  ext x
  simp only [coeff_finSuccInvFun_apply, PowerSeries.coeff_mul, map_sum, coeff_mul, ← sum_product']
  let e : ((Fin (n + 1) →₀ ℕ) × (Fin (n + 1) →₀ ℕ)) → (ℕ × ℕ) × (Fin n →₀ ℕ) × (Fin n →₀ ℕ) :=
    fun (x, y) ↦ ((x (Fin.last n), y (Fin.last n)), aux_init n x, aux_init n y)
  have img_e : image e (antidiagonal x) = antidiagonal (x (Fin.last n)) ×ˢ
    antidiagonal (aux_init n x) := by
    simp only [aux_init, Finset.ext_iff, mem_image, mem_antidiagonal, Finsupp.ext_iff,
      Finsupp.coe_add, Pi.add_apply, Prod.exists, mem_product,
      Finsupp.equivFunOnFinite_symm_apply_toFun, Fin.init, Fin.castSucc, Fin.castAdd, Fin.castLE,
      Prod.forall, Prod.mk.injEq, e]
    intro u v a b
    constructor
    · grind
    rintro ⟨h1, h2⟩
    use Finsupp.equivFunOnFinite.symm (Fin.snoc a u), Finsupp.equivFunOnFinite.symm (Fin.snoc b v)
    simp only [Finsupp.equivFunOnFinite_symm_apply_toFun, Fin.snoc, Fin.castLT, Fin.castSucc_mk,
      Fin.eta, cast_eq, Fin.val_last, lt_self_iff_false, ↓reduceDIte, and_self, Fin.is_lt,
      Fin.castLT_mk, implies_true, and_true]
    grind
  rw [← img_e, sum_image]
  · apply Function.Injective.injOn
    simp only [Function.Injective, aux_init, Prod.mk.injEq, EmbeddingLike.apply_eq_iff_eq,
      funext_iff, Fin.init, Fin.castSucc, Fin.castAdd, Fin.castLE, and_imp, Prod.forall,
      Finsupp.ext_iff, e]
    refine fun _ _ _ _ _ _ h1 h2 ↦ ⟨fun i ↦ ?_, fun i ↦ ?_⟩
    · by_cases! h : i = Fin.last n
      · grind
      have : i.1 ≠ n := by grind
      grind [h1 ⟨i.1, by omega⟩]
    by_cases! h : i = Fin.last n
    · grind
    have : i.1 ≠ n := by grind
    grind [h2 ⟨i.1, by omega⟩]

private lemma left_inv : Function.LeftInverse (finSuccInvFun n) (@finSuccFun R _ n) := by
  intro f; ext x
  rw [coeff_finSuccInvFun_apply, coeff_finSuccFun_apply, aux_euclidean_alg]

private lemma right_inv : Function.RightInverse (finSuccInvFun n) (@finSuccFun R _ n) := by
  intro f; ext k x
  rw [coeff_finSuccFun_apply, euclidean_alg_finSuccInvFun]

def finSuccInvAlgEquiv : PowerSeries (MvPowerSeries (Fin n) R) ≃ₐ[R] MvPowerSeries (Fin (n + 1)) R := {
  toFun := finSuccInvFun n
  invFun := finSuccFun n
  left_inv := right_inv n
  right_inv := left_inv n
  map_mul' := finSuccInvFun_mul n
  map_add' := by simp [MvPowerSeries.ext_iff, coeff_finSuccInvFun_apply]
  commutes' := finSuccInvFun_commute n
}

def MvPowerSeries.isEmptyAlgEquiv {σ} [IsEmpty σ] : MvPowerSeries σ R ≃ₐ[R] R := sorry

theorem MvPowerSeries.isNoetherianRing_fin [IsNoetherianRing R] :
    IsNoetherianRing (MvPowerSeries (Fin n) R) := by
  induction n with
  | zero =>
    exact isNoetherianRing_of_ringEquiv _ MvPowerSeries.isEmptyAlgEquiv.symm.toRingEquiv
  | succ n ih =>
    exact isNoetherianRing_of_ringEquiv _ (finSuccInvAlgEquiv n).toRingEquiv
