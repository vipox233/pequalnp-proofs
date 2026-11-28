import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Dual.Defs
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Tauto
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Tactic.Abel
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_32025_aux

abbrev F := ZMod 2
abbrev V (n : ℕ) := Fin n → F
abbrev E (c : ℕ) := (Fin c × Fin 3) → F

def diff {n : ℕ} (g : V n → F) (a x : V n) : F := g (x + a) - g x

def third {n : ℕ} (g : V n → F) (a b c : V n) : F :=
  diff (diff (diff g a) b) c 0

def cubic {n : ℕ} (g : V n → F) : Prop :=
  ∀ a b c d x, diff (diff (diff (diff g a) b) c) d x = 0

def quad {n : ℕ} (q : V n → F) : Prop :=
  ∃ (s : F) (h : V n) (M : Fin n → Fin n → F),
    ∀ x, q x = s + dotProduct h x + ∑ i, ∑ j, M i j * x i * x j

def affine {n : ℕ} (a : V n → F) : Prop :=
  ∃ (s : F) (h : V n), ∀ x, a x = s + dotProduct h x

def unit {n : ℕ} (i j : Fin n) : F := if i = j then (1 : F) else 0

noncomputable def rankAt {n : ℕ} (g : V n → F) (u : V n) : ℕ :=
  (Matrix.of (fun i j : Fin n => third g u (unit i) (unit j))).rank

lemma f_cases (a : F) : a = 0 ∨ a = 1 := by
  match a with
  | ⟨0, _⟩ => left; rfl
  | ⟨1, _⟩ => right; rfl

lemma f_add_self (a : F) : a + a = 0 := by
  match a with
  | ⟨0, _⟩ => rfl
  | ⟨1, _⟩ => rfl

lemma f_sub_eq_add (a b : F) : a - b = a + b := by
  match a, b with
  | ⟨0, _⟩, ⟨0, _⟩ => rfl
  | ⟨0, _⟩, ⟨1, _⟩ => rfl
  | ⟨1, _⟩, ⟨0, _⟩ => rfl
  | ⟨1, _⟩, ⟨1, _⟩ => rfl

lemma f_neg_eq (a : F) : -a = a := by
  rcases f_cases a with rfl | rfl <;> decide

lemma f_mul_self (a : F) : a * a = a := by
  match a with
  | ⟨0, _⟩ => rfl
  | ⟨1, _⟩ => rfl

lemma vec_add_self {α : Type*} (x : α → F) : x + x = 0 := by
  funext i; exact f_add_self (x i)

lemma diff_eq_add {n : ℕ} (g : V n → F) (a x : V n) :
    diff g a x = g (x + a) + g x := by
  simp [diff, f_sub_eq_add]

lemma diff_zero {n : ℕ} (g : V n → F) (x : V n) : diff g 0 x = 0 := by
  simp [diff_eq_add, f_add_self]

lemma diff_add_fun {n : ℕ} (g₁ g₂ : V n → F) (a x : V n) :
    diff (fun y => g₁ y + g₂ y) a x = diff g₁ a x + diff g₂ a x := by
  simp only [diff_eq_add]; ring

lemma diff_comm {n : ℕ} (g : V n → F) (a b x : V n) :
    diff (diff g a) b x = diff (diff g b) a x := by
  simp only [diff_eq_add, add_assoc, add_comm a b]; ring

lemma diff_self {n : ℕ} (g : V n → F) (a x : V n) :
    diff (diff g a) a x = 0 := by
  simp only [diff_eq_add]
  have h : x + a + a = x := by rw [add_assoc, vec_add_self, add_zero]
  rw [h]
  have h1 : g x + g (x + a) + (g (x + a) + g x) = (g x + g x) + (g (x + a) + g (x + a)) := by ring
  rw [h1, f_add_self, f_add_self, add_zero]

lemma diff_add_dir {n : ℕ} (g : V n → F) (a b x : V n) :
    diff g (a + b) x = diff g a (x + b) + diff g b x := by
  simp only [diff_eq_add]
  have h1 : x + (a + b) = x + b + a := by rw [add_comm a b, add_assoc]
  rw [h1]
  have h2 : g (x + b + a) + g (x + b) + (g (x + b) + g x) =
      g (x + b + a) + g x + (g (x + b) + g (x + b)) := by ring
  rw [h2, f_add_self, add_zero]

lemma diff_const {n : ℕ} (c : F) (a x : V n) : diff (fun _ => c) a x = 0 := by
  simp [diff_eq_add, f_add_self]

lemma diff_dotProduct {n : ℕ} (h : V n) (a x : V n) :
    diff (fun y => dotProduct h y) a x = dotProduct h a := by
  simp only [diff_eq_add, dotProduct_add]
  have h1 : dotProduct h x + dotProduct h a + dotProduct h x =
      dotProduct h a + (dotProduct h x + dotProduct h x) := by ring
  rw [h1, f_add_self, add_zero]

lemma diff_mul_lin {n : ℕ} (l₁ l₂ : V n →ₗ[F] F) (a x : V n) :
    diff (fun y => l₁ y * l₂ y) a x = l₁ a * l₂ x + l₁ x * l₂ a + l₁ a * l₂ a := by
  simp only [diff_eq_add, map_add]
  have h1 : (l₁ x + l₁ a) * (l₂ x + l₂ a) + l₁ x * l₂ x =
      (l₁ x * l₂ x + l₁ x * l₂ x) + (l₁ a * l₂ x + l₁ x * l₂ a + l₁ a * l₂ a) := by ring
  rw [h1, f_add_self, zero_add]

lemma diff2_mul_lin {n : ℕ} (l₁ l₂ : V n →ₗ[F] F) (a b x : V n) :
    diff (diff (fun y => l₁ y * l₂ y) a) b x = l₁ a * l₂ b + l₁ b * l₂ a := by
  have hfun : diff (fun y => l₁ y * l₂ y) a = fun y => l₁ a * l₂ y + l₁ y * l₂ a + l₁ a * l₂ a := by
    funext y; exact diff_mul_lin l₁ l₂ a y
  rw [hfun, diff_eq_add]
  simp only [map_add]
  have h1 : (l₁ a * (l₂ x + l₂ b) + (l₁ x + l₁ b) * l₂ a + l₁ a * l₂ a) +
      (l₁ a * l₂ x + l₁ x * l₂ a + l₁ a * l₂ a) =
      (l₁ a * l₂ x + l₁ a * l₂ x) + (l₁ x * l₂ a + l₁ x * l₂ a) +
      (l₁ a * l₂ a + l₁ a * l₂ a) + (l₁ a * l₂ b + l₁ b * l₂ a) := by ring
  rw [h1]; simp only [f_add_self, zero_add]

lemma diff3_mul_lin {n : ℕ} (l₁ l₂ : V n →ₗ[F] F) (a b c x : V n) :
    diff (diff (diff (fun y => l₁ y * l₂ y) a) b) c x = 0 := by
  have hfun : diff (diff (fun y => l₁ y * l₂ y) a) b = fun _ => l₁ a * l₂ b + l₁ b * l₂ a := by
    funext y; exact diff2_mul_lin l₁ l₂ a b y
  rw [hfun]
  exact diff_const _ c x

lemma diff_sum {n : ℕ} {ι : Type*} (s : Finset ι) (f : ι → V n → F) (a x : V n) :
    diff (fun y => ∑ i ∈ s, f i y) a x = ∑ i ∈ s, diff (f i) a x := by
  simp only [diff_eq_add, ← Finset.sum_add_distrib]

lemma diff3_quad {n : ℕ} {q : V n → F} (hq : quad q) (a b c x : V n) :
    diff (diff (diff q a) b) c x = 0 := by
  rcases hq with ⟨s, h, M, hq⟩
  have hq' : q = fun y => s + dotProduct h y + ∑ i, ∑ j, M i j * y i * y j := funext hq
  rw [hq']
  have h1 : diff (fun y => s + dotProduct h y + ∑ i, ∑ j, M i j * y i * y j) a =
      fun y => dotProduct h a + ∑ i, ∑ j, diff (fun z => (M i j * z i) * z j) a y := by
    funext y
    rw [diff_add_fun, diff_add_fun, diff_const, zero_add, diff_dotProduct, diff_sum]
    congr 1; apply Finset.sum_congr rfl; intro i _; rw [diff_sum]
  rw [h1]
  have h2 : diff (fun y => dotProduct h a + ∑ i, ∑ j, diff (fun z => (M i j * z i) * z j) a y) b =
      fun y => ∑ i, ∑ j, diff (diff (fun z => (M i j * z i) * z j) a) b y := by
    funext y
    rw [diff_add_fun, diff_const, zero_add, diff_sum]
    apply Finset.sum_congr rfl; intro i _; rw [diff_sum]
  rw [h2, diff_sum]
  apply Finset.sum_eq_zero; intro i _
  rw [diff_sum]
  apply Finset.sum_eq_zero; intro j _
  let l₁ : V n →ₗ[F] F :=
    { toFun := fun z => M i j * z i
      map_add' := fun u v => by simp [mul_add]
      map_smul' := fun r u => by simp; ring }
  let l₂ : V n →ₗ[F] F :=
    { toFun := fun z => z j
      map_add' := fun u v => by simp
      map_smul' := fun r u => by simp }
  exact diff3_mul_lin l₁ l₂ a b c x

lemma third_quad {n : ℕ} {q : V n → F} (hq : quad q) (a b c : V n) :
    third q a b c = 0 :=
  diff3_quad hq a b c 0

lemma third_add_fun {n : ℕ} (g₁ g₂ : V n → F) (a b c : V n) :
    third (fun y => g₁ y + g₂ y) a b c = third g₁ a b c + third g₂ a b c := by
  unfold third
  have h1 : diff (fun y => g₁ y + g₂ y) a = fun y => diff g₁ a y + diff g₂ a y :=
    funext (diff_add_fun g₁ g₂ a)
  rw [h1]
  have h2 : diff (fun y => diff g₁ a y + diff g₂ a y) b =
      fun y => diff (diff g₁ a) b y + diff (diff g₂ a) b y :=
    funext (diff_add_fun _ _ b)
  rw [h2]
  exact diff_add_fun _ _ c 0

lemma third_sum {n : ℕ} {ι : Type*} (s : Finset ι) (f : ι → V n → F) (a b c : V n) :
    third (fun y => ∑ i ∈ s, f i y) a b c = ∑ i ∈ s, third (f i) a b c := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    unfold third
    have h1 : diff (fun _ : V n => (0 : F)) a = fun _ => 0 := funext (diff_const 0 a)
    rw [h1]
    have h2 : diff (fun _ : V n => (0 : F)) b = fun _ => 0 := funext (diff_const 0 b)
    rw [h2, diff_const]
  | @insert i s hi ih =>
    have hfun : (fun y => ∑ j ∈ insert i s, f j y) = fun y => f i y + ∑ j ∈ s, f j y := by
      funext y; exact Finset.sum_insert hi
    rw [hfun, third_add_fun, ih, Finset.sum_insert hi]

def det3 (u v w : Fin 3 → F) : F :=
  u 0 * v 1 * w 2 + u 0 * v 2 * w 1 +
  u 1 * v 0 * w 2 + u 1 * v 2 * w 0 +
  u 2 * v 0 * w 1 + u 2 * v 1 * w 0

lemma third_triple {n : ℕ} (l₀ l₁ l₂ : V n →ₗ[F] F) (a b c : V n) :
    third (fun x => l₀ x * l₁ x * l₂ x) a b c =
      det3 ![l₀ a, l₁ a, l₂ a] ![l₀ b, l₁ b, l₂ b] ![l₀ c, l₁ c, l₂ c] := by
  simp only [third, diff_eq_add, det3, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, map_add, map_zero, zero_add]
  have h2 : (2 : F) = 0 := by decide
  have h4 : (4 : F) = 0 := by decide
  ring_nf
  simp [h2, h4]

lemma diff3_triple_const {n : ℕ} (l₀ l₁ l₂ : V n →ₗ[F] F) (a b c x : V n) :
    diff (diff (diff (fun y => l₀ y * l₁ y * l₂ y) a) b) c x =
      third (fun y => l₀ y * l₁ y * l₂ y) a b c := by
  have h1 : diff (fun y => l₀ y * l₁ y * l₂ y) a =
      fun y => l₀ a * (l₁ y * l₂ y) + l₁ a * (l₀ y * l₂ y) + l₂ a * (l₀ y * l₁ y) +
        (l₀ a * l₁ a * l₂ y + l₀ a * l₂ a * l₁ y + l₁ a * l₂ a * l₀ y + l₀ a * l₁ a * l₂ a) := by
    funext y
    simp only [diff_eq_add, map_add]
    have h2 : (2 : F) = 0 := by decide
    ring_nf; simp [h2]
  have h2 : diff (diff (fun y => l₀ y * l₁ y * l₂ y) a) b =
      fun y =>
        l₀ a * (l₁ b * l₂ y + l₁ y * l₂ b + l₁ b * l₂ b) +
        l₁ a * (l₀ b * l₂ y + l₀ y * l₂ b + l₀ b * l₂ b) +
        l₂ a * (l₀ b * l₁ y + l₀ y * l₁ b + l₀ b * l₁ b) +
        (l₀ a * l₁ a * l₂ b + l₀ a * l₂ a * l₁ b + l₁ a * l₂ a * l₀ b) := by
    funext y
    rw [h1, diff_eq_add]
    simp only [map_add]
    have h2 : (2 : F) = 0 := by decide
    ring_nf; simp [h2]
  have h3 : ∀ z, diff (diff (diff (fun y => l₀ y * l₁ y * l₂ y) a) b) c z =
      det3 ![l₀ a, l₁ a, l₂ a] ![l₀ b, l₁ b, l₂ b] ![l₀ c, l₁ c, l₂ c] := by
    intro z
    rw [h2, diff_eq_add]
    simp only [map_add, det3, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two]
    have h2' : (2 : F) = 0 := by decide
    ring_nf; simp [h2']; ring
  rw [h3 x, third, h3 0]

lemma prefixVec_step {n : ℕ} (x : V n) (k : ℕ) (hk : k < n) :
    (fun i : Fin n => if i.val < k + 1 then x i else 0) =
      (fun i : Fin n => if i.val < k then x i else 0) +
        (if x ⟨k, hk⟩ = 1 then unit ⟨k, hk⟩ else 0) := by
  funext i
  simp only [Pi.add_apply]
  by_cases hi : i.val < k
  · have h1 : i.val < k + 1 := by omega
    have hne : (⟨k, hk⟩ : Fin n) ≠ i := by intro he; have := congrArg Fin.val he; dsimp at this; omega
    simp only [h1, hi, ite_true]
    split_ifs <;> simp [unit, hne]
  · by_cases heq : i.val = k
    · have hi' : i = ⟨k, hk⟩ := Fin.ext heq
      subst hi'
      simp only [Nat.lt_succ_self, ite_true, Nat.lt_irrefl, ite_false, zero_add]
      rcases f_cases (x ⟨k, hk⟩) with hx | hx
      · simp [hx]
      · simp [hx, unit]
    · have h1 : ¬ (i.val < k + 1) := by omega
      have hne : (⟨k, hk⟩ : Fin n) ≠ i := by intro he; have := congrArg Fin.val he; dsimp at this; omega
      simp only [h1, hi, ite_false, zero_add]
      split_ifs <;> simp [unit, hne]

lemma const_of_diff_eq_zero {n : ℕ} {f : V n → F} (h : ∀ a x, diff f a x = 0) (x : V n) :
    f x = f 0 := by
  have hx := h x 0
  rw [diff_eq_add, zero_add] at hx
  have hx' := congrArg (· + f 0) hx
  simp only [add_assoc, f_add_self, add_zero, zero_add] at hx'
  exact hx'

lemma affine_of_diff2_eq_zero {n : ℕ} {f : V n → F}
    (h : ∀ a b x, diff (diff f a) b x = 0) : affine f := by
  refine ⟨f 0, fun i => diff f (unit i) 0, ?_⟩
  have hconst : ∀ a x, diff f a x = diff f a 0 := fun a x => const_of_diff_eq_zero (fun b y => h a b y) x
  have hpref : ∀ k (hk : k ≤ n) (x : V n),
      f (fun i : Fin n => if i.val < k then x i else 0) =
        f 0 + ∑ i : Fin n, if i.val < k then diff f (unit i) 0 * x i else 0 := by
    intro k hk x
    induction k with
    | zero =>
      simp only [Nat.not_lt_zero, ite_false, Finset.sum_const_zero, add_zero]
      rfl
    | succ k ih =>
      have hlt : k < n := by omega
      rw [prefixVec_step x k hlt]
      have hsum : (∑ i : Fin n, if i.val < k + 1 then diff f (unit i) 0 * x i else 0) =
          (∑ i : Fin n, if i.val < k then diff f (unit i) 0 * x i else 0) +
            diff f (unit ⟨k, hlt⟩) 0 * x ⟨k, hlt⟩ := by
        rw [← Finset.sum_erase_add _ _ (Finset.mem_univ (⟨k, hlt⟩ : Fin n))]
        simp only [Nat.lt_succ_self, ite_true]
        congr 1
        rw [← Finset.sum_erase_add _ _ (Finset.mem_univ (⟨k, hlt⟩ : Fin n))]
        simp only [Nat.lt_irrefl, ite_false, add_zero]
        apply Finset.sum_congr rfl
        intro i hi
        have hne : i.val ≠ k := fun he => (Finset.mem_erase.mp hi).1 (Fin.ext he)
        have hiff : i.val < k + 1 ↔ i.val < k := by omega
        simp [hiff]
      rw [hsum]
      rcases f_cases (x ⟨k, hlt⟩) with hx | hx
      · simp [hx, ih (by omega)]
      · simp only [hx, ite_true, mul_one]
        have hd := hconst (unit ⟨k, hlt⟩) (fun i : Fin n => if i.val < k then x i else 0)
        rw [diff_eq_add] at hd
        have hd' := congrArg (· + f (fun i : Fin n => if i.val < k then x i else 0)) hd
        simp only [add_assoc, f_add_self, add_zero] at hd'
        rw [hd', ih (by omega)]
        ring
  intro x
  have hx := hpref n le_rfl x
  have h1 : (fun i : Fin n => if i.val < n then x i else 0) = x := by
    funext i; simp [i.isLt]
  rw [h1] at hx
  rw [hx]
  congr 1
  simp only [dotProduct]
  apply Finset.sum_congr rfl
  intro i _; simp [i.isLt]

lemma quad_of_diff3_eq_zero {n : ℕ} {f : V n → F}
    (h : ∀ a b c x, diff (diff (diff f a) b) c x = 0) : quad f := by
  have haff : ∀ i : Fin n, affine (diff f (unit i)) := fun i =>
    affine_of_diff2_eq_zero (fun b c x => h (unit i) b c x)
  choose c₀ L hL using haff
  refine ⟨f 0, c₀, fun i j => if j.val < i.val then L i j else 0, ?_⟩
  have hpref : ∀ k (hk : k ≤ n) (x : V n),
      f (fun i : Fin n => if i.val < k then x i else 0) =
        f 0 + (∑ i : Fin n, if i.val < k then c₀ i * x i else 0) +
          ∑ i : Fin n, if i.val < k then (∑ j : Fin n, (if j.val < i.val then L i j else 0) * x j * x i) else 0 := by
    intro k hk x
    induction k with
    | zero =>
      simp only [Nat.not_lt_zero, ite_false, Finset.sum_const_zero, add_zero]
      rfl
    | succ k ih =>
      have hlt : k < n := by omega
      rw [prefixVec_step x k hlt]
      have hsum1 : (∑ i : Fin n, if i.val < k + 1 then c₀ i * x i else 0) =
          (∑ i : Fin n, if i.val < k then c₀ i * x i else 0) + c₀ ⟨k, hlt⟩ * x ⟨k, hlt⟩ := by
        rw [← Finset.sum_erase_add _ _ (Finset.mem_univ (⟨k, hlt⟩ : Fin n))]
        simp only [Nat.lt_succ_self, ite_true]
        congr 1
        rw [← Finset.sum_erase_add _ _ (Finset.mem_univ (⟨k, hlt⟩ : Fin n))]
        simp only [Nat.lt_irrefl, ite_false, add_zero]
        apply Finset.sum_congr rfl
        intro i hi
        have hne : i.val ≠ k := fun he => (Finset.mem_erase.mp hi).1 (Fin.ext he)
        have hiff : i.val < k + 1 ↔ i.val < k := by omega
        simp [hiff]
      have hsum2 :
          (∑ i : Fin n, if i.val < k + 1 then (∑ j : Fin n, (if j.val < i.val then L i j else 0) * x j * x i) else 0) =
          (∑ i : Fin n, if i.val < k then (∑ j : Fin n, (if j.val < i.val then L i j else 0) * x j * x i) else 0) +
            ∑ j : Fin n, (if j.val < k then L ⟨k, hlt⟩ j else 0) * x j * x ⟨k, hlt⟩ := by
        rw [← Finset.sum_erase_add _ _ (Finset.mem_univ (⟨k, hlt⟩ : Fin n))]
        simp only [Nat.lt_succ_self, ite_true]
        congr 1
        rw [← Finset.sum_erase_add _ _ (Finset.mem_univ (⟨k, hlt⟩ : Fin n))]
        simp only [Nat.lt_irrefl, ite_false, add_zero]
        apply Finset.sum_congr rfl
        intro i hi
        have hne : i.val ≠ k := fun he => (Finset.mem_erase.mp hi).1 (Fin.ext he)
        have hiff : i.val < k + 1 ↔ i.val < k := by omega
        simp [hiff]
      rw [hsum1, hsum2]
      rcases f_cases (x ⟨k, hlt⟩) with hx | hx
      · simp [hx, ih (by omega)]
      · simp only [hx, ite_true, mul_one]
        have hd := hL ⟨k, hlt⟩ (fun i : Fin n => if i.val < k then x i else 0)
        rw [diff_eq_add] at hd
        have hd' := congrArg (· + f (fun i : Fin n => if i.val < k then x i else 0)) hd
        simp only [add_assoc, f_add_self, add_zero] at hd'
        rw [hd', ih (by omega)]
        have hdot : dotProduct (L ⟨k, hlt⟩) (fun i : Fin n => if i.val < k then x i else 0) =
            ∑ j : Fin n, (if j.val < k then L ⟨k, hlt⟩ j else 0) * x j := by
          simp only [dotProduct]
          apply Finset.sum_congr rfl
          intro j _; split_ifs <;> simp
        rw [hdot]; ring
  intro x
  have hx := hpref n le_rfl x
  have h1 : (fun i : Fin n => if i.val < n then x i else 0) = x := by
    funext i; simp [i.isLt]
  rw [h1] at hx
  rw [hx]
  congr 1
  · congr 1
    simp only [dotProduct]
    apply Finset.sum_congr rfl
    intro i _; simp [i.isLt]
  · apply Finset.sum_congr rfl
    intro i _
    simp only [i.isLt, ite_true]
    apply Finset.sum_congr rfl
    intro j _; ring

lemma diff3_const_of_cubic {n : ℕ} {g : V n → F} (hg : cubic g) (a b c x : V n) :
    diff (diff (diff g a) b) c x = third g a b c :=
  const_of_diff_eq_zero (fun d y => hg a b c d y) x

lemma third_add_left {n : ℕ} {g : V n → F} (hg : cubic g) (a₁ a₂ b c : V n) :
    third g (a₁ + a₂) b c = third g a₁ b c + third g a₂ b c := by
  unfold third
  have h1 : diff g (a₁ + a₂) = fun x => diff g a₁ (x + a₂) + diff g a₂ x :=
    funext (diff_add_dir g a₁ a₂)
  rw [h1]
  have h2 : diff (fun x => diff g a₁ (x + a₂) + diff g a₂ x) b =
      fun x => diff (diff g a₁) b (x + a₂) + diff (diff g a₂) b x := by
    funext x
    rw [diff_add_fun]
    congr 1
    simp only [diff_eq_add, add_assoc, add_comm a₂ b]
  rw [h2, diff_add_fun]
  congr 1
  have h3 : diff (fun x => diff (diff g a₁) b (x + a₂)) c 0 =
      diff (diff (diff g a₁) b) c a₂ := by
    simp only [diff_eq_add, zero_add, add_comm a₂ c]
  rw [h3, diff3_const_of_cubic hg]; rfl

lemma third_symm12 {n : ℕ} (g : V n → F) (a b c : V n) :
    third g a b c = third g b a c := by
  unfold third
  have h : diff (diff g a) b = diff (diff g b) a := funext (diff_comm g a b)
  rw [h]

lemma third_symm23 {n : ℕ} (g : V n → F) (a b c : V n) :
    third g a b c = third g a c b := by
  unfold third
  exact diff_comm (diff g a) b c 0

lemma third_self12 {n : ℕ} (g : V n → F) (a c : V n) :
    third g a a c = 0 := by
  unfold third
  have h : diff (diff g a) a = fun _ => 0 := funext (diff_self g a)
  rw [h, diff_const]

lemma third_self23 {n : ℕ} (g : V n → F) (a b : V n) :
    third g a b b = 0 := by
  rw [third_symm12, third_symm23, third_symm12]
  exact third_self12 g b a

lemma third_add_mid {n : ℕ} {g : V n → F} (hg : cubic g) (a b₁ b₂ c : V n) :
    third g a (b₁ + b₂) c = third g a b₁ c + third g a b₂ c := by
  rw [third_symm12 g a (b₁ + b₂) c, third_add_left hg, third_symm12 g b₁ a c, third_symm12 g b₂ a c]

lemma third_add_right {n : ℕ} {g : V n → F} (hg : cubic g) (a b c₁ c₂ : V n) :
    third g a b (c₁ + c₂) = third g a b c₁ + third g a b c₂ := by
  rw [third_symm23 g a b (c₁ + c₂), third_add_mid hg, third_symm23 g a c₁ b, third_symm23 g a c₂ b]

lemma third_zero_left {n : ℕ} (g : V n → F) (b c : V n) : third g 0 b c = 0 := by
  unfold third
  have h1 : diff g 0 = fun _ => 0 := funext (diff_zero g)
  rw [h1]
  have h2 : diff (fun _ : V n => (0 : F)) b = fun _ => 0 := funext (diff_const 0 b)
  rw [h2, diff_const]

lemma third_smul_left {n : ℕ} (g : V n → F) (r : F) (a b c : V n) :
    third g (r • a) b c = r * third g a b c := by
  rcases f_cases r with rfl | rfl
  · simp [third_zero_left]
  · simp

lemma third_smul_mid {n : ℕ} (g : V n → F) (r : F) (a b c : V n) :
    third g a (r • b) c = r * third g a b c := by
  rw [third_symm12, third_smul_left, third_symm12]

lemma third_smul_right {n : ℕ} (g : V n → F) (r : F) (a b c : V n) :
    third g a b (r • c) = r * third g a b c := by
  rw [third_symm23, third_smul_mid, third_symm23]

def bilinMap {n : ℕ} {g : V n → F} (hg : cubic g) (u : V n) : V n →ₗ[F] (V n →ₗ[F] F) where
  toFun v :=
    { toFun := fun w => third g u v w
      map_add' := fun w₁ w₂ => third_add_right hg u v w₁ w₂
      map_smul' := fun r w => by simp [third_smul_right] }
  map_add' v₁ v₂ := by apply LinearMap.ext; intro w; exact third_add_mid hg u v₁ v₂ w
  map_smul' r v := by apply LinearMap.ext; intro w; simp [third_smul_mid]

lemma vec_eq_sum_unit {n : ℕ} (v : V n) : v = ∑ i : Fin n, v i • unit i := by
  funext j
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, unit]
  rw [Finset.sum_eq_single j]
  · simp
  · intro i _ hij; simp [hij]
  · intro hj; exact (hj (Finset.mem_univ j)).elim

lemma rankAt_eq_finrank_range {n : ℕ} {g : V n → F} (hg : cubic g) (u : V n) :
    rankAt g u = Module.finrank F (LinearMap.range (bilinMap hg u)) := by
  unfold rankAt Matrix.rank
  let M : Matrix (Fin n) (Fin n) F := Matrix.of (fun i j : Fin n => third g u (unit i) (unit j))
  let e : (Fin n → F) ≃ₗ[F] (V n →ₗ[F] F) :=
    { toFun := fun c =>
        { toFun := fun w => dotProduct c w
          map_add' := fun w₁ w₂ => dotProduct_add c w₁ w₂
          map_smul' := fun r w => by simp [dotProduct_smul] }
      map_add' := fun c₁ c₂ => by apply LinearMap.ext; intro w; exact add_dotProduct c₁ c₂ w
      map_smul' := fun r c => by apply LinearMap.ext; intro w; simp [smul_dotProduct]
      invFun := fun f i => f (unit i)
      left_inv := fun c => by
        funext i
        change dotProduct c (unit i) = c i
        simp only [dotProduct, unit]
        rw [Finset.sum_eq_single i]
        · simp
        · intro j _ hji; simp [Ne.symm hji]
        · intro hi; exact (hi (Finset.mem_univ i)).elim
      right_inv := fun f => by
        apply LinearMap.ext; intro w
        change dotProduct (fun i => f (unit i)) w = f w
        conv_rhs => rw [vec_eq_sum_unit w]
        simp only [map_sum, map_smul, smul_eq_mul, dotProduct]
        apply Finset.sum_congr rfl; intro i _; ring }
  have hcomp : e.toLinearMap.comp (Matrix.mulVecLin M) = bilinMap hg u := by
    apply LinearMap.ext; intro v; apply LinearMap.ext; intro w
    change dotProduct (Matrix.mulVec M v) w = third g u v w
    conv_rhs => rw [vec_eq_sum_unit v, vec_eq_sum_unit w]
    simp only [dotProduct, Matrix.mulVec, M, Matrix.of_apply]
    have h1 : ∀ a : V n, third g u a (∑ j : Fin n, w j • unit j) =
        ∑ j : Fin n, w j * third g u a (unit j) := by
      intro a
      have hm := map_sum (bilinMap hg u a) (fun j : Fin n => w j • unit j) Finset.univ
      refine hm.trans (Finset.sum_congr rfl fun j _ => ?_)
      change third g u a (w j • unit j) = _; exact third_smul_right g _ _ _ _
    rw [h1]
    have h2 : ∀ j : Fin n, third g u (∑ i : Fin n, v i • unit i) (unit j) =
        ∑ i : Fin n, v i * third g u (unit i) (unit j) := by
      intro j
      have hm := map_sum (bilinMap hg u) (fun i : Fin n => v i • unit i) Finset.univ
      have hm' := LinearMap.congr_fun hm (unit j)
      change third g u (∑ i : Fin n, v i • unit i) (unit j) =
        (∑ i : Fin n, (bilinMap hg u) (v i • unit i)) (unit j) at hm'
      rw [hm', LinearMap.sum_apply]
      apply Finset.sum_congr rfl; intro i _
      change third g u (v i • unit i) (unit j) = _; exact third_smul_mid g _ _ _ _
    simp_rw [h2, Finset.mul_sum]
    apply Finset.sum_congr rfl; intro j _
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl; intro i _
    rw [third_symm23]; ring
  rw [← hcomp, LinearMap.range_comp, LinearEquiv.finrank_map_eq]

lemma finrank_range_pullback {U W : Type*} [AddCommGroup U] [Module F U] [FiniteDimensional F U]
    [AddCommGroup W] [Module F W] [FiniteDimensional F W]
    (L : U →ₗ[F] W) (hL : Function.Surjective L)
    (B : W →ₗ[F] (W →ₗ[F] F)) :
    Module.finrank F (LinearMap.range ((L.dualMap.comp B).comp L)) =
      Module.finrank F (LinearMap.range B) := by
  have hinj : Function.Injective L.dualMap := by
    intro f₁ f₂ hf
    apply LinearMap.ext; intro w
    obtain ⟨u, rfl⟩ := hL w
    exact LinearMap.congr_fun hf u
  rw [LinearMap.range_comp, LinearMap.range_eq_top.mpr hL, Submodule.map_top,
    LinearMap.range_comp]
  let f_lin : LinearMap.range B →ₗ[F] Submodule.map L.dualMap (LinearMap.range B) :=
    { toFun := fun ⟨f, hf⟩ => ⟨L.dualMap f, Submodule.mem_map_of_mem hf⟩
      map_add' := fun _ _ => Subtype.ext (map_add _ _ _)
      map_smul' := fun _ _ => Subtype.ext (map_smul _ _ _) }
  let e : LinearMap.range B ≃ₗ[F] Submodule.map L.dualMap (LinearMap.range B) :=
    LinearEquiv.ofBijective f_lin
      ⟨fun ⟨f₁, _⟩ ⟨f₂, _⟩ h => Subtype.ext (hinj (by simpa [f_lin] using congrArg Subtype.val h)),
       fun ⟨_, ⟨f, hf, rfl⟩⟩ => ⟨⟨f, hf⟩, rfl⟩⟩
  exact e.finrank_eq.symm

lemma rank_restrict_hyperplane {U : Type*} [AddCommGroup U] [Module F U] [FiniteDimensional F U]
    (B : U →ₗ[F] (U →ₗ[F] F))
    (hsym : ∀ x y, B x y = B y x) (halt : ∀ x, B x x = 0)
    (α : U →ₗ[F] F) (hα : α ≠ 0) :
    let H := LinearMap.ker α
    let ι := H.subtype
    let BH : H →ₗ[F] (H →ₗ[F] F) := (ι.dualMap.comp B).comp ι
    (α ∈ LinearMap.range B →
      Module.finrank F (LinearMap.range BH) + 2 = Module.finrank F (LinearMap.range B)) ∧
    (α ∉ LinearMap.range B →
      Module.finrank F (LinearMap.range BH) = Module.finrank F (LinearMap.range B)) := by
  intro H ι BH
  have hH_dim : Module.finrank F H + 1 = Module.finrank F U := by
    have htop : LinearMap.range α = ⊤ := by
      rw [Submodule.eq_top_iff']
      intro r
      obtain ⟨u, hu⟩ : ∃ u, α u ≠ 0 := by
        by_contra h; push Not at h; exact hα (LinearMap.ext h)
      have hu1 : α u = 1 := (f_cases (α u)).resolve_left hu
      rcases f_cases r with rfl | rfl
      · exact ⟨0, map_zero α⟩
      · exact ⟨u, hu1⟩
    have hr := LinearMap.finrank_range_add_finrank_ker α
    rw [htop, finrank_top, Module.finrank_self] at hr
    change 1 + Module.finrank F H = Module.finrank F U at hr
    omega
  have hker_sub_iff : LinearMap.ker B ≤ H ↔ α ∈ LinearMap.range B := by
    constructor
    · intro hsub
      have hB_dual : ∀ f ∈ LinearMap.range B, LinearMap.ker B ≤ LinearMap.ker f := by
        rintro _ ⟨x, rfl⟩ y hy
        rw [LinearMap.mem_ker] at hy ⊢
        rw [hsym, hy]; rfl
      let ann : Submodule F (U →ₗ[F] F) :=
        { carrier := {f | LinearMap.ker B ≤ LinearMap.ker f}, add_mem' := fun {f₁ f₂} h₁ h₂ y hy => by
            rw [LinearMap.mem_ker] at hy ⊢
            simp [LinearMap.mem_ker.mp (h₁ hy), LinearMap.mem_ker.mp (h₂ hy)]
          zero_mem' := fun y _ => by simp
          smul_mem' := fun r {f} hf y hy => by
            rw [LinearMap.mem_ker] at hy ⊢
            simp [LinearMap.mem_ker.mp (hf hy)] }
      have hle : LinearMap.range B ≤ ann := hB_dual
      have hdim_ann : Module.finrank F ann = Module.finrank F (LinearMap.range B) := by
        let res : (U →ₗ[F] F) →ₗ[F] (LinearMap.ker B →ₗ[F] F) := (LinearMap.ker B).subtype.dualMap
        have hker_res : LinearMap.ker res = ann := by
          ext f
          constructor
          · intro hf y hy
            rw [LinearMap.mem_ker] at hf ⊢
            exact LinearMap.congr_fun hf ⟨y, hy⟩
          · intro hf
            rw [LinearMap.mem_ker]
            apply LinearMap.ext; rintro ⟨y, hy⟩
            exact LinearMap.mem_ker.mp (hf hy)
        have hsurj : Function.Surjective res := by
          intro g
          obtain ⟨p, hp⟩ := Submodule.exists_isCompl (LinearMap.ker B)
          let h1 := Submodule.projectionOnto (LinearMap.ker B) p hp
          refine ⟨g.comp h1, ?_⟩
          apply LinearMap.ext; rintro ⟨x, hx⟩
          change g (h1 x) = g ⟨x, hx⟩
          have : h1 x = ⟨x, hx⟩ := Submodule.projectionOnto_apply_left hp ⟨x, hx⟩
          rw [this]
        have hr1 := LinearMap.finrank_range_add_finrank_ker res
        rw [LinearMap.range_eq_top.mpr hsurj, finrank_top, hker_res] at hr1
        have hd1 : Module.finrank F (U →ₗ[F] F) = Module.finrank F U :=
          Subspace.dual_finrank_eq
        have hd2 : Module.finrank F (LinearMap.ker B →ₗ[F] F) = Module.finrank F (LinearMap.ker B) :=
          Subspace.dual_finrank_eq
        have hr2 := LinearMap.finrank_range_add_finrank_ker B
        omega
      have heq : LinearMap.range B = ann :=
        Submodule.eq_of_le_of_finrank_eq hle hdim_ann.symm
      rw [heq]
      exact hsub
    · rintro ⟨w, hw⟩ y hy
      rw [LinearMap.mem_ker] at hy ⊢
      rw [← hw, hsym, hy]; rfl
  let B₁ : H →ₗ[F] (U →ₗ[F] F) := B.comp ι
  have hkerB₁ : Module.finrank F (LinearMap.ker B₁) =
      Module.finrank F (LinearMap.ker B ⊓ H : Submodule F U) := by
    let e : LinearMap.ker B₁ ≃ₗ[F] (LinearMap.ker B ⊓ H : Submodule F U) :=
      { toFun := fun ⟨⟨x, hx⟩, hbx⟩ => ⟨x, ⟨hbx, hx⟩⟩
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl
        invFun := fun ⟨x, ⟨hbx, hx⟩⟩ => ⟨⟨x, hx⟩, hbx⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    exact e.finrank_eq
  have hker_dual : LinearMap.ker ι.dualMap = Submodule.span F {α} := by
    ext f
    rw [LinearMap.mem_ker, Submodule.mem_span_singleton]
    constructor
    · intro hf
      by_cases hf0 : f = 0
      · exact ⟨0, by simp [hf0]⟩
      · refine ⟨1, ?_⟩
        apply LinearMap.ext; intro u
        by_cases hau : α u = 0
        · rw [one_smul, hau]; exact (LinearMap.congr_fun hf ⟨u, hau⟩).symm
        · have hau1 : α u = 1 := (f_cases (α u)).resolve_left hau
          obtain ⟨v, hv⟩ : ∃ v, f v ≠ 0 := by
            by_contra h; push Not at h; exact hf0 (LinearMap.ext h)
          have hv1 : f v = 1 := (f_cases (f v)).resolve_left hv
          have hav : α v ≠ 0 := by
            intro h0; exact hv (LinearMap.congr_fun hf ⟨v, h0⟩)
          have hav1 : α v = 1 := (f_cases (α v)).resolve_left hav
          have huv : α (u + v) = 0 := by rw [map_add, hau1, hav1, f_add_self]
          have hfuv : f (u + v) = 0 := LinearMap.congr_fun hf ⟨u + v, huv⟩
          rw [map_add, hv1] at hfuv
          have hfu : f u = 1 := by
            rcases f_cases (f u) with h | h
            · rw [h, zero_add] at hfuv; exact absurd hfuv (by decide)
            · exact h
          rw [one_smul, hau1, hfu]
    · rintro ⟨r, rfl⟩
      apply LinearMap.ext; rintro ⟨x, hx⟩
      change r * α x = 0
      rw [LinearMap.mem_ker.mp hx, mul_zero]
  have hr_B : Module.finrank F (LinearMap.range B) + Module.finrank F (LinearMap.ker B) =
      Module.finrank F U := LinearMap.finrank_range_add_finrank_ker B
  have hr_B₁ : Module.finrank F (LinearMap.range B₁) + Module.finrank F (LinearMap.ker B₁) =
      Module.finrank F H := LinearMap.finrank_range_add_finrank_ker B₁
  have hr_BH : Module.finrank F (LinearMap.range BH) + Module.finrank F (LinearMap.ker BH) =
      Module.finrank F H := LinearMap.finrank_range_add_finrank_ker BH
  constructor
  · intro hmem
    have hsub : LinearMap.ker B ≤ H := hker_sub_iff.mpr hmem
    have hinf : (LinearMap.ker B ⊓ H : Submodule F U) = LinearMap.ker B := inf_eq_left.mpr hsub
    rw [hinf] at hkerB₁
    obtain ⟨w, hw⟩ := hmem
    have hwH : w ∈ H := by
      rw [LinearMap.mem_ker, ← hw, halt]
    let wH : H := ⟨w, hwH⟩
    have hwH_ne : wH ≠ 0 := by
      intro h0; apply hα; rw [← hw]
      have : w = 0 := congrArg Subtype.val h0
      rw [this, map_zero]
    have hkerBH_eq : LinearMap.ker BH = (LinearMap.ker B₁ ⊔ Submodule.span F {wH} : Submodule F H) := by
      ext x
      constructor
      · intro hx
        have hBx : B₁ x ∈ LinearMap.ker ι.dualMap := hx
        rw [hker_dual, Submodule.mem_span_singleton] at hBx
        rcases hBx with ⟨r, hr⟩
        rcases f_cases r with rfl | rfl
        · simp only [zero_smul] at hr
          exact Submodule.mem_sup_left (LinearMap.mem_ker.mpr hr.symm)
        · simp only [one_smul] at hr
          have hxker : x + wH ∈ LinearMap.ker B₁ := by
            rw [LinearMap.mem_ker, map_add]
            change B₁ x + B w = 0
            rw [← hr, hw]
            apply LinearMap.ext; intro u; exact f_add_self (α u)
          have hx_eq : x = (x + wH) + wH := by
            apply Subtype.ext
            change x.1 = x.1 + w + w
            have hww : w + w = 0 := by
              have : (1 + 1 : F) • w = 0 := by rw [f_add_self, zero_smul]
              rwa [add_smul, one_smul] at this
            rw [add_assoc, hww, add_zero]
          rw [hx_eq]
          exact Submodule.add_mem _ (Submodule.mem_sup_left hxker)
            (Submodule.mem_sup_right (Submodule.subset_span (Set.mem_singleton wH)))
      · intro hx
        rcases Submodule.mem_sup.mp hx with ⟨a, ha, b, hb, rfl⟩
        rw [LinearMap.mem_ker, map_add]
        have ha0 : BH a = 0 := by change ι.dualMap (B₁ a) = 0; rw [LinearMap.mem_ker.mp ha, map_zero]
        rw [Submodule.mem_span_singleton] at hb
        rcases hb with ⟨r, rfl⟩
        have hb0 : BH (r • wH) = 0 := by
          rw [map_smul]
          have : BH wH = 0 := by
            change ι.dualMap (B w) = 0; rw [hw]
            exact LinearMap.mem_ker.mp (hker_dual.symm ▸ Submodule.subset_span (Set.mem_singleton α))
          rw [this, smul_zero]
        rw [ha0, hb0, add_zero]
    have hinf_bot : (LinearMap.ker B₁ ⊓ Submodule.span F {wH} : Submodule F H) = ⊥ := by
      rw [eq_bot_iff]; rintro x ⟨hx1, hx2⟩
      change x ∈ Submodule.span F {wH} at hx2
      rw [Submodule.mem_span_singleton] at hx2
      rcases hx2 with ⟨r, rfl⟩
      rcases f_cases r with rfl | rfl
      · simp
      · simp only [one_smul] at hx1
        have h0 : B₁ wH = 0 := LinearMap.mem_ker.mp hx1
        exact absurd (hw.symm.trans h0) hα
    have hmod := Submodule.finrank_sup_add_finrank_inf_eq (LinearMap.ker B₁) (Submodule.span F {wH})
    rw [← hkerBH_eq, hinf_bot, finrank_bot, add_zero, finrank_span_singleton hwH_ne] at hmod
    omega
  · intro hmem
    have hnsub : ¬ (LinearMap.ker B ≤ H) := fun h => hmem (hker_sub_iff.mp h)
    have hsup : (LinearMap.ker B ⊔ H : Submodule F U) = ⊤ := by
      have hgt : H < (LinearMap.ker B ⊔ H : Submodule F U) :=
        lt_of_le_of_ne le_sup_right (fun heq => hnsub (heq ▸ le_sup_left))
      have hle : Module.finrank F H < Module.finrank F (LinearMap.ker B ⊔ H : Submodule F U) :=
        Submodule.finrank_lt_finrank_of_lt hgt
      have hle2 : Module.finrank F (LinearMap.ker B ⊔ H : Submodule F U) ≤ Module.finrank F U :=
        Submodule.finrank_le _
      exact Submodule.eq_top_of_finrank_eq (by omega)
    have hmod := Submodule.finrank_sup_add_finrank_inf_eq (LinearMap.ker B) H
    rw [hsup, finrank_top] at hmod
    have hkerBH_eq : LinearMap.ker BH = LinearMap.ker B₁ := by
      ext x
      constructor
      · intro hx
        have hBx : B₁ x ∈ LinearMap.ker ι.dualMap := hx
        rw [hker_dual, Submodule.mem_span_singleton] at hBx
        rcases hBx with ⟨r, hr⟩
        rcases f_cases r with rfl | rfl
        · simp only [zero_smul] at hr; exact LinearMap.mem_ker.mpr hr.symm
        · simp only [one_smul] at hr; exact (hmem ⟨x.1, hr.symm⟩).elim
      · intro hx
        change ι.dualMap (B₁ x) = 0; rw [LinearMap.mem_ker.mp hx, map_zero]
    rw [hkerBH_eq] at hr_BH
    omega

def omegaE {c : ℕ} (a b d : E c) : F :=
  ∑ i : Fin c, det3 (fun s => a (i, s)) (fun s => b (i, s)) (fun s => d (i, s))

lemma det3_symm23 (u v w : Fin 3 → F) : det3 u v w = det3 u w v := by
  simp only [det3]; ring

lemma det3_self23 (u v : Fin 3 → F) : det3 u v v = 0 := by
  simp only [det3]
  have h1 : u 0 * v 1 * v 2 + u 0 * v 2 * v 1 + u 1 * v 0 * v 2 + u 1 * v 2 * v 0 +
      u 2 * v 0 * v 1 + u 2 * v 1 * v 0 =
      (u 0 * v 1 * v 2 + u 0 * v 1 * v 2) + (u 1 * v 0 * v 2 + u 1 * v 0 * v 2) +
      (u 2 * v 0 * v 1 + u 2 * v 0 * v 1) := by ring
  rw [h1]; simp only [f_add_self, zero_add]

lemma det3_add_mid (u v₁ v₂ w : Fin 3 → F) :
    det3 u (v₁ + v₂) w = det3 u v₁ w + det3 u v₂ w := by
  simp only [det3, Pi.add_apply]; ring

lemma det3_add_right (u v w₁ w₂ : Fin 3 → F) :
    det3 u v (w₁ + w₂) = det3 u v w₁ + det3 u v w₂ := by
  simp only [det3, Pi.add_apply]; ring

lemma det3_smul_mid (u : Fin 3 → F) (r : F) (v w : Fin 3 → F) :
    det3 u (r • v) w = r * det3 u v w := by
  simp only [det3, Pi.smul_apply, smul_eq_mul]; ring

lemma det3_smul_right (u v : Fin 3 → F) (r : F) (w : Fin 3 → F) :
    det3 u v (r • w) = r * det3 u v w := by
  simp only [det3, Pi.smul_apply, smul_eq_mul]; ring

def B3 (u : Fin 3 → F) : (Fin 3 → F) →ₗ[F] ((Fin 3 → F) →ₗ[F] F) where
  toFun v :=
    { toFun := fun w => det3 u v w
      map_add' := fun w₁ w₂ => det3_add_right u v w₁ w₂
      map_smul' := fun r w => by simp [det3_smul_right] }
  map_add' v₁ v₂ := by apply LinearMap.ext; intro w; exact det3_add_mid u v₁ v₂ w
  map_smul' r v := by apply LinearMap.ext; intro w; simp [det3_smul_mid]

lemma B3_range_iff (u : Fin 3 → F) (hu : u ≠ 0) (φ : (Fin 3 → F) →ₗ[F] F) :
    φ ∈ LinearMap.range (B3 u) ↔ φ u = 0 := by
  constructor
  · rintro ⟨v, rfl⟩
    change det3 u v u = 0
    rw [det3_symm23]
    have : det3 u u v = 0 := by
      simp only [det3]
      have h : u 0 * u 1 * v 2 + u 0 * u 2 * v 1 + u 1 * u 0 * v 2 + u 1 * u 2 * v 0 +
          u 2 * u 0 * v 1 + u 2 * u 1 * v 0 =
          (u 0 * u 1 * v 2 + u 0 * u 1 * v 2) + (u 0 * u 2 * v 1 + u 0 * u 2 * v 1) +
          (u 1 * u 2 * v 0 + u 1 * u 2 * v 0) := by ring
      rw [h]; simp only [f_add_self, zero_add]
    exact this
  · intro hφ
    have hne : u 0 = 1 ∨ u 1 = 1 ∨ u 2 = 1 := by
      by_contra h; push Not at h
      apply hu; funext s; fin_cases s
      · exact (f_cases (u 0)).resolve_right h.1
      · exact (f_cases (u 1)).resolve_right h.2.1
      · exact (f_cases (u 2)).resolve_right h.2.2
    have hsum : φ (Pi.single 0 1) * u 0 + φ (Pi.single 1 1) * u 1 + φ (Pi.single 2 1) * u 2 = 0 := by
      have hu_eq : u = u 0 • Pi.single 0 1 + u 1 • Pi.single 1 1 + u 2 • Pi.single 2 1 := by
        funext s; fin_cases s <;> simp
      rw [hu_eq] at hφ
      simp only [map_add, map_smul, smul_eq_mul] at hφ
      convert hφ using 1; ring
    have hex : ∃ v0 v1 v2 : F,
        u 1 * v2 + u 2 * v1 = φ (Pi.single 0 1) ∧
        u 0 * v2 + u 2 * v0 = φ (Pi.single 1 1) ∧
        u 0 * v1 + u 1 * v0 = φ (Pi.single 2 1) := by
      rcases hne with h0 | h1 | h2
      · refine ⟨0, φ (Pi.single 2 1), φ (Pi.single 1 1), ?_, by simp [h0], by simp [h0]⟩
        rw [h0, mul_one] at hsum
        have := congrArg (· + φ (Pi.single 0 1)) hsum
        have ha : φ (Pi.single 0 1) + φ (Pi.single 1 1) * u 1 + φ (Pi.single 2 1) * u 2 + φ (Pi.single 0 1) =
            (φ (Pi.single 0 1) + φ (Pi.single 0 1)) + (u 1 * φ (Pi.single 1 1) + u 2 * φ (Pi.single 2 1)) := by ring
        rw [ha, f_add_self, zero_add, zero_add] at this
        exact this
      · refine ⟨φ (Pi.single 2 1), 0, φ (Pi.single 0 1), by simp [h1], ?_, by simp [h1]⟩
        rw [h1, mul_one] at hsum
        have := congrArg (· + φ (Pi.single 1 1)) hsum
        have ha : φ (Pi.single 0 1) * u 0 + φ (Pi.single 1 1) + φ (Pi.single 2 1) * u 2 + φ (Pi.single 1 1) =
            (φ (Pi.single 1 1) + φ (Pi.single 1 1)) + (u 0 * φ (Pi.single 0 1) + u 2 * φ (Pi.single 2 1)) := by ring
        rw [ha, f_add_self, zero_add, zero_add] at this
        exact this
      · refine ⟨φ (Pi.single 1 1), φ (Pi.single 0 1), 0, by simp [h2], by simp [h2], ?_⟩
        rw [h2, mul_one] at hsum
        have := congrArg (· + φ (Pi.single 2 1)) hsum
        have ha : φ (Pi.single 0 1) * u 0 + φ (Pi.single 1 1) * u 1 + φ (Pi.single 2 1) + φ (Pi.single 2 1) =
            (φ (Pi.single 2 1) + φ (Pi.single 2 1)) + (u 0 * φ (Pi.single 0 1) + u 1 * φ (Pi.single 1 1)) := by ring
        rw [ha, f_add_self, zero_add, zero_add] at this
        exact this
    obtain ⟨v0, v1, v2, h0, h1, h2⟩ := hex
    refine ⟨![v0, v1, v2], ?_⟩
    apply LinearMap.ext; intro w
    have hw : w = w 0 • Pi.single 0 1 + w 1 • Pi.single 1 1 + w 2 • Pi.single 2 1 := by
      funext s; fin_cases s <;> simp
    conv_rhs => rw [hw]
    simp only [map_add, map_smul, smul_eq_mul]
    change det3 u ![v0, v1, v2] w = _
    rw [← h0, ← h1, ← h2]
    simp only [det3, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons]
    ring

lemma B3_ker_eq_span (u : Fin 3 → F) (hu : u ≠ 0) :
    LinearMap.ker (B3 u) = Submodule.span F {u} := by
  ext v
  simp only [LinearMap.mem_ker, Submodule.mem_span_singleton]
  constructor
  · intro hv
    have h0 : det3 u v (Pi.single 0 1) = 0 := LinearMap.congr_fun hv (Pi.single 0 1)
    have h1 : det3 u v (Pi.single 1 1) = 0 := LinearMap.congr_fun hv (Pi.single 1 1)
    have h2 : det3 u v (Pi.single 2 1) = 0 := LinearMap.congr_fun hv (Pi.single 2 1)
    have hne : u 0 = 1 ∨ u 1 = 1 ∨ u 2 = 1 := by
      by_contra h; push Not at h
      apply hu; funext s; fin_cases s
      · exact (f_cases (u 0)).resolve_right h.1
      · exact (f_cases (u 1)).resolve_right h.2.1
      · exact (f_cases (u 2)).resolve_right h.2.2
    have h0' : u 1 * v 2 + u 2 * v 1 = 0 := by
      have hp0 : (Pi.single 0 (1 : F) : Fin 3 → F) 0 = 1 := by simp
      have hp1 : (Pi.single 0 (1 : F) : Fin 3 → F) 1 = 0 := by simp
      have hp2 : (Pi.single 0 (1 : F) : Fin 3 → F) 2 = 0 := by simp
      simp only [det3, hp0, hp1, hp2, mul_zero, mul_one, zero_add, add_zero] at h0
      exact h0
    have h1' : u 0 * v 2 + u 2 * v 0 = 0 := by
      have hp0 : (Pi.single 1 (1 : F) : Fin 3 → F) 0 = 0 := by simp
      have hp1 : (Pi.single 1 (1 : F) : Fin 3 → F) 1 = 1 := by simp
      have hp2 : (Pi.single 1 (1 : F) : Fin 3 → F) 2 = 0 := by simp
      simp only [det3, hp0, hp1, hp2, mul_zero, mul_one, zero_add, add_zero] at h1
      exact h1
    have h2' : u 0 * v 1 + u 1 * v 0 = 0 := by
      have hp0 : (Pi.single 2 (1 : F) : Fin 3 → F) 0 = 0 := by simp
      have hp1 : (Pi.single 2 (1 : F) : Fin 3 → F) 1 = 0 := by simp
      have hp2 : (Pi.single 2 (1 : F) : Fin 3 → F) 2 = 1 := by simp
      simp only [det3, hp0, hp1, hp2, mul_zero, mul_one, zero_add, add_zero] at h2
      exact h2
    have hex : ∃ r : F, r * u 0 = v 0 ∧ r * u 1 = v 1 ∧ r * u 2 = v 2 := by
      rcases hne with hu0 | hu1 | hu2
      · refine ⟨v 0, by simp [hu0], ?_, ?_⟩
        · rw [hu0, one_mul] at h2'
          have := congrArg (· + v 1) h2'
          have ha : v 1 + u 1 * v 0 + v 1 = (v 1 + v 1) + v 0 * u 1 := by ring
          rw [ha, f_add_self, zero_add, zero_add] at this; exact this
        · rw [hu0, one_mul] at h1'
          have := congrArg (· + v 2) h1'
          have ha : v 2 + u 2 * v 0 + v 2 = (v 2 + v 2) + v 0 * u 2 := by ring
          rw [ha, f_add_self, zero_add, zero_add] at this; exact this
      · refine ⟨v 1, ?_, by simp [hu1], ?_⟩
        · rw [hu1, one_mul] at h2'
          have := congrArg (· + v 0) h2'
          have ha : u 0 * v 1 + v 0 + v 0 = v 1 * u 0 + (v 0 + v 0) := by ring
          rw [ha, f_add_self, add_zero, zero_add] at this; exact this
        · rw [hu1, one_mul] at h0'
          have := congrArg (· + v 2) h0'
          have ha : v 2 + u 2 * v 1 + v 2 = (v 2 + v 2) + v 1 * u 2 := by ring
          rw [ha, f_add_self, zero_add, zero_add] at this; exact this
      · refine ⟨v 2, ?_, ?_, by simp [hu2]⟩
        · rw [hu2, one_mul] at h1'
          have := congrArg (· + v 0) h1'
          have ha : u 0 * v 2 + v 0 + v 0 = v 2 * u 0 + (v 0 + v 0) := by ring
          rw [ha, f_add_self, add_zero, zero_add] at this; exact this
        · rw [hu2, one_mul] at h0'
          have := congrArg (· + v 1) h0'
          have ha : u 1 * v 2 + v 1 + v 1 = v 2 * u 1 + (v 1 + v 1) := by ring
          rw [ha, f_add_self, add_zero, zero_add] at this; exact this
    obtain ⟨r, r0, r1, r2⟩ := hex
    refine ⟨r, ?_⟩; funext s; fin_cases s <;> simpa [Pi.smul_apply, smul_eq_mul]
  · rintro ⟨r, rfl⟩
    apply LinearMap.ext; intro w
    change det3 u (r • u) w = 0
    rw [det3_smul_mid]
    have : det3 u u w = 0 := by
      simp only [det3]
      have h : u 0 * u 1 * w 2 + u 0 * u 2 * w 1 + u 1 * u 0 * w 2 + u 1 * u 2 * w 0 +
          u 2 * u 0 * w 1 + u 2 * u 1 * w 0 =
          (u 0 * u 1 * w 2 + u 0 * u 1 * w 2) + (u 0 * u 2 * w 1 + u 0 * u 2 * w 1) +
          (u 1 * u 2 * w 0 + u 1 * u 2 * w 0) := by ring
      rw [h]; simp only [f_add_self, zero_add]
    rw [this, mul_zero]

lemma B3_finrank_range (u : Fin 3 → F) :
    Module.finrank F (LinearMap.range (B3 u)) = if u = 0 then 0 else 2 := by
  split_ifs with hu
  · subst hu
    have h0 : B3 0 = 0 := by apply LinearMap.ext; intro v; apply LinearMap.ext; intro w; simp [B3, det3]
    rw [h0, LinearMap.range_zero, finrank_bot]
  · have hr := LinearMap.finrank_range_add_finrank_ker (B3 u)
    rw [B3_ker_eq_span u hu, finrank_span_singleton hu, Module.finrank_fin_fun] at hr
    omega

def BE {c : ℕ} (z : E c) : E c →ₗ[F] (E c →ₗ[F] F) where
  toFun x :=
    { toFun := fun y => omegaE z x y
      map_add' := fun y₁ y₂ => by
        simp only [omegaE, Pi.add_apply, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl; intro i _
        exact det3_add_right _ _ _ _
      map_smul' := fun r y => by
        simp only [omegaE, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
        apply Finset.sum_congr rfl; intro i _
        exact det3_smul_right _ _ r _ }
  map_add' x₁ x₂ := by
    apply LinearMap.ext; intro y
    change omegaE z (x₁ + x₂) y = omegaE z x₁ y + omegaE z x₂ y
    simp only [omegaE, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro i _
    exact det3_add_mid _ _ _ _
  map_smul' r x := by
    apply LinearMap.ext; intro y
    change omegaE z (r • x) y = r * omegaE z x y
    simp only [omegaE, Finset.mul_sum]
    apply Finset.sum_congr rfl; intro i _
    exact det3_smul_mid _ r _ _

lemma BE_symm {c : ℕ} (z x y : E c) : BE z x y = BE z y x := by
  change omegaE z x y = omegaE z y x
  simp only [omegaE]
  apply Finset.sum_congr rfl; intro i _
  exact det3_symm23 _ _ _

lemma BE_alt {c : ℕ} (z x : E c) : BE z x x = 0 := by
  change omegaE z x x = 0
  simp only [omegaE]
  apply Finset.sum_eq_zero; intro i _
  exact det3_self23 _ _

def blockVec {c : ℕ} (z : E c) (i : Fin c) : Fin 3 → F := fun s => z (i, s)

def occ {c : ℕ} (z : E c) : Finset (Fin c) :=
  Finset.univ.filter (fun i => blockVec z i ≠ 0)

def blockEmb {c : ℕ} (i : Fin c) : (Fin 3 → F) →ₗ[F] E c where
  toFun v p := if h : p.1 = i then v p.2 else 0
  map_add' v₁ v₂ := by funext p; by_cases h : p.1 = i <;> simp [h]
  map_smul' r v := by funext p; by_cases h : p.1 = i <;> simp [h]

lemma BE_block_eval {c : ℕ} (z x : E c) (i : Fin c) (w : Fin 3 → F) :
    BE z x (blockEmb i w) = B3 (blockVec z i) (blockVec x i) w := by
  change omegaE z x (blockEmb i w) = det3 (blockVec z i) (blockVec x i) w
  simp only [omegaE]
  rw [Finset.sum_eq_single i]
  · simp [blockEmb]; rfl
  · intro j _ hji
    have h0 : (fun s => blockEmb i w (j, s)) = 0 := by funext s; simp [blockEmb, hji]
    rw [h0]; simp [det3]
  · intro hi; exact (hi (Finset.mem_univ i)).elim

lemma BE_range_iff {c : ℕ} (z : E c) (φ : E c →ₗ[F] F) :
    φ ∈ LinearMap.range (BE z) ↔
      ∀ i : Fin c,
        (blockVec z i = 0 → φ.comp (blockEmb i) = 0) ∧
        φ (blockEmb i (blockVec z i)) = 0 := by
  constructor
  · rintro ⟨x, rfl⟩ i
    constructor
    · intro hzi
      apply LinearMap.ext; intro w
      change BE z x (blockEmb i w) = 0
      rw [BE_block_eval, hzi]; simp [B3, det3]
    · change BE z x (blockEmb i (blockVec z i)) = 0
      rw [BE_block_eval]
      change det3 (blockVec z i) (blockVec x i) (blockVec z i) = 0
      rw [det3_symm23]
      simp only [det3]
      have h : blockVec z i 0 * blockVec z i 1 * blockVec x i 2 +
          blockVec z i 0 * blockVec z i 2 * blockVec x i 1 +
          blockVec z i 1 * blockVec z i 0 * blockVec x i 2 +
          blockVec z i 1 * blockVec z i 2 * blockVec x i 0 +
          blockVec z i 2 * blockVec z i 0 * blockVec x i 1 +
          blockVec z i 2 * blockVec z i 1 * blockVec x i 0 =
          (blockVec z i 0 * blockVec z i 1 * blockVec x i 2 + blockVec z i 0 * blockVec z i 1 * blockVec x i 2) +
          (blockVec z i 0 * blockVec z i 2 * blockVec x i 1 + blockVec z i 0 * blockVec z i 2 * blockVec x i 1) +
          (blockVec z i 1 * blockVec z i 2 * blockVec x i 0 + blockVec z i 1 * blockVec z i 2 * blockVec x i 0) := by ring
      rw [h]; simp only [f_add_self, zero_add]
  · intro h
    have hblock : ∀ i : Fin c, ∃ xi : Fin 3 → F, B3 (blockVec z i) xi = φ.comp (blockEmb i) := by
      intro i
      by_cases hzi : blockVec z i = 0
      · refine ⟨0, ?_⟩
        rw [(h i).1 hzi, hzi]
        apply LinearMap.ext; intro w; simp [B3, det3]
      · exact (B3_range_iff (blockVec z i) hzi (φ.comp (blockEmb i))).mpr (h i).2
    choose xblock hxblock using hblock
    refine ⟨fun p => xblock p.1 p.2, ?_⟩
    apply LinearMap.ext; intro y
    have hy : y = ∑ i : Fin c, blockEmb i (blockVec y i) := by
      funext ⟨j, s⟩
      simp only [Finset.sum_apply, blockEmb, blockVec, LinearMap.coe_mk, AddHom.coe_mk]
      rw [Finset.sum_eq_single j]
      · simp
      · intro i _ hij; simp [Ne.symm hij]
      · intro hj; exact (hj (Finset.mem_univ j)).elim
    conv_lhs => rw [hy]
    conv_rhs => rw [hy]
    simp only [map_sum]
    apply Finset.sum_congr rfl; intro i _
    rw [BE_block_eval]
    exact LinearMap.congr_fun (hxblock i) (blockVec y i)

lemma BE_finrank_range {c : ℕ} (z : E c) :
    Module.finrank F (LinearMap.range (BE z)) = 2 * (occ z).card := by
  classical
  let e : LinearMap.range (BE z) ≃ₗ[F] ((i : Fin c) → LinearMap.range (B3 (blockVec z i))) :=
    { toFun := fun ⟨φ, hφ⟩ i => ⟨φ.comp (blockEmb i), by
        rcases hφ with ⟨x, rfl⟩
        exact ⟨blockVec x i, by apply LinearMap.ext; intro w; exact (BE_block_eval z x i w).symm⟩⟩
      map_add' := fun _ _ => by funext i; apply Subtype.ext; apply LinearMap.ext; intro w; simp
      map_smul' := fun _ _ => by funext i; apply Subtype.ext; apply LinearMap.ext; intro w; simp
      invFun := fun f =>
        ⟨{ toFun := fun y => ∑ i : Fin c, (f i).1 (blockVec y i)
           map_add' := fun y₁ y₂ => by
             simp only [← Finset.sum_add_distrib]
             apply Finset.sum_congr rfl; intro i _
             have : blockVec (y₁ + y₂) i = blockVec y₁ i + blockVec y₂ i := by
               funext s; rfl
             rw [this, map_add]
           map_smul' := fun r y => by
             simp only [RingHom.id_apply, smul_eq_mul, Finset.mul_sum]
             apply Finset.sum_congr rfl; intro i _
             have : blockVec (r • y) i = r • blockVec y i := by funext s; rfl
             rw [this, map_smul, smul_eq_mul] }, by
          have hchoose : ∀ i : Fin c, ∃ xi : Fin 3 → F, B3 (blockVec z i) xi = (f i).1 :=
            fun i => (f i).2
          choose xb hxb using hchoose
          refine ⟨fun p => xb p.1 p.2, ?_⟩
          apply LinearMap.ext; intro y
          have hy : y = ∑ i : Fin c, blockEmb i (blockVec y i) := by
            funext ⟨j, s⟩
            simp only [Finset.sum_apply, blockEmb, blockVec, LinearMap.coe_mk, AddHom.coe_mk]
            rw [Finset.sum_eq_single j]
            · simp
            · intro i _ hij; simp [Ne.symm hij]
            · intro hj; exact (hj (Finset.mem_univ j)).elim
          conv_lhs => rw [hy]
          simp only [map_sum, LinearMap.coe_mk, AddHom.coe_mk]
          apply Finset.sum_congr rfl; intro i _
          rw [BE_block_eval]
          exact LinearMap.congr_fun (hxb i) (blockVec y i)⟩
      left_inv := fun ⟨φ, _⟩ => by
        apply Subtype.ext; apply LinearMap.ext; intro y
        have hy : y = ∑ i : Fin c, blockEmb i (blockVec y i) := by
          funext ⟨j, s⟩
          simp only [Finset.sum_apply, blockEmb, blockVec, LinearMap.coe_mk, AddHom.coe_mk]
          rw [Finset.sum_eq_single j]
          · simp
          · intro i _ hij; simp [Ne.symm hij]
          · intro hj; exact (hj (Finset.mem_univ j)).elim
        conv_rhs => rw [hy]
        simp [map_sum]
      right_inv := fun f => by
        funext i; apply Subtype.ext; apply LinearMap.ext; intro w
        simp only [LinearMap.comp_apply, LinearMap.coe_mk, AddHom.coe_mk]
        rw [Finset.sum_eq_single i]
        · have : blockVec (blockEmb i w) i = w := by funext s; simp [blockVec, blockEmb]
          rw [this]
        · intro j _ hji
          have : blockVec (blockEmb i w) j = 0 := by funext s; simp [blockVec, blockEmb, hji]
          rw [this, map_zero]
        · intro hi; exact (hi (Finset.mem_univ i)).elim }
  have hcard : Fintype.card (LinearMap.range (BE z)) =
      Fintype.card ((i : Fin c) → LinearMap.range (B3 (blockVec z i))) :=
    Fintype.card_congr e.toEquiv
  have hL : Fintype.card (LinearMap.range (BE z)) = 2 ^ Module.finrank F (LinearMap.range (BE z)) := by
    simpa [ZMod.card] using Module.card_eq_pow_finrank (K := F) (V := LinearMap.range (BE z))
  have hR : Fintype.card ((i : Fin c) → LinearMap.range (B3 (blockVec z i))) =
      2 ^ (∑ i : Fin c, Module.finrank F (LinearMap.range (B3 (blockVec z i)))) := by
    rw [Fintype.card_pi, ← Finset.prod_pow_eq_pow_sum]
    apply Finset.prod_congr rfl; intro i _
    simpa [ZMod.card] using Module.card_eq_pow_finrank (K := F) (V := LinearMap.range (B3 (blockVec z i)))
  rw [hL, hR] at hcard
  have hfin : Module.finrank F (LinearMap.range (BE z)) =
      ∑ i : Fin c, Module.finrank F (LinearMap.range (B3 (blockVec z i))) :=
    Nat.pow_right_injective (by omega : 1 < 2) hcard
  rw [hfin]
  simp_rw [B3_finrank_range]
  have hsum : (∑ i : Fin c, if blockVec z i = 0 then 0 else 2) =
      ∑ _ ∈ occ z, 2 := by
    rw [occ, Finset.sum_filter]
    apply Finset.sum_congr rfl; intro i _
    by_cases h : blockVec z i = 0 <;> simp [h]
  rw [hsum, Finset.sum_const, smul_eq_mul, mul_comm]

def alphaT (c t : ℕ) : E c →ₗ[F] F where
  toFun z := ∑ i : Fin c, if i.val < t then z (i, 0) else 0
  map_add' z₁ z₂ := by
    simp only [Pi.add_apply, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro i _; split_ifs <;> simp
  map_smul' r z := by
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    apply Finset.sum_congr rfl; intro i _; split_ifs <;> simp

lemma alphaT_ne_zero {c t : ℕ} (ht1 : 1 ≤ t) (htc : t ≤ c) : alphaT c t ≠ 0 := by
  intro h0
  have h1 : alphaT c t (blockEmb ⟨0, by omega⟩ ![1, 0, 0]) = 0 :=
    LinearMap.congr_fun h0 _
  have h2 : alphaT c t (blockEmb ⟨0, by omega⟩ ![1, 0, 0]) = 1 := by
    simp only [alphaT, LinearMap.coe_mk, AddHom.coe_mk]
    rw [Finset.sum_eq_single (⟨0, by omega⟩ : Fin c)]
    · have : (0 : ℕ) < t := by omega
      simp [this, blockEmb]
    · intro i _ hi
      split_ifs with hlt
      · simp [blockEmb, hi]
      · rfl
    · intro h; exact (h (Finset.mem_univ _)).elim
  rw [h2] at h1
  exact absurd h1 (by decide)

lemma alphaT_comp_blockEmb {c t : ℕ} (i : Fin c) (w : Fin 3 → F) :
    alphaT c t (blockEmb i w) = if i.val < t then w 0 else 0 := by
  simp only [alphaT, LinearMap.coe_mk, AddHom.coe_mk]
  rw [Finset.sum_eq_single i]
  · split_ifs <;> simp [blockEmb]
  · intro j _ hji; split_ifs <;> simp [blockEmb, hji]
  · intro hi; exact (hi (Finset.mem_univ i)).elim

lemma alphaT_mem_range_BE_iff {c t : ℕ} (z : E c) :
    alphaT c t ∈ LinearMap.range (BE z) ↔
      ∀ i : Fin c, i.val < t → blockVec z i ≠ 0 ∧ z (i, 0) = 0 := by
  rw [BE_range_iff]
  constructor
  · intro h i hi
    obtain ⟨h1, h2⟩ := h i
    constructor
    · intro hz0
      have := LinearMap.congr_fun (h1 hz0) ![1, 0, 0]
      simp only [LinearMap.comp_apply, LinearMap.zero_apply, alphaT_comp_blockEmb, hi, ite_true,
        Matrix.cons_val_zero] at this
      exact absurd this (by decide)
    · rw [alphaT_comp_blockEmb, if_pos hi] at h2
      exact h2
  · intro h i
    constructor
    · intro hz0
      apply LinearMap.ext; intro w
      simp only [LinearMap.comp_apply, LinearMap.zero_apply, alphaT_comp_blockEmb]
      by_cases hi : i.val < t
      · exact ((h i hi).1 hz0).elim
      · simp [hi]
    · rw [alphaT_comp_blockEmb]
      by_cases hi : i.val < t
      · simp [hi, blockVec, (h i hi).2]
      · simp [hi]

lemma card_fin3_nz : (Finset.univ.filter (fun v : Fin 3 → F => v ≠ 0)).card = 7 := by
  decide

lemma card_fin3_nz_zero0 :
    (Finset.univ.filter (fun v : Fin 3 → F => v ≠ 0 ∧ v 0 = 0)).card = 3 := by
  decide

lemma occ_blockEmb {c : ℕ} (i : Fin c) (v : Fin 3 → F) (hv : v ≠ 0) :
    occ (blockEmb i v) = {i} := by
  ext j
  simp only [occ, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
  constructor
  · intro hj
    by_contra hne
    apply hj; funext s; simp [blockVec, blockEmb, hne]
  · intro hj; subst hj
    have : blockVec (blockEmb j v) j = v := by funext s; simp [blockVec, blockEmb]
    rw [this]; exact hv

lemma blockVec_blockEmb_self {c : ℕ} (i : Fin c) (v : Fin 3 → F) :
    blockVec (blockEmb i v) i = v := by
  funext s; simp [blockVec, blockEmb]

lemma card_fin_lt (c t : ℕ) (htc : t ≤ c) :
    (Finset.univ.filter (fun i : Fin c => i.val < t)).card = t := by
  have : Finset.univ.filter (fun i : Fin c => i.val < t) =
      (Finset.range t).attach.map ⟨fun k => ⟨k.1, by have := Finset.mem_range.mp k.2; omega⟩,
        fun a b hab => Subtype.ext (congrArg Fin.val hab)⟩ := by
    ext i; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map,
      Finset.mem_attach, Subtype.exists, Finset.mem_range]
    constructor
    · intro hi; exact ⟨i.val, hi, Fin.ext rfl⟩
    · rintro ⟨k, hk, rfl⟩; exact hk
  rw [this, Finset.card_map, Finset.card_attach, Finset.card_range]

lemma card_fin_ge (c t : ℕ) (htc : t ≤ c) :
    (Finset.univ.filter (fun i : Fin c => t ≤ i.val)).card = c - t := by
  have hunion : (Finset.univ.filter (fun i : Fin c => i.val < t)) ∪
      (Finset.univ.filter (fun i : Fin c => t ≤ i.val)) = Finset.univ := by
    ext i; simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
    omega
  have hdisj : Disjoint (Finset.univ.filter (fun i : Fin c => i.val < t))
      (Finset.univ.filter (fun i : Fin c => t ≤ i.val)) := by
    rw [Finset.disjoint_left]
    intro i h1 h2
    have a1 := (Finset.mem_filter.mp h1).2
    have a2 := (Finset.mem_filter.mp h2).2
    omega
  have hcard := congrArg Finset.card hunion
  rw [Finset.card_union_of_disjoint hdisj, card_fin_lt c t htc, Finset.card_univ, Fintype.card_fin] at hcard
  omega

lemma model_analysis {n c t : ℕ} {g : V n → F} {R : Submodule F (V n)}
    (hg : cubic g) (hR : ∀ u : V n, u ∈ R ↔ ∀ v w : V n, third g u v w = 0)
    (hdc : (n - Module.finrank F R) + 1 = 3 * c)
    (ht2 : 2 ≤ t) (htc : t ≤ c)
    (L : V n →ₗ[F] E c) (q : V n → F) (hq : quad q)
    (hL_range : ∀ z : E c, (∃ x : V n, L x = z) ↔ alphaT c t z = 0)
    (hg_eq : ∀ x : V n, g x = q x + ∑ i : Fin c, L x (i, 0) * L x (i, 1) * L x (i, 2)) :
    let S := R ⊔ Submodule.span F {u : V n | rankAt g u = 2}
    let p := (n - Module.finrank F S) + 1
    t = p ∧
    ((Finset.univ : Finset (V n)).filter (fun u => rankAt g u = 2)).card =
      2 ^ (Module.finrank F R) * (7 * (c - t) + 3 * t + (if t = 2 then 9 else 0)) := by
  classical
  intro S p
  have hthird : ∀ a b d : V n, third g a b d = omegaE (L a) (L b) (L d) := by
    intro a b d
    have hg_fun : g = fun x => q x + ∑ i : Fin c, L x (i, 0) * L x (i, 1) * L x (i, 2) := funext hg_eq
    rw [hg_fun, third_add_fun, third_quad hq, zero_add, third_sum]
    simp only [omegaE]
    apply Finset.sum_congr rfl; intro i _
    let l₀ : V n →ₗ[F] F := (LinearMap.proj (i, (0 : Fin 3))).comp L
    let l₁ : V n →ₗ[F] F := (LinearMap.proj (i, (1 : Fin 3))).comp L
    let l₂ : V n →ₗ[F] F := (LinearMap.proj (i, (2 : Fin 3))).comp L
    exact third_triple l₀ l₁ l₂ a b d
  let H := LinearMap.ker (alphaT c t)
  let L_H : V n →ₗ[F] H := L.codRestrict H (fun x => (hL_range (L x)).mp ⟨x, rfl⟩)
  have hL_H_surj : Function.Surjective L_H := by
    rintro ⟨z, hz⟩
    obtain ⟨x, hx⟩ := (hL_range z).mpr hz
    exact ⟨x, Subtype.ext hx⟩
  have hrank : ∀ u : V n,
      rankAt g u = if (∀ i : Fin c, i.val < t → blockVec (L u) i ≠ 0 ∧ L u (i, 0) = 0)
        then 2 * (occ (L u)).card - 2
        else 2 * (occ (L u)).card := by
    intro u
    rw [rankAt_eq_finrank_range hg u]
    let BH : H →ₗ[F] (H →ₗ[F] F) := (H.subtype.dualMap.comp (BE (L u))).comp H.subtype
    have hpb : bilinMap hg u = (L_H.dualMap.comp BH).comp L_H := by
      apply LinearMap.ext; intro v; apply LinearMap.ext; intro w
      exact hthird u v w
    rw [hpb, finrank_range_pullback L_H hL_H_surj BH]
    have hres := rank_restrict_hyperplane (BE (L u)) (BE_symm (L u)) (BE_alt (L u))
      (alphaT c t) (alphaT_ne_zero (by omega) htc)
    dsimp only at hres
    rw [BE_finrank_range (L u), alphaT_mem_range_BE_iff (L u)] at hres
    split_ifs with hcond
    · have h1 : Module.finrank F (LinearMap.range BH) + 2 = 2 * (occ (L u)).card := hres.1 hcond
      omega
    · exact hres.2 hcond
  have hkerL : LinearMap.ker L = R := by
    ext u
    rw [LinearMap.mem_ker, hR]
    constructor
    · intro hLu v w
      rw [hthird, hLu]
      simp [omegaE, det3]
    · intro hzero
      have hr0 : rankAt g u = 0 := by
        rw [rankAt_eq_finrank_range hg u]
        have hb0 : bilinMap hg u = 0 := by
          apply LinearMap.ext; intro v; apply LinearMap.ext; intro w; exact hzero v w
        rw [hb0, LinearMap.range_zero, finrank_bot]
      rw [hrank u] at hr0
      by_cases hcond : ∀ i : Fin c, i.val < t → blockVec (L u) i ≠ 0 ∧ L u (i, 0) = 0
      · rw [if_pos hcond] at hr0
        have hsub : Finset.univ.filter (fun i : Fin c => i.val < t) ⊆ occ (L u) := by
          intro i hi
          rw [Finset.mem_filter] at hi
          rw [occ, Finset.mem_filter]
          exact ⟨Finset.mem_univ i, (hcond i hi.2).1⟩
        have hocc_ge : t ≤ (occ (L u)).card := card_fin_lt c t htc ▸ Finset.card_le_card hsub
        omega
      · rw [if_neg hcond] at hr0
        have hocc0 : occ (L u) = ∅ := Finset.card_eq_zero.mp (by omega)
        funext ⟨i, s⟩
        have hni : i ∉ occ (L u) := by rw [hocc0]; simp
        rw [occ, Finset.mem_filter] at hni
        push Not at hni
        exact congrFun (hni (Finset.mem_univ i)) s
  have hrank2_iff : ∀ u : V n, rankAt g u = 2 ↔
      (occ (L u)).card = 1 ∨
      (t = 2 ∧ (occ (L u)).card = 2 ∧
        ∀ i : Fin c, i.val < t → blockVec (L u) i ≠ 0 ∧ L u (i, 0) = 0) := by
    intro u
    rw [hrank u]
    by_cases hcond : ∀ i : Fin c, i.val < t → blockVec (L u) i ≠ 0 ∧ L u (i, 0) = 0
    · have hsub : Finset.univ.filter (fun i : Fin c => i.val < t) ⊆ occ (L u) := by
        intro i hi
        rw [Finset.mem_filter] at hi
        rw [occ, Finset.mem_filter]
        exact ⟨Finset.mem_univ i, (hcond i hi.2).1⟩
      have hocc_ge : t ≤ (occ (L u)).card := card_fin_lt c t htc ▸ Finset.card_le_card hsub
      rw [if_pos hcond]
      constructor
      · intro h2; right; exact ⟨by omega, by omega, hcond⟩
      · rintro (h1 | ⟨_, h2, _⟩) <;> omega
    · rw [if_neg hcond]
      constructor
      · intro h2; left; omega
      · rintro (h1 | ⟨_, _, hc⟩)
        · omega
        · exact (hcond hc).elim
  let W_t : Submodule F (E c) :=
    { carrier := {z : E c | ∀ i : Fin c, i.val < t → z (i, 0) = 0}, add_mem' := fun {z₁ z₂} h₁ h₂ i hi => by simp [h₁ i hi, h₂ i hi]
      zero_mem' := fun i _ => rfl
      smul_mem' := fun r {z} hz i hi => by simp [hz i hi] }
  have hmapS : Submodule.map L S = W_t := by
    apply le_antisymm
    · rw [Submodule.map_le_iff_le_comap]
      apply sup_le
      · rw [← hkerL]; intro u hu
        simp only [Submodule.mem_comap, LinearMap.mem_ker.mp hu]
        exact W_t.zero_mem
      · rw [Submodule.span_le]
        intro u hu
        change rankAt g u = 2 at hu
        rw [hrank2_iff] at hu
        show L u ∈ W_t
        rcases hu with h1 | ⟨_, _, hcond⟩
        · intro i hi
          by_cases hmem : i ∈ occ (L u)
          · have hocc_eq : occ (L u) = {i} := by
              obtain ⟨j, hj⟩ := Finset.card_eq_one.mp h1
              rw [hj] at hmem ⊢
              have : i = j := Finset.mem_singleton.mp hmem
              subst this; rfl
            have halpha : alphaT c t (L u) = 0 := (hL_range (L u)).mp ⟨u, rfl⟩
            simp only [alphaT, LinearMap.coe_mk, AddHom.coe_mk] at halpha
            rw [Finset.sum_eq_single i] at halpha
            · simpa [hi] using halpha
            · intro j _ hji
              have hnj : j ∉ occ (L u) := by rw [hocc_eq]; simp [hji]
              rw [occ, Finset.mem_filter] at hnj; push Not at hnj
              have hj0 : L u (j, 0) = 0 := congrFun (hnj (Finset.mem_univ j)) 0
              simp [hj0]
            · intro h; exact (h (Finset.mem_univ i)).elim
          · rw [occ, Finset.mem_filter] at hmem; push Not at hmem
            exact congrFun (hmem (Finset.mem_univ i)) 0
        · intro i hi; exact (hcond i hi).2
    · intro z hz
      have hz_sum : z = ∑ q : Fin c × Fin 3, z q • Pi.single q (1 : F) := by
        funext r
        simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply]
        rw [Finset.sum_eq_single r]
        · simp
        · intro q _ hqr; simp [hqr.symm]
        · intro hr; exact (hr (Finset.mem_univ r)).elim
      rw [hz_sum]
      apply Submodule.sum_mem
      intro ⟨i, s⟩ _
      by_cases hzero : z (i, s) = 0
      · rw [hzero, zero_smul]; exact Submodule.zero_mem _
      · apply Submodule.smul_mem
        have hnotbad : ¬ (i.val < t ∧ s = 0) := by
          rintro ⟨hi, rfl⟩; exact hzero (hz i hi)
        have halpha : alphaT c t (Pi.single (i, s) (1 : F)) = 0 := by
          simp only [alphaT, LinearMap.coe_mk, AddHom.coe_mk]
          apply Finset.sum_eq_zero; intro j _
          split_ifs with hjt
          · simp only [Pi.single_apply]
            split_ifs with heq
            · exfalso
              have h1 : j = i := congrArg Prod.fst heq
              have h2 : (0 : Fin 3) = s := congrArg Prod.snd heq
              exact hnotbad ⟨h1 ▸ hjt, h2.symm⟩
            · rfl
          · rfl
        obtain ⟨u, hu⟩ := (hL_range (Pi.single (i, s) (1 : F))).mpr halpha
        refine ⟨u, Submodule.mem_sup_right (Submodule.subset_span ?_), hu⟩
        change rankAt g u = 2
        rw [hrank2_iff]
        left
        have hocc : occ (L u) = {i} := by
          rw [hu]; ext j
          simp only [occ, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
          constructor
          · intro hj
            by_contra hne
            apply hj; funext s'; simp [blockVec, Pi.single_apply, hne]
          · rintro rfl
            intro h0
            have := congrFun h0 s
            simp [blockVec, Pi.single_apply] at this
        rw [hocc, Finset.card_singleton]
  have hfinrank_Wt : Module.finrank F W_t = 3 * c - t := by
    let idx := {q : Fin c × Fin 3 // ¬ (q.1.val < t ∧ q.2 = 0)}
    let e : W_t ≃ₗ[F] (idx → F) :=
      { toFun := fun ⟨z, _⟩ q => z q.1
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl
        invFun := fun f =>
          ⟨fun q => if h : ¬ (q.1.val < t ∧ q.2 = 0) then f ⟨q, h⟩ else 0, by
            intro i hi; simp [hi]⟩
        left_inv := fun ⟨z, hz⟩ => by
          ext ⟨i, s⟩
          by_cases h : ¬ (i.val < t ∧ s = 0)
          · simp [h]
          · push Not at h
            rcases h with ⟨hi, rfl⟩
            simp [hi, hz i hi]
        right_inv := fun f => by
          ext ⟨q, hq⟩; simp [hq] }
    rw [e.finrank_eq, Module.finrank_fintype_fun_eq_card]
    have hcard_idx : Fintype.card idx = 3 * c - t := by
      have htot : Fintype.card (Fin c × Fin 3) = 3 * c := by
        rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_fin]; ring
      have hbad : (Finset.univ.filter (fun q : Fin c × Fin 3 => q.1.val < t ∧ q.2 = 0)).card = t := by
        have : Finset.univ.filter (fun q : Fin c × Fin 3 => q.1.val < t ∧ q.2 = 0) =
            (Finset.range t).attach.map
              ⟨fun k => (⟨k.1, by have := Finset.mem_range.mp k.2; omega⟩, 0),
               fun a b hab => Subtype.ext (congrArg (fun x : Fin c × Fin 3 => x.1.val) hab)⟩ := by
          ext ⟨i, s⟩
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map,
            Finset.mem_attach, Subtype.exists, Finset.mem_range]
          constructor
          · rintro ⟨hi, rfl⟩; exact ⟨i.val, hi, Prod.ext (Fin.ext rfl) rfl⟩
          · rintro ⟨k, hk, heq⟩
            have h1 : (⟨k, _⟩ : Fin c) = i := congrArg Prod.fst heq
            have h2 : (0 : Fin 3) = s := congrArg Prod.snd heq
            exact ⟨by rw [← h1]; exact hk, h2.symm⟩
        rw [this, Finset.card_map, Finset.card_attach, Finset.card_range]
      rw [Fintype.card_subtype_compl]
      have hsub : Fintype.card {q : Fin c × Fin 3 // q.1.val < t ∧ q.2 = 0} = t := by
        rw [Fintype.card_subtype]; exact hbad
      omega
    exact hcard_idx
  have hfinrank_S : Module.finrank F S = Module.finrank F R + (3 * c - t) := by
    have hr := LinearMap.finrank_range_add_finrank_ker (L.domRestrict S)
    have h1 : LinearMap.range (L.domRestrict S) = Submodule.map L S := LinearMap.range_domRestrict S L
    have h2 : Module.finrank F (LinearMap.ker (L.domRestrict S)) = Module.finrank F R := by
      have hRS : R ≤ S := le_sup_left
      let e : LinearMap.ker (L.domRestrict S) ≃ₗ[F] R :=
        { toFun := fun ⟨⟨u, _⟩, hu⟩ => ⟨u, hkerL ▸ hu⟩
          map_add' := fun _ _ => rfl
          map_smul' := fun _ _ => rfl
          invFun := fun ⟨u, hu⟩ => ⟨⟨u, hRS hu⟩, by
            have hu' : u ∈ LinearMap.ker L := hkerL.symm ▸ hu
            exact LinearMap.mem_ker.mpr (LinearMap.mem_ker.mp hu')⟩
          left_inv := fun _ => rfl
          right_inv := fun _ => rfl }
      exact e.finrank_eq
    rw [h1, hmapS, hfinrank_Wt, h2] at hr
    omega
  have hR_le : Module.finrank F R ≤ n := by
    have := Submodule.finrank_le R
    simpa [Module.finrank_fin_fun] using this
  have htp : t = p := by
    change t = (n - Module.finrank F S) + 1
    omega
  refine ⟨htp, ?_⟩
  let T : Finset (E c) := Finset.univ.filter (fun z => alphaT c t z = 0 ∧
    ((occ z).card = 1 ∨
      (t = 2 ∧ (occ z).card = 2 ∧ ∀ i : Fin c, i.val < t → blockVec z i ≠ 0 ∧ z (i, 0) = 0)))
  have hfib : ((Finset.univ : Finset (V n)).filter (fun u => rankAt g u = 2)).card =
      2 ^ (Module.finrank F R) * T.card := by
    have hfilt : (Finset.univ : Finset (V n)).filter (fun u => rankAt g u = 2) =
        Finset.univ.filter (fun u => L u ∈ T) := by
      ext u
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, T]
      rw [hrank2_iff]
      have hLu : alphaT c t (L u) = 0 := (hL_range (L u)).mp ⟨u, rfl⟩
      simp [hLu]
    rw [hfilt, Finset.card_eq_sum_ones, ← Finset.sum_fiberwise_of_maps_to (g := L) (t := T)
      (fun u hu => (Finset.mem_filter.mp hu).2)]
    have hcard_R : Fintype.card R = 2 ^ (Module.finrank F R) := by
      have := Module.card_eq_pow_finrank (K := F) (V := R)
      simpa [ZMod.card] using this
    have hfiber : ∀ z ∈ T, (∑ _ ∈ (Finset.univ.filter (fun u => L u ∈ T)).filter (fun u => L u = z), 1) =
        2 ^ (Module.finrank F R) := by
      intro z hz
      rw [Finset.sum_const, smul_eq_mul, mul_one]
      obtain ⟨u₀, hu₀⟩ := (hL_range z).mpr (Finset.mem_filter.mp hz).2.1
      have hbij : (Finset.univ.filter (fun u => L u ∈ T)).filter (fun u => L u = z) =
          Finset.univ.map ⟨fun r : R => u₀ + r.1, fun a b hab => Subtype.ext (add_left_cancel hab)⟩ := by
        ext u
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map,
          Function.Embedding.coeFn_mk]
        constructor
        · rintro ⟨_, hLu⟩
          have hmem : u + u₀ ∈ R := by
            rw [← hkerL, LinearMap.mem_ker, map_add, hLu, hu₀]
            funext q; exact f_add_self _
          refine ⟨⟨u + u₀, hmem⟩, ?_⟩
          change u₀ + (u + u₀) = u
          rw [add_comm u u₀, ← add_assoc, vec_add_self, zero_add]
        · rintro ⟨⟨r, hr⟩, rfl⟩
          have hLr : L r = 0 := LinearMap.mem_ker.mp (hkerL.symm ▸ hr)
          have hLu : L (u₀ + r) = z := by rw [map_add, hu₀, hLr, add_zero]
          exact ⟨hLu ▸ hz, hLu⟩
      rw [hbij, Finset.card_map, Finset.card_univ, hcard_R]
    rw [Finset.sum_congr rfl hfiber, Finset.sum_const, smul_eq_mul, mul_comm]
  rw [hfib]
  congr 1
  let T1u : Finset (E c) := Finset.univ.filter (fun z => ∃ i : Fin c, t ≤ i.val ∧ occ z = {i})
  let T1m : Finset (E c) := Finset.univ.filter (fun z => ∃ i : Fin c, i.val < t ∧ occ z = {i} ∧ z (i, 0) = 0)
  let T2 : Finset (E c) := Finset.univ.filter (fun z =>
    t = 2 ∧ (occ z).card = 2 ∧ ∀ i : Fin c, i.val < t → blockVec z i ≠ 0 ∧ z (i, 0) = 0)
  have hT_eq : T = (T1u ∪ T1m) ∪ T2 := by
    ext z
    simp only [T, T1u, T1m, T2, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨hα, h1 | h2⟩
      · obtain ⟨i, hi⟩ := Finset.card_eq_one.mp h1
        by_cases hlt : i.val < t
        · left; right
          refine ⟨i, hlt, hi, ?_⟩
          simp only [alphaT, LinearMap.coe_mk, AddHom.coe_mk] at hα
          rw [Finset.sum_eq_single i] at hα
          · simpa [hlt] using hα
          · intro j _ hji
            have hnj : j ∉ occ z := by rw [hi]; simp [hji]
            rw [occ, Finset.mem_filter] at hnj; push Not at hnj
            have hj0 : z (j, 0) = 0 := congrFun (hnj (Finset.mem_univ j)) 0
            simp [hj0]
          · intro h; exact (h (Finset.mem_univ i)).elim
        · left; left; exact ⟨i, by omega, hi⟩
      · right; exact h2
    · rintro ((⟨i, hge, hi⟩ | ⟨i, hlt, hi, hz0⟩) | ⟨ht2', hc2, hcond⟩)
      · refine ⟨?_, Or.inl (by rw [hi, Finset.card_singleton])⟩
        simp only [alphaT, LinearMap.coe_mk, AddHom.coe_mk]
        apply Finset.sum_eq_zero; intro j _
        split_ifs with hj
        · have hji : j ≠ i := by intro he; rw [he] at hj; omega
          have hnj : j ∉ occ z := by rw [hi]; simp [hji]
          rw [occ, Finset.mem_filter] at hnj; push Not at hnj
          exact congrFun (hnj (Finset.mem_univ j)) 0
        · rfl
      · refine ⟨?_, Or.inl (by rw [hi, Finset.card_singleton])⟩
        simp only [alphaT, LinearMap.coe_mk, AddHom.coe_mk]
        rw [Finset.sum_eq_single i]
        · simp [hlt, hz0]
        · intro j _ hji
          have hnj : j ∉ occ z := by rw [hi]; simp [hji]
          rw [occ, Finset.mem_filter] at hnj; push Not at hnj
          have hj0 : z (j, 0) = 0 := congrFun (hnj (Finset.mem_univ j)) 0
          simp [hj0]
        · intro h; exact (h (Finset.mem_univ i)).elim
      · refine ⟨?_, Or.inr ⟨ht2', hc2, hcond⟩⟩
        simp only [alphaT, LinearMap.coe_mk, AddHom.coe_mk]
        apply Finset.sum_eq_zero; intro j _
        split_ifs with hj
        · exact (hcond j hj).2
        · rfl
  have hdisj1 : Disjoint T1u T1m := by
    rw [Finset.disjoint_left]
    intro z h1 h2
    rcases (Finset.mem_filter.mp h1).2 with ⟨i, hge, hi⟩
    rcases (Finset.mem_filter.mp h2).2 with ⟨j, hlt, hj, _⟩
    have : i = j := Finset.singleton_injective (hi.symm.trans hj)
    omega
  have hdisj2 : Disjoint (T1u ∪ T1m) T2 := by
    rw [Finset.disjoint_left]
    intro z h1 h2
    have hc2 := (Finset.mem_filter.mp h2).2.2.1
    rcases Finset.mem_union.mp h1 with hu | hm
    · rcases (Finset.mem_filter.mp hu).2 with ⟨i, _, hi⟩
      rw [hi, Finset.card_singleton] at hc2; omega
    · rcases (Finset.mem_filter.mp hm).2 with ⟨i, _, hi, _⟩
      rw [hi, Finset.card_singleton] at hc2; omega
  rw [hT_eq, Finset.card_union_of_disjoint hdisj2, Finset.card_union_of_disjoint hdisj1]
  have hcard_T1u : T1u.card = 7 * (c - t) := by
    let S_idx := Finset.univ.filter (fun i : Fin c => t ≤ i.val)
    let S_vec := Finset.univ.filter (fun v : Fin 3 → F => v ≠ 0)
    have hbij : (S_idx ×ˢ S_vec).card = T1u.card := by
      apply Finset.card_bij (fun p _ => blockEmb p.1 p.2)
      · rintro ⟨i, v⟩ hp
        rcases Finset.mem_product.mp hp with ⟨hi, hv⟩
        rw [Finset.mem_filter] at hi hv
        rw [Finset.mem_filter]
        exact ⟨Finset.mem_univ _, i, hi.2, occ_blockEmb i v hv.2⟩
      · rintro ⟨i₁, v₁⟩ hp₁ ⟨i₂, v₂⟩ hp₂ heq
        have hv₁ : v₁ ≠ 0 := (Finset.mem_filter.mp (Finset.mem_product.mp hp₁).2).2
        have hv₂ : v₂ ≠ 0 := (Finset.mem_filter.mp (Finset.mem_product.mp hp₂).2).2
        have hi : i₁ = i₂ := Finset.singleton_injective
          ((occ_blockEmb i₁ v₁ hv₁).symm.trans (by rw [heq]; exact occ_blockEmb i₂ v₂ hv₂))
        subst hi
        have hv : v₁ = v₂ := by
          rw [← blockVec_blockEmb_self i₁ v₁, heq, blockVec_blockEmb_self]
        rw [hv]
      · intro z hz
        rcases (Finset.mem_filter.mp hz).2 with ⟨i, hge, hi⟩
        have hnz : blockVec z i ≠ 0 := by
          have : i ∈ occ z := by rw [hi]; simp
          exact (Finset.mem_filter.mp this).2
        refine ⟨(i, blockVec z i), Finset.mem_product.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hge⟩,
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, hnz⟩⟩, ?_⟩
        funext ⟨j, s⟩
        by_cases hji : j = i
        · subst hji; simp [blockEmb, blockVec]
        · simp only [blockEmb, LinearMap.coe_mk, AddHom.coe_mk, hji, dite_false]
          have hnj : j ∉ occ z := by rw [hi]; simp [hji]
          rw [occ, Finset.mem_filter] at hnj; push Not at hnj
          exact (congrFun (hnj (Finset.mem_univ j)) s).symm
    rw [← hbij, Finset.card_product, card_fin_ge c t htc, card_fin3_nz, mul_comm]
  have hcard_T1m : T1m.card = 3 * t := by
    let S_idx := Finset.univ.filter (fun i : Fin c => i.val < t)
    let S_vec := Finset.univ.filter (fun v : Fin 3 → F => v ≠ 0 ∧ v 0 = 0)
    have hbij : (S_idx ×ˢ S_vec).card = T1m.card := by
      apply Finset.card_bij (fun p _ => blockEmb p.1 p.2)
      · rintro ⟨i, v⟩ hp
        rcases Finset.mem_product.mp hp with ⟨hi, hv⟩
        rw [Finset.mem_filter] at hi hv
        rw [Finset.mem_filter]
        exact ⟨Finset.mem_univ _, i, hi.2, occ_blockEmb i v hv.2.1, by simp [blockEmb]; exact hv.2.2⟩
      · rintro ⟨i₁, v₁⟩ hp₁ ⟨i₂, v₂⟩ hp₂ heq
        have hv₁ : v₁ ≠ 0 := (Finset.mem_filter.mp (Finset.mem_product.mp hp₁).2).2.1
        have hv₂ : v₂ ≠ 0 := (Finset.mem_filter.mp (Finset.mem_product.mp hp₂).2).2.1
        have hi : i₁ = i₂ := Finset.singleton_injective
          ((occ_blockEmb i₁ v₁ hv₁).symm.trans (by rw [heq]; exact occ_blockEmb i₂ v₂ hv₂))
        subst hi
        have hv : v₁ = v₂ := by
          rw [← blockVec_blockEmb_self i₁ v₁, heq, blockVec_blockEmb_self]
        rw [hv]
      · intro z hz
        rcases (Finset.mem_filter.mp hz).2 with ⟨i, hlt, hi, hz0⟩
        have hnz : blockVec z i ≠ 0 := by
          have : i ∈ occ z := by rw [hi]; simp
          exact (Finset.mem_filter.mp this).2
        refine ⟨(i, blockVec z i), Finset.mem_product.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hlt⟩,
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, hnz, hz0⟩⟩, ?_⟩
        funext ⟨j, s⟩
        by_cases hji : j = i
        · subst hji; simp [blockEmb, blockVec]
        · simp only [blockEmb, LinearMap.coe_mk, AddHom.coe_mk, hji, dite_false]
          have hnj : j ∉ occ z := by rw [hi]; simp [hji]
          rw [occ, Finset.mem_filter] at hnj; push Not at hnj
          exact (congrFun (hnj (Finset.mem_univ j)) s).symm
    rw [← hbij, Finset.card_product, card_fin_lt c t htc, card_fin3_nz_zero0, mul_comm]
  have hcard_T2 : T2.card = if t = 2 then 9 else 0 := by
    split_ifs with ht_eq
    · let S_vec := Finset.univ.filter (fun v : Fin 3 → F => v ≠ 0 ∧ v 0 = 0)
      have hc2_ge : 2 ≤ c := by omega
      let i0 : Fin c := ⟨0, Nat.lt_of_lt_of_le (by decide) hc2_ge⟩
      let i1 : Fin c := ⟨1, Nat.lt_of_lt_of_le (by decide) hc2_ge⟩
      have hi01 : i0 ≠ i1 := by intro h; have := congrArg Fin.val h; simp [i0, i1] at this
      have hbij : (S_vec ×ˢ S_vec).card = T2.card := by
        apply Finset.card_bij (fun p _ => blockEmb i0 p.1 + blockEmb i1 p.2)
        · rintro ⟨v₀, v₁⟩ hp
          rcases Finset.mem_product.mp hp with ⟨h0, h1⟩
          rw [Finset.mem_filter] at h0 h1
          rw [Finset.mem_filter]
          have hocc : occ (blockEmb i0 v₀ + blockEmb i1 v₁) = {i0, i1} := by
            ext j
            simp only [occ, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
              Finset.mem_singleton]
            constructor
            · intro hj
              by_contra hne; push Not at hne
              apply hj; funext s; simp [blockVec, blockEmb, hne.1, hne.2]
            · rintro (rfl | rfl)
              · have : blockVec (blockEmb i0 v₀ + blockEmb i1 v₁) i0 = v₀ := by
                  funext s; simp [blockVec, blockEmb, hi01]
                rw [this]; exact h0.2.1
              · have : blockVec (blockEmb i0 v₀ + blockEmb i1 v₁) i1 = v₁ := by
                  funext s; simp [blockVec, blockEmb, hi01.symm]
                rw [this]; exact h1.2.1
          refine ⟨Finset.mem_univ _, ht_eq, by rw [hocc, Finset.card_pair hi01], ?_⟩
          intro j hj
          have hcases : j = i0 ∨ j = i1 := by
            have : j.val = 0 ∨ j.val = 1 := by omega
            rcases this with h | h
            · left; exact Fin.ext h
            · right; exact Fin.ext h
          rcases hcases with rfl | rfl
          · have hb : blockVec (blockEmb i0 v₀ + blockEmb i1 v₁) i0 = v₀ := by
              funext s; simp [blockVec, blockEmb, hi01]
            exact ⟨by rw [hb]; exact h0.2.1, by simp [blockEmb, hi01]; exact h0.2.2⟩
          · have hb : blockVec (blockEmb i0 v₀ + blockEmb i1 v₁) i1 = v₁ := by
              funext s; simp [blockVec, blockEmb, hi01.symm]
            exact ⟨by rw [hb]; exact h1.2.1, by simp [blockEmb, hi01.symm]; exact h1.2.2⟩
        · rintro ⟨a₀, a₁⟩ _ ⟨b₀, b₁⟩ _ heq
          have ha0 : a₀ = b₀ := by
            funext s
            have := congrFun heq (i0, s)
            simpa [blockEmb, hi01] using this
          have ha1 : a₁ = b₁ := by
            funext s
            have := congrFun heq (i1, s)
            simpa [blockEmb, hi01.symm] using this
          rw [ha0, ha1]
        · intro z hz
          rcases (Finset.mem_filter.mp hz).2 with ⟨_, hc2, hcond⟩
          have h0 := hcond i0 (by simp [i0, ht_eq])
          have h1 := hcond i1 (by simp [i1, ht_eq])
          have hsub : ({i0, i1} : Finset (Fin c)) ⊆ occ z := by
            intro j hj
            rcases Finset.mem_insert.mp hj with rfl | hj
            · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, h0.1⟩
            · rw [Finset.mem_singleton.mp hj]; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, h1.1⟩
          have hocc : occ z = {i0, i1} :=
            (Finset.eq_of_subset_of_card_le hsub (by rw [Finset.card_pair hi01, hc2])).symm
          refine ⟨(blockVec z i0, blockVec z i1), Finset.mem_product.mpr
            ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, h0⟩,
             Finset.mem_filter.mpr ⟨Finset.mem_univ _, h1⟩⟩, ?_⟩
          funext ⟨j, s⟩
          by_cases hj0 : j = i0
          · subst hj0; simp [blockEmb, blockVec, hi01]
          · by_cases hj1 : j = i1
            · subst hj1; simp [blockEmb, blockVec, hi01.symm]
            · simp only [Pi.add_apply, blockEmb, LinearMap.coe_mk, AddHom.coe_mk, hj0, hj1,
                dite_false, add_zero]
              have hnj : j ∉ occ z := by rw [hocc]; simp [hj0, hj1]
              rw [occ, Finset.mem_filter] at hnj; push Not at hnj
              exact (congrFun (hnj (Finset.mem_univ j)) s).symm
      rw [← hbij, Finset.card_product, card_fin3_nz_zero0]
    · have hempty : T2 = ∅ := by
        rw [Finset.eq_empty_iff_forall_notMem]
        intro z hz; exact ht_eq (Finset.mem_filter.mp hz).2.1
      rw [hempty, Finset.card_empty]
  rw [hcard_T1u, hcard_T1m, hcard_T2]

open PEqualNP.CircuitLowerBounds

def b2f (b : Bool) : F := if b then 1 else 0

lemma b2f_decide (a : F) : b2f (decide (a = 1)) = a := by
  rcases f_cases a with rfl | rfl <;> decide

lemma decide_b2f (b : Bool) : decide (b2f b = 1) = b := by
  cases b <;> decide

lemma b2f_and (a b : Bool) : b2f (a && b) = b2f a * b2f b := by
  cases a <;> cases b <;> decide

lemma b2f_not (a : Bool) : b2f (!a) = b2f a + 1 := by
  cases a <;> decide

lemma b2f_mod2_pair (a b : Bool) :
    b2f (GateOp.eval (.mod 2) [a, b]) = b2f a + b2f b + 1 := by
  cases a <;> cases b <;> decide

lemma b2f_or_pair (a b : Bool) :
    b2f (GateOp.eval .or [a, b]) = b2f a + b2f b + b2f a * b2f b := by
  cases a <;> cases b <;> decide

def bits (n : ℕ) (u : V n) : List Bool :=
  List.ofFn (fun j : Fin n => decide (u j = 1))

lemma bits_length (n : ℕ) (u : V n) : (bits n u).length = n := by
  simp [bits]

def legalGate (h : Gate) : Prop :=
  h.inputs.length ≤ 2 ∧
    (h.op = .and ∨ h.op = .or ∨ h.op = .mod 2 ∨ (h.op = .not ∧ h.inputs.length = 1))

noncomputable def isMulGate (h : Gate) : Bool :=
  @decide ((h.op = .and ∨ h.op = .or) ∧ h.inputs.length = 2) (Classical.propDecidable _)

noncomputable def gateCost (gs : List Gate) : ℕ := gs.countP isMulGate

lemma gateCost_append (gs₁ gs₂ : List Gate) :
    gateCost (gs₁ ++ gs₂) = gateCost gs₁ + gateCost gs₂ := by
  simp [gateCost, List.countP_append]

lemma wires_length (C : Circuit) (inp : List Bool) :
    (C.wires inp).length = inp.length + C.gates.length := by
  unfold Circuit.wires
  have h : ∀ (gs : List Gate) (acc : List Bool),
      (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) acc).length =
        acc.length + gs.length := by
    intro gs
    induction gs with
    | nil => intro acc; simp
    | cons g gs ih =>
      intro acc
      simp only [List.foldl_cons, ih, List.length_append, List.length_cons, List.length_nil]
      omega
  exact h C.gates inp

lemma wires_append_gate (gs : List Gate) (g : Gate) (inp : List Bool) :
    Circuit.wires ⟨gs ++ [g], 0⟩ inp =
      Circuit.wires ⟨gs, 0⟩ inp ++
        [g.op.eval (g.inputs.map fun i => (Circuit.wires ⟨gs, 0⟩ inp).getD i false)] := by
  simp [Circuit.wires, List.foldl_append]

def wireVal {n : ℕ} (gs : List Gate) (w : ℕ) (x y : V n) : F :=
  b2f ((Circuit.wires ⟨gs, 0⟩ (bits n x ++ bits n y)).getD w false)

lemma foldl_getD_prefix (gs : List Gate) (acc : List Bool) (i : ℕ) (hi : i < acc.length) :
    (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun k => w.getD k false)]) acc).getD i false =
      acc.getD i false := by
  induction gs generalizing acc with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hi' : i < (acc ++ [g.op.eval (g.inputs.map fun k => acc.getD k false)]).length := by
      simp; omega
    rw [ih _ hi', List.getD_eq_getElem _ _ hi', List.getElem_append_left hi,
      List.getD_eq_getElem _ _ hi]

lemma wireVal_input_x {n : ℕ} (gs : List Gate) (j : Fin n) (x y : V n) :
    wireVal gs j.val x y = x j := by
  unfold wireVal
  have hlen : j.val < (bits n x ++ bits n y).length := by simp [bits_length]; omega
  rw [Circuit.wires, foldl_getD_prefix gs _ j.val hlen]
  have hjx : j.val < (bits n x).length := by simp [bits_length]
  rw [List.getD_eq_getElem _ _ hlen, List.getElem_append_left hjx]
  simp [bits, b2f_decide]

lemma wireVal_input_y {n : ℕ} (gs : List Gate) (j : Fin n) (x y : V n) :
    wireVal gs (n + j.val) x y = y j := by
  unfold wireVal
  have hlen : n + j.val < (bits n x ++ bits n y).length := by simp [bits_length]
  rw [Circuit.wires, foldl_getD_prefix gs _ (n + j.val) hlen]
  have hge : (bits n x).length ≤ n + j.val := by simp [bits_length]
  rw [List.getD_eq_getElem _ _ hlen, List.getElem_append_right hge]
  simp [bits, b2f_decide]

lemma wireVal_append_old {n : ℕ} (gs : List Gate) (g : Gate) (w : ℕ)
    (hw : w < 2 * n + gs.length) (x y : V n) :
    wireVal (gs ++ [g]) w x y = wireVal gs w x y := by
  unfold wireVal
  rw [wires_append_gate]
  have hlen : w < (Circuit.wires ⟨gs, 0⟩ (bits n x ++ bits n y)).length := by
    rw [wires_length]; simp [bits_length]; omega
  have hlen' : w < (Circuit.wires ⟨gs, 0⟩ (bits n x ++ bits n y) ++
      [g.op.eval (g.inputs.map fun i => (Circuit.wires ⟨gs, 0⟩ (bits n x ++ bits n y)).getD i false)]).length := by
    rw [List.length_append, List.length_singleton]; omega
  rw [List.getD_eq_getElem _ _ hlen', List.getElem_append_left hlen, List.getD_eq_getElem _ _ hlen]

lemma wireVal_append_new {n : ℕ} (gs : List Gate) (g : Gate) (x y : V n) :
    wireVal (gs ++ [g]) (2 * n + gs.length) x y =
      b2f (g.op.eval (g.inputs.map fun i => decide (wireVal gs i x y = 1))) := by
  unfold wireVal
  rw [wires_append_gate]
  set ws := Circuit.wires ⟨gs, 0⟩ (bits n x ++ bits n y)
  set v := g.op.eval (g.inputs.map fun i => ws.getD i false)
  have hlen : ws.length = 2 * n + gs.length := by
    simp only [ws, wires_length, List.length_append, bits_length]; omega
  have hlt : 2 * n + gs.length < (ws ++ [v]).length := by simp [hlen]
  rw [List.getD_eq_getElem _ _ hlt, List.getElem_append_right (le_of_eq hlen)]
  simp only [hlen, Nat.sub_self, List.getElem_cons_zero, v]
  congr 2
  apply List.map_congr_left
  intro i _
  exact (decide_b2f _).symm

structure BuildState (n : ℕ) where
  gates : List Gate
  hread : PEqualNP.MetaComplexity.NestedCover.ReadsBack (2 * n) ⟨gates, 0⟩
  hleg : ∀ h ∈ gates, legalGate h

def BuildState.len {n : ℕ} (B : BuildState n) : ℕ := 2 * n + B.gates.length

lemma BuildState.append_readsBack {n : ℕ} (B : BuildState n) (g : Gate)
    (hg : ∀ i ∈ g.inputs, i < B.len) :
    PEqualNP.MetaComplexity.NestedCover.ReadsBack (2 * n) ⟨B.gates ++ [g], 0⟩ := by
  intro j hj i hi
  simp only [PEqualNP.MetaComplexity.NestedCover.gateAt] at hi
  simp only [List.length_append, List.length_singleton] at hj
  by_cases hlt : j < B.gates.length
  · have hget : (B.gates ++ [g]).getD j ⟨.or, []⟩ = B.gates.getD j ⟨.or, []⟩ := by
      rw [List.getD_eq_getElem _ _ (by simp; omega), List.getElem_append_left hlt,
        List.getD_eq_getElem _ _ hlt]
    rw [hget] at hi
    exact B.hread j hlt i hi
  · have heq : j = B.gates.length := by omega
    subst heq
    have hget : (B.gates ++ [g]).getD B.gates.length ⟨.or, []⟩ = g := by
      rw [List.getD_eq_getElem _ _ (by simp), List.getElem_append_right le_rfl]
      simp
    rw [hget] at hi
    exact hg i hi

def BuildState.push {n : ℕ} (B : BuildState n) (g : Gate)
    (hread : ∀ i ∈ g.inputs, i < B.len) (hleg : legalGate g) : BuildState n :=
  { gates := B.gates ++ [g]
    hread := B.append_readsBack g hread
    hleg := fun h hh => by
      rcases List.mem_append.mp hh with h1 | h2
      · exact B.hleg h h1
      · rw [List.mem_singleton.mp h2]; exact hleg }

def BuildState.empty (n : ℕ) : BuildState n :=
  { gates := []
    hread := fun j hj => by simp at hj
    hleg := fun h hh => by simp at hh }

def BuildState.addConst0 {n : ℕ} (B : BuildState n) : BuildState n × ℕ :=
  (B.push ⟨.or, []⟩ (fun _ h => by simp at h) ⟨by simp, Or.inr (Or.inl rfl)⟩, B.len)

def BuildState.addConst1 {n : ℕ} (B : BuildState n) : BuildState n × ℕ :=
  (B.push ⟨.and, []⟩ (fun _ h => by simp at h) ⟨by simp, Or.inl rfl⟩, B.len)

def BuildState.addXor {n : ℕ} (B : BuildState n) (w₁ w₂ : ℕ) (h₁ : w₁ < B.len) (h₂ : w₂ < B.len) :
    BuildState n × ℕ :=
  let B₁ := B.push ⟨.mod 2, [w₁, w₂]⟩
    (fun i hi => by
      rcases List.mem_cons.mp hi with rfl | hi
      · exact h₁
      · rcases List.mem_singleton.mp hi with rfl; exact h₂)
    ⟨by simp, Or.inr (Or.inr (Or.inl rfl))⟩
  let B₂ := B₁.push ⟨.not, [B.len]⟩
    (fun i hi => by
      rw [List.mem_singleton.mp hi]
      change 2 * n + B.gates.length < 2 * n + (B.gates ++ [_]).length
      simp)
    ⟨by simp, Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩))⟩
  (B₂, B₁.len)

def BuildState.addAnd {n : ℕ} (B : BuildState n) (w₁ w₂ : ℕ) (h₁ : w₁ < B.len) (h₂ : w₂ < B.len) :
    BuildState n × ℕ :=
  (B.push ⟨.and, [w₁, w₂]⟩
    (fun i hi => by
      rcases List.mem_cons.mp hi with rfl | hi
      · exact h₁
      · rcases List.mem_singleton.mp hi with rfl; exact h₂)
    ⟨by simp, Or.inl rfl⟩, B.len)

lemma isMulGate_const0 : isMulGate ⟨.or, []⟩ = false := by
  simp [isMulGate]

lemma isMulGate_const1 : isMulGate ⟨.and, []⟩ = false := by
  simp [isMulGate]

lemma isMulGate_mod2 (a b : ℕ) : isMulGate ⟨.mod 2, [a, b]⟩ = false := by
  simp [isMulGate]

lemma isMulGate_not (a : ℕ) : isMulGate ⟨.not, [a]⟩ = false := by
  simp [isMulGate]

lemma isMulGate_and2 (a b : ℕ) : isMulGate ⟨.and, [a, b]⟩ = true := by
  simp [isMulGate]

lemma addConst0_spec {n : ℕ} (B : BuildState n) :
    let r := B.addConst0
    B.len ≤ r.1.len ∧ r.2 < r.1.len ∧ gateCost r.1.gates = gateCost B.gates ∧
    (∀ w < B.len, ∀ x y : V n, wireVal r.1.gates w x y = wireVal B.gates w x y) ∧
    (∀ x y : V n, wireVal r.1.gates r.2 x y = 0) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp [BuildState.addConst0, BuildState.push, BuildState.len]
  · simp [BuildState.addConst0, BuildState.push, BuildState.len]
  · simp [BuildState.addConst0, BuildState.push, gateCost, isMulGate_const0]
  · intro w hw x y; exact wireVal_append_old B.gates ⟨.or, []⟩ w hw x y
  · intro x y
    change wireVal (B.gates ++ [⟨.or, []⟩]) (2 * n + B.gates.length) x y = 0
    rw [wireVal_append_new]; rfl

lemma addConst1_spec {n : ℕ} (B : BuildState n) :
    let r := B.addConst1
    B.len ≤ r.1.len ∧ r.2 < r.1.len ∧ gateCost r.1.gates = gateCost B.gates ∧
    (∀ w < B.len, ∀ x y : V n, wireVal r.1.gates w x y = wireVal B.gates w x y) ∧
    (∀ x y : V n, wireVal r.1.gates r.2 x y = 1) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp [BuildState.addConst1, BuildState.push, BuildState.len]
  · simp [BuildState.addConst1, BuildState.push, BuildState.len]
  · simp [BuildState.addConst1, BuildState.push, gateCost, isMulGate_const1]
  · intro w hw x y; exact wireVal_append_old B.gates ⟨.and, []⟩ w hw x y
  · intro x y
    change wireVal (B.gates ++ [⟨.and, []⟩]) (2 * n + B.gates.length) x y = 1
    rw [wireVal_append_new]; rfl

lemma addXor_spec {n : ℕ} (B : BuildState n) (w₁ w₂ : ℕ) (h₁ : w₁ < B.len) (h₂ : w₂ < B.len) :
    let r := B.addXor w₁ w₂ h₁ h₂
    B.len ≤ r.1.len ∧ r.2 < r.1.len ∧ gateCost r.1.gates = gateCost B.gates ∧
    (∀ w < B.len, ∀ x y : V n, wireVal r.1.gates w x y = wireVal B.gates w x y) ∧
    (∀ x y : V n, wireVal r.1.gates r.2 x y = wireVal B.gates w₁ x y + wireVal B.gates w₂ x y) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp [BuildState.addXor, BuildState.push, BuildState.len]
  · simp [BuildState.addXor, BuildState.push, BuildState.len]
  · simp [BuildState.addXor, BuildState.push, gateCost, isMulGate_mod2, isMulGate_not]
  · intro w hw x y
    dsimp only [BuildState.addXor, BuildState.push]
    rw [wireVal_append_old _ _ w (by simp [BuildState.len] at hw ⊢; omega)]
    exact wireVal_append_old B.gates _ w hw x y
  · intro x y
    dsimp only [BuildState.addXor, BuildState.push, BuildState.len]
    rw [wireVal_append_new]
    simp only [List.map_cons, List.map_nil, GateOp.eval, List.headD_cons, b2f_not, b2f_decide]
    rw [wireVal_append_new]
    simp only [List.map_cons, List.map_nil, b2f_mod2_pair, b2f_decide]
    have h : wireVal B.gates w₁ x y + wireVal B.gates w₂ x y + 1 + 1 =
        wireVal B.gates w₁ x y + wireVal B.gates w₂ x y + (1 + 1) := by ring
    rw [h]; simp only [f_add_self, add_zero]

lemma addAnd_spec {n : ℕ} (B : BuildState n) (w₁ w₂ : ℕ) (h₁ : w₁ < B.len) (h₂ : w₂ < B.len) :
    let r := B.addAnd w₁ w₂ h₁ h₂
    B.len ≤ r.1.len ∧ r.2 < r.1.len ∧ gateCost r.1.gates = gateCost B.gates + 1 ∧
    (∀ w < B.len, ∀ x y : V n, wireVal r.1.gates w x y = wireVal B.gates w x y) ∧
    (∀ x y : V n, wireVal r.1.gates r.2 x y = wireVal B.gates w₁ x y * wireVal B.gates w₂ x y) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp [BuildState.addAnd, BuildState.push, BuildState.len]
  · simp [BuildState.addAnd, BuildState.push, BuildState.len]
  · simp [BuildState.addAnd, BuildState.push, gateCost, isMulGate_and2]
  · intro w hw x y; exact wireVal_append_old B.gates _ w hw x y
  · intro x y
    dsimp only [BuildState.addAnd, BuildState.push, BuildState.len]
    rw [wireVal_append_new]
    simp only [List.map_cons, List.map_nil, GateOp.eval, List.all_cons, List.all_nil, id_eq,
      Bool.and_true, b2f_and, b2f_decide]

lemma build_sum {n : ℕ} (B : BuildState n) (ws : List ℕ) (hws : ∀ w ∈ ws, w < B.len) :
    ∃ (B' : BuildState n) (out : ℕ),
      B.len ≤ B'.len ∧ out < B'.len ∧ gateCost B'.gates = gateCost B.gates ∧
      (∀ w < B.len, ∀ x y : V n, wireVal B'.gates w x y = wireVal B.gates w x y) ∧
      (∀ x y : V n, wireVal B'.gates out x y = (ws.map (fun w => wireVal B.gates w x y)).sum) := by
  induction ws generalizing B with
  | nil =>
    obtain ⟨h1, h2, h3, h4, h5⟩ := addConst0_spec B
    exact ⟨B.addConst0.1, B.addConst0.2, h1, h2, h3, h4, fun x y => by simp [h5 x y]⟩
  | cons w ws ih =>
    have hw : w < B.len := hws w List.mem_cons_self
    have hrest : ∀ u ∈ ws, u < B.len := fun u hu => hws u (List.mem_cons_of_mem w hu)
    obtain ⟨B₁, out₁, hle1, hout1, hcost1, hold1, hval1⟩ := ih B hrest
    have hw1 : w < B₁.len := lt_of_lt_of_le hw hle1
    obtain ⟨hle2, hout2, hcost2, hold2, hval2⟩ := addXor_spec B₁ w out₁ hw1 hout1
    refine ⟨(B₁.addXor w out₁ hw1 hout1).1, (B₁.addXor w out₁ hw1 hout1).2,
      le_trans hle1 hle2, hout2, hcost2.trans hcost1, ?_, ?_⟩
    · intro u hu x y
      rw [hold2 u (lt_of_lt_of_le hu hle1), hold1 u hu]
    · intro x y
      rw [hval2 x y, hold1 w hw x y, hval1 x y]
      rfl

lemma build_weighted_sum {n : ℕ} {ι : Type*} [Fintype ι] (B : BuildState n)
    (coeff : ι → F) (wire : ι → ℕ) (hwire : ∀ i : ι, wire i < B.len) :
    ∃ (B' : BuildState n) (out : ℕ),
      B.len ≤ B'.len ∧ out < B'.len ∧ gateCost B'.gates = gateCost B.gates ∧
      (∀ w < B.len, ∀ x y : V n, wireVal B'.gates w x y = wireVal B.gates w x y) ∧
      (∀ x y : V n, wireVal B'.gates out x y = ∑ i : ι, coeff i * wireVal B.gates (wire i) x y) := by
  classical
  let l : List ι := Finset.univ.toList
  let ws : List ℕ := l.filterMap (fun i => if coeff i = 1 then some (wire i) else none)
  have hws : ∀ w ∈ ws, w < B.len := by
    intro w hw
    rcases List.mem_filterMap.mp hw with ⟨i, _, hi⟩
    split_ifs at hi
    cases hi; exact hwire i
  obtain ⟨B', out, h1, h2, h3, h4, h5⟩ := build_sum B ws hws
  refine ⟨B', out, h1, h2, h3, h4, ?_⟩
  intro x y
  rw [h5 x y]
  have hmap : ∀ (xs : List ι),
      ((xs.filterMap (fun i => if coeff i = 1 then some (wire i) else none)).map
        (fun w => wireVal B.gates w x y)).sum =
      (xs.map (fun i => coeff i * wireVal B.gates (wire i) x y)).sum := by
    intro xs
    induction xs with
    | nil => simp
    | cons a xs ih =>
      simp only [List.filterMap_cons, List.map_cons, List.sum_cons]
      rcases f_cases (coeff a) with ha | ha
      · simp [ha, ih]
      · simp [ha, ih]
  rw [hmap l]
  have hlist : (l.map (fun i => coeff i * wireVal B.gates (wire i) x y)).sum =
      ∑ i ∈ Finset.univ, coeff i * wireVal B.gates (wire i) x y := by
    change (Finset.univ.toList.map (fun i => coeff i * wireVal B.gates (wire i) x y)).sum = _
    rw [← Multiset.sum_coe, ← Multiset.map_coe, Finset.coe_toList]; rfl
  exact hlist

lemma model_implies_fits {n c : ℕ} {g : V n → F}
    (L : V n →ₗ[F] E c) (q : V n → F) (hq : quad q)
    (hg_eq : ∀ x : V n, g x = q x + ∑ i : Fin c, L x (i, 0) * L x (i, 1) * L x (i, 2)) :
    ∃ C : Circuit,
      (PEqualNP.MetaComplexity.NestedCover.ReadsBack (2 * n) C ∧
        ∀ h ∈ C.gates, legalGate h) ∧
      gateCost C.gates ≤ n + c ∧
      ∀ x y : V n, C.eval (bits n x ++ bits n y) = decide (dotProduct x y + g y = 1) := by
  rcases hq with ⟨s₀, h₀, M₀, hq⟩
  have hstep1 : ∀ k (hk : k ≤ c),
      ∃ (B : BuildState n) (pW : Fin k → ℕ),
        gateCost B.gates = k ∧
        (∀ i : Fin k, pW i < B.len) ∧
        (∀ i : Fin k, ∀ x y : V n,
          wireVal B.gates (pW i) x y = L y (⟨i.val, by omega⟩, 1) * L y (⟨i.val, by omega⟩, 2)) := by
    intro k hk
    induction k with
    | zero =>
      exact ⟨BuildState.empty n, fun i => i.elim0, rfl, fun i => i.elim0, fun i => i.elim0⟩
    | succ k ih =>
      obtain ⟨B, pW, hcost, hpW_lt, hpW_val⟩ := ih (by omega)
      let i_cur : Fin c := ⟨k, by omega⟩
      have hylen : ∀ j : Fin n, n + j.val < B.len := fun j => by
        change n + j.val < 2 * n + B.gates.length; omega
      obtain ⟨B₁, w₁, hle1, hw1, hc1, ho1, hv1⟩ :=
        build_weighted_sum B (fun j : Fin n => L (unit j) (i_cur, 1)) (fun j => n + j.val) hylen
      have hylen1 : ∀ j : Fin n, n + j.val < B₁.len := fun j => lt_of_lt_of_le (hylen j) hle1
      obtain ⟨B₂, w₂, hle2, hw2, hc2, ho2, hv2⟩ :=
        build_weighted_sum B₁ (fun j : Fin n => L (unit j) (i_cur, 2)) (fun j => n + j.val) hylen1
      have hw1' : w₁ < B₂.len := lt_of_lt_of_le hw1 hle2
      obtain ⟨hle3, hw3, hc3, ho3, hv3⟩ := addAnd_spec B₂ w₁ w₂ hw1' hw2
      let B₃ := (B₂.addAnd w₁ w₂ hw1' hw2).1
      let w₃ := (B₂.addAnd w₁ w₂ hw1' hw2).2
      refine ⟨B₃, Fin.snoc pW w₃, ?_, ?_, ?_⟩
      · change gateCost (B₂.addAnd w₁ w₂ hw1' hw2).1.gates = k + 1; omega
      · intro i
        refine Fin.lastCases ?_ ?_ i
        · simp only [Fin.snoc_last]; exact hw3
        · intro j; simp only [Fin.snoc_castSucc]
          exact lt_of_lt_of_le (hpW_lt j) (le_trans hle1 (le_trans hle2 hle3))
      · intro i x y
        refine Fin.lastCases ?_ ?_ i
        · simp only [Fin.snoc_last]
          rw [hv3 x y, ho2 w₁ hw1 x y, hv1 x y, hv2 x y]
          have hL1 : (∑ j : Fin n, L (unit j) (i_cur, 1) * wireVal B.gates (n + j.val) x y) =
              L y (i_cur, 1) := by
            conv_rhs => rw [vec_eq_sum_unit y]
            simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
            apply Finset.sum_congr rfl; intro j _
            rw [wireVal_input_y]; ring
          have hL2 : (∑ j : Fin n, L (unit j) (i_cur, 2) * wireVal B₁.gates (n + j.val) x y) =
              L y (i_cur, 2) := by
            conv_rhs => rw [vec_eq_sum_unit y]
            simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
            apply Finset.sum_congr rfl; intro j _
            rw [wireVal_input_y]; ring
          rw [hL1, hL2]; rfl
        · intro j
          simp only [Fin.snoc_castSucc]
          rw [ho3 _ (lt_of_lt_of_le (hpW_lt j) (le_trans hle1 hle2)),
            ho2 _ (lt_of_lt_of_le (hpW_lt j) hle1), ho1 _ (hpW_lt j), hpW_val j x y]
          rfl
  obtain ⟨Bp, pW, hBp_cost, hpW_lt, hpW_val⟩ := hstep1 c le_rfl
  have hstep2 : ∀ k (hk : k ≤ n),
      ∃ (B : BuildState n) (tW : Fin k → ℕ),
        Bp.len ≤ B.len ∧
        gateCost B.gates = c + k ∧
        (∀ w < Bp.len, ∀ x y : V n, wireVal B.gates w x y = wireVal Bp.gates w x y) ∧
        (∀ j : Fin k, tW j < B.len) ∧
        (∀ j : Fin k, ∀ x y : V n,
          wireVal B.gates (tW j) x y =
            (x ⟨j.val, by omega⟩ + h₀ ⟨j.val, by omega⟩ +
              (∑ r : Fin n, M₀ ⟨j.val, by omega⟩ r * y r) +
              (∑ i : Fin c, L (unit ⟨j.val, by omega⟩) (i, 0) * (L y (i, 1) * L y (i, 2)))) *
            y ⟨j.val, by omega⟩) := by
    intro k hk
    induction k with
    | zero =>
      exact ⟨Bp, fun j => j.elim0, le_rfl, hBp_cost, fun _ _ _ _ => rfl,
        fun j => j.elim0, fun j => j.elim0⟩
    | succ k ih =>
      obtain ⟨B, tW, hBpB, hB_cost, hB_old, htW_lt, htW_val⟩ := ih (by omega)
      let j_cur : Fin n := ⟨k, by omega⟩
      have hxlen : j_cur.val < B.len := by change k < 2 * n + B.gates.length; omega
      have hylen : ∀ r : Fin n, n + r.val < B.len := fun r => by
        change n + r.val < 2 * n + B.gates.length; omega
      obtain ⟨B₁, wm, hle1, hwm, hc1, ho1, hvm⟩ :=
        build_weighted_sum B (fun r : Fin n => M₀ j_cur r) (fun r => n + r.val) hylen
      have hpW1 : ∀ i : Fin c, pW i < B₁.len := fun i =>
        lt_of_lt_of_le (hpW_lt i) (le_trans hBpB hle1)
      obtain ⟨B₂, wp, hle2, hwp, hc2, ho2, hvp⟩ :=
        build_weighted_sum B₁ (fun i : Fin c => L (unit j_cur) (i, 0)) pW hpW1
      have hconst : ∃ (B₃ : BuildState n) (wc : ℕ),
          B₂.len ≤ B₃.len ∧ wc < B₃.len ∧ gateCost B₃.gates = gateCost B₂.gates ∧
          (∀ w < B₂.len, ∀ x y : V n, wireVal B₃.gates w x y = wireVal B₂.gates w x y) ∧
          (∀ x y : V n, wireVal B₃.gates wc x y = h₀ j_cur) := by
        rcases f_cases (h₀ j_cur) with hh | hh
        · obtain ⟨a, b, c', d, e⟩ := addConst0_spec B₂
          exact ⟨B₂.addConst0.1, B₂.addConst0.2, a, b, c', d, fun x y => by rw [e, hh]⟩
        · obtain ⟨a, b, c', d, e⟩ := addConst1_spec B₂
          exact ⟨B₂.addConst1.1, B₂.addConst1.2, a, b, c', d, fun x y => by rw [e, hh]⟩
      obtain ⟨B₃, wc, hle3, hwc, hc3, ho3, hvc⟩ := hconst
      have hxj3 : j_cur.val < B₃.len := lt_of_lt_of_le hxlen (le_trans hle1 (le_trans hle2 hle3))
      have hwm3 : wm < B₃.len := lt_of_lt_of_le hwm (le_trans hle2 hle3)
      have hwp3 : wp < B₃.len := lt_of_lt_of_le hwp hle3
      obtain ⟨hle4, hw4, hc4, ho4, hv4⟩ := addXor_spec B₃ j_cur.val wc hxj3 hwc
      let B₄ := (B₃.addXor j_cur.val wc hxj3 hwc).1
      let w₄ := (B₃.addXor j_cur.val wc hxj3 hwc).2
      obtain ⟨hle5, hw5, hc5, ho5, hv5⟩ := addXor_spec B₄ w₄ wm hw4 (lt_of_lt_of_le hwm3 hle4)
      let B₅ := (B₄.addXor w₄ wm hw4 (lt_of_lt_of_le hwm3 hle4)).1
      let w₅ := (B₄.addXor w₄ wm hw4 (lt_of_lt_of_le hwm3 hle4)).2
      obtain ⟨hle6, hw6, hc6, ho6, hv6⟩ := addXor_spec B₅ w₅ wp hw5 (lt_of_lt_of_le hwp3 (le_trans hle4 hle5))
      let B₆ := (B₅.addXor w₅ wp hw5 (lt_of_lt_of_le hwp3 (le_trans hle4 hle5))).1
      let w₆ := (B₅.addXor w₅ wp hw5 (lt_of_lt_of_le hwp3 (le_trans hle4 hle5))).2
      have hyj6 : n + j_cur.val < B₆.len :=
        lt_of_lt_of_le (hylen j_cur) (le_trans hle1 (le_trans hle2 (le_trans hle3 (le_trans hle4 (le_trans hle5 hle6)))))
      obtain ⟨hle7, hw7, hc7, ho7, hv7⟩ := addAnd_spec B₆ w₆ (n + j_cur.val) hw6 hyj6
      let B₇ := (B₆.addAnd w₆ (n + j_cur.val) hw6 hyj6).1
      let w₇ := (B₆.addAnd w₆ (n + j_cur.val) hw6 hyj6).2
      have hB_le : B.len ≤ B₇.len :=
        le_trans hle1 (le_trans hle2 (le_trans hle3 (le_trans hle4 (le_trans hle5 (le_trans hle6 hle7)))))
      have hB_pres : ∀ w < B.len, ∀ x y : V n, wireVal B₇.gates w x y = wireVal B.gates w x y := by
        intro w hw x y
        rw [ho7 w (lt_of_lt_of_le hw (le_trans hle1 (le_trans hle2 (le_trans hle3 (le_trans hle4 (le_trans hle5 hle6)))))),
          ho6 w (lt_of_lt_of_le hw (le_trans hle1 (le_trans hle2 (le_trans hle3 (le_trans hle4 hle5))))),
          ho5 w (lt_of_lt_of_le hw (le_trans hle1 (le_trans hle2 (le_trans hle3 hle4)))),
          ho4 w (lt_of_lt_of_le hw (le_trans hle1 (le_trans hle2 hle3))),
          ho3 w (lt_of_lt_of_le hw (le_trans hle1 hle2)),
          ho2 w (lt_of_lt_of_le hw hle1),
          ho1 w hw]
      refine ⟨B₇, Fin.snoc tW w₇, le_trans hBpB hB_le, by
        have hcost7 : gateCost B₇.gates = gateCost B₆.gates + 1 := hc7
        rw [hcost7, hc6, hc5, hc4, hc3, hc2, hc1, hB_cost]; omega, ?_, ?_, ?_⟩
      · intro w hw x y; rw [hB_pres w (lt_of_lt_of_le hw hBpB), hB_old w hw]
      · intro j
        refine Fin.lastCases ?_ ?_ j
        · simp only [Fin.snoc_last]; exact hw7
        · intro j'; simp only [Fin.snoc_castSucc]; exact lt_of_lt_of_le (htW_lt j') hB_le
      · intro j x y
        refine Fin.lastCases ?_ ?_ j
        · simp only [Fin.snoc_last]
          rw [hv7 x y, wireVal_input_y, hv6 x y, hv5 x y, hv4 x y, wireVal_input_x, hvc x y]
          rw [ho4 wm hwm3 x y, ho3 wm (lt_of_lt_of_le hwm hle2) x y, ho2 wm hwm x y, hvm x y]
          rw [ho5 wp (lt_of_lt_of_le hwp3 hle4) x y, ho4 wp hwp3 x y, ho3 wp hwp x y, hvp x y]
          have h1 : (∑ r : Fin n, M₀ j_cur r * wireVal B.gates (n + r.val) x y) =
              ∑ r : Fin n, M₀ j_cur r * y r := by
            apply Finset.sum_congr rfl; intro r _; rw [wireVal_input_y]
          have h2 : (∑ i : Fin c, L (unit j_cur) (i, 0) * wireVal B₁.gates (pW i) x y) =
              ∑ i : Fin c, L (unit j_cur) (i, 0) * (L y (i, 1) * L y (i, 2)) := by
            apply Finset.sum_congr rfl; intro i _
            rw [ho1 (pW i) (lt_of_lt_of_le (hpW_lt i) hBpB), hB_old (pW i) (hpW_lt i), hpW_val i x y]
          rw [h1, h2]; rfl
        · intro j'
          simp only [Fin.snoc_castSucc]
          rw [hB_pres (tW j') (htW_lt j') x y, htW_val j' x y]; rfl
  obtain ⟨Bt, tW, _, hBt_cost, _, htW_lt, htW_val⟩ := hstep2 n le_rfl
  obtain ⟨Bs, ws, hle_s, hws, hc_s, ho_s, hv_s⟩ :=
    build_weighted_sum Bt (fun _ : Fin n => (1 : F)) tW htW_lt
  have hfinal : ∃ (Bf : BuildState n) (out : ℕ),
      gateCost Bf.gates = n + c ∧
      (∀ x y : V n, wireVal Bf.gates out x y = s₀ + ∑ j : Fin n, wireVal Bt.gates (tW j) x y) := by
    rcases f_cases s₀ with hs0 | hs0
    · refine ⟨Bs, ws, by omega, fun x y => ?_⟩
      rw [hs0, zero_add, hv_s x y]
      apply Finset.sum_congr rfl; intro j _; rw [one_mul]
    · obtain ⟨hle1, hwc1, hc1, ho1, hvc1⟩ := addConst1_spec Bs
      let B₁ := Bs.addConst1.1
      let wc1 := Bs.addConst1.2
      obtain ⟨_, _, hc2, _, hv2⟩ := addXor_spec B₁ wc1 ws hwc1 (lt_of_lt_of_le hws hle1)
      refine ⟨(B₁.addXor wc1 ws hwc1 (lt_of_lt_of_le hws hle1)).1,
        (B₁.addXor wc1 ws hwc1 (lt_of_lt_of_le hws hle1)).2,
        by rw [hc2, hc1, hc_s, hBt_cost]; omega, fun x y => ?_⟩
      rw [hv2 x y, hvc1 x y, ho1 ws hws x y, hv_s x y, hs0]
      congr 1; apply Finset.sum_congr rfl; intro j _; rw [one_mul]
  obtain ⟨Bf, out, hBf_cost, hBf_val⟩ := hfinal
  refine ⟨⟨Bf.gates, out⟩, ⟨Bf.hread, Bf.hleg⟩, le_of_eq hBf_cost, ?_⟩
  intro x y
  have hev : Circuit.eval ⟨Bf.gates, out⟩ (bits n x ++ bits n y) =
      decide (wireVal Bf.gates out x y = 1) := by
    unfold Circuit.eval wireVal
    exact (decide_b2f _).symm
  rw [hev, hBf_val x y]
  congr 1
  rw [hg_eq y, hq y]
  have hexp : ∑ j : Fin n, wireVal Bt.gates (tW j) x y =
      dotProduct x y + dotProduct h₀ y + (∑ j : Fin n, ∑ r : Fin n, M₀ j r * y j * y r) +
        ∑ i : Fin c, L y (i, 0) * L y (i, 1) * L y (i, 2) := by
    have h1 : ∀ j : Fin n, wireVal Bt.gates (tW j) x y =
        x j * y j + h₀ j * y j + (∑ r : Fin n, M₀ j r * y j * y r) +
          (∑ i : Fin c, L (unit j) (i, 0) * y j * (L y (i, 1) * L y (i, 2))) := by
      intro j
      rw [htW_val j x y]
      simp only [add_mul, Finset.sum_mul]
      congr 1
      · congr 1
        apply Finset.sum_congr rfl; intro r _; ring
      · apply Finset.sum_congr rfl; intro i _; ring
    simp_rw [h1, Finset.sum_add_distrib]
    congr 1
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro i _
    rw [← Finset.sum_mul]
    have hLi : (∑ j : Fin n, L (unit j) (i, 0) * y j) = L y (i, 0) := by
      conv_rhs => rw [vec_eq_sum_unit y]
      simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      apply Finset.sum_congr rfl; intro j _; ring
    rw [hLi]; ring
  rw [hexp]; ring

structure AffExpr (n k : ℕ) where
  c0 : F
  lx : V n
  ly : V n
  lm : Fin k → F

def AffExpr.eval {n k : ℕ} (e : AffExpr n k) (x y : V n) (m : Fin k → F) : F :=
  e.c0 + dotProduct e.lx x + dotProduct e.ly y + ∑ j : Fin k, e.lm j * m j

def AffExpr.const {n k : ℕ} (c : F) : AffExpr n k := ⟨c, 0, 0, 0⟩
def AffExpr.varX {n k : ℕ} (j : Fin n) : AffExpr n k := ⟨0, unit j, 0, 0⟩
def AffExpr.varY {n k : ℕ} (j : Fin n) : AffExpr n k := ⟨0, 0, unit j, 0⟩
def AffExpr.varM {n k : ℕ} (j : Fin k) : AffExpr n k := ⟨0, 0, 0, Pi.single j 1⟩
def AffExpr.add {n k : ℕ} (e₁ e₂ : AffExpr n k) : AffExpr n k :=
  ⟨e₁.c0 + e₂.c0, e₁.lx + e₂.lx, e₁.ly + e₂.ly, e₁.lm + e₂.lm⟩
def AffExpr.add1 {n k : ℕ} (e : AffExpr n k) : AffExpr n k := ⟨e.c0 + 1, e.lx, e.ly, e.lm⟩
def AffExpr.lift {n k : ℕ} (e : AffExpr n k) : AffExpr n (k + 1) :=
  ⟨e.c0, e.lx, e.ly, Fin.snoc e.lm 0⟩

lemma AffExpr.eval_const {n k : ℕ} (c : F) (x y : V n) (m : Fin k → F) :
    (AffExpr.const c).eval x y m = c := by simp [AffExpr.eval, AffExpr.const]

lemma AffExpr.eval_varX {n k : ℕ} (j : Fin n) (x y : V n) (m : Fin k → F) :
    (AffExpr.varX j).eval x y m = x j := by
  simp only [AffExpr.eval, AffExpr.varX, zero_add, dotProduct_zero, add_zero, Pi.zero_apply,
    zero_mul, Finset.sum_const_zero, dotProduct, unit]
  rw [Finset.sum_eq_single j]
  · simp
  · intro i _ hij; simp [Ne.symm hij]
  · intro hj; exact (hj (Finset.mem_univ j)).elim

lemma AffExpr.eval_varY {n k : ℕ} (j : Fin n) (x y : V n) (m : Fin k → F) :
    (AffExpr.varY j).eval x y m = y j := by
  simp only [AffExpr.eval, AffExpr.varY, zero_add, dotProduct_zero, add_zero, Pi.zero_apply,
    zero_mul, Finset.sum_const_zero, dotProduct, unit]
  rw [Finset.sum_eq_single j]
  · simp
  · intro i _ hij; simp [Ne.symm hij]
  · intro hj; exact (hj (Finset.mem_univ j)).elim

lemma AffExpr.eval_varM {n k : ℕ} (j : Fin k) (x y : V n) (m : Fin k → F) :
    (AffExpr.varM j).eval x y m = m j := by
  simp only [AffExpr.eval, AffExpr.varM, zero_add, dotProduct_zero, add_zero, Pi.single_apply]
  rw [Finset.sum_eq_single j]
  · simp
  · intro i _ hij; simp [hij]
  · intro hj; exact (hj (Finset.mem_univ j)).elim

lemma AffExpr.eval_add {n k : ℕ} (e₁ e₂ : AffExpr n k) (x y : V n) (m : Fin k → F) :
    (e₁.add e₂).eval x y m = e₁.eval x y m + e₂.eval x y m := by
  simp only [AffExpr.eval, AffExpr.add, add_dotProduct, Pi.add_apply, add_mul,
    Finset.sum_add_distrib]
  ring

lemma AffExpr.eval_add1 {n k : ℕ} (e : AffExpr n k) (x y : V n) (m : Fin k → F) :
    e.add1.eval x y m = e.eval x y m + 1 := by
  simp only [AffExpr.eval, AffExpr.add1]; ring

lemma AffExpr.eval_lift {n k : ℕ} (e : AffExpr n k) (x y : V n) (m : Fin (k + 1) → F) :
    e.lift.eval x y m = e.eval x y (fun j => m j.castSucc) := by
  simp only [AffExpr.eval, AffExpr.lift, Fin.sum_univ_castSucc, Fin.snoc_castSucc, Fin.snoc_last,
    zero_mul, add_zero]

structure SLP (n s : ℕ) where
  u : ∀ j : Fin s, AffExpr n j.val
  v : ∀ j : Fin s, AffExpr n j.val

def SLP.evalM {n s : ℕ} (S : SLP n s) (x y : V n) : (k : ℕ) → (hk : k ≤ s) → Fin k → F
  | 0, _, i => i.elim0
  | k + 1, hk, i =>
    let prev := S.evalM x y k (by omega)
    let cur := (S.u ⟨k, by omega⟩).eval x y prev * (S.v ⟨k, by omega⟩).eval x y prev
    Fin.snoc (α := fun _ => F) prev cur i

def SLP.evalFull {n s : ℕ} (S : SLP n s) (x y : V n) : Fin s → F :=
  S.evalM x y s le_rfl

def SLP.snoc {n s : ℕ} (S : SLP n s) (u' v' : AffExpr n s) : SLP n (s + 1) where
  u j := if h : j.val < s then S.u ⟨j.val, h⟩ else
    cast (congrArg (AffExpr n) (show s = j.val by omega)) u'
  v j := if h : j.val < s then S.v ⟨j.val, h⟩ else
    cast (congrArg (AffExpr n) (show s = j.val by omega)) v'

lemma SLP.evalM_snoc_le {n s : ℕ} (S : SLP n s) (u' v' : AffExpr n s) (x y : V n) :
    ∀ (k : ℕ) (hk : k ≤ s),
      (S.snoc u' v').evalM x y k (by omega) = S.evalM x y k hk := by
  intro k hk
  induction k with
  | zero => funext i; exact i.elim0
  | succ k ih =>
    funext i
    rw [SLP.evalM, SLP.evalM, ih (by omega)]
    have hlt : k < s := by omega
    simp only [SLP.snoc, Fin.val_mk, hlt, dite_true]

lemma SLP.evalFull_snoc {n s : ℕ} (S : SLP n s) (u' v' : AffExpr n s) (x y : V n) :
    (S.snoc u' v').evalFull x y =
      Fin.snoc (α := fun _ => F) (S.evalFull x y) (u'.eval x y (S.evalFull x y) * v'.eval x y (S.evalFull x y)) := by
  funext i
  rw [SLP.evalFull, SLP.evalM, SLP.evalM_snoc_le S u' v' x y s le_rfl]
  simp only [SLP.snoc, Fin.val_mk, Nat.lt_irrefl, dite_false, cast_eq]; rfl

lemma circuit_to_slp {n : ℕ} (gs : List Gate)
    (hread : PEqualNP.MetaComplexity.NestedCover.ReadsBack (2 * n) ⟨gs, 0⟩)
    (hleg : ∀ h ∈ gs, legalGate h) :
    ∃ (S : SLP n (gateCost gs)) (wireE : Fin (2 * n + gs.length) → AffExpr n (gateCost gs)),
      ∀ (w : Fin (2 * n + gs.length)) (x y : V n),
        (wireE w).eval x y (S.evalFull x y) = wireVal gs w.val x y := by
  induction gs using List.reverseRecOn with
  | nil =>
    refine ⟨⟨fun j => j.elim0, fun j => j.elim0⟩, fun w =>
      if h : w.val < n then AffExpr.varX ⟨w.val, h⟩
      else AffExpr.varY ⟨w.val - n, by have := w.isLt; simp only [List.length_nil, add_zero] at this; omega⟩, ?_⟩
    intro w x y
    by_cases h : w.val < n
    · simp only [h, dite_true, AffExpr.eval_varX]
      exact (wireVal_input_x [] ⟨w.val, h⟩ x y).symm
    · simp only [h, dite_false, AffExpr.eval_varY]
      have hw : w.val < 2 * n := by have := w.isLt; simp only [List.length_nil, add_zero] at this; omega
      have heq : n + (w.val - n) = w.val := by omega
      have hv := wireVal_input_y [] ⟨w.val - n, by omega⟩ x y
      rw [heq] at hv; exact hv.symm
  | append_singleton gs g ih =>
    have hread_gs : PEqualNP.MetaComplexity.NestedCover.ReadsBack (2 * n) ⟨gs, 0⟩ := by
      intro j hj i hi
      have hj' : j < (gs ++ [g]).length := by
        dsimp only at hj; rw [List.length_append, List.length_singleton]; omega
      have hget : (gs ++ [g]).getD j ⟨.or, []⟩ = gs.getD j ⟨.or, []⟩ := by
        rw [List.getD_eq_getElem _ _ hj', List.getElem_append_left hj, List.getD_eq_getElem _ _ hj]
      have hi' : i ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt ⟨gs ++ [g], 0⟩ j).inputs := by
        change i ∈ ((gs ++ [g]).getD j ⟨.or, []⟩).inputs
        rw [hget]; exact hi
      exact hread j hj' i hi'
    have hleg_gs : ∀ h ∈ gs, legalGate h := fun h hh => hleg h (List.mem_append_left [g] hh)
    have hleg_g : legalGate g := hleg g (List.mem_append_right gs List.mem_cons_self)
    have hread_g : ∀ i ∈ g.inputs, i < 2 * n + gs.length := by
      intro i hi
      have hget : (gs ++ [g]).getD gs.length ⟨.or, []⟩ = g := by
        rw [List.getD_eq_getElem _ _ (by simp), List.getElem_append_right le_rfl]; simp
      have hi' : i ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt ⟨gs ++ [g], 0⟩ gs.length).inputs := by
        simpa [PEqualNP.MetaComplexity.NestedCover.gateAt, hget] using hi
      exact hread gs.length (by simp) i hi'
    obtain ⟨S, wireE, hwireE⟩ := ih hread_gs hleg_gs
    rcases g with ⟨op, ins⟩
    rcases hleg_g with ⟨hlen_ins, hop⟩
    have hcost_app : gateCost (gs ++ [⟨op, ins⟩]) = gateCost gs + (if isMulGate ⟨op, ins⟩ then 1 else 0) := by
      rw [gateCost_append]; simp [gateCost, List.countP_cons, List.countP_nil]
    cases ins with
    | nil =>
      have hmul : isMulGate ⟨op, []⟩ = false := by simp [isMulGate]
      have hc : gateCost (gs ++ [⟨op, []⟩]) = gateCost gs := by rw [hcost_app, hmul]; simp
      have hconst : ∃ c : F, ∀ x y : V n, wireVal (gs ++ [⟨op, []⟩]) (2 * n + gs.length) x y = c := by
        rcases hop with rfl | rfl | rfl | ⟨rfl, h1⟩
        · exact ⟨1, fun x y => by rw [wireVal_append_new]; rfl⟩
        · exact ⟨0, fun x y => by rw [wireVal_append_new]; rfl⟩
        · exact ⟨1, fun x y => by rw [wireVal_append_new]; rfl⟩
        · simp at h1
      obtain ⟨c, hc_val⟩ := hconst
      rw [hc]
      refine ⟨S, fun w =>
        if hw : w.val < 2 * n + gs.length then wireE ⟨w.val, hw⟩ else AffExpr.const c, ?_⟩
      intro w x y
      by_cases hw : w.val < 2 * n + gs.length
      · simp only [hw, dite_true, hwireE ⟨w.val, hw⟩ x y]
        exact (wireVal_append_old gs ⟨op, []⟩ w.val hw x y).symm
      · have heq : w.val = 2 * n + gs.length := by
          have := w.isLt; simp only [List.length_append, List.length_singleton] at this; omega
        simp only [hw, dite_false, AffExpr.eval_const]; rw [heq, hc_val x y]
    | cons a rest =>
      cases rest with
      | nil =>
        have hmul : isMulGate ⟨op, [a]⟩ = false := by simp [isMulGate]
        have hc : gateCost (gs ++ [⟨op, [a]⟩]) = gateCost gs := by rw [hcost_app, hmul]; simp
        have ha : a < 2 * n + gs.length := hread_g a List.mem_cons_self
        have hexpr : ∃ e : AffExpr n (gateCost gs),
            ∀ x y, e.eval x y (S.evalFull x y) = wireVal (gs ++ [⟨op, [a]⟩]) (2 * n + gs.length) x y := by
          rcases hop with rfl | rfl | rfl | ⟨rfl, _⟩
          · refine ⟨wireE ⟨a, ha⟩, fun x y => ?_⟩
            rw [wireVal_append_new, hwireE ⟨a, ha⟩ x y]
            simp [GateOp.eval, b2f_decide]
          · refine ⟨wireE ⟨a, ha⟩, fun x y => ?_⟩
            rw [wireVal_append_new, hwireE ⟨a, ha⟩ x y]
            simp [GateOp.eval, b2f_decide]
          · refine ⟨(wireE ⟨a, ha⟩).add1, fun x y => ?_⟩
            rw [wireVal_append_new, AffExpr.eval_add1, hwireE ⟨a, ha⟩ x y]
            rcases f_cases (wireVal gs a x y) with h | h <;> simp [h, GateOp.eval, b2f, f_add_self]
          · refine ⟨(wireE ⟨a, ha⟩).add1, fun x y => ?_⟩
            rw [wireVal_append_new, AffExpr.eval_add1, hwireE ⟨a, ha⟩ x y]
            simp [GateOp.eval, b2f_not, b2f_decide]
        obtain ⟨e, he⟩ := hexpr
        rw [hc]
        refine ⟨S, fun w => if hw : w.val < 2 * n + gs.length then wireE ⟨w.val, hw⟩ else e, ?_⟩
        intro w x y
        by_cases hw : w.val < 2 * n + gs.length
        · simp only [hw, dite_true, hwireE ⟨w.val, hw⟩ x y]
          exact (wireVal_append_old gs ⟨op, [a]⟩ w.val hw x y).symm
        · have heq : w.val = 2 * n + gs.length := by
            have := w.isLt; simp only [List.length_append, List.length_singleton] at this; omega
          simp only [hw, dite_false]; rw [heq]; exact he x y
      | cons b rest' =>
        have hnil : rest' = [] := List.length_eq_zero_iff.mp (by simp only [List.length_cons] at hlen_ins; omega)
        subst hnil
        have ha : a < 2 * n + gs.length := hread_g a List.mem_cons_self
        have hb : b < 2 * n + gs.length := hread_g b (List.mem_cons_of_mem a List.mem_cons_self)
        rcases hop with rfl | rfl | rfl | ⟨rfl, h1⟩
        · have hmul : isMulGate ⟨.and, [a, b]⟩ = true := by simp [isMulGate]
          have hc : gateCost (gs ++ [⟨.and, [a, b]⟩]) = gateCost gs + 1 := by
            rw [hcost_app, hmul]; simp
          rw [hc]
          let S' := S.snoc (wireE ⟨a, ha⟩) (wireE ⟨b, hb⟩)
          refine ⟨S', fun w =>
            if hw : w.val < 2 * n + gs.length then (wireE ⟨w.val, hw⟩).lift
            else AffExpr.varM (Fin.last (gateCost gs)), ?_⟩
          intro w x y
          have hS' : S'.evalFull x y =
              Fin.snoc (S.evalFull x y) (wireVal gs a x y * wireVal gs b x y) := by
            rw [SLP.evalFull_snoc, hwireE ⟨a, ha⟩ x y, hwireE ⟨b, hb⟩ x y]
          by_cases hw : w.val < 2 * n + gs.length
          · simp only [hw, dite_true, AffExpr.eval_lift, hS', Fin.snoc_castSucc, hwireE ⟨w.val, hw⟩ x y]
            exact (wireVal_append_old gs ⟨.and, [a, b]⟩ w.val hw x y).symm
          · have heq : w.val = 2 * n + gs.length := by
              have := w.isLt; simp only [List.length_append, List.length_singleton] at this; omega
            simp only [hw, dite_false, AffExpr.eval_varM, hS', Fin.snoc_last]
            rw [heq, wireVal_append_new]
            simp only [List.map_cons, List.map_nil, GateOp.eval, List.all_cons, List.all_nil, id_eq,
              Bool.and_true, b2f_and, b2f_decide]
        · have hmul : isMulGate ⟨.or, [a, b]⟩ = true := by simp [isMulGate]
          have hc : gateCost (gs ++ [⟨.or, [a, b]⟩]) = gateCost gs + 1 := by
            rw [hcost_app, hmul]; simp
          rw [hc]
          let S' := S.snoc (wireE ⟨a, ha⟩) (wireE ⟨b, hb⟩)
          refine ⟨S', fun w =>
            if hw : w.val < 2 * n + gs.length then (wireE ⟨w.val, hw⟩).lift
            else ((wireE ⟨a, ha⟩).lift.add (wireE ⟨b, hb⟩).lift).add (AffExpr.varM (Fin.last (gateCost gs))), ?_⟩
          intro w x y
          have hS' : S'.evalFull x y =
              Fin.snoc (S.evalFull x y) (wireVal gs a x y * wireVal gs b x y) := by
            rw [SLP.evalFull_snoc, hwireE ⟨a, ha⟩ x y, hwireE ⟨b, hb⟩ x y]
          by_cases hw : w.val < 2 * n + gs.length
          · simp only [hw, dite_true, AffExpr.eval_lift, hS', Fin.snoc_castSucc, hwireE ⟨w.val, hw⟩ x y]
            exact (wireVal_append_old gs ⟨.or, [a, b]⟩ w.val hw x y).symm
          · have heq : w.val = 2 * n + gs.length := by
              have := w.isLt; simp only [List.length_append, List.length_singleton] at this; omega
            simp only [hw, dite_false, AffExpr.eval_add, AffExpr.eval_lift, AffExpr.eval_varM, hS',
              Fin.snoc_castSucc, Fin.snoc_last, hwireE ⟨a, ha⟩ x y, hwireE ⟨b, hb⟩ x y]
            rw [heq, wireVal_append_new]
            simp only [List.map_cons, List.map_nil, b2f_or_pair, b2f_decide]
        · have hmul : isMulGate ⟨.mod 2, [a, b]⟩ = false := by simp [isMulGate]
          have hc : gateCost (gs ++ [⟨.mod 2, [a, b]⟩]) = gateCost gs := by
            rw [hcost_app, hmul]; simp
          rw [hc]
          refine ⟨S, fun w =>
            if hw : w.val < 2 * n + gs.length then wireE ⟨w.val, hw⟩
            else ((wireE ⟨a, ha⟩).add (wireE ⟨b, hb⟩)).add1, ?_⟩
          intro w x y
          by_cases hw : w.val < 2 * n + gs.length
          · simp only [hw, dite_true, hwireE ⟨w.val, hw⟩ x y]
            exact (wireVal_append_old gs ⟨.mod 2, [a, b]⟩ w.val hw x y).symm
          · have heq : w.val = 2 * n + gs.length := by
              have := w.isLt; simp only [List.length_append, List.length_singleton] at this; omega
            simp only [hw, dite_false, AffExpr.eval_add1, AffExpr.eval_add,
              hwireE ⟨a, ha⟩ x y, hwireE ⟨b, hb⟩ x y]
            rw [heq, wireVal_append_new]
            simp only [List.map_cons, List.map_nil, b2f_mod2_pair, b2f_decide]
        · simp at h1

structure YAffExpr (n m : ℕ) where
  c0 : F
  ly : V n
  lp : Fin m → F

def YAffExpr.eval {n m : ℕ} (e : YAffExpr n m) (y : V n) (P : Fin m → F) : F :=
  e.c0 + dotProduct e.ly y + ∑ j : Fin m, e.lp j * P j

def YAffExpr.add {n m : ℕ} (e₁ e₂ : YAffExpr n m) : YAffExpr n m :=
  ⟨e₁.c0 + e₂.c0, e₁.ly + e₂.ly, e₁.lp + e₂.lp⟩

def YAffExpr.smul {n m : ℕ} (r : F) (e : YAffExpr n m) : YAffExpr n m :=
  ⟨r * e.c0, r • e.ly, r • e.lp⟩

def YAffExpr.lift {n m : ℕ} (e : YAffExpr n m) : YAffExpr n (m + 1) :=
  ⟨e.c0, e.ly, Fin.snoc e.lp 0⟩

lemma YAffExpr.eval_add {n m : ℕ} (e₁ e₂ : YAffExpr n m) (y : V n) (P : Fin m → F) :
    (e₁.add e₂).eval y P = e₁.eval y P + e₂.eval y P := by
  simp only [YAffExpr.eval, YAffExpr.add, add_dotProduct, Pi.add_apply, add_mul,
    Finset.sum_add_distrib]
  ring

lemma YAffExpr.eval_smul {n m : ℕ} (r : F) (e : YAffExpr n m) (y : V n) (P : Fin m → F) :
    (e.smul r).eval y P = r * e.eval y P := by
  simp only [YAffExpr.eval, YAffExpr.smul, smul_dotProduct, smul_eq_mul, Pi.smul_apply,
    mul_add, Finset.mul_sum]
  congr 1; apply Finset.sum_congr rfl; intro j _; ring

lemma YAffExpr.eval_lift {n m : ℕ} (e : YAffExpr n m) (y : V n) (P : Fin (m + 1) → F) :
    e.lift.eval y P = e.eval y (fun j => P j.castSucc) := by
  simp only [YAffExpr.eval, YAffExpr.lift, Fin.sum_univ_castSucc, Fin.snoc_castSucc, Fin.snoc_last,
    zero_mul, add_zero]

structure YSLP (n m : ℕ) where
  a : ∀ i : Fin m, YAffExpr n i.val
  b : ∀ i : Fin m, YAffExpr n i.val

def YSLP.evalP {n m : ℕ} (Y : YSLP n m) (y : V n) : (k : ℕ) → (hk : k ≤ m) → Fin k → F
  | 0, _, i => i.elim0
  | k + 1, hk, i =>
    let prev := Y.evalP y k (by omega)
    let cur := (Y.a ⟨k, by omega⟩).eval y prev * (Y.b ⟨k, by omega⟩).eval y prev
    Fin.snoc (α := fun _ => F) prev cur i

def YSLP.evalFull {n m : ℕ} (Y : YSLP n m) (y : V n) : Fin m → F :=
  Y.evalP y m le_rfl

def YSLP.snoc {n m : ℕ} (Y : YSLP n m) (a' b' : YAffExpr n m) : YSLP n (m + 1) where
  a i := if h : i.val < m then Y.a ⟨i.val, h⟩ else
    cast (congrArg (YAffExpr n) (show m = i.val by omega)) a'
  b i := if h : i.val < m then Y.b ⟨i.val, h⟩ else
    cast (congrArg (YAffExpr n) (show m = i.val by omega)) b'

lemma YSLP.evalP_snoc_le {n m : ℕ} (Y : YSLP n m) (a' b' : YAffExpr n m) (y : V n) :
    ∀ (k : ℕ) (hk : k ≤ m), (Y.snoc a' b').evalP y k (by omega) = Y.evalP y k hk := by
  intro k hk
  induction k with
  | zero => funext i; exact i.elim0
  | succ k ih =>
    funext i
    rw [YSLP.evalP, YSLP.evalP, ih (by omega)]
    have hlt : k < m := by omega
    simp only [YSLP.snoc, Fin.val_mk, hlt, dite_true]

lemma YSLP.evalFull_snoc {n m : ℕ} (Y : YSLP n m) (a' b' : YAffExpr n m) (y : V n) :
    (Y.snoc a' b').evalFull y =
      Fin.snoc (α := fun _ => F) (Y.evalFull y) (a'.eval y (Y.evalFull y) * b'.eval y (Y.evalFull y)) := by
  funext i
  rw [YSLP.evalFull, YSLP.evalP, YSLP.evalP_snoc_le Y a' b' y m le_rfl]
  simp only [YSLP.snoc, Fin.val_mk, Nat.lt_irrefl, dite_false, cast_eq]; rfl

def substX {n k r : ℕ} (e : AffExpr n k) (sub : Fin n → YAffExpr n r)
    (mapM : Fin k → Option (Fin r)) : YAffExpr n r where
  c0 := e.c0 + ∑ i : Fin n, e.lx i * (sub i).c0
  ly := e.ly + ∑ i : Fin n, e.lx i • (sub i).ly
  lp := (∑ i : Fin n, e.lx i • (sub i).lp) +
    ∑ j : Fin k, match mapM j with
      | some idx => e.lm j • Pi.single idx 1
      | none => 0

lemma substX_eval {n k r : ℕ} (e : AffExpr n k) (sub : Fin n → YAffExpr n r)
    (mapM : Fin k → Option (Fin r)) (w y : V n) (P : Fin r → F) (mvals : Fin k → F)
    (hm : ∀ j : Fin k, mvals j = match mapM j with | some idx => P idx | none => 0) :
    e.eval (w + fun i => (sub i).eval y P) y mvals =
      dotProduct e.lx w + (substX e sub mapM).eval y P := by
  simp only [AffExpr.eval, dotProduct_add]
  have hsub : (substX e sub mapM).eval y P =
      (e.c0 + ∑ i : Fin n, e.lx i * (sub i).c0) +
      (dotProduct e.ly y + dotProduct (∑ i : Fin n, e.lx i • (sub i).ly) y) +
      (∑ t : Fin r, ((∑ i : Fin n, e.lx i • (sub i).lp) +
        ∑ j : Fin k, match mapM j with | some idx => e.lm j • Pi.single idx (1 : F) | none => 0) t * P t) := by
    simp only [substX, YAffExpr.eval, add_dotProduct]
  rw [hsub]
  have h1 : dotProduct e.lx (fun i => (sub i).eval y P) =
      (∑ i : Fin n, e.lx i * (sub i).c0) +
      dotProduct (∑ i : Fin n, e.lx i • (sub i).ly) y +
      ∑ t : Fin r, (∑ i : Fin n, e.lx i • (sub i).lp) t * P t := by
    simp only [dotProduct, YAffExpr.eval, mul_add, Finset.sum_add_distrib, Finset.sum_apply,
      Pi.smul_apply, smul_eq_mul, Finset.sum_mul, Finset.mul_sum]
    congr 1
    · congr 1
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl; intro j _
      apply Finset.sum_congr rfl; intro i _; ring
    · rw [Finset.sum_comm]
      apply Finset.sum_congr rfl; intro t _
      apply Finset.sum_congr rfl; intro i _; ring
  have h2 : (∑ j : Fin k, e.lm j * mvals j) =
      ∑ t : Fin r, (∑ j : Fin k, (match mapM j with
        | some idx => e.lm j • Pi.single idx (1 : F)
        | none => 0) t) * P t := by
    simp_rw [Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro j _
    rw [hm j]
    cases mapM j with
    | none => simp
    | some idx =>
      simp only [Pi.smul_apply, smul_eq_mul, Pi.single_apply]
      rw [Finset.sum_eq_single idx]
      · simp
      · intro t _ ht; simp [ht]
      · intro h; exact (h (Finset.mem_univ idx)).elim
  have h3 : (∑ t : Fin r, ((∑ i : Fin n, e.lx i • (sub i).lp) +
        ∑ j : Fin k, match mapM j with | some idx => e.lm j • Pi.single idx (1 : F) | none => 0) t * P t) =
      (∑ t : Fin r, (∑ i : Fin n, e.lx i • (sub i).lp) t * P t) +
      (∑ t : Fin r, (∑ j : Fin k, (match mapM j with
        | some idx => e.lm j • Pi.single idx (1 : F)
        | none => 0) t) * P t) := by
    simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib, Finset.sum_apply]
  rw [h1, h2, h3]; ring

lemma finrank_inf_ker_dot {n : ℕ} (W : Submodule F (V n)) (lx : V n) (e : V n)
    (heW : e ∈ W) (he1 : dotProduct lx e = 1) :
    let l : V n →ₗ[F] F :=
      { toFun := fun w => dotProduct lx w
        map_add' := fun u v => dotProduct_add lx u v
        map_smul' := fun r u => by simp [dotProduct_smul] }
    Module.finrank F (W ⊓ LinearMap.ker l : Submodule F (V n)) + 1 = Module.finrank F W := by
  intro l
  have hr := LinearMap.finrank_range_add_finrank_ker (l.domRestrict W)
  have htop : LinearMap.range (l.domRestrict W) = ⊤ := by
    rw [Submodule.eq_top_iff']
    intro r
    rcases f_cases r with rfl | rfl
    · exact ⟨0, map_zero _⟩
    · exact ⟨⟨e, heW⟩, he1⟩
  have hker : Module.finrank F (LinearMap.ker (l.domRestrict W)) =
      Module.finrank F (W ⊓ LinearMap.ker l : Submodule F (V n)) := by
    let eqv : LinearMap.ker (l.domRestrict W) ≃ₗ[F] (W ⊓ LinearMap.ker l : Submodule F (V n)) :=
      { toFun := fun ⟨⟨w, hw⟩, hlw⟩ => ⟨w, ⟨hw, hlw⟩⟩
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl
        invFun := fun ⟨w, ⟨hw, hlw⟩⟩ => ⟨⟨w, hw⟩, hlw⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    exact eqv.finrank_eq
  rw [htop, finrank_top, Module.finrank_self, hker] at hr
  omega

lemma elim_x_from_slp {n s : ℕ} (S : SLP n s) (out : AffExpr n s) (g : V n → F)
    (heval : ∀ x y : V n, out.eval x y (S.evalFull x y) = dotProduct x y + g y) :
    ∃ (r : ℕ) (hr : r + n ≤ s) (Y : YSLP n r) (q₀ : V n → F) (ℓ : Fin r → V n) (β : Fin r → F),
      quad q₀ ∧
      ∀ y : V n, g y = q₀ y + ∑ i : Fin r, (dotProduct (ℓ i) y + β i) * Y.evalFull y i := by
  have hstep : ∀ (k : ℕ) (hk : k ≤ s),
      ∃ (W : Submodule F (V n)) (r : ℕ) (Y : YSLP n r)
        (sub : Fin n → YAffExpr n r) (mapM : Fin k → Option (Fin r)),
        r + (n - Module.finrank F W) ≤ k ∧
        ∀ w ∈ W, ∀ y : V n, ∀ j : Fin k,
          S.evalM (w + fun i => (sub i).eval y (Y.evalFull y)) y k hk j =
            match mapM j with | some idx => Y.evalFull y idx | none => 0 := by
    intro k hk
    induction k with
    | zero =>
      refine ⟨⊤, 0, ⟨fun i => i.elim0, fun i => i.elim0⟩, fun _ => ⟨0, 0, fun i => i.elim0⟩,
        fun j => j.elim0, ?_, fun _ _ _ j => j.elim0⟩
      rw [finrank_top, Module.finrank_fin_fun]; omega
    | succ k ih =>
      obtain ⟨W, r, Y, sub, mapM, hdim, hinv⟩ := ih (by omega)
      have hW_le : Module.finrank F W ≤ n := by
        have := Submodule.finrank_le W; simpa [Module.finrank_fin_fun] using this
      let uk := S.u ⟨k, by omega⟩
      let vk := S.v ⟨k, by omega⟩
      let yu := substX uk sub mapM
      let yv := substX vk sub mapM
      by_cases hu0 : ∀ w ∈ W, dotProduct uk.lx w = 0
      · by_cases hv0 : ∀ w ∈ W, dotProduct vk.lx w = 0
        · let Y' := Y.snoc yu yv
          let sub' : Fin n → YAffExpr n (r + 1) := fun i => (sub i).lift
          let mapM' : Fin (k + 1) → Option (Fin (r + 1)) :=
            Fin.snoc (fun j => (mapM j).map Fin.castSucc) (some (Fin.last r))
          refine ⟨W, r + 1, Y', sub', mapM', by omega, ?_⟩
          intro w hw y j
          have hsub_eq : (fun i => (sub' i).eval y (Y'.evalFull y)) =
              (fun i => (sub i).eval y (Y.evalFull y)) := by
            funext i
            simp only [sub', YAffExpr.eval_lift, Y', YSLP.evalFull_snoc, Fin.snoc_castSucc]
          rw [hsub_eq]
          simp only [SLP.evalM]
          refine Fin.lastCases ?_ ?_ j
          · simp only [Fin.snoc_last, mapM', Y', YSLP.evalFull_snoc]
            have h1 := substX_eval uk sub mapM w y (Y.evalFull y)
              (S.evalM (w + fun i => (sub i).eval y (Y.evalFull y)) y k (by omega))
              (hinv w hw y)
            have h2 := substX_eval vk sub mapM w y (Y.evalFull y)
              (S.evalM (w + fun i => (sub i).eval y (Y.evalFull y)) y k (by omega))
              (hinv w hw y)
            rw [h1, h2, hu0 w hw, hv0 w hw, zero_add, zero_add]
          · intro j'
            simp only [Fin.snoc_castSucc, mapM']
            rw [hinv w hw y j']
            cases mapM j' with
            | none => rfl
            | some idx => simp [Y', YSLP.evalFull_snoc]
        · push Not at hv0
          obtain ⟨e, heW, hene⟩ := hv0
          have he1 : dotProduct vk.lx e = 1 := (f_cases _).resolve_left hene
          let l : V n →ₗ[F] F :=
            { toFun := fun w => dotProduct vk.lx w
              map_add' := fun a b => dotProduct_add vk.lx a b
              map_smul' := fun r' a => by simp [dotProduct_smul] }
          let W' : Submodule F (V n) := W ⊓ LinearMap.ker l
          have hW'_dim : Module.finrank F W' + 1 = Module.finrank F W :=
            finrank_inf_ker_dot W vk.lx e heW he1
          let sub' : Fin n → YAffExpr n r := fun i => (sub i).add (yv.smul (e i))
          let mapM' : Fin (k + 1) → Option (Fin r) := Fin.snoc mapM none
          refine ⟨W', r, Y, sub', mapM', by omega, ?_⟩
          intro w' hw' y j
          have hshift : w' + (fun i => (sub' i).eval y (Y.evalFull y)) =
              (w' + yv.eval y (Y.evalFull y) • e) + (fun i => (sub i).eval y (Y.evalFull y)) := by
            funext i
            simp only [sub', Pi.add_apply, Pi.smul_apply, smul_eq_mul, YAffExpr.eval_add,
              YAffExpr.eval_smul]
            ring
          have hw_mem : w' + yv.eval y (Y.evalFull y) • e ∈ W :=
            W.add_mem hw'.1 (W.smul_mem _ heW)
          rw [hshift]
          simp only [SLP.evalM]
          refine Fin.lastCases ?_ ?_ j
          · simp only [Fin.snoc_last, mapM']
            have h2 := substX_eval vk sub mapM (w' + yv.eval y (Y.evalFull y) • e) y (Y.evalFull y)
              (S.evalM ((w' + yv.eval y (Y.evalFull y) • e) + fun i => (sub i).eval y (Y.evalFull y)) y k (by omega))
              (hinv _ hw_mem y)
            rw [h2, dotProduct_add, dotProduct_smul, smul_eq_mul, he1, mul_one]
            have hlw' : dotProduct vk.lx w' = 0 := hw'.2
            rw [hlw', zero_add, f_add_self, mul_zero]
          · intro j'
            simp only [Fin.snoc_castSucc, mapM']
            exact hinv _ hw_mem y j'
      · push Not at hu0
        obtain ⟨e, heW, hene⟩ := hu0
        have he1 : dotProduct uk.lx e = 1 := (f_cases _).resolve_left hene
        let l : V n →ₗ[F] F :=
          { toFun := fun w => dotProduct uk.lx w
            map_add' := fun a b => dotProduct_add uk.lx a b
            map_smul' := fun r' a => by simp [dotProduct_smul] }
        let W' : Submodule F (V n) := W ⊓ LinearMap.ker l
        have hW'_dim : Module.finrank F W' + 1 = Module.finrank F W :=
          finrank_inf_ker_dot W uk.lx e heW he1
        let sub' : Fin n → YAffExpr n r := fun i => (sub i).add (yu.smul (e i))
        let mapM' : Fin (k + 1) → Option (Fin r) := Fin.snoc mapM none
        refine ⟨W', r, Y, sub', mapM', by omega, ?_⟩
        intro w' hw' y j
        have hshift : w' + (fun i => (sub' i).eval y (Y.evalFull y)) =
            (w' + yu.eval y (Y.evalFull y) • e) + (fun i => (sub i).eval y (Y.evalFull y)) := by
          funext i
          simp only [sub', Pi.add_apply, Pi.smul_apply, smul_eq_mul, YAffExpr.eval_add,
            YAffExpr.eval_smul]
          ring
        have hw_mem : w' + yu.eval y (Y.evalFull y) • e ∈ W :=
          W.add_mem hw'.1 (W.smul_mem _ heW)
        rw [hshift]
        simp only [SLP.evalM]
        refine Fin.lastCases ?_ ?_ j
        · simp only [Fin.snoc_last, mapM']
          have h1 := substX_eval uk sub mapM (w' + yu.eval y (Y.evalFull y) • e) y (Y.evalFull y)
            (S.evalM ((w' + yu.eval y (Y.evalFull y) • e) + fun i => (sub i).eval y (Y.evalFull y)) y k (by omega))
            (hinv _ hw_mem y)
          rw [h1, dotProduct_add, dotProduct_smul, smul_eq_mul, he1, mul_one]
          have hlw' : dotProduct uk.lx w' = 0 := hw'.2
          rw [hlw', zero_add, f_add_self, zero_mul]
        · intro j'
          simp only [Fin.snoc_castSucc, mapM']
          exact hinv _ hw_mem y j'
  obtain ⟨W, r, Y, sub, mapM, hdim, hinv⟩ := hstep s le_rfl
  let yout := substX out sub mapM
  have hmain : ∀ w ∈ W, ∀ y : V n,
      dotProduct w y + dotProduct (fun i => (sub i).eval y (Y.evalFull y)) y + g y =
        dotProduct out.lx w + yout.eval y (Y.evalFull y) := by
    intro w hw y
    have h1 := substX_eval out sub mapM w y (Y.evalFull y)
      (S.evalFull (w + fun i => (sub i).eval y (Y.evalFull y)) y) (hinv w hw y)
    have h2 := heval (w + fun i => (sub i).eval y (Y.evalFull y)) y
    rw [h1, add_dotProduct] at h2
    exact h2.symm
  have hW_bot : W = ⊥ := by
    rw [eq_bot_iff]
    intro w hw
    have h0 := hmain 0 W.zero_mem
    have hw_eq : ∀ y : V n, dotProduct w y = dotProduct out.lx w := by
      intro y
      have ha := hmain w hw y
      have hb := h0 y
      simp only [zero_dotProduct, dotProduct_zero, zero_add] at hb
      rw [add_assoc, hb] at ha
      have ha' := congrArg (· + yout.eval y (Y.evalFull y)) ha
      have hsimp : dotProduct w y + yout.eval y (Y.evalFull y) + yout.eval y (Y.evalFull y) =
          dotProduct w y + (yout.eval y (Y.evalFull y) + yout.eval y (Y.evalFull y)) := by ring
      have hsimp2 : dotProduct out.lx w + yout.eval y (Y.evalFull y) + yout.eval y (Y.evalFull y) =
          dotProduct out.lx w + (yout.eval y (Y.evalFull y) + yout.eval y (Y.evalFull y)) := by ring
      rw [hsimp, hsimp2, f_add_self, add_zero, add_zero] at ha'
      exact ha'
    have hlx0 : dotProduct out.lx w = 0 := by
      have := hw_eq 0; simpa using this.symm
    funext i
    have hi := hw_eq (unit i)
    rw [hlx0] at hi
    simp only [dotProduct, unit] at hi
    rw [Finset.sum_eq_single i] at hi
    · simpa using hi
    · intro j _ hji; simp [Ne.symm hji]
    · intro h; exact (h (Finset.mem_univ i)).elim
  have hrn : r + n ≤ s := by
    rw [hW_bot, finrank_bot, Nat.sub_zero] at hdim
    exact hdim
  let q₀ : V n → F := fun y =>
    yout.c0 + dotProduct (yout.ly + fun i => (sub i).c0) y +
      ∑ i : Fin n, ∑ j : Fin n, (sub i).ly j * y j * y i
  have hq₀ : quad q₀ := ⟨yout.c0, yout.ly + fun i => (sub i).c0, fun i j => (sub j).ly i, fun y => by
    simp only [q₀]
    congr 1
    rw [Finset.sum_comm]⟩
  refine ⟨r, hrn, Y, q₀, fun t i => (sub i).lp t, yout.lp, hq₀, ?_⟩
  intro y
  have h0 := hmain 0 W.zero_mem y
  simp only [zero_dotProduct, dotProduct_zero, zero_add] at h0
  have h0' := congrArg (· + dotProduct (fun i => (sub i).eval y (Y.evalFull y)) y) h0
  have hL : dotProduct (fun i => (sub i).eval y (Y.evalFull y)) y + g y +
      dotProduct (fun i => (sub i).eval y (Y.evalFull y)) y =
      g y + (dotProduct (fun i => (sub i).eval y (Y.evalFull y)) y +
        dotProduct (fun i => (sub i).eval y (Y.evalFull y)) y) := by ring
  rw [hL, f_add_self, add_zero] at h0'
  rw [h0']
  simp only [q₀, YAffExpr.eval, dotProduct, Pi.add_apply, add_mul,
    Finset.sum_add_distrib, Finset.sum_mul]
  have hswap : (∑ i : Fin n, ∑ t : Fin r, (sub i).lp t * Y.evalFull y t * y i) =
      ∑ t : Fin r, ∑ i : Fin n, (sub i).lp t * y i * Y.evalFull y t := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro t _
    apply Finset.sum_congr rfl; intro i _; ring
  rw [hswap]; ring

def diffG {U : Type*} [AddCommGroup U] (f : U → F) (a x : U) : F :=
  f (x + a) + f x

def isAffG {U : Type*} [AddCommGroup U] (f : U → F) : Prop :=
  ∀ a b x : U, diffG (diffG f a) b x = 0

def isQuadG {U : Type*} [AddCommGroup U] (f : U → F) : Prop :=
  ∀ a b c x : U, diffG (diffG (diffG f a) b) c x = 0

def isCubG {U : Type*} [AddCommGroup U] (f : U → F) : Prop :=
  ∀ a b c d x : U, diffG (diffG (diffG (diffG f a) b) c) d x = 0

lemma diffG_add_fun {U : Type*} [AddCommGroup U] (f₁ f₂ : U → F) (a x : U) :
    diffG (fun y => f₁ y + f₂ y) a x = diffG f₁ a x + diffG f₂ a x := by
  simp only [diffG]; ring

lemma diffG_const {U : Type*} [AddCommGroup U] (c : F) (a x : U) :
    diffG (fun _ => c) a x = 0 := by
  simp [diffG, f_add_self]

lemma isAffG_const {U : Type*} [AddCommGroup U] (c : F) : isAffG (fun _ : U => c) := by
  intro a b x
  have h1 : diffG (fun _ : U => c) a = fun _ => 0 := funext (diffG_const c a)
  rw [h1, diffG_const]

lemma isAffG_add {U : Type*} [AddCommGroup U] {f₁ f₂ : U → F}
    (h₁ : isAffG f₁) (h₂ : isAffG f₂) : isAffG (fun y => f₁ y + f₂ y) := by
  intro a b x
  have h : diffG (fun y => f₁ y + f₂ y) a = fun y => diffG f₁ a y + diffG f₂ a y :=
    funext (diffG_add_fun f₁ f₂ a)
  rw [h, diffG_add_fun, h₁ a b x, h₂ a b x, add_zero]

lemma isQuadG_add {U : Type*} [AddCommGroup U] {f₁ f₂ : U → F}
    (h₁ : isQuadG f₁) (h₂ : isQuadG f₂) : isQuadG (fun y => f₁ y + f₂ y) := by
  intro a b c x
  have h1 : diffG (fun y => f₁ y + f₂ y) a = fun y => diffG f₁ a y + diffG f₂ a y :=
    funext (diffG_add_fun f₁ f₂ a)
  rw [h1]
  have h2 : diffG (fun y => diffG f₁ a y + diffG f₂ a y) b =
      fun y => diffG (diffG f₁ a) b y + diffG (diffG f₂ a) b y :=
    funext (diffG_add_fun _ _ b)
  rw [h2, diffG_add_fun, h₁ a b c x, h₂ a b c x, add_zero]

lemma isCubG_add {U : Type*} [AddCommGroup U] {f₁ f₂ : U → F}
    (h₁ : isCubG f₁) (h₂ : isCubG f₂) : isCubG (fun y => f₁ y + f₂ y) := by
  intro a b c d x
  have h1 : diffG (fun y => f₁ y + f₂ y) a = fun y => diffG f₁ a y + diffG f₂ a y :=
    funext (diffG_add_fun f₁ f₂ a)
  rw [h1]
  have h2 : diffG (fun y => diffG f₁ a y + diffG f₂ a y) b =
      fun y => diffG (diffG f₁ a) b y + diffG (diffG f₂ a) b y :=
    funext (diffG_add_fun _ _ b)
  rw [h2]
  have h3 : diffG (fun y => diffG (diffG f₁ a) b y + diffG (diffG f₂ a) b y) c =
      fun y => diffG (diffG (diffG f₁ a) b) c y + diffG (diffG (diffG f₂ a) b) c y :=
    funext (diffG_add_fun _ _ c)
  rw [h3, diffG_add_fun, h₁ a b c d x, h₂ a b c d x, add_zero]

lemma isAffG_of_linear {U : Type*} [AddCommGroup U] [Module F U] (l : U →ₗ[F] F) :
    isAffG l := by
  intro a b x
  have h1 : diffG l a = fun _ => l a := by
    funext y
    simp only [diffG, map_add]
    have : l y + l a + l y = l a + (l y + l y) := by ring
    rw [this, f_add_self, add_zero]
  rw [h1, diffG_const]

lemma isAffG_exists_linear {U : Type*} [AddCommGroup U] [Module F U] {f : U → F} (hf : isAffG f) :
    ∃ (c : F) (l : U →ₗ[F] F), ∀ x : U, f x = c + l x := by
  refine ⟨f 0,
    { toFun := fun x => f x + f 0
      map_add' := fun a b => by
        have h := hf a b 0
        simp only [diffG, zero_add] at h
        have h' := congrArg (· + (f a + f 0 + (f b + f 0))) h
        have hl : f (b + a) + f b + (f a + f 0) + (f a + f 0 + (f b + f 0)) =
            (f (a + b) + f 0) + ((f b + f b) + (f a + f a) + (f 0 + f 0)) := by
          rw [add_comm b a]; ring
        rw [hl] at h'; simp only [f_add_self, add_zero, zero_add] at h'
        exact h'
      map_smul' := fun r x => by
        rcases f_cases r with rfl | rfl
        · simp [f_add_self]
        · simp }, ?_⟩
  intro x
  change f x = f 0 + (f x + f 0)
  have : f 0 + (f x + f 0) = f x + (f 0 + f 0) := by ring
  rw [this, f_add_self, add_zero]

lemma isQuadG_of_isAffG {U : Type*} [AddCommGroup U] {f : U → F} (h : isAffG f) :
    isQuadG f := by
  intro a b c x
  have h1 : diffG (diffG f a) b = fun _ => 0 := funext (h a b)
  rw [h1, diffG_const]

lemma isCubG_of_isQuadG {U : Type*} [AddCommGroup U] {f : U → F} (h : isQuadG f) :
    isCubG f := by
  intro a b c d x
  have h1 : diffG (diffG (diffG f a) b) c = fun _ => 0 := funext (h a b c)
  rw [h1, diffG_const]

lemma isQuadG_mul_aff {U : Type*} [AddCommGroup U] [Module F U] {f₁ f₂ : U → F}
    (h₁ : isAffG f₁) (h₂ : isAffG f₂) : isQuadG (fun y => f₁ y * f₂ y) := by
  obtain ⟨c₁, l₁, hf₁⟩ := isAffG_exists_linear h₁
  obtain ⟨c₂, l₂, hf₂⟩ := isAffG_exists_linear h₂
  have hfun : (fun y => f₁ y * f₂ y) = fun y => (c₁ * c₂ + c₁ * l₂ y + c₂ * l₁ y) + l₁ y * l₂ y := by
    funext y; rw [hf₁ y, hf₂ y]; ring
  rw [hfun]
  apply isQuadG_add
  · apply isQuadG_of_isAffG
    have hsm : ∀ (r : F) (l : U →ₗ[F] F), isAffG (fun y => r * l y) := fun r l => by
      have : (fun y => r * l y) = (r • l) := rfl
      rw [this]; exact isAffG_of_linear (r • l)
    exact isAffG_add (isAffG_add (isAffG_const _) (hsm c₁ l₂)) (hsm c₂ l₁)
  · intro a b c x
    have hs1 : diffG (fun y => l₁ y * l₂ y) a = fun y => l₁ a * l₂ y + l₁ y * l₂ a + l₁ a * l₂ a := by
      funext y; simp only [diffG, map_add]
      have : (l₁ y + l₁ a) * (l₂ y + l₂ a) + l₁ y * l₂ y =
          (l₁ y * l₂ y + l₁ y * l₂ y) + (l₁ a * l₂ y + l₁ y * l₂ a + l₁ a * l₂ a) := by ring
      rw [this, f_add_self, zero_add]
    have hs2 : diffG (diffG (fun y => l₁ y * l₂ y) a) b = fun _ => l₁ a * l₂ b + l₁ b * l₂ a := by
      funext y; rw [hs1]; simp only [diffG, map_add]
      have : (l₁ a * (l₂ y + l₂ b) + (l₁ y + l₁ b) * l₂ a + l₁ a * l₂ a) +
          (l₁ a * l₂ y + l₁ y * l₂ a + l₁ a * l₂ a) =
          (l₁ a * l₂ y + l₁ a * l₂ y) + (l₁ y * l₂ a + l₁ y * l₂ a) +
          (l₁ a * l₂ a + l₁ a * l₂ a) + (l₁ a * l₂ b + l₁ b * l₂ a) := by ring
      rw [this]; simp only [f_add_self, zero_add]
    rw [hs2, diffG_const]

lemma isCubG_mul_aff_quad {U : Type*} [AddCommGroup U] [Module F U] {f₁ f₂ f₃ : U → F}
    (h₁ : isAffG f₁) (h₂ : isAffG f₂) (h₃ : isAffG f₃) :
    isCubG (fun y => f₁ y * (f₂ y * f₃ y)) := by
  obtain ⟨c₁, l₁, hf₁⟩ := isAffG_exists_linear h₁
  have hfun : (fun y => f₁ y * (f₂ y * f₃ y)) =
      fun y => (if c₁ = 1 then f₂ y * f₃ y else 0) + l₁ y * (f₂ y * f₃ y) := by
    funext y; rw [hf₁ y]; rcases f_cases c₁ with rfl | rfl <;> simp [add_mul]
  rw [hfun]
  apply isCubG_add
  · apply isCubG_of_isQuadG
    rcases f_cases c₁ with rfl | rfl
    · simp only [zero_ne_one, ite_false]; exact isQuadG_of_isAffG (isAffG_const 0)
    · simp only [ite_true]; exact isQuadG_mul_aff h₂ h₃
  · obtain ⟨c₂, l₂, hf₂⟩ := isAffG_exists_linear h₂
    obtain ⟨c₃, l₃, hf₃⟩ := isAffG_exists_linear h₃
    have hfun2 : (fun y => l₁ y * (f₂ y * f₃ y)) =
        fun y => (l₁ y * (c₂ * c₃ + c₂ * l₃ y + c₃ * l₂ y)) + l₁ y * l₂ y * l₃ y := by
      funext y; rw [hf₂ y, hf₃ y]; ring
    rw [hfun2]
    apply isCubG_add
    · apply isCubG_of_isQuadG
      apply isQuadG_mul_aff (isAffG_of_linear l₁)
      have hsm : ∀ (r : F) (l : U →ₗ[F] F), isAffG (fun y => r * l y) := fun r l => by
        have : (fun y => r * l y) = (r • l) := rfl
        rw [this]; exact isAffG_of_linear (r • l)
      exact isAffG_add (isAffG_add (isAffG_const _) (hsm c₂ l₃)) (hsm c₃ l₂)
    · intro a b c d x
      have hs1 : diffG (fun y => l₁ y * l₂ y * l₃ y) a =
          fun y => l₁ a * (l₂ y * l₃ y) + l₂ a * (l₁ y * l₃ y) + l₃ a * (l₁ y * l₂ y) +
            (l₁ a * l₂ a * l₃ y + l₁ a * l₃ a * l₂ y + l₂ a * l₃ a * l₁ y + l₁ a * l₂ a * l₃ a) := by
        funext y; simp only [diffG, map_add]
        have h2' : (2 : F) = 0 := by decide
        ring_nf; simp [h2']
      have hs2 : diffG (diffG (fun y => l₁ y * l₂ y * l₃ y) a) b =
          fun y =>
            l₁ a * (l₂ b * l₃ y + l₂ y * l₃ b + l₂ b * l₃ b) +
            l₂ a * (l₁ b * l₃ y + l₁ y * l₃ b + l₁ b * l₃ b) +
            l₃ a * (l₁ b * l₂ y + l₁ y * l₂ b + l₁ b * l₂ b) +
            (l₁ a * l₂ a * l₃ b + l₁ a * l₃ a * l₂ b + l₂ a * l₃ a * l₁ b) := by
        funext y; rw [hs1]; simp only [diffG, map_add]
        have h2' : (2 : F) = 0 := by decide
        ring_nf; simp [h2']
      have hs3 : diffG (diffG (diffG (fun y => l₁ y * l₂ y * l₃ y) a) b) c =
          fun _ => det3 ![l₁ a, l₂ a, l₃ a] ![l₁ b, l₂ b, l₃ b] ![l₁ c, l₂ c, l₃ c] := by
        funext y; rw [hs2]
        simp only [diffG, map_add, det3, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two]
        have h2' : (2 : F) = 0 := by decide
        ring_nf; simp [h2']; ring
      rw [hs3, diffG_const]

lemma mul_aff_quad_factor {U : Type*} [AddCommGroup U] {A Q : U → F}
    (hA : isAffG A) (e : U) (he : A e ≠ A 0)
    (hAQ : isQuadG (fun y => A y * Q y)) :
    ∃ M : U → F, isAffG M ∧ ∀ x : U, A x * Q x = A x * M x := by
  have hshift : ∀ x : U, A (x + e) = A x + 1 := by
    intro x
    have hconst : diffG A e x = diffG A e 0 := by
      have h0 := hA e x 0
      rw [diffG, zero_add] at h0
      have h0' := congrArg (· + diffG A e 0) h0
      simp only [add_assoc, f_add_self, add_zero, zero_add] at h0'
      exact h0'
    have hd1 : diffG A e 0 = 1 := by
      rw [diffG, zero_add]
      rcases f_cases (A e) with h1 | h1 <;> rcases f_cases (A 0) with h2 | h2
      · exact (he (h1.trans h2.symm)).elim
      · rw [h1, h2]; decide
      · rw [h1, h2]; decide
      · exact (he (h1.trans h2.symm)).elim
    rw [hd1, diffG] at hconst
    have := congrArg (· + A x) hconst
    simp only [add_assoc, f_add_self, add_zero] at this
    rw [add_comm 1 (A x)] at this; exact this
  refine ⟨diffG (fun y => A y * Q y) e, fun a b x => hAQ e a b x, ?_⟩
  intro x
  rcases f_cases (A x) with hx | hx
  · simp [hx]
  · simp only [hx, one_mul, diffG, hshift x, f_add_self, zero_mul, zero_add]

lemma mul_aff_cubic_quad {U : Type*} [AddCommGroup U] {A P : U → F}
    (hA : isAffG A) (e : U) (he : A e ≠ A 0)
    (hAP : isCubG (fun y => A y * P y)) :
    ∃ M : U → F, isQuadG M ∧ ∀ x : U, A x * P x = A x * M x := by
  have hshift : ∀ x : U, A (x + e) = A x + 1 := by
    intro x
    have hconst : diffG A e x = diffG A e 0 := by
      have h0 := hA e x 0
      rw [diffG, zero_add] at h0
      have h0' := congrArg (· + diffG A e 0) h0
      simp only [add_assoc, f_add_self, add_zero, zero_add] at h0'
      exact h0'
    have hd1 : diffG A e 0 = 1 := by
      rw [diffG, zero_add]
      rcases f_cases (A e) with h1 | h1 <;> rcases f_cases (A 0) with h2 | h2
      · exact (he (h1.trans h2.symm)).elim
      · rw [h1, h2]; decide
      · rw [h1, h2]; decide
      · exact (he (h1.trans h2.symm)).elim
    rw [hd1, diffG] at hconst
    have := congrArg (· + A x) hconst
    simp only [add_assoc, f_add_self, add_zero] at this
    rw [add_comm 1 (A x)] at this; exact this
  refine ⟨diffG (fun y => A y * P y) e, fun a b c x => hAP e a b c x, ?_⟩
  intro x
  rcases f_cases (A x) with hx | hx
  · simp [hx]
  · simp only [hx, one_mul, diffG, hshift x, f_add_self, zero_mul, zero_add]

lemma quad_prod_linearize {U : Type*} [AddCommGroup U] [Module F U]
    {k : ℕ} (P : Fin k → U → F) (z₁ z₂ : U → F) (hz₁ : isAffG z₁) (hz₂ : isAffG z₂)
    (u v : Fin k → F)
    (hquad : isQuadG (fun h => (z₁ h + ∑ j : Fin k, u j * P j h) * (z₂ h + ∑ j : Fin k, v j * P j h)))
    (hshift :
      (∃ e₂ : U, (∀ h, z₁ (h + e₂) = z₁ h) ∧ (∀ h, z₂ (h + e₂) = z₂ h + 1) ∧ (∀ j h, P j (h + e₂) = P j h)) ∨
      (∃ e₁ : U, (∀ h, z₁ (h + e₁) = z₁ h + 1) ∧ (∀ h, z₂ (h + e₁) = z₂ h) ∧ (∀ j h, P j (h + e₁) = P j h)) ∨
      (∃ e₁₂ : U, (∀ h, z₁ (h + e₁₂) = z₁ h + 1) ∧ (∀ h, z₂ (h + e₁₂) = z₂ h + 1) ∧ (∀ j h, P j (h + e₁₂) = P j h))) :
    (∃ a' b' : U → F, isAffG a' ∧ isAffG b' ∧
      ∀ h, (z₁ h + ∑ j : Fin k, u j * P j h) * (z₂ h + ∑ j : Fin k, v j * P j h) = a' h * b' h) ∨
    (∃ a' : U → F, ∃ w : Fin k → F, isAffG a' ∧
      ∀ h, (z₁ h + ∑ j : Fin k, u j * P j h) * (z₂ h + ∑ j : Fin k, v j * P j h) =
        a' h + ∑ j : Fin k, w j * P j h) := by
  let Uf : U → F := fun h => ∑ j : Fin k, u j * P j h
  let Wf : U → F := fun h => ∑ j : Fin k, v j * P j h
  let Pk : U → F := fun h => (z₁ h + Uf h) * (z₂ h + Wf h)
  rcases hshift with ⟨e₂, h1, h2, hP⟩ | ⟨e₁, h1, h2, hP⟩ | ⟨e₁₂, h1, h2, hP⟩
  · have hd : diffG Pk e₂ = fun h => z₁ h + Uf h := by
      funext h
      have hU : Uf (h + e₂) = Uf h := Finset.sum_congr rfl fun j _ => by rw [hP j h]
      have hW : Wf (h + e₂) = Wf h := Finset.sum_congr rfl fun j _ => by rw [hP j h]
      simp only [diffG, Pk, h1 h, h2 h, hU, hW]
      have hx : (z₁ h + Uf h) * (z₂ h + 1 + Wf h) + (z₁ h + Uf h) * (z₂ h + Wf h) =
          (z₁ h + Uf h) * ((z₂ h + Wf h) + (z₂ h + Wf h)) + (z₁ h + Uf h) := by ring
      rw [hx, f_add_self, mul_zero, zero_add]
    have hA : isAffG (fun h => z₁ h + Uf h) := by rw [← hd]; exact fun a b x => hquad e₂ a b x
    by_cases hconst : ∀ h, z₁ h + Uf h = z₁ 0 + Uf 0
    · rcases f_cases (z₁ 0 + Uf 0) with h0 | h0
      · left
        refine ⟨fun _ => 0, fun _ => 0, isAffG_const 0, isAffG_const 0, fun h => ?_⟩
        change (z₁ h + Uf h) * (z₂ h + Wf h) = 0 * 0
        rw [hconst h, h0, zero_mul, zero_mul]
      · right
        refine ⟨z₂, v, hz₂, fun h => ?_⟩
        rw [hconst h, h0, one_mul]
    · push Not at hconst
      obtain ⟨e, he⟩ := hconst
      obtain ⟨M, hM, hAM⟩ := mul_aff_quad_factor hA e he hquad
      left
      exact ⟨fun h => z₁ h + Uf h, M, hA, hM, hAM⟩
  · have hd : diffG Pk e₁ = fun h => z₂ h + Wf h := by
      funext h
      have hU : Uf (h + e₁) = Uf h := Finset.sum_congr rfl fun j _ => by rw [hP j h]
      have hW : Wf (h + e₁) = Wf h := Finset.sum_congr rfl fun j _ => by rw [hP j h]
      simp only [diffG, Pk, h1 h, h2 h, hU, hW]
      have hx : (z₁ h + 1 + Uf h) * (z₂ h + Wf h) + (z₁ h + Uf h) * (z₂ h + Wf h) =
          ((z₁ h + Uf h) + (z₁ h + Uf h)) * (z₂ h + Wf h) + (z₂ h + Wf h) := by ring
      rw [hx, f_add_self, zero_mul, zero_add]
    have hB : isAffG (fun h => z₂ h + Wf h) := by rw [← hd]; exact fun a b x => hquad e₁ a b x
    by_cases hconst : ∀ h, z₂ h + Wf h = z₂ 0 + Wf 0
    · rcases f_cases (z₂ 0 + Wf 0) with h0 | h0
      · left
        refine ⟨fun _ => 0, fun _ => 0, isAffG_const 0, isAffG_const 0, fun h => ?_⟩
        rw [hconst h, h0, mul_zero, zero_mul]
      · right
        refine ⟨z₁, u, hz₁, fun h => ?_⟩
        rw [hconst h, h0, mul_one]
    · push Not at hconst
      obtain ⟨e, he⟩ := hconst
      have hquad' : isQuadG (fun h => (z₂ h + Wf h) * (z₁ h + Uf h)) := by
        have : (fun h => (z₂ h + Wf h) * (z₁ h + Uf h)) = Pk := by funext h; simp [Pk]; ring
        rw [this]; exact hquad
      obtain ⟨M, hM, hBM⟩ := mul_aff_quad_factor hB e he hquad'
      left
      exact ⟨M, fun h => z₂ h + Wf h, hM, hB, fun h => by rw [mul_comm, hBM h, mul_comm]⟩
  · have hd : diffG Pk e₁₂ = fun h => z₁ h + Uf h + z₂ h + Wf h + 1 := by
      funext h
      have hU : Uf (h + e₁₂) = Uf h := Finset.sum_congr rfl fun j _ => by rw [hP j h]
      have hW : Wf (h + e₁₂) = Wf h := Finset.sum_congr rfl fun j _ => by rw [hP j h]
      simp only [diffG, Pk, h1 h, h2 h, hU, hW]
      have hx : (z₁ h + 1 + Uf h) * (z₂ h + 1 + Wf h) + (z₁ h + Uf h) * (z₂ h + Wf h) =
          ((z₁ h + Uf h) * (z₂ h + Wf h) + (z₁ h + Uf h) * (z₂ h + Wf h)) +
          (z₁ h + Uf h + z₂ h + Wf h + 1) := by ring
      rw [hx, f_add_self, zero_add]
    have hd_aff : isAffG (fun h => z₁ h + Uf h + z₂ h + Wf h + 1) := by
      rw [← hd]; exact fun a b x => hquad e₁₂ a b x
    let M : U → F := fun h => Uf h + Wf h
    have hM_aff : isAffG M := by
      have hMeq : M = fun h => (z₁ h + Uf h + z₂ h + Wf h + 1) + (z₁ h + z₂ h + 1) := by
        funext h
        have : (z₁ h + Uf h + z₂ h + Wf h + 1) + (z₁ h + z₂ h + 1) =
            (z₁ h + z₁ h) + (z₂ h + z₂ h) + (1 + 1) + (Uf h + Wf h) := by ring
        rw [this]; simp only [f_add_self, zero_add]; rfl
      rw [hMeq]
      exact isAffG_add hd_aff (isAffG_add (isAffG_add hz₁ hz₂) (isAffG_const 1))
    let B : U → F := fun h => z₁ h + z₂ h + M h + 1
    have hB_aff : isAffG B := isAffG_add (isAffG_add (isAffG_add hz₁ hz₂) hM_aff) (isAffG_const 1)
    have hPk_eq : ∀ h, Pk h = z₁ h * (z₂ h + M h) + B h * Uf h := by
      intro h
      have hWf : Wf h = Uf h + M h := by
        simp only [M]
        have : Uf h + (Uf h + Wf h) = (Uf h + Uf h) + Wf h := by ring
        rw [this, f_add_self, zero_add]
      simp only [Pk, hWf, B]
      have hx : (z₁ h + Uf h) * (z₂ h + (Uf h + M h)) =
          z₁ h * (z₂ h + M h) + (z₁ h + z₂ h + M h) * Uf h + Uf h * Uf h := by ring
      rw [hx, f_mul_self]; ring
    by_cases hconst : ∀ h, B h = B 0
    · rcases f_cases (B 0) with h0 | h0
      · left
        refine ⟨z₁, fun h => z₂ h + M h, hz₁, isAffG_add hz₂ hM_aff, fun h => ?_⟩
        change Pk h = z₁ h * (z₂ h + M h)
        rw [hPk_eq h, hconst h, h0, zero_mul, add_zero]
      · right
        refine ⟨z₁, u, hz₁, fun h => ?_⟩
        have hB1 : z₁ h + z₂ h + M h + 1 = 1 := by change B h = 1; rw [hconst h, h0]
        have heq : z₂ h + M h = z₁ h := by
          have := congrArg (· + (z₁ h + 1)) hB1
          have hl : z₁ h + z₂ h + M h + 1 + (z₁ h + 1) = (z₁ h + z₁ h) + (1 + 1) + (z₂ h + M h) := by ring
          have hr : 1 + (z₁ h + 1) = (1 + 1) + z₁ h := by ring
          rw [hl, hr] at this; simp only [f_add_self, zero_add] at this
          exact this
        change Pk h = z₁ h + Uf h
        rw [hPk_eq h, heq, f_mul_self, hconst h, h0, one_mul]
    · push Not at hconst
      obtain ⟨e, he⟩ := hconst
      have hBU_quad : isQuadG (fun h => B h * Uf h) := by
        have hfun : (fun h => B h * Uf h) = fun h => Pk h + z₁ h * (z₂ h + M h) := by
          funext h; rw [hPk_eq h]
          have : z₁ h * (z₂ h + M h) + B h * Uf h + z₁ h * (z₂ h + M h) =
              (z₁ h * (z₂ h + M h) + z₁ h * (z₂ h + M h)) + B h * Uf h := by ring
          rw [this, f_add_self, zero_add]
        rw [hfun]
        exact isQuadG_add hquad (isQuadG_mul_aff hz₁ (isAffG_add hz₂ hM_aff))
      obtain ⟨N, hN_aff, hBN⟩ := mul_aff_quad_factor hB_aff e he hBU_quad
      left
      refine ⟨fun h => z₁ h + N h, fun h => z₂ h + M h + N h,
        isAffG_add hz₁ hN_aff, isAffG_add (isAffG_add hz₂ hM_aff) hN_aff, fun h => ?_⟩
      change Pk h = (z₁ h + N h) * (z₂ h + M h + N h)
      rw [hPk_eq h, hBN h]
      simp only [B]
      have hx : (z₁ h + N h) * (z₂ h + M h + N h) =
          z₁ h * (z₂ h + M h) + (z₁ h + z₂ h + M h) * N h + N h * N h := by ring
      rw [hx, f_mul_self]; ring

lemma aff_triples_to_lin_triples {n s : ℕ} {U : Type*} [AddCommGroup U] [Module F U]
    (L₀ : V n →ₗ[F] U) {g q₀ : V n → F} (hq₀ : quad q₀)
    {Q : U → F} (hQ : isQuadG Q)
    (a₀ a₁ a₂ : Fin s → U → F)
    (ha : ∀ i : Fin s, isAffG (a₀ i) ∧ isAffG (a₁ i) ∧ isAffG (a₂ i))
    (hg : ∀ y : V n, g y = q₀ y + Q (L₀ y) + ∑ i : Fin s, a₀ i (L₀ y) * a₁ i (L₀ y) * a₂ i (L₀ y)) :
    ∃ (L : V n →ₗ[F] E s) (q : V n → F),
      quad q ∧ ∀ y : V n, g y = q y + ∑ i : Fin s, L y (i, 0) * L y (i, 1) * L y (i, 2) := by
  have hlin0 : ∀ i : Fin s, ∃ (c : F) (l : U →ₗ[F] F), ∀ u : U, a₀ i u = c + l u := fun i => isAffG_exists_linear (ha i).1
  have hlin1 : ∀ i : Fin s, ∃ (c : F) (l : U →ₗ[F] F), ∀ u : U, a₁ i u = c + l u := fun i => isAffG_exists_linear (ha i).2.1
  have hlin2 : ∀ i : Fin s, ∃ (c : F) (l : U →ₗ[F] F), ∀ u : U, a₂ i u = c + l u := fun i => isAffG_exists_linear (ha i).2.2
  choose c₀ l₀ hl₀ using hlin0
  choose c₁ l₁ hl₁ using hlin1
  choose c₂ l₂ hl₂ using hlin2
  let L : V n →ₗ[F] E s :=
    { toFun := fun y p => match p.2 with
        | ⟨0, _⟩ => l₀ p.1 (L₀ y)
        | ⟨1, _⟩ => l₁ p.1 (L₀ y)
        | ⟨2, _⟩ => l₂ p.1 (L₀ y)
      map_add' := fun y₁ y₂ => by
        funext ⟨i, r⟩; fin_cases r <;> simp [map_add]
      map_smul' := fun r y => by
        funext ⟨i, k⟩; fin_cases k <;> simp [map_smul] }
  let q : V n → F := fun y => g y + ∑ i : Fin s, L y (i, 0) * L y (i, 1) * L y (i, 2)
  have hq_diff3 : ∀ a b d x : V n, diff (diff (diff q a) b) d x = 0 := by
    have hq_eq : q = fun y => q₀ y + Q (L₀ y) +
        ∑ i : Fin s, (a₀ i (L₀ y) * a₁ i (L₀ y) * a₂ i (L₀ y) +
          l₀ i (L₀ y) * l₁ i (L₀ y) * l₂ i (L₀ y)) := by
      funext y
      simp only [q, hg y, L, LinearMap.coe_mk, AddHom.coe_mk, Finset.sum_add_distrib]
      ring
    intro a b d x
    rw [hq_eq]
    have hdiff_add : ∀ (f₁ f₂ : V n → F),
        diff (diff (diff (fun y => f₁ y + f₂ y) a) b) d x =
          diff (diff (diff f₁ a) b) d x + diff (diff (diff f₂ a) b) d x := by
      intro f₁ f₂
      have e1 : diff (fun y => f₁ y + f₂ y) a = fun y => diff f₁ a y + diff f₂ a y :=
        funext (diff_add_fun f₁ f₂ a)
      rw [e1]
      have e2 : diff (fun y => diff f₁ a y + diff f₂ a y) b =
          fun y => diff (diff f₁ a) b y + diff (diff f₂ a) b y :=
        funext (diff_add_fun _ _ b)
      rw [e2, diff_add_fun]
    rw [hdiff_add, hdiff_add, diff3_quad hq₀, zero_add]
    have hQL : diff (diff (diff (fun y => Q (L₀ y)) a) b) d x = 0 := by
      have h1 : ∀ f : U → F, ∀ u : V n, diff (fun y => f (L₀ y)) u = fun y => diffG f (L₀ u) (L₀ y) := by
        intro f u; funext y; simp [diff_eq_add, diffG, map_add]
      rw [h1 Q a, h1 (diffG Q (L₀ a)) b, h1 (diffG (diffG Q (L₀ a)) (L₀ b)) d]
      exact hQ (L₀ a) (L₀ b) (L₀ d) (L₀ x)
    rw [hQL, zero_add]
    have hdiff_sum : ∀ (S : Finset (Fin s)) (f : Fin s → V n → F),
        diff (diff (diff (fun y => ∑ i ∈ S, f i y) a) b) d x =
          ∑ i ∈ S, diff (diff (diff (f i) a) b) d x := by
      intro S f
      have e1 : diff (fun y => ∑ i ∈ S, f i y) a = fun y => ∑ i ∈ S, diff (f i) a y :=
        funext (diff_sum S f a)
      rw [e1]
      have e2 : diff (fun y => ∑ i ∈ S, diff (f i) a y) b = fun y => ∑ i ∈ S, diff (diff (f i) a) b y :=
        funext (diff_sum S (fun i => diff (f i) a) b)
      rw [e2, diff_sum]
    rw [hdiff_sum]
    apply Finset.sum_eq_zero; intro i _
    have hrem : (fun y => a₀ i (L₀ y) * a₁ i (L₀ y) * a₂ i (L₀ y) +
        l₀ i (L₀ y) * l₁ i (L₀ y) * l₂ i (L₀ y)) =
        fun y =>
          (c₀ i * c₁ i * c₂ i +
           c₀ i * c₁ i * l₂ i (L₀ y) + c₀ i * c₂ i * l₁ i (L₀ y) + c₁ i * c₂ i * l₀ i (L₀ y)) +
          (c₀ i * l₁ i (L₀ y) * l₂ i (L₀ y) + c₁ i * l₀ i (L₀ y) * l₂ i (L₀ y) +
           c₂ i * l₀ i (L₀ y) * l₁ i (L₀ y)) := by
      funext y
      rw [hl₀ i (L₀ y), hl₁ i (L₀ y), hl₂ i (L₀ y)]
      have h : (c₀ i + l₀ i (L₀ y)) * (c₁ i + l₁ i (L₀ y)) * (c₂ i + l₂ i (L₀ y)) +
          l₀ i (L₀ y) * l₁ i (L₀ y) * l₂ i (L₀ y) =
          (l₀ i (L₀ y) * l₁ i (L₀ y) * l₂ i (L₀ y) + l₀ i (L₀ y) * l₁ i (L₀ y) * l₂ i (L₀ y)) +
          ((c₀ i * c₁ i * c₂ i +
            c₀ i * c₁ i * l₂ i (L₀ y) + c₀ i * c₂ i * l₁ i (L₀ y) + c₁ i * c₂ i * l₀ i (L₀ y)) +
           (c₀ i * l₁ i (L₀ y) * l₂ i (L₀ y) + c₁ i * l₀ i (L₀ y) * l₂ i (L₀ y) +
            c₂ i * l₀ i (L₀ y) * l₁ i (L₀ y))) := by ring
      rw [h, f_add_self, zero_add]
    rw [hrem]
    have h1 : ∀ f : U → F, ∀ u : V n, diff (fun y => f (L₀ y)) u = fun y => diffG f (L₀ u) (L₀ y) := by
      intro f u; funext y; simp [diff_eq_add, diffG, map_add]
    let R_i : U → F := fun u =>
      (c₀ i * c₁ i * c₂ i + c₀ i * c₁ i * l₂ i u + c₀ i * c₂ i * l₁ i u + c₁ i * c₂ i * l₀ i u) +
      (c₀ i * l₁ i u * l₂ i u + c₁ i * l₀ i u * l₂ i u + c₂ i * l₀ i u * l₁ i u)
    have hRi_quad : isQuadG R_i := by
      have hsm : ∀ (r : F) (l : U →ₗ[F] F), isAffG (fun u => r * l u) := fun r l => by
        have : (fun u => r * l u) = (r • l) := rfl
        rw [this]; exact isAffG_of_linear (r • l)
      apply isQuadG_add
      · apply isQuadG_of_isAffG
        exact isAffG_add (isAffG_add (isAffG_add (isAffG_const _) (hsm _ (l₂ i))) (hsm _ (l₁ i))) (hsm _ (l₀ i))
      · exact isQuadG_add
          (isQuadG_add
            (isQuadG_mul_aff (hsm (c₀ i) (l₁ i)) (isAffG_of_linear (l₂ i)))
            (isQuadG_mul_aff (hsm (c₁ i) (l₀ i)) (isAffG_of_linear (l₂ i))))
          (isQuadG_mul_aff (hsm (c₂ i) (l₀ i)) (isAffG_of_linear (l₁ i)))
    change diff (diff (diff (fun y => R_i (L₀ y)) a) b) d x = 0
    rw [h1 R_i a, h1 (diffG R_i (L₀ a)) b, h1 (diffG (diffG R_i (L₀ a)) (L₀ b)) d]
    exact hRi_quad (L₀ a) (L₀ b) (L₀ d) (L₀ x)
  refine ⟨L, q, quad_of_diff3_eq_zero hq_diff3, fun y => ?_⟩
  simp only [q]
  have h : g y + (∑ i : Fin s, L y (i, 0) * L y (i, 1) * L y (i, 2)) +
      (∑ i : Fin s, L y (i, 0) * L y (i, 1) * L y (i, 2)) =
      g y + ((∑ i : Fin s, L y (i, 0) * L y (i, 1) * L y (i, 2)) +
        (∑ i : Fin s, L y (i, 0) * L y (i, 1) * L y (i, 2))) := by ring
  rw [h, f_add_self, add_zero]

lemma no_fewer_triples {n c s : ℕ} {g : V n → F} {R : Submodule F (V n)}
    (hR : ∀ u : V n, u ∈ R ↔ ∀ v w : V n, third g u v w = 0)
    (hdc : (n - Module.finrank F R) + 1 = 3 * c) (hs : s < c)
    (L : V n →ₗ[F] E s) (q : V n → F) (hq : quad q)
    (hg : ∀ y : V n, g y = q y + ∑ i : Fin s, L y (i, 0) * L y (i, 1) * L y (i, 2)) :
    False := by
  have hker_le : LinearMap.ker L ≤ R := by
    intro u hu
    rw [hR]
    intro v w
    have hg_fun : g = fun y => q y + ∑ i : Fin s, L y (i, 0) * L y (i, 1) * L y (i, 2) := funext hg
    rw [hg_fun, third_add_fun, third_quad hq, zero_add, third_sum]
    apply Finset.sum_eq_zero; intro i _
    let l₀ : V n →ₗ[F] F := (LinearMap.proj (i, (0 : Fin 3))).comp L
    let l₁ : V n →ₗ[F] F := (LinearMap.proj (i, (1 : Fin 3))).comp L
    let l₂ : V n →ₗ[F] F := (LinearMap.proj (i, (2 : Fin 3))).comp L
    change third (fun y => l₀ y * l₁ y * l₂ y) u v w = 0
    rw [third_triple l₀ l₁ l₂ u v w]
    have hLu : L u = 0 := LinearMap.mem_ker.mp hu
    simp [det3, l₀, l₁, l₂, hLu]
  have hle1 : Module.finrank F (LinearMap.ker L) ≤ Module.finrank F R :=
    Submodule.finrank_mono hker_le
  have hle2 : Module.finrank F (LinearMap.range L) ≤ 3 * s := by
    have h1 := Submodule.finrank_le (LinearMap.range L)
    have h2 : Module.finrank F (E s) = 3 * s := by
      rw [Module.finrank_fintype_fun_eq_card, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin]
      ring
    omega
  have hr := LinearMap.finrank_range_add_finrank_ker L
  rw [Module.finrank_fin_fun] at hr
  have hRle : Module.finrank F R ≤ n := by
    have := Submodule.finrank_le R; simpa [Module.finrank_fin_fun] using this
  omega

lemma no_surjective_triples {n c : ℕ} {g : V n → F} {R : Submodule F (V n)}
    (hg : cubic g) (hR : ∀ u : V n, u ∈ R ↔ ∀ v w : V n, third g u v w = 0)
    (hdc : (n - Module.finrank F R) + 1 = 3 * c)
    (L : V n →ₗ[F] E c) (q : V n → F) (hq : quad q)
    (hge : ∀ y : V n, g y = q y + ∑ i : Fin c, L y (i, 0) * L y (i, 1) * L y (i, 2))
    (hsurj : Function.Surjective L) :
    False := by
  have hthird : ∀ a b d : V n, third g a b d = omegaE (L a) (L b) (L d) := by
    intro a b d
    have hg_fun : g = fun x => q x + ∑ i : Fin c, L x (i, 0) * L x (i, 1) * L x (i, 2) := funext hge
    rw [hg_fun, third_add_fun, third_quad hq, zero_add, third_sum]
    simp only [omegaE]
    apply Finset.sum_congr rfl; intro i _
    let l₀ : V n →ₗ[F] F := (LinearMap.proj (i, (0 : Fin 3))).comp L
    let l₁ : V n →ₗ[F] F := (LinearMap.proj (i, (1 : Fin 3))).comp L
    let l₂ : V n →ₗ[F] F := (LinearMap.proj (i, (2 : Fin 3))).comp L
    exact third_triple l₀ l₁ l₂ a b d
  have hker : LinearMap.ker L = R := by
    ext u
    rw [LinearMap.mem_ker, hR]
    constructor
    · intro hLu v w; rw [hthird, hLu]; simp [omegaE, det3]
    · intro hz
      have hr0 : rankAt g u = 0 := by
        rw [rankAt_eq_finrank_range hg u]
        have hb0 : bilinMap hg u = 0 := by
          apply LinearMap.ext; intro v; apply LinearMap.ext; intro w; exact hz v w
        rw [hb0, LinearMap.range_zero, finrank_bot]
      rw [rankAt_eq_finrank_range hg u] at hr0
      have hpb : bilinMap hg u = (L.dualMap.comp (BE (L u))).comp L := by
        apply LinearMap.ext; intro v; apply LinearMap.ext; intro w; exact hthird u v w
      rw [hpb, finrank_range_pullback L hsurj (BE (L u)), BE_finrank_range (L u)] at hr0
      have hocc0 : occ (L u) = ∅ := Finset.card_eq_zero.mp (by omega)
      funext ⟨i, s⟩
      have hni : i ∉ occ (L u) := by rw [hocc0]; simp
      rw [occ, Finset.mem_filter] at hni; push Not at hni
      exact congrFun (hni (Finset.mem_univ i)) s
  have hr := LinearMap.finrank_range_add_finrank_ker L
  rw [LinearMap.range_eq_top.mpr hsurj, finrank_top, Module.finrank_fintype_fun_eq_card,
    Fintype.card_prod, Fintype.card_fin, Fintype.card_fin, Module.finrank_fin_fun, hker] at hr
  have hRle : Module.finrank F R ≤ n := by
    have := Submodule.finrank_le R; simpa [Module.finrank_fin_fun] using this
  omega

lemma fold_linearized_sum {U : Type*} [AddCommGroup U] [Module F U]
    {m : ℕ} (P : Fin m → U → F) (M : Fin m → U → F) (hM : ∀ i, isAffG (M i))
    (hP : ∀ k : Fin m,
      (∃ a b : U → F, isAffG a ∧ isAffG b ∧ ∀ h, P k h = a h * b h) ∨
      (∃ a : U → F, ∃ w : Fin k.val → F, isAffG a ∧
        ∀ h, P k h = a h + ∑ j : Fin k.val, w j * P ⟨j.val, by omega⟩ h)) :
    ∃ (s : ℕ) (_ : s ≤ m) (Q : U → F) (a₀ a₁ a₂ : Fin s → U → F),
      isQuadG Q ∧ (∀ i, isAffG (a₀ i) ∧ isAffG (a₁ i) ∧ isAffG (a₂ i)) ∧
      ∀ h, ∑ k : Fin m, M k h * P k h = Q h + ∑ i : Fin s, a₀ i h * a₁ i h * a₂ i h := by
  induction m with
  | zero =>
    exact ⟨0, le_rfl, fun _ => 0, fun i => i.elim0, fun i => i.elim0, fun i => i.elim0,
      isQuadG_of_isAffG (isAffG_const 0), fun i => i.elim0, fun _ => by simp⟩
  | succ m ih =>
    let P' : Fin m → U → F := fun j => P j.castSucc
    have hP' : ∀ k : Fin m,
        (∃ a b : U → F, isAffG a ∧ isAffG b ∧ ∀ h, P' k h = a h * b h) ∨
        (∃ a : U → F, ∃ w : Fin k.val → F, isAffG a ∧
          ∀ h, P' k h = a h + ∑ j : Fin k.val, w j * P' ⟨j.val, by omega⟩ h) :=
      fun k => hP k.castSucc
    rcases hP (Fin.last m) with ⟨a, b, ha, hb, hlast⟩ | ⟨a, w, ha, hlast⟩
    · obtain ⟨s, hs, Q, a₀, a₁, a₂, hQ, ha', hsum⟩ := ih P' (fun j => M j.castSucc) (fun j => hM j.castSucc) hP'
      refine ⟨s + 1, by omega, Q, Fin.snoc a₀ (M (Fin.last m)), Fin.snoc a₁ a, Fin.snoc a₂ b, hQ, ?_, ?_⟩
      · intro i
        refine Fin.lastCases ?_ ?_ i
        · simp [hM (Fin.last m), ha, hb]
        · intro j; simp [ha' j]
      · intro h
        rw [Fin.sum_univ_castSucc, Fin.sum_univ_castSucc, hsum h, hlast h]
        simp only [Fin.snoc_castSucc, Fin.snoc_last]; ring
    · let M' : Fin m → U → F := fun j h => M j.castSucc h + w j * M (Fin.last m) h
      have hM' : ∀ j : Fin m, isAffG (M' j) := fun j => by
        apply isAffG_add (hM j.castSucc)
        rcases f_cases (w j) with hw | hw
        · simp only [hw, zero_mul]; exact isAffG_const 0
        · simp only [hw, one_mul]; exact hM (Fin.last m)
      obtain ⟨s, hs, Q, a₀, a₁, a₂, hQ, ha', hsum⟩ := ih P' M' hM' hP'
      refine ⟨s, by omega, fun h => Q h + M (Fin.last m) h * a h, a₀, a₁, a₂,
        isQuadG_add hQ (isQuadG_mul_aff (hM (Fin.last m)) ha), ha', ?_⟩
      intro h
      rw [Fin.sum_univ_castSucc, hlast h, mul_add, Finset.mul_sum]
      have hcombine : (∑ j : Fin m, M j.castSucc h * P j.castSucc h) +
          (M (Fin.last m) h * a h + ∑ j : Fin m, M (Fin.last m) h * (w j * P j.castSucc h)) =
          M (Fin.last m) h * a h + ∑ j : Fin m, M' j h * P' j h := by
        simp only [M', P', add_mul, Finset.sum_add_distrib]
        have heq : (∑ j : Fin m, M (Fin.last m) h * (w j * P j.castSucc h)) =
            ∑ j : Fin m, w j * M (Fin.last m) h * P j.castSucc h := by
          apply Finset.sum_congr rfl; intro j _; ring
        rw [heq]; ring
      have hcast : (∑ j : Fin (Fin.last m).val, M (Fin.last m) h * (w j * P ⟨j.val, by omega⟩ h)) =
          ∑ j : Fin m, M (Fin.last m) h * (w j * P j.castSucc h) := by
        apply Finset.sum_congr rfl; intro j _; rfl
      change (∑ j : Fin m, M j.castSucc h * P j.castSucc h) +
        (M (Fin.last m) h * a h + ∑ j : Fin (Fin.last m).val, M (Fin.last m) h * (w j * P ⟨j.val, by omega⟩ h)) = _
      rw [hcast, hcombine, hsum h]; ring

def Ptilde {n m : ℕ} (Y : YSLP n m) : (k : ℕ) → (hk : k < m) → E m → F
  | k, hk, z =>
    (z (⟨k, hk⟩, 1) + (Y.a ⟨k, hk⟩).c0 +
      ∑ j : Fin k, (Y.a ⟨k, hk⟩).lp j * Ptilde Y j.val (by omega) z) *
    (z (⟨k, hk⟩, 2) + (Y.b ⟨k, hk⟩).c0 +
      ∑ j : Fin k, (Y.b ⟨k, hk⟩).lp j * Ptilde Y j.val (by omega) z)

lemma Ptilde_eval {n m : ℕ} (Y : YSLP n m) (ℓ : Fin m → V n) :
    let L₀ : V n →ₗ[F] E m :=
      { toFun := fun y p => match p.2 with
          | ⟨0, _⟩ => dotProduct (ℓ p.1) y
          | ⟨1, _⟩ => dotProduct (Y.a p.1).ly y
          | ⟨2, _⟩ => dotProduct (Y.b p.1).ly y
        map_add' := fun y₁ y₂ => by funext ⟨i, s⟩; fin_cases s <;> simp [dotProduct_add]
        map_smul' := fun r y => by funext ⟨i, s⟩; fin_cases s <;> simp [dotProduct_smul] }
    ∀ (k : ℕ) (hk : k < m) (y : V n),
      Ptilde Y k hk (L₀ y) = Y.evalFull y ⟨k, hk⟩ := by
  intro L₀
  have hpref : ∀ (y : V n) (t : ℕ) (ht : t ≤ m) (j : Fin t),
      Y.evalP y t ht j = Y.evalFull y ⟨j.val, by omega⟩ := by
    intro y t ht
    have hstep : ∀ (a b : ℕ) (hab : a ≤ b) (hb : b ≤ m) (j : Fin a),
        Y.evalP y b hb ⟨j.val, by omega⟩ = Y.evalP y a (by omega) j := by
      intro a b hab
      induction b with
      | zero => intro _ j; have := j.isLt; omega
      | succ b ih =>
        intro hb j
        by_cases hle : a ≤ b
        · have h1 : (⟨j.val, by omega⟩ : Fin (b + 1)) = (⟨j.val, by omega⟩ : Fin b).castSucc := rfl
          rw [h1]; simp only [YSLP.evalP, Fin.snoc_castSucc]; exact ih hle (by omega) j
        · have heq : a = b + 1 := by omega
          subst heq; rfl
    intro j
    exact (hstep t m ht le_rfl j).symm
  intro k hk y
  induction k using Nat.strong_induction_on with
  | ind k ih =>
    rw [Ptilde]
    have hcur : Y.evalFull y ⟨k, hk⟩ =
        (Y.a ⟨k, hk⟩).eval y (Y.evalP y k (by omega)) *
        (Y.b ⟨k, hk⟩).eval y (Y.evalP y k (by omega)) := by
      have h1 : Y.evalP y (k + 1) (by omega) (Fin.last k) = Y.evalFull y ⟨k, hk⟩ :=
        hpref y (k + 1) (by omega) (Fin.last k)
      rw [← h1]
      simp only [YSLP.evalP, Fin.snoc_last]
    rw [hcur]
    simp only [YAffExpr.eval]
    congr 1
    · have ha1 : L₀ y (⟨k, hk⟩, 1) = dotProduct (Y.a ⟨k, hk⟩).ly y := rfl
      rw [ha1, add_comm (dotProduct (Y.a ⟨k, hk⟩).ly y)]
      congr 1
      apply Finset.sum_congr rfl; intro j _
      rw [ih j.val j.isLt (by omega), hpref y k (by omega) j]
    · have hb1 : L₀ y (⟨k, hk⟩, 2) = dotProduct (Y.b ⟨k, hk⟩).ly y := rfl
      rw [hb1, add_comm (dotProduct (Y.b ⟨k, hk⟩).ly y)]
      congr 1
      apply Finset.sum_congr rfl; intro j _
      rw [ih j.val j.isLt (by omega), hpref y k (by omega) j]

lemma Ptilde_indep {n m : ℕ} (Y : YSLP n m) (k : ℕ) (hk : k < m) (z d : E m)
    (hd : ∀ j : Fin m, j.val ≤ k → d (j, 1) = 0 ∧ d (j, 2) = 0) :
    Ptilde Y k hk (z + d) = Ptilde Y k hk z := by
  induction k using Nat.strong_induction_on with
  | ind k ih =>
    rw [Ptilde, Ptilde]
    have hcur := hd ⟨k, hk⟩ le_rfl
    simp only [Pi.add_apply, hcur.1, hcur.2, add_zero]
    congr 1
    · congr 1; apply Finset.sum_congr rfl; intro j _
      rw [ih j.val j.isLt (by omega) (fun r hr => hd r (by omega))]
    · congr 1; apply Finset.sum_congr rfl; intro j _
      rw [ih j.val j.isLt (by omega) (fun r hr => hd r (by omega))]

lemma exists_hyperplane_covector {U : Type*} [AddCommGroup U] [Module F U] [FiniteDimensional F U]
    (H : Submodule F U) (hH : Module.finrank F H + 1 = Module.finrank F U) :
    ∃ α : U →ₗ[F] F, α ≠ 0 ∧ LinearMap.ker α = H := by
  classical
  obtain ⟨K, hK⟩ := Submodule.exists_isCompl H
  have hKdim : Module.finrank F K = 1 := by
    have h1 := Submodule.finrank_sup_add_finrank_inf_eq H K
    rw [hK.sup_eq_top, hK.inf_eq_bot, finrank_top, finrank_bot, add_zero] at h1
    omega
  have hKne : K ≠ ⊥ := by
    intro h0; rw [h0, finrank_bot] at hKdim; omega
  obtain ⟨v₀, hv₀K, hv₀ne⟩ : ∃ v₀ ∈ K, v₀ ≠ 0 := by
    by_contra h; push Not at h
    apply hKne; rw [eq_bot_iff]; exact h
  have hKspan : Submodule.span F {v₀} = K := by
    apply Submodule.eq_of_le_of_finrank_eq
    · exact Submodule.span_le.mpr (Set.singleton_subset_iff.mpr hv₀K)
    · rw [finrank_span_singleton hv₀ne, hKdim]
  let pK : U →ₗ[F] K := Submodule.projectionOnto K H hK.symm
  let coord : K →ₗ[F] F :=
    { toFun := fun x => if x.1 = 0 then 0 else 1
      map_add' := fun ⟨a, ha⟩ ⟨b, hb⟩ => by
        rw [← hKspan, Submodule.mem_span_singleton] at ha hb
        rcases ha with ⟨ra, rfl⟩; rcases hb with ⟨rb, rfl⟩
        rcases f_cases ra with rfl | rfl <;> rcases f_cases rb with rfl | rfl
        · simp
        · simp [hv₀ne]
        · simp [hv₀ne]
        · simp only [one_smul]
          have h0 : v₀ + v₀ = 0 := by
            have : (1 + 1 : F) • v₀ = 0 := by rw [f_add_self, zero_smul]
            rwa [add_smul, one_smul] at this
          simp [h0, hv₀ne, f_add_self]
      map_smul' := fun r ⟨a, ha⟩ => by
        rcases f_cases r with rfl | rfl
        · simp
        · simp }
  let α : U →ₗ[F] F := coord.comp pK
  refine ⟨α, ?_, ?_⟩
  · intro h0
    have := LinearMap.congr_fun h0 v₀
    have hp : pK v₀ = ⟨v₀, hv₀K⟩ := Submodule.projectionOnto_apply_left hK.symm ⟨v₀, hv₀K⟩
    simp only [α, LinearMap.comp_apply, LinearMap.zero_apply, hp, coord, LinearMap.coe_mk,
      AddHom.coe_mk, hv₀ne, ite_false] at this
    exact absurd this (by decide)
  · ext u
    rw [LinearMap.mem_ker]
    constructor
    · intro hu
      have hp0 : pK u = 0 := by
        by_contra hne
        have h1 : coord (pK u) = 1 := by
          simp only [coord, LinearMap.coe_mk, AddHom.coe_mk]
          have : (pK u).1 ≠ 0 := fun h0 => hne (Subtype.ext h0)
          simp [this]
        exact absurd (hu.symm.trans h1) (by decide)
      have hkerp : LinearMap.ker pK = H := Submodule.ker_projectionOnto hK.symm
      rw [← hkerp, LinearMap.mem_ker]
      exact hp0
    · intro hu
      have hp0 : pK u = 0 := by
        have hkerp : LinearMap.ker pK = H := Submodule.ker_projectionOnto hK.symm
        rw [← hkerp, LinearMap.mem_ker] at hu
        exact hu
      simp [α, hp0]

lemma slp_to_triples_I0_one_A1 {n r : ℕ} {g : V n → F} {R : Submodule F (V n)}
    (hR : ∀ u : V n, u ∈ R ↔ ∀ v w : V n, third g u v w = 0)
    (Y : YSLP n r) (q₀ : V n → F) (β : Fin r → F) (hq₀ : quad q₀)
    (L₀ : V n →ₗ[F] E r) (hkerL₀ : LinearMap.ker L₀ = R)
    (α : E r →ₗ[F] F) (hH_mem : ∀ z : E r, z ∈ LinearMap.range L₀ ↔ α z = 0)
    (i₀ : Fin r) (hα_i₀ : α (Pi.single (i₀, (0 : Fin 3)) 1) = 1)
    (hgF : ∀ y : V n, g y = q₀ y + ∑ i : Fin r, (L₀ y (i, 0) + β i) * Ptilde Y i.val i.isLt (L₀ y))
    (hP_quad_other : ∀ k : Fin r, k ≠ i₀ → isQuadG (fun h : LinearMap.range L₀ => Ptilde Y k.val k.isLt h.1))
    (hAP_cub : isCubG (fun h : LinearMap.range L₀ => (h.1 (i₀, 0) + β i₀) * Ptilde Y i₀.val i₀.isLt h.1))
    (hA1 : ∀ h : LinearMap.range L₀, h.1 (i₀, 0) + β i₀ = 1) :
    False := by
  classical
  let H := LinearMap.range L₀
  let L₀H : V n →ₗ[F] H := L₀.rangeRestrict
  have hL₀H_surj : Function.Surjective L₀H := LinearMap.surjective_rangeRestrict L₀
  let Ftilde : E r → F := fun z => ∑ i : Fin r, (z (i, 0) + β i) * Ptilde Y i.val i.isLt z
  let eU : Fin r → Fin 3 → E r := fun i s => Pi.single (i, s) 1
  let A : H → F := fun h => h.1 (i₀, 0) + β i₀
  have hz_i₀_zero : ∀ h : H, h.1 (i₀, 0) = 0 := by
    intro h
    have h1 := hA1 h; have h2 := hA1 0
    simp only [A, Submodule.coe_zero, Pi.zero_apply, zero_add] at h1 h2
    rw [h2] at h1
    have := congrArg (· + 1) h1
    simp only [add_assoc, f_add_self, add_zero] at this
    exact this
  have hα_only : ∀ p : Fin r × Fin 3, p ≠ (i₀, 0) → α (Pi.single p 1) = 0 := by
    intro p hp
    by_contra hne
    have h1 : α (Pi.single p 1) = 1 := (f_cases _).resolve_left hne
    have hmem : Pi.single p (1 : F) + eU i₀ 0 ∈ H :=
      (hH_mem _).mpr (by rw [map_add, h1, hα_i₀, f_add_self])
    have h0 := hz_i₀_zero ⟨Pi.single p 1 + eU i₀ 0, hmem⟩
    simp only [Pi.add_apply, Pi.single_apply, eU, hp.symm, ite_false, ite_true, zero_add] at h0
    exact absurd h0 (by decide)
  have hPi₀_cub : isCubG (fun h : H => Ptilde Y i₀.val i₀.isLt h.1) := by
    have : (fun h : H => Ptilde Y i₀.val i₀.isLt h.1) = fun h : H => (h.1 (i₀, 0) + β i₀) * Ptilde Y i₀.val i₀.isLt h.1 := by
      funext h; rw [hA1 h, one_mul]
    rw [this]; exact hAP_cub
  have heH : ∀ (k : Fin r) (s : Fin 3), (k, s) ≠ (i₀, 0) → eU k s ∈ H :=
    fun k s hne => (hH_mem _).mpr (hα_only (k, s) hne)
  have hlp_zero : ∀ (k : Fin r), k ≠ i₀ →
      (∀ j : Fin k.val, (Y.a k).lp j = 0) ∧ (∀ j : Fin k.val, (Y.b k).lp j = 0) := by
    intro k hk
    have hqk := hP_quad_other k hk
    have hU_aff : isAffG (fun h : H => ∑ j : Fin k.val, (Y.a k).lp j * Ptilde Y j.val (by omega) h.1) := by
      let ek2 : H := ⟨eU k 2, heH k 2 (by simp)⟩
      have hd : ∀ h : H, diffG (fun x : H => Ptilde Y k.val k.isLt x.1) ek2 h =
          h.1 (k, 1) + (Y.a k).c0 + ∑ j : Fin k.val, (Y.a k).lp j * Ptilde Y j.val (by omega) h.1 := by
        intro h
        have hj_inv : ∀ j : Fin k.val, Ptilde Y j.val (by omega) (h + ek2).1 = Ptilde Y j.val (by omega) h.1 :=
          fun j => Ptilde_indep Y j.val (by omega) h.1 _ (fun m hm => by
            have hne : m ≠ k := by intro he; subst he; omega
            simp [ek2, eU, Pi.single_apply, hne])
        simp only [diffG]; rw [Ptilde, Ptilde]; simp_rw [hj_inv]
        have hc1 : (h + ek2).1 (k, 1) = h.1 (k, 1) := by simp [ek2, eU, Pi.single_apply]
        have hc2 : (h + ek2).1 (k, 2) = h.1 (k, 2) + 1 := by simp [ek2, eU, Pi.single_apply]
        rw [hc1, hc2]
        set A' := h.1 (k, 1) + (Y.a k).c0 + ∑ j : Fin k.val, (Y.a k).lp j * Ptilde Y j.val (by omega) h.1
        set B' := h.1 (k, 2) + (Y.b k).c0 + ∑ j : Fin k.val, (Y.b k).lp j * Ptilde Y j.val (by omega) h.1
        have : A' * (h.1 (k, 2) + 1 + (Y.b k).c0 + ∑ j : Fin k.val, (Y.b k).lp j * Ptilde Y j.val (by omega) h.1) + A' * B' =
            (A' * B' + A' * B') + A' := by simp only [B']; ring
        rw [this, f_add_self, zero_add]
      have hda : isAffG (fun h : H => h.1 (k, 1) + (Y.a k).c0 + ∑ j : Fin k.val, (Y.a k).lp j * Ptilde Y j.val (by omega) h.1) := by
        rw [← funext hd]; exact fun a b x => hqk ek2 a b x
      have heq : (fun h : H => ∑ j : Fin k.val, (Y.a k).lp j * Ptilde Y j.val (by omega) h.1) =
          fun h => (h.1 (k, 1) + (Y.a k).c0 + ∑ j : Fin k.val, (Y.a k).lp j * Ptilde Y j.val (by omega) h.1) +
            (h.1 (k, 1) + (Y.a k).c0) := by
        funext h
        have : (h.1 (k, 1) + (Y.a k).c0 + ∑ j : Fin k.val, (Y.a k).lp j * Ptilde Y j.val (by omega) h.1) +
            (h.1 (k, 1) + (Y.a k).c0) =
            ((h.1 (k, 1) + (Y.a k).c0) + (h.1 (k, 1) + (Y.a k).c0)) +
            ∑ j : Fin k.val, (Y.a k).lp j * Ptilde Y j.val (by omega) h.1 := by ring
        rw [this, f_add_self, zero_add]
      rw [heq]
      exact isAffG_add hda (isAffG_add (isAffG_of_linear ((LinearMap.proj (k, (1 : Fin 3))).comp H.subtype)) (isAffG_const _))
    have hW_aff : isAffG (fun h : H => ∑ j : Fin k.val, (Y.b k).lp j * Ptilde Y j.val (by omega) h.1) := by
      let ek1 : H := ⟨eU k 1, heH k 1 (by simp)⟩
      have hd : ∀ h : H, diffG (fun x : H => Ptilde Y k.val k.isLt x.1) ek1 h =
          h.1 (k, 2) + (Y.b k).c0 + ∑ j : Fin k.val, (Y.b k).lp j * Ptilde Y j.val (by omega) h.1 := by
        intro h
        have hj_inv : ∀ j : Fin k.val, Ptilde Y j.val (by omega) (h + ek1).1 = Ptilde Y j.val (by omega) h.1 :=
          fun j => Ptilde_indep Y j.val (by omega) h.1 _ (fun m hm => by
            have hne : m ≠ k := by intro he; subst he; omega
            simp [ek1, eU, Pi.single_apply, hne])
        simp only [diffG]; rw [Ptilde, Ptilde]; simp_rw [hj_inv]
        have hc1 : (h + ek1).1 (k, 1) = h.1 (k, 1) + 1 := by simp [ek1, eU, Pi.single_apply]
        have hc2 : (h + ek1).1 (k, 2) = h.1 (k, 2) := by simp [ek1, eU, Pi.single_apply]
        rw [hc1, hc2]
        set A' := h.1 (k, 1) + (Y.a k).c0 + ∑ j : Fin k.val, (Y.a k).lp j * Ptilde Y j.val (by omega) h.1
        set B' := h.1 (k, 2) + (Y.b k).c0 + ∑ j : Fin k.val, (Y.b k).lp j * Ptilde Y j.val (by omega) h.1
        have : (h.1 (k, 1) + 1 + (Y.a k).c0 + ∑ j : Fin k.val, (Y.a k).lp j * Ptilde Y j.val (by omega) h.1) * B' + A' * B' =
            (A' * B' + A' * B') + B' := by simp only [A']; ring
        rw [this, f_add_self, zero_add]
      have hdb : isAffG (fun h : H => h.1 (k, 2) + (Y.b k).c0 + ∑ j : Fin k.val, (Y.b k).lp j * Ptilde Y j.val (by omega) h.1) := by
        rw [← funext hd]; exact fun a b x => hqk ek1 a b x
      have heq : (fun h : H => ∑ j : Fin k.val, (Y.b k).lp j * Ptilde Y j.val (by omega) h.1) =
          fun h => (h.1 (k, 2) + (Y.b k).c0 + ∑ j : Fin k.val, (Y.b k).lp j * Ptilde Y j.val (by omega) h.1) +
            (h.1 (k, 2) + (Y.b k).c0) := by
        funext h
        have : (h.1 (k, 2) + (Y.b k).c0 + ∑ j : Fin k.val, (Y.b k).lp j * Ptilde Y j.val (by omega) h.1) +
            (h.1 (k, 2) + (Y.b k).c0) =
            ((h.1 (k, 2) + (Y.b k).c0) + (h.1 (k, 2) + (Y.b k).c0)) +
            ∑ j : Fin k.val, (Y.b k).lp j * Ptilde Y j.val (by omega) h.1 := by ring
        rw [this, f_add_self, zero_add]
      rw [heq]
      exact isAffG_add hdb (isAffG_add (isAffG_of_linear ((LinearMap.proj (k, (2 : Fin 3))).comp H.subtype)) (isAffG_const _))
    have hvanish : ∀ (w : Fin k.val → F),
        isAffG (fun h : H => ∑ j : Fin k.val, w j * Ptilde Y j.val (by omega) h.1) →
        ∀ j : Fin k.val, w j = 0 := by
      intro w hw
      by_contra hne; push Not at hne
      let S := Finset.univ.filter (fun j : Fin k.val => w j ≠ 0)
      have hSne : S.Nonempty := by obtain ⟨j, hj⟩ := hne; exact ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ j, hj⟩⟩
      let jmax := S.max' hSne
      have hjmax_ne : w jmax ≠ 0 := (Finset.mem_filter.mp (Finset.max'_mem S hSne)).2
      have hjmax_1 : w jmax = 1 := (f_cases _).resolve_left hjmax_ne
      have hgt0 : ∀ j : Fin k.val, jmax < j → w j = 0 := by
        intro j hj; by_contra hwn
        have : j ≤ jmax := Finset.le_max' S j (Finset.mem_filter.mpr ⟨Finset.mem_univ j, hwn⟩)
        exact not_lt_of_ge this hj
      let e1 : H := ⟨eU ⟨jmax.val, by omega⟩ 1, heH ⟨jmax.val, by omega⟩ 1 (by simp)⟩
      let e2 : H := ⟨eU ⟨jmax.val, by omega⟩ 2, heH ⟨jmax.val, by omega⟩ 2 (by simp)⟩
      have h0 := hw e1 e2 0
      have hdiff_sum : diffG (diffG (fun h : H => ∑ j : Fin k.val, w j * Ptilde Y j.val (by omega) h.1) e1) e2 0 = 1 := by
        have hd : ∀ (f : Fin k.val → H → F),
            diffG (diffG (fun h => ∑ j : Fin k.val, f j h) e1) e2 0 =
              ∑ j : Fin k.val, diffG (diffG (f j) e1) e2 0 := by
          intro f; simp only [diffG, ← Finset.sum_add_distrib]
        rw [hd]
        rw [Finset.sum_eq_single jmax]
        · rw [hjmax_1]
          have hlt_inv : ∀ t : Fin jmax.val, ∀ h : H,
              Ptilde Y t.val (by omega) (h + e1).1 = Ptilde Y t.val (by omega) h.1 ∧
              Ptilde Y t.val (by omega) (h + e2).1 = Ptilde Y t.val (by omega) h.1 := fun t h =>
            ⟨Ptilde_indep Y t.val (by omega) h.1 _ (fun m hm => by
              have : m.val ≠ jmax.val := by omega
              simp [e1, eU, Pi.single_apply, Fin.ext_iff, this]),
             Ptilde_indep Y t.val (by omega) h.1 _ (fun m hm => by
              have : m.val ≠ jmax.val := by omega
              simp [e2, eU, Pi.single_apply, Fin.ext_iff, this])⟩
          simp only [one_mul, diffG, zero_add]; rw [Ptilde, Ptilde, Ptilde, Ptilde]
          have hinv1 : ∀ t : Fin jmax.val, Ptilde Y t.val (by omega) (e2 + e1).1 = Ptilde Y t.val (by omega) 0 := by
            intro t; rw [(hlt_inv t e2).1, ← zero_add e2, (hlt_inv t 0).2]; rfl
          have hinv2 : ∀ t : Fin jmax.val, Ptilde Y t.val (by omega) e2.1 = Ptilde Y t.val (by omega) 0 := by
            intro t; rw [← zero_add e2, (hlt_inv t 0).2]; rfl
          have hinv3 : ∀ t : Fin jmax.val, Ptilde Y t.val (by omega) e1.1 = Ptilde Y t.val (by omega) 0 := by
            intro t; rw [← zero_add e1, (hlt_inv t 0).1]; rfl
          simp_rw [hinv1, hinv2, hinv3]
          have c11 : (e2 + e1).1 (⟨jmax.val, by omega⟩, 1) = 1 := by simp [e1, e2, eU, Pi.single_apply]
          have c12 : (e2 + e1).1 (⟨jmax.val, by omega⟩, 2) = 1 := by simp [e1, e2, eU, Pi.single_apply]
          have c21 : e2.1 (⟨jmax.val, by omega⟩, 1) = 0 := by simp [e2, eU, Pi.single_apply]
          have c22 : e2.1 (⟨jmax.val, by omega⟩, 2) = 1 := by simp [e2, eU, Pi.single_apply]
          have c31 : e1.1 (⟨jmax.val, by omega⟩, 1) = 1 := by simp [e1, eU, Pi.single_apply]
          have c32 : e1.1 (⟨jmax.val, by omega⟩, 2) = 0 := by simp [e1, eU, Pi.single_apply]
          rw [c11, c12, c21, c22, c31, c32]
          simp only [Submodule.coe_zero, Pi.zero_apply, zero_add]
          let U0 := (Y.a ⟨jmax.val, by omega⟩).c0 + ∑ t : Fin jmax.val, (Y.a ⟨jmax.val, by omega⟩).lp t * Ptilde Y t.val (by omega) 0
          let W0 := (Y.b ⟨jmax.val, by omega⟩).c0 + ∑ t : Fin jmax.val, (Y.b ⟨jmax.val, by omega⟩).lp t * Ptilde Y t.val (by omega) 0
          have halg : (1 + U0) * (1 + W0) + U0 * (1 + W0) + ((1 + U0) * W0 + U0 * W0) = 1 := by
            have : (1 + U0) * (1 + W0) + U0 * (1 + W0) + ((1 + U0) * W0 + U0 * W0) =
                (U0 * W0 + U0 * W0) + (U0 * W0 + U0 * W0) + (U0 + U0) + (W0 + W0) + 1 := by ring
            rw [this]; simp only [f_add_self, zero_add]
          have hrewrite : (1 + (Y.a ⟨jmax.val, by omega⟩).c0 + ∑ t : Fin jmax.val, (Y.a ⟨jmax.val, by omega⟩).lp t * Ptilde Y t.val (by omega) 0) *
              (1 + (Y.b ⟨jmax.val, by omega⟩).c0 + ∑ t : Fin jmax.val, (Y.b ⟨jmax.val, by omega⟩).lp t * Ptilde Y t.val (by omega) 0) +
              ((Y.a ⟨jmax.val, by omega⟩).c0 + ∑ t : Fin jmax.val, (Y.a ⟨jmax.val, by omega⟩).lp t * Ptilde Y t.val (by omega) 0) *
              (1 + (Y.b ⟨jmax.val, by omega⟩).c0 + ∑ t : Fin jmax.val, (Y.b ⟨jmax.val, by omega⟩).lp t * Ptilde Y t.val (by omega) 0) +
              ((1 + (Y.a ⟨jmax.val, by omega⟩).c0 + ∑ t : Fin jmax.val, (Y.a ⟨jmax.val, by omega⟩).lp t * Ptilde Y t.val (by omega) 0) *
              ((Y.b ⟨jmax.val, by omega⟩).c0 + ∑ t : Fin jmax.val, (Y.b ⟨jmax.val, by omega⟩).lp t * Ptilde Y t.val (by omega) 0) +
              ((Y.a ⟨jmax.val, by omega⟩).c0 + ∑ t : Fin jmax.val, (Y.a ⟨jmax.val, by omega⟩).lp t * Ptilde Y t.val (by omega) 0) *
              ((Y.b ⟨jmax.val, by omega⟩).c0 + ∑ t : Fin jmax.val, (Y.b ⟨jmax.val, by omega⟩).lp t * Ptilde Y t.val (by omega) 0)) =
              (1 + U0) * (1 + W0) + U0 * (1 + W0) + ((1 + U0) * W0 + U0 * W0) := by
            simp only [U0, W0, add_assoc]
          rw [hrewrite, halg]
        · intro j _ hjne
          by_cases hlt : j < jmax
          · have hi : ∀ h : H, Ptilde Y j.val (by omega) (h + e1).1 = Ptilde Y j.val (by omega) h.1 :=
              fun h => Ptilde_indep Y j.val (by omega) h.1 _ (fun m hm => by
                have : m.val ≠ jmax.val := by omega
                simp [e1, eU, Pi.single_apply, Fin.ext_iff, this])
            simp only [diffG, hi, f_add_self, add_zero]
          · have hgt : jmax < j := lt_of_le_of_ne (not_lt.mp hlt) hjne.symm
            simp [diffG, hgt0 j hgt]
        · intro h; exact (h (Finset.mem_univ jmax)).elim
      rw [hdiff_sum] at h0
      exact absurd h0 (by decide)
    exact ⟨hvanish (Y.a k).lp hU_aff, hvanish (Y.b k).lp hW_aff⟩
  have hradH : ∀ u : H, (∀ v w : H, diffG (diffG (diffG (fun h : H => Ftilde h.1) u) v) w 0 = 0) → u = 0 := by
    intro u hu
    obtain ⟨x, hx⟩ := hL₀H_surj u
    have hxR : x ∈ R := by
      rw [hR]; intro v w
      have hg_fun : g = fun y => q₀ y + Ftilde (L₀ y) := funext hgF
      rw [hg_fun, third_add_fun, third_quad hq₀, zero_add]
      have h3 : third (fun y => Ftilde (L₀ y)) x v w =
          diffG (diffG (diffG (fun h : H => Ftilde h.1) (L₀H x)) (L₀H v)) (L₀H w) 0 := by
        simp only [third, diff_eq_add, diffG, map_add, map_zero, zero_add]; rfl
      rw [h3, hx]; exact hu (L₀H v) (L₀H w)
    have hxker : L₀ x = 0 := LinearMap.mem_ker.mp (hkerL₀.symm ▸ hxR)
    exact Subtype.ext (by rw [← hx]; exact hxker)
  have hF_indep_i0 : ∀ (d : H),
      (∀ p : Fin r × Fin 3, p ≠ (i₀, 1) → p ≠ (i₀, 2) → d.1 p = 0) →
      ∀ k : Fin r, k ≠ i₀ → ∀ h : H, Ptilde Y k.val k.isLt (h + d).1 = Ptilde Y k.val k.isLt h.1 := by
    intro d hd k hk h
    rw [Ptilde, Ptilde]
    have hlp := hlp_zero k hk
    simp only [hlp.1, hlp.2, zero_mul, Finset.sum_const_zero, add_zero]
    have h1 : d.1 (k, 1) = 0 := hd (k, 1) (fun h => hk (congrArg Prod.fst h)) (by simp)
    have h2 : d.1 (k, 2) = 0 := hd (k, 2) (by simp) (fun h => hk (congrArg Prod.fst h))
    simp [h1, h2]
  have hPi₀_rad : ∀ d : H,
      (∀ p : Fin r × Fin 3, p ≠ (i₀, 1) → p ≠ (i₀, 2) → d.1 p = 0) →
      isAffG (diffG (fun h : H => Ptilde Y i₀.val i₀.isLt h.1) d) → d = 0 := by
    intro d hd haff
    apply hradH d
    intro v w
    have hFdiff : diffG (fun h : H => Ftilde h.1) d =
        diffG (fun h : H => Ptilde Y i₀.val i₀.isLt h.1) d := by
      funext h
      simp only [diffG, Ftilde, ← Finset.sum_add_distrib]
      rw [Finset.sum_eq_single i₀]
      · have hA_d : A (h + d) = 1 := hA1 (h + d)
        have hA_h : A h = 1 := hA1 h
        change A (h + d) * Ptilde Y i₀.val i₀.isLt (h + d).1 + A h * Ptilde Y i₀.val i₀.isLt h.1 = _
        rw [hA_d, hA_h, one_mul, one_mul]
      · intro k _ hk
        rw [hF_indep_i0 d hd k hk h]
        have hd0 : d.1 (k, 0) = 0 := hd (k, 0) (by simp) (by simp)
        simp [hd0, f_add_self]
      · intro h; exact (h (Finset.mem_univ i₀)).elim
    rw [hFdiff]; exact haff v w 0
  let u0 : Fin i₀.val → F := (Y.a i₀).lp
  let v0 : Fin i₀.val → F := (Y.b i₀).lp
  by_cases hu0 : u0 = 0
  · let d : H := ⟨eU i₀ 2, heH i₀ 2 (by simp)⟩
    have hd0 : d = 0 := hPi₀_rad d (fun p _ hp2 => by simp [d, eU, Pi.single_apply, hp2]) (by
      have hfun : diffG (fun h : H => Ptilde Y i₀.val i₀.isLt h.1) d =
          fun h => h.1 (i₀, 1) + (Y.a i₀).c0 := by
        funext h
        have hj_inv : ∀ j : Fin i₀.val, Ptilde Y j.val (by omega) (h + d).1 = Ptilde Y j.val (by omega) h.1 :=
          fun j => Ptilde_indep Y j.val (by omega) h.1 _ (fun m hm => by
            have hne : m ≠ i₀ := by intro he; subst he; omega
            simp [d, eU, Pi.single_apply, hne])
        simp only [diffG]; rw [Ptilde, Ptilde]; simp_rw [hj_inv]
        have hc1 : (h + d).1 (i₀, 1) = h.1 (i₀, 1) := by simp [d, eU, Pi.single_apply]
        have hc2 : (h + d).1 (i₀, 2) = h.1 (i₀, 2) + 1 := by simp [d, eU, Pi.single_apply]
        rw [hc1, hc2]
        have hu0' : ∀ j : Fin i₀.val, (Y.a i₀).lp j = 0 := fun j => congrFun hu0 j
        simp only [hu0', zero_mul, Finset.sum_const_zero, add_zero]
        set A' := h.1 (i₀, 1) + (Y.a i₀).c0
        set B' := h.1 (i₀, 2) + (Y.b i₀).c0 + ∑ j : Fin i₀.val, (Y.b i₀).lp j * Ptilde Y j.val (by omega) h.1
        have : A' * (h.1 (i₀, 2) + 1 + (Y.b i₀).c0 + ∑ j : Fin i₀.val, (Y.b i₀).lp j * Ptilde Y j.val (by omega) h.1) + A' * B' =
            (A' * B' + A' * B') + A' := by simp only [B']; ring
        rw [this, f_add_self, zero_add]
      rw [hfun]
      exact isAffG_add (isAffG_of_linear ((LinearMap.proj (i₀, (1 : Fin 3))).comp H.subtype)) (isAffG_const _))
    have := congrFun (congrArg Subtype.val hd0) (i₀, 2)
    simp [d, eU, Pi.single_apply] at this
  · by_cases hv0 : v0 = 0
    · let d : H := ⟨eU i₀ 1, heH i₀ 1 (by simp)⟩
      have hd0 : d = 0 := hPi₀_rad d (fun p hp1 _ => by simp [d, eU, Pi.single_apply, hp1]) (by
        have hfun : diffG (fun h : H => Ptilde Y i₀.val i₀.isLt h.1) d =
            fun h => h.1 (i₀, 2) + (Y.b i₀).c0 := by
          funext h
          have hj_inv : ∀ j : Fin i₀.val, Ptilde Y j.val (by omega) (h + d).1 = Ptilde Y j.val (by omega) h.1 :=
            fun j => Ptilde_indep Y j.val (by omega) h.1 _ (fun m hm => by
              have hne : m ≠ i₀ := by intro he; subst he; omega
              simp [d, eU, Pi.single_apply, hne])
          simp only [diffG]; rw [Ptilde, Ptilde]; simp_rw [hj_inv]
          have hc1 : (h + d).1 (i₀, 1) = h.1 (i₀, 1) + 1 := by simp [d, eU, Pi.single_apply]
          have hc2 : (h + d).1 (i₀, 2) = h.1 (i₀, 2) := by simp [d, eU, Pi.single_apply]
          rw [hc1, hc2]
          have hv0' : ∀ j : Fin i₀.val, (Y.b i₀).lp j = 0 := fun j => congrFun hv0 j
          simp only [hv0', zero_mul, Finset.sum_const_zero, add_zero]
          set A' := h.1 (i₀, 1) + (Y.a i₀).c0 + ∑ j : Fin i₀.val, (Y.a i₀).lp j * Ptilde Y j.val (by omega) h.1
          set B' := h.1 (i₀, 2) + (Y.b i₀).c0
          have : (h.1 (i₀, 1) + 1 + (Y.a i₀).c0 + ∑ j : Fin i₀.val, (Y.a i₀).lp j * Ptilde Y j.val (by omega) h.1) * B' + A' * B' =
              (A' * B' + A' * B') + B' := by simp only [A']; ring
          rw [this, f_add_self, zero_add]
        rw [hfun]
        exact isAffG_add (isAffG_of_linear ((LinearMap.proj (i₀, (2 : Fin 3))).comp H.subtype)) (isAffG_const _))
      have := congrFun (congrArg Subtype.val hd0) (i₀, 1)
      simp [d, eU, Pi.single_apply] at this
    · by_cases huv : u0 = v0
      · let d : H := ⟨eU i₀ 1 + eU i₀ 2, H.add_mem (heH i₀ 1 (by simp)) (heH i₀ 2 (by simp))⟩
        have hd0 : d = 0 := hPi₀_rad d (fun p hp1 hp2 => by simp [d, eU, Pi.single_apply, hp1, hp2]) (by
          have hfun : diffG (fun h : H => Ptilde Y i₀.val i₀.isLt h.1) d =
              fun h => h.1 (i₀, 1) + h.1 (i₀, 2) + (Y.a i₀).c0 + (Y.b i₀).c0 + 1 := by
            funext h
            have hj_inv : ∀ j : Fin i₀.val, Ptilde Y j.val (by omega) (h + d).1 = Ptilde Y j.val (by omega) h.1 :=
              fun j => Ptilde_indep Y j.val (by omega) h.1 _ (fun m hm => by
                have hne : m ≠ i₀ := by intro he; subst he; omega
                simp [d, eU, Pi.single_apply, hne])
            simp only [diffG]; rw [Ptilde, Ptilde]; simp_rw [hj_inv]
            have hc1 : (h + d).1 (i₀, 1) = h.1 (i₀, 1) + 1 := by simp [d, eU, Pi.single_apply]
            have hc2 : (h + d).1 (i₀, 2) = h.1 (i₀, 2) + 1 := by simp [d, eU, Pi.single_apply]
            rw [hc1, hc2]
            have huv' : ∀ j : Fin i₀.val, (Y.a i₀).lp j = (Y.b i₀).lp j := fun j => congrFun huv j
            simp_rw [huv']
            set S' := ∑ j : Fin i₀.val, (Y.b i₀).lp j * Ptilde Y j.val (by omega) h.1
            have : (h.1 (i₀, 1) + 1 + (Y.a i₀).c0 + S') * (h.1 (i₀, 2) + 1 + (Y.b i₀).c0 + S') +
                (h.1 (i₀, 1) + (Y.a i₀).c0 + S') * (h.1 (i₀, 2) + (Y.b i₀).c0 + S') =
                ((h.1 (i₀, 1) + (Y.a i₀).c0 + S') * (h.1 (i₀, 2) + (Y.b i₀).c0 + S') +
                 (h.1 (i₀, 1) + (Y.a i₀).c0 + S') * (h.1 (i₀, 2) + (Y.b i₀).c0 + S')) +
                (S' + S') + (h.1 (i₀, 1) + h.1 (i₀, 2) + (Y.a i₀).c0 + (Y.b i₀).c0 + 1) := by ring
            rw [this]; simp only [f_add_self, zero_add]
          rw [hfun]
          exact isAffG_add (isAffG_add (isAffG_add (isAffG_add
            (isAffG_of_linear ((LinearMap.proj (i₀, (1 : Fin 3))).comp H.subtype))
            (isAffG_of_linear ((LinearMap.proj (i₀, (2 : Fin 3))).comp H.subtype)))
            (isAffG_const _)) (isAffG_const _)) (isAffG_const 1))
        have := congrFun (congrArg Subtype.val hd0) (i₀, 1)
        simp [d, eU, Pi.single_apply] at this
      · have hex_pair : ∃ j₁ j₂ : Fin i₀.val, j₁ ≠ j₂ ∧ u0 j₁ * v0 j₂ + u0 j₂ * v0 j₁ = 1 := by
          have hdiff : ∃ j : Fin i₀.val, u0 j ≠ v0 j := by
            by_contra h; push Not at h; exact huv (funext h)
          obtain ⟨j, hj⟩ := hdiff
          rcases f_cases (u0 j) with huj | huj <;> rcases f_cases (v0 j) with hvj | hvj
          · exact (hj (huj.trans hvj.symm)).elim
          · obtain ⟨j₁, hj₁⟩ : ∃ j₁ : Fin i₀.val, u0 j₁ ≠ 0 := by
              by_contra h; push Not at h; exact hu0 (funext h)
            have hj₁1 : u0 j₁ = 1 := (f_cases _).resolve_left hj₁
            have hne : j₁ ≠ j := by intro he; rw [he, huj] at hj₁1; exact absurd hj₁1 (by decide)
            exact ⟨j₁, j, hne, by simp [hj₁1, hvj, huj]⟩
          · obtain ⟨j₂, hj₂⟩ : ∃ j₂ : Fin i₀.val, v0 j₂ ≠ 0 := by
              by_contra h; push Not at h; exact hv0 (funext h)
            have hj₂1 : v0 j₂ = 1 := (f_cases _).resolve_left hj₂
            have hne : j ≠ j₂ := by intro he; rw [← he, hvj] at hj₂1; exact absurd hj₂1 (by decide)
            exact ⟨j, j₂, hne, by simp [huj, hj₂1, hvj]⟩
          · exact (hj (huj.trans hvj.symm)).elim
        obtain ⟨j₁, j₂, hj12, hcross⟩ := hex_pair
        let k₁ : Fin r := ⟨j₁.val, by omega⟩
        let k₂ : Fin r := ⟨j₂.val, by omega⟩
        have hk12 : k₁ ≠ k₂ := fun h => hj12 (Fin.ext (by simpa [k₁, k₂] using congrArg Fin.val h))
        let d1 : H := ⟨eU k₁ 1, heH k₁ 1 (by simp)⟩
        let d2 : H := ⟨eU k₁ 2, heH k₁ 2 (by simp)⟩
        let d3 : H := ⟨eU k₂ 1, heH k₂ 1 (by simp)⟩
        let d4 : H := ⟨eU k₂ 2, heH k₂ 2 (by simp)⟩
        have hP_lt : ∀ j : Fin i₀.val, ∀ h : H,
            Ptilde Y j.val (by omega) h.1 =
              (h.1 (⟨j.val, by omega⟩, 1) + (Y.a ⟨j.val, by omega⟩).c0) *
              (h.1 (⟨j.val, by omega⟩, 2) + (Y.b ⟨j.val, by omega⟩).c0) := by
          intro j h
          have hne : (⟨j.val, by omega⟩ : Fin r) ≠ i₀ := by
            intro he; have := congrArg Fin.val he; dsimp at this; omega
          have hlp := hlp_zero ⟨j.val, by omega⟩ hne
          rw [Ptilde]
          simp only [hlp.1, hlp.2, zero_mul, Finset.sum_const_zero, add_zero]
        have h0 := hPi₀_cub d1 d2 d3 d4 0
        have hP_eval : ∀ (b1 b2 b3 b4 : F),
            let pt : H := b1 • d1 + b2 • d2 + b3 • d3 + b4 • d4
            Ptilde Y i₀.val i₀.isLt pt.1 =
              (u0 j₁ * ((b1 + (Y.a k₁).c0) * (b2 + (Y.b k₁).c0)) +
               u0 j₂ * ((b3 + (Y.a k₂).c0) * (b4 + (Y.b k₂).c0)) +
               ((Y.a i₀).c0 + ∑ j ∈ (Finset.univ.erase j₁).erase j₂, u0 j * ((Y.a ⟨j.val, by omega⟩).c0 * (Y.b ⟨j.val, by omega⟩).c0))) *
              (v0 j₁ * ((b1 + (Y.a k₁).c0) * (b2 + (Y.b k₁).c0)) +
               v0 j₂ * ((b3 + (Y.a k₂).c0) * (b4 + (Y.b k₂).c0)) +
               ((Y.b i₀).c0 + ∑ j ∈ (Finset.univ.erase j₁).erase j₂, v0 j * ((Y.a ⟨j.val, by omega⟩).c0 * (Y.b ⟨j.val, by omega⟩).c0))) := by
          intro b1 b2 b3 b4 pt
          rw [Ptilde]
          have hi1 : pt.1 (i₀, 1) = 0 := by
            have hk1i : k₁ ≠ i₀ := by intro h; have := congrArg Fin.val h; dsimp [k₁] at this; omega
            have hk2i : k₂ ≠ i₀ := by intro h; have := congrArg Fin.val h; dsimp [k₂] at this; omega
            simp [pt, d1, d2, d3, d4, eU, Pi.single_apply, hk1i.symm, hk2i.symm]
          have hi2 : pt.1 (i₀, 2) = 0 := by
            have hk1i : k₁ ≠ i₀ := by intro h; have := congrArg Fin.val h; dsimp [k₁] at this; omega
            have hk2i : k₂ ≠ i₀ := by intro h; have := congrArg Fin.val h; dsimp [k₂] at this; omega
            simp [pt, d1, d2, d3, d4, eU, Pi.single_apply, hk1i.symm, hk2i.symm]
          rw [hi1, hi2, zero_add, zero_add]
          have hsplit : ∀ w : Fin i₀.val → F,
              (∑ j : Fin i₀.val, w j * Ptilde Y j.val (by omega) pt.1) =
                w j₁ * ((b1 + (Y.a k₁).c0) * (b2 + (Y.b k₁).c0)) +
                w j₂ * ((b3 + (Y.a k₂).c0) * (b4 + (Y.b k₂).c0)) +
                ∑ j ∈ (Finset.univ.erase j₁).erase j₂, w j * ((Y.a ⟨j.val, by omega⟩).c0 * (Y.b ⟨j.val, by omega⟩).c0) := by
            intro w
            rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j₁)]
            rw [← Finset.add_sum_erase _ _ (Finset.mem_erase.mpr ⟨hj12.symm, Finset.mem_univ j₂⟩)]
            rw [hP_lt j₁ pt, hP_lt j₂ pt]
            have hc1 : pt.1 (k₁, 1) = b1 := by simp [pt, d1, d2, d3, d4, eU, Pi.single_apply, hk12]
            have hc2 : pt.1 (k₁, 2) = b2 := by simp [pt, d1, d2, d3, d4, eU, Pi.single_apply, hk12]
            have hc3 : pt.1 (k₂, 1) = b3 := by simp [pt, d1, d2, d3, d4, eU, Pi.single_apply, hk12.symm]
            have hc4 : pt.1 (k₂, 2) = b4 := by simp [pt, d1, d2, d3, d4, eU, Pi.single_apply, hk12.symm]
            have hrest : ∑ j ∈ (Finset.univ.erase j₁).erase j₂, w j * Ptilde Y j.val (by omega) pt.1 =
                ∑ j ∈ (Finset.univ.erase j₁).erase j₂, w j * ((Y.a ⟨j.val, by omega⟩).c0 * (Y.b ⟨j.val, by omega⟩).c0) := by
              apply Finset.sum_congr rfl; intro j hj
              rw [hP_lt j pt]
              have hne2 : j ≠ j₂ := (Finset.mem_erase.mp hj).1
              have hne1 : j ≠ j₁ := (Finset.mem_erase.mp (Finset.mem_erase.mp hj).2).1
              have hnk1 : (⟨j.val, by omega⟩ : Fin r) ≠ k₁ := fun h => hne1 (Fin.ext (by simpa [k₁] using congrArg Fin.val h))
              have hnk2 : (⟨j.val, by omega⟩ : Fin r) ≠ k₂ := fun h => hne2 (Fin.ext (by simpa [k₂] using congrArg Fin.val h))
              have hz1 : pt.1 (⟨j.val, by omega⟩, 1) = 0 := by
                simp [pt, d1, d2, d3, d4, eU, Pi.single_apply, hnk1, hnk2]
              have hz2 : pt.1 (⟨j.val, by omega⟩, 2) = 0 := by
                simp [pt, d1, d2, d3, d4, eU, Pi.single_apply, hnk1, hnk2]
              rw [hz1, hz2, zero_add, zero_add]
            rw [hrest]
            change w j₁ * ((pt.1 (k₁, 1) + (Y.a k₁).c0) * (pt.1 (k₁, 2) + (Y.b k₁).c0)) +
              (w j₂ * ((pt.1 (k₂, 1) + (Y.a k₂).c0) * (pt.1 (k₂, 2) + (Y.b k₂).c0)) + _) = _
            rw [hc1, hc2, hc3, hc4]; ring
          rw [hsplit u0, hsplit v0]; ring
        have hdiff4_val : ∀ (U1 U2 C1 V1 V2 C2 a1 b1 a2 b2 : F),
            let f : F → F → F → F → F := fun x1 x2 x3 x4 =>
              (U1 * ((x1 + a1) * (x2 + b1)) + U2 * ((x3 + a2) * (x4 + b2)) + C1) *
              (V1 * ((x1 + a1) * (x2 + b1)) + V2 * ((x3 + a2) * (x4 + b2)) + C2)
            ((f 1 1 1 1 + f 0 1 1 1) + (f 1 0 1 1 + f 0 0 1 1)) +
            ((f 1 1 0 1 + f 0 1 0 1) + (f 1 0 0 1 + f 0 0 0 1)) +
            (((f 1 1 1 0 + f 0 1 1 0) + (f 1 0 1 0 + f 0 0 1 0)) +
             ((f 1 1 0 0 + f 0 1 0 0) + (f 1 0 0 0 + f 0 0 0 0))) =
            U1 * V2 + U2 * V1 := by
          intro U1 U2 C1 V1 V2 C2 a1 b1 a2 b2 f
          let p : F → F → F := fun x1 x2 => (x1 + a1) * (x2 + b1)
          let q : F → F → F := fun x3 x4 => (x3 + a2) * (x4 + b2)
          let A : F → F → F := fun x1 x2 => U1 * V1 * (p x1 x2 * p x1 x2) + (U1 * C2 + C1 * V1) * p x1 x2 + C1 * C2
          let B : F → F → F := fun x3 x4 => U2 * V2 * (q x3 x4 * q x3 x4) + (U2 * C2 + C1 * V2) * q x3 x4
          have hfeq : ∀ x1 x2 x3 x4, f x1 x2 x3 x4 = (U1 * V2 + U2 * V1) * (p x1 x2 * q x3 x4) + A x1 x2 + B x3 x4 := by
            intro x1 x2 x3 x4; simp only [f, p, q, A, B]; ring
          simp_rw [hfeq]
          have hsumA : ∀ (t : F), t + t = 0 := f_add_self
          have hrearr :
              ((((U1 * V2 + U2 * V1) * (p 1 1 * q 1 1) + A 1 1 + B 1 1) + ((U1 * V2 + U2 * V1) * (p 0 1 * q 1 1) + A 0 1 + B 1 1)) +
               (((U1 * V2 + U2 * V1) * (p 1 0 * q 1 1) + A 1 0 + B 1 1) + ((U1 * V2 + U2 * V1) * (p 0 0 * q 1 1) + A 0 0 + B 1 1))) +
              ((((U1 * V2 + U2 * V1) * (p 1 1 * q 0 1) + A 1 1 + B 0 1) + ((U1 * V2 + U2 * V1) * (p 0 1 * q 0 1) + A 0 1 + B 0 1)) +
               (((U1 * V2 + U2 * V1) * (p 1 0 * q 0 1) + A 1 0 + B 0 1) + ((U1 * V2 + U2 * V1) * (p 0 0 * q 0 1) + A 0 0 + B 0 1))) +
              (((((U1 * V2 + U2 * V1) * (p 1 1 * q 1 0) + A 1 1 + B 1 0) + ((U1 * V2 + U2 * V1) * (p 0 1 * q 1 0) + A 0 1 + B 1 0)) +
                (((U1 * V2 + U2 * V1) * (p 1 0 * q 1 0) + A 1 0 + B 1 0) + ((U1 * V2 + U2 * V1) * (p 0 0 * q 1 0) + A 0 0 + B 1 0))) +
               ((((U1 * V2 + U2 * V1) * (p 1 1 * q 0 0) + A 1 1 + B 0 0) + ((U1 * V2 + U2 * V1) * (p 0 1 * q 0 0) + A 0 1 + B 0 0)) +
                (((U1 * V2 + U2 * V1) * (p 1 0 * q 0 0) + A 1 0 + B 0 0) + ((U1 * V2 + U2 * V1) * (p 0 0 * q 0 0) + A 0 0 + B 0 0)))) =
              (U1 * V2 + U2 * V1) * ((p 1 1 + p 0 1 + p 1 0 + p 0 0) * (q 1 1 + q 0 1 + q 1 0 + q 0 0)) +
              ((A 1 1 + A 1 1) + (A 1 1 + A 1 1)) + ((A 0 1 + A 0 1) + (A 0 1 + A 0 1)) +
              ((A 1 0 + A 1 0) + (A 1 0 + A 1 0)) + ((A 0 0 + A 0 0) + (A 0 0 + A 0 0)) +
              ((B 1 1 + B 1 1) + (B 1 1 + B 1 1)) + ((B 0 1 + B 0 1) + (B 0 1 + B 0 1)) +
              ((B 1 0 + B 1 0) + (B 1 0 + B 1 0)) + ((B 0 0 + B 0 0) + (B 0 0 + B 0 0)) := by ring
          rw [hrearr]; simp only [hsumA, add_zero]
          have hp1 : p 1 1 + p 0 1 + p 1 0 + p 0 0 = 1 := by
            simp only [p]
            have : (1 + a1) * (1 + b1) + (0 + a1) * (1 + b1) + (1 + a1) * (0 + b1) + (0 + a1) * (0 + b1) =
                1 + (a1 + a1) + (b1 + b1) + ((a1 * b1 + a1 * b1) + (a1 * b1 + a1 * b1)) := by ring
            rw [this]; simp only [f_add_self, add_zero]
          have hq1 : q 1 1 + q 0 1 + q 1 0 + q 0 0 = 1 := by
            simp only [q]
            have : (1 + a2) * (1 + b2) + (0 + a2) * (1 + b2) + (1 + a2) * (0 + b2) + (0 + a2) * (0 + b2) =
                1 + (a2 + a2) + (b2 + b2) + ((a2 * b2 + a2 * b2) + (a2 * b2 + a2 * b2)) := by ring
            rw [this]; simp only [f_add_self, add_zero]
          rw [hp1, hq1, mul_one, mul_one]
        have hexp : diffG (diffG (diffG (diffG (fun h : H => Ptilde Y i₀.val i₀.isLt h.1) d1) d2) d3) d4 0 =
            u0 j₁ * v0 j₂ + u0 j₂ * v0 j₁ := by
          simp only [diffG, zero_add]
          have hpt : ∀ (b1 b2 b3 b4 : F) (h : H),
              h = b1 • d1 + b2 • d2 + b3 • d3 + b4 • d4 →
              Ptilde Y i₀.val i₀.isLt h.1 =
                (u0 j₁ * ((b1 + (Y.a k₁).c0) * (b2 + (Y.b k₁).c0)) +
                 u0 j₂ * ((b3 + (Y.a k₂).c0) * (b4 + (Y.b k₂).c0)) +
                 ((Y.a i₀).c0 + ∑ j ∈ (Finset.univ.erase j₁).erase j₂, u0 j * ((Y.a ⟨j.val, by omega⟩).c0 * (Y.b ⟨j.val, by omega⟩).c0))) *
                (v0 j₁ * ((b1 + (Y.a k₁).c0) * (b2 + (Y.b k₁).c0)) +
                 v0 j₂ * ((b3 + (Y.a k₂).c0) * (b4 + (Y.b k₂).c0)) +
                 ((Y.b i₀).c0 + ∑ j ∈ (Finset.univ.erase j₁).erase j₂, v0 j * ((Y.a ⟨j.val, by omega⟩).c0 * (Y.b ⟨j.val, by omega⟩).c0))) := by
            intro b1 b2 b3 b4 h hh; rw [hh]; exact hP_eval b1 b2 b3 b4
          rw [hpt 1 1 1 1 _ (by simp only [one_smul]; abel), hpt 0 1 1 1 _ (by simp; abel),
              hpt 1 0 1 1 _ (by simp; abel), hpt 0 0 1 1 _ (by simp; abel),
              hpt 1 1 0 1 _ (by simp; abel), hpt 0 1 0 1 _ (by simp; abel),
              hpt 1 0 0 1 _ (by simp; abel), hpt 0 0 0 1 _ (by simp),
              hpt 1 1 1 0 _ (by simp; abel), hpt 0 1 1 0 _ (by simp; abel),
              hpt 1 0 1 0 _ (by simp; abel), hpt 0 0 1 0 _ (by simp),
              hpt 1 1 0 0 _ (by simp; abel), hpt 0 1 0 0 _ (by simp),
              hpt 1 0 0 0 _ (by simp), hpt 0 0 0 0 _ (by simp)]
          exact hdiff4_val _ _ _ _ _ _ _ _ _ _
        rw [hexp, hcross] at h0
        exact absurd h0 (by decide)

lemma slp_to_triples_I0_one_Anconst {n r : ℕ} {g : V n → F}
    (Y : YSLP n r) (β : Fin r → F)
    (L₀ : V n →ₗ[F] E r)
    (α : E r →ₗ[F] F) (hH_mem : ∀ z : E r, z ∈ LinearMap.range L₀ ↔ α z = 0)
    (i₀ : Fin r) (hα_i₀ : α (Pi.single (i₀, (0 : Fin 3)) 1) = 1)
    (hfinish : ∀ (s : ℕ) (_ : s ≤ r) (Q : LinearMap.range L₀ → F) (a₀ a₁ a₂ : Fin s → LinearMap.range L₀ → F),
      isQuadG Q → (∀ i, isAffG (a₀ i) ∧ isAffG (a₁ i) ∧ isAffG (a₂ i)) →
      (∀ h : LinearMap.range L₀, (∑ i : Fin r, (h.1 (i, 0) + β i) * Ptilde Y i.val i.isLt h.1) =
        Q h + ∑ i : Fin s, a₀ i h * a₁ i h * a₂ i h) →
      ∃ (L : V n →ₗ[F] E r) (q : V n → F),
        quad q ∧ ∀ y : V n, g y = q y + ∑ i : Fin r, L y (i, 0) * L y (i, 1) * L y (i, 2))
    (hP_other_aff : ∀ k : Fin r, k ≠ i₀ →
      ∃ a b : LinearMap.range L₀ → F, isAffG a ∧ isAffG b ∧ ∀ h : LinearMap.range L₀, Ptilde Y k.val k.isLt h.1 = a h * b h)
    (hAP_cub : isCubG (fun h : LinearMap.range L₀ => (h.1 (i₀, 0) + β i₀) * Ptilde Y i₀.val i₀.isLt h.1))
    (hA_const : ∃ eA : LinearMap.range L₀, (eA.1 (i₀, 0) + β i₀) ≠ ((0 : LinearMap.range L₀).1 (i₀, 0) + β i₀)) :
    ∃ (L : V n →ₗ[F] E r) (q : V n → F),
      quad q ∧ ∀ y : V n, g y = q y + ∑ i : Fin r, L y (i, 0) * L y (i, 1) * L y (i, 2) := by
  classical
  let H := LinearMap.range L₀
  let Ftilde : E r → F := fun z => ∑ i : Fin r, (z (i, 0) + β i) * Ptilde Y i.val i.isLt z
  let eU : Fin r → Fin 3 → E r := fun i s => Pi.single (i, s) 1
  let e' : Fin r → Fin 3 → H := fun k s =>
    ⟨eU k s + α (eU k s) • eU i₀ 0, (hH_mem _).mpr (by
      rw [map_add, map_smul, smul_eq_mul, hα_i₀, mul_one, f_add_self])⟩
  let A : H → F := fun h => h.1 (i₀, 0) + β i₀
  have hA_aff : isAffG A := isAffG_add (isAffG_of_linear ((LinearMap.proj (R := F) (φ := fun _ : Fin r × Fin 3 => F) (i₀, (0 : Fin 3))).comp H.subtype)) (isAffG_const _)
  obtain ⟨eA, heA⟩ := hA_const
  obtain ⟨M_i₀, hM_quad, hAM⟩ := mul_aff_cubic_quad hA_aff eA heA hAP_cub
  obtain ⟨cA, lA, hlA⟩ := isAffG_exists_linear hA_aff
  have hlAe : lA eA = 1 := by
    have h1 := hlA eA; have h0 := hlA 0; rw [map_zero, add_zero] at h0
    rw [← h0] at h1
    have hne : lA eA ≠ 0 := by intro hz; rw [hz, add_zero] at h1; exact heA h1
    exact (f_cases _).resolve_left hne
  let x₀ : H := if A 0 = 1 then 0 else eA
  have hAx₀ : A x₀ = 1 := by
    simp only [x₀]
    split_ifs with h0
    · exact h0
    · have h0' : A 0 = 0 := (f_cases _).resolve_right h0
      have h1 := hlA eA; rw [hlAe] at h1
      have h0'' := hlA 0; rw [map_zero, add_zero] at h0''
      rw [← h0'', h0', zero_add] at h1; exact h1
  let K := LinearMap.ker lA
  have hA_K : ∀ v : K, A (x₀ + v.1) = 1 := by
    intro v; rw [hlA, map_add, LinearMap.mem_ker.mp v.2, add_zero, ← hlA, hAx₀]
  have hPK_quad : isQuadG (fun v : K => Ptilde Y i₀.val i₀.isLt (x₀ + v.1).1) := by
    have heq : (fun v : K => Ptilde Y i₀.val i₀.isLt (x₀ + v.1).1) = fun v : K => M_i₀ (x₀ + v.1) := by
      funext v
      have := hAM (x₀ + v.1)
      rw [hA_K v, one_mul, one_mul] at this
      exact this
    rw [heq]
    intro a b d x
    have hs : ∀ (f : H → F) (u : K), diffG (fun v : K => f (x₀ + v.1)) u =
        fun v : K => diffG f u.1 (x₀ + v.1) := by
      intro f u; funext v; simp [diffG, add_assoc]
    rw [hs M_i₀ a, hs (diffG M_i₀ a.1) b, hs (diffG (diffG M_i₀ a.1) b.1) d]
    exact hM_quad a.1 b.1 d.1 (x₀ + x.1)
  let z₁K : K → F := fun v => (x₀ + v.1).1 (i₀, 1) + (Y.a i₀).c0
  let z₂K : K → F := fun v => (x₀ + v.1).1 (i₀, 2) + (Y.b i₀).c0
  have hz₁K : isAffG z₁K := by
    have : z₁K = fun v : K => (x₀.1 (i₀, 1) + (Y.a i₀).c0) + v.1.1 (i₀, 1) := by
      funext v; simp [z₁K]; ring
    rw [this]
    exact isAffG_add (isAffG_const _) (isAffG_of_linear
      { toFun := fun v : K => v.1.1 (i₀, 1)
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl })
  have hz₂K : isAffG z₂K := by
    have : z₂K = fun v : K => (x₀.1 (i₀, 2) + (Y.b i₀).c0) + v.1.1 (i₀, 2) := by
      funext v; simp [z₂K]; ring
    rw [this]
    exact isAffG_add (isAffG_const _) (isAffG_of_linear
      { toFun := fun v : K => v.1.1 (i₀, 2)
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl })
  have hshiftK :
      (∃ e₂ : K, (∀ v, z₁K (v + e₂) = z₁K v) ∧ (∀ v, z₂K (v + e₂) = z₂K v + 1) ∧
        (∀ j : Fin i₀.val, ∀ v, Ptilde Y j.val (by omega) (x₀ + (v + e₂).1).1 = Ptilde Y j.val (by omega) (x₀ + v.1).1)) ∨
      (∃ e₁ : K, (∀ v, z₁K (v + e₁) = z₁K v + 1) ∧ (∀ v, z₂K (v + e₁) = z₂K v) ∧
        (∀ j : Fin i₀.val, ∀ v, Ptilde Y j.val (by omega) (x₀ + (v + e₁).1).1 = Ptilde Y j.val (by omega) (x₀ + v.1).1)) ∨
      (∃ e₁₂ : K, (∀ v, z₁K (v + e₁₂) = z₁K v + 1) ∧ (∀ v, z₂K (v + e₁₂) = z₂K v + 1) ∧
        (∀ j : Fin i₀.val, ∀ v, Ptilde Y j.val (by omega) (x₀ + (v + e₁₂).1).1 = Ptilde Y j.val (by omega) (x₀ + v.1).1)) := by
    rcases f_cases (lA (e' i₀ 2)) with h2 | h2
    · left
      refine ⟨⟨e' i₀ 2, h2⟩,
        fun v => by simp [z₁K, e', eU, Pi.single_apply],
        fun v => by simp [z₂K, e', eU, Pi.single_apply]; ring,
        fun j v => by
          have heq : (x₀ + (v + ⟨e' i₀ 2, h2⟩).1).1 = (x₀ + v.1).1 + (e' i₀ 2).1 := by
            simp [add_assoc]
          rw [heq]
          exact Ptilde_indep Y j.val (by omega) _ _ (fun m hm => by
            have : m ≠ i₀ := by intro he; subst he; omega
            simp [e', eU, Pi.single_apply, this])⟩
    · rcases f_cases (lA (e' i₀ 1)) with h1 | h1
      · right; left
        refine ⟨⟨e' i₀ 1, h1⟩,
          fun v => by simp [z₁K, e', eU, Pi.single_apply]; ring,
          fun v => by simp [z₂K, e', eU, Pi.single_apply],
          fun j v => by
            have heq : (x₀ + (v + ⟨e' i₀ 1, h1⟩).1).1 = (x₀ + v.1).1 + (e' i₀ 1).1 := by
              simp [add_assoc]
            rw [heq]
            exact Ptilde_indep Y j.val (by omega) _ _ (fun m hm => by
              have : m ≠ i₀ := by intro he; subst he; omega
              simp [e', eU, Pi.single_apply, this])⟩
      · right; right
        have h12 : lA (e' i₀ 1 + e' i₀ 2) = 0 := by rw [map_add, h1, h2, f_add_self]
        refine ⟨⟨e' i₀ 1 + e' i₀ 2, h12⟩,
          fun v => by simp [z₁K, e', eU, Pi.single_apply]; ring,
          fun v => by simp [z₂K, e', eU, Pi.single_apply]; ring,
          fun j v => by
            have heq : (x₀ + (v + ⟨e' i₀ 1 + e' i₀ 2, h12⟩).1).1 = (x₀ + v.1).1 + (e' i₀ 1 + e' i₀ 2).1 := by
              simp [add_assoc]
            rw [heq]
            exact Ptilde_indep Y j.val (by omega) _ _ (fun m hm => by
              have : m ≠ i₀ := by intro he; subst he; omega
              simp [e', eU, Pi.single_apply, this])⟩
  have hPK_eq : (fun v : K => Ptilde Y i₀.val i₀.isLt (x₀ + v.1).1) =
      fun v : K => (z₁K v + ∑ j : Fin i₀.val, (Y.a i₀).lp j * Ptilde Y j.val (by omega) (x₀ + v.1).1) *
        (z₂K v + ∑ j : Fin i₀.val, (Y.b i₀).lp j * Ptilde Y j.val (by omega) (x₀ + v.1).1) := by
    funext v; rw [Ptilde]
  have hPK_quad' : isQuadG (fun v : K => (z₁K v + ∑ j : Fin i₀.val, (Y.a i₀).lp j * Ptilde Y j.val (by omega) (x₀ + v.1).1) *
      (z₂K v + ∑ j : Fin i₀.val, (Y.b i₀).lp j * Ptilde Y j.val (by omega) (x₀ + v.1).1)) := by
    rw [← hPK_eq]; exact hPK_quad
  have hlinK' := quad_prod_linearize
    (fun j : Fin i₀.val => fun v : K => Ptilde Y j.val (by omega) (x₀ + v.1).1)
    z₁K z₂K hz₁K hz₂K (Y.a i₀).lp (Y.b i₀).lp hPK_quad' hshiftK
  have hlinK : (∃ a' b' : K → F, isAffG a' ∧ isAffG b' ∧
      ∀ v : K, Ptilde Y i₀.val i₀.isLt (x₀ + v.1).1 = a' v * b' v) ∨
    (∃ a' : K → F, ∃ w : Fin i₀.val → F, isAffG a' ∧
      ∀ v : K, Ptilde Y i₀.val i₀.isLt (x₀ + v.1).1 =
        a' v + ∑ j : Fin i₀.val, w j * Ptilde Y j.val (by omega) (x₀ + v.1).1) := by
    rcases hlinK' with ⟨a', b', ha', hb', heq⟩ | ⟨a', w, ha', heq⟩
    · exact Or.inl ⟨a', b', ha', hb', fun v => (congrFun hPK_eq v).trans (heq v)⟩
    · exact Or.inr ⟨a', w, ha', fun v => (congrFun hPK_eq v).trans (heq v)⟩
  let projK : H → K := fun h => ⟨h + x₀ + (A h + 1) • eA, by
    rw [LinearMap.mem_ker, map_add, map_add, map_smul, smul_eq_mul, hlAe, mul_one]
    have h1 := hlA h; have h2 := hlA x₀; rw [hAx₀] at h2
    have hlh : lA h = A h + cA := by
      have := congrArg (· + cA) h1
      have h2' : cA + lA h + cA = lA h := by
        rw [add_comm cA (lA h), add_assoc, f_add_self, add_zero]
      rw [h2'] at this; exact this.symm
    have hlx : lA x₀ = 1 + cA := by
      have := congrArg (· + cA) h2
      have h2' : cA + lA x₀ + cA = lA x₀ := by
        rw [add_comm cA (lA x₀), add_assoc, f_add_self, add_zero]
      rw [h2'] at this; exact this.symm
    rw [hlh, hlx]
    have : A h + cA + (1 + cA) + (A h + 1) = (A h + A h) + (cA + cA) + (1 + 1) := by ring
    rw [this]; simp only [f_add_self, zero_add]⟩
  have hprojK_eq : ∀ h : H, A h = 1 → x₀ + (projK h).1 = h := by
    intro h hAh
    change x₀ + (h + x₀ + (A h + 1) • eA) = h
    rw [hAh, f_add_self, zero_smul, add_zero]
    have hxx : x₀ + x₀ = 0 := by
      apply Subtype.ext; funext p; exact f_add_self _
    rw [add_comm h x₀, ← add_assoc, hxx, zero_add]
  have hext_aff : ∀ f : K → F, isAffG f → isAffG (fun h : H => f (projK h)) := by
    intro f hf
    obtain ⟨cf, lf, hlf⟩ := isAffG_exists_linear hf
    have hfun : (fun h : H => f (projK h)) = fun h : H =>
        (cf + lf (projK 0)) + (lf (projK h) + lf (projK 0)) := by
      funext h; rw [hlf (projK h)]
      have : cf + lf (projK 0) + (lf (projK h) + lf (projK 0)) =
          cf + lf (projK h) + (lf (projK 0) + lf (projK 0)) := by ring
      rw [this, f_add_self, add_zero]
    rw [hfun]
    have hlin : ∀ h₁ h₂ : H, projK (h₁ + h₂) + projK 0 = projK h₁ + projK h₂ := by
      intro h₁ h₂
      apply Subtype.ext
      change (h₁ + h₂ + x₀ + (A (h₁ + h₂) + 1) • eA) + (0 + x₀ + (A 0 + 1) • eA) =
        (h₁ + x₀ + (A h₁ + 1) • eA) + (h₂ + x₀ + (A h₂ + 1) • eA)
      have hAadd : A (h₁ + h₂) + A 0 = A h₁ + A h₂ := by
        rw [hlA, hlA, hlA, hlA, map_add, map_zero, add_zero]
        have : cA + (lA h₁ + lA h₂) + cA = (cA + cA) + (lA h₁ + lA h₂) := by ring
        have h' : cA + lA h₁ + (cA + lA h₂) = (cA + cA) + (lA h₁ + lA h₂) := by ring
        rw [this, h']
      have hcoeff : (A (h₁ + h₂) + 1) + (A 0 + 1) = (A h₁ + 1) + (A h₂ + 1) := by
        have : A (h₁ + h₂) + 1 + (A 0 + 1) = (A (h₁ + h₂) + A 0) + (1 + 1) := by ring
        have h' : A h₁ + 1 + (A h₂ + 1) = (A h₁ + A h₂) + (1 + 1) := by ring
        rw [this, h', hAadd]
      rw [zero_add]
      have hl : h₁ + h₂ + x₀ + (A (h₁ + h₂) + 1) • eA + (x₀ + (A 0 + 1) • eA) =
          (h₁ + h₂ + x₀ + x₀) + ((A (h₁ + h₂) + 1) + (A 0 + 1)) • eA := by
        rw [add_smul (A (h₁ + h₂) + 1) (A 0 + 1) eA]; abel
      have hr : h₁ + x₀ + (A h₁ + 1) • eA + (h₂ + x₀ + (A h₂ + 1) • eA) =
          (h₁ + h₂ + x₀ + x₀) + ((A h₁ + 1) + (A h₂ + 1)) • eA := by
        rw [add_smul (A h₁ + 1) (A h₂ + 1) eA]; abel
      rw [hl, hr, hcoeff]
    let linMap : H →ₗ[F] F :=
      { toFun := fun h => lf (projK h) + lf (projK 0)
        map_add' := fun h₁ h₂ => by
          have := congrArg lf (hlin h₁ h₂)
          rw [map_add, map_add] at this
          rw [this]
          have : (lf (projK h₁) + lf (projK 0)) + (lf (projK h₂) + lf (projK 0)) =
              lf (projK h₁) + lf (projK h₂) + (lf (projK 0) + lf (projK 0)) := by ring
          rw [this, f_add_self, add_zero]
        map_smul' := fun r h => by
          rcases f_cases r with rfl | rfl
          · simp [f_add_self]
          · simp }
    exact isAffG_add (isAffG_const _) (isAffG_of_linear linMap)
  rcases hlinK with ⟨a', b', ha', hb', hprod⟩ | ⟨a', w', ha', hlin⟩
  · have hother_all : ∀ k : Fin r, ∃ a b : H → F, isAffG a ∧ isAffG b ∧
        ∀ h : H, (h.1 (k, 0) + β k) * Ptilde Y k.val k.isLt h.1 = (h.1 (k, 0) + β k) * a h * b h := by
      intro k
      by_cases hki : k = i₀
      · subst hki
        refine ⟨fun h => a' (projK h), fun h => b' (projK h), hext_aff a' ha', hext_aff b' hb', fun h => ?_⟩
        rcases f_cases (A h) with h0 | h1
        · change A h * _ = A h * _ * _; rw [h0, zero_mul, zero_mul, zero_mul]
        · change A h * _ = A h * _ * _
          rw [h1, one_mul, one_mul]
          have := hprod (projK h)
          rw [hprojK_eq h h1] at this
          exact this
      · obtain ⟨a, b, ha, hb, hab⟩ := hP_other_aff k hki
        exact ⟨a, b, ha, hb, fun h => by rw [hab h]; ring⟩
    choose aH bH haH hbH habH using hother_all
    exact hfinish r le_rfl (fun _ => 0)
      (fun k h => h.1 (k, 0) + β k) aH bH
      (isQuadG_of_isAffG (isAffG_const 0))
      (fun k => ⟨isAffG_add (isAffG_of_linear ((LinearMap.proj (k, (0 : Fin 3))).comp H.subtype)) (isAffG_const _), haH k, hbH k⟩)
      (fun h => by simp only [Ftilde, zero_add]; apply Finset.sum_congr rfl; intro k _; exact habH k h)
  · have hAi₀ : ∀ h : H, A h * Ptilde Y i₀.val i₀.isLt h.1 =
        A h * a' (projK h) + ∑ j : Fin i₀.val, w' j * A h * Ptilde Y j.val (by omega) h.1 := by
      intro h
      rcases f_cases (A h) with h0 | h1
      · simp [h0]
      · rw [h1, one_mul, one_mul]
        have := hlin (projK h)
        rw [hprojK_eq h h1] at this
        rw [this]; congr 1
        apply Finset.sum_congr rfl; intro j _
        rw [mul_one]
    let r' := r - 1
    have hr' : r' + 1 = r := by have := i₀.isLt; omega
    let pick : Fin r' → Fin r := fun j => ((i₀.cast hr'.symm).succAbove j).cast hr'
    have hpick_ne : ∀ j : Fin r', pick j ≠ i₀ := fun j he =>
      Fin.succAbove_ne (i₀.cast hr'.symm) j (Fin.ext (by simpa [pick] using congrArg Fin.val he))
    have hother_pick : ∀ j : Fin r', ∃ a b : H → F, isAffG a ∧ isAffG b ∧
        ∀ h : H, Ptilde Y (pick j).val (pick j).isLt h.1 = a h * b h :=
      fun j => hP_other_aff (pick j) (hpick_ne j)
    choose ao bo hao hbo habo using hother_pick
    let M' : Fin r' → H → F := fun j h =>
      let k := pick j
      (h.1 (k, 0) + β k) + (if hk : k.val < i₀.val then w' ⟨k.val, hk⟩ * A h else 0)
    have hM'_aff : ∀ j : Fin r', isAffG (M' j) := fun j => by
      dsimp only [M']
      apply isAffG_add (isAffG_add (isAffG_of_linear ((LinearMap.proj (pick j, (0 : Fin 3))).comp H.subtype)) (isAffG_const _))
      split_ifs with hk
      · rcases f_cases (w' ⟨_, hk⟩) with hw | hw
        · simp only [hw, zero_mul]; exact isAffG_const 0
        · simp only [hw, one_mul]; exact hA_aff
      · exact isAffG_const 0
    have hsum_less : ∀ h : H, Ftilde h.1 = A h * a' (projK h) + ∑ j : Fin r', M' j h * ao j h * bo j h := by
      intro h
      simp only [Ftilde]
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i₀)]
      change A h * Ptilde Y i₀.val i₀.isLt h.1 + _ = _
      rw [hAi₀ h]
      have hbij : ∀ (f : Fin r → F),
          ∑ k ∈ Finset.univ.erase i₀, f k = ∑ j : Fin r', f (pick j) := by
        intro f; symm
        apply Finset.sum_bij (fun j _ => pick j)
        · intro j _; exact Finset.mem_erase.mpr ⟨hpick_ne j, Finset.mem_univ _⟩
        · intro a _ b _ hab
          exact Fin.succAbove_right_injective (p := i₀.cast hr'.symm)
            (Fin.ext (by simpa [pick] using congrArg Fin.val hab))
        · intro k hk
          have hk' : k.cast hr'.symm ≠ i₀.cast hr'.symm := fun he =>
            (Finset.mem_erase.mp hk).1 (Fin.ext (by simpa using congrArg Fin.val he))
          obtain ⟨j, hj⟩ := Fin.exists_succAbove_eq hk'
          exact ⟨j, Finset.mem_univ _, Fin.ext (by simpa [pick] using congrArg Fin.val hj)⟩
        · intro j _; rfl
      have hlt_sum : (∑ j : Fin i₀.val, w' j * A h * Ptilde Y j.val (by omega) h.1) =
          ∑ k ∈ Finset.univ.erase i₀, (if hk : k.val < i₀.val then w' ⟨k.val, hk⟩ * A h else 0) * Ptilde Y k.val k.isLt h.1 := by
        have hrw : (∑ k ∈ Finset.univ.erase i₀, (if hk : k.val < i₀.val then w' ⟨k.val, hk⟩ * A h else 0) * Ptilde Y k.val k.isLt h.1) =
            ∑ k ∈ (Finset.univ.erase i₀).filter (fun k : Fin r => k.val < i₀.val),
              (if hk : k.val < i₀.val then w' ⟨k.val, hk⟩ * A h * Ptilde Y k.val k.isLt h.1 else 0) := by
          rw [Finset.sum_filter]
          apply Finset.sum_congr rfl; intro k _
          split_ifs <;> simp
        rw [hrw]
        symm
        apply Finset.sum_bij (fun k hk => ⟨k.val, (Finset.mem_filter.mp hk).2⟩)
        · intro _ _; exact Finset.mem_univ _
        · intro a _ b _ hab; exact Fin.ext (by simpa using congrArg Fin.val hab)
        · intro j _
          refine ⟨⟨j.val, by omega⟩, Finset.mem_filter.mpr ⟨Finset.mem_erase.mpr
            ⟨by intro he; have := congrArg Fin.val he; dsimp at this; omega, Finset.mem_univ _⟩, j.isLt⟩, rfl⟩
        · intro k hk
          have hlt : k.val < i₀.val := (Finset.mem_filter.mp hk).2
          simp only [hlt, dite_true]
      rw [add_assoc, hlt_sum, ← Finset.sum_add_distrib, hbij]
      congr 1
      apply Finset.sum_congr rfl; intro j _
      rw [habo j h]; simp only [M']; ring
    exact hfinish r' (by omega) (fun h => A h * a' (projK h)) M' ao bo
      (isQuadG_mul_aff hA_aff (hext_aff a' ha'))
      (fun j => ⟨hM'_aff j, hao j, hbo j⟩) hsum_less

lemma slp_to_triples {n c r : ℕ} {g : V n → F} {R : Submodule F (V n)}
    (hg : cubic g) (hR : ∀ u : V n, u ∈ R ↔ ∀ v w : V n, third g u v w = 0)
    (hdc : (n - Module.finrank F R) + 1 = 3 * c) (hrc : r ≤ c)
    (Y : YSLP n r) (q₀ : V n → F) (ℓ : Fin r → V n) (β : Fin r → F)
    (hq₀ : quad q₀)
    (hg_eq : ∀ y : V n, g y = q₀ y + ∑ i : Fin r, (dotProduct (ℓ i) y + β i) * Y.evalFull y i) :
    ∃ (L : V n →ₗ[F] E c) (q : V n → F),
      quad q ∧ ∀ y : V n, g y = q y + ∑ i : Fin c, L y (i, 0) * L y (i, 1) * L y (i, 2) := by
  classical
  let L₀ : V n →ₗ[F] E r :=
    { toFun := fun y p => match p.2 with
        | ⟨0, _⟩ => dotProduct (ℓ p.1) y
        | ⟨1, _⟩ => dotProduct (Y.a p.1).ly y
        | ⟨2, _⟩ => dotProduct (Y.b p.1).ly y
      map_add' := fun y₁ y₂ => by funext ⟨i, s⟩; fin_cases s <;> simp [dotProduct_add]
      map_smul' := fun s y => by funext ⟨i, k⟩; fin_cases k <;> simp [dotProduct_smul] }
  let Ftilde : E r → F := fun z => ∑ i : Fin r, (z (i, 0) + β i) * Ptilde Y i.val i.isLt z
  have hgF : ∀ y : V n, g y = q₀ y + Ftilde (L₀ y) := by
    intro y
    rw [hg_eq y]
    congr 1
    apply Finset.sum_congr rfl; intro i _
    rw [Ptilde_eval Y ℓ i.val i.isLt y]; rfl
  have hker_le : LinearMap.ker L₀ ≤ R := by
    intro u hu
    rw [hR]
    intro v w
    have hLu : L₀ u = 0 := LinearMap.mem_ker.mp hu
    have hdiff_F : diff (fun y => Ftilde (L₀ y)) u = fun _ => 0 := by
      funext y; simp [diff_eq_add, map_add, hLu, f_add_self]
    have hg_fun : g = fun y => q₀ y + Ftilde (L₀ y) := funext hgF
    rw [hg_fun, third_add_fun, third_quad hq₀, zero_add]
    unfold third
    rw [hdiff_F]
    have h2 : diff (fun _ : V n => (0 : F)) v = fun _ => 0 := funext (diff_const 0 v)
    rw [h2, diff_const]
  have hRle : Module.finrank F R ≤ n := by
    have := Submodule.finrank_le R; simpa [Module.finrank_fin_fun] using this
  have hdim_range : 3 * c - 1 ≤ Module.finrank F (LinearMap.range L₀) ∧
      Module.finrank F (LinearMap.range L₀) ≤ 3 * r := by
    have h1 := LinearMap.finrank_range_add_finrank_ker L₀
    rw [Module.finrank_fin_fun] at h1
    have h2 : Module.finrank F (LinearMap.ker L₀) ≤ Module.finrank F R := Submodule.finrank_mono hker_le
    have h3 : Module.finrank F (LinearMap.range L₀) ≤ 3 * r := by
      have := Submodule.finrank_le (LinearMap.range L₀)
      rw [Module.finrank_fintype_fun_eq_card, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin] at this
      omega
    omega
  have hr_eq : r = c := by omega
  subst hr_eq
  let H := LinearMap.range L₀
  let L₀H : V n →ₗ[F] H := L₀.rangeRestrict
  have hL₀H_surj : Function.Surjective L₀H := LinearMap.surjective_rangeRestrict L₀
  have hFH_cub : isCubG (fun h : H => Ftilde h.1) := by
    intro a b d e x
    obtain ⟨ua, rfl⟩ := hL₀H_surj a
    obtain ⟨ub, rfl⟩ := hL₀H_surj b
    obtain ⟨ud, rfl⟩ := hL₀H_surj d
    obtain ⟨ue, rfl⟩ := hL₀H_surj e
    obtain ⟨ux, rfl⟩ := hL₀H_surj x
    have hstep : ∀ (f : E r → F) (w : V n),
        (fun y => diffG (fun h : H => f h.1) (L₀H w) (L₀H y)) =
          diff (fun y => f (L₀ y)) w := by
      intro f w; funext y; simp [diffG, diff_eq_add, map_add]; rfl
    have h4 : diffG (diffG (diffG (diffG (fun h : H => Ftilde h.1) (L₀H ua)) (L₀H ub)) (L₀H ud))
        (L₀H ue) (L₀H ux) =
        diff (diff (diff (diff (fun y => Ftilde (L₀ y)) ua) ub) ud) ue ux := by
      simp only [diffG, diff_eq_add, map_add]; rfl
    rw [h4]
    have hF_eq : (fun y => Ftilde (L₀ y)) = fun y => g y + q₀ y := by
      funext y; rw [hgF y]
      have : q₀ y + Ftilde (L₀ y) + q₀ y = (q₀ y + q₀ y) + Ftilde (L₀ y) := by ring
      rw [this, f_add_self, zero_add]
    rw [hF_eq]
    have hadd4 : ∀ (f₁ f₂ : V n → F),
        diff (diff (diff (diff (fun y => f₁ y + f₂ y) ua) ub) ud) ue ux =
          diff (diff (diff (diff f₁ ua) ub) ud) ue ux + diff (diff (diff (diff f₂ ua) ub) ud) ue ux := by
      intro f₁ f₂
      have e1 : diff (fun y => f₁ y + f₂ y) ua = fun y => diff f₁ ua y + diff f₂ ua y :=
        funext (diff_add_fun f₁ f₂ ua)
      rw [e1]
      have e2 : diff (fun y => diff f₁ ua y + diff f₂ ua y) ub =
          fun y => diff (diff f₁ ua) ub y + diff (diff f₂ ua) ub y := funext (diff_add_fun _ _ ub)
      rw [e2]
      have e3 : diff (fun y => diff (diff f₁ ua) ub y + diff (diff f₂ ua) ub y) ud =
          fun y => diff (diff (diff f₁ ua) ub) ud y + diff (diff (diff f₂ ua) ub) ud y :=
        funext (diff_add_fun _ _ ud)
      rw [e3, diff_add_fun]
    rw [hadd4, hg ua ub ud ue ux, zero_add]
    have hq3 : diff (diff (diff q₀ ua) ub) ud = fun _ => 0 := funext (diff3_quad hq₀ ua ub ud)
    rw [hq3, diff_const]
  have hdiff_F_e0 : ∀ (k : Fin r) (z : E r),
      diffG Ftilde (Pi.single (k, (0 : Fin 3)) (1 : F)) z = Ptilde Y k.val k.isLt z := by
    intro k z
    simp only [diffG, Ftilde, ← Finset.sum_add_distrib]
    rw [Finset.sum_eq_single k]
    · have hind : Ptilde Y k.val k.isLt (z + Pi.single (k, (0 : Fin 3)) 1) = Ptilde Y k.val k.isLt z :=
        Ptilde_indep Y k.val k.isLt z _ (fun j _ => by simp [Pi.single_apply])
      rw [hind]
      simp only [Pi.add_apply, Pi.single_apply, ite_true]
      have : (z (k, 0) + 1 + β k) * Ptilde Y k.val k.isLt z +
          (z (k, 0) + β k) * Ptilde Y k.val k.isLt z =
          ((z (k, 0) + β k) * Ptilde Y k.val k.isLt z + (z (k, 0) + β k) * Ptilde Y k.val k.isLt z) +
          Ptilde Y k.val k.isLt z := by ring
      rw [this, f_add_self, zero_add]
    · intro j _ hjk
      have hind : Ptilde Y j.val j.isLt (z + Pi.single (k, (0 : Fin 3)) 1) = Ptilde Y j.val j.isLt z :=
        Ptilde_indep Y j.val j.isLt z _ (fun m _ => by simp [Pi.single_apply])
      rw [hind]
      have hne : (j, (0 : Fin 3)) ≠ (k, (0 : Fin 3)) := fun h => hjk (congrArg Prod.fst h)
      simp only [Pi.add_apply, Pi.single_apply, hne, ite_false, add_zero, f_add_self]
    · intro hk; exact (hk (Finset.mem_univ k)).elim
  have hH_ne_top : Module.finrank F H ≠ 3 * r := by
    intro htop_dim
    have hH_top : H = ⊤ := by
      apply Submodule.eq_top_of_finrank_eq
      rw [htop_dim, Module.finrank_fintype_fun_eq_card, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin]
      ring
    have hL₀_surj : Function.Surjective L₀ := LinearMap.range_eq_top.mp hH_top
    have hF_cub : isCubG Ftilde := by
      intro a b d e x
      exact hFH_cub ⟨a, hH_top ▸ Submodule.mem_top⟩ ⟨b, hH_top ▸ Submodule.mem_top⟩
        ⟨d, hH_top ▸ Submodule.mem_top⟩ ⟨e, hH_top ▸ Submodule.mem_top⟩
        ⟨x, hH_top ▸ Submodule.mem_top⟩
    have hP_quad : ∀ k : Fin r, isQuadG (Ptilde Y k.val k.isLt) := by
      intro k
      have heq : Ptilde Y k.val k.isLt = diffG Ftilde (Pi.single (k, (0 : Fin 3)) 1) :=
        (funext (hdiff_F_e0 k)).symm
      rw [heq]; exact fun a b d x => hF_cub (Pi.single (k, 0) 1) a b d x
    have hAB_aff : ∀ k : Fin r,
        isAffG (fun z : E r => z (k, 1) + (Y.a k).c0 + ∑ j : Fin k.val, (Y.a k).lp j * Ptilde Y j.val (by omega) z) ∧
        isAffG (fun z : E r => z (k, 2) + (Y.b k).c0 + ∑ j : Fin k.val, (Y.b k).lp j * Ptilde Y j.val (by omega) z) := by
      intro k
      have he1 : ∀ z, diffG (Ptilde Y k.val k.isLt) (Pi.single (k, (1 : Fin 3)) 1) z =
          z (k, 2) + (Y.b k).c0 + ∑ j : Fin k.val, (Y.b k).lp j * Ptilde Y j.val (by omega) z := by
        intro z
        simp only [diffG]; rw [Ptilde, Ptilde]
        have h1 : ∀ j : Fin k.val, Ptilde Y j.val (by omega) (z + Pi.single (k, (1 : Fin 3)) 1) =
            Ptilde Y j.val (by omega) z := fun j =>
          Ptilde_indep Y j.val (by omega) z _ (fun m hm => by
            have hmk : m ≠ k := by intro h; subst h; omega
            simp [Pi.single_apply, hmk])
        simp_rw [h1]
        have hp1 : (z + (Pi.single (k, (1 : Fin 3)) (1 : F) : E r)) (k, 1) = z (k, 1) + 1 := by
          simp [Pi.single_apply]
        have hp2 : (z + (Pi.single (k, (1 : Fin 3)) (1 : F) : E r)) (k, 2) = z (k, 2) := by
          simp [Pi.single_apply]
        rw [hp1, hp2]
        set A := z (k, 1) + (Y.a k).c0 + ∑ j : Fin k.val, (Y.a k).lp j * Ptilde Y j.val (by omega) z
        set B := z (k, 2) + (Y.b k).c0 + ∑ j : Fin k.val, (Y.b k).lp j * Ptilde Y j.val (by omega) z
        have : (z (k, 1) + 1 + (Y.a k).c0 + ∑ j : Fin k.val, (Y.a k).lp j * Ptilde Y j.val (by omega) z) * B + A * B =
            (A * B + A * B) + B := by simp only [A]; ring
        rw [this, f_add_self, zero_add]
      have he2 : ∀ z, diffG (Ptilde Y k.val k.isLt) (Pi.single (k, (2 : Fin 3)) 1) z =
          z (k, 1) + (Y.a k).c0 + ∑ j : Fin k.val, (Y.a k).lp j * Ptilde Y j.val (by omega) z := by
        intro z
        simp only [diffG]; rw [Ptilde, Ptilde]
        have h1 : ∀ j : Fin k.val, Ptilde Y j.val (by omega) (z + Pi.single (k, (2 : Fin 3)) 1) =
            Ptilde Y j.val (by omega) z := fun j =>
          Ptilde_indep Y j.val (by omega) z _ (fun m hm => by
            have hmk : m ≠ k := by intro h; subst h; omega
            simp [Pi.single_apply, hmk])
        simp_rw [h1]
        have hp1 : (z + (Pi.single (k, (2 : Fin 3)) (1 : F) : E r)) (k, 1) = z (k, 1) := by
          simp [Pi.single_apply]
        have hp2 : (z + (Pi.single (k, (2 : Fin 3)) (1 : F) : E r)) (k, 2) = z (k, 2) + 1 := by
          simp [Pi.single_apply]
        rw [hp1, hp2]
        set A := z (k, 1) + (Y.a k).c0 + ∑ j : Fin k.val, (Y.a k).lp j * Ptilde Y j.val (by omega) z
        set B := z (k, 2) + (Y.b k).c0 + ∑ j : Fin k.val, (Y.b k).lp j * Ptilde Y j.val (by omega) z
        have : A * (z (k, 2) + 1 + (Y.b k).c0 + ∑ j : Fin k.val, (Y.b k).lp j * Ptilde Y j.val (by omega) z) + A * B =
            (A * B + A * B) + A := by simp only [B]; ring
        rw [this, f_add_self, zero_add]
      exact ⟨by rw [← funext he2]; exact fun a b x => hP_quad k (Pi.single (k, 2) 1) a b x,
             by rw [← funext he1]; exact fun a b x => hP_quad k (Pi.single (k, 1) 1) a b x⟩
    let a₀ : Fin r → E r → F := fun k z => z (k, 0) + β k
    let a₁ : Fin r → E r → F := fun k z => z (k, 1) + (Y.a k).c0 + ∑ j : Fin k.val, (Y.a k).lp j * Ptilde Y j.val (by omega) z
    let a₂ : Fin r → E r → F := fun k z => z (k, 2) + (Y.b k).c0 + ∑ j : Fin k.val, (Y.b k).lp j * Ptilde Y j.val (by omega) z
    have ha_aff : ∀ k, isAffG (a₀ k) ∧ isAffG (a₁ k) ∧ isAffG (a₂ k) := fun k =>
      ⟨isAffG_add (isAffG_of_linear (LinearMap.proj (R := F) (φ := fun _ : Fin r × Fin 3 => F) (k, (0 : Fin 3)))) (isAffG_const (β k)),
       (hAB_aff k).1, (hAB_aff k).2⟩
    let Phi : E r →ₗ[F] E r :=
      { toFun := fun z p => match p.2 with
          | ⟨0, _⟩ => z (p.1, 0)
          | ⟨1, _⟩ => a₁ p.1 z + a₁ p.1 0
          | ⟨2, _⟩ => a₂ p.1 z + a₂ p.1 0
        map_add' := fun z₁ z₂ => by
          funext ⟨k, s⟩; fin_cases s
          · rfl
          · obtain ⟨c₁, l₁, hl₁⟩ := isAffG_exists_linear (ha_aff k).2.1
            simp only [Pi.add_apply, hl₁, map_add, map_zero, add_zero]
            have h : c₁ + (l₁ z₁ + l₁ z₂) + c₁ = (c₁ + c₁) + (l₁ z₁ + l₁ z₂) := by ring
            have h1 : c₁ + l₁ z₁ + c₁ = (c₁ + c₁) + l₁ z₁ := by ring
            have h2 : c₁ + l₁ z₂ + c₁ = (c₁ + c₁) + l₁ z₂ := by ring
            rw [h, h1, h2]; simp only [f_add_self, zero_add]
          · obtain ⟨c₂, l₂, hl₂⟩ := isAffG_exists_linear (ha_aff k).2.2
            simp only [Pi.add_apply, hl₂, map_add, map_zero, add_zero]
            have h : c₂ + (l₂ z₁ + l₂ z₂) + c₂ = (c₂ + c₂) + (l₂ z₁ + l₂ z₂) := by ring
            have h1 : c₂ + l₂ z₁ + c₂ = (c₂ + c₂) + l₂ z₁ := by ring
            have h2 : c₂ + l₂ z₂ + c₂ = (c₂ + c₂) + l₂ z₂ := by ring
            rw [h, h1, h2]; simp only [f_add_self, zero_add]
        map_smul' := fun s z => by
          rcases f_cases s with rfl | rfl
          · funext ⟨k, t⟩; fin_cases t <;> simp [f_add_self]
          · funext ⟨k, t⟩; fin_cases t <;> simp }
    have hPhi_inj : Function.Injective Phi := by
      rw [injective_iff_map_eq_zero]
      intro z hz
      have hrec : ∀ (k : ℕ) (hk : k < r),
          z (⟨k, hk⟩, 0) = 0 ∧ z (⟨k, hk⟩, 1) = 0 ∧ z (⟨k, hk⟩, 2) = 0 := by
        intro k hk
        induction k using Nat.strong_induction_on with
        | ind k ih =>
          have h0 : z (⟨k, hk⟩, 0) = 0 := congrFun hz (⟨k, hk⟩, 0)
          have hPeq : ∀ j : Fin k, Ptilde Y j.val (by omega) z = Ptilde Y j.val (by omega) 0 := by
            intro j
            have h := Ptilde_indep Y j.val (by omega) 0 z (fun m hm => by
              have hm' := ih m.val (by omega) (by omega)
              exact ⟨hm'.2.1, hm'.2.2⟩)
            simpa using h
          have h1 : a₁ ⟨k, hk⟩ z + a₁ ⟨k, hk⟩ 0 = 0 := congrFun hz (⟨k, hk⟩, 1)
          have h2 : a₂ ⟨k, hk⟩ z + a₂ ⟨k, hk⟩ 0 = 0 := congrFun hz (⟨k, hk⟩, 2)
          simp only [a₁, a₂, Pi.zero_apply, zero_add, hPeq] at h1 h2
          set S1 := ∑ j : Fin k, (Y.a ⟨k, hk⟩).lp j * Ptilde Y j.val (by omega) 0
          set S2 := ∑ j : Fin k, (Y.b ⟨k, hk⟩).lp j * Ptilde Y j.val (by omega) 0
          have hz1 : z (⟨k, hk⟩, 1) = 0 := by
            have : z (⟨k, hk⟩, 1) + (Y.a ⟨k, hk⟩).c0 + S1 + ((Y.a ⟨k, hk⟩).c0 + S1) =
                z (⟨k, hk⟩, 1) + (((Y.a ⟨k, hk⟩).c0 + S1) + ((Y.a ⟨k, hk⟩).c0 + S1)) := by ring
            rw [this, f_add_self, add_zero] at h1; exact h1
          have hz2 : z (⟨k, hk⟩, 2) = 0 := by
            have : z (⟨k, hk⟩, 2) + (Y.b ⟨k, hk⟩).c0 + S2 + ((Y.b ⟨k, hk⟩).c0 + S2) =
                z (⟨k, hk⟩, 2) + (((Y.b ⟨k, hk⟩).c0 + S2) + ((Y.b ⟨k, hk⟩).c0 + S2)) := by ring
            rw [this, f_add_self, add_zero] at h2; exact h2
          exact ⟨h0, hz1, hz2⟩
      funext ⟨k, s⟩
      have hk := hrec k.val k.isLt
      fin_cases s
      · exact hk.1
      · exact hk.2.1
      · exact hk.2.2
    have hPhi_surj : Function.Surjective Phi := LinearMap.injective_iff_surjective.mp hPhi_inj
    let L' : V n →ₗ[F] E r := Phi.comp L₀
    have hL'_surj : Function.Surjective L' := hPhi_surj.comp hL₀_surj
    let q' : V n → F := fun y => g y + ∑ i : Fin r, L' y (i, 0) * L' y (i, 1) * L' y (i, 2)
    have hq'_quad : quad q' := by
      have hdiff_eq : q' = fun y => q₀ y + ∑ i : Fin r,
          (a₀ i (L₀ y) * a₁ i (L₀ y) * a₂ i (L₀ y) + L' y (i, 0) * L' y (i, 1) * L' y (i, 2)) := by
        funext y
        simp only [q', hgF y, Ftilde]
        rw [Finset.sum_add_distrib, add_assoc]
        congr 1; congr 1
        apply Finset.sum_congr rfl; intro i _
        simp only [a₀, a₁, a₂]; rw [Ptilde]; ring
      apply quad_of_diff3_eq_zero
      intro u v w x
      rw [hdiff_eq]
      have hadd3 : ∀ (f₁ f₂ : V n → F),
          diff (diff (diff (fun y => f₁ y + f₂ y) u) v) w x =
            diff (diff (diff f₁ u) v) w x + diff (diff (diff f₂ u) v) w x := by
        intro f₁ f₂
        have e1 : diff (fun y => f₁ y + f₂ y) u = fun y => diff f₁ u y + diff f₂ u y :=
          funext (diff_add_fun f₁ f₂ u)
        rw [e1]
        have e2 : diff (fun y => diff f₁ u y + diff f₂ u y) v =
            fun y => diff (diff f₁ u) v y + diff (diff f₂ u) v y := funext (diff_add_fun _ _ v)
        rw [e2, diff_add_fun]
      rw [hadd3, diff3_quad hq₀ u v w x, zero_add]
      have hterm_quad : ∀ i : Fin r,
          isQuadG (fun z : E r => a₀ i z * a₁ i z * a₂ i z + Phi z (i, 0) * Phi z (i, 1) * Phi z (i, 2)) := by
        intro i
        have ha0 : ∀ z, a₀ i z = β i + Phi z (i, 0) := fun z => by simp [a₀, Phi, add_comm]
        have ha1 : ∀ z, a₁ i z = a₁ i 0 + Phi z (i, 1) := fun z => by
          simp only [Phi, LinearMap.coe_mk, AddHom.coe_mk]
          have : a₁ i 0 + (a₁ i z + a₁ i 0) = a₁ i z + (a₁ i 0 + a₁ i 0) := by ring
          rw [this, f_add_self, add_zero]
        have ha2 : ∀ z, a₂ i z = a₂ i 0 + Phi z (i, 2) := fun z => by
          simp only [Phi, LinearMap.coe_mk, AddHom.coe_mk]
          have : a₂ i 0 + (a₂ i z + a₂ i 0) = a₂ i z + (a₂ i 0 + a₂ i 0) := by ring
          rw [this, f_add_self, add_zero]
        have hfun : (fun z : E r => a₀ i z * a₁ i z * a₂ i z + Phi z (i, 0) * Phi z (i, 1) * Phi z (i, 2)) =
            fun z => (β i * a₁ i z * a₂ i z) + (Phi z (i, 0) * (a₁ i 0 * a₂ i z + Phi z (i, 1) * a₂ i 0)) := by
          funext z; rw [ha0 z, ha1 z, ha2 z]
          have : (β i + Phi z (i, 0)) * (a₁ i 0 + Phi z (i, 1)) * (a₂ i 0 + Phi z (i, 2)) +
              Phi z (i, 0) * Phi z (i, 1) * Phi z (i, 2) =
              (Phi z (i, 0) * Phi z (i, 1) * Phi z (i, 2) + Phi z (i, 0) * Phi z (i, 1) * Phi z (i, 2)) +
              (β i * (a₁ i 0 + Phi z (i, 1)) * (a₂ i 0 + Phi z (i, 2)) +
                Phi z (i, 0) * (a₁ i 0 * (a₂ i 0 + Phi z (i, 2)) + Phi z (i, 1) * a₂ i 0)) := by ring
          rw [this, f_add_self, zero_add]
        rw [hfun]
        have hp0 : isAffG (fun z : E r => Phi z (i, 0)) :=
          isAffG_of_linear ((LinearMap.proj (R := F) (φ := fun _ : Fin r × Fin 3 => F) (i, (0 : Fin 3))).comp Phi)
        have hp1 : isAffG (fun z : E r => Phi z (i, 1)) :=
          isAffG_of_linear ((LinearMap.proj (R := F) (φ := fun _ : Fin r × Fin 3 => F) (i, (1 : Fin 3))).comp Phi)
        have hsm : ∀ (c : F) (f : E r → F), isAffG f → isAffG (fun z => c * f z) := fun c f hf => by
          rcases f_cases c with rfl | rfl
          · simp only [zero_mul]; exact isAffG_const 0
          · simp only [one_mul]; exact hf
        apply isQuadG_add
        · exact isQuadG_mul_aff (hsm (β i) _ (ha_aff i).2.1) (ha_aff i).2.2
        · exact isQuadG_mul_aff hp0 (isAffG_add (hsm (a₁ i 0) _ (ha_aff i).2.2)
            (by have : (fun z : E r => Phi z (i, 1) * a₂ i 0) = fun z => a₂ i 0 * Phi z (i, 1) := by funext z; ring
                rw [this]; exact hsm (a₂ i 0) _ hp1))
      have hsum_q : isQuadG (fun z : E r => ∑ i : Fin r, (a₀ i z * a₁ i z * a₂ i z + Phi z (i, 0) * Phi z (i, 1) * Phi z (i, 2))) := by
        have hgen : ∀ S : Finset (Fin r),
            isQuadG (fun z : E r => ∑ i ∈ S, (a₀ i z * a₁ i z * a₂ i z + Phi z (i, 0) * Phi z (i, 1) * Phi z (i, 2))) := by
          intro S; induction S using Finset.induction_on with
          | empty => simp only [Finset.sum_empty]; exact isQuadG_of_isAffG (isAffG_const 0)
          | @insert i S hi ih =>
            have hf : (fun z : E r => ∑ j ∈ insert i S, (a₀ j z * a₁ j z * a₂ j z + Phi z (j, 0) * Phi z (j, 1) * Phi z (j, 2))) =
                fun z => (a₀ i z * a₁ i z * a₂ i z + Phi z (i, 0) * Phi z (i, 1) * Phi z (i, 2)) +
                  ∑ j ∈ S, (a₀ j z * a₁ j z * a₂ j z + Phi z (j, 0) * Phi z (j, 1) * Phi z (j, 2)) :=
              funext fun z => Finset.sum_insert hi
            rw [hf]; exact isQuadG_add (hterm_quad i) ih
        exact hgen Finset.univ
      have hpull : diff (diff (diff (fun y : V n => ∑ i : Fin r,
            (a₀ i (L₀ y) * a₁ i (L₀ y) * a₂ i (L₀ y) + L' y (i, 0) * L' y (i, 1) * L' y (i, 2))) u) v) w x =
          diffG (diffG (diffG (fun z : E r => ∑ i : Fin r,
            (a₀ i z * a₁ i z * a₂ i z + Phi z (i, 0) * Phi z (i, 1) * Phi z (i, 2))) (L₀ u)) (L₀ v)) (L₀ w) (L₀ x) := by
        simp only [diff_eq_add, diffG, L', LinearMap.comp_apply, map_add]
      rw [hpull]
      exact hsum_q (L₀ u) (L₀ v) (L₀ w) (L₀ x)
    have hg' : ∀ y : V n, g y = q' y + ∑ i : Fin r, L' y (i, 0) * L' y (i, 1) * L' y (i, 2) := by
      intro y; simp only [q', add_assoc, f_add_self, add_zero]
    exact no_surjective_triples hg hR hdc L' q' hq'_quad hg' hL'_surj
  have hH_dim : Module.finrank F H + 1 = Module.finrank F (E r) := by
    have hdr : 3 * r - 1 ≤ Module.finrank F H ∧ Module.finrank F H ≤ 3 * r := hdim_range
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin]
    omega
  have hkerL₀ : LinearMap.ker L₀ = R := by
    apply Submodule.eq_of_le_of_finrank_eq hker_le
    have h1 := LinearMap.finrank_range_add_finrank_ker L₀
    rw [Module.finrank_fin_fun] at h1
    change Module.finrank F H + Module.finrank F (LinearMap.ker L₀) = n at h1
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin] at hH_dim
    omega
  obtain ⟨α, hα_ne, hker_α⟩ := exists_hyperplane_covector H hH_dim
  have hH_mem : ∀ z : E r, z ∈ H ↔ α z = 0 := fun z => by rw [← hker_α, LinearMap.mem_ker]
  let eU : Fin r → Fin 3 → E r := fun i s => Pi.single (i, s) 1
  let I₀ : Finset (Fin r) := Finset.univ.filter (fun i => α (eU i 0) = 1)
  have hfinish : ∀ (s : ℕ) (_ : s ≤ r) (Q : H → F) (a₀ a₁ a₂ : Fin s → H → F),
      isQuadG Q → (∀ i, isAffG (a₀ i) ∧ isAffG (a₁ i) ∧ isAffG (a₂ i)) →
      (∀ h : H, Ftilde h.1 = Q h + ∑ i : Fin s, a₀ i h * a₁ i h * a₂ i h) →
      ∃ (L : V n →ₗ[F] E r) (q : V n → F),
        quad q ∧ ∀ y : V n, g y = q y + ∑ i : Fin r, L y (i, 0) * L y (i, 1) * L y (i, 2) := by
    intro s hs Q a₀ a₁ a₂ hQ ha hsum
    have hg_sum : ∀ y : V n, g y = q₀ y + Q (L₀H y) + ∑ i : Fin s, a₀ i (L₀H y) * a₁ i (L₀H y) * a₂ i (L₀H y) := by
      intro y; rw [hgF y]; change q₀ y + Ftilde (L₀H y).1 = _; rw [hsum (L₀H y)]; ring
    obtain ⟨Ls, qs, hqs, hgs⟩ := aff_triples_to_lin_triples L₀H hq₀ hQ a₀ a₁ a₂ ha hg_sum
    by_cases hlt : s < r
    · exact (no_fewer_triples hR hdc hlt Ls qs hqs hgs).elim
    · have heq : s = r := by omega
      subst heq; exact ⟨Ls, qs, hqs, hgs⟩
  have hP_quad_of_e0 : ∀ k : Fin r, k ∉ I₀ → isQuadG (fun h : H => Ptilde Y k.val k.isLt h.1) := by
    intro k hk
    have hα0 : α (eU k 0) = 0 := by
      have hne : α (eU k 0) ≠ 1 := by
        intro h1; exact hk (Finset.mem_filter.mpr ⟨Finset.mem_univ k, h1⟩)
      exact (f_cases _).resolve_right hne
    let ekH : H := ⟨eU k 0, (hH_mem _).mpr hα0⟩
    have heq : (fun h : H => Ptilde Y k.val k.isLt h.1) = diffG (fun h : H => Ftilde h.1) ekH := by
      funext h; exact (hdiff_F_e0 k h.1).symm
    rw [heq]; exact fun a b d x => hFH_cub ekH a b d x
  by_cases hI₀_empty : I₀ = ∅
  · have hP_lin : ∀ k : Fin r,
        (∃ a b : H → F, isAffG a ∧ isAffG b ∧ ∀ h : H, Ptilde Y k.val k.isLt h.1 = a h * b h) ∨
        (∃ a : H → F, ∃ w : Fin k.val → F, isAffG a ∧
          ∀ h : H, Ptilde Y k.val k.isLt h.1 = a h + ∑ j : Fin k.val, w j * Ptilde Y j.val (by omega) h.1) := by
      intro k
      have hk_not : k ∉ I₀ := by rw [hI₀_empty]; simp
      have hquad := hP_quad_of_e0 k hk_not
      let z₁ : H → F := fun h => h.1 (k, 1) + (Y.a k).c0
      let z₂ : H → F := fun h => h.1 (k, 2) + (Y.b k).c0
      have hz₁ : isAffG z₁ := isAffG_add (isAffG_of_linear ((LinearMap.proj (k, (1 : Fin 3))).comp H.subtype)) (isAffG_const _)
      have hz₂ : isAffG z₂ := isAffG_add (isAffG_of_linear ((LinearMap.proj (k, (2 : Fin 3))).comp H.subtype)) (isAffG_const _)
      have hshift :
          (∃ e₂ : H, (∀ h, z₁ (h + e₂) = z₁ h) ∧ (∀ h, z₂ (h + e₂) = z₂ h + 1) ∧
            (∀ j : Fin k.val, ∀ h, Ptilde Y j.val (by omega) (h + e₂).1 = Ptilde Y j.val (by omega) h.1)) ∨
          (∃ e₁ : H, (∀ h, z₁ (h + e₁) = z₁ h + 1) ∧ (∀ h, z₂ (h + e₁) = z₂ h) ∧
            (∀ j : Fin k.val, ∀ h, Ptilde Y j.val (by omega) (h + e₁).1 = Ptilde Y j.val (by omega) h.1)) ∨
          (∃ e₁₂ : H, (∀ h, z₁ (h + e₁₂) = z₁ h + 1) ∧ (∀ h, z₂ (h + e₁₂) = z₂ h + 1) ∧
            (∀ j : Fin k.val, ∀ h, Ptilde Y j.val (by omega) (h + e₁₂).1 = Ptilde Y j.val (by omega) h.1)) := by
        rcases f_cases (α (eU k 2)) with h2 | h2
        · left
          refine ⟨⟨eU k 2, (hH_mem _).mpr h2⟩, fun h => by simp [z₁, eU, Pi.single_apply],
            fun h => by simp [z₂, eU, Pi.single_apply]; ring, fun j h =>
              Ptilde_indep Y j.val (by omega) h.1 _ (fun m hm => by
                have : m ≠ k := by intro he; subst he; omega
                simp [eU, Pi.single_apply, this])⟩
        · rcases f_cases (α (eU k 1)) with h1 | h1
          · right; left
            refine ⟨⟨eU k 1, (hH_mem _).mpr h1⟩, fun h => by simp [z₁, eU, Pi.single_apply]; ring,
              fun h => by simp [z₂, eU, Pi.single_apply], fun j h =>
                Ptilde_indep Y j.val (by omega) h.1 _ (fun m hm => by
                  have : m ≠ k := by intro he; subst he; omega
                  simp [eU, Pi.single_apply, this])⟩
          · right; right
            have h12 : α (eU k 1 + eU k 2) = 0 := by rw [map_add, h1, h2, f_add_self]
            refine ⟨⟨eU k 1 + eU k 2, (hH_mem _).mpr h12⟩,
              fun h => by simp [z₁, eU, Pi.single_apply]; ring,
              fun h => by simp [z₂, eU, Pi.single_apply]; ring,
              fun j h => Ptilde_indep Y j.val (by omega) h.1 _ (fun m hm => by
                have : m ≠ k := by intro he; subst he; omega
                simp [eU, Pi.single_apply, this])⟩
      have hPeq : (fun h : H => Ptilde Y k.val k.isLt h.1) =
          fun h : H => (z₁ h + ∑ j : Fin k.val, (Y.a k).lp j * Ptilde Y j.val (by omega) h.1) *
            (z₂ h + ∑ j : Fin k.val, (Y.b k).lp j * Ptilde Y j.val (by omega) h.1) := by
        funext h; rw [Ptilde]
      rw [hPeq] at hquad
      have hres := quad_prod_linearize (fun j : Fin k.val => fun h : H => Ptilde Y j.val (by omega) h.1)
        z₁ z₂ hz₁ hz₂ (Y.a k).lp (Y.b k).lp hquad hshift
      rcases hres with ⟨a', b', ha', hb', heq⟩ | ⟨a', w, ha', heq⟩
      · exact Or.inl ⟨a', b', ha', hb', fun h => (congrFun hPeq h).trans (heq h)⟩
      · exact Or.inr ⟨a', w, ha', fun h => (congrFun hPeq h).trans (heq h)⟩
    obtain ⟨s, hs, Q, a₀, a₁, a₂, hQ, ha, hsum⟩ :=
      fold_linearized_sum (fun k : Fin r => fun h : H => Ptilde Y k.val k.isLt h.1)
        (fun k : Fin r => fun h : H => h.1 (k, 0) + β k)
        (fun k => isAffG_add (isAffG_of_linear ((LinearMap.proj (k, (0 : Fin 3))).comp H.subtype)) (isAffG_const _))
        hP_lin
    exact hfinish s hs Q a₀ a₁ a₂ hQ ha hsum
  · have hI₀_pos : 0 < I₀.card := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hI₀_empty)
    by_cases hI₀_ge2 : 2 ≤ I₀.card
    · let i₂ : Fin r := I₀.max' (Finset.card_pos.mp hI₀_pos)
      have hi₂_mem : i₂ ∈ I₀ := Finset.max'_mem I₀ _
      obtain ⟨i₁, hi₁_mem, hi₁_ne⟩ : ∃ i₁ ∈ I₀, i₁ ≠ i₂ := by
        have hlt : 1 < I₀.card := by omega
        obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp hlt
        by_cases ha2 : a = i₂
        · exact ⟨b, hb, fun h => hab (ha2.trans h.symm)⟩
        · exact ⟨a, ha, ha2⟩
      have hi₁_lt : i₁.val < i₂.val := by
        have hle : i₁ ≤ i₂ := Finset.le_max' I₀ i₁ hi₁_mem
        exact lt_of_le_of_ne hle (fun h => hi₁_ne (Fin.ext h))
      have hα_i₁ : α (eU i₁ 0) = 1 := (Finset.mem_filter.mp hi₁_mem).2
      have hα_i₂ : α (eU i₂ 0) = 1 := (Finset.mem_filter.mp hi₂_mem).2
      have hP_sum_quad : ∀ k ∈ I₀, isQuadG (fun h : H => Ptilde Y k.val k.isLt h.1 + Ptilde Y i₂.val i₂.isLt h.1) := by
        intro k hk
        have hαk : α (eU k 0) = 1 := (Finset.mem_filter.mp hk).2
        have hmem : eU k 0 + eU i₂ 0 ∈ H := (hH_mem _).mpr (by rw [map_add, hαk, hα_i₂, f_add_self])
        let ekH : H := ⟨eU k 0 + eU i₂ 0, hmem⟩
        have hdiff : ∀ h : H, diffG (fun x : H => Ftilde x.1) ekH h =
            Ptilde Y k.val k.isLt h.1 + Ptilde Y i₂.val i₂.isLt h.1 := by
          intro h
          have hstep : diffG Ftilde (eU k 0 + eU i₂ 0) h.1 =
              diffG Ftilde (eU k 0) (h.1 + eU i₂ 0) + diffG Ftilde (eU i₂ 0) h.1 := by
            simp only [diffG]
            have h1 : h.1 + (eU k 0 + eU i₂ 0) = h.1 + eU i₂ 0 + eU k 0 := by rw [add_comm (eU k 0), add_assoc]
            rw [h1]
            have h2 : Ftilde (h.1 + eU i₂ 0 + eU k 0) + Ftilde (h.1 + eU i₂ 0) +
                (Ftilde (h.1 + eU i₂ 0) + Ftilde h.1) =
                Ftilde (h.1 + eU i₂ 0 + eU k 0) + Ftilde h.1 +
                (Ftilde (h.1 + eU i₂ 0) + Ftilde (h.1 + eU i₂ 0)) := by ring
            rw [h2, f_add_self, add_zero]
          change diffG Ftilde (eU k 0 + eU i₂ 0) h.1 = _
          rw [hstep, hdiff_F_e0 k (h.1 + eU i₂ 0), hdiff_F_e0 i₂ h.1]
          rw [Ptilde_indep Y k.val k.isLt h.1 (eU i₂ 0) (fun m _ => by simp [eU, Pi.single_apply])]
        rw [← funext hdiff]
        exact fun a b d x => hFH_cub ekH a b d x
      let e' : Fin r → Fin 3 → H := fun k s =>
        ⟨eU k s + α (eU k s) • eU i₁ 0, (hH_mem _).mpr (by
          rw [map_add, map_smul, smul_eq_mul, hα_i₁, mul_one, f_add_self])⟩
      have hPi₂_quad : isQuadG (fun h : H => Ptilde Y i₂.val i₂.isLt h.1) := by
        have hsum_q := hP_sum_quad i₁ hi₁_mem
        have hd1 : ∀ h : H, diffG (fun x : H => Ptilde Y i₁.val i₁.isLt x.1 + Ptilde Y i₂.val i₂.isLt x.1) (e' i₂ 1) h =
            h.1 (i₂, 2) + (Y.b i₂).c0 + ∑ j : Fin i₂.val, (Y.b i₂).lp j * Ptilde Y j.val (by omega) h.1 := by
          intro h
          have hi1_inv : Ptilde Y i₁.val i₁.isLt (h + e' i₂ 1).1 = Ptilde Y i₁.val i₁.isLt h.1 :=
            Ptilde_indep Y i₁.val i₁.isLt h.1 _ (fun m hm => by
              have hne : m ≠ i₂ := by intro he; subst he; omega
              simp [e', eU, Pi.single_apply, hne])
          have hj_inv : ∀ j : Fin i₂.val, Ptilde Y j.val (by omega) (h + e' i₂ 1).1 = Ptilde Y j.val (by omega) h.1 :=
            fun j => Ptilde_indep Y j.val (by omega) h.1 _ (fun m hm => by
              have hne : m ≠ i₂ := by intro he; subst he; omega
              simp [e', eU, Pi.single_apply, hne])
          simp only [diffG, hi1_inv]
          have hcancel : (Ptilde Y i₁.val i₁.isLt h.1 + Ptilde Y i₂.val i₂.isLt (h + e' i₂ 1).1) +
              (Ptilde Y i₁.val i₁.isLt h.1 + Ptilde Y i₂.val i₂.isLt h.1) =
              (Ptilde Y i₁.val i₁.isLt h.1 + Ptilde Y i₁.val i₁.isLt h.1) +
              (Ptilde Y i₂.val i₂.isLt (h + e' i₂ 1).1 + Ptilde Y i₂.val i₂.isLt h.1) := by ring
          rw [hcancel, f_add_self, zero_add, Ptilde, Ptilde]
          simp_rw [hj_inv]
          have hc1 : (h + e' i₂ 1).1 (i₂, 1) = h.1 (i₂, 1) + 1 := by
            simp [e', eU, Pi.single_apply]
          have hc2 : (h + e' i₂ 1).1 (i₂, 2) = h.1 (i₂, 2) := by
            simp [e', eU, Pi.single_apply]
          rw [hc1, hc2]
          set A := h.1 (i₂, 1) + (Y.a i₂).c0 + ∑ j : Fin i₂.val, (Y.a i₂).lp j * Ptilde Y j.val (by omega) h.1
          set B := h.1 (i₂, 2) + (Y.b i₂).c0 + ∑ j : Fin i₂.val, (Y.b i₂).lp j * Ptilde Y j.val (by omega) h.1
          have : (h.1 (i₂, 1) + 1 + (Y.a i₂).c0 + ∑ j : Fin i₂.val, (Y.a i₂).lp j * Ptilde Y j.val (by omega) h.1) * B + A * B =
              (A * B + A * B) + B := by simp only [A]; ring
          rw [this, f_add_self, zero_add]
        have hd2 : ∀ h : H, diffG (fun x : H => Ptilde Y i₁.val i₁.isLt x.1 + Ptilde Y i₂.val i₂.isLt x.1) (e' i₂ 2) h =
            h.1 (i₂, 1) + (Y.a i₂).c0 + ∑ j : Fin i₂.val, (Y.a i₂).lp j * Ptilde Y j.val (by omega) h.1 := by
          intro h
          have hi1_inv : Ptilde Y i₁.val i₁.isLt (h + e' i₂ 2).1 = Ptilde Y i₁.val i₁.isLt h.1 :=
            Ptilde_indep Y i₁.val i₁.isLt h.1 _ (fun m hm => by
              have hne : m ≠ i₂ := by intro he; subst he; omega
              simp [e', eU, Pi.single_apply, hne])
          have hj_inv : ∀ j : Fin i₂.val, Ptilde Y j.val (by omega) (h + e' i₂ 2).1 = Ptilde Y j.val (by omega) h.1 :=
            fun j => Ptilde_indep Y j.val (by omega) h.1 _ (fun m hm => by
              have hne : m ≠ i₂ := by intro he; subst he; omega
              simp [e', eU, Pi.single_apply, hne])
          simp only [diffG, hi1_inv]
          have hcancel : (Ptilde Y i₁.val i₁.isLt h.1 + Ptilde Y i₂.val i₂.isLt (h + e' i₂ 2).1) +
              (Ptilde Y i₁.val i₁.isLt h.1 + Ptilde Y i₂.val i₂.isLt h.1) =
              (Ptilde Y i₁.val i₁.isLt h.1 + Ptilde Y i₁.val i₁.isLt h.1) +
              (Ptilde Y i₂.val i₂.isLt (h + e' i₂ 2).1 + Ptilde Y i₂.val i₂.isLt h.1) := by ring
          rw [hcancel, f_add_self, zero_add, Ptilde, Ptilde]
          simp_rw [hj_inv]
          have hc1 : (h + e' i₂ 2).1 (i₂, 1) = h.1 (i₂, 1) := by
            simp [e', eU, Pi.single_apply]
          have hc2 : (h + e' i₂ 2).1 (i₂, 2) = h.1 (i₂, 2) + 1 := by
            simp [e', eU, Pi.single_apply]
          rw [hc1, hc2]
          set A := h.1 (i₂, 1) + (Y.a i₂).c0 + ∑ j : Fin i₂.val, (Y.a i₂).lp j * Ptilde Y j.val (by omega) h.1
          set B := h.1 (i₂, 2) + (Y.b i₂).c0 + ∑ j : Fin i₂.val, (Y.b i₂).lp j * Ptilde Y j.val (by omega) h.1
          have : A * (h.1 (i₂, 2) + 1 + (Y.b i₂).c0 + ∑ j : Fin i₂.val, (Y.b i₂).lp j * Ptilde Y j.val (by omega) h.1) + A * B =
              (A * B + A * B) + A := by simp only [B]; ring
          rw [this, f_add_self, zero_add]
        have hA_aff : isAffG (fun h : H => h.1 (i₂, 1) + (Y.a i₂).c0 + ∑ j : Fin i₂.val, (Y.a i₂).lp j * Ptilde Y j.val (by omega) h.1) := by
          rw [← funext hd2]; exact fun a b x => hsum_q (e' i₂ 2) a b x
        have hB_aff : isAffG (fun h : H => h.1 (i₂, 2) + (Y.b i₂).c0 + ∑ j : Fin i₂.val, (Y.b i₂).lp j * Ptilde Y j.val (by omega) h.1) := by
          rw [← funext hd1]; exact fun a b x => hsum_q (e' i₂ 1) a b x
        have hPeq : (fun h : H => Ptilde Y i₂.val i₂.isLt h.1) =
            fun h : H => (h.1 (i₂, 1) + (Y.a i₂).c0 + ∑ j : Fin i₂.val, (Y.a i₂).lp j * Ptilde Y j.val (by omega) h.1) *
              (h.1 (i₂, 2) + (Y.b i₂).c0 + ∑ j : Fin i₂.val, (Y.b i₂).lp j * Ptilde Y j.val (by omega) h.1) := by
          funext h; rw [Ptilde]
        rw [hPeq]; exact isQuadG_mul_aff hA_aff hB_aff
      have hP_all_quad : ∀ k : Fin r, isQuadG (fun h : H => Ptilde Y k.val k.isLt h.1) := by
        intro k
        by_cases hk : k ∈ I₀
        · have hfun : (fun h : H => Ptilde Y k.val k.isLt h.1) =
              fun h : H => (Ptilde Y k.val k.isLt h.1 + Ptilde Y i₂.val i₂.isLt h.1) + Ptilde Y i₂.val i₂.isLt h.1 := by
            funext h; rw [add_assoc, f_add_self, add_zero]
          rw [hfun]; exact isQuadG_add (hP_sum_quad k hk) hPi₂_quad
        · exact hP_quad_of_e0 k hk
      have hP_lin : ∀ k : Fin r,
          (∃ a b : H → F, isAffG a ∧ isAffG b ∧ ∀ h : H, Ptilde Y k.val k.isLt h.1 = a h * b h) ∨
          (∃ a : H → F, ∃ w : Fin k.val → F, isAffG a ∧
            ∀ h : H, Ptilde Y k.val k.isLt h.1 = a h + ∑ j : Fin k.val, w j * Ptilde Y j.val (by omega) h.1) := by
        intro k
        let z₁ : H → F := fun h => h.1 (k, 1) + (Y.a k).c0
        let z₂ : H → F := fun h => h.1 (k, 2) + (Y.b k).c0
        have hz₁ : isAffG z₁ := isAffG_add (isAffG_of_linear ((LinearMap.proj (k, (1 : Fin 3))).comp H.subtype)) (isAffG_const _)
        have hz₂ : isAffG z₂ := isAffG_add (isAffG_of_linear ((LinearMap.proj (k, (2 : Fin 3))).comp H.subtype)) (isAffG_const _)
        have hPeq : (fun h : H => Ptilde Y k.val k.isLt h.1) =
            fun h : H => (z₁ h + ∑ j : Fin k.val, (Y.a k).lp j * Ptilde Y j.val (by omega) h.1) *
              (z₂ h + ∑ j : Fin k.val, (Y.b k).lp j * Ptilde Y j.val (by omega) h.1) := by
          funext h; rw [Ptilde]
        have hqk := hP_all_quad k
        rw [hPeq] at hqk
        have hres := quad_prod_linearize (fun j : Fin k.val => fun h : H => Ptilde Y j.val (by omega) h.1)
          z₁ z₂ hz₁ hz₂ (Y.a k).lp (Y.b k).lp hqk
          (Or.inl ⟨e' k 2,
            fun h => by simp [z₁, e', eU, Pi.single_apply],
            fun h => by simp [z₂, e', eU, Pi.single_apply]; ring,
            fun j h => Ptilde_indep Y j.val (by omega) h.1 _ (fun m hm => by
              have : m ≠ k := by intro he; subst he; omega
              simp [e', eU, Pi.single_apply, this])⟩)
        rcases hres with ⟨a', b', ha', hb', heq⟩ | ⟨a', w, ha', heq⟩
        · exact Or.inl ⟨a', b', ha', hb', fun h => (congrFun hPeq h).trans (heq h)⟩
        · exact Or.inr ⟨a', w, ha', fun h => (congrFun hPeq h).trans (heq h)⟩
      obtain ⟨s, hs, Q, a₀, a₁, a₂, hQ, ha, hsum⟩ :=
        fold_linearized_sum (fun k : Fin r => fun h : H => Ptilde Y k.val k.isLt h.1)
          (fun k : Fin r => fun h : H => h.1 (k, 0) + β k)
          (fun k => isAffG_add (isAffG_of_linear ((LinearMap.proj (k, (0 : Fin 3))).comp H.subtype)) (isAffG_const _))
          hP_lin
      exact hfinish s hs Q a₀ a₁ a₂ hQ ha hsum
    · have hI₀_one : I₀.card = 1 := by omega
      obtain ⟨i₀, hi₀_eq⟩ := Finset.card_eq_one.mp hI₀_one
      have hi₀_mem : i₀ ∈ I₀ := by rw [hi₀_eq]; simp
      have hα_i₀ : α (eU i₀ 0) = 1 := (Finset.mem_filter.mp hi₀_mem).2
      let e' : Fin r → Fin 3 → H := fun k s =>
        ⟨eU k s + α (eU k s) • eU i₀ 0, (hH_mem _).mpr (by
          rw [map_add, map_smul, smul_eq_mul, hα_i₀, mul_one, f_add_self])⟩
      have hP_other_aff : ∀ k : Fin r, k ≠ i₀ →
          ∃ a b : H → F, isAffG a ∧ isAffG b ∧ ∀ h : H, Ptilde Y k.val k.isLt h.1 = a h * b h := by
        intro k hk
        have hk_not : k ∉ I₀ := by rw [hi₀_eq]; simp [hk]
        have hq := hP_quad_of_e0 k hk_not
        have hd1 : ∀ h : H, diffG (fun x : H => Ptilde Y k.val k.isLt x.1) (e' k 1) h =
            h.1 (k, 2) + (Y.b k).c0 + ∑ j : Fin k.val, (Y.b k).lp j * Ptilde Y j.val (by omega) h.1 := by
          intro h
          have hj_inv : ∀ j : Fin k.val, Ptilde Y j.val (by omega) (h + e' k 1).1 = Ptilde Y j.val (by omega) h.1 :=
            fun j => Ptilde_indep Y j.val (by omega) h.1 _ (fun m hm => by
              have hne : m ≠ k := by intro he; subst he; omega
              simp [e', eU, Pi.single_apply, hne])
          simp only [diffG]; rw [Ptilde, Ptilde]; simp_rw [hj_inv]
          have hc1 : (h + e' k 1).1 (k, 1) = h.1 (k, 1) + 1 := by simp [e', eU, Pi.single_apply]
          have hc2 : (h + e' k 1).1 (k, 2) = h.1 (k, 2) := by simp [e', eU, Pi.single_apply]
          rw [hc1, hc2]
          set A := h.1 (k, 1) + (Y.a k).c0 + ∑ j : Fin k.val, (Y.a k).lp j * Ptilde Y j.val (by omega) h.1
          set B := h.1 (k, 2) + (Y.b k).c0 + ∑ j : Fin k.val, (Y.b k).lp j * Ptilde Y j.val (by omega) h.1
          have : (h.1 (k, 1) + 1 + (Y.a k).c0 + ∑ j : Fin k.val, (Y.a k).lp j * Ptilde Y j.val (by omega) h.1) * B + A * B =
              (A * B + A * B) + B := by simp only [A]; ring
          rw [this, f_add_self, zero_add]
        have hd2 : ∀ h : H, diffG (fun x : H => Ptilde Y k.val k.isLt x.1) (e' k 2) h =
            h.1 (k, 1) + (Y.a k).c0 + ∑ j : Fin k.val, (Y.a k).lp j * Ptilde Y j.val (by omega) h.1 := by
          intro h
          have hj_inv : ∀ j : Fin k.val, Ptilde Y j.val (by omega) (h + e' k 2).1 = Ptilde Y j.val (by omega) h.1 :=
            fun j => Ptilde_indep Y j.val (by omega) h.1 _ (fun m hm => by
              have hne : m ≠ k := by intro he; subst he; omega
              simp [e', eU, Pi.single_apply, hne])
          simp only [diffG]; rw [Ptilde, Ptilde]; simp_rw [hj_inv]
          have hc1 : (h + e' k 2).1 (k, 1) = h.1 (k, 1) := by simp [e', eU, Pi.single_apply]
          have hc2 : (h + e' k 2).1 (k, 2) = h.1 (k, 2) + 1 := by simp [e', eU, Pi.single_apply]
          rw [hc1, hc2]
          set A := h.1 (k, 1) + (Y.a k).c0 + ∑ j : Fin k.val, (Y.a k).lp j * Ptilde Y j.val (by omega) h.1
          set B := h.1 (k, 2) + (Y.b k).c0 + ∑ j : Fin k.val, (Y.b k).lp j * Ptilde Y j.val (by omega) h.1
          have : A * (h.1 (k, 2) + 1 + (Y.b k).c0 + ∑ j : Fin k.val, (Y.b k).lp j * Ptilde Y j.val (by omega) h.1) + A * B =
              (A * B + A * B) + A := by simp only [B]; ring
          rw [this, f_add_self, zero_add]
        refine ⟨fun h => h.1 (k, 1) + (Y.a k).c0 + ∑ j : Fin k.val, (Y.a k).lp j * Ptilde Y j.val (by omega) h.1,
          fun h => h.1 (k, 2) + (Y.b k).c0 + ∑ j : Fin k.val, (Y.b k).lp j * Ptilde Y j.val (by omega) h.1,
          ?_, ?_, fun h => by rw [Ptilde]⟩
        · rw [← funext hd2]; exact fun a b x => hq (e' k 2) a b x
        · rw [← funext hd1]; exact fun a b x => hq (e' k 1) a b x
      let A : H → F := fun h => h.1 (i₀, 0) + β i₀
      have hA_aff : isAffG A := isAffG_add (isAffG_of_linear ((LinearMap.proj (i₀, (0 : Fin 3))).comp H.subtype)) (isAffG_const _)
      have hAP_cub : isCubG (fun h : H => A h * Ptilde Y i₀.val i₀.isLt h.1) := by
        have hsum_cub : isCubG (fun h : H => ∑ k ∈ Finset.univ.erase i₀, (h.1 (k, 0) + β k) * Ptilde Y k.val k.isLt h.1) := by
          have hgen : ∀ (S : Finset (Fin r)), (∀ k ∈ S, k ≠ i₀) →
              isCubG (fun h : H => ∑ k ∈ S, (h.1 (k, 0) + β k) * Ptilde Y k.val k.isLt h.1) := by
            intro S
            induction S using Finset.induction_on with
            | empty =>
              intro _; simp only [Finset.sum_empty]
              exact isCubG_of_isQuadG (isQuadG_of_isAffG (isAffG_const 0))
            | @insert k S hk ih =>
              intro hne
              have hfun : (fun h : H => ∑ j ∈ insert k S, (h.1 (j, 0) + β j) * Ptilde Y j.val j.isLt h.1) =
                  fun h => (h.1 (k, 0) + β k) * Ptilde Y k.val k.isLt h.1 +
                    ∑ j ∈ S, (h.1 (j, 0) + β j) * Ptilde Y j.val j.isLt h.1 := by
                funext h; exact Finset.sum_insert hk
              rw [hfun]
              apply isCubG_add
              · obtain ⟨a, b, ha, hb, hab⟩ := hP_other_aff k (hne k (Finset.mem_insert_self k S))
                have hf1 : (fun h : H => (h.1 (k, 0) + β k) * Ptilde Y k.val k.isLt h.1) =
                    fun h => (h.1 (k, 0) + β k) * (a h * b h) := funext fun h => by rw [hab h]
                rw [hf1]
                exact isCubG_mul_aff_quad
                  (isAffG_add (isAffG_of_linear ((LinearMap.proj (k, (0 : Fin 3))).comp H.subtype)) (isAffG_const _))
                  ha hb
              · exact ih (fun j hj => hne j (Finset.mem_insert_of_mem hj))
          exact hgen (Finset.univ.erase i₀) (fun k hk => (Finset.mem_erase.mp hk).1)
        have hfun : (fun h : H => A h * Ptilde Y i₀.val i₀.isLt h.1) =
            fun h => Ftilde h.1 + ∑ k ∈ Finset.univ.erase i₀, (h.1 (k, 0) + β k) * Ptilde Y k.val k.isLt h.1 := by
          funext h
          have hsplit : Ftilde h.1 = A h * Ptilde Y i₀.val i₀.isLt h.1 +
              ∑ k ∈ Finset.univ.erase i₀, (h.1 (k, 0) + β k) * Ptilde Y k.val k.isLt h.1 := by
            simp only [Ftilde, A]; rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i₀)]
          rw [hsplit, add_assoc, f_add_self, add_zero]
        rw [hfun]
        exact isCubG_add hFH_cub hsum_cub
      by_cases hA_const : ∀ h : H, A h = A 0
      · rcases f_cases (A 0) with hA0 | hA0
        · let r' := r - 1
          have hr' : r' + 1 = r := by have := i₀.isLt; omega
          let pick : Fin r' → Fin r := fun j => ((i₀.cast hr'.symm).succAbove j).cast hr'
          have hpick_ne : ∀ j : Fin r', pick j ≠ i₀ := fun j he =>
            Fin.succAbove_ne (i₀.cast hr'.symm) j (Fin.ext (by simpa [pick] using congrArg Fin.val he))
          have hother_pick : ∀ j : Fin r', ∃ a b : H → F, isAffG a ∧ isAffG b ∧
              ∀ h : H, Ptilde Y (pick j).val (pick j).isLt h.1 = a h * b h :=
            fun j => hP_other_aff (pick j) (hpick_ne j)
          choose ao bo hao hbo habo using hother_pick
          have hsum_less : ∀ h : H, Ftilde h.1 = (0 : F) +
              ∑ j : Fin r', (h.1 (pick j, 0) + β (pick j)) * ao j h * bo j h := by
            intro h
            simp only [Ftilde, zero_add]
            rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i₀)]
            have h0 : (h.1 (i₀, 0) + β i₀) * Ptilde Y i₀.val i₀.isLt h.1 = 0 := by
              change A h * _ = 0; rw [hA_const h, hA0, zero_mul]
            rw [h0, zero_add]
            have hbij : ∑ k ∈ Finset.univ.erase i₀, (h.1 (k, 0) + β k) * Ptilde Y k.val k.isLt h.1 =
                ∑ j : Fin r', (h.1 (pick j, 0) + β (pick j)) *
                  Ptilde Y (pick j).val (pick j).isLt h.1 := by
              symm
              apply Finset.sum_bij (fun j _ => pick j)
              · intro j _; exact Finset.mem_erase.mpr ⟨hpick_ne j, Finset.mem_univ _⟩
              · intro a _ b _ hab
                exact Fin.succAbove_right_injective (p := i₀.cast hr'.symm)
                  (Fin.ext (by simpa [pick] using congrArg Fin.val hab))
              · intro k hk
                have hk' : k.cast hr'.symm ≠ i₀.cast hr'.symm := fun he =>
                  (Finset.mem_erase.mp hk).1 (Fin.ext (by simpa using congrArg Fin.val he))
                obtain ⟨j, hj⟩ := Fin.exists_succAbove_eq hk'
                exact ⟨j, Finset.mem_univ _, Fin.ext (by simpa [pick] using congrArg Fin.val hj)⟩
              · intro j _; rfl
            rw [hbij]
            apply Finset.sum_congr rfl; intro j _
            rw [habo j h]; ring
          exact hfinish r' (by omega) (fun _ => 0)
            (fun j h => h.1 (pick j, 0) + β (pick j))
            ao bo (isQuadG_of_isAffG (isAffG_const 0))
            (fun j => ⟨isAffG_add (isAffG_of_linear ((LinearMap.proj (pick j, (0 : Fin 3))).comp H.subtype)) (isAffG_const _), hao j, hbo j⟩)
            hsum_less
        · exact (slp_to_triples_I0_one_A1 hR Y q₀ β hq₀ L₀ hkerL₀ α hH_mem i₀ hα_i₀ hgF
            (fun k hk => hP_quad_of_e0 k (by rw [hi₀_eq]; simp [hk])) hAP_cub
            (fun h => (hA_const h).trans hA0)).elim
      · push Not at hA_const
        exact slp_to_triples_I0_one_Anconst Y β L₀ α hH_mem i₀ hα_i₀ hfinish hP_other_aff hAP_cub hA_const

def normBlock (a : Fin 3 → F) : (Fin 3 → F) →ₗ[F] (Fin 3 → F) :=
  if a 0 = 1 then
    { toFun := fun x => ![a 0 * x 0 + a 1 * x 1 + a 2 * x 2, x 1, x 2]
      map_add' := fun x y => by funext s; fin_cases s <;> simp <;> ring
      map_smul' := fun r x => by funext s; fin_cases s <;> simp <;> ring }
  else if a 1 = 1 then
    { toFun := fun x => ![a 0 * x 0 + a 1 * x 1 + a 2 * x 2, x 0, x 2]
      map_add' := fun x y => by funext s; fin_cases s <;> simp <;> ring
      map_smul' := fun r x => by funext s; fin_cases s <;> simp <;> ring }
  else if a 2 = 1 then
    { toFun := fun x => ![a 0 * x 0 + a 1 * x 1 + a 2 * x 2, x 0, x 1]
      map_add' := fun x y => by funext s; fin_cases s <;> simp <;> ring
      map_smul' := fun r x => by funext s; fin_cases s <;> simp <;> ring }
  else LinearMap.id

lemma det3_normBlock (a x y z : Fin 3 → F) :
    det3 (normBlock a x) (normBlock a y) (normBlock a z) = det3 x y z := by
  unfold normBlock
  split_ifs with h0 h1 h2
  · simp only [det3, LinearMap.coe_mk, AddHom.coe_mk, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, h0, one_mul]
    ring_nf; simp only [mul_two, two_mul, f_add_self, add_zero, zero_add]
  · have h0' : a 0 = 0 := (f_cases _).resolve_right h0
    simp only [det3, LinearMap.coe_mk, AddHom.coe_mk, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, h0', h1, zero_mul, one_mul, zero_add]
    ring_nf; simp only [mul_two, two_mul, f_add_self, add_zero, zero_add]
  · have h0' : a 0 = 0 := (f_cases _).resolve_right h0
    have h1' : a 1 = 0 := (f_cases _).resolve_right h1
    simp only [det3, LinearMap.coe_mk, AddHom.coe_mk, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, h0', h1', h2, zero_mul, one_mul, zero_add]
    ring
  · rfl

lemma normBlock_bijective (a : Fin 3 → F) : Function.Bijective (normBlock a) := by
  have hinj : Function.Injective (normBlock a) := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    unfold normBlock at hx
    split_ifs at hx with h0 h1 h2
    · have c0 : a 0 * x 0 + a 1 * x 1 + a 2 * x 2 = 0 := congrFun hx 0
      have c1 : x 1 = 0 := congrFun hx 1
      have c2 : x 2 = 0 := congrFun hx 2
      rw [h0, c1, c2, one_mul, mul_zero, mul_zero, add_zero, add_zero] at c0
      funext s; fin_cases s <;> assumption
    · have h0' : a 0 = 0 := (f_cases _).resolve_right h0
      have c0 : a 0 * x 0 + a 1 * x 1 + a 2 * x 2 = 0 := congrFun hx 0
      have c1 : x 0 = 0 := congrFun hx 1
      have c2 : x 2 = 0 := congrFun hx 2
      rw [h0', h1, c2, zero_mul, one_mul, mul_zero, zero_add, add_zero] at c0
      funext s; fin_cases s <;> assumption
    · have h0' : a 0 = 0 := (f_cases _).resolve_right h0
      have h1' : a 1 = 0 := (f_cases _).resolve_right h1
      have c0 : a 0 * x 0 + a 1 * x 1 + a 2 * x 2 = 0 := congrFun hx 0
      have c1 : x 0 = 0 := congrFun hx 1
      have c2 : x 1 = 0 := congrFun hx 2
      rw [h0', h1', h2, zero_mul, zero_mul, one_mul, zero_add, zero_add] at c0
      funext s; fin_cases s <;> assumption
    · exact hx
  exact ⟨hinj, LinearMap.injective_iff_surjective.mp hinj⟩

lemma normBlock_first (a x : Fin 3 → F) (ha : a ≠ 0) :
    normBlock a x 0 = a 0 * x 0 + a 1 * x 1 + a 2 * x 2 := by
  unfold normBlock
  split_ifs with h0 h1 h2
  · rfl
  · rfl
  · rfl
  · exfalso; apply ha; funext s; fin_cases s
    · exact (f_cases _).resolve_right h0
    · exact (f_cases _).resolve_right h1
    · exact (f_cases _).resolve_right h2

lemma triples_to_model {n c : ℕ} {g : V n → F} {R : Submodule F (V n)}
    (hg : cubic g) (hR : ∀ u : V n, u ∈ R ↔ ∀ v w : V n, third g u v w = 0)
    (hdc : (n - Module.finrank F R) + 1 = 3 * c)
    (L : V n →ₗ[F] E c) (q : V n → F) (hq : quad q)
    (hg_eq : ∀ y : V n, g y = q y + ∑ i : Fin c, L y (i, 0) * L y (i, 1) * L y (i, 2)) :
    ∃ (t : ℕ) (_ : 2 ≤ t) (_ : t ≤ c) (L' : V n →ₗ[F] E c) (q' : V n → F),
      quad q' ∧
      (∀ z : E c, (∃ x : V n, L' x = z) ↔ alphaT c t z = 0) ∧
      ∀ x : V n, g x = q' x + ∑ i : Fin c, L' x (i, 0) * L' x (i, 1) * L' x (i, 2) := by
  classical
  have hker_le : LinearMap.ker L ≤ R := by
    intro u hu
    rw [hR]; intro v w
    have hg_fun : g = fun y => q y + ∑ i : Fin c, L y (i, 0) * L y (i, 1) * L y (i, 2) := funext hg_eq
    rw [hg_fun, third_add_fun, third_quad hq, zero_add, third_sum]
    apply Finset.sum_eq_zero; intro i _
    let l₀ : V n →ₗ[F] F := (LinearMap.proj (i, (0 : Fin 3))).comp L
    let l₁ : V n →ₗ[F] F := (LinearMap.proj (i, (1 : Fin 3))).comp L
    let l₂ : V n →ₗ[F] F := (LinearMap.proj (i, (2 : Fin 3))).comp L
    change third (fun y => l₀ y * l₁ y * l₂ y) u v w = 0
    rw [third_triple l₀ l₁ l₂ u v w]
    have hLu : L u = 0 := LinearMap.mem_ker.mp hu
    simp [det3, l₀, l₁, l₂, hLu]
  have hRle : Module.finrank F R ≤ n := by
    have := Submodule.finrank_le R; simpa [Module.finrank_fin_fun] using this
  have hdim_H : Module.finrank F (LinearMap.range L) + 1 = Module.finrank F (E c) := by
    have hr := LinearMap.finrank_range_add_finrank_ker L
    rw [Module.finrank_fin_fun] at hr
    have h1 : Module.finrank F (LinearMap.ker L) ≤ Module.finrank F R := Submodule.finrank_mono hker_le
    have hE : Module.finrank F (E c) = 3 * c := by
      rw [Module.finrank_fintype_fun_eq_card, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin]; ring
    have h2 : Module.finrank F (LinearMap.range L) ≤ 3 * c := by
      have := Submodule.finrank_le (LinearMap.range L); omega
    have hne : Module.finrank F (LinearMap.range L) ≠ 3 * c := by
      intro htop
      have hsurj : Function.Surjective L :=
        LinearMap.range_eq_top.mp (Submodule.eq_top_of_finrank_eq (by omega))
      exact no_surjective_triples hg hR hdc L q hq hg_eq hsurj
    omega
  obtain ⟨α, hα_ne, hker_α⟩ := exists_hyperplane_covector (LinearMap.range L) hdim_H
  let αBlock : Fin c → Fin 3 → F := fun i s => α (Pi.single (i, s) 1)
  have hα_eval : ∀ z : E c, α z = ∑ i : Fin c, (αBlock i 0 * z (i, 0) + αBlock i 1 * z (i, 1) + αBlock i 2 * z (i, 2)) := by
    intro z
    have hz : z = ∑ i : Fin c, (z (i, 0) • Pi.single (i, (0 : Fin 3)) (1 : F) +
        z (i, 1) • Pi.single (i, (1 : Fin 3)) 1 + z (i, 2) • Pi.single (i, (2 : Fin 3)) 1) := by
      funext ⟨j, s⟩
      simp only [Finset.sum_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply]
      rw [Finset.sum_eq_single j]
      · fin_cases s <;> simp
      · intro i _ hij; simp [Ne.symm hij]
      · intro hj; exact (hj (Finset.mem_univ j)).elim
    conv_lhs => rw [hz]
    rw [map_sum]
    apply Finset.sum_congr rfl; intro i _
    simp only [map_add, map_smul, smul_eq_mul, αBlock]; ring
  let marked : Finset (Fin c) := Finset.univ.filter (fun i => αBlock i ≠ 0)
  let t := marked.card
  have htc : t ≤ c := by
    have := Finset.card_le_univ marked; simpa [Fintype.card_fin] using this
  have ht1 : 1 ≤ t := by
    by_contra ht0
    have hm0 : marked = ∅ := Finset.card_eq_zero.mp (by omega)
    apply hα_ne
    apply LinearMap.ext; intro z
    rw [hα_eval z]
    apply Finset.sum_eq_zero; intro i _
    have hni : i ∉ marked := by rw [hm0]; simp
    rw [Finset.mem_filter] at hni; push Not at hni
    have h0 := hni (Finset.mem_univ i)
    simp [h0]
  let eM : marked ≃ Fin t := marked.equivFin
  let eU : (markedᶜ : Finset (Fin c)) ≃ Fin (c - t) :=
    (markedᶜ).equivFinOfCardEq (by
      rw [Finset.card_compl, Fintype.card_fin])
  let σ : Fin c ≃ Fin c :=
    { toFun := fun i =>
        if hi : i ∈ marked then ⟨(eM ⟨i, hi⟩).val, by omega⟩
        else ⟨t + (eU ⟨i, Finset.mem_compl.mpr hi⟩).val, by
          have := (eU ⟨i, Finset.mem_compl.mpr hi⟩).isLt; omega⟩
      invFun := fun j =>
        if hj : j.val < t then (eM.symm ⟨j.val, hj⟩).1
        else (eU.symm ⟨j.val - t, by omega⟩).1
      left_inv := fun i => by
        by_cases hi : i ∈ marked
        · simp only [hi, dite_true, (eM ⟨i, hi⟩).isLt, Fin.eta, Equiv.symm_apply_apply]
        · simp only [hi, dite_false]
          have hge : ¬ (t + (eU ⟨i, Finset.mem_compl.mpr hi⟩).val < t) := by omega
          simp only [hge, dite_false, Nat.add_sub_cancel_left, Fin.eta, Equiv.symm_apply_apply]
      right_inv := fun j => by
        by_cases hj : j.val < t
        · simp only [hj, dite_true, (eM.symm ⟨j.val, hj⟩).2, Subtype.coe_eta, Equiv.apply_symm_apply, Fin.eta]
        · simp only [hj, dite_false]
          have hnot : (eU.symm ⟨j.val - t, by omega⟩).1 ∉ marked :=
            Finset.mem_compl.mp (eU.symm ⟨j.val - t, by omega⟩).2
          simp only [hnot, dite_false, Subtype.coe_eta, Equiv.apply_symm_apply]
          apply Fin.ext; dsimp; omega }
  have hσ_marked : ∀ i : Fin c, (σ i).val < t ↔ i ∈ marked := by
    intro i
    by_cases hi : i ∈ marked
    · simp [σ, hi, (eM ⟨i, hi⟩).isLt]
    · simp only [σ, Equiv.coe_fn_mk, hi, dite_false, Fin.val_mk, iff_false]; omega
  let Tmap : E c →ₗ[F] E c :=
    { toFun := fun z p => normBlock (αBlock (σ.symm p.1)) (blockVec z (σ.symm p.1)) p.2
      map_add' := fun z₁ z₂ => by
        funext ⟨j, s⟩
        have : blockVec (z₁ + z₂) (σ.symm j) = blockVec z₁ (σ.symm j) + blockVec z₂ (σ.symm j) := by
          funext k; rfl
        rw [this, map_add]; rfl
      map_smul' := fun r z => by
        funext ⟨j, s⟩
        have : blockVec (r • z) (σ.symm j) = r • blockVec z (σ.symm j) := by funext k; rfl
        rw [this, map_smul]; rfl }
  have hT_bij : Function.Bijective Tmap := by
    have hinj : Function.Injective Tmap := by
      rw [injective_iff_map_eq_zero]
      intro z hz
      funext ⟨i, s⟩
      have hblock : normBlock (αBlock i) (blockVec z i) = 0 := by
        funext k
        have := congrFun hz (σ i, k)
        simpa [Tmap] using this
      have hb0 : blockVec z i = 0 := (normBlock_bijective (αBlock i)).1 (by rw [hblock, map_zero])
      exact congrFun hb0 s
    exact ⟨hinj, LinearMap.injective_iff_surjective.mp hinj⟩
  have hT_alpha : ∀ z : E c, alphaT c t (Tmap z) = α z := by
    intro z
    rw [hα_eval z]
    simp only [alphaT, LinearMap.coe_mk, AddHom.coe_mk, Tmap]
    rw [← Equiv.sum_comp σ]
    apply Finset.sum_congr rfl; intro i _
    simp only [Equiv.symm_apply_apply]
    by_cases hi : i ∈ marked
    · have hlt : (σ i).val < t := (hσ_marked i).mpr hi
      rw [if_pos hlt]
      have hne : αBlock i ≠ 0 := (Finset.mem_filter.mp hi).2
      exact normBlock_first (αBlock i) (blockVec z i) hne
    · have hge : ¬ (σ i).val < t := fun h => hi ((hσ_marked i).mp h)
      rw [if_neg hge]
      rw [Finset.mem_filter] at hi; push Not at hi
      have h0 := hi (Finset.mem_univ i)
      simp [h0]
  let L' : V n →ₗ[F] E c := Tmap.comp L
  have hL'_range : ∀ z : E c, (∃ x : V n, L' x = z) ↔ alphaT c t z = 0 := by
    intro z
    obtain ⟨w, rfl⟩ := hT_bij.2 z
    rw [hT_alpha w]
    constructor
    · rintro ⟨x, hx⟩
      have hLx : L x = w := hT_bij.1 hx
      have hw : w ∈ LinearMap.range L := ⟨x, hLx⟩
      rw [← hker_α, LinearMap.mem_ker] at hw
      exact hw
    · intro hαw
      have hw : w ∈ LinearMap.range L := by rw [← hker_α, LinearMap.mem_ker]; exact hαw
      obtain ⟨x, hx⟩ := hw
      exact ⟨x, congrArg Tmap hx⟩
  have hthird_eq : ∀ a b d : V n,
      third g a b d = third (fun y => ∑ i : Fin c, L' y (i, 0) * L' y (i, 1) * L' y (i, 2)) a b d := by
    intro a b d
    have hL_third : third g a b d = omegaE (L a) (L b) (L d) := by
      have hg_fun : g = fun y => q y + ∑ i : Fin c, L y (i, 0) * L y (i, 1) * L y (i, 2) := funext hg_eq
      rw [hg_fun, third_add_fun, third_quad hq, zero_add, third_sum]
      simp only [omegaE]
      apply Finset.sum_congr rfl; intro i _
      let l₀ : V n →ₗ[F] F := (LinearMap.proj (i, (0 : Fin 3))).comp L
      let l₁ : V n →ₗ[F] F := (LinearMap.proj (i, (1 : Fin 3))).comp L
      let l₂ : V n →ₗ[F] F := (LinearMap.proj (i, (2 : Fin 3))).comp L
      exact third_triple l₀ l₁ l₂ a b d
    have hL'_third : third (fun y => ∑ i : Fin c, L' y (i, 0) * L' y (i, 1) * L' y (i, 2)) a b d =
        omegaE (L' a) (L' b) (L' d) := by
      rw [third_sum]
      simp only [omegaE]
      apply Finset.sum_congr rfl; intro i _
      let l₀ : V n →ₗ[F] F := (LinearMap.proj (i, (0 : Fin 3))).comp L'
      let l₁ : V n →ₗ[F] F := (LinearMap.proj (i, (1 : Fin 3))).comp L'
      let l₂ : V n →ₗ[F] F := (LinearMap.proj (i, (2 : Fin 3))).comp L'
      exact third_triple l₀ l₁ l₂ a b d
    rw [hL_third, hL'_third]
    simp only [omegaE, L', LinearMap.comp_apply, Tmap, LinearMap.coe_mk, AddHom.coe_mk]
    rw [← Equiv.sum_comp σ.symm]
    apply Finset.sum_congr rfl; intro i _
    exact (det3_normBlock (αBlock (σ.symm i)) (blockVec (L a) (σ.symm i))
      (blockVec (L b) (σ.symm i)) (blockVec (L d) (σ.symm i))).symm
  let q' : V n → F := fun y => g y + ∑ i : Fin c, L' y (i, 0) * L' y (i, 1) * L' y (i, 2)
  have hq' : quad q' := by
    apply quad_of_diff3_eq_zero
    intro a b d x
    have hadd3 : ∀ (f₁ f₂ : V n → F),
        diff (diff (diff (fun y => f₁ y + f₂ y) a) b) d x =
          diff (diff (diff f₁ a) b) d x + diff (diff (diff f₂ a) b) d x := by
      intro f₁ f₂
      have e1 : diff (fun y => f₁ y + f₂ y) a = fun y => diff f₁ a y + diff f₂ a y :=
        funext (diff_add_fun f₁ f₂ a)
      rw [e1]
      have e2 : diff (fun y => diff f₁ a y + diff f₂ a y) b =
          fun y => diff (diff f₁ a) b y + diff (diff f₂ a) b y := funext (diff_add_fun _ _ b)
      rw [e2, diff_add_fun]
    have hsum3 : diff (diff (diff (fun y => ∑ i : Fin c, L' y (i, 0) * L' y (i, 1) * L' y (i, 2)) a) b) d x =
        third (fun y => ∑ i : Fin c, L' y (i, 0) * L' y (i, 1) * L' y (i, 2)) a b d := by
      have e1 : diff (fun y => ∑ i : Fin c, L' y (i, 0) * L' y (i, 1) * L' y (i, 2)) a =
          fun y => ∑ i : Fin c, diff (fun z => L' z (i, 0) * L' z (i, 1) * L' z (i, 2)) a y :=
        funext (diff_sum _ _ a)
      rw [e1]
      have e2 : diff (fun y => ∑ i : Fin c, diff (fun z => L' z (i, 0) * L' z (i, 1) * L' z (i, 2)) a y) b =
          fun y => ∑ i : Fin c, diff (diff (fun z => L' z (i, 0) * L' z (i, 1) * L' z (i, 2)) a) b y :=
        funext (diff_sum _ _ b)
      rw [e2, diff_sum, third_sum]
      apply Finset.sum_congr rfl; intro i _
      let l₀ : V n →ₗ[F] F := (LinearMap.proj (i, (0 : Fin 3))).comp L'
      let l₁ : V n →ₗ[F] F := (LinearMap.proj (i, (1 : Fin 3))).comp L'
      let l₂ : V n →ₗ[F] F := (LinearMap.proj (i, (2 : Fin 3))).comp L'
      exact diff3_triple_const l₀ l₁ l₂ a b d x
    rw [hadd3, diff3_const_of_cubic hg, hsum3, hthird_eq a b d, f_add_self]
  have hg_eq' : ∀ y : V n, g y = q' y + ∑ i : Fin c, L' y (i, 0) * L' y (i, 1) * L' y (i, 2) := by
    intro y; simp only [q', add_assoc, f_add_self, add_zero]
  have ht2 : 2 ≤ t := by
    by_contra ht_lt
    have ht_eq1 : t = 1 := by omega
    let i0 : Fin c := ⟨0, by omega⟩
    let z0 : E c := blockEmb i0 ![0, 1, 0]
    have hz0_alpha : alphaT c t z0 = 0 := by
      rw [alphaT_comp_blockEmb]; split_ifs <;> rfl
    obtain ⟨u0, hu0⟩ := (hL'_range z0).mpr hz0_alpha
    have hu0R : u0 ∈ R := by
      rw [hR]; intro v w
      rw [hthird_eq u0 v w, third_sum]
      apply Finset.sum_eq_zero; intro i _
      let l₀ : V n →ₗ[F] F := (LinearMap.proj (i, (0 : Fin 3))).comp L'
      let l₁ : V n →ₗ[F] F := (LinearMap.proj (i, (1 : Fin 3))).comp L'
      let l₂ : V n →ₗ[F] F := (LinearMap.proj (i, (2 : Fin 3))).comp L'
      change third (fun y => l₀ y * l₁ y * l₂ y) u0 v w = 0
      rw [third_triple l₀ l₁ l₂ u0 v w]
      by_cases hi : i = i0
      · subst hi
        have hv0 : L' v (i0, 0) = 0 := by
          have := (hL'_range (L' v)).mp ⟨v, rfl⟩
          simp only [alphaT, LinearMap.coe_mk, AddHom.coe_mk, ht_eq1] at this
          rw [Finset.sum_eq_single i0] at this
          · simpa [i0] using this
          · intro j _ hji
            have hge : ¬ (j.val < 1) := by intro hlt; exact hji (Fin.ext (by dsimp [i0]; omega))
            simp [hge]
          · intro h; exact (h (Finset.mem_univ i0)).elim
        have hw0 : L' w (i0, 0) = 0 := by
          have := (hL'_range (L' w)).mp ⟨w, rfl⟩
          simp only [alphaT, LinearMap.coe_mk, AddHom.coe_mk, ht_eq1] at this
          rw [Finset.sum_eq_single i0] at this
          · simpa [i0] using this
          · intro j _ hji
            have hge : ¬ (j.val < 1) := by intro hlt; exact hji (Fin.ext (by dsimp [i0]; omega))
            simp [hge]
          · intro h; exact (h (Finset.mem_univ i0)).elim
        have hu00 : L' u0 (i0, 0) = 0 := by rw [hu0]; simp [z0, blockEmb]
        simp [det3, l₀, l₁, l₂, hv0, hw0, hu00]
      · have hu0i : ∀ s : Fin 3, L' u0 (i, s) = 0 := fun s => by rw [hu0]; simp [z0, blockEmb, hi]
        simp [det3, l₀, l₁, l₂, hu0i]
    have hkerL' : LinearMap.ker L' = R := by
      have hkerL : LinearMap.ker L = R := by
        apply Submodule.eq_of_le_of_finrank_eq hker_le
        have hr := LinearMap.finrank_range_add_finrank_ker L
        rw [Module.finrank_fin_fun] at hr
        rw [Module.finrank_fintype_fun_eq_card, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin] at hdim_H
        omega
      ext u
      rw [LinearMap.mem_ker, ← hkerL, LinearMap.mem_ker]
      exact ⟨fun h => hT_bij.1 (by change Tmap (L u) = 0 at h; rw [h, map_zero]),
        fun h => by change Tmap (L u) = 0; rw [h, map_zero]⟩
    have hL'u0 : L' u0 = 0 := LinearMap.mem_ker.mp (hkerL'.symm ▸ hu0R)
    rw [hu0] at hL'u0
    have := congrFun hL'u0 (i0, 1)
    simp [z0, blockEmb] at this
  exact ⟨t, ht2, htc, L', q', hq', hL'_range, hg_eq'⟩

lemma main_proof : ∀ n : ℕ,
  let F := ZMod 2
  let Circ := PEqualNP.CircuitLowerBounds.Circuit
  let legal := fun (n : ℕ) (C : Circ) =>
    PEqualNP.MetaComplexity.NestedCover.ReadsBack n C ∧
      (∀ h ∈ C.gates, h.inputs.length ≤ 2 ∧
        (h.op = .and ∨ h.op = .or ∨ h.op = .mod 2 ∨ (h.op = .not ∧ h.inputs.length = 1)))
  let cost := fun (C : Circ) => C.gates.countP (fun h => @decide
    ((h.op = .and ∨ h.op = .or) ∧ h.inputs.length = 2) (Classical.propDecidable _))
  let bits := fun (n : ℕ) (u : Fin n → F) => List.ofFn (fun j : Fin n => decide (u j = 1))
  let V := Fin n → F
  let diff := fun (g : V → F) (a x : V) => g (x+a) - g x
  let third := fun (g : V → F) (a b c : V) => diff (diff (diff g a) b) c 0
  let cubic := fun (g : V → F) => ∀ a b c d x, diff (diff (diff (diff g a) b) c) d x = 0
  let quad := fun (q : V → F) => ∃ (s : F) (h : V) (M : Fin n → Fin n → F),
    ∀ x, q x = s + dotProduct h x + ∑ i, ∑ j, M i j * x i * x j
  let unit := fun (i j : Fin n) => if i = j then (1 : F) else 0
  let rankAt := fun (g : V → F) (u : V) =>
    (Matrix.of (fun i j : Fin n => third g u (unit i) (unit j))).rank
  let fits := fun (g : V → F) (s : ℕ) => ∃ C : Circ, legal (2*n) C ∧ cost C ≤ s ∧
    ∀ x y : V, C.eval (bits n x ++ bits n y) = decide (dotProduct x y + g y = 1)
  ∀ (g : V → F) (R : Submodule F V), cubic g →
    (∀ u : V, u ∈ R ↔ ∀ v w : V, third g u v w = 0) →
    let d := n - Module.finrank F R
    ∀ c : ℕ, d+1 = 3*c →
      let E := (Fin c × Fin 3) → F
      let S := R ⊔ Submodule.span F {u : V | rankAt g u = 2}
      let p := (n - Module.finrank F S) + 1
      let model := fun (t : ℕ) => ∃ (L : V →ₗ[F] E) (q : V → F), quad q ∧
        (∀ z : E, (∃ x : V, L x = z) ↔
          (∑ i : Fin c, if i.val < t then z (i,0) else 0) = 0) ∧
        ∀ x, g x = q x + ∑ i : Fin c, L x (i,0) * L x (i,1) * L x (i,2)
      (fits g (n+c) ↔ 2 ≤ p ∧ p ≤ c ∧ model p) ∧
        (∀ t : ℕ, 2 ≤ t → t ≤ c → model t → t = p) ∧
        (fits g (n+c) → ((Finset.univ : Finset V).filter (fun u => rankAt g u = 2)).card =
          2^(Module.finrank F R) * (7*(c-p) + 3*p + (if p = 2 then 9 else 0))) := by
  intro n F Circ legal cost bits V diff third cubic quad unit rankAt fits g R hcub hR d c hdc E S p model
  have huniq : ∀ t : ℕ, 2 ≤ t → t ≤ c → model t → t = p := by
    intro t ht2 htc ⟨L, q, hq, hLr, hgq⟩
    exact (model_analysis hcub hR hdc ht2 htc L q hq hLr hgq).1
  have hfits_to_model : fits g (n + c) → 2 ≤ p ∧ p ≤ c ∧ model p := by
    rintro ⟨C, ⟨hread, hleg⟩, hcost, heval⟩
    obtain ⟨slp, wireE, hwireE⟩ := circuit_to_slp C.gates hread hleg
    let outE : AffExpr n (gateCost C.gates) :=
      if h : C.output < 2 * n + C.gates.length then wireE ⟨C.output, h⟩ else AffExpr.const 0
    have hout : ∀ x y : V, outE.eval x y (slp.evalFull x y) = dotProduct x y + g y := by
      intro x y
      have hev := heval x y
      have hevF : wireVal C.gates C.output x y = dotProduct x y + g y := by
        unfold wireVal
        have h1 : Circuit.wires ⟨C.gates, 0⟩ (L_meta_32025_aux.bits n x ++ L_meta_32025_aux.bits n y) =
            C.wires (bits n x ++ bits n y) := rfl
        rw [h1]
        change b2f (C.eval (bits n x ++ bits n y)) = dotProduct x y + g y
        rw [hev, b2f_decide]
      rw [← hevF]
      dsimp only [outE]
      split_ifs with hlt
      · exact hwireE ⟨C.output, hlt⟩ x y
      · rw [AffExpr.eval_const]
        unfold wireVal
        have hlen : (Circuit.wires ⟨C.gates, 0⟩ (L_meta_32025_aux.bits n x ++ L_meta_32025_aux.bits n y)).length =
            2 * n + C.gates.length := by
          rw [wires_length, List.length_append, bits_length, bits_length]; dsimp only; omega
        rw [List.getD_eq_default _ _ (by omega)]; rfl
    obtain ⟨r, hrn, Y, q₀, ℓ, β, hq₀, hgY⟩ := elim_x_from_slp slp outE g hout
    have hrc : r ≤ c := by
      have : gateCost C.gates ≤ n + c := hcost
      omega
    obtain ⟨L1, q1, hq1, hg1⟩ := slp_to_triples hcub hR hdc hrc Y q₀ ℓ β hq₀ hgY
    obtain ⟨t, ht2, htc, L2, q2, hq2, hLr2, hg2⟩ := triples_to_model hcub hR hdc L1 q1 hq1 hg1
    have hmodt : model t := ⟨L2, q2, hq2, hLr2, hg2⟩
    have htp : t = p := huniq t ht2 htc hmodt
    subst htp
    exact ⟨ht2, htc, hmodt⟩
  refine ⟨⟨hfits_to_model, ?_⟩, huniq, ?_⟩
  · rintro ⟨_, _, L, q, hq, _, hgq⟩
    exact model_implies_fits L q hq hgq
  · intro hfits
    obtain ⟨hp2, hpc, L, q, hq, hLr, hgq⟩ := hfits_to_model hfits
    exact (model_analysis hcub hR hdc hp2 hpc L q hq hLr hgq).2

end PEqualNP.Outside.L_meta_32025_aux

theorem PEqualNP.Outside.L_meta_32025 : (∀ n : ℕ,
  let F := ZMod 2
  let Circ := PEqualNP.CircuitLowerBounds.Circuit
  let legal := fun (n : ℕ) (C : Circ) =>
    PEqualNP.MetaComplexity.NestedCover.ReadsBack n C ∧
      (∀ h ∈ C.gates, h.inputs.length ≤ 2 ∧
        (h.op = .and ∨ h.op = .or ∨ h.op = .mod 2 ∨ (h.op = .not ∧ h.inputs.length = 1)))
  let cost := fun (C : Circ) => C.gates.countP (fun h => @decide
    ((h.op = .and ∨ h.op = .or) ∧ h.inputs.length = 2) (Classical.propDecidable _))
  let bits := fun (n : ℕ) (u : Fin n → F) => List.ofFn (fun j : Fin n => decide (u j = 1))
  let V := Fin n → F
  let diff := fun (g : V → F) (a x : V) => g (x+a) - g x
  let third := fun (g : V → F) (a b c : V) => diff (diff (diff g a) b) c 0
  let cubic := fun (g : V → F) => ∀ a b c d x, diff (diff (diff (diff g a) b) c) d x = 0
  let quad := fun (q : V → F) => ∃ (s : F) (h : V) (M : Fin n → Fin n → F),
    ∀ x, q x = s + dotProduct h x + ∑ i, ∑ j, M i j * x i * x j
  let unit := fun (i j : Fin n) => if i = j then (1 : F) else 0
  let rankAt := fun (g : V → F) (u : V) =>
    (Matrix.of (fun i j : Fin n => third g u (unit i) (unit j))).rank
  let fits := fun (g : V → F) (s : ℕ) => ∃ C : Circ, legal (2*n) C ∧ cost C ≤ s ∧
    ∀ x y : V, C.eval (bits n x ++ bits n y) = decide (dotProduct x y + g y = 1)
  ∀ (g : V → F) (R : Submodule F V), cubic g →
    (∀ u : V, u ∈ R ↔ ∀ v w : V, third g u v w = 0) →
    let d := n - Module.finrank F R
    ∀ c : ℕ, d+1 = 3*c →
      let E := (Fin c × Fin 3) → F
      let S := R ⊔ Submodule.span F {u : V | rankAt g u = 2}
      let p := (n - Module.finrank F S) + 1
      let model := fun (t : ℕ) => ∃ (L : V →ₗ[F] E) (q : V → F), quad q ∧
        (∀ z : E, (∃ x : V, L x = z) ↔
          (∑ i : Fin c, if i.val < t then z (i,0) else 0) = 0) ∧
        ∀ x, g x = q x + ∑ i : Fin c, L x (i,0) * L x (i,1) * L x (i,2)
      (fits g (n+c) ↔ 2 ≤ p ∧ p ≤ c ∧ model p) ∧
        (∀ t : ℕ, 2 ≤ t → t ≤ c → model t → t = p) ∧
        (fits g (n+c) → ((Finset.univ : Finset V).filter (fun u => rankAt g u = 2)).card =
          2^(Module.finrank F R) * (7*(c-p) + 3*p + (if p = 2 then 9 else 0)))) :=
  PEqualNP.Outside.L_meta_32025_aux.main_proof
