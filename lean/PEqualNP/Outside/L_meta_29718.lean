import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Field.ZMod
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Pi
import Mathlib.LinearAlgebra.Projection
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

namespace PEqualNP.Outside.L_meta_29718_aux

section Differences

variable {W R : Type} [AddCommGroup W] [CommRing R]

def delta (f : W → R) (u x : W) : R := f (x + u) - f x

def differences (f : W → R) (directions : List W) : W → R :=
  directions.foldl delta f

def degree : ℕ → (W → R) → Prop
  | 0, f => ∀ u x, delta f u x = 0
  | n + 1, f => ∀ u, degree n (delta f u)

theorem degree_zero_const {f : W → R} (h : degree 0 f) (x : W) : f x = f 0 := by
  have hx := h x 0
  simpa [delta, sub_eq_zero] using hx

theorem delta_add (f g : W → R) (u : W) :
    delta (fun x => f x + g x) u = fun x => delta f u x + delta g u x := by
  funext x
  unfold delta
  ring

theorem delta_sub (f g : W → R) (u : W) :
    delta (fun x => f x - g x) u = fun x => delta f u x - delta g u x := by
  funext x
  unfold delta
  ring

theorem delta_scale (c : R) (f : W → R) (u : W) :
    delta (fun x => c * f x) u = fun x => c * delta f u x := by
  funext x
  unfold delta
  ring

theorem delta_shift (f : W → R) (u v : W) :
    delta (fun x => f (x + v)) u = fun x => delta f u (x + v) := by
  funext x
  simp only [delta, add_right_comm x u v]

theorem delta_mul (f g : W → R) (u : W) :
    delta (fun x => f x * g x) u =
      fun x => delta f u x * g (x + u) + f x * delta g u x := by
  funext x
  unfold delta
  ring

theorem degree_const (n : ℕ) (c : R) : degree n (fun _ : W => c) := by
  induction n generalizing c with
  | zero => intro u x; simp [delta]
  | succ n ih =>
    intro u
    have h : delta (fun _ : W => c) u = fun _ => 0 := by funext x; simp [delta]
    rw [h]
    exact ih 0

theorem degree_add {n : ℕ} {f g : W → R}
    (hf : degree n f) (hg : degree n g) : degree n (fun x => f x + g x) := by
  induction n generalizing f g with
  | zero => intro u x; simpa [hf u x, hg u x] using congrFun (delta_add f g u) x
  | succ n ih =>
    intro u
    rw [delta_add]
    exact ih (hf u) (hg u)

theorem degree_sub {n : ℕ} {f g : W → R}
    (hf : degree n f) (hg : degree n g) : degree n (fun x => f x - g x) := by
  induction n generalizing f g with
  | zero => intro u x; simpa [hf u x, hg u x] using congrFun (delta_sub f g u) x
  | succ n ih =>
    intro u
    rw [delta_sub]
    exact ih (hf u) (hg u)

theorem degree_scale {n : ℕ} (c : R) {f : W → R}
    (hf : degree n f) : degree n (fun x => c * f x) := by
  induction n generalizing f with
  | zero => intro u x; simpa [hf u x] using congrFun (delta_scale c f u) x
  | succ n ih =>
    intro u
    rw [delta_scale]
    exact ih (hf u)

theorem degree_shift {n : ℕ} (v : W) {f : W → R}
    (hf : degree n f) : degree n (fun x => f (x + v)) := by
  induction n generalizing f with
  | zero =>
    intro u x
    rw [delta_shift]
    exact hf u (x + v)
  | succ n ih =>
    intro u
    rw [delta_shift]
    exact ih (hf u)

theorem degree_raise {n : ℕ} {f : W → R} (hf : degree n f) : degree (n + 1) f := by
  induction n generalizing f with
  | zero =>
    intro u v x
    change delta f u (x + v) - delta f u x = 0
    rw [hf u (x + v), hf u x, sub_self]
  | succ n ih => exact fun u => ih (hf u)

theorem degree_mul {a b : ℕ} {f g : W → R}
    (hf : degree a f) (hg : degree b g) : degree (a + b) (fun x => f x * g x) := by
  induction a generalizing b f g with
  | zero =>
    have he : (fun x => f x * g x) = fun x => f 0 * g x := by
      funext x
      rw [degree_zero_const hf x]
    simpa only [Nat.zero_add, he] using degree_scale (f 0) hg
  | succ a ia =>
    induction b generalizing f g with
    | zero =>
      have he : (fun x => f x * g x) = fun x => g 0 * f x := by
        funext x
        rw [degree_zero_const hg x, mul_comm]
      simpa only [Nat.add_zero, he] using degree_scale (g 0) hf
    | succ b ib =>
      change degree (a + 1 + b + 1) _
      intro u
      rw [delta_mul]
      have h₁ := ia (hf u) (degree_shift u hg)
      have h₂ := ib hf (hg u)
      rw [show a + (b + 1) = a + 1 + b by omega] at h₁
      exact degree_add h₁ h₂

theorem degree_sum {ι : Type} (s : Finset ι) {n : ℕ} (f : ι → W → R)
    (hf : ∀ i ∈ s, degree n (f i)) : degree n (fun x => ∑ i ∈ s, f i x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (degree_const n (0 : R) : degree n (fun _ : W => (0 : R)))
  | @insert i s hi ih =>
    have h := degree_add (hf i (Finset.mem_insert_self _ _))
      (ih (fun j hj => hf j (Finset.mem_insert_of_mem hj)))
    simpa only [Finset.sum_insert hi] using h

theorem degree_fold {f : W → R} (us : List W) (n : ℕ)
    (hf : degree (us.length + n) f) : degree n (differences f us) := by
  induction us generalizing f with
  | nil => simpa [differences] using hf
  | cons u us ih =>
    change degree n (differences (delta f u) us)
    apply ih
    rw [show (u :: us).length + n = (us.length + n) + 1 by simp; omega] at hf
    exact hf u

theorem differences_sub (f g : W → R) (us : List W) (x : W) :
    differences (fun y => f y - g y) us x = differences f us x - differences g us x := by
  induction us generalizing f g with
  | nil => rfl
  | cons u us ih =>
    change differences (delta (fun y => f y - g y) u) us x = _
    rw [delta_sub, ih]
    rfl

theorem differences_zero {f : W → R} (us : List W) {n : ℕ} (hu : us.length = n + 1)
    (hf : degree n f) (x : W) : differences f us x = 0 := by
  induction us generalizing n f with
  | nil => simp at hu
  | cons u us ih =>
    cases n with
    | zero =>
      have hnil : us = [] := List.length_eq_zero_iff.1 (by simpa using hu)
      subst us
      exact hf u x
    | succ n => exact ih (Nat.succ.inj hu) (hf u)

end Differences

abbrev Scalar := ZMod 2
abbrev Word (k : ℕ) := Fin k → Scalar

def index {k : ℕ} (hk : 0 < k) (n : ℕ) : Fin k := ⟨n % k, Nat.mod_lt _ hk⟩

def rotate {k : ℕ} (hk : 0 < k) (s : ℕ) (x : Word k) (i : Fin k) : Scalar :=
  x (index hk (i.val + k - s % k))

def mix {k : ℕ} (hk : 0 < k) (g : ℕ) (x : Word k) (i : Fin k) : Scalar :=
  x i + x (index hk (i.val + g)) + x (index hk (i.val + k - g % k))

def step {k : ℕ} (hk : 0 < k) (x : Word k) (i : Fin k) : Scalar :=
  x i + (1 + x (index hk (i.val + 1))) * x (index hk (i.val + 2))

def gap (b : Bool) : ℕ := if b then 2 else 1

def spin (b : Bool) : ℕ := if b then 3 else 1

def linearInput {k : ℕ} (hk : 0 < k) (b : Bool) (x : Word k) : Word k :=
  mix hk (gap b) (rotate hk (spin b) x)

def namedInput {k : ℕ} (hk : 0 < k) (name : Bool → Word k) (b : Bool) (x : Word k) : Word k :=
  mix hk (gap b) (rotate hk (spin b) x + name b)

def firstRow {k : ℕ} (hk : 0 < k) (name c₁ : Bool → Word k) (b : Bool) (x : Word k) : Word k :=
  step hk (namedInput hk name b x) + rotate hk (if b then 4 else 0) x + c₁ b

def quadratic {k : ℕ} (hk : 0 < k) (b : Bool) (x : Word k) (j : Fin k) : Scalar :=
  linearInput hk b x (index hk (j.val + 1)) * linearInput hk b x (index hk (j.val + 2))

def outputWord {k : ℕ} (hk : 0 < k) (name c₁ c₂ : Bool → Word k) (x : Word k) (b : Bool) : Word k :=
  step hk (mix hk (gap b) (firstRow hk name c₁ b x)) +
    rotate hk (if b then 7 else 2) x + c₂ b

def topWord {k : ℕ} (hk : 0 < k) (x : Word k) (b : Bool) (i : Fin k) : Scalar :=
  mix hk (gap b) (quadratic hk b x) (index hk (i.val + 1)) *
    mix hk (gap b) (quadratic hk b x) (index hk (i.val + 2))

theorem degree_coord {k : ℕ} (i : Fin k) : degree 1 (fun x : Word k => x i) := by
  intro u v x
  simp only [delta, Pi.add_apply]
  ring

theorem degree_mix {k n : ℕ} (hk : 0 < k) (g : ℕ) (f : Word k → Word k)
    (hf : ∀ i, degree n (fun x => f x i)) (i : Fin k) :
    degree n (fun x => mix hk g (f x) i) :=
  degree_add (degree_add (hf i) (hf _)) (hf _)

theorem mix_sub {k : ℕ} (hk : 0 < k) (g : ℕ) (f h : Word k) (i : Fin k) :
    mix hk g f i - mix hk g h i = mix hk g (f - h) i := by
  simp only [mix, Pi.sub_apply]
  ring

theorem namedInput_eq {k : ℕ} (hk : 0 < k) (name : Bool → Word k) (b : Bool) (x : Word k)
    (i : Fin k) : namedInput hk name b x i = linearInput hk b x i + mix hk (gap b) (name b) i := by
  simp only [namedInput, linearInput, mix, Pi.add_apply]
  ring

theorem degree_linearInput {k : ℕ} (hk : 0 < k) (b : Bool) (i : Fin k) :
    degree 1 (fun x => linearInput hk b x i) :=
  degree_mix hk _ _ (fun _ => degree_coord _) i

theorem degree_namedInput {k : ℕ} (hk : 0 < k) (name : Bool → Word k) (b : Bool) (i : Fin k) :
    degree 1 (fun x => namedInput hk name b x i) := by
  simpa only [namedInput_eq] using
    degree_add (degree_linearInput hk b i) (degree_const 1 (mix hk (gap b) (name b) i))

theorem degree_input_remainder {k : ℕ} (hk : 0 < k) (name : Bool → Word k) (b : Bool)
    (i : Fin k) : degree 0 (fun x => namedInput hk name b x i - linearInput hk b x i) := by
  simp only [namedInput_eq, add_sub_cancel_left]
  exact degree_const 0 _

theorem degree_quadratic {k : ℕ} (hk : 0 < k) (b : Bool) (i : Fin k) :
    degree 2 (fun x => quadratic hk b x i) :=
  degree_mul (degree_linearInput hk b _) (degree_linearInput hk b _)

theorem product_remainder {k n : ℕ} {a b a₀ b₀ : Word k → Scalar}
    (hb : degree (n + 1) b) (ha₀ : degree (n + 1) a₀)
    (ha : degree n (fun x => a x - a₀ x)) (hb' : degree n (fun x => b x - b₀ x)) :
    degree (n + (n + 1)) (fun x => (1 + a x) * b x - a₀ x * b₀ x) := by
  have hp := degree_mul (degree_add (degree_const n (1 : Scalar)) ha) hb
  have hq := degree_mul ha₀ hb'
  rw [Nat.add_comm (n + 1) n] at hq
  convert degree_add hp hq using 1
  funext x
  ring

theorem degree_first_remainder {k : ℕ} (hk : 0 < k) (name c₁ : Bool → Word k) (b : Bool)
    (i : Fin k) : degree 1 (fun x => firstRow hk name c₁ b x i - quadratic hk b x i) := by
  have hp := product_remainder (n := 0) (degree_namedInput hk name b (index hk (i.val + 2)))
    (degree_linearInput hk b (index hk (i.val + 1)))
    (degree_input_remainder hk name b (index hk (i.val + 1)))
    (degree_input_remainder hk name b (index hk (i.val + 2)))
  have hd := degree_add (degree_add (degree_add (degree_namedInput hk name b i) hp)
    (degree_coord (index hk (i.val + k - (if b then 4 else 0) % k)))) (degree_const 1 (c₁ b i))
  convert hd using 1
  funext x
  simp only [firstRow, step, quadratic, rotate, Pi.add_apply]
  ring

theorem degree_firstRow {k : ℕ} (hk : 0 < k) (name c₁ : Bool → Word k) (b : Bool) (i : Fin k) :
    degree 2 (fun x => firstRow hk name c₁ b x i) := by
  simpa only [sub_add_cancel] using
    degree_add (degree_raise (degree_first_remainder hk name c₁ b i)) (degree_quadratic hk b i)

theorem degree_output_remainder {k : ℕ} (hk : 0 < k) (name c₁ c₂ : Bool → Word k) (b : Bool)
    (i : Fin k) : degree 3 (fun x => outputWord hk name c₁ c₂ x b i - topWord hk x b i) := by
  let y := fun x => mix hk (gap b) (firstRow hk name c₁ b x)
  let q := fun x => mix hk (gap b) (quadratic hk b x)
  have hy (j : Fin k) : degree 2 (fun x => y x j) :=
    degree_mix hk _ _ (degree_firstRow hk name c₁ b) j
  have hq (j : Fin k) : degree 2 (fun x => q x j) :=
    degree_mix hk _ _ (degree_quadratic hk b) j
  have hdiff (j : Fin k) : degree 1 (fun x => y x j - q x j) := by
    simpa only [y, q, mix_sub] using
      degree_mix hk (gap b) (fun x => firstRow hk name c₁ b x - quadratic hk b x)
        (degree_first_remainder hk name c₁ b) j
  have hp := product_remainder (n := 1) (hy (index hk (i.val + 2))) (hq (index hk (i.val + 1)))
    (hdiff (index hk (i.val + 1))) (hdiff (index hk (i.val + 2)))
  have hrotate := degree_raise (degree_raise
    (degree_coord (index hk (i.val + k - (if b then 7 else 2) % k))))
  have hd := degree_add (degree_add (degree_add (degree_raise (hy i)) hp) hrotate)
    (degree_const 3 (c₂ b i))
  convert hd using 1
  funext x
  simp only [outputWord, step, topWord, rotate, Pi.add_apply, y, q]
  ring

theorem degree_topWord {k : ℕ} (hk : 0 < k) (b : Bool) (i : Fin k) :
    degree 4 (fun x => topWord hk x b i) :=
  degree_mul (degree_mix hk _ _ (degree_quadratic hk b) _)
    (degree_mix hk _ _ (degree_quadratic hk b) _)

def observe {k : ℕ} (mask : Bool → Fin k → Scalar) (y : Bool → Word k) : Scalar :=
  (∑ i, mask false i * y false i) + (∑ i, mask true i * y true i)

theorem observed_degree {k : ℕ} (hk : 0 < k) (mask : Bool → Fin k → Scalar) :
    degree 4 (fun x => observe mask (topWord hk x)) :=
  degree_add
    (degree_sum Finset.univ _ (fun i _ => degree_scale (mask false i) (degree_topWord hk false i)))
    (degree_sum Finset.univ _ (fun i _ => degree_scale (mask true i) (degree_topWord hk true i)))

theorem observed_remainder {k : ℕ} (hk : 0 < k) (name c₁ c₂ : Bool → Word k)
    (mask : Bool → Fin k → Scalar) :
    degree 3 (fun x => observe mask (outputWord hk name c₁ c₂ x) - observe mask (topWord hk x)) := by
  have h (b : Bool) := degree_sum Finset.univ _
    (fun i _ => degree_scale (mask b i) (degree_output_remainder hk name c₁ c₂ b i))
  convert degree_add (h false) (h true) using 1
  funext x
  simp only [observe, mul_sub, Finset.sum_sub_distrib]
  ring

theorem observed_fourth {k : ℕ} (hk : 0 < k) (name c₁ c₂ : Bool → Word k)
    (mask : Bool → Fin k → Scalar) (us : List (Word k)) (hlen : us.length = 4) (x : Word k) :
    differences (fun y => observe mask (outputWord hk name c₁ c₂ y)) us x =
      differences (fun y => observe mask (topWord hk y)) us 0 := by
  have h := differences_zero us hlen (observed_remainder hk name c₁ c₂ mask) x
  rw [differences_sub, sub_eq_zero] at h
  have hc := degree_fold us 0 (by simpa [hlen] using observed_degree hk mask)
  exact h.trans (degree_zero_const hc x)


abbrev Query (k : ℕ) := Word k →ₗ[Scalar] Scalar

def fourthDifference {k : ℕ} (f : Word k → Scalar) (v : Fin 4 → Word k) : Word k → Scalar :=
  differences f (List.ofFn v)

def IsCubic {k : ℕ} (f : Word k → Scalar) : Prop :=
  ∀ v x, fourthDifference f v x = 0

def commonKernel {k d : ℕ} (queries : Fin d → Query k) : Submodule Scalar (Word k) :=
  ⨅ n, LinearMap.ker (queries n)

theorem mem_commonKernel {k d : ℕ} (queries : Fin d → Query k) (x : Word k) :
    x ∈ commonKernel queries ↔ ∀ n, queries n x = 0 := by
  simp [commonKernel, Submodule.mem_iInf, LinearMap.mem_ker]

def queryRun {k d : ℕ} (ask : Fin d → ℕ → Query k) (x : Word k) : ℕ :=
  (List.finRange d).foldl (fun h j => 2 * h + (if ask j h x = 0 then 0 else 1)) 0

theorem queryRun_zero {k d : ℕ} (ask : Fin d → ℕ → Query k) (x : Word k)
    (h : ∀ n, ask n 0 x = 0) : queryRun ask x = 0 := by
  unfold queryRun
  generalize List.finRange d = indices
  induction indices with
  | nil => rfl
  | cons j indices ih => simpa [List.foldl_cons, h j] using ih

theorem binaryFold_eq_bits {ι : Type} (indices : List ι) (a b : ι → ℕ)
    (ha : ∀ j, a j ≤ 1) (hb : ∀ j, b j ≤ 1)
    (heq : indices.foldl (fun h j => 2 * h + a j) 0 =
      indices.foldl (fun h j => 2 * h + b j) 0) :
    ∀ j ∈ indices, a j = b j := by
  induction indices using List.reverseRecOn with
  | nil => simp
  | append_singleton indices j ih =>
    simp only [List.foldl_append, List.foldl_cons, List.foldl_nil] at heq
    have hp : indices.foldl (fun h j => 2 * h + a j) 0 =
        indices.foldl (fun h j => 2 * h + b j) 0 := by
      have := ha j
      have := hb j
      omega
    intro i hi
    rcases List.mem_append.1 hi with h | h
    · exact ih hp i h
    · have hij := List.mem_singleton.1 h
      subst i
      omega

theorem fixed_query_eq {k d : ℕ} (queries : Fin d → Query k) (x y : Word k)
    (h : queryRun (fun n _ => queries n) x = queryRun (fun n _ => queries n) y) :
    ∀ n, queries n x = queries n y := by
  let bits (z : Word k) (j : Fin d) : ℕ := if queries j z = 0 then 0 else 1
  have hbits (z : Word k) (j : Fin d) : bits z j ≤ 1 := by
    unfold bits
    split <;> omega
  intro n
  have h' := binaryFold_eq_bits (List.finRange d) (bits x) (bits y)
    (hbits x) (hbits y) h n (List.mem_finRange n)
  change (if queries n x = 0 then (0 : ℕ) else 1) = (if queries n y = 0 then 0 else 1) at h'
  generalize queries n x = a at h' ⊢
  generalize queries n y = b at h' ⊢
  fin_cases a <;> fin_cases b
  · rfl
  · change (0 : ℕ) = 1 at h'
    omega
  · change (1 : ℕ) = 0 at h'
    omega
  · rfl

theorem differences_eq_on_submodule {k : ℕ} (S : Submodule Scalar (Word k))
    (f g : Word k → Scalar) (hfg : ∀ x ∈ S, f x = g x)
    (us : List (Word k)) (hu : ∀ u ∈ us, u ∈ S) (x : Word k) (hx : x ∈ S) :
    differences f us x = differences g us x := by
  induction us generalizing f g with
  | nil => exact hfg x hx
  | cons u us ih =>
    change differences (delta f u) us x = differences (delta g u) us x
    apply ih
    · intro z hz
      have hu' := hu u (by simp)
      simp only [delta, hfg (z + u) (S.add_mem hz hu'), hfg z hz]
    · exact fun v hv => hu v (List.mem_cons_of_mem _ hv)

theorem differences_affine {k : ℕ} (p : Word k →ₗ[Scalar] Word k) (c : Word k)
    (f : Word k → Scalar) (us : List (Word k)) (x : Word k) :
    differences (fun y => f (p y + c)) us x = differences f (us.map p) (p x + c) := by
  induction us generalizing f with
  | nil => rfl
  | cons u us ih =>
    change differences (delta (fun y => f (p y + c)) u) us x =
      differences (delta f (p u)) (us.map p) (p x + c)
    have hδ : delta (fun y => f (p y + c)) u = fun y => delta f (p u) (p y + c) := by
      funext y
      simp only [delta, map_add, add_right_comm (p y) (p u) c]
    rw [hδ, ih]

theorem parity_criterion {k d m : ℕ} (actual leading : Word k → Fin m → Scalar)
    (hlead : ∀ j v x, fourthDifference (fun y => actual y j) v x =
      fourthDifference (fun y => leading y j) v 0) :
    (∃ (ask : Fin d → ℕ → Query k) (readout : ℕ → Fin m → Word k → Scalar),
      (∀ h j, IsCubic (readout h j)) ∧
      ∀ x j, actual x j = readout (queryRun ask x) j x) ↔
    (∃ queries : Fin d → Query k, ∀ (j : Fin m) (v : Fin 4 → Word k),
      (∀ e n, queries n (v e) = 0) → fourthDifference (fun x => leading x j) v 0 = 0) := by
  classical
  constructor
  · rintro ⟨ask, readout, cubic, agree⟩
    let queries (n : Fin d) := ask n 0
    let K := commonKernel queries
    refine ⟨queries, fun j v hv => ?_⟩
    have hfg (x : Word k) (hx : x ∈ K) : actual x j = readout 0 j x := by
      have hz := queryRun_zero ask x ((mem_commonKernel queries x).1 hx)
      rw [← hz]
      exact agree x j
    have hmem (u : Word k) (hu : u ∈ List.ofFn v) : u ∈ K := by
      obtain ⟨e, rfl⟩ := List.mem_ofFn.1 hu
      exact (mem_commonKernel queries (v e)).2 (hv e)
    rw [← hlead j v 0]
    exact (differences_eq_on_submodule K _ _ hfg _ hmem 0 K.zero_mem).trans (cubic 0 j v 0)
  · rintro ⟨queries, fourthZero⟩
    let K := commonKernel queries
    obtain ⟨L, hKL⟩ := K.exists_isCompl
    let p := K.projection L hKL
    have proj_mem (x : Word k) : p x ∈ K := by
      change K.projection L hKL x ∈ K
      rw [← Submodule.coe_projectionOnto_apply]
      exact (K.projectionOnto L hKL x).property
    let ask (n : Fin d) (_ : ℕ) := queries n
    let rep (h : ℕ) : Word k := if hr : ∃ z, queryRun ask z = h then Classical.choose hr else 0
    let readout (h : ℕ) (j : Fin m) (x : Word k) := actual (p x + (rep h - p (rep h))) j
    refine ⟨ask, readout, ?_, ?_⟩
    · intro h j v x
      let c := rep h - p (rep h)
      change differences (fun y => actual (p y + c) j) (List.ofFn v) x = 0
      rw [differences_affine p c (fun y => actual y j), List.map_ofFn]
      change fourthDifference (fun y => actual y j) (fun e => p (v e)) (p x + c) = 0
      rw [hlead]
      exact fourthZero j (fun e => p (v e)) (fun e => (mem_commonKernel queries _).1 (proj_mem (v e)))
    · intro x j
      let y := rep (queryRun ask x)
      have hy : queryRun ask y = queryRun ask x := by
        have h : ∃ z, queryRun ask z = queryRun ask x := ⟨x, rfl⟩
        change queryRun ask (if hr : ∃ z, queryRun ask z = queryRun ask x then
          Classical.choose hr else 0) = queryRun ask x
        rw [dite_eq_left h]
        exact Classical.choose_spec h
      have hK : x - y ∈ K := by
        apply (mem_commonKernel queries _).2
        intro n
        rw [map_sub, fixed_query_eq queries y x hy n, sub_self]
      have hfix : p (x - y) = x - y := Submodule.projection_apply_of_mem_left hKL hK
      have he : p x + (y - p y) = x := calc
        p x + (y - p y) = p (x - y) + y := by rw [map_sub]; abel
        _ = x := by rw [hfix, sub_add_cancel]
      change actual x j = actual (p x + (y - p y)) j
      rw [he]

end PEqualNP.Outside.L_meta_29718_aux

open PEqualNP.Outside.L_meta_29718_aux in
theorem PEqualNP.Outside.L_meta_29718 : (∀ (k : ℕ) (hk : 0 < k),
  let F := ZMod 2
  let W := Fin k → F
  let D := W →ₗ[F] F
  let ix := fun n : ℕ => (⟨n % k, Nat.mod_lt _ hk⟩ : Fin k)
  let rot := fun (s : ℕ) (x : W) (i : Fin k) => x (ix (i.val + k - s % k))
  let mix := fun (g : ℕ) (x : W) (i : Fin k) =>
    x i + x (ix (i.val + g)) + x (ix (i.val + k - g % k))
  let step := fun (x : W) (i : Fin k) =>
    x i + (1 + x (ix (i.val + 1))) * x (ix (i.val + 2))
  let gap := fun b : Bool => if b then 2 else (1 : ℕ)
  let spin := fun b : Bool => if b then 3 else (1 : ℕ)
  let diff := fun (f : W → F) (u x : W) => f (x + u) - f x
  let fourth := fun (f : W → F) (v : Fin 4 → W) => (List.ofFn v).foldl diff f
  let cubic := fun (f : W → F) => ∀ v x, fourth f v x = 0
  ∀ (name c₁ c₂ : Bool → W) (d : ℕ),
    let out := fun (x : W) (b : Bool) =>
      let z := mix (gap b) (rot (spin b) x + name b)
      let y := step z + rot (if b then 4 else 0) x + c₁ b
      step (mix (gap b) y) + rot (if b then 7 else 2) x + c₂ b
    let run := fun (ask : Fin d → ℕ → D) (x : W) =>
      (List.finRange d).foldl (fun h j =>
        2 * h + (if ask j h x = 0 then 0 else 1)) (0 : ℕ)
    let top := fun (x : W) (b : Bool) (i : Fin k) =>
      let g := gap b
      let z := mix g (rot (spin b) x)
      let two := fun p : ℕ => z (ix (p + 1)) * z (ix (p + 2))
      let q := fun j : Fin k =>
        two j.val + two (ix (j.val + g)).val + two (ix (j.val + k - g % k)).val
      q (ix (i.val + 1)) * q (ix (i.val + 2))
    ∀ (m : ℕ) (mask : Fin m → Bool → Fin k → F),
      let observe := fun (w : Bool → W) (j : Fin m) =>
        (∑ i, mask j false i * w false i) + (∑ i, mask j true i * w true i)
      (∃ (ask : Fin d → ℕ → D) (readout : ℕ → Fin m → W → F),
        (∀ h j, cubic (readout h j)) ∧
        ∀ x j, observe (out x) j = readout (run ask x) j x) ↔
      (∃ queries : Fin d → D, ∀ (j : Fin m) (v : Fin 4 → W),
        (∀ e n, queries n (v e) = 0) →
        fourth (fun x => observe (top x) j) v (0 : W) = 0)) := by
  intro k hk
  dsimp only
  intro name c₁ c₂ d m mask
  exact parity_criterion (d := d)
    (fun x j => observe (mask j) (outputWord hk name c₁ c₂ x))
    (fun x j => observe (mask j) (topWord hk x))
    (fun j v x => observed_fourth hk name c₁ c₂ (mask j) (List.ofFn v) List.length_ofFn x)
