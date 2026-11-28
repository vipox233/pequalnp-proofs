import PEqualNP.Defs
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.List.Induction
import Mathlib.Data.List.OfFn
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push

namespace PEqualNP.Outside.L_lib_870_aux

section LinearCore

variable {s : ℕ} (n : Fin s → Bool → Option (Fin s))

def Absorbs : Prop :=
  ∃ pick : Fin s → Bool, ∀ i : Fin s,
    (fun x : Option (Fin s) => x.bind (fun h => n h (pick h)))^[s] (some i) = none

def Ends (r : Fin s → Bool → ℝ) (x : Fin s → ℝ) (i : Fin s) (b : Bool) : ℝ :=
  (n i b).elim (r i b) x

def Solves (r : Fin s → Bool → ℝ) (x : Fin s → ℝ) : Prop :=
  ∀ i, 2 * x i = Ends n r x i false + Ends n r x i true

lemma sum_bool_comm {α : Type*} [AddCommMonoid α] (f : Bool → α) :
    (∑ b : Bool, f b) = f false + f true := by
  have hu : (Finset.univ : Finset Bool) = {false, true} := by decide
  rw [hu, Finset.sum_pair (by decide)]

lemma exists_min_on_univ (x : Fin s → ℝ) (start : Fin s) :
    ∃ i : Fin s, ∀ j : Fin s, x i ≤ x j := by
  classical
  let imgs : Finset ℝ := Finset.univ.image x
  have hne : imgs.Nonempty := ⟨x start, Finset.mem_image_of_mem x (Finset.mem_univ start)⟩
  let mval := imgs.min' hne
  have hm : mval ∈ imgs := Finset.min'_mem imgs hne
  obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hm
  refine ⟨i, fun j => ?_⟩
  rw [hi]
  exact Finset.min'_le imgs (x j) (Finset.mem_image_of_mem x (Finset.mem_univ j))

theorem minimumLaw (hn : Absorbs n) (x : Fin s → ℝ)
    (h : ∀ i, (n i false).elim 0 x + (n i true).elim 0 x ≤ 2 * x i) :
    ∀ i, 0 ≤ x i := by
  classical
  intro start
  obtain ⟨i, hle⟩ := exists_min_on_univ x start
  suffices 0 ≤ x i by exact this.trans (hle start)
  by_contra! hi
  obtain ⟨c, hc⟩ := hn
  let F := fun o : Option (Fin s) => o.bind (fun j => n j (c j))
  have hb (o : Option (Fin s)) : x i ≤ o.elim 0 x := by cases o <;> simp [hi.le, hle]
  have step (o : Option (Fin s)) (ho : o.elim 0 x = x i) : (F o).elim 0 x = x i := by
    cases o with
    | none => exact ho
    | some j =>
      change x j = x i at ho
      have hj := h j
      rw [ho] at hj
      have h0 := hb (n j false)
      have h1 := hb (n j true)
      change (n j (c j)).elim 0 x = x i
      cases c j <;> linarith
  have rep (k : ℕ) : (F^[k] (some i)).elim 0 x = x i := by
    induction k with
    | zero => rfl
    | succ k ih => rw [Function.iterate_succ_apply']; exact step _ ih
  have he := rep s
  rw [show F^[s] (some i) = none from hc i] at he
  exact hi.ne (by simpa using he.symm)

def drift : (Fin s → ℝ) →ₗ[ℝ] (Fin s → ℝ) where
  toFun x i := 2 * x i - (n i false).elim 0 x - (n i true).elim 0 x
  map_add' x y := by
    ext i
    cases h0 : n i false <;> cases h1 : n i true <;> simp [h0, h1] <;> ring
  map_smul' a x := by
    ext i
    cases h0 : n i false <;> cases h1 : n i true <;> simp [h0, h1] <;> ring

theorem uniqueDrift (hn : Absorbs n) : Function.Injective (drift n) := by
  apply LinearMap.ker_eq_bot.mp
  rw [LinearMap.ker_eq_bot']
  intro x hx
  have hz (i) : 2 * x i = (n i false).elim 0 x + (n i true).elim 0 x := by
    have h := congrFun hx i
    change 2 * x i - _ - _ = 0 at h
    linarith
  have hp := minimumLaw n hn x (fun i => (hz i).ge)
  have hm := minimumLaw n hn (fun j => -x j) (fun i => by
    specialize hz i
    cases h0 : n i false <;> cases h1 : n i true <;> simp [h0, h1] at hz ⊢ <;> linarith)
  ext i
  exact le_antisymm (neg_nonneg.mp (hm i)) (hp i)

def boundary (r : Fin s → Bool → ℝ) (i : Fin s) : ℝ :=
  (n i false).elim (r i false) (fun _ => 0) + (n i true).elim (r i true) (fun _ => 0)

theorem solves_iff (r : Fin s → Bool → ℝ) (x : Fin s → ℝ) :
    Solves n r x ↔ drift n x = boundary n r := by
  constructor
  · intro h
    ext i
    specialize h i
    change 2 * x i - _ - _ = _
    cases h0 : n i false <;> cases h1 : n i true <;>
      simp [Ends, boundary, h0, h1] at h ⊢ <;> linarith
  · intro h i
    have hh := congrFun h i
    change 2 * x i - _ - _ = _ at hh
    cases h0 : n i false <;> cases h1 : n i true <;>
      simp [Ends, boundary, h0, h1] at hh ⊢ <;> linarith

noncomputable def mean (hn : Absorbs n) : (Fin s → Bool → ℝ) →ₗ[ℝ] (Fin s → ℝ) :=
  (LinearEquiv.ofBijective (drift n)
    ⟨uniqueDrift n hn, LinearMap.surjective_of_injective (uniqueDrift n hn)⟩).symm.toLinearMap.comp
      ({
        toFun := boundary n
        map_add' := by
          intro x y
          ext i
          cases h0 : n i false <;> cases h1 : n i true <;> simp [boundary, h0, h1] <;> ring
        map_smul' := by
          intro a x
          ext i
          cases h0 : n i false <;> cases h1 : n i true <;> simp [boundary, h0, h1] <;> ring } :
        (Fin s → Bool → ℝ) →ₗ[ℝ] (Fin s → ℝ))

theorem mean_solves (hn : Absorbs n) (r) : Solves n r (mean n hn r) := by
  rw [solves_iff]
  exact (LinearEquiv.ofBijective (drift n)
    ⟨uniqueDrift n hn, LinearMap.surjective_of_injective (uniqueDrift n hn)⟩).apply_symm_apply _

theorem eqMean (hn : Absorbs n) {r x} (h : Solves n r x) : x = mean n hn r :=
  uniqueDrift n hn (((solves_iff n _ _).mp h).trans ((solves_iff n _ _).mp (mean_solves n hn r)).symm)

theorem mean_nonneg (hn : Absorbs n) (r : Fin s → Bool → ℝ) (hr : ∀ i b, 0 ≤ r i b) :
    ∀ i, 0 ≤ mean n hn r i := by
  apply minimumLaw n hn
  intro i
  rw [mean_solves n hn r i]
  cases h0 : n i false <;> cases h1 : n i true <;> simp [Ends, h0, h1, hr, add_nonneg]

end LinearCore

def Dyad (x : ℝ) : Prop := ∃ b k : ℕ, (2 : ℝ) ^ b * x = (k : ℝ)

lemma dyadNat (k : ℕ) : Dyad (k : ℝ) := ⟨0, k, by simp⟩

lemma dyadMid {x y z : ℝ} (h : 2 * z = x + y) (hx : Dyad x) (hy : Dyad y) : Dyad z := by
  obtain ⟨b, m, hm⟩ := hx
  obtain ⟨c, k, hk⟩ := hy
  refine ⟨b + c + 1, 2 ^ c * m + 2 ^ b * k, ?_⟩
  push_cast
  rw [pow_succ, pow_add]
  linear_combination (2 ^ b * 2 ^ c) * h + 2 ^ c * hm + 2 ^ b * hk

lemma not_dyad_of_non_dvd {D a : ℕ} {x : ℝ} (hx : (D : ℝ) * x = (a : ℝ))
    (hnd : ∀ b : ℕ, ¬ D ∣ 2 ^ b * a) : ¬ Dyad x := by
  rintro ⟨b, k, hk⟩
  have heq : ((2 ^ b * a : ℕ) : ℝ) = ((D * k : ℕ) : ℝ) := by
    push_cast
    linear_combination (2 : ℝ) ^ b * hx.symm + (D : ℝ) * hk
  have hnat : 2 ^ b * a = D * k := Nat.cast_injective heq
  exact hnd b ⟨k, hnat⟩

def runFrom {s : ℕ} (n : Fin s → Bool → Option (Fin s)) (x : Option (Fin s)) (L : List Bool) :
    Option (Fin s) :=
  L.foldl (fun (y : Option (Fin s)) (bit : Bool) => y.bind (fun i => n i bit)) x

lemma runFrom_nil {s : ℕ} (n : Fin s → Bool → Option (Fin s)) (x : Option (Fin s)) :
    runFrom n x [] = x := rfl

lemma runFrom_none {s : ℕ} (n : Fin s → Bool → Option (Fin s)) (L : List Bool) :
    runFrom n none L = none := by
  induction L with
  | nil => rfl
  | cons a t ih => exact ih

lemma runFrom_append {s : ℕ} (n : Fin s → Bool → Option (Fin s)) (x : Option (Fin s))
    (L1 L2 : List Bool) :
    runFrom n x (L1 ++ L2) = runFrom n (runFrom n x L1) L2 := by
  dsimp only [runFrom]
  exact List.foldl_append

lemma runFrom_singleton {s : ℕ} (n : Fin s → Bool → Option (Fin s)) (x : Fin s) (b : Bool) :
    runFrom n (some x) [b] = n x b := rfl

lemma runFrom_cons {s : ℕ} (n : Fin s → Bool → Option (Fin s)) (x : Option (Fin s))
    (b : Bool) (L : List Bool) :
    runFrom n x (b :: L) = runFrom n (x.bind (fun i => n i b)) L := rfl

lemma runFrom_repeat {s : ℕ} (n : Fin s → Bool → Option (Fin s)) (x : Fin s) (L : List Bool)
    (hcyc : runFrom n (some x) L = some x) (q : ℕ) :
    runFrom n (some x) (List.flatten (List.replicate q L)) = some x := by
  induction q with
  | zero => rfl
  | succ q ih =>
    rw [List.replicate_succ, List.flatten_cons, runFrom_append, hcyc, ih]

lemma runFrom_append_some {s : ℕ} (n : Fin s → Bool → Option (Fin s)) (x : Option (Fin s))
    (L1 L2 : List Bool) (y : Fin s) (h : runFrom n x (L1 ++ L2) = some y) :
    ∃ w : Fin s, runFrom n x L1 = some w ∧ runFrom n (some w) L2 = some y := by
  rw [runFrom_append] at h
  cases h1 : runFrom n x L1 with
  | none =>
    rw [h1, runFrom_none] at h
    cases h
  | some w =>
    rw [h1] at h
    exact ⟨w, rfl, h⟩

lemma list_ofFn_get {b : ℕ} (L : List Bool) (hL : L.length = b) :
    List.ofFn (fun i : Fin b => L[i.val]'(by omega)) = L := by
  apply List.ext_getElem
  · simp [hL]
  · intro i h1 h2
    simp

lemma list_ofFn_snoc {b : ℕ} (w : Fin b → Bool) (bit : Bool) :
    List.ofFn (Fin.snoc w bit) = List.ofFn w ++ [bit] := by
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp only [List.getElem_ofFn, List.getElem_append, List.length_ofFn, List.getElem_singleton]
    split_ifs with hi
    · have : (⟨i, by simp only [List.length_ofFn] at h1; exact h1⟩ : Fin (b + 1)) =
          Fin.castSucc ⟨i, hi⟩ := rfl
      rw [this, Fin.snoc_castSucc]
    · have hib : i = b := by simp only [List.length_ofFn] at h1; omega
      have : (⟨i, by simp only [List.length_ofFn] at h1; exact h1⟩ : Fin (b + 1)) =
          Fin.last b := Fin.ext hib
      rw [this, Fin.snoc_last]

lemma append_singleton_inj {α : Type*} {L1 L2 : List α} {a1 a2 : α}
    (h : L1 ++ [a1] = L2 ++ [a2]) : L1 = L2 ∧ a1 = a2 := by
  have hlen : L1.length = L2.length := by
    have := congrArg List.length h
    simp at this
    exact this
  have h1 : L1 = L2 := by
    apply List.ext_getElem hlen
    intro i hi1 hi2
    have := congrArg (fun L => L[i]?) h
    simp only [List.getElem?_append_left hi1, List.getElem?_append_left hi2,
      List.getElem?_eq_getElem hi1, List.getElem?_eq_getElem hi2] at this
    exact Option.some.inj this
  subst h1
  have h2 := congrArg (fun L => L[L1.length]?) h
  simp at h2
  exact ⟨rfl, h2⟩

lemma exists_cycle_of_closed {s : ℕ} (n : Fin s → Bool → Option (Fin s))
    (S : Finset (Fin s)) (hS_ne : S.Nonempty)
    (hS_step : ∀ x ∈ S, ∃ b k, n x b = some k ∧ k ∈ S) :
    ∃ C : Finset (Fin s), C.Nonempty ∧ C ⊆ S ∧
      (∀ c ∈ C, ∃ x ∈ C, ∃ b, n x b = some c) ∧
      (∀ c1 ∈ C, ∀ c2 ∈ C, ∃ L : List Bool, runFrom n (some c1) L = some c2) := by
  classical
  obtain ⟨x0, hx0⟩ := hS_ne
  let stepBit : Fin s → Bool := fun x =>
    if hx : x ∈ S then Classical.choose (hS_step x hx) else false
  let stepSt : Fin s → Fin s := fun x =>
    if hx : x ∈ S then Classical.choose (Classical.choose_spec (hS_step x hx)) else x
  have hstep : ∀ x ∈ S, n x (stepBit x) = some (stepSt x) ∧ stepSt x ∈ S := by
    intro x hx
    dsimp only [stepBit, stepSt]
    rw [dif_pos hx, dif_pos hx]
    exact Classical.choose_spec (Classical.choose_spec (hS_step x hx))
  let st : ℕ → Fin s := fun t => stepSt^[t] x0
  have hst_mem : ∀ t, st t ∈ S := by
    intro t
    induction t with
    | zero => exact hx0
    | succ t ih =>
      rw [show st (t + 1) = stepSt (st t) from Function.iterate_succ_apply' stepSt t x0]
      exact (hstep (st t) ih).2
  have hst_next : ∀ t, n (st t) (stepBit (st t)) = some (st (t + 1)) := by
    intro t
    have h1 := (hstep (st t) (hst_mem t)).1
    rwa [show stepSt (st t) = st (t + 1) from (Function.iterate_succ_apply' stepSt t x0).symm] at h1
  have hex_rep : ∃ q : ℕ, ∃ q1 < q, st q1 = st q := by
    have hnot_inj : ¬ Function.Injective (fun i : Fin (s + 1) => st i.val) := by
      intro hinj
      have := Fintype.card_le_of_injective _ hinj
      simp at this
    rw [Function.Injective] at hnot_inj
    push Not at hnot_inj
    obtain ⟨i1, i2, heq, hne⟩ := hnot_inj
    have hne_val : i1.val ≠ i2.val := fun h => hne (Fin.ext h)
    rcases Nat.lt_or_gt_of_ne hne_val with hlt | hgt
    · exact ⟨i2.val, i1.val, hlt, heq⟩
    · exact ⟨i1.val, i2.val, hgt, heq.symm⟩
  let q2 := Nat.find hex_rep
  obtain ⟨q1, hq12, hst_eq⟩ := Nat.find_spec hex_rep
  let p := q2 - q1
  have hp_pos : 0 < p := by omega
  let cyc : Fin p → Fin s := fun r => st (q1 + r.val)
  have hcyc_step : ∀ r : Fin p,
      n (cyc r) (stepBit (cyc r)) = some (cyc ⟨(r.val + 1) % p, Nat.mod_lt _ hp_pos⟩) := by
    intro r
    dsimp only [cyc]
    rw [hst_next]
    congr 1
    by_cases hlt : r.val + 1 < p
    · rw [Nat.mod_eq_of_lt hlt, Nat.add_assoc]
    · have hlast : r.val + 1 = p := by omega
      rw [hlast, Nat.mod_self, add_zero, show q1 + r.val + 1 = q2 by omega, hst_eq]
  let C : Finset (Fin s) := Finset.univ.image cyc
  refine ⟨C, ⟨cyc ⟨0, hp_pos⟩, Finset.mem_image_of_mem cyc (Finset.mem_univ _)⟩, ?_, ?_, ?_⟩
  · intro c hc
    obtain ⟨r, _, rfl⟩ := Finset.mem_image.mp hc
    exact hst_mem _
  · intro c hc
    obtain ⟨r, _, rfl⟩ := Finset.mem_image.mp hc
    let rprev : Fin p := ⟨(r.val + p - 1) % p, Nat.mod_lt _ hp_pos⟩
    refine ⟨cyc rprev, Finset.mem_image_of_mem cyc (Finset.mem_univ rprev), stepBit (cyc rprev), ?_⟩
    rw [hcyc_step rprev]
    congr 2
    apply Fin.ext
    dsimp only [rprev]
    by_cases hr0 : r.val = 0
    · rw [hr0, zero_add, Nat.mod_eq_of_lt (by omega : p - 1 < p),
        show p - 1 + 1 = p by omega, Nat.mod_self]
    · have h1 : (r.val + p - 1) % p = r.val - 1 := by
        rw [show r.val + p - 1 = (r.val - 1) + p by omega, Nat.add_mod_right,
          Nat.mod_eq_of_lt (by omega : r.val - 1 < p)]
      rw [h1, show r.val - 1 + 1 = r.val by omega, Nat.mod_eq_of_lt r.isLt]
  · intro c1 hc1 c2 hc2
    obtain ⟨r1, _, rfl⟩ := Finset.mem_image.mp hc1
    obtain ⟨r2, _, rfl⟩ := Finset.mem_image.mp hc2
    have hwalk : ∀ t : ℕ, ∃ L : List Bool,
        runFrom n (some (cyc r1)) L = some (cyc ⟨(r1.val + t) % p, Nat.mod_lt _ hp_pos⟩) := by
      intro t
      induction t with
      | zero =>
        refine ⟨[], ?_⟩
        simp [runFrom_nil, Nat.mod_eq_of_lt r1.isLt]
      | succ t ih =>
        obtain ⟨L, hL⟩ := ih
        let rt : Fin p := ⟨(r1.val + t) % p, Nat.mod_lt _ hp_pos⟩
        refine ⟨L ++ [stepBit (cyc rt)], ?_⟩
        rw [runFrom_append, hL, runFrom_singleton, hcyc_step rt]
        congr 2
        apply Fin.ext
        dsimp only [rt]
        rw [← Nat.add_assoc, Nat.mod_add_mod]
    obtain ⟨L, hL⟩ := hwalk ((r2.val + p - r1.val) % p)
    refine ⟨L, ?_⟩
    rw [hL]
    congr 2
    apply Fin.ext
    dsimp only
    rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
    have hsum : r1.val + (r2.val + p - r1.val) = r2.val + p := by omega
    rw [hsum, Nat.add_mod_right, Nat.mod_eq_of_lt r2.isLt]

lemma unroll_tree {s : ℕ} (n0 : Fin s → Bool → Option (Fin s))
    (val : Fin s → ℝ) (lv : Fin s → Bool → ℝ)
    (hval : ∀ i, 2 * val i = ∑ bit : Bool, (n0 i bit).elim (lv i bit) val)
    (B : ℕ) (x : Option (Fin s)) :
    (2 : ℝ) ^ B * x.elim 0 val =
      (∑ t : Fin B, (2 : ℝ) ^ (B - 1 - t.val) *
        ∑ w : Fin t.val → Bool, (runFrom n0 x (List.ofFn w)).elim 0
          (fun i => ∑ bit : Bool, if n0 i bit = none then lv i bit else 0)) +
      ∑ w : Fin B → Bool, (runFrom n0 x (List.ofFn w)).elim 0 val := by
  classical
  induction B with
  | zero =>
    simp only [pow_zero, one_mul, Finset.univ_eq_empty, Finset.sum_empty, zero_add]
    have huniq : ∀ w : Fin 0 → Bool, List.ofFn w = [] := fun w => by simp
    have hcard : (Finset.univ : Finset (Fin 0 → Bool)) = {Fin.elim0} := by
      ext w
      simp only [Finset.mem_univ, Finset.mem_singleton, true_iff]
      funext i
      exact Fin.elim0 i
    rw [hcard, Finset.sum_singleton, huniq, runFrom_nil]
  | succ B ih =>
    have hmul : (2 : ℝ) ^ (B + 1) * x.elim 0 val = 2 * ((2 : ℝ) ^ B * x.elim 0 val) := by
      rw [pow_succ']; ring
    rw [hmul, ih, mul_add, Finset.mul_sum]
    have hfirst :
        ∑ t : Fin B, 2 * ((2 : ℝ) ^ (B - 1 - t.val) *
          ∑ w : Fin t.val → Bool, (runFrom n0 x (List.ofFn w)).elim 0
            (fun i => ∑ bit : Bool, if n0 i bit = none then lv i bit else 0)) =
        ∑ t : Fin B, (2 : ℝ) ^ (B - t.val) *
          ∑ w : Fin t.val → Bool, (runFrom n0 x (List.ofFn w)).elim 0
            (fun i => ∑ bit : Bool, if n0 i bit = none then lv i bit else 0) := by
      apply Finset.sum_congr rfl
      intro t _
      have hexp : B - t.val = (B - 1 - t.val) + 1 := by omega
      rw [hexp, pow_succ']
      ring
    rw [hfirst, Finset.mul_sum]
    have hstep : ∀ w : Fin B → Bool,
        2 * (runFrom n0 x (List.ofFn w)).elim 0 val =
        (runFrom n0 x (List.ofFn w)).elim 0
          (fun i => ∑ bit : Bool, if n0 i bit = none then lv i bit else 0) +
        ∑ bit : Bool, (runFrom n0 x (List.ofFn w ++ [bit])).elim 0 val := by
      intro w
      cases hrun : runFrom n0 x (List.ofFn w) with
      | none =>
        simp only [Option.elim_none, mul_zero, zero_add]
        symm
        apply Finset.sum_eq_zero
        intro bit _
        rw [runFrom_append, hrun, runFrom_none]
        rfl
      | some i =>
        simp only [Option.elim_some]
        rw [hval i]
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro bit _
        rw [runFrom_append, hrun, runFrom_singleton]
        cases hn : n0 i bit with
        | none => simp
        | some k => simp
    simp_rw [hstep, Finset.sum_add_distrib]
    have hsnoc :
        (∑ w : Fin B → Bool, ∑ bit : Bool,
          (runFrom n0 x (List.ofFn w ++ [bit])).elim 0 val) =
        ∑ w' : Fin (B + 1) → Bool, (runFrom n0 x (List.ofFn w')).elim 0 val := by
      rw [← Fintype.sum_prod_type']
      let e : (Fin B → Bool) × Bool ≃ (Fin (B + 1) → Bool) :=
        (Equiv.prodComm (Fin B → Bool) Bool).trans (Fin.snocEquiv (fun _ : Fin (B + 1) => Bool))
      refine Fintype.sum_equiv e _ _ (fun p => ?_)
      have he : e p = Fin.snoc p.1 p.2 := rfl
      rw [he, list_ofFn_snoc]
    rw [hsnoc, ← add_assoc]
    congr 1
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last, Nat.add_sub_cancel, Nat.sub_self, pow_zero, one_mul]

lemma unroll_leaf_sum {s : ℕ} (n0 : Fin s → Bool → Option (Fin s))
    (z : Fin s) (B : ℕ) (pred : Fin s → Bool → Prop) [∀ i b, Decidable (pred i b)]
    (W : List Bool) (hW_pos : 1 ≤ W.length) (hW_le : W.length ≤ B)
    (hW : ∀ L_init b, (∃ i, runFrom n0 (some z) L_init = some i ∧ pred i b) ↔ L_init ++ [b] = W)
    (a : ℝ) :
    (∑ t : Fin B, (2 : ℝ) ^ (B - 1 - t.val) *
      ∑ w : Fin t.val → Bool, (runFrom n0 (some z) (List.ofFn w)).elim 0
        (fun i => ∑ bit : Bool, if pred i bit then a else 0)) =
    (2 : ℝ) ^ (B - W.length) * a := by
  let t0 : Fin B := ⟨W.length - 1, by omega⟩
  rw [Finset.sum_eq_single t0]
  · have hsub : B - 1 - t0.val = B - W.length := by dsimp only [t0]; omega
    rw [hsub]
    congr 1
    let w0 : Fin t0.val → Bool := fun r => W[r.val]'(by dsimp only [t0]; omega)
    let b0 : Bool := W[t0.val]'(by dsimp only [t0]; omega)
    have hW_eq : List.ofFn w0 ++ [b0] = W := by
      apply List.ext_getElem
      · simp [t0]; omega
      · intro k hk1 hk2
        simp only [List.getElem_append, List.length_ofFn, List.getElem_ofFn, List.getElem_singleton]
        split_ifs with hlt
        · rfl
        · have hk : k = t0.val := by simp only [List.length_ofFn, t0] at hk1 hk2 hlt ⊢; omega
          subst hk; rfl
    rw [Finset.sum_eq_single w0]
    · obtain ⟨i0, hi0_run, hi0_pred⟩ := (hW (List.ofFn w0) b0).mpr hW_eq
      rw [hi0_run]
      simp only [Option.elim_some]
      rw [Finset.sum_eq_single b0]
      · rw [if_pos hi0_pred]
      · intro bit _ hne
        rw [if_neg]
        intro hp
        have h1 := (hW (List.ofFn w0) bit).mp ⟨i0, hi0_run, hp⟩
        rw [← hW_eq] at h1
        exact hne (append_singleton_inj h1).2
      · intro h; exact absurd (Finset.mem_univ b0) h
    · intro w _ hne
      cases hrun : runFrom n0 (some z) (List.ofFn w) with
      | none => rfl
      | some i =>
        simp only [Option.elim_some]
        apply Finset.sum_eq_zero
        intro bit _
        rw [if_neg]
        intro hp
        have h1 := (hW (List.ofFn w) bit).mp ⟨i, hrun, hp⟩
        rw [← hW_eq] at h1
        have hw_eq : List.ofFn w = List.ofFn w0 := (append_singleton_inj h1).1
        exact hne (List.ofFn_injective hw_eq)
    · intro h; exact absurd (Finset.mem_univ w0) h
  · intro t _ hne
    have hinner :
        (∑ w : Fin t.val → Bool, (runFrom n0 (some z) (List.ofFn w)).elim 0
          (fun i => ∑ bit : Bool, if pred i bit then a else 0)) = 0 := by
      apply Finset.sum_eq_zero
      intro w _
      cases hrun : runFrom n0 (some z) (List.ofFn w) with
      | none => rfl
      | some i =>
        simp only [Option.elim_some]
        apply Finset.sum_eq_zero
        intro bit _
        rw [if_neg]
        intro hp
        have h1 := (hW (List.ofFn w) bit).mp ⟨i, hrun, hp⟩
        have hlen := congrArg List.length h1
        simp at hlen
        apply hne
        apply Fin.ext
        dsimp only [t0]
        omega
    rw [hinner, mul_zero]
  · intro h; exact absurd (Finset.mem_univ t0) h

lemma part1_main (m D : ℕ) (A : Fin m → ℕ) (hm : 2 ≤ m) (hD : 0 < D)
    (hA : ∀ j, 0 < A j ∧ ∀ b : ℕ, ¬ D ∣ 2 ^ b * A j)
    (s : ℕ) (z : Fin s) (n : Fin s → Bool → Option (Fin s))
    (out : Fin s → Bool → Fin m) (P : Fin s → Fin m → ℝ)
    (hn : Absorbs n)
    (hP_eq : ∀ i j, 2 * P i j = ∑ bit : Bool, (n i bit).elim
      (if out i bit = j then (1 : ℝ) else 0) (fun k => P k j))
    (hP_z : ∀ j, (D : ℝ) * P z j = (A j : ℝ)) :
    m ≤ s ∧ (s ≤ m →
      ∃ (p : ℕ) (d : Fin m → ℕ),
        (2 ≤ p ∧ ∀ j, 0 < d j ∧ A j * (2 ^ p - 1) * 2 ^ (d j) = D * 2 ^ p) ∧
        ∀ b j,
          (∑ w : Fin b → Bool, ((List.ofFn w).foldl
            (fun (x : Option (Fin s)) (bit : Bool) => x.bind (fun i => n i bit)) (some z)).elim 0
            (fun i => ((Finset.univ : Finset Bool).filter
              (fun bit => n i bit = none ∧ out i bit = j)).card)) =
          if d j ≤ b + 1 ∧ p ∣ b + 1 - d j then 1 else 0) := by
  classical
  have hP_solves : ∀ j, Solves n (fun i bit => if out i bit = j then (1 : ℝ) else 0) (fun i => P i j) := by
    intro j i
    have h := hP_eq i j
    rw [sum_bool_comm] at h
    exact h
  have hP_nonneg : ∀ i j, 0 ≤ P i j := by
    intro i j
    have heq := eqMean n hn (hP_solves j)
    have hnn := mean_nonneg n hn (fun i' bit => if out i' bit = j then (1 : ℝ) else 0)
      (fun i' bit => by split_ifs <;> norm_num) i
    rw [show P i j = mean n hn (fun i' bit => if out i' bit = j then (1 : ℝ) else 0) i from congrFun heq i]
    exact hnn
  have hP_z_nondyad : ∀ j, ¬ Dyad (P z j) := fun j =>
    not_dyad_of_non_dvd (hP_z j) (hA j).2
  let Rset : Finset (Fin s) :=
    Finset.univ.filter (fun x => ∃ L : List Bool, runFrom n (some z) L = some x)
  have hz_R : z ∈ Rset := Finset.mem_filter.mpr ⟨Finset.mem_univ z, ⟨[], rfl⟩⟩
  have hR_closed : ∀ x ∈ Rset, ∀ bit y, n x bit = some y → y ∈ Rset := by
    intro x hx bit y hxy
    obtain ⟨L, hL⟩ := (Finset.mem_filter.mp hx).2
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ y, ⟨L ++ [bit], ?_⟩⟩
    rw [runFrom_append, hL, runFrom_singleton, hxy]
  let u := Rset.card
  have hu_le : u ≤ s := by
    calc u = Rset.card := rfl
      _ ≤ (Finset.univ : Finset (Fin s)).card := Finset.card_le_card (Finset.subset_univ Rset)
      _ = s := Fintype.card_fin s
  let Exits : Finset (Fin s × Bool) :=
    (Rset ×ˢ (Finset.univ : Finset Bool)).filter (fun e => n e.1 e.2 = none)
  let Internal : Finset (Fin s × Bool) :=
    (Rset ×ˢ (Finset.univ : Finset Bool)).filter (fun e => (n e.1 e.2).isSome)
  have hcard_sum : Exits.card + Internal.card = 2 * u := by
    have hdisj : Disjoint Exits Internal := by
      rw [Finset.disjoint_left]
      intro e he1 he2
      have h1 := (Finset.mem_filter.mp he1).2
      have h2 := (Finset.mem_filter.mp he2).2
      rw [h1] at h2
      simp at h2
    have hunion : Exits ∪ Internal = Rset ×ˢ (Finset.univ : Finset Bool) := by
      ext e
      simp only [Finset.mem_union, Exits, Internal, Finset.mem_filter]
      constructor
      · rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact h
      · intro h
        cases hne : n e.1 e.2 with
        | none => left; exact ⟨h, rfl⟩
        | some y => right; exact ⟨h, rfl⟩
    rw [← Finset.card_union_of_disjoint hdisj, hunion, Finset.card_product]
    have hbool : (Finset.univ : Finset Bool).card = 2 := by decide
    rw [hbool, mul_comm]
  have hzero_on_closed : ∀ (S : Finset (Fin s)) (j : Fin m),
      (∀ x ∈ S, ∀ bit y, n x bit = some y → y ∈ S) →
      (∀ x ∈ S, ∀ bit, n x bit = none → out x bit ≠ j) →
      ∀ x ∈ S, P x j = 0 := by
    intro S j hS_cl hS_no
    let Q : Fin s → ℝ := fun i => if i ∈ S then -(P i j) else 0
    have hQ : ∀ i, (n i false).elim 0 Q + (n i true).elim 0 Q ≤ 2 * Q i := by
      intro i
      by_cases hi : i ∈ S
      · have hterm : ∀ bit : Bool,
            (n i bit).elim 0 Q = -((n i bit).elim (if out i bit = j then (1 : ℝ) else 0) (fun k => P k j)) := by
          intro bit
          cases hnb : n i bit with
          | none =>
            simp only [Option.elim_none]
            rw [if_neg (hS_no i hi bit hnb), neg_zero]
          | some k =>
            simp only [Option.elim_some, Q, if_pos (hS_cl i hi bit k hnb)]
        rw [hterm false, hterm true]
        have hsol := hP_solves j i
        dsimp only [Ends] at hsol
        simp only [Q, if_pos hi]
        linarith
      · simp only [Q, if_neg hi, mul_zero]
        have hle : ∀ bit : Bool, (n i bit).elim 0 Q ≤ 0 := by
          intro bit
          cases n i bit with
          | none => simp
          | some k =>
            simp only [Option.elim_some, Q]
            split_ifs
            · linarith [hP_nonneg k j]
            · exact le_rfl
        linarith [hle false, hle true]
    have hmin := minimumLaw n hn Q hQ
    intro x hx
    have h1 : 0 ≤ -(P x j) := by simpa [Q, hx] using hmin x
    linarith [hP_nonneg x j]
  have hexits_surj : ∀ j : Fin m, ∃ e ∈ Exits, out e.1 e.2 = j := by
    intro j
    by_contra hno
    push Not at hno
    have hz0 : P z j = 0 := hzero_on_closed Rset j hR_closed (fun x hx bit hnb =>
      hno (x, bit) (Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hx, Finset.mem_univ bit⟩, hnb⟩)) z hz_R
    have hpos : (0 : ℝ) < (A j : ℝ) := Nat.cast_pos.mpr (hA j).1
    have hDz := hP_z j
    rw [hz0, mul_zero] at hDz
    linarith
  have hm_le_exits : m ≤ Exits.card := by
    have hsub : (Finset.univ : Finset (Fin m)) ⊆ Exits.image (fun e => out e.1 e.2) := by
      intro j _
      obtain ⟨e, he, hout⟩ := hexits_surj j
      exact Finset.mem_image.mpr ⟨e, he, hout⟩
    calc m = (Finset.univ : Finset (Fin m)).card := (Fintype.card_fin m).symm
      _ ≤ (Exits.image (fun e => out e.1 e.2)).card := Finset.card_le_card hsub
      _ ≤ Exits.card := Finset.card_image_le
  let j0 : Fin m := ⟨0, by omega⟩
  let Bad : Finset (Fin s) := Rset.filter (fun i => ¬ Dyad (P i j0))
  have hz_Bad : z ∈ Bad := Finset.mem_filter.mpr ⟨hz_R, hP_z_nondyad j0⟩
  have hBad_step : ∀ x ∈ Bad, ∃ bit k, n x bit = some k ∧ k ∈ Bad := by
    intro x hx
    have hxR : x ∈ Rset := (Finset.mem_filter.mp hx).1
    have hxND : ¬ Dyad (P x j0) := (Finset.mem_filter.mp hx).2
    by_contra hno
    push Not at hno
    apply hxND
    have hbranch : ∀ bit : Bool,
        Dyad ((n x bit).elim (if out x bit = j0 then (1 : ℝ) else 0) (fun k => P k j0)) := by
      intro bit
      cases hnb : n x bit with
      | none =>
        simp only [Option.elim_none]
        split_ifs
        · exact dyadNat 1
        · exact dyadNat 0
      | some k =>
        simp only [Option.elim_some]
        have hkR : k ∈ Rset := hR_closed x hxR bit k hnb
        have hkNB : k ∉ Bad := hno bit k hnb
        by_contra hnk
        exact hkNB (Finset.mem_filter.mpr ⟨hkR, hnk⟩)
    exact dyadMid (hP_solves j0 x) (hbranch false) (hbranch true)
  obtain ⟨Cset, hC_ne, hC_sub_Bad, hC_in, hC_conn⟩ := exists_cycle_of_closed n Bad ⟨z, hz_Bad⟩ hBad_step
  have hC_sub_R : Cset ⊆ Rset := fun x hx => (Finset.mem_filter.mp (hC_sub_Bad hx)).1
  let tgt : Fin s × Bool → Option (Fin s) := fun e => n e.1 e.2
  have hin_R : ∀ y ∈ Rset, y ≠ z → ∃ e ∈ Internal, tgt e = some y := by
    intro y hy hne
    obtain ⟨L, hL⟩ := (Finset.mem_filter.mp hy).2
    cases L using List.reverseRecOn with
    | nil =>
      rw [runFrom_nil] at hL
      exact absurd (Option.some.inj hL).symm hne
    | append_singleton L' bit =>
      obtain ⟨x', hx', hstep⟩ := runFrom_append_some n (some z) L' [bit] y hL
      rw [runFrom_singleton] at hstep
      have hx'R : x' ∈ Rset := Finset.mem_filter.mpr ⟨Finset.mem_univ x', ⟨L', hx'⟩⟩
      refine ⟨(x', bit), Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hx'R, Finset.mem_univ bit⟩, ?_⟩, hstep⟩
      rw [hstep]; rfl
  have hu_le_int : u ≤ Internal.card := by
    by_cases hzC : z ∈ Cset
    · have hsub : Rset.image some ⊆ Internal.image tgt := by
        intro o ho
        obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp ho
        by_cases hyz : y = z
        · rw [hyz]
          obtain ⟨x, hxC, bit, hstep⟩ := hC_in z hzC
          have hxR : x ∈ Rset := hC_sub_R hxC
          refine Finset.mem_image.mpr ⟨(x, bit), ?_, hstep⟩
          refine Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hxR, Finset.mem_univ bit⟩, ?_⟩
          rw [hstep]; rfl
        · obtain ⟨e, he, hte⟩ := hin_R y hy hyz
          exact Finset.mem_image.mpr ⟨e, he, hte⟩
      calc u = (Rset.image some).card := (Finset.card_image_of_injective Rset (Option.some_injective (Fin s))).symm
        _ ≤ (Internal.image tgt).card := Finset.card_le_card hsub
        _ ≤ Internal.card := Finset.card_image_le
    · have hex_path : ∃ len : ℕ, ∃ c ∈ Cset, ∃ L : List Bool, L.length = len ∧ runFrom n (some z) L = some c := by
        obtain ⟨c, hc⟩ := hC_ne
        obtain ⟨L, hL⟩ := (Finset.mem_filter.mp (hC_sub_R hc)).2
        exact ⟨L.length, c, hc, L, rfl, hL⟩
      let minLen := Nat.find hex_path
      obtain ⟨c0, hc0C, L0, hL0_len, hL0_run⟩ := Nat.find_spec hex_path
      have hL0_ne : L0 ≠ [] := by
        intro hnil
        rw [hnil, runFrom_nil] at hL0_run
        exact hzC (Option.some.inj hL0_run ▸ hc0C)
      cases L0 using List.reverseRecOn with
      | nil => exact absurd rfl hL0_ne
      | append_singleton L_init b0 =>
        obtain ⟨v_prev, hv_run, hv_step⟩ := runFrom_append_some n (some z) L_init [b0] c0 hL0_run
        rw [runFrom_singleton] at hv_step
        have hv_R : v_prev ∈ Rset := Finset.mem_filter.mpr ⟨Finset.mem_univ v_prev, ⟨L_init, hv_run⟩⟩
        have hv_notC : v_prev ∉ Cset := by
          intro hvC
          exact Nat.find_min hex_path (show L_init.length < minLen by simp at hL0_len; omega)
            ⟨v_prev, hvC, L_init, rfl, hv_run⟩
        let e0 : Fin s × Bool := (v_prev, b0)
        have he0_int : e0 ∈ Internal := by
          refine Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hv_R, Finset.mem_univ b0⟩, ?_⟩
          rw [hv_step]; rfl
        have hsub : (Rset.erase z).image some ⊆ (Internal.erase e0).image tgt := by
          intro o ho
          obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp ho
          have hyR : y ∈ Rset := Finset.mem_of_mem_erase hy
          have hyz : y ≠ z := Finset.ne_of_mem_erase hy
          by_cases hyc : y = c0
          · rw [hyc]
            obtain ⟨x, hxC, bit, hstep⟩ := hC_in c0 hc0C
            have hxR : x ∈ Rset := hC_sub_R hxC
            have hne_e0 : (x, bit) ≠ e0 := by
              intro heq
              have : x = v_prev := congrArg Prod.fst heq
              exact hv_notC (this ▸ hxC)
            refine Finset.mem_image.mpr ⟨(x, bit), Finset.mem_erase.mpr ⟨hne_e0, ?_⟩, hstep⟩
            refine Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hxR, Finset.mem_univ bit⟩, ?_⟩
            rw [hstep]; rfl
          · obtain ⟨e, he, hte⟩ := hin_R y hyR hyz
            have hne_e0 : e ≠ e0 := by
              intro heq
              subst heq
              have : some y = some c0 := hte.symm.trans hv_step
              exact hyc (Option.some.inj this)
            exact Finset.mem_image.mpr ⟨e, Finset.mem_erase.mpr ⟨hne_e0, he⟩, hte⟩
        have hcard1 : u - 1 ≤ Internal.card - 1 := by
          calc u - 1 = (Rset.erase z).card := (Finset.card_erase_of_mem hz_R).symm
            _ = ((Rset.erase z).image some).card :=
                (Finset.card_image_of_injective _ (Option.some_injective (Fin s))).symm
            _ ≤ ((Internal.erase e0).image tgt).card := Finset.card_le_card hsub
            _ ≤ (Internal.erase e0).card := Finset.card_image_le
            _ = Internal.card - 1 := Finset.card_erase_of_mem he0_int
        have hint_pos : 1 ≤ Internal.card := Finset.card_pos.mpr ⟨e0, he0_int⟩
        omega
  have hm_le_s : m ≤ s := by omega
  refine ⟨hm_le_s, ?_⟩
  intro hs_le_m
  have hsm : s = m := le_antisymm hs_le_m hm_le_s
  have hum : u = m := by omega
  have hExits_card : Exits.card = m := by omega
  have hInt_card : Internal.card = m := by omega
  have hR_univ : Rset = Finset.univ := by
    apply Finset.eq_univ_of_card
    rw [Fintype.card_fin]
    change u = s
    omega
  have hout_inj : Set.InjOn (fun e : Fin s × Bool => out e.1 e.2) Exits := by
    apply Finset.injOn_of_card_image_eq
    have himg : Exits.image (fun e => out e.1 e.2) = Finset.univ := by
      apply Finset.eq_univ_iff_forall.mpr
      intro j
      obtain ⟨e, he, hout⟩ := hexits_surj j
      exact Finset.mem_image.mpr ⟨e, he, hout⟩
    rw [himg, Finset.card_univ, Fintype.card_fin, hExits_card]
  have hexit_mem : ∀ i bit, n i bit = none → (i, bit) ∈ Exits := by
    intro i bit hnb
    exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hR_univ ▸ Finset.mem_univ i, Finset.mem_univ bit⟩, hnb⟩
  have hint_mem : ∀ i bit y, n i bit = some y → (i, bit) ∈ Internal := by
    intro i bit y hnb
    refine Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hR_univ ▸ Finset.mem_univ i, Finset.mem_univ bit⟩, ?_⟩
    rw [hnb]; rfl
  have hexit_uniq : ∀ j : Fin m, ∀ e1 e2 : Fin s × Bool,
      n e1.1 e1.2 = none → out e1.1 e1.2 = j →
      n e2.1 e2.2 = none → out e2.1 e2.2 = j → e1 = e2 := by
    intro j e1 e2 hn1 ho1 hn2 ho2
    exact hout_inj (hexit_mem e1.1 e1.2 hn1) (hexit_mem e2.1 e2.2 hn2) (ho1.trans ho2.symm)
  have hzC : z ∈ Cset := by
    by_contra hzNotC
    have hex_path : ∃ len : ℕ, ∃ c ∈ Cset, ∃ L : List Bool, L.length = len ∧ runFrom n (some z) L = some c := by
      obtain ⟨c, hc⟩ := hC_ne
      obtain ⟨L, hL⟩ := (Finset.mem_filter.mp (hC_sub_R hc)).2
      exact ⟨L.length, c, hc, L, rfl, hL⟩
    let minLen := Nat.find hex_path
    obtain ⟨c0, hc0C, L0, hL0_len, hL0_run⟩ := Nat.find_spec hex_path
    have hL0_ne : L0 ≠ [] := by
      intro hnil
      rw [hnil, runFrom_nil] at hL0_run
      exact hzNotC (Option.some.inj hL0_run ▸ hc0C)
    cases hL0_rev : L0 using List.reverseRecOn with
    | nil => exact absurd hL0_rev hL0_ne
    | append_singleton L_init b0 =>
      rw [hL0_rev] at hL0_len hL0_run
      obtain ⟨v_prev, hv_run, hv_step⟩ := runFrom_append_some n (some z) L_init [b0] c0 hL0_run
      rw [runFrom_singleton] at hv_step
      have hv_notC : v_prev ∉ Cset := by
        intro hvC
        exact Nat.find_min hex_path (show L_init.length < minLen by simp at hL0_len; omega)
          ⟨v_prev, hvC, L_init, rfl, hv_run⟩
      let e0 : Fin s × Bool := (v_prev, b0)
      have he0_int : e0 ∈ Internal := hint_mem v_prev b0 c0 hv_step
      obtain ⟨xc, hxcC, bc, hxc_step⟩ := hC_in c0 hc0C
      let ec : Fin s × Bool := (xc, bc)
      have hec_ne_e0 : ec ≠ e0 := by
        intro heq
        have hx : xc = v_prev := congrArg Prod.fst heq
        exact hv_notC (hx ▸ hxcC)
      have hec_mem : ec ∈ Internal.erase e0 :=
        Finset.mem_erase.mpr ⟨hec_ne_e0, hint_mem xc bc c0 hxc_step⟩
      have hsub : (Finset.univ.erase z).image some ⊆ (Internal.erase e0).image tgt := by
        intro o ho
        obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp ho
        have hyz : y ≠ z := Finset.ne_of_mem_erase hy
        by_cases hyc : y = c0
        · rw [hyc]
          exact Finset.mem_image.mpr ⟨ec, hec_mem, hxc_step⟩
        · obtain ⟨e, he, hte⟩ := hin_R y (hR_univ ▸ Finset.mem_univ y) hyz
          have hne_e0 : e ≠ e0 := by
            intro heq
            subst heq
            exact hyc (Option.some.inj (hte.symm.trans hv_step))
          exact Finset.mem_image.mpr ⟨e, Finset.mem_erase.mpr ⟨hne_e0, he⟩, hte⟩
      have hcard_lhs : ((Finset.univ.erase z).image some).card = m - 1 := by
        rw [Finset.card_image_of_injective _ (Option.some_injective (Fin s)),
          Finset.card_erase_of_mem (Finset.mem_univ z), Finset.card_univ, Fintype.card_fin]
        omega
      have hcard_rhs : (Internal.erase e0).card = m - 1 := by
        rw [Finset.card_erase_of_mem he0_int, hInt_card]
      have himg_eq : (Internal.erase e0).image tgt = (Finset.univ.erase z).image some :=
        (Finset.eq_of_subset_of_card_le hsub (by rw [hcard_lhs, ← hcard_rhs]; exact Finset.card_image_le)).symm
      have htgt_inj : Set.InjOn tgt (Internal.erase e0) := by
        apply Finset.injOn_of_card_image_eq
        rw [himg_eq, hcard_lhs, hcard_rhs]
      have hno_in_z : ∀ x bit, n x bit ≠ some z := by
        intro x bit hxz
        have hmem : (x, bit) ∈ Internal := hint_mem x bit z hxz
        have hne_e0 : (x, bit) ≠ e0 := by
          intro heq
          have hx : x = v_prev := congrArg Prod.fst heq
          have hb : bit = b0 := congrArg Prod.snd heq
          rw [hx, hb] at hxz
          exact hzNotC (Option.some.inj (hxz.symm.trans hv_step) ▸ hc0C)
        have hmem_img : some z ∈ (Internal.erase e0).image tgt :=
          Finset.mem_image.mpr ⟨(x, bit), Finset.mem_erase.mpr ⟨hne_e0, hmem⟩, hxz⟩
        rw [himg_eq] at hmem_img
        obtain ⟨y, hy, hyz⟩ := Finset.mem_image.mp hmem_img
        exact Finset.ne_of_mem_erase hy (Option.some.inj hyz)
      have hindeg : ∀ y x1 b1 x2 b2,
          n x1 b1 = some y → n x2 b2 = some y → (x1, b1) ≠ (x2, b2) →
          y = c0 ∧ ((x1, b1) = e0 ∨ (x1, b1) = ec) ∧ ((x2, b2) = e0 ∨ (x2, b2) = ec) := by
        intro y x1 b1 x2 b2 h1 h2 hne
        have hm1 : (x1, b1) ∈ Internal := hint_mem x1 b1 y h1
        have hm2 : (x2, b2) ∈ Internal := hint_mem x2 b2 y h2
        by_cases hyc : y = c0
        · refine ⟨hyc, ?_, ?_⟩
          · by_cases he1 : (x1, b1) = e0
            · exact Or.inl he1
            · right
              exact htgt_inj (Finset.mem_erase.mpr ⟨he1, hm1⟩) hec_mem (h1.trans (hyc ▸ hxc_step.symm))
          · by_cases he2 : (x2, b2) = e0
            · exact Or.inl he2
            · right
              exact htgt_inj (Finset.mem_erase.mpr ⟨he2, hm2⟩) hec_mem (h2.trans (hyc ▸ hxc_step.symm))
        · exfalso
          have he1 : (x1, b1) ≠ e0 := by
            intro heq
            have hx : x1 = v_prev := congrArg Prod.fst heq
            have hb : b1 = b0 := congrArg Prod.snd heq
            rw [hx, hb] at h1
            exact hyc (Option.some.inj (h1.symm.trans hv_step))
          have he2 : (x2, b2) ≠ e0 := by
            intro heq
            have hx : x2 = v_prev := congrArg Prod.fst heq
            have hb : b2 = b0 := congrArg Prod.snd heq
            rw [hx, hb] at h2
            exact hyc (Option.some.inj (h2.symm.trans hv_step))
          exact hne (htgt_inj (Finset.mem_erase.mpr ⟨he1, hm1⟩) (Finset.mem_erase.mpr ⟨he2, hm2⟩) (h1.trans h2.symm))
      have hL0_cons : ∃ b1 L_rest, L_init ++ [b0] = b1 :: L_rest := by
        cases L_init with
        | nil => exact ⟨b0, [], rfl⟩
        | cons b1 L_tail => exact ⟨b1, L_tail ++ [b0], rfl⟩
      obtain ⟨b1, L_rest, hcons⟩ := hL0_cons
      rw [hcons] at hL0_run
      have hr1_ex : ∃ r1, n z b1 = some r1 ∧ runFrom n (some r1) L_rest = some c0 := by
        rw [runFrom_cons] at hL0_run
        change runFrom n (n z b1) L_rest = some c0 at hL0_run
        cases hnb : n z b1 with
        | none =>
          rw [hnb] at hL0_run
          simp [runFrom_none] at hL0_run
        | some r1 =>
          rw [hnb] at hL0_run
          exact ⟨r1, rfl, hL0_run⟩
      obtain ⟨r1, hr1_step, hr1_c0⟩ := hr1_ex
      let Sub1 : Finset (Fin s) :=
        Finset.univ.filter (fun y => ∃ M : List Bool, runFrom n (some r1) M = some y)
      have hr1_Sub1 : r1 ∈ Sub1 := Finset.mem_filter.mpr ⟨Finset.mem_univ r1, ⟨[], rfl⟩⟩
      have hc0_Sub1 : c0 ∈ Sub1 := Finset.mem_filter.mpr ⟨Finset.mem_univ c0, ⟨L_rest, hr1_c0⟩⟩
      have hSub1_cl : ∀ x ∈ Sub1, ∀ bit y, n x bit = some y → y ∈ Sub1 := by
        intro x hx bit y hxy
        obtain ⟨M, hM⟩ := (Finset.mem_filter.mp hx).2
        refine Finset.mem_filter.mpr ⟨Finset.mem_univ y, ⟨M ++ [bit], ?_⟩⟩
        rw [runFrom_append, hM, runFrom_singleton, hxy]
      have hSub1_run_cl : ∀ x ∈ Sub1, ∀ M y, runFrom n (some x) M = some y → y ∈ Sub1 := by
        intro x hx M y hM
        obtain ⟨M0, hM0⟩ := (Finset.mem_filter.mp hx).2
        refine Finset.mem_filter.mpr ⟨Finset.mem_univ y, ⟨M0 ++ M, ?_⟩⟩
        rw [runFrom_append, hM0, hM]
      have hz_not_Sub1 : z ∉ Sub1 := by
        intro hzS
        obtain ⟨M, hM⟩ := (Finset.mem_filter.mp hzS).2
        cases M using List.reverseRecOn with
        | nil =>
          rw [runFrom_nil] at hM
          exact hno_in_z z b1 (hr1_step.trans hM)
        | append_singleton M' bit =>
          obtain ⟨x', _, hstep⟩ := runFrom_append_some n (some r1) M' [bit] z hM
          rw [runFrom_singleton] at hstep
          exact hno_in_z x' bit hstep
      have hC_sub_Sub1 : Cset ⊆ Sub1 := by
        intro c hc
        obtain ⟨M, hM⟩ := hC_conn c0 hc0C c hc
        exact hSub1_run_cl c0 hc0_Sub1 M c hM
      have hv_in : v_prev = z ∨ v_prev ∈ Sub1 := by
        cases L_init with
        | nil =>
          left
          rw [runFrom_nil] at hv_run
          exact (Option.some.inj hv_run).symm
        | cons b1' L_tail =>
          right
          have hb1' : b1' = b1 := by
            simp only [List.cons_append, List.cons.injEq] at hcons
            exact hcons.1
          rw [hb1'] at hv_run
          rw [runFrom_cons] at hv_run
          change runFrom n (n z b1) L_tail = some v_prev at hv_run
          rw [hr1_step] at hv_run
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ v_prev, ⟨L_tail, hv_run⟩⟩
      let b_sib : Bool := !b1
      have hbsib_ne : b_sib ≠ b1 := by cases b1 <;> decide
      let Sub_sib : Finset (Fin s) :=
        Finset.univ.filter (fun y => ∃ M : List Bool, runFrom n (n z b_sib) M = some y)
      have hSub_sib_cl : ∀ x ∈ Sub_sib, ∀ bit y, n x bit = some y → y ∈ Sub_sib := by
        intro x hx bit y hxy
        obtain ⟨M, hM⟩ := (Finset.mem_filter.mp hx).2
        refine Finset.mem_filter.mpr ⟨Finset.mem_univ y, ⟨M ++ [bit], ?_⟩⟩
        rw [runFrom_append, hM, runFrom_singleton, hxy]
      have hz_not_Sub_sib : z ∉ Sub_sib := by
        intro hzS
        obtain ⟨M, hM⟩ := (Finset.mem_filter.mp hzS).2
        cases M using List.reverseRecOn with
        | nil =>
          rw [runFrom_nil] at hM
          exact hno_in_z z b_sib hM
        | append_singleton M' bit =>
          obtain ⟨x', _, hstep⟩ := runFrom_append_some n (n z b_sib) M' [bit] z hM
          rw [runFrom_singleton] at hstep
          exact hno_in_z x' bit hstep
      have hdisj_sub : Disjoint Sub_sib Sub1 := by
        rw [Finset.disjoint_left]
        intro y_any hy_sib hy_1
        have hex_meet : ∃ len : ℕ, ∃ y ∈ Sub1, ∃ M : List Bool,
            M.length = len ∧ runFrom n (n z b_sib) M = some y := by
          obtain ⟨M, hM⟩ := (Finset.mem_filter.mp hy_sib).2
          exact ⟨M.length, y_any, hy_1, M, rfl, hM⟩
        let mlen := Nat.find hex_meet
        obtain ⟨y0, hy0_1, M0, hM0_len, hM0_run⟩ := Nat.find_spec hex_meet
        cases M0 using List.reverseRecOn with
        | nil =>
          rw [runFrom_nil] at hM0_run
          by_cases hy0_r1 : y0 = r1
          · rw [hy0_r1] at hM0_run
            have hne_pair : (z, b1) ≠ (z, b_sib) := fun h => hbsib_ne (congrArg Prod.snd h).symm
            have ⟨_, h1c, h2c⟩ := hindeg r1 z b1 z b_sib hr1_step hM0_run hne_pair
            have hne_ec1 : (z, b1) ≠ ec := fun h => hzNotC ((show z = xc from congrArg Prod.fst h).symm ▸ hxcC)
            have hne_ec2 : (z, b_sib) ≠ ec := fun h => hzNotC ((show z = xc from congrArg Prod.fst h).symm ▸ hxcC)
            have h1e := h1c.resolve_right hne_ec1
            have h2e := h2c.resolve_right hne_ec2
            exact hne_pair (h1e.trans h2e.symm)
          · obtain ⟨M1, hM1⟩ := (Finset.mem_filter.mp hy0_1).2
            cases M1 using List.reverseRecOn with
            | nil =>
              rw [runFrom_nil] at hM1
              exact hy0_r1 (Option.some.inj hM1).symm
            | append_singleton M1' bit1 =>
              obtain ⟨x1, hx1_run, hx1_step⟩ := runFrom_append_some n (some r1) M1' [bit1] y0 hM1
              rw [runFrom_singleton] at hx1_step
              have hx1_1 : x1 ∈ Sub1 := Finset.mem_filter.mpr ⟨Finset.mem_univ x1, ⟨M1', hx1_run⟩⟩
              have hne_pair : (z, b_sib) ≠ (x1, bit1) := fun h =>
                hz_not_Sub1 ((show z = x1 from congrArg Prod.fst h).symm ▸ hx1_1)
              have ⟨_, h1c, _⟩ := hindeg y0 z b_sib x1 bit1 hM0_run hx1_step hne_pair
              have hne_ec : (z, b_sib) ≠ ec := fun h => hzNotC ((show z = xc from congrArg Prod.fst h).symm ▸ hxcC)
              have heq_e0 : (z, b_sib) = e0 := h1c.resolve_right hne_ec
              have hvz : v_prev = z := (congrArg Prod.fst heq_e0).symm
              have hbb0 : b_sib = b0 := congrArg Prod.snd heq_e0
              have hLinit_nil : L_init = [] := by
                cases L_init using List.reverseRecOn with
                | nil => rfl
                | append_singleton Lp bp =>
                  obtain ⟨xp, _, hsp⟩ := runFrom_append_some n (some z) Lp [bp] v_prev hv_run
                  rw [runFrom_singleton, hvz] at hsp
                  exact absurd hsp (hno_in_z xp bp)
              rw [hLinit_nil] at hcons
              simp only [List.nil_append, List.cons.injEq] at hcons
              exact hbsib_ne (hbb0.trans hcons.1)
        | append_singleton M_init bit_sib =>
          obtain ⟨xs, hxs_run, hxs_step⟩ := runFrom_append_some n (n z b_sib) M_init [bit_sib] y0 hM0_run
          rw [runFrom_singleton] at hxs_step
          have hxs_not1 : xs ∉ Sub1 := by
            intro hxs1
            exact Nat.find_min hex_meet (show M_init.length < mlen by simp at hM0_len; omega)
              ⟨xs, hxs1, M_init, rfl, hxs_run⟩
          have hxs_sib : xs ∈ Sub_sib := Finset.mem_filter.mpr ⟨Finset.mem_univ xs, ⟨M_init, hxs_run⟩⟩
          have hxs_nez : xs ≠ z := fun h => hz_not_Sub_sib (h ▸ hxs_sib)
          have hxs_ne_e0 : (xs, bit_sib) ≠ e0 := by
            intro heq
            have h1 : xs = v_prev := congrArg Prod.fst heq
            rcases hv_in with hvz | hv1
            · exact hxs_nez (h1.trans hvz)
            · exact hxs_not1 (h1 ▸ hv1)
          have hxs_ne_ec : (xs, bit_sib) ≠ ec := by
            intro heq
            exact hxs_not1 ((show xs = xc from congrArg Prod.fst heq).symm ▸ hC_sub_Sub1 hxcC)
          by_cases hy0_r1 : y0 = r1
          · rw [hy0_r1] at hxs_step
            have hne_pair : (xs, bit_sib) ≠ (z, b1) := fun h => hxs_nez (congrArg Prod.fst h)
            have ⟨_, h1c, _⟩ := hindeg r1 xs bit_sib z b1 hxs_step hr1_step hne_pair
            exact h1c.elim hxs_ne_e0 hxs_ne_ec
          · obtain ⟨M1, hM1⟩ := (Finset.mem_filter.mp hy0_1).2
            cases M1 using List.reverseRecOn with
            | nil =>
              rw [runFrom_nil] at hM1
              exact hy0_r1 (Option.some.inj hM1).symm
            | append_singleton M1' bit1 =>
              obtain ⟨x1, hx1_run, hx1_step⟩ := runFrom_append_some n (some r1) M1' [bit1] y0 hM1
              rw [runFrom_singleton] at hx1_step
              have hx1_1 : x1 ∈ Sub1 := Finset.mem_filter.mpr ⟨Finset.mem_univ x1, ⟨M1', hx1_run⟩⟩
              have hne_pair : (xs, bit_sib) ≠ (x1, bit1) := fun h =>
                hxs_not1 ((show xs = x1 from congrArg Prod.fst h).symm ▸ hx1_1)
              have ⟨_, h1c, _⟩ := hindeg y0 xs bit_sib x1 bit1 hxs_step hx1_step hne_pair
              exact h1c.elim hxs_ne_e0 hxs_ne_ec
      cases hnsib : n z b_sib with
      | none =>
        let j_sib : Fin m := out z b_sib
        have hSub1_no : ∀ x ∈ Sub1, ∀ bit, n x bit = none → out x bit ≠ j_sib := by
          intro x hx bit hnb hout
          have heq := hexit_uniq j_sib (x, bit) (z, b_sib) hnb hout hnsib rfl
          exact hz_not_Sub1 ((show x = z from congrArg Prod.fst heq) ▸ hx)
        have hPr1_0 : P r1 j_sib = 0 := hzero_on_closed Sub1 j_sib hSub1_cl hSub1_no r1 hr1_Sub1
        have hz_eq := hP_solves j_sib z
        dsimp only [Ends] at hz_eq
        have h2Pz : 2 * P z j_sib = 1 := by
          cases hb1 : b1 with
          | false =>
            have hbs : b_sib = true := by simp [b_sib, hb1]
            rw [hb1] at hr1_step; rw [hbs] at hnsib
            simp only [hr1_step, hnsib, Option.elim_some, Option.elim_none, hPr1_0] at hz_eq
            have hout_eq : out z true = j_sib := by simp [j_sib, hbs]
            rw [if_pos hout_eq] at hz_eq
            linarith
          | true =>
            have hbs : b_sib = false := by simp [b_sib, hb1]
            rw [hb1] at hr1_step; rw [hbs] at hnsib
            simp only [hr1_step, hnsib, Option.elim_some, Option.elim_none, hPr1_0] at hz_eq
            have hout_eq : out z false = j_sib := by simp [j_sib, hbs]
            rw [if_pos hout_eq] at hz_eq
            linarith
        have hdyad : Dyad (P z j_sib) := ⟨1, 1, by simp [h2Pz]⟩
        exact hP_z_nondyad j_sib hdyad
      | some r_sib =>
        have hrsib_mem : r_sib ∈ Sub_sib :=
          Finset.mem_filter.mpr ⟨Finset.mem_univ r_sib, ⟨[], by simp [runFrom_nil, hnsib]⟩⟩
        obtain ⟨pick, hpick⟩ := hn
        let F := fun o : Option (Fin s) => o.bind (fun h => n h (pick h))
        have hex_t : ∃ t : ℕ, F^[t] (some r_sib) = none := ⟨s, hpick r_sib⟩
        let t_hit := Nat.find hex_t
        have ht_spec : F^[t_hit] (some r_sib) = none := Nat.find_spec hex_t
        have ht_pos : 0 < t_hit := by
          by_contra h0
          have ht0 : t_hit = 0 := by omega
          rw [ht0] at ht_spec
          cases ht_spec
        have hF_in_sib : ∀ k < t_hit, ∃ x ∈ Sub_sib, F^[k] (some r_sib) = some x := by
          intro k hk
          induction k with
          | zero => exact ⟨r_sib, hrsib_mem, rfl⟩
          | succ k ih =>
            obtain ⟨x, hx_sib, hx_eq⟩ := ih (by omega)
            have hne_none : F^[k + 1] (some r_sib) ≠ none := Nat.find_min hex_t hk
            rw [Function.iterate_succ_apply', hx_eq] at hne_none ⊢
            change n x (pick x) ≠ none at hne_none
            cases hnx : n x (pick x) with
            | none => exact absurd hnx hne_none
            | some y => exact ⟨y, hSub_sib_cl x hx_sib (pick x) y hnx, hnx⟩
        obtain ⟨e_st, hest_sib, hest_eq⟩ := hF_in_sib (t_hit - 1) (by omega)
        have hest_none : n e_st (pick e_st) = none := by
          have h1 : F^[t_hit - 1 + 1] (some r_sib) = none := by
            rw [show t_hit - 1 + 1 = t_hit by omega]; exact ht_spec
          rw [Function.iterate_succ_apply', hest_eq] at h1
          exact h1
        let j_sib : Fin m := out e_st (pick e_st)
        have hSub1_no : ∀ x ∈ Sub1, ∀ bit, n x bit = none → out x bit ≠ j_sib := by
          intro x hx bit hnb hout
          have heq := hexit_uniq j_sib (x, bit) (e_st, pick e_st) hnb hout hest_none rfl
          have hxeq : x = e_st := congrArg Prod.fst heq
          exact Finset.disjoint_left.mp hdisj_sub hest_sib (hxeq ▸ hx)
        have hPr1_0 : P r1 j_sib = 0 := hzero_on_closed Sub1 j_sib hSub1_cl hSub1_no r1 hr1_Sub1
        have hrsib_dyad : Dyad (P r_sib j_sib) := by
          by_contra hnd_sib
          let Bad_sib : Finset (Fin s) := Sub_sib.filter (fun x => ¬ Dyad (P x j_sib))
          have hrsib_Bad : r_sib ∈ Bad_sib := Finset.mem_filter.mpr ⟨hrsib_mem, hnd_sib⟩
          have hBad_sib_step : ∀ x ∈ Bad_sib, ∃ bit k, n x bit = some k ∧ k ∈ Bad_sib := by
            intro x hx
            have hxS : x ∈ Sub_sib := (Finset.mem_filter.mp hx).1
            have hxND : ¬ Dyad (P x j_sib) := (Finset.mem_filter.mp hx).2
            by_contra hno
            push Not at hno
            apply hxND
            have hbr : ∀ bit : Bool,
                Dyad ((n x bit).elim (if out x bit = j_sib then (1 : ℝ) else 0) (fun k => P k j_sib)) := by
              intro bit
              cases hnb : n x bit with
              | none =>
                simp only [Option.elim_none]
                split_ifs
                · exact dyadNat 1
                · exact dyadNat 0
              | some k =>
                simp only [Option.elim_some]
                have hkS : k ∈ Sub_sib := hSub_sib_cl x hxS bit k hnb
                have hkNB : k ∉ Bad_sib := hno bit k hnb
                by_contra hnk
                exact hkNB (Finset.mem_filter.mpr ⟨hkS, hnk⟩)
            exact dyadMid (hP_solves j_sib x) (hbr false) (hbr true)
          obtain ⟨C_sib, hCs_ne, hCs_sub_Bad, hCs_in, _⟩ :=
            exists_cycle_of_closed n Bad_sib ⟨r_sib, hrsib_Bad⟩ hBad_sib_step
          have hCs_sub_sib : C_sib ⊆ Sub_sib := fun x hx => (Finset.mem_filter.mp (hCs_sub_Bad hx)).1
          have hex_ps : ∃ len : ℕ, ∃ c ∈ C_sib, ∃ M : List Bool,
              M.length = len ∧ runFrom n (some r_sib) M = some c := by
            obtain ⟨c, hc⟩ := hCs_ne
            obtain ⟨M, hM⟩ := (Finset.mem_filter.mp (hCs_sub_sib hc)).2
            rw [hnsib] at hM
            exact ⟨M.length, c, hc, M, rfl, hM⟩
          let mls := Nat.find hex_ps
          obtain ⟨cs, hcs_C, Ms, hMs_len, hMs_run⟩ := Nat.find_spec hex_ps
          obtain ⟨xcs, hxcs_C, bcs, hxcs_step⟩ := hCs_in cs hcs_C
          have hcs_not_c0 : cs ≠ c0 := fun h =>
            Finset.disjoint_left.mp hdisj_sub (hCs_sub_sib hcs_C) (h ▸ hc0_Sub1)
          cases Ms using List.reverseRecOn with
          | nil =>
            rw [runFrom_nil] at hMs_run
            have hcs_eq : r_sib = cs := Option.some.inj hMs_run
            have hne_pair : (z, b_sib) ≠ (xcs, bcs) := fun h =>
              hz_not_Sub_sib ((show z = xcs from congrArg Prod.fst h).symm ▸ hCs_sub_sib hxcs_C)
            have ⟨hc_eq, _, _⟩ := hindeg cs z b_sib xcs bcs (hcs_eq ▸ hnsib) hxcs_step hne_pair
            exact hcs_not_c0 hc_eq
          | append_singleton Ms' bs =>
            obtain ⟨vs, hvs_run, hvs_step⟩ := runFrom_append_some n (some r_sib) Ms' [bs] cs hMs_run
            rw [runFrom_singleton] at hvs_step
            have hvs_notC : vs ∉ C_sib := fun hvsC =>
              Nat.find_min hex_ps (show Ms'.length < mls by simp at hMs_len; omega)
                ⟨vs, hvsC, Ms', rfl, hvs_run⟩
            have hne_pair : (vs, bs) ≠ (xcs, bcs) := fun h =>
              hvs_notC ((show vs = xcs from congrArg Prod.fst h).symm ▸ hxcs_C)
            have ⟨hc_eq, _, _⟩ := hindeg cs vs bs xcs bcs hvs_step hxcs_step hne_pair
            exact hcs_not_c0 hc_eq
        have hz_eq := hP_solves j_sib z
        dsimp only [Ends] at hz_eq
        have h2Pz : 2 * P z j_sib = P r_sib j_sib + 0 := by
          cases hb1 : b1 with
          | false =>
            have hbs : b_sib = true := by simp [b_sib, hb1]
            rw [hb1] at hr1_step; rw [hbs] at hnsib
            simp only [hr1_step, hnsib, Option.elim_some, hPr1_0] at hz_eq
            linarith
          | true =>
            have hbs : b_sib = false := by simp [b_sib, hb1]
            rw [hb1] at hr1_step; rw [hbs] at hnsib
            simp only [hr1_step, hnsib, Option.elim_some, hPr1_0] at hz_eq
            linarith
        exact hP_z_nondyad j_sib (dyadMid h2Pz hrsib_dyad (dyadNat 0))
  obtain ⟨x_ret, hx_ret_C, b_ret, hret_step⟩ := hC_in z hzC
  let e_ret : Fin s × Bool := (x_ret, b_ret)
  have heret_int : e_ret ∈ Internal := hint_mem x_ret b_ret z hret_step
  have hsub_ret : (Finset.univ.erase z).image some ⊆ (Internal.erase e_ret).image tgt := by
    intro o ho
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp ho
    have hyz : y ≠ z := Finset.ne_of_mem_erase hy
    obtain ⟨e, he, hte⟩ := hin_R y (hR_univ ▸ Finset.mem_univ y) hyz
    have hne_ret : e ≠ e_ret := by
      intro heq
      rw [heq] at hte
      exact hyz (Option.some.inj (hte.symm.trans hret_step))
    exact Finset.mem_image.mpr ⟨e, Finset.mem_erase.mpr ⟨hne_ret, he⟩, hte⟩
  have hcard_lhs_r : ((Finset.univ.erase z).image some).card = m - 1 := by
    rw [Finset.card_image_of_injective _ (Option.some_injective (Fin s)),
      Finset.card_erase_of_mem (Finset.mem_univ z), Finset.card_univ, Fintype.card_fin]
    omega
  have hcard_rhs_r : (Internal.erase e_ret).card = m - 1 := by
    rw [Finset.card_erase_of_mem heret_int, hInt_card]
  have himg_ret : (Internal.erase e_ret).image tgt = (Finset.univ.erase z).image some :=
    (Finset.eq_of_subset_of_card_le hsub_ret (by rw [hcard_lhs_r, ← hcard_rhs_r]; exact Finset.card_image_le)).symm
  have htgt_ret_inj : Set.InjOn tgt (Internal.erase e_ret) := by
    apply Finset.injOn_of_card_image_eq
    rw [himg_ret, hcard_lhs_r, hcard_rhs_r]
  have hret_uniq : ∀ x bit, n x bit = some z ↔ (x, bit) = e_ret := by
    intro x bit
    constructor
    · intro hxz
      by_contra hne
      have hmem : some z ∈ (Internal.erase e_ret).image tgt :=
        Finset.mem_image.mpr ⟨(x, bit), Finset.mem_erase.mpr ⟨hne, hint_mem x bit z hxz⟩, hxz⟩
      rw [himg_ret] at hmem
      obtain ⟨y, hy, hyz⟩ := Finset.mem_image.mp hmem
      exact Finset.ne_of_mem_erase hy (Option.some.inj hyz)
    · intro heq
      rw [show x = x_ret from congrArg Prod.fst heq, show bit = b_ret from congrArg Prod.snd heq]
      exact hret_step
  have hin_uniq : ∀ y, y ≠ z → ∀ x1 b1 x2 b2,
      n x1 b1 = some y → n x2 b2 = some y → (x1, b1) = (x2, b2) := by
    intro y hyz x1 b1 x2 b2 h1 h2
    have hne1 : (x1, b1) ≠ e_ret := by
      intro heq
      rw [show x1 = x_ret from congrArg Prod.fst heq, show b1 = b_ret from congrArg Prod.snd heq] at h1
      exact hyz (Option.some.inj (h1.symm.trans hret_step))
    have hne2 : (x2, b2) ≠ e_ret := by
      intro heq
      rw [show x2 = x_ret from congrArg Prod.fst heq, show b2 = b_ret from congrArg Prod.snd heq] at h2
      exact hyz (Option.some.inj (h2.symm.trans hret_step))
    exact htgt_ret_inj (Finset.mem_erase.mpr ⟨hne1, hint_mem x1 b1 y h1⟩)
      (Finset.mem_erase.mpr ⟨hne2, hint_mem x2 b2 y h2⟩) (h1.trans h2.symm)
  let n_tree : Fin s → Bool → Option (Fin s) := fun i bit =>
    if (i, bit) = e_ret then none else n i bit
  have hnt_no_z : ∀ i bit, n_tree i bit ≠ some z := by
    intro i bit h
    dsimp only [n_tree] at h
    by_cases heq : (i, bit) = e_ret
    · rw [if_pos heq] at h; cases h
    · rw [if_neg heq] at h; exact heq ((hret_uniq i bit).mp h)
  have hnt_to_n : ∀ i bit y, n_tree i bit = some y → n i bit = some y := by
    intro i bit y h
    dsimp only [n_tree] at h
    by_cases heq : (i, bit) = e_ret
    · rw [if_pos heq] at h; cases h
    · rw [if_neg heq] at h; exact h
  have hnt_run_to_n : ∀ L y, runFrom n_tree (some z) L = some y → runFrom n (some z) L = some y := by
    intro L
    induction L using List.reverseRecOn with
    | nil => intro y h; exact h
    | append_singleton L' bit ih =>
      intro y h
      obtain ⟨w, hw, hstep⟩ := runFrom_append_some n_tree (some z) L' [bit] y h
      rw [runFrom_singleton] at hstep
      rw [runFrom_append, ih w hw, runFrom_singleton]
      exact hnt_to_n w bit y hstep
  have hnt_path_uniq : ∀ L1 L2 y,
      runFrom n_tree (some z) L1 = some y → runFrom n_tree (some z) L2 = some y → L1 = L2 := by
    intro L1
    induction L1 using List.reverseRecOn with
    | nil =>
      intro L2 y h1 h2
      rw [runFrom_nil] at h1
      have hyz : y = z := (Option.some.inj h1).symm
      rw [hyz] at h2
      cases L2 using List.reverseRecOn with
      | nil => rfl
      | append_singleton L2' b2 =>
        obtain ⟨w2, _, hstep2⟩ := runFrom_append_some n_tree (some z) L2' [b2] z h2
        rw [runFrom_singleton] at hstep2
        exact absurd hstep2 (hnt_no_z w2 b2)
    | append_singleton L1' b1 ih =>
      intro L2 y h1 h2
      obtain ⟨w1, hw1, hstep1⟩ := runFrom_append_some n_tree (some z) L1' [b1] y h1
      rw [runFrom_singleton] at hstep1
      have hyz : y ≠ z := fun heq => hnt_no_z w1 b1 (heq ▸ hstep1)
      cases L2 using List.reverseRecOn with
      | nil =>
        rw [runFrom_nil] at h2
        exact absurd (Option.some.inj h2).symm hyz
      | append_singleton L2' b2 =>
        obtain ⟨w2, hw2, hstep2⟩ := runFrom_append_some n_tree (some z) L2' [b2] y h2
        rw [runFrom_singleton] at hstep2
        have hpair : (w1, b1) = (w2, b2) :=
          hin_uniq y hyz w1 b1 w2 b2 (hnt_to_n w1 b1 y hstep1) (hnt_to_n w2 b2 y hstep2)
        have hw_eq : w1 = w2 := congrArg Prod.fst hpair
        have hb_eq : b1 = b2 := congrArg Prod.snd hpair
        rw [ih L2' w1 hw1 (hw_eq ▸ hw2), hb_eq]
  have hnt_len_lt : ∀ L y, runFrom n_tree (some z) L = some y → L.length < m := by
    intro L y hL
    by_contra hge
    have hsm_le : s ≤ L.length := by omega
    have htake_some : ∀ k : Fin (s + 1), ∃ v, runFrom n_tree (some z) (L.take k.val) = some v := by
      intro k
      have hsplit : L.take k.val ++ L.drop k.val = L := List.take_append_drop k.val L
      rw [← hsplit] at hL
      obtain ⟨v, hv, _⟩ := runFrom_append_some n_tree (some z) (L.take k.val) (L.drop k.val) y hL
      exact ⟨v, hv⟩
    let vOf : Fin (s + 1) → Fin s := fun k => Classical.choose (htake_some k)
    have hvOf : ∀ k : Fin (s + 1), runFrom n_tree (some z) (L.take k.val) = some (vOf k) :=
      fun k => Classical.choose_spec (htake_some k)
    have hnot_inj : ¬ Function.Injective vOf := by
      intro hinj
      have := Fintype.card_le_of_injective vOf hinj
      simp at this
    rw [Function.Injective] at hnot_inj
    push Not at hnot_inj
    obtain ⟨k1, k2, hveq, hkne⟩ := hnot_inj
    have htake_eq : L.take k1.val = L.take k2.val :=
      hnt_path_uniq _ _ (vOf k1) (hvOf k1) (hveq ▸ hvOf k2)
    have hlen_eq := congrArg List.length htake_eq
    simp only [List.length_take] at hlen_eq
    have h1 : min k1.val L.length = k1.val := min_eq_left (by omega)
    have h2 : min k2.val L.length = k2.val := min_eq_left (by omega)
    rw [h1, h2] at hlen_eq
    exact hkne (Fin.ext hlen_eq)
  have hnt_none_ge : ∀ L : List Bool, m ≤ L.length → runFrom n_tree (some z) L = none := by
    intro L hL
    cases hrun : runFrom n_tree (some z) L with
    | none => rfl
    | some y => exact absurd (hnt_len_lt L y hrun) (by omega)
  have hnt_reach : ∀ y : Fin s, ∃ L : List Bool, runFrom n_tree (some z) L = some y := by
    intro y
    have hex_y : ∃ len : ℕ, ∃ L : List Bool, L.length = len ∧ runFrom n (some z) L = some y := by
      have hyR : y ∈ Rset := hR_univ ▸ Finset.mem_univ y
      obtain ⟨L, hL⟩ := (Finset.mem_filter.mp hyR).2
      exact ⟨L.length, L, rfl, hL⟩
    let minY := Nat.find hex_y
    obtain ⟨L, hL_len, hL_run⟩ := Nat.find_spec hex_y
    refine ⟨L, ?_⟩
    have hagree : ∀ k ≤ L.length, runFrom n_tree (some z) (L.take k) = runFrom n (some z) (L.take k) := by
      intro k hk
      induction k with
      | zero => rfl
      | succ k ih =>
        have hk' : k < L.length := by omega
        have htake_succ : L.take (k + 1) = L.take k ++ [L[k]'hk'] := by
          apply List.ext_getElem
          · simp [Nat.min_eq_left hk, Nat.min_eq_left (by omega : k ≤ L.length)]
          · intro r hr1 hr2
            simp only [List.getElem_take, List.getElem_append, List.length_take,
              Nat.min_eq_left (by omega : k ≤ L.length), List.getElem_singleton]
            split_ifs with hrk
            · rfl
            · have : r = k := by
                simp only [List.length_take, Nat.min_eq_left hk] at hr1
                omega
              subst this; rfl
        rw [htake_succ, runFrom_append, runFrom_append, ih (by omega)]
        have hsplit : L.take k ++ L.drop k = L := List.take_append_drop k L
        have hL' := hL_run
        rw [← hsplit] at hL'
        obtain ⟨w, hw, _⟩ := runFrom_append_some n (some z) (L.take k) (L.drop k) y hL'
        rw [hw, runFrom_singleton, runFrom_singleton]
        dsimp only [n_tree]
        rw [if_neg]
        intro heq
        have hstep_z : n w (L[k]'hk') = some z := (hret_uniq w (L[k]'hk')).mpr heq
        have htake_z : runFrom n (some z) (L.take (k + 1)) = some z := by
          rw [htake_succ, runFrom_append, hw, runFrom_singleton, hstep_z]
        have hdrop_y : runFrom n (some z) (L.drop (k + 1)) = some y := by
          have hsp := List.take_append_drop (k + 1) L
          have hL2 := hL_run
          rw [← hsp, runFrom_append, htake_z] at hL2
          exact hL2
        exact Nat.find_min hex_y (show (L.drop (k + 1)).length < minY by simp; omega)
          ⟨L.drop (k + 1), rfl, hdrop_y⟩
    have hfull := hagree L.length le_rfl
    rw [List.take_length] at hfull
    exact hfull.trans hL_run
  let pathTo : Fin s → List Bool := fun y => Classical.choose (hnt_reach y)
  have hpathTo_run : ∀ y, runFrom n_tree (some z) (pathTo y) = some y :=
    fun y => Classical.choose_spec (hnt_reach y)
  have hpathTo_eq : ∀ L y, runFrom n_tree (some z) L = some y ↔ L = pathTo y := by
    intro L y
    constructor
    · intro h; exact hnt_path_uniq L (pathTo y) y h (hpathTo_run y)
    · intro h; rw [h]; exact hpathTo_run y
  let exitOf : Fin m → Fin s × Bool := fun j => Classical.choose (hexits_surj j)
  have hexitOf_spec : ∀ j, n (exitOf j).1 (exitOf j).2 = none ∧ out (exitOf j).1 (exitOf j).2 = j := by
    intro j
    have hs := Classical.choose_spec (hexits_surj j)
    exact ⟨(Finset.mem_filter.mp hs.1).2, hs.2⟩
  have hexitOf_iff : ∀ j i bit, (n i bit = none ∧ out i bit = j) ↔ (i, bit) = exitOf j := by
    intro j i bit
    constructor
    · rintro ⟨hnb, hout⟩
      exact hexit_uniq j (i, bit) (exitOf j) hnb hout (hexitOf_spec j).1 (hexitOf_spec j).2
    · intro heq
      rw [show i = (exitOf j).1 from congrArg Prod.fst heq,
        show bit = (exitOf j).2 from congrArg Prod.snd heq]
      exact hexitOf_spec j
  let W_cyc : List Bool := pathTo e_ret.1 ++ [e_ret.2]
  let p : ℕ := W_cyc.length
  let W_out : Fin m → List Bool := fun j => pathTo (exitOf j).1 ++ [(exitOf j).2]
  let d : Fin m → ℕ := fun j => (W_out j).length
  have hp_pos : 1 ≤ p := by dsimp only [p, W_cyc]; simp
  have hp_le : p ≤ m := by
    have hlt := hnt_len_lt (pathTo e_ret.1) e_ret.1 (hpathTo_run e_ret.1)
    dsimp only [p, W_cyc]; simp; omega
  have hd_pos : ∀ j, 1 ≤ d j := fun j => by dsimp only [d, W_out]; simp
  have hd_le : ∀ j, d j ≤ m := fun j => by
    have hlt := hnt_len_lt (pathTo (exitOf j).1) (exitOf j).1 (hpathTo_run (exitOf j).1)
    dsimp only [d, W_out]; simp; omega
  have hW_cyc_run : runFrom n (some z) W_cyc = some z := by
    dsimp only [W_cyc]
    rw [runFrom_append, hnt_run_to_n _ _ (hpathTo_run e_ret.1), runFrom_singleton]
    exact hret_step
  have hW_cyc_iff : ∀ L_init bit,
      (∃ i, runFrom n_tree (some z) L_init = some i ∧ (i, bit) = e_ret) ↔ L_init ++ [bit] = W_cyc := by
    intro L_init bit
    constructor
    · rintro ⟨i, hrun, heq⟩
      have hi : i = e_ret.1 := congrArg Prod.fst heq
      have hb : bit = e_ret.2 := congrArg Prod.snd heq
      rw [hi] at hrun
      rw [(hpathTo_eq L_init e_ret.1).mp hrun, hb]
    · intro h
      have ⟨hL, hb⟩ := append_singleton_inj h
      rw [hL, hb]
      exact ⟨e_ret.1, hpathTo_run e_ret.1, rfl⟩
  have hW_out_iff : ∀ j L_init bit,
      (∃ i, runFrom n_tree (some z) L_init = some i ∧ n i bit = none ∧ out i bit = j) ↔
      L_init ++ [bit] = W_out j := by
    intro j L_init bit
    constructor
    · rintro ⟨i, hrun, hnb, hout⟩
      have heq := (hexitOf_iff j i bit).mp ⟨hnb, hout⟩
      have hi : i = (exitOf j).1 := congrArg Prod.fst heq
      have hb : bit = (exitOf j).2 := congrArg Prod.snd heq
      rw [hi] at hrun
      rw [(hpathTo_eq L_init (exitOf j).1).mp hrun, hb]
    · intro h
      have ⟨hL, hb⟩ := append_singleton_inj h
      rw [hL, hb]
      exact ⟨(exitOf j).1, hpathTo_run (exitOf j).1, hexitOf_spec j⟩
  have hW_out_iff' : ∀ j L_init bit,
      (∃ i, runFrom n_tree (some z) L_init = some i ∧ (i, bit) = exitOf j) ↔
      L_init ++ [bit] = W_out j := by
    intro j L_init bit
    have heqv : (∃ i, runFrom n_tree (some z) L_init = some i ∧ (i, bit) = exitOf j) ↔
        (∃ i, runFrom n_tree (some z) L_init = some i ∧ n i bit = none ∧ out i bit = j) := by
      constructor
      · rintro ⟨i, hr, h⟩; exact ⟨i, hr, (hexitOf_iff j i bit).mpr h⟩
      · rintro ⟨i, hr, h⟩; exact ⟨i, hr, (hexitOf_iff j i bit).mp h⟩
    rw [heqv]
    exact hW_out_iff j L_init bit
  have hterm_char : ∀ (j : Fin m) (L : List Bool),
      (∃ L_init i bit, L = L_init ++ [bit] ∧ runFrom n (some z) L_init = some i ∧
        n i bit = none ∧ out i bit = j) ↔
      ∃ q : ℕ, L = List.flatten (List.replicate q W_cyc) ++ W_out j := by
    intro j L
    constructor
    · intro h
      induction hlen : L.length using Nat.strong_induction_on generalizing L with
      | ind len ih =>
        obtain ⟨L_init, i, bit, rfl, hrun, hnb, hout⟩ := h
        by_cases hsame : runFrom n_tree (some z) L_init = some i
        · refine ⟨0, ?_⟩
          simp only [List.replicate_zero, List.flatten_nil, List.nil_append]
          exact (hW_out_iff j L_init bit).mp ⟨i, hsame, hnb, hout⟩
        · have hex_diff : ∃ k : ℕ, k ≤ L_init.length ∧
              runFrom n_tree (some z) (L_init.take k) ≠ runFrom n (some z) (L_init.take k) :=
            ⟨L_init.length, le_rfl, by simpa [List.take_length, hrun] using hsame⟩
          let k := Nat.find hex_diff
          have ⟨hk_le, hk_diff⟩ := Nat.find_spec hex_diff
          have hk_pos : 0 < k := by
            by_contra h0
            have hk0 : k = 0 := by omega
            change runFrom n_tree (some z) (L_init.take k) ≠ runFrom n (some z) (L_init.take k) at hk_diff
            rw [hk0] at hk_diff
            exact hk_diff rfl
          have hk_prev : runFrom n_tree (some z) (L_init.take (k - 1)) =
              runFrom n (some z) (L_init.take (k - 1)) := by
            by_contra hne
            exact Nat.find_min hex_diff (show k - 1 < k by omega) ⟨by omega, hne⟩
          have hk_lt : k - 1 < L_init.length := by omega
          have htake_succ : L_init.take k = L_init.take (k - 1) ++ [L_init[k - 1]'hk_lt] := by
            apply List.ext_getElem
            · simp [Nat.min_eq_left hk_le, Nat.min_eq_left (by omega : k - 1 ≤ L_init.length)]; omega
            · intro r hr1 hr2
              simp only [List.getElem_take, List.getElem_append, List.length_take,
                Nat.min_eq_left (by omega : k - 1 ≤ L_init.length), List.getElem_singleton]
              split_ifs with hrk
              · rfl
              · have : r = k - 1 := by
                  simp only [List.length_take, Nat.min_eq_left hk_le] at hr1
                  omega
                subst this; rfl
          have hsplit1 := List.take_append_drop (k - 1) L_init
          have hrun1 := hrun
          rw [← hsplit1] at hrun1
          obtain ⟨w, hw, _⟩ := runFrom_append_some n (some z) (L_init.take (k - 1)) (L_init.drop (k - 1)) i hrun1
          have hw_nt : runFrom n_tree (some z) (L_init.take (k - 1)) = some w := hk_prev.trans hw
          have hpair_ret : (w, L_init[k - 1]'hk_lt) = e_ret := by
            by_contra hne
            apply hk_diff
            rw [htake_succ, runFrom_append, runFrom_append, hw_nt, hw, runFrom_singleton, runFrom_singleton]
            dsimp only [n_tree]
            rw [if_neg hne]
          have htake_W : L_init.take k = W_cyc := by
            rw [htake_succ]
            exact (hW_cyc_iff (L_init.take (k - 1)) (L_init[k - 1]'hk_lt)).mp ⟨w, hw_nt, hpair_ret⟩
          have hL_split : L_init = W_cyc ++ L_init.drop k := by
            rw [← htake_W, List.take_append_drop]
          have hdrop_run : runFrom n (some z) (L_init.drop k) = some i := by
            have h1 := hrun
            rw [hL_split, runFrom_append, hW_cyc_run] at h1
            exact h1
          let L' : List Bool := L_init.drop k ++ [bit]
          have hL'_len : L'.length < len := by
            have h1 : L_init.length = W_cyc.length + (L_init.drop k).length := by
              have := congrArg List.length hL_split
              simpa using this
            have hp1 : 1 ≤ W_cyc.length := hp_pos
            dsimp only [L']
            simp at hlen ⊢
            omega
          obtain ⟨q', hq'⟩ := ih L'.length hL'_len L' ⟨L_init.drop k, i, bit, rfl, hdrop_run, hnb, hout⟩ rfl
          refine ⟨q' + 1, ?_⟩
          rw [List.replicate_succ, List.flatten_cons, List.append_assoc, ← hq']
          dsimp only [L']
          rw [← List.append_assoc, ← hL_split]
    · rintro ⟨q, rfl⟩
      refine ⟨List.flatten (List.replicate q W_cyc) ++ pathTo (exitOf j).1, (exitOf j).1, (exitOf j).2, ?_, ?_, ?_⟩
      · dsimp only [W_out]; rw [List.append_assoc]
      · rw [runFrom_append, runFrom_repeat n z W_cyc hW_cyc_run q,
          hnt_run_to_n _ _ (hpathTo_run (exitOf j).1)]
      · exact hexitOf_spec j
  have hrel_j : ∀ j : Fin m, A j * (2 ^ p - 1) * 2 ^ (d j) = D * 2 ^ p := by
    intro j
    let lv : Fin s → Bool → ℝ := fun i bit =>
      if (i, bit) = e_ret then P z j
      else if (i, bit) = exitOf j then 1 else 0
    have hval : ∀ i : Fin s, 2 * P i j = ∑ bit : Bool, (n_tree i bit).elim (lv i bit) (fun k => P k j) := by
      intro i
      rw [hP_eq i j]
      apply Finset.sum_congr rfl
      intro bit _
      dsimp only [n_tree, lv]
      by_cases hret : (i, bit) = e_ret
      · rw [if_pos hret, if_pos hret]
        have hstep : n i bit = some z := (hret_uniq i bit).mpr hret
        rw [hstep]
        rfl
      · rw [if_neg hret, if_neg hret]
        cases hnb : n i bit with
        | none =>
          simp only [Option.elim_none]
          by_cases hout : out i bit = j
          · rw [if_pos hout, if_pos ((hexitOf_iff j i bit).mp ⟨hnb, hout⟩)]
          · rw [if_neg hout, if_neg]
            intro heq
            exact hout ((hexitOf_iff j i bit).mpr heq).2
        | some k => simp
    have hunroll := unroll_tree n_tree (fun i => P i j) lv hval (m + 1) (some z)
    simp only [Option.elim_some] at hunroll
    have hrem : (∑ w : Fin (m + 1) → Bool, (runFrom n_tree (some z) (List.ofFn w)).elim 0 (fun i => P i j)) = 0 := by
      apply Finset.sum_eq_zero
      intro w _
      rw [hnt_none_ge (List.ofFn w) (by simp)]
      rfl
    rw [hrem, add_zero] at hunroll
    have hne_ret_exit : e_ret ≠ exitOf j := by
      intro heq
      have h1 : n e_ret.1 e_ret.2 = some z := hret_step
      rw [heq] at h1
      rw [(hexitOf_spec j).1] at h1
      cases h1
    have hsplit_lv : ∀ i bit, n_tree i bit = none →
        lv i bit = (if (i, bit) = e_ret then P z j else 0) + (if (i, bit) = exitOf j then 1 else 0) := by
      intro i bit _
      dsimp only [lv]
      by_cases h1 : (i, bit) = e_ret
      · rw [if_pos h1, if_pos h1, if_neg (h1 ▸ hne_ret_exit), add_zero]
      · rw [if_neg h1, if_neg h1, zero_add]
    have hsum_split :
        (∑ t : Fin (m + 1), (2 : ℝ) ^ (m + 1 - 1 - t.val) *
          ∑ w : Fin t.val → Bool, (runFrom n_tree (some z) (List.ofFn w)).elim 0
            (fun i => ∑ bit : Bool, if n_tree i bit = none then lv i bit else 0)) =
        (∑ t : Fin (m + 1), (2 : ℝ) ^ (m + 1 - 1 - t.val) *
          ∑ w : Fin t.val → Bool, (runFrom n_tree (some z) (List.ofFn w)).elim 0
            (fun i => ∑ bit : Bool, if (i, bit) = e_ret then P z j else 0)) +
        (∑ t : Fin (m + 1), (2 : ℝ) ^ (m + 1 - 1 - t.val) *
          ∑ w : Fin t.val → Bool, (runFrom n_tree (some z) (List.ofFn w)).elim 0
            (fun i => ∑ bit : Bool, if (i, bit) = exitOf j then (1 : ℝ) else 0)) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro t _
      rw [← mul_add, ← Finset.sum_add_distrib]
      congr 1
      apply Finset.sum_congr rfl
      intro w _
      cases runFrom n_tree (some z) (List.ofFn w) with
      | none => simp
      | some i =>
        simp only [Option.elim_some, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro bit _
        by_cases hnt : n_tree i bit = none
        · rw [if_pos hnt, hsplit_lv i bit hnt]
        · rw [if_neg hnt]
          have h1 : (i, bit) ≠ e_ret := by
            intro heq
            apply hnt
            dsimp only [n_tree]
            rw [if_pos heq]
          have h2 : (i, bit) ≠ exitOf j := by
            intro heq
            apply hnt
            dsimp only [n_tree]
            rw [if_neg h1, show i = (exitOf j).1 from congrArg Prod.fst heq,
              show bit = (exitOf j).2 from congrArg Prod.snd heq]
            exact (hexitOf_spec j).1
          rw [if_neg h1, if_neg h2, add_zero]
    rw [hsum_split] at hunroll
    have hterm1 := unroll_leaf_sum n_tree z (m + 1) (fun i bit => (i, bit) = e_ret)
      W_cyc hp_pos (show W_cyc.length ≤ m + 1 by change p ≤ m + 1; omega) hW_cyc_iff (P z j)
    have hterm2 := unroll_leaf_sum n_tree z (m + 1) (fun i bit => (i, bit) = exitOf j)
      (W_out j) (hd_pos j) (show (W_out j).length ≤ m + 1 by change d j ≤ m + 1; have := hd_le j; omega)
      (hW_out_iff' j) (1 : ℝ)
    rw [hterm1, hterm2, mul_one] at hunroll
    have hpow_p : (2 : ℝ) ^ (m + 1 - p) * (2 : ℝ) ^ p = (2 : ℝ) ^ (m + 1) := by
      rw [← pow_add, Nat.sub_add_cancel (by omega)]
    have hpow_d : (2 : ℝ) ^ (m + 1 - d j) * (2 : ℝ) ^ (d j) = (2 : ℝ) ^ (m + 1) := by
      rw [← pow_add, Nat.sub_add_cancel (by have := hd_le j; omega)]
    have hscaled :
        (2 : ℝ) ^ (m + 1) * ((D : ℝ) * P z j * (2 : ℝ) ^ p * (2 : ℝ) ^ (d j)) =
        (2 : ℝ) ^ (m + 1) * ((D : ℝ) * P z j * (2 : ℝ) ^ (d j) + (D : ℝ) * (2 : ℝ) ^ p) := by
      calc (2 : ℝ) ^ (m + 1) * ((D : ℝ) * P z j * (2 : ℝ) ^ p * (2 : ℝ) ^ (d j))
          = ((2 : ℝ) ^ (m + 1) * P z j) * ((D : ℝ) * (2 : ℝ) ^ p * (2 : ℝ) ^ (d j)) := by ring
        _ = ((2 : ℝ) ^ (m + 1 - p) * P z j + (2 : ℝ) ^ (m + 1 - d j)) *
              ((D : ℝ) * (2 : ℝ) ^ p * (2 : ℝ) ^ (d j)) := by rw [hunroll]
        _ = ((2 : ℝ) ^ (m + 1 - p) * (2 : ℝ) ^ p) * ((D : ℝ) * P z j * (2 : ℝ) ^ (d j)) +
            ((2 : ℝ) ^ (m + 1 - d j) * (2 : ℝ) ^ (d j)) * ((D : ℝ) * (2 : ℝ) ^ p) := by ring
        _ = (2 : ℝ) ^ (m + 1) * ((D : ℝ) * P z j * (2 : ℝ) ^ (d j) + (D : ℝ) * (2 : ℝ) ^ p) := by
            rw [hpow_p, hpow_d]; ring
    have hpos2 : (2 : ℝ) ^ (m + 1) ≠ 0 := by positivity
    have hcancel := mul_left_cancel₀ hpos2 hscaled
    rw [hP_z j] at hcancel
    have h2p_ge : 1 ≤ 2 ^ p := Nat.one_le_pow p 2 (by decide)
    have hcast_eq : ((A j * (2 ^ p - 1) * 2 ^ (d j) : ℕ) : ℝ) = ((D * 2 ^ p : ℕ) : ℝ) := by
      push_cast [Nat.cast_sub h2p_ge]
      linarith
    exact Nat.cast_injective hcast_eq
  have hp_ge2 : 2 ≤ p := by
    by_contra hlt
    have hp1 : p = 1 := by omega
    have h0 := hrel_j j0
    rw [hp1] at h0
    have hd0 : 1 ≤ d j0 := hd_pos j0
    have hpow : 2 ^ (d j0) = 2 * 2 ^ (d j0 - 1) := by
      rw [← pow_succ', Nat.sub_add_cancel hd0]
    rw [hpow] at h0
    have hmul : 2 ^ (d j0 - 1) * A j0 = D := by
      have h0' : 2 * (2 ^ (d j0 - 1) * A j0) = 2 * D := by
        have : A j0 * 1 * (2 * 2 ^ (d j0 - 1)) = D * 2 := by simpa using h0
        linarith
      exact Nat.eq_of_mul_eq_mul_left (by decide : 0 < 2) h0'
    exact (hA j0).2 (d j0 - 1) ⟨1, by omega⟩
  refine ⟨p, d, ⟨hp_ge2, fun j => ⟨hd_pos j, hrel_j j⟩⟩, ?_⟩
  intro b j
  have hsum_eq :
      (∑ w : Fin b → Bool, ((List.ofFn w).foldl
        (fun (x : Option (Fin s)) (bit : Bool) => x.bind (fun i => n i bit)) (some z)).elim 0
        (fun i => ((Finset.univ : Finset Bool).filter
          (fun bit => n i bit = none ∧ out i bit = j)).card)) =
      ((Finset.univ : Finset ((Fin b → Bool) × Bool)).filter (fun wb =>
        ∃ q : ℕ, List.ofFn wb.1 ++ [wb.2] = List.flatten (List.replicate q W_cyc) ++ W_out j)).card := by
    rw [Finset.card_filter, Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro w _
    change (runFrom n (some z) (List.ofFn w)).elim 0
      (fun i => ((Finset.univ : Finset Bool).filter
        (fun bit => n i bit = none ∧ out i bit = j)).card) = _
    cases hrun : runFrom n (some z) (List.ofFn w) with
    | none =>
      simp only [Option.elim_none]
      symm
      apply Finset.sum_eq_zero
      intro bit _
      rw [if_neg]
      intro hq
      obtain ⟨L_init, i, bit', heq, hrun', _, _⟩ := (hterm_char j (List.ofFn w ++ [bit])).mpr hq
      have ⟨hL, _⟩ := append_singleton_inj heq
      rw [← hL, hrun] at hrun'
      cases hrun'
    | some i =>
      simp only [Option.elim_some, Finset.card_filter]
      apply Finset.sum_congr rfl
      intro bit _
      congr 1
      apply propext
      rw [← hterm_char j (List.ofFn w ++ [bit])]
      constructor
      · rintro ⟨hnb, hout⟩
        exact ⟨List.ofFn w, i, bit, rfl, hrun, hnb, hout⟩
      · rintro ⟨L_init, i', bit', heq, hrun', hnb, hout⟩
        have ⟨hL, hb⟩ := append_singleton_inj heq
        rw [← hL, hrun] at hrun'
        have hi' : i = i' := Option.some.inj hrun'
        rw [hi', hb]
        exact ⟨hnb, hout⟩
  rw [hsum_eq]
  have hlen_rep : ∀ q : ℕ, (List.flatten (List.replicate q W_cyc) ++ W_out j).length = q * p + d j := by
    intro q
    simp [List.length_flatten, List.map_replicate, List.sum_replicate, p, d]
  split_ifs with hcond
  · obtain ⟨hd_le_b, hdiv⟩ := hcond
    obtain ⟨q0, hq0⟩ := hdiv
    let L0 : List Bool := List.flatten (List.replicate q0 W_cyc) ++ W_out j
    have hL0_len : L0.length = b + 1 := by
      rw [hlen_rep q0, mul_comm q0 p, ← hq0]
      omega
    let w0 : Fin b → Bool := fun r => L0[r.val]'(by omega)
    let b0 : Bool := L0[b]'(by omega)
    have hwb0 : List.ofFn w0 ++ [b0] = L0 := by
      apply List.ext_getElem
      · simp [hL0_len]
      · intro r hr1 hr2
        simp only [List.getElem_append, List.length_ofFn, List.getElem_ofFn, List.getElem_singleton]
        split_ifs with hr
        · rfl
        · have : r = b := by omega
          subst this; rfl
    have hfilt_eq :
        ((Finset.univ : Finset ((Fin b → Bool) × Bool)).filter (fun wb =>
          ∃ q : ℕ, List.ofFn wb.1 ++ [wb.2] = List.flatten (List.replicate q W_cyc) ++ W_out j)) =
        {(w0, b0)} := by
      ext wb
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      constructor
      · rintro ⟨q, hq⟩
        have hlen_q : q * p + d j = b + 1 := by
          have := congrArg List.length hq
          rw [hlen_rep q] at this
          simpa using this.symm
        have hqq0 : q = q0 := by
          have : q * p = q0 * p := by rw [mul_comm q0 p, ← hq0]; omega
          exact Nat.eq_of_mul_eq_mul_right (by omega : 0 < p) this
        rw [hqq0] at hq
        have heq_list : List.ofFn wb.1 ++ [wb.2] = List.ofFn w0 ++ [b0] := hq.trans hwb0.symm
        have ⟨h1, h2⟩ := append_singleton_inj heq_list
        exact Prod.ext (List.ofFn_injective h1) h2
      · intro heq
        rw [heq]
        exact ⟨q0, hwb0⟩
    rw [hfilt_eq, Finset.card_singleton]
  · have hempty :
        ((Finset.univ : Finset ((Fin b → Bool) × Bool)).filter (fun wb =>
          ∃ q : ℕ, List.ofFn wb.1 ++ [wb.2] = List.flatten (List.replicate q W_cyc) ++ W_out j)) = ∅ := by
      rw [Finset.filter_eq_empty_iff]
      intro wb _
      rintro ⟨q, hq⟩
      have hlen_q : q * p + d j = b + 1 := by
        have := congrArg List.length hq
        rw [hlen_rep q] at this
        simpa using this.symm
      apply hcond
      refine ⟨by omega, ⟨q, ?_⟩⟩
      rw [mul_comm]
      omega
    rw [hempty, Finset.card_empty]

def treeNext {k : ℕ} (child : Fin (k + 1) → Bool → Sum (Fin (k + 2)) (Fin (k + 1)))
    (i : Fin (k + 1)) (b : Bool) : Option (Fin (k + 1)) :=
  match child i b with
  | Sum.inl _ => none
  | Sum.inr j => some j

lemma kraft_tree (k : ℕ) :
    ∀ (N : ℕ) (L : Fin (k + 2) → ℕ),
      (∀ idx, L idx ≤ N) →
      (∑ idx : Fin (k + 2), 2 ^ (N - L idx)) = 2 ^ N →
      ∃ (root : Fin (k + 1))
        (child : Fin (k + 1) → Bool → Sum (Fin (k + 2)) (Fin (k + 1)))
        (rk : Fin (k + 1) → ℕ),
        (∀ i, rk i < k + 1) ∧
        (∀ i b j, child i b = Sum.inr j → rk j < rk i) ∧
        (∀ i, child i false ≠ child i true) ∧
        (∀ idx : Fin (k + 2), ∃ W : List Bool, W.length = L idx ∧
          ∀ L_init b,
            (∃ i, runFrom (treeNext child) (some root) L_init = some i ∧ child i b = Sum.inl idx) ↔
              L_init ++ [b] = W) := by
  classical
  induction k with
  | zero =>
    intro N L hL_le hKraft
    have hsum2 : 2 ^ (N - L 0) + 2 ^ (N - L 1) = 2 ^ N := by
      have := hKraft
      rw [Fin.sum_univ_two] at this
      exact this
    have hL0_pos : 1 ≤ L 0 := by
      by_contra h0
      have hL0 : L 0 = 0 := by omega
      rw [hL0, Nat.sub_zero] at hsum2
      have hpos : 1 ≤ 2 ^ (N - L 1) := Nat.one_le_pow _ 2 (by decide)
      omega
    have hL1_pos : 1 ≤ L 1 := by
      by_contra h0
      have hL1 : L 1 = 0 := by omega
      rw [hL1, Nat.sub_zero] at hsum2
      have hpos : 1 ≤ 2 ^ (N - L 0) := Nat.one_le_pow _ 2 (by decide)
      omega
    have hN_pos : 1 ≤ N := le_trans hL0_pos (hL_le 0)
    have hpow_le0 : 2 ^ (N - L 0) ≤ 2 ^ (N - 1) :=
      Nat.pow_le_pow_right (by decide) (by omega)
    have hpow_le1 : 2 ^ (N - L 1) ≤ 2 ^ (N - 1) :=
      Nat.pow_le_pow_right (by decide) (by omega)
    have h2N : 2 ^ N = 2 ^ (N - 1) + 2 ^ (N - 1) := by
      rw [← two_mul, ← pow_succ', Nat.sub_add_cancel hN_pos]
    have heq0 : 2 ^ (N - L 0) = 2 ^ (N - 1) := by omega
    have heq1 : 2 ^ (N - L 1) = 2 ^ (N - 1) := by omega
    have hL0_eq : L 0 = 1 := by
      have hinj := Nat.pow_right_injective (by decide : 1 < 2) heq0
      have := hL_le 0
      omega
    have hL1_eq : L 1 = 1 := by
      have hinj := Nat.pow_right_injective (by decide : 1 < 2) heq1
      have := hL_le 1
      omega
    let child : Fin 1 → Bool → Sum (Fin 2) (Fin 1) := fun _ b =>
      if b then Sum.inl 1 else Sum.inl 0
    refine ⟨0, child, (fun _ => 0 : Fin 1 → ℕ), fun _ => Nat.zero_lt_one, ?_, ?_, ?_⟩
    · intro i b j h
      dsimp only [child] at h
      cases b <;> simp at h
    · intro i
      dsimp only [child]
      simp
    · intro idx
      fin_cases idx
      · refine ⟨[false], by simp [hL0_eq], ?_⟩
        intro L_init b
        constructor
        · rintro ⟨i, hrun, hc⟩
          have hi : i = 0 := Fin.ext (by omega)
          subst hi
          have hb : b = false := by
            cases b
            · rfl
            · simp [child] at hc
          subst hb
          have hLnil : L_init = [] := by
            cases L_init with
            | nil => rfl
            | cons a t =>
              rw [runFrom_cons] at hrun
              have hnone : treeNext child 0 a = none := by cases a <;> rfl
              change runFrom (treeNext child) (treeNext child 0 a) t = some 0 at hrun
              rw [hnone, runFrom_none] at hrun
              cases hrun
          rw [hLnil]; rfl
        · intro heq
          have ⟨hL, hb⟩ := append_singleton_inj (show L_init ++ [b] = [] ++ [false] from heq)
          rw [hL, hb]
          exact ⟨0, rfl, rfl⟩
      · refine ⟨[true], by simp [hL1_eq], ?_⟩
        intro L_init b
        constructor
        · rintro ⟨i, hrun, hc⟩
          have hi : i = 0 := Fin.ext (by omega)
          subst hi
          have hb : b = true := by
            cases b
            · simp [child] at hc
            · rfl
          subst hb
          have hLnil : L_init = [] := by
            cases L_init with
            | nil => rfl
            | cons a t =>
              rw [runFrom_cons] at hrun
              have hnone : treeNext child 0 a = none := by cases a <;> rfl
              change runFrom (treeNext child) (treeNext child 0 a) t = some 0 at hrun
              rw [hnone, runFrom_none] at hrun
              cases hrun
          rw [hLnil]; rfl
        · intro heq
          have ⟨hL, hb⟩ := append_singleton_inj (show L_init ++ [b] = [] ++ [true] from heq)
          rw [hL, hb]
          exact ⟨0, rfl, rfl⟩
  | succ k ih =>
    intro N L hL_le hKraft
    let imgs : Finset ℕ := Finset.univ.image L
    have hne_imgs : imgs.Nonempty := ⟨L 0, Finset.mem_image_of_mem L (Finset.mem_univ 0)⟩
    let M : ℕ := imgs.max' hne_imgs
    have hL_le_M : ∀ idx, L idx ≤ M := fun idx =>
      Finset.le_max' imgs (L idx) (Finset.mem_image_of_mem L (Finset.mem_univ idx))
    have hM_mem : ∃ idx_m, L idx_m = M := by
      obtain ⟨idx, _, hidx⟩ := Finset.mem_image.mp (Finset.max'_mem imgs hne_imgs)
      exact ⟨idx, hidx⟩
    obtain ⟨idx_m, hidx_m⟩ := hM_mem
    have hM_le_N : M ≤ N := hidx_m ▸ hL_le idx_m
    have hKraft_M : (∑ idx : Fin (k + 3), 2 ^ (M - L idx)) = 2 ^ M := by
      have hmul : 2 ^ (N - M) * (∑ idx : Fin (k + 3), 2 ^ (M - L idx)) = 2 ^ (N - M) * 2 ^ M := by
        rw [Finset.mul_sum, ← pow_add, Nat.sub_add_cancel hM_le_N, ← hKraft]
        apply Finset.sum_congr rfl
        intro idx _
        rw [← pow_add]
        congr 1
        have := hL_le_M idx
        omega
      exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero (by positivity)) hmul
    have hM_ge2 : 2 ≤ M := by
      by_contra hlt
      have hsum_ge : k + 3 ≤ ∑ idx : Fin (k + 3), 2 ^ (M - L idx) := by
        calc k + 3 = ∑ _idx : Fin (k + 3), 1 := by simp
          _ ≤ ∑ idx : Fin (k + 3), 2 ^ (M - L idx) :=
              Finset.sum_le_sum (fun idx _ => Nat.one_le_pow _ 2 (by decide))
      rw [hKraft_M] at hsum_ge
      have hpow_le : 2 ^ M ≤ 2 := by
        have : M = 0 ∨ M = 1 := by omega
        rcases this with h0 | h1
        · rw [h0]; decide
        · rw [h1]; decide
      omega
    let Top : Finset (Fin (k + 3)) := Finset.univ.filter (fun idx => L idx = M)
    have hTop_ne : Top.Nonempty := ⟨idx_m, Finset.mem_filter.mpr ⟨Finset.mem_univ idx_m, hidx_m⟩⟩
    have hTop_even : 2 ∣ Top.card := by
      have hsplit : (∑ idx : Fin (k + 3), 2 ^ (M - L idx)) =
          (∑ idx ∈ Top, 2 ^ (M - L idx)) + (∑ idx ∈ Finset.univ.filter (fun idx => L idx ≠ M), 2 ^ (M - L idx)) := by
        rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun idx => L idx = M)]
      have h1 : (∑ idx ∈ Top, 2 ^ (M - L idx)) = Top.card := by
        calc (∑ idx ∈ Top, 2 ^ (M - L idx)) = ∑ _idx ∈ Top, 1 := by
              apply Finset.sum_congr rfl
              intro idx hidx
              rw [(Finset.mem_filter.mp hidx).2, Nat.sub_self, pow_zero]
          _ = Top.card := by simp
      have h2 : 2 ∣ ∑ idx ∈ Finset.univ.filter (fun idx => L idx ≠ M), 2 ^ (M - L idx) := by
        apply Finset.dvd_sum
        intro idx hidx
        have hne : L idx ≠ M := (Finset.mem_filter.mp hidx).2
        have hle := hL_le_M idx
        have hpos : 1 ≤ M - L idx := by omega
        rw [show M - L idx = (M - L idx - 1) + 1 by omega, pow_succ']
        exact dvd_mul_right 2 _
      have h2M : 2 ∣ 2 ^ M := by
        rw [show M = (M - 1) + 1 by omega, pow_succ']
        exact dvd_mul_right 2 _
      rw [hsplit, h1] at hKraft_M
      exact (Nat.dvd_add_left h2).mp (hKraft_M.symm ▸ h2M)
    have hTop_ge2 : 1 < Top.card := by
      have hpos : 0 < Top.card := Finset.card_pos.mpr hTop_ne
      obtain ⟨c, hc⟩ := hTop_even
      omega
    obtain ⟨i1, hi1_top, i2, hi2_top, hi12_ne⟩ := Finset.one_lt_card.mp hTop_ge2
    have hLi1 : L i1 = M := (Finset.mem_filter.mp hi1_top).2
    have hLi2 : L i2 = M := (Finset.mem_filter.mp hi2_top).2
    let Rest : Finset (Fin (k + 3)) := (Finset.univ.erase i1).erase i2
    have hRest_card : Rest.card = k + 1 := by
      have hi2_in : i2 ∈ Finset.univ.erase i1 := Finset.mem_erase.mpr ⟨hi12_ne.symm, Finset.mem_univ i2⟩
      rw [Finset.card_erase_of_mem hi2_in, Finset.card_erase_of_mem (Finset.mem_univ i1),
        Finset.card_univ, Fintype.card_fin]
      omega
    let eRest : {x : Fin (k + 3) // x ∈ Rest} ≃ Fin (k + 1) :=
      Finset.equivFinOfCardEq hRest_card
    let L' : Fin (k + 2) → ℕ := Fin.cases (M - 1) (fun r => L (eRest.symm r).val)
    have hL'_le : ∀ j, L' j ≤ N := by
      intro j
      refine Fin.cases ?_ ?_ j
      · simp only [L', Fin.cases_zero]; omega
      · intro r; simp only [L', Fin.cases_succ]; exact hL_le _
    have hKraft' : (∑ j : Fin (k + 2), 2 ^ (N - L' j)) = 2 ^ N := by
      rw [Fin.sum_univ_succ]
      simp only [L', Fin.cases_zero, Fin.cases_succ]
      have hsum_rest : (∑ r : Fin (k + 1), 2 ^ (N - L (eRest.symm r).val)) =
          ∑ x ∈ Rest, 2 ^ (N - L x) := by
        rw [← Finset.sum_coe_sort Rest (fun x => 2 ^ (N - L x))]
        exact Fintype.sum_equiv eRest.symm _ _ (fun r => rfl)
      rw [hsum_rest]
      have hfull : (∑ x : Fin (k + 3), 2 ^ (N - L x)) =
          2 ^ (N - L i1) + 2 ^ (N - L i2) + ∑ x ∈ Rest, 2 ^ (N - L x) := by
        have h1 : (∑ x : Fin (k + 3), 2 ^ (N - L x)) =
            2 ^ (N - L i1) + ∑ x ∈ Finset.univ.erase i1, 2 ^ (N - L x) :=
          (Finset.add_sum_erase Finset.univ (fun x => 2 ^ (N - L x)) (Finset.mem_univ i1)).symm
        have hi2_in : i2 ∈ Finset.univ.erase i1 := Finset.mem_erase.mpr ⟨hi12_ne.symm, Finset.mem_univ i2⟩
        have h2 : (∑ x ∈ Finset.univ.erase i1, 2 ^ (N - L x)) =
            2 ^ (N - L i2) + ∑ x ∈ Rest, 2 ^ (N - L x) :=
          (Finset.add_sum_erase (Finset.univ.erase i1) (fun x => 2 ^ (N - L x)) hi2_in).symm
        rw [h1, h2, add_assoc]
      have hmerge : 2 ^ (N - (M - 1)) = 2 ^ (N - M) + 2 ^ (N - M) := by
        rw [← two_mul, ← pow_succ']
        congr 1
        omega
      rw [hLi1, hLi2] at hfull
      rw [hmerge, ← hfull, hKraft]
    obtain ⟨root', child', rk', hrk'_lt, hrk'_dec, hch'_ne, hleaf'⟩ := ih N L' hL'_le hKraft'
    let liftOut : Sum (Fin (k + 2)) (Fin (k + 1)) → Sum (Fin (k + 3)) (Fin (k + 2))
      | Sum.inr j0 => Sum.inr j0.castSucc
      | Sum.inl idx' =>
          Fin.cases (Sum.inr (Fin.last (k + 1))) (fun r => Sum.inl (eRest.symm r).val) idx'
    have hlift_inj : Function.Injective liftOut := by
      intro a b hab
      cases a with
      | inl ia =>
        cases b with
        | inl ib =>
          congr 1
          induction ia using Fin.cases with
          | zero =>
            induction ib using Fin.cases with
            | zero => rfl
            | succ rb =>
              simp only [liftOut, Fin.cases_zero, Fin.cases_succ] at hab
              cases hab
          | succ ra =>
            induction ib using Fin.cases with
            | zero =>
              simp only [liftOut, Fin.cases_zero, Fin.cases_succ] at hab
              cases hab
            | succ rb =>
              simp only [liftOut, Fin.cases_succ] at hab
              have hval : (eRest.symm ra).val = (eRest.symm rb).val := Sum.inl.inj hab
              have hsub : eRest.symm ra = eRest.symm rb := Subtype.ext hval
              rw [eRest.symm.injective hsub]
        | inr jb =>
          induction ia using Fin.cases with
          | zero =>
            simp only [liftOut, Fin.cases_zero] at hab
            exact absurd (Sum.inr.inj hab) (Fin.castSucc_ne_last jb).symm
          | succ ra =>
            simp only [liftOut, Fin.cases_succ] at hab
            cases hab
      | inr ja =>
        cases b with
        | inl ib =>
          induction ib using Fin.cases with
          | zero =>
            simp only [liftOut, Fin.cases_zero] at hab
            exact absurd (Sum.inr.inj hab) (Fin.castSucc_ne_last ja)
          | succ rb =>
            simp only [liftOut, Fin.cases_succ] at hab
            cases hab
        | inr jb =>
          simp only [liftOut] at hab
          exact congrArg Sum.inr (Fin.castSucc_injective _ (Sum.inr.inj hab))
    let root : Fin (k + 2) := root'.castSucc
    let rk : Fin (k + 2) → ℕ := Fin.snoc (fun i => rk' i + 1) 0
    let child : Fin (k + 2) → Bool → Sum (Fin (k + 3)) (Fin (k + 2)) :=
      Fin.snoc (fun i0 b => liftOut (child' i0 b)) (fun b => if b then Sum.inl i2 else Sum.inl i1)
    have hchild_cast : ∀ (i0 : Fin (k + 1)) (b : Bool),
        child i0.castSucc b = liftOut (child' i0 b) := fun i0 b => by
      dsimp only [child]
      rw [Fin.snoc_castSucc]
    have hchild_last : ∀ b : Bool,
        child (Fin.last (k + 1)) b = if b then Sum.inl i2 else Sum.inl i1 := fun b => by
      dsimp only [child]
      rw [Fin.snoc_last]
    have hstep_cast : ∀ (i : Fin (k + 2)) (b : Bool) (j0 : Fin (k + 1)),
        treeNext child i b = some j0.castSucc ↔
        ∃ i0 : Fin (k + 1), i = i0.castSucc ∧ treeNext child' i0 b = some j0 := by
      intro i b j0
      refine Fin.lastCases ?_ ?_ i
      · simp only [treeNext, hchild_last]
        constructor
        · intro h; cases b <;> simp at h
        · rintro ⟨i0, heq, _⟩; exact absurd heq.symm (Fin.castSucc_ne_last i0)
      · intro i0
        simp only [Fin.castSucc_inj, exists_eq_left']
        dsimp only [treeNext]
        rw [hchild_cast i0 b]
        cases hcb : child' i0 b with
        | inl idx' =>
          refine Fin.cases ?_ ?_ idx'
          · simp only [liftOut, Fin.cases_zero]
            constructor
            · intro h; exact absurd (Option.some.inj h) (Fin.castSucc_ne_last j0).symm
            · intro h; cases h
          · intro r
            simp only [liftOut, Fin.cases_succ]
            constructor <;> (intro h; cases h)
        | inr j1 =>
          simp only [liftOut, Option.some.injEq, Fin.castSucc_inj]
    have hrun_cast : ∀ (L_init : List Bool) (i0 : Fin (k + 1)),
        runFrom (treeNext child) (some root) L_init = some i0.castSucc ↔
        runFrom (treeNext child') (some root') L_init = some i0 := by
      intro L_init
      induction L_init using List.reverseRecOn with
      | nil =>
        intro i0
        simp [runFrom_nil, root]
      | append_singleton L1 b ih =>
        intro i0
        constructor
        · intro h
          obtain ⟨w, hw, hst⟩ := runFrom_append_some (treeNext child) (some root) L1 [b] i0.castSucc h
          rw [runFrom_singleton] at hst
          obtain ⟨w0, rfl, hst'⟩ := (hstep_cast w b i0).mp hst
          rw [runFrom_append, (ih w0).mp hw, runFrom_singleton, hst']
        · intro h
          obtain ⟨w0, hw0, hst'⟩ := runFrom_append_some (treeNext child') (some root') L1 [b] i0 h
          rw [runFrom_singleton] at hst'
          rw [runFrom_append, (ih w0).mpr hw0, runFrom_singleton]
          exact (hstep_cast w0.castSucc b i0).mpr ⟨w0, rfl, hst'⟩
    obtain ⟨W0, hW0_len, hW0_iff⟩ := hleaf' 0
    have hW0_len_eq : W0.length = M - 1 := by simpa [L'] using hW0_len
    have hW0_ne : W0 ≠ [] := by
      intro hnil
      rw [hnil] at hW0_len_eq
      simp at hW0_len_eq
      omega
    have hstep_last : ∀ (i : Fin (k + 2)) (b : Bool),
        treeNext child i b = some (Fin.last (k + 1)) ↔
        ∃ i0 : Fin (k + 1), i = i0.castSucc ∧ child' i0 b = Sum.inl 0 := by
      intro i b
      refine Fin.lastCases ?_ ?_ i
      · simp only [treeNext, hchild_last]
        constructor
        · intro h; cases b <;> simp at h
        · rintro ⟨i0, heq, _⟩; exact absurd heq.symm (Fin.castSucc_ne_last i0)
      · intro i0
        simp only [Fin.castSucc_inj, exists_eq_left']
        dsimp only [treeNext]
        rw [hchild_cast i0 b]
        cases hcb : child' i0 b with
        | inl idx' =>
          refine Fin.cases ?_ ?_ idx'
          · simp [liftOut]
          · intro r
            simp only [liftOut, Fin.cases_succ]
            constructor
            · intro h; cases h
            · intro h; exact absurd (Sum.inl.inj h) (Fin.succ_ne_zero r)
        | inr j1 =>
          simp only [liftOut]
          constructor
          · intro h; exact absurd (Option.some.inj h) (Fin.castSucc_ne_last j1)
          · intro h; cases h
    have hrun_last : ∀ (L_init : List Bool),
        runFrom (treeNext child) (some root) L_init = some (Fin.last (k + 1)) ↔ L_init = W0 := by
      intro L_init
      cases L_init using List.reverseRecOn with
      | nil =>
        simp only [runFrom_nil, Option.some.injEq]
        constructor
        · intro h; exact absurd h (Fin.castSucc_ne_last root')
        · intro h; exact absurd h.symm hW0_ne
      | append_singleton L1 b =>
        constructor
        · intro h
          obtain ⟨w, hw, hst⟩ := runFrom_append_some (treeNext child) (some root) L1 [b] (Fin.last (k + 1)) h
          rw [runFrom_singleton] at hst
          obtain ⟨w0, rfl, hch0⟩ := (hstep_last w b).mp hst
          exact (hW0_iff L1 b).mp ⟨w0, (hrun_cast L1 w0).mp hw, hch0⟩
        · intro h
          obtain ⟨w0, hw0, hch0⟩ := (hW0_iff L1 b).mpr h
          rw [runFrom_append, (hrun_cast L1 w0).mpr hw0, runFrom_singleton]
          exact (hstep_last w0.castSucc b).mpr ⟨w0, rfl, hch0⟩
    refine ⟨root, child, rk, ?_, ?_, ?_, ?_⟩
    · intro i
      refine Fin.lastCases ?_ ?_ i
      · simp [rk]
      · intro i0; simp only [rk, Fin.snoc_castSucc]; have := hrk'_lt i0; omega
    · intro i b j hch
      induction i using Fin.lastCases with
      | last =>
        rw [hchild_last] at hch
        cases b <;> simp at hch
      | cast i0 =>
        rw [hchild_cast i0 b] at hch
        simp only [rk, Fin.snoc_castSucc]
        cases hcb : child' i0 b with
        | inl idx' =>
          rw [hcb] at hch
          induction idx' using Fin.cases with
          | zero =>
            simp only [liftOut, Fin.cases_zero] at hch
            have hj : j = Fin.last (k + 1) := (Sum.inr.inj hch).symm
            rw [hj, Fin.snoc_last]; omega
          | succ r =>
            simp only [liftOut, Fin.cases_succ] at hch
            cases hch
        | inr j0 =>
          rw [hcb] at hch
          simp only [liftOut] at hch
          have hj : j = j0.castSucc := (Sum.inr.inj hch).symm
          rw [hj, Fin.snoc_castSucc]
          have := hrk'_dec i0 b j0 hcb
          omega
    · intro i
      refine Fin.lastCases ?_ ?_ i
      · simp [hchild_last, hi12_ne]
      · intro i0
        rw [hchild_cast i0 false, hchild_cast i0 true]
        exact fun h => hch'_ne i0 (hlift_inj h)
    · intro idx
      by_cases h1 : idx = i1
      · rw [h1]
        refine ⟨W0 ++ [false], by simp [hW0_len_eq, hLi1]; omega, ?_⟩
        intro L_init b
        have hch_iff : ∀ i, child i b = Sum.inl i1 ↔ i = Fin.last (k + 1) ∧ b = false := by
          intro i
          refine Fin.lastCases ?_ ?_ i
          · rw [hchild_last]
            cases b
            · simp
            · simp [hi12_ne.symm]
          · intro i0
            rw [hchild_cast i0 b]
            simp only [Fin.castSucc_ne_last, false_and, iff_false]
            cases child' i0 b with
            | inr _ => simp [liftOut]
            | inl idx' =>
              refine Fin.cases ?_ ?_ idx'
              · simp [liftOut]
              · intro r
                simp only [liftOut, Fin.cases_succ, Sum.inl.injEq]
                intro hval
                have hmem := (eRest.symm r).property
                rw [hval] at hmem
                exact Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hmem) rfl
        constructor
        · rintro ⟨i, hrun, hch⟩
          obtain ⟨rfl, rfl⟩ := (hch_iff i).mp hch
          rw [(hrun_last L_init).mp hrun]
        · intro heq
          have ⟨hL, hb⟩ := append_singleton_inj heq
          rw [hL, hb]
          exact ⟨Fin.last (k + 1), (hrun_last W0).mpr rfl, by simp [hchild_last]⟩
      · by_cases h2 : idx = i2
        · rw [h2]
          refine ⟨W0 ++ [true], by simp [hW0_len_eq, hLi2]; omega, ?_⟩
          intro L_init b
          have hch_iff : ∀ i, child i b = Sum.inl i2 ↔ i = Fin.last (k + 1) ∧ b = true := by
            intro i
            refine Fin.lastCases ?_ ?_ i
            · rw [hchild_last]
              cases b
              · simp [hi12_ne]
              · simp
            · intro i0
              rw [hchild_cast i0 b]
              simp only [Fin.castSucc_ne_last, false_and, iff_false]
              cases child' i0 b with
              | inr _ => simp [liftOut]
              | inl idx' =>
                refine Fin.cases ?_ ?_ idx'
                · simp [liftOut]
                · intro r
                  simp only [liftOut, Fin.cases_succ, Sum.inl.injEq]
                  intro hval
                  have hmem := (eRest.symm r).property
                  rw [hval] at hmem
                  exact Finset.ne_of_mem_erase hmem rfl
          constructor
          · rintro ⟨i, hrun, hch⟩
            obtain ⟨rfl, rfl⟩ := (hch_iff i).mp hch
            rw [(hrun_last L_init).mp hrun]
          · intro heq
            have ⟨hL, hb⟩ := append_singleton_inj heq
            rw [hL, hb]
            exact ⟨Fin.last (k + 1), (hrun_last W0).mpr rfl, by simp [hchild_last]⟩
        · have hmem_Rest : idx ∈ Rest :=
            Finset.mem_erase.mpr ⟨h2, Finset.mem_erase.mpr ⟨h1, Finset.mem_univ idx⟩⟩
          let r : Fin (k + 1) := eRest ⟨idx, hmem_Rest⟩
          have hr_val : (eRest.symm r).val = idx := by
            dsimp only [r]; simp
          obtain ⟨Wr, hWr_len, hWr_iff⟩ := hleaf' r.succ
          have hWr_len_eq : Wr.length = L idx := by
            simpa [L', hr_val] using hWr_len
          refine ⟨Wr, hWr_len_eq, ?_⟩
          intro L_init b
          have hch_iff : ∀ i, child i b = Sum.inl idx ↔
              ∃ i0 : Fin (k + 1), i = i0.castSucc ∧ child' i0 b = Sum.inl r.succ := by
            intro i
            refine Fin.lastCases ?_ ?_ i
            · rw [hchild_last]
              constructor
              · intro hc
                cases b
                · simp at hc; exact absurd hc.symm h1
                · simp at hc; exact absurd hc.symm h2
              · rintro ⟨i0, heq, _⟩; exact absurd heq.symm (Fin.castSucc_ne_last i0)
            · intro i0
              rw [hchild_cast i0 b]
              simp only [Fin.castSucc_inj, exists_eq_left']
              cases hcb : child' i0 b with
              | inr _ => simp [liftOut]
              | inl idx' =>
                refine Fin.cases ?_ ?_ idx'
                · simp [liftOut, (Fin.succ_ne_zero r).symm]
                · intro r'
                  simp only [liftOut, Fin.cases_succ, Sum.inl.injEq, Fin.succ_inj]
                  constructor
                  · intro hval
                    have hsub : eRest.symm r' = eRest.symm r := Subtype.ext (hval.trans hr_val.symm)
                    exact eRest.symm.injective hsub
                  · intro hrr
                    rw [hrr, hr_val]
          constructor
          · rintro ⟨i, hrun, hch⟩
            obtain ⟨i0, rfl, hch'⟩ := (hch_iff i).mp hch
            exact (hWr_iff L_init b).mp ⟨i0, (hrun_cast L_init i0).mp hrun, hch'⟩
          · intro heq
            obtain ⟨i0, hi0, hch'⟩ := (hWr_iff L_init b).mpr heq
            exact ⟨i0.castSucc, (hrun_cast L_init i0).mpr hi0, (hch_iff i0.castSucc).mpr ⟨i0, rfl, hch'⟩⟩

lemma part2_converse (m D : ℕ) (A : Fin m → ℕ) (hm : 2 ≤ m) (hD : 0 < D)
    (hsumA : (∑ j, A j) = D)
    (p : ℕ) (d : Fin m → ℕ)
    (hp : 2 ≤ p) (hd : ∀ j, 0 < d j ∧ A j * (2 ^ p - 1) * 2 ^ (d j) = D * 2 ^ p) :
    ∃ (z : Fin m) (n : Fin m → Bool → Option (Fin m))
      (out : Fin m → Bool → Fin m) (P : Fin m → Fin m → ℝ),
      Absorbs n ∧
      (∀ i j, 2 * P i j = ∑ bit : Bool, (n i bit).elim
        (if out i bit = j then (1 : ℝ) else 0) (fun k => P k j)) ∧
      ∀ j, (D : ℝ) * P z j = (A j : ℝ) := by
  classical
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show m ≠ 0 by omega)
  let L : Fin (k + 2) → ℕ := Fin.snoc d p
  let imgs : Finset ℕ := Finset.univ.image L
  have hne_imgs : imgs.Nonempty := ⟨L 0, Finset.mem_image_of_mem L (Finset.mem_univ 0)⟩
  let N : ℕ := imgs.max' hne_imgs
  have hL_le : ∀ idx, L idx ≤ N := fun idx =>
    Finset.le_max' imgs (L idx) (Finset.mem_image_of_mem L (Finset.mem_univ idx))
  have hp_le_N : p ≤ N := by
    have := hL_le (Fin.last (k + 1))
    simpa [L] using this
  have hd_le_N : ∀ j, d j ≤ N := fun j => by
    have := hL_le j.castSucc
    simpa [L] using this
  have hKraft : (∑ idx : Fin (k + 2), 2 ^ (N - L idx)) = 2 ^ N := by
    have hmul : D * 2 ^ p * (∑ idx : Fin (k + 2), 2 ^ (N - L idx)) = D * 2 ^ p * 2 ^ N := by
      rw [Fin.sum_univ_castSucc, mul_add, Finset.mul_sum]
      have hterm_j : ∀ j : Fin (k + 1),
          D * 2 ^ p * 2 ^ (N - L j.castSucc) = A j * (2 ^ p - 1) * 2 ^ N := by
        intro j
        simp only [L, Fin.snoc_castSucc]
        rw [← (hd j).2, mul_assoc (A j * (2 ^ p - 1)), ← pow_add, Nat.add_sub_cancel' (hd_le_N j)]
      have hsum_j : (∑ j : Fin (k + 1), D * 2 ^ p * 2 ^ (N - L j.castSucc)) =
          D * (2 ^ p - 1) * 2 ^ N := by
        simp_rw [hterm_j, ← Finset.sum_mul, hsumA]
      rw [hsum_j]
      simp only [L, Fin.snoc_last]
      have hlast : D * 2 ^ p * 2 ^ (N - p) = D * 2 ^ N := by
        rw [mul_assoc, ← pow_add, Nat.add_sub_cancel' hp_le_N]
      rw [hlast]
      have h2p_ge : 1 ≤ 2 ^ p := Nat.one_le_pow p 2 (by decide)
      calc D * (2 ^ p - 1) * 2 ^ N + D * 2 ^ N
          = D * ((2 ^ p - 1) + 1) * 2 ^ N := by ring
        _ = D * 2 ^ p * 2 ^ N := by rw [Nat.sub_add_cancel h2p_ge]
    have hpos : 0 < D * 2 ^ p := Nat.mul_pos hD (by positivity)
    exact Nat.eq_of_mul_eq_mul_left hpos hmul
  obtain ⟨root, child, rk, hrk_lt, hrk_dec, hch_ne, hleaf⟩ := kraft_tree k N L hL_le hKraft
  let n0 := treeNext child
  let n : Fin (k + 1) → Bool → Option (Fin (k + 1)) := fun i b =>
    match child i b with
    | Sum.inr j => some j
    | Sum.inl idx => if idx = Fin.last (k + 1) then some root else none
  let out : Fin (k + 1) → Bool → Fin (k + 1) := fun i b =>
    match child i b with
    | Sum.inl idx => if h : idx.val < k + 1 then ⟨idx.val, h⟩ else ⟨0, by omega⟩
    | Sum.inr _ => ⟨0, by omega⟩
  have hn_abs : Absorbs n := by
    let pick : Fin (k + 1) → Bool := fun i =>
      if child i false = Sum.inl (Fin.last (k + 1)) then true else false
    refine ⟨pick, ?_⟩
    have hpick_eq : ∀ i, n i (pick i) = n0 i (pick i) := by
      intro i
      have hne_last : child i (pick i) ≠ Sum.inl (Fin.last (k + 1)) := by
        dsimp only [pick]
        split_ifs with hf
        · intro ht; exact hch_ne i (hf.trans ht.symm)
        · exact hf
      cases hcb : child i (pick i) with
      | inr j => simp [n, n0, treeNext, hcb]
      | inl idx =>
        have hidx : idx ≠ Fin.last (k + 1) := fun heq => hne_last (hcb.trans (congrArg Sum.inl heq))
        simp [n, n0, treeNext, hcb, hidx]
    let F := fun o : Option (Fin (k + 1)) => o.bind (fun h => n h (pick h))
    have hrk_step : ∀ (t : ℕ) (i j : Fin (k + 1)),
        F^[t] (some i) = some j → rk j + t ≤ rk i := by
      intro t
      induction t with
      | zero =>
        intro i j h
        have hij : i = j := Option.some.inj h
        rw [hij]; omega
      | succ t ih =>
        intro i j h
        rw [Function.iterate_succ_apply'] at h
        cases hprev : F^[t] (some i) with
        | none =>
          rw [hprev] at h; cases h
        | some hst =>
          rw [hprev] at h
          change n hst (pick hst) = some j at h
          rw [hpick_eq hst] at h
          dsimp only [n0, treeNext] at h
          cases hcb : child hst (pick hst) with
          | inl _ => rw [hcb] at h; cases h
          | inr j' =>
            rw [hcb] at h
            have hjj' : j' = j := Option.some.inj h
            have hdec := hrk_dec hst (pick hst) j (hjj' ▸ hcb)
            have hih := ih i hst hprev
            omega
    intro i
    cases hres : F^[k + 1] (some i) with
    | none => rfl
    | some j =>
      have h1 := hrk_step (k + 1) i j hres
      have h2 := hrk_lt i
      omega
  let P : Fin (k + 1) → Fin (k + 1) → ℝ := fun i j =>
    mean n hn_abs (fun i' bit => if out i' bit = j then (1 : ℝ) else 0) i
  have hP_eq : ∀ i j, 2 * P i j = ∑ bit : Bool, (n i bit).elim
      (if out i bit = j then (1 : ℝ) else 0) (fun q => P q j) := by
    intro i j
    rw [sum_bool_comm]
    exact mean_solves n hn_abs (fun i' bit => if out i' bit = j then (1 : ℝ) else 0) i
  have hn0_none_ge : ∀ (L_w : List Bool), N + 1 ≤ L_w.length → runFrom n0 (some root) L_w = none := by
    have hW_ext : ∀ (v : Fin (k + 1)),
        ∃ L_ext : List Bool, ∃ idx : Fin (k + 2), ∃ w b,
          runFrom n0 (some v) L_ext = some w ∧ child w b = Sum.inl idx := by
      intro v
      induction hv : rk v using Nat.strong_induction_on generalizing v with
      | ind r ih_r =>
        cases hcb : child v false with
        | inl idx => exact ⟨[], idx, v, false, rfl, hcb⟩
        | inr v' =>
          have hlt_r : rk v' < r := hv ▸ hrk_dec v false v' hcb
          obtain ⟨L_ext, idx, w, b, hrun_e, hch_e⟩ := ih_r (rk v') hlt_r v' rfl
          exact ⟨false :: L_ext, idx, w, b, by
            rw [runFrom_cons]
            change runFrom n0 (n0 v false) L_ext = some w
            dsimp only [n0, treeNext]; rw [hcb]; exact hrun_e, hch_e⟩
    intro L_w hlen
    cases hrun : runFrom n0 (some root) L_w with
    | none => rfl
    | some j =>
      exfalso
      obtain ⟨L_ext, idx, w, b, hrun_e, hch_e⟩ := hW_ext j
      obtain ⟨W_idx, hW_len, hW_iff⟩ := hleaf idx
      have hrun_full : runFrom n0 (some root) (L_w ++ L_ext) = some w := by
        rw [runFrom_append, hrun, hrun_e]
      have hW_eq := (hW_iff (L_w ++ L_ext) b).mp ⟨w, hrun_full, hch_e⟩
      have hlen_W : (L_w ++ L_ext ++ [b]).length = L idx := by
        have := congrArg List.length hW_eq
        rw [hW_len] at this
        simpa using this
      have hidx_le := hL_le idx
      simp at hlen_W
      omega
  have hP_z : ∀ j : Fin (k + 1), (D : ℝ) * P root j = (A j : ℝ) := by
    intro j
    let lv : Fin (k + 1) → Bool → ℝ := fun i b =>
      match child i b with
      | Sum.inl idx =>
          if idx = Fin.last (k + 1) then P root j
          else if idx = j.castSucc then 1 else 0
      | Sum.inr _ => 0
    have hval : ∀ i : Fin (k + 1),
        2 * P i j = ∑ bit : Bool, (n0 i bit).elim (lv i bit) (fun q => P q j) := by
      intro i
      rw [hP_eq i j]
      apply Finset.sum_congr rfl
      intro bit _
      cases hcb : child i bit with
      | inr q => simp [n, n0, treeNext, lv, hcb]
      | inl idx =>
        simp only [n, n0, treeNext, out, lv, hcb]
        by_cases hlast : idx = Fin.last (k + 1)
        · rw [if_pos hlast, if_pos hlast]; rfl
        · rw [if_neg hlast, if_neg hlast]
          have hlt : idx.val < k + 1 := by
            have := idx.isLt
            have hne : idx.val ≠ k + 1 := fun h => hlast (Fin.ext h)
            omega
          simp only [Option.elim_none, dif_pos hlt]
          by_cases hj : idx = j.castSucc
          · rw [if_pos hj, if_pos (Fin.ext (show idx.val = j.val from congrArg Fin.val hj))]
          · rw [if_neg hj, if_neg]
            intro heq
            exact hj (Fin.ext (show idx.val = j.val from congrArg Fin.val heq))
    have hunroll := unroll_tree n0 (fun i => P i j) lv hval (N + 1) (some root)
    simp only [Option.elim_some] at hunroll
    have hrem : (∑ w : Fin (N + 1) → Bool, (runFrom n0 (some root) (List.ofFn w)).elim 0 (fun i => P i j)) = 0 := by
      apply Finset.sum_eq_zero
      intro w _
      rw [hn0_none_ge (List.ofFn w) (by simp)]
      rfl
    rw [hrem, add_zero] at hunroll
    have hsum_split :
        (∑ t : Fin (N + 1), (2 : ℝ) ^ (N + 1 - 1 - t.val) *
          ∑ w : Fin t.val → Bool, (runFrom n0 (some root) (List.ofFn w)).elim 0
            (fun i => ∑ bit : Bool, if n0 i bit = none then lv i bit else 0)) =
        (∑ t : Fin (N + 1), (2 : ℝ) ^ (N + 1 - 1 - t.val) *
          ∑ w : Fin t.val → Bool, (runFrom n0 (some root) (List.ofFn w)).elim 0
            (fun i => ∑ bit : Bool, if child i bit = Sum.inl (Fin.last (k + 1)) then P root j else 0)) +
        (∑ t : Fin (N + 1), (2 : ℝ) ^ (N + 1 - 1 - t.val) *
          ∑ w : Fin t.val → Bool, (runFrom n0 (some root) (List.ofFn w)).elim 0
            (fun i => ∑ bit : Bool, if child i bit = Sum.inl j.castSucc then (1 : ℝ) else 0)) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro t _
      rw [← mul_add, ← Finset.sum_add_distrib]
      congr 1
      apply Finset.sum_congr rfl
      intro w _
      cases runFrom n0 (some root) (List.ofFn w) with
      | none => simp
      | some i =>
        simp only [Option.elim_some, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro bit _
        cases hcb : child i bit with
        | inr q => simp [n0, treeNext, lv, hcb]
        | inl idx =>
          simp only [n0, treeNext, lv, hcb, ↓reduceIte, Sum.inl.injEq]
          by_cases h1 : idx = Fin.last (k + 1)
          · rw [if_pos h1, if_pos h1, if_neg (h1 ▸ (Fin.castSucc_ne_last j).symm), add_zero]
          · rw [if_neg h1, if_neg h1, zero_add]
    rw [hsum_split] at hunroll
    obtain ⟨W_p, hWp_len, hWp_iff⟩ := hleaf (Fin.last (k + 1))
    obtain ⟨W_j, hWj_len, hWj_iff⟩ := hleaf j.castSucc
    have hWp_eq : W_p.length = p := by simpa [L] using hWp_len
    have hWj_eq : W_j.length = d j := by simpa [L] using hWj_len
    have hterm1 := unroll_leaf_sum n0 root (N + 1)
      (fun i bit => child i bit = Sum.inl (Fin.last (k + 1))) W_p
      (by rw [hWp_eq]; omega) (by rw [hWp_eq]; omega) hWp_iff (P root j)
    have hterm2 := unroll_leaf_sum n0 root (N + 1)
      (fun i bit => child i bit = Sum.inl j.castSucc) W_j
      (by rw [hWj_eq]; have := (hd j).1; omega) (by rw [hWj_eq]; have := hd_le_N j; omega) hWj_iff (1 : ℝ)
    rw [hterm1, hterm2, hWp_eq, hWj_eq, mul_one] at hunroll
    have hpow_p : (2 : ℝ) ^ (N + 1 - p) * (2 : ℝ) ^ p = (2 : ℝ) ^ (N + 1) := by
      rw [← pow_add, Nat.sub_add_cancel (by omega)]
    have hpow_d : (2 : ℝ) ^ (N + 1 - d j) * (2 : ℝ) ^ (d j) = (2 : ℝ) ^ (N + 1) := by
      rw [← pow_add, Nat.sub_add_cancel (by have := hd_le_N j; omega)]
    have hscaled :
        (2 : ℝ) ^ (N + 1) * (((2 : ℝ) ^ p - 1) * (2 : ℝ) ^ (d j) * P root j) =
        (2 : ℝ) ^ (N + 1) * (2 : ℝ) ^ p := by
      calc (2 : ℝ) ^ (N + 1) * (((2 : ℝ) ^ p - 1) * (2 : ℝ) ^ (d j) * P root j)
          = ((2 : ℝ) ^ (N + 1) * P root j) * ((2 : ℝ) ^ p * (2 : ℝ) ^ (d j)) -
            (2 : ℝ) ^ (N + 1) * (2 : ℝ) ^ (d j) * P root j := by ring
        _ = ((2 : ℝ) ^ (N + 1 - p) * P root j + (2 : ℝ) ^ (N + 1 - d j)) *
              ((2 : ℝ) ^ p * (2 : ℝ) ^ (d j)) -
            (2 : ℝ) ^ (N + 1) * (2 : ℝ) ^ (d j) * P root j := by rw [hunroll]
        _ = ((2 : ℝ) ^ (N + 1 - p) * (2 : ℝ) ^ p) * ((2 : ℝ) ^ (d j) * P root j) +
            ((2 : ℝ) ^ (N + 1 - d j) * (2 : ℝ) ^ (d j)) * (2 : ℝ) ^ p -
            (2 : ℝ) ^ (N + 1) * (2 : ℝ) ^ (d j) * P root j := by ring
        _ = (2 : ℝ) ^ (N + 1) * (2 : ℝ) ^ p := by rw [hpow_p, hpow_d]; ring
    have hpos2 : (2 : ℝ) ^ (N + 1) ≠ 0 := by positivity
    have hcancel := mul_left_cancel₀ hpos2 hscaled
    have h2p_ge : 1 ≤ 2 ^ p := Nat.one_le_pow p 2 (by decide)
    have hrel_real : (A j : ℝ) * ((2 : ℝ) ^ p - 1) * (2 : ℝ) ^ (d j) = (D : ℝ) * (2 : ℝ) ^ p := by
      have hcast : ((A j * (2 ^ p - 1) * 2 ^ (d j) : ℕ) : ℝ) = ((D * 2 ^ p : ℕ) : ℝ) :=
        congrArg Nat.cast (hd j).2
      push_cast [Nat.cast_sub h2p_ge] at hcast
      exact hcast
    have hcoeff_pos : (0 : ℝ) < ((2 : ℝ) ^ p - 1) * (2 : ℝ) ^ (d j) := by
      have h2p_gt1 : (1 : ℝ) < (2 : ℝ) ^ p := by
        have : 2 ≤ 2 ^ p := by
          calc 2 = 2 ^ 1 := by norm_num
            _ ≤ 2 ^ p := Nat.pow_le_pow_right (by decide) (by omega)
        have : (2 : ℝ) ≤ (2 : ℝ) ^ p := by exact_mod_cast this
        linarith
      have h2d_pos : (0 : ℝ) < (2 : ℝ) ^ (d j) := by positivity
      exact mul_pos (by linarith) h2d_pos
    have hfinal : (((2 : ℝ) ^ p - 1) * (2 : ℝ) ^ (d j)) * ((D : ℝ) * P root j) =
        (((2 : ℝ) ^ p - 1) * (2 : ℝ) ^ (d j)) * (A j : ℝ) := by
      calc (((2 : ℝ) ^ p - 1) * (2 : ℝ) ^ (d j)) * ((D : ℝ) * P root j)
          = (D : ℝ) * (((2 : ℝ) ^ p - 1) * (2 : ℝ) ^ (d j) * P root j) := by ring
        _ = (D : ℝ) * (2 : ℝ) ^ p := by rw [hcancel]
        _ = (A j : ℝ) * ((2 : ℝ) ^ p - 1) * (2 : ℝ) ^ (d j) := hrel_real.symm
        _ = (((2 : ℝ) ^ p - 1) * (2 : ℝ) ^ (d j)) * (A j : ℝ) := by ring
    exact mul_left_cancel₀ (ne_of_gt hcoeff_pos) hfinal
  exact ⟨root, n, out, P, hn_abs, hP_eq, hP_z⟩

end PEqualNP.Outside.L_lib_870_aux

open PEqualNP.Outside.L_lib_870_aux in
theorem PEqualNP.Outside.L_lib_870 : (∀ (m D : ℕ) (A : Fin m → ℕ), 2 ≤ m → 0 < D → (∑ j, A j) = D →
  (∀ j, 0 < A j ∧ ∀ b : ℕ, ¬ D ∣ 2^b*A j) →
  let law := fun (s : ℕ) (z : Fin s) (n : Fin s → Bool → Option (Fin s))
      (out : Fin s → Bool → Fin m) (P : Fin s → Fin m → ℝ) =>
    (∃ pick : Fin s → Bool, ∀ i : Fin s,
      (fun x : Option (Fin s) => x.bind (fun h => n h (pick h)))^[s] (some i) = none) ∧
    (∀ i j, 2*P i j = ∑ bit : Bool, (n i bit).elim
      (if out i bit = j then (1 : ℝ) else 0) (fun k => P k j)) ∧
    ∀ j, (D : ℝ)*P z j = (A j : ℝ)
  let lengths := fun (p : ℕ) (d : Fin m → ℕ) =>
    2 ≤ p ∧ ∀ j, 0 < d j ∧ A j * (2^p-1) * 2^(d j) = D*2^p
  let hits := fun (s : ℕ) (z : Fin s) (n : Fin s → Bool → Option (Fin s))
      (out : Fin s → Bool → Fin m) (b : ℕ) (j : Fin m) =>
    ∑ w : Fin b → Bool, ((List.ofFn w).foldl
      (fun (x : Option (Fin s)) (bit : Bool) => x.bind (fun i => n i bit)) (some z)).elim 0
      (fun i => ((Finset.univ : Finset Bool).filter
        (fun bit => n i bit = none ∧ out i bit = j)).card)
  (∀ (s : ℕ) (z : Fin s) (n : Fin s → Bool → Option (Fin s))
      (out : Fin s → Bool → Fin m) (P : Fin s → Fin m → ℝ),
    law s z n out P → m ≤ s ∧ (s ≤ m →
      ∃ (p : ℕ) (d : Fin m → ℕ), lengths p d ∧ ∀ b j,
        hits s z n out b j = if d j ≤ b+1 ∧ p ∣ b+1-d j then 1 else 0)) ∧
  ((∃ (p : ℕ) (d : Fin m → ℕ), lengths p d) ↔
    ∃ (z : Fin m) (n : Fin m → Bool → Option (Fin m))
      (out : Fin m → Bool → Fin m) (P : Fin m → Fin m → ℝ), law m z n out P)) := by
  intro m D A hm hD hsumA hA law lengths hits
  refine ⟨?_, ?_⟩
  · intro s z n out P hlaw
    exact part1_main m D A hm hD hA s z n out P hlaw.1 hlaw.2.1 hlaw.2.2
  · constructor
    · rintro ⟨p, d, hp, hd⟩
      exact part2_converse m D A hm hD hsumA p d hp hd
    · rintro ⟨z, n, out, P, hlaw⟩
      obtain ⟨_, htight⟩ := part1_main m D A hm hD hA m z n out P hlaw.1 hlaw.2.1 hlaw.2.2
      obtain ⟨p, d, hlen, _⟩ := htight le_rfl
      exact ⟨p, d, hlen⟩
