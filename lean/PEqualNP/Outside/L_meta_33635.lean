import Mathlib.Tactic.Ring
import Mathlib.Data.List.FinRange
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Nat.ModEq
import Mathlib.Data.Int.Basic
import Mathlib.Data.List.OfFn
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.Fintype.Fin
import Mathlib.Tactic.FinCases
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_33635
namespace Builder
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

abbrev BitFn (n : Nat) := (Fin n → Bool) → Bool

structure Bank (n : Nat) where
  gates : List Gate
  fan : FanInTwo ⟨gates, 0⟩
  back : ReadsBack n ⟨gates, 0⟩

namespace Bank
variable {n : Nat}

def val (B : Bank n) (i : Nat) (x : Fin n → Bool) : Bool :=
  ((⟨B.gates, 0⟩ : Circuit).wires (List.ofFn x)).getD i false

def Has (B : Bank n) (f : BitFn n) : Prop :=
  ∃ i < n + B.gates.length, ∀ x, B.val i x = f x

def Ext (B D : Bank n) : Prop := ∀ {f}, B.Has f → D.Has f

def Grow (B : Bank n) (cost : Nat) (p : Bank n → Prop) : Prop :=
  ∃ D, B.Ext D ∧ D.gates.length ≤ B.gates.length + cost ∧ p D

def empty (n : Nat) : Bank n := ⟨[], by simp [FanInTwo], by simp [ReadsBack]⟩

lemma ext_refl (B : Bank n) : B.Ext B := fun h => h

lemma ext_trans {A B C : Bank n} (h1 : A.Ext B) (h2 : B.Ext C) : A.Ext C :=
  fun h => h2 (h1 h)

lemma input (i : Fin n) : (empty n).Has (fun x => x i) := by
  refine ⟨i, i.isLt, ?_⟩
  intro x
  simp [val, empty, Circuit.wires, List.getD_eq_getElem?_getD, i.isLt]

lemma Grow.pure (B : Bank n) {p : Bank n → Prop} (h : p B) : B.Grow 0 p :=
  ⟨B, fun h => h, by omega, h⟩

lemma Grow.weaken {B : Bank n} {p q : Bank n → Prop} {a b : Nat} (h : B.Grow a p)
    (hab : a ≤ b) (hpq : ∀ D, p D → q D) : B.Grow b q := by
  obtain ⟨D, e, c, t⟩ := h
  exact ⟨D, e, by omega, hpq D t⟩

lemma Grow.bind {B : Bank n} {p q : Bank n → Prop} {a b : Nat} (h : B.Grow a p)
    (f : ∀ D, B.Ext D → p D → D.Grow b q) : B.Grow (a + b) q := by
  obtain ⟨D, e, c, t⟩ := h
  obtain ⟨E, e', c', t'⟩ := f D e t
  exact ⟨E, fun h => e' (e h), by omega, t'⟩

private lemma wireLen (gs : List Gate) (x : List Bool) :
    ((⟨gs, 0⟩ : Circuit).wires x).length = x.length + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [Circuit.wires]
  | append_singleton gs g ih =>
    simp [Circuit.wires, List.foldl_append] at ih ⊢
    omega

private lemma gate (B : Bank n) (g : Gate)
    (ok : g.op ∈ ({GateOp.and, .or, .not} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (back : ∀ i ∈ g.inputs, i < n + B.gates.length) :
    B.Grow 1 (fun D => D.Has (fun x => g.op.eval (g.inputs.map fun i => B.val i x))) := by
  let D : Bank n :=
    { gates := B.gates ++ [g]
      fan := by
        intro g' h
        change g' ∈ B.gates ++ [g] at h
        rcases List.mem_append.mp h with h | h
        · exact B.fan g' h
        · simpa using (show g' = g from List.mem_singleton.mp h) ▸ ok
      back := by
        intro j hj w hw
        change j < (B.gates ++ [g]).length at hj
        change w ∈ ((B.gates ++ [g]).getD j _).inputs at hw
        by_cases h : j < B.gates.length
        · rw [List.getD_append _ _ _ _ h] at hw
          exact B.back j h w hw
        · have he : j = B.gates.length := by simp at hj; omega
          subst j
          simp at hw
          exact back w hw }
  have hv (x : Fin n → Bool) :
      ((⟨D.gates, 0⟩ : Circuit).wires (List.ofFn x)) =
        ((⟨B.gates, 0⟩ : Circuit).wires (List.ofFn x)) ++
        [g.op.eval (g.inputs.map fun i => B.val i x)] := by
    simp [D, val, Circuit.wires, List.foldl_append]
  have hl (x : Fin n → Bool) :
      ((⟨B.gates, 0⟩ : Circuit).wires (List.ofFn x)).length = n + B.gates.length := by
    simp [wireLen]
  refine ⟨D, ?_, by simp [D], n + B.gates.length, by simp [D], ?_⟩
  · intro f hf
    obtain ⟨i, hi, he⟩ := hf
    refine ⟨i, by simp [D]; omega, ?_⟩
    intro x
    unfold val
    rw [hv, List.getD_append _ _ _ _ (by rw [hl]; exact hi)]
    exact he x
  · intro x
    unfold val
    rw [hv, ← hl x]
    simp [val, List.getD_eq_getElem?_getD]

lemma const (B : Bank n) (b : Bool) : B.Grow 1 (fun D => D.Has (fun _ => b)) := by
  cases b with
  | false => simpa [GateOp.eval] using B.gate ⟨.or, []⟩ (by simp) (by simp)
  | true => simpa [GateOp.eval] using B.gate ⟨.and, []⟩ (by simp) (by simp)

lemma inv {B : Bank n} {f : BitFn n} (a : B.Has f) :
    B.Grow 1 (fun D => D.Has (fun x => !(f x))) := by
  obtain ⟨i, hi, he⟩ := a
  simpa [GateOp.eval, he] using B.gate ⟨.not, [i]⟩ (by simp) (by simpa using hi)

lemma meet {B : Bank n} {f g : BitFn n} (a : B.Has f) (b : B.Has g) :
    B.Grow 1 (fun D => D.Has (fun x => f x && g x)) := by
  obtain ⟨i, hi, he⟩ := a
  obtain ⟨j, hj, hf⟩ := b
  simpa [GateOp.eval, he, hf] using B.gate ⟨.and, [i, j]⟩ (by simp) (by simp [hi, hj])

lemma join {B : Bank n} {f g : BitFn n} (a : B.Has f) (b : B.Has g) :
    B.Grow 1 (fun D => D.Has (fun x => f x || g x)) := by
  obtain ⟨i, hi, he⟩ := a
  obtain ⟨j, hj, hf⟩ := b
  simpa [GateOp.eval, he, hf] using B.gate ⟨.or, [i, j]⟩ (by simp) (by simp [hi, hj])

lemma xor2 {B : Bank n} {f g : BitFn n} (a : B.Has f) (b : B.Has g) :
    B.Grow 4 (fun D => D.Has (fun x => xor (f x) (g x))) := by
  apply (meet a b).bind (b := 3)
  intro C e hab
  apply (inv hab).bind (b := 2)
  intro D e' hn
  apply (join (e' (e a)) (e' (e b))).bind (b := 1)
  intro E e'' hor
  apply (meet hor (e'' hn)).weaken (le_refl _)
  intro F h
  have eq (x) : ((f x || g x) && !(f x && g x)) = xor (f x) (g x) := by
    cases f x <;> cases g x <;> decide
  simpa only [eq] using h

lemma mux {B : Bank n} {c f g : BitFn n} (hc : B.Has c) (hf : B.Has f) (hg : B.Has g) :
    B.Grow 4 (fun D => D.Has (fun x => if c x then f x else g x)) := by
  apply (inv hc).bind (b := 3)
  intro C e hnc
  apply (meet (e hc) (e hf)).bind (b := 2)
  intro D e' h1
  apply (meet (e' hnc) (e' (e hg))).bind (b := 1)
  intro E e'' h2
  apply (join (e'' h1) h2).weaken (le_refl _)
  intro F h
  have eq (x) : ((c x && f x) || (!c x && g x)) = (if c x then f x else g x) := by
    cases c x <;> cases f x <;> cases g x <;> decide
  simpa only [eq] using h

lemma xorConst {B : Bank n} {f : BitFn n} (a : B.Has f) (b : Bool) :
    B.Grow 1 (fun D => D.Has (fun x => xor (f x) b)) := by
  cases b with
  | false =>
    exact (Grow.pure B a).weaken (by omega) (fun _ t => by simpa using t)
  | true => simpa using inv a

lemma eqBool {B : Bank n} {f g : BitFn n} (a : B.Has f) (b : B.Has g) :
    B.Grow 5 (fun D => D.Has (fun x => f x == g x)) := by
  apply (xor2 a b).bind (b := 1)
  intro C _ hx
  apply (inv hx).weaken (le_refl _)
  intro D h
  have hfn : (fun x => !(xor (f x) (g x))) = fun x => f x == g x := by
    funext x; cases f x <;> cases g x <;> decide
  rwa [hfn] at h

lemma foldGrow {α σ : Type} (B : Bank n) (l : List α) (s0 : σ)
    (step : σ → α → σ) (Inv : σ → Bank n → Prop) (cost : Nat)
    (h0 : Inv s0 B)
    (hstep : ∀ D, B.Ext D → ∀ s a, a ∈ l → Inv s D → D.Grow cost (Inv (step s a))) :
    B.Grow (l.length * cost) (Inv (l.foldl step s0)) := by
  induction l generalizing B s0 with
  | nil => simpa using Grow.pure B h0
  | cons a l ih =>
    have h1 : B.Grow cost (Inv (step s0 a)) := hstep B (fun h => h) s0 a (by simp) h0
    have h2 := h1.bind (b := l.length * cost) (fun D e hInv =>
      ih D (step s0 a) hInv (fun E e' s x hx =>
        hstep E (fun h => e' (e h)) s x (by simp [hx])))
    simpa [List.foldl_cons, Nat.succ_mul, Nat.add_comm] using h2

lemma collect {α : Type} (B : Bank n) (l : List α) (f : α → BitFn n) (cost : Nat)
    (emit : ∀ D : Bank n, B.Ext D → ∀ i ∈ l, D.Grow cost (fun E => E.Has (f i))) :
    B.Grow (l.length * cost) (fun D => ∀ i ∈ l, D.Has (f i)) := by
  induction l with
  | nil => simpa using (Grow.pure B (p := fun D => ∀ i ∈ ([] : List α), D.Has (f i)) (by simp))
  | cons a l ih =>
    have t := ih (fun D e i hi => emit D e i (by simp [hi]))
    have out := t.bind (b := cost) (q := fun E => ∀ i ∈ a :: l, E.Has (f i)) (by
      intro D e haveL
      obtain ⟨E, e', c', ha⟩ := emit D e a (by simp)
      refine ⟨E, e', c', ?_⟩
      intro i hi
      rcases List.mem_cons.mp hi with rfl | h
      · exact ha
      · exact e' (haveL i h))
    simpa [Nat.succ_mul] using out

lemma collectFin (B : Bank n) (m : Nat) (f : Fin m → BitFn n) (cost : Nat)
    (emit : ∀ D : Bank n, B.Ext D → ∀ i, D.Grow cost (fun E => E.Has (f i))) :
    B.Grow (m * cost) (fun D => ∀ i, D.Has (f i)) := by
  simpa using B.collect (List.finRange m) f cost (fun D e i _ => emit D e i)

private lemma foldl_apply {α β γ : Type} (op : γ → α → β → γ) (init : β → γ)
    (l : List α) (x : β) :
    (l.foldl (fun acc a y => op (acc y) a y) init) x =
      l.foldl (fun acc a => op acc a x) (init x) := by
  induction l generalizing init with
  | nil => rfl
  | cons a l ih => simp only [List.foldl_cons, ih]

lemma xorList {α : Type} (B : Bank n) (l : List α) (f : α → BitFn n)
    (hf : ∀ a ∈ l, B.Has (f a)) :
    B.Grow (1 + l.length * 4)
      (fun D => D.Has (fun x => l.foldl (fun acc a => xor acc (f a x)) false)) := by
  apply (B.const false).bind (b := l.length * 4)
  intro C e hc
  have hg := foldGrow C l (fun _ => false) (fun acc a x => xor (acc x) (f a x))
    (fun acc D => D.Has acc) 4 hc (fun D e' acc a ha hacc =>
      xor2 hacc (e' (e (hf a ha))))
  refine hg.weaken (le_refl _) (fun D hD => ?_)
  have hfn : l.foldl (fun acc a x => xor (acc x) (f a x)) (fun _ => false) =
      fun x => l.foldl (fun acc a => xor acc (f a x)) false :=
    funext (foldl_apply (fun acc a x => xor acc (f a x)) (fun _ => false) l)
  rwa [hfn] at hD

lemma orList {α : Type} (B : Bank n) (l : List α) (f : α → BitFn n)
    (hf : ∀ a ∈ l, B.Has (f a)) :
    B.Grow (1 + l.length * 1)
      (fun D => D.Has (fun x => l.foldl (fun acc a => acc || f a x) false)) := by
  apply (B.const false).bind (b := l.length * 1)
  intro C e hc
  have hg := foldGrow C l (fun _ => false) (fun acc a x => acc x || f a x)
    (fun acc D => D.Has acc) 1 hc (fun D e' acc a ha hacc =>
      join hacc (e' (e (hf a ha))))
  refine hg.weaken (le_refl _) (fun D hD => ?_)
  have hfn : l.foldl (fun acc a x => acc x || f a x) (fun _ => false) =
      fun x => l.foldl (fun acc a => acc || f a x) false :=
    funext (foldl_apply (fun acc a x => acc || f a x) (fun _ => false) l)
  rwa [hfn] at hD

lemma andList {α : Type} (B : Bank n) (l : List α) (f : α → BitFn n)
    (hf : ∀ a ∈ l, B.Has (f a)) :
    B.Grow (1 + l.length * 1)
      (fun D => D.Has (fun x => l.foldl (fun acc a => acc && f a x) true)) := by
  apply (B.const true).bind (b := l.length * 1)
  intro C e hc
  have hg := foldGrow C l (fun _ => true) (fun acc a x => acc x && f a x)
    (fun acc D => D.Has acc) 1 hc (fun D e' acc a ha hacc =>
      meet hacc (e' (e (hf a ha))))
  refine hg.weaken (le_refl _) (fun D hD => ?_)
  have hfn : l.foldl (fun acc a x => acc x && f a x) (fun _ => true) =
      fun x => l.foldl (fun acc a => acc && f a x) true :=
    funext (foldl_apply (fun acc a x => acc && f a x) (fun _ => true) l)
  rwa [hfn] at hD

lemma finish {f : BitFn n} {b : Nat} (h : (empty n).Grow b (fun B => B.Has f)) :
    ∃ C : Circuit, FanInTwo C ∧ ReadsBack n C ∧ C.size ≤ b ∧
      ∀ bits, C.eval (List.ofFn bits) = f bits := by
  obtain ⟨B, _, budget, i, _, he⟩ := h
  exact ⟨⟨B.gates, i⟩, B.fan, B.back, by simpa [Circuit.size, empty] using budget, he⟩

end Bank
end Builder
end PEqualNP.Outside.L_meta_33635

namespace PEqualNP.Outside.L_meta_33635.ScheduledTrace

open scoped BigOperators

variable {S R : Type*} [Fintype S] [DecidableEq S]

def transfer [Semiring R] (T : ℕ → Matrix S S R) : ℕ → Matrix S S R
  | 0 => 1
  | q+1 => T 0 * transfer (fun i => T (i+1)) q

theorem transfer_eq_list_prod [Semiring R] (T : ℕ → Matrix S S R) (q : ℕ) :
    transfer T q = (List.ofFn (fun i : Fin q => T i.val)).prod := by
  induction q generalizing T with
  | zero => simp [transfer]
  | succ q ih =>
    simp only [transfer, List.ofFn_succ, List.prod_cons]
    rw [ih]
    rfl

def endpoint : (q : ℕ) → S → (Fin q → S) → S
  | 0, a, _ => a
  | q+1, _, w => endpoint q (w 0) (Fin.tail w)

def pathWeight [Semiring R] (T : ℕ → Matrix S S R) :
    (q : ℕ) → S → (Fin q → S) → R
  | 0, _, _ => 1
  | q+1, a, w => T 0 a (w 0) * pathWeight (fun i => T (i+1)) q (w 0) (Fin.tail w)

omit [DecidableEq S] in
theorem sum_cons [AddCommMonoid R] (q : ℕ) (f : (Fin (q+1) → S) → R) :
    (∑ w, f w) = ∑ a, ∑ w : Fin q → S, f (Fin.cons a w) := by
  rw [← (Fin.consEquiv (fun _ : Fin (q+1) => S)).sum_comp f]
  simp only [Fintype.sum_prod_type, Fin.consEquiv_apply]

theorem transfer_apply [Semiring R] (T : ℕ → Matrix S S R)
    (q : ℕ) (a b : S) :
    transfer T q a b = ∑ w : Fin q → S,
      pathWeight T q a w * (if endpoint q a w = b then 1 else 0) := by
  induction q generalizing T a with
  | zero => by_cases h : a = b <;> simp [transfer, pathWeight, endpoint, Matrix.one_apply, h]
  | succ q ih =>
    rw [transfer, Matrix.mul_apply, sum_cons]
    simp only [pathWeight, endpoint, Fin.cons_zero, Fin.tail_cons]
    simp_rw [ih, Finset.mul_sum, mul_assoc]

theorem trace_closed_paths [Semiring R] (T : ℕ → Matrix S S R) (q : ℕ) :
    Matrix.trace (transfer T q) = ∑ a : S, ∑ w : Fin q → S,
      pathWeight T q a w * (if endpoint q a w = a then 1 else 0) := by
  simp only [Matrix.trace, Matrix.diag, transfer_apply]

def validPath (edge : ℕ → S → S → Bool) : (q : ℕ) → S → (Fin q → S) → Bool
  | 0, _, _ => true
  | q+1, a, w => edge 0 a (w 0) && validPath (fun i => edge (i+1)) q (w 0) (Fin.tail w)

def pathParity (label : ℕ → S → S → Bool) : (q : ℕ) → S → (Fin q → S) → Bool
  | 0, _, _ => false
  | q+1, a, w => xor (label 0 a (w 0))
      (pathParity (fun i => label (i+1)) q (w 0) (Fin.tail w))

def adjacency (edge : ℕ → S → S → Bool) (i : ℕ) : Matrix S S ℕ :=
  fun a b => if edge i a b then 1 else 0

omit [Fintype S] [DecidableEq S] in
theorem adjacency_pathWeight (edge : ℕ → S → S → Bool) (q : ℕ)
    (a : S) (w : Fin q → S) :
    pathWeight (adjacency edge) q a w = if validPath edge q a w then 1 else 0 := by
  induction q generalizing edge a with
  | zero => rfl
  | succ q ih =>
    simp only [pathWeight, validPath]
    change (if edge 0 a (w 0) then 1 else 0) *
      pathWeight (adjacency (fun i => edge (i+1))) q (w 0) (Fin.tail w) = _
    rw [ih]
    by_cases h : edge 0 a (w 0) = true
    · simp [h]
    · have hf : edge 0 a (w 0) = false := Bool.eq_false_iff.mpr h
      simp [hf]

theorem transfer_count (edge : ℕ → S → S → Bool) (q : ℕ) (a b : S) :
    transfer (adjacency edge) q a b =
      (Finset.univ.filter fun w : Fin q → S =>
        validPath edge q a w = true ∧ endpoint q a w = b).card := by
  classical
  rw [transfer_apply, Finset.card_filter]
  apply Finset.sum_congr rfl
  intro w _
  rw [adjacency_pathWeight]
  cases validPath edge q a w <;> by_cases he : endpoint q a w = b <;> simp [he]

theorem trace_count_closed (edge : ℕ → S → S → Bool) (q : ℕ) :
    Matrix.trace (transfer (adjacency edge) q) =
      ∑ a : S, (Finset.univ.filter fun w : Fin q → S =>
        validPath edge q a w = true ∧ endpoint q a w = a).card := by
  classical
  simp only [Matrix.trace, Matrix.diag, transfer_count]

def parityDP (edge label : ℕ → S → S → Bool) : ℕ → S → S → Bool → ℕ
  | 0, a, b, parity => if a = b ∧ parity = false then 1 else 0
  | q+1, a, b, parity => ∑ v : S, if edge 0 a v then
      parityDP (fun i => edge (i+1)) (fun i => label (i+1)) q v b
        (xor (label 0 a v) parity) else 0

theorem parityDP_count (edge label : ℕ → S → S → Bool) (q : ℕ)
    (a b : S) (parity : Bool) :
    parityDP edge label q a b parity =
      (Finset.univ.filter fun w : Fin q → S =>
        validPath edge q a w = true ∧ endpoint q a w = b ∧
        pathParity label q a w = parity).card := by
  classical
  induction q generalizing edge label a parity with
  | zero =>
    cases parity <;> by_cases h : a = b <;>
      simp [parityDP, validPath, endpoint, pathParity, h]
  | succ q ih =>
    rw [Finset.card_filter, sum_cons]
    simp only [parityDP, validPath, endpoint, pathParity, Fin.cons_zero, Fin.tail_cons]
    apply Finset.sum_congr rfl
    intro v _
    rw [ih, Finset.card_filter]
    by_cases hv : edge 0 a v = true
    · simp only [hv, Bool.true_and, ↓reduceIte]
      apply Finset.sum_congr rfl
      intro w _
      cases label 0 a v <;>
        cases pathParity (fun i => label (i+1)) q v w <;> cases parity <;> simp
    · have hf : edge 0 a v = false := Bool.eq_false_iff.mpr hv
      simp [hf]

def signedAdjacency (edge label : ℕ → S → S → Bool) (i : ℕ) : Matrix S S ℤ :=
  fun a b => if edge i a b then (if label i a b then -1 else 1) else 0

theorem signed_transfer_eq_parity (edge label : ℕ → S → S → Bool)
    (q : ℕ) (a b : S) :
    transfer (signedAdjacency edge label) q a b =
      (parityDP edge label q a b false : ℤ) - parityDP edge label q a b true := by
  induction q generalizing edge label a with
  | zero => by_cases h : a = b <;> simp [transfer, Matrix.one_apply, parityDP, h]
  | succ q ih =>
    simp only [transfer, Matrix.mul_apply, parityDP, Nat.cast_sum]
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro v _
    change signedAdjacency edge label 0 a v *
      transfer (signedAdjacency (fun i => edge (i+1)) (fun i => label (i+1))) q v b = _
    rw [ih]
    cases he : edge 0 a v <;> cases hl : label 0 a v <;>
      simp [signedAdjacency, he, hl, sub_eq_add_neg, add_comm]

theorem trace_parity_difference (edge label : ℕ → S → S → Bool) (q : ℕ) :
    Matrix.trace (transfer (signedAdjacency edge label) q) =
      ((∑ a : S, parityDP edge label q a a false : ℕ) : ℤ) -
        (∑ a : S, parityDP edge label q a a true : ℕ) := by
  simp only [Matrix.trace, Matrix.diag, signed_transfer_eq_parity,
    Nat.cast_sum, Finset.sum_sub_distrib]

abbrev ClosedPath (edge : ℕ → S → S → Bool) (q : ℕ) :=
  {p : S × (Fin q → S) // validPath edge q p.1 p.2 = true ∧ endpoint q p.1 p.2 = p.1}

abbrev ParityClosedPath (edge label : ℕ → S → S → Bool) (q : ℕ) (parity : Bool) :=
  {p : S × (Fin q → S) // validPath edge q p.1 p.2 = true ∧
    endpoint q p.1 p.2 = p.1 ∧ pathParity label q p.1 p.2 = parity}

theorem trace_eq_closed_card (edge : ℕ → S → S → Bool) (q : ℕ) :
    Matrix.trace (transfer (adjacency edge) q) = Fintype.card (ClosedPath edge q) := by
  classical
  rw [trace_count_closed]
  unfold ClosedPath
  rw [Fintype.card_subtype, Finset.card_filter, Fintype.sum_prod_type]
  simp only [Finset.card_filter]

theorem parityDP_closed_card (edge label : ℕ → S → S → Bool) (q : ℕ) (parity : Bool) :
    (∑ a : S, parityDP edge label q a a parity) =
      Fintype.card (ParityClosedPath edge label q parity) := by
  classical
  unfold ParityClosedPath
  rw [Fintype.card_subtype, Finset.card_filter, Fintype.sum_prod_type]
  simp only [parityDP_count, Finset.card_filter]

theorem trace_count_of_equiv {W : Type*} [Fintype W]
    (edge : ℕ → S → S → Bool) (q : ℕ) (e : W ≃ ClosedPath edge q) :
    Matrix.trace (transfer (adjacency edge) q) = Fintype.card W := by
  rw [trace_eq_closed_card]
  exact Fintype.card_congr e.symm

theorem trace_parity_of_equiv {W : Bool → Type*} [∀ b, Fintype (W b)]
    (edge label : ℕ → S → S → Bool) (q : ℕ)
    (e : ∀ b, W b ≃ ParityClosedPath edge label q b) :
    Matrix.trace (transfer (signedAdjacency edge label) q) =
      (Fintype.card (W false) : ℤ) - Fintype.card (W true) := by
  rw [trace_parity_difference, parityDP_closed_card, parityDP_closed_card,
    Fintype.card_congr (e false).symm, Fintype.card_congr (e true).symm]

end PEqualNP.Outside.L_meta_33635.ScheduledTrace

namespace PEqualNP.Outside.L_meta_33635.Compiler
open Builder

abbrev Env (n : ℕ) := Fin n → Bool
def HasWord {n : ℕ} (B : Bank n) (w : ℕ) (f : Env n → ℕ) : Prop :=
  ∀ i : Fin w, B.Has (fun x => (f x).testBit i.val)

theorem keep {n w : ℕ} {A B : Bank n} (h : A.Ext B) {f : Env n → ℕ}
    (hf : HasWord A w f) : HasWord B w f := fun i => h (hf i)

private lemma has_congr {n : ℕ} {B : Bank n} {f g : BitFn n}
    (hf : B.Has f) (h : ∀ x, f x=g x) : B.Has g := by
  simpa only [show f=g from funext h] using hf

private theorem majority {n : ℕ} {B : Bank n} {a b c : BitFn n}
    (ha : B.Has a) (hb : B.Has b) (hc : B.Has c) :
    B.Grow 5 (fun E => E.Has (fun x => Bool.atLeastTwo (a x) (b x) (c x))) := by
  obtain ⟨A,eA,kA,hab⟩ := Bank.meet ha hb
  obtain ⟨C,eC,kC,hac⟩ := Bank.meet (eA ha) (eA hc)
  obtain ⟨D,eD,kD,hbc⟩ := Bank.meet (eC (eA hb)) (eC (eA hc))
  obtain ⟨E,eE,kE,h1⟩ := Bank.join (eD (eC hab)) (eD hac)
  obtain ⟨F,eF,kF,h2⟩ := Bank.join h1 (eE hbc)
  exact ⟨F, fun h => eF (eE (eD (eC (eA h)))), by omega, h2⟩

private def carry (w i a b : ℕ) : Bool :=
  BitVec.carry i (BitVec.ofNat w a) (BitVec.ofNat w b) false

private lemma carry_succ {w i : ℕ} (hi : i<w) (a b : ℕ) :
    carry w (i+1) a b = Bool.atLeastTwo (a.testBit i) (b.testBit i) (carry w i a b) := by
  simp only [carry, BitVec.carry_succ, BitVec.getLsbD_ofNat, hi, decide_true, Bool.true_and]

private lemma digit_add {w i : ℕ} (hi : i<w) (a b : ℕ) :
    (a+b).testBit i = xor (a.testBit i) (xor (b.testBit i) (carry w i a b)) := by
  have h := BitVec.getLsbD_add hi (BitVec.ofNat w a) (BitVec.ofNat w b)
  rw [← BitVec.ofNat_add] at h
  simpa only [BitVec.getLsbD_ofNat, hi, decide_true, Bool.true_and, carry] using h

private theorem carry_prefix {n w : ℕ} (B : Bank n) (hz : B.Has (fun _ => false))
    (a b : Env n → ℕ) (ha : HasWord B w a) (hb : HasWord B w b) (t : ℕ) (ht : t≤w) :
    B.Grow (t*5) (fun D => ∀ i ≤ t, D.Has (fun x => carry w i (a x) (b x))) := by
  induction t with
  | zero =>
    refine ⟨B, Bank.ext_refl B, by simp, ?_⟩
    intro i hi
    obtain rfl : i=0 := by omega
    simpa [carry] using hz
  | succ t ih =>
    have hlt : t<w := by omega
    obtain ⟨D,eD,kD,hD⟩ := ih (by omega)
    obtain ⟨E,eE,kE,hc⟩ := majority (eD (ha ⟨t,hlt⟩)) (eD (hb ⟨t,hlt⟩)) (hD t (by omega))
    refine ⟨E, Bank.ext_trans eD eE, by rw [Nat.succ_mul]; omega, ?_⟩
    intro i hu
    by_cases hh : i≤t
    · exact eE (hD i hh)
    · obtain rfl : i=t+1 := by omega
      exact has_congr hc (fun x => (carry_succ hlt (a x) (b x)).symm)

theorem addWord {n w : ℕ} (B : Bank n) (hz : B.Has (fun _ => false))
    (a b : Env n → ℕ) (ha : HasWord B w a) (hb : HasWord B w b) :
    B.Grow (w*13) (fun D => HasWord D w (fun x => a x + b x)) := by
  obtain ⟨C,eC,kC,hc⟩ := carry_prefix B hz a b ha hb w (le_refl _)
  obtain ⟨D,eD,kD,hs⟩ := C.collectFin w (fun i x => (a x+b x).testBit i.val) 8 (by
    intro E e i
    obtain ⟨F,eF,kF,h1⟩ := Bank.xor2 (e (eC (hb i))) (e (hc _ i.isLt.le))
    obtain ⟨G,eG,kG,h2⟩ := Bank.xor2 (eF (e (eC (ha i)))) h1
    exact ⟨G, Bank.ext_trans eF eG, by omega,
      has_congr h2 (fun x => (digit_add i.isLt (a x) (b x)).symm)⟩)
  exact ⟨D, Bank.ext_trans eC eD, by omega, hs⟩

theorem muxWord {n w : ℕ} (B : Bank n) (f : BitFn n) (a b : Env n → ℕ)
    (hf : B.Has f) (ha : HasWord B w a) (hb : HasWord B w b) :
    B.Grow (w*4) (fun D => HasWord D w (fun x => if f x then a x else b x)) := by
  apply B.collectFin w _ 4
  intro C e i
  apply (Bank.mux (e hf) (e (ha i)) (e (hb i))).weaken (le_refl _)
  intro D hD
  exact has_congr hD (fun x => by cases h : f x <;> simp [h])

theorem constWord {n w : ℕ} (B : Bank n) (hz : B.Has (fun _ => false))
    (ho : B.Has (fun _ => true)) (c : ℕ) : HasWord B w (fun _ => c) := by
  intro i
  cases h : c.testBit i.val
  · simpa only [h] using hz
  · simpa only [h] using ho

theorem sumWords {n w : ℕ} {α : Type*} [DecidableEq α] (B : Bank n)
    (hz : B.Has (fun _ => false)) (ho : B.Has (fun _ => true))
    (U : Finset α) (val : α → Env n → ℕ) (cost : ℕ)
    (emit : ∀ j ∈ U, ∀ D, B.Ext D → D.Grow cost (fun E => HasWord E w (val j))) :
    B.Grow (U.card*(cost+w*13)) (fun E => HasWord E w (fun x => ∑ j ∈ U, val j x)) := by
  induction U using Finset.induction_on with
  | empty =>
    simpa using Bank.Grow.pure B (constWord (w:=w) B hz ho 0)
  | @insert j U hj ih =>
    obtain ⟨D,eD,kD,hU⟩ := ih (fun a ha => emit a (Finset.mem_insert_of_mem ha))
    obtain ⟨E,eE,kE,hj'⟩ := emit j (Finset.mem_insert_self _ _) D eD
    obtain ⟨F,eF,kF,hF⟩ := addWord E (eE (eD hz)) (val j) _ hj' (keep eE hU)
    refine ⟨F, Bank.ext_trans eD (Bank.ext_trans eE eF), ?_, ?_⟩
    · rw [Finset.card_insert_of_notMem hj, Nat.succ_mul]
      omega
    · simpa [Finset.sum_insert hj] using hF

end PEqualNP.Outside.L_meta_33635.Compiler

namespace PEqualNP.Outside.L_meta_33635.Compiler
open Builder

private theorem gather {n w : ℕ} {α : Type*} [DecidableEq α] (B : Bank n)
    (U : Finset α) (f : α → Env n → ℕ) (cost : ℕ)
    (emit : ∀ j ∈ U, ∀ D, B.Ext D → D.Grow cost (fun E => HasWord E w (f j))) :
    B.Grow (U.card*cost) (fun E => ∀ j ∈ U, HasWord E w (f j)) := by
  induction U using Finset.induction_on with
  | empty => exact ⟨B, Bank.ext_refl B, by simp, by simp⟩
  | @insert j U hj ih =>
    obtain ⟨D,eD,kD,hD⟩ := ih (fun i hi => emit i (Finset.mem_insert_of_mem hi))
    obtain ⟨E,eE,kE,he⟩ := emit j (Finset.mem_insert_self _ _) D eD
    refine ⟨E, Bank.ext_trans eD eE, ?_, ?_⟩
    · rw [Finset.card_insert_of_notMem hj, Nat.succ_mul]
      omega
    · intro a ha
      rcases Finset.mem_insert.mp ha with rfl|hu
      · exact he
      · exact keep eE (hD a hu)

abbrev Edge (D : ℕ) := ℕ → Fin D → Fin D → Bool
abbrev Labels (n D : ℕ) := Env n → Edge D

private theorem oneCell {n D w : ℕ} (B : Bank n)
    (hz : B.Has (fun _ => false)) (ho : B.Has (fun _ => true))
    (edge : Edge D) (label : Labels n D) (q : ℕ)
    (hl : ∀ a v, B.Has (fun x => label x 0 a v))
    (prev : ∀ v b p, HasWord B w (fun x =>
      ScheduledTrace.parityDP (fun i => edge (i+1)) (fun i => label x (i+1)) q v b p))
    (a b : Fin D) (p : Bool) :
    B.Grow (D*(w*4+w*13)) (fun E => HasWord E w (fun x =>
      ScheduledTrace.parityDP edge (label x) (q+1) a b p)) := by
  let T (v : Fin D) (p' : Bool) (x : Env n) :=
    ScheduledTrace.parityDP (fun i => edge (i+1)) (fun i => label x (i+1)) q v b p'
  let term (v : Fin D) (x : Env n) :=
    if edge 0 a v then T v (xor (label x 0 a v) p) x else 0
  have hsum := sumWords (w:=w) B hz ho Finset.univ term (w*4) (by
    intro v _ C e
    cases he : edge 0 a v
    · have hz' := constWord (w:=w) C (e hz) (e ho) 0
      exact (Bank.Grow.pure C hz').weaken (Nat.zero_le _) (fun _ z => by simpa [term, he] using z)
    · apply (muxWord C (fun x => label x 0 a v) (T v (!p)) (T v p)
          (e (hl a v)) (keep e (prev v b (!p))) (keep e (prev v b p))).weaken (le_refl _)
      intro E hm
      have eqfn : (fun x => if label x 0 a v then T v (!p) x else T v p x) = term v := by
        funext x
        cases hlv : label x 0 a v <;> cases p <;> simp [term, he, hlv]
      rwa [← eqfn])
  simpa [term, T, ScheduledTrace.parityDP] using hsum

def layerCost (D w : ℕ) : ℕ := (D*(D*2))*(D*(w*4+w*13))

theorem compileParityDP {n D w : ℕ} (B : Bank n)
    (hz : B.Has (fun _ => false)) (ho : B.Has (fun _ => true))
    (edge : Edge D) (label : Labels n D) (q : ℕ)
    (hl : ∀ i, i<q → ∀ a v, B.Has (fun x => label x i a v)) :
    B.Grow (q*layerCost D w) (fun E => ∀ a b p, HasWord E w
      (fun x => ScheduledTrace.parityDP edge (label x) q a b p)) := by
  induction q generalizing edge label with
  | zero =>
    refine ⟨B, Bank.ext_refl B, by simp, ?_⟩
    intro a b p
    exact constWord B hz ho (if a=b ∧ p=false then 1 else 0)
  | succ q ih =>
    obtain ⟨C,eC,kC,prev⟩ := ih (fun i => edge (i+1)) (fun x i => label x (i+1))
      (fun i hi => hl (i+1) (by omega))
    let cells := Fin D × Fin D × Bool
    let f (j : cells) (x : Env n) := ScheduledTrace.parityDP edge (label x) (q+1) j.1 j.2.1 j.2.2
    obtain ⟨K,eK,kK,out⟩ := gather (w:=w) C (Finset.univ : Finset cells) f (D*(w*4+w*13)) (by
      intro j _ E e
      exact oneCell E (e (eC hz)) (e (eC ho)) edge label q
        (fun a v => e (eC (hl 0 (Nat.succ_pos _) a v)))
        (fun v b p => keep e (prev v b p)) j.1 j.2.1 j.2.2)
    have hk : K.gates.length ≤ C.gates.length + layerCost D w := by
      simpa [cells, layerCost, Fintype.card_prod] using kK
    refine ⟨K, Bank.ext_trans eC eK, by rw [Nat.succ_mul]; omega, ?_⟩
    exact fun a b p => out (a,b,p) (Finset.mem_univ _)

theorem closedParity {n D w : ℕ} (B : Bank n)
    (hz : B.Has (fun _ => false)) (ho : B.Has (fun _ => true))
    (edge : Edge D) (label : Labels n D) (q : ℕ)
    (hl : ∀ i, i<q → ∀ a v, B.Has (fun x => label x i a v)) :
    B.Grow (q*layerCost D w + 2*(D*(w*13))) (fun E => ∀ p : Bool, HasWord E w
      (fun x => ∑ a : Fin D, ScheduledTrace.parityDP edge (label x) q a a p)) := by
  obtain ⟨C,eC,kC,table⟩ := compileParityDP B hz ho edge label q hl
  let f (p : Bool) (x : Env n) := ∑ a : Fin D, ScheduledTrace.parityDP edge (label x) q a a p
  obtain ⟨K,eK,kK,out⟩ := gather (w:=w) C Finset.univ f (D*(w*13)) (by
    intro p _ E e
    have z := sumWords (w:=w) E (e (eC hz)) (e (eC ho)) Finset.univ
      (fun a x => ScheduledTrace.parityDP edge (label x) q a a p) 0 (by
        intro a _ F eF
        exact Bank.Grow.pure F (keep eF (keep e (table a a p))))
    simpa [f] using z)
  refine ⟨K, Bank.ext_trans eC eK, ?_, fun p => out p (Finset.mem_univ _)⟩
  simp at kK
  omega

end PEqualNP.Outside.L_meta_33635.Compiler

namespace PEqualNP.Outside.L_meta_33635.Compiler
open Builder

theorem aggregateColors {n w : ℕ} {α : Type*} [DecidableEq α] (B : Bank n)
    (hz : B.Has (fun _ => false)) (ho : B.Has (fun _ => true))
    (colors : Finset α) (tag : α → BitFn n) (counts : α → Bool → Env n → ℕ)
    (cost : ℕ) (emit : ∀ c ∈ colors, ∀ C, B.Ext C →
      C.Grow cost (fun E => E.Has (tag c) ∧ ∀ p, HasWord E w (counts c p))) :
    B.Grow (colors.card*(cost+2*(w*4+w*13))) (fun E => ∀ p : Bool, HasWord E w
      (fun x => ∑ c ∈ colors, counts c (xor (tag c x) p) x)) := by
  induction colors using Finset.induction_on with
  | empty =>
    refine ⟨B, Bank.ext_refl B, by simp, ?_⟩
    intro p
    simpa using constWord (w:=w) B hz ho 0
  | @insert c colors hc ih =>
    obtain ⟨C,eC,kC,prev⟩ := ih (fun v hv => emit v (Finset.mem_insert_of_mem hv))
    obtain ⟨E,eE,kE,htag,hs⟩ := emit c (Finset.mem_insert_self _ _) C eC
    let f (p : Bool) (x : Env n) :=
      counts c (xor (tag c x) p) x + ∑ z ∈ colors, counts z (xor (tag z x) p) x
    obtain ⟨K,eK,kK,out⟩ := gather (w:=w) E Finset.univ f (w*4+w*13) (by
      intro p _ J e
      obtain ⟨A,eA,kA,hm⟩ := muxWord J (tag c) (counts c (!p)) (counts c p)
        (e htag) (keep e (hs (!p))) (keep e (hs p))
      have heq : (fun x => if tag c x then counts c (!p) x else counts c p x) =
          fun x => counts c (xor (tag c x) p) x := by
        funext x
        cases tag c x <;> cases p <;> simp
      rw [heq] at hm
      obtain ⟨A',ee,kk,hw⟩ := addWord A (eA (e (eE (eC hz)))) _ _ hm
        (keep eA (keep e (keep eE (prev p))))
      exact ⟨A', Bank.ext_trans eA ee, by omega, hw⟩)
    refine ⟨K, Bank.ext_trans eC (Bank.ext_trans eE eK), ?_, ?_⟩
    · rw [Finset.card_insert_of_notMem hc, Nat.succ_mul]
      simp only [Finset.card_univ, Fintype.card_bool] at kK
      omega
    · intro p
      simpa [f, Finset.sum_insert hc] using out p (Finset.mem_univ _)

theorem coloredClosedParity {n D w : ℕ} {α : Type*} [DecidableEq α] (B : Bank n)
    (hz : B.Has (fun _ => false)) (ho : B.Has (fun _ => true))
    (colors : Finset α) (edge : Edge D) (tag : α → BitFn n)
    (labels : α → Labels n D) (q prep : ℕ)
    (emit : ∀ c ∈ colors, ∀ C, B.Ext C →
      C.Grow prep (fun E => E.Has (tag c) ∧
        ∀ i, i<q → ∀ a b, E.Has (fun x => labels c x i a b))) :
    B.Grow (colors.card*((prep+q*layerCost D w+2*(D*(w*13)))+2*(w*4+w*13)))
      (fun E => ∀ p : Bool, HasWord E w (fun x => ∑ c ∈ colors, ∑ a : Fin D,
        ScheduledTrace.parityDP edge (labels c x) q a a (xor (tag c x) p))) := by
  let counts (c : α) (p : Bool) (x : Env n) :=
    ∑ a : Fin D, ScheduledTrace.parityDP edge (labels c x) q a a p
  apply aggregateColors B hz ho colors tag counts (prep+q*layerCost D w+2*(D*(w*13)))
  intro c hc C e
  obtain ⟨J,eJ,kJ,htag,hlabel⟩ := emit c hc C e
  obtain ⟨A,eA,kA,hA⟩ := closedParity J (eJ (e hz)) (eJ (e ho)) edge (labels c) q hlabel
  exact ⟨A, Bank.ext_trans eJ eA, by omega, eA htag, hA⟩

end PEqualNP.Outside.L_meta_33635.Compiler

namespace PEqualNP.Outside.L_meta_33635.Compiler
open Builder

theorem characterBit {n m : ℕ} (B : Bank n) (hz : B.Has (fun _ => false))
    (mask : ℕ) (y : Env n → ℕ) (hy : HasWord B m y) :
    B.Grow (1+m*4) (fun E => E.Has (fun x => (List.range m).foldl
      (fun b j => xor b (mask.testBit j && (y x).testBit j)) false)) := by
  have h := B.xorList (List.range m) (fun j x => mask.testBit j && (y x).testBit j) (by
    intro j hj
    cases hm : mask.testBit j
    · simpa only [hm, Bool.false_and] using hz
    · simpa only [hm, Bool.true_and] using hy ⟨j,List.mem_range.mp hj⟩)
  simpa using h

private lemma mod_split (a i : ℕ) : a % 2^(i+1) = 2^i*(a.testBit i).toNat+a % 2^i := by
  rw [Nat.mod_pow_succ, Nat.add_comm, Nat.toNat_testBit]

private lemma le_step (a b i : ℕ) :
    decide (a % 2^(i+1) ≤ b % 2^(i+1)) =
      (if a.testBit i == b.testBit i then decide (a % 2^i ≤ b % 2^i) else b.testBit i) := by
  rw [mod_split a, mod_split b]
  have ha := Nat.mod_lt a (Nat.two_pow_pos i)
  have hb := Nat.mod_lt b (Nat.two_pow_pos i)
  cases a.testBit i <;> cases b.testBit i <;> simp <;> omega

private def leBits (w a b : ℕ) := decide (a % 2^w ≤ b % 2^w)

theorem compareLow {n w : ℕ} (B : Bank n) (ho : B.Has (fun _ => true))
    (a b : Env n → ℕ) (ha : HasWord B w a) (hb : HasWord B w b) :
    B.Grow (w*9) (fun E => E.Has (fun x => decide (a x % 2^w ≤ b x % 2^w))) := by
  have iter (i : ℕ) (hi : i≤w) :
      B.Grow (i*9) (fun E => E.Has (fun x => leBits i (a x) (b x))) := by
    induction i with
    | zero =>
      refine ⟨B, Bank.ext_refl B, by simp, ?_⟩
      exact has_congr ho (fun x => by simp [leBits, Nat.mod_one])
    | succ i ih =>
      have hlt : i<w := by omega
      obtain ⟨C,eC,kC,prev⟩ := ih (by omega)
      obtain ⟨J,eJ,kJ,equalBit⟩ := Bank.eqBool (eC (ha ⟨i,hlt⟩)) (eC (hb ⟨i,hlt⟩))
      obtain ⟨K,eK,kK,answer⟩ := Bank.mux equalBit (eJ prev) (eJ (eC (hb ⟨i,hlt⟩)))
      refine ⟨K, Bank.ext_trans eC (Bank.ext_trans eJ eK), by rw [Nat.succ_mul]; omega, ?_⟩
      exact has_congr answer (fun x => (le_step (a x) (b x) i).symm)
  exact iter w (le_refl _)

theorem shiftWord {n w : ℕ} (B : Bank n) (hz : B.Has (fun _ => false))
    (m : ℕ) (a : Env n → ℕ) (ha : HasWord B w a) :
    HasWord B w (fun x => 2^m * a x) := by
  intro i
  by_cases h : m ≤ i.val
  · exact has_congr (ha ⟨i.val-m,by omega⟩) (fun x => by simp [Nat.testBit_two_pow_mul,h])
  · exact has_congr hz (fun x => by simp [Nat.testBit_two_pow_mul,h])

theorem widenWord {n w z : ℕ} (B : Bank n) (hz : B.Has (fun _ => false))
    (a : Env n → ℕ) (h : ∀ x, a x < 2^z) (ha : HasWord B z a) : HasWord B w a := by
  intro i
  by_cases hi : i.val<z
  · exact ha ⟨i.val,hi⟩
  · exact has_congr hz (fun x => (Nat.testBit_lt_two_pow
      ((h x).trans_le (Nat.pow_le_pow_right Nat.zero_lt_two (by omega)))).symm)

theorem thresholdOutput {n w : ℕ} (B : Bank n) (hz : B.Has (fun _ => false))
    (ho : B.Has (fun _ => true)) (k m : ℕ) (valid : BitFn n) (hv : B.Has valid)
    (t pos neg : Env n → ℕ) (ht : HasWord B w t) (hp : HasWord B w pos) (hn : HasWord B w neg)
    (bounds : ∀ x, valid x = true → 2^m*t x + neg x < 2^w ∧ 2^k+pos x < 2^w) :
    B.Grow (w*35+1) (fun E => E.Has (fun x =>
      valid x && decide (2^m*t x + neg x ≤ 2^k+pos x))) := by
  obtain ⟨C,eC,kC,left⟩ := addWord B hz (fun x => 2^m*t x) neg (shiftWord B hz m t ht) hn
  obtain ⟨J,eJ,kJ,right⟩ := addWord C (eC hz) (fun _ => 2^k) pos
    (constWord C (eC hz) (eC ho) _) (keep eC hp)
  obtain ⟨K,eK,kK,cmp⟩ := compareLow J (eJ (eC ho)) _ _ (keep eJ left) right
  obtain ⟨E,eE,kE,ans⟩ := Bank.meet (eK (eJ (eC hv))) cmp
  refine ⟨E, Bank.ext_trans eC (Bank.ext_trans eJ (Bank.ext_trans eK eE)), by omega, ?_⟩
  apply has_congr ans
  intro x
  cases h : valid x
  · simp
  · obtain ⟨l,r⟩ := bounds x h
    simp [Nat.mod_eq_of_lt l,Nat.mod_eq_of_lt r]

end PEqualNP.Outside.L_meta_33635.Compiler

namespace PEqualNP.Outside.L_meta_33635.Compiler
open Builder

def colorTotal {α : Type*} {D n : ℕ} (colors : Finset α) (edge : Edge D)
    (tag : α → BitFn n) (labels : α → Labels n D) (q : ℕ) (p : Bool) (x : Env n) : ℕ :=
  ∑ c ∈ colors, ∑ a : Fin D, ScheduledTrace.parityDP edge (labels c x) q a a (xor (tag c x) p)

def colorCost (D w q prep : ℕ) := (prep+q*layerCost D w+2*(D*(w*13)))+2*(w*4+w*13)

theorem growScheduledThreshold {α : Type*} [DecidableEq α] {n D w k m : ℕ}
    (B : Bank n) (hz : B.Has (fun _ => false)) (ho : B.Has (fun _ => true))
    (valid : BitFn n) (hv : B.Has valid) (t : Env n → ℕ) (ht : HasWord B w t)
    (colors : Finset α) (edge : Edge D) (tag : α → BitFn n) (labels : α → Labels n D)
    (q prep : ℕ) (emit : ∀ c ∈ colors, ∀ C, B.Ext C →
      C.Grow prep (fun E => E.Has (tag c) ∧
        ∀ i, i<q → ∀ a b, E.Has (fun x => labels c x i a b)))
    (bounds : ∀ x, valid x = true →
      2^m*t x + colorTotal colors edge tag labels q true x < 2^w ∧
      2^k + colorTotal colors edge tag labels q false x < 2^w) :
    B.Grow (colors.card*colorCost D w q prep + (w*35+1)) (fun E =>
      E.Has (fun x => valid x && decide
        (2^m*t x + colorTotal colors edge tag labels q true x ≤
         2^k + colorTotal colors edge tag labels q false x))) := by
  obtain ⟨C,eC,kC,hs⟩ := coloredClosedParity (w:=w) B hz ho colors edge tag labels q prep emit
  obtain ⟨K,eK,kK,answer⟩ := thresholdOutput C (eC hz) (eC ho) k m valid (eC hv)
    t (colorTotal colors edge tag labels q false) (colorTotal colors edge tag labels q true)
    (keep eC ht) (hs false) (hs true) bounds
  exact ⟨K, Bank.ext_trans eC eK, by unfold colorCost; omega, answer⟩

end PEqualNP.Outside.L_meta_33635.Compiler

namespace PEqualNP.Outside.L_meta_33635.Compiler

theorem layerCost_eq (D w : ℕ) : layerCost D w = 34*D^3*w := by
  simp only [layerCost]
  ring

theorem colorCost_eq (D w q prep : ℕ) :
    colorCost D w q prep = prep + 34*(q*D^3*w) + 26*(D*w) + 34*w := by
  simp only [colorCost, layerCost_eq]
  ring

theorem colorCost_le {D w q P : ℕ} (hD : 0<D) (hP : 0<P) (hw : w≤P) (hq : q≤P) (prep : ℕ) :
    colorCost D w q prep ≤ prep + 94*(P^2*D^3) := by
  have dpos : 1 ≤ D^3 := Nat.pow_pos hD
  have d1 : D ≤ D^3 := by
    calc D = D*1 := by simp
         _ ≤ D*(D*D) := Nat.mul_le_mul_left _ (Nat.mul_pos hD hD)
         _ = D^3 := by ring
  have p1 : P ≤ P^2 := by
    calc P = P*1 := by simp
         _ ≤ P*P := Nat.mul_le_mul_left _ hP
         _ = P^2 := by ring
  have a : q*D^3*w ≤ P^2*D^3 := by
    calc q*D^3*w ≤ P*D^3*P := Nat.mul_le_mul (Nat.mul_le_mul_right _ hq) hw
         _ = P^2*D^3 := by ring
  have b : D*w ≤ P^2*D^3 := by
    rw [Nat.mul_comm D w]
    exact Nat.mul_le_mul (hw.trans p1) d1
  have c : w ≤ P^2*D^3 := by
    calc w = w*1 := by simp
         _ ≤ P^2*D^3 := Nat.mul_le_mul (hw.trans p1) dpos
  rw [colorCost_eq]
  omega

end PEqualNP.Outside.L_meta_33635.Compiler

namespace PEqualNP.Outside.L_meta_33635.Pivot

abbrev Stream := ℤ → Bool

def spacing (col : Bool) : ℤ := if col then 2 else 1
def initialShift (col : Bool) : ℤ := if col then 3 else 1
def injection (col : Bool) (t : ℕ) : ℤ :=
  if col then 3 * (t : ℤ) + 4 else 2 * (t : ℤ)

def mix (col : Bool) (x : Stream) (j : ℤ) : Bool :=
  xor (xor (x j) (x (j - spacing col))) (x (j + spacing col))

def nonlinear (col : Bool) (x : Stream) (j : ℤ) : Bool :=
  xor (mix col x j) (!(mix col x (j + 1)) && mix col x (j + 2))

def run (col : Bool) (w name : Stream) (schedule : ℕ → Stream) : ℕ → Stream
  | 0 => fun j => xor (w (j - initialShift col)) (name j)
  | t+1 => fun j => xor (xor (nonlinear col (run col w name schedule t) j)
      (w (j - injection col t))) (schedule t j)

def past (col : Bool) (t : ℕ) : ℤ :=
  if col then max (2*(t:ℤ)+3) (3*(t:ℤ)+1) else max ((t:ℤ)+1) (2*(t:ℤ)-2)

def future (col : Bool) (t : ℕ) : ℤ :=
  if col then 4*(t:ℤ)-3 else 3*(t:ℤ)-1

def reach (col : Bool) (r : ℕ) : ℤ :=
  if col then 7*(r:ℤ)-2 else 5*(r:ℤ)-3

def Agree (x y : Stream) (a b : ℤ) : Prop := ∀ j, a ≤ j → j ≤ b → x j = y j

lemma nonlinear_congr (col : Bool) (x y : Stream) (i : ℤ)
    (h : Agree x y (i-spacing col) (i+spacing col+2)) :
    nonlinear col x i = nonlinear col y i := by
  have hg : 0 ≤ spacing col := by cases col <;> decide
  have hm (j : ℤ) (h₁ : i ≤ j) (h₂ : j ≤ i+2) : mix col x j = mix col y j := by
    unfold mix
    rw [h j (by omega) (by omega), h (j-spacing col) (by omega) (by omega),
      h (j+spacing col) (by omega) (by omega)]
  unfold nonlinear
  rw [hm i (by omega) (by omega), hm (i+1) (by omega) (by omega),
    hm (i+2) (by omega) (by omega)]

private lemma init_bounds (col : Bool) :
    -past col 0 ≤ -initialShift col ∧ -initialShift col ≤ future col 0 := by
  cases col <;> decide

private lemma step_bounds (col : Bool) (t : ℕ) :
    past col t + spacing col ≤ past col (t+1) ∧
    future col t + spacing col + 2 ≤ future col (t+1) ∧
    -past col (t+1) ≤ -injection col t ∧ -injection col t ≤ future col (t+1) := by
  cases col <;> simp [past, future, injection, spacing] <;> omega

theorem run_congr (col : Bool) (x y name : Stream) (schedule : ℕ → Stream) (t : ℕ)
    (i : ℤ) (h : Agree x y (i-past col t) (i+future col t)) :
    run col x name schedule t i = run col y name schedule t i := by
  induction t generalizing i with
  | zero =>
    obtain ⟨hl, hr⟩ := init_bounds col
    simpa only [run] using congrArg (fun b => xor b (name i))
      (h (i-initialShift col) (by omega) (by omega))
  | succ t ih =>
    obtain ⟨hl, hr, il, ir⟩ := step_bounds col t
    have hcore : nonlinear col (run col x name schedule t) i =
        nonlinear col (run col y name schedule t) i := by
      apply nonlinear_congr
      intro j hj₁ hj₂
      apply ih
      intro p hp₁ hp₂
      exact h p (by omega) (by omega)
    simp only [run]
    rw [hcore, h (i-injection col t) (by omega) (by omega)]

private lemma last_bounds (col : Bool) (t : ℕ) (ht : 3 ≤ t) :
    1 ≤ injection col t - spacing col - past col t ∧
    injection col t + spacing col + 2 + future col t ≤ reach col (t+1) := by
  cases col <;> simp [injection, spacing, past, future, reach] <;> omega

theorem last_congr (col : Bool) (x y name : Stream) (schedule : ℕ → Stream)
    (t : ℕ) (ht : 3 ≤ t) (p : ℤ) (h : Agree x y (p+1) (p+reach col (t+1))) :
    nonlinear col (run col x name schedule t) (p+injection col t) =
      nonlinear col (run col y name schedule t) (p+injection col t) := by
  obtain ⟨hl, hr⟩ := last_bounds col t ht
  apply nonlinear_congr
  intro j hj₁ hj₂
  apply run_congr
  intro u hu₁ hu₂
  exact h u (by omega) (by omega)

theorem affine_pivot (col : Bool) (x y name : Stream) (schedule : ℕ → Stream)
    (t : ℕ) (ht : 3 ≤ t) (p : ℤ) (h : Agree x y (p+1) (p+reach col (t+1))) :
    xor (run col x name schedule (t+1) (p+injection col t))
        (run col y name schedule (t+1) (p+injection col t)) = xor (x p) (y p) := by
  have hc := last_congr col x y name schedule t ht p h
  have hp : p+injection col t-injection col t = p := by omega
  simp only [run, hp, hc]
  cases nonlinear col (run col y name schedule t) (p+injection col t) <;>
    cases x p <;> cases y p <;> cases schedule t (p+injection col t) <;> rfl

end PEqualNP.Outside.L_meta_33635.Pivot

namespace PEqualNP.Outside.L_meta_33635.Pivot.Word
def rot (k s word : Nat) : Nat :=
  ((word <<< (s % k)) ||| (word >>> (k - s % k))) % 2 ^ k

def stepBit (k word i : Nat) : Bool :=
  xor (word.testBit i) (!(word.testBit ((i + 1) % k)) && word.testBit ((i + 2) % k))

def step (k word : Nat) : Nat :=
  (List.range k).foldl (fun acc i =>
    acc ||| ((xor (word.testBit i)
      (!(word.testBit ((i + 1) % k)) && word.testBit ((i + 2) % k))).toNat <<< i)) 0

def roundStep (k : Nat) (col : Bool) (w : Nat) (x : Nat) (cj : Nat) (j : Nat) : Nat :=
  let g := if col then 2 else 1
  step k (x ^^^ rot k g x ^^^ rot k (k - g) x) ^^^
    rot k (if col then 3 * (j + 1) + 1 else 2 * j) w ^^^ cj

def state (k r : Nat) (col : Bool) (w u : Nat) (c : Fin r → Fin (2 ^ k)) : Nat :=
  let g := if col then 2 else 1
  (List.finRange r).foldl (fun x j =>
    step k (x ^^^ rot k g x ^^^ rot k (k - g) x) ^^^
      rot k (if col then 3 * (j.val + 1) + 1 else 2 * j.val) w ^^^ (c j).val)
    (rot k (if col then 3 else 1) w ^^^ u)

lemma rot_lt (k s word : Nat) : rot k s word < 2 ^ k :=
  Nat.mod_lt _ (Nat.two_pow_pos k)

lemma xor_lt {k a b : Nat} (ha : a < 2 ^ k) (hb : b < 2 ^ k) : a ^^^ b < 2 ^ k := by
  apply Nat.lt_pow_two_of_testBit
  intro j hj
  have hpow := Nat.pow_le_pow_right Nat.zero_lt_two hj
  simp [Nat.testBit_xor, Nat.testBit_lt_two_pow (ha.trans_le hpow),
    Nat.testBit_lt_two_pow (hb.trans_le hpow)]

lemma testBit_rot {k s word b : Nat} (hw : word < 2 ^ k) (hb : b < k) :
    (rot k s word).testBit b = word.testBit ((b + k - s % k) % k) := by
  have hk : 0 < k := by omega
  have hs : s % k < k := Nat.mod_lt _ hk
  simp only [rot, Nat.testBit_mod_two_pow, hb, decide_true, Bool.true_and,
    Nat.testBit_or, Nat.testBit_shiftLeft, Nat.testBit_shiftRight]
  by_cases h : s % k ≤ b
  · have hz : word.testBit (k - s % k + b) = false :=
      Nat.testBit_lt_two_pow (hw.trans_le (Nat.pow_le_pow_right Nat.zero_lt_two (by omega)))
    have he : (b + k - s % k) % k = b - s % k := by
      rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]; omega
    simp [h, hz, he]
  · have he : (b + k - s % k) % k = k - s % k + b := by
      rw [Nat.mod_eq_of_lt (by omega)]; omega
    simp [h, he]

lemma testBit_foldl_or (p : Nat → Bool) (xs : List Nat) (acc i : Nat) :
    (xs.foldl (fun a j => a ||| ((p j).toNat <<< j)) acc).testBit i =
      (acc.testBit i || (decide (i ∈ xs) && p i)) := by
  induction xs generalizing acc with
  | nil => simp
  | cons j xs ih =>
    simp only [List.foldl_cons, ih, Nat.testBit_or, Nat.testBit_shiftLeft]
    by_cases hji : j = i
    · subst j; cases p i <;> simp
    · by_cases hle : j ≤ i
      · have hsub : 1 ≤ i - j := by omega
        have hbt : (p j).toNat.testBit (i - j) = false := by
          cases p j
          · simp
          · exact Nat.testBit_lt_two_pow (lt_of_lt_of_le (by omega : 1 < 2 ^ 1)
              (Nat.pow_le_pow_right Nat.zero_lt_two hsub))
        simp [hle, hbt, Ne.symm hji]
      · simp [hle, Ne.symm hji]

lemma testBit_step_all (k word b : Nat) :
    (step k word).testBit b = (decide (b < k) && stepBit k word b) := by
  unfold step stepBit; rw [testBit_foldl_or]; simp

lemma testBit_step {k word b : Nat} (hb : b < k) :
    (step k word).testBit b = stepBit k word b := by
  simp [testBit_step_all, hb]

lemma step_lt (k word : Nat) : step k word < 2 ^ k := by
  apply Nat.lt_pow_two_of_testBit
  intro b hb
  simp [testBit_step_all, Nat.not_lt_of_ge hb]

lemma foldl_state_lt {k r : Nat} (col : Bool) (w : Nat) (c : Fin r → Fin (2 ^ k))
    (l : List (Fin r)) (init : Nat) (hinit : init < 2 ^ k) :
    let g := if col then 2 else 1
    l.foldl (fun x j =>
      step k (x ^^^ rot k g x ^^^ rot k (k - g) x) ^^^
        rot k (if col then 3 * (j.val + 1) + 1 else 2 * j.val) w ^^^ (c j).val) init < 2 ^ k := by
  induction l generalizing init with
  | nil => exact hinit
  | cons j l ih =>
    simp only [List.foldl_cons]
    apply ih
    exact xor_lt (xor_lt (step_lt k _) (rot_lt k _ _)) (c j).isLt

lemma state_lt {k r : Nat} (col : Bool) (w u : Nat) (hu : u < 2 ^ k)
    (c : Fin r → Fin (2 ^ k)) : state k r col w u c < 2 ^ k :=
  foldl_state_lt col w c (List.finRange r) _ (xor_lt (rot_lt k _ _) hu)

def statePre (k r : Nat) (col : Bool) (w u : Nat) (c : Fin r → Fin (2 ^ k)) (t : Nat) : Nat :=
  let g := if col then 2 else 1
  ((List.finRange r).take t).foldl (fun x j =>
    step k (x ^^^ rot k g x ^^^ rot k (k - g) x) ^^^
      rot k (if col then 3 * (j.val + 1) + 1 else 2 * j.val) w ^^^ (c j).val)
    (rot k (if col then 3 else 1) w ^^^ u)

lemma statePre_zero (k r : Nat) (col : Bool) (w u : Nat) (c : Fin r → Fin (2 ^ k)) :
    statePre k r col w u c 0 = rot k (if col then 3 else 1) w ^^^ u := by
  simp [statePre]

lemma statePre_full (k r : Nat) (col : Bool) (w u : Nat) (c : Fin r → Fin (2 ^ k)) :
    statePre k r col w u c r = state k r col w u c := by
  simp [statePre, state, List.take_of_length_le]

lemma statePre_succ {k r : Nat} (col : Bool) (w u : Nat) (c : Fin r → Fin (2 ^ k))
    {t : Nat} (ht : t < r) :
    let g := if col then 2 else 1
    let x := statePre k r col w u c t
    statePre k r col w u c (t + 1) =
      step k (x ^^^ rot k g x ^^^ rot k (k - g) x) ^^^
        rot k (if col then 3 * (t + 1) + 1 else 2 * t) w ^^^ (c ⟨t, ht⟩).val := by
  have htake : (List.finRange r).take (t + 1) =
      (List.finRange r).take t ++ [⟨t, ht⟩] := by
    rw [List.take_add_one, List.getElem?_eq_getElem (by simp [ht])]
    simp [List.getElem_finRange]
  unfold statePre
  rw [htake, List.foldl_append]
  simp

lemma statePre_lt {k r : Nat} (col : Bool) (w u : Nat) (hu : u < 2 ^ k)
    (c : Fin r → Fin (2 ^ k)) (t : Nat) : statePre k r col w u c t < 2 ^ k :=
  foldl_state_lt col w c ((List.finRange r).take t) _ (xor_lt (rot_lt k _ _) hu)

end PEqualNP.Outside.L_meta_33635.Pivot.Word

namespace PEqualNP.Outside.L_meta_33635.Pivot

def idx (k : ℕ) (j : ℤ) : ℕ := (j % (k:ℤ)).toNat
def wordStream (k word : ℕ) (j : ℤ) : Bool := word.testBit (idx k j)

private lemma idx_cast {k : ℕ} (hk : 0 < k) (j : ℤ) :
    ((idx k j : ℕ):ℤ) = j % (k:ℤ) :=
  Int.toNat_of_nonneg (Int.emod_nonneg _ (by omega))

private lemma idx_lt {k : ℕ} (hk : 0 < k) (j : ℤ) : idx k j < k := by
  have h₁ := idx_cast hk j
  have h₂ := Int.emod_lt_of_pos j (by exact_mod_cast hk : (0:ℤ) < k)
  omega

private lemma idx_sub_nat (k h : ℕ) (hk : 0 < k) (j : ℤ) :
    (idx k j + k - h % k) % k = idx k (j - (h:ℤ)) := by
  apply Int.ofNat_inj.mp
  have ha : h % k ≤ idx k j+k := by have := Nat.mod_lt h hk; omega
  rw [← Int.ofNat_mod_ofNat, Int.natCast_sub ha, Int.natCast_add,
    idx_cast hk, ← Int.ofNat_mod_ofNat, idx_cast hk]
  have e : j % (k:ℤ) + k - (h:ℤ)%k = (j % (k:ℤ) - (h:ℤ)%k)+k := by omega
  rw [e, Int.add_emod_right, Int.emod_sub_emod, Int.sub_emod_emod]

private lemma idx_add_nat (k h : ℕ) (hk : 0 < k) (j : ℤ) :
    (idx k j + h) % k = idx k (j+(h:ℤ)) := by
  apply Int.ofNat_inj.mp
  rw [← Int.ofNat_mod_ofNat, Int.natCast_add, idx_cast hk, idx_cast hk, Int.emod_add_emod]

private lemma idx_reversed (k g : ℕ) (hg : g ≤ k) (j : ℤ) :
    idx k (j-((k-g:ℕ):ℤ)) = idx k (j+(g:ℤ)) := by
  unfold idx
  rw [Int.natCast_sub hg]
  have h : j-((k:ℤ)-(g:ℤ))=j+g-k := by omega
  rw [h, Int.sub_emod_right]

private lemma stream_rot {k : ℕ} (hk : 0 < k) (h word : ℕ) (hw : word < 2^k) (j : ℤ) :
    wordStream k (Word.rot k h word) j = wordStream k word (j-(h:ℤ)) := by
  unfold wordStream
  rw [Word.testBit_rot hw (idx_lt hk j), idx_sub_nat k h hk j]

private lemma stream_xor (k a b : ℕ) (j : ℤ) :
    wordStream k (a ^^^ b) j = xor (wordStream k a j) (wordStream k b j) :=
  Nat.testBit_xor a b (idx k j)

private lemma stream_step {k : ℕ} (hk : 0 < k) (word : ℕ) (j : ℤ) :
    wordStream k (Word.step k word) j =
    xor (wordStream k word j) (!(wordStream k word (j+1)) && wordStream k word (j+2)) := by
  unfold wordStream
  rw [Word.testBit_step (idx_lt hk j)]
  unfold Word.stepBit
  rw [idx_add_nat k 1 hk j, idx_add_nat k 2 hk j]
  rfl

private lemma stream_mix {k : ℕ} (hk : 2 ≤ k) (col : Bool) (w : ℕ) (hw : w < 2^k) (j : ℤ) :
    let g := if col then 2 else 1
    wordStream k (w ^^^ Word.rot k g w ^^^ Word.rot k (k-g) w) j =
       mix col (wordStream k w) j := by
  intro g
  have hp : 0 < k := by omega
  have hg : g ≤ k := by cases col <;> simp [g] <;> omega
  have he : (g:ℤ) = spacing col := by cases col <;> rfl
  rw [stream_xor, stream_xor, stream_rot hp g w hw, stream_rot hp (k-g) w hw]
  unfold mix wordStream
  rw [idx_reversed k g hg, he]

private lemma stream_stepmix {k : ℕ} (hk : 2 ≤ k) (col : Bool) (w : ℕ) (hw : w < 2^k) (j : ℤ) :
    let g := if col then 2 else 1
    wordStream k (Word.step k (w ^^^ Word.rot k g w ^^^ Word.rot k (k-g) w)) j =
       nonlinear col (wordStream k w) j := by
  intro g
  rw [stream_step (by omega)]
  have hm (v : ℤ) :
      wordStream k (w ^^^ Word.rot k g w ^^^ Word.rot k (k-g) w) v =
          mix col (wordStream k w) v := stream_mix hk col w hw v
  rw [hm j, hm (j+1), hm (j+2)]
  rfl

def liftedSchedule {k r : ℕ} (c : Fin r → Fin (2^k)) (t : ℕ) : Stream :=
  if h : t < r then wordStream k (c ⟨t,h⟩).val else fun _ => false

private lemma lift_pre {k r : ℕ} (hk : 2 ≤ k) (col : Bool) (w u : ℕ)
    (hw : w < 2^k) (hu : u < 2^k) (c : Fin r → Fin (2^k)) (t : ℕ) (ht : t ≤ r) :
    wordStream k (Word.statePre k r col w u c t) =
    run col (wordStream k w) (wordStream k u) (liftedSchedule c) t := by
  have hp : 0 < k := by omega
  induction t with
  | zero =>
    funext j
    rw [Word.statePre_zero, stream_xor, stream_rot hp _ w hw]
    cases col <;> rfl
  | succ t ih =>
    have htr : t < r := by omega
    have hprev := ih (by omega)
    funext j
    rw [Word.statePre_succ col w u c htr]
    rw [stream_xor, stream_xor, stream_stepmix hk col _ (Word.statePre_lt col w u hu c t) j,
      stream_rot hp _ w hw, hprev]
    have e : ((if col then 3*(t+1)+1 else 2*t : ℕ):ℤ) = injection col t := by
      cases col <;> simp [injection]
      omega
    simp [run, liftedSchedule, htr, e]

theorem word_affine_pivot {k : ℕ} (hk : 2 ≤ k) (col : Bool) (t : ℕ) (ht : 3 ≤ t)
    (x y u : Fin (2^k)) (c : Fin (t+1) → Fin (2^k)) (p : ℤ)
    (h : Agree (wordStream k x.val) (wordStream k y.val) (p+1) (p+reach col (t+1))) :
    xor (wordStream k (Word.state k (t+1) col x.val u.val c) (p+injection col t))
        (wordStream k (Word.state k (t+1) col y.val u.val c) (p+injection col t)) =
    xor (wordStream k x.val p) (wordStream k y.val p) := by
  rw [← Word.statePre_full, ← Word.statePre_full,
    lift_pre hk col x.val u.val x.isLt u.isLt c (t+1) (by omega),
    lift_pre hk col y.val u.val y.isLt u.isLt c (t+1) (by omega)]
  exact affine_pivot col _ _ _ _ t ht p h

theorem word_sensor_xor {k r : ℕ} (hk : 2 ≤ k) (hr : 4 ≤ r) (col : Bool)
    (x y u : Fin (2^k)) (c : Fin r → Fin (2^k)) (p : Fin k)
    (h : ∀ a : ℕ, 0 < a → a ≤ (if col then 7*r-2 else 5*r-3) →
      x.val.testBit ((p.val+a)%k) = y.val.testBit ((p.val+a)%k)) :
    let delay := if col then 3*r+1 else 2*r-2
    xor ((Word.state k r col x.val u.val c).testBit ((p.val+delay)%k))
        ((Word.state k r col y.val u.val c).testBit ((p.val+delay)%k)) =
      xor (x.val.testBit p.val) (y.val.testBit p.val) := by
  cases r with
  | zero => omega
  | succ t =>
    have ht : 3 ≤ t := by omega
    have hp : 0 < k := by omega
    have hr' : ((if col then 7*(t+1)-2 else 5*(t+1)-3 : ℕ):ℤ) = reach col (t+1) := by
      cases col <;> simp [reach] <;> omega
    let delay := if col then 3*(t+1)+1 else 2*(t+1)-2
    have hd : (delay:ℤ) = injection col t := by cases col <;> simp [delay,injection] <;> omega
    have hi : idx k (p.val:ℤ) = p.val := by
      unfold idx
      rw [Int.emod_eq_of_lt (by omega) (by exact_mod_cast p.isLt)]
      rfl
    have hstream : Agree (wordStream k x.val) (wordStream k y.val)
        ((p.val:ℤ)+1) ((p.val:ℤ)+reach col (t+1)) := by
      intro j hlow hhigh
      let a := (j-(p.val:ℤ)).toNat
      have ha : (a:ℤ) = j-(p.val:ℤ) := Int.toNat_of_nonneg (by omega)
      have hj : j=(p.val:ℤ)+(a:ℤ) := by omega
      have hcyc := idx_add_nat k a hp (p.val:ℤ)
      rw [hi, ← hj] at hcyc
      unfold wordStream
      rw [← hcyc]
      exact h a (by omega) (by omega)
    have hv := word_affine_pivot hk col t ht x y u c (p.val:ℤ) hstream
    have hcyc := idx_add_nat k delay hp (p.val:ℤ)
    rw [hi, hd] at hcyc
    unfold wordStream at hv
    simpa only [hi, ← hcyc] using hv

def flipKey {k : ℕ} (x : Fin (2^k)) (p : Fin k) : Fin (2^k) :=
  ⟨x.val ^^^ 2^p.val, Word.xor_lt x.isLt (Nat.pow_lt_pow_right (by decide) p.isLt)⟩

theorem flipKey_involutive {k : ℕ} (p : Fin k) : Function.Involutive (fun x => flipKey x p) := by
  intro x
  apply Fin.ext
  simp [flipKey, Nat.xor_assoc]

theorem word_sensor_fixed_of_outside {k r : ℕ} (hk : 2 ≤ k) (hr : 4 ≤ r) (col : Bool)
    (x u : Fin (2^k)) (c : Fin r → Fin (2^k)) (p q : Fin k)
    (hout : ∀ a : ℕ, a ≤ (if col then 7*r-2 else 5*r-3) → q.val ≠ (p.val+a)%k) :
    let d := if col then 3*r+1 else 2*r-2
    (Word.state k r col (flipKey x q).val u.val c).testBit ((p.val+d)%k) =
      (Word.state k r col x.val u.val c).testBit ((p.val+d)%k) := by
  have h := word_sensor_xor hk hr col x (flipKey x q) u c p (by
    intro a _ ha
    simp [flipKey, Nat.testBit_xor, Nat.testBit_two_pow_of_ne (hout a ha)])
  have hqp : q.val ≠ p.val := by simpa [Nat.mod_eq_of_lt p.isLt] using hout 0 (Nat.zero_le _)
  have hp : (flipKey x q).val.testBit p.val = x.val.testBit p.val := by
    simp [flipKey, Nat.testBit_xor, Nat.testBit_two_pow_of_ne hqp]
  dsimp only at h ⊢
  rw [hp] at h
  have bit_rule (a b v : Bool) : xor a b = xor v v → b = a := by
    cases a <;> cases b <;> cases v <;> decide
  exact bit_rule _ _ _ h

theorem word_sensor_flip {k r : ℕ} (hk : 2 ≤ k) (hr : 4 ≤ r) (col : Bool)
    (hwindow : (if col then 7*r-2 else 5*r-3) < k)
    (x u : Fin (2^k)) (c : Fin r → Fin (2^k)) (p : Fin k) :
    let d := if col then 3*r+1 else 2*r-2
    (Word.state k r col (flipKey x p).val u.val c).testBit ((p.val+d)%k) =
      !((Word.state k r col x.val u.val c).testBit ((p.val+d)%k)) := by
  have h := word_sensor_xor hk hr col x (flipKey x p) u c p (by
    intro a ha hb
    have hne : p.val ≠ (p.val+a)%k := by
      by_cases hsmall : p.val+a < k
      · rw [Nat.mod_eq_of_lt hsmall]; omega
      · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]; omega
    simp [flipKey, Nat.testBit_xor, Nat.testBit_two_pow_of_ne hne])
  have hp : (flipKey x p).val.testBit p.val = !x.val.testBit p.val := by
    simp [flipKey, Nat.testBit_xor, Nat.testBit_two_pow_self]
  dsimp only at h ⊢
  rw [hp] at h
  have bit_rule (a b v : Bool) : xor a b = xor v (!v) → b = !a := by
    cases a <;> cases b <;> cases v <;> decide
  exact bit_rule _ _ _ h

end PEqualNP.Outside.L_meta_33635.Pivot

namespace PEqualNP.Outside.L_meta_33635.Pivot

def site {q s : ℕ} (hs : 0 < s) (off : Fin (q*s)) (i : Fin q) : Fin (q*s) :=
  ⟨(off.val+i.val*s)%(q*s), Nat.mod_lt _ (Nat.mul_pos ((Nat.zero_le i.val).trans_lt i.isLt) hs)⟩

theorem site_separated {q s : ℕ} (hs : 0 < s) (off : Fin (q*s)) (i j : Fin q)
    (hi : 2 ≤ i.val) (h₀ : j ≠ i) (h₁ : j.val+1 ≠ i.val) (h₂ : j.val+2 ≠ i.val)
    (a : ℕ) (ha : a < 3*s) :
    (site hs off i).val ≠ ((site hs off j).val+a)%(q*s) := by
  intro he
  have hm : off.val+(j.val*s+a) ≡ off.val+i.val*s [MOD q*s] := by
    change (off.val+(j.val*s+a))%(q*s) = (off.val+i.val*s)%(q*s)
    simpa only [site, Nat.mod_add_mod, Nat.add_assoc] using he.symm
  have hb := Nat.ModEq.add_left_cancel' off.val hm
  change (j.val*s+a)%(q*s) = (i.val*s)%(q*s) at hb
  have hd := congrArg (fun z => z/s) hb
  simp only [Nat.mod_mul_left_div_self, Nat.mul_div_cancel _ hs] at hd
  rw [Nat.add_comm (j.val*s) a, Nat.add_mul_div_right _ _ hs, Nat.mod_eq_of_lt i.isLt] at hd
  have hva : a/s < 3 := (Nat.div_lt_iff_lt_mul hs).mpr ha
  have hne : j.val ≠ i.val := fun h => h₀ (Fin.ext h)
  by_cases hlt : a/s+j.val < q
  · rw [Nat.mod_eq_of_lt hlt] at hd
    have small (b : ℕ) (h : b < 3) : b=0 ∨ b=1 ∨ b=2 := by omega
    rcases small _ hva with hh | hh | hh <;> rw [hh] at hd <;> omega
  · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)] at hd
    omega

def sensor {q s r : ℕ} (hs : 0 < s) (nr nc : Fin (2^(q*s)))
    (cr cc : Fin r → Fin (2^(q*s))) (off : Fin (q*s)) (bank : Fin q → Bool)
    (i : Fin q) (w : Fin (2^(q*s))) : Bool :=
  (Word.state (q*s) r (bank i) w.val (if bank i then nc.val else nr.val)
    (if bank i then cc else cr)).testBit
      (((site hs off i).val + (if bank i then 3*r+1 else 2*r-2))%(q*s))

theorem sensor_gap_flip {q s r d : ℕ} (hs : 0 < s) (hr : 4 ≤ r) (hd : d < 3*s)
    (nr nc : Fin (2^(q*s))) (cr cc : Fin r → Fin (2^(q*s)))
    (off : Fin (q*s)) (bank : Fin q → Bool)
    (valid : ∀ j, (if bank j then 7*r-2 else 5*r-3) ≤ d)
    (i : Fin q) (hi : 2 ≤ i.val) :
    ∃ flip : Fin (2^(q*s)) ≃ Fin (2^(q*s)),
      (∀ w, sensor hs nr nc cr cc off bank i (flip w) = !(sensor hs nr nc cr cc off bank i w)) ∧
      ∀ j : Fin q, j ≠ i → j.val+1 ≠ i.val → j.val+2 ≠ i.val →
        ∀ w, sensor hs nr nc cr cc off bank j (flip w) = sensor hs nr nc cr cc off bank j w := by
  have hq : 3 ≤ q := by omega
  have hthree : 3*s ≤ q*s := Nat.mul_le_mul_right s hq
  have hk : 2 ≤ q*s := by omega
  let e : Fin (2^(q*s)) ≃ Fin (2^(q*s)) :=
    ⟨fun w => flipKey w (site hs off i), fun w => flipKey w (site hs off i),
      flipKey_involutive _, flipKey_involutive _⟩
  refine ⟨e, ?_, ?_⟩
  · intro w
    change sensor hs nr nc cr cc off bank i (flipKey w (site hs off i)) = _
    have hrk := (valid i).trans_lt (hd.trans_le hthree)
    cases hbi : bank i <;> simp only [sensor, hbi, Bool.false_eq_true, ite_false, ite_true]
    · exact word_sensor_flip hk hr false (by simpa [hbi] using hrk) w nr cr (site hs off i)
    · exact word_sensor_flip hk hr true (by simpa [hbi] using hrk) w nc cc (site hs off i)
  · intro j h₀ h₁ h₂ w
    change sensor hs nr nc cr cc off bank j (flipKey w (site hs off i)) = _
    have hout (a : ℕ) (ha : a ≤ (if bank j then 7*r-2 else 5*r-3)) :
        (site hs off i).val ≠ ((site hs off j).val+a)%(q*s) :=
      site_separated hs off i j hi h₀ h₁ h₂ a (lt_of_le_of_lt (ha.trans (valid j)) hd)
    cases hbj : bank j <;> simp only [sensor, hbj, Bool.false_eq_true, ite_false, ite_true]
    · exact word_sensor_fixed_of_outside hk hr false w nr cr (site hs off j) (site hs off i)
        (by simpa [hbj] using hout)
    · exact word_sensor_fixed_of_outside hk hr true w nc cc (site hs off j) (site hs off i)
        (by simpa [hbj] using hout)

end PEqualNP.Outside.L_meta_33635.Pivot

namespace PEqualNP.Outside.L_meta_33635.ScheduledLayout
open PEqualNP.Outside.L_meta_33635
open Builder Compiler

def inLen (k r q m : ℕ) := 3*k+2*r*k+q+m+(k+1)
def bits (w a : ℕ) := (List.range w).map (fun i => a.testBit i)
def sched {r k : ℕ} (c : Fin r → Fin (2^k)) :=
  (List.finRange r).flatMap (fun j => bits k (c j).val)

def inputs {k r q m : ℕ} (nr nc : Fin (2^k)) (cr cc : Fin r → Fin (2^k))
    (off : Fin k) (bank : Fin q → Bool) (y : Fin (2^m)) (t : Fin (2^(k+1))) :=
  bits k nr.val ++ bits k nc.val ++ sched cr ++ sched cc ++ bits k off.val ++
    List.ofFn bank ++ bits m y.val ++ bits (k+1) t.val

@[simp] theorem bits_length (w a : ℕ) : (bits w a).length=w := by simp [bits]

private lemma flat_length {α β : Type} (l : List α) (f : α → List β) (k : ℕ)
    (hf : ∀ a, (f a).length=k) : (l.flatMap f).length=l.length*k := by
  induction l with
  | nil => simp
  | cons a l ih => simp [hf,ih,Nat.succ_mul,Nat.add_comm]

@[simp] theorem sched_length {r k : ℕ} (c : Fin r → Fin (2^k)) :
    (sched c).length = r*k := by
  unfold sched
  rw [flat_length _ _ k (fun _ => bits_length _ _), List.length_finRange]

@[simp] theorem inputs_length {k r q m : ℕ} (nr nc : Fin (2^k)) (cr cc : Fin r → Fin (2^k))
    (off : Fin k) (bank : Fin q → Bool) (y : Fin (2^m)) (t : Fin (2^(k+1))) :
    (inputs nr nc cr cc off bank y t).length=inLen k r q m := by
  simp [inputs,inLen]
  ring

def encoded {k r q m : ℕ} (nr nc : Fin (2^k)) (cr cc : Fin r → Fin (2^k))
    (off : Fin k) (bank : Fin q → Bool) (y : Fin (2^m)) (t : Fin (2^(k+1))) :
    Env (inLen k r q m) := fun i => (inputs nr nc cr cc off bank y t).getD i.val false

theorem ofFn_encoded {k r q m : ℕ} (nr nc : Fin (2^k)) (cr cc : Fin r → Fin (2^k))
    (off : Fin k) (bank : Fin q → Bool) (y : Fin (2^m)) (t : Fin (2^(k+1))) :
    List.ofFn (encoded nr nc cr cc off bank y t) = inputs nr nc cr cc off bank y t := by
  apply List.ext_getElem
  · simp
  · intro i h₁ h₂
    simp only [List.getElem_ofFn, encoded, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem h₂, Option.getD_some]

def raw {n : ℕ} (x : Env n) (i : ℕ) := (List.ofFn x).getD i false

def readWord {n : ℕ} (w base : ℕ) (x : Env n) : Fin (2^w) :=
  ⟨(List.range w).foldl (fun z i => z ||| ((raw x (base+i)).toNat <<< i)) 0, by
    apply Nat.lt_pow_two_of_testBit
    intro i hi
    rw [Pivot.Word.testBit_foldl_or]
    simp [Nat.not_lt_of_ge hi]⟩

theorem readWord_bit {n : ℕ} (w base : ℕ) (x : Env n) (i : Fin w) :
    (readWord w base x).val.testBit i.val = raw x (base+i.val) := by
  simp only [readWord, Pivot.Word.testBit_foldl_or, List.mem_range, i.isLt,
    decide_true, Bool.true_and, Nat.zero_testBit, Bool.false_or]

theorem empty_raw {n : ℕ} (B : Bank n) (ext : (Bank.empty n).Ext B)
    (hz : B.Has (fun _ => false)) (i : ℕ) : B.Has (fun x => raw x i) := by
  by_cases hi : i < n
  · have h := ext (Bank.input ⟨i,hi⟩)
    simpa [raw,List.getD_eq_getElem?_getD,List.getElem?_eq_getElem,hi] using h
  · simpa [raw,List.getD_eq_getElem?_getD,hi] using hz

theorem readWord_wires {n : ℕ} (B : Bank n) (ext : (Bank.empty n).Ext B)
    (hz : B.Has (fun _ => false)) (w base : ℕ) :
    HasWord B w (fun x => (readWord w base x).val) := by
  intro i
  simpa only [readWord_bit] using empty_raw B ext hz (base+i.val)

def rowName {k r q m : ℕ} (x : Env (inLen k r q m)) := readWord k 0 x
def colName {k r q m : ℕ} (x : Env (inLen k r q m)) := readWord k k x
def rowSchedule {k r q m : ℕ} (x : Env (inLen k r q m)) (j : Fin r) := readWord k (2*k+j.val*k) x
def colSchedule {k r q m : ℕ} (x : Env (inLen k r q m)) (j : Fin r) := readWord k (2*k+r*k+j.val*k) x
def offsetWord {k r q m : ℕ} (x : Env (inLen k r q m)) := readWord k (2*k+2*r*k) x
def bankBit {k r q m : ℕ} (x : Env (inLen k r q m)) (j : Fin q) := raw x (3*k+2*r*k+j.val)
def target {k r q m : ℕ} (x : Env (inLen k r q m)) := readWord m (3*k+2*r*k+q) x
def threshold {k r q m : ℕ} (x : Env (inLen k r q m)) := readWord (k+1) (3*k+2*r*k+q+m) x

private theorem get_bounded (pre field post : List Bool) (j : ℕ) (hj : j < field.length) :
    (pre++field++post).getD (pre.length+j) false = field.getD j false := by
  rw [List.getD_append _ _ _ _ (by simp; omega),
    List.getD_append_right _ _ _ _ (by omega), Nat.add_sub_cancel_left]

private theorem bits_get (w x j : ℕ) (hj : j<w) : (bits w x).getD j false=x.testBit j := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simpa using hj)]
  simp [bits]

private lemma get_flat {α β : Type} (l : List α) (f : α → List β) (k : ℕ)
    (hf : ∀ z, (f z).length=k) {j i : ℕ} (hj : j<l.length) (hi : i<k)
    (hidx : j*k+i<(l.flatMap f).length) :
    (l.flatMap f)[j*k+i]'hidx = (f (l[j]'hj))[i]'(by rw [hf]; exact hi) := by
  induction l generalizing j with
  | nil => simp at hj
  | cons a l ih =>
    cases j with
    | zero =>
      simp only [Nat.zero_mul,Nat.zero_add,List.flatMap_cons,List.getElem_cons_zero]
      rw [List.getElem_append_left (by rw [hf]; exact hi)]
    | succ j =>
      simp only [List.flatMap_cons,List.getElem_cons_succ]
      have hh : (f a).length ≤ (j+1)*k+i := by rw [hf, Nat.succ_mul]; omega
      rw [List.getElem_append_right hh]
      have he : (j+1)*k+i-(f a).length=j*k+i := by rw [hf,Nat.succ_mul]; omega
      simp only [he]
      exact ih (by simpa using hj) _

private theorem sched_get {k r : ℕ} (c : Fin r → Fin (2^k)) (j : Fin r) (i : Fin k) :
    (sched c).getD (j.val*k+i.val) false = (c j).val.testBit i.val := by
  have hidx : j.val*k+i.val < (sched c).length := by
    have h := Nat.mul_le_mul_right k (Nat.succ_le_of_lt j.isLt)
    rw [Nat.succ_mul] at h
    rw [sched_length]; omega
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hidx]
  change ((List.finRange r).flatMap (fun j => bits k (c j).val))[j.val*k+i.val] = _
  rw [get_flat _ _ k (fun _ => bits_length _ _) (by simp [j.isLt]) i.isLt hidx]
  simp [bits,List.getElem_finRange]

private theorem word_ext {w : ℕ} (a b : Fin (2^w))
    (h : ∀ i : Fin w, a.val.testBit i.val = b.val.testBit i.val) : a=b := by
  apply Fin.ext
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < w
  · exact h ⟨i,hi⟩
  · rw [Nat.testBit_lt_two_pow (a.isLt.trans_le (Nat.pow_le_pow_right Nat.zero_lt_two (by omega))),
      Nat.testBit_lt_two_pow (b.isLt.trans_le (Nat.pow_le_pow_right Nat.zero_lt_two (by omega)))]

end PEqualNP.Outside.L_meta_33635.ScheduledLayout

namespace PEqualNP.Outside.L_meta_33635.ScheduledLayout
open PEqualNP.Outside.L_meta_33635 Builder Compiler
theorem decode_encoded {k r q m : ℕ} (nr nc : Fin (2^k)) (cr cc : Fin r → Fin (2^k))
    (off : Fin k) (bank : Fin q → Bool) (y : Fin (2^m)) (t : Fin (2^(k+1))) :
    let x := encoded nr nc cr cc off bank y t
    rowName x=nr ∧ colName x=nc ∧ rowSchedule x=cr ∧ colSchedule x=cc ∧
    (offsetWord x).val=off.val ∧ bankBit x=bank ∧ target x=y ∧ threshold x=t := by
  let x := encoded nr nc cr cc off bank y t
  have pick (pre field post : List Bool) (a : ℕ)
      (hlist : inputs nr nc cr cc off bank y t = pre++field++post) (hsize : pre.length=a)
      (i : ℕ) (hi : i<field.length) : raw x (a+i)=field.getD i false := by
    unfold x raw
    rw [ofFn_encoded,hlist,← hsize]
    exact get_bounded pre field post i hi
  have get0 (j : ℕ) (hj : j < k) : raw x (0+j) = (bits k nr.val).getD j false := by
    exact pick (([] : List Bool)) (bits k nr.val) (bits k nc.val ++ sched cr ++ sched cc ++ bits k off.val ++ List.ofFn bank ++ bits m y.val ++ bits (k+1) t.val) (0)
      (by simp [inputs,List.append_assoc]) (by simp) j (by simpa using hj)
  have get1 (j : ℕ) (hj : j < k) : raw x (k+j) = (bits k nc.val).getD j false := by
    exact pick (bits k nr.val) (bits k nc.val) (sched cr ++ sched cc ++ bits k off.val ++ List.ofFn bank ++ bits m y.val ++ bits (k+1) t.val) (k)
      (by simp [inputs,List.append_assoc]) (by simp) j (by simpa using hj)
  have get2 (j : ℕ) (hj : j < r*k) : raw x (2*k+j) = (sched cr).getD j false := by
    exact pick (bits k nr.val ++ bits k nc.val) (sched cr) (sched cc ++ bits k off.val ++ List.ofFn bank ++ bits m y.val ++ bits (k+1) t.val) (2*k)
      (by simp [inputs,List.append_assoc]) (by simp; ring) j (by simpa using hj)
  have get3 (j : ℕ) (hj : j < r*k) : raw x (2*k+r*k+j) = (sched cc).getD j false := by
    exact pick (bits k nr.val ++ bits k nc.val ++ sched cr) (sched cc) (bits k off.val ++ List.ofFn bank ++ bits m y.val ++ bits (k+1) t.val) (2*k+r*k)
      (by simp [inputs,List.append_assoc]) (by simp; ring) j (by simpa using hj)
  have get4 (j : ℕ) (hj : j < k) : raw x (2*k+2*r*k+j) = (bits k off.val).getD j false := by
    exact pick (bits k nr.val ++ bits k nc.val ++ sched cr ++ sched cc) (bits k off.val) (List.ofFn bank ++ bits m y.val ++ bits (k+1) t.val) (2*k+2*r*k)
      (by simp [inputs,List.append_assoc]) (by simp; ring) j (by simpa using hj)
  have get5 (j : ℕ) (hj : j < q) : raw x (3*k+2*r*k+j) = (List.ofFn bank).getD j false := by
    exact pick (bits k nr.val ++ bits k nc.val ++ sched cr ++ sched cc ++ bits k off.val) (List.ofFn bank) (bits m y.val ++ bits (k+1) t.val) (3*k+2*r*k)
      (by simp [inputs,List.append_assoc]) (by simp; ring) j (by simpa using hj)
  have get6 (j : ℕ) (hj : j < m) : raw x (3*k+2*r*k+q+j) = (bits m y.val).getD j false := by
    exact pick (bits k nr.val ++ bits k nc.val ++ sched cr ++ sched cc ++ bits k off.val ++ List.ofFn bank) (bits m y.val) (bits (k+1) t.val) (3*k+2*r*k+q)
      (by simp [inputs,List.append_assoc]) (by simp; ring) j (by simpa using hj)
  have get7 (j : ℕ) (hj : j < k+1) : raw x (3*k+2*r*k+q+m+j) = (bits (k+1) t.val).getD j false := by
    exact pick (bits k nr.val ++ bits k nc.val ++ sched cr ++ sched cc ++ bits k off.val ++ List.ofFn bank ++ bits m y.val) (bits (k+1) t.val) (([] : List Bool)) (3*k+2*r*k+q+m)
      (by simp [inputs,List.append_assoc]) (by simp; ring) j (by simpa using hj)
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_⟩
  · change rowName x = nr
    apply word_ext; intro i
    exact (readWord_bit (k) _ x i).trans ((get0 i.val i.isLt).trans (bits_get (k) _ _ i.isLt))
  · change colName x = nc
    apply word_ext; intro i
    exact (readWord_bit (k) _ x i).trans ((get1 i.val i.isLt).trans (bits_get (k) _ _ i.isLt))
  · change rowSchedule x = cr
    funext j
    apply word_ext; intro i
    have hb : j.val*k+i.val < r*k := by
      have H := Nat.mul_le_mul_right k (Nat.succ_le_of_lt j.isLt)
      rw [Nat.succ_mul] at H; omega
    simpa only [rowSchedule,readWord_bit,Nat.add_assoc] using (get2 _ hb).trans (sched_get cr j i)
  · change colSchedule x = cc
    funext j
    apply word_ext; intro i
    have hb : j.val*k+i.val < r*k := by
      have H := Nat.mul_le_mul_right k (Nat.succ_le_of_lt j.isLt)
      rw [Nat.succ_mul] at H; omega
    simpa only [colSchedule,readWord_bit,Nat.add_assoc] using (get3 _ hb).trans (sched_get cc j i)
  · have ho : off.val < 2^k := off.isLt.trans Nat.lt_two_pow_self
    suffices hw : offsetWord x = (⟨off.val,ho⟩ : Fin (2^k)) from congrArg Fin.val hw
    apply word_ext; intro i
    exact (readWord_bit k _ x i).trans ((get4 i.val i.isLt).trans (bits_get k _ _ i.isLt))
  · change bankBit x = bank
    funext j
    have H := get5 j.val j.isLt
    simpa [bankBit,List.getD_eq_getElem?_getD,List.getElem?_eq_getElem,j.isLt] using H
  · change target x = y
    apply word_ext; intro i
    exact (readWord_bit (m) _ x i).trans ((get6 i.val i.isLt).trans (bits_get (m) _ _ i.isLt))
  · change threshold x = t
    apply word_ext; intro i
    exact (readWord_bit (k+1) _ x i).trans ((get7 i.val i.isLt).trans (bits_get (k+1) _ _ i.isLt))
end PEqualNP.Outside.L_meta_33635.ScheduledLayout

namespace PEqualNP.Outside.L_meta_33635.ScheduledLayout
open PEqualNP.Outside.L_meta_33635 Builder Compiler

private theorem andFold {α : Type*} (l : List α) (f : α → Bool) (b : Bool) :
    l.foldl (fun z i => z && f i) b = (b && l.all f) := by
  induction l generalizing b with
  | nil => simp
  | cons i l ih => simp [List.foldl_cons, ih, Bool.and_assoc]

def validFlag {k r q m : ℕ} (d : ℕ) (x : Env (inLen k r q m)) : Bool :=
  decide (∀ j : Fin q, (if bankBit x j then 7*r-2 else 5*r-3) ≤ d)

theorem valid_wires {k r q m : ℕ} (d : ℕ) (B : Bank (inLen k r q m))
    (ext : (Bank.empty _).Ext B) (hz : B.Has (fun _ => false)) (ho : B.Has (fun _ => true)) :
    B.Grow (5*q+1) (fun E => E.Has (validFlag d)) := by
  let test (j : Fin q) (x : Env (inLen k r q m)) :=
    decide ((if bankBit x j then 7*r-2 else 5*r-3) ≤ d)
  have const (b : Bool) : B.Has (fun _ => b) := by cases b <;> assumption
  obtain ⟨C,eC,kC,hs⟩ := B.collectFin q test 4 (by
    intro E e j
    have hb := e (empty_raw B ext hz (3*k+2*r*k+j.val))
    apply (Bank.mux hb (e (const (decide (7*r-2 ≤ d)))) (e (const (decide (5*r-3 ≤ d))))).weaken (le_refl _)
    intro F hF
    have eq : (fun x => if raw x (3*k+2*r*k+j.val) then decide (7*r-2 ≤ d) else decide (5*r-3 ≤ d)) =
        test j := by
      funext x
      cases h : raw x (3*k+2*r*k+j.val) <;> simp [test,bankBit,h]
    rwa [← eq])
  obtain ⟨E,eE,kE,ans⟩ := C.andList (List.finRange q) test (fun j _ => hs j)
  refine ⟨E, Bank.ext_trans eC eE, ?_, ?_⟩
  · simp at kE; omega
  · have eq : (fun x => (List.finRange q).foldl (fun b i => b && test i x) true) =
        (validFlag (k:=k) (r:=r) (q:=q) (m:=m) d) := by
      funext x
      rw [andFold]
      apply Bool.eq_iff_iff.mpr
      simp [test,validFlag]
    rwa [← eq]

end PEqualNP.Outside.L_meta_33635.ScheduledLayout

namespace PEqualNP.Outside.L_meta_33635.SensorBuilder

open Builder Pivot.Word

private lemma foldl_apply' {α β γ : Type} (op : γ → α → β → γ) (init : β → γ)
    (l : List α) (x : β) :
    (l.foldl (fun acc a y => op (acc y) a y) init) x =
      l.foldl (fun acc a => op acc a x) (init x) := by
  induction l generalizing init with
  | nil => rfl
  | cons a l ih => simp only [List.foldl_cons, ih]

private lemma has_congr {n : Nat} {B : Bank n} {f g : BitFn n}
    (h : B.Has f) (heq : ∀ x, f x = g x) : B.Has g := by
  obtain ⟨i, hi, hf⟩ := h; exact ⟨i, hi, fun x => (hf x).trans (heq x)⟩

theorem grow_stateBits {n k r : Nat} (hk : 0 < k) (col : Bool) (B : Bank n)
    (w u : (Fin n → Bool) → Fin (2 ^ k)) (c : (Fin n → Bool) → Fin r → Fin (2 ^ k))
    (hw : ∀ i : Fin k, B.Has (fun x => (w x).val.testBit i.val))
    (hu : ∀ i : Fin k, B.Has (fun x => (u x).val.testBit i.val))
    (hc : ∀ (j : Fin r) (i : Fin k), B.Has (fun x => (c x j).val.testBit i.val)) :
    B.Grow (k * 4 + r * (k * 22))
      (fun D => ∀ i : Fin k, D.Has (fun x => (state k r col (w x).val (u x).val (c x)).testBit i.val)) := by
  let g := if col then 2 else 1
  let s0 : (Fin n → Bool) → Nat := fun x => rot k (if col then 3 else 1) (w x).val ^^^ (u x).val
  have hs0_lt : ∀ x, s0 x < 2 ^ k := fun x => xor_lt (rot_lt k _ _) (u x).isLt
  have hinit : B.Grow (k * 4) (fun D => ∀ i : Fin k, D.Has (fun x => (s0 x).testBit i.val)) := by
    apply B.collectFin k (fun i x => (s0 x).testBit i.val) 4
    intro D e i
    let idx : Fin k := ⟨(i.val + k - (if col then 3 else 1) % k) % k, Nat.mod_lt _ hk⟩
    apply (Bank.xor2 (e (hw idx)) (e (hu i))).weaken (le_refl _)
    intro E hE
    exact has_congr hE (fun x => by
      simp only [s0, Nat.testBit_xor, testBit_rot (w x).isLt i.isLt, idx])
  apply hinit.bind (b := r * (k * 22))
  intro D0 e0 hD0
  let stepFn : ((Fin n → Bool) → Nat) → Fin r → (Fin n → Bool) → Nat :=
    fun cur j x => step k (cur x ^^^ rot k g (cur x) ^^^ rot k (k - g) (cur x)) ^^^
      rot k (if col then 3 * (j.val + 1) + 1 else 2 * j.val) (w x).val ^^^ (c x j).val
  have hfold := Bank.foldGrow D0 (List.finRange r) s0 stepFn
    (fun cur D => (∀ x, cur x < 2 ^ k) ∧ ∀ i : Fin k, D.Has (fun x => (cur x).testBit i.val))
    (k * 22) ⟨hs0_lt, hD0⟩ (by
      intro D e cur j _ ⟨hcur_lt, hcur⟩
      let t1 : (Fin n → Bool) → Nat := fun x => cur x ^^^ rot k g (cur x)
      let t2 : (Fin n → Bool) → Nat := fun x => t1 x ^^^ rot k (k - g) (cur x)
      let t3 : (Fin n → Bool) → Nat := fun x => step k (t2 x)
      let t4 : (Fin n → Bool) → Nat := fun x => t3 x ^^^ rot k (if col then 3 * (j.val + 1) + 1 else 2 * j.val) (w x).val
      obtain ⟨E1, e1, c1, h1⟩ := D.collectFin k (fun i x => (t1 x).testBit i.val) 4 (fun E e' i => by
        let idx : Fin k := ⟨(i.val + k - g % k) % k, Nat.mod_lt _ hk⟩
        apply (Bank.xor2 (e' (hcur i)) (e' (hcur idx))).weaken (le_refl _)
        intro F hF
        exact has_congr hF (fun x => by simp only [t1, Nat.testBit_xor, testBit_rot (hcur_lt x) i.isLt, idx]))
      obtain ⟨E2, e2, c2, h2⟩ := E1.collectFin k (fun i x => (t2 x).testBit i.val) 4 (fun E e' i => by
        let idx : Fin k := ⟨(i.val + k - (k - g) % k) % k, Nat.mod_lt _ hk⟩
        apply (Bank.xor2 (e' (h1 i)) (e' (e1 (hcur idx)))).weaken (le_refl _)
        intro F hF
        exact has_congr hF (fun x => by simp only [t2, Nat.testBit_xor, testBit_rot (hcur_lt x) i.isLt, idx]))
      obtain ⟨E3, e3, c3, h3⟩ := E2.collectFin k (fun i x => (t3 x).testBit i.val) 6 (fun E e' i => by
        let i1 : Fin k := ⟨(i.val + 1) % k, Nat.mod_lt _ hk⟩
        let i2 : Fin k := ⟨(i.val + 2) % k, Nat.mod_lt _ hk⟩
        obtain ⟨F1, ef1, cf1, hnot⟩ := Bank.inv (e' (h2 i1))
        obtain ⟨F2, ef2, cf2, hand⟩ := Bank.meet hnot (ef1 (e' (h2 i2)))
        obtain ⟨F3, ef3, cf3, hxr⟩ := Bank.xor2 (ef2 (ef1 (e' (h2 i)))) hand
        exact ⟨F3, Bank.ext_trans ef1 (Bank.ext_trans ef2 ef3), by omega,
          has_congr hxr (fun x => by simp only [t3, testBit_step i.isLt, stepBit, i1, i2])⟩)
      obtain ⟨E4, e4, c4, h4⟩ := E3.collectFin k (fun i x => (t4 x).testBit i.val) 4 (fun E e' i => by
        let idx : Fin k := ⟨(i.val + k - (if col then 3 * (j.val + 1) + 1 else 2 * j.val) % k) % k, Nat.mod_lt _ hk⟩
        apply (Bank.xor2 (e' (h3 i)) (e' (e3 (e2 (e1 (e (e0 (hw idx)))))))).weaken (le_refl _)
        intro F hF
        exact has_congr hF (fun x => by simp only [t4, Nat.testBit_xor, testBit_rot (w x).isLt i.isLt, idx]))
      obtain ⟨E5, e5, c5, h5⟩ := E4.collectFin k (fun i x => (stepFn cur j x).testBit i.val) 4 (fun E e' i => by
        apply (Bank.xor2 (e' (h4 i)) (e' (e4 (e3 (e2 (e1 (e (e0 (hc j i))))))))).weaken (le_refl _)
        intro F hF
        exact has_congr hF (fun x => by simp only [stepFn, t4, t3, t2, t1, Nat.testBit_xor]))
      exact ⟨E5, Bank.ext_trans e1 (Bank.ext_trans e2 (Bank.ext_trans e3 (Bank.ext_trans e4 e5))),
        by omega, fun x => xor_lt (xor_lt (step_lt k _) (rot_lt k _ _)) (c x j).isLt, h5⟩)
  refine hfold.weaken (by simp) (fun D hD i => ?_)
  exact has_congr (hD.2 i) (fun x => by
    have hfl := foldl_apply' (fun acc j x => stepFn (fun _ => acc) j x) s0 (List.finRange r) x
    have hfeq : (List.finRange r).foldl stepFn s0 x = state k r col (w x).val (u x).val (c x) := by
      have : (List.finRange r).foldl stepFn s0 =
          (List.finRange r).foldl (fun acc j y => stepFn (fun _ => acc y) j y) s0 := by
        rfl
      rw [this, hfl]; rfl
    rw [hfeq])

theorem localSensor {n k r : ℕ} (hk : 0 < k) (B : Bank n)
    (w : Fin (2^k)) (nr nc : (Fin n → Bool) → Fin (2^k))
    (cr cc : (Fin n → Bool) → Fin r → Fin (2^k))
    (bank : BitFn n) (rowBit colBit : Fin k)
    (hw : ∀ i : Fin k, B.Has (fun _ => w.val.testBit i.val))
    (hr : ∀ i : Fin k, B.Has (fun x => (nr x).val.testBit i.val))
    (hc : ∀ i : Fin k, B.Has (fun x => (nc x).val.testBit i.val))
    (hsr : ∀ (j : Fin r) (i : Fin k), B.Has (fun x => (cr x j).val.testBit i.val))
    (hsc : ∀ (j : Fin r) (i : Fin k), B.Has (fun x => (cc x j).val.testBit i.val))
    (hb : B.Has bank) :
    B.Grow ((k*4+r*(k*22)) + ((k*4+r*(k*22)) + 4))
      (fun D => D.Has (fun x =>
        (state k r (bank x) w.val (if bank x then (nc x).val else (nr x).val)
          (if bank x then cc x else cr x)).testBit (if bank x then colBit.val else rowBit.val))) := by
  apply (grow_stateBits hk false B (fun _ => w) nr cr hw hr hsr).bind
  intro R eR rows
  apply (grow_stateBits hk true R (fun _ => w) nc cc (fun i => eR (hw i))
    (fun i => eR (hc i)) (fun j i => eR (hsc j i))).bind
  intro T eT cols
  apply (Bank.mux (eT (eR hb)) (cols colBit) (eT (rows rowBit))).weaken (le_refl _)
  intro D wire
  apply has_congr wire
  intro x
  cases bank x <;> simp

theorem collectType {n : ℕ} {A : Type} [Fintype A] (B : Bank n)
    (f : A → BitFn n) (cost : ℕ)
    (emit : ∀ D : Bank n, B.Ext D → ∀ a, D.Grow cost (fun E => E.Has (f a))) :
    B.Grow (Fintype.card A * cost) (fun D => ∀ a, D.Has (f a)) := by
  classical
  let e := Fintype.equivFin A
  apply (B.collectFin (Fintype.card A) (fun j => f (e.symm j)) cost
    (fun D h j => emit D h (e.symm j))).weaken (le_refl _)
  intro D h a
  simpa using h (e a)

theorem labelTable {n k r q : ℕ} {S : Type} [Fintype S]
    (hk : 0 < k) (B : Bank n) (rep : Fin q × S × S → Fin (2^k))
    (nr nc : (Fin n → Bool) → Fin (2^k))
    (cr cc : (Fin n → Bool) → Fin r → Fin (2^k))
    (bank : Fin q → BitFn n) (selected : Fin q → Bool) (rowBit colBit : Fin q → Fin k)
    (hconst : ∀ b : Bool, B.Has (fun _ => b))
    (hr : ∀ i : Fin k, B.Has (fun x => (nr x).val.testBit i.val))
    (hc : ∀ i : Fin k, B.Has (fun x => (nc x).val.testBit i.val))
    (hsr : ∀ (j : Fin r) (i : Fin k), B.Has (fun x => (cr x j).val.testBit i.val))
    (hsc : ∀ (j : Fin r) (i : Fin k), B.Has (fun x => (cc x j).val.testBit i.val))
    (hb : ∀ i, B.Has (bank i)) :
    B.Grow (Fintype.card (Fin q × S × S) * ((k*4+r*(k*22)) + ((k*4+r*(k*22)) + 4)))
      (fun D => ∀ z : Fin q × S × S,
        D.Has (fun x => if selected z.1 then
          (state k r (bank z.1 x) (rep z).val (if bank z.1 x then (nc x).val else (nr x).val)
           (if bank z.1 x then cc x else cr x)).testBit
           (if bank z.1 x then (colBit z.1).val else (rowBit z.1).val)
          else false)) := by
  apply collectType
  intro D e z
  cases hs : selected z.1 with
  | false =>
    simpa using (Bank.Grow.pure D (e (hconst false))).weaken (Nat.zero_le _) (fun _ h => h)
  | true =>
    simpa using localSensor hk D (rep z) nr nc cr cc (bank z.1) (rowBit z.1) (colBit z.1)
      (fun i => e (hconst ((rep z).val.testBit i.val))) (fun i => e (hr i))
      (fun i => e (hc i)) (fun j i => e (hsr j i)) (fun j i => e (hsc j i)) (e (hb z.1))

end PEqualNP.Outside.L_meta_33635.SensorBuilder

namespace PEqualNP.Outside.L_meta_33635.ScheduledWalsh

abbrev Word (m : ℕ) := Fin (2^m)

def sign (b : Bool) : ℤ := if b then -1 else 1

def par (m mask x : ℕ) : Bool :=
  (List.range m).foldl (fun b i => xor b (mask.testBit i && x.testBit i)) false

theorem par_succ (m a x : ℕ) : par (m+1) a x =
    xor (par m a x) (a.testBit m && x.testBit m) := by
  simp [par, List.range_succ]

theorem sign_xor (a b : Bool) : sign (xor a b) = sign a * sign b := by
  cases a <;> cases b <;> decide

@[simp] theorem sign_sq (a : Bool) : sign a * sign a = 1 := by cases a <;> decide

@[simp] theorem sign_not (a : Bool) : sign (!a) = -sign a := by cases a <;> decide

theorem par_comm (m a b : ℕ) : par m a b = par m b a := by
  induction m with
  | zero => rfl
  | succ m ih => simp only [par_succ, ih, Bool.and_comm]

theorem par_xor (m a b x : ℕ) : par m (a ^^^ b) x = xor (par m a x) (par m b x) := by
  induction m with
  | zero => rfl
  | succ m ih =>
    simp only [par_succ, ih, Nat.testBit_xor]
    cases par m a x <;> cases par m b x <;> cases a.testBit m <;> cases b.testBit m <;>
      cases x.testBit m <;> rfl

@[simp] theorem par_zero (m x : ℕ) : par m 0 x = false := by
  induction m with
  | zero => rfl
  | succ m ih => simp [par_succ, ih]

theorem par_single (m i x : ℕ) : par m (2^i) x = if i < m then x.testBit i else false := by
  induction m with
  | zero => simp [par]
  | succ m ih =>
    rw [par_succ, ih, Nat.testBit_two_pow]
    rcases lt_trichotomy i m with h | rfl | h
    · simp [h, h.ne, Nat.lt_succ_of_lt h]
    · simp
    · simp [show ¬i<m by omega, Ne.symm h.ne, show ¬i<m+1 by omega]

def flip {m : ℕ} (i : Fin m) : Word m ≃ Word m :=
  let f (w : Word m) : Word m := ⟨w.val ^^^ 2^i.val, Nat.xor_lt_two_pow w.isLt
    (Nat.pow_lt_pow_right (by decide) i.isLt)⟩
  have invol (w : Word m) : f (f w) = w := Fin.ext (by simp [f, Nat.xor_assoc])
  ⟨f, f, invol, invol⟩

theorem flip_bit {m : ℕ} (i : Fin m) (x : Word m) (j : Nat) :
    ((flip i x).val).testBit j = xor (x.val.testBit j) (decide (i.val=j)) := by
  simp [flip, Nat.testBit_two_pow]

theorem signed_sum_cancel {W : Type*} [Fintype W] (e : W ≃ W) (f : W → ℤ)
    (neg : ∀ w, f (e w) = -(f w)) : ∑ w, f w = 0 := by
  have h := e.sum_comp f
  simp only [neg, Finset.sum_neg_distrib] at h
  omega

private theorem different_bit {m : ℕ} {x y : Word m} (hxy : x ≠ y) :
    ∃ i : Fin m, x.val.testBit i.val ≠ y.val.testBit i.val := by
  by_contra! nope
  apply hxy
  apply Fin.ext
  apply Nat.eq_of_testBit_eq
  intro j
  by_cases hj : j < m
  · exact nope ⟨j,hj⟩
  · have le := Nat.pow_le_pow_right (by decide : 0 < 2) (Nat.le_of_not_gt hj)
    rw [Nat.testBit_lt_two_pow (x.isLt.trans_le le), Nat.testBit_lt_two_pow (y.isLt.trans_le le)]

theorem orthogonality {m : ℕ} (x y : Word m) :
    (∑ a : Word m, sign (par m a.val x.val) * sign (par m a.val y.val)) =
      if x = y then (2:ℤ)^m else 0 := by
  by_cases hxy : x = y
  · subst y
    simp [Word]
  · simp only [hxy, ↓reduceIte]
    obtain ⟨i,hi⟩ := different_bit hxy
    apply signed_sum_cancel (flip i)
    intro w
    change sign (par m (w.val ^^^ 2^i.val) x.val) * sign (par m (w.val ^^^ 2^i.val) y.val) = _
    simp only [par_xor, par_single, i.isLt, ↓reduceIte, sign_xor]
    cases hx : x.val.testBit i.val <;> cases hy : y.val.testBit i.val <;>
      cases par m w.val x.val <;> cases par m w.val y.val <;> simp_all [sign]

theorem fiber_inversion {W : Type*} [Fintype W] {m : ℕ} (f : W → Word m) (y : Word m) :
    (2:ℤ)^m * (Nat.card {w : W // f w = y} : ℤ) =
      ∑ a : Word m, sign (par m a.val y.val) * ∑ w, sign (par m a.val (f w).val) := by
  classical
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  simp_rw [orthogonality]
  have count : (∑ w : W, if y = f w then (1:ℤ) else 0) =
      (Nat.card {w : W // f w = y} : ℤ) := by
    simp [Nat.card_eq_fintype_card, Fintype.card_subtype, eq_comm]
  rw [← count, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro w _
  split_ifs <;> simp

theorem par_xor_right (m a x y : ℕ) :
    par m a (x ^^^ y) = xor (par m a x) (par m a y) := by
  rw [par_comm m a (x ^^^ y), par_xor, par_comm m x a, par_comm m y a]

def report {W : Type*} {q : ℕ} (col : Fin q → ℕ) (sensor : Fin q → W → Bool) (w : W) : ℕ :=
  (List.finRange q).foldl (fun z i => if sensor i w then z ^^^ col i else z) 0

def factor {W : Type*} {q : ℕ} (m a : ℕ)
    (col : Fin q → ℕ) (sensor : Fin q → W → Bool) (w : W) (i : Fin q) : ℤ :=
  if par m a (col i) then sign (sensor i w) else 1

theorem report_product {W : Type*} {q : ℕ} (m a : ℕ)
    (col : Fin q → ℕ) (sensor : Fin q → W → Bool) (w : W) :
    sign (par m a (report col sensor w)) = ∏ i, factor m a col sensor w i := by
  have fold (xs : List (Fin q)) (acc : ℕ) :
      sign (par m a (xs.foldl (fun z i => if sensor i w then z ^^^ col i else z) acc)) =
      sign (par m a acc) * (xs.map (factor m a col sensor w)).prod := by
    induction xs generalizing acc with
    | nil => simp
    | cons i xs ih =>
      simp only [List.foldl_cons, List.map_cons, List.prod_cons]
      rw [ih, ← mul_assoc]
      apply congrArg (· * _)
      cases h : sensor i w <;> cases b : par m a (col i) <;> cases c : par m a acc <;>
        simp [h, b, c, factor, par_xor_right, sign]
  have first := fold (List.finRange q) 0
  rw [par_comm m a 0, par_zero] at first
  rw [show sign false = 1 by rfl, one_mul] at first
  rw [Fin.prod_univ_def]
  exact first

theorem cancel_sensor {W : Type*} [Fintype W] {q : ℕ} (m a : ℕ)
    (col : Fin q → ℕ) (sensor : Fin q → W → Bool) (keyFlip : W ≃ W) (i : Fin q)
    (selected : par m a (col i) = true)
    (pivot : ∀ w, sensor i (keyFlip w) = !sensor i w)
    (others : ∀ j, j ≠ i → par m a (col j) = true → ∀ w, sensor j (keyFlip w) = sensor j w) :
    (∑ w, sign (par m a (report col sensor w))) = 0 := by
  apply signed_sum_cancel keyFlip
  intro w
  rw [report_product, report_product]
  let F := factor m a col sensor
  change (∏ j, F (keyFlip w) j) = -(∏ j, F w j)
  rw [← Finset.mul_prod_erase Finset.univ (F (keyFlip w)) (Finset.mem_univ i),
      ← Finset.mul_prod_erase Finset.univ (F w) (Finset.mem_univ i)]
  have hi : F (keyFlip w) i = -F w i := by simp [F, factor, selected, pivot]
  have rest : ∏ j ∈ Finset.univ.erase i, F (keyFlip w) j =
      ∏ j ∈ Finset.univ.erase i, F w j := by
    apply Finset.prod_congr rfl
    intro j hj
    cases s : par m a (col j) with
    | false => simp [F, factor, s]
    | true => simp [F, factor, s, others j (Finset.mem_erase.mp hj).1 s]
  rw [hi, rest, neg_mul]

theorem fiber_pruned {C : Type*} {k m : ℕ} (colors : Finset C)
    (enc : C → Word m) (inj : Function.Injective enc)
    (nonzero : ∀ c ∈ colors, (enc c).val ≠ 0)
    (f : Word k → ℕ) (bound : ∀ w, f w < 2^m)
    (drop : ∀ a : Word m, a.val ≠ 0 → (∀ c ∈ colors, enc c ≠ a) →
      (∑ w : Word k, sign (par m a.val (f w))) = 0) (y : Word m) :
    (2:ℤ)^m * (Nat.card {w : Word k // f w = y.val} : ℤ) =
      (2:ℤ)^k + ∑ c ∈ colors, sign (par m (enc c).val y.val) *
        ∑ w : Word k, sign (par m (enc c).val (f w)) := by
  classical
  let F (w : Word k) : Word m := ⟨f w, bound w⟩
  let term (a : Word m) := sign (par m a.val y.val) * ∑ w : Word k, sign (par m a.val (f w))
  have h := fiber_inversion F y
  have same : {w : Word k // F w = y} = {w : Word k // f w = y.val} := by
    congr 1
    funext w
    exact propext Fin.ext_iff
  rw [same] at h
  change (2:ℤ)^m * _ = ∑ a, term a at h
  rw [h]
  let z : Word m := ⟨0, Nat.two_pow_pos m⟩
  have hz : z ∉ colors.image enc := by
    intro bad
    obtain ⟨c,hc,e⟩ := Finset.mem_image.mp bad
    exact nonzero c hc (congrArg Fin.val e)
  have restrict : ∑ a, term a = ∑ a ∈ insert z (colors.image enc), term a := by
    symm
    apply Finset.sum_subset (Finset.subset_univ _)
    intro a _ outside
    have hn : a.val ≠ 0 := by
      intro zero
      exact outside (Finset.mem_insert.mpr (Or.inl (Fin.ext zero)))
    have ha : ∀ c ∈ colors, enc c ≠ a := by
      intro c hc hca
      exact outside (Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨c,hc,hca⟩))
    simp [term, drop a hn ha]
  rw [restrict, Finset.sum_insert hz, Finset.sum_image (fun _ _ _ _ eq => inj eq)]
  have base : term z = (2:ℤ)^k := by simp [term,z,sign,Word]
  rw [base]

theorem uniform_hit {m k h : ℕ} (width : m ≤ k)
    (eqn : (2:ℤ)^m * (h:ℤ) = (2:ℤ)^k) : h = 2^(k-m) := by
  have p : (2:ℤ)^m * (h:ℤ) = (2:ℤ)^m * (2:ℤ)^(k-m) := by
    rw [eqn, ← pow_add, Nat.add_sub_of_le width]
  have pos : (2:ℤ)^m ≠ 0 := by simp
  exact_mod_cast mul_left_cancel₀ pos p

end PEqualNP.Outside.L_meta_33635.ScheduledWalsh

namespace PEqualNP.Outside.L_meta_33635.ScheduledLabels

open PEqualNP.Outside.L_meta_33635.Pivot

def relative {k : ℕ} (p : Fin k) (j : ℕ) : ℕ := (j + (k-p.val)) % k

theorem relative_at {k : ℕ} (p : Fin k) {a : ℕ} (ha : a < k) :
    relative p ((p.val+a)%k) = a := by
  unfold relative
  rw [Nat.mod_add_mod]
  have h : p.val+a+(k-p.val) = a+k := by have := p.isLt; omega
  rw [h, Nat.add_mod_right, Nat.mod_eq_of_lt ha]

def representativeBit {k width : ℕ} (p : Fin k) (localBits : Fin width → Bool) (j : ℕ) : Bool :=
  if h : relative p j < width then localBits ⟨relative p j,h⟩ else false

def representative {k width : ℕ} (p : Fin k) (localBits : Fin width → Bool) : Fin (2^k) :=
  ⟨(List.range k).foldl (fun acc j => acc ||| ((representativeBit p localBits j).toNat <<< j)) 0, by
    apply Nat.lt_pow_two_of_testBit
    intro j hj
    rw [Word.testBit_foldl_or]
    simp [Nat.not_lt_of_ge hj]⟩

theorem get_representative {k width : ℕ} (p : Fin k) (localBits : Fin width → Bool)
    {j : ℕ} (hj : j < k) :
    (representative p localBits).val.testBit j = representativeBit p localBits j := by
  unfold representative
  rw [Word.testBit_foldl_or]
  simp [hj]

theorem bit_at {k width : ℕ} (p : Fin k) (localBits : Fin width → Bool)
    (hw : width ≤ k) (a : Fin width) :
    (representative p localBits).val.testBit ((p.val+a.val)%k) = localBits a := by
  rw [get_representative _ _ (Nat.mod_lt _ (by have := p.isLt; omega))]
  simp [representativeBit, relative_at p (lt_of_lt_of_le a.isLt hw), a.isLt]

theorem sensor_representative {q s r width : ℕ} (hs : 0 < s) (hk : 2 ≤ q*s) (hr : 4 ≤ r)
    (nr nc : Fin (2^(q*s))) (cr cc : Fin r → Fin (2^(q*s)))
    (off : Fin (q*s)) (bank : Fin q → Bool) (i : Fin q)
    (localBits : Fin width → Bool) (w : Fin (2^(q*s))) (hw : width ≤ q*s)
    (hreach : (if bank i then 7*r-2 else 5*r-3) < width)
    (agree : ∀ a : Fin width, localBits a = w.val.testBit (((site hs off i).val+a.val)%(q*s))) :
    sensor hs nr nc cr cc off bank i (representative (site hs off i) localBits) =
      sensor hs nr nc cr cc off bank i w := by
  let p := site hs off i
  let z := representative p localBits
  have bits (a : ℕ) (ha : a < width) :
      z.val.testBit ((p.val+a)%(q*s)) = w.val.testBit ((p.val+a)%(q*s)) :=
    (bit_at p localBits hw ⟨a,ha⟩).trans (agree ⟨a,ha⟩)
  have pivot : z.val.testBit p.val = w.val.testBit p.val := by
    simpa only [Nat.add_zero, Nat.mod_eq_of_lt p.isLt] using bits 0 (by omega)
  have h := word_sensor_xor hk hr (bank i) z w (if bank i then nc else nr)
    (if bank i then cc else cr) p (fun a _ ha => bits a (lt_of_le_of_lt ha hreach))
  rw [pivot, Bool.xor_self] at h
  have same (a b : Bool) : xor a b = false → a = b := by cases a <;> cases b <;> decide
  apply same
  simpa only [sensor, p, z, apply_ite Fin.val] using h

end PEqualNP.Outside.L_meta_33635.ScheduledLabels

namespace PEqualNP.Outside.L_meta_33635.ScheduledWindows

abbrev Word (n : ℕ) := Fin n → Bool

def linearPos {q s : ℕ} (i : Fin q) (j : Fin s) : Fin (q*s) :=
  ⟨i.val*s+j.val, by
    have h := Nat.mul_le_mul_right s (show i.val+1 ≤ q from i.isLt)
    rw [Nat.add_mul, Nat.one_mul] at h
    have := j.isLt
    omega⟩

def regroup {q s : ℕ} (hs : 0 < s) : Word (q*s) ≃ (Fin q → Word s) where
  toFun x i j := x (linearPos i j)
  invFun y i := y ⟨i.val/s, (Nat.div_lt_iff_lt_mul hs).mpr i.isLt⟩
    ⟨i.val % s, Nat.mod_lt _ hs⟩
  left_inv x := by
    funext j
    apply congrArg x
    apply Fin.ext
    change j.val/s*s+j.val % s=j.val
    simpa [Nat.mul_comm, Nat.add_comm] using Nat.mod_add_div j.val s
  right_inv f := by
    funext i j
    change f ⟨(i.val*s+j.val)/s, _⟩ ⟨(i.val*s+j.val)%s, _⟩ = f i j
    congr 1
    · apply Fin.ext
      simp [Nat.add_comm _ j.val, Nat.add_mul_div_right, Nat.div_eq_of_lt j.isLt, hs]
    · apply Fin.ext
      simp [Nat.mod_eq_of_lt j.isLt]

def next {q : ℕ} (hq : 0 < q) (i : Fin q) : Fin q :=
  ⟨(i.val+1)%q, Nat.mod_lt _ hq⟩

def window {q s : ℕ} (hq : 0 < q) (hs : 0 < s)
    (x : Word (q*s)) (i : Fin q) (l : ℕ) : Word l :=
  fun j => x ⟨(i.val*s+j.val)%(q*s), Nat.mod_lt _ (Nat.mul_pos hq hs)⟩

theorem step_index {q s : ℕ} (hq : 0 < q) (_hs : 0 < s)
    (i : Fin q) (t : ℕ) (ht : s ≤ t) :
    (i.val*s+t)%(q*s) = ((next hq i).val*s+(t-s))%(q*s) := by
  have hts := Nat.sub_add_cancel ht
  by_cases hi : i.val+1 < q
  · simp only [next, Nat.mod_eq_of_lt hi]
    congr 1
    rw [Nat.add_mul, Nat.one_mul]
    omega
  · have hi' : i.val+1=q := by have := i.isLt; omega
    have hn : (next hq i).val=0 := by simp [next, hi']
    rw [hn, Nat.zero_mul, Nat.zero_add]
    have he : i.val*s+t=q*s+(t-s) := by
      have heq := congrArg (fun n => n*s) hi'
      rw [Nat.add_mul, Nat.one_mul] at heq
      omega
    rw [he, Nat.add_mod]
    simp

theorem window_first {q s : ℕ} (hq : 0 < q) (hs : 0 < s)
    (x : Word (q*s)) (i : Fin q) (l : ℕ) (j : Fin l) (hj : j.val < s) :
    window hq hs x i l j = regroup hs x i ⟨j.val,hj⟩ := by
  apply congrArg x
  apply Fin.ext
  exact Nat.mod_eq_of_lt (linearPos i ⟨j.val,hj⟩).isLt

theorem window_step {q s : ℕ} (hq : 0 < q) (hs : 0 < s)
    (x : Word (q*s)) (i : Fin q) (l : ℕ) (j : Fin l) (hj : s ≤ j.val) :
    window hq hs x i l j =
      window hq hs x (next hq i) l ⟨j.val-s, by have := j.isLt; omega⟩ := by
  apply congrArg x
  apply Fin.ext
  exact step_index hq hs i j.val hj

def Compatible {s l : ℕ} (a : Word l) (t : Word s) (b : Word l) : Prop :=
  ∀ j : Fin l, a j = if h : j.val < s then t ⟨j.val,h⟩
    else b ⟨j.val-s, by have := j.isLt; omega⟩

theorem window_compatible {q s : ℕ} (hq : 0 < q) (hs : 0 < s)
    (x : Word (q*s)) (i : Fin q) (l : ℕ) :
    Compatible (window hq hs x i l) (regroup hs x i)
      (window hq hs x (next hq i) l) := by
  intro j
  split
  · exact window_first hq hs x i l j ‹_›
  · exact window_step hq hs x i l j (by omega)

abbrev LabelledCycle {q s : ℕ} (hq : 0 < q) (l : ℕ) :=
  {p : (Fin q → Word l) × (Fin q → Word s) //
    ∀ i, Compatible (p.1 i) (p.2 i) (p.1 (next hq i))}

theorem states_unique {q s l : ℕ} (hq : 0 < q) (hs : 0 < s)
    (a b : Fin q → Word l) (t : Fin q → Word s)
    (ha : ∀ i, Compatible (a i) (t i) (a (next hq i)))
    (hb : ∀ i, Compatible (b i) (t i) (b (next hq i))) : a=b := by
  have h : ∀ n, ∀ hn : n < l, ∀ i : Fin q, a i ⟨n,hn⟩ = b i ⟨n,hn⟩ := by
    intro n
    induction n using Nat.strong_induction_on with
    | ind n ih =>
      intro hn i
      rw [ha i ⟨n,hn⟩, hb i ⟨n,hn⟩]
      by_cases hns : n < s
      · simp only [hns, ↓reduceDIte]
      · simp only [hns, ↓reduceDIte]
        exact ih (n-s) (by omega) (by omega) (next hq i)
  funext i j
  exact h j.val j.isLt i

def keyCycleEquiv {q s : ℕ} (hq : 0 < q) (hs : 0 < s) (l : ℕ) :
    Word (q*s) ≃ LabelledCycle (s:=s) hq l where
  toFun x := ⟨(fun i => window hq hs x i l, regroup hs x),
    fun i => window_compatible hq hs x i l⟩
  invFun p := (regroup hs).symm p.val.2
  left_inv x := (regroup hs).symm_apply_apply x
  right_inv p := by
    apply Subtype.ext
    apply Prod.ext
    · apply states_unique hq hs _ _ p.val.2
      · intro i
        have h := window_compatible hq hs ((regroup hs).symm p.val.2) i l
        simpa only [Equiv.apply_symm_apply] using h
      · exact p.property
    · exact (regroup hs).apply_symm_apply p.val.2

def edgeWindow {s l : ℕ} (t : Word s) (b : Word l) : Word (l+s) :=
  fun j => if h : j.val < s then t ⟨j.val,h⟩
    else b ⟨j.val-s, by have := j.isLt; omega⟩

theorem edgeWindow_keyCycle {q s : ℕ} (hq : 0 < q) (hs : 0 < s)
    (x : Word (q*s)) (i : Fin q) (l : ℕ) :
    edgeWindow ((keyCycleEquiv hq hs l x).val.2 i)
      ((keyCycleEquiv hq hs l x).val.1 (next hq i)) = window hq hs x i (l+s) := by
  funext j
  change (if h : j.val < s then regroup hs x i ⟨j.val,h⟩
    else window hq hs x (next hq i) l ⟨j.val-s,_⟩) = _
  split
  · exact (window_first hq hs x i (l+s) j ‹_›).symm
  · apply congrArg x
    apply Fin.ext
    exact (step_index hq hs i j.val (by omega)).symm

def firstBits {s l : ℕ} (hsl : s ≤ l) (a : Word l) : Word s :=
  fun j => a ⟨j.val, lt_of_lt_of_le j.isLt hsl⟩

theorem compatible_label_unique {s l : ℕ} (hsl : s ≤ l)
    (a b : Word l) (t : Word s) (h : Compatible a t b) : t = firstBits hsl a := by
  funext j
  have hh := h ⟨j.val, lt_of_lt_of_le j.isLt hsl⟩
  simpa only [j.isLt, ↓reduceDIte, firstBits] using hh.symm

abbrev ClosedWindows {q s : ℕ} (hq : 0 < q) {l : ℕ} (hsl : s ≤ l) :=
  {a : Fin q → Word l // ∀ i, Compatible (a i) (firstBits hsl (a i)) (a (next hq i))}

def forgetLabels {q s l : ℕ} (hq : 0 < q) (hsl : s ≤ l) :
    LabelledCycle (s:=s) hq l ≃ ClosedWindows hq hsl where
  toFun p := ⟨p.val.1, by
    intro i
    have h := p.property i
    rwa [compatible_label_unique hsl _ _ _ h] at h⟩
  invFun a := ⟨(a.val, fun i => firstBits hsl (a.val i)), a.property⟩
  left_inv p := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · funext i
      exact (compatible_label_unique hsl _ _ _ (p.property i)).symm
  right_inv a := rfl

def keyClosedWindowsEquiv {q s l : ℕ} (hq : 0 < q) (hs : 0 < s) (hsl : s ≤ l) :
    Word (q*s) ≃ ClosedWindows hq hsl :=
  (keyCycleEquiv hq hs l).trans (forgetLabels hq hsl)

def bits (n : ℕ) (w : Fin (2^n)) : Word n := fun j => w.val.testBit j.val

theorem bits_injective (n : ℕ) : Function.Injective (bits n) := by
  intro a b h
  apply Fin.ext
  apply Nat.eq_of_testBit_eq
  intro j
  by_cases hj : j < n
  · exact congrFun h ⟨j,hj⟩
  · have hp : 2^n ≤ 2^j := Nat.pow_le_pow_right (by decide) (by omega)
    rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le a.isLt hp),
      Nat.testBit_lt_two_pow (lt_of_lt_of_le b.isLt hp)]

theorem bits_surjective (n : ℕ) : Function.Surjective (bits n) := by
  by_contra h
  have hh := Fintype.card_lt_of_injective_not_surjective (bits n) (bits_injective n) h
  simp [Word, Fintype.card_fun] at hh

noncomputable def bitsEquiv (n : ℕ) : Fin (2^n) ≃ Word n :=
  Equiv.ofBijective (bits n) ⟨bits_injective n, bits_surjective n⟩

noncomputable def numericKeyCycleEquiv {q s : ℕ} (hq : 0 < q) (hs : 0 < s) (l : ℕ) :
    Fin (2^(q*s)) ≃ LabelledCycle (s:=s) hq l :=
  (bitsEquiv (q*s)).trans (keyCycleEquiv hq hs l)

noncomputable def numericKeyClosedWindowsEquiv {q s l : ℕ}
    (hq : 0 < q) (hs : 0 < s) (hsl : s ≤ l) :
    Fin (2^(q*s)) ≃ ClosedWindows hq hsl :=
  (bitsEquiv (q*s)).trans (keyClosedWindowsEquiv hq hs hsl)

theorem numeric_edgeWindow {q s : ℕ} (hq : 0 < q) (hs : 0 < s)
    (x : Fin (2^(q*s))) (i : Fin q) (l : ℕ) (j : Fin (l+s)) :
    edgeWindow ((numericKeyCycleEquiv hq hs l x).val.2 i)
      ((numericKeyCycleEquiv hq hs l x).val.1 (next hq i)) j =
      x.val.testBit ((i.val*s+j.val)%(q*s)) := by
  change edgeWindow ((keyCycleEquiv hq hs l (bits (q*s) x)).val.2 i)
    ((keyCycleEquiv hq hs l (bits (q*s) x)).val.1 (next hq i)) j = _
  rw [edgeWindow_keyCycle]
  rfl

end PEqualNP.Outside.L_meta_33635.ScheduledWindows

namespace PEqualNP.Outside.L_meta_33635.ScheduledRotated

open ScheduledWindows ScheduledLabels PEqualNP.Outside.L_meta_33635.Pivot

def rotate {k : ℕ} (off : Fin k) : Word k ≃ Word k where
  toFun w j := w ⟨(off.val+j.val)%k, Nat.mod_lt _ (by have := off.isLt; omega)⟩
  invFun w j := w ⟨relative off j.val, Nat.mod_lt _ (by have := off.isLt; omega)⟩
  left_inv w := by
    funext j
    apply congrArg w
    apply Fin.ext
    change (off.val+(j.val+(k-off.val))%k)%k = j.val
    rw [Nat.add_mod_mod]
    have h : off.val+(j.val+(k-off.val)) = j.val+k := by have := off.isLt; omega
    rw [h, Nat.add_mod_right, Nat.mod_eq_of_lt j.isLt]
  right_inv w := by
    funext j
    apply congrArg w
    apply Fin.ext
    exact relative_at off j.isLt

noncomputable def labelled {q s : ℕ} (hq : 0 < q) (hs : 0 < s)
    (off : Fin (q*s)) (l : ℕ) : Fin (2^(q*s)) ≃ LabelledCycle (s:=s) hq l :=
  ((bitsEquiv (q*s)).trans (rotate off)).trans (keyCycleEquiv hq hs l)

noncomputable def closed {q s l : ℕ} (hq : 0 < q) (hs : 0 < s)
    (off : Fin (q*s)) (hsl : s ≤ l) : Fin (2^(q*s)) ≃ ClosedWindows hq hsl :=
  (labelled hq hs off l).trans (forgetLabels hq hsl)

theorem labelled_bit {q s : ℕ} (hq : 0 < q) (hs : 0 < s) (off : Fin (q*s))
    (l : ℕ) (w : Fin (2^(q*s))) (i : Fin q) (a : Fin (l+s)) :
    edgeWindow ((labelled hq hs off l w).val.2 i)
      ((labelled hq hs off l w).val.1 (next hq i)) a =
      w.val.testBit (((site hs off i).val + a.val)%(q*s)) := by
  change edgeWindow ((keyCycleEquiv hq hs l (rotate off (bits (q*s) w))).val.2 i)
    ((keyCycleEquiv hq hs l (rotate off (bits (q*s) w))).val.1 (next hq i)) a = _
  rw [edgeWindow_keyCycle]
  change w.val.testBit ((off.val+((i.val*s+a.val)%(q*s)))%(q*s)) = _
  simp only [site, Nat.add_mod_mod, Nat.mod_add_mod, Nat.add_assoc]

def localWindow {q s l : ℕ} (hq : 0 < q) (hsl : s ≤ l)
    (path : ClosedWindows hq hsl) (i : Fin q) : Word (l+s) :=
  edgeWindow (firstBits hsl (path.val i)) (path.val (next hq i))

theorem closed_bit {q s l : ℕ} (hq : 0 < q) (hs : 0 < s) (off : Fin (q*s))
    (hsl : s ≤ l) (w : Fin (2^(q*s))) (i : Fin q) (a : Fin (l+s)) :
    localWindow hq hsl (closed hq hs off hsl w) i a =
      w.val.testBit (((site hs off i).val+a.val)%(q*s)) := by
  let path := labelled hq hs off l w
  have forced := compatible_label_unique hsl _ _ _ (path.property i)
  change edgeWindow (firstBits hsl (path.val.1 i)) (path.val.1 (next hq i)) a = _
  rw [←forced]
  exact labelled_bit hq hs off l w i a

theorem closed_sensor {q s r l : ℕ} (hq : 0 < q) (hs : 0 < s) (hk : 2 ≤ q*s)
    (hr : 4 ≤ r) (off : Fin (q*s)) (hsl : s ≤ l)
    (nr nc : Fin (2^(q*s))) (cr cc : Fin r → Fin (2^(q*s))) (bank : Fin q → Bool)
    (w : Fin (2^(q*s))) (i : Fin q) (hw : l+s ≤ q*s)
    (hreach : (if bank i then 7*r-2 else 5*r-3) < l+s) :
    sensor hs nr nc cr cc off bank i (representative (site hs off i)
      (localWindow hq hsl (closed hq hs off hsl w) i)) =
      sensor hs nr nc cr cc off bank i w :=
  sensor_representative hs hk hr nr nc cr cc off bank i _ w hw hreach
    (closed_bit hq hs off hsl w i)

end PEqualNP.Outside.L_meta_33635.ScheduledRotated

namespace PEqualNP.Outside.L_meta_33635.ScheduledTrace

variable {S : Type*}

theorem endpoint_eq_last (q : ℕ) (a : S) (w : Fin q → S) :
    endpoint q a w = (Fin.cons a w : Fin (q+1) → S) (Fin.last q) := by
  induction q generalizing a with
  | zero => rfl
  | succ q ih =>
    rw [endpoint, ih]
    change (Fin.cons (w 0) (Fin.tail w)) (Fin.last q) = w (Fin.last q)
    rw [Fin.cons_self_tail]

theorem validPath_iff_edges (edge : ℕ → S → S → Bool)
    (q : ℕ) (a : S) (w : Fin q → S) :
    validPath edge q a w = true ↔
      ∀ i : Fin q, edge i.val ((Fin.cons a w : Fin (q+1) → S) i.castSucc) (w i) = true := by
  induction q generalizing edge a with
  | zero => simp [validPath]
  | succ q ih =>
    rw [validPath, Bool.and_eq_true, ih]
    constructor
    · rintro ⟨h0,ht⟩ i
      refine Fin.cases ?_ (fun j => ?_) i
      · exact h0
      · simpa only [Fin.cons_self_tail, Fin.castSucc_succ, Fin.cons_succ, Fin.tail,
          Fin.val_succ] using ht j
    · intro h
      refine ⟨h 0, fun j => ?_⟩
      simpa only [Fin.cons_self_tail, Fin.castSucc_succ, Fin.cons_succ, Fin.tail,
        Fin.val_succ] using h j.succ

abbrev ClosedSequence (edge : ℕ → S → S → Bool) (q : ℕ) :=
  {z : Fin (q+1) → S // z (Fin.last q) = z 0 ∧
    ∀ i : Fin q, edge i.val (z i.castSucc) (z i.succ) = true}

def sequencePathEquiv (edge : ℕ → S → S → Bool) (q : ℕ) :
    ClosedSequence edge q ≃ ClosedPath edge q where
  toFun z := ⟨(z.val 0, Fin.tail z.val), by
    constructor
    · apply (validPath_iff_edges edge q _ _).mpr
      intro i
      simpa only [Fin.cons_self_tail, Fin.tail] using z.property.2 i
    · rw [endpoint_eq_last, Fin.cons_self_tail]
      exact z.property.1⟩
  invFun p := ⟨Fin.cons p.val.1 p.val.2, by
    constructor
    · rw [← endpoint_eq_last]
      exact p.property.2
    · exact (validPath_iff_edges edge q _ _).mp p.property.1⟩
  left_inv z := by
    apply Subtype.ext
    exact Fin.cons_self_tail _
  right_inv p := by
    apply Subtype.ext
    rfl

abbrev PhaseCycle {q : ℕ} (hq : 0 < q) (edge : ℕ → S → S → Bool) :=
  {a : Fin q → S // ∀ i, edge i.val (a i) (a (ScheduledWindows.next hq i)) = true}

def cycleSequenceEquiv {q : ℕ} (hq : 0 < q) (edge : ℕ → S → S → Bool) :
    PhaseCycle hq edge ≃ ClosedSequence edge q where
  toFun a := ⟨fun i => a.val ⟨i.val % q, Nat.mod_lt _ hq⟩, by
    constructor
    · apply congrArg a.val
      apply Fin.ext
      simp
    · intro i
      have hi : (⟨i.val % q, Nat.mod_lt _ hq⟩ : Fin q)=i := by
        apply Fin.ext
        exact Nat.mod_eq_of_lt i.isLt
      change edge i.val (a.val ⟨i.val % q,_⟩)
        (a.val (ScheduledWindows.next hq i)) = true
      rw [hi]
      exact a.property i⟩
  invFun z := ⟨fun i => z.val i.castSucc, by
    intro i
    have hnext : z.val (ScheduledWindows.next hq i).castSucc = z.val i.succ := by
      by_cases hi : i.val+1 < q
      · apply congrArg z.val
        apply Fin.ext
        exact Nat.mod_eq_of_lt hi
      · have hi' : i.val+1=q := by have := i.isLt; omega
        have hn : (ScheduledWindows.next hq i).castSucc = (0 : Fin (q+1)) := by
          apply Fin.ext
          simp [ScheduledWindows.next, hi']
        have hl : i.succ = Fin.last q := Fin.ext hi'
        rw [hn,hl]
        exact z.property.1.symm
    change edge i.val (z.val i.castSucc) (z.val (ScheduledWindows.next hq i).castSucc) = true
    rw [hnext]
    exact z.property.2 i⟩
  left_inv a := by
    apply Subtype.ext
    funext i
    apply congrArg a.val
    apply Fin.ext
    exact Nat.mod_eq_of_lt i.isLt
  right_inv z := by
    apply Subtype.ext
    funext i
    by_cases hi : i.val < q
    · apply congrArg z.val
      apply Fin.ext
      exact Nat.mod_eq_of_lt hi
    · have hi' : i.val=q := by have := i.isLt; omega
      have hn : (⟨i.val % q, Nat.mod_lt _ hq⟩ : Fin q).castSucc = (0 : Fin (q+1)) := by
        apply Fin.ext
        simp [hi']
      have hl : i = Fin.last q := Fin.ext hi'
      change z.val (⟨i.val % q,_⟩ : Fin q).castSucc=z.val i
      rw [hn,hl]
      exact z.property.1.symm

def cyclePathEquiv {q : ℕ} (hq : 0 < q) (edge : ℕ → S → S → Bool) :
    PhaseCycle hq edge ≃ ClosedPath edge q :=
  (cycleSequenceEquiv hq edge).trans (sequencePathEquiv edge q)

def phaseCongr {T : Type*} {q : ℕ} (hq : 0 < q) (e : S ≃ T)
    (edge : ℕ → S → S → Bool) :
    PhaseCycle hq edge ≃ PhaseCycle hq (fun i a b => edge i (e.symm a) (e.symm b)) where
  toFun a := ⟨fun i => e (a.val i), by
    intro i
    simpa only [Equiv.symm_apply_apply] using a.property i⟩
  invFun a := ⟨fun i => e.symm (a.val i), a.property⟩
  left_inv a := by apply Subtype.ext; funext i; exact e.symm_apply_apply _
  right_inv a := by apply Subtype.ext; funext i; exact e.apply_symm_apply _

theorem pathParity_eq_foldr (label : ℕ → S → S → Bool)
    (q : ℕ) (a : S) (w : Fin q → S) :
    pathParity label q a w =
      (List.ofFn (fun i : Fin q =>
        label i.val ((Fin.cons a w : Fin (q+1) → S) i.castSucc) (w i))).foldr xor false := by
  induction q generalizing label a with
  | zero => rfl
  | succ q ih =>
    rw [pathParity, ih, List.ofFn_succ, List.foldr_cons]
    simp only [Fin.cons_self_tail, Fin.castSucc_succ, Fin.cons_succ, Fin.tail,
      Fin.val_succ, Fin.castSucc_zero, Fin.cons_zero, Fin.val_zero]

theorem cyclePath_parity {q : ℕ} (hq : 0 < q) (edge label : ℕ → S → S → Bool)
    (a : PhaseCycle hq edge) :
    pathParity label q ((cyclePathEquiv hq edge a).val.1)
      ((cyclePathEquiv hq edge a).val.2) =
      (List.ofFn (fun i : Fin q => label i.val (a.val i)
        (a.val (ScheduledWindows.next hq i)))).foldr xor false := by
  rw [pathParity_eq_foldr]
  congr 1
  apply congrArg List.ofFn
  funext i
  change label i.val
    ((Fin.cons ((cycleSequenceEquiv hq edge a).val 0)
      (Fin.tail (cycleSequenceEquiv hq edge a).val)) i.castSucc)
    ((cycleSequenceEquiv hq edge a).val i.succ) = _
  rw [Fin.cons_self_tail]
  change label i.val (a.val ⟨i.val % q,_⟩)
    (a.val (ScheduledWindows.next hq i)) = _
  have hi : (⟨i.val % q, Nat.mod_lt _ hq⟩ : Fin q)=i := by
    apply Fin.ext
    exact Nat.mod_eq_of_lt i.isLt
  rw [hi]

def parityPathEquiv {W : Type*} (edge label : ℕ → S → S → Bool) (q : ℕ)
    (e : W ≃ ClosedPath edge q) (parity : Bool) :
    {x : W // pathParity label q (e x).val.1 (e x).val.2 = parity} ≃
      ParityClosedPath edge label q parity where
  toFun x := ⟨(e x.val).val, (e x.val).property.1,
    (e x.val).property.2, x.property⟩
  invFun p := ⟨e.symm ⟨p.val,p.property.1,p.property.2.1⟩, by
    simpa only [Equiv.apply_symm_apply] using p.property.2.2⟩
  left_inv x := by
    apply Subtype.ext
    exact e.symm_apply_apply x.val
  right_inv p := by
    apply Subtype.ext
    change (e (e.symm (⟨p.val,p.property.1,p.property.2.1⟩ : ClosedPath edge q))).val=p.val
    rw [e.apply_symm_apply]

theorem parityDP_count_of_equiv [Fintype S] [DecidableEq S]
    {W : Type*} [Fintype W] (edge label : ℕ → S → S → Bool) (q : ℕ)
    (e : W ≃ ClosedPath edge q) (parity : Bool) :
    (∑ a : S, parityDP edge label q a a parity) =
      Fintype.card {x : W // pathParity label q (e x).val.1 (e x).val.2 = parity} := by
  rw [parityDP_closed_card]
  exact Fintype.card_congr (parityPathEquiv edge label q e parity).symm

end PEqualNP.Outside.L_meta_33635.ScheduledTrace

namespace PEqualNP.Outside.L_meta_33635.ScheduledWindows

def overlapEdge {s l : ℕ} (hsl : s ≤ l) (_i : ℕ) (a b : Word l) : Bool := by
  letI : Decidable (Compatible a (firstBits hsl a) b) := by unfold Compatible; infer_instance
  exact decide (Compatible a (firstBits hsl a) b)

def windowsPhaseEquiv {q s l : ℕ} (hq : 0 < q) (hsl : s ≤ l) :
    ClosedWindows hq hsl ≃ ScheduledTrace.PhaseCycle hq (overlapEdge hsl) where
  toFun a := ⟨a.val, by simpa only [overlapEdge, decide_eq_true_eq] using a.property⟩
  invFun a := ⟨a.val, by simpa only [overlapEdge, decide_eq_true_eq] using a.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

noncomputable def numericKeyPathEquiv {q s l : ℕ}
    (hq : 0 < q) (hs : 0 < s) (hsl : s ≤ l) :
    Fin (2^(q*s)) ≃ ScheduledTrace.ClosedPath (overlapEdge hsl) q :=
  (numericKeyClosedWindowsEquiv hq hs hsl).trans
    ((windowsPhaseEquiv hq hsl).trans (ScheduledTrace.cyclePathEquiv hq _))

theorem trace_overlap_count {q s l : ℕ}
    (hq : 0 < q) (hs : 0 < s) (hsl : s ≤ l) :
    Matrix.trace (ScheduledTrace.transfer (ScheduledTrace.adjacency (overlapEdge hsl)) q) =
      2^(q*s) := by
  classical
  simpa using ScheduledTrace.trace_count_of_equiv (overlapEdge hsl) q
    (numericKeyPathEquiv hq hs hsl)

def numericOverlapEdge {s l : ℕ} (hsl : s ≤ l) (i : ℕ)
    (a b : Fin (2^l)) : Bool := overlapEdge hsl i (bits l a) (bits l b)

noncomputable def numericWindowsPhaseEquiv {q s l : ℕ} (hq : 0 < q) (hsl : s ≤ l) :
    ClosedWindows hq hsl ≃ ScheduledTrace.PhaseCycle hq (numericOverlapEdge hsl) :=
  (windowsPhaseEquiv hq hsl).trans
    (ScheduledTrace.phaseCongr hq (bitsEquiv l).symm (overlapEdge hsl))

noncomputable def numericWindowsPathEquiv {q s l : ℕ} (hq : 0 < q) (hsl : s ≤ l) :
    ClosedWindows hq hsl ≃ ScheduledTrace.ClosedPath (numericOverlapEdge hsl) q :=
  (numericWindowsPhaseEquiv hq hsl).trans (ScheduledTrace.cyclePathEquiv hq _)

theorem numericWindowsPath_parity {q s l : ℕ} (hq : 0 < q) (hsl : s ≤ l)
    (label : ℕ → Fin (2^l) → Fin (2^l) → Bool) (a : ClosedWindows hq hsl) :
    ScheduledTrace.pathParity label q (numericWindowsPathEquiv hq hsl a).val.1
      (numericWindowsPathEquiv hq hsl a).val.2 =
      (List.ofFn (fun i : Fin q => label i.val ((bitsEquiv l).symm (a.val i))
        ((bitsEquiv l).symm (a.val (next hq i))))).foldr xor false :=
  ScheduledTrace.cyclePath_parity hq (numericOverlapEdge hsl) label
    (numericWindowsPhaseEquiv hq hsl a)

end PEqualNP.Outside.L_meta_33635.ScheduledWindows

namespace PEqualNP.Outside.L_meta_33635.ScheduledColorMasks

abbrev Pair := Bool × Bool

def nonzero (p : Pair) : Prop := p ≠ (false, false)

def adjacent (p q : Pair) : Pair := (xor p.1 q.1, xor p.2 q.2)

def scan : Bool → List Bool → Prop
  | _, [] => True
  | prev, x :: xs => (prev = true ∨ x = true) ∧ scan x xs

def block (anchor : Bool) (p : Pair) := [p.1, p.2, anchor]

def bank {n : ℕ} (edges : List (Fin n × Fin n)) (anchor : Bool) (p : Fin n → Pair) :=
  [anchor, anchor, anchor] ++
    (List.finRange n).flatMap (fun i => block anchor (p i)) ++
    edges.flatMap (fun e => block anchor (adjacent (p e.1) (p e.2)))

theorem block_scan (p : Pair) (xs : List Bool) :
    scan true (block true p ++ xs) ↔ nonzero p ∧ scan true xs := by
  obtain ⟨a,b⟩ := p
  cases a <;> cases b <;> simp [scan, block, nonzero]

theorem blocks_scan {α : Type*} (xs : List α) (f : α → Pair) (tail : List Bool) :
    scan true (xs.flatMap (fun i => block true (f i)) ++ tail) ↔
    (∀ i ∈ xs, nonzero (f i)) ∧ scan true tail := by
  induction xs with
  | nil => simp
  | cons i xs ih => simp [List.append_assoc, block_scan, ih, and_assoc]

theorem adjacent_nonzero (p q : Pair) : nonzero (adjacent p q) ↔ p ≠ q := by
  rcases p with ⟨a,b⟩
  rcases q with ⟨c,d⟩
  cases a <;> cases b <;> cases c <;> cases d <;> simp [nonzero, adjacent]

theorem scan_bank {n : ℕ} (edges : List (Fin n × Fin n)) (a : Bool) (p : Fin n → Pair) :
    scan a (bank edges a p ++ [a]) ↔
      a = true ∧ (∀ i, nonzero (p i)) ∧ ∀ e ∈ edges, p e.1 ≠ p e.2 := by
  cases a
  · simp [bank, scan]
  · simp [bank, List.append_assoc, scan, blocks_scan, adjacent_nonzero]

def encode (c : Fin 3) : Pair := (c.val != 1, c.val != 0)

theorem encode_inj : Function.Injective encode := by
  intro a b
  fin_cases a <;> fin_cases b <;> decide
theorem encode_nz (c : Fin 3) : nonzero (encode c) := by
  fin_cases c <;> unfold nonzero <;> decide

def decode (p : Pair) : Fin 3 := if p.1 then (if p.2 then 2 else 0) else 1

theorem encode_decode (p : Pair) (h : nonzero p) : encode (decode p) = p := by
  obtain ⟨a,b⟩ := p
  cases a <;> cases b <;> simp_all [nonzero, decode, encode]

theorem color_classification {n : ℕ} (edges : List (Fin n × Fin n))
    (a : Bool) (p : Fin n → Pair) :
    scan a (bank edges a p ++ [a]) ↔ a = true ∧
      ∃! c : Fin n → Fin 3, (∀ e ∈ edges, c e.1 ≠ c e.2) ∧ ∀ i, p i = encode (c i) := by
  rw [scan_bank]
  constructor
  · rintro ⟨ha,hp,he⟩
    let c := fun i => decode (p i)
    have bits (i) : p i = encode (c i) := (encode_decode _ (hp i)).symm
    refine ⟨ha, c, ⟨?_,bits⟩,?_⟩
    · intro e h eq
      apply he e h
      exact (bits e.1).trans ((congrArg encode eq).trans (bits e.2).symm)
    · intro c' hc
      funext i
      exact encode_inj ((hc.2 i).symm.trans (bits i))
  · rintro ⟨ha,c,⟨proper,hp⟩,_⟩
    refine ⟨ha, fun i => hp i ▸ encode_nz (c i), ?_⟩
    intro e h eq
    exact proper e h (encode_inj ((hp e.1).symm.trans (eq.trans (hp e.2))))

lemma one_testBit (j : ℕ) : (1 : ℕ).testBit j = decide (j = 0) := by
  simpa [eq_comm] using Nat.testBit_two_pow (n := 0) (m := j)

def normalOf {n : ℕ} (c : Fin n → Fin 3) : ℕ :=
  (List.finRange n).foldl (fun p i => p ||| (((c i).val + 1) <<< (2 * i.val + 1))) (1 : ℕ)

lemma foldl_or_testBit {α : Type*} (l : List α) (f : α → ℕ) (init j : ℕ) :
    (l.foldl (fun p a => p ||| f a) init).testBit j =
      (init.testBit j || l.any (fun a => (f a).testBit j)) := by
  induction l generalizing init with
  | nil => simp
  | cons a t ih =>
    simp only [List.foldl_cons, List.any_cons, ih, Nat.testBit_or, Bool.or_assoc]

lemma normalOf_testBit {n : ℕ} (c : Fin n → Fin 3) :
    (normalOf c).testBit 0 = true ∧
    (∀ k : Fin n, (normalOf c).testBit (2 * k.val + 1) = ((c k).val + 1).testBit 0) ∧
    (∀ k : Fin n, (normalOf c).testBit (2 * k.val + 2) = ((c k).val + 1).testBit 1) := by
  unfold normalOf
  refine ⟨?_, ?_, ?_⟩
  · rw [foldl_or_testBit]; simp [one_testBit]
  · intro k
    rw [foldl_or_testBit, one_testBit]
    simp only [Nat.succ_ne_zero, decide_false, Bool.false_or]
    have h1 : ∀ i : Fin n, (((c i).val + 1) <<< (2 * i.val + 1)).testBit (2 * k.val + 1) =
        if i = k then ((c k).val + 1).testBit 0 else false := by
      intro i
      rw [Nat.testBit_shiftLeft]
      by_cases hik : i = k
      · subst hik; simp
      · rw [if_neg hik]
        by_cases hle : 2 * i.val + 1 ≤ 2 * k.val + 1
        · have hge2 : 2 ≤ 2 * k.val + 1 - (2 * i.val + 1) := by
            have hne : i.val ≠ k.val := fun h => hik (Fin.ext h)
            omega
          have hlt4 : (c i).val + 1 < 2 ^ (2 * k.val + 1 - (2 * i.val + 1)) := by
            have := (c i).isLt
            calc (c i).val + 1 < 2 ^ 2 := by omega
              _ ≤ 2 ^ (2 * k.val + 1 - (2 * i.val + 1)) := Nat.pow_le_pow_right (by omega) hge2
          rw [Nat.testBit_eq_false_of_lt hlt4, Bool.and_false]
        · simp [hle]
    cases hb : ((c k).val + 1).testBit 0
    · rw [Bool.eq_false_iff]
      intro hany
      rw [List.any_eq_true] at hany
      obtain ⟨i, _, hi⟩ := hany
      rw [h1 i] at hi
      by_cases hik : i = k
      · rw [if_pos hik, hb] at hi; exact Bool.noConfusion hi
      · rw [if_neg hik] at hi; exact Bool.noConfusion hi
    · rw [List.any_eq_true]
      refine ⟨k, List.mem_finRange k, ?_⟩
      rw [h1 k, if_pos rfl, hb]
  · intro k
    rw [foldl_or_testBit, one_testBit]
    simp only [Nat.succ_ne_zero, decide_false, Bool.false_or]
    have h1 : ∀ i : Fin n, (((c i).val + 1) <<< (2 * i.val + 1)).testBit (2 * k.val + 2) =
        if i = k then ((c k).val + 1).testBit 1 else false := by
      intro i
      rw [Nat.testBit_shiftLeft]
      by_cases hik : i = k
      · subst hik
        have hsub : 2 * i.val + 2 - (2 * i.val + 1) = 1 := by omega
        simp [hsub]
      · rw [if_neg hik]
        by_cases hle : 2 * i.val + 1 ≤ 2 * k.val + 2
        · have hge2 : 2 ≤ 2 * k.val + 2 - (2 * i.val + 1) := by
            have hne : i.val ≠ k.val := fun h => hik (Fin.ext h)
            omega
          have hlt4 : (c i).val + 1 < 2 ^ (2 * k.val + 2 - (2 * i.val + 1)) := by
            have := (c i).isLt
            calc (c i).val + 1 < 2 ^ 2 := by omega
              _ ≤ 2 ^ (2 * k.val + 2 - (2 * i.val + 1)) := Nat.pow_le_pow_right (by omega) hge2
          rw [Nat.testBit_eq_false_of_lt hlt4, Bool.and_false]
        · simp [hle]
    cases hb : ((c k).val + 1).testBit 1
    · rw [Bool.eq_false_iff]
      intro hany
      rw [List.any_eq_true] at hany
      obtain ⟨i, _, hi⟩ := hany
      rw [h1 i] at hi
      by_cases hik : i = k
      · rw [if_pos hik, hb] at hi; exact Bool.noConfusion hi
      · rw [if_neg hik] at hi; exact Bool.noConfusion hi
    · rw [List.any_eq_true]
      refine ⟨k, List.mem_finRange k, ?_⟩
      rw [h1 k, if_pos rfl, hb]

def readPair {n : ℕ} (w : ℕ) (i : Fin n) : Pair :=
  (w.testBit (2*i.val+1), w.testBit (2*i.val+2))

theorem read_normal {n : ℕ} (c : Fin n → Fin 3) :
    (normalOf c).testBit 0 = true ∧ ∀ i, readPair (normalOf c) i = encode (c i) := by
  obtain ⟨ha,hl,hh⟩ := normalOf_testBit c
  refine ⟨ha,fun i => ?_⟩
  unfold readPair
  rw [hl,hh]
  generalize c i = z
  fin_cases z <;> decide

theorem normal_high {n : ℕ} (c : Fin n → Fin 3) (j : ℕ) (h : 2*n+1 ≤ j) :
    (normalOf c).testBit j = false := by
  unfold normalOf
  rw [foldl_or_testBit,one_testBit]
  have hj : j ≠ 0 := by omega
  simp only [hj,decide_false,Bool.false_or]
  apply Bool.eq_false_iff.mpr
  intro ht
  obtain ⟨i,_,hi⟩ := List.any_eq_true.mp ht
  have delta : 2 ≤ j-(2*i.val+1) := by have := i.isLt; omega
  have v : (c i).val+1 < 2^(j-(2*i.val+1)) := by
    calc (c i).val + 1 < 2^2 := by have := (c i).isLt; omega
         _ ≤ _ := Nat.pow_le_pow_right (by decide) delta
  simp [Nat.testBit_shiftLeft,Nat.testBit_eq_false_of_lt v] at hi

theorem reconstruct {n : ℕ} (w : Fin (2^(2*n+1))) (c : Fin n → Fin 3)
    (h0 : w.val.testBit 0 = true) (hPair : ∀ i, readPair w.val i = encode (c i)) :
    w.val = normalOf c := by
  obtain ⟨ha,hc⟩ := read_normal c
  apply Nat.eq_of_testBit_eq
  intro j
  by_cases j0 : j = 0
  · simpa [j0] using h0.trans ha.symm
  by_cases beyond : 2*n+1 ≤ j
  · rw [normal_high c j beyond]
    exact Nat.testBit_eq_false_of_lt (w.isLt.trans_le (Nat.pow_le_pow_right (by decide) beyond))
  let i : Fin n := ⟨(j-1)/2,by omega⟩
  have eqp := (hPair i).trans (hc i).symm
  have split : j=2*i.val+1 ∨ j=2*i.val+2 := by dsimp [i]; omega
  obtain h | h := split
  · rw [h]
    exact congrArg Prod.fst eqp
  · rw [h]
    exact congrArg Prod.snd eqp

theorem normalized_masks_iff_proper {n : ℕ} (es : List (Fin n × Fin n))
    (w : Fin (2^(2*n+1))) :
    scan (w.val.testBit 0)
      (bank es (w.val.testBit 0) (readPair w.val) ++ [w.val.testBit 0]) ↔
    ∃! c : Fin n → Fin 3, (∀ e ∈ es, c e.1 ≠ c e.2) ∧ w.val = normalOf c := by
  rw [color_classification]
  constructor
  · rintro ⟨h0,c,⟨hp,hc⟩,hu⟩
    refine ⟨c,⟨hp,reconstruct w c h0 hc⟩,?_⟩
    rintro c' ⟨hp',hc'⟩
    exact hu _ ⟨hp',by rw [hc']; exact (read_normal c').2⟩
  · rintro ⟨c,⟨hp,hc⟩,hu⟩
    have h0 : w.val.testBit 0 = true := hc ▸ (read_normal c).1
    refine ⟨h0,c,⟨hp,by rw [hc]; exact (read_normal c).2⟩,?_⟩
    rintro c' ⟨hp',hc'⟩
    exact hu _ ⟨hp',reconstruct w c' h0 hc'⟩

end PEqualNP.Outside.L_meta_33635.ScheduledColorMasks

namespace PEqualNP.Outside.L_meta_33635.ScheduledCombined
open ScheduledWalsh ScheduledColorMasks

def low {n : ℕ} (i : Fin n) : ℕ := 1 <<< (2*i.val+1)
def high {n : ℕ} (i : Fin n) : ℕ := 1 <<< (2*i.val+2)

def columns {n : ℕ} (es : List (Fin n × Fin n)) : List ℕ :=
  [1,1,1] ++ (List.finRange n).flatMap (fun i => [low i, high i, 1]) ++
    es.flatMap (fun e => [low e.1 ^^^ low e.2, high e.1 ^^^ high e.2, 1])

def colors {n : ℕ} (es : List (Fin n × Fin n)) : Finset (Fin n → Fin 3) :=
  Finset.univ.filter fun c => ∀ e ∈ es, c e.1 ≠ c e.2

theorem column_bits {n : ℕ} (es : List (Fin n × Fin n)) (w : Word (2*n+1)) :
    (columns es).map (par (2*n+1) w.val) =
      bank es (w.val.testBit 0) (readPair w.val) := by
  have bit (j : ℕ) (hj : j < 2*n+1) :
      par (2*n+1) w.val (1 <<< j) = w.val.testBit j := by
    rw [par_comm, Nat.shiftLeft_eq, Nat.one_mul, par_single]; simp [hj]
  have one : par (2*n+1) w.val 1 = w.val.testBit 0 := bit 0 (by omega)
  have lo (i : Fin n) : par (2*n+1) w.val (low i) = w.val.testBit (2*i.val+1) :=
    bit _ (by have := i.isLt; omega)
  have hi (i : Fin n) : par (2*n+1) w.val (high i) = w.val.testBit (2*i.val+2) :=
    bit _ (by have := i.isLt; omega)
  simp [columns, bank, block, adjacent, readPair, List.map_flatMap, par_xor_right, lo, hi, one]

def hasGap (l : List Bool) : Prop := ∃ x y, l = x ++ false :: false :: true :: y

private theorem gap_left {l : List Bool} (g : hasGap l) (r : List Bool) : hasGap (l++r) := by
  obtain ⟨x,y,rfl⟩ := g
  exact ⟨x,y++r,by simp⟩

private theorem gap_right {l : List Bool} (g : hasGap l) (r : List Bool) : hasGap (r++l) := by
  obtain ⟨x,y,rfl⟩ := g
  exact ⟨r++x,y,by simp⟩

private theorem gap_after (l : List Bool) (h : true ∈ l) : hasGap (false::false::l) := by
  induction l with
  | nil => simp at h
  | cons b l ih =>
    cases b with
    | true => exact ⟨[],l,rfl⟩
    | false => exact gap_right (ih (by simpa using h)) [false]

private theorem gap_bad {α : Type*} {i : α} {xs : List α} (f : α → Pair)
    (h : i ∈ xs) (bad : ¬nonzero (f i)) : hasGap (xs.flatMap fun j => block true (f j)) := by
  obtain ⟨p,t,rfl⟩ := List.mem_iff_append.mp h
  have eq : f i = (false,false) := Classical.byContradiction bad
  rw [List.flatMap_append, List.flatMap_cons, eq]
  exact ⟨_,_,rfl⟩

private theorem contains_bit {n : ℕ} (es : List (Fin n × Fin n)) (v : Fin n → Pair)
    (i : Fin n) (h : (v i).1=true ∨ (v i).2=true) :
    true ∈ (List.finRange n).flatMap (fun j => block false (v j)) ++
      es.flatMap (fun e => block false (adjacent (v e.1) (v e.2))) := by
  apply List.mem_append_left
  apply List.mem_flatMap.mpr
  exact ⟨i, List.mem_finRange _, by rcases h with h | h <;> simp [block,h]⟩

private theorem testBit_zero_of_pairs {n : ℕ} (w : Word (2*n+1)) (anch : w.val.testBit 0=false)
    (zeros : ∀ i : Fin n, (readPair w.val i) = (false,false)) : w.val=0 := by
  apply Nat.eq_of_testBit_eq
  intro j
  simp only [Nat.zero_testBit]
  by_cases h : 2*n+1≤j
  · exact Nat.testBit_eq_false_of_lt (w.isLt.trans_le (Nat.pow_le_pow_right (by decide) h))
  by_cases z : j=0
  · simpa only [z] using anch
  let i : Fin n := ⟨(j-1)/2,by omega⟩
  rcases (show j=2*i.val+1 ∨ j=2*i.val+2 by dsimp [i]; omega) with e | e
  · rw [e]; exact congrArg Prod.fst (zeros i)
  · rw [e]; exact congrArg Prod.snd (zeros i)

theorem gap_of_bad_mask {n : ℕ} (es : List (Fin n × Fin n)) (w : Word (2*n+1))
    (nz : w.val ≠ 0) (bad : ∀ c ∈ colors es, w.val ≠ normalOf c) :
    hasGap ((columns es).map (par (2*n+1) w.val)) := by
  rw [column_bits]
  let v := readPair w.val (n := n)
  change hasGap (bank es (w.val.testBit 0) v)
  by_contra nogap
  cases anch : w.val.testBit 0 with
  | false =>
    rw [anch] at nogap
    apply nz
    apply testBit_zero_of_pairs w anch
    intro i
    cases e : v i with | mk a b =>
      have off : ¬(a=true ∨ b=true) := by
        intro hb
        have mem := contains_bit es v i (by simpa [e] using hb)
        apply nogap
        exact gap_right (gap_after _ mem) [false]
      change v i = _
      rw [e]
      cases a <;> cases b <;> simp_all
  | true =>
    rw [anch] at nogap
    have vertices (i : Fin n) : nonzero (v i) := by
      intro fail
      apply nogap
      exact gap_left (gap_right (gap_bad v (List.mem_finRange i) (fun h => h fail)) _) _
    have edges : ∀ e ∈ es, v e.1 ≠ v e.2 := by
      intro e he eq
      apply nogap
      have b : ¬ nonzero (adjacent (v e.1) (v e.2)) := fun h => (adjacent_nonzero _ _).mp h eq
      exact gap_right (gap_bad (fun e : Fin n × Fin n => adjacent (v e.1) (v e.2)) he b) _
    have valid := (scan_bank es true v).mpr ⟨rfl,vertices,edges⟩
    have sc : scan (w.val.testBit 0) (bank es (w.val.testBit 0) (readPair w.val) ++ [w.val.testBit 0]) := by
      simpa [anch,v] using valid
    obtain ⟨c,⟨proper,hc⟩,_⟩ := (normalized_masks_iff_proper es w).mp sc
    exact bad c (Finset.mem_filter.mpr ⟨Finset.mem_univ _,proper⟩) hc

private theorem projections {α : Type*} (l : List α) (f : α → Bool) (hg : hasGap (l.map f)) :
    ∃ i : Fin l.length, 2 ≤ i.val ∧ f (l.get i) = true ∧
      ∀ j : Fin l.length, j.val + 1 = i.val ∨ j.val + 2 = i.val → f (l.get j) = false := by
  obtain ⟨p,t,e⟩ := hg
  have len := congrArg List.length e
  simp only [List.length_map, List.length_append, List.length_cons] at len
  let i : Fin l.length := ⟨p.length+2,by omega⟩
  have at_all (j : Fin l.length) : (l.map f)[j.val]? = some (f (l.get j)) := by
    simp [j.isLt]
  refine ⟨i,by dsimp [i]; omega,?_,?_⟩
  · have h := at_all i
    rw [e, List.getElem?_append_right (by dsimp [i]; omega)] at h
    simpa [i] using h.symm
  · intro j hj
    have h := at_all j
    change j.val+1=p.length+2 ∨ j.val+2=p.length+2 at hj
    rw [e,List.getElem?_append_right (by omega)] at h
    rcases hj with hj | hj
    · rw [show j.val-p.length=1 by omega] at h
      simpa using h.symm
    · rw [show j.val-p.length=0 by omega] at h
      simpa using h.symm

def LocalPivot {q k : ℕ} (sensor : Fin q → Word k → Bool) : Prop :=
  ∀ i : Fin q, 2 ≤ i.val → ∃ flipKey : Word k ≃ Word k,
    (∀ w, sensor i (flipKey w) = !sensor i w) ∧
    ∀ j : Fin q, j ≠ i → j.val+1 ≠ i.val → j.val+2 ≠ i.val →
      ∀ w, sensor j (flipKey w) = sensor j w

theorem mask_cancels {n k : ℕ} (es : List (Fin n × Fin n))
    (sensor : Fin (columns es).length → Word k → Bool) (localP : LocalPivot sensor)
    (a : Word (2*n+1)) (nz : a.val ≠ 0) (bad : ∀ c ∈ colors es, a.val ≠ normalOf c) :
    (∑ w, sign (par (2*n+1) a.val (report (columns es).get sensor w))) = 0 := by
  obtain ⟨i,hi,on,off⟩ := projections _ _ (gap_of_bad_mask es a nz bad)
  obtain ⟨e,flip,keep⟩ := localP i hi
  apply cancel_sensor _ _ _ _ e i on flip
  intro j other selected
  exact keep j other (fun near => Bool.noConfusion (selected.symm.trans (off j (Or.inl near))))
    (fun near => Bool.noConfusion (selected.symm.trans (off j (Or.inr near))))

private theorem columns_bound {n : ℕ} (es : List (Fin n × Fin n)) :
    ∀ x ∈ columns es, x < 2^(2*n+1) := by
  have one : 1 < 2^(2*n+1) :=
    Nat.one_lt_two_pow (by omega)
  have lo (i : Fin n) : low i < 2^(2*n+1) := by
    unfold low
    rw [Nat.shiftLeft_eq,Nat.one_mul]
    exact Nat.pow_lt_pow_right (by decide) (by have := i.isLt; omega)
  have hi (i : Fin n) : high i < 2^(2*n+1) := by
    unfold high
    rw [Nat.shiftLeft_eq,Nat.one_mul]
    exact Nat.pow_lt_pow_right (by decide) (by have := i.isLt; omega)
  intro x hx
  simp only [columns, List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.mem_flatMap] at hx
  rcases hx with ((h|h|h) | ⟨i,_,h|h|h⟩) | ⟨e,_,h|h|h⟩ <;> subst x
  all_goals first | exact one | exact lo _ | exact hi _ | exact Nat.xor_lt_two_pow (lo _) (lo _) | exact Nat.xor_lt_two_pow (hi _) (hi _)

private theorem report_bound {m q k : ℕ} (col : Fin q → ℕ) (sensor : Fin q → Word k → Bool)
    (h : ∀ i, col i < 2^m) (w : Word k) : report col sensor w < 2^m := by
  have aux (l : List (Fin q)) (a : ℕ) (ha : a < 2^m) :
      l.foldl (fun z i => if sensor i w then z ^^^ col i else z) a < 2^m := by
    induction l generalizing a with
    | nil => exact ha
    | cons i l ih =>
      apply ih
      change (if sensor i w then a ^^^ col i else a) < 2^m
      split <;> first | exact Nat.xor_lt_two_pow ha (h _) | exact ha
  exact aux _ _ (Nat.two_pow_pos _)

def normalized {n : ℕ} (c : Fin n → Fin 3) : Word (2*n+1) :=
  ⟨normalOf c, Nat.lt_pow_two_of_testBit _ (normal_high c)⟩

theorem normalized_inj {n : ℕ} : Function.Injective (normalized (n:=n)) := by
  intro c d he
  have e : normalOf c = normalOf d := congrArg Fin.val he
  funext i
  apply encode_inj
  rw [←(read_normal c).2 i, e, (read_normal d).2 i]

theorem key_width {n s : ℕ} (es : List (Fin n × Fin n)) (hs : 0 < s) :
    2*n+1 ≤ (columns es).length*s := by
  have lens : (columns es).length = 3 + 3*n + 3*es.length := by
    simp [columns]; omega
  have pos : (columns es).length ≤ (columns es).length * s := by
    simpa using Nat.mul_le_mul_left (columns es).length (show 1 ≤ s by omega)
  omega

theorem count_formulas {n k : ℕ} (es : List (Fin n × Fin n)) (width : 2*n+1 ≤ k)
    (sensor : Fin (columns es).length → Word k → Bool) (localP : LocalPivot sensor) :
    let f := report (columns es).get sensor
    let hits := fun y : Word (2*n+1) => Nat.card {w : Word k // f w = y.val}
    (∀ y : Word (2*n+1), (2:ℤ)^(2*n+1) * (hits y : ℤ) = (2:ℤ)^k +
      ∑ c ∈ colors es, sign (par (2*n+1) (normalOf c) y.val) *
        ∑ w : Word k, sign (par (2*n+1) (normalOf c) (f w))) ∧
    ((colors es).card = 0 → ∀ y, hits y = 2^(k-(2*n+1))) := by
  intro f hits
  have formula (y : Word (2*n+1)) := fiber_pruned (colors es) normalized normalized_inj
    (fun c _ hc => by
      have h := (read_normal c).1
      change normalOf c = 0 at hc
      simp [hc] at h)
    f (report_bound _ _ (fun i => columns_bound es _ (List.get_mem _ i)))
    (fun a nz bad => mask_cancels es sensor localP a nz (fun c hc eq =>
      bad c hc (Fin.ext eq.symm))) y
  refine ⟨formula,?_⟩
  intro empty y
  apply uniform_hit width
  simpa [Finset.card_eq_zero.mp empty, hits] using formula y

end PEqualNP.Outside.L_meta_33635.ScheduledCombined

namespace PEqualNP.Outside.L_meta_33635.ScheduledThreshold

variable {α : Type*}

theorem unsigned_threshold {m k hits t : ℕ} (colors : Finset α)
    (swap : α → Bool) (even odd : α → ℕ)
    (h : (2 : ℤ)^m * (hits : ℤ) = (2 : ℤ)^k +
      ∑ a ∈ colors, (if swap a then (-1 : ℤ) else 1) * ((even a : ℤ) - odd a)) :
    t ≤ hits ↔ 2^m * t + (∑ a ∈ colors, if swap a then even a else odd a) ≤
      2^k + (∑ a ∈ colors, if swap a then odd a else even a) := by
  have term (a : α) : (if swap a then (-1 : ℤ) else 1) * ((even a : ℤ) - odd a) =
      ((if swap a then odd a else even a : ℕ) : ℤ) -
      ((if swap a then even a else odd a : ℕ) : ℤ) := by
    cases swap a <;> simp
  simp_rw [term] at h
  rw [Finset.sum_sub_distrib] at h
  have equiv : (2 : ℤ)^m * (t : ℤ) ≤ (2 : ℤ)^m * (hits : ℤ) ↔
      (2 : ℤ)^m * (t : ℤ) + (∑ a ∈ colors, ((if swap a then even a else odd a : ℕ) : ℤ)) ≤
      (2 : ℤ)^k + (∑ a ∈ colors, ((if swap a then odd a else even a : ℕ) : ℤ)) := by
    rw [h]
    omega
  rw [mul_le_mul_iff_right₀ (by positivity : (0 : ℤ) < 2^m)] at equiv
  exact_mod_cast equiv

theorem colors_bound {n : ℕ} (colors : Finset (Fin n → Fin 3)) :
    colors.card ≤ 2^(2*n+1) := by
  calc
    colors.card ≤ Fintype.card (Fin n → Fin 3) := Finset.card_le_univ _
    _ = 3^n := by simp
    _ ≤ (2^2)^n := Nat.pow_le_pow_left (by decide) _
    _ = 2^(2*n) := (pow_mul _ _ _).symm
    _ ≤ 2^(2*n+1) := Nat.pow_le_pow_right (by decide) (by omega)

theorem total_le {m k : ℕ} (colors : Finset α) (count : α → ℕ)
    (hc : colors.card ≤ 2^m) (hmax : ∀ a ∈ colors, count a ≤ 2^k) :
    ∑ a ∈ colors, count a ≤ 2^(k+m) := by
  calc
    ∑ a ∈ colors, count a ≤ ∑ _a ∈ colors, 2^k := Finset.sum_le_sum hmax
    _ = colors.card * 2^k := by simp
    _ ≤ 2^m * 2^k := Nat.mul_le_mul_right _ hc
    _ = 2^(k+m) := by rw [← pow_add, Nat.add_comm]

theorem width {k m t pos neg : ℕ} (ht : t < 2^(k+1))
    (hp : pos ≤ 2^(k+m)) (hn : neg ≤ 2^(k+m)) :
    2^m*t + neg < 2^(k+m+2) ∧ 2^k + pos < 2^(k+m+2) := by
  have kt : 2^m*t < 2^(k+m)*2 := by
    calc
      2^m*t < 2^m*2^(k+1) := Nat.mul_lt_mul_of_pos_left ht (by positivity)
      _ = 2^(k+m)*2 := by rw [pow_succ, pow_add]; ring
  have hk : 2^k ≤ 2^(k+m) := Nat.pow_le_pow_right (by decide) (by omega)
  have hpos : 0 < 2^(k+m) := by positivity
  rw [pow_add (2 : ℕ) (k+m) 2]
  omega

end PEqualNP.Outside.L_meta_33635.ScheduledThreshold

namespace PEqualNP.Outside.L_meta_33635.ScheduledColorIdentity

open ScheduledWindows ScheduledWalsh ScheduledTrace ScheduledRotated ScheduledLabels
open PEqualNP.Outside.L_meta_33635.Pivot
open scoped BigOperators

theorem sign_fold {q : ℕ} (b : Fin q → Bool) :
    sign ((List.ofFn b).foldr xor false) = ∏ i, sign (b i) := by
  have listRule (xs : List Bool) : sign (xs.foldr xor false) = (xs.map sign).prod := by
    induction xs with
    | nil => rfl
    | cons x xs ih => simp [sign_xor, ih]
  rw [listRule, Fin.prod_univ_def, ←List.ofFn_eq_map, List.map_ofFn]
  rfl

def gateLabel {q s r l : ℕ} (hq : 0 < q) (hs : 0 < s) (hsl : s ≤ l)
    (off : Fin (q*s)) (nr nc : Fin (2^(q*s))) (cr cc : Fin r → Fin (2^(q*s)))
    (bank : Fin q → Bool) (m mask : ℕ) (col : Fin q → ℕ)
    (t : ℕ) (a b : Fin (2^l)) : Bool :=
  let i : Fin q := ⟨t % q,Nat.mod_lt _ hq⟩
  par m mask (col i) && sensor hs nr nc cr cc off bank i
    (representative (site hs off i) (edgeWindow (firstBits hsl (bits l a)) (bits l b)))

noncomputable def keyPath {q s l : ℕ} (hq : 0 < q) (hs : 0 < s)
    (off : Fin (q*s)) (hsl : s ≤ l) : Fin (2^(q*s)) ≃ ClosedPath (numericOverlapEdge hsl) q :=
  (closed hq hs off hsl).trans (numericWindowsPathEquiv hq hsl)

theorem character_path {q s r l : ℕ} (hq : 0 < q) (hs : 0 < s) (hsl : s ≤ l)
    (hk : 2 ≤ q*s) (hr : 4 ≤ r) (hw : l+s ≤ q*s)
    (off : Fin (q*s)) (nr nc : Fin (2^(q*s))) (cr cc : Fin r → Fin (2^(q*s)))
    (bank : Fin q → Bool) (reach : ∀ i, (if bank i then 7*r-2 else 5*r-3) < l+s)
    (m mask : ℕ) (col : Fin q → ℕ) (w : Fin (2^(q*s))) :
    let lab := gateLabel hq hs hsl off nr nc cr cc bank m mask col
    let path := keyPath hq hs off hsl w
    sign (par m mask (report col (sensor hs nr nc cr cc off bank) w)) =
      sign (pathParity lab q path.val.1 path.val.2) := by
  let lab := gateLabel hq hs hsl off nr nc cr cc bank m mask col
  let p := closed hq hs off hsl w
  change _ = sign (pathParity lab q ((numericWindowsPathEquiv hq hsl p).val.1)
    ((numericWindowsPathEquiv hq hsl p).val.2))
  rw [numericWindowsPath_parity, sign_fold, report_product]
  apply Finset.prod_congr rfl
  intro i _
  have recover (x : ScheduledWindows.Word l) : bits l ((bitsEquiv l).symm x) = x :=
    (bitsEquiv l).apply_symm_apply x
  dsimp only [lab, gateLabel]
  rw [recover, recover]
  have pos : (⟨i.val % q,Nat.mod_lt _ hq⟩ : Fin q) = i := Fin.ext (Nat.mod_eq_of_lt i.isLt)
  change factor m mask col (sensor hs nr nc cr cc off bank) w i =
    sign (par m mask (col ⟨i.val % q,_⟩) && sensor hs nr nc cr cc off bank ⟨i.val % q,_⟩
      (representative (site hs off ⟨i.val % q,_⟩) (localWindow hq hsl p i)))
  rw [pos, closed_sensor hq hs hk hr off hsl nr nc cr cc bank w i hw (reach i)]
  cases h : par m mask (col i) <;> simp [factor, h, sign]

theorem sum_sign {X : Type*} [Fintype X] (b : X → Bool) :
    (∑ x, sign (b x)) = (Fintype.card {x : X // b x = false} : ℤ) -
      Fintype.card {x : X // b x = true} := by
  classical
  simp only [Fintype.card_subtype, Finset.card_filter, Nat.cast_sum, Nat.cast_ite,
    Nat.cast_one, Nat.cast_zero, ←Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro x _
  cases b x <;> simp [sign]

theorem character_trace {q s r l : ℕ} (hq : 0 < q) (hs : 0 < s) (hsl : s ≤ l)
    (hk : 2 ≤ q*s) (hr : 4 ≤ r) (hw : l+s ≤ q*s)
    (off : Fin (q*s)) (nr nc : Fin (2^(q*s))) (cr cc : Fin r → Fin (2^(q*s)))
    (bank : Fin q → Bool) (reach : ∀ i, (if bank i then 7*r-2 else 5*r-3) < l+s)
    (m mask : ℕ) (col : Fin q → ℕ) :
    let edge := numericOverlapEdge hsl
    let lab := gateLabel hq hs hsl off nr nc cr cc bank m mask col
    (∑ w, sign (par m mask (report col (sensor hs nr nc cr cc off bank) w))) =
      Matrix.trace (transfer (signedAdjacency edge lab) q) := by
  let edge := numericOverlapEdge hsl
  let lab := gateLabel hq hs hsl off nr nc cr cc bank m mask col
  let e := keyPath hq hs off hsl
  let b := fun w : Fin (2^(q*s)) => pathParity lab q (e w).val.1 (e w).val.2
  change _ = Matrix.trace (transfer (signedAdjacency edge lab) q)
  calc
    _ = ∑ w, sign (b w) := Finset.sum_congr rfl fun w _ =>
      character_path hq hs hsl hk hr hw off nr nc cr cc bank reach m mask col w
    _ = _ := by
      rw [sum_sign, trace_parity_difference, parityDP_count_of_equiv edge lab q e false,
        parityDP_count_of_equiv edge lab q e true]

theorem character_counts {q s r l : ℕ} (hq : 0 < q) (hs : 0 < s) (hsl : s ≤ l)
    (hk : 2 ≤ q*s) (hr : 4 ≤ r) (hw : l+s ≤ q*s)
    (off : Fin (q*s)) (nr nc : Fin (2^(q*s))) (cr cc : Fin r → Fin (2^(q*s)))
    (bank : Fin q → Bool) (reach : ∀ i, (if bank i then 7*r-2 else 5*r-3) < l+s)
    (m mask : ℕ) (col : Fin q → ℕ) :
    let edge := numericOverlapEdge hsl
    let lab := gateLabel hq hs hsl off nr nc cr cc bank m mask col
    (∑ w, sign (par m mask (report col (sensor hs nr nc cr cc off bank) w))) =
      ((∑ a, parityDP edge lab q a a false : ℕ) : ℤ) - (∑ a, parityDP edge lab q a a true : ℕ) := by
  exact (character_trace hq hs hsl hk hr hw off nr nc cr cc bank reach m mask col).trans
    (trace_parity_difference _ _ _)

theorem diagonal_count_le {q s l : ℕ} (hq : 0 < q) (hs : 0 < s) (hsl : s ≤ l)
    (off : Fin (q*s)) (lab : ℕ → Fin (2^l) → Fin (2^l) → Bool) (b : Bool) :
    (∑ a, parityDP (numericOverlapEdge hsl) lab q a a b) ≤ 2^(q*s) := by
  classical
  rw [parityDP_count_of_equiv _ lab q (keyPath hq hs off hsl) b]
  exact (Fintype.card_le_of_injective Subtype.val Subtype.val_injective).trans_eq (Fintype.card_fin _)

open ScheduledCombined ScheduledColorMasks

theorem at_least_three {n : ℕ} (es : List (Fin n × Fin n)) : 3 ≤ (columns es).length := by
  simp [columns]

theorem graph_comparison {n s d r : ℕ} (es : List (Fin n × Fin n))
    (hs : 0 < s) (hr : 4 ≤ r) (hd₁ : 2*s ≤ d) (hd₂ : d < 3*s) :
    let q := (columns es).length
    let k := q*s
    let l := d+1-s
    let hq : 0 < q := lt_of_lt_of_le (by decide : 0<3) (at_least_three es)
    let hsl : s ≤ l := by dsimp [l]; omega
    ∀ (nr nc : Fin (2^k)) (cr cc : Fin r → Fin (2^k)) (off : Fin k) (bank : Fin q → Bool),
    (∀ i, (if bank i then 7*r-2 else 5*r-3) ≤ d) →
    ∀ (y : Fin (2^(2*n+1))) (t : ℕ),
    let swap := fun c => par (2*n+1) (normalOf c) y.val
    let edge := numericOverlapEdge hsl
    let lab := fun c => gateLabel hq hs hsl off nr nc cr cc bank (2*n+1) (normalOf c) (columns es).get
    let count := fun c b => ∑ a, parityDP edge (lab c) q a a b
    let f := report (columns es).get (sensor hs nr nc cr cc off bank)
    t ≤ Nat.card {w : Fin (2^k) // f w = y.val} ↔
      2^(2*n+1)*t + (∑ c ∈ colors es, if swap c then count c false else count c true) ≤
        2^k + (∑ c ∈ colors es, if swap c then count c true else count c false) := by
  intro q k l hq hsl nr nc cr cc off bank valid y t swap edge lab count f
  apply ScheduledThreshold.unsigned_threshold (colors es) swap (fun c => count c false)
    (fun c => count c true)
  have hp := sensor_gap_flip hs hr hd₂ nr nc cr cc off bank valid
  have h := (count_formulas es (key_width es hs) (sensor hs nr nc cr cc off bank) hp).1 y
  refine h.trans ?_
  apply congrArg ((2:ℤ)^k + ·)
  apply Finset.sum_congr rfl
  intro c _
  apply congrArg (sign (swap c) * ·)
  have hthree : 3*s ≤ k := Nat.mul_le_mul_right s (at_least_three es)
  have hlen : l+s = d+1 := by dsimp [l]; omega
  apply character_counts hq hs hsl (by omega) hr (by omega) off nr nc cr cc bank
  intro i
  have hi := valid i
  omega

end PEqualNP.Outside.L_meta_33635.ScheduledColorIdentity

namespace PEqualNP.Outside.L_meta_33635.ScheduledInstantiation

open PEqualNP.Outside.L_meta_33635 Builder Compiler
open ScheduledLayout ScheduledColorIdentity ScheduledWindows ScheduledWalsh ScheduledLabels

def tag {k r q m : ℕ} (mask : ℕ) (x : Env (inLen k r q m)) : Bool :=
  par m mask (target x).val

def labels {q s r m l : ℕ} (hq : 0<q) (hs : 0<s) (hsl : s≤l) (off : Fin (q*s))
    (mask : ℕ) (col : Fin q → ℕ) (x : Env (inLen (q*s) r q m)) : Edge (2^l) :=
  gateLabel hq hs hsl off (rowName x) (colName x) (rowSchedule x) (colSchedule x)
    (bankBit x) m mask col

def prep (k r q m D : ℕ) := (1+m*4) + q*(D*D)*((k*4+r*(k*22))+((k*4+r*(k*22))+4))

theorem prepare {q s r m l : ℕ} (hq : 0<q) (hs : 0<s) (hsl : s≤l) (off : Fin (q*s))
    (B : Bank (inLen (q*s) r q m)) (ext : (Bank.empty _).Ext B)
    (hz : B.Has (fun _ => false)) (ho : B.Has (fun _ => true)) (mask : ℕ) (col : Fin q → ℕ) :
    B.Grow (prep (q*s) r q m (2^l)) (fun E => E.Has (tag mask) ∧ ∀ i, i<q → ∀ a b,
      E.Has (fun x => labels hq hs hsl off mask col x i a b)) := by
  let k := q*s
  have hk : 0<k := Nat.mul_pos hq hs
  let rep (z : Fin q × Fin (2^l) × Fin (2^l)) : Fin (2^k) :=
    representative (Pivot.site hs off z.1)
      (edgeWindow (firstBits hsl (ScheduledWindows.bits l z.2.1)) (ScheduledWindows.bits l z.2.2))
  let row (j : Fin q) : Fin k := ⟨((Pivot.site hs off j).val+(2*r-2))%k, Nat.mod_lt _ hk⟩
  let column (j : Fin q) : Fin k := ⟨((Pivot.site hs off j).val+(3*r+1))%k, Nat.mod_lt _ hk⟩
  obtain ⟨C,eC,kC,htag⟩ := characterBit B hz mask (fun x => (target x).val)
    (readWord_wires B ext hz m (3*k+2*r*k+q))
  have e : (Bank.empty _).Ext C := Bank.ext_trans ext eC
  have z := eC hz
  have const (b : Bool) : C.Has (fun _ => b) := by cases b <;> first | exact eC hz | exact eC ho
  obtain ⟨F,eF,kF,tab⟩ := SensorBuilder.labelTable hk C rep rowName colName rowSchedule colSchedule
    (fun j x => bankBit x j) (fun j => par m mask (col j)) row column const
    (readWord_wires C e z k 0) (readWord_wires C e z k k)
    (fun j => readWord_wires C e z k (2*k+j.val*k))
    (fun j => readWord_wires C e z k (2*k+r*k+j.val*k))
    (fun j => empty_raw C e z (3*k+2*r*k+j.val))
  refine ⟨F,Bank.ext_trans eC eF,?_,eF htag,?_⟩
  · simp only [Fintype.card_prod,Fintype.card_fin] at kF
    dsimp only [prep,k] at *
    omega
  · intro i hi a b
    let j : Fin q := ⟨i,hi⟩
    have hj : (⟨i % q,Nat.mod_lt _ hq⟩ : Fin q) = j := Fin.ext (Nat.mod_eq_of_lt hi)
    refine (show _ = (fun x => labels hq hs hsl off mask col x i a b) from ?_) ▸ tab (j,a,b)
    funext x
    unfold labels gateLabel
    dsimp only
    rw [hj]
    cases hp : par m mask (col j) <;> cases hb : bankBit x j <;>
      simp [Pivot.sensor, hb, rep, row, column, k]

theorem fixedOffset {α : Type*} [DecidableEq α] {q s r m l d : ℕ}
    (hq : 0<q) (hs : 0<s) (hsl : s≤l) (off : Fin (q*s))
    (B : Bank (inLen (q*s) r q m)) (ext : (Bank.empty _).Ext B)
    (hz : B.Has (fun _ => false)) (ho : B.Has (fun _ => true)) (hv : B.Has (validFlag d))
    (colors : Finset α) (hc : colors.card ≤ 2^m) (mask : α → ℕ) (col : Fin q → ℕ) :
    let k := q*s
    let w := k+m+2
    let D := 2^l
    let T := tag (k:=k) (r:=r) (q:=q) (m:=m) ∘ mask
    let L := fun c => labels (r:=r) (m:=m) hq hs hsl off (mask c) col
    let edge := numericOverlapEdge hsl
    B.Grow (colors.card*colorCost D w q (prep k r q m D)+(w*35+1)) (fun E =>
      E.Has (fun x => validFlag d x && decide
        (2^m*(threshold x).val+colorTotal colors edge T L q true x ≤
          2^k+colorTotal colors edge T L q false x))) := by
  dsimp only
  apply growScheduledThreshold (w:=q*s+m+2) B hz ho (validFlag d) hv
    (fun x => (threshold x).val) (widenWord B hz _ (fun x => (threshold x).isLt)
      (readWord_wires B ext hz (q*s+1) (3*(q*s)+2*r*(q*s)+q+m)))
  · intro c _ C e
    exact prepare hq hs hsl off C (Bank.ext_trans ext e) (e hz) (e ho) (mask c) col
  · intro x _
    apply ScheduledThreshold.width (threshold x).isLt
    all_goals
      apply ScheduledThreshold.total_le _ _ hc
      intro c _
      exact diagonal_count_le hq hs hsl off _ _

end PEqualNP.Outside.L_meta_33635.ScheduledInstantiation

namespace PEqualNP.Outside.L_meta_33635.ScheduledBudget

open PEqualNP.Outside.L_meta_33635

def sensorCost (k r q D : ℕ) := q*D^2*(2*(4*k+22*r*k)+4)

def prepCost (k r m q D : ℕ) := sensorCost k r q D + (1+4*m)

def thresholdCost (k r m q D w c : ℕ) :=
  c*Compiler.colorCost D w q (prepCost k r m q D) + (35*w+1)

def selectCost (k cost : ℕ) := k*((k*5+(1+k))+(cost+1))+(1+k)

def actualCost (k r m q D w c : ℕ) :=
  2+(5*q+1)+selectCost k (thresholdCost k r m q D w c)

def repeatedValidCost (k r m q D w c : ℕ) :=
  2+(5*q+1)+selectCost k (thresholdCost k r m q D w c+(5*q+1))

theorem prepCost_eq_literal (k r m q D : ℕ) :
    prepCost k r m q D =
      (1+m*4)+q*(D*D)*((k*4+r*(k*22))+((k*4+r*(k*22))+4)) := by
  unfold prepCost sensorCost
  ring

theorem actualCost_eq_literal (k r m q D w c : ℕ) :
    actualCost k r m q D w c =
      2+(5*q+1)+(k*((k*5+(1+k))+
        ((c*Compiler.colorCost D w q
          ((1+m*4)+q*(D*D)*((k*4+r*(k*22))+((k*4+r*(k*22))+4)))+(w*35+1))+1))+
          (1+k)) := by
  simp only [actualCost, selectCost, thresholdCost, prepCost_eq_literal]
  ring

theorem prepCost_le {k r m q D P : ℕ} (hD : 0<D) (hP : 0<P)
    (hk : k≤P) (hr : r≤P) (hm : m≤P) (hq : q≤P) :
    prepCost k r m q D ≤ 61*(P^3*D^3) := by
  have p12 : P≤P^2 := by simpa using Nat.pow_le_pow_right hP (by decide : 1≤2)
  have p13 : P≤P^3 := by simpa using Nat.pow_le_pow_right hP (by decide : 1≤3)
  have p02 : 1≤P^2 := Nat.pow_pos hP
  have d03 : 1≤D^3 := Nat.pow_pos hD
  have d23 : D^2≤D^3 := Nat.pow_le_pow_right hD (by decide)
  have rk : r*k≤P^2 := by simpa [pow_two] using Nat.mul_le_mul hr hk
  have coefficient : 2*(4*k+22*r*k)+4≤56*P^2 := by
    have := hk.trans p12
    nlinarith
  have table : sensorCost k r q D ≤ 56*(P^3*D^3) := by
    calc
      sensorCost k r q D ≤ P*D^3*(56*P^2) :=
        Nat.mul_le_mul (Nat.mul_le_mul hq d23) coefficient
      _ = 56*(P^3*D^3) := by ring
  have pT : P≤P^3*D^3 := by
    calc P = P*1 := by simp
         _ ≤ P^3*D^3 := Nat.mul_le_mul p13 d03
  have mT := hm.trans pT
  have oneT : 1≤P^3*D^3 := le_trans (show 1≤P from hP) pT
  unfold prepCost
  omega

theorem colorCost_le {k r m q D w P : ℕ} (hD : 0<D) (hP : 0<P)
    (hk : k≤P) (hr : r≤P) (hm : m≤P) (hq : q≤P) (hw : w≤P) :
    Compiler.colorCost D w q (prepCost k r m q D) ≤ 155*(P^3*D^3) := by
  have pre := prepCost_le hD hP hk hr hm hq
  have base := Compiler.colorCost_le hD hP hw hq (prepCost k r m q D)
  have pp : P^2*D^3≤P^3*D^3 :=
    Nat.mul_le_mul_right _ (Nat.pow_le_pow_right hP (by decide : 2≤3))
  omega

theorem coarse_cost_le {k r m q D w P c : ℕ} (hD : 0<D) (hP : 0<P)
    (hk : k≤P) (hr : r≤P) (hm : m≤P) (hq : q≤P) (hw : w≤P) :
    repeatedValidCost k r m q D w c ≤ 256*P^4*(1+c*D^3) := by
  let B := P^3*(1+c*D^3)
  have p13 : P≤P^3 := by simpa using Nat.pow_le_pow_right hP (by decide : 1≤3)
  have pB : P≤B := by
    calc P = P*1 := by simp
         _ ≤ B := Nat.mul_le_mul p13 (by omega)
  have oneB : 1≤B := le_trans (show 1≤P from hP) pB
  have kB := hk.trans pB
  have qB := hq.trans pB
  have wB := hw.trans pB
  have cT : c*(P^3*D^3)≤B := by
    dsimp [B]
    nlinarith
  have hcolor : c*Compiler.colorCost D w q (prepCost k r m q D) ≤ 155*B := by
    calc
      _ ≤ c*(155*(P^3*D^3)) :=
        Nat.mul_le_mul_left _ (colorCost_le hD hP hk hr hm hq hw)
      _ = 155*(c*(P^3*D^3)) := by ring
      _ ≤ 155*B := Nat.mul_le_mul_left _ cT
  have inner : thresholdCost k r m q D w c+(5*q+1)≤197*B := by
    unfold thresholdCost
    omega
  have cmp : k*5+(1+k)≤7*B := by omega
  have sum : (k*5+(1+k))+((thresholdCost k r m q D w c+(5*q+1))+1)≤205*B := by
    omega
  have pkB : k*B≤P*B := Nat.mul_le_mul_right B hk
  have pPB : P≤P*B := by simpa using Nat.mul_le_mul_left P oneB
  have kPB := hk.trans pPB
  have qPB := hq.trans pPB
  have onePB : 1≤P*B := le_trans (show 1≤P from hP) pPB
  have selected : selectCost k (thresholdCost k r m q D w c+(5*q+1))≤207*(P*B) := by
    unfold selectCost
    calc
      _ ≤ k*(205*B)+(1+k) := Nat.add_le_add_right (Nat.mul_le_mul_left _ sum) _
      _ = 205*(k*B)+(1+k) := by ring
      _ ≤ 207*(P*B) := by omega
  have total : repeatedValidCost k r m q D w c≤215*(P*B) := by
    unfold repeatedValidCost
    omega
  calc
    _ ≤ 215*(P*B) := total
    _ ≤ 256*(P*B) := Nat.mul_le_mul_right _ (by decide)
    _ = 256*P^4*(1+c*D^3) := by dsimp [B]; ring

theorem actualCost_le_repeated (k r m q D w c : ℕ) :
    actualCost k r m q D w c≤repeatedValidCost k r m q D w c := by
  unfold actualCost repeatedValidCost selectCost
  apply Nat.add_le_add_left
  apply Nat.add_le_add_right
  exact Nat.mul_le_mul_left k (by omega)

theorem global_cost_le_repeated_valid (k r m q l s c : ℕ) (hq : q≤k) :
    repeatedValidCost k r m q (2^l) (k+m+2) c ≤
      2^44*(k+r+m+5)^16*(1+c*(2^(l+s)+2^(3*l))) := by
  let P := k+r+m+5
  have hP : 0<P := by dsimp [P]; omega
  have coarse := coarse_cost_le (k:=k) (r:=r) (m:=m) (q:=q) (D:=2^l)
    (w:=k+m+2) (P:=P) (c:=c) (by positivity) hP
    (by dsimp [P]; omega) (by dsimp [P]; omega) (by dsimp [P]; omega)
    (by dsimp [P]; omega) (by dsimp [P]; omega)
  have powers : (2^l)^3=2^(3*l) := by rw [← Nat.pow_mul, Nat.mul_comm l 3]
  rw [powers] at coarse
  have poly : 256*P^4 ≤ 2^44*P^16 :=
    Nat.mul_le_mul (by decide) (Nat.pow_le_pow_right hP (by decide : 4≤16))
  have exp : 1+c*2^(3*l)≤1+c*(2^(l+s)+2^(3*l)) := by
    exact Nat.add_le_add_left (Nat.mul_le_mul_left c (Nat.le_add_left _ _)) 1
  exact coarse.trans (Nat.mul_le_mul poly exp)

theorem global_cost_le (k r m q l s c : ℕ) (hq : q≤k) :
    actualCost k r m q (2^l) (k+m+2) c ≤
      2^44*(k+r+m+5)^16*(1+c*(2^(l+s)+2^(3*l))) :=
  (actualCost_le_repeated ..).trans (global_cost_le_repeated_valid k r m q l s c hq)

end PEqualNP.Outside.L_meta_33635.ScheduledBudget

namespace PEqualNP.Outside.L_meta_33635.ScheduledCombined
open PEqualNP.Outside.L_meta_33635

theorem exact_counts : (∀ (n : Nat) (es : List (Fin n × Fin n)) (s d r : Nat),
  0 < s → 4 ≤ r → 2*s ≤ d → d < 3*s →
  let m := 2*n+1
  let lo := fun i : Fin n => (1 : Nat) <<< (2*i.val+1)
  let hi := fun i : Fin n => (1 : Nat) <<< (2*i.val+2)
  let cols : List Nat := [1,1,1] ++
    (List.finRange n).flatMap (fun i => [lo i, hi i, 1]) ++
    es.flatMap (fun e => [lo e.1 ^^^ lo e.2, hi e.1 ^^^ hi e.2, 1])
  let q := cols.length
  let k := q*s
  let Y := Fin (2^m)
  let C := Fin n → Fin 3
  let proper := fun (c : C) => ∀ e ∈ es, c e.1 ≠ c e.2
  let normal := fun (c : C) => (List.finRange n).foldl
    (fun p i => p ||| (((c i).val+1) <<< (2*i.val+1))) (1 : Nat)
  let par := fun (mask : Nat) (y : Y) => (List.range m).foldl
    (fun b j => xor b (mask.testBit j && y.val.testBit j)) false
  let rot := fun (h w : Nat) =>
    ((w <<< (h % k)) ||| (w >>> (k - h % k))) % 2^k
  let step := fun (w : Nat) =>
    (List.range k).foldl (fun acc i => acc ||| ((xor (w.testBit i)
      (!(w.testBit ((i+1)%k)) && w.testBit ((i+2)%k))).toNat <<< i)) 0
  let state := fun (col : Bool) (w name : Nat) (c : Fin r → Fin (2^k)) =>
    let g := if col then 2 else 1
    (List.finRange r).foldl (fun x j =>
      step (x ^^^ rot g x ^^^ rot (k-g) x) ^^^
        rot (if col then 3*(j.val+1)+1 else 2*j.val) w ^^^ (c j).val)
      (rot (if col then 3 else 1) w ^^^ name)
  let reach := fun col : Bool => if col then 7*r-2 else 5*r-3
  let delay := fun col : Bool => if col then 3*r+1 else 2*r-2
  let sign := fun b : Bool => if b then (-1 : ℤ) else 1
  let colors := (Finset.univ : Finset C).filter proper
    ∀ (nr nc : Fin (2^k)) (cr cc : Fin r → Fin (2^k)) (off : Fin k) (bank : Fin q → Bool),
      let p := fun i : Fin q => (off.val+i.val*s)%k
      let sensor := fun (i : Fin q) (w : Nat) =>
        (state (bank i) w (if bank i then nc.val else nr.val)
          (if bank i then cc else cr)).testBit ((p i + delay (bank i))%k)
      let valid := ∀ i, reach (bank i) ≤ d
      let report := fun (w : Nat) => (List.finRange q).foldl
        (fun z i => if sensor i w then z ^^^ cols.get i else z) (0 : Nat)
      let chi := fun (c : C) (w : Nat) => (List.range m).foldl
        (fun b j => xor b ((normal c).testBit j && w.testBit j)) false
      let hits := fun y : Y => Nat.card {w : Fin (2^k) // report w.val = y.val}
      (valid → ∀ y : Y, (2 : ℤ)^m * (hits y : ℤ) = (2 : ℤ)^k +
        ∑ c ∈ colors, sign (par (normal c) y) *
          (∑ w : Fin (2^k), sign (chi c (report w.val)))) ∧
      (valid → colors.card = 0 → ∀ y : Y, hits y = 2^(k-m))) := by
  intro n es s d r hs hr _ hd
  dsimp only
  intro nr nc cr cc off bank
  constructor
  · intro valid
    exact (count_formulas es (key_width es hs) (Pivot.sensor hs nr nc cr cc off bank)
      (Pivot.sensor_gap_flip hs hr hd nr nc cr cc off bank valid)).1
  · intro valid
    exact (count_formulas es (key_width es hs) (Pivot.sensor hs nr nc cr cc off bank)
      (Pivot.sensor_gap_flip hs hr hd nr nc cr cc off bank valid)).2

end PEqualNP.Outside.L_meta_33635.ScheduledCombined

namespace PEqualNP.Outside.L_meta_33635.Offset

open Builder

private theorem allFold {A : Type*} (l : List A) (f : A → Bool) (v : Bool) :
    l.foldl (fun b i => b && f i) v = true ↔ v = true ∧ ∀ i ∈ l, f i = true := by
  induction l generalizing v with
  | nil => simp
  | cons a l ih => simp [List.foldl_cons, ih, and_assoc]

private theorem anyFold {A : Type*} (l : List A) (f : A → Bool) (v : Bool) :
    l.foldl (fun b i => b || f i) v = true ↔ v = true ∨ ∃ i ∈ l, f i = true := by
  induction l generalizing v with
  | nil => simp
  | cons a l ih => simp [List.foldl_cons, ih, or_assoc]

theorem compareConst {n k : ℕ} (B : Bank n) (u : (Fin n → Bool) → Fin (2^k))
    (a : Fin (2^k)) (hc : ∀ b : Bool, B.Has (fun _ => b))
    (hu : ∀ i : Fin k, B.Has (fun x => (u x).val.testBit i.val)) :
    B.Grow (k*5+(1+k)) (fun E => E.Has (fun x => decide (u x = a))) := by
  let matchBit (i : Fin k) (x : Fin n → Bool) := (u x).val.testBit i.val == a.val.testBit i.val
  apply (B.collectFin k matchBit 5 (fun E e i => Bank.eqBool (e (hu i))
    (e (hc (a.val.testBit i.val))))).bind
  intro C _ matchWires
  apply (C.andList (List.finRange k) matchBit (fun i _ => matchWires i)).weaken (by simp)
  intro D h
  convert h using 1
  funext x
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq, allFold, true_and, List.mem_finRange, forall_true_left]
  constructor
  · intro eq i
    simp [matchBit,eq]
  · intro eq
    apply ScheduledWindows.bits_injective k
    funext i
    simpa [ScheduledWindows.bits, matchBit] using eq i

theorem selectOffset {n k cost : ℕ} (B : Bank n)
    (u : (Fin n → Bool) → Fin (2^k)) (code : Fin k → Fin (2^k))
    (answer : Fin k → BitFn n) (hc : ∀ b : Bool, B.Has (fun _ => b))
    (hu : ∀ i : Fin k, B.Has (fun x => (u x).val.testBit i.val))
    (emit : ∀ D : Bank n, B.Ext D → ∀ i, D.Grow cost (fun E => E.Has (answer i))) :
    B.Grow (k*((k*5+(1+k))+(cost+1))+(1+k))
      (fun E => E.Has (fun x => decide (∃ i, u x = code i ∧ answer i x = true))) := by
  let hit (i : Fin k) (x : Fin n → Bool) := decide (u x = code i) && answer i x
  apply (B.collectFin k hit _ (fun D e i => by
    apply (compareConst D u (code i) (fun b => e (hc b)) (fun j => e (hu j))).bind
    intro C ec eq
    apply (emit C (Bank.ext_trans e ec) i).bind
    intro F ef a
    exact Bank.meet (ef eq) a)).bind
  intro C _ hx
  apply (C.orList (List.finRange k) hit (fun i _ => hx i)).weaken (by simp)
  intro D h
  convert h using 1
  funext x
  apply Bool.eq_iff_iff.mpr
  simp [anyFold,hit]

end PEqualNP.Outside.L_meta_33635.Offset

namespace PEqualNP.Outside.L_meta_33635.ScheduledFinal

open PEqualNP PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_33635 Builder Compiler Pivot
open ScheduledLayout ScheduledInstantiation ScheduledColorIdentity ScheduledColorMasks ScheduledCombined
open ScheduledWindows ScheduledTrace ScheduledWalsh
open scoped BigOperators

def offsetCode {k : ℕ} (i : Fin k) : Fin (2^k) :=
  ⟨i.val, i.isLt.trans Nat.lt_two_pow_self⟩

def fixedAnswer {α : Type*} {q s r m l : ℕ} (hq : 0<q) (hs : 0<s) (hsl : s≤l)
    (d : ℕ) (colors : Finset α) (mask : α → ℕ) (col : Fin q → ℕ)
    (off : Fin (q*s)) (x : Env (inLen (q*s) r q m)) : Bool :=
  let T := tag (k:=q*s) (r:=r) (q:=q) (m:=m) ∘ mask
  let L := fun c => labels (r:=r) (m:=m) hq hs hsl off (mask c) col
  validFlag d x && decide (2^m*(threshold x).val +
    colorTotal colors (numericOverlapEdge hsl) T L q true x ≤
    2^(q*s)+colorTotal colors (numericOverlapEdge hsl) T L q false x)

theorem build {α : Type*} [DecidableEq α] {q s r m l : ℕ}
    (hq : 0<q) (hs : 0<s) (hsl : s≤l) (d : ℕ) (colors : Finset α)
    (hc : colors.card ≤ 2^m) (mask : α → ℕ) (col : Fin q → ℕ) :
    let k := q*s
    let n := inLen k r q m
    ∃ C : Circuit, FanInTwo C ∧ NestedCover.ReadsBack n C ∧
      C.size ≤ 2^44*(k+r+m+5)^16*(1+colors.card*(2^(l+s)+2^(3*l))) ∧
      ∀ x : Env n, C.eval (List.ofFn x) = decide (∃ i : Fin k,
        offsetWord x = offsetCode i ∧ fixedAnswer hq hs hsl d colors mask col i x = true) := by
  intro k n
  let B := Bank.empty n
  let w := k+m+2
  let D := 2^l
  let cost := colors.card*colorCost D w q (prep k r q m D)+(w*35+1)
  let ans := fixedAnswer (r:=r) (m:=m) hq hs hsl d colors mask col
  let bound := 2^44*(k+r+m+5)^16*(1+colors.card*(2^(l+s)+2^(3*l)))
  have qsmall : q≤k := by simpa [k] using Nat.mul_le_mul_left q (show 1≤s by omega)
  have prepEq : prep k r q m D = ScheduledBudget.prepCost k r m q D := by
    unfold prep ScheduledBudget.prepCost ScheduledBudget.sensorCost
    ring
  have costEq : cost = ScheduledBudget.thresholdCost k r m q D w colors.card := by
    simp only [cost, prepEq, ScheduledBudget.thresholdCost, Nat.mul_comm w 35]
  have enough : 1+(1+((5*q+1)+ScheduledBudget.selectCost k cost)) ≤ bound := by
    have h := ScheduledBudget.global_cost_le k r m q l s colors.card qsmall
    change 2+(5*q+1)+ScheduledBudget.selectCost k
      (ScheduledBudget.thresholdCost k r m q D w colors.card) ≤ bound at h
    rw [costEq]
    omega
  apply Bank.finish
  apply Bank.Grow.weaken (b:=bound) (hab:=enough) (hpq:=fun _ h => h)
  apply (B.const false).bind
  intro B1 e1 hz
  apply (B1.const true).bind
  intro B2 e2 ho
  have e02 : B.Ext B2 := Bank.ext_trans e1 e2
  apply (valid_wires (k:=k) (r:=r) (q:=q) (m:=m) d B2 e02 (e2 hz) ho).bind
  intro B3 e3 hv
  have ez := e3 (e2 hz)
  have eo := e3 ho
  have e03 : B.Ext B3 := Bank.ext_trans e02 e3
  apply Offset.selectOffset B3 (offsetWord (k:=k) (r:=r) (q:=q) (m:=m)) offsetCode ans
    (fun b => by cases b <;> assumption) (readWord_wires B3 e03 ez k (2*k+2*r*k))
  intro E e off
  exact fixedOffset hq hs hsl off E (Bank.ext_trans e03 e) (e ez) (e eo) (e hv)
    colors hc mask col

theorem total_as_if {α : Type*} {D n : ℕ} (colors : Finset α) (edge : Edge D)
    (T : α → BitFn n) (L : α → Compiler.Labels n D) (q : ℕ) (p : Bool) (x : Env n) :
    colorTotal colors edge T L q p x =
      ∑ c ∈ colors, if T c x then (∑ a, parityDP edge (L c x) q a a (!p))
                    else (∑ a, parityDP edge (L c x) q a a p) := by
  apply Finset.sum_congr rfl
  intro c _
  cases T c x <;> simp

theorem evaluate {n s d r : ℕ} (es : List (Fin n × Fin n)) (hs : 0<s)
    (hr : 4≤r) (hd₁ : 2*s≤d) (hd₂ : d<3*s) :
    let q := (columns es).length
    let k := q*s
    let m := 2*n+1
    let l := d+1-s
    let hq : 0<q := lt_of_lt_of_le (by decide : 0<3) (at_least_three es)
    let hsl : s≤l := by dsimp [l]; omega
    ∀ (nr nc : Fin (2^k)) (cr cc : Fin r → Fin (2^k)) (off : Fin k)
      (bank : Fin q → Bool) (y : Fin (2^m)) (t : Fin (2^(k+1))),
    let x := encoded nr nc cr cc off bank y t
    let valid := ∀ i, (if bank i then 7*r-2 else 5*r-3) ≤ d
    let f := report (columns es).get (sensor hs nr nc cr cc off bank)
    (∃ i : Fin k, offsetWord x = offsetCode i ∧
      fixedAnswer hq hs hsl d (colors es) normalOf (columns es).get i x = true) ↔
      valid ∧ t.val ≤ Nat.card {w : Fin (2^k) // f w = y.val} := by
  intro q k m l hq hsl nr nc cr cc off bank y t x valid f
  obtain ⟨hnr,hnc,hcr,hcc,hoff,hbank,hy,ht⟩ := decode_encoded nr nc cr cc off bank y t
  change rowName x=nr at hnr
  change colName x=nc at hnc
  change rowSchedule x=cr at hcr
  change colSchedule x=cc at hcc
  change (offsetWord x).val=off.val at hoff
  change bankBit x=bank at hbank
  change target x=y at hy
  change threshold x=t at ht
  have code (i : Fin k) : offsetWord x = offsetCode i ↔ i=off := by
    constructor
    · intro h
      exact Fin.ext ((congrArg Fin.val h).symm.trans hoff)
    · rintro rfl
      exact Fin.ext hoff
  simp only [code, exists_eq_left]
  unfold fixedAnswer
  have flag : validFlag d x = decide valid := by unfold validFlag; rw [hbank]
  rw [flag, Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq]
  apply and_congr_right
  intro hv
  have hh := graph_comparison es hs hr hd₁ hd₂ nr nc cr cc off bank hv y t.val
  dsimp only at hh
  rw [total_as_if, total_as_if]
  simp only [Bool.not_true, Bool.not_false, tag, Function.comp_apply, labels, hnr,hnc,hcr,hcc,hbank,hy,ht]
  exact hh.symm

end PEqualNP.Outside.L_meta_33635.ScheduledFinal
open PEqualNP.Outside.L_meta_33635 in
theorem PEqualNP.Outside.L_meta_33635 : (∀ (n : Nat) (es : List (Fin n × Fin n)) (s d r : Nat),
  0 < s → 4 ≤ r → 2*s ≤ d → d < 3*s →
  let m := 2*n+1
  let lo := fun i : Fin n => (1 : Nat) <<< (2*i.val+1)
  let hi := fun i : Fin n => (1 : Nat) <<< (2*i.val+2)
  let cols : List Nat := [1,1,1] ++
    (List.finRange n).flatMap (fun i => [lo i, hi i, 1]) ++
    es.flatMap (fun e => [lo e.1 ^^^ lo e.2, hi e.1 ^^^ hi e.2, 1])
  let q := cols.length
  let k := q*s
  let l := d+1-s
  let Y := Fin (2^m)
  let C := Fin n → Fin 3
  let proper := fun (c : C) => ∀ e ∈ es, c e.1 ≠ c e.2
  let normal := fun (c : C) => (List.finRange n).foldl
    (fun p i => p ||| (((c i).val+1) <<< (2*i.val+1))) (1 : Nat)
  let par := fun (mask : Nat) (y : Y) => (List.range m).foldl
    (fun b j => xor b (mask.testBit j && y.val.testBit j)) false
  let rot := fun (h w : Nat) =>
    ((w <<< (h % k)) ||| (w >>> (k - h % k))) % 2^k
  let step := fun (w : Nat) =>
    (List.range k).foldl (fun acc i => acc ||| ((xor (w.testBit i)
      (!(w.testBit ((i+1)%k)) && w.testBit ((i+2)%k))).toNat <<< i)) 0
  let state := fun (col : Bool) (w name : Nat) (c : Fin r → Fin (2^k)) =>
    let g := if col then 2 else 1
    (List.finRange r).foldl (fun x j =>
      step (x ^^^ rot g x ^^^ rot (k-g) x) ^^^
        rot (if col then 3*(j.val+1)+1 else 2*j.val) w ^^^ (c j).val)
      (rot (if col then 3 else 1) w ^^^ name)
  let reach := fun col : Bool => if col then 7*r-2 else 5*r-3
  let delay := fun col : Bool => if col then 3*r+1 else 2*r-2
  let sign := fun b : Bool => if b then (-1 : ℤ) else 1
  let bits := fun (a x : Nat) => (List.range a).map (fun i => x.testBit i)
  let sched := fun (c : Fin r → Fin (2^k)) =>
    (List.finRange r).flatMap (fun j => bits k (c j).val)
  let colors := (Finset.univ : Finset C).filter proper
  ∃ D : PEqualNP.CircuitLowerBounds.Circuit,
    PEqualNP.MetaComplexity.FanInTwo D ∧
    PEqualNP.MetaComplexity.NestedCover.ReadsBack (3*k+2*r*k+q+m+(k+1)) D ∧
    D.size ≤ 2^44*(k+r+m+5)^16*(1+colors.card*(2^(l+s)+2^(3*l))) ∧
    ∀ (nr nc : Fin (2^k)) (cr cc : Fin r → Fin (2^k)) (off : Fin k) (bank : Fin q → Bool),
      let p := fun i : Fin q => (off.val+i.val*s)%k
      let sensor := fun (i : Fin q) (w : Nat) =>
        (state (bank i) w (if bank i then nc.val else nr.val)
          (if bank i then cc else cr)).testBit ((p i + delay (bank i))%k)
      let valid := ∀ i, reach (bank i) ≤ d
      let report := fun (w : Nat) => (List.finRange q).foldl
        (fun z i => if sensor i w then z ^^^ cols.get i else z) (0 : Nat)
      let chi := fun (c : C) (w : Nat) => (List.range m).foldl
        (fun b j => xor b ((normal c).testBit j && w.testBit j)) false
      let hits := fun y : Y => Nat.card {w : Fin (2^k) // report w.val = y.val}
      (valid → ∀ y : Y, (2 : ℤ)^m * (hits y : ℤ) = (2 : ℤ)^k +
        ∑ c ∈ colors, sign (par (normal c) y) *
          (∑ w : Fin (2^k), sign (chi c (report w.val)))) ∧
      (valid → colors.card = 0 → ∀ y : Y, hits y = 2^(k-m)) ∧
      ∀ (y : Y) (t : Fin (2^(k+1))),
        D.eval (bits k nr.val ++ bits k nc.val ++ sched cr ++ sched cc ++ bits k off.val ++
          List.ofFn bank ++ bits m y.val ++ bits (k+1) t.val) = decide (valid ∧ t.val ≤ hits y)) := by
  intro n es s d r hs hr hd₁ hd₂ m lo hi cols q k l Y C proper normal par rot step state reach delay sign bits sched colors
  have hq : 0<q := lt_of_lt_of_le (by decide : 0<3) (ScheduledColorIdentity.at_least_three es)
  have hsl : s≤l := by dsimp [l]; omega
  have hc : colors.card ≤ 2^m := by
    calc
      _ ≤ Fintype.card C := Finset.card_le_univ _
      _ ≤ Fintype.card (Fin (2^m)) := Fintype.card_le_of_injective
        ScheduledCombined.normalized ScheduledCombined.normalized_inj
      _ = _ := Fintype.card_fin _
  obtain ⟨D,fan,back,cost,eval⟩ := ScheduledFinal.build (r:=r) (m:=m)
    hq hs hsl d colors hc normal cols.get
  refine ⟨D,fan,back,cost,?_⟩
  intro nr nc cr cc off bank p sensor valid report chi hits
  obtain ⟨fone,ftwo⟩ := ScheduledCombined.exact_counts n es s d r hs hr hd₁ hd₂ nr nc cr cc off bank
  refine ⟨fone,ftwo,?_⟩
  intro y t
  let x := ScheduledLayout.encoded nr nc cr cc off bank y t
  change D.eval (ScheduledLayout.inputs nr nc cr cc off bank y t) = _
  rw [←ScheduledLayout.ofFn_encoded,eval]
  exact decide_eq_decide.mpr (ScheduledFinal.evaluate es hs hr hd₁ hd₂ nr nc cr cc off bank y t)
