import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_1279
open PEqualNP.CircuitLowerBounds

def dg : Gate := ⟨GateOp.or, []⟩

def run (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem run_snoc (gs : List Gate) (g : Gate) (w : List Bool) :
    run (gs ++ [g]) w = run gs w ++ [g.op.eval (g.inputs.map fun i => (run gs w).getD i false)] := by
  simp [run, List.foldl_append]

theorem run_length (gs : List Gate) (w : List Bool) : (run gs w).length = w.length + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [run]
  | append_singleton gs g ih => rw [run_snoc]; simp [ih]; omega

theorem run_low (gs : List Gate) (w : List Bool) (i : Nat) (h : i < w.length) :
    (run gs w).getD i false = w.getD i false := by
  induction gs using List.reverseRecOn with
  | nil => simp [run]
  | append_singleton gs g ih =>
    rw [run_snoc, List.getD_append _ _ _ _ (by rw [run_length]; omega)]; exact ih

theorem run_eq (gs : List Gate) (w : List Bool) (k : Nat) (hk : k < gs.length)
    (hr : ∀ i ∈ (gs.getD k dg).inputs, i < w.length + k) :
    (run gs w).getD (w.length + k) false =
      (gs.getD k dg).op.eval ((gs.getD k dg).inputs.map fun i => (run gs w).getD i false) := by
  induction gs using List.reverseRecOn with
  | nil => simp at hk
  | append_singleton gs g ih =>
    rw [run_snoc]
    by_cases h : k < gs.length
    · have e : (gs ++ [g]).getD k dg = gs.getD k dg := List.getD_append _ _ _ _ h
      rw [e] at hr ⊢
      rw [List.getD_append _ _ _ _ (by rw [run_length]; omega), ih h hr]
      congr 1
      apply List.map_congr_left
      intro i hi
      rw [List.getD_append _ _ _ _ (by rw [run_length]; have := hr i hi; omega)]
    · have hk' : k = gs.length := by simp at hk; omega
      subst hk'
      have e : (gs ++ [g]).getD gs.length dg = g := by simp
      rw [e] at hr ⊢
      rw [List.getD_append_right _ _ _ _ (by rw [run_length]), run_length]
      simp only [Nat.sub_self, List.getD_cons_zero]
      congr 1
      apply List.map_congr_left
      intro i hi
      rw [List.getD_append _ _ _ _ (by rw [run_length]; have := hr i hi; omega)]

def sgF (p : Nat → Bool) (b : Nat → Nat) (k : Nat) : Nat :=
  ((List.range k).filter p).foldl (fun s i => 2*s + b i) 0

theorem sgF_succ (p : Nat → Bool) (b : Nat → Nat) (k : Nat) :
    sgF p b (k+1) = if p k = true then 2 * sgF p b k + b k else sgF p b k := by
  cases h : p k <;> simp [sgF, List.range_succ, List.filter_append, h]

theorem sgF_lt (p : Nat → Bool) (b : Nat → Nat) (hb : ∀ i, b i ≤ 1) (k : Nat) :
    sgF p b k < 2 ^ ((List.range k).filter p).length := by
  induction k with
  | zero => simp [sgF]
  | succ k ih =>
    rw [sgF_succ]
    have := hb k
    cases h : p k <;> simp [List.range_succ, List.filter_append, h, pow_succ] <;> omega

theorem cnt0 (gs : List Gate) (q : Gate → Bool) :
    ((List.range gs.length).filter (fun i => q (gs.getD i dg))).length =
      (gs.filter q).length := by
  induction gs using List.reverseRecOn with
  | nil => simp
  | append_singleton gs g ih =>
    rw [List.length_append, List.length_singleton, List.range_succ, List.filter_append,
      List.filter_append, List.length_append, List.length_append, ← ih]
    congr 1
    · congr 1
      apply List.filter_congr
      intro i hi
      simp only [List.mem_range] at hi
      rw [List.getD_append _ _ _ _ hi]
    · have e : (gs ++ [g]).getD gs.length dg = g := by simp
      simp only [List.filter_cons, e, List.filter_nil]
      split <;> rfl

theorem cnt (gs : List Gate) (p : Nat → Bool) (q : Gate → Bool)
    (hp : ∀ i, p i = true ↔ (gs.getD i dg).op = GateOp.not)
    (hq : ∀ g, q g = true ↔ g.op = GateOp.not) :
    ((List.range gs.length).filter p).length = (gs.filter q).length := by
  have : p = fun i => q (gs.getD i dg) := by
    funext i
    rw [Bool.eq_iff_iff, hp, hq]
  subst this
  exact cnt0 gs q

theorem raw_ord (n : Nat) (a b : Fin n → Bool) (h : ∀ j, a j = true → b j = true) (i : Nat) :
    (List.ofFn a ++ [false,true]).getD i false = true →
      (List.ofFn b ++ [false,true]).getD i false = true := by
  by_cases hi : i < n
  · rw [List.getD_append _ _ _ _ (by simpa), List.getD_append _ _ _ _ (by simpa)]
    simpa [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem, hi] using h ⟨i, hi⟩
  · rw [List.getD_append_right _ _ _ _ (by simpa using Nat.le_of_not_gt hi),
      List.getD_append_right _ _ _ _ (by simpa using Nat.le_of_not_gt hi)]
    simp

theorem key (gs : List Gate)
    (fan : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not)
    (m : Nat) (X Y : List Bool) (p : Nat → Bool)
    (hp : ∀ i, p i = true ↔ (gs.getD i dg).op = GateOp.not)
    (bx bY : Nat → Nat)
    (hx1 : ∀ i, X.getD (m+i) false = true → bx i = 1)
    (hx0 : ∀ i, X.getD (m+i) false = false → bx i = 0)
    (hy1 : ∀ i, Y.getD (m+i) false = true → bY i = 1)
    (hy0 : ∀ i, Y.getD (m+i) false = false → bY i = 0)
    (hX : ∀ k < gs.length, X.getD (m+k) false =
      (gs.getD k dg).op.eval ((gs.getD k dg).inputs.map fun i => X.getD i false))
    (hY : ∀ k < gs.length, Y.getD (m+k) false =
      (gs.getD k dg).op.eval ((gs.getD k dg).inputs.map fun i => Y.getD i false))
    (rb : ∀ k < gs.length, ∀ i ∈ (gs.getD k dg).inputs, i < m + k)
    (h0 : ∀ i < m, X.getD i false = true → Y.getD i false = true) :
    ∀ k ≤ gs.length, sgF p bY k ≤ sgF p bx k ∧
      (sgF p bY k = sgF p bx k → ∀ i < m + k, X.getD i false = true → Y.getD i false = true) := by
  intro k
  induction k with
  | zero => intro _; exact ⟨by simp [sgF], fun _ => h0⟩
  | succ k ih =>
    intro hk
    have hk' : k < gs.length := hk
    obtain ⟨ih1, ih2⟩ := ih (by omega)
    rw [sgF_succ, sgF_succ]
    have hg : gs.getD k dg ∈ gs := by
      rw [List.getD_eq_getElem _ _ hk']; exact List.getElem_mem _
    have ex := hX k hk'
    have ey := hY k hk'
    have r := rb k hk'
    rcases fan _ hg with h | h | h
    · have np : ¬ p k = true := by rw [hp, h]; simp
      simp only [np, ite_false]
      refine ⟨ih1, fun e i hi xi => ?_⟩
      by_cases hlt : i < m + k
      · exact ih2 e i hlt xi
      · have : i = m + k := by omega
        subst this
        rw [ey, h]; rw [ex, h] at xi
        simp only [GateOp.eval, List.all_eq_true, List.mem_map, forall_exists_index, and_imp,
          id] at xi ⊢
        intro z a ha ez
        subst ez
        exact ih2 e a (r a ha) (xi _ a ha rfl)
    · have np : ¬ p k = true := by rw [hp, h]; simp
      simp only [np, ite_false]
      refine ⟨ih1, fun e i hi xi => ?_⟩
      by_cases hlt : i < m + k
      · exact ih2 e i hlt xi
      · have : i = m + k := by omega
        subst this
        rw [ey, h]; rw [ex, h] at xi
        simp only [GateOp.eval, List.any_eq_true, List.mem_map, id] at xi ⊢
        obtain ⟨z, ⟨a, ha, rfl⟩, yes⟩ := xi
        exact ⟨_, ⟨a, ha, rfl⟩, ih2 e a (r a ha) yes⟩
    · have np : p k = true := by rw [hp, h]
      simp only [np, ite_true]
      have bx01 : bx k ≤ 1 := by
        cases hh : X.getD (m+k) false
        · rw [hx0 k hh]; omega
        · rw [hx1 k hh]
      have by01 : bY k ≤ 1 := by
        cases hh : Y.getD (m+k) false
        · rw [hy0 k hh]; omega
        · rw [hy1 k hh]
      by_cases e : sgF p bY k = sgF p bx k
      · have ord := ih2 e
        have anti : Y.getD (m+k) false = true → X.getD (m+k) false = true := by
          rw [ey, ex, h]
          cases inp : (gs.getD k dg).inputs with
          | nil => simp [GateOp.eval]
          | cons a more =>
            have ha : a < m + k := r a (by rw [inp]; simp)
            simp only [GateOp.eval, List.map_cons, List.headD_cons, Bool.not_eq_true']
            intro yz
            cases xz : X.getD a false
            · rfl
            · have := ord a ha xz
              simp_all
        have le : bY k ≤ bx k := by
          cases hh : Y.getD (m+k) false
          · rw [hy0 k hh]; omega
          · rw [hy1 k hh, hx1 k (anti hh)]
        refine ⟨by omega, fun e2 i hi xi => ?_⟩
        by_cases hlt : i < m + k
        · exact ord i hlt xi
        · have : i = m + k := by omega
          subst this
          have b1 := hx1 k xi
          cases hh : Y.getD (m+k) false
          · have := hy0 k hh; omega
          · rfl
      · refine ⟨by omega, fun e2 => ?_⟩
        omega

theorem main_mono (n : Nat) (C : Circuit) (fan : PEqualNP.MetaComplexity.FanInTwo C)
    (rb : PEqualNP.MetaComplexity.NestedCover.ReadsBack (n+2) C)
    (a b : Fin n → Bool) (hab : ∀ j, a j = true → b j = true)
    (p : Nat → Bool) (hp : ∀ i, p i = true ↔ (C.gates.getD i dg).op = GateOp.not)
    (bx bY : Nat → Nat)
    (hx1 : ∀ i, (C.wires (List.ofFn a ++ [false,true])).getD (n+2+i) false = true → bx i = 1)
    (hx0 : ∀ i, (C.wires (List.ofFn a ++ [false,true])).getD (n+2+i) false = false → bx i = 0)
    (hy1 : ∀ i, (C.wires (List.ofFn b ++ [false,true])).getD (n+2+i) false = true → bY i = 1)
    (hy0 : ∀ i, (C.wires (List.ofFn b ++ [false,true])).getD (n+2+i) false = false → bY i = 0) :
    sgF p bY C.gates.length ≤ sgF p bx C.gates.length ∧
      (sgF p bY C.gates.length = sgF p bx C.gates.length → ∀ i < n + 2 + C.gates.length,
        (C.wires (List.ofFn a ++ [false,true])).getD i false = true →
        (C.wires (List.ofFn b ++ [false,true])).getD i false = true) := by
  have la : (List.ofFn a ++ [false,true]).length = n+2 := by simp
  have lb : (List.ofFn b ++ [false,true]).length = n+2 := by simp
  refine key C.gates (fun g hg => by simpa using (fan g hg).1) (n+2) (run C.gates _)
    (run C.gates _) p hp bx bY hx1 hx0 hy1 hy0 ?_ ?_ rb ?_ C.gates.length le_rfl
  · intro k hk
    have := run_eq C.gates (List.ofFn a ++ [false,true]) k hk (by rw [la]; exact rb k hk)
    rw [la] at this
    exact this
  · intro k hk
    have := run_eq C.gates (List.ofFn b ++ [false,true]) k hk (by rw [lb]; exact rb k hk)
    rw [lb] at this
    exact this
  · intro i hi hx
    rw [run_low _ _ _ (by rw [lb]; exact hi)]
    rw [run_low _ _ _ (by rw [la]; exact hi)] at hx
    exact raw_ord n a b hab i hx

end PEqualNP.Outside.L_lib_1279

theorem PEqualNP.Outside.L_lib_1279 : (letI : ∀ P : Prop, Decidable P := Classical.propDecidable
∀ (n : Nat) (C : PEqualNP.CircuitLowerBounds.Circuit),
  PEqualNP.MetaComplexity.FanInTwo C → PEqualNP.MetaComplexity.NestedCover.ReadsBack (n+2) C →
  let gates := (List.range C.size).filter (fun i =>
    decide ((C.gates.getD i ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩).op =
      PEqualNP.CircuitLowerBounds.GateOp.not))
  let wire := fun (x : Finset (Fin n)) (i : Nat) =>
    (C.wires (List.ofFn (fun j : Fin n => decide (j ∈ x)) ++ [false,true])).getD i false
  let sig := fun x => gates.foldl (fun s i => 2*s + (if wire x (n+2+i) then 1 else 0)) 0
  let drop := fun x y => ∃ i, i < n+2+C.size ∧ wire x i = true ∧ wire y i = false
  let before := Nat.rec (motive := fun _ => Finset (Fin n) → Prop) (fun _ => True)
    (fun _ prev x => ∃ u v, prev u ∧ u ⊆ v ∧ v ⊆ x ∧ drop u v)
  let after := Nat.rec (motive := fun _ => Finset (Fin n) → Prop) (fun _ => True)
    (fun _ prev x => ∃ u v, x ⊆ u ∧ u ⊆ v ∧ drop u v ∧ prev v)
  (∀ x y, x ⊆ y → sig y ≤ sig x ∧ (drop x y → sig y < sig x)) ∧
  ∀ x i j, before i x → after j x →
    j ≤ sig x ∧ sig x + i < 2^(PEqualNP.NotBracket.notCount C) ∧
    (i+j+1 = 2^(PEqualNP.NotBracket.notCount C) → sig x = j)) := by
  intro n C fan rb gates wire sig drop before after
  have hmono : ∀ x y, x ⊆ y → sig y ≤ sig x ∧ (drop x y → sig y < sig x) := by
    intro x y xy
    have K := L_lib_1279.main_mono n C fan rb
      (fun j => @decide (j ∈ x) (Classical.propDecidable _))
      (fun j => @decide (j ∈ y) (Classical.propDecidable _))
      (fun j h => by simp only [decide_eq_true_eq] at h ⊢; exact xy h)
      (fun i => @decide ((C.gates.getD i ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩).op =
        PEqualNP.CircuitLowerBounds.GateOp.not) (Classical.propDecidable _))
      (by intro i; simp [L_lib_1279.dg])
      (fun i => @ite _ (wire x (n+2+i) = true) (Classical.propDecidable _) 1 0)
      (fun i => @ite _ (wire y (n+2+i) = true) (Classical.propDecidable _) 1 0)
      (fun i h => if_pos h)
      (fun i h => if_neg (fun t => Bool.noConfusion (h.symm.trans t)))
      (fun i h => if_pos h)
      (fun i h => if_neg (fun t => Bool.noConfusion (h.symm.trans t)))
    refine ⟨K.1, fun d => ?_⟩
    obtain ⟨i, hi, xi, yi⟩ := d
    by_contra hn
    have e : sig y = sig x := le_antisymm K.1 (not_lt.mp hn)
    have := K.2 e i hi xi
    exact Bool.noConfusion (this.symm.trans yi)
  have hbound : ∀ x, sig x < 2^(PEqualNP.NotBracket.notCount C) := by
    intro x
    have hp : ∀ i, (@decide ((C.gates.getD i ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩).op =
        PEqualNP.CircuitLowerBounds.GateOp.not) (Classical.propDecidable _)) = true ↔
        (C.gates.getD i L_lib_1279.dg).op = PEqualNP.CircuitLowerBounds.GateOp.not := by
      intro i; simp [L_lib_1279.dg]
    have e : ((List.range C.gates.length).filter (fun i =>
        @decide ((C.gates.getD i ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩).op =
        PEqualNP.CircuitLowerBounds.GateOp.not) (Classical.propDecidable _))).length =
        PEqualNP.NotBracket.notCount C := by
      unfold PEqualNP.NotBracket.notCount
      exact L_lib_1279.cnt C.gates _ _ hp (fun g => by simp)
    have L := L_lib_1279.sgF_lt (fun i =>
        @decide ((C.gates.getD i ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩).op =
        PEqualNP.CircuitLowerBounds.GateOp.not) (Classical.propDecidable _))
      (fun i => @ite _ (wire x (n+2+i) = true) (Classical.propDecidable _) 1 0) (fun i => by split <;> omega)
      C.gates.length
    rw [e] at L
    exact L
  have hb : ∀ i x, before i x → sig x + i < 2^(PEqualNP.NotBracket.notCount C) := by
    intro i
    induction i with
    | zero => intro x _; exact hbound x
    | succ i ih =>
      intro x hx
      obtain ⟨u, v, hu, uv, vx, d⟩ := hx
      have h1 := ih u hu
      have h2 := (hmono u v uv).2 d
      have h3 := (hmono v x vx).1
      omega
  have ha : ∀ j x, after j x → j ≤ sig x := by
    intro j
    induction j with
    | zero => intro x _; exact Nat.zero_le _
    | succ j ih =>
      intro x hx
      obtain ⟨u, v, xu, uv, d, hv⟩ := hx
      have h1 := ih v hv
      have h2 := (hmono u v uv).2 d
      have h3 := (hmono x u xu).1
      omega
  refine ⟨hmono, fun x i j bi aj => ?_⟩
  have h1 := hb i x bi
  have h2 := ha j x aj
  refine ⟨h2, h1, fun e => ?_⟩
  omega
