import Mathlib.Data.Finset.Interval
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_27335_aux

open PEqualNP.CircuitLowerBounds

def stepWire (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma foldl_stepWire_len (gs : List Gate) (w : List Bool) :
    (gs.foldl stepWire w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons, ih, stepWire, List.length_append, List.length_cons, List.length_nil]
    omega

lemma foldl_stepWire_prefix (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl stepWire w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hlt : i < (stepWire w g).length := by
      simp only [stepWire, List.length_append, List.length_cons, List.length_nil]
      omega
    rw [ih (stepWire w g) hlt]
    simp only [stepWire, List.getD_eq_getElem _ _ hi,
      List.getD_eq_getElem _ _ (by simp; omega : i < (w ++ [_]).length),
      List.getElem_append_left hi]

lemma wire_getD_input (C : Circuit) (x : Fin 9 → Bool) (i : Fin 9) :
    (C.wires (List.ofFn x)).getD i.val false = x i := by
  unfold Circuit.wires
  change (C.gates.foldl stepWire (List.ofFn x)).getD i.val false = x i
  have hi : i.val < (List.ofFn x).length := by simp
  rw [foldl_stepWire_prefix C.gates (List.ofFn x) i.val hi, List.getD_eq_getElem _ _ hi,
    List.getElem_ofFn]

lemma wire_getD_gate (C : Circuit) (x : Fin 9 → Bool) (j : ℕ) (hj : j < C.gates.length) :
    (C.wires (List.ofFn x)).getD (9 + j) false =
      (C.gates[j]'hj).op.eval
        ((C.gates[j]'hj).inputs.map fun i =>
          ((C.gates.take j).foldl stepWire (List.ofFn x)).getD i false) := by
  unfold Circuit.wires
  change (C.gates.foldl stepWire (List.ofFn x)).getD (9 + j) false = _
  have hsplit : C.gates = C.gates.take j ++ (C.gates[j]'hj) :: C.gates.drop (j + 1) := by
    have h1 : C.gates.take j ++ C.gates.drop j = C.gates := List.take_append_drop j C.gates
    have h2 : C.gates.drop j = (C.gates[j]'hj) :: C.gates.drop (j + 1) := List.drop_eq_getElem_cons hj
    rw [← h2, h1]
  conv_lhs => rw [hsplit]
  rw [List.foldl_append, List.foldl_cons]
  set pref := (C.gates.take j).foldl stepWire (List.ofFn x)
  have hlen : pref.length = 9 + j := by
    rw [foldl_stepWire_len, List.length_ofFn, List.length_take]
    omega
  have hlt : 9 + j < (stepWire pref (C.gates[j]'hj)).length := by
    simp only [stepWire, List.length_append, List.length_cons, List.length_nil, hlen]
    omega
  rw [foldl_stepWire_prefix (C.gates.drop (j + 1)) (stepWire pref (C.gates[j]'hj)) (9 + j) hlt]
  dsimp only [stepWire]
  have hlt' : 9 + j < (pref ++ [(C.gates[j]'hj).op.eval ((C.gates[j]'hj).inputs.map fun i => pref.getD i false)]).length := by
    simp only [List.length_append, List.length_cons, List.length_nil, hlen]
    omega
  rw [List.getD_eq_getElem _ _ hlt', List.getElem_append_right (by omega : pref.length ≤ 9 + j)]
  simp only [hlen, Nat.sub_self, List.getElem_cons_zero]

lemma wire_getD_gate_full (C : Circuit) (x : Fin 9 → Bool) (j : ℕ) (hj : j < C.gates.length)
    (hback : ∀ i ∈ (C.gates[j]'hj).inputs, i < 9 + j) :
    (C.wires (List.ofFn x)).getD (9 + j) false =
      (C.gates[j]'hj).op.eval
        ((C.gates[j]'hj).inputs.map fun i => (C.wires (List.ofFn x)).getD i false) := by
  rw [wire_getD_gate C x j hj]
  congr 1
  refine List.map_congr_left ?_
  intro i hi
  have hlt : i < 9 + j := hback i hi
  unfold Circuit.wires
  change ((C.gates.take j).foldl stepWire (List.ofFn x)).getD i false =
    (C.gates.foldl stepWire (List.ofFn x)).getD i false
  have hsplit : C.gates = C.gates.take j ++ C.gates.drop j := (List.take_append_drop j C.gates).symm
  conv_rhs => rw [hsplit]
  rw [List.foldl_append]
  have hlen : ((C.gates.take j).foldl stepWire (List.ofFn x)).length = 9 + j := by
    rw [foldl_stepWire_len, List.length_ofFn, List.length_take]
    omega
  rw [foldl_stepWire_prefix (C.gates.drop j) _ i (by omega)]

def pm3 (x : Fin 9 → Bool) : Bool :=
  (x 0 && x 4 && x 8) || (x 0 && x 5 && x 7) || (x 1 && x 3 && x 8) ||
  (x 1 && x 5 && x 6) || (x 2 && x 3 && x 7) || (x 2 && x 4 && x 6)

def mkIn (b0 b1 b2 b3 b4 b5 b6 b7 b8 : Bool) : Fin 9 → Bool
  | ⟨0, _⟩ => b0
  | ⟨1, _⟩ => b1
  | ⟨2, _⟩ => b2
  | ⟨3, _⟩ => b3
  | ⟨4, _⟩ => b4
  | ⟨5, _⟩ => b5
  | ⟨6, _⟩ => b6
  | ⟨7, _⟩ => b7
  | ⟨8, _⟩ => b8

def witX (v : Fin 9) : Fin 9 → Bool :=
  match v with
  | ⟨0, _⟩ => mkIn false false false false false true false true false
  | ⟨1, _⟩ => mkIn false false false true false false false false true
  | ⟨2, _⟩ => mkIn true false false true true false false true false
  | ⟨3, _⟩ => mkIn false false true false false false false true false
  | ⟨4, _⟩ => mkIn false false true false false false true false false
  | ⟨5, _⟩ => mkIn true false false false false false false true false
  | ⟨6, _⟩ => mkIn false true false false false true false false false
  | ⟨7, _⟩ => mkIn true false false false false true false false false
  | ⟨8, _⟩ => mkIn true false false false true false false false false

def witY (v : Fin 9) : Fin 9 → Bool :=
  fun i => if i = v then true else witX v i

lemma wit_props (v : Fin 9) :
    (∀ i : Fin 9, i ≠ v → witX v i = witY v i) ∧
    (witX v 0 && witX v 4) = (witY v 0 && witY v 4) ∧
    (witX v 2 || (witX v 0 && witX v 4)) = (witY v 2 || (witY v 0 && witY v 4)) ∧
    pm3 (witX v) ≠ pm3 (witY v) := by
  have hall : ∀ v : Fin 9,
      (∀ i : Fin 9, i ≠ v → witX v i = witY v i) ∧
      (witX v 0 && witX v 4) = (witY v 0 && witY v 4) ∧
      (witX v 2 || (witX v 0 && witX v 4)) = (witY v 2 || (witY v 0 && witY v 4)) ∧
      pm3 (witX v) ≠ pm3 (witY v) := by
    decide
  exact hall v

lemma agree_of_unused (C : Circuit)
    (hback : ∀ (j : ℕ) (hj : j < C.gates.length), ∀ i ∈ (C.gates[j]'hj).inputs, i < 9 + j)
    (hge2 : 2 ≤ C.gates.length)
    (v : Fin 9)
    (hunused : ∀ (j : ℕ) (hj : j < C.gates.length), 2 ≤ j → v.val ∉ (C.gates[j]'hj).inputs)
    (x y : Fin 9 → Bool)
    (hxy_in : ∀ i : Fin 9, i ≠ v → x i = y i)
    (h9 : (C.wires (List.ofFn x)).getD 9 false = (C.wires (List.ofFn y)).getD 9 false)
    (h10 : (C.wires (List.ofFn x)).getD 10 false = (C.wires (List.ofFn y)).getD 10 false) :
    ∀ w : ℕ, w < 9 + C.gates.length → w ≠ v.val →
      (C.wires (List.ofFn x)).getD w false = (C.wires (List.ofFn y)).getD w false := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hw hne
    by_cases h9lt : w < 9
    · have hfx := wire_getD_input C x ⟨w, h9lt⟩
      have hfy := wire_getD_input C y ⟨w, h9lt⟩
      rw [hfx, hfy]
      exact hxy_in ⟨w, h9lt⟩ (fun h => hne (congrArg Fin.val h))
    · by_cases hw9 : w = 9
      · subst hw9; exact h9
      · by_cases hw10 : w = 10
        · subst hw10; exact h10
        · have hj2 : 2 ≤ w - 9 := by omega
          have hjlt : w - 9 < C.gates.length := by omega
          have hw_eq : 9 + (w - 9) = w := by omega
          rw [← hw_eq, wire_getD_gate_full C x (w - 9) hjlt (hback (w - 9) hjlt),
            wire_getD_gate_full C y (w - 9) hjlt (hback (w - 9) hjlt)]
          congr 1
          refine List.map_congr_left ?_
          intro u hu
          have hult : u < 9 + (w - 9) := hback (w - 9) hjlt u hu
          have hune : u ≠ v.val := fun h => hunused (w - 9) hjlt hj2 (h ▸ hu)
          exact ih u (by omega) (by omega) hune

inductive IsRO : Finset (Fin 4) → ((Fin 4 → Bool) → Bool) → Prop
  | const (b : Bool) : IsRO ∅ (fun _ => b)
  | var (i : Fin 4) : IsRO {i} (fun y => y i)
  | and {s t : Finset (Fin 4)} {f g : (Fin 4 → Bool) → Bool} :
      Disjoint s t → IsRO s f → IsRO t g → IsRO (s ∪ t) (fun y => f y && g y)
  | or {s t : Finset (Fin 4)} {f g : (Fin 4 → Bool) → Bool} :
      Disjoint s t → IsRO s f → IsRO t g → IsRO (s ∪ t) (fun y => f y || g y)

lemma IsRO.mono {s : Finset (Fin 4)} {f : (Fin 4 → Bool) → Bool} (h : IsRO s f) :
    ∀ x y : Fin 4 → Bool, (∀ i : Fin 4, x i = true → y i = true) → f x = true → f y = true := by
  induction h with
  | const b => intro _ _ _ hx; exact hx
  | var i => intro x y hxy hx; exact hxy i hx
  | and _ _ _ ihf ihg =>
    intro x y hxy hx
    simp only [Bool.and_eq_true] at hx ⊢
    exact ⟨ihf x y hxy hx.1, ihg x y hxy hx.2⟩
  | or _ _ _ ihf ihg =>
    intro x y hxy hx
    simp only [Bool.or_eq_true] at hx ⊢
    exact hx.elim (fun h1 => Or.inl (ihf x y hxy h1)) (fun h2 => Or.inr (ihg x y hxy h2))

lemma IsRO.indep {s : Finset (Fin 4)} {f : (Fin 4 → Bool) → Bool} (h : IsRO s f) :
    ∀ x y : Fin 4 → Bool, (∀ i ∈ s, x i = y i) → f x = f y := by
  induction h with
  | const b => intro _ _ _; rfl
  | var i =>
    intro x y hxy
    exact hxy i (Finset.mem_singleton_self i)
  | and _ _ _ ihf ihg =>
    intro x y hxy
    dsimp only
    rw [ihf x y (fun i hi => hxy i (Finset.mem_union_left _ hi)),
      ihg x y (fun i hi => hxy i (Finset.mem_union_right _ hi))]
  | or _ _ _ ihf ihg =>
    intro x y hxy
    dsimp only
    rw [ihf x y (fun i hi => hxy i (Finset.mem_union_left _ hi)),
      ihg x y (fun i hi => hxy i (Finset.mem_union_right _ hi))]

def p4 (y : Fin 4 → Bool) : Bool :=
  (y 0 && y 1) || (y 1 && y 2) || (y 2 && y 3)

def ind4 (s : Finset (Fin 4)) : Fin 4 → Bool :=
  fun i => decide (i ∈ s)

lemma p4_false_0 : p4 (ind4 ∅) = false := by decide
lemma p4_true_01 : p4 (ind4 {0, 1}) = true := by decide
lemma p4_true_12 : p4 (ind4 {1, 2}) = true := by decide
lemma p4_true_23 : p4 (ind4 {2, 3}) = true := by decide
lemma p4_false_03 : p4 (ind4 {0, 3}) = false := by decide
lemma p4_false_1 : p4 (ind4 {1}) = false := by decide
lemma p4_false_2 : p4 (ind4 {2}) = false := by decide

lemma IsRO.not_p4 {s : Finset (Fin 4)} {f : (Fin 4 → Bool) → Bool} (h : IsRO s f) :
    f ≠ p4 := by
  induction h with
  | const b =>
    intro heq
    have h0 := congrFun heq (ind4 ∅)
    have h1 := congrFun heq (ind4 {0, 1})
    rw [p4_false_0] at h0
    rw [p4_true_01] at h1
    cases b <;> simp at h0 h1
  | var i =>
    intro heq
    fin_cases i
    · have h := congrFun heq (ind4 {1, 2}); simp [ind4, p4] at h
    · have h := congrFun heq (ind4 {1}); simp [ind4, p4] at h
    · have h := congrFun heq (ind4 {2}); simp [ind4, p4] at h
    · have h := congrFun heq (ind4 {0, 1}); simp [ind4, p4] at h
  | @and s1 s2 f g hdisj hf hg ihf ihg =>
    intro heq
    by_cases hf1 : f (ind4 ∅) = true
    · have hft : ∀ y, f y = true := fun y =>
        hf.mono (ind4 ∅) y (fun i hi => by simp [ind4] at hi) hf1
      apply ihg
      funext y
      have hy := congrFun heq y
      simp only [hft y, Bool.true_and] at hy
      exact hy
    · by_cases hg1 : g (ind4 ∅) = true
      · have hgt : ∀ y, g y = true := fun y =>
          hg.mono (ind4 ∅) y (fun i hi => by simp [ind4] at hi) hg1
        apply ihf
        funext y
        have hy := congrFun heq y
        simp only [hgt y, Bool.and_true] at hy
        exact hy
      · have hf0 : f (ind4 ∅) = false := Bool.eq_false_iff.mpr hf1
        have hg0 : g (ind4 ∅) = false := Bool.eq_false_iff.mpr hg1
        have hhit : ∀ a b : Fin 4, p4 (ind4 {a, b}) = true →
            (a ∈ s1 ∧ b ∈ s2) ∨ (a ∈ s2 ∧ b ∈ s1) := by
          intro a b hab
          have hfg := congrFun heq (ind4 {a, b})
          rw [hab, Bool.and_eq_true] at hfg
          have ha1 : a ∈ s1 ∨ b ∈ s1 := by
            by_contra hno
            push Not at hno
            have heq0 : f (ind4 {a, b}) = f (ind4 ∅) := hf.indep _ _ fun i hi => by
              simp only [ind4, Finset.notMem_empty, decide_false, decide_eq_false_iff_not,
                Finset.mem_insert, Finset.mem_singleton, not_or]
              exact ⟨fun h => hno.1 (h ▸ hi), fun h => hno.2 (h ▸ hi)⟩
            rw [heq0, hf0] at hfg
            exact Bool.false_ne_true hfg.1
          have ha2 : a ∈ s2 ∨ b ∈ s2 := by
            by_contra hno
            push Not at hno
            have heq0 : g (ind4 {a, b}) = g (ind4 ∅) := hg.indep _ _ fun i hi => by
              simp only [ind4, Finset.notMem_empty, decide_false, decide_eq_false_iff_not,
                Finset.mem_insert, Finset.mem_singleton, not_or]
              exact ⟨fun h => hno.1 (h ▸ hi), fun h => hno.2 (h ▸ hi)⟩
            rw [heq0, hg0] at hfg
            exact Bool.false_ne_true hfg.2
          rcases ha1 with h1 | h1 <;> rcases ha2 with h2 | h2
          · exact False.elim (Finset.disjoint_left.mp hdisj h1 h2)
          · exact Or.inl ⟨h1, h2⟩
          · exact Or.inr ⟨h2, h1⟩
          · exact False.elim (Finset.disjoint_left.mp hdisj h1 h2)
        have h01 := hhit 0 1 p4_true_01
        have h12 := hhit 1 2 p4_true_12
        have h23 := hhit 2 3 p4_true_23
        have hfg01 := congrFun heq (ind4 {0, 1})
        rw [p4_true_01, Bool.and_eq_true] at hfg01
        have hfg23 := congrFun heq (ind4 {2, 3})
        rw [p4_true_23, Bool.and_eq_true] at hfg23
        have hfg03 := congrFun heq (ind4 {0, 3})
        rw [p4_false_03] at hfg03
        rcases h01 with ⟨h0s1, h1s2⟩ | ⟨h0s2, h1s1⟩
        · have h2s1 : (2 : Fin 4) ∈ s1 := by
            rcases h12 with ⟨h1s1, _⟩ | ⟨_, h2s1⟩
            · exact False.elim (Finset.disjoint_left.mp hdisj h1s1 h1s2)
            · exact h2s1
          have h3s2 : (3 : Fin 4) ∈ s2 := by
            rcases h23 with ⟨_, h3s2⟩ | ⟨h2s2, _⟩
            · exact h3s2
            · exact False.elim (Finset.disjoint_left.mp hdisj h2s1 h2s2)
          have hf03 : f (ind4 {0, 3}) = f (ind4 {0, 1}) := hf.indep _ _ fun i hi => by
            have hne1 : i ≠ 1 := fun h => Finset.disjoint_left.mp hdisj (h ▸ hi) h1s2
            have hne3 : i ≠ 3 := fun h => Finset.disjoint_left.mp hdisj (h ▸ hi) h3s2
            simp [ind4, hne1, hne3]
          have hg03 : g (ind4 {0, 3}) = g (ind4 {2, 3}) := hg.indep _ _ fun i hi => by
            have hne0 : i ≠ 0 := fun h => Finset.disjoint_left.mp hdisj h0s1 (h ▸ hi)
            have hne2 : i ≠ 2 := fun h => Finset.disjoint_left.mp hdisj h2s1 (h ▸ hi)
            simp [ind4, hne0, hne2]
          rw [hf03, hg03, hfg01.1, hfg23.2] at hfg03
          exact Bool.noConfusion hfg03
        · have h2s2 : (2 : Fin 4) ∈ s2 := by
            rcases h12 with ⟨_, h2s2⟩ | ⟨h1s2, _⟩
            · exact h2s2
            · exact False.elim (Finset.disjoint_left.mp hdisj h1s1 h1s2)
          have h3s1 : (3 : Fin 4) ∈ s1 := by
            rcases h23 with ⟨h2s1, _⟩ | ⟨_, h3s1⟩
            · exact False.elim (Finset.disjoint_left.mp hdisj h2s1 h2s2)
            · exact h3s1
          have hf03 : f (ind4 {0, 3}) = f (ind4 {2, 3}) := hf.indep _ _ fun i hi => by
            have hne0 : i ≠ 0 := fun h => Finset.disjoint_left.mp hdisj (h ▸ hi) h0s2
            have hne2 : i ≠ 2 := fun h => Finset.disjoint_left.mp hdisj (h ▸ hi) h2s2
            simp [ind4, hne0, hne2]
          have hg03 : g (ind4 {0, 3}) = g (ind4 {0, 1}) := hg.indep _ _ fun i hi => by
            have hne1 : i ≠ 1 := fun h => Finset.disjoint_left.mp hdisj h1s1 (h ▸ hi)
            have hne3 : i ≠ 3 := fun h => Finset.disjoint_left.mp hdisj h3s1 (h ▸ hi)
            simp [ind4, hne1, hne3]
          rw [hf03, hg03, hfg23.1, hfg01.2] at hfg03
          exact Bool.noConfusion hfg03
  | @or s1 s2 f g hdisj hf hg ihf ihg =>
    intro heq
    by_cases hf0 : f (ind4 s1) = false
    · have hff : ∀ y, f y = false := by
        intro y
        by_contra htr
        have h1 : f y = true := Bool.eq_true_of_not_eq_false htr
        have h2 : f (ind4 s1) = true := by
          have hs : f (ind4 s1) = f (fun i => if i ∈ s1 then true else y i) :=
            hf.indep _ _ fun i hi => by simp [ind4, hi]
          rw [hs]
          exact hf.mono y _ (fun i hy => by by_cases hi : i ∈ s1 <;> simp [hi, hy]) h1
        rw [hf0] at h2
        exact Bool.false_ne_true h2
      apply ihg
      funext y
      have hy := congrFun heq y
      simp only [hff y, Bool.false_or] at hy
      exact hy
    · by_cases hg0 : g (ind4 s2) = false
      · have hgf : ∀ y, g y = false := by
          intro y
          by_contra htr
          have h1 : g y = true := Bool.eq_true_of_not_eq_false htr
          have h2 : g (ind4 s2) = true := by
            have hs : g (ind4 s2) = g (fun i => if i ∈ s2 then true else y i) :=
              hg.indep _ _ fun i hi => by simp [ind4, hi]
            rw [hs]
            exact hg.mono y _ (fun i hy => by by_cases hi : i ∈ s2 <;> simp [hi, hy]) h1
          rw [hg0] at h2
          exact Bool.false_ne_true h2
        apply ihf
        funext y
        have hy := congrFun heq y
        simp only [hgf y, Bool.or_false] at hy
        exact hy
      · have hf1 : f (ind4 s1) = true := Bool.eq_true_of_not_eq_false hf0
        have hg1 : g (ind4 s2) = true := Bool.eq_true_of_not_eq_false hg0
        have hp1 : p4 (ind4 s1) = true := by
          have h := congrFun heq (ind4 s1)
          rw [hf1, Bool.true_or] at h
          exact h.symm
        have hp2 : p4 (ind4 s2) = true := by
          have h := congrFun heq (ind4 s2)
          rw [hg1, Bool.or_true] at h
          exact h.symm
        have hedge : ∀ s : Finset (Fin 4), p4 (ind4 s) = true →
            ((0 : Fin 4) ∈ s ∧ (1 : Fin 4) ∈ s) ∨
            ((1 : Fin 4) ∈ s ∧ (2 : Fin 4) ∈ s) ∨
            ((2 : Fin 4) ∈ s ∧ (3 : Fin 4) ∈ s) := by
          intro s hs
          simp only [p4, ind4, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hs
          rcases hs with (h01 | h12) | h23
          · exact Or.inl h01
          · exact Or.inr (Or.inl h12)
          · exact Or.inr (Or.inr h23)
        have he1 := hedge s1 hp1
        have he2 := hedge s2 hp2
        have hsplit : ((0 : Fin 4) ∈ s1 ∧ (1 : Fin 4) ∈ s1 ∧ (2 : Fin 4) ∈ s2 ∧ (3 : Fin 4) ∈ s2) ∨
            ((0 : Fin 4) ∈ s2 ∧ (1 : Fin 4) ∈ s2 ∧ (2 : Fin 4) ∈ s1 ∧ (3 : Fin 4) ∈ s1) := by
          rcases he1 with ⟨h0, h1⟩ | ⟨h1, h2⟩ | ⟨h2, h3⟩ <;>
            rcases he2 with ⟨k0, k1⟩ | ⟨k1, k2⟩ | ⟨k2, k3⟩
          · exact False.elim (Finset.disjoint_left.mp hdisj h0 k0)
          · exact False.elim (Finset.disjoint_left.mp hdisj h1 k1)
          · exact Or.inl ⟨h0, h1, k2, k3⟩
          · exact False.elim (Finset.disjoint_left.mp hdisj h1 k1)
          · exact False.elim (Finset.disjoint_left.mp hdisj h1 k1)
          · exact False.elim (Finset.disjoint_left.mp hdisj h2 k2)
          · exact Or.inr ⟨k0, k1, h2, h3⟩
          · exact False.elim (Finset.disjoint_left.mp hdisj h2 k2)
          · exact False.elim (Finset.disjoint_left.mp hdisj h2 k2)
        have h12 := congrFun heq (ind4 {1, 2})
        rw [p4_true_12, Bool.or_eq_true] at h12
        rcases hsplit with ⟨_, h1s1, h2s2, _⟩ | ⟨_, h1s2, h2s1, _⟩
        · rcases h12 with hf12 | hg12
          · have hfeq : f (ind4 {1}) = f (ind4 {1, 2}) := hf.indep _ _ fun i hi => by
              have hne2 : i ≠ 2 := fun h => Finset.disjoint_left.mp hdisj (h ▸ hi) h2s2
              simp [ind4, hne2]
            have hp := congrFun heq (ind4 {1})
            rw [hfeq, hf12, Bool.true_or, p4_false_1] at hp
            exact Bool.noConfusion hp
          · have hgeq : g (ind4 {2}) = g (ind4 {1, 2}) := hg.indep _ _ fun i hi => by
              have hne1 : i ≠ 1 := fun h => Finset.disjoint_left.mp hdisj h1s1 (h ▸ hi)
              simp [ind4, hne1]
            have hp := congrFun heq (ind4 {2})
            rw [hgeq, hg12, Bool.or_true, p4_false_2] at hp
            exact Bool.noConfusion hp
        · rcases h12 with hf12 | hg12
          · have hfeq : f (ind4 {2}) = f (ind4 {1, 2}) := hf.indep _ _ fun i hi => by
              have hne1 : i ≠ 1 := fun h => Finset.disjoint_left.mp hdisj (h ▸ hi) h1s2
              simp [ind4, hne1]
            have hp := congrFun heq (ind4 {2})
            rw [hfeq, hf12, Bool.true_or, p4_false_2] at hp
            exact Bool.noConfusion hp
          · have hgeq : g (ind4 {1}) = g (ind4 {1, 2}) := hg.indep _ _ fun i hi => by
              have hne2 : i ≠ 2 := fun h => Finset.disjoint_left.mp hdisj h2s1 (h ▸ hi)
              simp [ind4, hne2]
            have hp := congrFun heq (ind4 {1})
            rw [hgeq, hg12, Bool.or_true, p4_false_1] at hp
            exact Bool.noConfusion hp

def assign4 (y : Fin 4 → Bool) : Fin 9 → Bool :=
  mkIn true true true (y 0) false (y 2) (y 3) (y 1) false

lemma pm3_assign4 (y : Fin 4 → Bool) : pm3 (assign4 y) = p4 y := by
  simp only [pm3, assign4, mkIn, p4]
  cases y 0 <;> cases y 1 <;> cases y 2 <;> cases y 3 <;> rfl

lemma list_flatMap_length_le_two (gs : List Gate) (h : ∀ g ∈ gs, g.inputs.length ≤ 2) :
    (gs.flatMap Gate.inputs).length ≤ 2 * gs.length := by
  induction gs with
  | nil => simp
  | cons g gs ih =>
    simp only [List.flatMap_cons, List.length_append, List.length_cons]
    have h1 : g.inputs.length ≤ 2 := h g List.mem_cons_self
    have h2 : (gs.flatMap Gate.inputs).length ≤ 2 * gs.length :=
      ih (fun g' hg' => h g' (List.mem_cons_of_mem g hg'))
    omega

lemma list_flatMap_length_lt_of_len1 (gs : List Gate) (h : ∀ g ∈ gs, g.inputs.length ≤ 2)
    (g0 : Gate) (hg0 : g0 ∈ gs) (hlen1 : g0.inputs.length = 1) :
    (gs.flatMap Gate.inputs).length < 2 * gs.length := by
  induction gs with
  | nil => simp at hg0
  | cons g gs ih =>
    simp only [List.flatMap_cons, List.length_append, List.length_cons]
    rcases List.mem_cons.mp hg0 with rfl | hmem
    · have h2 := list_flatMap_length_le_two gs (fun g' hg' => h g' (List.mem_cons_of_mem g0 hg'))
      omega
    · have h1 : g.inputs.length ≤ 2 := h g List.mem_cons_self
      have h2 := ih (fun g' hg' => h g' (List.mem_cons_of_mem g hg')) hmem
      omega

def deps0 (w : ℕ) : Finset (Fin 4) :=
  match w with
  | 3 => {0}
  | 7 => {1}
  | 5 => {2}
  | 6 => {3}
  | _ => ∅

lemma mem_deps0 {w : ℕ} {x : Fin 4} (h : x ∈ deps0 w) :
    (x = 0 ∧ w = 3) ∨ (x = 1 ∧ w = 7) ∨ (x = 2 ∧ w = 5) ∨ (x = 3 ∧ w = 6) := by
  unfold deps0 at h
  split at h <;> simp_all

lemma deps0_disjoint (u v : ℕ) (huv : u ≠ v) : Disjoint (deps0 u) (deps0 v) := by
  rw [Finset.disjoint_left]
  intro x hx1 hx2
  rcases mem_deps0 hx1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    rcases mem_deps0 hx2 with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
    first | exact huv h2.symm | exact absurd h1 (by decide)

lemma mem_drop_of_ge {α : Type*} (l : List α) (d j : ℕ) (hj : j < l.length) (hd : d ≤ j) :
    l[j]'hj ∈ l.drop d := by
  have hj' : j - d < (l.drop d).length := by rw [List.length_drop]; omega
  have hidx : d + (j - d) = j := by omega
  have h : (l.drop d)[j - d]'hj' = l[j]'hj := by
    simp only [List.getElem_drop, hidx]
  rw [← h]
  exact List.getElem_mem hj'

lemma list_nodup_of_toFinset_card {α : Type*} [DecidableEq α] (l : List α)
    (h : l.toFinset.card = l.length) : l.Nodup := by
  induction l with
  | nil => exact List.nodup_nil
  | cons x xs ih =>
    simp only [List.toFinset_cons, List.length_cons] at h
    by_cases hx : x ∈ xs.toFinset
    · rw [Finset.insert_eq_of_mem hx] at h
      have hle := List.toFinset_card_le xs
      omega
    · rw [Finset.card_insert_of_notMem hx] at h
      rw [List.mem_toFinset] at hx
      exact List.nodup_cons.mpr ⟨hx, ih (by omega)⟩

set_option maxHeartbeats 1200000 in
theorem main_proof :
    ¬ (∃ C : PEqualNP.CircuitLowerBounds.Circuit,
      PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 11 ∧
      (∀ x : Fin 9 → Bool, C.eval (List.ofFn x) = ((x 0 && x 4 && x 8) || (x 0 && x 5 && x 7) || (x 1 && x 3 && x 8) || (x 1 && x 5 && x 6) || (x 2 && x 3 && x 7) || (x 2 && x 4 && x 6))) ∧
      C.output + 1 = 9 + C.size ∧
      (∀ j : Fin C.gates.length,
        ((C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧
            ∃ a, a < 9 + j.val ∧ (C.gates.get j).inputs = [a]) ∨
        (((C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
            (C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧
            ∃ a b, a < b ∧ b < 9 + j.val ∧ (C.gates.get j).inputs = [a, b])) ∧
      (∀ j : Fin C.gates.length,
        (∃ x y : Fin 9 → Bool,
          (C.wires (List.ofFn x)).getD (9 + j.val) false ≠ (C.wires (List.ofFn y)).getD (9 + j.val) false) ∧
        ∀ k, k < 9 + j.val → ∃ x : Fin 9 → Bool,
          (C.wires (List.ofFn x)).getD (9 + j.val) false ≠ (C.wires (List.ofFn x)).getD k false) ∧
      (∀ j : Fin C.gates.length, j.val + 1 < C.gates.length →
        ∃ k : Fin C.gates.length, j.val < k.val ∧ 9 + j.val ∈ (C.gates.get k).inputs) ∧
      C.gates.head? = some ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 4]⟩ ∧
      C.gates.tail.head? = some ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [2, 9]⟩) := by
  rintro ⟨C, _, hSize, hEval, hOut, hShape, _, hUsed, hHead, hTail⟩
  have hS_le : C.gates.length ≤ 11 := hSize
  cases hg0 : C.gates with
  | nil => simp [hg0] at hHead
  | cons g0 rest0 =>
    simp only [hg0, List.head?_cons, Option.some.injEq] at hHead
    subst hHead
    cases hg1 : rest0 with
    | nil => simp [hg0, hg1] at hTail
    | cons g1 tail =>
      simp only [hg0, hg1, List.tail_cons, List.head?_cons, Option.some.injEq] at hTail
      subst hTail
      have hge2 : 2 ≤ C.gates.length := by rw [hg0, hg1]; simp
      have hback : ∀ (j : ℕ) (hj : j < C.gates.length), ∀ i ∈ (C.gates[j]'hj).inputs, i < 9 + j := by
        intro j hj i hi
        have hs := hShape ⟨j, hj⟩
        simp only [List.get_eq_getElem] at hs
        rcases hs with ⟨_, a, ha, hinp⟩ | ⟨_, a, b, hab, hb, hinp⟩
        · rw [hinp] at hi
          simp only [List.mem_singleton] at hi
          omega
        · rw [hinp] at hi
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
          rcases hi with rfl | rfl <;> omega
      have hg0_val : ∀ x : Fin 9 → Bool, (C.wires (List.ofFn x)).getD 9 false = (x 0 && x 4) := by
        intro x
        have h := wire_getD_gate_full C x 0 (by omega) (hback 0 (by omega))
        have hg0e : C.gates[0]'(by omega) = ⟨.and, [0, 4]⟩ := by simp [hg0]
        rw [hg0e] at h
        simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil, id_eq,
          Bool.and_true] at h
        have h0 : (C.wires (List.ofFn x)).getD 0 false = x 0 := wire_getD_input C x 0
        have h4 : (C.wires (List.ofFn x)).getD 4 false = x 4 := wire_getD_input C x 4
        rw [h0, h4] at h
        exact h
      have hg1_val : ∀ x : Fin 9 → Bool, (C.wires (List.ofFn x)).getD 10 false = (x 2 || (x 0 && x 4)) := by
        intro x
        have h := wire_getD_gate_full C x 1 (by omega) (hback 1 (by omega))
        have hg1e : C.gates[1]'(by omega) = ⟨.or, [2, 9]⟩ := by simp [hg0, hg1]
        rw [hg1e] at h
        simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil, id_eq,
          Bool.or_false] at h
        have h2 : (C.wires (List.ofFn x)).getD 2 false = x 2 := wire_getD_input C x 2
        rw [h2, hg0_val x] at h
        exact h
      have hTailEq : tail = C.gates.drop 2 := by simp [hg0, hg1]
      have hSlots_in : ∀ v : Fin 9, v.val ∈ tail.flatMap Gate.inputs := by
        intro v
        by_contra hnot
        have hunused : ∀ (j : ℕ) (hj : j < C.gates.length), 2 ≤ j → v.val ∉ (C.gates[j]'hj).inputs := by
          intro j hj hj2 hmem
          apply hnot
          refine List.mem_flatMap.mpr ⟨C.gates[j]'hj, ?_, hmem⟩
          rw [hTailEq]
          exact mem_drop_of_ge C.gates 2 j hj hj2
        obtain ⟨hxy, h9e, h10e, hpm⟩ := wit_props v
        have h9w : (C.wires (List.ofFn (witX v))).getD 9 false =
            (C.wires (List.ofFn (witY v))).getD 9 false := by
          rw [hg0_val, hg0_val, h9e]
        have h10w : (C.wires (List.ofFn (witX v))).getD 10 false =
            (C.wires (List.ofFn (witY v))).getD 10 false := by
          rw [hg1_val, hg1_val, h10e]
        have hout_lt : C.output < 9 + C.gates.length := by
          change C.output + 1 = 9 + C.gates.length at hOut
          omega
        have hout_ne : C.output ≠ v.val := by
          change C.output + 1 = 9 + C.gates.length at hOut
          have := v.isLt
          omega
        have heq_out := agree_of_unused C hback hge2 v hunused (witX v) (witY v) hxy h9w h10w
          C.output hout_lt hout_ne
        have hevX : C.eval (List.ofFn (witX v)) = pm3 (witX v) := hEval (witX v)
        have hevY : C.eval (List.ofFn (witY v)) = pm3 (witY v) := hEval (witY v)
        exact hpm (hevX.symm.trans (heq_out.trans hevY))
      have hSlots_gate : ∀ j : ℕ, 1 ≤ j → j + 1 < C.gates.length → 9 + j ∈ tail.flatMap Gate.inputs := by
        intro j hj1 hjlt
        obtain ⟨k, hjk, hmem⟩ := hUsed ⟨j, by omega⟩ hjlt
        dsimp only at hjk hmem
        refine List.mem_flatMap.mpr ⟨C.gates[k.val]'k.isLt, ?_, by simpa only [List.get_eq_getElem] using hmem⟩
        rw [hTailEq]
        exact mem_drop_of_ge C.gates 2 k.val k.isLt (by omega)
      let req : Finset ℕ := Finset.range 9 ∪ Finset.Ico 10 (9 + C.gates.length - 1)
      have hreq_sub : req ⊆ (tail.flatMap Gate.inputs).toFinset := by
        intro w hw
        rw [List.mem_toFinset]
        rcases Finset.mem_union.mp hw with h1 | h2
        · rw [Finset.mem_range] at h1
          exact hSlots_in ⟨w, h1⟩
        · rw [Finset.mem_Ico] at h2
          have h := hSlots_gate (w - 9) (by omega) (by omega)
          have hw_eq : 9 + (w - 9) = w := by omega
          rwa [hw_eq] at h
      have hreq_card : req.card = 9 + (C.gates.length - 2) := by
        have hdisj : Disjoint (Finset.range 9) (Finset.Ico 10 (9 + C.gates.length - 1)) := by
          rw [Finset.disjoint_left]
          intro a ha1 ha2
          rw [Finset.mem_range] at ha1
          rw [Finset.mem_Ico] at ha2
          omega
        rw [Finset.card_union_of_disjoint hdisj, Finset.card_range, Nat.card_Ico]
        omega
      have htail_len : tail.length = C.gates.length - 2 := by rw [hTailEq, List.length_drop]
      have htail_le2 : ∀ g ∈ tail, g.inputs.length ≤ 2 := by
        intro g hg
        rw [hTailEq] at hg
        obtain ⟨idx, hidx, rfl⟩ := List.mem_iff_getElem.mp hg
        have hjlt : 2 + idx < C.gates.length := by simp at hidx; omega
        have hs := hShape ⟨2 + idx, hjlt⟩
        simp only [List.get_eq_getElem] at hs
        rw [List.getElem_drop]
        rcases hs with ⟨_, a, _, hinp⟩ | ⟨_, a, b, _, _, hinp⟩ <;> simp [hinp]
      have hlen_le : (tail.flatMap Gate.inputs).length ≤ 2 * tail.length :=
        list_flatMap_length_le_two tail htail_le2
      have hcard_le : req.card ≤ (tail.flatMap Gate.inputs).toFinset.card :=
        Finset.card_le_card hreq_sub
      have hfin_le : (tail.flatMap Gate.inputs).toFinset.card ≤ (tail.flatMap Gate.inputs).length :=
        List.toFinset_card_le _
      have hS_eq : C.gates.length = 11 := by omega
      have hlen_eq : (tail.flatMap Gate.inputs).length = 18 := by omega
      have hfin_eq : (tail.flatMap Gate.inputs).toFinset.card = 18 := by omega
      have hnodup : (tail.flatMap Gate.inputs).Nodup :=
        list_nodup_of_toFinset_card (tail.flatMap Gate.inputs) (by omega)
      have hreq_eq : (tail.flatMap Gate.inputs).toFinset = req :=
        (Finset.eq_of_subset_of_card_le hreq_sub (by omega)).symm
      have hno_not : ∀ (j : ℕ) (hj : j < C.gates.length), 2 ≤ j →
          ((C.gates[j]'hj).op = GateOp.and ∨ (C.gates[j]'hj).op = GateOp.or) ∧
          ∃ a b, a < b ∧ b < 9 + j ∧ (C.gates[j]'hj).inputs = [a, b] := by
        intro j hj hj2
        have hs := hShape ⟨j, hj⟩
        simp only [List.get_eq_getElem] at hs
        rcases hs with ⟨_, a, _, hinp⟩ | hbin
        · have hmem : C.gates[j]'hj ∈ tail := by
            rw [hTailEq]
            exact mem_drop_of_ge C.gates 2 j hj hj2
          have hlt := list_flatMap_length_lt_of_len1 tail htail_le2 (C.gates[j]'hj) hmem
            (by simp [hinp])
          omega
        · exact hbin
      have hnot9 : 9 ∉ tail.flatMap Gate.inputs := by
        intro h9mem
        have h9r : 9 ∈ req := by rw [← hreq_eq, List.mem_toFinset]; exact h9mem
        rcases Finset.mem_union.mp h9r with h1 | h2
        · rw [Finset.mem_range] at h1; omega
        · rw [Finset.mem_Ico] at h2; omega
      let wfn : ℕ → (Fin 4 → Bool) → Bool :=
        fun w y => (C.wires (List.ofFn (assign4 y))).getD w false
      have hbase_ro : ∀ w ∈ (Finset.range 9 ∪ {10} : Finset ℕ),
          IsRO (deps0 w) (wfn w) := by
        intro w hw
        rcases Finset.mem_union.mp hw with h1 | h2
        · rw [Finset.mem_range] at h1
          have hwv : wfn w = fun y => assign4 y ⟨w, h1⟩ := by
            funext y
            exact wire_getD_input C (assign4 y) ⟨w, h1⟩
          rw [hwv]
          interval_cases w <;> simp only [deps0, assign4, mkIn]
          · exact IsRO.const true
          · exact IsRO.const true
          · exact IsRO.const true
          · exact IsRO.var 0
          · exact IsRO.const false
          · exact IsRO.var 2
          · exact IsRO.var 3
          · exact IsRO.var 1
          · exact IsRO.const false
        · rw [Finset.mem_singleton] at h2
          subst h2
          have hw10 : wfn 10 = fun _ => true := by
            funext y
            simp only [wfn, hg1_val, assign4, mkIn, Bool.true_or]
          rw [hw10]
          exact IsRO.const true
      have hstep_inv : ∀ m : ℕ, m ≤ 9 →
          ∃ (deps : ℕ → Finset (Fin 4)),
            let active : Finset ℕ :=
              ((Finset.range 9 ∪ {10}) ∪ Finset.Ico 11 (11 + m)) \
                ((tail.take m).flatMap Gate.inputs).toFinset
            (∀ w ∈ active, IsRO (deps w) (wfn w)) ∧
            (∀ u ∈ active, ∀ v ∈ active, u ≠ v → Disjoint (deps u) (deps v)) := by
        intro m
        induction m with
        | zero =>
          intro _
          refine ⟨deps0, ?_, ?_⟩
          · intro w hw
            simp only [List.take_zero, List.flatMap_nil, List.toFinset_nil, Finset.sdiff_empty,
              Nat.add_zero, Finset.Ico_self, Finset.union_empty] at hw
            exact hbase_ro w hw
          · intro u _ v _ huv
            exact deps0_disjoint u v huv
        | succ m ih =>
          intro hm
          obtain ⟨deps, hro, hdisj⟩ := ih (by omega)
          have hjlt : 2 + m < C.gates.length := by omega
          obtain ⟨hop, a, b, hab, hblt, hinp⟩ := hno_not (2 + m) hjlt (by omega)
          have htail_m : tail[m]'(by omega) = C.gates[2 + m]'hjlt := by
            simp only [hTailEq, List.getElem_drop]
          have htake : tail.take (m + 1) = tail.take m ++ [C.gates[2 + m]'hjlt] := by
            rw [List.take_succ_eq_append_getElem (by omega : m < tail.length), htail_m]
          have htake_flat : (tail.take (m + 1)).flatMap Gate.inputs =
              (tail.take m).flatMap Gate.inputs ++ [a, b] := by
            rw [htake, List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil, hinp]
          have ha_not_prev : a ∉ (tail.take m).flatMap Gate.inputs := by
            have hsub : tail = tail.take (m + 1) ++ tail.drop (m + 1) := (List.take_append_drop _ _).symm
            have hnd1 : ((tail.take (m + 1)).flatMap Gate.inputs).Nodup := by
              have h := hnodup
              rw [hsub, List.flatMap_append] at h
              exact (List.nodup_append.mp h).1
            rw [htake_flat, List.nodup_append] at hnd1
            intro ha_in
            exact hnd1.2.2 a ha_in a (by simp) rfl
          have hb_not_prev : b ∉ (tail.take m).flatMap Gate.inputs := by
            have hsub : tail = tail.take (m + 1) ++ tail.drop (m + 1) := (List.take_append_drop _ _).symm
            have hnd1 : ((tail.take (m + 1)).flatMap Gate.inputs).Nodup := by
              have h := hnodup
              rw [hsub, List.flatMap_append] at h
              exact (List.nodup_append.mp h).1
            rw [htake_flat, List.nodup_append] at hnd1
            intro hb_in
            exact hnd1.2.2 b hb_in b (by simp) rfl
          have ha_ne9 : a ≠ 9 := by
            intro ha9
            apply hnot9
            refine List.mem_flatMap.mpr ⟨C.gates[2 + m]'hjlt, ?_, by rw [hinp, ha9]; simp⟩
            rw [← htail_m]
            exact List.getElem_mem (by omega)
          have hb_ne9 : b ≠ 9 := by
            intro hb9
            apply hnot9
            refine List.mem_flatMap.mpr ⟨C.gates[2 + m]'hjlt, ?_, by rw [hinp, hb9]; simp⟩
            rw [← htail_m]
            exact List.getElem_mem (by omega)
          have ha_act : a ∈ ((Finset.range 9 ∪ {10}) ∪ Finset.Ico 11 (11 + m)) \
              ((tail.take m).flatMap Gate.inputs).toFinset := by
            rw [Finset.mem_sdiff, List.mem_toFinset]
            refine ⟨?_, ha_not_prev⟩
            by_cases h9 : a < 9
            · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_range.mpr h9))
            · by_cases h10 : a = 10
              · exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h10))
              · exact Finset.mem_union_right _ (Finset.mem_Ico.mpr ⟨by omega, by omega⟩)
          have hb_act : b ∈ ((Finset.range 9 ∪ {10}) ∪ Finset.Ico 11 (11 + m)) \
              ((tail.take m).flatMap Gate.inputs).toFinset := by
            rw [Finset.mem_sdiff, List.mem_toFinset]
            refine ⟨?_, hb_not_prev⟩
            by_cases h9 : b < 9
            · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_range.mpr h9))
            · by_cases h10 : b = 10
              · exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h10))
              · exact Finset.mem_union_right _ (Finset.mem_Ico.mpr ⟨by omega, by omega⟩)
          have hdisj_ab : Disjoint (deps a) (deps b) := hdisj a ha_act b hb_act (by omega)
          have hw_new : IsRO (deps a ∪ deps b) (wfn (11 + m)) := by
            rcases hop with hand | hor
            · have hwf : wfn (11 + m) = fun y => wfn a y && wfn b y := by
                funext y
                have h := wire_getD_gate_full C (assign4 y) (2 + m) hjlt (hback (2 + m) hjlt)
                have h9m : 9 + (2 + m) = 11 + m := by omega
                rw [h9m, hinp, hand] at h
                simpa [wfn, GateOp.eval] using h
              rw [hwf]
              exact IsRO.and hdisj_ab (hro a ha_act) (hro b hb_act)
            · have hwf : wfn (11 + m) = fun y => wfn a y || wfn b y := by
                funext y
                have h := wire_getD_gate_full C (assign4 y) (2 + m) hjlt (hback (2 + m) hjlt)
                have h9m : 9 + (2 + m) = 11 + m := by omega
                rw [h9m, hinp, hor] at h
                simpa [wfn, GateOp.eval] using h
              rw [hwf]
              exact IsRO.or hdisj_ab (hro a ha_act) (hro b hb_act)
          let deps' : ℕ → Finset (Fin 4) := fun w => if w = 11 + m then deps a ∪ deps b else deps w
          refine ⟨deps', ?_, ?_⟩
          · intro w hw
            by_cases hwm : w = 11 + m
            · subst hwm
              simp only [deps', ite_true]
              exact hw_new
            · simp only [deps', hwm, ite_false]
              rw [Finset.mem_sdiff, List.mem_toFinset, htake_flat, List.mem_append] at hw
              have hw_old : w ∈ ((Finset.range 9 ∪ {10}) ∪ Finset.Ico 11 (11 + m)) \
                  ((tail.take m).flatMap Gate.inputs).toFinset := by
                rw [Finset.mem_sdiff, List.mem_toFinset]
                refine ⟨?_, fun h => hw.2 (Or.inl h)⟩
                rcases Finset.mem_union.mp hw.1 with h1 | h2
                · exact Finset.mem_union_left _ h1
                · rw [Finset.mem_Ico] at h2
                  exact Finset.mem_union_right _ (Finset.mem_Ico.mpr ⟨h2.1, by omega⟩)
              exact hro w hw_old
          · intro u hu v hv huv
            rw [Finset.mem_sdiff, List.mem_toFinset, htake_flat, List.mem_append] at hu hv
            have hmem_old : ∀ w, w ≠ 11 + m →
                w ∈ ((Finset.range 9 ∪ {10}) ∪ Finset.Ico 11 (11 + (m + 1))) ∧
                  ¬(w ∈ (tail.take m).flatMap Gate.inputs ∨ w ∈ [a, b]) →
                w ∈ ((Finset.range 9 ∪ {10}) ∪ Finset.Ico 11 (11 + m)) \
                  ((tail.take m).flatMap Gate.inputs).toFinset ∧ w ≠ a ∧ w ≠ b := by
              intro w hwm hw
              refine ⟨?_, fun h => hw.2 (Or.inr (by simp [h])), fun h => hw.2 (Or.inr (by simp [h]))⟩
              rw [Finset.mem_sdiff, List.mem_toFinset]
              refine ⟨?_, fun h => hw.2 (Or.inl h)⟩
              rcases Finset.mem_union.mp hw.1 with h1 | h2
              · exact Finset.mem_union_left _ h1
              · rw [Finset.mem_Ico] at h2
                exact Finset.mem_union_right _ (Finset.mem_Ico.mpr ⟨h2.1, by omega⟩)
            by_cases hum : u = 11 + m
            · subst hum
              have hvm : v ≠ 11 + m := huv.symm
              obtain ⟨hv_old, hva, hvb⟩ := hmem_old v hvm hv
              simp only [deps', ite_true, hvm, ite_false]
              exact Finset.disjoint_union_left.mpr ⟨hdisj a ha_act v hv_old hva.symm, hdisj b hb_act v hv_old hvb.symm⟩
            · by_cases hvm : v = 11 + m
              · subst hvm
                obtain ⟨hu_old, hua, hub⟩ := hmem_old u hum hu
                simp only [deps', ite_true, hum, ite_false]
                exact Finset.disjoint_union_right.mpr ⟨hdisj u hu_old a ha_act hua, hdisj u hu_old b hb_act hub⟩
              · obtain ⟨hu_old, _, _⟩ := hmem_old u hum hu
                obtain ⟨hv_old, _, _⟩ := hmem_old v hvm hv
                simp only [deps', hum, hvm, ite_false]
                exact hdisj u hu_old v hv_old huv
      obtain ⟨deps, hro9, _⟩ := hstep_inv 9 (le_refl 9)
      have h19_act : 19 ∈ ((Finset.range 9 ∪ {10}) ∪ Finset.Ico 11 (11 + 9)) \
          ((tail.take 9).flatMap Gate.inputs).toFinset := by
        rw [Finset.mem_sdiff, List.mem_toFinset]
        refine ⟨Finset.mem_union_right _ (Finset.mem_Ico.mpr (by omega)), ?_⟩
        rw [List.take_of_length_le (by omega : tail.length ≤ 9)]
        intro h19m
        have h19r : 19 ∈ req := by rw [← hreq_eq, List.mem_toFinset]; exact h19m
        rcases Finset.mem_union.mp h19r with h1 | h2
        · rw [Finset.mem_range] at h1; omega
        · rw [Finset.mem_Ico] at h2; omega
      have hro_out : IsRO (deps 19) (wfn 19) := hro9 19 h19_act
      have hw19_p4 : wfn 19 = p4 := by
        funext y
        have hout19 : C.output = 19 := by
          change C.output + 1 = 9 + C.gates.length at hOut
          omega
        have h := hEval (assign4 y)
        change (C.wires (List.ofFn (assign4 y))).getD C.output false = pm3 (assign4 y) at h
        rw [hout19, pm3_assign4] at h
        exact h
      exact hro_out.not_p4 hw19_p4

end PEqualNP.Outside.L_meta_27335_aux

theorem PEqualNP.Outside.L_meta_27335 : ¬ (∃ C : PEqualNP.CircuitLowerBounds.Circuit,
    PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 11 ∧
    (∀ x : Fin 9 → Bool, C.eval (List.ofFn x) = ((x 0 && x 4 && x 8) || (x 0 && x 5 && x 7) || (x 1 && x 3 && x 8) || (x 1 && x 5 && x 6) || (x 2 && x 3 && x 7) || (x 2 && x 4 && x 6))) ∧
    C.output + 1 = 9 + C.size ∧
    (∀ j : Fin C.gates.length,
      ((C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧
          ∃ a, a < 9 + j.val ∧ (C.gates.get j).inputs = [a]) ∨
      (((C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
          (C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧
          ∃ a b, a < b ∧ b < 9 + j.val ∧ (C.gates.get j).inputs = [a, b])) ∧
    (∀ j : Fin C.gates.length,
      (∃ x y : Fin 9 → Bool,
        (C.wires (List.ofFn x)).getD (9 + j.val) false ≠ (C.wires (List.ofFn y)).getD (9 + j.val) false) ∧
      ∀ k, k < 9 + j.val → ∃ x : Fin 9 → Bool,
        (C.wires (List.ofFn x)).getD (9 + j.val) false ≠ (C.wires (List.ofFn x)).getD k false) ∧
    (∀ j : Fin C.gates.length, j.val + 1 < C.gates.length →
      ∃ k : Fin C.gates.length, j.val < k.val ∧ 9 + j.val ∈ (C.gates.get k).inputs) ∧
    C.gates.head? = some ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 4]⟩ ∧
    C.gates.tail.head? = some ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [2, 9]⟩) :=
  PEqualNP.Outside.L_meta_27335_aux.main_proof
