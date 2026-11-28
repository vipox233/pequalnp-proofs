import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_32030.Shared

open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity (FanInTwo)
open PEqualNP.MetaComplexity.NestedCover (ReadsBack)

section GateBridge

variable {α : Type*}

def Scheduled (n : Nat) (F : α → (Fin n → Bool) → Bool) (k : Nat) (S : Set α) : Prop :=
  ∃ gs : List Gate, gs.length = k ∧ ReadsBack n ⟨gs, 0⟩ ∧ FanInTwo ⟨gs, 0⟩ ∧
    ∀ a ∈ S, ∃ i : Nat, i < n + k ∧
      ∀ x : Fin n → Bool, ((Circuit.mk gs 0).wires (List.ofFn x)).getD i false = F a x

theorem wireLength (C : Circuit) (w : List Bool) :
    (C.wires w).length = w.length + C.gates.length := by
  rcases C with ⟨gs, out⟩
  change (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    w).length = w.length + gs.length
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega

theorem schedStart {n : Nat} {F : α → (Fin n → Bool) → Bool}
    (input : Fin n → α) (h : ∀ i x, F (input i) x = x i) :
    Scheduled n F 0 (Set.range input) := by
  refine ⟨[], rfl, ?_, ?_, ?_⟩
  · simp [ReadsBack]
  · simp [FanInTwo]
  · intro a ha
    obtain ⟨i, rfl⟩ := Set.mem_range.mp ha
    refine ⟨i.val, by simp, fun x => ?_⟩
    change (List.ofFn x).getD i.val false = F (input i) x
    rw [List.getD_eq_getElem _ _ (by simp), List.getElem_ofFn, h i x]

theorem schedRestrict {n k : Nat} {F : α → (Fin n → Bool) → Bool} {S T : Set α}
    (h : Scheduled n F k S) (hsub : T ⊆ S) : Scheduled n F k T := by
  obtain ⟨gs, hs, hr, hf, hw⟩ := h
  exact ⟨gs, hs, hr, hf, fun a ha => hw a (hsub ha)⟩

theorem realizeDeps {n k : Nat} {F : α → (Fin n → Bool) → Bool} {S : Set α}
    {gs : List Gate}
    (hw : ∀ a ∈ S, ∃ i : Nat, i < n + k ∧
      ∀ x : Fin n → Bool, ((Circuit.mk gs 0).wires (List.ofFn x)).getD i false = F a x)
    (deps : List α) (hdeps : ∀ a ∈ deps, a ∈ S) :
    ∃ is : List Nat, is.length = deps.length ∧ (∀ i ∈ is, i < n + k) ∧
      ∀ x : Fin n → Bool,
        is.map (fun i => ((Circuit.mk gs 0).wires (List.ofFn x)).getD i false) =
          deps.map (fun a => F a x) := by
  induction deps with
  | nil => exact ⟨[], rfl, by simp, by simp⟩
  | cons a deps ih =>
    obtain ⟨i, hi, hval⟩ := hw a (hdeps a List.mem_cons_self)
    obtain ⟨is, hlen, hbound, hvals⟩ := ih (fun b hb => hdeps b (List.mem_cons_of_mem a hb))
    refine ⟨i :: is, by simp [hlen], ?_, fun x => ?_⟩
    · intro j hj
      rcases List.mem_cons.mp hj with rfl | hj
      · exact hi
      · exact hbound j hj
    · simp only [List.map_cons, hval x, hvals x]

theorem schedPush {n k : Nat} {F : α → (Fin n → Bool) → Bool} {S : Set α}
    (h : Scheduled n F k S) (op : GateOp) (deps : List α) (out : α)
    (hop : op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp))
    (hlen : deps.length ≤ 2) (hdeps : ∀ a ∈ deps, a ∈ S)
    (hval : ∀ x, F out x = op.eval (deps.map fun a => F a x)) :
    Scheduled n F (k + 1) (insert out S) := by
  obtain ⟨gs, hgs, hr, hf, hw⟩ := h
  obtain ⟨is, his, hbound, hvalues⟩ := realizeDeps hw deps hdeps
  let g : Gate := ⟨op, is⟩
  have hlength (x : Fin n → Bool) :
      ((Circuit.mk gs 0).wires (List.ofFn x)).length = n + k := by
    rw [wireLength]
    simpa using congrArg (n + ·) hgs
  have hsnoc (x : Fin n → Bool) :
      (Circuit.mk (gs ++ [g]) 0).wires (List.ofFn x) =
        (Circuit.mk gs 0).wires (List.ofFn x) ++ [F out x] := by
    simp only [Circuit.wires, List.foldl_append, List.foldl_cons, List.foldl_nil]
    change (Circuit.mk gs 0).wires (List.ofFn x) ++
      [op.eval (is.map fun i => ((Circuit.mk gs 0).wires (List.ofFn x)).getD i false)] =
        (Circuit.mk gs 0).wires (List.ofFn x) ++ [F out x]
    rw [hvalues x, hval x]
  refine ⟨gs ++ [g], by simp [hgs], ?_, ?_, ?_⟩
  · intro j hj i hi
    change j < (gs ++ [g]).length at hj
    change i ∈ ((gs ++ [g]).getD j ⟨GateOp.or, []⟩).inputs at hi
    by_cases hj' : j < gs.length
    · rw [List.getD_append _ _ _ _ hj'] at hi
      exact hr j hj' i hi
    · have heq : j = gs.length := by
        simp only [List.length_append, List.length_singleton] at hj
        omega
      subst j
      rw [List.getD_append_right _ _ _ _ le_rfl] at hi
      have hi' : i ∈ is := by simpa [g] using hi
      simpa [hgs] using hbound i hi'
  · intro g' hg'
    change g' ∈ gs ++ [g] at hg'
    rcases List.mem_append.mp hg' with hg' | hg'
    · exact hf g' hg'
    · have heq : g' = g := List.mem_singleton.mp hg'
      subst g'
      refine ⟨hop, ?_⟩
      change is.length ≤ 2
      simpa only [his] using hlen
  · intro a ha
    rcases Set.mem_insert_iff.mp ha with rfl | ha
    · refine ⟨n + k, by omega, fun x => ?_⟩
      rw [hsnoc x, List.getD_append_right _ _ _ _ (by simp [hlength x])]
      simp [hlength x]
    · obtain ⟨i, hi, hval'⟩ := hw a ha
      refine ⟨i, by omega, fun x => ?_⟩
      rw [hsnoc x, List.getD_append _ _ _ _ (by simpa [hlength x] using hi), hval' x]

end GateBridge

section BuildComb

variable {n : Nat}
abbrev Sig (n : Nat) := (Fin n → Bool) → Bool

def Build (A B : Set (Sig n)) (b : Nat) : Prop :=
  True ∧ (∀ {m S}, Scheduled n id m S → A ⊆ S →
    ∃ c ≤ b, Scheduled n id (m + c) (S ∪ B))

theorem Build.run {A B : Set (Sig n)} {b m S} (H : Build A B b)
    (HS : Scheduled n id m S) (hA : A ⊆ S) :
    ∃ c ≤ b, Scheduled n id (m + c) (S ∪ B) := H.2 HS hA

theorem idle {A B : Set (Sig n)} (h : B ⊆ A) : Build A B 0 := by
  refine ⟨trivial, ?_⟩
  intro m S HS hA
  refine ⟨0, Nat.le_refl _, ?_⟩
  simpa [Set.union_eq_left.mpr (h.trans hA)] using HS

theorem relax {A B C D : Set (Sig n)} {b d : Nat}
    (H : Build A B b) (hA : A ⊆ C) (hB : D ⊆ B) (h : b ≤ d) : Build C D d := by
  refine ⟨trivial, ?_⟩
  intro m S HS hC
  obtain ⟨c, hc, HS'⟩ := H.run HS (hA.trans hC)
  exact ⟨c, hc.trans h, schedRestrict HS' (Set.union_subset_union le_rfl hB)⟩

theorem seq {A B C : Set (Sig n)} {b c : Nat}
    (H : Build A B b) (J : Build (A ∪ B) C c) : Build A (B ∪ C) (b + c) := by
  refine ⟨trivial, ?_⟩
  intro m S HS hA
  obtain ⟨d, hd, K⟩ := H.run HS hA
  obtain ⟨e, he, K'⟩ := J.run K (Set.union_subset_union hA le_rfl)
  exact ⟨d + e, Nat.add_le_add hd he, by simpa [Nat.add_assoc, Set.union_assoc] using K'⟩

theorem oneG {A : Set (Sig n)} (op : GateOp) (deps : List (Sig n))
    (hop : op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp)) (hlen : deps.length ≤ 2)
    (hd : ∀ g ∈ deps, g ∈ A) (f : Sig n)
    (hv : ∀ x, f x = op.eval (deps.map fun g => g x)) : Build A {f} 1 := by
  refine ⟨trivial, ?_⟩
  intro m S HS hA
  refine ⟨1, le_rfl, ?_⟩
  have h := schedPush HS op deps f hop hlen (fun g hg => hA (hd g hg)) hv
  rw [Set.insert_eq] at h
  exact schedRestrict h (by intro g hg; exact hg.elim Or.inr Or.inl)

def an (f g : Sig n) : Sig n := fun x => f x && g x
def orS (f g : Sig n) : Sig n := fun x => f x || g x
def nt (f : Sig n) : Sig n := fun x => !f x
def xr (f g : Sig n) : Sig n := fun x => xor (f x) (g x)

theorem andG {A : Set (Sig n)} {f g : Sig n} (hf : f ∈ A) (hg : g ∈ A) :
    Build A {an f g} 1 :=
  oneG .and [f, g] (by simp) (by simp) (by simpa using And.intro hf hg) _ (by simp [GateOp.eval, an])

theorem orG {A : Set (Sig n)} {f g : Sig n} (hf : f ∈ A) (hg : g ∈ A) :
    Build A {orS f g} 1 :=
  oneG .or [f, g] (by simp) (by simp) (by simpa using And.intro hf hg) _ (by simp [GateOp.eval, orS])

theorem notG {A : Set (Sig n)} {f : Sig n} (hf : f ∈ A) : Build A {nt f} 1 :=
  oneG .not [f] (by simp) (by simp) (by simpa using hf) _ (by simp [GateOp.eval, nt])

theorem constG {A : Set (Sig n)} (b : Bool) : Build A {fun _ => b} 1 := by
  cases b
  · exact oneG .or [] (by simp) (by simp) (by simp) _ (by intro; rfl)
  · exact oneG .and [] (by simp) (by simp) (by simp) _ (by intro; rfl)

theorem xorG {A : Set (Sig n)} {f g : Sig n} (hf : f ∈ A) (hg : g ∈ A) :
    Build A {xr f g} 4 := by
  have he : xr f g = an (orS f g) (nt (an f g)) := by
    funext x; simp only [xr, an, orS, nt]; cases f x <;> cases g x <;> rfl
  rw [he]
  have h1 := orG hf hg
  have h2 := andG (A := A ∪ {orS f g}) (Or.inl hf) (Or.inl hg)
  have h3 := notG (A := A ∪ ({orS f g} ∪ {an f g})) (Or.inr (Or.inr rfl))
  have h4 := andG (A := A ∪ (({orS f g} ∪ {an f g}) ∪ {nt (an f g)}))
    (Or.inr (Or.inl (Or.inl rfl))) (Or.inr (Or.inr rfl))
  exact relax (seq (seq (seq h1 h2) h3) h4) le_rfl (Set.singleton_subset_iff.mpr (Or.inr rfl)) le_rfl

theorem muxG {A : Set (Sig n)} {sw nsw t f : Sig n}
    (hsw : sw ∈ A) (hnsw : nsw ∈ A) (ht : t ∈ A) (hf : f ∈ A)
    (hneg : ∀ x, nsw x = !(sw x)) :
    Build A {fun x => if sw x then t x else f x} 3 := by
  have he : (fun x => if sw x then t x else f x) = orS (an sw t) (an nsw f) := by
    funext x
    simp only [orS, an, hneg x]
    cases sw x <;> cases t x <;> cases f x <;> rfl
  rw [he]
  have h1 := andG hsw ht
  have h2 := andG (A := A ∪ {an sw t}) (Or.inl hnsw) (Or.inl hf)
  have h3 := orG (A := A ∪ ({an sw t} ∪ {an nsw f}))
    (f := an sw t) (g := an nsw f) (Or.inr (Or.inl rfl)) (Or.inr (Or.inr rfl))
  exact relax (seq (seq h1 h2) h3) le_rfl (Set.singleton_subset_iff.mpr (Or.inr rfl)) le_rfl

theorem listBuild {α : Type*} {A : Set (Sig n)} (xs : List α)
    (F : α → Sig n) (c : Nat) (H : ∀ a ∈ xs, Build A {F a} c) :
    Build A {f | ∃ a ∈ xs, f = F a} (xs.length * c) := by
  induction xs with
  | nil =>
    exact relax (idle (A := A) (B := ∅) (by simp)) le_rfl (by simp) (by simp)
  | cons a xs ih =>
    have h1 := H a List.mem_cons_self
    have h2 := ih (fun b hb => H b (List.mem_cons_of_mem a hb))
    have h2' := relax h2 (C := A ∪ {F a}) Set.subset_union_left le_rfl le_rfl
    refine relax (seq h1 h2') le_rfl ?_ ?_
    · rintro f ⟨b, hb, rfl⟩
      rcases List.mem_cons.mp hb with rfl | hb
      · exact Or.inl rfl
      · exact Or.inr ⟨b, hb, rfl⟩
    · simp only [List.length_cons]
      rw [Nat.succ_mul xs.length, Nat.add_comm]

theorem listBuildSets {α : Type*} {A : Set (Sig n)} (xs : List α)
    (B : α → Set (Sig n)) (c : Nat) (H : ∀ a ∈ xs, Build A (B a) c) :
    Build A {f | ∃ a ∈ xs, f ∈ B a} (xs.length * c) := by
  induction xs with
  | nil =>
    exact relax (idle (A := A) (B := ∅) (by simp)) le_rfl (by simp) (by simp)
  | cons a xs ih =>
    have h1 := H a List.mem_cons_self
    have h2 := ih (fun b hb => H b (List.mem_cons_of_mem a hb))
    have h2' := relax h2 (C := A ∪ B a) Set.subset_union_left le_rfl le_rfl
    refine relax (seq h1 h2') le_rfl ?_ ?_
    · rintro f ⟨b, hb, hfb⟩
      rcases List.mem_cons.mp hb with rfl | hb
      · exact Or.inl hfb
      · exact Or.inr ⟨b, hb, hfb⟩
    · simp only [List.length_cons]
      rw [Nat.succ_mul xs.length, Nat.add_comm]

theorem finG {k : Nat} {A : Set (Sig n)} (F : Fin k → Sig n) (c : Nat)
    (H : ∀ i, Build A {F i} c) : Build A (Set.range F) (k * c) := by
  have h := listBuild (List.finRange k) F c (fun i _ => H i)
  rw [List.length_finRange] at h
  refine relax h le_rfl ?_ le_rfl
  rintro _ ⟨i, rfl⟩
  exact ⟨i, List.mem_finRange i, rfl⟩

theorem rangeG {m : Nat} {A : Set (Sig n)} (F : Nat → Sig n) (c : Nat)
    (H : ∀ i < m, Build A {F i} c) : Build A {f | ∃ i < m, f = F i} (m * c) := by
  have h := listBuild (List.range m) F c (fun i hi => H i (List.mem_range.mp hi))
  rw [List.length_range] at h
  refine relax h le_rfl ?_ le_rfl
  rintro f ⟨i, hi, rfl⟩
  exact ⟨i, List.mem_range.mpr hi, rfl⟩

theorem rangeSetsG {m : Nat} {A : Set (Sig n)} (B : Nat → Set (Sig n)) (c : Nat)
    (H : ∀ i < m, Build A (B i) c) : Build A {f | ∃ i < m, f ∈ B i} (m * c) := by
  have h := listBuildSets (List.range m) B c (fun i hi => H i (List.mem_range.mp hi))
  rw [List.length_range] at h
  refine relax h le_rfl ?_ le_rfl
  rintro f ⟨i, hi, hfi⟩
  exact ⟨i, List.mem_range.mpr hi, hfi⟩

theorem ltStepG {A : Set (Sig n)} {xm ym prev : Sig n}
    (hx : xm ∈ A) (hy : ym ∈ A) (hp : prev ∈ A) :
    Build A {fun v => (!(xm v) && ym v) || ((!(xm v) || ym v) && prev v)} 5 := by
  have h1 := notG hx
  have h2 := andG (A := A ∪ {nt xm}) (Or.inr rfl) (Or.inl hy)
  have h3 := orG (A := A ∪ ({nt xm} ∪ {an (nt xm) ym}))
    (Or.inr (Or.inl rfl)) (Or.inl hy)
  have h4 := andG (A := A ∪ (({nt xm} ∪ {an (nt xm) ym}) ∪ {orS (nt xm) ym}))
    (Or.inr (Or.inr rfl)) (Or.inl hp)
  have h5 := orG (A := A ∪ ((({nt xm} ∪ {an (nt xm) ym}) ∪ {orS (nt xm) ym}) ∪ {an (orS (nt xm) ym) prev}))
    (Or.inr (Or.inl (Or.inl (Or.inr rfl)))) (Or.inr (Or.inr rfl))
  exact relax (seq (seq (seq (seq h1 h2) h3) h4) h5) le_rfl
    (Set.singleton_subset_iff.mpr (Or.inr rfl)) le_rfl

def bitsVal (f : Nat → Bool) : Nat → Nat
  | 0 => 0
  | m + 1 => bitsVal f m + if f m then 2 ^ m else 0

theorem bitsVal_lt (f : Nat → Bool) : ∀ m, bitsVal f m < 2 ^ m
  | 0 => by simp [bitsVal]
  | m + 1 => by
    have ih := bitsVal_lt f m
    simp only [bitsVal, Nat.pow_succ]
    cases f m <;> simp <;> omega

theorem bitsVal_testBit (f : Nat → Bool) : ∀ m i, i < m → (bitsVal f m).testBit i = f i
  | 0, _, hi => by omega
  | m + 1, i, hi => by
    simp only [bitsVal]
    have hlt := bitsVal_lt f m
    by_cases him : i = m
    · subst him
      cases hfm : f i
      · simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_zero]
        exact Nat.testBit_lt_two_pow hlt
      · simp only [↓reduceIte]
        rw [Nat.add_comm, Nat.testBit_two_pow_add_eq, Nat.testBit_lt_two_pow hlt]
        rfl
    · have him' : i < m := by omega
      cases hfm : f m
      · simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_zero]
        exact bitsVal_testBit f m i him'
      · simp only [↓reduceIte]
        rw [Nat.add_comm, Nat.testBit_two_pow_add_gt him']
        exact bitsVal_testBit f m i him'

theorem bitsVal_congr (f g : Nat → Bool) : ∀ m, (∀ i < m, f i = g i) → bitsVal f m = bitsVal g m
  | 0, _ => rfl
  | m + 1, h => by
    simp only [bitsVal]
    rw [bitsVal_congr f g m (fun i hi => h i (by omega)), h m (by omega)]

theorem bitsVal_add (f : Nat → Bool) (m : Nat) : ∀ k,
    bitsVal f (m + k) = bitsVal f m + 2 ^ m * bitsVal (fun j => f (m + j)) k
  | 0 => by simp [bitsVal]
  | k + 1 => by
    rw [← Nat.add_assoc]
    simp only [bitsVal]
    rw [bitsVal_add f m k]
    by_cases hf : f (m + k) = true <;> simp [hf, Nat.pow_add, Nat.mul_add, Nat.add_assoc]

theorem bitsVal_inj (f g : Nat → Bool) (m : Nat) (h : bitsVal f m = bitsVal g m) :
    ∀ i < m, f i = g i := by
  intro i hi
  rw [← bitsVal_testBit f m i hi, ← bitsVal_testBit g m i hi, h]

theorem bitsVal_of_testBit (x m : Nat) (hx : x < 2 ^ m) :
    bitsVal (fun i => x.testBit i) m = x := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < m
  · exact bitsVal_testBit (fun j => x.testBit j) m i hi
  · have h1 := Nat.testBit_lt_two_pow
      ((bitsVal_lt (fun j => x.testBit j) m).trans_le
        (Nat.pow_le_pow_right Nat.zero_lt_two (Nat.not_lt.mp hi)))
    have h2 := Nat.testBit_lt_two_pow
      (hx.trans_le (Nat.pow_le_pow_right Nat.zero_lt_two (Nat.not_lt.mp hi)))
    rw [h1, h2]

theorem bitsVal_lt_step (f g : Nat → Bool) (m : Nat) :
    decide (bitsVal f (m + 1) < bitsVal g (m + 1)) =
      ((!(f m) && g m) || ((!(f m) || g m) && decide (bitsVal f m < bitsVal g m))) := by
  have hf := bitsVal_lt f m
  have hg := bitsVal_lt g m
  apply Bool.eq_iff_iff.mpr
  rw [decide_eq_true_eq]
  simp only [bitsVal, Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq]
  cases f m <;> cases g m <;> simp <;> omega

theorem ltWordG {A : Set (Sig n)} (f g : Nat → Sig n) (m : Nat)
    (hf : ∀ i < m, f i ∈ A) (hg : ∀ i < m, g i ∈ A) (hfalse : (fun _ => false) ∈ A) :
    Build A {fun v => decide (bitsVal (fun i => f i v) m < bitsVal (fun i => g i v) m)} (5 * m) := by
  induction m with
  | zero =>
    have he : (fun v : Fin n → Bool => decide (bitsVal (fun i => f i v) 0 < bitsVal (fun i => g i v) 0)) =
        (fun _ => false) := by
      funext v; rfl
    rw [he]
    exact relax (idle (Set.singleton_subset_iff.mpr hfalse)) le_rfl le_rfl (by omega)
  | succ m ih =>
    have hprev := ih (fun i hi => hf i (by omega)) (fun i hi => hg i (by omega))
    let prev : Sig n := fun v => decide (bitsVal (fun i => f i v) m < bitsVal (fun i => g i v) m)
    have hstep : Build (A ∪ {prev})
        {fun v => (!(f m v) && g m v) || ((!(f m v) || g m v) && prev v)} 5 :=
      ltStepG (Or.inl (hf m (by omega))) (Or.inl (hg m (by omega))) (Or.inr rfl)
    have he : (fun v => (!(f m v) && g m v) || ((!(f m v) || g m v) && prev v)) =
        (fun v => decide (bitsVal (fun i => f i v) (m + 1) < bitsVal (fun i => g i v) (m + 1))) := by
      funext v
      exact (bitsVal_lt_step (fun i => f i v) (fun i => g i v) m).symm
    rw [he] at hstep
    refine relax (seq hprev hstep) le_rfl (Set.singleton_subset_iff.mpr (Or.inr rfl)) ?_
    omega

theorem neWordG {A : Set (Sig n)} (f g : Nat → Sig n) (m : Nat)
    (hf : ∀ i < m, f i ∈ A) (hg : ∀ i < m, g i ∈ A) (hfalse : (fun _ => false) ∈ A) :
    Build A {fun v => decide (bitsVal (fun i => f i v) m ≠ bitsVal (fun i => g i v) m)} (5 * m) := by
  induction m with
  | zero =>
    have he : (fun v : Fin n → Bool => decide (bitsVal (fun i => f i v) 0 ≠ bitsVal (fun i => g i v) 0)) =
        (fun _ => false) := by funext v; rfl
    rw [he]
    exact relax (idle (Set.singleton_subset_iff.mpr hfalse)) le_rfl le_rfl (by omega)
  | succ m ih =>
    have hprev := ih (fun i hi => hf i (by omega)) (fun i hi => hg i (by omega))
    let prev : Sig n := fun v => decide (bitsVal (fun i => f i v) m ≠ bitsVal (fun i => g i v) m)
    have hxr : Build (A ∪ {prev}) {xr (f m) (g m)} 4 :=
      xorG (Or.inl (hf m (by omega))) (Or.inl (hg m (by omega)))
    have hor : Build (A ∪ ({prev} ∪ {xr (f m) (g m)})) {orS prev (xr (f m) (g m))} 1 :=
      orG (Or.inr (Or.inl rfl)) (Or.inr (Or.inr rfl))
    have he : orS prev (xr (f m) (g m)) =
        (fun v => decide (bitsVal (fun i => f i v) (m + 1) ≠ bitsVal (fun i => g i v) (m + 1))) := by
      funext v
      have h1 := bitsVal_lt (fun i => f i v) m
      have h2 := bitsVal_lt (fun i => g i v) m
      apply Bool.eq_iff_iff.mpr
      simp only [orS, prev, xr, bitsVal, Bool.or_eq_true, decide_eq_true_eq]
      rcases Bool.eq_false_or_eq_true (f m v) with hf' | hf' <;>
        rcases Bool.eq_false_or_eq_true (g m v) with hg' | hg' <;>
        simp [hf', hg'] <;> omega
    have htot := seq (seq hprev hxr) hor
    rw [he] at htot
    exact relax htot le_rfl (Set.singleton_subset_iff.mpr (Or.inr rfl)) (by omega)

theorem eqWordG {A : Set (Sig n)} (f g : Nat → Sig n) (m : Nat)
    (hf : ∀ i < m, f i ∈ A) (hg : ∀ i < m, g i ∈ A) (hfalse : (fun _ => false) ∈ A) :
    Build A {fun v => decide (bitsVal (fun i => f i v) m = bitsVal (fun i => g i v) m)} (5 * m + 1) := by
  have hne := neWordG f g m hf hg hfalse
  let neS : Sig n := fun v => decide (bitsVal (fun i => f i v) m ≠ bitsVal (fun i => g i v) m)
  have hnt : Build (A ∪ {neS}) {nt neS} 1 := notG (Or.inr rfl)
  have he : nt neS = (fun v => decide (bitsVal (fun i => f i v) m = bitsVal (fun i => g i v) m)) := by
    funext v
    simp only [nt, neS]
    by_cases h : bitsVal (fun i => f i v) m = bitsVal (fun i => g i v) m <;> simp [h]
  have htot := seq hne hnt
  rw [he] at htot
  exact relax htot le_rfl (Set.singleton_subset_iff.mpr (Or.inr rfl)) le_rfl

def carryRec (f g : Nat → Bool) : Nat → Bool
  | 0 => false
  | m + 1 => (f m && g m) || (carryRec f g m && xor (f m) (g m))

def sumBitRec (f g : Nat → Bool) (m i : Nat) : Bool :=
  if i < m then xor (xor (f i) (g i)) (carryRec f g i)
  else if i = m then carryRec f g m
  else false

theorem bitsVal_addWord (f g : Nat → Bool) : ∀ m,
    bitsVal (sumBitRec f g m) (m + 1) = bitsVal f m + bitsVal g m := by
  have haux : ∀ m, bitsVal (fun i => xor (xor (f i) (g i)) (carryRec f g i)) m +
      (if carryRec f g m then 2 ^ m else 0) = bitsVal f m + bitsVal g m := by
    intro m
    induction m with
    | zero => simp [bitsVal, carryRec]
    | succ m ih =>
      simp only [bitsVal, carryRec]
      have hpow : 2 ^ (m + 1) = 2 ^ m + 2 ^ m := by rw [Nat.pow_succ]; omega
      rcases Bool.eq_false_or_eq_true (f m) with hf' | hf' <;>
        rcases Bool.eq_false_or_eq_true (g m) with hg' | hg' <;>
        rcases Bool.eq_false_or_eq_true (carryRec f g m) with hc' | hc' <;>
        simp [hf', hg', hc'] at ih ⊢ <;> omega
  intro m
  simp only [bitsVal]
  have hcon : bitsVal (sumBitRec f g m) m =
      bitsVal (fun i => xor (xor (f i) (g i)) (carryRec f g i)) m :=
    bitsVal_congr _ _ m (fun i hi => by simp [sumBitRec, hi])
  have htop : sumBitRec f g m m = carryRec f g m := by simp [sumBitRec]
  rw [hcon, htop]
  exact haux m

theorem addWordG {A : Set (Sig n)} (f g : Nat → Sig n) (m : Nat)
    (hf : ∀ i < m, f i ∈ A) (hg : ∀ i < m, g i ∈ A) (hfalse : (fun _ => false) ∈ A) :
    Build A {h | ∃ i < m + 1, h = fun v => sumBitRec (fun j => f j v) (fun j => g j v) m i}
      (12 * m) := by
  have hstep : ∀ t ≤ m, Build A
      ({fun v => carryRec (fun j => f j v) (fun j => g j v) t} ∪
       {h | ∃ i < t, h = fun v => xor (xor (f i v) (g i v)) (carryRec (fun j => f j v) (fun j => g j v) i)})
      (12 * t) := by
    intro t
    induction t with
    | zero =>
      intro _
      refine relax (idle (A := A) ?_) le_rfl le_rfl (by omega)
      rintro h (rfl | ⟨i, hi, _⟩)
      · exact hfalse
      · omega
    | succ t ih =>
      intro ht
      have Hprev := ih (by omega)
      let Bprev :=
        {fun v => carryRec (fun j => f j v) (fun j => g j v) t} ∪
        {h | ∃ i < t, h = fun v => xor (xor (f i v) (g i v)) (carryRec (fun j => f j v) (fun j => g j v) i)}
      let A0 := A ∪ Bprev
      let cSig : Sig n := fun v => carryRec (fun j => f j v) (fun j => g j v) t
      have hc : cSig ∈ A0 := Or.inr (Or.inl rfl)
      have hft : f t ∈ A0 := Or.inl (hf t (by omega))
      have hgt : g t ∈ A0 := Or.inl (hg t (by omega))
      have Hx1 : Build A0 {xr (f t) (g t)} 4 := xorG hft hgt
      have Hsum : Build (A0 ∪ {xr (f t) (g t)}) {xr (xr (f t) (g t)) cSig} 4 :=
        xorG (Or.inr rfl) (Or.inl hc)
      have Hab : Build (A0 ∪ ({xr (f t) (g t)} ∪ {xr (xr (f t) (g t)) cSig})) {an (f t) (g t)} 1 :=
        andG (Or.inl hft) (Or.inl hgt)
      have Hcx : Build (A0 ∪ (({xr (f t) (g t)} ∪ {xr (xr (f t) (g t)) cSig}) ∪ {an (f t) (g t)}))
          {an cSig (xr (f t) (g t))} 1 :=
        andG (Or.inl hc) (Or.inr (Or.inl (Or.inl rfl)))
      have Hcnext : Build (A0 ∪ ((({xr (f t) (g t)} ∪ {xr (xr (f t) (g t)) cSig}) ∪ {an (f t) (g t)}) ∪
          {an cSig (xr (f t) (g t))})) {orS (an (f t) (g t)) (an cSig (xr (f t) (g t)))} 1 :=
        orG (Or.inr (Or.inl (Or.inr rfl))) (Or.inr (Or.inr rfl))
      have Htot := seq Hprev (seq (seq (seq (seq Hx1 Hsum) Hab) Hcx) Hcnext)
      refine relax Htot le_rfl ?_ (by omega)
      rintro h (rfl | ⟨i, hi, rfl⟩)
      · exact Or.inr (Or.inr rfl)
      · by_cases hit : i = t
        · subst hit
          exact Or.inr (Or.inl (Or.inl (Or.inl (Or.inr rfl))))
        · exact Or.inl (Or.inr ⟨i, by omega, rfl⟩)
  have hmain := hstep m (Nat.le_refl m)
  refine relax hmain le_rfl ?_ le_rfl
  rintro h ⟨i, hi, rfl⟩
  by_cases him : i < m
  · right
    refine ⟨i, him, ?_⟩
    funext v; simp [sumBitRec, him]
  · have heq : i = m := by omega
    subst heq
    left
    funext v; simp [sumBitRec]

def popBits (b : Nat → Bool) (off : Nat) : Nat → Nat → Bool
  | 0, i => if i = 0 then b off else false
  | k + 1, i => sumBitRec (popBits b off k) (popBits b (off + 2 ^ k) k) (k + 1) i

theorem bitsVal_popBits (b : Nat → Bool) : ∀ k off,
    bitsVal (popBits b off k) (k + 1) =
      ((List.range (2 ^ k)).map (fun j => b (off + j))).count true
  | 0, off => by
    simp only [bitsVal, popBits, ↓reduceIte, Nat.pow_zero, List.range_one, List.map_cons,
      List.map_nil, Nat.add_zero]
    cases b off <;> rfl
  | k + 1, off => by
    have hL := bitsVal_popBits b k off
    have hR := bitsVal_popBits b k (off + 2 ^ k)
    have hadd := bitsVal_addWord (popBits b off k) (popBits b (off + 2 ^ k) k) (k + 1)
    change bitsVal (sumBitRec (popBits b off k) (popBits b (off + 2 ^ k) k) (k + 1)) (k + 2) = _
    rw [hadd, hL, hR]
    have hpow : 2 ^ (k + 1) = 2 ^ k + 2 ^ k := by rw [Nat.pow_succ]; omega
    rw [hpow, List.range_add, List.map_append, List.count_append]
    congr 1
    rw [List.map_map]
    congr 1
    apply List.map_congr_left
    intro j _
    simp [Nat.add_assoc]

theorem popCount_budget_le (k : Nat) : 12 * (k + 2) ≤ 24 * 2 ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Nat.pow_succ]
    omega

theorem popCountG_aux {A : Set (Sig n)} (b : Nat → Sig n) (hfalse : (fun _ => false) ∈ A) :
    ∀ k off, (∀ j < 2 ^ k, b (off + j) ∈ A) →
      Build A {h | ∃ i < k + 1, h = fun v => popBits (fun j => b j v) off k i}
        (24 * 2 ^ k - 12 * (k + 2))
  | 0, off, hb => by
    refine relax (idle ?_) le_rfl le_rfl (by omega)
    rintro h ⟨i, hi, rfl⟩
    have hi0 : i = 0 := by omega
    subst hi0
    have he : (fun v => popBits (fun j => b j v) off 0 0) = b (off + 0) := by
      funext v; simp [popBits]
    rw [he]
    exact hb 0 (by simp)
  | k + 1, off, hb => by
    have hL := popCountG_aux b hfalse k off (fun j hj => hb j (by rw [Nat.pow_succ]; omega))
    have hR := popCountG_aux b hfalse k (off + 2 ^ k) (fun j hj => by
      have := hb (2 ^ k + j) (by rw [Nat.pow_succ]; omega)
      simpa [Nat.add_assoc] using this)
    let BL := {h | ∃ i < k + 1, h = fun v => popBits (fun j => b j v) off k i}
    let BR := {h | ∃ i < k + 1, h = fun v => popBits (fun j => b j v) (off + 2 ^ k) k i}
    have hR' := relax hR (C := A ∪ BL) Set.subset_union_left le_rfl le_rfl
    have hLR := seq hL hR'
    have hAdd : Build (A ∪ (BL ∪ BR))
        {h | ∃ i < k + 2, h = fun v => popBits (fun j => b j v) off (k + 1) i}
        (12 * (k + 1)) :=
      addWordG (fun i v => popBits (fun j => b j v) off k i)
        (fun i v => popBits (fun j => b j v) (off + 2 ^ k) k i) (k + 1)
        (fun i hi => Or.inr (Or.inl ⟨i, hi, rfl⟩))
        (fun i hi => Or.inr (Or.inr ⟨i, hi, rfl⟩))
        (Or.inl hfalse)
    have hble := popCount_budget_le k
    have hpow : 2 ^ (k + 1) = 2 ^ k * 2 := Nat.pow_succ 2 k
    refine relax (seq hLR hAdd) le_rfl Set.subset_union_right ?_
    omega

theorem popCountG {A : Set (Sig n)} (b : Nat → Sig n) (hfalse : (fun _ => false) ∈ A)
    (k off : Nat) (hb : ∀ j < 2 ^ k, b (off + j) ∈ A) :
    Build A {h | ∃ i < k + 1, h = fun v => popBits (fun j => b j v) off k i}
      (24 * 2 ^ k) :=
  relax (popCountG_aux b hfalse k off hb) le_rfl le_rfl (Nat.sub_le _ _)

end BuildComb

section BitonicSec

def bitonicMerge (off : Nat) : Nat → Bool → List (Nat × Nat × Bool)
  | 0, _ => []
  | k + 1, asc =>
    let h := 2 ^ k
    let stage := (List.range h).map (fun i => (off + i, off + h + i, asc))
    stage ++ bitonicMerge off k asc ++ bitonicMerge (off + h) k asc

def bitonicSort (off : Nat) : Nat → Bool → List (Nat × Nat × Bool)
  | 0, _ => []
  | k + 1, asc =>
    let h := 2 ^ k
    bitonicSort off k true ++ bitonicSort (off + h) k false ++ bitonicMerge off (k + 1) asc

theorem bitonicMerge_length (off : Nat) : ∀ k asc,
    2 * (bitonicMerge off k asc).length = k * 2 ^ k
  | 0, _ => by simp [bitonicMerge]
  | k + 1, asc => by
    simp only [bitonicMerge, List.length_append, List.length_map, List.length_range]
    have h1 := bitonicMerge_length off k asc
    have h2 := bitonicMerge_length (off + 2 ^ k) k asc
    have he : (k + 1) * 2 ^ (k + 1) = 2 * 2 ^ k + 2 * (k * 2 ^ k) := by
      rw [Nat.pow_succ, Nat.succ_mul]
      rw [← Nat.mul_assoc k (2 ^ k) 2, Nat.mul_comm (k * 2 ^ k) 2, Nat.mul_comm (2 ^ k) 2, Nat.add_comm]
    omega

theorem bitonicSort_length (off : Nat) : ∀ k asc,
    4 * (bitonicSort off k asc).length = k * (k + 1) * 2 ^ k
  | 0, _ => by simp [bitonicSort]
  | k + 1, asc => by
    simp only [bitonicSort, List.length_append]
    have h1 := bitonicSort_length off k true
    have h2 := bitonicSort_length (off + 2 ^ k) k false
    have hm := bitonicMerge_length off (k + 1) asc
    have he : (k + 1) * (k + 1 + 1) * 2 ^ (k + 1) =
        2 * (k * (k + 1) * 2 ^ k) + 2 * ((k + 1) * 2 ^ (k + 1)) := by
      rw [Nat.pow_succ]
      have e1 : k * (k + 1) * 2 ^ k = (k + 1) * k * 2 ^ k := by rw [Nat.mul_comm k (k + 1)]
      have e2 : (k + 1) * (k + 2) * (2 ^ k * 2) =
          (k + 1) * k * (2 ^ k * 2) + (k + 1) * 2 * (2 ^ k * 2) := by
        rw [Nat.mul_add (k + 1) k 2, Nat.add_mul]
      rw [e2]
      have e3 : 2 * (k * (k + 1) * 2 ^ k) = (k + 1) * k * (2 ^ k * 2) := by
        rw [e1, Nat.mul_comm 2, Nat.mul_assoc]
      have e4 : 2 * ((k + 1) * (2 ^ k * 2)) = (k + 1) * 2 * (2 ^ k * 2) := by
        rw [← Nat.mul_assoc 2 (k + 1), Nat.mul_comm 2 (k + 1)]
      omega
    omega

theorem bitonicMerge_mem (off : Nat) : ∀ k asc c,
    c ∈ bitonicMerge off k asc → off ≤ c.1 ∧ c.1 < c.2.1 ∧ c.2.1 < off + 2 ^ k
  | 0, _, c, hc => by simp [bitonicMerge] at hc
  | k + 1, asc, c, hc => by
    simp only [bitonicMerge, List.mem_append, List.mem_map, List.mem_range] at hc
    rcases hc with (⟨i, hi, rfl⟩ | hc) | hc
    · dsimp only
      rw [Nat.pow_succ]
      omega
    · have h := bitonicMerge_mem off k asc c hc
      rw [Nat.pow_succ]
      omega
    · have h := bitonicMerge_mem (off + 2 ^ k) k asc c hc
      rw [Nat.pow_succ]
      omega

theorem bitonicSort_mem (off : Nat) : ∀ k asc c,
    c ∈ bitonicSort off k asc → off ≤ c.1 ∧ c.1 < c.2.1 ∧ c.2.1 < off + 2 ^ k
  | 0, _, c, hc => by simp [bitonicSort] at hc
  | k + 1, asc, c, hc => by
    simp only [bitonicSort, List.mem_append] at hc
    rcases hc with (hc | hc) | hc
    · have h := bitonicSort_mem off k true c hc
      rw [Nat.pow_succ]
      omega
    · have h := bitonicSort_mem (off + 2 ^ k) k false c hc
      rw [Nat.pow_succ]
      omega
    · exact bitonicMerge_mem off (k + 1) asc c hc

def swapBit (k1 k2 : Nat) (asc : Bool) : Bool :=
  if asc then decide (k2 < k1) else decide (k1 < k2)

def applySwap {α : Type*} (u v : Nat) (sw : Bool) (st : Nat → α) : Nat → α :=
  fun idx =>
    if sw then
      if idx = u then st v else if idx = v then st u else st idx
    else st idx

theorem applySwap_invol {α : Type*} (u v : Nat) (sw : Bool) (st : Nat → α) :
    applySwap u v sw (applySwap u v sw st) = st := by
  funext idx
  simp only [applySwap]
  cases sw with
  | false => rfl
  | true =>
    simp only [↓reduceIte]
    by_cases h1 : idx = u
    · subst h1
      by_cases huv : idx = v
      · subst huv; simp
      · simp [Ne.symm huv]
    · by_cases h2 : idx = v
      · subst h2; simp [h1]
      · simp [h1, h2]

theorem applySwap_comp {α β : Type*} (u v : Nat) (sw : Bool) (f : α → β) (st : Nat → α) :
    applySwap u v sw (fun idx => f (st idx)) = fun idx => f (applySwap u v sw st idx) := by
  funext idx
  simp only [applySwap]
  cases sw <;> simp only [Bool.false_eq_true, ↓reduceIte]
  by_cases h1 : idx = u
  · simp [h1]
  · by_cases h2 : idx = v
    · subst h2; simp [h1]
    · simp [h1, h2]

def runNet {α : Type*} (key : α → Nat) : List (Nat × Nat × Bool) → (Nat → α) → (Nat → α)
  | [], st => st
  | (u, v, asc) :: rest, st =>
    let sw := swapBit (key (st u)) (key (st v)) asc
    runNet key rest (applySwap u v sw st)

theorem runNet_append {α : Type*} (key : α → Nat) (n1 n2 : List (Nat × Nat × Bool)) (st : Nat → α) :
    runNet key (n1 ++ n2) st = runNet key n2 (runNet key n1 st) := by
  induction n1 generalizing st with
  | nil => rfl
  | cons c rest ih =>
    rcases c with ⟨u, v, asc⟩
    simp only [List.cons_append, runNet]
    exact ih _

def netSwaps {α : Type*} (key : α → Nat) : List (Nat × Nat × Bool) → (Nat → α) → List (Nat × Nat × Bool)
  | [], _ => []
  | (u, v, asc) :: rest, st =>
    let sw := swapBit (key (st u)) (key (st v)) asc
    (u, v, sw) :: netSwaps key rest (applySwap u v sw st)

def replaySwaps {β : Type*} : List (Nat × Nat × Bool) → (Nat → β) → (Nat → β)
  | [], st => st
  | (u, v, sw) :: rest, st => replaySwaps rest (applySwap u v sw st)

theorem replaySwaps_append {β : Type*} (s1 s2 : List (Nat × Nat × Bool)) (st : Nat → β) :
    replaySwaps (s1 ++ s2) st = replaySwaps s2 (replaySwaps s1 st) := by
  induction s1 generalizing st with
  | nil => rfl
  | cons c rest ih =>
    rcases c with ⟨u, v, sw⟩
    simp only [List.cons_append, replaySwaps]
    exact ih _

theorem replaySwaps_comp {α β : Type*} (sws : List (Nat × Nat × Bool)) (f : α → β) (st : Nat → α) :
    replaySwaps sws (fun idx => f (st idx)) = fun idx => f (replaySwaps sws st idx) := by
  induction sws generalizing st with
  | nil => rfl
  | cons c rest ih =>
    rcases c with ⟨u, v, sw⟩
    simp only [replaySwaps]
    rw [applySwap_comp]
    exact ih _

theorem replaySwaps_reverse_cancel {β : Type*} (sws : List (Nat × Nat × Bool)) (st : Nat → β) :
    replaySwaps sws.reverse (replaySwaps sws st) = st := by
  induction sws generalizing st with
  | nil => rfl
  | cons c rest ih =>
    rcases c with ⟨u, v, sw⟩
    simp only [List.reverse_cons, replaySwaps, replaySwaps_append]
    rw [ih, applySwap_invol]

theorem runNet_eq_replay {α : Type*} (key : α → Nat) (net : List (Nat × Nat × Bool)) (st : Nat → α) :
    runNet key net st = replaySwaps (netSwaps key net st) st := by
  induction net generalizing st with
  | nil => rfl
  | cons c rest ih =>
    rcases c with ⟨u, v, asc⟩
    simp only [runNet, netSwaps, replaySwaps]
    exact ih _

theorem runNet_unchanged {α : Type*} (key : α → Nat) (net : List (Nat × Nat × Bool))
    (st : Nat → α) (idx : Nat) (h : ∀ c ∈ net, idx ≠ c.1 ∧ idx ≠ c.2.1) :
    runNet key net st idx = st idx := by
  induction net generalizing st with
  | nil => rfl
  | cons c rest ih =>
    rcases c with ⟨u, v, asc⟩
    have hc := h (u, v, asc) List.mem_cons_self
    simp only [runNet]
    rw [ih _ (fun c' hc' => h c' (List.mem_cons_of_mem _ hc'))]
    simp only [applySwap]
    cases swapBit (key (st u)) (key (st v)) asc
    · rfl
    · simp only [↓reduceIte, hc.1, hc.2]

theorem runNet_mono_map {α : Type*} (key : α → Nat) (f : Nat → Bool)
    (hf : ∀ x y, x ≤ y → f x = true → f y = true)
    (net : List (Nat × Nat × Bool)) (st : Nat → α) :
    (fun idx => f (key (runNet key net st idx))) =
      runNet (fun b : Bool => b.toNat) net (fun idx => f (key (st idx))) := by
  induction net generalizing st with
  | nil => rfl
  | cons c rest ih =>
    rcases c with ⟨u, v, asc⟩
    simp only [runNet]
    rw [ih]
    congr 1
    funext idx
    simp only [applySwap, swapBit]
    have hpair :
        (f (key (if (if asc then decide (key (st v) < key (st u)) else decide (key (st u) < key (st v)))
          then st v else st u)) =
         if (if asc then decide ((f (key (st v))).toNat < (f (key (st u))).toNat)
             else decide ((f (key (st u))).toNat < (f (key (st v))).toNat))
          then f (key (st v)) else f (key (st u))) ∧
        (f (key (if (if asc then decide (key (st v) < key (st u)) else decide (key (st u) < key (st v)))
          then st u else st v)) =
         if (if asc then decide ((f (key (st v))).toNat < (f (key (st u))).toNat)
             else decide ((f (key (st u))).toNat < (f (key (st v))).toNat))
          then f (key (st u)) else f (key (st v))) := by
      cases asc <;> simp only [Bool.false_eq_true, ↓reduceIte]
      · by_cases hlt : key (st u) < key (st v)
        · have hle : key (st u) ≤ key (st v) := Nat.le_of_lt hlt
          simp only [hlt, decide_true, ↓reduceIte]
          cases hfu : f (key (st u)) <;> cases hfv : f (key (st v))
          · simp
          · simp
          · exact absurd (hf _ _ hle hfu) (by rw [hfv]; decide)
          · simp
        · have hle : key (st v) ≤ key (st u) := Nat.le_of_not_lt hlt
          simp only [hlt, decide_false, Bool.false_eq_true, ↓reduceIte]
          cases hfu : f (key (st u)) <;> cases hfv : f (key (st v))
          · simp
          · exact absurd (hf _ _ hle hfv) (by rw [hfu]; decide)
          · simp
          · simp
      · by_cases hlt : key (st v) < key (st u)
        · have hle : key (st v) ≤ key (st u) := Nat.le_of_lt hlt
          simp only [hlt, decide_true, ↓reduceIte]
          cases hfu : f (key (st u)) <;> cases hfv : f (key (st v))
          · simp
          · exact absurd (hf _ _ hle hfv) (by rw [hfu]; decide)
          · simp
          · simp
        · have hle : key (st u) ≤ key (st v) := Nat.le_of_not_lt hlt
          simp only [hlt, decide_false, Bool.false_eq_true, ↓reduceIte]
          cases hfu : f (key (st u)) <;> cases hfv : f (key (st v))
          · simp
          · simp
          · exact absurd (hf _ _ hle hfu) (by rw [hfv]; decide)
          · simp
    by_cases h1 : idx = u
    · subst h1
      have hl := hpair.1
      by_cases hs1 : (if asc then decide (key (st v) < key (st idx)) else decide (key (st idx) < key (st v))) = true <;>
        by_cases hs2 : (if asc then decide ((f (key (st v))).toNat < (f (key (st idx))).toNat)
          else decide ((f (key (st idx))).toNat < (f (key (st v))).toNat)) = true <;>
        simp only [hs1, hs2, ↓reduceIte] at hl ⊢ <;> exact hl
    · by_cases h2 : idx = v
      · subst h2
        have hr := hpair.2
        by_cases hs1 : (if asc then decide (key (st idx) < key (st u)) else decide (key (st u) < key (st idx))) = true <;>
          by_cases hs2 : (if asc then decide ((f (key (st idx))).toNat < (f (key (st u))).toNat)
            else decide ((f (key (st u))).toNat < (f (key (st idx))).toNat)) = true <;>
          simp only [hs1, hs2, h1, ↓reduceIte] at hr ⊢ <;> exact hr
      · by_cases hs1 : (if asc then decide (key (st v) < key (st u)) else decide (key (st u) < key (st v))) = true <;>
          by_cases hs2 : (if asc then decide ((f (key (st v))).toNat < (f (key (st u))).toNat)
            else decide ((f (key (st u))).toNat < (f (key (st v))).toNat)) = true <;>
          simp only [hs1, hs2, h1, h2, Bool.false_eq_true, ↓reduceIte]

def IsBitonic (off len : Nat) (g : Nat → Bool) : Prop :=
  ∃ s e, s ≤ e ∧ e ≤ len ∧
    ((∀ i < len, g (off + i) = true ↔ s ≤ i ∧ i < e) ∨
     (∀ i < len, g (off + i) = false ↔ s ≤ i ∧ i < e))

def IsSortedBool (off len : Nat) (asc : Bool) (g : Nat → Bool) : Prop :=
  ∀ i j, i ≤ j → j < len →
    if asc then (g (off + i) = true → g (off + j) = true)
    else (g (off + j) = true → g (off + i) = true)

theorem runNet_bool_const (net : List (Nat × Nat × Bool)) (off len : Nat) (v : Bool)
    (g : Nat → Bool)
    (hnet : ∀ c ∈ net, off ≤ c.1 ∧ c.1 < off + len ∧ off ≤ c.2.1 ∧ c.2.1 < off + len)
    (hg : ∀ i < len, g (off + i) = v) :
    ∀ i < len, runNet (fun b : Bool => b.toNat) net g (off + i) = v := by
  induction net generalizing g with
  | nil => exact hg
  | cons c rest ih =>
    rcases c with ⟨x, y, asc⟩
    have hc := hnet (x, y, asc) List.mem_cons_self
    dsimp only at hc
    simp only [runNet]
    apply ih _ (fun c' hc' => hnet c' (List.mem_cons_of_mem _ hc'))
    intro i hi
    simp only [applySwap]
    have hx : g x = v := by
      have e : off + (x - off) = x := by omega
      rw [← e]; exact hg (x - off) (by omega)
    have hy : g y = v := by
      have e : off + (y - off) = y := by omega
      rw [← e]; exact hg (y - off) (by omega)
    cases swapBit (g x).toNat (g y).toNat asc
    · exact hg i hi
    · simp only [↓reduceIte]
      by_cases h1 : off + i = x
      · simp [h1, hy]
      · by_cases h2 : off + i = y
        · simp only [h1, ↓reduceIte]; simp only [h2, ↓reduceIte]; exact hx
        · simp [h1, h2, hg i hi]

theorem stage_eval (off h : Nat) (asc : Bool) (g : Nat → Bool) :
    ∀ m ≤ h, ∀ idx,
      let stage := (List.range m).map (fun i => (off + i, off + h + i, asc))
      runNet (fun b : Bool => b.toNat) stage g idx =
        if off ≤ idx ∧ idx < off + m then
          if asc then g idx && g (idx + h) else g idx || g (idx + h)
        else if off + h ≤ idx ∧ idx < off + h + m then
          if asc then g (idx - h) || g idx else g (idx - h) && g idx
        else g idx := by
  intro m
  induction m with
  | zero =>
    intro _ idx
    dsimp only
    simp only [List.range_zero, List.map_nil, runNet, Nat.add_zero]
    simp only [show ¬ (off ≤ idx ∧ idx < off) by omega,
      show ¬ (off + h ≤ idx ∧ idx < off + h) by omega, ↓reduceIte]
  | succ m ih =>
    intro hm idx
    dsimp only
    rw [List.range_succ, List.map_append, List.map_cons, List.map_nil, runNet_append]
    simp only [runNet, applySwap, swapBit]
    have h1 := ih (by omega) (off + m)
    have h2 := ih (by omega) (off + h + m)
    have h3 := ih (by omega) idx
    have h1' : runNet (fun b : Bool => b.toNat) ((List.range m).map (fun i => (off + i, off + h + i, asc))) g (off + m) = g (off + m) := by
      rw [h1]; simp only [show ¬ (off ≤ off + m ∧ off + m < off + m) by omega,
        show ¬ (off + h ≤ off + m ∧ off + m < off + h + m) by omega, ↓reduceIte]
    have h2' : runNet (fun b : Bool => b.toNat) ((List.range m).map (fun i => (off + i, off + h + i, asc))) g (off + h + m) = g (off + h + m) := by
      rw [h2]; simp only [show ¬ (off ≤ off + h + m ∧ off + h + m < off + m) by omega,
        show ¬ (off + h ≤ off + h + m ∧ off + h + m < off + h + m) by omega, ↓reduceIte]
    rw [h1', h2']
    by_cases hidx1 : idx = off + m
    · subst hidx1
      rw [h1']
      have e1 : off + m + h = off + h + m := by omega
      have hc1 : off ≤ off + m ∧ off + m < off + (m + 1) := by omega
      simp only [hc1, ↓reduceIte, e1]
      cases asc <;> cases g (off + m) <;> cases g (off + h + m) <;> rfl
    · by_cases hidx2 : idx = off + h + m
      · subst hidx2
        rw [h2']
        have e1 : off + h + m - h = off + m := by omega
        have hc1 : ¬ (off ≤ off + h + m ∧ off + h + m < off + (m + 1)) := by omega
        have hc2 : off + h ≤ off + h + m ∧ off + h + m < off + h + (m + 1) := by omega
        have hne : off + h + m ≠ off + m := by omega
        simp only [hc1, hc2, hne, ↓reduceIte, e1]
        cases asc <;> cases g (off + m) <;> cases g (off + h + m) <;> rfl
      · have hne1 : ¬ (idx = off + m) := hidx1
        have hne2 : ¬ (idx = off + h + m) := hidx2
        have heq : (if (if asc then decide ((g (off + h + m)).toNat < (g (off + m)).toNat)
            else decide ((g (off + m)).toNat < (g (off + h + m)).toNat)) then
            if idx = off + m then g (off + h + m) else if idx = off + h + m then g (off + m)
            else runNet (fun b : Bool => b.toNat) ((List.range m).map (fun i => (off + i, off + h + i, asc))) g idx
          else runNet (fun b : Bool => b.toNat) ((List.range m).map (fun i => (off + i, off + h + i, asc))) g idx) =
          runNet (fun b : Bool => b.toNat) ((List.range m).map (fun i => (off + i, off + h + i, asc))) g idx := by
          cases (if asc then decide ((g (off + h + m)).toNat < (g (off + m)).toNat)
            else decide ((g (off + m)).toNat < (g (off + h + m)).toNat)) <;> simp [hne1, hne2]
        rw [heq, h3]
        by_cases c1 : off ≤ idx ∧ idx < off + m
        · have c1' : off ≤ idx ∧ idx < off + (m + 1) := by omega
          simp only [c1, c1', and_self, ↓reduceIte]
        · by_cases c2 : off + h ≤ idx ∧ idx < off + h + m
          · have c1' : ¬ (off ≤ idx ∧ idx < off + (m + 1)) := by omega
            have c2' : off + h ≤ idx ∧ idx < off + h + (m + 1) := by omega
            simp only [c1, c2, c1', c2', ↓reduceIte]
          · have c1' : ¬ (off ≤ idx ∧ idx < off + (m + 1)) := by omega
            have c2' : ¬ (off + h ≤ idx ∧ idx < off + h + (m + 1)) := by omega
            simp only [c1, c2, c1', c2', ↓reduceIte]

theorem bitonic_split_true (off h : Nat) (g : Nat → Bool) (hb : IsBitonic off (2 * h) g) :
    let lo : Nat → Bool := fun idx => g idx && g (idx + h)
    let hi : Nat → Bool := fun idx => g (idx - h) || g idx
    IsBitonic off h lo ∧ IsBitonic (off + h) h hi ∧
      ((∀ i < h, lo (off + i) = false) ∨ (∀ i < h, hi (off + h + i) = true)) := by
  intro lo hi
  rcases hb with ⟨s, e, hse, he2h, htr | hfa⟩
  · by_cases hlen : e - s ≤ h
    · have hlo_all : ∀ i < h, lo (off + i) = false := by
        intro i hi_lt
        dsimp only [lo]
        cases h1 : g (off + i) with
        | false => rfl
        | true =>
          have hi1 := (htr i (by omega)).mp h1
          cases h2 : g (off + i + h) with
          | false => rfl
          | true =>
            have e1 : off + i + h = off + (h + i) := by omega
            rw [e1] at h2
            have hi2 := (htr (h + i) (by omega)).mp h2
            omega
      refine ⟨⟨0, 0, Nat.le_refl 0, Nat.zero_le h, Or.inl (fun i hi_lt => by rw [hlo_all i hi_lt]; simp)⟩,
        ?_, Or.inl hlo_all⟩
      have hhi_iff : ∀ i < h, hi (off + h + i) = true ↔ (s ≤ i ∧ i < e) ∨ (s ≤ h + i ∧ h + i < e) := by
        intro i hi_lt
        dsimp only [hi]
        have e1 : off + h + i - h = off + i := by omega
        have e2 : off + h + i = off + (h + i) := by omega
        rw [e1, e2, Bool.or_eq_true, htr i (by omega), htr (h + i) (by omega)]
      by_cases heh : e ≤ h
      · exact ⟨s, e, hse, heh, Or.inl (fun i hi_lt => by rw [hhi_iff i hi_lt]; omega)⟩
      · by_cases hhs : h ≤ s
        · exact ⟨s - h, e - h, by omega, by omega, Or.inl (fun i hi_lt => by rw [hhi_iff i hi_lt]; omega)⟩
        · refine ⟨e - h, s, by omega, by omega, Or.inr (fun i hi_lt => ?_)⟩
          have h1 := hhi_iff i hi_lt
          cases hval : hi (off + h + i) with
          | false =>
            have hnt : ¬ ((s ≤ i ∧ i < e) ∨ (s ≤ h + i ∧ h + i < e)) := fun hp => by
              have := h1.mpr hp; rw [hval] at this; cases this
            constructor
            · intro _; omega
            · intro _; rfl
          | true =>
            have ht := h1.mp hval
            constructor
            · intro hc; cases hc
            · intro hr; omega
    · have hhi_all : ∀ i < h, hi (off + h + i) = true := by
        intro i hi_lt
        dsimp only [hi]
        have e1 : off + h + i - h = off + i := by omega
        have e2 : off + h + i = off + (h + i) := by omega
        rw [e1, e2, Bool.or_eq_true, htr i (by omega), htr (h + i) (by omega)]
        omega
      refine ⟨⟨s, e - h, by omega, by omega, Or.inl (fun i hi_lt => ?_)⟩,
        ⟨0, h, Nat.zero_le h, Nat.le_refl h, Or.inl (fun i hi_lt => by rw [hhi_all i hi_lt]; simp [hi_lt])⟩,
        Or.inr hhi_all⟩
      dsimp only [lo]
      have e1 : off + i + h = off + (h + i) := by omega
      rw [e1, Bool.and_eq_true, htr i (by omega), htr (h + i) (by omega)]
      omega
  · by_cases hlen : e - s ≤ h
    · have hhi_all : ∀ i < h, hi (off + h + i) = true := by
        intro i hi_lt
        dsimp only [hi]
        have e1 : off + h + i - h = off + i := by omega
        have e2 : off + h + i = off + (h + i) := by omega
        rw [e1, e2]
        cases h1 : g (off + i) with
        | true => rfl
        | false =>
          have hi1 := (hfa i (by omega)).mp h1
          cases h2 : g (off + (h + i)) with
          | true => rfl
          | false =>
            have hi2 := (hfa (h + i) (by omega)).mp h2
            omega
      refine ⟨?_, ⟨0, h, Nat.zero_le h, Nat.le_refl h, Or.inl (fun i hi_lt => by rw [hhi_all i hi_lt]; simp [hi_lt])⟩,
        Or.inr hhi_all⟩
      have hlo_iff : ∀ i < h, lo (off + i) = false ↔ (s ≤ i ∧ i < e) ∨ (s ≤ h + i ∧ h + i < e) := by
        intro i hi_lt
        dsimp only [lo]
        have e1 : off + i + h = off + (h + i) := by omega
        rw [e1, Bool.and_eq_false_iff, hfa i (by omega), hfa (h + i) (by omega)]
      by_cases heh : e ≤ h
      · exact ⟨s, e, hse, heh, Or.inr (fun i hi_lt => by rw [hlo_iff i hi_lt]; omega)⟩
      · by_cases hhs : h ≤ s
        · exact ⟨s - h, e - h, by omega, by omega, Or.inr (fun i hi_lt => by rw [hlo_iff i hi_lt]; omega)⟩
        · refine ⟨e - h, s, by omega, by omega, Or.inl (fun i hi_lt => ?_)⟩
          have h1 := hlo_iff i hi_lt
          cases hval : lo (off + i) with
          | true =>
            have hnf : ¬ ((s ≤ i ∧ i < e) ∨ (s ≤ h + i ∧ h + i < e)) := fun hp => by
              have := h1.mpr hp; rw [hval] at this; cases this
            constructor
            · intro _; omega
            · intro _; rfl
          | false =>
            have hf := h1.mp hval
            constructor
            · intro hc; cases hc
            · intro hr; omega
    · have hlo_all : ∀ i < h, lo (off + i) = false := by
        intro i hi_lt
        dsimp only [lo]
        have e1 : off + i + h = off + (h + i) := by omega
        rw [e1, Bool.and_eq_false_iff, hfa i (by omega), hfa (h + i) (by omega)]
        omega
      refine ⟨⟨0, 0, Nat.le_refl 0, Nat.zero_le h, Or.inl (fun i hi_lt => by rw [hlo_all i hi_lt]; simp)⟩,
        ⟨s, e - h, by omega, by omega, Or.inr (fun i hi_lt => ?_)⟩,
        Or.inl hlo_all⟩
      dsimp only [hi]
      have e1 : off + h + i - h = off + i := by omega
      have e2 : off + h + i = off + (h + i) := by omega
      rw [e1, e2, Bool.or_eq_false_iff, hfa i (by omega), hfa (h + i) (by omega)]
      omega

theorem bitonicMerge_sorted (off : Nat) : ∀ k asc (g : Nat → Bool),
    IsBitonic off (2 ^ k) g →
    IsSortedBool off (2 ^ k) asc (runNet (fun b : Bool => b.toNat) (bitonicMerge off k asc) g)
  | 0, asc, g, _ => by
    intro i j hij hj
    have hi0 : i = 0 := by omega
    have hj0 : j = 0 := by omega
    subst hi0; subst hj0
    cases asc <;> exact fun h => h
  | k + 1, asc, g, hb => by
    let h := 2 ^ k
    have h2 : 2 ^ (k + 1) = 2 * h := by dsimp [h]; rw [Nat.pow_succ, Nat.mul_comm]
    rw [h2] at hb ⊢
    simp only [bitonicMerge, runNet_append]
    let stage := (List.range h).map (fun i => (off + i, off + h + i, asc))
    let g1 := runNet (fun b : Bool => b.toNat) stage g
    let g2 := runNet (fun b : Bool => b.toNat) (bitonicMerge off k asc) g1
    let g3 := runNet (fun b : Bool => b.toNat) (bitonicMerge (off + h) k asc) g2
    change IsSortedBool off (2 * h) asc g3
    have hstage := stage_eval off h asc g h (Nat.le_refl h)
    have hg1_L : ∀ i < h, g1 (off + i) = if asc then g (off + i) && g (off + i + h) else g (off + i) || g (off + i + h) := by
      intro i hi_lt
      have hs := hstage (off + i)
      dsimp only at hs
      have hc1 : off ≤ off + i ∧ off + i < off + h := by omega
      simp only [hc1, and_self, ↓reduceIte] at hs
      exact hs
    have hg1_R : ∀ i < h, g1 (off + h + i) = if asc then g (off + h + i - h) || g (off + h + i) else g (off + h + i - h) && g (off + h + i) := by
      intro i hi_lt
      have hs := hstage (off + h + i)
      dsimp only at hs
      have hc1 : ¬ (off ≤ off + h + i ∧ off + h + i < off + h) := by omega
      have hc2 : off + h ≤ off + h + i ∧ off + h + i < off + h + h := by omega
      simp only [hc1, hc2, and_self, ↓reduceIte] at hs
      exact hs
    have hsp := bitonic_split_true off h g hb
    have hleft_bit : IsBitonic off h g1 := by
      cases asc with
      | true =>
        rcases hsp.1 with ⟨s, e, h1, h2', h3⟩
        refine ⟨s, e, h1, h2', ?_⟩
        rcases h3 with h3 | h3
        · left
          intro i hi_lt
          rw [hg1_L i hi_lt]
          exact h3 i hi_lt
        · right
          intro i hi_lt
          rw [hg1_L i hi_lt]
          exact h3 i hi_lt
      | false =>
        rcases hsp.2.1 with ⟨s, e, h1, h2', h3⟩
        refine ⟨s, e, h1, h2', ?_⟩
        rcases h3 with h3 | h3
        · left
          intro i hi_lt
          have e1 : off + h + i - h = off + i := by omega
          have e2 : off + h + i = off + i + h := by omega
          have h3' := h3 i hi_lt
          dsimp only at h3'
          rw [e1, e2] at h3'
          rw [hg1_L i hi_lt]
          exact h3'
        · right
          intro i hi_lt
          have e1 : off + h + i - h = off + i := by omega
          have e2 : off + h + i = off + i + h := by omega
          have h3' := h3 i hi_lt
          dsimp only at h3'
          rw [e1, e2] at h3'
          rw [hg1_L i hi_lt]
          exact h3'
    have hright_bit : IsBitonic (off + h) h g2 := by
      have hg2_eq : ∀ i < h, g2 (off + h + i) = g1 (off + h + i) := by
        intro i hi_lt
        apply runNet_unchanged
        intro c hc
        have hm := bitonicMerge_mem off k asc c hc
        dsimp only [h] at hi_lt ⊢
        omega
      cases asc with
      | true =>
        rcases hsp.2.1 with ⟨s, e, h1, h2', h3⟩
        refine ⟨s, e, h1, h2', ?_⟩
        rcases h3 with h3 | h3
        · left
          intro i hi_lt
          rw [hg2_eq i hi_lt, hg1_R i hi_lt]
          exact h3 i hi_lt
        · right
          intro i hi_lt
          rw [hg2_eq i hi_lt, hg1_R i hi_lt]
          exact h3 i hi_lt
      | false =>
        rcases hsp.1 with ⟨s, e, h1, h2', h3⟩
        refine ⟨s, e, h1, h2', ?_⟩
        rcases h3 with h3 | h3
        · left
          intro i hi_lt
          have e1 : off + h + i - h = off + i := by omega
          have e2 : off + h + i = off + i + h := by omega
          rw [hg2_eq i hi_lt, hg1_R i hi_lt]
          simp only [Bool.false_eq_true, ↓reduceIte]
          rw [e1, e2]
          exact h3 i hi_lt
        · right
          intro i hi_lt
          have e1 : off + h + i - h = off + i := by omega
          have e2 : off + h + i = off + i + h := by omega
          rw [hg2_eq i hi_lt, hg1_R i hi_lt]
          simp only [Bool.false_eq_true, ↓reduceIte]
          rw [e1, e2]
          exact h3 i hi_lt
    have hsL : IsSortedBool off h asc g2 := bitonicMerge_sorted off k asc g1 hleft_bit
    have hsR : IsSortedBool (off + h) h asc g3 := bitonicMerge_sorted (off + h) k asc g2 hright_bit
    have hg3_left : ∀ i < h, g3 (off + i) = g2 (off + i) := by
      intro i hi_lt
      apply runNet_unchanged
      intro c hc
      have hm := bitonicMerge_mem (off + h) k asc c hc
      dsimp only [h] at hi_lt ⊢
      omega
    have hnetL : ∀ c ∈ bitonicMerge off k asc, off ≤ c.1 ∧ c.1 < off + h ∧ off ≤ c.2.1 ∧ c.2.1 < off + h := by
      intro c hc; have hm := bitonicMerge_mem off k asc c hc; dsimp [h]; omega
    have hnetR : ∀ c ∈ bitonicMerge (off + h) k asc,
        off + h ≤ c.1 ∧ c.1 < off + h + h ∧ off + h ≤ c.2.1 ∧ c.2.1 < off + h + h := by
      intro c hc; have hm := bitonicMerge_mem (off + h) k asc c hc; dsimp [h]; omega
    intro i j hij hj
    by_cases hjh : j < h
    · rw [hg3_left i (by omega), hg3_left j hjh]
      exact hsL i j hij hjh
    · by_cases hih : h ≤ i
      · have ei : off + i = off + h + (i - h) := by omega
        have ej : off + j = off + h + (j - h) := by omega
        rw [ei, ej]
        exact hsR (i - h) (j - h) (by omega) (by omega)
      · have hi_lt : i < h := by omega
        have hj_lt : j - h < h := by omega
        have ej : off + j = off + h + (j - h) := by omega
        rw [hg3_left i hi_lt, ej]
        cases asc with
        | true =>
          simp only [↓reduceIte]
          rcases hsp.2.2 with hlo | hhi
          · have hg1L : ∀ x < h, g1 (off + x) = false := by
              intro x hx
              rw [hg1_L x hx]
              exact hlo x hx
            have hg2i : g2 (off + i) = false :=
              runNet_bool_const (bitonicMerge off k true) off h false g1 hnetL hg1L i hi_lt
            intro ht; rw [hg2i] at ht; cases ht
          · have hg2R : ∀ x < h, g2 (off + h + x) = true := by
              intro x hx
              have heq : g2 (off + h + x) = g1 (off + h + x) := by
                apply runNet_unchanged; intro c hc; have hm := bitonicMerge_mem off k true c hc; dsimp [h] at hx ⊢; omega
              rw [heq, hg1_R x hx]
              exact hhi x hx
            intro _
            exact runNet_bool_const (bitonicMerge (off + h) k true) (off + h) h true g2 hnetR hg2R (j - h) hj_lt
        | false =>
          simp only [Bool.false_eq_true, ↓reduceIte]
          rcases hsp.2.2 with hlo | hhi
          · have hg2R : ∀ x < h, g2 (off + h + x) = false := by
              intro x hx
              have heq : g2 (off + h + x) = g1 (off + h + x) := by
                apply runNet_unchanged; intro c hc; have hm := bitonicMerge_mem off k false c hc; dsimp [h] at hx ⊢; omega
              rw [heq, hg1_R x hx]
              simp only [Bool.false_eq_true, ↓reduceIte]
              have e1 : off + h + x - h = off + x := by omega
              have e2 : off + h + x = off + x + h := by omega
              rw [e1, e2]
              exact hlo x hx
            have hg3j : g3 (off + h + (j - h)) = false :=
              runNet_bool_const (bitonicMerge (off + h) k false) (off + h) h false g2 hnetR hg2R (j - h) hj_lt
            intro ht; rw [hg3j] at ht; cases ht
          · have hg1L : ∀ x < h, g1 (off + x) = true := by
              intro x hx
              rw [hg1_L x hx]
              simp only [Bool.false_eq_true, ↓reduceIte]
              have e1 : off + h + x - h = off + x := by omega
              have e2 : off + h + x = off + x + h := by omega
              have hhi' := hhi x hx
              dsimp only at hhi'
              rw [e1, e2] at hhi'
              exact hhi'
            intro _
            exact runNet_bool_const (bitonicMerge off k false) off h true g1 hnetL hg1L i hi_lt

theorem sorted_asc_desc_bitonic (off h : Nat) (g : Nat → Bool)
    (hL : IsSortedBool off h true g) (hR : IsSortedBool (off + h) h false g) :
    IsBitonic off (2 * h) g := by
  have hexL : ∃ s ≤ h, ∀ i < h, g (off + i) = true ↔ s ≤ i := by
    have hgenL : ∀ n, IsSortedBool off n true g → ∃ s ≤ n, ∀ i < n, g (off + i) = true ↔ s ≤ i := by
      intro n
      induction n with
      | zero => intro _; exact ⟨0, Nat.le_refl 0, fun i hi => by omega⟩
      | succ m ih =>
        intro hLm
        rcases ih (fun i j hij hj => hLm i j hij (by omega)) with ⟨s, hsm, hs⟩
        cases hgm : g (off + m) with
        | false =>
          refine ⟨m + 1, Nat.le_refl _, fun i hi => ?_⟩
          constructor
          · intro ht
            by_cases him : i = m
            · subst him; rw [hgm] at ht; cases ht
            · have hgt := hLm i m (by omega) (by omega)
              simp only [↓reduceIte] at hgt
              have := hgt ht; rw [hgm] at this; cases this
          · intro hc; omega
        | true =>
          refine ⟨s, by omega, fun i hi => ?_⟩
          by_cases him : i = m
          · subst i; rw [hgm]; simp [show s ≤ m from hsm]
          · exact hs i (by omega)
    exact hgenL h hL
  have hexR : ∃ e ≤ h, ∀ i < h, g (off + h + i) = true ↔ i < e := by
    have hgen : ∀ n (g' : Nat → Bool), IsSortedBool 0 n false g' →
        ∃ e ≤ n, ∀ i < n, g' i = true ↔ i < e := by
      intro n g'
      induction n with
      | zero => intro _; exact ⟨0, Nat.le_refl 0, fun i hi => by omega⟩
      | succ m ih =>
        intro hg'
        rcases ih (fun i j hij hj => hg' i j hij (by omega)) with ⟨e, hem, he⟩
        cases hgm : g' m with
        | false =>
          refine ⟨e, by omega, fun i hi => ?_⟩
          by_cases him : i = m
          · subst i; rw [hgm]; simp [show ¬ m < e by omega]
          · exact he i (by omega)
        | true =>
          refine ⟨m + 1, Nat.le_refl _, fun i hi => ?_⟩
          constructor
          · intro _; omega
          · intro _
            have := hg' i m (by omega) (by omega)
            simp only [Nat.zero_add, Bool.false_eq_true, ↓reduceIte] at this
            exact this hgm
    have hR' : IsSortedBool 0 h false (fun i => g (off + h + i)) := by
      intro i j hij hj
      simpa only [Nat.zero_add] using hR i j hij hj
    exact hgen h (fun i => g (off + h + i)) hR'
  rcases hexL with ⟨s, hsh, hs⟩
  rcases hexR with ⟨e, heh, he⟩
  refine ⟨s, h + e, by omega, by omega, Or.inl (fun i hi => ?_)⟩
  by_cases hih : i < h
  · rw [hs i hih]
    omega
  · have e1 : off + i = off + h + (i - h) := by omega
    rw [e1, he (i - h) (by omega)]
    omega

theorem bitonicSort_sorted_bool (off : Nat) : ∀ k asc (g : Nat → Bool),
    IsSortedBool off (2 ^ k) asc (runNet (fun b : Bool => b.toNat) (bitonicSort off k asc) g)
  | 0, asc, g => by
    intro i j hij hj
    have hi0 : i = 0 := by omega
    have hj0 : j = 0 := by omega
    subst hi0; subst hj0
    cases asc <;> exact fun h => h
  | k + 1, asc, g => by
    let h := 2 ^ k
    simp only [bitonicSort, runNet_append]
    let g1 := runNet (fun b : Bool => b.toNat) (bitonicSort off k true) g
    let g2 := runNet (fun b : Bool => b.toNat) (bitonicSort (off + h) k false) g1
    have hsL : IsSortedBool off h true g1 := bitonicSort_sorted_bool off k true g
    have hsR : IsSortedBool (off + h) h false g2 := bitonicSort_sorted_bool (off + h) k false g1
    have hg2L : IsSortedBool off h true g2 := by
      intro i j hij hj
      have e1 : g2 (off + i) = g1 (off + i) := by
        apply runNet_unchanged; intro c hc; have hm := bitonicSort_mem (off + h) k false c hc; dsimp [h] at hij hj ⊢; omega
      have e2 : g2 (off + j) = g1 (off + j) := by
        apply runNet_unchanged; intro c hc; have hm := bitonicSort_mem (off + h) k false c hc; dsimp [h] at hj ⊢; omega
      rw [e1, e2]
      exact hsL i j hij hj
    have hbit : IsBitonic off (2 ^ (k + 1)) g2 := by
      rw [Nat.pow_succ, Nat.mul_comm]
      exact sorted_asc_desc_bitonic off h g2 hg2L hsR
    exact bitonicMerge_sorted off (k + 1) asc g2 hbit

theorem bitonicSort_sorted {α : Type*} (key : α → Nat) (p : Nat) (st : Nat → α) :
    ∀ i j, i ≤ j → j < 2 ^ p →
      key (runNet key (bitonicSort 0 p true) st i) ≤ key (runNet key (bitonicSort 0 p true) st j) := by
  intro i j hij hj
  let T := key (runNet key (bitonicSort 0 p true) st i)
  let f : Nat → Bool := fun x => decide (T ≤ x)
  have hf : ∀ x y, x ≤ y → f x = true → f y = true := by
    intro x y hxy hx
    simp only [f, decide_eq_true_eq] at hx ⊢
    omega
  have hs := bitonicSort_sorted_bool 0 p true (fun idx => f (key (st idx))) i j hij hj
  simp only [Nat.zero_add, ↓reduceIte] at hs
  rw [← runNet_mono_map key f hf] at hs
  have hiT : f (key (runNet key (bitonicSort 0 p true) st i)) = true := by
    simp [f, T]
  have hjT := hs hiT
  simp only [f, decide_eq_true_eq] at hjT
  exact hjT

theorem count_applySwap {α : Type*} (N u v : Nat) (hu : u < N) (hv : v < N) (sw : Bool)
    (st : Nat → α) (P : α → Prop) [DecidablePred P] :
    ((Finset.range N).filter (fun i => P (applySwap u v sw st i))).card =
      ((Finset.range N).filter (fun i => P (st i))).card := by
  cases sw with
  | false => rfl
  | true =>
    apply Finset.card_nbij' (fun i => if i = u then v else if i = v then u else i)
      (fun i => if i = u then v else if i = v then u else i)
    · intro i hi
      simp only [Finset.coe_filter, Finset.mem_range, Set.mem_ofPred_eq, applySwap, ↓reduceIte] at hi ⊢
      by_cases h1 : i = u
      · subst h1
        by_cases h2 : i = v
        · subst h2; simpa using hi
        · simp only [↓reduceIte] at hi ⊢; exact ⟨hv, hi.2⟩
      · by_cases h2 : i = v
        · subst h2; simp only [h1, ↓reduceIte, ↓reduceIte] at hi ⊢; exact ⟨hu, hi.2⟩
        · simp only [h1, h2, ↓reduceIte] at hi ⊢; exact hi
    · intro i hi
      simp only [Finset.coe_filter, Finset.mem_range, Set.mem_ofPred_eq, applySwap, ↓reduceIte] at hi ⊢
      by_cases h1 : i = u
      · subst h1
        by_cases h2 : v = i
        · subst h2; simpa using hi
        · simp only [↓reduceIte, h2, ↓reduceIte] at hi ⊢; exact ⟨hv, hi.2⟩
      · by_cases h2 : i = v
        · subst h2
          simp only [h1, ↓reduceIte, ↓reduceIte] at hi ⊢; exact ⟨hu, hi.2⟩
        · have h3 : ¬ (i = u) := h1
          simp only [h1, h2, ↓reduceIte] at hi ⊢; exact hi
    · intro i _
      show (if (if i = u then v else if i = v then u else i) = u then v
        else if (if i = u then v else if i = v then u else i) = v then u
        else (if i = u then v else if i = v then u else i)) = i
      by_cases h1 : i = u
      · subst h1; by_cases h2 : v = i
        · subst h2; simp
        · simp [h2]
      · by_cases h2 : i = v
        · subst h2; simp [h1]
        · simp [h1, h2]
    · intro i _
      show (if (if i = u then v else if i = v then u else i) = u then v
        else if (if i = u then v else if i = v then u else i) = v then u
        else (if i = u then v else if i = v then u else i)) = i
      by_cases h1 : i = u
      · subst h1; by_cases h2 : v = i
        · subst h2; simp
        · simp [h2]
      · by_cases h2 : i = v
        · subst h2; simp [h1]
        · simp [h1, h2]

theorem count_runNet {α : Type*} (key : α → Nat) (N : Nat) (net : List (Nat × Nat × Bool))
    (hnet : ∀ c ∈ net, c.1 < N ∧ c.2.1 < N) (st : Nat → α) (P : α → Prop) [DecidablePred P] :
    ((Finset.range N).filter (fun i => P (runNet key net st i))).card =
      ((Finset.range N).filter (fun i => P (st i))).card := by
  induction net generalizing st with
  | nil => rfl
  | cons c rest ih =>
    rcases c with ⟨u, v, asc⟩
    have hc := hnet (u, v, asc) List.mem_cons_self
    have h1 := ih (fun c' hc' => hnet c' (List.mem_cons_of_mem _ hc'))
      (applySwap u v (swapBit (key (st u)) (key (st v)) asc) st)
    have h2 := count_applySwap N u v hc.1 hc.2 (swapBit (key (st u)) (key (st v)) asc) st P
    exact h1.trans h2

theorem all_runNet {α : Type*} (key : α → Nat) (N : Nat) (net : List (Nat × Nat × Bool))
    (hnet : ∀ c ∈ net, c.1 < N ∧ c.2.1 < N) (st : Nat → α) (P : α → Prop)
    (h : ∀ i < N, P (st i)) : ∀ i < N, P (runNet key net st i) := by
  classical
  intro i hi
  by_contra hne
  have hc := count_runNet key N net hnet st (fun a => ¬ P a)
  have h0 : ((Finset.range N).filter (fun i => ¬ P (st i))).card = 0 := by
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro j hj; simpa using h j (Finset.mem_range.mp hj)
  rw [h0, Finset.card_eq_zero, Finset.filter_eq_empty_iff] at hc
  exact hc (Finset.mem_range.mpr hi) hne

end BitonicSec

section NetCirc

abbrev Rec := (Nat → Bool) × (Nat → Bool)

def recKey (kw : Nat) (r : Rec) : Nat :=
  bitsVal r.1 kw

theorem netSwaps_length {α : Type*} (key : α → Nat) (net : List (Nat × Nat × Bool)) (st : Nat → α) :
    (netSwaps key net st).length = net.length := by
  induction net generalizing st with
  | nil => rfl
  | cons c rest ih =>
    rcases c with ⟨u, v, asc⟩
    simp [netSwaps, ih]

theorem netSwaps_getD_uv {α : Type*} (key : α → Nat) (net : List (Nat × Nat × Bool)) (st : Nat → α) :
    ∀ t < net.length,
      ((netSwaps key net st).getD t (0, 0, false)).1 = (net.getD t (0, 0, false)).1 ∧
      ((netSwaps key net st).getD t (0, 0, false)).2.1 = (net.getD t (0, 0, false)).2.1 := by
  induction net generalizing st with
  | nil => intro t ht; simp at ht
  | cons c rest ih =>
    rcases c with ⟨u, v, asc⟩
    intro t ht
    cases t with
    | zero => simp [netSwaps]
    | succ t =>
      simp only [List.length_cons] at ht
      simpa [netSwaps] using ih _ t (by omega)

theorem replaySwaps_lt (N : Nat) (l : List (Nat × Nat × Bool))
    (hl : ∀ c ∈ l, c.1 < N ∧ c.2.1 < N) :
    ∀ (f : Nat → Nat), (∀ idx < N, f idx < N) → ∀ idx < N, replaySwaps l f idx < N := by
  induction l with
  | nil => intro f hf idx hidx; exact hf idx hidx
  | cons c rest ih =>
    rcases c with ⟨u, v, sw⟩
    intro f hf idx hidx
    have hc := hl (u, v, sw) List.mem_cons_self
    apply ih (fun c' hc' => hl c' (List.mem_cons_of_mem _ hc')) _ _ idx hidx
    intro m hm
    simp only [applySwap]
    cases sw
    · exact hf m hm
    · simp only [↓reduceIte]
      by_cases h1 : m = u
      · simp [h1, hf v hc.2]
      · by_cases h2 : m = v
        · simp only [h1, ↓reduceIte]; simp only [h2, ↓reduceIte]; exact hf u hc.1
        · simp [h1, h2, hf m hm]

theorem netSwaps_mem_lt {α : Type*} (key : α → Nat) (N : Nat) (net : List (Nat × Nat × Bool))
    (hnet : ∀ c ∈ net, c.1 < N ∧ c.2.1 < N) (st : Nat → α) :
    ∀ c ∈ netSwaps key net st, c.1 < N ∧ c.2.1 < N := by
  induction net generalizing st with
  | nil => intro c hc; simp [netSwaps] at hc
  | cons a rest ih =>
    rcases a with ⟨u, v, asc⟩
    intro c hc
    have ha := hnet (u, v, asc) List.mem_cons_self
    simp only [netSwaps, List.mem_cons] at hc
    rcases hc with rfl | hc
    · exact ha
    · exact ih (fun c' hc' => hnet c' (List.mem_cons_of_mem _ hc')) _ c hc

theorem bitonicPerm {α : Type*} (key : α → Nat) (N : Nat) (net : List (Nat × Nat × Bool))
    (hnet : ∀ c ∈ net, c.1 < N ∧ c.2.1 < N) (st : Nat → α) :
    let sws := netSwaps key net st
    let pFwd : Nat → Nat := replaySwaps sws id
    let pInv : Nat → Nat := replaySwaps sws.reverse id
    (∀ idx, pFwd (pInv idx) = idx) ∧
    (∀ idx, pInv (pFwd idx) = idx) ∧
    (∀ idx < N, pFwd idx < N) ∧
    (∀ idx < N, pInv idx < N) ∧
    (∀ idx, runNet key net st idx = st (pFwd idx)) ∧
    (∀ idx, runNet key net st (pInv idx) = st idx) ∧
    (∀ {β : Type} (f : Nat → β) (idx : Nat), replaySwaps sws.reverse f idx = f (pInv idx)) := by
  intro sws pFwd pInv
  have h1 : ∀ idx, pFwd (pInv idx) = idx := by
    intro idx
    have h3 : replaySwaps sws.reverse pFwd idx = idx :=
      congrFun (replaySwaps_reverse_cancel sws id) idx
    have h4 : replaySwaps sws.reverse pFwd idx = pFwd (pInv idx) :=
      congrFun (replaySwaps_comp sws.reverse pFwd id) idx
    rw [← h4]; exact h3
  have h2 : ∀ idx, pInv (pFwd idx) = idx := by
    intro idx
    have h3 : replaySwaps sws pInv idx = idx := by
      have h := congrFun (replaySwaps_reverse_cancel sws.reverse id) idx
      rw [List.reverse_reverse] at h
      exact h
    have h4 : replaySwaps sws pInv idx = pInv (pFwd idx) :=
      congrFun (replaySwaps_comp sws pInv id) idx
    rw [← h4]; exact h3
  have hsws_lt := netSwaps_mem_lt key N net hnet st
  have h3 : ∀ idx < N, pFwd idx < N := replaySwaps_lt N sws hsws_lt id (fun _ h => h)
  have h4 : ∀ idx < N, pInv idx < N :=
    replaySwaps_lt N sws.reverse (fun c hc => hsws_lt c (List.mem_reverse.mp hc)) id (fun _ h => h)
  have h5 : ∀ idx, runNet key net st idx = st (pFwd idx) := by
    intro idx
    rw [runNet_eq_replay]
    exact congrFun (replaySwaps_comp sws st id) idx
  have h6 : ∀ idx, runNet key net st (pInv idx) = st idx := by
    intro idx
    rw [h5, h1]
  exact ⟨h1, h2, h3, h4, h5, h6, fun f idx => congrFun (replaySwaps_comp sws.reverse f id) idx⟩

theorem netCircuit {n : Nat} {A : Set (Sig n)} (kw pw N : Nat)
    (net : List (Nat × Nat × Bool))
    (hnet : ∀ c ∈ net, c.1 < N ∧ c.2.1 < N)
    (st0 : (Fin n → Bool) → Nat → Rec)
    (hK : ∀ idx < N, ∀ j < kw, (fun v => (st0 v idx).1 j) ∈ A)
    (hV : ∀ idx < N, ∀ j < pw, (fun v => (st0 v idx).2 j) ∈ A)
    (hfalse : (fun _ => false) ∈ A) :
    Build A
      ({f | ∃ idx < N, ∃ j < kw, f = fun v => (runNet (recKey kw) net (st0 v) idx).1 j} ∪
       {f | ∃ idx < N, ∃ j < pw, f = fun v => (runNet (recKey kw) net (st0 v) idx).2 j} ∪
       {f | ∃ t < net.length,
         f = (fun v => ((netSwaps (recKey kw) net (st0 v)).getD t (0, 0, false)).2.2) ∨
         f = (fun v => !(((netSwaps (recKey kw) net (st0 v)).getD t (0, 0, false)).2.2))})
      (net.length * (11 * kw + 6 * pw + 1)) := by
  induction net generalizing st0 A with
  | nil =>
    refine relax (idle ?_) le_rfl le_rfl (by simp)
    rintro f ((⟨idx, hidx, j, hj, rfl⟩ | ⟨idx, hidx, j, hj, rfl⟩) | ⟨t, ht, _⟩)
    · exact hK idx hidx j hj
    · exact hV idx hidx j hj
    · simp at ht
  | cons c rest ih =>
    rcases c with ⟨u, v, asc⟩
    have hc := hnet (u, v, asc) List.mem_cons_self
    let swSig : Sig n := fun x =>
      swapBit (recKey kw (st0 x u)) (recKey kw (st0 x v)) asc
    have Hsw : Build A {swSig} (5 * kw) := by
      cases asc with
      | true =>
        exact ltWordG (fun j x => (st0 x v).1 j) (fun j x => (st0 x u).1 j) kw
          (fun j hj => hK v hc.2 j hj) (fun j hj => hK u hc.1 j hj) hfalse
      | false =>
        exact ltWordG (fun j x => (st0 x u).1 j) (fun j x => (st0 x v).1 j) kw
          (fun j hj => hK u hc.1 j hj) (fun j hj => hK v hc.2 j hj) hfalse
    let nswSig : Sig n := nt swSig
    have Hnsw : Build (A ∪ {swSig}) {nswSig} 1 := notG (Or.inr rfl)
    let st1 : (Fin n → Bool) → Nat → Rec := fun x => applySwap u v (swSig x) (st0 x)
    let A1 := A ∪ ({swSig} ∪ {nswSig})
    have hsw1 : swSig ∈ A1 := Or.inr (Or.inl rfl)
    have hnsw1 : nswSig ∈ A1 := Or.inr (Or.inr rfl)
    let K1 : Nat → Sig n := fun j x => (st1 x u).1 j
    let K2 : Nat → Sig n := fun j x => (st1 x v).1 j
    let V1 : Nat → Sig n := fun j x => (st1 x u).2 j
    let V2 : Nat → Sig n := fun j x => (st1 x v).2 j
    let BK1 := {f | ∃ j < kw, f = K1 j}
    let BK2 := {f | ∃ j < kw, f = K2 j}
    let BV1 := {f | ∃ j < pw, f = V1 j}
    let BV2 := {f | ∃ j < pw, f = V2 j}
    have HK1 : Build A1 BK1 (kw * 3) := rangeG K1 3 fun j hj => by
      have he : K1 j = fun x => if swSig x then (st0 x v).1 j else (st0 x u).1 j := by
        funext x; simp only [K1, st1, applySwap]; cases swSig x <;> simp
      rw [he]
      exact muxG hsw1 hnsw1 (Or.inl (hK v hc.2 j hj)) (Or.inl (hK u hc.1 j hj)) (fun _ => rfl)
    have HK2 : Build (A1 ∪ BK1) BK2 (kw * 3) := rangeG K2 3 fun j hj => by
      have he : K2 j = fun x => if swSig x then (st0 x u).1 j else (st0 x v).1 j := by
        funext x; simp only [K2, st1, applySwap]
        by_cases huv : v = u
        · subst huv; cases swSig x <;> simp
        · cases swSig x <;> simp [huv]
      rw [he]
      exact muxG (Or.inl hsw1) (Or.inl hnsw1) (Or.inl (Or.inl (hK u hc.1 j hj)))
        (Or.inl (Or.inl (hK v hc.2 j hj))) (fun _ => rfl)
    have HV1 : Build (A1 ∪ (BK1 ∪ BK2)) BV1 (pw * 3) := rangeG V1 3 fun j hj => by
      have he : V1 j = fun x => if swSig x then (st0 x v).2 j else (st0 x u).2 j := by
        funext x; simp only [V1, st1, applySwap]; cases swSig x <;> simp
      rw [he]
      exact muxG (Or.inl hsw1) (Or.inl hnsw1) (Or.inl (Or.inl (hV v hc.2 j hj)))
        (Or.inl (Or.inl (hV u hc.1 j hj))) (fun _ => rfl)
    have HV2 : Build (A1 ∪ ((BK1 ∪ BK2) ∪ BV1)) BV2 (pw * 3) := rangeG V2 3 fun j hj => by
      have he : V2 j = fun x => if swSig x then (st0 x u).2 j else (st0 x v).2 j := by
        funext x; simp only [V2, st1, applySwap]
        by_cases huv : v = u
        · subst huv; cases swSig x <;> simp
        · cases swSig x <;> simp [huv]
      rw [he]
      exact muxG (Or.inl hsw1) (Or.inl hnsw1) (Or.inl (Or.inl (hV u hc.1 j hj)))
        (Or.inl (Or.inl (hV v hc.2 j hj))) (fun _ => rfl)
    let B1 := ({swSig} ∪ {nswSig}) ∪ (((BK1 ∪ BK2) ∪ BV1) ∪ BV2)
    have Hstep : Build A B1 (11 * kw + 6 * pw + 1) :=
      relax (seq (seq Hsw Hnsw) (seq (seq (seq HK1 HK2) HV1) HV2)) le_rfl le_rfl (by omega)
    have hK1 : ∀ idx < N, ∀ j < kw, (fun x => (st1 x idx).1 j) ∈ A ∪ B1 := by
      intro idx hidx j hj
      by_cases hu : idx = u
      · subst hu; exact Or.inr (Or.inr (Or.inl (Or.inl (Or.inl ⟨j, hj, rfl⟩))))
      · by_cases hv : idx = v
        · subst hv; exact Or.inr (Or.inr (Or.inl (Or.inl (Or.inr ⟨j, hj, rfl⟩))))
        · have he : (fun x => (st1 x idx).1 j) = (fun x => (st0 x idx).1 j) := by
            funext x; simp only [st1, applySwap]; cases swSig x <;> simp [hu, hv]
          rw [he]; exact Or.inl (hK idx hidx j hj)
    have hV1 : ∀ idx < N, ∀ j < pw, (fun x => (st1 x idx).2 j) ∈ A ∪ B1 := by
      intro idx hidx j hj
      by_cases hu : idx = u
      · subst hu; exact Or.inr (Or.inr (Or.inl (Or.inr ⟨j, hj, rfl⟩)))
      · by_cases hv : idx = v
        · subst hv; exact Or.inr (Or.inr (Or.inr ⟨j, hj, rfl⟩))
        · have he : (fun x => (st1 x idx).2 j) = (fun x => (st0 x idx).2 j) := by
            funext x; simp only [st1, applySwap]; cases swSig x <;> simp [hu, hv]
          rw [he]; exact Or.inl (hV idx hidx j hj)
    have Hrest := ih (fun c' hc' => hnet c' (List.mem_cons_of_mem _ hc')) st1 hK1 hV1 (Or.inl hfalse)
    refine relax (seq Hstep Hrest) le_rfl ?_ ?_
    · rintro f ((⟨idx, hidx, j, hj, rfl⟩ | ⟨idx, hidx, j, hj, rfl⟩) | ⟨t, ht, hft⟩)
      · exact Or.inr (Or.inl (Or.inl ⟨idx, hidx, j, hj, rfl⟩))
      · exact Or.inr (Or.inl (Or.inr ⟨idx, hidx, j, hj, rfl⟩))
      · cases t with
        | zero =>
          rcases hft with rfl | rfl
          · exact Or.inl (Or.inl (Or.inl rfl))
          · exact Or.inl (Or.inl (Or.inr rfl))
        | succ t =>
          simp only [List.length_cons] at ht
          exact Or.inr (Or.inr ⟨t, by omega, hft⟩)
    · simp only [List.length_cons]
      rw [Nat.succ_mul rest.length, Nat.add_comm]

theorem replayCircuit {n : Nat} {A : Set (Sig n)} (pw N : Nat)
    (sws : (Fin n → Bool) → List (Nat × Nat × Bool))
    (L : Nat) (hL : ∀ v, (sws v).length = L)
    (hidx_fixed : ∀ t < L, ∃ u v, u < N ∧ v < N ∧
      ∀ x, ((sws x).getD t (0, 0, false)).1 = u ∧ ((sws x).getD t (0, 0, false)).2.1 = v)
    (hsw_mem : ∀ t < L,
      (fun x => ((sws x).getD t (0, 0, false)).2.2) ∈ A ∧
      (fun x => !(((sws x).getD t (0, 0, false)).2.2)) ∈ A)
    (ans0 : (Fin n → Bool) → Nat → Nat → Bool)
    (hA0 : ∀ idx < N, ∀ j < pw, (fun x => ans0 x idx j) ∈ A) :
    Build A {f | ∃ idx < N, ∃ j < pw, f = fun x => replaySwaps (sws x) (ans0 x) idx j} (L * (6 * pw)) := by
  induction L generalizing sws ans0 A with
  | zero =>
    refine relax (idle ?_) le_rfl le_rfl (by simp)
    rintro f ⟨idx, hidx, j, hj, rfl⟩
    have he : (fun x => replaySwaps (sws x) (ans0 x) idx j) = (fun x => ans0 x idx j) := by
      funext x
      rw [List.eq_nil_of_length_eq_zero (hL x)]
      rfl
    rw [he]
    exact hA0 idx hidx j hj
  | succ L ih =>
    rcases hidx_fixed 0 (Nat.zero_lt_succ L) with ⟨u, v, hu, hv, huv⟩
    let swSig : Sig n := fun x => ((sws x).getD 0 (0, 0, false)).2.2
    have hsw0 := hsw_mem 0 (Nat.zero_lt_succ L)
    let ans1 : (Fin n → Bool) → Nat → Nat → Bool := fun x => applySwap u v (swSig x) (ans0 x)
    let V1 : Nat → Sig n := fun j x => ans1 x u j
    let V2 : Nat → Sig n := fun j x => ans1 x v j
    let BV1 := {f | ∃ j < pw, f = V1 j}
    let BV2 := {f | ∃ j < pw, f = V2 j}
    have HV1 : Build A BV1 (pw * 3) := rangeG V1 3 fun j hj => by
      have he : V1 j = fun x => if swSig x then ans0 x v j else ans0 x u j := by
        funext x; simp only [V1, ans1, applySwap]; cases swSig x <;> simp
      rw [he]
      exact muxG hsw0.1 hsw0.2 (hA0 v hv j hj) (hA0 u hu j hj) (fun _ => rfl)
    have HV2 : Build (A ∪ BV1) BV2 (pw * 3) := rangeG V2 3 fun j hj => by
      have he : V2 j = fun x => if swSig x then ans0 x u j else ans0 x v j := by
        funext x; simp only [V2, ans1, applySwap]
        by_cases hvu : v = u
        · subst hvu; cases swSig x <;> simp
        · cases swSig x <;> simp [hvu]
      rw [he]
      exact muxG (Or.inl hsw0.1) (Or.inl hsw0.2) (Or.inl (hA0 u hu j hj)) (Or.inl (hA0 v hv j hj)) (fun _ => rfl)
    have Hstep := seq HV1 HV2
    let sws' : (Fin n → Bool) → List (Nat × Nat × Bool) := fun x => (sws x).tail
    have hL' : ∀ x, (sws' x).length = L := fun x => by simp [sws', List.length_tail, hL x]
    have hget_tail : ∀ t < L, ∀ x, (sws' x).getD t (0, 0, false) = (sws x).getD (t + 1) (0, 0, false) := by
      intro t _ x
      cases hs : sws x with
      | nil => have := hL x; rw [hs] at this; simp at this
      | cons c cs => simp [sws', hs]
    have hidx' : ∀ t < L, ∃ u' v', u' < N ∧ v' < N ∧
        ∀ x, ((sws' x).getD t (0, 0, false)).1 = u' ∧ ((sws' x).getD t (0, 0, false)).2.1 = v' := by
      intro t ht
      rcases hidx_fixed (t + 1) (by omega) with ⟨u', v', hu', hv', hEq⟩
      refine ⟨u', v', hu', hv', fun x => ?_⟩
      rw [hget_tail t ht x]; exact hEq x
    have hsw' : ∀ t < L,
        (fun x => ((sws' x).getD t (0, 0, false)).2.2) ∈ A ∪ (BV1 ∪ BV2) ∧
        (fun x => !(((sws' x).getD t (0, 0, false)).2.2)) ∈ A ∪ (BV1 ∪ BV2) := by
      intro t ht
      have h1 := hsw_mem (t + 1) (by omega)
      have e1 : (fun x => ((sws' x).getD t (0, 0, false)).2.2) = (fun x => ((sws x).getD (t + 1) (0, 0, false)).2.2) := by
        funext x; rw [hget_tail t ht x]
      have e2 : (fun x => !(((sws' x).getD t (0, 0, false)).2.2)) = (fun x => !(((sws x).getD (t + 1) (0, 0, false)).2.2)) := by
        funext x; rw [hget_tail t ht x]
      rw [e1, e2]; exact ⟨Or.inl h1.1, Or.inl h1.2⟩
    have hA1 : ∀ idx < N, ∀ j < pw, (fun x => ans1 x idx j) ∈ A ∪ (BV1 ∪ BV2) := by
      intro idx hidx j hj
      by_cases h1 : idx = u
      · subst h1; exact Or.inr (Or.inl ⟨j, hj, rfl⟩)
      · by_cases h2 : idx = v
        · subst h2; exact Or.inr (Or.inr ⟨j, hj, rfl⟩)
        · have he : (fun x => ans1 x idx j) = (fun x => ans0 x idx j) := by
            funext x; simp only [ans1, applySwap]; cases swSig x <;> simp [h1, h2]
          rw [he]; exact Or.inl (hA0 idx hidx j hj)
    have Hrest := ih sws' hL' hidx' hsw' ans1 hA1
    refine relax (seq Hstep Hrest) le_rfl ?_ ?_
    · rintro f ⟨idx, hidx, j, hj, rfl⟩
      right
      refine ⟨idx, hidx, j, hj, ?_⟩
      funext x
      cases hs : sws x with
      | nil => have := hL x; rw [hs] at this; simp at this
      | cons c cs =>
        have h0 := huv x
        rw [hs] at h0
        simp only [List.getD_cons_zero] at h0
        rcases c with ⟨cu, cv, csw⟩
        dsimp only at h0
        rcases h0 with ⟨rfl, rfl⟩
        have he_sw : swSig x = csw := by simp [swSig, hs]
        simp only [replaySwaps, sws', hs, List.tail_cons, ans1, he_sw]
    · rw [Nat.succ_mul L]; omega

theorem replayRevCircuit {n : Nat} {A : Set (Sig n)} (kw pw N : Nat)
    (net : List (Nat × Nat × Bool))
    (hnet : ∀ c ∈ net, c.1 < N ∧ c.2.1 < N)
    (st0 : (Fin n → Bool) → Nat → Rec)
    (hsw : ∀ t < net.length,
      (fun x => ((netSwaps (recKey kw) net (st0 x)).getD t (0, 0, false)).2.2) ∈ A ∧
      (fun x => !(((netSwaps (recKey kw) net (st0 x)).getD t (0, 0, false)).2.2)) ∈ A)
    (ans0 : (Fin n → Bool) → Nat → Nat → Bool)
    (hA0 : ∀ idx < N, ∀ j < pw, (fun x => ans0 x idx j) ∈ A) :
    Build A
      {f | ∃ idx < N, ∃ j < pw,
        f = fun x => replaySwaps (netSwaps (recKey kw) net (st0 x)).reverse (ans0 x) idx j}
      (net.length * (6 * pw)) := by
  let swsRev : (Fin n → Bool) → List (Nat × Nat × Bool) :=
    fun v => (netSwaps (recKey kw) net (st0 v)).reverse
  have hL : ∀ v, (swsRev v).length = net.length := fun v => by simp [swsRev, netSwaps_length]
  have hget : ∀ t < net.length, ∀ v,
      (swsRev v).getD t (0, 0, false) =
        (netSwaps (recKey kw) net (st0 v)).getD (net.length - 1 - t) (0, 0, false) := by
    intro t ht v
    have hlen : (netSwaps (recKey kw) net (st0 v)).length = net.length := netSwaps_length _ _ _
    dsimp only [swsRev]
    rw [List.getD_eq_getElem _ _ (by simp [hlen]; omega),
        List.getD_eq_getElem _ _ (by omega), List.getElem_reverse]
    congr 1; omega
  have hidx : ∀ t < net.length, ∃ u' v', u' < N ∧ v' < N ∧
      ∀ x, ((swsRev x).getD t (0, 0, false)).1 = u' ∧ ((swsRev x).getD t (0, 0, false)).2.1 = v' := by
    intro t ht
    let t' := net.length - 1 - t
    have ht' : t' < net.length := by omega
    have hbd := hnet _ (List.getElem_mem ht')
    have hgn : net.getD t' (0, 0, false) = net[t']'ht' := by simp [List.getD_eq_getElem?_getD, ht']
    refine ⟨(net[t']'ht').1, (net[t']'ht').2.1, hbd.1, hbd.2, fun x => ?_⟩
    rw [hget t ht x]
    have huv := netSwaps_getD_uv (recKey kw) net (st0 x) t' ht'
    rw [hgn] at huv; exact huv
  have hsw' : ∀ t < net.length,
      (fun x => ((swsRev x).getD t (0, 0, false)).2.2) ∈ A ∧
      (fun x => !(((swsRev x).getD t (0, 0, false)).2.2)) ∈ A := by
    intro t ht
    let t' := net.length - 1 - t
    have e1 : (fun x => ((swsRev x).getD t (0, 0, false)).2.2) =
        (fun x => ((netSwaps (recKey kw) net (st0 x)).getD t' (0, 0, false)).2.2) := by
      funext x; rw [hget t ht x]
    have e2 : (fun x => !(((swsRev x).getD t (0, 0, false)).2.2)) =
        (fun x => !(((netSwaps (recKey kw) net (st0 x)).getD t' (0, 0, false)).2.2)) := by
      funext x; rw [hget t ht x]
    rw [e1, e2]; exact hsw t' (by omega)
  exact replayCircuit pw N swsRev net.length hL hidx hsw' ans0 hA0

end NetCirc

section CipherCore

def toNat {k : ℕ} (x : Fin k → Bool) : ℕ :=
  ∑ j : Fin k, (x j).toNat * 2 ^ j.val

def ofNat (k w : ℕ) : Fin k → Bool :=
  fun j => w.testBit j.val

theorem toNat_lt {k : ℕ} (x : Fin k → Bool) : toNat x < 2 ^ k := by
  unfold toNat
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Fin.sum_univ_castSucc]
    have hlt := ih (fun j => x j.castSucc)
    have hle : (x (Fin.last k)).toNat ≤ 1 := by cases x (Fin.last k) <;> simp
    have hpow : 2 ^ (k + 1) = 2 ^ k + 2 ^ k := by ring
    simp only [Fin.val_castSucc, Fin.val_last]
    nlinarith [Nat.one_le_pow k 2 (by omega)]

theorem testBit_toNat_aux (k : ℕ) (x : Fin k → Bool) (i : ℕ) :
    (toNat x).testBit i = if h : i < k then x ⟨i, h⟩ else false := by
  induction k generalizing i with
  | zero =>
    simp [toNat]
  | succ k ih =>
    unfold toNat
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last]
    set lo := ∑ j : Fin k, (x j.castSucc).toNat * 2 ^ j.val
    have hlo : lo < 2 ^ k := toNat_lt (fun j => x j.castSucc)
    have hlo_eq : lo = toNat (fun j : Fin k => x j.castSucc) := rfl
    have hpow2 : ∀ (n m : ℕ), n.testBit m = decide ((n / 2 ^ m) % 2 = 1) := by
      intro n m
      simp only [Nat.testBit, Nat.shiftRight_eq_div_pow]
      rcases Nat.mod_two_eq_zero_or_one (n / 2 ^ m) with h | h <;> simp [h]
    by_cases hik : i < k
    · have hlt : i < k + 1 := by omega
      simp only [hlt, ↓reduceDIte]
      have hdiv : (lo + (x (Fin.last k)).toNat * 2 ^ k) / 2 ^ i =
          lo / 2 ^ i + (x (Fin.last k)).toNat * 2 ^ (k - i) := by
        have hk_eq : 2 ^ k = 2 ^ (k - i) * 2 ^ i := by
          rw [← Nat.pow_add, Nat.sub_add_cancel (Nat.le_of_lt hik)]
        rw [hk_eq, ← Nat.mul_assoc, Nat.add_mul_div_right _ _ (Nat.pow_pos (by omega))]
      have heven : 2 ∣ (x (Fin.last k)).toNat * 2 ^ (k - i) := by
        have hk2 : 2 ^ (k - i) = 2 ^ (k - i - 1) * 2 := by
          have : k - i = (k - i - 1) + 1 := by omega
          conv_lhs => rw [this, Nat.pow_succ]
        rw [hk2, ← Nat.mul_assoc]; exact dvd_mul_left 2 _
      have hbit_eq : (lo + (x (Fin.last k)).toNat * 2 ^ k).testBit i = lo.testBit i := by
        rw [hpow2, hpow2, hdiv]
        obtain ⟨t, ht⟩ := heven
        rw [ht, Nat.add_mul_mod_self_left]
      rw [hbit_eq, hlo_eq, ih _ i, dite_eq_left hik]
      rfl
    · have hki : k ≤ i := Nat.not_lt.mp hik
      have hdivk : (lo + (x (Fin.last k)).toNat * 2 ^ k) / 2 ^ k = (x (Fin.last k)).toNat := by
        rw [Nat.add_mul_div_right _ _ (Nat.pow_pos (by omega)), Nat.div_eq_of_lt hlo, Nat.zero_add]
      have hdivi : (lo + (x (Fin.last k)).toNat * 2 ^ k) / 2 ^ i =
          (x (Fin.last k)).toNat / 2 ^ (i - k) := by
        have hi_eq : 2 ^ i = 2 ^ k * 2 ^ (i - k) := by
          rw [← Nat.pow_add, Nat.add_sub_of_le hki]
        rw [hi_eq, ← Nat.div_div_eq_div_mul, hdivk]
      have hbit_eq : (lo + (x (Fin.last k)).toNat * 2 ^ k).testBit i =
          ((x (Fin.last k)).toNat).testBit (i - k) := by
        rw [hpow2, hpow2, hdivi]
      rw [hbit_eq]
      by_cases hik1 : i = k
      · subst hik1
        simp only [Nat.lt_succ_self, ↓reduceDIte, Nat.sub_self]
        rw [show (⟨i, Nat.lt_succ_self i⟩ : Fin (i + 1)) = Fin.last i from rfl]
        cases x (Fin.last i) <;> rfl
      · have hnot1 : ¬ i < k + 1 := by omega
        simp only [hnot1, ↓reduceDIte]
        have hpos : 0 < i - k := by omega
        cases x (Fin.last k)
        · simp
        · change (1 : ℕ).testBit (i - k) = false
          cases hd : i - k with
          | zero => omega
          | succ d =>
            rw [hpow2, Nat.div_eq_of_lt (Nat.one_lt_two_pow (Nat.succ_ne_zero d))]
            rfl

theorem testBit_toNat {k : ℕ} (x : Fin k → Bool) (i : ℕ) :
    (toNat x).testBit i = if h : i < k then x ⟨i, h⟩ else false :=
  testBit_toNat_aux k x i

theorem testBit_toNat_fin {k : ℕ} (x : Fin k → Bool) (i : Fin k) :
    (toNat x).testBit i.val = x i := by
  rw [testBit_toNat]; simp [i.isLt]

theorem ofNat_toNat {k : ℕ} (x : Fin k → Bool) : ofNat k (toNat x) = x := by
  ext i
  exact testBit_toNat_fin x i

theorem toNat_inj {k : ℕ} {x y : Fin k → Bool} (h : toNat x = toNat y) : x = y := by
  have := congrArg (ofNat k) h
  simpa [ofNat_toNat] using this

theorem toNat_ofNat {k w : ℕ} (hw : w < 2 ^ k) : toNat (ofNat k w) = w := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [testBit_toNat]
  by_cases hi : i < k
  · simp [hi, ofNat]
  · simp only [hi, ↓reduceDIte]
    symm
    apply Nat.testBit_lt_two_pow
    calc w < 2 ^ k := hw
      _ ≤ 2 ^ i := Nat.pow_le_pow_right (by omega) (Nat.not_lt.mp hi)

theorem mod_two_pow_testBit (w k i : ℕ) :
    (w % 2 ^ k).testBit i = if i < k then w.testBit i else false := by
  rw [Nat.testBit_mod_two_pow]
  by_cases hi : i < k <;> simp [hi]

theorem testBit_xor_apply (a b : ℕ) (i : ℕ) :
    (a ^^^ b).testBit i = xor (a.testBit i) (b.testBit i) :=
  Nat.testBit_xor a b i

theorem xor_toNat {k : ℕ} (x y : Fin k → Bool) :
    toNat (fun i => xor (x i) (y i)) = toNat x ^^^ toNat y := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [testBit_toNat, Nat.testBit_xor, testBit_toNat, testBit_toNat]
  split <;> simp

theorem testBit_one_ne {p : ℕ} (hp : p ≠ 0) : (1 : ℕ).testBit p = false := by
  cases p with
  | zero => contradiction
  | succ p =>
    simp [Nat.testBit, Nat.shiftRight_eq_div_pow,
      Nat.div_eq_of_lt (Nat.one_lt_two_pow (Nat.succ_ne_zero p))]

def rotB {k : ℕ} (hk : 0 < k) (s : ℕ) (x : Fin k → Bool) : Fin k → Bool :=
  fun i => x ⟨(i.val + k - s % k) % k, Nat.mod_lt _ hk⟩

theorem rot_toNat {k : ℕ} (hk : 0 < k) (s : ℕ) (x : Fin k → Bool) :
    ((toNat x <<< (s % k)) ||| (toNat x >>> (k - s % k))) % 2 ^ k =
      toNat (rotB hk s x) := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [mod_two_pow_testBit, testBit_toNat]
  by_cases hi : i < k
  · simp only [hi, ↓reduceIte, ↓reduceDIte, Nat.testBit_or, Nat.testBit_shiftLeft,
      Nat.testBit_shiftRight]
    set r := s % k
    have hr : r < k := Nat.mod_lt s hk
    by_cases hri : r ≤ i
    · have hb1 : decide (r ≤ i) = true := decide_eq_true hri
      have hb2 : (toNat x).testBit (k - r + i) = false := by
        rw [testBit_toNat]; simp [show ¬ k - r + i < k by omega]
      simp only [hb1, Bool.true_and, hb2, Bool.or_false]
      rw [testBit_toNat]; simp only [show i - r < k by omega, ↓reduceDIte]
      congr 1; rw [Fin.ext_iff]; dsimp [rotB]
      have : (i + k - r) = k + (i - r) := by omega
      rw [this, Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]
    · have hi_lt : i < r := Nat.not_le.mp hri
      have hb1 : decide (r ≤ i) = false := decide_eq_false hri
      simp only [hb1, Bool.false_and, Bool.false_or]
      rw [testBit_toNat]; simp only [show k - r + i < k by omega, ↓reduceDIte]
      congr 1; rw [Fin.ext_iff]; dsimp [rotB]
      have hsub : i + k - r < k := by omega
      rw [Nat.mod_eq_of_lt hsub]; omega
  · simp [hi]

def stepB {k : ℕ} (hk : 0 < k) (x : Fin k → Bool) : Fin k → Bool :=
  fun i => xor (x i)
    (!(x ⟨(i.val + 1) % k, Nat.mod_lt _ hk⟩) && x ⟨(i.val + 2) % k, Nat.mod_lt _ hk⟩)

theorem step_toNat_aux {k : ℕ} (hk : 0 < k) (x : Fin k → Bool) (m : ℕ) (hm : m ≤ k) :
    ((List.range m).foldl (fun acc i =>
      acc ||| ((xor ((toNat x).testBit i)
        (!((toNat x).testBit ((i + 1) % k)) && (toNat x).testBit ((i + 2) % k))).toNat <<< i)) 0) =
    toNat (fun j : Fin k => if j.val < m then stepB hk x j else false) := by
  induction m with
  | zero =>
    simp [toNat]
  | succ m ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    rw [ih (by omega)]
    set lhs_prev := toNat (fun j : Fin k => if j.val < m then stepB hk x j else false)
    have hbit : ∀ i,
        (lhs_prev ||| ((xor ((toNat x).testBit m)
          (!((toNat x).testBit ((m + 1) % k)) && (toNat x).testBit ((m + 2) % k))).toNat <<< m)).testBit i =
        (toNat (fun j : Fin k => if j.val < m + 1 then stepB hk x j else false)).testBit i := by
      intro i
      rw [Nat.testBit_or, Nat.testBit_shiftLeft]
      rw [show (toNat x).testBit m = x ⟨m, by omega⟩ from by rw [testBit_toNat]; simp [show m < k by omega]]
      rw [show (toNat x).testBit ((m + 1) % k) = x ⟨(m + 1) % k, Nat.mod_lt _ hk⟩ from by
        rw [testBit_toNat]; simp [Nat.mod_lt _ hk]]
      rw [show (toNat x).testBit ((m + 2) % k) = x ⟨(m + 2) % k, Nat.mod_lt _ hk⟩ from by
        rw [testBit_toNat]; simp [Nat.mod_lt _ hk]]
      by_cases hik : i < k
      · rw [testBit_toNat, testBit_toNat]; simp only [hik, ↓reduceDIte]
        by_cases him : i < m
        · have hnm : ¬ m ≤ i := by omega
          have him1 : i < m + 1 := by omega
          simp [him, him1, hnm]
        · by_cases heq : i = m
          · subst heq
            have hnm : ¬ i < i := Nat.lt_irrefl i
            have hi1 : i < i + 1 := Nat.lt_succ_self i
            simp only [hnm, ↓reduceIte, Bool.false_or, le_refl, decide_true, Bool.true_and,
              Nat.sub_self, hi1]
            change (xor (x ⟨i, hik⟩) (!(x ⟨(i + 1) % k, Nat.mod_lt _ hk⟩) &&
              x ⟨(i + 2) % k, Nat.mod_lt _ hk⟩)).toNat.testBit 0 = stepB hk x ⟨i, hik⟩
            dsimp [stepB]
            cases x ⟨i, hik⟩ <;> cases x ⟨(i + 1) % k, Nat.mod_lt _ hk⟩ <;>
              cases x ⟨(i + 2) % k, Nat.mod_lt _ hk⟩ <;> rfl
          · have hlt : m < i := by omega
            have hnm1 : ¬ i < m + 1 := by omega
            have hmi : m ≤ i := by omega
            have hpos : i - m ≠ 0 := by omega
            simp only [him, hnm1, ↓reduceIte, Bool.false_or, hmi, decide_true, Bool.true_and]
            cases xor (x ⟨m, by omega⟩) (!(x ⟨(m + 1) % k, Nat.mod_lt _ hk⟩) && x ⟨(m + 2) % k, Nat.mod_lt _ hk⟩)
            · simp
            · change (1 : ℕ).testBit (i - m) = false; exact testBit_one_ne hpos
      · have hmi : m ≤ i := by omega
        have hlt_pow : lhs_prev < 2 ^ i := by
          calc lhs_prev < 2 ^ k := toNat_lt _
            _ ≤ 2 ^ i := Nat.pow_le_pow_right (by omega) (Nat.not_lt.mp hik)
        rw [Nat.testBit_lt_two_pow hlt_pow, testBit_toNat]; simp only [hik, ↓reduceDIte]
        simp only [Bool.false_or, hmi, decide_true, Bool.true_and]
        have hpos : i - m ≠ 0 := by omega
        cases xor (x ⟨m, by omega⟩) (!(x ⟨(m + 1) % k, Nat.mod_lt _ hk⟩) && x ⟨(m + 2) % k, Nat.mod_lt _ hk⟩)
        · simp
        · change (1 : ℕ).testBit (i - m) = false; exact testBit_one_ne hpos
    exact Nat.eq_of_testBit_eq hbit

theorem step_toNat {k : ℕ} (hk : 0 < k) (x : Fin k → Bool) :
    (List.range k).foldl (fun acc i =>
      acc ||| ((xor ((toNat x).testBit i)
        (!((toNat x).testBit ((i + 1) % k)) && (toNat x).testBit ((i + 2) % k))).toNat <<< i)) 0 =
    toNat (stepB hk x) := by
  rw [step_toNat_aux hk x k (le_refl k)]
  congr 1; ext j; simp [j.isLt]

def mixB {k : ℕ} (hk : 0 < k) (δ : ℕ) (x : Fin k → Bool) : Fin k → Bool :=
  fun i => xor (xor (x i) (rotB hk δ x i)) (rotB hk (k - δ % k) x i)

theorem mixB_toNat {k : ℕ} (hk : 0 < k) (δ : ℕ) (x : Fin k → Bool) :
    toNat x ^^^ ((toNat x <<< (δ % k)) ||| (toNat x >>> (k - δ % k))) % 2 ^ k ^^^
      ((toNat x <<< ((k - δ % k) % k)) ||| (toNat x >>> (k - (k - δ % k) % k))) % 2 ^ k =
    toNat (mixB hk δ x) := by
  rw [rot_toNat hk δ x, rot_toNat hk (k - δ % k) x, ← xor_toNat, ← xor_toNat]
  rfl

def affId : Bool × Bool := (true, false)

def affComp (f g : Bool × Bool) : Bool × Bool :=
  (f.1 && g.1, xor f.2 (f.1 && g.2))

theorem affComp_assoc (f g h : Bool × Bool) :
    affComp (affComp f g) h = affComp f (affComp g h) := by
  rcases f with ⟨a1, b1⟩; rcases g with ⟨a2, b2⟩; rcases h with ⟨a3, b3⟩
  cases a1 <;> cases b1 <;> cases a2 <;> cases b2 <;> cases a3 <;> cases b3 <;> rfl

theorem affComp_id_left (f : Bool × Bool) : affComp affId f = f := by
  rcases f with ⟨a, b⟩; cases a <;> cases b <;> rfl

theorem affComp_id_right (f : Bool × Bool) : affComp f affId = f := by
  rcases f with ⟨a, b⟩; cases a <;> cases b <;> rfl

def affEval (f : Bool × Bool) (t : Bool) : Bool :=
  xor f.2 (f.1 && t)

theorem affEval_comp (f g : Bool × Bool) (t : Bool) :
    affEval (affComp f g) t = affEval f (affEval g t) := by
  rcases f with ⟨a1, b1⟩; rcases g with ⟨a2, b2⟩
  cases a1 <;> cases b1 <;> cases a2 <;> cases b2 <;> cases t <;> rfl

def stride2Idx (k p : ℕ) (hk : 0 < k) : Fin k :=
  ⟨(2 * p) % k, Nat.mod_lt _ hk⟩

theorem odd_div_two_mul (_hk : 0 < k) (hk_odd : k % 2 = 1) (p : ℕ) :
    (2 * ((p * ((k + 1) / 2)) % k)) % k = p % k := by
  have h2k : 2 * ((k + 1) / 2) = k + 1 := Nat.mul_div_cancel' (by omega : 2 ∣ k + 1)
  calc (2 * ((p * ((k + 1) / 2)) % k)) % k
      = (2 * (p * ((k + 1) / 2))) % k := Nat.mul_mod_mod 2 (p * ((k + 1) / 2)) k
    _ = (p * (2 * ((k + 1) / 2))) % k := by ring_nf
    _ = (p * (k + 1)) % k := by rw [h2k]
    _ = (p * k + p) % k := by ring_nf
    _ = p % k := by rw [Nat.add_mod, Nat.mul_mod_left, Nat.zero_add, Nat.mod_mod]

def stride2Inv (k : ℕ) (hk : 0 < k) (i : Fin k) : Fin k :=
  ⟨(i.val * ((k + 1) / 2)) % k, Nat.mod_lt _ hk⟩

theorem stride2_right_inv {k : ℕ} (hk : 0 < k) (hk_odd : k % 2 = 1) (i : Fin k) :
    stride2Idx k (stride2Inv k hk i).val hk = i := by
  ext; dsimp [stride2Idx, stride2Inv]
  rw [odd_div_two_mul hk hk_odd i.val, Nat.mod_eq_of_lt i.isLt]

theorem stride2_left_inv {k : ℕ} (hk : 0 < k) (hk_odd : k % 2 = 1) (p : Fin k) :
    stride2Inv k hk (stride2Idx k p.val hk) = p := by
  ext; dsimp [stride2Idx, stride2Inv]
  have h1 : ((2 * p.val) % k * ((k + 1) / 2)) % k = (p.val * (2 * ((k + 1) / 2))) % k := by
    rw [Nat.mod_mul_mod]; ring_nf
  have h2k : 2 * ((k + 1) / 2) = k + 1 := by omega
  rw [h1, h2k, show p.val * (k + 1) = p.val * k + p.val by ring, Nat.add_mod, Nat.mul_mod_left,
    Nat.zero_add, Nat.mod_mod, Nat.mod_eq_of_lt p.isLt]

def chiMapAt {k : ℕ} (hk : 0 < k) (y : Fin k → Bool) (p : Fin k) : Bool × Bool :=
  let i := stride2Idx k p.val hk
  (!(y ⟨(i.val + 1) % k, Nat.mod_lt _ hk⟩), y i)

def chiList {k : ℕ} (hk : 0 < k) (y : Fin k → Bool) : List (Bool × Bool) :=
  List.ofFn (chiMapAt hk y)

def invChiAt {k : ℕ} (hk : 0 < k) (y : Fin k → Bool) (p : Fin k) : Bool :=
  let hs := chiList hk y
  let pref := (hs.take p.val).foldl affComp affId
  let suf := (hs.drop p.val).foldr affComp affId
  (affComp suf pref).2

def invChiB {k : ℕ} (hk : 0 < k) (y : Fin k → Bool) : Fin k → Bool :=
  fun i => invChiAt hk y (stride2Inv k hk i)

theorem foldr_affComp_drop (l : List (Bool × Bool)) (p : ℕ) (hp : p < l.length) :
    (l.drop p).foldr affComp affId = affComp l[p] ((l.drop (p + 1)).foldr affComp affId) := by
  rw [List.drop_eq_getElem_cons hp, List.foldr_cons]

theorem foldl_affComp_take_succ (l : List (Bool × Bool)) (p : ℕ) (hp : p < l.length) :
    (l.take (p + 1)).foldl affComp affId = affComp ((l.take p).foldl affComp affId) l[p] := by
  rw [List.take_succ_eq_append_getElem hp, List.foldl_append, List.foldl_cons, List.foldl_nil]

theorem fold_affComp_split (l : List (Bool × Bool)) (init : Bool × Bool) :
    l.foldl affComp init = affComp init (l.foldr affComp affId) := by
  induction l generalizing init with
  | nil => simp [affComp_id_right]
  | cons a t ih =>
    simp only [List.foldl_cons, List.foldr_cons]
    rw [ih (affComp init a), affComp_assoc]

theorem foldl_affComp_all_eq_foldr (l : List (Bool × Bool)) (p : ℕ) :
    affComp ((l.take p).foldl affComp affId) ((l.drop p).foldr affComp affId) =
      l.foldr affComp affId := by
  rw [fold_affComp_split, affComp_id_left]
  induction p generalizing l with
  | zero => simp [affComp_id_left]
  | succ p ih =>
    cases l with
    | nil => simp [affComp_id_left]
    | cons a t =>
      simp only [List.take_succ_cons, List.drop_succ_cons, List.foldr_cons]
      rw [affComp_assoc, ih t]

theorem affComp_fst_eq_all (l : List (Bool × Bool)) :
    (l.foldr affComp affId).1 = l.all (fun x => x.1) := by
  induction l with
  | nil => rfl
  | cons a t ih =>
    simp only [List.foldr_cons, affComp, List.all_cons, ih]

theorem step_stepB_key (x y : Fin k → Bool) (hk : 0 < k) (hy : y = stepB hk x) (i : Fin k) :
    (!(x ⟨(i.val + 1) % k, Nat.mod_lt _ hk⟩) && x ⟨(i.val + 2) % k, Nat.mod_lt _ hk⟩) =
    (!(y ⟨(i.val + 1) % k, Nat.mod_lt _ hk⟩) && x ⟨(i.val + 2) % k, Nat.mod_lt _ hk⟩) := by
  subst hy
  set i1 : Fin k := ⟨(i.val + 1) % k, Nat.mod_lt _ hk⟩
  set i2 : Fin k := ⟨(i.val + 2) % k, Nat.mod_lt _ hk⟩
  have h12 : (⟨(i1.val + 1) % k, Nat.mod_lt _ hk⟩ : Fin k) = i2 := by
    rw [Fin.ext_iff]; dsimp [i1, i2]; rw [Nat.mod_add_mod]
  change (!(x i1) && x i2) = (!(stepB hk x i1) && x i2)
  dsimp [stepB]
  rw [h12]
  cases x i1 <;> cases x i2 <;> cases x ⟨(i1.val + 2) % k, Nat.mod_lt _ hk⟩ <;> rfl

theorem stepB_zero_eq {k : ℕ} (hk : 0 < k) (hk_odd : k % 2 = 1) (x : Fin k → Bool)
    (h : stepB hk x = fun _ => false) : x = fun _ => false := by
  have hrel : ∀ i : Fin k, x i = (!(x ⟨(i.val + 1) % k, Nat.mod_lt _ hk⟩) &&
      x ⟨(i.val + 2) % k, Nat.mod_lt _ hk⟩) := by
    intro i
    have hi := congrFun h i
    dsimp [stepB] at hi
    cases hx : x i <;> cases hb : (!(x ⟨(i.val + 1) % k, Nat.mod_lt _ hk⟩) &&
      x ⟨(i.val + 2) % k, Nat.mod_lt _ hk⟩)
    · rfl
    · rw [hx, hb] at hi; exact absurd hi (by decide)
    · rw [hx, hb] at hi; exact absurd hi (by decide)
    · rfl
  by_contra hne
  have hex : ∃ i, x i = true := by
    by_contra hall
    apply hne; ext i; cases hx : x i with
    | false => rfl
    | true => exact False.elim (hall ⟨i, hx⟩)
  obtain ⟨i0, hi0⟩ := hex
  have haltern : ∀ n : ℕ,
      x ⟨(i0.val + 2 * n) % k, Nat.mod_lt _ hk⟩ = true ∧
      x ⟨(i0.val + 2 * n + 1) % k, Nat.mod_lt _ hk⟩ = false := by
    intro n
    induction n with
    | zero =>
      have hi0' : x ⟨i0.val % k, Nat.mod_lt _ hk⟩ = true := by
        have hfin : (⟨i0.val % k, Nat.mod_lt _ hk⟩ : Fin k) = i0 := Fin.ext (Nat.mod_eq_of_lt i0.isLt)
        rw [hfin]; exact hi0
      have hr := hrel ⟨i0.val % k, Nat.mod_lt _ hk⟩
      rw [hi0'] at hr
      have hfin1 : (⟨((i0.val % k) + 1) % k, Nat.mod_lt _ hk⟩ : Fin k) =
          ⟨(i0.val + 1) % k, Nat.mod_lt _ hk⟩ := by rw [Fin.ext_iff]; dsimp; rw [Nat.mod_add_mod]
      change true = (!(x ⟨((i0.val % k) + 1) % k, Nat.mod_lt _ hk⟩) &&
        x ⟨((i0.val % k) + 2) % k, Nat.mod_lt _ hk⟩) at hr
      rw [hfin1] at hr
      have hfalse : x ⟨(i0.val + 1) % k, Nat.mod_lt _ hk⟩ = false := by
        cases hc : x ⟨(i0.val + 1) % k, Nat.mod_lt _ hk⟩ with
        | false => rfl
        | true => rw [hc] at hr; simp at hr
      exact ⟨by simpa using hi0', hfalse⟩
    | succ n ih =>
      obtain ⟨ht, hf⟩ := ih
      have hr := hrel ⟨(i0.val + 2 * n) % k, Nat.mod_lt _ hk⟩
      rw [ht] at hr
      have h2n1 : (⟨((i0.val + 2 * n) % k + 1) % k, Nat.mod_lt _ hk⟩ : Fin k) =
          ⟨(i0.val + 2 * n + 1) % k, Nat.mod_lt _ hk⟩ := by
        rw [Fin.ext_iff]; dsimp; rw [Nat.mod_add_mod]
      have h2n2 : (⟨((i0.val + 2 * n) % k + 2) % k, Nat.mod_lt _ hk⟩ : Fin k) =
          ⟨(i0.val + 2 * (n + 1)) % k, Nat.mod_lt _ hk⟩ := by
        rw [Fin.ext_iff]; dsimp; rw [Nat.mod_add_mod]; ring_nf
      change true = (!(x ⟨((i0.val + 2 * n) % k + 1) % k, Nat.mod_lt _ hk⟩) &&
        x ⟨((i0.val + 2 * n) % k + 2) % k, Nat.mod_lt _ hk⟩) at hr
      rw [h2n1, h2n2, hf] at hr
      have h2 : x ⟨(i0.val + 2 * (n + 1)) % k, Nat.mod_lt _ hk⟩ = true := by
        cases hc : x ⟨(i0.val + 2 * (n + 1)) % k, Nat.mod_lt _ hk⟩ with
        | true => rfl
        | false => rw [hc] at hr; simp at hr
      have hr2 := hrel ⟨(i0.val + 2 * (n + 1)) % k, Nat.mod_lt _ hk⟩
      rw [h2] at hr2
      have hmod2 : (⟨((i0.val + 2 * (n + 1)) % k + 1) % k, Nat.mod_lt _ hk⟩ : Fin k) =
          ⟨(i0.val + 2 * (n + 1) + 1) % k, Nat.mod_lt _ hk⟩ := by
        rw [Fin.ext_iff]; dsimp; rw [Nat.mod_add_mod]
      change true = (!(x ⟨((i0.val + 2 * (n + 1)) % k + 1) % k, Nat.mod_lt _ hk⟩) &&
        x ⟨((i0.val + 2 * (n + 1)) % k + 2) % k, Nat.mod_lt _ hk⟩) at hr2
      rw [hmod2] at hr2
      have hf2 : x ⟨(i0.val + 2 * (n + 1) + 1) % k, Nat.mod_lt _ hk⟩ = false := by
        cases hc : x ⟨(i0.val + 2 * (n + 1) + 1) % k, Nat.mod_lt _ hk⟩ with
        | false => rfl
        | true => rw [hc] at hr2; simp at hr2
      exact ⟨h2, hf2⟩
  have hk2 := haltern ((k - 1) / 2)
  have heq_idx : (⟨(i0.val + 2 * ((k - 1) / 2) + 1) % k, Nat.mod_lt _ hk⟩ : Fin k) = i0 := by
    rw [Fin.ext_iff]; dsimp
    have : 2 * ((k - 1) / 2) + 1 = k := by omega
    rw [Nat.add_assoc, this, Nat.add_mod_right, Nat.mod_eq_of_lt i0.isLt]
  rw [heq_idx, hi0] at hk2
  exact absurd hk2.2 (by decide)

theorem invChiB_zero {k : ℕ} (hk : 0 < k) (y : Fin k → Bool) (hy : ∀ q : Fin k, y q = false) :
    invChiB hk y = fun _ => false := by
  ext i
  dsimp [invChiB, invChiAt]
  have hs_snd : ∀ g ∈ chiList hk y, g.2 = false := by
    intro g hg
    simp only [chiList, List.mem_ofFn] at hg
    obtain ⟨p, rfl⟩ := hg
    exact hy _
  have htake : ∀ n (l : List (Bool × Bool)), (∀ g ∈ l, g.2 = false) →
      ((l.take n).foldl affComp affId).2 = false := by
    intro n l hl
    have hfold : ∀ (ll : List (Bool × Bool)) (init : Bool × Bool),
        init.2 = false → (∀ g ∈ ll, g.2 = false) → (ll.foldl affComp init).2 = false := by
      intro ll
      induction ll with
      | nil => intro init h _; exact h
      | cons a t ih =>
        intro init h1 h2
        apply ih
        · dsimp [affComp]; simp [h1, h2 a List.mem_cons_self]
        · intro g hg; exact h2 g (List.mem_cons_of_mem _ hg)
    exact hfold _ _ rfl (fun g hg => hl g (List.mem_of_mem_take hg))
  have hdrop : ∀ n (l : List (Bool × Bool)), (∀ g ∈ l, g.2 = false) →
      ((l.drop n).foldr affComp affId).2 = false := by
    intro n l hl
    have hfold : ∀ (ll : List (Bool × Bool)),
        (∀ g ∈ ll, g.2 = false) → (ll.foldr affComp affId).2 = false := by
      intro ll
      induction ll with
      | nil => intro _; rfl
      | cons a t ih =>
        intro h2
        dsimp [affComp]
        simp [h2 a List.mem_cons_self, ih (fun g hg => h2 g (List.mem_cons_of_mem _ hg))]
    exact hfold _ (fun g hg => hl g (List.mem_of_mem_drop hg))
  dsimp [affComp]
  rw [hdrop _ _ hs_snd, htake _ _ hs_snd]
  simp

theorem foldr_affComp_append (l1 l2 : List (Bool × Bool)) :
    (l1 ++ l2).foldr affComp affId =
      affComp (l1.foldr affComp affId) (l2.foldr affComp affId) := by
  induction l1 with
  | nil => simp [affComp_id_left]
  | cons a t ih =>
    simp only [List.cons_append, List.foldr_cons, ih, affComp_assoc]

theorem invChiB_stepB {k : ℕ} (hk : 0 < k) (hk_odd : k % 2 = 1) (x : Fin k → Bool) :
    invChiB hk (stepB hk x) = x := by
  by_cases hy : ∃ q : Fin k, stepB hk x q = true
  · set y := stepB hk x
    have hstep_rec : ∀ p : Fin k, x (stride2Idx k p.val hk) =
        affEval (chiMapAt hk y p) (x (stride2Idx k (⟨(p.val + 1) % k, Nat.mod_lt _ hk⟩ : Fin k).val hk)) := by
      intro p
      set i := stride2Idx k p.val hk
      have hi2 : stride2Idx k (⟨(p.val + 1) % k, Nat.mod_lt _ hk⟩ : Fin k).val hk =
          ⟨(i.val + 2) % k, Nat.mod_lt _ hk⟩ := by
        rw [Fin.ext_iff]; dsimp [stride2Idx, i]
        rw [Nat.mul_mod_mod, show 2 * (p.val + 1) = 2 * p.val + 2 by ring,
          Nat.add_mod (2 * p.val % k), Nat.mod_mod, ← Nat.add_mod]
      rw [hi2]
      dsimp [affEval, chiMapAt]
      have hk_key := step_stepB_key x y hk rfl i
      have hb_eq : (!(y ⟨(i.val + 1) % k, Nat.mod_lt _ hk⟩) &&
          x ⟨(i.val + 2) % k, Nat.mod_lt _ hk⟩) =
          (!(x ⟨(i.val + 1) % k, Nat.mod_lt _ hk⟩) &&
          x ⟨(i.val + 2) % k, Nat.mod_lt _ hk⟩) := hk_key.symm
      change x i = xor (y i) (!(y ⟨(i.val + 1) % k, Nat.mod_lt _ hk⟩) &&
        x ⟨(i.val + 2) % k, Nat.mod_lt _ hk⟩)
      rw [hb_eq]
      dsimp [y, stepB]
      cases x i <;> cases (!(x ⟨(i.val + 1) % k, Nat.mod_lt _ hk⟩) &&
        x ⟨(i.val + 2) % k, Nat.mod_lt _ hk⟩) <;> rfl
    have hiter : ∀ (n : ℕ) (p : Fin k),
        x (stride2Idx k p.val hk) =
        affEval (((List.range n).map (fun d =>
          chiMapAt hk y ⟨(p.val + d) % k, Nat.mod_lt _ hk⟩)).foldr affComp affId)
          (x (stride2Idx k (⟨(p.val + n) % k, Nat.mod_lt _ hk⟩ : Fin k).val hk)) := by
      intro n
      induction n with
      | zero =>
        intro p
        have hp0 : (⟨(p.val + 0) % k, Nat.mod_lt _ hk⟩ : Fin k) = p := by
          rw [Fin.ext_iff]; dsimp; exact Nat.mod_eq_of_lt p.isLt
        rw [hp0, List.range_zero, List.map_nil, List.foldr_nil]
        simp [affEval, affId]
      | succ n ih =>
        intro p
        rw [hstep_rec p, ih ⟨(p.val + 1) % k, Nat.mod_lt _ hk⟩]
        have hmod : (⟨((p.val + 1) % k + n) % k, Nat.mod_lt _ hk⟩ : Fin k) =
            ⟨(p.val + (n + 1)) % k, Nat.mod_lt _ hk⟩ := by
          rw [Fin.ext_iff]; dsimp; rw [Nat.mod_add_mod]; ring_nf
        rw [hmod, List.range_succ_eq_map, List.map_cons, List.map_map, List.foldr_cons, affEval_comp]
        congr 2
        · simp [Nat.mod_eq_of_lt p.isLt]
        · congr 1
          apply List.map_congr_left
          intro d _
          congr 1; rw [Fin.ext_iff]; dsimp [Function.comp]
          rw [Nat.mod_add_mod, Nat.add_assoc, Nat.add_comm 1 d]
    ext i
    set p := stride2Inv k hk i
    have hi_eq : stride2Idx k p.val hk = i := stride2_right_inv hk hk_odd i
    have hk_eq := hiter k p
    have hwrap : (⟨(p.val + k) % k, Nat.mod_lt _ hk⟩ : Fin k) = p := by
      rw [Fin.ext_iff]; dsimp; rw [Nat.add_mod_right, Nat.mod_eq_of_lt p.isLt]
    rw [hwrap, hi_eq] at hk_eq
    set hs := chiList hk y
    have hlen : hs.length = k := List.length_ofFn
    have hcyc_list : (List.range k).map (fun d =>
        chiMapAt hk y ⟨(p.val + d) % k, Nat.mod_lt _ hk⟩) =
        hs.drop p.val ++ hs.take p.val := by
      apply List.ext_getElem
      · simp [hlen]
      · intro d hd1 hd2
        simp only [List.getElem_map, List.getElem_range]
        by_cases hdk : d < k - p.val
        · have hd_drop : d < (hs.drop p.val).length := by simp [hlen]; omega
          rw [List.getElem_append_left hd_drop, List.getElem_drop]
          have hpd : p.val + d < k := by omega
          have hpd_len : p.val + d < hs.length := by rw [hlen]; exact hpd
          have hget : hs[p.val + d]'hpd_len = chiMapAt hk y ⟨p.val + d, hpd⟩ := by
            simp [hs, chiList]
          rw [hget]
          congr 1; rw [Fin.ext_iff]; dsimp; exact Nat.mod_eq_of_lt hpd
        · have hd_drop : ¬ d < (hs.drop p.val).length := by simp [hlen]; omega
          rw [List.getElem_append_right (Nat.not_lt.mp hd_drop), List.getElem_take]
          have hlen_drop : (hs.drop p.val).length = k - p.val := by simp [hlen]
          have hidx : d - (k - p.val) < k := by simp at hd1; omega
          have hidx' : d - (hs.drop p.val).length < k := by rw [hlen_drop]; exact hidx
          have hidx_len : d - (hs.drop p.val).length < hs.length := by rw [hlen]; exact hidx'
          have hget : hs[d - (hs.drop p.val).length]'hidx_len =
              chiMapAt hk y ⟨d - (hs.drop p.val).length, hidx'⟩ := by
            simp [hs, chiList]
          rw [hget]
          congr 1; rw [Fin.ext_iff]; dsimp
          rw [hlen_drop]
          have : p.val + d = k + (d - (k - p.val)) := by omega
          rw [this, Nat.add_mod_left, Nat.mod_eq_of_lt hidx]
    have hcyc : ((List.range k).map (fun d =>
        chiMapAt hk y ⟨(p.val + d) % k, Nat.mod_lt _ hk⟩)).foldr affComp affId =
        affComp ((hs.drop p.val).foldr affComp affId) ((hs.take p.val).foldl affComp affId) := by
      rw [hcyc_list, foldr_affComp_append]
      congr 1
      rw [fold_affComp_split, affComp_id_left]
    set M_p := affComp ((hs.drop p.val).foldr affComp affId) ((hs.take p.val).foldl affComp affId)
    have hMp_fst : M_p.1 = false := by
      have h1 : M_p.1 = (((hs.take p.val).foldl affComp affId).1 &&
          ((hs.drop p.val).foldr affComp affId).1) :=
        Bool.and_comm _ _
      have heq := congrArg Prod.fst (foldl_affComp_all_eq_foldr hs p.val)
      have hall : (hs.foldr affComp affId).1 = false := by
        rw [affComp_fst_eq_all]
        obtain ⟨q, hq⟩ := hy
        let q1 : Fin k := ⟨(q.val + k - 1) % k, Nat.mod_lt _ hk⟩
        let r := stride2Inv k hk q1
        have hr : (chiMapAt hk y r).1 = false := by
          dsimp [chiMapAt, r]
          have hst : (stride2Idx k (stride2Inv k hk q1).val hk).val = q1.val :=
            congrArg Fin.val (stride2_right_inv hk hk_odd q1)
          have hmod : (q1.val + 1) % k = q.val := by
            dsimp [q1]; rw [Nat.mod_add_mod]
            have : q.val + k - 1 + 1 = q.val + k := by omega
            rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt q.isLt]
          have hfin : (⟨((stride2Idx k (stride2Inv k hk q1).val hk).val + 1) % k,
              Nat.mod_lt _ hk⟩ : Fin k) = q := by
            rw [Fin.ext_iff]; dsimp; rw [hst, hmod]
          rw [hfin, hq]; rfl
        cases htrue : hs.all (fun x => x.1) with
        | false => rfl
        | true =>
          have hmem : chiMapAt hk y r ∈ hs := by
            simp only [hs, chiList, List.mem_ofFn]; exact ⟨r, rfl⟩
          have := List.all_eq_true.mp htrue _ hmem
          rw [hr] at this; exact absurd this (by decide)
      rw [h1]
      exact heq.trans hall
    rw [hcyc] at hk_eq
    have hev : affEval M_p (x i) = M_p.2 := by
      dsimp [affEval]; rw [hMp_fst]; simp
    rw [hk_eq, hev]
    rfl
  · have hy0 : ∀ q : Fin k, stepB hk x q = false := by
      intro q; cases hq : stepB hk x q with
      | false => rfl
      | true => exact False.elim (hy ⟨q, hq⟩)
    have hx0 := stepB_zero_eq hk hk_odd x (funext hy0)
    rw [invChiB_zero hk _ hy0, hx0]

theorem stepB_invChiB {k : ℕ} (hk : 0 < k) (hk_odd : k % 2 = 1) (y : Fin k → Bool) :
    stepB hk (invChiB hk y) = y := by
  have hinj : Function.Injective (stepB hk) :=
    Function.LeftInverse.injective (invChiB_stepB hk hk_odd)
  have hsurj : Function.Surjective (stepB hk) := Finite.injective_iff_surjective.mp hinj
  obtain ⟨x, rfl⟩ := hsurj y
  rw [invChiB_stepB hk hk_odd]

def inv3Pos (k : ℕ) : ℕ :=
  if k % 6 = 1 then 4 * (k / 6) + 1 else 2 * (k / 6) + 2

def inv3dConst (k δ : ℕ) : ℕ :=
  if δ = 1 then inv3Pos k else (inv3Pos k * ((k + 1) / 2)) % k

theorem inv3dConst_spec {k δ : ℕ} (hk6 : k % 6 = 1 ∨ k % 6 = 5) (hk5 : 5 ≤ k)
    (hδ : δ = 1 ∨ δ = 2) :
    (3 * δ * inv3dConst k δ) % k = 1 := by
  have hpos : (3 * inv3Pos k) % k = 1 := by
    dsimp [inv3Pos]
    rcases hk6 with h1 | h5
    · simp only [h1, ↓reduceIte]
      have hq : k = 6 * (k / 6) + 1 := by omega
      have : 3 * (4 * (k / 6) + 1) = 2 * k + 1 := by omega
      rw [this, Nat.add_mod, show 2 * k % k = 0 from Nat.mul_mod_left 2 k, Nat.zero_add,
        Nat.mod_mod, Nat.mod_eq_of_lt (by omega)]
    · have hne1 : k % 6 ≠ 1 := by omega
      simp only [hne1, ↓reduceIte]
      have hq : k = 6 * (k / 6) + 5 := by omega
      have : 3 * (2 * (k / 6) + 2) = k + 1 := by omega
      rw [this, Nat.add_mod, Nat.mod_self, Nat.zero_add, Nat.mod_mod, Nat.mod_eq_of_lt (by omega)]
  rcases hδ with rfl | rfl
  · simpa [inv3dConst] using hpos
  · simp only [inv3dConst, show (2 : ℕ) ≠ 1 by decide, ↓reduceIte]
    have h2 : 2 * ((k + 1) / 2) = k + 1 := Nat.mul_div_cancel' (by omega : 2 ∣ k + 1)
    calc (3 * 2 * ((inv3Pos k * ((k + 1) / 2)) % k)) % k
        = (3 * 2 * (inv3Pos k * ((k + 1) / 2))) % k := Nat.mul_mod_mod _ _ k
      _ = ((3 * inv3Pos k) * (2 * ((k + 1) / 2))) % k := by ring_nf
      _ = ((3 * inv3Pos k) * (k + 1)) % k := by rw [h2]
      _ = (((3 * inv3Pos k) % k) * ((k + 1) % k)) % k := Nat.mul_mod _ _ k
      _ = (1 * (1 % k)) % k := by
        rw [hpos]
        have hk1 : (k + 1) % k = 1 % k := by rw [Nat.add_mod, Nat.mod_self, Nat.zero_add, Nat.mod_mod]
        rw [hk1]
      _ = 1 := by rw [Nat.one_mul, Nat.mod_mod, Nat.mod_eq_of_lt (by omega)]

def m3dIdx (k δ p : ℕ) (hk : 0 < k) : Fin k :=
  ⟨(3 * δ * p) % k, Nat.mod_lt _ hk⟩

def m3dInv (k δ : ℕ) (hk : 0 < k) (i : Fin k) : Fin k :=
  ⟨(i.val * inv3dConst k δ) % k, Nat.mod_lt _ hk⟩

theorem m3d_right_inv {k δ : ℕ} (hk : 0 < k) (hk6 : k % 6 = 1 ∨ k % 6 = 5) (hk5 : 5 ≤ k)
    (hδ : δ = 1 ∨ δ = 2) (i : Fin k) :
    m3dIdx k δ (m3dInv k δ hk i).val hk = i := by
  ext; dsimp [m3dIdx, m3dInv]
  calc (3 * δ * ((i.val * inv3dConst k δ) % k)) % k
      = (3 * δ * (i.val * inv3dConst k δ)) % k := Nat.mul_mod_mod _ _ k
    _ = (i.val * (3 * δ * inv3dConst k δ)) % k := by ring_nf
    _ = ((i.val % k) * ((3 * δ * inv3dConst k δ) % k)) % k := Nat.mul_mod _ _ k
    _ = (i.val % k * 1) % k := by rw [inv3dConst_spec hk6 hk5 hδ]
    _ = i.val := by rw [Nat.mul_one, Nat.mod_mod, Nat.mod_eq_of_lt i.isLt]

def mixDiffAt {k : ℕ} (hk : 0 < k) (δ : ℕ) (y : Fin k → Bool) (p : Fin k) : Bool :=
  xor (y ⟨(3 * δ * p.val + δ) % k, Nat.mod_lt _ hk⟩)
      (y ⟨(3 * δ * p.val + 2 * δ) % k, Nat.mod_lt _ hk⟩)

def mixPref {k : ℕ} (hk : 0 < k) (δ : ℕ) (y : Fin k → Bool) (p : ℕ) : Bool :=
  ((List.range p).map (fun j => mixDiffAt hk δ y ⟨j % k, Nat.mod_lt _ hk⟩)).foldl xor false

def invMixB {k : ℕ} (hk : 0 < k) (δ : ℕ) (y : Fin k → Bool) : Fin k → Bool :=
  if k < 5 then y
  else
    let pPos : ℕ := inv3Pos k % k
    let pNeg : ℕ := (k - pPos) % k
    let x0 : Bool := xor (xor (y ⟨0, hk⟩) (mixPref hk δ y pPos)) (mixPref hk δ y pNeg)
    fun i => xor x0 (mixPref hk δ y (m3dInv k δ hk i).val)

theorem mixPref_succ {k : ℕ} (hk : 0 < k) (δ : ℕ) (y : Fin k → Bool) (p : ℕ) :
    mixPref hk δ y (p + 1) = xor (mixPref hk δ y p) (mixDiffAt hk δ y ⟨p % k, Nat.mod_lt _ hk⟩) := by
  dsimp [mixPref]
  rw [List.range_succ, List.map_append, List.map_singleton, List.foldl_append, List.foldl_cons, List.foldl_nil]

theorem mixB_one {k : ℕ} (hk : 0 < k) (hk1 : k = 1) (δ : ℕ) (x : Fin k → Bool) :
    mixB hk δ x = x := by
  subst hk1
  ext i
  have hi : i = ⟨0, hk⟩ := Fin.ext (by omega)
  subst hi
  dsimp [mixB, rotB]
  have h0 : ∀ a : ℕ, (⟨a % 1, Nat.mod_lt _ hk⟩ : Fin 1) = ⟨0, hk⟩ := fun a => Fin.ext (Nat.mod_one a)
  rw [h0, h0]
  cases x ⟨0, hk⟩ <;> simp

theorem invMixB_mixB {k : ℕ} (hk : 0 < k) (hk6 : k % 6 = 1 ∨ k % 6 = 5)
    (δ : ℕ) (hδ : δ = 1 ∨ δ = 2) (x : Fin k → Bool) :
    invMixB hk δ (mixB hk δ x) = x := by
  by_cases hk5 : k < 5
  · have hk1 : k = 1 := by omega
    dsimp [invMixB]
    simp only [hk5, ↓reduceIte]
    exact mixB_one hk hk1 δ x
  · have h5 : 5 ≤ k := Nat.not_lt.mp hk5
    have hδk : δ % k = δ := Nat.mod_eq_of_lt (by omega)
    have hdiff : ∀ p : ℕ, mixDiffAt hk δ (mixB hk δ x) ⟨p % k, Nat.mod_lt _ hk⟩ =
        xor (x (m3dIdx k δ p hk)) (x (m3dIdx k δ (p + 1) hk)) := by
      intro p
      dsimp [mixDiffAt, mixB, rotB, m3dIdx]
      have hmod_p : (3 * δ * (p % k)) % k = (3 * δ * p) % k := Nat.mul_mod_mod _ _ k
      have h0 : ∀ s t : ℕ, ((s % k) + k - t % k) % k = (s + k - t % k) % k := by
        intro s t
        have htm : t % k < k := Nat.mod_lt t hk
        rw [Nat.add_sub_assoc (by omega), Nat.mod_add_mod, ← Nat.add_sub_assoc (by omega)]
      have hkmd : (k - δ) % k = k - δ := Nat.mod_eq_of_lt (by omega)
      have h_i1 : (⟨((3 * δ * (p % k) + δ) % k + k - δ % k) % k, Nat.mod_lt _ hk⟩ : Fin k) =
          ⟨(3 * δ * p) % k, Nat.mod_lt _ hk⟩ := by
        rw [Fin.ext_iff]; dsimp; rw [h0, hδk]
        rw [show 3 * δ * (p % k) + δ + k - δ = 3 * δ * (p % k) + k by omega]
        rw [Nat.add_mod, Nat.mod_self, Nat.add_zero, Nat.mod_mod]; exact hmod_p
      have h_i2 : (⟨((3 * δ * (p % k) + δ) % k + k - (k - δ % k) % k) % k, Nat.mod_lt _ hk⟩ : Fin k) =
          ⟨(3 * δ * p + 2 * δ) % k, Nat.mod_lt _ hk⟩ := by
        rw [Fin.ext_iff]; dsimp; rw [h0, hδk, hkmd]
        have : 3 * δ * (p % k) + δ + k - (k - δ) = (3 * δ * (p % k) + 2 * δ) := by omega
        rw [this, Nat.add_mod, Nat.mul_mod_mod, ← Nat.add_mod]
      have h_i3 : (⟨((3 * δ * (p % k) + 2 * δ) % k + k - δ % k) % k, Nat.mod_lt _ hk⟩ : Fin k) =
          ⟨(3 * δ * p + δ) % k, Nat.mod_lt _ hk⟩ := by
        rw [Fin.ext_iff]; dsimp; rw [h0, hδk]
        have : 3 * δ * (p % k) + 2 * δ + k - δ = k + (3 * δ * (p % k) + δ) := by omega
        rw [this, Nat.add_mod_left, Nat.add_mod, Nat.mul_mod_mod, ← Nat.add_mod]
      have h_i4 : (⟨((3 * δ * (p % k) + 2 * δ) % k + k - (k - δ % k) % k) % k, Nat.mod_lt _ hk⟩ : Fin k) =
          ⟨(3 * δ * (p + 1)) % k, Nat.mod_lt _ hk⟩ := by
        rw [Fin.ext_iff]; dsimp; rw [h0, hδk, hkmd]
        have : 3 * δ * (p % k) + 2 * δ + k - (k - δ) = 3 * δ * (p % k) + 3 * δ := by omega
        rw [this, show 3 * δ * (p % k) + 3 * δ = 3 * δ * ((p % k) + 1) by ring,
          show 3 * δ * (p + 1) = 3 * δ * p + 3 * δ by ring]
        rw [Nat.mul_add, Nat.mul_one, Nat.add_mod, Nat.mul_mod_mod, ← Nat.add_mod]
      have h_j1 : (⟨(3 * δ * (p % k) + δ) % k, Nat.mod_lt _ hk⟩ : Fin k) =
          ⟨(3 * δ * p + δ) % k, Nat.mod_lt _ hk⟩ := by
        rw [Fin.ext_iff]; dsimp; rw [Nat.add_mod, Nat.mul_mod_mod, ← Nat.add_mod]
      have h_j2 : (⟨(3 * δ * (p % k) + 2 * δ) % k, Nat.mod_lt _ hk⟩ : Fin k) =
          ⟨(3 * δ * p + 2 * δ) % k, Nat.mod_lt _ hk⟩ := by
        rw [Fin.ext_iff]; dsimp; rw [Nat.add_mod, Nat.mul_mod_mod, ← Nat.add_mod]
      rw [h_i1, h_i2, h_i3, h_i4, h_j1, h_j2]
      cases x ⟨(3 * δ * p) % k, Nat.mod_lt _ hk⟩ <;>
        cases x ⟨(3 * δ * p + δ) % k, Nat.mod_lt _ hk⟩ <;>
        cases x ⟨(3 * δ * p + 2 * δ) % k, Nat.mod_lt _ hk⟩ <;>
        cases x ⟨(3 * δ * (p + 1)) % k, Nat.mod_lt _ hk⟩ <;> rfl
    have hpref : ∀ p : ℕ, mixPref hk δ (mixB hk δ x) p =
        xor (x ⟨0, hk⟩) (x (m3dIdx k δ p hk)) := by
      intro p
      induction p with
      | zero =>
        simp [mixPref, m3dIdx]
      | succ p ih =>
        rw [mixPref_succ, ih, hdiff p]
        cases x ⟨0, hk⟩ <;> cases x (m3dIdx k δ p hk) <;> cases x (m3dIdx k δ (p + 1) hk) <;> rfl
    have hpPos : (3 * δ * (inv3Pos k % k)) % k = δ := by
      have h3p : (3 * inv3Pos k) % k = 1 := by
        have := inv3dConst_spec hk6 h5 (Or.inl rfl)
        simpa [inv3dConst] using this
      calc (3 * δ * (inv3Pos k % k)) % k
          = (3 * δ * inv3Pos k) % k := Nat.mul_mod_mod _ _ k
        _ = (δ * (3 * inv3Pos k)) % k := by ring_nf
        _ = ((δ % k) * ((3 * inv3Pos k) % k)) % k := Nat.mul_mod _ _ k
        _ = δ := by rw [h3p, hδk, Nat.mul_one, Nat.mod_eq_of_lt (by omega)]
    have hpNeg : (3 * δ * ((k - inv3Pos k % k) % k)) % k = k - δ := by
      have hp_lt : inv3Pos k % k < k := Nat.mod_lt _ hk
      have hp_pos_ne : 0 < inv3Pos k % k := by
        by_contra hle
        have h0 : inv3Pos k % k = 0 := by omega
        have hp := hpPos
        rw [h0, Nat.mul_zero, Nat.zero_mod] at hp
        omega
      have h1 : 3 * δ * (inv3Pos k % k) + 3 * δ * (k - inv3Pos k % k) = (3 * δ) * k := by
        rw [← Nat.mul_add, Nat.add_sub_of_le (Nat.le_of_lt hp_lt)]
      have hsum : ((3 * δ * (inv3Pos k % k)) % k + (3 * δ * (k - inv3Pos k % k)) % k) % k = 0 := by
        rw [← Nat.add_mod, h1, Nat.mul_mod_left]
      rw [hpPos] at hsum
      rw [Nat.mul_mod_mod]
      have hlt : (3 * δ * (k - inv3Pos k % k)) % k < k := Nat.mod_lt _ hk
      have hnz : (3 * δ * (k - inv3Pos k % k)) % k ≠ 0 := by
        intro hz
        rw [hz, Nat.add_zero, Nat.mod_eq_of_lt (by omega)] at hsum
        omega
      obtain ⟨m, hm⟩ := Nat.dvd_of_mod_eq_zero hsum
      have hm0 : m ≠ 0 := by
        intro hz; rw [hz, Nat.mul_zero] at hm; omega
      have hm2 : m < 2 := by
        by_contra h2
        have hge : 2 ≤ m := by omega
        have hkm : 2 * k ≤ k * m := by linarith [Nat.mul_le_mul_left k hge]
        omega
      have hm1 : m = 1 := by omega
      rw [hm1, Nat.mul_one] at hm
      omega
    dsimp [invMixB]
    simp only [hk5, ↓reduceIte]
    ext i
    rw [hpref, hpref, hpref, m3d_right_inv hk hk6 h5 hδ i]
    have hm_pos : m3dIdx k δ (inv3Pos k % k) hk = ⟨δ, by omega⟩ := Fin.ext hpPos
    have hm_neg : m3dIdx k δ ((k - inv3Pos k % k) % k) hk = ⟨k - δ, by omega⟩ := Fin.ext hpNeg
    have hm_0 : mixB hk δ x ⟨0, hk⟩ =
        xor (xor (x ⟨0, hk⟩) (x ⟨k - δ, by omega⟩)) (x ⟨δ, by omega⟩) := by
      dsimp [mixB, rotB]
      have hkmd : (k - δ) % k = k - δ := Nat.mod_eq_of_lt (by omega)
      have hr1 : (⟨(0 + k - δ % k) % k, Nat.mod_lt _ hk⟩ : Fin k) = ⟨k - δ, by omega⟩ := by
        rw [Fin.ext_iff]; dsimp; rw [Nat.zero_add, hδk, hkmd]
      have hr2 : (⟨(0 + k - (k - δ % k) % k) % k, Nat.mod_lt _ hk⟩ : Fin k) = ⟨δ, by omega⟩ := by
        rw [Fin.ext_iff]; dsimp; rw [Nat.zero_add, hδk, hkmd]
        rw [show k - (k - δ) = δ by omega, hδk]
      rw [hr1, hr2]
    rw [hm_pos, hm_neg, hm_0]
    cases x ⟨0, hk⟩ <;> cases x ⟨k - δ, by omega⟩ <;> cases x ⟨δ, by omega⟩ <;> cases x i <;> rfl

theorem mixB_invMixB {k : ℕ} (hk : 0 < k) (hk6 : k % 6 = 1 ∨ k % 6 = 5)
    (δ : ℕ) (hδ : δ = 1 ∨ δ = 2) (y : Fin k → Bool) :
    mixB hk δ (invMixB hk δ y) = y := by
  have hinj : Function.Injective (mixB hk δ) :=
    Function.LeftInverse.injective (invMixB_mixB hk hk6 δ hδ)
  have hsurj : Function.Surjective (mixB hk δ) := Finite.injective_iff_surjective.mp hinj
  obtain ⟨x, rfl⟩ := hsurj y
  rw [invMixB_mixB hk hk6 δ hδ]

end CipherCore

section CipherRun

def runB {k : Nat} (hk : 0 < k) (r : Nat) (masks : Nat → Fin k → Bool)
    (col : Bool) (key name : Fin k → Bool) : Fin k → Bool :=
  let gap : Nat := if col then 2 else 1
  (List.range r).foldl
    (fun z j =>
      let mixed := mixB hk gap z
      fun i => xor (xor (stepB hk mixed i) (rotB hk (if col then 3 * (j + 1) + 1 else 2 * j) key i))
        (masks (if col then r + j else j) i))
    (fun i => xor (rotB hk (if col then 3 else 1) key i) (name i))

def invRoundB {k : Nat} (hk : 0 < k) (r : Nat) (masks : Nat → Fin k → Bool)
    (col : Bool) (j : Nat) (key y : Fin k → Bool) : Fin k → Bool :=
  let gap : Nat := if col then 2 else 1
  invMixB hk gap (invChiB hk (fun i =>
    xor (xor (y i) (rotB hk (if col then 3 * (j + 1) + 1 else 2 * j) key i))
      (masks (if col then r + j else j) i)))

def invRunB {k : Nat} (hk : 0 < k) (r : Nat) (masks : Nat → Fin k → Bool)
    (col : Bool) (key out : Fin k → Bool) : Fin k → Bool :=
  let st0 := (List.range r).reverse.foldl (fun st j => invRoundB hk r masks col j key st) out
  fun i => xor (rotB hk (if col then 3 else 1) key i) (st0 i)

theorem foldl_range_toNat {k : Nat} (r : Nat)
    (fn : Nat → Nat → Nat) (fb : (Fin k → Bool) → Nat → (Fin k → Bool))
    (init : Fin k → Bool)
    (hstep : ∀ (x : Fin k → Bool) (idx : Nat), fn (toNat x) idx = toNat (fb x idx)) :
    (List.range r).foldl fn (toNat init) = toNat ((List.range r).foldl fb init) := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_append, List.foldl_cons, List.foldl_nil,
      List.foldl_cons, List.foldl_nil, ih, hstep]

theorem runB_toNat {k : Nat} (hk : 0 < k) (r : Nat) (masks : Nat → Fin (2 ^ k))
    (col : Bool) (key name : Fin k → Bool) :
    let N := 2 ^ k
    let rot := fun (shift x : Nat) => ((x <<< (shift % k)) ||| (x >>> (k - shift % k))) % N
    let chi := fun (x : Nat) => (List.range k).foldl (fun (acc i : Nat) =>
      acc ||| ((xor (x.testBit i) (!(x.testBit ((i + 1) % k)) && x.testBit ((i + 2) % k))).toNat <<< i)) 0
    let gap : Nat := if col then 2 else 1
    (List.range r).foldl (fun z j =>
      let mixed := z ^^^ rot gap z ^^^ rot (k - gap % k) z
      chi mixed ^^^ rot (if col then 3 * (j + 1) + 1 else 2 * j) (toNat key) ^^^
        (masks (if col then r + j else j)).val) (rot (if col then 3 else 1) (toNat key) ^^^ toNat name) =
    toNat (runB hk r (fun j => ofNat k (masks j).val) col key name) := by
  intro N rot chi gap
  have hinit : rot (if col then 3 else 1) (toNat key) ^^^ toNat name =
      toNat (fun i => xor (rotB hk (if col then 3 else 1) key i) (name i)) := by
    dsimp only [rot, N]
    rw [rot_toNat hk _ key, ← xor_toNat]
  dsimp only [runB]
  rw [hinit]
  apply foldl_range_toNat
  intro x j
  have hm : toNat x ^^^ rot gap (toNat x) ^^^ rot (k - gap % k) (toNat x) =
      toNat (mixB hk gap x) := mixB_toNat hk gap x
  dsimp only [rot, chi, N] at hm ⊢
  rw [hm, step_toNat hk (mixB hk gap x), rot_toNat hk _ key]
  have hmask : (masks (if col then r + j else j)).val =
      toNat (ofNat k (masks (if col then r + j else j)).val) :=
    (toNat_ofNat (masks (if col then r + j else j)).isLt).symm
  conv_lhs => rw [hmask]
  rw [← xor_toNat, ← xor_toNat]

theorem invRoundB_spec {k : Nat} (hk : 0 < k) (hk6 : k % 6 = 1 ∨ k % 6 = 5)
    (r : Nat) (masks : Nat → Fin k → Bool) (col : Bool) (j : Nat) (key st : Fin k → Bool) :
    let gap : Nat := if col then 2 else 1
    invRoundB hk r masks col j key (fun i =>
      xor (xor (stepB hk (mixB hk gap st) i)
        (rotB hk (if col then 3 * (j + 1) + 1 else 2 * j) key i))
        (masks (if col then r + j else j) i)) = st := by
  intro gap
  have hk_odd : k % 2 = 1 := by omega
  have hgap : gap = 1 ∨ gap = 2 := by dsimp [gap]; cases col <;> simp
  dsimp only [invRoundB]
  have hfun : (fun i => xor (xor (xor (xor (stepB hk (mixB hk gap st) i)
      (rotB hk (if col then 3 * (j + 1) + 1 else 2 * j) key i))
      (masks (if col then r + j else j) i))
      (rotB hk (if col then 3 * (j + 1) + 1 else 2 * j) key i))
      (masks (if col then r + j else j) i)) = stepB hk (mixB hk gap st) := by
    ext i
    cases stepB hk (mixB hk gap st) i <;>
      cases rotB hk (if col then 3 * (j + 1) + 1 else 2 * j) key i <;>
      cases masks (if col then r + j else j) i <;> rfl
  rw [hfun, invChiB_stepB hk hk_odd, invMixB_mixB hk hk6 gap hgap]

theorem invRunB_runB {k : Nat} (hk : 0 < k) (hk6 : k % 6 = 1 ∨ k % 6 = 5)
    (r : Nat) (masks : Nat → Fin k → Bool) (col : Bool) (key name : Fin k → Bool) :
    invRunB hk r masks col key (runB hk r masks col key name) = name := by
  have hfold : ∀ (l : List Nat) (st : Fin k → Bool),
      l.reverse.foldl (fun s idx => invRoundB hk r masks col idx key s)
        (l.foldl (fun s idx => fun i =>
          xor (xor (stepB hk (mixB hk (if col then 2 else 1) s) i)
            (rotB hk (if col then 3 * (idx + 1) + 1 else 2 * idx) key i))
            (masks (if col then r + idx else idx) i)) st) = st := by
    intro l
    induction l with
    | nil => intro st; rfl
    | cons a t ih =>
      intro st
      simp only [List.reverse_cons, List.foldl_append, List.foldl_cons, List.foldl_nil]
      rw [ih, invRoundB_spec hk hk6]
  dsimp only [invRunB, runB]
  rw [hfold]
  ext i
  cases rotB hk (if col then 3 else 1) key i <;> cases name i <;> rfl

theorem runB_invRunB {k : Nat} (hk : 0 < k) (hk6 : k % 6 = 1 ∨ k % 6 = 5)
    (r : Nat) (masks : Nat → Fin k → Bool) (col : Bool) (key out : Fin k → Bool) :
    runB hk r masks col key (invRunB hk r masks col key out) = out := by
  have hinj : Function.Injective (runB hk r masks col key) :=
    Function.LeftInverse.injective (invRunB_runB hk hk6 r masks col key)
  have hsurj : Function.Surjective (runB hk r masks col key) :=
    Finite.injective_iff_surjective.mp hinj
  obtain ⟨x, rfl⟩ := hsurj out
  rw [invRunB_runB hk hk6]

def combWord {k : Nat} (prefixLen : Nat) (targ : Fin (2 ^ prefixLen)) (lo : Nat) : Fin k → Bool :=
  fun i => if i.val < k - prefixLen then lo.testBit i.val else targ.val.testBit (i.val - (k - prefixLen))

theorem combWord_shift {k prefixLen : Nat} (hp : prefixLen ≤ k)
    (targ : Fin (2 ^ prefixLen)) (lo : Nat) :
    toNat (combWord (k := k) prefixLen targ lo) >>> (k - prefixLen) = targ.val := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_shiftRight, testBit_toNat]
  by_cases hj : j < prefixLen
  · have hlt : k - prefixLen + j < k := by omega
    simp only [hlt, ↓reduceDIte, combWord, show ¬ (k - prefixLen + j < k - prefixLen) by omega,
      ↓reduceIte, Nat.add_sub_cancel_left]
  · have hge : ¬ (k - prefixLen + j < k) := by omega
    simp only [hge, ↓reduceDIte]
    symm
    exact Nat.testBit_lt_two_pow (targ.isLt.trans_le (Nat.pow_le_pow_right Nat.zero_lt_two (by omega)))

theorem combWord_of_shift {k prefixLen : Nat} (_hp : prefixLen ≤ k)
    (targ : Fin (2 ^ prefixLen)) (z : Fin k → Bool)
    (hz : toNat z >>> (k - prefixLen) = targ.val) :
    z = combWord (k := k) prefixLen targ (toNat z % 2 ^ (k - prefixLen)) := by
  ext i
  dsimp only [combWord]
  by_cases hi : i.val < k - prefixLen
  · simp only [hi, ↓reduceIte, mod_two_pow_testBit, testBit_toNat_fin]
  · simp only [hi, ↓reduceIte, ← hz, Nat.testBit_shiftRight]
    have he : k - prefixLen + (i.val - (k - prefixLen)) = i.val := by omega
    rw [he, testBit_toNat_fin]

theorem invRun_shift_iff {k prefixLen : Nat} (hk : 0 < k) (hk6 : k % 6 = 1 ∨ k % 6 = 5)
    (hp : prefixLen ≤ k) (r : Nat) (masks : Nat → Fin (2 ^ k)) (col : Bool)
    (targ : Fin (2 ^ prefixLen)) (w x : Fin (2 ^ k)) :
    (let N := 2 ^ k
     let rot := fun (shift x : Nat) => ((x <<< (shift % k)) ||| (x >>> (k - shift % k))) % N
     let chi := fun (x : Nat) => (List.range k).foldl (fun (acc i : Nat) =>
       acc ||| ((xor (x.testBit i) (!(x.testBit ((i + 1) % k)) && x.testBit ((i + 2) % k))).toNat <<< i)) 0
     let gap : Nat := if col then 2 else 1
     (List.range r).foldl (fun z j =>
       let mixed := z ^^^ rot gap z ^^^ rot (k - gap % k) z
       chi mixed ^^^ rot (if col then 3 * (j + 1) + 1 else 2 * j) w.val ^^^
         (masks (if col then r + j else j)).val) (rot (if col then 3 else 1) w.val ^^^ x.val)) >>> (k - prefixLen) = targ.val ↔
    ∃ lo < 2 ^ (k - prefixLen),
      x.val = toNat (invRunB hk r (fun j => ofNat k (masks j).val) col (ofNat k w.val)
        (combWord prefixLen targ lo)) := by
  have hrun := runB_toNat hk r masks col (ofNat k w.val) (ofNat k x.val)
  rw [toNat_ofNat w.isLt, toNat_ofNat x.isLt] at hrun
  dsimp only at hrun ⊢
  rw [hrun]
  constructor
  · intro hsh
    refine ⟨toNat (runB hk r (fun j => ofNat k (masks j).val) col (ofNat k w.val) (ofNat k x.val)) % 2 ^ (k - prefixLen),
      Nat.mod_lt _ (Nat.two_pow_pos _), ?_⟩
    rw [← combWord_of_shift hp targ _ hsh, invRunB_runB hk hk6, toNat_ofNat x.isLt]
  · rintro ⟨lo, _, hx⟩
    have hx' : ofNat k x.val = invRunB hk r (fun j => ofNat k (masks j).val) col (ofNat k w.val)
        (combWord prefixLen targ lo) := by
      rw [hx, ofNat_toNat]
    rw [hx', runB_invRunB hk hk6, combWord_shift hp]

theorem invRun_inj_lo {k prefixLen : Nat} (hk : 0 < k) (hk6 : k % 6 = 1 ∨ k % 6 = 5)
    (r : Nat) (masks : Nat → Fin k → Bool) (col : Bool)
    (targ : Fin (2 ^ prefixLen)) (key : Fin k → Bool)
    {lo1 lo2 : Nat} (h1 : lo1 < 2 ^ (k - prefixLen)) (h2 : lo2 < 2 ^ (k - prefixLen))
    (heq : toNat (invRunB hk r masks col key (combWord prefixLen targ lo1)) =
           toNat (invRunB hk r masks col key (combWord prefixLen targ lo2))) :
    lo1 = lo2 := by
  have hinv := toNat_inj heq
  have hcw : combWord (k := k) prefixLen targ lo1 = combWord (k := k) prefixLen targ lo2 := by
    have := congrArg (runB hk r masks col key) hinv
    rwa [runB_invRunB hk hk6, runB_invRunB hk hk6] at this
  apply Nat.eq_of_testBit_eq
  intro j
  by_cases hj : j < k - prefixLen
  · have hbit := congrFun hcw ⟨j, by omega⟩
    simpa [combWord, hj] using hbit
  · rw [Nat.testBit_lt_two_pow (h1.trans_le (Nat.pow_le_pow_right Nat.zero_lt_two (by omega))),
        Nat.testBit_lt_two_pow (h2.trans_le (Nat.pow_le_pow_right Nat.zero_lt_two (by omega)))]

theorem affCompG {n : Nat} {A : Set (Sig n)} {a1 b1 a2 b2 : Sig n}
    (ha1 : a1 ∈ A) (hb1 : b1 ∈ A) (ha2 : a2 ∈ A) (hb2 : b2 ∈ A) :
    Build A {fun v => (affComp (a1 v, b1 v) (a2 v, b2 v)).1,
             fun v => (affComp (a1 v, b1 v) (a2 v, b2 v)).2} 6 := by
  have h1 : Build A {an a1 a2} 1 := andG ha1 ha2
  have h2 : Build (A ∪ {an a1 a2}) {an a1 b2} 1 := andG (Or.inl ha1) (Or.inl hb2)
  have h3 : Build (A ∪ ({an a1 a2} ∪ {an a1 b2})) {xr b1 (an a1 b2)} 4 :=
    xorG (Or.inl hb1) (Or.inr (Or.inr rfl))
  refine relax (seq (seq h1 h2) h3) le_rfl ?_ (by omega)
  rintro f (rfl | rfl)
  · exact Or.inl (Or.inl rfl)
  · exact Or.inr rfl

theorem invChiG {n k : Nat} (hk : 0 < k) {A : Set (Sig n)}
    (y : Fin k → Sig n) (hy : ∀ i, y i ∈ A)
    (htrue : (fun _ => true) ∈ A) (hfalse : (fun _ => false) ∈ A) :
    Build A {f | ∃ i : Fin k, f = fun v => invChiB hk (fun j => y j v) i} (18 * k) := by
  let cm1 : Fin k → Sig n := fun p v => (chiMapAt hk (fun j => y j v) p).1
  let cm2 : Fin k → Sig n := fun p v => (chiMapAt hk (fun j => y j v) p).2
  have Hcm : Build A (Set.range cm1) k := by
    have h := finG cm1 1 fun p => notG (hy ⟨((stride2Idx k p.val hk).val + 1) % k, Nat.mod_lt _ hk⟩)
    exact relax h le_rfl le_rfl (by omega)
  have hcm2 : ∀ p, cm2 p ∈ A ∪ Set.range cm1 := fun p => Or.inl (hy (stride2Idx k p.val hk))
  let A1 := A ∪ Set.range cm1
  let pref1 : Nat → Sig n := fun p v => ((chiList hk (fun j => y j v)).take p).foldl affComp affId |>.1
  let pref2 : Nat → Sig n := fun p v => ((chiList hk (fun j => y j v)).take p).foldl affComp affId |>.2
  have Hpref : ∀ m ≤ k, Build A1
      ({f | ∃ p ≤ m, f = pref1 p} ∪ {f | ∃ p ≤ m, f = pref2 p}) (6 * m) := by
    intro m
    induction m with
    | zero =>
      intro _
      refine relax (idle ?_) le_rfl le_rfl (by omega)
      rintro f (⟨p, hp, rfl⟩ | ⟨p, hp, rfl⟩)
      · have hp0 : p = 0 := by omega
        subst hp0; exact Or.inl htrue
      · have hp0 : p = 0 := by omega
        subst hp0; exact Or.inl hfalse
    | succ m ih =>
      intro hm
      have Hprev := ih (by omega)
      let Bprev := {f | ∃ p ≤ m, f = pref1 p} ∪ {f | ∃ p ≤ m, f = pref2 p}
      have Hstep := affCompG (A := A1 ∪ Bprev)
        (a1 := pref1 m) (b1 := pref2 m) (a2 := cm1 ⟨m, by omega⟩) (b2 := cm2 ⟨m, by omega⟩)
        (Or.inr (Or.inl ⟨m, le_rfl, rfl⟩)) (Or.inr (Or.inr ⟨m, le_rfl, rfl⟩))
        (Or.inl (Or.inr ⟨⟨m, by omega⟩, rfl⟩)) (Or.inl (hcm2 ⟨m, by omega⟩))
      have he1 : pref1 (m + 1) = fun v => (affComp (pref1 m v, pref2 m v) (cm1 ⟨m, by omega⟩ v, cm2 ⟨m, by omega⟩ v)).1 := by
        funext v
        dsimp only [pref1, pref2, cm1, cm2]
        have hlen : (chiList hk (fun j => y j v)).length = k := List.length_ofFn
        have hrec := foldl_affComp_take_succ (chiList hk (fun j => y j v)) m (by omega)
        have hget : (chiList hk (fun j => y j v))[m]'(by omega) = chiMapAt hk (fun j => y j v) ⟨m, by omega⟩ := by
          simp [chiList]
        rw [hrec, hget]
      have he2 : pref2 (m + 1) = fun v => (affComp (pref1 m v, pref2 m v) (cm1 ⟨m, by omega⟩ v, cm2 ⟨m, by omega⟩ v)).2 := by
        funext v
        dsimp only [pref1, pref2, cm1, cm2]
        have hlen : (chiList hk (fun j => y j v)).length = k := List.length_ofFn
        have hrec := foldl_affComp_take_succ (chiList hk (fun j => y j v)) m (by omega)
        have hget : (chiList hk (fun j => y j v))[m]'(by omega) = chiMapAt hk (fun j => y j v) ⟨m, by omega⟩ := by
          simp [chiList]
        rw [hrec, hget]
      refine relax (seq Hprev Hstep) le_rfl ?_ (by omega)
      rintro f (⟨p, hp, rfl⟩ | ⟨p, hp, rfl⟩)
      · by_cases hpm : p = m + 1
        · subst hpm; rw [he1]; exact Or.inr (Or.inl rfl)
        · exact Or.inl (Or.inl ⟨p, by omega, rfl⟩)
      · by_cases hpm : p = m + 1
        · subst hpm; rw [he2]; exact Or.inr (Or.inr rfl)
        · exact Or.inl (Or.inr ⟨p, by omega, rfl⟩)
  let suf1 : Nat → Sig n := fun p v => ((chiList hk (fun j => y j v)).drop p).foldr affComp affId |>.1
  let suf2 : Nat → Sig n := fun p v => ((chiList hk (fun j => y j v)).drop p).foldr affComp affId |>.2
  have Hsuf : ∀ m ≤ k, Build A1
      ({f | ∃ p, k - m ≤ p ∧ p ≤ k ∧ f = suf1 p} ∪ {f | ∃ p, k - m ≤ p ∧ p ≤ k ∧ f = suf2 p}) (6 * m) := by
    intro m
    induction m with
    | zero =>
      intro _
      refine relax (idle ?_) le_rfl le_rfl (by omega)
      rintro f (⟨p, h1, h2, rfl⟩ | ⟨p, h1, h2, rfl⟩)
      · have hpk : p = k := by omega
        subst p
        have he : suf1 k = fun _ => true := by
          funext v
          have hnil : (chiList hk (fun j => y j v)).drop k = [] :=
            List.drop_eq_nil_iff.mpr (by simp [chiList])
          simp [suf1, hnil, affId]
        rw [he]; exact Or.inl htrue
      · have hpk : p = k := by omega
        subst p
        have he : suf2 k = fun _ => false := by
          funext v
          have hnil : (chiList hk (fun j => y j v)).drop k = [] :=
            List.drop_eq_nil_iff.mpr (by simp [chiList])
          simp [suf2, hnil, affId]
        rw [he]; exact Or.inl hfalse
    | succ m ih =>
      intro hm
      have Hprev := ih (by omega)
      let Bprev := {f | ∃ p, k - m ≤ p ∧ p ≤ k ∧ f = suf1 p} ∪ {f | ∃ p, k - m ≤ p ∧ p ≤ k ∧ f = suf2 p}
      let q := k - (m + 1)
      have hq1 : q + 1 = k - m := by omega
      have hqk : q < k := by omega
      have Hstep := affCompG (A := A1 ∪ Bprev)
        (a1 := cm1 ⟨q, hqk⟩) (b1 := cm2 ⟨q, hqk⟩) (a2 := suf1 (q + 1)) (b2 := suf2 (q + 1))
        (Or.inl (Or.inr ⟨⟨q, hqk⟩, rfl⟩)) (Or.inl (hcm2 ⟨q, hqk⟩))
        (Or.inr (Or.inl ⟨q + 1, by omega, by omega, rfl⟩))
        (Or.inr (Or.inr ⟨q + 1, by omega, by omega, rfl⟩))
      have he1 : suf1 q = fun v => (affComp (cm1 ⟨q, hqk⟩ v, cm2 ⟨q, hqk⟩ v) (suf1 (q + 1) v, suf2 (q + 1) v)).1 := by
        funext v
        dsimp only [suf1, suf2, cm1, cm2]
        have hlen : (chiList hk (fun j => y j v)).length = k := List.length_ofFn
        have hrec := foldr_affComp_drop (chiList hk (fun j => y j v)) q (by omega)
        have hget : (chiList hk (fun j => y j v))[q]'(by omega) = chiMapAt hk (fun j => y j v) ⟨q, hqk⟩ := by
          simp [chiList]
        rw [hrec, hget]
      have he2 : suf2 q = fun v => (affComp (cm1 ⟨q, hqk⟩ v, cm2 ⟨q, hqk⟩ v) (suf1 (q + 1) v, suf2 (q + 1) v)).2 := by
        funext v
        dsimp only [suf1, suf2, cm1, cm2]
        have hlen : (chiList hk (fun j => y j v)).length = k := List.length_ofFn
        have hrec := foldr_affComp_drop (chiList hk (fun j => y j v)) q (by omega)
        have hget : (chiList hk (fun j => y j v))[q]'(by omega) = chiMapAt hk (fun j => y j v) ⟨q, hqk⟩ := by
          simp [chiList]
        rw [hrec, hget]
      refine relax (seq Hprev Hstep) le_rfl ?_ (by omega)
      rintro f (⟨p, h1, h2, rfl⟩ | ⟨p, h1, h2, rfl⟩)
      · by_cases hpq : p = q
        · subst hpq; rw [he1]; exact Or.inr (Or.inl rfl)
        · exact Or.inl (Or.inl ⟨p, by omega, h2, rfl⟩)
      · by_cases hpq : p = q
        · subst hpq; rw [he2]; exact Or.inr (Or.inr rfl)
        · exact Or.inl (Or.inr ⟨p, by omega, h2, rfl⟩)
  let Bpref := {f | ∃ p ≤ k, f = pref1 p} ∪ {f | ∃ p ≤ k, f = pref2 p}
  let Bsuf := {f | ∃ p, 0 ≤ p ∧ p ≤ k ∧ f = suf1 p} ∪ {f | ∃ p, 0 ≤ p ∧ p ≤ k ∧ f = suf2 p}
  have Hp := Hpref k le_rfl
  have Hs : Build (A1 ∪ Bpref) Bsuf (6 * k) := by
    have h := Hsuf k le_rfl
    rw [Nat.sub_self] at h
    exact relax h Set.subset_union_left le_rfl le_rfl
  let A2 := A1 ∪ (Bpref ∪ Bsuf)
  let outAt : Fin k → Sig n := fun p v => invChiAt hk (fun j => y j v) p
  have Hout : Build A2 (Set.range outAt) (k * 5) := finG outAt 5 fun p => by
    have h1 : Build A2 {an (suf1 p.val) (pref2 p.val)} 1 :=
      andG (Or.inr (Or.inr (Or.inl ⟨p.val, Nat.zero_le _, Nat.le_of_lt p.isLt, rfl⟩)))
        (Or.inr (Or.inl (Or.inr ⟨p.val, Nat.le_of_lt p.isLt, rfl⟩)))
    have h2 : Build (A2 ∪ {an (suf1 p.val) (pref2 p.val)}) {xr (suf2 p.val) (an (suf1 p.val) (pref2 p.val))} 4 :=
      xorG (Or.inl (Or.inr (Or.inr (Or.inr ⟨p.val, Nat.zero_le _, Nat.le_of_lt p.isLt, rfl⟩)))) (Or.inr rfl)
    have he : xr (suf2 p.val) (an (suf1 p.val) (pref2 p.val)) = outAt p := rfl
    rw [he] at h2
    exact relax (seq h1 h2) le_rfl (Set.singleton_subset_iff.mpr (Or.inr rfl)) le_rfl
  have Htot := seq Hcm (seq (seq Hp Hs) Hout)
  refine relax Htot le_rfl ?_ (by omega)
  rintro f ⟨i, rfl⟩
  exact Or.inr (Or.inr ⟨stride2Inv k hk i, rfl⟩)

theorem invMixG {n k : Nat} (hk : 0 < k) (δ : Nat) {A : Set (Sig n)}
    (y : Fin k → Sig n) (hy : ∀ i, y i ∈ A) (hfalse : (fun _ => false) ∈ A) :
    Build A {f | ∃ i : Fin k, f = fun v => invMixB hk δ (fun j => y j v) i} (12 * k + 8) := by
  by_cases hk5 : k < 5
  · refine relax (idle ?_) le_rfl le_rfl (by omega)
    rintro f ⟨i, rfl⟩
    have he : (fun v => invMixB hk δ (fun j => y j v) i) = y i := by
      funext v; simp [invMixB, hk5]
    rw [he]; exact hy i
  · let md : Fin k → Sig n := fun p v => mixDiffAt hk δ (fun j => y j v) p
    have Hmd : Build A (Set.range md) (k * 4) := finG md 4 fun p =>
      xorG (hy ⟨(3 * δ * p.val + δ) % k, Nat.mod_lt _ hk⟩)
        (hy ⟨(3 * δ * p.val + 2 * δ) % k, Nat.mod_lt _ hk⟩)
    let A1 := A ∪ Set.range md
    let mp : Nat → Sig n := fun p v => mixPref hk δ (fun j => y j v) p
    have Hmp : ∀ m ≤ k, Build A1 {f | ∃ p ≤ m, f = mp p} (4 * m) := by
      intro m
      induction m with
      | zero =>
        intro _
        refine relax (idle ?_) le_rfl le_rfl (by omega)
        rintro f ⟨p, hp, rfl⟩
        have hp0 : p = 0 := by omega
        subst hp0; exact Or.inl hfalse
      | succ m ih =>
        intro hm
        have Hprev := ih (by omega)
        have Hstep : Build (A1 ∪ {f | ∃ p ≤ m, f = mp p})
            {xr (mp m) (md ⟨m % k, Nat.mod_lt _ hk⟩)} 4 :=
          xorG (Or.inr ⟨m, le_rfl, rfl⟩) (Or.inl (Or.inr ⟨⟨m % k, Nat.mod_lt _ hk⟩, rfl⟩))
        have he : xr (mp m) (md ⟨m % k, Nat.mod_lt _ hk⟩) = mp (m + 1) := by
          funext v; exact (mixPref_succ hk δ (fun j => y j v) m).symm
        rw [he] at Hstep
        refine relax (seq Hprev Hstep) le_rfl ?_ (by omega)
        rintro f ⟨p, hp, rfl⟩
        by_cases hpm : p = m + 1
        · subst hpm; exact Or.inr rfl
        · exact Or.inl ⟨p, by omega, rfl⟩
    let Bmp := {f | ∃ p ≤ k, f = mp p}
    let A2 := A ∪ (Set.range md ∪ Bmp)
    let pPos : Nat := inv3Pos k % k
    let pNeg : Nat := (k - pPos) % k
    have hpPos_le : pPos ≤ k := Nat.le_of_lt (Nat.mod_lt _ hk)
    have hpNeg_le : pNeg ≤ k := Nat.le_of_lt (Nat.mod_lt _ hk)
    let x0a : Sig n := xr (y ⟨0, hk⟩) (mp pPos)
    let x0 : Sig n := xr x0a (mp pNeg)
    have Hx0a : Build A2 {x0a} 4 :=
      xorG (Or.inl (hy ⟨0, hk⟩)) (Or.inr (Or.inr ⟨pPos, hpPos_le, rfl⟩))
    have Hx0 : Build (A2 ∪ {x0a}) {x0} 4 :=
      xorG (Or.inr rfl) (Or.inl (Or.inr (Or.inr ⟨pNeg, hpNeg_le, rfl⟩)))
    let A3 := A ∪ ((Set.range md ∪ Bmp) ∪ ({x0a} ∪ {x0}))
    let outF : Fin k → Sig n := fun i v => invMixB hk δ (fun j => y j v) i
    have Hout : Build A3 (Set.range outF) (k * 4) := finG outF 4 fun i => by
      have he : outF i = xr x0 (mp (m3dInv k δ hk i).val) := by
        funext v; simp [outF, invMixB, hk5, xr, x0, x0a, mp, pPos, pNeg]
      rw [he]
      exact xorG (Or.inr (Or.inr (Or.inr rfl)))
        (Or.inr (Or.inl (Or.inr ⟨(m3dInv k δ hk i).val, Nat.le_of_lt (m3dInv k δ hk i).isLt, rfl⟩)))
    have Htot := seq (seq (seq Hmd (Hmp k le_rfl)) (seq Hx0a Hx0)) Hout
    refine relax Htot le_rfl ?_ (by omega)
    rintro f ⟨i, rfl⟩
    exact Or.inr ⟨i, rfl⟩

theorem invRoundG {n k : Nat} (hk : 0 < k) (r : Nat) {A : Set (Sig n)}
    (masks : Nat → Fin k → Sig n) (col : Bool) (j : Nat) (key : Fin k → Bool)
    (y : Fin k → Sig n)
    (hy : ∀ i, y i ∈ A) (hm : ∀ i, masks (if col then r + j else j) i ∈ A)
    (htrue : (fun _ => true) ∈ A) (hfalse : (fun _ => false) ∈ A) :
    Build A {f | ∃ i : Fin k, f = fun v =>
      invRoundB hk r (fun t a => masks t a v) col j key (fun a => y a v) i} (38 * k + 8) := by
  let shift := if col then 3 * (j + 1) + 1 else 2 * j
  let z1 : Fin k → Sig n := fun i v => xor (y i v) (rotB hk shift key i)
  have Hz1 : Build A (Set.range z1) (k * 4) := finG z1 4 fun i => by
    have hc : (fun _ : Fin n → Bool => rotB hk shift key i) ∈ A := by
      cases rotB hk shift key i
      · exact hfalse
      · exact htrue
    exact xorG (hy i) hc
  let z2 : Fin k → Sig n := fun i v => xor (z1 i v) (masks (if col then r + j else j) i v)
  have Hz2 : Build (A ∪ Set.range z1) (Set.range z2) (k * 4) := finG z2 4 fun i =>
    xorG (Or.inr ⟨i, rfl⟩) (Or.inl (hm i))
  let A2 := A ∪ (Set.range z1 ∪ Set.range z2)
  let z3 : Fin k → Sig n := fun i v => invChiB hk (fun a => z2 a v) i
  have Hz3 : Build A2 {f | ∃ i : Fin k, f = z3 i} (18 * k) :=
    invChiG hk z2 (fun i => Or.inr (Or.inr ⟨i, rfl⟩)) (Or.inl htrue) (Or.inl hfalse)
  let A3 := A ∪ ((Set.range z1 ∪ Set.range z2) ∪ {f | ∃ i : Fin k, f = z3 i})
  let gap : Nat := if col then 2 else 1
  have Hz4 : Build A3 {f | ∃ i : Fin k, f = fun v => invMixB hk gap (fun a => z3 a v) i} (12 * k + 8) :=
    invMixG hk gap z3 (fun i => Or.inr (Or.inr ⟨i, rfl⟩)) (Or.inl hfalse)
  have Htot := seq (seq (seq Hz1 Hz2) Hz3) Hz4
  refine relax Htot le_rfl ?_ (by omega)
  rintro f ⟨i, rfl⟩
  exact Or.inr ⟨i, rfl⟩

theorem invRunG {n k : Nat} (hk : 0 < k) (r : Nat) {A : Set (Sig n)}
    (masks : Nat → Fin k → Sig n) (col : Bool) (key : Fin k → Bool) (out : Fin k → Sig n)
    (hout : ∀ i, out i ∈ A)
    (hm : ∀ j < r, ∀ i, masks (if col then r + j else j) i ∈ A)
    (htrue : (fun _ => true) ∈ A) (hfalse : (fun _ => false) ∈ A) :
    Build A {f | ∃ i : Fin k, f = fun v =>
      invRunB hk r (fun t a => masks t a v) col key (fun a => out a v) i}
      (r * (38 * k + 8) + 4 * k) := by
  have hfold : ∀ (l : List Nat), (∀ j ∈ l, j < r) →
      Build A {f | ∃ i : Fin k, f = fun v =>
        l.foldl (fun st j => invRoundB hk r (fun t a => masks t a v) col j key st)
          (fun a => out a v) i} (l.length * (38 * k + 8)) := by
    intro l
    induction l using List.reverseRecOn with
    | nil =>
      intro _
      refine relax (idle ?_) le_rfl le_rfl (by simp)
      rintro f ⟨i, rfl⟩; exact hout i
    | append_singleton l a ih =>
      intro hl
      have Hprev := ih (fun j hj => hl j (List.mem_append_left _ hj))
      let prevF : Fin k → Sig n := fun i v =>
        l.foldl (fun st j => invRoundB hk r (fun t a => masks t a v) col j key st)
          (fun a => out a v) i
      have Hstep := invRoundG hk r masks col a key prevF
        (A := A ∪ {f | ∃ i : Fin k, f = prevF i})
        (fun i => Or.inr ⟨i, rfl⟩)
        (fun i => Or.inl (hm a (hl a (by simp)) i))
        (Or.inl htrue) (Or.inl hfalse)
      refine relax (seq Hprev Hstep) le_rfl ?_ ?_
      · rintro f ⟨i, rfl⟩
        right
        refine ⟨i, ?_⟩
        funext v
        simp only [List.foldl_append, List.foldl_cons, List.foldl_nil, prevF]
      · simp only [List.length_append, List.length_singleton, Nat.add_mul, Nat.one_mul]
        omega
  have Hrev := hfold (List.range r).reverse (fun j hj => by
    rw [List.mem_reverse, List.mem_range] at hj; exact hj)
  rw [List.length_reverse, List.length_range] at Hrev
  let st0 : Fin k → Sig n := fun i v =>
    (List.range r).reverse.foldl
      (fun st j => invRoundB hk r (fun t a => masks t a v) col j key st)
      (fun a => out a v) i
  let A1 := A ∪ {f | ∃ i : Fin k, f = st0 i}
  let finF : Fin k → Sig n := fun i v => invRunB hk r (fun t a => masks t a v) col key (fun a => out a v) i
  have Hfin : Build A1 (Set.range finF) (k * 4) := finG finF 4 fun i => by
    have hc : (fun _ : Fin n → Bool => rotB hk (if col then 3 else 1) key i) ∈ A1 := by
      cases rotB hk (if col then 3 else 1) key i
      · exact Or.inl hfalse
      · exact Or.inl htrue
    exact xorG hc (Or.inr ⟨i, rfl⟩)
  refine relax (seq Hrev Hfin) le_rfl ?_ (by omega)
  rintro f ⟨i, rfl⟩
  exact Or.inr ⟨i, rfl⟩

end CipherRun

end PEqualNP.Outside.L_meta_32030.Shared

namespace PEqualNP.Outside.L_meta_32030.Work
open PEqualNP.Outside.L_meta_32030.Shared
abbrev Words (n : Nat) := Nat → (Fin n → Bool) → Nat
def Bank {n : Nat} (Q W : Nat) (v : Words n) : Set (Sig n) := {f | ∃ i < Q, ∃ b < W, f = fun x => (v i x).testBit b}
def groupMin (Q : Nat) (addr val : Nat → Nat) (d j : Nat) : Nat :=
  (List.range Q).foldl (fun acc i => if addr i = j then min acc (val i) else acc) d
end PEqualNP.Outside.L_meta_32030.Work

namespace PEqualNP.Outside.L_meta_32030.Work
open PEqualNP.Outside.L_meta_32030.Shared

def rotC (k d x : Nat) := ((x <<< (d % k)) ||| (x >>> (k-d%k))) % (2^k)
def chiC (k x : Nat) := (List.range k).foldl (fun (acc i : Nat) => acc ||| ((xor (x.testBit i) (!(x.testBit ((i+1)%k)) && x.testBit ((i+2)%k))).toNat <<< i)) 0
def runC (k r : Nat) (masks : Nat → Fin (2^k)) (col : Bool) (key name : Nat) :=
  let gap : Nat := if col then 2 else 1
  (List.range r).foldl (fun z j =>
    let mixed := z ^^^ rotC k gap z ^^^ rotC k (k - gap % k) z
    chiC k mixed ^^^ rotC k (if col then 3*(j+1)+1 else 2*j) key ^^^
      (masks (if col then r+j else j)).val) (rotC k (if col then 3 else 1) key ^^^ name)
def bitsC (w x : Nat) := (List.range w).map (fun j => x.testBit j)
abbrev dimC (k r h : Nat) := 2*r*k+2*h+2^k*k
def inputC (k r h : Nat) (masks : Nat → Fin (2^k)) (a c : Fin (2^h)) (priority : Fin (2^k) → Fin (2^k)) :=
  (List.range (2*r)).flatMap (fun j => bitsC k (masks j).val) ++ bitsC h a.val ++ bitsC h c.val ++ (List.finRange (2^k)).flatMap (fun y => bitsC k (priority y).val)
def vecC (k r h : Nat) (masks : Nat → Fin (2^k)) (a c : Fin (2^h)) (priority : Fin (2^k) → Fin (2^k)) (j : Fin (dimC k r h)) := (inputC k r h masks a c priority).getD j.val false
def rawC (n : Nat) : Set (Sig n) := Set.range (fun i : Fin n => fun x => x i)
def constantsC (n : Nat) : Set (Sig n) := {f | ∃ b : Bool, f = fun _ => b}
end PEqualNP.Outside.L_meta_32030.Work

namespace PEqualNP.Outside.L_meta_32030.Work
open PEqualNP.Outside.L_meta_32030.Shared

abbrev fee (e w : Nat) := 512*(e+2)^2*(e+w+2)*2^e

def GatherOK (n : Nat) := ∀ (e w : Nat) (src addr : Words n) (A : Set (Sig n)),
  constantsC n ⊆ A → Bank (2^e) w src ⊆ A → Bank (2^e) e addr ⊆ A →
  (∀ i < 2^e, ∀ x, addr i x < 2^e) → (∀ i < 2^e, ∀ x, src i x < 2^w) →
  Build A (Bank (2^e) w (fun i x => src (addr i x) x)) (fee e w)

def MinOK (n : Nat) := ∀ (e w d : Nat) (addr val : Words n) (A : Set (Sig n)),
  constantsC n ⊆ A → Bank (2^e) w val ⊆ A → Bank (2^e) e addr ⊆ A →
  (∀ i < 2^e, ∀ x, addr i x < 2^e) → (∀ i < 2^e, ∀ x, val i x ≤ d) → d < 2^w →
  Build A (Bank (2^e) w (fun j x => groupMin (2^e) (fun i => addr i x) (fun i => val i x) d j)) (fee e w)

theorem chainKeep {n} {A B C : Set (Sig n)} {b c : Nat} (h : Build A B b) (j : Build B C c) : Build A (B ∪ C) (b+c) := seq h (relax j Set.subset_union_right le_rfl le_rfl)

theorem wire {n Q W : Nat} {v : Words n} {A : Set (Sig n)} (hs : Bank Q W v ⊆ A) {i b} (hi : i<Q) (hb : b<W) : (fun x => (v i x).testBit b) ∈ A := hs ⟨i,hi,b,hb,rfl⟩
theorem constWire {n} {A : Set (Sig n)} (h : constantsC n ⊆ A) (b : Bool) : (fun _ => b) ∈ A := h ⟨b,rfl⟩
theorem bankWide {n Q w w' : Nat} {v : Words n} {A : Set (Sig n)} (c : constantsC n ⊆ A) (hv : Bank Q w v ⊆ A)
    (bd : ∀ i<Q, ∀ x, v i x < 2^w) : Bank Q w' v ⊆ A := by
  rintro _ ⟨i,hi,b,_,rfl⟩
  by_cases hb : b<w
  · exact wire hv hi hb
  · have eq : (fun x => (v i x).testBit b) = (fun _ => false) := by
      funext x; exact Nat.testBit_lt_two_pow ((bd i hi x).trans_le (Nat.pow_le_pow_right (by decide) (by omega)))
    rw [eq]; exact constWire c false

theorem bankStatic {n Q w} {A : Set (Sig n)} (c : constantsC n ⊆ A) (fn : Nat → Nat) : Bank Q w (n:=n) (fun i _ => fn i) ⊆ A := by
  rintro _ ⟨i,hi,b,hb,rfl⟩; exact constWire c _

theorem bankJoin {n Q l h : Nat} {lo high : Words n} {A : Set (Sig n)} (low : Bank Q l lo ⊆ A) (upper : Bank Q h high ⊆ A)
    (bound : ∀ i<Q, ∀ x, lo i x < 2^l) : Bank Q (l+h) (fun i x => high i x * 2^l + lo i x) ⊆ A := by
  rintro _ ⟨i,hi,b,hb,rfl⟩
  by_cases ht : b<l
  · have eq : (fun x => (high i x*2^l+lo i x).testBit b) = fun x => (lo i x).testBit b := by
      funext x; rw [Nat.mul_comm, Nat.testBit_two_pow_mul_add _ (bound i hi x) b, if_pos ht]
    rw [eq]; exact wire low hi ht
  · have eq : (fun x => (high i x*2^l+lo i x).testBit b) = fun x => (high i x).testBit (b-l) := by
      funext x; rw [Nat.mul_comm, Nat.testBit_two_pow_mul_add _ (bound i hi x) b, if_neg ht]
    rw [eq]; exact wire upper hi (by omega)

theorem bankReindex {n Q R w : Nat} {v : Words n} {A : Set (Sig n)} (known : Bank R w v ⊆ A) (ix : Nat → Nat) (h : ∀ i<Q, ix i<R) : Bank Q w (fun i x => v (ix i) x) ⊆ A := by
  rintro _ ⟨i,hi,b,hb,rfl⟩; exact wire known (h i hi) hb

theorem bankName {n Q k : Nat} {v : Words n} {A : Set (Sig n)} (hv : Bank Q (3*k+1) v ⊆ A) : Bank Q k (fun i x => (v i x/2^k)%2^k) ⊆ A := by
  rintro _ ⟨i,hi,b,hb,rfl⟩
  have eq : (fun x => ((v i x/2^k)%2^k).testBit b) = fun x => (v i x).testBit (b+k) := by
    funext x; simp [Nat.testBit_mod_two_pow,hb,Nat.testBit_div_two_pow]
  rw [eq]; exact wire hv hi (by omega)

theorem feeBound (e w k : Nat) (he : e≤2*k) (hw : w≤3*k+1) : fee e w ≤ 12288*(k+1)^3*2^e := by
  apply Nat.mul_le_mul_right
  have hsq : (e+2)^2 ≤ (2*(k+1))^2 := Nat.pow_le_pow_left (by omega) 2
  have hsum : e+w+2 ≤ 6*(k+1) := by omega
  calc
    _ ≤ 512*(2*(k+1))^2*(6*(k+1)) := by gcongr
    _ = _ := by ring
end PEqualNP.Outside.L_meta_32030.Work

namespace PEqualNP.Outside.L_meta_32030.Work
open PEqualNP.Outside.L_meta_32030.Shared
namespace GatherImpl
def keyBits2 (k : Nat) (dummy tag : Bool) (addr : Nat → Bool) (j : Nat) : Bool :=
  if j = 0 then tag else if j = k + 1 then dummy else addr (j - 1)

theorem keyBits2_val (k : Nat) (dummy tag : Bool) (addr : Nat → Bool) :
    bitsVal (keyBits2 k dummy tag addr) (k + 2) =
      (if dummy then 2 ^ (k + 1) else 0) + 2 * bitsVal addr k + (if tag then 1 else 0) := by
  have hmid : ∀ m ≤ k, bitsVal (keyBits2 k dummy tag addr) (m + 1) =
      (if tag then 1 else 0) + 2 * bitsVal addr m := by
    intro m
    induction m with
    | zero =>
      intro _; simp [bitsVal, keyBits2]
    | succ m ih =>
      intro hm
      have hih := ih (by omega)
      change bitsVal (keyBits2 k dummy tag addr) (m + 1) +
          (if keyBits2 k dummy tag addr (m + 1) then 2 ^ (m + 1) else 0) = _
      have hbit : keyBits2 k dummy tag addr (m + 1) = addr m := by
        simp only [keyBits2, show m + 1 ≠ 0 by omega, show m + 1 ≠ k + 1 by omega, ↓reduceIte,
          Nat.add_sub_cancel]
      rw [hih, hbit]
      simp only [bitsVal, Nat.mul_add]
      have hpow : 2 ^ (m + 1) = 2 * 2 ^ m := by rw [Nat.pow_succ, Nat.mul_comm]
      rw [hpow]
      cases addr m
      · simp
      · simp [Nat.add_assoc]
  change bitsVal (keyBits2 k dummy tag addr) (k + 1) +
      (if keyBits2 k dummy tag addr (k + 1) then 2 ^ (k + 1) else 0) = _
  rw [hmid k le_rfl]
  have htop : keyBits2 k dummy tag addr (k + 1) = dummy := by simp [keyBits2]
  rw [htop]
  omega

def scan2 (k : Nat) (st : Nat → Rec) : Nat → Bool × (Nat → Bool)
  | 0 => (false, fun _ => false)
  | m + 1 =>
    let prev := scan2 k st m
    let isTab := !((st m).1 (k + 1)) && !((st m).1 0)
    let cur := if isTab then (st m).2 0 else prev.1
    (cur, fun idx => if idx = m then cur else prev.2 idx)

theorem scan2Circuit {n : Nat} {A : Set (Sig n)} (k P : Nat)
    (st : (Fin n → Bool) → Nat → Rec)
    (hK : ∀ idx < P, ∀ j < k + 2, (fun v => (st v idx).1 j) ∈ A)
    (hV : ∀ idx < P, (fun v => (st v idx).2 0) ∈ A)
    (hfalse : (fun _ => false) ∈ A) :
    ∀ m ≤ P,
      Build A
        ({fun v => (scan2 k (st v) m).1} ∪
         {f | ∃ idx < m, f = fun v => (scan2 k (st v) m).2 idx})
        (m * 7) := by
  intro m
  induction m with
  | zero =>
    intro _
    refine relax (idle ?_) le_rfl le_rfl (by simp)
    rintro f (rfl | ⟨idx, hidx, _⟩)
    · exact hfalse
    · omega
  | succ m ih =>
    intro hm
    have Hprev := ih (by omega)
    let Bprev := {fun v => (scan2 k (st v) m).1} ∪
      {f | ∃ idx < m, f = fun v => (scan2 k (st v) m).2 idx}
    let A1 := A ∪ Bprev
    let dSig : Sig n := fun v => (st v m).1 (k + 1)
    let tSig : Sig n := fun v => (st v m).1 0
    have hd : dSig ∈ A1 := Or.inl (hK m (by omega) (k + 1) (by omega))
    have ht : tSig ∈ A1 := Or.inl (hK m (by omega) 0 (by omega))
    have Hnd : Build A1 {nt dSig} 1 := notG hd
    have Hnt : Build (A1 ∪ {nt dSig}) {nt tSig} 1 := notG (Or.inl ht)
    let isTab : Sig n := an (nt dSig) (nt tSig)
    have HisTab : Build (A1 ∪ ({nt dSig} ∪ {nt tSig})) {isTab} 1 :=
      andG (Or.inr (Or.inl rfl)) (Or.inr (Or.inr rfl))
    let nisTab : Sig n := nt isTab
    have HnisTab : Build (A1 ∪ (({nt dSig} ∪ {nt tSig}) ∪ {isTab})) {nisTab} 1 :=
      notG (Or.inr (Or.inr rfl))
    let A2 := A1 ∪ ((({nt dSig} ∪ {nt tSig}) ∪ {isTab}) ∪ {nisTab})
    let curF : Sig n := fun v => (scan2 k (st v) (m + 1)).1
    have Hcur : Build A2 {curF} 3 :=
      muxG (Or.inr (Or.inl (Or.inr rfl))) (Or.inr (Or.inr rfl))
        (Or.inl (Or.inl (hV m (by omega))))
        (Or.inl (Or.inr (Or.inl rfl))) (fun _ => rfl)
    have Htot := seq Hprev (seq (seq (seq (seq Hnd Hnt) HisTab) HnisTab) Hcur)
    refine relax Htot le_rfl ?_ (by rw [Nat.succ_mul m])
    rintro f (rfl | ⟨idx, hidx, rfl⟩)
    · exact Or.inr (Or.inr rfl)
    · by_cases hjm : idx = m
      · subst hjm
        exact Or.inr (Or.inr (by funext v; simp [curF, scan2]))
      · exact Or.inl (Or.inr ⟨idx, by omega, by funext v; simp [scan2, hjm]⟩)

theorem scan2_answer (k P : Nat) (st : Nat → Rec) (table : Nat → Bool)
    (hsorted : ∀ i j, i ≤ j → j < P → recKey (k + 2) (st i) ≤ recKey (k + 2) (st j))
    (htab_real : ∀ i < P, (st i).1 (k + 1) = false → (st i).1 0 = false →
      ∃ addr < 2 ^ k, recKey (k + 2) (st i) = 2 * addr ∧ (st i).2 0 = table addr)
    (htab_exists : ∀ addr < 2 ^ k, ∃ i < P,
      (st i).1 (k + 1) = false ∧ (st i).1 0 = false ∧ recKey (k + 2) (st i) = 2 * addr) :
    ∀ m ≤ P,
      (∀ t < m, (st t).1 (k + 1) = false → (st t).1 0 = true →
        ∀ addr < 2 ^ k, recKey (k + 2) (st t) = 2 * addr + 1 →
          (scan2 k st m).2 t = table addr) ∧
      (∀ t < m, (st t).1 (k + 1) = false → (st t).1 0 = false →
        ∃ addr < 2 ^ k,
          (∀ j < m, (st j).1 (k + 1) = false → (st j).1 0 = false → recKey (k + 2) (st j) ≤ 2 * addr) ∧
          (∃ j < m, (st j).1 (k + 1) = false ∧ (st j).1 0 = false ∧ recKey (k + 2) (st j) = 2 * addr) ∧
          (scan2 k st m).1 = table addr) := by
  intro m
  induction m with
  | zero => intro _; exact ⟨fun _ h => by omega, fun _ h => by omega⟩
  | succ m ih =>
    intro hm
    rcases ih (by omega) with ⟨ih_ans, ih_cur⟩
    constructor
    · intro t ht hd0 ht1 addr haddr hkey
      simp only [scan2]
      by_cases htm : t = m
      · subst t
        simp only [↓reduceIte, ht1, Bool.not_true, Bool.and_false, Bool.false_eq_true]
        rcases htab_exists addr haddr with ⟨i0, hi0P, hi0d, hi0t, hi0k⟩
        have hi0_lt : i0 < m := by
          by_contra hge
          have hle := hsorted m i0 (by omega) hi0P
          omega
        rcases ih_cur i0 hi0_lt hi0d hi0t with ⟨addr', _, hmax, ⟨j0, hj0m, _, _, hj0k⟩, hcur_eq⟩
        have hle1 : 2 * addr ≤ 2 * addr' := by have := hmax i0 hi0_lt hi0d hi0t; omega
        have hle2 : 2 * addr' ≤ 2 * addr + 1 := by have := hsorted j0 m (by omega) (by omega); omega
        have heq : addr' = addr := by omega
        rw [hcur_eq, heq]
      · simp only [htm, ↓reduceIte]
        exact ih_ans t (by omega) hd0 ht1 addr haddr hkey
    · intro t ht hd0 ht0
      simp only [scan2]
      by_cases hmtab : (st m).1 (k + 1) = false ∧ (st m).1 0 = false
      · simp only [hmtab.1, hmtab.2, Bool.not_false, Bool.and_self, ↓reduceIte]
        rcases htab_real m (by omega) hmtab.1 hmtab.2 with ⟨addr, haddr, hkey, hval⟩
        refine ⟨addr, haddr, ?_, ⟨m, by omega, hmtab.1, hmtab.2, hkey⟩, hval⟩
        intro j hj _ _
        have hle := hsorted j m (by omega) (by omega)
        omega
      · have hnot : (!((st m).1 (k + 1)) && !((st m).1 0)) = false := by
          cases h1 : (st m).1 (k + 1) <;> cases h2 : (st m).1 0
          · exact absurd ⟨h1, h2⟩ hmtab
          · rfl
          · rfl
          · rfl
        simp only [hnot, Bool.false_eq_true, ↓reduceIte]
        have htm : t < m := by
          by_contra hge
          have hteq : t = m := by omega
          subst hteq; exact hmtab ⟨hd0, ht0⟩
        rcases ih_cur t htm hd0 ht0 with ⟨addr, haddr, hmax, ⟨j0, hj0, hj0d, hj0t, hj0k⟩, hcur_eq⟩
        refine ⟨addr, haddr, ?_, ⟨j0, by omega, hj0d, hj0t, hj0k⟩, hcur_eq⟩
        intro j hj hjd hjt
        by_cases hjm : j = m
        · subst hjm; exact absurd ⟨hjd, hjt⟩ hmtab
        · exact hmax j (by omega) hjd hjt

end GatherImpl

open GatherImpl in
theorem gather {n : Nat} (e w : Nat) (src addr : Words n) (A : Set (Sig n))
    (hc : constantsC n ⊆ A) (hs : Bank (2^e) w src ⊆ A)
    (ha : Bank (2^e) e addr ⊆ A) (hb : ∀ i < 2^e, ∀ x, addr i x < 2^e) :
    Build A (Bank (2^e) w (fun i x => src (addr i x) x))
      (512 * (e+2)^2 * (e+w+2) * 2^e) := by
  let Q := 2^e
  let P := 2^(e+1)
  have hp : P = Q+Q := by simp [P,Q,pow_succ,Nat.mul_two]
  let net := bitonicSort 0 (e+1) true
  have hn : ∀ c ∈ net, c.1 < P ∧ c.2.1 < P := by
    intro c h
    have hm := bitonicSort_mem 0 (e+1) true c h
    dsimp only [P]; omega
  let st : (Fin n → Bool) → Nat → Rec := fun x i =>
    if i < Q then (keyBits2 e false false i.testBit, (src i x).testBit)
    else (keyBits2 e false true (addr (i-Q) x).testBit, fun _ => false)
  have hC (b : Bool) : (fun _ : Fin n → Bool => b) ∈ A := hc ⟨b,rfl⟩
  have hK : ∀ i < P, ∀ j < e+2, (fun x => (st x i).1 j) ∈ A := by
    intro i hi j hj
    by_cases h : i < Q
    · simpa only [st,h,if_true] using hC (keyBits2 e false false i.testBit j)
    · simp only [st,h,if_false,keyBits2]
      split_ifs with h0 h1
      · exact hC true
      · exact hC false
      · exact ha ⟨i-Q,by change i-Q<Q; omega,j-1,by omega,rfl⟩
  have hV : ∀ i < P, ∀ j < w, (fun x => (st x i).2 j) ∈ A := by
    intro i hi j hj
    by_cases h : i < Q
    · simp only [st,h,if_true]; exact hs ⟨i,h,j,hj,rfl⟩
    · simp only [st,h,if_false]; exact hC false
  let key := recKey (e+2)
  let sorted := fun x => runNet key net (st x)
  let sw := fun x => netSwaps key net (st x)
  let B : Set (Sig n) :=
    ({f | ∃ i < P, ∃ j < e+2, f = fun x => (sorted x i).1 j} ∪
     {f | ∃ i < P, ∃ j < w, f = fun x => (sorted x i).2 j}) ∪
     {f | ∃ t < net.length, f = (fun x => ((sw x).getD t (0,0,false)).2.2) ∨
        f = (fun x => !(((sw x).getD t (0,0,false)).2.2))}
  have H1 : Build A B _ := netCircuit (e+2) w P net hn st hK hV (hC false)
  let slice := fun j x i => ((sorted x i).1, fun _ : Nat => (sorted x i).2 j)
  let ans := fun x i j => (scan2 e (slice j x) P).2 i
  let C := fun j => {f : Sig n | ∃ i < P, f = fun x => ans x i j}
  have H2 := rangeSetsG (m := w) (A := A ∪ B) C (P*7) fun j hj => by
    have hh := scan2Circuit (A := A ∪ B) e P (slice j)
      (fun i hi a h => Or.inr (Or.inl (Or.inl ⟨i,hi,a,h,rfl⟩)))
      (fun i hi => Or.inr (Or.inl (Or.inr ⟨i,hi,j,hj,rfl⟩)))
      (Or.inl (hC false)) P le_rfl
    exact relax hh le_rfl (fun _ h => Or.inr h) le_rfl
  let D := {f : Sig n | ∃ j < w, f ∈ C j}
  have H3 := replayRevCircuit (A := A ∪ (B ∪ D)) (e+2) w P net hn st
    (fun t ht => ⟨Or.inr (Or.inl (Or.inr ⟨t,ht,Or.inl rfl⟩)),
                  Or.inr (Or.inl (Or.inr ⟨t,ht,Or.inr rfl⟩))⟩)
    ans (fun i hi j hj => Or.inr (Or.inr ⟨j,hj,i,hi,rfl⟩))
  refine relax (seq (seq H1 H2) H3) le_rfl ?_ ?_
  · rintro f ⟨i,hi,j,hj,rfl⟩
    change i < Q at hi
    right
    refine ⟨Q+i,by omega,j,hj,?_⟩
    funext x
    rcases bitonicPerm key P net hn (st x) with ⟨_,_,_,hlt,hrun,hinv,hrep⟩
    rw [congrFun (hrep (ans x) (Q+i)) j]
    let inv := replaySwaps (sw x).reverse id
    let fwd := replaySwaps (sw x) id
    have hF (t : Nat) : sorted x t = st x (fwd t) := hrun t
    have hI (t : Nat) : sorted x (inv t) = st x t := hinv t
    have hkey (t : Nat) (ht : t < Q) : key (st x t) = 2*t := by
      simp [key,st,ht,recKey,keyBits2_val,bitsVal_of_testBit _ _ ht]
    have hr (t : Nat) (_ : t < P) (_hd : (slice j x t).1 (e+1) = false)
        (ht : (slice j x t).1 0 = false) :
        ∃ a < 2^e, recKey (e+2) (slice j x t) = 2*a ∧
          (slice j x t).2 0 = (src a x).testBit j := by
      change (sorted x t).1 0 = false at ht
      change ∃ a < Q, key (sorted x t) = 2*a ∧ (sorted x t).2 j = _
      rw [hF] at ht ⊢
      by_cases ht' : fwd t < Q
      · exact ⟨_,ht',hkey _ ht',by simp [st,ht']⟩
      · simp [st,ht',keyBits2] at ht
    have he (a : Nat) (ha' : a < 2^e) : ∃ t < P,
        (slice j x t).1 (e+1) = false ∧ (slice j x t).1 0 = false ∧
        recKey (e+2) (slice j x t) = 2*a := by
      change a < Q at ha'
      refine ⟨inv a,hlt a (by omega),?_⟩
      change (sorted x (inv a)).1 (e+1) = false ∧ (sorted x (inv a)).1 0 = false ∧
        key (sorted x (inv a)) = 2*a
      rw [hI]
      exact ⟨by simp [st,ha',keyBits2],by simp [st,ha',keyBits2],hkey _ ha'⟩
    have hall := (scan2_answer e P (slice j x) (fun a => (src a x).testBit j)
      (bitonicSort_sorted key (e+1) (st x)) hr he P le_rfl).1
    have hq : ¬ Q+i < Q := by omega
    symm
    apply hall (inv (Q+i)) (hlt _ (by omega)) _ _ _ (hb i hi x)
    · change key (sorted x (inv (Q+i))) = _
      rw [hI]
      simp [key,recKey,st,hq,keyBits2_val,bitsVal_of_testBit _ _ (hb i hi x)]
    · change (sorted x (inv (Q+i))).1 (e+1) = false
      rw [hI]; simp [st,hq,keyBits2]
    · change (sorted x (inv (Q+i))).1 0 = true
      rw [hI]; simp [st,hq,keyBits2]
  · change net.length * (11*(e+2)+6*w+1) + w*(P*7) + net.length*(6*w) ≤
      512*(e+2)^2*(e+w+2)*Q
    have hlen : 4*net.length = (e+1)*(e+1+1)*P := bitonicSort_length 0 (e+1) true
    rw [hp] at hlen ⊢
    have hle : net.length ≤ (e+2)^2*Q := by
      nlinarith only [hlen, Nat.zero_le (e*Q), Nat.zero_le (e^2*Q),Nat.zero_le Q]
    calc
      _ ≤ (e+2)^2*Q*(11*(e+2)+6*w+1) + w*((Q+Q)*7) + (e+2)^2*Q*(6*w) := by gcongr
      _ ≤ _ := by ring_nf; omega
end PEqualNP.Outside.L_meta_32030.Work

namespace PEqualNP.Outside.L_meta_32030.Work
open PEqualNP.Outside.L_meta_32030.Shared

namespace MinScatter

private def adr (q : Nat) (a : Nat → Nat) (i : Nat) :=
  if i < q then i else if i < 2*q then a (i-q) else (i-2*q)%q
private def num (q d : Nat) (v : Nat → Nat) (i : Nat) :=
  if i < q then 0 else if i < 2*q then v (i-q) else d
private def code (q B d : Nat) (a v : Nat → Nat) (i : Nat) :=
  2*B * adr q a i + ((if i < q then 0 else B) + num q d v i)

private def row (q w d : Nat) (a v : Nat → Nat) (i : Nat) : Rec :=
  (fun b => if b < w then (num q d v i).testBit b else if b = w then decide (q ≤ i)
            else (adr q a i).testBit (b-(w+1)), fun _ => false)

private theorem row_key {e w d i : Nat} {a v : Nat → Nat} (ha : ∀ t < 2^e, a t < 2^e)
    (hv : ∀ t < 2^e, v t ≤ d) (hd : d < 2^w) :
    recKey (w+1+e) (row (2^e) w d a v i) = code (2^e) (2^w) d a v i := by
  let q := 2^e
  have hq : 0 < q := pow_pos (by decide) _
  have had : adr q a i < 2^e := by
    unfold adr; split <;> rename_i h
    · exact h
    · split <;> rename_i h'
      · exact ha _ (show i-q < q by omega)
      · exact Nat.mod_lt _ hq
  have hnu : num q d v i < 2^w := by
    unfold num; split
    · omega
    · split <;> rename_i h
      · exact lt_of_le_of_lt (hv _ (show i-q < q by omega)) hd
      · exact hd
  let f := (row q w d a v i).1
  have hlow : bitsVal f w = num q d v i := by
    rw [bitsVal_congr f (fun b => (num q d v i).testBit b) w (fun b hb => by simp [f,row,hb]),
        bitsVal_of_testBit _ _ hnu]
  have hhigh : bitsVal (fun b => f (w+1+b)) e = adr q a i := by
    rw [bitsVal_congr _ (fun b => (adr q a i).testBit b) e (fun b _ => by
      simp [f,row, show ¬ w+1+b < w by omega, show w+1+b ≠ w by omega]), bitsVal_of_testBit _ _ had]
  change bitsVal f ((w+1)+e) = code q (2^w) d a v i
  rw [bitsVal_add, hhigh, bitsVal, hlow, pow_succ]
  by_cases hi : i < q <;> simp [code,f,row,hi,show q ≤ i ↔ ¬i < q by omega] <;> ring

private theorem min_spec (q : Nat) (a v : Nat → Nat) (d j : Nat) :
    let m := groupMin q a v d j
    m ≤ d ∧ (∀ i < q, a i = j → m ≤ v i) ∧ (m = d ∨ ∃ i < q, a i = j ∧ v i = m) := by
  induction q with
  | zero => simp [groupMin]
  | succ q ih =>
    dsimp only at ih ⊢
    have he : groupMin (q+1) a v d j = if a q = j then min (groupMin q a v d j) (v q)
        else groupMin q a v d j := by simp [groupMin,List.range_succ]
    rw [he]; by_cases haj : a q = j
    · simp only [haj,ite_true]
      refine ⟨le_trans (min_le_left ..) ih.1, ?_, ?_⟩
      · intro i hi hai
        rcases Nat.lt_succ_iff_lt_or_eq.mp hi with h | rfl
        · exact le_trans (min_le_left ..) (ih.2.1 i h hai)
        · exact min_le_right ..
      · by_cases h : v q ≤ groupMin q a v d j
        · exact Or.inr ⟨q, by omega, haj, (min_eq_right h).symm⟩
        · rw [min_eq_left (by omega : groupMin q a v d j ≤ v q)]
          rcases ih.2.2 with hd | ⟨i, hi, hh⟩
          · exact Or.inl hd
          · exact Or.inr ⟨i, by omega, hh⟩
    · simp only [haj,ite_false]
      refine ⟨ih.1, fun i hi hai => ih.2.1 i (by
        have hne : i ≠ q := fun h => haj (h ▸ hai)
        omega) hai, ?_⟩
      rcases ih.2.2 with hd | ⟨i, hi, hh⟩
      · exact Or.inl hd
      · exact Or.inr ⟨i, by omega, hh⟩

private theorem digit_sep {B a b x y : Nat} (hab : a < b) (hx : x < B) :
    B*a+x < B*b+y := by
  have H := Nat.mul_le_mul_left B (Nat.succ_le_of_lt hab)
  rw [Nat.mul_succ] at H; omega

private theorem successor {q B d j : Nat} (a v src pos : Nat → Nat) (hj : j < q)
    (hd : d < B) (hv : ∀ t < q, v t ≤ d)
    (hsp : ∀ i, src (pos i) = i) (hps : ∀ i, pos (src i) = i)
    (hp : ∀ i < 4*q, pos i < 4*q)
    (hs : ∀ l r, l ≤ r → r < 4*q → code q B d a v (src l) ≤ code q B d a v (src r)) :
    pos j + 1 < 4*q ∧ num q d v (src (pos j+1)) = groupMin q a v d j := by
  let m := groupMin q a v d j
  obtain ⟨hmd, hmv, hor⟩ := min_spec q a v d j
  have hhead : code q B d a v j = 2*B*j := by simp [code,adr,num,hj]
  have wit : ∃ t < 4*q, code q B d a v t = 2*B*j + (B+m) := by
    rcases hor with h | ⟨i,hi,hai,hvi⟩
    · refine ⟨2*q+j, by omega, ?_⟩
      simp [code,adr,num,show ¬2*q+j<q by omega,show ¬2*q+j<2*q by omega,Nat.mod_eq_of_lt hj,m,h]
    · refine ⟨q+i,by omega, ?_⟩
      simp [code,adr,num,show ¬q+i<q by omega,show q+i<2*q by omega,hai,hvi,m]
  obtain ⟨t,ht,hcode⟩ := wit
  have hjp := hp j (by omega); have htp := hp t ht
  have hpos : pos j < pos t := by
    by_contra! h
    have H := hs _ _ h hjp
    rw [hsp,hsp,hcode,hhead] at H; omega
  have hnext : pos j + 1 < 4*q := by omega
  refine ⟨hnext, ?_⟩
  let z := src (pos j+1)
  have hne : z ≠ j := by
    intro h; have E := congrArg pos h; change pos (src (pos j+1)) = pos j at E; rw [hps] at E; omega
  have hl : 2*B*j ≤ code q B d a v z := by
    have H := hs (pos j) (pos j+1) (by omega) hnext; rwa [hsp,hhead] at H
  have hu : code q B d a v z ≤ 2*B*j+(B+m) := by
    have H := hs (pos j+1) (pos t) (by omega) htp; rwa [hsp,hcode] at H
  have hzv : num q d v z ≤ d := by
    unfold num; split <;> rename_i hh
    · omega
    · split <;> rename_i h2
      · exact hv _ (by omega)
      · exact le_rfl
  have hmB : m < B := lt_of_le_of_lt hmd hd
  have hzoff : (if z < q then 0 else B) + num q d v z < 2*B := by split <;> omega
  have haddr : adr q a z = j := by
    rcases lt_trichotomy (adr q a z) j with h | h | h
    · have H := digit_sep (y:=0) h hzoff; unfold code at hl; omega
    · exact h
    · have H := digit_sep (y:=(if z < q then 0 else B) + num q d v z) h
          (show B+m < 2*B by omega); unfold code at hu; omega
  have hn : ¬ z < q := by intro h; exact hne (by simpa [adr,h] using haddr)
  unfold code at hu; rw [haddr, ite_eq_right hn] at hu
  change num q d v z = m
  apply Nat.le_antisymm (by omega)
  by_cases hz : z < 2*q
  · simp only [adr, hn, hz, ite_false, ite_true] at haddr
    simpa [num, hn, hz] using hmv (z-q) (by omega) haddr
  · simpa [num, hn, hz] using hmd

end MinScatter
open MinScatter

theorem scatterMin {n : Nat} (e w d : Nat) (addr val : Words n) (A : Set (Sig n))
    (hc : constantsC n ⊆ A) (hv : Bank (2^e) w val ⊆ A) (ha : Bank (2^e) e addr ⊆ A)
    (hab : ∀ i < 2^e, ∀ x, addr i x < 2^e) (hvb : ∀ i < 2^e, ∀ x, val i x ≤ d)
    (hd : d < 2^w) :
    Build A (Bank (2^e) w (fun j x => groupMin (2^e) (fun i => addr i x) (fun i => val i x) d j))
      (512*(e+2)^2*(e+w+2)*(2^e)) := by
  let q := 2^e
  let N := 2^(e+2)
  have hN : N = 4*q := by dsimp [N,q]; rw [pow_add]; ring
  let net := bitonicSort 0 (e+2) true
  have hnet : ∀ c ∈ net, c.1 < N ∧ c.2.1 < N := by
    intro c hc; obtain ⟨_,h,h'⟩ := bitonicSort_mem 0 (e+2) true c hc
    simp only [Nat.zero_add] at h'; exact ⟨h.trans h',h'⟩
  let kw := w+1+e
  let st := fun (x : Fin n → Bool) i => row q w d (fun t => addr t x) (fun t => val t x) i
  have constMem : ∀ b : Bool, (fun _ : Fin n → Bool => b) ∈ A := fun b => hc ⟨b,rfl⟩
  have hK : ∀ i < N, ∀ b < kw, (fun x => (st x i).1 b) ∈ A := by
    intro i _ b hb
    by_cases hbw : b < w
    · simp only [st,row,hbw,ite_true,num]
      split <;> rename_i hi
      · exact constMem _
      · split <;> rename_i hi'
        · exact hv ⟨i-q,show i-q < q by omega,b,hbw,rfl⟩
        · exact constMem _
    · by_cases heq : b = w
      · subst b; simp only [st,row,lt_irrefl,ite_false,ite_true]; exact constMem _
      · simp only [st,row,hbw,heq,ite_false,adr]
        split <;> rename_i hi
        · exact constMem _
        · split <;> rename_i hi'
          · exact ha ⟨i-q,show i-q < q by omega,b-(w+1),by dsimp [kw] at hb; omega,rfl⟩
          · exact constMem _
  have H := netCircuit kw 0 N net hnet st hK (fun _ _ _ h => by omega) (constMem false)
  let sorted := fun x => runNet (recKey kw) net (st x)
  let nx := fun i => if i+1 < N then i+1 else i
  let ans := fun x i => (sorted x (nx i)).1
  refine relax (seq H (replayRevCircuit kw w N net hnet st ?_ ans ?_)) le_rfl ?_ ?_
  · exact fun t ht => ⟨Or.inr (Or.inr ⟨t,ht,Or.inl rfl⟩),Or.inr (Or.inr ⟨t,ht,Or.inr rfl⟩)⟩
  · exact fun i hi b hb => Or.inr (Or.inl (Or.inl ⟨nx i,by dsimp [nx]; split <;> assumption,b,by dsimp [kw]; omega,rfl⟩))
  · rintro f ⟨j,hj,b,hb,rfl⟩; right
    refine ⟨j,show j < N by change j < q at hj; omega,b,hb,?_⟩
    funext x
    let sw := netSwaps (recKey kw) net (st x)
    let src := replaySwaps sw id
    let pos := replaySwaps sw.reverse id
    obtain ⟨hsp,hps,_,hp,hsort,_,hrev⟩ := bitonicPerm (recKey kw) N net hnet (st x)
    let a := fun i => addr i x
    let v := fun i => val i x
    have hkey : ∀ i, recKey kw (st x i) = code q (2^w) d a v i := fun _ =>
      row_key (fun t ht => hab t ht x) (fun t ht => hvb t ht x) hd
    have hs : ∀ l r, l ≤ r → r < 4*q → code q (2^w) d a v (src l) ≤ code q (2^w) d a v (src r) := by
      intro l r hl hr
      have M := bitonicSort_sorted (recKey kw) (e+2) (st x) l r hl (show r < N by omega)
      change recKey kw (sorted x l) ≤ recKey kw (sorted x r) at M
      dsimp only [sorted] at M
      rwa [hsort,hsort,hkey,hkey] at M
    obtain ⟨hn,he⟩ := successor a v src pos hj hd (fun t ht => hvb t ht x) hsp hps
      (fun t ht => by rw [← hN] at ht ⊢; exact hp t ht) hs
    have hn' : pos j+1 < N := by omega
    rw [hrev]
    change (groupMin q a v d j).testBit b = (sorted x (nx (pos j))).1 b
    rw [show nx (pos j) = pos j+1 by simp [nx,hn']]
    dsimp only [sorted]; rw [hsort]
    change (groupMin q a v d j).testBit b = (row q w d a v (src (pos j+1))).1 b
    simp only [row,hb,ite_true]
    exact congrArg (fun z : Nat => z.testBit b) he.symm
  · have hn := bitonicSort_length 0 (e+2) true
    change 4*net.length = (e+2)*(e+2+1)*N at hn
    rw [hN] at hn
    have heq : net.length = (e+2)*(e+2+1)*q := by nlinarith only [hn]
    change net.length*(11*kw+6*0+1)+net.length*(6*w) ≤ 512*(e+2)^2*(e+w+2)*q
    rw [heq]; dsimp only [kw]; ring_nf; gcongr <;> omega

end PEqualNP.Outside.L_meta_32030.Work

namespace PEqualNP.Outside.L_meta_32030.Work

private theorem foldThreshold {α : Type*} (l : List α) (step : Nat → α → Nat)
    (z : Nat) (P : α → Prop) (H : ∀ d a, step d a ≤ z ↔ d ≤ z ∨ P a) (d : Nat) :
    l.foldl step d ≤ z ↔ d ≤ z ∨ ∃ a ∈ l, P a := by
  induction l generalizing d with
  | nil => simp
  | cons a l ih =>
    simp only [List.foldl_cons, ih, H, List.mem_cons]
    aesop

theorem groupMin_le_iff (Q : Nat) (addr val : Nat → Nat) (d j z : Nat) :
    groupMin Q addr val d j ≤ z ↔ d ≤ z ∨ ∃ i < Q, addr i = j ∧ val i ≤ z := by
  unfold groupMin
  rw [foldThreshold _ _ z (fun i => addr i = j ∧ val i ≤ z)]
  · simp only [List.mem_range]
  · intro a i; by_cases hi : addr i = j <;> simp [hi, min_le_iff]

theorem groupMin_le_default (Q : Nat) (addr val : Nat → Nat) (d j : Nat) :
    groupMin Q addr val d j ≤ d := (groupMin_le_iff ..).2 (Or.inl le_rfl)

def semP (N : Nat) (col tbl : Nat → Nat) (i : Nat) := tbl (col i) * N + col i
def semBP (N S : Nat) (col tbl : Nat → Nat) :=
  groupMin (N*S) (fun i => i/S) (semP N col tbl) (N^2)
def semBV (N S : Nat) (col tbl : Nat → Nat) (i : Nat) := semBP N S col tbl (i/S)*N+i/S
def semBK (N S : Nat) (row col tbl : Nat → Nat) := groupMin (N*S) row (semBV N S col tbl) (N^3)

private theorem lexBound {a b B m : Nat} (ha : a < B) (hb : b < m) : a*m+b < B*m := by
  calc a*m+b < a*m+m := Nat.add_lt_add_left hb _
       _ = (a+1)*m := (Nat.succ_mul _ _).symm
       _ ≤ B*m := Nat.mul_le_mul_right _ ha

theorem semLexBound {a b B m : Nat} (ha : a < B) (hb : b < m) : a*m+b < B*m :=
  lexBound ha hb

private theorem inBlock {S w t : Nat} (hs : 0 < S) (ht : t < S) : (w*S+t)/S = w := by
  rw [Nat.add_comm, Nat.add_mul_div_right _ _ hs, Nat.div_eq_of_lt ht, Nat.zero_add]

theorem semP_lt {N S : Nat} {col tbl : Nat → Nat}
    (hc : ∀ i < N*S, col i < N) (ht : ∀ y < N, tbl y < N) {i} (hi : i < N*S) :
    semP N col tbl i < N^2 := by simpa [semP, pow_two] using lexBound (ht _ (hc _ hi)) (hc _ hi)

theorem semBP_lt {N S : Nat} (hs : 0 < S) {col tbl : Nat → Nat}
    (hc : ∀ i < N*S, col i < N) (ht : ∀ y < N, tbl y < N) {w} (hw : w < N) :
    semBP N S col tbl w < N^2 := by
  have hi : w*S+0 < N*S := lexBound hw hs
  refine lt_of_le_of_lt ((groupMin_le_iff ..).2 (Or.inr ⟨w*S+0, hi, inBlock hs hs, le_rfl⟩)) (semP_lt hc ht hi)

theorem semBV_lt {N S : Nat} (hs : 0 < S) {col tbl : Nat → Nat}
    (hc : ∀ i < N*S, col i < N) (ht : ∀ y < N, tbl y < N) {i} (hi : i < N*S) :
    semBV N S col tbl i < N^3 := by
  have hw := (Nat.div_lt_iff_lt_mul hs).2 hi
  simpa [semBV, pow_succ] using lexBound (semBP_lt hs hc ht hw) hw

theorem semBK_le (N S : Nat) (row col tbl : Nat → Nat) (x : Nat) : semBK N S row col tbl x ≤ N^3 :=
  (groupMin_le_iff ..).2 (Or.inl le_rfl)

def semBest (N : Nat) (R T : Nat → Nat → Prop) [DecidableRel R] [DecidableRel T]
    (tbl : Nat → Nat) (x : Nat) :=
  (List.finRange N).foldl (fun acc y => (List.finRange N).foldl (fun v w =>
    if R w.val x ∧ T w.val y.val then min v ((tbl y.val*N+y.val)*N+w.val) else v) acc) (N^3)

private theorem semBest_le_iff (N : Nat) (R T : Nat → Nat → Prop) [DecidableRel R] [DecidableRel T]
    (tbl : Nat → Nat) (x z : Nat) : semBest N R T tbl x ≤ z ↔ N^3 ≤ z ∨
      ∃ y : Fin N, ∃ w : Fin N, (R w x ∧ T w y) ∧ (tbl y*N+y.val)*N+w.val ≤ z := by
  unfold semBest
  rw [foldThreshold _ _ z (fun y : Fin N => ∃ w : Fin N, (R w x ∧ T w y) ∧ (tbl y*N+y.val)*N+w.val ≤ z)]
  · simp
  · intro d y
    rw [foldThreshold _ _ z (fun w : Fin N => (R w x ∧ T w y) ∧ (tbl y*N+y.val)*N+w.val ≤ z)]
    · simp
    · intro v w; by_cases h : R w x ∧ T w y <;> simp [h, min_le_iff]

theorem semBK_eq_best {N S : Nat} (hs : 0 < S) {row col tbl : Nat → Nat}
    (hc : ∀ i < N*S, col i < N) (ht : ∀ y < N, tbl y < N)
    (R T : Nat → Nat → Prop) [DecidableRel R] [DecidableRel T]
    (hr : ∀ w < N, ∀ x < N, R w x ↔ ∃ t < S, row (w*S+t) = x)
    (htc : ∀ w < N, ∀ y < N, T w y ↔ ∃ t < S, col (w*S+t) = y)
    {x : Nat} (hx : x < N) : semBK N S row col tbl x = semBest N R T tbl x := by
  suffices he : ∀ z, semBK N S row col tbl x ≤ z ↔ semBest N R T tbl x ≤ z from
    le_antisymm ((he _).2 le_rfl) ((he _).1 le_rfl)
  intro z
  rw [semBK, groupMin_le_iff, semBest_le_iff]
  apply or_congr_right
  constructor
  · rintro ⟨i, hi, hrow, hv⟩
    let w := i/S
    have hw : w < N := (Nat.div_lt_iff_lt_mul hs).2 hi
    have decI : w*S+i%S = i := Nat.div_add_mod' _ _
    have hrw := (hr w hw x hx).2 ⟨i%S, Nat.mod_lt _ hs, (congrArg row decI).trans hrow⟩
    have bound := semBP_lt hs hc ht hw
    obtain h | ⟨j, hj, hkey, hval⟩ := (groupMin_le_iff (N*S) (fun i => i/S) (semP N col tbl) (N^2) w (semBP N S col tbl w)).1 le_rfl
    · omega
    · have decJ : w*S+j%S = j := hkey ▸ Nat.div_add_mod' j S
      refine ⟨⟨col j, hc _ hj⟩, ⟨w, hw⟩, ⟨hrw, (htc w hw _ (hc _ hj)).2 ⟨j%S, Nat.mod_lt _ hs, by rw [decJ]⟩⟩, ?_⟩
      exact le_trans (Nat.add_le_add_right (Nat.mul_le_mul_right N hval) w) hv
  · rintro ⟨y, w, ⟨hR, hT⟩, hv⟩
    obtain ⟨t, ht', hrow⟩ := (hr w w.isLt _ hx).1 hR
    obtain ⟨u, hu, hcol⟩ := (htc w w.isLt _ y.isLt).1 hT
    have hp : semBP N S col tbl w ≤ semP N col tbl (w*S+u) :=
      (groupMin_le_iff ..).2 (Or.inr ⟨_, lexBound w.isLt hu, inBlock hs hu, le_rfl⟩)
    refine ⟨_, lexBound w.isLt ht', hrow, ?_⟩
    simp only [semBV, inBlock hs ht', semP, hcol] at hp ⊢
    exact le_trans (Nat.add_le_add_right (Nat.mul_le_mul_right N hp) _) hv

def countAddr (N : Nat) (bk : Nat → Nat) (i : Nat) := (bk i/N)%N
def countVal (N : Nat) (bk : Nat → Nat) (i : Nat) := if i < N then bk i/N^3 else 1
def countImage (N : Nat) (bk : Nat → Nat) :=
  ((Finset.univ.filter (fun x : Fin N => bk x < N^3)).image (fun x : Fin N => (bk x/N)%N))

theorem count_group_zero {N Q : Nat} (hQ : N ≤ Q) (bk : Nat → Nat) (y : Nat) :
    groupMin Q (countAddr N bk) (countVal N bk) 1 y = 0 ↔ y ∈ countImage N bk := by
  rw [← Nat.le_zero, groupMin_le_iff]
  simp only [countImage, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro (h | ⟨i, _, ha, hv⟩)
    · omega
    · by_cases hi : i < N
      · have hN : 0 < N := Nat.zero_lt_of_lt hi
        have hd : bk i / N^3 < 1 := by simpa [countVal, hi] using hv
        have hlt := (Nat.div_lt_iff_lt_mul (pow_pos hN 3)).1 hd
        exact ⟨⟨_, hi⟩, by simpa using hlt, ha⟩
      · simp [countVal, hi] at hv
  · rintro ⟨i, hi, hy⟩
    exact Or.inr ⟨_, lt_of_lt_of_le i.isLt hQ, hy, by simp [countVal, i.isLt, Nat.div_eq_of_lt hi]⟩

theorem count_flags_eq_card {N Q : Nat} (hN : 0 < N) (hQ : N ≤ Q) (bk : Nat → Nat) :
    (∑ y ∈ Finset.range N, if groupMin Q (countAddr N bk) (countVal N bk) 1 y = 0 then 1 else 0) =
      (countImage N bk).card := by
  simp_rw [count_group_zero hQ bk]
  rw [← Finset.card_filter]
  congr 1
  ext y
  simp only [Finset.mem_filter, Finset.mem_range, and_iff_right_iff_imp]
  rintro hy
  obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hy
  exact Nat.mod_lt _ hN

end PEqualNP.Outside.L_meta_32030.Work

namespace PEqualNP.Outside.L_meta_32030.Work
open PEqualNP.Outside.L_meta_32030.Shared
theorem bits_length (len val : Nat) :
    ((List.range len).map (fun i => val.testBit i)).length = len := by
  simp

theorem flatMap_bits_length (m k : Nat) (f : Nat → Nat) :
    ((List.range m).flatMap (fun j => (List.range k).map (fun i => (f j).testBit i))).length = m * k := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [List.range_succ, List.flatMap_append, List.length_append, ih]
    simp [Nat.succ_mul]

theorem flatMap_bits_getD (m k : Nat) (f : Nat → Nat) (j i : Nat) (hj : j < m) (hi : i < k) :
    ((List.range m).flatMap (fun t => (List.range k).map (fun b => (f t).testBit b))).getD (j * k + i) false =
      (f j).testBit i := by
  induction m with
  | zero => omega
  | succ m ih =>
    rw [List.range_succ, List.flatMap_append]
    by_cases hjm : j < m
    · have hlt : j * k + i < ((List.range m).flatMap (fun t => (List.range k).map (fun b => (f t).testBit b))).length := by
        rw [flatMap_bits_length]
        have := Nat.mul_le_mul_right k (show j + 1 ≤ m by omega)
        rw [Nat.succ_mul] at this; omega
      rw [List.getD_append _ _ _ _ hlt]
      exact ih hjm
    · have heq : j = m := by omega
      subst j
      have hlen := flatMap_bits_length m k f
      rw [List.getD_append_right _ _ _ _ (by omega), hlen, Nat.add_sub_cancel_left]
      simp [List.getD_eq_getElem?_getD, hi]
private theorem packPri (N k : Nat) (p : Fin N → Nat) :
    (List.finRange N).flatMap (fun y => bitsC k (p y)) =
      (List.range N).flatMap (fun j => bitsC k (if hj : j<N then p ⟨j,hj⟩ else 0)) := by
  have he : (List.finRange N).map Fin.val = List.range N := by
    apply List.ext_getElem (by simp)
    intros; simp
  rw [← he, List.flatMap_map]
  congr 1; funext i; simp

theorem ofFn_vecC (k r h : Nat) (masks : Nat → Fin (2^k)) (a c : Fin (2^h)) (priority : Fin (2^k) → Fin (2^k)) :
    List.ofFn (vecC k r h masks a c priority) = inputC k r h masks a c priority := by
  have hlen : (inputC k r h masks a c priority).length = dimC k r h := by
    unfold inputC; rw [packPri]; simp [bitsC,dimC]; omega
  apply List.ext_getElem (by simp [hlen])
  intro i h1 h2; rw [List.getElem_ofFn]; exact List.getD_eq_getElem _ _ h2
set_option maxHeartbeats 2000000 in
theorem inverseRows (k r prefixLen : Nat) (hk_odd : k%2=1) (hk_three : k%3≠0)
    (hp_pos : 0<prefixLen) (hp_le : prefixLen≤k) :
    let N := 2^k
    let S := 2^(k-prefixLen)
    let M := 2^(k+(k-prefixLen))
    let dim := dimC k r prefixLen
    ∃ row col pri : Words dim,
      Build (rawC dim) (constantsC dim ∪ Bank M k row ∪ Bank M k col ∪ Bank M k pri)
        (2 + M*(2*(r*(38*k+8)+4*k))) ∧
      (∀ i v, row i v < N) ∧ (∀ i v, col i v < N) ∧ (∀ i v, pri i v < N) ∧
      (∀ i v, N ≤ i → pri i v = 0) ∧
      ∀ masks a c priority,
        let v := vecC k r prefixLen masks a c priority
        (∀ (y : Fin N), pri y.val v = (priority y).val) ∧
        (∀ (branch : Bool) (key name : Fin N),
          runC k r masks branch key.val name.val >>> (k-prefixLen) = (if branch then c else a).val ↔
          ∃ t < S, (if branch then col else row) (key.val*S+t) v = name.val) := by
  intro N S M dim
  let s := k-prefixLen
  have hk : 0<k := by omega
  have hk6 : k%6=1 ∨ k%6=5 := by omega
  have hSpos : 0<S := Nat.two_pow_pos _
  let maskV : Nat → Fin k → Sig dim := fun j i v =>
    if hj : j < 2 * r then
      v ⟨j * k + i.val, by
        have hm := Nat.mul_le_mul_right k (show j + 1 ≤ 2 * r by omega)
        rw [Nat.succ_mul] at hm; dsimp [dim,dimC]; omega⟩
    else false
  let rowTargV : Fin prefixLen → Sig dim := fun i v =>
    v ⟨2 * r * k + i.val, by dsimp [dim,dimC]; omega⟩
  let colTargV : Fin prefixLen → Sig dim := fun i v =>
    v ⟨2 * r * k + prefixLen + i.val, by dsimp [dim,dimC]; omega⟩
  let inputs : Set (Sig dim) := Set.range (fun idx : Fin dim => fun v => v idx)
  let S0 : Set (Sig dim) := inputs ∪ {fun _ => false, fun _ => true}
  have hS0_sub : inputs ⊆ S0 := Set.subset_union_left
  have H0 : Build inputs S0 2 := by
    have hconst : Build inputs {fun _ => false, fun _ => true} 2 := by
      simpa only [Set.singleton_union] using
        (seq (constG (A := inputs) false) (constG (A := inputs ∪ {fun _ => false}) true))
    have h1 := seq (idle (A := inputs) (B := inputs) le_rfl) (relax hconst Set.subset_union_left le_rfl le_rfl)
    exact relax h1 le_rfl le_rfl (by omega)
  have h0_c : ∀ c : Bool, (fun _ : Fin dim → Bool => c) ∈ S0 := fun c => by
    cases c <;> exact Or.inr (by simp)
  have h0_mask : ∀ j i, maskV j i ∈ S0 := fun j i => by
    dsimp only [maskV]
    by_cases hj : j < 2 * r
    · simp only [hj, ↓reduceDIte]; exact Or.inl ⟨_, rfl⟩
    · simp only [hj, ↓reduceDIte]; exact h0_c false
  have h0_rt : ∀ i, rowTargV i ∈ S0 := fun i => Or.inl ⟨_, rfl⟩
  have h0_ct : ∀ i, colTargV i ∈ S0 := fun i => Or.inl ⟨_, rfl⟩
  let targWord : (Fin prefixLen → Bool) → Nat → Fin k → Bool := fun tb lo i =>
    if h : i.val < s then lo.testBit i.val else tb ⟨i.val - s, by dsimp [s]; omega⟩
  let rowInvV : (Fin dim → Bool) → Nat → Nat → Fin k → Bool := fun v w lo =>
    invRunB hk r (fun j a => maskV j a v) false (ofNat k w) (targWord (fun i => rowTargV i v) lo)
  let colInvV : (Fin dim → Bool) → Nat → Nat → Fin k → Bool := fun v w lo =>
    invRunB hk r (fun j a => maskV j a v) true (ofNat k w) (targWord (fun i => colTargV i v) lo)
  let B1 : Set (Sig dim) :=
    {f | ∃ idx < M, (∃ i : Fin k, f = fun v => rowInvV v (idx / S) (idx % S) i) ∨
                    (∃ i : Fin k, f = fun v => colInvV v (idx / S) (idx % S) i)}
  have H1 : Build S0 B1 (M * (2 * (r * (38 * k + 8) + 4 * k))) := by
    have Hper : ∀ idx < M, Build S0
        ({f | ∃ i : Fin k, f = fun v => rowInvV v (idx / S) (idx % S) i} ∪
         {f | ∃ i : Fin k, f = fun v => colInvV v (idx / S) (idx % S) i})
        (2 * (r * (38 * k + 8) + 4 * k)) := by
      intro idx _
      have hr : Build S0 {f | ∃ i : Fin k, f = fun v => rowInvV v (idx / S) (idx % S) i}
          (r * (38 * k + 8) + 4 * k) :=
        invRunG hk r maskV false (ofNat k (idx / S))
          (fun i v => targWord (fun t => rowTargV t v) (idx % S) i)
          (fun i => by
            dsimp only [targWord]
            by_cases h : i.val < s
            · simp only [h, ↓reduceDIte]; exact h0_c _
            · simp only [h, ↓reduceDIte]; exact h0_rt _)
          (fun j _ i => h0_mask _ i) (h0_c true) (h0_c false)
      have hc : Build S0 {f | ∃ i : Fin k, f = fun v => colInvV v (idx / S) (idx % S) i}
          (r * (38 * k + 8) + 4 * k) :=
        invRunG hk r maskV true (ofNat k (idx / S))
          (fun i v => targWord (fun t => colTargV t v) (idx % S) i)
          (fun i => by
            dsimp only [targWord]
            by_cases h : i.val < s
            · simp only [h, ↓reduceDIte]; exact h0_c _
            · simp only [h, ↓reduceDIte]; exact h0_ct _)
          (fun j _ i => h0_mask _ i) (h0_c true) (h0_c false)
      exact relax (seq hr (relax hc Set.subset_union_left le_rfl le_rfl)) le_rfl le_rfl (by omega)
    have hall := rangeSetsG (m := M) _ _ Hper
    refine relax hall le_rfl ?_ le_rfl
    rintro f ⟨idx, hidx, hf⟩
    exact ⟨idx, hidx, hf⟩
  let pbit (y : Nat) (i : Fin k) : Sig dim := fun v =>
    if hy : y<N then v ⟨2*r*k+2*prefixLen+y*k+i.val, by
      have hm := Nat.mul_le_mul_right k (show y+1 ≤ N by omega)
      rw [Nat.succ_mul] at hm; dsimp only [dim,dimC]; change _ < 2*r*k+2*prefixLen+N*k; omega⟩ else false
  let pri : Words dim := fun y v => toNat (fun i => pbit y i v)
  let row : Words dim := fun j v => toNat (rowInvV v (j/S) (j%S))
  let col : Words dim := fun j v => toNat (colInvV v (j/S) (j%S))
  refine ⟨row,col,pri,?_,fun _ _ => toNat_lt _, fun _ _ => toNat_lt _,fun _ _ => toNat_lt _,?_,?_⟩
  · refine relax (seq H0 (relax H1 Set.subset_union_right le_rfl le_rfl)) le_rfl ?_ le_rfl
    intro f hf
    rcases hf with (((⟨b,rfl⟩|⟨j,hj,i,hi,rfl⟩)|⟨j,hj,i,hi,rfl⟩)|⟨y,hy,i,hi,rfl⟩)
    · exact Or.inl (h0_c b)
    · exact Or.inr ⟨j,hj,Or.inl ⟨⟨i,hi⟩,by funext v; simp [row,testBit_toNat,hi]⟩⟩
    · exact Or.inr ⟨j,hj,Or.inr ⟨⟨i,hi⟩,by funext v; simp [col,testBit_toNat,hi]⟩⟩
    · apply Or.inl
      by_cases hy' : y<N
      · apply Or.inl
        simp only [pri,testBit_toNat,hi,↓reduceDIte,pbit,hy']
        exact ⟨_,rfl⟩
      · convert h0_c false using 1; funext v; simp [pri,pbit,testBit_toNat,hi,hy']
  · intro y v hy
    apply Nat.eq_of_testBit_eq; intro i; simp [pri,pbit,testBit_toNat,Nat.not_lt.mpr hy]
  · intro masks rowTarget colTarget priority v
    let input := inputC k r prefixLen masks rowTarget colTarget priority
    let A0 := (List.range (2 * r)).flatMap (fun j => bitsC k (masks j).val)
    let A1 := bitsC prefixLen rowTarget.val
    let A2 := bitsC prefixLen colTarget.val
    let A3 := (List.finRange N).flatMap (fun y => bitsC k (priority y).val)
    have hLA0 : A0.length = 2 * r * k := flatMap_bits_length (2 * r) k (fun j => (masks j).val)
    have hLA1 : A1.length = prefixLen := bits_length prefixLen rowTarget.val
    have hLA2 : A2.length = prefixLen := bits_length prefixLen colTarget.val
    have hinput_eq : input = A0 ++ (A1 ++ (A2 ++ A3)) := by simp only [input,inputC,A0,A1,A2,A3,N,List.append_assoc]
    have hv_mask : ∀ j < 2 * r, ∀ i : Fin k, maskV j i v = (masks j).val.testBit i.val := by
      intro j hj i
      dsimp only [maskV, v, vecC]
      simp only [hj, ↓reduceDIte]
      have hlt : j * k + i.val < A0.length := by
        rw [hLA0]
        have hm := Nat.mul_le_mul_right k (show j + 1 ≤ 2 * r by omega)
        rw [Nat.succ_mul] at hm; omega
      change input.getD _ false = _
      rw [hinput_eq, List.getD_append _ _ _ _ hlt]
      exact flatMap_bits_getD (2 * r) k (fun t => (masks t).val) j i.val hj i.isLt
    have hv_rt : ∀ i : Fin prefixLen, rowTargV i v = rowTarget.val.testBit i.val := by
      intro i
      dsimp only [rowTargV, v, vecC]
      change input.getD _ false = _
      rw [hinput_eq, List.getD_append_right _ _ _ _ (by omega), hLA0, Nat.add_sub_cancel_left,
          List.getD_append _ _ _ _ (by rw [hLA1]; exact i.isLt)]
      simp [A1, bitsC, List.getD_eq_getElem?_getD, i.isLt]
    have hv_ct : ∀ i : Fin prefixLen, colTargV i v = colTarget.val.testBit i.val := by
      intro i
      dsimp only [colTargV, v, vecC]
      change input.getD _ false = _
      rw [hinput_eq, List.getD_append_right _ _ _ _ (by omega), hLA0,
          show 2 * r * k + prefixLen + i.val - 2 * r * k = prefixLen + i.val by omega,
          List.getD_append_right _ _ _ _ (by omega), hLA1, Nat.add_sub_cancel_left,
          List.getD_append _ _ _ _ (by rw [hLA2]; exact i.isLt)]
      simp [A2, bitsC, List.getD_eq_getElem?_getD, i.isLt]
    have hinv_congr : ∀ col (key out : Fin k → Bool),
        invRunB hk r (fun t a => maskV t a v) col key out =
        invRunB hk r (fun t => ofNat k (masks t).val) col key out := by
      intro col key out
      have hfold : ∀ (l : List Nat), (∀ t ∈ l, t < r) → ∀ st,
          l.foldl (fun z idx => invRoundB hk r (fun t a => maskV t a v) col idx key z) st =
          l.foldl (fun z idx => invRoundB hk r (fun t => ofNat k (masks t).val) col idx key z) st := by
        intro l
        induction l with
        | nil => intro _ _; rfl
        | cons a l ih =>
          intro hl st
          simp only [List.foldl_cons]
          have ha : a < r := hl a List.mem_cons_self
          have hstep : invRoundB hk r (fun t a' => maskV t a' v) col a key st =
              invRoundB hk r (fun t => ofNat k (masks t).val) col a key st := by
            dsimp only [invRoundB]
            congr 2; ext i
            have hm : (if col then r + a else a) < 2 * r := by cases col <;> simp <;> omega
            rw [hv_mask _ hm i]; rfl
          rw [hstep]
          exact ih (fun t ht => hl t (List.mem_cons_of_mem a ht)) _
      dsimp only [invRunB]
      rw [hfold (List.range r).reverse (fun t ht => by rw [List.mem_reverse, List.mem_range] at ht; exact ht)]
    have hrowInv_eq : ∀ w lo,
        rowInvV v w lo = invRunB hk r (fun t => ofNat k (masks t).val) false (ofNat k w) (combWord prefixLen rowTarget lo) := by
      intro w lo
      dsimp only [rowInvV]
      rw [hinv_congr]
      congr 1; ext i; dsimp only [targWord, combWord, s]
      by_cases h : i.val < k - prefixLen
      · simp only [h, ↓reduceDIte, ↓reduceIte]
      · simp only [h, ↓reduceDIte, ↓reduceIte]; exact hv_rt _
    have hcolInv_eq : ∀ w lo,
        colInvV v w lo = invRunB hk r (fun t => ofNat k (masks t).val) true (ofNat k w) (combWord prefixLen colTarget lo) := by
      intro w lo
      dsimp only [colInvV]
      rw [hinv_congr]
      congr 1; ext i; dsimp only [targWord, combWord, s]
      by_cases h : i.val < k - prefixLen
      · simp only [h, ↓reduceDIte, ↓reduceIte]
      · simp only [h, ↓reduceDIte, ↓reduceIte]; exact hv_ct _
    constructor
    · intro y
      rw [← toNat_ofNat (priority y).isLt]; unfold pri; apply congrArg toNat; funext i
      change pbit y.val i v = _
      simp only [pbit, y.isLt, ↓reduceDIte]
      change input.getD (2*r*k+2*prefixLen+y.val*k+i.val) false = _
      rw [hinput_eq, List.getD_append_right _ _ _ _ (by omega), hLA0,
        show 2*r*k+2*prefixLen+y.val*k+i.val-2*r*k = 2*prefixLen+y.val*k+i.val by omega,
        List.getD_append_right _ _ _ _ (by omega), hLA1,
        show 2*prefixLen+y.val*k+i.val-prefixLen = prefixLen+y.val*k+i.val by omega,
        List.getD_append_right _ _ _ _ (by omega), hLA2,
        show prefixLen+y.val*k+i.val-prefixLen = y.val*k+i.val by omega]
      dsimp only [A3]; rw [packPri]
      change ((List.range N).flatMap (fun j => bitsC k (if hj : j<N then (priority ⟨j,hj⟩).val else 0))).getD (y.val*k+i.val) false = (priority y).val.testBit i.val
      rw [show ((List.range N).flatMap (fun j => bitsC k (if hj : j<N then (priority ⟨j,hj⟩).val else 0))).getD (y.val*k+i.val) false = _ from flatMap_bits_getD N k (fun j => if hj : j<N then (priority ⟨j,hj⟩).val else 0) y.val i.val y.isLt i.isLt]
      simp only [y.isLt,↓reduceDIte]
      rfl
    · intro branch key name
      have hd (t : Nat) (ht : t<S) : (key.val*S+t)/S = key.val := by
        rw [Nat.add_comm,Nat.mul_comm,Nat.add_mul_div_left _ _ hSpos,Nat.div_eq_of_lt ht,Nat.zero_add]
      have hm (t : Nat) (ht : t<S) : (key.val*S+t)%S = t := by
        rw [Nat.add_comm,Nat.mul_comm,Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt ht]
      cases branch
      · apply (invRun_shift_iff hk hk6 hp_le r masks false rowTarget key name).trans
        apply exists_congr; intro t; apply and_congr_right; intro ht
        simp only [Bool.false_eq_true, ↓reduceIte,row,hd t ht,hm t ht,hrowInv_eq]; exact eq_comm
      · apply (invRun_shift_iff hk hk6 hp_le r masks true colTarget key name).trans
        apply exists_congr; intro t; apply and_congr_right; intro ht
        simp only [↓reduceIte,col,hd t ht,hm t ht,hcolInv_eq]; exact eq_comm
end PEqualNP.Outside.L_meta_32030.Work

namespace PEqualNP.Outside.L_meta_32030.Work
open PEqualNP.Outside.L_meta_32030.Shared

def pv {n} (k : Nat) (pri col : Words n) : Words n := fun i x => pri (col i x) x * 2^k + col i x
def bpW {n} (k e S : Nat) (pri col : Words n) : Words n := fun j x => groupMin (2^e) (fun i => i/S) (fun i => pv k pri col i x) ((2^k)^2) j
def bvW {n} (k e S : Nat) (pri col : Words n) : Words n := fun i x => bpW k e S pri col (i/S) x * 2^k + i/S
def bestW {n} (k e S : Nat) (pri row col : Words n) : Words n := fun j x => groupMin (2^e) (fun i => row i x) (fun i => bvW k e S pri col i x) ((2^k)^3) j
def valSeen {n} (k : Nat) (bk : Words n) : Words n := fun i x => if i < 2^k then bk i x / (2^k)^3 else 1
def seenW {n} (k e : Nat) (bk : Words n) : Words n := fun j x => groupMin (2^e) (fun i => (bk i x/2^k)%2^k) (fun i => valSeen k bk i x) 1 j
def hitW {n} (k e : Nat) (bk : Words n) (i : Nat) : Sig n := fun x => !(seenW k e bk i x).testBit 0
def outCount {n} (k e : Nat) (bk : Words n) (b : Nat) : Sig n := fun x => popBits (fun i => hitW k e bk i x) 0 k b

private theorem gm_acc_le (ls : List Nat) (a v : Nat → Nat) (d j : Nat) : ls.foldl (fun b i => if a i=j then min b (v i) else b) d ≤ d := by
  induction ls generalizing d with
  | nil => rfl
  | cons i is ih => rw [List.foldl_cons]; exact (ih _).trans (by split <;> simp)
private theorem gm_default (Q : Nat) (a v : Nat → Nat) (d j : Nat) : groupMin Q a v d j ≤ d := gm_acc_le _ _ _ _ _
private theorem gm_le_at (ls : List Nat) (a v : Nat → Nat) (d i : Nat) (hi : i ∈ ls) : ls.foldl (fun b t => if a t = a i then min b (v t) else b) d ≤ v i := by
  induction ls generalizing d with
  | nil => simp at hi
  | cons t ts ih =>
    rw [List.foldl_cons]; rcases List.mem_cons.mp hi with rfl | hh
    · rw [if_pos rfl]; exact (gm_acc_le _ _ _ _ _).trans (min_le_right _ _)
    · exact ih _ hh
private theorem joinBound (B a b : Nat) (ha : a<B) (hb : b<B) : a*B+b < B^2 := by
  have t := Nat.mul_le_mul_right B (show a+1≤B by omega); rw [Nat.add_mul,one_mul] at t
  rw [pow_two]; omega

theorem pipe {n : Nat} (gatherOK : GatherOK n) (minOK : MinOK n) (k s : Nat) (hs : s≤k)
    (pri row col : Words n) (A : Set (Sig n)) (con : constantsC n ⊆ A)
    (rowB : Bank (2^(k+s)) k row ⊆ A) (colB : Bank (2^(k+s)) k col ⊆ A) (priB : Bank (2^(k+s)) k pri ⊆ A)
    (rBound : ∀ i x, row i x < 2^k) (cBound : ∀ i x, col i x < 2^k) (pBound : ∀ i x, pri i x < 2^k) :
    let e := k+s; let bk := bestW k e (2^s) pri row col
    Build A (Bank (2^k) (3*k+1) bk ∪ {f | ∃ b<k+1, f=outCount k e bk b}) (50000*(k+1)^3*2^(k+s)) := by
  let e := k+s; let N:=2^k; let S:=2^s; let Q:=2^e
  let bk := bestW k e S pri row col
  let f1 : Words n := fun i x => pri (col i x) x
  let A1 := A ∪ Bank Q k f1
  have nq : N≤Q := Nat.pow_le_pow_right (by decide) (by dsimp [e]; omega)
  have sn : N*S=Q := by dsimp [N,S,Q,e]; rw [Nat.pow_add]
  have sp : 0<S := Nat.two_pow_pos _
  have keylt {i : Nat} (h:i<Q) : i/S<N := (Nat.div_lt_iff_lt_mul sp).mpr (by rwa [sn])
  have h1 : Build A (Bank Q k f1) (fee e k) := gatherOK e k pri col A con priB (bankWide con colB (fun i _ => cBound i)) (fun i _ x => (cBound i x).trans_le nq) (fun i _ => pBound i)
  have h1full : Build A A1 (fee e k) := by
    exact relax (seq (idle (A:=A) (B:=A) le_rfl) (relax h1 Set.subset_union_left le_rfl le_rfl)) le_rfl le_rfl (by omega)
  have c1 : constantsC n ⊆ A1 := con.trans Set.subset_union_left
  have pvb : Bank Q (2*k+1) (pv k pri col) ⊆ A1 := by
    have b0 : Bank Q (k+k) (pv k pri col) ⊆ A1 := bankJoin (colB.trans Set.subset_union_left) (show Bank Q k f1 ⊆ A1 from Set.subset_union_right) (fun i _ => cBound i)
    apply bankWide c1 b0
    intro i _ x; dsimp [pv]; rw [Nat.pow_add,←pow_two]; exact joinBound _ _ _ (pBound _ _) (cBound _ _)
  have pairLt (i : Nat) (x : Fin n → Bool) : pv k pri col i x<N^2 := joinBound _ _ _ (pBound _ _) (cBound _ _)
  let bp := bpW k e S pri col
  let A2 := A1 ∪ Bank Q (2*k+1) bp
  have h2 : Build A1 (Bank Q (2*k+1) bp) (fee e (2*k+1)) := by
    apply minOK e (2*k+1) (N^2) (fun i _ => i/S) (pv k pri col) A1 c1 pvb (bankStatic c1 _)
    · exact fun i hi _ => (keylt hi).trans_le nq
    · exact fun i _ x => (pairLt i x).le
    · dsimp [N]; rw [←Nat.pow_mul, Nat.mul_comm k 2, Nat.pow_succ]; have := Nat.two_pow_pos (2*k); omega
  have h2full : Build A A2 (fee e k + fee e (2*k+1)) := chainKeep h1full h2
  have c2 : constantsC n ⊆ A2 := c1.trans Set.subset_union_left
  have bpBound {j : Nat} (hj : j<N) (x) : bp j x < N^2 := by
    have hini : j*S<Q := by rw [←sn]; exact Nat.mul_lt_mul_of_pos_right hj sp
    have hle := gm_le_at (List.range Q) (fun i => i/S) (fun i => pv k pri col i x) (N^2) (j*S) (List.mem_range.mpr hini)
    simp only [Nat.mul_div_cancel _ sp] at hle
    exact hle.trans_lt (pairLt _ _)
  have bb : Bank Q (3*k+1) (bvW k e S pri col) ⊆ A2 := by
    have b := bankReindex (show Bank Q (2*k+1) bp ⊆ A2 from Set.subset_union_right) (fun i => i/S) (fun i hi => (keylt hi).trans_le nq)
    have a := bankJoin (bankStatic (w:=k) c2 (fun i => i/S)) b (fun i hi _ => keylt hi)
    convert a using 1 <;> congr 1 <;> omega
  have tripleLt {i : Nat} (hi:i<Q) (x) : bvW k e S pri col i x<N^3 := by
    have lim := Nat.mul_le_mul_right N (show bp (i/S) x + 1 ≤ N^2 from bpBound (keylt hi) x)
    rw [Nat.add_mul,one_mul] at lim; change bp (i/S) x * N + i/S < N ^ 3
    have := keylt hi; rw [pow_succ N 2]; omega
  let A3 := A2 ∪ Bank Q (3*k+1) bk
  have h3 : Build A2 (Bank Q (3*k+1) bk) (fee e (3*k+1)) := by
    apply minOK e (3*k+1) (N^3) row (bvW k e S pri col) A2 c2 bb
    · exact bankWide c2 (rowB.trans (Set.subset_union_left.trans Set.subset_union_left)) (fun i _ => rBound i)
    · exact fun i _ x => (rBound i x).trans_le nq
    · exact fun i hi x => (tripleLt hi x).le
    · dsimp [N]; rw [←Nat.pow_mul,Nat.mul_comm k 3,Nat.pow_succ]; have := Nat.two_pow_pos (3*k); omega
  have h3full := chainKeep h2full h3
  have c3 : constantsC n ⊆ A3 := c2.trans Set.subset_union_left
  have kb : Bank Q (3*k+1) bk ⊆ A3 := Set.subset_union_right
  have bkLe (i x) : bk i x ≤ N^3 := gm_default _ _ _ _ _
  have p3 : (2^k)^3 = 2^(3*k) := by rw [←Nat.pow_mul,Nat.mul_comm k 3]
  have vSeenB : Bank Q 1 (valSeen k bk) ⊆ A3 := by
    rintro _ ⟨i,hi,b,hb,rfl⟩; have bz : b=0 := by omega
    subst b; by_cases lt : i<N
    · have heq : (fun x => (valSeen k bk i x).testBit 0) = fun x => (bk i x).testBit (3*k) := by
        funext x; simp only [valSeen,ite_eq_left (show i<2^k from lt),p3,Nat.testBit_div_two_pow,Nat.zero_add]
      rw [heq]; exact wire kb hi (by omega)
    · have heq : (fun x => (valSeen k bk i x).testBit 0) = fun _ => (1:Nat).testBit 0 := by
        funext x; simp [valSeen,show ¬ i<2^k from lt]
      rw [heq]; exact constWire c3 _
  let sw := seenW k e bk
  have h4 : Build A3 (Bank Q 1 sw) (fee e 1) := by
    apply minOK e 1 1 (fun i x => (bk i x /N)%N) (valSeen k bk) A3 c3 vSeenB
    · exact bankWide c3 (bankName kb) (fun i _ x => Nat.mod_lt _ (Nat.two_pow_pos k))
    · exact fun _ _ _ => (Nat.mod_lt _ (Nat.two_pow_pos k)).trans_le nq
    · intro i _ x; dsimp [valSeen]; split
      · exact (Nat.div_le_div_right (bkLe i x)).trans (by rw [Nat.div_self (by dsimp [N]; positivity)])
      · rfl
    · decide
  have h4full := chainKeep h3full h4
  let A4 := A3 ∪ Bank Q 1 sw
  have h5 : Build A4 {f | ∃ i<N, f=hitW k e bk i} N := by
    simpa using (rangeG (m:=N) (A:=A4) (F:=hitW k e bk) 1 (fun i hi => notG (wire (show Bank Q 1 sw ⊆ A4 from Set.subset_union_right) (hi.trans_le nq) (by decide : 0<1))))
  have h5full := chainKeep h4full h5
  let A5 := A4 ∪ {f | ∃ i<N, f=hitW k e bk i}
  have h6 : Build A5 {f | ∃ b<k+1, f=outCount k e bk b} (24*N) := by
    have hf : (fun _ => false) ∈ A5 := Or.inl (Or.inl (constWire c3 false))
    apply popCountG (hitW k e bk) hf k 0
    intro j hj; exact Or.inr ⟨j,hj,by rw [Nat.zero_add]⟩
  apply relax (chainKeep h5full h6) le_rfl
  · intro f hf; rcases hf with hf|hf
    · obtain ⟨i,hi,b,hb,rfl⟩ := hf
      exact Or.inl (Or.inl (Or.inl (Or.inr ⟨i,hi.trans_le nq,b,hb,rfl⟩)))
    · exact Or.inr hf
  · have he : e≤2*k := by dsimp [e]; omega
    have f1b := feeBound e k k he (by omega);have f2b := feeBound e (2*k+1) k he (by omega)
    have f3b := feeBound e (3*k+1) k he le_rfl;have f4b := feeBound e 1 k he (by omega)
    have Qle : Q ≤ (k+1)^3*Q := Nat.le_mul_of_pos_left _ (by positivity)
    change _ ≤ 50000*(k+1)^3*Q
    change fee e k + fee e (2*k+1) + fee e (3*k+1) + fee e 1 + N + 24*N ≤ _
    change fee e k ≤ 12288*(k+1)^3*Q at f1b
    change fee e (2*k+1) ≤ 12288*(k+1)^3*Q at f2b
    change fee e (3*k+1) ≤ 12288*(k+1)^3*Q at f3b
    change fee e 1 ≤ 12288*(k+1)^3*Q at f4b
    simp only [Nat.mul_assoc] at f1b f2b f3b f4b ⊢
    omega
end PEqualNP.Outside.L_meta_32030.Work

namespace PEqualNP.Outside.L_meta_32030.Work
open PEqualNP.Outside.L_meta_32030.Shared

private theorem flags_count (f : Nat → Bool) (m : Nat) :
    ((List.range m).map f).count true = ∑ i ∈ Finset.range m, if f i then 1 else 0 := by
  induction m with
  | zero => simp
  | succ m ih => rw [List.range_succ, List.map_append, List.count_append, ih, Finset.sum_range_succ]; cases hh : f m <;> simp [hh]

private theorem count_output {n : Nat} (k e : Nat) (hne : 2^k ≤ 2^e) (bk : Words n)
    (v : Fin n → Bool) {b : Nat} (hb : b < k+1) :
    outCount k e bk b v = (countImage (2^k) (fun i => bk i v)).card.testBit b := by
  let f := fun i => hitW k e bk i v
  change popBits f 0 k b = _
  rw [← bitsVal_testBit (popBits f 0 k) _ _ hb, bitsVal_popBits]
  simp only [Nat.zero_add, flags_count]
  congr 1
  rw [← count_flags_eq_card (Nat.two_pow_pos k) hne]
  apply Finset.sum_congr rfl
  intro i _
  have hle : seenW k e bk i v ≤ 1 := groupMin_le_default ..
  change (if !(seenW k e bk i v).testBit 0 then _ else _) = (if seenW k e bk i v = 0 then _ else _)
  rcases (show seenW k e bk i v = 0 ∨ seenW k e bk i v = 1 by omega) with h|h <;> simp [h]

def pktBest (k r h : Nat) (masks : Nat → Fin (2^k)) (a c : Fin (2^h))
    (priority : Fin (2^k) → Fin (2^k)) (x : Fin (2^k)) :=
  (List.finRange (2^k)).foldl (fun acc y => (List.finRange (2^k)).foldl (fun v w =>
    if runC k r masks false w.val x.val >>> (k-h) = a.val ∧
       runC k r masks true w.val y.val >>> (k-h) = c.val then
      min v (((priority y).val*2^k+y.val)*2^k+w.val) else v) acc) ((2^k)^3)

def pktCount {N : Nat} (best : Fin N → Nat) :=
  ((Finset.univ.filter (fun x : Fin N => best x < N^3)).image (fun x => (best x/N)%N)).card

private theorem finPacket (N W : Nat) (p : Fin N → Nat) :
    (List.finRange N).flatMap (fun y => bitsC W (p y)) =
    (List.range N).flatMap (fun j => bitsC W (if hj : j<N then p ⟨j,hj⟩ else 0)) := by
  have he : (List.finRange N).map Fin.val = List.range N := by
    apply List.ext_getElem (by simp); intros; simp
  rw [← he, List.flatMap_map]
  congr 1; funext i; simp

theorem packetCorrect (k r h : Nat) (row col pri : Words (dimC k r h))
    (masks : Nat → Fin (2^k)) (a c : Fin (2^h)) (priority : Fin (2^k) → Fin (2^k))
    (cBound : ∀ i v, col i v < 2^k)
    (pCorr : ∀ y : Fin (2^k), pri y.val (vecC k r h masks a c priority) = (priority y).val)
    (coverage : ∀ (branch : Bool) (key name : Fin (2^k)),
      runC k r masks branch key.val name.val >>> (k-h) = (if branch then c else a).val ↔
      ∃ t < 2^(k-h), (if branch then col else row) (key.val*2^(k-h)+t) (vecC k r h masks a c priority) = name.val)
    (j : Nat) (hj : j < 2^k*(3*k+1)+k+1) :
    let v := vecC k r h masks a c priority
    let bk := bestW k (k+(k-h)) (2^(k-h)) pri row col
    let best := pktBest k r h masks a c priority
    (if j < 2^k*(3*k+1) then (bk (j/(3*k+1)) v).testBit (j%(3*k+1))
     else outCount k (k+(k-h)) bk (j-2^k*(3*k+1)) v) =
      ((List.finRange (2^k)).flatMap (fun x => bitsC (3*k+1) (best x)) ++ bitsC (k+1) (pktCount best)).getD j false := by
  intro v bk best
  let N := 2^k; let S := 2^(k-h); let W := 3*k+1
  let R := fun w x : Nat => runC k r masks false w x >>> (k-h) = a.val
  let T := fun w y : Nat => runC k r masks true w y >>> (k-h) = c.val
  have bEq (x : Fin N) : bk x.val v = best x := by
    have H := semBK_eq_best (N:=N) (S:=S) (row:=fun i => row i v) (col:=fun i => col i v) (tbl:=fun i => pri i v)
      (Nat.two_pow_pos _) (fun i _ => cBound i v) (fun y hy => (pCorr ⟨y,hy⟩) ▸ (priority ⟨y,hy⟩).isLt) R T
      (fun w hw x hx => coverage false ⟨w, hw⟩ ⟨x,hx⟩) (fun w hw y hy => coverage true ⟨w,hw⟩ ⟨y,hy⟩) x.isLt
    trans semBK N S (fun i => row i v) (fun i => col i v) (fun i => pri i v) x
    · unfold bk bestW bvW bpW pv
      rw [Nat.pow_add]
      rfl
    · rw [H]; unfold semBest best pktBest
      simp only [N, R, T, v, pCorr]
  have hcount : (countImage N (fun i => bk i v)).card = pktCount best := by
    simp only [countImage, pktCount, bEq, N]
  let extBest := fun j : Nat => if hj : j<N then best ⟨j,hj⟩ else 0
  let headBits := (List.range N).flatMap (fun j => bitsC W (extBest j))
  have plen : headBits.length = N*W := flatMap_bits_length ..
  rw [finPacket]
  change (if j<N*W then _ else _) = (headBits ++ _).getD j false
  by_cases hprefix : j<N*W
  · rw [if_pos hprefix, List.getD_append _ _ _ _ (by omega)]
    have hW : 0<W := by dsimp [W]; omega
    have hdiv := (Nat.div_lt_iff_lt_mul hW).2 hprefix
    have hm := Nat.mod_lt j hW
    have get := flatMap_bits_getD N W extBest (j/W) (j%W) hdiv hm
    rw [Nat.div_add_mod'] at get
    rw [show headBits.getD j false = (extBest (j/W)).testBit (j%W) from get]
    exact congrArg (fun u : Nat => u.testBit (j%W)) (by simpa only [extBest, dif_pos hdiv] using bEq ⟨j/W,hdiv⟩)
  · rw [if_neg hprefix, List.getD_append_right _ _ _ _ (by omega), plen]
    have hb : j-N*W < k+1 := by change j < N*W+k+1 at hj; omega
    have hne : N ≤ 2^(k+(k-h)) := Nat.pow_le_pow_right (by decide) (by omega)
    rw [count_output k _ hne _ _ hb, hcount]
    simp [bitsC, List.getD_eq_getElem?_getD, hb]

end PEqualNP.Outside.L_meta_32030.Work

namespace PEqualNP.Outside.L_meta_32030.Work
open PEqualNP.Outside.L_meta_32030.Shared PEqualNP.CircuitLowerBounds
set_option maxHeartbeats 2000000 in
theorem solve (go : ∀ n, GatherOK n) (mo : ∀ n, MinOK n) : (∀ k r h : ℕ, k % 2 = 1 → k % 3 ≠ 0 → 0 < h → h ≤ k →
  let N := 2^k
  let X := Fin N
  let rot := fun (d x : ℕ) => ((x <<< (d % k)) ||| (x >>> (k-d % k))) % N
  let chi := fun (x : ℕ) => (List.range k).foldl (fun (acc i : ℕ) =>
    acc ||| ((xor (x.testBit i) (!(x.testBit ((i+1) % k)) && x.testBit ((i+2) % k))).toNat <<< i)) 0
  let run := fun (masks : ℕ → X) (col : Bool) (key name : ℕ) =>
    let gap : ℕ := if col then 2 else 1
    (List.range r).foldl (fun z j =>
      let mixed := z ^^^ rot gap z ^^^ rot (k-gap % k) z
      chi mixed ^^^ rot (if col then 3*(j+1)+1 else 2*j) key ^^^
        (masks (if col then r+j else j)).val) (rot (if col then 3 else 1) key ^^^ name)
  let bits := fun (len val : ℕ) => (List.range len).map (fun i => val.testBit i)
  let dim := 2*r*k+2*h+N*k
  let numOut := N*(3*k+1)+k+1
  ∃ (C : PEqualNP.CircuitLowerBounds.Circuit) (out : Fin numOut → Fin (dim+C.size)),
    PEqualNP.MetaComplexity.FanInTwo C ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack dim C ∧
    C.output < dim+C.size ∧ C.size ≤ 1048576*(r+1)*(k+1)^3 * 2^(2*k-h) ∧
    ∀ (masks : ℕ → X) (a c : Fin (2^h)) (priority : X → X),
      let input := (List.range (2*r)).flatMap (fun j => bits k (masks j).val) ++
        bits h a.val ++ bits h c.val ++ (List.finRange N).flatMap (fun y => bits k (priority y).val)
      let best := fun (x : X) => (List.finRange N).foldl (fun acc y =>
        (List.finRange N).foldl (fun v w =>
          if run masks false w.val x.val >>> (k-h) = a.val ∧
            run masks true w.val y.val >>> (k-h) = c.val then
            min v (((priority y).val*N+y.val)*N+w.val) else v) acc) (N^3)
      let count := ((Finset.univ.filter (fun x : X => best x < N^3)).image
        (fun x => (best x / N) % N)).card
      let answer := (List.finRange N).flatMap (fun x => bits (3*k+1) (best x)) ++ bits (k+1) count
      ∀ j : Fin numOut, (C.wires input).getD (out j).val false = answer.getD j.val false) := by
  intro k r h hk hk3 hp hle N X rot chi run bits dim numOut
  let s := k-h
  let e := k+s
  let M := 2^e
  let W := 3*k+1
  obtain ⟨row,col,pri,bi,rl,cl,pl,_,sem⟩ := inverseRows k r h hk hk3 hp hle
  let A := constantsC dim ∪ Bank M k row ∪ Bank M k col ∪ Bank M k pri
  let bk := bestW k e (2^s) pri row col
  have bp := pipe (go dim) (mo dim) k s (Nat.sub_le _ _) pri row col A
    (fun _ hf => Or.inl (Or.inl (Or.inl hf))) (fun _ hf => Or.inl (Or.inl (Or.inr hf)))
    (fun _ hf => Or.inl (Or.inr hf)) (fun _ hf => Or.inr hf) rl cl pl
  have bb := seq bi (relax bp Set.subset_union_right le_rfl le_rfl)
  obtain ⟨c,hc,gs,hgs,hread,hfan,hw⟩ := bb.run (schedStart (F:=id) (fun i : Fin dim => fun v => v i) (by intros; rfl)) le_rfl
  let C : Circuit := ⟨gs,0⟩
  have hsiz : C.size=c := by simp [C,Circuit.size,hgs]
  let f (j : Fin numOut) : Sig dim := fun v => if j.val < N*W then (bk (j.val / W) v).testBit (j.val % W)
    else outCount k e bk (j.val-N*W) v
  have hout (j : Fin numOut) : ∃ idx < dim + C.size, ∀ v, (C.wires (List.ofFn v)).getD idx false = f j v := by
    have hm : f j ∈ Bank N W bk ∪ {g | ∃ b<k+1, g=outCount k e bk b} := by
      by_cases hj : j.val<N*W
      · refine Or.inl ⟨j.val / W,(Nat.div_lt_iff_lt_mul (by dsimp [W]; omega)).mpr hj, j.val % W,Nat.mod_lt _ (by dsimp [W]; omega),?_⟩
        funext; simp [f,hj]
      · refine Or.inr ⟨j.val-N*W,by have := j.isLt; change j.val < N*W+k+1 at this; omega,?_⟩
        funext; simp [f,hj]
    obtain ⟨idx,hi,hh⟩ := hw _ (Or.inr (Or.inr hm))
    exact ⟨idx,by rw [hsiz]; change idx < dim+(0+c) at hi; simpa using hi,hh⟩
  let out (j : Fin numOut) : Fin (dim+C.size) := ⟨(hout j).choose,(hout j).choose_spec.1⟩
  refine ⟨C,out,hfan,hread,?_,?_,?_⟩
  · change 0 < dim+C.size; dsimp [dim]; omega
  · rw [hsiz]; apply hc.trans
    change 2 + M*(2*(r*(38*k+8)+4*k)) + 50000*(k+1)^3*M ≤ 1048576*(r+1)*(k+1)^3*2^(2*k-h)
    have hm : 2^(2*k-h) = M := by dsimp [M,e,s]; congr 1; omega
    rw [hm]; have hm1 : 1 ≤ M := Nat.two_pow_pos _
    have ci : 2 + 2*(r*(38*k+8)+4*k)+50000*(k+1)^3 ≤ 1048576*(r+1)*(k+1)^3 := by
      ring_nf; omega
    have zz := Nat.mul_le_mul_right M ci
    rw [Nat.add_mul,Nat.add_mul] at zz
    rw [Nat.mul_comm M]; omega
  · intro masks a cTarget priority input best count answer j
    let v := vecC k r h masks a cTarget priority
    have hv : List.ofFn v = input := ofFn_vecC k r h masks a cTarget priority
    rw [←hv, (hout j).choose_spec.2 v]
    obtain ⟨pc,cov⟩ := sem masks a cTarget priority
    exact packetCorrect k r h row col pri masks a cTarget priority cl pc cov j.val j.isLt
end PEqualNP.Outside.L_meta_32030.Work

theorem PEqualNP.Outside.L_meta_32030 : (∀ k r h : ℕ, k % 2 = 1 → k % 3 ≠ 0 → 0 < h → h ≤ k →
  let N := 2^k
  let X := Fin N
  let rot := fun (d x : ℕ) => ((x <<< (d % k)) ||| (x >>> (k-d % k))) % N
  let chi := fun (x : ℕ) => (List.range k).foldl (fun (acc i : ℕ) =>
    acc ||| ((xor (x.testBit i) (!(x.testBit ((i+1) % k)) && x.testBit ((i+2) % k))).toNat <<< i)) 0
  let run := fun (masks : ℕ → X) (col : Bool) (key name : ℕ) =>
    let gap : ℕ := if col then 2 else 1
    (List.range r).foldl (fun z j =>
      let mixed := z ^^^ rot gap z ^^^ rot (k-gap % k) z
      chi mixed ^^^ rot (if col then 3*(j+1)+1 else 2*j) key ^^^
        (masks (if col then r+j else j)).val) (rot (if col then 3 else 1) key ^^^ name)
  let bits := fun (len val : ℕ) => (List.range len).map (fun i => val.testBit i)
  let dim := 2*r*k+2*h+N*k
  let numOut := N*(3*k+1)+k+1
  ∃ (C : PEqualNP.CircuitLowerBounds.Circuit) (out : Fin numOut → Fin (dim+C.size)),
    PEqualNP.MetaComplexity.FanInTwo C ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack dim C ∧
    C.output < dim+C.size ∧ C.size ≤ 1048576*(r+1)*(k+1)^3 * 2^(2*k-h) ∧
    ∀ (masks : ℕ → X) (a c : Fin (2^h)) (priority : X → X),
      let input := (List.range (2*r)).flatMap (fun j => bits k (masks j).val) ++
        bits h a.val ++ bits h c.val ++ (List.finRange N).flatMap (fun y => bits k (priority y).val)
      let best := fun (x : X) => (List.finRange N).foldl (fun acc y =>
        (List.finRange N).foldl (fun v w =>
          if run masks false w.val x.val >>> (k-h) = a.val ∧
            run masks true w.val y.val >>> (k-h) = c.val then
            min v (((priority y).val*N+y.val)*N+w.val) else v) acc) (N^3)
      let count := ((Finset.univ.filter (fun x : X => best x < N^3)).image
        (fun x => (best x / N) % N)).card
      let answer := (List.finRange N).flatMap (fun x => bits (3*k+1) (best x)) ++ bits (k+1) count
      ∀ j : Fin numOut, (C.wires input).getD (out j).val false = answer.getD j.val false) := by
  apply PEqualNP.Outside.L_meta_32030.Work.solve
  · exact fun _ e w src addr A hc hs ha hb _ =>
      PEqualNP.Outside.L_meta_32030.Work.gather e w src addr A hc hs ha hb
  · exact fun _ => PEqualNP.Outside.L_meta_32030.Work.scatterMin
