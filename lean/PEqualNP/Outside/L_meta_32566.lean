import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_32566

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

-- Signal, sorting, and cipher lemmas ported from a5155e523e2d6953c6a74fecf481bd6d63aa9bc8, lean/PEqualNP/Outside/L_meta_32053.lean.
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

theorem finRange_map_getD {α : Type*} (N : Nat) (f : Fin N → α) (d : α) (x : Nat) (hx : x < N) :
    ((List.finRange N).map f).getD x d = f ⟨x, hx⟩ := by
  rw [List.getD_eq_getElem _ _ (by simp [hx]), List.getElem_map, List.getElem_finRange]
  rfl

-- Fragment Input.

section Input

variable {n : Nat}

abbrev Word (n w : Nat) := Fin w → Sig n

def projections (n : Nat) : Set (Sig n) := Set.range (fun i : Fin n => fun x => x i)
def initial (n : Nat) : Set (Sig n) := projections n ∪ {fun _ => false, fun _ => true}

lemma initial_build : Build (projections n) (initial n) 2 := by
  have h := seq (constG (A := projections n) false)
    (constG (A := projections n ∪ {fun _ => false}) true)
  exact relax (seq (idle (A := projections n) (B := projections n) le_rfl)
    (relax h Set.subset_union_left le_rfl le_rfl)) le_rfl
    (by rintro f (hf | hf); exact Or.inl hf; rcases hf with rfl | rfl <;> simp) (by omega)

lemma initial_const (b : Bool) : (fun _ : Fin n → Bool => b) ∈ initial n := by
  cases b <;> exact Or.inr (by simp)

lemma build_keep {A B : Set (Sig n)} {b : Nat} (h : Build A B b) :
    Build A (A ∪ B) b := by
  exact relax (seq (idle (A := A) (B := A) le_rfl)
    (relax h Set.subset_union_left le_rfl le_rfl)) le_rfl le_rfl (by omega)

lemma build_next {A B C : Set (Sig n)} {b c : Nat}
    (h : Build A B b) (g : Build B C c) : Build A C (b+c) :=
  relax (seq h (relax g Set.subset_union_right le_rfl le_rfl)) le_rfl Set.subset_union_right le_rfl

lemma finSetsG {m : Nat} {A : Set (Sig n)} (S : Fin m → Set (Sig n)) (c : Nat)
    (h : ∀ i, Build A (S i) c) : Build A {f | ∃ i, f ∈ S i} (m*c) := by
  have h' := listBuildSets (List.finRange m) S c (fun i _ => h i)
  rw [List.length_finRange] at h'
  exact relax h' le_rfl (by rintro f ⟨i, hi⟩; exact ⟨i, List.mem_finRange _, hi⟩) le_rfl

lemma set_range₂ {α β γ : Type*} (f : α → β → γ) :
    {x | ∃ a, x ∈ Set.range (f a)} = Set.range (fun p : α × β => f p.1 p.2) := by
  ext x; constructor
  · rintro ⟨a,b,rfl⟩; exact ⟨(a,b),rfl⟩
  · rintro ⟨⟨a,b⟩,rfl⟩; exact ⟨a,b,rfl⟩

lemma gather₂ {a b : Nat} {A : Set (Sig n)} (S : Fin a → Fin b → Set (Sig n)) (c : Nat)
    (h : ∀ i j, Build A (S i j) c) : Build A {f | ∃ i j, f ∈ S i j} (a*b*c) := by
  simpa only [Nat.mul_assoc, Set.mem_setOf_eq] using finSetsG (fun i => {f | ∃ j, f ∈ S i j}) (b*c)
    (fun i => finSetsG (S i) c (h i))

lemma gather₃ {a b c : Nat} {A : Set (Sig n)} (S : Fin a → Fin b → Fin c → Set (Sig n)) (cost : Nat)
    (h : ∀ i j l, Build A (S i j l) cost) :
    Build A {f | ∃ i j l, f ∈ S i j l} (a*b*c*cost) := by
  simpa only [Nat.mul_assoc, Set.mem_ofPred_eq] using finSetsG (fun i => {f | ∃ j l, f ∈ S i j l}) (b*c*cost)
    (fun i => gather₂ (S i) cost (h i))

abbrev dimOf (k r B hRow hCol : Nat) := 2*r*k+hRow+hCol+B*k+2^k

def maskAt (k r B hRow hCol : Nat) (j : Nat) : Word (dimOf k r B hRow hCol) k :=
  fun i x => if hj : j < 2*r then x ⟨j*k+i.val, by
    have hm := Nat.mul_le_mul_right k (show j+1 ≤ 2*r by omega)
    rw [Nat.succ_mul] at hm
    exact (show j*k+i.val < 2*r*k from by have := i.isLt; omega).trans_le
      (by dsimp [dimOf]; have := Nat.two_pow_pos k; omega)⟩ else false

def rowAt (k r B hRow hCol : Nat) : Word (dimOf k r B hRow hCol) hRow :=
  fun i x => x ⟨2*r*k+i.val, by
    exact (Nat.add_lt_add_left i.isLt (2*r*k)).trans_le (by dsimp [dimOf]; have := Nat.two_pow_pos k; omega)⟩

def colAt (k r B hRow hCol : Nat) : Word (dimOf k r B hRow hCol) hCol :=
  fun i x => x ⟨2*r*k+hRow+i.val, by
    exact (Nat.add_lt_add_left i.isLt (2*r*k+hRow)).trans_le (by dsimp [dimOf]; have := Nat.two_pow_pos k; omega)⟩

def sampleAt (k r B hRow hCol : Nat) (j : Fin B) : Word (dimOf k r B hRow hCol) k :=
  fun i x => x ⟨2*r*k+hRow+hCol+(j.val*k+i.val), by
    have hm := Nat.mul_le_mul_right k (show j.val+1 ≤ B by omega)
    rw [Nat.succ_mul] at hm
    exact (Nat.add_lt_add_left (show j.val*k+i.val < B*k from by have := i.isLt; omega)
      (2*r*k+hRow+hCol)).trans_le (by dsimp [dimOf]; have := Nat.two_pow_pos k; omega)⟩

def keepAt (k r B hRow hCol : Nat) (y : Fin (2^k)) : Sig (dimOf k r B hRow hCol) :=
  fun x => x ⟨2*r*k+hRow+hCol+B*k+y.val, by have := y.isLt; dsimp [dimOf]; omega⟩

lemma initial_mask (k r B hRow hCol j : Nat) (i : Fin k) :
    maskAt k r B hRow hCol j i ∈ initial (dimOf k r B hRow hCol) := by
  unfold maskAt
  split
  · exact Or.inl ⟨_, rfl⟩
  · exact initial_const false

lemma initial_row (k r B hRow hCol : Nat) (i : Fin hRow) :
    rowAt k r B hRow hCol i ∈ initial (dimOf k r B hRow hCol) := Or.inl ⟨_, rfl⟩
lemma initial_col (k r B hRow hCol : Nat) (i : Fin hCol) :
    colAt k r B hRow hCol i ∈ initial (dimOf k r B hRow hCol) := Or.inl ⟨_, rfl⟩
lemma initial_sample (k r B hRow hCol : Nat) (j : Fin B) (i : Fin k) :
    sampleAt k r B hRow hCol j i ∈ initial (dimOf k r B hRow hCol) := Or.inl ⟨_, rfl⟩
lemma initial_keep (k r B hRow hCol : Nat) (y : Fin (2^k)) :
    keepAt k r B hRow hCol y ∈ initial (dimOf k r B hRow hCol) := Or.inl ⟨_, rfl⟩

def encBits (len val : Nat) : List Bool := (List.range len).map (fun i => val.testBit i)

def encode {k r B hRow hCol : Nat} (masks : Nat → Fin (2^k))
    (rt : Fin (2^hRow)) (ct : Fin (2^hCol)) (sample : Fin B → Fin (2^k))
    (keep : Fin (2^k) → Bool) : List Bool :=
  (List.range (2*r)).flatMap (fun j => encBits k (masks j).val) ++
    encBits hRow rt.val ++ encBits hCol ct.val ++
    (List.finRange B).flatMap (fun i => encBits k (sample i).val) ++ (List.finRange (2^k)).map keep

lemma encode_flat {B k : Nat} (sample : Fin B → Fin (2^k)) :
    (List.finRange B).flatMap (fun i => encBits k (sample i).val) =
      (List.range B).flatMap (fun i => encBits k (if h : i < B then (sample ⟨i,h⟩).val else 0)) := by
  have hmap : (List.finRange B).map Fin.val = List.range B := by
    apply List.ext_getElem
    · simp
    · simp
  rw [← hmap, List.flatMap_map]
  exact List.flatMap_congr (fun i _ => by simp [i.isLt])

lemma encode_len {k r B hRow hCol : Nat} (masks : Nat → Fin (2^k))
    (rt : Fin (2^hRow)) (ct : Fin (2^hCol)) (sample : Fin B → Fin (2^k))
    (keep : Fin (2^k) → Bool) : (encode (r:=r) masks rt ct sample keep).length = dimOf k r B hRow hCol := by
  unfold encode
  rw [encode_flat]
  simp only [encBits, List.length_append, flatMap_bits_length, List.length_map, List.length_range,
    List.length_finRange, dimOf]

def readInput {k r B hRow hCol : Nat} (masks : Nat → Fin (2^k))
    (rt : Fin (2^hRow)) (ct : Fin (2^hCol)) (sample : Fin B → Fin (2^k))
    (keep : Fin (2^k) → Bool) : Fin (dimOf k r B hRow hCol) → Bool :=
  fun i => (encode (r:=r) masks rt ct sample keep).getD i.val false

lemma readInput_ofFn {k r B hRow hCol : Nat} (masks : Nat → Fin (2^k))
    (rt : Fin (2^hRow)) (ct : Fin (2^hCol)) (sample : Fin B → Fin (2^k))
    (keep : Fin (2^k) → Bool) :
    List.ofFn (readInput (r:=r) masks rt ct sample keep) = encode (r:=r) masks rt ct sample keep := by
  apply List.ext_getElem
  · simp [encode_len]
  · intro i hi hi'
    rw [List.getElem_ofFn]
    exact List.getD_eq_getElem _ _ hi'

lemma readInput_bits {k r B hRow hCol : Nat} (masks : Nat → Fin (2^k))
    (rt : Fin (2^hRow)) (ct : Fin (2^hCol)) (sample : Fin B → Fin (2^k))
    (keep : Fin (2^k) → Bool) :
    let x := readInput (r:=r) masks rt ct sample keep
    (∀ j < 2*r, ∀ i, maskAt k r B hRow hCol j i x = (masks j).val.testBit i.val) ∧
    (∀ i, rowAt k r B hRow hCol i x = rt.val.testBit i.val) ∧
    (∀ i, colAt k r B hRow hCol i x = ct.val.testBit i.val) ∧
    (∀ j i, sampleAt k r B hRow hCol j i x = (sample j).val.testBit i.val) ∧
    (∀ y, keepAt k r B hRow hCol y x = keep y) := by
  dsimp only
  have ha : ∀ j < 2*r, ∀ i : Fin k, j*k+i.val < 2*r*k := by
    intro j hj i
    have ht := Nat.mul_le_mul_right k (show j+1 ≤ 2*r by omega)
    rw [Nat.succ_mul] at ht
    have := i.isLt
    omega
  have hb : ∀ j : Fin B, ∀ i : Fin k, j.val*k+i.val < B*k := by
    intro j i
    have ht := Nat.mul_le_mul_right k (show j.val+1 ≤ B by omega)
    rw [Nat.succ_mul] at ht
    have := i.isLt
    omega
  have left {l t : List Bool} {i : Nat} (h : i < l.length) := List.getD_append l t false i h
  have right {l t : List Bool} {i : Nat} (h : l.length ≤ i) := List.getD_append_right l t false i h
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro j hj i
    simp only [maskAt, hj, ↓reduceDIte, readInput, encode]
    rw [encode_flat]
    unfold encBits
    repeat rw [left (by simp only [List.length_append, List.length_range, List.length_map,
      flatMap_bits_length]; have := ha j hj i; omega)]
    exact flatMap_bits_getD (2*r) k (fun t => (masks t).val) j i.val hj i.isLt
  · intro i
    have := i.isLt
    simp only [rowAt, readInput, encode]
    rw [encode_flat]
    unfold encBits
    rw [left (by simp only [List.length_append, List.length_range, List.length_map, flatMap_bits_length]; omega),
      left (by simp only [List.length_append, List.length_range, List.length_map, flatMap_bits_length]; omega),
      left (by simp only [List.length_append, List.length_range, List.length_map, flatMap_bits_length]; omega),
      right (by simp [flatMap_bits_length]), flatMap_bits_length, Nat.add_sub_cancel_left]
    simp [List.getD_eq_getElem?_getD, i.isLt]
  · intro i
    have := i.isLt
    simp only [colAt, readInput, encode]
    rw [encode_flat]
    unfold encBits
    rw [left (by simp only [List.length_append, List.length_range, List.length_map, flatMap_bits_length]; omega),
      left (by simp only [List.length_append, List.length_range, List.length_map, flatMap_bits_length]; omega),
      right (by simp only [List.length_append, List.length_range, List.length_map, flatMap_bits_length]; omega),
      List.length_append, flatMap_bits_length, List.length_map, List.length_range, Nat.add_sub_cancel_left]
    simp [List.getD_eq_getElem?_getD, i.isLt]
  · intro j i
    have := hb j i
    simp only [sampleAt, readInput, encode]
    rw [encode_flat]
    unfold encBits
    rw [left (by simp only [List.length_append, List.length_range, List.length_map, flatMap_bits_length]; omega),
      right (by simp only [List.length_append, List.length_range, List.length_map, flatMap_bits_length]; omega)]
    simp only [List.length_append, List.length_range, List.length_map, flatMap_bits_length, Nat.add_sub_cancel_left]
    rw [flatMap_bits_getD B k _ j.val i.val j.isLt i.isLt]
    simp [j.isLt]
  · intro y
    simp only [keepAt, readInput, encode]
    rw [encode_flat]
    unfold encBits
    rw [right (by simp only [List.length_append, List.length_range, List.length_map, flatMap_bits_length]; omega)]
    simp only [List.length_append, List.length_range, List.length_map, flatMap_bits_length, Nat.add_sub_cancel_left]
    exact finRange_map_getD _ keep false _ y.isLt

end Input

-- Fragment Cipher.

section CipherCore

-- Ported from lean/PEqualNP/Outside/L_meta_32053.lean at
-- a5155e523e2d6953c6a74fecf481bd6d63aa9bc8. The pinned inverse
-- already uses the posted rotations and row/column key schedules.

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

private theorem cipher_uniform_cost (k r c i : Nat)
    (hc : c ≤ 100 * (k+1)^2) (hi : i ≤ 100 * (k+1)^2) :
    r * c + i ≤ 100 * (k+1)^2 * (r+1) := by
  calc
    r * c + i ≤ r * (100 * (k+1)^2) + 100 * (k+1)^2 :=
      Nat.add_le_add (Nat.mul_le_mul_left r hc) hi
    _ = _ := by ring

theorem invRunG_uniform {n k : Nat} (hk : 0 < k) (r : Nat) {A : Set (Sig n)}
    (masks : Nat → Fin k → Sig n) (col : Bool) (key : Fin k → Bool) (out : Fin k → Sig n)
    (hout : ∀ i, out i ∈ A)
    (hm : ∀ j < r, ∀ i, masks (if col then r + j else j) i ∈ A)
    (htrue : (fun _ => true) ∈ A) (hfalse : (fun _ => false) ∈ A) :
    Build A {f | ∃ i : Fin k, f = fun v =>
      invRunB hk r (fun t a => masks t a v) col key (fun a => out a v) i}
      (100 * (k+1)^2 * (r+1)) :=
  relax (invRunG hk r masks col key out hout hm htrue hfalse) le_rfl le_rfl
    (cipher_uniform_cost k r _ _ (by nlinarith [Nat.zero_le (k * k)])
      (by nlinarith [Nat.zero_le (k * k)]))

private theorem forwardMixG {n k : Nat} (hk : 0 < k) (gap : Nat)
    {A : Set (Sig n)} (x : Fin k → Sig n) (hx : ∀ i, x i ∈ A) :
    Build A (Set.range (fun i v => mixB hk gap (fun a => x a v) i)) (k * 8) := by
  apply finG _ 8
  intro i
  let p := x ⟨(i.val + k - gap % k) % k, Nat.mod_lt _ hk⟩
  let q := x ⟨(i.val + k - (k - gap % k) % k) % k, Nat.mod_lt _ hk⟩
  have hp : p ∈ A := hx _
  have hq : q ∈ A := hx _
  have H := xorG (hx i) hp
  have J := xorG (A := A ∪ {xr (x i) p}) (f := xr (x i) p)
    (Or.inr (by rfl)) (Or.inl hq)
  exact relax (seq H J) le_rfl (fun _ h => Or.inr h) le_rfl

private theorem forwardChiG {n k : Nat} (hk : 0 < k)
    {A : Set (Sig n)} (x : Fin k → Sig n) (hx : ∀ i, x i ∈ A) :
    Build A (Set.range (fun i v => stepB hk (fun a => x a v) i)) (k * 6) := by
  apply finG _ 6
  intro i
  let p := x ⟨(i.val + 1) % k, Nat.mod_lt _ hk⟩
  let q := x ⟨(i.val + 2) % k, Nat.mod_lt _ hk⟩
  have hp : p ∈ A := hx _
  have hq : q ∈ A := hx _
  have H := notG hp
  have J := andG (A := A ∪ {nt p}) (f := nt p) (Or.inr (by rfl)) (Or.inl hq)
  have K := xorG (A := A ∪ ({nt p} ∪ {an (nt p) q})) (g := an (nt p) q)
    (Or.inl (hx i)) (Or.inr (Or.inr (by rfl)))
  exact relax (seq (seq H J) K) le_rfl (fun _ h => Or.inr h) le_rfl

private theorem forwardRoundG {n k : Nat} (hk : 0 < k) (r : Nat)
    {A : Set (Sig n)} (masks : Nat → Fin k → Sig n) (col : Bool) (j : Nat)
    (key : Fin k → Bool) (x : Fin k → Sig n)
    (hx : ∀ i, x i ∈ A) (hm : ∀ i, masks (if col then r + j else j) i ∈ A)
    (htrue : (fun _ => true) ∈ A) (hfalse : (fun _ => false) ∈ A) :
    Build A {f | ∃ i : Fin k, f = fun v =>
      xor (xor (stepB hk (mixB hk (if col then 2 else 1) (fun a => x a v)) i)
        (rotB hk (if col then 3 * (j + 1) + 1 else 2 * j) key i))
        (masks (if col then r + j else j) i v)} (22 * k) := by
  let gap := if col then 2 else 1
  let shift := if col then 3 * (j + 1) + 1 else 2 * j
  let X : Fin k → Sig n := fun i v => mixB hk gap (fun a => x a v) i
  let Y : Fin k → Sig n := fun i v => stepB hk (fun a => X a v) i
  let Z : Fin k → Sig n := fun i v => xor (Y i v) (rotB hk shift key i)
  let W : Fin k → Sig n := fun i v => xor (Z i v) (masks (if col then r + j else j) i v)
  have HX : Build A (Set.range X) (k * 8) := forwardMixG hk gap x hx
  have HY : Build (A ∪ Set.range X) (Set.range Y) (k * 6) :=
    forwardChiG hk X (fun i => Or.inr ⟨i, rfl⟩)
  let A₂ := A ∪ (Set.range X ∪ Set.range Y)
  have HZ : Build A₂ (Set.range Z) (k * 4) := finG Z 4 fun i => by
    have hc : (fun _ : Fin n → Bool => rotB hk shift key i) ∈ A₂ := by
      cases rotB hk shift key i
      · exact Or.inl hfalse
      · exact Or.inl htrue
    exact xorG (Or.inr (Or.inr ⟨i, rfl⟩)) hc
  let A₃ := A ∪ ((Set.range X ∪ Set.range Y) ∪ Set.range Z)
  have HW : Build A₃ (Set.range W) (k * 4) := finG W 4 fun i =>
    xorG (Or.inr (Or.inr ⟨i, rfl⟩)) (Or.inl (hm i))
  refine relax (seq (seq (seq HX HY) HZ) HW) le_rfl ?_ (by omega)
  rintro f ⟨i, rfl⟩
  exact Or.inr ⟨i, rfl⟩

theorem runG {n k : Nat} (hk : 0 < k) (r : Nat) {A : Set (Sig n)}
    (masks : Nat → Fin k → Sig n) (col : Bool) (key : Fin k → Bool) (name : Fin k → Sig n)
    (hname : ∀ i, name i ∈ A)
    (hm : ∀ j < r, ∀ i, masks (if col then r + j else j) i ∈ A)
    (htrue : (fun _ => true) ∈ A) (hfalse : (fun _ => false) ∈ A) :
    Build A {f | ∃ i : Fin k, f = fun v =>
      runB hk r (fun t a => masks t a v) col key (fun a => name a v) i}
      (100 * (k+1)^2 * (r+1)) := by
  let init : Fin k → Sig n := fun i v => xor (rotB hk (if col then 3 else 1) key i) (name i v)
  have Hinit : Build A (Set.range init) (k * 4) := finG init 4 fun i => by
    have hc : (fun _ : Fin n → Bool => rotB hk (if col then 3 else 1) key i) ∈ A := by
      cases rotB hk (if col then 3 else 1) key i
      · exact hfalse
      · exact htrue
    exact xorG hc (hname i)
  let A₁ := A ∪ Set.range init
  let step (v : Fin n → Bool) (x : Fin k → Bool) (j : Nat) (i : Fin k) : Bool :=
    xor (xor (stepB hk (mixB hk (if col then 2 else 1) x) i)
      (rotB hk (if col then 3 * (j + 1) + 1 else 2 * j) key i))
      (masks (if col then r + j else j) i v)
  let word (l : List Nat) (i : Fin k) : Sig n :=
    fun v => l.foldl (step v) (fun a => init a v) i
  have hfold : ∀ l : List Nat, (∀ j ∈ l, j < r) →
      Build A₁ {f | ∃ i : Fin k, f = word l i} (l.length * (22 * k)) := by
    intro l
    induction l using List.reverseRecOn with
    | nil =>
      intro _
      refine relax (idle ?_) le_rfl le_rfl (by simp)
      rintro f ⟨i, rfl⟩
      exact Or.inr ⟨i, rfl⟩
    | append_singleton l a ih =>
      intro hl
      have Hprev := ih (fun j hj => hl j (List.mem_append_left _ hj))
      have Hstep := forwardRoundG hk r masks col a key (word l)
        (A := A₁ ∪ {f | ∃ i : Fin k, f = word l i})
        (fun i => Or.inr ⟨i, rfl⟩)
        (fun i => Or.inl (Or.inl (hm a (hl a (by simp)) i)))
        (Or.inl (Or.inl htrue)) (Or.inl (Or.inl hfalse))
      refine relax (seq Hprev Hstep) le_rfl ?_ ?_
      · rintro f ⟨i, rfl⟩
        right
        refine ⟨i, ?_⟩
        funext v
        simp only [word, List.foldl_append, List.foldl_cons, List.foldl_nil, step]
      · simp [Nat.add_mul]
  have H := hfold (List.range r) (fun j hj => List.mem_range.mp hj)
  rw [List.length_range] at H
  refine relax (seq Hinit H) le_rfl ?_ ?_
  · rintro f ⟨i, rfl⟩
    exact Or.inr ⟨i, rfl⟩
  · rw [Nat.add_comm]
    exact cipher_uniform_cost k r _ _ (by nlinarith [Nat.zero_le (k * k)])
      (by nlinarith [Nat.zero_le (k * k)])

end CipherRun

-- Fragment Table.

section Tables

variable {n k : Nat}

def fwdWord (hk : 0 < k) (r : Nat) (m : Nat → Word n k) (c : Bool)
    (key : Fin (2^k)) (name : Word n k) : Word n k :=
  fun i x => runB hk r (fun t a => m t a x) c (ofNat k key.val) (fun a => name a x) i

def prefixWord {h : Nat} (hh : h ≤ k) (z : Word n k) : Word n h :=
  fun i => z ⟨k-h+i.val, by have := i.isLt; omega⟩

abbrev wordNat {w : Nat} (z : Word n w) (x : Fin n → Bool) : Nat := toNat (fun i => z i x)

def tableBit {h : Nat} (hh : h ≤ k) (z : Word n k) (t : Word n h) : Sig n :=
  fun x => decide (wordNat (prefixWord hh z) x = wordNat t x)

def constWord (y : Fin (2^k)) : Word n k := fun i _ => ofNat k y.val i

def slotWord {h : Nat} (t : Word n h) (lo : Fin (2^(k-h))) : Word n k :=
  fun i x => if hi : i.val < k-h then lo.val.testBit i.val else t ⟨i.val-(k-h), by
    have := i.isLt
    omega⟩ x

def backWord {h : Nat} (hk : 0 < k) (r : Nat) (m : Nat → Word n k) (c : Bool)
    (key : Fin (2^k)) (t : Word n h) (lo : Fin (2^(k-h))) : Word n k :=
  fun i x => invRunB hk r (fun a b => m a b x) c (ofNat k key.val) (fun a => slotWord t lo a x) i

lemma wordNat_bit {w : Nat} (z : Word n w) (x : Fin n → Bool) (i : Fin w) :
    (wordNat z x).testBit i.val = z i x := testBit_toNat_fin _ _

lemma slotWord_comb {h : Nat} (t : Word n h) (lo : Fin (2^(k-h))) (x : Fin n → Bool) :
    (fun i => slotWord t lo i x) = combWord h ⟨wordNat t x, toNat_lt _⟩ lo.val := by
  funext i
  unfold slotWord combWord
  by_cases hi : i.val < k-h
  · simp [hi]
  · simp only [hi, ↓reduceDIte, ↓reduceIte]
    exact (wordNat_bit t x ⟨i.val-(k-h),by have := i.isLt; omega⟩).symm

lemma prefixWord_shift {h : Nat} (hh : h ≤ k) (z : Word n k) (x : Fin n → Bool) :
    wordNat (prefixWord hh z) x = wordNat z x >>> (k-h) := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_shiftRight]
  by_cases hi : i < h
  · rw [wordNat_bit (prefixWord hh z) x ⟨i,hi⟩, wordNat_bit z x ⟨k-h+i,by omega⟩]
    rfl
  · rw [Nat.testBit_lt_two_pow ((toNat_lt (fun j => prefixWord hh z j x)).trans_le
      (Nat.pow_le_pow_right Nat.zero_lt_two (by omega : h ≤ i))),
      Nat.testBit_lt_two_pow ((toNat_lt (fun j => z j x)).trans_le
      (Nat.pow_le_pow_right Nat.zero_lt_two (by omega : k ≤ k-h+i)))]

lemma tableBit_back {h : Nat} (hh : h ≤ k) (hk : 0 < k) (hk6 : k%6=1 ∨ k%6=5)
    (r : Nat) (m : Nat → Word n k) (c : Bool) (key : Fin (2^k)) (z : Word n k) (t : Word n h)
    (x : Fin n → Bool) : tableBit hh (fwdWord hk r m c key z) t x = true ↔
      ∃ lo : Fin (2^(k-h)), wordNat z x = wordNat (backWord hk r m c key t lo) x := by
  simp only [tableBit, decide_eq_true_eq, prefixWord_shift]
  constructor
  · intro he
    let q := wordNat (fwdWord hk r m c key z) x
    let lo : Fin (2^(k-h)) := ⟨q % 2^(k-h), Nat.mod_lt _ (Nat.two_pow_pos _)⟩
    refine ⟨lo, ?_⟩
    have hf := combWord_of_shift hh ⟨wordNat t x,toNat_lt _⟩
      (fun i => fwdWord hk r m c key z i x) he
    change (fun i => fwdWord hk r m c key z i x) = combWord h ⟨wordNat t x,toNat_lt _⟩ lo.val at hf
    change toNat (fun i => z i x) = toNat (invRunB hk r (fun a b => m a b x) c (ofNat k key.val)
      (fun a => slotWord t lo a x))
    rw [slotWord_comb, ← hf]
    change toNat (fun i => z i x) = toNat (invRunB hk r (fun a b => m a b x) c (ofNat k key.val)
      (runB hk r (fun a b => m a b x) c (ofNat k key.val) (fun i => z i x)))
    rw [invRunB_runB hk hk6]
  · rintro ⟨lo,he⟩
    have he' := toNat_inj he
    unfold wordNat
    change toNat (runB hk r (fun a b => m a b x) c (ofNat k key.val) (fun i => z i x)) >>> (k-h) = _
    rw [he']
    change toNat (runB hk r (fun a b => m a b x) c (ofNat k key.val)
      (invRunB hk r (fun a b => m a b x) c (ofNat k key.val) (fun a => slotWord t lo a x))) >>> (k-h) = _
    rw [runB_invRunB hk hk6, slotWord_comb]
    exact combWord_shift hh ⟨wordNat t x,toNat_lt _⟩ lo.val

lemma build_tableBit {h : Nat} (hh : h ≤ k) {A : Set (Sig n)} (z : Word n k) (t : Word n h)
    (hz : ∀ i, z i ∈ A) (ht : ∀ i, t i ∈ A) (hc : ∀ b : Bool, (fun _ => b) ∈ A) :
    Build A {tableBit hh z t} (11*k+5) := by
  let f := fun i : Nat => if hi : i < h then prefixWord hh z ⟨i,hi⟩ else fun _ => false
  let g := fun i : Nat => if hi : i < h then t ⟨i,hi⟩ else fun _ => false
  have hf : ∀ i < h, f i ∈ A := fun i hi => by simpa [f, hi, prefixWord] using hz ⟨k-h+i,by omega⟩
  have hg : ∀ i < h, g i ∈ A := fun i hi => by simpa [g, hi] using ht ⟨i,hi⟩
  have hF (x : Fin n → Bool) : bitsVal (fun i => f i x) h = wordNat (prefixWord hh z) x := by
    change bitsVal (fun i => f i x) h = toNat (fun j => prefixWord hh z j x)
    rw [← bitsVal_of_testBit _ _ (toNat_lt (fun j => prefixWord hh z j x))]
    apply bitsVal_congr
    intro i hi
    simpa [f, hi] using (wordNat_bit (prefixWord hh z) x ⟨i,hi⟩).symm
  have hG (x : Fin n → Bool) : bitsVal (fun i => g i x) h = wordNat t x := by
    change bitsVal (fun i => g i x) h = toNat (fun j => t j x)
    rw [← bitsVal_of_testBit _ _ (toNat_lt (fun j => t j x))]
    apply bitsVal_congr
    intro i hi
    simpa [g, hi] using (wordNat_bit t x ⟨i,hi⟩).symm
  refine relax (eqWordG f g h hf hg (hc false)) le_rfl ?_ (by omega)
  intro v hv
  have he : v = tableBit hh z t := Set.mem_singleton_iff.mp hv
  rw [he]
  apply Set.mem_singleton_iff.mpr
  funext x
  simp [tableBit, hF, hG]

abbrev unitCost (k r : Nat) := 120*(k+1)^2*(r+1)

lemma build_test {h : Nat} (hh : h ≤ k) (hk : 0 < k) (r : Nat) {A : Set (Sig n)}
    (m : Nat → Word n k) (c : Bool) (a : Fin (2^k)) (z : Word n k) (t : Word n h)
    (hm : ∀ j i, m j i ∈ A) (hz : ∀ i, z i ∈ A) (ht : ∀ i, t i ∈ A)
    (hc : ∀ b : Bool, (fun _ => b) ∈ A) :
    Build A {tableBit hh (fwdWord hk r m c a z) t} (unitCost k r) := by
  have hg := runG hk r m c (ofNat k a.val) z hz (fun _ _ _ => hm _ _) (hc true) (hc false)
  have hg' : Build A (Set.range (fwdWord hk r m c a z)) (100*(k+1)^2*(r+1)) := by
    exact relax hg le_rfl (by rintro f ⟨i,rfl⟩; exact ⟨i,rfl⟩) le_rfl
  have h := build_tableBit hh (fwdWord hk r m c a z) t
    (A := A ∪ Set.range (fwdWord hk r m c a z)) (fun i => Or.inr ⟨i,rfl⟩)
    (fun i => Or.inl (ht i)) (fun b => Or.inl (hc b))
  refine relax (seq hg' h) le_rfl Set.subset_union_right ?_
  have h1 : 11*k+5 ≤ 20*(k+1)^2 := by nlinarith [Nat.zero_le (k*k)]
  calc
    _ ≤ 100*(k+1)^2*(r+1) + 20*(k+1)^2*(r+1) := Nat.add_le_add_left
      (h1.trans (Nat.le_mul_of_pos_right _ (by omega))) _
    _ = _ := by dsimp [unitCost]; ring

lemma build_back {h : Nat} (hk : 0 < k) (r : Nat) {A : Set (Sig n)}
    (m : Nat → Word n k) (c : Bool) (a : Fin (2^k)) (t : Word n h) (lo : Fin (2^(k-h)))
    (hm : ∀ j i, m j i ∈ A) (ht : ∀ i, t i ∈ A)
    (hc : ∀ b : Bool, (fun _ => b) ∈ A) : Build A (Set.range (backWord hk r m c a t lo)) (unitCost k r) := by
  have hlo : ∀ i, slotWord t lo i ∈ A := by
    intro i
    unfold slotWord
    by_cases hi : i.val < k-h
    · simpa [hi] using hc (lo.val.testBit i.val)
    · simpa [hi] using ht ⟨i.val-(k-h),by have := i.isLt; omega⟩
  refine relax (invRunG_uniform hk r m c (ofNat k a.val) (slotWord t lo) hlo
    (fun _ _ _ => hm _ _) (hc true) (hc false)) le_rfl ?_ ?_
  · rintro f ⟨i,rfl⟩; exact ⟨i,rfl⟩
  · dsimp [unitCost]; gcongr <;> decide

end Tables

-- Fragment Join.
section GroupedOrJoin

-- The sorting and reverse-replay construction uses the pinned L_meta_32053
-- BitonicSec/NetCirc machinery (a5155e523e2d6953c6a74fecf481bd6d63aa9bc8).
-- Unlike its single-table-value scan2, this scan resets at a key boundary and ORs payloads.
private def joinInit {n : Nat} (tag : Nat → Bool)
    (key : (Fin n → Bool) → Nat → Nat) (payload : (Fin n → Bool) → Nat → Nat → Bool)
    (x : Fin n → Bool) (i : Nat) : Rec :=
  (fun b => if b = 0 then tag i else (key x i).testBit (b - 1),
   fun b => if tag i then false else payload x i b)

private def joinGroup (kw : Nat) (r : Rec) : Nat :=
  bitsVal (fun b => r.1 (b + 1)) kw

private theorem joinRecKey (kw : Nat) (r : Rec) :
    recKey (kw + 1) r = 2 * joinGroup kw r + (if r.1 0 then 1 else 0) := by
  unfold recKey
  rw [Nat.add_comm kw 1, bitsVal_add]
  simp only [bitsVal, Nat.pow_zero, Nat.pow_one, Nat.zero_add, joinGroup, Nat.add_comm 1]
  exact Nat.add_comm _ _

private theorem joinGroup_mono (kw : Nat) {r s : Rec}
    (h : recKey (kw + 1) r ≤ recKey (kw + 1) s) : joinGroup kw r ≤ joinGroup kw s := by
  rw [joinRecKey, joinRecKey] at h
  have hs : (if s.1 0 then 1 else 0 : Nat) ≤ 1 := by split <;> omega
  omega

private def joinSame (kw : Nat) (st : Nat → Rec) (i : Nat) : Bool :=
  decide (joinGroup kw (st (i - 1)) = joinGroup kw (st i))

private def joinPrefix (kw : Nat) (st : Nat → Rec) : Nat → Nat → Bool
  | 0, _ => false
  | m + 1, b => (st m).2 b || (joinSame kw st m && joinPrefix kw st m b)

private theorem joinPrefix_spec (kw P : Nat) (st : Nat → Rec)
    (hmono : ∀ i j, i ≤ j → j < P → joinGroup kw (st i) ≤ joinGroup kw (st j)) :
    ∀ m < P, ∀ b, joinPrefix kw st (m + 1) b = true ↔
      ∃ i ≤ m, joinGroup kw (st i) = joinGroup kw (st m) ∧ (st i).2 b = true := by
  intro m
  induction m with
  | zero =>
    intro _ b
    change ((st 0).2 b || (joinSame kw st 0 && false)) = true ↔ _
    simp only [Bool.and_false, Bool.or_false]
    constructor
    · intro h; exact ⟨0, le_rfl, rfl, h⟩
    · rintro ⟨i, hi, _, hv⟩
      have he : i = 0 := by omega
      subst i
      exact hv
  | succ m ih =>
    intro hm b
    change ((st (m + 1)).2 b ||
      (joinSame kw st (m + 1) && joinPrefix kw st (m + 1) b)) = true ↔ _
    simp only [Bool.or_eq_true, Bool.and_eq_true, joinSame, Nat.add_sub_cancel, decide_eq_true_eq]
    rw [ih (by omega) b]
    constructor
    · rintro (hv | ⟨he, i, hi, hk, hv⟩)
      · exact ⟨m + 1, le_rfl, rfl, hv⟩
      · exact ⟨i, by omega, hk.trans he, hv⟩
    · rintro ⟨i, hi, hk, hv⟩
      by_cases he : i = m + 1
      · subst i; exact Or.inl hv
      · have him : i ≤ m := by omega
        have hle := hmono i m him (by omega)
        rw [hk] at hle
        have h_eq := le_antisymm (hmono m (m + 1) (by omega) hm) hle
        exact Or.inr ⟨h_eq, i, him, hk.trans h_eq.symm, hv⟩

private theorem joinPrefixG {n : Nat} {A : Set (Sig n)} (kw w P : Nat)
    (st : (Fin n → Bool) → Nat → Rec)
    (hK : ∀ i < P, ∀ j < kw, (fun x => (st x i).1 (j + 1)) ∈ A)
    (hV : ∀ i < P, ∀ b < w, (fun x => (st x i).2 b) ∈ A)
    (hfalse : (fun _ => false) ∈ A) :
    ∀ M ≤ P, Build A
      {f | ∃ m ≤ M, ∃ b < w, f = fun x => joinPrefix kw (st x) m b}
      (M * (5 * kw + 1 + w * 2)) := by
  intro M
  induction M with
  | zero =>
    intro _
    refine relax (idle ?_) le_rfl le_rfl (by simp)
    rintro f ⟨i, hi, b, hb, rfl⟩
    have he : i = 0 := by omega
    subst i
    exact hfalse
  | succ M ih =>
    intro hM
    let B : Set (Sig n) := {f | ∃ m ≤ M, ∃ b < w, f = fun x => joinPrefix kw (st x) m b}
    have Hprev : Build A B (M * (5 * kw + 1 + w * 2)) := ih (by omega)
    let cmp : Sig n := fun x => joinSame kw (st x) M
    have HC : Build (A ∪ B) {cmp} (5 * kw + 1) :=
      eqWordG (fun j x => (st x (M - 1)).1 (j + 1)) (fun j x => (st x M).1 (j + 1)) kw
        (fun j hj => Or.inl (hK (M - 1) (by omega) j hj))
        (fun j hj => Or.inl (hK M (by omega) j hj)) (Or.inl hfalse)
    let out : Nat → Sig n := fun b x => joinPrefix kw (st x) (M + 1) b
    have Hnext : Build ((A ∪ B) ∪ {cmp}) {f | ∃ b < w, f = out b} (w * 2) :=
      rangeG (m := w) out 2 fun b hb => by
        let v : Sig n := fun x => (st x M).2 b
        let prev : Sig n := fun x => joinPrefix kw (st x) M b
        let T := (A ∪ B) ∪ {cmp}
        have H1 : Build T {an cmp prev} 1 :=
          andG (Or.inr rfl) (Or.inl (Or.inr ⟨M, le_rfl, b, hb, rfl⟩))
        have H2 : Build (T ∪ {an cmp prev}) {out b} 1 := by
          have he : out b = orS v (an cmp prev) := rfl
          rw [he]
          exact orG (Or.inl (Or.inl (Or.inl (hV M (by omega) b hb)))) (Or.inr rfl)
        exact relax (seq H1 H2) le_rfl (Set.singleton_subset_iff.mpr (Or.inr rfl)) le_rfl
    refine relax (seq Hprev (seq HC Hnext)) le_rfl ?_ ?_
    · rintro f ⟨m, hm, b, hb, rfl⟩
      by_cases he : m = M + 1
      · subst m; exact Or.inr (Or.inr ⟨b, hb, rfl⟩)
      · exact Or.inl ⟨m, by omega, b, hb, rfl⟩
    · simp only [Nat.add_mul, Nat.one_mul, Nat.add_assoc, le_refl]

open scoped Classical

/-- For each query-tagged record, OR the payload bits of all matching data-tagged records.
A query-tagged dummy may be placed at any padding position. -/
theorem groupedOrJoinG {n : Nat} {A : Set (Sig n)} (p kw w : Nat) (tag : Nat → Bool)
    (key : (Fin n → Bool) → Nat → Nat) (payload : (Fin n → Bool) → Nat → Nat → Bool)
    (hkeyBound : ∀ x i, i < 2 ^ p → key x i < 2 ^ kw)
    (hkey : ∀ i < 2 ^ p, ∀ b < kw, (fun x => (key x i).testBit b) ∈ A)
    (hpayload : ∀ i < 2 ^ p, tag i = false → ∀ b < w, (fun x => payload x i b) ∈ A)
    (hfalse : (fun _ => false) ∈ A) (htrue : (fun _ => true) ∈ A) :
    Build A {f | ∃ q < 2 ^ p, tag q = true ∧ ∃ b < w,
      f = fun x => decide (∃ i < 2 ^ p, tag i = false ∧ key x i = key x q ∧ payload x i b = true)}
      (100 * (p + 1)^2 * 2^p * (kw + w + 1)) := by
  let P := 2 ^ p
  let net := bitonicSort 0 p true
  have hnet : ∀ c ∈ net, c.1 < P ∧ c.2.1 < P := by
    intro c hc
    have h := bitonicSort_mem 0 p true c hc
    have h2 : c.2.1 < P := by simpa [P] using h.2.2
    exact ⟨h.2.1.trans h2, h2⟩
  let init := joinInit tag key payload
  let sorted : (Fin n → Bool) → Nat → Rec := fun x => runNet (recKey (kw + 1)) net (init x)
  let ans : (Fin n → Bool) → Nat → Nat → Bool := fun x i b => joinPrefix kw (sorted x) (i + 1) b
  have hK : ∀ i < P, ∀ j < kw + 1, (fun x => (init x i).1 j) ∈ A := by
    intro i hi j hj
    dsimp only [init, joinInit]
    by_cases hz : j = 0
    · subst j
      cases ht : tag i
      · simpa [ht] using hfalse
      · simpa [ht] using htrue
    · simp only [hz, ↓reduceIte]
      exact hkey i hi (j - 1) (by omega)
  have hV : ∀ i < P, ∀ b < w, (fun x => (init x i).2 b) ∈ A := by
    intro i hi b hb
    dsimp only [init, joinInit]
    cases ht : tag i
    · simpa [ht] using hpayload i hi ht b hb
    · simpa [ht] using hfalse
  let Bsort : Set (Sig n) :=
    ({f | ∃ i < P, ∃ j < kw + 1, f = fun x => (sorted x i).1 j} ∪
     {f | ∃ i < P, ∃ b < w, f = fun x => (sorted x i).2 b}) ∪
    {f | ∃ t < net.length,
      f = (fun x => ((netSwaps (recKey (kw + 1)) net (init x)).getD t (0, 0, false)).2.2) ∨
      f = (fun x => !(((netSwaps (recKey (kw + 1)) net (init x)).getD t (0, 0, false)).2.2))}
  have Hsort : Build A Bsort (net.length * (11 * (kw + 1) + 6 * w + 1)) :=
    netCircuit (kw + 1) w P net hnet init hK hV hfalse
  let Bscan : Set (Sig n) := {f | ∃ m ≤ P, ∃ b < w, f = fun x => joinPrefix kw (sorted x) m b}
  have Hscan : Build (A ∪ Bsort) Bscan (P * (5 * kw + 1 + w * 2)) :=
    joinPrefixG kw w P sorted
      (fun i hi j hj => Or.inr (Or.inl (Or.inl ⟨i, hi, j + 1, by omega, rfl⟩)))
      (fun i hi b hb => Or.inr (Or.inl (Or.inr ⟨i, hi, b, hb, rfl⟩))) (Or.inl hfalse) P le_rfl
  have Hreplay := replayRevCircuit (A := A ∪ (Bsort ∪ Bscan)) (kw + 1) w P net hnet init
    (fun t ht => ⟨Or.inr (Or.inl (Or.inr ⟨t, ht, Or.inl rfl⟩)),
                  Or.inr (Or.inl (Or.inr ⟨t, ht, Or.inr rfl⟩))⟩) ans
    (fun i hi b hb => Or.inr (Or.inr ⟨i + 1, by omega, b, hb, rfl⟩))
  have hanswer (x : Fin n → Bool) (q : Nat) (hq : q < P) (ht : tag q = true) (b : Nat) :
      replaySwaps (netSwaps (recKey (kw + 1)) net (init x)).reverse (ans x) q b =
        decide (∃ i < P, tag i = false ∧ key x i = key x q ∧ payload x i b = true) := by
    let fwd := replaySwaps (netSwaps (recKey (kw + 1)) net (init x)) id
    let inv := replaySwaps (netSwaps (recKey (kw + 1)) net (init x)).reverse id
    rcases bitonicPerm (recKey (kw + 1)) P net hnet (init x) with
      ⟨_, _, hFlt, hIlt, hF, hI, hrep⟩
    change (∀ i < P, fwd i < P) at hFlt
    change (∀ i < P, inv i < P) at hIlt
    change (∀ i, sorted x i = init x (fwd i)) at hF
    change (∀ i, sorted x (inv i) = init x i) at hI
    have hsorted : ∀ i j, i ≤ j → j < P →
        recKey (kw + 1) (sorted x i) ≤ recKey (kw + 1) (sorted x j) :=
      bitonicSort_sorted (recKey (kw + 1)) p (init x)
    have hgroup (i : Nat) (hi : i < P) : joinGroup kw (init x i) = key x i := by
      simpa [joinGroup, init, joinInit, Nat.add_sub_cancel] using
        bitsVal_of_testBit (key x i) kw (hkeyBound x i hi)
    have hrec (i : Nat) (hi : i < P) :
        recKey (kw + 1) (init x i) = 2 * key x i + (if tag i then 1 else 0) := by
      rw [joinRecKey, hgroup i hi]
      simp [init, joinInit]
    rw [congrFun (hrep (ans x) q) b]
    change joinPrefix kw (sorted x) (inv q + 1) b = _
    have hpos : inv q < P := hIlt q hq
    apply Bool.eq_iff_iff.mpr
    rw [decide_eq_true_eq, joinPrefix_spec kw P (sorted x)
      (fun i j hij hj => joinGroup_mono kw (hsorted i j hij hj)) (inv q) hpos b, hI q, hgroup q hq]
    constructor
    · rintro ⟨i, hi, hk, hv⟩
      have hf := hFlt i (hi.trans_lt hpos)
      rw [hF i, hgroup (fwd i) hf] at hk
      rw [hF i] at hv
      have htag : tag (fwd i) = false := by
        cases hh : tag (fwd i)
        · rfl
        · simp [init, joinInit, hh] at hv
      exact ⟨fwd i, hf, htag, hk, by simpa [init, joinInit, htag] using hv⟩
    · rintro ⟨i, hi, htag, hk, hv⟩
      have hip := hIlt i hi
      have hle : inv i ≤ inv q := by
        by_contra hn
        have ho := hsorted (inv q) (inv i) (by omega) hip
        rw [hI q, hI i, hrec q hq, hrec i hi] at ho
        simp only [ht, htag, ↓reduceIte, Bool.false_eq_true, Nat.add_zero] at ho
        omega
      refine ⟨inv i, hle, ?_, ?_⟩
      · rw [hI i, hgroup i hi]; exact hk
      · rw [hI i]; simpa [init, joinInit, htag] using hv
  refine relax (seq (seq Hsort Hscan) Hreplay) le_rfl ?_ ?_
  · rintro f ⟨q, hq, ht, b, hb, rfl⟩
    exact Or.inr ⟨q, hq, b, hb, funext (fun x => (hanswer x q hq ht b).symm)⟩
  · let U := (p + 1)^2 * P
    let W := kw + w + 1
    have hP : P ≤ U := by
      simpa only [U, Nat.one_mul] using
        Nat.mul_le_mul_right P (show 1 ≤ (p + 1)^2 from Nat.succ_le_of_lt (by positivity))
    have hL : net.length ≤ U := by
      have hlen : 4 * net.length = p * (p + 1) * P := bitonicSort_length 0 p true
      have hmul : p * (p + 1) * P ≤ U := by
        simpa only [U, pow_two] using Nat.mul_le_mul_right P
          (Nat.mul_le_mul_right (p + 1) (show p ≤ p + 1 by omega))
      omega
    calc
      net.length * (11 * (kw + 1) + 6 * w + 1) + P * (5 * kw + 1 + w * 2) + net.length * (6 * w)
          = net.length * (11 * (kw + 1) + 12 * w + 1) + P * (5 * kw + 1 + w * 2) := by ring
      _ ≤ U * (12 * W) + U * (5 * W) :=
        Nat.add_le_add (Nat.mul_le_mul hL (by dsimp [W]; omega))
          (Nat.mul_le_mul hP (by dsimp [W]; omega))
      _ = 17 * (U * W) := by ring
      _ ≤ 100 * (p + 1)^2 * 2^p * (kw + w + 1) := by
        simpa only [U, W, P, Nat.mul_assoc] using
          Nat.mul_le_mul_right (U * W) (show 17 ≤ 100 by decide)

end GroupedOrJoin

-- Fragment JoinAdapter.

section JoinAdapter

variable {n : Nat}

def joinFlag {α β : Type*} [Fintype α] (dk : (Fin n → Bool) → α → Nat)
    (qk : (Fin n → Bool) → β → Nat) (pay : α → Nat → Sig n) (q : β) (b : Nat) : Sig n :=
  fun x => decide (∃ a, dk x a = qk x q ∧ pay a b x = true)

set_option maxHeartbeats 600000 in
lemma typedJoinG {α β : Type*} [Fintype α] [Fintype β] {A : Set (Sig n)} (p kw w : Nat)
    (dk : (Fin n → Bool) → α → Nat) (qk : (Fin n → Bool) → β → Nat) (pay : α → Nat → Sig n)
    (hpad : Fintype.card α + Fintype.card β ≤ 2^p)
    (hdb : ∀ x a, dk x a < 2^kw) (hqb : ∀ x q, qk x q < 2^kw)
    (hd : ∀ a b, b < kw → (fun x => (dk x a).testBit b) ∈ A)
    (hq : ∀ q b, b < kw → (fun x => (qk x q).testBit b) ∈ A)
    (hp : ∀ a b, b < w → pay a b ∈ A)
    (hf : (fun _ => false) ∈ A) (ht : (fun _ => true) ∈ A) :
    Build A {f | ∃ q b, b < w ∧ f = joinFlag dk qk pay q b}
      (100*(p+1)^2*2^p*(kw+w+1)) := by
  classical
  let m := Fintype.card α
  let s := Fintype.card β
  let d := Fintype.equivFin α
  let q := Fintype.equivFin β
  let tag := fun i : Nat => decide (m ≤ i)
  let key := fun x i => if hi : i < m then dk x (d.symm ⟨i,hi⟩)
    else if hj : i-m < s then qk x (q.symm ⟨i-m,hj⟩) else 0
  let payload := fun x i b => if hi : i < m then pay (d.symm ⟨i,hi⟩) b x else false
  have hkBound : ∀ x i, i < 2^p → key x i < 2^kw := by
    intro x i hi
    unfold key
    split
    · exact hdb _ _
    · split
      · exact hqb _ _
      · exact Nat.two_pow_pos _
  have hk : ∀ i < 2^p, ∀ b < kw, (fun x => (key x i).testBit b) ∈ A := by
    intro i hi b hb
    by_cases hm : i < m
    · simpa only [key, hm, ↓reduceDIte] using hd (d.symm ⟨i,hm⟩) b hb
    · by_cases hs : i-m < s
      · simpa only [key, hm, hs, ↓reduceDIte] using hq (q.symm ⟨i-m,hs⟩) b hb
      · simpa [key, hm, hs] using hf
  have hv : ∀ i < 2^p, tag i = false → ∀ b < w, (fun x => payload x i b) ∈ A := by
    intro i _ ti b hb
    have hi : i < m := by simpa [tag] using ti
    simpa only [payload, hi, ↓reduceDIte] using hp (d.symm ⟨i,hi⟩) b hb
  refine relax (groupedOrJoinG p kw w tag key payload hkBound hk hv hf ht) le_rfl ?_ le_rfl
  rintro f ⟨j,b,hb,rfl⟩
  let t := m + (q j).val
  have hj : (q j).val < s := (q j).isLt
  have hpad' : m + s ≤ 2^p := hpad
  have htlt : t < 2^p := by dsimp [t]; omega
  have htm : ¬ t < m := by dsimp [t]; omega
  have hsub : t-m = (q j).val := by dsimp [t]; omega
  have hkeyt (x) : key x t = qk x j := by
    simp [key, htm, hsub, hj]
  refine ⟨t,htlt,by simp [tag, t],b,hb,?_⟩
  funext x
  simp only [joinFlag, hkeyt]
  congr 1
  apply propext
  constructor
  · rintro ⟨a,he,hv⟩
    have ha : (d a).val < m := (d a).isLt
    have ha' : (d a).val < 2^p := by omega
    exact ⟨(d a).val,ha',by simp [tag, Nat.not_le.mpr ha], by simpa [key, ha] using he,
      by simpa [payload, ha] using hv⟩
  · rintro ⟨i,hi,ti,he,hv⟩
    have hm : i < m := by simpa [tag] using ti
    exact ⟨d.symm ⟨i,hm⟩, by simpa [key, hm] using he, by simpa [payload, hm] using hv⟩

lemma padding_bound (a b : Nat) : 2^a+2^b ≤ 2^(max a b+1) := by
  rw [pow_succ]
  have h₁ := Nat.pow_le_pow_right (by decide : 0 < 2) (le_max_left a b)
  have h₂ := Nat.pow_le_pow_right (by decide : 0 < 2) (le_max_right a b)
  omega

lemma padding_cost (a b : Nat) : 2^(max a b+1) ≤ 2*(2^a+2^b) := by
  by_cases h : a ≤ b
  · rw [max_eq_right h, pow_succ, Nat.mul_comm (2^b)]
    exact Nat.mul_le_mul_left _ (Nat.le_add_left _ _)
  · rw [max_eq_left (by omega), pow_succ, Nat.mul_comm (2^a)]
    exact Nat.mul_le_mul_left _ (Nat.le_add_right _ _)

def pairKey (k a b : Nat) : Nat := bitsVal (fun i => if i < k then a.testBit i else b.testBit (i-k)) (k+k)

lemma pairKey_bound (k a b : Nat) : pairKey k a b < 2^(k+k) := bitsVal_lt _ _

lemma pairKey_bit (k a b i : Nat) (hi : i < k+k) :
    (pairKey k a b).testBit i = if i < k then a.testBit i else b.testBit (i-k) :=
  bitsVal_testBit _ _ _ hi

lemma pairKey_eq {k a b c d : Nat} (ha : a < 2^k) (hb : b < 2^k)
    (hc : c < 2^k) (hd : d < 2^k) : pairKey k a b = pairKey k c d ↔ a = c ∧ b = d := by
  constructor
  · intro h
    constructor
    · rw [← bitsVal_of_testBit a k ha, ← bitsVal_of_testBit c k hc]
      apply bitsVal_congr
      intro i hi
      simpa [pairKey_bit, show i < k+k by omega, hi] using congrArg (fun u : Nat => u.testBit i) h
    · rw [← bitsVal_of_testBit b k hb, ← bitsVal_of_testBit d k hd]
      apply bitsVal_congr
      intro i hi
      have h' := congrArg (fun u : Nat => u.testBit (k+i)) h
      simpa [pairKey_bit, show k+i < k+k by omega, show ¬ k+i < k by omega] using h'
  · rintro ⟨rfl,rfl⟩; rfl

end JoinAdapter

-- Fragment Routes.

section Routes

variable {n k s r hr hc : Nat}

abbrev Side (k : Nat) := Fin (2^k)
abbrev Samples (s : Nat) := Fin (2^s)

abbrev rowTests (hk : 0 < k) (hrk : hr ≤ k) (m : Nat → Word n k)
    (row : Word n hr) (sample : Samples s → Word n k) : Samples s → Side k → Sig n :=
  fun i a => tableBit hrk (fwdWord hk r m false a (sample i)) row

abbrev colTests (hk : 0 < k) (hck : hc ≤ k) (m : Nat → Word n k)
    (col : Word n hc) : Side k → Side k → Sig n :=
  fun a y => tableBit hck (fwdWord hk r m true a (constWord y)) col

def witSignal (f : Samples s → Side k → Sig n) (g : Side k → Side k → Sig n)
    (i : Samples s) (y : Side k) : Sig n :=
  fun x => decide (∃ a, f i a x = true ∧ g a y x = true)

def signalGrid {α β : Type*} (f : α → β → Sig n) : Set (Sig n) := {b | ∃ i j, b = f i j}

def wordGrid {α β : Type*} (f : α → β → Word n k) : Set (Sig n) :=
  {b | ∃ i j, b ∈ Set.range (f i j)}

lemma build_rowTests (hk : 0 < k) (hrk : hr ≤ k) {A : Set (Sig n)}
    (m : Nat → Word n k) (row : Word n hr) (sample : Samples s → Word n k)
    (hm : ∀ j i, m j i ∈ A) (ht : ∀ i, row i ∈ A) (hs : ∀ i j, sample i j ∈ A)
    (hc : ∀ b : Bool, (fun _ => b) ∈ A) :
    Build A (signalGrid (rowTests (r:=r) hk hrk m row sample)) (2^k*2^s*unitCost k r) := by
  simpa only [signalGrid, Set.mem_singleton_iff, Nat.mul_comm (2^k) (2^s)] using
    (gather₂ (fun i a => {rowTests (r:=r) hk hrk m row sample i a}) _
      (fun i a => build_test hrk hk r m false a (sample i) row hm (hs i) ht hc))

lemma build_colTests (hk : 0 < k) (hck : hc ≤ k) {A : Set (Sig n)}
    (m : Nat → Word n k) (col : Word n hc) (hm : ∀ j i, m j i ∈ A) (ht : ∀ i, col i ∈ A)
    (hconst : ∀ b : Bool, (fun _ => b) ∈ A) :
    Build A (signalGrid (colTests (r:=r) hk hck m col)) (2^k*2^k*unitCost k r) := by
  simpa only [signalGrid, Set.mem_singleton_iff] using
    (gather₂ (fun a y => {colTests (r:=r) hk hck m col a y}) _
      (fun a y => build_test hck hk r m true a (constWord y) col hm (fun i => hconst _) ht hconst))

lemma build_backTable {h : Nat} (hk : 0 < k) (c : Bool) {A : Set (Sig n)}
    (m : Nat → Word n k) (t : Word n h) (hm : ∀ j i, m j i ∈ A) (ht : ∀ i, t i ∈ A)
    (hconst : ∀ b : Bool, (fun _ => b) ∈ A) :
    Build A (wordGrid (backWord hk r m c · t ·)) (2^k*2^(k-h)*unitCost k r) :=
  gather₂ (fun a lo => Set.range (backWord hk r m c a t lo)) _
    (fun a lo => build_back hk r m c a t lo hm ht hconst)

abbrev payloadSize (k s r hc : Nat) :=
  (r+1)*2^k*(2^s+2^(k-hc)) + 2^k*2^(k-hc)*2^s

abbrev expansionSize (k s r hr hc : Nat) :=
  (r+1)*2^k*(2^(k-hr)+2^(k-hc)) + 2^k*2^(k-hr)*2^(k-hc) + 2^s*2^k

abbrev routeCost (k z : Nat) := 10000*(k+1)^3*z

lemma unitCost_le (k r : Nat) : unitCost k r ≤ (10000*(k+1)^3)*(r+1) := by
  unfold unitCost
  apply Nat.mul_le_mul_right
  calc
    120 * (k+1)^2 ≤ 10000*(k+1)^2 := Nat.mul_le_mul_right _ (by decide)
    _ ≤ 10000*(k+1)^3 := by gcongr; omega

set_option maxHeartbeats 900000 in
lemma payloadWitnessG (hk : 0 < k) (hk6 : k%6=1 ∨ k%6=5) (hrk : hr ≤ k) (hck : hc ≤ k)
    {A : Set (Sig n)} (m : Nat → Word n k) (row : Word n hr) (col : Word n hc)
    (sample : Samples s → Word n k) (hm : ∀ j i, m j i ∈ A) (hrow : ∀ i, row i ∈ A)
    (hcol : ∀ i, col i ∈ A) (hsamp : ∀ i j, sample i j ∈ A)
    (hconst : ∀ b : Bool, (fun _ => b) ∈ A) :
    Build A (signalGrid (witSignal (rowTests (r:=r) hk hrk m row sample) (colTests (r:=r) hk hck m col)))
      (routeCost k (payloadSize k s r hc)) := by
  let F := rowTests (r:=r) hk hrk m row sample
  let G := colTests (r:=r) hk hck m col
  let Y := fun a lo => backWord hk r m true a col lo
  let D := Side k × Fin (2^(k-hc))
  let p := k+(k-hc)+1
  let A₁ := A ∪ signalGrid F
  let A₂ := A₁ ∪ wordGrid Y
  let dq := fun (x : Fin n → Bool) (a : D) => wordNat (Y a.1 a.2) x
  let qq := fun (_ : Fin n → Bool) (y : Side k) => y.val
  let pay := fun (a : D) (b : Nat) => if h : b < 2^s then F ⟨b,h⟩ a.1 else fun _ => false
  have H₁ : Build A A₁ (2^k*2^s*unitCost k r) := build_keep (build_rowTests hk hrk m row sample hm hrow hsamp hconst)
  have H₂ : Build A₁ A₂ (2^k*2^(k-hc)*unitCost k r) := build_keep
    (build_backTable hk true m col (fun j i => Or.inl (hm j i)) (fun i => Or.inl (hcol i))
      (fun b => Or.inl (hconst b)))
  have hpow : 2^p = 2*(2^k*2^(k-hc)) := by dsimp [p]; rw [pow_succ, pow_add]; ac_rfl
  have hv : 1 ≤ 2^(k-hc) := Nat.two_pow_pos _
  have hB : 1 ≤ 2^s := Nat.two_pow_pos _
  have hpad : Fintype.card D + Fintype.card (Side k) ≤ 2^p := by
    simp only [D, Side, Fintype.card_prod, Fintype.card_fin, hpow]
    have hh := Nat.mul_le_mul_left (2^k) hv
    simp only [Nat.mul_one] at hh
    omega
  have H₃ := typedJoinG (A:=A₂) p k (2^s) dq qq pay hpad
    (fun x a => toNat_lt _) (fun x y => y.isLt)
    (fun a b hb => by
      rw [show (fun x => (dq x a).testBit b) = Y a.1 a.2 ⟨b,hb⟩ from
        funext fun x => wordNat_bit (Y a.1 a.2) x ⟨b,hb⟩]
      exact Or.inr ⟨a.1,a.2,⟨⟨b,hb⟩,rfl⟩⟩)
    (fun y b _ => Or.inl (Or.inl (hconst (y.val.testBit b))))
    (fun a b hb => by simpa only [pay, hb, ↓reduceDIte] using
      (show F ⟨b,hb⟩ a.1 ∈ A₂ from Or.inl (Or.inr ⟨_,_,rfl⟩)))
    (Or.inl (Or.inl (hconst false))) (Or.inl (Or.inl (hconst true)))
  have HG : Build A₂ (signalGrid (witSignal F G)) (100*(p+1)^2*2^p*(k+2^s+1)) := by
    refine relax H₃ le_rfl ?_ le_rfl
    rintro f ⟨i,y,rfl⟩
    refine ⟨y,i.val,i.isLt,?_⟩
    funext x
    unfold witSignal joinFlag
    congr 1
    apply propext
    have hg (a : Side k) : G a y x = true ↔ ∃ lo : Fin (2^(k-hc)), y.val = dq x (a,lo) := by
      simpa only [G, dq, colTests, constWord, wordNat, toNat_ofNat y.isLt] using
        tableBit_back hck hk hk6 r m true a (constWord y) col x
    constructor
    · rintro ⟨a,ha,hg'⟩
      obtain ⟨lo,hl⟩ := (hg a).mp hg'
      exact ⟨(a,lo),hl.symm,by simpa [pay, i.isLt] using ha⟩
    · rintro ⟨⟨a,lo⟩,he,hv'⟩
      exact ⟨a,by simpa [pay, i.isLt] using hv', (hg a).mpr ⟨lo,he.symm⟩⟩
  refine relax (build_next (build_next H₁ H₂) HG) le_rfl le_rfl ?_
  have hp : p+1 ≤ 2*(k+1) := by dsimp [p]; omega
  have hb : k+2^s+1 ≤ (k+2)*2^s := by
    calc
      k+2^s+1 = k+1+2^s := by omega
      _ ≤ (k+1)*2^s+2^s := Nat.add_le_add_right (Nat.le_mul_of_pos_right _ hB) _
      _ = _ := by ring
  have hb' := hb.trans (Nat.mul_le_mul_right (2^s) (show k+2 ≤ 2*(k+1) by omega))
  have hj : 100*(p+1)^2*2^p*(k+2^s+1) ≤ (10000*(k+1)^3)*(2^k*2^(k-hc)*2^s) := by
    calc
      _ ≤ 100*(2*(k+1))^2*(2*(2^k*2^(k-hc)))*(2*(k+1)*2^s) := by rw [hpow]; gcongr
      _ = 1600*(k+1)^3*(2^k*2^(k-hc)*2^s) := by ring
      _ ≤ _ := by gcongr; decide
  calc
    _ ≤ (2^k*2^s*((10000*(k+1)^3)*(r+1)) + 2^k*2^(k-hc)*((10000*(k+1)^3)*(r+1))) +
        (10000*(k+1)^3)*(2^k*2^(k-hc)*2^s) := by gcongr <;> exact unitCost_le _ _
    _ = _ := by dsimp [routeCost, payloadSize]; ring

set_option maxHeartbeats 900000 in
lemma expandedWitnessG (hk : 0 < k) (hk6 : k%6=1 ∨ k%6=5) (hsk : s ≤ k)
    (hrk : hr ≤ k) (hck : hc ≤ k) {A : Set (Sig n)} (m : Nat → Word n k)
    (row : Word n hr) (col : Word n hc) (sample : Samples s → Word n k)
    (hm : ∀ j i, m j i ∈ A) (hrow : ∀ i, row i ∈ A) (hcol : ∀ i, col i ∈ A)
    (hsamp : ∀ i j, sample i j ∈ A) (hconst : ∀ b : Bool, (fun _ => b) ∈ A) :
    Build A (signalGrid (witSignal (rowTests (r:=r) hk hrk m row sample) (colTests (r:=r) hk hck m col)))
      (routeCost k (expansionSize k s r hr hc)) := by
  let F := rowTests (r:=r) hk hrk m row sample
  let G := colTests (r:=r) hk hck m col
  let U := fun a lo => backWord hk r m false a row lo
  let V := fun a lo => backWord hk r m true a col lo
  let D := Side k × Fin (2^(k-hr)) × Fin (2^(k-hc))
  let Q := Samples s × Side k
  let a := k+(k-hr)+(k-hc)
  let b := s+k
  let p := max a b+1
  let A₁ := A ∪ wordGrid U
  let A₂ := A₁ ∪ wordGrid V
  let dq := fun (x : Fin n → Bool) (i : D) => pairKey k (wordNat (U i.1 i.2.1) x) (wordNat (V i.1 i.2.2) x)
  let qq := fun (x : Fin n → Bool) (i : Q) => pairKey k (wordNat (sample i.1) x) i.2.val
  let pay := fun (_ : D) (_ : Nat) (_ : Fin n → Bool) => true
  have H₁ : Build A A₁ (2^k*2^(k-hr)*unitCost k r) :=
    build_keep (build_backTable hk false m row hm hrow hconst)
  have H₂ : Build A₁ A₂ (2^k*2^(k-hc)*unitCost k r) := build_keep
    (build_backTable hk true m col (fun j i => Or.inl (hm j i)) (fun i => Or.inl (hcol i))
      (fun b => Or.inl (hconst b)))
  have hpad : Fintype.card D + Fintype.card Q ≤ 2^p := by
    simpa only [D, Q, Side, Samples, Fintype.card_prod, Fintype.card_fin, a, b, p, pow_add, Nat.mul_assoc] using padding_bound a b
  have H₃ := typedJoinG (A:=A₂) p (k+k) 1 dq qq pay hpad
    (fun x i => pairKey_bound _ _ _) (fun x i => pairKey_bound _ _ _) ?_ ?_
    (fun i j h => Or.inl (Or.inl (hconst true)))
    (Or.inl (Or.inl (hconst false))) (Or.inl (Or.inl (hconst true)))
  · have HG : Build A₂ (signalGrid (witSignal F G)) (100*(p+1)^2*2^p*(k+k+1+1)) := by
      refine relax H₃ le_rfl ?_ le_rfl
      rintro f ⟨i,y,rfl⟩
      refine ⟨(i,y),0,by decide,?_⟩
      funext x
      unfold witSignal joinFlag
      congr 1
      apply propext
      have hu (j : Side k) : F i j x = true ↔ ∃ lo : Fin (2^(k-hr)),
          wordNat (sample i) x = wordNat (U j lo) x :=
        tableBit_back hrk hk hk6 r m false j (sample i) row x
      have hv (j : Side k) : G j y x = true ↔ ∃ lo : Fin (2^(k-hc)), y.val = wordNat (V j lo) x := by
        simpa only [G, V, colTests, constWord, wordNat, toNat_ofNat y.isLt] using
          tableBit_back hck hk hk6 r m true j (constWord y) col x
      constructor
      · rintro ⟨j,hr',hc'⟩
        obtain ⟨u,hu'⟩ := (hu j).mp hr'
        obtain ⟨v,hv'⟩ := (hv j).mp hc'
        exact ⟨(j,u,v),by simp [dq, qq, hu', hv'], rfl⟩
      · rintro ⟨⟨j,u,v⟩,he,_⟩
        have h := (pairKey_eq (toNat_lt _) (toNat_lt _) (toNat_lt _) y.isLt).mp he
        exact ⟨j,(hu j).mpr ⟨u,h.1.symm⟩,(hv j).mpr ⟨v,h.2.symm⟩⟩
    refine relax (build_next (build_next H₁ H₂) HG) le_rfl le_rfl ?_
    have hp : p+1 ≤ 3*(k+1) := by dsimp [p,a,b]; omega
    have hP : 2^p ≤ 2*(2^k*2^(k-hr)*2^(k-hc)+2^s*2^k) := by
      simpa only [p, a, b, pow_add] using padding_cost a b
    have hj : 100*(p+1)^2*2^p*(k+k+1+1) ≤
        (10000*(k+1)^3)*(2^k*2^(k-hr)*2^(k-hc)+2^s*2^k) := by
      calc
        _ ≤ 100*(3*(k+1))^2*(2*(2^k*2^(k-hr)*2^(k-hc)+2^s*2^k))*(2*(k+1)) := by gcongr <;> omega
        _ = 3600*(k+1)^3*(2^k*2^(k-hr)*2^(k-hc)+2^s*2^k) := by ring
        _ ≤ _ := by gcongr; decide
    calc
      _ ≤ (2^k*2^(k-hr)*((10000*(k+1)^3)*(r+1)) + 2^k*2^(k-hc)*((10000*(k+1)^3)*(r+1))) +
          (10000*(k+1)^3)*(2^k*2^(k-hr)*2^(k-hc)+2^s*2^k) := by gcongr <;> exact unitCost_le _ _
      _ = _ := by dsimp [routeCost, expansionSize]; ring
  · intro i j hj
    by_cases h : j < k
    · rw [show (fun x => (dq x i).testBit j) = U i.1 i.2.1 ⟨j,h⟩ from by
        funext x; simp [dq, pairKey_bit, hj, h, wordNat_bit _ x ⟨j,h⟩]]
      exact Or.inl (Or.inr ⟨_,_,⟨_,rfl⟩⟩)
    · have hj' : j-k < k := by omega
      rw [show (fun x => (dq x i).testBit j) = V i.1 i.2.2 ⟨j-k,hj'⟩ from by
        funext x; simp [dq, pairKey_bit, hj, h, wordNat_bit _ x ⟨j-k,hj'⟩]]
      exact Or.inr ⟨_,_,⟨_,rfl⟩⟩
  · intro i j hj
    by_cases h : j < k
    · rw [show (fun x => (qq x i).testBit j) = sample i.1 ⟨j,h⟩ from by
        funext x; simp [qq, pairKey_bit, hj, h, wordNat_bit _ x ⟨j,h⟩]]
      exact Or.inl (Or.inl (hsamp _ _))
    · simpa [qq, pairKey_bit, hj, h] using (show (fun _ : Fin n → Bool => i.2.val.testBit (j-k)) ∈ A₂ from
        Or.inl (Or.inl (hconst _)))

end Routes

-- Fragment Product.

section FastWordProduct

open scoped BigOperators Matrix

variable {n : Nat}

abbrev ProductWord (k : Nat) := ZMod (2 ^ (k + 1))

abbrev ProductSignal (n k : Nat) := (Fin n → Bool) → ProductWord k

def wordBit (k : Nat) (f : ProductSignal n k) (i : Nat) : Sig n :=
  fun x => (f x).val.testBit i

def wordSignals (k : Nat) (f : ProductSignal n k) : Set (Sig n) :=
  {g | ∃ i < k + 1, g = wordBit k f i}

private theorem wordBits_mem {k : Nat} {A : Set (Sig n)} {f : ProductSignal n k}
    (h : wordSignals k f ⊆ A) {i : Nat} (hi : i < k + 1) : wordBit k f i ∈ A :=
  h ⟨i, hi, rfl⟩

private theorem wordBit_natCast (k a i : Nat) (hi : i < k + 1) :
    (a : ProductWord k).val.testBit i = a.testBit i := by
  simp [ZMod.val_natCast, hi]

abbrev wordBool (k : Nat) (f : Sig n) : ProductSignal n k := fun x => (f x).toNat

private theorem wordBool_bit (k : Nat) (f : Sig n) (i : Nat) (hi : i < k + 1) :
    wordBit k (wordBool k f) i = if i = 0 then f else fun _ => false := by
  funext x
  change ((f x).toNat : ProductWord k).val.testBit i = _
  rw [wordBit_natCast k _ _ hi]
  cases i with
  | zero => cases hx : f x <;> simp [hx, Nat.testBit_zero]
  | succ i =>
    simp only [Nat.succ_ne_zero, ↓reduceIte]
    apply Nat.testBit_lt_two_pow
    have hp := Nat.one_lt_two_pow (n := i + 1) (by omega)
    cases f x <;> simp_all

theorem wordZeroG (k : Nat) {A : Set (Sig n)} :
    Build A (wordSignals k (fun _ => 0)) 1 := by
  refine relax (constG (A := A) false) le_rfl ?_ le_rfl
  rintro _ ⟨i, hi, rfl⟩
  exact Set.mem_singleton_iff.mpr (by funext x; simp [wordBit])

theorem wordBoolG (k : Nat) {A : Set (Sig n)} {f : Sig n} (hf : f ∈ A) :
    Build A (wordSignals k (wordBool k f)) 1 := by
  have H := constG (A := A) false
  refine relax (seq H (idle (A := A ∪ {fun _ => false}) (B := wordSignals k (wordBool k f)) ?_))
    le_rfl Set.subset_union_right (by omega)
  rintro _ ⟨i, hi, rfl⟩
  rw [wordBool_bit k f i hi]
  split
  · exact Or.inl hf
  · exact Or.inr rfl

private theorem wordOneG (k : Nat) {A : Set (Sig n)} :
    Build A (wordSignals k (fun _ => 1)) 2 := by
  have he : wordBool k (fun _ : Fin n → Bool => true) = (fun _ => 1) := by
    funext x
    exact Nat.cast_one
  rw [← he]
  have H := wordBoolG k (A := A ∪ {fun _ => true}) (f := fun _ => true) (Or.inr rfl)
  exact relax (seq (constG (A := A) true) H) le_rfl Set.subset_union_right le_rfl

private theorem wordAddWithFalseG (k : Nat) {A : Set (Sig n)} (f g : ProductSignal n k)
    (hf : wordSignals k f ⊆ A) (hg : wordSignals k g ⊆ A)
    (hz : (fun _ => false) ∈ A) :
    Build A (wordSignals k (fun x => f x + g x)) (12 * (k + 1)) := by
  refine relax (addWordG (wordBit k f) (wordBit k g) (k+1)
    (fun _ hi => wordBits_mem hf hi) (fun _ hi => wordBits_mem hg hi) hz) le_rfl ?_ le_rfl
  rintro _ ⟨i, hi, rfl⟩
  refine ⟨i, by omega, ?_⟩
  funext x
  let a := fun j => (f x).val.testBit j
  let b := fun j => (g x).val.testBit j
  change (f x + g x).val.testBit i = sumBitRec a b (k+1) i
  have ha : bitsVal a (k+1) = (f x).val :=
    bitsVal_of_testBit _ _ (ZMod.val_lt _)
  have hb : bitsVal b (k+1) = (g x).val :=
    bitsVal_of_testBit _ _ (ZMod.val_lt _)
  rw [ZMod.val_add, Nat.testBit_mod_two_pow]
  simp only [hi, decide_true, Bool.true_and]
  rw [← ha, ← hb, ← bitsVal_addWord]
  exact bitsVal_testBit _ _ _ (by omega)

theorem wordAddG (k : Nat) {A : Set (Sig n)} (f g : ProductSignal n k)
    (hf : wordSignals k f ⊆ A) (hg : wordSignals k g ⊆ A) :
    Build A (wordSignals k (fun x => f x + g x)) (13 * (k + 1)) := by
  have H := wordAddWithFalseG k (A := A ∪ {fun _ => false}) f g
    (hf.trans Set.subset_union_left)
    (hg.trans Set.subset_union_left) (Or.inr rfl)
  exact relax (seq (constG (A := A) false) H) le_rfl Set.subset_union_right (by omega)

private def wordFrom (k : Nat) (f : Nat → Sig n) : ProductSignal n k :=
  fun x => (bitsVal (fun i => f i x) (k+1) : ProductWord k)

private theorem wordFrom_bit (k : Nat) (f : Nat → Sig n) (i : Nat) (hi : i < k + 1) :
    wordBit k (wordFrom k f) i = f i := by
  funext x
  change (bitsVal (fun j => f j x) (k+1) : ProductWord k).val.testBit i = f i x
  rw [wordBit_natCast k _ _ hi, bitsVal_testBit _ _ _ hi]

private theorem complement_bitsVal (f : Nat → Bool) (m : Nat) :
    bitsVal f m + bitsVal (fun i => !(f i)) m + 1 = 2^m := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [Nat.pow_succ]
    simp only [bitsVal]
    rcases Bool.eq_false_or_eq_true (f m) with hm | hm <;> simp [hm] <;> omega

private def wordCompl (k : Nat) (f : ProductSignal n k) : ProductSignal n k :=
  wordFrom k (fun i => nt (wordBit k f i))

private theorem wordCompl_eq (k : Nat) (f : ProductSignal n k) (x : Fin n → Bool) :
    wordCompl k f x + 1 = -(f x) := by
  let g := fun i => (f x).val.testBit i
  have hb : bitsVal g (k+1) = (f x).val := bitsVal_of_testBit _ _ (ZMod.val_lt _)
  have hc := complement_bitsVal g (k+1)
  rw [hb] at hc
  have hcast := congrArg (fun t : Nat => (t : ProductWord k)) hc
  change ((↑((f x).val + bitsVal (fun i => !(g i)) (k+1) + 1) : ProductWord k) =
    (↑(2^(k+1) : Nat) : ProductWord k)) at hcast
  simp only [Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat] at hcast
  have hmod : (2 : ProductWord k) ^ (k+1) = 0 := by
    simpa only [Nat.cast_pow, Nat.cast_ofNat] using (ZMod.natCast_self (2 ^ (k+1)))
  rw [ZMod.natCast_zmod_val, hmod] at hcast
  change (bitsVal (fun i => !(g i)) (k+1) : ProductWord k) + 1 = _
  linear_combination hcast

private theorem wordComplG (k : Nat) {A : Set (Sig n)} (g : ProductSignal n k)
    (hg : wordSignals k g ⊆ A) : Build A (wordSignals k (wordCompl k g)) (k + 1) := by
  have H := rangeG (A := A) (m := k+1) (fun i => nt (wordBit k g i)) 1
    (fun _ hi => notG (wordBits_mem hg hi))
  refine relax H le_rfl ?_ (by omega)
  rintro _ ⟨i, hi, rfl⟩
  exact ⟨i, hi, wordFrom_bit k _ i hi⟩

theorem wordSubG (k : Nat) {A : Set (Sig n)} (f g : ProductSignal n k)
    (hf : wordSignals k f ⊆ A) (hg : wordSignals k g ⊆ A) :
    Build A (wordSignals k (fun x => f x - g x)) (30 * (k + 1)) := by
  let B := wordSignals k (fun _ : Fin n → Bool => 1)
  let C := wordSignals k (wordCompl k g)
  have H1 : Build A B 2 := wordOneG k
  have H2 : Build (A ∪ B) C (k+1) := wordComplG k g (hg.trans Set.subset_union_left)
  have H3 := wordAddG k (A := A ∪ (B ∪ C)) f (wordCompl k g)
    (hf.trans Set.subset_union_left) (by intro y hy; exact Or.inr (Or.inr hy))
  have H4 := wordAddG k (A := A ∪ ((B ∪ C) ∪ wordSignals k (fun x => f x + wordCompl k g x)))
    (fun x => f x + wordCompl k g x) (fun _ => 1)
    (by intro y hy; exact Or.inr (Or.inr hy))
    (by intro y hy; exact Or.inr (Or.inl (Or.inl hy)))
  have he : (fun x => (f x + wordCompl k g x) + 1) = (fun x => f x - g x) := by
    funext x
    rw [add_assoc, wordCompl_eq, sub_eq_add_neg]
  refine relax (seq (seq (seq H1 H2) H3) H4) le_rfl ?_ (by omega)
  rw [← he]
  exact Set.subset_union_right

private def wordPartial (k : Nat) (f g : ProductSignal n k) (j : Nat) : ProductSignal n k :=
  fun x => if wordBit k g j x then f x * (2 : ProductWord k)^j else 0

private theorem wordPartial_bit (k : Nat) (f g : ProductSignal n k) (j i : Nat)
    (hi : i < k+1) : wordBit k (wordPartial k f g j) i =
      if j ≤ i then an (wordBit k f (i-j)) (wordBit k g j) else fun _ => false := by
  funext x
  by_cases h : wordBit k g j x = true
  · have hcast : f x * (2 : ProductWord k)^j = (↑((f x).val <<< j) : ProductWord k) := by
      rw [Nat.shiftLeft_eq, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, ZMod.natCast_zmod_val]
    change (if wordBit k g j x then f x * (2 : ProductWord k)^j else 0).val.testBit i = _
    rw [ite_eq_left h, hcast, wordBit_natCast k _ _ hi, Nat.testBit_shiftLeft]
    have hg : (g x).val.testBit j = true := h
    by_cases hij : j ≤ i <;> simp [hij, an, wordBit, hg]
  · have h' : wordBit k g j x = false := Bool.eq_false_of_not_eq_true h
    change (if wordBit k g j x then f x * (2 : ProductWord k)^j else 0).val.testBit i = _
    by_cases hij : j ≤ i <;> simp [hij, an, h']

private theorem wordPartialG (k : Nat) {A : Set (Sig n)} (f g : ProductSignal n k)
    (hf : wordSignals k f ⊆ A) (hg : wordSignals k g ⊆ A) (hz : (fun _ => false) ∈ A)
    (j : Nat) (hj : j < k+1) : Build A (wordSignals k (wordPartial k f g j)) (k+1) := by
  have H := rangeG (A := A) (m := k+1) (wordBit k (wordPartial k f g j)) 1 (by
    intro i hi
    rw [wordPartial_bit k f g j i hi]
    split
    · exact andG (wordBits_mem hf (by omega)) (wordBits_mem hg hj)
    · exact relax (idle (Set.singleton_subset_iff.mpr hz)) le_rfl le_rfl (by omega))
  simpa only [wordSignals, Nat.mul_one] using H

private def wordPrefix (k : Nat) (f g : ProductSignal n k) (j : Nat) : ProductSignal n k :=
  fun x => f x * (bitsVal (fun i => wordBit k g i x) j : ProductWord k)

private theorem wordPrefix_succ (k : Nat) (f g : ProductSignal n k) (j : Nat) :
    wordPrefix k f g (j+1) = fun x => wordPrefix k f g j x + wordPartial k f g j x := by
  funext x
  simp only [wordPrefix, wordPartial, bitsVal, Nat.cast_add, mul_add]
  by_cases h : wordBit k g j x = true <;> simp [h, Nat.cast_pow]

private theorem wordMulG (k : Nat) {A : Set (Sig n)} (f g : ProductSignal n k)
    (hf : wordSignals k f ⊆ A) (hg : wordSignals k g ⊆ A) :
    Build A (wordSignals k (fun x => f x * g x)) (15 * (k+1)^2) := by
  let Z : Set (Sig n) := {fun _ => false}
  let S := A ∪ Z
  have hz : (fun _ => false) ∈ S := Or.inr rfl
  have H : ∀ j ≤ k+1, Build S (wordSignals k (wordPrefix k f g j)) (13 * (k+1)*j) := by
    intro j
    induction j with
    | zero =>
      intro _
      rw [Nat.mul_zero]
      apply idle
      rintro _ ⟨i, hi, rfl⟩
      have he : wordBit k (wordPrefix k f g 0) i = fun _ => false := by
        funext x; simp [wordBit, wordPrefix, bitsVal]
      rw [he]
      exact hz
    | succ j ih =>
      intro hj
      have P := ih (by omega)
      have Q := wordPartialG k (A := S) f g (hf.trans Set.subset_union_left)
        (hg.trans Set.subset_union_left) hz j (by omega)
      have R := seq P (relax Q Set.subset_union_left le_rfl le_rfl)
      have T := wordAddWithFalseG k
        (A := S ∪ (wordSignals k (wordPrefix k f g j) ∪ wordSignals k (wordPartial k f g j)))
        (wordPrefix k f g j) (wordPartial k f g j)
        (by intro y hy; exact Or.inr (Or.inl hy)) (by intro y hy; exact Or.inr (Or.inr hy))
        (Or.inl hz)
      rw [wordPrefix_succ]
      refine relax (seq R T) le_rfl Set.subset_union_right ?_
      rw [Nat.mul_succ (13*(k+1)) j]
      omega
  have he : wordPrefix k f g (k+1) = (fun x => f x * g x) := by
    funext x
    unfold wordPrefix
    change f x * (bitsVal (fun i => (g x).val.testBit i) (k+1) : ProductWord k) = _
    rw [bitsVal_of_testBit _ _ (ZMod.val_lt _), ZMod.natCast_zmod_val]
  rw [← he]
  refine relax (seq (constG (A := A) false) (H _ le_rfl)) le_rfl Set.subset_union_right ?_
  have hw : 1 ≤ (k+1)^2 := Nat.succ_le_of_lt (pow_pos (Nat.succ_pos _) _)
  rw [Nat.mul_assoc, ← pow_two]
  omega

abbrev ProductMatrix (n k d : Nat) := Fin d → Fin d → ProductSignal n k

def matrixSignals (k : Nat) {d : Nat} (F : ProductMatrix n k d) : Set (Sig n) :=
  {g | ∃ i j, g ∈ wordSignals k (F i j)}

private theorem productFamilyG {α : Type*} [Fintype α] {A : Set (Sig n)}
    (S : α → Set (Sig n)) (c : Nat) (H : ∀ i, Build A (S i) c) :
    Build A {g | ∃ i, g ∈ S i} (Fintype.card α * c) := by
  classical
  have h := listBuildSets (Finset.univ : Finset α).toList S c (fun i _ => H i)
  simpa only [Finset.length_toList, Finset.card_univ, Finset.mem_toList, Finset.mem_univ, true_and] using h

private theorem productEntriesG (k : Nat) {d : Nat} {A : Set (Sig n)}
    (F : ProductMatrix n k d) (c : Nat) (H : ∀ i j, Build A (wordSignals k (F i j)) c) :
    Build A (matrixSignals k F) (d*d*c) := by
  have h := productFamilyG (fun p : Fin d × Fin d => wordSignals k (F p.1 p.2)) c
    (fun p => H p.1 p.2)
  simp only [Fintype.card_prod, Fintype.card_fin] at h
  refine relax h le_rfl ?_ le_rfl
  rintro _ ⟨i, j, hj⟩
  exact ⟨(i, j), hj⟩

theorem matrixAddG (k : Nat) {d : Nat} {A : Set (Sig n)} (F G : ProductMatrix n k d)
    (hF : matrixSignals k F ⊆ A) (hG : matrixSignals k G ⊆ A) :
    Build A (matrixSignals k (fun i j x => F i j x + G i j x)) (d*d*(13*(k+1))) :=
  productEntriesG k _ _ (fun i j => wordAddG k _ _
    (fun _ hg => hF ⟨i, j, hg⟩) (fun _ hg => hG ⟨i, j, hg⟩))

private theorem matrixSubG (k : Nat) {d : Nat} {A : Set (Sig n)} (F G : ProductMatrix n k d)
    (hF : matrixSignals k F ⊆ A) (hG : matrixSignals k G ⊆ A) :
    Build A (matrixSignals k (fun i j x => F i j x - G i j x)) (d*d*(30*(k+1))) :=
  productEntriesG k _ _ (fun i j => wordSubG k _ _
    (fun _ hg => hF ⟨i, j, hg⟩) (fun _ hg => hG ⟨i, j, hg⟩))

private abbrev ProductLinear (n k d : Nat) :=
  Bool × ProductMatrix n k d × ProductMatrix n k d

private def productLinearOutput {k d : Nat} (T : ProductLinear n k d) : ProductMatrix n k d :=
  match T.1 with
  | false => fun i j x => T.2.1 i j x + T.2.2 i j x
  | true => fun i j x => T.2.1 i j x - T.2.2 i j x

private def matrixFamilySignals (k : Nat) {d t : Nat} (F : Fin t → ProductMatrix n k d) :
    Set (Sig n) := {g | ∃ i, g ∈ matrixSignals k (F i)}

private theorem matrixFamilyG (k : Nat) {d t : Nat} {A : Set (Sig n)}
    (F : Fin t → ProductMatrix n k d) (c : Nat)
    (H : ∀ i, Build A (matrixSignals k (F i)) c) :
    Build A (matrixFamilySignals k F) (t*c) := by
  simpa only [Fintype.card_fin, matrixFamilySignals] using
    productFamilyG (fun i => matrixSignals k (F i)) c H

private theorem matrixLinearFamilyG (k : Nat) {d t : Nat} {A : Set (Sig n)}
    (T : Fin t → ProductLinear n k d)
    (hL : ∀ i, matrixSignals k (T i).2.1 ⊆ A)
    (hR : ∀ i, matrixSignals k (T i).2.2 ⊆ A) :
    Build A (matrixFamilySignals k (fun i => productLinearOutput (T i))) (t * (d*d*(30*(k+1)))) := by
  apply matrixFamilyG
  intro i
  unfold productLinearOutput
  split
  · refine relax (matrixAddG k _ _ (hL i) (hR i)) le_rfl le_rfl ?_
    exact Nat.mul_le_mul_left _ (by omega)
  · exact matrixSubG k _ _ (hL i) (hR i)

private def productMatrix {k d : Nat} (F G : ProductMatrix n k d) : ProductMatrix n k d :=
  fun i j x => ∑ l, F i l x * G l j x

private def productSplitEquiv (s : Nat) : Fin (2^s) ⊕ Fin (2^s) ≃ Fin (2^(s+1)) :=
  finSumFinEquiv.trans (finCongr (by rw [pow_succ, mul_two]))

private def productEmbed (s : Nat) (b : Bool) (i : Fin (2^s)) : Fin (2^(s+1)) :=
  productSplitEquiv s (if b then Sum.inr i else Sum.inl i)

private def productQuadrant (s : Nat) {k : Nat} (F : ProductMatrix n k (2^(s+1)))
    (b c : Bool) : ProductMatrix n k (2^s) :=
  fun i j => F (productEmbed s b i) (productEmbed s c j)

private theorem quadrantSignals_subset (s k : Nat) (F : ProductMatrix n k (2^(s+1)))
    (b c : Bool) : matrixSignals k (productQuadrant s F b c) ⊆ matrixSignals k F := by
  rintro _ ⟨i, j, hj⟩
  exact ⟨productEmbed s b i, productEmbed s c j, hj⟩

private theorem quadrantSignals_cover (s k : Nat) {A : Set (Sig n)}
    (F : ProductMatrix n k (2^(s+1))) (H : ∀ b c, matrixSignals k (productQuadrant s F b c) ⊆ A) :
    matrixSignals k F ⊆ A := by
  rintro _ ⟨i, j, hj⟩
  obtain ⟨i, rfl⟩ := (productSplitEquiv s).surjective i
  obtain ⟨j, rfl⟩ := (productSplitEquiv s).surjective j
  rcases i with i | i <;> rcases j with j | j
  · exact H false false ⟨i, j, hj⟩
  · exact H false true ⟨i, j, hj⟩
  · exact H true false ⟨i, j, hj⟩
  · exact H true true ⟨i, j, hj⟩

private theorem productQuadrant_mul (s : Nat) {k : Nat}
    (F G : ProductMatrix n k (2^(s+1))) (b c : Bool) :
    productQuadrant s (productMatrix F G) b c = fun i j x =>
      productMatrix (productQuadrant s F b false) (productQuadrant s G false c) i j x +
      productMatrix (productQuadrant s F b true) (productQuadrant s G true c) i j x := by
  funext i j x
  let f := fun l : Fin (2^(s+1)) => F (productEmbed s b i) l x * G l (productEmbed s c j) x
  change (∑ l, f l) = _
  rw [← (productSplitEquiv s).sum_comp f, Fintype.sum_sum_type] <;> rfl

private theorem strassenProducts {R : Type*} [Ring R] (a b c d e f g h : R) :
    let p₀ := (a + d) * (e + h)
    let p₁ := (c + d) * e
    let p₂ := a * (f - h)
    let p₃ := d * (g - e)
    let p₄ := (a + b) * h
    let p₅ := (c - a) * (e + f)
    let p₆ := (b - d) * (g + h)
    ((p₀ + p₃) + (p₆ - p₄) = a*e + b*g) ∧
    (p₂ + p₄ = a*f + b*h) ∧ (p₁ + p₃ = c*e + d*g) ∧
    ((p₀ - p₁) + (p₂ + p₅) = c*f + d*h) := by
  dsimp
  refine ⟨?_, ?_, ?_, ?_⟩ <;> noncomm_ring

-- Charge each non-leaf for ten input and eight output block combinations.
-- Slack proportional to the number of entries pays for these combinations.
private def squareProductCost (k : Nat) : Nat → Nat
  | 0 => 15*(k+1)^2
  | s+1 => 7*squareProductCost k s + 540*(k+1)*(2^s * 2^s)

private theorem squareProductCost_bound (k s : Nat) :
    squareProductCost k s + 200*(k+1)^2*4^s ≤ 1000*(k+1)^2*7^s := by
  induction s with
  | zero =>
    simp only [squareProductCost, pow_zero, mul_one]
    omega
  | succ s ih =>
    have hw : k+1 ≤ (k+1)^2 := by
      rw [pow_two]
      exact Nat.le_mul_of_pos_right _ (by omega)
    have hd : (2 : Nat)^s * 2^s = 4^s := by rw [← mul_pow] <;> norm_num
    have hc : 540*(k+1)*(2^s * 2^s) ≤ 600*(k+1)^2*4^s := by
      rw [hd]
      exact Nat.mul_le_mul_right _ (by omega)
    calc
      _ = (7*squareProductCost k s + 540*(k+1)*(2^s * 2^s)) + 800*(k+1)^2*4^s := by
        simp only [squareProductCost, pow_succ (4 : Nat) s]
        ring
      _ ≤ 7*squareProductCost k s + 600*(k+1)^2*4^s + 800*(k+1)^2*4^s := by omega
      _ = 7*(squareProductCost k s + 200*(k+1)^2*4^s) := by ring
      _ ≤ 7*(1000*(k+1)^2*7^s) := Nat.mul_le_mul_left _ ih
      _ = _ := by rw [pow_succ (7 : Nat) s]; ring

set_option maxHeartbeats 2000000 in
private theorem matrixProductAtCostG (k s : Nat) {A : Set (Sig n)}
    (F G : ProductMatrix n k (2^s)) (hF : matrixSignals k F ⊆ A) (hG : matrixSignals k G ⊆ A) :
    Build A (matrixSignals k (productMatrix F G)) (squareProductCost k s) := by
  induction s generalizing A with
  | zero =>
    have H := wordMulG k (F 0 0) (G 0 0) (fun _ hg => hF ⟨0, 0, hg⟩)
      (fun _ hg => hG ⟨0, 0, hg⟩)
    refine relax H le_rfl ?_ le_rfl
    rintro _ ⟨i, j, hij⟩
    have hi : i = 0 := by
      apply Fin.ext
      have ht : i.val < 1 := i.isLt
      change i.val = 0
      omega
    have hj : j = 0 := by
      apply Fin.ext
      have ht : j.val < 1 := j.isLt
      change j.val = 0
      omega
    subst i
    subst j
    have hentry : productMatrix F G 0 0 = (fun x => F 0 0 x * G 0 0 x) := by
      funext x
      change (∑ l : Fin 1, F 0 l x * G l 0 x) = _
      exact Fin.sum_univ_one _
    rw [hentry] at hij
    exact hij
  | succ s ih =>
    let d₀ := 2^s
    let a := productQuadrant s F false false
    let b := productQuadrant s F false true
    let c := productQuadrant s F true false
    let d := productQuadrant s F true true
    let e := productQuadrant s G false false
    let f := productQuadrant s G false true
    let g := productQuadrant s G true false
    let h := productQuadrant s G true true
    have ha : matrixSignals k a ⊆ A := (quadrantSignals_subset s k F false false).trans hF
    have hb : matrixSignals k b ⊆ A := (quadrantSignals_subset s k F false true).trans hF
    have hc : matrixSignals k c ⊆ A := (quadrantSignals_subset s k F true false).trans hF
    have hd : matrixSignals k d ⊆ A := (quadrantSignals_subset s k F true true).trans hF
    have he : matrixSignals k e ⊆ A := (quadrantSignals_subset s k G false false).trans hG
    have hf : matrixSignals k f ⊆ A := (quadrantSignals_subset s k G false true).trans hG
    have hg : matrixSignals k g ⊆ A := (quadrantSignals_subset s k G true false).trans hG
    have hh : matrixSignals k h ⊆ A := (quadrantSignals_subset s k G true true).trans hG
    let T : Fin 10 → ProductLinear n k d₀ :=
      ![⟨false,a,d⟩, ⟨false,e,h⟩, ⟨false,c,d⟩, ⟨true,f,h⟩, ⟨true,g,e⟩,
        ⟨false,a,b⟩, ⟨true,c,a⟩, ⟨false,e,f⟩, ⟨true,b,d⟩, ⟨false,g,h⟩]
    let U := fun t => productLinearOutput (T t)
    let B := matrixFamilySignals k U
    have HT : Build A B (10 * (d₀*d₀*(30*(k+1)))) := matrixLinearFamilyG k T
      (by intro i; fin_cases i <;> first | exact ha | exact he | exact hc | exact hf | exact hg | exact hb)
      (by intro i; fin_cases i <;> first | exact hd | exact hh | exact he | exact hb | exact ha | exact hf)
    have hU : ∀ i, matrixSignals k (U i) ⊆ A ∪ B := fun i _ hm => Or.inr ⟨i, hm⟩
    let L : Fin 7 → ProductMatrix n k d₀ := ![U 0, U 2, a, d, U 5, U 6, U 8]
    let R : Fin 7 → ProductMatrix n k d₀ := ![U 1, e, U 3, U 4, h, U 7, U 9]
    let P := fun i => productMatrix (L i) (R i)
    let C := matrixFamilySignals k P
    have HP : Build (A ∪ B) C (7 * squareProductCost k s) := matrixFamilyG k P _ (by
      intro i
      refine ih (L i) (R i) ?_ ?_
      · fin_cases i
        · exact hU 0
        · exact hU 2
        · exact ha.trans Set.subset_union_left
        · exact hd.trans Set.subset_union_left
        · exact hU 5
        · exact hU 6
        · exact hU 8
      · fin_cases i
        · exact hU 1
        · exact he.trans Set.subset_union_left
        · exact hU 3
        · exact hU 4
        · exact hh.trans Set.subset_union_left
        · exact hU 7
        · exact hU 9)
    let S := A ∪ (B ∪ C)
    have hP : ∀ i, matrixSignals k (P i) ⊆ S := fun i _ hm => Or.inr (Or.inr ⟨i, hm⟩)
    let V : Fin 6 → ProductLinear n k d₀ :=
      ![⟨false,P 0,P 3⟩, ⟨true,P 6,P 4⟩, ⟨false,P 2,P 4⟩,
        ⟨false,P 1,P 3⟩, ⟨true,P 0,P 1⟩, ⟨false,P 2,P 5⟩]
    let Q := fun i => productLinearOutput (V i)
    let D := matrixFamilySignals k Q
    have HQ : Build S D (6 * (d₀*d₀*(30*(k+1)))) := matrixLinearFamilyG k V
      (by intro i; fin_cases i <;> first | exact hP 0 | exact hP 6 | exact hP 2 | exact hP 1)
      (by intro i; fin_cases i <;> first | exact hP 3 | exact hP 4 | exact hP 1 | exact hP 5)
    let S' := A ∪ ((B ∪ C) ∪ D)
    have hQ : ∀ i, matrixSignals k (Q i) ⊆ S' := fun i _ hm => Or.inr (Or.inr ⟨i, hm⟩)
    let W : Fin 2 → ProductLinear n k d₀ := ![⟨false,Q 0,Q 1⟩, ⟨false,Q 4,Q 5⟩]
    let O := fun i => productLinearOutput (W i)
    let E := matrixFamilySignals k O
    have HO : Build S' E (2 * (d₀*d₀*(30*(k+1)))) := matrixLinearFamilyG k W
      (by intro i; fin_cases i <;> first | exact hQ 0 | exact hQ 4)
      (by intro i; fin_cases i <;> first | exact hQ 1 | exact hQ 5)
    let asMatrix := fun (X : ProductMatrix n k d₀) (x : Fin n → Bool) =>
      show Matrix (Fin d₀) (Fin d₀) (ProductWord k) from fun i j => X i j x
    have hs (x : Fin n → Bool) := strassenProducts (asMatrix a x) (asMatrix b x)
      (asMatrix c x) (asMatrix d x) (asMatrix e x) (asMatrix f x) (asMatrix g x) (asMatrix h x)
    have h00 : productQuadrant s (productMatrix F G) false false = O 0 := by
      rw [productQuadrant_mul]
      funext i j x
      exact congrArg (fun M : Matrix (Fin d₀) (Fin d₀) (ProductWord k) => M i j) (hs x).1.symm
    have h01 : productQuadrant s (productMatrix F G) false true = Q 2 := by
      rw [productQuadrant_mul]
      funext i j x
      exact congrArg (fun M : Matrix (Fin d₀) (Fin d₀) (ProductWord k) => M i j) (hs x).2.1.symm
    have h10 : productQuadrant s (productMatrix F G) true false = Q 3 := by
      rw [productQuadrant_mul]
      funext i j x
      exact congrArg (fun M : Matrix (Fin d₀) (Fin d₀) (ProductWord k) => M i j) (hs x).2.2.1.symm
    have h11 : productQuadrant s (productMatrix F G) true true = O 1 := by
      rw [productQuadrant_mul]
      funext i j x
      exact congrArg (fun M : Matrix (Fin d₀) (Fin d₀) (ProductWord k) => M i j) (hs x).2.2.2.symm
    refine relax (seq (seq (seq HT HP) HQ) HO) le_rfl ?_ ?_
    · apply quadrantSignals_cover
      intro b₀ c₀
      cases b₀ <;> cases c₀
      · rw [h00]; intro z hz; exact Or.inr ⟨0, hz⟩
      · rw [h01]; intro z hz; exact Or.inl (Or.inr ⟨2, hz⟩)
      · rw [h10]; intro z hz; exact Or.inl (Or.inr ⟨3, hz⟩)
      · rw [h11]; intro z hz; exact Or.inr ⟨1, hz⟩
    · apply le_of_eq
      simp only [squareProductCost, d₀]
      ring

theorem matrixProductG (k s : Nat) {A : Set (Sig n)}
    (F G : ProductMatrix n k (2^s)) (hF : matrixSignals k F ⊆ A) (hG : matrixSignals k G ⊆ A) :
    Build A (matrixSignals k (fun i j x => ∑ l, F i l x * G l j x)) (1000*(k+1)^2*7^s) :=
  relax (matrixProductAtCostG k s F G hF hG) le_rfl le_rfl
    ((Nat.le_add_right _ _).trans (squareProductCost_bound k s))

end FastWordProduct

-- Fragment Tiling.

section TiledProduct

open scoped BigOperators

variable {n : Nat}

private def tileScale (k s : Nat) : Nat := (k+1)^2 * 7^s

private theorem tileArea_le (s : Nat) : 2^s * 2^s ≤ 7^s := by
  rw [← mul_pow]
  exact Nat.pow_le_pow_left (by decide) _

private theorem tileWidth_le (k : Nat) : k+1 ≤ (k+1)^2 := by
  rw [pow_two]
  exact Nat.le_mul_of_pos_right _ (by omega)

private theorem tileAreaWidth_le (k s : Nat) :
    2^s * 2^s * (k+1) ≤ tileScale k s := by
  unfold tileScale
  rw [Nat.mul_comm ((k+1)^2)]
  exact Nat.mul_le_mul (tileArea_le s) (tileWidth_le k)

private theorem tileAreaScale_le (k s : Nat) : 2^s * 2^s ≤ tileScale k s :=
  (Nat.le_mul_of_pos_right _ (by omega : 0 < k+1)).trans (tileAreaWidth_le k s)

private theorem tileScale_pos (k s : Nat) : 0 < tileScale k s := by
  unfold tileScale
  positivity

private theorem tileSquareBoolG (k s : Nat) {A : Set (Sig n)}
    (f g : Fin (2^s) → Fin (2^s) → Sig n)
    (hf : ∀ i j, f i j ∈ A) (hg : ∀ i j, g i j ∈ A) :
    Build A (matrixSignals k (fun i j x => ∑ l, wordBool k (f i l) x * wordBool k (g l j) x))
      (1100 * tileScale k s) := by
  let F := fun i j => wordBool k (f i j)
  let G := fun i j => wordBool k (g i j)
  have BF : Build A (matrixSignals k F) (2^s * 2^s * 1) :=
    gather₂ (fun i j => wordSignals k (F i j)) 1 (fun i j => wordBoolG k (hf i j))
  have BG : Build A (matrixSignals k G) (2^s * 2^s * 1) :=
    gather₂ (fun i j => wordSignals k (G i j)) 1 (fun i j => wordBoolG k (hg i j))
  have BFG := build_keep (seq BF (relax BG Set.subset_union_left le_rfl le_rfl))
  have BP := matrixProductG k s (A := A ∪ (matrixSignals k F ∪ matrixSignals k G)) F G
    (by intro b hb; exact Or.inr (Or.inl hb)) (by intro b hb; exact Or.inr (Or.inr hb))
  refine relax (build_next BFG BP) le_rfl le_rfl ?_
  have harea := tileAreaScale_le k s
  rw [show 1000 * (k+1)^2 * 7^s = 1000 * tileScale k s by unfold tileScale; ac_rfl]
  omega

private theorem tileSumG (k s t : Nat) {A : Set (Sig n)}
    (P : Fin t → Fin (2^s) → Fin (2^s) → ProductSignal n k)
    (hP : ∀ l, matrixSignals k (P l) ⊆ A) (u : Finset (Fin t)) :
    Build A (matrixSignals k (fun i j x => ∑ l ∈ u, P l i j x))
      (u.card * (2^s * 2^s * (13 * (k+1))) + 1) := by
  induction u using Finset.induction_on with
  | empty =>
    refine relax (wordZeroG k (A := A)) le_rfl ?_ (by simp)
    rintro b ⟨i, j, hb⟩
    simpa only [Finset.sum_empty] using hb
  | @insert l u hl ih =>
    let Q : Fin (2^s) → Fin (2^s) → ProductSignal n k := fun i j x => ∑ a ∈ u, P a i j x
    have H := matrixAddG k (A := A ∪ matrixSignals k Q) (P l) Q
      ((hP l).trans Set.subset_union_left) Set.subset_union_right
    refine relax (seq ih H) le_rfl ?_ ?_
    · rintro b ⟨i, j, hb⟩
      exact Or.inr ⟨i, j, by simpa only [Q, Finset.sum_insert hl] using hb⟩
    · rw [Finset.card_insert_of_notMem hl, Nat.add_mul, Nat.one_mul]
      omega

private theorem tileColumnG (k s t : Nat) (ht : 0 < t) {A : Set (Sig n)}
    (f : Fin (2^s) → (Fin t × Fin (2^s)) → Sig n)
    (g : (Fin t × Fin (2^s)) → Fin (2^s) → Sig n)
    (hf : ∀ i l, f i l ∈ A) (hg : ∀ l j, g l j ∈ A) :
    Build A (matrixSignals k (fun i j x => ∑ l, wordBool k (f i l) x * wordBool k (g l j) x))
      (1200 * t * tileScale k s) := by
  let P (a : Fin t) (i j : Fin (2^s)) : ProductSignal n k := fun x =>
    ∑ l : Fin (2^s), wordBool k (f i (a,l)) x * wordBool k (g (a,l) j) x
  let S : Set (Sig n) := {b | ∃ a, b ∈ matrixSignals k (P a)}
  have H : Build A S (t * (1100 * tileScale k s)) :=
    finSetsG (fun a => matrixSignals k (P a)) _ (fun a =>
      tileSquareBoolG k s (fun i l => f i (a,l)) (fun l j => g (a,l) j)
        (fun i l => hf i (a,l)) (fun l j => hg (a,l) j))
  have J := tileSumG k s t (A := S) P (fun a b hb => ⟨a, hb⟩) Finset.univ
  rw [Finset.card_univ, Fintype.card_fin] at J
  have he : (fun i j x => ∑ a, P a i j x) =
      (fun i j x => ∑ l, wordBool k (f i l) x * wordBool k (g l j) x) := by
    funext i j x
    exact (Fintype.sum_prod_type (fun l => wordBool k (f i l) x * wordBool k (g l j) x)).symm
  rw [← he]
  refine relax (build_next H J) le_rfl le_rfl ?_
  have hadd : 2^s * 2^s * (13 * (k+1)) ≤ 13 * tileScale k s := by
    calc
      _ = 13 * (2^s * 2^s * (k+1)) := by ac_rfl
      _ ≤ _ := Nat.mul_le_mul_left _ (tileAreaWidth_le k s)
  calc
    _ ≤ t * (1100 * tileScale k s) + (t * (13 * tileScale k s) + 1) := by
      exact Nat.add_le_add_left (Nat.add_le_add_right (Nat.mul_le_mul_left t hadd) 1) _
    _ ≤ 1200 * t * tileScale k s := by
      have hp := Nat.mul_pos ht (tileScale_pos k s)
      calc
        _ = 1113 * (t * tileScale k s) + 1 := by ring
        _ ≤ 1200 * (t * tileScale k s) := by omega
        _ = _ := by ac_rfl

private def tileIndex (k s : Nat) (hs : s ≤ k) :
    Fin (2^(k-s)) × Fin (2^s) ≃ Fin (2^k) :=
  finProdFinEquiv.trans (finCongr (by rw [← pow_add, Nat.sub_add_cancel hs]))

private theorem tileCountVal (k : Nat) (f g : Fin (2^k) → Sig n) (x : Fin n → Bool) :
    (∑ l, wordBool k (f l) x * wordBool k (g l) x).val =
      (Finset.univ.filter (fun l => f l x = true ∧ g l x = true)).card := by
  let p : Fin (2^k) → Prop := fun l => f l x = true ∧ g l x = true
  have hv : (∑ l, wordBool k (f l) x * wordBool k (g l) x) =
      ((Finset.univ.filter p).card : ProductWord k) := by
    rw [Finset.natCast_card_filter]
    apply Finset.sum_congr rfl
    intro l _
    cases hf : f l x <;> cases hg : g l x <;> simp [p, wordBool, hf, hg]
  rw [hv]
  apply ZMod.val_natCast_of_lt
  have hle : (Finset.univ.filter p).card ≤ 2^k := by
    simpa using Finset.card_le_card (Finset.filter_subset p (Finset.univ : Finset (Fin (2^k))))
  rw [pow_succ]
  have hp := Nat.two_pow_pos k
  omega

private theorem tileWordNonzeroG (k : Nat) {A : Set (Sig n)} (f : ProductSignal n k)
    (hf : wordSignals k f ⊆ A) :
    Build A {fun x => decide ((f x).val ≠ 0)} (5 * (k+1) + 1) := by
  have H := neWordG (A := A ∪ {fun _ => false}) (wordBit k f) (fun _ _ => false) (k+1)
    (fun i hi => Or.inl (hf ⟨i, hi, rfl⟩)) (fun _ _ => Or.inr rfl) (Or.inr rfl)
  have hz : ∀ m, bitsVal (fun _ => false) m = 0 := by
    intro m
    induction m with
    | zero => rfl
    | succ m ih => simp [bitsVal, ih]
  have he : (fun x : Fin n → Bool =>
      decide (bitsVal (fun i => wordBit k f i x) (k+1) ≠ bitsVal (fun _ => false) (k+1))) =
      (fun x => decide ((f x).val ≠ 0)) := by
    funext x
    change decide (bitsVal (fun i => (f x).val.testBit i) (k+1) ≠
      bitsVal (fun _ => false) (k+1)) = _
    rw [bitsVal_of_testBit _ _ (ZMod.val_lt (f x)), hz]
  rw [he] at H
  refine relax (seq (constG (A := A) false) H) le_rfl Set.subset_union_right ?_
  omega

/-- All Boolean witness outputs, with both the inner dimension and output columns tiled. -/
theorem tiledWitnessG (k s : Nat) (hs : s ≤ k) {A : Set (Sig n)}
    (f : Fin (2^s) → Fin (2^k) → Sig n) (g : Fin (2^k) → Fin (2^k) → Sig n)
    (hf : ∀ i l, f i l ∈ A) (hg : ∀ l j, g l j ∈ A) :
    Build A {b | ∃ i j, b = fun x => decide (∃ l, f i l x = true ∧ g l j x = true)}
      (3000 * (k+1)^2 * (2^(k-s))^2 * 7^s) := by
  let t := 2^(k-s)
  let e : Fin t × Fin (2^s) ≃ Fin (2^k) := tileIndex k s hs
  let W (i : Fin (2^s)) (j : Fin (2^k)) : ProductSignal n k := fun x =>
    ∑ l, wordBool k (f i l) x * wordBool k (g l j) x
  let V (i : Fin (2^s)) (j : Fin (2^k)) : Sig n := fun x =>
    decide (∃ l, f i l x = true ∧ g l j x = true)
  have hval (i : Fin (2^s)) (j : Fin (2^k)) : (fun x => decide ((W i j x).val ≠ 0)) = V i j := by
    funext x
    change decide ((W i j x).val ≠ 0) = decide (∃ l, f i l x = true ∧ g l j x = true)
    rw [show (W i j x).val = _ from tileCountVal k (f i) (fun l => g l j) x]
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq, ← Nat.pos_iff_ne_zero, Finset.card_pos]
    simp [Finset.Nonempty]
  have ht : 0 < t := Nat.two_pow_pos _
  have H (a : Fin t) : Build A {b | ∃ i j, b = V i (e (a,j))}
      (3000 * t * tileScale k s) := by
    let M : Fin (2^s) → Fin (2^s) → ProductSignal n k := fun i j => W i (e (a,j))
    have P := tileColumnG k s t ht (fun i l => f i (e l)) (fun l j => g (e l) (e (a,j)))
      (fun i l => hf i (e l)) (fun l j => hg (e l) (e (a,j)))
    have hM : (fun i j x => ∑ l, wordBool k (f i (e l)) x * wordBool k (g (e l) (e (a,j))) x) = M := by
      funext i j x
      exact e.sum_comp (fun l => wordBool k (f i l) x * wordBool k (g l (e (a,j))) x)
    rw [hM] at P
    have Q := gather₂ (A := matrixSignals k M) (fun i j => {V i (e (a,j))}) (5 * (k+1) + 1) (by
      intro i j
      rw [← hval i (e (a,j))]
      exact tileWordNonzeroG k (M i j) (fun b hb => ⟨i,j,hb⟩))
    refine relax (build_next P Q) le_rfl ?_ ?_
    · rintro b ⟨i,j,rfl⟩
      exact ⟨i,j,rfl⟩
    · have hdet : 2^s * 2^s * (5 * (k+1) + 1) ≤ 6 * tileScale k s := by
        calc
          _ ≤ (2^s * 2^s) * (6 * (k+1)) := Nat.mul_le_mul_left _ (by omega)
          _ = 6 * (2^s * 2^s * (k+1)) := by ac_rfl
          _ ≤ _ := Nat.mul_le_mul_left _ (tileAreaWidth_le k s)
      have hscale : tileScale k s ≤ t * tileScale k s := by
        simpa using Nat.mul_le_mul_right (tileScale k s) (show 1 ≤ t by omega)
      calc
        _ ≤ 1200 * t * tileScale k s + 6 * tileScale k s := Nat.add_le_add_left hdet _
        _ ≤ 1200 * t * tileScale k s + 6 * (t * tileScale k s) :=
          Nat.add_le_add_left (Nat.mul_le_mul_left _ hscale) _
        _ ≤ _ := by rw [Nat.mul_assoc 1200, Nat.mul_assoc 3000]; omega
  have R := finSetsG (fun a : Fin t => {b | ∃ i j, b = V i (e (a,j))}) _ H
  refine relax R le_rfl ?_ ?_
  · rintro b ⟨i,j,rfl⟩
    obtain ⟨⟨a,z⟩, hz⟩ := e.surjective j
    exact ⟨a,i,z,by rw [hz]⟩
  · apply le_of_eq
    dsimp [t, tileScale]
    ring

/-- The bits of common-neighbor counts, formed by multiplying the edge matrix by its transpose. -/
theorem tiledCommonG (k s : Nat) (hs : s ≤ k) {A : Set (Sig n)}
    (edge : Fin (2^s) → Fin (2^k) → Sig n) (he : ∀ i l, edge i l ∈ A) :
    Build A {b | ∃ i j, ∃ u : Fin (k+1), b = fun x =>
      (Finset.univ.filter (fun l => edge i l x = true ∧ edge j l x = true)).card.testBit u.val}
      (3000 * (k+1)^2 * 2^(k-s) * 7^s) := by
  let t := 2^(k-s)
  let e : Fin t × Fin (2^s) ≃ Fin (2^k) := tileIndex k s hs
  have P := tileColumnG k s t (Nat.two_pow_pos _) (fun i l => edge i (e l))
    (fun l j => edge j (e l)) (fun i l => he i (e l)) (fun l j => he j (e l))
  let M (i j : Fin (2^s)) : ProductSignal n k := fun x =>
    ∑ l, wordBool k (edge i l) x * wordBool k (edge j l) x
  have hM : (fun i j x => ∑ l, wordBool k (edge i (e l)) x * wordBool k (edge j (e l)) x) = M := by
    funext i j x
    exact e.sum_comp (fun l => wordBool k (edge i l) x * wordBool k (edge j l) x)
  rw [hM] at P
  refine relax P le_rfl ?_ ?_
  · rintro b ⟨i,j,u,rfl⟩
    refine ⟨i,j,u.val,u.isLt,?_⟩
    funext x
    exact (congrArg (fun c : Nat => c.testBit u.val) (tileCountVal k (edge i) (edge j) x)).symm
  · calc
      _ ≤ 3000 * t * tileScale k s := Nat.mul_le_mul_right _
        (Nat.mul_le_mul_right _ (by decide : 1200 ≤ 3000))
      _ = _ := by dsimp [t, tileScale]; ac_rfl

end TiledProduct

-- Fragment WireFinal.
section WireFinal

lemma realize32566 {k B dim budget : Nat}
    (hdim : 0 < dim)
    (E : Fin B → Fin (2^k) → Sig dim)
    (K : Fin B → Fin B → Fin (k+1) → Sig dim)
    (h : Build (projections dim)
      ({f | ∃ i y, f = E i y} ∪ {f | ∃ i j u, f = K i j u}) budget) :
    ∃ (C : Circuit) (edge : Fin B → Fin (2^k) → Fin (dim+C.size))
      (common : Fin B → Fin B → Fin (k+1) → Fin (dim+C.size)),
      FanInTwo C ∧ ReadsBack dim C ∧ C.output < dim+C.size ∧ C.size ≤ budget ∧
      ∀ x : Fin dim → Bool,
        (∀ i y, (C.wires (List.ofFn x)).getD (edge i y).val false = E i y x) ∧
        ∀ i j u, (C.wires (List.ofFn x)).getD (common i j u).val false = K i j u x := by
  have start : Scheduled dim id 0 (projections dim) :=
    schedStart (fun (i : Fin dim) (x : Fin dim → Bool) => x i) (fun _ _ => rfl)
  obtain ⟨c, hc, hs⟩ := h.run start le_rfl
  rw [Nat.zero_add] at hs
  obtain ⟨gs, hgs, hread, hfan, hw⟩ := hs
  let C : Circuit := ⟨gs, 0⟩
  have hsize : C.size = c := by simp [C, Circuit.size, hgs]
  have wire (f : Sig dim)
      (hf : f ∈ ({f | ∃ i y, f = E i y} ∪ {f | ∃ i j u, f = K i j u} : Set (Sig dim))) :
      ∃ w : Fin (dim+C.size), ∀ x, (C.wires (List.ofFn x)).getD w.val false = f x := by
    obtain ⟨w, hwlt, hwval⟩ := hw f (Or.inr hf)
    exact ⟨⟨w, by simpa only [hsize] using hwlt⟩, hwval⟩
  have he (i : Fin B) (y : Fin (2^k)) := wire (E i y) (Or.inl ⟨i, y, rfl⟩)
  have hk (i j : Fin B) (u : Fin (k+1)) := wire (K i j u) (Or.inr ⟨i, j, u, rfl⟩)
  refine ⟨C, fun i y => Classical.choose (he i y), fun i j u => Classical.choose (hk i j u),
    hfan, hread, ?_, hsize.trans_le hc, fun x => ⟨?_, ?_⟩⟩
  · change 0 < dim + C.size
    omega
  · intro i y
    exact Classical.choose_spec (he i y) x
  · intro i j u
    exact Classical.choose_spec (hk i j u) x

lemma realizeInput32566 {k r B hRow hCol budget : Nat}
    {E : Fin B → Fin (2^k) → Sig (dimOf k r B hRow hCol)}
    {K : Fin B → Fin B → Fin (k+1) → Sig (dimOf k r B hRow hCol)}
    (h : Build (projections (dimOf k r B hRow hCol))
      ({f | ∃ i y, f = E i y} ∪ {f | ∃ i j u, f = K i j u}) budget) :
    let dim := dimOf k r B hRow hCol
    ∃ (C : Circuit) (edge : Fin B → Fin (2^k) → Fin (dim+C.size))
      (common : Fin B → Fin B → Fin (k+1) → Fin (dim+C.size)),
      FanInTwo C ∧ ReadsBack dim C ∧ C.output < dim+C.size ∧ C.size ≤ budget ∧
      ∀ (masks : Nat → Fin (2^k)) (rt : Fin (2^hRow)) (ct : Fin (2^hCol))
        (sample : Fin B → Fin (2^k)) (keep : Fin (2^k) → Bool),
        let x := readInput (r := r) masks rt ct sample keep
        let input := encode (r := r) masks rt ct sample keep
        (∀ i y, (C.wires input).getD (edge i y).val false = E i y x) ∧
        ∀ i j u, (C.wires input).getD (common i j u).val false = K i j u x := by
  have hdim : 0 < dimOf k r B hRow hCol := by
    have := Nat.two_pow_pos k
    dsimp [dimOf]
    omega
  obtain ⟨C, edge, common, hfan, hread, hout, hbudget, hw⟩ := realize32566 hdim E K h
  refine ⟨C, edge, common, hfan, hread, hout, hbudget, ?_⟩
  intro masks rt ct sample keep
  dsimp only
  rw [← readInput_ofFn (r := r) masks rt ct sample keep]
  exact hw _

end WireFinal

-- Fragment Fold.

lemma foldl_agree32566 {α β : Type*} (l : List α) (f g : β → α → β) (z : β)
    (h : ∀ i ∈ l, ∀ a, f a i = g a i) : l.foldl f z = l.foldl g z := by
  induction l generalizing z with
  | nil => rfl
  | cons i l ih =>
    simp only [List.foldl_cons, h i List.mem_cons_self]
    exact ih _ (fun j hj => h j (List.mem_cons_of_mem i hj))

set_option maxHeartbeats 1600000 in
lemma solve32566 : ∀ k r sampleLog hRow hCol : ℕ, k % 2 = 1 → k % 3 ≠ 0 → sampleLog ≤ k → hRow ≤ k → hCol ≤ k →
  let N := 2^k
  let X := Fin N
  let rot := fun (shift x : ℕ) => ((x <<< (shift % k)) ||| (x >>> (k-shift % k))) % N
  let chi := fun (x : ℕ) => (List.range k).foldl (fun (acc i : ℕ) =>
    acc ||| ((xor (x.testBit i) (!(x.testBit ((i+1) % k)) && x.testBit ((i+2) % k))).toNat <<< i)) 0
  let run := fun (masks : ℕ → X) (col : Bool) (key name : ℕ) =>
    let gap : ℕ := if col then 2 else 1
    (List.range r).foldl (fun z j =>
      let mixed := z ^^^ rot gap z ^^^ rot (k-gap % k) z
      chi mixed ^^^ rot (if col then 3*(j+1)+1 else 2*j) key ^^^
        (masks (if col then r+j else j)).val) (rot (if col then 3 else 1) key ^^^ name)
  let bits := fun (len val : ℕ) => (List.range len).map (fun i => val.testBit i)
  let B := 2^sampleLog
  let rowSlots := 2^(k-hRow)
  let colSlots := 2^(k-hCol)
  let blocks := 2^(k-sampleLog)
  let payload := (r+1)*N*(B+colSlots) + N*colSlots*B
  let expandPairs := (r+1)*N*(rowSlots+colSlots) + N*rowSlots*colSlots + B*N
  let multiply := (r+1)*N*(N+B) + blocks^2*7^sampleLog
  let budget := 1048576*(k+1)^3*(min payload (min expandPairs multiply) + blocks*7^sampleLog)
  let dim := 2*r*k+hRow+hCol+B*k+N
  ∃ (C : PEqualNP.CircuitLowerBounds.Circuit) (edge : Fin B → X → Fin (dim+C.size))
    (common : Fin B → Fin B → Fin (k+1) → Fin (dim+C.size)),
    PEqualNP.MetaComplexity.FanInTwo C ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack dim C ∧
    C.output < dim+C.size ∧ C.size ≤ budget ∧
    ∀ (masks : ℕ → X) (rowTarget : Fin (2^hRow)) (colTarget : Fin (2^hCol))
      (sample : Fin B → X) (keep : X → Bool),
      let input := (List.range (2*r)).flatMap (fun j => bits k (masks j).val) ++
        bits hRow rowTarget.val ++ bits hCol colTarget.val ++
        (List.finRange B).flatMap (fun i => bits k (sample i).val) ++ (List.finRange N).map keep
      let adjacent := fun (i : Fin B) (y : X) => keep y = true ∧ ∃ key : X,
        run masks false key.val (sample i).val >>> (k-hRow) = rowTarget.val ∧
        run masks true key.val y.val >>> (k-hCol) = colTarget.val
      let valAt := fun wire : Fin (dim+C.size) => (C.wires input).getD wire.val false
      (∀ i y, valAt (edge i y) = decide (adjacent i y)) ∧
      ∀ i j u, valAt (common i j u) =
        ((Finset.univ.filter (fun y : X => adjacent i y ∧ adjacent j y)).card).testBit u.val := by
  intro k r s hr hc hko hk3 hsk hrk hck N X rot chi run bits B rowSlots colSlots blocks payload expandPairs multiply budget dim
  have hk : 0 < k := by omega
  have hk6 : k%6=1 ∨ k%6=5 := by omega
  let A := initial dim
  let M := maskAt k r B hr hc
  let T := rowAt k r B hr hc
  let U := colAt k r B hr hc
  let S := sampleAt k r B hr hc
  let L := keepAt k r B hr hc
  let F := rowTests (r:=r) (s:=s) hk hrk M T S
  let G := colTests (r:=r) hk hck M U
  let W := witSignal F G
  let E := fun i y => an (L y) (W i y)
  let K := fun (i j : Samples s) (u : Fin (k+1)) (x : Fin dim → Bool) =>
    ((Finset.univ.filter (fun y : X => E i y x = true ∧ E j y x = true)).card).testBit u.val
  let commonSize := blocks*7^s
  let winner := min payload (min expandPairs multiply)
  have hConst (b : Bool) : (fun _ : Fin dim → Bool => b) ∈ A := initial_const b
  have hM : ∀ j i, M j i ∈ A := initial_mask k r B hr hc
  have hT : ∀ i, T i ∈ A := initial_row k r B hr hc
  have hU : ∀ i, U i ∈ A := initial_col k r B hr hc
  have hS : ∀ j i, S j i ∈ A := initial_sample k r B hr hc
  have hL : ∀ y, L y ∈ A := initial_keep k r B hr hc
  have Hpay : Build A (signalGrid W) (routeCost k payload) :=
    payloadWitnessG (r:=r) hk hk6 hrk hck M T U S hM hT hU hS hConst
  have Hexp : Build A (signalGrid W) (routeCost k expandPairs) :=
    expandedWitnessG (r:=r) hk hk6 hsk hrk hck M T U S hM hT hU hS hConst
  have Hmul : Build A (signalGrid W) (routeCost k multiply) := by
    let AF := A ∪ signalGrid F
    let AG := AF ∪ signalGrid G
    have HF : Build A AF (N*B*unitCost k r) := build_keep (build_rowTests hk hrk M T S hM hT hS hConst)
    have HG : Build AF AG (N*N*unitCost k r) := build_keep
      (build_colTests (r:=r) hk hck M U (fun j i => Or.inl (hM j i))
        (fun i => Or.inl (hU i)) (fun b => Or.inl (hConst b)))
    have HP : Build AG (signalGrid W) (3000*(k+1)^2*blocks^2*7^s) :=
      tiledWitnessG k s hsk F G (fun i a => Or.inl (Or.inr ⟨i,a,rfl⟩)) (fun a y => Or.inr ⟨a,y,rfl⟩)
    refine relax (build_next (build_next HF HG) HP) le_rfl le_rfl ?_
    have hUCost := unitCost_le k r
    have hMM : 3000*(k+1)^2 ≤ 10000*(k+1)^3 := by
      calc
        _ ≤ 10000*(k+1)^2 := Nat.mul_le_mul_right _ (by decide)
        _ ≤ _ := by gcongr; omega
    calc
      _ ≤ N*B*((10000*(k+1)^3)*(r+1)) + N*N*((10000*(k+1)^3)*(r+1)) +
        (10000*(k+1)^3)*blocks^2*7^s := by gcongr
      _ = _ := by dsimp [routeCost, multiply]; ring
  have HW : Build A (signalGrid W) (routeCost k winner) := by
    unfold winner
    by_cases h : payload ≤ min expandPairs multiply
    · simpa only [min_eq_left h] using Hpay
    · rw [min_eq_right (by omega : min expandPairs multiply ≤ payload)]
      by_cases g : expandPairs ≤ multiply
      · simpa only [min_eq_left g] using Hexp
      · simpa only [min_eq_right (by omega : multiply ≤ expandPairs)] using Hmul
  let AW := A ∪ signalGrid W
  let AE := AW ∪ signalGrid E
  have HE : Build AW (signalGrid E) (B*N) := by
    have h := gather₂ (fun i y => {E i y}) 1 (fun i y =>
      andG (A:=AW) (Or.inl (hL y)) (Or.inr ⟨i,y,rfl⟩))
    simpa only [Nat.mul_one, signalGrid, Set.mem_singleton_iff] using h
  have HC : Build AE {f | ∃ i j u, f = K i j u} (3000*(k+1)^2*commonSize) := by
    simpa only [commonSize, Nat.mul_assoc] using
      tiledCommonG k s hsk E (A:=AE) (fun i y => Or.inr ⟨i,y,rfl⟩)
  have HA := build_next initial_build (build_keep HW)
  have HAE : Build (projections dim) AE (2 + routeCost k winner + B*N) := build_next HA (build_keep HE)
  have H := seq HAE (relax HC Set.subset_union_right le_rfl le_rfl)
  have hBN : B*N ≤ winner := by
    have hN : 0 < N := Nat.two_pow_pos _
    have hp : B*N ≤ payload := by
      dsimp [payload]
      calc
        B*N = 1*N*B := by ring
        _ ≤ (r+1)*N*(B+colSlots) :=
          Nat.mul_le_mul (Nat.mul_le_mul_right N (by omega)) (Nat.le_add_right _ _)
        _ ≤ _ := Nat.le_add_right _ _
    have hm : B*N ≤ multiply := by
      dsimp [multiply]
      calc
        B*N = 1*N*B := by ring
        _ ≤ (r+1)*N*(N+B) :=
          Nat.mul_le_mul (Nat.mul_le_mul_right N (by omega)) (Nat.le_add_left _ _)
        _ ≤ _ := Nat.le_add_right _ _
    exact le_min hp (le_min (Nat.le_add_left _ _) hm)
  have hP : 0 < B*N := Nat.mul_pos (Nat.two_pow_pos _) (Nat.two_pow_pos _)
  have hW : 1 ≤ winner := hP.trans_le hBN
  have hFactor : 1 ≤ (k+1)^3 := Nat.pow_pos (by omega)
  have hCC : 3000*(k+1)^2*commonSize ≤ 10000*(k+1)^3*commonSize := by
    gcongr
    · decide
    · omega
  have hBudget : 2 + routeCost k winner + B*N + 3000*(k+1)^2*commonSize ≤ budget := by
    calc
      _ ≤ (3*winner + routeCost k winner) + 10000*(k+1)^3*commonSize := by omega
      _ ≤ (3*(k+1)^3*winner + routeCost k winner) + 10000*(k+1)^3*commonSize := by
        gcongr
        exact Nat.le_mul_of_pos_right _ hFactor
      _ ≤ budget := by
        change 3*(k+1)^3*winner + 10000*(k+1)^3*winner + 10000*(k+1)^3*commonSize ≤
          1048576*(k+1)^3*(winner+commonSize)
        nlinarith [Nat.zero_le ((k+1)^3 * winner), Nat.zero_le ((k+1)^3 * commonSize)]
  have Hfin : Build (projections dim) (signalGrid E ∪ {f | ∃ i j u, f = K i j u}) budget :=
    relax H le_rfl (Set.union_subset_union Set.subset_union_right le_rfl) hBudget
  obtain ⟨C, edge, common, hfan, hread, hout, hbudget, hval⟩ := realizeInput32566 Hfin
  refine ⟨C,edge,common,hfan,hread,hout,hbudget,?_⟩
  intro masks rt ct sample keep
  let x := readInput (r:=r) masks rt ct sample keep
  obtain ⟨hm,htr,htc,hs,hl⟩ := readInput_bits (r:=r) masks rt ct sample keep
  have hrun (c : Bool) (a name : X) (z : Word dim k) (hz : ∀ i, z i x = name.val.testBit i.val) :
      wordNat (fwdWord hk r M c a z) x = run masks c a.val name.val := by
    have hName : (fun i => z i x) = ofNat k name.val := funext hz
    have hm' : ∀ j < r, (fun i => M (if c then r+j else j) i x) =
        ofNat k (masks (if c then r+j else j)).val := by
      intro j hj
      funext i
      exact hm _ (by cases c <;> simp <;> omega) i
    have he : runB hk r (fun j i => M j i x) c (ofNat k a.val) (ofNat k name.val) =
        runB hk r (fun j => ofNat k (masks j).val) c (ofNat k a.val) (ofNat k name.val) := by
      unfold runB
      apply foldl_agree32566
      intro j hj w
      have hj' : j < r := List.mem_range.mp hj
      funext i
      dsimp only
      rw [congrFun (hm' j hj') i]
    change toNat (runB hk r (fun j i => M j i x) c (ofNat k a.val) (fun i => z i x)) = _
    rw [hName, he]
    have hb := runB_toNat hk r masks c (ofNat k a.val) (ofNat k name.val)
    rw [toNat_ofNat a.isLt, toNat_ofNat name.isLt] at hb
    exact hb.symm
  have hrt : wordNat T x = rt.val := by
    change toNat (fun i => T i x) = rt.val
    rw [show (fun i => T i x) = ofNat hr rt.val from funext htr, toNat_ofNat rt.isLt]
  have hct : wordNat U x = ct.val := by
    change toNat (fun i => U i x) = ct.val
    rw [show (fun i => U i x) = ofNat hc ct.val from funext htc, toNat_ofNat ct.isLt]
  have hF (i : Samples s) (a : X) : F i a x = true ↔
      run masks false a.val (sample i).val >>> (k-hr) = rt.val := by
    change tableBit hrk (fwdWord hk r M false a (S i)) T x = true ↔ _
    simp only [tableBit, decide_eq_true_eq, prefixWord_shift, hrt, hrun false a (sample i) (S i) (hs i)]
  have hG (a y : X) : G a y x = true ↔
      run masks true a.val y.val >>> (k-hc) = ct.val := by
    change tableBit hck (fwdWord hk r M true a (constWord y)) U x = true ↔ _
    simp only [tableBit, decide_eq_true_eq, prefixWord_shift, hct, hrun true a y (constWord y) (fun _ => rfl)]
  let adjacent := fun (i : Samples s) (y : X) => keep y = true ∧ ∃ a : X,
    run masks false a.val (sample i).val >>> (k-hr) = rt.val ∧
    run masks true a.val y.val >>> (k-hc) = ct.val
  have hE (i : Samples s) (y : X) : E i y x = true ↔ adjacent i y := by
    change (L y x && decide (∃ a : X, F i a x = true ∧ G a y x = true)) = true ↔ _
    simp only [Bool.and_eq_true, decide_eq_true_eq, hF, hG, adjacent, show L y x = keep y from hl y]
  obtain ⟨hvalE,hvalK⟩ := hval masks rt ct sample keep
  refine ⟨?_,?_⟩
  · intro i y
    change (C.wires (encode (r:=r) masks rt ct sample keep)).getD (edge i y).val false = decide (adjacent i y)
    rw [hvalE]
    exact Bool.eq_iff_iff.mpr (by simpa only [decide_eq_true_eq] using hE i y)
  · intro i j u
    change (C.wires (encode (r:=r) masks rt ct sample keep)).getD (common i j u).val false =
      ((Finset.univ.filter (fun y : X => adjacent i y ∧ adjacent j y)).card).testBit u.val
    rw [hvalK]
    have heq : (Finset.univ.filter (fun y : X => E i y x = true ∧ E j y x = true)) =
        Finset.univ.filter (fun y : X => adjacent i y ∧ adjacent j y) := by
      ext y
      simp only [Finset.mem_filter, hE]
    change ((Finset.univ.filter (fun y : X => E i y x = true ∧ E j y x = true)).card).testBit u.val = _
    rw [heq]

end PEqualNP.Outside.L_meta_32566

theorem PEqualNP.Outside.L_meta_32566 : ∀ k r sampleLog hRow hCol : ℕ, k % 2 = 1 → k % 3 ≠ 0 → sampleLog ≤ k → hRow ≤ k → hCol ≤ k →
  let N := 2^k
  let X := Fin N
  let rot := fun (shift x : ℕ) => ((x <<< (shift % k)) ||| (x >>> (k-shift % k))) % N
  let chi := fun (x : ℕ) => (List.range k).foldl (fun (acc i : ℕ) =>
    acc ||| ((xor (x.testBit i) (!(x.testBit ((i+1) % k)) && x.testBit ((i+2) % k))).toNat <<< i)) 0
  let run := fun (masks : ℕ → X) (col : Bool) (key name : ℕ) =>
    let gap : ℕ := if col then 2 else 1
    (List.range r).foldl (fun z j =>
      let mixed := z ^^^ rot gap z ^^^ rot (k-gap % k) z
      chi mixed ^^^ rot (if col then 3*(j+1)+1 else 2*j) key ^^^
        (masks (if col then r+j else j)).val) (rot (if col then 3 else 1) key ^^^ name)
  let bits := fun (len val : ℕ) => (List.range len).map (fun i => val.testBit i)
  let B := 2^sampleLog
  let rowSlots := 2^(k-hRow)
  let colSlots := 2^(k-hCol)
  let blocks := 2^(k-sampleLog)
  let payload := (r+1)*N*(B+colSlots) + N*colSlots*B
  let expandPairs := (r+1)*N*(rowSlots+colSlots) + N*rowSlots*colSlots + B*N
  let multiply := (r+1)*N*(N+B) + blocks^2*7^sampleLog
  let budget := 1048576*(k+1)^3*(min payload (min expandPairs multiply) + blocks*7^sampleLog)
  let dim := 2*r*k+hRow+hCol+B*k+N
  ∃ (C : PEqualNP.CircuitLowerBounds.Circuit) (edge : Fin B → X → Fin (dim+C.size))
    (common : Fin B → Fin B → Fin (k+1) → Fin (dim+C.size)),
    PEqualNP.MetaComplexity.FanInTwo C ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack dim C ∧
    C.output < dim+C.size ∧ C.size ≤ budget ∧
    ∀ (masks : ℕ → X) (rowTarget : Fin (2^hRow)) (colTarget : Fin (2^hCol))
      (sample : Fin B → X) (keep : X → Bool),
      let input := (List.range (2*r)).flatMap (fun j => bits k (masks j).val) ++
        bits hRow rowTarget.val ++ bits hCol colTarget.val ++
        (List.finRange B).flatMap (fun i => bits k (sample i).val) ++ (List.finRange N).map keep
      let adjacent := fun (i : Fin B) (y : X) => keep y = true ∧ ∃ key : X,
        run masks false key.val (sample i).val >>> (k-hRow) = rowTarget.val ∧
        run masks true key.val y.val >>> (k-hCol) = colTarget.val
      let valAt := fun wire : Fin (dim+C.size) => (C.wires input).getD wire.val false
      (∀ i y, valAt (edge i y) = decide (adjacent i y)) ∧
      ∀ i j u, valAt (common i j u) =
        ((Finset.univ.filter (fun y : X => adjacent i y ∧ adjacent j y)).card).testBit u.val :=
  PEqualNP.Outside.L_meta_32566.solve32566
