import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_32053

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

section TopDSec

def IsTopD (D N : Nat) (A : Finset Nat) (L : Nat → Nat) : Prop :=
  (∀ j < D, L j ≤ N) ∧
  (∀ i j, i < j → j < D → L i ≤ L j ∧ (L i < N → L i < L j)) ∧
  (∀ j < D, L j < N → L j ∈ A) ∧
  (∀ y ∈ A, (∃ j < D, L j = y) ∨ (∀ j < D, L j < y))

theorem IsTopD_congr {D N : Nat} {A : Finset Nat} {L1 L2 : Nat → Nat}
    (h : IsTopD D N A L1) (heq : ∀ j < D, L1 j = L2 j) : IsTopD D N A L2 := by
  rcases h with ⟨h1, h2, h3, h4⟩
  refine ⟨fun j hj => by rw [← heq j hj]; exact h1 j hj,
    fun i j hij hj => by rw [← heq i (by omega), ← heq j hj]; exact h2 i j hij hj,
    fun j hj => by rw [← heq j hj]; exact h3 j hj,
    fun y hy => ?_⟩
  rcases h4 y hy with ⟨j, hj, rfl⟩ | hall
  · exact Or.inl ⟨j, hj, (heq j hj).symm⟩
  · exact Or.inr (fun j hj => by rw [← heq j hj]; exact hall j hj)

theorem IsTopD_uniq {D N : Nat} {A : Finset Nat} {L1 L2 : Nat → Nat}
    (h1 : IsTopD D N A L1) (h2 : IsTopD D N A L2) : ∀ j < D, L1 j = L2 j := by
  have hle : ∀ {X Y : Nat → Nat}, IsTopD D N A X → IsTopD D N A Y →
      ∀ j < D, (∀ i < j, X i = Y i) → ¬ (X j < Y j) := by
    intro X Y hX hY j hj hprev hlt
    have hXjN : X j < N := lt_of_lt_of_le hlt (hY.1 j hj)
    have hmem : X j ∈ A := hX.2.2.1 j hj hXjN
    rcases hY.2.2.2 (X j) hmem with ⟨i, hi, hYi⟩ | hall
    · by_cases hij : i < j
      · have hXi : X i = X j := (hprev i hij).trans hYi
        have hst := (hX.2.1 i j hij hj).2 (by omega)
        omega
      · by_cases heq : i = j
        · subst heq; omega
        · have hji : j < i := by omega
          have hord := (hY.2.1 j i hji hi).1
          omega
    · have := hall j hj
      omega
  intro j
  induction j using Nat.strong_induction_on with
  | ind j ih =>
    intro hj
    have hprev : ∀ i < j, L1 i = L2 i := fun i hi => ih i hi (by omega)
    have hnot1 : ¬ (L1 j < L2 j) := hle h1 h2 j hj hprev
    have hnot2 : ¬ (L2 j < L1 j) := hle h2 h1 j hj (fun i hi => (hprev i hi).symm)
    omega

theorem IsTopD_empty (D N : Nat) : IsTopD D N ∅ (fun _ => N) :=
  ⟨fun _ _ => le_rfl, fun _ _ _ _ => ⟨le_rfl, fun h => absurd h (Nat.lt_irrefl N)⟩,
   fun _ _ h => absurd h (Nat.lt_irrefl N), fun _ hy => absurd hy (Finset.notMem_empty _)⟩

theorem IsTopD_of_sorted_distinct (D N s : Nat) (A : Finset Nat) (arr : Nat → Nat)
    (hbound : ∀ i < 2 ^ s, arr i ≤ N)
    (hdist : ∀ i < 2 ^ s, ∀ j < 2 ^ s, arr i < N → arr i = arr j → i = j)
    (hmem : ∀ y, y ∈ A ↔ ∃ i < 2 ^ s, arr i = y ∧ y < N) :
    let sorted := runNet id (bitonicSort 0 s true) arr
    IsTopD D N A (fun j => if j < 2 ^ s then sorted j else N) := by
  intro sorted
  let net := bitonicSort 0 s true
  have hnet : ∀ c ∈ net, c.1 < 2 ^ s ∧ c.2.1 < 2 ^ s := fun c hc => by
    have hm := bitonicSort_mem 0 s true c hc; omega
  have hsorted : ∀ i j, i ≤ j → j < 2 ^ s → sorted i ≤ sorted j :=
    bitonicSort_sorted id s arr
  have hall_le : ∀ i < 2 ^ s, sorted i ≤ N := all_runNet id (2 ^ s) net hnet arr (· ≤ N) hbound
  have hcount : ∀ v, ((Finset.range (2 ^ s)).filter (fun i => sorted i = v)).card =
      ((Finset.range (2 ^ s)).filter (fun i => arr i = v)).card := fun v =>
    count_runNet id (2 ^ s) net hnet arr (· = v)
  have hcard_le1 : ∀ v < N, ((Finset.range (2 ^ s)).filter (fun i => sorted i = v)).card ≤ 1 := by
    intro v hv
    rw [hcount v, Finset.card_le_one]
    intro i hi j hj
    simp only [Finset.mem_filter, Finset.mem_range] at hi hj
    exact hdist i hi.1 j hj.1 (by omega) (hi.2.trans hj.2.symm)
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro j _
    by_cases hj : j < 2 ^ s
    · simp only [hj, ↓reduceIte]; exact hall_le j hj
    · simp only [hj, ↓reduceIte]; exact le_rfl
  · intro i j hij _
    by_cases hjS : j < 2 ^ s
    · have hiS : i < 2 ^ s := by omega
      simp only [hiS, hjS, ↓reduceIte]
      have hle := hsorted i j (by omega) hjS
      refine ⟨hle, fun hlt => ?_⟩
      by_contra hge
      have heq : sorted i = sorted j := by omega
      have hsub : ({i, j} : Finset Nat) ⊆ (Finset.range (2 ^ s)).filter (fun idx => sorted idx = sorted i) := by
        intro t ht
        simp only [Finset.mem_insert, Finset.mem_singleton] at ht
        rcases ht with rfl | rfl
        · exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hiS, rfl⟩
        · exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hjS, heq.symm⟩
      have h2 : 2 ≤ ((Finset.range (2 ^ s)).filter (fun idx => sorted idx = sorted i)).card := by
        have hc := Finset.card_le_card hsub
        rw [Finset.card_pair (by omega)] at hc
        exact hc
      have h1 := hcard_le1 (sorted i) hlt
      omega
    · by_cases hiS : i < 2 ^ s
      · simp only [hiS, hjS, ↓reduceIte]
        exact ⟨hall_le i hiS, fun hlt => hlt⟩
      · simp only [hiS, hjS, ↓reduceIte]
        exact ⟨le_rfl, fun h => absurd h (Nat.lt_irrefl N)⟩
  · intro j _ hlt
    by_cases hjS : j < 2 ^ s
    · simp only [hjS, ↓reduceIte] at hlt ⊢
      have hpos : 0 < ((Finset.range (2 ^ s)).filter (fun idx => sorted idx = sorted j)).card :=
        Finset.card_pos.mpr ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hjS, rfl⟩⟩
      rw [hcount] at hpos
      obtain ⟨i, hi⟩ := Finset.card_pos.mp hpos
      simp only [Finset.mem_filter, Finset.mem_range] at hi
      exact (hmem (sorted j)).mpr ⟨i, hi.1, hi.2, hlt⟩
    · simp only [hjS, ↓reduceIte] at hlt
      exact absurd hlt (Nat.lt_irrefl N)
  · intro y hy
    obtain ⟨i0, hi0, hval, hyN⟩ := (hmem y).mp hy
    have hpos : 0 < ((Finset.range (2 ^ s)).filter (fun idx => sorted idx = y)).card := by
      rw [hcount]
      exact Finset.card_pos.mpr ⟨i0, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hi0, hval⟩⟩
    obtain ⟨idx, hidx⟩ := Finset.card_pos.mp hpos
    simp only [Finset.mem_filter, Finset.mem_range] at hidx
    by_cases hidxD : idx < D
    · left
      exact ⟨idx, hidxD, by simp [hidx.1, hidx.2]⟩
    · right
      intro j hj
      have hjS : j < 2 ^ s := by omega
      simp only [hjS, ↓reduceIte]
      have hle := hsorted j idx (by omega) hidx.1
      by_contra hge
      have heq : sorted j = y := by omega
      have hsub : ({j, idx} : Finset Nat) ⊆ (Finset.range (2 ^ s)).filter (fun t => sorted t = y) := by
        intro t ht
        simp only [Finset.mem_insert, Finset.mem_singleton] at ht
        rcases ht with rfl | rfl
        · exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hjS, heq⟩
        · exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hidx.1, hidx.2⟩
      have h2 : 2 ≤ ((Finset.range (2 ^ s)).filter (fun t => sorted t = y)).card := by
        have hc := Finset.card_le_card hsub
        rw [Finset.card_pair (by omega)] at hc
        exact hc
      have h1 := hcard_le1 y hyN
      omega

theorem IsTopD_nonempty_iff {D N : Nat} {A : Finset Nat} {L : Nat → Nat}
    (hD : 0 < D) (hA : ∀ y ∈ A, y < N) (hL : IsTopD D N A L) :
    A.Nonempty ↔ L 0 < N := by
  constructor
  · rintro ⟨y, hy⟩
    have hyN := hA y hy
    rcases hL.2.2.2 y hy with ⟨j, hj, hLj⟩ | hall
    · by_cases hj0 : j = 0
      · subst hj0; omega
      · have hle := (hL.2.1 0 j (by omega) hj).1; omega
    · exact lt_trans (hall 0 hD) hyN
  · intro h0
    exact ⟨L 0, hL.2.2.1 0 hD h0⟩

theorem IsTopD_card_le_iff {d N : Nat} {A : Finset Nat} {L : Nat → Nat}
    (hA : ∀ y ∈ A, y < N) (hL : IsTopD (d + 1) N A L) :
    A.card ≤ d ↔ L d = N := by
  constructor
  · intro hcard
    by_contra hne
    have hlt : L d < N := lt_of_le_of_ne (hL.1 d (by omega)) hne
    have hsub : (Finset.range (d + 1)).image L ⊆ A := by
      intro y hy
      rcases Finset.mem_image.mp hy with ⟨j, hj, rfl⟩
      have hj' : j < d + 1 := Finset.mem_range.mp hj
      have hjN : L j < N := by
        by_cases hjd : j = d
        · subst hjd; exact hlt
        · exact lt_of_le_of_lt (hL.2.1 j d (by omega) (by omega)).1 hlt
      exact hL.2.2.1 j hj' hjN
    have hinj : Set.InjOn L (Finset.range (d + 1) : Set Nat) := by
      intro i hi j hj heq
      have hi' : i < d + 1 := Finset.mem_range.mp hi
      have hj' : j < d + 1 := Finset.mem_range.mp hj
      by_contra hne'
      rcases Nat.lt_or_gt_of_ne hne' with h | h
      · have hiN : L i < N := lt_of_le_of_lt (hL.2.1 i d (by omega) (by omega)).1 hlt
        have := (hL.2.1 i j h hj').2 hiN
        omega
      · have hjN : L j < N := lt_of_le_of_lt (hL.2.1 j d (by omega) (by omega)).1 hlt
        have := (hL.2.1 j i h hi').2 hjN
        omega
    have h1 := Finset.card_le_card hsub
    rw [Finset.card_image_of_injOn hinj, Finset.card_range] at h1
    omega
  · intro hLd
    have hsub : A ⊆ (Finset.range d).image L := by
      intro y hy
      have hyN := hA y hy
      rcases hL.2.2.2 y hy with ⟨j, hj, hLj⟩ | hall
      · have hjd : j < d := by
          by_contra hge
          have heq : j = d := by omega
          subst heq; omega
        exact Finset.mem_image.mpr ⟨j, Finset.mem_range.mpr hjd, hLj⟩
      · have := hall d (by omega); omega
    exact (Finset.card_le_card hsub).trans (Finset.card_image_le.trans (by rw [Finset.card_range]))

theorem IsTopD_eq_iff {d N : Nat} {A B : Finset Nat} {L1 L2 : Nat → Nat}
    (hA : ∀ y ∈ A, y < N) (hB : ∀ y ∈ B, y < N)
    (h1 : IsTopD (d + 1) N A L1) (h2 : IsTopD (d + 1) N B L2) (hcard : A.card ≤ d) :
    (∀ j < d + 1, L1 j = L2 j) ↔ A = B := by
  constructor
  · intro heq
    have hLd1 : L1 d = N := (IsTopD_card_le_iff hA h1).mp hcard
    have hLd2 : L2 d = N := by rw [← heq d (by omega), hLd1]
    ext y
    constructor
    · intro hy
      have hyN := hA y hy
      rcases h1.2.2.2 y hy with ⟨j, hj, hLj⟩ | hall
      · rw [heq j hj] at hLj
        rw [← hLj]
        exact h2.2.2.1 j hj (by omega)
      · have := hall d (by omega); omega
    · intro hy
      have hyN := hB y hy
      rcases h2.2.2.2 y hy with ⟨j, hj, hLj⟩ | hall
      · rw [← heq j hj] at hLj
        rw [← hLj]
        exact h1.2.2.1 j hj (by omega)
      · have := hall d (by omega); omega
  · rintro rfl
    exact IsTopD_uniq h1 h2

def ceilLog2 (D : Nat) : Nat :=
  if D ≤ 1 then 0 else Nat.log2 (D - 1) + 1

theorem ceilLog2_spec {D : Nat} (hD : 1 ≤ D) :
    D ≤ 2 ^ ceilLog2 D ∧ 2 ^ ceilLog2 D ≤ 2 * D := by
  by_cases h1 : D ≤ 1
  · simp [ceilLog2, h1]; omega
  · simp only [ceilLog2, h1, ↓reduceIte]
    have hne : D - 1 ≠ 0 := by omega
    have hlt := Nat.lt_log2_self (n := D - 1)
    have hle := Nat.log2_self_le hne
    rw [Nat.pow_succ]
    omega

theorem ceilLog2_le {k D : Nat} (hD : D ≤ 2 ^ k + 1) :
    ceilLog2 D ≤ k + 1 := by
  by_cases h1 : D ≤ 1
  · simp [ceilLog2, h1]
  · simp only [ceilLog2, h1, ↓reduceIte]
    have hne : D - 1 ≠ 0 := by omega
    have hle := Nat.log2_self_le hne
    by_contra hgt
    have hge : k + 1 ≤ Nat.log2 (D - 1) := by omega
    have hp := Nat.pow_le_pow_right Nat.zero_lt_two hge
    rw [Nat.pow_succ] at hp
    have hpos := Nat.two_pow_pos k
    omega

def sentBit (k b : Nat) : Bool := decide (b = k)

theorem bitsVal_sentBit (k : Nat) : bitsVal (sentBit k) (k + 1) = 2 ^ k := by
  have h0 : ∀ m ≤ k, bitsVal (sentBit k) m = 0 := by
    intro m
    induction m with
    | zero => intro _; rfl
    | succ m ih =>
      intro hm
      simp only [bitsVal, sentBit, show m ≠ k by omega, decide_false, Bool.false_eq_true, ↓reduceIte,
        Nat.add_zero]
      exact ih (by omega)
  simp only [bitsVal, h0 k le_rfl, sentBit, decide_true, ↓reduceIte, Nat.zero_add]

def mergeRawRec (k D q : Nat) (A B : Nat → Nat → Bool) (idx : Nat) : Rec :=
  (if idx < D then A idx
   else if 2 ^ q ≤ idx ∧ idx < 2 ^ q + D then B (idx - 2 ^ q)
   else sentBit k,
   fun _ => false)

def mergeDedupRec (k : Nat) (uRec : Nat → Rec) (idx : Nat) : Rec :=
  let isDup := decide (0 < idx) && decide (recKey (k + 1) (uRec idx) = recKey (k + 1) (uRec (idx - 1)))
  (fun b => if isDup then sentBit k b else (uRec idx).1 b, fun _ => false)

def mergeTruncBits (k D q : Nat) (A B : Nat → Nat → Bool) : Nat → Nat → Bool :=
  let net := bitonicSort 0 (q + 1) true
  let uRec := runNet (recKey (k + 1)) net (mergeRawRec k D q A B)
  let vRec := runNet (recKey (k + 1)) net (mergeDedupRec k uRec)
  fun j b => (vRec j).1 b

theorem IsTopD_mergeTrunc (k D q : Nat) (hDq : D ≤ 2 ^ q)
    (S1 S2 : Finset Nat) (hS1 : ∀ y ∈ S1, y < 2 ^ k) (hS2 : ∀ y ∈ S2, y < 2 ^ k)
    (A B : Nat → Nat → Bool)
    (h1 : IsTopD D (2 ^ k) S1 (fun j => bitsVal (A j) (k + 1)))
    (h2 : IsTopD D (2 ^ k) S2 (fun j => bitsVal (B j) (k + 1))) :
    IsTopD D (2 ^ k) (S1 ∪ S2) (fun j => bitsVal (mergeTruncBits k D q A B j) (k + 1)) := by
  let N := 2 ^ k
  let P := 2 ^ (q + 1)
  have hP : P = 2 ^ q + 2 ^ q := by dsimp [P]; rw [Nat.pow_succ]; omega
  let net := bitonicSort 0 (q + 1) true
  have hnet : ∀ c ∈ net, c.1 < P ∧ c.2.1 < P := fun c hc => by
    have hm := bitonicSort_mem 0 (q + 1) true c hc; omega
  let raw := mergeRawRec k D q A B
  let uRec := runNet (recKey (k + 1)) net raw
  let ded := mergeDedupRec k uRec
  let vRec := runNet (recKey (k + 1)) net ded
  let rk := recKey (k + 1)
  have hraw_le : ∀ idx < P, rk (raw idx) ≤ N := by
    intro idx _
    dsimp only [rk, recKey, raw, mergeRawRec]
    by_cases c1 : idx < D
    · simp only [c1, ↓reduceIte]; exact h1.1 idx c1
    · by_cases c2 : 2 ^ q ≤ idx ∧ idx < 2 ^ q + D
      · simp only [c1, c2, ↓reduceIte]; exact h2.1 (idx - 2 ^ q) (by omega)
      · simp only [c1, c2, ↓reduceIte]; exact le_of_eq (bitsVal_sentBit k)
  have hu_le : ∀ idx < P, rk (uRec idx) ≤ N := all_runNet rk P net hnet raw (fun r => rk r ≤ N) hraw_le
  have hu_sorted : ∀ i j, i ≤ j → j < P → rk (uRec i) ≤ rk (uRec j) :=
    bitonicSort_sorted rk (q + 1) raw
  have hded_val : ∀ idx, rk (ded idx) =
      if 0 < idx ∧ rk (uRec idx) = rk (uRec (idx - 1)) then N else rk (uRec idx) := by
    intro idx
    by_cases hd : 0 < idx ∧ rk (uRec idx) = rk (uRec (idx - 1))
    · have ht : (decide (0 < idx) && decide (recKey (k + 1) (uRec idx) = recKey (k + 1) (uRec (idx - 1)))) = true := by
        simp [hd.1, hd.2, rk]
      simp only [hd]
      change bitsVal (fun b => if (decide (0 < idx) && decide (recKey (k + 1) (uRec idx) = recKey (k + 1) (uRec (idx - 1)))) = true then sentBit k b else (uRec idx).1 b) (k + 1) = N
      simp only [ht, ↓reduceIte]
      exact bitsVal_sentBit k
    · have hf : (decide (0 < idx) && decide (recKey (k + 1) (uRec idx) = recKey (k + 1) (uRec (idx - 1)))) = false := by
        cases h1' : decide (0 < idx) <;> cases h2' : decide (recKey (k + 1) (uRec idx) = recKey (k + 1) (uRec (idx - 1)))
        · rfl
        · rfl
        · rfl
        · exfalso; apply hd; exact ⟨of_decide_eq_true h1', of_decide_eq_true h2'⟩
      simp only [hd]
      change bitsVal (fun b => if (decide (0 < idx) && decide (recKey (k + 1) (uRec idx) = recKey (k + 1) (uRec (idx - 1)))) = true then sentBit k b else (uRec idx).1 b) (k + 1) = _
      simp only [hf, Bool.false_eq_true, ↓reduceIte]
      rfl
  have hded_le : ∀ idx < P, rk (ded idx) ≤ N := by
    intro idx hidx
    rw [hded_val idx]
    split
    · exact le_rfl
    · exact hu_le idx hidx
  have hv_le : ∀ idx < P, rk (vRec idx) ≤ N := all_runNet rk P net hnet ded (fun r => rk r ≤ N) hded_le
  have hv_sorted : ∀ i j, i ≤ j → j < P → rk (vRec i) ≤ rk (vRec j) :=
    bitonicSort_sorted rk (q + 1) ded
  have hcount_u : ∀ v, ((Finset.range P).filter (fun i => rk (uRec i) = v)).card =
      ((Finset.range P).filter (fun i => rk (raw i) = v)).card := fun v =>
    count_runNet rk P net hnet raw (fun r => rk r = v)
  have hcount_v : ∀ v, ((Finset.range P).filter (fun i => rk (vRec i) = v)).card =
      ((Finset.range P).filter (fun i => rk (ded i) = v)).card := fun v =>
    count_runNet rk P net hnet ded (fun r => rk r = v)
  have hded_card_le1 : ∀ v < N, ((Finset.range P).filter (fun i => rk (ded i) = v)).card ≤ 1 := by
    intro v hv
    rw [Finset.card_le_one]
    intro i hi j hj
    simp only [Finset.mem_filter, Finset.mem_range] at hi hj
    rw [hded_val i] at hi
    rw [hded_val j] at hj
    have hni : ¬ (0 < i ∧ rk (uRec i) = rk (uRec (i - 1))) := by
      intro hc; rw [ite_eq_left_of_eq_true _ _ (eq_true hc)] at hi; omega
    have hnj : ¬ (0 < j ∧ rk (uRec j) = rk (uRec (j - 1))) := by
      intro hc; rw [ite_eq_left_of_eq_true _ _ (eq_true hc)] at hj; omega
    simp only [hni, ↓reduceIte] at hi
    simp only [hnj, ↓reduceIte] at hj
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
    · apply hnj
      refine ⟨by omega, ?_⟩
      have ha := hu_sorted i (j - 1) (by omega) (by omega)
      have hb := hu_sorted (j - 1) j (by omega) hj.1
      omega
    · apply hni
      refine ⟨by omega, ?_⟩
      have ha := hu_sorted j (i - 1) (by omega) (by omega)
      have hb := hu_sorted (i - 1) i (by omega) hi.1
      omega
  have hex_v_iff : ∀ v < N, (∃ i < P, rk (vRec i) = v) ↔ (∃ i < P, rk (raw i) = v) := by
    intro v hv
    constructor
    · rintro ⟨i, hi, hvi⟩
      have hpos : 0 < ((Finset.range P).filter (fun t => rk (vRec t) = v)).card :=
        Finset.card_pos.mpr ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hi, hvi⟩⟩
      rw [hcount_v] at hpos
      obtain ⟨j, hj⟩ := Finset.card_pos.mp hpos
      simp only [Finset.mem_filter, Finset.mem_range] at hj
      rw [hded_val j] at hj
      have hnj : ¬ (0 < j ∧ rk (uRec j) = rk (uRec (j - 1))) := by
        intro hc; rw [ite_eq_left_of_eq_true _ _ (eq_true hc)] at hj; omega
      simp only [hnj, ↓reduceIte] at hj
      have hposu : 0 < ((Finset.range P).filter (fun t => rk (uRec t) = v)).card :=
        Finset.card_pos.mpr ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hj.1, hj.2⟩⟩
      rw [hcount_u] at hposu
      obtain ⟨r, hr⟩ := Finset.card_pos.mp hposu
      simp only [Finset.mem_filter, Finset.mem_range] at hr
      exact ⟨r, hr.1, hr.2⟩
    · rintro ⟨r, hr, hrv⟩
      have hposu : 0 < ((Finset.range P).filter (fun t => rk (uRec t) = v)).card := by
        rw [hcount_u]
        exact Finset.card_pos.mpr ⟨r, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hr, hrv⟩⟩
      have hex_u : ∃ j, j < P ∧ rk (uRec j) = v := by
        obtain ⟨j, hj⟩ := Finset.card_pos.mp hposu
        simp only [Finset.mem_filter, Finset.mem_range] at hj
        exact ⟨j, hj.1, hj.2⟩
      let j0 := Nat.find hex_u
      have hj0 := Nat.find_spec hex_u
      have hmin : ¬ (0 < j0 ∧ rk (uRec j0) = rk (uRec (j0 - 1))) := by
        rintro ⟨hpos0, heq0⟩
        have hlt0 : j0 - 1 < j0 := by omega
        exact Nat.find_min hex_u hlt0 ⟨by omega, heq0.symm.trans hj0.2⟩
      have hded0 : rk (ded j0) = v := by
        rw [hded_val j0]; simp only [hmin, ↓reduceIte]; exact hj0.2
      have hposv : 0 < ((Finset.range P).filter (fun t => rk (vRec t) = v)).card := by
        rw [hcount_v]
        exact Finset.card_pos.mpr ⟨j0, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hj0.1, hded0⟩⟩
      obtain ⟨i, hi⟩ := Finset.card_pos.mp hposv
      simp only [Finset.mem_filter, Finset.mem_range] at hi
      exact ⟨i, hi.1, hi.2⟩
  have hraw_mem : ∀ v < N, (∃ i < P, rk (raw i) = v) ↔
      (∃ j < D, bitsVal (A j) (k + 1) = v) ∨ (∃ j < D, bitsVal (B j) (k + 1) = v) := by
    intro v hv
    constructor
    · rintro ⟨i, hi, hri⟩
      dsimp only [rk, recKey, raw, mergeRawRec] at hri
      by_cases c1 : i < D
      · simp only [c1, ↓reduceIte] at hri; exact Or.inl ⟨i, c1, hri⟩
      · by_cases c2 : 2 ^ q ≤ i ∧ i < 2 ^ q + D
        · simp only [c1, c2, ↓reduceIte] at hri; exact Or.inr ⟨i - 2 ^ q, by omega, hri⟩
        · simp only [c1, c2, ↓reduceIte] at hri; rw [bitsVal_sentBit] at hri; omega
    · rintro (⟨j, hj, hAj⟩ | ⟨j, hj, hBj⟩)
      · refine ⟨j, by omega, ?_⟩
        dsimp only [rk, recKey, raw, mergeRawRec]; simp [hj, hAj]
      · refine ⟨2 ^ q + j, by omega, ?_⟩
        dsimp only [rk, recKey, raw, mergeRawRec]
        have h1' : ¬ (2 ^ q + j < D) := by omega
        have h2' : 2 ^ q ≤ 2 ^ q + j ∧ 2 ^ q + j < 2 ^ q + D := by omega
        simp only [h1', h2', ↓reduceIte, Nat.add_sub_cancel_left]
        exact hBj
  change IsTopD D N (S1 ∪ S2) (fun j => rk (vRec j))
  refine ⟨fun j hj => hv_le j (by omega), ?_, ?_, ?_⟩
  · intro i j hij hjD
    dsimp only
    have hle := hv_sorted i j (by omega) (by omega)
    refine ⟨hle, fun hlt => ?_⟩
    by_contra hge
    have heq : rk (vRec i) = rk (vRec j) := by omega
    have hsub : ({i, j} : Finset Nat) ⊆ (Finset.range P).filter (fun t => rk (vRec t) = rk (vRec i)) := by
      intro t ht
      simp only [Finset.mem_insert, Finset.mem_singleton] at ht
      rcases ht with rfl | rfl
      · exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), rfl⟩
      · exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), heq.symm⟩
    have h2' : 2 ≤ ((Finset.range P).filter (fun t => rk (vRec t) = rk (vRec i))).card := by
      have hc := Finset.card_le_card hsub
      rw [Finset.card_pair (by omega)] at hc; exact hc
    rw [hcount_v] at h2'
    have h1' := hded_card_le1 (rk (vRec i)) hlt
    omega
  · intro j hjD hlt
    dsimp only at hlt ⊢
    have hex := (hex_v_iff (rk (vRec j)) hlt).mp ⟨j, by omega, rfl⟩
    rcases (hraw_mem (rk (vRec j)) hlt).mp hex with ⟨t, ht, hAt⟩ | ⟨t, ht, hBt⟩
    · rw [← hAt]; exact Finset.mem_union_left _ (h1.2.2.1 t ht (by dsimp only; omega))
    · rw [← hBt]; exact Finset.mem_union_right _ (h2.2.2.1 t ht (by dsimp only; omega))
  · have hside : ∀ (L : Nat → Nat) (S : Finset Nat),
        (∀ y ∈ S, y < N) → IsTopD D N S L →
        (∀ j < D, L j < N → ∃ i < P, rk (raw i) = L j) →
        ∀ y ∈ S, (∃ j < D, rk (vRec j) = y) ∨ (∀ j < D, rk (vRec j) < y) := by
      intro L S hSN hL hLin y hy
      have hyN : y < N := hSN y hy
      rcases hL.2.2.2 y hy with ⟨j0, hj0, hLj0⟩ | hall
      · obtain ⟨idx, hidx, hvidx⟩ := (hex_v_iff y hyN).mpr (by rw [← hLj0]; exact hLin j0 hj0 (by omega))
        by_cases hidxD : idx < D
        · exact Or.inl ⟨idx, hidxD, hvidx⟩
        · right
          intro j hjD
          have hle := hv_sorted j idx (by omega) hidx
          by_contra hge
          have heq : rk (vRec j) = y := by omega
          have hsub : ({j, idx} : Finset Nat) ⊆ (Finset.range P).filter (fun t => rk (vRec t) = y) := by
            intro t ht
            simp only [Finset.mem_insert, Finset.mem_singleton] at ht
            rcases ht with rfl | rfl
            · exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), heq⟩
            · exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hidx, hvidx⟩
          have h2' : 2 ≤ ((Finset.range P).filter (fun t => rk (vRec t) = y)).card := by
            have hc := Finset.card_le_card hsub
            rw [Finset.card_pair (by omega)] at hc; exact hc
          rw [hcount_v] at h2'
          have h1' := hded_card_le1 y hyN
          omega
      · right
        have hvals : (Finset.range D).image L ⊆ ((Finset.range P).filter (fun i => rk (vRec i) < y)).image (fun i => rk (vRec i)) := by
          intro z hz
          rcases Finset.mem_image.mp hz with ⟨t, ht, rfl⟩
          have htD : t < D := Finset.mem_range.mp ht
          have hty : L t < y := hall t htD
          obtain ⟨idx, hidx, hvidx⟩ := (hex_v_iff (L t) (by omega)).mpr (hLin t htD (by omega))
          exact Finset.mem_image.mpr ⟨idx, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hidx, by omega⟩, hvidx⟩
        have hinj : Set.InjOn L (Finset.range D : Set Nat) := by
          intro a ha b hb heq
          have ha' : a < D := Finset.mem_range.mp ha
          have hb' : b < D := Finset.mem_range.mp hb
          by_contra hne
          rcases Nat.lt_or_gt_of_ne hne with h | h
          · have := (hL.2.1 a b h hb').2 (lt_trans (hall a ha') hyN); omega
          · have := (hL.2.1 b a h ha').2 (lt_trans (hall b hb') hyN); omega
        have hcardD : D ≤ ((Finset.range P).filter (fun i => rk (vRec i) < y)).card := by
          calc D = ((Finset.range D).image L).card := by
                rw [Finset.card_image_of_injOn hinj, Finset.card_range]
            _ ≤ (((Finset.range P).filter (fun i => rk (vRec i) < y)).image (fun i => rk (vRec i))).card :=
                Finset.card_le_card hvals
            _ ≤ ((Finset.range P).filter (fun i => rk (vRec i) < y)).card := Finset.card_image_le
        intro j hjD
        by_contra hge
        have hsub : (Finset.range P).filter (fun i => rk (vRec i) < y) ⊆ Finset.range j := by
          intro i hi
          simp only [Finset.mem_filter, Finset.mem_range] at hi ⊢
          by_contra hij
          have := hv_sorted j i (by omega) hi.1
          omega
        have hc := Finset.card_le_card hsub
        rw [Finset.card_range] at hc
        omega
    intro y hy
    rcases Finset.mem_union.mp hy with hy1 | hy2
    · exact hside _ S1 hS1 h1 (fun j hj hlt => (hraw_mem _ hlt).mpr (Or.inl ⟨j, hj, rfl⟩)) y hy1
    · exact hside _ S2 hS2 h2 (fun j hj hlt => (hraw_mem _ hlt).mpr (Or.inr ⟨j, hj, rfl⟩)) y hy2

theorem mergeTruncG {n : Nat} {S : Set (Sig n)} (k D q : Nat) (hDq : D ≤ 2 ^ q)
    (A B : (Fin n → Bool) → Nat → Nat → Bool)
    (hA : ∀ j < D, ∀ b < k + 1, (fun v => A v j b) ∈ S)
    (hB : ∀ j < D, ∀ b < k + 1, (fun v => B v j b) ∈ S)
    (hfalse : (fun _ => false) ∈ S) (htrue : (fun _ => true) ∈ S) :
    Build S {f | ∃ j < D, ∃ b < k + 1, f = fun v => mergeTruncBits k D q (A v) (B v) j b}
      (2 * (bitonicSort 0 (q + 1) true).length * (11 * (k + 1) + 1) +
       2 ^ (q + 1) * (8 * (k + 1) + 2)) := by
  let P := 2 ^ (q + 1)
  have hP : P = 2 ^ q + 2 ^ q := by dsimp [P]; rw [Nat.pow_succ]; omega
  let net := bitonicSort 0 (q + 1) true
  have hnet : ∀ c ∈ net, c.1 < P ∧ c.2.1 < P := fun c hc => by
    have hm := bitonicSort_mem 0 (q + 1) true c hc; omega
  have hconst : ∀ c : Bool, (fun _ : Fin n → Bool => c) ∈ S := fun c => by
    cases c
    · exact hfalse
    · exact htrue
  let stRaw : (Fin n → Bool) → Nat → Rec := fun v => mergeRawRec k D q (A v) (B v)
  have hK0 : ∀ idx < P, ∀ b < k + 1, (fun v => (stRaw v idx).1 b) ∈ S := by
    intro idx _ b hb
    dsimp only [stRaw, mergeRawRec]
    by_cases c1 : idx < D
    · simp only [c1, ↓reduceIte]; exact hA idx c1 b hb
    · by_cases c2 : 2 ^ q ≤ idx ∧ idx < 2 ^ q + D
      · simp only [c1, c2, ↓reduceIte]; exact hB (idx - 2 ^ q) (by omega) b hb
      · simp only [c1, c2, ↓reduceIte]; exact hconst (sentBit k b)
  have Hsort1 := netCircuit (k + 1) 0 P net hnet stRaw hK0 (fun _ _ _ hj => by omega) hfalse
  let B1 :=
    ({f | ∃ idx < P, ∃ b < k + 1, f = fun v => (runNet (recKey (k + 1)) net (stRaw v) idx).1 b} ∪
     {f | ∃ idx < P, ∃ b < 0, f = fun v => (runNet (recKey (k + 1)) net (stRaw v) idx).2 b}) ∪
    {f | ∃ t < net.length,
      f = (fun v => ((netSwaps (recKey (k + 1)) net (stRaw v)).getD t (0, 0, false)).2.2) ∨
      f = (fun v => !(((netSwaps (recKey (k + 1)) net (stRaw v)).getD t (0, 0, false)).2.2))}
  let A1 := S ∪ B1
  let uRec : (Fin n → Bool) → Nat → Rec := fun v => runNet (recKey (k + 1)) net (stRaw v)
  have huMem : ∀ idx < P, ∀ b < k + 1, (fun v => (uRec v idx).1 b) ∈ A1 :=
    fun idx hidx b hb => Or.inr (Or.inl (Or.inl ⟨idx, hidx, b, hb, rfl⟩))
  let stDed : (Fin n → Bool) → Nat → Rec := fun v => mergeDedupRec k (uRec v)
  have Hded : Build A1 {f | ∃ idx < P, ∃ b < k + 1, f = fun v => (stDed v idx).1 b}
      (P * (8 * (k + 1) + 2)) := by
    have Hper : ∀ idx < P, Build A1 {f | ∃ b < k + 1, f = fun v => (stDed v idx).1 b}
        (8 * (k + 1) + 2) := by
      intro idx hidx
      by_cases hpos : 0 < idx
      · let eqS : Sig n := fun v => decide (recKey (k + 1) (uRec v idx) = recKey (k + 1) (uRec v (idx - 1)))
        have Heq : Build A1 {eqS} (5 * (k + 1) + 1) :=
          eqWordG (fun b v => (uRec v idx).1 b) (fun b v => (uRec v (idx - 1)).1 b) (k + 1)
            (fun b hb => huMem idx hidx b hb) (fun b hb => huMem (idx - 1) (by omega) b hb)
            (Or.inl hfalse)
        have Hneq : Build (A1 ∪ {eqS}) {nt eqS} 1 := notG (Or.inr rfl)
        let A1' := A1 ∪ ({eqS} ∪ {nt eqS})
        have Hbits : Build A1' {f | ∃ b < k + 1, f = fun v => (stDed v idx).1 b} ((k + 1) * 3) :=
          rangeG (fun b v => (stDed v idx).1 b) 3 fun b hb => by
            have he : (fun v => (stDed v idx).1 b) =
                (fun v => if eqS v then sentBit k b else (uRec v idx).1 b) := by
              funext v; simp [stDed, mergeDedupRec, hpos, eqS]
            rw [he]
            exact muxG (Or.inr (Or.inl rfl)) (Or.inr (Or.inr rfl))
              (Or.inl (Or.inl (hconst (sentBit k b))))
              (Or.inl (huMem idx hidx b hb)) (fun _ => rfl)
        exact relax (seq (seq Heq Hneq) Hbits) le_rfl Set.subset_union_right (by omega)
      · refine relax (idle ?_) le_rfl le_rfl (by omega)
        rintro f ⟨b, hb, rfl⟩
        have he : (fun v => (stDed v idx).1 b) = (fun v => (uRec v idx).1 b) := by
          funext v; simp [stDed, mergeDedupRec, hpos]
        rw [he]; exact huMem idx hidx b hb
    have hall := rangeSetsG (m := P) (fun idx => {f | ∃ b < k + 1, f = fun v => (stDed v idx).1 b})
      (8 * (k + 1) + 2) Hper
    refine relax hall le_rfl ?_ le_rfl
    rintro f ⟨idx, hidx, b, hb, rfl⟩
    exact ⟨idx, hidx, b, hb, rfl⟩
  let B2 := {f | ∃ idx < P, ∃ b < k + 1, f = fun v => (stDed v idx).1 b}
  have Hsort2 := netCircuit (A := S ∪ (B1 ∪ B2)) (k + 1) 0 P net hnet stDed
    (fun idx hidx b hb => Or.inr (Or.inr ⟨idx, hidx, b, hb, rfl⟩))
    (fun _ _ _ hj => by omega) (Or.inl hfalse)
  have Htot := seq (seq Hsort1 Hded) Hsort2
  refine relax Htot le_rfl ?_ (by dsimp only [net, P]; simp only [Nat.mul_zero, Nat.add_zero]; rw [Nat.two_mul, Nat.add_mul]; omega)
  rintro f ⟨j, hj, b, hb, rfl⟩
  exact Or.inr (Or.inl (Or.inl ⟨j, by omega, b, hb, rfl⟩))

end TopDSec

section PipelineHelpers

theorem chain {n : Nat} {A B C : Set (Sig n)} {b c : Nat}
    (_hAB : A ⊆ B) (H : Build A B b) (J : Build B C c) : Build A (B ∪ C) (b + c) :=
  seq H (relax J Set.subset_union_right le_rfl le_rfl)

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

def packList (k : Nat) (L : Nat → Nat → Bool) (t : Nat) : Bool :=
  L (t / (k + 1)) (t % (k + 1))

def unpackList (k : Nat) (p : Nat → Bool) (j b : Nat) : Bool :=
  p (j * (k + 1) + b)

theorem unpack_pack (k : Nat) (L : Nat → Nat → Bool) (j b : Nat) (hb : b < k + 1) :
    unpackList k (packList k L) j b = L j b := by
  dsimp only [unpackList, packList]
  have h1 : (j * (k + 1) + b) / (k + 1) = j := by
    rw [Nat.add_comm, Nat.mul_comm, Nat.add_mul_div_left _ _ (Nat.succ_pos k), Nat.div_eq_of_lt hb, Nat.zero_add]
  have h2 : (j * (k + 1) + b) % (k + 1) = b := by
    rw [Nat.add_comm, Nat.mul_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hb]
  rw [h1, h2]

theorem pack_bitsVal_eq_iff (k D : Nat) (L1 L2 : Nat → Nat → Bool) :
    bitsVal (packList k L1) (D * (k + 1)) = bitsVal (packList k L2) (D * (k + 1)) ↔
      ∀ j < D, bitsVal (L1 j) (k + 1) = bitsVal (L2 j) (k + 1) := by
  constructor
  · intro heq j hj
    apply bitsVal_congr
    intro b hb
    have hidx : j * (k + 1) + b < D * (k + 1) := by
      have hm := Nat.mul_le_mul_right (k + 1) (show j + 1 ≤ D by omega)
      rw [Nat.succ_mul] at hm; omega
    have hbit := bitsVal_inj _ _ _ heq (j * (k + 1) + b) hidx
    rw [← unpack_pack k L1 j b hb, ← unpack_pack k L2 j b hb]
    exact hbit
  · intro hall
    apply bitsVal_congr
    intro t ht
    dsimp only [packList]
    have hq : t / (k + 1) < D := Nat.div_lt_of_lt_mul (by rwa [Nat.mul_comm])
    have hr : t % (k + 1) < k + 1 := Nat.mod_lt t (Nat.succ_pos k)
    exact bitsVal_inj _ _ _ (hall (t / (k + 1)) hq) (t % (k + 1)) hr

def scan4 (k D q : Nat) (st : Nat → Rec) : Nat → (Nat → Nat → Bool) × (Nat → Nat → Nat → Bool)
  | 0 =>
    let L0 := unpackList k (st 0).2
    (L0, fun idx => if idx = 0 then L0 else fun _ => sentBit k)
  | m + 1 =>
    let prev := scan4 k D q st m
    let isF := (st m).1 0
    let base : Nat → Nat → Bool := fun j b => if isF then sentBit k b else prev.1 j b
    let cur := mergeTruncBits k D q base (unpackList k (st (m + 1)).2)
    (cur, fun idx => if idx = m + 1 then cur else prev.2 idx)

theorem scan4_at (k D q : Nat) (st : Nat → Rec) :
    ∀ m idx, idx ≤ m → (scan4 k D q st m).2 idx = (scan4 k D q st idx).1 := by
  intro m
  induction m with
  | zero =>
    intro idx hidx
    have h0 : idx = 0 := by omega
    subst h0; rfl
  | succ m ih =>
    intro idx hidx
    simp only [scan4]
    by_cases heq : idx = m + 1
    · subst heq; simp [scan4]
    · simp only [heq, ↓reduceIte]
      exact ih idx (by omega)

def segUnion (st : Nat → Rec) (recSet : Nat → Finset Nat) : Nat → Finset Nat
  | 0 => recSet 0
  | m + 1 => if (st m).1 0 then recSet (m + 1) else segUnion st recSet m ∪ recSet (m + 1)

theorem scan4_isTopD (k D q : Nat) (hDq : D ≤ 2 ^ q) (st : Nat → Rec)
    (recSet : Nat → Finset Nat)
    (hBound : ∀ m, ∀ y ∈ recSet m, y < 2 ^ k)
    (hRec : ∀ m, IsTopD D (2 ^ k) (recSet m) (fun j => bitsVal (unpackList k (st m).2 j) (k + 1))) :
    ∀ m, (∀ y ∈ segUnion st recSet m, y < 2 ^ k) ∧
      IsTopD D (2 ^ k) (segUnion st recSet m) (fun j => bitsVal ((scan4 k D q st m).1 j) (k + 1)) := by
  intro m
  induction m with
  | zero =>
    exact ⟨hBound 0, hRec 0⟩
  | succ m ih =>
    simp only [scan4, segUnion]
    cases hF : (st m).1 0
    · simp only [Bool.false_eq_true, ↓reduceIte]
      refine ⟨fun y hy => (Finset.mem_union.mp hy).elim (ih.1 y) (hBound (m + 1) y), ?_⟩
      exact IsTopD_mergeTrunc k D q hDq (segUnion st recSet m) (recSet (m + 1)) ih.1 (hBound (m + 1))
        (scan4 k D q st m).1 (unpackList k (st (m + 1)).2) ih.2 (hRec (m + 1))
    · simp only [↓reduceIte]
      refine ⟨hBound (m + 1), ?_⟩
      have hemp : IsTopD D (2 ^ k) ∅ (fun j => bitsVal (fun b => sentBit k b) (k + 1)) :=
        IsTopD_congr (IsTopD_empty D (2 ^ k)) (fun _ _ => (bitsVal_sentBit k).symm)
      have hm := IsTopD_mergeTrunc k D q hDq ∅ (recSet (m + 1))
        (fun _ h => absurd h (Finset.notMem_empty _)) (hBound (m + 1))
        (fun _ => sentBit k) (unpackList k (st (m + 1)).2) hemp (hRec (m + 1))
      simpa using hm

theorem segUnion_interval (st : Nat → Rec) (recSet : Nat → Finset Nat) :
    ∀ a b, a ≤ b → (∀ t, a ≤ t → t < b → (st t).1 0 = false) →
      segUnion st recSet b =
        (if a = 0 then recSet 0 else if (st (a - 1)).1 0 then recSet a else segUnion st recSet a) ∪
          ((Finset.Icc a b).erase a).biUnion recSet := by
  intro a b hab
  induction b with
  | zero =>
    intro _
    have ha : a = 0 := by omega
    subst ha
    simp [segUnion]
  | succ b ih =>
    intro hnoF
    by_cases heq : a = b + 1
    · subst heq
      have her : (Finset.Icc (b + 1) (b + 1)).erase (b + 1) = ∅ := by
        ext t; simp
      rw [her, Finset.biUnion_empty, Finset.union_empty]
      simp only [Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte, Nat.add_sub_cancel]
      cases hF : (st b).1 0 <;> simp [segUnion, hF]
    · have hab' : a ≤ b := by omega
      have hFb : (st b).1 0 = false := hnoF b hab' (Nat.lt_succ_self b)
      have ih' := ih hab' (fun t h1 h2 => hnoF t h1 (by omega))
      simp only [segUnion, hFb, Bool.false_eq_true, ↓reduceIte]
      rw [ih', Finset.union_assoc]
      congr 1
      have hset : (Finset.Icc a (b + 1)).erase a = insert (b + 1) ((Finset.Icc a b).erase a) := by
        ext t
        simp only [Finset.mem_erase, Finset.mem_Icc, Finset.mem_insert]
        omega
      rw [hset, Finset.biUnion_insert, Finset.union_comm]

theorem scan4Circuit {n : Nat} {A : Set (Sig n)} (k D q P : Nat) (hDq : D ≤ 2 ^ q)
    (st : (Fin n → Bool) → Nat → Rec)
    (hF : ∀ idx < P, (fun v => (st v idx).1 0) ∈ A)
    (hV : ∀ idx < P, ∀ j < D, ∀ b < k + 1, (fun v => unpackList k (st v idx).2 j b) ∈ A)
    (hfalse : (fun _ => false) ∈ A) (htrue : (fun _ => true) ∈ A) :
    let stepCost := 1 + 3 * (D * (k + 1)) +
      (2 * (bitonicSort 0 (q + 1) true).length * (11 * (k + 1) + 1) +
       2 ^ (q + 1) * (8 * (k + 1) + 2))
    ∀ m < P,
      Build A
        ({f | ∃ j < D, ∃ b < k + 1, f = fun v => (scan4 k D q (st v) m).1 j b} ∪
         {f | ∃ idx ≤ m, ∃ j < D, ∃ b < k + 1, f = fun v => (scan4 k D q (st v) m).2 idx j b})
        (m * stepCost) := by
  intro stepCost m
  induction m with
  | zero =>
    intro h0
    refine relax (idle ?_) le_rfl le_rfl (by simp)
    rintro f (⟨j, hj, b, hb, rfl⟩ | ⟨idx, hidx, j, hj, b, hb, rfl⟩)
    · exact hV 0 h0 j hj b hb
    · have hi0 : idx = 0 := by omega
      subst hi0
      simpa [scan4] using hV 0 h0 j hj b hb
  | succ m ih =>
    intro hm
    have Hprev := ih (by omega)
    let Bprev :=
      {f | ∃ j < D, ∃ b < k + 1, f = fun v => (scan4 k D q (st v) m).1 j b} ∪
      {f | ∃ idx ≤ m, ∃ j < D, ∃ b < k + 1, f = fun v => (scan4 k D q (st v) m).2 idx j b}
    let A1 := A ∪ Bprev
    let fSig : Sig n := fun v => (st v m).1 0
    have hf1 : fSig ∈ A1 := Or.inl (hF m (by omega))
    have Hnf : Build A1 {nt fSig} 1 := notG hf1
    let A2 := A1 ∪ {nt fSig}
    let baseF : (Fin n → Bool) → Nat → Nat → Bool :=
      fun v j b => if fSig v then sentBit k b else (scan4 k D q (st v) m).1 j b
    have hconst2 : ∀ c : Bool, (fun _ : Fin n → Bool => c) ∈ A2 := fun c => by
      cases c
      · exact Or.inl (Or.inl hfalse)
      · exact Or.inl (Or.inl htrue)
    have Hbase : Build A2 {f | ∃ t < D * (k + 1), f = fun v => packList k (baseF v) t}
        (D * (k + 1) * 3) := rangeG (fun t v => packList k (baseF v) t) 3 fun t ht => by
      have hq' : t / (k + 1) < D := Nat.div_lt_of_lt_mul (by rwa [Nat.mul_comm])
      have hr' : t % (k + 1) < k + 1 := Nat.mod_lt t (Nat.succ_pos k)
      exact muxG (Or.inl hf1) (Or.inr rfl) (hconst2 (sentBit k (t % (k + 1))))
        (Or.inl (Or.inr (Or.inl ⟨t / (k + 1), hq', t % (k + 1), hr', rfl⟩))) (fun _ => rfl)
    let Bbase := {f | ∃ t < D * (k + 1), f = fun v => packList k (baseF v) t}
    let A3 := A1 ∪ ({nt fSig} ∪ Bbase)
    have hbaseMem : ∀ j < D, ∀ b < k + 1, (fun v => baseF v j b) ∈ A3 := by
      intro j hj b hb
      have hidx : j * (k + 1) + b < D * (k + 1) := by
        have := Nat.mul_le_mul_right (k + 1) (show j + 1 ≤ D by omega)
        rw [Nat.succ_mul] at this; omega
      have he : (fun v => baseF v j b) = (fun v => packList k (baseF v) (j * (k + 1) + b)) := by
        funext v; exact (unpack_pack k (baseF v) j b hb).symm
      rw [he]
      exact Or.inr (Or.inr ⟨j * (k + 1) + b, hidx, rfl⟩)
    have Hmerge := mergeTruncG (S := A3) k D q hDq baseF (fun v => unpackList k (st v (m + 1)).2)
      hbaseMem (fun j hj b hb => Or.inl (Or.inl (hV (m + 1) hm j hj b hb)))
      (Or.inl (Or.inl hfalse)) (Or.inl (Or.inl htrue))
    have Htot := seq Hprev (seq (seq Hnf Hbase) Hmerge)
    refine relax Htot le_rfl ?_ ?_
    · rintro f (⟨j, hj, b, hb, rfl⟩ | ⟨idx, hidx, j, hj, b, hb, rfl⟩)
      · exact Or.inr (Or.inr ⟨j, hj, b, hb, rfl⟩)
      · by_cases him : idx = m + 1
        · subst him
          exact Or.inr (Or.inr ⟨j, hj, b, hb, by funext v; simp [scan4, baseF, fSig]⟩)
        · exact Or.inl (Or.inr ⟨idx, by omega, j, hj, b, hb, by funext v; simp [scan4, him]⟩)
    · rw [Nat.succ_mul m]
      dsimp only [stepCost]
      omega

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

end PipelineHelpers

section PipelineMain

theorem gate_budget_bound (k r prefixLen degreeCap : Nat)
    (hk_odd : k % 2 = 1) (hp_pos : 0 < prefixLen) (hp_le : prefixLen ≤ k) (hd_le : degreeCap ≤ 2 ^ k) :
    let N := 2 ^ k
    let s := k - prefixLen
    let S := 2 ^ s
    let M := 2 ^ (k + s)
    let e := k + s + 1
    let P := 2 ^ e
    let D := degreeCap + 1
    let q := ceilLog2 D
    let LW := D * (k + 1)
    let W5 := k + LW + 1
    let netE := bitonicSort 0 e true
    let netS := bitonicSort 0 s true
    let netQ := bitonicSort 0 (q + 1) true
    let netK := bitonicSort 0 k true
    let step4 := 1 + 3 * LW + (2 * netQ.length * (11 * (k + 1) + 1) + 2 ^ (q + 1) * (8 * (k + 1) + 2))
    2 +
      M * (2 * (r * (38 * k + 8) + 4 * k)) +
      (netE.length * (11 * (k + 2) + 6 * 1 + 1) + P * 7 + netE.length * 6) +
      (M * (k + 1) + N * (netS.length * (11 * (k + 1) + 1))) +
      (netE.length * (11 * (k + 2) + 6 * LW + 1) + (P - 1) * step4 + netE.length * (6 * LW)) +
      (N * 4 + netK.length * (11 * W5 + 1) + N * (5 * LW + 2) + netK.length * 6 + 24 * N) ≤
    1048576 * (r + 1) * (k + 1) ^ 4 * (degreeCap + 1) * 2 ^ (2 * k - prefixLen) := by
  intro N s S M e P D q LW W5 netE netS netQ netK step4
  have hk1 : 1 ≤ k := by omega
  let K := k + 1
  have hK2 : 2 ≤ K := by dsimp [K]; omega
  have hKpos : 1 ≤ K := by omega
  have hR1 : 1 ≤ r + 1 := by omega
  have hD1 : 1 ≤ D := by dsimp [D]; omega
  have hMeq : M = 2 ^ (2 * k - prefixLen) := by
    dsimp [M, s]; congr 1; omega
  have hNS : N * S = M := by dsimp [N, S, M]; rw [← Nat.pow_add]
  have hP2M : P = 2 * M := by dsimp [P, M, e]; rw [Nat.pow_succ, Nat.mul_comm]
  have hNleM : N ≤ M := by
    dsimp [N, M]; exact Nat.pow_le_pow_right Nat.zero_lt_two (by omega)
  have hMpos : 1 ≤ M := Nat.two_pow_pos _
  let U := (r + 1) * K ^ 4 * D * M
  have hK_le_K4 : K ≤ K ^ 4 := by
    have h2 : K ≤ K * K := Nat.le_mul_of_pos_right K hKpos
    have h3 : K * K ≤ K * K * K := Nat.le_mul_of_pos_right (K * K) hKpos
    have h4 : K * K * K ≤ K * K * K * K := Nat.le_mul_of_pos_right (K * K * K) hKpos
    have hp4 : K ^ 4 = K * K * K * K := by ring
    omega
  have hK2_le_K4 : K ^ 2 ≤ K ^ 4 := by
    have hp : K ^ 4 = K ^ 2 * K ^ 2 := by ring
    have h1 : 1 ≤ K ^ 2 := Nat.one_le_pow 2 K hKpos
    calc K ^ 2 = K ^ 2 * 1 := (Nat.mul_one _).symm
      _ ≤ K ^ 2 * K ^ 2 := Nat.mul_le_mul_left _ h1
      _ = K ^ 4 := hp.symm
  have hK3_le_K4 : K ^ 3 ≤ K ^ 4 := by
    have hp : K ^ 4 = K ^ 3 * K := by ring
    calc K ^ 3 = K ^ 3 * 1 := (Nat.mul_one _).symm
      _ ≤ K ^ 3 * K := Nat.mul_le_mul_left _ hKpos
      _ = K ^ 4 := hp.symm
  have hM_le_U : M ≤ U := by
    dsimp [U]
    have h1 : 1 ≤ (r + 1) * K ^ 4 * D :=
      Nat.mul_pos (Nat.mul_pos hR1 (Nat.pow_pos hKpos)) hD1
    calc M = 1 * M := (Nat.one_mul M).symm
      _ ≤ ((r + 1) * K ^ 4 * D) * M := Nat.mul_le_mul_right M h1
  have hK3DM_le_U : K ^ 3 * D * M ≤ U := by
    dsimp [U]
    have h1 : K ^ 3 * D ≤ (r + 1) * K ^ 4 * D := by
      have ha : K ^ 3 ≤ (r + 1) * K ^ 4 := by
        calc K ^ 3 ≤ K ^ 4 := hK3_le_K4
          _ = 1 * K ^ 4 := (Nat.one_mul _).symm
          _ ≤ (r + 1) * K ^ 4 := Nat.mul_le_mul_right _ hR1
      exact Nat.mul_le_mul_right D ha
    exact Nat.mul_le_mul_right M h1
  have hK3M_le_U : K ^ 3 * M ≤ U := by
    have h1 : K ^ 3 * M ≤ K ^ 3 * D * M := by
      rw [Nat.mul_assoc (K ^ 3) D M]
      exact Nat.mul_le_mul_left (K ^ 3) (by calc M = 1 * M := (Nat.one_mul M).symm
        _ ≤ D * M := Nat.mul_le_mul_right M hD1)
    exact h1.trans hK3DM_le_U
  have hK2M_le_U : K ^ 2 * M ≤ U := by
    have h1 : K ^ 2 * M ≤ K ^ 3 * M := Nat.mul_le_mul_right M (by
      have : K ^ 3 = K ^ 2 * K := by ring
      rw [this]; exact Nat.le_mul_of_pos_right _ hKpos)
    exact h1.trans hK3M_le_U
  have hKM_le_U : K * M ≤ U := by
    have h1 : K * M ≤ K ^ 2 * M := Nat.mul_le_mul_right M (by
      have : K ^ 2 = K * K := by ring
      rw [this]; exact Nat.le_mul_of_pos_right _ hKpos)
    exact h1.trans hK2M_le_U
  have hNetE_le : netE.length ≤ 2 * K ^ 2 * M := by
    have hl := bitonicSort_length 0 e true
    have he1 : e ≤ 2 * K := by dsimp [e, s, K]; omega
    have he2 : e + 1 ≤ 2 * K := by dsimp [e, s, K]; omega
    have hprod : e * (e + 1) * P ≤ (2 * K) * (2 * K) * (2 * M) := by
      rw [hP2M]
      exact Nat.mul_le_mul_right _ (Nat.mul_le_mul he1 he2)
    have hrhs : (2 * K) * (2 * K) * (2 * M) = 4 * (2 * K ^ 2 * M) := by ring
    change 4 * netE.length = e * (e + 1) * P at hl
    omega
  have hNetS_le : N * netS.length ≤ K ^ 2 * M := by
    have hl := bitonicSort_length 0 s true
    have hs1 : s ≤ K := by dsimp [s, K]; omega
    have hs2 : s + 1 ≤ K := by dsimp [s, K]; omega
    have hprod : s * (s + 1) * S ≤ K * K * S := Nat.mul_le_mul_right S (Nat.mul_le_mul hs1 hs2)
    have h4 : 4 * (N * netS.length) = N * (4 * netS.length) := by ring
    change 4 * netS.length = s * (s + 1) * S at hl
    rw [hl] at h4
    have h5 : N * (s * (s + 1) * S) ≤ N * (K * K * S) := Nat.mul_le_mul_left N hprod
    have h6 : N * (K * K * S) = K ^ 2 * M := by rw [← hNS]; ring
    omega
  have hNetK_le : netK.length ≤ K ^ 2 * M := by
    have hl := bitonicSort_length 0 k true
    have hk_le : k ≤ K := by dsimp [K]; omega
    have hprod : k * (k + 1) * N ≤ K * K * M := Nat.mul_le_mul (Nat.mul_le_mul hk_le le_rfl) hNleM
    have hrhs : K * K * M = K ^ 2 * M := by ring
    change 4 * netK.length = k * (k + 1) * N at hl
    omega
  have hq_spec := ceilLog2_spec hD1
  have hq_le : q ≤ K := ceilLog2_le (by dsimp [D]; omega)
  have h2q1 : 2 ^ (q + 1) ≤ 4 * D := by
    have h2q : 2 ^ q ≤ 2 * D := hq_spec.2
    rw [Nat.pow_succ]; omega
  have hNetQ_le : netQ.length ≤ 4 * K ^ 2 * D := by
    have hl : 4 * netQ.length = (q + 1) * (q + 2) * 2 ^ (q + 1) := bitonicSort_length 0 (q + 1) true
    have h1 : q + 1 ≤ 2 * K := by omega
    have h2 : q + 2 ≤ 2 * K := by omega
    have hprod : (q + 1) * (q + 2) * 2 ^ (q + 1) ≤ (2 * K) * (2 * K) * (4 * D) :=
      Nat.mul_le_mul (Nat.mul_le_mul h1 h2) h2q1
    have hrhs : (2 * K) * (2 * K) * (4 * D) = 4 * (4 * K ^ 2 * D) := by ring
    omega
  have hS0 : 2 ≤ 2 * U := by omega
  have hS1 : M * (2 * (r * (38 * k + 8) + 4 * k)) ≤ 100 * U := by
    have h1 : 38 * k + 8 ≤ 46 * K := by dsimp [K]; omega
    have h2 : r * (38 * k + 8) + 4 * k ≤ (r + 1) * (46 * K) := by
      have hrk := Nat.mul_le_mul_left r h1
      have h4k : 4 * k ≤ 46 * K := by dsimp [K]; omega
      rw [Nat.add_mul, Nat.one_mul]; omega
    have h3 : 2 * (r * (38 * k + 8) + 4 * k) ≤ 92 * ((r + 1) * K) := by
      have := Nat.mul_le_mul_left 2 h2
      have he : 2 * ((r + 1) * (46 * K)) = 92 * ((r + 1) * K) := by ring
      omega
    have h4 : M * (2 * (r * (38 * k + 8) + 4 * k)) ≤ 92 * ((r + 1) * K * M) := by
      have := Nat.mul_le_mul_left M h3
      have he : M * (92 * ((r + 1) * K)) = 92 * ((r + 1) * K * M) := by ring
      omega
    have h5 : (r + 1) * K * M ≤ U := by
      dsimp [U]
      have ha : (r + 1) * K ≤ (r + 1) * K ^ 4 := Nat.mul_le_mul_left (r + 1) hK_le_K4
      have hb : (r + 1) * K ^ 4 ≤ (r + 1) * K ^ 4 * D := Nat.le_mul_of_pos_right _ hD1
      exact Nat.mul_le_mul_right M (ha.trans hb)
    omega
  have hS2 : netE.length * (11 * (k + 2) + 6 * 1 + 1) + P * 7 + netE.length * 6 ≤ 100 * U := by
    have hc : 11 * (k + 2) + 6 * 1 + 1 ≤ 20 * K := by dsimp [K]; omega
    have h1 : netE.length * (11 * (k + 2) + 6 * 1 + 1) ≤ (2 * K ^ 2 * M) * (20 * K) :=
      Nat.mul_le_mul hNetE_le hc
    have he1 : (2 * K ^ 2 * M) * (20 * K) = 40 * (K ^ 3 * M) := by ring
    have h2 : P * 7 = 14 * M := by rw [hP2M]; ring
    have h3 : netE.length * 6 ≤ 12 * (K ^ 2 * M) := by
      have := Nat.mul_le_mul_right 6 hNetE_le
      have he : (2 * K ^ 2 * M) * 6 = 12 * (K ^ 2 * M) := by ring
      omega
    omega
  have hS3 : M * (k + 1) + N * (netS.length * (11 * (k + 1) + 1)) ≤ 20 * U := by
    have h1 : M * (k + 1) = K * M := by dsimp [K]; ring
    have h2 : 11 * (k + 1) + 1 ≤ 12 * K := by dsimp [K]; omega
    have h3 : N * (netS.length * (11 * (k + 1) + 1)) = (N * netS.length) * (11 * (k + 1) + 1) := by ring
    have h4 : (N * netS.length) * (11 * (k + 1) + 1) ≤ (K ^ 2 * M) * (12 * K) :=
      Nat.mul_le_mul hNetS_le h2
    have he : (K ^ 2 * M) * (12 * K) = 12 * (K ^ 3 * M) := by ring
    omega
  have hStep4 : step4 ≤ 150 * (K ^ 3 * D) := by
    have hc1 : 11 * (k + 1) + 1 ≤ 12 * K := by dsimp [K]; omega
    have h1 : 2 * netQ.length * (11 * (k + 1) + 1) ≤ 2 * (4 * K ^ 2 * D) * (12 * K) :=
      Nat.mul_le_mul (Nat.mul_le_mul_left 2 hNetQ_le) hc1
    have he1 : 2 * (4 * K ^ 2 * D) * (12 * K) = 96 * (K ^ 3 * D) := by ring
    have hc2 : 8 * (k + 1) + 2 ≤ 9 * K := by dsimp [K]; omega
    have h2 : 2 ^ (q + 1) * (8 * (k + 1) + 2) ≤ (4 * D) * (9 * K) := Nat.mul_le_mul h2q1 hc2
    have hKD_le : K * D ≤ K ^ 3 * D := Nat.mul_le_mul_right D (by
      have : K ≤ K ^ 3 := by
        have hp : K ^ 3 = K * (K * K) := by ring
        rw [hp]; exact Nat.le_mul_of_pos_right K (Nat.mul_pos hKpos hKpos)
      exact this)
    have he2 : (4 * D) * (9 * K) = 36 * (K * D) := by ring
    have hLW : LW = D * K := rfl
    have h3 : 1 + 3 * LW ≤ 4 * (K * D) := by
      have : 1 ≤ K * D := Nat.mul_pos hKpos hD1
      rw [hLW]; rw [Nat.mul_comm D K]; omega
    dsimp only [step4]
    omega
  have hS4 : netE.length * (11 * (k + 2) + 6 * LW + 1) + (P - 1) * step4 + netE.length * (6 * LW) ≤ 400 * U := by
    have hc1 : 11 * (k + 2) + 6 * LW + 1 ≤ 26 * (K * D) := by
      have h1 : 11 * (k + 2) + 1 ≤ 20 * K := by dsimp [K]; omega
      have h2 : 20 * K ≤ 20 * (K * D) := by
        rw [← Nat.mul_assoc]; exact Nat.le_mul_of_pos_right _ hD1
      have h3 : LW = K * D := by dsimp [LW, K]; ring
      omega
    have h1 : netE.length * (11 * (k + 2) + 6 * LW + 1) ≤ (2 * K ^ 2 * M) * (26 * (K * D)) :=
      Nat.mul_le_mul hNetE_le hc1
    have he1 : (2 * K ^ 2 * M) * (26 * (K * D)) = 52 * (K ^ 3 * D * M) := by ring
    have h2 : (P - 1) * step4 ≤ (2 * M) * (150 * (K ^ 3 * D)) :=
      Nat.mul_le_mul (by omega) hStep4
    have he2 : (2 * M) * (150 * (K ^ 3 * D)) = 300 * (K ^ 3 * D * M) := by ring
    have h3 : netE.length * (6 * LW) ≤ (2 * K ^ 2 * M) * (6 * (K * D)) := by
      have hLW : LW = K * D := by dsimp [LW, K]; ring
      rw [hLW]; exact Nat.mul_le_mul_right _ hNetE_le
    have he3 : (2 * K ^ 2 * M) * (6 * (K * D)) = 12 * (K ^ 3 * D * M) := by ring
    omega
  have hS5 : N * 4 + netK.length * (11 * W5 + 1) + N * (5 * LW + 2) + netK.length * 6 + 24 * N ≤ 100 * U := by
    have hW5 : 11 * W5 + 1 ≤ 24 * (K * D) := by
      have hLW : LW = K * D := by dsimp [LW, K]; ring
      have hK_le : K ≤ K * D := Nat.le_mul_of_pos_right K hD1
      have h1 : W5 ≤ 2 * (K * D) := by dsimp [W5]; omega
      have h1le : 1 ≤ K * D := Nat.mul_pos hKpos hD1
      omega
    have h1 : netK.length * (11 * W5 + 1) ≤ (K ^ 2 * M) * (24 * (K * D)) :=
      Nat.mul_le_mul hNetK_le hW5
    have he1 : (K ^ 2 * M) * (24 * (K * D)) = 24 * (K ^ 3 * D * M) := by ring
    have h2 : N * (5 * LW + 2) ≤ M * (7 * (K * D)) := by
      have hLW : LW = K * D := by dsimp [LW, K]; ring
      have h1le : 1 ≤ K * D := Nat.mul_pos hKpos hD1
      exact Nat.mul_le_mul hNleM (by omega)
    have he2 : M * (7 * (K * D)) = 7 * (K * D * M) := by ring
    have hKDM_le : K * D * M ≤ K ^ 3 * D * M := by
      have : K ≤ K ^ 3 := by
        have hp : K ^ 3 = K * (K * K) := by ring
        rw [hp]; exact Nat.le_mul_of_pos_right K (Nat.mul_pos hKpos hKpos)
      exact Nat.mul_le_mul_right M (Nat.mul_le_mul_right D this)
    have h3 : netK.length * 6 ≤ 6 * (K ^ 2 * M) := by
      have := Nat.mul_le_mul_right 6 hNetK_le; omega
    omega
  have hRhs : 1048576 * (r + 1) * (k + 1) ^ 4 * (degreeCap + 1) * 2 ^ (2 * k - prefixLen) = 1048576 * U := by
    rw [← hMeq]; dsimp only [U, K, D]; ring
  rw [hRhs]
  omega

set_option maxHeartbeats 800000 in
theorem solve_32053 (k r prefixLen degreeCap : Nat)
    (hk_odd : k % 2 = 1) (hk3 : k % 3 ≠ 0) (hp_pos : 0 < prefixLen) (hp_le : prefixLen ≤ k)
    (hd_le : degreeCap ≤ 2 ^ k) :
    let N := 2 ^ k
    let X := Fin N
    let rot := fun (shift x : Nat) => ((x <<< (shift % k)) ||| (x >>> (k - shift % k))) % N
    let chi := fun (x : Nat) => (List.range k).foldl (fun (acc i : Nat) =>
      acc ||| ((xor (x.testBit i) (!(x.testBit ((i + 1) % k)) && x.testBit ((i + 2) % k))).toNat <<< i)) 0
    let run := fun (masks : Nat → X) (col : Bool) (key name : Nat) =>
      let gap : Nat := if col then 2 else 1
      (List.range r).foldl (fun z j =>
        let mixed := z ^^^ rot gap z ^^^ rot (k - gap % k) z
        chi mixed ^^^ rot (if col then 3 * (j + 1) + 1 else 2 * j) key ^^^
          (masks (if col then r + j else j)).val) (rot (if col then 3 else 1) key ^^^ name)
    let bits := fun (len val : Nat) => (List.range len).map (fun i => val.testBit i)
    let dim := 2 * r * k + 2 * prefixLen + 2 * N
    let numOut := N + k + 1
    ∃ (C : Circuit) (out : Fin numOut → Fin (dim + C.size)),
      FanInTwo C ∧ ReadsBack dim C ∧
      C.output < dim + C.size ∧ C.size ≤ 1048576 * (r + 1) * (k + 1) ^ 4 * (degreeCap + 1) * 2 ^ (2 * k - prefixLen) ∧
      ∀ (masks : Nat → X) (rowTarget colTarget : Fin (2 ^ prefixLen)) (keepRow keepCol : X → Bool),
        let input := (List.range (2 * r)).flatMap (fun j => bits k (masks j).val) ++
          bits prefixLen rowTarget.val ++ bits prefixLen colTarget.val ++
          (List.finRange N).map keepRow ++ (List.finRange N).map keepCol
        let neigh := fun x : X => Finset.univ.filter (fun y : X => keepCol y = true ∧ ∃ w : X,
          run masks false w.val x.val >>> (k - prefixLen) = rowTarget.val ∧
          run masks true w.val y.val >>> (k - prefixLen) = colTarget.val)
        let mark := fun x : X => decide (keepRow x = true ∧ (neigh x).Nonempty ∧ (neigh x).card ≤ degreeCap ∧
          ∀ z : X, z < x → keepRow z = true → neigh z ≠ neigh x)
        let flags := (List.finRange N).map mark
        let answer := flags ++ bits (k + 1) (flags.count true)
        ∀ j : Fin numOut, (C.wires input).getD (out j).val false = answer.getD j.val false := by
  intro N X rot chi run bits dim numOut
  have hk : 0 < k := by omega
  have hk6 : k % 6 = 1 ∨ k % 6 = 5 := by omega
  let s := k - prefixLen
  let S := 2 ^ s
  have hSpos : 0 < S := Nat.two_pow_pos s
  let M := 2 ^ (k + s)
  have hNS : N * S = M := by dsimp [N, S, M]; rw [← Nat.pow_add]
  have hSN : S * N = M := by rw [Nat.mul_comm, hNS]
  have hNleM : N ≤ M := Nat.pow_le_pow_right Nat.zero_lt_two (by omega)
  let e := k + s + 1
  let P := 2 ^ e
  have hP2M : P = 2 * M := by dsimp [P, M, e]; rw [Nat.pow_succ, Nat.mul_comm]
  have hPpos : 2 ≤ P := by have := Nat.two_pow_pos (k + s); omega
  let D := degreeCap + 1
  have hD1 : 1 ≤ D := by omega
  let q := ceilLog2 D
  have hDq : D ≤ 2 ^ q := (ceilLog2_spec hD1).1
  let LW := D * (k + 1)
  let W5 := k + LW + 1
  let netE := bitonicSort 0 e true
  let netS := bitonicSort 0 s true
  let netQ := bitonicSort 0 (q + 1) true
  let netK := bitonicSort 0 k true
  have hnetE : ∀ c ∈ netE, c.1 < P ∧ c.2.1 < P := fun c hc => by
    have hm := bitonicSort_mem 0 e true c hc; omega
  have hnetS : ∀ c ∈ netS, c.1 < S ∧ c.2.1 < S := fun c hc => by
    have hm := bitonicSort_mem 0 s true c hc; omega
  have hnetK : ∀ c ∈ netK, c.1 < N ∧ c.2.1 < N := fun c hc => by
    have hm := bitonicSort_mem 0 k true c hc; omega
  let maskV : Nat → Fin k → Sig dim := fun j i v =>
    if hj : j < 2 * r then
      v ⟨j * k + i.val, by
        have hm := Nat.mul_le_mul_right k (show j + 1 ≤ 2 * r by omega)
        rw [Nat.succ_mul] at hm; dsimp [dim]; omega⟩
    else false
  let rowTargV : Fin prefixLen → Sig dim := fun i v =>
    v ⟨2 * r * k + i.val, by dsimp [dim]; omega⟩
  let colTargV : Fin prefixLen → Sig dim := fun i v =>
    v ⟨2 * r * k + prefixLen + i.val, by dsimp [dim]; omega⟩
  let keepRowV : Nat → Sig dim := fun x v =>
    if hx : x < N then v ⟨2 * r * k + 2 * prefixLen + x, by dsimp [dim]; omega⟩ else false
  let keepColV : Nat → Sig dim := fun y v =>
    if hy : y < N then v ⟨2 * r * k + 2 * prefixLen + N + y, by dsimp [dim]; omega⟩ else false
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
  have h0_kr : ∀ x, keepRowV x ∈ S0 := fun x => by
    dsimp only [keepRowV]; by_cases hx : x < N
    · simp only [hx, ↓reduceDIte]; exact Or.inl ⟨_, rfl⟩
    · simp only [hx, ↓reduceDIte]; exact h0_c false
  have h0_kc : ∀ y, keepColV y ∈ S0 := fun y => by
    dsimp only [keepColV]; by_cases hy : y < N
    · simp only [hy, ↓reduceDIte]; exact Or.inl ⟨_, rfl⟩
    · simp only [hy, ↓reduceDIte]; exact h0_c false
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
  let S1 := S0 ∪ B1
  have hC1 : Build inputs S1 (2 + M * (2 * (r * (38 * k + 8) + 4 * k))) := chain hS0_sub H0 H1
  have h1_row : ∀ w < N, ∀ lo < S, ∀ i : Fin k, (fun v => rowInvV v w lo i) ∈ S1 := by
    intro w hw lo hlo i
    have hidx : w * S + lo < M := by
      have hm := Nat.mul_le_mul_right S (show w + 1 ≤ N by omega)
      rw [Nat.succ_mul, hNS] at hm; omega
    have hdiv : (w * S + lo) / S = w := by
      rw [Nat.add_comm, Nat.mul_comm, Nat.add_mul_div_left _ _ hSpos, Nat.div_eq_of_lt hlo, Nat.zero_add]
    have hmod : (w * S + lo) % S = lo := by
      rw [Nat.add_comm, Nat.mul_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlo]
    exact Or.inr ⟨w * S + lo, hidx, Or.inl ⟨i, by rw [hdiv, hmod]⟩⟩
  have h1_col : ∀ w < N, ∀ lo < S, ∀ i : Fin k, (fun v => colInvV v w lo i) ∈ S1 := by
    intro w hw lo hlo i
    have hidx : w * S + lo < M := by
      have hm := Nat.mul_le_mul_right S (show w + 1 ≤ N by omega)
      rw [Nat.succ_mul, hNS] at hm; omega
    have hdiv : (w * S + lo) / S = w := by
      rw [Nat.add_comm, Nat.mul_comm, Nat.add_mul_div_left _ _ hSpos, Nat.div_eq_of_lt hlo, Nat.zero_add]
    have hmod : (w * S + lo) % S = lo := by
      rw [Nat.add_comm, Nat.mul_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlo]
    exact Or.inr ⟨w * S + lo, hidx, Or.inr ⟨i, by rw [hdiv, hmod]⟩⟩
  let st2Init : (Fin dim → Bool) → Nat → Rec := fun v idx =>
    if idx < N then
      (keyBits2 k false false (fun b => idx.testBit b), fun _ => keepColV idx v)
    else if idx < N + M then
      let qIdx := idx - N
      (keyBits2 k false true (fun b => if hb : b < k then colInvV v (qIdx / S) (qIdx % S) ⟨b, hb⟩ else false),
       fun _ => false)
    else
      (keyBits2 k true true (fun _ => false), fun _ => false)
  let s2Sorted : (Fin dim → Bool) → Nat → Rec := fun v => runNet (recKey (k + 2)) netE (st2Init v)
  let selColArr : (Fin dim → Bool) → Nat → Nat → Bool := fun v =>
    replaySwaps (netSwaps (recKey (k + 2)) netE (st2Init v)).reverse (fun idx (_ : Nat) => (scan2 k (s2Sorted v) P).2 idx)
  let selColV : (Fin dim → Bool) → Nat → Nat → Bool := fun v w lo => selColArr v (N + (w * S + lo)) 0
  let B2 : Set (Sig dim) := {f | ∃ idx < P, f = fun v => selColArr v idx 0}
  have H2 : Build S1 B2 (netE.length * (11 * (k + 2) + 6 * 1 + 1) + P * 7 + netE.length * 6) := by
    have hK2 : ∀ idx < P, ∀ j < k + 2, (fun v => (st2Init v idx).1 j) ∈ S1 := by
      intro idx _ j _
      dsimp only [st2Init]
      by_cases c1 : idx < N
      · simp only [c1, ↓reduceIte]; exact Or.inl (h0_c _)
      · by_cases c2 : idx < N + M
        · simp only [c1, c2, ↓reduceIte, keyBits2]
          by_cases hj0 : j = 0
          · simp only [hj0, ↓reduceIte]; exact Or.inl (h0_c true)
          · by_cases hjk : j = k + 1
            · simp only [hjk, ↓reduceIte]; exact Or.inl (h0_c false)
            · simp only [hj0, hjk, ↓reduceIte]
              by_cases hb : j - 1 < k
              · simp only [hb, ↓reduceDIte]
                have hqM : idx - N < M := by omega
                have hw : (idx - N) / S < N := Nat.div_lt_of_lt_mul (by rwa [hSN])
                have hlo : (idx - N) % S < S := Nat.mod_lt _ hSpos
                exact h1_col _ hw _ hlo ⟨j - 1, hb⟩
              · simp only [hb, ↓reduceDIte]; exact Or.inl (h0_c false)
        · simp only [c1, c2, ↓reduceIte]; exact Or.inl (h0_c _)
    have hV2 : ∀ idx < P, ∀ j < 1, (fun v => (st2Init v idx).2 j) ∈ S1 := by
      intro idx _ _ _
      dsimp only [st2Init]
      by_cases c1 : idx < N
      · simp only [c1, ↓reduceIte]; exact Or.inl (h0_kc idx)
      · by_cases c2 : idx < N + M
        · simp only [c1, c2, ↓reduceIte]; exact Or.inl (h0_c false)
        · simp only [c1, c2, ↓reduceIte]; exact Or.inl (h0_c false)
    have Hnet2 := netCircuit (A := S1) (k + 2) 1 P netE hnetE st2Init hK2 hV2 (Or.inl (h0_c false))
    let B2a :=
      ({f | ∃ idx < P, ∃ j < k + 2, f = fun v => (s2Sorted v idx).1 j} ∪
       {f | ∃ idx < P, ∃ j < 1, f = fun v => (s2Sorted v idx).2 j}) ∪
      {f | ∃ t < netE.length,
        f = (fun v => ((netSwaps (recKey (k + 2)) netE (st2Init v)).getD t (0, 0, false)).2.2) ∨
        f = (fun v => !(((netSwaps (recKey (k + 2)) netE (st2Init v)).getD t (0, 0, false)).2.2))}
    have Hsc2 := scan2Circuit (A := S1 ∪ B2a) k P s2Sorted
      (fun idx hidx j hj => Or.inr (Or.inl (Or.inl ⟨idx, hidx, j, hj, rfl⟩)))
      (fun idx hidx => Or.inr (Or.inl (Or.inr ⟨idx, hidx, 0, Nat.zero_lt_one, rfl⟩)))
      (Or.inl (Or.inl (h0_c false))) P le_rfl
    let B2b := {fun v => (scan2 k (s2Sorted v) P).1} ∪
      {f | ∃ idx < P, f = fun v => (scan2 k (s2Sorted v) P).2 idx}
    have Hrep2 := replayRevCircuit (A := S1 ∪ (B2a ∪ B2b)) (k + 2) 1 P netE hnetE st2Init
      (fun t ht => ⟨Or.inr (Or.inl (Or.inr ⟨t, ht, Or.inl rfl⟩)),
                    Or.inr (Or.inl (Or.inr ⟨t, ht, Or.inr rfl⟩))⟩)
      (fun v idx _ => (scan2 k (s2Sorted v) P).2 idx)
      (fun idx hidx _ _ => Or.inr (Or.inr (Or.inr ⟨idx, hidx, rfl⟩)))
    have Htot2 := seq (seq Hnet2 Hsc2) Hrep2
    refine relax Htot2 le_rfl ?_ (by omega)
    rintro f ⟨idx, hidx, rfl⟩
    exact Or.inr ⟨idx, hidx, 0, Nat.zero_lt_one, rfl⟩
  let S2 := S1 ∪ B2
  have hC2 := chain (hS0_sub.trans Set.subset_union_left) hC1 H2
  have h2_sel : ∀ w < N, ∀ lo < S, (fun v => selColV v w lo) ∈ S2 := by
    intro w hw lo hlo
    have hidx : w * S + lo < M := by
      have hm := Nat.mul_le_mul_right S (show w + 1 ≤ N by omega)
      rw [Nat.succ_mul, hNS] at hm; omega
    exact Or.inr ⟨N + (w * S + lo), by omega, rfl⟩
  let st3Init : (Fin dim → Bool) → Nat → Nat → Rec := fun v w lo =>
    (fun b => if b = k then !(selColV v w lo)
              else if hb : b < k then selColV v w lo && colInvV v w lo ⟨b, hb⟩
              else false,
     fun _ => false)
  let s3Sorted : (Fin dim → Bool) → Nat → Nat → Rec := fun v w => runNet (recKey (k + 1)) netS (st3Init v w)
  let keyListV : (Fin dim → Bool) → Nat → Nat → Nat → Bool := fun v w j b =>
    if j < S then (s3Sorted v w j).1 b else sentBit k b
  let B3 : Set (Sig dim) := {f | ∃ w < N, ∃ j < S, ∃ b < k + 1, f = fun v => (s3Sorted v w j).1 b}
  have H3 : Build S2 B3 (M * (k + 1) + N * (netS.length * (11 * (k + 1) + 1))) := by
    let B3a : Set (Sig dim) := {f | ∃ idx < M, ∃ b < k + 1, f = fun v => (st3Init v (idx / S) (idx % S)).1 b}
    have Hprep3 : Build S2 B3a (M * (k + 1)) := by
      have Hper : ∀ idx < M, Build S2 {f | ∃ b < k + 1, f = fun v => (st3Init v (idx / S) (idx % S)).1 b}
          (k + 1) := by
        intro idx hidx
        have hw : idx / S < N := Nat.div_lt_of_lt_mul (by rwa [hSN])
        have hlo : idx % S < S := Nat.mod_lt _ hSpos
        have h := rangeG (m := k + 1) (fun b v => (st3Init v (idx / S) (idx % S)).1 b) 1 fun b hb => by
          by_cases hbk : b = k
          · subst b
            have he : (fun v => (st3Init v (idx / S) (idx % S)).1 k) = nt (fun v => selColV v (idx / S) (idx % S)) := by
              funext v; simp [st3Init, nt]
            rw [he]; exact notG (h2_sel _ hw _ hlo)
          · have hlt : b < k := by omega
            have he : (fun v => (st3Init v (idx / S) (idx % S)).1 b) =
                an (fun v => selColV v (idx / S) (idx % S)) (fun v => colInvV v (idx / S) (idx % S) ⟨b, hlt⟩) := by
              funext v; simp [st3Init, an, hbk, hlt]
            rw [he]; exact andG (h2_sel _ hw _ hlo) (Or.inl (h1_col _ hw _ hlo ⟨b, hlt⟩))
        exact relax h le_rfl le_rfl (by omega)
      have hall := rangeSetsG (m := M) _ _ Hper
      refine relax hall le_rfl ?_ le_rfl
      rintro f ⟨idx, hidx, b, hb, rfl⟩; exact ⟨idx, hidx, b, hb, rfl⟩
    have Hsort3 : Build (S2 ∪ B3a) B3 (N * (netS.length * (11 * (k + 1) + 1))) := by
      have HperW : ∀ w < N, Build (S2 ∪ B3a)
          {f | ∃ j < S, ∃ b < k + 1, f = fun v => (s3Sorted v w j).1 b}
          (netS.length * (11 * (k + 1) + 1)) := by
        intro w hw
        have hK3 : ∀ lo < S, ∀ b < k + 1, (fun v => (st3Init v w lo).1 b) ∈ S2 ∪ B3a := by
          intro lo hlo b hb
          have hidx : w * S + lo < M := by
            have hm := Nat.mul_le_mul_right S (show w + 1 ≤ N by omega)
            rw [Nat.succ_mul, hNS] at hm; omega
          have hdiv : (w * S + lo) / S = w := by
            rw [Nat.add_comm, Nat.mul_comm, Nat.add_mul_div_left _ _ hSpos, Nat.div_eq_of_lt hlo, Nat.zero_add]
          have hmod : (w * S + lo) % S = lo := by
            rw [Nat.add_comm, Nat.mul_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlo]
          exact Or.inr ⟨w * S + lo, hidx, b, hb, by rw [hdiv, hmod]⟩
        have hnet := netCircuit (A := S2 ∪ B3a) (k + 1) 0 S netS hnetS (fun v => st3Init v w)
          hK3 (fun _ _ _ hj => by omega) (Or.inl (Or.inl (Or.inl (h0_c false))))
        exact relax hnet le_rfl (fun f ⟨j, hj, b, hb, hf⟩ => Or.inl (Or.inl ⟨j, hj, b, hb, hf⟩))
          (by simp only [Nat.mul_zero, Nat.add_zero]; exact le_rfl)
      have hall := rangeSetsG (m := N) _ _ HperW
      refine relax hall le_rfl ?_ le_rfl
      rintro f ⟨w, hw, j, hj, b, hb, rfl⟩; exact ⟨w, hw, j, hj, b, hb, rfl⟩
    exact relax (seq Hprep3 Hsort3) le_rfl Set.subset_union_right le_rfl
  let S3 := S2 ∪ B3
  have hC3 := chain (hS0_sub.trans (Set.subset_union_left.trans Set.subset_union_left)) hC2 H3
  have h3_kl : ∀ w < N, ∀ j < D, ∀ b < k + 1, (fun v => keyListV v w j b) ∈ S3 := by
    intro w hw j _ b hb
    dsimp only [keyListV]
    by_cases hjS : j < S
    · simp only [hjS, ↓reduceIte]; exact Or.inr ⟨w, hw, j, hjS, b, hb, rfl⟩
    · simp only [hjS, ↓reduceIte]; exact Or.inl (Or.inl (Or.inl (h0_c _)))
  let st4Init : (Fin dim → Bool) → Nat → Rec := fun v idx =>
    if idx < N then
      (keyBits2 k false true (fun b => idx.testBit b), packList k (fun _ => sentBit k))
    else if idx < N + M then
      let qIdx := idx - N
      (keyBits2 k false false (fun b => if hb : b < k then rowInvV v (qIdx / S) (qIdx % S) ⟨b, hb⟩ else false),
       packList k (keyListV v (qIdx / S)))
    else
      (keyBits2 k true true (fun _ => false), packList k (fun _ => sentBit k))
  let s4Sorted : (Fin dim → Bool) → Nat → Rec := fun v => runNet (recKey (k + 2)) netE (st4Init v)
  let summaryPacked : (Fin dim → Bool) → Nat → Nat → Bool := fun v =>
    replaySwaps (netSwaps (recKey (k + 2)) netE (st4Init v)).reverse
      (fun idx => packList k ((scan4 k D q (s4Sorted v) (P - 1)).2 idx))
  let summaryV : (Fin dim → Bool) → Nat → Nat → Nat → Bool := fun v x => unpackList k (summaryPacked v x)
  let step4 := 1 + 3 * LW + (2 * netQ.length * (11 * (k + 1) + 1) + 2 ^ (q + 1) * (8 * (k + 1) + 2))
  let B4 : Set (Sig dim) := {f | ∃ idx < P, ∃ t < LW, f = fun v => summaryPacked v idx t}
  have H4 : Build S3 B4 (netE.length * (11 * (k + 2) + 6 * LW + 1) + (P - 1) * step4 + netE.length * (6 * LW)) := by
    have hK4 : ∀ idx < P, ∀ j < k + 2, (fun v => (st4Init v idx).1 j) ∈ S3 := by
      intro idx _ j _
      dsimp only [st4Init]
      by_cases c1 : idx < N
      · simp only [c1, ↓reduceIte]; exact Or.inl (Or.inl (Or.inl (h0_c _)))
      · by_cases c2 : idx < N + M
        · simp only [c1, c2, ↓reduceIte, keyBits2]
          by_cases hj0 : j = 0
          · simp only [hj0, ↓reduceIte]; exact Or.inl (Or.inl (Or.inl (h0_c false)))
          · by_cases hjk : j = k + 1
            · simp only [hjk, ↓reduceIte]; exact Or.inl (Or.inl (Or.inl (h0_c false)))
            · simp only [hj0, hjk, ↓reduceIte]
              by_cases hb : j - 1 < k
              · simp only [hb, ↓reduceDIte]
                have hqM : idx - N < M := by omega
                have hw : (idx - N) / S < N := Nat.div_lt_of_lt_mul (by rwa [hSN])
                have hlo : (idx - N) % S < S := Nat.mod_lt _ hSpos
                exact Or.inl (Or.inl (h1_row _ hw _ hlo ⟨j - 1, hb⟩))
              · simp only [hb, ↓reduceDIte]; exact Or.inl (Or.inl (Or.inl (h0_c false)))
        · simp only [c1, c2, ↓reduceIte]; exact Or.inl (Or.inl (Or.inl (h0_c _)))
    have hV4 : ∀ idx < P, ∀ t < LW, (fun v => (st4Init v idx).2 t) ∈ S3 := by
      intro idx _ t ht
      dsimp only [st4Init]
      by_cases c1 : idx < N
      · simp only [c1, ↓reduceIte]; exact Or.inl (Or.inl (Or.inl (h0_c _)))
      · by_cases c2 : idx < N + M
        · simp only [c1, c2, ↓reduceIte, packList]
          have hqM : idx - N < M := by omega
          have hw : (idx - N) / S < N := Nat.div_lt_of_lt_mul (by rwa [hSN])
          have hj : t / (k + 1) < D := Nat.div_lt_of_lt_mul (by dsimp [LW] at ht; rwa [Nat.mul_comm])
          have hb : t % (k + 1) < k + 1 := Nat.mod_lt t (Nat.succ_pos k)
          exact h3_kl _ hw _ hj _ hb
        · simp only [c1, c2, ↓reduceIte]; exact Or.inl (Or.inl (Or.inl (h0_c _)))
    have Hnet4 := netCircuit (A := S3) (k + 2) LW P netE hnetE st4Init hK4 hV4
      (Or.inl (Or.inl (Or.inl (h0_c false))))
    let B4a :=
      ({f | ∃ idx < P, ∃ j < k + 2, f = fun v => (s4Sorted v idx).1 j} ∪
       {f | ∃ idx < P, ∃ t < LW, f = fun v => (s4Sorted v idx).2 t}) ∪
      {f | ∃ t < netE.length,
        f = (fun v => ((netSwaps (recKey (k + 2)) netE (st4Init v)).getD t (0, 0, false)).2.2) ∨
        f = (fun v => !(((netSwaps (recKey (k + 2)) netE (st4Init v)).getD t (0, 0, false)).2.2))}
    have Hsc4 := scan4Circuit (A := S3 ∪ B4a) k D q P hDq s4Sorted
      (fun idx hidx => Or.inr (Or.inl (Or.inl ⟨idx, hidx, 0, by omega, rfl⟩)))
      (fun idx hidx j hj b hb => by
        have ht : j * (k + 1) + b < LW := by
          have hm := Nat.mul_le_mul_right (k + 1) (show j + 1 ≤ D by omega)
          rw [Nat.succ_mul] at hm; dsimp [LW]; omega
        exact Or.inr (Or.inl (Or.inr ⟨idx, hidx, j * (k + 1) + b, ht, rfl⟩)))
      (Or.inl (Or.inl (Or.inl (Or.inl (h0_c false)))))
      (Or.inl (Or.inl (Or.inl (Or.inl (h0_c true)))))
      (P - 1) (by omega)
    let B4b :=
      {f | ∃ j < D, ∃ b < k + 1, f = fun v => (scan4 k D q (s4Sorted v) (P - 1)).1 j b} ∪
      {f | ∃ idx ≤ P - 1, ∃ j < D, ∃ b < k + 1, f = fun v => (scan4 k D q (s4Sorted v) (P - 1)).2 idx j b}
    have Hrep4 := replayRevCircuit (A := S3 ∪ (B4a ∪ B4b)) (k + 2) LW P netE hnetE st4Init
      (fun t ht => ⟨Or.inr (Or.inl (Or.inr ⟨t, ht, Or.inl rfl⟩)),
                    Or.inr (Or.inl (Or.inr ⟨t, ht, Or.inr rfl⟩))⟩)
      (fun v idx => packList k ((scan4 k D q (s4Sorted v) (P - 1)).2 idx))
      (fun idx hidx t ht => by
        have hj : t / (k + 1) < D := Nat.div_lt_of_lt_mul (by dsimp [LW] at ht; rwa [Nat.mul_comm])
        have hb : t % (k + 1) < k + 1 := Nat.mod_lt t (Nat.succ_pos k)
        exact Or.inr (Or.inr (Or.inr ⟨idx, by omega, t / (k + 1), hj, t % (k + 1), hb, rfl⟩)))
    exact relax (seq (seq Hnet4 Hsc4) Hrep4) le_rfl Set.subset_union_right (by dsimp only [step4, netQ, LW]; omega)
  let S4 := S3 ∪ B4
  have hC4 := chain (hS0_sub.trans (Set.subset_union_left.trans (Set.subset_union_left.trans Set.subset_union_left))) hC3 H4
  have h4_sum : ∀ x < N, ∀ t < LW, (fun v => summaryPacked v x t) ∈ S4 :=
    fun x hx t ht => Or.inr ⟨x, by omega, t, ht, rfl⟩
  have h4_sumJB : ∀ x < N, ∀ j < D, ∀ b < k + 1, (fun v => summaryV v x j b) ∈ S4 := by
    intro x hx j hj b hb
    have ht : j * (k + 1) + b < LW := by
      have hm := Nat.mul_le_mul_right (k + 1) (show j + 1 ≤ D by omega)
      rw [Nat.succ_mul] at hm; dsimp [LW]; omega
    exact h4_sum x hx (j * (k + 1) + b) ht
  let eligV : (Fin dim → Bool) → Nat → Bool := fun v x =>
    keepRowV x v && !(summaryV v x 0 k) && summaryV v x degreeCap k
  let keyBits5 : (Fin dim → Bool) → Nat → Nat → Bool := fun v x t =>
    if t < k then x.testBit t
    else if t < k + LW then summaryPacked v x (t - k)
    else if t = k + LW then !(eligV v x)
    else false
  let st5Init : (Fin dim → Bool) → Nat → Rec := fun v x => (keyBits5 v x, fun _ => false)
  let s5Sorted : (Fin dim → Bool) → Nat → Rec := fun v => runNet (recKey W5) netK (st5Init v)
  let isFirst5 : (Fin dim → Bool) → Nat → Bool := fun v idx =>
    !((s5Sorted v idx).1 (k + LW)) &&
      if idx = 0 then true
      else decide (bitsVal (fun t => (s5Sorted v idx).1 (k + t)) LW ≠
                   bitsVal (fun t => (s5Sorted v (idx - 1)).1 (k + t)) LW)
  let markOutV : (Fin dim → Bool) → Nat → Bool := fun v x =>
    replaySwaps (netSwaps (recKey W5) netK (st5Init v)).reverse (fun idx (_ : Nat) => isFirst5 v idx) x 0
  let countOutV : (Fin dim → Bool) → Nat → Bool := fun v i => popBits (markOutV v) 0 k i
  let B5 : Set (Sig dim) :=
    {f | ∃ x < N, f = fun v => markOutV v x} ∪ {f | ∃ i < k + 1, f = fun v => countOutV v i}
  have H5 : Build S4 B5 (N * 4 + netK.length * (11 * W5 + 1) + N * (5 * LW + 2) + netK.length * 6 + 24 * N) := by
    let B5a : Set (Sig dim) := {f | ∃ x < N, f = fun v => !(eligV v x)}
    have Helig : Build S4 B5a (N * 4) := by
      have Hper : ∀ x < N, Build S4 {fun v => !(eligV v x)} 4 := by
        intro x hx
        have h1 : Build S4 {nt (fun v => summaryV v x 0 k)} 1 :=
          notG (h4_sumJB x hx 0 hD1 k (Nat.lt_succ_self k))
        have h2 : Build (S4 ∪ {nt (fun v => summaryV v x 0 k)})
            {an (keepRowV x) (nt (fun v => summaryV v x 0 k))} 1 :=
          andG (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (h0_kr x)))))) (Or.inr rfl)
        have h3 : Build (S4 ∪ ({nt (fun v => summaryV v x 0 k)} ∪ {an (keepRowV x) (nt (fun v => summaryV v x 0 k))}))
            {fun v => eligV v x} 1 :=
          andG (Or.inr (Or.inr rfl))
            (Or.inl (h4_sumJB x hx degreeCap (Nat.lt_succ_self degreeCap) k (Nat.lt_succ_self k)))
        have h4 : Build (S4 ∪ (({nt (fun v => summaryV v x 0 k)} ∪ {an (keepRowV x) (nt (fun v => summaryV v x 0 k))}) ∪
            {fun v => eligV v x})) {fun v => !(eligV v x)} 1 :=
          notG (Or.inr (Or.inr rfl))
        exact relax (seq (seq (seq h1 h2) h3) h4) le_rfl (Set.singleton_subset_iff.mpr (Or.inr rfl)) (by omega)
      exact rangeG (m := N) (fun x v => !(eligV v x)) 4 Hper
    have hK5 : ∀ x < N, ∀ t < W5, (fun v => (st5Init v x).1 t) ∈ S4 ∪ B5a := by
      intro x hx t _
      dsimp only [st5Init, keyBits5]
      by_cases c1 : t < k
      · simp only [c1, ↓reduceIte]; exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (h0_c _)))))
      · by_cases c2 : t < k + LW
        · simp only [c1, c2, ↓reduceIte]; exact Or.inl (h4_sum x hx (t - k) (by omega))
        · by_cases c3 : t = k + LW
          · simp only [c1, c2, ↓reduceIte]; simp only [c3, ↓reduceIte]; exact Or.inr ⟨x, hx, rfl⟩
          · simp only [c1, c2, c3, ↓reduceIte]; exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (h0_c false)))))
    have Hnet5 := netCircuit (A := S4 ∪ B5a) W5 0 N netK hnetK st5Init hK5 (fun _ _ _ hj => by omega)
      (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (h0_c false))))))
    let B5b :=
      ({f | ∃ idx < N, ∃ t < W5, f = fun v => (s5Sorted v idx).1 t} ∪
       {f | ∃ idx < N, ∃ t < 0, f = fun v => (s5Sorted v idx).2 t}) ∪
      {f | ∃ t < netK.length,
        f = (fun v => ((netSwaps (recKey W5) netK (st5Init v)).getD t (0, 0, false)).2.2) ∨
        f = (fun v => !(((netSwaps (recKey W5) netK (st5Init v)).getD t (0, 0, false)).2.2))}
    let A5b := S4 ∪ (B5a ∪ B5b)
    have Hmark : Build A5b {f | ∃ idx < N, f = fun v => isFirst5 v idx} (N * (5 * LW + 2)) :=
      rangeG (m := N) (fun idx v => isFirst5 v idx) (5 * LW + 2) fun idx hidx => by
        have hnel : (fun v => (s5Sorted v idx).1 (k + LW)) ∈ A5b :=
          Or.inr (Or.inr (Or.inl (Or.inl ⟨idx, hidx, k + LW, by dsimp [W5]; omega, rfl⟩)))
        by_cases h0 : idx = 0
        · subst h0
          have he : (fun v => isFirst5 v 0) = nt (fun v => (s5Sorted v 0).1 (k + LW)) := by
            funext v; simp [isFirst5, nt]
          rw [he]; exact relax (notG hnel) le_rfl le_rfl (by omega)
        · have hnt : Build A5b {nt (fun v => (s5Sorted v idx).1 (k + LW))} 1 := notG hnel
          have hne : Build (A5b ∪ {nt (fun v => (s5Sorted v idx).1 (k + LW))})
              {fun v => decide (bitsVal (fun t => (s5Sorted v idx).1 (k + t)) LW ≠
                                bitsVal (fun t => (s5Sorted v (idx - 1)).1 (k + t)) LW)} (5 * LW) :=
            neWordG (fun t v => (s5Sorted v idx).1 (k + t)) (fun t v => (s5Sorted v (idx - 1)).1 (k + t)) LW
              (fun t ht => Or.inl (Or.inr (Or.inr (Or.inl (Or.inl ⟨idx, hidx, k + t, by dsimp [W5]; omega, rfl⟩)))))
              (fun t ht => Or.inl (Or.inr (Or.inr (Or.inl (Or.inl ⟨idx - 1, by omega, k + t, by dsimp [W5]; omega, rfl⟩)))))
              (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (h0_c false)))))))
          have hand : Build (A5b ∪ ({nt (fun v => (s5Sorted v idx).1 (k + LW))} ∪
              {fun v => decide (bitsVal (fun t => (s5Sorted v idx).1 (k + t)) LW ≠
                                bitsVal (fun t => (s5Sorted v (idx - 1)).1 (k + t)) LW)}))
              {fun v => isFirst5 v idx} 1 := by
            have he : (fun v => isFirst5 v idx) =
                an (nt (fun v => (s5Sorted v idx).1 (k + LW)))
                   (fun v => decide (bitsVal (fun t => (s5Sorted v idx).1 (k + t)) LW ≠
                                     bitsVal (fun t => (s5Sorted v (idx - 1)).1 (k + t)) LW)) := by
              funext v; simp [isFirst5, an, nt, h0]
            rw [he]; exact andG (Or.inr (Or.inl rfl)) (Or.inr (Or.inr rfl))
          exact relax (seq (seq hnt hne) hand) le_rfl (Set.singleton_subset_iff.mpr (Or.inr rfl)) (by omega)
    let B5c := {f | ∃ idx < N, f = fun v => isFirst5 v idx}
    let A5c := S4 ∪ ((B5a ∪ B5b) ∪ B5c)
    have Hrep5 := replayRevCircuit (A := A5c) W5 1 N netK hnetK st5Init
      (fun t ht => ⟨Or.inr (Or.inl (Or.inr (Or.inr ⟨t, ht, Or.inl rfl⟩))),
                    Or.inr (Or.inl (Or.inr (Or.inr ⟨t, ht, Or.inr rfl⟩)))⟩)
      (fun v idx _ => isFirst5 v idx)
      (fun idx hidx _ _ => Or.inr (Or.inr ⟨idx, hidx, rfl⟩))
    let B5d := {f | ∃ idx < N, ∃ j < 1, f = fun v =>
      replaySwaps (netSwaps (recKey W5) netK (st5Init v)).reverse (fun i _ => isFirst5 v i) idx j}
    let A5d := S4 ∪ (((B5a ∪ B5b) ∪ B5c) ∪ B5d)
    have Hpop : Build A5d {f | ∃ i < k + 1, f = fun v => countOutV v i} (24 * N) :=
      popCountG (A := A5d) (fun x v => markOutV v x)
        (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (h0_c false)))))) k 0
        (fun j hj => by
          have he : (fun v => markOutV v (0 + j)) = (fun v => markOutV v j) := by funext v; simp
          rw [he]; exact Or.inr (Or.inr ⟨j, hj, 0, Nat.zero_lt_one, rfl⟩))
    have Htot5 := seq (seq (seq (seq Helig Hnet5) Hmark) Hrep5) Hpop
    refine relax Htot5 le_rfl ?_ (by simp only [Nat.mul_zero, Nat.add_zero]; omega)
    rintro f (⟨x, hx, rfl⟩ | ⟨i, hi, rfl⟩)
    · exact Or.inl (Or.inr ⟨x, hx, 0, Nat.zero_lt_one, rfl⟩)
    · exact Or.inr ⟨i, hi, rfl⟩
  let S5 := S4 ∪ B5
  have hC5 := chain (hS0_sub.trans (Set.subset_union_left.trans (Set.subset_union_left.trans
    (Set.subset_union_left.trans Set.subset_union_left)))) hC4 H5
  obtain ⟨c, hc, HS⟩ := hC5.run (schedStart (F := id) (fun i : Fin dim => fun v => v i) (by intros; rfl)) le_rfl
  rcases HS with ⟨gs, hgs, hread, hfan, hwire⟩
  let C : Circuit := ⟨gs, 0⟩
  have hCsize : C.size = c := by simp [C, Circuit.size, hgs]
  have hout_ex : ∀ j : Fin numOut, ∃ idx < dim + C.size,
      ∀ v : Fin dim → Bool, (C.wires (List.ofFn v)).getD idx false =
        if j.val < N then markOutV v j.val else countOutV v (j.val - N) := by
    intro j
    by_cases hj : j.val < N
    · have hmem : (fun v => markOutV v j.val) ∈ inputs ∪ S5 := Or.inr (Or.inr (Or.inl ⟨j.val, hj, rfl⟩))
      obtain ⟨idx, hidx, hval⟩ := hwire _ hmem
      refine ⟨idx, by rw [hCsize]; omega, fun v => ?_⟩
      simp only [hj, ↓reduceIte]; exact hval v
    · have hmem : (fun v => countOutV v (j.val - N)) ∈ inputs ∪ S5 :=
        Or.inr (Or.inr (Or.inr ⟨j.val - N, by dsimp [numOut] at *; omega, rfl⟩))
      obtain ⟨idx, hidx, hval⟩ := hwire _ hmem
      refine ⟨idx, by rw [hCsize]; omega, fun v => ?_⟩
      simp only [hj, ↓reduceIte]; exact hval v
  let out : Fin numOut → Fin (dim + C.size) :=
    fun j => ⟨Classical.choose (hout_ex j), (Classical.choose_spec (hout_ex j)).1⟩
  refine ⟨C, out, hfan, hread, ?_, ?_, ?_⟩
  · simp only [C]; dsimp [dim]; omega
  · rw [hCsize]
    exact hc.trans (gate_budget_bound k r prefixLen degreeCap hk_odd hp_pos hp_le hd_le)
  · intro masks rowTarget colTarget keepRow keepCol input neigh mark flags answer j
    have hlen_in : input.length = dim := by
      dsimp only [input, bits, dim]
      simp only [List.length_append, List.length_map, List.length_range, flatMap_bits_length]
      have hfr : (List.finRange N).length = N := List.length_finRange
      rw [hfr]; omega
    let v : Fin dim → Bool := fun idx => input.getD idx.val false
    have hv_eq : List.ofFn v = input := by
      apply List.ext_getElem (by simp [hlen_in])
      intro idx h1 h2
      rw [List.getElem_ofFn]
      simp only [v, List.getD_eq_getElem _ _ h2]
    let A0 := (List.range (2 * r)).flatMap (fun j => bits k (masks j).val)
    let A1 := bits prefixLen rowTarget.val
    let A2 := bits prefixLen colTarget.val
    let A3 := (List.finRange N).map keepRow
    let A4 := (List.finRange N).map keepCol
    have hLA0 : A0.length = 2 * r * k := flatMap_bits_length (2 * r) k (fun j => (masks j).val)
    have hLA1 : A1.length = prefixLen := bits_length prefixLen rowTarget.val
    have hLA2 : A2.length = prefixLen := bits_length prefixLen colTarget.val
    have hLA3 : A3.length = N := by dsimp only [A3]; rw [List.length_map, List.length_finRange]
    have hLA4 : A4.length = N := by dsimp only [A4]; rw [List.length_map, List.length_finRange]
    have hinput_eq : input = A0 ++ (A1 ++ (A2 ++ (A3 ++ A4))) := by
      simp only [input, A0, A1, A2, A3, A4, List.append_assoc]
    have hv_mask : ∀ j < 2 * r, ∀ i : Fin k, maskV j i v = (masks j).val.testBit i.val := by
      intro j hj i
      dsimp only [maskV, v]
      simp only [hj, ↓reduceDIte]
      have hlt : j * k + i.val < A0.length := by
        rw [hLA0]
        have hm := Nat.mul_le_mul_right k (show j + 1 ≤ 2 * r by omega)
        rw [Nat.succ_mul] at hm; omega
      rw [hinput_eq, List.getD_append _ _ _ _ hlt]
      exact flatMap_bits_getD (2 * r) k (fun t => (masks t).val) j i.val hj i.isLt
    have hv_rt : ∀ i : Fin prefixLen, rowTargV i v = rowTarget.val.testBit i.val := by
      intro i
      dsimp only [rowTargV, v]
      rw [hinput_eq, List.getD_append_right _ _ _ _ (by omega), hLA0, Nat.add_sub_cancel_left,
          List.getD_append _ _ _ _ (by rw [hLA1]; exact i.isLt)]
      simp [A1, bits, List.getD_eq_getElem?_getD, i.isLt]
    have hv_ct : ∀ i : Fin prefixLen, colTargV i v = colTarget.val.testBit i.val := by
      intro i
      dsimp only [colTargV, v]
      rw [hinput_eq, List.getD_append_right _ _ _ _ (by omega), hLA0,
          show 2 * r * k + prefixLen + i.val - 2 * r * k = prefixLen + i.val by omega,
          List.getD_append_right _ _ _ _ (by omega), hLA1, Nat.add_sub_cancel_left,
          List.getD_append _ _ _ _ (by rw [hLA2]; exact i.isLt)]
      simp [A2, bits, List.getD_eq_getElem?_getD, i.isLt]
    have hv_kr : ∀ x : X, keepRowV x.val v = keepRow x := by
      intro x
      dsimp only [keepRowV, v]
      simp only [x.isLt, ↓reduceDIte]
      rw [hinput_eq, List.getD_append_right _ _ _ _ (by omega), hLA0,
          show 2 * r * k + 2 * prefixLen + x.val - 2 * r * k = 2 * prefixLen + x.val by omega,
          List.getD_append_right _ _ _ _ (by omega), hLA1,
          show 2 * prefixLen + x.val - prefixLen = prefixLen + x.val by omega,
          List.getD_append_right _ _ _ _ (by omega), hLA2, Nat.add_sub_cancel_left,
          List.getD_append _ _ _ _ (by rw [hLA3]; exact x.isLt)]
      exact finRange_map_getD N keepRow false x.val x.isLt
    have hv_kc : ∀ y : X, keepColV y.val v = keepCol y := by
      intro y
      dsimp only [keepColV, v]
      simp only [y.isLt, ↓reduceDIte]
      rw [hinput_eq, List.getD_append_right _ _ _ _ (by omega), hLA0,
          show 2 * r * k + 2 * prefixLen + N + y.val - 2 * r * k = 2 * prefixLen + N + y.val by omega,
          List.getD_append_right _ _ _ _ (by omega), hLA1,
          show 2 * prefixLen + N + y.val - prefixLen = prefixLen + N + y.val by omega,
          List.getD_append_right _ _ _ _ (by omega), hLA2,
          show prefixLen + N + y.val - prefixLen = N + y.val by omega,
          List.getD_append_right _ _ _ _ (by omega), hLA3, Nat.add_sub_cancel_left]
      exact finRange_map_getD N keepCol false y.val y.isLt
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
    have hsel_eq : ∀ w < N, ∀ lo < S, selColV v w lo = keepCol ⟨toNat (colInvV v w lo), toNat_lt _⟩ := by
      intro w hw lo hlo
      have hperm2 := bitonicPerm (recKey (k + 2)) P netE hnetE (st2Init v)
      rcases hperm2 with ⟨h2_fi, h2_if, h2_flt, h2_ilt, h2_run, h2_inv, h2_rep⟩
      let pFwd2 := replaySwaps (netSwaps (recKey (k + 2)) netE (st2Init v)) id
      let pInv2 := replaySwaps (netSwaps (recKey (k + 2)) netE (st2Init v)).reverse id
      have hsorted2 := bitonicSort_sorted (recKey (k + 2)) e (st2Init v)
      have hst2_tab : ∀ idx (hidx : idx < N),
          (st2Init v idx).1 (k + 1) = false ∧ (st2Init v idx).1 0 = false ∧
          recKey (k + 2) (st2Init v idx) = 2 * idx ∧ (st2Init v idx).2 0 = keepCol ⟨idx, hidx⟩ := by
        intro idx hidx
        refine ⟨by simp [st2Init, hidx, keyBits2], by simp [st2Init, hidx, keyBits2], ?_, ?_⟩
        · dsimp only [recKey, st2Init]; simp only [hidx, ↓reduceIte]
          rw [keyBits2_val, bitsVal_of_testBit idx k hidx]; simp
        · dsimp only [st2Init]; simp only [hidx, ↓reduceIte]; exact hv_kc ⟨idx, hidx⟩
      have htab_real : ∀ t < P, (s2Sorted v t).1 (k + 1) = false → (s2Sorted v t).1 0 = false →
          ∃ addr < N, recKey (k + 2) (s2Sorted v t) = 2 * addr ∧ (s2Sorted v t).2 0 = keepColV addr v := by
        intro t _ hd0 ht0
        change (runNet (recKey (k + 2)) netE (st2Init v) t).1 _ = _ at hd0 ht0
        rw [h2_run t] at hd0 ht0
        change ∃ addr < N, recKey (k + 2) (runNet (recKey (k + 2)) netE (st2Init v) t) = 2 * addr ∧
          (runNet (recKey (k + 2)) netE (st2Init v) t).2 0 = keepColV addr v
        rw [h2_run t]
        let orig := pFwd2 t
        by_cases c1 : orig < N
        · rcases hst2_tab orig c1 with ⟨_, _, hk2, hv2⟩
          exact ⟨orig, c1, hk2, hv2.trans (hv_kc ⟨orig, c1⟩).symm⟩
        · by_cases c2 : orig < N + M
          · have : (st2Init v orig).1 0 = true := by simp [st2Init, c1, c2, keyBits2]
            rw [this] at ht0; cases ht0
          · have : (st2Init v orig).1 0 = true := by simp [st2Init, c1, c2, keyBits2]
            rw [this] at ht0; cases ht0
      have htab_ex : ∀ addr < N, ∃ t < P, (s2Sorted v t).1 (k + 1) = false ∧ (s2Sorted v t).1 0 = false ∧
          recKey (k + 2) (s2Sorted v t) = 2 * addr := by
        intro addr haddr
        refine ⟨pInv2 addr, h2_ilt addr (by omega), ?_⟩
        change (runNet (recKey (k + 2)) netE (st2Init v) (pInv2 addr)).1 (k + 1) = false ∧
          (runNet (recKey (k + 2)) netE (st2Init v) (pInv2 addr)).1 0 = false ∧
          recKey (k + 2) (runNet (recKey (k + 2)) netE (st2Init v) (pInv2 addr)) = 2 * addr
        rw [h2_inv addr]
        rcases hst2_tab addr haddr with ⟨h1, h2, h3, _⟩; exact ⟨h1, h2, h3⟩
      have hsc := (scan2_answer k P (s2Sorted v) (fun a => keepColV a v) hsorted2 htab_real htab_ex P le_rfl).1
      let qIdx := w * S + lo
      have hqM : qIdx < M := by
        have hm := Nat.mul_le_mul_right S (show w + 1 ≤ N by omega)
        rw [Nat.succ_mul, hNS] at hm; dsimp [qIdx]; omega
      have hdiv : qIdx / S = w := by
        dsimp [qIdx]; rw [Nat.add_comm, Nat.mul_comm, Nat.add_mul_div_left _ _ hSpos, Nat.div_eq_of_lt hlo, Nat.zero_add]
      have hmod : qIdx % S = lo := by
        dsimp [qIdx]; rw [Nat.add_comm, Nat.mul_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlo]
      dsimp only [selColV, selColArr]
      have hrep := h2_rep (fun idx (_ : Nat) => (scan2 k (s2Sorted v) P).2 idx) (N + qIdx)
      rw [congrFun hrep 0]
      have hq_lt : N + qIdx < P := by omega
      have hq_rec : (st2Init v (N + qIdx)).1 (k + 1) = false ∧ (st2Init v (N + qIdx)).1 0 = true ∧
          recKey (k + 2) (st2Init v (N + qIdx)) = 2 * toNat (colInvV v w lo) + 1 := by
        have hnot : ¬ (N + qIdx < N) := by omega
        have hlt : N + qIdx < N + M := by omega
        refine ⟨by simp [st2Init, hnot, hlt, keyBits2], by simp [st2Init, hnot, hlt, keyBits2], ?_⟩
        dsimp only [recKey, st2Init]
        simp only [hnot, hlt, ↓reduceIte, Nat.add_sub_cancel_left, hdiv, hmod]
        rw [keyBits2_val]
        have hbv : bitsVal (fun b => if hb : b < k then colInvV v w lo ⟨b, hb⟩ else false) k = toNat (colInvV v w lo) := by
          rw [← bitsVal_of_testBit (toNat (colInvV v w lo)) k (toNat_lt _)]
          apply bitsVal_congr; intro b hb
          simp only [hb, ↓reduceDIte, testBit_toNat]
        rw [hbv]; simp
      have hans := hsc (pInv2 (N + qIdx)) (h2_ilt _ hq_lt)
        (by change (runNet (recKey (k + 2)) netE (st2Init v) _).1 _ = _; rw [h2_inv]; exact hq_rec.1)
        (by change (runNet (recKey (k + 2)) netE (st2Init v) _).1 _ = _; rw [h2_inv]; exact hq_rec.2.1)
        (toNat (colInvV v w lo)) (toNat_lt _)
        (by change recKey (k + 2) (runNet (recKey (k + 2)) netE (st2Init v) _) = _; rw [h2_inv]; exact hq_rec.2.2)
      rw [hans]; exact hv_kc ⟨toNat (colInvV v w lo), toNat_lt _⟩
    let colSet : Nat → Finset Nat := fun w =>
      (Finset.range N).filter (fun y => if hy : y < N then
        keepCol ⟨y, hy⟩ = true ∧ ∃ lo < S, toNat (colInvV v w lo) = y else false)
    have hcolSet_lt : ∀ w y, y ∈ colSet w → y < N := fun w y hy => Finset.mem_range.mp (Finset.mem_filter.mp hy).1
    have h3_topD : ∀ w < N, IsTopD D N (colSet w) (fun j => bitsVal (keyListV v w j) (k + 1)) := by
      intro w hw
      let arr : Nat → Nat := fun lo => recKey (k + 1) (st3Init v w lo)
      have harr_val : ∀ lo < S, arr lo = if selColV v w lo then toNat (colInvV v w lo) else N := by
        intro lo _
        dsimp only [arr, recKey, st3Init]
        cases hsel : selColV v w lo
        · simp only [Bool.false_eq_true, Bool.not_false, Bool.false_and, ↓reduceIte]
          have hcon : bitsVal (fun b => if b = k then true else if hb : b < k then false else false) (k + 1) =
              bitsVal (sentBit k) (k + 1) := by
            apply bitsVal_congr; intro b hb
            by_cases hbk : b = k
            · simp [hbk, sentBit]
            · simp [hbk, sentBit]
          rw [hcon]; exact bitsVal_sentBit k
        · simp only [Bool.not_true, Bool.true_and, ↓reduceIte]
          change bitsVal _ k + _ = _
          simp only [↓reduceIte, Bool.false_eq_true, Nat.add_zero]
          rw [← bitsVal_of_testBit (toNat (colInvV v w lo)) k (toNat_lt _)]
          apply bitsVal_congr; intro b hb
          have hne : b ≠ k := by omega
          simp only [hne, hb, ↓reduceIte, ↓reduceDIte, testBit_toNat]
      have hbound : ∀ lo < S, arr lo ≤ N := by
        intro lo hlo; rw [harr_val lo hlo]
        cases selColV v w lo
        · exact le_rfl
        · exact le_of_lt (toNat_lt _)
      have hdist : ∀ i < S, ∀ j < S, arr i < N → arr i = arr j → i = j := by
        intro i hi j hj hlt heq
        rw [harr_val i hi] at hlt heq
        rw [harr_val j hj] at heq
        cases hsi : selColV v w i
        · rw [hsi] at hlt; simp at hlt
        · cases hsj : selColV v w j
          · rw [hsi, hsj] at heq; simp only [↓reduceIte, Bool.false_eq_true] at heq
            exact absurd heq (ne_of_lt (toNat_lt _))
          · rw [hsi, hsj] at heq; simp only [↓reduceIte] at heq
            rw [hcolInv_eq, hcolInv_eq] at heq
            exact invRun_inj_lo hk hk6 r (fun t => ofNat k (masks t).val) true colTarget (ofNat k w) hi hj heq
      have hmem : ∀ y, y ∈ colSet w ↔ ∃ lo < S, arr lo = y ∧ y < N := by
        intro y
        simp only [colSet, Finset.mem_filter, Finset.mem_range]
        constructor
        · rintro ⟨hy, hrest⟩
          simp only [hy, ↓reduceDIte] at hrest
          rcases hrest with ⟨hkc, lo, hlo, heq⟩
          refine ⟨lo, hlo, ?_, hy⟩
          rw [harr_val lo hlo, hsel_eq w hw lo hlo]
          have hfin : (⟨toNat (colInvV v w lo), toNat_lt _⟩ : X) = ⟨y, hy⟩ := Fin.ext heq
          rw [hfin, hkc]; simp [heq]
        · rintro ⟨lo, hlo, heq, hy⟩
          refine ⟨hy, ?_⟩
          simp only [hy, ↓reduceDIte]
          rw [harr_val lo hlo] at heq
          cases hsi : selColV v w lo
          · rw [hsi] at heq; simp at heq; omega
          · rw [hsi] at heq; simp only [↓reduceIte] at heq
            rw [hsel_eq w hw lo hlo] at hsi
            have hfin : (⟨toNat (colInvV v w lo), toNat_lt _⟩ : X) = ⟨y, hy⟩ := Fin.ext heq
            rw [hfin] at hsi
            exact ⟨hsi, lo, hlo, heq⟩
      have htop := IsTopD_of_sorted_distinct D N s (colSet w) arr hbound hdist hmem
      have hmap : ∀ j, recKey (k + 1) (s3Sorted v w j) = runNet id netS arr j := by
        have hgen : ∀ (net : List (Nat × Nat × Bool)) (st : Nat → Rec),
            (fun idx => recKey (k + 1) (runNet (recKey (k + 1)) net st idx)) =
            runNet id net (fun idx => recKey (k + 1) (st idx)) := by
          intro net
          induction net with
          | nil => intro st; rfl
          | cons c rest ih =>
            rcases c with ⟨u, v', asc⟩
            intro st
            simp only [runNet]
            rw [ih, ← applySwap_comp]
            rfl
        exact congrFun (hgen netS (st3Init v w))
      refine IsTopD_congr htop fun j _ => ?_
      dsimp only [keyListV, S]
      by_cases hjS : j < 2 ^ s
      · simp only [hjS, ↓reduceIte]; exact (hmap j).symm
      · simp only [hjS, ↓reduceIte]; exact (bitsVal_sentBit k).symm
    let neighNat : Nat → Finset Nat := fun x =>
      if hx : x < N then (neigh ⟨x, hx⟩).image Fin.val else ∅
    have hneighNat_lt : ∀ x y, y ∈ neighNat x → y < N := by
      intro x y hy
      dsimp only [neighNat] at hy
      by_cases hx : x < N
      · simp only [hx, ↓reduceDIte, Finset.mem_image] at hy
        rcases hy with ⟨y', _, rfl⟩; exact y'.isLt
      · simp only [hx, ↓reduceDIte] at hy; exact absurd hy (Finset.notMem_empty _)
    have hneighNat_eq : ∀ x (hx : x < N) y, y ∈ neighNat x ↔
        ∃ qIdx < M, toNat (rowInvV v (qIdx / S) (qIdx % S)) = x ∧ y ∈ colSet (qIdx / S) := by
      intro x hx y
      dsimp only [neighNat]
      simp only [hx, ↓reduceDIte, Finset.mem_image]
      constructor
      · rintro ⟨y', hy', rfl⟩
        simp only [neigh, Finset.mem_filter, Finset.mem_univ, true_and] at hy'
        rcases hy' with ⟨hkc, w, hr, hc⟩
        have hr' := (invRun_shift_iff hk hk6 hp_le r masks false rowTarget w ⟨x, hx⟩).mp hr
        have hc' := (invRun_shift_iff hk hk6 hp_le r masks true colTarget w y').mp hc
        rcases hr' with ⟨lo1, hlo1, hrx⟩
        rcases hc' with ⟨lo2, hlo2, hcy⟩
        let qIdx := w.val * S + lo1
        have hqM : qIdx < M := by
          have hwlt : w.val < N := w.isLt
          have hlo1' : lo1 < S := hlo1
          have hm := Nat.mul_le_mul_right S (show w.val + 1 ≤ N by omega)
          rw [Nat.succ_mul, hNS] at hm; dsimp [qIdx]; omega
        have hdiv : qIdx / S = w.val := by
          dsimp [qIdx]; rw [Nat.add_comm, Nat.mul_comm, Nat.add_mul_div_left _ _ hSpos, Nat.div_eq_of_lt hlo1, Nat.zero_add]
        have hmod : qIdx % S = lo1 := by
          dsimp [qIdx]; rw [Nat.add_comm, Nat.mul_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlo1]
        refine ⟨qIdx, hqM, ?_, ?_⟩
        · rw [hdiv, hmod, hrowInv_eq]; exact hrx.symm
        · rw [hdiv]; simp only [colSet, Finset.mem_filter, Finset.mem_range, y'.isLt, ↓reduceDIte, true_and]
          exact ⟨hkc, lo2, hlo2, by rw [hcolInv_eq]; exact hcy.symm⟩
      · rintro ⟨qIdx, hqM, hrx, hycol⟩
        have hw : qIdx / S < N := Nat.div_lt_of_lt_mul (by rwa [hSN])
        have hlo1 : qIdx % S < S := Nat.mod_lt _ hSpos
        simp only [colSet, Finset.mem_filter, Finset.mem_range] at hycol
        rcases hycol with ⟨hyN, hrest⟩
        simp only [hyN, ↓reduceDIte] at hrest
        rcases hrest with ⟨hkc, lo2, hlo2, hcy⟩
        refine ⟨⟨y, hyN⟩, ?_, rfl⟩
        simp only [neigh, Finset.mem_filter, Finset.mem_univ, true_and]
        refine ⟨hkc, ⟨qIdx / S, hw⟩, ?_, ?_⟩
        · exact (invRun_shift_iff hk hk6 hp_le r masks false rowTarget ⟨qIdx / S, hw⟩ ⟨x, hx⟩).mpr
            ⟨qIdx % S, hlo1, by rw [← hrowInv_eq]; exact hrx.symm⟩
        · exact (invRun_shift_iff hk hk6 hp_le r masks true colTarget ⟨qIdx / S, hw⟩ ⟨y, hyN⟩).mpr
            ⟨lo2, hlo2, by rw [← hcolInv_eq]; exact hcy.symm⟩
    have h4_topD : ∀ x < N, IsTopD D N (neighNat x) (fun j => bitsVal (summaryV v x j) (k + 1)) := by
      have hperm4 := bitonicPerm (recKey (k + 2)) P netE hnetE (st4Init v)
      rcases hperm4 with ⟨h4_fi, h4_if, h4_flt, h4_ilt, h4_run, h4_inv, h4_rep⟩
      let pFwd4 := replaySwaps (netSwaps (recKey (k + 2)) netE (st4Init v)) id
      let pInv4 := replaySwaps (netSwaps (recKey (k + 2)) netE (st4Init v)).reverse id
      have h4_fi' : ∀ idx, pFwd4 (pInv4 idx) = idx := h4_fi
      have h4_if' : ∀ idx, pInv4 (pFwd4 idx) = idx := h4_if
      have h4_ilt' : ∀ idx < P, pInv4 idx < P := h4_ilt
      have hsorted4 := bitonicSort_sorted (recKey (k + 2)) e (st4Init v)
      let initSet : Nat → Finset Nat := fun idx =>
        if idx < N then ∅ else if idx < N + M then colSet ((idx - N) / S) else ∅
      let recSet4 : Nat → Finset Nat := fun t => initSet (pFwd4 t)
      have hRec4_bound : ∀ t, ∀ y ∈ recSet4 t, y < N := by
        intro t y hy
        dsimp only [recSet4, initSet] at hy
        by_cases c1 : pFwd4 t < N
        · simp only [c1, ↓reduceIte] at hy; exact absurd hy (Finset.notMem_empty _)
        · by_cases c2 : pFwd4 t < N + M
          · simp only [c1, c2, ↓reduceIte] at hy; exact hcolSet_lt _ y hy
          · simp only [c1, c2, ↓reduceIte] at hy; exact absurd hy (Finset.notMem_empty _)
      have hRec4_topD : ∀ t, IsTopD D N (recSet4 t)
          (fun j => bitsVal (unpackList k (s4Sorted v t).2 j) (k + 1)) := by
        intro t
        have hst : s4Sorted v t = st4Init v (pFwd4 t) := h4_run t
        rw [hst]
        dsimp only [recSet4, initSet, st4Init]
        by_cases c1 : pFwd4 t < N
        · simp only [c1, ↓reduceIte]
          exact IsTopD_congr (IsTopD_empty D N) (fun j _ => by
            dsimp only [N]; rw [← bitsVal_sentBit k]; apply bitsVal_congr; intro b hb; exact (unpack_pack k (fun _ => sentBit k) j b hb).symm)
        · by_cases c2 : pFwd4 t < N + M
          · simp only [c1, c2, ↓reduceIte]
            have hw : (pFwd4 t - N) / S < N := Nat.div_lt_of_lt_mul (by rw [hSN]; omega)
            exact IsTopD_congr (h3_topD _ hw) (fun j _ => by
              apply bitsVal_congr; intro b hb; exact (unpack_pack k _ j b hb).symm)
          · simp only [c1, c2, ↓reduceIte]
            exact IsTopD_congr (IsTopD_empty D N) (fun j _ => by
              dsimp only [N]; rw [← bitsVal_sentBit k]; apply bitsVal_congr; intro b hb; exact (unpack_pack k (fun _ => sentBit k) j b hb).symm)
      have hscan4 := scan4_isTopD k D q hDq (s4Sorted v) recSet4 hRec4_bound hRec4_topD
      have hfoot_key : ∀ z < N, recKey (k + 2) (st4Init v z) = 2 * z + 1 ∧ (st4Init v z).1 0 = true := by
        intro z hz
        refine ⟨?_, by simp [st4Init, hz, keyBits2]⟩
        dsimp only [recKey, st4Init]; simp only [hz, ↓reduceIte]
        rw [keyBits2_val, bitsVal_of_testBit z k hz]; simp
      have hinc_key : ∀ qIdx < M, recKey (k + 2) (st4Init v (N + qIdx)) =
          2 * toNat (rowInvV v (qIdx / S) (qIdx % S)) ∧ (st4Init v (N + qIdx)).1 0 = false := by
        intro qIdx hqM
        have h1 : ¬ (N + qIdx < N) := by omega
        have h2 : N + qIdx < N + M := by omega
        refine ⟨?_, by simp [st4Init, h1, h2, keyBits2]⟩
        dsimp only [recKey, st4Init]; simp only [h1, h2, ↓reduceIte, Nat.add_sub_cancel_left]
        rw [keyBits2_val]
        have hbv : bitsVal (fun b => if hb : b < k then rowInvV v (qIdx / S) (qIdx % S) ⟨b, hb⟩ else false) k =
            toNat (rowInvV v (qIdx / S) (qIdx % S)) := by
          rw [← bitsVal_of_testBit (toNat (rowInvV v (qIdx / S) (qIdx % S))) k (toNat_lt _)]
          apply bitsVal_congr; intro b hb; simp only [hb, ↓reduceDIte, testBit_toNat]
        rw [hbv]; simp
      have hdum_key : ∀ idx, N + M ≤ idx → recKey (k + 2) (st4Init v idx) = 2 * N + 1 := by
        intro idx hidx
        have h1 : ¬ (idx < N) := by omega
        have h2 : ¬ (idx < N + M) := by omega
        dsimp only [recKey, st4Init]; simp only [h1, h2, ↓reduceIte]
        rw [keyBits2_val]
        have h0 : bitsVal (fun _ => false) k = 0 := by
          rw [← bitsVal_of_testBit 0 k (Nat.two_pow_pos k)]; apply bitsVal_congr; intro b _; simp
        rw [h0]; simp [N, Nat.pow_succ, Nat.mul_comm]
      intro x hx
      have hxP : x < P := by omega
      have h4_ilt_x : pInv4 x < P := h4_ilt' x hxP
      have hsum_at : ∀ j < D, bitsVal (summaryV v x j) (k + 1) =
          bitsVal ((scan4 k D q (s4Sorted v) (pInv4 x)).1 j) (k + 1) := by
        intro j _
        apply bitsVal_congr; intro b hb
        dsimp only [summaryV, summaryPacked, unpackList]
        have hrep := h4_rep (fun idx => packList k ((scan4 k D q (s4Sorted v) (P - 1)).2 idx)) x
        rw [congrFun hrep (j * (k + 1) + b)]
        rw [show packList k ((scan4 k D q (s4Sorted v) (P - 1)).2 (pInv4 x)) (j * (k + 1) + b) =
            unpackList k (packList k ((scan4 k D q (s4Sorted v) (P - 1)).2 (pInv4 x))) j b from rfl]
        rw [unpack_pack k _ j b hb, scan4_at k D q (s4Sorted v) (P - 1) (pInv4 x) (by omega)]
      refine IsTopD_congr ?_ (fun j hj => (hsum_at j hj).symm)
      have hseg_eq : segUnion (s4Sorted v) recSet4 (pInv4 x) = neighNat x := by
        have hkey_x : recKey (k + 2) (s4Sorted v (pInv4 x)) = 2 * x + 1 := by
          change recKey (k + 2) (runNet (recKey (k + 2)) netE (st4Init v) (pInv4 x)) = _
          rw [h4_inv x]; exact (hfoot_key x hx).1
        have hrec_x : recSet4 (pInv4 x) = ∅ := by
          dsimp only [recSet4, initSet]; rw [h4_fi' x]; simp [hx]
        by_cases hx0 : x = 0
        · subst hx0
          have hnoF : ∀ t, 0 ≤ t → t < pInv4 0 → (s4Sorted v t).1 0 = false ∧
              N ≤ pFwd4 t ∧ pFwd4 t < N + M ∧ toNat (rowInvV v ((pFwd4 t - N) / S) ((pFwd4 t - N) % S)) = 0 := by
            intro t _ ht
            have hle := hsorted4 t (pInv4 0) (by omega) h4_ilt_x
            change recKey (k + 2) (s4Sorted v t) ≤ recKey (k + 2) (s4Sorted v (pInv4 0)) at hle
            rw [hkey_x] at hle
            have hrun : s4Sorted v t = st4Init v (pFwd4 t) := h4_run t
            rw [hrun] at hle ⊢
            by_cases c1 : pFwd4 t < N
            · have hk1 := (hfoot_key (pFwd4 t) c1).1
              have h0 : pFwd4 t = 0 := by omega
              have hti : t = pInv4 0 := by rw [← h4_if' t, h0]
              omega
            · by_cases c2 : pFwd4 t < N + M
              · have hk2 := hinc_key (pFwd4 t - N) (by omega)
                rw [Nat.add_sub_of_le (by omega : N ≤ pFwd4 t)] at hk2
                exact ⟨hk2.2, by omega, c2, by omega⟩
              · have hk3 := hdum_key (pFwd4 t) (by omega)
                have hNpos : 0 < N := Nat.two_pow_pos k
                omega
          have hseg := segUnion_interval (s4Sorted v) recSet4 0 (pInv4 0) (Nat.zero_le _)
            (fun t h1 h2 => (hnoF t h1 h2).1)
          rw [hseg]
          simp only [↓reduceIte]
          ext y
          rw [hneighNat_eq 0 hx y, Finset.mem_union, Finset.mem_biUnion]
          constructor
          · rintro (hy0 | ⟨t, ht, hyt⟩)
            · by_cases hp0 : pInv4 0 = 0
              · rw [← hp0, hrec_x] at hy0; exact absurd hy0 (Finset.notMem_empty _)
              · have h0 := hnoF 0 le_rfl (by omega)
                dsimp only [recSet4, initSet] at hy0
                simp only [show ¬ (pFwd4 0 < N) by omega, h0.2.2.1, ↓reduceIte] at hy0
                exact ⟨pFwd4 0 - N, by omega, h0.2.2.2, hy0⟩
            · simp only [Finset.mem_erase, Finset.mem_Icc] at ht
              by_cases hteq : t = pInv4 0
              · subst hteq; rw [hrec_x] at hyt; exact absurd hyt (Finset.notMem_empty _)
              · have ht' := hnoF t (by omega) (by omega)
                dsimp only [recSet4, initSet] at hyt
                simp only [show ¬ (pFwd4 t < N) by omega, ht'.2.2.1, ↓reduceIte] at hyt
                exact ⟨pFwd4 t - N, by omega, ht'.2.2.2, hyt⟩
          · rintro ⟨qIdx, hqM, hrx, hyc⟩
            let t := pInv4 (N + qIdx)
            have htlt : t < pInv4 0 := by
              by_contra hge
              have hle := hsorted4 (pInv4 0) t (by omega) (h4_ilt' (N + qIdx) (by omega))
              change recKey (k + 2) (s4Sorted v (pInv4 0)) ≤ recKey (k + 2) (s4Sorted v t) at hle
              rw [hkey_x] at hle
              have hk2 : recKey (k + 2) (s4Sorted v t) = 2 * 0 := by
                change recKey (k + 2) (runNet (recKey (k + 2)) netE (st4Init v) t) = _
                dsimp only [t]; rw [h4_inv, (hinc_key qIdx hqM).1, hrx]
              omega
            have hyt : y ∈ recSet4 t := by
              dsimp only [recSet4, initSet, t]; rw [h4_fi']
              simp only [show ¬ (N + qIdx < N) by omega, show N + qIdx < N + M by omega, ↓reduceIte,
                Nat.add_sub_cancel_left]
              exact hyc
            by_cases ht0 : t = 0
            · left; rwa [← ht0]
            · right; exact ⟨t, Finset.mem_erase.mpr ⟨ht0, Finset.mem_Icc.mpr ⟨Nat.zero_le _, by omega⟩⟩, hyt⟩
        · have hxpos : 0 < x := by omega
          have hkey_prev : recKey (k + 2) (s4Sorted v (pInv4 (x - 1))) = 2 * (x - 1) + 1 := by
            change recKey (k + 2) (runNet (recKey (k + 2)) netE (st4Init v) (pInv4 (x - 1))) = _
            rw [h4_inv (x - 1)]; exact (hfoot_key (x - 1) (by omega)).1
          have hfoot_prev : (s4Sorted v (pInv4 (x - 1))).1 0 = true := by
            change (runNet (recKey (k + 2)) netE (st4Init v) (pInv4 (x - 1))).1 0 = true
            rw [h4_inv (x - 1)]; exact (hfoot_key (x - 1) (by omega)).2
          have hlt_prev : pInv4 (x - 1) < pInv4 x := by
            by_contra hge
            have hle := hsorted4 (pInv4 x) (pInv4 (x - 1)) (by omega) (h4_ilt' (x - 1) (by omega))
            change recKey (k + 2) (s4Sorted v (pInv4 x)) ≤ recKey (k + 2) (s4Sorted v (pInv4 (x - 1))) at hle
            omega
          let a := pInv4 (x - 1) + 1
          have hnoF : ∀ t, a ≤ t → t < pInv4 x → (s4Sorted v t).1 0 = false ∧
              N ≤ pFwd4 t ∧ pFwd4 t < N + M ∧ toNat (rowInvV v ((pFwd4 t - N) / S) ((pFwd4 t - N) % S)) = x := by
            intro t hta htx
            have hle1 := hsorted4 (pInv4 (x - 1)) t (by dsimp [a] at hta; omega) (by omega)
            have hle2 := hsorted4 t (pInv4 x) (by omega) h4_ilt_x
            change recKey (k + 2) (s4Sorted v (pInv4 (x - 1))) ≤ recKey (k + 2) (s4Sorted v t) at hle1
            change recKey (k + 2) (s4Sorted v t) ≤ recKey (k + 2) (s4Sorted v (pInv4 x)) at hle2
            rw [hkey_prev] at hle1; rw [hkey_x] at hle2
            have hrun : s4Sorted v t = st4Init v (pFwd4 t) := h4_run t
            rw [hrun] at hle1 hle2 ⊢
            by_cases c1 : pFwd4 t < N
            · have hk1 := (hfoot_key (pFwd4 t) c1).1
              have hor : pFwd4 t = x - 1 ∨ pFwd4 t = x := by omega
              rcases hor with heq | heq
              · have hti : t = pInv4 (x - 1) := by rw [← h4_if' t, heq]
                dsimp [a] at hta; omega
              · have hti : t = pInv4 x := by rw [← h4_if' t, heq]
                omega
            · by_cases c2 : pFwd4 t < N + M
              · have hk2 := hinc_key (pFwd4 t - N) (by omega)
                rw [Nat.add_sub_of_le (by omega : N ≤ pFwd4 t)] at hk2
                exact ⟨hk2.2, by omega, c2, by omega⟩
              · have hk3 := hdum_key (pFwd4 t) (by omega)
                omega
          have hseg := segUnion_interval (s4Sorted v) recSet4 a (pInv4 x) (by dsimp [a]; omega)
            (fun t h1 h2 => (hnoF t h1 h2).1)
          rw [hseg]
          have ha_ne : a ≠ 0 := Nat.succ_ne_zero _
          have ha_sub : a - 1 = pInv4 (x - 1) := Nat.add_sub_cancel _ 1
          simp only [ha_ne, ha_sub, hfoot_prev, ↓reduceIte]
          ext y
          rw [hneighNat_eq x hx y, Finset.mem_union, Finset.mem_biUnion]
          constructor
          · rintro (hya | ⟨t, ht, hyt⟩)
            · by_cases hax : a = pInv4 x
              · rw [hax, hrec_x] at hya; exact absurd hya (Finset.notMem_empty _)
              · have ha' := hnoF a le_rfl (by dsimp [a] at hax ⊢; omega)
                dsimp only [recSet4, initSet] at hya
                simp only [show ¬ (pFwd4 a < N) by omega, ha'.2.2.1, ↓reduceIte] at hya
                exact ⟨pFwd4 a - N, by omega, ha'.2.2.2, hya⟩
            · simp only [Finset.mem_erase, Finset.mem_Icc] at ht
              by_cases hteq : t = pInv4 x
              · subst hteq; rw [hrec_x] at hyt; exact absurd hyt (Finset.notMem_empty _)
              · have ht' := hnoF t ht.2.1 (by omega)
                dsimp only [recSet4, initSet] at hyt
                simp only [show ¬ (pFwd4 t < N) by omega, ht'.2.2.1, ↓reduceIte] at hyt
                exact ⟨pFwd4 t - N, by omega, ht'.2.2.2, hyt⟩
          · rintro ⟨qIdx, hqM, hrx, hyc⟩
            let t := pInv4 (N + qIdx)
            have ht_key : recKey (k + 2) (s4Sorted v t) = 2 * x := by
              change recKey (k + 2) (runNet (recKey (k + 2)) netE (st4Init v) t) = _
              dsimp only [t]; rw [h4_inv, (hinc_key qIdx hqM).1, hrx]
            have hta : a ≤ t := by
              by_contra hlt
              have hle := hsorted4 t (pInv4 (x - 1)) (by dsimp [a] at hlt; omega) (h4_ilt' (x - 1) (by omega))
              change recKey (k + 2) (s4Sorted v t) ≤ recKey (k + 2) (s4Sorted v (pInv4 (x - 1))) at hle
              omega
            have htx : t < pInv4 x := by
              by_contra hge
              have hle := hsorted4 (pInv4 x) t (by omega) (h4_ilt' (N + qIdx) (by omega))
              change recKey (k + 2) (s4Sorted v (pInv4 x)) ≤ recKey (k + 2) (s4Sorted v t) at hle
              omega
            have hyt : y ∈ recSet4 t := by
              dsimp only [recSet4, initSet, t]; rw [h4_fi']
              simp only [show ¬ (N + qIdx < N) by omega, show N + qIdx < N + M by omega, ↓reduceIte,
                Nat.add_sub_cancel_left]
              exact hyc
            by_cases hteqa : t = a
            · left; rwa [← hteqa]
            · right; exact ⟨t, Finset.mem_erase.mpr ⟨hteqa, Finset.mem_Icc.mpr ⟨hta, by omega⟩⟩, hyt⟩
      rw [← hseg_eq]
      exact (hscan4 (pInv4 x)).2
    have hmark_eq : ∀ x : X, markOutV v x.val = mark x := by
      have hperm5 := bitonicPerm (recKey W5) N netK hnetK (st5Init v)
      rcases hperm5 with ⟨h5_fi, h5_if, h5_flt, h5_ilt, h5_run, h5_inv, h5_rep⟩
      let pFwd5 := replaySwaps (netSwaps (recKey W5) netK (st5Init v)) id
      let pInv5 := replaySwaps (netSwaps (recKey W5) netK (st5Init v)).reverse id
      have h5_run' : ∀ idx, s5Sorted v idx = st5Init v (pFwd5 idx) := h5_run
      have hsorted5 := bitonicSort_sorted (recKey W5) k (st5Init v)
      have hbitK : ∀ (u : Nat), u ≤ N → (u.testBit k = true ↔ u = N) := by
        intro u hu
        constructor
        · intro ht
          by_contra hne
          have hlt : u < N := lt_of_le_of_ne hu hne
          rw [Nat.testBit_lt_two_pow hlt] at ht; cases ht
        · rintro rfl; exact Nat.testBit_two_pow_self
      have helig_iff : ∀ x : X, eligV v x.val = true ↔
          keepRow x = true ∧ (neigh x).Nonempty ∧ (neigh x).card ≤ degreeCap := by
        intro x
        have htop := h4_topD x.val x.isLt
        have hne_iff : (neigh x).Nonempty ↔ bitsVal (summaryV v x.val 0) (k + 1) < N := by
          have h1 := IsTopD_nonempty_iff hD1 (hneighNat_lt x.val) htop
          dsimp only [neighNat] at h1; simp only [x.isLt, ↓reduceDIte] at h1
          rw [← h1, Finset.image_nonempty]
        have hcd_iff : (neigh x).card ≤ degreeCap ↔ bitsVal (summaryV v x.val degreeCap) (k + 1) = N := by
          have h1 := IsTopD_card_le_iff (hneighNat_lt x.val) htop
          dsimp only [neighNat] at h1; simp only [x.isLt, ↓reduceDIte] at h1
          rw [Finset.card_image_of_injective _ Fin.val_injective] at h1
          exact h1
        have h0_le : bitsVal (summaryV v x.val 0) (k + 1) ≤ N := htop.1 0 hD1
        have hd_le' : bitsVal (summaryV v x.val degreeCap) (k + 1) ≤ N := htop.1 degreeCap (Nat.lt_succ_self _)
        have h0_bit : summaryV v x.val 0 k = true ↔ bitsVal (summaryV v x.val 0) (k + 1) = N := by
          rw [← bitsVal_testBit (summaryV v x.val 0) (k + 1) k (Nat.lt_succ_self k)]
          exact hbitK _ h0_le
        have hd_bit : summaryV v x.val degreeCap k = true ↔ bitsVal (summaryV v x.val degreeCap) (k + 1) = N := by
          rw [← bitsVal_testBit (summaryV v x.val degreeCap) (k + 1) k (Nat.lt_succ_self k)]
          exact hbitK _ hd_le'
        dsimp only [eligV]
        rw [hv_kr x, Bool.and_eq_true, Bool.and_eq_true, Bool.not_eq_true', hne_iff, hcd_iff]
        have hnot0 : summaryV v x.val 0 k = false ↔ bitsVal (summaryV v x.val 0) (k + 1) < N := by
          cases hs0 : summaryV v x.val 0 k
          · simp only [true_iff]
            have hne : bitsVal (summaryV v x.val 0) (k + 1) ≠ N := fun h => by
              have := h0_bit.mpr h; rw [hs0] at this; cases this
            omega
          · simp only [Bool.true_eq_false, false_iff]
            have := h0_bit.mp hs0; omega
        rw [hnot0, hd_bit, and_assoc]
      let sumCode : Nat → Nat := fun x => bitsVal (summaryPacked v x) LW
      have hsumCode_lt : ∀ x, sumCode x < 2 ^ LW := fun x => bitsVal_lt _ _
      have hkey5_val : ∀ x < N, recKey W5 (st5Init v x) =
          x + 2 ^ k * sumCode x + (if !(eligV v x) then 2 ^ (k + LW) else 0) := by
        intro x hx
        dsimp only [recKey, W5, st5Init]
        change bitsVal (keyBits5 v x) (k + LW) + (if keyBits5 v x (k + LW) then 2 ^ (k + LW) else 0) = _
        have htop : keyBits5 v x (k + LW) = !(eligV v x) := by
          dsimp only [keyBits5]
          simp [show ¬ (k + LW < k) by omega]
        rw [htop, bitsVal_add (keyBits5 v x) k LW]
        have hlo : bitsVal (keyBits5 v x) k = x := by
          trans bitsVal (fun i => x.testBit i) k
          · apply bitsVal_congr; intro t ht; simp [keyBits5, ht]
          · exact bitsVal_of_testBit x k hx
        have hmid : bitsVal (fun j => keyBits5 v x (k + j)) LW = sumCode x := by
          apply bitsVal_congr; intro j hj
          dsimp only [keyBits5]
          simp [show ¬ (k + j < k) by omega, show k + j < k + LW by omega]
        rw [hlo, hmid]
      have hs5_sumCode : ∀ idx < N,
          bitsVal (fun t => (s5Sorted v idx).1 (k + t)) LW = sumCode (pFwd5 idx) := by
        intro idx _
        rw [h5_run' idx]
        apply bitsVal_congr; intro t ht
        dsimp only [st5Init, keyBits5]
        simp [show ¬ (k + t < k) by omega, show k + t < k + LW by omega]
      have hs5_elig : ∀ idx < N, (s5Sorted v idx).1 (k + LW) = !(eligV v (pFwd5 idx)) := by
        intro idx _
        rw [h5_run' idx]
        dsimp only [st5Init, keyBits5]
        simp [show ¬ (k + LW < k) by omega]
      have hsumCode_eq_iff : ∀ (a b : X), (neigh a).card ≤ degreeCap →
          (sumCode a.val = sumCode b.val ↔ neigh a = neigh b) := by
        intro a b hcard
        have hpa : ∀ t < LW, summaryPacked v a.val t = packList k (summaryV v a.val) t := by
          intro t ht
          dsimp only [summaryV, packList, unpackList]
          congr 1; exact (Nat.div_add_mod' t (k + 1)).symm
        have hpb : ∀ t < LW, summaryPacked v b.val t = packList k (summaryV v b.val) t := by
          intro t ht
          dsimp only [summaryV, packList, unpackList]
          congr 1; exact (Nat.div_add_mod' t (k + 1)).symm
        have hcode : sumCode a.val = sumCode b.val ↔
            ∀ j < D, bitsVal (summaryV v a.val j) (k + 1) = bitsVal (summaryV v b.val j) (k + 1) := by
          dsimp only [sumCode]
          rw [bitsVal_congr _ _ LW hpa, bitsVal_congr _ _ LW hpb]
          exact pack_bitsVal_eq_iff k D (summaryV v a.val) (summaryV v b.val)
        rw [hcode]
        have hcard' : (neighNat a.val).card ≤ degreeCap := by
          dsimp only [neighNat]; simp only [a.isLt, ↓reduceDIte]
          rwa [Finset.card_image_of_injective _ Fin.val_injective]
        rw [IsTopD_eq_iff (hneighNat_lt a.val) (hneighNat_lt b.val) (h4_topD a.val a.isLt) (h4_topD b.val b.isLt) hcard']
        dsimp only [neighNat]; simp only [a.isLt, b.isLt, ↓reduceDIte]
        exact Finset.image_injective Fin.val_injective |>.eq_iff
      have hkey5_ord : ∀ a b, a < N → b < N →
          recKey W5 (st5Init v a) ≤ recKey W5 (st5Init v b) →
          (eligV v b = true → eligV v a = true ∧ sumCode a ≤ sumCode b ∧
            (sumCode a = sumCode b → a ≤ b)) := by
        intro a b ha hb hle helb
        rw [hkey5_val a ha, hkey5_val b hb, helb] at hle
        simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, Nat.add_zero] at hle
        have hlt_b : b + 2 ^ k * sumCode b < 2 ^ (k + LW) := by
          rw [Nat.pow_add]
          have hs := hsumCode_lt b
          have hm := Nat.mul_le_mul_left (2 ^ k) (show sumCode b + 1 ≤ 2 ^ LW by omega)
          rw [Nat.mul_add, Nat.mul_one] at hm; dsimp [N] at hb; omega
        have hela : eligV v a = true := by
          cases h : eligV v a
          · rw [h] at hle; simp at hle; omega
          · rfl
        rw [hela] at hle
        simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, Nat.add_zero] at hle
        refine ⟨hela, ?_, ?_⟩
        · by_contra hgt
          have h1 : sumCode b + 1 ≤ sumCode a := by omega
          have hm := Nat.mul_le_mul_left (2 ^ k) h1
          rw [Nat.mul_add, Nat.mul_one] at hm; dsimp [N] at hb; omega
        · intro heq; rw [heq] at hle; omega
      intro x
      dsimp only [markOutV]
      have hrep := h5_rep (fun idx (_ : Nat) => isFirst5 v idx) x.val
      rw [congrFun hrep 0]
      let idx := pInv5 x.val
      have hidx : idx < N := h5_ilt x.val x.isLt
      have hpx : pFwd5 idx = x.val := h5_fi x.val
      change isFirst5 v idx = mark x
      apply Bool.eq_iff_iff.mpr
      dsimp only [isFirst5, mark]
      rw [decide_eq_true_eq, Bool.and_eq_true, hs5_elig idx hidx, hpx, Bool.not_not, helig_iff x]
      constructor
      · rintro ⟨⟨hkr, hne, hcd⟩, hfr⟩
        refine ⟨hkr, hne, hcd, ?_⟩
        intro z hzx hkrz hnz
        have helz : eligV v z.val = true := (helig_iff z).mpr ⟨hkrz, by rwa [hnz], by rwa [hnz]⟩
        have helx : eligV v x.val = true := (helig_iff x).mpr ⟨hkr, hne, hcd⟩
        have hsc_eq : sumCode z.val = sumCode x.val := ((hsumCode_eq_iff x z hcd).mpr hnz.symm).symm
        let idxZ := pInv5 z.val
        have hidxZ : idxZ < N := h5_ilt z.val z.isLt
        have hltZ : idxZ < idx := by
          by_contra hge
          have hle := hsorted5 idx idxZ (by omega) hidxZ
          change recKey W5 (runNet (recKey W5) netK (st5Init v) idx) ≤
                 recKey W5 (runNet (recKey W5) netK (st5Init v) idxZ) at hle
          rw [h5_inv x.val, h5_inv z.val, hkey5_val x.val x.isLt, hkey5_val z.val z.isLt,
              helx, helz, hsc_eq] at hle
          simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, Nat.add_zero] at hle
          have : z.val < x.val := hzx
          omega
        have hidx_ne : idx ≠ 0 := by omega
        simp only [hidx_ne, ↓reduceIte, decide_eq_true_eq] at hfr
        rw [hs5_sumCode idx hidx, hs5_sumCode (idx - 1) (by omega), hpx] at hfr
        let u := pFwd5 (idx - 1)
        have hu : u < N := h5_flt (idx - 1) (by omega)
        have hle1 : recKey W5 (st5Init v z.val) ≤ recKey W5 (st5Init v u) := by
          have h := hsorted5 idxZ (idx - 1) (by omega) (by omega)
          change recKey W5 (runNet (recKey W5) netK (st5Init v) idxZ) ≤
                 recKey W5 (runNet (recKey W5) netK (st5Init v) (idx - 1)) at h
          rwa [h5_inv z.val, h5_run (idx - 1)] at h
        have hle2 : recKey W5 (st5Init v u) ≤ recKey W5 (st5Init v x.val) := by
          have h := hsorted5 (idx - 1) idx (by omega) hidx
          change recKey W5 (runNet (recKey W5) netK (st5Init v) (idx - 1)) ≤
                 recKey W5 (runNet (recKey W5) netK (st5Init v) idx) at h
          rwa [h5_run (idx - 1), h5_inv x.val] at h
        have ho2 := hkey5_ord u x.val hu x.isLt hle2 helx
        have ho1 := hkey5_ord z.val u z.isLt hu hle1 ho2.1
        exact hfr (by dsimp only [u] at ho1 ho2; omega)
      · rintro ⟨hkr, hne, hcd, hfirst⟩
        refine ⟨⟨hkr, hne, hcd⟩, ?_⟩
        by_cases h0 : idx = 0
        · simp [h0]
        · simp only [h0, ↓reduceIte, decide_eq_true_eq]
          rw [hs5_sumCode idx hidx, hs5_sumCode (idx - 1) (by omega), hpx]
          intro heq
          let u := pFwd5 (idx - 1)
          have hu : u < N := h5_flt (idx - 1) (by omega)
          have hle := hsorted5 (idx - 1) idx (by omega) hidx
          change recKey W5 (runNet (recKey W5) netK (st5Init v) (idx - 1)) ≤
                 recKey W5 (runNet (recKey W5) netK (st5Init v) idx) at hle
          rw [h5_run (idx - 1), h5_inv x.val] at hle
          have helx : eligV v x.val = true := (helig_iff x).mpr ⟨hkr, hne, hcd⟩
          have ho := hkey5_ord u x.val hu x.isLt hle helx
          have hux_le : u ≤ x.val := ho.2.2 heq.symm
          have hux_ne : u ≠ x.val := by
            intro hux
            have := congrArg pInv5 hux
            dsimp only [u, pInv5, pFwd5] at this
            rw [h5_if (idx - 1)] at this
            change idx - 1 = idx at this
            omega
          have hkr_u : keepRow ⟨u, hu⟩ = true := ((helig_iff ⟨u, hu⟩).mp ho.1).1
          have hnu : neigh ⟨u, hu⟩ = neigh x := ((hsumCode_eq_iff x ⟨u, hu⟩ hcd).mp heq).symm
          exact hfirst ⟨u, hu⟩ (by show u < x.val; omega) hkr_u hnu
    have hwire_j := (Classical.choose_spec (hout_ex j)).2 v
    rw [hv_eq] at hwire_j
    change (C.wires input).getD (Classical.choose (hout_ex j)) false = answer.getD j.val false
    rw [hwire_j]
    have hflags_len : flags.length = N := by dsimp only [flags]; rw [List.length_map, List.length_finRange]
    by_cases hj : j.val < N
    · simp only [hj, ↓reduceIte]
      dsimp only [answer]
      rw [List.getD_append _ _ _ _ (by omega)]
      rw [finRange_map_getD N mark false j.val hj]
      exact hmark_eq ⟨j.val, hj⟩
    · simp only [hj, ↓reduceIte]
      dsimp only [answer]
      rw [List.getD_append_right _ _ _ _ (by omega), hflags_len]
      have hj' : j.val - N < k + 1 := by dsimp [numOut] at *; omega
      have hget : (bits (k + 1) (flags.count true)).getD (j.val - N) false =
          (flags.count true).testBit (j.val - N) := by
        simp [bits, List.getD_eq_getElem?_getD, hj']
      rw [hget]
      have hcnt : bitsVal (popBits (markOutV v) 0 k) (k + 1) = flags.count true := by
        rw [bitsVal_popBits (markOutV v) k 0]
        congr 1
        apply List.ext_getElem
        · dsimp only [flags, N]; rw [List.length_map, List.length_range, List.length_map, List.length_finRange]
        · intro i h1 h2
          simp only [List.getElem_map, List.getElem_range, Nat.zero_add, flags]
          have hiN : i < N := by rw [List.length_map, List.length_range] at h1; exact h1
          have hfe : (List.finRange N)[i]'(by rw [List.length_finRange]; exact hiN) = ⟨i, hiN⟩ :=
            List.getElem_finRange _
          rw [hfe]
          exact hmark_eq ⟨i, hiN⟩
      rw [← hcnt]
      exact (bitsVal_testBit (popBits (markOutV v) 0 k) (k + 1) (j.val - N) hj').symm

end PipelineMain

end PEqualNP.Outside.L_meta_32053

theorem PEqualNP.Outside.L_meta_32053 : ∀ k r prefixLen degreeCap : ℕ, k % 2 = 1 → k % 3 ≠ 0 → 0 < prefixLen → prefixLen ≤ k → degreeCap ≤ 2^k →
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
  let dim := 2*r*k+2*prefixLen+2*N
  let numOut := N+k+1
  ∃ (C : PEqualNP.CircuitLowerBounds.Circuit) (out : Fin numOut → Fin (dim+C.size)),
    PEqualNP.MetaComplexity.FanInTwo C ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack dim C ∧
    C.output < dim+C.size ∧ C.size ≤ 1048576*(r+1)*(k+1)^4*(degreeCap+1)*2^(2*k-prefixLen) ∧
    ∀ (masks : ℕ → X) (rowTarget colTarget : Fin (2^prefixLen)) (keepRow keepCol : X → Bool),
      let input := (List.range (2*r)).flatMap (fun j => bits k (masks j).val) ++
        bits prefixLen rowTarget.val ++ bits prefixLen colTarget.val ++ (List.finRange N).map keepRow ++ (List.finRange N).map keepCol
      let neigh := fun x : X => Finset.univ.filter (fun y : X => keepCol y = true ∧ ∃ w : X,
        run masks false w.val x.val >>> (k-prefixLen) = rowTarget.val ∧ run masks true w.val y.val >>> (k-prefixLen) = colTarget.val)
      let mark := fun x : X => decide (keepRow x = true ∧ (neigh x).Nonempty ∧ (neigh x).card ≤ degreeCap ∧
        ∀ z : X, z < x → keepRow z = true → neigh z ≠ neigh x)
      let flags := (List.finRange N).map mark
      let answer := flags ++ bits (k+1) (flags.count true)
      ∀ j : Fin numOut, (C.wires input).getD (out j).val false = answer.getD j.val false :=
  PEqualNP.Outside.L_meta_32053.solve_32053
