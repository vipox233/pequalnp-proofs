import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25586_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

abbrev Sig (n : Nat) := (Fin n → Bool) → Bool

def Scheduled (n m : Nat) (S : Set (Sig n)) : Prop :=
  ∃ gs : List Gate, gs.length = m ∧ ReadsBack n ⟨gs, 0⟩ ∧ FanInTwo ⟨gs, 0⟩ ∧
    ∀ f ∈ S, ∃ i < n + m, ∀ x : Fin n → Bool,
      ((⟨gs, 0⟩ : Circuit).wires (List.ofFn x)).getD i false = f x

def Build {n : Nat} (A B : Set (Sig n)) (b : Nat) : Prop :=
  True ∧ ∀ {m S}, Scheduled n m S → A ⊆ S → ∃ c ≤ b, Scheduled n (m + c) (S ∪ B)

lemma wireLength (gs : List Gate) (w : List Bool) :
    ((⟨gs, 0⟩ : Circuit).wires w).length = w.length + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [Circuit.wires]
  | append_singleton gs g ih =>
    simp [Circuit.wires, List.foldl_append] at ih ⊢
    omega

lemma sched_start (n : Nat) :
    Scheduled n 0 (Set.range (fun i : Fin n => fun x : Fin n → Bool => x i)) := by
  refine ⟨[], rfl, by simp [ReadsBack], by simp [FanInTwo], ?_⟩
  rintro _ ⟨i, rfl⟩
  refine ⟨i.val, by omega, fun x => ?_⟩
  simp [Circuit.wires, List.getD_eq_getElem?_getD, i.isLt]

lemma sched_restrict {n m : Nat} {S T : Set (Sig n)} (h : Scheduled n m S) (hT : T ⊆ S) :
    Scheduled n m T := by
  obtain ⟨gs, hlen, hr, hf, hw⟩ := h
  exact ⟨gs, hlen, hr, hf, fun f hf' => hw f (hT hf')⟩

lemma sched_push {n m : Nat} {S : Set (Sig n)} (h : Scheduled n m S)
    (op : GateOp) (deps : List (Sig n)) (f : Sig n)
    (hop : op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp)) (hlen : deps.length ≤ 2)
    (hdeps : ∀ g ∈ deps, g ∈ S)
    (hf : ∀ x, f x = op.eval (deps.map fun g => g x)) :
    Scheduled n (m + 1) (S ∪ {f}) := by
  obtain ⟨gs, hgs, hr, hfan, hw⟩ := h
  have hreal : ∀ l : List (Sig n), (∀ g ∈ l, g ∈ S) →
      ∃ is : List Nat, is.length = l.length ∧ (∀ i ∈ is, i < n + m) ∧
        ∀ x : Fin n → Bool,
          is.map (fun i => ((⟨gs, 0⟩ : Circuit).wires (List.ofFn x)).getD i false) =
            l.map fun g => g x := by
    intro l hl
    induction l with
    | nil => exact ⟨[], rfl, by simp, by simp⟩
    | cons g l ih =>
      obtain ⟨i, hi, hgi⟩ := hw g (hl g List.mem_cons_self)
      obtain ⟨is, his, hbd, hmap⟩ := ih (fun g' hg' => hl g' (List.mem_cons_of_mem g hg'))
      refine ⟨i :: is, by simp [his], ?_, fun x => ?_⟩
      · intro j hj
        rcases List.mem_cons.mp hj with rfl | hj
        · exact hi
        · exact hbd j hj
      · simp only [List.map_cons, hgi, hmap]
  obtain ⟨is, his, hbd, hmap⟩ := hreal deps hdeps
  let g : Gate := ⟨op, is⟩
  have hsnoc (x : Fin n → Bool) :
      ((⟨gs ++ [g], 0⟩ : Circuit).wires (List.ofFn x)) =
        ((⟨gs, 0⟩ : Circuit).wires (List.ofFn x)) ++ [f x] := by
    simp only [Circuit.wires, List.foldl_append, List.foldl_cons, List.foldl_nil, g]
    congr 1
    simp only [hf x, ← hmap x]
    rfl
  have hwlen (x : Fin n → Bool) :
      ((⟨gs, 0⟩ : Circuit).wires (List.ofFn x)).length = n + m := by
    rw [wireLength, List.length_ofFn, hgs]
  refine ⟨gs ++ [g], by simp [hgs], ?_, ?_, ?_⟩
  · intro j hj w hw'
    change j < (gs ++ [g]).length at hj
    change w ∈ ((gs ++ [g]).getD j _).inputs at hw'
    by_cases hlt : j < gs.length
    · rw [List.getD_append _ _ _ _ hlt] at hw'
      exact hr j hlt w hw'
    · have heq : j = gs.length := by simp at hj; omega
      subst heq
      rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (le_refl _), Nat.sub_self] at hw'
      simp only [List.getElem?_cons_zero, Option.getD_some] at hw'
      have := hbd w hw'
      omega
  · intro g' hg'
    change g' ∈ gs ++ [g] at hg'
    rcases List.mem_append.mp hg' with hg' | hg'
    · exact hfan g' hg'
    · rw [List.mem_singleton.mp hg']
      exact ⟨hop, by simp [g, his, hlen]⟩
  · intro h' hh'
    rcases hh' with hh' | hh'
    · obtain ⟨i, hi, hval⟩ := hw h' hh'
      refine ⟨i, by omega, fun x => ?_⟩
      rw [hsnoc x, List.getD_append _ _ _ _ (by rw [hwlen x]; exact hi), hval x]
    · rw [Set.mem_singleton_iff.mp hh']
      refine ⟨n + m, by omega, fun x => ?_⟩
      rw [hsnoc x, ← hwlen x]
      simp [List.getD_eq_getElem?_getD]

lemma sched_finish {n m : Nat} {S : Set (Sig n)} {out : Sig n}
    (h : Scheduled n m S) (hout : out ∈ S) :
    ∃ C : Circuit, FanInTwo C ∧ ReadsBack n C ∧ C.size = m ∧
      ∀ x : Fin n → Bool, C.eval (List.ofFn x) = out x := by
  obtain ⟨gs, hgs, hr, hf, hw⟩ := h
  obtain ⟨i, _, hi⟩ := hw out hout
  exact ⟨⟨gs, i⟩, hf, hr, hgs, hi⟩

lemma build_idle {n : Nat} {A B : Set (Sig n)} (h : B ⊆ A) : Build A B 0 :=
  ⟨trivial, fun HS hA => ⟨0, le_refl _, by simpa [Set.union_eq_left.mpr (h.trans hA)] using HS⟩⟩

lemma build_relax {n : Nat} {A B C D : Set (Sig n)} {b d : Nat}
    (H : Build A B b) (hA : A ⊆ C) (hB : D ⊆ B) (hbd : b ≤ d) : Build C D d :=
  ⟨trivial, fun HS hC => by
    obtain ⟨c, hc, HS'⟩ := H.2 HS (hA.trans hC)
    exact ⟨c, hc.trans hbd, sched_restrict HS' (Set.union_subset_union le_rfl hB)⟩⟩

lemma build_seq {n : Nat} {A B C : Set (Sig n)} {b c : Nat}
    (H : Build A B b) (J : Build (A ∪ B) C c) : Build A (B ∪ C) (b + c) :=
  ⟨trivial, fun HS hA => by
    obtain ⟨d, hd, K⟩ := H.2 HS hA
    obtain ⟨e, he, K'⟩ := J.2 K (Set.union_subset_union hA le_rfl)
    exact ⟨d + e, Nat.add_le_add hd he, by simpa [Nat.add_assoc, Set.union_assoc] using K'⟩⟩

lemma build_one {n : Nat} {A : Set (Sig n)} (op : GateOp) (deps : List (Sig n))
    (hop : op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp)) (hlen : deps.length ≤ 2)
    (hd : ∀ g ∈ deps, g ∈ A) (f : Sig n)
    (hv : ∀ x, f x = op.eval (deps.map fun g => g x)) : Build A {f} 1 :=
  ⟨trivial, fun HS hA => ⟨1, le_refl _, sched_push HS op deps f hop hlen (fun g hg => hA (hd g hg)) hv⟩⟩

lemma build_const {n : Nat} {A : Set (Sig n)} (b : Bool) : Build A {fun _ => b} 1 := by
  cases b
  · exact build_one .or [] (by simp) (by simp) (by simp) _ (fun _ => rfl)
  · exact build_one .and [] (by simp) (by simp) (by simp) _ (fun _ => rfl)

lemma build_and {n : Nat} {A : Set (Sig n)} {f g : Sig n} (hf : f ∈ A) (hg : g ∈ A) :
    Build A {fun x => f x && g x} 1 :=
  build_one .and [f, g] (by simp) (by simp) (by simpa using And.intro hf hg) _ (by simp [GateOp.eval])

lemma build_or {n : Nat} {A : Set (Sig n)} {f g : Sig n} (hf : f ∈ A) (hg : g ∈ A) :
    Build A {fun x => f x || g x} 1 :=
  build_one .or [f, g] (by simp) (by simp) (by simpa using And.intro hf hg) _ (by simp [GateOp.eval])

lemma build_not {n : Nat} {A : Set (Sig n)} {f : Sig n} (hf : f ∈ A) :
    Build A {fun x => !f x} 1 :=
  build_one .not [f] (by simp) (by simp) (by simpa using hf) _ (by simp [GateOp.eval])

lemma build_xor {n : Nat} {A : Set (Sig n)} {f g : Sig n} (hf : f ∈ A) (hg : g ∈ A) :
    Build A {fun x => xor (f x) (g x)} 4 := by
  let a : Sig n := fun x => f x && g x
  let o : Sig n := fun x => f x || g x
  let na : Sig n := fun x => !a x
  have he : (fun x => xor (f x) (g x)) = (fun x => o x && na x) := by
    funext x
    change xor (f x) (g x) = ((f x || g x) && !(f x && g x))
    cases f x <;> cases g x <;> rfl
  rw [he]
  have h1 : Build A {a} 1 := build_and hf hg
  have h2 : Build (A ∪ {a}) {o} 1 := build_or (Or.inl hf) (Or.inl hg)
  have h3 : Build (A ∪ ({a} ∪ {o})) {na} 1 := build_not (Or.inr (Or.inl rfl))
  have h4 : Build (A ∪ (({a} ∪ {o}) ∪ {na})) {fun x => o x && na x} 1 :=
    build_and (Or.inr (Or.inl (Or.inr rfl))) (Or.inr (Or.inr rfl))
  exact build_relax (build_seq (build_seq (build_seq h1 h2) h3) h4) le_rfl (by simp) le_rfl

lemma build_flip {n : Nat} {A : Set (Sig n)} {f : Sig n} (hf : f ∈ A) (b : Bool) :
    Build A {fun x => xor (f x) b} 1 := by
  cases b
  · have he : (fun x => xor (f x) false) = f := by funext x; cases f x <;> rfl
    rw [he]
    exact build_relax (build_idle (Set.singleton_subset_iff.mpr hf)) le_rfl le_rfl (by omega)
  · have he : (fun x => xor (f x) true) = (fun x => !f x) := by funext x; cases f x <;> rfl
    rw [he]
    exact build_not hf

lemma build_mix {n : Nat} {A : Set (Sig n)} {f g h : Sig n}
    (hf : f ∈ A) (hg : g ∈ A) (hh : h ∈ A) :
    Build A {fun x => xor (xor (f x) (g x)) (h x)} 8 :=
  build_relax (build_seq (build_xor hf hg)
    (build_xor (A := A ∪ {fun x => xor (f x) (g x)}) (Or.inr rfl) (Or.inl hh)))
    le_rfl (by simp) le_rfl

lemma build_chi {n : Nat} {A : Set (Sig n)} {f g h : Sig n}
    (hf : f ∈ A) (hg : g ∈ A) (hh : h ∈ A) :
    Build A {fun x => xor (f x) (!(g x) && h x)} 6 := by
  let ng : Sig n := fun x => !g x
  let p : Sig n := fun x => ng x && h x
  have h1 : Build A {ng} 1 := build_not hg
  have h2 : Build (A ∪ {ng}) {p} 1 := build_and (Or.inr rfl) (Or.inl hh)
  have h3 : Build (A ∪ ({ng} ∪ {p})) {fun x => xor (f x) (p x)} 4 :=
    build_xor (Or.inl hf) (Or.inr (Or.inr rfl))
  exact build_relax (build_seq (build_seq h1 h2) h3) le_rfl Set.subset_union_right le_rfl

lemma build_befZ {n : Nat} {A : Set (Sig n)} {sm s0 s1 s2 s3 : Sig n}
    (hm : sm ∈ A) (h0 : s0 ∈ A) (h1 : s1 ∈ A) (h2 : s2 ∈ A) (h3 : s3 ∈ A) :
    Build A {(fun x =>
      let m0 := xor (xor (s0 x) (sm x)) (s1 x)
      let m1 := xor (xor (s1 x) (s0 x)) (s2 x)
      let m2 := xor (xor (s2 x) (s1 x)) (s3 x)
      xor m0 (!m1 && m2))} 30 := by
  let m0 : Sig n := fun x => xor (xor (s0 x) (sm x)) (s1 x)
  let m1 : Sig n := fun x => xor (xor (s1 x) (s0 x)) (s2 x)
  let m2 : Sig n := fun x => xor (xor (s2 x) (s1 x)) (s3 x)
  have H0 : Build A {m0} 8 := build_mix h0 hm h1
  have H1 : Build (A ∪ {m0}) {m1} 8 := build_mix (Or.inl h1) (Or.inl h0) (Or.inl h2)
  have H2 : Build (A ∪ ({m0} ∪ {m1})) {m2} 8 :=
    build_mix (Or.inl h2) (Or.inl h1) (Or.inl h3)
  have H3 : Build (A ∪ (({m0} ∪ {m1}) ∪ {m2})) {fun x => xor (m0 x) (!(m1 x) && m2 x)} 6 :=
    build_chi (Or.inr (Or.inl (Or.inl rfl))) (Or.inr (Or.inl (Or.inr rfl))) (Or.inr (Or.inr rfl))
  exact build_relax (build_seq (build_seq (build_seq H0 H1) H2) H3) le_rfl Set.subset_union_right (by omega)

lemma build_list {α : Type} {n : Nat} {A : Set (Sig n)} (xs : List α)
    (F : α → Sig n) (c : Nat) (H : ∀ a ∈ xs, Build A {F a} c) :
    Build A {f | ∃ a ∈ xs, f = F a} (xs.length * c) := by
  induction xs with
  | nil => exact build_relax (build_idle (B := ∅) (by simp)) le_rfl (by simp) (by simp)
  | cons a xs ih =>
    have h1 := H a List.mem_cons_self
    have h2 := build_relax (C := A ∪ {F a}) (ih (fun b hb => H b (List.mem_cons_of_mem a hb)))
      Set.subset_union_left le_rfl le_rfl
    refine build_relax (build_seq h1 h2) le_rfl ?_ ?_
    · rintro f ⟨b, hb, rfl⟩
      rcases List.mem_cons.mp hb with rfl | hb
      · exact Or.inl rfl
      · exact Or.inr ⟨b, hb, rfl⟩
    · simp only [List.length_cons]
      rw [Nat.succ_mul, Nat.add_comm]

lemma build_fin {k n : Nat} {A : Set (Sig n)} (F : Fin k → Sig n) (c : Nat)
    (H : ∀ i, Build A {F i} c) : Build A (Set.range F) (k * c) := by
  have h := build_list (List.finRange k) F c (fun i _ => H i)
  rw [List.length_finRange] at h
  refine build_relax h le_rfl ?_ le_rfl
  rintro _ ⟨i, rfl⟩
  exact ⟨i, List.mem_finRange i, rfl⟩

lemma build_any {n : Nat} {A : Set (Sig n)} (xs : List (Sig n))
    (hs : ∀ f ∈ xs, f ∈ A) (hfalse : (fun _ => false) ∈ A) :
    Build A {fun x => xs.any (fun f => f x)} xs.length := by
  induction xs with
  | nil => exact build_idle (Set.singleton_subset_iff.mpr hfalse)
  | cons f xs ih =>
    have H := ih (fun g hg => hs g (List.mem_cons_of_mem f hg))
    have K := build_or (A := A ∪ {fun x => xs.any (fun g => g x)})
      (Or.inl (hs f List.mem_cons_self)) (Or.inr rfl)
    exact build_relax (build_seq H K) le_rfl (Set.singleton_subset_iff.mpr (Or.inr rfl)) (by simp)

lemma build_chain {n : Nat} (P : Nat → Set (Sig n)) (cost : Nat → Nat)
    (step : ∀ i, Build (P i) (P (i + 1)) (cost i)) :
    ∀ len, Build (P 0) (P len) (∑ i ∈ Finset.range len, cost i) := by
  intro len
  induction len with
  | zero => simpa using build_idle (le_refl (P 0))
  | succ len ih =>
    rw [Finset.sum_range_succ]
    have hstep := build_relax (C := P 0 ∪ P len) (step len) Set.subset_union_right le_rfl le_rfl
    exact build_relax (build_seq ih hstep) le_rfl Set.subset_union_right le_rfl

def inputs (n : Nat) : Set (Sig n) := Set.range (fun i : Fin n => fun v => v i)
def base (n : Nat) : Set (Sig n) := inputs n ∪ {fun _ => false, fun _ => true}

lemma const_mem_base {n : Nat} (b : Bool) : (fun _ : Fin n → Bool => b) ∈ base n := by
  cases b <;> exact Or.inr (by simp)

lemma build_base_exact (n : Nat) : Build (inputs n) {fun _ => false, fun _ => true} 2 := by
  simpa only [Set.singleton_union] using
    build_seq (build_const (A := inputs n) false)
      (build_const (A := inputs n ∪ {fun _ => false}) true)

def rot (k s word : Nat) : Nat :=
  ((word <<< (s % k)) ||| (word >>> (k - s % k))) % 2 ^ k

def step (k word : Nat) : Nat :=
  (List.range k).foldl (fun acc i =>
    acc ||| ((xor (word.testBit i)
      (!(word.testBit ((i + 1) % k)) && word.testBit ((i + 2) % k))).toNat <<< i)) 0

def constW (k j : Nat) : Nat := 3 ^ (k + j) % 2 ^ k

def rowWord (k w u t : Nat) : Nat :=
  (List.range t).foldl (fun s idx =>
    step k (s ^^^ rot k 1 s ^^^ rot k (k - 1) s) ^^^
      rot k (2 * idx) w ^^^ constW k (idx + 1)) (rot k 1 w ^^^ u)

def colWord (k r w v t : Nat) : Nat :=
  (List.range t).foldl (fun s idx =>
    step k (s ^^^ rot k 2 s ^^^ rot k (k - 2) s) ^^^
      rot k (3 * (idx + 1) + 1) w ^^^ constW k (r + (idx + 1))) (rot k 3 w ^^^ v)

def res (k : Nat) (z : Int) : Nat := (z % (k : Int)).toNat

def pz (k w : Nat) (z : Int) : Bool := w.testBit (res k z)

lemma res_lt {k : Nat} (hk : 0 < k) (z : Int) : res k z < k := by
  have h0 := Int.emod_nonneg z (by omega : (k : Int) ≠ 0)
  have h1 := Int.emod_lt_of_pos z (by omega : (0 : Int) < k)
  unfold res
  omega

lemma res_cast {k : Nat} (hk : 0 < k) (z : Int) : (res k z : Int) = z % (k : Int) :=
  Int.toNat_of_nonneg (Int.emod_nonneg z (by omega))

lemma res_nat (k a : Nat) : res k (a : Int) = a % k := by
  unfold res
  rw [← Int.natCast_mod, Int.toNat_natCast]

lemma pz_nat (k w a : Nat) : pz k w (a : Int) = w.testBit (a % k) := by
  unfold pz; rw [res_nat]

lemma pz_lt (k w i : Nat) (hi : i < k) : pz k w (i : Int) = w.testBit i := by
  rw [pz_nat, Nat.mod_eq_of_lt hi]

lemma pz_of_emod {k w : Nat} {a b : Int} (h : a % (k : Int) = b % (k : Int)) :
    pz k w a = pz k w b := by
  unfold pz res; rw [h]

lemma pz_xor (k a b : Nat) (z : Int) : pz k (a ^^^ b) z = xor (pz k a z) (pz k b z) :=
  Nat.testBit_xor _ _ _

lemma big_bit_false {k x j : Nat} (hx : x < 2 ^ k) (hj : k ≤ j) : x.testBit j = false :=
  Nat.testBit_lt_two_pow (lt_of_lt_of_le hx (Nat.pow_le_pow_right (by decide) hj))

lemma rot_lt (k s w : Nat) : rot k s w < 2 ^ k :=
  Nat.mod_lt _ (Nat.two_pow_pos k)

lemma constW_lt (k j : Nat) : constW k j < 2 ^ k :=
  Nat.mod_lt _ (Nat.two_pow_pos k)

lemma testBit_foldl_or (g : Nat → Bool) (n j : Nat) :
    ((List.range n).foldl (fun acc i => acc ||| ((g i).toNat <<< i)) 0).testBit j =
      (decide (j < n) && g j) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, Nat.testBit_or, ih]
    rcases lt_trichotomy j n with h | h | h
    · cases g n <;> simp [h, Nat.shiftLeft_eq, show j < n + 1 by omega, show n ≠ j by omega]
    · subst h; cases g j <;> simp [Nat.shiftLeft_eq]
    · cases g n <;> simp [Nat.shiftLeft_eq, show ¬ j < n by omega, show ¬ j < n + 1 by omega,
        show n ≠ j by omega]

lemma testBit_step (k w i : Nat) :
    (step k w).testBit i =
      (decide (i < k) && xor (w.testBit i) (!(w.testBit ((i + 1) % k)) && w.testBit ((i + 2) % k))) :=
  testBit_foldl_or _ k i

lemma step_lt (k w : Nat) : step k w < 2 ^ k :=
  Nat.lt_pow_two_of_testBit _ (fun i hi => by rw [testBit_step]; simp [show ¬ i < k by omega])

lemma testBit_rot {k s w i : Nat} (hw : w < 2 ^ k) (hi : i < k) :
    (rot k s w).testBit i = w.testBit ((i + k - s % k) % k) := by
  have hk : 0 < k := by omega
  have hs : s % k < k := Nat.mod_lt _ hk
  unfold rot
  rw [Nat.testBit_mod_two_pow, Nat.testBit_or, Nat.testBit_shiftLeft, Nat.testBit_shiftRight]
  simp only [hi, decide_true, Bool.true_and]
  by_cases h : s % k ≤ i
  · rw [big_bit_false hw (by omega : k ≤ k - s % k + i)]
    have he : (i + k - s % k) % k = i - s % k := by
      rw [show i + k - s % k = (i - s % k) + k by omega, Nat.add_mod_right,
        Nat.mod_eq_of_lt (by omega)]
    simp [h, he]
  · have he : (i + k - s % k) % k = k - s % k + i := by
      rw [Nat.mod_eq_of_lt (by omega)]; omega
    simp [show ¬ (i ≥ s % k) by omega, he]

lemma pz_rot {k s w : Nat} (hk : 0 < k) (hw : w < 2 ^ k) (z : Int) :
    pz k (rot k s w) z = pz k w (z - (s : Int)) := by
  have hi : res k z < k := res_lt hk z
  have hrc : (res k z : Int) = z % (k : Int) := res_cast hk z
  have hs : s % k < k := Nat.mod_lt _ hk
  calc pz k (rot k s w) z = (rot k s w).testBit (res k z) := rfl
    _ = w.testBit ((res k z + k - s % k) % k) := testBit_rot hw hi
    _ = pz k w ((res k z + k - s % k : Nat) : Int) := (pz_nat _ _ _).symm
    _ = pz k w (z - (s : Int)) := by
      apply pz_of_emod
      rw [Nat.cast_sub (by omega), Nat.cast_add, hrc, Int.natCast_mod]
      rw [Int.sub_emod, Int.add_emod, Int.emod_emod, Int.emod_self, Int.add_zero,
        Int.emod_emod, Int.emod_emod, ← Int.sub_emod]

lemma pz_step {k : Nat} (hk : 0 < k) (w : Nat) (z : Int) :
    pz k (step k w) z = xor (pz k w z) (!(pz k w (z + 1)) && pz k w (z + 2)) := by
  have hi : res k z < k := res_lt hk z
  have hrc : (res k z : Int) = z % (k : Int) := res_cast hk z
  have he : ∀ a : Nat, pz k w (z + (a : Int)) = w.testBit ((res k z + a) % k) := by
    intro a
    rw [← pz_nat]
    apply pz_of_emod
    rw [Nat.cast_add, hrc, Int.emod_add_emod]
  have e0 : pz k w z = w.testBit (res k z) := rfl
  have e1 : pz k w (z + 1) = w.testBit ((res k z + 1) % k) := he 1
  have e2 : pz k w (z + 2) = w.testBit ((res k z + 2) % k) := he 2
  rw [e0, e1, e2]
  show (step k w).testBit (res k z) = _
  rw [testBit_step]
  simp [hi]

lemma rowWord_zero (k w u : Nat) : rowWord k w u 0 = rot k 1 w ^^^ u := rfl

lemma rowWord_succ (k w u t : Nat) :
    rowWord k w u (t + 1) =
      step k (rowWord k w u t ^^^ rot k 1 (rowWord k w u t) ^^^ rot k (k - 1) (rowWord k w u t)) ^^^
        rot k (2 * t) w ^^^ constW k (t + 1) := by
  unfold rowWord
  rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]

lemma rowWord_lt {k u : Nat} (hu : u < 2 ^ k) (w t : Nat) : rowWord k w u t < 2 ^ k := by
  cases t with
  | zero => exact Nat.xor_lt_two_pow (rot_lt k 1 w) hu
  | succ t =>
    rw [rowWord_succ]
    exact Nat.xor_lt_two_pow (Nat.xor_lt_two_pow (step_lt k _) (rot_lt k _ w)) (constW_lt k _)

lemma colWord_zero (k r w v : Nat) : colWord k r w v 0 = rot k 3 w ^^^ v := rfl

lemma colWord_succ (k r w v t : Nat) :
    colWord k r w v (t + 1) =
      step k (colWord k r w v t ^^^ rot k 2 (colWord k r w v t) ^^^ rot k (k - 2) (colWord k r w v t)) ^^^
        rot k (3 * (t + 1) + 1) w ^^^ constW k (r + (t + 1)) := by
  unfold colWord
  rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]

lemma colWord_lt {k r v : Nat} (hv : v < 2 ^ k) (w t : Nat) : colWord k r w v t < 2 ^ k := by
  cases t with
  | zero => exact Nat.xor_lt_two_pow (rot_lt k 3 w) hv
  | succ t =>
    rw [colWord_succ]
    exact Nat.xor_lt_two_pow (Nat.xor_lt_two_pow (step_lt k _) (rot_lt k _ w)) (constW_lt k _)

def mixZ (f : Int → Bool) (z : Int) : Bool := xor (xor (f z) (f (z - 1))) (f (z + 1))

def befZ (f : Int → Bool) (z : Int) : Bool :=
  xor (mixZ f z) (!(mixZ f (z + 1)) && mixZ f (z + 2))

def stZ (pub : Nat → Int → Bool) (start : Int → Bool) (rounds : Nat) : Int → Bool :=
  (List.range rounds).foldl (fun (prev : Int → Bool) (tick : Nat) (z : Int) =>
    xor (xor (befZ prev z) (start (z + 1 - 2 * (tick : Int)))) (pub (tick + 1) z)) start

def pubBit (k u : Nat) (t : Nat) (z : Int) : Bool :=
  xor (pz k u (z + 1 - 2 * ((t - 1 : Nat) : Int))) (pz k (constW k t) z)

lemma stZ_zero (pub : Nat → Int → Bool) (s : Int → Bool) : stZ pub s 0 = s := rfl

lemma stZ_succ (pub : Nat → Int → Bool) (s : Int → Bool) (t : Nat) (z : Int) :
    stZ pub s (t + 1) z =
      xor (xor (befZ (stZ pub s t) z) (s (z + 1 - 2 * (t : Int)))) (pub (t + 1) z) := by
  unfold stZ
  rw [List.range_succ, List.foldl_append]
  rfl

lemma befZ_eq (f : Int → Bool) (z : Int) :
    befZ f z =
      let m0 := xor (xor (f z) (f (z - 1))) (f (z + 1))
      let m1 := xor (xor (f (z + 1)) (f z)) (f (z + 2))
      let m2 := xor (xor (f (z + 2)) (f (z + 1))) (f (z + 3))
      xor m0 (!m1 && m2) := by
  unfold befZ mixZ
  rw [show z + 1 - 1 = z by omega, show z + 2 - 1 = z + 1 by omega,
    show z + 1 + 1 = z + 2 by omega, show z + 2 + 1 = z + 3 by omega]

lemma befZ_agree {f g : Int → Bool} (z : Int)
    (h : ∀ j : Int, -1 ≤ j → j ≤ 3 → f (z + j) = g (z + j)) : befZ f z = befZ g z := by
  have hm := h (-1) (by omega) (by omega)
  have h0 := h 0 (by omega) (by omega)
  have h1 := h 1 (by omega) (by omega)
  have h2 := h 2 (by omega) (by omega)
  have h3 := h 3 (by omega) (by omega)
  rw [show z + (-1) = z - 1 by omega] at hm
  rw [show z + 0 = z by omega] at h0
  rw [befZ_eq, befZ_eq, hm, h0, h1, h2, h3]

lemma pz_mix_step {k s : Nat} (hk : 2 ≤ k) (hs : s < 2 ^ k) (z : Int) :
    pz k (step k (s ^^^ rot k 1 s ^^^ rot k (k - 1) s)) z = befZ (pz k s) z := by
  have hk0 : 0 < k := by omega
  have hmix : ∀ y : Int, pz k (s ^^^ rot k 1 s ^^^ rot k (k - 1) s) y = mixZ (pz k s) y := by
    intro y
    rw [pz_xor, pz_xor, pz_rot hk0 hs, pz_rot hk0 hs]
    have hshift : pz k s (y - ((k - 1 : Nat) : Int)) = pz k s (y + 1) := by
      apply pz_of_emod
      rw [Nat.cast_sub (by omega : 1 ≤ k), Nat.cast_one]
      rw [show y - ((k : Int) - 1) = (y + 1) - (k : Int) by omega, Int.sub_emod_right]
    rw [hshift]
    rfl
  rw [pz_step hk0, hmix z, hmix (z + 1), hmix (z + 2)]
  rfl

lemma stZ_eq_rowWord {k w u : Nat} (hk : 2 ≤ k) (hw : w < 2 ^ k) (hu : u < 2 ^ k) :
    ∀ t z, stZ (pubBit k u) (pz k (rot k 1 w ^^^ u)) t z = pz k (rowWord k w u t) z := by
  have hk0 : 0 < k := by omega
  intro t
  induction t with
  | zero => intro z; rfl
  | succ t ih =>
    intro z
    rw [stZ_succ, rowWord_succ, pz_xor, pz_xor, pz_xor, pz_mix_step hk (rowWord_lt hu w t)]
    have hih : stZ (pubBit k u) (pz k (rot k 1 w ^^^ u)) t = pz k (rowWord k w u t) := funext ih
    rw [hih, pz_rot hk0 hw, pz_rot hk0 hw]
    simp only [pubBit, Nat.add_sub_cancel]
    have hpos : z + 1 - 2 * (t : Int) - ((1 : Nat) : Int) = z - ((2 * t : Nat) : Int) := by push_cast; omega
    rw [hpos]
    cases befZ (pz k (rowWord k w u t)) z <;> cases pz k w (z - ((2 * t : Nat) : Int)) <;>
      cases pz k u (z + 1 - 2 * (t : Int)) <;> cases pz k (constW k (t + 1)) z <;> rfl

lemma recover_key {k w u : Nat} (hk : 2 ≤ k) (hw : w < 2 ^ k) (hu : u < 2 ^ k) :
    rot k (k - 1) ((rot k 1 w ^^^ u) ^^^ u) = w := by
  have hk0 : 0 < k := by omega
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < k
  · rw [← pz_lt k _ i hi, ← pz_lt k w i hi, pz_rot hk0 (Nat.xor_lt_two_pow (Nat.xor_lt_two_pow (rot_lt k 1 w) hu) hu)]
    rw [Nat.xor_assoc, Nat.xor_self, Nat.xor_zero, pz_rot hk0 hw]
    apply pz_of_emod
    rw [Nat.cast_sub (by omega : 1 ≤ k), Nat.cast_one]
    rw [show (i : Int) - ((k : Int) - 1) - 1 = (i : Int) - (k : Int) by omega, Int.sub_emod_right]
  · rw [big_bit_false (rot_lt k _ _) (by omega), big_bit_false hw (by omega)]

def loZ (s : Nat) : Int := if s ≤ 3 then -(s : Int) else -2 * (s : Int) + 3

lemma loZ_succ (s : Nat) : loZ (s + 1) ≤ loZ s - 1 ∧ loZ (s + 1) ≤ 1 - 2 * (s : Int) := by
  unfold loZ; split_ifs <;> push_cast <;> omega

lemma loZ_nonpos (s : Nat) : loZ s ≤ 0 := by
  unfold loZ; split_ifs <;> omega

lemma loZ_ge3 {s : Nat} (hs : 3 ≤ s) : loZ s = -2 * (s : Int) + 3 := by
  unfold loZ; split_ifs <;> omega

lemma zdep (pub : Nat → Int → Bool) (a b : Int → Bool) :
    ∀ s : Nat, ∀ z : Int,
      (∀ y, z + loZ s ≤ y → y ≤ z + 3 * (s : Int) → a y = b y) →
        stZ pub a s z = stZ pub b s z := by
  intro s
  induction s with
  | zero => intro z h; exact h z (by simp [loZ]) (by simp)
  | succ s ih =>
    intro z h
    have hl := loZ_succ s
    rw [stZ_succ, stZ_succ, h _ (by omega) (by push_cast; omega)]
    rw [befZ_agree z (fun j h1 h2 => ih _ (fun y hy1 hy2 =>
      h y (by omega) (by push_cast at hy2 ⊢; omega)))]

def cntC (cb : Nat → Bool) : Nat → Nat
  | 0 => 0
  | j + 1 => cntC cb j + if cb j then 1 else 0

lemma cntC_le (cb : Nat → Bool) : ∀ j, cntC cb j ≤ j
  | 0 => le_refl 0
  | j + 1 => by simp only [cntC]; have := cntC_le cb j; split_ifs <;> omega

def front (cut : Int) (n : Nat) (cb : Nat → Bool) : Nat → Int
  | 0 => cut
  | t + 1 => front cut n cb t - 3 + if 4 ≤ t ∧ t - 4 < n ∧ cb (t - 4) = true then 1 else 0

lemma front_val (cut : Int) (n : Nat) (cb : Nat → Bool) :
    ∀ t, front cut n cb t = cut - 3 * (t : Int) + (cntC cb (min n (t - 4)) : Int) := by
  intro t
  induction t with
  | zero => simp [front, cntC]
  | succ t ih =>
    simp only [front, ih]
    by_cases h4 : 4 ≤ t
    · by_cases hn : t - 4 < n
      · rw [show min n (t + 1 - 4) = (t - 4) + 1 by omega, show min n (t - 4) = t - 4 by omega]
        simp only [cntC]
        by_cases hc : cb (t - 4) = true
        · simp [h4, hn, hc]; omega
        · simp [h4, hn, hc]; omega
      · rw [show min n (t + 1 - 4) = n by omega, show min n (t - 4) = n by omega]
        simp [hn]; omega
    · rw [show min n (t + 1 - 4) = min n (t - 4) by omega]
      simp [h4]; omega

lemma front_agree (n : Nat) (pub : Nat → Int → Bool) (cut : Int) (cb : Nat → Bool)
    (start other : Int → Bool)
    (htr : ∀ j < n,
      let S := stZ pub start (4 + j)
      let a := cut - 3 * (5 + (j : Int)) + (cntC cb j : Int)
      xor (xor (S a) (S (a + 1))) (S (a + 2)) = cb j)
    (hag : ∀ z < cut, start z = other z) :
    ∀ t, (∀ z < front cut n cb t, stZ pub start t z = stZ pub other t z) ∧
      (∀ z < front cut n cb (t + 1), befZ (stZ pub start t) z = befZ (stZ pub other t) z) := by
  have pre : ∀ t, (∀ z < front cut n cb t, stZ pub start t z = stZ pub other t z) →
      ∀ z < front cut n cb (t + 1), befZ (stZ pub start t) z = befZ (stZ pub other t) z := by
    intro t ht z hz
    simp only [front] at hz
    by_cases hlow : z < front cut n cb t - 3
    · exact befZ_agree z (fun j h1 h2 => ht _ (by omega))
    · have hb : 4 ≤ t ∧ t - 4 < n ∧ cb (t - 4) = true := by
        by_contra hb; simp only [hb, ↓reduceIte] at hz; omega
      simp only [hb] at hz
      have hz' : z = front cut n cb t - 3 := by omega
      obtain ⟨j, rfl⟩ : ∃ j, t = 4 + j := ⟨t - 4, by omega⟩
      have hj : j < n := by omega
      have hg := htr j hj
      rw [show 4 + j - 4 = j by omega] at hb
      rw [hb.2.2] at hg
      have hfv := front_val cut n cb (4 + j)
      rw [show min n (4 + j - 4) = j by omega] at hfv
      have hza : cut - 3 * (5 + (j : Int)) + (cntC cb j : Int) = z := by
        rw [hz', hfv]; push_cast; omega
      dsimp only at hg
      rw [hza] at hg
      have a0 := ht z (by omega)
      have a1 := ht (z + 1) (by omega)
      have a2 := ht (z + 2) (by omega)
      have am := ht (z - 1) (by omega)
      rw [befZ_eq, befZ_eq, ← a0, ← a1, ← a2, ← am]
      have hmix1 : xor (xor (stZ pub start (4 + j) (z + 1)) (stZ pub start (4 + j) z))
          (stZ pub start (4 + j) (z + 2)) = true := by
        rw [Bool.xor_comm (stZ pub start (4 + j) (z + 1))]; exact hg
      simp [hmix1]
  intro t
  induction t with
  | zero =>
    have h0 : ∀ z < front cut n cb 0, stZ pub start 0 z = stZ pub other 0 z := fun z hz => hag z hz
    exact ⟨h0, pre 0 h0⟩
  | succ t ih =>
    have h1 : ∀ z < front cut n cb (t + 1), stZ pub start (t + 1) z = stZ pub other (t + 1) z := by
      intro z hz
      have hfv := front_val cut n cb (t + 1)
      have hc := cntC_le cb (min n (t + 1 - 4))
      rw [stZ_succ, stZ_succ, ih.2 z hz, hag _ (by omega)]
    exact ⟨h1, pre (t + 1) h1⟩

def actualTrace (pub : Nat → Int → Bool) (start : Int → Bool) (cut : Int) : Nat → List Bool
  | 0 => []
  | j + 1 =>
    let tr := actualTrace pub start cut j
    let o := tr.count true
    let a := cut - 3 * (5 + (j : Int)) + (o : Int)
    let S := stZ pub start (4 + j)
    tr ++ [xor (xor (S a) (S (a + 1))) (S (a + 2))]

lemma actualTrace_length (pub : Nat → Int → Bool) (start : Int → Bool) (cut : Int) :
    ∀ n, (actualTrace pub start cut n).length = n
  | 0 => rfl
  | n + 1 => by simp [actualTrace, actualTrace_length pub start cut n]

lemma actualTrace_take (pub : Nat → Int → Bool) (start : Int → Bool) (cut : Int) :
    ∀ n j, j ≤ n → (actualTrace pub start cut n).take j = actualTrace pub start cut j := by
  intro n
  induction n with
  | zero =>
    intro j hj
    obtain rfl : j = 0 := by omega
    simp [actualTrace]
  | succ n ih =>
    intro j hj
    rcases Nat.lt_or_eq_of_le hj with hlt | rfl
    · simp only [actualTrace]
      rw [List.take_append_of_le_length (by rw [actualTrace_length]; omega)]
      exact ih j (by omega)
    · have hlen := actualTrace_length pub start cut (n + 1)
      conv_lhs => arg 1; rw [← hlen]
      exact List.take_length

lemma actualTrace_getD (pub : Nat → Int → Bool) (start : Int → Bool) (cut : Int) :
    ∀ n j, j < n →
      (actualTrace pub start cut n).getD j false =
        let o := ((actualTrace pub start cut n).take j).count true
        let a := cut - 3 * (5 + (j : Int)) + (o : Int)
        let S := stZ pub start (4 + j)
        xor (xor (S a) (S (a + 1))) (S (a + 2)) := by
  intro n
  induction n with
  | zero => intro j hj; omega
  | succ n ih =>
    intro j hj
    rw [actualTrace_take pub start cut (n + 1) j (by omega)]
    rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp hj) with hlt | rfl
    · simp only [actualTrace]
      rw [List.getD_append _ _ _ _ (by rw [actualTrace_length]; exact hlt)]
      have h1 := ih j hlt
      rw [actualTrace_take pub start cut n j (by omega)] at h1
      exact h1
    · simp only [actualTrace, List.getD_eq_getElem?_getD]
      rw [List.getElem?_append_right (by rw [actualTrace_length]), actualTrace_length, Nat.sub_self]
      rfl

lemma count_take_eq_cntC (tr : List Bool) :
    ∀ j, j ≤ tr.length → (tr.take j).count true = cntC (fun h => tr.getD h false) j := by
  intro j
  induction j with
  | zero => intro _; simp [cntC]
  | succ j ih =>
    intro hj
    have hsp : tr.take (j + 1) = tr.take j ++ [tr.getD j false] := by
      have hget : tr[j]'(by omega) = tr.getD j false := by
        simp [List.getD_eq_getElem?_getD, show j < tr.length by omega]
      rw [List.take_succ_eq_append_getElem (by omega), hget]
    rw [hsp, List.count_append, ih (by omega)]
    simp only [cntC]
    have hb : [tr.getD j false].count true = if tr.getD j false = true then 1 else 0 := by
      cases tr.getD j false <;> rfl
    rw [hb]

lemma pack_succ {n : Nat} (x : Fin (n + 1) → Bool) :
    tableIndex x = tableIndex (fun i : Fin n => x i.castSucc) +
      (if x (Fin.last n) = true then 2 ^ n else 0) := by
  unfold tableIndex
  rw [Fin.sum_univ_castSucc]
  rfl

lemma pack_lt : ∀ {n : Nat} (x : Fin n → Bool), tableIndex x < 2 ^ n := by
  intro n
  induction n with
  | zero => intro x; simp [tableIndex]
  | succ n ih =>
    intro x
    rw [pack_succ, pow_succ]
    have := ih (fun i : Fin n => x i.castSucc)
    split <;> omega

lemma bit_pack : ∀ {n : Nat} (x : Fin n → Bool) (i : Fin n),
    (tableIndex x).testBit i.val = x i := by
  intro n
  induction n with
  | zero => intro x i; exact i.elim0
  | succ n ih =>
    intro x i
    have hlt := pack_lt (fun i : Fin n => x i.castSucc)
    rw [pack_succ]
    refine Fin.lastCases ?_ (fun j => ?_) i
    · rw [Fin.val_last]
      cases x (Fin.last n) <;> simp only [Bool.false_eq_true, ↓reduceIte]
      · rw [Nat.add_zero, Nat.testBit_lt_two_pow hlt]
      · rw [Nat.add_comm, Nat.testBit_two_pow_add_eq, Nat.testBit_lt_two_pow hlt]; rfl
    · change (tableIndex (fun i : Fin n => x i.castSucc) +
        (if x (Fin.last n) = true then 2 ^ n else 0)).testBit j.val = x j.castSucc
      cases x (Fin.last n) <;> simp only [Bool.false_eq_true, ↓reduceIte]
      · rw [Nat.add_zero]; exact ih _ j
      · rw [Nat.add_comm, Nat.testBit_two_pow_add_gt j.isLt]; exact ih _ j

def U (k : Nat) (v : Fin (k + k) → Bool) : Nat := tableIndex fun i : Fin k => v (Fin.castAdd k i)
def V (k : Nat) (v : Fin (k + k) → Bool) : Nat := tableIndex fun i : Fin k => v (Fin.natAdd k i)

lemma U_lt (k : Nat) (v) : U k v < 2 ^ k := pack_lt _
lemma V_lt (k : Nat) (v) : V k v < 2 ^ k := pack_lt _

def ix {k : Nat} (hk : 0 < k) (i : Nat) : Fin k := ⟨i % k, Nat.mod_lt _ hk⟩
def bits {k n : Nat} (w : (Fin n → Bool) → Nat) (i : Fin k) : Sig n := fun v => (w v).testBit i.val

lemma bitU_mem (k : Nat) (i : Fin k) : bits (U k) i ∈ base (k + k) :=
  Or.inl ⟨Fin.castAdd k i, funext fun v => (bit_pack (fun j : Fin k => v (Fin.castAdd k j)) i).symm⟩

lemma bitV_mem (k : Nat) (i : Fin k) : bits (V k) i ∈ base (k + k) :=
  Or.inl ⟨Fin.natAdd k i, funext fun v => (bit_pack (fun j : Fin k => v (Fin.natAdd k j)) i).symm⟩

lemma pzU_mem {k : Nat} (hk : 0 < k) (z : Int) :
    (fun v => pz k (U k v) z) ∈ base (k + k) := by
  exact bitU_mem k ⟨res k z, res_lt hk z⟩

lemma rotG {k n : Nat} (hk : 0 < k) {A : Set (Sig n)}
    {w : (Fin n → Bool) → Nat} (hw : ∀ v, w v < 2 ^ k) (hs : ∀ i : Fin k, bits w i ∈ A)
    (d : Nat) (i : Fin k) : bits (fun v => rot k d (w v)) i ∈ A := by
  convert hs (ix hk (i.val + k - d % k)) using 1
  funext v
  exact testBit_rot (hw v) i.isLt

lemma xorBitsG {k n : Nat} {A : Set (Sig n)} {w u : (Fin n → Bool) → Nat} (i : Fin k)
    (hw : bits w i ∈ A) (hu : bits u i ∈ A) :
    Build A {bits (fun v => w v ^^^ u v) i} 4 := by
  have he : bits (fun v => w v ^^^ u v) i = (fun v => xor (bits w i v) (bits u i v)) := by
    funext v; exact Nat.testBit_xor _ _ _
  rw [he]; exact build_xor hw hu

lemma roundG {k n : Nat} (hk : 0 < k) {A : Set (Sig n)} (d : Nat)
    (w s : (Fin n → Bool) → Nat) (hw : ∀ v, w v < 2 ^ k) (hs : ∀ v, s v < 2 ^ k)
    (hW : ∀ i : Fin k, bits w i ∈ A) (hS : ∀ i : Fin k, bits s i ∈ A) (sh cj : Nat) :
    Build A (Set.range (fun i : Fin k =>
      bits (fun v => step k (s v ^^^ rot k d (s v) ^^^ rot k (k - d) (s v)) ^^^
        rot k sh (w v) ^^^ constW k cj) i)) (19 * k) := by
  let w1 := fun v => s v ^^^ rot k d (s v) ^^^ rot k (k - d) (s v)
  let F := fun i : Fin k => bits w1 i
  have H : Build A (Set.range F) (k * 8) := build_fin F 8 fun i => by
    have E : F i = (fun v => xor (xor (bits s i v) (bits (fun v => rot k d (s v)) i v))
        (bits (fun v => rot k (k - d) (s v)) i v)) := by
      funext v; simp only [F, bits, w1, Nat.testBit_xor]
    rw [E]
    exact build_mix (hS i) (rotG hk hs hS d i) (rotG hk hs hS (k - d) i)
  let G := fun i : Fin k =>
    bits (fun v => step k (w1 v) ^^^ rot k sh (w v) ^^^ constW k cj) i
  have J : Build (A ∪ Set.range F) (Set.range G) (k * 11) := build_fin G 11 fun i => by
    let p : Sig n := fun v => xor (F i v) (!(F (ix hk (i.val + 1)) v) && F (ix hk (i.val + 2)) v)
    let q : Sig n := fun v => xor (p v) (bits (fun v => rot k sh (w v)) i v)
    have h1 : Build (A ∪ Set.range F) {p} 6 :=
      build_chi (Or.inr ⟨i, rfl⟩) (Or.inr ⟨ix hk (i.val + 1), rfl⟩) (Or.inr ⟨ix hk (i.val + 2), rfl⟩)
    have h2 : Build ((A ∪ Set.range F) ∪ {p}) {q} 4 :=
      build_xor (Or.inr rfl) (Or.inl (Or.inl (rotG hk hw hW sh i)))
    have h3 : Build ((A ∪ Set.range F) ∪ ({p} ∪ {q})) {fun v => xor (q v) ((constW k cj).testBit i.val)} 1 :=
      build_flip (Or.inr (Or.inr rfl)) ((constW k cj).testBit i.val)
    have hG : G i = (fun v => xor (q v) ((constW k cj).testBit i.val)) := by
      funext v
      simp only [G, bits, Nat.testBit_xor, testBit_step, i.isLt, decide_true, Bool.true_and, q, p, F, ix]
    rw [hG]
    exact build_relax (build_seq (build_seq h1 h2) h3) le_rfl (by simp) (by omega)
  exact build_relax (build_seq H J) le_rfl Set.subset_union_right (by omega)

lemma rowSchedule {k n : Nat} (hk : 0 < k) {A : Set (Sig n)}
    (w u : (Fin n → Bool) → Nat) (hw : ∀ x, w x < 2 ^ k) (hu : ∀ x, u x < 2 ^ k)
    (hW : ∀ i : Fin k, bits w i ∈ A) (hU : ∀ i : Fin k, bits u i ∈ A) (t : Nat) :
    Build A (Set.range (fun i : Fin k => bits (fun x => rowWord k (w x) (u x) t) i)) (4 * k + 19 * k * t) := by
  induction t with
  | zero =>
    simpa [Nat.mul_comm, rowWord_zero] using
      (build_fin (fun i : Fin k => bits (fun x => rot k 1 (w x) ^^^ u x) i) 4
        (fun i => xorBitsG i (rotG hk hw hW 1 i) (hU i)))
  | succ t ih =>
    have H := roundG hk 1 (A := A ∪ Set.range (fun i : Fin k => bits (fun x => rowWord k (w x) (u x) t) i))
      w (fun x => rowWord k (w x) (u x) t) hw (fun x => rowWord_lt (hu x) (w x) t)
      (fun i => Or.inl (hW i)) (fun i => Or.inr ⟨i, rfl⟩) (2 * t) (t + 1)
    have heq : (fun i : Fin k => bits (fun x => rowWord k (w x) (u x) (t + 1)) i) =
        (fun i : Fin k => bits (fun x =>
          step k (rowWord k (w x) (u x) t ^^^ rot k 1 (rowWord k (w x) (u x) t) ^^^
            rot k (k - 1) (rowWord k (w x) (u x) t)) ^^^
          rot k (2 * t) (w x) ^^^ constW k (t + 1)) i) := by
      funext i x; simp only [bits, rowWord_succ]
    rw [heq]
    exact build_relax (build_seq ih H) le_rfl Set.subset_union_right (by rw [Nat.mul_succ]; omega)

lemma colSchedule {k n : Nat} (hk : 0 < k) {A : Set (Sig n)}
    (r : Nat) (w v : (Fin n → Bool) → Nat) (hw : ∀ x, w x < 2 ^ k) (hv : ∀ x, v x < 2 ^ k)
    (hW : ∀ i : Fin k, bits w i ∈ A) (hV : ∀ i : Fin k, bits v i ∈ A) (t : Nat) :
    Build A (Set.range (fun i : Fin k => bits (fun x => colWord k r (w x) (v x) t) i)) (4 * k + 19 * k * t) := by
  induction t with
  | zero =>
    simpa [Nat.mul_comm, colWord_zero] using
      (build_fin (fun i : Fin k => bits (fun x => rot k 3 (w x) ^^^ v x) i) 4
        (fun i => xorBitsG i (rotG hk hw hW 3 i) (hV i)))
  | succ t ih =>
    have H := roundG hk 2 (A := A ∪ Set.range (fun i : Fin k => bits (fun x => colWord k r (w x) (v x) t) i))
      w (fun x => colWord k r (w x) (v x) t) hw (fun x => colWord_lt (hv x) (w x) t)
      (fun i => Or.inl (hW i)) (fun i => Or.inr ⟨i, rfl⟩) (3 * (t + 1) + 1) (r + (t + 1))
    have heq : (fun i : Fin k => bits (fun x => colWord k r (w x) (v x) (t + 1)) i) =
        (fun i : Fin k => bits (fun x =>
          step k (colWord k r (w x) (v x) t ^^^ rot k 2 (colWord k r (w x) (v x) t) ^^^
            rot k (k - 2) (colWord k r (w x) (v x) t)) ^^^
          rot k (3 * (t + 1) + 1) (w x) ^^^ constW k (r + (t + 1))) i) := by
      funext i x; simp only [bits, colWord_succ]
    rw [heq]
    exact build_relax (build_seq ih H) le_rfl Set.subset_union_right (by rw [Nat.mul_succ]; omega)

lemma lt_two_pow_iff_high {n k a : Nat} (hn : n < 2 ^ k) :
    n < 2 ^ a ↔ ∀ i, a ≤ i → i < k → n.testBit i = false := by
  constructor
  · intro ha i hai _
    exact Nat.testBit_lt_two_pow (lt_of_lt_of_le ha (Nat.pow_le_pow_right (by decide) hai))
  · intro h
    apply Nat.lt_pow_two_of_testBit
    intro i hai
    by_cases hi : i < k
    · exact h i hai hi
    · exact big_bit_false hn (by omega)

lemma build_threshold {k n : Nat} {A : Set (Sig n)} (low : Nat) (w : (Fin n → Bool) → Nat)
    (hw : ∀ v, w v < 2 ^ k) (hs : ∀ i : Fin k, bits w i ∈ A) (hfalse : (fun _ => false) ∈ A) :
    Build A {fun v => decide (w v < 2 ^ low)} (k + 1) := by
  let xs : List (Fin k) := (List.finRange k).filter (fun i => decide (low ≤ i.val))
  have hs' : ∀ f ∈ xs.map (bits w), f ∈ A := by
    intro f hf; obtain ⟨i, _, rfl⟩ := List.mem_map.mp hf; exact hs i
  have he : (fun v => !((xs.map (bits w)).any (fun f => f v))) = (fun v => decide (w v < 2 ^ low)) := by
    funext v
    apply Bool.eq_iff_iff.mpr
    rw [Bool.not_eq_true', decide_eq_true_eq, lt_two_pow_iff_high (hw v)]
    simp only [List.any_eq_false, List.mem_map, forall_exists_index, and_imp]
    constructor
    · intro H i hi hik
      exact Bool.eq_false_iff.mpr (H _ ⟨i, hik⟩ (by simp [xs, hi]) rfl)
    · intro H f i hi hfe
      subst hfe
      exact Bool.eq_false_iff.mp (H _ (by simpa [xs] using hi) i.isLt)
  rw [← he]
  have H1 := build_any (xs.map (bits w)) hs' hfalse
  have H2 := build_not (A := A ∪ {fun v => (xs.map (bits w)).any (fun f => f v)}) (Or.inr rfl)
  refine build_relax (build_seq H1 H2) le_rfl (by simp) ?_
  simp only [List.length_map]
  have hlen : xs.length ≤ k := by
    simpa [xs] using List.length_filter_le (p := fun i : Fin k => decide (low ≤ i.val)) (List.finRange k)
  omega

lemma build_testSlot {k r : Nat} (hk : 0 < k) {A : Set (Sig (k + k))}
    (W : (Fin (k + k) → Bool) → Nat) (hWlt : ∀ v, W v < 2 ^ k)
    (hW : ∀ i : Fin k, bits W i ∈ A) (hBase : base (k + k) ⊆ A) :
    Build A {(fun v =>
      decide (rowWord k (W v) (U k v) r < 2 ^ (k - (k + 1) / 2)) &&
      decide (colWord k r (W v) (V k v) r < 2 ^ (k - (k + 1) / 2)))}
      (38 * k * r + 10 * k + 3) := by
  let low := k - (k + 1) / 2
  let R := Set.range (fun i : Fin k => bits (fun v => rowWord k (W v) (U k v) r) i)
  have HR : Build A R (4 * k + 19 * k * r) :=
    rowSchedule hk W (U k) hWlt (U_lt k) hW (fun i => hBase (bitU_mem k i)) r
  let C := Set.range (fun i : Fin k => bits (fun v => colWord k r (W v) (V k v) r) i)
  have HC : Build (A ∪ R) C (4 * k + 19 * k * r) :=
    colSchedule hk r W (V k) hWlt (V_lt k) (fun i => Or.inl (hW i))
      (fun i => Or.inl (hBase (bitV_mem k i))) r
  let rl : Sig (k + k) := fun v => decide (rowWord k (W v) (U k v) r < 2 ^ low)
  let cl : Sig (k + k) := fun v => decide (colWord k r (W v) (V k v) r < 2 ^ low)
  have Hrl : Build (A ∪ (R ∪ C)) {rl} (k + 1) :=
    build_threshold low _ (fun v => rowWord_lt (U_lt k v) (W v) r)
      (fun i => Or.inr (Or.inl ⟨i, rfl⟩)) (Or.inl (hBase (const_mem_base false)))
  have Hcl : Build (A ∪ ((R ∪ C) ∪ {rl})) {cl} (k + 1) :=
    build_threshold low _ (fun v => colWord_lt (V_lt k v) (W v) r)
      (fun i => Or.inr (Or.inl (Or.inr ⟨i, rfl⟩))) (Or.inl (hBase (const_mem_base false)))
  have HA : Build (A ∪ (((R ∪ C) ∪ {rl}) ∪ {cl})) {fun v => rl v && cl v} 1 :=
    build_and (Or.inr (Or.inl (Or.inr rfl))) (Or.inr (Or.inr rfl))
  refine build_relax (build_seq (build_seq (build_seq (build_seq HR HC) Hrl) Hcl) HA)
    le_rfl Set.subset_union_right ?_
  have h19 : 19 * k * r + 19 * k * r = 38 * k * r := by ring
  omega

lemma build_testFromX0 {k r : Nat} (hk : 0 < k) {A : Set (Sig (k + k))}
    (X0 : (Fin (k + k) → Bool) → Nat) (hX0lt : ∀ v, X0 v < 2 ^ k)
    (hX0 : ∀ i : Fin k, bits X0 i ∈ A) (hBase : base (k + k) ⊆ A) :
    let W := fun v => rot k (k - 1) (X0 v ^^^ U k v)
    Build A {(fun v =>
      decide (rowWord k (W v) (U k v) r < 2 ^ (k - (k + 1) / 2)) &&
      decide (colWord k r (W v) (V k v) r < 2 ^ (k - (k + 1) / 2)))}
      (38 * k * r + 14 * k + 3) := by
  intro W
  let XU := fun v => X0 v ^^^ U k v
  have Hxu : Build A (Set.range (fun i : Fin k => bits XU i)) (k * 4) :=
    build_fin (fun i => bits XU i) 4 (fun i => xorBitsG i (hX0 i) (hBase (bitU_mem k i)))
  have hWmem : ∀ i : Fin k, bits W i ∈ A ∪ Set.range (fun j : Fin k => bits XU j) := by
    intro i
    exact rotG hk (fun v => Nat.xor_lt_two_pow (hX0lt v) (U_lt k v))
      (fun j => Or.inr ⟨j, rfl⟩) (k - 1) i
  have Htest := build_testSlot (r := r) hk W (fun v => rot_lt k _ _) hWmem
    (hBase.trans Set.subset_union_left)
  exact build_relax (build_seq Hxu Htest) le_rfl Set.subset_union_right (by omega)

lemma build_stepZ {k : Nat} (hk : 0 < k) {A : Set (Sig (k + k))}
    {sm s0 s1 s2 s3 inj : Sig (k + k)}
    (hm : sm ∈ A) (h0 : s0 ∈ A) (h1 : s1 ∈ A) (h2 : s2 ∈ A) (h3 : s3 ∈ A)
    (hinj : inj ∈ A) (hBase : base (k + k) ⊆ A) (t : Nat) (z : Int) :
    Build A {(fun v =>
      let m0 := xor (xor (s0 v) (sm v)) (s1 v)
      let m1 := xor (xor (s1 v) (s0 v)) (s2 v)
      let m2 := xor (xor (s2 v) (s1 v)) (s3 v)
      xor (xor (xor m0 (!m1 && m2)) (inj v)) (pubBit k (U k v) (t + 1) z))} 39 := by
  let bf : Sig (k + k) := fun v =>
    let m0 := xor (xor (s0 v) (sm v)) (s1 v)
    let m1 := xor (xor (s1 v) (s0 v)) (s2 v)
    let m2 := xor (xor (s2 v) (s1 v)) (s3 v)
    xor m0 (!m1 && m2)
  let sA : Sig (k + k) := fun v => xor (bf v) (inj v)
  let uSig : Sig (k + k) := fun v => pz k (U k v) (z + 1 - 2 * (t : Int))
  let sB : Sig (k + k) := fun v => xor (sA v) (uSig v)
  let cBit : Bool := pz k (constW k (t + 1)) z
  have H1 : Build A {bf} 30 := build_befZ hm h0 h1 h2 h3
  have H2 : Build (A ∪ {bf}) {sA} 4 := build_xor (Or.inr rfl) (Or.inl hinj)
  have H3 : Build (A ∪ ({bf} ∪ {sA})) {sB} 4 :=
    build_xor (Or.inr (Or.inr rfl)) (Or.inl (hBase (pzU_mem hk _)))
  have H4 : Build (A ∪ (({bf} ∪ {sA}) ∪ {sB})) {fun v => xor (sB v) cBit} 1 :=
    build_flip (Or.inr (Or.inr rfl)) cBit
  have he : (fun v => xor (sB v) cBit) =
      (fun v => xor (xor (bf v) (inj v)) (pubBit k (U k v) (t + 1) z)) := by
    funext v
    simp only [sB, sA, uSig, cBit, pubBit, Nat.add_sub_cancel, Bool.xor_assoc]
  rw [← he]
  exact build_relax (build_seq (build_seq (build_seq H1 H2) H3) H4) le_rfl (by simp) (by omega)

def sweepSet {k : Nat} (T : Nat) (zLo0 zHi0 mHi : Int)
    (start : Int → Sig (k + k)) (d : Nat) : Set (Sig (k + k)) :=
  base (k + k) ∪
  {f | ∃ y : Int, mHi - (d : Int) < y ∧ y ≤ mHi ∧ f = start y} ∪
  {f | ∃ t : Nat, ∃ z : Int, t ≤ T ∧ zLo0 + (t : Int) ≤ z ∧ z ≤ zHi0 - 3 * (t : Int) ∧
    mHi - (d : Int) < z + loZ t ∧ z + loZ t ≤ mHi ∧
    f = fun v => stZ (pubBit k (U k v)) (fun y => start y v) t z}

lemma liftedSweep {k : Nat} (hk : 0 < k) (T : Nat) (zLo0 zHi0 mLo mHi : Int)
    (hm : mLo ≤ mHi) (hzHi : zHi0 ≤ mHi)
    (start : Int → Sig (k + k)) (recCost : Int → Nat)
    (hRec : ∀ d : Nat, d ≤ (mHi - mLo).toNat →
      Build (sweepSet T zLo0 zHi0 mHi start d) {start (mHi - (d : Int))} (recCost (mHi - (d : Int)))) :
    let L := (mHi - mLo).toNat + 1
    Build (base (k + k)) (sweepSet T zLo0 zHi0 mHi start L)
      ((∑ d ∈ Finset.range L, recCost (mHi - (d : Int))) +
       39 * ∑ t ∈ Finset.range T, (zHi0 - zLo0 + 1 - 4 * ((t + 1 : Nat) : Int)).toNat) := by
  intro L
  let cell : Nat → Int → Sig (k + k) :=
    fun t z v => stZ (pubBit k (U k v)) (fun y => start y v) t z
  let cellCost (d t : Nat) : Nat :=
    let m : Int := mHi - (d : Int)
    let z : Int := m - loZ (t + 1)
    if zLo0 + ((t + 1 : Nat) : Int) ≤ z ∧ z ≤ zHi0 - 3 * ((t + 1 : Nat) : Int) then 39 else 0
  have hstep : ∀ d : Nat, d < L →
      Build (sweepSet T zLo0 zHi0 mHi start d)
        (sweepSet T zLo0 zHi0 mHi start (d + 1))
        (recCost (mHi - (d : Int)) + ∑ t ∈ Finset.range T, cellCost d t) := by
    intro d hd
    let m : Int := mHi - (d : Int)
    have hrec_d : Build (sweepSet T zLo0 zHi0 mHi start d) {start m} (recCost m) :=
      hRec d (by dsimp [L] at hd; omega)
    let Q (s : Nat) : Set (Sig (k + k)) :=
      sweepSet T zLo0 zHi0 mHi start d ∪ {start m} ∪
      {f | ∃ t : Nat, t ≤ s ∧
        let z := m - loZ t
        zLo0 + (t : Int) ≤ z ∧ z ≤ zHi0 - 3 * (t : Int) ∧ f = cell t z}
    have hQ0 : Q 0 ⊆ sweepSet T zLo0 zHi0 mHi start d ∪ {start m} := by
      rintro f (hf | ⟨t, ht, _, _, rfl⟩)
      · exact hf
      · obtain rfl : t = 0 := by omega
        right
        simp only [Set.mem_singleton_iff, cell, stZ_zero, loZ]
        norm_num
    have hQstep : ∀ s : Nat, s < T → Build (Q s) (Q (s + 1)) (cellCost d s) := by
      intro s hs
      let z : Int := m - loZ (s + 1)
      by_cases hwin : zLo0 + ((s + 1 : Nat) : Int) ≤ z ∧ z ≤ zHi0 - 3 * ((s + 1 : Nat) : Int)
      · have hcc : cellCost d s = 39 := by simp only [cellCost, m, z, hwin, and_self, ↓reduceIte]
        rw [hcc]
        have hprev : ∀ j : Int, -1 ≤ j → j ≤ 3 → cell s (z + j) ∈ Q s := by
          intro j hj1 hj2
          have hl := loZ_succ s
          have hmz : m ≤ (z + j) + loZ s := by dsimp [z]; omega
          have hlo : zLo0 + (s : Int) ≤ z + j := by push_cast at hwin; omega
          have hhi : z + j ≤ zHi0 - 3 * (s : Int) := by push_cast at hwin; omega
          have hle_mHi : (z + j) + loZ s ≤ mHi := by
            have := loZ_nonpos s
            omega
          by_cases heq : (z + j) + loZ s = m
          · right
            refine ⟨s, le_refl s, ?_, ?_, ?_⟩
            · rwa [show m - loZ s = z + j by omega]
            · rwa [show m - loZ s = z + j by omega]
            · rw [show m - loZ s = z + j by omega]
          · left; left; right
            exact ⟨s, z + j, by omega, hlo, hhi, by dsimp [m] at heq hmz; omega, hle_mHi, rfl⟩
        have hinj : start (z + 1 - 2 * (s : Int)) ∈ Q s := by
          have hl := loZ_succ s
          have hy1 : m ≤ z + 1 - 2 * (s : Int) := by dsimp [z]; omega
          have hy2 : z + 1 - 2 * (s : Int) ≤ mHi := by push_cast at hwin; omega
          by_cases heq : z + 1 - 2 * (s : Int) = m
          · left; right; rw [heq]; rfl
          · left; left; left; right
            exact ⟨z + 1 - 2 * (s : Int), by dsimp [m] at hy1 heq; omega, hy2, rfl⟩
        have hBase : base (k + k) ⊆ Q s :=
          fun f hf => Or.inl (Or.inl (Or.inl (Or.inl hf)))
        have H1 := build_stepZ hk
          (hprev (-1) (by omega) (by omega))
          (hprev 0 (by omega) (by omega))
          (hprev 1 (by omega) (by omega))
          (hprev 2 (by omega) (by omega))
          (hprev 3 (by omega) (by omega))
          hinj hBase s z
        have heq_cell : cell (s + 1) z =
            (fun v =>
              let m0 := xor (xor (cell s (z + 0) v) (cell s (z + -1) v)) (cell s (z + 1) v)
              let m1 := xor (xor (cell s (z + 1) v) (cell s (z + 0) v)) (cell s (z + 2) v)
              let m2 := xor (xor (cell s (z + 2) v) (cell s (z + 1) v)) (cell s (z + 3) v)
              xor (xor (xor m0 (!m1 && m2)) (start (z + 1 - 2 * (s : Int)) v))
                (pubBit k (U k v) (s + 1) z)) := by
          funext v
          simp only [cell, stZ_succ, befZ_eq, add_zero, show z + -1 = z - 1 by omega]
        have H1' := build_seq (build_idle (le_refl (Q s)))
          (build_relax (C := Q s ∪ Q s) H1 Set.subset_union_left le_rfl le_rfl)
        refine build_relax H1' le_rfl ?_ (by omega)
        rintro f (hf | ⟨t, ht, hlo, hhi, rfl⟩)
        · exact Or.inl (Or.inl hf)
        · rcases Nat.lt_or_eq_of_le ht with hlt | rfl
          · exact Or.inl (Or.inr ⟨t, by omega, hlo, hhi, rfl⟩)
          · exact Or.inr (Set.mem_singleton_iff.mpr heq_cell)
      · have hcc : cellCost d s = 0 := by simp only [cellCost, m, z, hwin, ↓reduceIte]
        rw [hcc]
        apply build_idle
        rintro f (hf | ⟨t, ht, hlo, hhi, rfl⟩)
        · exact Or.inl hf
        · rcases Nat.lt_or_eq_of_le ht with hlt | rfl
          · exact Or.inr ⟨t, by omega, hlo, hhi, rfl⟩
          · exact absurd ⟨hlo, hhi⟩ hwin
    have hchain : Build (Q 0) (Q T) (∑ t ∈ Finset.range T, cellCost d t) := by
      have hch := build_chain (fun s => if s ≤ T then Q s else Q T)
        (fun s => if s < T then cellCost d s else 0) (fun s => by
          by_cases hs : s < T
          · simp only [show s ≤ T by omega, show s + 1 ≤ T by omega, hs, ↓reduceIte]
            exact hQstep s hs
          · by_cases hse : s = T
            · subst s
              simp only [le_refl, show ¬ T + 1 ≤ T by omega, show ¬ T < T by omega, ↓reduceIte]
              exact build_idle le_rfl
            · simp only [show ¬ s ≤ T by omega, show ¬ s + 1 ≤ T by omega, hs, ↓reduceIte]
              exact build_idle le_rfl) T
      simp only [Nat.zero_le, le_refl, ↓reduceIte] at hch
      have hsum : (∑ i ∈ Finset.range T, if i < T then cellCost d i else 0) =
          ∑ t ∈ Finset.range T, cellCost d t := by
        apply Finset.sum_congr rfl
        intro i hi
        simp [Finset.mem_range.mp hi]
      rwa [hsum] at hch
    have hQsub : sweepSet T zLo0 zHi0 mHi start (d + 1) ⊆ Q T := by
      rintro f ((hf | ⟨y, hy1, hy2, rfl⟩) | ⟨t, z, ht, hlo, hhi, hm1, hm2, rfl⟩)
      · exact Or.inl (Or.inl (Or.inl (Or.inl hf)))
      · by_cases hym : y = m
        · exact Or.inl (Or.inr (by rw [hym]; rfl))
        · exact Or.inl (Or.inl (Or.inl (Or.inr ⟨y, by dsimp [m] at hym; push_cast at hy1; omega, hy2, rfl⟩)))
      · by_cases hzm : z + loZ t = m
        · right
          refine ⟨t, ht, ?_, ?_, ?_⟩
          · rwa [show m - loZ t = z by omega]
          · rwa [show m - loZ t = z by omega]
          · rw [show m - loZ t = z by omega]
        · exact Or.inl (Or.inl (Or.inr ⟨t, z, ht, hlo, hhi,
            by dsimp [m] at hzm; push_cast at hm1; omega, hm2, rfl⟩))
    exact build_relax (build_seq hrec_d (build_relax hchain hQ0 hQsub le_rfl))
      le_rfl Set.subset_union_right le_rfl
  have houter := build_chain
    (fun d => if d ≤ L then sweepSet T zLo0 zHi0 mHi start d else sweepSet T zLo0 zHi0 mHi start L)
    (fun d => if d < L then recCost (mHi - (d : Int)) + ∑ t ∈ Finset.range T, cellCost d t else 0)
    (fun d => by
      by_cases hd : d < L
      · simp only [show d ≤ L by omega, show d + 1 ≤ L by omega, hd, ↓reduceIte]
        exact hstep d hd
      · by_cases hde : d = L
        · subst d
          simp only [le_refl, show ¬ L + 1 ≤ L by omega, show ¬ L < L by omega, ↓reduceIte]
          exact build_idle le_rfl
        · simp only [show ¬ d ≤ L by omega, show ¬ d + 1 ≤ L by omega, hd, ↓reduceIte]
          exact build_idle le_rfl) L
  simp only [Nat.zero_le, le_refl, ↓reduceIte] at houter
  have h0sub : sweepSet T zLo0 zHi0 mHi start 0 ⊆ base (k + k) := by
    rintro f ((hf | ⟨y, hy1, hy2, _⟩) | ⟨t, z, _, _, _, hm1, hm2, _⟩)
    · exact hf
    · omega
    · omega
  have hsum_eq :
      (∑ d ∈ Finset.range L, if d < L then recCost (mHi - (d : Int)) +
          ∑ t ∈ Finset.range T, cellCost d t else 0) =
      (∑ d ∈ Finset.range L, recCost (mHi - (d : Int))) +
      ∑ t ∈ Finset.range T, ∑ d ∈ Finset.range L, cellCost d t := by
    rw [Finset.sum_comm]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro d hd
    simp [Finset.mem_range.mp hd]
  have hinner : ∀ t ∈ Finset.range T,
      ∑ d ∈ Finset.range L, cellCost d t ≤
        39 * (zHi0 - zLo0 + 1 - 4 * ((t + 1 : Nat) : Int)).toNat := by
    intro t _
    let lo : Int := zLo0 + ((t + 1 : Nat) : Int)
    let hi : Int := zHi0 - 3 * ((t + 1 : Nat) : Int)
    have hsplit : ∑ d ∈ Finset.range L, cellCost d t =
        39 * ((Finset.range L).filter (fun d : Nat => lo ≤ mHi - (d : Int) - loZ (t + 1) ∧
          mHi - (d : Int) - loZ (t + 1) ≤ hi)).card := by
      trans ∑ d ∈ (Finset.range L).filter (fun d : Nat => lo ≤ mHi - (d : Int) - loZ (t + 1) ∧
          mHi - (d : Int) - loZ (t + 1) ≤ hi), 39
      · rw [Finset.sum_filter]
      · simp [Nat.mul_comm]
    rw [hsplit]
    apply Nat.mul_le_mul_left
    let S := (Finset.range L).filter (fun d : Nat => lo ≤ mHi - (d : Int) - loZ (t + 1) ∧
      mHi - (d : Int) - loZ (t + 1) ≤ hi)
    have hcard : S.card ≤ (Finset.range (hi + 1 - lo).toNat).card := by
      apply Finset.card_le_card_of_injOn (fun d : Nat => (mHi - (d : Int) - loZ (t + 1) - lo).toNat)
      · intro d hd
        simp only [S, Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at hd ⊢
        omega
      · intro d1 hd1 d2 hd2 heq
        simp only [S, Finset.mem_coe, Finset.mem_filter] at hd1 hd2
        dsimp only at heq
        omega
    rw [Finset.card_range] at hcard
    have heq_w : hi + 1 - lo = zHi0 - zLo0 + 1 - 4 * ((t + 1 : Nat) : Int) := by
      dsimp [lo, hi]; omega
    rwa [heq_w] at hcard
  have hsum_cells :
      ∑ t ∈ Finset.range T, ∑ d ∈ Finset.range L, cellCost d t ≤
        39 * ∑ t ∈ Finset.range T, (zHi0 - zLo0 + 1 - 4 * ((t + 1 : Nat) : Int)).toNat := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum hinner
  exact build_relax houter h0sub le_rfl (by rw [hsum_eq]; exact Nat.add_le_add_left hsum_cells _)

def visBit (k r q : Nat) (vis : Fin (2 ^ (k - q))) (b : Nat) : Bool :=
  let P0 := k - q - 2 * r + 3
  if b < P0 then vis.val.testBit b
  else if P0 + q ≤ b then vis.val.testBit (b - q)
  else false

def ordBase (k r q : Nat) (vis : Fin (2 ^ (k - q))) (z : Int) : Bool :=
  let P0 : Int := ((k - q - 2 * r + 3 : Nat) : Int)
  let H : Int := (k : Int) + P0
  if H ≤ z then false
  else if P0 + (q : Int) ≤ z then visBit k r q vis (res k z)
  else false

def ordStartStep (k r q u : Nat) (vis : Fin (2 ^ (k - q))) : Nat → Int → Bool
  | 0 => ordBase k r q vis
  | s + 1 =>
    let prev := ordStartStep k r q u vis s
    let P0 : Int := ((k - q - 2 * r + 3 : Nat) : Int)
    let a := q - 1 - s
    let pos : Int := P0 + (a : Int)
    let i : Int := ((k - q + a : Nat) : Int)
    let b := xor (befZ (stZ (pubBit k u) prev (r - 1)) i) (pubBit k u r i)
    fun z => if z = pos then b else prev z

def ordFinal (k r q u : Nat) (vis : Fin (2 ^ (k - q))) : Int → Bool :=
  ordStartStep k r q u vis q

lemma ordStartStep_agree_above (k r q u : Nat) (vis : Fin (2 ^ (k - q))) :
    ∀ s1 s2, s1 ≤ s2 → s2 ≤ q →
      ∀ z : Int, ((k - q - 2 * r + 3 : Nat) : Int) + ((q - s1 : Nat) : Int) ≤ z →
        ordStartStep k r q u vis s2 z = ordStartStep k r q u vis s1 z := by
  intro s1 s2 hle hsq
  induction s2 with
  | zero =>
    obtain rfl : s1 = 0 := by omega
    intro _ _; rfl
  | succ s2 ih =>
    intro z hz
    rcases Nat.lt_or_eq_of_le hle with hlt | rfl
    · simp only [ordStartStep]
      have hne : z ≠ ((k - q - 2 * r + 3 : Nat) : Int) + ((q - 1 - s2 : Nat) : Int) := by omega
      simp only [hne, ↓reduceIte]
      exact ih (by omega) (by omega) z hz
    · rfl

lemma ordFinal_outside (k r q u : Nat) (vis : Fin (2 ^ (k - q)))
    (z : Int) (hz : ((k - q - 2 * r + 3 : Nat) : Int) + (q : Int) ≤ z) :
    ordFinal k r q u vis z = ordBase k r q vis z :=
  ordStartStep_agree_above k r q u vis 0 q (Nat.zero_le q) le_rfl z (by simpa using hz)

lemma ordFinal_fixed {k r q u : Nat} (hr : 5 ≤ r) (hkr : 4 * r + 1 ≤ k) (hqr : q + 4 ≤ r)
    (vis : Fin (2 ^ (k - q))) (a : Nat) (ha : a < q) :
    let P0 : Int := ((k - q - 2 * r + 3 : Nat) : Int)
    let i : Int := ((k - q + a : Nat) : Int)
    ordFinal k r q u vis (P0 + (a : Int)) =
      xor (befZ (stZ (pubBit k u) (ordFinal k r q u vis) (r - 1)) i) (pubBit k u r i) := by
  intro P0 i
  let s := q - 1 - a
  have hs1 : s + 1 ≤ q := by omega
  have ha_eq : q - 1 - s = a := by omega
  have h1 := ordStartStep_agree_above k r q u vis (s + 1) q hs1 le_rfl (P0 + (a : Int)) (by dsimp [P0, s]; omega)
  unfold ordFinal
  rw [h1]
  simp only [ordStartStep, ha_eq, P0, ↓reduceIte]
  congr 1
  apply befZ_agree
  intro j hj1 hj2
  apply zdep
  intro y hy1 _
  have hlo : loZ (r - 1) = -2 * ((r - 1 : Nat) : Int) + 3 := loZ_ge3 (by omega)
  rw [hlo] at hy1
  have hy_ge : P0 + ((q - s : Nat) : Int) ≤ y := by dsimp [P0, i, s] at hy1 ⊢; omega
  exact (ordStartStep_agree_above k r q u vis s q (by omega) le_rfl y hy_ge).symm

lemma ordFinal_eq_other {k r q u : Nat} (hr : 5 ≤ r) (hkr : 4 * r + 1 ≤ k) (hqr : q + 4 ≤ r)
    (vis : Fin (2 ^ (k - q))) (x0 : Fin (2 ^ k))
    (hvis : ∀ b < k, (b < k - q - 2 * r + 3 ∨ k - q - 2 * r + 3 + q ≤ b) →
      visBit k r q vis b = x0.val.testBit b)
    (hmatch : ∀ a < q,
      let i : Int := ((k - q + a : Nat) : Int)
      let P0 : Int := ((k - q - 2 * r + 3 : Nat) : Int)
      let other : Int → Bool := fun z => if z < (k : Int) + P0 then pz k x0.val z else false
      xor (befZ (stZ (pubBit k u) other (r - 1)) i) (pubBit k u r i) = pz k x0.val (P0 + (a : Int))) :
    let P0 : Int := ((k - q - 2 * r + 3 : Nat) : Int)
    let other : Int → Bool := fun z => if z < (k : Int) + P0 then pz k x0.val z else false
    ∀ s ≤ q, ∀ z : Int, P0 + ((q - s : Nat) : Int) ≤ z →
      ordStartStep k r q u vis s z = other z := by
  intro P0 other s
  have hk0 : 0 < k := by omega
  induction s with
  | zero =>
    intro _ z hz
    simp only [ordStartStep, ordBase, Nat.sub_zero] at hz ⊢
    by_cases hH : (k : Int) + P0 ≤ z
    · simp only [show (k : Int) + ((k - q - 2 * r + 3 : Nat) : Int) ≤ z from hH, ↓reduceIte,
        other, show ¬ z < (k : Int) + P0 by omega]
    · simp only [show ¬ (k : Int) + ((k - q - 2 * r + 3 : Nat) : Int) ≤ z from hH, ↓reduceIte,
        show ((k - q - 2 * r + 3 : Nat) : Int) + (q : Int) ≤ z from hz,
        other, show z < (k : Int) + P0 by omega]
      have hres_lt : res k z < k := res_lt hk0 z
      have hres_out : res k z < k - q - 2 * r + 3 ∨ k - q - 2 * r + 3 + q ≤ res k z := by
        have hrc := res_cast hk0 z
        by_cases hzk : z < (k : Int)
        · have heq : (res k z : Int) = z := by
            rw [hrc, Int.emod_eq_of_lt (by dsimp [P0] at hz; omega) hzk]
          right; dsimp [P0] at hz; omega
        · have heq : (res k z : Int) = z - (k : Int) := by
            rw [hrc, ← Int.sub_emod_right, Int.emod_eq_of_lt (by omega) (by dsimp [P0] at hH; omega)]
          left; dsimp [P0] at hH; omega
      exact hvis (res k z) hres_lt hres_out
  | succ s ih =>
    intro hs z hz
    simp only [ordStartStep]
    let a := q - 1 - s
    let pos : Int := P0 + (a : Int)
    let i : Int := ((k - q + a : Nat) : Int)
    by_cases hzp : z = pos
    · subst hzp
      simp only [show pos = ((k - q - 2 * r + 3 : Nat) : Int) + ((q - 1 - s : Nat) : Int) from rfl,
        ↓reduceIte]
      have hbf : befZ (stZ (pubBit k u) (ordStartStep k r q u vis s) (r - 1)) i =
          befZ (stZ (pubBit k u) other (r - 1)) i := by
        apply befZ_agree
        intro j hj1 hj2
        apply zdep
        intro y hy1 _
        have hlo : loZ (r - 1) = -2 * ((r - 1 : Nat) : Int) + 3 := loZ_ge3 (by omega)
        rw [hlo] at hy1
        exact ih (by omega) y (by dsimp [P0, i, a] at hy1 ⊢; omega)
      rw [hbf]
      have hm := hmatch a (by omega)
      dsimp only at hm
      rw [hm]
      have hlt_H : ((k - q - 2 * r + 3 : Nat) : Int) + ((q - 1 - s : Nat) : Int) < (k : Int) + P0 := by
        dsimp [P0]; omega
      simp only [other, hlt_H, ↓reduceIte, a]
    · simp only [show ¬ z = ((k - q - 2 * r + 3 : Nat) : Int) + ((q - 1 - s : Nat) : Int) from hzp,
        ↓reduceIte]
      exact ih (by omega) z (by dsimp [pos, P0, a] at hzp hz ⊢; omega)

def ordX0 (k r q : Nat) (vis : Fin (2 ^ (k - q))) (v : Fin (k + k) → Bool) : Nat :=
  let P0 := k - q - 2 * r + 3
  tableIndex (fun b : Fin k =>
    if P0 ≤ b.val ∧ b.val < P0 + q then ordFinal k r q (U k v) vis (b.val : Int)
    else visBit k r q vis b.val)

lemma ordX0_lt (k r q : Nat) (vis : Fin (2 ^ (k - q))) (v : Fin (k + k) → Bool) :
    ordX0 k r q vis v < 2 ^ k := pack_lt _

lemma build_ordSlot {k r e q : Nat} (hq : 0 < q) (hkr : 4 * r + 1 ≤ k)
    (heqr : e + q + 4 ≤ r) (hke : k + e + 3 = 5 * r) (vis : Fin (2 ^ (k - q))) :
    let W := fun v => rot k (k - 1) (ordX0 k r q vis v ^^^ U k v)
    Build (base (k + k)) {(fun v =>
      decide (rowWord k (W v) (U k v) r < 2 ^ (k - (k + 1) / 2)) &&
      decide (colWord k r (W v) (V k v) r < 2 ^ (k - (k + 1) / 2)))}
      (77 * k * r + 14 * k + 35 * r + 3) := by
  intro W
  have hk0 : 0 < k := by omega
  have hr5 : 5 ≤ r := by omega
  let P0 : Nat := k - q - 2 * r + 3
  let zLo0 : Int := ((k - q - r : Nat) : Int)
  let zHi0 : Int := (k : Int) - 1 + 3 * (r : Int)
  let mLo : Int := (P0 : Int)
  let mHi : Int := zHi0
  let start : Int → Sig (k + k) := fun y v => ordFinal k r q (U k v) vis y
  let recCost : Int → Nat := fun m => if (P0 : Int) ≤ m ∧ m < (P0 : Int) + (q : Int) then 35 else 0
  have hm : mLo ≤ mHi := by dsimp [mLo, mHi, zHi0, P0]; omega
  have hRec : ∀ d : Nat, d ≤ (mHi - mLo).toNat →
      Build (sweepSet (r - 1) zLo0 zHi0 mHi start d) {start (mHi - (d : Int))} (recCost (mHi - (d : Int))) := by
    intro d hd
    let m : Int := mHi - (d : Int)
    by_cases hhid : (P0 : Int) ≤ m ∧ m < (P0 : Int) + (q : Int)
    · rw [show recCost m = 35 by simp only [recCost, hhid, and_self, ↓reduceIte]]
      let a : Nat := (m - (P0 : Int)).toNat
      have ha : a < q := by omega
      have hma : m = (P0 : Int) + (a : Int) := by omega
      let i : Int := ((k - q + a : Nat) : Int)
      have hcell : ∀ j : Int, -1 ≤ j → j ≤ 3 →
          (fun v => stZ (pubBit k (U k v)) (fun y => start y v) (r - 1) (i + j)) ∈
            sweepSet (r - 1) zLo0 zHi0 mHi start d := by
        intro j hj1 hj2
        right
        have hlo : loZ (r - 1) = -2 * ((r - 1 : Nat) : Int) + 3 := loZ_ge3 (by omega)
        refine ⟨r - 1, i + j, le_refl _, ?_, ?_, ?_, ?_, rfl⟩
        · dsimp [zLo0, i]; omega
        · dsimp [zHi0, i]; omega
        · rw [hlo]; dsimp [m, i, P0] at hma ⊢; omega
        · rw [hlo]; dsimp [mHi, zHi0, i]; omega
      let sAt (j : Int) : Sig (k + k) :=
        fun v => stZ (pubBit k (U k v)) (fun y => start y v) (r - 1) (i + j)
      let bf : Sig (k + k) := fun v =>
        let m0 := xor (xor (sAt 0 v) (sAt (-1) v)) (sAt 1 v)
        let m1 := xor (xor (sAt 1 v) (sAt 0 v)) (sAt 2 v)
        let m2 := xor (xor (sAt 2 v) (sAt 1 v)) (sAt 3 v)
        xor m0 (!m1 && m2)
      let uSig : Sig (k + k) := fun v => pz k (U k v) (i + 1 - 2 * ((r - 1 : Nat) : Int))
      let sB : Sig (k + k) := fun v => xor (bf v) (uSig v)
      let cBit : Bool := pz k (constW k r) i
      have H1 : Build (sweepSet (r - 1) zLo0 zHi0 mHi start d) {bf} 30 :=
        build_befZ (hcell (-1) (by omega) (by omega)) (hcell 0 (by omega) (by omega))
          (hcell 1 (by omega) (by omega)) (hcell 2 (by omega) (by omega))
          (hcell 3 (by omega) (by omega))
      have H2 : Build (sweepSet (r - 1) zLo0 zHi0 mHi start d ∪ {bf}) {sB} 4 :=
        build_xor (Or.inr rfl) (Or.inl (Or.inl (Or.inl (pzU_mem hk0 _))))
      have H3 : Build (sweepSet (r - 1) zLo0 zHi0 mHi start d ∪ ({bf} ∪ {sB}))
          {fun v => xor (sB v) cBit} 1 := build_flip (Or.inr (Or.inr rfl)) cBit
      have heq : start m = (fun v => xor (sB v) cBit) := by
        funext v
        rw [hma]
        have hfix := ordFinal_fixed hr5 hkr (by omega) vis a ha (u := U k v)
        dsimp only at hfix
        change ordFinal k r q (U k v) vis ((P0 : Int) + (a : Int)) = _
        rw [hfix]
        simp only [sB, bf, sAt, uSig, cBit, pubBit, befZ_eq, add_zero,
          show i + -1 = i - 1 by omega, Bool.xor_assoc, start, i]
      rw [heq]
      exact build_relax (build_seq (build_seq H1 H2) H3) le_rfl Set.subset_union_right (by omega)
    · rw [show recCost m = 0 by simp only [recCost, hhid, ↓reduceIte]]
      have hge : (P0 : Int) + (q : Int) ≤ m := by dsimp [m, mLo, P0] at hd hhid ⊢; omega
      have hconst : start m = fun _ => ordBase k r q vis m := by
        funext v
        exact ordFinal_outside k r q (U k v) vis m hge
      rw [hconst]
      exact build_idle (Set.singleton_subset_iff.mpr (Or.inl (Or.inl (const_mem_base _))))
  have Hsweep := liftedSweep hk0 (r - 1) zLo0 zHi0 mLo mHi hm le_rfl start recCost hRec
  let L := (mHi - mLo).toNat + 1
  have hX0mem : ∀ b : Fin k, bits (ordX0 k r q vis) b ∈ base (k + k) ∪ sweepSet (r - 1) zLo0 zHi0 mHi start L := by
    intro b
    by_cases hhid : P0 ≤ b.val ∧ b.val < P0 + q
    · right; left; right
      refine ⟨(b.val : Int), ?_, ?_, ?_⟩
      · dsimp [L, mLo, mHi, zHi0, P0]; omega
      · dsimp [mHi, zHi0, P0]; omega
      · funext v
        dsimp only [P0] at hhid
        simp only [bits, ordX0, bit_pack, hhid, and_self, ↓reduceIte, start]
    · left
      have heq : bits (ordX0 k r q vis) b = fun _ => visBit k r q vis b.val := by
        funext v
        dsimp only [P0] at hhid
        simp only [bits, ordX0, bit_pack, hhid, ↓reduceIte]
      rw [heq]
      exact const_mem_base _
  have Htest := build_testFromX0 (r := r) hk0 (ordX0 k r q vis) (ordX0_lt k r q vis) hX0mem
    Set.subset_union_left
  have hrec_sum : ∑ d ∈ Finset.range L, recCost (mHi - (d : Int)) ≤ 35 * r := by
    let F := (Finset.range L).filter (fun d : Nat => (P0 : Int) ≤ mHi - (d : Int) ∧ mHi - (d : Int) < (P0 : Int) + (q : Int))
    have h1 : ∑ d ∈ Finset.range L, recCost (mHi - (d : Int)) = 35 * F.card := by
      trans ∑ d ∈ F, 35
      · rw [Finset.sum_filter]
      · simp [Nat.mul_comm]
    rw [h1]
    have hF : F.card ≤ q := by
      have hc : F.card ≤ (Finset.range q).card := by
        apply Finset.card_le_card_of_injOn (fun d : Nat => (mHi - (d : Int) - (P0 : Int)).toNat)
        · intro d hd
          simp only [F, Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at hd ⊢; omega
        · intro d1 hd1 d2 hd2 heq
          simp only [F, Finset.mem_coe, Finset.mem_filter] at hd1 hd2
          dsimp only at heq
          omega
      simpa using hc
    have hqr : q ≤ r := by omega
    exact Nat.mul_le_mul_left 35 (hF.trans hqr)
  have hcell_sum : ∑ t ∈ Finset.range (r - 1), (zHi0 - zLo0 + 1 - 4 * ((t + 1 : Nat) : Int)).toNat ≤ k * r := by
    have hterm : ∀ t ∈ Finset.range (r - 1), (zHi0 - zLo0 + 1 - 4 * ((t + 1 : Nat) : Int)).toNat ≤ k := by
      intro t ht
      rw [Finset.mem_range] at ht
      dsimp [zLo0, zHi0]
      omega
    have h1 := Finset.sum_le_card_nsmul (Finset.range (r - 1)) _ k hterm
    simp only [Finset.card_range, smul_eq_mul] at h1
    exact h1.trans (by rw [Nat.mul_comm]; exact Nat.mul_le_mul_left k (by omega))
  refine build_relax (build_seq Hsweep Htest) le_rfl Set.subset_union_right ?_
  dsimp only [L] at hrec_sum
  have h39 := Nat.mul_le_mul_left 39 hcell_sum
  have h77 : 39 * (k * r) + 38 * k * r = 77 * k * r := by ring
  omega

def onesTr (tr : List Bool) (j : Nat) : Nat := (tr.take j).count true

lemma onesTr_mono (tr : List Bool) : ∀ a b, a ≤ b →
    onesTr tr a ≤ onesTr tr b ∧ onesTr tr b - onesTr tr a ≤ b - a := by
  intro a b hab
  unfold onesTr
  have hsp : tr.take b = tr.take a ++ (tr.drop a).take (b - a) := by
    rw [← List.take_add]; congr 1; omega
  rw [hsp, List.count_append]
  have hc : ((tr.drop a).take (b - a)).count true ≤ b - a :=
    (List.count_le_length).trans (by rw [List.length_take]; omega)
  omega

def placeTr (H : Int) (tr : List Bool) (j : Nat) : Int :=
  H - 3 * (5 + (j : Int)) + (onesTr tr j : Int)

def leadTr (H : Int) (tr : List Bool) (j : Nat) : Int :=
  H + 5 - 5 * (5 + (j : Int)) + (onesTr tr j : Int)

def pivsTr (k N : Nat) (H : Int) (tr : List Bool) : List Nat :=
  (List.range N).map (fun j => res k (leadTr H tr j))

def offsTr (k N : Nat) (H : Int) (tr : List Bool) : List Nat :=
  (List.range k).filter (fun b => decide (b ∉ pivsTr k N H tr))

lemma int_emod_ne_of_diff {k : Nat} {a b : Int} (hk : 0 < k) (h1 : 0 < b - a) (h2 : b - a < (k : Int)) :
    res k a ≠ res k b := by
  intro h
  have hmod : a % (k : Int) = b % (k : Int) := by
    rw [← res_cast hk a, ← res_cast hk b, h]
  have hsub : (b - a) % (k : Int) = 0 := by
    rw [Int.sub_emod, hmod, sub_self, Int.zero_emod]
  rw [Int.emod_eq_of_lt (by omega) h2] at hsub
  omega

lemma leadTr_strictAnti (H : Int) (tr : List Bool) {a b : Nat} (hab : a < b) :
    leadTr H tr b < leadTr H tr a := by
  have hm := onesTr_mono tr a b (by omega)
  unfold leadTr; omega

lemma pivsTr_nodup {k N : Nat} (hk : 5 * N + 15 ≤ k) (H : Int) (tr : List Bool) :
    (pivsTr k N H tr).Nodup := by
  unfold pivsTr
  rw [List.nodup_map_iff_inj_on List.nodup_range]
  intro a ha b hb hab
  simp only [List.mem_range] at ha hb
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
  · have hm := onesTr_mono tr a b (by omega)
    exact int_emod_ne_of_diff (by omega)
      (by unfold leadTr; omega) (by unfold leadTr; omega) hab.symm
  · have hm := onesTr_mono tr b a (by omega)
    exact int_emod_ne_of_diff (by omega)
      (by unfold leadTr; omega) (by unfold leadTr; omega) hab

lemma offsTr_length {k N : Nat} (hk : 5 * N + 15 ≤ k) (H : Int) (tr : List Bool) :
    (offsTr k N H tr).length = k - N := by
  let ps := pivsTr k N H tr
  have hnd : ps.Nodup := pivsTr_nodup hk H tr
  have hlt : ∀ p ∈ ps, p < k := by
    intro p hp
    simp only [ps, pivsTr, List.mem_map, List.mem_range] at hp
    rcases hp with ⟨j, _, rfl⟩
    exact res_lt (by omega) _
  have hps_len : ps.length = N := by simp [ps, pivsTr]
  have hsplit : ∀ l : List Nat,
      (l.filter (fun p => decide (p ∉ ps))).length +
      (l.filter (fun p => decide (p ∈ ps))).length = l.length := by
    intro l
    induction l with
    | nil => rfl
    | cons x xs ih =>
      by_cases hx : x ∈ ps
      · simp only [List.filter_cons, List.length_cons, hx, decide_true, decide_false,
          not_true_eq_false, Bool.false_eq_true, ↓reduceIte]
        omega
      · simp only [List.filter_cons, List.length_cons, hx, decide_false, decide_true,
          not_false_eq_true, Bool.false_eq_true, ↓reduceIte]
        omega
  have h1 := hsplit (List.range k)
  rw [List.length_range] at h1
  have h2 : ((List.range k).filter (fun p => decide (p ∈ ps))).length = ps.length := by
    have hnd1 : ((List.range k).filter (fun p => decide (p ∈ ps))).Nodup :=
      List.Nodup.filter _ List.nodup_range
    have heq : ((List.range k).filter (fun p => decide (p ∈ ps))).toFinset = ps.toFinset := by
      ext x
      simp only [List.mem_toFinset, List.mem_filter, List.mem_range, decide_eq_true_eq]
      exact ⟨fun h => h.2, fun h => ⟨hlt x h, h⟩⟩
    rw [← List.toFinset_card_of_nodup hnd1, heq, List.toFinset_card_of_nodup hnd]
  change ((List.range k).filter (fun p => decide (p ∉ ps))).length = _
  omega

def seedBit (k N : Nat) (H : Int) (tr : List Bool) (rest : Fin (2 ^ (k - N))) (b : Nat) : Bool :=
  match (offsTr k N H tr).findIdx? (fun x => decide (x = b)) with
  | some j => rest.val.testBit j
  | none => false

lemma seedBit_of_rest {k N : Nat} (hk : 5 * N + 15 ≤ k) (H : Int) (tr : List Bool)
    (x0 : Fin (2 ^ k)) :
    ∃ rest : Fin (2 ^ (k - N)),
      ∀ b < k, b ∉ pivsTr k N H tr → seedBit k N H tr rest b = x0.val.testBit b := by
  let offs := offsTr k N H tr
  have hlen : offs.length = k - N := offsTr_length hk H tr
  have hnd : offs.Nodup := List.Nodup.filter _ List.nodup_range
  let restVal := tableIndex (fun j : Fin (k - N) => x0.val.testBit (offs[j.val]'(by omega)))
  refine ⟨⟨restVal, pack_lt _⟩, fun b hb hnot => ?_⟩
  have hmem : b ∈ offs := by
    simp only [offs, offsTr, List.mem_filter, List.mem_range, decide_eq_true_eq]
    exact ⟨hb, hnot⟩
  rcases List.getElem_of_mem hmem with ⟨j, hj, hval⟩
  have hfind : offs.findIdx? (fun x => decide (x = b)) = some j := by
    rw [List.findIdx?_eq_some_iff_getElem]
    refine ⟨hj, by simp [hval], fun i hi => ?_⟩
    intro heq
    have h1 : offs[i] = b := of_decide_eq_true heq
    have hinj := (List.Nodup.getElem_inj_iff hnd).mp (h1.trans hval.symm)
    omega
  change (match offs.findIdx? (fun x => decide (x = b)) with
    | some j => restVal.testBit j
    | none => false) = x0.val.testBit b
  rw [hfind]
  dsimp only [restVal]
  rw [bit_pack _ ⟨j, by omega⟩, hval]

def excStartStep (k N u : Nat) (H : Int) (tr : List Bool) (rest : Fin (2 ^ (k - N))) :
    Nat → Int → Bool
  | 0 => fun z => seedBit k N H tr rest (res k z)
  | s + 1 =>
    let prev := excStartStep k N u H tr rest s
    let a := placeTr H tr s
    let L := leadTr H tr s
    let S3 := stZ (pubBit k u) prev (3 + s)
    let S4 := stZ (pubBit k u) prev (4 + s)
    let b := xor (xor (xor (xor (befZ S3 a) (pubBit k u (4 + s) a)) (S4 (a + 1))) (S4 (a + 2)))
      (tr.getD s false)
    fun z => if z = L then b else prev z

def excFinal (k N u : Nat) (H : Int) (tr : List Bool) (rest : Fin (2 ^ (k - N))) : Int → Bool :=
  excStartStep k N u H tr rest N

lemma excStartStep_agree_above (k N u : Nat) (H : Int) (tr : List Bool)
    (rest : Fin (2 ^ (k - N))) :
    ∀ s1 s2, s1 ≤ s2 → s2 ≤ N → ∀ z : Int,
      (∀ j, s1 ≤ j → j < s2 → z ≠ leadTr H tr j) →
      excStartStep k N u H tr rest s2 z = excStartStep k N u H tr rest s1 z := by
  intro s1 s2 hle hN
  induction s2 with
  | zero =>
    obtain rfl : s1 = 0 := by omega
    intro _ _; rfl
  | succ s2 ih =>
    intro z hz
    rcases Nat.lt_or_eq_of_le hle with hlt | rfl
    · simp only [excStartStep]
      have hne := hz s2 (by omega) (by omega)
      simp only [hne, ↓reduceIte]
      exact ih (by omega) (by omega) z (fun j h1 h2 => hz j h1 (by omega))
    · rfl

lemma excFinal_nonlead (k N u : Nat) (H : Int) (tr : List Bool)
    (rest : Fin (2 ^ (k - N))) (z : Int) (hz : ∀ j < N, z ≠ leadTr H tr j) :
    excFinal k N u H tr rest z = seedBit k N H tr rest (res k z) :=
  excStartStep_agree_above k N u H tr rest 0 N (Nat.zero_le N) le_rfl z (fun j _ hj => hz j hj)

lemma excFinal_fixed {k N u : Nat} (H : Int) (tr : List Bool) (rest : Fin (2 ^ (k - N)))
    (j : Nat) (hj : j < N) :
    let a := placeTr H tr j
    let L := leadTr H tr j
    let S3 := stZ (pubBit k u) (excFinal k N u H tr rest) (3 + j)
    let S4 := stZ (pubBit k u) (excFinal k N u H tr rest) (4 + j)
    excFinal k N u H tr rest L =
      xor (xor (xor (xor (befZ S3 a) (pubBit k u (4 + j) a)) (S4 (a + 1))) (S4 (a + 2)))
        (tr.getD j false) := by
  intro a L S3 S4
  have h1 := excStartStep_agree_above k N u H tr rest (j + 1) N (by omega) le_rfl L
    (fun j' h1 _ => ne_of_gt (leadTr_strictAnti H tr (by omega)))
  unfold excFinal
  rw [h1]
  simp only [excStartStep, L, a, ↓reduceIte]
  have hag : ∀ y : Int, leadTr H tr j < y →
      excStartStep k N u H tr rest j y = excFinal k N u H tr rest y := by
    intro y hy
    exact (excStartStep_agree_above k N u H tr rest j N (by omega) le_rfl y (fun j' hj' _ => by
      have : leadTr H tr j' ≤ leadTr H tr j := by
        rcases Nat.lt_or_eq_of_le hj' with hlt | rfl
        · exact le_of_lt (leadTr_strictAnti H tr hlt)
        · exact le_refl _
      omega)).symm
  have hbf : befZ (stZ (pubBit k u) (excStartStep k N u H tr rest j) (3 + j)) a = befZ S3 a := by
    apply befZ_agree
    intro c hc1 hc2
    apply zdep
    intro y hy1 _
    have hlo : loZ (3 + j) = -2 * ((3 + j : Nat) : Int) + 3 := loZ_ge3 (by omega)
    rw [hlo] at hy1
    exact hag y (by dsimp [a, placeTr, leadTr] at hy1 ⊢; omega)
  have h41 : stZ (pubBit k u) (excStartStep k N u H tr rest j) (4 + j) (a + 1) = S4 (a + 1) := by
    apply zdep
    intro y hy1 _
    have hlo : loZ (4 + j) = -2 * ((4 + j : Nat) : Int) + 3 := loZ_ge3 (by omega)
    rw [hlo] at hy1
    exact hag y (by dsimp [a, placeTr, leadTr] at hy1 ⊢; omega)
  have h42 : stZ (pubBit k u) (excStartStep k N u H tr rest j) (4 + j) (a + 2) = S4 (a + 2) := by
    apply zdep
    intro y hy1 _
    have hlo : loZ (4 + j) = -2 * ((4 + j : Nat) : Int) + 3 := loZ_ge3 (by omega)
    rw [hlo] at hy1
    exact hag y (by dsimp [a, placeTr, leadTr] at hy1 ⊢; omega)
  rw [hbf, h41, h42]

lemma excFinal_eq_x0 {k N u : Nat} (hN : 0 < N) (hk : 5 * N + 15 ≤ k) (H : Int)
    (tr : List Bool) (rest : Fin (2 ^ (k - N))) (x0 : Fin (2 ^ k))
    (htr : ∀ j < N,
      let a := placeTr H tr j
      let S4 := stZ (pubBit k u) (pz k x0.val) (4 + j)
      xor (xor (S4 a) (S4 (a + 1))) (S4 (a + 2)) = tr.getD j false)
    (hrest : ∀ b < k, b ∉ pivsTr k N H tr → seedBit k N H tr rest b = x0.val.testBit b) :
    ∀ s ≤ N, ∀ y : Int,
      leadTr H tr (N - 1) ≤ y →
      (∀ j, s ≤ j → j < N → leadTr H tr j < y) →
      y ≤ H - 1 + (onesTr tr (N - 1) : Int) →
      excStartStep k N u H tr rest s y = pz k x0.val y := by
  have hk0 : 0 < k := by omega
  have hnonpiv : ∀ y : Int, leadTr H tr (N - 1) ≤ y → y ≤ H - 1 + (onesTr tr (N - 1) : Int) →
      (∀ j < N, y ≠ leadTr H tr j) → res k y ∉ pivsTr k N H tr := by
    intro y hy1 hy2 hne hmem
    simp only [pivsTr, List.mem_map, List.mem_range] at hmem
    rcases hmem with ⟨j, hj, hres⟩
    have hm_j := onesTr_mono tr j (N - 1) (by omega)
    have hm_0 := onesTr_mono tr 0 (N - 1) (by omega)
    have hlj_ge : leadTr H tr (N - 1) ≤ leadTr H tr j := by unfold leadTr; omega
    have hlj_le : leadTr H tr j ≤ leadTr H tr 0 := by
      have hm0j := onesTr_mono tr 0 j (Nat.zero_le j)
      unfold leadTr; omega
    have hdiff_lt : y - leadTr H tr j < (k : Int) := by unfold leadTr at hlj_ge ⊢; omega
    have hdiff_gt : leadTr H tr j - y < (k : Int) := by
      unfold leadTr at hlj_le hy1 ⊢
      have : onesTr tr 0 = 0 := by simp [onesTr]
      omega
    rcases lt_or_gt_of_ne (hne j hj) with hlt | hgt
    · exact int_emod_ne_of_diff hk0 (by omega) hdiff_gt hres.symm
    · exact int_emod_ne_of_diff hk0 (by omega) hdiff_lt hres
  intro s
  induction s with
  | zero =>
    intro _ y hge hy1 hy2
    simp only [excStartStep]
    have hne : ∀ j < N, y ≠ leadTr H tr j := fun j hj => ne_of_gt (hy1 j (Nat.zero_le _) hj)
    exact hrest (res k y) (res_lt hk0 y) (hnonpiv y hge hy2 hne)
  | succ s ih =>
    intro hs y hge hy1 hy2
    simp only [excStartStep]
    let a := placeTr H tr s
    let L := leadTr H tr s
    by_cases hyL : y = L
    · subst hyL
      simp only [L, ↓reduceIte]
      have hbf : befZ (stZ (pubBit k u) (excStartStep k N u H tr rest s) (3 + s)) a =
          befZ (stZ (pubBit k u) (pz k x0.val) (3 + s)) a := by
        apply befZ_agree
        intro c hc1 hc2
        apply zdep
        intro w hw1 hw2
        have hlo : loZ (3 + s) = -2 * ((3 + s : Nat) : Int) + 3 := loZ_ge3 (by omega)
        rw [hlo] at hw1
        have hm_s := onesTr_mono tr s (N - 1) (by omega)
        apply ih (by omega) w
        · dsimp [a, placeTr, leadTr] at hw1 ⊢; omega
        · intro j hj1 hj2
          have hm_sj := onesTr_mono tr s j (by omega)
          dsimp [a, placeTr, leadTr] at hw1 ⊢; omega
        · dsimp [a, placeTr] at hw2 ⊢; omega
      have h4c : ∀ c : Int, 1 ≤ c → c ≤ 2 →
          stZ (pubBit k u) (excStartStep k N u H tr rest s) (4 + s) (a + c) =
            stZ (pubBit k u) (pz k x0.val) (4 + s) (a + c) := by
        intro c hc1 hc2
        apply zdep
        intro w hw1 hw2
        have hlo : loZ (4 + s) = -2 * ((4 + s : Nat) : Int) + 3 := loZ_ge3 (by omega)
        rw [hlo] at hw1
        have hm_s := onesTr_mono tr s (N - 1) (by omega)
        apply ih (by omega) w
        · dsimp [a, placeTr, leadTr] at hw1 ⊢; omega
        · intro j hj1 hj2
          have hm_sj := onesTr_mono tr s j (by omega)
          dsimp [a, placeTr, leadTr] at hw1 ⊢; omega
        · dsimp [a, placeTr] at hw2 ⊢; omega
      rw [hbf, h4c 1 le_rfl (by omega), h4c 2 (by omega) le_rfl, ← htr s (by omega)]
      have hst : stZ (pubBit k u) (pz k x0.val) (4 + s) a =
          xor (xor (befZ (stZ (pubBit k u) (pz k x0.val) (3 + s)) a) (pz k x0.val L))
            (pubBit k u (4 + s) a) := by
        rw [show 4 + s = (3 + s) + 1 by omega, stZ_succ,
          show a + 1 - 2 * ((3 + s : Nat) : Int) = L by dsimp [a, L, placeTr, leadTr]; omega]
      rw [hst]
      cases befZ (stZ (pubBit k u) (pz k x0.val) (3 + s)) a <;>
        cases pz k x0.val L <;> cases pubBit k u (4 + s) a <;>
        cases stZ (pubBit k u) (pz k x0.val) (4 + s) (a + 1) <;>
        cases stZ (pubBit k u) (pz k x0.val) (4 + s) (a + 2) <;> rfl
    · simp only [show ¬ y = leadTr H tr s from hyL, ↓reduceIte]
      by_cases hgt : L < y
      · apply ih (by omega) y hge _ hy2
        intro j hj1 hj2
        rcases Nat.lt_or_eq_of_le hj1 with hlt | rfl
        · exact hy1 j hlt hj2
        · exact hgt
      · have hlt : y < L := lt_of_le_of_ne (le_of_not_gt hgt) hyL
        have hne_all : ∀ j < N, y ≠ leadTr H tr j := by
          intro j hj
          by_cases hjs : j < s
          · exact ne_of_lt (lt_trans hlt (leadTr_strictAnti H tr hjs))
          · by_cases hje : j = s
            · subst hje; exact hyL
            · exact ne_of_gt (hy1 j (by omega) hj)
        have h0 := excStartStep_agree_above k N u H tr rest 0 s (Nat.zero_le s) (by omega) y
          (fun j _ hj => hne_all j (by omega))
        rw [h0]
        simp only [excStartStep]
        exact hrest (res k y) (res_lt hk0 y) (hnonpiv y hge hy2 hne_all)

def excX0 (k N : Nat) (H : Int) (tr : List Bool) (rest : Fin (2 ^ (k - N)))
    (v : Fin (k + k) → Bool) : Nat :=
  tableIndex (fun b : Fin k =>
    match (pivsTr k N H tr).findIdx? (fun p => decide (p = b.val)) with
    | some j => excFinal k N (U k v) H tr rest (leadTr H tr j)
    | none => seedBit k N H tr rest b.val)

lemma excX0_lt (k N : Nat) (H : Int) (tr : List Bool) (rest : Fin (2 ^ (k - N)))
    (v : Fin (k + k) → Bool) : excX0 k N H tr rest v < 2 ^ k := pack_lt _

lemma build_excSlot {k r N : Nat} (hN : 0 < N) (hNr : N + 4 ≤ r) (hk : 5 * N + 15 ≤ k)
    (H : Int) (tr : List Bool) (rest : Fin (2 ^ (k - N))) :
    let W := fun v => rot k (k - 1) (excX0 k N H tr rest v ^^^ U k v)
    Build (base (k + k)) {(fun v =>
      decide (rowWord k (W v) (U k v) r < 2 ^ (k - (k + 1) / 2)) &&
      decide (colWord k r (W v) (V k v) r < 2 ^ (k - (k + 1) / 2)))}
      (77 * k * r + 14 * k + 44 * r + 3) := by
  intro W
  have hk0 : 0 < k := by omega
  let oN : Int := (onesTr tr (N - 1) : Int)
  let zLo0 : Int := H - 15 - 4 * (N : Int) + oN
  let zHi0 : Int := H - 1 + oN
  let mLo : Int := leadTr H tr (N - 1)
  let mHi : Int := zHi0
  let start : Int → Sig (k + k) := fun y v => excFinal k N (U k v) H tr rest y
  let findJ (m : Int) : Option Nat := (List.range N).find? (fun j => decide (leadTr H tr j = m))
  let recCost : Int → Nat := fun m => if (findJ m).isSome then 44 else 0
  have hm : mLo ≤ mHi := by dsimp [mLo, mHi, zHi0, leadTr, oN]; omega
  have hRec : ∀ d : Nat, d ≤ (mHi - mLo).toNat →
      Build (sweepSet (N + 3) zLo0 zHi0 mHi start d) {start (mHi - (d : Int))}
        (recCost (mHi - (d : Int))) := by
    intro d _
    let m : Int := mHi - (d : Int)
    cases hfind : findJ m with
    | none =>
      rw [show recCost m = 0 by simp [recCost, hfind]]
      have hne : ∀ j < N, m ≠ leadTr H tr j := by
        intro j hj heq
        have hmem := List.find?_eq_none.mp hfind j (List.mem_range.mpr hj)
        exact hmem (by simp [heq])
      have hconst : start m = fun _ => seedBit k N H tr rest (res k m) := by
        funext v
        exact excFinal_nonlead k N (U k v) H tr rest m hne
      rw [hconst]
      exact build_idle (Set.singleton_subset_iff.mpr (Or.inl (Or.inl (const_mem_base _))))
    | some j =>
      rw [show recCost m = 44 by simp [recCost, hfind]]
      have hjN : j < N := List.mem_range.mp (List.mem_of_find?_eq_some hfind)
      have hmj : leadTr H tr j = m := by
        dsimp only [findJ] at hfind
        exact of_decide_eq_true (List.find?_some (p := fun j => decide (leadTr H tr j = m)) hfind)
      have hm_j := onesTr_mono tr j (N - 1) (by omega)
      let a : Int := placeTr H tr j
      have hcell3 : ∀ c : Int, -1 ≤ c → c ≤ 3 →
          (fun v => stZ (pubBit k (U k v)) (fun y => start y v) (3 + j) (a + c)) ∈
            sweepSet (N + 3) zLo0 zHi0 mHi start d := by
        intro c hc1 hc2
        right
        have hlo : loZ (3 + j) = -2 * ((3 + j : Nat) : Int) + 3 := loZ_ge3 (by omega)
        refine ⟨3 + j, a + c, by omega, ?_, ?_, ?_, ?_, rfl⟩
        · dsimp [zLo0, a, placeTr, oN]; omega
        · dsimp [zHi0, a, placeTr, oN]; omega
        · rw [hlo]; dsimp [m, a, placeTr, leadTr] at hmj ⊢; omega
        · rw [hlo]; dsimp [mHi, zHi0, a, placeTr, oN]; omega
      have hcell4 : ∀ c : Int, 1 ≤ c → c ≤ 2 →
          (fun v => stZ (pubBit k (U k v)) (fun y => start y v) (4 + j) (a + c)) ∈
            sweepSet (N + 3) zLo0 zHi0 mHi start d := by
        intro c hc1 hc2
        right
        have hlo : loZ (4 + j) = -2 * ((4 + j : Nat) : Int) + 3 := loZ_ge3 (by omega)
        refine ⟨4 + j, a + c, by omega, ?_, ?_, ?_, ?_, rfl⟩
        · dsimp [zLo0, a, placeTr, oN]; omega
        · dsimp [zHi0, a, placeTr, oN]; omega
        · rw [hlo]; dsimp [m, a, placeTr, leadTr] at hmj ⊢; omega
        · rw [hlo]; dsimp [mHi, zHi0, a, placeTr, oN]; omega
      let s3 (c : Int) : Sig (k + k) :=
        fun v => stZ (pubBit k (U k v)) (fun y => start y v) (3 + j) (a + c)
      let s4 (c : Int) : Sig (k + k) :=
        fun v => stZ (pubBit k (U k v)) (fun y => start y v) (4 + j) (a + c)
      let bf : Sig (k + k) := fun v =>
        let m0 := xor (xor (s3 0 v) (s3 (-1) v)) (s3 1 v)
        let m1 := xor (xor (s3 1 v) (s3 0 v)) (s3 2 v)
        let m2 := xor (xor (s3 2 v) (s3 1 v)) (s3 3 v)
        xor m0 (!m1 && m2)
      let uSig : Sig (k + k) := fun v => pz k (U k v) (a + 1 - 2 * ((3 + j : Nat) : Int))
      let p1 : Sig (k + k) := fun v => xor (bf v) (uSig v)
      let c1 : Bool := pz k (constW k (4 + j)) a
      let p2 : Sig (k + k) := fun v => xor (p1 v) c1
      let p3 : Sig (k + k) := fun v => xor (p2 v) (s4 1 v)
      let p4 : Sig (k + k) := fun v => xor (p3 v) (s4 2 v)
      let p5 : Sig (k + k) := fun v => xor (p4 v) (tr.getD j false)
      let S0 := sweepSet (N + 3) zLo0 zHi0 mHi start d
      have H1 : Build S0 {bf} 30 :=
        build_befZ (hcell3 (-1) (by omega) (by omega)) (hcell3 0 (by omega) (by omega))
          (hcell3 1 (by omega) (by omega)) (hcell3 2 (by omega) (by omega))
          (hcell3 3 (by omega) (by omega))
      have H2 : Build (S0 ∪ {bf}) {p1} 4 :=
        build_xor (Or.inr rfl) (Or.inl (Or.inl (Or.inl (pzU_mem hk0 _))))
      have H3 : Build (S0 ∪ ({bf} ∪ {p1})) {p2} 1 := build_flip (Or.inr (Or.inr rfl)) c1
      have H4 : Build (S0 ∪ (({bf} ∪ {p1}) ∪ {p2})) {p3} 4 :=
        build_xor (Or.inr (Or.inr rfl)) (Or.inl (hcell4 1 le_rfl (by omega)))
      have H5 : Build (S0 ∪ ((({bf} ∪ {p1}) ∪ {p2}) ∪ {p3})) {p4} 4 :=
        build_xor (Or.inr (Or.inr rfl)) (Or.inl (hcell4 2 (by omega) le_rfl))
      have H6 : Build (S0 ∪ (((({bf} ∪ {p1}) ∪ {p2}) ∪ {p3}) ∪ {p4})) {p5} 1 :=
        build_flip (Or.inr (Or.inr rfl)) (tr.getD j false)
      have heq : start m = p5 := by
        funext v
        rw [← hmj]
        have hfix := excFinal_fixed (k := k) (N := N) (u := U k v) H tr rest j hjN
        dsimp only at hfix
        change excFinal k N (U k v) H tr rest (leadTr H tr j) = _
        rw [hfix]
        simp only [p5, p4, p3, p2, p1, bf, s3, s4, uSig, c1, pubBit, befZ_eq, add_zero,
          show a + -1 = a - 1 by omega, show 4 + j - 1 = 3 + j by omega,
          Bool.xor_assoc, start, a]
      rw [heq]
      exact build_relax
        (build_seq (build_seq (build_seq (build_seq (build_seq H1 H2) H3) H4) H5) H6)
        le_rfl (by simp) (by omega)
  have Hsweep := liftedSweep hk0 (N + 3) zLo0 zHi0 mLo mHi hm le_rfl start recCost hRec
  let L := (mHi - mLo).toNat + 1
  have hX0mem : ∀ b : Fin k, bits (excX0 k N H tr rest) b ∈
      base (k + k) ∪ sweepSet (N + 3) zLo0 zHi0 mHi start L := by
    intro b
    cases hfind : (pivsTr k N H tr).findIdx? (fun p => decide (p = b.val)) with
    | none =>
      left
      have heq : bits (excX0 k N H tr rest) b = fun _ => seedBit k N H tr rest b.val := by
        funext v; simp only [bits, excX0, bit_pack, hfind]
      rw [heq]
      exact const_mem_base _
    | some j =>
      have hjN : j < N := by
        have := (List.findIdx?_eq_some_iff_getElem.mp hfind).1
        simpa [pivsTr] using this
      have hm_j := onesTr_mono tr j (N - 1) (by omega)
      have hm_0 := onesTr_mono tr 0 j (Nat.zero_le j)
      right; left; right
      refine ⟨leadTr H tr j, ?_, ?_, ?_⟩
      · dsimp [L, mLo, mHi, zHi0, leadTr, oN]; omega
      · dsimp [mHi, zHi0, leadTr, oN]; omega
      · funext v; simp only [bits, excX0, bit_pack, hfind, start]
  have Htest := build_testFromX0 (r := r) hk0 (excX0 k N H tr rest) (excX0_lt k N H tr rest) hX0mem
    Set.subset_union_left
  have hrec_sum : ∑ d ∈ Finset.range L, recCost (mHi - (d : Int)) ≤ 44 * r := by
    let F := (Finset.range L).filter (fun d : Nat => (findJ (mHi - (d : Int))).isSome = true)
    have h1 : ∑ d ∈ Finset.range L, recCost (mHi - (d : Int)) = 44 * F.card := by
      trans ∑ d ∈ F, 44
      · rw [Finset.sum_filter]
      · simp [Nat.mul_comm]
    rw [h1]
    have hF : F.card ≤ N := by
      have hc : F.card ≤ (Finset.range N).card := by
        apply Finset.card_le_card_of_injOn (fun d : Nat => (findJ (mHi - (d : Int))).getD 0)
        · intro d hd
          simp only [F, Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at hd ⊢
          cases hf : findJ (mHi - (d : Int)) with
          | none => simp [hf] at hd
          | some j =>
            simp only [Option.getD_some]
            exact List.mem_range.mp (List.mem_of_find?_eq_some hf)
        · intro d1 hd1 d2 hd2 heq
          simp only [F, Finset.mem_coe, Finset.mem_filter] at hd1 hd2
          cases hf1 : findJ (mHi - (d1 : Int)) with
          | none => simp [hf1] at hd1
          | some j1 =>
            cases hf2 : findJ (mHi - (d2 : Int)) with
            | none => simp [hf2] at hd2
            | some j2 =>
              simp only [hf1, hf2, Option.getD_some] at heq
              subst heq
              dsimp only [findJ] at hf1 hf2
              have e1 : leadTr H tr j1 = mHi - (d1 : Int) :=
                of_decide_eq_true (List.find?_some (p := fun j => decide (leadTr H tr j = mHi - (d1 : Int))) hf1)
              have e2 : leadTr H tr j1 = mHi - (d2 : Int) :=
                of_decide_eq_true (List.find?_some (p := fun j => decide (leadTr H tr j = mHi - (d2 : Int))) hf2)
              omega
      simpa using hc
    exact Nat.mul_le_mul_left 44 (hF.trans (by omega))
  have hcell_sum : ∑ t ∈ Finset.range (N + 3), (zHi0 - zLo0 + 1 - 4 * ((t + 1 : Nat) : Int)).toNat ≤ k * r := by
    have hterm : ∀ t ∈ Finset.range (N + 3), (zHi0 - zLo0 + 1 - 4 * ((t + 1 : Nat) : Int)).toNat ≤ k := by
      intro t _
      dsimp [zLo0, zHi0, oN]
      omega
    have h1 := Finset.sum_le_card_nsmul (Finset.range (N + 3)) _ k hterm
    simp only [Finset.card_range, smul_eq_mul] at h1
    exact h1.trans (by rw [Nat.mul_comm]; exact Nat.mul_le_mul_left k (by omega))
  refine build_relax (build_seq Hsweep Htest) le_rfl Set.subset_union_right ?_
  dsimp only [L] at hrec_sum
  have h39 := Nat.mul_le_mul_left 39 hcell_sum
  have h77 : 39 * (k * r) + 38 * k * r = 77 * k * r := by ring
  omega

def exactWeight : Nat → Nat → List (List Bool)
  | 0, 0 => [[]]
  | 0, _ + 1 => []
  | n + 1, 0 => (exactWeight n 0).map (false :: ·)
  | n + 1, d + 1 => (exactWeight n (d + 1)).map (false :: ·) ++ (exactWeight n d).map (true :: ·)

lemma exactWeight_length : ∀ n d, (exactWeight n d).length = Nat.choose n d
  | 0, 0 => rfl
  | 0, _ + 1 => rfl
  | n + 1, 0 => by simp [exactWeight, exactWeight_length n 0]
  | n + 1, d + 1 => by
    simp only [exactWeight, List.length_append, List.length_map, exactWeight_length,
      Nat.choose_succ_succ, Nat.add_comm]

lemma mem_exactWeight : ∀ n d (w : List Bool),
    w ∈ exactWeight n d ↔ w.length = n ∧ w.count true = d
  | 0, 0, w => by cases w <;> simp [exactWeight]
  | 0, d + 1, w => by cases w <;> simp [exactWeight]
  | n + 1, 0, w => by
    cases w with
    | nil => simp [exactWeight]
    | cons b bs =>
      cases b <;> simp [exactWeight, mem_exactWeight n 0 bs]
  | n + 1, d + 1, w => by
    cases w with
    | nil => simp [exactWeight]
    | cons b bs =>
      cases b <;> simp [exactWeight, mem_exactWeight]

def lowWeight (n D : Nat) : List (List Bool) :=
  (List.range (D + 1)).flatMap (exactWeight n)

lemma mem_lowWeight (n D : Nat) (w : List Bool) :
    w ∈ lowWeight n D ↔ w.length = n ∧ w.count true ≤ D := by
  simp only [lowWeight, List.mem_flatMap, List.mem_range, mem_exactWeight]
  constructor
  · rintro ⟨d, hd, hl, hc⟩; exact ⟨hl, by omega⟩
  · rintro ⟨hl, hc⟩; exact ⟨w.count true, by omega, hl, rfl⟩

lemma lowWeight_length (n D : Nat) :
    (lowWeight n D).length = ∑ j ∈ Finset.range (D + 1), Nat.choose n j := by
  unfold lowWeight
  induction D with
  | zero => simp [exactWeight_length]
  | succ D ih =>
    rw [List.range_succ, List.flatMap_append, List.length_append, Finset.sum_range_succ, ih]
    simp [exactWeight_length]

lemma flatMap_length_const {α β : Type} (l : List α) (f : α → List β) (m : Nat)
    (hm : ∀ x ∈ l, (f x).length = m) : (l.flatMap f).length = l.length * m := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    simp only [List.flatMap_cons, List.length_append, List.length_cons,
      hm x List.mem_cons_self, ih (fun y hy => hm y (List.mem_cons_of_mem x hy)), Nat.succ_mul]
    omega

theorem main (k r e q : Nat) (hq : 0 < q) (hkr : 4 * r + 1 ≤ k)
    (heqr : e + q + 4 ≤ r) (hke : k + e + 3 = 5 * r) :
    let h := (k + 1) / 2
    let T := min r ((k + 5) / 5)
    let N := T - 4
    let D := e + q - 1
    let exceptions := 2 ^ (k - N) * (∑ j ∈ Finset.range (D + 1), Nat.choose N j)
    D < N →
    ∃ C : Circuit, FanInTwo C ∧ ReadsBack (k + k) C ∧
      C.size ≤ 256 * (k + 1) * (r + 1) * (2 ^ (k - q) + exceptions) ∧
      ∀ bits : Fin (k + k) → Bool,
        C.eval (List.ofFn bits) =
          (List.range (2 ^ k)).any (fun w =>
            decide (rowWord k w (U k bits) r < 2 ^ (k - h)) &&
            decide (colWord k r w (V k bits) r < 2 ^ (k - h))) := by
  intro h T N D exceptions hDN
  have hr5 : 5 ≤ r := by omega
  have hk2 : 2 ≤ k := by omega
  have hk0 : 0 < k := by omega
  have hNpos : 0 < N := by omega
  have hTge5 : 5 ≤ T := by dsimp [N] at hNpos; omega
  have hNr : N + 4 ≤ r := by
    have : T ≤ r := Nat.min_le_left _ _
    dsimp [N] at hNpos ⊢; omega
  have h5N : 5 * N + 15 ≤ k := by
    have h1 : T ≤ (k + 5) / 5 := Nat.min_le_right _ _
    have h2 : 5 * T ≤ k + 5 := by omega
    dsimp [N] at hNpos ⊢; omega
  let P0 : Nat := k - q - 2 * r + 3
  let H : Int := (k : Int) + (P0 : Int)
  let S : Nat := 77 * k * r + 14 * k + 44 * r + 3
  let WordTest (W : (Fin (k + k) → Bool) → Nat) : Sig (k + k) := fun v =>
    decide (rowWord k (W v) (U k v) r < 2 ^ (k - h)) &&
    decide (colWord k r (W v) (V k v) r < 2 ^ (k - h))
  let ordW (vis : Fin (2 ^ (k - q))) (v : Fin (k + k) → Bool) : Nat :=
    rot k (k - 1) (ordX0 k r q vis v ^^^ U k v)
  let excW (tr : List Bool) (rest : Fin (2 ^ (k - N))) (v : Fin (k + k) → Bool) : Nat :=
    rot k (k - 1) (excX0 k N H tr rest v ^^^ U k v)
  let ordSlots : List (Sig (k + k)) := (List.finRange (2 ^ (k - q))).map (fun vis => WordTest (ordW vis))
  let excSlots : List (Sig (k + k)) :=
    (lowWeight N D).flatMap (fun tr =>
      (List.finRange (2 ^ (k - N))).map (fun rest => WordTest (excW tr rest)))
  let allSlots : List (Sig (k + k)) := ordSlots ++ excSlots
  have hall_build : ∀ f ∈ allSlots, Build (base (k + k)) {f} S := by
    intro f hf
    rcases List.mem_append.mp hf with hf | hf
    · rcases List.mem_map.mp hf with ⟨vis, _, rfl⟩
      exact build_relax (build_ordSlot hq hkr heqr hke vis) le_rfl le_rfl (by dsimp [S]; omega)
    · rcases List.mem_flatMap.mp hf with ⟨tr, _, hf1⟩
      rcases List.mem_map.mp hf1 with ⟨rest, _, rfl⟩
      exact build_excSlot hNpos hNr h5N H tr rest
  have Hs : Build (base (k + k)) {f | ∃ g ∈ allSlots, f = g} (allSlots.length * S) :=
    build_list allSlots id S hall_build
  let O : Sig (k + k) := fun v => allSlots.any (fun f => f v)
  have Ho : Build (base (k + k) ∪ {f | ∃ g ∈ allSlots, f = g}) {O} allSlots.length :=
    build_any allSlots (fun f hf => Or.inr ⟨f, hf, rfl⟩) (Or.inl (const_mem_base false))
  have Htot : Build (inputs (k + k)) {O} (2 + (allSlots.length * S + allSlots.length)) :=
    build_relax (build_seq (build_base_exact (k + k)) (build_seq Hs Ho)) le_rfl
      (Set.singleton_subset_iff.mpr (Or.inr (Or.inr rfl))) le_rfl
  obtain ⟨c, hc, HS⟩ := Htot.2 (sched_start (k + k)) le_rfl
  obtain ⟨C, hfan, hread, hsize, hout⟩ := sched_finish HS (Or.inr (Set.mem_singleton O))
  have hlen_ord : ordSlots.length = 2 ^ (k - q) := by simp [ordSlots]
  have hlen_exc : excSlots.length = exceptions := by
    dsimp only [excSlots, exceptions]
    rw [flatMap_length_const (lowWeight N D) _ (2 ^ (k - N)) (fun _ _ => by simp),
      lowWeight_length, Nat.mul_comm]
  have hlen_all : allSlots.length = 2 ^ (k - q) + exceptions := by
    dsimp only [allSlots]; rw [List.length_append, hlen_ord, hlen_exc]
  refine ⟨C, hfan, hread, ?_, fun v => ?_⟩
  · rw [hsize, Nat.zero_add]
    have hMpos : 1 ≤ allSlots.length := by
      rw [hlen_all]; have := Nat.two_pow_pos (k - q); omega
    have hS3 : S + 3 ≤ 256 * (k + 1) * (r + 1) := by
      dsimp [S]
      nlinarith
    have h1 : c ≤ allSlots.length * (S + 3) := by
      rw [Nat.mul_add]; omega
    have h2 := h1.trans (Nat.mul_le_mul_left allSlots.length hS3)
    rw [hlen_all, Nat.mul_comm] at h2
    exact h2
  · rw [hout]
    change O v = _
    apply Bool.eq_iff_iff.mpr
    simp only [O, List.any_eq_true, List.mem_range]
    constructor
    · rintro ⟨f, hf, hfv⟩
      rcases List.mem_append.mp hf with hf | hf
      · rcases List.mem_map.mp hf with ⟨vis, _, rfl⟩
        exact ⟨ordW vis v, rot_lt k _ _, hfv⟩
      · rcases List.mem_flatMap.mp hf with ⟨tr, _, hf1⟩
        rcases List.mem_map.mp hf1 with ⟨rest, _, rfl⟩
        exact ⟨excW tr rest v, rot_lt k _ _, hfv⟩
    · rintro ⟨w, hw, hpass⟩
      have hrow : rowWord k w (U k v) r < 2 ^ (k - h) :=
        of_decide_eq_true (Bool.and_eq_true_iff.mp hpass).1
      let x0Val : Nat := rot k 1 w ^^^ U k v
      have hx0lt : x0Val < 2 ^ k := Nat.xor_lt_two_pow (rot_lt k 1 w) (U_lt k v)
      let x0 : Fin (2 ^ k) := ⟨x0Val, hx0lt⟩
      let tr := actualTrace (pubBit k (U k v)) (pz k x0Val) H N
      have htr_len : tr.length = N := actualTrace_length _ _ _ N
      have htr_spec : ∀ j < N,
          let a := placeTr H tr j
          let S4 := stZ (pubBit k (U k v)) (pz k x0Val) (4 + j)
          xor (xor (S4 a) (S4 (a + 1))) (S4 (a + 2)) = tr.getD j false := by
        intro j hj
        exact (actualTrace_getD (pubBit k (U k v)) (pz k x0Val) H N j hj).symm
      by_cases hwt : tr.count true ≤ D
      · obtain ⟨rest, hrest⟩ := seedBit_of_rest h5N H tr x0
        have heq_x0 : excX0 k N H tr rest v = x0Val := by
          apply Nat.eq_of_testBit_eq
          intro b
          by_cases hb : b < k
          · simp only [excX0, bit_pack _ ⟨b, hb⟩]
            cases hfind : (pivsTr k N H tr).findIdx? (fun p => decide (p = b)) with
            | none =>
              have hnot : b ∉ pivsTr k N H tr := by
                intro hmem
                have hsome : ((pivsTr k N H tr).findIdx? (fun p => decide (p = b))).isSome = true := by
                  rw [List.findIdx?_isSome, List.any_eq_true]
                  exact ⟨b, hmem, by simp⟩
                simp [hfind] at hsome
              exact hrest b hb hnot
            | some j =>
              have hspec := List.findIdx?_eq_some_iff_getElem.mp hfind
              have hjN : j < N := by simpa [pivsTr] using hspec.1
              have hres_eq : res k (leadTr H tr j) = b := by
                have h1 := of_decide_eq_true hspec.2.1
                simp only [pivsTr, List.getElem_map, List.getElem_range] at h1
                exact h1
              have hmatch := excFinal_eq_x0 hNpos h5N H tr rest x0 htr_spec hrest N le_rfl
                (leadTr H tr j)
                (by have := onesTr_mono tr j (N - 1) (by omega); unfold leadTr; omega)
                (fun _ h1 h2 => by omega)
                (by have := onesTr_mono tr j (N - 1) (by omega); unfold leadTr; omega)
              dsimp only [excFinal]
              rw [hmatch]
              simp only [pz, hres_eq]
              rfl
          · rw [big_bit_false (excX0_lt k N H tr rest v) (by omega), big_bit_false hx0lt (by omega)]
        have heq_w : excW tr rest v = w := by
          dsimp only [excW]
          rw [heq_x0]
          exact recover_key hk2 hw (U_lt k v)
        refine ⟨WordTest (excW tr rest), List.mem_append_right _ ?_, ?_⟩
        · rw [List.mem_flatMap]
          refine ⟨tr, (mem_lowWeight N D tr).mpr ⟨htr_len, hwt⟩, ?_⟩
          rw [List.mem_map]
          exact ⟨rest, List.mem_finRange rest, rfl⟩
        · simpa only [WordTest, heq_w] using hpass
      · let visVal : Nat := tableIndex (fun j : Fin (k - q) =>
            if j.val < P0 then x0Val.testBit j.val else x0Val.testBit (j.val + q))
        let vis : Fin (2 ^ (k - q)) := ⟨visVal, pack_lt _⟩
        have hvis : ∀ b < k, (b < P0 ∨ P0 + q ≤ b) → visBit k r q vis b = x0Val.testBit b := by
          intro b hb hbp
          unfold visBit
          change (if b < P0 then visVal.testBit b
            else if P0 + q ≤ b then visVal.testBit (b - q) else false) = _
          by_cases h1 : b < P0
          · simp only [h1, ↓reduceIte]
            dsimp only [visVal]
            rw [bit_pack _ ⟨b, by dsimp [P0] at h1 ⊢; omega⟩]
            simp only [h1, ↓reduceIte]
          · have h2 : P0 + q ≤ b := by omega
            simp only [h1, h2, ↓reduceIte]
            dsimp only [visVal]
            rw [bit_pack _ ⟨b - q, by omega⟩]
            simp only [show ¬ (b - q < P0) by omega, ↓reduceIte]
            congr 1; omega
        have hcnt_eq : cntC (fun j => tr.getD j false) N = tr.count true := by
          have h1 := count_take_eq_cntC tr N (by omega)
          conv_lhs at h1 => rw [← htr_len, List.take_length]
          exact h1.symm
        have hcb_tr : ∀ j < N,
            let S := stZ (pubBit k (U k v)) (pz k x0Val) (4 + j)
            let a := H - 3 * (5 + (j : Int)) + (cntC (fun idx => tr.getD idx false) j : Int)
            xor (xor (S a) (S (a + 1))) (S (a + 2)) = tr.getD j false := by
          intro j hj
          have hcj := count_take_eq_cntC tr j (by omega)
          have := htr_spec j hj
          dsimp only [placeTr, onesTr] at this
          rwa [← hcj]
        let other : Int → Bool := fun z => if z < H then pz k x0Val z else false
        have hfront := (front_agree N (pubBit k (U k v)) H (fun j => tr.getD j false)
          (pz k x0Val) other hcb_tr (fun z hz => by simp [other, hz]) (r - 1)).2
        have hfv := front_val H N (fun j => tr.getD j false) (r - 1 + 1)
        rw [show r - 1 + 1 = r by omega, show min N (r - 4) = N by omega, hcnt_eq] at hfv
        have hmatch : ∀ a < q,
            let i : Int := ((k - q + a : Nat) : Int)
            xor (befZ (stZ (pubBit k (U k v)) other (r - 1)) i) (pubBit k (U k v) r i) =
              pz k x0Val ((P0 : Int) + (a : Int)) := by
          intro a ha
          dsimp only
          let i : Int := ((k - q + a : Nat) : Int)
          have hlt_front : i < front H N (fun j => tr.getD j false) (r - 1 + 1) := by
            rw [show r - 1 + 1 = r by omega, hfv]
            dsimp [i, H, P0, D] at hwt ⊢; omega
          change xor (befZ (stZ (pubBit k (U k v)) other (r - 1)) i) (pubBit k (U k v) r i) = _
          rw [← hfront i hlt_front]
          have hzero : stZ (pubBit k (U k v)) (pz k x0Val) r i = false := by
            rw [stZ_eq_rowWord hk2 hw (U_lt k v) r i]
            rw [pz_lt k _ (k - q + a) (by omega)]
            exact (lt_two_pow_iff_high (rowWord_lt (U_lt k v) w r)).mp hrow (k - q + a)
              (by dsimp [h]; omega) (by omega)
          rw [show r = (r - 1) + 1 by omega, stZ_succ] at hzero
          have hpos : i + 1 - 2 * ((r - 1 : Nat) : Int) = (P0 : Int) + (a : Int) := by
            dsimp [i, P0]; omega
          rw [hpos, show r - 1 + 1 = r by omega] at hzero
          cases hb1 : befZ (stZ (pubBit k (U k v)) (pz k x0Val) (r - 1)) i <;>
            cases hb2 : pz k x0Val ((P0 : Int) + (a : Int)) <;>
            cases hb3 : pubBit k (U k v) r i <;>
            simp [hb1, hb2, hb3] at hzero ⊢
        have hord_eq := ordFinal_eq_other hr5 hkr (by omega) vis x0 hvis hmatch q le_rfl
        have heq_x0 : ordX0 k r q vis v = x0Val := by
          apply Nat.eq_of_testBit_eq
          intro b
          by_cases hb : b < k
          · simp only [ordX0, bit_pack _ ⟨b, hb⟩]
            change (if P0 ≤ b ∧ b < P0 + q then ordFinal k r q (U k v) vis (b : Int)
              else visBit k r q vis b) = x0Val.testBit b
            by_cases hhid : P0 ≤ b ∧ b < P0 + q
            · simp only [hhid, and_self, ↓reduceIte]
              have h1 := hord_eq (b : Int) (by dsimp [P0]; omega)
              dsimp only at h1
              unfold ordFinal
              rw [h1]
              have hblt : (b : Int) < (k : Int) + ((k - q - 2 * r + 3 : Nat) : Int) := by omega
              simp only [hblt, ↓reduceIte, x0, pz_lt k x0Val b hb]
            · simp only [hhid, ↓reduceIte]
              exact hvis b hb (by omega)
          · rw [big_bit_false (ordX0_lt k r q vis v) (by omega), big_bit_false hx0lt (by omega)]
        have heq_w : ordW vis v = w := by
          dsimp only [ordW]
          rw [heq_x0]
          exact recover_key hk2 hw (U_lt k v)
        refine ⟨WordTest (ordW vis), List.mem_append_left _ ?_, ?_⟩
        · rw [List.mem_map]
          exact ⟨vis, List.mem_finRange vis, rfl⟩
        · simpa only [WordTest, heq_w] using hpass

end PEqualNP.Outside.L_meta_25586_aux

theorem PEqualNP.Outside.L_meta_25586 : ∀ (k r e q : Nat), 0 < q → 4 * r + 1 ≤ k → e + q + 4 ≤ r → k + e + 3 = 5 * r →
  let rot := fun (s word : Nat) =>
    ((word <<< (s % k)) ||| (word >>> (k - s % k))) % 2 ^ k
  let step := fun (word : Nat) =>
    (List.range k).foldl (fun acc i =>
      acc ||| ((xor (word.testBit i)
        (!(word.testBit ((i + 1) % k)) && word.testBit ((i + 2) % k))).toNat <<< i)) 0
  let constant := fun (j : Nat) => 3 ^ (k + j) % 2 ^ k
  let first := fun (rowKey rowName : Nat) =>
    (List.range r).foldl (fun rowState rowIndex =>
      step (rowState ^^^ rot 1 rowState ^^^ rot (k - 1) rowState) ^^^
        rot (2 * rowIndex) rowKey ^^^ constant (rowIndex + 1)) (rot 1 rowKey ^^^ rowName)
  let second := fun (colKey colName : Nat) =>
    (List.range r).foldl (fun colState colIndex =>
      step (colState ^^^ rot 2 colState ^^^ rot (k - 2) colState) ^^^
        rot (3 * (colIndex + 1) + 1) colKey ^^^ constant (r + (colIndex + 1)))
      (rot 3 colKey ^^^ colName)
  let h := (k + 1) / 2
  let graph : Fin (2 ^ k) → Fin (2 ^ k) → Bool := fun row col =>
    (List.range (2 ^ k)).any (fun w =>
      decide (first w row.val < 2 ^ (k - h)) && decide (second w col.val < 2 ^ (k - h)))
  let T := min r ((k + 5) / 5)
  let N := T - 4
  let D := e + q - 1
  let exceptions := 2 ^ (k - N) * (∑ j ∈ Finset.range (D + 1), Nat.choose N j)
  D < N →
  ∃ C : PEqualNP.CircuitLowerBounds.Circuit,
    PEqualNP.MetaComplexity.FanInTwo C ∧
    PEqualNP.MetaComplexity.NestedCover.ReadsBack (k + k) C ∧
    C.size ≤ 256 * (k + 1) * (r + 1) *
      (2 ^ (k - q) + exceptions) ∧
    ∀ bits : Fin (k + k) → Bool,
      C.eval (List.ofFn bits) = PEqualNP.Represents.adjFun (k := k) (l := k) graph bits := by
  intro k r e q hq hkr heqr hke
  dsimp only
  intro hDN
  obtain ⟨C, hfan, hread, hsize, heval⟩ :=
    PEqualNP.Outside.L_meta_25586_aux.main k r e q hq hkr heqr hke hDN
  refine ⟨C, hfan, hread, hsize, fun bits => ?_⟩
  rw [heval bits]
  unfold PEqualNP.Represents.adjFun
  dsimp only
  have hrow_mod : (PEqualNP.MetaComplexity.tableIndex fun i : Fin k => bits (Fin.castAdd k i)) % 2 ^ k =
      PEqualNP.Outside.L_meta_25586_aux.U k bits :=
    Nat.mod_eq_of_lt (PEqualNP.Outside.L_meta_25586_aux.U_lt k bits)
  have hcol_mod : (PEqualNP.MetaComplexity.tableIndex fun j : Fin k => bits (Fin.natAdd k j)) % 2 ^ k =
      PEqualNP.Outside.L_meta_25586_aux.V k bits :=
    Nat.mod_eq_of_lt (PEqualNP.Outside.L_meta_25586_aux.V_lt k bits)
  change _ = (List.range (2 ^ k)).any (fun w =>
    decide (PEqualNP.Outside.L_meta_25586_aux.rowWord k w
      ((PEqualNP.MetaComplexity.tableIndex fun i : Fin k => bits (Fin.castAdd k i)) % 2 ^ k) r <
      2 ^ (k - (k + 1) / 2)) &&
    decide (PEqualNP.Outside.L_meta_25586_aux.colWord k r w
      ((PEqualNP.MetaComplexity.tableIndex fun j : Fin k => bits (Fin.natAdd k j)) % 2 ^ k) r <
      2 ^ (k - (k + 1) / 2)))
  rw [hrow_mod, hcol_mod]
