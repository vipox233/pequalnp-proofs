import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_906

-- ============================================================
-- PART 1: Circuit Builder (Bank + Grow + Generic Combinators)
-- ============================================================

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

lemma xor_lt {k a b : Nat} (ha : a < 2 ^ k) (hb : b < 2 ^ k) : a ^^^ b < 2 ^ k := by
  apply Nat.lt_pow_two_of_testBit
  intro j hj
  have hpow := Nat.pow_le_pow_right Nat.zero_lt_two hj
  simp [Nat.testBit_xor, Nat.testBit_lt_two_pow (ha.trans_le hpow),
    Nat.testBit_lt_two_pow (hb.trans_le hpow)]


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


-- ============================================================
-- PART 3: ANF, Fast Mobius Transform (FMT), Global ANF & V_s
-- ============================================================

local instance : Std.Commutative (α := Bool) xor := ⟨Bool.xor_comm⟩
local instance : Std.Associative (α := Bool) xor := ⟨Bool.xor_assoc⟩

def bxorFinset {α : Type} (s : Finset α) (f : α → Bool) : Bool :=
  s.fold xor false f

lemma bxorFinset_empty {α : Type} (f : α → Bool) : bxorFinset (∅ : Finset α) f = false := by
  simp [bxorFinset]

lemma bxorFinset_insert {α : Type} [DecidableEq α] {s : Finset α} {a : α} (ha : a ∉ s)
    (f : α → Bool) : bxorFinset (insert a s) f = xor (f a) (bxorFinset s f) := by
  simp [bxorFinset, Finset.fold_insert ha]

lemma bxorFinset_xor {α : Type} [DecidableEq α] (s : Finset α) (f g : α → Bool) :
    bxorFinset s (fun a => xor (f a) (g a)) = xor (bxorFinset s f) (bxorFinset s g) := by
  induction s using Finset.induction with
  | empty => simp [bxorFinset]
  | insert a s ha ih =>
    rw [bxorFinset_insert ha, bxorFinset_insert ha, bxorFinset_insert ha, ih]
    cases f a <;> cases g a <;> cases bxorFinset s f <;> cases bxorFinset s g <;> rfl

lemma bxorFinset_congr {α : Type} {s : Finset α} {f g : α → Bool}
    (h : ∀ a ∈ s, f a = g a) : bxorFinset s f = bxorFinset s g := by
  unfold bxorFinset
  exact Finset.fold_congr h

lemma bxorFinset_zero {α : Type} [DecidableEq α] {s : Finset α} {f : α → Bool}
    (h : ∀ a ∈ s, f a = false) : bxorFinset s f = false := by
  induction s using Finset.induction with
  | empty => simp [bxorFinset]
  | insert a s ha ih =>
    rw [bxorFinset_insert ha, h a (Finset.mem_insert_self _ _),
        ih (fun b hb => h b (Finset.mem_insert_of_mem hb))]
    rfl

lemma bxorFinset_filter_eq {α : Type} [DecidableEq α] (s : Finset α) (p : α → Bool) (f : α → Bool) :
    bxorFinset (s.filter (fun a => p a = true)) f = bxorFinset s (fun a => p a && f a) := by
  induction s using Finset.induction with
  | empty => simp [bxorFinset]
  | insert a s ha ih =>
    by_cases hp : p a = true
    · rw [Finset.filter_insert, if_pos hp, bxorFinset_insert (by simp [ha]),
          bxorFinset_insert ha, hp, Bool.true_and, ih]
    · have hpf : p a = false := Bool.eq_false_iff.mpr hp
      rw [Finset.filter_insert, if_neg hp, bxorFinset_insert ha, hpf, Bool.false_and,
          Bool.false_xor, ih]

lemma bxorFinset_union_disjoint {α : Type} [DecidableEq α] {s t : Finset α}
    (h : Disjoint s t) (f : α → Bool) :
    bxorFinset (s ∪ t) f = xor (bxorFinset s f) (bxorFinset t f) := by
  induction s using Finset.induction with
  | empty => simp [bxorFinset]
  | insert a s ha ih =>
    have hdisj : Disjoint s t := Disjoint.mono_left (Finset.subset_insert a s) h
    have hat : a ∉ t := Finset.disjoint_left.mp h (Finset.mem_insert_self a s)
    rw [Finset.insert_union, bxorFinset_insert (by simp [ha, hat]),
        bxorFinset_insert ha, ih hdisj]
    cases f a <;> cases bxorFinset s f <;> cases bxorFinset t f <;> rfl

lemma bxorFinset_comm {α β : Type} [DecidableEq α] [DecidableEq β]
    (s : Finset α) (t : Finset β) (f : α → β → Bool) :
    bxorFinset s (fun a => bxorFinset t (fun b => f a b)) =
    bxorFinset t (fun b => bxorFinset s (fun a => f a b)) := by
  induction s using Finset.induction with
  | empty =>
    rw [bxorFinset_empty]
    symm
    exact bxorFinset_zero (fun _ _ => bxorFinset_empty _)
  | insert a s ha ih =>
    rw [bxorFinset_insert ha, ih, ← bxorFinset_xor]
    apply bxorFinset_congr
    intro b _
    rw [bxorFinset_insert ha]

lemma bxorFinset_bij {α β : Type} [DecidableEq α] [DecidableEq β]
    (s : Finset α) (t : Finset β) (f : α → Bool) (g : β → Bool)
    (i : (a : α) → a ∈ s → β)
    (hi : ∀ a ha, i a ha ∈ t)
    (inj : ∀ a1 ha1 a2 ha2, i a1 ha1 = i a2 ha2 → a1 = a2)
    (surj : ∀ b ∈ t, ∃ a ha, i a ha = b)
    (hfg : ∀ a ha, f a = g (i a ha)) :
    bxorFinset s f = bxorFinset t g := by
  induction s using Finset.induction generalizing t with
  | empty =>
    have ht : t = ∅ := by
      ext b; simp only [Finset.notMem_empty, iff_false]
      intro hb; obtain ⟨a, ha, _⟩ := surj b hb; exact Finset.notMem_empty a ha
    subst ht; rfl
  | insert a s has ih =>
    have hia : i a (Finset.mem_insert_self a s) ∈ t := hi a _
    have ht : t = insert (i a (Finset.mem_insert_self a s)) (t.erase (i a (Finset.mem_insert_self a s))) :=
      (Finset.insert_erase hia).symm
    rw [bxorFinset_insert has, ht, bxorFinset_insert (Finset.notMem_erase _ _), hfg a (Finset.mem_insert_self a s)]
    congr 1
    apply ih (t.erase (i a (Finset.mem_insert_self a s)))
      (fun x hx => i x (Finset.mem_insert_of_mem hx))
    · intro x hx
      refine Finset.mem_erase.mpr ⟨?_, hi x _⟩
      intro heq
      exact has ((inj x _ a _ heq) ▸ hx)
    · intro x1 hx1 x2 hx2 heq
      exact inj x1 _ x2 _ heq
    · intro b hb
      obtain ⟨hbne, hbt⟩ := Finset.mem_erase.mp hb
      obtain ⟨x, hx, rfl⟩ := surj b hbt
      rcases Finset.mem_insert.mp hx with rfl | hxs
      · exact absurd rfl hbne
      · exact ⟨x, hxs, rfl⟩
    · intro x hx
      exact hfg x _

lemma bxorFinset_list_foldl {α : Type} [DecidableEq α] (l : List α) (hnd : l.Nodup)
    (f : α → Bool) :
    l.foldl (fun acc a => xor acc (f a)) false = bxorFinset l.toFinset f := by
  have hgen : ∀ acc : Bool,
      l.foldl (fun c a => xor c (f a)) acc = xor acc (bxorFinset l.toFinset f) := by
    induction l with
    | nil => intro acc; simp [bxorFinset]
    | cons a l ih =>
      intro acc
      rcases List.nodup_cons.mp hnd with ⟨hal, hnd'⟩
      simp only [List.foldl_cons, List.toFinset_cons]
      rw [ih hnd', bxorFinset_insert (by simp [hal])]
      cases acc <;> cases f a <;> cases bxorFinset l.toFinset f <;> rfl
  simpa using hgen false

lemma bxorFinset_finRange {n : Nat} (f : Fin n → Bool) :
    (List.finRange n).foldl (fun acc i => xor acc (f i)) false =
    bxorFinset (Finset.univ : Finset (Fin n)) f := by
  rw [bxorFinset_list_foldl _ (List.nodup_finRange n)]
  congr 1
  ext i; simp

-- Bitmask submask predicate
def submask (x y : Nat) : Bool := decide (x &&& y = x)

lemma submask_iff {x y : Nat} : submask x y = true ↔ ∀ i, x.testBit i = true → y.testBit i = true := by
  unfold submask
  simp only [decide_eq_true_eq]
  constructor
  · intro h i hi
    have hb := congrArg (fun n => n.testBit i) h
    rw [Nat.testBit_and, hi] at hb
    simpa using hb
  · intro h
    apply Nat.eq_of_testBit_eq
    intro i
    rw [Nat.testBit_and]
    cases hx : x.testBit i
    · simp
    · simp [h i hx]

-- Fast Mobius Transform (FMT)
def fmtLayer {b : Nat} (t : Nat) (ht : t < b) (T : Fin (2 ^ b) → Bool) (S : Fin (2 ^ b)) : Bool :=
  if S.val.testBit t then
    xor (T S) (T ⟨S.val ^^^ (1 <<< t), xor_lt S.isLt
      (by rw [Nat.shiftLeft_eq, Nat.one_mul]; exact Nat.pow_lt_pow_right (by omega) ht)⟩)
  else T S

def fmtPrefix {b : Nat} (T : Fin (2 ^ b) → Bool) (r : Nat) : Fin (2 ^ b) → Bool :=
  ((List.finRange b).take r).foldl (fun cur t => fmtLayer t.val t.isLt cur) T

def fmt {b : Nat} (T : Fin (2 ^ b) → Bool) : Fin (2 ^ b) → Bool :=
  (List.finRange b).foldl (fun cur t => fmtLayer t.val t.isLt cur) T

lemma fmtLayer_invol {b t : Nat} (ht : t < b) (T : Fin (2 ^ b) → Bool) :
    fmtLayer t ht (fmtLayer t ht T) = T := by
  funext S
  unfold fmtLayer
  by_cases h : S.val.testBit t = true
  · have hflip : (S.val ^^^ (1 <<< t)).testBit t = false := by
      simp [Nat.testBit_xor, Nat.shiftLeft_eq, Nat.testBit_two_pow, h]
    have hback : (S.val ^^^ (1 <<< t)) ^^^ (1 <<< t) = S.val := by
      rw [Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]
    simp only [h, hflip, Bool.false_eq_true, ↓reduceIte]
    cases T S <;> cases T ⟨S.val ^^^ (1 <<< t), _⟩ <;> rfl
  · simp [h]

lemma fmtLayer_xor {b t : Nat} (ht : t < b) (T1 T2 : Fin (2 ^ b) → Bool) :
    fmtLayer t ht (fun S => xor (T1 S) (T2 S)) =
    fun S => xor (fmtLayer t ht T1 S) (fmtLayer t ht T2 S) := by
  funext S
  unfold fmtLayer
  by_cases h : S.val.testBit t = true
  · simp only [h, ↓reduceIte]
    cases T1 S <;> cases T2 S <;> cases T1 ⟨S.val ^^^ (1 <<< t), _⟩ <;>
      cases T2 ⟨S.val ^^^ (1 <<< t), _⟩ <;> rfl
  · simp [h]

lemma fmt_xor {b : Nat} (T1 T2 : Fin (2 ^ b) → Bool) :
    fmt (fun S => xor (T1 S) (T2 S)) = fun S => xor (fmt T1 S) (fmt T2 S) := by
  unfold fmt
  have hgen : ∀ (l : List (Fin b)) (A B : Fin (2 ^ b) → Bool),
      l.foldl (fun cur t => fmtLayer t.val t.isLt cur) (fun S => xor (A S) (B S)) =
      fun S => xor (l.foldl (fun cur t => fmtLayer t.val t.isLt cur) A S)
                   (l.foldl (fun cur t => fmtLayer t.val t.isLt cur) B S) := by
    intro l
    induction l with
    | nil => intros; rfl
    | cons t l ih =>
      intro A B
      simp only [List.foldl_cons]
      rw [fmtLayer_xor, ih]
  exact hgen _ _ _

lemma fmt_bxorFinset {α : Type} [DecidableEq α] {b : Nat} (s : Finset α)
    (f : α → Fin (2 ^ b) → Bool) :
    fmt (fun x => bxorFinset s (fun a => f a x)) =
    fun S => bxorFinset s (fun a => fmt (f a) S) := by
  induction s using Finset.induction with
  | empty =>
    funext S
    have h0 : fmt (fun _ : Fin (2 ^ b) => false) = fun _ => false := by
      unfold fmt
      have hgen : ∀ (l : List (Fin b)),
          l.foldl (fun cur t => fmtLayer t.val t.isLt cur) (fun _ => false) = fun _ => false := by
        intro l; induction l with
        | nil => rfl
        | cons t l ih =>
          simp only [List.foldl_cons]
          have : fmtLayer t.val t.isLt (fun _ => false) = fun _ => false := by
            funext x; unfold fmtLayer; split_ifs <;> rfl
          rw [this, ih]
      exact hgen _
    simpa [bxorFinset] using congrFun h0 S
  | insert a s ha ih =>
    have h1 : (fun x => bxorFinset (insert a s) (fun c => f c x)) =
        fun x => xor (f a x) (bxorFinset s (fun c => f c x)) := by
      funext x; exact bxorFinset_insert ha _
    rw [h1, fmt_xor, ih]
    funext S; symm; exact bxorFinset_insert ha _

lemma fmtPrefix_eq {b : Nat} (T : Fin (2 ^ b) → Bool) (r : Nat) (hr : r ≤ b)
    (S : Fin (2 ^ b)) :
    fmtPrefix T r S =
      bxorFinset (Finset.univ.filter (fun x : Fin (2 ^ b) =>
        (∀ i : Fin b, i.val < r → x.val.testBit i.val = true → S.val.testBit i.val = true) ∧
        (∀ i : Fin b, r ≤ i.val → x.val.testBit i.val = S.val.testBit i.val))) T := by
  induction r generalizing S with
  | zero =>
    have huniq : Finset.univ.filter (fun x : Fin (2 ^ b) =>
        (∀ i : Fin b, i.val < 0 → x.val.testBit i.val = true → S.val.testBit i.val = true) ∧
        (∀ i : Fin b, 0 ≤ i.val → x.val.testBit i.val = S.val.testBit i.val)) = {S} := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      constructor
      · intro ⟨_, h2⟩
        apply Fin.ext
        apply Nat.eq_of_testBit_eq
        intro i
        by_cases hi : i < b
        · exact h2 ⟨i, hi⟩ (Nat.zero_le _)
        · rw [Nat.testBit_lt_two_pow (x.isLt.trans_le (Nat.pow_le_pow_right Nat.zero_lt_two (by omega))),
              Nat.testBit_lt_two_pow (S.isLt.trans_le (Nat.pow_le_pow_right Nat.zero_lt_two (by omega)))]
      · rintro rfl; exact ⟨fun _ h => by omega, fun _ _ => rfl⟩
    rw [huniq]
    simp [fmtPrefix, bxorFinset]
  | succ r ih =>
    have hr' : r < b := by omega
    have htake : (List.finRange b).take (r + 1) = (List.finRange b).take r ++ [⟨r, hr'⟩] := by
      rw [List.take_add_one, List.getElem?_eq_getElem (by simp [hr'])]
      simp [List.getElem_finRange]
    have hstep : fmtPrefix T (r + 1) S = fmtLayer r hr' (fmtPrefix T r) S := by
      unfold fmtPrefix; rw [htake, List.foldl_append]; simp
    rw [hstep]
    unfold fmtLayer
    by_cases hSr : S.val.testBit r = true
    · simp only [hSr, ↓reduceIte]
      set S' : Fin (2 ^ b) := ⟨S.val ^^^ (1 <<< r), xor_lt S.isLt
        (by rw [Nat.shiftLeft_eq, Nat.one_mul]; exact Nat.pow_lt_pow_right (by omega) hr')⟩
      rw [ih (by omega) S, ih (by omega) S', ← bxorFinset_union_disjoint]
      · congr 1
        ext x
        simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
        have hS'r : S'.val.testBit r = false := by
          simp [S', Nat.testBit_xor, Nat.shiftLeft_eq, hSr]
        have hS'ne : ∀ i, i ≠ r → S'.val.testBit i = S.val.testBit i := by
          intro i hne
          simp [S', Nat.testBit_xor, Nat.shiftLeft_eq, Ne.symm hne]
        constructor
        · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
          · refine ⟨fun i hi hxi => ?_, fun i hi => h2 i (by omega)⟩
            by_cases hir : i.val = r
            · rw [hir]; exact hSr
            · exact h1 i (by omega) hxi
          · refine ⟨fun i hi hxi => ?_, fun i hi => ?_⟩
            · by_cases hir : i.val = r
              · rw [hir]; exact hSr
              · rw [← hS'ne i.val hir]; exact h1 i (by omega) hxi
            · rw [h2 i (by omega), hS'ne i.val (by omega)]
        · rintro ⟨h1, h2⟩
          cases hxr : x.val.testBit r
          · right
            refine ⟨fun i hi hxi => ?_, fun i hi => ?_⟩
            · rw [hS'ne i.val (by omega)]; exact h1 i (by omega) hxi
            · by_cases hir : i.val = r
              · rw [hir, hxr, hS'r]
              · rw [h2 i (by omega), hS'ne i.val hir]
          · left
            refine ⟨fun i hi hxi => h1 i (by omega) hxi, fun i hi => ?_⟩
            by_cases hir : i.val = r
            · rw [hir, hxr, hSr]
            · exact h2 i (by omega)
      · rw [Finset.disjoint_left]
        intro x hx1 hx2
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx1 hx2
        have h1 := hx1.2 ⟨r, hr'⟩ (le_refl r)
        have h2 := hx2.2 ⟨r, hr'⟩ (le_refl r)
        have hS'r : S'.val.testBit r = false := by
          simp [S', Nat.testBit_xor, Nat.shiftLeft_eq, hSr]
        rw [hSr] at h1; rw [hS'r] at h2; rw [h1] at h2; cases h2
    · rw [if_neg hSr]
      rw [ih (by omega) S]
      congr 1
      ext x
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      have hSrf : S.val.testBit r = false := Bool.eq_false_iff.mpr hSr
      constructor
      · rintro ⟨h1, h2⟩
        refine ⟨fun i hi hxi => ?_, fun i hi => h2 i (by omega)⟩
        by_cases hir : i.val = r
        · have := h2 ⟨r, hr'⟩ (le_refl r); rw [hir] at hxi; rw [hxi, hSrf] at this; cases this
        · exact h1 i (by omega) hxi
      · rintro ⟨h1, h2⟩
        refine ⟨fun i hi hxi => h1 i (by omega) hxi, fun i hi => ?_⟩
        by_cases hir : i.val = r
        · rw [hir]
          cases hxr : x.val.testBit r
          · rw [hSrf]
          · exact (h1 ⟨r, hr'⟩ (Nat.lt_succ_self r) hxr).symm
        · exact h2 i (by omega)

lemma fmt_eq_submaskSum {b : Nat} (T : Fin (2 ^ b) → Bool) (S : Fin (2 ^ b)) :
    fmt T S = bxorFinset (Finset.univ.filter (fun x : Fin (2 ^ b) => submask x.val S.val = true)) T := by
  have h1 : fmt T S = fmtPrefix T b S := by simp [fmt, fmtPrefix, List.take_of_length_le]
  rw [h1, fmtPrefix_eq T b (le_refl b) S]
  congr 1
  ext x
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, submask_iff]
  constructor
  · rintro ⟨h1, _⟩ i hxi
    by_cases hi : i < b
    · exact h1 ⟨i, hi⟩ hi hxi
    · have : x.val.testBit i = false :=
        Nat.testBit_lt_two_pow (x.isLt.trans_le (Nat.pow_le_pow_right Nat.zero_lt_two (by omega)))
      rw [this] at hxi; cases hxi
  · intro h
    exact ⟨fun i _ hxi => h i.val hxi, fun i hi => by omega⟩

lemma fmtLayer_comm {b t1 t2 : Nat} (h1 : t1 < b) (h2 : t2 < b) (T : Fin (2 ^ b) → Bool) :
    fmtLayer t1 h1 (fmtLayer t2 h2 T) = fmtLayer t2 h2 (fmtLayer t1 h1 T) := by
  by_cases heq : t1 = t2
  · subst heq; rfl
  · funext S
    unfold fmtLayer
    have hflip1 : (S.val ^^^ (1 <<< t1)).testBit t2 = S.val.testBit t2 := by
      simp [Nat.testBit_xor, Nat.shiftLeft_eq, Nat.testBit_two_pow, heq]
    have hflip2 : (S.val ^^^ (1 <<< t2)).testBit t1 = S.val.testBit t1 := by
      simp [Nat.testBit_xor, Nat.shiftLeft_eq, Nat.testBit_two_pow, Ne.symm heq]
    have hxor_comm : (S.val ^^^ (1 <<< t1)) ^^^ (1 <<< t2) = (S.val ^^^ (1 <<< t2)) ^^^ (1 <<< t1) := by
      rw [Nat.xor_assoc, Nat.xor_comm (1 <<< t1), ← Nat.xor_assoc]
    cases hb1 : S.val.testBit t1 <;> cases hb2 : S.val.testBit t2 <;>
      simp only [hflip1, hflip2, hb1, hb2, Bool.false_eq_true, ↓reduceIte]
    have heqF : (⟨(S.val ^^^ (1 <<< t1)) ^^^ (1 <<< t2), xor_lt (xor_lt S.isLt
        (by rw [Nat.shiftLeft_eq, Nat.one_mul]; exact Nat.pow_lt_pow_right (by omega) h1))
        (by rw [Nat.shiftLeft_eq, Nat.one_mul]; exact Nat.pow_lt_pow_right (by omega) h2)⟩ : Fin (2 ^ b)) =
      ⟨(S.val ^^^ (1 <<< t2)) ^^^ (1 <<< t1), xor_lt (xor_lt S.isLt
        (by rw [Nat.shiftLeft_eq, Nat.one_mul]; exact Nat.pow_lt_pow_right (by omega) h2))
        (by rw [Nat.shiftLeft_eq, Nat.one_mul]; exact Nat.pow_lt_pow_right (by omega) h1)⟩ :=
      Fin.ext hxor_comm
    rw [heqF]
    generalize T S = a
    generalize T ⟨S.val ^^^ (1 <<< t2), _⟩ = c
    generalize T ⟨S.val ^^^ (1 <<< t1), _⟩ = d
    generalize T ⟨(S.val ^^^ (1 <<< t2)) ^^^ (1 <<< t1), _⟩ = e
    cases a <;> cases c <;> cases d <;> cases e <;> rfl

lemma fmt_invol {b : Nat} (T : Fin (2 ^ b) → Bool) : fmt (fmt T) = T := by
  unfold fmt
  have hgen : ∀ (l : List (Fin b)) (X : Fin (2 ^ b) → Bool),
      l.foldl (fun cur t => fmtLayer t.val t.isLt cur)
        (l.foldl (fun cur t => fmtLayer t.val t.isLt cur) X) = X := by
    intro l
    induction l with
    | nil => intro X; rfl
    | cons t l ih =>
      intro X
      simp only [List.foldl_cons]
      have hcomm : ∀ (l' : List (Fin b)) (Y : Fin (2 ^ b) → Bool),
          fmtLayer t.val t.isLt (l'.foldl (fun cur u => fmtLayer u.val u.isLt cur) Y) =
          l'.foldl (fun cur u => fmtLayer u.val u.isLt cur) (fmtLayer t.val t.isLt Y) := by
        intro l'
        induction l' with
        | nil => intro Y; rfl
        | cons u l' ih' =>
          intro Y
          simp only [List.foldl_cons]
          rw [ih', fmtLayer_comm]
      rw [hcomm, fmtLayer_invol, ih]
  exact hgen _ _

lemma anf_unique {b : Nat} {c1 c2 : Fin (2 ^ b) → Bool}
    (h : fmt c1 = fmt c2) : c1 = c2 := by
  have := congrArg fmt h
  rwa [fmt_invol, fmt_invol] at this

-- Global ANF of a single local window function

def popcount (k x : Nat) : Nat :=
  ((List.range k).filter (fun i => x.testBit i)).length

lemma popcount_eq_card {k : Nat} (x : Nat) :
    popcount k x = (Finset.univ.filter (fun i : Fin k => x.testBit i.val = true)).card := by
  unfold popcount
  have h1 : ((List.range k).filter (fun i => x.testBit i)).length =
      ((List.finRange k).filter (fun i : Fin k => x.testBit i.val)).length := by
    have hmap : (List.range k) = (List.finRange k).map Fin.val := by
      apply List.ext_getElem <;> simp
    rw [hmap, List.filter_map, List.length_map]
    rfl
  rw [h1, ← List.toFinset_card_of_nodup ((List.nodup_finRange k).filter _)]
  congr 1
  ext i; simp

lemma popcount_le {k x : Nat} : popcount k x ≤ k := by
  unfold popcount
  exact (List.length_filter_le _ _).trans (by simp)

lemma popcount_submask_le {k x y : Nat} (h : submask x y = true) :
    popcount k x ≤ popcount k y := by
  rw [popcount_eq_card, popcount_eq_card]
  apply Finset.card_le_card
  intro i hi
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
  exact submask_iff.mp h i.val hi

lemma popcount_submask_eq_imp {k : Nat} {x y : Fin (2 ^ k)}
    (hsub : submask x.val y.val = true) (hpop : popcount k x.val = popcount k y.val) :
    x = y := by
  rw [popcount_eq_card, popcount_eq_card] at hpop
  have hss : Finset.univ.filter (fun i : Fin k => x.val.testBit i.val = true) ⊆
      Finset.univ.filter (fun i : Fin k => y.val.testBit i.val = true) := by
    intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    exact submask_iff.mp hsub i.val hi
  have heq := Finset.eq_of_subset_of_card_le hss (le_of_eq hpop.symm)
  apply Fin.ext
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < k
  · have hmem : (⟨i, hi⟩ : Fin k) ∈ Finset.univ.filter (fun j : Fin k => x.val.testBit j.val = true) ↔
        (⟨i, hi⟩ : Fin k) ∈ Finset.univ.filter (fun j : Fin k => y.val.testBit j.val = true) := by
      rw [heq]
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hmem
    cases hx : x.val.testBit i <;> cases hy : y.val.testBit i <;> simp_all
  · rw [Nat.testBit_lt_two_pow (x.isLt.trans_le (Nat.pow_le_pow_right Nat.zero_lt_two (by omega))),
        Nat.testBit_lt_two_pow (y.isLt.trans_le (Nat.pow_le_pow_right Nat.zero_lt_two (by omega)))]

lemma popcount_zero_iff {k : Nat} {x : Fin (2 ^ k)} : popcount k x.val = 0 ↔ x.val = 0 := by
  rw [popcount_eq_card, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  constructor
  · intro h
    apply Nat.eq_of_testBit_eq
    intro i
    simp only [Nat.zero_testBit]
    by_cases hi : i < k
    · exact Bool.eq_false_iff.mpr (h (Finset.mem_univ ⟨i, hi⟩))
    · exact Nat.testBit_lt_two_pow (x.isLt.trans_le (Nat.pow_le_pow_right Nat.zero_lt_two (by omega)))
  · intro hx i _
    simp [hx]


-- Helper: bxorFinset of constant true over a set of size 2^m is (m == 0)
lemma bxorFinset_const_true {α : Type} [DecidableEq α] (s : Finset α) :
    bxorFinset s (fun _ => true) = decide (s.card % 2 = 1) := by
  induction s using Finset.induction with
  | empty => simp [bxorFinset]
  | insert a s ha ih =>
    rw [bxorFinset_insert ha, ih, Finset.card_insert_of_notMem ha]
    have hmod : s.card % 2 = 0 ∨ s.card % 2 = 1 := Nat.mod_two_eq_zero_or_one s.card
    rcases hmod with h | h <;> simp [Nat.add_mod, h]

-- Key shift lemma for FMT: fmt (g(· ⊕ d)) T = ⨁_{S ⊇ T, (S ^^^ T) ⊆ d} fmt g S
lemma fmt_shift {k : Nat} (g : Fin (2 ^ k) → Bool) (d : Fin (2 ^ k)) (T : Fin (2 ^ k)) :
    fmt (fun w : Fin (2 ^ k) => g ⟨w.val ^^^ d.val, xor_lt w.isLt d.isLt⟩) T =
      bxorFinset (Finset.univ.filter (fun S : Fin (2 ^ k) =>
        submask T.val S.val = true ∧ submask (S.val ^^^ T.val) d.val = true)) (fmt g) := by
  let c' : Fin (2 ^ k) → Bool := fun U =>
    bxorFinset (Finset.univ.filter (fun S : Fin (2 ^ k) =>
      submask U.val S.val = true ∧ submask (S.val ^^^ U.val) d.val = true)) (fmt g)
  suffices h : fmt c' = fun w : Fin (2 ^ k) => g ⟨w.val ^^^ d.val, xor_lt w.isLt d.isLt⟩ by
    have := congrArg fmt h
    rw [fmt_invol] at this
    exact (congrFun this T).symm
  funext w
  rw [fmt_eq_submaskSum]
  have hg : g ⟨w.val ^^^ d.val, xor_lt w.isLt d.isLt⟩ =
      fmt (fmt g) ⟨w.val ^^^ d.val, xor_lt w.isLt d.isLt⟩ := by rw [fmt_invol]
  rw [hg, fmt_eq_submaskSum]
  -- Expand c' and swap the double bxorFinset
  have hswap :
      bxorFinset (Finset.univ.filter (fun U : Fin (2 ^ k) => submask U.val w.val = true)) c' =
      bxorFinset Finset.univ (fun S : Fin (2 ^ k) =>
        bxorFinset (Finset.univ.filter (fun U : Fin (2 ^ k) =>
          submask U.val w.val = true ∧ submask U.val S.val = true ∧
          submask (S.val ^^^ U.val) d.val = true)) (fun _ => fmt g S)) := by
    have h1 : ∀ U : Fin (2 ^ k), c' U =
        bxorFinset Finset.univ (fun S : Fin (2 ^ k) =>
          (submask U.val S.val && submask (S.val ^^^ U.val) d.val) && fmt g S) := by
      intro U
      unfold c'
      rw [← bxorFinset_filter_eq]
      congr 1
    have h2 : bxorFinset (Finset.univ.filter (fun U : Fin (2 ^ k) => submask U.val w.val = true)) c' =
        bxorFinset Finset.univ (fun U : Fin (2 ^ k) =>
          bxorFinset Finset.univ (fun S : Fin (2 ^ k) =>
            (submask U.val w.val && (submask U.val S.val && submask (S.val ^^^ U.val) d.val)) && fmt g S)) := by
      rw [bxorFinset_filter_eq]
      apply bxorFinset_congr
      intro U _
      rw [h1 U]
      cases hUw : submask U.val w.val
      · simp only [Bool.false_and]
        symm; exact bxorFinset_zero (fun _ _ => rfl)
      · simp only [Bool.true_and]
    rw [h2, bxorFinset_comm]
    apply bxorFinset_congr
    intro S _
    rw [← bxorFinset_filter_eq]
    congr 1
  rw [hswap]
  rw [bxorFinset_filter_eq]
  apply bxorFinset_congr
  intro S _
  -- Compute parity of the inner set { U | U ⊆ w ∧ U ⊆ S ∧ (S ^^^ U) ⊆ d }
  set inner := Finset.univ.filter (fun U : Fin (2 ^ k) =>
    submask U.val w.val = true ∧ submask U.val S.val = true ∧
    submask (S.val ^^^ U.val) d.val = true)
  cases hfg : fmt g S
  · simp only [Bool.and_false]
    exact bxorFinset_zero (fun _ _ => rfl)
  · simp only [Bool.and_true]
    rw [bxorFinset_const_true]
    -- Count |inner|: if S ⊆ w ||| d, each bit i ∈ S with w_i = d_i = 1 has 2 choices, else 1 choice!
    -- So |inner| = 1 iff submask S (w ^^^ d), else even (0 or ≥ 2 power of 2)!
    by_cases hSwd : submask S.val (w.val ^^^ d.val) = true
    · -- Unique element U = S &&& w!
      have huniq : inner = {⟨S.val &&& w.val, Nat.and_lt_two_pow _ w.isLt⟩} := by
        ext U
        simp only [inner, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
        constructor
        · rintro ⟨hUw, hUS, hSUd⟩
          apply Fin.ext
          apply Nat.eq_of_testBit_eq
          intro i
          rw [Nat.testBit_and]
          have h1 := submask_iff.mp hUw i
          have h2 := submask_iff.mp hUS i
          have h3 := submask_iff.mp hSUd i
          have h4 := submask_iff.mp hSwd i
          rw [Nat.testBit_xor] at h3 h4
          cases hSi : S.val.testBit i <;> cases hwi : w.val.testBit i <;>
            cases hdi : d.val.testBit i <;> cases hUi : U.val.testBit i <;>
            simp_all
        · rintro rfl
          refine ⟨submask_iff.mpr (fun i hi => ?_), submask_iff.mpr (fun i hi => ?_),
                  submask_iff.mpr (fun i hi => ?_)⟩
          · rw [Nat.testBit_and] at hi; exact (Bool.and_eq_true _ _).mp hi |>.2
          · rw [Nat.testBit_and] at hi; exact (Bool.and_eq_true _ _).mp hi |>.1
          · rw [Nat.testBit_xor, Nat.testBit_and] at hi
            have h4 := submask_iff.mp hSwd i
            rw [Nat.testBit_xor] at h4
            cases hSi : S.val.testBit i <;> cases hwi : w.val.testBit i <;>
              cases hdi : d.val.testBit i <;> simp_all
      rw [huniq, hSwd]; simp
    · simp only [Bool.eq_false_iff.mpr hSwd, decide_eq_false_iff_not]
      -- Find a witness bit i where S_i = 1 and w_i = d_i
      have hex : ∃ i, S.val.testBit i = true ∧ w.val.testBit i = d.val.testBit i := by
        by_contra hall
        push_neg at hall
        apply hSwd
        rw [submask_iff]
        intro i hSi
        rw [Nat.testBit_xor]
        have hne := hall i hSi
        cases hwi : w.val.testBit i <;> cases hdi : d.val.testBit i <;> simp_all
      obtain ⟨i, hSi, hwdi⟩ := hex
      have hi_lt : i < k := by
        by_contra hge
        have : S.val.testBit i = false :=
          Nat.testBit_lt_two_pow (S.isLt.trans_le (Nat.pow_le_pow_right Nat.zero_lt_two (by omega)))
        rw [this] at hSi; cases hSi
      cases hwi : w.val.testBit i
      · -- w_i = false, d_i = false, S_i = true => inner is empty!
        have hdi : d.val.testBit i = false := by rw [← hwdi, hwi]
        have hemp : inner = ∅ := by
          rw [Finset.eq_empty_iff_forall_notMem]
          intro U hU
          simp only [inner, Finset.mem_filter, Finset.mem_univ, true_and] at hU
          have h1 := submask_iff.mp hU.1 i
          have h3 := submask_iff.mp hU.2.2 i
          rw [Nat.testBit_xor] at h3
          cases hUi : U.val.testBit i <;> simp_all
        rw [hemp]; simp
      · -- w_i = true, d_i = true, S_i = true => flipping bit i is a fixed-point-free involution on inner!
        have hdi : d.val.testBit i = true := by rw [← hwdi, hwi]
        let flip : Fin (2 ^ k) → Fin (2 ^ k) := fun U =>
          ⟨U.val ^^^ (1 <<< i), xor_lt U.isLt
            (by rw [Nat.shiftLeft_eq, Nat.one_mul]; exact Nat.pow_lt_pow_right (by omega) hi_lt)⟩
        have hflip_mem : ∀ U ∈ inner, flip U ∈ inner := by
          intro U hU
          simp only [inner, Finset.mem_filter, Finset.mem_univ, true_and] at hU ⊢
          refine ⟨submask_iff.mpr ?_, submask_iff.mpr ?_, submask_iff.mpr ?_⟩
          · intro j hj
            by_cases hji : j = i
            · subst hji; exact hwi
            · simp [flip, Nat.testBit_xor, Nat.shiftLeft_eq, Ne.symm hji] at hj
              exact submask_iff.mp hU.1 j hj
          · intro j hj
            by_cases hji : j = i
            · subst hji; exact hSi
            · simp [flip, Nat.testBit_xor, Nat.shiftLeft_eq, Ne.symm hji] at hj
              exact submask_iff.mp hU.2.1 j hj
          · intro j hj
            by_cases hji : j = i
            · subst hji; exact hdi
            · simp [flip, Nat.testBit_xor, Nat.shiftLeft_eq, Ne.symm hji] at hj
              have := submask_iff.mp hU.2.2 j
              rw [Nat.testBit_xor] at this
              exact this (by cases hSj : S.val.testBit j <;> cases hUj : U.val.testBit j <;> simp_all)
        -- Split inner into bit-i-false and bit-i-true halves, which have equal cardinality!
        let lo := inner.filter (fun U => U.val.testBit i = false)
        let hi := inner.filter (fun U => U.val.testBit i = true)
        have hpart : inner.card = lo.card + hi.card := by
          rw [← Finset.card_union_of_disjoint]
          · congr 1; ext U; simp only [lo, hi, Finset.mem_union, Finset.mem_filter]
            cases U.val.testBit i <;> simp
          · rw [Finset.disjoint_left]; intro U h1 h2
            simp only [lo, hi, Finset.mem_filter] at h1 h2
            rw [h1.2] at h2; cases h2.2
        have hcard_eq : lo.card = hi.card := by
          apply Finset.card_bij (fun U _ => flip U)
          · intro U hU
            simp only [lo, hi, Finset.mem_filter] at hU ⊢
            exact ⟨hflip_mem U hU.1, by
              simp [flip, Nat.testBit_xor, Nat.shiftLeft_eq, Nat.testBit_two_pow, hU.2]⟩
          · intro U1 _ U2 _ heq
            have hv := congrArg (fun x : Fin (2 ^ k) => x.val ^^^ (1 <<< i)) heq
            dsimp only [flip] at hv
            rw [Nat.xor_assoc, Nat.xor_self, Nat.xor_zero,
                Nat.xor_assoc, Nat.xor_self, Nat.xor_zero] at hv
            exact Fin.ext hv
          · intro U hU
            simp only [lo, hi, Finset.mem_filter] at hU ⊢
            refine ⟨flip U, ⟨hflip_mem U hU.1, by
              simp [flip, Nat.testBit_xor, Nat.shiftLeft_eq, Nat.testBit_two_pow, hU.2]⟩, ?_⟩
            apply Fin.ext
            dsimp only [flip]
            rw [Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]
        omega

-- Degree and Iterative Subspace V_s
def degLe {k : Nat} (g : Fin (2 ^ k) → Bool) (s : Nat) : Prop :=
  ∀ T : Fin (2 ^ k), s < popcount k T.val → fmt g T = false

lemma degLe_shift {k : Nat} {g : Fin (2 ^ k) → Bool} {s : Nat}
    (hg : degLe g s) (d : Fin (2 ^ k)) :
    degLe (fun w => g ⟨w.val ^^^ d.val, xor_lt w.isLt d.isLt⟩) s := by
  intro T hT
  rw [fmt_shift]
  apply bxorFinset_zero
  intro S hS
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hS
  exact hg S (lt_of_lt_of_le hT (popcount_submask_le hS.1))

lemma fmt_shift_top {k : Nat} {g : Fin (2 ^ k) → Bool} {s : Nat}
    (hg : degLe g s) (d : Fin (2 ^ k)) {T : Fin (2 ^ k)} (hT : popcount k T.val = s) :
    fmt (fun w => g ⟨w.val ^^^ d.val, xor_lt w.isLt d.isLt⟩) T = fmt g T := by
  rw [fmt_shift]
  have hsplit : Finset.univ.filter (fun S : Fin (2 ^ k) =>
      submask T.val S.val = true ∧ submask (S.val ^^^ T.val) d.val = true) =
      insert T ((Finset.univ.filter (fun S : Fin (2 ^ k) =>
        submask T.val S.val = true ∧ submask (S.val ^^^ T.val) d.val = true)).erase T) := by
    symm
    apply Finset.insert_erase
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨submask_iff.mpr (fun _ h => h),
           by rw [Nat.xor_self]; exact submask_iff.mpr (fun _ h => by simp at h)⟩
  rw [hsplit, bxorFinset_insert (Finset.notMem_erase _ _)]
  have hrest : bxorFinset ((Finset.univ.filter (fun S : Fin (2 ^ k) =>
      submask T.val S.val = true ∧ submask (S.val ^^^ T.val) d.val = true)).erase T) (fmt g) = false := by
    apply bxorFinset_zero
    intro S hS
    simp only [Finset.mem_erase, Finset.mem_filter, Finset.mem_univ, true_and] at hS
    have hle := popcount_submask_le (k := k) hS.2.1
    have hlt : s < popcount k S.val := by
      by_contra hnot
      have heq : popcount k T.val = popcount k S.val := by omega
      exact hS.1 (popcount_submask_eq_imp hS.2.1 heq).symm
    exact hg S hlt
  rw [hrest, Bool.xor_false]

lemma degLe_xor {k : Nat} {g1 g2 : Fin (2 ^ k) → Bool} {s : Nat}
    (h1 : degLe g1 s) (h2 : degLe g2 s) :
    degLe (fun w => xor (g1 w) (g2 w)) s := by
  intro T hT
  rw [fmt_xor]; dsimp only; rw [h1 T hT, h2 T hT]; rfl

lemma degLe_deriv_of_degLe {k : Nat} {g : Fin (2 ^ k) → Bool} {b : Nat}
    (hb : 1 ≤ b) (hg : degLe g b) (d : Fin (2 ^ k)) :
    degLe (fun w => xor (g ⟨w.val ^^^ d.val, xor_lt w.isLt d.isLt⟩) (g w)) (b - 1) := by
  intro T hT
  rw [fmt_xor]; dsimp only
  by_cases heq : popcount k T.val = b
  · rw [fmt_shift_top hg d heq, Bool.xor_self]
  · have hgt : b < popcount k T.val := by omega
    rw [degLe_shift hg d T hgt, hg T hgt]; rfl

lemma degLe_zero_iff_const {k : Nat} (g : Fin (2 ^ k) → Bool) :
    degLe g 0 ↔ ∃ a : Bool, ∀ w : Fin (2 ^ k), g w = a := by
  constructor
  · intro hg
    refine ⟨fmt g ⟨0, Nat.two_pow_pos k⟩, fun w => ?_⟩
    have h1 : g w = fmt (fmt g) w := by rw [fmt_invol]
    rw [h1, fmt_eq_submaskSum]
    have hsplit : Finset.univ.filter (fun x : Fin (2 ^ k) => submask x.val w.val = true) =
        insert ⟨0, Nat.two_pow_pos k⟩
          ((Finset.univ.filter (fun x : Fin (2 ^ k) => submask x.val w.val = true)).erase
            ⟨0, Nat.two_pow_pos k⟩) := by
      symm
      apply Finset.insert_erase
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact submask_iff.mpr (fun _ h => by simp at h)
    rw [hsplit, bxorFinset_insert (Finset.notMem_erase _ _)]
    have hrest : bxorFinset ((Finset.univ.filter (fun x : Fin (2 ^ k) =>
        submask x.val w.val = true)).erase ⟨0, Nat.two_pow_pos k⟩) (fmt g) = false := by
      apply bxorFinset_zero
      intro x hx
      simp only [Finset.mem_erase, Finset.mem_filter, Finset.mem_univ, true_and] at hx
      have hpos : 0 < popcount k x.val := by
        by_contra h0
        have hpc0 : popcount k x.val = 0 := by omega
        exact hx.1 (Fin.ext (popcount_zero_iff.mp hpc0))
      exact hg x hpos
    rw [hrest, Bool.xor_false]
  · rintro ⟨a, ha⟩
    have hconst : fmt (fun _ : Fin (2 ^ k) => a) =
        fun T : Fin (2 ^ k) => if T.val = 0 then a else false := by
      apply anf_unique
      rw [fmt_invol]
      funext w
      rw [fmt_eq_submaskSum]
      have hsplit : Finset.univ.filter (fun x : Fin (2 ^ k) => submask x.val w.val = true) =
          insert ⟨0, Nat.two_pow_pos k⟩
            ((Finset.univ.filter (fun x : Fin (2 ^ k) => submask x.val w.val = true)).erase
              ⟨0, Nat.two_pow_pos k⟩) := by
        symm
        apply Finset.insert_erase
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact submask_iff.mpr (fun _ h => by simp at h)
      rw [hsplit, bxorFinset_insert (Finset.notMem_erase _ _)]
      have hrest : bxorFinset ((Finset.univ.filter (fun x : Fin (2 ^ k) =>
          submask x.val w.val = true)).erase ⟨0, Nat.two_pow_pos k⟩)
          (fun T : Fin (2 ^ k) => if T.val = 0 then a else false) = false := by
        apply bxorFinset_zero
        intro x hx
        simp only [Finset.mem_erase] at hx
        have hne : x.val ≠ 0 := fun h => hx.1 (Fin.ext h)
        simp [hne]
      rw [hrest]; simp
    intro T hT
    have hge : g = fun _ => a := funext ha
    rw [hge, hconst]
    have hne : T.val ≠ 0 := fun h => by
      have := popcount_zero_iff.mpr h
      omega
    simp [hne]

-- Iterative subspace V_s for any multi-output function f : Fin (2^k) → Fin m → Bool
def deriv {k m : Nat} (f : Fin (2 ^ k) → Fin m → Bool) (d : Fin (2 ^ k))
    (j : Fin m) (w : Fin (2 ^ k)) : Bool :=
  xor (f ⟨w.val ^^^ d.val, xor_lt w.isLt d.isLt⟩ j) (f w j)

def subV {k m : Nat} (f : Fin (2 ^ k) → Fin m → Bool) (s : Nat) (d : Fin (2 ^ k)) : Prop :=
  ∀ j : Fin m, degLe (deriv f d j) s

lemma subV_zero {k m : Nat} (f : Fin (2 ^ k) → Fin m → Bool) (s : Nat) :
    subV f s ⟨0, Nat.two_pow_pos k⟩ := by
  intro j
  have hd0 : deriv f ⟨0, Nat.two_pow_pos k⟩ j = fun _ => false := by
    funext w; simp [deriv]
  rw [hd0]
  have h0 : degLe (fun _ : Fin (2 ^ k) => false) 0 :=
    (degLe_zero_iff_const _).mpr ⟨false, fun _ => rfl⟩
  intro T hT; exact h0 T (by omega)

lemma deriv_xor {k m : Nat} (f : Fin (2 ^ k) → Fin m → Bool)
    (d1 d2 : Fin (2 ^ k)) (j : Fin m) (w : Fin (2 ^ k)) :
    deriv f ⟨d1.val ^^^ d2.val, xor_lt d1.isLt d2.isLt⟩ j w =
      xor (deriv f d1 j ⟨w.val ^^^ d2.val, xor_lt w.isLt d2.isLt⟩) (deriv f d2 j w) := by
  unfold deriv
  have heq : (⟨(w.val ^^^ d2.val) ^^^ d1.val, xor_lt (xor_lt w.isLt d2.isLt) d1.isLt⟩ : Fin (2 ^ k)) =
      ⟨w.val ^^^ (d1.val ^^^ d2.val), xor_lt w.isLt (xor_lt d1.isLt d2.isLt)⟩ := by
    apply Fin.ext
    dsimp only
    rw [Nat.xor_assoc, Nat.xor_comm d2.val d1.val]
  rw [heq]
  generalize f ⟨w.val ^^^ (d1.val ^^^ d2.val), _⟩ j = a
  generalize f ⟨w.val ^^^ d2.val, _⟩ j = b
  generalize f w j = c
  cases a <;> cases b <;> cases c <;> rfl

lemma subV_xor {k m : Nat} {f : Fin (2 ^ k) → Fin m → Bool} {s : Nat}
    {d1 d2 : Fin (2 ^ k)} (h1 : subV f s d1) (h2 : subV f s d2) :
    subV f s ⟨d1.val ^^^ d2.val, xor_lt d1.isLt d2.isLt⟩ := by
  intro j
  have hfun : deriv f ⟨d1.val ^^^ d2.val, xor_lt d1.isLt d2.isLt⟩ j =
      fun w => xor (deriv f d1 j ⟨w.val ^^^ d2.val, xor_lt w.isLt d2.isLt⟩) (deriv f d2 j w) :=
    funext (deriv_xor f d1 d2 j)
  rw [hfun]
  exact degLe_xor (degLe_shift (h1 j) d2) (h2 j)

lemma fmt_deriv_xor_top {k m : Nat} {f : Fin (2 ^ k) → Fin m → Bool} {s : Nat}
    {d1 d2 : Fin (2 ^ k)} (h1 : subV f s d1) (j : Fin m)
    {T : Fin (2 ^ k)} (hT : popcount k T.val = s) :
    fmt (deriv f ⟨d1.val ^^^ d2.val, xor_lt d1.isLt d2.isLt⟩ j) T =
      xor (fmt (deriv f d1 j) T) (fmt (deriv f d2 j) T) := by
  have hfun : deriv f ⟨d1.val ^^^ d2.val, xor_lt d1.isLt d2.isLt⟩ j =
      fun w => xor (deriv f d1 j ⟨w.val ^^^ d2.val, xor_lt w.isLt d2.isLt⟩) (deriv f d2 j w) :=
    funext (deriv_xor f d1 d2 j)
  rw [hfun, fmt_xor]; dsimp only
  rw [fmt_shift_top (h1 j) d2 hT]

-- ============================================================
-- PART 4: GF(2) Vector Algebra, Kernel Step, Echelonization & Counting
-- ============================================================

abbrev Vec (n : Nat) := Fin n → Bool

def vecZero (n : Nat) : Vec n := fun _ => false

def vecXor {n : Nat} (u v : Vec n) : Vec n := fun i => xor (u i) (v i)

def stdBasis (n : Nat) (i0 : Fin n) : Vec n := fun i => decide (i = i0)

def toVec (k : Nat) (w : Fin (2 ^ k)) : Vec k := fun i => w.val.testBit i.val

def ofVec (k : Nat) (v : Vec k) : Fin (2 ^ k) :=
  ⟨(List.range k).foldl (fun acc i =>
    acc ||| ((if hi : i < k then v ⟨i, hi⟩ else false).toNat <<< i)) 0, by
    apply Nat.lt_pow_two_of_testBit
    intro i hi
    rw [testBit_foldl_or]
    simp [Nat.not_lt_of_ge hi]⟩

lemma testBit_ofVec {k : Nat} (v : Vec k) (i : Nat) :
    (ofVec k v).val.testBit i = if hi : i < k then v ⟨i, hi⟩ else false := by
  unfold ofVec
  dsimp only
  rw [testBit_foldl_or]
  by_cases hi : i < k
  · simp [hi]
  · simp [hi]

lemma toVec_ofVec {k : Nat} (v : Vec k) : toVec k (ofVec k v) = v := by
  funext i
  simp [toVec, testBit_ofVec, i.isLt]

lemma ofVec_toVec {k : Nat} (w : Fin (2 ^ k)) : ofVec k (toVec k w) = w := by
  apply Fin.ext
  apply Nat.eq_of_testBit_eq
  intro i
  rw [testBit_ofVec]
  by_cases hi : i < k
  · simp [toVec, hi]
  · simp only [hi, ↓reduceDIte]
    symm
    exact Nat.testBit_lt_two_pow (w.isLt.trans_le (Nat.pow_le_pow_right Nat.zero_lt_two (by omega)))

lemma toVec_xor {k : Nat} (w1 w2 : Fin (2 ^ k)) :
    toVec k ⟨w1.val ^^^ w2.val, xor_lt w1.isLt w2.isLt⟩ = vecXor (toVec k w1) (toVec k w2) := by
  funext i; simp [toVec, vecXor, Nat.testBit_xor]

lemma ofVec_xor {k : Nat} (u v : Vec k) :
    ofVec k (vecXor u v) = ⟨(ofVec k u).val ^^^ (ofVec k v).val, xor_lt (ofVec k u).isLt (ofVec k v).isLt⟩ := by
  have := congrArg (ofVec k) (toVec_xor (ofVec k u) (ofVec k v))
  rw [ofVec_toVec, toVec_ofVec, toVec_ofVec] at this
  exact this.symm

lemma toVec_zero {k : Nat} : toVec k ⟨0, Nat.two_pow_pos k⟩ = vecZero k := by
  funext i; simp [toVec, vecZero]

lemma ofVec_zero {k : Nat} : ofVec k (vecZero k) = ⟨0, Nat.two_pow_pos k⟩ := by
  rw [← toVec_zero, ofVec_toVec]

lemma vecXor_comm {n : Nat} (u v : Vec n) : vecXor u v = vecXor v u := by
  funext i; exact Bool.xor_comm _ _

lemma vecXor_assoc {n : Nat} (u v w : Vec n) : vecXor (vecXor u v) w = vecXor u (vecXor v w) := by
  funext i; exact Bool.xor_assoc _ _ _

lemma vecXor_self {n : Nat} (u : Vec n) : vecXor u u = vecZero n := by
  funext i; simp [vecXor, vecZero]

lemma vecXor_zero {n : Nat} (u : Vec n) : vecXor u (vecZero n) = u := by
  funext i; simp [vecXor, vecZero]

lemma zero_vecXor {n : Nat} (u : Vec n) : vecXor (vecZero n) u = u := by
  funext i; simp [vecXor, vecZero]

def vecDot {n : Nat} (u v : Vec n) : Bool :=
  (List.finRange n).foldl (fun acc i => xor acc (u i && v i)) false

lemma vecDot_eq_bxor {n : Nat} (u v : Vec n) :
    vecDot u v = bxorFinset Finset.univ (fun i : Fin n => u i && v i) :=
  bxorFinset_finRange _

lemma vecDot_zero_left {n : Nat} (v : Vec n) : vecDot (vecZero n) v = false := by
  rw [vecDot_eq_bxor]; exact bxorFinset_zero (fun _ _ => rfl)

lemma vecDot_zero_right {n : Nat} (u : Vec n) : vecDot u (vecZero n) = false := by
  rw [vecDot_eq_bxor]; exact bxorFinset_zero (fun _ _ => by simp [vecZero])

lemma vecDot_xor_left {n : Nat} (u1 u2 v : Vec n) :
    vecDot (vecXor u1 u2) v = xor (vecDot u1 v) (vecDot u2 v) := by
  rw [vecDot_eq_bxor, vecDot_eq_bxor, vecDot_eq_bxor, ← bxorFinset_xor]
  apply bxorFinset_congr
  intro i _
  dsimp only [vecXor]
  cases u1 i <;> cases u2 i <;> cases v i <;> rfl

lemma vecDot_xor_right {n : Nat} (u v1 v2 : Vec n) :
    vecDot u (vecXor v1 v2) = xor (vecDot u v1) (vecDot u v2) := by
  rw [vecDot_eq_bxor, vecDot_eq_bxor, vecDot_eq_bxor, ← bxorFinset_xor]
  apply bxorFinset_congr
  intro i _
  dsimp only [vecXor]
  cases u i <;> cases v1 i <;> cases v2 i <;> rfl

lemma vecDot_stdBasis_left {n : Nat} (i0 : Fin n) (v : Vec n) :
    vecDot (stdBasis n i0) v = v i0 := by
  rw [vecDot_eq_bxor]
  have hsp : (Finset.univ : Finset (Fin n)) = insert i0 (Finset.univ.erase i0) :=
    (Finset.insert_erase (Finset.mem_univ i0)).symm
  rw [hsp, bxorFinset_insert (Finset.notMem_erase _ _)]
  have hrest : bxorFinset (Finset.univ.erase i0) (fun i => stdBasis n i0 i && v i) = false := by
    apply bxorFinset_zero
    intro i hi
    simp only [Finset.mem_erase] at hi
    simp [stdBasis, hi.1]
  rw [hrest]; simp [stdBasis]

lemma vecDot_stdBasis_right {n : Nat} (u : Vec n) (i0 : Fin n) :
    vecDot u (stdBasis n i0) = u i0 := by
  have h : vecDot u (stdBasis n i0) = vecDot (stdBasis n i0) u := by
    rw [vecDot_eq_bxor, vecDot_eq_bxor]
    apply bxorFinset_congr
    intro i _; exact Bool.and_comm _ _
  rw [h, vecDot_stdBasis_left]

lemma bxorFinset_and_left {α : Type} [DecidableEq α] (s : Finset α) (b : Bool) (f : α → Bool) :
    (b && bxorFinset s f) = bxorFinset s (fun a => b && f a) := by
  cases b
  · simp only [Bool.false_and]
    symm; exact bxorFinset_zero (fun _ _ => rfl)
  · simp only [Bool.true_and]

def vecLinComb {m n : Nat} (M : Fin m → Vec n) (a : Vec m) : Vec n :=
  fun j => vecDot a (fun i => M i j)

lemma vecLinComb_zero {m n : Nat} (M : Fin m → Vec n) :
    vecLinComb M (vecZero m) = vecZero n := by
  funext j; exact vecDot_zero_left _

lemma vecLinComb_xor {m n : Nat} (M : Fin m → Vec n) (a b : Vec m) :
    vecLinComb M (vecXor a b) = vecXor (vecLinComb M a) (vecLinComb M b) := by
  funext j; exact vecDot_xor_left _ _ _

lemma vecLinComb_stdBasis {m n : Nat} (M : Fin m → Vec n) (i0 : Fin m) :
    vecLinComb M (stdBasis m i0) = M i0 := by
  funext j; exact vecDot_stdBasis_left i0 _

lemma vecLinComb_id {n : Nat} (a : Vec n) :
    vecLinComb (stdBasis n) a = a := by
  funext j
  change vecDot a (fun i => stdBasis n i j) = a j
  have h : (fun i : Fin n => stdBasis n i j) = stdBasis n j := by
    funext i; simp [stdBasis, eq_comm]
  rw [h, vecDot_stdBasis_right]

lemma vecLinComb_comp {p m n : Nat} (M : Fin m → Vec n) (U : Fin p → Vec m) (a : Vec p) :
    vecLinComb (fun r => vecLinComb M (U r)) a = vecLinComb M (vecLinComb U a) := by
  funext j
  simp only [vecLinComb, vecDot_eq_bxor]
  have h1 : bxorFinset Finset.univ (fun r : Fin p => a r && bxorFinset Finset.univ (fun i : Fin m => U r i && M i j)) =
      bxorFinset Finset.univ (fun r : Fin p => bxorFinset Finset.univ (fun i : Fin m => a r && (U r i && M i j))) := by
    apply bxorFinset_congr
    intro r _; exact bxorFinset_and_left _ _ _
  rw [h1, bxorFinset_comm]
  apply bxorFinset_congr
  intro i _
  have h2 : (bxorFinset Finset.univ (fun r : Fin p => a r && U r i) && M i j) =
      bxorFinset Finset.univ (fun r : Fin p => (a r && U r i) && M i j) := by
    rw [Bool.and_comm, bxorFinset_and_left]
    apply bxorFinset_congr
    intro r _; exact Bool.and_comm _ _
  rw [h2]
  apply bxorFinset_congr
  intro r _; exact (Bool.and_assoc _ _ _).symm

def inSpan {m n : Nat} (M : Fin m → Vec n) (v : Vec n) : Prop :=
  ∃ a : Vec m, v = vecLinComb M a

lemma inSpan_zero {m n : Nat} (M : Fin m → Vec n) : inSpan M (vecZero n) :=
  ⟨vecZero m, (vecLinComb_zero M).symm⟩

lemma inSpan_xor {m n : Nat} {M : Fin m → Vec n} {u v : Vec n}
    (hu : inSpan M u) (hv : inSpan M v) : inSpan M (vecXor u v) := by
  obtain ⟨a, rfl⟩ := hu; obtain ⟨b, rfl⟩ := hv
  exact ⟨vecXor a b, (vecLinComb_xor M a b).symm⟩

lemma inSpan_row {m n : Nat} (M : Fin m → Vec n) (i : Fin m) : inSpan M (M i) :=
  ⟨stdBasis m i, (vecLinComb_stdBasis M i).symm⟩

lemma inSpan_stdBasis {n : Nat} (v : Vec n) : inSpan (stdBasis n) v :=
  ⟨v, (vecLinComb_id v).symm⟩

lemma inSpan_comp {p m n : Nat} (M : Fin m → Vec n) (U : Fin p → Vec m) (v : Vec n) :
    inSpan (fun r => vecLinComb M (U r)) v ↔ ∃ a : Vec m, inSpan U a ∧ v = vecLinComb M a := by
  constructor
  · rintro ⟨b, rfl⟩
    exact ⟨vecLinComb U b, ⟨b, rfl⟩, vecLinComb_comp M U b⟩
  · rintro ⟨a, ⟨b, rfl⟩, rfl⟩
    exact ⟨b, (vecLinComb_comp M U b).symm⟩

lemma additive_vecLinComb {m n : Nat} (L : Vec n → Bool)
    (h0 : L (vecZero n) = false)
    (hadd : ∀ u v, L (vecXor u v) = xor (L u) (L v))
    (M : Fin m → Vec n) (a : Vec m) :
    L (vecLinComb M a) = vecDot a (fun i => L (M i)) := by
  have hgen : ∀ (s : Finset (Fin m)),
      L (fun j => bxorFinset s (fun i => a i && M i j)) =
        bxorFinset s (fun i => a i && L (M i)) := by
    intro s
    induction s using Finset.induction with
    | empty =>
      have : (fun j : Fin n => bxorFinset (∅ : Finset (Fin m)) (fun i => a i && M i j)) = vecZero n := by
        funext j; simp [bxorFinset, vecZero]
      rw [this, h0, bxorFinset_empty]
    | insert x s hx ih =>
      have hfn : (fun j : Fin n => bxorFinset (insert x s) (fun i => a i && M i j)) =
          vecXor (fun j => a x && M x j) (fun j => bxorFinset s (fun i => a i && M i j)) := by
        funext j; exact bxorFinset_insert hx _
      rw [hfn, hadd, ih, bxorFinset_insert hx]
      congr 1
      cases a x
      · simp [h0, show (fun _ : Fin n => false) = vecZero n from rfl]
      · simp
  have hlc : vecLinComb M a = fun j => bxorFinset Finset.univ (fun i => a i && M i j) := by
    funext j; exact vecDot_eq_bxor _ _
  rw [hlc, vecDot_eq_bxor]
  exact hgen Finset.univ

-- First-true bit and anyBit
def anyBit {m : Nat} (c : Vec m) : Bool :=
  (List.finRange m).foldl (fun acc i => acc || c i) false

lemma foldl_or_eq_true {α : Type} (l : List α) (f : α → Bool) (init : Bool) :
    l.foldl (fun acc x => acc || f x) init = true ↔ init = true ∨ ∃ x ∈ l, f x = true := by
  induction l generalizing init with
  | nil => simp
  | cons a l ih =>
    simp only [List.foldl_cons, ih, Bool.or_eq_true, List.mem_cons]
    constructor
    · rintro ((h | h) | ⟨x, hx, hfx⟩)
      · exact Or.inl h
      · exact Or.inr ⟨a, Or.inl rfl, h⟩
      · exact Or.inr ⟨x, Or.inr hx, hfx⟩
    · rintro (h | ⟨x, rfl | hx, hfx⟩)
      · exact Or.inl (Or.inl h)
      · exact Or.inl (Or.inr hfx)
      · exact Or.inr ⟨x, hx, hfx⟩

lemma foldl_and_eq_true {α : Type} (l : List α) (f : α → Bool) (init : Bool) :
    l.foldl (fun acc x => acc && f x) init = true ↔ init = true ∧ ∀ x ∈ l, f x = true := by
  induction l generalizing init with
  | nil => simp
  | cons a l ih =>
    simp only [List.foldl_cons, ih, Bool.and_eq_true, List.mem_cons]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      refine ⟨h1, fun x hx => ?_⟩
      rcases hx with rfl | hx
      · exact h2
      · exact h3 x hx
    · rintro ⟨h1, h2⟩
      exact ⟨⟨h1, h2 a (Or.inl rfl)⟩, fun x hx => h2 x (Or.inr hx)⟩

lemma anyBit_eq_true {m : Nat} (c : Vec m) :
    anyBit c = true ↔ ∃ i : Fin m, c i = true := by
  unfold anyBit
  rw [foldl_or_eq_true]
  simp

def firstBit {m : Nat} (c : Vec m) (i : Fin m) : Bool :=
  c i && (List.finRange m).foldl (fun acc j => acc && (decide (i.val ≤ j.val) || !(c j))) true

lemma firstBit_eq_true {m : Nat} (c : Vec m) (i : Fin m) :
    firstBit c i = true ↔ c i = true ∧ ∀ j : Fin m, j.val < i.val → c j = false := by
  unfold firstBit
  rw [Bool.and_eq_true, foldl_and_eq_true]
  constructor
  · rintro ⟨hci, _, hall⟩
    refine ⟨hci, fun j hj => ?_⟩
    have h := hall j (List.mem_finRange j)
    simp only [Bool.or_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at h
    rcases h with hle | hcf
    · omega
    · exact hcf
  · rintro ⟨hci, hall⟩
    refine ⟨hci, rfl, fun j _ => ?_⟩
    simp only [Bool.or_eq_true, decide_eq_true_eq, Bool.not_eq_true']
    by_cases hle : i.val ≤ j.val
    · exact Or.inl hle
    · exact Or.inr (hall j (by omega))

lemma firstBit_unique {m : Nat} {c : Vec m} {i1 i2 : Fin m}
    (h1 : firstBit c i1 = true) (h2 : firstBit c i2 = true) : i1 = i2 := by
  rw [firstBit_eq_true] at h1 h2
  apply Fin.ext
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
  · have := h2.2 i1 hlt; rw [h1.1] at this; cases this
  · have := h1.2 i2 hgt; rw [h2.1] at this; cases this

lemma exists_firstBit_of_exists {m : Nat} {c : Vec m} (h : ∃ i : Fin m, c i = true) :
    ∃ p : Fin m, firstBit c p = true := by
  classical
  have hex : ∃ k : Nat, ∃ hk : k < m, c ⟨k, hk⟩ = true := by
    obtain ⟨i, hi⟩ := h; exact ⟨i.val, i.isLt, hi⟩
  let k0 := Nat.find hex
  have hk0 := Nat.find_spec hex
  obtain ⟨hlt, hck⟩ := hk0
  refine ⟨⟨k0, hlt⟩, (firstBit_eq_true c ⟨k0, hlt⟩).mpr ⟨hck, fun j hj => ?_⟩⟩
  cases hcj : c j
  · rfl
  · exfalso
    exact Nat.find_min hex hj ⟨j.isLt, hcj⟩

def pivotVec {m n : Nat} (U : Fin m → Vec n) (c : Vec m) : Vec n :=
  vecLinComb U (firstBit c)

lemma pivotVec_eq_of_firstBit {m n : Nat} (U : Fin m → Vec n) {c : Vec m} {p : Fin m}
    (hp : firstBit c p = true) : pivotVec U c = U p := by
  have hfb : firstBit c = stdBasis m p := by
    funext i
    cases h : firstBit c i
    · unfold stdBasis
      symm; rw [decide_eq_false_iff_not]
      rintro rfl; rw [hp] at h; cases h
    · simp [stdBasis, firstBit_unique h hp]
  unfold pivotVec
  rw [hfb, vecLinComb_stdBasis]

def restrictKernelStep {m n : Nat} (U : Fin m → Vec n) (c : Vec m) (i : Fin m) : Vec n :=
  if firstBit c i then vecZero n
  else if c i then vecXor (U i) (pivotVec U c)
  else U i

lemma inSpan_restrictKernelStep {m n : Nat} (U : Fin m → Vec n) (c : Vec m) (w : Vec n) :
    inSpan (restrictKernelStep U c) w ↔ ∃ a : Vec m, w = vecLinComb U a ∧ vecDot a c = false := by
  by_cases hany : ∃ i : Fin m, c i = true
  · obtain ⟨p, hp⟩ := exists_firstBit_of_exists hany
    have hcp : c p = true := ((firstBit_eq_true c p).mp hp).1
    have hpiv : pivotVec U c = U p := pivotVec_eq_of_firstBit U hp
    have hrow : ∀ i : Fin m, restrictKernelStep U c i =
        if i = p then vecZero n else if c i then vecXor (U i) (U p) else U i := by
      intro i
      unfold restrictKernelStep
      by_cases hip : i = p
      · subst hip; simp [hp]
      · have hnf : firstBit c i = false := by
          cases hf : firstBit c i
          · rfl
          · exfalso; exact hip (firstBit_unique hf hp)
        simp [hnf, hip, hpiv]
    let rest : Finset (Fin m) := Finset.univ.erase p
    have hsp : (Finset.univ : Finset (Fin m)) = insert p rest :=
      (Finset.insert_erase (Finset.mem_univ p)).symm
    have hp_not_rest : p ∉ rest := Finset.notMem_erase _ _
    have hcomb_eq : ∀ (b : Vec m),
        vecLinComb (restrictKernelStep U c) b =
          vecLinComb U (fun i => if i = p then
            bxorFinset rest (fun j => b j && c j) else b i) := by
      intro b
      funext k
      simp only [vecLinComb, vecDot_eq_bxor]
      rw [hsp, bxorFinset_insert hp_not_rest, bxorFinset_insert hp_not_rest]
      simp only [hrow p, ↓reduceIte, vecZero, Bool.and_false, Bool.false_xor]
      have hlhs : bxorFinset rest (fun i => b i && restrictKernelStep U c i k) =
          bxorFinset rest (fun i => xor (b i && U i k) ((b i && c i) && U p k)) := by
        apply bxorFinset_congr
        intro i hi
        have hne : i ≠ p := (Finset.mem_erase.mp hi).1
        rw [hrow i, if_neg hne]
        cases hc : c i
        · simp [hc]
        · simp only [hc, ↓reduceIte, vecXor]
          cases b i <;> cases U i k <;> cases U p k <;> rfl
      rw [hlhs, bxorFinset_xor]
      have hr1 : bxorFinset rest (fun i => (b i && c i) && U p k) =
          (bxorFinset rest (fun j => b j && c j) && U p k) := by
        rw [Bool.and_comm, bxorFinset_and_left]
        apply bxorFinset_congr
        intro i _; exact Bool.and_comm _ _
      have hr2 : bxorFinset rest
          (fun i => (if i = p then bxorFinset rest (fun j => b j && c j) else b i) && U i k) =
          bxorFinset rest (fun i => b i && U i k) := by
        apply bxorFinset_congr
        intro i hi
        have hne : i ≠ p := (Finset.mem_erase.mp hi).1
        simp [hne]
      rw [hr1, hr2, Bool.xor_comm]
    constructor
    · rintro ⟨b, rfl⟩
      refine ⟨fun i => if i = p then bxorFinset rest (fun j => b j && c j) else b i,
        hcomb_eq b, ?_⟩
      rw [vecDot_eq_bxor, hsp, bxorFinset_insert hp_not_rest]
      simp only [↓reduceIte, hcp, Bool.and_true]
      have hr : bxorFinset rest
          (fun i => (if i = p then bxorFinset rest (fun j => b j && c j) else b i) && c i) =
          bxorFinset rest (fun i => b i && c i) := by
        apply bxorFinset_congr
        intro i hi; simp [(Finset.mem_erase.mp hi).1]
      rw [hr, Bool.xor_self]
    · rintro ⟨a, rfl, hdot⟩
      refine ⟨a, ?_⟩
      rw [hcomb_eq a]
      congr 1
      funext i
      by_cases hip : i = p
      · subst hip
        simp only [↓reduceIte]
        rw [vecDot_eq_bxor, hsp, bxorFinset_insert hp_not_rest, hcp, Bool.and_true] at hdot
        cases ha : a i <;> cases hb : bxorFinset rest (fun j => a j && c j) <;>
          simp [ha, hb] at hdot ⊢
      · simp [hip]
  · push_neg at hany
    have hcf : ∀ i : Fin m, c i = false := fun i => Bool.eq_false_iff.mpr (hany i)
    have hstep : restrictKernelStep U c = U := by
      funext i
      have hnf : firstBit c i = false := by simp [firstBit, hcf i]
      simp [restrictKernelStep, hnf, hcf i]
    rw [hstep]
    constructor
    · rintro ⟨a, rfl⟩
      exact ⟨a, rfl, by rw [vecDot_eq_bxor]; exact bxorFinset_zero (fun i _ => by simp [hcf i])⟩
    · rintro ⟨a, rfl, _⟩; exact ⟨a, rfl⟩

-- Echelonization of an (nrows × ncols) GF(2) matrix
structure EchState (nrows ncols : Nat) where
  work : Fin nrows → Vec ncols
  hasP : Fin ncols → Bool
  piv  : Fin ncols → Vec ncols

def echelonStep {nrows ncols : Nat} (st : EchState nrows ncols) (col : Fin ncols) :
    EchState nrows ncols :=
  let c : Vec nrows := fun i => st.work i col
  let pvec : Vec ncols := pivotVec st.work c
  { work := restrictKernelStep st.work c
    hasP := fun j => if j = col then anyBit c else st.hasP j
    piv  := fun j => if j = col then pvec else st.piv j }

def echelonInit {nrows ncols : Nat} (M : Fin nrows → Vec ncols) : EchState nrows ncols :=
  { work := M, hasP := fun _ => false, piv := fun _ => vecZero ncols }

def echelonPrefix {nrows ncols : Nat} (M : Fin nrows → Vec ncols) (t : Nat) :
    EchState nrows ncols :=
  ((List.finRange ncols).take t).foldl echelonStep (echelonInit M)

def echelon {nrows ncols : Nat} (M : Fin nrows → Vec ncols) : EchState nrows ncols :=
  (List.finRange ncols).foldl echelonStep (echelonInit M)

lemma echelonPrefix_zero {nrows ncols : Nat} (M : Fin nrows → Vec ncols) :
    echelonPrefix M 0 = echelonInit M := rfl

lemma echelonPrefix_succ {nrows ncols : Nat} (M : Fin nrows → Vec ncols)
    {t : Nat} (ht : t < ncols) :
    echelonPrefix M (t + 1) = echelonStep (echelonPrefix M t) ⟨t, ht⟩ := by
  unfold echelonPrefix
  have htake : (List.finRange ncols).take (t + 1) = (List.finRange ncols).take t ++ [⟨t, ht⟩] := by
    rw [List.take_add_one, List.getElem?_eq_getElem (by simp [ht])]
    simp [List.getElem_finRange]
  rw [htake, List.foldl_append]; rfl

lemma echelon_eq_prefix {nrows ncols : Nat} (M : Fin nrows → Vec ncols) :
    echelon M = echelonPrefix M ncols := by
  simp [echelon, echelonPrefix, List.take_of_length_le]

structure EchInv {nrows ncols : Nat} (M : Fin nrows → Vec ncols) (t : Nat)
    (st : EchState nrows ncols) : Prop where
  work_zero_lt : ∀ i : Fin nrows, ∀ j : Fin ncols, j.val < t → st.work i j = false
  piv_zero_ge : ∀ j : Fin ncols, t ≤ j.val → st.hasP j = false ∧ st.piv j = vecZero ncols
  piv_tri : ∀ j : Fin ncols,
    (∀ j' : Fin ncols, j'.val < j.val → st.piv j j' = false) ∧
    (st.hasP j = true → st.piv j j = true) ∧
    (st.hasP j = false → st.piv j = vecZero ncols)
  span_eq : ∀ v : Vec ncols,
    (∃ w1 w2, inSpan st.piv w1 ∧ inSpan st.work w2 ∧ v = vecXor w1 w2) ↔ inSpan M v
  rank_le_zeros :
    (Finset.univ.filter (fun j : Fin ncols => st.hasP j = true)).card ≤
      (Finset.univ.filter (fun i : Fin nrows => st.work i = vecZero ncols)).card

lemma echelonPrefix_inv {nrows ncols : Nat} (M : Fin nrows → Vec ncols)
    (t : Nat) (ht : t ≤ ncols) : EchInv M t (echelonPrefix M t) := by
  induction t with
  | zero =>
    rw [echelonPrefix_zero]
    refine ⟨fun _ _ hj => by omega, fun j _ => ⟨rfl, rfl⟩,
      fun j => ⟨fun _ _ => rfl, (fun h => by simp [echelonInit] at h), fun _ => rfl⟩, ?_, by simp [echelonInit]⟩
    intro v
    constructor
    · rintro ⟨w1, w2, ⟨a1, rfl⟩, hw2, rfl⟩
      have h1 : vecLinComb (echelonInit M).piv a1 = vecZero ncols := by
        funext j; simp [echelonInit, vecLinComb, vecDot_eq_bxor]
        exact bxorFinset_zero (fun _ _ => by simp [vecZero])
      rw [h1, zero_vecXor]; exact hw2
    · intro hv
      exact ⟨vecZero ncols, v, inSpan_zero _, hv, (zero_vecXor v).symm⟩
  | succ t ih =>
    have ht' : t < ncols := by omega
    have hprev := ih (by omega)
    rw [echelonPrefix_succ M ht']
    set st := echelonPrefix M t
    set col : Fin ncols := ⟨t, ht'⟩
    set c : Vec nrows := fun i => st.work i col
    set pvec : Vec ncols := pivotVec st.work c
    set st' := echelonStep st col
    have hpvec_in : inSpan st.work pvec := ⟨firstBit c, rfl⟩
    have hpvec_lt : ∀ j' : Fin ncols, j'.val < t → pvec j' = false := by
      intro j' hj'
      simp only [pvec, pivotVec, vecLinComb, vecDot_eq_bxor]
      exact bxorFinset_zero (fun i _ => by rw [hprev.work_zero_lt i j' hj', Bool.and_false])
    have hpvec_diag : anyBit c = true → pvec col = true := by
      intro ha
      obtain ⟨p, hp⟩ := exists_firstBit_of_exists ((anyBit_eq_true c).mp ha)
      dsimp only [pvec]
      rw [pivotVec_eq_of_firstBit st.work hp]
      exact ((firstBit_eq_true c p).mp hp).1
    have hpvec_false : anyBit c = false → pvec = vecZero ncols := by
      intro ha
      have hcf : ∀ i, c i = false := fun i => by
        cases hci : c i
        · rfl
        · have := (anyBit_eq_true c).mpr ⟨i, hci⟩; rw [ha] at this; cases this
      funext j
      simp only [pvec, pivotVec, vecLinComb, vecDot_eq_bxor, vecZero]
      exact bxorFinset_zero (fun i _ => by simp [firstBit, hcf i])
    have hwork_lt : ∀ i : Fin nrows, ∀ j : Fin ncols, j.val < t + 1 → st'.work i j = false := by
      intro i j hj
      have hwi : inSpan st'.work (st'.work i) := inSpan_row _ i
      obtain ⟨a, ha, hdot⟩ := (inSpan_restrictKernelStep st.work c (st'.work i)).mp hwi
      rw [ha]
      by_cases hjt : j.val < t
      · simp only [vecLinComb, vecDot_eq_bxor]
        exact bxorFinset_zero (fun r _ => by rw [hprev.work_zero_lt r j hjt, Bool.and_false])
      · have hjeq : j = col := Fin.ext (show j.val = t by omega)
        subst hjeq
        exact hdot
    have hpiv_ge : ∀ j : Fin ncols, t + 1 ≤ j.val → st'.hasP j = false ∧ st'.piv j = vecZero ncols := by
      intro j hj
      have hne : j ≠ col := fun h => by have := congrArg Fin.val h; dsimp [col] at this; omega
      simpa [st', echelonStep, hne] using hprev.piv_zero_ge j (by omega)
    have hpiv_tri : ∀ j : Fin ncols,
        (∀ j' : Fin ncols, j'.val < j.val → st'.piv j j' = false) ∧
        (st'.hasP j = true → st'.piv j j = true) ∧
        (st'.hasP j = false → st'.piv j = vecZero ncols) := by
      intro j
      by_cases hjc : j = col
      · subst hjc
        simp only [st', echelonStep, ↓reduceIte]
        exact ⟨hpvec_lt, hpvec_diag, hpvec_false⟩
      · simp only [st', echelonStep, hjc, ↓reduceIte]
        exact hprev.piv_tri j
    have hspan : ∀ v : Vec ncols,
        (∃ w1 w2, inSpan st'.piv w1 ∧ inSpan st'.work w2 ∧ v = vecXor w1 w2) ↔ inSpan M v := by
      intro v
      rw [← hprev.span_eq v]
      have hpiv_old : ∀ j : Fin ncols, j ≠ col → st'.piv j = st.piv j := by
        intro j hne; simp [st', echelonStep, hne]
      have hcol_old : st.piv col = vecZero ncols := (hprev.piv_zero_ge col (le_refl t)).2
      have hspan_piv' : ∀ u, inSpan st'.piv u ↔
          ∃ (u1 : Vec ncols) (b : Bool), inSpan st.piv u1 ∧ u = vecXor u1 (if b then pvec else vecZero ncols) := by
        intro u
        constructor
        · rintro ⟨a, rfl⟩
          refine ⟨vecLinComb st.piv (fun j => if j = col then false else a j), a col, ⟨_, rfl⟩, ?_⟩
          funext k
          simp only [vecLinComb, vecDot_eq_bxor, vecXor]
          have hsp : (Finset.univ : Finset (Fin ncols)) = insert col (Finset.univ.erase col) :=
            (Finset.insert_erase (Finset.mem_univ col)).symm
          rw [hsp, bxorFinset_insert (Finset.notMem_erase _ _),
              bxorFinset_insert (Finset.notMem_erase _ _)]
          simp only [↓reduceIte, Bool.false_and, Bool.false_xor]
          have hrest : bxorFinset (Finset.univ.erase col) (fun j => a j && st'.piv j k) =
              bxorFinset (Finset.univ.erase col) (fun j => (if j = col then false else a j) && st.piv j k) := by
            apply bxorFinset_congr
            intro j hj
            have hne : j ≠ col := (Finset.mem_erase.mp hj).1
            simp [hne, hpiv_old j hne]
          rw [hrest, Bool.xor_comm]
          congr 1
          cases a col <;> simp [st', echelonStep, vecZero, pvec, c]
        · rintro ⟨u1, b, ⟨a, rfl⟩, rfl⟩
          refine ⟨fun j => if j = col then b else a j, ?_⟩
          funext k
          simp only [vecLinComb, vecDot_eq_bxor, vecXor]
          have hsp : (Finset.univ : Finset (Fin ncols)) = insert col (Finset.univ.erase col) :=
            (Finset.insert_erase (Finset.mem_univ col)).symm
          rw [hsp, bxorFinset_insert (Finset.notMem_erase _ _),
              bxorFinset_insert (Finset.notMem_erase _ _)]
          simp only [hcol_old, vecZero, Bool.and_false, Bool.false_xor, ↓reduceIte]
          have hrest : bxorFinset (Finset.univ.erase col)
              (fun j => (if j = col then b else a j) && st'.piv j k) =
              bxorFinset (Finset.univ.erase col) (fun j => a j && st.piv j k) := by
            apply bxorFinset_congr
            intro j hj
            have hne : j ≠ col := (Finset.mem_erase.mp hj).1
            simp [hne, hpiv_old j hne]
          rw [hrest, Bool.xor_comm]
          congr 1
          cases b <;> simp [st', echelonStep, vecZero, pvec, c]
      constructor
      · rintro ⟨w1, w2, hw1, hw2, rfl⟩
        obtain ⟨u1, b, hu1, rfl⟩ := (hspan_piv' w1).mp hw1
        obtain ⟨a2, rfl, _⟩ := (inSpan_restrictKernelStep st.work c w2).mp hw2
        refine ⟨u1, vecXor (if b then pvec else vecZero ncols) (vecLinComb st.work a2), hu1, ?_, by rw [vecXor_assoc]⟩
        apply inSpan_xor
        · cases b
          · exact inSpan_zero _
          · exact hpvec_in
        · exact ⟨a2, rfl⟩
      · rintro ⟨w1, w2, hw1, ⟨a, rfl⟩, rfl⟩
        by_cases hdot : vecDot a c = false
        · refine ⟨w1, vecLinComb st.work a, (hspan_piv' w1).mpr ⟨w1, false, hw1, by simp [vecXor_zero]⟩,
            (inSpan_restrictKernelStep st.work c _).mpr ⟨a, rfl, hdot⟩, rfl⟩
        · have hdotT : vecDot a c = true := Bool.eq_true_of_not_eq_false hdot
          have hany : ∃ i, c i = true := by
            by_contra hall; push_neg at hall
            have h0 : vecDot a c = false := by
              rw [vecDot_eq_bxor]; exact bxorFinset_zero (fun i _ => by simp [Bool.eq_false_iff.mpr (hall i)])
            rw [h0] at hdotT; cases hdotT
          obtain ⟨p, hp⟩ := exists_firstBit_of_exists hany
          have hcp : c p = true := ((firstBit_eq_true c p).mp hp).1
          have hpivp : pvec = st.work p := pivotVec_eq_of_firstBit st.work hp
          set a' : Vec nrows := vecXor a (stdBasis nrows p)
          have hdot' : vecDot a' c = false := by
            simp only [a', vecDot_xor_left, hdotT, vecDot_stdBasis_left, hcp]; rfl
          have hcomb' : vecLinComb st.work a' = vecXor (vecLinComb st.work a) pvec := by
            rw [vecLinComb_xor, vecLinComb_stdBasis, hpivp]
          have heqv : vecXor w1 (vecLinComb st.work a) = vecXor (vecXor w1 pvec) (vecLinComb st.work a') := by
            rw [hcomb', vecXor_assoc, ← vecXor_assoc pvec (vecLinComb st.work a) pvec,
                vecXor_comm pvec (vecLinComb st.work a), vecXor_assoc, vecXor_self, vecXor_zero]
          refine ⟨vecXor w1 pvec, vecLinComb st.work a',
            (hspan_piv' _).mpr ⟨w1, true, hw1, by simp⟩,
            (inSpan_restrictKernelStep st.work c _).mpr ⟨a', rfl, hdot'⟩, heqv⟩
    have hrank :
        (Finset.univ.filter (fun j : Fin ncols => st'.hasP j = true)).card ≤
          (Finset.univ.filter (fun i : Fin nrows => st'.work i = vecZero ncols)).card := by
      by_cases ha : anyBit c = true
      · obtain ⟨p, hp⟩ := exists_firstBit_of_exists ((anyBit_eq_true c).mp ha)
        have hcp : c p = true := ((firstBit_eq_true c p).mp hp).1
        have hsubP : Finset.univ.filter (fun j : Fin ncols => st'.hasP j = true) ⊆
            insert col (Finset.univ.filter (fun j : Fin ncols => st.hasP j = true)) := by
          intro j hj
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert] at hj ⊢
          by_cases hjc : j = col
          · exact Or.inl hjc
          · right; simpa [st', echelonStep, hjc] using hj
        have hcardP : (Finset.univ.filter (fun j : Fin ncols => st'.hasP j = true)).card ≤
            (Finset.univ.filter (fun j : Fin ncols => st.hasP j = true)).card + 1 :=
          (Finset.card_le_card hsubP).trans (Finset.card_insert_le _ _)
        have hsubZ : insert p (Finset.univ.filter (fun i : Fin nrows => st.work i = vecZero ncols)) ⊆
            Finset.univ.filter (fun i : Fin nrows => st'.work i = vecZero ncols) := by
          intro i hi
          simp only [Finset.mem_insert, Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
          rcases hi with rfl | hiz
          · dsimp only [c] at hp
            simp [st', echelonStep, restrictKernelStep, hp]
          · have hci : st.work i col = false := by simp [hiz, vecZero]
            have hfi : firstBit (fun r => st.work r col) i = false := by simp [firstBit, hci]
            simp [st', echelonStep, restrictKernelStep, hfi, hci, hiz]
        have hpNotMem : p ∉ Finset.univ.filter (fun i : Fin nrows => st.work i = vecZero ncols) := by
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          intro hz
          have := congrFun hz col
          change c p = false at this
          rw [hcp] at this; cases this
        have hcardZ : (Finset.univ.filter (fun i : Fin nrows => st.work i = vecZero ncols)).card + 1 ≤
            (Finset.univ.filter (fun i : Fin nrows => st'.work i = vecZero ncols)).card := by
          rw [← Finset.card_insert_of_notMem hpNotMem]
          exact Finset.card_le_card hsubZ
        have := hprev.rank_le_zeros
        omega
      · have haf : anyBit c = false := Bool.eq_false_iff.mpr ha
        have hcf : ∀ i, c i = false := fun i => by
          cases hci : c i
          · rfl
          · exfalso; exact ha ((anyBit_eq_true c).mpr ⟨i, hci⟩)
        have hhasP_eq : st'.hasP = st.hasP := by
          funext j
          by_cases hjc : j = col
          · dsimp only [c] at haf
            subst hjc; simp [st', echelonStep, haf, (hprev.piv_zero_ge col (le_refl t)).1]
          · simp [st', echelonStep, hjc]
        have hwork_eq : st'.work = st.work := by
          funext i
          have hci : st.work i col = false := hcf i
          have hfi : firstBit (fun r => st.work r col) i = false := by simp [firstBit, hci]
          simp [st', echelonStep, restrictKernelStep, hfi, hci]
        rw [hhasP_eq, hwork_eq]
        exact hprev.rank_le_zeros
    exact ⟨hwork_lt, hpiv_ge, hpiv_tri, hspan, hrank⟩

lemma echelon_inSpan {nrows ncols : Nat} (M : Fin nrows → Vec ncols) (v : Vec ncols) :
    inSpan (echelon M).piv v ↔ inSpan M v := by
  rw [echelon_eq_prefix]
  have hinv := echelonPrefix_inv M ncols (le_refl ncols)
  rw [← hinv.span_eq v]
  have hwork0 : ∀ i, (echelonPrefix M ncols).work i = vecZero ncols := by
    intro i; funext j; exact hinv.work_zero_lt i j j.isLt
  constructor
  · intro hv; exact ⟨v, vecZero ncols, hv, inSpan_zero _, (vecXor_zero v).symm⟩
  · rintro ⟨w1, w2, hw1, ⟨a, rfl⟩, rfl⟩
    have hw2 : vecLinComb (echelonPrefix M ncols).work a = vecZero ncols := by
      funext j; simp [vecLinComb, vecDot_eq_bxor, hwork0, vecZero]
      exact bxorFinset_zero (fun _ _ => rfl)
    rw [hw2, vecXor_zero]; exact hw1

lemma echelon_tri {nrows ncols : Nat} (M : Fin nrows → Vec ncols) (j : Fin ncols) :
    (∀ j' : Fin ncols, j'.val < j.val → (echelon M).piv j j' = false) ∧
    ((echelon M).hasP j = true → (echelon M).piv j j = true) ∧
    ((echelon M).hasP j = false → (echelon M).piv j = vecZero ncols) := by
  rw [echelon_eq_prefix]
  exact (echelonPrefix_inv M ncols (le_refl ncols)).piv_tri j

lemma echelon_rank_le {nrows ncols : Nat} (M : Fin nrows → Vec ncols) :
    (Finset.univ.filter (fun j : Fin ncols => (echelon M).hasP j = true)).card ≤ nrows := by
  rw [echelon_eq_prefix]
  have hinv := echelonPrefix_inv M ncols (le_refl ncols)
  exact hinv.rank_le_zeros.trans ((Finset.card_filter_le _ _).trans (by simp))

lemma tri_linComb_zero_imp {ncols : Nat} {hasP : Fin ncols → Bool} {piv : Fin ncols → Vec ncols}
    (htri : ∀ j : Fin ncols,
      (∀ j' : Fin ncols, j'.val < j.val → piv j j' = false) ∧
      (hasP j = true → piv j j = true) ∧
      (hasP j = false → piv j = vecZero ncols))
    {a : Vec ncols} (hsupp : ∀ j : Fin ncols, hasP j = false → a j = false)
    (hzero : vecLinComb piv a = vecZero ncols) : a = vecZero ncols := by
  funext j
  change a j = false
  have hstrong : ∀ m : Nat, ∀ j : Fin ncols, j.val < m → a j = false := by
    intro m
    induction m with
    | zero => intro j hj; omega
    | succ m ih =>
      intro j hj
      by_cases hlt : j.val < m
      · exact ih j hlt
      · have hjeq : j.val = m := by omega
        cases hp : hasP j
        · exact hsupp j hp
        · have hbit := congrFun hzero j
          simp only [vecLinComb, vecDot_eq_bxor, vecZero] at hbit
          have hsp : (Finset.univ : Finset (Fin ncols)) = insert j (Finset.univ.erase j) :=
            (Finset.insert_erase (Finset.mem_univ j)).symm
          rw [hsp, bxorFinset_insert (Finset.notMem_erase _ _)] at hbit
          have hrest : bxorFinset (Finset.univ.erase j) (fun i => a i && piv i j) = false := by
            apply bxorFinset_zero
            intro i hi
            have hne : i ≠ j := (Finset.mem_erase.mp hi).1
            rcases Nat.lt_or_gt_of_ne (fun h => hne (Fin.ext h)) with hlti | hgti
            · rw [ih i (by omega), Bool.false_and]
            · rw [(htri i).1 j hgti, Bool.and_false]
          rw [hrest, (htri j).2.1 hp, Bool.and_true, Bool.xor_false] at hbit
          exact hbit
  exact hstrong ncols j j.isLt

lemma tri_linComb_inj {ncols : Nat} {hasP : Fin ncols → Bool} {piv : Fin ncols → Vec ncols}
    (htri : ∀ j : Fin ncols,
      (∀ j' : Fin ncols, j'.val < j.val → piv j j' = false) ∧
      (hasP j = true → piv j j = true) ∧
      (hasP j = false → piv j = vecZero ncols))
    {a1 a2 : Vec ncols}
    (h1 : ∀ j, hasP j = false → a1 j = false)
    (h2 : ∀ j, hasP j = false → a2 j = false)
    (heq : vecLinComb piv a1 = vecLinComb piv a2) : a1 = a2 := by
  have h0 : vecLinComb piv (vecXor a1 a2) = vecZero ncols := by
    rw [vecLinComb_xor, heq, vecXor_self]
  have hs : ∀ j, hasP j = false → vecXor a1 a2 j = false := by
    intro j hj; simp [vecXor, h1 j hj, h2 j hj]
  have hx := tri_linComb_zero_imp htri hs h0
  funext j
  have := congrFun hx j
  simp only [vecXor, vecZero] at this
  cases ha1 : a1 j <;> cases ha2 : a2 j <;> simp_all

lemma echelon_card_span {nrows ncols : Nat} (M : Fin nrows → Vec ncols) :
    Nat.card { v : Vec ncols // inSpan M v } =
      2 ^ (Finset.univ.filter (fun j : Fin ncols => (echelon M).hasP j = true)).card := by
  classical
  let st := echelon M
  let Pset := Finset.univ.filter (fun j : Fin ncols => st.hasP j = true)
  rw [Nat.card_eq_fintype_card]
  have hbij : Fintype.card { v : Vec ncols // inSpan M v } = Fintype.card (Pset → Bool) := by
    symm
    apply Fintype.card_of_bijective (f := fun (g : Pset → Bool) =>
      ⟨vecLinComb st.piv (fun j => if h : j ∈ Pset then g ⟨j, h⟩ else false),
       (echelon_inSpan M _).mp ⟨_, rfl⟩⟩)
    constructor
    · intro g1 g2 heq
      have hval := congrArg Subtype.val heq
      dsimp only at hval
      have hveq := tri_linComb_inj (echelon_tri M)
        (fun j hj => by
          have hn : j ∉ Pset := by
            simp only [Pset, st, Finset.mem_filter, Finset.mem_univ, true_and, hj, Bool.false_eq_true, not_false_eq_true]
          simp [hn])
        (fun j hj => by
          have hn : j ∉ Pset := by
            simp only [Pset, st, Finset.mem_filter, Finset.mem_univ, true_and, hj, Bool.false_eq_true, not_false_eq_true]
          simp [hn])
        hval
      funext ⟨j, hj⟩
      have := congrFun hveq j
      simpa [hj] using this
    · rintro ⟨v, hv⟩
      obtain ⟨a, rfl⟩ := (echelon_inSpan M v).mpr hv
      refine ⟨fun ⟨j, _⟩ => a j, Subtype.ext ?_⟩
      dsimp only
      funext k
      simp only [vecLinComb, vecDot_eq_bxor]
      apply bxorFinset_congr
      intro j _
      by_cases hj : j ∈ Pset
      · simp only [hj, ↓reduceDIte]; rfl
      · have hpf : st.hasP j = false := by
          simp only [Pset, Finset.mem_filter, Finset.mem_univ, true_and] at hj
          exact Bool.eq_false_iff.mpr hj
        simp only [hj, ↓reduceDIte, Bool.false_and]
        rw [(echelon_tri M j).2.2 hpf]; simp [vecZero]
  rw [hbij, Fintype.card_fun, Fintype.card_bool, Fintype.card_coe]

-- Echelon reduction for membership test
def echelonReducePrefix {ncols : Nat} (hasP : Fin ncols → Bool) (piv : Fin ncols → Vec ncols)
    (z : Vec ncols) (t : Nat) : Vec ncols :=
  ((List.finRange ncols).take t).foldl
    (fun rem j => if rem j && hasP j then vecXor rem (piv j) else rem) z

def echelonReduce {ncols : Nat} (hasP : Fin ncols → Bool) (piv : Fin ncols → Vec ncols)
    (z : Vec ncols) : Vec ncols :=
  (List.finRange ncols).foldl
    (fun rem j => if rem j && hasP j then vecXor rem (piv j) else rem) z

lemma echelonReduce_eq_zero_iff {nrows ncols : Nat} (M : Fin nrows → Vec ncols) (z : Vec ncols) :
    echelonReduce (echelon M).hasP (echelon M).piv z = vecZero ncols ↔ inSpan M z := by
  let st := echelon M
  have htri : ∀ j : Fin ncols,
      (∀ j' : Fin ncols, j'.val < j.val → st.piv j j' = false) ∧
      (st.hasP j = true → st.piv j j = true) ∧
      (st.hasP j = false → st.piv j = vecZero ncols) := echelon_tri M
  have hinv : ∀ t ≤ ncols,
      inSpan st.piv (vecXor (echelonReducePrefix st.hasP st.piv z t) z) ∧
      ∀ j : Fin ncols, j.val < t → st.hasP j = true →
        echelonReducePrefix st.hasP st.piv z t j = false := by
    intro t ht
    induction t with
    | zero =>
      refine ⟨by simp [echelonReducePrefix, vecXor_self, inSpan_zero], fun _ hj => by omega⟩
    | succ t ih =>
      have ht' : t < ncols := by omega
      obtain ⟨hsp, hzl⟩ := ih (by omega)
      have htake : (List.finRange ncols).take (t + 1) = (List.finRange ncols).take t ++ [⟨t, ht'⟩] := by
        rw [List.take_add_one, List.getElem?_eq_getElem (by simp [ht'])]
        simp [List.getElem_finRange]
      have hstep : echelonReducePrefix st.hasP st.piv z (t + 1) =
          let rem := echelonReducePrefix st.hasP st.piv z t
          if rem ⟨t, ht'⟩ && st.hasP ⟨t, ht'⟩ then vecXor rem (st.piv ⟨t, ht'⟩) else rem := by
        unfold echelonReducePrefix; rw [htake, List.foldl_append]; rfl
      rw [hstep]
      set rem := echelonReducePrefix st.hasP st.piv z t
      set j0 : Fin ncols := ⟨t, ht'⟩
      dsimp only
      by_cases hcond : (rem j0 && st.hasP j0) = true
      · rw [if_pos hcond]
        obtain ⟨hrem, hp0⟩ := (Bool.and_eq_true _ _).mp hcond
        refine ⟨?_, fun j hj hpj => ?_⟩
        · have heq : vecXor (vecXor rem (st.piv j0)) z = vecXor (vecXor rem z) (st.piv j0) := by
            rw [vecXor_assoc, vecXor_comm (st.piv j0) z, ← vecXor_assoc]
          rw [heq]
          exact inSpan_xor hsp (inSpan_row st.piv j0)
        · by_cases hlt : j.val < t
          · simp only [vecXor, hzl j hlt hpj, (htri j0).1 j hlt]; rfl
          · have hjeq : j = j0 := Fin.ext (show j.val = t by omega)
            rw [hjeq]
            simp only [vecXor, hrem, (htri j0).2.1 hp0]; rfl
      · rw [if_neg hcond]
        refine ⟨hsp, fun j hj hpj => ?_⟩
        by_cases hlt : j.val < t
        · exact hzl j hlt hpj
        · have hjeq : j = j0 := Fin.ext (show j.val = t by omega)
          rw [hjeq] at hpj ⊢
          cases hr : rem j0
          · rfl
          · exfalso; apply hcond; simp [hr, hpj]
  have hfull : echelonReduce st.hasP st.piv z = echelonReducePrefix st.hasP st.piv z ncols := by
    simp [echelonReduce, echelonReducePrefix, List.take_of_length_le]
  rw [hfull]
  obtain ⟨hsp, hzl⟩ := hinv ncols (le_refl ncols)
  rw [← echelon_inSpan M z]
  set rem := echelonReducePrefix st.hasP st.piv z ncols
  constructor
  · intro h0
    rw [h0, zero_vecXor] at hsp; exact hsp
  · intro hz
    have hrem_in : inSpan st.piv rem := by
      have : rem = vecXor (vecXor rem z) z := by rw [vecXor_assoc, vecXor_self, vecXor_zero]
      rw [this]; exact inSpan_xor hsp hz
    obtain ⟨a, ha⟩ := hrem_in
    let a' : Vec ncols := fun j => if st.hasP j then a j else false
    have ha' : rem = vecLinComb st.piv a' := by
      rw [ha]; funext k; simp only [vecLinComb, vecDot_eq_bxor]
      apply bxorFinset_congr
      intro j _
      cases hp : st.hasP j
      · simp only [a', hp, Bool.false_eq_true, ↓reduceIte, Bool.false_and]
        rw [(htri j).2.2 hp]; simp [vecZero]
      · simp [a', hp]
    have ha'0 : a' = vecZero ncols := by
      funext j
      change a' j = false
      have hstr : ∀ m : Nat, ∀ j : Fin ncols, j.val < m → a' j = false := by
        intro m
        induction m with
        | zero => intro j hj; omega
        | succ m ih =>
          intro j hj
          by_cases hlt : j.val < m
          · exact ih j hlt
          · have hjeq : j.val = m := by omega
            cases hp : st.hasP j
            · simp [a', hp]
            · have hremj := hzl j j.isLt hp
              rw [ha'] at hremj
              simp only [vecLinComb, vecDot_eq_bxor] at hremj
              have hspj : (Finset.univ : Finset (Fin ncols)) = insert j (Finset.univ.erase j) :=
                (Finset.insert_erase (Finset.mem_univ j)).symm
              rw [hspj, bxorFinset_insert (Finset.notMem_erase _ _)] at hremj
              have hrest : bxorFinset (Finset.univ.erase j) (fun i => a' i && st.piv i j) = false := by
                apply bxorFinset_zero
                intro i hi
                have hne : i ≠ j := (Finset.mem_erase.mp hi).1
                rcases Nat.lt_or_gt_of_ne (fun h => hne (Fin.ext h)) with hlti | hgti
                · rw [ih i (by omega), Bool.false_and]
                · rw [(echelon_tri M i).1 j hgti, Bool.and_false]
              rw [hrest, (echelon_tri M j).2.1 hp, Bool.and_true, Bool.xor_false] at hremj
              exact hremj
      exact hstr ncols j j.isLt
    rw [ha', ha'0, vecLinComb_zero]

-- Unary running counter for pivot / complementary indexing
def cntAt {n : Nat} (p : Fin n → Bool) (c : Nat) : Nat :=
  (Finset.univ.filter (fun i : Fin n => i.val < c ∧ p i = true)).card

def cntEq {n : Nat} (p : Fin n → Bool) (c v : Nat) : Bool :=
  decide (cntAt p c = v)

lemma cntAt_zero {n : Nat} (p : Fin n → Bool) : cntAt p 0 = 0 := by
  simp [cntAt]

lemma cntAt_succ {n : Nat} (p : Fin n → Bool) {c : Nat} (hc : c < n) :
    cntAt p (c + 1) = cntAt p c + if p ⟨c, hc⟩ then 1 else 0 := by
  unfold cntAt
  cases hp : p ⟨c, hc⟩
  · simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_zero]
    congr 1; ext i; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨hlt, hpi⟩
      refine ⟨?_, hpi⟩
      by_cases he : i.val = c
      · have : i = ⟨c, hc⟩ := Fin.ext he; subst this; rw [hp] at hpi; cases hpi
      · omega
    · rintro ⟨hlt, hpi⟩; exact ⟨by omega, hpi⟩
  · simp only [↓reduceIte]
    have hset : Finset.univ.filter (fun i : Fin n => i.val < c + 1 ∧ p i = true) =
        insert ⟨c, hc⟩ (Finset.univ.filter (fun i : Fin n => i.val < c ∧ p i = true)) := by
      ext i; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
      constructor
      · rintro ⟨hlt, hpi⟩
        by_cases he : i.val = c
        · exact Or.inl (Fin.ext he)
        · exact Or.inr ⟨by omega, hpi⟩
      · rintro (rfl | ⟨hlt, hpi⟩)
        · exact ⟨Nat.lt_succ_self c, hp⟩
        · exact ⟨by omega, hpi⟩
    have hnot : (⟨c, hc⟩ : Fin n) ∉ Finset.univ.filter (fun i : Fin n => i.val < c ∧ p i = true) := by
      simp
    rw [hset, Finset.card_insert_of_notMem hnot]

lemma cntAt_full {n : Nat} (p : Fin n → Bool) :
    cntAt p n = (Finset.univ.filter (fun i : Fin n => p i = true)).card := by
  unfold cntAt; congr 1; ext i; simp [i.isLt]

lemma cntAt_mono {n : Nat} (p : Fin n → Bool) {c1 c2 : Nat} (h : c1 ≤ c2) :
    cntAt p c1 ≤ cntAt p c2 := by
  unfold cntAt
  apply Finset.card_le_card
  intro i hi
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
  exact ⟨by omega, hi.2⟩

lemma cntAt_le {n : Nat} (p : Fin n → Bool) (c : Nat) : cntAt p c ≤ n := by
  unfold cntAt; exact (Finset.card_filter_le _ _).trans (by simp)

lemma cntEq_zero {n : Nat} (p : Fin n → Bool) (v : Nat) :
    cntEq p 0 v = decide (v = 0) := by
  simp [cntEq, cntAt_zero, eq_comm]

lemma cntEq_succ_zero {n : Nat} (p : Fin n → Bool) {c : Nat} (hc : c < n) :
    cntEq p (c + 1) 0 = (cntEq p c 0 && !(p ⟨c, hc⟩)) := by
  simp only [cntEq, cntAt_succ p hc]
  cases p ⟨c, hc⟩ <;> simp

lemma cntEq_succ_succ {n : Nat} (p : Fin n → Bool) {c : Nat} (hc : c < n) (v : Nat) :
    cntEq p (c + 1) (v + 1) =
      ((cntEq p c (v + 1) && !(p ⟨c, hc⟩)) || (cntEq p c v && p ⟨c, hc⟩)) := by
  simp only [cntEq, cntAt_succ p hc]
  cases p ⟨c, hc⟩ <;> simp

lemma exists_unique_cntAt {n : Nat} (p : Fin n → Bool) {r : Nat} (hr : r < cntAt p n) :
    ∃! i : Fin n, p i = true ∧ cntAt p i.val = r := by
  classical
  have hex : ∃ c : Nat, c < n ∧ r < cntAt p (c + 1) := by
    by_contra hall; push_neg at hall
    have hle : ∀ c ≤ n, cntAt p c ≤ r := by
      intro c hc
      cases c with
      | zero => rw [cntAt_zero]; omega
      | succ c => exact hall c (by omega)
    have := hle n (le_refl n); omega
  let c0 := Nat.find hex
  have hc0 := Nat.find_spec hex
  have hc0_lt : c0 < n := hc0.1
  have hc0_r : r < cntAt p (c0 + 1) := hc0.2
  have hprev : cntAt p c0 ≤ r := by
    cases hc : c0 with
    | zero => rw [cntAt_zero]; omega
    | succ m =>
      have hmin := Nat.find_min hex (show m < c0 by omega)
      push_neg at hmin
      exact hmin (by omega)
  have hsucc := cntAt_succ p hc0_lt
  have hpc0 : p ⟨c0, hc0_lt⟩ = true := by
    cases hp : p ⟨c0, hc0_lt⟩
    · rw [hp] at hsucc; simp at hsucc; omega
    · rfl
  have hcnt : cntAt p c0 = r := by
    rw [hpc0] at hsucc; simp at hsucc; omega
  refine ⟨⟨c0, hc0_lt⟩, ⟨hpc0, hcnt⟩, ?_⟩
  rintro i ⟨hpi, hci⟩
  apply Fin.ext
  dsimp only
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
  · have h1 := cntAt_succ p i.isLt
    rw [hpi] at h1; simp at h1
    have h2 := cntAt_mono p (show i.val + 1 ≤ c0 by omega)
    omega
  · have h1 := cntAt_succ p hc0_lt
    rw [hpc0] at h1; simp at h1
    have h2 := cntAt_mono p (show c0 + 1 ≤ i.val by omega)
    omega

-- Basis completion and complementary seed construction

-- Butterfly shift on b-bit truth tables
def shiftLayer {b : Nat} (t : Nat) (ht : t < b) (bit : Bool) (T : Fin (2 ^ b) → Bool)
    (α : Fin (2 ^ b)) : Bool :=
  if bit then
    T ⟨α.val ^^^ (1 <<< t), xor_lt α.isLt
      (by rw [Nat.shiftLeft_eq, Nat.one_mul]; exact Nat.pow_lt_pow_right (by omega) ht)⟩
  else T α

def shiftTablePrefix {b : Nat} (δ : Fin (2 ^ b)) (T : Fin (2 ^ b) → Bool) (r : Nat) :
    Fin (2 ^ b) → Bool :=
  ((List.finRange b).take r).foldl (fun cur t => shiftLayer t.val t.isLt (δ.val.testBit t.val) cur) T

def shiftTable {b : Nat} (δ : Fin (2 ^ b)) (T : Fin (2 ^ b) → Bool) : Fin (2 ^ b) → Bool :=
  (List.finRange b).foldl (fun cur t => shiftLayer t.val t.isLt (δ.val.testBit t.val) cur) T

lemma shiftTable_eq {b : Nat} (δ : Fin (2 ^ b)) (T : Fin (2 ^ b) → Bool) (α : Fin (2 ^ b)) :
    shiftTable δ T α = T ⟨α.val ^^^ δ.val, xor_lt α.isLt δ.isLt⟩ := by
  have hinv : ∀ (r : Nat) (hr : r ≤ b) (α : Fin (2 ^ b)),
      shiftTablePrefix δ T r α =
        T ⟨α.val ^^^ (δ.val % 2 ^ r), xor_lt α.isLt
          ((Nat.mod_lt _ (Nat.two_pow_pos r)).trans_le (Nat.pow_le_pow_right Nat.zero_lt_two hr))⟩ := by
    intro r hr
    induction r with
    | zero =>
      intro α; simp [shiftTablePrefix, Nat.mod_one, Nat.xor_zero]
    | succ r ih =>
      intro α
      have hr' : r < b := by omega
      have htake : (List.finRange b).take (r + 1) = (List.finRange b).take r ++ [⟨r, hr'⟩] := by
        rw [List.take_add_one, List.getElem?_eq_getElem (by simp [hr'])]
        simp [List.getElem_finRange]
      have hstep : shiftTablePrefix δ T (r + 1) α =
          shiftLayer r hr' (δ.val.testBit r) (shiftTablePrefix δ T r) α := by
        unfold shiftTablePrefix; rw [htake, List.foldl_append]; rfl
      rw [hstep]
      unfold shiftLayer
      cases hb : δ.val.testBit r
      · simp only [Bool.false_eq_true, ↓reduceIte]
        rw [ih (by omega) α]
        congr 1; apply Fin.ext; dsimp only; congr 1
        apply Nat.eq_of_testBit_eq; intro i
        rw [Nat.testBit_mod_two_pow, Nat.testBit_mod_two_pow]
        by_cases hi : i < r
        · simp [hi, show i < r + 1 by omega]
        · by_cases hieq : i = r
          · subst hieq; simp [hb]
          · simp [show ¬(i < r) by omega, show ¬(i < r + 1) by omega]
      · simp only [↓reduceIte]
        rw [ih (by omega)]
        congr 1; apply Fin.ext; dsimp only
        rw [Nat.xor_assoc]
        congr 1
        apply Nat.eq_of_testBit_eq; intro i
        rw [Nat.testBit_xor, Nat.shiftLeft_eq, Nat.one_mul, Nat.testBit_two_pow,
            Nat.testBit_mod_two_pow, Nat.testBit_mod_two_pow]
        by_cases hi : i < r
        · simp [hi, show i < r + 1 by omega, show r ≠ i by omega]
        · by_cases hieq : i = r
          · subst hieq; simp [hb]
          · simp [show ¬(i < r) by omega, show ¬(i < r + 1) by omega, show r ≠ i by omega]
  have hfull : shiftTable δ T α = shiftTablePrefix δ T b α := by
    simp [shiftTable, shiftTablePrefix, List.take_of_length_le]
  rw [hfull, hinv b (le_refl b) α]
  congr 1; apply Fin.ext; dsimp only
  rw [Nat.mod_eq_of_lt δ.isLt]

def derivTable {b : Nat} (ψ : Fin (2 ^ b) → Bool) (δ : Fin (2 ^ b)) : Fin (2 ^ b) → Bool :=
  fmt (fun α => xor (shiftTable δ ψ α) (ψ α))


lemma fmt_scale_bool {b : Nat} (c : Bool) (T : Fin (2 ^ b) → Bool) (S : Fin (2 ^ b)) :
    fmt (fun x => c && T x) S = (c && fmt T S) := by
  cases c
  · simp only [Bool.false_and]
    have h0 : fmt (fun _ : Fin (2 ^ b) => false) = fun _ => false := by
      unfold fmt
      have hgen : ∀ (l : List (Fin b)),
          l.foldl (fun cur t => fmtLayer t.val t.isLt cur) (fun _ => false) = fun _ => false := by
        intro l; induction l with
        | nil => rfl
        | cons t l ih =>
          simp only [List.foldl_cons]
          have : fmtLayer t.val t.isLt (fun _ => false) = fun _ => false := by
            funext x; unfold fmtLayer; split_ifs <;> rfl
          rw [this, ih]
      exact hgen _
    exact congrFun h0 S
  · simp only [Bool.true_and]


lemma mod_two_pow_succ (x t : Nat) :
    x % 2 ^ (t + 1) = x % 2 ^ t + (x.testBit t).toNat * 2 ^ t := by
  have hdiv : x = x % 2 ^ t + 2 ^ t * (x / 2 ^ t) := (Nat.mod_add_div x (2 ^ t)).symm
  have h2 : (x.testBit t).toNat = (x / 2 ^ t) % 2 := by
    rw [Nat.testBit, Nat.shiftRight_eq_div_pow]
    rcases Nat.mod_two_eq_zero_or_one (x / 2 ^ t) with h | h <;> simp [Nat.and_one_is_mod, h]
  have h3 : x % (2 ^ t * 2) = x % 2 ^ t + 2 ^ t * ((x / 2 ^ t) % 2) := by
    have hd := Nat.mod_add_div (x / 2 ^ t) 2
    have hlt : x % 2 ^ t + 2 ^ t * ((x / 2 ^ t) % 2) < 2 ^ t * 2 := by
      have hm1 := Nat.mod_lt x (Nat.two_pow_pos t)
      rcases Nat.mod_two_eq_zero_or_one (x / 2 ^ t) with h | h <;> rw [h] <;> omega
    have heq : x = (x % 2 ^ t + 2 ^ t * ((x / 2 ^ t) % 2)) + (2 ^ t * 2) * ((x / 2 ^ t) / 2) := by
      calc x = x % 2 ^ t + 2 ^ t * (x / 2 ^ t) := hdiv
        _ = x % 2 ^ t + 2 ^ t * ((x / 2 ^ t) % 2 + 2 * ((x / 2 ^ t) / 2)) := by rw [hd]
        _ = (x % 2 ^ t + 2 ^ t * ((x / 2 ^ t) % 2)) + (2 ^ t * 2) * ((x / 2 ^ t) / 2) := by ring
    conv_lhs => rw [heq]
    rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlt]
  rw [pow_succ, h3, h2, mul_comm]

def incCarry {w : Nat} (a : Vec w) (b : Bool) : Nat → Bool
  | 0 => b
  | i + 1 => if h : i < w then a ⟨i, h⟩ && incCarry a b i else false

def incBits {w : Nat} (a : Vec w) (b : Bool) : Vec w :=
  fun i => xor (a i) (incCarry a b i.val)

lemma ofVec_incBits_mod {w : Nat} (a : Vec w) (b : Bool) (t : Nat) (ht : t ≤ w) :
    (ofVec w (incBits a b)).val % 2 ^ t + (incCarry a b t).toNat * 2 ^ t =
      (ofVec w a).val % 2 ^ t + b.toNat := by
  induction t with
  | zero => simp [incCarry, Nat.mod_one]
  | succ t ih =>
    have hlt : t < w := by omega
    rw [mod_two_pow_succ, mod_two_pow_succ, testBit_ofVec, testBit_ofVec]
    simp only [hlt, ↓reduceDIte]
    have hinc : incBits a b ⟨t, hlt⟩ = xor (a ⟨t, hlt⟩) (incCarry a b t) := rfl
    have hcar : incCarry a b (t + 1) = (a ⟨t, hlt⟩ && incCarry a b t) := by simp [incCarry, hlt]
    rw [hinc, hcar]
    have hih := ih (by omega)
    have hpow : 2 ^ (t + 1) = 2 * 2 ^ t := by rw [pow_succ, mul_comm]
    cases ha : a ⟨t, hlt⟩ <;> cases hc : incCarry a b t <;>
      simp only [hc, hpow, Bool.false_xor, Bool.true_xor, Bool.not_false, Bool.not_true,
        Bool.false_and, Bool.true_and, Bool.toNat_false, Bool.toNat_true,
        zero_mul, one_mul, add_zero] at hih ⊢ <;> omega

lemma ofVec_incBits {w : Nat} (a : Vec w) (b : Bool)
    (hlt : (ofVec w a).val + b.toNat < 2 ^ w) :
    (ofVec w (incBits a b)).val = (ofVec w a).val + b.toNat := by
  have h := ofVec_incBits_mod a b w (le_refl w)
  rw [Nat.mod_eq_of_lt (ofVec w (incBits a b)).isLt, Nat.mod_eq_of_lt (ofVec w a).isLt] at h
  cases hc : incCarry a b w
  · simp [hc] at h; exact h
  · simp [hc] at h; omega

def countBits {α : Type} (w : Nat) (l : List α) (p : α → Bool) : Vec w :=
  l.foldl (fun acc x => incBits acc (p x)) (vecZero w)

lemma ofVec_countBits_foldl {α : Type} {w : Nat} (l : List α) (p : α → Bool) (acc : Vec w)
    (hlt : (ofVec w acc).val + l.length < 2 ^ w) :
    (ofVec w (l.foldl (fun c x => incBits c (p x)) acc)).val =
      (ofVec w acc).val + (l.filter p).length := by
  induction l generalizing acc with
  | nil => simp
  | cons a l ih =>
    simp only [List.foldl_cons, List.filter_cons, List.length_cons] at hlt ⊢
    have h1 : (ofVec w acc).val + (p a).toNat < 2 ^ w := by
      cases p a <;> simp <;> omega
    have hinc := ofVec_incBits acc (p a) h1
    have h2 : (ofVec w (incBits acc (p a))).val + l.length < 2 ^ w := by
      rw [hinc]; cases p a <;> simp <;> omega
    rw [ih (incBits acc (p a)) h2, hinc]
    cases p a <;> simp <;> omega

lemma ofVec_countBits_finRange {n w : Nat} (p : Fin n → Bool) (hn : n < 2 ^ w) :
    (ofVec w (countBits w (List.finRange n) p)).val =
      (Finset.univ.filter (fun i : Fin n => p i = true)).card := by
  unfold countBits
  have h1 := ofVec_countBits_foldl (List.finRange n) p (vecZero w) (by simp [ofVec_zero, hn])
  rw [ofVec_zero] at h1
  dsimp only at h1
  rw [Nat.zero_add] at h1
  rw [h1, ← List.toFinset_card_of_nodup ((List.nodup_finRange n).filter p)]
  congr 1; ext i; simp

def shiftByRank {m : Nat} (hasP : Fin m → Bool) (q w : Nat) (pc : Vec w) : Vec w :=
  fun i => (List.finRange (q + 1)).foldl
    (fun acc ρ => acc || (cntEq hasP m ρ.val &&
      if h : q - ρ.val ≤ i.val then pc ⟨i.val - (q - ρ.val), by omega⟩ else false)) false

lemma ofVec_shiftByRank {m q w : Nat} (hasP : Fin m → Bool) (pc : Vec w)
    (hρ : cntAt hasP m ≤ q)
    (hlt : (ofVec w pc).val * 2 ^ (q - cntAt hasP m) < 2 ^ w) :
    (ofVec w (shiftByRank hasP q w pc)).val = (ofVec w pc).val * 2 ^ (q - cntAt hasP m) := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [testBit_ofVec]
  by_cases hi : i < w
  · simp only [hi, ↓reduceDIte, shiftByRank]
    rw [← Nat.shiftLeft_eq, Nat.testBit_shiftLeft]
    have hiff : (List.finRange (q + 1)).foldl
        (fun acc ρ => acc || (cntEq hasP m ρ.val &&
          if h : q - ρ.val ≤ i then pc ⟨i - (q - ρ.val), by omega⟩ else false)) false = true ↔
        (decide (q - cntAt hasP m ≤ i) && (ofVec w pc).val.testBit (i - (q - cntAt hasP m))) = true := by
      rw [foldl_or_eq_true]
      simp only [Bool.false_eq_true, false_or, List.mem_finRange, true_and, Bool.and_eq_true,
        cntEq, decide_eq_true_eq]
      constructor
      · rintro ⟨ρ, hreq, hpc⟩
        rw [hreq]
        by_cases hle : q - ρ.val ≤ i
        · simp only [hle, ↓reduceDIte] at hpc
          refine ⟨hle, ?_⟩
          rw [testBit_ofVec]
          simp [show i - (q - ρ.val) < w by omega, hpc]
        · simp [hle] at hpc
      · rintro ⟨hle, htb⟩
        refine ⟨⟨cntAt hasP m, by omega⟩, rfl, ?_⟩
        simp only [hle, ↓reduceDIte]
        rw [testBit_ofVec] at htb
        simpa [show i - (q - cntAt hasP m) < w by omega] using htb
    cases hL : (List.finRange (q + 1)).foldl
        (fun acc ρ => acc || (cntEq hasP m ρ.val &&
          if h : q - ρ.val ≤ i then pc ⟨i - (q - ρ.val), by omega⟩ else false)) false <;>
      cases hR : (decide (q - cntAt hasP m ≤ i) && (ofVec w pc).val.testBit (i - (q - cntAt hasP m)))
    · rfl
    · exact absurd (hiff.mpr hR) (by rw [hL]; exact Bool.false_ne_true)
    · exact absurd (hiff.mp hL) (by rw [hR]; exact Bool.false_ne_true)
    · rfl
  · simp only [hi, ↓reduceDIte]
    symm
    exact Nat.testBit_lt_two_pow (hlt.trans_le (Nat.pow_le_pow_right Nat.zero_lt_two (by omega)))

def leVecPrefix {w : Nat} (a b : Vec w) (t : Nat) : Bool :=
  ((List.finRange w).take t).foldl (fun acc i => (!(a i) && b i) || ((a i == b i) && acc)) true

def leVec {w : Nat} (a b : Vec w) : Bool :=
  (List.finRange w).foldl (fun acc i => (!(a i) && b i) || ((a i == b i) && acc)) true

lemma leVec_eq_decide {w : Nat} (a b : Vec w) :
    leVec a b = decide ((ofVec w a).val ≤ (ofVec w b).val) := by
  have hinv : ∀ t ≤ w, leVecPrefix a b t = decide ((ofVec w a).val % 2 ^ t ≤ (ofVec w b).val % 2 ^ t) := by
    intro t ht
    induction t with
    | zero => simp [leVecPrefix, Nat.mod_one]
    | succ t ih =>
      have hlt : t < w := by omega
      have htake : (List.finRange w).take (t + 1) = (List.finRange w).take t ++ [⟨t, hlt⟩] := by
        rw [List.take_add_one, List.getElem?_eq_getElem (by simp [hlt])]
        simp [List.getElem_finRange]
      have hstep : leVecPrefix a b (t + 1) =
          ((!(a ⟨t, hlt⟩) && b ⟨t, hlt⟩) || ((a ⟨t, hlt⟩ == b ⟨t, hlt⟩) && leVecPrefix a b t)) := by
        unfold leVecPrefix; rw [htake, List.foldl_append]; rfl
      rw [hstep, ih (by omega), mod_two_pow_succ, mod_two_pow_succ, testBit_ofVec, testBit_ofVec]
      simp only [hlt, ↓reduceDIte]
      have ha_lt : (ofVec w a).val % 2 ^ t < 2 ^ t := Nat.mod_lt _ (Nat.two_pow_pos t)
      have hb_lt : (ofVec w b).val % 2 ^ t < 2 ^ t := Nat.mod_lt _ (Nat.two_pow_pos t)
      cases a ⟨t, hlt⟩ <;> cases b ⟨t, hlt⟩
      · simp
      · simp only [Bool.not_false, Bool.true_and, Bool.true_or, Bool.toNat_false, Bool.toNat_true,
          zero_mul, one_mul, add_zero]
        symm; exact decide_eq_true (by omega)
      · simp only [Bool.not_true, Bool.false_and, Bool.false_or, Bool.toNat_true, Bool.toNat_false,
          one_mul, zero_mul, add_zero]
        change false = decide _
        symm; exact decide_eq_false (by omega)
      · simp [Nat.add_le_add_iff_right]
  have hfull : leVec a b = leVecPrefix a b w := by
    simp [leVec, leVecPrefix, List.take_of_length_le]
  rw [hfull, hinv w (le_refl w), Nat.mod_eq_of_lt (ofVec w a).isLt, Nat.mod_eq_of_lt (ofVec w b).isLt]

lemma not_anyBit_eq_decide {m : Nat} (z : Vec m) :
    (!anyBit z) = decide (z = vecZero m) := by
  cases h : anyBit z
  · symm; apply decide_eq_true
    funext i
    cases hzi : z i
    · rfl
    · have := (anyBit_eq_true z).mpr ⟨i, hzi⟩; rw [h] at this; cases this
  · symm; apply decide_eq_false
    intro hz
    obtain ⟨i, hi⟩ := (anyBit_eq_true z).mp h
    have := congrFun hz i
    rw [hi] at this; cases this

def dimGe {k : Nat} (hasP : Fin k → Bool) (q : Nat) : Bool :=
  (List.range (k + 1 - q)).foldl (fun acc d => acc || cntEq hasP k (q + d)) false

lemma dimGe_eq_decide {k q : Nat} (hasP : Fin k → Bool) (hqk : q ≤ k) :
    dimGe hasP q = decide (q ≤ cntAt hasP k) := by
  have hiff : dimGe hasP q = true ↔ q ≤ cntAt hasP k := by
    unfold dimGe
    rw [foldl_or_eq_true]
    simp only [Bool.false_eq_true, false_or, List.mem_range, cntEq, decide_eq_true_eq]
    constructor
    · rintro ⟨d, _, hd⟩; omega
    · intro hle
      have hcnt_le := cntAt_le hasP k
      exact ⟨cntAt hasP k - q, by omega, by omega⟩
  cases hd : dimGe hasP q
  · symm; rw [decide_eq_false_iff_not]; intro h; exact Bool.false_ne_true (hd ▸ hiff.mpr h)
  · symm; rw [decide_eq_true_eq]; exact hiff.mp hd


-- ============================================================
-- PART S: Locality through injective site maps
-- ============================================================

def extractS {k b : Nat} (s : Fin b → Fin k) (w : Nat) : Fin (2 ^ b) :=
  ofVec b (fun j => w.testBit (s j).val)

def embedS {k b : Nat} (s : Fin b → Fin k) (α : Nat) : Fin (2 ^ k) :=
  ofVec k (fun l => decide (∃ j : Fin b, s j = l ∧ α.testBit j.val = true))

def siteMask {k b : Nat} (s : Fin b → Fin k) : Nat :=
  (ofVec k (fun l => decide (∃ j : Fin b, s j = l))).val

lemma testBit_extractS {k b : Nat} (s : Fin b → Fin k) (w t : Nat) :
    (extractS s w).val.testBit t = if h : t < b then w.testBit (s ⟨t, h⟩).val else false := by
  unfold extractS; rw [testBit_ofVec]

lemma testBit_embedS_site {k b : Nat} {s : Fin b → Fin k} (hs : Function.Injective s)
    (α : Nat) (j : Fin b) : (embedS s α).val.testBit (s j).val = α.testBit j.val := by
  unfold embedS; rw [testBit_ofVec]
  simp only [(s j).isLt, ↓reduceDIte]
  cases h : α.testBit j.val
  · apply decide_eq_false
    rintro ⟨j', hj', hb⟩
    have hjj : j' = j := hs (by rw [hj'])
    subst hjj; rw [h] at hb; cases hb
  · exact decide_eq_true ⟨j, rfl, h⟩

lemma testBit_embedS_true {k b : Nat} {s : Fin b → Fin k} {α q : Nat}
    (h : (embedS s α).val.testBit q = true) :
    ∃ hq : q < k, ∃ j : Fin b, s j = ⟨q, hq⟩ ∧ α.testBit j.val = true := by
  unfold embedS at h; rw [testBit_ofVec] at h
  by_cases hq : q < k
  · simp only [hq, ↓reduceDIte, decide_eq_true_eq] at h
    exact ⟨hq, h⟩
  · simp [hq] at h

lemma extract_embedS {k b : Nat} {s : Fin b → Fin k} (hs : Function.Injective s)
    (S : Fin (2 ^ b)) : extractS s (embedS s S.val).val = S := by
  apply Fin.ext; apply Nat.eq_of_testBit_eq; intro t
  rw [testBit_extractS]
  by_cases ht : t < b
  · simp only [ht, ↓reduceDIte]; exact testBit_embedS_site hs S.val ⟨t, ht⟩
  · simp only [ht, ↓reduceDIte]; symm
    exact Nat.testBit_lt_two_pow (S.isLt.trans_le (Nat.pow_le_pow_right (by omega) (by omega)))

lemma submask_siteMask_iff {k b : Nat} {s : Fin b → Fin k} (hs : Function.Injective s)
    (T : Fin (2 ^ k)) :
    submask T.val (siteMask s) = true ↔ embedS s (extractS s T.val).val = T := by
  rw [submask_iff]
  constructor
  · intro hsub
    apply Fin.ext; apply Nat.eq_of_testBit_eq; intro q
    by_cases hq : q < k
    · unfold embedS; rw [testBit_ofVec]
      simp only [hq, ↓reduceDIte]
      cases hT : T.val.testBit q
      · apply decide_eq_false
        rintro ⟨j, hj, hb⟩
        rw [testBit_extractS] at hb
        simp only [j.isLt, ↓reduceDIte] at hb
        have hjq : (s j).val = q := by rw [hj]
        rw [hjq, hT] at hb; cases hb
      · have hm := hsub q hT
        unfold siteMask at hm; rw [testBit_ofVec] at hm
        simp only [hq, ↓reduceDIte, decide_eq_true_eq] at hm
        obtain ⟨j, hj⟩ := hm
        apply decide_eq_true
        refine ⟨j, hj, ?_⟩
        rw [testBit_extractS]
        simp only [j.isLt, ↓reduceDIte]
        have hjq : (s j).val = q := by rw [hj]
        rw [hjq, hT]
    · rw [Nat.testBit_lt_two_pow ((embedS s _).isLt.trans_le (Nat.pow_le_pow_right (by omega) (by omega))),
        Nat.testBit_lt_two_pow (T.isLt.trans_le (Nat.pow_le_pow_right (by omega) (by omega)))]
  · intro heq q hTq
    rw [← heq] at hTq
    obtain ⟨hq, j, hj, _⟩ := testBit_embedS_true hTq
    unfold siteMask; rw [testBit_ofVec]
    simp only [hq, ↓reduceDIte, decide_eq_true_eq]
    exact ⟨j, hj⟩

lemma submask_embedS_iff {k b : Nat} {s : Fin b → Fin k} (hs : Function.Injective s)
    {S : Nat} (hS : S < 2 ^ b) (w : Nat) :
    submask (embedS s S).val w = true ↔ submask S (extractS s w).val = true := by
  rw [submask_iff, submask_iff]
  constructor
  · intro h t ht
    have htb : t < b := by
      by_contra hge
      have := Nat.testBit_lt_two_pow (hS.trans_le (Nat.pow_le_pow_right (by omega) (by omega : b ≤ t)))
      rw [this] at ht; cases ht
    rw [testBit_extractS]
    simp only [htb, ↓reduceDIte]
    apply h
    rw [testBit_embedS_site hs]; exact ht
  · intro h q hq
    obtain ⟨hqk, j, hj, hSj⟩ := testBit_embedS_true hq
    have hw := h j.val hSj
    rw [testBit_extractS] at hw
    simp only [j.isLt, ↓reduceDIte] at hw
    have hjq : (s j).val = q := by rw [hj]
    rw [hjq] at hw; exact hw

lemma popcount_embedS {k b : Nat} {s : Fin b → Fin k} (hs : Function.Injective s)
    (S : Fin (2 ^ b)) : popcount k (embedS s S.val).val = popcount b S.val := by
  rw [popcount_eq_card, popcount_eq_card]
  symm
  apply Finset.card_bij (fun t _ => s t)
  · intro t ht
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ht ⊢
    rw [testBit_embedS_site hs]; exact ht
  · intro t1 _ t2 _ heq; exact hs heq
  · intro q hq
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hq
    obtain ⟨_, j, hj, hSj⟩ := testBit_embedS_true hq
    refine ⟨j, ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact hSj
    · rw [hj]

lemma popcount_siteMask_le {k b : Nat} (s : Fin b → Fin k) : popcount k (siteMask s) ≤ b := by
  rw [popcount_eq_card]
  have hsub : Finset.univ.filter (fun l : Fin k => (siteMask s).testBit l.val = true) ⊆
      Finset.univ.image s := by
    intro l hl
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image] at hl ⊢
    unfold siteMask at hl; rw [testBit_ofVec] at hl
    simp only [l.isLt, ↓reduceDIte, decide_eq_true_eq] at hl
    obtain ⟨j, hj⟩ := hl
    exact ⟨j, by rw [hj]⟩
  exact (Finset.card_le_card hsub).trans (Finset.card_image_le.trans (by simp))

lemma extractS_xor {k b : Nat} (s : Fin b → Fin k) (w1 w2 : Nat) :
    extractS s (w1 ^^^ w2) =
      ⟨(extractS s w1).val ^^^ (extractS s w2).val,
        xor_lt (extractS s w1).isLt (extractS s w2).isLt⟩ := by
  apply Fin.ext; apply Nat.eq_of_testBit_eq; intro t
  dsimp only
  rw [Nat.testBit_xor, testBit_extractS, testBit_extractS, testBit_extractS]
  by_cases ht : t < b
  · simp only [ht, ↓reduceDIte, Nat.testBit_xor]
  · simp only [ht, ↓reduceDIte]; rfl

lemma fmt_localS {k b : Nat} {s : Fin b → Fin k} (hs : Function.Injective s)
    (ψ : Fin (2 ^ b) → Bool) (T : Fin (2 ^ k)) :
    fmt (fun w : Fin (2 ^ k) => ψ (extractS s w.val)) T =
      if submask T.val (siteMask s) then fmt ψ (extractS s T.val) else false := by
  let c : Fin (2 ^ k) → Bool := fun U =>
    if submask U.val (siteMask s) then fmt ψ (extractS s U.val) else false
  suffices h : fmt c = fun w : Fin (2 ^ k) => ψ (extractS s w.val) by
    have := congrArg fmt h
    rw [fmt_invol] at this
    exact (congrFun this T).symm
  funext w
  rw [fmt_eq_submaskSum]
  have h1 : ψ (extractS s w.val) = fmt (fmt ψ) (extractS s w.val) := by rw [fmt_invol]
  rw [h1, fmt_eq_submaskSum]
  have hfilt :
      bxorFinset (Finset.univ.filter (fun U : Fin (2 ^ k) => submask U.val w.val = true)) c =
      bxorFinset (Finset.univ.filter (fun U : Fin (2 ^ k) =>
        submask U.val w.val = true ∧ submask U.val (siteMask s) = true))
        (fun U => fmt ψ (extractS s U.val)) := by
    have hsplit : Finset.univ.filter (fun U : Fin (2 ^ k) =>
        submask U.val w.val = true ∧ submask U.val (siteMask s) = true) =
      (Finset.univ.filter (fun U : Fin (2 ^ k) => submask U.val w.val = true)).filter
        (fun U => submask U.val (siteMask s) = true) := by
      ext U; simp
    symm
    rw [hsplit, bxorFinset_filter_eq]
    apply bxorFinset_congr
    intro U _
    unfold c
    cases hsm : submask U.val (siteMask s) <;> simp [hsm]
  rw [hfilt]
  symm
  apply bxorFinset_bij _ _ _ _ (fun S _ => embedS s S.val)
  · intro S hS
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hS ⊢
    refine ⟨(submask_embedS_iff hs S.isLt w.val).mpr hS, ?_⟩
    rw [submask_siteMask_iff hs, extract_embedS hs S]
  · intro S1 _ S2 _ heq
    have h2 := congrArg (fun x : Fin (2 ^ k) => extractS s x.val) heq
    simp only [extract_embedS hs] at h2
    exact h2
  · intro U hU
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hU
    refine ⟨extractS s U.val, ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      have hemb := (submask_siteMask_iff hs U).mp hU.2
      rw [← submask_embedS_iff hs (extractS s U.val).isLt, hemb]
      exact hU.1
    · exact (submask_siteMask_iff hs U).mp hU.2
  · intro S _
    rw [extract_embedS hs S]

-- ============================================================
-- PART F: The XOR of local tables and its derivative coefficients
-- ============================================================

def fF {k m p b : Nat} (sites : Fin p → Fin b → Fin k)
    (Tt : Fin p → Fin (2 ^ b) → Fin m → Bool) (w : Fin (2 ^ k)) (j : Fin m) : Bool :=
  bxorFinset Finset.univ (fun i : Fin p => Tt i (extractS (sites i) w.val) j)

lemma fmt_fF {k m p b : Nat} {sites : Fin p → Fin b → Fin k}
    (hinj : ∀ i, Function.Injective (sites i))
    (Tt : Fin p → Fin (2 ^ b) → Fin m → Bool) (j : Fin m) (T : Fin (2 ^ k)) :
    fmt (fun w => fF sites Tt w j) T = bxorFinset Finset.univ (fun i : Fin p =>
      if submask T.val (siteMask (sites i)) then
        fmt (fun α => Tt i α j) (extractS (sites i) T.val) else false) := by
  unfold fF
  rw [fmt_bxorFinset]
  apply bxorFinset_congr; intro i _
  exact fmt_localS (hinj i) (fun α => Tt i α j) T

lemma degLe_fF {k m p b : Nat} {sites : Fin p → Fin b → Fin k}
    (hinj : ∀ i, Function.Injective (sites i))
    (Tt : Fin p → Fin (2 ^ b) → Fin m → Bool) (j : Fin m) :
    degLe (fun w => fF sites Tt w j) b := by
  intro T hT
  rw [fmt_fF hinj]
  apply bxorFinset_zero; intro i _
  have hno : submask T.val (siteMask (sites i)) = false := by
    cases hsm : submask T.val (siteMask (sites i))
    · rfl
    · exfalso
      have h1 := popcount_submask_le (k := k) hsm
      have h2 := popcount_siteMask_le (sites i)
      omega
  simp [hno]

lemma subV_topS {k m p b : Nat} {sites : Fin p → Fin b → Fin k}
    (hinj : ∀ i, Function.Injective (sites i))
    (Tt : Fin p → Fin (2 ^ b) → Fin m → Bool) (d : Fin (2 ^ k)) :
    subV (fF sites Tt) b d := by
  intro j
  exact degLe_xor (degLe_shift (degLe_fF hinj Tt j) d) (degLe_fF hinj Tt j)

def dFE {k m p b : Nat} (sites : Fin p → Fin b → Fin k)
    (Tt : Fin p → Fin (2 ^ b) → Fin m → Bool) (dir : Vec k) (j : Fin m) (T : Fin (2 ^ k)) : Bool :=
  (List.finRange p).foldl (fun acc i => xor acc
    (if submask T.val (siteMask (sites i)) then
      derivTable (fun α => Tt i α j) (extractS (sites i) (ofVec k dir).val)
        (extractS (sites i) T.val)
    else false)) false

lemma fmt_deriv_dFE {k m p b : Nat} {sites : Fin p → Fin b → Fin k}
    (hinj : ∀ i, Function.Injective (sites i))
    (Tt : Fin p → Fin (2 ^ b) → Fin m → Bool) (dir : Vec k) (j : Fin m) (T : Fin (2 ^ k)) :
    fmt (deriv (fF sites Tt) (ofVec k dir) j) T = dFE sites Tt dir j T := by
  have hfun : deriv (fF sites Tt) (ofVec k dir) j =
      fun w => bxorFinset Finset.univ (fun i : Fin p =>
        (fun α => xor (shiftTable (extractS (sites i) (ofVec k dir).val) (fun α => Tt i α j) α)
          (Tt i α j)) (extractS (sites i) w.val)) := by
    funext w
    unfold deriv fF
    rw [← bxorFinset_xor]
    apply bxorFinset_congr; intro i _
    dsimp only
    rw [shiftTable_eq, extractS_xor]
  rw [hfun, fmt_bxorFinset]
  unfold dFE
  rw [bxorFinset_finRange]
  apply bxorFinset_congr; intro i _
  exact fmt_localS (hinj i) (fun α => xor (shiftTable (extractS (sites i) (ofVec k dir).val)
    (fun α => Tt i α j) α) (Tt i α j)) T

-- ============================================================
-- PART L: Descending chain of linear-structure subspaces
-- ============================================================

def levelEqs (p b m s : Nat) : List (Fin m × Fin p × Fin (2 ^ b)) :=
  (List.finRange m).flatMap fun j =>
    (List.finRange p).flatMap fun i =>
      ((List.finRange (2 ^ b)).filter fun α => decide (popcount b α.val = s)).map fun α =>
        (j, i, α)

lemma mem_levelEqs {p b m s : Nat} (j : Fin m) (i : Fin p) (α : Fin (2 ^ b)) :
    (j, i, α) ∈ levelEqs p b m s ↔ popcount b α.val = s := by
  simp [levelEqs]

def subVLevelEq {k m p b : Nat} (sites : Fin p → Fin b → Fin k)
    (Tt : Fin p → Fin (2 ^ b) → Fin m → Bool)
    (V : Fin k → Vec k) (U : Fin k → Vec k)
    (eq : Fin m × Fin p × Fin (2 ^ b)) : Fin k → Vec k :=
  let T : Fin (2 ^ k) := embedS (sites eq.2.1) eq.2.2.val
  let col : Vec k := fun idx => dFE sites Tt (V idx) eq.1 T
  let c : Vec k := fun row => vecDot (U row) col
  restrictKernelStep U c

def subVLevel {k m p b : Nat} (sites : Fin p → Fin b → Fin k)
    (Tt : Fin p → Fin (2 ^ b) → Fin m → Bool)
    (s : Nat) (V : Fin k → Vec k) : Fin k → Vec k :=
  let U := (levelEqs p b m s).foldl (subVLevelEq sites Tt V) (stdBasis k)
  fun row => vecLinComb V (U row)

def subVChain {k m p b : Nat} (sites : Fin p → Fin b → Fin k)
    (Tt : Fin p → Fin (2 ^ b) → Fin m → Bool) : Fin k → Vec k :=
  ((List.range b).reverse.map (· + 1)).foldl
    (fun V s => subVLevel sites Tt s V) (stdBasis k)

lemma subVLevel_correct {k m p b : Nat} {sites : Fin p → Fin b → Fin k}
    (hinj : ∀ i, Function.Injective (sites i))
    (Tt : Fin p → Fin (2 ^ b) → Fin m → Bool)
    {s : Nat} (hs : 1 ≤ s) {V : Fin k → Vec k}
    (hV : ∀ v : Vec k, inSpan V v ↔ subV (fF sites Tt) s (ofVec k v)) :
    ∀ v : Vec k, inSpan (subVLevel sites Tt s V) v ↔
      subV (fF sites Tt) (s - 1) (ofVec k v) := by
  let f := fF sites Tt
  have hlin : ∀ (j : Fin m) (T : Fin (2 ^ k)), popcount k T.val = s →
      ∀ (a : Vec k),
        fmt (deriv f (ofVec k (vecLinComb V a)) j) T =
          vecDot a (fun idx => dFE sites Tt (V idx) j T) := by
    intro j T hTs a
    have hgen : ∀ (S : Finset (Fin k)),
        fmt (deriv f (ofVec k (fun c => bxorFinset S (fun idx => a idx && V idx c))) j) T =
          bxorFinset S (fun idx => a idx && dFE sites Tt (V idx) j T) := by
      intro S
      induction S using Finset.induction with
      | empty =>
        have hz : (fun c : Fin k => bxorFinset (∅ : Finset (Fin k)) (fun idx => a idx && V idx c)) = vecZero k := by
          funext c; simp [bxorFinset, vecZero]
        rw [hz, ofVec_zero, bxorFinset_empty]
        exact subV_zero f 0 j T (by omega)
      | insert idx S hidx ih =>
        have hv1 : (fun c : Fin k => bxorFinset (insert idx S) (fun i => a i && V i c)) =
            vecXor (fun c => a idx && V idx c) (fun c => bxorFinset S (fun i => a i && V i c)) := by
          funext c; exact bxorFinset_insert hidx _
        rw [hv1, ofVec_xor, bxorFinset_insert hidx]
        have h1_in : subV f s (ofVec k (fun c => a idx && V idx c)) := by
          cases ha : a idx
          · have : (fun c : Fin k => false && V idx c) = vecZero k := by funext c; rfl
            rw [this, ofVec_zero]; exact subV_zero f s
          · have : (fun c : Fin k => true && V idx c) = V idx := by funext c; rfl
            rw [this]; exact (hV (V idx)).mp (inSpan_row V idx)
        rw [fmt_deriv_xor_top h1_in j hTs, ih]
        congr 1
        cases ha : a idx
        · have : (fun c : Fin k => false && V idx c) = vecZero k := by funext c; rfl
          rw [this, ofVec_zero, Bool.false_and]
          exact subV_zero f 0 j T (by omega)
        · have : (fun c : Fin k => true && V idx c) = V idx := by funext c; rfl
          rw [this, Bool.true_and]
          exact fmt_deriv_dFE hinj Tt (V idx) j T
    have hlc : vecLinComb V a = fun c => bxorFinset Finset.univ (fun idx => a idx && V idx c) := by
      funext c; exact vecDot_eq_bxor _ _
    rw [hlc, vecDot_eq_bxor]
    exact hgen Finset.univ
  have hfold : ∀ (eqs : List (Fin m × Fin p × Fin (2 ^ b))) (U0 : Fin k → Vec k),
      (∀ eq ∈ eqs, popcount b eq.2.2.val = s) →
      ∀ a : Vec k,
        inSpan (eqs.foldl (subVLevelEq sites Tt V) U0) a ↔
          inSpan U0 a ∧ ∀ eq ∈ eqs,
            fmt (deriv f (ofVec k (vecLinComb V a)) eq.1)
              (embedS (sites eq.2.1) eq.2.2.val) = false := by
    intro eqs
    induction eqs with
    | nil => intro U0 _ a; simp
    | cons eq eqs ih =>
      intro U0 heqs a
      simp only [List.foldl_cons]
      rw [ih _ (fun e he => heqs e (List.mem_cons_of_mem _ he))]
      rcases eq with ⟨j, i, α⟩
      have hpc : popcount b α.val = s := heqs (j, i, α) List.mem_cons_self
      have hTs : popcount k (embedS (sites i) α.val).val = s := by
        rw [popcount_embedS (hinj i) α]; exact hpc
      set T : Fin (2 ^ k) := embedS (sites i) α.val
      set col : Vec k := fun idx => dFE sites Tt (V idx) j T
      have hstep_iff : inSpan (subVLevelEq sites Tt V U0 (j, i, α)) a ↔
          inSpan U0 a ∧ fmt (deriv f (ofVec k (vecLinComb V a)) j) T = false := by
        unfold subVLevelEq
        dsimp only
        rw [inSpan_restrictKernelStep]
        constructor
        · rintro ⟨coef, rfl, hdot⟩
          refine ⟨⟨coef, rfl⟩, ?_⟩
          rw [hlin j T hTs]
          have hadd := additive_vecLinComb (fun x => vecDot x col)
            (vecDot_zero_left col) (fun u1 u2 => vecDot_xor_left u1 u2 col) U0 coef
          rw [hadd]; exact hdot
        · rintro ⟨⟨coef, rfl⟩, hfmt⟩
          refine ⟨coef, rfl, ?_⟩
          rw [hlin j T hTs] at hfmt
          have hadd := additive_vecLinComb (fun x => vecDot x col)
            (vecDot_zero_left col) (fun u1 u2 => vecDot_xor_left u1 u2 col) U0 coef
          rwa [hadd] at hfmt
      rw [hstep_iff]
      simp only [List.mem_cons, forall_eq_or_imp, and_assoc]
      rfl
  intro v
  unfold subVLevel
  dsimp only
  rw [inSpan_comp]
  have heqs_pc : ∀ eq ∈ levelEqs p b m s, popcount b eq.2.2.val = s := by
    rintro ⟨j, i, α⟩ hmem; exact (mem_levelEqs j i α).mp hmem
  constructor
  · rintro ⟨a, haU, rfl⟩
    have hfa := (hfold (levelEqs p b m s) (stdBasis k) heqs_pc a).mp haU
    have hVs : subV f s (ofVec k (vecLinComb V a)) := (hV _).mp ⟨a, rfl⟩
    intro j T hT
    by_cases hgt : s < popcount k T.val
    · exact hVs j T hgt
    · have hTeq : popcount k T.val = s := by omega
      by_cases hexp : ∃ i : Fin p, submask T.val (siteMask (sites i)) = true
      · obtain ⟨i, hi⟩ := hexp
        set α : Fin (2 ^ b) := extractS (sites i) T.val
        have hTemb : embedS (sites i) α.val = T := (submask_siteMask_iff (hinj i) T).mp hi
        have hαpc : popcount b α.val = s := by
          have := popcount_embedS (hinj i) α
          rw [hTemb, hTeq] at this; exact this.symm
        have hmem : (j, i, α) ∈ levelEqs p b m s := (mem_levelEqs j i α).mpr hαpc
        have hres := hfa.2 (j, i, α) hmem
        simpa only [hTemb] using hres
      · simp only [not_exists] at hexp
        have hno : ∀ i : Fin p, submask T.val (siteMask (sites i)) = false :=
          fun i => Bool.eq_false_iff.mpr (hexp i)
        rw [fmt_deriv_dFE hinj]
        unfold dFE
        rw [bxorFinset_finRange]
        apply bxorFinset_zero; intro i _
        simp [hno i]
  · intro hv
    have hVs : subV f s (ofVec k v) := fun j T hT => hv j T (by omega)
    obtain ⟨a, rfl⟩ := (hV v).mpr hVs
    refine ⟨a, ?_, rfl⟩
    rw [hfold (levelEqs p b m s) (stdBasis k) heqs_pc a]
    refine ⟨inSpan_stdBasis a, ?_⟩
    rintro ⟨j, i, α⟩ hmem
    have hpc : popcount b α.val = s := (mem_levelEqs j i α).mp hmem
    have hTs : popcount k (embedS (sites i) α.val).val = s := by
      rw [popcount_embedS (hinj i) α]; exact hpc
    exact hv j (embedS (sites i) α.val) (by omega)

lemma inSpan_subVChain {k m p b : Nat} {sites : Fin p → Fin b → Fin k}
    (hinj : ∀ i, Function.Injective (sites i))
    (Tt : Fin p → Fin (2 ^ b) → Fin m → Bool) (v : Vec k) :
    inSpan (subVChain sites Tt) v ↔ subV (fF sites Tt) 0 (ofVec k v) := by
  have hgen : ∀ (t : Nat) (V : Fin k → Vec k),
      (∀ v : Vec k, inSpan V v ↔ subV (fF sites Tt) t (ofVec k v)) →
      ∀ v : Vec k,
        inSpan (((List.range t).reverse.map (· + 1)).foldl
          (fun W s => subVLevel sites Tt s W) V) v ↔
        subV (fF sites Tt) 0 (ofVec k v) := by
    intro t
    induction t with
    | zero => intro V hV v; simpa using hV v
    | succ t ih =>
      intro V hV v
      have hlist : ((List.range (t + 1)).reverse.map (· + 1)) =
          (t + 1) :: ((List.range t).reverse.map (· + 1)) := by
        rw [List.range_succ, List.reverse_append, List.reverse_singleton,
            List.singleton_append, List.map_cons]
      rw [hlist, List.foldl_cons]
      exact ih _ (subVLevel_correct hinj Tt (by omega) hV) v
  unfold subVChain
  exact hgen b (stdBasis k)
    (fun w => ⟨fun _ => subV_topS hinj Tt _, fun _ => inSpan_stdBasis w⟩) v

-- ============================================================
-- PART P: Pins, consistency and counting
-- ============================================================

lemma fmt_at_zero {k : Nat} (g : Fin (2 ^ k) → Bool) :
    fmt g ⟨0, Nat.two_pow_pos k⟩ = g ⟨0, Nat.two_pow_pos k⟩ := by
  rw [fmt_eq_submaskSum]
  have hset : Finset.univ.filter (fun x : Fin (2 ^ k) =>
      submask x.val (⟨0, Nat.two_pow_pos k⟩ : Fin (2 ^ k)).val = true) =
      {⟨0, Nat.two_pow_pos k⟩} := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · intro h
      apply Fin.ext; apply Nat.eq_of_testBit_eq; intro i
      have h2 := submask_iff.mp h i
      cases hx : x.val.testBit i
      · simp
      · have h3 := h2 hx; simp at h3
    · rintro rfl; exact submask_iff.mpr (fun i h => by simp at h)
  rw [hset]
  simp [bxorFinset]

lemma dFE_zero_eq {k m p b : Nat} {sites : Fin p → Fin b → Fin k}
    (hinj : ∀ i, Function.Injective (sites i))
    (Tt : Fin p → Fin (2 ^ b) → Fin m → Bool) (dir : Vec k) (j : Fin m) :
    dFE sites Tt dir j ⟨0, Nat.two_pow_pos k⟩ =
      deriv (fF sites Tt) (ofVec k dir) j ⟨0, Nat.two_pow_pos k⟩ := by
  rw [← fmt_deriv_dFE hinj, fmt_at_zero]

lemma deriv_const_of_subV {k m : Nat} {f : Fin (2 ^ k) → Fin m → Bool} {d : Fin (2 ^ k)}
    (h : subV f 0 d) (j : Fin m) (w : Fin (2 ^ k)) :
    deriv f d j w = deriv f d j ⟨0, Nat.two_pow_pos k⟩ := by
  obtain ⟨a, ha⟩ := (degLe_zero_iff_const _).mp (h j)
  rw [ha w, ha]

lemma deriv_zero_xor {k m : Nat} {f : Fin (2 ^ k) → Fin m → Bool} {d1 d2 : Fin (2 ^ k)}
    (h1 : subV f 0 d1) (j : Fin m) :
    deriv f ⟨d1.val ^^^ d2.val, xor_lt d1.isLt d2.isLt⟩ j ⟨0, Nat.two_pow_pos k⟩ =
      xor (deriv f d1 j ⟨0, Nat.two_pow_pos k⟩) (deriv f d2 j ⟨0, Nat.two_pow_pos k⟩) := by
  rw [deriv_xor, deriv_const_of_subV h1 j]

lemma additive_on_span {m n : Nat} (P : Vec n → Prop) (hP0 : P (vecZero n))
    (hPx : ∀ u v, P u → P v → P (vecXor u v))
    (L : Vec n → Bool) (h0 : L (vecZero n) = false)
    (hadd : ∀ u v, P u → P v → L (vecXor u v) = xor (L u) (L v))
    (M : Fin m → Vec n) (hM : ∀ i, P (M i)) (a : Vec m) :
    P (vecLinComb M a) ∧ L (vecLinComb M a) = vecDot a (fun i => L (M i)) := by
  have hterm : ∀ x : Fin m, P (fun j => a x && M x j) ∧
      L (fun j => a x && M x j) = (a x && L (M x)) := by
    intro x
    cases a x
    · have h1 : (fun j : Fin n => false && M x j) = vecZero n := by funext j; rfl
      rw [h1]; exact ⟨hP0, h0⟩
    · have h1 : (fun j : Fin n => true && M x j) = M x := by funext j; rfl
      rw [h1]; exact ⟨hM x, rfl⟩
  have hgen : ∀ (s : Finset (Fin m)),
      P (fun j => bxorFinset s (fun i => a i && M i j)) ∧
      L (fun j => bxorFinset s (fun i => a i && M i j)) =
        bxorFinset s (fun i => a i && L (M i)) := by
    intro s
    induction s using Finset.induction with
    | empty =>
      have h1 : (fun j : Fin n => bxorFinset (∅ : Finset (Fin m)) (fun i => a i && M i j)) =
          vecZero n := by
        funext j; simp [bxorFinset, vecZero]
      rw [h1, bxorFinset_empty]; exact ⟨hP0, h0⟩
    | insert x s hx ih =>
      have hfn : (fun j : Fin n => bxorFinset (insert x s) (fun i => a i && M i j)) =
          vecXor (fun j => a x && M x j) (fun j => bxorFinset s (fun i => a i && M i j)) := by
        funext j; exact bxorFinset_insert hx _
      rw [hfn, bxorFinset_insert hx]
      obtain ⟨hP1, hL1⟩ := hterm x
      exact ⟨hPx _ _ hP1 ih.1, by rw [hadd _ _ hP1 ih.1, hL1, ih.2]⟩
  have hlc : vecLinComb M a = fun j => bxorFinset Finset.univ (fun i => a i && M i j) := by
    funext j; exact vecDot_eq_bxor _ _
  rw [hlc, vecDot_eq_bxor]
  exact hgen Finset.univ

def respV {k m p b : Nat} (sites : Fin p → Fin b → Fin k)
    (Tt : Fin p → Fin (2 ^ b) → Fin m → Bool) (d : Vec k) : Vec m :=
  fun j => dFE sites Tt d j ⟨0, Nat.two_pow_pos k⟩

def phiV {k m p b : Nat} (sites : Fin p → Fin b → Fin k)
    (Tt : Fin p → Fin (2 ^ b) → Fin m → Bool) (pdv : Vec k) (pyv : Vec m) (d : Vec k) :
    Vec (k + m) := fun r =>
  if h : r.val < k then pdv ⟨r.val, h⟩ && d ⟨r.val, h⟩
  else pyv ⟨r.val - k, by have := r.isLt; omega⟩ &&
    respV sites Tt d ⟨r.val - k, by have := r.isLt; omega⟩

def tgtV {k m : Nat} (pdv vdv : Vec k) (pyv vyv : Vec m) : Vec (k + m) := fun r =>
  if h : r.val < k then pdv ⟨r.val, h⟩ && vdv ⟨r.val, h⟩
  else pyv ⟨r.val - k, by have := r.isLt; omega⟩ && vyv ⟨r.val - k, by have := r.isLt; omega⟩

lemma band_xor (a x y : Bool) : (a && xor x y) = xor (a && x) (a && y) := by
  cases a <;> cases x <;> cases y <;> rfl

lemma respV_zero {k m p b : Nat} {sites : Fin p → Fin b → Fin k}
    (hinj : ∀ i, Function.Injective (sites i))
    (Tt : Fin p → Fin (2 ^ b) → Fin m → Bool) :
    respV sites Tt (vecZero k) = vecZero m := by
  funext j
  unfold respV
  rw [dFE_zero_eq hinj, ofVec_zero]
  simp [deriv, vecZero]

lemma respV_xor {k m p b : Nat} {sites : Fin p → Fin b → Fin k}
    (hinj : ∀ i, Function.Injective (sites i))
    (Tt : Fin p → Fin (2 ^ b) → Fin m → Bool) {u : Vec k} (v : Vec k)
    (hu : subV (fF sites Tt) 0 (ofVec k u)) :
    respV sites Tt (vecXor u v) = vecXor (respV sites Tt u) (respV sites Tt v) := by
  funext j
  show dFE sites Tt (vecXor u v) j ⟨0, Nat.two_pow_pos k⟩ =
    xor (dFE sites Tt u j ⟨0, Nat.two_pow_pos k⟩) (dFE sites Tt v j ⟨0, Nat.two_pow_pos k⟩)
  rw [dFE_zero_eq hinj, dFE_zero_eq hinj, dFE_zero_eq hinj, ofVec_xor]
  exact deriv_zero_xor hu j

lemma phiV_zero {k m p b : Nat} {sites : Fin p → Fin b → Fin k}
    (hinj : ∀ i, Function.Injective (sites i))
    (Tt : Fin p → Fin (2 ^ b) → Fin m → Bool) (pdv : Vec k) (pyv : Vec m) :
    phiV sites Tt pdv pyv (vecZero k) = vecZero (k + m) := by
  funext r
  unfold phiV
  rw [respV_zero hinj]
  split_ifs <;> simp [vecZero]

lemma phiV_xor {k m p b : Nat} {sites : Fin p → Fin b → Fin k}
    (hinj : ∀ i, Function.Injective (sites i))
    (Tt : Fin p → Fin (2 ^ b) → Fin m → Bool) (pdv : Vec k) (pyv : Vec m)
    {u : Vec k} (v : Vec k) (hu : subV (fF sites Tt) 0 (ofVec k u)) :
    phiV sites Tt pdv pyv (vecXor u v) =
      vecXor (phiV sites Tt pdv pyv u) (phiV sites Tt pdv pyv v) := by
  funext r
  unfold phiV
  rw [respV_xor hinj Tt v hu]
  unfold vecXor
  by_cases h : r.val < k <;> simp only [h, ↓reduceDIte, band_xor]

lemma phiV_lin {k m p b N : Nat} {sites : Fin p → Fin b → Fin k}
    (hinj : ∀ i, Function.Injective (sites i))
    (Tt : Fin p → Fin (2 ^ b) → Fin m → Bool) (pdv : Vec k) (pyv : Vec m)
    (M : Fin N → Vec k) (hM : ∀ i, subV (fF sites Tt) 0 (ofVec k (M i))) (a : Vec N) :
    subV (fF sites Tt) 0 (ofVec k (vecLinComb M a)) ∧
      phiV sites Tt pdv pyv (vecLinComb M a) =
        vecLinComb (fun i => phiV sites Tt pdv pyv (M i)) a := by
  let P : Vec k → Prop := fun v => subV (fF sites Tt) 0 (ofVec k v)
  have hP0 : P (vecZero k) := by
    show subV (fF sites Tt) 0 (ofVec k (vecZero k)); rw [ofVec_zero]; exact subV_zero _ 0
  have hPx : ∀ u v, P u → P v → P (vecXor u v) := by
    intro u v hu hv
    show subV (fF sites Tt) 0 (ofVec k (vecXor u v)); rw [ofVec_xor]; exact subV_xor hu hv
  refine ⟨(additive_on_span P hP0 hPx (fun _ => false) rfl (fun _ _ _ _ => rfl) M hM a).1, ?_⟩
  funext r
  exact (additive_on_span P hP0 hPx (fun v => phiV sites Tt pdv pyv v r)
    (by rw [phiV_zero hinj]; rfl)
    (fun u v hu _ => by rw [phiV_xor hinj Tt pdv pyv v hu]; rfl) M hM a).2

def kerFold {N n : Nat} (U : Fin N → Vec n) (cols : List (Fin n)) : Fin N → Vec n :=
  cols.foldl (fun U r => restrictKernelStep U (fun i => U i r)) U

lemma inSpan_kerFold {N n : Nat} (cols : List (Fin n)) (U : Fin N → Vec n) (v : Vec n) :
    inSpan (kerFold U cols) v ↔ inSpan U v ∧ ∀ r ∈ cols, v r = false := by
  induction cols generalizing U with
  | nil => simp [kerFold]
  | cons r cols ih =>
    have hk : kerFold U (r :: cols) = kerFold (restrictKernelStep U (fun i => U i r)) cols := rfl
    rw [hk, ih, inSpan_restrictKernelStep]
    constructor
    · rintro ⟨⟨a, rfl, ha⟩, hrest⟩
      refine ⟨⟨a, rfl⟩, ?_⟩
      intro r' hr'
      rcases List.mem_cons.mp hr' with rfl | h
      · exact ha
      · exact hrest r' h
    · rintro ⟨⟨a, rfl⟩, hall⟩
      exact ⟨⟨a, rfl, hall r List.mem_cons_self⟩, fun r' h => hall r' (List.mem_cons_of_mem _ h)⟩

def augV {N k c : Nat} (L : Fin N → Vec c) (V : Fin N → Vec k) : Fin N → Vec (c + k) :=
  fun idx r => if h : r.val < c then L idx ⟨r.val, h⟩
    else V idx ⟨r.val - c, by have := r.isLt; omega⟩

def colsK (c k : Nat) : List (Fin (c + k)) :=
  (List.finRange (c + k)).filter (fun r => decide (r.val < c))

lemma mem_colsK {c k : Nat} (r : Fin (c + k)) : r ∈ colsK c k ↔ r.val < c := by
  simp [colsK]

def embK {c k : Nat} (u : Vec k) : Vec (c + k) := fun r =>
  if h : r.val < c then false else u ⟨r.val - c, by have := r.isLt; omega⟩

def secK {c k : Nat} (v : Vec (c + k)) : Vec k := fun l => v ⟨c + l.val, by omega⟩

lemma secK_embK {c k : Nat} (u : Vec k) : secK (c := c) (embK (c := c) u) = u := by
  funext l
  unfold secK embK
  have h1 : ¬ (c + l.val < c) := by omega
  simp only [h1, ↓reduceDIte]
  congr 1; apply Fin.ext; simp

lemma vecLinComb_augV {N k c : Nat} (L : Fin N → Vec c) (V : Fin N → Vec k) (a : Vec N)
    (r : Fin (c + k)) :
    vecLinComb (augV L V) a r = if h : r.val < c then vecLinComb L a ⟨r.val, h⟩
      else vecLinComb V a ⟨r.val - c, by have := r.isLt; omega⟩ := by
  by_cases h : r.val < c
  · simp only [h, ↓reduceDIte, vecLinComb, augV]
  · simp only [h, ↓reduceDIte, vecLinComb, augV]

lemma inSpan_kerK {k c N : Nat} (L : Fin N → Vec c) (V : Fin N → Vec k)
    (Φ : Vec k → Vec c) (hΦ : ∀ a, Φ (vecLinComb V a) = vecLinComb L a) (v : Vec (c + k)) :
    inSpan (kerFold (augV L V) (colsK c k)) v ↔
      v = embK (secK v) ∧ inSpan V (secK v) ∧ Φ (secK v) = vecZero c := by
  rw [inSpan_kerFold, ]
  constructor
  · rintro ⟨⟨a, rfl⟩, hall⟩
    have hsec : secK (c := c) (vecLinComb (augV L V) a) = vecLinComb V a := by
      funext l
      unfold secK
      rw [vecLinComb_augV]
      have h1 : ¬ (c + l.val < c) := by omega
      simp only [h1, ↓reduceDIte]
      congr 1; apply Fin.ext; simp
    rw [hsec]
    refine ⟨?_, ⟨a, rfl⟩, ?_⟩
    · funext r
      unfold embK
      by_cases h : r.val < c
      · simp only [h, ↓reduceDIte]
        exact hall r ((mem_colsK r).mpr h)
      · simp only [h, ↓reduceDIte]
        rw [vecLinComb_augV]
        simp only [h, ↓reduceDIte]
    · rw [hΦ]
      funext r
      have h0 := hall ⟨r.val, by omega⟩ ((mem_colsK _).mpr r.isLt)
      rw [vecLinComb_augV] at h0
      simp only [r.isLt, ↓reduceDIte] at h0
      exact h0
  · rintro ⟨hv, ⟨a, ha⟩, hz⟩
    rw [ha] at hz
    rw [hΦ] at hz
    have hveq : v = vecLinComb (augV L V) a := by
      rw [hv]
      funext r
      rw [vecLinComb_augV]
      unfold embK
      by_cases h : r.val < c
      · simp only [h, ↓reduceDIte]
        have := congrFun hz ⟨r.val, h⟩
        exact this.symm
      · simp only [h, ↓reduceDIte]
        rw [← ha]
    refine ⟨⟨a, hveq⟩, ?_⟩
    intro r hr
    rw [hv]
    unfold embK
    simp only [(mem_colsK r).mp hr, ↓reduceDIte]

-- ============================================================
-- PART G: The good set, its size and the spec
-- ============================================================

def goodS {k m p b : Nat} (sites : Fin p → Fin b → Fin k)
    (Tt : Fin p → Fin (2 ^ b) → Fin m → Bool) (pd vd : Fin (2 ^ k)) (py vy : Fin (2 ^ m))
    (d : Fin (2 ^ k)) : Prop :=
  (d.val &&& pd.val) = (vd.val &&& pd.val) ∧
  ∃ y : Fin m → Bool, (∀ j, py.val.testBit j.val = true → y j = vy.val.testBit j.val) ∧
    ∀ (w : Fin (2 ^ k)) (j : Fin m), deriv (fF sites Tt) d j w = y j

lemma pin_iff {k : Nat} (d pd vd : Fin (2 ^ k)) :
    (d.val &&& pd.val) = (vd.val &&& pd.val) ↔
      ∀ l : Fin k, (toVec k pd l && toVec k d l) = (toVec k pd l && toVec k vd l) := by
  constructor
  · intro h l
    have h1 := congrArg (fun x => x.testBit l.val) h
    simp only [Nat.testBit_and] at h1
    simp only [toVec]
    rw [Bool.and_comm, h1, Bool.and_comm]
  · intro h
    apply Nat.eq_of_testBit_eq; intro i
    rw [Nat.testBit_and, Nat.testBit_and]
    by_cases hi : i < k
    · have h1 := h ⟨i, hi⟩
      simp only [toVec] at h1
      rw [Bool.and_comm, h1, Bool.and_comm]
    · have h1 : d.val.testBit i = false :=
        Nat.testBit_lt_two_pow (d.isLt.trans_le (Nat.pow_le_pow_right (by omega) (by omega)))
      have h2 : vd.val.testBit i = false :=
        Nat.testBit_lt_two_pow (vd.isLt.trans_le (Nat.pow_le_pow_right (by omega) (by omega)))
      rw [h1, h2]

lemma goodS_iff {k m p b : Nat} {sites : Fin p → Fin b → Fin k}
    (hinj : ∀ i, Function.Injective (sites i))
    (Tt : Fin p → Fin (2 ^ b) → Fin m → Bool) (pd vd : Fin (2 ^ k)) (py vy : Fin (2 ^ m))
    (d : Fin (2 ^ k)) :
    goodS sites Tt pd vd py vy d ↔
      inSpan (subVChain sites Tt) (toVec k d) ∧
      phiV sites Tt (toVec k pd) (toVec m py) (toVec k d) =
        tgtV (toVec k pd) (toVec k vd) (toVec m py) (toVec m vy) := by
  rw [inSpan_subVChain hinj, ofVec_toVec]
  have hresp : ∀ j : Fin m, respV sites Tt (toVec k d) j =
      deriv (fF sites Tt) d j ⟨0, Nat.two_pow_pos k⟩ := by
    intro j; unfold respV; rw [dFE_zero_eq hinj, ofVec_toVec]
  have hphi : phiV sites Tt (toVec k pd) (toVec m py) (toVec k d) =
        tgtV (toVec k pd) (toVec k vd) (toVec m py) (toVec m vy) ↔
      (∀ l : Fin k, (toVec k pd l && toVec k d l) = (toVec k pd l && toVec k vd l)) ∧
      (∀ j : Fin m, (toVec m py j && deriv (fF sites Tt) d j ⟨0, Nat.two_pow_pos k⟩) =
        (toVec m py j && toVec m vy j)) := by
    constructor
    · intro h
      constructor
      · intro l
        have h1 := congrFun h ⟨l.val, by omega⟩
        unfold phiV tgtV at h1
        simp only [l.isLt, ↓reduceDIte] at h1
        exact h1
      · intro j
        have h1 := congrFun h ⟨k + j.val, by omega⟩
        unfold phiV tgtV at h1
        have h2 : ¬ (k + j.val < k) := by omega
        simp only [h2, ↓reduceDIte] at h1
        have h3 : (⟨k + j.val - k, by omega⟩ : Fin m) = j := Fin.ext (by simp)
        rw [h3, hresp] at h1
        exact h1
    · rintro ⟨h1, h2⟩
      funext r
      unfold phiV tgtV
      by_cases hr : r.val < k
      · simp only [hr, ↓reduceDIte]; exact h1 ⟨r.val, hr⟩
      · simp only [hr, ↓reduceDIte]; rw [hresp]; exact h2 _
  rw [hphi]
  unfold goodS
  rw [pin_iff]
  constructor
  · rintro ⟨hp, y, hy, hall⟩
    refine ⟨fun j => (degLe_zero_iff_const _).mpr ⟨y j, fun w => hall w j⟩, hp, ?_⟩
    intro j
    rw [hall]
    cases hpj : toVec m py j
    · rfl
    · simp only [Bool.true_and]; exact hy j hpj
  · rintro ⟨hsub, hp, hy⟩
    refine ⟨hp, fun j => deriv (fF sites Tt) d j ⟨0, Nat.two_pow_pos k⟩, ?_, ?_⟩
    · intro j hj
      have h1 := hy j
      simp only [toVec] at h1
      rw [hj] at h1
      simpa using h1
    · intro w j; exact deriv_const_of_subV hsub j w

def LrowsOf {k m p b : Nat} (sites : Fin p → Fin b → Fin k)
    (Tt : Fin p → Fin (2 ^ b) → Fin m → Bool) (pdv : Vec k) (pyv : Vec m) :
    Fin k → Vec (k + m) :=
  fun idx => phiV sites Tt pdv pyv (subVChain sites Tt idx)

def kerKOf {k m p b : Nat} (sites : Fin p → Fin b → Fin k)
    (Tt : Fin p → Fin (2 ^ b) → Fin m → Bool) (pdv : Vec k) (pyv : Vec m) :
    Fin k → Vec (k + m + k) :=
  kerFold (augV (LrowsOf sites Tt pdv pyv) (subVChain sites Tt)) (colsK (k + m) k)

def consOf {k m p b : Nat} (sites : Fin p → Fin b → Fin k)
    (Tt : Fin p → Fin (2 ^ b) → Fin m → Bool) (pdv vdv : Vec k) (pyv vyv : Vec m) : Bool :=
  !(anyBit (echelonReduce (echelon (LrowsOf sites Tt pdv pyv)).hasP
    (echelon (LrowsOf sites Tt pdv pyv)).piv (tgtV pdv vdv pyv vyv)))

def spec {k m p b : Nat} (sites : Fin p → Fin b → Fin k)
    (Tt : Fin p → Fin (2 ^ b) → Fin m → Bool) (pdv vdv : Vec k) (pyv vyv : Vec m)
    (tv : Vec (k + 1)) : Bool :=
  leVec tv (fun i : Fin (k + 1) => consOf sites Tt pdv vdv pyv vyv &&
    cntEq (echelon (kerKOf sites Tt pdv pyv)).hasP (k + m + k) i.val)

lemma card_goodS {k m p b : Nat} {sites : Fin p → Fin b → Fin k}
    (hinj : ∀ i, Function.Injective (sites i))
    (Tt : Fin p → Fin (2 ^ b) → Fin m → Bool) (pd vd : Fin (2 ^ k)) (py vy : Fin (2 ^ m)) :
    Nat.card {d : Fin (2 ^ k) // goodS sites Tt pd vd py vy d} =
      if consOf sites Tt (toVec k pd) (toVec k vd) (toVec m py) (toVec m vy) then
        2 ^ (Finset.univ.filter (fun j =>
          (echelon (kerKOf sites Tt (toVec k pd) (toVec m py))).hasP j = true)).card
      else 0 := by
  have hV0 : ∀ idx, subV (fF sites Tt) 0 (ofVec k (subVChain sites Tt idx)) := fun idx =>
    (inSpan_subVChain hinj Tt _).mp (inSpan_row _ idx)
  have hΦ : ∀ a, phiV sites Tt (toVec k pd) (toVec m py) (vecLinComb (subVChain sites Tt) a) =
      vecLinComb (LrowsOf sites Tt (toVec k pd) (toVec m py)) a := fun a =>
    (phiV_lin hinj Tt (toVec k pd) (toVec m py) (subVChain sites Tt) hV0 a).2
  have hP : ∀ u, inSpan (subVChain sites Tt) u → subV (fF sites Tt) 0 (ofVec k u) :=
    fun u hu => (inSpan_subVChain hinj Tt u).mp hu
  have hG : Nat.card {d : Fin (2 ^ k) // goodS sites Tt pd vd py vy d} =
      Nat.card {u : Vec k // inSpan (subVChain sites Tt) u ∧
        phiV sites Tt (toVec k pd) (toVec m py) u =
          tgtV (toVec k pd) (toVec k vd) (toVec m py) (toVec m vy)} := by
    apply Nat.card_congr
    exact {
      toFun := fun d => ⟨toVec k d.val, (goodS_iff hinj Tt pd vd py vy d.val).mp d.property⟩
      invFun := fun u => ⟨ofVec k u.val, (goodS_iff hinj Tt pd vd py vy _).mpr
        (by rw [toVec_ofVec]; exact u.property)⟩
      left_inv := fun d => Subtype.ext (ofVec_toVec d.val)
      right_inv := fun u => Subtype.ext (toVec_ofVec u.val) }
  rw [hG]
  have hcons : consOf sites Tt (toVec k pd) (toVec k vd) (toVec m py) (toVec m vy) = true ↔
      inSpan (LrowsOf sites Tt (toVec k pd) (toVec m py))
        (tgtV (toVec k pd) (toVec k vd) (toVec m py) (toVec m vy)) := by
    unfold consOf
    rw [not_anyBit_eq_decide, decide_eq_true_eq, echelonReduce_eq_zero_iff]
  by_cases hc : consOf sites Tt (toVec k pd) (toVec k vd) (toVec m py) (toVec m vy) = true
  · rw [if_pos hc]
    obtain ⟨a0, ha0⟩ := hcons.mp hc
    have hu0 : inSpan (subVChain sites Tt) (vecLinComb (subVChain sites Tt) a0) ∧
        phiV sites Tt (toVec k pd) (toVec m py) (vecLinComb (subVChain sites Tt) a0) =
          tgtV (toVec k pd) (toVec k vd) (toVec m py) (toVec m vy) :=
      ⟨⟨a0, rfl⟩, by rw [hΦ]; exact ha0.symm⟩
    have hS : Nat.card {u : Vec k // inSpan (subVChain sites Tt) u ∧
        phiV sites Tt (toVec k pd) (toVec m py) u =
          tgtV (toVec k pd) (toVec k vd) (toVec m py) (toVec m vy)} =
        Nat.card {u : Vec k // inSpan (subVChain sites Tt) u ∧
          phiV sites Tt (toVec k pd) (toVec m py) u = vecZero (k + m)} := by
      apply Nat.card_congr
      exact {
        toFun := fun u => ⟨vecXor u.val (vecLinComb (subVChain sites Tt) a0),
          inSpan_xor u.property.1 hu0.1, by
            rw [phiV_xor hinj Tt _ _ _ (hP _ u.property.1), u.property.2, hu0.2, vecXor_self]⟩
        invFun := fun u => ⟨vecXor u.val (vecLinComb (subVChain sites Tt) a0),
          inSpan_xor u.property.1 hu0.1, by
            rw [phiV_xor hinj Tt _ _ _ (hP _ u.property.1), u.property.2, hu0.2, zero_vecXor]⟩
        left_inv := fun u => Subtype.ext (by
          show vecXor (vecXor u.val (vecLinComb (subVChain sites Tt) a0))
            (vecLinComb (subVChain sites Tt) a0) = u.val
          rw [vecXor_assoc, vecXor_self, vecXor_zero])
        right_inv := fun u => Subtype.ext (by
          show vecXor (vecXor u.val (vecLinComb (subVChain sites Tt) a0))
            (vecLinComb (subVChain sites Tt) a0) = u.val
          rw [vecXor_assoc, vecXor_self, vecXor_zero]) }
    rw [hS]
    have hiff := fun v => inSpan_kerK (LrowsOf sites Tt (toVec k pd) (toVec m py))
      (subVChain sites Tt) (phiV sites Tt (toVec k pd) (toVec m py)) hΦ v
    have hK : Nat.card {u : Vec k // inSpan (subVChain sites Tt) u ∧
          phiV sites Tt (toVec k pd) (toVec m py) u = vecZero (k + m)} =
        Nat.card {v : Vec (k + m + k) //
          inSpan (kerKOf sites Tt (toVec k pd) (toVec m py)) v} := by
      apply Nat.card_congr
      exact {
        toFun := fun u => ⟨embK u.val, (hiff _).mpr ⟨(by rw [secK_embK]),
          (by rw [secK_embK]; exact u.property.1), (by rw [secK_embK]; exact u.property.2)⟩⟩
        invFun := fun v => ⟨secK v.val, ((hiff v.val).mp v.property).2⟩
        left_inv := fun u => Subtype.ext (secK_embK u.val)
        right_inv := fun v => Subtype.ext (((hiff v.val).mp v.property).1.symm) }
    rw [hK, echelon_card_span]
  · rw [if_neg hc]
    rw [Nat.card_eq_zero]
    left
    constructor
    rintro ⟨u, ⟨a, rfl⟩, hu⟩
    apply hc
    rw [hcons]
    exact ⟨a, by rw [← hΦ]; exact hu.symm⟩

lemma ofVec_onehot {w r : Nat} (hr : r < w) :
    (ofVec w (fun i : Fin w => decide (r = i.val))).val = 2 ^ r := by
  apply Nat.eq_of_testBit_eq; intro i
  rw [testBit_ofVec, Nat.testBit_two_pow]
  by_cases hi : i < w
  · simp only [hi, ↓reduceDIte]
  · simp only [hi, ↓reduceDIte]; symm; apply decide_eq_false; omega

lemma spec_eq {k m p b : Nat} {sites : Fin p → Fin b → Fin k}
    (hinj : ∀ i, Function.Injective (sites i))
    (Tt : Fin p → Fin (2 ^ b) → Fin m → Bool) (pd vd : Fin (2 ^ k)) (py vy : Fin (2 ^ m))
    (t : Fin (2 ^ (k + 1))) :
    spec sites Tt (toVec k pd) (toVec k vd) (toVec m py) (toVec m vy) (toVec (k + 1) t) =
      decide (t.val ≤ Nat.card {d : Fin (2 ^ k) // goodS sites Tt pd vd py vy d}) := by
  unfold spec
  rw [leVec_eq_decide, ofVec_toVec, card_goodS hinj]
  have hrk : (Finset.univ.filter (fun j =>
      (echelon (kerKOf sites Tt (toVec k pd) (toVec m py))).hasP j = true)).card ≤ k :=
    echelon_rank_le _
  by_cases hc : consOf sites Tt (toVec k pd) (toVec k vd) (toVec m py) (toVec m vy) = true
  · rw [if_pos hc]
    have hv : (fun i : Fin (k + 1) => consOf sites Tt (toVec k pd) (toVec k vd) (toVec m py)
        (toVec m vy) && cntEq (echelon (kerKOf sites Tt (toVec k pd) (toVec m py))).hasP
          (k + m + k) i.val) = fun i => decide ((Finset.univ.filter (fun j =>
            (echelon (kerKOf sites Tt (toVec k pd) (toVec m py))).hasP j = true)).card = i.val) := by
      funext i; rw [hc, Bool.true_and]; unfold cntEq; rw [cntAt_full]
    rw [hv, ofVec_onehot (by omega)]
  · rw [if_neg hc]
    have hv : (fun i : Fin (k + 1) => consOf sites Tt (toVec k pd) (toVec k vd) (toVec m py)
        (toVec m vy) && cntEq (echelon (kerKOf sites Tt (toVec k pd) (toVec m py))).hasP
          (k + m + k) i.val) = vecZero (k + 1) := by
      funext i; simp [hc, vecZero]
    rw [hv, ofVec_zero]

-- ============================================================
-- PART D: Statement bridge and input layout
-- ============================================================

lemma addr_eq {k b : Nat} (s : Fin b → Fin k) (x : Nat) :
    (List.finRange b).foldl (fun acc j => acc ||| ((x.testBit (s j).val).toNat <<< j.val)) 0
      % 2 ^ b = (extractS s x).val := by
  apply Nat.eq_of_testBit_eq; intro t
  rw [Nat.testBit_mod_two_pow, testBit_extractS]
  have hr : List.range b = (List.finRange b).map Fin.val := by
    apply List.ext_getElem <;> simp
  have hfold : (List.finRange b).foldl
      (fun acc j => acc ||| ((x.testBit (s j).val).toNat <<< j.val)) 0 =
      (List.range b).foldl (fun acc j =>
        acc ||| ((if h : j < b then x.testBit (s ⟨j, h⟩).val else false).toNat <<< j)) 0 := by
    rw [hr, List.foldl_map]
    congr 1; funext acc j; simp [j.isLt]
  rw [hfold, testBit_foldl_or]
  by_cases ht : t < b
  · simp [ht, List.mem_range]
  · simp [ht, List.mem_range]

lemma f_eq {k m p b : Nat} (sites : Fin p → Fin b → Fin k)
    (T : Fin p → Fin (2 ^ b) → Fin m → Bool) (x : Nat) (j : Fin m) :
    (List.finRange p).foldl (fun acc i => xor acc (T i (Fin.ofNat (2 ^ b)
      ((List.finRange b).foldl (fun acc j => acc ||| ((x.testBit (sites i j).val).toNat <<< j.val)) 0
        % 2 ^ b)) j)) false =
      bxorFinset Finset.univ (fun i : Fin p => T i (extractS (sites i) x) j) := by
  rw [← bxorFinset_finRange]
  congr 1; funext acc i; congr 2
  rw [addr_eq]
  exact Fin.ext (Nat.mod_eq_of_lt (extractS _ _).isLt)

lemma good_bridge {k m p b : Nat} (sites : Fin p → Fin b → Fin k)
    (T : Fin p → Fin (2 ^ b) → Fin m → Bool) (pd vd : Fin (2 ^ k)) (py vy : Fin (2 ^ m))
    (F : Nat → Fin m → Bool)
    (hF : ∀ x j, F x j = bxorFinset Finset.univ (fun i : Fin p => T i (extractS (sites i) x) j))
    (d : Fin (2 ^ k)) :
    ((d.val &&& pd.val) = (vd.val &&& pd.val) ∧
      ∃ y : Fin m → Bool, (∀ j, py.val.testBit j.val = true → y j = vy.val.testBit j.val) ∧
        ∀ (w : Fin (2 ^ k)) (j : Fin m), xor (F (w.val ^^^ d.val) j) (F w.val j) = y j) ↔
      goodS sites T pd vd py vy d := by
  simp only [hF]
  unfold goodS deriv fF
  exact Iff.rfl

def bitsL (n x : Nat) : List Bool := (List.range n).map (fun j => x.testBit j)

def inList {k m p b : Nat} (T : Fin p → Fin (2 ^ b) → Fin m → Bool)
    (pd vd : Fin (2 ^ k)) (py vy : Fin (2 ^ m)) (t : Fin (2 ^ (k + 1))) : List Bool :=
  (List.finRange p).flatMap (fun i => (List.finRange (2 ^ b)).flatMap (fun z => List.ofFn (T i z)))
    ++ bitsL k pd.val ++ bitsL k vd.val ++ bitsL m py.val ++ bitsL m vy.val ++ bitsL (k + 1) t.val

def inLen (k m p b : Nat) : Nat := p * 2 ^ b * m + 2 * k + 2 * m + (k + 1)

lemma length_flatMap_const {α β : Type} (l : List α) (f : α → List β) (k : Nat)
    (hf : ∀ a ∈ l, (f a).length = k) : (l.flatMap f).length = l.length * k := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.flatMap_cons, List.length_append, List.length_cons,
      hf a List.mem_cons_self, ih (fun x hx => hf x (List.mem_cons_of_mem _ hx))]
    ring

lemma getElem_flatMap_const {α β : Type} (l : List α) (f : α → List β) (k : Nat)
    (hf : ∀ a ∈ l, (f a).length = k) {j i : Nat} (hj : j < l.length) (hi : i < k)
    (hidx : j * k + i < (l.flatMap f).length) :
    (l.flatMap f)[j * k + i]'hidx =
      (f (l[j]'hj))[i]'(by rw [hf _ (List.getElem_mem hj)]; exact hi) := by
  induction l generalizing j with
  | nil => simp at hj
  | cons a l ih =>
    cases j with
    | zero =>
      simp only [Nat.zero_mul, Nat.zero_add, List.flatMap_cons, List.getElem_cons_zero]
      rw [List.getElem_append_left (by rw [hf a List.mem_cons_self]; exact hi)]
    | succ j =>
      simp only [List.flatMap_cons, List.getElem_cons_succ]
      have hlen : (f a).length = k := hf a List.mem_cons_self
      have hge : (f a).length ≤ (j + 1) * k + i := by rw [hlen]; nlinarith
      rw [List.getElem_append_right hge]
      have hsub : (j + 1) * k + i - (f a).length = j * k + i := by
        rw [hlen, Nat.add_mul, Nat.one_mul]; omega
      simp only [hsub]
      exact ih (fun x hx => hf x (List.mem_cons_of_mem _ hx)) (by simpa using hj) _

lemma length_entries {m p b : Nat} (T : Fin p → Fin (2 ^ b) → Fin m → Bool) :
    ((List.finRange p).flatMap (fun i => (List.finRange (2 ^ b)).flatMap
      (fun z => List.ofFn (T i z)))).length = p * (2 ^ b * m) := by
  rw [length_flatMap_const _ _ (2 ^ b * m), List.length_finRange]
  intro i _
  rw [length_flatMap_const _ _ m, List.length_finRange]
  intro z _; simp

lemma length_bitsL (n x : Nat) : (bitsL n x).length = n := by simp [bitsL]

lemma length_inList {k m p b : Nat} (T : Fin p → Fin (2 ^ b) → Fin m → Bool)
    (pd vd : Fin (2 ^ k)) (py vy : Fin (2 ^ m)) (t : Fin (2 ^ (k + 1))) :
    (inList T pd vd py vy t).length = inLen k m p b := by
  unfold inList inLen
  simp only [List.length_append, length_entries, length_bitsL]
  ring

lemma idx_lt {i p z B j m : Nat} (hi : i < p) (hz : z < B) (hj : j < m) :
    i * (B * m) + (z * m + j) < p * (B * m) := by
  have h1 : z * m + j < B * m := by
    have : (z + 1) * m ≤ B * m := Nat.mul_le_mul_right _ hz
    nlinarith
  have h2 : (i + 1) * (B * m) ≤ p * (B * m) := Nat.mul_le_mul_right _ hi
  nlinarith

lemma inLen_eq (k m p b : Nat) : inLen k m p b = p * (2 ^ b * m) + 2 * k + 2 * m + (k + 1) := by
  unfold inLen; rw [Nat.mul_assoc]

def decTab {k m p b : Nat} (x : Fin (inLen k m p b) → Bool) (i : Fin p) (z : Fin (2 ^ b))
    (j : Fin m) : Bool :=
  x ⟨i.val * (2 ^ b * m) + (z.val * m + j.val), by
    have := idx_lt i.isLt z.isLt j.isLt
    rw [inLen_eq]; omega⟩

def decPd {k m p b : Nat} (x : Fin (inLen k m p b) → Bool) : Vec k := fun l =>
  x ⟨p * (2 ^ b * m) + l.val, by rw [inLen_eq]; omega⟩

def decVd {k m p b : Nat} (x : Fin (inLen k m p b) → Bool) : Vec k := fun l =>
  x ⟨p * (2 ^ b * m) + k + l.val, by rw [inLen_eq]; omega⟩

def decPy {k m p b : Nat} (x : Fin (inLen k m p b) → Bool) : Vec m := fun l =>
  x ⟨p * (2 ^ b * m) + 2 * k + l.val, by rw [inLen_eq]; omega⟩

def decVy {k m p b : Nat} (x : Fin (inLen k m p b) → Bool) : Vec m := fun l =>
  x ⟨p * (2 ^ b * m) + 2 * k + m + l.val, by rw [inLen_eq]; omega⟩

def decT {k m p b : Nat} (x : Fin (inLen k m p b) → Bool) : Vec (k + 1) := fun l =>
  x ⟨p * (2 ^ b * m) + 2 * k + 2 * m + l.val, by rw [inLen_eq]; omega⟩

lemma getD_app_left {α : Type} (l l' : List α) (d : α) {n : Nat} (h : n < l.length) :
    (l ++ l').getD n d = l.getD n d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

lemma getD_app_right {α : Type} (l l' : List α) (d : α) {n : Nat} (h : l.length ≤ n) :
    (l ++ l').getD n d = l'.getD (n - l.length) d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_right h]

lemma getD_bitsL (n x i : Nat) (hi : i < n) : (bitsL n x).getD i false = x.testBit i := by
  simp [bitsL, List.getD_eq_getElem?_getD, hi]

lemma ofFn_getD {n : Nat} (L : List Bool) (h : L.length = n) :
    List.ofFn (fun i : Fin n => L.getD i.val false) = L := by
  apply List.ext_getElem
  · simp [h]
  · intro i h1 h2
    simp [List.getD_eq_getElem?_getD, h2]

lemma getD_flatMap_fin {β : Type} {n L : Nat} (f : Fin n → List β)
    (hf : ∀ a, (f a).length = L) (d : β) (i : Fin n) {r : Nat} (hr : r < L) :
    ((List.finRange n).flatMap f).getD (i.val * L + r) d = (f i).getD r d := by
  have hlen : ((List.finRange n).flatMap f).length = n * L := by
    rw [length_flatMap_const _ _ L (fun a _ => hf a), List.length_finRange]
  have hidx : i.val * L + r < ((List.finRange n).flatMap f).length := by
    rw [hlen]
    have : (i.val + 1) * L ≤ n * L := Nat.mul_le_mul_right _ i.isLt
    nlinarith
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hidx, Option.getD_some,
    getElem_flatMap_const _ _ L (fun a _ => hf a) (by simp) hr hidx]
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by rw [hf]; exact hr), Option.getD_some]
  simp [List.getElem_finRange]

section Layout
variable {k m p b : Nat} (T : Fin p → Fin (2 ^ b) → Fin m → Bool)
  (pd vd : Fin (2 ^ k)) (py vy : Fin (2 ^ m)) (t : Fin (2 ^ (k + 1)))

lemma dec_tab :
    decTab (fun i : Fin (inLen k m p b) => (inList T pd vd py vy t).getD i.val false) = T := by
  funext i z j
  unfold decTab inList
  have hlenE := length_entries T
  have hidx := idx_lt i.isLt z.isLt j.isLt
  have hpeel : ∀ N, N < p * (2 ^ b * m) →
      ((List.finRange p).flatMap (fun i => (List.finRange (2 ^ b)).flatMap
        (fun z => List.ofFn (T i z))) ++ bitsL k pd.val ++ bitsL k vd.val ++ bitsL m py.val ++
        bitsL m vy.val ++ bitsL (k + 1) t.val).getD N false =
      ((List.finRange p).flatMap (fun i => (List.finRange (2 ^ b)).flatMap
        (fun z => List.ofFn (T i z)))).getD N false := by
    intro N hN
    rw [getD_app_left _ _ _ (by simp only [List.length_append, hlenE, length_bitsL]; omega),
      getD_app_left _ _ _ (by simp only [List.length_append, hlenE, length_bitsL]; omega),
      getD_app_left _ _ _ (by simp only [List.length_append, hlenE, length_bitsL]; omega),
      getD_app_left _ _ _ (by simp only [List.length_append, hlenE, length_bitsL]; omega),
      getD_app_left _ _ _ (by simp only [List.length_append, hlenE, length_bitsL]; omega)]
  dsimp only
  rw [hpeel _ hidx]
  have hzj : z.val * m + j.val < 2 ^ b * m := by
    have : (z.val + 1) * m ≤ 2 ^ b * m := Nat.mul_le_mul_right _ z.isLt
    nlinarith [j.isLt]
  rw [getD_flatMap_fin _ (fun i => by rw [length_flatMap_const _ _ m (fun z _ => by simp),
    List.length_finRange]) _ i hzj]
  rw [getD_flatMap_fin _ (fun z => by simp) _ z j.isLt]
  simp [List.getD_eq_getElem?_getD]

lemma dec_pd :
    decPd (fun i : Fin (inLen k m p b) => (inList T pd vd py vy t).getD i.val false) =
      toVec k pd := by
  funext l
  unfold decPd inList toVec
  have hlenE := length_entries T
  dsimp only
  rw [getD_app_left _ _ _ (by simp only [List.length_append, hlenE, length_bitsL]; omega),
    getD_app_left _ _ _ (by simp only [List.length_append, hlenE, length_bitsL]; omega),
    getD_app_left _ _ _ (by simp only [List.length_append, hlenE, length_bitsL]; omega),
    getD_app_left _ _ _ (by simp only [List.length_append, hlenE, length_bitsL]; omega),
    getD_app_right _ _ _ (by simp only [List.length_append, hlenE, length_bitsL]; omega)]
  rw [hlenE, Nat.add_sub_cancel_left, getD_bitsL _ _ _ l.isLt]

lemma dec_vd :
    decVd (fun i : Fin (inLen k m p b) => (inList T pd vd py vy t).getD i.val false) =
      toVec k vd := by
  funext l
  unfold decVd inList toVec
  have hlenE := length_entries T
  dsimp only
  rw [getD_app_left _ _ _ (by simp only [List.length_append, hlenE, length_bitsL]; omega),
    getD_app_left _ _ _ (by simp only [List.length_append, hlenE, length_bitsL]; omega),
    getD_app_left _ _ _ (by simp only [List.length_append, hlenE, length_bitsL]; omega),
    getD_app_right _ _ _ (by simp only [List.length_append, hlenE, length_bitsL]; omega)]
  simp only [List.length_append, hlenE, length_bitsL]
  rw [show p * (2 ^ b * m) + k + l.val - (p * (2 ^ b * m) + k) = l.val by omega,
    getD_bitsL _ _ _ l.isLt]

lemma dec_py :
    decPy (fun i : Fin (inLen k m p b) => (inList T pd vd py vy t).getD i.val false) =
      toVec m py := by
  funext l
  unfold decPy inList toVec
  have hlenE := length_entries T
  dsimp only
  rw [getD_app_left _ _ _ (by simp only [List.length_append, hlenE, length_bitsL]; omega),
    getD_app_left _ _ _ (by simp only [List.length_append, hlenE, length_bitsL]; omega),
    getD_app_right _ _ _ (by simp only [List.length_append, hlenE, length_bitsL]; omega)]
  simp only [List.length_append, hlenE, length_bitsL]
  rw [show p * (2 ^ b * m) + 2 * k + l.val - (p * (2 ^ b * m) + k + k) = l.val by omega,
    getD_bitsL _ _ _ l.isLt]

lemma dec_vy :
    decVy (fun i : Fin (inLen k m p b) => (inList T pd vd py vy t).getD i.val false) =
      toVec m vy := by
  funext l
  unfold decVy inList toVec
  have hlenE := length_entries T
  dsimp only
  rw [getD_app_left _ _ _ (by simp only [List.length_append, hlenE, length_bitsL]; omega),
    getD_app_right _ _ _ (by simp only [List.length_append, hlenE, length_bitsL]; omega)]
  simp only [List.length_append, hlenE, length_bitsL]
  rw [show p * (2 ^ b * m) + 2 * k + m + l.val - (p * (2 ^ b * m) + k + k + m) = l.val by omega,
    getD_bitsL _ _ _ l.isLt]

lemma dec_t :
    decT (fun i : Fin (inLen k m p b) => (inList T pd vd py vy t).getD i.val false) =
      toVec (k + 1) t := by
  funext l
  unfold decT inList toVec
  have hlenE := length_entries T
  dsimp only
  rw [getD_app_right _ _ _ (by simp only [List.length_append, hlenE, length_bitsL]; omega)]
  simp only [List.length_append, hlenE, length_bitsL]
  rw [show p * (2 ^ b * m) + 2 * k + 2 * m + l.val - (p * (2 ^ b * m) + k + k + m + m) = l.val
    by omega, getD_bitsL _ _ _ l.isLt]

end Layout
section Synth
open Builder

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

private lemma has_constBool {n : Nat} {B : Bank n}
    (h0 : B.Has (fun _ => false)) (h1 : B.Has (fun _ => true)) (c : Bool) :
    B.Has (fun _ => c) := by
  cases c <;> assumption

private lemma collectPropList {n : Nat} {α : Type} (B : Bank n) (l : List α)
    (P : α → Bank n → Prop) (hmono : ∀ a C D, C.Ext D → P a C → P a D) (cost : Nat)
    (emit : ∀ D : Bank n, B.Ext D → ∀ a ∈ l, D.Grow cost (P a)) :
    B.Grow (l.length * cost) (fun D => ∀ a ∈ l, P a D) := by
  induction l with
  | nil => simpa using (Bank.Grow.pure B (p := fun D => ∀ a ∈ ([] : List α), P a D) (by simp))
  | cons a l ih =>
    have t := ih (fun D e x hx => emit D e x (List.mem_cons_of_mem _ hx))
    have out := t.bind (b := cost) (q := fun E => ∀ x ∈ a :: l, P x E) (by
      intro D e haveL
      obtain ⟨E, e', c', ha⟩ := emit D e a List.mem_cons_self
      refine ⟨E, e', c', ?_⟩
      intro x hx
      rcases List.mem_cons.mp hx with rfl | h
      · exact ha
      · exact hmono x D E e' (haveL x h))
    simpa [Nat.succ_mul] using out

private lemma collectPropFin {n m : Nat} (B : Bank n)
    (P : Fin m → Bank n → Prop) (hmono : ∀ i C D, C.Ext D → P i C → P i D) (cost : Nat)
    (emit : ∀ D : Bank n, B.Ext D → ∀ i : Fin m, D.Grow cost (P i)) :
    B.Grow (m * cost) (fun D => ∀ i : Fin m, P i D) := by
  simpa using collectPropList B (List.finRange m) P hmono cost (fun D e i _ => emit D e i)


private lemma grow_vecXor {n d : Nat} (B : Bank n)
    (u v : (Fin n → Bool) → Vec d)
    (hu : ∀ i, B.Has (fun x => u x i)) (hv : ∀ i, B.Has (fun x => v x i)) :
    B.Grow (d * 4) (fun D => ∀ i, D.Has (fun x => vecXor (u x) (v x) i)) :=
  B.collectFin d _ 4 (fun D e i => Bank.xor2 (e (hu i)) (e (hv i)))

private lemma grow_vecDot {n d : Nat} (B : Bank n)
    (u v : (Fin n → Bool) → Vec d)
    (hu : ∀ i, B.Has (fun x => u x i)) (hv : ∀ i, B.Has (fun x => v x i)) :
    B.Grow (1 + d * 5) (fun D => D.Has (fun x => vecDot (u x) (v x))) := by
  obtain ⟨D1, e1, c1, h1⟩ := B.collectFin d (fun i x => u x i && v x i) 1
    (fun D e i => Bank.meet (e (hu i)) (e (hv i)))
  obtain ⟨D2, e2, c2, h2⟩ := D1.xorList (List.finRange d) (fun i x => u x i && v x i) (fun i _ => h1 i)
  simp only [List.length_finRange] at c2
  exact ⟨D2, Bank.ext_trans e1 e2, by omega, h2⟩

private lemma grow_vecLinComb {n d1 d2 : Nat} (B : Bank n)
    (M : (Fin n → Bool) → Fin d1 → Vec d2) (a : (Fin n → Bool) → Vec d1)
    (hM : ∀ i j, B.Has (fun x => M x i j)) (ha : ∀ i, B.Has (fun x => a x i)) :
    B.Grow (d2 * (1 + d1 * 5)) (fun D => ∀ j, D.Has (fun x => vecLinComb (M x) (a x) j)) :=
  B.collectFin d2 _ (1 + d1 * 5) (fun D e j =>
    grow_vecDot D a (fun x i => M x i j) (fun i => e (ha i)) (fun i => e (hM i j)))

private lemma grow_anyBit {n d : Nat} (B : Bank n)
    (c : (Fin n → Bool) → Vec d) (hc : ∀ i, B.Has (fun x => c x i)) :
    B.Grow (1 + d) (fun D => D.Has (fun x => anyBit (c x))) := by
  exact (B.orList (List.finRange d) (fun i x => c x i) (fun i _ => hc i)).weaken (by simp) (fun _ h => h)

private lemma grow_firstBit {n d : Nat} (B : Bank n)
    (h1 : B.Has (fun _ => true))
    (c : (Fin n → Bool) → Vec d) (hc : ∀ i, B.Has (fun x => c x i)) :
    B.Grow (d + d * (d + 2)) (fun D => ∀ i, D.Has (fun x => firstBit (c x) i)) := by
  obtain ⟨D1, e1, c1, hnc⟩ := B.collectFin d (fun j x => !(c x j)) 1 (fun D e j => Bank.inv (e (hc j)))
  obtain ⟨D2, e2, c2, hfb⟩ := D1.collectFin d (fun i x => firstBit (c x) i) (d + 2) (fun E eE i => by
    have ht : ∀ j ∈ List.finRange d, E.Has (fun x => decide (i.val ≤ j.val) || !(c x j)) := by
      intro j _
      by_cases hij : i.val ≤ j.val
      · exact has_congr (eE (e1 h1)) (fun x => by simp [hij])
      · exact has_congr (eE (hnc j)) (fun x => by simp [hij])
    obtain ⟨F1, ef1, cf1, ha⟩ := E.andList (List.finRange d) (fun j x => decide (i.val ≤ j.val) || !(c x j)) ht
    obtain ⟨F2, ef2, cf2, hm⟩ := Bank.meet (ef1 (eE (e1 (hc i)))) ha
    simp only [List.length_finRange] at cf1
    exact ⟨F2, Bank.ext_trans ef1 ef2, by omega, hm⟩)
  exact ⟨D2, Bank.ext_trans e1 e2, by omega, hfb⟩

private def rkCost (d1 d2 : Nat) : Nat :=
  (d1 + d1 * (d1 + 2)) + d2 * (1 + d1 * 5) + d1 * (d2 * 12)

private lemma grow_restrictKernelStep {n d1 d2 : Nat} (B : Bank n)
    (h0 : B.Has (fun _ => false)) (h1 : B.Has (fun _ => true))
    (U : (Fin n → Bool) → Fin d1 → Vec d2) (c : (Fin n → Bool) → Vec d1)
    (hU : ∀ i j, B.Has (fun x => U x i j)) (hc : ∀ i, B.Has (fun x => c x i)) :
    B.Grow (rkCost d1 d2)
      (fun D => (∀ j, D.Has (fun x => pivotVec (U x) (c x) j)) ∧
        (∀ i j, D.Has (fun x => restrictKernelStep (U x) (c x) i j))) := by
  obtain ⟨D1, e1, c1, hfb⟩ := grow_firstBit B h1 c hc
  obtain ⟨D2, e2, c2, hpv⟩ := grow_vecLinComb D1 U (fun x => firstBit (c x))
    (fun i j => e1 (hU i j)) hfb
  obtain ⟨D3, e3, c3, hrk⟩ := collectPropFin D2
    (fun i D => ∀ j : Fin d2, D.Has (fun x => restrictKernelStep (U x) (c x) i j))
    (fun _ _ _ e h j => e (h j)) (d2 * 12) (fun D e i =>
      D.collectFin d2 (fun j x => restrictKernelStep (U x) (c x) i j) 12 (fun E ee j => by
        obtain ⟨F1, ef1, cf1, hxor⟩ := Bank.xor2 (ee (e (e2 (e1 (hU i j))))) (ee (e (hpv j)))
        obtain ⟨F2, ef2, cf2, hm1⟩ := Bank.mux (ef1 (ee (e (e2 (e1 (hc i)))))) hxor
          (ef1 (ee (e (e2 (e1 (hU i j))))))
        obtain ⟨F3, ef3, cf3, hm2⟩ := Bank.mux (ef2 (ef1 (ee (e (e2 (hfb i))))))
          (ef2 (ef1 (ee (e (e2 (e1 h0)))))) hm1
        exact ⟨F3, Bank.ext_trans ef1 (Bank.ext_trans ef2 ef3), by omega,
          has_congr hm2 (fun x => by unfold restrictKernelStep; split_ifs <;> rfl)⟩))
  exact ⟨D3, Bank.ext_trans e1 (Bank.ext_trans e2 e3), by unfold rkCost; omega,
    ⟨fun j => e3 (hpv j), hrk⟩⟩

private def echCost (nrows ncols : Nat) : Nat :=
  ncols * (1 + nrows + rkCost nrows ncols)

private lemma grow_echelon {n nrows ncols : Nat} (B : Bank n)
    (h0 : B.Has (fun _ => false)) (h1 : B.Has (fun _ => true))
    (M : (Fin n → Bool) → Fin nrows → Vec ncols)
    (hM : ∀ i j, B.Has (fun x => M x i j)) :
    B.Grow (echCost nrows ncols)
      (fun D => (∀ j, D.Has (fun x => (echelon (M x)).hasP j)) ∧
        (∀ j1 j2, D.Has (fun x => (echelon (M x)).piv j1 j2))) := by
  let initSt : (Fin n → Bool) → EchState nrows ncols := fun x => echelonInit (M x)
  let stepSt : ((Fin n → Bool) → EchState nrows ncols) → Fin ncols → (Fin n → Bool) → EchState nrows ncols :=
    fun st col x => echelonStep (st x) col
  let Inv : ((Fin n → Bool) → EchState nrows ncols) → Bank n → Prop :=
    fun st D => (∀ i j, D.Has (fun x => (st x).work i j)) ∧
      (∀ j, D.Has (fun x => (st x).hasP j)) ∧
      (∀ j1 j2, D.Has (fun x => (st x).piv j1 j2))
  have hinit : Inv initSt B := ⟨hM, fun _ => h0, fun _ _ => h0⟩
  have hfold := Bank.foldGrow B (List.finRange ncols) initSt stepSt Inv
    (1 + nrows + rkCost nrows ncols) hinit (by
      intro D e st col _ ⟨hwork, hhasP, hpiv⟩
      obtain ⟨D1, e1, c1, hany⟩ := grow_anyBit D (fun x i => (st x).work i col) (fun i => hwork i col)
      obtain ⟨D2, e2, c2, ⟨hpv, hrk⟩⟩ := grow_restrictKernelStep D1 (e1 (e h0)) (e1 (e h1))
        (fun x => (st x).work) (fun x i => (st x).work i col)
        (fun i j => e1 (hwork i j)) (fun i => e1 (hwork i col))
      refine ⟨D2, Bank.ext_trans e1 e2, by omega, hrk, ?_, ?_⟩
      · intro j
        by_cases hj : j = col
        · exact has_congr (e2 hany) (fun x => by simp [stepSt, echelonStep, hj])
        · exact has_congr (e2 (e1 (hhasP j))) (fun x => by simp [stepSt, echelonStep, hj])
      · intro j1 j2
        by_cases hj : j1 = col
        · exact has_congr (hpv j2) (fun x => by simp [stepSt, echelonStep, hj])
        · exact has_congr (e2 (e1 (hpiv j1 j2))) (fun x => by simp [stepSt, echelonStep, hj]))
  refine hfold.weaken (by unfold echCost; simp) (fun D ⟨_, hhasP, hpiv⟩ => ?_)
  have hfl : ∀ x, ((List.finRange ncols).foldl stepSt initSt) x = echelon (M x) := fun x =>
    foldl_apply' (fun acc col y => echelonStep acc col) initSt (List.finRange ncols) x
  exact ⟨fun j => has_congr (hhasP j) (fun x => by rw [hfl x]),
    fun j1 j2 => has_congr (hpiv j1 j2) (fun x => by rw [hfl x])⟩

private lemma grow_echelonReduce {n ncols : Nat} (B : Bank n)
    (hasP : (Fin n → Bool) → Fin ncols → Bool)
    (piv : (Fin n → Bool) → Fin ncols → Vec ncols)
    (z : (Fin n → Bool) → Vec ncols)
    (hhasP : ∀ j, B.Has (fun x => hasP x j))
    (hpiv : ∀ j1 j2, B.Has (fun x => piv x j1 j2))
    (hz : ∀ j, B.Has (fun x => z x j)) :
    B.Grow (ncols * (1 + ncols * 8))
      (fun D => ∀ j, D.Has (fun x => echelonReduce (hasP x) (piv x) (z x) j)) := by
  let stepR : ((Fin n → Bool) → Vec ncols) → Fin ncols → (Fin n → Bool) → Vec ncols :=
    fun rem j x => if rem x j && hasP x j then vecXor (rem x) (piv x j) else rem x
  have hfold := Bank.foldGrow B (List.finRange ncols) z stepR
    (fun rem D => ∀ j, D.Has (fun x => rem x j)) (1 + ncols * 8) hz (by
      intro D e rem j _ hrem
      obtain ⟨D1, e1, c1, hcond⟩ := Bank.meet (hrem j) (e (hhasP j))
      obtain ⟨D2, e2, c2, hnext⟩ := D1.collectFin ncols (fun j' x => stepR rem j x j') 8 (fun E ee j' => by
        obtain ⟨F1, ef1, cf1, hxor⟩ := Bank.xor2 (ee (e1 (hrem j'))) (ee (e1 (e (hpiv j j'))))
        obtain ⟨F2, ef2, cf2, hmux⟩ := Bank.mux (ef1 (ee hcond)) hxor (ef1 (ee (e1 (hrem j'))))
        exact ⟨F2, Bank.ext_trans ef1 ef2, by omega, has_congr hmux (fun x => by
          dsimp only [stepR]; split_ifs <;> rfl)⟩)
      exact ⟨D2, Bank.ext_trans e1 e2, by omega, hnext⟩)
  refine hfold.weaken (by simp) (fun D hD j => ?_)
  exact has_congr (hD j) (fun x => by
    have hfl := foldl_apply'
      (fun acc j y => if acc j && hasP y j then vecXor acc (piv y j) else acc) z (List.finRange ncols) x
    exact congrFun hfl j)

private lemma grow_shiftTable {n b : Nat} (B : Bank n)
    (δ : (Fin n → Bool) → Fin (2 ^ b))
    (T : (Fin n → Bool) → Fin (2 ^ b) → Bool)
    (hδ : ∀ t : Fin b, B.Has (fun x => (δ x).val.testBit t.val))
    (hT : ∀ α : Fin (2 ^ b), B.Has (fun x => T x α)) :
    B.Grow (b * (2 ^ b * 4))
      (fun D => ∀ α : Fin (2 ^ b), D.Has (fun x => shiftTable (δ x) (T x) α)) := by
  let stepS : ((Fin n → Bool) → Fin (2 ^ b) → Bool) → Fin b → (Fin n → Bool) → Fin (2 ^ b) → Bool :=
    fun cur t x => shiftLayer t.val t.isLt ((δ x).val.testBit t.val) (cur x)
  have hfold := Bank.foldGrow B (List.finRange b) T stepS
    (fun cur D => ∀ α, D.Has (fun x => cur x α)) (2 ^ b * 4) hT (by
      intro D e cur t _ hcur
      apply D.collectFin (2 ^ b) (fun α x => stepS cur t x α) 4
      intro E ee α
      let α' : Fin (2 ^ b) := ⟨α.val ^^^ (1 <<< t.val), xor_lt α.isLt
        (by rw [Nat.shiftLeft_eq, Nat.one_mul]; exact Nat.pow_lt_pow_right (by omega) t.isLt)⟩
      exact Bank.mux (ee (e (hδ t))) (ee (hcur α')) (ee (hcur α)))
  refine hfold.weaken (by simp) (fun D hD α => ?_)
  exact has_congr (hD α) (fun x => by
    have hfl := foldl_apply'
      (fun acc t y => shiftLayer t.val t.isLt ((δ y).val.testBit t.val) acc) T (List.finRange b) x
    exact congrFun hfl α)

private lemma grow_fmt {n b : Nat} (B : Bank n)
    (T : (Fin n → Bool) → Fin (2 ^ b) → Bool)
    (hT : ∀ α : Fin (2 ^ b), B.Has (fun x => T x α)) :
    B.Grow (b * (2 ^ b * 4))
      (fun D => ∀ α : Fin (2 ^ b), D.Has (fun x => fmt (T x) α)) := by
  let stepF : ((Fin n → Bool) → Fin (2 ^ b) → Bool) → Fin b → (Fin n → Bool) → Fin (2 ^ b) → Bool :=
    fun cur t x => fmtLayer t.val t.isLt (cur x)
  have hfold := Bank.foldGrow B (List.finRange b) T stepF
    (fun cur D => ∀ α, D.Has (fun x => cur x α)) (2 ^ b * 4) hT (by
      intro D _ cur t _ hcur
      apply D.collectFin (2 ^ b) (fun α x => stepF cur t x α) 4
      intro E ee α
      by_cases hbit : α.val.testBit t.val = true
      · let α' : Fin (2 ^ b) := ⟨α.val ^^^ (1 <<< t.val), xor_lt α.isLt
          (by rw [Nat.shiftLeft_eq, Nat.one_mul]; exact Nat.pow_lt_pow_right (by omega) t.isLt)⟩
        exact (Bank.xor2 (ee (hcur α)) (ee (hcur α'))).weaken (le_refl _) (fun F hF =>
          has_congr hF (fun x => by simp [stepF, fmtLayer, hbit, α']))
      · exact (Bank.Grow.pure E (has_congr (ee (hcur α)) (fun x => by
          simp [stepF, fmtLayer, hbit]))).weaken (by omega) (fun _ h => h))
  refine hfold.weaken (by simp) (fun D hD α => ?_)
  exact has_congr (hD α) (fun x => by
    have hfl := foldl_apply' (fun acc t _ => fmtLayer t.val t.isLt acc) T (List.finRange b) x
    exact congrFun hfl α)

private lemma grow_derivTable {n b : Nat} (B : Bank n)
    (ψ : (Fin n → Bool) → Fin (2 ^ b) → Bool)
    (δ : (Fin n → Bool) → Fin (2 ^ b))
    (hψ : ∀ α, B.Has (fun x => ψ x α))
    (hδ : ∀ t : Fin b, B.Has (fun x => (δ x).val.testBit t.val)) :
    B.Grow ((2 * b + 1) * (2 ^ b * 4))
      (fun D => ∀ α, D.Has (fun x => derivTable (ψ x) (δ x) α)) := by
  obtain ⟨D1, e1, c1, hsh⟩ := grow_shiftTable B δ ψ hδ hψ
  obtain ⟨D2, e2, c2, hxr⟩ := D1.collectFin (2 ^ b) (fun α x => xor (shiftTable (δ x) (ψ x) α) (ψ x α)) 4
    (fun D e α => Bank.xor2 (e (hsh α)) (e (e1 (hψ α))))
  obtain ⟨D3, e3, c3, hfm⟩ := grow_fmt D2 (fun x α => xor (shiftTable (δ x) (ψ x) α) (ψ x α)) hxr
  exact ⟨D3, Bank.ext_trans e1 (Bank.ext_trans e2 e3), by
    have hmul : (2 * b + 1) * (2 ^ b * 4) = b * (2 ^ b * 4) + 2 ^ b * 4 + b * (2 ^ b * 4) := by ring
    omega, hfm⟩


private lemma grow_cntEq_prefix {n d : Nat} (B : Bank n)
    (h0 : B.Has (fun _ => false)) (h1 : B.Has (fun _ => true))
    (p : (Fin n → Bool) → Fin d → Bool)
    (hp : ∀ i : Fin d, B.Has (fun x => p x i))
    (c : Nat) (hc : c ≤ d) :
    B.Grow (c * ((d + 1) * 4))
      (fun D => ∀ c' ≤ c, ∀ v : Fin (d + 1), D.Has (fun x => cntEq (p x) c' v.val)) := by
  induction c with
  | zero =>
    refine ⟨B, Bank.ext_refl B, by simp, fun c' hc' v => ?_⟩
    have hc0 : c' = 0 := by omega
    subst hc0
    exact has_congr (has_constBool h0 h1 (decide (v.val = 0))) (fun x => (cntEq_zero (p x) v.val).symm)
  | succ c ih =>
    have hlt : c < d := by omega
    obtain ⟨D1, e1, c1, hprev⟩ := ih (by omega)
    obtain ⟨D2, e2, c2, hcur⟩ := D1.collectFin (d + 1) (fun v x => cntEq (p x) (c + 1) v.val) 4 (fun D e v => by
      cases hv : v.val with
      | zero =>
        obtain ⟨E1, ee1, cc1, hnp⟩ := Bank.inv (e (e1 (hp ⟨c, hlt⟩)))
        obtain ⟨E2, ee2, cc2, hand⟩ := Bank.meet (ee1 (e (hprev c (le_refl c) ⟨0, Nat.succ_pos d⟩))) hnp
        exact ⟨E2, Bank.ext_trans ee1 ee2, by omega, has_congr hand (fun x => by
          rw [← cntEq_succ_zero (p x) hlt])⟩
      | succ v' =>
        have hv'lt : v' < d + 1 := by omega
        obtain ⟨E1, ee1, cc1, hmux⟩ := Bank.mux (e (e1 (hp ⟨c, hlt⟩)))
          (e (hprev c (le_refl c) ⟨v', hv'lt⟩)) (e (hprev c (le_refl c) v))
        exact ⟨E1, ee1, by omega, has_congr hmux (fun x => by
          rw [cntEq_succ_succ (p x) hlt v', ← hv]
          cases p x ⟨c, hlt⟩ <;> simp)⟩)
    refine ⟨D2, Bank.ext_trans e1 e2, by rw [Nat.succ_mul]; omega, fun c' hc' v => ?_⟩
    by_cases hle : c' ≤ c
    · exact e2 (hprev c' hle v)
    · have heq : c' = c + 1 := by omega
      subst heq; exact hcur v

private lemma grow_incCarry_prefix {n w : Nat} (B : Bank n)
    (a : (Fin n → Bool) → Vec w) (b : (Fin n → Bool) → Bool)
    (ha : ∀ i, B.Has (fun x => a x i)) (hb : B.Has b)
    (t : Nat) (ht : t ≤ w) :
    B.Grow t (fun D => ∀ i ≤ t, D.Has (fun x => incCarry (a x) (b x) i)) := by
  induction t with
  | zero =>
    refine ⟨B, Bank.ext_refl B, by simp, fun i hi => ?_⟩
    have hi0 : i = 0 := by omega
    subst hi0; exact hb
  | succ t ih =>
    have hlt : t < w := by omega
    obtain ⟨D1, e1, c1, hprev⟩ := ih (by omega)
    obtain ⟨D2, e2, c2, hm⟩ := Bank.meet (e1 (ha ⟨t, hlt⟩)) (hprev t (le_refl t))
    refine ⟨D2, Bank.ext_trans e1 e2, by omega, fun i hi => ?_⟩
    by_cases hle : i ≤ t
    · exact e2 (hprev i hle)
    · have heq : i = t + 1 := by omega
      subst heq
      exact has_congr hm (fun x => by simp [incCarry, hlt])

private lemma grow_incBits {n w : Nat} (B : Bank n)
    (a : (Fin n → Bool) → Vec w) (b : (Fin n → Bool) → Bool)
    (ha : ∀ i, B.Has (fun x => a x i)) (hb : B.Has b) :
    B.Grow (w * 5) (fun D => ∀ i, D.Has (fun x => incBits (a x) (b x) i)) := by
  obtain ⟨D1, e1, c1, hcar⟩ := grow_incCarry_prefix B a b ha hb w (le_refl w)
  obtain ⟨D2, e2, c2, hres⟩ := D1.collectFin w (fun i x => incBits (a x) (b x) i) 4 (fun D e i =>
    Bank.xor2 (e (e1 (ha i))) (e (hcar i.val (Nat.le_of_lt i.isLt))))
  exact ⟨D2, Bank.ext_trans e1 e2, by omega, hres⟩

private lemma grow_countBits {n w : Nat} {α : Type} (B : Bank n)
    (h0 : B.Has (fun _ => false))
    (l : List α) (p : α → (Fin n → Bool) → Bool)
    (hp : ∀ a ∈ l, B.Has (p a)) :
    B.Grow (l.length * (w * 5))
      (fun D => ∀ i, D.Has (fun x => countBits w l (fun a => p a x) i)) := by
  let stepC : ((Fin n → Bool) → Vec w) → α → (Fin n → Bool) → Vec w :=
    fun acc a x => incBits (acc x) (p a x)
  have hfold := Bank.foldGrow B l (fun _ => vecZero w) stepC
    (fun acc D => ∀ i, D.Has (fun x => acc x i)) (w * 5) (fun _ => h0) (by
      intro D e acc a ha hacc
      exact grow_incBits D acc (p a) hacc (e (hp a ha)))
  refine hfold.weaken (le_refl _) (fun D hD i => ?_)
  exact has_congr (hD i) (fun x => by
    have hfl := foldl_apply' (fun acc a y => incBits acc (p a y)) (fun _ => vecZero w) l x
    exact congrFun hfl i)

private lemma grow_shiftByRank {n m q w : Nat} (B : Bank n)
    (h0 : B.Has (fun _ => false))
    (hasP : (Fin n → Bool) → Fin m → Bool)
    (hcnt : ∀ v : Fin (m + 1), B.Has (fun x => cntEq (hasP x) m v.val))
    (pc : (Fin n → Bool) → Vec w)
    (hpc : ∀ i, B.Has (fun x => pc x i)) :
    B.Grow (w * (2 * q + 3))
      (fun D => ∀ i, D.Has (fun x => shiftByRank (hasP x) q w (pc x) i)) := by
  apply B.collectFin w (fun i x => shiftByRank (hasP x) q w (pc x) i) (2 * q + 3)
  intro D e i
  obtain ⟨E1, ee1, cc1, hterms⟩ := D.collectFin (q + 1)
    (fun ρ x => cntEq (hasP x) m ρ.val &&
      if h : q - ρ.val ≤ i.val then pc x ⟨i.val - (q - ρ.val), by omega⟩ else false) 1
    (fun E eE ρ => by
      have h1 : E.Has (fun x => cntEq (hasP x) m ρ.val) := by
        by_cases hρ : ρ.val ≤ m
        · exact eE (e (hcnt ⟨ρ.val, by omega⟩))
        · exact has_congr (eE (e h0)) (fun x => by
            have hle := cntAt_le (hasP x) m
            simp [cntEq]; omega)
      have h2 : E.Has (fun x => if h : q - ρ.val ≤ i.val then pc x ⟨i.val - (q - ρ.val), by omega⟩ else false) := by
        by_cases hle : q - ρ.val ≤ i.val
        · exact has_congr (eE (e (hpc ⟨i.val - (q - ρ.val), by omega⟩))) (fun x => by simp [hle])
        · exact has_congr (eE (e h0)) (fun x => by simp [hle])
      exact Bank.meet h1 h2)
  obtain ⟨E2, ee2, cc2, hor⟩ := E1.orList (List.finRange (q + 1)) _ (fun ρ _ => hterms ρ)
  simp only [List.length_finRange] at cc2
  exact ⟨E2, Bank.ext_trans ee1 ee2, by omega, hor⟩

private lemma grow_leVec {n w : Nat} (B : Bank n)
    (h1 : B.Has (fun _ => true))
    (a b : (Fin n → Bool) → Vec w)
    (ha : ∀ i, B.Has (fun x => a x i)) (hb : ∀ i, B.Has (fun x => b x i)) :
    B.Grow (w * 9) (fun D => D.Has (fun x => leVec (a x) (b x))) := by
  let stepL : BitFn n → Fin w → BitFn n :=
    fun acc i x => (!(a x i) && b x i) || ((a x i == b x i) && acc x)
  have hfold := Bank.foldGrow B (List.finRange w) (fun _ => true) stepL
    (fun acc D => D.Has acc) 9 h1 (by
      intro D e acc i _ hacc
      obtain ⟨E1, ee1, cc1, hna⟩ := Bank.inv (e (ha i))
      obtain ⟨E2, ee2, cc2, hm1⟩ := Bank.meet hna (ee1 (e (hb i)))
      obtain ⟨E3, ee3, cc3, heq⟩ := Bank.eqBool (ee2 (ee1 (e (ha i)))) (ee2 (ee1 (e (hb i))))
      obtain ⟨E4, ee4, cc4, hm2⟩ := Bank.meet heq (ee3 (ee2 (ee1 hacc)))
      obtain ⟨E5, ee5, cc5, hj⟩ := Bank.join (ee4 (ee3 hm1)) hm2
      exact ⟨E5, Bank.ext_trans ee1 (Bank.ext_trans ee2 (Bank.ext_trans ee3 (Bank.ext_trans ee4 ee5))),
        by omega, hj⟩)
  refine hfold.weaken (by simp) (fun D hD => ?_)
  exact has_congr hD (fun x =>
    foldl_apply' (fun acc i y => (!(a y i) && b y i) || ((a y i == b y i) && acc)) (fun _ => true)
      (List.finRange w) x)


-- ============================================================
-- PART E: Circuit construction for the spec
-- ============================================================

private lemma testBit_extractS_ofVec {k b : Nat} (s : Fin b → Fin k) (v : Vec k) (t : Fin b) :
    (extractS s (ofVec k v).val).val.testBit t.val = v (s t) := by
  simp [testBit_extractS, testBit_ofVec]

private lemma grow_dTables {n k m p b N : Nat} (sites : Fin p → Fin b → Fin k) (B : Bank n)
    (Tt : (Fin n → Bool) → Fin p → Fin (2 ^ b) → Fin m → Bool)
    (hT : ∀ i z j, B.Has (fun x => Tt x i z j))
    (V : (Fin n → Bool) → Fin N → Vec k) (hV : ∀ idx c, B.Has (fun x => V x idx c)) :
    B.Grow (N * (p * (m * ((2 * b + 1) * (2 ^ b * 4)))))
      (fun D => ∀ idx i j α, D.Has (fun x => derivTable (fun α => Tt x i α j)
        (extractS (sites i) (ofVec k (V x idx)).val) α)) := by
  apply collectPropFin B (fun idx D => ∀ i j α, D.Has (fun x => derivTable (fun α => Tt x i α j)
        (extractS (sites i) (ofVec k (V x idx)).val) α)) (fun _ _ _ e h i j α => e (h i j α))
  intro D e idx
  apply collectPropFin D (fun i E => ∀ j α, E.Has (fun x => derivTable (fun α => Tt x i α j)
        (extractS (sites i) (ofVec k (V x idx)).val) α)) (fun _ _ _ e h j α => e (h j α))
  intro E ee i
  apply collectPropFin E (fun j F => ∀ α, F.Has (fun x => derivTable (fun α => Tt x i α j)
        (extractS (sites i) (ofVec k (V x idx)).val) α)) (fun _ _ _ e h α => e (h α))
  intro F ef j
  exact grow_derivTable F (fun x α => Tt x i α j)
    (fun x => extractS (sites i) (ofVec k (V x idx)).val)
    (fun α => ef (ee (e (hT i α j))))
    (fun t => has_congr (ef (ee (e (hV idx (sites i t)))))
      (fun x => (testBit_extractS_ofVec (sites i) (V x idx) t).symm))

private lemma grow_dFE {n k m p b N : Nat} (sites : Fin p → Fin b → Fin k) (B : Bank n)
    (h0 : B.Has (fun _ => false))
    (Tt : (Fin n → Bool) → Fin p → Fin (2 ^ b) → Fin m → Bool)
    (V : (Fin n → Bool) → Fin N → Vec k)
    (hdt : ∀ idx i j α, B.Has (fun x => derivTable (fun α => Tt x i α j)
        (extractS (sites i) (ofVec k (V x idx)).val) α))
    (idx : Fin N) (j : Fin m) (T : Fin (2 ^ k)) :
    B.Grow (1 + p * 4) (fun D => D.Has (fun x => dFE sites (Tt x) (V x idx) j T)) := by
  have hf : ∀ i ∈ List.finRange p, B.Has (fun x =>
      if submask T.val (siteMask (sites i)) then
        derivTable (fun α => Tt x i α j) (extractS (sites i) (ofVec k (V x idx)).val)
          (extractS (sites i) T.val)
      else false) := by
    intro i _
    by_cases hsm : submask T.val (siteMask (sites i)) = true
    · exact has_congr (hdt idx i j (extractS (sites i) T.val)) (fun x => by simp [hsm])
    · exact has_congr h0 (fun x => by simp [hsm])
  refine (B.xorList (List.finRange p) _ hf).weaken (by simp) (fun D hD => ?_)
  exact hD

private def eqCostS (k p : Nat) : Nat := k * (1 + p * 4) + k * (1 + k * 5) + rkCost k k

private def levelCostS (k m p b : Nat) : Nat :=
  k * (p * (m * ((2 * b + 1) * (2 ^ b * 4)))) + (m * p * 2 ^ b) * eqCostS k p +
    k * (k * (1 + k * 5))

private lemma length_levelEqs_le (p b m s : Nat) :
    (levelEqs p b m s).length ≤ m * p * 2 ^ b := by
  unfold levelEqs
  have h1 : ∀ (j : Fin m), ((List.finRange p).flatMap fun i =>
      ((List.finRange (2 ^ b)).filter fun α => decide (popcount b α.val = s)).map fun α =>
        (j, i, α)).length ≤ p * 2 ^ b := by
    intro j
    have hle : ∀ (l : List (Fin p)), (l.flatMap fun i =>
        ((List.finRange (2 ^ b)).filter fun α => decide (popcount b α.val = s)).map fun α =>
          (j, i, α)).length ≤ l.length * 2 ^ b := by
      intro l; induction l with
      | nil => simp
      | cons i l ih =>
        simp only [List.flatMap_cons, List.length_append, List.length_map, List.length_cons]
        have hf : ((List.finRange (2 ^ b)).filter fun α =>
            decide (popcount b α.val = s)).length ≤ 2 ^ b :=
          (List.length_filter_le _ _).trans (by simp)
        nlinarith
    simpa using hle (List.finRange p)
  have h2 : ∀ (l : List (Fin m)), (l.flatMap fun j =>
      (List.finRange p).flatMap fun i =>
        ((List.finRange (2 ^ b)).filter fun α => decide (popcount b α.val = s)).map fun α =>
          (j, i, α)).length ≤ l.length * (p * 2 ^ b) := by
    intro l; induction l with
    | nil => simp
    | cons j l ih =>
      simp only [List.flatMap_cons, List.length_append, List.length_cons]
      have := h1 j; nlinarith
  have h3 := h2 (List.finRange m)
  simp only [List.length_finRange] at h3
  nlinarith

private lemma grow_subVLevel {n k m p b : Nat} (sites : Fin p → Fin b → Fin k) (B : Bank n)
    (h0 : B.Has (fun _ => false)) (h1 : B.Has (fun _ => true))
    (Tt : (Fin n → Bool) → Fin p → Fin (2 ^ b) → Fin m → Bool)
    (hT : ∀ i z j, B.Has (fun x => Tt x i z j))
    (s : Nat) (V : (Fin n → Bool) → Fin k → Vec k)
    (hV : ∀ idx c, B.Has (fun x => V x idx c)) :
    B.Grow (levelCostS k m p b)
      (fun D => ∀ idx c, D.Has (fun x => subVLevel sites (Tt x) s (V x) idx c)) := by
  obtain ⟨D1, e1, c1, hdt⟩ := grow_dTables sites B Tt hT V hV
  let stepU : ((Fin n → Bool) → Fin k → Vec k) → (Fin m × Fin p × Fin (2 ^ b)) →
      (Fin n → Bool) → Fin k → Vec k :=
    fun U eq x => subVLevelEq sites (Tt x) (V x) (U x) eq
  have hU0 : ∀ row c, D1.Has (fun _ : Fin n → Bool => stdBasis k row c) :=
    fun row c => has_constBool (e1 h0) (e1 h1) _
  obtain ⟨D3, e3, c3, hU⟩ := Bank.foldGrow D1 (levelEqs p b m s) (fun _ => stdBasis k) stepU
    (fun U D => ∀ row c, D.Has (fun x => U x row c)) (eqCostS k p) hU0 (by
      intro D e U eq _ hUcur
      rcases eq with ⟨j, i0, α⟩
      let T : Fin (2 ^ k) := embedS (sites i0) α.val
      obtain ⟨E1, ee1, cc1, hcol⟩ := D.collectFin k
        (fun idx x => dFE sites (Tt x) (V x idx) j T) (1 + p * 4)
        (fun E eE idx => grow_dFE sites E (eE (e (e1 h0))) Tt V
          (fun a i' j' α' => eE (e (hdt a i' j' α'))) idx j T)
      obtain ⟨E2, ee2, cc2, hc⟩ := E1.collectFin k
        (fun row x => vecDot (U x row) (fun idx => dFE sites (Tt x) (V x idx) j T))
        (1 + k * 5) (fun E eE row =>
          grow_vecDot E (fun x => U x row) (fun x idx => dFE sites (Tt x) (V x idx) j T)
            (fun idx => eE (ee1 (hUcur row idx))) (fun idx => eE (hcol idx)))
      obtain ⟨E3, ee3, cc3, ⟨_, hrk⟩⟩ := grow_restrictKernelStep E2
        (ee2 (ee1 (e (e1 h0)))) (ee2 (ee1 (e (e1 h1)))) U
        (fun x row => vecDot (U x row) (fun idx => dFE sites (Tt x) (V x idx) j T))
        (fun row idx => ee2 (ee1 (hUcur row idx))) hc
      exact ⟨E3, Bank.ext_trans ee1 (Bank.ext_trans ee2 ee3), by unfold eqCostS; omega, hrk⟩)
  let Ufin : (Fin n → Bool) → Fin k → Vec k := fun x =>
    (levelEqs p b m s).foldl (subVLevelEq sites (Tt x) (V x)) (stdBasis k)
  have hUfin : ∀ row c, D3.Has (fun x => Ufin x row c) := fun row c =>
    has_congr (hU row c) (fun x => by
      have hfl := foldl_apply'
        (fun acc eq y => subVLevelEq sites (Tt y) (V y) acc eq)
        (fun _ => stdBasis k) (levelEqs p b m s) x
      exact congrFun (congrFun hfl row) c)
  obtain ⟨D4, e4, c4, hres⟩ := collectPropFin D3
    (fun (row : Fin k) D => ∀ c : Fin k, D.Has (fun x => vecLinComb (V x) (Ufin x row) c))
    (fun _ _ _ e h c => e (h c)) (k * (1 + k * 5)) (fun D e row =>
      grow_vecLinComb D V (fun x => Ufin x row)
        (fun idx c => e (e3 (e1 (hV idx c)))) (fun idx => e (hUfin row idx)))
  have hlen := length_levelEqs_le p b m s
  have hmul_le : (levelEqs p b m s).length * eqCostS k p ≤ (m * p * 2 ^ b) * eqCostS k p :=
    Nat.mul_le_mul_right _ hlen
  exact ⟨D4, Bank.ext_trans e1 (Bank.ext_trans e3 e4), by
    unfold levelCostS; omega, hres⟩

private lemma grow_subVChain {n k m p b : Nat} (sites : Fin p → Fin b → Fin k) (B : Bank n)
    (h0 : B.Has (fun _ => false)) (h1 : B.Has (fun _ => true))
    (Tt : (Fin n → Bool) → Fin p → Fin (2 ^ b) → Fin m → Bool)
    (hT : ∀ i z j, B.Has (fun x => Tt x i z j)) :
    B.Grow (b * levelCostS k m p b)
      (fun D => ∀ idx c, D.Has (fun x => subVChain sites (Tt x) idx c)) := by
  let levels := (List.range b).reverse.map (· + 1)
  let stepL : ((Fin n → Bool) → Fin k → Vec k) → Nat → (Fin n → Bool) → Fin k → Vec k :=
    fun V s x => subVLevel sites (Tt x) s (V x)
  have hV0 : ∀ idx c, B.Has (fun _ : Fin n → Bool => stdBasis k idx c) :=
    fun idx c => has_constBool h0 h1 _
  have hfold := Bank.foldGrow B levels (fun _ => stdBasis k) stepL
    (fun V D => ∀ idx c, D.Has (fun x => V x idx c)) (levelCostS k m p b) hV0 (by
      intro D e V s _ hV
      exact grow_subVLevel sites D (e h0) (e h1) Tt (fun i z j => e (hT i z j)) s V hV)
  refine hfold.weaken (by simp [levels]) (fun D hD idx c => ?_)
  exact has_congr (hD idx c) (fun x => by
    have hfl := foldl_apply'
      (fun acc s y => subVLevel sites (Tt y) s acc)
      (fun _ => stdBasis k) levels x
    exact congrFun (congrFun hfl idx) c)

private lemma grow_Lrows {n k m p b : Nat} (sites : Fin p → Fin b → Fin k) (B : Bank n)
    (h0 : B.Has (fun _ => false))
    (Tt : (Fin n → Bool) → Fin p → Fin (2 ^ b) → Fin m → Bool)
    (hT : ∀ i z j, B.Has (fun x => Tt x i z j))
    (pdv : (Fin n → Bool) → Vec k) (pyv : (Fin n → Bool) → Vec m)
    (hpd : ∀ l, B.Has (fun x => pdv x l)) (hpy : ∀ j, B.Has (fun x => pyv x j))
    (hV : ∀ idx c, B.Has (fun x => subVChain sites (Tt x) idx c)) :
    B.Grow (k * (p * (m * ((2 * b + 1) * (2 ^ b * 4)))) + k * ((k + m) * (1 + p * 4 + 1)))
      (fun D => ∀ idx r, D.Has (fun x => LrowsOf sites (Tt x) (pdv x) (pyv x) idx r)) := by
  obtain ⟨D1, e1, c1, hdt⟩ := grow_dTables sites B Tt hT (fun x => subVChain sites (Tt x)) hV
  obtain ⟨D2, e2, c2, hL⟩ := collectPropFin D1
    (fun idx D => ∀ r, D.Has (fun x => LrowsOf sites (Tt x) (pdv x) (pyv x) idx r))
    (fun _ _ _ e h r => e (h r)) ((k + m) * (1 + p * 4 + 1)) (fun D e idx =>
      D.collectFin (k + m) _ (1 + p * 4 + 1) (fun E ee r => by
        by_cases hr : r.val < k
        · refine (Bank.meet (ee (e (e1 (hpd ⟨r.val, hr⟩)))) (ee (e (e1 (hV idx ⟨r.val, hr⟩))))).weaken
            (by omega) (fun F hF => has_congr hF (fun x => ?_))
          unfold LrowsOf phiV; simp only [hr, ↓reduceDIte]
        · have hj : r.val - k < m := by have := r.isLt; omega
          obtain ⟨F1, ef1, cf1, hd⟩ := grow_dFE sites E (ee (e (e1 h0))) Tt
            (fun x => subVChain sites (Tt x)) (fun a i j α => ee (e (hdt a i j α))) idx
            ⟨r.val - k, hj⟩ ⟨0, Nat.two_pow_pos k⟩
          obtain ⟨F2, ef2, cf2, hm⟩ := Bank.meet (ef1 (ee (e (e1 (hpy ⟨r.val - k, hj⟩))))) hd
          refine ⟨F2, Bank.ext_trans ef1 ef2, by omega, has_congr hm (fun x => ?_)⟩
          unfold LrowsOf phiV respV; simp only [hr, ↓reduceDIte]))
  exact ⟨D2, Bank.ext_trans e1 e2, by omega, hL⟩

private lemma grow_kerFold {n N c : Nat} (B : Bank n)
    (h0 : B.Has (fun _ => false)) (h1 : B.Has (fun _ => true))
    (U : (Fin n → Bool) → Fin N → Vec c) (hU : ∀ i j, B.Has (fun x => U x i j))
    (cols : List (Fin c)) :
    B.Grow (cols.length * rkCost N c)
      (fun D => ∀ i j, D.Has (fun x => kerFold (U x) cols i j)) := by
  let stepK : ((Fin n → Bool) → Fin N → Vec c) → Fin c → (Fin n → Bool) → Fin N → Vec c :=
    fun W r x => restrictKernelStep (W x) (fun i => W x i r)
  have hfold := Bank.foldGrow B cols U stepK (fun W D => ∀ i j, D.Has (fun x => W x i j))
    (rkCost N c) hU (by
      intro D e W r _ hW
      obtain ⟨E, ee, ce, ⟨_, hrk⟩⟩ := grow_restrictKernelStep D (e h0) (e h1) W
        (fun x i => W x i r) hW (fun i => hW i r)
      exact ⟨E, ee, ce, hrk⟩)
  refine hfold.weaken (le_refl _) (fun D hD i j => has_congr (hD i j) (fun x => ?_))
  have hfl := foldl_apply' (fun acc r (_ : Fin n → Bool) => restrictKernelStep acc (fun i => acc i r))
    U cols x
  exact congrFun (congrFun hfl i) j

private def totalCost (k m p b : Nat) : Nat :=
  2 + b * levelCostS k m p b +
    (k * (p * (m * ((2 * b + 1) * (2 ^ b * 4)))) + k * ((k + m) * (1 + p * 4 + 1))) +
    (k + m) * 1 + echCost k (k + m) + (k + m) * (1 + (k + m) * 8) + (1 + (k + m)) + 1 +
    (k + m + k) * rkCost k (k + m + k) + echCost k (k + m + k) +
    (k + m + k) * ((k + m + k + 1) * 4) + (k + 1) * 1 + (k + 1) * 9

private lemma length_colsK (c k : Nat) : (colsK c k).length ≤ c + k := by
  unfold colsK
  exact (List.length_filter_le _ _).trans (by simp)

private lemma build_grow {k m p b : Nat} (sites : Fin p → Fin b → Fin k) :
    (Bank.empty (inLen k m p b)).Grow (totalCost k m p b)
      (fun B => B.Has (fun x => spec sites (decTab x) (decPd x) (decVd x) (decPy x) (decVy x)
        (decT x))) := by
  let n := inLen k m p b
  let B0 := Bank.empty n
  have hTab : ∀ i z j, B0.Has (fun x => decTab x i z j) := fun i z j => Bank.input _
  have hPd : ∀ l, B0.Has (fun x => decPd x l) := fun l => Bank.input _
  have hVd : ∀ l, B0.Has (fun x => decVd x l) := fun l => Bank.input _
  have hPy : ∀ l, B0.Has (fun x => decPy x l) := fun l => Bank.input _
  have hVy : ∀ l, B0.Has (fun x => decVy x l) := fun l => Bank.input _
  have hTv : ∀ l, B0.Has (fun x => decT x l) := fun l => Bank.input _
  obtain ⟨D0a, e0a, c0a, h0a⟩ := B0.const false
  obtain ⟨D0, e0b, c0b, h1⟩ := D0a.const true
  have e0 : B0.Ext D0 := Bank.ext_trans e0a e0b
  have h0 : D0.Has (fun _ => false) := e0b h0a
  -- Stage 1: the linear-structure space
  obtain ⟨D1, e1, c1, hV⟩ := grow_subVChain sites D0 h0 h1 (fun x => decTab x)
    (fun i z j => e0 (hTab i z j))
  have e01 : B0.Ext D1 := Bank.ext_trans e0 e1
  -- Stage 2: pinned images of the basis
  obtain ⟨D2, e2, c2, hL⟩ := grow_Lrows sites D1 (e1 h0) (fun x => decTab x)
    (fun i z j => e01 (hTab i z j)) (fun x => decPd x) (fun x => decPy x)
    (fun l => e01 (hPd l)) (fun l => e01 (hPy l)) hV
  have e02 : B0.Ext D2 := Bank.ext_trans e01 e2
  have e12 : D1.Ext D2 := e2
  -- Stage 3: target vector
  obtain ⟨D3, e3, c3, htg⟩ := D2.collectFin (k + m)
    (fun r x => tgtV (decPd x) (decVd x) (decPy x) (decVy x) r) 1 (fun E ee r => by
      by_cases hr : r.val < k
      · refine (Bank.meet (ee (e02 (hPd ⟨r.val, hr⟩))) (ee (e02 (hVd ⟨r.val, hr⟩)))).weaken
          (le_refl _) (fun F hF => has_congr hF (fun x => ?_))
        unfold tgtV; simp only [hr, ↓reduceDIte]
      · have hj : r.val - k < m := by have := r.isLt; omega
        refine (Bank.meet (ee (e02 (hPy ⟨r.val - k, hj⟩))) (ee (e02 (hVy ⟨r.val - k, hj⟩)))).weaken
          (le_refl _) (fun F hF => has_congr hF (fun x => ?_))
        unfold tgtV; simp only [hr, ↓reduceDIte])
  have e03 : B0.Ext D3 := Bank.ext_trans e02 e3
  have e13 : D1.Ext D3 := Bank.ext_trans e12 e3
  -- Stage 4: echelon of the pinned images and consistency
  obtain ⟨D4, e4, c4, ⟨hLp, hLv⟩⟩ := grow_echelon D3 (e13 (e1 h0)) (e13 (e1 h1))
    (fun x => LrowsOf sites (decTab x) (decPd x) (decPy x)) (fun i j => e3 (hL i j))
  obtain ⟨D5, e5, c5, hred⟩ := grow_echelonReduce D4
    (fun x => (echelon (LrowsOf sites (decTab x) (decPd x) (decPy x))).hasP)
    (fun x => (echelon (LrowsOf sites (decTab x) (decPd x) (decPy x))).piv)
    (fun x => tgtV (decPd x) (decVd x) (decPy x) (decVy x)) hLp hLv (fun r => e4 (htg r))
  obtain ⟨D6, e6, c6, hany⟩ := grow_anyBit D5 _ hred
  obtain ⟨D7, e7, c7, hcons⟩ := Bank.inv hany
  have e17 : D1.Ext D7 := Bank.ext_trans e13 (Bank.ext_trans e4 (Bank.ext_trans e5
    (Bank.ext_trans e6 e7)))
  have e27 : D2.Ext D7 := Bank.ext_trans e3 (Bank.ext_trans e4 (Bank.ext_trans e5
    (Bank.ext_trans e6 e7)))
  have e07 : B0.Ext D7 := Bank.ext_trans e01 e17
  -- Stage 5: kernel of the pinned map
  have haug : ∀ idx r, D7.Has (fun x => augV (LrowsOf sites (decTab x) (decPd x) (decPy x))
      (subVChain sites (decTab x)) idx r) := by
    intro idx r
    by_cases hr : r.val < k + m
    · exact has_congr (e27 (hL idx ⟨r.val, hr⟩)) (fun x => by unfold augV; simp only [hr, ↓reduceDIte])
    · exact has_congr (e17 (hV idx ⟨r.val - (k + m), by have := r.isLt; omega⟩))
        (fun x => by unfold augV; simp only [hr, ↓reduceDIte])
  obtain ⟨D8, e8, c8, hK⟩ := grow_kerFold D7 (e17 (e1 h0)) (e17 (e1 h1))
    (fun x => augV (LrowsOf sites (decTab x) (decPd x) (decPy x)) (subVChain sites (decTab x)))
    haug (colsK (k + m) k)
  have e18 : D1.Ext D8 := Bank.ext_trans e17 e8
  obtain ⟨D9, e9, c9, ⟨hKp, _⟩⟩ := grow_echelon D8 (e18 (e1 h0)) (e18 (e1 h1))
    (fun x => kerKOf sites (decTab x) (decPd x) (decPy x)) hK
  have e19 : D1.Ext D9 := Bank.ext_trans e18 e9
  obtain ⟨D10, e10, c10, hcnt⟩ := grow_cntEq_prefix D9 (e19 (e1 h0)) (e19 (e1 h1))
    (fun x => (echelon (kerKOf sites (decTab x) (decPd x) (decPy x))).hasP) hKp
    (k + m + k) (le_refl _)
  have e7_10 : D7.Ext D10 := Bank.ext_trans e8 (Bank.ext_trans e9 e10)
  -- Stage 6: the count vector and the comparison
  obtain ⟨D11, e11, c11, hcv⟩ := D10.collectFin (k + 1)
    (fun i x => consOf sites (decTab x) (decPd x) (decVd x) (decPy x) (decVy x) &&
      cntEq (echelon (kerKOf sites (decTab x) (decPd x) (decPy x))).hasP (k + m + k) i.val) 1
    (fun E ee i => Bank.meet (ee (e7_10 hcons))
      (ee (hcnt (k + m + k) (le_refl _) ⟨i.val, by omega⟩)))
  obtain ⟨D12, e12', c12, hle⟩ := grow_leVec D11 (e11 (e7_10 (e17 (e1 h1))))
    (fun x => decT x)
    (fun x i => consOf sites (decTab x) (decPd x) (decVd x) (decPy x) (decVy x) &&
      cntEq (echelon (kerKOf sites (decTab x) (decPd x) (decPy x))).hasP (k + m + k) i.val)
    (fun i => e11 (e7_10 (e07 (hTv i)))) hcv
  have hlenc := length_colsK (k + m) k
  have hmul : (colsK (k + m) k).length * rkCost k (k + m + k) ≤
      (k + m + k) * rkCost k (k + m + k) := Nat.mul_le_mul_right _ hlenc
  refine ⟨D12, Bank.ext_trans e0 (Bank.ext_trans e1 (Bank.ext_trans e2 (Bank.ext_trans e3
    (Bank.ext_trans e4 (Bank.ext_trans e5 (Bank.ext_trans e6 (Bank.ext_trans e7
    (Bank.ext_trans e8 (Bank.ext_trans e9 (Bank.ext_trans e10 (Bank.ext_trans e11 e12'))))))))))),
    ?_, ?_⟩
  · have hz : B0.gates.length = 0 := rfl
    rw [hz] at c0a
    show D12.gates.length ≤ 0 + totalCost k m p b
    unfold totalCost
    omega
  · exact has_congr hle (fun x => rfl)

-- ============================================================
-- PART F: Size bound and the finished circuit
-- ============================================================

private def totalCostQ (k m p b Q : Nat) : Nat :=
  2 + b * (k * (p * (m * ((2 * b + 1) * (Q * 4)))) + (m * p * Q) * eqCostS k p +
      k * (k * (1 + k * 5))) +
    (k * (p * (m * ((2 * b + 1) * (Q * 4)))) + k * ((k + m) * (1 + p * 4 + 1))) +
    (k + m) * 1 + echCost k (k + m) + (k + m) * (1 + (k + m) * 8) + (1 + (k + m)) + 1 +
    (k + m + k) * rkCost k (k + m + k) + echCost k (k + m + k) +
    (k + m + k) * ((k + m + k + 1) * 4) + (k + 1) * 1 + (k + 1) * 9

private lemma totalCost_eq (k m p b : Nat) : totalCost k m p b = totalCostQ k m p b (2 ^ b) := by
  unfold totalCost totalCostQ levelCostS
  rfl

private lemma totalCostQ_mono {k m p b Q S : Nat} (hk : k ≤ S) (hm : m ≤ S) (hp : p ≤ S)
    (hb : b ≤ S) : totalCostQ k m p b Q ≤ totalCostQ S S S S Q := by
  unfold totalCostQ eqCostS echCost
  unfold rkCost
  gcongr

private lemma pow_le_big {S Q : Nat} (hS : 1 ≤ S) (hQ : 1 ≤ Q) {i : Nat} (hi : i ≤ 8) :
    S ^ i ≤ S ^ 8 * Q ∧ S ^ i * Q ≤ S ^ 8 * Q := by
  have h1 : S ^ i ≤ S ^ 8 := Nat.pow_le_pow_right hS hi
  refine ⟨h1.trans (Nat.le_mul_of_pos_right _ hQ), Nat.mul_le_mul_right Q h1⟩

private lemma totalCostQ_le {S Q : Nat} (hS : 1 ≤ S) (hQ : 1 ≤ Q) :
    totalCostQ S S S S Q ≤ 2 ^ 16 * S ^ 8 * Q := by
  obtain ⟨a0, b0⟩ := pow_le_big hS hQ (i := 0) (by omega)
  obtain ⟨a1, b1⟩ := pow_le_big hS hQ (i := 1) (by omega)
  obtain ⟨a2, b2⟩ := pow_le_big hS hQ (i := 2) (by omega)
  obtain ⟨a3, b3⟩ := pow_le_big hS hQ (i := 3) (by omega)
  obtain ⟨a4, b4⟩ := pow_le_big hS hQ (i := 4) (by omega)
  obtain ⟨a5, b5⟩ := pow_le_big hS hQ (i := 5) (by omega)
  obtain ⟨a6, b6⟩ := pow_le_big hS hQ (i := 6) (by omega)
  obtain ⟨a7, b7⟩ := pow_le_big hS hQ (i := 7) (by omega)
  unfold totalCostQ eqCostS echCost
  unfold rkCost
  simp only [pow_zero, pow_one, one_mul] at a0 b0 a1 b1
  nlinarith

private lemma totalCost_le (k m p b : Nat) :
    totalCost k m p b ≤ 2 ^ 16 * (k + m + p + b + 2) ^ 8 * 2 ^ b := by
  rw [totalCost_eq]
  exact (totalCostQ_mono (by omega) (by omega) (by omega) (by omega)).trans
    (totalCostQ_le (by omega) Nat.one_le_two_pow)

end Synth

lemma build_main {k m p b : Nat} (sites : Fin p → Fin b → Fin k)
    (hinj : ∀ i, Function.Injective (sites i)) :
    ∃ C : PEqualNP.CircuitLowerBounds.Circuit,
      PEqualNP.MetaComplexity.FanInTwo C ∧
      PEqualNP.MetaComplexity.NestedCover.ReadsBack (inLen k m p b) C ∧
      C.size ≤ 2 ^ 16 * (k + m + p + b + 2) ^ 8 * 2 ^ b ∧
      ∀ x : Fin (inLen k m p b) → Bool, C.eval (List.ofFn x) =
        spec sites (decTab x) (decPd x) (decVd x) (decPy x) (decVy x) (decT x) := by
  obtain ⟨C, h1, h2, h3, h4⟩ := Builder.Bank.finish (build_grow (k := k) (m := m) sites)
  exact ⟨C, h1, h2, h3.trans (totalCost_le k m p b), h4⟩

end PEqualNP.Outside.L_lib_906

theorem PEqualNP.Outside.L_lib_906 : ∀ (k m p b : Nat) (sites : Fin p → Fin b → Fin k),
  (∀ i, Function.Injective (sites i)) →
  let bits := fun (n x : Nat) => (List.range n).map (fun j => x.testBit j)
  let addr := fun (i : Fin p) (w : Nat) =>
    (List.finRange b).foldl (fun acc j =>
      acc ||| ((w.testBit (sites i j).val).toNat <<< j.val)) 0 % 2^b
  ∃ C : PEqualNP.CircuitLowerBounds.Circuit,
    PEqualNP.MetaComplexity.FanInTwo C ∧
    PEqualNP.MetaComplexity.NestedCover.ReadsBack (p*2^b*m+2*k+2*m+(k+1)) C ∧
    C.size ≤ 2^16 * (k+m+p+b+2)^8 * 2^b ∧
    ∀ (T : Fin p → Fin (2^b) → Fin m → Bool)
      (pd vd : Fin (2^k)) (py vy : Fin (2^m)) (t : Fin (2^(k+1))),
      let f := fun (w : Nat) (j : Fin m) =>
        (List.finRange p).foldl (fun acc i =>
          xor acc (T i (Fin.ofNat (2^b) (addr i w)) j)) false
      let good := fun (d : Fin (2^k)) =>
        (d.val &&& pd.val) = (vd.val &&& pd.val) ∧
        ∃ y : Fin m → Bool, (∀ j, py.val.testBit j.val = true → y j = vy.val.testBit j.val) ∧
          ∀ (w : Fin (2^k)) (j : Fin m), xor (f (w.val ^^^ d.val) j) (f w.val j) = y j
      let entries := (List.finRange p).flatMap (fun i =>
        (List.finRange (2^b)).flatMap (fun z => List.ofFn (T i z)))
      C.eval (entries ++ bits k pd.val ++ bits k vd.val ++ bits m py.val ++
        bits m vy.val ++ bits (k+1) t.val) = decide (t.val ≤ Nat.card {d : Fin (2^k) // good d}) := by
  intro k m p b sites hinj bits addr
  obtain ⟨C, hfan, hback, hsize, heval⟩ := PEqualNP.Outside.L_lib_906.build_main sites hinj
  refine ⟨C, hfan, hback, hsize, ?_⟩
  intro T pd vd py vy t f good entries
  have hL : entries ++ bits k pd.val ++ bits k vd.val ++ bits m py.val ++ bits m vy.val ++
      bits (k + 1) t.val = PEqualNP.Outside.L_lib_906.inList T pd vd py vy t := rfl
  rw [hL]
  have hx := PEqualNP.Outside.L_lib_906.ofFn_getD (PEqualNP.Outside.L_lib_906.inList T pd vd py vy t)
    (PEqualNP.Outside.L_lib_906.length_inList T pd vd py vy t)
  rw [← hx, heval, PEqualNP.Outside.L_lib_906.dec_tab, PEqualNP.Outside.L_lib_906.dec_pd,
    PEqualNP.Outside.L_lib_906.dec_vd, PEqualNP.Outside.L_lib_906.dec_py,
    PEqualNP.Outside.L_lib_906.dec_vy, PEqualNP.Outside.L_lib_906.dec_t,
    PEqualNP.Outside.L_lib_906.spec_eq hinj]
  have hcard : Nat.card {d : Fin (2 ^ k) // good d} =
      Nat.card {d : Fin (2 ^ k) // PEqualNP.Outside.L_lib_906.goodS sites T pd vd py vy d} :=
    Nat.card_congr (Equiv.subtypeEquivRight (fun d =>
      PEqualNP.Outside.L_lib_906.good_bridge sites T pd vd py vy f
        (fun x j => PEqualNP.Outside.L_lib_906.f_eq sites T x j) d))
  rw [hcard]
