import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_32039

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

-- ============================================================
-- PART 2: Bitwise rot / step / state & Window Dependency
-- ============================================================

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

def parity (k mask x : Nat) : Bool :=
  (List.range k).foldl (fun b i => xor b (mask.testBit i && x.testBit i)) false

def winSize (k r : Nat) : Nat := min k (max (6 * r + 1) (7 * r - 1))

def loShift (col : Bool) (r : Nat) : Nat :=
  if col then max (2 * r + 3) (3 * r + 1) else if r = 0 then 1 else 2 * r

lemma winSize_pos {k r : Nat} (hk : 0 < k) : 0 < winSize k r := by
  unfold winSize; omega

lemma winSize_le (k r : Nat) : winSize k r ≤ k := Nat.min_le_left _ _

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

-- Window extraction and zero-padded embedding
def extract (k b p w : Nat) : Fin (2 ^ b) :=
  ⟨(List.range b).foldl (fun acc s => acc ||| ((w.testBit ((p + s) % k)).toNat <<< s)) 0, by
    apply Nat.lt_pow_two_of_testBit
    intro s hs
    rw [testBit_foldl_or]
    simp [Nat.not_lt_of_ge hs]⟩

lemma testBit_extract (k b p w s : Nat) :
    (extract k b p w).val.testBit s = (decide (s < b) && w.testBit ((p + s) % k)) := by
  unfold extract
  dsimp only
  rw [testBit_foldl_or]
  simp

def embed (k b p α : Nat) : Nat :=
  (List.range b).foldl (fun acc s => acc ||| ((α.testBit s).toNat <<< ((p + s) % k))) 0

private lemma testBit_foldl_or_map (f : Nat → Nat) (g : Nat → Bool) (xs : List Nat)
    (acc q : Nat) :
    (xs.foldl (fun a s => a ||| ((g s).toNat <<< f s)) acc).testBit q =
      (acc.testBit q || xs.any (fun s => decide (f s = q) && g s)) := by
  induction xs generalizing acc with
  | nil => simp
  | cons s xs ih =>
    simp only [List.foldl_cons, ih, Nat.testBit_or, Nat.testBit_shiftLeft, List.any_cons]
    by_cases hfq : f s = q
    · subst hfq; cases g s <;> simp [Bool.or_assoc]
    · by_cases hle : f s ≤ q
      · have hsub : 1 ≤ q - f s := by omega
        have hbt : (g s).toNat.testBit (q - f s) = false := by
          cases g s
          · simp
          · exact Nat.testBit_lt_two_pow (lt_of_lt_of_le (by omega : 1 < 2 ^ 1)
              (Nat.pow_le_pow_right Nat.zero_lt_two hsub))
        simp [hle, hbt, hfq]
      · simp [hle, hfq]

lemma embed_lt {k b p α : Nat} (hk : 0 < k) : embed k b p α < 2 ^ k := by
  apply Nat.lt_pow_two_of_testBit
  intro q hq
  unfold embed
  rw [testBit_foldl_or_map]
  simp only [Nat.zero_testBit, Bool.false_or, List.any_eq_false, List.mem_range]
  intro s _
  have hm : (p + s) % k < k := Nat.mod_lt _ hk
  have hne : (p + s) % k ≠ q := by omega
  simp [hne]

lemma mod_add_inj {k p s1 s2 : Nat} (hs1 : s1 < k) (hs2 : s2 < k)
    (heq : (p + s1) % k = (p + s2) % k) : s1 = s2 := by
  have hk : 0 < k := by omega
  have h1 : (p % k + s1) % k = (p % k + s2) % k := by
    simpa [Nat.add_mod] using heq
  have hp : p % k < k := Nat.mod_lt _ hk
  by_cases ha : p % k + s1 < k <;> by_cases hb : p % k + s2 < k
  · rw [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at h1; omega
  · have hge : k ≤ p % k + s2 := by omega
    have hlt : p % k + s2 - k < k := by omega
    rw [Nat.mod_eq_of_lt ha, Nat.mod_eq_sub_mod hge, Nat.mod_eq_of_lt hlt] at h1
    omega
  · have hge : k ≤ p % k + s1 := by omega
    have hlt : p % k + s1 - k < k := by omega
    rw [Nat.mod_eq_sub_mod hge, Nat.mod_eq_of_lt hlt, Nat.mod_eq_of_lt hb] at h1
    omega
  · have hge1 : k ≤ p % k + s1 := by omega
    have hlt1 : p % k + s1 - k < k := by omega
    have hge2 : k ≤ p % k + s2 := by omega
    have hlt2 : p % k + s2 - k < k := by omega
    rw [Nat.mod_eq_sub_mod hge1, Nat.mod_eq_of_lt hlt1,
        Nat.mod_eq_sub_mod hge2, Nat.mod_eq_of_lt hlt2] at h1
    omega

lemma testBit_embed_win {k b p α s : Nat} (hb : b ≤ k) (hs : s < b) :
    (embed k b p α).testBit ((p + s) % k) = α.testBit s := by
  unfold embed
  rw [testBit_foldl_or_map]
  simp only [Nat.zero_testBit, Bool.false_or]
  cases h : α.testBit s
  · simp only [List.any_eq_false, List.mem_range]
    intro s' hs'
    by_cases he : (p + s') % k = (p + s) % k
    · have hss : s' = s := mod_add_inj (by omega) (by omega) he
      subst hss; simp [h]
    · simp [he]
  · simp only [List.any_eq_true, List.mem_range]
    exact ⟨s, hs, by simp [h]⟩

lemma testBit_embed_general {k b p α q : Nat} (hb : b ≤ k) (hq : q < k) :
    (embed k b p α).testBit q =
      let s := (q + k - p % k) % k
      decide (s < b) && α.testBit s := by
  have hk : 0 < k := by omega
  have hp : p % k < k := Nat.mod_lt _ hk
  set s := (q + k - p % k) % k
  have hps : (p + s) % k = q := by
    have hq_mod : (p % k + (q + k - p % k)) % k = q := by
      have : p % k + (q + k - p % k) = q + k := by omega
      rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt hq]
    calc (p + s) % k = (p % k + (q + k - p % k) % k) % k := by rw [Nat.add_mod]; simp [s]
      _ = (p % k + (q + k - p % k)) % k := Nat.add_mod_mod _ _ _
      _ = q := hq_mod
  by_cases hsb : s < b
  · rw [← hps, testBit_embed_win hb hsb]
    simp [hsb]
  · simp only [hsb, decide_false, Bool.false_and]
    unfold embed
    rw [testBit_foldl_or_map]
    simp only [Nat.zero_testBit, Bool.false_or, List.any_eq_false, List.mem_range]
    intro s' hs'
    by_cases he : (p + s') % k = q
    · have hss : s' = s := mod_add_inj (by omega) (Nat.mod_lt _ hk) (he.trans hps.symm)
      omega
    · simp [he]

lemma embed_extract_eq_self {k p w : Nat} (hw : w < 2 ^ k) :
    embed k k p (extract k k p w).val = w := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp at hw; subst hw; simp [embed]
  · apply Nat.eq_of_testBit_eq
    intro q
    by_cases hq : q < k
    · rw [testBit_embed_general (le_refl k) hq]
      have hs : (q + k - p % k) % k < k := Nat.mod_lt _ hk
      simp only [hs, decide_true, Bool.true_and, testBit_extract]
      have hp : p % k < k := Nat.mod_lt _ hk
      have hps : (p + (q + k - p % k) % k) % k = q := by
        calc (p + (q + k - p % k) % k) % k
            = (p % k + (q + k - p % k) % k) % k := by rw [Nat.add_mod, Nat.mod_mod]
          _ = (p % k + (q + k - p % k)) % k := by rw [Nat.add_mod_mod]
          _ = (q + k) % k := by congr 1; omega
          _ = q := by rw [Nat.add_mod_right, Nat.mod_eq_of_lt hq]
      rw [hps]
    · have h1 : (embed k k p (extract k k p w).val).testBit q = false :=
        Nat.testBit_lt_two_pow ((embed_lt hk).trans_le (Nat.pow_le_pow_right Nat.zero_lt_two (by omega)))
      have h2 : w.testBit q = false :=
        Nat.testBit_lt_two_pow (hw.trans_le (Nat.pow_le_pow_right Nat.zero_lt_two (by omega)))
      rw [h1, h2]

-- Prefix of state fold for round induction
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

private lemma mod_sub_shift {k base d s : Nat} (hk : 0 < k) (h1 : d ≤ base) (h2 : s ≤ base - d) :
    ((base - d) % k + k - s % k) % k = (base - (d + s)) % k := by
  have hs : s % k < k := Nat.mod_lt _ hk
  have hsub : base - d = (base - (d + s)) + s := by omega
  have hL : (base - d) % k + k - s % k + s % k = (base - d) % k + k := by omega
  have hR : ((base - (d + s)) % k + s % k) % k = (base - d) % k := by
    rw [← Nat.add_mod, ← hsub]
  have hmod : (((base - d) % k + k - s % k) + s % k) % k =
      ((base - (d + s)) % k + s % k) % k := by
    rw [hL, Nat.add_mod_right, Nat.mod_mod, hR]
  have hlt1 : ((base - d) % k + k - s % k) % k < k := Nat.mod_lt _ hk
  have hlt2 : (base - (d + s)) % k < k := Nat.mod_lt _ hk
  have hmod2 : (((base - d) % k + k - s % k) % k + s % k) % k =
      ((base - (d + s)) % k + s % k) % k := by
    rw [Nat.mod_add_mod]; exact hmod
  rw [Nat.add_comm _ (s % k), Nat.add_comm _ (s % k)] at hmod2
  exact mod_add_inj hlt1 hlt2 hmod2

private lemma mod_add_shift {k base d : Nat} (hk : 0 < k) (h1 : d ≤ base) (e : Nat) :
    ((base - d) % k + e) % k = (base - d + e) % k := by
  rw [Nat.mod_add_mod]

theorem state_testBit_window {k r : Nat} (hk : 0 < k) (col : Bool)
    {w w' u : Nat} (hw : w < 2 ^ k) (hw' : w' < 2 ^ k) (hu : u < 2 ^ k)
    (c : Fin r → Fin (2 ^ k)) {i : Nat} (hi : i < k)
    (hwin : ∀ s < winSize k r,
      w.testBit (((i + k - loShift col r % k) % k + s) % k) =
      w'.testBit (((i + k - loShift col r % k) % k + s) % k)) :
    (state k r col w u c).testBit i = (state k r col w' u c).testBit i := by
  set b := winSize k r
  set lo := loShift col r
  set p := (i + k - lo % k) % k
  by_cases hbk : b = k
  · have hweq : w = w' := by
      apply Nat.eq_of_testBit_eq
      intro q
      by_cases hq : q < k
      · have hp : p < k := Nat.mod_lt _ hk
        set s := (q + k - p) % k
        have hs : s < b := by rw [hbk]; exact Nat.mod_lt _ hk
        have hps : (p + s) % k = q := by
          calc (p + (q + k - p) % k) % k = (p + (q + k - p)) % k := Nat.add_mod_mod _ _ _
            _ = (q + k) % k := by congr 1; omega
            _ = q := by rw [Nat.add_mod_right, Nat.mod_eq_of_lt hq]
        simpa [hps] using hwin s hs
      · rw [Nat.testBit_lt_two_pow (hw.trans_le (Nat.pow_le_pow_right Nat.zero_lt_two (by omega))),
            Nat.testBit_lt_two_pow (hw'.trans_le (Nat.pow_le_pow_right Nat.zero_lt_two (by omega)))]
    rw [hweq]
  · have hblt : b < k := lt_of_le_of_ne (winSize_le k r) hbk
    have hbeq : b = max (6 * r + 1) (7 * r - 1) := by
      unfold b winSize at hblt ⊢; omega
    -- Base offset M = k * (4*r + 4) so subtractions never underflow
    set M := k * (4 * r + 4)
    have h4r : 4 * r + 4 ≤ M := Nat.le_mul_of_pos_left _ hk
    have hlo_le : lo ≤ 3 * r + 3 := by
      show loShift col r ≤ 3 * r + 3
      cases col <;> simp [loShift, max_def] <;> split_ifs <;> omega
    have hM_lo : lo ≤ i + M := by omega
    have hwinM : ∀ s < b,
        w.testBit ((i + M - lo + s) % k) = w'.testBit ((i + M - lo + s) % k) := by
      intro s hs
      have hps : (p + s) % k = (i + M - lo + s) % k := by
        have hpM : p = (i + M - lo) % k := by
          have h1 := mod_sub_shift hk (Nat.zero_le (i + M)) hM_lo
          have h2 : (i + M) % k = i := by
            show (i + k * (4 * r + 4)) % k = i
            rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hi]
          simpa [p, h2] using h1
        rw [hpM, Nat.mod_add_mod]
      simpa [hps] using hwin s hs
    rcases Nat.eq_zero_or_pos r with rfl | hr
    · -- r = 0
      have hb1 : b = 1 := by omega
      have h0 := hwinM 0 (by omega)
      simp only [state, List.finRange_zero, List.foldl_nil, Nat.testBit_xor]
      rw [testBit_rot hw hi, testBit_rot hw' hi]
      have hlo : lo = if col then 3 else 1 := by
        show loShift col 0 = _; unfold loShift; cases col <;> simp
      have hidx : (i + k - (if col then 3 else 1) % k) % k = (i + M - lo + 0) % k := by
        have h1 := mod_sub_shift hk (Nat.zero_le (i + M)) hM_lo
        have h2 : (i + M) % k = i := by
          show (i + k * (4 * 0 + 4)) % k = i
          rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hi]
        simpa [h2, hlo] using h1
      rw [hidx, h0]
    · -- r ≥ 1, hence k > b ≥ 7, so k ≥ 8
      have hk8 : 8 ≤ k := by omega
      set g := if col then 2 else 1
      have hg_pos : 0 < g := by show 0 < if col then 2 else 1; cases col <;> simp
      have hg_le2 : g ≤ 2 := by show (if col then 2 else 1) ≤ 2; cases col <;> simp
      have hg_lt : g < k := by omega
      have hmain : ∀ t ≤ r, ∀ a ≤ (2 + 2 * g) * (r - t),
          (statePre k r col w u c t).testBit ((i + M - g * (r - t) + a) % k) =
          (statePre k r col w' u c t).testBit ((i + M - g * (r - t) + a) % k) := by
        intro t ht
        induction t with
        | zero =>
          intro a ha
          simp only [statePre_zero, Nat.sub_zero, Nat.testBit_xor]
          have hpos_lt : (i + M - g * r + a) % k < k := Nat.mod_lt _ hk
          rw [testBit_rot hw hpos_lt, testBit_rot hw' hpos_lt]
          set initRot := if col then 3 else 1
          have hgr_le2 : g * r ≤ 2 * r := Nat.mul_le_mul_right r hg_le2
          have hgr_le : g * r ≤ i + M := by omega
          have hinit_le3 : initRot ≤ 3 := by show (if col then 3 else 1) ≤ 3; cases col <;> simp
          have hinit_le : initRot ≤ i + M - g * r + a := by omega
          have hlo_ge : g * r + initRot ≤ lo := by
            show (if col then 2 else 1) * r + (if col then 3 else 1) ≤ loShift col r
            cases col <;> simp [loShift, max_def] <;> split_ifs <;> omega
          have hsub : ((i + M - g * r + a) % k + k - initRot % k) % k =
              (i + M - lo + (lo - (g * r + initRot) + a)) % k := by
            have h1 := mod_sub_shift hk (Nat.zero_le (i + M - g * r + a)) hinit_le
            have heq : i + M - g * r + a - initRot = i + M - lo + (lo - (g * r + initRot) + a) := by
              omega
            simpa [heq] using h1
          have hs_lt : lo - (g * r + initRot) + a < b := by
            have hbound : (2 + 2 * g) * r = if col then 6 * r else 4 * r := by
              show (2 + 2 * (if col then 2 else 1)) * r = _; cases col <;> simp
            have ha' : a ≤ if col then 6 * r else 4 * r := by
              have : r - 0 = r := Nat.sub_zero r
              rw [this, hbound] at ha; exact ha
            have hstep_b : lo - (g * r + initRot) + (if col then 6 * r else 4 * r) < b := by
              show loShift col r - ((if col then 2 else 1) * r + (if col then 3 else 1)) +
                (if col then 6 * r else 4 * r) < b
              rw [hbeq]; cases col <;> simp [loShift, max_def] <;> split_ifs <;> omega
            omega
          rw [hsub, hwinM _ hs_lt]
        | succ t ih =>
          intro a ha
          have ht_lt : t < r := by omega
          rw [statePre_succ col w u c ht_lt, statePre_succ col w' u c ht_lt]
          simp only [Nat.testBit_xor]
          have hpos_lt : (i + M - g * (r - (t + 1)) + a) % k < k := Nat.mod_lt _ hk
          rw [testBit_step hpos_lt, testBit_step hpos_lt,
              testBit_rot hw hpos_lt, testBit_rot hw' hpos_lt]
          -- First show the w-injection bits agree
          set rotAmt := if col then 3 * (t + 1) + 1 else 2 * t
          have hgr1_le2 : g * (r - (t + 1)) ≤ 2 * (r - (t + 1)) := Nat.mul_le_mul_right _ hg_le2
          have hgr1_le : g * (r - (t + 1)) ≤ i + M := by omega
          have hlo_ge : g * (r - (t + 1)) + rotAmt ≤ lo := by
            show (if col then 2 else 1) * (r - (t + 1)) +
              (if col then 3 * (t + 1) + 1 else 2 * t) ≤ loShift col r
            cases col <;> simp [loShift, max_def] <;> split_ifs <;> omega
          have hrot_le : rotAmt ≤ i + M - g * (r - (t + 1)) + a := by omega
          have hw_eq : w.testBit (((i + M - g * (r - (t + 1)) + a) % k + k - rotAmt % k) % k) =
              w'.testBit (((i + M - g * (r - (t + 1)) + a) % k + k - rotAmt % k) % k) := by
            have h1 := mod_sub_shift hk (Nat.zero_le (i + M - g * (r - (t + 1)) + a)) hrot_le
            have heq : i + M - g * (r - (t + 1)) + a - rotAmt =
                i + M - lo + (lo - (g * (r - (t + 1)) + rotAmt) + a) := by omega
            have hs_lt : lo - (g * (r - (t + 1)) + rotAmt) + a < b := by
              have hbound : (2 + 2 * g) * (r - (t + 1)) =
                  if col then 6 * (r - (t + 1)) else 4 * (r - (t + 1)) := by
                show (2 + 2 * (if col then 2 else 1)) * (r - (t + 1)) = _; cases col <;> simp
              have ha' : a ≤ if col then 6 * (r - (t + 1)) else 4 * (r - (t + 1)) := by
                rwa [hbound] at ha
              have hstep_b : lo - (g * (r - (t + 1)) + rotAmt) +
                  (if col then 6 * (r - (t + 1)) else 4 * (r - (t + 1))) < b := by
                show loShift col r - ((if col then 2 else 1) * (r - (t + 1)) +
                  (if col then 3 * (t + 1) + 1 else 2 * t)) +
                  (if col then 6 * (r - (t + 1)) else 4 * (r - (t + 1))) < b
                rw [hbeq]; cases col <;> simp [loShift, max_def] <;> split_ifs <;> omega
              omega
            rw [show ((i + M - g * (r - (t + 1)) + a) % k + k - rotAmt % k) % k =
                (i + M - lo + (lo - (g * (r - (t + 1)) + rotAmt) + a)) % k by simpa [heq] using h1]
            exact hwinM _ hs_lt
          -- Next show the mix_g(statePre t) bits agree at offsets 0, 1, 2
          have hmix_eq : ∀ d ≤ 2,
              let pos := ((i + M - g * (r - (t + 1)) + a) % k + d) % k
              let x := statePre k r col w u c t
              let x' := statePre k r col w' u c t
              (x ^^^ rot k g x ^^^ rot k (k - g) x).testBit pos =
              (x' ^^^ rot k g x' ^^^ rot k (k - g) x').testBit pos := by
            intro d hd
            dsimp only
            set pos := ((i + M - g * (r - (t + 1)) + a) % k + d) % k
            have hpos2 : pos < k := Nat.mod_lt _ hk
            have hx_lt := statePre_lt col w u hu c t
            have hx'_lt := statePre_lt col w' u hu c t
            simp only [Nat.testBit_xor]
            rw [testBit_rot hx_lt hpos2, testBit_rot hx'_lt hpos2,
                testBit_rot hx_lt hpos2, testBit_rot hx'_lt hpos2]
            have hpos_eq : pos = (i + M - g * (r - (t + 1)) + a + d) % k := by
              show ((i + M - g * (r - (t + 1)) + a) % k + d) % k = _
              rw [Nat.mod_add_mod]
            have hrt : r - t = (r - (t + 1)) + 1 := by omega
            have hgrt : g * (r - t) = g * (r - (t + 1)) + g := by rw [hrt, Nat.mul_succ]
            have hgrt_le2 : g * (r - t) ≤ 2 * (r - t) := Nat.mul_le_mul_right _ hg_le2
            have hgrt_le : g * (r - t) ≤ i + M := by omega
            have hspan : (2 + 2 * g) * (r - t) = (2 + 2 * g) * (r - (t + 1)) + (2 + 2 * g) := by
              rw [hrt, Nat.mul_succ]
            -- 1) offset 0: pos = (i + M - g*(r-t) + (a + d + g)) % k
            have h0_eq : pos = (i + M - g * (r - t) + (a + d + g)) % k := by
              rw [hpos_eq]; congr 1; omega
            have h0_a : a + d + g ≤ (2 + 2 * g) * (r - t) := by omega
            have hb0 := ih (by omega) (a + d + g) h0_a
            -- 2) offset -g: (pos + k - g % k) % k = (i + M - g*(r-t) + (a + d)) % k
            have h1_eq : (pos + k - g % k) % k = (i + M - g * (r - t) + (a + d)) % k := by
              rw [hpos_eq]
              have hle_g : g ≤ i + M - g * (r - (t + 1)) + a + d := by omega
              have h1 := mod_sub_shift hk (Nat.zero_le _) hle_g
              have heq : i + M - g * (r - (t + 1)) + a + d - g = i + M - g * (r - t) + (a + d) := by omega
              simpa [heq] using h1
            have h1_a : a + d ≤ (2 + 2 * g) * (r - t) := by omega
            have hb1 := ih (by omega) (a + d) h1_a
            -- 3) offset +g: (pos + k - (k - g) % k) % k = (i + M - g*(r-t) + (a + d + 2*g)) % k
            have h2_eq : (pos + k - (k - g) % k) % k = (i + M - g * (r - t) + (a + d + 2 * g)) % k := by
              rw [Nat.mod_eq_of_lt (by omega : k - g < k)]
              have he1 : pos + k - (k - g) = pos + g := by omega
              rw [he1, hpos_eq, Nat.mod_add_mod]
              congr 1; omega
            have h2_a : a + d + 2 * g ≤ (2 + 2 * g) * (r - t) := by omega
            have hb2 := ih (by omega) (a + d + 2 * g) h2_a
            rw [h1_eq, h2_eq, h0_eq, hb0, hb1, hb2]
          unfold stepBit
          have hm0 := hmix_eq 0 (by omega)
          have hm1 := hmix_eq 1 (by omega)
          have hm2 := hmix_eq 2 (by omega)
          have hpos_mod : ((i + M - g * (r - (t + 1)) + a) % k + 0) % k =
              (i + M - g * (r - (t + 1)) + a) % k := by
            rw [Nat.add_zero, Nat.mod_mod]
          rw [hpos_mod] at hm0
          rw [hm0, hm1, hm2, hw_eq]
      have hres := hmain r (le_refl r) 0 (by simp)
      rw [statePre_full, statePre_full] at hres
      have hidx : (i + M - g * (r - r) + 0) % k = i := by
        show (i + k * (4 * r + 4) - g * (r - r) + 0) % k = i
        simp only [Nat.sub_self, Nat.mul_zero, Nat.sub_zero, Nat.add_zero,
          Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hi]
      rw [hidx] at hres
      exact hres

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
def winMask (k b p : Nat) : Nat :=
  embed k b p (2 ^ b - 1)

lemma testBit_winMask {k b p q : Nat} (hb : b ≤ k) (hq : q < k) :
    (winMask k b p).testBit q = decide ((q + k - p % k) % k < b) := by
  unfold winMask
  rw [testBit_embed_general hb hq]
  by_cases hs : (q + k - p % k) % k < b
  · have h1 : (2 ^ b - 1).testBit ((q + k - p % k) % k) = true := by
      rw [Nat.testBit_two_pow_sub_one]; exact decide_eq_true hs
    simp [hs, h1]
  · simp [hs]

lemma submask_winMask_iff {k b p T : Nat} (hk : 0 < k) (hb : b ≤ k) (hT : T < 2 ^ k) :
    submask T (winMask k b p) = true ↔
      embed k b p (extract k b p T).val = T := by
  rw [submask_iff]
  constructor
  · intro hsub
    apply Nat.eq_of_testBit_eq
    intro q
    by_cases hq : q < k
    · rw [testBit_embed_general hb hq]
      dsimp only
      rw [testBit_extract]
      set s := (q + k - p % k) % k
      have hp : p % k < k := Nat.mod_lt _ hk
      have hps : (p + s) % k = q := by
        calc (p + (q + k - p % k) % k) % k
            = (p % k + (q + k - p % k) % k) % k := by rw [Nat.add_mod, Nat.mod_mod]
          _ = (p % k + (q + k - p % k)) % k := by rw [Nat.add_mod_mod]
          _ = (q + k) % k := by congr 1; omega
          _ = q := by rw [Nat.add_mod_right, Nat.mod_eq_of_lt hq]
      rw [hps]
      by_cases hs : s < b
      · simp [hs]
      · simp only [hs, decide_false, Bool.false_and]
        cases hTq : T.testBit q
        · rfl
        · have hw := hsub q hTq
          rw [testBit_winMask hb hq] at hw
          simp [s, hs] at hw
    · rw [Nat.testBit_lt_two_pow ((embed_lt hk).trans_le (Nat.pow_le_pow_right Nat.zero_lt_two (by omega))),
          Nat.testBit_lt_two_pow (hT.trans_le (Nat.pow_le_pow_right Nat.zero_lt_two (by omega)))]
  · intro heq q hTq
    rw [← heq] at hTq
    have hq : q < k := by
      by_contra hge
      have hle : k ≤ q := by omega
      have hlt : embed k b p (extract k b p T).val < 2 ^ q :=
        (embed_lt hk).trans_le (Nat.pow_le_pow_right Nat.zero_lt_two hle)
      have := Nat.testBit_lt_two_pow hlt
      rw [this] at hTq; cases hTq
    rw [testBit_embed_general hb hq] at hTq
    rw [testBit_winMask hb hq]
    exact (Bool.and_eq_true _ _).mp hTq |>.1

lemma submask_embed_iff {k b p S w : Nat} (hk : 0 < k) (hb : b ≤ k) (hS : S < 2 ^ b) :
    submask (embed k b p S) w = true ↔ submask S (extract k b p w).val = true := by
  rw [submask_iff, submask_iff]
  constructor
  · intro h s hs
    have hsb : s < b := by
      by_contra hge
      have hle : b ≤ s := by omega
      have := Nat.testBit_lt_two_pow (hS.trans_le (Nat.pow_le_pow_right Nat.zero_lt_two hle))
      rw [this] at hs; cases hs
    rw [testBit_extract, decide_eq_true hsb, Bool.true_and]
    apply h ((p + s) % k)
    rw [testBit_embed_win hb hsb]
    exact hs
  · intro h q hq
    have hq_lt : q < k := by
      by_contra hge
      have hle : k ≤ q := by omega
      have hlt : embed k b p S < 2 ^ q :=
        (embed_lt hk).trans_le (Nat.pow_le_pow_right Nat.zero_lt_two hle)
      have := Nat.testBit_lt_two_pow hlt
      rw [this] at hq; cases hq
    rw [testBit_embed_general hb hq_lt] at hq
    obtain ⟨hsb, hSs⟩ := (Bool.and_eq_true _ _).mp hq
    have hsb' : (q + k - p % k) % k < b := of_decide_eq_true hsb
    have hw := h _ hSs
    rw [testBit_extract] at hw
    have hp : p % k < k := Nat.mod_lt _ hk
    have hps : (p + (q + k - p % k) % k) % k = q := by
      calc (p + (q + k - p % k) % k) % k
          = (p % k + (q + k - p % k) % k) % k := by rw [Nat.add_mod, Nat.mod_mod]
        _ = (p % k + (q + k - p % k)) % k := by rw [Nat.add_mod_mod]
        _ = (q + k) % k := by congr 1; omega
        _ = q := by rw [Nat.add_mod_right, Nat.mod_eq_of_lt hq_lt]
    rw [hps] at hw
    exact (Bool.and_eq_true _ _).mp hw |>.2

lemma extract_embed {k b p S : Nat} (hb : b ≤ k) (hS : S < 2 ^ b) :
    (extract k b p (embed k b p S)).val = S := by
  apply Nat.eq_of_testBit_eq
  intro s
  rw [testBit_extract]
  by_cases hs : s < b
  · simp only [hs, decide_true, Bool.true_and, testBit_embed_win hb hs]
  · simp only [hs, decide_false, Bool.false_and]
    symm
    exact Nat.testBit_lt_two_pow (hS.trans_le (Nat.pow_le_pow_right Nat.zero_lt_two (by omega)))

lemma fmt_local {k b : Nat} (hk : 0 < k) (hb : b ≤ k) (p : Nat) (ψ : Fin (2 ^ b) → Bool)
    (T : Fin (2 ^ k)) :
    fmt (fun w : Fin (2 ^ k) => ψ (extract k b p w.val)) T =
      if submask T.val (winMask k b p) then fmt ψ (extract k b p T.val) else false := by
  let c : Fin (2 ^ k) → Bool := fun U =>
    if submask U.val (winMask k b p) then fmt ψ (extract k b p U.val) else false
  suffices h : fmt c = fun w : Fin (2 ^ k) => ψ (extract k b p w.val) by
    have := congrArg fmt h
    rw [fmt_invol] at this
    exact (congrFun this T).symm
  funext w
  rw [fmt_eq_submaskSum]
  have h1 : ψ (extract k b p w.val) = fmt (fmt ψ) (extract k b p w.val) := by rw [fmt_invol]
  rw [h1, fmt_eq_submaskSum]
  -- Filter c to submasks of winMask, then biject with S : Fin (2^b)
  have hfilt :
      bxorFinset (Finset.univ.filter (fun U : Fin (2 ^ k) => submask U.val w.val = true)) c =
      bxorFinset (Finset.univ.filter (fun U : Fin (2 ^ k) =>
        submask U.val w.val = true ∧ submask U.val (winMask k b p) = true))
        (fun U => fmt ψ (extract k b p U.val)) := by
    have hsplit : Finset.univ.filter (fun U : Fin (2 ^ k) =>
        submask U.val w.val = true ∧ submask U.val (winMask k b p) = true) =
      (Finset.univ.filter (fun U : Fin (2 ^ k) => submask U.val w.val = true)).filter
        (fun U => submask U.val (winMask k b p) = true) := by
      ext U; simp
    symm
    rw [hsplit, bxorFinset_filter_eq]
    apply bxorFinset_congr
    intro U _
    unfold c
    cases hsm : submask U.val (winMask k b p) <;> simp [hsm]
  rw [hfilt]
  symm
  apply bxorFinset_bij _ _ _ _ (fun S _ => ⟨embed k b p S.val, embed_lt hk⟩)
  · intro S hS
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hS ⊢
    refine ⟨(submask_embed_iff hk hb S.isLt).mpr hS, ?_⟩
    rw [submask_winMask_iff hk hb (embed_lt hk), extract_embed hb S.isLt]
  · intro S1 _ S2 _ heq
    have hval := congrArg Fin.val heq
    dsimp only at hval
    have h2 := congrArg (fun x => (extract k b p x).val) hval
    rw [extract_embed hb S1.isLt, extract_embed hb S2.isLt] at h2
    exact Fin.ext h2
  · intro U hU
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hU
    refine ⟨extract k b p U.val, ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      have hemb := (submask_winMask_iff hk hb U.isLt).mp hU.2
      rw [← submask_embed_iff hk hb (extract k b p U.val).isLt, hemb]
      exact hU.1
    · exact Fin.ext ((submask_winMask_iff hk hb U.isLt).mp hU.2)
  · intro S _
    congr 1
    exact Fin.ext (extract_embed hb S.isLt).symm

-- Popcount and ANF Shift Formula
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

lemma popcount_embed {k b p S : Nat} (hb : b ≤ k) (hS : S < 2 ^ b) :
    popcount k (embed k b p S) = popcount b S := by
  rcases Nat.eq_zero_or_pos b with rfl | hbpos
  · simp at hS; subst hS; simp [popcount, embed]
  · have hk : 0 < k := by omega
    rw [popcount_eq_card, popcount_eq_card]
    symm
    apply Finset.card_bij (fun s _ => ⟨(p + s.val) % k, Nat.mod_lt _ hk⟩)
    · intro s hs
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hs ⊢
      rw [testBit_embed_win hb s.isLt]; exact hs
    · intro s1 _ s2 _ heq
      have hv := congrArg Fin.val heq
      exact Fin.ext (mod_add_inj (by omega) (by omega) hv)
    · intro q hq
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hq
      rw [testBit_embed_general hb q.isLt] at hq
      obtain ⟨hsb, hSs⟩ := (Bool.and_eq_true _ _).mp hq
      have hsb' : (q.val + k - p % k) % k < b := of_decide_eq_true hsb
      refine ⟨⟨(q.val + k - p % k) % k, hsb'⟩, ?_, ?_⟩
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact hSs
      · apply Fin.ext
        have hp : p % k < k := Nat.mod_lt _ hk
        calc (p + (q.val + k - p % k) % k) % k
            = (p % k + (q.val + k - p % k) % k) % k := by rw [Nat.add_mod, Nat.mod_mod]
          _ = (p % k + (q.val + k - p % k)) % k := by rw [Nat.add_mod_mod]
          _ = (q.val + k) % k := by congr 1; omega
          _ = q.val := by rw [Nat.add_mod_right, Nat.mod_eq_of_lt q.isLt]

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
def isPiv {k q : Nat} (hasP : Fin k → Bool) (r : Fin q) (c : Fin k) : Bool :=
  hasP c && cntEq hasP c.val r.val

def selDir {k q : Nat} (hasP : Fin k → Bool) (piv : Fin k → Vec k) (r : Fin q) : Vec k :=
  vecLinComb piv (isPiv hasP r)

def inSq {k : Nat} (hasP : Fin k → Bool) (q : Nat) (c : Fin k) : Bool :=
  hasP c && (List.finRange q).foldl (fun acc r => acc || cntEq hasP c.val r.val) false

def isComp {k : Nat} (hasP : Fin k → Bool) (q : Nat) (l : Fin (k - q)) (c : Fin k) : Bool :=
  !(inSq hasP q c) && cntEq (fun c' => !(inSq hasP q c')) c.val l.val

def seedVec {k : Nat} (hasP : Fin k → Bool) (q : Nat) (σ : Fin (2 ^ (k - q))) : Vec k :=
  fun c => (List.finRange (k - q)).foldl (fun acc l => acc || (σ.val.testBit l.val && isComp hasP q l c)) false

lemma inSq_eq_true {k : Nat} (hasP : Fin k → Bool) (q : Nat) (c : Fin k) :
    inSq hasP q c = true ↔ hasP c = true ∧ cntAt hasP c.val < q := by
  unfold inSq
  rw [Bool.and_eq_true, foldl_or_eq_true]
  simp only [Bool.false_eq_true, false_or, List.mem_finRange, true_and, cntEq, decide_eq_true_eq]
  constructor
  · rintro ⟨hp, r, hr⟩; exact ⟨hp, hr ▸ r.isLt⟩
  · rintro ⟨hp, hlt⟩; exact ⟨hp, ⟨cntAt hasP c.val, hlt⟩, rfl⟩

lemma card_inSq {k q : Nat} (hasP : Fin k → Bool) (hq : q ≤ cntAt hasP k) :
    (Finset.univ.filter (fun c : Fin k => inSq hasP q c = true)).card = q := by
  have hbij : (Finset.univ : Finset (Fin q)).card =
      (Finset.univ.filter (fun c : Fin k => inSq hasP q c = true)).card := by
    apply Finset.card_bij (fun r _ => Classical.choose (exists_unique_cntAt hasP (lt_of_lt_of_le r.isLt hq)))
    · intro r _
      have hsp := (Classical.choose_spec (exists_unique_cntAt hasP (lt_of_lt_of_le r.isLt hq))).1
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, inSq_eq_true]
      exact ⟨hsp.1, hsp.2.symm ▸ r.isLt⟩
    · intro r1 _ r2 _ heq
      have h1 := (Classical.choose_spec (exists_unique_cntAt hasP (lt_of_lt_of_le r1.isLt hq))).1.2
      have h2 := (Classical.choose_spec (exists_unique_cntAt hasP (lt_of_lt_of_le r2.isLt hq))).1.2
      rw [heq] at h1
      exact Fin.ext (h1.symm.trans h2)
    · intro c hc
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, inSq_eq_true] at hc
      refine ⟨⟨cntAt hasP c.val, hc.2⟩, Finset.mem_univ _, ?_⟩
      have huniq := (Classical.choose_spec (exists_unique_cntAt hasP (lt_of_lt_of_le hc.2 hq))).2
      exact (huniq c ⟨hc.1, rfl⟩).symm
  simpa using hbij.symm

lemma cntAt_not_inSq {k q : Nat} (hasP : Fin k → Bool) (hqk : q ≤ k) (hq : q ≤ cntAt hasP k) :
    cntAt (fun c => !(inSq hasP q c)) k = k - q := by
  rw [cntAt_full]
  have hsum : (Finset.univ.filter (fun c : Fin k => !(inSq hasP q c) = true)).card +
      (Finset.univ.filter (fun c : Fin k => inSq hasP q c = true)).card = k := by
    rw [← Finset.card_union_of_disjoint]
    · have hunion : (Finset.univ.filter (fun c : Fin k => !(inSq hasP q c) = true)) ∪
          (Finset.univ.filter (fun c : Fin k => inSq hasP q c = true)) = Finset.univ := by
        ext c; simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
        cases inSq hasP q c <;> simp
      rw [hunion]; simp
    · rw [Finset.disjoint_left]; intro c h1 h2
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h1 h2
      rw [h2] at h1; cases h1
  rw [card_inSq hasP hq] at hsum
  exact Nat.eq_sub_of_add_eq hsum

-- Coset decomposition and exact hit count theorem
lemma coset_hits_eq {k m q : Nat} (hqk : q ≤ k)
    {hasP : Fin k → Bool} {piv : Fin k → Vec k}
    (htriP : ∀ j : Fin k,
      (∀ j' : Fin k, j'.val < j.val → piv j j' = false) ∧
      (hasP j = true → piv j j = true) ∧
      (hasP j = false → piv j = vecZero k))
    (hq : q ≤ cntAt hasP k)
    (f : Fin (2 ^ k) → Vec m) (y : Vec m)
    (resp : Fin q → Vec m)
    (hgood : ∀ (r : Fin q) (w : Fin (2 ^ k)),
      vecXor (f ⟨w.val ^^^ (ofVec k (selDir hasP piv r)).val, xor_lt w.isLt (ofVec k _).isLt⟩) (f w) = resp r) :
    let echR := echelon resp
    let ρ := cntAt echR.hasP m
    let passCount := (Finset.univ.filter (fun σ : Fin (2 ^ (k - q)) =>
      echelonReduce echR.hasP echR.piv (vecXor (f (ofVec k (seedVec hasP q σ))) y) = vecZero m)).card
    Nat.card { w : Fin (2 ^ k) // f w = y } = passCount * 2 ^ (q - ρ) := by
  classical
  dsimp only
  let echR := echelon resp
  let ρ := cntAt echR.hasP m
  let pivCol : Fin q → Fin k := fun r =>
    Classical.choose (exists_unique_cntAt hasP (lt_of_lt_of_le r.isLt hq))
  have hpivCol_spec : ∀ r : Fin q, hasP (pivCol r) = true ∧ cntAt hasP (pivCol r).val = r.val :=
    fun r => (Classical.choose_spec (exists_unique_cntAt hasP (lt_of_lt_of_le r.isLt hq))).1
  have hpivCol_uniq : ∀ r : Fin q, ∀ c : Fin k, hasP c = true ∧ cntAt hasP c.val = r.val → c = pivCol r :=
    fun r c hc => (Classical.choose_spec (exists_unique_cntAt hasP (lt_of_lt_of_le r.isLt hq))).2 c hc
  have hselDir : ∀ r : Fin q, selDir hasP piv r = piv (pivCol r) := by
    intro r
    have hisP : isPiv hasP r = stdBasis k (pivCol r) := by
      funext c
      unfold isPiv stdBasis
      by_cases hcp : c = pivCol r
      · subst hcp; simp [hpivCol_spec r, cntEq]
      · simp only [hcp, decide_false]
        cases hpc : hasP c
        · simp
        · simp only [Bool.true_and, cntEq, decide_eq_false_iff_not]
          intro hcnt
          exact hcp (hpivCol_uniq r c ⟨hpc, hcnt⟩)
    unfold selDir
    rw [hisP, vecLinComb_stdBasis]
  have hpivCol_lt : ∀ r1 r2 : Fin q, r1.val < r2.val → (pivCol r1).val < (pivCol r2).val := by
    intro r1 r2 hlt
    by_contra hge
    have hle : (pivCol r2).val ≤ (pivCol r1).val := by omega
    have hm := cntAt_mono hasP hle
    rw [(hpivCol_spec r1).2, (hpivCol_spec r2).2] at hm
    omega
  have hnot_inSq_cnt : cntAt (fun c => !(inSq hasP q c)) k = k - q := cntAt_not_inSq hasP hqk hq
  have hl_lt : ∀ l : Fin (k - q), l.val < cntAt (fun c => !(inSq hasP q c)) k :=
    fun l => by rw [hnot_inSq_cnt]; exact l.isLt
  let compCol : Fin (k - q) → Fin k := fun l =>
    Classical.choose (exists_unique_cntAt (fun c => !(inSq hasP q c)) (hl_lt l))
  have hcompCol_spec : ∀ l : Fin (k - q),
      !(inSq hasP q (compCol l)) = true ∧ cntAt (fun c => !(inSq hasP q c)) (compCol l).val = l.val :=
    fun l => (Classical.choose_spec (exists_unique_cntAt (fun c => !(inSq hasP q c)) (hl_lt l))).1
  have hcompCol_uniq : ∀ l : Fin (k - q), ∀ c : Fin k,
      !(inSq hasP q c) = true ∧ cntAt (fun c' => !(inSq hasP q c')) c.val = l.val → c = compCol l :=
    fun l c hc => (Classical.choose_spec (exists_unique_cntAt (fun c => !(inSq hasP q c)) (hl_lt l))).2 c hc
  have hseed_piv : ∀ (σ : Fin (2 ^ (k - q))) (r : Fin q), seedVec hasP q σ (pivCol r) = false := by
    intro σ r
    unfold seedVec
    cases h : (List.finRange (k - q)).foldl (fun acc l => acc || (σ.val.testBit l.val && isComp hasP q l (pivCol r))) false
    · rfl
    · rw [foldl_or_eq_true] at h
      rcases h with h | ⟨l, _, hl⟩
      · cases h
      · obtain ⟨_, hcomp⟩ := (Bool.and_eq_true _ _).mp hl
        unfold isComp at hcomp
        obtain ⟨hnot, _⟩ := (Bool.and_eq_true _ _).mp hcomp
        have hin : inSq hasP q (pivCol r) = true :=
          (inSq_eq_true hasP q (pivCol r)).mpr ⟨(hpivCol_spec r).1, (hpivCol_spec r).2.symm ▸ r.isLt⟩
        rw [hin] at hnot; cases hnot
  have hseed_comp : ∀ (σ : Fin (2 ^ (k - q))) (l : Fin (k - q)),
      seedVec hasP q σ (compCol l) = σ.val.testBit l.val := by
    intro σ l
    unfold seedVec
    have hiff : (List.finRange (k - q)).foldl (fun acc l' => acc || (σ.val.testBit l'.val && isComp hasP q l' (compCol l))) false = true ↔
        σ.val.testBit l.val = true := by
      rw [foldl_or_eq_true]
      simp only [Bool.false_eq_true, false_or, List.mem_finRange, true_and, Bool.and_eq_true]
      constructor
      · rintro ⟨l', htb, hcomp⟩
        unfold isComp at hcomp
        obtain ⟨hnot, hce⟩ := (Bool.and_eq_true _ _).mp hcomp
        simp only [cntEq, decide_eq_true_eq] at hce
        have heq : l' = l := Fin.ext (hce.symm.trans (hcompCol_spec l).2)
        rwa [heq] at htb
      · intro htb
        refine ⟨l, htb, ?_⟩
        have h1 : inSq hasP q (compCol l) = false := by
          have h := (hcompCol_spec l).1
          cases hq' : inSq hasP q (compCol l)
          · rfl
          · simp [hq'] at h
        simp [isComp, h1, cntEq, (hcompCol_spec l).2]
    cases hl : (List.finRange (k - q)).foldl (fun acc l' => acc || (σ.val.testBit l'.val && isComp hasP q l' (compCol l))) false <;>
      cases htb : σ.val.testBit l.val
    · rfl
    · exact absurd (hiff.mpr htb) (by simp [hl])
    · exact absurd (hiff.mp hl) (by simp [htb])
    · rfl
  -- Define coset bijection Φ : Fin (2^(k-q)) × Vec q → Fin (2^k)
  let Φ : Fin (2 ^ (k - q)) × Vec q → Fin (2 ^ k) := fun ⟨σ, α⟩ =>
    ofVec k (vecXor (seedVec hasP q σ) (vecLinComb (selDir hasP piv) α))
  have hΦ_inj : Function.Injective Φ := by
    rintro ⟨σ1, α1⟩ ⟨σ2, α2⟩ heq
    have hveq : vecXor (seedVec hasP q σ1) (vecLinComb (selDir hasP piv) α1) =
        vecXor (seedVec hasP q σ2) (vecLinComb (selDir hasP piv) α2) := by
      have := congrArg (toVec k) heq
      simpa [Φ, toVec_ofVec] using this
    have hα : α1 = α2 := by
      funext r
      have hstr : ∀ t : Nat, ∀ r : Fin q, r.val < t → α1 r = α2 r := by
        intro t
        induction t with
        | zero => intro r hr; omega
        | succ t ih =>
          intro r hr
          by_cases hlt : r.val < t
          · exact ih r hlt
          · have hreq : r.val = t := by omega
            have hbit := congrFun hveq (pivCol r)
            simp only [vecXor, hseed_piv, Bool.false_xor] at hbit
            have hcomb_eval : ∀ (α : Vec q),
                vecLinComb (selDir hasP piv) α (pivCol r) =
                  xor (α r) (bxorFinset (Finset.univ.filter (fun r' : Fin q => r'.val < r.val))
                    (fun r' => α r' && selDir hasP piv r' (pivCol r))) := by
              intro α
              simp only [vecLinComb, vecDot_eq_bxor]
              have hsp : (Finset.univ : Finset (Fin q)) =
                  insert r ((Finset.univ.filter (fun r' : Fin q => r'.val < r.val)) ∪
                    (Finset.univ.filter (fun r' : Fin q => r.val < r'.val))) := by
                ext r'; simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_union,
                  Finset.mem_filter, true_and, true_iff]
                rcases Nat.lt_trichotomy r'.val r.val with h1 | h2 | h3
                · exact Or.inr (Or.inl h1)
                · exact Or.inl (Fin.ext h2)
                · exact Or.inr (Or.inr h3)
              have hrnot : r ∉ (Finset.univ.filter (fun r' : Fin q => r'.val < r.val)) ∪
                  (Finset.univ.filter (fun r' : Fin q => r.val < r'.val)) := by simp
              have hdisj : Disjoint (Finset.univ.filter (fun r' : Fin q => r'.val < r.val))
                  (Finset.univ.filter (fun r' : Fin q => r.val < r'.val)) := by
                rw [Finset.disjoint_left]; intro r' h1 h2
                simp only [Finset.mem_filter] at h1 h2; omega
              conv_lhs => rw [hsp]
              rw [bxorFinset_insert hrnot, bxorFinset_union_disjoint hdisj]
              have hgt0 : bxorFinset (Finset.univ.filter (fun r' : Fin q => r.val < r'.val))
                  (fun r' => α r' && selDir hasP piv r' (pivCol r)) = false := by
                apply bxorFinset_zero
                intro r' hr'
                simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hr'
                rw [hselDir r', (htriP (pivCol r')).1 (pivCol r) (hpivCol_lt r r' hr'), Bool.and_false]
              rw [hgt0, Bool.xor_false, hselDir r, (htriP (pivCol r)).2.1 (hpivCol_spec r).1, Bool.and_true]
            rw [hcomb_eval α1, hcomb_eval α2] at hbit
            have hlt_eq : bxorFinset (Finset.univ.filter (fun r' : Fin q => r'.val < r.val))
                (fun r' => α1 r' && selDir hasP piv r' (pivCol r)) =
                bxorFinset (Finset.univ.filter (fun r' : Fin q => r'.val < r.val))
                (fun r' => α2 r' && selDir hasP piv r' (pivCol r)) := by
              apply bxorFinset_congr
              intro r' hr'
              simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hr'
              rw [ih r' (by omega)]
            rw [hlt_eq] at hbit
            generalize bxorFinset (Finset.univ.filter (fun r' : Fin q => r'.val < r.val))
              (fun r' => α2 r' && selDir hasP piv r' (pivCol r)) = x at hbit
            rcases ha1 : α1 r with _ | _ <;> rcases ha2 : α2 r with _ | _ <;> rcases x with _ | _ <;>
              simp only [ha1, ha2, Bool.false_xor, Bool.true_xor] at hbit <;> first | rfl | cases hbit
      exact hstr q r r.isLt
    subst hα
    have hseed_eq : seedVec hasP q σ1 = seedVec hasP q σ2 := by
      funext c
      have hbit := congrFun hveq c
      simp only [vecXor] at hbit
      generalize seedVec hasP q σ1 c = x1 at hbit ⊢
      generalize seedVec hasP q σ2 c = x2 at hbit ⊢
      generalize vecLinComb (selDir hasP piv) α1 c = x3 at hbit
      cases x1 <;> cases x2 <;> cases x3 <;>
        simp only [Bool.false_xor, Bool.true_xor] at hbit <;> first | rfl | cases hbit
    have hσ : σ1 = σ2 := by
      apply Fin.ext
      apply Nat.eq_of_testBit_eq
      intro l
      by_cases hl : l < k - q
      · have h1 := hseed_comp σ1 ⟨l, hl⟩
        have h2 := hseed_comp σ2 ⟨l, hl⟩
        rw [hseed_eq] at h1
        exact h1.symm.trans h2
      · rw [Nat.testBit_lt_two_pow (σ1.isLt.trans_le (Nat.pow_le_pow_right Nat.zero_lt_two (by omega))),
            Nat.testBit_lt_two_pow (σ2.isLt.trans_le (Nat.pow_le_pow_right Nat.zero_lt_two (by omega)))]
    subst hσ; rfl
  have hΦ_bij : Function.Bijective Φ := by
    rw [Fintype.bijective_iff_injective_and_card]
    refine ⟨hΦ_inj, ?_⟩
    rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin,
        Fintype.card_fin, ← pow_add, Nat.sub_add_cancel hqk]
  -- Evaluate f on coset elements: f (Φ (σ, α)) = vecXor (f (seed σ)) (vecLinComb resp α)
  have hf_coset : ∀ (σ : Fin (2 ^ (k - q))) (α : Vec q),
      f (Φ (σ, α)) = vecXor (f (ofVec k (seedVec hasP q σ))) (vecLinComb resp α) := by
    intro σ α
    have hgen : ∀ (s : Finset (Fin q)) (w : Fin (2 ^ k)),
        f (ofVec k (vecXor (toVec k w) (fun c => bxorFinset s (fun r => α r && selDir hasP piv r c)))) =
          vecXor (f w) (fun j => bxorFinset s (fun r => α r && resp r j)) := by
      intro s
      induction s using Finset.induction with
      | empty =>
        intro w
        have h1 : (fun c : Fin k => bxorFinset (∅ : Finset (Fin q)) (fun r => α r && selDir hasP piv r c)) = vecZero k := by
          funext c; simp [bxorFinset, vecZero]
        have h2 : (fun j : Fin m => bxorFinset (∅ : Finset (Fin q)) (fun r => α r && resp r j)) = vecZero m := by
          funext j; simp [bxorFinset, vecZero]
        rw [h1, h2, vecXor_zero, vecXor_zero, ofVec_toVec]
      | insert r s hr ih =>
        intro w
        have h1 : (fun c : Fin k => bxorFinset (insert r s) (fun r' => α r' && selDir hasP piv r' c)) =
            vecXor (fun c => α r && selDir hasP piv r c)
              (fun c => bxorFinset s (fun r' => α r' && selDir hasP piv r' c)) := by
          funext c; exact bxorFinset_insert hr _
        have h2 : (fun j : Fin m => bxorFinset (insert r s) (fun r' => α r' && resp r' j)) =
            vecXor (fun j => α r && resp r j)
              (fun j => bxorFinset s (fun r' => α r' && resp r' j)) := by
          funext j; exact bxorFinset_insert hr _
        rw [h1, h2]
        cases hαr : α r
        · have hz1 : (fun c : Fin k => false && selDir hasP piv r c) = vecZero k := by funext c; rfl
          have hz2 : (fun j : Fin m => false && resp r j) = vecZero m := by funext j; rfl
          rw [hz1, hz2, zero_vecXor, zero_vecXor]
          exact ih w
        · have ht1 : (fun c : Fin k => true && selDir hasP piv r c) = selDir hasP piv r := by funext c; rfl
          have ht2 : (fun j : Fin m => true && resp r j) = resp r := by funext j; rfl
          rw [ht1, ht2]
          set w' : Fin (2 ^ k) := ⟨w.val ^^^ (ofVec k (selDir hasP piv r)).val, xor_lt w.isLt (ofVec k _).isLt⟩
          have hw' : toVec k w' = vecXor (toVec k w) (selDir hasP piv r) := by
            simp [w', toVec_xor, toVec_ofVec]
          rw [← vecXor_assoc, ← hw', ih w']
          have hg := hgood r w
          have hfw' : f w' = vecXor (f w) (resp r) := by
            funext j
            have := congrFun hg j
            simp only [vecXor, w'] at this ⊢
            generalize f w' j = b1 at this ⊢
            generalize f w j = b2 at this ⊢
            generalize resp r j = b3 at this ⊢
            cases b1 <;> cases b2 <;> cases b3 <;>
              simp only [Bool.false_xor, Bool.true_xor] at this ⊢ <;> first | rfl | cases this
          rw [hfw', vecXor_assoc]
    have hlc1 : vecLinComb (selDir hasP piv) α =
        fun c => bxorFinset Finset.univ (fun r => α r && selDir hasP piv r c) := by
      funext c; exact vecDot_eq_bxor _ _
    have hlc2 : vecLinComb resp α =
        fun j => bxorFinset Finset.univ (fun r => α r && resp r j) := by
      funext j; exact vecDot_eq_bxor _ _
    have hs := hgen Finset.univ (ofVec k (seedVec hasP q σ))
    rw [toVec_ofVec] at hs
    simpa only [Φ, hlc1, hlc2] using hs
  -- Kernel size of resp is 2^(q - ρ)
  have hρ_le : ρ ≤ q := by
    have := echelon_rank_le resp
    simpa [ρ, echR, cntAt_full] using this
  have hker_card : (Finset.univ.filter (fun α : Vec q => vecLinComb resp α = vecZero m)).card = 2 ^ (q - ρ) := by
    have hmul : (Finset.univ.filter (fun α : Vec q => vecLinComb resp α = vecZero m)).card *
        (Finset.univ.filter (fun v : Vec m => inSpan resp v)).card = 2 ^ q := by
      have htot : (Finset.univ : Finset (Vec q)).card = 2 ^ q := by simp
      rw [← htot]
      have hfib := Finset.card_eq_sum_card_fiberwise (f := vecLinComb resp)
        (s := (Finset.univ : Finset (Vec q)))
        (t := Finset.univ.filter (fun v : Vec m => inSpan resp v))
        (fun α _ => Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨α, rfl⟩⟩)
      rw [hfib]
      have hconst : ∀ v ∈ Finset.univ.filter (fun v : Vec m => inSpan resp v),
          (Finset.univ.filter (fun α : Vec q => vecLinComb resp α = v)).card =
          (Finset.univ.filter (fun α : Vec q => vecLinComb resp α = vecZero m)).card := by
        intro v hv
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv
        obtain ⟨α0, rfl⟩ := hv
        symm
        apply Finset.card_bij (fun α _ => vecXor α α0)
        · intro α hα
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hα ⊢
          rw [vecLinComb_xor, hα, zero_vecXor]
        · intro α1 _ α2 _ heq
          have := congrArg (fun x => vecXor x α0) heq
          simpa [vecXor_assoc, vecXor_self, vecXor_zero] using this
        · intro α hα
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hα
          refine ⟨vecXor α α0, ?_, by rw [vecXor_assoc, vecXor_self, vecXor_zero]⟩
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          rw [vecLinComb_xor, hα, vecXor_self]
      rw [Finset.sum_congr rfl hconst, Finset.sum_const, smul_eq_mul, mul_comm]
    have him : (Finset.univ.filter (fun v : Vec m => inSpan resp v)).card = 2 ^ ρ := by
      have h1 := echelon_card_span resp
      rw [Nat.card_eq_fintype_card, Fintype.card_subtype] at h1
      simpa [ρ, echR, cntAt_full] using h1
    rw [him] at hmul
    have hpow : 2 ^ (q - ρ) * 2 ^ ρ = 2 ^ q := by rw [← pow_add, Nat.sub_add_cancel hρ_le]
    have hpos : 0 < 2 ^ ρ := Nat.two_pow_pos ρ
    nlinarith
  -- Now count hits via Φ
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  have hbij_hits : (Finset.univ.filter (fun w : Fin (2 ^ k) => f w = y)).card =
      (Finset.univ.filter (fun p : Fin (2 ^ (k - q)) × Vec q =>
        vecLinComb resp p.2 = vecXor (f (ofVec k (seedVec hasP q p.1))) y)).card := by
    symm
    apply Finset.card_bij (fun p _ => Φ p)
    · intro ⟨σ, α⟩ hp
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
      rw [hf_coset σ α, hp, ← vecXor_assoc, vecXor_self, zero_vecXor]
    · intro p1 _ p2 _ heq; exact hΦ_inj heq
    · intro w hw
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw
      obtain ⟨⟨σ, α⟩, hσα⟩ := hΦ_bij.2 w
      refine ⟨⟨σ, α⟩, ?_, hσα⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      have h1 := hf_coset σ α
      rw [hσα, hw] at h1
      have h2 := congrArg (vecXor (f (ofVec k (seedVec hasP q σ)))) h1
      rw [← vecXor_assoc, vecXor_self, zero_vecXor] at h2
      exact h2.symm
  rw [hbij_hits]
  -- Group by σ
  have hsum : (Finset.univ.filter (fun p : Fin (2 ^ (k - q)) × Vec q =>
        vecLinComb resp p.2 = vecXor (f (ofVec k (seedVec hasP q p.1))) y)).card =
      ∑ σ : Fin (2 ^ (k - q)),
        (Finset.univ.filter (fun α : Vec q =>
          vecLinComb resp α = vecXor (f (ofVec k (seedVec hasP q σ))) y)).card := by
    rw [Finset.card_eq_sum_card_fiberwise (f := Prod.fst) (t := Finset.univ) (fun _ _ => Finset.mem_univ _)]
    apply Finset.sum_congr rfl
    intro σ _
    apply Finset.card_bij (fun p _ => p.2)
    · intro ⟨σ', α⟩ hp
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
      rcases hp with ⟨h1, rfl⟩; exact h1
    · intro ⟨σ1, α1⟩ h1 ⟨σ2, α2⟩ h2 heq
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h1 h2
      dsimp only at heq
      rcases h1 with ⟨_, rfl⟩; rcases h2 with ⟨_, rfl⟩; rw [heq]
    · intro α hα
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hα
      exact ⟨⟨σ, α⟩, by simp [hα], rfl⟩
  rw [hsum]
  have hterm : ∀ σ : Fin (2 ^ (k - q)),
      (Finset.univ.filter (fun α : Vec q =>
        vecLinComb resp α = vecXor (f (ofVec k (seedVec hasP q σ))) y)).card =
      if echelonReduce echR.hasP echR.piv (vecXor (f (ofVec k (seedVec hasP q σ))) y) = vecZero m
      then 2 ^ (q - ρ) else 0 := by
    intro σ
    set tgt := vecXor (f (ofVec k (seedVec hasP q σ))) y
    by_cases hred : echelonReduce echR.hasP echR.piv tgt = vecZero m
    · simp only [hred, ↓reduceIte]
      obtain ⟨α0, hα0⟩ := (echelonReduce_eq_zero_iff resp tgt).mp hred
      rw [← hker_card]
      symm
      apply Finset.card_bij (fun α _ => vecXor α α0)
      · intro α hα
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hα ⊢
        rw [vecLinComb_xor, hα, zero_vecXor, ← hα0]
      · intro α1 _ α2 _ heq
        have := congrArg (fun x => vecXor x α0) heq
        simpa [vecXor_assoc, vecXor_self, vecXor_zero] using this
      · intro α hα
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hα
        refine ⟨vecXor α α0, ?_, by rw [vecXor_assoc, vecXor_self, vecXor_zero]⟩
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        rw [vecLinComb_xor, hα, ← hα0, vecXor_self]
    · simp only [hred, ↓reduceIte]
      rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
      intro α hα
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hα
      exact hred ((echelonReduce_eq_zero_iff resp tgt).mpr ⟨α, hα.symm⟩)
  simp only [hterm, Finset.sum_ite, Finset.sum_const, smul_eq_mul, mul_zero, add_zero]
  rfl

-- ============================================================
-- PART 5: Local Window ANF & Descending Subspace Chain V_{b-1} ⊇ ... ⊇ V_0
-- ============================================================

def targetF (k r m : Nat) (u v : Fin (2 ^ k)) (cr cc : Fin r → Fin (2 ^ k))
    (A B : Fin m → Fin (2 ^ k)) (w : Fin (2 ^ k)) (j : Fin m) : Bool :=
  xor (parity k (A j).val (state k r false w.val u.val cr))
      (parity k (B j).val (state k r true w.val v.val cc))

def winStart (k r : Nat) (col : Bool) (i : Nat) : Nat :=
  (i + k - loShift col r % k) % k

def localPsi (k r : Nat) (col : Bool) (name : Fin (2 ^ k)) (sched : Fin r → Fin (2 ^ k))
    (i : Fin k) (α : Fin (2 ^ winSize k r)) : Bool :=
  (state k r col (embed k (winSize k r) (winStart k r col i.val) α.val) name.val sched).testBit i.val

lemma state_testBit_eq_localPsi {k r : Nat} (hk : 0 < k) (col : Bool)
    (name : Fin (2 ^ k)) (sched : Fin r → Fin (2 ^ k)) (w : Fin (2 ^ k)) (i : Fin k) :
    (state k r col w.val name.val sched).testBit i.val =
      localPsi k r col name sched i (extract k (winSize k r) (winStart k r col i.val) w.val) := by
  unfold localPsi
  apply state_testBit_window hk col w.isLt (embed_lt hk) name.isLt sched i.isLt
  intro s hs
  change w.val.testBit ((winStart k r col i.val + s) % k) =
    (embed k (winSize k r) (winStart k r col i.val)
      (extract k (winSize k r) (winStart k r col i.val) w.val).val).testBit
      ((winStart k r col i.val + s) % k)
  rw [testBit_embed_win (winSize_le k r) hs, testBit_extract]
  simp [hs]

lemma parity_eq_bxor {k : Nat} (mask x : Nat) :
    parity k mask x = bxorFinset Finset.univ (fun i : Fin k => mask.testBit i.val && x.testBit i.val) := by
  unfold parity
  rw [← bxorFinset_finRange]
  have hmap : List.range k = (List.finRange k).map Fin.val := by apply List.ext_getElem <;> simp
  rw [hmap, List.foldl_map]

lemma extract_xor {k b p : Nat} (w1 w2 : Fin (2 ^ k)) :
    extract k b p (w1.val ^^^ w2.val) =
      ⟨(extract k b p w1.val).val ^^^ (extract k b p w2.val).val,
       xor_lt (extract k b p w1.val).isLt (extract k b p w2.val).isLt⟩ := by
  apply Fin.ext
  apply Nat.eq_of_testBit_eq
  intro s
  dsimp only
  rw [Nat.testBit_xor, testBit_extract, testBit_extract, testBit_extract, Nat.testBit_xor]
  by_cases hs : s < b
  · simp [hs]
  · simp [hs]

lemma popcount_winMask_le {k b p : Nat} (hk : 0 < k) (hb : b ≤ k) :
    popcount k (winMask k b p) ≤ b := by
  rw [popcount_eq_card]
  have hsub : Finset.univ.filter (fun i : Fin k => (winMask k b p).testBit i.val = true) ⊆
      Finset.univ.image (fun s : Fin b => (⟨(p + s.val) % k, Nat.mod_lt _ hk⟩ : Fin k)) := by
    intro q hq
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image] at hq ⊢
    rw [testBit_winMask hb q.isLt] at hq
    have hlt : (q.val + k - p % k) % k < b := of_decide_eq_true hq
    refine ⟨⟨(q.val + k - p % k) % k, hlt⟩, ?_⟩
    apply Fin.ext; dsimp only
    have hp : p % k < k := Nat.mod_lt _ hk
    calc (p + (q.val + k - p % k) % k) % k
        = (p % k + (q.val + k - p % k) % k) % k := by rw [Nat.add_mod, Nat.mod_mod]
      _ = (p % k + (q.val + k - p % k)) % k := by rw [Nat.add_mod_mod]
      _ = (q.val + k) % k := by congr 1; omega
      _ = q.val := by rw [Nat.add_mod_right, Nat.mod_eq_of_lt q.isLt]
  exact (Finset.card_le_card hsub).trans (Finset.card_image_le.trans (by simp))

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

def derivFmtEval (k r m : Nat) (u v_in : Fin (2 ^ k)) (cr cc : Fin r → Fin (2 ^ k))
    (A B : Fin m → Fin (2 ^ k)) (dir : Vec k) (j : Fin m) (T : Fin (2 ^ k)) : Bool :=
  let b := winSize k r
  let ψ0 := localPsi k r false u cr
  let ψ1 := localPsi k r true v_in cc
  let term0 := (List.finRange k).foldl (fun acc i =>
    xor acc ((A j).val.testBit i.val &&
      if submask T.val (winMask k b (winStart k r false i.val)) then
        derivTable (ψ0 i) (extract k b (winStart k r false i.val) (ofVec k dir).val)
          (extract k b (winStart k r false i.val) T.val)
      else false)) false
  let term1 := (List.finRange k).foldl (fun acc i =>
    xor acc ((B j).val.testBit i.val &&
      if submask T.val (winMask k b (winStart k r true i.val)) then
        derivTable (ψ1 i) (extract k b (winStart k r true i.val) (ofVec k dir).val)
          (extract k b (winStart k r true i.val) T.val)
      else false)) false
  xor term0 term1

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

lemma fmt_targetF_eq {k r m : Nat} (hk : 0 < k) (u v_in : Fin (2 ^ k))
    (cr cc : Fin r → Fin (2 ^ k)) (A B : Fin m → Fin (2 ^ k)) (j : Fin m) (T : Fin (2 ^ k)) :
    fmt (fun w : Fin (2 ^ k) => targetF k r m u v_in cr cc A B w j) T =
      xor
        (bxorFinset Finset.univ (fun i : Fin k => (A j).val.testBit i.val &&
          if submask T.val (winMask k (winSize k r) (winStart k r false i.val)) then
            fmt (localPsi k r false u cr i) (extract k (winSize k r) (winStart k r false i.val) T.val)
          else false))
        (bxorFinset Finset.univ (fun i : Fin k => (B j).val.testBit i.val &&
          if submask T.val (winMask k (winSize k r) (winStart k r true i.val)) then
            fmt (localPsi k r true v_in cc i) (extract k (winSize k r) (winStart k r true i.val) T.val)
          else false)) := by
  have hfun : (fun w : Fin (2 ^ k) => targetF k r m u v_in cr cc A B w j) =
      fun w => xor
        (bxorFinset Finset.univ (fun i : Fin k => (A j).val.testBit i.val &&
          localPsi k r false u cr i (extract k (winSize k r) (winStart k r false i.val) w.val)))
        (bxorFinset Finset.univ (fun i : Fin k => (B j).val.testBit i.val &&
          localPsi k r true v_in cc i (extract k (winSize k r) (winStart k r true i.val) w.val))) := by
    funext w
    unfold targetF
    rw [parity_eq_bxor, parity_eq_bxor]
    congr 1
    · apply bxorFinset_congr; intro i _; rw [state_testBit_eq_localPsi hk false u cr w i]
    · apply bxorFinset_congr; intro i _; rw [state_testBit_eq_localPsi hk true v_in cc w i]
  rw [hfun, fmt_xor]; dsimp only
  rw [fmt_bxorFinset, fmt_bxorFinset]; dsimp only
  congr 1
  · apply bxorFinset_congr; intro i _
    rw [fmt_scale_bool, fmt_local hk (winSize_le k r)]
  · apply bxorFinset_congr; intro i _
    rw [fmt_scale_bool, fmt_local hk (winSize_le k r)]

lemma degLe_targetF_b {k r m : Nat} (hk : 0 < k) (u v_in : Fin (2 ^ k))
    (cr cc : Fin r → Fin (2 ^ k)) (A B : Fin m → Fin (2 ^ k)) (j : Fin m) :
    degLe (fun w : Fin (2 ^ k) => targetF k r m u v_in cr cc A B w j) (winSize k r) := by
  intro T hT
  rw [fmt_targetF_eq hk]
  have hno : ∀ p : Nat, submask T.val (winMask k (winSize k r) p) = false := by
    intro p
    cases hsm : submask T.val (winMask k (winSize k r) p)
    · rfl
    · exfalso
      have h1 := popcount_submask_le (k := k) hsm
      have h2 := popcount_winMask_le (p := p) hk (winSize_le k r)
      omega
  have hz1 : bxorFinset Finset.univ (fun i : Fin k => (A j).val.testBit i.val &&
      if submask T.val (winMask k (winSize k r) (winStart k r false i.val)) then
        fmt (localPsi k r false u cr i) (extract k (winSize k r) (winStart k r false i.val) T.val)
      else false) = false := by
    apply bxorFinset_zero; intro i _; simp [hno]
  have hz2 : bxorFinset Finset.univ (fun i : Fin k => (B j).val.testBit i.val &&
      if submask T.val (winMask k (winSize k r) (winStart k r true i.val)) then
        fmt (localPsi k r true v_in cc i) (extract k (winSize k r) (winStart k r true i.val) T.val)
      else false) = false := by
    apply bxorFinset_zero; intro i _; simp [hno]
  rw [hz1, hz2]; rfl

lemma subV_top {k r m : Nat} (hk : 0 < k) (u v_in : Fin (2 ^ k))
    (cr cc : Fin r → Fin (2 ^ k)) (A B : Fin m → Fin (2 ^ k)) (d : Fin (2 ^ k)) :
    subV (targetF k r m u v_in cr cc A B) (winSize k r - 1) d := by
  intro j
  exact degLe_deriv_of_degLe (winSize_pos hk) (degLe_targetF_b hk u v_in cr cc A B j) d

lemma fmt_deriv_eq_derivFmtEval {k r m : Nat} (hk : 0 < k) (u v_in : Fin (2 ^ k))
    (cr cc : Fin r → Fin (2 ^ k)) (A B : Fin m → Fin (2 ^ k))
    (dir : Vec k) (j : Fin m) (T : Fin (2 ^ k)) :
    fmt (deriv (targetF k r m u v_in cr cc A B) (ofVec k dir) j) T =
      derivFmtEval k r m u v_in cr cc A B dir j T := by
  let b := winSize k r
  let d := ofVec k dir
  have hfun : deriv (targetF k r m u v_in cr cc A B) d j =
      fun w => xor
        (bxorFinset Finset.univ (fun i : Fin k => (A j).val.testBit i.val &&
          (fun α => xor (shiftTable (extract k b (winStart k r false i.val) d.val)
              (localPsi k r false u cr i) α)
            (localPsi k r false u cr i α)) (extract k b (winStart k r false i.val) w.val)))
        (bxorFinset Finset.univ (fun i : Fin k => (B j).val.testBit i.val &&
          (fun α => xor (shiftTable (extract k b (winStart k r true i.val) d.val)
              (localPsi k r true v_in cc i) α)
            (localPsi k r true v_in cc i α)) (extract k b (winStart k r true i.val) w.val))) := by
    funext w
    unfold deriv targetF
    rw [parity_eq_bxor, parity_eq_bxor, parity_eq_bxor, parity_eq_bxor]
    have hrearr : ∀ a1 b1 a2 b2 : Bool, xor (xor a1 b1) (xor a2 b2) = xor (xor a1 a2) (xor b1 b2) := by
      intro a1 b1 a2 b2; cases a1 <;> cases b1 <;> cases a2 <;> cases b2 <;> rfl
    rw [hrearr, ← bxorFinset_xor, ← bxorFinset_xor]
    congr 1
    · apply bxorFinset_congr; intro i _
      dsimp only
      rw [state_testBit_eq_localPsi hk false u cr ⟨w.val ^^^ d.val, xor_lt w.isLt d.isLt⟩ i,
          state_testBit_eq_localPsi hk false u cr w i,
          shiftTable_eq, ← extract_xor w d]
      cases (A j).val.testBit i.val <;> rfl
    · apply bxorFinset_congr; intro i _
      dsimp only
      rw [state_testBit_eq_localPsi hk true v_in cc ⟨w.val ^^^ d.val, xor_lt w.isLt d.isLt⟩ i,
          state_testBit_eq_localPsi hk true v_in cc w i,
          shiftTable_eq, ← extract_xor w d]
      cases (B j).val.testBit i.val <;> rfl
  rw [hfun, fmt_xor]; dsimp only
  rw [fmt_bxorFinset, fmt_bxorFinset]; dsimp only
  unfold derivFmtEval
  dsimp only
  rw [bxorFinset_finRange, bxorFinset_finRange]
  congr 1
  · apply bxorFinset_congr; intro i _
    rw [fmt_scale_bool]
    exact congrArg ((A j).val.testBit i.val && ·)
      (fmt_local hk (winSize_le k r) (winStart k r false i.val)
        (fun α => xor (shiftTable (extract k b (winStart k r false i.val) d.val)
            (localPsi k r false u cr i) α) (localPsi k r false u cr i α)) T)
  · apply bxorFinset_congr; intro i _
    rw [fmt_scale_bool]
    exact congrArg ((B j).val.testBit i.val && ·)
      (fmt_local hk (winSize_le k r) (winStart k r true i.val)
        (fun α => xor (shiftTable (extract k b (winStart k r true i.val) d.val)
            (localPsi k r true v_in cc i) α) (localPsi k r true v_in cc i α)) T)

-- Descending chain definitions
def levelEqs (k b m s : Nat) : List (Fin m × Fin k × Fin (2 ^ b)) :=
  (List.finRange m).flatMap fun j =>
    (List.finRange k).flatMap fun p =>
      ((List.finRange (2 ^ b)).filter fun α => decide (popcount b α.val = s)).map fun α =>
        (j, p, α)

def subVLevelEq (k r m : Nat) (hk : 0 < k) (u v_in : Fin (2 ^ k))
    (cr cc : Fin r → Fin (2 ^ k)) (A B : Fin m → Fin (2 ^ k))
    (V : Fin k → Vec k) (U : Fin k → Vec k)
    (eq : Fin m × Fin k × Fin (2 ^ winSize k r)) : Fin k → Vec k :=
  let (j, p, α) := eq
  let T : Fin (2 ^ k) := ⟨embed k (winSize k r) p.val α.val, embed_lt hk⟩
  let col : Vec k := fun idx => derivFmtEval k r m u v_in cr cc A B (V idx) j T
  let c : Vec k := fun row => vecDot (U row) col
  restrictKernelStep U c

def subVLevel (k r m : Nat) (hk : 0 < k) (u v_in : Fin (2 ^ k))
    (cr cc : Fin r → Fin (2 ^ k)) (A B : Fin m → Fin (2 ^ k))
    (s : Nat) (V : Fin k → Vec k) : Fin k → Vec k :=
  let U := (levelEqs k (winSize k r) m s).foldl
    (subVLevelEq k r m hk u v_in cr cc A B V) (stdBasis k)
  fun row => vecLinComb V (U row)

def subVChain (k r m : Nat) (hk : 0 < k) (u v_in : Fin (2 ^ k))
    (cr cc : Fin r → Fin (2 ^ k)) (A B : Fin m → Fin (2 ^ k)) : Fin k → Vec k :=
  ((List.range (winSize k r - 1)).reverse.map (· + 1)).foldl
    (fun V s => subVLevel k r m hk u v_in cr cc A B s V) (stdBasis k)

lemma mem_levelEqs {k b m s : Nat} (j : Fin m) (p : Fin k) (α : Fin (2 ^ b)) :
    (j, p, α) ∈ levelEqs k b m s ↔ popcount b α.val = s := by
  simp [levelEqs]

lemma subVLevel_correct {k r m : Nat} (hk : 0 < k) (u v_in : Fin (2 ^ k))
    (cr cc : Fin r → Fin (2 ^ k)) (A B : Fin m → Fin (2 ^ k))
    {s : Nat} (hs : 1 ≤ s) {V : Fin k → Vec k}
    (hV : ∀ v : Vec k, inSpan V v ↔ subV (targetF k r m u v_in cr cc A B) s (ofVec k v)) :
    ∀ v : Vec k, inSpan (subVLevel k r m hk u v_in cr cc A B s V) v ↔
      subV (targetF k r m u v_in cr cc A B) (s - 1) (ofVec k v) := by
  let f := targetF k r m u v_in cr cc A B
  let b := winSize k r
  -- On V_s, for any T with popcount k T = s, dir ↦ fmt (deriv f (ofVec k dir) j) T is additive on span V
  have hlin : ∀ (j : Fin m) (T : Fin (2 ^ k)), popcount k T.val = s →
      ∀ (a : Vec k),
        fmt (deriv f (ofVec k (vecLinComb V a)) j) T =
          vecDot a (fun idx => derivFmtEval k r m u v_in cr cc A B (V idx) j T) := by
    intro j T hTs a
    have hgen : ∀ (S : Finset (Fin k)),
        fmt (deriv f (ofVec k (fun c => bxorFinset S (fun idx => a idx && V idx c))) j) T =
          bxorFinset S (fun idx => a idx && derivFmtEval k r m u v_in cr cc A B (V idx) j T) := by
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
          exact fmt_deriv_eq_derivFmtEval hk u v_in cr cc A B (V idx) j T
    have hlc : vecLinComb V a = fun c => bxorFinset Finset.univ (fun idx => a idx && V idx c) := by
      funext c; exact vecDot_eq_bxor _ _
    rw [hlc, vecDot_eq_bxor]
    exact hgen Finset.univ
  -- Fold invariant for the kernel restriction over a list of equations
  have hfold : ∀ (eqs : List (Fin m × Fin k × Fin (2 ^ b))) (U0 : Fin k → Vec k),
      (∀ eq ∈ eqs, popcount b eq.2.2.val = s) →
      ∀ a : Vec k,
        inSpan (eqs.foldl (subVLevelEq k r m hk u v_in cr cc A B V) U0) a ↔
          inSpan U0 a ∧ ∀ eq ∈ eqs,
            fmt (deriv f (ofVec k (vecLinComb V a)) eq.1)
              ⟨embed k b eq.2.1.val eq.2.2.val, embed_lt hk⟩ = false := by
    intro eqs
    induction eqs with
    | nil => intro U0 _ a; simp
    | cons eq eqs ih =>
      intro U0 heqs a
      simp only [List.foldl_cons]
      rw [ih _ (fun e he => heqs e (List.mem_cons_of_mem _ he))]
      rcases eq with ⟨j, p, α⟩
      have hpc : popcount b α.val = s := heqs (j, p, α) List.mem_cons_self
      have hTs : popcount k (embed k b p.val α.val) = s := by
        rw [popcount_embed (winSize_le k r) α.isLt]; exact hpc
      set T : Fin (2 ^ k) := ⟨embed k b p.val α.val, embed_lt hk⟩
      set col : Vec k := fun idx => derivFmtEval k r m u v_in cr cc A B (V idx) j T
      have hstep_iff : inSpan (subVLevelEq k r m hk u v_in cr cc A B V U0 (j, p, α)) a ↔
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
  -- Apply hfold to levelEqs
  intro v
  unfold subVLevel
  dsimp only
  rw [inSpan_comp]
  have heqs_pc : ∀ eq ∈ levelEqs k b m s, popcount b eq.2.2.val = s := by
    rintro ⟨j, p, α⟩ hmem; exact (mem_levelEqs j p α).mp hmem
  constructor
  · rintro ⟨a, haU, rfl⟩
    have hfa := (hfold (levelEqs k b m s) (stdBasis k) heqs_pc a).mp haU
    have hVs : subV f s (ofVec k (vecLinComb V a)) := (hV _).mp ⟨a, rfl⟩
    intro j T hT
    by_cases hgt : s < popcount k T.val
    · exact hVs j T hgt
    · have hTeq : popcount k T.val = s := by omega
      by_cases hexp : ∃ p : Fin k, submask T.val (winMask k b p.val) = true
      · obtain ⟨p, hp⟩ := hexp
        set α : Fin (2 ^ b) := extract k b p.val T.val
        have hTemb : T = ⟨embed k b p.val α.val, embed_lt hk⟩ :=
          Fin.ext ((submask_winMask_iff hk (winSize_le k r) T.isLt).mp hp).symm
        have hαpc : popcount b α.val = s := by
          have := popcount_embed (p := p.val) (winSize_le k r) α.isLt
          have hval : (embed k b p.val α.val) = T.val := congrArg Fin.val hTemb.symm
          rw [hval, hTeq] at this; exact this.symm
        have hmem : (j, p, α) ∈ levelEqs k b m s := (mem_levelEqs j p α).mpr hαpc
        have hres := hfa.2 (j, p, α) hmem
        simpa only [← hTemb] using hres
      · simp only [not_exists] at hexp
        have hno : ∀ p : Fin k, submask T.val (winMask k b p.val) = false :=
          fun p => Bool.eq_false_iff.mpr (hexp p)
        rw [fmt_deriv_eq_derivFmtEval hk]
        unfold derivFmtEval
        dsimp only
        rw [bxorFinset_finRange, bxorFinset_finRange]
        have hz0 : bxorFinset Finset.univ (fun i : Fin k => (A j).val.testBit i.val &&
            if submask T.val (winMask k b (winStart k r false i.val)) then
              derivTable (localPsi k r false u cr i)
                (extract k b (winStart k r false i.val) (ofVec k (vecLinComb V a)).val)
                (extract k b (winStart k r false i.val) T.val)
            else false) = false := by
          apply bxorFinset_zero; intro i _
          have hlt : winStart k r false i.val < k := Nat.mod_lt _ hk
          have := hno ⟨winStart k r false i.val, hlt⟩
          simp [this]
        have hz1 : bxorFinset Finset.univ (fun i : Fin k => (B j).val.testBit i.val &&
            if submask T.val (winMask k b (winStart k r true i.val)) then
              derivTable (localPsi k r true v_in cc i)
                (extract k b (winStart k r true i.val) (ofVec k (vecLinComb V a)).val)
                (extract k b (winStart k r true i.val) T.val)
            else false) = false := by
          apply bxorFinset_zero; intro i _
          have hlt : winStart k r true i.val < k := Nat.mod_lt _ hk
          have := hno ⟨winStart k r true i.val, hlt⟩
          simp [this]
        rw [hz0, hz1]; rfl
  · intro hv
    have hVs : subV f s (ofVec k v) := fun j T hT => hv j T (by omega)
    obtain ⟨a, rfl⟩ := (hV v).mpr hVs
    refine ⟨a, ?_, rfl⟩
    rw [hfold (levelEqs k b m s) (stdBasis k) heqs_pc a]
    refine ⟨inSpan_stdBasis a, ?_⟩
    rintro ⟨j, p, α⟩ hmem
    have hpc : popcount b α.val = s := (mem_levelEqs j p α).mp hmem
    have hTs : popcount k (embed k b p.val α.val) = s := by
      rw [popcount_embed (winSize_le k r) α.isLt]; exact hpc
    exact hv j ⟨embed k b p.val α.val, embed_lt hk⟩ (by dsimp; omega)

lemma inSpan_subVChain {k r m : Nat} (hk : 0 < k) (u v_in : Fin (2 ^ k))
    (cr cc : Fin r → Fin (2 ^ k)) (A B : Fin m → Fin (2 ^ k)) (v : Vec k) :
    inSpan (subVChain k r m hk u v_in cr cc A B) v ↔
      subV (targetF k r m u v_in cr cc A B) 0 (ofVec k v) := by
  have hgen : ∀ (t : Nat) (V : Fin k → Vec k),
      (∀ v : Vec k, inSpan V v ↔ subV (targetF k r m u v_in cr cc A B) t (ofVec k v)) →
      ∀ v : Vec k,
        inSpan (((List.range t).reverse.map (· + 1)).foldl
          (fun W s => subVLevel k r m hk u v_in cr cc A B s W) V) v ↔
        subV (targetF k r m u v_in cr cc A B) 0 (ofVec k v) := by
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
      exact ih _ (subVLevel_correct hk u v_in cr cc A B (by omega) hV) v
  unfold subVChain
  exact hgen (winSize k r - 1) (stdBasis k)
    (fun w => ⟨fun _ => subV_top hk u v_in cr cc A B _, fun _ => inSpan_stdBasis w⟩) v

lemma subV_zero_iff_good {k r m : Nat} (u v_in : Fin (2 ^ k))
    (cr cc : Fin r → Fin (2 ^ k)) (A B : Fin m → Fin (2 ^ k)) (d : Fin (2 ^ k)) :
    subV (targetF k r m u v_in cr cc A B) 0 d ↔
      ∃ a : Fin m → Bool, ∀ (w : Fin (2 ^ k)) (j : Fin m),
        xor (targetF k r m u v_in cr cc A B ⟨w.val ^^^ d.val, xor_lt w.isLt d.isLt⟩ j)
            (targetF k r m u v_in cr cc A B w j) = a j := by
  unfold subV deriv
  constructor
  · intro h
    have hex : ∀ j : Fin m, ∃ a : Bool, ∀ w : Fin (2 ^ k),
        xor (targetF k r m u v_in cr cc A B ⟨w.val ^^^ d.val, xor_lt w.isLt d.isLt⟩ j)
            (targetF k r m u v_in cr cc A B w j) = a :=
      fun j => (degLe_zero_iff_const _).mp (h j)
    exact ⟨fun j => Classical.choose (hex j), fun w j => Classical.choose_spec (hex j) w⟩
  · rintro ⟨a, ha⟩ j
    exact (degLe_zero_iff_const _).mpr ⟨a j, fun w => ha w j⟩

-- ============================================================
-- PART 6: Binary Arithmetic, Spec Correctness, Circuit Builder & Main Theorem
-- ============================================================

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

def evalSpec (k r m q : Nat) (hk : 0 < k) (u v : Fin (2 ^ k))
    (cr cc : Fin r → Fin (2 ^ k)) (A B : Fin m → Fin (2 ^ k))
    (y : Fin m → Bool) (t : Fin (2 ^ (k + 1))) : Bool :=
  let V := subVChain k r m hk u v cr cc A B
  let echV := echelon V
  let dimOk := dimGe echV.hasP q
  let f0 : Vec m := targetF k r m u v cr cc A B ⟨0, Nat.two_pow_pos k⟩
  let resp : Fin q → Vec m := fun idx =>
    vecXor (targetF k r m u v cr cc A B (ofVec k (selDir echV.hasP echV.piv idx))) f0
  let echR := echelon resp
  let pass : Fin (2 ^ (k - q)) → Bool := fun σ =>
    !(anyBit (echelonReduce echR.hasP echR.piv
      (vecXor (targetF k r m u v cr cc A B (ofVec k (seedVec echV.hasP q σ))) y)))
  let pc := countBits (k + 1) (List.finRange (2 ^ (k - q))) pass
  let hitsVec := shiftByRank echR.hasP q (k + 1) pc
  let hitsOk := leVec (toVec (k + 1) t) hitsVec
  dimOk && hitsOk

lemma evalSpec_correct {k r m q : Nat} (hk : 0 < k) (hqk : q ≤ k)
    (u v : Fin (2 ^ k)) (cr cc : Fin r → Fin (2 ^ k)) (A B : Fin m → Fin (2 ^ k))
    (y : Fin m → Bool) (t : Fin (2 ^ (k + 1))) :
    let f := fun (w : Nat) (j : Fin m) =>
      xor (parity k (A j).val (state k r false w u.val cr))
          (parity k (B j).val (state k r true w v.val cc))
    let good := fun (d : Fin (2 ^ k)) => ∃ a : Fin m → Bool,
      ∀ (w : Fin (2 ^ k)) (j : Fin m), xor (f (w.val ^^^ d.val) j) (f w.val j) = a j
    let hits := Nat.card {w : Fin (2 ^ k) // ∀ j, f w.val j = y j}
    evalSpec k r m q hk u v cr cc A B y t =
      decide (2 ^ q ≤ Nat.card {d : Fin (2 ^ k) // good d} ∧ t.val ≤ hits) := by
  intro f good hits
  classical
  unfold evalSpec
  dsimp only
  set V := subVChain k r m hk u v cr cc A B
  set echV := echelon V
  have hcard_good : Nat.card {d : Fin (2 ^ k) // good d} = 2 ^ cntAt echV.hasP k := by
    have hbij : Nat.card {d : Fin (2 ^ k) // good d} = Nat.card {vec : Vec k // inSpan V vec} := by
      rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
      apply Fintype.card_of_bijective (f := fun ⟨d, hd⟩ =>
        ⟨toVec k d, (inSpan_subVChain hk u v cr cc A B (toVec k d)).mpr
          (by rw [ofVec_toVec]; exact (subV_zero_iff_good u v cr cc A B d).mpr hd)⟩)
      constructor
      · rintro ⟨d1, _⟩ ⟨d2, _⟩ heq
        have hv : toVec k d1 = toVec k d2 := congrArg Subtype.val heq
        apply Subtype.ext; dsimp only
        rw [← ofVec_toVec d1, ← ofVec_toVec d2, hv]
      · rintro ⟨vec, hvec⟩
        have hsub : subV (targetF k r m u v cr cc A B) 0 (ofVec k vec) :=
          (inSpan_subVChain hk u v cr cc A B vec).mp hvec
        refine ⟨⟨ofVec k vec, (subV_zero_iff_good u v cr cc A B _).mp hsub⟩, Subtype.ext (toVec_ofVec vec)⟩
    rw [hbij, echelon_card_span V, cntAt_full]
  have hdim_iff : 2 ^ q ≤ Nat.card {d : Fin (2 ^ k) // good d} ↔ q ≤ cntAt echV.hasP k := by
    rw [hcard_good]
    exact Nat.pow_le_pow_iff_right (by omega : 1 < 2)
  rw [dimGe_eq_decide echV.hasP hqk]
  by_cases hq : q ≤ cntAt echV.hasP k
  · simp only [hq, decide_true, Bool.true_and]
    have hdimT : 2 ^ q ≤ Nat.card {d : Fin (2 ^ k) // good d} := hdim_iff.mpr hq
    simp only [hdimT, true_and]
    set f0 : Vec m := targetF k r m u v cr cc A B ⟨0, Nat.two_pow_pos k⟩
    set resp : Fin q → Vec m := fun idx =>
      vecXor (targetF k r m u v cr cc A B (ofVec k (selDir echV.hasP echV.piv idx))) f0
    set echR := echelon resp
    have hgood_resp : ∀ (idx : Fin q) (w : Fin (2 ^ k)),
        vecXor (targetF k r m u v cr cc A B
          ⟨w.val ^^^ (ofVec k (selDir echV.hasP echV.piv idx)).val, xor_lt w.isLt (ofVec k _).isLt⟩)
          (targetF k r m u v cr cc A B w) = resp idx := by
      intro idx w
      have hin : inSpan V (selDir echV.hasP echV.piv idx) :=
        (echelon_inSpan V _).mp ⟨isPiv echV.hasP idx, rfl⟩
      have hgd : good (ofVec k (selDir echV.hasP echV.piv idx)) :=
        (subV_zero_iff_good u v cr cc A B _).mp ((inSpan_subVChain hk u v cr cc A B _).mp hin)
      obtain ⟨a, ha⟩ := hgd
      funext j
      have hw := ha w j
      have h0 := ha ⟨0, Nat.two_pow_pos k⟩ j
      simp only [Nat.zero_xor] at h0
      have h0' : xor (targetF k r m u v cr cc A B (ofVec k (selDir echV.hasP echV.piv idx)) j) (f0 j) = a j := by
        simpa [targetF, f, f0] using h0
      have hw' : xor (targetF k r m u v cr cc A B
          ⟨w.val ^^^ (ofVec k (selDir echV.hasP echV.piv idx)).val, xor_lt w.isLt (ofVec k _).isLt⟩ j)
          (targetF k r m u v cr cc A B w j) = a j := by
        simpa [targetF, f] using hw
      simp only [vecXor, resp]
      rw [hw', ← h0']
    have hcoset := coset_hits_eq hqk (echelon_tri V) hq (targetF k r m u v cr cc A B) y resp hgood_resp
    dsimp only at hcoset
    have hhits_eq : hits = Nat.card {w : Fin (2 ^ k) // targetF k r m u v cr cc A B w = y} :=
      Nat.card_congr (Equiv.subtypeEquivRight fun w =>
        ⟨fun h => funext h, fun h j => congrFun h j⟩)
    rw [hhits_eq, hcoset]
    set pass : Fin (2 ^ (k - q)) → Bool := fun σ =>
      !(anyBit (echelonReduce echR.hasP echR.piv
        (vecXor (targetF k r m u v cr cc A B (ofVec k (seedVec echV.hasP q σ))) y)))
    have hpc_lt : 2 ^ (k - q) < 2 ^ (k + 1) :=
      Nat.pow_lt_pow_right (by omega) (by omega)
    have hpc_val : (ofVec (k + 1) (countBits (k + 1) (List.finRange (2 ^ (k - q))) pass)).val =
        (Finset.univ.filter (fun σ : Fin (2 ^ (k - q)) =>
          echelonReduce echR.hasP echR.piv
            (vecXor (targetF k r m u v cr cc A B (ofVec k (seedVec echV.hasP q σ))) y) = vecZero m)).card := by
      rw [ofVec_countBits_finRange pass hpc_lt]
      congr 1; ext σ
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      dsimp only [pass]
      rw [not_anyBit_eq_decide, decide_eq_true_eq]
    have hρ_le : cntAt echR.hasP m ≤ q := by
      have := echelon_rank_le resp
      simpa [echR, cntAt_full] using this
    have hhits_lt : (Finset.univ.filter (fun σ : Fin (2 ^ (k - q)) =>
          echelonReduce echR.hasP echR.piv
            (vecXor (targetF k r m u v cr cc A B (ofVec k (seedVec echV.hasP q σ))) y) = vecZero m)).card *
        2 ^ (q - cntAt echR.hasP m) < 2 ^ (k + 1) := by
      rw [← hcoset, Nat.card_eq_fintype_card, Fintype.card_subtype]
      calc (Finset.univ.filter (fun w : Fin (2 ^ k) => targetF k r m u v cr cc A B w = y)).card
          ≤ (Finset.univ : Finset (Fin (2 ^ k))).card := Finset.card_filter_le _ _
        _ = 2 ^ k := by simp
        _ < 2 ^ (k + 1) := Nat.pow_lt_pow_right (by omega) (by omega)
    have hshift := ofVec_shiftByRank echR.hasP (countBits (k + 1) (List.finRange (2 ^ (k - q))) pass)
      hρ_le (by rw [hpc_val]; exact hhits_lt)
    rw [hpc_val] at hshift
    rw [leVec_eq_decide, ofVec_toVec, hshift]
  · simp only [hq, decide_false, Bool.false_and]
    have hdimF : ¬(2 ^ q ≤ Nat.card {d : Fin (2 ^ k) // good d}) := fun h => hq (hdim_iff.mp h)
    symm; exact decide_eq_false (fun h => hdimF h.1)

-- ============================================================
-- Input Bit Layout & Decoding Round-Trip
-- ============================================================

def inLen (k r m : Nat) : Nat := 2 * k + 2 * r * k + 2 * m * k + m + (k + 1)

def bitsList (n x : Nat) : List Bool := (List.range n).map (fun i => x.testBit i)

def bankList {k m : Nat} (A : Fin m → Fin (2 ^ k)) : List Bool :=
  (List.finRange m).flatMap (fun j => bitsList k (A j).val)

def schedList {k r : Nat} (c : Fin r → Fin (2 ^ k)) : List Bool :=
  (List.finRange r).flatMap (fun j => bitsList k (c j).val)

def inputList {k r m : Nat} (u v : Fin (2 ^ k)) (cr cc : Fin r → Fin (2 ^ k))
    (A B : Fin m → Fin (2 ^ k)) (y : Fin m → Bool) (t : Fin (2 ^ (k + 1))) : List Bool :=
  bitsList k u.val ++ bitsList k v.val ++ schedList cr ++ schedList cc ++
    bankList A ++ bankList B ++ List.ofFn y ++ bitsList (k + 1) t.val

lemma length_bitsList (n x : Nat) : (bitsList n x).length = n := by
  simp [bitsList]

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
    (l.flatMap f)[j * k + i]'hidx = (f (l[j]'hj))[i]'(by rw [hf _ (List.getElem_mem hj)]; exact hi) := by
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
      have hsub : (j + 1) * k + i - (f a).length = j * k + i := by rw [hlen, Nat.add_mul, Nat.one_mul]; omega
      simp only [hsub]
      exact ih (fun x hx => hf x (List.mem_cons_of_mem _ hx)) (by simpa using hj) _

lemma length_schedList {k r : Nat} (c : Fin r → Fin (2 ^ k)) : (schedList c).length = r * k := by
  unfold schedList
  rw [length_flatMap_const _ _ k (fun _ _ => length_bitsList k _), List.length_finRange]

lemma length_bankList {k m : Nat} (A : Fin m → Fin (2 ^ k)) : (bankList A).length = m * k := by
  unfold bankList
  rw [length_flatMap_const _ _ k (fun _ _ => length_bitsList k _), List.length_finRange]

lemma length_inputList {k r m : Nat} (u v : Fin (2 ^ k)) (cr cc : Fin r → Fin (2 ^ k))
    (A B : Fin m → Fin (2 ^ k)) (y : Fin m → Bool) (t : Fin (2 ^ (k + 1))) :
    (inputList u v cr cc A B y t).length = inLen k r m := by
  unfold inputList inLen
  simp only [List.length_append, length_bitsList, length_schedList, length_bankList, List.length_ofFn]
  ring

def encBits {k r m : Nat} (u v : Fin (2 ^ k)) (cr cc : Fin r → Fin (2 ^ k))
    (A B : Fin m → Fin (2 ^ k)) (y : Fin m → Bool) (t : Fin (2 ^ (k + 1))) :
    Fin (inLen k r m) → Bool :=
  fun idx => (inputList u v cr cc A B y t).getD idx.val false

lemma ofFn_encBits {k r m : Nat} (u v : Fin (2 ^ k)) (cr cc : Fin r → Fin (2 ^ k))
    (A B : Fin m → Fin (2 ^ k)) (y : Fin m → Bool) (t : Fin (2 ^ (k + 1))) :
    List.ofFn (encBits u v cr cc A B y t) = inputList u v cr cc A B y t := by
  apply List.ext_getElem
  · simp [length_inputList]
  · intro i h1 h2
    simp only [List.getElem_ofFn, encBits, List.getD_eq_getElem?_getD]
    rw [List.getElem?_eq_getElem h2]; rfl

def decU {k r m : Nat} (x : Fin (inLen k r m) → Bool) : Fin (2 ^ k) :=
  ofVec k (fun i => x ⟨i.val, by unfold inLen; omega⟩)

def decV {k r m : Nat} (x : Fin (inLen k r m) → Bool) : Fin (2 ^ k) :=
  ofVec k (fun i => x ⟨k + i.val, by unfold inLen; omega⟩)

def decCr {k r m : Nat} (x : Fin (inLen k r m) → Bool) (j : Fin r) : Fin (2 ^ k) :=
  ofVec k (fun i => x ⟨2 * k + j.val * k + i.val, by
    unfold inLen; have := Nat.mul_le_mul_right k (Nat.succ_le_of_lt j.isLt); nlinarith [i.isLt]⟩)

def decCc {k r m : Nat} (x : Fin (inLen k r m) → Bool) (j : Fin r) : Fin (2 ^ k) :=
  ofVec k (fun i => x ⟨2 * k + r * k + j.val * k + i.val, by
    unfold inLen; have := Nat.mul_le_mul_right k (Nat.succ_le_of_lt j.isLt); nlinarith [i.isLt]⟩)

def decA {k r m : Nat} (x : Fin (inLen k r m) → Bool) (j : Fin m) : Fin (2 ^ k) :=
  ofVec k (fun i => x ⟨2 * k + 2 * r * k + j.val * k + i.val, by
    unfold inLen; have := Nat.mul_le_mul_right k (Nat.succ_le_of_lt j.isLt); nlinarith [i.isLt]⟩)

def decB {k r m : Nat} (x : Fin (inLen k r m) → Bool) (j : Fin m) : Fin (2 ^ k) :=
  ofVec k (fun i => x ⟨2 * k + 2 * r * k + m * k + j.val * k + i.val, by
    unfold inLen; have := Nat.mul_le_mul_right k (Nat.succ_le_of_lt j.isLt); nlinarith [i.isLt]⟩)

def decY {k r m : Nat} (x : Fin (inLen k r m) → Bool) (j : Fin m) : Bool :=
  x ⟨2 * k + 2 * r * k + 2 * m * k + j.val, by unfold inLen; omega⟩

def decT {k r m : Nat} (x : Fin (inLen k r m) → Bool) : Fin (2 ^ (k + 1)) :=
  ofVec (k + 1) (fun i => x ⟨2 * k + 2 * r * k + 2 * m * k + m + i.val, by unfold inLen; omega⟩)

private lemma getD_append_left {α : Type} (l1 l2 : List α) (i : Nat) (d : α) (hi : i < l1.length) :
    (l1 ++ l2).getD i d = l1.getD i d := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

private lemma getD_append_right {α : Type} (l1 l2 : List α) (i : Nat) (d : α) (hi : l1.length ≤ i) :
    (l1 ++ l2).getD i d = l2.getD (i - l1.length) d := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append_right hi]

lemma dec_encBits {k r m : Nat} (u v : Fin (2 ^ k)) (cr cc : Fin r → Fin (2 ^ k))
    (A B : Fin m → Fin (2 ^ k)) (y : Fin m → Bool) (t : Fin (2 ^ (k + 1))) :
    decU (encBits u v cr cc A B y t) = u ∧
    decV (encBits u v cr cc A B y t) = v ∧
    decCr (encBits u v cr cc A B y t) = cr ∧
    decCc (encBits u v cr cc A B y t) = cc ∧
    decA (encBits u v cr cc A B y t) = A ∧
    decB (encBits u v cr cc A B y t) = B ∧
    decY (encBits u v cr cc A B y t) = y ∧
    decT (encBits u v cr cc A B y t) = t := by
  have hbits_getD : ∀ (n x i : Nat), i < n → (bitsList n x).getD i false = x.testBit i := by
    intro n x i hi
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simp [length_bitsList, hi])]
    simp [bitsList]
  have hfin_ofVec : ∀ (n : Nat) (a b : Fin (2 ^ n)),
      (∀ i : Fin n, a.val.testBit i.val = b.val.testBit i.val) → a = b := by
    intro n a b h
    apply Fin.ext; apply Nat.eq_of_testBit_eq; intro i
    by_cases hi : i < n
    · exact h ⟨i, hi⟩
    · rw [Nat.testBit_lt_two_pow (a.isLt.trans_le (Nat.pow_le_pow_right Nat.zero_lt_two (by omega))),
          Nat.testBit_lt_two_pow (b.isLt.trans_le (Nat.pow_le_pow_right Nat.zero_lt_two (by omega)))]
  have hsched_getD : ∀ {d : Nat} (f : Fin d → Fin (2 ^ k)) (j : Fin d) (i : Fin k),
      ((List.finRange d).flatMap (fun j => bitsList k (f j).val)).getD (j.val * k + i.val) false =
        (f j).val.testBit i.val := by
    intro d f j i
    have hlen : ((List.finRange d).flatMap (fun j => bitsList k (f j).val)).length = d * k := by
      rw [length_flatMap_const _ _ k (fun _ _ => length_bitsList k _), List.length_finRange]
    have hidx : j.val * k + i.val < ((List.finRange d).flatMap (fun j => bitsList k (f j).val)).length := by
      rw [hlen]; have := Nat.mul_le_mul_right k (Nat.succ_le_of_lt j.isLt); nlinarith [i.isLt]
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hidx]
    dsimp only [Option.getD]
    rw [getElem_flatMap_const (List.finRange d) _ k (fun _ _ => length_bitsList k _) (by simp [j.isLt]) i.isLt hidx]
    simp [bitsList, List.getElem_finRange]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · apply hfin_ofVec; intro i
    simp only [decU, testBit_ofVec, i.isLt, ↓reduceDIte, encBits, inputList]
    repeat rw [getD_append_left _ _ _ _ (by simp [length_bitsList, length_schedList, length_bankList]; try nlinarith [i.isLt])]
    exact hbits_getD k u.val i.val i.isLt
  · apply hfin_ofVec; intro i
    simp only [decV, testBit_ofVec, i.isLt, ↓reduceDIte, encBits, inputList]
    rw [getD_append_left _ _ _ _ (by simp [length_bitsList, length_schedList, length_bankList]; nlinarith [i.isLt]),
        getD_append_left _ _ _ _ (by simp [length_bitsList, length_schedList, length_bankList]; nlinarith [i.isLt]),
        getD_append_left _ _ _ _ (by simp [length_bitsList, length_schedList, length_bankList]; nlinarith [i.isLt]),
        getD_append_left _ _ _ _ (by simp [length_bitsList, length_schedList, length_bankList]; nlinarith [i.isLt]),
        getD_append_left _ _ _ _ (by simp [length_bitsList, length_schedList, length_bankList]; nlinarith [i.isLt]),
        getD_append_left _ _ _ _ (by simp [length_bitsList]),
        getD_append_right _ _ _ _ (by simp [length_bitsList])]
    simp only [length_bitsList, Nat.add_sub_cancel_left]
    exact hbits_getD k v.val i.val i.isLt
  · funext j; apply hfin_ofVec; intro i
    have hmul : j.val * k + i.val < r * k := by
      have := Nat.mul_le_mul_right k (Nat.succ_le_of_lt j.isLt); nlinarith [i.isLt]
    simp only [decCr, testBit_ofVec, i.isLt, ↓reduceDIte, encBits, inputList]
    rw [getD_append_left _ _ _ _ (by simp [length_bitsList, length_schedList, length_bankList]; nlinarith),
        getD_append_left _ _ _ _ (by simp [length_bitsList, length_schedList, length_bankList]; nlinarith),
        getD_append_left _ _ _ _ (by simp [length_bitsList, length_schedList, length_bankList]; nlinarith),
        getD_append_left _ _ _ _ (by simp [length_bitsList, length_schedList, length_bankList]; nlinarith),
        getD_append_left _ _ _ _ (by simp [length_bitsList, length_schedList, length_bankList]; nlinarith),
        getD_append_right _ _ _ _ (by simp [length_bitsList]; omega)]
    have hsub : 2 * k + j.val * k + i.val - (bitsList k u.val ++ bitsList k v.val).length = j.val * k + i.val := by
      simp [length_bitsList]; omega
    rw [hsub]; exact hsched_getD cr j i
  · funext j; apply hfin_ofVec; intro i
    have hmul : j.val * k + i.val < r * k := by
      have := Nat.mul_le_mul_right k (Nat.succ_le_of_lt j.isLt); nlinarith [i.isLt]
    simp only [decCc, testBit_ofVec, i.isLt, ↓reduceDIte, encBits, inputList]
    rw [getD_append_left _ _ _ _ (by simp [length_bitsList, length_schedList, length_bankList]; nlinarith),
        getD_append_left _ _ _ _ (by simp [length_bitsList, length_schedList, length_bankList]; nlinarith),
        getD_append_left _ _ _ _ (by simp [length_bitsList, length_schedList, length_bankList]; nlinarith),
        getD_append_left _ _ _ _ (by simp [length_bitsList, length_schedList, length_bankList]; nlinarith),
        getD_append_right _ _ _ _ (by simp [length_bitsList, length_schedList]; omega)]
    have hsub : 2 * k + r * k + j.val * k + i.val -
        (bitsList k u.val ++ bitsList k v.val ++ schedList cr).length = j.val * k + i.val := by
      simp [length_bitsList, length_schedList]; omega
    rw [hsub]; exact hsched_getD cc j i
  · funext j; apply hfin_ofVec; intro i
    have hmul : j.val * k + i.val < m * k := by
      have := Nat.mul_le_mul_right k (Nat.succ_le_of_lt j.isLt); nlinarith [i.isLt]
    simp only [decA, testBit_ofVec, i.isLt, ↓reduceDIte, encBits, inputList]
    rw [getD_append_left _ _ _ _ (by simp [length_bitsList, length_schedList, length_bankList]; nlinarith),
        getD_append_left _ _ _ _ (by simp [length_bitsList, length_schedList, length_bankList]; nlinarith),
        getD_append_left _ _ _ _ (by simp [length_bitsList, length_schedList, length_bankList]; nlinarith),
        getD_append_right _ _ _ _ (by simp [length_bitsList, length_schedList]; nlinarith)]
    have hsub : 2 * k + 2 * r * k + j.val * k + i.val -
        (bitsList k u.val ++ bitsList k v.val ++ schedList cr ++ schedList cc).length = j.val * k + i.val := by
      simp [length_bitsList, length_schedList]; rw [Nat.mul_assoc 2 r k]; omega
    rw [hsub]; exact hsched_getD A j i
  · funext j; apply hfin_ofVec; intro i
    have hmul : j.val * k + i.val < m * k := by
      have := Nat.mul_le_mul_right k (Nat.succ_le_of_lt j.isLt); nlinarith [i.isLt]
    simp only [decB, testBit_ofVec, i.isLt, ↓reduceDIte, encBits, inputList]
    rw [getD_append_left _ _ _ _ (by simp [length_bitsList, length_schedList, length_bankList]; nlinarith),
        getD_append_left _ _ _ _ (by simp [length_bitsList, length_schedList, length_bankList]; nlinarith),
        getD_append_right _ _ _ _ (by simp [length_bitsList, length_schedList, length_bankList]; nlinarith)]
    have hsub : 2 * k + 2 * r * k + m * k + j.val * k + i.val -
        (bitsList k u.val ++ bitsList k v.val ++ schedList cr ++ schedList cc ++ bankList A).length =
        j.val * k + i.val := by
      simp [length_bitsList, length_schedList, length_bankList]; rw [Nat.mul_assoc 2 r k]; omega
    rw [hsub]; exact hsched_getD B j i
  · funext j
    simp only [decY, encBits, inputList]
    rw [getD_append_left _ _ _ _ (by simp [length_bitsList, length_schedList, length_bankList]; nlinarith [j.isLt]),
        getD_append_right _ _ _ _ (by simp [length_bitsList, length_schedList, length_bankList]; nlinarith)]
    have hsub : 2 * k + 2 * r * k + 2 * m * k + j.val -
        (bitsList k u.val ++ bitsList k v.val ++ schedList cr ++ schedList cc ++
          bankList A ++ bankList B).length = j.val := by
      simp [length_bitsList, length_schedList, length_bankList]; rw [Nat.mul_assoc 2 r k, Nat.mul_assoc 2 m k]; omega
    rw [hsub, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simp [j.isLt])]
    simp
  · apply hfin_ofVec; intro i
    simp only [decT, testBit_ofVec, i.isLt, ↓reduceDIte, encBits, inputList]
    rw [getD_append_right _ _ _ _ (by simp [length_bitsList, length_schedList, length_bankList]; nlinarith)]
    have hsub : 2 * k + 2 * r * k + 2 * m * k + m + i.val -
        (bitsList k u.val ++ bitsList k v.val ++ schedList cr ++ schedList cc ++
          bankList A ++ bankList B ++ List.ofFn y).length = i.val := by
      simp [length_bitsList, length_schedList, length_bankList]; rw [Nat.mul_assoc 2 r k, Nat.mul_assoc 2 m k]; omega
    rw [hsub]; exact hbits_getD (k + 1) t.val i.val i.isLt

-- ============================================================
-- Circuit Synthesis Combinators (Builder.Bank)
-- ============================================================

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

private lemma grow_stateBits {n k r : Nat} (hk : 0 < k) (col : Bool) (B : Bank n)
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

private lemma grow_parityBit {n k : Nat} (B : Bank n)
    (mask val : (Fin n → Bool) → Nat)
    (hm : ∀ i : Fin k, B.Has (fun x => (mask x).testBit i.val))
    (hv : ∀ i : Fin k, B.Has (fun x => (val x).testBit i.val)) :
    B.Grow (k * 1 + (1 + k * 4)) (fun D => D.Has (fun x => parity k (mask x) (val x))) := by
  have h1 : B.Grow (k * 1) (fun D => ∀ i : Fin k, D.Has (fun x => (mask x).testBit i.val && (val x).testBit i.val)) :=
    B.collectFin k _ 1 (fun D e i => Bank.meet (e (hm i)) (e (hv i)))
  apply h1.bind (b := 1 + k * 4)
  intro D _ hD
  have h2 := D.xorList (List.finRange k) (fun i x => (mask x).testBit i.val && (val x).testBit i.val) (fun i _ => hD i)
  refine h2.weaken (by simp) (fun E hE => ?_)
  exact has_congr hE (fun x => by
    unfold parity
    have hmap : List.range k = (List.finRange k).map Fin.val := by apply List.ext_getElem <;> simp
    rw [hmap, List.foldl_map])

private lemma grow_targetFBits {n k r m : Nat} (hk : 0 < k) (B : Bank n)
    (u v : (Fin n → Bool) → Fin (2 ^ k))
    (cr cc : (Fin n → Bool) → Fin r → Fin (2 ^ k))
    (A B_mask : (Fin n → Bool) → Fin m → Fin (2 ^ k))
    (w : (Fin n → Bool) → Fin (2 ^ k))
    (hu : ∀ i : Fin k, B.Has (fun x => (u x).val.testBit i.val))
    (hv : ∀ i : Fin k, B.Has (fun x => (v x).val.testBit i.val))
    (hcr : ∀ (j : Fin r) (i : Fin k), B.Has (fun x => (cr x j).val.testBit i.val))
    (hcc : ∀ (j : Fin r) (i : Fin k), B.Has (fun x => (cc x j).val.testBit i.val))
    (hA : ∀ (j : Fin m) (i : Fin k), B.Has (fun x => (A x j).val.testBit i.val))
    (hB : ∀ (j : Fin m) (i : Fin k), B.Has (fun x => (B_mask x j).val.testBit i.val))
    (hw : ∀ i : Fin k, B.Has (fun x => (w x).val.testBit i.val)) :
    B.Grow (2 * (k * 4 + r * (k * 22)) + m * (10 * k + 6))
      (fun D => ∀ j : Fin m, D.Has (fun x => targetF k r m (u x) (v x) (cr x) (cc x) (A x) (B_mask x) (w x) j)) := by
  obtain ⟨D1, e1, c1, hs0⟩ := grow_stateBits hk false B w u cr hw hu hcr
  obtain ⟨D2, e2, c2, hs1⟩ := grow_stateBits hk true D1 w v cc
    (fun i => e1 (hw i)) (fun i => e1 (hv i)) (fun j i => e1 (hcc j i))
  obtain ⟨D3, e3, c3, hf⟩ := D2.collectFin m
    (fun j x => targetF k r m (u x) (v x) (cr x) (cc x) (A x) (B_mask x) (w x) j)
    (10 * k + 6) (fun D e j => by
      obtain ⟨E1, ee1, cc1, hp0⟩ := grow_parityBit D (fun x => (A x j).val)
        (fun x => state k r false (w x).val (u x).val (cr x))
        (fun i => e (e2 (e1 (hA j i)))) (fun i => e (e2 (hs0 i)))
      obtain ⟨E2, ee2, cc2, hp1⟩ := grow_parityBit E1 (fun x => (B_mask x j).val)
        (fun x => state k r true (w x).val (v x).val (cc x))
        (fun i => ee1 (e (e2 (e1 (hB j i))))) (fun i => ee1 (e (hs1 i)))
      obtain ⟨E3, ee3, cc3, hx⟩ := Bank.xor2 (ee2 hp0) hp1
      exact ⟨E3, Bank.ext_trans ee1 (Bank.ext_trans ee2 ee3), by omega, hx⟩)
  exact ⟨D3, Bank.ext_trans e1 (Bank.ext_trans e2 e3), by omega, hf⟩

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

private lemma length_levelEqs_le (k b m s : Nat) :
    (levelEqs k b m s).length ≤ m * k * 2 ^ b := by
  unfold levelEqs
  have h1 : ∀ (j : Fin m), ((List.finRange k).flatMap fun p =>
      ((List.finRange (2 ^ b)).filter fun α => decide (popcount b α.val = s)).map fun α =>
        (j, p, α)).length ≤ k * 2 ^ b := by
    intro j
    have hle : ∀ (l : List (Fin k)), (l.flatMap fun p =>
        ((List.finRange (2 ^ b)).filter fun α => decide (popcount b α.val = s)).map fun α =>
          (j, p, α)).length ≤ l.length * 2 ^ b := by
      intro l; induction l with
      | nil => simp
      | cons p l ih =>
        simp only [List.flatMap_cons, List.length_append, List.length_map, List.length_cons]
        have hf : ((List.finRange (2 ^ b)).filter fun α => decide (popcount b α.val = s)).length ≤ 2 ^ b :=
          (List.length_filter_le _ _).trans (by simp)
        nlinarith
    simpa using hle (List.finRange k)
  have h2 : ∀ (l : List (Fin m)), (l.flatMap fun j =>
      (List.finRange k).flatMap fun p =>
        ((List.finRange (2 ^ b)).filter fun α => decide (popcount b α.val = s)).map fun α =>
          (j, p, α)).length ≤ l.length * (k * 2 ^ b) := by
    intro l; induction l with
    | nil => simp
    | cons j l ih =>
      simp only [List.flatMap_cons, List.length_append, List.length_cons]
      have := h1 j; nlinarith
  have h3 := h2 (List.finRange m)
  simp only [List.length_finRange] at h3
  nlinarith

private lemma testBit_extract_ofVec {k b p : Nat} (hk : 0 < k) (v : Vec k) (s : Fin b) :
    (extract k b p (ofVec k v).val).val.testBit s.val = v ⟨(p + s.val) % k, Nat.mod_lt _ hk⟩ := by
  rw [testBit_extract]
  simp only [s.isLt, decide_true, Bool.true_and, testBit_ofVec, Nat.mod_lt _ hk, ↓reduceDIte]

private def eqStepCost (k : Nat) : Nat :=
  k * (10 * k + 6) + k * (1 + k * 5) + rkCost k k

private def levelCost (k b m : Nat) : Nat :=
  2 * (k * (k * ((2 * b + 1) * (2 ^ b * 4)))) + (m * k * 2 ^ b) * eqStepCost k + k * (k * (1 + k * 5))

private lemma grow_subVLevel {n k r m : Nat} (hk : 0 < k) (B : Bank n)
    (h0 : B.Has (fun _ => false)) (h1 : B.Has (fun _ => true))
    (u v_in : (Fin n → Bool) → Fin (2 ^ k))
    (cr cc : (Fin n → Bool) → Fin r → Fin (2 ^ k))
    (A B_mask : (Fin n → Bool) → Fin m → Fin (2 ^ k))
    (hA : ∀ (j : Fin m) (i : Fin k), B.Has (fun x => (A x j).val.testBit i.val))
    (hB : ∀ (j : Fin m) (i : Fin k), B.Has (fun x => (B_mask x j).val.testBit i.val))
    (hψ0 : ∀ i α, B.Has (fun x => localPsi k r false (u x) (cr x) i α))
    (hψ1 : ∀ i α, B.Has (fun x => localPsi k r true (v_in x) (cc x) i α))
    (s : Nat) (V : (Fin n → Bool) → Fin k → Vec k)
    (hV : ∀ idx c, B.Has (fun x => V x idx c)) :
    B.Grow (levelCost k (winSize k r) m)
      (fun D => ∀ idx c, D.Has (fun x => subVLevel k r m hk (u x) (v_in x) (cr x) (cc x) (A x) (B_mask x) s (V x) idx c)) := by
  let b := winSize k r
  -- 1. Precompute derivTables for col = false
  obtain ⟨D1, e1, c1, hdt0⟩ := collectPropFin B
    (fun (idx : Fin k) D => ∀ (i : Fin k) (α : Fin (2 ^ b)),
      D.Has (fun x => derivTable (localPsi k r false (u x) (cr x) i)
        (extract k b (winStart k r false i.val) (ofVec k (V x idx)).val) α))
    (fun _ _ _ e h i α => e (h i α))
    (k * ((2 * b + 1) * (2 ^ b * 4))) (fun D e idx =>
      collectPropFin D
        (fun (i : Fin k) E => ∀ α : Fin (2 ^ b),
          E.Has (fun x => derivTable (localPsi k r false (u x) (cr x) i)
            (extract k b (winStart k r false i.val) (ofVec k (V x idx)).val) α))
        (fun _ _ _ ee h α => ee (h α))
        ((2 * b + 1) * (2 ^ b * 4)) (fun E ee i =>
          grow_derivTable E (fun x => localPsi k r false (u x) (cr x) i)
            (fun x => extract k b (winStart k r false i.val) (ofVec k (V x idx)).val)
            (fun α => ee (e (hψ0 i α)))
            (fun t => has_congr (ee (e (hV idx ⟨(winStart k r false i.val + t.val) % k, Nat.mod_lt _ hk⟩)))
              (fun x => (testBit_extract_ofVec hk (V x idx) t).symm))))
  -- 2. Precompute derivTables for col = true
  obtain ⟨D2, e2, c2, hdt1⟩ := collectPropFin D1
    (fun (idx : Fin k) D => ∀ (i : Fin k) (α : Fin (2 ^ b)),
      D.Has (fun x => derivTable (localPsi k r true (v_in x) (cc x) i)
        (extract k b (winStart k r true i.val) (ofVec k (V x idx)).val) α))
    (fun _ _ _ e h i α => e (h i α))
    (k * ((2 * b + 1) * (2 ^ b * 4))) (fun D e idx =>
      collectPropFin D
        (fun (i : Fin k) E => ∀ α : Fin (2 ^ b),
          E.Has (fun x => derivTable (localPsi k r true (v_in x) (cc x) i)
            (extract k b (winStart k r true i.val) (ofVec k (V x idx)).val) α))
        (fun _ _ _ ee h α => ee (h α))
        ((2 * b + 1) * (2 ^ b * 4)) (fun E ee i =>
          grow_derivTable E (fun x => localPsi k r true (v_in x) (cc x) i)
            (fun x => extract k b (winStart k r true i.val) (ofVec k (V x idx)).val)
            (fun α => ee (e (e1 (hψ1 i α))))
            (fun t => has_congr (ee (e (e1 (hV idx ⟨(winStart k r true i.val + t.val) % k, Nat.mod_lt _ hk⟩))))
              (fun x => (testBit_extract_ofVec hk (V x idx) t).symm))))
  -- 3. Fold over levelEqs
  have e12 : B.Ext D2 := Bank.ext_trans e1 e2
  let stepU : ((Fin n → Bool) → Fin k → Vec k) → (Fin m × Fin k × Fin (2 ^ b)) →
      (Fin n → Bool) → Fin k → Vec k :=
    fun U eq x => subVLevelEq k r m hk (u x) (v_in x) (cr x) (cc x) (A x) (B_mask x) (V x) (U x) eq
  have hU0 : ∀ row c, D2.Has (fun _ : Fin n → Bool => stdBasis k row c) :=
    fun row c => has_constBool (e12 h0) (e12 h1) _
  obtain ⟨D3, e3, c3, hU⟩ := Bank.foldGrow D2 (levelEqs k b m s) (fun _ => stdBasis k) stepU
    (fun U D => ∀ row c, D.Has (fun x => U x row c)) (eqStepCost k) hU0 (by
      intro D e U eq _ hUcur
      rcases eq with ⟨j, p, α⟩
      let T : Fin (2 ^ k) := ⟨embed k b p.val α.val, embed_lt hk⟩
      -- Build col : Fin k → BitFn n
      obtain ⟨E1, ee1, cc1, hcol⟩ := D.collectFin k
        (fun idx x => derivFmtEval k r m (u x) (v_in x) (cr x) (cc x) (A x) (B_mask x) (V x idx) j T)
        (10 * k + 6) (fun E eE idx => by
          obtain ⟨F1, ef1, cf1, hm0⟩ := E.collectFin k (fun i x =>
            (A x j).val.testBit i.val &&
              if submask T.val (winMask k b (winStart k r false i.val)) then
                derivTable (localPsi k r false (u x) (cr x) i)
                  (extract k b (winStart k r false i.val) (ofVec k (V x idx)).val)
                  (extract k b (winStart k r false i.val) T.val)
              else false) 1 (fun F eF i => by
                have htb : F.Has (fun x =>
                    if submask T.val (winMask k b (winStart k r false i.val)) then
                      derivTable (localPsi k r false (u x) (cr x) i)
                        (extract k b (winStart k r false i.val) (ofVec k (V x idx)).val)
                        (extract k b (winStart k r false i.val) T.val)
                    else false) := by
                  by_cases hsm : submask T.val (winMask k b (winStart k r false i.val)) = true
                  · exact has_congr (eF (eE (e (e2 (hdt0 idx i (extract k b (winStart k r false i.val) T.val))))))
                      (fun x => by simp [hsm])
                  · exact has_congr (eF (eE (e (e12 h0)))) (fun x => by simp [hsm])
                exact Bank.meet (eF (eE (e (e12 (hA j i))))) htb)
          obtain ⟨F2, ef2, cf2, ht0⟩ := F1.xorList (List.finRange k) _ (fun i _ => hm0 i)
          obtain ⟨F3, ef3, cf3, hm1⟩ := F2.collectFin k (fun i x =>
            (B_mask x j).val.testBit i.val &&
              if submask T.val (winMask k b (winStart k r true i.val)) then
                derivTable (localPsi k r true (v_in x) (cc x) i)
                  (extract k b (winStart k r true i.val) (ofVec k (V x idx)).val)
                  (extract k b (winStart k r true i.val) T.val)
              else false) 1 (fun F eF i => by
                have htb : F.Has (fun x =>
                    if submask T.val (winMask k b (winStart k r true i.val)) then
                      derivTable (localPsi k r true (v_in x) (cc x) i)
                        (extract k b (winStart k r true i.val) (ofVec k (V x idx)).val)
                        (extract k b (winStart k r true i.val) T.val)
                    else false) := by
                  by_cases hsm : submask T.val (winMask k b (winStart k r true i.val)) = true
                  · exact has_congr (eF (ef2 (ef1 (eE (e (hdt1 idx i (extract k b (winStart k r true i.val) T.val)))))))
                      (fun x => by simp [hsm])
                  · exact has_congr (eF (ef2 (ef1 (eE (e (e12 h0)))))) (fun x => by simp [hsm])
                exact Bank.meet (eF (ef2 (ef1 (eE (e (e12 (hB j i))))))) htb)
          obtain ⟨F4, ef4, cf4, ht1⟩ := F3.xorList (List.finRange k) _ (fun i _ => hm1 i)
          obtain ⟨F5, ef5, cf5, hres⟩ := Bank.xor2 (ef4 (ef3 ht0)) ht1
          simp only [List.length_finRange] at cf2 cf4
          exact ⟨F5, Bank.ext_trans ef1 (Bank.ext_trans ef2 (Bank.ext_trans ef3 (Bank.ext_trans ef4 ef5))),
            by omega, hres⟩)
      -- Build c : Fin k → BitFn n
      obtain ⟨E2, ee2, cc2, hc⟩ := E1.collectFin k
        (fun row x => vecDot (U x row) (fun idx =>
          derivFmtEval k r m (u x) (v_in x) (cr x) (cc x) (A x) (B_mask x) (V x idx) j T))
        (1 + k * 5) (fun E eE row =>
          grow_vecDot E (fun x => U x row)
            (fun x idx => derivFmtEval k r m (u x) (v_in x) (cr x) (cc x) (A x) (B_mask x) (V x idx) j T)
            (fun idx => eE (ee1 (hUcur row idx))) (fun idx => eE (hcol idx)))
      -- Apply restrictKernelStep
      obtain ⟨E3, ee3, cc3, ⟨_, hrk⟩⟩ := grow_restrictKernelStep E2
        (ee2 (ee1 (e (e12 h0)))) (ee2 (ee1 (e (e12 h1)))) U
        (fun x row => vecDot (U x row) (fun idx =>
          derivFmtEval k r m (u x) (v_in x) (cr x) (cc x) (A x) (B_mask x) (V x idx) j T))
        (fun row idx => ee2 (ee1 (hUcur row idx))) hc
      exact ⟨E3, Bank.ext_trans ee1 (Bank.ext_trans ee2 ee3), by unfold eqStepCost; omega, hrk⟩)
  -- 4. Matrix multiply V * U
  let Ufin : (Fin n → Bool) → Fin k → Vec k := fun x =>
    (levelEqs k b m s).foldl
      (subVLevelEq k r m hk (u x) (v_in x) (cr x) (cc x) (A x) (B_mask x) (V x)) (stdBasis k)
  have hUfin : ∀ row c, D3.Has (fun x => Ufin x row c) := fun row c =>
    has_congr (hU row c) (fun x => by
      have hfl := foldl_apply'
        (fun acc eq y => subVLevelEq k r m hk (u y) (v_in y) (cr y) (cc y) (A y) (B_mask y) (V y) acc eq)
        (fun _ => stdBasis k) (levelEqs k b m s) x
      exact congrFun (congrFun hfl row) c)
  obtain ⟨D4, e4, c4, hres⟩ := collectPropFin D3
    (fun (row : Fin k) D => ∀ c : Fin k, D.Has (fun x => vecLinComb (V x) (Ufin x row) c))
    (fun _ _ _ e h c => e (h c)) (k * (1 + k * 5)) (fun D e row =>
      grow_vecLinComb D V (fun x => Ufin x row)
        (fun idx c => e (e3 (e12 (hV idx c)))) (fun idx => e (hUfin row idx)))
  have hlen := length_levelEqs_le k b m s
  have hmul_le : (levelEqs k b m s).length * eqStepCost k ≤ (m * k * 2 ^ b) * eqStepCost k :=
    Nat.mul_le_mul_right _ hlen
  exact ⟨D4, Bank.ext_trans e12 (Bank.ext_trans e3 e4), by
    change D4.gates.length ≤ B.gates.length + levelCost k b m
    unfold levelCost; omega, hres⟩

private lemma grow_subVChain {n k r m : Nat} (hk : 0 < k) (B : Bank n)
    (h0 : B.Has (fun _ => false)) (h1 : B.Has (fun _ => true))
    (u v_in : (Fin n → Bool) → Fin (2 ^ k))
    (cr cc : (Fin n → Bool) → Fin r → Fin (2 ^ k))
    (A B_mask : (Fin n → Bool) → Fin m → Fin (2 ^ k))
    (hA : ∀ (j : Fin m) (i : Fin k), B.Has (fun x => (A x j).val.testBit i.val))
    (hB : ∀ (j : Fin m) (i : Fin k), B.Has (fun x => (B_mask x j).val.testBit i.val))
    (hψ0 : ∀ i α, B.Has (fun x => localPsi k r false (u x) (cr x) i α))
    (hψ1 : ∀ i α, B.Has (fun x => localPsi k r true (v_in x) (cc x) i α)) :
    B.Grow ((winSize k r - 1) * levelCost k (winSize k r) m)
      (fun D => ∀ idx c, D.Has (fun x => subVChain k r m hk (u x) (v_in x) (cr x) (cc x) (A x) (B_mask x) idx c)) := by
  let levels := (List.range (winSize k r - 1)).reverse.map (· + 1)
  let stepL : ((Fin n → Bool) → Fin k → Vec k) → Nat → (Fin n → Bool) → Fin k → Vec k :=
    fun V s x => subVLevel k r m hk (u x) (v_in x) (cr x) (cc x) (A x) (B_mask x) s (V x)
  have hV0 : ∀ idx c, B.Has (fun _ : Fin n → Bool => stdBasis k idx c) :=
    fun idx c => has_constBool h0 h1 _
  have hfold := Bank.foldGrow B levels (fun _ => stdBasis k) stepL
    (fun V D => ∀ idx c, D.Has (fun x => V x idx c)) (levelCost k (winSize k r) m) hV0 (by
      intro D e V s _ hV
      exact grow_subVLevel hk D (e h0) (e h1) u v_in cr cc A B_mask
        (fun j i => e (hA j i)) (fun j i => e (hB j i))
        (fun i α => e (hψ0 i α)) (fun i α => e (hψ1 i α)) s V hV)
  refine hfold.weaken (by simp [levels]) (fun D hD idx c => ?_)
  exact has_congr (hD idx c) (fun x => by
    have hfl := foldl_apply'
      (fun acc s y => subVLevel k r m hk (u y) (v_in y) (cr y) (cc y) (A y) (B_mask y) s acc)
      (fun _ => stdBasis k) levels x
    exact congrFun (congrFun hfl idx) c)

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

private lemma buildEvalSpec_cost_le {k r m q : Nat} (hqk : q ≤ k) :
    let b := winSize k r
    let seedCost := k * (1 + (k - q) * 2) + (2 * (k * 4 + r * (k * 22)) + m * (10 * k + 6)) +
      m * 4 + m * (1 + m * 8) + (1 + m) + 1
    1 + 1 +
    k * (2 ^ b * (k * 4 + r * (k * 22))) +
    k * (2 ^ b * (k * 4 + r * (k * 22))) +
    (b - 1) * levelCost k b m +
    echCost k k +
    k * ((k + 1) * 4) +
    (1 + 2 * (k + 1 - q)) +
    q * (k * 1) +
    q * (k * (1 + k * 5)) +
    (2 * (k * 4 + r * (k * 22)) + m * (10 * k + 6)) +
    q * (2 * (k * 4 + r * (k * 22)) + m * (10 * k + 6) + m * 4) +
    echCost q m +
    m * ((m + 1) * 4) +
    k * (1 + q + 1) +
    k * 1 +
    k * ((k + 1) * 4) +
    (k - q) * (k * 1) +
    2 ^ (k - q) * seedCost +
    2 ^ (k - q) * ((k + 1) * 5) +
    (k + 1) * (2 * q + 3) +
    (k + 1) * 9 +
    1 ≤ 2 ^ 44 * (k + r + m + 3) ^ 12 * (2 ^ b + 2 ^ (k - q)) := by
  intro b seedCost
  let S := k + r + m + 3
  let E := 2 ^ b + 2 ^ (k - q)
  have hS_pos : 3 ≤ S := by dsimp [S]; omega
  have hb_le : b ≤ S := (winSize_le k r).trans (by dsimp [S]; omega)
  have hk_le : k ≤ S := by dsimp [S]; omega
  have hr_le : r ≤ S := by dsimp [S]; omega
  have hm_le : m ≤ S := by dsimp [S]; omega
  have hq_le : q ≤ S := by dsimp [S]; omega
  have hkq_le : k - q ≤ S := by omega
  have h2b_le : 2 ^ b ≤ E := Nat.le_add_right _ _
  have h2kq_le : 2 ^ (k - q) ≤ E := Nat.le_add_left _ _
  have h1_le_E : 1 ≤ E := (Nat.two_pow_pos b).trans_le h2b_le
  have h1_le_S : 1 ≤ S := by omega
  have hpow_le : ∀ a c : Nat, a ≤ c → S ^ a ≤ S ^ c := fun a c hac =>
    Nat.pow_le_pow_right (by omega) hac
  have hS1 : S ≤ S ^ 6 := by simpa using hpow_le 1 6 (by omega)
  have hS2 : S ^ 2 ≤ S ^ 6 := hpow_le 2 6 (by omega)
  have hS3 : S ^ 3 ≤ S ^ 6 := hpow_le 3 6 (by omega)
  have hS5 : S ^ 5 ≤ S ^ 6 := hpow_le 5 6 (by omega)
  have hS6_pos : 1 ≤ S ^ 6 := Nat.one_le_pow 6 S (by omega)
  have hE1 : 1 ≤ S ^ 6 * E := Nat.mul_pos hS6_pos (by omega)
  have hB_rk : ∀ d1 d2 : Nat, d1 ≤ S → d2 ≤ S → rkCost d1 d2 ≤ 24 * S ^ 2 := by
    intro d1 d2 hd1 hd2; unfold rkCost; nlinarith only [hd1, hd2, hS_pos]
  have hB_ech : ∀ d1 d2 : Nat, d1 ≤ S → d2 ≤ S → echCost d1 d2 ≤ 28 * S ^ 3 := by
    intro d1 d2 hd1 hd2; unfold echCost
    have hrk := hB_rk d1 d2 hd1 hd2
    have h1 : 1 + d1 + rkCost d1 d2 ≤ 28 * S ^ 2 := by nlinarith only [hd1, hrk, hS_pos]
    calc d2 * (1 + d1 + rkCost d1 d2)
        ≤ S * (28 * S ^ 2) := Nat.mul_le_mul hd2 h1
      _ = 28 * S ^ 3 := by ring
  have hB_c1 : k * (2 ^ b * (k * 4 + r * (k * 22))) ≤ 26 * (S ^ 3 * E) := by
    have h1 : k * 4 + r * (k * 22) ≤ 26 * S ^ 2 := by nlinarith only [hk_le, hr_le, hS_pos]
    calc k * (2 ^ b * (k * 4 + r * (k * 22)))
        ≤ S * (E * (26 * S ^ 2)) := Nat.mul_le_mul hk_le (Nat.mul_le_mul h2b_le h1)
      _ = 26 * (S ^ 3 * E) := by ring
  have hB_c2 : (b - 1) * levelCost k b m ≤ 200 * (S ^ 5 * E) := by
    unfold levelCost eqStepCost
    have hrk := hB_rk k k hk_le hk_le
    have heq : k * (10 * k + 6) + k * (1 + k * 5) + rkCost k k ≤ 50 * S ^ 2 := by
      nlinarith only [hk_le, hrk, hS_pos]
    have ht1 : 2 * (k * (k * ((2 * b + 1) * (2 ^ b * 4)))) ≤ 24 * (S ^ 3 * E) := by
      have h1 : 2 * b + 1 ≤ 3 * S := by omega
      have h2 : k * (k * ((2 * b + 1) * (2 ^ b * 4))) ≤ S * (S * ((3 * S) * (E * 4))) :=
        Nat.mul_le_mul hk_le (Nat.mul_le_mul hk_le (Nat.mul_le_mul h1 (Nat.mul_le_mul h2b_le (le_refl 4))))
      calc 2 * (k * (k * ((2 * b + 1) * (2 ^ b * 4))))
          ≤ 2 * (S * (S * ((3 * S) * (E * 4)))) := Nat.mul_le_mul_left 2 h2
        _ = 24 * (S ^ 3 * E) := by ring
    have ht2 : (m * k * 2 ^ b) * (k * (10 * k + 6) + k * (1 + k * 5) + rkCost k k) ≤ 50 * (S ^ 4 * E) := by
      have h1 : m * k * 2 ^ b ≤ S * S * E :=
        Nat.mul_le_mul (Nat.mul_le_mul hm_le hk_le) h2b_le
      calc (m * k * 2 ^ b) * (k * (10 * k + 6) + k * (1 + k * 5) + rkCost k k)
          ≤ (S * S * E) * (50 * S ^ 2) := Nat.mul_le_mul h1 heq
        _ = 50 * (S ^ 4 * E) := by ring
    have ht3 : k * (k * (1 + k * 5)) ≤ 6 * (S ^ 3 * E) := by
      have h0' : k * (1 + k * 5) ≤ 6 * S ^ 2 := by nlinarith only [hk_le, hS_pos]
      have h1 : k * (k * (1 + k * 5)) ≤ 6 * S ^ 3 :=
        calc k * (k * (1 + k * 5)) ≤ S * (6 * S ^ 2) := Nat.mul_le_mul hk_le h0'
          _ = 6 * S ^ 3 := by ring
      calc k * (k * (1 + k * 5)) ≤ 6 * S ^ 3 * E := h1.trans (Nat.le_mul_of_pos_right _ (by omega))
        _ = 6 * (S ^ 3 * E) := by ring
    have h34 : S ^ 3 * E ≤ S ^ 4 * E := Nat.mul_le_mul_right E (hpow_le 3 4 (by omega))
    have hlv : 2 * (k * (k * ((2 * b + 1) * (2 ^ b * 4)))) +
        (m * k * 2 ^ b) * (k * (10 * k + 6) + k * (1 + k * 5) + rkCost k k) +
        k * (k * (1 + k * 5)) ≤ 200 * (S ^ 4 * E) := by
      have ht1' : 2 * (k * (k * ((2 * b + 1) * (2 ^ b * 4)))) ≤ 24 * (S ^ 4 * E) :=
        ht1.trans (Nat.mul_le_mul_left 24 h34)
      have ht3' : k * (k * (1 + k * 5)) ≤ 6 * (S ^ 4 * E) :=
        ht3.trans (Nat.mul_le_mul_left 6 h34)
      omega
    calc (b - 1) * (2 * (k * (k * ((2 * b + 1) * (2 ^ b * 4)))) +
          (m * k * 2 ^ b) * (k * (10 * k + 6) + k * (1 + k * 5) + rkCost k k) +
          k * (k * (1 + k * 5)))
        ≤ S * (200 * (S ^ 4 * E)) := Nat.mul_le_mul (by omega) hlv
      _ = 200 * (S ^ 5 * E) := by ring
  have hB_c3a : echCost k k ≤ 28 * S ^ 3 := hB_ech k k hk_le hk_le
  have hB_c3b : k * ((k + 1) * 4) ≤ 8 * S ^ 2 := by nlinarith only [hk_le, hS_pos]
  have hB_c3c : 1 + 2 * (k + 1 - q) ≤ 3 * S := by omega
  have hB_c4a : q * (k * 1) ≤ S ^ 2 := by nlinarith only [hq_le, hk_le]
  have hB_c4b : q * (k * (1 + k * 5)) ≤ 6 * S ^ 3 := by
    have h1 : k * (1 + k * 5) ≤ 6 * S ^ 2 := by nlinarith only [hk_le, hS_pos]
    calc q * (k * (1 + k * 5)) ≤ S * (6 * S ^ 2) := Nat.mul_le_mul hq_le h1
      _ = 6 * S ^ 3 := by ring
  have hB_c4c : 2 * (k * 4 + r * (k * 22)) + m * (10 * k + 6) ≤ 68 * S ^ 2 := by
    nlinarith only [hk_le, hr_le, hm_le, hS_pos]
  have hB_c4d : q * (2 * (k * 4 + r * (k * 22)) + m * (10 * k + 6) + m * 4) ≤ 72 * S ^ 3 := by
    have h1 : 2 * (k * 4 + r * (k * 22)) + m * (10 * k + 6) + m * 4 ≤ 72 * S ^ 2 := by
      nlinarith only [hk_le, hr_le, hm_le, hS_pos]
    calc q * (2 * (k * 4 + r * (k * 22)) + m * (10 * k + 6) + m * 4)
        ≤ S * (72 * S ^ 2) := Nat.mul_le_mul hq_le h1
      _ = 72 * S ^ 3 := by ring
  have hB_c4e : echCost q m ≤ 28 * S ^ 3 := hB_ech q m hq_le hm_le
  have hB_c4f : m * ((m + 1) * 4) ≤ 8 * S ^ 2 := by nlinarith only [hm_le, hS_pos]
  have hB_c5a : k * (1 + q + 1) ≤ 3 * S ^ 2 := by nlinarith only [hk_le, hq_le, hS_pos]
  have hB_c5b : k * 1 ≤ S := by omega
  have hB_c5c : k * ((k + 1) * 4) ≤ 8 * S ^ 2 := by nlinarith only [hk_le, hS_pos]
  have hB_c5d : (k - q) * (k * 1) ≤ S ^ 2 := by nlinarith only [hkq_le, hk_le]
  have hB_c6 : 2 ^ (k - q) * seedCost ≤ 100 * (S ^ 2 * E) := by
    have hs : seedCost ≤ 100 * S ^ 2 := by
      dsimp [seedCost]; nlinarith only [hk_le, hr_le, hm_le, hkq_le, hS_pos]
    calc 2 ^ (k - q) * seedCost ≤ E * (100 * S ^ 2) := Nat.mul_le_mul h2kq_le hs
      _ = 100 * (S ^ 2 * E) := by ring
  have hB_c7a : 2 ^ (k - q) * ((k + 1) * 5) ≤ 10 * (S * E) := by
    have h1 : (k + 1) * 5 ≤ 10 * S := by omega
    calc 2 ^ (k - q) * ((k + 1) * 5) ≤ E * (10 * S) := Nat.mul_le_mul h2kq_le h1
      _ = 10 * (S * E) := by ring
  have hB_c7b : (k + 1) * (2 * q + 3) ≤ 6 * S ^ 2 := by nlinarith only [hk_le, hq_le, hS_pos]
  have hB_c7c : (k + 1) * 9 ≤ 18 * S := by omega
  have hB1 : 1 ≤ S ^ 6 * E := hE1
  have hB2 : S ≤ S ^ 6 * E := hS1.trans (Nat.le_mul_of_pos_right _ (by omega))
  have hB3 : S ^ 2 ≤ S ^ 6 * E := hS2.trans (Nat.le_mul_of_pos_right _ (by omega))
  have hB4 : S ^ 3 ≤ S ^ 6 * E := hS3.trans (Nat.le_mul_of_pos_right _ (by omega))
  have hB5 : S ^ 5 * E ≤ S ^ 6 * E := Nat.mul_le_mul_right E hS5
  have hB6 : S ^ 3 * E ≤ S ^ 6 * E := Nat.mul_le_mul_right E hS3
  have hB7 : S ^ 2 * E ≤ S ^ 6 * E := Nat.mul_le_mul_right E hS2
  have hB8 : S * E ≤ S ^ 6 * E := Nat.mul_le_mul_right E hS1
  have hpow12 : 1024 * (S ^ 6 * E) ≤ 2 ^ 44 * (S ^ 12 * E) :=
    Nat.mul_le_mul (by norm_num) (Nat.mul_le_mul_right E (hpow_le 6 12 (by omega)))
  change _ ≤ 2 ^ 44 * S ^ 12 * E
  rw [show 2 ^ 44 * S ^ 12 * E = 2 ^ 44 * (S ^ 12 * E) by ring]
  linarith only [hB_c1, hB_c2, hB_c3a, hB_c3b, hB_c3c, hB_c4a, hB_c4b, hB_c4c, hB_c4d, hB_c4e,
    hB_c4f, hB_c5a, hB_c5b, hB_c5c, hB_c5d, hB_c6, hB_c7a, hB_c7b, hB_c7c,
    hB1, hB2, hB3, hB4, hB5, hB6, hB7, hB8, hpow12]

lemma buildEvalSpec {k r m q : Nat} (hk : 0 < k) (hqk : q ≤ k) :
    (Bank.empty (inLen k r m)).Grow
      (2 ^ 44 * (k + r + m + 3) ^ 12 * (2 ^ winSize k r + 2 ^ (k - q)))
      (fun B => B.Has (fun x => evalSpec k r m q hk
        (decU x) (decV x) (decCr x) (decCc x) (decA x) (decB x) (decY x) (decT x))) := by
  let N := inLen k r m
  let B0 := Bank.empty N
  let b := winSize k r
  -- Input wires in B0
  have hu : ∀ i : Fin k, B0.Has (fun x => (decU x).val.testBit i.val) := fun i =>
    has_congr (Bank.input ⟨i.val, by dsimp [N]; unfold inLen; omega⟩) (fun x => by simp [decU, testBit_ofVec, i.isLt])
  have hv : ∀ i : Fin k, B0.Has (fun x => (decV x).val.testBit i.val) := fun i =>
    has_congr (Bank.input ⟨k + i.val, by dsimp [N]; unfold inLen; omega⟩) (fun x => by simp [decV, testBit_ofVec, i.isLt])
  have hcr : ∀ (j : Fin r) (i : Fin k), B0.Has (fun x => (decCr x j).val.testBit i.val) := fun j i =>
    has_congr (Bank.input ⟨2 * k + j.val * k + i.val, by
      dsimp [N]; unfold inLen; have := Nat.mul_le_mul_right k (Nat.succ_le_of_lt j.isLt); nlinarith [i.isLt]⟩)
      (fun x => by simp [decCr, testBit_ofVec, i.isLt])
  have hcc : ∀ (j : Fin r) (i : Fin k), B0.Has (fun x => (decCc x j).val.testBit i.val) := fun j i =>
    has_congr (Bank.input ⟨2 * k + r * k + j.val * k + i.val, by
      dsimp [N]; unfold inLen; have := Nat.mul_le_mul_right k (Nat.succ_le_of_lt j.isLt); nlinarith [i.isLt]⟩)
      (fun x => by simp [decCc, testBit_ofVec, i.isLt])
  have hA : ∀ (j : Fin m) (i : Fin k), B0.Has (fun x => (decA x j).val.testBit i.val) := fun j i =>
    has_congr (Bank.input ⟨2 * k + 2 * r * k + j.val * k + i.val, by
      dsimp [N]; unfold inLen; have := Nat.mul_le_mul_right k (Nat.succ_le_of_lt j.isLt); nlinarith [i.isLt]⟩)
      (fun x => by simp [decA, testBit_ofVec, i.isLt])
  have hB : ∀ (j : Fin m) (i : Fin k), B0.Has (fun x => (decB x j).val.testBit i.val) := fun j i =>
    has_congr (Bank.input ⟨2 * k + 2 * r * k + m * k + j.val * k + i.val, by
      dsimp [N]; unfold inLen; have := Nat.mul_le_mul_right k (Nat.succ_le_of_lt j.isLt); nlinarith [i.isLt]⟩)
      (fun x => by simp [decB, testBit_ofVec, i.isLt])
  have hY : ∀ j : Fin m, B0.Has (fun x => decY x j) := fun j =>
    Bank.input ⟨2 * k + 2 * r * k + 2 * m * k + j.val, by dsimp [N]; unfold inLen; omega⟩
  have hT : ∀ i : Fin (k + 1), B0.Has (fun x => toVec (k + 1) (decT x) i) := fun i =>
    has_congr (Bank.input ⟨2 * k + 2 * r * k + 2 * m * k + m + i.val, by dsimp [N]; unfold inLen; omega⟩)
      (fun x => by simp [toVec, decT, testBit_ofVec, i.isLt])
  -- Stage 0: constants false and true
  obtain ⟨D0a, e0a, c0a, h0a⟩ := B0.const false
  obtain ⟨D0, e0b, c0b, h1⟩ := D0a.const true
  have e0 : B0.Ext D0 := Bank.ext_trans e0a e0b
  have h0 : D0.Has (fun _ => false) := e0b h0a
  -- Stage 1: localPsi tables for col = false and col = true
  obtain ⟨D1a, e1a, c1a, hψ0⟩ := collectPropFin D0
    (fun (i : Fin k) D => ∀ α : Fin (2 ^ b), D.Has (fun x => localPsi k r false (decU x) (decCr x) i α))
    (fun _ _ _ e h α => e (h α))
    (2 ^ b * (k * 4 + r * (k * 22))) (fun D e i =>
      D.collectFin (2 ^ b) (fun α x => localPsi k r false (decU x) (decCr x) i α)
        (k * 4 + r * (k * 22)) (fun E ee α => by
          let w0 : Fin (2 ^ k) := ⟨embed k b (winStart k r false i.val) α.val, embed_lt hk⟩
          obtain ⟨F, ef, cf, hst⟩ := grow_stateBits hk false E (fun _ => w0) decU decCr
            (fun t => has_constBool (ee (e h0)) (ee (e h1)) _)
            (fun t => ee (e (e0 (hu t)))) (fun j t => ee (e (e0 (hcr j t))))
          exact ⟨F, ef, cf, hst i⟩))
  obtain ⟨D1, e1b, c1b, hψ1⟩ := collectPropFin D1a
    (fun (i : Fin k) D => ∀ α : Fin (2 ^ b), D.Has (fun x => localPsi k r true (decV x) (decCc x) i α))
    (fun _ _ _ e h α => e (h α))
    (2 ^ b * (k * 4 + r * (k * 22))) (fun D e i =>
      D.collectFin (2 ^ b) (fun α x => localPsi k r true (decV x) (decCc x) i α)
        (k * 4 + r * (k * 22)) (fun E ee α => by
          let w0 : Fin (2 ^ k) := ⟨embed k b (winStart k r true i.val) α.val, embed_lt hk⟩
          obtain ⟨F, ef, cf, hst⟩ := grow_stateBits hk true E (fun _ => w0) decV decCc
            (fun t => has_constBool (ee (e (e1a h0))) (ee (e (e1a h1))) _)
            (fun t => ee (e (e1a (e0 (hv t))))) (fun j t => ee (e (e1a (e0 (hcc j t)))))
          exact ⟨F, ef, cf, hst i⟩))
  have e01 : B0.Ext D1 := Bank.ext_trans e0 (Bank.ext_trans e1a e1b)
  have e1 : D0.Ext D1 := Bank.ext_trans e1a e1b
  -- Stage 2: subVChain
  obtain ⟨D2, e2, c2, hV⟩ := grow_subVChain hk D1 (e1 h0) (e1 h1) decU decV decCr decCc decA decB
    (fun j i => e01 (hA j i)) (fun j i => e01 (hB j i)) (fun i α => e1b (hψ0 i α)) hψ1
  have e02 : B0.Ext D2 := Bank.ext_trans e01 e2
  have e_0_2 : D0.Ext D2 := Bank.ext_trans e1 e2
  -- Stage 3: echelon V, cntEq echV.hasP, dimGe
  let Vfn : (Fin N → Bool) → Fin k → Vec k := fun x =>
    subVChain k r m hk (decU x) (decV x) (decCr x) (decCc x) (decA x) (decB x)
  obtain ⟨D3a, e3a, c3a, ⟨hechV_p, hechV_v⟩⟩ := grow_echelon D2 (e_0_2 h0) (e_0_2 h1) Vfn hV
  obtain ⟨D3b, e3b, c3b, hcntV⟩ := grow_cntEq_prefix D3a (e3a (e_0_2 h0)) (e3a (e_0_2 h1))
    (fun x => (echelon (Vfn x)).hasP) hechV_p k (le_refl k)
  obtain ⟨D3, e3c, c3c, hdim⟩ := D3b.orList (List.range (k + 1 - q))
    (fun d x => cntEq (echelon (Vfn x)).hasP k (q + d)) (fun d hd => by
      have hlt : q + d < k + 1 := by simp only [List.mem_range] at hd; omega
      exact hcntV k (le_refl k) ⟨q + d, hlt⟩)
  have e23 : D2.Ext D3 := Bank.ext_trans e3a (Bank.ext_trans e3b e3c)
  have e03 : B0.Ext D3 := Bank.ext_trans e02 e23
  have e_0_3 : D0.Ext D3 := Bank.ext_trans e_0_2 e23
  -- Stage 4: isPiv, selDir, f0, resp, echR, cntEq echR.hasP
  obtain ⟨D4a, e4a, c4a, hisPiv⟩ := collectPropFin D3
    (fun (idx : Fin q) D => ∀ c : Fin k, D.Has (fun x => isPiv (echelon (Vfn x)).hasP idx c))
    (fun _ _ _ e h c => e (h c)) (k * 1) (fun D e idx =>
      D.collectFin k (fun c x => isPiv (echelon (Vfn x)).hasP idx c) 1 (fun E ee c =>
        Bank.meet (ee (e (e3c (e3b (hechV_p c)))))
          (ee (e (e3c (hcntV c.val (Nat.le_of_lt c.isLt) ⟨idx.val, by omega⟩))))))
  obtain ⟨D4b, e4b, c4b, hselDir⟩ := collectPropFin D4a
    (fun (idx : Fin q) D => ∀ c : Fin k, D.Has (fun x => selDir (echelon (Vfn x)).hasP (echelon (Vfn x)).piv idx c))
    (fun _ _ _ e h c => e (h c)) (k * (1 + k * 5)) (fun D e idx =>
      grow_vecLinComb D (fun x => (echelon (Vfn x)).piv) (fun x => isPiv (echelon (Vfn x)).hasP idx)
        (fun j1 j2 => e (e4a (e3c (e3b (hechV_v j1 j2))))) (fun c => e (hisPiv idx c)))
  obtain ⟨D4c, e4c, c4c, hf0⟩ := grow_targetFBits hk D4b decU decV decCr decCc decA decB
    (fun _ => ⟨0, Nat.two_pow_pos k⟩)
    (fun i => e4b (e4a (e03 (hu i)))) (fun i => e4b (e4a (e03 (hv i))))
    (fun j i => e4b (e4a (e03 (hcr j i)))) (fun j i => e4b (e4a (e03 (hcc j i))))
    (fun j i => e4b (e4a (e03 (hA j i)))) (fun j i => e4b (e4a (e03 (hB j i))))
    (fun _ => has_congr (e4b (e4a (e_0_3 h0))) (fun _ => by simp))
  let respFn : (Fin N → Bool) → Fin q → Vec m := fun x idx =>
    vecXor (targetF k r m (decU x) (decV x) (decCr x) (decCc x) (decA x) (decB x)
      (ofVec k (selDir (echelon (Vfn x)).hasP (echelon (Vfn x)).piv idx)))
      (targetF k r m (decU x) (decV x) (decCr x) (decCc x) (decA x) (decB x) ⟨0, Nat.two_pow_pos k⟩)
  obtain ⟨D4d, e4d, c4d, hresp⟩ := collectPropFin D4c
    (fun (idx : Fin q) D => ∀ j : Fin m, D.Has (fun x => respFn x idx j))
    (fun _ _ _ e h j => e (h j))
    (2 * (k * 4 + r * (k * 22)) + m * (10 * k + 6) + m * 4) (fun D e idx => by
      obtain ⟨E1, ee1, cc1, hfd⟩ := grow_targetFBits hk D decU decV decCr decCc decA decB
        (fun x => ofVec k (selDir (echelon (Vfn x)).hasP (echelon (Vfn x)).piv idx))
        (fun i => e (e4c (e4b (e4a (e03 (hu i)))))) (fun i => e (e4c (e4b (e4a (e03 (hv i))))))
        (fun j i => e (e4c (e4b (e4a (e03 (hcr j i)))))) (fun j i => e (e4c (e4b (e4a (e03 (hcc j i))))))
        (fun j i => e (e4c (e4b (e4a (e03 (hA j i)))))) (fun j i => e (e4c (e4b (e4a (e03 (hB j i))))))
        (fun i => has_congr (e (e4c (hselDir idx i))) (fun x => by simp [testBit_ofVec, i.isLt]))
      obtain ⟨E2, ee2, cc2, hxr⟩ := grow_vecXor E1
        (fun x => targetF k r m (decU x) (decV x) (decCr x) (decCc x) (decA x) (decB x)
          (ofVec k (selDir (echelon (Vfn x)).hasP (echelon (Vfn x)).piv idx)))
        (fun x => targetF k r m (decU x) (decV x) (decCr x) (decCc x) (decA x) (decB x) ⟨0, Nat.two_pow_pos k⟩)
        hfd (fun j => ee1 (e (hf0 j)))
      exact ⟨E2, Bank.ext_trans ee1 ee2, by omega, hxr⟩)
  have e34d : D3.Ext D4d := Bank.ext_trans e4a (Bank.ext_trans e4b (Bank.ext_trans e4c e4d))
  obtain ⟨D4e, e4e, c4e, ⟨hechR_p, hechR_v⟩⟩ := grow_echelon D4d (e34d (e_0_3 h0)) (e34d (e_0_3 h1)) respFn hresp
  obtain ⟨D4, e4f, c4f, hcntR⟩ := grow_cntEq_prefix D4e (e4e (e34d (e_0_3 h0))) (e4e (e34d (e_0_3 h1)))
    (fun x => (echelon (respFn x)).hasP) hechR_p m (le_refl m)
  have e34 : D3.Ext D4 := Bank.ext_trans e34d (Bank.ext_trans e4e e4f)
  have e04 : B0.Ext D4 := Bank.ext_trans e03 e34
  have e_0_4 : D0.Ext D4 := Bank.ext_trans e_0_3 e34
  -- Stage 5: inSq, !inSq, cntEq (!inSq), isComp
  obtain ⟨D5a, e5a, c5a, hinSq⟩ := D4.collectFin k (fun c x => inSq (echelon (Vfn x)).hasP q c) (1 + q + 1)
    (fun D e c => by
      obtain ⟨E1, ee1, cc1, hor⟩ := D.orList (List.finRange q)
        (fun idx x => cntEq (echelon (Vfn x)).hasP c.val idx.val)
        (fun idx _ => e (e34 (e3c (hcntV c.val (Nat.le_of_lt c.isLt) ⟨idx.val, by omega⟩))))
      obtain ⟨E2, ee2, cc2, hm⟩ := Bank.meet (ee1 (e (e34 (e3c (e3b (hechV_p c)))))) hor
      simp only [List.length_finRange] at cc1
      exact ⟨E2, Bank.ext_trans ee1 ee2, by omega, hm⟩)
  obtain ⟨D5b, e5b, c5b, hninSq⟩ := D5a.collectFin k (fun c x => !(inSq (echelon (Vfn x)).hasP q c)) 1
    (fun D e c => Bank.inv (e (hinSq c)))
  obtain ⟨D5c, e5c, c5c, hcntComp⟩ := grow_cntEq_prefix D5b (e5b (e5a (e_0_4 h0))) (e5b (e5a (e_0_4 h1)))
    (fun x c => !(inSq (echelon (Vfn x)).hasP q c)) hninSq k (le_refl k)
  obtain ⟨D5, e5d, c5d, hisComp⟩ := collectPropFin D5c
    (fun (l : Fin (k - q)) D => ∀ c : Fin k, D.Has (fun x => isComp (echelon (Vfn x)).hasP q l c))
    (fun _ _ _ e h c => e (h c)) (k * 1) (fun D e l =>
      D.collectFin k (fun c x => isComp (echelon (Vfn x)).hasP q l c) 1 (fun E ee c =>
        Bank.meet (ee (e (e5c (hninSq c))))
          (ee (e (hcntComp c.val (Nat.le_of_lt c.isLt) ⟨l.val, by omega⟩)))))
  have e45 : D4.Ext D5 := Bank.ext_trans e5a (Bank.ext_trans e5b (Bank.ext_trans e5c e5d))
  have e05 : B0.Ext D5 := Bank.ext_trans e04 e45
  have e_0_5 : D0.Ext D5 := Bank.ext_trans e_0_4 e45
  -- Stage 6: 2^(k-q) complementary seeds & pass bits
  let passFn : Fin (2 ^ (k - q)) → (Fin N → Bool) → Bool := fun σ x =>
    !(anyBit (echelonReduce (echelon (respFn x)).hasP (echelon (respFn x)).piv
      (vecXor (targetF k r m (decU x) (decV x) (decCr x) (decCc x) (decA x) (decB x)
        (ofVec k (seedVec (echelon (Vfn x)).hasP q σ))) (decY x))))
  let seedCost := k * (1 + (k - q) * 2) + (2 * (k * 4 + r * (k * 22)) + m * (10 * k + 6)) +
    m * 4 + m * (1 + m * 8) + (1 + m) + 1
  obtain ⟨D6, e6, c6, hpass⟩ := D5.collectFin (2 ^ (k - q)) passFn seedCost (fun D e σ => by
    -- seedVec
    obtain ⟨E1, ee1, cc1, hseed⟩ := D.collectFin k (fun c x => seedVec (echelon (Vfn x)).hasP q σ c)
      (1 + (k - q) * 2) (fun E eE c => by
        obtain ⟨F1, ef1, cf1, hm⟩ := E.collectFin (k - q)
          (fun l x => σ.val.testBit l.val && isComp (echelon (Vfn x)).hasP q l c) 1 (fun F eF l =>
            Bank.meet (has_constBool (eF (eE (e (e_0_5 h0)))) (eF (eE (e (e_0_5 h1)))) _)
              (eF (eE (e (hisComp l c)))))
        obtain ⟨F2, ef2, cf2, hor⟩ := F1.orList (List.finRange (k - q)) _ (fun l _ => hm l)
        simp only [List.length_finRange] at cf2
        exact ⟨F2, Bank.ext_trans ef1 ef2, by omega, hor⟩)
    -- targetF on seed
    obtain ⟨E2, ee2, cc2, hfs⟩ := grow_targetFBits hk E1 decU decV decCr decCc decA decB
      (fun x => ofVec k (seedVec (echelon (Vfn x)).hasP q σ))
      (fun i => ee1 (e (e05 (hu i)))) (fun i => ee1 (e (e05 (hv i))))
      (fun j i => ee1 (e (e05 (hcr j i)))) (fun j i => ee1 (e (e05 (hcc j i))))
      (fun j i => ee1 (e (e05 (hA j i)))) (fun j i => ee1 (e (e05 (hB j i))))
      (fun i => has_congr (hseed i) (fun x => by simp [testBit_ofVec, i.isLt]))
    -- vecXor with y
    obtain ⟨E3, ee3, cc3, hdiff⟩ := grow_vecXor E2
      (fun x => targetF k r m (decU x) (decV x) (decCr x) (decCc x) (decA x) (decB x)
        (ofVec k (seedVec (echelon (Vfn x)).hasP q σ)))
      decY hfs (fun j => ee2 (ee1 (e (e05 (hY j)))))
    -- echelonReduce
    obtain ⟨E4, ee4, cc4, hred⟩ := grow_echelonReduce E3
      (fun x => (echelon (respFn x)).hasP) (fun x => (echelon (respFn x)).piv) _
      (fun j => ee3 (ee2 (ee1 (e (e45 (e4f (hechR_p j)))))))
      (fun j1 j2 => ee3 (ee2 (ee1 (e (e45 (e4f (hechR_v j1 j2))))))) hdiff
    -- anyBit and inv
    obtain ⟨E5, ee5, cc5, hany⟩ := grow_anyBit E4 _ hred
    obtain ⟨E6, ee6, cc6, hnot⟩ := Bank.inv hany
    exact ⟨E6, Bank.ext_trans ee1 (Bank.ext_trans ee2 (Bank.ext_trans ee3
      (Bank.ext_trans ee4 (Bank.ext_trans ee5 ee6)))), by unfold seedCost; omega, hnot⟩)
  have e06 : B0.Ext D6 := Bank.ext_trans e05 e6
  have e_0_6 : D0.Ext D6 := Bank.ext_trans e_0_5 e6
  -- Stage 7: countBits, shiftByRank, leVec, final AND
  obtain ⟨D7a, e7a, c7a, hpc⟩ := grow_countBits (w := k + 1) D6 (e_0_6 h0)
    (List.finRange (2 ^ (k - q))) passFn (fun σ _ => hpass σ)
  obtain ⟨D7b, e7b, c7b, hsh⟩ := grow_shiftByRank D7a (e7a (e_0_6 h0))
    (fun x => (echelon (respFn x)).hasP)
    (fun v => e7a (e6 (e45 (hcntR m (le_refl m) v))))
    (fun x => countBits (k + 1) (List.finRange (2 ^ (k - q))) (fun σ => passFn σ x)) hpc
  obtain ⟨D7c, e7c, c7c, hle⟩ := grow_leVec D7b (e7b (e7a (e_0_6 h1)))
    (fun x => toVec (k + 1) (decT x))
    (fun x => shiftByRank (echelon (respFn x)).hasP q (k + 1)
      (countBits (k + 1) (List.finRange (2 ^ (k - q))) (fun σ => passFn σ x)))
    (fun i => e7b (e7a (e06 (hT i)))) hsh
  obtain ⟨D7, e7d, c7d, hfin⟩ := Bank.meet (e7c (e7b (e7a (e6 (e45 (e34 hdim)))))) hle
  -- Bound total gate count via standalone arithmetic lemma
  have htotal : D7.gates.length ≤ B0.gates.length +
      2 ^ 44 * (k + r + m + 3) ^ 12 * (2 ^ winSize k r + 2 ^ (k - q)) := by
    have hcost := buildEvalSpec_cost_le (r := r) (m := m) hqk
    dsimp only at hcost
    simp only [List.length_range] at c3c
    simp only [List.length_finRange] at c7a
    dsimp only [b] at c1a c1b
    dsimp only [seedCost] at c6
    omega
  exact ⟨D7, Bank.ext_trans e06 (Bank.ext_trans e7a (Bank.ext_trans e7b (Bank.ext_trans e7c e7d))),
    htotal, hfin⟩

end Synth

end PEqualNP.Outside.L_meta_32039

theorem PEqualNP.Outside.L_meta_32039 :
    ∀ (k r m q : Nat), 0 < k → q ≤ k →
  let rot := fun (s word : Nat) =>
    ((word <<< (s % k)) ||| (word >>> (k - s % k))) % 2 ^ k
  let step := fun (word : Nat) =>
    (List.range k).foldl (fun acc i =>
      acc ||| ((xor (word.testBit i)
        (!(word.testBit ((i + 1) % k)) && word.testBit ((i + 2) % k))).toNat <<< i)) 0
  let state := fun (col : Bool) (w u : Nat) (c : Fin r → Fin (2^k)) =>
    let g := if col then 2 else 1
    (List.finRange r).foldl (fun x j =>
      step (x ^^^ rot g x ^^^ rot (k-g) x) ^^^
        rot (if col then 3*(j.val+1)+1 else 2*j.val) w ^^^ (c j).val)
      (rot (if col then 3 else 1) w ^^^ u)
  let parity := fun (mask x : Nat) =>
    (List.range k).foldl (fun b i => xor b (mask.testBit i && x.testBit i)) false
  let bits := fun (n x : Nat) => (List.range n).map (fun i => x.testBit i)
  let bank := fun (A : Fin m → Fin (2^k)) =>
    (List.finRange m).flatMap (fun j => bits k (A j).val)
  let sched := fun (c : Fin r → Fin (2^k)) =>
    (List.finRange r).flatMap (fun j => bits k (c j).val)
  let b := min k (max (6*r+1) (7*r-1))
  ∃ C : PEqualNP.CircuitLowerBounds.Circuit,
    PEqualNP.MetaComplexity.FanInTwo C ∧
    PEqualNP.MetaComplexity.NestedCover.ReadsBack (2*k+2*r*k+2*m*k+m+(k+1)) C ∧
    C.size ≤ 2^44 * (k+r+m+3)^12 * (2^b+2^(k-q)) ∧
    ∀ (u v : Fin (2^k)) (cr cc : Fin r → Fin (2^k)) (A B : Fin m → Fin (2^k))
      (y : Fin m → Bool) (t : Fin (2^(k+1))),
      let f := fun (w : Nat) (j : Fin m) =>
        xor (parity (A j).val (state false w u.val cr)) (parity (B j).val (state true w v.val cc))
      let good := fun (d : Fin (2^k)) => ∃ a : Fin m → Bool,
        ∀ (w : Fin (2^k)) (j : Fin m), xor (f (w.val ^^^ d.val) j) (f w.val j) = a j
      let hits := Nat.card {w : Fin (2^k) // ∀ j, f w.val j = y j}
      C.eval (bits k u.val ++ bits k v.val ++ sched cr ++ sched cc ++ bank A ++ bank B ++
        List.ofFn y ++ bits (k+1) t.val) =
        decide (2^q ≤ Nat.card {d : Fin (2^k) // good d} ∧ t.val ≤ hits) := by
  intro k r m q hk hqk
  open PEqualNP.Outside.L_meta_32039 in
  obtain ⟨C, hfan, hback, hsize, heval⟩ := Builder.Bank.finish (buildEvalSpec (r := r) (m := m) hk hqk)
  refine ⟨C, hfan, hback, hsize, fun u v cr cc A B y t => ?_⟩
  open PEqualNP.Outside.L_meta_32039 in
  have hof : List.ofFn (encBits u v cr cc A B y t) = inputList u v cr cc A B y t :=
    ofFn_encBits u v cr cc A B y t
  open PEqualNP.Outside.L_meta_32039 in
  have hdec := dec_encBits u v cr cc A B y t
  open PEqualNP.Outside.L_meta_32039 in
  have hev := heval (encBits u v cr cc A B y t)
  rw [hof] at hev
  rw [hdec.1, hdec.2.1, hdec.2.2.1, hdec.2.2.2.1, hdec.2.2.2.2.1, hdec.2.2.2.2.2.1,
      hdec.2.2.2.2.2.2.1, hdec.2.2.2.2.2.2.2] at hev
  exact hev.trans (evalSpec_correct hk hqk u v cr cc A B y t)
