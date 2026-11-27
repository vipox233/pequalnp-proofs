import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_27215

open PEqualNP.CircuitLowerBounds

private def pm (x : Fin 9 → Bool) : Bool :=
  (x 0 && x 4 && x 8) || (x 0 && x 5 && x 7) || (x 1 && x 3 && x 8) ||
    (x 1 && x 5 && x 6) || (x 2 && x 3 && x 7) || (x 2 && x 4 && x 6)

private def bin (m a b : Bool) : Bool := if m then a && b else a || b

private def firstVal (m : Bool) (a b : Fin 9) (x : Fin 9 → Bool) : Bool :=
  bin m (x a) (x b)

private def matchingRows : Fin 9 → ℕ × ℕ :=
  ![(273, 161), (266, 98), (140, 84), (266, 140), (273, 84),
    (161, 98), (98, 84), (161, 140), (273, 266)]

private def assign (m : Bool) (i j : Fin 9) (z : Bool) (k : Fin 9) : Bool :=
  if k = i then z else
    if m then
      (if (matchingRows i).1.testBit j.val then (matchingRows i).2 else (matchingRows i).1).testBit k.val
    else k == j || (matchingRows i).1.testBit k.val

private theorem assignPm (m : Bool) (i j : Fin 9) : i ≠ j →
    pm (assign m i j false) = false ∧ pm (assign m i j true) = true ∧
      assign m i j false j = !m ∧ assign m i j true j = !m := by
  cases m <;> fin_cases i <;> fin_cases j <;> decide

private theorem witness (m : Bool) (a b i : Fin 9) (hab : a ≠ b) :
    ∃ x y : Fin 9 → Bool, (∀ j : Fin 9, j ≠ i → x j = y j) ∧
      firstVal m a b x = firstVal m a b y ∧
      x i = false ∧ y i = true ∧ pm x = false ∧ pm y = true := by
  let j := if i = a then b else a
  have hj : i ≠ j := by
    by_cases ha : i = a
    · simpa [j, ha] using hab
    · simp [j, ha]
  obtain ⟨hp, hq, hjp, hjq⟩ := assignPm m i j hj
  have agree (k : Fin 9) (hk : k ≠ i) : assign m i j false k = assign m i j true k := by
    simp [assign, hk]
  refine ⟨assign m i j false, assign m i j true, agree, ?_, by simp [assign], by simp [assign], hp, hq⟩
  unfold firstVal
  by_cases ha : i = a
  · have he : j = b := ite_eq_left ha
    rw [← he, hjp, hjq]
    cases m <;> simp [bin]
  · by_cases hb : i = b
    · have he : j = a := ite_eq_right ha
      rw [← he, hjp, hjq]
      cases m <;> simp [bin]
    · rw [agree a (Ne.symm ha), agree b (Ne.symm hb)]

private def firstGate (m : Bool) (a b : Fin 9) : Gate :=
  ⟨if m then .and else .or, [a.val, b.val]⟩

private def secondGate (r : Fin 9) : Gate := ⟨.not, [r.val]⟩

private theorem splitGates (m : Bool) (a b r : Fin 9) (gs : List Gate)
    (h₁ : gs.head? = some (firstGate m a b)) (h₂ : gs.tail.head? = some (secondGate r)) :
    ∃ rest, gs = firstGate m a b :: secondGate r :: rest := by
  cases gs with
  | nil => simp at h₁
  | cons g tail =>
    have hg : g = firstGate m a b := Option.some.inj h₁
    subst g
    cases tail with
    | nil => simp at h₂
    | cons g rest =>
      have hg : g = secondGate r := Option.some.inj h₂
      exact ⟨rest, by rw [hg]⟩

private def reads (gs : List Gate) : List ℕ := gs.flatMap Gate.inputs

private def gateValue (w : List Bool) (g : Gate) : Bool :=
  g.op.eval (g.inputs.map fun i => w.getD i false)

private def step (w : List Bool) (g : Gate) : List Bool := w ++ [gateValue w g]

private def seed (m : Bool) (a b r : Fin 9) (x : Fin 9 → Bool) : List Bool :=
  (List.ofFn x ++ [firstVal m a b x]) ++ [!(x r)]

private theorem inputGet (x : Fin 9 → Bool) (i : ℕ) (hi : i < 9) :
    (List.ofFn x).getD i false = x ⟨i, hi⟩ := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn, dite_eq_left hi]
  rfl

private theorem seedInput (m : Bool) (a b r : Fin 9) (x : Fin 9 → Bool) (i : Fin 9) :
    (seed m a b r x).getD i.val false = x i := by
  have hi := i.isLt
  rw [seed, List.getD_append _ _ _ _ (by simp; omega), List.getD_append _ _ _ _ (by simp)]
  exact inputGet x _ hi

private theorem evalWithSeed (C : Circuit) (m : Bool) (a b r : Fin 9) (gs : List Gate)
    (hgs : C.gates = firstGate m a b :: secondGate r :: gs) (x : Fin 9 → Bool) :
    C.eval (List.ofFn x) = (gs.foldl step (seed m a b r x)).getD C.output false := by
  change (C.gates.foldl step (List.ofFn x)).getD C.output false = _
  rw [hgs]
  simp only [List.foldl_cons]
  have h₀ : (List.ofFn x).getD a.val false = x a := inputGet x _ a.isLt
  have h₁ : (List.ofFn x).getD b.val false = x b := inputGet x _ b.isLt
  have hr : r.val < (List.ofFn x).length := by simp
  have hfirst : step (List.ofFn x) (firstGate m a b) = List.ofFn x ++ [firstVal m a b x] := by
    cases m
    · change step (List.ofFn x) ⟨.or, [a.val, b.val]⟩ = List.ofFn x ++ [x a || x b]
      simp only [step, gateValue, GateOp.eval, List.map_cons, List.map_nil,
        List.any_cons, List.any_nil, id_eq, Bool.or_false, h₀, h₁]
    · change step (List.ofFn x) ⟨.and, [a.val, b.val]⟩ = List.ofFn x ++ [x a && x b]
      simp only [step, gateValue, GateOp.eval, List.map_cons, List.map_nil,
        List.all_cons, List.all_nil, id_eq, Bool.and_true, h₀, h₁]
  rw [hfirst]
  have hread : (List.ofFn x ++ [firstVal m a b x]).getD r.val false = x r := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_append_left hr,
      ← List.getD_eq_getElem?_getD, inputGet x _ r.isLt]
  have hsecond : step (List.ofFn x ++ [firstVal m a b x]) (secondGate r) = seed m a b r x := by
    simp only [step, gateValue, secondGate, GateOp.eval, List.map_cons, List.map_nil,
      List.headD_cons, hread, seed]
  rw [hsecond]

private def RelatedAt (R : Bool → Bool → Prop) (r : ℕ) (u v : List Bool) : Prop :=
  ∀ i, i ≠ r → R (u.getD i false) (v.getD i false)

private theorem extendRelated {R : Bool → Bool → Prop} {r : ℕ} {u v : List Bool}
    (hf : R false false) (hlen : u.length = v.length) (h : RelatedAt R r u v)
    {a b : Bool} (hab : R a b) : RelatedAt R r (u ++ [a]) (v ++ [b]) := by
  intro i hi
  by_cases hlt : i < u.length
  · have hv : i < v.length := hlen ▸ hlt
    simpa only [List.getD_eq_getElem?_getD, List.getElem?_append_left hlt,
      List.getElem?_append_left hv] using h i hi
  · have hu : u.length ≤ i := Nat.le_of_not_gt hlt
    have hv : v.length ≤ i := hlen ▸ hu
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
      List.getElem?_append_right hu, List.getElem?_append_right hv, ← hlen]
    cases i - u.length with
    | zero => simpa using hab
    | succ n => simpa using hf

private theorem seedRelated {R : Bool → Bool → Prop} {m : Bool} {a b r i : Fin 9} {x y : Fin 9 → Bool}
    (refl : ∀ z, R z z) (h : ∀ j : Fin 9, j ≠ i → x j = y j)
    (hfirst : firstVal m a b x = firstVal m a b y) (hnot : R (!(x r)) (!(y r))) :
    RelatedAt R i.val (seed m a b r x) (seed m a b r y) := by
  apply extendRelated (refl false) (by simp) _ hnot
  apply extendRelated (refl false) (by simp)
  · intro j hj
    by_cases hj' : j < 9
    · rw [inputGet x j hj', inputGet y j hj', h _ (fun eq => hj (congrArg Fin.val eq))]
      exact refl _
    · simpa [List.getD_eq_getElem?_getD, hj'] using refl false
  · rw [hfirst]
    exact refl _

private theorem foldRelated (gs : List Gate) {R : Bool → Bool → Prop} {r : ℕ}
    (hf : R false false) (hn : r ∉ reads gs)
    (hg : ∀ g ∈ gs, ∀ u v : List Bool,
      (∀ i ∈ g.inputs, R (u.getD i false) (v.getD i false)) → R (gateValue u g) (gateValue v g))
    {u v : List Bool} (hlen : u.length = v.length) (h : RelatedAt R r u v) :
    RelatedAt R r (gs.foldl step u) (gs.foldl step v) := by
  induction gs generalizing u v with
  | nil => exact h
  | cons g gs ih =>
    simp only [List.foldl_cons]
    apply ih
    · intro hr
      apply hn
      exact List.mem_append.mpr (Or.inr hr)
    · exact fun g' hm => hg g' (List.mem_cons_of_mem g hm)
    · simp [step, hlen]
    · apply extendRelated hf hlen h
      apply hg g (List.mem_cons_self) u v
      intro i hi
      apply h i
      intro eq
      subst i
      exact hn (by simp [reads, hi])

private theorem gateEqual (g : Gate) (u v : List Bool)
    (h : ∀ i ∈ g.inputs, u.getD i false = v.getD i false) : gateValue u g = gateValue v g :=
  congrArg g.op.eval (List.map_congr_left h)

private theorem binaryMonotone : ∀ a b c d : Bool, a ≤ c → b ≤ d →
    ((a && b) ≤ (c && d)) ∧ ((a || b) ≤ (c || d)) := by decide

private theorem gateOrdered (g : Gate) (a b : ℕ)
    (hop : g.op = .and ∨ g.op = .or) (hs : g.inputs = [a, b]) (u v : List Bool)
    (h : ∀ i ∈ g.inputs, u.getD i false ≤ v.getD i false) : gateValue u g ≤ gateValue v g := by
  have hp := h a (by simp [hs])
  have hq := h b (by simp [hs])
  have hmono := binaryMonotone _ _ _ _ hp hq
  rcases hop with hop | hop
  · simpa [gateValue, hs, hop, GateOp.eval] using hmono.1
  · simpa [gateValue, hs, hop, GateOp.eval] using hmono.2

private abbrev Profile := Bool → Option Bool → Bool

private def sensitive (u : Profile) (k : Bool) : Prop :=
  ∃ c, u c none ≠ u c (some k)

private def strong (u : Profile) (k : Bool) : Prop :=
  ∀ c, u c none ≠ u c (some k)

private def admissible (u : Profile) : Prop :=
  (∀ k, strong u k → u false none ≠ u true none) ∧
  ¬ (strong u false ∧ strong u true)

private theorem insensitive {u : Profile} {k : Bool} (h : ¬ sensitive u k) (c : Bool) :
    u c none = u c (some k) := by
  by_contra hne
  exact h ⟨c, hne⟩

private def inv (u : Profile) : Profile := fun c k => !(u c k)

private theorem invSensitive (u : Profile) (k : Bool) :
    sensitive (inv u) k ↔ sensitive u k := by
  simp [sensitive, inv]

private theorem invAdmissible (u : Profile) (h : admissible u) : admissible (inv u) := by
  simpa [admissible, strong, inv] using h

private def join (m : Bool) (u v : Profile) : Profile := fun c k => bin m (u c k) (v c k)

private theorem binComm : ∀ m a b, bin m a b = bin m b a := by decide

private theorem binRelay : ∀ m a b d, bin m a b ≠ bin m d b →
    a ≠ d ∧ b = m ∧ bin m a b = a := by decide

private theorem joinSensitive {m : Bool} {u v : Profile} {k : Bool}
    (h : sensitive (join m u v) k) : sensitive u k ∨ sensitive v k := by
  by_cases hu : sensitive u k
  · exact Or.inl hu
  · right
    obtain ⟨c, hc⟩ := h
    refine ⟨c, ?_⟩
    intro hv
    apply hc
    change bin m (u c none) (v c none) = bin m (u c (some k)) (v c (some k))
    rw [← insensitive hu c, ← hv]

private theorem joinStrong {m : Bool} {u v : Profile} {k : Bool}
    (hv : ¬ sensitive v k) (h : strong (join m u v) k) :
    strong u k ∧ (∀ c, v c none = m) ∧ (∀ c, join m u v c none = u c none) := by
  have localFact (c : Bool) := h c
  have hc (c : Bool) : (u c none ≠ u c (some k)) ∧ v c none = m ∧
      join m u v c none = u c none := by
    have h' := localFact c
    change bin m (u c none) (v c none) ≠ bin m (u c (some k)) (v c (some k)) at h'
    rw [← insensitive hv c] at h'
    exact binRelay _ _ _ _ h'
  exact ⟨fun c => (hc c).1, fun c => (hc c).2.1, fun c => (hc c).2.2⟩

private theorem joinAdmissible {m : Bool} {u v : Profile}
    (hu : admissible u) (hv : admissible v)
    (hd : ∀ k, ¬ (sensitive u k ∧ sensitive v k)) : admissible (join m u v) := by
  have routes (k : Bool) (h : strong (join m u v) k) :
      (strong u k ∧ (∀ c, v c none = m) ∧ (∀ c, join m u v c none = u c none)) ∨
      (strong v k ∧ (∀ c, u c none = m) ∧ (∀ c, join m u v c none = v c none)) := by
    by_cases hvs : sensitive v k
    · right
      have hcomm : join m u v = join m v u := by
        funext c q
        exact binComm m _ _
      rw [hcomm] at h ⊢
      exact joinStrong (fun hus => hd k ⟨hus, hvs⟩) h
    · exact Or.inl (joinStrong hvs h)
  constructor
  · intro k h
    rcases routes k h with ⟨hs, _, he⟩ | ⟨hs, _, he⟩
    · rw [he false, he true]
      exact hu.1 k hs
    · rw [he false, he true]
      exact hv.1 k hs
  · rintro ⟨h₀, h₁⟩
    rcases routes false h₀ with hl | hl <;> rcases routes true h₁ with hr | hr
    · exact hu.2 ⟨hl.1, hr.1⟩
    · exact hv.1 true hr.1 ((hl.2.1 false).trans (hl.2.1 true).symm)
    · exact hu.1 true hr.1 ((hl.2.1 false).trans (hl.2.1 true).symm)
    · exact hv.2 ⟨hl.1, hr.1⟩

private abbrev Samples := Bool → Option Bool → List Bool

private def atWire (w : Samples) (i : ℕ) : Profile := fun c k => (w c k).getD i false

private def fit (w : Samples) (n : ℕ) : Prop := ∀ c k, (w c k).length = n

private def exclusive (w : Samples) (is : List ℕ) : Prop :=
  ∀ i ∈ is, ∀ j ∈ is, i ≠ j → ∀ k, ¬ (sensitive (atWire w i) k ∧ sensitive (atWire w j) k)

private def runSamples (w : Samples) (g : Gate) : Samples := fun c k => step (w c k) g

private def finishSamples (gs : List Gate) (w : Samples) : Samples :=
  fun c k => gs.foldl step (w c k)

private theorem oldWire {w : Samples} {n : ℕ} (hn : fit w n) (g : Gate) (i : ℕ) (hi : i ≠ n) :
    atWire (runSamples w g) i = atWire w i := by
  funext c k
  change (step (w c k) g).getD i false = (w c k).getD i false
  have hlen := hn c k
  by_cases h : i < n
  · exact List.getD_append _ _ _ _ (by omega)
  · have h₀ : (w c k).length ≤ i := by omega
    have h₁ : (step (w c k) g).length ≤ i := by simp [step]; omega
    rw [List.getD_eq_default _ _ h₁, List.getD_eq_default _ _ h₀]

private theorem newWire {w : Samples} {n : ℕ} (hn : fit w n) (g : Gate) (c : Bool)
    (k : Option Bool) : atWire (runSamples w g) n c k = gateValue (w c k) g := by
  change (step (w c k) g).getD n false = _
  rw [step, List.getD_append_right _ _ _ _ (le_of_eq (hn c k)), hn c k, Nat.sub_self]
  rfl

private def GateForm (g : Gate) : Prop :=
  (∃ a, g.op = .not ∧ g.inputs = [a]) ∨
  (∃ a b, a < b ∧ (g.op = .and ∨ g.op = .or) ∧ g.inputs = [a, b])

private theorem newGood {w : Samples} {n : ℕ} {g : Gate} (hn : fit w n) (hg : GateForm g)
    (ha : ∀ i, admissible (atWire w i)) (hd : exclusive w g.inputs) :
    admissible (atWire (runSamples w g) n) ∧
      ∀ k, sensitive (atWire (runSamples w g) n) k →
        ∃ i ∈ g.inputs, sensitive (atWire w i) k := by
  rcases hg with ⟨a, ho, hi⟩ | ⟨a, b, hab, ho, hi⟩
  · have he : atWire (runSamples w g) n = inv (atWire w a) := by
      funext c k
      rw [newWire hn]
      simp [gateValue, ho, hi, GateOp.eval, inv, atWire]
    rw [he]
    exact ⟨invAdmissible _ (ha a), fun k h => ⟨a, by simp [hi], (invSensitive _ _).mp h⟩⟩
  · have hm : ∃ m, atWire (runSamples w g) n = join m (atWire w a) (atWire w b) := by
      rcases ho with ho | ho
      · refine ⟨true, ?_⟩
        funext c k
        rw [newWire hn]
        simp [gateValue, ho, hi, GateOp.eval, join, bin, atWire]
      · refine ⟨false, ?_⟩
        funext c k
        rw [newWire hn]
        simp [gateValue, ho, hi, GateOp.eval, join, bin, atWire]
    obtain ⟨m, he⟩ := hm
    have ham : a ∈ g.inputs := by simp [hi]
    have hbm : b ∈ g.inputs := by simp [hi]
    rw [he]
    refine ⟨joinAdmissible (ha a) (ha b) (hd a ham b hbm hab.ne), ?_⟩
    intro k hk
    exact (joinSensitive hk).elim (fun h => ⟨a, ham, h⟩) (fun h => ⟨b, hbm, h⟩)

private theorem foldGood (gs : List Gate) (hforms : ∀ g ∈ gs, GateForm g)
    (hnd : (reads gs).Nodup) (w : Samples) (n : ℕ) (hn : fit w n)
    (ha : ∀ i, admissible (atWire w i)) (hd : exclusive w (reads gs)) :
    ∀ i, admissible (atWire (finishSamples gs w) i) := by
  induction gs generalizing w n with
  | nil => exact ha
  | cons g gs ih =>
    change (g.inputs ++ reads gs).Nodup at hnd
    change exclusive w (g.inputs ++ reads gs) at hd
    obtain ⟨_, hnd, hsep⟩ := List.nodup_append.mp hnd
    have hl (i : ℕ) (h : i ∈ g.inputs) : i ∈ g.inputs ++ reads gs := List.mem_append_left _ h
    have hr (i : ℕ) (h : i ∈ reads gs) : i ∈ g.inputs ++ reads gs := List.mem_append_right _ h
    obtain ⟨hgood, hflow⟩ := newGood hn (hforms g (List.mem_cons_self)) ha
      (fun i hi j hj => hd i (hl i hi) j (hl j hj))
    change ∀ i, admissible (atWire (finishSamples gs (runSamples w g)) i)
    apply ih (fun g' hg' => hforms g' (List.mem_cons_of_mem _ hg')) hnd _ (n + 1)
    · intro c k
      simp [runSamples, step, hn c k]
    · intro i
      by_cases hi : i = n
      · simpa only [hi] using hgood
      · rw [oldWire hn g i hi]
        exact ha i
    · intro i hi j hj hij k
      have hnew (p : ℕ) (hp : p ∈ reads gs) (hpne : p ≠ n) :
          ¬ (sensitive (atWire (runSamples w g) n) k ∧ sensitive (atWire (runSamples w g) p) k) := by
        rintro ⟨hs, ht⟩
        rw [oldWire hn g p hpne] at ht
        obtain ⟨q, hq, hqs⟩ := hflow k hs
        exact hd q (hl q hq) p (hr p hp) (hsep q hq p hp) k ⟨hqs, ht⟩
      by_cases hin : i = n
      · subst i
        exact hnew j hj hij.symm
      by_cases hjn : j = n
      · subst j
        exact fun h => hnew i hi hin ⟨h.2, h.1⟩
      rw [oldWire hn g i hin, oldWire hn g j hjn]
      exact hd i (hr i hi) j (hr j hj) hij k

private def varWire (d : Fin 4) (k : Bool) : Fin 9 :=
  if k then (![8, 7, 3, 6] : Fin 4 → Fin 9) d else (![4, 5, 1, 2] : Fin 4 → Fin 9) d

private def group (i : Fin 9) : Fin 4 := ![0, 2, 3, 2, 0, 1, 3, 1, 0] i

private theorem groupOfVar (d : Fin 4) (k : Bool) : group (varWire d k) = d := by
  fin_cases d <;> cases k <;> decide

private theorem freshGroup (a b r : Fin 4) : ∃ d : Fin 4, d ≠ a ∧ d ≠ b ∧ d ≠ r := by
  fin_cases a <;> fin_cases b <;> fin_cases r <;> decide

private def yesRows : Fin 4 → ℕ × ℕ × ℕ :=
  ![(273, 257, 17), (161, 129, 33), (266, 264, 258), (84, 80, 20)]

private def noRows : Fin 4 → ℕ × ℕ × ℕ :=
  ![(79, 95, 335), (79, 111, 207), (484, 486, 492), (170, 174, 234)]

private def sample (d : Fin 4) (c : Bool) (k : Option Bool) (i : Fin 9) : Bool :=
  let ns := if c then yesRows d else noRows d
  (if k = none then ns.1 else if k = some false then ns.2.1 else ns.2.2).testBit i.val

private theorem sampleEq (d : Fin 4) (c k : Bool) (i : Fin 9) :
    i ≠ varWire d k → sample d c none i = sample d c (some k) i := by
  fin_cases d <;> cases c <;> cases k <;> fin_cases i <;> decide

private theorem seedSupport (m : Bool) (a b r : Fin 9) (d : Fin 4) (k : Bool) (i : ℕ)
    (havoid : varWire d k ≠ a ∧ varWire d k ≠ b ∧ varWire d k ≠ r)
    (h : sensitive (atWire (fun c q => seed m a b r (sample d c q)) i) k) :
    i = (varWire d k).val := by
  obtain ⟨c, hc⟩ := h
  by_contra hne
  apply hc
  exact seedRelated (R := Eq) (fun _ => rfl) (fun j => sampleEq d c k j)
    (by unfold firstVal; rw [sampleEq d c k a havoid.1.symm, sampleEq d c k b havoid.2.1.symm])
    (by rw [sampleEq d c k r havoid.2.2.symm]) i hne

private theorem noReadOnce (C : Circuit) (m : Bool) (a b r : Fin 9) (gs : List Gate)
    (hgs : C.gates = firstGate m a b :: secondGate r :: gs)
    (hpm : ∀ x, C.eval (List.ofFn x) = pm x)
    (hforms : ∀ g ∈ gs, GateForm g) (hnd : (reads gs).Nodup) : False := by
  obtain ⟨d, ha, hb, hr⟩ := freshGroup (group a) (group b) (group r)
  let w : Samples := fun c k => seed m a b r (sample d c k)
  have support (k : Bool) (i : ℕ) (h : sensitive (atWire w i) k) : i = (varWire d k).val := by
    apply seedSupport m a b r d k i _ h
    exact ⟨fun e => ha ((groupOfVar d k).symm.trans (congrArg group e)),
      fun e => hb ((groupOfVar d k).symm.trans (congrArg group e)),
      fun e => hr ((groupOfVar d k).symm.trans (congrArg group e))⟩
  have ha (i : ℕ) : admissible (atWire w i) := by
    have hs (k : Bool) (h : strong (atWire w i) k) := support k i ⟨false, h false⟩
    constructor
    · intro k hk
      rw [hs k hk]
      change (seed m a b r (sample d false none)).getD (varWire d k).val false ≠
        (seed m a b r (sample d true none)).getD (varWire d k).val false
      rw [seedInput, seedInput]
      fin_cases d <;> cases k <;> decide
    · rintro ⟨hl, hr⟩
      have he := (hs false hl).symm.trans (hs true hr)
      have hne : (varWire d false).val ≠ (varWire d true).val := by fin_cases d <;> decide
      exact hne he
  have hd : exclusive w (reads gs) := by
    rintro i _ j _ hne k ⟨hi, hj⟩
    exact hne ((support k i hi).trans (support k j hj).symm)
  have hv := foldGood gs hforms hnd w 11 (by intro c k; simp [w, seed]) ha hd C.output
  apply hv.2
  have he (c : Bool) (q : Option Bool) :
      atWire (finishSamples gs w) C.output c q = pm (sample d c q) :=
    (evalWithSeed C m a b r gs hgs (sample d c q)).symm.trans (hpm _)
  have hstrong (k : Bool) : strong (atWire (finishSamples gs w) C.output) k := by
    intro c
    rw [he c none, he c (some k)]
    fin_cases d <;> cases c <;> cases k <;> decide
  exact ⟨hstrong false, hstrong true⟩

private theorem mustRead (C : Circuit) (m : Bool) (a b r i : Fin 9) (hab : a ≠ b) (gs : List Gate)
    (hgs : C.gates = firstGate m a b :: secondGate r :: gs) (hne : i.val ≠ r.val)
    (hout : C.output ≠ i.val) (hpm : ∀ x, C.eval (List.ofFn x) = pm x) : i.val ∈ reads gs := by
  by_contra hn
  obtain ⟨lo, hi, he, hfirst, _, _, hlo, hhi⟩ := witness m a b i hab
  have hr : lo r = hi r := he r (fun eq => hne (congrArg Fin.val eq.symm))
  have hseed : RelatedAt Eq i.val (seed m a b r lo) (seed m a b r hi) :=
    seedRelated (fun _ => rfl) he hfirst (congrArg (fun b => !b) hr)
  have hfold := foldRelated gs rfl hn (fun g _ => gateEqual g) (by simp [seed]) hseed
  have heval := hfold C.output hout
  rw [← evalWithSeed C m a b r gs hgs, ← evalWithSeed C m a b r gs hgs, hpm, hpm, hlo, hhi] at heval
  exact Bool.false_ne_true heval

private theorem boundReads (gs : List Gate) (h : ∀ g ∈ gs, g.inputs.length ≤ 2) :
    (reads gs).length ≤ 2 * gs.length ∧
    ((reads gs).length = 2 * gs.length → ∀ g ∈ gs, g.inputs.length = 2) := by
  induction gs with
  | nil => simp [reads]
  | cons g gs ih =>
    obtain ⟨hbound, heq⟩ := ih (fun g' hg' => h g' (List.mem_cons_of_mem g hg'))
    have hg := h g (List.mem_cons_self)
    have hs : (reads (g :: gs)).length = g.inputs.length + (reads gs).length := by
      simp [reads]
    simp only [hs, List.length_cons]
    constructor
    · omega
    · intro hfull g' hm
      rcases List.mem_cons.mp hm with rfl | hm
      · omega
      · exact heq (by omega) g' hm

private def Shaped (gs : List Gate) : Prop :=
  ∀ j : Fin gs.length,
    ((gs.get j).op = .not ∧ ∃ a, a < 9 + j.val ∧ (gs.get j).inputs = [a]) ∨
    (((gs.get j).op = .and ∨ (gs.get j).op = .or) ∧
      ∃ a b, a < b ∧ b < 9 + j.val ∧ (gs.get j).inputs = [a, b])

private theorem noWithInput (op : GateOp) (a b r : Fin 9) (C : Circuit)
    (hop : op = .and ∨ op = .or) (hab : a ≠ b) (hsize : C.size ≤ 12)
    (hpm : ∀ x, C.eval (List.ofFn x) = pm x) (hout : C.output + 1 = 9 + C.size)
    (hshape : Shaped C.gates)
    (hlive : ∀ j : Fin C.gates.length, j.val + 1 < C.gates.length →
      ∃ k : Fin C.gates.length, j.val < k.val ∧ 9 + j.val ∈ (C.gates.get k).inputs)
    (h₁ : C.gates.head? = some ⟨op, [a.val, b.val]⟩) (h₂ : C.gates.tail.head? = some (secondGate r)) : False := by
  let m := op.eval []
  have hfirst : C.gates.head? = some (firstGate m a b) := by
    rcases hop with rfl | rfl <;> exact h₁
  obtain ⟨gs, hgs⟩ := splitGates m a b r C.gates hfirst h₂
  have hlen : C.gates.length = gs.length + 2 := by simp [hgs, Nat.add_assoc]
  change C.gates.length ≤ 12 at hsize
  change C.output + 1 = 9 + C.gates.length at hout
  have hforms : ∀ g ∈ gs, GateForm g := by
    intro g hg
    have hmem : g ∈ C.gates := by simp [hgs, hg]
    obtain ⟨j, rfl⟩ := List.mem_iff_get.mp hmem
    rcases hshape j with ⟨hop, a, _, ha⟩ | ⟨hop, a, b, hlt, _, hab⟩
    · exact Or.inl ⟨a, hop, ha⟩
    · exact Or.inr ⟨a, b, hlt, hop, hab⟩
  obtain ⟨hbound, hfull⟩ := boundReads gs (by
    intro g hg
    rcases hforms g hg with ⟨a, _, ha⟩ | ⟨a, b, _, _, hab⟩
    · simp [ha]
    · simp [hab])

  let required := (Finset.range (10 + gs.length)).erase r.val
  have hsub : required ⊆ (reads gs).toFinset := by
    intro w hw
    obtain ⟨hne, hwr⟩ := Finset.mem_erase.mp hw
    have hwlt := Finset.mem_range.mp hwr
    apply List.mem_toFinset.mpr
    by_cases hi : w < 9
    · exact mustRead C m a b r ⟨w, hi⟩ hab gs hgs hne (by omega) hpm
    · let j : Fin C.gates.length := ⟨w - 9, by omega⟩
      obtain ⟨k, _, hk⟩ := hlive j (by dsimp [j]; omega)
      have hwj : 9 + j.val = w := by dsimp [j]; omega
      rw [hwj] at hk
      have hm : C.gates.get k ∈ firstGate m a b :: secondGate r :: gs := by
        rw [← hgs]
        exact List.get_mem C.gates k
      simp only [List.mem_cons] at hm
      rcases hm with h | h | h
      · rw [h] at hk
        simp [firstGate] at hk
        have ha := a.isLt
        have hb := b.isLt
        omega
      · rw [h] at hk
        simp [secondGate] at hk
        have hr := r.isLt
        omega
      · exact List.mem_flatMap.mpr ⟨_, h, hk⟩
  have hr := r.isLt
  have hcard : required.card = 9 + gs.length := by
    have hmem : r.val ∈ Finset.range (10 + gs.length) := Finset.mem_range.mpr (by omega)
    dsimp [required]
    rw [Finset.card_erase_of_mem hmem, Finset.card_range]
    omega
  have hrequired := Finset.card_le_card hsub
  have hreadCard := (reads gs).toFinset_card_le

  have tight (he : (reads gs).toFinset.card = (reads gs).length) : False :=
    noReadOnce C m a b r gs hgs hpm hforms (Multiset.toFinset_card_eq_card_iff_nodup.mp he)
  by_cases hnotRead : r.val ∈ reads gs
  · apply tight
    have hall : Finset.range (10 + gs.length) ⊆ (reads gs).toFinset := by
      intro w hw
      by_cases e : w = r.val
      · exact List.mem_toFinset.mpr (e.symm ▸ hnotRead)
      · exact hsub (Finset.mem_erase.mpr ⟨e, hw⟩)
    have hc := Finset.card_le_card hall
    rw [Finset.card_range] at hc
    omega
  by_cases htwo : ∀ g ∈ gs, g.inputs.length = 2
  swap
  · apply tight
    have hshort : (reads gs).length < 2 * gs.length := lt_of_le_of_ne hbound (fun e => htwo (hfull e))
    omega
  obtain ⟨lo, hi, he, hfirst, hlow, hhigh, hlo, hhi⟩ := witness m a b r hab
  have hseed : RelatedAt (· ≤ ·) r.val (seed m a b r hi) (seed m a b r lo) :=
    seedRelated (fun _ => le_rfl) (fun j hj => (he j hj).symm) hfirst.symm (by simp [hlow, hhigh])
  have hg : ∀ g ∈ gs, ∀ u v : List Bool,
      (∀ i ∈ g.inputs, u.getD i false ≤ v.getD i false) → gateValue u g ≤ gateValue v g := by
    intro g hm
    rcases hforms g hm with ⟨a, _, ha⟩ | ⟨a, b, _, hop, hab⟩
    · have ht := htwo g hm
      simp [ha] at ht
    · exact gateOrdered g a b hop hab
  have hfold := foldRelated gs (by decide) hnotRead hg (by simp [seed]) hseed
  have heval := hfold C.output (by omega)
  rw [← evalWithSeed C m a b r gs hgs, ← evalWithSeed C m a b r gs hgs, hpm, hpm, hhi, hlo] at heval
  exact (by decide : ¬ true ≤ false) heval

end PEqualNP.Outside.L_meta_27215

theorem PEqualNP.Outside.L_meta_27215 : ¬ (∃ C : PEqualNP.CircuitLowerBounds.Circuit,
    PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 12 ∧
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
    C.gates.head? = some ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 1]⟩ ∧
    C.gates.tail.head? = some ⟨PEqualNP.CircuitLowerBounds.GateOp.not, [0]⟩) := by
  rintro ⟨C, _, hsize, hpm, hout, hshape, _, hlive, h₁, h₂⟩
  exact L_meta_27215.noWithInput _ ⟨_, by decide⟩ ⟨_, by decide⟩ ⟨_, by decide⟩
    C (by simp) (by decide) hsize hpm hout hshape hlive h₁ h₂
