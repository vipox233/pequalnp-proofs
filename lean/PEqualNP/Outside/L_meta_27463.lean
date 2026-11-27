import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_27463

abbrev Gate := PEqualNP.CircuitLowerBounds.Gate
abbrev Circuit := PEqualNP.CircuitLowerBounds.Circuit

def gateValue (w : List Bool) (g : Gate) : Bool :=
  g.op.eval (g.inputs.map (fun a => w.getD a false))

def step (w : List Bool) (g : Gate) : List Bool := w ++ [gateValue w g]

lemma stepAt (w : List Bool) (g : Gate) :
    (step w g).getD w.length false = gateValue w g := by
  simp only [step, List.getD_eq_getElem?_getD]
  rw [List.getElem?_append_right (by omega)]
  simp

lemma stepOther (w : List Bool) (g : Gate) {a : ℕ} (ha : a ≠ w.length) :
    (step w g).getD a false = w.getD a false := by
  rcases lt_or_gt_of_ne ha with h | h
  · unfold step
    rw [List.getD_append _ _ _ _ h]
  · rw [List.getD_eq_default _ _ (by simp [step]; omega),
      List.getD_eq_default _ _ (by omega)]

lemma stepLength (w : List Bool) (g : Gate) : (step w g).length = w.length + 1 := by
  simp [step]

def hot {n : ℕ} (i : Fin n) : List Bool := List.ofFn (fun j : Fin n => decide (j = i))

def input {n : ℕ} (i : Option (Fin n)) : List Bool :=
  match i with
  | none => List.replicate n false
  | some j => hot j

def run {n : ℕ} (gs : List Gate) (i : Option (Fin n)) : List Bool :=
  gs.foldl step (input i)

def views {n : ℕ} (gs : List Gate) (i : Option (Fin n)) (a : ℕ) : Bool :=
  (run gs i).getD a false

lemma inputLength {n : ℕ} (i : Option (Fin n)) : (input i).length = n := by
  cases i <;> simp [input, hot]

lemma runLength {n : ℕ} (gs : List Gate) (i : Option (Fin n)) :
    (run gs i).length = n + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [run, inputLength]
  | append_singleton gs g ih =>
    have h : run (gs ++ [g]) i = step (run gs i) g := by simp [run, List.foldl_append]
    rw [h, stepLength, ih]
    simp [Nat.add_assoc]

lemma runAppend {n : ℕ} (gs : List Gate) (g : Gate) (i : Option (Fin n)) :
    run (gs ++ [g]) i = step (run gs i) g := by simp [run, List.foldl_append]

def agree (W : Finset ℕ) (u v : ℕ → Bool) : Prop := ∀ a ∈ W, u a = v a

def separated {n : ℕ} (S : Finset (Fin n)) (W : Finset ℕ)
    (v : Option (Fin n) → ℕ → Bool) : Prop :=
  (∀ i ∈ S, ¬ agree W (v (some i)) (v none)) ∧
    (∀ i ∈ S, ∀ j ∈ S, agree W (v (some i)) (v (some j)) → i = j)

def difference {n : ℕ} (W : Finset ℕ) (v : Option (Fin n) → ℕ → Bool) (i : Fin n) :
    Finset ℕ := W.filter (fun a => v (some i) a ≠ v none a)

def singletons {n : ℕ} (S : Finset (Fin n)) (W : Finset ℕ)
    (v : Option (Fin n) → ℕ → Bool) : Finset (Fin n) :=
  S.filter (fun i => (difference W v i).card = 1)

def potential {n : ℕ} (S : Finset (Fin n)) (W : Finset ℕ)
    (v : Option (Fin n) → ℕ → Bool) : ℕ :=
  W.card + (singletons S W v).card

lemma diffNonempty {n : ℕ} {S : Finset (Fin n)} {W : Finset ℕ}
    {v : Option (Fin n) → ℕ → Bool} (h : separated S W v) {i : Fin n} (hi : i ∈ S) :
    (difference W v i).Nonempty := by
  classical
  by_contra hn
  apply h.1 i hi
  intro a ha
  by_contra hneq
  exact hn ⟨a, Finset.mem_filter.mpr ⟨ha, hneq⟩⟩

lemma sameDiff {n : ℕ} {W : Finset ℕ} {v : Option (Fin n) → ℕ → Bool}
    {i j : Fin n} (h : difference W v i = difference W v j) :
    agree W (v (some i)) (v (some j)) := by
  intro a ha
  have hb : (v (some i) a ≠ v none a) ↔ (v (some j) a ≠ v none a) := by
    have hm : a ∈ difference W v i ↔ a ∈ difference W v j := by rw [h]
    simpa [difference, ha] using hm
  cases h₀ : v none a <;> cases h₁ : v (some i) a <;> cases h₂ : v (some j) a <;>
    simp_all

lemma countAssigned {n : ℕ} {S T : Finset (Fin n)} {W Q : Finset ℕ}
    {v : Option (Fin n) → ℕ → Bool} (sep : separated S W v) (hsub : T ⊆ S)
    (h : ∀ i ∈ T, ∃ a ∈ Q, difference W v i = {a}) : T.card ≤ Q.card := by
  classical
  have choices : ∀ i : ↥T, ∃ a ∈ Q, difference W v i.val = {a} :=
    fun i => h i.val i.property
  choose pick hmem heq using choices
  let f : ↥T → ↥Q := fun i => ⟨pick i, hmem i⟩
  apply Finset.card_le_card_of_injective (f := f)
  intro i j hij
  apply Subtype.ext
  have hab : pick i = pick j := congrArg Subtype.val hij
  apply sep.2 i.val (hsub i.property) j.val (hsub j.property)
  exact sameDiff ((heq i).trans (hab ▸ (heq j).symm))

lemma countSingletons {n : ℕ} {S : Finset (Fin n)} {W : Finset ℕ}
    {v : Option (Fin n) → ℕ → Bool} (sep : separated S W v) :
    (singletons S W v).card ≤ W.card := by
  apply countAssigned sep (Finset.filter_subset _ _)
  intro i hi
  obtain ⟨a, he⟩ := Finset.card_eq_one.mp (Finset.mem_filter.mp hi).2
  have hmem : a ∈ difference W v i := by rw [he]; simp
  exact ⟨a, (Finset.mem_filter.mp hmem).1, he⟩

set_option maxHeartbeats 1200000 in
lemma transfer {n : ℕ} (S : Finset (Fin n)) (R P : Finset ℕ) (o : ℕ) (ho : o ∉ R)
    (old next : Option (Fin n) → ℕ → Bool)
    (retained : ∀ i a, a ∈ R → next i a = old i a)
    (gate : ∀ i j, agree P (old i) (old j) → next i o = next j o)
    (hs : separated S (insert o R) next) :
    separated S (R ∪ P) old ∧
      potential S (R ∪ P) old + 1 ≤ potential S (insert o R) next + P.card := by
  classical
  have liftAgree : ∀ i j, agree (R ∪ P) (old i) (old j) →
      agree (insert o R) (next i) (next j) := by
    intro i j ha a hmem
    rcases Finset.mem_insert.mp hmem with rfl | hr
    · exact gate i j (fun z hz => ha z (Finset.mem_union.mpr (.inr hz)))
    · rw [retained i a hr, retained j a hr]
      exact ha a (Finset.mem_union.mpr (.inl hr))
  have sepBefore : separated S (R ∪ P) old := by
    refine ⟨?_, ?_⟩
    · intro i hi he
      exact hs.1 i hi (liftAgree _ _ he)
    · intro i hi j hj he
      exact hs.2 i hi j hj (liftAgree _ _ he)
  refine ⟨sepBefore, ?_⟩
  let U := singletons S (R ∪ P) old
  let V := singletons S (insert o R) next
  have hLost : (U \ V).card ≤ (R ∩ P).card := by
    apply countAssigned sepBefore
    · intro i hi
      exact (Finset.mem_filter.mp (Finset.mem_sdiff.mp hi).1).1
    · intro i hi
      obtain ⟨hiU, hiV⟩ := Finset.mem_sdiff.mp hi
      obtain ⟨hiS, hcard⟩ := Finset.mem_filter.mp hiU
      obtain ⟨a, hone⟩ := Finset.card_eq_one.mp hcard
      have clash : ∀ x, difference (insert o R) next i ⊆ {x} → False := by
        intro x hsub
        have hle := Finset.card_le_card hsub
        have hp := Finset.card_pos.mpr (diffNonempty hs hiS)
        apply hiV
        apply Finset.mem_filter.mpr
        refine ⟨hiS, ?_⟩
        simpa using (show (difference (insert o R) next i).card = 1 by
          simp only [Finset.card_singleton] at hle
          omega)
      have pin : ∀ z ∈ R, next (some i) z ≠ next none z → z ∈ ({a} : Finset ℕ) := by
        intro z hz hdiff
        rw [← hone]
        apply Finset.mem_filter.mpr
        exact ⟨Finset.mem_union.mpr (.inl hz), by simpa [retained _ _ hz] using hdiff⟩
      have haR : a ∈ R := by
        by_contra ha
        apply clash o
        intro z hz
        obtain ⟨hzA, hdiff⟩ := Finset.mem_filter.mp hz
        rcases Finset.mem_insert.mp hzA with rfl | hzR
        · simp
        · have he : z = a := Finset.mem_singleton.mp (pin z hzR hdiff)
          exact (ha (he ▸ hzR)).elim
      have haP : a ∈ P := by
        by_contra ha
        have hsP : agree P (old (some i)) (old none) := by
          intro z hz
          by_contra hdiff
          have hm : z ∈ difference (R ∪ P) old i :=
            Finset.mem_filter.mpr ⟨Finset.mem_union.mpr (.inr hz), hdiff⟩
          have he : z = a := by simpa [hone] using hm
          exact ha (he ▸ hz)
        apply clash a
        intro z hz
        obtain ⟨hzA, hdiff⟩ := Finset.mem_filter.mp hz
        rcases Finset.mem_insert.mp hzA with rfl | hzR
        · exact (hdiff (gate _ _ hsP)).elim
        · exact pin z hzR hdiff
      exact ⟨a, Finset.mem_inter.mpr ⟨haR, haP⟩, hone⟩
  have hc := Finset.card_le_card_sdiff_add_card (s := U) (t := V)
  have hUnion := Finset.card_union_add_card_inter R P
  have hInsert : (insert o R).card = R.card + 1 := Finset.card_insert_of_notMem ho
  change (R ∪ P).card + U.card + 1 ≤ (insert o R).card + V.card + P.card
  omega

lemma viewsAppendOther {n : ℕ} (gs : List Gate) (g : Gate) (i : Option (Fin n))
    {a : ℕ} (h : a ≠ n + gs.length) : views (gs ++ [g]) i a = views gs i a := by
  unfold views
  rw [runAppend]
  apply stepOther
  simpa [runLength] using h

lemma viewsAppendGate {n : ℕ} (gs : List Gate) (g : Gate) (i : Option (Fin n)) :
    views (gs ++ [g]) i (n + gs.length) = gateValue (run gs i) g := by
  unfold views
  rw [runAppend, ← runLength gs i, stepAt]

def binaryCount (gs : List Gate) : ℕ :=
  gs.countP (fun g => decide (g.inputs.length = 2))

lemma binaryLe (gs : List Gate) : binaryCount gs ≤ gs.length :=
  List.countP_le_length

lemma binaryAppend (gs : List Gate) (g : Gate) :
    binaryCount (gs ++ [g]) = binaryCount gs + (if g.inputs.length = 2 then 1 else 0) := by
  simp [binaryCount, List.countP_append]

set_option maxHeartbeats 1000000 in
lemma walkBack {n : ℕ} (S : Finset (Fin n)) (gs : List Gate) :
    ∀ A : Finset ℕ, (∀ g ∈ gs, g.inputs.length ≤ 2) → separated S A (views gs) →
      ∃ B, separated S B (views []) ∧
        potential S B (views []) ≤ potential S A (views gs) + binaryCount gs := by
  classical
  induction gs using List.reverseRecOn with
  | nil =>
    intro A _ h
    exact ⟨A, h, by simp [binaryCount]⟩
  | append_singleton gs g ih =>
    intro A hall hs
    let o := n + gs.length
    have hold : ∀ h ∈ gs, (h : Gate).inputs.length ≤ 2 :=
      fun h hh => hall h (List.mem_append.mpr (.inl hh))
    have hgate : g.inputs.length ≤ 2 := hall g (by simp)
    by_cases live : o ∈ A
    · let R := A.erase o
      let P := g.inputs.toFinset
      have hinsert : insert o R = A := Finset.insert_erase live
      have ho : o ∉ R := Finset.notMem_erase _ _
      have hR (i : Option (Fin n)) (a) (ha : a ∈ R) :
          views (gs ++ [g]) i a = views gs i a :=
        viewsAppendOther gs g i (Finset.mem_erase.mp ha).1
      have hP (i j : Option (Fin n)) (h : agree P (views gs i) (views gs j)) :
          views (gs ++ [g]) i o = views (gs ++ [g]) j o := by
        change views (gs ++ [g]) i (n + gs.length) = views (gs ++ [g]) j (n + gs.length)
        rw [viewsAppendGate, viewsAppendGate]
        unfold gateValue
        congr 1
        apply List.map_congr_left
        intro a ha
        exact h a (List.mem_toFinset.mpr ha)
      have nextSep : separated S (insert o R) (views (gs ++ [g])) := by
        simpa only [hinsert] using hs
      obtain ⟨prior, delta⟩ := transfer S R P o ho (views gs) (views (gs ++ [g])) hR hP nextSep
      rw [hinsert] at delta
      obtain ⟨B, hSep, hBound⟩ := ih (R ∪ P) hold prior
      have hcard : P.card ≤ g.inputs.length := List.toFinset_card_le g.inputs
      refine ⟨B, hSep, ?_⟩
      rw [binaryAppend]
      by_cases h₂ : g.inputs.length = 2 <;> simp only [h₂, ite_true, ite_false] <;> omega
    · have holdEq (i : Option (Fin n)) (a) (ha : a ∈ A) :
          views (gs ++ [g]) i a = views gs i a :=
        viewsAppendOther gs g i (fun eq => live (by
          change n + gs.length ∈ A
          rwa [← eq]))
      have liftEq (i j : Option (Fin n)) (h : agree A (views gs i) (views gs j)) :
          agree A (views (gs ++ [g]) i) (views (gs ++ [g]) j) := by
        intro a ha
        rw [holdEq i a ha, holdEq j a ha]
        exact h a ha
      have hsep : separated S A (views gs) := by
        refine ⟨?_, ?_⟩
        · intro i hi h
          exact hs.1 i hi (liftEq _ _ h)
        · intro i hi j hj h
          exact hs.2 i hi j hj (liftEq _ _ h)
      have hd (i : Fin n) :
          difference A (views (gs ++ [g])) i = difference A (views gs) i := by
        ext a
        by_cases ha : a ∈ A
        · simp [difference, ha, holdEq _ _ ha]
        · simp [difference, ha]
      have hpot : potential S A (views (gs ++ [g])) = potential S A (views gs) := by
        simp only [potential, singletons, hd]
      obtain ⟨B, hb, hbound⟩ := ih A hold hsep
      refine ⟨B, hb, ?_⟩
      rw [hpot, binaryAppend]
      omega

lemma rawHot {n : ℕ} (i : Fin n) {a : ℕ} (ha : a < n) :
    views [] (some i) a = decide ((⟨a, ha⟩ : Fin n) = i) := by
  change (hot i).getD a false = _
  rw [List.getD_eq_getElem _ _ (by simpa [hot] using ha)]
  simp only [hot, List.getElem_ofFn]

lemma rawDiff {n : ℕ} (i : Fin n) (a : ℕ) :
    views [] (some i) a ≠ views [] (none : Option (Fin n)) a ↔ a = i.val := by
  have hz : views [] (none : Option (Fin n)) a = false := by
    change (List.replicate n false).getD a false = false
    by_cases ha : a < n
    · rw [List.getD_eq_getElem _ _ (by simpa using ha)]
      simp
    · exact List.getD_eq_default _ _ (by simp; omega)
  rw [hz]
  by_cases ha : a < n
  · rw [rawHot i ha]
    simp [Fin.ext_iff]
  · have hval : views [] (some i) a = false := by
      change (hot i).getD a false = false
      exact List.getD_eq_default _ _ (by simp [hot]; omega)
    rw [hval]
    have hx := i.isLt
    simp [show a ≠ i.val by omega]

lemma basePotential {n : ℕ} (S : Finset (Fin n)) (W : Finset ℕ)
    (h : separated S W (views [])) : 2 * S.card ≤ potential S W (views []) := by
  have live (i : Fin n) (hi : i ∈ S) : i.val ∈ W := by
    obtain ⟨a, ha⟩ := diffNonempty h hi
    obtain ⟨hm, hv⟩ := Finset.mem_filter.mp ha
    have eq := (rawDiff i a).mp hv
    simpa only [← eq] using hm
  have hdom : S.image Fin.val ⊆ W := by
    intro a ha
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp ha
    exact live i hi
  have hcard := Finset.card_le_card hdom
  rw [Finset.card_image_of_injective _ Fin.val_injective] at hcard
  have hone : singletons S W (views []) = S := by
    ext i
    constructor
    · exact fun hm => (Finset.mem_filter.mp hm).1
    · intro hi
      have hd : difference W (views []) i = {i.val} := by
        ext a
        simp only [difference, Finset.mem_filter, Finset.mem_singleton, rawDiff]
        exact ⟨fun h => h.2, fun e => ⟨e.symm ▸ live i hi, e⟩⟩
      exact Finset.mem_filter.mpr ⟨hi, by rw [hd]; simp⟩
  unfold potential
  rw [hone]
  omega

def encoder {n k : ℕ} (F : Fin n → Finset (Fin k)) (C : Circuit) : Prop :=
  ∀ j : Fin k, ∃ a : ℕ, ∀ i : Fin n, views C.gates (some i) a = decide (j ∈ F i)

set_option maxHeartbeats 1000000 in
lemma lowerBound {n k : ℕ} (F : Fin n → Finset (Fin k)) (hf : Function.Injective F)
    (C : Circuit) (he : encoder F C) (hfanin : ∀ g ∈ C.gates, g.inputs.length ≤ 2) :
    2 * n ≤ binaryCount C.gates + 2 * k + 2 := by
  classical
  unfold encoder at he
  choose out hOut using he
  let W : Finset ℕ := Finset.univ.image out
  let zeroWord : Finset (Fin k) := Finset.univ.filter (fun j => views C.gates (none : Option (Fin n)) (out j) = true)
  let S : Finset (Fin n) := Finset.univ.filter (fun i => F i ≠ zeroWord)
  have hW : ∀ j, out j ∈ W := fun j => Finset.mem_image.mpr ⟨j, by simp, rfl⟩
  have sep : separated S W (views C.gates) := by
    refine ⟨?_, ?_⟩
    · intro i hi h
      apply (Finset.mem_filter.mp hi).2
      ext j
      have ha := h (out j) (hW j)
      simp only [zeroWord, Finset.mem_filter, Finset.mem_univ, true_and]
      rw [← ha, hOut]
      simp
    · intro i _ j _ h
      apply hf
      ext a
      have hv := h (out a) (hW a)
      rw [hOut a i, hOut a j] at hv
      simpa using hv
  have hxCard : n ≤ S.card + 1 := by
    have hpartition := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin n)))
      (fun i : Fin n => F i ≠ zeroWord)
    have hzero : ((Finset.univ : Finset (Fin n)).filter (fun i => ¬ F i ≠ zeroWord)).card ≤ 1 := by
      apply Finset.card_le_one.mpr
      intro i hi j hj
      apply hf
      have hi' : F i = zeroWord := not_ne_iff.mp (Finset.mem_filter.mp hi).2
      have hj' : F j = zeroWord := not_ne_iff.mp (Finset.mem_filter.mp hj).2
      exact hi'.trans hj'.symm
    change S.card + _ = (Finset.univ : Finset (Fin n)).card at hpartition
    rw [Finset.card_univ, Fintype.card_fin] at hpartition
    omega
  have hWcard : W.card ≤ k := by
    dsimp [W]
    exact Finset.card_image_le.trans_eq (by simp)
  obtain ⟨B, hB, hBack⟩ := walkBack S C.gates W hfanin sep
  have hStart := basePotential S B hB
  have hEnd := countSingletons sep
  unfold potential at hBack hStart
  omega


def orGates (gs : List Gate) : Prop :=
  ∀ g ∈ gs, g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ g.inputs.length = 2

def covers {n k : ℕ} (F : Fin n → Finset (Fin k)) (A : Finset (Fin n))
    (gs : List Gate) (w : Fin n → ℕ) : Prop :=
  ∀ (z : Fin n) (j : Fin k), j ∈ F z ↔
    ∃ a ∈ A, j ∈ F a ∧ views gs (some z) (w a) = true

lemma orValue (v : List Bool) (a b : ℕ) :
    gateValue v ⟨.or, [a, b]⟩ = (v.getD a false || v.getD b false) := by
  simp [gateValue, PEqualNP.CircuitLowerBounds.GateOp.eval]

set_option maxHeartbeats 1000000 in
lemma extend {n k : ℕ} (F : Fin n → Finset (Fin k)) (A : Finset (Fin n))
    (gs : List Gate) (w : Fin n → ℕ) (i p q : Fin n)
    (hi : i ∈ A) (hp : p ∈ A) (hq : q ∈ A)
    (hps : F p ⊂ F i) (hqs : F q ⊂ F i) (hu : F p ∪ F q = F i)
    (hg : orGates gs) (hw : ∀ a, w a < n + gs.length) (hc : covers F A gs w) :
    ∃ next w', next.length = gs.length + 2 ∧ orGates next ∧
      (∀ a, w' a < n + next.length) ∧ covers F (A.erase i) next w' := by
  classical
  have hcp := Finset.card_lt_card hps
  have hcq := Finset.card_lt_card hqs
  have hpi : p ≠ i := by intro e; simp [e] at hcp
  have hqi : q ≠ i := by intro e; simp [e] at hcq
  have hpq : p ≠ q := by
    intro e
    subst q
    have eq : F p = F i := by simpa using hu
    rw [eq] at hcp
    exact (lt_irrefl _ hcp)
  let o := n + gs.length
  let ga : Gate := ⟨.or, [w p, w i]⟩
  let gb : Gate := ⟨.or, [w q, w i]⟩
  let prev := gs ++ [ga]
  let next := prev ++ [gb]
  let w' : Fin n → ℕ := fun a => if a = p then o else if a = q then o + 1 else w a
  have prevLen : n + prev.length = o + 1 := by simp [prev, o, Nat.add_assoc]
  have nextLen : next.length = gs.length + 2 := by simp [next, prev]
  have prevValue (z a : Fin n) :
      views prev (some z) (w a) = views gs (some z) (w a) :=
    viewsAppendOther gs ga (some z) (Nat.ne_of_lt (hw a))
  have oldValue (z a : Fin n) :
      views next (some z) (w a) = views gs (some z) (w a) := by
    change views (prev ++ [gb]) (some z) (w a) = _
    rw [viewsAppendOther prev gb (some z) (by rw [prevLen]; have h := hw a; omega), prevValue]
  have outA (z : Fin n) :
      views next (some z) o = (views gs (some z) (w p) || views gs (some z) (w i)) := by
    change views (prev ++ [gb]) (some z) o = _
    rw [viewsAppendOther prev gb (some z) (by rw [prevLen]; omega)]
    change views (gs ++ [ga]) (some z) (n + gs.length) = _
    rw [viewsAppendGate]
    exact orValue (run gs (some z)) (w p) (w i)
  have outB (z : Fin n) :
      views next (some z) (o + 1) = (views gs (some z) (w q) || views gs (some z) (w i)) := by
    change views (prev ++ [gb]) (some z) (o + 1) = _
    rw [← prevLen, viewsAppendGate]
    change gateValue (run prev (some z)) ⟨.or, [w q, w i]⟩ = _
    rw [orValue]
    change (views prev (some z) (w q) || views prev (some z) (w i)) = _
    rw [prevValue, prevValue]
  have getP (z : Fin n) :
      views next (some z) (w' p) = (views gs (some z) (w p) || views gs (some z) (w i)) := by
    simpa only [w', ite_true] using outA z
  have getQ (z : Fin n) :
      views next (some z) (w' q) = (views gs (some z) (w q) || views gs (some z) (w i)) := by
    simpa only [w', Ne.symm hpq, ite_false, ite_true] using outB z
  have getOld (z a : Fin n) (hap : a ≠ p) (haq : a ≠ q) :
      views next (some z) (w' a) = views gs (some z) (w a) := by
    simpa only [w', hap, haq, ite_false] using oldValue z a
  refine ⟨next, w', nextLen, ?_, ?_, ?_⟩
  · intro g hm
    change g ∈ (gs ++ [ga]) ++ [gb] at hm
    simp only [List.mem_append, List.mem_singleton] at hm
    rcases hm with (ho | rfl) | rfl
    · exact hg g ho
    · exact ⟨rfl, rfl⟩
    · exact ⟨rfl, rfl⟩
  · intro a
    have h := hw a
    rw [nextLen]
    by_cases ep : a = p
    · simp [w', ep, o]
    · by_cases eq : a = q
      · subst a
        simp [w', Ne.symm hpq, o, Nat.add_assoc]
      · simp only [w', ep, eq, ite_false]
        omega
  · intro z j
    constructor
    · intro h
      obtain ⟨a, ha, hj, truth⟩ := (hc z j).mp h
      by_cases e : a = i
      · subst a
        have hm : j ∈ F p ∪ F q := by rwa [hu]
        rcases Finset.mem_union.mp hm with hm | hm
        · refine ⟨p, Finset.mem_erase.mpr ⟨hpi, hp⟩, hm, ?_⟩
          rw [getP]; simp [truth]
        · refine ⟨q, Finset.mem_erase.mpr ⟨hqi, hq⟩, hm, ?_⟩
          rw [getQ]; simp [truth]
      · refine ⟨a, Finset.mem_erase.mpr ⟨e, ha⟩, hj, ?_⟩
        by_cases ep : a = p
        · subst a; rw [getP]; simp [truth]
        · by_cases eq : a = q
          · subst a; rw [getQ]; simp [truth]
          · rw [getOld z a ep eq]; exact truth
    · rintro ⟨a, ha, hj, truth⟩
      have haA : a ∈ A := (Finset.mem_erase.mp ha).2
      apply (hc z j).mpr
      by_cases ep : a = p
      · subst a
        rw [getP] at truth
        simp at truth
        rcases truth with h | h
        · exact ⟨p, hp, hj, h⟩
        · exact ⟨i, hi, hps.subset hj, h⟩
      · by_cases eq : a = q
        · subst a
          rw [getQ] at truth
          simp at truth
          rcases truth with h | h
          · exact ⟨q, hq, hj, h⟩
          · exact ⟨i, hi, hqs.subset hj, h⟩
        · exact ⟨a, haA, hj, (getOld z a ep eq) ▸ truth⟩


def large {n k : ℕ} (F : Fin n → Finset (Fin k)) (A : Finset (Fin n)) :
    Finset (Fin n) := A.filter (fun i => 2 ≤ (F i).card)

def downward {n k : ℕ} (F : Fin n → Finset (Fin k)) (A : Finset (Fin n)) : Prop :=
  ∀ a ∈ A, ∀ z, F z ⊂ F a → z ∈ A

set_option maxHeartbeats 1500000 in
lemma finish {n k : ℕ} (F : Fin n → Finset (Fin k))
    (hf : Function.Injective F) (single : ∀ j : Fin k, ∃ i, F i = {j})
    (join : ∀ i, 2 ≤ (F i).card → ∃ p q : Fin n, F p ⊂ F i ∧ F q ⊂ F i ∧ F p ∪ F q = F i) :
    ∀ (m : ℕ) (A : Finset (Fin n)) (gs : List Gate) (w : Fin n → ℕ),
      (large F A).card = m → downward F A →
      (∀ a, (F a).card ≤ 1 → a ∈ A) →
      orGates gs → (∀ a, w a < n + gs.length) → covers F A gs w →
      ∃ C : Circuit, encoder F C ∧ orGates C.gates ∧ C.gates.length = gs.length + 2*m := by
  classical
  intro m
  induction m using Nat.strong_induction_on with
  | ind m ih =>
    intro A gs w hm hdown hsmall hgs hw hcov
    by_cases hlarge : (large F A).Nonempty
    · obtain ⟨i, hbig, maximal⟩ := Finset.exists_max_image (large F A) (fun a => (F a).card) hlarge
      obtain ⟨hi, hsize⟩ := Finset.mem_filter.mp hbig
      obtain ⟨p, q, hp, hq, union⟩ := join i hsize
      obtain ⟨gs', w', hlength, hor, hw', hcov'⟩ := extend F A gs w i p q hi
        (hdown i hi p hp) (hdown i hi q hq) hp hq union hgs hw hcov
      have hd' : downward F (A.erase i) := by
        intro a ha z hz
        have hA : a ∈ A := (Finset.mem_erase.mp ha).2
        refine Finset.mem_erase.mpr ⟨?_, hdown a hA z hz⟩
        intro hz'
        subst z
        have hinc := Finset.card_lt_card hz
        have hbigA : a ∈ large F A := Finset.mem_filter.mpr ⟨hA, by omega⟩
        exact (not_lt_of_ge (maximal a hbigA)) hinc
      have hs' : ∀ a, (F a).card ≤ 1 → a ∈ A.erase i := by
        intro a ha
        refine Finset.mem_erase.mpr ⟨?_, hsmall a ha⟩
        intro eq
        subst a
        omega
      have hErase : large F (A.erase i) = (large F A).erase i := by
        ext a
        simp [large, and_assoc, and_comm, and_left_comm]
      have hcount : (large F (A.erase i)).card + 1 = m := by
        rw [hErase, ← hm]
        exact Finset.card_erase_add_one hbig
      obtain ⟨C, hC, hOr, hLen⟩ := ih (large F (A.erase i)).card (by omega)
        (A.erase i) gs' w' rfl hd' hs' hor hw' hcov'
      refine ⟨C, hC, hOr, ?_⟩
      rw [hLen, hlength]
      omega
    · have absent : large F A = ∅ := Finset.not_nonempty_iff_eq_empty.mp hlarge
      have hm0 : m = 0 := by rw [← hm, absent]; simp
      refine ⟨⟨gs, 0⟩, ?_, hgs, by simp [hm0]⟩
      intro j
      obtain ⟨p, hp⟩ := single j
      have hpA : p ∈ A := hsmall p (by simp [hp])
      refine ⟨w p, ?_⟩
      intro i
      change views gs (some i) (w p) = decide (j ∈ F i)
      by_cases hji : j ∈ F i
      · obtain ⟨a, ha, hj, trueAt⟩ := (hcov i j).mp hji
        have hs : (F a).card ≤ 1 := by
          by_contra bad
          exact hlarge ⟨a, Finset.mem_filter.mpr ⟨ha, by omega⟩⟩
        have sub : ({j} : Finset (Fin k)) ⊆ F a := Finset.singleton_subset_iff.mpr hj
        have he : ({j} : Finset (Fin k)) = F a :=
          Finset.eq_of_subset_of_card_le sub (by simpa using hs)
        have same : a = p := hf (he.symm.trans hp.symm)
        simpa [hji, same] using trueAt
      · cases hview : views gs (some i) (w p) with
        | false => simp [hji]
        | true => exact (hji ((hcov i j).mpr ⟨p, hpA, by simp [hp], hview⟩)).elim

set_option maxHeartbeats 1000000 in
lemma largeCard {n k : ℕ} (F : Fin n → Finset (Fin k)) (hf : Function.Injective F)
    (empty : ∃ i, F i = ∅) (single : ∀ j : Fin k, ∃ i, F i = {j}) :
    (large F (Finset.univ : Finset (Fin n))).card + (k + 1) = n := by
  classical
  obtain ⟨e, he⟩ := empty
  choose s hs using single
  let pick : Option (Fin k) → Fin n
    | none => e
    | some j => s j
  have hpick : Function.Injective pick := by
    intro a b hab
    cases a <;> cases b <;> simpa [pick, he, hs] using congrArg F hab
  let small : Finset (Fin n) := Finset.univ.filter (fun i => ¬ 2 ≤ (F i).card)
  have hSmall : small = Finset.univ.image pick := by
    ext i
    constructor
    · intro hi
      have hi' := (Finset.mem_filter.mp hi).2
      by_cases hzero : (F i).card = 0
      · have he' : F i = ∅ := Finset.card_eq_zero.mp hzero
        exact Finset.mem_image.mpr ⟨none, by simp, hf (by simpa [pick, he] using he'.symm)⟩
      · have hOne : (F i).card = 1 := by omega
        obtain ⟨j, hj⟩ := Finset.card_eq_one.mp hOne
        exact Finset.mem_image.mpr ⟨some j, by simp, hf (by simpa [pick, hs] using hj.symm)⟩
    · intro hi
      obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hi
      cases a <;> simp [small, pick, he, hs]
  have hSmallCard : small.card = k + 1 := by
    rw [hSmall, Finset.card_image_of_injective _ hpick]
    simp
  have htotal := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin n)))
    (fun i : Fin n => 2 ≤ (F i).card)
  change (large F Finset.univ).card + small.card = (Finset.univ : Finset (Fin n)).card at htotal
  simpa [hSmallCard] using htotal

lemma upperBound {n k : ℕ} (F : Fin n → Finset (Fin k)) (hf : Function.Injective F)
    (empty : ∃ i, F i = ∅) (single : ∀ j : Fin k, ∃ i, F i = {j})
    (join : ∀ i, 2 ≤ (F i).card → ∃ p q : Fin n, F p ⊂ F i ∧ F q ⊂ F i ∧ F p ∪ F q = F i)
    (b : ℕ) (bound : 2*n ≤ b + 2*k + 2) :
    ∃ C : Circuit, encoder F C ∧ orGates C.gates ∧ C.size ≤ b := by
  have hstart : covers F Finset.univ [] Fin.val := by
    intro z j
    constructor
    · intro h
      exact ⟨z, by simp, h, by rw [rawHot z z.isLt]; simp⟩
    · rintro ⟨a, _, hmem, htrue⟩
      rw [rawHot z a.isLt] at htrue
      simp at htrue
      simpa [htrue] using hmem
  obtain ⟨C, henc, hOr, hLen⟩ := finish F hf single join
    (large F Finset.univ).card Finset.univ [] Fin.val rfl (by simp [downward])
    (by simp) (by simp [orGates]) (fun i => by simp) hstart
  have htotal := largeCard F hf empty single
  refine ⟨C, henc, hOr, ?_⟩
  change C.gates.length ≤ b
  simp only [List.length_nil, zero_add] at hLen
  omega


end PEqualNP.Outside.L_meta_27463

open PEqualNP.Outside.L_meta_27463

theorem PEqualNP.Outside.L_meta_27463 : (∀ (n k : ℕ) (F : Fin n → Finset (Fin k)), Function.Injective F →
  (∃ i, F i = ∅) → (∀ j : Fin k, ∃ i, F i = {j}) →
  (∀ i, 2 ≤ (F i).card → ∃ p q : Fin n,
    F p ⊂ F i ∧ F q ⊂ F i ∧ F p ∪ F q = F i) →
  let enc := fun C : PEqualNP.CircuitLowerBounds.Circuit =>
    ∀ j : Fin k, ∃ w : ℕ, ∀ i : Fin n,
      (C.wires (List.ofFn (fun h : Fin n => decide (h = i)))).getD w false = decide (j ∈ F i)
  ∀ b : ℕ,
    ((∃ C : PEqualNP.CircuitLowerBounds.Circuit, enc C ∧
      (∀ g ∈ C.gates, g.inputs.length ≤ 2) ∧
      C.gates.countP (fun g => decide (g.inputs.length = 2)) ≤ b) ↔ 2*n ≤ b + 2*k + 2) ∧
    ((∃ E : PEqualNP.CircuitLowerBounds.Circuit, enc E ∧
      (∀ g ∈ E.gates, g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ g.inputs.length ≤ 2) ∧
      E.size ≤ b) ↔ 2*n ≤ b + 2*k + 2)) := by
  intro n k F hf he hs hj
  dsimp only
  intro b
  constructor
  · constructor
    · rintro ⟨C, hEnc, hFan, hCap⟩
      have h := lowerBound F hf C hEnc hFan
      change binaryCount C.gates ≤ b at hCap
      omega
    · intro bound
      obtain ⟨C, hEnc, hOr, hSize⟩ := upperBound F hf he hs hj b bound
      refine ⟨C, hEnc, fun g hg => (hOr g hg).2.le, ?_⟩
      exact (binaryLe C.gates).trans hSize
  · constructor
    · rintro ⟨C, hEnc, hOr, hSize⟩
      have h := lowerBound F hf C hEnc (fun g hg => (hOr g hg).2)
      have hc : binaryCount C.gates ≤ b := (binaryLe C.gates).trans hSize
      omega
    · intro bound
      obtain ⟨C, hEnc, hOr, hSize⟩ := upperBound F hf he hs hj b bound
      exact ⟨C, hEnc, fun g hg => ⟨(hOr g hg).1, (hOr g hg).2.le⟩, hSize⟩
