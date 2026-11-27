import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_808_aux

open PEqualNP.MetaComplexity Finset

def leaves {n : ℕ} : DMFormula n → Finset (Fin n)
  | .lit i _ => {i}
  | .and a b | .or a b => leaves a ∪ leaves b

def readOnce {n : ℕ} : DMFormula n → Prop
  | .lit _ b => b = true
  | .and a b | .or a b => readOnce a ∧ readOnce b ∧ Disjoint (leaves a) (leaves b)

def value {n : ℕ} (f : DMFormula n) (s : Finset (Fin n)) : Bool :=
  f.eval (fun i => decide (i ∈ s))

theorem value_congr {n : ℕ} (f : DMFormula n) {s t : Finset (Fin n)}
    (same : ∀ i ∈ leaves f, i ∈ s ↔ i ∈ t) : value f s = value f t := by
  induction f with
  | lit i b =>
    have hi := same i (by simp [leaves])
    simp [value, DMFormula.eval, hi]
  | and a b ihA ihB =>
    have ha := ihA (fun i hi => same i (by simp [leaves, hi]))
    have hb := ihB (fun i hi => same i (by simp [leaves, hi]))
    show (value a s && value b s) = (value a t && value b t)
    rw [ha, hb]
  | or a b ihA ihB =>
    have ha := ihA (fun i hi => same i (by simp [leaves, hi]))
    have hb := ihB (fun i hi => same i (by simp [leaves, hi]))
    show (value a s || value b s) = (value a t || value b t)
    rw [ha, hb]

theorem value_mono {n : ℕ} (f : DMFormula n) (rf : readOnce f) {s t : Finset (Fin n)}
    (sub : s ⊆ t) (yes : value f s = true) : value f t = true := by
  induction f with
  | lit i b =>
    have h : b = true := rf
    subst b
    simp only [value, DMFormula.eval, ite_true, decide_eq_true_eq] at yes ⊢
    exact sub yes
  | and a b ihA ihB =>
    obtain ⟨ra, rb, -⟩ := rf
    change (value a s && value b s) = true at yes
    change (value a t && value b t) = true
    simp only [Bool.and_eq_true] at yes ⊢
    exact ⟨ihA ra yes.1, ihB rb yes.2⟩
  | or a b ihA ihB =>
    obtain ⟨ra, rb, -⟩ := rf
    change (value a s || value b s) = true at yes
    change (value a t || value b t) = true
    simp only [Bool.or_eq_true] at yes ⊢
    exact yes.imp (ihA ra) (ihB rb)

theorem value_empty {n : ℕ} (f : DMFormula n) (rf : readOnce f) : value f ∅ = false := by
  induction f with
  | lit i b =>
    have h : b = true := rf
    simp [value, DMFormula.eval, h]
  | and a b ihA ihB =>
    show (value a ∅ && value b ∅) = false
    simp [ihA rf.1, ihB rf.2.1]
  | or a b ihA ihB =>
    show (value a ∅ || value b ∅) = false
    simp [ihA rf.1, ihB rf.2.1]

theorem value_insert_skip {n : ℕ} (f : DMFormula n) (s : Finset (Fin n)) {i : Fin n}
    (no : i ∉ leaves f) : value f (insert i s) = value f s := by
  apply value_congr
  intro j hj
  have ne : j ≠ i := fun h => no (h ▸ hj)
  simp [ne]

def pairAt {n : ℕ} (f : DMFormula n) (s : Finset (Fin n)) (a b : Fin n) : Bool :=
  value f (insert a (insert b s))

theorem pair_comm {n : ℕ} (f : DMFormula n) (s : Finset (Fin n)) (a b : Fin n) :
    pairAt f s a b = pairAt f s b a := by
  unfold pairAt
  rw [insert_comm]

theorem pair_skip_left {n : ℕ} (f : DMFormula n) (s : Finset (Fin n)) {a b : Fin n}
    (no : a ∉ leaves f) : pairAt f s a b = value f (insert b s) := value_insert_skip f _ no

theorem pair_skip_right {n : ℕ} (f : DMFormula n) (s : Finset (Fin n)) {a b : Fin n}
    (no : b ∉ leaves f) : pairAt f s a b = value f (insert a s) := by
  rw [pair_comm f s a b]
  exact pair_skip_left f s no

theorem pair_support {n : ℕ} (f : DMFormula n) (s : Finset (Fin n)) {a b : Fin n}
    (oneA : value f (insert a s) = false) (oneB : value f (insert b s) = false)
    (yes : pairAt f s a b = true) : a ∈ leaves f ∧ b ∈ leaves f := by
  constructor
  · by_contra no
    rw [pair_skip_left f s no, oneB] at yes
    contradiction
  · by_contra no
    rw [pair_skip_right f s no, oneA] at yes
    contradiction

theorem pair_split {n : ℕ} (a b : DMFormula n) (s : Finset (Fin n)) {i j : Fin n}
    (sep : Disjoint (leaves a) (leaves b)) (emptyA : value a s = false)
    (emptyB : value b s = false) (ha : pairAt a s i j = true) (hb : pairAt b s i j = true) :
    ((i ∈ leaves a ∧ j ∈ leaves b) ∧
      value a (insert i s) = true ∧ value b (insert j s) = true) ∨
    ((j ∈ leaves a ∧ i ∈ leaves b) ∧
      value a (insert j s) = true ∧ value b (insert i s) = true) := by
  have need : ∀ f : DMFormula n, value f s = false → pairAt f s i j = true →
      i ∈ leaves f ∨ j ∈ leaves f := by
    intro f hf ht
    by_contra! h
    rw [pair_skip_left f s h.1, value_insert_skip f s h.2, hf] at ht
    contradiction
  have apart := disjoint_left.1 sep
  rcases need a emptyA ha with ia | ja
  · have ib : i ∉ leaves b := fun hi => apart ia hi
    have jb : j ∈ leaves b := (need b emptyB hb).resolve_left ib
    have jna : j ∉ leaves a := fun hj => apart hj jb
    refine Or.inl ⟨⟨ia, jb⟩, ?_, ?_⟩
    · simpa only [pair_skip_right a s jna] using ha
    · simpa only [pair_skip_left b s ib] using hb
  · have jb : j ∉ leaves b := fun hj => apart ja hj
    have ib : i ∈ leaves b := (need b emptyB hb).resolve_right jb
    have ina : i ∉ leaves a := fun hi => apart hi ib
    refine Or.inr ⟨⟨ja, ib⟩, ?_, ?_⟩
    · simpa only [pair_skip_left a s ina] using ha
    · simpa only [pair_skip_right b s jb] using hb

theorem single_into_pair {n : ℕ} (p : Finset (Fin n)) (i j : Fin n) :
    insert i p ⊆ insert i (insert j p) := by
  intro z hz
  rcases mem_insert.1 hz with rfl | hz
  · exact mem_insert_self _ _
  · exact mem_insert_of_mem (mem_insert_of_mem hz)

theorem second_into_pair {n : ℕ} (p : Finset (Fin n)) (i j : Fin n) :
    insert j p ⊆ insert i (insert j p) := subset_insert _ _

theorem cross_rectangle {α : Type} {A B : α → Prop}
    (apart : ∀ i, A i → B i → False) {a b c d : α}
    (ab : (A a ∧ B b) ∨ (A b ∧ B a))
    (cb : (A c ∧ B b) ∨ (A b ∧ B c))
    (cd : (A c ∧ B d) ∨ (A d ∧ B c)) : (A a ∧ B d) ∨ (A d ∧ B a) := by
  rcases ab with ⟨aa, bb⟩ | ⟨ba, ab⟩
  · have ac : A c := cb.elim And.left fun h => False.elim (apart b h.1 bb)
    have bd : B d := cd.elim And.right fun h => False.elim (apart c ac h.2)
    exact Or.inl ⟨aa, bd⟩
  · have bc : B c := cb.elim (fun h => False.elim (apart b ba h.2)) And.right
    have ad : A d := cd.elim (fun h => False.elim (apart c h.1 bc)) And.left
    exact Or.inr ⟨ad, ab⟩

theorem pair_and_rectangle {n : ℕ} (f g : DMFormula n) (p : Finset (Fin n))
    (rf : readOnce f) (rg : readOnce g) (sep : Disjoint (leaves f) (leaves g))
    (zeroF : value f p = false) (zeroG : value g p = false) {a b c d : Fin n}
    (ab : (pairAt f p a b && pairAt g p a b) = true)
    (cb : (pairAt f p c b && pairAt g p c b) = true)
    (cd : (pairAt f p c d && pairAt g p c d) = true) :
    (pairAt f p a d && pairAt g p a d) = true := by
  let A := fun i => i ∈ leaves f ∧ value f (insert i p) = true
  let B := fun i => i ∈ leaves g ∧ value g (insert i p) = true
  have apart (i : Fin n) (a : A i) (b : B i) : False := disjoint_left.1 sep a.1 b.1
  have edges (i j : Fin n) (h : (pairAt f p i j && pairAt g p i j) = true) :
      (A i ∧ B j) ∨ (A j ∧ B i) := by
    simp only [Bool.and_eq_true] at h
    rcases pair_split f g p sep zeroF zeroG h.1 h.2 with ⟨⟨hi, hj⟩, hx, hy⟩ | ⟨⟨hj, hi⟩, hy, hx⟩
    · exact Or.inl ⟨⟨hi, hx⟩, ⟨hj, hy⟩⟩
    · exact Or.inr ⟨⟨hj, hy⟩, ⟨hi, hx⟩⟩
  simp only [Bool.and_eq_true]
  rcases cross_rectangle apart (edges a b ab) (edges c b cb) (edges c d cd) with ⟨hA, hB⟩ | ⟨hA, hB⟩
  · exact ⟨value_mono f rf (single_into_pair p a d) hA.2, value_mono g rg (second_into_pair p a d) hB.2⟩
  · exact ⟨value_mono f rf (second_into_pair p a d) hA.2, value_mono g rg (single_into_pair p a d) hB.2⟩

theorem or_false_parts (a b : Bool) (h : (a || b) = false) : a = false ∧ b = false := by
  cases a <;> cases b <;> simp_all

theorem or_in_branch {n : ℕ} (f g : DMFormula n) (p : Finset (Fin n))
    (sep : Disjoint (leaves f) (leaves g)) {i j : Fin n}
    (ni : value g (insert i p) = false) (nj : value g (insert j p) = false)
    (here : i ∈ leaves f ∨ j ∈ leaves f)
    (yes : (pairAt f p i j || pairAt g p i j) = true) : pairAt f p i j = true := by
  simp only [Bool.or_eq_true] at yes
  rcases yes with yes | yes
  · exact yes
  · obtain ⟨hi, hj⟩ := pair_support g p ni nj yes
    exact False.elim (here.elim (fun x => disjoint_left.1 sep x hi)
      (fun x => disjoint_left.1 sep x hj))

theorem pair_rectangle {n : ℕ} (f : DMFormula n) (p : Finset (Fin n)) (K : Fin n → Prop)
    (rf : readOnce f) (initial : value f p = false)
    (neutral : ∀ i, K i → value f (insert i p) = false) :
    ∀ a b c d, K a → K b → K c → K d →
      pairAt f p a b = true → pairAt f p c b = true → pairAt f p c d = true → pairAt f p a d = true := by
  induction f with
  | lit j flag =>
    intro a b c d ha hb _ _ hit _ _
    have pos : flag = true := rf
    have hm : j ∈ insert a (insert b p) := by simpa [pairAt, value, DMFormula.eval, pos] using hit
    have na : j ∉ insert a p := by simpa [value, DMFormula.eval, pos] using neutral a ha
    have nb : j ∉ insert b p := by simpa [value, DMFormula.eval, pos] using neutral b hb
    rcases mem_insert.1 hm with rfl | hb
    · exact False.elim (na (mem_insert_self _ _))
    · exact False.elim (nb hb)
  | and f g ihf ihg =>
    intro a b c d ha hb hc hd ab cb cd
    obtain ⟨rf, rg, sep⟩ := rf
    change (value f p && value g p) = false at initial
    change (pairAt f p a b && pairAt g p a b) = true at ab
    change (pairAt f p c b && pairAt g p c b) = true at cb
    change (pairAt f p c d && pairAt g p c d) = true at cd
    change (pairAt f p a d && pairAt g p a d) = true
    cases hf : value f p
    · cases hg : value g p
      · exact pair_and_rectangle f g p rf rg sep hf hg ab cb cd
      · have nf : ∀ i, K i → value f (insert i p) = false := by
          intro i hi
          have h := neutral i hi
          change (value f (insert i p) && value g (insert i p)) = false at h
          simpa [value_mono g rg (subset_insert _ _) hg] using h
        simp only [Bool.and_eq_true] at ab cb cd ⊢
        exact ⟨ihf rf hf nf a b c d ha hb hc hd ab.1 cb.1 cd.1,
          value_mono g rg ((subset_insert _ _).trans (subset_insert _ _)) hg⟩
    · have hg : value g p = false := by simpa [hf] using initial
      have ng : ∀ i, K i → value g (insert i p) = false := by
        intro i hi
        have h := neutral i hi
        change (value f (insert i p) && value g (insert i p)) = false at h
        simpa [value_mono f rf (subset_insert _ _) hf] using h
      simp only [Bool.and_eq_true] at ab cb cd ⊢
      exact ⟨value_mono f rf ((subset_insert _ _).trans (subset_insert _ _)) hf,
        ihg rg hg ng a b c d ha hb hc hd ab.2 cb.2 cd.2⟩
  | or f g ihf ihg =>
    intro a b c d ha hb hc hd ab cb cd
    obtain ⟨rf, rg, sep⟩ := rf
    change (value f p || value g p) = false at initial
    obtain ⟨hf, hg⟩ := or_false_parts _ _ initial
    have small (i : Fin n) (hi : K i) :
        value f (insert i p) = false ∧ value g (insert i p) = false :=
      or_false_parts _ _ (neutral i hi)
    change (pairAt f p a b || pairAt g p a b) = true at ab
    change (pairAt f p c b || pairAt g p c b) = true at cb
    change (pairAt f p c d || pairAt g p c d) = true at cd
    change (pairAt f p a d || pairAt g p a d) = true
    simp only [Bool.or_eq_true] at ab ⊢
    rcases ab with ab | ab
    · have ib := (pair_support f p (small a ha).1 (small b hb).1 ab).2
      have fh := or_in_branch f g p sep (small c hc).2 (small b hb).2 (Or.inr ib) cb
      have ic := (pair_support f p (small c hc).1 (small b hb).1 fh).1
      have fk := or_in_branch f g p sep (small c hc).2 (small d hd).2 (Or.inl ic) cd
      exact Or.inl (ihf rf hf (fun i hi => (small i hi).1) a b c d ha hb hc hd ab fh fk)
    · have ib := (pair_support g p (small a ha).2 (small b hb).2 ab).2
      have gh := or_in_branch g f p sep.symm (small c hc).1 (small b hb).1 (Or.inr ib)
        (by simpa only [Bool.or_comm] using cb)
      have ic := (pair_support g p (small c hc).2 (small b hb).2 gh).1
      have gk := or_in_branch g f p sep.symm (small c hc).1 (small d hd).1 (Or.inl ic)
        (by simpa only [Bool.or_comm] using cd)
      exact Or.inr (ihg rg hg (fun i hi => (small i hi).2) a b c d ha hb hc hd ab gh gk)

theorem pair_without_pin {n : ℕ} (f : DMFormula n) {l i j : Fin n}
    (outside : l ∉ leaves f) : pairAt f {l} i j = pairAt f ∅ i j := by
  have reorder : insert i (insert j ({l} : Finset (Fin n))) = insert l (insert i (insert j ∅)) := by
    ext z
    simp only [mem_insert, mem_singleton, notMem_empty, or_false]
    tauto
  unfold pairAt
  rw [reorder, value_insert_skip f _ outside]

theorem or_isolation_branch {n : ℕ} (f g : DMFormula n) {h l p q t i : Fin n}
    (rf : readOnce f) (sep : Disjoint (leaves f) (leaves g))
    (single : ∀ z, value f {z} = false ∧ value g {z} = false)
    (lowQ : value f (insert q {l}) = false ∧ value g (insert q {l}) = false)
    (lowT : value f (insert t {l}) = false ∧ value g (insert t {l}) = false)
    (lowI : value g (insert i {l}) = false)
    (hi : pairAt f ∅ h i = false) (hq : pairAt f ∅ h q = true)
    (lp : (pairAt f ∅ l p || pairAt g ∅ l p) = true)
    (qt : (pairAt f {l} q t || pairAt g {l} q t) = true)
    (sameSide : pairAt f ∅ l p = true → pairAt f {l} q t = true → pairAt f {l} i t = false) :
    (pairAt f {l} i t || pairAt g {l} i t) = false := by
  have fSingle : ∀ z, value f (insert z ∅) = false := fun z => by simpa using (single z).1
  have gSingle : ∀ z, value g (insert z ∅) = false := fun z => by simpa using (single z).2
  have qf := (pair_support f ∅ (fSingle h) (fSingle q) hq).2
  have qtf := or_in_branch f g {l} sep lowQ.2 lowT.2 (Or.inl qf) qt
  have tf := (pair_support f {l} lowQ.1 lowT.1 qtf).2
  have tg : t ∉ leaves g := fun h => disjoint_left.1 sep tf h
  have rit : pairAt g {l} i t = false := (pair_skip_right g {l} tg).trans lowI
  rw [rit, Bool.or_false]
  simp only [Bool.or_eq_true] at lp
  rcases lp with lp | lp
  · exact sameSide lp qtf
  · have lg := (pair_support g ∅ (gSingle l) (gSingle p) lp).1
    have lf : l ∉ leaves f := fun h => disjoint_left.1 sep h lg
    by_contra contra
    have it : pairAt f {l} i t = true := Bool.eq_true_of_not_eq_false contra
    have tq : pairAt f ∅ t q = true := by
      rw [pair_comm f ∅ t q, ← pair_without_pin f lf]
      exact qtf
    have ti : pairAt f ∅ t i = true := by
      rw [pair_comm f ∅ t i, ← pair_without_pin f lf]
      exact it
    have bad := pair_rectangle f ∅ (fun _ => True) rf (value_empty f rf)
      (fun z _ => fSingle z) h q t i trivial trivial trivial trivial hq tq ti
    rw [hi] at bad
    contradiction

theorem and_isolation_branch {n : ℕ} (f g : DMFormula n) {h l p q t : Fin n}
    (rf : readOnce f) (rg : readOnce g) (sep : Disjoint (leaves f) (leaves g))
    (qg : q ∈ leaves g) (hready : value f (insert h ∅) = true)
    (lp : (pairAt f ∅ l p && pairAt g ∅ l p) = true)
    (hp : (pairAt f ∅ h p && pairAt g ∅ h p) = false)
    (lt : (value f (insert t {l}) && value g (insert t {l})) = false)
    (qt : (pairAt f {l} q t && pairAt g {l} q t) = true) : False := by
  simp only [Bool.and_eq_true] at lp qt
  rcases pair_split f g ∅ sep (value_empty f rf) (value_empty g rg) lp.1 lp.2 with
    ⟨_, _, pReady⟩ | ⟨_, _, lReady⟩
  · have hf : pairAt f ∅ h p = true := value_mono f rf (single_into_pair ∅ h p) hready
    have hg : pairAt g ∅ h p = true := value_mono g rg (second_into_pair ∅ h p) pReady
    simp [hf, hg] at hp
  · have qf : q ∉ leaves f := fun h => disjoint_left.1 sep h qg
    have ht : value f (insert t {l}) = true := (pair_skip_left f {l} qf).symm.trans qt.1
    have hsub : insert l (∅ : Finset (Fin n)) ⊆ insert t {l} := subset_insert t {l}
    have hgt := value_mono g rg hsub lReady
    simp [ht, hgt] at lt

theorem pair_isolation {n : ℕ} (f : DMFormula n) (h l p q t i : Fin n)
    (rf : readOnce f) (single : ∀ z, value f {z} = false)
    (hq : pairAt f ∅ h q = true) (lp : pairAt f ∅ l p = true)
    (hp : pairAt f ∅ h p = false) (hi : pairAt f ∅ h i = false)
    (lq : value f (insert q {l}) = false) (lt : value f (insert t {l}) = false)
    (li : value f (insert i {l}) = false) (qt : pairAt f {l} q t = true) :
    pairAt f {l} i t = false := by
  induction f with
  | lit j flag =>
    have pos : flag = true := rf
    have empty := single j
    simp [value, DMFormula.eval, pos] at empty
  | and f g ihf ihg =>
    obtain ⟨rf, rg, sep⟩ := rf
    change (pairAt f ∅ h q && pairAt g ∅ h q) = true at hq
    simp only [Bool.and_eq_true] at hq
    rcases pair_split f g ∅ sep (value_empty f rf) (value_empty g rg) hq.1 hq.2 with
      ⟨⟨_, qg⟩, hf, _⟩ | ⟨⟨qf, _⟩, _, hg⟩
    · exact False.elim (and_isolation_branch f g rf rg sep qg hf lp hp lt qt)
    · change (pairAt f ∅ l p && pairAt g ∅ l p) = true at lp
      change (pairAt f ∅ h p && pairAt g ∅ h p) = false at hp
      change (value f (insert t {l}) && value g (insert t {l})) = false at lt
      change (pairAt f {l} q t && pairAt g {l} q t) = true at qt
      exact False.elim (and_isolation_branch g f rg rf sep.symm qf hg
        (by simpa only [Bool.and_comm] using lp) (by simpa only [Bool.and_comm] using hp)
        (by simpa only [Bool.and_comm] using lt) (by simpa only [Bool.and_comm] using qt))
  | or f g ihf ihg =>
    obtain ⟨rf, rg, sep⟩ := rf
    have singles (z : Fin n) : value f {z} = false ∧ value g {z} = false := or_false_parts _ _ (single z)
    have nHP : pairAt f ∅ h p = false ∧ pairAt g ∅ h p = false := or_false_parts _ _ hp
    have nHI : pairAt f ∅ h i = false ∧ pairAt g ∅ h i = false := or_false_parts _ _ hi
    have nQ : value f (insert q {l}) = false ∧ value g (insert q {l}) = false := or_false_parts _ _ lq
    have nT : value f (insert t {l}) = false ∧ value g (insert t {l}) = false := or_false_parts _ _ lt
    have nI : value f (insert i {l}) = false ∧ value g (insert i {l}) = false := or_false_parts _ _ li
    change (pairAt f ∅ h q || pairAt g ∅ h q) = true at hq
    change (pairAt f ∅ l p || pairAt g ∅ l p) = true at lp
    change (pairAt f {l} q t || pairAt g {l} q t) = true at qt
    change (pairAt f {l} i t || pairAt g {l} i t) = false
    simp only [Bool.or_eq_true] at hq
    rcases hq with hq | hq
    · exact or_isolation_branch f g rf sep singles nQ nT nI.2 nHI.1 hq lp qt
        (fun hLP hQT => ihf rf (fun z => (singles z).1) hq hLP nHP.1 nHI.1 nQ.1 nT.1 nI.1 hQT)
    · rw [Bool.or_comm]
      exact or_isolation_branch g f rg sep.symm (fun z => (singles z).symm) nQ.symm nT.symm nI.1 nHI.2 hq
        (by simpa only [Bool.or_comm] using lp) (by simpa only [Bool.or_comm] using qt)
        (fun hLP hQT => ihg rg (fun z => (singles z).2) hq hLP nHP.2 nHI.2 nQ.2 nT.2 nI.2 hQT)



open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover

theorem getD_snoc_old {α : Type} (xs : List α) (x d : α) {w : ℕ} (hw : w < xs.length) :
    (xs ++ [x]).getD w d = xs.getD w d := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hw]

theorem getD_snoc_last {α : Type} (xs : List α) (x d : α) :
    (xs ++ [x]).getD xs.length d = x := by
  simp [List.getD_eq_getElem?_getD]

theorem getD_map_of_lt {α β : Type} (xs : List α) (f : α → β) (d : α) (e : β)
    {w : ℕ} (hw : w < xs.length) : (xs.map f).getD w e = f (xs.getD w d) := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hw]

def defaultGate : Gate := ⟨.or, []⟩

theorem count_reads (gs : List Gate) (w : ℕ) :
    (gs.flatMap Gate.inputs).count w = ∑ j ∈ range gs.length, ((gs.getD j defaultGate).inputs.count w) := by
  induction gs using List.reverseRecOn with
  | nil => simp
  | append_singleton gs g ih =>
    simp only [List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil,
      List.count_append, List.length_append, List.length_singleton, sum_range_succ]
    rw [ih, getD_snoc_last]
    congr 1
    apply sum_congr rfl
    intro j hj
    rw [getD_snoc_old gs g defaultGate (mem_range.1 hj)]

def composeGate {n : ℕ} (op : GateOp) (a b : DMFormula n) : DMFormula n :=
  match op with
  | .and => .and a b
  | _ => .or a b

def stepValues (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

/-- After each gate, the formulas of the unconsumed wires have disjoint supports. -/
theorem compile_prefix {n : ℕ} (seed : DMFormula n) (gs : List Gate)
    (binary : ∀ g ∈ gs, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length = 2)
    (back : ∀ j < gs.length, ∀ w ∈ (gs.getD j defaultGate).inputs, w < n+j)
    (once : ∀ w, (gs.flatMap Gate.inputs).count w ≤ 1) :
    ∃ xs : List (DMFormula n), xs.length = n + gs.length ∧
      (∀ s : Finset (Fin n), xs.map (fun f => value f s) =
        gs.foldl stepValues (List.ofFn (fun i : Fin n => decide (i ∈ s)))) ∧
      (∀ w < xs.length, readOnce (xs.getD w seed)) ∧
      ∀ w v, w < xs.length → v < xs.length → w ≠ v →
        w ∉ gs.flatMap Gate.inputs → v ∉ gs.flatMap Gate.inputs →
        Disjoint (leaves (xs.getD w seed)) (leaves (xs.getD v seed)) := by
  induction gs using List.reverseRecOn with
  | nil =>
    let xs := List.ofFn (fun i : Fin n => DMFormula.lit i true)
    have atInput (w : ℕ) (hw : w < xs.length) :
        xs.getD w seed = .lit ⟨w, by simpa [xs] using hw⟩ true := by
      have hn : w < n := by simpa [xs] using hw
      simp [xs, List.getD_eq_getElem?_getD, hn]
    refine ⟨xs, by simp [xs], ?_, ?_, ?_⟩
    · intro s
      simp only [xs, List.map_ofFn, List.foldl_nil]
      rfl
    · intro w hw
      simp only [atInput w hw, readOnce]
    · intro w v hw hv diff _ _
      rw [atInput w hw, atInput v hv, leaves, leaves]
      exact disjoint_singleton.2 (fun heq => diff (congrArg Fin.val heq))
  | append_singleton gs g ih =>
    have gb := binary g (by simp)
    obtain ⟨a, b, operands⟩ := List.length_eq_two.1 gb.2
    have prevBack : ∀ j < gs.length, ∀ w ∈ (gs.getD j defaultGate).inputs, w < n+j := by
      intro j hj w hw
      exact back j (by simp; omega) w (by simpa only [getD_snoc_old gs g defaultGate hj] using hw)
    have allCount (w : ℕ) : (gs.flatMap Gate.inputs).count w + [a,b].count w ≤ 1 := by
      simpa [List.flatMap_append, List.count_append, operands] using once w
    obtain ⟨xs, hx, sound, read, apart⟩ := ih
      (fun h hg => binary h (List.mem_append_left _ hg)) prevBack (fun w => by have := allCount w; omega)
    have gback : ∀ w ∈ g.inputs, w < xs.length := by
      intro w hw
      rw [hx]
      exact back gs.length (by simp) w (by simpa using hw)
    have ha : a < xs.length := gback _ (by simp [operands])
    have hb : b < xs.length := gback _ (by simp [operands])
    have noOld (w : ℕ) (h : w ∈ ([a,b] : List ℕ)) : w ∉ gs.flatMap Gate.inputs := by
      intro old
      have h1 := List.count_pos_iff.2 h
      have h2 := List.count_pos_iff.2 old
      have h3 := allCount w
      omega
    have ab : a ≠ b := by
      intro heq
      subst b
      have h := allCount a
      simp at h
    have oldA : a ∉ gs.flatMap Gate.inputs := noOld _ (by simp)
    have oldB : b ∉ gs.flatMap Gate.inputs := noOld _ (by simp)
    let c := composeGate g.op (xs.getD a seed) (xs.getD b seed)
    have hc : readOnce c ∧ leaves c = leaves (xs.getD a seed) ∪ leaves (xs.getD b seed) := by
      rcases gb.1 with hop | hop <;>
        (simp only [c, composeGate, hop, readOnce, leaves];
          exact ⟨⟨read a ha, read b hb, apart a b ha hb ab oldA oldB⟩, trivial⟩)
    have before (w : ℕ) (h : w ∉ (gs ++ [g]).flatMap Gate.inputs) :
        w ∉ gs.flatMap Gate.inputs ∧ w ≠ a ∧ w ≠ b := by
      simpa [List.flatMap_append, operands, not_or] using h
    have cross (w : ℕ) (hw : w < xs.length) (h : w ∉ (gs ++ [g]).flatMap Gate.inputs) :
        Disjoint (leaves (xs.getD w seed)) (leaves c) := by
      rw [hc.2, disjoint_union_right]
      obtain ⟨old, wa, wb⟩ := before w h
      exact ⟨apart w a hw ha wa old oldA, apart w b hw hb wb old oldB⟩
    refine ⟨xs ++ [c], by simp [hx, Nat.add_assoc], ?_, ?_, ?_⟩
    · intro s
      rw [List.map_append, List.foldl_append, ← sound s]
      simp only [List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil, stepValues]
      congr 1
      rw [operands]
      simp only [List.map_cons, List.map_nil, getD_map_of_lt xs _ seed false ha,
        getD_map_of_lt xs _ seed false hb]
      rcases gb.1 with hop | hop <;> simp [c, composeGate, hop, value, DMFormula.eval, GateOp.eval]
    · intro w hw
      by_cases old : w < xs.length
      · rw [getD_snoc_old xs c seed old]
        exact read w old
      · have last : w = xs.length := by simp at hw; omega
        subst w
        simpa only [getD_snoc_last] using hc.1
    · intro w v hw hv ne nw nv
      by_cases ow : w < xs.length
      · rw [getD_snoc_old xs c seed ow]
        by_cases ov : v < xs.length
        · rw [getD_snoc_old xs c seed ov]
          exact apart w v ow ov ne (before w nw).1 (before v nv).1
        · have last : v = xs.length := by simp at hv; omega
          subst v
          simpa only [getD_snoc_last] using cross w ow nw
      · have last : w = xs.length := by simp at hw; omega
        subst w
        have ov : v < xs.length := by simp at hv; omega
        rw [getD_snoc_last, getD_snoc_old xs c seed ov]
        exact (cross v ov nv).symm

theorem formula_of_circuit {n : ℕ} (seed : DMFormula n) (F : Circuit)
    (binary : ∀ g ∈ F.gates, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length = 2)
    (back : ReadsBack n F) (out : F.output < n + F.size)
    (once : ∀ w, readsIn F (range F.size) w ≤ 1) :
    ∃ f : DMFormula n, readOnce f ∧ ∀ s : Finset (Fin n),
      value f s = F.eval (List.ofFn (fun i : Fin n => decide (i ∈ s))) := by
  have counts (w : ℕ) : (F.gates.flatMap Gate.inputs).count w ≤ 1 := by
    rw [count_reads]
    exact once w
  obtain ⟨xs, hx, sound, read, -⟩ := compile_prefix seed F.gates binary back counts
  have hw : F.output < xs.length := by simpa only [hx, Circuit.size] using out
  refine ⟨xs.getD F.output seed, read F.output hw, ?_⟩
  intro s
  change value (xs.getD F.output seed) s =
    (F.gates.foldl stepValues (List.ofFn fun i : Fin n => decide (i ∈ s))).getD F.output false
  rw [← sound s, getD_map_of_lt xs _ seed false hw]

end PEqualNP.Outside.L_lib_808_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.Outside.L_lib_808_aux in
theorem PEqualNP.Outside.L_lib_808 :
∀ (N : Nat) (F : PEqualNP.CircuitLowerBounds.Circuit) (x : Fin 4 ↪ Fin N),
  let tree := fun D : PEqualNP.CircuitLowerBounds.Circuit =>
    (∀ g ∈ D.gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length = 2) ∧
    PEqualNP.MetaComplexity.NestedCover.ReadsBack N D ∧
    (D.output + 1 = N + D.size ∨ (D.size = 0 ∧ D.output < N)) ∧
    (∀ i < N, PEqualNP.MetaComplexity.NestedCover.readsIn D (Finset.range D.size) i ≤ 1) ∧
    (∀ j < D.size, PEqualNP.MetaComplexity.NestedCover.readsIn D (Finset.range D.size) (N+j) =
      if j+1 = D.size then 0 else 1)
  let val := fun (D : PEqualNP.CircuitLowerBounds.Circuit) (s : Finset (Fin N)) =>
    D.eval (List.ofFn (fun z : Fin N => decide (z ∈ s)))
  let other := fun z : Fin N => ∀ i : Fin 4, z ≠ x i
  let keep := fun z : Fin N => z = x 3 ∨ other z
  let E := fun i j : Fin N => val F {x 1,i,j}
  tree F → val F ∅ = false → (∀ z, val F {z} = false) →
  val F {x 0,x 3} = true → val F {x 1,x 2} = true →
  val F {x 0,x 2} = false → val F {x 1,x 3} = false →
  (∀ z, other z → val F {x 0,z} = false ∧ val F {x 1,z} = false) →
  (∀ a b c d, keep a → keep b → keep c → keep d →
    E a b = true → E c b = true → E c d = true → E a d = true) ∧
  ∀ t i, keep t → keep i → i ≠ x 3 → E (x 3) t = true → E i t = false := by
  classical
  intro N F x
  dsimp only
  intro tree empty single hq lp hp lq other
  obtain ⟨ops, back, out, raw, internal⟩ := tree
  have outBound : F.output < N + F.size := by
    rcases out with h | ⟨h, h'⟩ <;> omega
  have once (w : ℕ) : readsIn F (Finset.range F.size) w ≤ 1 := by
    by_cases early : w < N
    · exact raw w early
    by_cases present : w < N + F.size
    · have j : w - N < F.size := by omega
      have eq : N + (w - N) = w := by omega
      rw [← eq, internal _ j]
      split <;> omega
    · have none : readsIn F (Finset.range F.size) w = 0 := by
        unfold readsIn
        apply Finset.sum_eq_zero
        intro j hj
        apply List.count_eq_zero_of_not_mem
        intro used
        have below := back j (Finset.mem_range.1 hj) w used
        have size := Finset.mem_range.1 hj
        omega
      omega
  obtain ⟨f, rf, sound⟩ := formula_of_circuit (.lit (x 0) true) F ops back outBound once
  let V := fun s : Finset (Fin N) => F.eval (List.ofFn (fun z : Fin N => decide (z ∈ s)))
  have rawPair (a b : Fin N) : pairAt f ∅ a b = V {a,b} := by
    simpa [pairAt, V] using sound (insert a (insert b ∅))
  have pinPair (a b : Fin N) : pairAt f {x 1} a b = V {x 1,a,b} := by
    have eq : insert a (insert b ({x 1} : Finset (Fin N))) = {x 1,a,b} := by
      ext z
      simp only [Finset.mem_insert, Finset.mem_singleton]
      tauto
    rw [pairAt, eq, sound]
  have lowPair (a : Fin N) : value f (insert a {x 1}) = V {x 1,a} := by
    have eq : insert a ({x 1} : Finset (Fin N)) = {x 1,a} := by
      ext z
      simp [or_comm]
    rw [eq, sound]
  have safeLow (a : Fin N) (ha : a = x 3 ∨ ∀ j : Fin 4, a ≠ x j) :
      value f (insert a {x 1}) = false := by
    rw [lowPair]
    rcases ha with rfl | ha
    · exact lq
    · exact (other a ha).2
  constructor
  · intro a b c d ha hb hc hd ab cb cd
    have initial : value f {x 1} = false := (sound _).trans (single _)
    have result := pair_rectangle f {x 1} (fun z => z = x 3 ∨ ∀ j : Fin 4, z ≠ x j) rf
      initial safeLow a b c d ha hb hc hd ((pinPair a b).trans ab) ((pinPair c b).trans cb)
      ((pinPair c d).trans cd)
    exact (pinPair a d).symm.trans result
  · intro t i ht hi iq qt
    have hi' : pairAt f ∅ (x 0) i = false := (rawPair _ _).trans (other i (hi.resolve_left iq)).1
    have result := pair_isolation f (x 0) (x 1) (x 2) (x 3) t i rf
      (fun z => (sound _).trans (single z)) ((rawPair _ _).trans hq) ((rawPair _ _).trans lp)
      ((rawPair _ _).trans hp) hi' (safeLow _ (Or.inl rfl)) (safeLow t ht) (safeLow i hi)
      ((pinPair _ _).trans qt)
    exact (pinPair i t).symm.trans result
