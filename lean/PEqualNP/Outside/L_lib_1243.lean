import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_1243

variable {n m : Nat}
abbrev Box (n : Nat) := Finset (Fin n)
abbrev Bank (m n : Nat) := Fin m → Box n

def run (a b c d : Bank m n) (L : Box n) (js : List (Fin m)) (y : Box n) : Prop :=
  List.rec (motive := fun _ => Box n → Prop) (fun _ => True)
    (fun j _ prev y => ∃ u v, prev u ∧ u ⊆ v ∧ v ⊆ y ∧ a j \ L ⊆ u ∧ u ⊆ b j \ L ∧ c j \ L ⊆ v ∧ v ⊆ d j \ L) js y

def need (a c : Bank m n) (i : Fin m) := a i ∪ c i
def room (b d : Bank m n) (i : Fin m) := b i ∩ d i
def regular (a b c d : Bank m n) := ∀ j, a j⊆b j ∧ a j⊆d j ∧ c j⊆d j

lemma regular_of_single {a b c d : Bank m n} (h : ∀ i, run a b c d ∅ [i] Finset.univ) : regular a b c d := by
  intro i
  obtain ⟨u,v,_,huv,_,ha,hb,hc,hd⟩ := h i
  simp only [Finset.sdiff_empty] at ha hb hc hd
  exact ⟨ha.trans hb,ha.trans (huv.trans hd),hc.trans hd⟩

lemma characterize (a b c d : Bank m n) (h : regular a b c d) (L : Box n) (js : List (Fin m)) (y : Box n) :
  run a b c d L js y ↔ js.Pairwise (fun j i => need a c i \ L ⊆ room b d j) ∧
    ∀ i∈js, need a c i \ L ⊆ y := by
  induction js generalizing y with
  | nil => simp [run]
  | cons j js ih =>
    change (∃ u v, run a b c d L js u ∧ u ⊆ v ∧ v ⊆ y ∧ a j \ L ⊆ u ∧ u ⊆ b j \ L ∧ c j \ L ⊆ v ∧ v ⊆ d j \ L) ↔ _
    rw [List.pairwise_cons]
    constructor
    · rintro ⟨u,v,hu,huv,hvy,ha,hb,hc,hd⟩
      obtain ⟨hp,ht⟩ := (ih u).1 hu
      refine ⟨⟨?_,hp⟩,?_⟩
      · intro i hi z hz; have hzu := ht i hi hz
        exact Finset.mem_inter.mpr ⟨(Finset.mem_sdiff.mp (hb hzu)).1,(Finset.mem_sdiff.mp (hd (huv hzu))).1⟩
      · intro i hi; rcases List.mem_cons.mp hi with rfl | hi
        · intro z hz; obtain ⟨hz,hl⟩ := Finset.mem_sdiff.mp hz
          rcases Finset.mem_union.mp hz with hz | hz
          · exact hvy (huv (ha (Finset.mem_sdiff.mpr ⟨hz,hl⟩)))
          · exact hvy (hc (Finset.mem_sdiff.mpr ⟨hz,hl⟩))
        · exact (ht i hi).trans (huv.trans hvy)
    · rintro ⟨⟨hp,hr⟩,ht⟩
      let v := y ∩ (d j \ L)
      let u := v ∩ (b j \ L)
      refine ⟨u,v,(ih u).2 ⟨hr,?_⟩,Finset.inter_subset_left,Finset.inter_subset_left,?_,Finset.inter_subset_right,?_,Finset.inter_subset_right⟩
      · intro i hi z hz
        have hrm := Finset.mem_inter.mp (hp i hi hz)
        have hl := (Finset.mem_sdiff.mp hz).2
        exact Finset.mem_inter.mpr ⟨Finset.mem_inter.mpr ⟨ht i (List.mem_cons_of_mem _ hi) hz,
          Finset.mem_sdiff.mpr ⟨hrm.2,hl⟩⟩,Finset.mem_sdiff.mpr ⟨hrm.1,hl⟩⟩
      · intro z hz; obtain ⟨haz,hl⟩ := Finset.mem_sdiff.mp hz
        have hy := ht j List.mem_cons_self (Finset.mem_sdiff.mpr ⟨Finset.mem_union_left _ haz,hl⟩)
        exact Finset.mem_inter.mpr ⟨Finset.mem_inter.mpr ⟨hy,Finset.mem_sdiff.mpr ⟨(h j).2.1 haz,hl⟩⟩,
          Finset.mem_sdiff.mpr ⟨(h j).1 haz,hl⟩⟩
      · intro z hz; obtain ⟨hcz,hl⟩ := Finset.mem_sdiff.mp hz
        exact Finset.mem_inter.mpr ⟨ht j List.mem_cons_self (Finset.mem_sdiff.mpr ⟨Finset.mem_union_right _ hcz,hl⟩),
          Finset.mem_sdiff.mpr ⟨(h j).2.2 hcz,hl⟩⟩

lemma erased {S L Y : Box n} : S \ L ⊆ Y \ L ↔ S \ L ⊆ Y := by
  constructor
  · intro h z hz; exact (Finset.mem_sdiff.mp (h hz)).1
  · intro h z hz; exact Finset.mem_sdiff.mpr ⟨h hz,(Finset.mem_sdiff.mp hz).2⟩

lemma runEnd (a b c d : Bank m n) (h : regular a b c d) (L : Box n) (js : List (Fin m)) (y : Box n) :
  run a b c d L js (y \ L) ↔ js.Pairwise (fun j i => need a c i \ L ⊆ room b d j) ∧
    ∀ i∈js, need a c i \ L ⊆ y := by
  rw [characterize _ _ _ _ h]; simp only [erased]

lemma runTop (a b c d : Bank m n) (h : regular a b c d) (L : Box n) (js : List (Fin m)) :
  run a b c d L js (Finset.univ \ L) ↔ js.Pairwise (fun j i => need a c i \ L ⊆ room b d j) := by
  rw [runEnd _ _ _ _ h]; simp

lemma eraseCover (A B : Box n) (r : Prop) (e : Nat) :
    (∀ L : Box n, L.card ≤ e → (A \ L ⊆ B ↔ ¬ r)) ↔
    (r → e < (A \ B).card) ∧ (¬ r → (A \ B).card=0) := by
  classical
  constructor
  · intro h
    constructor
    · intro hr; by_contra! hle
      apply (h (A \ B) hle).1 _ hr
      intro z hz; obtain ⟨ha,hn⟩ := Finset.mem_sdiff.mp hz
      by_contra hb; exact hn (Finset.mem_sdiff.mpr ⟨ha,hb⟩)
    · intro hr; have sub := (h ∅ (by simp)).2 hr
      simp only [Finset.sdiff_empty] at sub
      simp [Finset.sdiff_eq_empty_iff_subset.mpr sub]
  · rintro ⟨hy,hn⟩ L hl
    constructor
    · intro hs hr
      have sub : A \ B ⊆ L := by
        intro z hz; obtain ⟨ha,hb⟩ := Finset.mem_sdiff.mp hz
        by_contra hh; exact hb (hs (Finset.mem_sdiff.mpr ⟨ha,hh⟩))
      exact (Nat.not_lt_of_ge ((Finset.card_le_card sub).trans hl)) (hy hr)
    · intro hr; have sub := Finset.sdiff_eq_empty_iff_subset.mp (Finset.card_eq_zero.mp (hn hr))
      exact Finset.sdiff_subset.trans sub

end PEqualNP.Outside.L_lib_1243

namespace PEqualNP.Outside.L_lib_1243

open scoped Classical

abbrev Cols (m t : Nat) := Fin m ⊕ Fin t

def Fit {m t n : Nat} (e : Nat) (conf : Fin m → Fin m → Prop) (off : Fin m → Fin t → Prop)
    (a b c d : Bank m n) (ends : Fin t → Box n) :=
  (∀ v w, (∀ i, off i w → off i v) → ends v ⊆ ends w) ∧
  ∀ L : Box n, L.card ≤ e →
    (∀ js, run a b c d L js (Finset.univ \ L) ↔ js.Pairwise (fun late early => ¬conf early late)) ∧
    ∀ v js, run a b c d L js (ends v \ L) ↔ js.Pairwise (fun late early => ¬conf early late) ∧ ∀ i∈js, ¬off i v

noncomputable def cells {m t n : Nat} (rows : Fin n → Finset (Fin m)) (cols : Fin n → Finset (Cols m t))
    (i : Fin m) (y : Cols m t) : Box n :=
  letI : ∀ P : Prop, Decidable P := Classical.propDecidable
  Finset.univ.filter (fun h => i∈rows h ∧ y∈cols h)

def Cover {m t n : Nat} (e : Nat) (conf : Fin m → Fin m → Prop) (off : Fin m → Fin t → Prop)
    (rows : Fin n → Finset (Fin m)) (cols : Fin n → Finset (Cols m t)) :=
  ∀ i y, (Sum.elim (conf i) (off i) y → e < (cells rows cols i y).card) ∧
    (¬Sum.elim (conf i) (off i) y → (cells rows cols i y).card=0)

lemma forward {m t n e : Nat} {conf : Fin m → Fin m → Prop} {off : Fin m → Fin t → Prop}
    {a b c d : Bank m n} {ends : Fin t → Box n} (F : Fit e conf off a b c d ends) :
    ∃ rows cols, Cover (n:=n) e conf off rows cols := by
  classical
  have reg : regular a b c d := regular_of_single (by
    intro j
    have H := ((F.2 ∅ (by simp)).1 [j]).2 (by simp)
    simpa only [Finset.sdiff_empty] using H)
  let cap : Cols m t → Box n := Sum.elim (room b d) ends
  let row (h : Fin n) := Finset.univ.filter (fun i => h∈need a c i)
  let col (h : Fin n) := Finset.univ.filter (fun j => h∉cap j)
  have exactCells (i y) : cells row col i y = (need a c i) \ cap y := by ext h; simp [cells,row,col]
  refine ⟨row,col,?_⟩
  intro i y; rw [exactCells]; apply (eraseCover ..).1
  intro L hL
  obtain ⟨ht,he⟩ := F.2 L hL
  rcases y with j | v
  · have H := (runTop _ _ _ _ reg L [j,i]).symm.trans (ht [j,i])
    simpa [List.pairwise_cons,cap] using H
  · have H := (runEnd _ _ _ _ reg L [i] (ends v)).symm.trans (he v [i])
    simpa [cap] using H

lemma backward {m t n e : Nat} {conf : Fin m → Fin m → Prop} {off : Fin m → Fin t → Prop}
    {rows : Fin n → Finset (Fin m)} {cols : Fin n → Finset (Cols m t)} (H : Cover e conf off rows cols) :
    ∃ a b c d ends, Fit (n:=n) e conf off a b c d ends := by
  classical
  let A (i : Fin m) := Finset.univ.filter (fun h => i∈rows h)
  let B (y : Cols m t) := Finset.univ.filter (fun h => y∉cols h)
  let Z : Bank m n := fun _ => ∅
  let U : Bank m n := fun _ => Finset.univ
  let B' : Bank m n := fun j => B (.inl j)
  let ends (v : Fin t) := Finset.univ.filter (fun h => ∃ j∈rows h, ¬off j v)
  have cellEq (i y) : cells rows cols i y = A i \ B y := by ext h; simp [A,B,cells]
  have robust (i y) (L : Box n) (hL : L.card≤e) :
      A i \ L ⊆ B y ↔ ¬Sum.elim (conf i) (off i) y := by
    apply (eraseCover _ _ _ _).2 _ L hL
    rw [← cellEq]; exact H i y
  have endSub (v : Fin t) : ends v ⊆ B (.inr v) := by
    intro h hh; obtain ⟨j,hj,hno⟩ := (Finset.mem_filter.mp hh).2
    have sub := (robust j (.inr v) ∅ (by simp)).2 hno
    exact sub (by simp [A,hj])
  have endIff (i v) (L : Box n) (hL : L.card≤e) : A i \ L ⊆ ends v ↔ ¬off i v := by
    constructor
    · intro sub; exact (robust i (.inr v) L hL).1 (sub.trans (endSub v))
    · intro hno h hm
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,i,(Finset.mem_filter.mp (Finset.mem_sdiff.mp hm).1).2,hno⟩
  have reg : regular Z B' A U := by intro i; simp [Z,U]
  have nr (i) : need Z A i = A i := by simp [need,Z]
  have rm (i) : room B' U i = B (.inl i) := by simp [room,B',U]
  refine ⟨Z,B',A,U,ends,?_,?_⟩
  · intro v w h h' hv; obtain ⟨i,hi,hn⟩ := (Finset.mem_filter.mp hv).2
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,i,hi,fun hh => hn (h i hh)⟩
  · intro L hL
    have eq (js : List (Fin m)) : js.Pairwise (fun j i => need Z A i \ L ⊆ room B' U j) ↔
        js.Pairwise (fun j i => ¬conf i j) := by
      have each (i j : Fin m) : (need Z A i \ L ⊆ room B' U j) ↔ ¬conf i j :=
        (nr i ▸ rm j ▸ robust i (.inl j) L hL)
      constructor
      · intro hp; exact hp.imp (fun {j i} hh => (each i j).1 hh)
      · intro hp; exact hp.imp (fun {j i} hh => (each i j).2 hh)
    constructor
    · intro js; exact (runTop _ _ _ _ reg L js).trans (eq js)
    · intro v js; rw [runEnd _ _ _ _ reg,eq]; simp only [nr,endIff _ _ _ hL]

end PEqualNP.Outside.L_lib_1243

namespace PEqualNP.Outside.L_lib_1243

theorem realization : (letI : ∀ P : Prop, Decidable P := Classical.propDecidable
let named := fun (n m : Nat) (a b c d : Fin m → Finset (Fin n))
    (lost last : Finset (Fin n)) (js : List (Fin m)) =>
  List.rec (motive := fun _ => Finset (Fin n) → Prop) (fun _ => True)
    (fun j _ prev y => ∃ u v, prev u ∧ u ⊆ v ∧ v ⊆ y ∧
      a j \ lost ⊆ u ∧ u ⊆ b j \ lost ∧ c j \ lost ⊆ v ∧ v ⊆ d j \ lost)
    js (last \ lost)
∀ (m t n e : Nat) (conf : Fin m → Fin m → Prop) (off : Fin m → Fin t → Prop),
  (∀ i, conf i i) →
  let Col := Fin m ⊕ Fin t
  let rel := fun i => Sum.elim (conf i) (off i)
  let allowed := fun (js : List (Fin m)) => js.Pairwise (fun late early => ¬conf early late)
  (∃ (a b c d : Fin m → Finset (Fin n)) (ends : Fin t → Finset (Fin n)),
    (∀ v w, (∀ i, off i w → off i v) → ends v ⊆ ends w) ∧
    ∀ lost : Finset (Fin n), lost.card ≤ e →
      (∀ js, named n m a b c d lost Finset.univ js ↔ allowed js) ∧
      ∀ v js, named n m a b c d lost (ends v) js ↔
        allowed js ∧ ∀ i ∈ js, ¬off i v) ↔
  ∃ (rows : Fin n → Finset (Fin m)) (cols : Fin n → Finset Col),
    ∀ i y,
      let witnesses := (Finset.univ : Finset (Fin n)).filter (fun h => i ∈ rows h ∧ y ∈ cols h)
      (rel i y → e < witnesses.card) ∧ (¬rel i y → witnesses.card = 0)) := by
  dsimp only
  intro m t n e conf off _
  have de : (fun a b : Fin n => Classical.propDecidable (a=b)) = instDecidableEqFin n := Subsingleton.elim _ _
  rw [de]
  constructor
  · rintro ⟨a,b,c,d,ends,F⟩
    obtain ⟨rows,cols,H⟩ := PEqualNP.Outside.L_lib_1243.forward (n:=n) (e:=e) (conf:=conf) (off:=off) (a:=a) (b:=b) (c:=c) (d:=d) (ends:=ends) F
    exact ⟨rows,cols,H⟩
  · rintro ⟨rows,cols,H⟩
    obtain ⟨a,b,c,d,ends,F⟩ := PEqualNP.Outside.L_lib_1243.backward (n:=n) (e:=e) (conf:=conf) (off:=off) (rows:=rows) (cols:=cols) H
    exact ⟨a,b,c,d,ends,F⟩

end PEqualNP.Outside.L_lib_1243

theorem PEqualNP.Outside.L_lib_1243 : (letI : ∀ P : Prop, Decidable P := Classical.propDecidable
let named := fun (n m : Nat) (a b c d : Fin m → Finset (Fin n))
    (lost last : Finset (Fin n)) (js : List (Fin m)) =>
  List.rec (motive := fun _ => Finset (Fin n) → Prop) (fun _ => True)
    (fun j _ prev y => ∃ u v, prev u ∧ u ⊆ v ∧ v ⊆ y ∧
      a j \ lost ⊆ u ∧ u ⊆ b j \ lost ∧ c j \ lost ⊆ v ∧ v ⊆ d j \ lost)
    js (last \ lost)
∀ (m t n e : Nat) (conf : Fin m → Fin m → Prop) (off : Fin m → Fin t → Prop),
  (∀ i, conf i i) →
  let Col := Fin m ⊕ Fin t
  let rel := fun i => Sum.elim (conf i) (off i)
  let allowed := fun (js : List (Fin m)) => js.Pairwise (fun late early => ¬conf early late)
  (∃ (a b c d : Fin m → Finset (Fin n)) (ends : Fin t → Finset (Fin n)),
    (∀ v w, (∀ i, off i w → off i v) → ends v ⊆ ends w) ∧
    ∀ lost : Finset (Fin n), lost.card ≤ e →
      (∀ js, named n m a b c d lost Finset.univ js ↔ allowed js) ∧
      ∀ v js, named n m a b c d lost (ends v) js ↔
        allowed js ∧ ∀ i ∈ js, ¬off i v) ↔
  ∃ (rows : Fin n → Finset (Fin m)) (cols : Fin n → Finset Col),
    ∀ i y,
      let witnesses := (Finset.univ : Finset (Fin n)).filter (fun h => i ∈ rows h ∧ y ∈ cols h)
      (rel i y → e < witnesses.card) ∧ (¬rel i y → witnesses.card = 0)) := by
  exact PEqualNP.Outside.L_lib_1243.realization
