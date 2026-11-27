import PEqualNP.Defs

namespace PEqualNP.Outside.L_clb_057_aux

open Classical

abbrev Word (n : Nat) := Fin n → Bool
abbrev State (d : Nat) := Word (d + 1)
abbrev Payload (d : Nat) := Word d
abbrev Test (w : Nat) := Fin w → Word (w + 1) → Bool

def splice {w : Nat} (a b : Word w) (i : Fin w) : Word (w + 1) := fun j =>
  if h : i.val + j.val < w then a ⟨i.val + j.val, h⟩ else
    b ⟨i.val + j.val - w, by have := i.isLt; have := j.isLt; omega⟩

def SweepOk {w : Nat} (test : Test w) (a b : Word w) := ∀ i, test i (splice a b i) = true

lemma splice_head {w : Nat} (a b : Word w) (i : Fin w) : splice a b i 0 = a i := by
  simp [splice, i.isLt]

lemma splice_last {w : Nat} (a b : Word w) (i : Fin w) :
    splice a b i (Fin.last w) = b i := by
  simp [splice, show ¬ (i.val + w < w) by omega]

def tagOffset {d : Nat} (i : Fin (d + 1)) : Fin ((d + 1) + 1) :=
  ⟨d + 1 - i.val, by omega⟩

lemma splice_tag {d : Nat} (a b : State d) (i : Fin (d + 1)) :
    splice a b i (tagOffset i) = b 0 := by
  have e : i.val + (d + 1 - i.val) = d + 1 := by have := i.isLt; omega
  simp [splice, tagOffset, e]

def payload {d : Nat} (a : State d) : Payload d := fun j => a j.succ
def diff {d : Nat} (a h : Payload d) : Payload d := fun j => xor (a j) (h j)
def mask {d : Nat} (h : Payload d) (a : State d) : State d :=
  Fin.cases (a 0) (fun j => xor (a j.succ) (a 0 && h j))
def rise {d : Nat} (a : State d) : State d := Fin.cases true (payload a)

def maskTest {d : Nat} (h : Payload d) : Test (d + 1) :=
  Fin.cases (fun p => p (Fin.last (d + 1)) == p 0) (fun j p =>
    p (Fin.last (d + 1)) == xor (p 0) (p (tagOffset j.succ) && h j))

lemma mask_ok {d : Nat} (h : Payload d) (a b : State d) :
    SweepOk (maskTest h) a b ↔ b = mask h a := by
  constructor
  · intro ok
    have tag : b 0 = a 0 := by
      simpa [maskTest, splice_last, splice_head] using ok 0
    funext i
    refine Fin.cases (by simpa [mask] using tag) ?_ i
    intro j
    simpa [maskTest, splice_last, splice_head, splice_tag, mask, tag] using ok j.succ
  · rintro rfl i
    refine Fin.cases ?_ ?_ i
    · simp [maskTest, splice_last, splice_head, mask]
    · intro j
      simp [maskTest, splice_last, splice_head, splice_tag, mask]

def toggleTest {d : Nat} (h : Payload d) (A : Payload d → Payload d → Bool) : Test (d + 1) :=
  Fin.cases (fun p =>
    if p (Fin.last (d + 1)) == p 0 then true else
    if p 0 then false else A (fun j => p j.succ.castSucc) (diff (fun j => p j.succ.castSucc) h))
    (fun _ p => p (Fin.last (d + 1)) == p 0)

lemma splice_payload {d : Nat} (a b : State d) (j : Fin d) :
    splice a b 0 j.succ.castSucc = a j.succ := by
  simp [splice]
  rfl

lemma toggle_proj {d : Nat} (h : Payload d) (i : Fin (d + 1)) (p : Word ((d + 1) + 1)) :
    (∃ c : Bool, ∀ A, toggleTest h A i p = c) ∨
    ∃ u v, ∀ A, toggleTest h A i p = A u v := by
  refine Fin.cases ?_ (fun _ => Or.inl ⟨_, fun _ => rfl⟩) i
  simp only [toggleTest, Fin.cases_zero]
  split
  · exact Or.inl ⟨_, fun _ => rfl⟩
  · split
    · exact Or.inl ⟨_, fun _ => rfl⟩
    · exact Or.inr ⟨_, _, fun _ => rfl⟩

lemma toggle_ok {d : Nat} (h : Payload d) (A : Payload d → Payload d → Bool) (a b : State d) :
    SweepOk (toggleTest h A) a b ↔
      b = a ∨ (a 0 = false ∧ A (payload a) (diff (payload a) h) = true ∧ b = rise a) := by
  have at0 : toggleTest h A 0 (splice a b 0) =
      (if b 0 == a 0 then true else if a 0 then false else A (payload a) (diff (payload a) h)) := by
    simp only [toggleTest, Fin.cases_zero, splice_last, splice_head, splice_payload]
    rfl
  have at1 (j : Fin d) : toggleTest h A j.succ (splice a b j.succ) = (b j.succ == a j.succ) := by
    simp [toggleTest, splice_last, splice_head]
  constructor
  · intro ok
    have pl (j : Fin d) : b j.succ = a j.succ := by simpa [at1] using ok j.succ
    have hd := ok 0
    rw [at0] at hd
    by_cases he : b 0 = a 0
    · exact Or.inl (funext (fun i => Fin.cases he pl i))
    · have e : a 0 = false ∧ b 0 = true ∧ A (payload a) (diff (payload a) h) = true := by
        cases ha : a 0 <;> cases hb : b 0 <;> simp_all
      exact Or.inr ⟨e.1, e.2.2, funext (fun i => Fin.cases (by simpa [rise] using e.2.1)
        (fun j => by simpa [rise, payload] using pl j) i)⟩
  · rintro (rfl | ⟨ha, ht, rfl⟩) i
    · exact Fin.cases (by simp [at0]) (fun j => by simp [at1]) i
    · exact Fin.cases (by simp [at0, rise, ha, ht]) (fun j => by simp [at1, rise, payload]) i

lemma mask_twice {d : Nat} (h : Payload d) (a : State d) : mask h (mask h a) = a := by
  funext i
  refine Fin.cases (by simp [mask]) ?_ i
  intro j
  simp [mask]

lemma mask_off {d : Nat} (h : Payload d) {a : State d} (ha : a 0 = false) : mask h a = a := by
  funext i; refine Fin.cases (by simp [mask]) (fun j => by simp [mask, ha]) i

def switched {d : Nat} (h : Payload d) (a : State d) : State d :=
  Fin.cases true (diff (payload a) h)

lemma mask_rise {d : Nat} (a : State d) (h : Payload d) : mask h (rise a) = switched h a := by
  funext i
  refine Fin.cases (by simp [mask, rise, switched])
    (fun j => by simp [mask, rise, switched, diff, payload]) i

noncomputable def ways {w : Nat} : List (Test w) → Word w → Word w → Nat
  | [], a, b => if a = b then 1 else 0
  | t :: ts, a, b => ∑ y, if SweepOk t a y then ways ts y b else 0

lemma ways_append {w : Nat} (fs gs : List (Test w)) (a c : Word w) :
    ways (fs ++ gs) a c = ∑ b : Word w, ways fs a b * ways gs b c := by
  induction fs generalizing a with
  | nil =>
    simp only [List.nil_append, ways]
    rw [Finset.sum_eq_single a]
    · simp
    · intro b _ hba; simp [Ne.symm hba]
    · simp
  | cons f fs ih =>
    simp only [List.cons_append, ways]
    have h1 : ∀ y : Word w,
        (if SweepOk f a y then ways (fs ++ gs) y c else 0) =
        ∑ b : Word w, (if SweepOk f a y then ways fs y b else 0) * ways gs b c := by
      intro y
      by_cases hy : SweepOk f a y
      · simp [hy, ih]
      · simp [hy]
    simp_rw [h1]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro b _
    rw [Finset.sum_mul]

def tests {d : Nat} (A : Payload d → Payload d → Bool) (hs : List (Payload d)) : List (Test (d + 1)) :=
  hs.flatMap (fun h => [maskTest h, toggleTest h A, maskTest h])

lemma len_tests {d : Nat} (A : Payload d → Payload d → Bool) (hs : List (Payload d)) :
    (tests A hs).length = 3 * hs.length := by
  induction hs with
  | nil => simp [tests]
  | cons h hs ih =>
    change (tests A hs).length + 3 = 3 * (hs.length + 1)
    rw [ih]; omega

private lemma applyMask {d : Nat} (h : Payload d) (fs : List (Test (d + 1))) (a b : State d) :
    ways (maskTest h :: fs) a b = ways fs (mask h a) b := by
  simp [ways, mask_ok]

private lemma applyToggle {d : Nat} (A : Payload d → Payload d → Bool) (h : Payload d)
    (fs : List (Test (d + 1))) (a b : State d) :
    ways (toggleTest h A :: fs) a b = ways fs a b +
      (if a 0 = false ∧ A (payload a) (diff (payload a) h) = true then ways fs (rise a) b else 0) := by
  by_cases ho : a 0 = false ∧ A (payload a) (diff (payload a) h) = true
  · have ne : a ≠ rise a := by
      intro he
      have := congrFun he 0
      simp [rise, ho.1] at this
    have point (y : State d) :
        (if SweepOk (toggleTest h A) a y then ways fs y b else 0) =
        (if y = a then ways fs y b else 0) + (if y = rise a then ways fs y b else 0) := by
      by_cases yh : y = a <;> by_cases yr : y = rise a <;> simp_all [toggle_ok]
    simp [ways, point, Finset.sum_add_distrib, ho]
  · have hnot (y) : SweepOk (toggleTest h A) a y ↔ y = a := by
      rw [toggle_ok]; tauto
    simp [ways, hnot, ho]

lemma blockStep {d : Nat} (A : Payload d → Payload d → Bool) (hs : List (Payload d))
    (h : Payload d) (a b : State d) :
    ways (tests A (h :: hs)) a b = ways (tests A hs) a b +
      (if a 0 = false ∧ A (payload a) (diff (payload a) h) = true then
        ways (tests A hs) (switched h a) b else 0) := by
  change ways (maskTest h :: toggleTest h A :: maskTest h :: tests A hs) a b = _
  rw [applyMask, applyToggle, applyMask, applyMask, mask_twice]
  by_cases ha : a 0 = false
  · simp [mask_off h ha, mask_rise]
  · simp [mask, ha]

def hit {d : Nat} (A : Payload d → Payload d → Bool) (a b : State d) (h : Payload d) : Bool :=
  decide (a 0 = false ∧ A (payload a) (diff (payload a) h) = true ∧ switched h a = b)

lemma ways_formula {d : Nat} (A : Payload d → Payload d → Bool) (hs : List (Payload d))
    (a b : State d) :
    ways (tests A hs) a b = (if a = b then 1 else 0) + (hs.filter (hit A a b)).length := by
  induction hs generalizing a with
  | nil => simp [tests, ways]
  | cons h hs ih =>
    rw [blockStep, ih, ih]
    have dead (k : Payload d) : hit A (switched h a) b k = false := by simp [hit, switched]
    have deadList : hs.filter (hit A (switched h a) b) = [] :=
      List.filter_eq_nil_iff.mpr (fun k _ => by simp [dead k])
    simp only [deadList, List.length_nil, Nat.add_zero]
    by_cases en : a 0 = false ∧ A (payload a) (diff (payload a) h) = true
    · by_cases sw : switched h a = b
      · simp [hit, en.1, en.2, sw]; omega
      · simp [hit, en.1, en.2, sw]
    · have hnot : hit A a b h = false := by simp [hit]; tauto
      simp [hnot, en]

noncomputable def keyList (d : Nat) : List (Payload d) :=
  (List.finRange (Fintype.card (Payload d))).map (Fintype.equivFin (Payload d)).symm

lemma keylen (d : Nat) : (keyList d).length = 2 ^ d := by simp [keyList]

lemma keyAll {d : Nat} (h : Payload d) : h ∈ keyList d := by
  apply List.mem_map.mpr
  exact ⟨Fintype.equivFin _ h, List.mem_finRange _, Equiv.symm_apply_apply _ _⟩

lemma keyNodup (d : Nat) : (keyList d).Nodup :=
  (List.nodup_finRange _).map (Equiv.injective _)

lemma keyList_getElem (d : Nat) (q : Nat) (hq : q < (keyList d).length) :
    (keyList d)[q] = (Fintype.equivFin (Payload d)).symm ⟨q, by rw [keylen] at hq; simpa using hq⟩ := by
  simp [keyList]

private lemma hit_iff {d : Nat} (A : Payload d → Payload d → Bool) (a b : State d) (h : Payload d) :
    hit A a b h = true ↔ a 0 = false ∧ b 0 = true ∧ A (payload a) (payload b) = true ∧
      h = diff (payload a) (payload b) := by
  simp only [hit, decide_eq_true_eq]
  constructor
  · rintro ⟨ha, he, sw⟩
    have pb : payload b = diff (payload a) h := by rw [← sw]; rfl
    refine ⟨ha, by rw [← sw]; rfl, pb ▸ he, ?_⟩
    funext j
    simp [pb, diff]
  · rintro ⟨ha, hb, he, rfl⟩
    have e : diff (payload a) (diff (payload a) (payload b)) = payload b := by
      funext j; simp [diff]
    exact ⟨ha, by rwa [e], funext (fun i => Fin.cases (by simpa [switched] using hb.symm)
      (fun j => by simp [switched, e, payload]) i)⟩

lemma net_result {d : Nat} (A : Payload d → Payload d → Bool) (a b : State d) :
    ways (tests A (keyList d)) a b = (if a = b then 1 else 0) +
      (if a 0 = false ∧ b 0 = true ∧ A (payload a) (payload b) = true then 1 else 0) := by
  rw [ways_formula]
  congr 1
  by_cases en : a 0 = false ∧ b 0 = true ∧ A (payload a) (payload b) = true
  · simp only [en, ite_true]
    let h := diff (payload a) (payload b)
    have only : (keyList d).filter (hit A a b) = [h] := by
      have nodup := (keyNodup d).filter (hit A a b)
      have mem (q) : q ∈ (keyList d).filter (hit A a b) ↔ q = h := by
        simp [List.mem_filter, hit_iff, keyAll, en.1, en.2.1, en.2.2, h]
      cases he : (keyList d).filter (hit A a b) with
      | nil => have := (mem h).mpr rfl; simp [he] at this
      | cons q qs =>
        have eu := (mem q).mp (by simp [he])
        rw [he, List.nodup_cons] at nodup
        cases qt : qs with
        | nil => simp [eu]
        | cons p ps =>
          have ep := (mem p).mp (by simp [he, qt])
          exact False.elim (nodup.1 (by simp [eu, ← ep, qt]))
    simp [only]
  · have no (q : Payload d) : hit A a b q = false := by
      cases e : hit A a b q with
      | false => rfl
      | true =>
        obtain ⟨ha, hb, ht, _⟩ := (hit_iff ..).mp e
        exact False.elim (en ⟨ha, hb, ht⟩)
    simp [en, no]

def GridOk {w : Nat} (fs : List (Test w)) (x : Fin (fs.length + 1) → Word w) (a b : Word w) : Prop :=
  x 0 = a ∧ x (Fin.last fs.length) = b ∧
    ∀ t : Fin fs.length, SweepOk fs[t.val] (x t.castSucc) (x t.succ)

private lemma gridNil {w} (x : Fin 1 → Word w) (a b : Word w) :
    GridOk [] x a b ↔ x 0 = a ∧ a = b := by
  simp [GridOk, Fin.last_zero]; rintro rfl; rfl

private lemma gridCons {w} (f : Test w) (fs : List (Test w))
    (a b s : Word w) (x : Fin (fs.length + 1) → Word w) :
    GridOk (f :: fs) (Fin.cons s x) a b ↔
      s = a ∧ SweepOk f s (x 0) ∧ GridOk fs x (x 0) b := by
  change (s = a ∧ x (Fin.last fs.length) = b ∧
    ∀ j : Fin (fs.length + 1), SweepOk (f :: fs)[j.val] (Fin.cons (α := fun _ => Word w) s x j.castSucc) (x j))
      ↔ s = a ∧ SweepOk f s (x 0) ∧ GridOk fs x (x 0) b
  constructor
  · rintro ⟨rfl, e, h⟩
    exact ⟨rfl, h 0, rfl, e, fun i => h i.succ⟩
  · rintro ⟨rfl, t, _, e, h⟩
    exact ⟨rfl, e, fun j => Fin.cases t (fun i => h i) j⟩

private lemma sumCons {w p : Nat} (f : (Fin (p + 1) → Word w) → Nat) :
    ∑ x, f x = ∑ s : Word w, ∑ x : Fin p → Word w, f (Fin.cons (α := fun _ => Word w) s x) := by
  have h := (Fin.consEquiv (n := p) (fun _ => Word w)).sum_comp f
  rw [← h, Fintype.sum_prod_type]
  rfl

lemma count_grid {w : Nat} (fs : List (Test w)) (a b : Word w) :
    (∑ x : Fin (fs.length + 1) → Word w, if GridOk fs x a b then 1 else 0) = ways fs a b := by
  induction fs generalizing a with
  | nil =>
    rw [sumCons]
    by_cases h : a = b <;> simp [gridNil, ways, h]
  | cons f fs ih =>
    rw [sumCons]
    simp only [gridCons]
    have hs (s) : (∑ x : Fin (fs.length + 1) → Word w,
        if s = a ∧ SweepOk f s (x 0) ∧ GridOk fs x (x 0) b then 1 else 0) =
        if s = a then (∑ y, if SweepOk f a y then ways fs y b else 0) else 0 := by
      by_cases eq : s = a
      · subst s
        simp only [true_and, ite_true]
        simp_rw [← ih]
        have distribute (y : Word w) :
            (if SweepOk f a y then ∑ x, if GridOk fs x y b then 1 else 0 else 0 : Nat) =
            ∑ x, if SweepOk f a y then (if GridOk fs x y b then 1 else 0) else 0 := by
          by_cases p : SweepOk f a y <;> simp [p]
        simp_rw [distribute]
        rw [Finset.sum_comm (s := Finset.univ) (t := Finset.univ)]
        apply Finset.sum_congr rfl
        intro x _
        have restrict (y : Word w) (neq : y ≠ x 0) : ¬ GridOk fs x y b := fun h => neq h.1.symm
        rw [Finset.sum_eq_single (x 0)]
        · split_ifs <;> simp_all
        · intro z _ ne
          simp [restrict z ne]
        · simp
      · simp [eq]
    exact (Finset.sum_congr rfl (fun s _ => hs s)).trans (by simp [ways])

def CycleOk {w : Nat} (fs : List (Test w)) (hpos : 0 < fs.length) (x : Fin fs.length → Word w) : Prop :=
  ∀ t : Fin fs.length, SweepOk fs[t.val] (x t) (x ⟨(t.val + 1) % fs.length, Nat.mod_lt _ hpos⟩)

lemma count_cycle {w : Nat} (fs : List (Test w)) (hpos : 0 < fs.length) :
    (∑ x : Fin fs.length → Word w, if CycleOk fs hpos x then 1 else 0) =
    ∑ a : Word w, ways fs a a := by
  have h1 : ∀ a : Word w,
      (∑ x : Fin fs.length → Word w, if x ⟨0, hpos⟩ = a ∧ CycleOk fs hpos x then 1 else 0) =
      ways fs a a := by
    intro a
    rw [← count_grid fs a a]
    let extend : (Fin fs.length → Word w) → (Fin (fs.length + 1) → Word w) :=
      fun x t => if ht : t.val < fs.length then x ⟨t.val, ht⟩ else x ⟨0, hpos⟩
    have hext_inj : Function.Injective extend := by
      intro x y hxy
      funext t
      have h := congrFun hxy t.castSucc
      simp only [extend, Fin.val_castSucc, t.isLt, ↓reduceDIte] at h
      exact h
    have hext_iff : ∀ x, GridOk fs (extend x) a a ↔ x ⟨0, hpos⟩ = a ∧ CycleOk fs hpos x := by
      intro x
      constructor
      · rintro ⟨h0, _, hall⟩
        have hx0 : x ⟨0, hpos⟩ = a := by simpa [extend, hpos] using h0
        refine ⟨hx0, fun t => ?_⟩
        have ht := hall t
        have h1 : extend x t.castSucc = x t := by simp [extend, t.isLt]
        have h2 : extend x t.succ = x ⟨(t.val + 1) % fs.length, Nat.mod_lt _ hpos⟩ := by
          dsimp only [extend]
          by_cases hlt : t.val + 1 < fs.length
          · simp only [Fin.val_succ, hlt, ↓reduceDIte]
            congr 1; apply Fin.ext; exact (Nat.mod_eq_of_lt hlt).symm
          · have heq : t.val + 1 = fs.length := by omega
            simp only [Fin.val_succ, hlt, ↓reduceDIte]
            congr 1; apply Fin.ext; simp [heq]
        rw [h1, h2] at ht
        exact ht
      · rintro ⟨hx0, hcyc⟩
        refine ⟨by simpa [extend, hpos] using hx0, by simp [extend, hx0], fun t => ?_⟩
        have h1 : extend x t.castSucc = x t := by simp [extend, t.isLt]
        have h2 : extend x t.succ = x ⟨(t.val + 1) % fs.length, Nat.mod_lt _ hpos⟩ := by
          dsimp only [extend]
          by_cases hlt : t.val + 1 < fs.length
          · simp only [Fin.val_succ, hlt, ↓reduceDIte]
            congr 1; apply Fin.ext; exact (Nat.mod_eq_of_lt hlt).symm
          · have heq : t.val + 1 = fs.length := by omega
            simp only [Fin.val_succ, hlt, ↓reduceDIte]
            congr 1; apply Fin.ext; simp [heq]
        rw [h1, h2]
        exact hcyc t
    symm
    rw [← Finset.sum_subset (Finset.subset_univ (Finset.univ.image extend))]
    · rw [Finset.sum_image (fun x _ y _ h => hext_inj h)]
      apply Finset.sum_congr rfl
      intro x _
      simp [hext_iff x]
    · intro y _ hnot
      by_cases hg : GridOk fs y a a
      · exfalso
        apply hnot
        refine Finset.mem_image.mpr ⟨fun t => y t.castSucc, Finset.mem_univ _, ?_⟩
        funext t
        dsimp only [extend]
        by_cases hlt : t.val < fs.length
        · simp only [hlt, ↓reduceDIte]; rfl
        · have hlast : t = Fin.last fs.length := Fin.ext (by simp [Fin.val_last]; omega)
          simp only [hlt, ↓reduceDIte]
          rw [hlast, hg.2.1]
          exact hg.1
      · simp [hg]
  simp_rw [← h1]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  rw [Finset.sum_eq_single (x ⟨0, hpos⟩)]
  · simp
  · intro a _ hne; simp [Ne.symm hne]
  · simp

def linearPos {m w : Nat} (i : Fin m) (j : Fin w) : Fin (m * w) :=
  ⟨i.val * w + j.val, by
    have := Nat.mul_le_mul_right w (show i.val + 1 ≤ m from i.isLt)
    rw [Nat.add_mul, Nat.one_mul] at this
    have := j.isLt; omega⟩

def regroup {m w P : Nat} (hw : 0 < w) (eq : P = m * w) : (Word P) ≃ (Fin m → Word w) where
  toFun x i j := x ⟨(linearPos i j).val, eq ▸ (linearPos i j).isLt⟩
  invFun y i := y ⟨i.val / w, (Nat.div_lt_iff_lt_mul hw).mpr (eq ▸ i.isLt)⟩
    ⟨i.val % w, Nat.mod_lt _ hw⟩
  left_inv x := by
    funext j; apply congrArg x; apply Fin.ext; change j.val / w * w + j.val % w = j.val
    simpa [Nat.mul_comm, Nat.add_comm] using Nat.mod_add_div j.val w
  right_inv f := by
    funext i j
    change f ⟨(i.val * w + j.val) / w, _⟩ ⟨(i.val * w + j.val) % w, _⟩ = f i j
    congr 1
    · apply Fin.ext; simp [Nat.add_comm _ j.val, Nat.add_mul_div_right, Nat.div_eq_of_lt j.isLt, hw]
    · apply Fin.ext; simp [Nat.mod_eq_of_lt j.isLt]

def getPhase {w n : Nat} (fs : List (Test w)) (hw : 0 < w) (eq : n = fs.length * w) (i : Fin n) :
    Word (w + 1) → Bool :=
  (fs[i.val / w]'(by apply (Nat.div_lt_iff_lt_mul hw).mpr; exact eq ▸ i.isLt))
    ⟨i.val % w, Nat.mod_lt _ hw⟩

lemma cyclic_window_eq_splice {w m n : Nat} (hw : 0 < w) (hm : 0 < m) (eq : n = m * w)
    (word : Word n) (t : Fin m) (i : Fin w) :
    (fun j : Fin (w + 1) => word ⟨((t.val * w + i.val) + j.val) % n, Nat.mod_lt _ (by rw [eq]; exact Nat.mul_pos hm hw)⟩) =
    splice (regroup hw eq word t) (regroup hw eq word ⟨(t.val + 1) % m, Nat.mod_lt _ hm⟩) i := by
  have hnpos : 0 < n := by rw [eq]; exact Nat.mul_pos hm hw
  funext j
  unfold splice
  split
  · rename_i hlt
    have hlt_n : t.val * w + i.val + j.val < n := by
      have h1 : (t.val + 1) * w ≤ m * w := Nat.mul_le_mul_right w t.isLt
      rw [Nat.add_mul, Nat.one_mul] at h1
      omega
    dsimp only [regroup, linearPos]
    congr 1
    apply Fin.ext
    dsimp only
    rw [Nat.mod_eq_of_lt hlt_n]
    omega
  · rename_i hge
    dsimp only [regroup, linearPos]
    congr 1
    apply Fin.ext
    dsimp only
    by_cases ht1 : t.val + 1 < m
    · have hlt_n : t.val * w + i.val + j.val < n := by
        have h1 : (t.val + 2) * w ≤ m * w := Nat.mul_le_mul_right w ht1
        have h2 : (t.val + 2) * w = t.val * w + w + w := by
          have : t.val + 2 = t.val + 1 + 1 := rfl
          rw [this, Nat.add_mul, Nat.add_mul, Nat.one_mul]
        have hj := j.isLt
        omega
      rw [Nat.mod_eq_of_lt hlt_n, Nat.mod_eq_of_lt ht1, Nat.add_mul, Nat.one_mul]
      omega
    · have hteq : t.val + 1 = m := by omega
      have hmod_m : (t.val + 1) % m = 0 := by rw [hteq, Nat.mod_self]
      rw [hmod_m, Nat.zero_mul, Nat.zero_add]
      have h1 : t.val * w + i.val + j.val = n + (i.val + j.val - w) := by
        have hmw : m * w = t.val * w + w := by
          calc m * w = (t.val + 1) * w := by rw [hteq]
            _ = t.val * w + w := by rw [Nat.add_mul, Nat.one_mul]
        omega
      have h2 : i.val + j.val - w < n := by
        have h1w : w ≤ n := by
          have : 1 * w ≤ m * w := Nat.mul_le_mul_right w hm
          omega
        have hi := i.isLt
        have hj := j.isLt
        omega
      rw [h1, Nat.add_mod, Nat.mod_self, Nat.zero_add, Nat.mod_mod, Nat.mod_eq_of_lt h2]

theorem cyclic_count {w n : Nat} (fs : List (Test w)) (hw : 0 < w) (hpos : 0 < fs.length)
    (eq : n = fs.length * w) :
    let hn : 0 < n := by rw [eq]; exact Nat.mul_pos hpos hw
    (Finset.univ.filter (fun word : Word n =>
      ∀ i : Fin n, getPhase fs hw eq i
        (fun j => word ⟨(i.val + j.val) % n, Nat.mod_lt _ hn⟩) = true)).card =
    ∑ a : Word w, ways fs a a := by
  intro hn
  rw [← count_cycle fs hpos]
  rw [Finset.card_filter]
  have hiff : ∀ word : Word n,
      (∀ i : Fin n, getPhase fs hw eq i (fun j => word ⟨(i.val + j.val) % n, Nat.mod_lt _ hn⟩) = true) ↔
      CycleOk fs hpos (regroup hw eq word) := by
    intro word
    constructor
    · intro hall t i
      have hlt : t.val * w + i.val < n := by
        have h1 : (t.val + 1) * w ≤ fs.length * w := Nat.mul_le_mul_right w t.isLt
        rw [Nat.add_mul, Nat.one_mul] at h1
        have hi := i.isLt
        omega
      have hrow := hall ⟨t.val * w + i.val, hlt⟩
      have hdiv : (t.val * w + i.val) / w = t.val := by
        rw [Nat.add_comm, Nat.add_mul_div_right _ _ hw, Nat.div_eq_of_lt i.isLt, Nat.zero_add]
      have hmod : (t.val * w + i.val) % w = i.val := by
        rw [Nat.mul_add_mod_self_right, Nat.mod_eq_of_lt i.isLt]
      have hph : getPhase fs hw eq ⟨t.val * w + i.val, hlt⟩ = fs[t.val] i := by
        unfold getPhase
        simp only [hmod]
        exact congrFun (getElem_congr (c := fs) rfl hdiv (by omega)) i
      rw [hph, cyclic_window_eq_splice hw hpos eq word t i] at hrow
      exact hrow
    · intro hcyc idx
      let t : Fin fs.length := ⟨idx.val / w, (Nat.div_lt_iff_lt_mul hw).mpr (eq ▸ idx.isLt)⟩
      let i : Fin w := ⟨idx.val % w, Nat.mod_lt _ hw⟩
      have hidx : idx.val = t.val * w + i.val := by
        dsimp [t, i]
        simpa [Nat.mul_comm, Nat.add_comm] using (Nat.mod_add_div idx.val w).symm
      have hph : getPhase fs hw eq idx = fs[t.val] i := rfl
      rw [hph]
      have hwin : (fun j : Fin (w + 1) => word ⟨(idx.val + j.val) % n, Nat.mod_lt _ hn⟩) =
          (fun j : Fin (w + 1) => word ⟨((t.val * w + i.val) + j.val) % n, Nat.mod_lt _ hn⟩) := by
        funext j; congr 1; apply Fin.ext; simp only [hidx]
      rw [hwin, cyclic_window_eq_splice hw hpos eq word t i]
      exact hcyc t i
  simp_rw [hiff]
  exact (regroup hw eq).sum_comp (fun x => if CycleOk fs hpos x then 1 else 0)

def pinHead {d : Nat} (b : Bool) (f : Test (d + 1)) : Test (d + 1) :=
  Fin.cases (fun p => (p 0 == b) && f 0 p) (fun j => f j.succ)

lemma sweepOk_pinHead {d : Nat} (b : Bool) (f : Test (d + 1)) (x y : State d) :
    SweepOk (pinHead b f) x y ↔ x 0 = b ∧ SweepOk f x y := by
  constructor
  · intro h
    have h0 := h 0
    simp only [pinHead, Fin.cases_zero, splice_head, Bool.and_eq_true, beq_iff_eq] at h0
    refine ⟨h0.1, fun i => ?_⟩
    exact Fin.cases h0.2 (fun j => by simpa [pinHead] using h j.succ) i
  · rintro ⟨hx, hf⟩ i
    refine Fin.cases ?_ (fun j => by simpa [pinHead] using hf j.succ) i
    simp only [pinHead, Fin.cases_zero, splice_head, Bool.and_eq_true, beq_iff_eq]
    exact ⟨hx, hf 0⟩

def pinList {d : Nat} (b : Bool) : List (Test (d + 1)) → List (Test (d + 1))
  | [] => []
  | f :: rest => pinHead b f :: rest

lemma len_pinList {d : Nat} (b : Bool) (fs : List (Test (d + 1))) :
    (pinList b fs).length = fs.length := by
  cases fs <;> rfl

lemma ways_pinList {d : Nat} (b : Bool) (fs : List (Test (d + 1))) (hne : fs ≠ []) (x y : State d) :
    ways (pinList b fs) x y = if x 0 = b then ways fs x y else 0 := by
  cases fs with
  | nil => exact absurd rfl hne
  | cons f rest =>
    simp only [pinList, ways, sweepOk_pinHead]
    by_cases hx : x 0 = b <;> simp [hx]

def flipTag {d : Nat} (a : State d) : State d :=
  Fin.cases (!(a 0)) (payload a)

lemma flipTag_invol {d : Nat} (a : State d) : flipTag (flipTag a) = a := by
  funext i
  refine Fin.cases (by simp [flipTag]) (fun j => by simp [flipTag, payload]) i

lemma flipTag_inj {d : Nat} : Function.Injective (@flipTag d) := by
  intro a b h
  have := congrArg flipTag h
  simpa [flipTag_invol] using this

def flipPat {d : Nat} (i : Fin (d + 1)) (p : Word ((d + 1) + 1)) : Word ((d + 1) + 1) :=
  fun j => if (i.val + j.val) % (d + 1) = 0 then !(p j) else p j

lemma flipPat_splice {d : Nat} (a b : State d) (i : Fin (d + 1)) :
    flipPat i (splice a b i) = splice (flipTag a) (flipTag b) i := by
  funext j
  by_cases hlt : i.val + j.val < d + 1
  · simp only [flipPat, splice, hlt, ↓reduceDIte]
    have hmod : (i.val + j.val) % (d + 1) = i.val + j.val := Nat.mod_eq_of_lt hlt
    rw [hmod]
    by_cases hz : i.val + j.val = 0
    · have hfin : (⟨i.val + j.val, hlt⟩ : Fin (d + 1)) = 0 := Fin.ext hz
      simp [hz, hfin, flipTag]
    · let k : Fin d := ⟨i.val + j.val - 1, by omega⟩
      have hfin : (⟨i.val + j.val, hlt⟩ : Fin (d + 1)) = k.succ := Fin.ext (by dsimp [k]; omega)
      rw [if_neg hz, hfin]
      simp [flipTag, payload]
  · simp only [flipPat, splice, hlt, ↓reduceDIte]
    have hsub : i.val + j.val - (d + 1) < d + 1 := by have := i.isLt; have := j.isLt; omega
    have hmod : (i.val + j.val) % (d + 1) = i.val + j.val - (d + 1) := by
      rw [Nat.mod_eq_sub_mod (by omega)]
      exact Nat.mod_eq_of_lt hsub
    rw [hmod]
    by_cases hz : i.val + j.val - (d + 1) = 0
    · have hfin : (⟨i.val + j.val - (d + 1), hsub⟩ : Fin (d + 1)) = 0 := Fin.ext hz
      simp [hz, hfin, flipTag]
    · let k : Fin d := ⟨i.val + j.val - (d + 1) - 1, by omega⟩
      have hfin : (⟨i.val + j.val - (d + 1), hsub⟩ : Fin (d + 1)) = k.succ := Fin.ext (by dsimp [k]; omega)
      simp [hz, hfin, flipTag, payload]

def compTest {d : Nat} (f : Test (d + 1)) : Test (d + 1) :=
  fun i p => f i (flipPat i p)

lemma sweepOk_compTest {d : Nat} (f : Test (d + 1)) (a b : State d) :
    SweepOk (compTest f) a b ↔ SweepOk f (flipTag a) (flipTag b) := by
  simp only [SweepOk, compTest, flipPat_splice]

lemma ways_compTest {d : Nat} (fs : List (Test (d + 1))) (a b : State d) :
    ways (fs.map compTest) a b = ways fs (flipTag a) (flipTag b) := by
  induction fs generalizing a with
  | nil =>
    simp only [List.map_nil, ways]
    by_cases h : a = b
    · subst h; simp
    · have hne : flipTag a ≠ flipTag b := fun he => h (flipTag_inj he)
      simp [h, hne]
  | cons f fs ih =>
    simp only [List.map_cons, ways, sweepOk_compTest, ih]
    let e : State d ≃ State d :=
      { toFun := flipTag, invFun := flipTag, left_inv := flipTag_invol, right_inv := flipTag_invol }
    exact e.sum_comp (fun y => if SweepOk f (flipTag a) y then ways fs y (flipTag b) else 0)

def tagFlipTest {d : Nat} : Test (d + 1) :=
  Fin.cases (fun p => (p 0 == true) && (p (Fin.last (d + 1)) == false))
    (fun _ p => p (Fin.last (d + 1)) == p 0)

lemma sweepOk_tagFlip {d : Nat} (a b : State d) :
    SweepOk (@tagFlipTest d) a b ↔ a 0 = true ∧ b = flipTag a := by
  constructor
  · intro ok
    have h0 := ok 0
    simp only [tagFlipTest, Fin.cases_zero, splice_head, splice_last, Bool.and_eq_true, beq_iff_eq] at h0
    refine ⟨h0.1, funext (fun i => Fin.cases ?_ ?_ i)⟩
    · simp [flipTag, h0.1, h0.2]
    · intro j
      have hj := ok j.succ
      simp only [tagFlipTest, Fin.cases_succ, splice_head, splice_last, beq_iff_eq] at hj
      simpa [flipTag, payload] using hj
  · rintro ⟨ha, rfl⟩ i
    refine Fin.cases ?_ ?_ i
    · simp [tagFlipTest, splice_head, splice_last, flipTag, ha]
    · intro j
      simp [tagFlipTest, splice_head, splice_last, flipTag, payload]

lemma ways_tagFlip {d : Nat} (a b : State d) :
    ways [@tagFlipTest d] a b = if a 0 = true ∧ b = flipTag a then 1 else 0 := by
  simp only [ways, sweepOk_tagFlip]
  by_cases ha : a 0 = true ∧ b = flipTag a
  · rw [Finset.sum_eq_single b]
    · simp [ha]
    · intro y _ hne; simp [hne]
    · simp
  · have hzero : ∀ y : State d,
        (if a 0 = true ∧ y = flipTag a then if y = b then 1 else 0 else 0) = 0 := by
      intro y
      split_ifs with h1 h2
      · subst h2; exact absurd h1 ha
      · rfl
      · rfl
    simp [hzero, ha]

private def mkPat {d : Nat} (z : Payload d) : Word ((d + 1) + 1) := fun j =>
  if h0 : j.val = 0 then false
  else if h : j.val ≤ d then z ⟨j.val - 1, by omega⟩
  else true

private lemma mkPat_zero {d : Nat} (z : Payload d) : mkPat z 0 = false := by
  simp [mkPat]

private lemma mkPat_last {d : Nat} (z : Payload d) : mkPat z (Fin.last (d + 1)) = true := by
  simp only [mkPat, Fin.val_last]
  rw [dif_neg (by omega), dif_neg (by omega)]

private lemma mkPat_mid {d : Nat} (z : Payload d) (j : Fin d) :
    mkPat z j.succ.castSucc = z j := by
  simp only [mkPat, Fin.val_castSucc, Fin.val_succ]
  rw [dif_neg (by omega), dif_pos (by omega)]
  rfl

private theorem solve_clb_057 (d : Nat) :
    let w := d + 1
    let m := 2 ^ d
    let n := 9 * w * m + w
    let D := Fin d → Bool
    let S := Fin n × (Fin (w + 1) → Bool)
    let window := fun (word : Fin n → Bool) (i : Fin n) (j : Fin (w + 1)) =>
      word ⟨(i.val + j.val) % n, Nat.mod_lt _ (by dsimp [n, w, m]; positivity)⟩
    ∃ (base : (D → D → Bool) → (D → D → Bool) → S → Bool) (port : D × D → S),
      Function.Injective port ∧
      (∀ s : S, (∃ c : Bool, ∀ A B, base A B s = c) ∨
        (∃ u v : D, ∀ A B, base A B s = A u v) ∨
        (∃ v z : D, ∀ A B, base A B s = B v z)) ∧
      (∀ A B e, base A B (port e) = false) ∧
      ∀ (A B : D → D → Bool) (enabled : Finset (D × D)),
        (Finset.univ.filter (fun word : Fin n → Bool =>
          ∀ i : Fin n, base A B (i, window word i) = true ∨
            (i, window word i) ∈ enabled.image port)).card =
        (Finset.univ.filter (fun t : D × D × D =>
          A t.1 t.2.1 = true ∧ B t.2.1 t.2.2 = true ∧
            (t.1, t.2.2) ∈ enabled)).card := by
  intro w m n D S window
  have hw_pos : 0 < w := by dsimp [w]; omega
  have hm_pos : 0 < m := by dsimp [m]; positivity
  have hkey_ne : keyList d ≠ [] := by
    intro h
    have := congrArg List.length h
    rw [keylen] at this
    simp at this
  have htests_ne : ∀ E : D → D → Bool, tests E (keyList d) ≠ [] := by
    intro E h
    have hlen := congrArg List.length h
    rw [len_tests, keylen] at hlen
    have h2 : 0 < 2 ^ d := by positivity
    simp only [List.length_nil] at hlen
    omega
  let stage1 (A : D → D → Bool) : List (Test w) := pinList false (tests A (keyList d))
  let stage2 (B : D → D → Bool) : List (Test w) := pinList true ((tests B (keyList d)).map compTest)
  let stage3 (E : D → D → Bool) : List (Test w) := pinList false (tests E (keyList d))
  let fullList (A B E : D → D → Bool) : List (Test w) :=
    stage1 A ++ stage2 B ++ stage3 E ++ [@tagFlipTest d]
  have hlen1 : ∀ A, (stage1 A).length = 3 * m := fun A => by
    dsimp [stage1]; rw [len_pinList, len_tests, keylen]
  have hlen2 : ∀ B, (stage2 B).length = 3 * m := fun B => by
    dsimp [stage2]; rw [len_pinList, List.length_map, len_tests, keylen]
  have hlen3 : ∀ E, (stage3 E).length = 3 * m := fun E => by
    dsimp [stage3]; rw [len_pinList, len_tests, keylen]
  have hlen_full : ∀ A B E, (fullList A B E).length = 9 * m + 1 := fun A B E => by
    dsimp [fullList]
    simp only [List.length_append, List.length_singleton, hlen1, hlen2, hlen3]
    omega
  have hn_eq : ∀ A B E, n = (fullList A B E).length * w := fun A B E => by
    rw [hlen_full]
    dsimp [n, w, m]
    ring
  have hpos_full : ∀ A B E, 0 < (fullList A B E).length := fun A B E => by
    rw [hlen_full]; omega
  let base : (D → D → Bool) → (D → D → Bool) → S → Bool := fun A B s =>
    getPhase (fullList A B (fun _ _ => false)) hw_pos (hn_eq A B (fun _ _ => false)) s.1 s.2
  let port : D × D → S := fun e =>
    let h := diff e.2 e.1
    let q := (Fintype.equivFin (Payload d) h).val
    let idx : Nat := (6 * m + (3 * q + 1)) * w
    have hqlt : q < m := by
      have := (Fintype.equivFin (Payload d) h).isLt
      simpa [m] using this
    have hidx_lt : idx < n := by
      have h1 : 6 * m + (3 * q + 1) < 9 * m + 1 := by omega
      have h2 : (6 * m + (3 * q + 1)) * w < (9 * m + 1) * w := Nat.mul_lt_mul_of_pos_right h1 hw_pos
      have h3 : (9 * m + 1) * w = n := by dsimp [n, w, m]; ring
      omega
    (⟨idx, hidx_lt⟩, mkPat e.2)
  have hport_inj : Function.Injective port := by
    intro ⟨u₁, z₁⟩ ⟨u₂, z₂⟩ heq
    have hp : mkPat z₁ = mkPat z₂ := congrArg Prod.snd heq
    have hz : z₁ = z₂ := by
      funext j
      have h1 := congrFun hp j.succ.castSucc
      rw [mkPat_mid, mkPat_mid] at h1
      exact h1
    subst hz
    have hi : ((port (u₁, z₁)).1).val = ((port (u₂, z₁)).1).val := congrArg (fun s => s.1.val) heq
    dsimp only [port] at hi
    have hmul := Nat.eq_of_mul_eq_mul_right hw_pos hi
    have hqeq : (Fintype.equivFin (Payload d) (diff z₁ u₁)).val =
        (Fintype.equivFin (Payload d) (diff z₁ u₂)).val := by omega
    have hdiff : diff z₁ u₁ = diff z₁ u₂ :=
      (Fintype.equivFin (Payload d)).injective (Fin.ext hqeq)
    have hu : u₁ = u₂ := by
      funext j
      have hj := congrFun hdiff j
      dsimp only [diff] at hj
      cases hz1 : z₁ j <;> cases hu1 : u₁ j <;> cases hu2 : u₂ j <;> simp [hz1, hu1, hu2] at hj ⊢
    subst hu
    rfl
  have htests_getElem : ∀ (E : D → D → Bool) (idx : Nat) (hidx : idx < 3 * m),
      let q := idx / 3
      let h := (Fintype.equivFin (Payload d)).symm ⟨q, by simpa [m] using (Nat.div_lt_iff_lt_mul (by omega : 0 < 3)).mpr (by omega : idx < m * 3)⟩
      (tests E (keyList d))[idx]'(by rw [len_tests, keylen]; exact hidx) =
        if idx % 3 = 0 then maskTest h
        else if idx % 3 = 1 then toggleTest h E
        else maskTest h := by
    intro E idx hidx
    have hgen : ∀ (hs : List (Payload d)) (j : Nat) (hj : j < 3 * hs.length),
        (tests E hs)[j]'(by rw [len_tests]; exact hj) =
          let h := hs[j / 3]'(by rw [Nat.div_lt_iff_lt_mul (by omega : 0 < 3)]; rw [Nat.mul_comm]; exact hj)
          if j % 3 = 0 then maskTest h
          else if j % 3 = 1 then toggleTest h E
          else maskTest h := by
      intro hs
      induction hs with
      | nil => intro j hj; simp at hj
      | cons h0 hs ih =>
        intro j hj
        have hj_lt : j < 3 * hs.length + 3 := by simp only [List.length_cons] at hj; omega
        change (maskTest h0 :: toggleTest h0 E :: maskTest h0 :: tests E hs)[j]'(by simp [len_tests]; omega) = _
        cases j with
        | zero => simp
        | succ j1 =>
          cases j1 with
          | zero => simp
          | succ j2 =>
            cases j2 with
            | zero => simp
            | succ j3 =>
              have hj3 : j3 < 3 * hs.length := by omega
              have hget : (maskTest h0 :: toggleTest h0 E :: maskTest h0 :: tests E hs)[j3 + 3]'(by simp [len_tests]; omega) =
                  (tests E hs)[j3]'(by rw [len_tests]; exact hj3) := rfl
              rw [hget, ih j3 hj3]
              have hdiv : (j3 + 3) / 3 = j3 / 3 + 1 := by omega
              have hmod : (j3 + 3) % 3 = j3 % 3 := by omega
              have hhs : (h0 :: hs)[(j3 + 3) / 3]'(by rw [Nat.div_lt_iff_lt_mul (by omega : 0 < 3)]; simp only [List.length_cons]; omega) =
                  hs[j3 / 3]'(by rw [Nat.div_lt_iff_lt_mul (by omega : 0 < 3)]; omega) := by
                simp only [hdiv]; rfl
              simp only [hmod, hhs]
    have h1 := hgen (keyList d) idx (by rw [keylen]; exact hidx)
    rw [h1]
    have hq_lt : idx / 3 < (keyList d).length := by
      rw [keylen, Nat.div_lt_iff_lt_mul (by omega : 0 < 3)]
      rw [Nat.mul_comm]
      exact hidx
    rw [keyList_getElem d (idx / 3) hq_lt]
  have hpinList_getElem : ∀ (b : Bool) (fs : List (Test w)) (idx : Nat) (hidx : idx < fs.length),
      (pinList b fs)[idx]'(by rw [len_pinList]; exact hidx) =
        if idx = 0 then pinHead b (fs[0]'(by omega)) else fs[idx] := by
    intro b fs
    cases fs with
    | nil => intro idx hidx; simp at hidx
    | cons f rest =>
      intro idx hidx
      cases idx with
      | zero => simp [pinList]
      | succ k => simp [pinList]
  have hfull_getElem : ∀ (A B E : D → D → Bool) (t : Nat) (ht : t < 9 * m + 1),
      (fullList A B E)[t]'(by rw [hlen_full]; exact ht) =
        if h1 : t < 3 * m then (stage1 A)[t]'(by rw [hlen1]; exact h1)
        else if h2 : t < 6 * m then (stage2 B)[t - 3 * m]'(by rw [hlen2]; omega)
        else if h3 : t < 9 * m then (stage3 E)[t - 6 * m]'(by rw [hlen3]; omega)
        else @tagFlipTest d := by
    intro A B E t ht
    dsimp only [fullList]
    by_cases h1 : t < 3 * m
    · rw [dif_pos h1]
      have ha1 : t < (stage1 A ++ stage2 B ++ stage3 E).length := by
        simp [hlen1, hlen2, hlen3]; omega
      rw [List.getElem_append_left ha1]
      have ha2 : t < (stage1 A ++ stage2 B).length := by simp [hlen1, hlen2]; omega
      rw [List.getElem_append_left ha2]
      rw [List.getElem_append_left (by rw [hlen1]; exact h1)]
    · rw [dif_neg h1]
      by_cases h2 : t < 6 * m
      · rw [dif_pos h2]
        have ha1 : t < (stage1 A ++ stage2 B ++ stage3 E).length := by
          simp [hlen1, hlen2, hlen3]; omega
        rw [List.getElem_append_left ha1]
        have ha2 : t < (stage1 A ++ stage2 B).length := by simp [hlen1, hlen2]; omega
        rw [List.getElem_append_left ha2]
        rw [List.getElem_append_right (by rw [hlen1]; omega)]
        simp only [hlen1]
      · rw [dif_neg h2]
        by_cases h3 : t < 9 * m
        · rw [dif_pos h3]
          have ha1 : t < (stage1 A ++ stage2 B ++ stage3 E).length := by
            simp [hlen1, hlen2, hlen3]; omega
          rw [List.getElem_append_left ha1]
          rw [List.getElem_append_right (by simp [hlen1, hlen2]; omega)]
          simp only [List.length_append, hlen1, hlen2, show 3 * m + 3 * m = 6 * m by omega]
        · rw [dif_neg h3]
          rw [List.getElem_append_right (by simp [hlen1, hlen2, hlen3]; omega)]
          simp only [List.length_append, hlen1, hlen2, hlen3]
          have h0 : t - (3 * m + 3 * m + 3 * m) = 0 := by omega
          simp [h0]
  have hbase_proj : ∀ s : S,
      (∃ c : Bool, ∀ A B, base A B s = c) ∨
      (∃ u v : D, ∀ A B, base A B s = A u v) ∨
      (∃ v z : D, ∀ A B, base A B s = B v z) := by
    rintro ⟨idx, pat⟩
    let t := idx.val / w
    let off : Fin w := ⟨idx.val % w, Nat.mod_lt _ hw_pos⟩
    have ht : t < 9 * m + 1 := by
      rw [Nat.div_lt_iff_lt_mul hw_pos]
      have h1 : (9 * m + 1) * w = n := by dsimp [n, w, m]; ring
      rw [h1]; exact idx.isLt
    have hbase_eq : ∀ A B, base A B (idx, pat) =
        ((fullList A B (fun _ _ => false))[t]'(by rw [hlen_full]; exact ht)) off pat := fun A B => rfl
    by_cases h1 : t < 3 * m
    · have h1eq : ∀ A B, ((fullList A B (fun _ _ => false))[t]'(by rw [hlen_full]; exact ht)) off pat =
          (if t = 0 then pinHead false ((tests A (keyList d))[0]'(by rw [len_tests, keylen]; omega))
           else (tests A (keyList d))[t]'(by rw [len_tests, keylen]; exact h1)) off pat := by
        intro A B
        rw [hfull_getElem _ _ _ t ht, dif_pos h1]
        dsimp only [stage1]
        rw [hpinList_getElem false (tests A (keyList d)) t (by rw [len_tests, keylen]; exact h1)]
      simp_rw [hbase_eq, h1eq]
      by_cases ht0 : t = 0
      · simp only [ht0, ↓reduceIte]
        have h0eq : ∀ A : D → D → Bool,
            pinHead false ((tests A (keyList d))[0]'(by rw [len_tests, keylen]; omega)) off pat =
            pinHead false (maskTest ((Fintype.equivFin (Payload d)).symm ⟨0, by simpa [m] using hm_pos⟩)) off pat := by
          intro A
          rw [htests_getElem A 0 (by omega)]
          simp
        exact Or.inl ⟨_, fun A _ => h0eq A⟩
      · simp only [if_neg ht0]
        have hteq : ∀ A : D → D → Bool,
            (tests A (keyList d))[t]'(by rw [len_tests, keylen]; exact h1) =
              let q := t / 3
              let h := (Fintype.equivFin (Payload d)).symm ⟨q, by simpa [m] using (Nat.div_lt_iff_lt_mul (by omega : 0 < 3)).mpr (by omega : t < m * 3)⟩
              if t % 3 = 0 then maskTest h
              else if t % 3 = 1 then toggleTest h A
              else maskTest h := fun A => htests_getElem A t h1
        simp_rw [hteq]
        by_cases hm0 : t % 3 = 0
        · simp only [hm0, ↓reduceIte]; exact Or.inl ⟨_, fun _ _ => rfl⟩
        · by_cases hm1 : t % 3 = 1
          · simp only [hm0, hm1, ↓reduceIte]
            rcases toggle_proj _ off pat with ⟨c, hc⟩ | ⟨u, v, huv⟩
            · exact Or.inl ⟨c, fun A _ => hc A⟩
            · exact Or.inr (Or.inl ⟨u, v, fun A _ => huv A⟩)
          · simp only [hm0, hm1, ↓reduceIte]; exact Or.inl ⟨_, fun _ _ => rfl⟩
    · by_cases h2 : t < 6 * m
      · have h2eq : ∀ A B, ((fullList A B (fun _ _ => false))[t]'(by rw [hlen_full]; exact ht)) off pat =
            (if t - 3 * m = 0 then pinHead true (((tests B (keyList d)).map compTest)[0]'(by rw [List.length_map, len_tests, keylen]; omega))
             else ((tests B (keyList d)).map compTest)[t - 3 * m]'(by rw [List.length_map, len_tests, keylen]; omega)) off pat := by
          intro A B
          rw [hfull_getElem _ _ _ t ht, dif_neg h1, dif_pos h2]
          dsimp only [stage2]
          rw [hpinList_getElem true ((tests B (keyList d)).map compTest) (t - 3 * m)
            (by rw [List.length_map, len_tests, keylen]; omega)]
        simp_rw [hbase_eq, h2eq]
        by_cases ht0 : t - 3 * m = 0
        · simp only [ht0, ↓reduceIte]
          have h0eq : ∀ B : D → D → Bool,
              pinHead true (((tests B (keyList d)).map compTest)[0]'(by rw [List.length_map, len_tests, keylen]; omega)) off pat =
              pinHead true (compTest (maskTest ((Fintype.equivFin (Payload d)).symm ⟨0, by simpa [m] using hm_pos⟩))) off pat := by
            intro B
            rw [List.getElem_map, htests_getElem B 0 (by omega)]
            simp
          exact Or.inl ⟨_, fun _ B => h0eq B⟩
        · simp only [if_neg ht0]
          have hteq : ∀ B : D → D → Bool,
              ((tests B (keyList d)).map compTest)[t - 3 * m]'(by rw [List.length_map, len_tests, keylen]; omega) =
                compTest (
                  let q := (t - 3 * m) / 3
                  let h := (Fintype.equivFin (Payload d)).symm ⟨q, by simpa [m] using (Nat.div_lt_iff_lt_mul (by omega : 0 < 3)).mpr (by omega : t - 3 * m < m * 3)⟩
                  if (t - 3 * m) % 3 = 0 then maskTest h
                  else if (t - 3 * m) % 3 = 1 then toggleTest h B
                  else maskTest h) := by
            intro B
            rw [List.getElem_map, htests_getElem B (t - 3 * m) (by omega)]
          simp_rw [hteq]
          by_cases hm0 : (t - 3 * m) % 3 = 0
          · simp only [hm0, ↓reduceIte]; exact Or.inl ⟨_, fun _ _ => rfl⟩
          · by_cases hm1 : (t - 3 * m) % 3 = 1
            · simp only [hm0, hm1, ↓reduceIte, compTest]
              rcases toggle_proj _ off (flipPat off pat) with ⟨c, hc⟩ | ⟨v, z, hvz⟩
              · exact Or.inl ⟨c, fun _ B => hc B⟩
              · exact Or.inr (Or.inr ⟨v, z, fun _ B => hvz B⟩)
            · simp only [hm0, hm1, ↓reduceIte]; exact Or.inl ⟨_, fun _ _ => rfl⟩
      · by_cases h3 : t < 9 * m
        · have h3eq : ∀ A B, base A B (idx, pat) = ((stage3 (fun _ _ => false))[t - 6 * m]'(by rw [hlen3]; omega)) off pat := by
            intro A B; rw [hbase_eq, hfull_getElem _ _ _ t ht, dif_neg h1, dif_neg h2, dif_pos h3]
          exact Or.inl ⟨_, h3eq⟩
        · have h4eq : ∀ A B, base A B (idx, pat) = (@tagFlipTest d) off pat := by
            intro A B; rw [hbase_eq, hfull_getElem _ _ _ t ht, dif_neg h1, dif_neg h2, dif_neg h3]
          exact Or.inl ⟨_, h4eq⟩
  have hbase_port_false : ∀ A B e, base A B (port e) = false := by
    intro A B ⟨u, z⟩
    let h := diff z u
    let q := (Fintype.equivFin (Payload d) h).val
    have hqlt : q < m := by
      have := (Fintype.equivFin (Payload d) h).isLt
      simpa [m] using this
    let t := 6 * m + (3 * q + 1)
    have ht : t < 9 * m + 1 := by omega
    have hdiv : (t * w) / w = t := Nat.mul_div_cancel t hw_pos
    have hmod : (t * w) % w = 0 := Nat.mul_mod_left t w
    have hbase_eq : base A B (port (u, z)) =
        ((fullList A B (fun _ _ => false))[t]'(by rw [hlen_full]; exact ht)) 0 (mkPat z) := by
      unfold base getPhase
      dsimp only [port]
      have h0 : (⟨(t * w) % w, Nat.mod_lt _ hw_pos⟩ : Fin w) = 0 := Fin.ext hmod
      rw [h0]
      exact congrFun (congrFun (getElem_congr (c := fullList A B (fun _ _ => false)) rfl hdiv (by rw [hdiv, hlen_full]; exact ht)) 0) (mkPat z)
    rw [hbase_eq, hfull_getElem _ _ _ t ht]
    have h1 : ¬ t < 3 * m := by omega
    have h2 : ¬ t < 6 * m := by omega
    have h3 : t < 9 * m := by omega
    rw [dif_neg h1, dif_neg h2, dif_pos h3]
    dsimp only [stage3]
    rw [hpinList_getElem false (tests (fun _ _ => false) (keyList d)) (t - 6 * m) (by rw [len_tests, keylen]; omega)]
    have hne0 : t - 6 * m ≠ 0 := by omega
    rw [if_neg hne0, htests_getElem (fun _ _ => false) (t - 6 * m) (by omega)]
    have hmod3 : (t - 6 * m) % 3 = 1 := by dsimp [t]; omega
    simp only [hmod3, show ¬ (1 = 0) by omega, ↓reduceIte, toggleTest, Fin.cases_zero, mkPat_zero, mkPat_last]
    rfl
  refine ⟨base, port, hport_inj, hbase_proj, hbase_port_false, ?_⟩
  intro A B enabled
  let E : D → D → Bool := fun z u => decide ((u, z) ∈ enabled)
  have hrow_equiv : ∀ (i : Fin n) (pat : Fin (w + 1) → Bool),
      (base A B (i, pat) = true ∨ (i, pat) ∈ enabled.image port) ↔
      getPhase (fullList A B E) hw_pos (hn_eq A B E) i pat = true := by
    intro i pat
    let t := i.val / w
    let off : Fin w := ⟨i.val % w, Nat.mod_lt _ hw_pos⟩
    have ht : t < 9 * m + 1 := by
      rw [Nat.div_lt_iff_lt_mul hw_pos]
      have h1 : (9 * m + 1) * w = n := by dsimp [n, w, m]; ring
      rw [h1]; exact i.isLt
    have hL : base A B (i, pat) = ((fullList A B (fun _ _ => false))[t]'(by rw [hlen_full]; exact ht)) off pat := rfl
    have hR : getPhase (fullList A B E) hw_pos (hn_eq A B E) i pat =
        ((fullList A B E)[t]'(by rw [hlen_full]; exact ht)) off pat := rfl
    rw [hL, hR, hfull_getElem _ _ _ t ht, hfull_getElem _ _ _ t ht]
    by_cases h1 : t < 3 * m
    · rw [dif_pos h1, dif_pos h1]
      have hnot_port : (i, pat) ∉ enabled.image port := by
        intro hmem
        rcases Finset.mem_image.mp hmem with ⟨e, _, heq⟩
        have hi : ((port e).1).val = i.val := congrArg (fun s => s.1.val) heq
        dsimp only [port] at hi
        have hdiv : i.val / w = 6 * m + (3 * (Fintype.equivFin (Payload d) (diff e.2 e.1)).val + 1) := by
          rw [← hi, Nat.mul_div_cancel _ hw_pos]
        omega
      simp [hnot_port]
    · rw [dif_neg h1, dif_neg h1]
      by_cases h2 : t < 6 * m
      · rw [dif_pos h2, dif_pos h2]
        have hnot_port : (i, pat) ∉ enabled.image port := by
          intro hmem
          rcases Finset.mem_image.mp hmem with ⟨e, _, heq⟩
          have hi : ((port e).1).val = i.val := congrArg (fun s => s.1.val) heq
          dsimp only [port] at hi
          have hdiv : i.val / w = 6 * m + (3 * (Fintype.equivFin (Payload d) (diff e.2 e.1)).val + 1) := by
            rw [← hi, Nat.mul_div_cancel _ hw_pos]
          omega
        simp [hnot_port]
      · rw [dif_neg h2, dif_neg h2]
        by_cases h3 : t < 9 * m
        · rw [dif_pos h3, dif_pos h3]
          dsimp only [stage3]
          rw [hpinList_getElem false (tests _ (keyList d)) (t - 6 * m) (by rw [len_tests, keylen]; omega),
              hpinList_getElem false (tests _ (keyList d)) (t - 6 * m) (by rw [len_tests, keylen]; omega)]
          by_cases ht0 : t - 6 * m = 0
          · rw [if_pos ht0, if_pos ht0]
            have hnot_port : (i, pat) ∉ enabled.image port := by
              intro hmem
              rcases Finset.mem_image.mp hmem with ⟨e, _, heq⟩
              have hi : ((port e).1).val = i.val := congrArg (fun s => s.1.val) heq
              dsimp only [port] at hi
              have hdiv : i.val / w = 6 * m + (3 * (Fintype.equivFin (Payload d) (diff e.2 e.1)).val + 1) := by
                rw [← hi, Nat.mul_div_cancel _ hw_pos]
              omega
            simp [hnot_port, htests_getElem _ 0 (by omega)]
          · rw [if_neg ht0, if_neg ht0,
                htests_getElem _ (t - 6 * m) (by omega), htests_getElem _ (t - 6 * m) (by omega)]
            by_cases hm0 : (t - 6 * m) % 3 = 0
            · rw [if_pos hm0, if_pos hm0]
              have hnot_port : (i, pat) ∉ enabled.image port := by
                intro hmem
                rcases Finset.mem_image.mp hmem with ⟨e, _, heq⟩
                have hi : ((port e).1).val = i.val := congrArg (fun s => s.1.val) heq
                dsimp only [port] at hi
                have hdiv : i.val / w = 6 * m + (3 * (Fintype.equivFin (Payload d) (diff e.2 e.1)).val + 1) := by
                  rw [← hi, Nat.mul_div_cancel _ hw_pos]
                omega
              simp [hnot_port]
            · rw [if_neg hm0, if_neg hm0]
              by_cases hm1 : (t - 6 * m) % 3 = 1
              · rw [if_pos hm1, if_pos hm1]
                by_cases hoff0 : off = 0
                · rw [hoff0]
                  simp only [toggleTest, Fin.cases_zero]
                  by_cases hsame : (pat (Fin.last (d + 1)) == pat 0) = true
                  · simp only [hsame, ↓reduceIte, true_or]
                  · simp only [hsame, ↓reduceIte]
                    by_cases hp0 : pat 0 = true
                    · have hnot_port : (i, pat) ∉ enabled.image port := by
                        intro hmem
                        rcases Finset.mem_image.mp hmem with ⟨e, _, heq⟩
                        have hp : mkPat e.2 = pat := congrArg Prod.snd heq
                        have h0 := congrFun hp 0
                        rw [mkPat_zero, hp0] at h0; cases h0
                      simp [hp0, hnot_port]
                    · have hp0f : pat 0 = false := by cases h : pat 0 <;> simp_all
                      have hplast : pat (Fin.last (d + 1)) = true := by
                        cases h : pat (Fin.last (d + 1)) <;> simp_all
                      simp only [hp0f, Bool.false_eq_true, ↓reduceIte, false_or]
                      let h := (Fintype.equivFin (Payload d)).symm
                        ⟨(t - 6 * m) / 3, by
                          simpa [m] using (Nat.div_lt_iff_lt_mul (by omega : 0 < 3)).mpr
                            (by omega : t - 6 * m < m * 3)⟩
                      let z : D := fun j => pat j.succ.castSucc
                      let u : D := diff z h
                      have hdiff_zu : diff z u = h := by
                        funext j; dsimp [u, diff]; cases z j <;> cases h j <;> rfl
                      have hpat_eq : mkPat z = pat := by
                        funext j
                        by_cases hj0 : j.val = 0
                        · have hj : j = 0 := Fin.ext hj0
                          rw [hj, mkPat_zero, hp0f]
                        · by_cases hjd : j.val ≤ d
                          · let k : Fin d := ⟨j.val - 1, by omega⟩
                            have hj : j = k.succ.castSucc := Fin.ext (by dsimp [k]; omega)
                            rw [hj, mkPat_mid]
                          · have hj : j = Fin.last w := Fin.ext (by dsimp [w]; omega)
                            rw [hj, mkPat_last, hplast]
                      have hi_eq : (port (u, z)).1 = i := by
                        apply Fin.ext
                        dsimp only [port]
                        rw [hdiff_zu]
                        have hq : (Fintype.equivFin (Payload d) h).val = (t - 6 * m) / 3 := by
                          dsimp [h]
                          simp
                        rw [hq]
                        have ht_eq : 6 * m + (3 * ((t - 6 * m) / 3) + 1) = t := by omega
                        rw [ht_eq]
                        have hmod0 : i.val % w = 0 := congrArg Fin.val hoff0
                        have hdm := Nat.div_add_mod i.val w
                        rw [hmod0, Nat.add_zero, Nat.mul_comm] at hdm
                        exact hdm
                      have hport_eq : port (u, z) = (i, pat) := Prod.ext hi_eq hpat_eq
                      rw [← hport_eq, Finset.mem_image]
                      constructor
                      · rintro ⟨e, he, hpe⟩
                        have heq : e = (u, z) := hport_inj hpe
                        subst heq
                        simp only [E, decide_eq_true_eq]
                        exact he
                      · intro hE
                        simp only [E, decide_eq_true_eq] at hE
                        exact ⟨(u, z), hE, rfl⟩
                · have hnot_port : (i, pat) ∉ enabled.image port := by
                    intro hmem
                    rcases Finset.mem_image.mp hmem with ⟨e, _, heq⟩
                    have hi : ((port e).1).val = i.val := congrArg (fun s => s.1.val) heq
                    dsimp only [port] at hi
                    have hmod0 : i.val % w = 0 := by rw [← hi, Nat.mul_mod_left]
                    exact hoff0 (Fin.ext hmod0)
                  simp only [hnot_port, or_false]
                  have hsucc : ∃ j : Fin d, off = j.succ := by
                    refine ⟨⟨off.val - 1, by have := off.isLt; dsimp [w] at this; omega⟩, Fin.ext ?_⟩
                    have hne0 : off.val ≠ 0 := fun h => hoff0 (Fin.ext h)
                    dsimp; omega
                  rcases hsucc with ⟨j, hj⟩
                  rw [hj]
                  simp [toggleTest]
              · rw [if_neg hm1, if_neg hm1]
                have hnot_port : (i, pat) ∉ enabled.image port := by
                  intro hmem
                  rcases Finset.mem_image.mp hmem with ⟨e, _, heq⟩
                  have hi : ((port e).1).val = i.val := congrArg (fun s => s.1.val) heq
                  dsimp only [port] at hi
                  have hdiv : i.val / w = 6 * m + (3 * (Fintype.equivFin (Payload d) (diff e.2 e.1)).val + 1) := by
                    rw [← hi, Nat.mul_div_cancel _ hw_pos]
                  omega
                simp [hnot_port]
        · rw [dif_neg h3, dif_neg h3]
          have hnot_port : (i, pat) ∉ enabled.image port := by
            intro hmem
            rcases Finset.mem_image.mp hmem with ⟨e, _, heq⟩
            have hi : ((port e).1).val = i.val := congrArg (fun s => s.1.val) heq
            dsimp only [port] at hi
            have hdiv : i.val / w = 6 * m + (3 * (Fintype.equivFin (Payload d) (diff e.2 e.1)).val + 1) := by
              rw [← hi, Nat.mul_div_cancel _ hw_pos]
            have hqlt : (Fintype.equivFin (Payload d) (diff e.2 e.1)).val < m := by
              have := (Fintype.equivFin (Payload d) (diff e.2 e.1)).isLt
              simpa [m] using this
            omega
          simp [hnot_port]
  have hfilt_eq :
      (Finset.univ.filter (fun word : Fin n → Bool =>
        ∀ i : Fin n, base A B (i, window word i) = true ∨
          (i, window word i) ∈ enabled.image port)) =
      (Finset.univ.filter (fun word : Word n =>
        ∀ i : Fin n, getPhase (fullList A B E) hw_pos (hn_eq A B E) i
          (fun j => word ⟨(i.val + j.val) % n, Nat.mod_lt _ (by dsimp [n, w, m]; positivity)⟩) = true)) := by
    ext word
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact forall_congr' (fun i => hrow_equiv i (window word i))
  rw [hfilt_eq, cyclic_count (fullList A B E) hw_pos (hpos_full A B E) (hn_eq A B E)]
  have hways_s1 : ∀ s₀ s₁ : State d,
      ways (stage1 A) s₀ s₁ =
        if s₀ 0 = false then
          (if s₀ = s₁ then 1 else 0) +
          (if s₀ 0 = false ∧ s₁ 0 = true ∧ A (payload s₀) (payload s₁) = true then 1 else 0)
        else 0 := by
    intro s₀ s₁
    dsimp only [stage1]
    rw [ways_pinList false _ (htests_ne A), net_result]
  have hways_s2 : ∀ s₁ s₂ : State d,
      ways (stage2 B) s₁ s₂ =
        if s₁ 0 = true then
          (if flipTag s₁ = flipTag s₂ then 1 else 0) +
          (if (flipTag s₁) 0 = false ∧ (flipTag s₂) 0 = true ∧
              B (payload (flipTag s₁)) (payload (flipTag s₂)) = true then 1 else 0)
        else 0 := by
    intro s₁ s₂
    dsimp only [stage2]
    have hne : (tests B (keyList d)).map compTest ≠ [] := by
      intro h; exact htests_ne B (List.map_eq_nil_iff.mp h)
    rw [ways_pinList true _ hne, ways_compTest, net_result]
  have hways_s3 : ∀ s₂ s₃ : State d,
      ways (stage3 E) s₂ s₃ =
        if s₂ 0 = false then
          (if s₂ = s₃ then 1 else 0) +
          (if s₂ 0 = false ∧ s₃ 0 = true ∧ E (payload s₂) (payload s₃) = true then 1 else 0)
        else 0 := by
    intro s₂ s₃
    dsimp only [stage3]
    rw [ways_pinList false _ (htests_ne E), net_result]
  have hsum_full :
      (∑ s₀ : State d, ways (fullList A B E) s₀ s₀) =
      ∑ u : D, ∑ v : D, ∑ z : D,
        if A u v = true ∧ B v z = true ∧ (u, z) ∈ enabled then 1 else 0 := by
    have hexpand : ∀ s₀ : State d,
        ways (fullList A B E) s₀ s₀ =
        ∑ s₁ : State d, ∑ s₂ : State d, ∑ s₃ : State d,
          ways (stage1 A) s₀ s₁ * ways (stage2 B) s₁ s₂ * ways (stage3 E) s₂ s₃ *
            ways [@tagFlipTest d] s₃ s₀ := by
      intro s₀
      have hassoc : fullList A B E = stage1 A ++ (stage2 B ++ (stage3 E ++ [@tagFlipTest d])) := by
        dsimp only [fullList]
        simp [List.append_assoc]
      rw [hassoc, ways_append (stage1 A)]
      apply Finset.sum_congr rfl; intro s₁ _
      rw [ways_append (stage2 B), Finset.mul_sum]
      apply Finset.sum_congr rfl; intro s₂ _
      rw [ways_append (stage3 E), Finset.mul_sum, Finset.mul_sum]
      apply Finset.sum_congr rfl; intro s₃ _
      ring
    simp_rw [hexpand]
    let mkS : Bool → D → State d := fun b u => Fin.cases b u
    let hmk_equiv : (Bool × D) ≃ State d :=
      { toFun := fun p => mkS p.1 p.2
        invFun := fun s => (s 0, payload s)
        left_inv := fun ⟨b, u⟩ => by
          apply Prod.ext
          · simp [mkS]
          · funext j; simp [mkS, payload]
        right_inv := fun s => by
          funext i; refine Fin.cases (by simp [mkS]) (fun j => by simp [mkS, payload]) i }
    have hsum_state : ∀ f : State d → Nat, (∑ s : State d, f s) = ∑ u : D, f (mkS false u) + ∑ u : D, f (mkS true u) := by
      intro f
      rw [← hmk_equiv.sum_comp f, Fintype.sum_prod_type]
      dsimp only [hmk_equiv]
      rw [Fintype.sum_bool, Nat.add_comm]
      rfl
    have hterm_zero_s0 : ∀ u : D,
        (∑ s₁ : State d, ∑ s₂ : State d, ∑ s₃ : State d,
          ways (stage1 A) (mkS true u) s₁ * ways (stage2 B) s₁ s₂ * ways (stage3 E) s₂ s₃ *
            ways [@tagFlipTest d] s₃ (mkS true u)) = 0 := by
      intro u
      apply Finset.sum_eq_zero; intro s₁ _
      apply Finset.sum_eq_zero; intro s₂ _
      apply Finset.sum_eq_zero; intro s₃ _
      rw [hways_s1]
      simp [mkS]
    rw [hsum_state]
    simp_rw [hterm_zero_s0, Finset.sum_const_zero, Nat.add_zero]
    apply Finset.sum_congr rfl; intro u _
    have hterm_zero_s1 : ∀ v : D,
        (∑ s₂ : State d, ∑ s₃ : State d,
          ways (stage1 A) (mkS false u) (mkS false v) * ways (stage2 B) (mkS false v) s₂ *
            ways (stage3 E) s₂ s₃ * ways [@tagFlipTest d] s₃ (mkS false u)) = 0 := by
      intro v
      apply Finset.sum_eq_zero; intro s₂ _
      apply Finset.sum_eq_zero; intro s₃ _
      rw [hways_s2]
      simp [mkS]
    rw [hsum_state]
    simp_rw [hterm_zero_s1, Finset.sum_const_zero, Nat.zero_add]
    apply Finset.sum_congr rfl; intro v _
    have hterm_zero_s2 : ∀ z : D,
        (∑ s₃ : State d,
          ways (stage1 A) (mkS false u) (mkS true v) * ways (stage2 B) (mkS true v) (mkS true z) *
            ways (stage3 E) (mkS true z) s₃ * ways [@tagFlipTest d] s₃ (mkS false u)) = 0 := by
      intro z
      apply Finset.sum_eq_zero; intro s₃ _
      rw [hways_s3]
      simp [mkS]
    rw [hsum_state]
    simp_rw [hterm_zero_s2, Finset.sum_const_zero, Nat.add_zero]
    apply Finset.sum_congr rfl; intro z _
    rw [Finset.sum_eq_single (mkS true u)]
    · have hne01 : mkS false u ≠ mkS true v := fun h => by
        have := congrFun h 0; simp [mkS] at this
      have hne12 : mkS false v ≠ mkS true z := fun h => by
        have := congrFun h 0; simp [mkS] at this
      have hne23 : mkS false z ≠ mkS true u := fun h => by
        have := congrFun h 0; simp [mkS] at this
      have hpl : ∀ b (x : D), payload (mkS b x) = x := fun b x => by funext j; simp [payload, mkS]
      have hfl : ∀ b (x : D), flipTag (mkS b x) = mkS (!b) x := fun b x => by
        funext i; refine Fin.cases (by simp [flipTag, mkS]) (fun j => by simp [flipTag, payload, mkS]) i
      have h0b : ∀ b (x : D), mkS b x 0 = b := fun b x => by simp [mkS]
      rw [hways_s1, hways_s2, hways_s3, ways_tagFlip]
      simp only [hfl, Bool.not_true, Bool.not_false, hpl, h0b, hne01, hne12, hne23,
        ite_true, ite_false, Nat.zero_add, true_and, E, decide_eq_true_eq]
      by_cases hA : A u v = true <;> by_cases hB : B v z = true <;> by_cases hE : (u, z) ∈ enabled <;>
        simp [hA, hB, hE]
    · intro s₃ _ hne
      rw [ways_tagFlip]
      have hnot : ¬ (s₃ 0 = true ∧ mkS false u = flipTag s₃) := by
        rintro ⟨h0, heq⟩
        apply hne
        have h1 := congrArg flipTag heq
        rw [flipTag_invol] at h1
        rw [← h1]
        funext i
        refine Fin.cases (by simp [flipTag, mkS]) (fun j => by simp [flipTag, payload, mkS]) i
      simp [hnot]
    · simp
  rw [hsum_full, Finset.card_filter]
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl; intro u _
  rw [Fintype.sum_prod_type]

end PEqualNP.Outside.L_clb_057_aux

theorem PEqualNP.Outside.L_clb_057 :
∀ d : ℕ,
  let w := d + 1
  let m := 2 ^ d
  let n := 9 * w * m + w
  let D := Fin d → Bool
  let S := Fin n × (Fin (w + 1) → Bool)
  let window := fun (word : Fin n → Bool) (i : Fin n) (j : Fin (w + 1)) =>
    word ⟨(i.val + j.val) % n, Nat.mod_lt _ (by dsimp [n, w, m]; positivity)⟩
  ∃ (base : (D → D → Bool) → (D → D → Bool) → S → Bool) (port : D × D → S),
    Function.Injective port ∧
    (∀ s : S, (∃ c : Bool, ∀ A B, base A B s = c) ∨
      (∃ u v : D, ∀ A B, base A B s = A u v) ∨
      (∃ v z : D, ∀ A B, base A B s = B v z)) ∧
    (∀ A B e, base A B (port e) = false) ∧
    ∀ (A B : D → D → Bool) (enabled : Finset (D × D)),
      (Finset.univ.filter (fun word : Fin n → Bool =>
        ∀ i : Fin n, base A B (i, window word i) = true ∨
          (i, window word i) ∈ enabled.image port)).card =
      (Finset.univ.filter (fun t : D × D × D =>
        A t.1 t.2.1 = true ∧ B t.2.1 t.2.2 = true ∧
          (t.1, t.2.2) ∈ enabled)).card :=
  PEqualNP.Outside.L_clb_057_aux.solve_clb_057
