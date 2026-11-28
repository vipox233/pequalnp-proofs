import PEqualNP.Library.Helpers.L17550Bounded

namespace PEqualNP.MetaComplexity.L17550Projection.FreeOr

open Bounded

abbrev Mask := BitVec 8
abbrev Operand := Mask × Bool
abbrev Term := Operand × Operand

private def columns : List (Nat × Word) :=
  [(0,63491),(1,1386508),(2,235568),(3,151748),(4,287504),(5,558408),(6,1246721),(7,1835170)]

private def selected (s : Mask) : List (Nat × Word) → Word
  | [] => 0
  | (i,a) :: xs => (if s.getLsbD i then a else 0) ||| selected s xs

def seedUnion (s : Mask) : Word := selected s columns

private theorem or_left_comm (a b c : Word) : a ||| (b ||| c) = b ||| (a ||| c) := by ac_rfl
private theorem or_left_idem (a b : Word) : a ||| (a ||| b) = a ||| b := by
  rw [← BitVec.or_assoc,BitVec.or_self]

private theorem selected_or (u v : Mask) (xs : List (Nat × Word)) :
    selected (u ||| v) xs = selected u xs ||| selected v xs := by
  induction xs with
  | nil => simp [selected]
  | cons x xs ih =>
    rcases x with ⟨i,a⟩
    simp only [selected,BitVec.getLsbD_or,ih]
    cases hu : u.getLsbD i <;> cases hv : v.getLsbD i <;>
      simp [BitVec.or_assoc,BitVec.or_comm,or_left_comm, or_left_idem]

def operand (d : Word) (o : Operand) := seedUnion o.1 ||| (if o.2 then d else 0)
private def joins (a b : Operand) : Operand := (a.1 ||| b.1, a.2 || b.2)

private theorem operand_join (d : Word) (a b : Operand) :
    operand d (joins a b) = operand d a ||| operand d b := by
  obtain ⟨ma,fa⟩ := a
  obtain ⟨mb,fb⟩ := b
  cases fa <;> cases fb <;> simp [operand,joins,seedUnion,selected_or,
    BitVec.or_assoc,BitVec.or_comm,or_left_comm,or_left_idem]

def term (d : Word) (p : Term) := operand d p.1 &&& operand d p.2

def fits (u v : Mask) (ts : List Term) : Bool :=
  let d := seedUnion u &&& seedUnion v
  ts.all (fun t => (term d t &&& 2095104) == 0) &&
    ((ts.foldl (fun acc t => acc ||| term d t) 0 &&& 2047) == 2047)

/-- Only the two pre-AND masks, six terminal masks and six optional-use flags are symbolic. -/
def RejectThree : Prop := ∀ (u v : Mask) (a b c : Term), fits u v [a,b,c] = false

private theorem seed_zero : seedUnion 0#8 = 0#21 := by decide
private theorem enc_zero (d : Word) : operand d (0#8,false) = 0#21 := by simp [operand,seed_zero]

private def Pure (w : List Word) := ∀ a ∈ w, ∃ u, seedUnion u = a
private def After (d : Word) (w : List Word) := ∀ a ∈ w, ∃ o, operand d o = a

private theorem seed_pure : Pure (seeds.map (BitVec.ofNat 21)) := by
  let tags : List Mask := [1,2,4,0,8,16,0,0,32,64,128,0,64,128,0,0]
  have eqn : tags.map seedUnion = seeds.map (BitVec.ofNat 21) := by decide
  intro a ha
  rw [←eqn] at ha
  obtain ⟨u,_,hu⟩ := List.mem_map.mp ha
  exact ⟨u,hu⟩

private theorem read_prop {P : Word → Prop} (hz : P 0) {w : List Word} (h : ∀ a ∈ w, P a)
    (i : Idx) : P (read w i) := by
  induction w generalizing i with
  | nil => exact hz
  | cons a xs ih =>
    unfold Bounded.read
    split
    · exact h a (by simp)
    · exact ih (fun z hz => h z (by simp [hz])) _

private theorem lift_pure {w : List Word} (h : Pure w) (d : Word) : After d w := by
  intro a ha
  obtain ⟨u,rfl⟩ := h a ha
  exact ⟨(u,false),by simp [operand]⟩

private theorem append_prop {P : Word → Prop} {w : List Word} {v : Word}
    (hw : ∀ a ∈ w, P a) (hv : P v) : ∀ a ∈ w ++ [v], P a := by
  intro a ha
  rcases List.mem_append.mp ha with ht | ht
  · exact hw a ht
  · simpa only [List.mem_singleton.mp ht] using hv

private theorem pure_or (w : List Word) (g : Op) (h : Pure w) (hg : g.1 = false) :
    Pure (advance w g) := by
  obtain ⟨u,hu⟩ := read_prop (P := fun a => ∃ m, seedUnion m = a) ⟨0,seed_zero⟩ h g.2.1
  obtain ⟨v,hv⟩ := read_prop (P := fun a => ∃ m, seedUnion m = a) ⟨0,seed_zero⟩ h g.2.2
  unfold advance
  rw [hg]
  apply append_prop h
  exact ⟨u ||| v,(selected_or u v columns).trans (by rw [←hu,←hv]; rfl)⟩

private theorem after_or (d : Word) (w : List Word) (g : Op) (h : After d w) (hg : g.1 = false) :
    After d (advance w g) := by
  obtain ⟨u,hu⟩ := read_prop (P := fun a => ∃ m, operand d m = a) ⟨_,enc_zero d⟩ h g.2.1
  obtain ⟨v,hv⟩ := read_prop (P := fun a => ∃ m, operand d m = a) ⟨_,enc_zero d⟩ h g.2.2
  unfold advance
  rw [hg]
  apply append_prop h
  exact ⟨joins u v, by simpa [hu,hv] using operand_join d u v⟩

private theorem rest (d : Word) (gs : List Op) (w : List Word) (h : After d w)
    (hb : withinAndBudget true gs = true) : After d (gs.foldl advance w) := by
  induction gs generalizing w with
  | nil => exact h
  | cons g gs ih =>
    cases hg : g.1 <;> simp [withinAndBudget,hg] at hb
    exact ih _ (after_or d w g h hg) hb

private theorem normal (gs : List Op) (w : List Word) (h : Pure w)
    (hb : withinAndBudget false gs = true) :
    ∃ u v, After (seedUnion u &&& seedUnion v) (gs.foldl advance w) := by
  induction gs generalizing w with
  | nil => exact ⟨0,0,lift_pure h _⟩
  | cons g gs ih =>
    cases hg : g.1 <;> simp [withinAndBudget,hg] at hb
    · exact ih _ (pure_or w g h hg) hb
    · obtain ⟨u,hu⟩ := read_prop (P := fun a => ∃ m, seedUnion m = a) ⟨0,seed_zero⟩ h g.2.1
      obtain ⟨v,hv⟩ := read_prop (P := fun a => ∃ m, seedUnion m = a) ⟨0,seed_zero⟩ h g.2.2
      let d := seedUnion u &&& seedUnion v
      refine ⟨u,v,rest d gs (advance w g) ?_ hb⟩
      unfold advance
      rw [hg]
      apply append_prop (lift_pure h d)
      exact ⟨(0,true),by simp [operand,seed_zero,d,hu,hv,product]⟩

private def productsFit (xs : List Word) :=
  xs.all (fun z => (z &&& 2095104) == 0) &&
    ((xs.foldl (· ||| ·) 0 &&& 2047) == 2047)

/-- Every program with a fit gives as many free-OR products as it has terminal pairs. -/
theorem normalize {gs : List Op} {ps : List Terminal} (h : accepts gs ps = true) :
    ∃ (u v : Mask) (ts : List Term), ts.length = ps.length ∧ fits u v ts = true := by
  classical
  let w := gs.foldl advance (seeds.map (BitVec.ofNat 21))
  have hb : withinAndBudget false gs = true := by
    simp only [accepts,Bool.and_eq_true] at h
    exact h.1.1
  obtain ⟨u,v,hn⟩ := normal gs _ seed_pure hb
  let d := seedUnion u &&& seedUnion v
  have source (i : Idx) : ∃ s, operand d s = read w i :=
    read_prop (P := fun a => ∃ s, operand d s = a) ⟨_,enc_zero d⟩ hn i
  let chooseTag := fun i => (source i).choose
  let rewire := fun p : Terminal => (chooseTag p.1,chooseTag p.2)
  have wire (p : Terminal) : term d (rewire p) = product w p := by
    exact congrArg₂ (· &&& ·) (source p.1).choose_spec (source p.2).choose_spec
  refine ⟨u,v,ps.map rewire,by simp,?_⟩
  have hr : productsFit (ps.map (product w)) = true := by
    simpa [productsFit,List.foldl_map,List.all_map,Function.comp_def,accepts,hb,w] using h
  have hm : (ps.map rewire).map (term d) = ps.map (product w) := by
    simp [List.map_map,Function.comp_def,wire]
  rw [← hm] at hr
  simpa [productsFit,List.foldl_map,List.all_map,Function.comp_def,fits,d] using hr

private def blank : Term := ((0,false),(0,false))

private theorem pad_blank (u v : Mask) (ps : List Term) :
    fits u v (ps ++ [blank]) = fits u v ps := by
  simp [fits,List.foldl_append,blank,term,enc_zero]

theorem small_of_rejectThree (exc : RejectThree) {gs : List Gate} {ps : List Pair}
    (h : Admissible gs ps) (hq : ps.length ≤ 3) : False := by
  obtain ⟨g',p',hp,hh⟩ : ∃ (g' : List Op) (p' : List Terminal),
      p'.length = ps.length ∧ accepts g' p' = true :=
    ⟨_,_,List.length_map _,encode h⟩
  obtain ⟨u,v,ts,hl,ht⟩ := normalize hh
  have hs : ts.length ≤ 3 := by omega
  have pad (qs : List Term) (hfit : fits u v qs = true) : fits u v (qs ++ [blank]) = true :=
    (pad_blank u v qs).trans hfit
  cases ts with
  | nil => simpa [exc u v blank blank blank] using pad _ (pad _ (pad _ ht))
  | cons a ts =>
    cases ts with
    | nil => simpa [exc u v a blank blank] using pad _ (pad _ ht)
    | cons b ts =>
      cases ts with
      | nil => simpa [exc u v a b blank] using pad _ ht
      | cons c ts =>
        cases ts with
        | nil => simp [exc u v a b c] at ht
        | cons x xs => simp at hs; omega

/-- Assemble the native claim from the free-OR exclusion and four bounded replays. -/
theorem of_replays (small : RejectThree)
    (four : Reject 7 4) (five : Reject 5 5) (six : Reject 3 6) (seven : Reject 1 7) : Claim :=
  of_four_replays (fun _ _ h hq => small_of_rejectThree small h hq) four five six seven

end PEqualNP.MetaComplexity.L17550Projection.FreeOr
