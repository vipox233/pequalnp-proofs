import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_45796_aux
namespace CoreSigned

section Live

variable {α : Type} [DecidableEq α]

def build (ops : α → α → Finset α) (goal : α) : ℕ → Finset α → Prop
  | 0, available => goal ∈ available
  | k + 1, available => build ops goal k available ∨
    ∃ a ∈ available, ∃ b ∈ available, a ≠ b ∧
      ∃ z ∈ ops a b, build ops goal k (insert z available)

def live (ops : α → α → Finset α) (goal : α) : ℕ → Finset α → Prop
  | 0, s => s = {goal}
  | k + 1, s => live ops goal k s ∨
    ∃ a ∈ s, ∃ b ∈ s, a ≠ b ∧ ∃ z ∈ ops a b, z ∉ s ∧
      ∃ rest : Finset α, s = insert a (insert b rest) ∧ live ops goal k (insert z rest)

set_option maxRecDepth 100000 in
theorem compress {ops : α → α → Finset α} {goal : α} {k : ℕ} {available : Finset α}
    (h : build ops goal k available) : ∃ s ⊆ available, live ops goal k s := by
  induction k generalizing available with
  | zero =>
    exact ⟨{goal}, Finset.singleton_subset_iff.mpr h, rfl⟩
  | succ k ih =>
    rcases h with skip | ⟨a, ha, b, hb, hab, z, hz, tail⟩
    · obtain ⟨s, hs, hrun⟩ := ih skip
      exact ⟨s, hs, Or.inl hrun⟩
    · obtain ⟨t, ht, hrun⟩ := ih tail
      by_cases sub : t ⊆ available
      · exact ⟨t, sub, Or.inl hrun⟩
      · have hzmem : z ∈ t := by
          by_contra hn
          apply sub
          intro u hu
          rcases Finset.mem_insert.mp (ht hu) with rfl | ok
          · exact False.elim (hn hu)
          · exact ok
        have hzout : z ∉ available := by
          intro hh
          exact sub ((Finset.insert_eq_of_mem hh) ▸ ht)
        let rest := t.erase z
        have hrest : rest ⊆ available := by
          intro u hu
          have hu' := Finset.mem_erase.mp hu
          exact (Finset.mem_insert.mp (ht hu'.2)).resolve_left hu'.1
        let s := insert a (insert b rest)
        have hs : s ⊆ available := Finset.insert_subset ha (Finset.insert_subset hb hrest)
        refine ⟨s, hs, Or.inr ⟨a, by simp [s], b, by simp [s], hab, z, hz,
          fun h => hzout (hs h), rest, rfl, ?_⟩⟩
        simpa [rest, Finset.insert_erase hzmem] using hrun

set_option maxRecDepth 100000 in
theorem live_card {ops : α → α → Finset α} {goal : α} {k : ℕ} {s : Finset α}
    (h : live ops goal k s) : s.card ≤ k + 1 := by
  induction k generalizing s with
  | zero => change s = {goal} at h; simp [h]
  | succ k ih =>
    rcases h with skip | ⟨a, ha, b, hb, hab, z, hz, hout, rest, rfl, tail⟩
    · exact (ih skip).trans (by omega)
    · have hzrest : z ∉ rest := fun hm => hout (by simp [hm])
      have htail := ih tail
      rw [Finset.card_insert_of_notMem hzrest] at htail
      have h₁ := Finset.card_insert_le a (insert b rest)
      have h₂ := Finset.card_insert_le b rest
      omega

set_option maxRecDepth 100000 in
theorem live_separates {ops : α → α → Finset α} {goal : α} (D : α → Prop)
    (hd : D goal) (hops : ∀ a b, ∀ z ∈ ops a b, D z → D a ∨ D b)
    {k : ℕ} {s : Finset α} (h : live ops goal k s) : ∃ w ∈ s, D w := by
  induction k generalizing s with
  | zero => change s = {goal} at h; exact ⟨goal, by simp [h], hd⟩
  | succ k ih =>
    rcases h with skip | ⟨a, ha, b, hb, hab, z, hz, hout, rest, rfl, tail⟩
    · exact ih skip
    · obtain ⟨w, hw, hD⟩ := ih tail
      rcases Finset.mem_insert.mp hw with rfl | hw
      · rcases hops a b w hz hD with h | h
        · exact ⟨a, ha, h⟩
        · exact ⟨b, hb, h⟩
      · exact ⟨w, by simp [hw], hD⟩

set_option maxRecDepth 100000 in
theorem first_live {ops : α → α → Finset α} {goal : α} {k : ℕ} {s : Finset α}
    (h : live ops goal (k + 1) s) :
    s = {goal} ∨
    ∃ a ∈ s, ∃ b ∈ s, a ≠ b ∧ ∃ z ∈ ops a b, z ∉ s ∧
      ∃ rest : Finset α, s = insert a (insert b rest) ∧ live ops goal k (insert z rest) := by
  induction k with
  | zero => exact h
  | succ k ih =>
    rcases h with skip | step
    · rcases ih skip with done | ⟨a, ha, b, hb, hab, z, hz, hn, r, hs, tail⟩
      · exact .inl done
      · exact .inr ⟨a, ha, b, hb, hab, z, hz, hn, r, hs, Or.inl tail⟩
    · exact .inr step

end Live

def singles {α : Type} : List α → List (α × List α)
  | [] => []
  | a :: rest => (a, rest) :: (singles rest).map (fun (b, bs) => (b, a :: bs))

def pairs {α : Type} : List α → List (α × α × List α)
  | [] => []
  | a :: rest => (singles rest).map (fun (b, bs) => (a, b, bs)) ++
      (pairs rest).map (fun (b, c, bs) => (b, c, a :: bs))

set_option maxRecDepth 100000 in
theorem pick_one {α : Type} {a : α} {ws : List α} (h : a ∈ ws) :
    ∃ rest, (a, rest) ∈ singles ws ∧ ws.Perm (a :: rest) := by
  induction ws with
  | nil => simp at h
  | cons x xs ih =>
    rcases List.mem_cons.mp h with e | h
    · subst x; exact ⟨xs, by simp [singles], .refl _⟩
    · obtain ⟨rest, hm, hp⟩ := ih h
      refine ⟨x :: rest, List.mem_cons_of_mem _ (List.mem_map.mpr ⟨(a, rest), hm, rfl⟩), ?_⟩
      exact (hp.cons x).trans (.swap _ _ _)

set_option maxRecDepth 100000 in
theorem pick_two {α : Type} {a b : α} {ws : List α} (ha : a ∈ ws) (hb : b ∈ ws) (hne : a ≠ b) :
    ∃ rest, ((a, b, rest) ∈ pairs ws ∨ (b, a, rest) ∈ pairs ws) ∧
      ws.Perm (a :: b :: rest) := by
  induction ws with
  | nil => simp at ha
  | cons x xs ih =>
    rcases List.mem_cons.mp ha with h | ha
    · subst x
      obtain ⟨r, hm, hp⟩ := pick_one ((List.mem_cons.mp hb).resolve_left (Ne.symm hne))
      exact ⟨r, .inl (List.mem_append_left _ (List.mem_map.mpr ⟨(b, r), hm, rfl⟩)), hp.cons a⟩
    · rcases List.mem_cons.mp hb with h | hb
      · subst x
        obtain ⟨r, hm, hp⟩ := pick_one (ws := xs) (a := a) (by assumption)
        exact ⟨r, .inr (List.mem_append_left _ (List.mem_map.mpr ⟨(a, r), hm, rfl⟩)),
          (hp.cons b).trans (.swap _ _ _)⟩
      · obtain ⟨r, hm, hp⟩ := ih ha hb
        refine ⟨x :: r, ?_,
          (hp.cons x).trans ((List.Perm.swap _ _ _).trans ((List.Perm.swap _ _ _).cons a))⟩
        rcases hm with hm | hm
        · exact .inl (List.mem_append_right _ (List.mem_map.mpr ⟨(a, b, r), hm, rfl⟩))
        · exact .inr (List.mem_append_right _ (List.mem_map.mpr ⟨(b, a, r), hm, rfl⟩))

end CoreSigned

namespace SignedProjection
variable {α β : Type} [DecidableEq α] [DecidableEq β] [Zero β]

def avail (pin : α → β) (S : Finset α) := (S.image pin).erase 0
def lost (pin : α → β) (S : Finset α) := (S.filter fun x => pin x = 0).card

theorem avail_mem (pin : α → β) {S : Finset α} {x : β} :
    x ∈ avail pin S ↔ x ≠ 0 ∧ ∃ a ∈ S, pin a = x := by simp [avail]

theorem avail_mono (pin : α → β) {S T : Finset α} (h : S ⊆ T) : avail pin S ⊆ avail pin T := by
  intro y hy
  obtain ⟨hn,x,hx,rfl⟩ := (avail_mem pin).mp hy
  exact (avail_mem pin).mpr ⟨hn,x,h hx,rfl⟩

theorem avail_cases (pin : α → β) {S : Finset α} {c : α} {x : β} (h : x ∈ avail pin (insert c S)) :
    x = pin c ∨ x ∈ avail pin S := by
  obtain ⟨hn,y,hy,rfl⟩ := (avail_mem pin).mp h
  rcases Finset.mem_insert.mp hy with rfl|hy
  · exact Or.inl rfl
  · exact Or.inr ((avail_mem pin).mpr ⟨hn,y,hy,rfl⟩)

theorem lost_insert (pin : α → β) (c : α) (S : Finset α) :
    lost pin (insert c S) = lost pin S + (if pin c = 0 ∧ c ∉ S then 1 else 0) := by
  by_cases mem : c ∈ S
  · rw [Finset.insert_eq_of_mem mem,ite_eq_right (fun q => q.2 mem),Nat.add_zero]
  · by_cases h : pin c = 0
    · rw [ite_eq_left ⟨h,mem⟩]
      unfold lost
      rw [Finset.filter_insert,ite_eq_left h,Finset.card_insert_of_notMem]
      exact fun q => mem (Finset.mem_filter.mp q).1
    · rw [ite_eq_right (fun q => h q.1),Nat.add_zero]
      unfold lost
      rw [Finset.filter_insert,ite_eq_right h]

theorem projected (pin : α → β) (ops : α → α → Finset α) (ops2 : β → β → Finset β) (goal : α)
    (hgoal : pin goal ≠ 0)
    (maps : ∀ {a b c}, c ∈ ops a b → pin c ∈ ops2 (pin a) (pin b))
    (idA : ∀ {a b c}, c ∈ ops2 a b → a = 0 → c = 0 ∨ c = b)
    (idB : ∀ {a b c}, c ∈ ops2 a b → b = 0 → c = 0 ∨ c = a)
    (idS : ∀ {a b c}, c ∈ ops2 a b → a = b → c = 0 ∨ c = b)
    {k : Nat} {S : Finset α} (h : CoreSigned.live ops goal k S) :
    ∃ j, j + lost pin S ≤ k ∧ ∃ T ⊆ avail pin S, CoreSigned.live ops2 (pin goal) j T := by
  induction k generalizing S with
  | zero =>
    change S = {goal} at h
    subst S
    exact ⟨0,by simp [lost,hgoal],{(pin goal)},by simp [avail,hgoal],rfl⟩
  | succ k ih =>
    rcases h with skip | ⟨a,_,b,_,ne,c,op,fresh,U,rfl,tail⟩
    · obtain ⟨j,hj,ws,sub,hws⟩ := ih skip
      exact ⟨j,by omega,ws,sub,hws⟩
    let prev := insert a (insert b U)
    have cnew : c ∉ U := fun h => fresh (by simp [h])
    have repr := maps op
    obtain ⟨j,limit,T,sub,path⟩ := ih tail
    have both (ha : pin a = 0) (hb : pin b = 0) : pin c = 0 := by
      exact (idA repr ha).elim id (fun e => e.trans hb)
    have skipcost : lost pin prev ≤ lost pin (insert c U) + 1 := by
      simp only [prev,lost_insert]
      split_ifs <;> grind
    have liftU : avail pin U ⊆ avail pin prev := avail_mono pin (by intro u hu; simp [prev,hu])
    by_cases useful : pin c ∈ T ∧ pin c ∉ avail pin prev
    · have nz := ((avail_mem pin).mp (sub useful.1)).1
      have df (v : α) (hv : v ∈ prev) : pin c ≠ pin v := by
        intro e
        exact useful.2 ((avail_mem pin).mpr ⟨nz,v,hv,e.symm⟩)
      have da := df a (by simp [prev])
      have db := df b (by simp [prev])
      have ha : pin a ≠ 0 := fun e => (idA repr e).elim nz db
      have hb : pin b ≠ 0 := fun e => (idB repr e).elim nz da
      have distinct : pin a ≠ pin b := fun e => (idS repr e).elim nz db
      have vcost : lost pin prev ≤ lost pin (insert c U) := by
        simp only [prev,lost_insert]
        split_ifs <;> grind
      let V := T.erase (pin c)
      have old (v : β) (hv : v ∈ V) : v ∈ avail pin U :=
        (avail_cases pin (sub (Finset.mem_erase.mp hv).2)).resolve_left (Finset.mem_erase.mp hv).1
      let B := insert (pin a) (insert (pin b) V)
      refine ⟨j+1,by change j+1+lost pin prev ≤ k+1; omega,B,?_,Or.inr ?_⟩
      · intro v hv
        rcases Finset.mem_insert.mp hv with rfl|hv
        · exact (avail_mem pin).mpr ⟨ha,a,by simp,rfl⟩
        rcases Finset.mem_insert.mp hv with rfl|hv
        · exact (avail_mem pin).mpr ⟨hb,b,by simp,rfl⟩
        exact liftU (old _ hv)
      · refine ⟨pin a,by simp [B],pin b,by simp [B],distinct,pin c,?_,?_,V,rfl,?_⟩
        · exact repr
        · simp [B,V,da,db]
        · rwa [show insert (pin c) V = T from Finset.insert_erase useful.1]
    · refine ⟨j,by change j+lost pin prev ≤ k+1; omega,T,?_,path⟩
      intro v hv
      rcases avail_cases pin (sub hv) with rfl|old
      · by_contra miss
        exact useful ⟨hv,miss⟩
      · exact liftU old

end SignedProjection

namespace SignedProjection
variable {n : Nat}

def signedOps (a b : BitVec n) := [a &&& b, a ||| b, a &&& ~~~b, b &&& ~~~a].toFinset

theorem zero_left {a b c : BitVec n} (h : c ∈ signedOps a b) (eq : a = 0) : c = 0 ∨ c = b := by
  subst a
  simpa [signedOps,or_comm] using h

theorem zero_right {a b c : BitVec n} (h : c ∈ signedOps a b) (eq : b = 0) : c = 0 ∨ c = a := by
  subst b
  simpa [signedOps,or_comm] using h

theorem equal_inputs {a b c : BitVec n} (h : c ∈ signedOps a b) (eq : a = b) : c = 0 ∨ c = b := by
  subst a
  simpa [signedOps,or_comm] using h

def signedPin (mask : BitVec n) (base : Fin n) (x : BitVec n) : BitVec n :=
  (if x[base.val] then ~~~x else x) &&& mask

theorem masked_ops (m : BitVec n) {a b c : BitVec n} (h : c ∈ signedOps a b) :
    c &&& m ∈ signedOps (a &&& m) (b &&& m) := by
  simp only [signedOps,List.mem_toFinset,List.mem_cons,List.not_mem_nil,or_false] at *
  rcases h with rfl|rfl|rfl|rfl
  · left; ext i h; simp [Bool.and_assoc, Bool.and_left_comm, Bool.and_comm]
  · right;left; ext i h; simp only [BitVec.getElem_or,BitVec.getElem_and]; cases a[i] <;> cases b[i] <;> simp
  · right;right;left; ext i h
    simp only [BitVec.getElem_and,BitVec.getElem_not]
    cases a[i] <;> cases b[i] <;> cases m[i] <;> decide
  · right;right;right; ext i h
    simp only [BitVec.getElem_and,BitVec.getElem_not]
    cases a[i] <;> cases b[i] <;> cases m[i] <;> decide

def polarity (b : Bool) (x : BitVec n) := if b then ~~~x else x

theorem polarity_ops (i : Fin n) {a b c : BitVec n} (h : c ∈ signedOps a b) :
    polarity (c[i.val]) c ∈ signedOps (polarity (a[i.val]) a) (polarity (b[i.val]) b) := by
  simp only [signedOps,List.mem_toFinset,List.mem_cons,List.not_mem_nil,or_false] at *
  rcases h with rfl|rfl|rfl|rfl <;>
    simp only [BitVec.getElem_and,BitVec.getElem_or,BitVec.getElem_not] <;>
    cases a[i.val] <;> cases b[i.val] <;>
    simp [polarity,BitVec.not_and,BitVec.not_or,BitVec.and_comm,BitVec.or_comm]

theorem signedPin_ops (m : BitVec n) (i : Fin n) {a b c : BitVec n} (h : c ∈ signedOps a b) :
    signedPin m i c ∈ signedOps (signedPin m i a) (signedPin m i b) :=
  masked_ops m (polarity_ops i h)

theorem live_build {α : Type} [DecidableEq α] {ops : α → α → Finset α} {goal : α}
    {k : Nat} {S V : Finset α} (h : CoreSigned.live ops goal k S) (sub : S ⊆ V) :
    CoreSigned.build ops goal k V := by
  induction k generalizing S V with
  | zero => change S = {goal} at h; subst S; exact sub (Finset.mem_singleton_self _)
  | succ k ih =>
    rcases h with skip|⟨a,ha,b,hb,ne,c,opc,_,rest,eq,tail⟩
    · exact Or.inl (ih skip sub)
    · refine Or.inr ⟨a,sub ha,b,sub hb,ne,c,opc,ih tail ?_⟩
      intro v hv
      rcases Finset.mem_insert.mp hv with rfl|hr
      · simp
      · exact Finset.mem_insert_of_mem (sub (eq ▸ Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hr)))

end SignedProjection

namespace SignedProjection
variable {α : Type} [DecidableEq α]

def generated (ops : α → α → Finset α) (stock : Finset α) : List (α × α × α) → Finset α → Prop
  | [], result => stock = result
  | (a,b,w) :: rest, result =>
    a ∈ stock ∧ b ∈ stock ∧ a ≠ b ∧ w ∈ ops a b ∧ generated ops (insert w stock) rest result

theorem extend_generated {ops : α → α → Finset α} {goal : α} {stock result : Finset α}
    {recipe : List (α × α × α)} {k : ℕ}
    (h : generated ops stock recipe result) (tail : CoreSigned.build ops goal k result) :
    CoreSigned.build ops goal (k + recipe.length) stock := by
  induction recipe generalizing stock with
  | nil => change stock = result at h; simpa [h] using tail
  | cons step rest ih =>
    obtain ⟨a,b,w⟩ := step
    rcases h with ⟨ha,hb,hn,ho,hrest⟩
    change CoreSigned.build ops goal (k+rest.length+1) stock
    exact Or.inr ⟨a,ha,b,hb,hn,w,ho,ih hrest⟩

theorem pad_build {ops : α → α → Finset α} {goal : α} {S : Finset α} {a b : Nat}
    (le : a ≤ b) (ha : CoreSigned.build ops goal a S) : CoreSigned.build ops goal b S := by
  induction le with
  | refl => exact ha
  | step _ ih => exact Or.inl ih

end SignedProjection

namespace SignedProjection
variable {n : Nat}

theorem exclude_cut (m : BitVec n) (i : Fin n) (goal : BitVec n) (k cap : ℕ)
    (S A U : Finset (BitVec n)) (recipes : List (BitVec n × BitVec n × BitVec n))
    (nonzero : signedPin m i goal ≠ 0)
    (bound : ¬ CoreSigned.build signedOps (signedPin m i goal) cap A)
    (regen : generated signedOps A recipes U) (sub : avail (signedPin m i) S ⊆ U)
    (budget : recipes.length + k ≤ cap + lost (signedPin m i) S) :
    ¬ CoreSigned.live signedOps goal k S := by
  intro h
  obtain ⟨j, hj, T, ht, path⟩ := projected (signedPin m i) signedOps signedOps goal nonzero
    (signedPin_ops m i) zero_left zero_right equal_inputs h
  have localRun := live_build path (ht.trans sub)
  exact bound (pad_build (by omega) (extend_generated regen localRun))

end SignedProjection

namespace SignedProjection
open CoreSigned (live build first_live live_card pairs pick_two live_separates)

abbrev Word := BitVec 64
def signedList (a b : Word) := [a &&& b, a ||| b, a &&& ~~~b, b &&& ~~~a]
theorem ops_swap (a b : Word) : signedOps a b = signedOps b a := by
  ext z
  simp only [signedOps, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false]
  rw [BitVec.and_comm a b, BitVec.or_comm a b]
  tauto
def keepChoices (a b : Word) (r : List Word) : List (List Word) := [r, a :: r, b :: r, a :: b :: r]

theorem recover_kept {ws r : List Word} {a b : Word} {needed : Finset Word}
    (hp : ws.Perm (a :: b :: r)) (hn : ws.Nodup)
    (hs : ws.toFinset = insert a (insert b needed)) :
    ∃ kept ∈ keepChoices a b r, kept.Nodup ∧ kept.toFinset = needed := by
  have habr := hp.nodup_iff.mp hn
  have hbase : ws.toFinset = insert a (insert b r.toFinset) := by
    ext v
    simp [hp.mem_iff]
  have henne : ∀ v, v ∈ r ↔ v ∈ needed ∧ v ≠ a ∧ v ≠ b := by
    intro v
    have he : (v ∈ insert a (insert b r.toFinset)) ↔ v ∈ insert a (insert b needed) := by
      rw [← hbase, ← hs]
    simp only [Finset.mem_insert, List.mem_toFinset] at he
    simp only [List.nodup_cons, List.mem_cons, not_or] at habr
    grind
  by_cases ha : a ∈ needed <;> by_cases hb : b ∈ needed
  · refine ⟨a :: b :: r, by simp [keepChoices], habr, ?_⟩
    ext v; simp [henne]; grind
  · refine ⟨a :: r, by simp [keepChoices], ?_, ?_⟩
    · simp_all [List.nodup_cons]
    · ext v; simp [henne]; grind
  · refine ⟨b :: r, by simp [keepChoices], (List.nodup_cons.mp habr).2, ?_⟩
    ext v; simp [henne]; grind
  · refine ⟨r, by simp [keepChoices], (List.nodup_cons.mp (List.nodup_cons.mp habr).2).2, ?_⟩
    ext v; simp [henne]; grind

theorem singleton_list {goal : Word} {ws : List Word} (hn : ws.Nodup) (hs : ws.toFinset = {goal}) : ws = [goal] := by
  have hc := List.toFinset_card_of_nodup hn
  rw [hs] at hc
  cases ws with
  | nil => simp at hc
  | cons w ws =>
    cases ws with
    | nil => simpa using hs
    | cons => simp at hc

def insertW (v : Word) : List Word → List Word
  | [] => [v]
  | x :: xs => if v ≤ x then v :: x :: xs else x :: insertW v xs

def ordered (ws : List Word) := ws.foldr insertW []

theorem insertW_perm (v : Word) (ws : List Word) : (insertW v ws).Perm (v :: ws) := by
  induction ws with
  | nil => exact .refl _
  | cons x xs ih =>
    simp only [insertW]
    split
    · exact .refl _
    · exact (ih.cons x).trans (.swap _ _ _)

theorem ordered_perm (ws : List Word) : (ordered ws).Perm ws := by
  induction ws with
  | nil => exact .refl _
  | cons x xs ih => exact (insertW_perm x (ordered xs)).trans (ih.cons x)

theorem perm_set {u v : List Word} (p : u.Perm v) : u.toFinset = v.toFinset := by
  ext a
  simpa only [List.mem_toFinset] using (p.mem_iff : a ∈ u ↔ a ∈ v)

def children (k : Nat) (ws : List Word) : List (List Word) :=
  (pairs ws).flatMap fun (a,b,r) => (signedList a b).flatMap fun z =>
    if z ∈ ws then [] else
      (keepChoices a b r).filterMap fun kept =>
        if kept.length ≤ k then some (ordered (z :: kept)) else none

theorem zero_prune {goal : Word} (nz : goal ≠ 0) {k : Nat} {S : Finset Word}
    (h : live signedOps goal k S) : ∃ j ≤ k, ∃ T ⊆ S.erase 0, live signedOps goal j T := by
  obtain ⟨j,le,T,sub,path⟩ := projected id signedOps signedOps goal nz (fun q => q)
    zero_left zero_right equal_inputs h
  refine ⟨j,by omega,T,?_,path⟩
  simpa [avail] using sub

theorem step_no (goal : Word) (n : Nat) (ws : List Word) (hn : ws.Nodup)
    (done_ : ws ≠ [goal])
    (children_ : ∀ qs ∈ children n ws, ¬ live signedOps goal n qs.toFinset)
    : ¬ live signedOps goal (n+1) ws.toFinset := by
  intro h
  rcases first_live h with done | ⟨a, ha, b, hb, hab, z, hz, hout, needed, hs, tail⟩
  · exact done_ (singleton_list hn done)
  obtain ⟨r,hm,hp⟩ := pick_two (List.mem_toFinset.mp ha) (List.mem_toFinset.mp hb) hab
  have go {a b : Word} (hp : ws.Perm (a :: b :: r)) (hmem : (a,b,r) ∈ pairs ws)
      (hset : ws.toFinset = insert a (insert b needed)) (hop : z ∈ signedOps a b) : False := by
    obtain ⟨kept,hkeep,hnk,hfin⟩ := recover_kept hp hn hset
    have hznew : z ∉ kept := by
      intro hu
      apply hout
      rw [hset]
      exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (hfin ▸ List.mem_toFinset.mpr hu))
    have hnd : (z :: kept).Nodup := List.nodup_cons.mpr ⟨hznew, hnk⟩
    have hraw : live signedOps goal n (z :: kept).toFinset := by simpa [hfin] using tail
    have hc := live_card hraw
    rw [List.toFinset_card_of_nodup hnd, List.length_cons] at hc
    have hzws : z ∉ ws := by simpa using hout
    have hp' := ordered_perm (z :: kept)
    have mem : ordered (z :: kept) ∈ children n ws := by
      apply List.mem_flatMap.mpr
      refine ⟨(a,b,r),hmem,List.mem_flatMap.mpr ⟨z,List.mem_toFinset.mp hop,?_⟩⟩
      simpa only [hzws,ite_false] using
        (List.mem_filterMap.mpr ⟨kept,hkeep,by simp [show kept.length ≤ n by omega]⟩ :
          ordered (z::kept) ∈ ((keepChoices a b r).filterMap fun kept =>
            if kept.length ≤ n then some (ordered (z :: kept)) else none))
    exact children_ _ mem ((perm_set hp').symm ▸ hraw)
  rcases hm with direct|swap
  · exact go hp direct hs hz
  · exact go (hp.trans (.swap _ _ _)) swap (by rw [hs, Finset.insert_comm]) (ops_swap a b ▸ hz)
end SignedProjection

namespace SignedProjection
abbrev V64 := BitVec 64

def bitAt (w : V64) (n : Nat) := w.getLsbD n
def mismatch (g : V64) (ws : List V64) (p q : Nat) :=
  (bitAt g p != bitAt g q) && ws.all (fun w => bitAt w p == bitAt w q)

theorem mismatch_sound {g : V64} {ws : List V64} {p q : Nat} (pp : p < 64) (qq : q < 64)
    (cert : mismatch g ws p q = true) (k : ℕ) : ¬ CoreSigned.live signedOps g k ws.toFinset := by
  intro h
  have parts := Bool.and_eq_true_iff.mp cert
  let D : V64 → Prop := fun w => bitAt w p ≠ bitAt w q
  have dg : D g := by simpa [D] using parts.1
  have hop (a b : V64) (z : V64) (hz : z ∈ signedOps a b) (dz : D z) : D a ∨ D b := by
    by_contra! fail
    apply dz
    obtain ⟨ea,eb⟩ := fail
    simp only [D, not_not] at ea eb
    change bitAt a p = bitAt a q at ea
    change bitAt b p = bitAt b q at eb
    simp only [signedOps, List.mem_toFinset,List.mem_cons, List.not_mem_nil,or_false] at hz
    rcases hz with rfl|rfl|rfl|rfl <;>
      simpa only [bitAt, BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_not,
        pp,qq,decide_true, Bool.true_and, show a.getLsbD p = a.getLsbD q from ea,
        show b.getLsbD p = b.getLsbD q from eb]
  obtain ⟨x,hx,dx⟩ := CoreSigned.live_separates D dg hop h
  exact dx (beq_iff_eq.mp (List.all_eq_true.mp parts.2 x (List.mem_toFinset.mp hx)))

end SignedProjection

namespace SignedProjection
abbrev View := Word × Fin 64 × Word × List Word × Nat × (Nat → Nat)
abbrev Node := Nat × Nat × List Word × (Nat → Nat)
def vm (v : View) := v.1
def va (v : View) := v.2.1
def vg (v : View) := v.2.2.1
def vs (v : View) := v.2.2.2.1
def vk (v : View) := v.2.2.2.2.1
def vh (v : View) := v.2.2.2.2.2
def nv (a : Node) := a.1
def nk (a : Node) := a.2.1
def ns (a : Node) := a.2.2.1
def nh (a : Node) := a.2.2.2

def recipeRun : Nat → Nat → List Word → Option (List (Word × Word × Word) × List Word)
  | 0, code, ws => if code = 1 then some ([],ws) else none
  | fuel+1, code, ws => if code = 1 then some ([],ws) else
    let i := code % 16
    let j := (code / 16) % 16
    let o := (code / 256) % 4
    match ws[i]?, ws[j]? with
    | some a, some b => if a = b then none else
      let w := (signedList a b).getD o 0
      match recipeRun fuel (code / 1024) (ws++[w]) with
      | some (rs,ws') => some ((a,b,w)::rs,ws')
      | none => none
    | _,_ => none

theorem recipeRun_sound (fuel code : Nat) (ws : List Word) {rs out}
    (h : recipeRun fuel code ws = some (rs,out)) :
    generated signedOps ws.toFinset rs out.toFinset := by
  induction fuel generalizing code ws rs out with
  | zero =>
    simp only [recipeRun] at h
    split at h
    · cases h; rfl
    · contradiction
  | succ k ih =>
    simp only [recipeRun] at h
    split at h
    · cases h; rfl
    split at h <;> try contradiction
    rename_i a b ha hb
    split at h <;> try contradiction
    rename_i ne
    split at h <;> try contradiction
    rename_i tail end_ ht
    cases h
    set r := (code / 256) % 4
    let w := (signedList a b).getD r 0
    change a ∈ ws.toFinset ∧ b ∈ ws.toFinset ∧ a ≠ b ∧ w ∈ signedOps a b ∧ _
    refine ⟨List.mem_toFinset.mpr (List.mem_of_getElem? ha),
      List.mem_toFinset.mpr (List.mem_of_getElem? hb),ne,?_,?_⟩
    · have hr : r < 4 := Nat.mod_lt _ (by decide)
      change w ∈ (signedList a b).toFinset
      simp only [List.mem_toFinset]
      have hr' : r < (signedList a b).length := by simpa [signedList] using hr
      simpa [w, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hr'] using
        (List.getElem_mem (l := signedList a b) (i := r) hr')
    · have eq : (ws++[w]).toFinset = insert w ws.toFinset := by
        ext x
        simp [or_comm]
      rw [← eq]
      exact ih _ _ ht

def ViewOK (v : View) := ¬ CoreSigned.build signedOps (vg v) (vk v) (vs v).toFinset

def cutOK (v : View) (g : Word) (k : Nat) (ws : List Word) (recipe : Nat) : Bool :=
  let p := signedPin (vm v) (va v)
  if p g != vg v || p g == 0 then false else
    match recipeRun 12 recipe (vs v) with
    | none => false
    | some (rs,out) =>
      decide (avail p ws.toFinset ⊆ out.toFinset) &&
      decide (rs.length+k ≤ vk v + lost p ws.toFinset)

theorem cutOK_sound {v : View} {g : Word} {k : Nat} {ws : List Word} {recipe : Nat}
    (hv : ViewOK v) (hc : cutOK v g k ws recipe = true) :
    ¬ CoreSigned.live signedOps g k ws.toFinset := by
  simp only [cutOK] at hc
  split at hc <;> try contradiction
  rename_i ok
  split at hc <;> try contradiction
  rename_i rs out hr
  have parts := Bool.and_eq_true_iff.mp hc
  have good : signedPin (vm v) (va v) g = vg v ∧ signedPin (vm v) (va v) g ≠ 0 := by
    simpa using ok
  apply exclude_cut (vm v) (va v) g k (vk v) ws.toFinset (vs v).toFinset out.toFinset rs good.2
    (good.1 ▸ hv) (recipeRun_sound _ _ _ hr) (of_decide_eq_true parts.1)
    (of_decide_eq_true parts.2)

end SignedProjection
namespace SignedProjection

def quickCut (v : View) (g : Word) (k : Nat) (ws : List Word) (receipt : Nat) : Bool :=
  let p := signedPin (vm v) (va v)
  if p g != vg v || p g == 0 then false else
    match recipeRun 12 receipt (vs v) with
    | none => false
    | some (rs,out) =>
      decide ws.Nodup &&
      ws.all (fun w => p w == 0 || out.contains (p w)) &&
      decide (rs.length+k ≤ vk v + ws.countP (fun w => p w = 0))

theorem quickCut_sound {v : View} {g : Word} {k : Nat} {ws : List Word} {receipt : Nat}
    (hv : ViewOK v) (ok : quickCut v g k ws receipt = true) :
    ¬ CoreSigned.live signedOps g k ws.toFinset := by
  simp only [quickCut] at ok
  split at ok <;> try contradiction
  rename_i good
  split at ok <;> try contradiction
  rename_i rs out hr
  have parts := Bool.and_eq_true_iff.mp ok
  have pp := Bool.and_eq_true_iff.mp parts.1
  have nd := of_decide_eq_true pp.1
  have gg : signedPin (vm v) (va v) g = vg v ∧ signedPin (vm v) (va v) g ≠ 0 := by
    simpa using good
  apply exclude_cut (vm v) (va v) g k (vk v) ws.toFinset (vs v).toFinset out.toFinset rs gg.2
    (gg.1 ▸ hv) (recipeRun_sound _ _ _ hr)
  · intro x hx
    obtain ⟨ne,w,hw,rfl⟩ := (avail_mem _).mp hx
    have has := List.all_eq_true.mp pp.2 w (List.mem_toFinset.mp hw)
    simp only [Bool.or_eq_true,beq_iff_eq,List.contains_iff_mem] at has
    exact List.mem_toFinset.mpr (has.resolve_left ne)
  · unfold lost
    rw [List.Nodup.card_eq_countP nd]
    exact of_decide_eq_true parts.2

end SignedProjection

namespace SignedProjection.QFast
abbrev Table (α : Type) := Nat × (Nat → Option α)
def get {α : Type} (t : Table α) (i : Nat) : Option α := if i < t.1 then t.2 i else none

def checkHint (views : Table View) (nodes : Table Node) (vID : Nat) (g : Word)
    (k : Nat) (ws : List Word) (hint : Nat) : Bool :=
  let val := hint/4
  match hint % 4 with
  | 0 => mismatch g ws (val % 64) ((val/64)%64)
  | 1 => match (get nodes val) with
    | some a => (nv a == vID) && (nk a == k) && (ns a == ws)
    | none => false
  | 2 =>
    let j := val % 1024
    if j < vID then
      match (get views j) with
      | some v => quickCut v g k ws (val/1024)
      | none => false
    else false
  | _ => (k == 0 && ws.toFinset != {g}) || decide (k+1 < ws.toFinset.card)

theorem checkHint_sound {views : Table View} {nodes : Table Node} {vID : Nat} {g : Word}
    {k : Nat} {ws : List Word} {h : Nat}
    (known : ∀ i < vID, ∀ v, (get views i) = some v → ViewOK v)
    (closed : ∀ (i : Nat) (a : Node), (get nodes i) = some a → nv a = vID → nk a = k →
      ¬ CoreSigned.live signedOps g k (ns a).toFinset)
    (ok : checkHint views nodes vID g k ws h = true) : ¬ CoreSigned.live signedOps g k ws.toFinset := by
  simp only [checkHint] at ok
  split at ok
  · exact mismatch_sound (Nat.mod_lt _ (by decide)) (Nat.mod_lt _ (by decide)) ok k
  · split at ok <;> try contradiction
    rename_i a ha
    simp only [Bool.and_eq_true,beq_iff_eq] at ok
    exact ok.2 ▸ closed _ a ha ok.1.1 ok.1.2
  · split at ok <;> try contradiction
    rename_i lt
    split at ok <;> try contradiction
    rename_i v hv
    exact quickCut_sound (known _ lt _ hv) ok
  · simp only [Bool.or_eq_true,Bool.and_eq_true,beq_iff_eq,bne_iff_ne,decide_eq_true_eq] at ok
    intro h
    rcases ok with ⟨rfl,ne⟩|wide
    · exact ne h
    · exact (Nat.not_lt_of_ge (CoreSigned.live_card h)) wide

def scanFrom {α : Type} (f : Nat → α → Bool) : Nat → List α → Bool
  | _, [] => true
  | i, x::xs => f i x && scanFrom f (i+1) xs

theorem scanFrom_sound {α : Type} (f : Nat → α → Bool) {i : Nat} {xs : List α}
    (ok : scanFrom f i xs = true) {x : α} (hx : x ∈ xs) : ∃ j, f j x = true := by
  induction xs generalizing i with
  | nil => simp at hx
  | cons a xs ih =>
    have parts := Bool.and_eq_true_iff.mp ok
    rcases List.mem_cons.mp hx with rfl|hm
    · exact ⟨_,parts.1⟩
    · exact ih parts.2 hm

def evalNode (views : Table View) (nodes : Table Node) (a : Node) : Bool :=
  match (get views (nv a)) with
  | none => false
  | some v => decide (ns a).Nodup && (ns a != [vg v]) &&
    match nk a with
    | 0 => true
    | k+1 => scanFrom (fun i ws => checkHint views nodes (nv a) (vg v) k ws (nh a i)) 0
               (children k (ns a))

def evalRoot (views : Table View) (nodes : Table Node) (i : Nat) (v : View) : Bool :=
  scanFrom (fun q ws => checkHint views nodes i (vg v) (vk v) ws (vh v q)) 0 (vs v).sublists

theorem view_from_earlier (views : Table View) (nodes : Table Node) (vID : Nat) (v : View)
    (hv : (get views vID) = some v)
    (earlier : ∀ i < vID, ∀ w, (get views i) = some w → ViewOK w)
    (hroots : evalRoot views nodes vID v = true)
    (hnodes : ∀ (i : Nat) (a : Node), (get nodes i) = some a → evalNode views nodes a = true) :
    ViewOK v := by
  have closed (k : Nat) : ∀ (i : Nat) (a : Node), (get nodes i) = some a → nv a = vID → nk a = k →
      ¬ CoreSigned.live signedOps (vg v) k (ns a).toFinset := by
    induction k with
    | zero =>
      intro i a found owner fuel h
      have ok := hnodes i a found
      simp only [evalNode,owner,hv,fuel,Bool.and_true,Bool.and_eq_true,decide_eq_true_eq,bne_iff_ne] at ok
      exact ok.2 (singleton_list ok.1 h)
    | succ k ih =>
      intro i a found owner fuel
      have ok := hnodes i a found
      simp only [evalNode,owner,hv,fuel,Bool.and_eq_true,decide_eq_true_eq,bne_iff_ne] at ok
      apply step_no _ _ _ ok.1.1 ok.1.2
      intro ws hm
      obtain ⟨j,good⟩ := scanFrom_sound _ ok.2 hm
      exact checkHint_sound earlier ih good
  intro build_
  classical
  obtain ⟨S, sub, path⟩ := CoreSigned.compress build_
  let ws := (vs v).filter (· ∈ S)
  have eq : ws.toFinset = S := by
    ext w
    simp only [ws,List.mem_toFinset,List.mem_filter,decide_eq_true_eq,and_iff_right_iff_imp]
    exact fun hw => List.mem_toFinset.mp (sub hw)
  obtain ⟨q,hq⟩ := scanFrom_sound _ hroots (show ws ∈ (vs v).sublists from
    List.mem_sublists.mpr (List.filter_sublist ..))
  exact checkHint_sound earlier (closed _) hq (eq.symm ▸ path)

theorem whole_sound (views : Table View) (nodes : Table Node)
    (allRoots : ∀ (i : Nat) (v : View), (get views i) = some v → evalRoot views nodes i v = true)
    (allNodes : ∀ (i : Nat) (a : Node), (get nodes i) = some a → evalNode views nodes a = true)
    (i : Nat) (v : View) (hv : (get views i) = some v) : ViewOK v := by
  induction i using Nat.strong_induction_on generalizing v with
  | ind i ih => exact view_from_earlier views nodes i v hv ih (allRoots i v hv) allNodes

def checkRootAt (views : Table View) (nodes : Table Node) (i : Nat) : Bool :=
  match (get views i) with
  | some v => evalRoot views nodes i v
  | none => true

def checkNodeAt (views : Table View) (nodes : Table Node) (i : Nat) : Bool :=
  match (get nodes i) with
  | some a => evalNode views nodes a
  | none => true

def passBlock (check : Nat → Bool) (start : Nat) : Nat → Bool
  | 0 => true
  | n+1 => passBlock check start n && check (start+n)

theorem block_at (check : Nat → Bool) {s n i} (ok : passBlock check s n = true)
    (lo : s ≤ i) (hi : i < s+n) : check i = true := by
  induction n with
  | zero => omega
  | succ n ih =>
    have parts := Bool.and_eq_true_iff.mp ok
    by_cases lt : i < s+n
    · exact ih parts.1 lt
    · have eq : i = s+n := by omega
      exact eq ▸ parts.2

theorem merge_blocks {c : Nat → Bool} {s a b : Nat} (x : passBlock c s a = true)
    (y : passBlock c (s+a) b = true) : passBlock c s (a+b) = true := by
  induction b with
  | zero => simpa using x
  | succ b ih =>
    have parts := Bool.and_eq_true_iff.mp y
    change passBlock c s (a+b) && c (s+(a+b)) = true
    exact Bool.and_eq_true_iff.mpr ⟨ih parts.1,by simpa [Nat.add_assoc] using parts.2⟩

theorem certified_view (views : Table View) (nodes : Table Node)
    (roots : passBlock (checkRootAt views nodes) 0 views.1 = true)
    (states : passBlock (checkNodeAt views nodes) 0 nodes.1 = true)
    {i : Nat} {v : View} (hv : (get views i) = some v) : ViewOK v := by
  apply whole_sound views nodes _ _ i v hv
  · intro j w hw
    have hj : j < views.1 := by by_contra! lo; simp [get, Nat.not_lt_of_ge lo] at hw
    have ok := block_at _ roots (i := j) (Nat.zero_le _) (by omega)
    simpa [checkRootAt,hw] using ok
  · intro j a ha
    have hj : j < nodes.1 := by by_contra! lo; simp [get, Nat.not_lt_of_ge lo] at ha
    have ok := block_at _ states (i := j) (Nat.zero_le _) (by omega)
    simpa [checkNodeAt,ha] using ok

end SignedProjection.QFast
namespace SignedProjection.QFast

def rowAt (m : Array Nat) (k : Fin 64) := Fin.ofNat 64 (m[k.val]?.getD 0)
def rowWord (m : Array Nat) (w : Word) : Word :=
  (BitVec.ofBoolListLE (List.ofFn (fun k : Fin 64 => w[(rowAt m k).val]))).cast List.length_ofFn

theorem rowWord_bit (m : Array Nat) (w : Word) (j : Nat) (hj : j < 64) :
    (rowWord m w)[j] = w[(rowAt m ⟨j,hj⟩).val] := by
  rw [← BitVec.getLsbD_eq_getElem hj]
  simp only [rowWord, BitVec.getLsbD_cast, BitVec.getLsbD_ofBoolListLE,
    List.getD_eq_getElem?_getD, List.getElem?_ofFn, hj, dite_true, Option.getD_some]

theorem rowWord_and (m : Array Nat) (x y : Word) : rowWord m (x &&& y) = rowWord m x &&& rowWord m y :=
  BitVec.eq_of_getElem_eq fun j hj => by simp only [rowWord_bit,BitVec.getElem_and]
theorem rowWord_or (m : Array Nat) (x y : Word) : rowWord m (x ||| y) = rowWord m x ||| rowWord m y :=
  BitVec.eq_of_getElem_eq fun j hj => by simp only [rowWord_bit,BitVec.getElem_or]
theorem rowWord_not (m : Array Nat) (x : Word) : rowWord m (~~~x) = ~~~rowWord m x :=
  BitVec.eq_of_getElem_eq fun j hj => by simp only [rowWord_bit,BitVec.getElem_not]

def viewMap (m : Array Nat) (v : View) (w : Word) := signedPin (vm v) (va v) (rowWord m w)
theorem viewMap_ops (m : Array Nat) (v : View) {a b c : Word} (hc : c ∈ signedOps a b) :
    viewMap m v c ∈ signedOps (viewMap m v a) (viewMap m v b) := by
  apply signedPin_ops
  simp only [signedOps,List.mem_toFinset,List.mem_cons,List.not_mem_nil,or_false] at hc ⊢
  rcases hc with rfl|rfl|rfl|rfl
  · exact Or.inl (rowWord_and ..)
  · exact Or.inr (Or.inl (rowWord_or ..))
  · exact Or.inr (Or.inr (Or.inl (by rw [rowWord_and,rowWord_not])))
  · exact Or.inr (Or.inr (Or.inr (by rw [rowWord_and,rowWord_not])))

def viewAliasOK (m : Array Nat) (src dst : View) : Bool :=
  (vg dst != 0) && (viewMap m dst (vg src) == vg dst) && decide (vk src ≤ vk dst) &&
  (vs src).all fun w => viewMap m dst w == 0 || (vs dst).contains (viewMap m dst w)

theorem viewAlias_sound {m : Array Nat} {src dst : View} (yes : ViewOK dst)
    (valid : viewAliasOK m src dst = true) : ViewOK src := by
  simp only [viewAliasOK,Bool.and_eq_true, bne_iff_ne,beq_iff_eq,decide_eq_true_eq] at valid
  obtain ⟨⟨⟨nz,go⟩,le⟩,all⟩ := valid
  intro run
  obtain ⟨S,sub,path⟩ := CoreSigned.compress run
  have ng := fun h : viewMap m dst (vg src) = 0 => nz (go.symm.trans h)
  obtain ⟨j,hj,T,ts,tail⟩ := projected (viewMap m dst) signedOps signedOps _ ng
    (viewMap_ops m dst) zero_left zero_right equal_inputs path
  have supply : T ⊆ (vs dst).toFinset := by
    intro y hy
    obtain ⟨pn,w,hw,rfl⟩ := (avail_mem _).mp (ts hy)
    have h := List.all_eq_true.mp all w (List.mem_toFinset.mp (sub hw))
    simp only [Bool.or_eq_true,beq_iff_eq] at h
    exact List.mem_toFinset.mpr (List.contains_iff_mem.mp (h.resolve_left pn))
  rw [go] at tail
  exact yes (pad_build (by omega) (live_build tail supply))

abbrev AliasTable := Nat → Option (Nat × Array Nat)
def symCheckRoot (aliases : AliasTable) (views : Table View) (nodes : Table Node) (i : Nat) : Bool :=
  match get views i with
  | none => true
  | some v => match aliases i with
    | none => evalRoot views nodes i v
    | some (j,m) => decide (j < i) &&
      match get views j with
      | none => false
      | some w => viewAliasOK m v w

theorem symCertified (aliases : AliasTable) (views : Table View) (nodes : Table Node)
    (roots : passBlock (symCheckRoot aliases views nodes) 0 views.1 = true)
    (states : passBlock (checkNodeAt views nodes) 0 nodes.1 = true)
    {i : Nat} {v : View} (hv : get views i = some v) : ViewOK v := by
  have allNodes (j : Nat) (a : Node) (ha : get nodes j = some a) : evalNode views nodes a = true := by
    have hj : j < nodes.1 := by by_contra! lo; simp [get, Nat.not_lt_of_ge lo] at ha
    have ok := block_at _ states (i := j) (Nat.zero_le _) (by omega)
    simpa [checkNodeAt,ha] using ok
  induction i using Nat.strong_induction_on generalizing v with
  | ind i ih =>
    have hi : i < views.1 := by by_contra! lo; simp [get, Nat.not_lt_of_ge lo] at hv
    have ok := block_at _ roots (i := i) (Nat.zero_le _) (by omega)
    simp only [symCheckRoot,hv] at ok
    cases he : aliases i with
    | none =>
      exact view_from_earlier views nodes i v hv ih (by simpa only [he] using ok) allNodes
    | some x =>
      rcases x with ⟨j,m⟩
      simp only [he,Bool.and_eq_true,decide_eq_true_eq] at ok
      cases hh : get views j with
      | none => simp [hh] at ok
      | some w => exact viewAlias_sound (ih j ok.1 hh) (by simpa only [hh] using ok.2)

end SignedProjection.QFast

namespace LowerSymSix
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def witness : Circuit :=
  ⟨[⟨.and,[1,4]⟩, ⟨.and,[1,2]⟩, ⟨.and,[3,7]⟩, ⟨.and,[0,4]⟩, ⟨.and,[5,6]⟩,
    ⟨.or,[0,10]⟩, ⟨.or,[5,6]⟩, ⟨.or,[8,9]⟩, ⟨.and,[12,13]⟩, ⟨.or,[2,3]⟩,
    ⟨.and,[11,15]⟩, ⟨.or,[14,16]⟩],17⟩

theorem size : witness.size = 12 := rfl

theorem monotone : Monotone2 witness := by
  simp [Monotone2,witness]

set_option maxRecDepth 16000 in
theorem correct : ∀ x : Fin 6 → Bool, witness.eval (List.ofFn x) =
    Nat.testBit (4008372896 * 2 ^ 32 + 3936922272) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  decide +kernel

end LowerSymSix

namespace Direct64
open PEqualNP.CircuitLowerBounds SignedProjection
abbrev W := BitVec 64
abbrev basicOps (a b : W) := signedOps a b
abbrev goal : W := ~~~0xeeeaeaa0eaa8aaa0
open CoreSigned (build)
def tableB (x : Fin 6 → Bool) :=
  Nat.testBit (4008372896 * 2 ^ 32 + 3936922272) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
def holds (av : Finset W) (z : W) : Prop :=
  z = 0 ∨ z = ~~~0 ∨ ∃ a ∈ av, z = a ∨ z = ~~~a

set_option maxRecDepth 100000 in
theorem holds_insert {av : Finset W} {z a : W} (h : holds av z) : holds (insert a av) z := by
  rcases h with h|h|⟨u,hu,he⟩
  · exact .inl h
  · exact .inr (.inl h)
  · exact .inr (.inr ⟨u,Finset.mem_insert_of_mem hu,he⟩)

set_option maxRecDepth 100000 in
theorem holds_not {av : Finset W} {z : W} (h : holds av z) : holds av (~~~z) := by
  rcases h with rfl|rfl|⟨a,ha,he⟩
  · exact .inr (.inl rfl)
  · exact .inl BitVec.not_not
  · rcases he with he|he <;> rw [he]
    · exact .inr (.inr ⟨a, ha, .inr rfl⟩)
    · exact .inr (.inr ⟨a, ha, .inl BitVec.not_not⟩)

def reachable (av : Finset W) (z : W) : Prop :=
  holds av z ∨ ∃ a ∈ av, ∃ b ∈ av, a ≠ b ∧ ∃ w ∈ basicOps a b, holds (insert w av) z

set_option maxRecDepth 100000 in
theorem reachable_not {av : Finset W} {z : W} (h : reachable av z) : reachable av (~~~z) := by
  rcases h with h|⟨a,ha,b,hb,ne,w,hop,hw⟩
  · exact .inl (holds_not h)
  · exact .inr ⟨a,ha,b,hb,ne,w,hop,holds_not hw⟩

set_option maxRecDepth 100000 in
theorem and_reach {av : Finset W} {x y : W} (hx : holds av x) (hy : holds av y) :
    reachable av (x &&& y) := by
  have const : holds av (0 : W) := .inl rfl
  have oldx := hx
  rcases hx with rfl|rfl|⟨a,ha,ea⟩
  · rw [show (0 : W) &&& y = 0 from BitVec.zero_and]; exact .inl const
  · change reachable av (BitVec.allOnes 64 &&& y)
    rw [BitVec.allOnes_and]; exact .inl hy
  rcases hy with rfl|rfl|⟨b,hb,eb⟩
  · rw [show x &&& (0 : W) = 0 from BitVec.and_zero]; exact .inl const
  · change reachable av (x &&& BitVec.allOnes 64)
    rw [BitVec.and_allOnes]; exact .inl oldx
  by_cases h : a = b
  · subst b
    rcases ea with ea|ea <;> rcases eb with eb|eb <;> rw [ea,eb] <;>
      simp only [BitVec.and_self, BitVec.and_not_self, BitVec.not_and_self] <;>
      first | exact .inl const | exact .inl (.inr (.inr ⟨a,ha,.inl rfl⟩)) |
        exact .inl (.inr (.inr ⟨a,ha,.inr rfl⟩))
  have add (w : W) (hw : w ∈ basicOps a b) (z : W) (hz : z = w ∨ z = ~~~w) :
      reachable av z :=
    .inr ⟨a,ha,b,hb,h,w,hw,.inr (.inr ⟨w,Finset.mem_insert_self ..,hz⟩)⟩
  rcases ea with ea|ea <;> rcases eb with eb|eb <;> rw [ea,eb]
  · exact add _ (by simp [basicOps,SignedProjection.signedOps] : a &&& b ∈ basicOps a b) _ (.inl rfl)
  · exact add _ (by simp [basicOps,SignedProjection.signedOps] : a &&& ~~~b ∈ basicOps a b) _ (.inl rfl)
  · exact add _ (by simp [basicOps,SignedProjection.signedOps] : b &&& ~~~a ∈ basicOps a b) _ (.inl (BitVec.and_comm ..))
  · exact add _ (by simp [basicOps,SignedProjection.signedOps] : a ||| b ∈ basicOps a b) _ (.inr BitVec.not_or.symm)

set_option maxRecDepth 100000 in
theorem or_reach {av : Finset W} {x y : W} (hx : holds av x) (hy : holds av y) :
    reachable av (x ||| y) := by
  simpa only [BitVec.not_and, BitVec.not_not] using reachable_not (and_reach (holds_not hx) (holds_not hy))

private def bit (k : Fin 64) (z : W) : Bool := z[k.val]
private def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

set_option maxRecDepth 100000 in
private theorem read_bit (w : List W) (i : ℕ) (k : Fin 64) :
    (w.map (bit k)).getD i false = bit k (w.getD i 0) := by
  by_cases h : i < w.length
  · simp [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem h]
  · simp [List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_eq_none (Nat.le_of_not_gt h), bit]

def legal (g : Gate) : Prop := (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2

def action (w : List W) (g : Gate) : W := match g.op with
  | .not => ~~~(g.inputs.head?.map (fun i => w.getD i 0)).getD 0
  | .and => (g.inputs.map fun i => w.getD i 0).foldr (· &&& ·) (~~~0)
  | .or => (g.inputs.map fun i => w.getD i 0).foldr (· ||| ·) 0
  | _ => 0

set_option maxRecDepth 100000 in
theorem action_spec (w : List W) (g : Gate) (hg : legal g) (k : Fin 64) :
    step (w.map (bit k)) g = (w ++ [action w g]).map (bit k) := by
  obtain ⟨op,args⟩ := g
  obtain ⟨hop,cap⟩ := hg
  change op = .and ∨ op = .or ∨ op = .not at hop
  change args.length ≤ 2 at cap
  rcases args with _|⟨i,_|⟨j,_|⟨u,tail⟩⟩⟩ <;> simp at cap
  all_goals have bit0 : (0 : W)[k.val] = false := by change (0#64)[k.val] = false; simp
  all_goals rcases hop with rfl|rfl|rfl <;>
    simp only [step, List.map_cons,List.map_nil,read_bit,List.map_append] <;>
    simp only [action, GateOp.eval, List.foldr_cons,List.foldr_nil,List.head?_cons,List.head?_nil,
      List.headD_cons,List.headD_nil,Option.map_some,Option.map_none,Option.getD_some,Option.getD_none,
      List.all_cons,List.all_nil,List.any_cons,List.any_nil,List.map_cons,List.map_nil,id_eq,
      Bool.and_true,Bool.or_false, bit,BitVec.getElem_and,BitVec.getElem_or,BitVec.getElem_not,
      bit0,Bool.not_false]

def isBinary (g : Gate) : Bool := match g.op with
  | .not => false
  | _ => true
def binaryCost (gs : List Gate) := (gs.filter isBinary).length

set_option maxRecDepth 100000 in
theorem available_read {av : Finset W} {w : List W} (hw : ∀ u ∈ w, holds av u) (i : ℕ) :
    holds av (w.getD i 0) := by
  by_cases h : i < w.length
  · exact hw _ (by simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h])
  · rw [List.getD_eq_default _ _ (Nat.le_of_not_gt h)]
    exact .inl rfl

set_option maxRecDepth 100000 in
theorem gate_reach (w : List W) (av : Finset W) (hw : ∀ u ∈ w, holds av u)
    (g : Gate) (hg : legal g) :
    if isBinary g then reachable av (action w g) else holds av (action w g) := by
  obtain ⟨op,args⟩ := g
  obtain ⟨hop,cap⟩ := hg
  change op = .and ∨ op = .or ∨ op = .not at hop
  change args.length ≤ 2 at cap
  rcases args with _|⟨i,_|⟨j,_|⟨u,tail⟩⟩⟩ <;> simp at cap
  all_goals rcases hop with rfl|rfl|rfl <;> simp only [isBinary,Bool.false_eq_true,ite_false,ite_true,
    action,List.head?_nil,List.head?_cons,List.map_nil,List.map_cons,List.foldr_nil,List.foldr_cons,
    Option.map_none,Option.map_some,Option.getD_none,Option.getD_some,
    show ∀ x : W, x ||| (0 : W) = x from fun x => BitVec.or_zero,
    show ∀ x : W, x &&& ~~~0 = x from fun x => BitVec.and_allOnes]
  all_goals first
    | exact .inl (.inl rfl)
    | exact .inl (.inr (.inl rfl))
    | exact .inr (.inl rfl)
    | exact .inl (available_read hw _)
    | exact holds_not (available_read hw _)
    | exact and_reach (available_read hw _) (available_read hw _)
    | exact or_reach (available_read hw _) (available_read hw _)

set_option maxRecDepth 100000 in
theorem compile (gs : List Gate) (out : ℕ) (hg : ∀ g ∈ gs, legal g)
    (w : List W) (av : Finset W) (hw : ∀ u ∈ w, holds av u)
    (he : ∀ k, (gs.foldl step (w.map (bit k))).getD out false = bit k (~~~goal)) :
    ∃ t, (t = goal ∨ t = ~~~goal) ∧ build basicOps t (binaryCost gs) av := by
  induction gs generalizing w av with
  | nil =>
    have hv : w.getD out 0 = ~~~goal := by
      apply BitVec.eq_of_getElem_eq
      intro i hi
      simpa only [List.foldl_nil, read_bit, bit] using he ⟨i,hi⟩
    have h := hv ▸ available_read hw out
    rcases h with zero|ones|⟨t,ht,eq|eq⟩
    · exact False.elim ((by decide : ~~~goal ≠ 0) zero)
    · exact False.elim ((by decide : ~~~goal ≠ ~~~0) ones)
    · exact ⟨t, .inr eq.symm, ht⟩
    · exact ⟨t, .inl (by simpa only [BitVec.not_not] using congrArg (fun w : W => ~~~w) eq.symm), ht⟩
  | cons g gs ih =>
    let z := action w g
    have stepOK := action_spec w g (hg g (by simp))
    have nextEval : ∀ k, (gs.foldl step ((w ++ [z]).map (bit k))).getD out false = bit k (~~~goal) := by
      intro k; simpa only [List.foldl_cons, stepOK] using he k
    have tail := ih (fun t ht => hg t (by simp [ht])) (w ++ [z])
    have cont (A : Finset W) (hold : ∀ u ∈ w, holds A u) (new : holds A z) :=
      tail A (by
        intro u hu
        rcases List.mem_append.mp hu with hu|hu
        · exact hold u hu
        · exact (List.mem_singleton.mp hu) ▸ new) nextEval
    have stepClass := gate_reach w av hw g (hg g (by simp))
    cases neg : isBinary g
    · simp only [neg,Bool.false_eq_true,ite_false] at stepClass
      simpa [binaryCost,neg] using cont av hw stepClass
    · simp only [neg,ite_true] at stepClass
      have len : binaryCost (g::gs) = binaryCost gs+1 := by simp [binaryCost,neg]
      rw [len]
      rcases stepClass with existing|⟨a,ha,b,hb,ne,new,op,rep⟩
      · obtain ⟨t,ht,run⟩ := cont av hw existing
        exact ⟨t,ht,Or.inl run⟩
      · obtain ⟨t,ht,run⟩ := cont (insert new av) (fun u hu => holds_insert (hw u hu)) rep
        exact ⟨t,ht,Or.inr ⟨a,ha,b,hb,ne,new,op,run⟩⟩

def cols : List W := [0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000]

theorem sample64 : ∀ k : Fin 64, tableB (fun i => (cols.getD i.val 0)[k.val]) = (~~~goal)[k.val] := by
  decide +kernel

theorem zero_open (k : ℕ) {t : W} (av : Finset W) (hz : ∀ u ∈ av, u.getLsbD 0 = false)
    (h : build basicOps t k av) : t.getLsbD 0 = false := by
  induction k generalizing av with
  | zero => exact hz t h
  | succ k ih =>
    rcases h with skip | ⟨a,ha,b,hb,_,z,hop,tail⟩
    · exact ih av hz skip
    · apply ih (insert z av) _ tail
      intro u hu
      rcases Finset.mem_insert.mp hu with rfl|hu
      · simp only [basicOps,signedOps,List.mem_toFinset,List.mem_cons,List.not_mem_nil,or_false] at hop
        rcases hop with rfl|rfl|rfl|rfl <;> simp only [BitVec.getLsbD_and,BitVec.getLsbD_or,BitVec.getLsbD_not,hz a ha,hz b hb,Bool.false_and,Bool.or_self]
      · exact hz u hu

theorem low (reject : ¬ build basicOps (0xeeeaeaa0eaa8aaa0 : W) 10 cols.toFinset)
    (gs : List Gate) (o : ℕ) (hg : ∀ g ∈ gs, legal g)
    (he : ∀ x : Fin 6 → Bool, Circuit.eval ⟨gs,o⟩ (List.ofFn x) = tableB x) : 10 < binaryCost gs := by
  by_contra! low
  have width : cols.length = 6 := rfl
  have init : ∀ u ∈ cols, holds cols.toFinset u := by
    intro u hu
    exact .inr (.inr ⟨u, List.mem_toFinset.mpr hu, .inl rfl⟩)
  have evaluate (k : Fin 64) :
      (gs.foldl step (cols.map (bit k))).getD o false = bit k (~~~goal) := by
    let x (i : Fin 6) : Bool := bit k (cols.getD i.val 0)
    have same : List.ofFn x = cols.map (bit k) := by
      apply List.ext_getElem
      · simp [width]
      · intro i hi hj
        have hlt : i < cols.length := by simpa using hj
        simp only [List.getElem_ofFn, List.getElem_map, x, List.getD_eq_getElem?_getD,
          List.getElem?_eq_getElem hlt, Option.getD_some]
    change Circuit.eval ⟨gs,o⟩ (cols.map (bit k)) = bit k (~~~goal)
    rw [← same, he]
    exact sample64 k
  obtain ⟨t, ht, run⟩ := compile gs o hg cols cols.toFinset init evaluate

  have h0 : ∀ u ∈ cols.toFinset, u.getLsbD 0 = false := by
    intro u hu
    simp only [cols,List.mem_toFinset,List.mem_cons,List.not_mem_nil,or_false] at hu
    rcases hu with rfl|rfl|rfl|rfl|rfl|rfl <;> decide +kernel
  rcases ht with rfl|rfl
  · have odd : goal.getLsbD 0 ≠ false := by decide +kernel
    exact odd (zero_open _ _ h0 run)
  · apply reject
    apply pad_build low
    exact run
end Direct64

namespace LowerSymSix
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
theorem finish
    (reject : ¬ CoreSigned.build SignedProjection.signedOps (0xeeeaeaa0eaa8aaa0 : BitVec 64) 10 Direct64.cols.toFinset) :
∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4008372896 * 2 ^ 32 + 3936922272) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4008372896 * 2 ^ 32 + 3936922272) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  rintro s ⟨C, hg, hs, he⟩
  by_cases neg : ∃ g ∈ C.gates, g.op = .not
  · obtain ⟨g, hm, op⟩ := neg
    have lo := Direct64.low reject C.gates C.output hg he
    have proper : Direct64.binaryCost C.gates < C.gates.length := by
      apply List.length_filter_lt_length_iff_exists.mpr
      exact ⟨g, hm, by simp [Direct64.isBinary, op]⟩
    have cap : C.gates.length ≤ s := hs
    exact ⟨witness, monotone, by rw [size]; omega, correct⟩
  · refine ⟨C, ?_, hs, he⟩
    intro g hm
    obtain ⟨hop, hin⟩ := hg g hm
    refine ⟨?_, hin⟩
    rcases hop with h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · exact (neg ⟨g, hm, h⟩).elim

end LowerSymSix

namespace SignedProjection
def ew0 : Word := 0x4000400040004000
def ew1 : Word := 0x4040000040400000
def ew2 : Word := 0x4040404000000000
def ew3 : Word := 0x4400000044000000
def ew4 : Word := 0x4400440000000000
def ew5 : Word := 0x4444000000000000
def ew6 : Word := 0x808080800000000
def ew7 : Word := 0xc000c0000000000
def ew8 : Word := 0xc0c000000000000
def ew9 : Word := 0x88008800000000
def ew10 : Word := 0xc000c000000000
def ew11 : Word := 0xcc000000000000
def ew12 : Word := 0x888800000000
def ew13 : Word := 0xc0c000000000
def ew14 : Word := 0xcc0000000000
def ew15 : Word := 0x404040404040404
def ew16 : Word := 0x600060006000600
def ew17 : Word := 0x606000006060000
def ew18 : Word := 0x606060600000000
def ew19 : Word := 0x802080208020802
def ew20 : Word := 0xc000c000c000c00
def ew21 : Word := 0xc0300000c030000
def ew22 : Word := 0xc030c0300000000
def ew23 : Word := 0xa000a0000a000a
def ew24 : Word := 0xc000c0000c000c
def ew25 : Word := 0xf000f000000000
def ew26 : Word := 0xf00000000f0000
def ew27 : Word := 0xa000a00000a000a
def ew28 : Word := 0xc000c00000c000c
def ew29 : Word := 0xf000f0000000000
def ew30 : Word := 0xf000000000f0000
def ew31 : Word := 0x4040404040404040
def ew32 : Word := 0x4400440044004400
def ew33 : Word := 0x4444000044440000
def ew34 : Word := 0x4444444400000000
def ew35 : Word := 0x5000500050005000
def ew36 : Word := 0x5050000050500000
def ew37 : Word := 0x5050505000000000
def ew38 : Word := 0x808080808080808
def ew39 : Word := 0xc0c00000c0c0000
def ew40 : Word := 0xc0c0c0c00000000
def ew41 : Word := 0x88888888
def ew42 : Word := 0xc0c0c0c0
def ew43 : Word := 0xcc00cc00
def ew44 : Word := 0xcccc0000
def ew45 : Word := 0x8888888800000000
def ew46 : Word := 0xc0c0c0c000000000
def ew47 : Word := 0xcc00cc0000000000
def ew48 : Word := 0xcccc000000000000
def ew49 : Word := 0xa0a00000a0a0000
def ew50 : Word := 0xf0000000f000000
def ew51 : Word := 0xf0f000000000000
def ew52 : Word := 0xaa000000aa0000
def ew53 : Word := 0xcc000000cc0000
def ew54 : Word := 0xf0000000f00000
def ew55 : Word := 0xff000000000000
def ew56 : Word := 0xaaaa0000
def ew57 : Word := 0xf0f00000
def ew58 : Word := 0xff000000
def ew59 : Word := 0x4010401040104010
def ew60 : Word := 0x4800480048004800
def ew61 : Word := 0x4812000048120000
def ew62 : Word := 0x4812481200000000
def ew63 : Word := 0x1010404010104040
def ew64 : Word := 0x1212000012120000
def ew65 : Word := 0x1200480012004800
def ew66 : Word := 0x1212484800000000
def ew67 : Word := 0x8282000082820000
def ew68 : Word := 0x8080404080804040
def ew69 : Word := 0x8200410082004100
def ew70 : Word := 0x8282414100000000
def ew71 : Word := 0x444400004444
def ew72 : Word := 0x606000006060
def ew73 : Word := 0x660000006600
def ew74 : Word := 0x666600000000
def ew75 : Word := 0x6060000060600000
def ew76 : Word := 0x6600000066000000
def ew77 : Word := 0x6666000000000000
def ew78 : Word := 0x50005000500050
def ew79 : Word := 0x48004800480048
def ew80 : Word := 0x5a0000005a0000
def ew81 : Word := 0x5a005a00000000
def ew82 : Word := 0x4848000048480000
def ew83 : Word := 0x5a0000005a000000
def ew84 : Word := 0x5a5a000000000000
def ew85 : Word := 0x50505050
def ew86 : Word := 0x48484848
def ew87 : Word := 0x5a005a00
def ew88 : Word := 0x5a5a0000
def ew89 : Word := 0x500050005000500
def ew90 : Word := 0x408040804080408
def ew91 : Word := 0x50a0000050a0000
def ew92 : Word := 0x50a050a00000000
def ew93 : Word := 0x5500000055000000
def ew94 : Word := 0x4488000044880000
def ew95 : Word := 0x50a0000050a00000
def ew96 : Word := 0x55aa000000000000
def ew97 : Word := 0x505050500000000
def ew98 : Word := 0x404040408080808
def ew99 : Word := 0x50005000a000a00
def ew100 : Word := 0x50500000a0a0000
def ew101 : Word := 0x55005500000000
def ew102 : Word := 0x44004400880088
def ew103 : Word := 0x50005000a000a0
def ew104 : Word := 0x55000000aa0000
def ew105 : Word := 0x5555000000000000
def ew106 : Word := 0x4444000088880000
def ew107 : Word := 0x50500000a0a00000
def ew108 : Word := 0x55000000aa000000
def ew109 : Word := 0x8888888888888888
def ew110 : Word := 0xc0c0c0c0c0c0c0c0
def ew111 : Word := 0xcc00cc00cc00cc00
def ew112 : Word := 0xcccc0000cccc0000
def ew113 : Word := 0xcccccccc00000000
def ew114 : Word := 0xa0a0a0a0a0a0a0a
def ew115 : Word := 0xc0c0c0c0c0c0c0c
def ew116 : Word := 0xf000f000f000f00
def ew117 : Word := 0xf0f00000f0f0000
def ew118 : Word := 0xf0f0f0f00000000
def ew119 : Word := 0xaa00aa00aa00aa
def ew120 : Word := 0xcc00cc00cc00cc
def ew121 : Word := 0xf000f000f000f0
def ew122 : Word := 0xff000000ff0000
def ew123 : Word := 0xff00ff00000000
def ew124 : Word := 0xaaaa0000aaaa0000
def ew125 : Word := 0xf0f00000f0f00000
def ew126 : Word := 0xff000000ff000000
def ew127 : Word := 0xffff000000000000
def ew128 : Word := 0x5050505050505050
def ew129 : Word := 0x4848484848484848
def ew130 : Word := 0x5a005a005a005a00
def ew131 : Word := 0x5a5a00005a5a0000
def ew132 : Word := 0x5a5a5a5a00000000
def ew133 : Word := 0x5500550055005500
def ew134 : Word := 0x4488448844884488
def ew135 : Word := 0x50a050a050a050a0
def ew136 : Word := 0x55aa000055aa0000
def ew137 : Word := 0x55aa55aa00000000
def ew138 : Word := 0xaaaaaaaaaaaaaaaa
def ew139 : Word := 0xcccccccccccccccc
def ew140 : Word := 0xf0f0f0f0f0f0f0f0
def ew141 : Word := 0xff00ff00ff00ff00
def ew142 : Word := 0xffff0000ffff0000
def ew143 : Word := 0xffffffff00000000
def ew144 : Word := 0x606000000000000
def ew145 : Word := 0x6060000
def ew146 : Word := 0x60600000000
def ew147 : Word := 0x4000000040000000
def ew148 : Word := 0x444000004440000
def ew149 : Word := 0x4000400000000000
def ew150 : Word := 0x444044400000000
def ew151 : Word := 0x400440004004400
def ew152 : Word := 0x4040000000000000
def ew153 : Word := 0x404444400000000
def ew154 : Word := 0x400040044004400
def ew155 : Word := 0x404000044440000
def ew156 : Word := 0x40404000404040
def ew157 : Word := 0x4400000000000000
def ew158 : Word := 0x44444400000000
def ew159 : Word := 0x40004040404040
def ew160 : Word := 0x44000044440000
def ew161 : Word := 0x404040404040
def ew162 : Word := 0x440044004400
def ew163 : Word := 0x444444400000000
def ew164 : Word := 0x444000044440000
def ew165 : Word := 0x400440044004400
def ew166 : Word := 0x40404040404040
def ew167 : Word := 0x80808080
def ew168 : Word := 0xc8c8c8c8
def ew169 : Word := 0x8080808
def ew170 : Word := 0x40404040
def ew171 : Word := 0x88008800
def ew172 : Word := 0xcc88cc88
def ew173 : Word := 0x880088
def ew174 : Word := 0x44004400
def ew175 : Word := 0x88880000
def ew176 : Word := 0xcccc8888
def ew177 : Word := 0x8888
def ew178 : Word := 0x44440000
def ew179 : Word := 0xc000c000
def ew180 : Word := 0xccc0ccc0
def ew181 : Word := 0xc000c0
def ew182 : Word := 0xc000c00
def ew183 : Word := 0xc0c00000
def ew184 : Word := 0xccccc0c0
def ew185 : Word := 0xc0c0
def ew186 : Word := 0xc0c0000
def ew187 : Word := 0xcc000000
def ew188 : Word := 0xcccccc00
def ew189 : Word := 0xcc00
def ew190 : Word := 0xcc0000
def ew191 : Word := 0xcc80cc80
def ew192 : Word := 0x4c004c00
def ew193 : Word := 0xcccc8080
def ew194 : Word := 0x4c4c0000
def ew195 : Word := 0xc800c800
def ew196 : Word := 0xc800c8
def ew197 : Word := 0xc8c80000
def ew198 : Word := 0xc8c8
def ew199 : Word := 0xc8c0c8c0
def ew200 : Word := 0x40c040c0
def ew201 : Word := 0xcccc8800
def ew202 : Word := 0x44cc0000
def ew203 : Word := 0xc080c080
def ew204 : Word := 0xc080c08
def ew205 : Word := 0xcc880000
def ew206 : Word := 0xcc88
def ew207 : Word := 0xc8c8c0c0
def ew208 : Word := 0x4040c0c0
def ew209 : Word := 0xcc88cc00
def ew210 : Word := 0x4400cc00
def ew211 : Word := 0xc0c08080
def ew212 : Word := 0xc0c0808
def ew213 : Word := 0xcc008800
def ew214 : Word := 0xcc0088
def ew215 : Word := 0xcccc00c0
def ew216 : Word := 0xcc0c0000
def ew217 : Word := 0xcccc0c00
def ew218 : Word := 0xc0cc0000
def ew219 : Word := 0xcc00ccc0
def ew220 : Word := 0xcc000c00
def ew221 : Word := 0xcc0ccc00
def ew222 : Word := 0xc000cc00
def ew223 : Word := 0xc0c0ccc0
def ew224 : Word := 0xc0c000c0
def ew225 : Word := 0xc0ccc0c0
def ew226 : Word := 0xc000c0c0
def ew227 : Word := 0x1212000000000000
def ew228 : Word := 0x484800000000
def ew229 : Word := 0xc000c000c000c000
def ew230 : Word := 0xccc0ccc0ccc0ccc0
def ew231 : Word := 0xc000c000c000c0
def ew232 : Word := 0xc0c00000c0c00000
def ew233 : Word := 0xccccc0c0ccccc0c0
def ew234 : Word := 0xc0c00000c0c0
def ew235 : Word := 0xcc000000cc000000
def ew236 : Word := 0xcccccc00cccccc00
def ew237 : Word := 0xcc000000cc00
def ew238 : Word := 0xa000a000a000a00
def ew239 : Word := 0xf0a0f0a0f0a0f0a
def ew240 : Word := 0xa000a000a000a
def ew241 : Word := 0xa0a0a0a00000000
def ew242 : Word := 0xc000c000c000c
def ew243 : Word := 0xf000f00000000
def ew244 : Word := 0xf080f080f080f08
def ew245 : Word := 0x700070007000700
def ew246 : Word := 0x707070700000000
def ew247 : Word := 0x400040004000400
def ew248 : Word := 0xf040f040f040f04
def ew249 : Word := 0xb000b000b000b00
def ew250 : Word := 0x40c040c040c040c
def ew251 : Word := 0x50f0000050f0000
def ew252 : Word := 0x50f050f00000000
def ew253 : Word := 0xc080c080c080c08
def ew254 : Word := 0xf0a00000f0a0000
def ew255 : Word := 0xf0a0f0a00000000
def ew256 : Word := 0xc040c040c040c04
def ew257 : Word := 0xf050f0500000000
def ew258 : Word := 0x80c080c080c080c
def ew259 : Word := 0x500050000000000
def ew260 : Word := 0xa0f0a0f00000000
def ew261 : Word := 0x40404040c0c0c0c
def ew262 : Word := 0xf0a0f0a0f000f00
def ew263 : Word := 0x50005000f000f00
def ew264 : Word := 0xf050f050f000f00
def ew265 : Word := 0xa000a000f000f00
def ew266 : Word := 0xe0a0e0a0e0a0e0a
def ew267 : Word := 0x20a020a020a020a
def ew268 : Word := 0xa0e0a0e0a0e0a0e
def ew269 : Word := 0xa020a020a020a02
def ew270 : Word := 0xf030f0300000000
def ew271 : Word := 0xf0a0f0a0a0a0a0a
def ew272 : Word := 0xa000a0a0a0a0a
def ew273 : Word := 0xa0f0a0f0a0a0a0a
def ew274 : Word := 0xa000a000a0a0a0a
def ew275 : Word := 0xc000c000c0c0c0c
def ew276 : Word := 0x40f0000040f0000
def ew277 : Word := 0x40f040f00000000
def ew278 : Word := 0x40c0000040c0000
def ew279 : Word := 0x103000001030000
def ew280 : Word := 0x50f000000000000
def ew281 : Word := 0x50f0000
def ew282 : Word := 0xc0800000c080000
def ew283 : Word := 0x302000003020000
def ew284 : Word := 0xf0a000000000000
def ew285 : Word := 0xf0a0000
def ew286 : Word := 0x703070300000000
def ew287 : Word := 0x40004000c0c0c0c
def ew288 : Word := 0x40c040c000c000c
def ew289 : Word := 0x50f0000000f0000
def ew290 : Word := 0xe0a00000e0a0000
def ew291 : Word := 0xe0a0e0a00000000
def ew292 : Word := 0xc080c0808080808
def ew293 : Word := 0xf0a00000a0a0000
def ew294 : Word := 0x5a5a5a5a5a005a00
def ew295 : Word := 0x50000000500000
def ew296 : Word := 0x5a0a00005a0a0000
def ew297 : Word := 0x5a5a5a5a00500050
def ew298 : Word := 0x500050
def ew299 : Word := 0x5a505a005a505a00
def ew300 : Word := 0x5a5a5a5a50500000
def ew301 : Word := 0x50500000
def ew302 : Word := 0x5a005a005a505a50
def ew303 : Word := 0x5a5a00000a0a0000
def ew304 : Word := 0x5a5a5a5a48480000
def ew305 : Word := 0x5a5a000012120000
def ew306 : Word := 0x5000505050005050
def ew307 : Word := 0x5a5a5a5a005a0000
def ew308 : Word := 0x5a0000
def ew309 : Word := 0x5050505050005000
def ew310 : Word := 0x5a5a00005a000000
def ew311 : Word := 0x4848484800004848
def ew312 : Word := 0x5050505000005050
def ew313 : Word := 0x5a005a005a5a5a00
def ew314 : Word := 0x5a5a00005a0a0000
def ew315 : Word := 0xfafafafafafafafa
def ew316 : Word := 0xffaaffaaffaaffaa
def ew317 : Word := 0x5555000055550000
def ew318 : Word := 0x5555555500000000
def ew319 : Word := 0xfff0fff0fff0fff0
def ew320 : Word := 0xfa00fa00fa00fa
def ew321 : Word := 0xfafa0000fafa0000
def ew322 : Word := 0xffaa0000ffaa0000
def ew323 : Word := 0xf5f5f0f0f5f5f0f0
def ew324 : Word := 0xff55ff00ff55ff00
def ew325 : Word := 0xf5f5f5f5f0f0f0f0
def ew326 : Word := 0xff55ff55ff00ff00
def ew327 : Word := 0x5550555055505550
def ew328 : Word := 0xfff00000fff00000
def ew329 : Word := 0xf0000000f0000
def ew330 : Word := 0xfff0fff000000000
def ew331 : Word := 0xafafafafaaaaaaaa
def ew332 : Word := 0xff0fff0fff00ff00
def ew333 : Word := 0xaaffaaffaaaaaaaa
def ew334 : Word := 0xf0fff0fff0f0f0f0
def ew335 : Word := 0xffffaaaaaaaaaaaa
def ew336 : Word := 0xfffff0f0f0f0f0f0
def ew337 : Word := 0xffffff00ff00ff00
def ew338 : Word := 0xfafafafafafa
def ew339 : Word := 0xffaaffaaffaa
def ew340 : Word := 0xfffaaaaafffaaaaa
def ew341 : Word := 0xfff0fff0fff0
def ew342 : Word := 0xf0f0a0a0a0a0a0a
def ew343 : Word := 0xff00aa00aa00aa
def ew344 : Word := 0xfff0aaa0aaa0aaa0
def labelsBlock0 : Array Nat := #[
  0x3658,
  0x2e98,
  0x1e38,
  0x1,
  0x3a28,
  0x2124,
  0x32c4,
  0x3144,
  0x1124,
  0x3184,
  0x904,
  0x5,
  0x2ea8,
  0x21,
  0x2e38,
  0x1e70
]
def labelsBlock1 : Array Nat := #[
  0x1e58,
  0x1002,
  0x3a68,
  0xb28,
  0xb0c,
  0x130c,
  0x1012,
  0x1348,
  0x1e68,
  0xcd,
  0x112c,
  0x2e8c,
  0x1938,
  0x318c,
  0xe2c,
  0x1cd
]
def labelsBlock2 : Array Nat := #[
  0x718,
  0x70c,
  0x1d9,
  0x1344,
  0x2b8c,
  0x219,
  0x1944,
  0x1544,
  0x37d,
  0x2984,
  0x2eb0,
  0x2ca4,
  0x381,
  0x2584,
  0x234c,
  0x411
]
def labelsBlock3 : Array Nat := #[
  0x3698,
  0xa24,
  0x3ac8,
  0x3aa8,
  0x9,
  0xd,
  0x11,
  0x15,
  0x19,
  0x1d,
  0x36c8,
  0x25,
  0x1006,
  0x29,
  0x100a,
  0x2d
]
def labelsBlock4 : Array Nat := #[
  0x100e,
  0x31,
  0x35,
  0x39,
  0x3d,
  0x41,
  0x45,
  0x49,
  0x4d,
  0x51,
  0x55,
  0x59,
  0x5d,
  0x61,
  0x65,
  0x69
]
def labelsBlock5 : Array Nat := #[
  0x6d,
  0x71,
  0x75,
  0x79,
  0x7d,
  0x81,
  0x85,
  0x89,
  0x8d,
  0x91,
  0x95,
  0x99,
  0x9d,
  0xa1,
  0xa5,
  0xa9
]
def labelsBlock6 : Array Nat := #[
  0xad,
  0xb1,
  0xb5,
  0xb9,
  0xbd,
  0xc1,
  0xc5,
  0xc9,
  0xd1,
  0xd5,
  0xd9,
  0x708,
  0xdd,
  0xe1,
  0xe5,
  0xe9
]
def labelsBlock7 : Array Nat := #[
  0xb08,
  0xed,
  0xf1,
  0x161c,
  0xf5,
  0xf9,
  0x1308,
  0xfd,
  0x101,
  0x105,
  0x109,
  0x10d,
  0x111,
  0x115,
  0x170c,
  0x119
]
def labelsBlock8 : Array Nat := #[
  0x11d,
  0x121,
  0x125,
  0x129,
  0x12d,
  0x131,
  0x135,
  0x139,
  0x13d,
  0xe1c,
  0x141,
  0x145,
  0x149,
  0x14d,
  0x151,
  0x155
]
def labelsBlock9 : Array Nat := #[
  0x159,
  0x15d,
  0x161,
  0x165,
  0x169,
  0x16d,
  0x171,
  0x175,
  0x179,
  0x17d,
  0x181,
  0x185,
  0x189,
  0x18d,
  0xf38,
  0x191
]
def labelsBlock10 : Array Nat := #[
  0x195,
  0x199,
  0xf0c,
  0x19d,
  0x1a1,
  0x1758,
  0x1a5,
  0x1a9,
  0x1ad,
  0x1b1,
  0x1b5,
  0x1b68,
  0x1b9,
  0x1bd,
  0x1c1,
  0x1b0c
]
def labelsBlock11 : Array Nat := #[
  0x1c5,
  0x1c9,
  0x3cb8,
  0x1c64,
  0x34c4,
  0x1d1,
  0x1d5,
  0x102e,
  0x261c,
  0x2798,
  0x1dd,
  0x1e1,
  0x1e5,
  0x1e9,
  0x338c,
  0x1ed
]
def labelsBlock12 : Array Nat := #[
  0x1f1,
  0x1f5,
  0x1f9,
  0x103a,
  0x278c,
  0x103e,
  0x1fd,
  0x201,
  0x205,
  0x209,
  0x41002e,
  0x101a,
  0x20d,
  0x1016,
  0x51002e,
  0x52103a
]
def labelsBlock13 : Array Nat := #[
  0x52103e,
  0x61002e,
  0x62103a,
  0x62103e,
  0x71002e,
  0x72103a,
  0x72103e,
  0x42002e,
  0x43103a,
  0x43103e,
  0x211,
  0x52002e,
  0x53103a,
  0x53103e,
  0x62002e,
  0x63103a
]
def labelsBlock14 : Array Nat := #[
  0x63103e,
  0x72002e,
  0x73103a,
  0x73103e,
  0x42102e,
  0x43203a,
  0x43203e,
  0x215,
  0x52102e,
  0x53203a,
  0x231c,
  0x53203e,
  0x62102e,
  0x63203a,
  0x63203e,
  0x72102e
]
def labelsBlock15 : Array Nat := #[
  0x73203a,
  0x73203e,
  0x14401002e,
  0x14802002e,
  0x14c43103a,
  0x14c43103e,
  0x14842102e,
  0x14c83203a,
  0x14c83203e,
  0x920,
  0x3ae0,
  0x21d,
  0x221,
  0x225,
  0x229,
  0x29a0
]
def labelsBlock16 : Array Nat := #[
  0x22d,
  0x900,
  0x231,
  0x1042,
  0x235,
  0x239,
  0x90c,
  0x23d,
  0x241,
  0xb04,
  0x245,
  0x249,
  0x101e,
  0x24d,
  0x251,
  0x410042
]
def labelsBlock17 : Array Nat := #[
  0x255,
  0x31c0,
  0x259,
  0x25d,
  0x261,
  0x106e,
  0x265,
  0x710042,
  0xb20,
  0x269,
  0x26d,
  0x271,
  0x275,
  0x279,
  0x420042,
  0x27d
]
def labelsBlock18 : Array Nat := #[
  0x281,
  0x285,
  0x1a4c,
  0x289,
  0x28d,
  0x291,
  0x3a48,
  0x295,
  0x1960,
  0x299,
  0x29d,
  0x520042,
  0x2a1,
  0x2a5,
  0x2a9,
  0x2ad
]
def labelsBlock19 : Array Nat := #[
  0x620042,
  0x1076,
  0x2b1,
  0x2b5,
  0x2b9,
  0x2bd,
  0x2c1,
  0x2c5,
  0x2c9,
  0x2cd,
  0x720042,
  0x2d1,
  0x2d5,
  0x2d9,
  0x2dd,
  0x2e1
]
def labelsBlock20 : Array Nat := #[
  0x430042,
  0x2824,
  0x2e5,
  0x2e9,
  0x2ed,
  0x730042,
  0x2920,
  0x2f1,
  0x2f5,
  0x2f9,
  0x1022,
  0x421042,
  0x2fd,
  0x301,
  0x621042,
  0x305
]
def labelsBlock21 : Array Nat := #[
  0x309,
  0x30d,
  0x432042,
  0x102a,
  0x311,
  0x315,
  0x319,
  0x732042,
  0x2904,
  0x3a60,
  0x232c,
  0x2b0c,
  0x1cd010042,
  0x1304,
  0x3a88,
  0x31d
]
def labelsBlock22 : Array Nat := #[
  0x321,
  0x3ac0,
  0x1340,
  0x3aa0,
  0x3104,
  0x1c5020042,
  0x325,
  0x329,
  0x32d,
  0x331,
  0x1cd020042,
  0x335,
  0x3a40,
  0x38c4,
  0x3140,
  0x339
]
def labelsBlock23 : Array Nat := #[
  0x110520042,
  0x33d,
  0x341,
  0x345,
  0x349,
  0x10d120042,
  0x1920,
  0x1024,
  0x1900,
  0x2900,
  0x908,
  0x34d,
  0x2024,
  0x2980,
  0x351,
  0xb00
]
def labelsBlock24 : Array Nat := #[
  0x355,
  0x359,
  0x1c5030042,
  0x35d,
  0x361,
  0x1b28,
  0x2a2c,
  0x2b28,
  0x365,
  0x369,
  0x3348,
  0x1cd221042,
  0x39a0,
  0x36d,
  0x371,
  0x33c0
]
def labelsBlock25 : Array Nat := #[
  0x1c5332042,
  0x375,
  0x214c,
  0x3304,
  0x379,
  0x1300,
  0x3100,
  0x1550,
  0x1046,
  0x104a,
  0x36d0,
  0x164c,
  0x1062,
  0x385,
  0x389,
  0x1318
]
def labelsBlock26 : Array Nat := #[
  0x1066,
  0xc24,
  0x106a,
  0x38d,
  0x2c24,
  0x104e,
  0x391,
  0x395,
  0x2e30,
  0x399,
  0x39d,
  0x3a1,
  0x3a5,
  0x3a9,
  0x3ad,
  0x3b1
]
def labelsBlock27 : Array Nat := #[
  0xc2c,
  0x1930,
  0x2930,
  0x3b5,
  0x3b9,
  0x3bd,
  0x420062,
  0x3c1,
  0x3c5,
  0x3c9,
  0x3cd,
  0x3d1,
  0x3d5,
  0x1052,
  0x421062,
  0x42104e
]
def labelsBlock28 : Array Nat := #[
  0x43106a,
  0x3d9,
  0x3dd,
  0x3e1,
  0x3e5,
  0x3e9,
  0x3ed,
  0x3f1,
  0x1904,
  0x3f5,
  0x3f9,
  0x532066,
  0x3fd,
  0x401,
  0x405,
  0x409
]
def labelsBlock29 : Array Nat := #[
  0x632062,
  0xe24,
  0x40d,
  0x1950,
  0x1e18,
  0x910,
  0x3618,
  0x3c64,
  0x3190,
  0x3c78,
  0x2b84,
  0x3344,
  0x330c,
  0x3944,
  0x510,
  0x415
]
def labelsBlock30 : Array Nat := #[
  0x500,
  0x1086,
  0x108a,
  0x419,
  0x108e,
  0x41d,
  0x2590,
  0x421,
  0x504,
  0x1082,
  0x425,
  0x429,
  0x42d,
  0x431,
  0x435,
  0x439
]
def labelsBlock31 : Array Nat := #[
  0xd30,
  0x2414,
  0x50c,
  0x43d,
  0x1114,
  0x2114,
  0x52008a,
  0x1092,
  0x441,
  0x445,
  0x105e,
  0x449,
  0x51003e,
  0x44d,
  0x451,
  0x520086
]
def labelsBlock32 : Array Nat := #[
  0xc14,
  0x455,
  0x459,
  0x1096,
  0x45d,
  0x52003e,
  0x461,
  0x465,
  0x469,
  0x730086,
  0x46d,
  0x73008a,
  0x471,
  0x73003e,
  0x614,
  0x475
]
def labelsBlock33 : Array Nat := #[
  0x479,
  0x47d,
  0x740086,
  0x481,
  0x74008a,
  0x485,
  0x74008e,
  0x2510,
  0x489,
  0x521082,
  0x48d,
  0x53208e,
  0x491,
  0x495,
  0x499,
  0x49d
]
def labelsBlock34 : Array Nat := #[
  0x4a1,
  0x731082,
  0x73208a,
  0x1504,
  0x73002e,
  0x4a5,
  0x741082,
  0x74208a,
  0x4a9,
  0x74208e,
  0x2504,
  0x732082,
  0x732086,
  0x73102e,
  0x4ad,
  0x742082
]
def labelsBlock35 : Array Nat := #[
  0x742086,
  0x4b1,
  0x74308e,
  0x443082,
  0x443086,
  0x43202e,
  0x44308a,
  0x4b5,
  0x4b9,
  0x4bd,
  0x520046,
  0x14851003e,
  0x4c1,
  0x620086,
  0x18911003e,
  0x4c5
]
def labelsBlock36 : Array Nat := #[
  0x430086,
  0x10d52008a,
  0x105a,
  0x52004a,
  0x10d11003e,
  0x61005e,
  0x732092,
  0x51003a,
  0x742092,
  0x73205e,
  0x443092,
  0x35d0,
  0x4c9,
  0x110d2008a,
  0x14852003e,
  0x4cd
]
def labelsBlock37 : Array Nat := #[
  0x70208a,
  0x1d052003e,
  0x4d1,
  0x620092,
  0x62005e,
  0x732096,
  0x730092,
  0x52003a,
  0x742096,
  0x740092,
  0x53004a,
  0x73105e,
  0x10d520086,
  0x43008a,
  0x1072,
  0x10d12003e
]
def labelsBlock38 : Array Nat := #[
  0x443096,
  0x39e0,
  0x110d20086,
  0x4d5,
  0x50202e,
  0x62008e,
  0x14973008a,
  0x62004a,
  0x14533003e,
  0x51202e,
  0x149730086,
  0x63008e,
  0x14933003e,
  0x63004a,
  0x1056,
  0x430092
]
def labelsBlock39 : Array Nat := #[
  0x520092,
  0x4d9,
  0x73003a,
  0x1ccb3008a,
  0x1cc73003e,
  0x1e28,
  0x1ccb30086,
  0x1ccb3003e,
  0x50302e,
  0x14974008a,
  0x14974008e,
  0x61003e,
  0x51302e,
  0x149740086,
  0x14d74008e,
  0x62003e
]
def labelsBlock40 : Array Nat := #[
  0x440092,
  0x53204a,
  0x1d4121082,
  0x720086,
  0x72008a,
  0x1d413208e,
  0x1d012103e,
  0x4dd,
  0x10d521082,
  0x432086,
  0x43208a,
  0x10911002e,
  0x4e1,
  0x10d12103e,
  0x1c911002e,
  0x1cd521082
]
def labelsBlock41 : Array Nat := #[
  0x1cd12103e,
  0x442086,
  0x44208a,
  0x10d11002e,
  0x111521082,
  0x11153208e,
  0x4e5,
  0x110d21082,
  0x4e9,
  0x4ed,
  0x141741082,
  0x2ba8,
  0x504086,
  0x14174208a,
  0x14174208e,
  0x60103e
]
def labelsBlock42 : Array Nat := #[
  0x149741082,
  0x524086,
  0x14533002e,
  0x1026,
  0x14d74208e,
  0x141742082,
  0x141742086,
  0x50408a,
  0x14174308e,
  0x60203e,
  0x107a,
  0x145742082,
  0x14133102e,
  0x52408a,
  0x14974308e,
  0x61203e
]
def labelsBlock43 : Array Nat := #[
  0x154043082,
  0x33c8,
  0x154043086,
  0x15404308a,
  0x54008e,
  0x53003e,
  0x107e,
  0x4f1,
  0x4f5,
  0x2e18,
  0x154443082,
  0x15484308a,
  0x15003202e,
  0x54208e,
  0x154843082,
  0x154843086
]
def labelsBlock44 : Array Nat := #[
  0x15043202e,
  0x54308e,
  0x710,
  0x4f9,
  0x4fd,
  0x18911003a,
  0x194043086,
  0x19003202e,
  0x18d11003e,
  0x66510d2008a,
  0x1e60,
  0x2e28,
  0x501,
  0x505,
  0x1d052003a,
  0x19404308a
]
def labelsBlock45 : Array Nat := #[
  0x19043202e,
  0x18d12003e,
  0x66510d20086,
  0x1510,
  0x1540,
  0x1c8330086,
  0x1940,
  0x1c833008a,
  0x508,
  0x3180,
  0x2580,
  0x1414,
  0x15413208e,
  0x5600d521082,
  0x154032086,
  0x15403208a
]
def labelsBlock46 : Array Nat := #[
  0x502096,
  0x509,
  0x66510d21082,
  0x194843086,
  0x19153208e,
  0x19484308a,
  0x1e50,
  0x1e48,
  0x704,
  0x1530,
  0x2530,
  0x814,
  0x46254043086
]
def labelsGet (i : Nat) : Nat :=
  if i < 368 then
    if i < 176 then
      if i < 80 then
        if i < 32 then
          if i < 16 then
            labelsBlock0.getD (i-0) 3
          else
            labelsBlock1.getD (i-16) 3
        else
          if i < 48 then
            labelsBlock2.getD (i-32) 3
          else
            if i < 64 then
              labelsBlock3.getD (i-48) 3
            else
              labelsBlock4.getD (i-64) 3
      else
        if i < 128 then
          if i < 96 then
            labelsBlock5.getD (i-80) 3
          else
            if i < 112 then
              labelsBlock6.getD (i-96) 3
            else
              labelsBlock7.getD (i-112) 3
        else
          if i < 144 then
            labelsBlock8.getD (i-128) 3
          else
            if i < 160 then
              labelsBlock9.getD (i-144) 3
            else
              labelsBlock10.getD (i-160) 3
    else
      if i < 272 then
        if i < 224 then
          if i < 192 then
            labelsBlock11.getD (i-176) 3
          else
            if i < 208 then
              labelsBlock12.getD (i-192) 3
            else
              labelsBlock13.getD (i-208) 3
        else
          if i < 240 then
            labelsBlock14.getD (i-224) 3
          else
            if i < 256 then
              labelsBlock15.getD (i-240) 3
            else
              labelsBlock16.getD (i-256) 3
      else
        if i < 320 then
          if i < 288 then
            labelsBlock17.getD (i-272) 3
          else
            if i < 304 then
              labelsBlock18.getD (i-288) 3
            else
              labelsBlock19.getD (i-304) 3
        else
          if i < 336 then
            labelsBlock20.getD (i-320) 3
          else
            if i < 352 then
              labelsBlock21.getD (i-336) 3
            else
              labelsBlock22.getD (i-352) 3
  else
    if i < 560 then
      if i < 464 then
        if i < 416 then
          if i < 384 then
            labelsBlock23.getD (i-368) 3
          else
            if i < 400 then
              labelsBlock24.getD (i-384) 3
            else
              labelsBlock25.getD (i-400) 3
        else
          if i < 432 then
            labelsBlock26.getD (i-416) 3
          else
            if i < 448 then
              labelsBlock27.getD (i-432) 3
            else
              labelsBlock28.getD (i-448) 3
      else
        if i < 512 then
          if i < 480 then
            labelsBlock29.getD (i-464) 3
          else
            if i < 496 then
              labelsBlock30.getD (i-480) 3
            else
              labelsBlock31.getD (i-496) 3
        else
          if i < 528 then
            labelsBlock32.getD (i-512) 3
          else
            if i < 544 then
              labelsBlock33.getD (i-528) 3
            else
              labelsBlock34.getD (i-544) 3
    else
      if i < 656 then
        if i < 608 then
          if i < 576 then
            labelsBlock35.getD (i-560) 3
          else
            if i < 592 then
              labelsBlock36.getD (i-576) 3
            else
              labelsBlock37.getD (i-592) 3
        else
          if i < 624 then
            labelsBlock38.getD (i-608) 3
          else
            if i < 640 then
              labelsBlock39.getD (i-624) 3
            else
              labelsBlock40.getD (i-640) 3
      else
        if i < 704 then
          if i < 672 then
            labelsBlock41.getD (i-656) 3
          else
            if i < 688 then
              labelsBlock42.getD (i-672) 3
            else
              labelsBlock43.getD (i-688) 3
        else
          if i < 720 then
            labelsBlock44.getD (i-704) 3
          else
            if i < 736 then
              labelsBlock45.getD (i-720) 3
            else
              labelsBlock46.getD (i-736) 3
def lh (s : Nat) (d : List Nat) (ws : List Nat) (i : Nat) : Nat :=
  labelsGet (d.getD (((ws.getD (i / (64 / s)) 0) >>> ((i % (64 / s)) * s)) % 2 ^ s) 0)
def viewsBlock0 : Array View := #[
  ⟨0x4040404040404040,⟨6,by decide⟩,0x4040400040000000,[ew0,ew1,ew2],3,lh 2 [0,1,2,3] [0xd900]⟩,
  ⟨0x4400440044004400,⟨10,by decide⟩,0x4400400040000000,[ew0,ew3,ew4],3,fun _ => 3⟩,
  ⟨0x4444000044440000,⟨18,by decide⟩,0x4440000040000000,[ew1,ew3,ew5],3,fun _ => 3⟩,
  ⟨0x4444444400000000,⟨34,by decide⟩,0x4440400000000000,[ew2,ew4,ew5],3,fun _ => 3⟩,
  ⟨0xc0c0c0c00000000,⟨34,by decide⟩,0xc08080000000000,[ew6,ew7,ew8],3,fun _ => 3⟩,
  ⟨0xcc00cc00000000,⟨34,by decide⟩,0xc8008000000000,[ew9,ew10,ew11],3,fun _ => 3⟩,
  ⟨0xcccc00000000,⟨34,by decide⟩,0xc88000000000,[ew12,ew13,ew14],3,fun _ => 3⟩,
  ⟨0x606060606060606,⟨1,by decide⟩,0x602020002000200,[ew15,ew16,ew17,ew18],4,lh 3 [4,6,5,8,7,9,10,11] [0xe71a5b852000]⟩,
  ⟨0xc030c030c030c03,⟨0,by decide⟩,0xc02080008000800,[ew19,ew20,ew21,ew22],4,fun _ => 3⟩,
  ⟨0xf000f0000f000f,⟨0,by decide⟩,0xe000a000080000,[ew23,ew24,ew25,ew26],4,fun _ => 3⟩,
  ⟨0xf000f00000f000f,⟨0,by decide⟩,0xe000a0000080000,[ew27,ew28,ew29,ew30],4,fun _ => 3⟩,
  ⟨0x4444444444444444,⟨2,by decide⟩,0x4440400040000000,[ew31,ew32,ew33,ew34],6,lh 3 [2,0,1,12,13] [0x8d2000249000]⟩,
  ⟨0x5050505050505050,⟨4,by decide⟩,0x4040400040000000,[ew31,ew35,ew36,ew37],4,lh 3 [14,15,16,2,17] [0x851651000000]⟩,
  ⟨0xc0c0c0c0c0c0c0c,⟨2,by decide⟩,0xc08080008080800,[ew38,ew20,ew39,ew40],4,lh 3 [18,19,20,21,22] [0x851651000000]⟩,
  ⟨0xcccccccc,⟨2,by decide⟩,0xc8888880,[ew41,ew42,ew43,ew44],5,lh 3 [23,24,2,16,25] [0x808608408408]⟩,
  ⟨0xcccccccc00000000,⟨34,by decide⟩,0xccc8c88000000000,[ew45,ew46,ew47,ew48],6,fun _ => 3⟩
]
def viewsBlock1 : Array View := #[
  ⟨0xf0f00000f0f0000,⟨16,by decide⟩,0xe0a00000a080000,[ew49,ew39,ew50,ew51],5,fun _ => 3⟩,
  ⟨0xff000000ff0000,⟨16,by decide⟩,0xea000000a80000,[ew52,ew53,ew54,ew55],5,fun _ => 3⟩,
  ⟨0xffff0000,⟨16,by decide⟩,0xeaa80000,[ew56,ew44,ew57,ew58],5,fun _ => 3⟩,
  ⟨0x4812481248124812,⟨1,by decide⟩,0x4802480048000800,[ew59,ew60,ew61,ew62],5,fun _ => 3⟩,
  ⟨0x1212484812124848,⟨3,by decide⟩,0x202480002000800,[ew63,ew64,ew65,ew66],4,lh 3 [7,26,27,20,28,29,30,31] [0xfac689000009]⟩,
  ⟨0x8282414182824141,⟨0,by decide⟩,0x8282400082800000,[ew67,ew68,ew69,ew70],5,fun _ => 3⟩,
  ⟨0x666600006666,⟨1,by decide⟩,0x622000002220,[ew71,ew72,ew73,ew74],4,fun _ => 3⟩,
  ⟨0x6666000066660000,⟨17,by decide⟩,0x6662000062200000,[ew33,ew75,ew76,ew77],6,fun _ => 3⟩,
  ⟨0x5a005a005a005a,⟨1,by decide⟩,0x4a000000080000,[ew78,ew79,ew80,ew81],4,fun _ => 3⟩,
  ⟨0x5a5a00005a5a0000,⟨17,by decide⟩,0x4a4a00004a080000,[ew36,ew82,ew83,ew84],4,fun _ => 3⟩,
  ⟨0x5a5a5a5a,⟨1,by decide⟩,0x4a080a00,[ew85,ew86,ew87,ew88],4,fun _ => 3⟩,
  ⟨0x50a050a050a050a,⟨1,by decide⟩,0x40a000000080000,[ew89,ew90,ew91,ew92],4,fun _ => 3⟩,
  ⟨0x55aa000055aa0000,⟨17,by decide⟩,0x44aa000040a80000,[ew93,ew94,ew95,ew96],4,fun _ => 3⟩,
  ⟨0x50505050a0a0a0a,⟨1,by decide⟩,0x40000000a080a00,[ew97,ew98,ew99,ew100],4,fun _ => 3⟩,
  ⟨0x55005500aa00aa,⟨1,by decide⟩,0x40000000a800a0,[ew101,ew102,ew103,ew104],4,fun _ => 3⟩,
  ⟨0x55550000aaaa0000,⟨17,by decide⟩,0x44400000aaa80000,[ew105,ew106,ew107,ew108],4,fun _ => 3⟩
]
def viewsBlock2 : Array View := #[
  ⟨0xcccccccccccccccc,⟨2,by decide⟩,0xccc8c880c8888880,[ew109,ew110,ew111,ew112,ew113],8,lh 3 [14,21,20,32,33,34] [0x1249000000000000,0x15c692449]⟩,
  ⟨0xf0f0f0f0f0f0f0f,⟨0,by decide⟩,0xe0a0a000a080a00,[ew114,ew115,ew116,ew117,ew118],7,lh 3 [7,35,36,21,19,37] [0x1489000000000000,0x1612912d9]⟩,
  ⟨0xff00ff00ff00ff,⟨0,by decide⟩,0xea00a000a800a0,[ew119,ew120,ew121,ew122,ew123],7,fun _ => 3⟩,
  ⟨0xffff0000ffff0000,⟨16,by decide⟩,0xeeea0000eaa80000,[ew124,ew112,ew125,ew126,ew127],7,lh 3 [7,38,39,23,35,40] [0x1249000000000000,0x15c692449]⟩,
  ⟨0x5a5a5a5a5a5a5a5a,⟨1,by decide⟩,0x4a4a4a004a080a00,[ew128,ew129,ew130,ew131,ew132],7,lh 3 [14,41,9,42,43,44] [0x2249000000000000,0x163649292]⟩,
  ⟨0x55aa55aa55aa55aa,⟨1,by decide⟩,0x44aa40a040a800a0,[ew133,ew134,ew135,ew136,ew137],7,fun _ => 3⟩,
  ⟨0xffffffffffffffff,⟨0,by decide⟩,0xeeeaeaa0eaa8aaa0,[ew138,ew139,ew140,ew141,ew142,ew143],10,lh 3 [45,23,42,36,46,14,21,47] [0x1000851000651000,0xca20014a2000ca,0x1440019440031440,0x7]⟩
]
def viewsGet (i : Nat) : Option View :=
  if i < 16 then
    viewsBlock0[(i-0)]?
  else
    if i < 32 then
      viewsBlock1[(i-16)]?
    else
      viewsBlock2[(i-32)]?
def nodesBlock0 : Array Node := #[
  ⟨0,3,[ew0,ew1,ew2],lh 3 [1,48,0,14,16,2] [0x483112144265808,0x1522c946b71b]⟩,
  ⟨7,4,[ew15,ew16,ew17,ew18],lh 4 [6,18,51,50,49,10,9,7,8,5,52,53,54,55,56] [0x466033454434050,0x7001047742206002,0x5223633225684110,0x1cba511373311579,0xe112d221]⟩,
  ⟨7,3,[ew15,ew16,ew144],lh 3 [18,5,50,6,9,49] [0x38d816469526a4c9,0x4051200c340]⟩,
  ⟨7,3,[ew15,ew16,ew144,ew17],lh 3 [5,50,18,6,49,7,51] [0x20484508dc4d5208,0x6]⟩,
  ⟨7,3,[ew15,ew16,ew144,ew18],lh 3 [50,8,51,6,49,18,9,5] [0x52074118dc4d6041,0x5]⟩,
  ⟨7,3,[ew145,ew15,ew16,ew17],lh 3 [18,50,51,5,6,7,57,9] [0x14d45cb2f0a01a04,0x2]⟩,
  ⟨7,3,[ew146,ew15,ew16,ew18],lh 3 [18,51,50,8,6,9,57,7] [0x20c41d34f0a4aa4c]⟩,
  ⟨7,2,[ew15,ew16,ew144],lh 3 [5,6,49,9,4] [0x8e044b210]⟩,
  ⟨11,6,[ew31,ew32,ew33,ew34],lh 5 [2,0,1,12,18,48,17,50,60,58,51,62,64,24,16,14,59,61,63,65,66,67] [0x40ce330c42824e7,0x3240088d4a32442,0x9348430c005a54a,0x3342160c8430c21,0x59ca541c00988a5,0x40882a382140800,0xa81e04388460821,0x58020615e559421]⟩,
  ⟨11,5,[ew0,ew31,ew32,ew33,ew34],lh 5 [2,0,17,48,18,58,50,14,60,51,12,1,62,64,68,69,70,71,72,73,74,75] [0x1096232c48508aa,0x7800c18d8003863,0x89ced085a73c021,0x925251150630842,0x99082000a949400,0xa0c62084a421421,0xa8428000c319800,0x1c08210c109884,0x806718c21]⟩,
  ⟨11,5,[ew1,ew31,ew32,ew33,ew34],lh 5 [0,1,17,18,12,51,16,50,62,14,60,2,64,58,68,76,77,78,72,79,80,81] [0x518ce0844868884,0x109622ade632821,0x8800c18d8004063,0x10424390810c8e7,0x98c641110528842,0xd0220008319000,0x30001284e839ca5,0xaa52618c2000461,0x8000a929400]⟩,
  ⟨11,5,[ew2,ew31,ew32,ew33,ew34],lh 5 [2,1,48,17,50,18,24,64,51,16,12,60,62,0,70,82,77,83,73,79,84,85] [0x5842e2106750cca,0x60850001e10ac84,0x18da32b62213000,0x18426210c10c884,0x18006420c004d08,0x8846198e528c63,0x4d1210008211000,0x540929427084a1,0x28047108a2]⟩,
  ⟨11,5,[ew31,ew3,ew32,ew33,ew34],lh 5 [0,12,1,18,48,60,24,58,17,62,14,2,64,68,86,74,80,50,87,88,89,90] [0xa026718c8305a1,0x388412842211de7,0x908749ce420601,0x3000118c2001863,0x2956822ca98a042,0x98c6c001831c800,0xa000228924214a5,0xaa94518c4000862,0x90008a21000]⟩,
  ⟨11,5,[ew31,ew4,ew32,ew33,ew34],lh 5 [2,12,0,58,60,51,16,48,17,64,24,1,62,70,91,75,84,87,92,18,89,93] [0x1a0617042808da3,0x198612042608de3,0x800329460004a5,0x508414842212a0a,0x614b1000895a0cb,0x2126810a452b000,0x2000639cc0050e7,0x54062192211084,0x100e939c42]⟩,
  ⟨11,5,[ew31,ew32,ew5,ew33,ew34],lh 5 [1,12,2,50,58,62,14,17,64,24,16,60,0,77,94,81,85,87,95,90,93,48] [0x200011842001063,0x9c2471087205a1,0x884429082105e1,0x498c1404260a609,0x2c0390c6b18220,0x84328c6210260,0x518c04000602a8a,0x29587330a8a9c42,0x228906314a5]⟩,
  ⟨11,4,[ew147,ew31,ew32,ew33,ew34],lh 4 [0,1,48,51,18,12,2,24,16,64,96,50,14] [0x23151ba090668175,0xc40101232040423,0x2]⟩
]
def nodesBlock1 : Array Node := #[
  ⟨11,4,[ew148,ew31,ew32,ew33,ew34],lh 4 [2,0,1,12,50,58,14,18,48] [0x2416168042425353,0x2104021717050323,0x61071]⟩,
  ⟨11,4,[ew149,ew31,ew32,ew33,ew34],lh 4 [2,0,18,48,12,1,50,51,62,97,14,24,58] [0x7c6b6a190805544,0x1021210303121207,0x3]⟩,
  ⟨11,4,[ew150,ew31,ew32,ew33,ew34],lh 4 [2,48,50,58,24,12,1,16,0,51,14] [0x4288101027663455,0x270101a334090932,0x110a2]⟩,
  ⟨11,4,[ew0,ew1,ew32,ew33,ew34],lh 4 [0,51,12,18,50,60,58,1,14,2,62,98] [0x54802021a1772652,0x3030141b03039964,0x108]⟩,
  ⟨11,4,[ew0,ew2,ew32,ew33,ew34],lh 4 [48,2,18,50,58,60,12,1,0,64,24,99] [0x53a2921010776654,0x232b101088010143,0x1001]⟩,
  ⟨11,4,[ew0,ew31,ew3,ew33,ew34],lh 4 [0,1,48,18,50,17,14,58,2,12,62,98] [0x54601012a2145191,0x3030880303272b74,0x206]⟩,
  ⟨11,4,[ew0,ew31,ew4,ew33,ew34],lh 4 [2,0,51,50,48,12,17,1,58,64,16,99,18] [0x63a1910404776355,0xc12020181b020283,0x410]⟩,
  ⟨11,4,[ew151,ew31,ew32,ew33,ew34],lh 4 [0,48,18,51,58,12,1,2,14] [0x5420203177665454,0x2031310202131345,0x10820]⟩,
  ⟨11,4,[ew152,ew31,ew32,ew33,ew34],lh 4 [1,2,18,12,51,0,50,58,60,100,48,14,16] [0x14030655a1908073,0x21200c1610b23214,0x14]⟩,
  ⟨11,4,[ew153,ew31,ew32,ew33,ew34],lh 4 [2,1,0,12,51,16,24,50,58,48,18] [0x17a2409015153638,0x1207012326040413,0x42052]⟩,
  ⟨11,4,[ew1,ew2,ew32,ew33,ew34],lh 4 [1,18,12,51,62,24,16,2,50,0,58,64,101] [0x851b1776050a242,0x1006083099234302,0x131c]⟩,
  ⟨11,4,[ew1,ew31,ew3,ew32,ew34],lh 4 [0,18,48,1,17,2,51,12,58,60,98,50] [0x4602012392554282,0x1010b30101373a76,0x1030]⟩,
  ⟨11,4,[ew1,ew31,ew32,ew5,ew34],lh 4 [2,1,12,14,51,16,17,50,0,58,48,64,101] [0x1703b00a60500190,0x151741322c246412,0x8831]⟩,
  ⟨11,4,[ew154,ew31,ew32,ew33,ew34],lh 4 [2,0,48,18,1,12,58,24,51,50] [0x4631310202947655,0x4102021313080847,0x21031]⟩,
  ⟨11,4,[ew155,ew31,ew32,ew33,ew34],lh 4 [1,48,12,18,50,14,24,2,0,58,16] [0x435887740406292,0xa01415323161202,0x311530]⟩,
  ⟨11,4,[ew2,ew31,ew4,ew32,ew33],lh 4 [2,0,18,48,24,51,17,16,1,12,60,99] [0x62301017a1126191,0x5020880505744b42,0x303]⟩
]
def nodesBlock2 : Array Node := #[
  ⟨11,4,[ew2,ew31,ew32,ew5,ew33],lh 4 [1,2,50,18,12,17,0,24,62,14,101,48] [0x291816653020244,0x100230171a735302,0xb112]⟩,
  ⟨11,4,[ew156,ew31,ew32,ew33,ew34],lh 4 [0,1,48,18,50,51,12,2,14] [0x1403032577141466,0x1012520303252514,0x20830]⟩,
  ⟨11,4,[ew31,ew157,ew32,ew33,ew34],lh 4 [2,0,12,1,48,58,17,102,24,50,51,18,14] [0x1218050232352762,0x10c1310404b1a093,0x4]⟩,
  ⟨11,4,[ew158,ew31,ew32,ew33,ew34],lh 4 [2,1,48,12,24,18,16,0,58,50] [0x1877202016193434,0x1602024535080313,0x22051]⟩,
  ⟨11,4,[ew31,ew3,ew4,ew33,ew34],lh 4 [0,12,1,48,24,58,62,2,50,64,16,18,103] [0x104353121251441,0xb02363a090778262,0x30c]⟩,
  ⟨11,4,[ew31,ew3,ew32,ew5,ew34],lh 4 [2,12,1,48,14,24,58,60,0,50,64,103] [0x4115363121260501,0x2b237304a0037090,0x8842]⟩,
  ⟨11,4,[ew159,ew31,ew32,ew33,ew34],lh 4 [2,0,18,51,12,48,1,50,16,58] [0x4712120303876694,0x2105051212030384,0x51021]⟩,
  ⟨11,4,[ew160,ew31,ew32,ew33,ew34],lh 4 [0,1,12,58,51,14,16,2,50,18,24] [0x1305097761813232,0x101641020a243412,0x40550]⟩,
  ⟨11,4,[ew31,ew4,ew32,ew5,ew33],lh 4 [2,58,12,0,1,60,16,18,62,14,103,48] [0x102313212211221,0xa63539080735344,0xb006]⟩,
  ⟨11,4,[ew161,ew31,ew32,ew33,ew34],lh 4 [2,1,50,18,51,12,0,14,48,58,16] [0x1273660408121255,0x1a02017393040412,0x43031]⟩,
  ⟨11,4,[ew162,ew31,ew32,ew33,ew34],lh 4 [2,0,12,48,58,1,14,50,18,24] [0x2761810303552424,0x7103031219040242,0x31061]⟩,
  ⟨11,3,[ew163,ew31,ew32,ew33],lh 3 [2,0,18,1,48,51,50,12] [0x41457de80829944a,0x20]⟩,
  ⟨11,3,[ew164,ew31,ew32,ew34],lh 3 [2,0,48,1,18,51,50,12] [0x130c7de088402a05,0x10b]⟩,
  ⟨11,3,[ew0,ew1,ew3,ew34],lh 4 [0,48,1,18,17,2,60,51,14] [0x5541802027422161,0x30300103]⟩,
  ⟨11,3,[ew0,ew2,ew4,ew33],lh 4 [2,0,18,48,17,1,60,12,51] [0x1241030355427161,0x80203010]⟩,
  ⟨11,3,[ew165,ew31,ew33,ew34],lh 3 [2,0,1,48,18,51,50,12] [0x30c1458510c3e96,0x19]⟩
]
def nodesBlock3 : Array Node := #[
  ⟨11,3,[ew1,ew2,ew32,ew5],lh 4 [2,1,12,17,50,18,0,62,16,48] [0x1214093080010270,0x14516635]⟩,
  ⟨11,3,[ew166,ew32,ew33,ew34],lh 3 [2,0,1,18,48,51,50,12] [0x6511042cb1455d6,0x21]⟩,
  ⟨11,3,[ew31,ew3,ew4,ew5],lh 3 [2,0,1,12,58,60,24,62] [0x10680b830b4d4183,0x8d]⟩,
  ⟨14,5,[ew41,ew42,ew43,ew44],lh 6 [24,20,21,2,33,23,16,19,32,126,104,30,105,106,107,108,109,110,111,112,113,114,115,116,117,118,119,120,121,122,123,124,125,127,128,129,130,131,132] [0x30810b285005,0x4081883c510e348,0x53487187447047,0x5c50965470c3508,0x416870996050c5,0x7400417001806c4,0xc07c4082784184,0x8840c9840089800,0x829060c38c1082,0x9810c1946]⟩,
  ⟨14,4,[ew167,ew41,ew42,ew43,ew44],lh 4 [23,24,2,16,21,32,33,133,134,135,136,30,19,118,20] [0x1ba29283736150,0x42114311ed00203c,0x232]⟩,
  ⟨14,4,[ew41,ew42,ew168,ew43,ew44],lh 4 [2,16,21,20,23,137,24,30,32,33,138,139,140,141] [0x3662020315544987,0x20d0c1b1a0202131,0x10]⟩,
  ⟨14,4,[ew169,ew41,ew42,ew43,ew44],lh 4 [2,24,21,16,20,23,137,33,32,107] [0x6981202043437155,0x2011231142020436,0x30]⟩,
  ⟨14,4,[ew170,ew41,ew42,ew43,ew44],lh 4 [21,20,2,23,33,16,32,24,107] [0x3843202051517463,0x402041510302151,0x102]⟩,
  ⟨14,4,[ew171,ew41,ew42,ew43,ew44],lh 4 [21,33,32,24,20,23,2,19,142,143,144,145,137,16] [0x1225b0a044918172,0x1030133105022dc,0x606]⟩,
  ⟨14,4,[ew41,ew42,ew43,ew172,ew44],lh 4 [21,19,33,20,24,2,137,32,146,147,16,148,149] [0x3431501713161421,0xb3050a3204092282,0xc0]⟩,
  ⟨14,4,[ew173,ew41,ew42,ew43,ew44],lh 4 [21,19,24,33,2,20,32,16,112] [0x1231040455323261,0x302032231401817,0x404]⟩,
  ⟨14,4,[ew174,ew41,ew42,ew43,ew44],lh 4 [21,2,24,33,20,32,19,16,23,112] [0x3558101074232366,0x122032240101945,0x101]⟩,
  ⟨14,4,[ew175,ew41,ew42,ew43,ew44],lh 4 [24,16,2,19,20,23,150,151,152,153,21,32,112,115,33] [0x30b0a29181706053,0x4200e100432dc131,0x212]⟩,
  ⟨14,4,[ew41,ew42,ew43,ew44,ew176],lh 4 [24,23,16,20,21,33,2,115,19,154,155,156,157] [0x38141712311051,0x22b3224a00950042,0x66c]⟩,
  ⟨14,4,[ew177,ew41,ew42,ew43,ew44],lh 4 [24,23,16,20,2,33,19,21,118] [0x1051743232505061,0x3400520038141231,0x424]⟩,
  ⟨14,4,[ew178,ew41,ew42,ew43,ew44],lh 4 [24,16,20,33,19,21,23,2,32,112,118] [0x4080771212030366,0x530051002a549141,0x211]⟩
]
def nodesBlock4 : Array Node := #[
  ⟨14,4,[ew41,ew179,ew42,ew43,ew44],lh 4 [158,23,21,2,33,24,16,115,118,159,20] [0x870100110011001,0x242344a932326655,0x323]⟩,
  ⟨14,4,[ew41,ew42,ew43,ew180,ew44],lh 4 [158,23,21,2,24,16,33,115,118,159,20] [0x870100110011001,0x23232a5344266549,0x323]⟩,
  ⟨14,4,[ew181,ew41,ew42,ew43,ew44],lh 4 [32,21,20,158,33,23,24,2,16,160,161,118,162] [0x5005a19182440303,0x17161c620b100320,0x217]⟩,
  ⟨14,4,[ew182,ew41,ew42,ew43,ew44],lh 4 [19,21,32,16,2,33,20,24,163,164,118,162] [0x220918166750202,0x14141b350a102303,0x434]⟩,
  ⟨14,4,[ew41,ew183,ew42,ew43,ew44],lh 4 [165,19,16,20,33,2,21,24,166] [0x1001021010011001,0x6468232355232374,0x322]⟩,
  ⟨14,4,[ew41,ew42,ew43,ew44,ew184],lh 4 [165,24,19,16,2,20,166,33,21] [0x2002200403202101,0x3354345714163115,0x845]⟩,
  ⟨14,4,[ew185,ew41,ew42,ew43,ew44],lh 4 [165,24,16,19,32,2,20,21,33,167,168,126] [0x310155a292814040,0x7b17211630030230,0x622]⟩,
  ⟨14,4,[ew186,ew41,ew42,ew43,ew44],lh 4 [23,16,2,165,20,24,19,169,170,21,33,126] [0x330928171550303,0x4b2a141460020160,0x212]⟩,
  ⟨14,4,[ew41,ew42,ew187,ew43,ew44],lh 4 [23,24,171,33,19,20,21,126,16,2,165,172] [0x42240220022001a0,0x9988771631153113,0x56b]⟩,
  ⟨14,4,[ew41,ew42,ew43,ew44,ew188],lh 4 [171,24,33,2,23,32,16,165,19,172,20,21] [0x5005800340040170,0x6369211221122112,0xb3a]⟩,
  ⟨14,4,[ew189,ew41,ew42,ew43,ew44],lh 4 [33,171,21,24,19,20,23,173,174,2,16,175] [0x301925580704141,0x232033021246116,0xba2]⟩,
  ⟨14,4,[ew190,ew41,ew42,ew43,ew44],lh 4 [33,171,20,24,23,21,2,176,177,16,19,175] [0x301559280704141,0x3300232a1162124,0xb62]⟩,
  ⟨14,3,[ew41,ew42,ew191,ew44],lh 3 [23,137,24,2,16,21,20] [0x5695896201048048,0xe3]⟩,
  ⟨14,3,[ew192,ew41,ew42,ew44],lh 4 [23,24,2,16,137,21,20,32,118] [0x170232513163044,0x21158002]⟩,
  ⟨14,3,[ew41,ew42,ew43,ew193],lh 4 [23,24,2,16,21,30,19,118,20] [0x3118700203600150,0x23242114]⟩,
  ⟨14,3,[ew194,ew41,ew42,ew43],lh 4 [24,2,23,16,21,30,137,118,20] [0x2055311401042721,0x30082366]⟩
]
def nodesBlock5 : Array Node := #[
  ⟨14,3,[ew41,ew42,ew195,ew44],lh 4 [2,23,16,21,30,137,24,32,118,20] [0x6629811012551744,0x2030303]⟩,
  ⟨14,3,[ew196,ew41,ew42,ew44],lh 3 [24,2,16,21,20,137,30,19] [0x3e59e36651810b62,0x40]⟩,
  ⟨14,3,[ew41,ew42,ew197,ew43],lh 4 [2,16,21,20,30,23,137,24,32,19] [0x7702316655209844,0x10021313]⟩,
  ⟨14,3,[ew198,ew41,ew42,ew43],lh 3 [24,23,2,21,16,30,137,20] [0x733622d694610459,0x100]⟩,
  ⟨14,3,[ew41,ew199,ew43,ew44],lh 4 [21,32,23,19,30,33,24,20,2] [0x7765020114413312,0x80805060]⟩,
  ⟨14,3,[ew200,ew41,ew43,ew44],lh 3 [19,21,20,32,24,33,23,2] [0x1188403a61aa2618,0x8f]⟩,
  ⟨14,3,[ew41,ew42,ew43,ew201],lh 4 [32,21,33,24,19,23,137,16,2,20] [0x2332441007602005,0x91812131]⟩,
  ⟨14,3,[ew202,ew41,ew42,ew43],lh 3 [19,21,20,32,24,33,23,2] [0x24030d82b9361c08,0x154]⟩,
  ⟨14,3,[ew41,ew203,ew43,ew44],lh 4 [19,21,20,33,24,32,137,23,2] [0x3242071020060530,0x21813141]⟩,
  ⟨14,3,[ew204,ew41,ew43,ew44],lh 3 [19,21,20,32,33,24,2] [0x118840334c5540c3,0x8e]⟩,
  ⟨14,3,[ew41,ew42,ew43,ew205],lh 3 [19,21,20,32,24,33,23,2] [0x1a61aa21884030d8,0x8f]⟩,
  ⟨14,3,[ew206,ew41,ew42,ew43],lh 3 [19,21,20,33,24,23,2,137] [0x2407118391319045,0xd4]⟩,
  ⟨14,3,[ew41,ew207,ew43,ew44],lh 4 [24,2,16,23,19,20,32,112,115,33] [0x2005418172423360,0x12151009]⟩,
  ⟨14,3,[ew208,ew41,ew43,ew44],lh 4 [23,24,16,2,21,19,115,32,20] [0x250311421181070,0x32345066]⟩,
  ⟨14,3,[ew41,ew42,ew209,ew44],lh 4 [24,2,19,16,23,115,20,32,33] [0x3006215544232070,0x13161008]⟩,
  ⟨14,3,[ew210,ew41,ew42,ew44],lh 4 [23,24,16,2,19,21,115,20,32] [0x180323512172040,0x31154066]⟩
]
def nodesBlock6 : Array Node := #[
  ⟨14,3,[ew41,ew211,ew43,ew44],lh 4 [23,24,16,19,115,20,21,33,2] [0x2115304402300170,0x52268116]⟩,
  ⟨14,3,[ew212,ew41,ew43,ew44],lh 3 [24,23,16,2,21,20,115,19] [0x48762a9803a023c8,0xd3]⟩,
  ⟨14,3,[ew41,ew42,ew213,ew44],lh 4 [23,24,16,21,20,115,2,32,33] [0x2114305502400170,0x66238113]⟩,
  ⟨14,3,[ew214,ew41,ew42,ew44],lh 4 [23,24,16,2,112,21,115,20,33] [0x180532371210402,0x31154066]⟩,
  ⟨14,3,[ew41,ew179,ew180,ew44],lh 3 [158,23,24,21,2,115,118,162] [0x38e24fa1a8201201,0x4]⟩,
  ⟨14,3,[ew41,ew42,ew43,ew215],lh 4 [32,21,20,23,158,24,162,33,2] [0x6252100404203003,0x21817151]⟩,
  ⟨14,3,[ew41,ew42,ew43,ew216],lh 4 [32,21,20,33,24,23,158,118,2] [0x3242071006203005,0x21813141]⟩,
  ⟨14,3,[ew41,ew42,ew43,ew217],lh 3 [19,32,21,33,24,162,2,20] [0x26a2763201201048,0x1d6]⟩,
  ⟨14,3,[ew41,ew42,ew218,ew43],lh 3 [19,32,21,16,20,118,2,33] [0x271ceb2201150048,0xe3]⟩,
  ⟨14,3,[ew41,ew183,ew43,ew184],lh 3 [24,165,19,16,20,126,21] [0x37a860444a2d1408,0x4]⟩,
  ⟨14,3,[ew41,ew42,ew219,ew44],lh 3 [24,165,19,16,2,21,126,20] [0x5d8560744c2d1408,0x11c]⟩,
  ⟨14,3,[ew41,ew42,ew220,ew44],lh 3 [24,165,19,16,21,126,2,20] [0x4b4460744a2d1408,0x1b3]⟩,
  ⟨14,3,[ew41,ew42,ew221,ew44],lh 4 [23,24,165,2,20,16,126,19,33] [0x5114700320020120,0x35346618]⟩,
  ⟨14,3,[ew41,ew222,ew42,ew44],lh 4 [23,2,16,19,165,24,21,126,20] [0x5528300104400230,0x77161216]⟩,
  ⟨14,3,[ew41,ew42,ew187,ew188],lh 4 [171,24,23,32,2,126,165,33,21,175] [0x4117300320020160,0x945518]⟩,
  ⟨14,3,[ew41,ew223,ew43,ew44],lh 3 [21,171,33,24,23,2,20,175] [0x418d9a04584c4d1,0x1c5]⟩
]
def nodesBlock7 : Array Node := #[
  ⟨14,3,[ew41,ew224,ew43,ew44],lh 3 [21,20,33,171,24,23,19,16] [0x4204610c62cd513,0x47]⟩,
  ⟨14,3,[ew41,ew225,ew43,ew44],lh 4 [20,171,33,23,2,24,21,19,175] [0x2050711401032321,0x8406652]⟩,
  ⟨14,3,[ew41,ew226,ew43,ew44],lh 3 [21,20,33,171,24,2,23] [0x4204610c52ce513,0x45]⟩,
  ⟨20,4,[ew63,ew64,ew65,ew66],lh 4 [179,1,178,7,14,38,180,29,20,28,30,181,182] [0x688a22070029a79,0x3664603061108001,0x7552112527110406,0x1535c33242232b44,0x54513114]⟩,
  ⟨20,3,[ew63,ew65,ew227,ew66],lh 3 [38,1,179,180,178,29,7] [0x40481604da4da208,0x6]⟩,
  ⟨20,3,[ew228,ew63,ew65,ew66],lh 3 [38,1,180,178,179,29,14] [0x1222508233208a9a]⟩,
  ⟨32,8,[ew109,ew110,ew111,ew112,ew113],lh 6 [183,0,19,20,33,2,21,23,24,32,16,195,197,18,51,14,1,185,48,196,190,36,184,186,187,188,162,189,191,192,58,193,126,194,198,199,200,175,201] [0x208009109002202,0x9289002102009,0xc300228a0020c2,0x7186002142009,0x3c7002182007147,0x113d1011016007,0x4105c40c3007007,0x6c429a6480c3608,0x186748492704514,0x2c43448441607de,0x41313353313041,0x8ca38e8954952c4,0x4198316590a186,0x31004131034d2c3,0x412c53c52c3343,0x2c504130e3ce30e]⟩,
  ⟨32,7,[ew109,ew229,ew110,ew111,ew112,ew113],lh 5 [202,22,158,2,14,33,20,17,0,185,60,50,58,190,23,21,18,183,62,64,205,24,16,203,204] [0xa220080202629,0x8a20398e02409,0x2569038a50098c,0x24c60096b008c2,0x386e039ee00862,0x240900882009ef,0x44a50080202484,0x39cf6044c652955,0xc9ef0c863085ef,0xcc84085080dc63,0x3a8f8084840cd08,0x95ad394e5528c6,0x394650b1ad3b06c,0xb2103b08409605,0x52c63a19a639484,0x990651863a2dab,0x51a100ad0852e0b,0xb4840b50808c83,0x8d08]⟩,
  ⟨32,7,[ew109,ew110,ew111,ew230,ew112,ew113],lh 5 [206,17,32,16,2,24,0,23,21,60,14,19,1,190,12,183,207,185,18,195,208,197,184,204,33,20,203,62] [0x8a20080202ca5,0x2c0b0086202c0b,0x1de70080202c63,0x1c07009e200802,0x1c8701da700882,0x441601cc7009a2,0xa43701c07044d1,0x15e50846309425,0x94850b90808438,0x96450b88409508,0x954a0ba520b94e,0x4b1080853900de3,0x4b08c48d0348c84,0x4b0c64b14c48cc3,0x84840e90848d43,0x84c33084840ed08,0x84cc6a5435084c6,0xa354da34c68114a,0x810c6]⟩,
  ⟨32,7,[ew231,ew109,ew110,ew111,ew112,ew113],lh 5 [209,32,60,24,190,0,48,14,19,50,20,17,210,211,23,12,2,183,22,185,18,16,195,197,33,62,203,184,162] [0x1080002104508,0x148580446304421,0x108845ad7504555,0x168c610884164c6,0x6dce76dca5658e7,0x40102068658a5,0x5210200800461,0x5410212902148,0x38ce03884004c6,0x4c1b038ae00481,0x109290380e04cb3,0x93c845897c58d63,0x5bccf90c8358cc3,0x6be946bcef60e83,0x12609128c660ce7,0x628aa12a10124c9,0x628ea6a4a56a4e7,0x690e4690a5640f0,0x640a5]⟩,
  ⟨32,7,[ew20,ew109,ew110,ew111,ew112,ew113],lh 5 [212,17,16,0,19,32,58,190,51,33,213,214,18,23,14,2,21,1,185,183,60,195,197,205,12,20,22,62,203,184,162] [0xa50008404e52,0x843804d2904c84,0x84e70e83904c42,0xf108084e70ed08,0x5d8635d98c55463,0x1525010c45558c,0x144501124014c6,0x14050104401004,0x350d034e701508,0x481d0346d014e5,0x98260340d04872,0xa5080d03e08442,0xa5ef09906099e6,0x5998c599c652589,0xa09efbc610525ce,0x50862a45f1b8a02,0x509c25c4635c5d1,0x59dc759c63541d0,0x54063]⟩,
  ⟨32,7,[ew109,ew232,ew110,ew111,ew112,ew113],lh 5 [215,16,19,165,12,0,14,20,51,17,62,216,217,185,33,22,21,183,36,18,190,60,195,197,203,184,24,205,2,218] [0xe2300c030362d,0xdc3008820340d,0xc23009c200c84,0xce700822008e2,0xd0800e8300902,0x3419008a200a82,0x448400802034ad,0x7d4217bce75295a,0x45087ec217d4e7,0x65ca55d8c64a53c,0x7b8e75d8a565cc6,0x4b821790e749024,0x4912452a104a93d,0x61273610c45ba6e,0x50501c4a105b8c6,0x584a1c490850601,0x584c1648a5648c6,0x620c8620a55c0c6,0x5c0a5]⟩,
  ⟨32,7,[ew109,ew110,ew111,ew112,ew233,ew113],lh 5 [219,17,16,32,23,20,19,24,2,58,0,220,221,48,14,62,18,36,183,185,195,197,184,218,33,205,60,21] [0xce300c03018e7,0x1a2600c4301806,0xda300e2301846,0xc030110401004,0x12440100401a46,0x4c160114401806,0xa4a50100404d53,0xa44909ca509c47,0x85080a4290bc37,0x59e070843802649,0x59d476261062549,0x789a278908795a5,0x88220972579505,0x589420974508822,0x58a026455164610,0x5a1c8085fb0364d,0x5a148635ce6354a,0x65435655ce5d034,0x5d1ce]⟩,
  ⟨32,7,[ew234,ew109,ew110,ew111,ew112,ew113],lh 5 [222,32,62,14,19,36,1,0,24,58,21,17,223,224,51,23,16,20,183,22,185,18,190,33,60,2,195,197,205,184,126] [0x840002104884,0x14c570493704821,0x160a5160c6108a5,0x5ad7904959170c6,0x6ece76ec63668e7,0x4010110466863,0x4c60100400508,0x4a1010c6010a4,0x3dcf03d4a005c1,0x501d03c6f00541,0x9a4a503c0f05074,0x5a4c99a2285a0c8,0x5897e5a569109ce,0x6a6b56a469622a8,0x141ce1455162063,0x640f0145d114150,0x64070694e569463,0x6d8766d8e76286a,0x628e7]⟩,
  ⟨32,7,[ew39,ew109,ew110,ew111,ew112,ew113],lh 5 [225,17,23,12,2,19,36,50,0,18,33,226,227,14,32,20,16,48,183,185,62,195,197,203,24,60,205,190,22,184,126] [0x1ce00042049ce,0x84380494a04842,0x84c60e4e7084c6,0xf03b048840e8e7,0x65908659295d508,0x394e008625d529,0x8e70094203863,0x8c2014e5014c6,0x8820080201485,0x4c1d0152501405,0xa8e70140504d33,0xaa1008ce308e03,0xd03e0848408c23,0x60d2360da35a929,0xa4090bbe2f5a9ad,0x5bd0fbbc84a4231,0x5bdaf61906619ad,0x645b164508591a4,0x59108]⟩,
  ⟨32,7,[ew109,ew110,ew235,ew111,ew112,ew113],lh 5 [228,196,24,171,32,18,21,14,1,48,60,62,229,230,36,205,20,0,19,183,185,190,22,17,203,195,197,184,16,2,231] [0x10440102104852,0xc030126404832,0x11040100400e63,0x11c400d0800dc3,0xd2300cc301124,0x501b00ca3010c6,0x786c100c03050b4,0x786e178ac278ae2,0x509c250908785c1,0x58922c04c678508,0x608a2c0529588c6,0x608e7684a1684e1,0x4d295ad7c04d08,0x6e8a5664e75295d,0x52d5e664a56e8e7,0x64230541505ad29,0x640b06ba2e6b8a5,0x6d4f56d631618e7,0x61a26]⟩
]
def nodesBlock8 : Array Node := #[
  ⟨32,7,[ew109,ew110,ew111,ew112,ew236,ew113],lh 5 [232,60,32,33,24,23,14,0,50,51,16,2,233,235,19,196,62,183,185,195,197,17,18,184,22,234,231,20,21] [0x882009ef03884,0x380e00942039ee,0x962008020394e,0x8020156501405,0x16250140500a22,0x4817014c500802,0x8d0301405048d2,0x8d430910809144,0x811298116b80d23,0x92a408f0380d63,0x60ec308ea309024,0x60cc66becf6bcd9,0x85290a0280c03a,0x628ea0843b02228,0x628ca6a0e76a0c6,0x62cc60861c02629,0x62ceb6a4c66a4e7,0x6d0346d0e764c33,0x64ce7]⟩,
  ⟨32,7,[ew237,ew109,ew110,ew111,ew112,ew113],lh 5 [236,19,62,12,14,0,16,32,21,60,237,238,23,33,196,24,48,50,183,205,185,18,190,17,2,195,197,22,20,184,175] [0xe700021048e7,0x15c63109ce04821,0x48c616c6315dce,0x4a5380491814c5c,0x5e8a55e884564a5,0x1dc70046356484,0x1cc7005c101c63,0x1c07004c100401,0x320c0310800601,0x501d030ac00501,0x9b62d0300c050b4,0x9b4c648e3148cc3,0x13d0f13e101350d,0x58c8353eaf1360d,0x1090853c8458eb5,0x518a64893e49926,0x518845c4a55c484,0x5d8965d8a552084,0x520a5]⟩,
  ⟨32,7,[ew53,ew109,ew110,ew111,ew112,ew113],lh 5 [239,60,23,24,2,0,20,19,58,14,1,33,240,241,32,51,18,183,185,62,17,195,197,203,22,16,190,205,184,175] [0x1ce00042045ce,0xd1080846304442,0x44c60e1080d063,0xec3a0448408439,0x6d9296d8a565529,0x396e00908654a5,0x9420096b03908,0x8c201d4701cc6,0x8820080201c87,0x481c01ca701c07,0xaccb01c0704932,0xad4a08cc308d4a,0x98def98c83badeb,0x6a12960e03bac84,0xa82a60d236a210,0x618a60cc3d08484,0x61a066a8a56aa10,0x6bd2f6bca561124,0x610a5]⟩,
  ⟨32,6,[ew109,ew229,ew230,ew112,ew113],lh 5 [242,2,22,16,17,23,0,21,158,1,58,185,20,33,50,14,190,184,162] [0x20630200802c63,0x218c015ce02c0b,0x202101585021ce,0x20e701425014e5,0x2ccb02c11014c5,0x2105200d8301405,0x10ce310c21124e7,0x125e910cc612429,0x230e710de3124c9,0x23421228ea22821,0x2288a228ca2348d,0x140c6105e1234cd,0x104c6141f0]⟩,
  ⟨32,6,[ew109,ew232,ew111,ew233,ew113],lh 5 [243,20,12,19,165,0,33,48,17,2,16,185,14,244,245,22,36,115,126] [0x11240101102d29,0xc210114402c0b,0xc430102400d43,0xcc301042010c4,0x2ca502c0b00ca3,0x7a54a79c2100c03,0x1c4779d477a421,0x71ca76a58c421f2,0x404c16a4a571d87,0x40442428c642842,0x740b07418c684a1,0x708a26990668581,0x698a670902]⟩,
  ⟨32,6,[ew109,ew110,ew235,ew236,ew113],lh 5 [246,24,185,18,171,33,48,2,51,60,247,248,21,205,14,20,196,175] [0x822008a201024,0x1004008e7010a5,0x8c600802010e7,0x982010c60118c,0x8630080201063,0x684e16950501004,0x49585694e568508,0x494c548581484c1,0x5c0705c1ce50461,0x4a5b1020c8505c1,0x5a1c85a06851dc7,0x5986353d2f51c63,0x53c6f59926]⟩,
  ⟨33,7,[ew114,ew115,ew116,ew117,ew118],lh 6 [259,21,35,22,249,51,7,18,250,20,23,255,38,50,10,19,9,262,41,251,49,252,253,254,256,257,258,260,261,263,264,265,266,5,267] [0x20f0cf0944c4204,0x58a34a5440820cf,0x39960b34b5c438e,0xa04100414568a,0x1c400404400a145,0xcb1cb0cb1866c4,0x251742391704186,0xc225f7884920c8,0x402002042000410,0xc2182000041002,0x1c70c81880c81c8,0xc14c0090490c2,0x18600914900c041,0xcd1860cd1e1809,0x1c500100188c1cc,0x11c1005005005]⟩,
  ⟨33,6,[ew38,ew114,ew115,ew116,ew117,ew118],lh 5 [18,250,21,268,9,273,22,51,41,7,10,255,271,38,249,20,259,50,36,19,35,269,270,272,49,274,8,5] [0x30e90084c69c1ce,0xb3de352ab290d4a,0x608502120213084,0x30ee3000c330c00,0x2c62b1ac6108c78,0x59ce5415718ad08,0x701cb12ca729445,0xca10e4a4a001525,0x610867bc2a085e1,0x3252c1082420442,0x510860002908401,0x6a5aa39da46b4fa,0x1304d001094201b,0x2000ec39c00]⟩,
  ⟨33,6,[ew15,ew114,ew115,ew116,ew117,ew118],lh 5 [249,7,9,18,51,35,273,50,10,22,38,268,279,21,41,259,20,250,19,275,276,277,278,280,281,265,8] [0x5ae2f2c56b93c00,0xb1cf5422873cdce,0x6108f109e423042,0x48c69085231a421,0x31ce94dd6528160,0x10064200700100,0xc00108c431846,0x2a100080c331826,0x6084586708424e7,0x284ac6b4a2115a5,0x8084518d210a463,0x50550211425289a,0x6b1aa1a9c173863,0xd0848c21021]⟩,
  ⟨33,6,[ew238,ew114,ew115,ew116,ew117,ew118],lh 5 [23,277,50,35,250,18,286,21,7,9,51,273,259,22,249,282,268,283,284,20,285,287,288,289,290,291,292,293,294,295] [0x685b0211e173000,0xa066c10a4188484,0x306ac39d86618e7,0xb86c1295a1684a5,0x58d60200031ac8b,0x329400802210438,0x140639c0a000e0,0x1e460401652ad0b,0x3252310c9a21042,0x1a0665286918d43,0x3252329488210a4,0xda1065284910942,0x398fd29448e08a2,0x7421264a509]⟩,
  ⟨33,6,[ew114,ew115,ew116,ew239,ew117,ew118],lh 5 [250,277,7,9,19,21,41,35,296,18,299,38,10,259,51,249,22,255,20,290,23,285,297,298,268,50,282,300,301,302] [0x79de4010873bc0f,0x234816308120433,0x439082948e206b4,0x8a63110909410a4,0x3180900ec62048,0x400c0037b1e52,0xc602814318610,0x800480e2128a5,0x30cc1d64cd31d27,0x58966739635adcb,0x5076b4a4c231926,0xe878a18daa6b463,0x2a8a110a0180442,0x51146a18c43]⟩,
  ⟨33,6,[ew240,ew114,ew115,ew116,ew117,ew118],lh 5 [35,21,7,250,50,18,51,304,255,296,277,9,19,259,22,249,10,23,268,303,305,306,257,307,308,309,310,311,312] [0x7001218d4a8b508,0x52a0d2426003863,0x3842d319a109cc6,0xa884e295c2150a5,0x4000c1b18002063,0x798d8bd98a62884,0x4952f0bd264a421,0x64091250542042,0x3ad602007a18c84,0x8070840b00020,0x384202806218ca3,0xd884731881210c4,0x9c3c29482210a4,0x1109675ac42]⟩,
  ⟨33,6,[ew89,ew114,ew115,ew116,ew117,ew118],lh 5 [35,51,23,9,18,250,7,314,21,38,277,10,273,20,259,41,22,249,275,268,313,50,315,305,316,257,307,308] [0x814b20014a8b842,0x52aae5ae852cc00,0x3842e18dc109c63,0xc109731a04258c6,0x6000228840030ac,0x3843bd654b58942,0x110474204108902,0x2c0230984230cc,0x38c606b4ab295a5,0x18070840318021,0x68c60210a629484,0x4992d0b5234a421,0x41d09225e67bc84,0x83206718cc6]⟩,
  ⟨33,6,[ew241,ew114,ew115,ew116,ew117,ew118],lh 5 [9,10,35,18,50,305,21,19,51,250,23,22,249,41,320,259,7,255,268,317,277,318,319,321,322] [0x59572109658bd8c,0xab5b40856599442,0x7800e31acd69421,0x5960f1c1c003cc6,0x6098749ce21312c,0x53547210ed3a88a,0x398ea4214651d07,0x1044a2a8a3194b7,0x70002211210a484,0x12c4e4212002508,0x800218d2b4a463,0xe0214048001108,0x338c11848b21063,0x61980e00060]⟩,
  ⟨33,6,[ew97,ew114,ew115,ew116,ew117,ew118],lh 5 [10,50,51,7,250,35,9,21,19,22,23,249,305,325,259,255,268,315,323,277,324,18,326,327] [0x490892958c7b96b,0x9043100124240a5,0x7084d39e810cc00,0x632ae18da2138e7,0x59568221052ac8b,0x50008085004282a,0x41d0a1094752048,0x280094d9831a98a,0x698c50848001021,0x28c6d1088631042,0x18c54948319124,0xc601082630442,0x3b4e0b802318521,0x719ccd31866]⟩,
  ⟨33,6,[ew114,ew20,ew115,ew116,ew117,ew118],lh 5 [35,18,51,9,249,7,23,10,22,19,21,330,331,38,259,255,41,268,328,329,275,274,291,309,321,250,50,262,5] [0x250899a53249224,0x2000942520012a4,0x31cc4b908739ac6,0x20c66118c331042,0x314af0bde5c1826,0x5af4e39d6bcb800,0x6084e18dc213063,0x40428295010a0a5,0x60c60581673a11b,0x140c5280300140,0x38c60081052a021,0x695a711da36b442,0x5314d086058403c,0xa0a84c10821]⟩
]
def nodesBlock9 : Array Node := #[
  ⟨33,6,[ew242,ew114,ew115,ew116,ew117,ew118],lh 5 [23,7,250,51,21,249,38,330,22,18,9,255,334,259,10,19,41,35,268,332,277,333,50,335,49,281,292,310,321,265,8] [0xa8014296600496b,0x41ecd739078b451,0x6108d18da423063,0x41ee70850741c21,0x2e4af13de8c2c42,0x1805d94a628340,0x290a01800401465,0x42b4ad61e0120,0x629473f44711cc6,0x4042c2104a50882,0x729484a44110922,0x304ce18cca3187e,0x2308649a0184129,0x40906c18c23]⟩,
  ⟨33,6,[ew114,ew115,ew29,ew116,ew117,ew118],lh 5 [9,35,51,250,23,7,249,22,20,255,10,338,19,38,259,339,21,277,336,337,315,293,311,322,330,50,18,5] [0x304cc1b18109863,0x350c99a5324b22c,0x22886b18ca512a4,0x300041108021842,0x214893a525492e4,0xe02338c67184e1,0xa103528681854a,0x588410002212c00,0x9c2329467184a1,0x7084b000e7cb908,0x7bf4e2956213800,0x4090d035a212008,0x82e0d7b5e529cfb,0x102c00b000a5]⟩,
  ⟨33,6,[ew243,ew114,ew115,ew116,ew117,ew118],lh 5 [250,23,249,35,51,38,18,21,339,9,22,343,273,259,19,255,20,41,10,305,340,277,341,330,342,7,295,312,321,327,344] [0xb319510a8c64c21,0x5230818d4855c63,0x6a52b211488b4b1,0x5232d319694b484,0x10c4e001c370800,0x9422d884510741,0x124412042908882,0xf42f33deae04c1,0x1c0602801080ca5,0x59ce04800702d29,0x198605000600d43,0x91085394a42c8e7,0x3ace84790631505,0x731c8b210c4]⟩,
  ⟨33,5,[ew114,ew115,ew116,ew244,ew117,ew118],lh 5 [19,250,273,51,9,21,18,20,7,290,262,347,249,36,277,35,345,10,346] [0x100026812960001,0x3854a0084000840,0x80428290247842e,0x1916b91c6519627,0xc3314c832064]⟩,
  ⟨33,5,[ew245,ew114,ew115,ew116,ew117,ew118],lh 4 [250,35,23,249,9,51,7,18,21,10,273] [0x765858990101323a,0x6232232332101076,0x5410015404100127,0x8448767654]⟩,
  ⟨33,5,[ew246,ew114,ew115,ew116,ew117],lh 4 [41,255,23,250,51,50,18,35,21,9,7,10,348] [0x3a77611a22a1a622,0xbb606abba3367763,0xc99688699c88a006,0x252171233277131,0x4428814120015510,0x7553003557001812,0x4080c44399344c99,0x4458554]⟩,
  ⟨33,5,[ew38,ew114,ew20,ew116,ew117,ew118],lh 4 [35,249,250,7,21,51,273,18,19,277,262,41,349,22,49,50] [0xd0c0050ba0029081,0x311661611612e203,0x545472235424f237,0x45347373]⟩,
  ⟨33,5,[ew247,ew114,ew115,ew116,ew117,ew118],lh 5 [51,7,18,21,23,9,249,35,250,280,326,10,19,41,50,321,262,265] [0x1040300dcd42186,0x200863112939841,0x162b81d4a79064,0x105650144111c05,0x6508c41]⟩,
  ⟨33,5,[ew114,ew115,ew116,ew248,ew117,ew118],lh 4 [249,50,250,21,273,7,35,18,51,280,23,112,9,10,350] [0x44040aab0019960,0x322c622612160440,0x837115e113d17225,0x3853757583]⟩,
  ⟨33,5,[ew114,ew249,ew115,ew116,ew117,ew118],lh 5 [249,50,21,9,7,35,273,18,23,51,250,353,268,10,259,351,22,352] [0x300010210030006,0x6154a01c8002440,0x9624811e2709a1,0x8ca43944328d6b,0x43188e109123]⟩,
  ⟨33,5,[ew242,ew15,ew114,ew116,ew117,ew118],lh 5 [7,250,10,35,273,9,280,21,356,268,354,50,22,49,353,355,345,8,5] [0x195625106418523,0x704226846060ce5,0x118448002078425,0x116220100631086,0x4200710240]⟩,
  ⟨33,5,[ew240,ew114,ew115,ew116,ew117,ew118],lh 4 [250,249,50,51,7,9,18,35,21,23,41,257] [0x46465353a2707091,0x716411351b121070,0x4322560043005200,0x8348622]⟩,
  ⟨33,5,[ew250,ew114,ew116,ew117,ew118],lh 4 [35,250,9,7,249,50,18,51,23,10,21,41,357,255,257] [0x10b0181040088141,0x220a0c220501b115,0x66131161030caa0,0x24748be45e4b4855,0x6dd3346642287782,0x979522577922434d,0x3aca969533566939,0xa337c773]⟩,
  ⟨33,5,[ew250,ew114,ew115,ew116,ew117,ew118],lh 4 [10,50,23,255,7,51,9,18,35,19,20,21] [0x74565610a0882393,0x4232232101322374,0x1074745656101023,0x454b011001]⟩,
  ⟨33,5,[ew89,ew114,ew115,ew116,ew117,ew118],lh 4 [250,23,51,7,20,9,18,35,50,21,19,257,10] [0x63632525880707a1,0xc16315112b417010,0x4452460032005400,0x9239436]⟩,
  ⟨33,5,[ew251,ew114,ew115,ew116,ew118],lh 5 [18,50,35,7,21,10,23,51,249,9,250,19,255,358,359,20,360,361,356,49,321] [0x398c45908621d6b,0x4884471082125a9,0x4852729ce10a5e9,0x2024789ce001204,0x40846528c232153,0x314a80850541826,0x40c6c03183a2008,0x1042a29541088a5,0x1000a18d4000863,0x2800118c2001463]⟩
]
def nodesBlock10 : Array Node := #[
  ⟨33,5,[ew252,ew114,ew115,ew116,ew117],lh 4 [18,273,7,35,10,9,19,51,250,50,21,362,20,38,249,255] [0x2320112e221f0e0,0x4009024228203008,0xb550aa050baa2920,0x6191131686633181,0x7715567614169664,0x3cc8488c83446561,0x7454b77353373b55,0x474d5dd7]⟩,
  ⟨33,5,[ew252,ew114,ew115,ew116,ew117,ew118],lh 4 [50,35,38,51,250,19,273,21,7,9,10,41] [0x373702b241416565,0x6553932020141488,0xa14413119020256,0x73372002a0]⟩,
  ⟨33,5,[ew238,ew114,ew20,ew115,ew117,ew118],lh 4 [18,35,21,51,23,41,9,50,7,38,290,273,257,268,262,353] [0x50529251e557d7c4,0xb02343141b47aa90,0x363608083232f140,0x6621801]⟩,
  ⟨33,5,[ew242,ew238,ew114,ew115,ew117,ew118],lh 5 [50,23,9,10,7,250,21,273,51,8,20,290,35,18,363,257,22,5,364] [0x300026140b08140,0x4a46580de37000d,0x3a0e10946489066,0x2910240827384c8,0x8211a44]⟩,
  ⟨33,5,[ew238,ew114,ew115,ew29,ew117,ew118],lh 5 [35,10,9,50,250,51,23,7,366,353,21,273,257,262,22,8,5,365,118,294] [0x78423704206818b,0x88c040102780422,0x1810839a45314c3,0x18804200a200929,0x5084a98ca2]⟩,
  ⟨33,5,[ew243,ew238,ew114,ew115,ew117,ew118],lh 5 [9,273,51,23,10,50,250,7,265,294,364,21,41,353,367,257,262,8,22,18,35] [0x9c66982309585,0x88108811e439c02,0x8231849391080,0x4d0401006108c02,0x1604ad4a]⟩,
  ⟨33,5,[ew114,ew253,ew116,ew117,ew118],lh 5 [250,273,7,9,35,20,255,21,18,38,51,368,41,19,277,296,10,23,290] [0x3108d045a421806,0x9426718c5285d2,0x31ce15042709946,0x78841404220bd08,0x214a08000529204,0x59ce018c0702c63,0x220801000801042,0x2a8a91a52a51463,0x4a12c1318842449,0x3884358c6219d67]⟩,
  ⟨33,5,[ew114,ew253,ew115,ew116,ew117,ew118],lh 4 [19,41,273,9,7,21,20,18,38,250] [0x230100220022002,0x7453536161990240,0x8174745353616174,0x4335811818]⟩,
  ⟨33,5,[ew114,ew115,ew116,ew254,ew118],lh 5 [250,18,35,249,21,51,7,41,9,296,10,19,277,255,20,38,290,321,262,369,349,370,371,372,356] [0x1884b02d6258c00,0x61ce360c6783190,0x1a0692a52840ca3,0x498cd0b5a68a429,0x139c05000e908e2,0xa90804500404d08,0x1044030001088c2,0x514af211e57a88a,0x5042731ce10a8c6,0x20708b94a1292c4]⟩,
  ⟨33,5,[ew114,ew115,ew116,ew255,ew117],lh 5 [9,7,35,23,51,18,250,10,19,255,41,373,21,249,20,38,277,296,321] [0x689a832102134d1,0x19c688210740e03,0x184292a52190ca3,0x48123210601a489,0x139c6398ce308e2,0x114a6084c528821,0x590820004422c00,0x394ea0a94529c27,0x5114f03de42280a,0x580016302002d8c]⟩,
  ⟨33,5,[ew114,ew115,ew116,ew255,ew117,ew118],lh 4 [38,21,255,23,250,9,41,35,51,20,7] [0x1818322302032332,0x1445744790903223,0x660610106607447,0x1551aa5151]⟩,
  ⟨33,5,[ew114,ew256,ew115,ew116,ew117,ew118],lh 4 [249,9,50,21,51,7,18,10,19,38,23,374,326,250,321,35] [0xbb309002088008aa,0x6543432929ddcce0,0x4165654141272f65,0x3113756771]⟩,
  ⟨33,5,[ew114,ew115,ew116,ew257,ew117,ew118],lh 4 [50,10,21,255,250,249,35,51,9,19,18,7] [0x3723533510105995,0x244864460101b335,0x1001100210016446,0x2882aa7272]⟩,
  ⟨33,5,[ew240,ew89,ew114,ew115,ew117,ew118],lh 5 [257,250,35,21,7,50,18,9,10,8,5,376,377,277,23,344,19,350,294,375] [0x4a46810441701a5,0x28c2208a00529e8,0x980011024429225,0x3106719d8c2016b,0xc730cc4]⟩,
  ⟨33,5,[ew240,ew89,ew115,ew116,ew117,ew118],lh 5 [51,35,18,249,273,9,21,7,354,321,257,277,10,23,280,50,378] [0x300806110809163,0xde3185c169082,0x142a8052910c06,0x11d450144710405,0xc539847]⟩,
  ⟨33,5,[ew240,ew114,ew20,ew115,ew117,ew118],lh 4 [19,255,10,21,51,7,18,35,9,262,23,20,296,353] [0x265224329972b2a1,0x11004c070011001,0x65487865654343d7,0x388365]⟩
]
def nodesBlock11 : Array Node := #[
  ⟨33,5,[ew240,ew242,ew114,ew115,ew117,ew118],lh 5 [50,18,21,250,7,9,257,19,10,8,377,268,20,23,265,112,35,379,49,376,380] [0x1210370da760160,0x80c077808120529,0x30e438800110005,0x1144552a8634c46,0x942209024]⟩,
  ⟨33,5,[ew240,ew114,ew115,ew29,ew117,ew118],lh 4 [250,35,51,257,9,50,21,255,5,23,41,10,7,375,294] [0x88cb6262a5101093,0x377332d337751010,0x2424100124245051,0x6446e5]⟩,
  ⟨33,5,[ew240,ew243,ew114,ew115,ew117,ew118],lh 5 [9,21,50,10,257,294,35,262,8,7,383,364,277,23,265,344,18,381,382,376,321] [0x8ce770da418982,0x118448887078d08,0x528c44a40100646,0x80202168504c04,0x280a15aca6]⟩,
  ⟨33,5,[ew258,ew114,ew115,ew116,ew117,ew118],lh 4 [9,7,10,249,20,23,21,250,326,35,22,384,321,345,8,5] [0xa160604242975353,0xc3050343453757b1,0xe2d1716060424288,0x101621f120]⟩,
  ⟨33,5,[ew259,ew114,ew115,ew116,ew117,ew118],lh 4 [250,35,9,249,51,23,7,50,326,344,21,255,18,5] [0x10c64242770101b3,0x188653553533510,0xd642421001420210,0xa22a99]⟩,
  ⟨33,5,[ew114,ew260,ew115,ew116,ew117,ew118],lh 4 [273,21,41,9,10,23,249,35,257,18,345,22,385,7,262,8] [0x6006884005505005,0x31312424c7b76006,0xf1aa97131372e2d9,0x1331422421]⟩,
  ⟨33,5,[ew261,ew114,ew116,ew117,ew118],lh 4 [250,35,21,7,23,19,51,50,18,255,41,386,9,10,20] [0x1a1055191151099,0xc0020bcc1e10a00e,0x181030080131b220,0x45654a45775a5474,0x8893948452546642,0xa66727766a224349,0x32b2d8d737788d33,0x2336b663]⟩,
  ⟨33,5,[ew114,ew115,ew116,ew262,ew117,ew118],lh 4 [9,23,41,18,250,35,51,19,21,5,7,255,10,277] [0x7616177127215114,0x60605445524213b3,0x832992060c23435,0x8008aa3d08]⟩,
  ⟨33,5,[ew263,ew114,ew115,ew116,ew117,ew118],lh 4 [250,35,21,41,249,51,7,18,23,9,19,10] [0x765252b30101a8a8,0x6445243438101076,0x5210012009100147,0x2992733632]⟩,
  ⟨33,5,[ew241,ew114,ew115,ew29,ew116,ew117],lh 5 [9,7,10,51,23,18,35,250,249,345,255,22,277,5,321,19,262,50] [0x684256042759d44,0x715042200108c22,0x2980300c4f11085,0x88866300c281929,0x10060180a0]⟩,
  ⟨33,5,[ew114,ew115,ew116,ew264,ew117,ew118],lh 4 [250,50,23,249,7,35,21,18,51,255,9,345,10,350] [0x3223233221313050,0x600a500510152942,0x867114d116c1b005,0x4846747486]⟩,
  ⟨33,5,[ew265,ew114,ew115,ew116,ew117,ew118],lh 5 [9,35,23,7,250,51,249,50,10,326,21,22,387,259,388,18,277,294] [0x6810861164308c2,0x308220920378dc0,0x385291880501447,0x28023204a108024,0x14002a2338ca0]⟩,
  ⟨33,5,[ew243,ew97,ew114,ew115,ew116,ew117],lh 4 [7,18,9,35,51,249,23,10,250,277,366,22,50,321,294,262] [0x24c008b0a0060190,0x4112e1178313d120,0x37f3542575565635,0x42424332]⟩,
  ⟨33,5,[ew114,ew115,ew266,ew116,ew117,ew118],lh 5 [7,21,19,10,9,35,49,290,389,391,18,50,249,390,277,250,262,265,268,392,259,393,305,8,5,344] [0x886239d82288c6,0x80de52b92968908,0x1c9405142409223,0xb9016054340cd6b,0x400720c0064]⟩,
  ⟨33,5,[ew267,ew114,ew115,ew116,ew117,ew118],lh 4 [9,10,18,50,21,250,35,51,19,7,20,249] [0x92070713aa6565b8,0x9247471383656592,0x7025264040313182,0x4004132110]⟩,
  ⟨33,5,[ew114,ew268,ew115,ew116,ew117,ew118],lh 4 [250,7,23,9,20,21,51,18,35,112,50,41,255,268] [0x12522699428220c2,0x1756564daa808017,0x6370015303400b17,0x133541b143]⟩
]
def nodesBlock12 : Array Node := #[
  ⟨33,5,[ew269,ew114,ew115,ew116,ew117,ew118],lh 5 [50,9,51,250,10,21,7,23,249,41,18,394,35,268,20,354,345] [0x95c0481a360d08,0x481e338cca32825,0x116b31c22088e0,0x112031984110404,0xa21148001081]⟩,
  ⟨33,5,[ew114,ew115,ew116,ew270,ew117],lh 5 [394,35,21,250,7,51,10,18,255,20,249,9,41,395,38,354,363,379,321,262,8] [0x505e0180010286a,0x18ca8a94630200,0x10883a104900e0,0x4090028002120a8,0xa52330c69984c6,0x9c2320c6718481,0x688415ac220b56b,0x49d2c231873a489,0x614ae5b9c5a316c,0x694a4108852b442]⟩,
  ⟨33,5,[ew114,ew115,ew116,ew271,ew117,ew118],lh 5 [35,21,255,250,7,10,365,396,321,9,5,344,18,20,19,397,268,305,50,8,398,259,277] [0x89c2688c610c02,0x3c0318082420e7,0x2c4031802002600,0xd16b528a198645,0x892058c25835]⟩,
  ⟨33,5,[ew272,ew114,ew115,ew116,ew117,ew118],lh 4 [50,10,51,250,35,9,255,21,18,7,41,249] [0x98727210aa4343b6,0x6862721060434398,0x2543342525010196,0x8557100115]⟩,
  ⟨33,5,[ew114,ew273,ew115,ew116,ew117,ew118],lh 4 [35,51,250,273,9,21,18,7,399,38,381,50,5,344,23,277] [0x365131aa938803e3,0x7651519fbb020273,0x1402201424022076,0x5445ddcc14]⟩,
  ⟨33,5,[ew274,ew114,ew115,ew116,ew117,ew118],lh 4 [10,9,50,250,18,35,21,51,249,7,273,277,399,366,344] [0x9961610202535388,0xa417170202c353b4,0x20534571312020da,0x61464e4001]⟩,
  ⟨33,5,[ew114,ew275,ew116,ew117,ew118],lh 5 [19,273,250,35,18,51,9,38,21,7,20,10,400,41,367,382,366] [0x8c601000318441,0xac207800b005c1,0x200129428400a0,0x24012402908080,0x1a9425884a10d63,0x614a2318452b0c6,0x190624884410d23,0x5154731ce52a8c6,0x390ed4b5a421d27,0x41086618c422188]⟩,
  ⟨33,4,[ew276,ew114,ew115,ew116,ew118],lh 4 [249,9,35,50,21,7,18,51,280,10] [0x4114173114217040,0x2932065090038820,0x63352562]⟩,
  ⟨33,4,[ew277,ew114,ew115,ew116,ew117],lh 4 [9,249,35,50,7,18,21,280,10,51] [0x606353442525141,0x2832090181137721,0x90306020]⟩,
  ⟨33,4,[ew278,ew251,ew114,ew116,ew118],lh 4 [9,250,20,50,23,7,19,257,326,21,35,401] [0x6a1153112164190,0x547723500b023040,0x233288]⟩,
  ⟨33,4,[ew279,ew251,ew114,ew116,ew118],lh 4 [35,250,21,50,20,23,403,257,326,9,19,402,321] [0x2a01100110100190,0xc5774366b2243252,0x433488]⟩,
  ⟨33,4,[ew280,ew251,ew114,ew115,ew116],lh 4 [7,21,50,10,18,321,51,280,366,118,401,402,49] [0x1504400440800566,0x3277c51321b11a91,0x232332]⟩,
  ⟨33,4,[ew281,ew251,ew114,ew115,ew116],lh 4 [18,23,7,356,50,10,51,21,366,321,49,280] [0x1620022002028077,0x51b11a3543366319,0x454514]⟩,
  ⟨33,4,[ew238,ew114,ew115,ew270,ew117],lh 4 [21,7,250,10,50,20,35,51,9,257,5,8] [0x6230b334a3355295,0x841210707141462,0x811002]⟩,
  ⟨33,4,[ew238,ew114,ew275,ew117,ew118],lh 4 [23,41,7,273,51,9,21,18,257,262,250,8,10] [0x3c11216b11a9180,0x7245450330640430,0x255672]⟩,
  ⟨33,4,[ew114,ew282,ew116,ew254,ew118],lh 4 [10,9,250,255,35,7,18,290,296,321,349,8,5,404] [0x5339181303073242,0xc001b14225a14020,0x616d05]⟩
]
def nodesBlock13 : Array Node := #[
  ⟨33,4,[ew283,ew114,ew116,ew254,ew118],lh 4 [35,250,18,10,249,21,290,257,405,38,344,403,9,321] [0x660210c003101001,0x23399542d4885477,0xbb25aa]⟩,
  ⟨33,4,[ew114,ew115,ew116,ew284,ew254],lh 4 [41,250,18,7,21,290,257,118,51,49,321,249,265,404,8] [0x774b32326655a191,0x320414d2123c010,0x8804e0]⟩,
  ⟨33,4,[ew285,ew114,ew115,ew116,ew254],lh 4 [296,35,249,18,7,356,280,38,21,290,257,262,265,403,10] [0x1083433413140202,0x151cb12002a00966,0xe775d5]⟩,
  ⟨33,4,[ew240,ew114,ew115,ew270,ew117],lh 4 [35,112,50,250,21,7,10,376,9,23,265,8] [0x36b465252030a91,0x803307741125101,0x822440]⟩,
  ⟨33,4,[ew240,ew114,ew275,ew117,ew118],lh 4 [21,257,35,9,7,10,344,5,383,376,381,294,23,262,8] [0x2177660e052d25c1,0xb203031aa1990188,0x4340b4]⟩,
  ⟨33,4,[ew286,ew114,ew115,ew116,ew117],lh 4 [20,21,35,250,249,9,7,23,321,326,5,356,8] [0xb16160a032329484,0x302171404072323,0x5c51515]⟩,
  ⟨33,4,[ew287,ew114,ew116,ew117,ew118],lh 4 [35,18,249,10,273,21,7,356,23,262,9,257,8] [0x1610500a03908002,0x35c321412442b224,0x77151613]⟩,
  ⟨33,4,[ew288,ew114,ew116,ew117,ew118],lh 4 [9,51,7,10,23,50,250,326,249,18,21] [0x9262101053534846,0x1010772401013534,0x200a3252]⟩,
  ⟨33,4,[ew289,ew114,ew115,ew116,ew118],lh 4 [9,51,7,10,23,50,250,326,21,249,35] [0x2008011001101001,0x5353772435349446,0x3252a262]⟩,
  ⟨33,4,[ew114,ew115,ew290,ew116,ew118],lh 4 [249,7,35,18,9,280,290,50,21,389,257,250,262,265,8] [0x310a06609405520,0x77e431312dc2b224,0x31318418]⟩,
  ⟨33,4,[ew114,ew115,ew291,ew116,ew117],lh 4 [9,21,249,10,7,18,280,290,257,118,262,35,265,5,344,8] [0x99128877254266b2,0xe3d31010c3aa5454,0x30f00101]⟩,
  ⟨33,4,[ew114,ew292,ew116,ew117,ew118],lh 5 [9,255,250,35,21,365,396,321,10,344,19,20,249,349,7,18,8,5] [0x31881584a50a861,0x6804018843604e7,0x4a628402007884e,0x20004]⟩,
  ⟨33,4,[ew114,ew115,ew116,ew293,ew118],lh 4 [250,35,9,21,365,257,249,118,326,344,321,8,50,10,5] [0x88a6773655441010,0xc2b2100132021001,0x322399ed]⟩,
  ⟨33,3,[ew278,ew280,ew114,ew116],lh 3 [35,250,9,50,20,257,23,406] [0x351ae96048201088,0x16c]⟩,
  ⟨33,3,[ew114,ew282,ew116,ew284],lh 3 [349,250,5,9,290,255,406,18] [0x20c808ad9d564041,0x1df]⟩,
  ⟨35,7,[ew124,ew112,ew125,ew126,ew127],lh 5 [259,24,0,15,16,407,408,38,39,296,7,409,62,23,35,18,273,410,58,50] [0x63463635cd61465,0x15050342d615c5,0x614850350801421,0x314e532489324e7,0x5c0505c14a62449,0xc21039085a549,0x338e70382100d03,0x3388430ce330c84,0x5c5515c44258d43,0x484020e758c42,0x54102084004e1,0x4420495204842,0x34c5334def31042,0x311ef]⟩
]
def nodesBlock14 : Array Node := #[
  ⟨36,7,[ew128,ew129,ew130,ew131,ew132],lh 6 [42,43,17,2,7,14,35,41,9,411,412,416,16,418,21,38,417,421,1,46,413,27,414,415,419,420,422,0,423,424,20,10,425,426,427,356] [0x186089000081181,0x2891c7081000089,0x3155011c7081301,0x2c90d7581208289,0x1100900c32c9209,0x601101081145350,0x30c2861c7350159,0x44630c4401c7080,0x2082c60c3680208,0x3461040800c32c6,0x15d7001000806c0,0x2cf0cf29e38e346,0x10f81f0c328f38e,0x28710485215228f,0x11334e15334f145,0x2ce1238881452c8]⟩,
  ⟨36,6,[ew78,ew129,ew128,ew130,ew131,ew132],lh 6 [15,7,14,9,2,35,21,412,10,417,17,0,20,42,179,43,41,410,48,30,38,416,418,411,16,428,429,430,431,432,27,433,434] [0x44a14529144a145,0x4101c75c73cf291,0x5524990c31ca607,0x2d60416924950c3,0x24958b2dc0826cb,0x1534c0240013745,0x30020800c005205,0xc300600d0cd14c,0x34b340040346180,0x24730c00b00d041,0x11f2461871de24a,0x38138910438638e,0x18e0823c13cf0a0,0x104506514104306,0x401410082201208,0xc3041102088088,0x40440c2]⟩,
  ⟨36,6,[ew129,ew36,ew128,ew130,ew131,ew132],lh 5 [15,16,14,41,35,9,7,417,21,416,0,17,30,42,10,43,421,412,2,418,438,5,411,435,428,436,437,415,439] [0x22c805800b01164,0x231807800c011e4,0x204801800101064,0x6a10028008034a5,0x84d319a2680c0,0xb843118d29b418c,0x4ae5044a210e1ce,0x9a95a10b2a54c42,0xa042719ce13d063,0x398e759d252a53b,0x194a751de633d4a,0x71aaee0c2508521,0x4084e1086618c55,0x8320a2294c6]⟩,
  ⟨36,6,[ew85,ew129,ew128,ew130,ew131,ew132],lh 5 [35,16,42,7,180,9,2,17,43,418,10,21,38,41,15,421,412,416,417,440,431,437,441,14,420,5,442,443] [0x3b9c7000ee71c00,0x984306b52993d08,0x898d55ae010d14a,0x49eef18ec63456b,0x1c022084710084,0x4026304110180,0x1184029406008a2,0x240218c4710060,0x20428621010918c,0x4190429086220a8,0x514a94e08722463,0x50d4a32825084c1,0x5a56a4a9a36b759,0xb1acbb29463]⟩,
  ⟨36,6,[ew82,ew129,ew128,ew130,ew131,ew132],lh 5 [42,9,411,7,417,41,16,14,0,416,20,17,43,421,10,30,448,412,418,445,35,21,444,432,446,447,29,449] [0x5884b21129a3400,0x698d12956212c84,0x4aead08626334a5,0x9211339ec8448e7,0x5bde02000fbad8c,0xca9402800a060a5,0x80c60981210a53a,0x129504200318100,0x204823188a510c4,0x10c445904108922,0x504224098363108,0x70c6eda8c109926,0x81cee3b8a3294e7,0x918c2708463]⟩,
  ⟨36,6,[ew86,ew129,ew128,ew130,ew131,ew132],lh 5 [21,411,20,7,410,418,17,9,42,30,16,41,2,421,417,179,38,43,412,416,10,35,445,450,14,424,434,5,451,452] [0x30426738a5ab508,0x688525acc1099ce,0x9801639e421356b,0x29b0d18ee004ce7,0x325247bc89219ef,0x208488210211210,0x4000439080220e8,0x88452e48621463,0x480015292212549,0x8c296302008581,0x10001286238c4da,0x50d42631405298c,0x14142d1635af9b,0x18cfd39c63]⟩,
  ⟨36,6,[ew80,ew129,ew128,ew130,ew131,ew132],lh 5 [35,14,7,411,2,1,43,42,10,412,416,15,421,17,417,418,428,453,38,21,454,455,449,439,456,457] [0x6000d5ada00316b,0x88c6d739a31c1ce,0x4a66c2112a930a5,0x788550868213c21,0xc07318e3180c6,0x1407420e538100,0x390805000401ec7,0x42711ce138040,0x194a6420c530d08,0x3108350c6421ae6,0x18426108c108c43,0x408494e14421525,0x20428084a211425,0x410b210a842]⟩,
  ⟨36,6,[ew129,ew128,ew130,ew131,ew132,ew294],lh 5 [411,42,35,21,1,14,2,9,417,41,43,412,418,421,17,459,416,7,451,442,458,431,5,10,460,455] [0x100014202000908,0x110814a42408922,0x8c6238843184e1,0x114a19042508982,0x138416842e089a2,0x10884a50440129,0x418c018c0602063,0x14aa9a94528180,0x380aaa94e50280,0x218cb18de631064,0x2348c2948b22d76,0x394e779cc533177,0x3e4e781c78199e6,0xb5c4ad88e03]⟩,
  ⟨36,6,[ew88,ew129,ew128,ew130,ew131,ew132],lh 6 [411,14,42,417,48,35,16,20,15,416,180,38,190,17,10,418,9,43,41,412,421,410,464,445,461,437,462,463,455,2,7,262,452,443,457,356] [0x14d082345157082,0xc33400190c3605,0x6cb2d338e68000d,0x7541044cb2dc38e,0x28a24979404124f,0x14015528a540005,0x1c82c82077c52c5,0x41020c202402147,0x810883c808c308,0xca1c7201042802,0x3032861831c30c6,0xc4100300004283,0x118514410403c0,0x104189187104001,0x4810465861e21c6,0x10f041181192592,0x9263109]⟩,
  ⟨36,5,[ew295,ew129,ew128,ew130,ew131,ew132],lh 4 [410,0,41,14,35,9,43,42,420,411,16,48,27,415,417,8] [0x41313b5a2960404,0x6210147005027040,0x3125f2881e65d5c2,0x131331]⟩,
  ⟨36,5,[ew129,ew128,ew130,ew296,ew131,ew132],lh 5 [417,410,10,179,38,35,42,14,7,0,344,21,262,41,48,27,411,420,5] [0x94a10b58128020,0x78802498c5305c6,0x1c52300c6000e00,0x52a441108211082,0x10741d0741d6b]⟩,
  ⟨36,5,[ew129,ew128,ew130,ew131,ew132,ew297],lh 5 [417,42,21,10,35,41,9,38,43,179,349,14,465,265,27,433,0,8] [0x5284169c2762429,0x700072042420424,0x210002200009e0,0x194a3194a318a23,0x16b118c2118c2]⟩,
  ⟨36,5,[ew298,ew129,ew128,ew130,ew131,ew132],lh 5 [417,21,10,35,42,9,14,349,420,344,17,421,43,411,41,16,416,466,0,432,465,262,265,27,433,434,8,5,46] [0x896057b9ac58d43,0x92c2a8a8098246,0xc02e00086420ce7,0xd8841d0508c8001,0x26e0529]⟩,
  ⟨36,5,[ew129,ew128,ew130,ew299,ew131,ew132],lh 4 [7,14,21,42,35,30,2,16,467,15,438,411,415,10] [0x2923433443345334,0x52c2b55a75881010,0x6210106272d71010,0x6106101062]⟩,
  ⟨36,5,[ew129,ew128,ew130,ew131,ew132,ew300],lh 4 [417,21,10,42,16,0,35,41,43,9,349,30,415,14] [0x6356aa134242b030,0x85001c040026336,0x2772477521410880,0xd519911951]⟩,
  ⟨36,5,[ew301,ew129,ew128,ew130,ew131,ew132],lh 4 [16,15,41,9,14,43,42,21,417,411,2,0,35,415] [0x15b4a30202951616,0x2164171130102c1,0x402003854853d302,0x743402]⟩
]
def nodesBlock15 : Array Node := #[
  ⟨36,5,[ew80,ew129,ew36,ew128,ew130,ew132],lh 5 [21,35,7,10,15,417,0,2,9,412,415,16,14,411,468,27,5] [0x154001d2040004,0x204243840c10160,0x694223042420425,0x78ca3308c270ce3,0x18a03288c2]⟩,
  ⟨36,5,[ew129,ew128,ew130,ew302,ew131,ew132],lh 4 [15,16,14,7,180,35,43,9,2,469,417,41] [0x8007500510155005,0x6446466416990320,0x8723218117b1a443,0x3232232387]⟩,
  ⟨36,5,[ew129,ew128,ew130,ew303,ew131,ew132],lh 4 [180,10,14,2,15,7,38,42,35,43,16,344,469,21] [0x74374884a1a18040,0x3039900901c12774,0xbb26366116612025,0x52535252d3]⟩,
  ⟨36,5,[ew85,ew129,ew128,ew130,ew131,ew294],lh 4 [35,2,15,7,420,5,14,42,21,412,180,417,9,17,10] [0x631c169665b42020,0x7070070220022493,0x15d3431a14a54507,0x8138e318]⟩,
  ⟨36,5,[ew85,ew88,ew129,ew128,ew130,ew131],lh 4 [41,16,9,420,42,14,7,35,416,15,417,470,471,21,472] [0xb21050a594545686,0xd2101063c6747452,0x1330427210107343,0x11232e3]⟩,
  ⟨36,5,[ew129,ew128,ew130,ew131,ew132,ew304],lh 5 [417,411,41,9,10,42,0,43,16,473,456,46,14,29,416,35,8,448,21] [0x28da34090208020,0x8001794ae31529,0x1ce031cc100420,0x208442084452a04,0x18c90c7130d6b]⟩,
  ⟨36,5,[ew80,ew82,ew129,ew128,ew130,ew132],lh 5 [411,43,9,7,0,10,14,2,21,42,421,29,16,35,20,175,262,265] [0x104011256242142,0x4016a46611982,0x4012188779cee,0x142520c8389605,0x28cc300c80]⟩,
  ⟨36,5,[ew129,ew128,ew130,ew305,ew131,ew132],lh 5 [20,417,42,410,7,179,38,21,14,411,420,344,41,35,424,434,5,9] [0x10da20080c48441,0x4802070c6438c62,0x529e5094a7094a1,0x5ae06018c7018c0,0x882208822227]⟩,
  ⟨36,5,[ew86,ew129,ew128,ew130,ew131,ew294],lh 4 [411,43,2,9,5,14,7,424,21,35,346,421,474,475,10] [0x565325a554010197,0x762323c4740101b6,0x23061010030414d7,0x8228e623]⟩,
  ⟨36,5,[ew86,ew88,ew129,ew128,ew130,ew131],lh 4 [411,38,7,424,417,20,356,14,41,475,416,35,476,21,29] [0xc758580404b372a2,0xd215120402239976,0x14136e351310304,0x51164006]⟩,
  ⟨36,5,[ew129,ew306,ew128,ew130,ew131,ew132],lh 4 [15,14,7,1,2,35,10,21,417,9] [0x4009500650055005,0x1247473636881210,0x4312124747363612,0x2121123237]⟩,
  ⟨36,5,[ew129,ew128,ew130,ew131,ew132,ew307],lh 4 [1,417,15,7,2,10,9,42,43,35,21,14] [0x2773422602059121,0x1883164101052772,0x5005530306401881,0xb34a643634]⟩,
  ⟨36,5,[ew308,ew129,ew128,ew130,ew131,ew132],lh 4 [43,411,42,1,2,15,14,35,7,10,456,9,38,21] [0x1088d4c310107272,0x162252552322910,0x39aa431001011010,0x4bb663]⟩,
  ⟨36,5,[ew88,ew80,ew129,ew128,ew130,ew132],lh 4 [42,417,411,1,35,14,2,9,7,10,420,412,456,38,356] [0xc3632161404067b6,0xe575d32121404088,0x2112500430092121,0x5339aa52]⟩,
  ⟨36,5,[ew129,ew309,ew128,ew130,ew131,ew132],lh 4 [15,2,7,1,14,35,21,41,424,43,9] [0x100a300550055005,0x4216163737998840,0x1342421616373742,0x2421423216]⟩,
  ⟨36,5,[ew129,ew128,ew130,ew310,ew131,ew132],lh 5 [10,35,179,43,411,21,15,42,14,38,344,1,459,8,5,9,412,7,46] [0x98c1580c021883,0x2006009ce138427,0x10c621884520844,0x529c0015a54a580,0xa892228821e5]⟩
]
def nodesBlock16 : Array Node := #[
  ⟨36,5,[ew311,ew129,ew128,ew130,ew131,ew132],lh 4 [20,190,41,7,14,417,411,30,9,42,179,21,8] [0x4318bb02027a7a99,0x4318180202757543,0xc163465665655043,0x3114022001]⟩,
  ⟨36,5,[ew129,ew312,ew128,ew130,ew131,ew132],lh 4 [35,42,7,14,10,1,48,411,190,20,417,2,8] [0x1001011001100110,0x3268b85959a70110,0xc432326768545732,0x2323423446]⟩,
  ⟨36,5,[ew129,ew128,ew130,ew313,ew131,ew132],lh 4 [38,42,410,14,180,48,411,35,417,2,477,10,7,464] [0x5221211270107117,0x8448466468803227,0x95aa309005b06446,0x93533d3c95]⟩,
  ⟨36,4,[ew129,ew128,ew130,ew314,ew132],lh 5 [21,41,9,14,10,43,424,411,417,420,344,432,465,262,265,35,469,27,8,5,46] [0x802705a161565,0x408e7886013186f,0x52a64202444a468,0xe80]⟩,
  ⟨38,10,[ew138,ew139,ew140,ew141,ew142,ew143],lh 6 [35,14,7,489,488,42,183,2,478,23,481,24,482,10,1,9,45,41,16,484,249,21,486,197,12,50,255,480,257,48,51,479,483,485,487,490,491,492,493,494,495,46] [0x14918900919a145,0x1892c919a000189,0x41b1882db7c8410,0x814454308648294,0x74830845c19449c,0x4c97494c9555188,0x96188041848555,0x8880821960565d6,0x104185618280104,0xc03400c06000c5,0x3800c534d0c538e,0xc01c00c53cf0c0,0x800c51c70c03c0,0xc50820c50450c0,0x38e28434d0c0041,0x30449228b6598d8,0x3cb4cb1cb2843c4,0x2840829041c428b,0x442900825d0050,0x4d21c73113d1944,0x829911d13123d2,0x30e0825ce04130d,0xa9a070419cd041,0x4c70875de0414de]⟩,
  ⟨38,9,[ew138,ew139,ew140,ew315,ew141,ew142,ew143],lh 6 [183,503,10,7,21,14,481,18,32,15,250,51,42,35,16,496,2,488,407,33,9,39,502,45,259,20,478,50,41,486,38,1,508,417,23,497,498,24,499,17,500,501,408,504,482,505,506,195,197,507,509,510,46] [0x30800834d01a31a,0x2101a35a008,0x80185d7008008,0x8388018022008,0x8200f38f00f082,0x1210400f40f008,0x15200f10f012412,0x1d15d01d0e3012,0x4e400d4510120c3,0xd4d3009449009,0x900900900a00a,0xd08d00a00a009,0x65900a08200a64a,0xa10a00c50c00d,0xc900c10400a514,0xc0c300c14c009,0x25013013009145,0x9e638e613659000,0x514191391186082,0x195515195428191,0x1691950d5191410,0x1951451970d7197,0x6db04138e5aa6db,0x6d2cb5ac08206b,0x10406e2cb041104,0x410c306f1c7041,0x11c0410c30701c7,0x59e11e61e2cb59c,0x1c75820c2c5c2dc,0xc821c759f0df81f,0x14b80b1f4cd0145,0x6101c780b]⟩,
  ⟨38,9,[ew138,ew139,ew140,ew141,ew316,ew142,ew143],lh 6 [183,482,488,15,14,511,515,21,0,48,496,7,35,2,41,410,9,19,24,10,296,42,58,20,38,481,249,255,33,517,408,12,49,512,478,321,498,513,503,60,514,516,518,16,519,506,195,197,520,46] [0xd101132001a0da,0x15149101a30c011,0x8200a48a00a082,0x4a00a041061151,0x6214a64a0414d3,0x141c700a34a041,0x11400a1c7014354,0x1b11b01b2e3014,0x72414c0820142cb,0x14c71c003083003,0x4d30435c304c4cc,0xf00f04c5d7043,0xf003003003003,0xf1cf01541500f,0x2c30151c700f410,0x152cb015115003,0x9521425d7003104,0x420421524d2052,0x6429c2982156656,0x142410196a16142,0x34215641079634d,0x75f2081422cba42,0x64ea8220215f2cb,0x4e24904606b14e,0x34e058249058358,0x4e10405820804e,0x24905810404e20e,0x1ad2491861c71ac,0x1041ae2081861c7,0x1861041af208186,0x109749231c07107,0x78d208749]⟩,
  ⟨38,9,[ew317,ew138,ew139,ew140,ew141,ew142,ew143],lh 6 [183,484,35,14,7,521,21,10,249,15,488,523,32,42,24,16,9,0,41,20,12,481,50,409,525,33,1,478,486,23,62,203,58,482,2,195,197,45,522,503,524,515,526,118,497,527,528,529] [0x8204105d1556dd,0x82000249000,0x38e15528a000249,0x1558207e728a7a6,0x1c77a83cf2e1492,0x1554222e15967e9,0x4515e30c3041022,0x5e34516240c3624,0x24c00c0aa01b34d,0x14838e01b08200c,0x94800c38c00c94c,0x81c82cc58c148,0x82cc1cc008588,0x4106b041186048,0x45c01c12c008448,0x14228200810401c,0x65900928a009649,0x94c92c21c2142,0x40d2c24d30091c7,0x4241004218204d,0xcd00210204d18d,0x20c300d10d00d,0x1c7b4e3cf1594d3,0x1541862ca69a154,0xb9414e18604e04e,0x6140c314a10404a,0x1925ca0c3154104,0x2cf18604f04f2d2,0xc32c7107047bd2,0x5c70c32da10461a,0xd00501040460c3,0x46106050]⟩,
  ⟨38,9,[ew318,ew138,ew139,ew140,ew141,ew142,ew143],lh 6 [183,15,1,2,530,7,42,10,9,197,488,532,249,24,12,195,534,32,35,48,21,23,20,478,481,45,409,16,486,58,41,482,484,531,503,533,515,14,526,535,536] [0x4100025c1185dc,0x41000186000,0x38e118659000186,0x11875d3e228a3e1,0x1c73e30822df79e,0x3cf0c32df0823e4,0x4d34200c34204d3,0x251181453da,0x510114a6017057,0x10c34c017492011,0x64c01134d011651,0xc1cc2d109110c,0x4cc2d11d100c08c,0x4154d541551400c,0x14501501500c514,0x112292000027009,0x34d00128a00134d,0x15812d21d2112,0x2062d25960011c1,0x401208401501006,0x6001141006506,0x1001006146006,0x1c7a0d6cd10a596,0x10e20e2ca08210e,0xc310d20840d0c3,0x24e24e10a14a68e,0x20224a3ca10e14e,0x2db20841b0c32c2,0x2422c71476820c2,0x2473c72c2142242,0x2484081452433c3,0x403143248]⟩,
  ⟨38,9,[ew138,ew139,ew140,ew141,ew319,ew142,ew143],lh 6 [537,481,9,14,7,15,2,482,35,24,16,478,32,249,42,12,1,23,539,206,17,208,489,486,183,484,21,195,197,499,513,503,538,527,536,488,10,540,541,542,543,544,46] [0x38c00c20800b38e,0x4d3cf00b20b00c,0x4d04c3cc04c74c,0x1cd78d1cc40c04d,0x6111cc1cc1cd40d,0x4cd60d50d7cd4d1,0x914cb18b511811,0x84b08b491186491,0xd75571044cb0cb,0x800888b10b4d7,0x249005005005249,0x5285008008008,0x800828a005005,0x5005005585008,0x18500e082008588,0xe18e005085005,0x10e00e0ce005105,0x410410050c300e,0x58904728a049049,0x4f082047063009,0x18f049082049189,0x4f0cf04910404f,0x58a0490c304f10f,0x1d008204106400a,0x1861ca0821ca18a,0x1d00d01ca1041d0,0x821ca0c31d0110,0x49969a4991869a5,0xc3a1b104527186,0x51b0c355c10455c,0xc248212aa460c3,0x486104542]⟩,
  ⟨38,9,[ew117,ew138,ew139,ew140,ew141,ew142,ew143],lh 6 [545,35,481,38,7,23,14,15,488,2,484,10,249,478,12,259,546,42,16,225,48,489,227,486,45,41,183,482,9,195,197,409,503,24,542,516,528,497,547,501] [0x34d3cf1454da34d,0x1c74da1453e0,0x410151c7015041,0x822a1015208000,0x2cb3cf0c341b2cb,0x1525c41b0c33e2,0x1043dd18608209c,0x3dd10459e18659e,0x1c700504100d1c7,0x8538500d041005,0x20508d38e08d20d,0x8cc0c3405485085,0x24c4050c34cc48c,0x28524928528528c,0x1254cc18c28c90c,0x7cc1044d7197597,0x20700738e001201,0x10c100138e007,0x4810070c7007487,0x1241011011001,0x101011251001001,0x11111011191001,0x4920882c8001181,0x8848808e2cb08e,0xa608a249088088,0x981a7088108082,0x50b088186098118,0x40350328324340b,0x18640310328b249,0x7c3183419119599,0x194294104289189,0x289104294]⟩,
  ⟨38,9,[ew118,ew138,ew139,ew140,ew141,ew142,ew143],lh 6 [550,481,16,24,35,42,9,10,14,488,2,21,32,195,197,0,249,551,23,41,553,478,548,15,255,250,489,409,486,183,45,482,484,549,503,552,18,518,497,554] [0x55536161859d555,0x14559d618362,0x65901a14501a659,0x4139e01a0de000,0x1c73634d345f082,0x34d2cb45f4d334d,0x1865202cb520186,0x4106401a3cf35b,0x14c00c112015145,0x500d001510400c,0x24904c0c304c24c,0x9501d044c08c050,0x29044c1cc590082,0x5122925122cb590,0x3a65923d26d02cb,0x39235259c21c39c,0x2570170c3004249,0x41c40040c3017,0x840171c7017097,0x42c4005185004,0x40052c5004186,0x5005005205004,0x820491c7004204,0x490820431c3043,0x183043283049189,0x4304304928a043,0x18604106704e208,0x44218250228a447,0x2084423c26c728a,0x3822024533d3393,0x2085063cf38a208,0x50a3cf386]⟩,
  ⟨38,9,[ew122,ew138,ew139,ew140,ew141,ew142,ew143],lh 6 [555,482,15,14,23,24,7,35,2,484,1,39,42,556,249,478,33,408,10,239,41,51,489,0,241,486,45,183,481,195,197,409,515,542,16,21,507,529,497,456] [0x3cf4511044db3cf,0x30c4db104460,0x1c70160820161c7,0x4512cb35c145000,0x51435c2cb461145,0x16208041262016,0x5d745d0c3041063,0x45d5d761e0c361e,0x820041c700f082,0x34414400f1c7004,0x2cb4cf14f90f2cb,0x4e514044284344,0x20e04450404e28e,0x24420824424424e,0x1a64ce0ce24e94e,0x7ce1864d90d9619,0x2cb0024020072cb,0x7487007410002,0x28700248200228a,0x220200c00c007,0x18200c20c002002,0xc18c00c0cc002,0x28a3504920020c2,0x50290345485045,0x555245205350550,0x345185250208345,0xc535a19a61a0c3,0x4920804a04a7c5,0xca052186041067,0x520c304a18604a,0xc32551862480c3,0x248186255]⟩,
  ⟨38,9,[ew123,ew138,ew139,ew140,ew141,ew142,ew143],lh 6 [559,482,488,35,24,9,16,42,10,14,2,560,21,32,195,197,15,486,249,478,562,23,18,557,45,410,489,58,409,183,481,1,484,0,558,515,561,526,509,344] [0x4d33a24515dd4d3,0x1c75dd4513a3,0x65901a1c701a659,0x3a46182de082000,0x19f2de6db38e082,0x38e30c0413df01a,0x14552030c520145,0x4106101a26139c,0x40d00d0e5013413,0x2d26db0130c300d,0x825cd10d98d08d,0x5221204d18d2d2,0x29204d208052186,0x51529551530c5d2,0x3d15d525571230c,0x3d53955d12513d1,0x90010104003082,0x3203003104010,0x183010210010190,0x3303007147003,0x3007307003145,0x7007007247003,0x1862c2208003243,0x421822c4204044,0x1445042842c2142,0x2c45847022822c4,0x2442d85983d8249,0x462860481453c4,0x4804828a046146,0x4106704f596048,0x2495055963ca24a,0x50a58a3c5]⟩,
  ⟨38,9,[ew138,ew139,ew140,ew141,ew127,ew142,ew143],lh 6 [563,484,14,15,2,478,564,273,566,21,50,42,32,10,195,488,249,197,58,35,24,410,16,565,20,33,41,489,45,183,481,482,526,510,520,567,498,544,568,569,51,7,46] [0xcc00c4e00052cb,0x1905100054d300c,0x7105cc51484c70c,0x89035020c58c190,0x75020c34c5d0596,0x5c77473878c75d0,0x247045105385385,0x45245047107047,0x874474475c5085,0x133cf4453855c7,0x6590033c3003664,0x3603013693013,0x3013618003683,0x150150156d5003,0x25500b00b0036c3,0xb24b015015015,0xb00b08b003003,0x19961800308200b,0x596194614954596,0x392992194794219,0x24938f38f192792,0x19224905210418f,0x8218f18f04f104,0x44f082192192452,0x7ca38a9ca21a7da,0x20d24d38d38d20a,0x10420a24904a10a,0x44a08a20d20d04d,0x10444d08220a20a,0x1b08204146801b,0x8204106a041069,0x44044051]⟩,
  ⟨38,8,[ew138,ew139,ew315,ew141,ew319,ew142,ew143],lh 6 [206,35,21,488,16,24,7,259,14,250,42,51,32,417,17,18,571,12,407,9,570,1,183,408,486,33,412,39,45,478,411,2,526,249,512,497,10,60,572] [0x28c00c06001d28a,0xc14c01d04100c,0x2200c10c007021,0xc00c00d10d00d,0x58d00d0de00059e,0xd7cd00e0c300d,0x820127d2012082,0x181a301221200d,0x9012186018218,0x1001001141009,0x109001001009145,0x1104009009009,0xc90096490010c1,0xa4ca001659009,0x820014d3001081,0xa20a00118100a,0x39700120800a18a,0x685385005104517,0xc3000596517104,0x5170c3005585005,0x2cb1c50823912d1,0x3853c56910911c5,0x2084113cf411211,0x1c71e40040c3685,0x821c42cb515082,0x5041845152d51c4,0x3c44151864153d5,0x1db2cb383082944,0x1833832cb1db09b,0x41c19c41c3cf383,0x1869822083833c3,0x1c2186413213413]⟩
]
def nodesBlock17 : Array Node := #[
  ⟨38,8,[ew320,ew138,ew139,ew140,ew141,ew142,ew143],lh 6 [573,209,24,502,35,14,7,50,2,32,15,249,9,45,21,488,42,407,478,481,60,574,304,486,183,506,412,195,197,482,16,503,203,575,46] [0x2cb0134920002cb,0x4128a0dd492013,0x10405828a058104,0x34d013082041,0x1c701334d000082,0x5142080c37de013,0x38e59920859938e,0x55c18651b1456a0,0x28a69b18655c145,0x49289049104052,0x34900b082052104,0xb34b009089009,0x1cb0cb04b0c91c9,0x492090c90c900b,0x38905121105138e,0x57186051151049,0x3c4051191057157,0xa3cf00a082004,0x1ca0c40c4004082,0xc41c70ca04a0ca,0x304044208050310,0x44184050210044,0x144050190050150,0x200200f1c7044,0x30c00f00f0021c2,0x230200220200f,0x14500218200f20f,0x214200d18d00d,0x30c0c72070c330c,0xc31860d42080c7,0x1450c71860c7147,0x54c1a28481450d4,0x58e18e54c145]⟩,
  ⟨38,8,[ew138,ew139,ew140,ew321,ew141,ew142,ew143],lh 6 [215,576,10,12,51,42,35,14,7,39,407,16,249,577,488,15,32,481,580,183,486,503,579,259,41,478,482,60,195,197,581,526,497,416,578,21,203] [0x3d001019f019145,0x4c0cc019186010,0x38e0500c3050390,0x4a44a04c04c04c,0x2ca04c44c00a4ca,0xc2cb00c08c34a,0xa04c10c34a08a,0xc00c00a10a00a,0x1d401422000a1ca,0x4638e00a208014,0xc304f38e04f0c3,0xf4cf005005046,0x820054c500f00f,0x50820052c5346,0x1060050053462c6,0x5104006006006,0x2050051c5006206,0x4e44e0061c6005,0x4e049449049049,0x432cb04908904e,0x1030492c9043083,0x49109049049043,0x1c3049209043043,0x491c9043203043,0x8285b2cb35a082,0x5110435a2cb89b,0x20859c1c7555563,0x59c20849d1c749d,0x34b78b104342342,0x3422025c210434b,0x1c23582184981c7,0x4842045e41c7582,0x7972084841c4]⟩,
  ⟨38,8,[ew122,ew138,ew139,ew140,ew315,ew141,ew142,ew143],lh 6 [35,18,10,2,14,7,582,407,42,39,556,32,1,496,33,239,502,15,51,488,250,486,183,481,503,41,45,482,60,408,38,581,21,583,508,570,417,249,24,501,259,506,240,241,456] [0x1cf5553c71d6555,0x20858000f208587,0x2892574d33c0016,0x6068dc5c924a4d3,0x65e19d758198606,0x4108174a041f797,0x162041885161041,0x44b2c0007447845,0x2c62ca2a41c01cb,0x2ca2a52ca2ca4d3,0x8b34c34d6592cc,0x1c30c73c734334b,0x55514534434d3cd,0x39101300d14d544,0x50f50038e453451,0x943d4446451191,0x300502514314002,0xf0000c020f200,0x1481080050080c8,0x2a638a380100205,0x28209030c382386,0x2490c939238e30c,0x12724524e0c3252,0x6d06c910468569a,0x49b082406710082,0xc3a524860c3a12,0xac1046104a81046,0xb1f0c3090086104,0x14c301042142410,0x48104310408104c,0xc1052104]⟩,
  ⟨38,8,[ew123,ew138,ew139,ew140,ew315,ew141,ew142,ew143],lh 6 [16,14,2,35,10,584,9,51,560,18,32,15,486,557,39,502,250,33,45,42,410,496,407,21,488,478,183,481,503,508,482,195,583,581,579,205,41,7,417,249,498,24,500,60,585,197,344] [0x30d65934c31a659,0xc369450d0c368c,0x21249b38e35451a,0x7057df6d248838e,0x1041608dc15c705,0x8461a00823dd91b,0x95b2498861a15d7,0x50a2830cc5143cf,0x2852882263030ca,0x288227288288618,0x10a540555104280,0x5825965d754254a,0x30c34c5815955d5,0x4680d8616356301,0x40d4034512d82cb,0xd03502c52cb14b,0x34041100100c4,0x4061900904c64c3,0x4d30532cd2d3093,0x22944844b04b4cd,0x20410f000444105,0x38e0aa446191000,0x52389391082386,0x78f78e041489492,0x1de0003c5acf000,0x82b071c5082887,0xb49245041749245,0x1c7106185041,0x4100f0041c7006,0x1c91c20413cfb9d,0x89247047]⟩,
  ⟨38,8,[ew138,ew139,ew140,ew315,ew141,ew127,ew142,ew143],lh 6 [14,15,586,33,250,50,16,2,564,496,565,42,35,32,587,10,21,41,39,508,45,481,183,503,583,195,478,488,566,506,197,502,589,51,581,526,417,249,24,572,17,575,588,203,259,60,18,46] [0x30d04d34c8da2cb,0x51434234822468c,0x346348225348348,0x24d3cf2462493cf,0x28939638e28e256,0x3871ce40e247249,0xe28e240249410,0xc131b309289380,0x10a10c0c305b041,0x304284042041081,0x18c10f10418430f,0x10a10458404a04c,0x1044042ca2c1581,0xb04a04b40b10a,0xc80c10012ca2cb,0x3e71860cf0c2226,0x2280d50c318620f,0xd00c3203215558,0x4831c34904921c7,0x12508514000488,0xa45142186705152,0xa825d764265c186,0x1c7b02ac25d7602,0x4c26421c7742742,0x442000782782000,0x61115f145b4545f,0x1501451c5450451,0x1450051a01911d1,0x4e1547846000160,0x4d3bd38ae540013,0x1e21d3000]⟩,
  ⟨38,8,[ew138,ew139,ew140,ew316,ew319,ew142,ew143],lh 6 [206,511,16,24,21,7,512,42,15,35,10,2,14,410,20,19,1,38,17,296,9,481,12,0,590,48,299,482,183,255,41,249,290,60,277,49,478,321,488,591] [0x1cf00f26301f1c7,0x4f0cf01f24900f,0x4f0460c6046006,0x6db6e404608604f,0x7060462a0000720,0x62c601228a006,0x1040132d3013104,0x1d165013313006,0x4901314501d31d,0x480080480c3049,0x8800d00d0490c3,0xd082008008008,0x28a00d38d009289,0x750700938e00d,0x10400d51400d10d,0x7307008148007,0x55500830c007147,0x43543043082041,0x6604338e052082,0x432cb05610405b,0x1430562cb043103,0x56156056316043,0x38e055055043303,0x5538e002702042,0x6426822cb850650,0x8425c28902d0682,0x1426105d7610150,0x69165948a104882,0x15148a64a691111,0x61e15e61e5d7491,0x1459c43044915d1,0x684145614314614]⟩,
  ⟨38,8,[ew239,ew138,ew139,ew140,ew141,ew142,ew143],lh 6 [511,212,35,592,16,14,9,7,2,15,58,10,32,249,42,21,407,481,17,478,593,299,486,20,41,183,503,506,277,195,197,482,488,203,497,594,46] [0x4d300034d0114d3,0x4124901134d0df,0x82059249059082,0x6a001128a041,0x1040002cb011104,0x4922080112cb0c3,0x18655b20855b186,0x51e1c749d145721,0x24971d1c751e145,0x4c24c04c08204d,0x68c00d28d04d082,0xd00d00c28c00c,0x10400d2cb0cc10c,0x4c20c0cc2cc0cd,0x3cf0502100503cf,0x561e205015004c,0x20501c7056156,0x9049009289002,0x5c90c22c200228a,0xc25d70c92c90c9,0x1860423c204e18e,0x421c204e3ce042,0x14504e1ce04e14e,0x310400a2cb042,0x18600a1040002cb,0xa18600a20a000,0x1450001c7012208,0x1214500a1ca00a,0x1840c42080cb186,0xc41c40cb2080c4,0x1440d81d80d8145,0x5061e48c81480c4,0x5481c7506146]⟩,
  ⟨38,8,[ew117,ew138,ew139,ew140,ew141,ew316,ew142,ew143],lh 6 [15,2,14,7,12,35,488,496,511,38,597,20,296,225,48,546,410,0,10,19,42,481,249,183,255,41,595,596,482,17,299,515,259,9,599,517,58,503,598,512,478,321,547,16,506,226,227] [0x31a59634c317596,0x5c514d0005cc,0x21b908186345157,0x24f4923c925c492,0x9a57ca7ca79d709,0x2088480612a081a,0xe30828c30e2082,0x134c514c000883,0x1c6193113305153,0x1cf3e74c64c7107,0x3e81d51cf2491ca,0x30104c34c1c11cf,0x6180e91c21c7347,0x1041461870c3602,0x152145105006000,0x4052cb0124802c0,0x35000a00028040d,0x40d41005050d510,0x514094003014041,0x20418b2c0082503,0x21554620610b104,0x10a21d115104204,0xc6208a9b041108,0x1820840c3102106,0x4b38b28facb54b,0xc92c1049389241,0x2422590d9642089,0x6c38e28105e38e,0x4512830ed451281,0x3914410822830ee,0x5144e08e]⟩,
  ⟨38,8,[ew118,ew138,ew139,ew140,ew141,ew316,ew142,ew143],lh 6 [24,9,14,2,15,35,488,511,600,48,0,496,255,38,20,548,41,551,42,250,19,296,410,481,249,183,10,517,595,482,195,515,599,596,602,45,503,601,22,7,512,478,17,554,16,8,603,197] [0x31c6183cc319618,0x1456534cf14564c,0x1db8c71863d34d9,0x41134d45041d34d,0x9647c87c879e750,0x84106024922099c,0x9c728a881061249,0x4d450514c4d31c7,0x2c6194014305154,0x2d146850650b00b,0x4692d72d169a2c8,0x5435550412c32d1,0x30c3cc54254b04b,0x1461953d5302,0x15a145005106104,0x58538e11a104384,0x3d610810420458f,0x5810560d6481496,0x49209210f1120d2,0x1c018e38408448f,0x1d75c61c600e000,0x481ea0170001c0,0xc60010000c0181,0x1c7adb082007006,0xb4e041211b0e5ce,0x28d3830cd04d343,0x34209029040240d,0xee2492030e2249,0x28a20209b28a203,0x24a2430822020af,0xca289089]⟩,
  ⟨38,8,[ew138,ew139,ew140,ew141,ew322,ew142,ew143],lh 6 [228,605,35,488,48,14,7,24,604,249,10,42,1,38,296,32,15,607,482,183,486,481,45,602,515,478,41,17,596,195,197,408,526,497,606,578,299,21,203] [0x40f00f0a00192cb,0x2091c901908200f,0xc300f1c700f0cf,0x4968904f30f209,0x4904f68f04930c,0xe4ce04e48e049,0xe049109049489,0x900900e10e00e,0x1540141a100e14e,0x2020c300e186014,0x1c70100c30101c7,0x5030c042282202,0xb04230205028a,0x20020024c200b,0x10200b00b00b4cb,0xb104002002002,0x18b00b14b002182,0x20328a00214200b,0x30c20728a04730c,0x8876c7203543043,0x2038c36c3207547,0x207207707104203,0x145203186903104,0x5c3145216196456,0x48d04d04d04a48a,0x4a10404a04a04d,0x4a04d10d04d04d,0x4c14504d18d04a,0x10404d14d04c186,0x5dd145618625215,0x18645e14545e186,0x4441847e61455dd,0x71f186444144]⟩,
  ⟨38,8,[ew138,ew139,ew140,ew141,ew316,ew127,ew142,ew143],lh 6 [24,496,15,2,14,608,58,20,566,565,410,42,609,488,35,38,21,19,517,564,183,511,515,249,45,10,599,482,41,195,610,506,197,48,0,596,512,478,591,586,594,17,16,60,8,5,611,203,408,46] [0x5d12d144e3972cb,0x10586110115ce,0x45048224458441,0x482250530483cf,0x24131430c24c054,0x3030cc40c043041,0x10c24c044041401,0x38d341241304,0x39938e00e08d082,0x28e1c70996421c2,0x24a085082142289,0x28928a50a08908a,0x28a0ca2c92c2502,0x10b08908b0cb289,0x3471c21022c92cb,0x18d20d007000980,0xa060130009c0193,0x195186a46015006,0x4060c6350340680,0x10601e00d0cd190,0x1d31c010019e186,0x6da22b1db1c522a,0xec1d040720721b,0x3c83c70c33d03cf,0x74f10470871c12d,0x596685b85596745,0x7c57c50c3c05bc5,0x8051044857450c3,0x4a1543845104805,0x492c528e2544892,0xe30d2104]⟩,
  ⟨38,8,[ew138,ew139,ew140,ew323,ew141,ew142,ew143],lh 6 [521,612,35,14,32,613,2,7,24,16,9,15,20,249,614,58,42,10,407,481,21,486,17,615,616,41,478,503,183,488,482,195,197,23,484,497,60] [0x2c404408205a2cb,0xd20805a082044,0xd0042040046c4,0x14488400d4e100d,0x24400d00d0044c4,0x4d24d04d44d384,0x514144184384451,0x4504152192152,0xd50551e30520d2,0x20020521c7055,0x20800b04b00b208,0x4b70b042042002,0x45104270204b04b,0x4b45104b30b382,0x18215029038230c,0x15019014228a142,0x1d00500d00421c2,0x84dd0420c2050,0x24800f30c01b01d,0xf249008308008,0x28f00f18f00028a,0x81c800518600f,0xc300f1cf00f0cf,0x59624939e30c008,0x28a39e2495a430c,0x1328a013186000,0xc35df1c7145186,0x5df0c36201c7620,0x28914918638c28a,0x3891c914c186389,0xc33991d96190c3,0x14a1c71460c35c9,0x1461c714a0c3]⟩,
  ⟨38,8,[ew138,ew139,ew140,ew141,ew324,ew142,ew143],lh 6 [523,617,14,7,619,2,15,32,9,24,249,35,618,33,16,50,42,296,21,488,482,478,58,486,481,45,620,621,515,183,17,60,195,197,484,498,10] [0x4070472cb055410,0x30a5960552d5047,0x4ca0475870474c7,0xa70a00738730a,0x50700700700a38a,0xa50a10a88a007,0x49210a14a007007,0xa492111151111,0x970570c3051091,0x30b4cb0510d1057,0x34d0464c6046363,0x638600b00b30b,0x4b00b38e006046,0x4604604674604b,0x48611021004b74b,0x110490106208106,0xc30500900460c6,0x30d3cd046082050,0x38e3093c900938e,0x7c978930d60d00d,0x2087cd78d309609,0x30920910914930d,0x823090c910d145,0x6c90893190d9699,0x20801c02430f60f,0xf20f00f145000,0x8f00e0c3004145,0xe08200f0cf00f,0x208014145000208,0x6e00c3104145014,0x826a10c36a1082,0x1080c31050856e0,0x1050c5108082]⟩,
  ⟨38,8,[ew317,ew138,ew139,ew140,ew141,ew319,ew142,ew143],lh 6 [15,14,24,16,9,7,521,35,206,12,1,42,32,249,539,523,17,478,21,486,183,481,0,484,482,623,62,207,208,488,626,525,23,203,622,503,624,2,526,625,118,10] [0x82cb38e8154d3,0x2492000082cb200,0x542086249182095,0xcf28a3c30d828a,0x6634104108a1603,0x38895510441a6a4,0x59c04171659b041,0xc3079910006d6,0x30830d2494471cc,0x34c28c34634c24c,0x51430f30d28d348,0x4089cd50d359348,0x44e3a8392491211,0x1514c14d3145441,0x80000821c61d1,0xc01cf1c7087,0x5001c81c70c7008,0x2c42c7507008000,0xb48b004100480,0x412c514b04b005,0x3c30c2182186180,0x891043c674219d,0x142246242102086,0x81089149241242,0xca104186a43183,0x14328f2831030cf,0xc10ca14a281283,0x4171045ce5ce104,0x1457c105e145390,0x10515204178105f,0x485484041]⟩,
  ⟨38,8,[ew117,ew317,ew138,ew139,ew140,ew141,ew143],lh 6 [225,521,15,2,7,488,35,14,21,12,16,9,627,249,478,32,20,259,38,48,10,481,628,484,0,183,1,409,486,42,41,17,118,24,8,23,629,62,578,526,497] [0xc30415550480c8,0x1938e048548019,0x2004838e008448,0x818800b082019,0x24b00b186008082,0x30b68b0415e104b,0x49245f69a4514a2,0x58b10b4481c830b,0x38e44810458b1c7,0x1865d75e3043,0x82003186003082,0x437c3055145000,0x492055064043145,0x983483943283313,0x6136c310331328a,0x6c3618593113593,0x8f00f1a700e08e,0x4d24d00e18600f,0x14504f24904f14f,0xd50d30f28f04d,0x60d30f51400d28d,0x1c1dc01c12800d,0x24904614500d104,0x46249042145042,0x502002402306514,0x2102306410002,0x1c201d11d01d1c7,0x49289045410002,0x10404528a049410,0x491040491c7045,0x1c730a10a0451c7,0x6ca1ca31e11e59e]⟩,
  ⟨38,8,[ew122,ew317,ew138,ew139,ew140,ew141,ew143],lh 6 [239,523,2,21,35,7,15,10,630,14,24,32,1,9,488,249,486,408,42,39,51,33,482,631,0,484,183,478,409,45,118,500,17,41,16,23,62,578,60,468,526,497,498] [0x82041596043083,0x1a41004358301a,0x1e043403003443,0x310300d49201a,0x38d00d104003483,0x46038e4514df20d,0x66220d84d20d4d3,0x5cd14d443243041,0x6c24431455cd249,0x104659663202,0x186002104002182,0x9022822144d3000,0x1c721428a9424c2,0x421c7042982056,0x614702142056067,0x7026185d41545d4,0x18b00b12801b186,0x20f28a01b10400b,0x38e00b28b00b38b,0x4f1cf04b30b20f,0x60f04b1cb04f30c,0x1061001016900f,0x56a20438e00f145,0x204555006386006,0x1c70463060441c4,0x614604430c046,0x249012152012249,0x4a30c2151c7006,0x14a05531520a1ca,0x21d15d5dd24920a,0x24904714770a24a,0x4724904c14504c]⟩
]
def nodesBlock18 : Array Node := #[
  ⟨38,8,[ew138,ew139,ew140,ew325,ew141,ew142,ew143],lh 5 [530,632,35,14,7,16,10,9,2,32,249,12,15,42,633,58,634,486,23,481,635,409,503,21,183,17,41,482,484,526,488,60] [0xa5a90a45d0c5b1,0x26c90296b0c442,0x2a6a0280a02569,0x280a02669b26c9,0xa8a50a8ca724a9,0x848e70a90a724c6,0xc8720aaea84912,0x48840c4710c491,0x302c0316c00802,0xb30c088220096b,0x708c208b020b02c,0x708a20b0cc0b0ac,0x808e780ae20b4ed,0xb46d088820b6ed,0x2e6b088620b48d,0x2cab03cc60581e,0x2ce703ca502cc6,0x2d0803cef03d0f,0x3c8f03c6f00084,0xce4a576cc605063,0xad4e776ca5cfcc6,0xad508870e787108,0x4c8404c6300084,0x81508718e60e063,0x71484a9908714e5,0xa14637689aa6863,0xa1c6381c84a2063,0x82084]⟩,
  ⟨38,8,[ew138,ew139,ew140,ew141,ew326,ew142,ew143],lh 6 [532,636,15,488,24,14,7,32,1,2,9,35,249,637,42,638,50,21,23,409,639,515,482,255,183,481,45,478,58,17,60,484,526,321,501,10] [0x870472e005b38e,0x34c71c05b2cb047,0xc30471070470c7,0xc54c00720734c,0x58700700700c20c,0xc58c54c54c007,0x45104c24c007007,0x4c4513d22523d2,0x1570571a1052152,0x34b0c3012186057,0x10b0420c3042104,0x220200b00b34b,0x4b00b208002042,0x4204204260204b,0x44204e28e04b60b,0x4e44e3c228a3c2,0x18e04e14e042182,0x34340304214204e,0x203344404004208,0x784744343643003,0x283783743344644,0x3442843c4244343,0x1623441844c3249,0x50414535a19a51a,0x28a015023350650,0x10290010249008,0x148000186008248,0x14145008188008,0x28a3df2494d328a,0x1864d32493df,0x145016186016145,0x3ca186509145058,0x3c918650a145]⟩,
  ⟨38,8,[ew318,ew138,ew139,ew140,ew141,ew319,ew142,ew143],lh 6 [15,9,206,7,24,16,530,249,2,42,12,1,35,23,32,532,208,207,48,21,481,183,195,17,641,197,482,640,539,14,478,534,486,503,624,64,526,535,488,10] [0x24200009081434d,0x104089242000089,0x50a28610418a294,0x2cf1453cb2da145,0x6e15d15d159668b,0x7124910415d18e2,0x7540dd61249c041,0xe38c91e249082,0x38238728a78c30e,0x1ce2ce1c61ce28e,0x54d38f3872c71c2,0x3423475471db1cd,0x4cd48d353347487,0xa54030cd08d1d3,0x2000100306302,0x14030f30c104,0x54030230c145002,0x24124c54c002000,0x94c90010404d3,0x802430c9089003,0x3c5144184186180,0x10a0413c6984184,0xc3288204041108,0x10610a0ca286284,0x20b0411869c5185,0xc32c82c5041148,0x14f14b0cb2cf2c5,0x21f0417c8218041,0xc36506500c3608,0x430c8448411599,0x203201401]⟩,
  ⟨38,8,[ew327,ew138,ew139,ew140,ew141,ew142,ew143],lh 6 [642,643,14,35,10,488,2,7,273,644,9,15,16,24,23,21,42,206,645,17,481,12,1,489,503,646,45,41,484,195,197,249,482,203,625,647,46] [0xc361861f01738e,0x170c30172cb000,0x5550541450002cb,0x54555041145041,0x104054596041104,0x4e13cf260596054,0x18649c3cf49c186,0x65e0824dd1c74d3,0x2cb4dd08265e1c7,0xe2cb00e0ce008,0x1450483480080c8,0x4814504134d041,0x30c249104248308,0x451186048104249,0x3cf4881864883c8,0x4481c844e08e462,0x14544e1c7448082,0xb14500b34d003,0x30c003103003343,0x330300b10400b,0x28a003183010290,0x31c3010190003,0x830101d0010090,0xd30c045104003,0x28a04530c04d104,0x4d28a04d186045,0x820451c5045186,0x4508205a1da05a,0x28a24c18624428a,0x2441c424418624c,0x8225b1db25b082,0x48a1e48c6082244,0x48f1c764a082]⟩,
  ⟨38,8,[ew138,ew139,ew140,ew141,ew328,ew142,ew143],lh 6 [648,649,14,15,10,35,488,650,16,24,9,478,32,539,42,7,249,407,21,0,12,651,1,481,486,653,641,489,45,41,183,203,195,197,526,652,578,501,482,2,17] [0xcc00c16200b38e,0x5051400b14500c,0x19004c50c04c18c,0x1d01101cc58c050,0x7901cc10c1d0590,0x5517917d18d1550,0x49134b54b90b7cb,0x34b48b351351351,0x986583cf54b08b,0x518668b3cb558,0x505003183003514,0x3583005105005,0x5005585003104,0x30030036c3005,0x48300e28e0056c5,0xe48e00328a003,0x3ce00e08e0033c3,0x4610400308300e,0x208049109009208,0x490490465c6046,0x28a0460460495c9,0x49289049049046,0xa50493c9046046,0x4908205c3dc05c,0x9880485c8044044,0x4428a0445c41c8,0x1c41c82881c81c8,0x1dd0821c83cf1c4,0x28a1c80821dd3dd,0x6a008234da2701b,0x4d36610826614d3,0x34a4d33520826a0,0x3524d234a082]⟩,
  ⟨38,8,[ew138,ew139,ew140,ew141,ew328,ew319,ew142,ew143],lh 6 [35,24,16,7,15,21,249,649,0,648,12,23,1,32,42,17,539,14,407,650,9,537,481,651,486,478,206,207,208,641,653,526,497,488,482,10,489,484,2] [0xd10d3407d938e,0x4134f346046640,0x18f18d08d18718d,0x486686353346082,0x5cb18f19269248f,0x2cf2d25d248f48b,0x18b40b2c52c65c6,0x45860380b20b185,0x1010402402c30d8,0x80240001044244,0x240002084244102,0x15004244115100,0x4244109100240,0x50000510e50e009,0x3913800c0385140,0x471c701100e0ce,0x1c1296293082047,0x4904a1ca056041,0x411c12852931e1,0x44a04304a1ca045,0x30730144128328a,0x8c58c0a2082582,0x4c23053071e3089,0x8308c4cc085082,0x9024423030cc44c,0x3e6545150425549,0x7030dc2086c30d0,0x3d014541041b208,0xc378821d0c340f,0x50820544574821e,0x148214454]⟩,
  ⟨38,8,[ew329,ew138,ew139,ew140,ew141,ew142,ew143],lh 6 [655,15,23,556,14,7,24,35,10,488,16,478,546,2,539,51,48,42,489,654,17,641,656,249,486,45,41,183,503,21,195,197,578,39,408,38,259] [0x2cb51c0824db2cb,0x414db08281c,0x1c70120410121c7,0xc38a1012249000,0x35d30c923012208,0x55e10438e51d012,0x14559f10459f145,0x21c700b04155e,0x18200b1c7002041,0xcb1860cb2490c2,0x2083022820c2249,0x30b208317297317,0x34238238238b34b,0x4c210238b50b382,0x1424d8118598145,0x1186007249542,0x207007187001241,0x1208001281007,0x341011011007287,0x1134d001001001,0x145011111001141,0xc9208001104011,0x28a0c620600628a,0xc63460c93c90c9,0x1460c934d0c63cf,0xd91590d91040c6,0x3cf3084080c6106,0xc83cf30a41030a,0x15a31a10430a14a,0x38d10430a10a31a,0x145390110390150,0x38d]⟩,
  ⟨38,8,[ew138,ew139,ew140,ew141,ew330,ew319,ew142,ew143],lh 6 [24,42,15,16,7,486,660,48,2,1,35,657,9,12,32,249,23,208,21,658,207,17,659,537,481,641,478,206,539,661,526,418,488,482,10,489,197,14,195] [0x28e08e38a79a041,0xe39538f00068a,0x3d53ce0ce3cb3ce,0x14f6cf39338f0cf,0x5903d43c56c5155,0x41540558515f150,0x4901d04124051c5,0x585144150590152,0x8008a18a404105,0x8a18a280002182,0x1822830c2182083,0x97081181057042,0x28118104604a18a,0x30c092481301286,0x46042104052042,0xb2cb086081101,0x2cd0180130c300b,0x3463402c035834d,0x30020034c3532e0,0x2cd00400d20800c,0xcb0c02c034434d,0x243603261249609,0x20824c24b2e2246,0xc40c92090cc303,0x8c34c32442494c9,0x1c75082114645c6,0x5c41191c770821c,0x31d1c764c311525,0x1044514591c774c,0x1c41c8508454991,0x204207447]⟩,
  ⟨38,8,[ew138,ew139,ew140,ew141,ew319,ew127,ew142,ew143],lh 6 [24,2,14,16,15,21,35,564,273,663,410,32,249,42,478,1,207,12,566,23,539,208,195,563,537,481,17,482,197,565,206,484,7,526,572,591,586,647,662,488,10,60,664,665,9,46] [0x18b10b2c684e34d,0xb2e22cc451386,0x32330b3cb30730b,0x3137532d22cc3cc,0x7934e54cc74c324,0x4d04c8788226213,0x38804820520e041,0x8821520e08e385,0x280286246390388,0xc624618000a24a,0x2461830c4244103,0x197184244117106,0x10a24a298284244,0x24a28528d24d118,0x34234424434534a,0x71c710210d24d,0x1e70170120c3007,0x1d96501da019012,0x1400404451401c0,0x91007011041005,0xd70c0082447451,0x6d04a90db0c71e8,0x413c514348349b,0xd20cf04f0c5143,0x5830823d23cf08f,0x41642ba9069a590,0x7c515f041505156,0x71c082550594041,0x56c601055082715,0x514b54520602814,0x54055082]⟩,
  ⟨38,8,[ew138,ew331,ew139,ew140,ew141,ew142,ew143],lh 6 [666,668,24,16,35,14,7,488,2,15,667,9,10,273,548,669,42,21,670,255,41,671,409,481,489,503,45,321,482,515,484,478,305,17,183] [0x25365965f013613,0xa24a00a104013,0x1c704a08a013104,0x4a1ca041082041,0xc338a50a3cd0c3,0x38a20a3cd50d38a,0x45148d20d48d44d,0x4d19b38e15b38a,0x24939518638d145,0x18249018104000,0x1c7057082000104,0x571c7041082041,0xc381d30c3dc0c3,0x5962083dc30c85d,0x45149e20849e451,0x41186057145596,0x1c70571863a2145,0x91c9009082004,0xc9004304004082,0x40c4009309009,0x2cb0042040102d0,0x4184010210004,0x144010190010150,0x420c304730c004,0x2cb0470c3042302,0x422c2042202047,0x145042182047207,0x214205a19a05a,0x2c34832033cc2cb,0x3c318358c2083c3,0x1433d4194554145,0x48b18b548145543,0x48818654b145]⟩,
  ⟨38,8,[ew138,ew139,ew140,ew141,ew332,ew142,ew143],lh 6 [672,673,32,24,9,15,41,255,488,551,35,21,14,0,2,18,50,42,23,676,211,674,409,481,250,489,12,183,515,195,5,484,526,60,675,10,482] [0x6020022a0007618,0x470c700728a002,0x2080420c2042202,0x247187242402047,0x6c2242182247410,0x5476c7847707542,0x2cb542382882702,0x5822cb4d23924d2,0x30c507507552312,0xa208512752547,0xc30052050050c3,0x540500a18a00a,0xa00a410005186,0x500500564500a,0x2c501111100a64a,0x112d1005104005,0x11011311005005,0x48186005305011,0x48043186043043,0x430430485c8048,0x1040480480435c3,0x4310404338e048,0x30c0433c304838e,0x330c05a3da05a,0x10425d263006646,0x25010425038e246,0x3de24935e246386,0x2543cf24634d046,0x2cb4df1045962cb,0x5734d5961044df,0x3cf26434d0413cf,0x4c434d50b30c057,0x4cb34d504304]⟩,
  ⟨38,8,[ew138,ew333,ew139,ew140,ew141,ew142,ew143],lh 6 [677,679,14,10,488,7,24,16,9,2,15,273,35,21,678,42,185,557,680,486,45,681,409,482,489,515,41,481,503,484,478,682,60,183] [0x3d365965e013613,0x1029001030c013,0x51038b18601330c,0x38b50b450186450,0x1c70410c304b1cb,0x45025004b0c3041,0x34d48b24948b34b,0x4b14b451082450,0x28a45514544b08b,0x1828a01830c000,0x10439b18600030c,0x39b10481c1867dc,0x1c70410c30571c7,0x5962490570c3041,0x34d49d24949d34d,0x41145057082596,0x104057145461082,0xa10400a18600c,0x1c700c0c300c186,0xc1c700a0c300a,0x20800a34d00f20f,0xa14500f34f00a,0x8200f14f00f08f,0x461c73840c400a,0x2080441c43860c3,0x386208486249384,0x82384144584244,0x544084394154554,0x208047249043208,0x43145043249047,0x8205a15a05a082,0x48814854d082003,0x48d145548088]⟩,
  ⟨38,8,[ew138,ew139,ew140,ew334,ew141,ew142,ew143],lh 6 [683,560,16,14,15,21,35,685,249,10,2,32,58,45,42,9,23,18,686,687,0,486,684,409,481,410,489,1,183,503,195,501,484,526,17,339,497,488,482] [0x64b00b1a1015659,0x4830801518600b,0x34804b30c04b34b,0x88b74b588708048,0x8b8c874858b70b,0x1c80821c82481cb,0x1455882881cb249,0x5c8145490290490,0xd54d54e45900d0,0x63464d0790595,0x30600434400430c,0x4684006006006,0x246006686004004,0x4244004084006,0x14400e3ce006086,0xe14e0043cf004,0xe00e0ce004004,0xd68d0040c400e,0x8204d24d05e065,0x4d082041249047,0x3cc04c28a04d3cf,0x4145f04d28a04c,0xc304c45104c0df,0x1c7082058249053,0x145058082041249,0x4a01454a028a5d7,0xc30414515d728a,0x1e60c3058451058,0x1451c228a1c9145,0x1c25021c928a1c2,0xc31db51b1db0c3,0x48f5144c50c5002,0x4855144cf0c3]⟩,
  ⟨38,8,[ew138,ew139,ew140,ew141,ew142,ew335,ew143],lh 6 [688,692,14,7,15,24,16,2,10,21,35,42,9,565,609,33,690,691,488,689,587,20,693,273,484,489,45,41,481,503,694,482,515,249,195,498,662,695,696,697,183] [0x11301328a017117,0x413153017297013,0x492354154354492,0x34e208454194413,0x1c745420834e18e,0x4e1c704e24e041,0x36100e64e041249,0x4e0ce34d082362,0x4923560c334e082,0x44840043e300a,0x54400a20a00a3cf,0xa555004204004,0x30c00424400b30b,0xb00b00b24b004,0x64b00a00a00a64a,0xb08b0040c400b,0x55500408400b0cb,0x40554590518640f,0x1c540f30c44f186,0x4f1c7405305045,0x70f78f74f405705,0x4050c394574540f,0x8241a0da59a082,0x461c744830c585,0x7c60481c8446306,0x4487c8788808446,0x824460c3986806,0x5860a745b0db59b,0x49049609047047,0x9089047607049,0xc904c08c04c0c3,0x410c3058082049,0x580c3368082]⟩,
  ⟨38,8,[ew138,ew139,ew140,ew141,ew142,ew336,ew143],lh 6 [564,698,58,16,21,20,42,32,14,35,15,701,2,23,249,17,699,221,0,700,481,478,486,10,489,41,48,183,503,195,482,7,497,488,60,484] [0x187047249055186,0xe082055255047,0xe0070870073c7,0x3ce14e4070c700e,0x30e4071474ce0ce,0x2cd30d2cd1042ce,0x7074cd6cd2ce104,0x3cd70d4c76c73c7,0x2164564604cd20d,0x4904944d74d4d6,0x8904a04a04a082,0x4a14a0495c9049,0x4604914504a5d7,0x4a04a04a10a046,0x606049049046106,0x49609046046046,0x4604620604a04a,0x214504a20a046,0xc300014500f0c3,0x2302000104002,0x60200b30c002102,0x1d021042,0x208002002002202,0x2c3303405105011,0x7852c530c403103,0x4037833c33c3405,0x2084034833c5885,0x443203419499459,0x2cc00c50c004004,0x442040045042cc,0x4922da21a2da492,0x142080000002c4,0x2e321f01401f]⟩,
  ⟨38,8,[ew138,ew139,ew140,ew141,ew142,ew337,ew143],lh 6 [702,566,35,488,21,50,24,42,249,2,705,18,23,14,32,703,15,60,235,704,482,486,489,45,51,478,183,515,195,481,17,7,526,497,10,484] [0x40e00e0a00191c7,0x3c818801908200e,0xc34ce18644e0ce,0x4844804e14e3c8,0x24804e04e048148,0x28c24c28c104288,0x6c84cc68c288104,0x44c6cc4c8688448,0x3554954a14cc34c,0x20c348c70c4d5,0x1860100c3010186,0x10150002002002,0x7002145010010,0x2002002102007,0x587002002007107,0x2582007007007,0x7007347002002,0x3c3145002342007,0x433c6145046446,0x2862493c3104043,0x7432832493c6104,0x3c67464467863c3,0x34d3c32c3443783,0x48334d3d72d7497,0x105045245041104,0x558504a249045,0x2cb04104105c062,0x522cb045045045,0x289049509044044,0x434d044504289,0x2cb2983582982cb,0x542cb041041284,0x2a32df05405f]⟩
]
def nodesBlock19 : Array Node := #[
  ⟨38,7,[ew138,ew139,ew315,ew141,ew319,ew127,ew142,ew143],lh 6 [35,478,250,16,587,24,488,21,14,42,12,706,411,10,468,697,554,526,249,512,45,408,565,412,707,60,570,17,708,500,9,7,46] [0x434c14812cb441,0x10104410150130c,0x80002044101044,0x80002080002080,0x9240240009002,0x5c51851560c50d5,0x20a2051c51ca298,0x38e0c70da64334d,0x74619c6c63cf203,0x7c8787410206187,0x7220]⟩,
  ⟨38,7,[ew320,ew138,ew139,ew140,ew141,ew127,ew142,ew143],lh 5 [24,249,50,42,478,45,14,587,15,488,35,21,410,195,2,486,554,10,412,60,197,17,573,502,709,589,9,7,46] [0x280a050d43785e1,0xa196e5b9b393622,0x882028423505a6,0x390873908739081,0x621484280501487,0x15031a06c60d0c,0x3252002536aa520,0x165c212f0215e10,0xb37366d2cc2]⟩,
  ⟨38,7,[ew338,ew138,ew139,ew140,ew141,ew142,ew143],lh 6 [14,35,16,2,42,488,18,32,21,20,711,15,478,58,45,51,10,407,273,496,39,710,481,250,50,503,183,486,33,41,482,9,586,7,713,418,60,197,712,526,497,498,707,500,501] [0x31649258c315492,0x5d768410a5d768c,0x54e39634d28411a,0x9e61858e39534d,0x3df7820a46188c2,0x8030d93cf6437e5,0x191866408661a1,0x2c71c19cc2cc800,0x1c51d234d301047,0x407087485147347,0x3d31d04130934d0,0x4c82110d1448213,0x45b01b6caa11191,0x14b2dca4114544a,0x2c92c140105c70b,0x4428404924b410,0x281103101281043,0x40044284100101,0x95249a82085249,0x214503ac5205142,0x380b141941430d4,0xc920850000e18e,0x8822430c2208083,0x8001d89d740002,0x18f00f3c6183000,0xc6]⟩,
  ⟨38,7,[ew138,ew139,ew140,ew316,ew319,ew127,ew142,ew143],lh 5 [512,35,16,24,410,609,10,21,42,14,1,249,280,290,714,564,17,715,344,49,478,41,488,511,629,277,716,717,8,9,7,46] [0x6b6805800b6326b,0x2800528005282a0,0x20481091ce18405,0x405042202420424,0x1de03b0c431bc28,0x3084f8c523c1c67,0x129425084a16b22,0x9492631f8636e06,0x1d3ff27a7]⟩,
  ⟨38,7,[ew239,ew138,ew139,ew140,ew141,ew127,ew142,ew143],lh 5 [249,15,42,2,478,35,14,587,58,16,10,21,410,41,195,488,344,277,17,197,526,511,718,610,60,592,9,7,46] [0x6a5ef288a201004,0x9996358dd28b9a9,0x100420002a01c6,0x381673800738080,0x604a1094a109407,0x4b4221044c6082c,0x45c6842ec84552a,0x328691a959c28c8,0x337366d0e10]⟩,
  ⟨38,7,[ew339,ew138,ew139,ew140,ew141,ew142,ew143],lh 6 [14,496,273,21,15,35,24,249,488,2,0,720,48,33,20,410,50,41,42,38,58,10,719,482,515,183,19,45,481,9,608,7,722,418,17,197,721,498,716] [0x1d70825c71d6082,0x3cf64514b3cf647,0x84821c5142c5159,0x457410708222514,0x31d5d1456410591,0x7830d830c603763,0x1828a6007e429f,0x3da6851473cf780,0x482075071c515a,0x424101c81c1501,0x301095541401055,0x43042302083081,0x4200208b081001,0x20410d94520804b,0x10e10554514d344,0x1122d214e384544,0x2c44830c42c4103,0x1000122d2480484,0x3463861a618d38e,0xc618918d0c3356,0x6c0006806349246,0x24e0c318019b81b,0x2933892530d34c9,0x4c04d1291440013,0x28c00c30a289009,0x24a]⟩,
  ⟨38,7,[ew327,ew317,ew139,ew140,ew141,ew142,ew143],lh 6 [249,23,15,118,16,14,480,24,7,32,35,257,112,0,42,484,273,729,725,727,645,486,107,730,381,12,1,503,723,17,354,724,726,2,206,366,728] [0xf0413d43c0040,0x28924224028001b,0x259240180002009,0x92c9019009186,0xc025a2402cb01a,0x1d00f0c33d4700,0x1521554d340200,0x28104279028a00d,0x4877c1181402081,0x8012c10471d2186,0xc10441132cb4c4,0x40d8c1141522841,0x90a18604d350150,0x2ca296582182096,0x28c3022cb08c08a,0xc245108308e44e,0x208385382202383,0x1c410630c08514e,0x1c60c3184107307,0x2071921870c71d2,0x1c51d72175c5147,0x3040c411310c0c3,0x218605144204313,0x448203145105118,0xc8211145]⟩,
  ⟨38,7,[ew327,ew138,ew139,ew140,ew141,ew127,ew142,ew143],lh 5 [42,35,24,21,488,45,2,41,23,273,10,14,410,195,478,16,17,257,554,344,694,197,265,643,501,60,644,5,9,7,46] [0x79c4511401005ce,0x5b4c330db4835e7,0x3a0a22882008175,0x4a066499094a231,0x606c701c4511509,0x110200040c6002c,0xc10833109781082,0xda9433295acaa52,0x35fbabe0e73]⟩,
  ⟨38,7,[ew138,ew139,ew140,ew141,ew340,ew142,ew143],lh 6 [15,16,24,7,14,12,296,42,9,1,35,165,488,10,21,732,407,734,735,489,651,587,731,733,481,482,484,2,195,197,249,622,503] [0x40b00b2ca290010,0x8b2cc2c614540a,0x18d18b04b18c30b,0x7864c62cd346041,0x3c618e58f5167d4,0x5430c61063ce386,0x8a30c1830d5115,0x34a282280300002,0x28128034000100a,0x1c05c00130075c7,0x20800e0072071d3,0x1c41c00c01ce1c0,0x4c34d0040070c7,0x605301302342081,0x151142602091085,0x142202091085205,0xc51441420c2151,0x52049649084085,0x49209252241641,0xc1252241201052,0x440490c9244241,0x6da3db68820f520,0x1047430dc1043c8,0x2030ce1047030dd,0x383388104]⟩,
  ⟨38,7,[ew138,ew139,ew140,ew141,ew319,ew142,ew335,ew143],lh 5 [35,21,2,14,16,609,7,24,273,15,42,587,624,23,690,488,481,10,736,482,737,503,694,46] [0x594ab42d6842408,0x28da5088a2414a8,0x4800948009380c3,0x501400294002809,0x388220bce43b80a,0x2103121cc339e0c,0x882430c849c882,0x844330cccb5682,0x6198611dc22]⟩,
  ⟨38,7,[ew341,ew138,ew139,ew140,ew141,ew142,ew143],lh 6 [7,58,50,14,35,2,23,478,42,9,1,15,249,12,21,16,24,738,410,481,739,484,740,486,183,489,418,694,482,197,708,717,741] [0x1db1866871d8186,0x492648211492607,0x50d353041448219,0x2940824cd354041,0x38e70a2930824ca,0x58515538e545156,0xd60007430d5000,0x2cb1841872c7543,0x1de1c60411c4106,0x307082194187041,0x14c1e01cc08c31f,0x30e38614618e18c,0x3170d75c000c0cc,0x44b2c12c4444300,0x2c22c444410110b,0x14824810210b44b,0x4205204249105,0x1030c8008203204,0x3d009040f3c1082,0x24104504d24904f,0x343350010345341,0x8a24940340d000,0x285282242085,0x3c33ca00a28328f,0x90c92400050c3,0x140]⟩,
  ⟨38,7,[ew341,ew138,ew139,ew140,ew141,ew319,ew142,ew143],lh 5 [23,14,249,35,2,7,42,478,15,21,1,24,16,12,486,481,739,9,714,742,715,697,482,489,195,58,50,468] [0x6d9af30cc3701c0,0x94912471753d50,0x11c07380e019c25,0x2884400802100e2,0x40e7350e5268c41,0x5c106320c841868,0x652815912b4e56a,0x49135a859b6313a,0x509481284a4]⟩,
  ⟨38,7,[ew342,ew138,ew139,ew140,ew141,ew142,ew335,ew143],lh 5 [35,14,7,273,2,16,9,42,24,20,587,33,489,481,478,503,690] [0x4956801c071a86a,0x104416b0c431125,0x195231a94301c03,0x40041105c330c64,0x1c800180728007,0x218a842402080e0,0x290c1104507a088,0x31881104454a4a4,0x20882208824]⟩,
  ⟨38,7,[ew343,ew138,ew139,ew140,ew141,ew142,ew335,ew143],lh 5 [609,15,45,21,35,2,14,24,42,7,16,273,10,743,697,489,482,587,249,500,468,515,691,46] [0x11c472048158160,0x4992683c651958c,0x5800b0444000481,0x892001a4018065,0x221011a08109081,0x98dad5082840504,0x50ce211ce211c43,0x18cae71956aaa8a,0x9324c535ca5]⟩,
  ⟨38,6,[ew338,ew138,ew139,ew141,ew319,ew142,ew143],lh 5 [478,24,58,42,488,16,35,587,21,14,12,697,250,408,512,10,468,46] [0x2842d1842c01c01,0xa9415042a20882,0x20802015c000cc0,0x28ca601ce001ce0,0x30c66198c311044,0x1216b496082a1e2,0x1098a52249088]⟩,
  ⟨38,6,[ew341,ew138,ew139,ew315,ew141,ew142,ew143],lh 5 [16,35,478,488,12,24,21,14,250,42,58,411,744,554,706,723,535,697,498,10,500,526,249,512,497,468,46] [0x2288a6324310d6b,0x6b4e319a8304c03,0x30840b8ac273aa2,0x405010a210c09ef,0x2829485210a428,0x18a42148529005,0xc7d1e3138320]⟩
]
def nodesBlock20 : Array Node := #[
  ⟨38,6,[ew339,ew138,ew139,ew140,ew319,ew142,ew143],lh 5 [16,10,21,35,512,42,24,50,1,14,2,249,478,280,745,746,714,715,344,410,481,49,321,488,46] [0x300142801363160,0x4a1004004809c27,0x9087590866b6ab,0x840c37bec473844,0x194a328c65184e3,0x506314994250ae1,0x49c0a5248542]⟩,
  ⟨38,6,[ew341,ew138,ew139,ew140,ew316,ew142,ew143],lh 5 [10,24,21,512,35,58,1,410,42,290,249,265,488,50,344,280,745,746,714,468,16,262,8,5,49,747,478,321,629,46,14] [0x630205aea050129,0x73ae000ac03340d,0x10f43c8c617bf0a,0x21e5209231d8e10,0x9488411073a0e4,0x1182528782288a1,0x5ee8a8635273]⟩,
  ⟨38,6,[ew138,ew139,ew140,ew141,ew344,ew142,ew143],lh 5 [24,16,42,7,35,23,410,21,14,609,2,587,10,748,482,488,481,484,48,183,0] [0x585214816020882,0x2a065394aa2a525,0x118c20882400804,0x800d218c4118c2,0xd005000703dc0,0x8d015042763201,0x1a068a0e6391e27]⟩
]
def nodesGet (i : Nat) : Option Node :=
  if i < 160 then
    if i < 80 then
      if i < 32 then
        if i < 16 then
          nodesBlock0[(i-0)]?
        else
          nodesBlock1[(i-16)]?
      else
        if i < 48 then
          nodesBlock2[(i-32)]?
        else
          if i < 64 then
            nodesBlock3[(i-48)]?
          else
            nodesBlock4[(i-64)]?
    else
      if i < 112 then
        if i < 96 then
          nodesBlock5[(i-80)]?
        else
          nodesBlock6[(i-96)]?
      else
        if i < 128 then
          nodesBlock7[(i-112)]?
        else
          if i < 144 then
            nodesBlock8[(i-128)]?
          else
            nodesBlock9[(i-144)]?
  else
    if i < 240 then
      if i < 192 then
        if i < 176 then
          nodesBlock10[(i-160)]?
        else
          nodesBlock11[(i-176)]?
      else
        if i < 208 then
          nodesBlock12[(i-192)]?
        else
          if i < 224 then
            nodesBlock13[(i-208)]?
          else
            nodesBlock14[(i-224)]?
    else
      if i < 288 then
        if i < 256 then
          nodesBlock15[(i-240)]?
        else
          if i < 272 then
            nodesBlock16[(i-256)]?
          else
            nodesBlock17[(i-272)]?
      else
        if i < 304 then
          nodesBlock18[(i-288)]?
        else
          if i < 320 then
            nodesBlock19[(i-304)]?
          else
            nodesBlock20[(i-320)]?
def fastViews : QFast.Table View := ⟨39,viewsGet⟩
def fastNodes : QFast.Table Node := ⟨323,nodesGet⟩
end SignedProjection

namespace SignedProjection
end SignedProjection

namespace SignedProjection
def aliasMap0 : Array Nat := #[0,0,0,0,0,0,10,0,0,0,0,0,0,0,14,0,0,0,0,0,0,0,26,0,0,0,0,0,0,0,30,0,0,0,0,0,0,0,42,0,0,0,0,0,0,0,46,0,0,0,0,0,0,0,58,0,0,0,0,0,0,0,62,0]
def aliasMap1 : Array Nat := #[0,0,0,0,0,0,18,0,0,0,0,0,0,0,22,0,0,0,0,0,0,0,26,0,0,0,0,0,0,0,30,0,0,0,0,0,0,0,50,0,0,0,0,0,0,0,54,0,0,0,0,0,0,0,58,0,0,0,0,0,0,0,62,0]
def aliasMap2 : Array Nat := #[0,0,0,0,0,0,34,0,0,0,0,0,0,0,38,0,0,0,0,0,0,0,42,0,0,0,0,0,0,0,46,0,0,0,0,0,0,0,50,0,0,0,0,0,0,0,54,0,0,0,0,0,0,0,58,0,0,0,0,0,0,0,62,0]
def aliasMap3 : Array Nat := #[0,0,0,0,0,0,34,0,0,0,0,0,0,0,35,0,0,0,0,0,0,0,42,0,0,0,0,0,0,0,43,0,0,0,0,0,0,0,50,0,0,0,0,0,0,0,51,0,0,0,0,0,0,0,58,0,0,0,0,0,0,0,59,0]
def aliasMap4 : Array Nat := #[0,0,0,0,0,0,34,0,0,0,0,0,0,0,35,0,0,0,0,0,0,0,38,0,0,0,0,0,0,0,39,0,0,0,0,0,0,0,50,0,0,0,0,0,0,0,51,0,0,0,0,0,0,0,54,0,0,0,0,0,0,0,55,0]
def aliasMap5 : Array Nat := #[0,0,0,0,0,0,34,0,0,0,0,0,0,0,35,0,0,0,0,0,0,0,38,0,0,0,0,0,0,0,39,0,0,0,0,0,0,0,42,0,0,0,0,0,0,0,43,0,0,0,0,0,0,0,46,0,0,0,0,0,0,0,47,0]
def aliasMap6 : Array Nat := #[0,1,0,0,0,0,0,0,0,11,10,0,0,0,0,0,0,17,16,0,0,0,0,0,0,27,26,0,0,0,0,0,0,33,32,0,0,0,0,0,0,43,42,0,0,0,0,0,0,49,48,0,0,0,0,0,0,59,58,0,0,0,0,0]
def aliasMap7 : Array Nat := #[0,1,0,0,0,0,0,0,0,37,36,0,0,0,0,0,0,3,2,0,0,0,0,0,0,39,38,0,0,0,0,0,0,17,16,0,0,0,0,0,0,53,52,0,0,0,0,0,0,19,18,0,0,0,0,0,0,55,54,0,0,0,0,0]
def aliasMap8 : Array Nat := #[0,1,0,0,0,0,0,0,0,41,40,0,0,0,0,0,0,3,2,0,0,0,0,0,0,43,42,0,0,0,0,0,0,17,16,0,0,0,0,0,0,57,56,0,0,0,0,0,0,19,18,0,0,0,0,0,0,59,58,0,0,0,0,0]
def aliasMap9 : Array Nat := #[0,0,63,0,0,0,62,0,0,0,59,0,0,0,58,0,0,0,55,0,0,0,54,0,0,0,51,0,0,0,50,0,0,0,47,0,0,0,46,0,0,0,43,0,0,0,42,0,0,0,39,0,0,0,38,0,0,0,35,0,0,0,34,0]
def aliasMap10 : Array Nat := #[0,0,16,17,0,0,18,19,0,0,24,25,0,0,26,27,0,0,48,49,0,0,50,51,0,0,56,57,0,0,58,59,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
def aliasMap11 : Array Nat := #[0,0,16,17,0,0,18,19,0,0,20,21,0,0,22,23,0,0,48,49,0,0,50,51,0,0,52,53,0,0,54,55,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
def aliasMap12 : Array Nat := #[0,0,16,17,0,0,18,19,0,0,20,21,0,0,22,23,0,0,24,25,0,0,26,27,0,0,28,29,0,0,30,31,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
def aliasMap13 : Array Nat := #[0,0,4,14,0,0,1,11,0,0,20,30,0,0,17,27,0,0,36,46,0,0,33,43,0,0,52,62,0,0,49,59,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
def aliasMap14 : Array Nat := #[0,0,0,17,0,0,6,23,0,0,8,25,0,0,14,31,0,0,32,49,0,0,38,55,0,0,40,57,0,0,46,63,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
def aliasMap15 : Array Nat := #[0,0,2,1,0,0,0,0,0,0,6,5,0,0,0,0,0,0,10,9,0,0,0,0,0,0,14,13,0,0,0,0,0,0,34,33,0,0,0,0,0,0,38,37,0,0,0,0,0,0,42,41,0,0,0,0,0,0,46,45,0,0,0,0]
def aliasMap16 : Array Nat := #[0,0,61,0,0,0,62,0,0,0,57,0,0,0,58,0,0,0,53,0,0,0,54,0,0,0,49,0,0,0,50,0,0,0,29,0,0,0,30,0,0,0,25,0,0,0,26,0,0,0,21,0,0,0,22,0,0,0,17,0,0,0,18,0]
def aliasMap17 : Array Nat := #[0,0,0,0,4,0,20,0,0,0,0,0,1,0,17,0,0,0,0,0,6,0,22,0,0,0,0,0,3,0,19,0,0,0,0,0,36,0,52,0,0,0,0,0,33,0,49,0,0,0,0,0,38,0,54,0,0,0,0,0,35,0,51,0]
def aliasMap18 : Array Nat := #[0,62,59,0,0,0,0,0,0,60,57,0,0,0,0,0,0,54,51,0,0,0,0,0,0,52,49,0,0,0,0,0,0,30,27,0,0,0,0,0,0,28,25,0,0,0,0,0,0,22,19,0,0,0,0,0,0,20,17,0,0,0,0,0]
def aliasMap19 : Array Nat := #[0,1,4,0,0,0,0,0,0,9,12,0,0,0,0,0,0,3,6,0,0,0,0,0,0,11,14,0,0,0,0,0,0,17,20,0,0,0,0,0,0,25,28,0,0,0,0,0,0,19,22,0,0,0,0,0,0,27,30,0,0,0,0,0]
def aliasMap20 : Array Nat := #[0,0,0,0,8,0,24,0,0,0,0,0,1,0,17,0,0,0,0,0,10,0,26,0,0,0,0,0,3,0,19,0,0,0,0,0,40,0,56,0,0,0,0,0,33,0,49,0,0,0,0,0,42,0,58,0,0,0,0,0,35,0,51,0]
def aliasMap21 : Array Nat := #[0,62,55,0,0,0,0,0,0,60,53,0,0,0,0,0,0,58,51,0,0,0,0,0,0,56,49,0,0,0,0,0,0,30,23,0,0,0,0,0,0,28,21,0,0,0,0,0,0,26,19,0,0,0,0,0,0,24,17,0,0,0,0,0]
def aliasMap22 : Array Nat := #[0,1,32,0,0,0,0,0,0,9,40,0,0,0,0,0,0,3,34,0,0,0,0,0,0,11,42,0,0,0,0,0,0,17,48,0,0,0,0,0,0,25,56,0,0,0,0,0,0,19,50,0,0,0,0,0,0,27,58,0,0,0,0,0]
def aliasMap23 : Array Nat := #[0,1,32,0,0,0,0,0,0,5,36,0,0,0,0,0,0,3,34,0,0,0,0,0,0,7,38,0,0,0,0,0,0,17,48,0,0,0,0,0,0,21,52,0,0,0,0,0,0,19,50,0,0,0,0,0,0,23,54,0,0,0,0,0]
def aliasMap24 : Array Nat := #[0,62,31,0,0,0,0,0,0,60,29,0,0,0,0,0,0,58,27,0,0,0,0,0,0,56,25,0,0,0,0,0,0,54,23,0,0,0,0,0,0,52,21,0,0,0,0,0,0,50,19,0,0,0,0,0,0,48,17,0,0,0,0,0]
def aliasMap25 : Array Nat := #[0,1,2,3,0,0,0,0,4,5,6,7,0,0,0,0,16,17,18,19,0,0,0,0,20,21,22,23,0,0,0,0,32,33,34,35,0,0,0,0,36,37,38,39,0,0,0,0,48,49,50,51,0,0,0,0,52,53,54,55,0,0,0,0]
def aliasMap26 : Array Nat := #[0,1,0,3,8,0,10,0,0,5,0,7,12,0,14,0,0,17,0,19,24,0,26,0,0,21,0,23,28,0,30,0,0,33,0,35,40,0,42,0,0,37,0,39,44,0,46,0,0,49,0,51,56,0,58,0,0,53,0,55,60,0,62,0]
def rootAliases : QFast.AliasTable
  | 1 => some (0, aliasMap0)
  | 2 => some (0, aliasMap1)
  | 3 => some (0, aliasMap2)
  | 4 => some (0, aliasMap3)
  | 5 => some (0, aliasMap4)
  | 6 => some (0, aliasMap5)
  | 8 => some (7, aliasMap6)
  | 9 => some (7, aliasMap7)
  | 10 => some (7, aliasMap8)
  | 15 => some (11, aliasMap9)
  | 16 => some (14, aliasMap10)
  | 17 => some (14, aliasMap11)
  | 18 => some (14, aliasMap12)
  | 19 => some (14, aliasMap13)
  | 21 => some (14, aliasMap14)
  | 22 => some (13, aliasMap15)
  | 23 => some (11, aliasMap16)
  | 24 => some (12, aliasMap17)
  | 25 => some (7, aliasMap18)
  | 26 => some (7, aliasMap19)
  | 27 => some (12, aliasMap20)
  | 28 => some (7, aliasMap21)
  | 29 => some (7, aliasMap22)
  | 30 => some (7, aliasMap23)
  | 31 => some (7, aliasMap24)
  | 34 => some (33, aliasMap25)
  | 37 => some (36, aliasMap26)
  | _ => none
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockRoots_0 : QFast.passBlock (QFast.symCheckRoot rootAliases fastViews fastNodes) 0 26 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockRoots_26 : QFast.passBlock (QFast.symCheckRoot rootAliases fastViews fastNodes) 26 13 = true := by decide +kernel
theorem joinRoots_0_0 : QFast.passBlock (QFast.symCheckRoot rootAliases fastViews fastNodes) 0 39 = true :=
  @QFast.merge_blocks (QFast.symCheckRoot rootAliases fastViews fastNodes) 0 26 13 blockRoots_0 blockRoots_26
theorem certifiedRoots : QFast.passBlock (QFast.symCheckRoot rootAliases fastViews fastNodes) 0 39 = true := joinRoots_0_0
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockNodes_0 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 0 55 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockNodes_55 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 55 64 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockNodes_119 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 119 10 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockNodes_129 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 129 14 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockNodes_143 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 143 26 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockNodes_169 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 169 41 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockNodes_210 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 210 27 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockNodes_237 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 237 26 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockNodes_263 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 263 7 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockNodes_270 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 270 7 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockNodes_277 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 277 7 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockNodes_284 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 284 7 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockNodes_291 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 291 7 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockNodes_298 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 298 8 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockNodes_306 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 306 17 = true := by decide +kernel
theorem joinNodes_0_0 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 0 119 = true :=
  @QFast.merge_blocks (QFast.checkNodeAt fastViews fastNodes) 0 55 64 blockNodes_0 blockNodes_55
theorem joinNodes_0_119 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 119 24 = true :=
  @QFast.merge_blocks (QFast.checkNodeAt fastViews fastNodes) 119 10 14 blockNodes_119 blockNodes_129
theorem joinNodes_0_143 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 143 67 = true :=
  @QFast.merge_blocks (QFast.checkNodeAt fastViews fastNodes) 143 26 41 blockNodes_143 blockNodes_169
theorem joinNodes_0_210 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 210 53 = true :=
  @QFast.merge_blocks (QFast.checkNodeAt fastViews fastNodes) 210 27 26 blockNodes_210 blockNodes_237
theorem joinNodes_0_263 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 263 14 = true :=
  @QFast.merge_blocks (QFast.checkNodeAt fastViews fastNodes) 263 7 7 blockNodes_263 blockNodes_270
theorem joinNodes_0_277 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 277 14 = true :=
  @QFast.merge_blocks (QFast.checkNodeAt fastViews fastNodes) 277 7 7 blockNodes_277 blockNodes_284
theorem joinNodes_0_291 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 291 15 = true :=
  @QFast.merge_blocks (QFast.checkNodeAt fastViews fastNodes) 291 7 8 blockNodes_291 blockNodes_298
theorem joinNodes_1_0 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 0 143 = true :=
  @QFast.merge_blocks (QFast.checkNodeAt fastViews fastNodes) 0 119 24 joinNodes_0_0 joinNodes_0_119
theorem joinNodes_1_143 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 143 120 = true :=
  @QFast.merge_blocks (QFast.checkNodeAt fastViews fastNodes) 143 67 53 joinNodes_0_143 joinNodes_0_210
theorem joinNodes_1_263 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 263 28 = true :=
  @QFast.merge_blocks (QFast.checkNodeAt fastViews fastNodes) 263 14 14 joinNodes_0_263 joinNodes_0_277
theorem joinNodes_1_291 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 291 32 = true :=
  @QFast.merge_blocks (QFast.checkNodeAt fastViews fastNodes) 291 15 17 joinNodes_0_291 blockNodes_306
theorem joinNodes_2_0 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 0 263 = true :=
  @QFast.merge_blocks (QFast.checkNodeAt fastViews fastNodes) 0 143 120 joinNodes_1_0 joinNodes_1_143
theorem joinNodes_2_263 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 263 60 = true :=
  @QFast.merge_blocks (QFast.checkNodeAt fastViews fastNodes) 263 28 32 joinNodes_1_263 joinNodes_1_291
theorem joinNodes_3_0 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 0 323 = true :=
  @QFast.merge_blocks (QFast.checkNodeAt fastViews fastNodes) 0 263 60 joinNodes_2_0 joinNodes_2_263
theorem certifiedNodes : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 0 323 = true := joinNodes_3_0
end SignedProjection

namespace SignedProjection
def bMatches (z : Option View) : Bool :=
  match z with
  | none => false
  | some v => vg v == (0xeeeaeaa0eaa8aaa0 : Word) && vk v == 10 && (vs v).toFinset == Direct64.cols.toFinset

theorem rootNegative : ¬ CoreSigned.build signedOps (0xeeeaeaa0eaa8aaa0 : BitVec 64) 10 Direct64.cols.toFinset := by
  have shape : bMatches (QFast.get fastViews 38) = true := by decide +kernel
  cases ev : QFast.get fastViews 38 with
  | none => simp [ev, bMatches] at shape
  | some v =>
    have valid := QFast.symCertified rootAliases fastViews fastNodes certifiedRoots certifiedNodes ev
    simp only [ev,bMatches,Bool.and_eq_true,beq_iff_eq] at shape
    change ¬ CoreSigned.build signedOps (vg v) (vk v) (vs v).toFinset at valid
    rwa [shape.1.1,shape.1.2,shape.2] at valid
end SignedProjection

end PEqualNP.Outside.L_meta_45796_aux

open PEqualNP.Outside.L_meta_45796_aux in
theorem PEqualNP.Outside.L_meta_45796 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4008372896 * 2 ^ 32 + 3936922272) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4008372896 * 2 ^ 32 + 3936922272) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  LowerSymSix.finish SignedProjection.rootNegative
