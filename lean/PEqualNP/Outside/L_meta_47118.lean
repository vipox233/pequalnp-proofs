import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_47118_aux
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
  ⟨[⟨.and,[0,1]⟩, ⟨.or,[6,3]⟩, ⟨.and,[7,2]⟩, ⟨.or,[8,0]⟩, ⟨.or,[8,4]⟩,
    ⟨.and,[10,9]⟩, ⟨.and,[10,1]⟩, ⟨.or,[12,0]⟩, ⟨.or,[7,2]⟩, ⟨.and,[14,5]⟩,
    ⟨.or,[15,11]⟩, ⟨.and,[16,13]⟩],17⟩

theorem size : witness.size = 12 := rfl

theorem monotone : Monotone2 witness := by
  simp [Monotone2,witness]

set_option maxRecDepth 16000 in
theorem correct : ∀ x : Fin 6 → Bool, witness.eval (List.ofFn x) =
    Nat.testBit (4008372904 * 2 ^ 32 + 3937067136) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  decide +kernel

end LowerSymSix

namespace Direct64
open PEqualNP.CircuitLowerBounds SignedProjection
abbrev W := BitVec 64
abbrev basicOps (a b : W) := signedOps a b
abbrev goal : W := ~~~0xeeeaeaa8eaaae080
open CoreSigned (build)
def tableB (x : Fin 6 → Bool) :=
  Nat.testBit (4008372904 * 2 ^ 32 + 3937067136) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
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

theorem low (reject : ¬ build basicOps (0xeeeaeaa8eaaae080 : W) 10 cols.toFinset)
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
    (reject : ¬ CoreSigned.build SignedProjection.signedOps (0xeeeaeaa8eaaae080 : BitVec 64) 10 Direct64.cols.toFinset) :
∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4008372904 * 2 ^ 32 + 3937067136) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4008372904 * 2 ^ 32 + 3937067136) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
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
def ew0 : Word := 0x4040000040400000
def ew1 : Word := 0x4400000044000000
def ew2 : Word := 0x4444000000000000
def ew3 : Word := 0x4040404000000000
def ew4 : Word := 0x4400440000000000
def ew5 : Word := 0x202000002020
def ew6 : Word := 0x220000002200
def ew7 : Word := 0x222200000000
def ew8 : Word := 0x8800000088
def ew9 : Word := 0xa0000000a0
def ew10 : Word := 0xaa00000000
def ew11 : Word := 0x800080008000800
def ew12 : Word := 0xc0000000c000000
def ew13 : Word := 0xc000c0000000000
def ew14 : Word := 0x88008800880088
def ew15 : Word := 0xc000c000c000c0
def ew16 : Word := 0xcc000000cc0000
def ew17 : Word := 0xcc00cc00000000
def ew18 : Word := 0x8800880088008800
def ew19 : Word := 0x8040804080408040
def ew20 : Word := 0x8844000088440000
def ew21 : Word := 0x8844884400000000
def ew22 : Word := 0x4040404040404040
def ew23 : Word := 0x4400440044004400
def ew24 : Word := 0x4444000044440000
def ew25 : Word := 0x4444444400000000
def ew26 : Word := 0x808020208080202
def ew27 : Word := 0xc0c00000c0c0000
def ew28 : Word := 0xc0003000c000300
def ew29 : Word := 0xc0c030300000000
def ew30 : Word := 0x8080202080802020
def ew31 : Word := 0xc0c00000c0c00000
def ew32 : Word := 0xc0003000c0003000
def ew33 : Word := 0xc0c0303000000000
def ew34 : Word := 0x88002200880022
def ew35 : Word := 0xc0003000c00030
def ew36 : Word := 0xcc003300000000
def ew37 : Word := 0x8800220088002200
def ew38 : Word := 0xcc000000cc000000
def ew39 : Word := 0xcc00330000000000
def ew40 : Word := 0xa00000a0a00000a
def ew41 : Word := 0xc00000c0c00000c
def ew42 : Word := 0xf0000000f000000
def ew43 : Word := 0xf00000f00000000
def ew44 : Word := 0x2020202020202020
def ew45 : Word := 0x2200220022002200
def ew46 : Word := 0x2222000022220000
def ew47 : Word := 0x2222222200000000
def ew48 : Word := 0x888800008888
def ew49 : Word := 0xc0c00000c0c0
def ew50 : Word := 0xcc000000cc00
def ew51 : Word := 0xcccc00000000
def ew52 : Word := 0x88888888
def ew53 : Word := 0xc0c0c0c0
def ew54 : Word := 0xcc00cc00
def ew55 : Word := 0xcccc0000
def ew56 : Word := 0xa0a0a0a00000000
def ew57 : Word := 0xc0c0c0c00000000
def ew58 : Word := 0xf000f0000000000
def ew59 : Word := 0xf0f000000000000
def ew60 : Word := 0xa000a000a000a0
def ew61 : Word := 0xf0000000f00000
def ew62 : Word := 0xf000f000000000
def ew63 : Word := 0xaa00aa00000000
def ew64 : Word := 0xff000000000000
def ew65 : Word := 0xaa000000aa00
def ew66 : Word := 0xf0000000f000
def ew67 : Word := 0xff0000000000
def ew68 : Word := 0xaa00aa00
def ew69 : Word := 0xf000f000
def ew70 : Word := 0xff000000
def ew71 : Word := 0xaaaa00000000
def ew72 : Word := 0xf0f000000000
def ew73 : Word := 0x8484000084840000
def ew74 : Word := 0x8400210084002100
def ew75 : Word := 0x8484212100000000
def ew76 : Word := 0x4040101040401010
def ew77 : Word := 0x4848000048480000
def ew78 : Word := 0x4800120048001200
def ew79 : Word := 0x4848121200000000
def ew80 : Word := 0x8040201080402010
def ew81 : Word := 0x8844221100000000
def ew82 : Word := 0x4400110044001100
def ew83 : Word := 0x4488000044880000
def ew84 : Word := 0x4080102040801020
def ew85 : Word := 0x4488112200000000
def ew86 : Word := 0x404040404040404
def ew87 : Word := 0x600060006000600
def ew88 : Word := 0x606000006060000
def ew89 : Word := 0x606060600000000
def ew90 : Word := 0x44004400440044
def ew91 : Word := 0x60006000600060
def ew92 : Word := 0x66000000660000
def ew93 : Word := 0x66006600000000
def ew94 : Word := 0x6000600060006000
def ew95 : Word := 0x6600000066000000
def ew96 : Word := 0x6600660000000000
def ew97 : Word := 0x6060606000000000
def ew98 : Word := 0x6666000000000000
def ew99 : Word := 0x4800480048004800
def ew100 : Word := 0x4848484800000000
def ew101 : Word := 0x505000005050
def ew102 : Word := 0x484800004848
def ew103 : Word := 0x5a0000005a00
def ew104 : Word := 0x5a5a00000000
def ew105 : Word := 0x4080408040804080
def ew106 : Word := 0x4488448800000000
def ew107 : Word := 0x500050005000500
def ew108 : Word := 0x408040804080408
def ew109 : Word := 0x50a0000050a0000
def ew110 : Word := 0x50a050a00000000
def ew111 : Word := 0x505000005050000
def ew112 : Word := 0x404080804040808
def ew113 : Word := 0x5000a0005000a00
def ew114 : Word := 0x5050a0a00000000
def ew115 : Word := 0x2800280028002800
def ew116 : Word := 0x3000300030003000
def ew117 : Word := 0x3c0000003c000000
def ew118 : Word := 0x3c003c0000000000
def ew119 : Word := 0x222200008888
def ew120 : Word := 0x333300000000
def ew121 : Word := 0x30300000c0c0
def ew122 : Word := 0x33000000cc00
def ew123 : Word := 0x8888222288882222
def ew124 : Word := 0xcccc0000cccc0000
def ew125 : Word := 0xc0c03030c0c03030
def ew126 : Word := 0xcc003300cc003300
def ew127 : Word := 0xcccc333300000000
def ew128 : Word := 0x8888888888888888
def ew129 : Word := 0xc0c0c0c0c0c0c0c0
def ew130 : Word := 0xcc00cc00cc00cc00
def ew131 : Word := 0xcccccccc00000000
def ew132 : Word := 0xa0a0a0a0a0a0a0a
def ew133 : Word := 0xc0c0c0c0c0c0c0c
def ew134 : Word := 0xf000f000f000f00
def ew135 : Word := 0xf0f00000f0f0000
def ew136 : Word := 0xf0f0f0f00000000
def ew137 : Word := 0xa0a0a0a0a0a0a0a0
def ew138 : Word := 0xf000f000f000f000
def ew139 : Word := 0xf0f00000f0f00000
def ew140 : Word := 0xf0f0f0f000000000
def ew141 : Word := 0xaa00aa00aa00aa
def ew142 : Word := 0xcc00cc00cc00cc
def ew143 : Word := 0xf000f000f000f0
def ew144 : Word := 0xff000000ff0000
def ew145 : Word := 0xff00ff00000000
def ew146 : Word := 0xaa00aa00aa00aa00
def ew147 : Word := 0xff000000ff000000
def ew148 : Word := 0xff00ff0000000000
def ew149 : Word := 0xaaaa0000aaaa
def ew150 : Word := 0xcccc0000cccc
def ew151 : Word := 0xf0f00000f0f0
def ew152 : Word := 0xff000000ff00
def ew153 : Word := 0xffff00000000
def ew154 : Word := 0xaaaaaaaa
def ew155 : Word := 0xcccccccc
def ew156 : Word := 0xf0f0f0f0
def ew157 : Word := 0xff00ff00
def ew158 : Word := 0xffff0000
def ew159 : Word := 0xaaaaaaaa00000000
def ew160 : Word := 0xffff000000000000
def ew161 : Word := 0x4444444444444444
def ew162 : Word := 0x6060606060606060
def ew163 : Word := 0x6600660066006600
def ew164 : Word := 0x6666000066660000
def ew165 : Word := 0x6666666600000000
def ew166 : Word := 0x5555000055550000
def ew167 : Word := 0x4444888844448888
def ew168 : Word := 0x5050a0a05050a0a0
def ew169 : Word := 0x5500aa005500aa00
def ew170 : Word := 0x5555aaaa00000000
def ew171 : Word := 0xaaaaaaaaaaaaaaaa
def ew172 : Word := 0xcccccccccccccccc
def ew173 : Word := 0xf0f0f0f0f0f0f0f0
def ew174 : Word := 0xff00ff00ff00ff00
def ew175 : Word := 0xffff0000ffff0000
def ew176 : Word := 0xffffffff00000000
def ew177 : Word := 0x80008000800080
def ew178 : Word := 0xc800c800c800c8
def ew179 : Word := 0x8000800080008
def ew180 : Word := 0x40004000400040
def ew181 : Word := 0x88000000880000
def ew182 : Word := 0xcc008800cc0088
def ew183 : Word := 0x44000000440000
def ew184 : Word := 0x88008800000000
def ew185 : Word := 0xcc00cc00880088
def ew186 : Word := 0x880088
def ew187 : Word := 0x44004400000000
def ew188 : Word := 0xc0000000c00000
def ew189 : Word := 0xcc00c000cc00c0
def ew190 : Word := 0xc0000000c0
def ew191 : Word := 0xc0000000c0000
def ew192 : Word := 0xc000c000000000
def ew193 : Word := 0xcc00cc00c000c0
def ew194 : Word := 0xc000c0
def ew195 : Word := 0xc000c00000000
def ew196 : Word := 0xcc000000000000
def ew197 : Word := 0xcc00cc00cc0000
def ew198 : Word := 0xcc0000
def ew199 : Word := 0xcc00000000
def ew200 : Word := 0xcc008000cc0080
def ew201 : Word := 0x4c0000004c0000
def ew202 : Word := 0xcc00cc00800080
def ew203 : Word := 0x4c004c00000000
def ew204 : Word := 0xc8000000c80000
def ew205 : Word := 0xc8000000c8
def ew206 : Word := 0xc800c800000000
def ew207 : Word := 0xc800c8
def ew208 : Word := 0xc800c000c800c0
def ew209 : Word := 0x4000c0004000c0
def ew210 : Word := 0xcc00cc00880000
def ew211 : Word := 0x4400cc00000000
def ew212 : Word := 0xc0008000c00080
def ew213 : Word := 0xc0008000c0008
def ew214 : Word := 0xcc008800000000
def ew215 : Word := 0xcc0088
def ew216 : Word := 0xc800c800c000c0
def ew217 : Word := 0x40004000c000c0
def ew218 : Word := 0xcc008800cc0000
def ew219 : Word := 0x44000000cc0000
def ew220 : Word := 0xc000c000800080
def ew221 : Word := 0xc000c00080008
def ew222 : Word := 0xcc000000880000
def ew223 : Word := 0xcc00000088
def ew224 : Word := 0xcc00cc000000c0
def ew225 : Word := 0xcc000c00000000
def ew226 : Word := 0xcc00cc000c0000
def ew227 : Word := 0xc000cc00000000
def ew228 : Word := 0xcc000000cc00c0
def ew229 : Word := 0xcc0000000c0000
def ew230 : Word := 0xcc000c00cc0000
def ew231 : Word := 0xc0000000cc0000
def ew232 : Word := 0xc000c000cc00c0
def ew233 : Word := 0xc000c0000000c0
def ew234 : Word := 0xc000cc00c000c0
def ew235 : Word := 0xc0000000c000c0
def ew236 : Word := 0x6000600000000000
def ew237 : Word := 0x6660666000000000
def ew238 : Word := 0x60006000000000
def ew239 : Word := 0x600060000000000
def ew240 : Word := 0x6060000000000000
def ew241 : Word := 0x6666606000000000
def ew242 : Word := 0x606000000000
def ew243 : Word := 0x606000000000000
def ew244 : Word := 0x6600000000000000
def ew245 : Word := 0x6666660000000000
def ew246 : Word := 0x660000000000
def ew247 : Word := 0x66000000000000
def ew248 : Word := 0x444044400000000
def ew249 : Word := 0x6666600000000000
def ew250 : Word := 0x666000000000000
def ew251 : Word := 0x404444400000000
def ew252 : Word := 0x6660660000000000
def ew253 : Word := 0x600660000000000
def ew254 : Word := 0x44444400000000
def ew255 : Word := 0x6660606000000000
def ew256 : Word := 0x60606000000000
def ew257 : Word := 0x4000400040004000
def ew258 : Word := 0x4840484048404840
def ew259 : Word := 0x4848404048484040
def ew260 : Word := 0x404000004040
def ew261 : Word := 0x808000008080000
def ew262 : Word := 0x4848484840404040
def ew263 : Word := 0x40404040
def ew264 : Word := 0x808080800000000
def ew265 : Word := 0x4800000048000000
def ew266 : Word := 0x4848480048484800
def ew267 : Word := 0x480000004800
def ew268 : Word := 0x48000000480000
def ew269 : Word := 0x4800480000000000
def ew270 : Word := 0x4848484848004800
def ew271 : Word := 0x48004800
def ew272 : Word := 0x48004800000000
def ew273 : Word := 0x4848000000000000
def ew274 : Word := 0x4848484848480000
def ew275 : Word := 0x48480000
def ew276 : Word := 0x484800000000
def ew277 : Word := 0x4848400048484000
def ew278 : Word := 0x848000008480000
def ew279 : Word := 0x4848484840004000
def ew280 : Word := 0x848084800000000
def ew281 : Word := 0x4800400048004000
def ew282 : Word := 0x48004000480040
def ew283 : Word := 0x4848484800004040
def ew284 : Word := 0x4848080800000000
def ew285 : Word := 0x4808480048084800
def ew286 : Word := 0x4000480040004800
def ew287 : Word := 0x4848484808080000
def ew288 : Word := 0x4040484800000000
def ew289 : Word := 0x4800480040004000
def ew290 : Word := 0x48004800400040
def ew291 : Word := 0x4848000048484040
def ew292 : Word := 0x4848000008080000
def ew293 : Word := 0x4808480848004800
def ew294 : Word := 0x4000400048004800
def ew295 : Word := 0x4848080848480000
def ew296 : Word := 0x4040000048480000
def ew297 : Word := 0x4840404048404040
def ew298 : Word := 0x40404000404040
def ew299 : Word := 0x4848484848000000
def ew300 : Word := 0x48484800000000
def ew301 : Word := 0x4840484040404040
def ew302 : Word := 0x40004040404040
def ew303 : Word := 0x4848480048480000
def ew304 : Word := 0x48000048480000
def ew305 : Word := 0x4848404040404040
def ew306 : Word := 0x404040404040
def ew307 : Word := 0x4848480048004800
def ew308 : Word := 0x480048004800
def ew309 : Word := 0x2800000028000000
def ew310 : Word := 0x3c0028003c002800
def ew311 : Word := 0x280000002800
def ew312 : Word := 0x1400000014000000
def ew313 : Word := 0x2800280000000000
def ew314 : Word := 0x3c003c0028002800
def ew315 : Word := 0x28002800
def ew316 : Word := 0x1400140000000000
def ew317 : Word := 0x3c00000000000000
def ew318 : Word := 0x3c003c003c000000
def ew319 : Word := 0x3c000000
def ew320 : Word := 0x3c0000000000
def ew321 : Word := 0x3800300038003000
def ew322 : Word := 0x3c003c0028000000
def ew323 : Word := 0x14003c0000000000
def ew324 : Word := 0xc0008000c000800
def ew325 : Word := 0x3c00280000000000
def ew326 : Word := 0x3c002800
def ew327 : Word := 0x3800380030003000
def ew328 : Word := 0x3c0028003c000000
def ew329 : Word := 0x140000003c000000
def ew330 : Word := 0xc000c0008000800
def ew331 : Word := 0x3c00000028000000
def ew332 : Word := 0x3c0000002800
def ew333 : Word := 0x300030003c003000
def ew334 : Word := 0x30003c0030003000
def ew335 : Word := 0x330000000000
def ew336 : Word := 0xcc00
def ew337 : Word := 0xcc88cc88cc88cc88
def ew338 : Word := 0xcccc000000000000
def ew339 : Word := 0xccccc0c0c0c0c0c0
def ew340 : Word := 0x808080808080808
def ew341 : Word := 0xa000a000a000a00
def ew342 : Word := 0xa0a00000a0a0000
def ew343 : Word := 0xf0f0a0a0f0f0a0a
def ew344 : Word := 0xa0a00000a0a
def ew345 : Word := 0xc0c00000c0c
def ew346 : Word := 0xf0000000f00
def ew347 : Word := 0x700070007000700
def ew348 : Word := 0xf0f08080f0f0808
def ew349 : Word := 0x707000007070000
def ew350 : Word := 0x404000004040000
def ew351 : Word := 0xf0f04040f0f0404
def ew352 : Word := 0xb0b00000b0b0000
def ew353 : Word := 0x40c040c040c040c
def ew354 : Word := 0xf0f0a000f0f0a00
def ew355 : Word := 0x50f0000050f0000
def ew356 : Word := 0x500000005000000
def ew357 : Word := 0xf0f05000f0f0500
def ew358 : Word := 0xa0f00000a0f0000
def ew359 : Word := 0x4040c0c04040c0c
def ew360 : Word := 0x5000f0005000f00
def ew361 : Word := 0x5050f0f00000000
def ew362 : Word := 0xc0c08080c0c0808
def ew363 : Word := 0xf000a000f000a00
def ew364 : Word := 0xf0f0a0a00000000
def ew365 : Word := 0xc0c04040c0c0404
def ew366 : Word := 0xf0005000f000500
def ew367 : Word := 0x8080c0c08080c0c
def ew368 : Word := 0xa000f000a000f00
def ew369 : Word := 0xe0e0a0a0e0e0a0a
def ew370 : Word := 0x2020a0a02020a0a
def ew371 : Word := 0xa0a0e0e0a0a0e0e
def ew372 : Word := 0xa0a02020a0a0202
def ew373 : Word := 0xf0003000f000300
def ew374 : Word := 0xf0a0a0a0f0a0a0a
def ew375 : Word := 0xa0a0a000a0a0a
def ew376 : Word := 0xa0a0f0a0a0a0f0a
def ew377 : Word := 0xa0a000a0a0a000a
def ew378 : Word := 0xc0c000c0c0c000c
def ew379 : Word := 0x4000f0004000f00
def ew380 : Word := 0x4040f0f00000000
def ew381 : Word := 0x4000c0c04000c0c
def ew382 : Word := 0x5000f0f00000000
def ew383 : Word := 0x4040c0c00000000
def ew384 : Word := 0x101030300000000
def ew385 : Word := 0x5000f0000000000
def ew386 : Word := 0x5000f00000000
def ew387 : Word := 0xc0c080800000000
def ew388 : Word := 0x303020200000000
def ew389 : Word := 0xf000a0000000000
def ew390 : Word := 0xf000a00000000
def ew391 : Word := 0x700030007000300
def ew392 : Word := 0x40c000c040c000c
def ew393 : Word := 0xe000a000e000a00
def ew394 : Word := 0xe0e0a0a00000000
def ew395 : Word := 0xc0808080c080808
def ew396 : Word := 0xf0a0a0a00000000
def ew397 : Word := 0xff00aa00ff00aa00
def ew398 : Word := 0xff00ff00aa00aa00
def ew399 : Word := 0xff00ff00ff000000
def ew400 : Word := 0xff00aa00
def ew401 : Word := 0xff000000aa00
def ew402 : Word := 0xffaaffaaffaaffaa
def ew403 : Word := 0xffffaaaaffffaaaa
def ew404 : Word := 0x5555555500000000
def ew405 : Word := 0xffffff00ffffff00
def ew406 : Word := 0xff88ff88ff88ff88
def ew407 : Word := 0xffff8888ffff8888
def ew408 : Word := 0xffff4444ffff4444
def ew409 : Word := 0xffaa0000ffaa
def ew410 : Word := 0xcc44cc44cc44cc44
def ew411 : Word := 0xffff00aaffff00aa
def ew412 : Word := 0xcccc8888cccc8888
def ew413 : Word := 0xffffaaaa00000000
def ew414 : Word := 0xcccc4444cccc4444
def ew415 : Word := 0x44444444cccccccc
def ew416 : Word := 0xffffaaaaffff0000
def ew417 : Word := 0x88888888cccccccc
def ew418 : Word := 0xffff5555ffff0000
def ew419 : Word := 0xaaaaeeeeaaaaeeee
def ew420 : Word := 0xaaaa2222aaaa2222
def ew421 : Word := 0xeeeeeeeeaaaaaaaa
def ew422 : Word := 0x22222222aaaaaaaa
def ew423 : Word := 0xffffccccffff0000
def ew424 : Word := 0xaaaaaa00aaaaaa00
def ew425 : Word := 0x5555550055555500
def ew426 : Word := 0xcccccc00cccccc00
def labelsBlock0 : Array Nat := #[
  0x3a68,
  0x1e48,
  0x1e58,
  0x1e68,
  0x1,
  0x2388,
  0x36c8,
  0x230c,
  0x130c,
  0x5,
  0x3698,
  0x3658,
  0xe28,
  0xe18,
  0x1002,
  0x2514
]
def labelsBlock1 : Array Nat := #[
  0x1104,
  0xd24,
  0xd14,
  0x100a,
  0x70c,
  0x105,
  0x3184,
  0x2984,
  0x2694,
  0x2584,
  0x109,
  0x2e98,
  0x1b2c,
  0x164c,
  0x185,
  0x2b2c
]
def labelsBlock2 : Array Nat := #[
  0xd30,
  0xd2c,
  0x2bd,
  0x211c,
  0x718,
  0xf2c,
  0x2518,
  0x292c,
  0x32d,
  0x2924,
  0x3384,
  0x2590,
  0x339,
  0x33d,
  0x2384,
  0x33c8
]
def labelsBlock3 : Array Nat := #[
  0x355,
  0x714,
  0x4b9,
  0x1924,
  0xe30,
  0x4bd,
  0x1244,
  0x4e1,
  0x2638,
  0x1b68,
  0x1e70,
  0x4e5,
  0x3ac8,
  0x9,
  0xd,
  0x11
]
def labelsBlock4 : Array Nat := #[
  0x708,
  0x15,
  0x19,
  0x161c,
  0x1348,
  0x1d,
  0x21,
  0x1308,
  0x25,
  0x29,
  0x261c,
  0x2d,
  0x31,
  0x2308,
  0x35,
  0x39
]
def labelsBlock5 : Array Nat := #[
  0x3d,
  0x170c,
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
  0x69,
  0x6d,
  0x71,
  0x75
]
def labelsBlock6 : Array Nat := #[
  0x79,
  0x7d,
  0x81,
  0x85,
  0x2718,
  0x3688,
  0x3648,
  0x89,
  0x8d,
  0x91,
  0x95,
  0x1748,
  0x99,
  0x9d,
  0xa1,
  0xa5
]
def labelsBlock7 : Array Nat := #[
  0xa9,
  0xad,
  0xb1,
  0xb5,
  0xb9,
  0xbd,
  0xc1,
  0xc5,
  0x1758,
  0xc9,
  0xcd,
  0xd1,
  0xd5,
  0xd9,
  0x2798,
  0xdd
]
def labelsBlock8 : Array Nat := #[
  0x3618,
  0xe1,
  0xe5,
  0x270c,
  0xe9,
  0xed,
  0xf1,
  0xf5,
  0xf9,
  0xfd,
  0x101,
  0x268c,
  0x2a8c,
  0xe08,
  0x2a38,
  0x232c
]
def labelsBlock9 : Array Nat := #[
  0x2aa4,
  0x1006,
  0x2ea8,
  0x3188,
  0x32c4,
  0x10d,
  0x111,
  0x2d84,
  0x115,
  0x119,
  0x3aa8,
  0x11d,
  0x121,
  0x3584,
  0x125,
  0x129
]
def labelsBlock10 : Array Nat := #[
  0x12d,
  0x131,
  0x135,
  0x3984,
  0x139,
  0x13d,
  0x141,
  0x145,
  0x149,
  0x14d,
  0x151,
  0x155,
  0x159,
  0x15d,
  0x161,
  0x165
]
def labelsBlock11 : Array Nat := #[
  0x169,
  0x16d,
  0x171,
  0x175,
  0x179,
  0x17d,
  0x181,
  0x189,
  0x18d,
  0x1b58,
  0xe2c,
  0x191,
  0xe0c,
  0x195,
  0x199,
  0x19d
]
def labelsBlock12 : Array Nat := #[
  0x1a1,
  0x1318,
  0x1a5,
  0x1a9,
  0x1e2c,
  0x1ad,
  0x1b1,
  0x2318,
  0x1b5,
  0x1b9,
  0x2e2c,
  0x1bd,
  0x1c1,
  0x1c5,
  0x1c9,
  0x1b0c
]
def labelsBlock13 : Array Nat := #[
  0x1cd,
  0x1d1,
  0x1d5,
  0x1d9,
  0x2b0c,
  0x1dd,
  0x1e1,
  0x1e5,
  0x1e9,
  0x1ed,
  0x1f9,
  0x1f5,
  0x1fd,
  0x201,
  0x205,
  0x209
]
def labelsBlock14 : Array Nat := #[
  0x20d,
  0x211,
  0x215,
  0x219,
  0x1f1,
  0x21d,
  0x221,
  0x225,
  0x229,
  0x22d,
  0x231,
  0x235,
  0x239,
  0x23d,
  0x241,
  0x245
]
def labelsBlock15 : Array Nat := #[
  0x249,
  0x1638,
  0x132c,
  0x24d,
  0x251,
  0x255,
  0x259,
  0x25d,
  0x261,
  0x265,
  0x269,
  0x26d,
  0x271,
  0x275,
  0x279,
  0x27d
]
def labelsBlock16 : Array Nat := #[
  0x281,
  0x285,
  0x289,
  0x28d,
  0x291,
  0x295,
  0x299,
  0x29d,
  0x330c,
  0x1e18,
  0x2a1,
  0x2a5,
  0x2a9,
  0x2ad,
  0x2b1,
  0x2b5
]
def labelsBlock17 : Array Nat := #[
  0x2b9,
  0x3ce8,
  0x1012,
  0x2c1,
  0x1c34,
  0x2c5,
  0x2c9,
  0x1b28,
  0x2cd,
  0x2d1,
  0x2ba8,
  0x2d5,
  0x2d9,
  0x2b28,
  0x2dd,
  0x2e1
]
def labelsBlock18 : Array Nat := #[
  0x2e5,
  0x2e9,
  0x2ed,
  0x2f1,
  0x2f5,
  0x2f9,
  0x3a28,
  0x2fd,
  0x301,
  0x305,
  0x309,
  0x30d,
  0x311,
  0x2c34,
  0x3ab0,
  0x3a70
]
def labelsBlock19 : Array Nat := #[
  0x2da8,
  0x315,
  0x319,
  0x31d,
  0x3df0,
  0x321,
  0x325,
  0x329,
  0x2c38,
  0x29a0,
  0x331,
  0x335,
  0x1e30,
  0x105e,
  0x105a,
  0x1066
]
def labelsBlock20 : Array Nat := #[
  0x1062,
  0x1022,
  0x102a,
  0x1026,
  0x102e,
  0x107a,
  0x1016,
  0x1a4c,
  0x341,
  0x345,
  0x349,
  0x34d,
  0x61007a,
  0x721016,
  0x103a,
  0x103e
]
def labelsBlock21 : Array Nat := #[
  0x731016,
  0x1a38,
  0x432016,
  0x351,
  0x1140,
  0x3ae0,
  0x359,
  0x35d,
  0x361,
  0x1960,
  0x365,
  0x369,
  0x36d,
  0x371,
  0x1100,
  0x375
]
def labelsBlock22 : Array Nat := #[
  0x1042,
  0x379,
  0x110c,
  0x37d,
  0x1304,
  0x381,
  0x1124,
  0x385,
  0x1904,
  0x106a,
  0x389,
  0x38d,
  0x391,
  0x410042,
  0x3ac0,
  0x395
]
def labelsBlock23 : Array Nat := #[
  0x399,
  0x39d,
  0x108a,
  0x3a1,
  0x710042,
  0x1340,
  0x1844,
  0x3a5,
  0x2144,
  0x3a9,
  0x1086,
  0x3ad,
  0x3b1,
  0x420042,
  0x3b5,
  0x3b9
]
def labelsBlock24 : Array Nat := #[
  0x3bd,
  0x3c1,
  0x720042,
  0x1940,
  0x3c5,
  0x3c9,
  0x3cd,
  0x3d1,
  0x3d5,
  0x3d9,
  0x3dd,
  0x430042,
  0x3e1,
  0x328c,
  0x3e5,
  0x3e9
]
def labelsBlock25 : Array Nat := #[
  0x3ed,
  0x3f1,
  0x31c0,
  0x3f5,
  0x3f9,
  0x530042,
  0x3fd,
  0x401,
  0x405,
  0x409,
  0x40d,
  0x630042,
  0x411,
  0x415,
  0x419,
  0x41d
]
def labelsBlock26 : Array Nat := #[
  0x3aa0,
  0x421,
  0x425,
  0x3a88,
  0x429,
  0x42d,
  0x730042,
  0x431,
  0x435,
  0x431042,
  0x439,
  0x43d,
  0x441,
  0x631042,
  0x445,
  0x449
]
def labelsBlock27 : Array Nat := #[
  0x432042,
  0x1032,
  0x44d,
  0x451,
  0x455,
  0x632042,
  0x1c9010042,
  0x2304,
  0x2920,
  0x459,
  0x45d,
  0x2380,
  0x1c5020042,
  0x192c,
  0x461,
  0x465
]
def labelsBlock28 : Array Nat := #[
  0x2980,
  0x1c5030042,
  0x1c9030042,
  0x469,
  0x46d,
  0x471,
  0x475,
  0x479,
  0x3a80,
  0x38a4,
  0x47d,
  0x110530042,
  0x110930042,
  0x481,
  0x485,
  0x489
]
def labelsBlock29 : Array Nat := #[
  0x48d,
  0x1108,
  0x1900,
  0x1300,
  0x1120,
  0x2044,
  0x3100,
  0x491,
  0x1920,
  0x495,
  0x499,
  0x49d,
  0x4a1,
  0x4a5,
  0x1c9231042,
  0x4a9
]
def labelsBlock30 : Array Nat := #[
  0x4ad,
  0x1a64,
  0x1b60,
  0x1c5232042,
  0x4b1,
  0x4b5,
  0x2300,
  0x2324,
  0x2b04,
  0x2904,
  0x36d0,
  0x1046,
  0x100e,
  0x104a,
  0x4c1,
  0x104e
]
def labelsBlock31 : Array Nat := #[
  0x4c5,
  0x4c9,
  0x1052,
  0x4cd,
  0x4d1,
  0x4d5,
  0x3960,
  0x4d9,
  0x1072,
  0x39a0,
  0x2eb0,
  0x4dd,
  0x2e30,
  0x1928,
  0xd28,
  0x1654
]
def labelsBlock32 : Array Nat := #[
  0x106e,
  0xd18,
  0x1076,
  0x4e9,
  0x109a,
  0x4ed,
  0x109e,
  0x10a2,
  0x10a6,
  0x4f1,
  0x4f5,
  0x10ae,
  0x4f9,
  0x4fd,
  0x501,
  0x10b6
]
def labelsBlock33 : Array Nat := #[
  0x505,
  0x509,
  0x50d,
  0x511,
  0x1114,
  0x1514,
  0x515,
  0x519,
  0x51d,
  0x10ba,
  0x521,
  0x10aa,
  0x4100a6,
  0x525,
  0x1056,
  0x10b2
]
def labelsBlock34 : Array Nat := #[
  0x41009e,
  0x4100a2,
  0x529,
  0x71009e,
  0x7100a2,
  0x7100a6,
  0x52d,
  0x10be,
  0x710,
  0x531,
  0x535,
  0x539,
  0x52009a,
  0x52009e,
  0x5200a2,
  0x53d
]
def labelsBlock35 : Array Nat := #[
  0x541,
  0x545,
  0x549,
  0x62009a,
  0x54d,
  0x62009e,
  0x6200a2,
  0x551,
  0xd10,
  0x53009a,
  0x53009e,
  0x1550,
  0x5300a2,
  0x5300a6,
  0x555,
  0xb1c
]
def labelsBlock36 : Array Nat := #[
  0x559,
  0x55d,
  0x5400b6,
  0x63009a,
  0x561,
  0x63009e,
  0x6300a2,
  0x6300a6,
  0x6400b6,
  0x1c38,
  0x565,
  0x3690,
  0x569,
  0x56d,
  0x44009a,
  0x571
]
def labelsBlock37 : Array Nat := #[
  0x44009e,
  0x4400a2,
  0x4400a6,
  0x4400ae,
  0x575,
  0x579,
  0xe10,
  0x74009a,
  0x57d,
  0x74009e,
  0x7400a2,
  0x7400a6,
  0x7400ae,
  0x581,
  0x62109e,
  0x6210a2
]
def labelsBlock38 : Array Nat := #[
  0x6310ae,
  0x6310b6,
  0x585,
  0x589,
  0x58d,
  0x63109e,
  0x6310a2,
  0x6310a6,
  0x1096,
  0x6410b6,
  0x591,
  0x595,
  0x599,
  0x44109e,
  0x4410a2,
  0x4410a6
]
def labelsBlock39 : Array Nat := #[
  0x4410ae,
  0x59d,
  0x5a1,
  0x53209a,
  0x53209e,
  0x5320a2,
  0x5a5,
  0x5a9,
  0x5430b6,
  0x5ad,
  0x74209a,
  0x74209e,
  0x7420a2,
  0x7430ae,
  0x74309a,
  0x74309e
]
def labelsBlock40 : Array Nat := #[
  0x7430a2,
  0x7430a6,
  0x3104,
  0xd0c,
  0x108e,
  0x1494100a2,
  0x14d4100a2,
  0x14d4100a6,
  0x107e,
  0x14d41009e,
  0x5b1,
  0x7420ba,
  0x4100aa,
  0x41004a,
  0x4100b2,
  0x1d081009e
]
def labelsBlock41 : Array Nat := #[
  0x1d08100a2,
  0x14d71009e,
  0x14d7100a2,
  0x14d7100a6,
  0x710056,
  0x6200ba,
  0x7100aa,
  0x18871009e,
  0x1887100a2,
  0x71004a,
  0x6300ba,
  0x18c71009e,
  0x18c7100a2,
  0x18c7100a6,
  0x7430be,
  0x7100b2
]
def labelsBlock42 : Array Nat := #[
  0x1d0b1009e,
  0x1d0b100a2,
  0x5300b2,
  0x520042,
  0x4400aa,
  0x6300be,
  0x530056,
  0x11012009a,
  0x7400be,
  0x4010a6,
  0x11452009e,
  0x1145200a2,
  0x40104a,
  0x1082,
  0x3cd8,
  0x18d52009a
]
def labelsBlock43 : Array Nat := #[
  0x18d52009e,
  0x18d5200a2,
  0x63004a,
  0x7430aa,
  0x1d0d2009a,
  0x1c562009e,
  0x1c56200a2,
  0x101a,
  0x14d62009a,
  0x14d62009e,
  0x14d6200a2,
  0x630056,
  0x53004a,
  0x4010ae,
  0x11453009e,
  0x1145300a2
]
def labelsBlock44 : Array Nat := #[
  0x1145300a6,
  0x401056,
  0x5b5,
  0x5300aa,
  0x1d093009e,
  0x1d09300a2,
  0x5400b2,
  0x11153009a,
  0x11153009e,
  0x1115300a2,
  0x1115300a6,
  0x7100ae,
  0x1c563009e,
  0x1c56300a2,
  0x1c56300a6,
  0x1c56400b6
]
def labelsBlock45 : Array Nat := #[
  0x6010be,
  0x18c63009e,
  0x18c6300a2,
  0x18c6300a6,
  0x1906400b6,
  0x6400b2,
  0x1510,
  0x3180,
  0x6300aa,
  0x1d0a3009e,
  0x1d0a300a2,
  0x1d0e3009a,
  0x1d0e3009e,
  0x1d0e300a2,
  0x1d0e300a6,
  0x3044
]
def labelsBlock46 : Array Nat := #[
  0x7100b6,
  0x1c544009e,
  0x1c54400a2,
  0x1c54400a6,
  0x1c54400ae,
  0x14d44009a,
  0x14d44009e,
  0x14d4400a2,
  0x14d4400a6,
  0x7400ba,
  0x6310b2,
  0x430016,
  0x18c4400ae,
  0x4100b6,
  0x1c574009e,
  0x1c57400a2
]
def labelsBlock47 : Array Nat := #[
  0x1c57400a6,
  0x1c57400ae,
  0x14d74009a,
  0x14d74009e,
  0x14d7400a2,
  0x14d7400a6,
  0x631056,
  0x6310be,
  0x7430ba,
  0x732016,
  0x60309a,
  0x14163109e,
  0x1416310a2,
  0x1416310a6,
  0x5010ae,
  0x1416410b6
]
def labelsBlock48 : Array Nat := #[
  0x40309a,
  0x7010ae,
  0x1c163109e,
  0x1c16310a2,
  0x1c16310a6,
  0x1c16410b6,
  0x743096,
  0x6310aa,
  0x63104a,
  0x1d0a3109e,
  0x1d0a310a2,
  0x54009a,
  0x15404109e,
  0x1540410a2,
  0x1540410a6,
  0x1540410ae
]
def labelsBlock49 : Array Nat := #[
  0x5100b6,
  0x64009a,
  0x19404109e,
  0x1940410a2,
  0x1940410a6,
  0x1940410ae,
  0x6100b6,
  0x53409a,
  0x14d44109e,
  0x14d4410a2,
  0x14d4410a6,
  0x1092,
  0x5410b6,
  0x5320ba,
  0x5430b2,
  0x4410aa
]
def labelsBlock50 : Array Nat := #[
  0x4410be,
  0x441096,
  0x513096,
  0x14c84109e,
  0x14c8410a2,
  0x11413209a,
  0x11413209e,
  0x1141320a2,
  0x4300a6,
  0x4300ae,
  0x1141430b6,
  0x1d413209a,
  0x1d413209e,
  0x1d41320a2,
  0x7300a6,
  0x7300ae
]
def labelsBlock51 : Array Nat := #[
  0x1d41430b6,
  0x11453209e,
  0x1145320a2,
  0x4310a6,
  0x4310ae,
  0x1145430b6,
  0x14d01004a,
  0x11053004a
]
def labelsGet (i : Nat) : Nat :=
  if i < 416 then
    if i < 208 then
      if i < 96 then
        if i < 48 then
          if i < 16 then
            labelsBlock0.getD (i-0) 3
          else
            if i < 32 then
              labelsBlock1.getD (i-16) 3
            else
              labelsBlock2.getD (i-32) 3
        else
          if i < 64 then
            labelsBlock3.getD (i-48) 3
          else
            if i < 80 then
              labelsBlock4.getD (i-64) 3
            else
              labelsBlock5.getD (i-80) 3
      else
        if i < 144 then
          if i < 112 then
            labelsBlock6.getD (i-96) 3
          else
            if i < 128 then
              labelsBlock7.getD (i-112) 3
            else
              labelsBlock8.getD (i-128) 3
        else
          if i < 176 then
            if i < 160 then
              labelsBlock9.getD (i-144) 3
            else
              labelsBlock10.getD (i-160) 3
          else
            if i < 192 then
              labelsBlock11.getD (i-176) 3
            else
              labelsBlock12.getD (i-192) 3
    else
      if i < 304 then
        if i < 256 then
          if i < 224 then
            labelsBlock13.getD (i-208) 3
          else
            if i < 240 then
              labelsBlock14.getD (i-224) 3
            else
              labelsBlock15.getD (i-240) 3
        else
          if i < 272 then
            labelsBlock16.getD (i-256) 3
          else
            if i < 288 then
              labelsBlock17.getD (i-272) 3
            else
              labelsBlock18.getD (i-288) 3
      else
        if i < 352 then
          if i < 320 then
            labelsBlock19.getD (i-304) 3
          else
            if i < 336 then
              labelsBlock20.getD (i-320) 3
            else
              labelsBlock21.getD (i-336) 3
        else
          if i < 384 then
            if i < 368 then
              labelsBlock22.getD (i-352) 3
            else
              labelsBlock23.getD (i-368) 3
          else
            if i < 400 then
              labelsBlock24.getD (i-384) 3
            else
              labelsBlock25.getD (i-400) 3
  else
    if i < 624 then
      if i < 512 then
        if i < 464 then
          if i < 432 then
            labelsBlock26.getD (i-416) 3
          else
            if i < 448 then
              labelsBlock27.getD (i-432) 3
            else
              labelsBlock28.getD (i-448) 3
        else
          if i < 480 then
            labelsBlock29.getD (i-464) 3
          else
            if i < 496 then
              labelsBlock30.getD (i-480) 3
            else
              labelsBlock31.getD (i-496) 3
      else
        if i < 560 then
          if i < 528 then
            labelsBlock32.getD (i-512) 3
          else
            if i < 544 then
              labelsBlock33.getD (i-528) 3
            else
              labelsBlock34.getD (i-544) 3
        else
          if i < 592 then
            if i < 576 then
              labelsBlock35.getD (i-560) 3
            else
              labelsBlock36.getD (i-576) 3
          else
            if i < 608 then
              labelsBlock37.getD (i-592) 3
            else
              labelsBlock38.getD (i-608) 3
    else
      if i < 720 then
        if i < 672 then
          if i < 640 then
            labelsBlock39.getD (i-624) 3
          else
            if i < 656 then
              labelsBlock40.getD (i-640) 3
            else
              labelsBlock41.getD (i-656) 3
        else
          if i < 688 then
            labelsBlock42.getD (i-672) 3
          else
            if i < 704 then
              labelsBlock43.getD (i-688) 3
            else
              labelsBlock44.getD (i-704) 3
      else
        if i < 768 then
          if i < 736 then
            labelsBlock45.getD (i-720) 3
          else
            if i < 752 then
              labelsBlock46.getD (i-736) 3
            else
              labelsBlock47.getD (i-752) 3
        else
          if i < 800 then
            if i < 784 then
              labelsBlock48.getD (i-768) 3
            else
              labelsBlock49.getD (i-784) 3
          else
            if i < 816 then
              labelsBlock50.getD (i-800) 3
            else
              labelsBlock51.getD (i-816) 3
def lh (s : Nat) (d : List Nat) (ws : List Nat) (i : Nat) : Nat :=
  labelsGet (d.getD (((ws.getD (i / (64 / s)) 0) >>> ((i % (64 / s)) * s)) % 2 ^ s) 0)
def viewsBlock0 : Array View := #[
  ⟨0x4444000044440000,⟨18,by decide⟩,0x4440000040000000,[ew0,ew1,ew2],3,lh 3 [0,1,2,3,4] [0x8d1000]⟩,
  ⟨0x4444444400000000,⟨34,by decide⟩,0x4440400000000000,[ew3,ew4,ew2],3,fun _ => 3⟩,
  ⟨0x222200002222,⟨1,by decide⟩,0x222000002000,[ew5,ew6,ew7],3,fun _ => 3⟩,
  ⟨0xaa000000aa,⟨1,by decide⟩,0xa800000080,[ew8,ew9,ew10],3,fun _ => 3⟩,
  ⟨0xc000c000c000c00,⟨10,by decide⟩,0xc00080008000000,[ew11,ew12,ew13],3,fun _ => 3⟩,
  ⟨0xcc00cc00cc00cc,⟨2,by decide⟩,0xc8008800880080,[ew14,ew15,ew16,ew17],5,lh 3 [5,6,7,8,9] [0x808608408408]⟩,
  ⟨0x8844884488448844,⟨2,by decide⟩,0x8840880088008000,[ew18,ew19,ew20,ew21],5,fun _ => 3⟩,
  ⟨0x4444444444444444,⟨2,by decide⟩,0x4440400040004000,[ew22,ew23,ew24,ew25],4,lh 3 [10,11,12,13,14] [0x89a000249000]⟩,
  ⟨0xc0c03030c0c0303,⟨0,by decide⟩,0xc08020008080000,[ew26,ew27,ew28,ew29],4,fun _ => 3⟩,
  ⟨0xc0c03030c0c03030,⟨4,by decide⟩,0xc0c02020c0802000,[ew30,ew31,ew32,ew33],4,fun _ => 3⟩,
  ⟨0xcc003300cc0033,⟨0,by decide⟩,0xc8002000880000,[ew34,ew16,ew35,ew36],4,fun _ => 3⟩,
  ⟨0xcc003300cc003300,⟨8,by decide⟩,0xcc002200c8002000,[ew37,ew38,ew32,ew39],4,fun _ => 3⟩,
  ⟨0xf00000f0f00000f,⟨0,by decide⟩,0xe0000080a000000,[ew40,ew41,ew42,ew43],4,fun _ => 3⟩,
  ⟨0x2222222222222222,⟨1,by decide⟩,0x2222222022222000,[ew44,ew45,ew46,ew47],4,lh 3 [15,16,17,18,19] [0x89a249000000]⟩,
  ⟨0xcccc0000cccc,⟨2,by decide⟩,0xc8880000c080,[ew48,ew49,ew50,ew51],3,lh 3 [13,7,5,20,21] [0x89a000249000]⟩,
  ⟨0xcccccccc,⟨2,by decide⟩,0xc888c080,[ew52,ew53,ew54,ew55],3,fun _ => 3⟩
]
def viewsBlock1 : Array View := #[
  ⟨0xf0f0f0f00000000,⟨32,by decide⟩,0xe0a0a0800000000,[ew56,ew57,ew58,ew59],5,fun _ => 3⟩,
  ⟨0xf000f000f000f0,⟨4,by decide⟩,0xe000a000a00080,[ew60,ew15,ew61,ew62],5,fun _ => 3⟩,
  ⟨0xff00ff00000000,⟨32,by decide⟩,0xea00a800000000,[ew63,ew17,ew62,ew64],5,fun _ => 3⟩,
  ⟨0xff000000ff00,⟨8,by decide⟩,0xea000000e000,[ew65,ew50,ew66,ew67],3,fun _ => 3⟩,
  ⟨0xff00ff00,⟨8,by decide⟩,0xea00e000,[ew68,ew54,ew69,ew70],3,fun _ => 3⟩,
  ⟨0xffff00000000,⟨32,by decide⟩,0xeaa800000000,[ew71,ew51,ew72,ew67],5,fun _ => 3⟩,
  ⟨0x8484212184842121,⟨0,by decide⟩,0x8480202080802000,[ew30,ew73,ew74,ew75],5,fun _ => 3⟩,
  ⟨0x4848121248481212,⟨1,by decide⟩,0x4848020048080000,[ew76,ew77,ew78,ew79],5,fun _ => 3⟩,
  ⟨0x8844221188442211,⟨0,by decide⟩,0x8840220088002000,[ew37,ew20,ew80,ew81],5,fun _ => 3⟩,
  ⟨0x4488112244881122,⟨1,by decide⟩,0x4488002040880000,[ew82,ew83,ew84,ew85],5,fun _ => 3⟩,
  ⟨0x606060606060606,⟨1,by decide⟩,0x602020002020000,[ew86,ew87,ew88,ew89],4,fun _ => 3⟩,
  ⟨0x66006600660066,⟨1,by decide⟩,0x62002000220000,[ew90,ew91,ew92,ew93],4,fun _ => 3⟩,
  ⟨0x6600660066006600,⟨9,by decide⟩,0x6600620062006000,[ew23,ew94,ew95,ew96],4,fun _ => 3⟩,
  ⟨0x6666666600000000,⟨33,by decide⟩,0x6662622000000000,[ew25,ew97,ew96,ew98],5,lh 3 [22,23,24,25,26] [0x89a249000000]⟩,
  ⟨0x4848484848484848,⟨3,by decide⟩,0x4848480848084000,[ew22,ew99,ew77,ew100],5,lh 3 [11,27,28,29,30] [0x8c9489000000]⟩,
  ⟨0x5a5a00005a5a,⟨1,by decide⟩,0x4a0800004000,[ew101,ew102,ew103,ew104],5,fun _ => 3⟩
]
def viewsBlock2 : Array View := #[
  ⟨0x4488448844884488,⟨3,by decide⟩,0x4488408840884080,[ew23,ew105,ew83,ew106],4,fun _ => 3⟩,
  ⟨0x50a050a050a050a,⟨1,by decide⟩,0x40a0008000a0000,[ew107,ew108,ew109,ew110],4,fun _ => 3⟩,
  ⟨0x5050a0a05050a0a,⟨1,by decide⟩,0x4000a0800000000,[ew111,ew112,ew113,ew114],4,fun _ => 3⟩,
  ⟨0x3c003c003c003c00,⟨10,by decide⟩,0x2c00280028002000,[ew115,ew116,ew117,ew118],5,lh 3 [31,28,32,33,34] [0x89a249000000]⟩,
  ⟨0x33330000cccc,⟨2,by decide⟩,0x22200000c080,[ew119,ew120,ew121,ew122],4,lh 3 [23,35,36,37,38,39,40] [0xcac689000009]⟩,
  ⟨0xcccc3333cccc3333,⟨0,by decide⟩,0xccc82220c8882000,[ew123,ew124,ew125,ew126,ew127],7,lh 3 [41,23,25,42,43,44] [0x1249000000000000,0x163692449]⟩,
  ⟨0xcccccccccccccccc,⟨2,by decide⟩,0xccc8c888c888c080,[ew128,ew129,ew130,ew124,ew131],7,lh 3 [7,8,13,36,20,45] [0x1249000000000000,0x15c692449]⟩,
  ⟨0xf0f0f0f0f0f0f0f,⟨0,by decide⟩,0xe0a0a080a0a0000,[ew132,ew133,ew134,ew135,ew136],7,lh 3 [7,23,46,16,47,48] [0x2249000000000000,0x1624492da]⟩,
  ⟨0xf0f0f0f0f0f0f0f0,⟨4,by decide⟩,0xe0e0e0a0e0a0e080,[ew137,ew129,ew138,ew139,ew140],7,fun _ => 3⟩,
  ⟨0xff00ff00ff00ff,⟨0,by decide⟩,0xea00a800aa0080,[ew141,ew142,ew143,ew144,ew145],7,lh 3 [16,36,49,20,7,50] [0x851651000000,0x14a2ca200]⟩,
  ⟨0xff00ff00ff00ff00,⟨8,by decide⟩,0xee00ea00ea00e000,[ew146,ew130,ew138,ew147,ew148],6,lh 3 [41,51,52,32,17,53] [0x1249000000000000,0x15a51a449]⟩,
  ⟨0xffff0000ffff,⟨0,by decide⟩,0xeaa80000e080,[ew149,ew150,ew151,ew152,ew153],7,fun _ => 3⟩,
  ⟨0xffffffff,⟨0,by decide⟩,0xeaaae080,[ew154,ew155,ew156,ew157,ew158],6,fun _ => 3⟩,
  ⟨0xffffffff00000000,⟨32,by decide⟩,0xeeeaeaa800000000,[ew159,ew131,ew140,ew148,ew160],7,fun _ => 3⟩,
  ⟨0x6666666666666666,⟨1,by decide⟩,0x6662622062226000,[ew161,ew162,ew163,ew164,ew165],7,lh 3 [17,15,54,16,18,55] [0x680240240240240,0x1501100d0]⟩,
  ⟨0x5555aaaa5555aaaa,⟨1,by decide⟩,0x4440aaa84000a080,[ew166,ew167,ew168,ew169,ew170],7,fun _ => 3⟩
]
def viewsBlock3 : Array View := #[
  ⟨0xffffffffffffffff,⟨0,by decide⟩,0xeeeaeaa8eaaae080,[ew171,ew172,ew173,ew174,ew175,ew176],10,lh 3 [22,56,3,57,58,7,18,59] [0x1249000000249249,0x15c692449,0x38d24b38d2480000,0x7]⟩
]
def viewsGet (i : Nat) : Option View :=
  if i < 32 then
    if i < 16 then
      viewsBlock0[(i-0)]?
    else
      viewsBlock1[(i-16)]?
  else
    if i < 48 then
      viewsBlock2[(i-32)]?
    else
      viewsBlock3[(i-48)]?
def nodesBlock0 : Array Node := #[
  ⟨0,3,[ew0,ew1,ew2],lh 3 [6,11,60,2,0,3] [0x8011640c54ab610,0xe344a899349]⟩,
  ⟨5,5,[ew14,ew15,ew16,ew17],lh 6 [7,10,8,5,6,20,68,11,36,81,61,29,62,63,64,65,66,67,69,70,71,72,73,74,75,76,77,78,79,80,82,83,84,85,86,87,88,89,90,91] [0x10830814b283103,0x4080413c314e348,0x944c6046486091,0x6030175861c6543,0x826c601a6431c3,0x784089744041705,0x1c48050007c5049,0x8c51c5884000844,0x9411c1902000,0x9c21c2981]⟩,
  ⟨5,4,[ew177,ew14,ew15,ew16,ew17],lh 4 [5,6,7,8,68,10,36,20,92,93,94,95,29,11] [0x1cb2a293837160,0x2d11251132004043,0x325]⟩,
  ⟨5,4,[ew14,ew15,ew178,ew16,ew17],lh 4 [7,36,8,20,10,11,6,29,5,96,97,98,99] [0x2661501142181317,0xc0b2a293050324,0x204]⟩,
  ⟨5,4,[ew179,ew14,ew15,ew16,ew17],lh 4 [6,7,36,8,11,10,100,5,20,64,101,102] [0x2920141435358072,0x1b001a0036612253,0x414]⟩,
  ⟨5,4,[ew180,ew14,ew15,ew16,ew17],lh 4 [7,8,10,11,20,36,6,5,64] [0x2847303021216455,0x403021210303121,0x102]⟩,
  ⟨5,4,[ew181,ew14,ew15,ew16,ew17],lh 4 [7,20,5,10,11,8,36,68,103,104,105,106,64,67,101] [0x2c12b0a055918176,0x10403e31022423d,0x403]⟩,
  ⟨5,4,[ew14,ew15,ew16,ew182,ew17],lh 4 [7,6,68,8,20,107,5,11,67,108,109,10,110,111] [0x1132702663285542,0xc3070b34110a1194,0xd0]⟩,
  ⟨5,4,[ew8,ew14,ew15,ew16,ew17],lh 4 [6,7,20,11,10,68,5,8,107,71] [0x8020131377202066,0x1200140025315954,0x314]⟩,
  ⟨5,4,[ew183,ew14,ew15,ew16,ew17],lh 4 [6,7,5,20,8,11,68,10,71] [0x2030515174030362,0x1300130041225842,0x415]⟩,
  ⟨5,4,[ew184,ew14,ew15,ew16,ew17],lh 4 [6,8,20,10,5,7,67,71,112,113,114,115,107,74,11,68] [0xc02055b1a1908044,0x120023001fed7766,0x133]⟩,
  ⟨5,4,[ew14,ew15,ew16,ew17,ew185],lh 4 [6,5,8,7,10,20,74,68,116,117,118,119,11] [0x27131614211050,0x22a2343900850034,0xc3b]⟩,
  ⟨5,4,[ew186,ew14,ew15,ew16,ew17],lh 4 [6,10,8,5,20,7,68,11,77] [0x3040552121404063,0x2400410028373123,0x211]⟩,
  ⟨5,4,[ew187,ew14,ew15,ew16,ew17],lh 4 [20,6,10,8,7,5,67,71,11,68,77] [0x101842323101055,0x401100110a497766,0x322]⟩,
  ⟨5,4,[ew14,ew188,ew15,ew16,ew17],lh 4 [120,7,11,5,20,8,74,6,10,121] [0x260500340033003,0x1412145921218574,0x512]⟩,
  ⟨5,4,[ew14,ew15,ew16,ew189,ew17],lh 4 [5,120,7,11,10,20,8,121,6] [0x2001011001100110,0x2324266323255487,0x323]⟩
]
def nodesBlock1 : Array Node := #[
  ⟨5,4,[ew190,ew14,ew15,ew16,ew17],lh 4 [36,5,7,6,8,20,120,11,10,122,123,81] [0x1303a29284550101,0x27332b3401100660,0x427]⟩,
  ⟨5,4,[ew191,ew14,ew15,ew16,ew17],lh 4 [68,36,7,6,8,5,20,10,11,124,125,81] [0x110a29244330101,0x26282b7605501001,0x827]⟩,
  ⟨5,4,[ew14,ew192,ew15,ew16,ew17],lh 4 [68,126,8,10,7,6,81,11,127,20] [0x110100101100110,0x4948663274323255,0x243]⟩,
  ⟨5,4,[ew14,ew15,ew16,ew17,ew193],lh 4 [68,126,11,8,6,10,128,127,20,7] [0x110021210010110,0x5536623842475443,0x923]⟩,
  ⟨5,4,[ew194,ew14,ew15,ew16,ew17],lh 4 [10,7,126,8,68,36,20,129,130,11,6,131] [0x4224918070665252,0x1ba1030312143030,0x310]⟩,
  ⟨5,4,[ew195,ew14,ew15,ew16,ew17],lh 4 [5,10,8,126,20,7,11,6,132,133,68,131] [0x340559181740303,0x2b641212a0060120,0x211]⟩,
  ⟨5,4,[ew14,ew15,ew196,ew16,ew17],lh 4 [5,47,20,7,6,8,10,126,68,11,134] [0x3118011001100720,0x9366234325452442,0x53a]⟩,
  ⟨5,4,[ew14,ew15,ew16,ew17,ew197],lh 4 [6,36,47,20,10,7,102,134,11,8] [0x1221122112212010,0x4847300360034003,0x559]⟩,
  ⟨5,4,[ew198,ew14,ew15,ew16,ew17],lh 4 [68,6,36,10,7,47,20,135,136,8,11,128] [0x120a49381710202,0x6114311605502002,0xb34]⟩,
  ⟨5,4,[ew199,ew14,ew15,ew16,ew17],lh 4 [68,6,36,5,10,7,47,8,20,137,138,102,11,128] [0x1205544a1913030,0xb118811706602002,0xdc7]⟩,
  ⟨5,3,[ew14,ew15,ew200,ew17],lh 4 [5,6,7,8,36,67,68,20,11,10] [0x7113200644300150,0x32928112]⟩,
  ⟨5,3,[ew201,ew14,ew15,ew17],lh 3 [36,6,5,8,7,20,68,10] [0x409040273c34bc18,0x149]⟩,
  ⟨5,3,[ew14,ew15,ew16,ew202],lh 4 [5,6,8,7,68,36,10,74,20] [0x6112550404200170,0x23638113]⟩,
  ⟨5,3,[ew203,ew14,ew15,ew16],lh 3 [36,5,6,7,8,20,10,68] [0x41e0201733553208,0x152]⟩,
  ⟨5,3,[ew14,ew15,ew204,ew17],lh 4 [36,7,5,8,29,10,6,68,11,20] [0x6653022007302044,0x31519181]⟩,
  ⟨5,3,[ew205,ew14,ew15,ew17],lh 4 [36,6,7,68,20,8,29,5,10,11] [0x3066282551410703,0x41120920]⟩
]
def nodesBlock2 : Array Node := #[
  ⟨5,3,[ew14,ew15,ew206,ew16],lh 4 [36,7,8,29,68,6,10,5,11,20] [0x5581042007104033,0x12619262]⟩,
  ⟨5,3,[ew207,ew14,ew15,ew16],lh 3 [36,6,5,7,8,20,10,29] [0x41a043f7a3669082,0x149]⟩,
  ⟨5,3,[ew14,ew208,ew16,ew17],lh 3 [5,7,20,10,11,8,68,29] [0x1461b5a2040f8190,0x10b]⟩,
  ⟨5,3,[ew209,ew14,ew16,ew17],lh 3 [5,7,68,8,10,20,64,11] [0x1402090a798e3c28,0xcc]⟩,
  ⟨5,3,[ew14,ew15,ew16,ew210],lh 4 [5,10,7,20,11,64,67,68,101,8] [0x1813700401600530,0x92123242]⟩,
  ⟨5,3,[ew211,ew14,ew15,ew16],lh 4 [5,7,68,10,8,20,67,11,64] [0x850143115710202,0x34340266]⟩,
  ⟨5,3,[ew14,ew212,ew16,ew17],lh 4 [6,68,5,7,20,67,8,107,10,11] [0x8006122121557040,0x63934003]⟩,
  ⟨5,3,[ew213,ew14,ew16,ew17],lh 4 [6,7,8,68,10,67,107,5,20,11] [0x2355100820040760,0x21413913]⟩,
  ⟨5,3,[ew14,ew15,ew16,ew214],lh 4 [6,7,20,8,67,68,5,107,11] [0x2003661535447020,0x31812001]⟩,
  ⟨5,3,[ew215,ew14,ew15,ew16],lh 4 [6,5,68,7,20,8,10,67,107] [0x8040365330402121,0x60051277]⟩,
  ⟨5,3,[ew14,ew216,ew16,ew17],lh 4 [6,8,10,20,67,71,68,107,74,11,7] [0x2001698655447030,0x1221a003]⟩,
  ⟨5,3,[ew217,ew14,ew16,ew17],lh 4 [6,7,20,8,10,67,71,74,107,5,68] [0x6655200140030820,0x3141a977]⟩,
  ⟨5,3,[ew14,ew15,ew218,ew17],lh 4 [6,20,67,71,74,8,10,7,107,11,68] [0x6005a94433228010,0x77651001]⟩,
  ⟨5,3,[ew219,ew14,ew15,ew17],lh 4 [6,7,67,71,8,10,20,74,107,5,68] [0x8060415105043322,0x6001a977]⟩,
  ⟨5,3,[ew14,ew220,ew16,ew17],lh 4 [6,7,20,5,68,71,74,8,10,107] [0x8007436655439020,0x71812001]⟩,
  ⟨5,3,[ew221,ew14,ew16,ew17],lh 4 [6,107,5,7,10,8,74,20,67] [0x2118300750040120,0x53431266]⟩
]
def nodesBlock3 : Array Node := #[
  ⟨5,3,[ew14,ew15,ew222,ew17],lh 4 [6,67,8,7,5,71,74,10,20] [0x7002146655214010,0x23738003]⟩,
  ⟨5,3,[ew223,ew14,ew15,ew17],lh 4 [71,6,7,5,10,8,20,74,67] [0x160242551418030,0x61120377]⟩,
  ⟨5,3,[ew14,ew188,ew189,ew17],lh 3 [120,7,5,10,8,11,107,81] [0x1a6967c290402c03,0x4]⟩,
  ⟨5,3,[ew14,ew15,ew16,ew224],lh 4 [36,7,120,5,8,10,81,11,20] [0x6654100202203003,0x41518171]⟩,
  ⟨5,3,[ew14,ew15,ew16,ew225],lh 4 [36,5,6,7,120,8,81,20,11] [0x6225011004401001,0x53837223]⟩,
  ⟨5,3,[ew14,ew15,ew16,ew226],lh 3 [68,36,6,7,20,81,10,8] [0x3893a94201201088,0x1de]⟩,
  ⟨5,3,[ew14,ew15,ew227,ew16],lh 4 [68,36,7,5,6,8,10,81,11] [0x4482100103300110,0x25627765]⟩,
  ⟨5,3,[ew14,ew192,ew16,ew193],lh 3 [68,126,6,10,81,8,131,7] [0x47f2695048201048,0x4]⟩,
  ⟨5,3,[ew14,ew15,ew228,ew17],lh 3 [7,10,8,128,68,126] [0x61828a0c345196c,0x81]⟩,
  ⟨5,3,[ew14,ew15,ew229,ew17],lh 3 [7,10,8,20,68,126,6] [0x63028a14445175c,0x81]⟩,
  ⟨5,3,[ew14,ew15,ew230,ew17],lh 4 [5,10,8,20,11,7,126,68,131] [0x1212700420010630,0x55123843]⟩,
  ⟨5,3,[ew14,ew231,ew15,ew17],lh 3 [5,7,8,10,20,11,126] [0x14594da2051a00d0,0x10d]⟩,
  ⟨5,3,[ew14,ew15,ew196,ew197],lh 4 [47,20,5,36,102,7,6,126,10,128] [0x4481300320020710,0x951665]⟩,
  ⟨5,3,[ew14,ew232,ew16,ew17],lh 3 [68,6,102,7,47,36,20,10] [0x344be4e0a0a05801,0x9a]⟩,
  ⟨5,3,[ew14,ew233,ew16,ew17],lh 3 [68,6,36,7,47,8,10,102] [0x3e4bc4d120402050,0x15e]⟩,
  ⟨5,3,[ew14,ew234,ew16,ew17],lh 3 [68,6,36,8,10,47,20,102] [0x3e4e84b168402050,0xe4]⟩
]
def nodesBlock4 : Array Node := #[
  ⟨5,3,[ew14,ew235,ew16,ew17],lh 4 [68,6,36,7,47,8,10,102,11] [0x6115044020020120,0x53837113]⟩,
  ⟨14,3,[ew48,ew49,ew50,ew51],lh 4 [13,5,7,36,20,141,139,126,140,142,143] [0x5504312310801761,0x2a04292]⟩,
  ⟨29,5,[ew25,ew97,ew96,ew98],lh 5 [145,144,23,146,24,27,10,25,154,22,148,6,60,151,157,147,149,150,152,153,155,156,158,159,160,161,162,163,164] [0x10e401064004e7,0x4a10104200463,0x521010a500441,0x4c60292a028cf,0x90c4d88ca581c42,0xaaccba0d0899cad,0xc08c2b8cceb2d0e,0xe091bd3129cb10c]⟩,
  ⟨29,4,[ew25,ew236,ew97,ew96,ew98],lh 4 [154,148,10,24,144,146,27,145,165,147,166,167,168,23,25] [0x109144113311871,0x22020edcb0a06655,0x20]⟩,
  ⟨29,4,[ew25,ew97,ew96,ew237,ew98],lh 4 [154,148,10,146,27,144,22,24,147,168,25,23] [0x108155115411731,0x60202b42020a3439,0x60]⟩,
  ⟨29,4,[ew238,ew25,ew97,ew96,ew98],lh 4 [154,148,10,24,146,27,144,25,147,23,151] [0x1341202055743131,0x22020a4901081661,0x20]⟩,
  ⟨29,4,[ew239,ew25,ew97,ew96,ew98],lh 4 [154,148,10,144,27,146,24,23,147,25,151] [0x1661020274553131,0x22020a4901081341,0x20]⟩,
  ⟨29,4,[ew25,ew240,ew97,ew96,ew98],lh 5 [148,154,27,146,151,145,169,24,144,147,6,170,171,10,23,172,22] [0x204001c60018a0,0x685825894308029,0x60110c2f2104e]⟩,
  ⟨29,4,[ew25,ew97,ew96,ew98,ew241],lh 4 [24,6,23,60,148,144,27,154,172,10,146] [0x5005044005601014,0x3322332a19181261,0x772]⟩,
  ⟨29,4,[ew242,ew25,ew97,ew96,ew98],lh 4 [60,24,148,6,23,27,154,146,10,157] [0x3112865050731212,0x4936305012610404,0x400]⟩,
  ⟨29,4,[ew243,ew25,ew97,ew96,ew98],lh 4 [60,24,148,23,6,154,27,151,146,10,157] [0x2112550303442121,0x3a98706012210303,0x300]⟩,
  ⟨29,4,[ew25,ew97,ew244,ew96,ew98],lh 4 [24,6,23,148,27,157,60,154,145,173,174,175,146,176,10] [0x330024209801003,0x7766551c12421ba1,0x2ed]⟩,
  ⟨29,4,[ew25,ew97,ew96,ew98,ew245],lh 4 [146,24,60,144,6,154,148,25,176,23,22] [0x1331365323214116,0x2528700704404002,0xa59]⟩,
  ⟨29,4,[ew246,ew25,ew97,ew96,ew98],lh 4 [25,146,22,144,24,60,23,154,147,6,163] [0x1010726510103434,0x292011032825334,0xa52]⟩,
  ⟨29,4,[ew247,ew25,ew97,ew96,ew98],lh 4 [6,148,144,25,154,60,146,22,23,163] [0x301745503031212,0x3004066041121221,0x948]⟩,
  ⟨29,3,[ew248,ew97,ew96,ew98],lh 4 [148,10,23,22,154,146,24,27,144,147,177,25] [0xb2a2100908700650,0x41411313]⟩
]
def nodesBlock5 : Array Node := #[
  ⟨29,3,[ew25,ew97,ew96,ew249],lh 4 [154,148,10,24,144,23,147,178,25] [0x8575010614411331,0x2022020]⟩,
  ⟨29,3,[ew250,ew25,ew97,ew96],lh 4 [154,148,10,27,146,147,24,144,23] [0x1641200202201005,0x34381731]⟩,
  ⟨29,3,[ew25,ew236,ew237,ew98],lh 4 [154,148,27,144,22,177,147,151,178] [0x8072010613311521,0x40420]⟩,
  ⟨29,3,[ew251,ew97,ew96,ew98],lh 4 [154,148,27,146,151,24,144,10,23,179,22] [0x4428010716211531,0xa023090]⟩,
  ⟨29,3,[ew25,ew97,ew252,ew98],lh 4 [154,148,27,146,6,24,144,147,23,180,10] [0x4428010716211531,0xa023090]⟩,
  ⟨29,3,[ew253,ew25,ew97,ew98],lh 4 [6,154,148,10,27,144,151,24,147] [0x702131360405242,0x30011218]⟩,
  ⟨29,3,[ew25,ew240,ew96,ew241],lh 4 [6,148,154,27,151,179,144,147,180,157,22] [0x380212716310501,0x442a90]⟩,
  ⟨29,3,[ew254,ew97,ew96,ew98],lh 4 [24,23,6,148,60,157,154,27,146,181,10] [0x2171036001442003,0x1a915528]⟩,
  ⟨29,3,[ew25,ew96,ew255,ew98],lh 4 [23,24,148,27,6,60,157,182,10,146] [0x5530122141121030,0x66490870]⟩,
  ⟨29,3,[ew256,ew25,ew96,ew98],lh 3 [60,24,23,6,148,154,157,27] [0x2329082d9d6382cc,0x80]⟩,
  ⟨29,3,[ew25,ew97,ew244,ew245],lh 4 [60,24,23,6,148,181,182,157,163] [0x3060124205013114,0x807232]⟩,
  ⟨29,2,[ew248,ew237,ew98],lh 3 [148,10,27,22,147] [0x2cb204090]⟩,
  ⟨29,2,[ew25,ew237,ew249],lh 3 [154,148,144,22,147] [0xc3044291]⟩,
  ⟨29,2,[ew251,ew96,ew241],lh 3 [148,154,151,27,144,147,22] [0x48e20d118]⟩,
  ⟨29,2,[ew25,ew252,ew241],lh 3 [6,148,154,144,147,22,151] [0xc054540c1]⟩,
  ⟨29,2,[ew254,ew97,ew245],lh 3 [60,24,23,6,157] [0x89a202048]⟩
]
def nodesBlock6 : Array Node := #[
  ⟨29,2,[ew25,ew255,ew245],lh 3 [60,23,148,24,157] [0x8016510c2]⟩,
  ⟨30,5,[ew22,ew99,ew77,ew100],lh 6 [7,11,27,186,8,29,28,139,10,2,13,188,31,183,184,185,187,189,190,191,192,193,194,195,196,197,198,199,200,201,202,203,204,205,206,207,208,209,210,211,212,213,214,215,216,217] [0x44b40308f387345,0x5031834c708b483,0x2185c5185585215,0x70705b685000643,0x1047c305e747000,0x88910984918680a,0x30294904190a1a3,0xa4a3289c2042982,0xac8041a84000,0xb44044b08]⟩,
  ⟨30,4,[ew257,ew22,ew77,ew100],lh 4 [11,27,28,2,139,31,29,10,186,218,219,220,221,222,223] [0x13233b3121a98161,0x223e31001d13001c,0x4046554746226764,0x755700255600454,0x20]⟩,
  ⟨30,4,[ew257,ew22,ew99,ew77,ew100],lh 4 [11,139,28,31,27,8,186,224,225,226,227,185,218,29] [0x11cba09082724461,0x330302525011312d,0x30]⟩,
  ⟨30,4,[ew22,ew99,ew258,ew77,ew100],lh 4 [10,11,27,31,139,28,8,7,185,186,219,2] [0xa21313050544298,0x317170606312120b,0x100]⟩,
  ⟨30,4,[ew180,ew22,ew77,ew100],lh 4 [10,188,11,31,27,28,2,185,218,228,229,230,231,232] [0x656600454987411,0x5162243442263340,0xc22131101b55a001,0x2030020533121d33,0x52]⟩,
  ⟨30,4,[ew180,ew22,ew99,ew77,ew100],lh 4 [10,186,31,11,28,27,139,218,188] [0x1817323204045561,0x2232340401231140,0x300]⟩,
  ⟨30,4,[ew11,ew22,ew99,ew77,ew100],lh 4 [10,11,31,27,139,28,186,228,188,2] [0x4834212150507366,0x2213130901442050,0x100]⟩,
  ⟨30,4,[ew0,ew22,ew99,ew77,ew100],lh 4 [186,11,27,31,2,139,10,29,188,193,28] [0x8005131366424270,0x33121244205500a9,0x131]⟩,
  ⟨30,4,[ew22,ew99,ew77,ew259,ew100],lh 4 [29,10,11,31,27,185,229,193,186,2,233,234,28] [0x1910320801070650,0x32113c13242b44a4,0x232]⟩,
  ⟨30,4,[ew260,ew22,ew99,ew77,ew100],lh 4 [11,29,27,2,31,10,186,235,236,185,230,28,196] [0x1a91807055232361,0x4402023321401c1b,0x40]⟩,
  ⟨30,4,[ew261,ew22,ew99,ew77,ew100],lh 5 [7,139,10,13,29,27,186,143,237,238,8,11,239,240,196,241,128] [0x6818b5092541484,0x198210384109861,0x400200c0738c4f]⟩,
  ⟨30,4,[ew3,ew22,ew99,ew77,ew100],lh 4 [10,27,8,13,7,139,188,11,29,199,186,241,143] [0x6618740202131355,0x4311c10b0a490202,0x200]⟩,
  ⟨30,4,[ew22,ew99,ew77,ew100,ew262],lh 4 [8,10,11,27,13,139,186,231,199,242,243,244,7] [0x906625810103735,0x1100120b44a42323,0xc20]⟩,
  ⟨30,4,[ew263,ew22,ew99,ew77,ew100],lh 4 [139,13,8,7,10,27,241,186,245,246,11,232,202,143] [0xb10a39282151570,0x313d31266c030240,0x244]⟩,
  ⟨30,4,[ew264,ew22,ew99,ew77,ew100],lh 4 [13,10,11,29,186,139,188,56,8,247,248,249,250,7,202,241] [0x6603d2c1b1a09055,0x8027701f1e244334,0x812]⟩
]
def nodesBlock7 : Array Node := #[
  ⟨30,4,[ew22,ew265,ew99,ew77,ew100],lh 4 [186,13,8,7,11,29,251,252,202,2,28,253,254,242,56] [0x840025210150760,0x313e312dc3b4a291,0x234]⟩,
  ⟨30,4,[ew22,ew99,ew77,ew266,ew100],lh 4 [186,7,2,28,139,31,11,29,242,13,8] [0x441400403732027,0x16565a3515192328,0x616]⟩,
  ⟨30,4,[ew267,ew22,ew99,ew77,ew100],lh 4 [11,31,139,186,2,28,8,13,193,207] [0x2342101055743232,0x1101094601012682,0x10]⟩,
  ⟨30,4,[ew268,ew22,ew99,ew77,ew100],lh 4 [29,31,11,139,2,28,13,188,8,207] [0x7760212185440303,0x1121295601203003,0x212]⟩,
  ⟨30,4,[ew22,ew269,ew99,ew77,ew100],lh 5 [29,11,28,13,2,188,139,7,255,256,193,27,257,258,31,207,143] [0x3000a2948002500,0x705a26096401820,0x4e138c301bc43]⟩,
  ⟨30,4,[ew22,ew99,ew77,ew100,ew270],lh 4 [186,29,8,27,10,31,28,13,11,139,143] [0x1001059001103031,0x44224427753a6263,0x882]⟩,
  ⟨30,4,[ew271,ew22,ew99,ew77,ew100],lh 4 [10,186,28,7,29,8,13,27,11,31,199,212] [0x7114982020661414,0x3b73202013a10505,0x530]⟩,
  ⟨30,4,[ew272,ew22,ew99,ew77,ew100],lh 4 [139,10,186,8,31,13,7,28,27,212] [0x220661313850202,0x4945717120040310,0x341]⟩,
  ⟨30,4,[ew22,ew99,ew273,ew77,ew100],lh 4 [139,8,7,186,13,28,212,10,259,260,193,261,262,31,11,263] [0x300201a009800330,0xe27766d251514cb4,0x12f]⟩,
  ⟨30,4,[ew22,ew99,ew77,ew100,ew274],lh 4 [139,29,13,186,10,27,11,2,263,8,7] [0x3113106101400330,0x4648255225522774,0xa69]⟩,
  ⟨30,4,[ew275,ew22,ew99,ew77,ew100],lh 4 [27,7,186,10,29,2,8,11,139,13,264] [0x204716650504242,0x9101035321813432,0xa31]⟩,
  ⟨30,4,[ew276,ew22,ew99,ew77,ew100],lh 4 [27,186,8,13,139,7,29,11,10,2,264] [0x106558203034141,0x3003029214711262,0xa72]⟩,
  ⟨30,3,[ew257,ew22,ew77,ew100],lh 4 [11,242,139,143,29,13,186,241,56] [0x2321415080517164,0x30302]⟩,
  ⟨30,3,[ew180,ew22,ew77,ew100],lh 3 [143,11,10,242,139,241,56,265] [0x24082134f622dee4,0x1]⟩,
  ⟨30,3,[ew180,ew257,ew77,ew100],lh 4 [11,28,31,27,186,29,10,266,267] [0x8041710202615133,0x20240]⟩,
  ⟨30,3,[ew257,ew22,ew277,ew100],lh 4 [11,31,2,27,28,266,268,29,10] [0x101847420603352,0x101]⟩
]
def nodesBlock8 : Array Node := #[
  ⟨30,3,[ew278,ew257,ew22,ew100],lh 4 [11,31,27,28,2,29,10,186,13] [0x8020720101365342,0x101]⟩,
  ⟨30,3,[ew257,ew22,ew77,ew279],lh 4 [11,31,27,28,267,268,2,29,10] [0x101837360235242,0x101]⟩,
  ⟨30,3,[ew280,ew257,ew22,ew77],lh 4 [11,31,2,28,27,186,13,29,10] [0x6223521001100140,0x8373]⟩,
  ⟨30,3,[ew22,ew99,ew277,ew100],lh 4 [139,31,11,2,27,266,29,28,8] [0x4438200107600530,0x21211212]⟩,
  ⟨30,3,[ew278,ew22,ew99,ew100],lh 4 [139,11,27,31,29,28,2,8,186] [0x820131372625040,0x31211003]⟩,
  ⟨30,3,[ew22,ew99,ew77,ew279],lh 3 [139,11,27,31,28,267,29,8] [0x36515e2203130150,0x59]⟩,
  ⟨30,3,[ew280,ew22,ew99,ew77],lh 4 [139,11,31,2,28,27,186,29,8] [0x630211212510102,0x43380470]⟩,
  ⟨30,3,[ew180,ew77,ew259,ew100],lh 3 [10,188,185,11,27,31,139,28] [0x359605e546b1084]⟩,
  ⟨30,3,[ew260,ew180,ew77,ew100],lh 3 [188,185,27,11,31,10,269] [0x470a651283c28050,0x3]⟩,
  ⟨30,3,[ew180,ew77,ew100,ew262],lh 3 [10,188,139,2,11,28,185,31] [0xe690601718930c2]⟩,
  ⟨30,3,[ew263,ew180,ew77,ew100],lh 4 [188,10,2,139,31,185,270,11,28] [0x3412137001600520,0x811423]⟩,
  ⟨30,3,[ew22,ew281,ew77,ew100],lh 4 [29,10,11,139,2,27,185,186,193,31] [0x5141033010080760,0x21194252]⟩,
  ⟨30,3,[ew282,ew22,ew77,ew100],lh 3 [29,10,11,186,31,27,2,193] [0x411060755438d0c3,0x89]⟩,
  ⟨30,3,[ew22,ew99,ew77,ew283],lh 4 [29,10,11,139,27,31,185,269,186,2] [0x4191083010030760,0x21155242]⟩,
  ⟨30,3,[ew22,ew99,ew77,ew284],lh 4 [29,186,31,27,11,2,10,193,139] [0x3553028010070110,0x66423424]⟩,
  ⟨30,3,[ew22,ew285,ew77,ew100],lh 4 [10,186,11,29,196,139,27,31,188,2] [0x6090155144018133,0x20077262]⟩
]
def nodesBlock9 : Array Node := #[
  ⟨30,3,[ew286,ew22,ew77,ew100],lh 4 [29,10,11,186,27,31,196,139,2,193] [0x6609524241813030,0x21150770]⟩,
  ⟨30,3,[ew22,ew99,ew77,ew287],lh 4 [186,10,139,196,29,27,11,7,188,241,13,8] [0x5191024433108002,0xb717a656]⟩,
  ⟨30,3,[ew22,ew288,ew99,ew77],lh 4 [7,13,8,29,139,186,196,143,10,241] [0x170623215133040,0x12910280]⟩,
  ⟨30,3,[ew22,ew289,ew77,ew100],lh 4 [13,242,10,11,139,199,186,241,27] [0x170345521210604,0x12310380]⟩,
  ⟨30,3,[ew290,ew22,ew77,ew100],lh 4 [13,186,242,10,139,241,11,27,199] [0x1232076055304001,0x23621481]⟩,
  ⟨30,3,[ew22,ew99,ew291,ew100],lh 4 [139,7,241,8,11,27,270,10,242] [0x5228400103700620,0x31412151]⟩,
  ⟨30,3,[ew22,ew99,ew292,ew100],lh 3 [139,7,241,8,186,10,242,27] [0x14794f28010e8110,0xcd]⟩,
  ⟨30,3,[ew22,ew293,ew77,ew100],lh 3 [11,10,143,139,13,8,186,241] [0x241087908234d99b,0x8]⟩,
  ⟨30,3,[ew294,ew22,ew77,ew100],lh 4 [11,10,139,13,7,186,241,143,8,202] [0x1812307031615232,0x1040904]⟩,
  ⟨30,3,[ew22,ew99,ew295,ew100],lh 4 [29,11,10,13,186,139,202,241,56,8] [0x3272061020050430,0x12193181]⟩,
  ⟨30,3,[ew296,ew22,ew99,ew100],lh 4 [29,10,11,13,188,56,139,241,7,202] [0x4430212813710106,0x32550920]⟩,
  ⟨30,3,[ew99,ew297,ew77,ew100],lh 4 [13,8,186,11,29,242,56,202,10] [0x2141036001502004,0x18312732]⟩,
  ⟨30,3,[ew298,ew99,ew77,ew100],lh 4 [13,8,186,11,29,242,202,56,10] [0x155263221410204,0x18310370]⟩,
  ⟨30,3,[ew22,ew99,ew77,ew299],lh 4 [7,186,13,8,29,11,242,56,2,28] [0x2366105113432124,0x90508070]⟩,
  ⟨30,3,[ew300,ew22,ew99,ew77],lh 3 [7,28,2,186,11,29,56,242] [0x76694d50600b00e0,0x51]⟩,
  ⟨30,3,[ew99,ew301,ew77,ew100],lh 4 [29,11,2,188,207,7,242,28,143,193,139,31] [0xa009218144763320,0x15150b10]⟩
]
def nodesBlock10 : Array Node := #[
  ⟨30,3,[ew302,ew99,ew77,ew100],lh 4 [29,11,31,188,207,143,2,193,139,242,28] [0x44a9021080073360,0x12122155]⟩,
  ⟨30,3,[ew22,ew99,ew303,ew100],lh 4 [29,11,13,188,139,2,193,28,27,143,7,31] [0x2872041040063350,0x1b1a2192]⟩,
  ⟨30,3,[ew304,ew22,ew99,ew100],lh 4 [13,29,31,11,27,193,139,28,207,188] [0x901323280701615,0x4401231]⟩,
  ⟨30,3,[ew99,ew77,ew305,ew100],lh 3 [139,10,7,186,28,212,8,31] [0x2c8ac08b7a618861,0xc0]⟩,
  ⟨30,3,[ew306,ew99,ew77,ew100],lh 4 [139,8,7,186,28,212,10,31,271] [0x4141300201600330,0x12825572]⟩,
  ⟨30,3,[ew22,ew77,ew307,ew100],lh 4 [139,7,8,186,193,10,212,28,272,31] [0x5572300103300244,0x66912181]⟩,
  ⟨30,3,[ew308,ew22,ew77,ew100],lh 4 [139,7,186,10,28,212,193,8,31] [0x766558143432020,0x71312001]⟩,
  ⟨30,3,[ew22,ew99,ew273,ew274],lh 4 [11,139,186,193,212,271,272,13,7,31,264] [0x7060213305011221,0xa04498]⟩,
  ⟨30,2,[ew180,ew277,ew100],lh 3 [31,11,27,2,10] [0x2082088d2]⟩,
  ⟨30,2,[ew180,ew77,ew279],lh 3 [11,27,31,29,28] [0x82042319]⟩,
  ⟨30,2,[ew22,ew277,ew279],lh 2 [11,27,31,28] [0x122277]⟩,
  ⟨30,2,[ew180,ew77,ew283],lh 3 [188,10,139,185,11] [0x8086102ca]⟩,
  ⟨30,2,[ew180,ew291,ew100],lh 2 [188,10,185,139] [0x14be44]⟩,
  ⟨30,2,[ew306,ew99,ew274],lh 3 [139,186,7,212,31] [0x6e2202048]⟩,
  ⟨30,2,[ew22,ew307,ew274],lh 3 [139,186,193,212,10,7,31] [0x6f5212060]⟩,
  ⟨35,5,[ew115,ew116,ew117,ew118],lh 5 [274,0,273,33,154,57,32,31,28,282,275,276,277,278,279,280,281,283,284,285,286,287,288,289,290] [0x18420186601445,0x6150b5188601465,0x814217990e69484,0xa18f3924218a4e7,0x8820080200c84,0x80200c2100c03,0xaa0e700c0300821,0xc2028b90e7b1021]⟩
]
def nodesBlock11 : Array Node := #[
  ⟨35,4,[ew309,ew115,ew116,ew117,ew118],lh 4 [273,154,31,32,33,57,285,294,291,274,28,292,293,276] [0x4030c2b2a1908055,0x240024101662331d,0x771]⟩,
  ⟨35,4,[ew115,ew116,ew117,ew310,ew118],lh 4 [273,0,57,33,31,28,154,276,32,274,295,296,297] [0x52142825272030,0xb1414663101a0093,0x1c1]⟩,
  ⟨35,4,[ew311,ew115,ew116,ew117,ew118],lh 4 [0,273,33,57,154,31,32,28,279,294] [0x3121505074212163,0x5201024143050834,0x90]⟩,
  ⟨35,4,[ew312,ew115,ew116,ew117,ew118],lh 4 [0,273,33,31,57,154,32,28,279,285] [0x2161030355121244,0x3201021179030876,0x30]⟩,
  ⟨35,4,[ew313,ew115,ew116,ew117,ew118],lh 5 [28,33,0,273,57,282,298,274,299,300,31,276,279,301,32,302,303,294] [0x50920400e130ca4,0x384d0300b08c23,0x222004500840f]⟩,
  ⟨35,4,[ew115,ew116,ew117,ew118,ew314],lh 4 [154,31,273,282,33,28,304,32,301,302,274,305,306,307,0] [0x907713850536643,0xc5001b22a42214,0xe1d]⟩,
  ⟨35,4,[ew315,ew115,ew116,ew117,ew118],lh 4 [273,154,0,33,28,32,31,304,282,285] [0x7030624141303055,0x4320230019824141,0x212]⟩,
  ⟨35,4,[ew316,ew115,ew116,ew117,ew118],lh 4 [273,154,33,32,28,31,0,282,285] [0x2030661414020273,0x5200520018533141,0x411]⟩,
  ⟨35,4,[ew115,ew116,ew317,ew117,ew118],lh 4 [273,282,308,33,32,154,0,285,309,31,28] [0x7224122112211041,0x6655300330033003,0xa98]⟩,
  ⟨35,4,[ew115,ew116,ew117,ew118,ew318],lh 4 [33,308,273,282,0,32,28,31,309,154] [0x5115511431130103,0x6498022004200220,0x776]⟩,
  ⟨35,4,[ew319,ew115,ew116,ew117,ew118],lh 4 [57,32,33,31,273,28,310,274,0,308,154,294] [0x110835572620101,0x2343244209301001,0xba3]⟩,
  ⟨35,4,[ew320,ew115,ew116,ew117,ew118],lh 4 [57,33,28,32,282,31,308,273,0,311,274,154,294] [0x33055b2a1914040,0x1871127206603003,0xc82]⟩,
  ⟨35,3,[ew115,ew321,ew117,ew118],lh 4 [154,273,32,31,285,57,276,28,33,294] [0x7010443220605121,0x90038113]⟩,
  ⟨35,3,[ew115,ew116,ew117,ew322],lh 3 [273,154,32,33,31,276,285,294] [0x4604641da246d610,0x1f9]⟩,
  ⟨35,3,[ew323,ew115,ew116,ew117],lh 4 [273,154,31,57,285,33,294,276,32,28] [0x3080661205024423,0x51019177]⟩,
  ⟨35,3,[ew324,ew115,ew117,ew118],lh 4 [0,273,57,31,33,154,276,32,28] [0x8266010455141721,0x3032030]⟩
]
def nodesBlock12 : Array Node := #[
  ⟨35,3,[ew115,ew116,ew117,ew325],lh 4 [0,273,57,276,28,31,33,32,285,294] [0x6114805042332171,0x9056010]⟩,
  ⟨35,3,[ew326,ew115,ew116,ew117],lh 3 [0,294,285,33,273,57,31,276] [0x147951ac011180a8,0xcc]⟩,
  ⟨35,3,[ew115,ew327,ew117,ew118],lh 4 [0,273,33,282,276,279,154,28,32,301,57,294] [0x2616a09055443381,0x7b072012]⟩,
  ⟨35,3,[ew115,ew116,ew328,ew118],lh 4 [28,33,273,0,301,276,282,57,294] [0x1020734406051212,0x8301321]⟩,
  ⟨35,3,[ew329,ew115,ew116,ew118],lh 4 [28,33,282,273,0,301,279,294,285] [0x1312074001306002,0x14318255]⟩,
  ⟨35,3,[ew330,ew115,ew117,ew118],lh 4 [273,154,32,33,28,31,304,303,282] [0x2141700310030260,0x41152852]⟩,
  ⟨35,3,[ew115,ew116,ew331,ew118],lh 3 [273,154,32,31,28,33,304,282] [0x3a03a015da461c10,0x109]⟩,
  ⟨35,3,[ew332,ew115,ew116,ew118],lh 4 [273,154,33,31,28,32,304,301,282,303] [0x6020311410201541,0x20093837]⟩,
  ⟨35,3,[ew115,ew116,ew317,ew318],lh 3 [33,308,282,273,0,32,285,294] [0x40d8118c4d44a042,0x7]⟩,
  ⟨35,3,[ew115,ew333,ew117,ew118],lh 4 [57,31,33,32,28,282,308,273,0,154,294] [0x4472061030032005,0xa1912181]⟩,
  ⟨35,3,[ew115,ew334,ew117,ew118],lh 4 [57,32,28,308,273,33,31,0,294] [0x5242033010010110,0x28726645]⟩,
  ⟨36,4,[ew119,ew120,ew121,ew122],lh 4 [43,312,12,20,13,23,25,313,39,36,38,314,315] [0x72298a010088919,0x4775704073302203,0x8661331618330507,0x2656c55141151b44,0x64625224]⟩,
  ⟨36,3,[ew119,ew121,ew335,ew122],lh 3 [25,313,43,12,312,39,23] [0x40d816044a44a0c1,0x6]⟩,
  ⟨36,3,[ew336,ew119,ew121,ew122],lh 3 [25,313,12,312,43,39,13] [0x2421302073410669]⟩,
  ⟨37,7,[ew123,ew124,ew125,ew126,ew127],lh 5 [41,23,25,42,43,11,2,14,3,316,68,19,321,322,323,317,318,319,32,320,324] [0x3a92a3a86339124,0x790427a90a39063,0x890c48284281104,0x990219c8c68c821,0x390a4590003a8a5,0x3a50860c425a800,0x68c2160d035a442,0x68cc35a4213a4c6,0x58c0038ca35a400,0x720c6608213a4a5,0x62000708c262021,0x720a560800708a2,0x684a1a0400698a5,0xa1800]⟩,
  ⟨38,7,[ew128,ew129,ew130,ew124,ew131],lh 5 [326,14,12,36,11,8,68,57,10,31,27,28,20,60,7,145,6,2,13,146,274,5,325,327,328,329,142,330,56,331] [0x8c42b0d8309842,0x1f1701a46a1986,0x8d080180601da7,0x8ca309d0709ca7,0xd4957d5ce08c83,0xa42041ad78dc3,0xa30a204252009ad,0xcb10c0c0a50c110,0x7cdd37cc93a09da,0x4571028a5d8884,0x449c0296b044a5,0x45290288a0292a,0x7a1290a084ead29,0xac8b]⟩
]
def nodesBlock13 : Array Node := #[
  ⟨38,6,[ew128,ew129,ew337,ew124,ew131],lh 5 [14,327,11,12,10,6,60,7,8,145,13,140,332,326,20,274,68] [0x63631ce60461,0x6b5b068541005c1,0x4840050102c8b,0x2ceb0044102d0b,0x794c5004e102c42,0x7954578cc660d43,0x15050148500d03,0x4944548ce300c84,0x288448c42494e5,0x29080188601906,0x49846498e64a842,0x1042020e74a8e7,0x2042010e4]⟩,
  ⟨38,6,[ew27,ew128,ew129,ew130,ew124,ew131],lh 5 [5,13,11,57,10,0,12,20,14,7,334,60,333,326,36,146,2,27,325,8,6,274,145,335,81,142,241] [0x40c72002431a000,0x62d6d08508a34e7,0x4566d24dab5b021,0xb94aa10ac52a842,0x1cee319c7380c0,0x30030846818021,0x280320c6818080,0x7252029409038a5,0x384e6598c131d67,0x3252a4614421946,0x9086109e97bc59,0x8821606048419a,0x52521286228c4a5,0x81088921042]⟩,
  ⟨38,6,[ew57,ew128,ew129,ew130,ew124,ew131],lh 5 [5,154,8,11,57,335,60,12,10,27,20,2,36,145,336,3,326,13,325,14,146,334,7,327,337,131,56] [0x98012632400158c,0x718d04a5a5a4154,0x9843510a0633929,0x296d018ea109442,0x294c39d8a500e0,0x38043108db80c6,0x8440908220021,0x2148018c0d01064,0x5254731ce93a8c6,0x3a10f0bde8c1c27,0x8a1056e4a31bcaf,0x58d710c5685ac21,0x1144b72d234a5da,0x21890d42068]⟩,
  ⟨38,6,[ew128,ew129,ew130,ew338,ew124,ew131],lh 5 [12,334,47,60,36,57,6,28,31,20,8,7,13,14,27,335,326,3,338,68,327,339,274,145,10,11] [0x9a524890894ce31,0x24885714ada11c4,0x284a26884d11425,0x21c826884711024,0x2a0a268848115e5,0x4b9201800e72469,0x406b18d530020,0x406528cd3014a,0x3c065acd73016b,0x6498380c721b20c,0x61ce3528671b14a,0x621035ac681b16b,0x7873042021c40e7,0x709c2843c2d]⟩,
  ⟨38,5,[ew128,ew129,ew130,ew124,ew339,ew131],lh 4 [6,47,13,10,11,60,57,8,36,7,28,12,31,326,274] [0x6116811815651080,0xcb0300a25206116,0x372454e22d235340,0x4949734773]⟩,
  ⟨39,7,[ew132,ew133,ew134,ew135,ew136],lh 6 [352,0,46,274,60,340,341,23,5,22,41,7,8,51,68,345,16,154,342,54,343,344,346,347,348,349,350,351,353,354,355,356,357,358,359,360] [0x18e0ce093485185,0x5451045050820ce,0x1c80cf10f0cf1c7,0x6054105c8448588,0x416c841a645445,0x804800828a005,0x1040c21c7005285,0xc21040c61c60c6,0x2460c631d702242,0x28a0c231f786,0x41002282002042,0xc436180730c000,0x2cb0c7363884249,0x42c4004041000,0x4100d2cb000041,0xd0410092c9009]⟩,
  ⟨39,6,[ew340,ew132,ew133,ew134,ew135,ew136],lh 5 [341,23,60,361,41,7,345,274,0,340,8,313,16,154,51,365,352,22,47,46,362,363,364,54,366,367,358] [0x38e70000e794129,0x38e83084e338c21,0xb29436b6aa50dad,0x794b0422052bd08,0x489291a46000c77,0x5b5690a4c231821,0x320cb62ccd69986,0x38426219685ac8b,0xcb1871600100042,0x790875280c0014a,0xb18f29404200a0,0x794a17384c109da,0x711cf2104510882,0xe43a248c508]⟩,
  ⟨39,6,[ew86,ew132,ew133,ew134,ew135,ew136],lh 5 [60,23,46,16,7,154,0,345,274,41,340,313,361,372,22,352,51,358,68,341,368,369,370,371,373,374,375,376] [0x6326f1098c93d4a,0x400080850002021,0xb94b618ea52d1ce,0x698cf211e633484,0x50148461821298a,0x5956a084e039c39,0x398eb1ace529c67,0x1042721d6632c8b,0x10c42001010a000,0x6a522297431a0a5,0x8e2d2104948882,0x690818400300211,0x1a46d4a40400120,0x3319c9738db]⟩,
  ⟨39,6,[ew341,ew132,ew133,ew134,ew135,ew136],lh 5 [46,60,154,7,41,340,16,341,274,5,378,0,381,352,51,345,361,377,23,379,380,374,382] [0x42110001087b4a5,0x42a4d0850a8a000,0xa39ca31a6e72842,0x6108d18da423063,0x280a93a520494e5,0x48925515410a955,0x2ad69324a2114c5,0x200518d2b5a463,0x1800080e839c21,0x61080100e639c47,0xb18cc18ce421c67,0x60c681082608442,0x310cc2102308481,0x65ac4420962]⟩,
  ⟨39,6,[ew107,ew132,ew133,ew134,ew135,ew136],lh 5 [341,0,46,41,5,23,16,340,154,274,7,378,386,352,51,22,345,60,361,383,384,370,385,387,388,376] [0x480091096b83490,0x5ae2d2c52004842,0xb211531a8844cc6,0x6042d18da10b063,0x388e40108221c07,0x220894dd6529d67,0x38424310e841cc7,0x114a719c8109064,0x118424880500120,0x60c624080600100,0x298cc0840318020,0x629457170632508,0x7294c18caa51465,0xe085ea7bc39]⟩,
  ⟨39,6,[ew342,ew132,ew133,ew134,ew135,ew136],lh 5 [46,23,5,154,370,7,395,0,341,60,41,352,274,313,340,389,361,390,391,378,392,393,8,394,396,397,398,399,400,401] [0x61190001e472c42,0x611930864489000,0xb92cb18ea4a1021,0x3130b39d66598e7,0x680024084003508,0x1044d4a5a108922,0x31ce22088319099,0x42629447108a2,0x68004a50142128,0x329401811b42063,0xf0262940a000a0,0x314a11853d4a463,0x314a65282508541,0x639c6518ce3]⟩,
  ⟨39,6,[ew132,ew133,ew134,ew135,ew343,ew136],lh 5 [46,23,7,370,0,345,341,60,68,8,405,352,22,340,16,274,51,402,41,397,5,394,403,404,361,406,407,378,154,389,408] [0x681a832100034cd,0x40505394a10a0e8,0x2aca3738a328c73,0x89231108a428eb4,0x304c63980109445,0x338c64980e000e7,0xc00c0077b0129,0x48001015290def,0x3a52781c294a842,0x8c21d847ac8601,0x88412054210def,0x80843ef18b62884,0x50fd0211821308c,0xa2116a5ac84]⟩,
  ⟨39,6,[ew344,ew132,ew133,ew134,ew135,ew136],lh 5 [46,60,154,41,341,23,7,0,68,411,345,370,340,352,274,402,5,361,409,378,410,16,350,412,413,414,415,416,417,418,419] [0x700112116b8358c,0x714b30864003884,0x5aead10a852b821,0x48c6d39da31a4e7,0x50008221000288a,0x4150a0a94552028,0x61d98bd90b42c42,0x14ac319e77bcc6,0x64000808521021,0x48c6016c9a21042,0x2f0a931803000c0,0x498c51783d08442,0x48c6918c2608461,0x939c43108e2]⟩,
  ⟨39,6,[ew111,ew132,ew133,ew134,ew135,ew136],lh 5 [46,5,23,60,7,341,51,0,41,422,8,370,313,352,16,22,274,340,368,361,420,383,378,421,154,350,412,413,376] [0x814b20016b8b421,0x80c7510a852cc00,0x5af0d31ae31d842,0x49ced211a73a484,0x6000128420030ac,0x882c18d8260461,0x49cfbd656630561,0x8092102708481,0x380018ca211463,0x4a100528ae71545,0x129492100840084,0x490823186a50cc3,0x320c94204410908,0x639de87bcfc]⟩,
  ⟨39,6,[ew132,ew27,ew133,ew134,ew135,ew136],lh 5 [23,60,41,68,46,345,5,274,16,0,7,321,425,51,340,352,22,341,361,423,424,368,367,398,414,8,354,358,376] [0x755c3a0c7319a46,0x7108338c641bace,0x18065094a000c23,0x320c5c14a829ae6,0x288a6498c231525,0x384270016b8bc91,0x5af2f420e109c00,0x6252f109e94b042,0x20427000e109000,0x608445916841cfa,0x210c5288221144,0x629406b428085bb,0x689ac1080a00040,0xd4a60a8413c]⟩,
  ⟨39,6,[ew345,ew132,ew133,ew134,ew135,ew136],lh 5 [23,7,341,5,321,345,41,22,0,60,274,340,429,68,51,352,16,361,426,370,427,46,428,8,54,375,374,399,415,356,376] [0xa0c735ae431c56b,0x5114400144abc42,0x512ef39d44b1000,0x6042f421e10b108,0x5e56d135aac2c42,0x68005494a0d352d,0x19c65e14a728f63,0x2842340c6119505,0x52522008494a800,0x618c427444110e7,0x400c0844630822,0x6042073930825c9,0x719cc31801080c6,0xe420e639d1e]⟩
]
def nodesBlock14 : Array Node := #[
  ⟨39,6,[ew132,ew133,ew42,ew134,ew135,ew136],lh 5 [341,0,46,340,23,41,8,274,5,345,432,7,433,68,16,352,22,378,430,431,383,382,400,417,321,60,51,358] [0x1886d035a210c00,0x1d0699a5324b62d,0x190893a52420ea3,0x43903b8c6e722c8,0x194a80a10540c21,0x1604038007008e2,0x11c402000700882,0x118c070006009c2,0x52d602800b028a5,0x6334f3198ccbc84,0x5042f295e10a8a5,0x52d646118631cfb,0x314ca0848b21021,0x60860584021]⟩,
  ⟨39,6,[ew346,ew132,ew133,ew134,ew135,ew136],lh 5 [46,0,5,60,7,22,345,341,433,274,41,437,313,352,8,340,378,434,370,435,321,436,23,51,388,401,418,360] [0x9b1927be2c64042,0x4a2a8001284d000,0x4a2ed29528b3463,0x5a94d211aa52c84,0x3000239c40118e6,0x1604618cc930862,0x114a6d18c528b22,0x310820844421826,0xc6749ce318120,0x380729cee380a0,0x58420500010ad4a,0x5908846c681a0a5,0x7108b0846418c21,0xe084a429421]⟩,
  ⟨39,5,[ew347,ew132,ew133,ew135,ew136],lh 4 [60,46,51,41,68,0,23,154,345,341,5,340,438,7,16] [0x6160886bb6860bb,0xe00206e669901009,0xc330d0030cdd6220,0x4a7a818494411898,0x55a3a454a2a47742,0x171922977122434a,0x5233c55131151c33,0x25573775]⟩,
  ⟨39,5,[ew132,ew133,ew134,ew135,ew348,ew136],lh 4 [68,313,23,7,8,60,341,345,0,41,354,5,370,46,242,154] [0x1b01104107707007,0xd66c46aa52520118,0x8353255224e28669,0x39394383f4]⟩,
  ⟨39,5,[ew349,ew132,ew133,ew134,ew135,ew136],lh 4 [340,0,60,46,341,41,23,313,7,8,16,54,242] [0x15a9262643430707,0x517007026004b015,0x2c13353443242601,0x1515181862]⟩,
  ⟨39,5,[ew340,ew132,ew27,ew134,ew135,ew136],lh 5 [60,0,46,41,23,313,341,16,7,350,440,68,370,274,354,439,54,340,8,358] [0x708406804661965,0x280a6819e310c47,0x114a1c52939480,0x21e6408c2391c04,0xa0280a028]⟩,
  ⟨39,5,[ew350,ew132,ew133,ew134,ew135,ew136],lh 4 [23,340,41,0,46,60,5,7,22,373,16,68,341,154,354,358] [0x413232d85050c4b1,0x5016636116050199,0x270af0323248e440,0xa73727]⟩,
  ⟨39,5,[ew132,ew133,ew134,ew135,ew351,ew136],lh 5 [154,41,340,23,60,46,341,313,373,387,5,7,0,68,71,16,294] [0x700404a462421a2,0x20c8511ce23894a,0x584c1298c501805,0x8c2b1908301003,0x18160601005e0]⟩,
  ⟨39,5,[ew132,ew352,ew133,ew134,ew135,ew136],lh 5 [7,23,0,60,154,313,41,340,46,373,341,16,416,361,274,441,352,442] [0x8c234a50529ce5,0x6a14a308c2290e4,0x186208016b785c1,0x204060198c22061,0x401004010083]⟩,
  ⟨39,5,[ew345,ew86,ew132,ew134,ew135,ew136],lh 5 [341,0,7,16,340,46,313,23,361,443,274,154,439,54,60,416,358,360] [0x29d47498a628105,0x700076818128563,0x218c40880278003,0x88e032044419086,0x1882208822]⟩,
  ⟨39,5,[ew353,ew132,ew134,ew135,ew136],lh 4 [68,60,341,46,8,41,154,23,345,0,5,7,444,22] [0x2377200388303288,0xd22423dd31127221,0xc99355393c553442,0x4a6a077818878010,0x9aa5a090a4a06604,0x766141166747055a,0x64bbc551bb151cbb,0x4996bb69]⟩,
  ⟨39,5,[ew132,ew133,ew134,ew135,ew354,ew136],lh 4 [41,51,5,46,60,7,0,341,68,366,358,374,445,370,23,16] [0x2882181224b43227,0x377331c199435656,0x505e44d14aa6030,0x5051060f1]⟩,
  ⟨39,5,[ew355,ew132,ew133,ew134,ew135,ew136],lh 4 [0,60,340,23,5,46,341,41,7,345,16] [0x7aa131365652499,0x4042242131244207,0x1307075665131320,0x808080831]⟩,
  ⟨39,5,[ew341,ew132,ew133,ew42,ew135,ew136],lh 5 [341,23,16,41,46,0,5,340,60,7,374,350,345,274,370,358,154] [0x784287042068187,0x52880200610a422,0x10663156b118e8,0x8092300c8200880,0x10ca228ca3]⟩,
  ⟨39,5,[ew356,ew132,ew133,ew134,ew135,ew136],lh 4 [0,16,46,341,41,5,23,7,345,60,387,350,154,358] [0x530404c199323288,0x364050bb15aa6525,0x761d10404213126,0x70707]⟩,
  ⟨39,5,[ew132,ew133,ew134,ew135,ew357,ew136],lh 4 [23,345,41,60,154,5,7,0,46,341,387,416,16] [0x51155414aa131551,0x8998bb4830306761,0x2006033003406292,0x72727242c4]⟩
]
def nodesBlock15 : Array Node := #[
  ⟨39,5,[ew132,ew358,ew133,ew134,ew135,ew136],lh 5 [340,5,23,41,341,16,46,7,154,419,387,274,446,60,378,352,447,416,294] [0x28400042008001,0x611640042008001,0x20a0378ca5709a2,0x408e320e24218c2,0x24340c6211d29]⟩,
  ⟨39,5,[ew346,ew107,ew132,ew133,ew135,ew136],lh 5 [23,341,16,41,60,46,387,5,0,378,448,274,154,374,419,439,376] [0x5605000601120,0x94256986002182,0x284a14108371082,0x2882219ce639847,0x10e0278c23]⟩,
  ⟨39,5,[ew344,ew132,ew133,ew134,ew135,ew136],lh 4 [23,60,46,341,41,0,340,7,154,5,22,350] [0x7575a80101232396,0x6576b6801012323,0x7011054242332101,0x5484404]⟩,
  ⟨39,5,[ew359,ew132,ew134,ew135,ew136],lh 4 [5,46,23,345,60,41,341,22,0,154,7,449,340,16] [0x41226001c11016c6,0x7669617114462264,0xb88155181b551916,0x3090020343322040,0x8005038307039337,0x2924744942723530,0x9daab552aa255baa,0xd887a778]⟩,
  ⟨39,5,[ew359,ew132,ew133,ew134,ew135,ew136],lh 4 [154,0,22,345,5,23,60,41,7,46,8,16] [0x1702a26565994343,0x8120204334344317,0x217170202656581,0x100b181802]⟩,
  ⟨39,5,[ew360,ew132,ew133,ew135,ew136],lh 4 [313,341,23,46,68,0,60,154,41,8,7,450,5,345,22] [0x62336002cc20d6cd,0x9667629221163361,0xb552a2252baa2726,0x4070033414433011,0x500a045409047449,0x3731e11713e34a40,0x7988b55188151b88,0x95978875]⟩,
  ⟨39,5,[ew360,ew132,ew133,ew134,ew135,ew136],lh 4 [7,68,313,46,341,41,8,154,23] [0x5076768843432121,0x121121221311450,0x7605053443344302,0x6070505076]⟩,
  ⟨39,5,[ew111,ew132,ew133,ew134,ew135,ew136],lh 4 [0,341,7,46,23,60,68,154,41,313,8,350] [0x202775454131366,0x42020ba945453131,0x2455408083113311,0x202020]⟩,
  ⟨39,5,[ew361,ew132,ew133,ew134,ew135],lh 5 [0,68,7,341,23,46,313,154,60,16,41,8,350,451,452,453,454] [0x18020884610020,0x50d4070003029aa,0x1104080004009e2,0x11c405800700962,0x314a11842509863,0x9026420c420501,0x32d813b02b098e6,0x2a0a320c6819484,0x29ca34a46719525,0x21c884a50741129]⟩,
  ⟨39,5,[ew342,ew132,ew27,ew133,ew134,ew136],lh 5 [60,313,7,154,16,46,5,23,41,0,350,361,354,358,376,397,77,416,294] [0x680856148358d46,0x284c378c8971080,0x896010a4c108026,0x29c079086201c07,0x4090212048]⟩,
  ⟨39,5,[ew345,ew342,ew132,ew133,ew134,ew136],lh 5 [7,313,23,5,16,154,341,41,0,8,46,455,350,274,358,376,456] [0x594a25186119525,0x708866918402008,0x8c231988078082,0x1e02308010a041,0xe038007]⟩,
  ⟨39,5,[ew342,ew132,ew133,ew42,ew134,ew136],lh 5 [46,16,41,154,341,0,23,5,448,416,7,313,350,354,378,358,376,457,77,419] [0x78423704206818b,0x88c040102280426,0x182453950831ce3,0x98ca20080421929,0x1284a28862]⟩,
  ⟨39,5,[ew346,ew342,ew132,ew133,ew134,ew136],lh 5 [41,313,5,46,0,16,60,154,356,456,7,51,416,458,23,350,354,274,376] [0x719a360c2209d67,0x89508815e501004,0x8822104a0900a6,0x1812930c0401041,0xa02883]⟩,
  ⟨39,5,[ew132,ew362,ew134,ew135,ew136],lh 5 [341,23,345,41,46,60,313,7,68,16,51,8,0,459,22,402,370,376] [0x790880210423c00,0x40502288410a0a8,0x32cc28084b11a06,0x11c46618c730982,0x214a00800501021,0x22d604a40b01124,0x69ce018c0703463,0xa9454a4aa28529,0x68c61384231b4e7,0x5318e1b9cc8a86a]⟩,
  ⟨39,5,[ew132,ew362,ew133,ew134,ew135,ew136],lh 4 [313,22,0,8,68,41,23,60,7,341,345] [0x1a10400404400440,0x2531317676995252,0x7325253131767625,0x3818286863]⟩,
  ⟨39,5,[ew132,ew133,ew363,ew135,ew136],lh 5 [341,46,345,41,23,7,5,8,68,60,51,0,22,340,460,370,376] [0x685a8021010b40d,0x411024884422128,0x31cc278847119e6,0x11446598c530962,0xa4202000900481,0x9c206000700581,0x714a018c0503863,0x2294939d2a490e7,0x70c64294831b8a5,0x52d6c1b18b8286a]⟩
]
def nodesBlock16 : Array Node := #[
  ⟨39,5,[ew132,ew133,ew363,ew134,ew135,ew136],lh 4 [22,0,345,5,7,46,341,41,51,23] [0x203322332232332,0x5060566556657171,0x8014148080991717,0x1404141480]⟩,
  ⟨39,5,[ew132,ew133,ew134,ew135,ew364],lh 5 [345,341,23,22,46,60,41,0,7,340,16,68,370,402,8,51,397,461,439,462,358,463,464] [0x4908b0ad6458020,0x4892028002124a9,0x60c606000383190,0x200d3b5a8400e0,0x214a11042529044,0x239c15282e09144,0x99e41304270c4c6,0x13de5194afa0863,0xb18c24204615508,0x51ce330c671a8c6]⟩,
  ⟨39,5,[ew132,ew365,ew133,ew134,ew135,ew136],lh 4 [68,7,60,154,23,41,22,0,340,5,387,341,374] [0x6003aac080088099,0x7136362424bb1710,0x2415153636242471,0x7535525142]⟩,
  ⟨39,5,[ew132,ew133,ew366,ew134,ew135,ew136],lh 4 [345,46,341,0,340,16,154,41,5,68,23,7,60] [0x8008400440044992,0x12211a2112210870,0x6537376565ccb117,0x36353a3b65]⟩,
  ⟨39,5,[ew344,ew111,ew132,ew133,ew134,ew136],lh 5 [7,350,341,23,0,46,41,154,16,358,466,370,5,360,68,419,465] [0x4a5a8408a260567,0x38c47115c101004,0x1842280480201e3,0x298a310c040054a,0xc330006]⟩,
  ⟨39,5,[ew344,ew111,ew133,ew134,ew135,ew136],lh 5 [313,0,41,340,46,23,350,7,5,60,370,16,373,387,154,465,467] [0x580a00200820148,0x195a31918410401,0x791254906208dc3,0x11ca64982208a06,0xc709c47]⟩,
  ⟨39,5,[ew344,ew132,ew27,ew133,ew134,ew136],lh 5 [7,68,16,402,41,23,154,60,46,354,358,466,470,341,5,8,360,0,468,469,419,294] [0x52a024a502789c3,0x404231842314402,0x315ad632615ae41,0x10e5396a030286,0x8720004]⟩,
  ⟨39,5,[ew344,ew345,ew132,ew133,ew134,ew136],lh 5 [154,16,7,41,23,416,350,60,376,467,468,466,361,5,356,341,71,46,471,54,470,456] [0x2042f705a108180,0x880068010818427,0x4a66610c4390007,0xa94a4150465ad4a,0x19082114a3]⟩,
  ⟨39,5,[ew344,ew132,ew133,ew42,ew134,ew136],lh 4 [350,46,341,7,345,41,0,154,16,358,376,470,5,51,23,419] [0xaa3899e8d71212c0,0xbb34044004400210,0x65f7353512211271,0x636365]⟩,
  ⟨39,5,[ew344,ew346,ew132,ew133,ew134,ew136],lh 5 [41,16,154,7,350,46,419,354,23,467,466,456,378,345,5,356,360,60,0,472,473,374,470] [0x804e7785cd08982,0x114449883200431,0x4a4a400c0342285,0x5acc50580452aa4,0x18c318060]⟩,
  ⟨39,5,[ew367,ew132,ew133,ew134,ew135,ew136],lh 5 [8,41,23,340,5,341,7,16,60,374,387,46,274,474,154,366,358,376] [0x71da86216520c83,0x4a465214c130407,0x2882408c030114a,0x808c13040501de2,0x18802211840]⟩,
  ⟨39,5,[ew368,ew132,ew133,ew134,ew135,ew136],lh 4 [51,7,313,340,46,41,16,60,373,366,274,475,23,354,439,376] [0x510606c7b4a42323,0x1303023223884251,0x61e1540d0997412,0x1f0515106]⟩,
  ⟨39,5,[ew132,ew133,ew369,ew134,ew135,ew136],lh 5 [23,68,41,60,7,46,54,397,22,341,16,154,376,5,0,370,354,476,378,361,477,352] [0x39c23005a1284c6,0x181292bc8e20501,0x4482208a881460,0x180551516b54c12,0x1426304001003]⟩,
  ⟨39,5,[ew370,ew132,ew133,ew134,ew135,ew136],lh 4 [16,7,341,68,41,60,23,0,46,154,340] [0x17090965658282a3,0x1703393563823217,0x5014148020522617,0x474414160]⟩,
  ⟨39,5,[ew132,ew371,ew133,ew134,ew135,ew136],lh 4 [5,46,341,7,41,22,0,23,60,71,154,340,361,358,360] [0x6995008701002b0,0x365caa7878121230,0xd534141221122136,0x64544343e5]⟩,
  ⟨39,5,[ew372,ew132,ew133,ew134,ew135,ew136],lh 4 [341,7,0,16,60,23,154,41,5,46,340,361,443] [0x7136365454b099a8,0x1236365454c08071,0x4320276003400512,0x2121212153]⟩
]
def nodesBlock17 : Array Node := #[
  ⟨39,5,[ew132,ew133,ew373,ew135,ew136],lh 5 [341,345,7,46,23,60,5,41,68,8,51,0,16,478,22,340,54,455,471,376] [0x78c680210383c00,0x4110128424220a8,0x330c19042c09a26,0x8826598c230561,0x194a02000500c83,0x1a5206000900d83,0x6884039c02034e7,0x229454a4aa29129,0x69ce4108873b442,0x52d6e139cb9a84a]⟩,
  ⟨39,5,[ew132,ew133,ew134,ew374,ew135,ew136],lh 5 [23,7,345,341,16,41,46,374,457,154,376,68,8,0,479,361,356,370,60,358,378,480,352] [0x42162008e710cc2,0x1b8c31802d08982,0x442509604191e3,0x250a00040498240,0x81528360d529]⟩,
  ⟨39,5,[ew375,ew132,ew133,ew134,ew135,ew136],lh 4 [7,154,16,60,23,41,0,345,341,46,51,482,340,481] [0x621aa43439898c7,0x621714343bbd706,0x1205051212343406,0x2565505012]⟩,
  ⟨39,5,[ew132,ew376,ew133,ew134,ew135,ew136],lh 4 [313,22,7,41,60,23,0,46,341,472,154,8,5,378,358,51] [0x6991050040870c0,0x261daa5454787820,0xe12323b1b1454526,0x63133232f1]⟩,
  ⟨39,5,[ew377,ew132,ew133,ew134,ew135,ew136],lh 4 [46,341,60,0,41,154,16,22,7,340,23,313,378,448] [0x847575c2aa010199,0x43b575d2b2010184,0x2630340110212043,0x6436323856]⟩,
  ⟨39,5,[ew132,ew378,ew134,ew135,ew136],lh 5 [60,345,46,41,23,0,341,5,68,8,7,16,51,483,22,340,458,473] [0x788483210213cc6,0x411010042422008,0x3ace18842b09e07,0x8c2729ce3384a1,0x10006210c000884,0x125265acc93096b,0x694a218c452b463,0x231804a40c01129,0x68c60528031b54a,0x6158e539c52b14a]⟩,
  ⟨39,4,[ew379,ew132,ew133,ew135,ew136],lh 4 [7,16,154,0,60,23,341,373,41,313,46] [0x3030212166454554,0x21210303121277a9,0x10300808]⟩,
  ⟨39,4,[ew380,ew132,ew133,ew134,ew135],lh 4 [7,16,154,0,60,23,41,373,313,46] [0x130033060063003,0x4545121254547798,0x21212121]⟩,
  ⟨39,4,[ew381,ew132,ew134,ew135,ew136],lh 4 [340,5,23,16,41,341,7,154,46,416,387] [0x6454935382521010,0x2373011010010a20,0x34734226]⟩,
  ⟨39,4,[ew382,ew132,ew133,ew134,ew135],lh 4 [340,5,16,23,41,341,7,60,154,387,46,416] [0x4282773646541010,0xa353100109300110,0x3282b252]⟩,
  ⟨39,4,[ew383,ew361,ew132,ew134,ew135],lh 4 [68,41,341,23,46,60,0,313,350,484,154,8] [0x1042244223204066,0x705301ba1311971,0x355388]⟩,
  ⟨39,4,[ew384,ew361,ew132,ew134,ew135],lh 4 [0,7,68,341,46,23,60,350,41,313] [0x1043345334324280,0x2926521001100101,0x566577]⟩,
  ⟨39,4,[ew385,ew361,ew132,ew133,ew135],lh 4 [68,341,7,23,46,60,0,313,350,484,154,8] [0x2035531413503066,0x740012ba2122972,0x411488]⟩,
  ⟨39,4,[ew386,ew361,ew132,ew133,ew135],lh 4 [0,41,68,341,23,46,60,350,7,313] [0x1046644353624280,0x2952231001100101,0x533577]⟩,
  ⟨39,4,[ew342,ew132,ew133,ew373,ew136],lh 4 [46,0,16,5,23,41,154,341,7,350,8,358,376] [0x725c226b220a093,0x1504745131464303,0x181810]⟩,
  ⟨39,4,[ew342,ew132,ew378,ew134,ew136],lh 4 [5,51,60,313,0,41,16,7,23,350,354,46,376] [0x367c661121ba190,0x4528287404033030,0x525745]⟩
]
def nodesBlock18 : Array Node := #[
  ⟨39,4,[ew132,ew387,ew134,ew135,ew364],lh 4 [8,41,402,60,46,341,345,397,0,360,485,376] [0x1216020726622542,0x1a90308140503534,0x1b113]⟩,
  ⟨39,4,[ew388,ew132,ew134,ew135,ew364],lh 5 [341,46,439,16,402,387,397,350,340,22,345,41,374,486,358,360,487,488] [0x80010800102880,0x120e7318a561161,0x48a22809e370d0d,0x69]⟩,
  ⟨39,4,[ew132,ew133,ew389,ew135,ew364],lh 5 [60,23,7,51,340,373,397,350,77,439,54,354,356,485,489,376,16] [0x39cc60802029544,0x60d630040142044,0x789c1080034a44d,0x202]⟩,
  ⟨39,4,[ew390,ew132,ew133,ew135,ew364],lh 4 [46,402,23,60,16,340,373,397,41,22,7,354,488] [0x1a3233403021225,0x804b05115417766,0x4998c0]⟩,
  ⟨39,4,[ew344,ew132,ew133,ew373,ew136],lh 4 [154,41,350,341,16,356,376,71,470,7,5,360,468,46,439] [0x72661440b04355a2,0x31030d881220c027,0x1919e1]⟩,
  ⟨39,4,[ew344,ew132,ew378,ew134,ew136],lh 4 [46,350,7,41,360,60,16,376,472,470,23,5,356,354,154] [0x1772665440d0cb1,0x230a50992118810e,0x3a3223]⟩,
  ⟨39,4,[ew391,ew132,ew133,ew135,ew136],lh 4 [46,341,7,340,41,16,0,5,60,374,154] [0x6262a58510108393,0x110272373370101,0x54642424]⟩,
  ⟨39,4,[ew392,ew132,ew134,ew135,ew136],lh 4 [46,16,41,313,340,7,60,373,366,8,439,23,376] [0xa202019008607003,0xb161232414134334,0x15c52525]⟩,
  ⟨39,4,[ew132,ew133,ew393,ew135,ew136],lh 4 [41,68,16,23,7,60,54,46,397,5,354,341,376] [0x901918815317166,0x3252404072aab353,0x20c20404]⟩,
  ⟨39,4,[ew132,ew133,ew394,ew134,ew135],lh 4 [23,340,41,60,7,46,54,77,387,16,376,154,68,397,354] [0x911d880177211c66,0x20459e530354242,0x330bbaa]⟩,
  ⟨39,4,[ew132,ew395,ew134,ew135,ew136],lh 4 [7,41,345,341,46,23,374,457,8,340,0,358,376,16] [0xa02827792662342,0x58b5010143344335,0xd1c11010]⟩,
  ⟨39,4,[ew132,ew133,ew134,ew396,ew135],lh 5 [41,16,341,46,340,7,373,23,387,77,457,345,54,439,358,360,376] [0x4a404420e43198b,0x68060188470914a,0x785c10140518843,0x28601]⟩,
  ⟨39,3,[ew383,ew385,ew132,ew135],lh 3 [7,341,41,68,60,0,350,313] [0x7522893048203b48,0x1b3]⟩,
  ⟨39,3,[ew132,ew387,ew389,ew135],lh 3 [439,41,360,402,60,486,341,397] [0x21b00604d730bb43,0x54]⟩,
  ⟨41,7,[ew141,ew142,ew143,ew144,ew145],lh 5 [326,340,491,10,46,16,25,15,36,6,7,490,493,49,20,11,492,5] [0x216b021a800561,0x121c810521005a1,0x82068105c112129,0x820a580463804a1,0x645f16454a605e1,0x2d29010c46054a,0x10a40112402cc6,0x106402cab02c63,0x10e701144034ed,0x12463118a60354d,0x1394a11866124a9,0x138ee11946118e7,0x60ce760def614e7,0x615e5]⟩,
  ⟨42,6,[ew146,ew130,ew138,ew147,ew148],lh 5 [274,52,32,17,341,495,51,41,498,28,31,3,146,0,313,154,57,345,12,481,494,496,497,472,499,500,440,337,142,501] [0x40300401300821,0x8630398c03a82,0x289e20386300982,0x288d7b45f1ac4c6,0xcb9adc38e7409a2,0x64101063408fa,0x284c60125200461,0x28529010c401124,0x10e401144404e7,0x2c1b28d294054a,0x42d4b28c0302d2b,0x42c0b0314c0301c,0x2bce7ebdad2a54a,0x419a6]⟩
]
def nodesBlock19 : Array Node := #[
  ⟨42,5,[ew23,ew146,ew138,ew147,ew148],lh 5 [154,345,341,12,51,0,52,41,3,32,274,17,313,146,57,337,142] [0x30cc25ad4a7192e,0x100462104319966,0x1144639cc000882,0x4ad2118cc5288e2,0x90290002b0a463,0x61ce12852420401,0x429e3000270b0ac,0x6aa082a06a1a008,0x14a43910a434ad,0x85200e7]⟩,
  ⟨42,5,[ew146,ew130,ew138,ew147,ew397,ew148],lh 5 [52,345,17,51,41,58,3,12,0,146,502,481,276,32,445,39,142,154,498,503] [0x8c2c1244908161,0x1b8090004a5102d,0x3184523ca029400,0x1c467240e7318e2,0x226892088]⟩,
  ⟨42,5,[ew65,ew146,ew130,ew138,ew147,ew148],lh 4 [52,17,0,345,41,12,154,316,32,274,504,51,481,472,337,142] [0x4242b61515a09083,0x13243d36151330c0,0x116e104207760500,0x242412f]⟩,
  ⟨42,5,[ew146,ew130,ew138,ew147,ew148,ew398],lh 5 [313,17,52,51,12,146,154,41,505,506,144,301,32,445,39,337,495,507,0] [0x420600102000940,0x1b4640902c01c0b,0x1bc224a4423b842,0x318642948129421,0x48f131a03]⟩,
  ⟨42,5,[ew68,ew146,ew130,ew138,ew147,ew148],lh 5 [313,17,51,0,52,146,154,506,508,294,32,274,504,41,144,440,337,142] [0x118250958759d40,0x9420011c068c46,0x214840bc0301840,0x184501210321046,0x252310471]⟩,
  ⟨42,5,[ew146,ew130,ew138,ew147,ew148,ew399],lh 4 [32,146,52,154,0,17,345,313,58,506,3,481,495,51,41] [0x67760660500102b2,0x8948383212150770,0x5115a41413a32992,0xe4d343c]⟩,
  ⟨42,4,[ew400,ew146,ew130,ew138,ew147],lh 4 [0,17,154,41,142,51,345,3,58,481] [0x5002047030030330,0x4141566214166898,0x12712525]⟩,
  ⟨42,4,[ew401,ew146,ew130,ew138,ew148],lh 4 [154,51,146,17,41,472,506,337,509,313,52] [0x1001072010010110,0x2323494552355686,0x3423a464]⟩,
  ⟨46,7,[ew161,ew162,ew163,ew164,ew165],lh 5 [514,25,481,11,41,16,10,23,3,51,2,361,511,14,13,24,12,512,504,17,54,19,18,15,510,513,358] [0xab26c6b2185d273,0x909d98b2cc5d210,0x6bca58b1ce90ac2,0x6bcc6688a2688c2,0x3eef03c6f00ae2,0x941ce584e100863,0x584a1885c15c0e7,0xa84c15a0a86a0c6,0x4840046102088,0x9293a89ca502068,0x286a91d298a8aa,0x288a01c6701c84,0x18840186302489,0x2469]⟩,
  ⟨48,10,[ew171,ew172,ew173,ew174,ew175,ew176],lh 6 [49,36,3,25,516,7,518,519,18,60,520,41,523,11,46,17,154,58,340,2,22,527,533,32,52,51,15,0,13,16,5,10,23,8,515,517,521,522,524,350,525,472,526,528,529,354,530,531,532,534,535,536] [0x601101000897451,0x1920828d7000101,0xd21c10811c10c3,0x9172082814c1192,0x7c128120195771c,0xa127e7992514301,0x145a81341301769,0xac114555e35e55e,0xc010008218e0c3,0x28080010e08e1c0,0x700b188181184d3,0x11186d300640100,0x2c0100840b91651,0x54e68e10e145bc0,0x208183249100145,0x1c320818f24f1cf,0x4021c25b018f40f,0x1821421cf596182,0x6821831431c369a,0xc494102885961c2,0x34d30841028975d,0x28934d5492c9293,0x6db3192cbc932cb,0xcd96db3142d4554]⟩,
  ⟨48,9,[ew128,ew171,ew172,ew173,ew174,ew175,ew176],lh 6 [537,516,20,32,7,340,3,16,52,0,23,2,490,18,544,545,14,10,326,540,17,341,15,51,22,13,514,41,8,12,19,43,25,57,58,352,520,49,491,538,539,541,542,543,54,358,546] [0x8a24924a14920e1,0x186041025492,0x82000186026082,0x2802700034d023,0x6184e40240002cb,0x1c702971c000,0x10400024902a71c,0x2b104000249023,0x304120804106c,0x3c308338575d043,0x2c53850823c375d,0x4036437833434c5,0x1c54034434c534d,0x4031c3405451405,0x25f69f104405245,0x5551478510569f,0x95048514048082,0x5565504c34d055,0x1c804c64c055355,0x4c1c704c44c048,0x10c048588048448,0x4810404c59604c,0x28a3d4654382282,0x3821c23c2642394,0x4423861c63c6451,0x3e05963861063c2,0x1ca3c65863a0120,0x4cb1cb40b5ed4ca,0x6ca4cb10b78a5d7,0xb8b6db4ca10a68a,0x6d86982497976d7,0x417249698]⟩,
  ⟨48,9,[ew161,ew171,ew172,ew173,ew174,ew175,ew176],lh 6 [516,14,32,49,2,340,41,11,547,548,18,3,25,20,19,549,22,23,10,17,46,533,51,12,16,8,0,43,13,15,52,537,518,519,520,539,542,543,352,7,31,36,550,551,552,553,354,554,532,358,145,555] [0xde000029000082,0x22030c0007de000,0x5d726134d2615d7,0x631043e228a220,0x4103e21043a328a,0x6b61806a492064,0x1c73a5186064492,0x651c73a6186066,0x2c0000c30027c2,0x2423022052cb000,0x1052053052422c2,0x421023822823c5,0x6050424823c528a,0x42602045492045,0x1db39b1860451c5,0x144d338518505b,0x34d0034d3003343,0x71c014294014,0x40300370302d28a,0x2f41000066e003,0x1c7003183003643,0x31c3014194014,0x45325310420c44c,0x20d64d24d104213,0x55520b64b24b570,0x24c1c720b9cb24d,0x55524b74b20c9cc,0x3c45440445b13d1,0x1913c4744391596,0xcc41863d1751c91,0xa1005069a396a16,0x5669a390]⟩,
  ⟨48,9,[ew171,ew172,ew173,ew174,ew402,ew175,ew176],lh 6 [49,520,539,556,20,57,6,41,11,490,19,557,558,18,32,10,16,23,7,533,52,17,493,8,51,516,12,313,46,22,25,518,519,374,36,559,560,13,358,542,551,561,543,352,562] [0x5050c500028e50e,0x2c568528e0000c5,0x10430e69a30e10e,0x450850410612c5,0x620c564504134d,0x28540528e3ce041,0x20528e4102853cf,0x59b21b59b4928c5,0x1862dc55528e492,0xdc11c3005400c0,0x3540d40d4040340,0x899090c00c0054,0x6490800800c0640,0xc95c92807400c9,0x1c00c05d7289749,0x5891c90c9209280,0x34d2de45e0c0200,0x30434d2d5455315,0x7c43048042c67c6,0x2c45c43068062c4,0x4d32c65c63064c6,0x3062062c41c4304,0x6513042042c61c6,0x514d30420650d1,0x6180414d3042626,0x511d104d48d051,0x3cf04d1c7051492,0xa93cf0a86180a7,0x1c70aa208082410,0x821c70ab208082,0x1c758f2082901d0,0xb1021058f]⟩,
  ⟨48,9,[ew141,ew171,ew172,ew173,ew174,ew175,ew176],lh 6 [520,539,57,563,46,13,32,7,3,565,566,11,49,14,17,60,52,51,22,20,10,16,25,58,15,41,493,516,12,313,518,519,2,145,36,537,564,23,551,567,542,352,543,568,492,376] [0x4100000220db186,0xdb4100db30c063,0x59625e20806430c,0x25e59629f20829f,0x4510000650db820,0x41451067492066,0x1c70412cb068492,0x6a1c70412cb069,0x4020c230c346406,0x24270234630c0c2,0x4d328671c2864c6,0x2042000145242,0x48234650600002b,0x346486342514342,0x2dd69d1c73422c2,0x24438e8421c269d,0x4c428c38e0cc4d3,0xd01450040040c4,0x5440c4144010050,0x3575570d7514344,0x2c48576170c4504,0xd72d76846180c4,0x3cf28e14e2533d3,0x24e55529314524e,0x50e248548288514,0x2966182481c828e,0x5552886082561d6,0xf54f00f44f005,0x64f0051c5005451,0x565900f1c700f,0x6526922edb11659,0x3512cb692]⟩,
  ⟨48,9,[ew171,ew172,ew173,ew174,ew175,ew403,ew176],lh 6 [523,49,551,569,13,52,570,572,18,345,12,573,11,17,41,20,571,22,3,2,68,7,46,25,533,15,23,51,14,19,16,516,542,0,340,402,8,58,518,519,520,527,67,36,354,574,575,532,358,539,143,576,10,577,543,578] [0x1540d4041722162,0x1942947220410d4,0x3cf1d02901d03cf,0x7492082d0110194,0x2a2d0210709109,0x79e009089000,0x30900002b0c97c9,0x823323823555709,0x3cf19634d749555,0xd63d61c13410c1,0x2050c51042c1201,0x57850c1104745,0x9240257a50e592c,0xc17c1085b450c5,0x3810c57c5081081,0x8163960d630c741,0x22e1976970c1301,0x1d720818d68d1cd,0x4521d262f18d44d,0x18a98a1cd618192,0x9ca1929921d29d2,0x1d765918a54a1ca,0x6181ca659197557,0x2d36130136f02c8,0x932c4a040086db,0x84c442d3a13093,0x65a81a3b22c4644,0xd17d1cc438e2da,0x86101b38e002034,0x1b861011391011,0xa908230c0b60b5,0x8230cde9]⟩,
  ⟨48,9,[ew149,ew171,ew172,ew173,ew174,ew175,ew176],lh 6 [523,49,41,579,52,581,25,582,10,18,3,23,17,583,14,13,345,154,2,20,7,19,11,584,68,571,46,15,340,516,0,402,58,518,519,520,539,22,551,543,527,12,36,537,580,350,585,586,587,588,589] [0x10400002a0dd71c,0xdd1040dd0413ab,0x18616128a3ac041,0x1611861e228a1e2,0x4925642cb363492,0xdd2253632cb3a4,0x823a75960009a5,0x5670825e85965e8,0x1180d804139c104,0x158a5839c0410d8,0x4d31d9a591d94d3,0x5502493593d9158,0x2083592493903d0,0x2d010990000,0x59f5df514390590,0x15a30c5505145df,0x4da1c13010c14d3,0xc43cf3412410da,0x40c13c1544244,0x20be00e022e004,0x5145410810c1230,0xc15015da09a0da,0x2cc1cc3cf1462c6,0x14c44c1c63c614c,0x20c14a44a1ca208,0x1c66c614a08a1cc,0x2081ca6db146082,0x35221201245134b,0x823496c9009451,0xc4908934b6cb5cb,0x8201179e000082,0x3279e011]⟩
]
def nodesBlock20 : Array Node := #[
  ⟨48,9,[ew159,ew171,ew172,ew173,ew174,ew175,ew176],lh 6 [527,590,49,11,36,3,2,25,46,592,593,340,543,23,595,594,51,22,58,32,14,17,20,0,18,13,533,8,516,16,52,10,518,519,520,539,523,7,402,537,591,596,559,74,597,598,354,532,358] [0x8200002605c104,0x5c08205c208327,0x1c7260145328208,0x2601c72a11452a1,0x18632334d3e2186,0x3a44103e234d323,0x45130c75d329451,0x32505c5e53a4,0x784044082513492,0x24b145513093044,0x1cb2841442841c4,0xa936133cb18b24b,0x7c43cb618513193,0x50b7df50b74b384,0xc300002b384744,0x24855500b30b000,0x596282555042582,0x5e65e3c8608048,0x44204266db1e618,0x5124520526ee382,0xc30123120426db,0x520d2008008048,0x355295659247347,0x2566d6296659255,0x69a2456c52856af,0x2870c72455c5296,0x69a2850c32475c7,0x3c66865064303cd,0x5d73c60c638d410,0x65c63cd0c300d,0x3910110c3390390,0x100d0391]⟩,
  ⟨48,9,[ew404,ew171,ew172,ew173,ew174,ew175,ew176],lh 6 [527,599,36,2,46,601,602,10,16,340,543,3,23,25,603,41,20,49,604,58,19,52,13,7,32,18,17,15,51,22,516,506,146,27,518,519,520,539,523,154,11,5,600,605,551,145,77,358,492,376] [0x45100002905e082,0x5e45105e7df28a,0x82016234d2aa7df,0x1628201a334d1a3,0xc32a58613a40c3,0x4a675d3a48612a5,0x9e72ac2082ab1c7,0x2a805e3e84a6,0x5420424515184d3,0x1492cb518451042,0x3491822c2182342,0x5186583890c9149,0x1c2389659b580d8,0x5091c7509209482,0x3cf009289482202,0x14469a00002e000,0x41019569a055415,0x55595384644044,0x204044596515659,0x5132130531c7484,0x5c40136d30441c4,0x535d70046db044,0x30c19a596150310,0x15020819059615a,0x1d014b20b18b1c7,0x18d6db14b5cb190,0x20c18b6cb14d5cd,0x383203c0372f38c,0x3cc3835c348c71c,0x33cf38c5cc00c,0x3dd01d03149c3cf,0x1c29c49d]⟩,
  ⟨48,9,[ew142,ew171,ew172,ew173,ew174,ew175,ew176],lh 6 [516,52,520,18,340,539,36,32,20,606,607,7,12,11,341,17,41,10,16,22,8,15,3,608,23,25,609,51,326,19,5,518,519,2,523,527,537,49,543,553,597,598,358,376,610] [0x1c715c1861641c7,0x4115c186145,0x20825f6590000a5,0x25f2082a03cf2a0,0x4d30000210000e1,0x1454d315c5145e2,0x2cb1454105e2514,0x1662cb6a35556a3,0x46006006007047,0x24430c0079c7006,0x3c428630c2863cf,0x870c3084084244,0x4460840c4087147,0x7444517445045c6,0x555a043445c6514,0x74454469e35e69e,0x3c100130c00e3cf,0x20c300e30e001,0x481000029001001,0xe49200e44e001,0x34e001541001441,0x134100e54e00e,0x61828c0cc248608,0x2484882880c324c,0x448256496296451,0x29934d2562d6288,0x4832963562592d9,0x824920856ea083,0x4180832cb0836db,0x834100982cb098,0x41369336b5db410,0xb1b34d5d3]⟩,
  ⟨48,9,[ew150,ew171,ew172,ew173,ew174,ew175,ew176],lh 6 [516,36,58,523,20,7,340,13,32,613,614,2,615,11,23,25,22,12,490,3,14,616,18,15,533,41,617,17,51,16,0,5,341,49,518,519,520,527,19,537,611,551,612,539,8,543,554,586,356,532,358,618] [0x208528041527208,0xa152a041529,0x1042623cf0000e1,0x2621042a33cf2a3,0x2cb56b1c73242cb,0x4103241c7555,0x14555534d00002c,0x56d1456a534d6a5,0x81001001008082,0x246451008b88001,0x106281451281101,0x9885883061c6246,0xc13065965081c8,0xc6bc60c64060c1,0x1455063460c1401,0x98614569f35f69f,0x6c20024510206db,0x12596020460002,0x1c70025820021c2,0x1201200375d012,0x3520025c2000030,0x23420125d7012,0x38e29b1c7244384,0x2447442841c425b,0x618253753293631,0x28f5d7253153284,0x6182935d324f14f,0x30b60b0cb73230e,0x64e30b14b0ce71c,0xccb65930e14568e,0x6500d079e0dc659,0xdc79e0d0]⟩,
  ⟨48,9,[ew171,ew131,ew172,ew173,ew174,ew175,ew176],lh 6 [516,16,32,3,25,5,49,18,527,543,621,2,15,154,36,52,622,623,41,624,340,58,533,60,10,20,146,27,23,19,22,518,519,520,539,523,11,537,619,620,145,46,625,616,39,51,626] [0x9c524598524e94e,0x23c224e24e245,0x18600e3cf00e18e,0x4021022850c5002,0x2ce2851054020c2,0xa022c27421c244e,0x79e4c260244e1c7,0x4c2782754614754,0x205205305214254,0x18621430c205,0x69a29f659000229,0x29f69a420659420,0x1c72626db4611c7,0x4e30414616db262,0x34d26b04126a618,0x240004a44e3,0x1060060c300a104,0x67060000c3006,0x2c600f70f00f2cb,0x1534d00f04f006,0x2c00f34f015055,0x15015008492000,0x7034032cb284704,0x2840414042cb283,0x596283041403583,0x404304283492404,0x59640330c284484,0x457041b8bb4b447,0x49744730c4c734d,0x207487457317217,0x30d20d20d4c1301,0x2012414cd]⟩,
  ⟨48,9,[ew171,ew172,ew173,ew174,ew175,ew405,ew176],lh 6 [520,36,52,11,49,627,3,629,51,539,523,32,628,2,41,20,340,60,25,17,15,154,632,46,516,14,5,28,58,518,519,7,527,630,551,631,492,445,633,616,626,337,358,18,16,543] [0x8114110464b08b,0x31018664b10b141,0x4901c11811c1481,0xb24b010350310,0x54101001000b34d,0x290555290210281,0x88b241841281208,0x2418c124b24b24b,0xda59a38e6410c1,0x31749290138159a,0x3cf1c44c41443cf,0x14234d004004157,0x202144344002242,0x29c21c15c6e5282,0x6022449841426db,0x1446042429c2142,0x3971570c3a02382,0x30f4521420c2597,0x34f3134531d334d,0x1c61e93132131cf,0x74f1d31d3306206,0x3067461c678630f,0xc33067c61cf78f,0x1c65063127d21d2,0x20801101100002a,0xa02b15161100a,0x51101139100d514,0x14860800d38e011,0xc328838e00002c,0x2880c3295395295,0x5145a00c326d514,0x2490c35a0]⟩,
  ⟨48,9,[ew145,ew171,ew172,ew173,ew174,ew175,ew176],lh 6 [46,520,5,634,32,635,25,636,539,20,41,22,527,18,52,10,637,0,16,58,3,2,12,13,340,51,17,36,493,49,516,154,518,519,60,523,11,546,555,576,588,618,358,489] [0x6db21c0822086db,0x20875d21c082208,0xde75d0de000,0x1e118616024921c,0x5621601861e1249,0x4237df0413220de,0x2cb2087df21c2cb,0x410640de2a4423,0x38e0c2000944384,0x1425829840040c2,0x1861c45961c4184,0x443440425c2142,0x3c404234d0445d7,0xa183d89d82cb404,0x2823184584042c4,0x31828a302442302,0x68e0ce596140186,0x403400c05801ce,0x5c004e34d0ce5d7,0xd33cf4004800c0,0x2930c03c0a53493,0x3002800c0440313,0x35a1491490d3453,0x1c934915a15a1da,0x4941d43cf149489,0x1542941c93c9154,0x1d41462861c61c6,0x5566a04d4921d4,0x5504d659055495,0x4106b04c28a055,0x28b30b44b419299,0x31945140b]⟩,
  ⟨48,9,[ew153,ew171,ew172,ew173,ew174,ew175,ew176],lh 6 [523,23,5,46,638,32,25,11,527,52,543,20,639,640,2,13,641,12,0,340,58,3,16,533,8,51,36,49,516,542,14,518,519,520,539,22,551,616,41,562,589,610,354,532,358,642] [0x69a29d08228a69a,0x2a56db29d0822a4,0xc311c6db11c0c3,0x36018631f2cb29d,0x38e31f1863602cb,0x2a238e2a2041421,0x22311c5a3421041,0x2611c492000,0x2491020c3785245,0x3024427850c5102,0x186345451345185,0x9c50454023c2302,0x54020417853cf,0x13a13013596005,0x2022131d3005585,0x2132932021c2202,0x189109451303186,0x403041103451349,0x3cfa490491093cf,0x11462a009589103,0x294109618014594,0x2032031031c7214,0x3cf30b04b1141d4,0x34b3cb311041351,0x6153555eb30b60b,0x31549534b5d7315,0x1d53064863461c7,0xe66c4015d7355,0x1ce00165940e5ce,0x4011c720149240e,0x1c701901920e48e,0x2d008]⟩,
  ⟨48,8,[ew171,ew172,ew173,ew406,ew175,ew176],lh 6 [556,32,14,7,52,3,340,25,18,490,23,19,11,15,2,57,13,10,514,341,533,8,20,22,17,16,644,539,43,274,58,643,537,326,532,645,358,376] [0x10f00f00f00179e,0x8f14500180100f,0x5960811412c1581,0x12010064102cf,0x441846206001410,0x864510865c6081,0xc30863060815c1,0x2c60c649c31c49c,0x61800459f01361f,0x9208013593004,0x409013208013413,0x9449004644009,0x344004451009659,0x934d009309004,0x208747287004304,0x74720769828a698,0x6450855222c7647,0x7450c52c7514085,0x3454870c3487347,0x68e5642ca5148c5,0x34e68a55508e50e,0x6ca34a6ca0c36ce,0x3252d50d56ce0ce,0x9530c4970d7497]⟩,
  ⟨48,8,[ew171,ew172,ew173,ew174,ew175,ew407,ew176],lh 6 [569,14,32,68,52,3,490,23,646,2,8,20,7,41,17,647,514,0,341,649,18,13,15,516,537,12,43,25,28,11,518,519,520,539,16,352,54,648,242,650,19] [0x103003024002102,0x43143002602003,0x2cb2026422022c2,0x425023c3243043,0x423c3514042242,0x43043003283042,0x30025c2042282,0x429420035c3003,0x75a41a30c043743,0x1238e04330c41a,0x65200438e004659,0x12552006514012,0x4006555012512,0x6006006286004,0x5c600400400428a,0x45c4006006006,0x596006306004584,0x3cb1cb004304006,0x54b4ce1c720e555,0x2052054cb28b20b,0x78e20b20b4c5285,0x4c57852057c54ce,0x5964c530520e7ce,0x2055854db31b21b,0x2890497263c7287,0x3c780704771c3c9,0x8473c9809049849,0x4073473c9309047,0x5e29c934d3c730c,0x4a34d61862200a,0x45141034d410451,0x42345106834d04a,0x4145142334d]⟩,
  ⟨48,8,[ew145,ew128,ew171,ew172,ew173,ew174,ew175,ew176],lh 6 [52,41,490,32,20,340,22,651,3,2,17,634,51,18,43,540,25,10,16,652,12,0,8,13,537,653,516,31,539,520,341,544,545,635,636,655,656,493,23,7,36,49,650,542,654,543,54,358,489] [0x60771c1d39581d8,0xc364e3930c3607,0x68208b00064e393,0x41f2082c209a000,0x2497d0420208810,0x64619330c3d399a,0x9da04164619330c,0x822cba0b38e3cf,0x88412128a2c7a4b,0x71d24984412228a,0x18674f74f2493c7,0xad6587186a96587,0x6c7041b1b6c7041,0x1c32c208b2eeb5b,0xd4503103154503,0x5c3343157145105,0x5850d10c534d0d7,0x155143583151445,0x28504539538e041,0x51e00a00051478a,0xd0005c008d35e,0x4824420120025c2,0x542001000440092,0x123100540081042,0x1043442a328a34a,0x444212208451112,0x401410910201204,0x24932f352488908,0x4124f24d30c252,0x19518c04c3cfc13,0x315546046]⟩,
  ⟨48,8,[ew171,ew172,ew173,ew174,ew175,ew408,ew176],lh 6 [579,68,58,46,20,14,10,32,660,23,11,3,41,657,658,2,7,13,659,17,15,154,18,516,49,12,43,25,518,519,520,539,543,352,542,0,337,145,16,19] [0x81001618007087,0x341641007607001,0x101387659387104,0x147596481441341,0x186481581147451,0x1181141141207,0x5c1207887207147,0x75c7001001001,0x29a21a4101418c1,0x34d314141021a,0x1030024d3002102,0x2451003583003,0x3003443002582,0x2002002182003,0x5c2003003003183,0x35c3002002002,0x514003283002502,0x34424400228a003,0x444353249393453,0x38b1a4344544384,0x70438418634b54b,0x34b70b38b74b344,0x51434b40b384744,0x38b50b35b41b39b,0x18f14f555489186,0x48978920955548f,0x7c948f78f14f7cf,0x20930948f40f149,0x5c694f30c489410,0x22730c145166006,0x28a20630c206286,0x22128a16030c205,0x16028a22130c]⟩,
  ⟨48,8,[ew142,ew161,ew171,ew173,ew174,ew175,ew176],lh 6 [549,46,20,662,16,7,32,52,341,663,664,18,10,14,11,340,23,516,12,43,3,665,41,520,49,51,537,17,15,19,25,22,661,13,552,326,36,598,358,376] [0x1c70005d70011c1,0x81a4d30015c181a,0xe20014c10c10c1,0x2980822416c10da,0x2e12410822986db,0xc1101451461441,0x3010c31040e330c,0xc11410d87180c1,0x4c70d81450c171c,0x248082451464447,0x492287087287487,0x80c80172cb248,0x1040170250082cb,0x348108348308347,0x38874714534730c,0x34738e548148548,0x48628608224f492,0xf00f24f082286,0x2cf0060c60062c6,0x34f10f34630600f,0x38634610434f30f,0x553393553145346,0x2cb242402746146,0x2822c2252410292,0x11429430c242104,0x254154282302254,0x39425e15e29e38e,0x3666010110294,0x145010659000104,0x1015001059000b,0x3a775959600b596,0x35938e55f59f55f]⟩,
  ⟨48,8,[ew150,ew161,ew171,ew173,ew174,ew175,ew176],lh 6 [14,32,660,58,49,20,18,667,668,46,7,16,17,669,15,490,340,13,516,11,23,12,3,2,41,537,51,542,22,43,533,25,666,662,341,552,8,36,316,532,358,492,376] [0xc30196d90040c4,0x8190410846c4819,0x23004041004004,0x2041441c930c019,0x1891c914520430c,0x21186021451349,0x4a4489709349449,0x89289004384492,0x4100428a08938e,0x1e21454924a5483,0x555203143203543,0x344334f1861e2,0x2cb34f451003183,0xf2cb00f00f09b,0x4cf00328309b026,0x34d308f28f08f,0x5412011451d0555,0x3504501d0145201,0x186001441001181,0x102d0081001350,0x4c10812c1010010,0x9d4dd09d28a001,0x1861c550500128a,0x2051861cc50c20c,0x2d62167a71cc2cc,0x1d629620c79e1d6,0x38e1df29f21f38e,0x176a83542cb216,0x39709469a3572d7,0x35438e094614357,0x4ea09a618a57618,0x9a4d309c61c09c]⟩,
  ⟨48,8,[ew145,ew161,ew171,ew172,ew173,ew174,ew175,ew176],lh 6 [32,20,49,13,46,340,634,22,41,662,51,43,549,18,0,31,25,17,12,3,665,2,10,16,8,533,539,516,493,547,548,23,651,635,636,520,542,543,671,672,673,15,36,52,145,670,552,354,492,532,358,489] [0x70969a50970969a,0x50b2c9000509,0x6c410608250b2c9,0x41d04118411b082,0x55f75041e041790,0x5071c928a3097db,0xa5b2085071c928a,0x104186a862cb30c,0x8924a10411a0ac6,0xe334d8524a2041,0x1c78c30cc34d303,0x9165ad1c7b165a4,0x3a620898e3a5208,0x1ae18410080094e,0x12000040152486,0x340143145041,0x5c5016005345003,0x14e1405d7156145,0x4452052ce2cb208,0x44091082041111,0x30d3460c308d084,0x5c662f0970820c3,0x3c4088082618c17,0x670423cf108204,0x6010c34674510c3,0x6594d84d3671458,0x40f410a104cf4d1,0x5552b20d9653a13,0x3cf54c54328a559,0x1ce1ca3ca30ccc9,0x28e3873c7]⟩,
  ⟨48,8,[ew159,ew171,ew172,ew173,ew174,ew402,ew175,ew176],lh 6 [46,20,57,11,23,10,18,16,674,32,490,6,0,594,51,49,676,52,25,22,12,17,556,590,14,493,557,558,520,679,592,593,313,675,661,516,677,678,7,374,36,301,13,358,542,680] [0x223cf848816082,0x416000163cf580,0x69249b0416d249a,0x10d18634411c186,0x1c74086565e3704,0x9534c81c76134e4,0x94492089960c3,0x502240242442080,0x92089514252242,0x8d10409008d367,0x4c224524d368097,0x219a494c9085142,0x5005550880880c3,0x180014011555454,0x1d01118645d440,0x28040001700a60a,0x1c72852801c0297,0x28328f20f00500a,0x1811013c33ca64a,0x78b046055104546,0x2df2c178105f04b,0x4b1cb2c52c11c1,0x30c2c32c1301045,0x40da845c404304b,0x38d1c740eac41c4,0xc310c3060c610e,0xb4e3ac14518c304,0x30d0c340e398145,0x20e40c3080c340c,0x3830c564514314e]⟩
]
def nodesBlock21 : Array Node := #[
  ⟨48,8,[ew171,ew337,ew172,ew173,ew174,ew175,ew176],lh 6 [556,490,681,7,57,32,18,20,682,683,16,12,11,17,8,14,23,340,15,533,3,684,41,516,19,51,539,10,43,512,685,25,22,518,519,542,543,352,520,52,13,686,532,358,376] [0x5c40040040055c5,0x5041085985004,0x605004044004004,0x2451c72042c4005,0x912041c42452cb,0x84684004184091,0x2913c56c5091191,0x3c528a3d16db3d1,0x31c55c0c33c5305,0x170416050c355c,0x2cb22134d0006a7,0x2212cb26234d262,0x186000000017186,0x76328a017028082,0x38e74f28a78f38e,0x5650c376430c7a3,0x34d7a40c356530c,0x13410012cb008,0x290011810001c7,0x1001002186000,0x28100138101828a,0x1849200038e001,0xc30014920010c1,0x24d186207407000,0x38724718720d410,0x2143942544ea207,0x4922140d42474d3,0x25449421f0df25f,0x4d309a66b0904d3,0x860c3090659082,0x5960900c3090590,0x56032c619596086,0x3d930c5605a0]⟩,
  ⟨48,8,[ew409,ew171,ew172,ew173,ew174,ew175,ew176],lh 6 [583,20,68,58,2,32,10,3,14,687,688,41,46,18,689,23,551,49,11,15,690,17,7,340,520,516,313,678,25,495,518,519,543,352,51,19] [0x5d70181450005d7,0x2080c3410145018,0x4512590c3259451,0x39f04129e1c7748,0x10429e04139f1c7,0x10400034d018,0x42225918601834d,0x5212cb220492410,0xc37602cb521492,0x2420c2242451205,0x412821c2205451,0x2820423851c7385,0x104005345002102,0x40518500234d005,0x405002182402402,0x51a2cb202482405,0x55520258251a49a,0x39155525104128c,0x10400c34c24c04c,0x24c10c00334d243,0x2032431836cc20c,0x2034c324c186203,0x58350c4d324c58c,0x3953552813c1243,0x2813813412953cf,0x287287387186281,0x4d3287587381181,0x3874c729c59c39c,0x18400400400f18f,0x44c400f00f004,0x2cb00f4cf00f2cf,0x5064866e32cb004,0x6c84925062cb]⟩,
  ⟨48,8,[ew153,ew171,ew172,ew173,ew174,ew402,ew175,ew176],lh 6 [20,11,52,23,57,313,32,674,18,691,490,46,6,0,641,51,16,533,49,17,678,8,556,3,25,638,543,542,12,14,493,677,58,557,558,520,539,680,692,639,640,551,22,675,41,374,36,13,358,642] [0x15f186505147186,0x49258b2c7820505,0x8986215d750b2d6,0xe32088586225d7,0x69a8c30ce208383,0x2476df969909909,0xb16041ac7a96410,0x841124850851c7,0x180184704152484,0x10e3ad10000671c,0x3ae11910e0c3109,0x11d10440415414e,0x145785181186410,0x2d34c61c6141,0x2c82cb00b0934c2,0x28b98b088082982,0x64a08908264229d,0x29028a54a09008a,0x28a04a087082555,0x20800300204229e,0x3273002004c30d3,0xca0c027000a00,0x45131530c44c015,0x30d34c04c00d000,0x4493af0d90c0041,0x3cf3914493f00d1,0xc104334d201043,0x7653cf6c96c8348,0x34d6810493cf509,0x3c73c934d1c1049,0x1dec47041]⟩,
  ⟨48,8,[ew171,ew410,ew172,ew173,ew174,ew175,ew176],lh 6 [563,49,20,549,57,32,10,16,7,18,693,694,13,14,340,11,23,15,12,695,3,665,17,46,2,41,516,51,533,43,25,22,36,537,518,519,542,543,352,520,52,358,376] [0x40046a00c59e0,0x5845005685004,0x41004004004044,0x2c5085284484005,0x30c2840822c5492,0x43040c42440ce,0x1ce3451850ce24e,0x3451c734e18634e,0x3dd55d20834e3ce,0x1a04134e20855d,0x4922a2082000868,0x2a24922e30822e3,0x24900030c01a249,0x4e41c701a30c0c3,0x1864cd1c74d3186,0x5663cf4e52084e4,0x5964e53cf566208,0x1581001082017,0x30c001241017097,0x1301003249000,0x1c70001860011c1,0x144100118100d,0x201017451017217,0x2d6256282402001,0x1c22c2242296410,0x2941d42d4186282,0x4512942142c2702,0x2d445429e21e2de,0x7180d86e90d071c,0xd84580d06db0d8,0x6590d04500d0650,0x55f3ea35b6590d8,0x35b3cf55f65f]⟩,
  ⟨48,8,[ew171,ew172,ew173,ew174,ew175,ew411,ew176],lh 6 [573,68,32,13,17,60,52,14,696,20,41,46,697,698,533,11,700,58,7,3,49,699,22,15,539,520,12,313,8,16,516,25,2,495,518,519,543,352,551,354,532,51,376] [0x1812015141c2182,0x3016811c2514201,0x24934269a342242,0x2602001801301,0x1c2001001002802,0x1c11c1001581542,0x1002642542582,0x542982001641001,0x3db41b28a1c13c1,0x30b1041c128141b,0x24b354104214249,0x2060c600b00b20b,0x58b20b0c3006606,0x1d175121172754b,0x7918461c620b71c,0x2067861d11d1211,0x5d720b48b1c65c6,0x30914920649240b,0xc93041453440c3,0x3533a8309749349,0x88434938e313753,0x3138933538d3304,0x5d73044843448c4,0x3445c431f49f35f,0x38e00500500338e,0x3643003003005,0x3005645005005,0x5285003483003,0x78e00328a005485,0x54e28a61862920e,0x3cf4162964163ea,0x4253cf86428a54e,0x1e43cf42528a]⟩,
  ⟨48,8,[ew171,ew412,ew172,ew173,ew174,ew175,ew176],lh 6 [569,68,32,52,7,2,701,20,16,702,703,14,704,18,8,15,17,23,12,3,533,41,516,11,705,22,43,506,25,51,402,13,551,58,518,519,520,539,543,352,36,523,532,358,706] [0x58100100101e59e,0x20c2182a68001,0x2c20010c1001001,0x2821c2241481002,0x7c12411c1282492,0x2c27c22c2342301,0x201182182301341,0x182202181801001,0x5da61a1042c25c2,0x160e12c210461a,0x1c7262492000821,0x2621c72a34922a3,0x34d2e514532434d,0x162083241452e5,0x38e18620800038e,0x6271042e63cf016,0x4102e61046273cf,0x34030031c7009,0x14300c34d0001c7,0x145003343003,0x20800038e003203,0x33c3003383006,0x10301b3db01b104,0x290150247447003,0x208287145250451,0x25321329352a250,0x3cf253113290514,0x2933d325c11c29c,0x50518576b311514,0x30510519175d305,0x555311104611551,0x1995d918e555b05,0x18e5d7199559]⟩,
  ⟨48,8,[ew145,ew171,ew172,ew173,ew174,ew175,ew403,ew176],lh 6 [13,46,41,52,12,49,25,670,18,402,20,51,345,58,0,573,22,637,68,3,707,16,571,17,8,533,340,569,551,634,700,31,2,570,572,23,523,539,708,635,636,709,520,543,493,7,67,36,354,706,532,358,489,10,352,710] [0x25469a78925469a,0x1456c1054145789,0x8861a128a78105b,0x8db0238461a228a,0x5554504242cb3d4,0x707707965910411,0xb5b0821d4b1c1dc,0xd24810490c93cf,0x586192112241052,0x216016486496116,0x46e58820c00c308,0x31d311555307311,0x24908230e31146f,0x1040575cc08224e,0x148141281157145,0xc50050c80c3000,0x61835534d6300d5,0x34734d74d0f10c3,0x417c1342343743,0x2a628d7df042,0x29860a0005e65d7,0x10a6594d84d3672,0xa044e74d3a13127,0x182186a46102104,0x8202f3019644a44,0x3c802a0082cb819,0xf0003c022a208,0xd4b74b3cfd14082,0x9040e40b08b1d1,0x1ce3ab1eb2ce390,0x1ce3b71f6]⟩,
  ⟨48,8,[ew171,ew172,ew173,ew174,ew175,ew413],lh 6 [595,340,20,46,36,711,712,713,18,41,7,23,714,17,58,3,32,49,13,15,533,2,22,543,8,51,52,12,14,402,25,11,19,0,16,551,354,532,358,376] [0x684144451710690,0x1816db710451144,0x821c46db1c4084,0x810210301481181,0x4301208710492,0x18c1001581004,0x249001841004584,0x12815dd85d01d,0x34d15108218334d,0x3032031430831d1,0x48381a20815a492,0x14e624003883143,0x4ce14361800e88e,0x5c34d31432835ce,0x20d1822c214e28e,0x1c220218d2cb1cd,0x60f1cf525182602,0x18f28f1c251418f,0x4cf19e29e1de4d3,0x1566630b5141cf,0x29500b659315515,0x30b28a5cb24b315,0x7e70192495d5249,0x197df016256016]⟩,
  ⟨48,8,[ew171,ew414,ew172,ew173,ew174,ew175,ew176],lh 6 [579,49,20,68,10,715,32,18,16,7,716,717,13,23,11,718,14,15,3,340,12,17,46,2,41,516,719,51,43,25,22,36,537,518,519,520,539,543,527,523,52,19,358,145,376] [0x300365f1539df,0x13813013653003,0x41003003003043,0x2c6082283503013,0x3032830822c6506,0x40630c4061c63c3,0x2031461063c31c7,0x146208003103143,0x39c69c249406386,0x1904140624969c,0x5142a1082000828,0x2a15142e20822e2,0x1c742430c3e31c7,0x192083e330c424,0x104145208000104,0x6a638e425249019,0x55542538e6a6249,0x1541001082016,0x30c0011c1016096,0x13010291c7000,0x208000104001201,0x1441001101005,0x241016451016256,0x2d51d5282342001,0x2022c21c229534d,0x2922122d2104282,0x4512922522c2102,0x2d245229d25d2dd,0x1171576ea3cd10d,0x3d745714d6db3d7,0x6183cd44d68d60d,0x15e3ac15b618ad7,0x15b38e15e61e]⟩,
  ⟨48,8,[ew149,ew150,ew171,ew172,ew173,ew174,ew176],lh 6 [579,14,7,10,13,18,316,20,16,17,350,721,722,15,723,154,12,724,726,472,533,51,11,23,516,587,523,551,58,22,68,727,416,25,41,720,725,402,36,356,71,49,54,145] [0xc30180180080c3,0x89488c86c8018,0x2700870869a6a6,0x804801871c018,0x4143142492c8408,0x3941142c8248314,0x145055115055145,0x45d082055595394,0x28a05508245d59d,0x8db28a05b068003,0x6a9003183043043,0x3031c32cf249000,0x1432cf1c7303249,0x4f14504f10f383,0x8f06434d383104,0x6408244f34d44f,0x19e01e02a00a186,0x2ca40a00a04a01e,0x1ca3124123121c7,0x531453921122ca,0x593392152053113,0x45f59f45f082053,0x410020249053093,0x20420006246006,0x145006106019145,0x6346019104006,0x58601934d019599,0x3091042c75c7006,0x873071072c95d7,0x2e10a132134d2c7,0x897384082307347,0xac48a2397082457]⟩,
  ⟨48,8,[ew149,ew145,ew171,ew172,ew173,ew174,ew175,ew176],lh 6 [41,46,18,52,154,10,3,17,0,20,25,637,402,2,583,345,728,68,49,58,571,690,340,584,12,13,539,634,579,493,36,145,635,636,520,670,527,581,582,23,523,729,730,651,16,7,350,585,489] [0x69055d41575a41a,0xc32cb79b59e690,0x7c105b0c36c106b,0x1e11868471e0186,0x34d3820a234d807,0x2e3b1b10488208e,0x24208900017208,0x59654c3105965c0,0x7010500c354c310,0x2a524954105c0c3,0xa794a2a624998a,0x2c51681043979dc,0xb5c000a0514b104,0xd144104c0cc38e,0x50a291611301051,0x9465444a454614,0x14550208f64f3c2,0x3c83cb2ee3e33cb,0x1cf00030830c000,0x601487492618047,0xc20c3659482481,0x4d316f0cb0d2652,0x2014c04c31454df,0x269253213040041,0x2490821e91c7087,0x149184186145244,0x28028aa8a180189,0x34d104085086a86,0x34e342104345,0x10810b00038ec17,0x5c8204000]⟩,
  ⟨48,8,[ew149,ew153,ew171,ew172,ew173,ew174,ew176],lh 6 [584,731,10,46,18,128,154,725,20,23,52,49,732,733,14,25,734,16,350,12,13,8,51,71,726,472,523,533,17,294,527,551,402,680,36,3,2,0,642,727,542,7,735] [0x18601e01e011186,0x514918517d101e,0x2cb39129169a6a2,0x3912cb055295055,0x4db35b3cf3158d5,0x41b91b3153d535b,0x104396516396104,0x1e02601695641b,0x4920161d601e145,0x85f4921df1e7002,0xc21c72cb1c21c2,0x1e80c30422c2042,0x2023423c23064d3,0x4025023063cf342,0x2491c65061c6246,0x69a6a9046146402,0x2970572cb392292,0x3174d73922cb057,0x2173584d8358208,0x399249418518317,0x159418258399519,0x2016002002a019,0x4d330371c0191d9,0x434c334a71c04a,0x10404a514403103,0xa1ca04350338a,0x145003003043143,0x35c10430824804a,0x74834810831c249,0x30f74f34f145308,0x75d404144348148,0x475d409149009]⟩,
  ⟨48,8,[ew415,ew171,ew172,ew173,ew174,ew175,ew176],lh 6 [590,15,46,20,13,32,23,16,11,340,736,738,737,14,10,36,739,17,25,740,18,3,41,2,8,51,516,402,12,43,22,49,537,518,519,520,539,335,523,7,527,19,358,376] [0x6db01a3cf2a86db,0x1a09f0003cf01a,0xc332149200081f,0x3210c32e24922e2,0x186964104423186,0x4e61c7423104364,0x61834d1c794d618,0x1a22728a0674e6,0x80500020801a041,0xf00f00f08f005,0xc530971c005082,0x3090c32c571c2c5,0x105345505409109,0x4c5385409514345,0x60534938e349609,0x29d0410092094c5,0x44228904929d21d,0xb4510000c3002,0x1040025140020c3,0x2104029514000,0x1c700038e0021c2,0xa04100238e00d,0x208002041002208,0x2d1104303183000,0x1c72c3104311186,0x3151d52d538e311,0x413155952d1391,0x2d50553125922d2,0x1d735766a4061c6,0x4170574c6659417,0x597406046286596,0x29e22b4d9599297,0x2992084de59e]⟩,
  ⟨48,8,[ew171,ew172,ew173,ew174,ew175,ew416,ew176],lh 6 [595,340,741,36,2,22,46,14,49,743,578,17,3,742,13,0,11,23,20,744,58,32,18,52,12,523,402,543,516,25,518,519,520,539,376,7,527,74,16] [0x5c30832081d55d5,0x3416181d5208083,0x492243618243483,0x1d55954c1101341,0x34c15961d5115,0x11c1001141003,0x641003003003143,0x3643281901001,0x41a29a2a5001401,0x3462cb2816c129a,0x4862482cb088492,0x973974c6586086,0x14608638e1d7596,0x14154094094006,0x7141c81c8086086,0x887081d41d4094,0x2860864062886c8,0x352452088410286,0x38e34b45124b38e,0x24c24c34b145252,0x78b24b24b34c14c,0x34c78c24c7cc34b,0x41034c3cc24b7cb,0x24c40c35d3dd25d,0x1440041c44d1151,0x4ce80e0110114c4,0x84e4c48041c4844,0x2913cf4c44041ce,0x7052843c44d1411,0x2201b026085,0x3cf0050050053e2,0x193cf00000000a,0x28a3e3019023]⟩,
  ⟨48,8,[ew142,ew159,ew171,ew172,ew173,ew174,ew175,ew176],lh 6 [52,340,11,20,16,36,590,23,18,10,0,25,341,22,609,676,17,32,12,3,594,51,746,516,747,745,539,543,46,592,593,13,595,527,606,607,520,608,14,748,537,661,326,5,19,7,74,598,358] [0x6cf69a58fa99a68,0x416051590416cf,0x19470601c60514f,0xde4107830dd410,0x1041867c621f743,0x80924f104609260,0xa128a84208e28a,0x38ead7041382,0x196b170005c65c6,0x2e30c38cb2e20c3,0x2085071e420888b,0x98d3651049071d4,0xb5728a94d356104,0x5146151000396,0x14b141492466445,0x44150104b045492,0x2450470513d1447,0x14d14124904d045,0x2c158138208e3ae,0x48c01000049230b,0x186bc018050820c,0xc104309300100,0x18c302300180009,0x4082031c300200c,0x2431030c80d01c7,0x2930c90d31134c9,0x4c24cb28b2c2093,0x5541043d5c07107,0x821ca2880881d5,0x3420959d520a287,0x54208d9cd]⟩,
  ⟨48,8,[ew417,ew171,ew172,ew173,ew174,ew175,ew176],lh 6 [599,15,506,32,340,749,20,750,751,18,2,490,7,12,23,17,752,13,10,36,22,753,8,16,514,3,51,41,516,25,14,543,43,341,518,519,520,539,523,527,49,19,358,376] [0xc30004d301c0c3,0x1c08201c4d3167,0x1861e275d0007e8,0x1e21862233cf223,0x24962528a424249,0x56651442428a625,0x59661851461e596,0x1c30c145041566,0x8300030c01c041,0x13082013013003,0x3cf1c434d003603,0x1c43c420334d203,0x451a43249404444,0x543483404244783,0x596784492784584,0x1600411447c4543,0x3cf004044160160,0x23c200234d021,0x44200b249021361,0xb44b002242002,0x5d700b48b0025c2,0x504100248200b,0x30c00b04b00b30b,0x20d4511c6386000,0x5c62064461cd38e,0x1d95d92194921c6,0x411d9319206486,0x2190411dd31d21d,0x5ca78a6aa40e5ce,0x40a04a54e69a40a,0x6db40e04114e6ce,0x15416b55a6db14a,0x15a7da5546d4]⟩
]
def nodesBlock22 : Array Node := #[
  ⟨48,8,[ew171,ew172,ew173,ew174,ew175,ew418,ew176],lh 6 [604,340,46,36,23,754,17,58,14,755,756,10,584,154,3,41,2,20,757,11,7,15,32,13,49,18,52,523,146,402,516,25,27,551,518,519,520,539,527,514,16] [0x683143618216696,0x24171c216618143,0x451283703283443,0x216656481801241,0x2c3481659216816,0x12c1001841003,0x9810036c3003003,0x30030016c1301,0x4dd31d5143014c1,0x24218600151431d,0x442298186158451,0x15a5da482642142,0x21425d721a659,0x72071472c7002,0x7872022021422cb,0x1427822079c7147,0x555142502307547,0x251111147507302,0x5d72461042865d7,0x28e2cb246346291,0x8862862cb24e34e,0x24e88e28e8ce246,0x55524e50e2868c6,0x28e54e25f51f29f,0x2d001034d4842c4,0x48490400434d490,0x944490910210950,0x3043c4490550204,0x78d3103cf484544,0x3cf02102814d,0x4d300d3cf00d4cd,0x1b4d30003cf00c,0x30c4d301b3cf]⟩,
  ⟨48,8,[ew153,ew142,ew171,ew172,ew173,ew174,ew175,ew176],lh 6 [32,11,20,18,23,52,638,17,5,341,36,8,0,608,340,506,25,16,12,533,3,691,641,51,609,539,516,746,543,758,606,607,520,22,761,639,640,523,527,14,326,759,41,760,49,13,598,532,358,642] [0x65571c55ba19559,0x28a74821b28a655,0x68f3c6145748229,0x41e08218f3da145,0xc379041f0827d0,0x8041160c3584120,0xa9a04135885a5e1,0x88822b00034d,0x196b063cf888215,0xa41c79020a31c7,0x451186b461048c2,0x94b2cd45134b2e5,0x6630c98105830c,0x14a2862803c0601,0x28728e49202700a,0xe58e38738a492,0x3403830c0540003,0xb00e9ce38b380,0x8048218200040,0x1c71524891c701b,0x2462560c3252245,0x4492c91511461ae,0x491461452cb251,0x84085041246249,0x820c21c41070c7,0x4d350b5144ef08b,0x40c41004150c502,0x4cd5f01134d4054,0x30c0c10445d7593,0x5cd5c3303101104,0x34dc5830c]⟩,
  ⟨48,8,[ew171,ew419,ew172,ew173,ew174,ew175,ew176],lh 6 [762,58,20,2,766,7,46,36,763,764,11,3,49,18,282,8,765,23,17,516,5,14,15,533,41,767,16,51,551,12,25,22,13,71,518,519,520,539,334,10,543,527,32,523,358,492,376] [0x4171c72a0074c7,0x7047007307000,0x8721475d00030c,0x21408224775d247,0x80e54e34d414814,0x10e10e41435454e,0x3e11047211043cf,0x64e14e54728700e,0x4154714564e28a,0x1304101330c000,0x822222cb00030c,0x2220822632cb263,0xc39a534d4240c3,0x12b12742434d565,0x69a0130130136a7,0x66914556828a000,0x4929a814566928a,0xc49200c2cb006,0xc30063460062c6,0x60c6001341001,0x6810013c1006686,0x15810063cf001,0x141006596006146,0x2520d2202442001,0x3c22420c2212451,0x20b3cf24b5cb202,0x5962021422425d7,0x24258221e15e25e,0x5c31036ec4115d7,0x4031431116db403,0x618411145651611,0x11f2ae11b618b43,0x11b28a11f61f]⟩,
  ⟨48,8,[ew420,ew171,ew172,ew173,ew174,ew175,ew176],lh 6 [768,52,18,10,769,20,17,16,36,770,771,2,11,41,7,490,282,772,23,22,12,5,3,14,15,516,773,51,537,13,341,25,49,523,518,519,520,539,334,543,527,32,552,358,145] [0x6071c729019208,0x19041019020000,0x186262145000121,0x2621862a31452a3,0x2cb5e50824642cb,0xc34640829a5,0x4d30190c30194d3,0x6a834d9a730c121,0x415e734d6a830c,0x8041008008000,0x18625551400072a,0x255195288514288,0x7505d0082455755,0x100d04550955d0,0x1c71040c31041c7,0x6903905c8308110,0x1865c838e69030c,0x118100151401e,0x74100f08201e51e,0xf74f001082001,0x1cf00f0cf0011c1,0x16010010c300f,0x38100f61800f38f,0x286082245485001,0x1c5285085246492,0x2561d62960c3245,0x6182563962850c5,0x29661625f39f29f,0x1cb10b6eb4521c7,0x44b38b1126db44b,0x34d45238e692352,0x11330311b34db0b,0x11b30c113353]⟩,
  ⟨48,8,[ew150,ew145,ew171,ew172,ew173,ew174,ew175,ew176],lh 6 [32,5,490,58,41,25,20,13,634,22,2,36,615,16,18,51,0,17,3,31,12,340,533,637,616,774,617,516,775,341,539,492,145,49,635,636,520,527,776,613,614,523,777,778,493,651,670,8,23,7,356,532,358,489] [0x799618719b19618,0x7cb2ed000799,0x2178480e180b2ee,0x1a31458c61a2145,0x28a3071e428a886,0x208bc83cf9071cc,0x4e51049534da104,0x2cb98105c2cb693,0x6c20880c398105c,0x16718620209b0c3,0x1c79c5168186a05,0x5c926934d31ac1b,0xc5b4d3a4925734d,0x8204804008230c,0x500150101f001,0x11c1045140514,0x5c004e3801c000e,0x9015815549240,0x101401044055415,0x4430d451d451544,0xc70c238e754743,0x9734d087083383,0x4020c40c8232088,0x1aa183403084082,0x1861c646a4511d1,0x59648d4925b318d,0x144145ac5484486,0x28a3f4396592ad2,0x10428c28e3cf296,0x25024f10430cd5a,0x3d0409109]⟩,
  ⟨48,8,[ew171,ew172,ew421,ew173,ew174,ew175,ew176],lh 6 [779,52,20,18,784,49,780,781,7,46,13,15,5,12,782,17,16,23,282,783,58,3,516,126,47,514,533,51,2,41,543,10,14,8,523,551,25,22,74,518,519,520,539,11,36,19,527,532,358,376] [0x4100c14c000041,0xc58c00014500c,0x8218c34c79e7ac,0x18c0821d73571d7,0x292b520c3397297,0x4d27d23970c3812,0x8528187d8818861,0x182261047a64d2,0x1104208118118,0x5005005585001,0x850093cf001581,0x90890053cf005,0xc100128a0090c9,0x1401009289001,0x7c10144140147df,0x92090142d4001,0x34d0142140092cb,0x1e834d1e83cf1a7,0xc33a928a1a73cf,0x3a90c366a28a66a,0x6636634104e2662,0x160164e2410663,0x2eb12e12b0002cb,0x1cd0c3182442016,0x4021c20c218d451,0x1954151d56af182,0x2cb1952151c269a,0x1d52d51a42241e4,0x69c81c6f039169a,0x39c21c4d16db39c,0x75d391208111751,0x1251314db75d11c,0x11b79b4e5765]⟩,
  ⟨48,8,[ew422,ew171,ew172,ew173,ew174,ew175,ew176],lh 6 [785,49,11,20,341,18,2,14,786,787,41,790,52,788,23,12,25,789,22,126,47,3,51,5,10,282,16,533,516,15,17,8,13,537,518,519,520,539,523,7,36,527,532,358] [0x30c86186801c5d7,0x1c30c01c041000,0x4102223cf000041,0x2224102633cf263,0x1861e5145364186,0x4666183641451e5,0x4921c76181c7492,0x2e92a701c0a7466,0x30c01c28a000082,0x1730c017041000,0xc32173cf000041,0x2170c32533d3253,0x8191d9145353813,0x4596193531531d9,0x69a1d46141d469a,0x2d47542cb082459,0x79e2cb75d014094,0x17810010c3004,0x8040011410040c4,0x1801004145004,0x6840047c4001681,0x17410017df004,0x82004744004084,0x25e145203383001,0x7c324314321e38e,0x2157d52556ea203,0x822152952436db,0x255095210290250,0x6c61c65ab34e6db,0x34608644e596346,0x28634e08e2ce28a,0x2d20824562962c6,0x2d6096452292]⟩,
  ⟨48,8,[ew171,ew172,ew173,ew174,ew175,ew423,ew176],lh 6 [791,49,341,20,32,340,624,23,41,36,11,15,154,3,2,792,793,10,18,794,14,796,146,17,516,27,795,5,25,52,551,518,519,520,539,16,616,523] [0x749009041005745,0x3c5596005045009,0xc34095894090c9,0x5044924c96493c5,0x4444c9489504644,0x185445185505184,0x785684504184184,0x684784505505505,0x29b55b2cb544284,0x25d75442c455b,0x5820015c1001596,0x2642001481002,0x1001641002492,0x2002002442001,0x602001001001451,0x1601002002002,0x2cb0022820012c1,0x3c31c3001281002,0x4833d71c7417492,0x40d4513c3303403,0x7c34034433cd30d,0x3cd7cd40d80d3c3,0x2cb3cd20d403803,0x40d2cd3dc21c41c,0x44e18e30c4c7447,0x4c784718730c4ce,0x8874ce84e50e88e,0x5472084ce2ce687,0x60c54e20e4c72c7,0x1862081a41a300c,0x28a18c20800c28c,0x28a018208195,0x1828a1a5208]⟩,
  ⟨48,8,[ew171,ew131,ew172,ew173,ew174,ew175,ew405,ew176],lh 6 [5,51,20,2,15,60,32,49,154,627,58,340,3,41,623,146,17,52,624,799,632,36,14,516,798,12,25,628,629,520,523,543,539,7,804,621,622,527,797,800,46,616,801,802,145,803,39,337,358,18,16] [0x540580016015995,0x28000700628a558,0x182180640187180,0x1800c0002086659,0x20600e0060c3193,0x18118b20b2c1046,0xb4cb2e72c0580,0x50000400b60b016,0x254a091c72c42c0,0x3dc08270f3db082,0xc338515d0c36cf,0x48821e04174514e,0x8137df788212041,0x1214d8b2baa9813,0x1cf3ed410249849,0x14724724f3c7410,0x511c5151251445,0x44844a04a288211,0x1ca24a297287247,0x24a50410926e1d7,0x4054100d008514a,0x30c8af0810820c3,0x90c0a3082882301,0x30d30290232330c,0xc0c10c68d69a104,0x5c348104338338e,0x14d34310348ec43,0xc815c10cd345105,0x10821220110438e,0x94d354104052048,0x50d365104]⟩,
  ⟨48,8,[ew424,ew171,ew172,ew173,ew174,ew175,ew176],lh 6 [808,17,5,805,52,809,41,13,14,806,807,51,10,36,7,46,11,60,25,2,154,12,28,58,3,49,15,539,810,43,516,520,20,537,340,518,519,523,543,527,18,140,445,337] [0x1046db6e20de362,0xde1040de21e221,0x41263492221221,0x2630412a44922a4,0x4d300016501f4d3,0x51401f028000,0x2cb01f51401f2cb,0x72718622638e165,0x10422618672738e,0xcd10d0cd64d21d,0x5d24255521d659,0x24204229d55529d,0x4d30006e90024c2,0x2502002002000,0x2c21455141452cb,0x70218220d40d142,0x4120d18d702410,0x2990590d955524f,0x1c700f00f0cf54f,0xcf1c70046c40c4,0x2d70d75aa1442c4,0x2176970c4596157,0x41770f69a0cf40f,0x2811c72604600d7,0x5812a01e0241441,0x25859829832b241,0x69a25839828130c,0x298698252392292,0x30c01159100730c,0x7387007587011,0x18601138e011191,0x14c40c14b186007,0x14b41014c186]⟩,
  ⟨48,8,[ew425,ew171,ew172,ew173,ew174,ew175,ew176],lh 6 [814,2,52,811,49,815,5,14,812,3,813,41,11,20,7,18,51,17,16,25,154,58,23,36,43,46,15,533,816,520,12,516,551,8,22,32,518,519,543,527,523,354,532,358,376] [0x1048208230df5e3,0xdf1040df0821c7,0x2492244d31c7082,0x2242492a54d32a5,0x3cf00004101d3cf,0x41001d041000,0x51401d41001d514,0x72730c1e62cb168,0x821e630c7272cb,0xd70820d71041d8,0x35820679e1d8118,0x20634d29879e298,0x410003cf006046,0x1465060063c6000,0x492145514145492,0x7063861d7317006,0x4511d738e70630c,0x2844440c434d219,0x420043c40d9359,0xc40410023c20c2,0x4950d5869142482,0x1d56950c2861155,0x39571969a0d9399,0x29104120d58d0d5,0x49128d04d211591,0x2094892896ea211,0x69a2093892916db,0x289689213393293,0x6c100142b0166db,0x1381016410001,0x2cb01638e0162d6,0x16232c1502cb001,0x15030c1622e2]⟩,
  ⟨48,8,[ew171,ew426,ew172,ew173,ew174,ew175,ew176],lh 6 [627,68,32,2,819,7,46,17,18,14,20,817,818,154,49,820,11,16,23,5,12,3,15,533,41,516,51,821,25,22,537,28,58,518,519,543,527,616,520,532,358,376] [0x781241241253793,0x2242253253241,0x382001001001381,0x3021c22c1501002,0xc12c11c1302514,0x1020c3102202101,0x7c13c2342101208,0x3c27c23c134d3c1,0x4136d3145242402,0x193a02421456d3,0x5142e128a000960,0x2e151432228a322,0x2080000c3019208,0x194510190c3104,0x34d12645100034d,0x6e4410263145019,0x1c72634106e4145,0xe1c700e28a006,0xc3006206006286,0x60c6004208000,0x45100034d006446,0xe58e00634600f,0x14e006596006146,0x3072072ca48a00e,0x44730a20a2c7492,0x2d54553155e72c7,0x5962d51553075d7,0x3155952dc15c31c,0x5c30036a81125d7,0x10314311269a103,0x618112145112612,0x3dd4293da618103,0x3da4103dd61d]⟩,
  ⟨48,7,[ew145,ew171,ew172,ew173,ew174,ew175,ew407,ew176],lh 5 [43,490,52,3,17,41,20,340,32,25,2,18,0,28,822,539,493,12,8,23,7,54,242,489,16] [0x48d230882202008,0xa160f83dcd7366a,0x210034411006a1,0x3800701ce001da0,0x1042208841310c4,0x310861042210422,0x1a52320c6420c64,0x95caa5a94b5cacb,0xc2b0ac2b0b8]⟩,
  ⟨48,7,[ew145,ew171,ew412,ew172,ew173,ew174,ew175,ew176],lh 5 [68,43,22,8,41,18,17,52,25,20,32,31,2,539,493,3,51,569,823,23,7,49,598,532,358,489] [0x91e27735cd0a82a,0xa10501426c43d0f,0x4200800708001,0x4201000102940,0x18985615264a2a7,0x395264996459062,0x2a5645906218ac5,0xc0cc8410c3b8ca6,0x310899214a3]⟩
]
def nodesGet (i : Nat) : Option Node :=
  if i < 176 then
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
      if i < 128 then
        if i < 96 then
          nodesBlock5[(i-80)]?
        else
          if i < 112 then
            nodesBlock6[(i-96)]?
          else
            nodesBlock7[(i-112)]?
      else
        if i < 144 then
          nodesBlock8[(i-128)]?
        else
          if i < 160 then
            nodesBlock9[(i-144)]?
          else
            nodesBlock10[(i-160)]?
  else
    if i < 272 then
      if i < 224 then
        if i < 192 then
          nodesBlock11[(i-176)]?
        else
          if i < 208 then
            nodesBlock12[(i-192)]?
          else
            nodesBlock13[(i-208)]?
      else
        if i < 240 then
          nodesBlock14[(i-224)]?
        else
          if i < 256 then
            nodesBlock15[(i-240)]?
          else
            nodesBlock16[(i-256)]?
    else
      if i < 320 then
        if i < 288 then
          nodesBlock17[(i-272)]?
        else
          if i < 304 then
            nodesBlock18[(i-288)]?
          else
            nodesBlock19[(i-304)]?
      else
        if i < 336 then
          nodesBlock20[(i-320)]?
        else
          if i < 352 then
            nodesBlock21[(i-336)]?
          else
            nodesBlock22[(i-352)]?
def fastViews : QFast.Table View := ⟨49,viewsGet⟩
def fastNodes : QFast.Table Node := ⟨366,nodesGet⟩
end SignedProjection

namespace SignedProjection
end SignedProjection

namespace SignedProjection
def aliasMap0 : Array Nat := #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,34,0,0,0,38,0,0,0,42,0,0,0,46,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,50,0,0,0,54,0,0,0,58,0,0,0,62,0]
def aliasMap1 : Array Nat := #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,5,0,0,0,9,0,0,0,13,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,33,0,0,0,37,0,0,0,41,0,0,0,45,0]
def aliasMap2 : Array Nat := #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,3,0,0,0,5,0,0,0,7,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,33,0,0,0,35,0,0,0,37,0,0,0,39,0]
def aliasMap3 : Array Nat := #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,10,0,0,0,11,0,0,0,26,0,0,0,27,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,42,0,0,0,43,0,0,0,58,0,0,0,59,0]
def aliasMap4 : Array Nat := #[0,0,2,11,0,0,6,15,0,0,0,0,0,0,0,0,0,0,18,27,0,0,22,31,0,0,0,0,0,0,0,0,0,0,34,43,0,0,38,47,0,0,0,0,0,0,0,0,0,0,50,59,0,0,54,63,0,0,0,0,0,0,0,0]
def aliasMap5 : Array Nat := #[0,0,0,0,0,0,1,0,0,0,18,0,0,0,19,0,0,0,8,0,0,0,9,0,0,0,26,0,0,0,27,0,0,0,32,0,0,0,33,0,0,0,50,0,0,0,51,0,0,0,40,0,0,0,41,0,0,0,58,0,0,0,59,0]
def aliasMap6 : Array Nat := #[0,0,63,0,0,0,62,0,0,0,45,0,0,0,44,0,0,0,55,0,0,0,54,0,0,0,37,0,0,0,36,0,0,0,31,0,0,0,30,0,0,0,13,0,0,0,12,0,0,0,23,0,0,0,22,0,0,0,5,0,0,0,4,0]
def aliasMap7 : Array Nat := #[0,0,0,0,0,0,1,0,0,0,18,0,0,0,19,0,0,0,4,0,0,0,5,0,0,0,22,0,0,0,23,0,0,0,32,0,0,0,33,0,0,0,50,0,0,0,51,0,0,0,36,0,0,0,37,0,0,0,54,0,0,0,55,0]
def aliasMap8 : Array Nat := #[0,0,63,0,0,0,62,0,0,0,45,0,0,0,44,0,0,0,59,0,0,0,58,0,0,0,41,0,0,0,40,0,0,0,31,0,0,0,30,0,0,0,13,0,0,0,12,0,0,0,27,0,0,0,26,0,0,0,9,0,0,0,8,0]
def aliasMap9 : Array Nat := #[0,0,0,0,0,0,1,0,0,0,24,0,0,0,25,0,0,0,2,0,0,0,3,0,0,0,26,0,0,0,27,0,0,0,32,0,0,0,33,0,0,0,56,0,0,0,57,0,0,0,34,0,0,0,35,0,0,0,58,0,0,0,59,0]
def aliasMap10 : Array Nat := #[0,0,2,3,0,0,6,7,0,0,10,11,0,0,14,15,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,18,19,0,0,22,23,0,0,26,27,0,0,30,31,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
def aliasMap11 : Array Nat := #[0,0,32,33,0,0,34,35,0,0,0,0,0,0,0,0,0,0,40,41,0,0,42,43,0,0,0,0,0,0,0,0,0,0,48,49,0,0,50,51,0,0,0,0,0,0,0,0,0,0,56,57,0,0,58,59,0,0,0,0,0,0,0,0]
def aliasMap12 : Array Nat := #[0,0,4,5,0,0,6,7,0,0,0,0,0,0,0,0,0,0,20,21,0,0,22,23,0,0,0,0,0,0,0,0,0,0,36,37,0,0,38,39,0,0,0,0,0,0,0,0,0,0,52,53,0,0,54,55,0,0,0,0,0,0,0,0]
def aliasMap13 : Array Nat := #[0,0,32,33,0,0,34,35,0,0,0,0,0,0,0,0,0,0,36,37,0,0,38,39,0,0,0,0,0,0,0,0,0,0,48,49,0,0,50,51,0,0,0,0,0,0,0,0,0,0,52,53,0,0,54,55,0,0,0,0,0,0,0,0]
def aliasMap14 : Array Nat := #[0,0,8,9,0,0,12,13,0,0,10,11,0,0,14,15,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,40,41,0,0,44,45,0,0,42,43,0,0,46,47,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
def aliasMap15 : Array Nat := #[0,0,8,9,0,0,12,13,0,0,10,11,0,0,14,15,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,24,25,0,0,28,29,0,0,26,27,0,0,30,31,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
def aliasMap16 : Array Nat := #[0,0,32,33,0,0,34,35,0,0,0,0,0,0,0,0,0,0,36,37,0,0,38,39,0,0,0,0,0,0,0,0,0,0,40,41,0,0,42,43,0,0,0,0,0,0,0,0,0,0,44,45,0,0,46,47,0,0,0,0,0,0,0,0]
def aliasMap17 : Array Nat := #[0,0,0,5,0,0,18,23,0,0,0,0,0,0,0,0,0,0,8,13,0,0,26,31,0,0,0,0,0,0,0,0,0,0,32,37,0,0,50,55,0,0,0,0,0,0,0,0,0,0,40,45,0,0,58,63,0,0,0,0,0,0,0,0]
def aliasMap18 : Array Nat := #[0,0,4,22,0,0,1,19,0,0,0,0,0,0,0,0,0,0,12,30,0,0,9,27,0,0,0,0,0,0,0,0,0,0,36,54,0,0,33,51,0,0,0,0,0,0,0,0,0,0,44,62,0,0,41,59,0,0,0,0,0,0,0,0]
def aliasMap19 : Array Nat := #[0,0,0,9,0,0,18,27,0,0,0,0,0,0,0,0,0,0,4,13,0,0,22,31,0,0,0,0,0,0,0,0,0,0,32,41,0,0,50,59,0,0,0,0,0,0,0,0,0,0,36,45,0,0,54,63,0,0,0,0,0,0,0,0]
def aliasMap20 : Array Nat := #[0,0,8,26,0,0,1,19,0,0,0,0,0,0,0,0,0,0,12,30,0,0,5,23,0,0,0,0,0,0,0,0,0,0,40,58,0,0,33,51,0,0,0,0,0,0,0,0,0,0,44,62,0,0,37,55,0,0,0,0,0,0,0,0]
def aliasMap21 : Array Nat := #[0,0,2,0,0,0,1,0,0,0,18,0,0,0,17,0,0,0,10,0,0,0,9,0,0,0,26,0,0,0,25,0,0,0,34,0,0,0,33,0,0,0,50,0,0,0,49,0,0,0,42,0,0,0,41,0,0,0,58,0,0,0,57,0]
def aliasMap22 : Array Nat := #[0,0,2,0,0,0,1,0,0,0,18,0,0,0,17,0,0,0,6,0,0,0,5,0,0,0,22,0,0,0,21,0,0,0,34,0,0,0,33,0,0,0,50,0,0,0,49,0,0,0,38,0,0,0,37,0,0,0,54,0,0,0,53,0]
def aliasMap23 : Array Nat := #[0,10,0,0,0,9,0,0,0,26,0,0,0,25,0,0,0,14,0,0,0,13,0,0,0,30,0,0,0,29,0,0,0,42,0,0,0,41,0,0,0,58,0,0,0,57,0,0,0,46,0,0,0,45,0,0,0,62,0,0,0,61,0,0]
def aliasMap24 : Array Nat := #[0,0,0,46,0,0,43,0,0,0,0,14,0,0,11,0,0,0,0,44,0,0,41,0,0,0,0,12,0,0,9,0,0,0,0,38,0,0,35,0,0,0,0,6,0,0,3,0,0,0,0,36,0,0,33,0,0,0,0,4,0,0,1,0]
def aliasMap25 : Array Nat := #[0,10,0,0,0,3,0,0,0,26,0,0,0,19,0,0,0,14,0,0,0,7,0,0,0,30,0,0,0,23,0,0,0,42,0,0,0,35,0,0,0,58,0,0,0,51,0,0,0,46,0,0,0,39,0,0,0,62,0,0,0,55,0,0]
def aliasMap26 : Array Nat := #[0,0,8,0,0,0,1,0,0,0,24,0,0,0,17,0,0,0,10,0,0,0,3,0,0,0,26,0,0,0,19,0,0,0,40,0,0,0,33,0,0,0,56,0,0,0,49,0,0,0,42,0,0,0,35,0,0,0,58,0,0,0,51,0]
def aliasMap27 : Array Nat := #[0,43,0,0,0,58,0,0,0,41,0,0,0,56,0,0,0,11,0,0,0,26,0,0,0,9,0,0,0,24,0,0,0,35,0,0,0,50,0,0,0,33,0,0,0,48,0,0,0,3,0,0,0,18,0,0,0,1,0,0,0,16,0,0]
def aliasMap28 : Array Nat := #[63,62,47,46,0,0,0,0,31,30,15,14,0,0,0,0,61,60,45,44,0,0,0,0,29,28,13,12,0,0,0,0,55,54,39,38,0,0,0,0,23,22,7,6,0,0,0,0,53,52,37,36,0,0,0,0,21,20,5,4,0,0,0,0]
def aliasMap29 : Array Nat := #[0,0,47,46,0,0,43,42,0,0,15,14,0,0,11,10,0,0,45,44,0,0,41,40,0,0,13,12,0,0,9,8,0,0,39,38,0,0,35,34,0,0,7,6,0,0,3,2,0,0,37,36,0,0,33,32,0,0,5,4,0,0,1,0]
def aliasMap30 : Array Nat := #[0,0,0,0,0,0,0,0,31,30,15,14,27,26,11,10,0,0,0,0,0,0,0,0,29,28,13,12,25,24,9,8,0,0,0,0,0,0,0,0,23,22,7,6,19,18,3,2,0,0,0,0,0,0,0,0,21,20,5,4,17,16,1,0]
def aliasMap31 : Array Nat := #[63,62,59,58,55,54,51,50,0,0,0,0,0,0,0,0,61,60,57,56,53,52,49,48,0,0,0,0,0,0,0,0,47,46,43,42,39,38,35,34,0,0,0,0,0,0,0,0,45,44,41,40,37,36,33,32,0,0,0,0,0,0,0,0]
def aliasMap32 : Array Nat := #[0,62,47,0,0,58,43,0,0,30,15,0,0,26,11,0,0,60,45,0,0,56,41,0,0,28,13,0,0,24,9,0,0,54,39,0,0,50,35,0,0,22,7,0,0,18,3,0,0,52,37,0,0,48,33,0,0,20,5,0,0,16,1,0]
def rootAliases : QFast.AliasTable
  | 1 => some (0, aliasMap0)
  | 2 => some (0, aliasMap1)
  | 3 => some (0, aliasMap2)
  | 4 => some (0, aliasMap3)
  | 6 => some (5, aliasMap4)
  | 8 => some (7, aliasMap5)
  | 9 => some (7, aliasMap6)
  | 10 => some (7, aliasMap7)
  | 11 => some (7, aliasMap8)
  | 12 => some (7, aliasMap9)
  | 15 => some (14, aliasMap10)
  | 16 => some (5, aliasMap11)
  | 17 => some (5, aliasMap12)
  | 18 => some (5, aliasMap13)
  | 19 => some (14, aliasMap14)
  | 20 => some (14, aliasMap15)
  | 21 => some (5, aliasMap16)
  | 22 => some (5, aliasMap17)
  | 23 => some (5, aliasMap18)
  | 24 => some (5, aliasMap19)
  | 25 => some (5, aliasMap20)
  | 26 => some (7, aliasMap21)
  | 27 => some (7, aliasMap22)
  | 28 => some (13, aliasMap23)
  | 31 => some (30, aliasMap24)
  | 32 => some (13, aliasMap25)
  | 33 => some (7, aliasMap26)
  | 34 => some (13, aliasMap27)
  | 40 => some (39, aliasMap28)
  | 43 => some (38, aliasMap29)
  | 44 => some (42, aliasMap30)
  | 45 => some (41, aliasMap31)
  | 47 => some (46, aliasMap32)
  | _ => none
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockRoots_0 : QFast.passBlock (QFast.symCheckRoot rootAliases fastViews fastNodes) 0 28 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockRoots_28 : QFast.passBlock (QFast.symCheckRoot rootAliases fastViews fastNodes) 28 14 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockRoots_42 : QFast.passBlock (QFast.symCheckRoot rootAliases fastViews fastNodes) 42 7 = true := by decide +kernel
theorem joinRoots_0_0 : QFast.passBlock (QFast.symCheckRoot rootAliases fastViews fastNodes) 0 42 = true :=
  @QFast.merge_blocks (QFast.symCheckRoot rootAliases fastViews fastNodes) 0 28 14 blockRoots_0 blockRoots_28
theorem joinRoots_1_0 : QFast.passBlock (QFast.symCheckRoot rootAliases fastViews fastNodes) 0 49 = true :=
  @QFast.merge_blocks (QFast.symCheckRoot rootAliases fastViews fastNodes) 0 42 7 joinRoots_0_0 blockRoots_42
theorem certifiedRoots : QFast.passBlock (QFast.symCheckRoot rootAliases fastViews fastNodes) 0 49 = true := joinRoots_1_0
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockNodes_0 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 0 64 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockNodes_64 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 64 64 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockNodes_128 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 128 64 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockNodes_192 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 192 27 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockNodes_219 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 219 25 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockNodes_244 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 244 34 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockNodes_278 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 278 36 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockNodes_314 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 314 7 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockNodes_321 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 321 7 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockNodes_328 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 328 7 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockNodes_335 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 335 7 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockNodes_342 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 342 7 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockNodes_349 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 349 7 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockNodes_356 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 356 7 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockNodes_363 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 363 3 = true := by decide +kernel
theorem joinNodes_0_0 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 0 128 = true :=
  @QFast.merge_blocks (QFast.checkNodeAt fastViews fastNodes) 0 64 64 blockNodes_0 blockNodes_64
theorem joinNodes_0_128 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 128 91 = true :=
  @QFast.merge_blocks (QFast.checkNodeAt fastViews fastNodes) 128 64 27 blockNodes_128 blockNodes_192
theorem joinNodes_0_219 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 219 59 = true :=
  @QFast.merge_blocks (QFast.checkNodeAt fastViews fastNodes) 219 25 34 blockNodes_219 blockNodes_244
theorem joinNodes_0_278 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 278 43 = true :=
  @QFast.merge_blocks (QFast.checkNodeAt fastViews fastNodes) 278 36 7 blockNodes_278 blockNodes_314
theorem joinNodes_0_321 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 321 14 = true :=
  @QFast.merge_blocks (QFast.checkNodeAt fastViews fastNodes) 321 7 7 blockNodes_321 blockNodes_328
theorem joinNodes_0_335 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 335 14 = true :=
  @QFast.merge_blocks (QFast.checkNodeAt fastViews fastNodes) 335 7 7 blockNodes_335 blockNodes_342
theorem joinNodes_0_349 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 349 14 = true :=
  @QFast.merge_blocks (QFast.checkNodeAt fastViews fastNodes) 349 7 7 blockNodes_349 blockNodes_356
theorem joinNodes_1_0 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 0 219 = true :=
  @QFast.merge_blocks (QFast.checkNodeAt fastViews fastNodes) 0 128 91 joinNodes_0_0 joinNodes_0_128
theorem joinNodes_1_219 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 219 102 = true :=
  @QFast.merge_blocks (QFast.checkNodeAt fastViews fastNodes) 219 59 43 joinNodes_0_219 joinNodes_0_278
theorem joinNodes_1_321 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 321 28 = true :=
  @QFast.merge_blocks (QFast.checkNodeAt fastViews fastNodes) 321 14 14 joinNodes_0_321 joinNodes_0_335
theorem joinNodes_1_349 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 349 17 = true :=
  @QFast.merge_blocks (QFast.checkNodeAt fastViews fastNodes) 349 14 3 joinNodes_0_349 blockNodes_363
theorem joinNodes_2_0 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 0 321 = true :=
  @QFast.merge_blocks (QFast.checkNodeAt fastViews fastNodes) 0 219 102 joinNodes_1_0 joinNodes_1_219
theorem joinNodes_2_321 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 321 45 = true :=
  @QFast.merge_blocks (QFast.checkNodeAt fastViews fastNodes) 321 28 17 joinNodes_1_321 joinNodes_1_349
theorem joinNodes_3_0 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 0 366 = true :=
  @QFast.merge_blocks (QFast.checkNodeAt fastViews fastNodes) 0 321 45 joinNodes_2_0 joinNodes_2_321
theorem certifiedNodes : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 0 366 = true := joinNodes_3_0
end SignedProjection

namespace SignedProjection
def bMatches (z : Option View) : Bool :=
  match z with
  | none => false
  | some v => vg v == (0xeeeaeaa8eaaae080 : Word) && vk v == 10 && (vs v).toFinset == Direct64.cols.toFinset

theorem rootNegative : ¬ CoreSigned.build signedOps (0xeeeaeaa8eaaae080 : BitVec 64) 10 Direct64.cols.toFinset := by
  have shape : bMatches (QFast.get fastViews 48) = true := by decide +kernel
  cases ev : QFast.get fastViews 48 with
  | none => simp [ev, bMatches] at shape
  | some v =>
    have valid := QFast.symCertified rootAliases fastViews fastNodes certifiedRoots certifiedNodes ev
    simp only [ev,bMatches,Bool.and_eq_true,beq_iff_eq] at shape
    change ¬ CoreSigned.build signedOps (vg v) (vk v) (vs v).toFinset at valid
    rwa [shape.1.1,shape.1.2,shape.2] at valid
end SignedProjection

end PEqualNP.Outside.L_meta_47118_aux

open PEqualNP.Outside.L_meta_47118_aux in
theorem PEqualNP.Outside.L_meta_47118 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4008372904 * 2 ^ 32 + 3937067136) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4008372904 * 2 ^ 32 + 3937067136) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  LowerSymSix.finish SignedProjection.rootNegative
