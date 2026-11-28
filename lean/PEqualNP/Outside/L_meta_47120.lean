import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_47120_aux
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
  ⟨[⟨.and,[4,5]⟩, ⟨.or,[3,6]⟩, ⟨.and,[2,7]⟩, ⟨.or,[4,5]⟩, ⟨.and,[1,8]⟩,
    ⟨.or,[2,7]⟩, ⟨.and,[9,11]⟩, ⟨.or,[1,8]⟩, ⟨.and,[0,13]⟩, ⟨.or,[12,14]⟩,
    ⟨.or,[0,10]⟩, ⟨.and,[15,16]⟩],17⟩

theorem size : witness.size = 12 := rfl

theorem monotone : Monotone2 witness := by
  simp [Monotone2,witness]

set_option maxRecDepth 16000 in
theorem correct : ∀ x : Fin 6 → Bool, witness.eval (List.ofFn x) =
    Nat.testBit (3941264040 * 2 ^ 32 + 3936921736) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  decide +kernel

end LowerSymSix

namespace Direct64
open PEqualNP.CircuitLowerBounds SignedProjection
abbrev W := BitVec 64
abbrev basicOps (a b : W) := signedOps a b
abbrev goal : W := ~~~0xeaeaeaa8eaa8a888
open CoreSigned (build)
def tableB (x : Fin 6 → Bool) :=
  Nat.testBit (3941264040 * 2 ^ 32 + 3936921736) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
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

theorem low (reject : ¬ build basicOps (0xeaeaeaa8eaa8a888 : W) 10 cols.toFinset)
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
    (reject : ¬ CoreSigned.build SignedProjection.signedOps (0xeaeaeaa8eaa8a888 : BitVec 64) 10 Direct64.cols.toFinset) :
∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (3941264040 * 2 ^ 32 + 3936921736) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (3941264040 * 2 ^ 32 + 3936921736) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
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
def ew3 : Word := 0x200020002000200
def ew4 : Word := 0x202000002020000
def ew5 : Word := 0x202020200000000
def ew6 : Word := 0x20002000200020
def ew7 : Word := 0x22000000220000
def ew8 : Word := 0x22002200000000
def ew9 : Word := 0x202000002020
def ew10 : Word := 0x220000002200
def ew11 : Word := 0x222200000000
def ew12 : Word := 0x20202020
def ew13 : Word := 0x22002200
def ew14 : Word := 0x22220000
def ew15 : Word := 0x2020202020202020
def ew16 : Word := 0x2200220022002200
def ew17 : Word := 0x2222000022220000
def ew18 : Word := 0x2222222200000000
def ew19 : Word := 0xa000a000a000a0
def ew20 : Word := 0xc000c000c000c0
def ew21 : Word := 0xf0000000f00000
def ew22 : Word := 0xf000f000000000
def ew23 : Word := 0xa0a00000a0a0
def ew24 : Word := 0xc0c00000c0c0
def ew25 : Word := 0xf0000000f000
def ew26 : Word := 0xf0f000000000
def ew27 : Word := 0xa0a0a0a0
def ew28 : Word := 0xc0c0c0c0
def ew29 : Word := 0xf000f000
def ew30 : Word := 0xf0f00000
def ew31 : Word := 0xaa000000aa0000
def ew32 : Word := 0xcc000000cc0000
def ew33 : Word := 0xff000000000000
def ew34 : Word := 0xaa00aa00000000
def ew35 : Word := 0xcc00cc00000000
def ew36 : Word := 0xaa000000aa00
def ew37 : Word := 0xcc000000cc00
def ew38 : Word := 0xff0000000000
def ew39 : Word := 0xaa00aa00
def ew40 : Word := 0xcc00cc00
def ew41 : Word := 0xff000000
def ew42 : Word := 0xaaaa0000
def ew43 : Word := 0xcccc0000
def ew44 : Word := 0x4040404040404040
def ew45 : Word := 0x6000600060006000
def ew46 : Word := 0x6060000060600000
def ew47 : Word := 0x6060606000000000
def ew48 : Word := 0x44004400440044
def ew49 : Word := 0x60006000600060
def ew50 : Word := 0x66000000660000
def ew51 : Word := 0x66006600000000
def ew52 : Word := 0x4400440044004400
def ew53 : Word := 0x6600000066000000
def ew54 : Word := 0x6600660000000000
def ew55 : Word := 0x444400004444
def ew56 : Word := 0x606000006060
def ew57 : Word := 0x660000006600
def ew58 : Word := 0x666600000000
def ew59 : Word := 0x44444444
def ew60 : Word := 0x60606060
def ew61 : Word := 0x66006600
def ew62 : Word := 0x66660000
def ew63 : Word := 0x50005000500050
def ew64 : Word := 0x48004800480048
def ew65 : Word := 0x5a0000005a0000
def ew66 : Word := 0x5a005a00000000
def ew67 : Word := 0x5000500050005000
def ew68 : Word := 0x4800480048004800
def ew69 : Word := 0x5a0000005a000000
def ew70 : Word := 0x5a005a0000000000
def ew71 : Word := 0x505000005050
def ew72 : Word := 0x484800004848
def ew73 : Word := 0x5a0000005a00
def ew74 : Word := 0x5a5a00000000
def ew75 : Word := 0x5050000050500000
def ew76 : Word := 0x4848000048480000
def ew77 : Word := 0x5a5a000000000000
def ew78 : Word := 0x550000005500
def ew79 : Word := 0x448800004488
def ew80 : Word := 0x50a0000050a0
def ew81 : Word := 0x55aa00000000
def ew82 : Word := 0x55005500
def ew83 : Word := 0x44884488
def ew84 : Word := 0x50a050a0
def ew85 : Word := 0x55aa0000
def ew86 : Word := 0x5050505050505050
def ew87 : Word := 0x4848484848484848
def ew88 : Word := 0x5a005a005a005a00
def ew89 : Word := 0x5a5a00005a5a0000
def ew90 : Word := 0x5a5a5a5a00000000
def ew91 : Word := 0x8282828282828282
def ew92 : Word := 0xc0c0c0c0c0c0c0c0
def ew93 : Word := 0xc300c300c300c300
def ew94 : Word := 0xc3c30000c3c30000
def ew95 : Word := 0xc3c3c3c300000000
def ew96 : Word := 0xa0a0a0a0a0a0a0a0
def ew97 : Word := 0xf000f000f000f000
def ew98 : Word := 0xf0f00000f0f00000
def ew99 : Word := 0xf0f0f0f000000000
def ew100 : Word := 0xaa00aa00aa00aa
def ew101 : Word := 0xcc00cc00cc00cc
def ew102 : Word := 0xf000f000f000f0
def ew103 : Word := 0xff000000ff0000
def ew104 : Word := 0xff00ff00000000
def ew105 : Word := 0xaaaa0000aaaa
def ew106 : Word := 0xcccc0000cccc
def ew107 : Word := 0xf0f00000f0f0
def ew108 : Word := 0xff000000ff00
def ew109 : Word := 0xffff00000000
def ew110 : Word := 0xaaaaaaaa
def ew111 : Word := 0xcccccccc
def ew112 : Word := 0xf0f0f0f0
def ew113 : Word := 0xff00ff00
def ew114 : Word := 0xffff0000
def ew115 : Word := 0xaaaaaaaaaaaaaaaa
def ew116 : Word := 0xcccccccccccccccc
def ew117 : Word := 0xf0f0f0f0f0f0f0f0
def ew118 : Word := 0xff00ff00ff00ff00
def ew119 : Word := 0xffff0000ffff0000
def ew120 : Word := 0xffffffff00000000
def ew121 : Word := 0x2220222022202220
def ew122 : Word := 0x2222202022222020
def ew123 : Word := 0x2222222220202020
def ew124 : Word := 0x2222220022222200
def ew125 : Word := 0x2222222222002200
def ew126 : Word := 0x2222222222220000
def ew127 : Word := 0x2222222022222220
def ew128 : Word := 0x222000002220
def ew129 : Word := 0x2222222222202220
def ew130 : Word := 0x22202220
def ew131 : Word := 0x22002000220020
def ew132 : Word := 0x2222222222222020
def ew133 : Word := 0x22222020
def ew134 : Word := 0x22002200200020
def ew135 : Word := 0x222200002020
def ew136 : Word := 0x202020002020200
def ew137 : Word := 0x2222222222222200
def ew138 : Word := 0x22222200
def ew139 : Word := 0x202020202000200
def ew140 : Word := 0x222200002200
def ew141 : Word := 0x202020202020000
def ew142 : Word := 0x22002200220000
def ew143 : Word := 0x22222220
def ew144 : Word := 0x222200002220
def ew145 : Word := 0x22002200220020
def ew146 : Word := 0x202020202020200
def ew147 : Word := 0x80008000800080
def ew148 : Word := 0xe000e000e000e0
def ew149 : Word := 0x40004000400040
def ew150 : Word := 0xa0000000a00000
def ew151 : Word := 0xf000a000f000a0
def ew152 : Word := 0xa0000000a0
def ew153 : Word := 0x50000000500000
def ew154 : Word := 0xa000a000000000
def ew155 : Word := 0xf000f000a000a0
def ew156 : Word := 0xa000a0
def ew157 : Word := 0x50005000000000
def ew158 : Word := 0xc0000000c00000
def ew159 : Word := 0xf000c000f000c0
def ew160 : Word := 0xc0000000c0
def ew161 : Word := 0x30000000300000
def ew162 : Word := 0xc000c000000000
def ew163 : Word := 0xf000f000c000c0
def ew164 : Word := 0xc000c0
def ew165 : Word := 0x30003000000000
def ew166 : Word := 0xf0000000000000
def ew167 : Word := 0xf000f000f00000
def ew168 : Word := 0xf00000
def ew169 : Word := 0xf000000000
def ew170 : Word := 0xf0008000f00080
def ew171 : Word := 0x70000000700000
def ew172 : Word := 0xf000f000800080
def ew173 : Word := 0x70007000000000
def ew174 : Word := 0xe0000000e00000
def ew175 : Word := 0xe0000000e0
def ew176 : Word := 0xe000e000000000
def ew177 : Word := 0xe000e0
def ew178 : Word := 0xe000c000e000c0
def ew179 : Word := 0x4000c0004000c0
def ew180 : Word := 0xf000f000a00000
def ew181 : Word := 0x5000f000000000
def ew182 : Word := 0xc0008000c00080
def ew183 : Word := 0x30002000300020
def ew184 : Word := 0xf000a000000000
def ew185 : Word := 0xf000a0
def ew186 : Word := 0xe000e000c000c0
def ew187 : Word := 0x40004000c000c0
def ew188 : Word := 0xf000a000f00000
def ew189 : Word := 0x50000000f00000
def ew190 : Word := 0xc000c000800080
def ew191 : Word := 0x30003000200020
def ew192 : Word := 0xf0000000a00000
def ew193 : Word := 0xf0000000a0
def ew194 : Word := 0xf000f0000000c0
def ew195 : Word := 0xf0003000000000
def ew196 : Word := 0xf000f000300000
def ew197 : Word := 0xc000f000000000
def ew198 : Word := 0xf0000000f000c0
def ew199 : Word := 0xf0000000300000
def ew200 : Word := 0xf0003000f00000
def ew201 : Word := 0xc0000000f00000
def ew202 : Word := 0xc000c000f000c0
def ew203 : Word := 0xc000c0000000c0
def ew204 : Word := 0xc000f000c000c0
def ew205 : Word := 0xc0000000c000c0
def ew206 : Word := 0x6600660066000000
def ew207 : Word := 0x66000000
def ew208 : Word := 0x660000000000
def ew209 : Word := 0x3030303030303030
def ew210 : Word := 0xffccffccffccffcc
def ew211 : Word := 0xffffccccffffcccc
def ew212 : Word := 0xffffffffcccccccc
def ew213 : Word := 0xffffff00ffffff00
def ew214 : Word := 0xffffffffff00ff00
def ew215 : Word := 0xffffffffffff0000
def ew216 : Word := 0xf050f050f050f050
def ew217 : Word := 0xf0f05050f0f05050
def ew218 : Word := 0xf0f0f0f050505050
def ew219 : Word := 0xf0c0f0c0f0c0f0c0
def ew220 : Word := 0xf0f0c0c0f0f0c0c0
def ew221 : Word := 0xf0f0f0f0c0c0c0c0
def ew222 : Word := 0xaaaaaa00aaaaaa00
def ew223 : Word := 0x3333330033333300
def ew224 : Word := 0xf0f0f000f0f0f000
def ew225 : Word := 0xaaaaaaaaaa00aa00
def ew226 : Word := 0x3333333333003300
def ew227 : Word := 0xf0f0f0f0f000f000
def ew228 : Word := 0xaaaaaaaaaaaa0000
def ew229 : Word := 0x3333333333330000
def ew230 : Word := 0xf0f0f0f0f0f00000
def ew231 : Word := 0x5f5f5f005f5f5f00
def ew232 : Word := 0x5f5f5f5f5f005f00
def ew233 : Word := 0x5f5f5f5f5f5f0000
def ew234 : Word := 0xcfcfcf00cfcfcf00
def ew235 : Word := 0xcfcfcfcfcf00cf00
def ew236 : Word := 0xcfcfcfcfcfcf0000
def labelsBlock0 : Array Nat := #[
  0x3658,
  0x2e98,
  0x1e38,
  0x1,
  0x3184,
  0x3144,
  0x2984,
  0x2584,
  0x5,
  0x2590,
  0x36d0,
  0x3698,
  0xb1,
  0x2e38,
  0xe34,
  0xd24
]
def labelsBlock1 : Array Nat := #[
  0x1924,
  0x1b1,
  0x2384,
  0x268c,
  0x1cd,
  0x718,
  0x714,
  0x1e58,
  0x1d1,
  0xe2c,
  0xb24,
  0x2924,
  0xf38,
  0xd14,
  0x1514,
  0x1d5
]
def labelsBlock2 : Array Nat := #[
  0x1006,
  0x9,
  0x100a,
  0x1544,
  0xd,
  0x100e,
  0x2514,
  0x11,
  0x1012,
  0x1944,
  0x15,
  0x19,
  0x1d,
  0x21,
  0x25,
  0x29
]
def labelsBlock3 : Array Nat := #[
  0x2d,
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
def labelsBlock4 : Array Nat := #[
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
def labelsBlock5 : Array Nat := #[
  0xad,
  0xb5,
  0x1654,
  0xb9,
  0xbd,
  0x710,
  0xc1,
  0xc5,
  0x1550,
  0xc9,
  0xcd,
  0x1510,
  0xd1,
  0xd5,
  0x261c,
  0xd9
]
def labelsBlock6 : Array Nat := #[
  0xdd,
  0x2510,
  0xe1,
  0xe5,
  0xe9,
  0xed,
  0x1714,
  0xf1,
  0xf5,
  0xf9,
  0xfd,
  0x2714,
  0x101,
  0x105,
  0x109,
  0x3514
]
def labelsBlock7 : Array Nat := #[
  0x10d,
  0x111,
  0x115,
  0x119,
  0x11d,
  0x121,
  0x125,
  0x129,
  0x12d,
  0x131,
  0x135,
  0x139,
  0x13d,
  0x141,
  0x161c,
  0x145
]
def labelsBlock8 : Array Nat := #[
  0x149,
  0x14d,
  0x151,
  0x155,
  0x159,
  0x15d,
  0x161,
  0x3650,
  0x2790,
  0x165,
  0x169,
  0x16d,
  0x171,
  0x3618,
  0x1758,
  0x175
]
def labelsBlock9 : Array Nat := #[
  0x179,
  0x17d,
  0x181,
  0x185,
  0x2798,
  0x189,
  0x18d,
  0x191,
  0x195,
  0x199,
  0x35d0,
  0x19d,
  0x1a1,
  0x1a5,
  0x1a9,
  0x1ad
]
def labelsBlock10 : Array Nat := #[
  0x1a64,
  0x1e68,
  0x2928,
  0x2aa4,
  0x2ea8,
  0x1b5,
  0x1b9,
  0x1bd,
  0x1c1,
  0x1c5,
  0x1c9,
  0x1c64,
  0x1002,
  0x1e70,
  0x1052,
  0x1056
]
def labelsBlock11 : Array Nat := #[
  0x304,
  0x104e,
  0x105a,
  0xd30,
  0x101a,
  0x101e,
  0x1022,
  0x2eb0,
  0x1016,
  0x29a0,
  0x1d9,
  0x60c,
  0x106e,
  0x308,
  0x1072,
  0xb28
]
def labelsBlock12 : Array Nat := #[
  0x1dd,
  0x1076,
  0x1348,
  0x1e1,
  0x107a,
  0x2388,
  0x1e5,
  0x50c,
  0x1e9,
  0x90c,
  0x1ed,
  0x1344,
  0x1f1,
  0x1f5,
  0x1f9,
  0xd04
]
def labelsBlock13 : Array Nat := #[
  0x1fd,
  0x1504,
  0x36c8,
  0x201,
  0x2504,
  0x205,
  0x209,
  0x20d,
  0x103a,
  0x103e,
  0x102e,
  0x1066,
  0x1026,
  0x1046,
  0x102a,
  0x104a
]
def labelsBlock14 : Array Nat := #[
  0x1960,
  0x211,
  0x215,
  0x219,
  0x62006e,
  0x21d,
  0xb08,
  0x1032,
  0x63006e,
  0x221,
  0x630072,
  0x1308,
  0x31c0,
  0x1036,
  0x64006e,
  0x225
]
def labelsBlock15 : Array Nat := #[
  0x640072,
  0x640076,
  0x2308,
  0x721072,
  0x106a,
  0x721076,
  0x72107a,
  0x704,
  0x229,
  0x22d,
  0x231,
  0x52106e,
  0x531076,
  0x53107a,
  0x235,
  0x53106e
]
def labelsBlock16 : Array Nat := #[
  0x531072,
  0x120c,
  0x54107a,
  0x220c,
  0x110c,
  0x239,
  0x54106e,
  0x541072,
  0x541076,
  0x210c,
  0x23d,
  0x610016,
  0x632076,
  0x63207a,
  0x620016,
  0x632072
]
def labelsBlock17 : Array Nat := #[
  0x64207a,
  0x630016,
  0x642072,
  0x642076,
  0x521016,
  0x53206e,
  0x241,
  0x54307a,
  0x245,
  0x249,
  0x531016,
  0x54206e,
  0x543076,
  0x24d,
  0x251,
  0x255
]
def labelsBlock18 : Array Nat := #[
  0x532016,
  0x54306e,
  0x543072,
  0x259,
  0x25d,
  0x261,
  0x532066,
  0x265,
  0x420026,
  0x53204a,
  0x71003e,
  0x710046,
  0x42002e,
  0x71004a,
  0x42002a,
  0x542066
]
def labelsBlock19 : Array Nat := #[
  0x532046,
  0x269,
  0x543066,
  0x53203e,
  0x26d,
  0x401016,
  0x720072,
  0x62001e,
  0x720026,
  0x620022,
  0x72002a,
  0x402016,
  0x720076,
  0x1c9630072,
  0x630022,
  0x403016
]
def labelsBlock20 : Array Nat := #[
  0x72007a,
  0x1c9640072,
  0x1c9640076,
  0x720036,
  0x53206a,
  0x271,
  0x721026,
  0x72102e,
  0x72102a,
  0x54206a,
  0x275,
  0x54306a,
  0x279,
  0x410016,
  0x412072,
  0xa0c
]
def labelsBlock21 : Array Nat := #[
  0x114931076,
  0x11493107a,
  0x412026,
  0x41202a,
  0x420016,
  0x114931072,
  0x412076,
  0x11494107a,
  0x430016,
  0x114941072,
  0x114941076,
  0x41207a,
  0x412036,
  0x11413206e,
  0x105e,
  0x430072
]
def labelsBlock22 : Array Nat := #[
  0x430076,
  0x11414307a,
  0x43002a,
  0x1d453206e,
  0x731072,
  0x731076,
  0x1d454307a,
  0x73102a,
  0x110121016,
  0x432072,
  0x432076,
  0x11494307a,
  0x43202a,
  0x11414206e,
  0x1062,
  0x440072
]
def labelsBlock23 : Array Nat := #[
  0x114143076,
  0x430026,
  0x43007a,
  0x1d454206e,
  0x741072,
  0x1d4543076,
  0x731026,
  0x73107a,
  0x110131016,
  0x442072,
  0x114943076,
  0x432026,
  0x43207a,
  0x11414306e,
  0x114143072,
  0x440076
]
def labelsBlock24 : Array Nat := #[
  0x44007a,
  0x1d454306e,
  0x1d4543072,
  0x741076,
  0x74107a,
  0x110132016,
  0x114943072,
  0x442076,
  0x44207a,
  0x1d0121016,
  0x72001a,
  0x72001e,
  0x1d0131016,
  0x73001a,
  0x1cd020026,
  0x720022
]
def labelsBlock25 : Array Nat := #[
  0x1d0132016,
  0x73001e,
  0x730022,
  0x11453206e,
  0x1cd721072,
  0x1cd721076,
  0x11454206e,
  0x1d1721072,
  0x1cd321026,
  0x1cd72107a,
  0x11454306e,
  0x1d1721076,
  0x1d172107a
]
def labelsGet (i : Nat) : Nat :=
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
def lh (s : Nat) (d : List Nat) (ws : List Nat) (i : Nat) : Nat :=
  labelsGet (d.getD (((ws.getD (i / (64 / s)) 0) >>> ((i % (64 / s)) * s)) % 2 ^ s) 0)
def viewsBlock0 : Array View := #[
  ⟨0x4040404040404040,⟨6,by decide⟩,0x4040400040000000,[ew0,ew1,ew2],3,lh 2 [0,1,2,3] [0xd900]⟩,
  ⟨0x202020202020202,⟨1,by decide⟩,0x202020002000000,[ew3,ew4,ew5],3,fun _ => 3⟩,
  ⟨0x22002200220022,⟨1,by decide⟩,0x22002000200000,[ew6,ew7,ew8],3,fun _ => 3⟩,
  ⟨0x222200002222,⟨1,by decide⟩,0x222000002000,[ew9,ew10,ew11],3,fun _ => 3⟩,
  ⟨0x22222222,⟨1,by decide⟩,0x22202000,[ew12,ew13,ew14],3,fun _ => 3⟩,
  ⟨0x2222222222222222,⟨1,by decide⟩,0x2222222022202000,[ew15,ew16,ew17,ew18],6,lh 3 [4,5,6,7,8] [0x8d2000249000]⟩,
  ⟨0xf000f000f000f0,⟨4,by decide⟩,0xe000a000a00080,[ew19,ew20,ew21,ew22],5,lh 3 [9,10,0,11,12] [0x808608408408]⟩,
  ⟨0xf0f00000f0f0,⟨4,by decide⟩,0xe0a00000a080,[ew23,ew24,ew25,ew26],5,fun _ => 3⟩,
  ⟨0xf0f0f0f0,⟨4,by decide⟩,0xe0a0a080,[ew27,ew28,ew29,ew30],5,fun _ => 3⟩,
  ⟨0xff000000ff0000,⟨16,by decide⟩,0xea000000a80000,[ew31,ew32,ew21,ew33],5,fun _ => 3⟩,
  ⟨0xff00ff00000000,⟨32,by decide⟩,0xea00a800000000,[ew34,ew35,ew22,ew33],5,fun _ => 3⟩,
  ⟨0xff000000ff00,⟨8,by decide⟩,0xea000000a800,[ew36,ew37,ew25,ew38],5,fun _ => 3⟩,
  ⟨0xff00ff00,⟨8,by decide⟩,0xea00a800,[ew39,ew40,ew29,ew41],5,fun _ => 3⟩,
  ⟨0xffff0000,⟨16,by decide⟩,0xeaa80000,[ew42,ew43,ew30,ew41],5,fun _ => 3⟩,
  ⟨0x6060606060606060,⟨5,by decide⟩,0x6060602060202000,[ew44,ew45,ew46,ew47],6,fun _ => 3⟩,
  ⟨0x66006600660066,⟨1,by decide⟩,0x62002000200000,[ew48,ew49,ew50,ew51],6,fun _ => 3⟩
]
def viewsBlock1 : Array View := #[
  ⟨0x6600660066006600,⟨9,by decide⟩,0x6200620062002000,[ew52,ew45,ew53,ew54],4,lh 3 [13,14,15,16,17] [0x851651000000]⟩,
  ⟨0x666600006666,⟨1,by decide⟩,0x622000002000,[ew55,ew56,ew57,ew58],6,fun _ => 3⟩,
  ⟨0x66666666,⟨1,by decide⟩,0x62202000,[ew59,ew60,ew61,ew62],6,fun _ => 3⟩,
  ⟨0x5a005a005a005a,⟨1,by decide⟩,0x4a000800080008,[ew63,ew64,ew65,ew66],4,fun _ => 3⟩,
  ⟨0x5a005a005a005a00,⟨9,by decide⟩,0x4a004a004a000800,[ew67,ew68,ew69,ew70],4,fun _ => 3⟩,
  ⟨0x5a5a00005a5a,⟨1,by decide⟩,0x4a0800000808,[ew71,ew72,ew73,ew74],4,fun _ => 3⟩,
  ⟨0x5a5a00005a5a0000,⟨17,by decide⟩,0x4a4a00004a080000,[ew75,ew76,ew69,ew77],4,fun _ => 3⟩,
  ⟨0x55aa000055aa,⟨1,by decide⟩,0x40a800000088,[ew78,ew79,ew80,ew81],4,fun _ => 3⟩,
  ⟨0x55aa55aa,⟨1,by decide⟩,0x40a80088,[ew82,ew83,ew84,ew85],4,fun _ => 3⟩,
  ⟨0x5a5a5a5a5a5a5a5a,⟨1,by decide⟩,0x4a4a4a084a080808,[ew86,ew87,ew88,ew89,ew90],7,lh 3 [5,4,6,18,19,20] [0x1249000000000000,0x163692449]⟩,
  ⟨0xc3c3c3c3c3c3c3c3,⟨0,by decide⟩,0xc2c2c280c2808080,[ew91,ew92,ew93,ew94,ew95],7,fun _ => 3⟩,
  ⟨0xf0f0f0f0f0f0f0f0,⟨4,by decide⟩,0xe0e0e0a0e0a0a080,[ew96,ew92,ew97,ew98,ew99],7,lh 3 [21,22,23,11,13,24] [0x408808408608408,0x1410810c1]⟩,
  ⟨0xff00ff00ff00ff,⟨0,by decide⟩,0xea00a800a80088,[ew100,ew101,ew102,ew103,ew104],7,fun _ => 3⟩,
  ⟨0xffff0000ffff,⟨0,by decide⟩,0xeaa80000a888,[ew105,ew106,ew107,ew108,ew109],7,fun _ => 3⟩,
  ⟨0xffffffff,⟨0,by decide⟩,0xeaa8a888,[ew110,ew111,ew112,ew113,ew114],7,fun _ => 3⟩,
  ⟨0xffffffffffffffff,⟨0,by decide⟩,0xeaeaeaa8eaa8a888,[ew115,ew116,ew117,ew118,ew119,ew120],10,lh 4 [25,26,29,27,14,28,15,30,31] [0x3514301035143010,0x3514301035143010,0x7514601025146010,0x8514601022222222]⟩
]
def viewsGet (i : Nat) : Option View :=
  if i < 16 then
    viewsBlock0[(i-0)]?
  else
    viewsBlock1[(i-16)]?
def nodesBlock0 : Array Node := #[
  ⟨0,3,[ew0,ew1,ew2],lh 3 [1,11,0,13,23,2] [0x483112144265808,0x1522c946b71b]⟩,
  ⟨5,6,[ew15,ew16,ew17,ew18],lh 5 [4,5,6,7,32,35,27,34,16,37,41,15,40,29,30,38,33,36,39,42,43,44] [0x22c4282dab20c42,0x895c520c0038da3,0x2142148dc321400,0x615e520c2190de3,0x3a8009a90838800,0xa08c23a82148902,0x4a0c6628c638821,0x62021480c0a8020]⟩,
  ⟨5,5,[ew15,ew16,ew121,ew17,ew18],lh 5 [4,5,32,27,16,15,29,34,30,38,7,6,37,40,45,46,47,48,49,50,51,52] [0x28947318a228842,0x1000e420a001c4a,0x1042f4a4a109508,0x3000212cc259529,0x30426210e004084,0x6000618ce10c463,0x6842c2126004884,0x20c6d18ea10d063,0x40840300020]⟩,
  ⟨5,5,[ew15,ew16,ew17,ew122,ew18],lh 5 [5,6,32,27,41,35,30,37,29,38,7,34,4,40,45,53,54,49,55,56,57,58] [0x2a0a2085c841421,0x28947318a228842,0x1000f4a4a001c4a,0x218848102609525,0x22c848902b084e1,0x80011848000641,0x30c62130c261063,0x68c66000e31cc00,0xd002a31d000]⟩,
  ⟨5,5,[ew15,ew16,ew17,ew18,ew123],lh 5 [4,6,32,16,7,41,38,40,29,30,34,37,5,46,53,35,59,51,60,61,57,62] [0x22082085a841021,0x22482001c949000,0x208873188220842,0x2800518c2001c4f,0x9821804a628461,0xa821884aa294e5,0x18009806619645,0x2c00a006b18ce3,0x2130c260ea3]⟩,
  ⟨5,5,[ew15,ew16,ew17,ew124,ew18],lh 5 [5,7,35,34,41,16,27,38,37,32,15,6,4,40,47,54,49,63,64,65,66,67] [0x8c2a2114e50481,0xa0222944f104a1,0xc4224885010521,0x11c410002708800,0x225682948320c63,0x18012318800206b,0x298c31b0a9610c6,0x69ce50010634c00,0xd002a73d000]⟩,
  ⟨5,5,[ew15,ew16,ew17,ew18,ew125],lh 5 [4,7,6,35,34,27,30,16,40,32,15,37,5,48,59,51,68,64,41,69,66,70] [0x902a1094d50442,0x98230006618400,0x1a0612842e08ca5,0x1c0614842f08d23,0x11c440022738800,0x124482944411084,0x1400980e52a092,0x2c00a00cb31d07,0x4230a961aa6]⟩,
  ⟨5,5,[ew15,ew16,ew17,ew18,ew126],lh 5 [6,7,4,5,37,15,29,35,41,40,32,34,56,61,57,71,65,69,66,72,16,27] [0x9825000a628400,0x9027108ec38442,0x3a4e118c2d09c63,0x2bca15042e09545,0x10081091040042,0x4250018c1102063,0x34cc05801201966,0x1284918c4411084,0x42546a1a494]⟩,
  ⟨5,4,[ew16,ew121,ew17,ew122,ew18],lh 4 [5,27,30,35,6,29,34,15,7,4,73,37] [0x3b1010757652a244,0x101991010883623,0x101]⟩,
  ⟨5,4,[ew16,ew121,ew17,ew18,ew123],lh 4 [4,16,7,38,6,29,34,15,5,74,40,35] [0x1075765393101044,0x11001b226322a20,0x8810]⟩,
  ⟨5,4,[ew15,ew121,ew17,ew124,ew18],lh 4 [5,16,38,27,15,7,32,41,6,4,73,29,37] [0x1c2020b44641a155,0x303993030887617,0x202]⟩,
  ⟨5,4,[ew15,ew121,ew17,ew18,ew125],lh 4 [4,6,30,27,15,32,16,5,7,74,29,40,41] [0x60a4454393202081,0x26003c115311b10,0x7720]⟩,
  ⟨5,4,[ew15,ew16,ew17,ew127,ew18],lh 4 [5,16,27,41,35,30,7,6,4,15,38,40,75] [0x1540a06651414393,0xb02028820207713,0xc]⟩,
  ⟨5,4,[ew128,ew15,ew16,ew17,ew18],lh 4 [4,5,27,35,41,15,7,29,6,16,38] [0x5421219088746653,0x21704031a1503034,0x100221]⟩,
  ⟨5,4,[ew15,ew16,ew17,ew18,ew129],lh 4 [4,6,7,27,38,16,5,15,30,35,41,37,76] [0x5092422320802171,0xc00b5003a1311410,0x66]⟩,
  ⟨5,4,[ew130,ew15,ew16,ew17,ew18],lh 4 [4,6,5,7,16,15,29,35,41,27,30] [0x5192404081617353,0x121040523230a031,0x200462]⟩
]
def nodesBlock1 : Array Node := #[
  ⟨5,4,[ew16,ew17,ew122,ew18,ew123],lh 4 [6,41,7,38,35,4,30,37,5,77,40] [0x1001100102100110,0x27322a4647639355,0x8842]⟩,
  ⟨5,4,[ew15,ew16,ew122,ew124,ew18],lh 4 [5,35,27,41,38,16,7,32,6,4,73,30,34] [0x5c1040b1176613a3,0x202995720208853,0x404]⟩,
  ⟨5,4,[ew131,ew15,ew16,ew17,ew18],lh 4 [5,6,27,35,16,30,15,7,4,41,38] [0x6102028854917736,0x10154130a0543431,0x20220]⟩,
  ⟨5,4,[ew15,ew16,ew122,ew18,ew126],lh 4 [4,6,5,35,29,32,30,41,7,77,40,16,27] [0x7063353292803141,0x5200a4116721210,0xc2b0]⟩,
  ⟨5,4,[ew15,ew16,ew17,ew18,ew132],lh 4 [4,6,5,7,35,41,29,15,34,78,38,16,27] [0x5073423230403161,0xb0200a9118521210,0xc2]⟩,
  ⟨5,4,[ew133,ew15,ew16,ew17,ew18],lh 4 [4,6,7,35,41,27,30,5,16,29] [0x9177806041413232,0x1410403225203021,0x600551]⟩,
  ⟨5,4,[ew15,ew16,ew17,ew123,ew125],lh 4 [4,6,7,27,30,32,38,16,5,74,35,34,41] [0x706225a220402191,0x40067003c1311b10,0x8835]⟩,
  ⟨5,4,[ew134,ew15,ew16,ew17,ew18],lh 4 [4,7,16,27,38,15,6,5,41,35,30] [0x5177430202661915,0x382020411310a018,0x200334]⟩,
  ⟨5,4,[ew15,ew16,ew17,ew123,ew126],lh 4 [4,6,5,7,29,32,38,41,77,35,37,16,27] [0x7063359230803141,0xb0200a4116721210,0xc225]⟩,
  ⟨5,4,[ew135,ew15,ew16,ew17,ew18],lh 4 [5,6,7,35,41,16,4,38,27,29] [0x9180706614142323,0x1014513020253221,0x70540]⟩,
  ⟨5,4,[ew136,ew15,ew16,ew17,ew18],lh 4 [5,7,16,27,41,30,38,29,6,4,35] [0x71060699258847a1,0x3024256010125114,0x30330]⟩,
  ⟨5,4,[ew15,ew17,ew124,ew18,ew125],lh 4 [7,6,35,16,27,41,4,37,5,79,40] [0x2005200401210320,0x17411a5337349466,0x8851]⟩,
  ⟨5,4,[ew15,ew16,ew124,ew18,ew126],lh 4 [4,7,5,16,41,15,35,34,6,79,40,27] [0x5113621210601451,0x7200a3437429280,0xb230]⟩,
  ⟨5,4,[ew15,ew16,ew17,ew18,ew137],lh 4 [4,5,6,7,35,27,15,32,80,16,29,30,38] [0x8337413130403262,0xb01005a251212090,0xc1]⟩,
  ⟨5,4,[ew138,ew15,ew16,ew17,ew18],lh 3 [4,6,7,35,16,41,5,15] [0x611e76820a6969a,0x402526910349a]⟩,
  ⟨5,4,[ew139,ew15,ew16,ew17,ew18],lh 4 [4,6,27,30,38,35,7,29,5,16,41] [0x71882403031a1766,0x1410905242305051,0x900221]⟩
]
def nodesBlock2 : Array Node := #[
  ⟨5,4,[ew15,ew16,ew17,ew125,ew126],lh 4 [4,5,6,7,27,15,35,34,79,41,37,16] [0x5334613130603252,0xb0100a4227912080,0x4117]⟩,
  ⟨5,4,[ew140,ew15,ew16,ew17,ew18],lh 3 [5,6,7,35,27,41,4,15] [0x3691e6083634d4d3,0x824041b4b082]⟩,
  ⟨5,4,[ew141,ew15,ew16,ew17,ew18],lh 4 [4,5,6,38,29,30,7,41,16,27,15] [0xa219130805242466,0x2120703131505042,0x100371]⟩,
  ⟨5,4,[ew142,ew15,ew16,ew17,ew18],lh 3 [4,5,7,27,15,16,6,35] [0xe1488b2c5176514,0x101b2cd14728a]⟩,
  ⟨5,3,[ew121,ew122,ew124,ew18],lh 4 [5,27,16,7,32,6,4,38,34,41] [0x6624101055943328,0x7070101]⟩,
  ⟨5,3,[ew121,ew17,ew123,ew125],lh 4 [4,6,27,16,32,5,34,41,38,30] [0x3002711421161030,0x55249008]⟩,
  ⟨5,3,[ew143,ew15,ew16,ew17],lh 3 [4,5,6,7,35,27,15,16] [0x6206b2a082a92e1,0x87]⟩,
  ⟨5,3,[ew144,ew15,ew16,ew18],lh 3 [4,5,6,7,35,27,16,15] [0x18596baa01190118,0x14a]⟩,
  ⟨5,3,[ew16,ew122,ew123,ew126],lh 4 [4,5,6,41,32,38,29,37,16,27] [0x1007622531212030,0x91148004]⟩,
  ⟨5,3,[ew145,ew15,ew17,ew18],lh 3 [4,5,6,7,27,35,15,16] [0x4a5962828c1c259a,0x40]⟩,
  ⟨5,3,[ew15,ew124,ew125,ew126],lh 3 [4,5,7,27,35,34,15,37] [0x5605207c93851420,0xc9]⟩,
  ⟨5,3,[ew146,ew16,ew17,ew18],lh 3 [4,5,6,7,35,27,15,16] [0x5a514382cc103593,0x40]⟩,
  ⟨6,5,[ew19,ew20,ew21,ew22],lh 6 [22,21,30,0,38,10,11,9,88,111,81,82,83,84,85,86,87,89,90,91,92,93,94,95,96,97,98,99,100,101,102,103,104,105,106,107,108,109,110,112,113] [0x14130100b287147,0x4011813c700e341,0x93488188448082,0x5c71165410c3501,0x806811196070c7,0x7450827051866c0,0xc58001007c019e,0x9000e3885104845,0x1099860c3942104,0xa020c99c6]⟩,
  ⟨6,4,[ew147,ew19,ew20,ew21,ew22],lh 4 [38,30,9,10,11,0,88,21,22,114,115,116,117,82] [0x223dc0b5a4948372,0x503041310206161,0x105]⟩,
  ⟨6,4,[ew19,ew20,ew148,ew21,ew22],lh 4 [21,22,38,30,0,11,82,9,10,118,119,120,121] [0x1810420053070106,0x22c2b3a391241135,0x324]⟩,
  ⟨6,4,[ew6,ew19,ew20,ew21,ew22],lh 4 [38,21,30,0,11,10,22,9,85] [0x1815030324246671,0x305042521301142,0x203]⟩
]
def nodesBlock3 : Array Node := #[
  ⟨6,4,[ew149,ew19,ew20,ew21,ew22],lh 4 [38,22,30,0,11,9,21,88,10,85] [0x5915303042428166,0x103112410507272,0x203]⟩,
  ⟨6,4,[ew150,ew19,ew20,ew21,ew22],lh 4 [22,38,21,10,30,9,85,0,88,122,123,124,125,126,11] [0x6625c1b144a09082,0x10130033025122ed,0x717]⟩,
  ⟨6,4,[ew19,ew20,ew21,ew151,ew22],lh 4 [22,38,30,10,88,21,0,82,126,127,128,11,129,130] [0x2301614552480307,0xc2161b20130a0090,0x1d1]⟩,
  ⟨6,4,[ew152,ew19,ew20,ew21,ew22],lh 4 [22,38,10,0,21,30,88,82,11,91] [0x207131355020244,0x1012002201316968,0x313]⟩,
  ⟨6,4,[ew153,ew19,ew20,ew21,ew22],lh 4 [0,38,22,21,10,30,85,88,11,9,91] [0x6639010185424273,0x1010225423010a53,0x10]⟩,
  ⟨6,4,[ew154,ew19,ew20,ew21,ew22],lh 4 [11,0,22,21,30,85,135,9,131,132,133,134,38,82,91,94] [0x553dc1b0a0928273,0x46612040231fe040,0x101]⟩,
  ⟨6,4,[ew19,ew20,ew21,ew22,ew155],lh 4 [22,30,9,11,136,10,0,94,38,21,137,138,139,140] [0x1309282723124402,0x11c1331b00a05503,0x66d]⟩,
  ⟨6,4,[ew156,ew19,ew20,ew21,ew22],lh 4 [22,10,30,11,0,21,9,141,38,97] [0x101842323010155,0x2011002109642326,0x774]⟩,
  ⟨6,4,[ew157,ew19,ew20,ew21,ew22],lh 4 [11,21,22,38,30,10,88,9,0,97] [0x2116830404525271,0x3235304029311060,0x400]⟩,
  ⟨6,4,[ew19,ew158,ew20,ew21,ew22],lh 4 [142,38,0,21,22,11,88,10,143,30] [0x210300340063003,0x1212149821215574,0x212]⟩,
  ⟨6,4,[ew19,ew20,ew21,ew159,ew22],lh 4 [142,9,10,0,38,11,143,22,30] [0x110100110011202,0x4353485322472526,0x343]⟩,
  ⟨6,4,[ew160,ew19,ew20,ew21,ew22],lh 4 [9,10,30,0,142,21,38,22,11,144,145,102] [0x141a39382715050,0x23116b1240042420,0x263]⟩,
  ⟨6,4,[ew161,ew19,ew20,ew21,ew22],lh 4 [88,9,0,22,10,30,11,38,146,147,142,102] [0x3a30928255440101,0x73723b6301101001,0x262]⟩,
  ⟨6,4,[ew19,ew162,ew20,ew21,ew22],lh 4 [148,88,22,30,11,38,0,10,149] [0x1001011020011001,0x5258234266434372,0x354]⟩,
  ⟨6,4,[ew19,ew20,ew21,ew22,ew163],lh 4 [88,148,30,11,10,0,22,38,149] [0x110011010010110,0x3322352665483242,0x772]⟩,
  ⟨6,4,[ew164,ew19,ew20,ew21,ew22],lh 4 [148,38,30,88,142,22,10,11,150,151,0,107] [0x3003a19282554040,0x1b61726210130330,0x217]⟩
]
def nodesBlock4 : Array Node := #[
  ⟨6,4,[ew165,ew19,ew20,ew21,ew22],lh 4 [148,22,30,88,9,38,11,0,10,152,153,107] [0x100355a292814040,0x2b71126130030330,0x267]⟩,
  ⟨6,4,[ew19,ew20,ew166,ew21,ew22],lh 4 [148,154,22,38,10,30,88,107,11,0,155] [0x3116011001102006,0x9385734325422442,0x53a]⟩,
  ⟨6,4,[ew19,ew20,ew21,ew22,ew167],lh 4 [21,154,11,0,22,10,155,30,38] [0x110031002101001,0x2326455435342524,0x837]⟩,
  ⟨6,4,[ew168,ew19,ew20,ew21,ew22],lh 4 [21,11,154,22,38,88,0,10,156,157,30,107,111] [0x200266a193835050,0xb474171302200120,0xc14]⟩,
  ⟨6,4,[ew169,ew19,ew20,ew21,ew22],lh 4 [21,22,0,154,148,11,10,30,158,159,38,111] [0x3003a25591814040,0x2621176102300330,0xb27]⟩,
  ⟨6,3,[ew19,ew20,ew170,ew22],lh 3 [9,126,10,0,11,38,30] [0x5695896201048048,0xe3]⟩,
  ⟨6,3,[ew171,ew19,ew20,ew22],lh 4 [9,10,88,0,126,11,38,30,21] [0x180353615172044,0x31162002]⟩,
  ⟨6,3,[ew19,ew20,ew21,ew172],lh 3 [9,88,38,10,30,0,82,11] [0x2a9af1c2010480f0,0x115]⟩,
  ⟨6,3,[ew173,ew19,ew20,ew21],lh 4 [38,30,10,88,9,0,82,126,11] [0x4266015005204003,0x81211317]⟩,
  ⟨6,3,[ew19,ew20,ew174,ew22],lh 4 [21,22,38,30,0,82,88,9,11] [0x1381072006301005,0x32421241]⟩,
  ⟨6,3,[ew175,ew19,ew20,ew22],lh 3 [21,22,38,30,10,0,88,82] [0x115020755330b0c6,0x54]⟩,
  ⟨6,3,[ew19,ew20,ew176,ew21],lh 4 [21,22,38,30,0,82,9,88,11] [0x1241073006201005,0x23421381]⟩,
  ⟨6,3,[ew177,ew19,ew20,ew21],lh 4 [21,22,38,30,10,9,0,82,11] [0x1007263214120205,0x13410830]⟩,
  ⟨6,3,[ew19,ew178,ew21,ew22],lh 4 [21,38,22,9,85,82,10,0,30] [0x2862031005504403,0x71712162]⟩,
  ⟨6,3,[ew179,ew19,ew21,ew22],lh 4 [21,22,38,30,85,10,82,88,9,0] [0x730125113514406,0x32920820]⟩,
  ⟨6,3,[ew19,ew20,ew21,ew180],lh 4 [21,38,22,10,9,85,126,11,0,30] [0x2332041007605504,0x91812132]⟩
]
def nodesBlock5 : Array Node := #[
  ⟨6,3,[ew181,ew19,ew20,ew21],lh 4 [21,38,22,30,10,85,9,0,82,88] [0x5508137112426010,0x23420930]⟩,
  ⟨6,3,[ew19,ew182,ew21,ew22],lh 4 [22,38,30,85,88,10,82,126,9,0] [0x250181424273306,0x21910150]⟩,
  ⟨6,3,[ew183,ew19,ew21,ew22],lh 3 [85,22,38,30,10,0,82,88] [0x21501d8311319c08,0xd5]⟩,
  ⟨6,3,[ew19,ew20,ew21,ew184],lh 4 [21,38,22,30,85,10,82,88,9,0] [0x2352081007304406,0x31912152]⟩,
  ⟨6,3,[ew185,ew19,ew20,ew21],lh 4 [22,38,30,10,21,9,0,82,126,88] [0x307162103014415,0x2302928]⟩,
  ⟨6,3,[ew19,ew186,ew21,ew22],lh 4 [0,11,30,21,85,22,82,91,94,38] [0x1215308071214436,0x1020905]⟩,
  ⟨6,3,[ew187,ew19,ew21,ew22],lh 4 [11,0,21,85,22,30,38,94,82,91] [0x9050161405043328,0x10162177]⟩,
  ⟨6,3,[ew19,ew20,ew188,ew22],lh 4 [11,0,30,21,85,94,22,135,82,91] [0x206315590204438,0x10127716]⟩,
  ⟨6,3,[ew189,ew19,ew20,ew22],lh 4 [11,0,30,22,21,85,94,135,91,38,82] [0x554a101920030820,0x77134166]⟩,
  ⟨6,3,[ew19,ew190,ew21,ew22],lh 3 [30,10,11,22,9,136,94,88] [0x64b408f26084a59,0x12]⟩,
  ⟨6,3,[ew191,ew19,ew21,ew22],lh 3 [22,30,10,9,11,135,88,85] [0x1edd30b090088c02,0x65]⟩,
  ⟨6,3,[ew19,ew20,ew192,ew22],lh 4 [22,10,30,9,88,94,21,11,0] [0x210633544230101,0x28720110]⟩,
  ⟨6,3,[ew193,ew19,ew20,ew22],lh 3 [22,88,30,10,21,9,11,0] [0x3690c15f20c2911,0x1b]⟩,
  ⟨6,3,[ew19,ew158,ew159,ew22],lh 3 [142,9,0,11,38,21,102] [0x4513533048201a03,0x2]⟩,
  ⟨6,3,[ew19,ew20,ew21,ew194],lh 3 [30,10,142,9,0,102,38,11] [0x84ea084da083651,0x3c]⟩,
  ⟨6,3,[ew19,ew20,ew21,ew195],lh 3 [30,10,142,9,0,102,38,11] [0x84ea084da083651,0x3c]⟩
]
def nodesBlock6 : Array Node := #[
  ⟨6,3,[ew19,ew20,ew21,ew196],lh 3 [88,10,22,142,9,30,38,0] [0x644a44a603804058,0x16f]⟩,
  ⟨6,3,[ew19,ew20,ew197,ew21],lh 3 [22,88,30,9,0,11,142,10] [0x20a81e044b2d9181,0x154]⟩,
  ⟨6,3,[ew19,ew162,ew21,ew163],lh 3 [148,88,22,30,11,10,107] [0x28b28eb401048201,0x3]⟩,
  ⟨6,3,[ew19,ew20,ew198,ew22],lh 3 [38,88,148,30,10,22,107,0] [0xc20b6308144a291,0xc7]⟩,
  ⟨6,3,[ew19,ew20,ew199,ew22],lh 3 [38,148,88,22,10,30,107,11] [0xc2076304229164a,0x147]⟩,
  ⟨6,3,[ew19,ew20,ew200,ew22],lh 3 [148,88,22,10,30,107,38,0] [0x4b5a51a201048401,0x1b7]⟩,
  ⟨6,3,[ew19,ew201,ew20,ew22],lh 3 [38,148,88,22,30,0,11,107] [0x8288f304264a291,0x1c5]⟩,
  ⟨6,3,[ew19,ew20,ew166,ew167],lh 4 [154,0,148,21,10,38,22,107,111] [0x1416300321010220,0x817545]⟩,
  ⟨6,3,[ew19,ew202,ew21,ew22],lh 3 [21,154,0,11,38,111,22,30] [0x45147de0880c8201,0x16a]⟩,
  ⟨6,3,[ew19,ew203,ew21,ew22],lh 4 [21,154,11,38,0,111,22,30,10] [0x2726011002101001,0x55234483]⟩,
  ⟨6,3,[ew19,ew204,ew21,ew22],lh 3 [21,154,0,11,22,30,111,38] [0x55d475c0880c8201,0x1b2]⟩,
  ⟨6,3,[ew19,ew205,ew21,ew22],lh 3 [21,154,0,38,11,111,22,10] [0x34d393e088048201,0x16a]⟩,
  ⟨16,4,[ew52,ew45,ew53,ew54],lh 4 [2,13,15,14,160,16,161,27,163,164,162,165,166,167,168,169] [0x4353464323363422,0x7881137a30045540,0x2006556002523118,0xb010211979911272,0xf0e11dc]⟩,
  ⟨16,3,[ew52,ew45,ew206],lh 3 [164,163,2,15,14,27,162] [0x1a4a32e204720059,0xd214041d712]⟩,
  ⟨16,3,[ew52,ew45,ew53,ew206],lh 4 [163,164,161,160,13,2,14,162,15] [0x1221400703301610,0x554228]⟩,
  ⟨16,3,[ew52,ew45,ew54,ew206],lh 3 [161,163,14,2,164,15,13] [0x360512064a44a081,0x6]⟩
]
def nodesBlock7 : Array Node := #[
  ⟨16,3,[ew207,ew52,ew45,ew54],lh 4 [161,163,164,2,16,170,14,162,13] [0x1706015302024131,0x22081]⟩,
  ⟨16,3,[ew208,ew52,ew45,ew53],lh 4 [161,163,164,2,162,13,170,14,16] [0x3107016320201514,0x200218]⟩,
  ⟨16,2,[ew52,ew45,ew206],lh 3 [13,15,14,27,160,162] [0xc10c5891]⟩,
  ⟨25,7,[ew86,ew87,ew88,ew89,ew90],lh 5 [5,4,6,18,172,19,2,13,23,171,32,174,173,175,176,177,178] [0x214632158522463,0x5a508514422258c,0x69421215055a442,0x694c552421224c6,0x51400214e552400,0x5b10850c42224e7,0x68c2120d035b042,0x68cc353021230c6,0x50c0020ce353800,0x5a0c668821238ee,0x7a000588c27a021,0x5a0e778800588e2,0x684e180400698e7,0x81800]⟩,
  ⟨27,7,[ew96,ew92,ew97,ew98,ew99],lh 5 [180,23,38,179,30,181,173,2,29,13,182,172,21,22,88,11,0,9,183,1] [0x5b0c65b1ac58cc3,0xd030302c58da3,0x58de30310800c23,0x28c842b8ee2b884,0x54531544425b92e,0x18260350853842,0x2b4840342101908,0x2b4e729884298e7,0x548525492951842,0x4e10208451929,0x441020e700481,0x52104c5304d29,0x2bc4f2be1029c42,0x29e10]⟩,
  ⟨31,10,[ew115,ew116,ew117,ew118,ew119,ew120],lh 6 [6,4,184,189,5,15,188,190,193,176,2,196,29,35,26,23,16,161,13,18,0,27,28,21,191,194,30,197,38,7,22,1,210,14,183,179,164,203,11,25,185,186,187,192,195,198,199,200,201,202,204,205,206,207,208,209,211,212,41,213,214,215] [0x8960963a10a38a1,0xa684670a338e096,0x14519791709716a,0x980001c33c3083,0x2831c3303ad83d8,0xb19299099041203,0x1042c3483203683,0x2c3703b5b49b09b,0x75e19e46e09375d,0x1d3000bc945119e,0x7df08e000c4e3f0,0xca528a2090491c9,0x10920928a0a5041,0x93104cd34922c9,0x30c1cd0002c9514,0x18d335d05005185,0x4d18d68d224041,0x2c51051856b7d8d,0x739e201041a0720,0xefa4101c0041185,0x1042002801cf041,0x1df104f005401cf,0x1012105502cc54c,0x2d0514226566f41]⟩,
  ⟨31,9,[ew96,ew115,ew116,ew117,ew118,ew119,ew120],lh 6 [184,219,189,29,30,38,176,16,27,161,41,224,173,216,22,180,23,2,210,164,13,181,26,182,5,197,18,4,28,217,6,185,15,218,220,221,222,223,187,225,226,227] [0x59600035c0007dc,0x59600038e000,0x2000024900038e,0x610c33dd28a000,0x1c705d0c304128a,0x411c7062104041,0x145041208063104,0x65145041208064,0x30200238e00b30b,0x4106600b38b002,0x402042042041249,0xb41000b28b002,0x1cb002442002282,0x21c200b45100b,0x519019208002502,0x6006002202019,0x24900c00c00c24c,0xc4100060c6006,0x10600640600c0c3,0xc10400c451006,0x514006146006446,0x650601a15a01a,0x28a3490c33d228a,0x5531c73520d23c9,0x1135521c7352112,0x3531535c9209353,0x1043491455d3208,0x3ca1049ca1c73c3,0x2083c36185431c3,0x5c32033de145a1e,0x145a5b61b544145,0x5c460455b]⟩,
  ⟨31,9,[ew100,ew115,ew116,ew117,ew118,ew119,ew120],lh 6 [184,190,176,191,35,228,15,218,23,16,27,5,4,173,30,38,220,161,224,1,179,2,13,7,188,26,185,18,6,221,223,222,189,219,229,230,231] [0x6590410601580c3,0x659000082000,0x1041e1186000082,0x1e2104158186158,0x24904101c15821c,0x41024941030c1dd,0x2cb1de28a1dd30c,0x1de2cb1c728a1df,0x343003082014354,0x3443014082003,0x5c31544511545d4,0x43003041208003,0x30c003543041063,0x3303012552012,0x59a01a2cb012592,0x21820122d201a,0x45114d18614d451,0x4d20d042042002,0x38204220804d00d,0xd38e00d555002,0x5960023c2002555,0x259601b3db01b,0x1c6146208044044,0x1c6246144204046,0x38e404249144384,0x1573cf904284146,0x38e1443c47d7297,0x4838e048249053,0x2930483cf053253,0x4828a0533d3053,0x28c40c2cb1c928a,0x4092cb1cc]⟩,
  ⟨31,9,[ew105,ew115,ew116,ew117,ew118,ew119,ew120],lh 6 [184,193,176,35,220,2,232,194,41,234,38,15,6,5,173,224,29,27,7,161,11,88,23,13,188,203,236,18,190,4,223,237,189,219,233,222,235] [0x6590410601981c7,0x659000082000,0x4921210c3000082,0x1224921980c3198,0x20810430c25c208,0x19815d25c30c104,0x28a11e34d04101d,0x11e28a10434d123,0x387007082015395,0x74c7015082007,0x2c71954d31952d5,0xf30c247587007,0x14524730700f58f,0x4106404f00f041,0x5da01a34d00f5cf,0x22c200f34f01a,0x4d318e2cb18e4d3,0xe596242402002,0x4224259600e410,0x4e00e04e145042,0x5d7002282042145,0x25d701b29b01b,0x20818b410243203,0x4b04b18340310b,0x14b043103183143,0x19228a7c344318b,0x5101832837d2452,0x248514048148250,0x451248288050145,0x10845124c28c10c,0x454054354045445,0x4534d054]⟩,
  ⟨31,9,[ew110,ew115,ew116,ew117,ew118,ew119,ew120],lh 6 [184,196,13,238,197,176,16,35,240,29,173,15,6,4,241,222,41,30,7,9,161,185,26,203,23,0,2,236,188,18,190,218,193,220,5,189,219,239,242,237] [0x28a0410630dc104,0x28a000145000,0x2cb3e4492000145,0x3e52cb0dc4920dc,0x30c3df24921e30c,0x3a034d21e2493df,0x1863e134d3e1186,0x410220dc0a23a0,0x28400414501328a,0x4504013153004,0x1c40d35130d31d3,0x1530c204604004,0x695204304015615,0x1b69b01b34d395,0x1b041082395355,0x52c504106605b,0x5140ca2cb0ca50a,0x16618205245005,0x456205618016256,0x1745701769a396,0x82057057396696,0x5709705d01d05d,0x4100d4249207407,0x38b18b0c72473d4,0x4519c71860c7447,0xd20820470470cb,0x4510c70870523d2,0x2104503d0186209,0x82210650389186,0x5008220c64c04c,0x8d04d659386082,0x4665938d]⟩,
  ⟨31,9,[ew209,ew115,ew116,ew117,ew118,ew119,ew120],lh 6 [188,184,30,29,38,179,161,189,243,244,23,176,245,246,194,26,203,16,4,2,13,6,0,164,27,41,197,18,210,5,190,193,196,219,22,7,218,220,222,247,248,249,1,250,11] [0x1c70411450611c7,0x2cb041145041,0x63000186000022,0x2640c321e555000,0x49221e0c3249555,0x24949226508231f,0x10436059631f082,0x360104249596266,0x470472cb045045,0x71860452c5047,0x47005185005005,0x450c3207287007,0x4c52070c304528a,0x4e4ce04e082305,0x10434e50e305082,0x34e10e05a51a05a,0x2700018600b24b,0x4f28a20b0c3000,0x8f20b28a04f0cf,0x500900504d330f,0x51435011030f4cf,0x35051005b11b05b,0x64600628a01c659,0x1745101c0dc006,0x82006451006086,0x17117006606017,0x82006104017618,0x20a082a19451203,0x61820375d3034c3,0x34350322a104a55,0x104ad2752311104,0x34258232c]⟩,
  ⟨31,9,[ew115,ew116,ew117,ew118,ew210,ew119,ew120],lh 6 [184,190,38,189,4,173,251,179,23,15,88,30,161,252,26,253,35,7,2,5,1,16,27,13,218,220,188,197,183,222,6,193,196,201,176,254,244] [0x14300338e007147,0x3303007387003,0x249187307187247,0x47007043203003,0xa043043047207,0x300300300300a,0x2ca34348300a00a,0x3432c300a49200a,0x5db01b0823ca5ca,0xe2493ca08a01b,0x30c185249185305,0x4500504106100e,0x62185685041208,0x549234e2ce041,0x8534e4920052cb,0x1c09c01c5d73c5,0x20c0500503c55d7,0x19020804c60c18c,0x9091896896118d0,0x351104191691609,0x2cb6501041902cb,0x1910913d04d3191,0x69e1900827514d3,0x5410404005e188,0x554048104048555,0x54594048082054,0x104048596054094,0x65910465955535f,0x5963e008235f555,0x3e059661d082618,0x826444c434b082,0x3cb4d3344]⟩,
  ⟨31,9,[ew115,ew116,ew117,ew118,ew119,ew211,ew120],lh 6 [184,193,173,2,179,38,255,35,5,189,15,220,256,41,194,6,203,258,11,161,23,29,13,7,188,197,10,27,1,190,196,257,259,260,176,261,244,237,4,222] [0x89009410004084,0x94c9004404009,0x28a1844d3184284,0x4544309709009,0xc9309555004704,0x4e0ce04e01f049,0xe004004049049,0x400400e00e00e,0x59901916044e58e,0x1028a44e145019,0x4d01822821824d3,0x2502310550010,0x61310514002542,0x410c3042002041,0x142041062182602,0x1a15a01a596442,0x514307347442582,0x1875072ca34a18a,0x2c71870c704a04a,0x2d78ca18a0c3047,0x6172c7907187607,0x197145447208197,0x48f187145957208,0x30d49204d0cd30f,0x2cd30f74f04f0c3,0x2cf2cf30d74d2cd,0x2082cf6cf30d208,0x18360344d6db30f,0x212043143040066,0x43203052152052,0x1452cb20845e145,0x45e2082e7]⟩,
  ⟨31,9,[ew115,ew116,ew117,ew118,ew119,ew120,ew212],lh 6 [184,196,35,179,262,13,183,189,41,16,161,15,263,4,264,6,23,222,0,18,2,194,197,10,29,30,188,7,190,218,193,220,257,259,265,176,237,266,244,5] [0x1870074d3003183,0x72870034c3007,0x2cb10328a1032c3,0x3603307407007,0x507307618003410,0x15515015660387,0x21055155387659,0x55055056156056,0x16016016003003,0x132cb003003016,0x28a1062c610628a,0x6406313613013,0x646313410006618,0x17657017514386,0x17041062386506,0x117697041145057,0x410302202041063,0x10240244b20810b,0x24910250238b24b,0x4204210b514902,0x14205b45b11b145,0x10a68a442942102,0x34d10268244a98a,0x30834d44824930f,0x14f30848838f24f,0x4814530f49204f,0x70f44f74f308708,0x38914544874830f,0x49238d14d04d492,0x44d7cd389789049,0x6924497c938d78d,0x40067112]⟩,
  ⟨31,9,[ew102,ew115,ew116,ew117,ew118,ew119,ew120],lh 6 [188,176,190,15,179,41,30,27,180,267,173,21,189,268,161,2,13,22,6,4,269,194,16,38,184,220,0,5,218,197,18,164,29,193,196,222,219,244,35,207] [0x30c2582cb22430c,0x2580412082cb258,0x451225041208451,0xa60000c3258,0x4d30000200004a0,0x2194d3208186361,0x69a5221c7361186,0x52269a21c1c7208,0x28a24b451244284,0xc38c24444424b,0xcc00438e0040c4,0x8414408b08b00c,0x3c408b145084704,0x6553d5255186344,0x1c7515415344184,0x5151d58dd41d25d,0xc300a38e0010c1,0x8114100138100a,0x8108a14508a70a,0x64a3cf341181081,0x1c13413c124a18a,0x25e1de8de410501,0x3002145501401,0x3583000027003,0x3c300e59600e3cf,0x1f4100031c3003,0x18600340301f1df,0x85185085596092,0x1d20855c5092592,0x851c50925d7092,0x5d36536db3465d7,0x5066db353]⟩,
  ⟨31,9,[ew107,ew115,ew116,ew117,ew118,ew119,ew120],lh 6 [188,29,193,38,161,179,181,270,176,16,21,35,271,4,189,41,22,220,5,272,26,203,23,194,173,13,27,184,197,18,210,6,190,196,237,219,244,15,30,257,259,260,209] [0x38e1db28a1a338e,0x1db20818628a1db,0x4101a4208186410,0xa50002cb1db,0x3cf1860413203cf,0x34d320041191,0xc34e1492000026,0x4e10c3191492186,0x6181ca4101c5605,0xe10e1c54051ca,0x2ce0051040052c5,0x1c504530a58a00e,0x8530a04a445596,0x97457097267085,0xe84d7657085249,0x4d70c389c65c1dc,0x2cb0181040082c8,0x308048008108018,0x5881d4054454596,0x95469094254308,0xd5094094095255,0x1dd0dd89d6594d5,0x4100b3cb4d5655,0xb0410043c4004,0x2a004004002249,0x1e0c3004684000,0x3410040c301e69e,0x30f34d08f249301,0x69a3010c1081241,0x4c168131f0df45f,0xcd08d48d0890c3,0x8949208d]⟩
]
def nodesBlock8 : Array Node := #[
  ⟨31,9,[ew112,ew115,ew116,ew117,ew118,ew119,ew120],lh 6 [188,29,196,30,22,179,7,182,273,27,274,21,275,23,5,164,2,189,176,6,4,26,203,210,194,41,222,16,184,173,197,18,15,190,193,237,219,244,218,220,38,257,259,265,212] [0x45121c2cb1e4451,0x21c4921c72cb21c,0x1041e54921c7104,0xa00005e021c,0x4d31c70412a14d3,0x3225142a10411e6,0xc31e75141c70c3,0x2800038e322,0x75d20b104205745,0x113d120510520b,0x1860053cf005185,0x20504528b34b011,0x40528b04168534d,0x8d84182180e9305,0x26a0980983050c3,0x9824909e69e09e,0x1840043cf012186,0x2840440123d2004,0x34421505569534d,0x8d64103150d5284,0x2563154152160d6,0x9f25f09f6ab096,0x34d006659096096,0x634600f65900f,0x6d70174100066c6,0x2249006406017,0xc100002c017017,0x2990c36996db281,0x2492813813016c1,0x81241293393093,0x25409438e303243,0x8338e314]⟩,
  ⟨31,9,[ew115,ew116,ew117,ew118,ew119,ew213,ew120],lh 6 [190,5,189,193,7,277,23,2,220,276,38,15,179,22,176,191,203,41,16,279,26,161,13,194,184,222,18,35,188,27,197,173,6,4,196,225,278,199,248,280,281,218] [0x7c224238e24c7cc,0x8c254224c38e242,0x2c214c55514c2cc,0xc44c002182242,0x1c200244200c186,0xd71d70d74970c2,0x60f2029020c2492,0x24260220f20f24f,0x59e25e0414cf58f,0x24e1044cf04f65e,0x55514d10d14d565,0x1419400d44d98e,0x49400d186014454,0xd04900d01d00d4,0x21024d60d0d41c7,0x21a9cd250610210,0x4165a59a4ce041,0x44444ce59625a,0x18600b45114b18b,0x15b1db0c4484144,0xa041441c70db49b,0x20b20b14b70b204,0x28a4cb041144704,0x14b28a644041144,0x1c7006006000000,0x3020146720003,0x4102975d006041,0x14772100675d000,0x410c728a000021,0xc70410c328a0c8,0x28a2080414e228a,0x4e2041219]⟩,
  ⟨31,9,[ew115,ew116,ew117,ew118,ew119,ew120,ew214],lh 6 [190,4,189,15,1,196,283,27,282,18,179,7,218,203,284,220,13,16,194,26,30,35,161,6,2,197,191,184,176,188,22,173,193,5,226,285,199,249,260,286,287,29] [0x7c220224920a7ca,0x88258220a24a202,0x2c218a59618a2ca,0xa5ca002102202,0x6020025c200a104,0x3d2612212041382,0x1d9152412382042,0x1521c7159419159,0x31a21a6da3028d2,0x2092cb2026c231a,0x59619e2de19e5a4,0x1311301c5dc95c,0x5301c1040135d3,0x20d50d3cd626393,0x40914d1cd393618,0x14d4101491c9149,0x6c930930920d6cd,0xb5cb30d9cd209,0x1040035c3183103,0x19551538304318b,0x1c31835033d5041,0x14b1c718b410143,0x743315a15183403,0x195755303303183,0x4100c451004041,0x4451000,0x7440051c7004004,0x3911d1005029184,0x1513811c11413c1,0x3c13c1394814151,0x7613d43d4381801,0x21187]⟩,
  ⟨31,9,[ew115,ew116,ew117,ew118,ew119,ew120,ew215],lh 6 [193,189,220,6,196,289,11,0,288,18,35,290,194,7,179,26,29,4,5,41,203,161,23,15,184,176,188,197,22,173,190,227,291,199,250,201,292,293,16,27] [0x74120124920e74e,0x7c154120e24e201,0x28114e55514e28e,0x20e40e2c1581201,0x1812c140108e596,0xc18c00c451001,0x49210c1cc001441,0x10c48c11b1db11b,0x8c20c60c081801,0x20934d20160108c,0x55515c35c15c561,0x8f5a32d90d9899,0x44f2d959620f0cf,0x1445401419400f,0x1c911449400f186,0x1141c7109489109,0x60908908920f60f,0x2cd0c308f90f209,0x40d0970c3157410,0x14a18a00d45114d,0x49214d18600a451,0x10d49214d1cd10a,0x68a09795714a1c7,0x15769708a08a14a,0x1930130932c3183,0x2d31d30030032d3,0x1132c31c3103083,0x830832d0790113,0x900902c3783,0x41c7006006000,0x687004026146686,0x27147]⟩,
  ⟨31,8,[ew96,ew115,ew116,ew117,ew118,ew119,ew213,ew120],lh 6 [294,189,41,176,16,38,5,224,173,164,161,27,276,18,23,2,210,180,219,197,13,22,296,184,298,299,220,216,217,181,221,301,21,15,218,295,222,297,187,32,29,300,30,302] [0x54034d3008004d3,0x24931554034d315,0x440880082300840,0x680104700700082,0x492780780104740,0x5808c0492680680,0x140186905140186,0x20104d347207945,0xa2800261cd1c1,0x38708704e041001,0x10704f0410811ce,0x4c0411011cf3c7,0x415c11cc1c75c7,0x1814d44d3186054,0x20c2082880cc0c1,0x8838e0c20c328a,0x3cf0c40c3383202,0xd70c33c3204108,0xc3303217208308,0x50334534d5140c5,0x28208a38a402083,0x4103d0244110390,0x6c95919c93c9404,0x28b2916db251249,0x44a14524b2c9149,0x482644102602658,0xa4b2c2145659a02,0xa8448408b2d1145,0x2cb5861842cb618,0x58619f14510619d,0x7c61ab145]⟩,
  ⟨31,8,[ew96,ew115,ew116,ew117,ew118,ew119,ew120,ew214],lh 6 [303,189,176,6,164,27,30,18,16,4,173,282,224,161,1,2,13,197,180,219,22,184,298,301,218,300,210,216,296,217,182,223,299,21,15,220,304,222,305,187,32,29,38] [0x5001c72c0840041,0x1042d45001c72d4,0x4806000c32c0880,0x1802087407400c3,0x1459061802088c6,0x7c07c0145780940,0x9804d36006004d3,0x2810471cc28c640,0x4100027307301,0x38c0cc04e041001,0x24c04f0410c130e,0x5004124130f3cc,0x41141450451145,0x54144b45155104b,0x28b28a10a08b081,0xca38e083082102,0x3cf089082382283,0x850823c228928a,0x824021c51c7410,0x2c21d51c72c7095,0x34334d38e6830c2,0x20d3cd10821a39a,0x4043453443c4348,0x652a0d40d105104,0xd26db1121046c4,0x2084861992080c6,0x5c51435835d6483,0x2461465d7a434c3,0x80619e18914925c,0x19c18980925c246,0x596a854c5]⟩,
  ⟨31,8,[ew96,ew115,ew116,ew117,ew118,ew119,ew120,ew215],lh 6 [306,189,176,4,5,29,164,41,6,173,288,224,18,210,161,23,11,296,0,197,181,219,22,184,299,301,220,216,221,182,223,298,21,15,307,222,308,187,32,30,38] [0x580082280800041,0x186296580082296,0x4451401c7280840,0x6800c38851401c7,0x1047007000c3500,0x7807801047408c0,0x900555680680555,0x24104c30b24b440,0xd3400252cc2c1,0x3cb20b04f041001,0xcb0500412012cf,0x520410c12d040b,0x411014d24d3104,0x5c14ca4d35d304a,0x24a24938908a081,0x2493cf08808238e,0x4100830823c2248,0x840824022430c9,0x8248230430c492,0x28231730c28c097,0x3871ce3ce3471c2,0x34d40d1830cd3cd,0x486384106406343,0x45498e48e184186,0xd46db1941866c6,0x5051c31c7447143,0x204208448144145,0x20844815f145745,0x60365850544521f,0x6599c3543644103,0x618a04544]⟩,
  ⟨31,8,[ew115,ew116,ew216,ew117,ew118,ew119,ew120],lh 6 [228,309,23,179,310,35,176,30,41,38,173,191,2,13,16,27,6,194,26,203,7,188,311,5,197,18,312,313,4,219,189,184,221,220,223,222,314,190,257,259,260,265,15] [0x28a04b186043283,0x10b94b04318304b,0x54b003003003543,0x314300b74b00b,0x8200b145003003,0x308310320311e,0x1e604330311e208,0x431c7051311051,0x358058267051351,0x467c6051249058,0x4604a7ca04a04a,0xa00a006146046,0x20600604600a145,0x11221211208a106,0x3280521d2106082,0x5230c0531d3053,0x259059369053253,0x1514505334d059,0x8201520800076a,0x15082104208000,0x1c76a130c5a01c7,0x6e22495a030c6a1,0x34d92324992334d,0x820052086e2,0x38e005082004208,0x538e0051c5014,0x2540053c50141d4,0x52450143cf014,0x1c210238e1101c7,0x102242110390102,0x3cf1102501103d0,0x69c5d758e3cf102,0x6ce5d759c3dc]⟩,
  ⟨31,8,[ew115,ew116,ew217,ew117,ew118,ew119,ew120],lh 6 [232,315,176,88,15,16,316,38,29,173,2,317,194,23,191,13,41,27,7,4,188,220,197,18,318,6,5,219,184,190,223,222,172,193,259,35] [0x24904c082043243,0x18c84c04308304c,0x50c003003003503,0x310300c6cc00c,0x34300c104003003,0x4e34e04e2082c3,0x14318e28e2c3203,0x18e145003283183,0x3d60561e204e3ce,0x4270204e1c7056,0x42049709049049,0x9009002104042,0x202002042009104,0x4920804934d2c2,0x2891821422c2342,0x18228a189145189,0x1d70573cf0421c2,0x141040423c2057,0x34d2dd2080006e3,0x2dd34d555208555,0x14500028a014145,0x61e1c701428a186,0x3cf81f1c781f3cf,0x420801241061e,0x144012212004404,0x614500028a004,0x1d2004444004284,0x41c4012451012,0x4d31901452c84c8,0x2d01d01881452d0,0x4512d91d9559451,0x1936931851c7610,0x18569a1931c7]⟩,
  ⟨31,8,[ew115,ew116,ew218,ew117,ew118,ew119,ew120],lh 6 [238,224,29,319,9,176,13,173,320,15,30,27,23,2,35,321,322,16,41,5,188,18,222,6,4,197,219,184,190,218,193,220,323,196,21,265,161] [0x1c70d91450c11c7,0x2018410c11410d9,0x501004004004522,0x4244001681001,0x304001241004004,0xc130c0c10813c4,0x2814043443c4082,0x4042840c134d0c1,0x1842042c4201181,0xc56c52012cb004,0xc50c76c70c70c7,0x70070052490c5,0x820050c5007249,0xc70820c730c3c5,0x34d4052853c530c,0x40534d0c728a0c7,0x2d52151a32052cb,0x14249205186215,0x30c3dc0820006a4,0x3dc30c59d08259d,0x28a81f34d41e28a,0x142cb41e34d81f,0x1862082cb000186,0x908900e48e014,0x44900e08e009492,0xe45100e28e009,0x18600e2ce009289,0xe18e0082cb000,0x2925924513c228a,0x3c24c24024423d2,0x1823d74d7217186,0x2184d3411191202,0x2114d3418198]⟩,
  ⟨31,8,[ew209,ew115,ew116,ew117,ew118,ew119,ew213,ew120],lh 6 [189,23,179,5,38,2,277,41,16,164,243,161,194,203,27,324,176,276,18,26,245,210,13,188,244,326,184,190,193,220,197,279,246,294,22,15,218,325,222,247,32,29,327,30,328] [0x8f0004420a1000,0x249186886492442,0x28f91b1c718f8c6,0x75c2086ca6ca1c7,0x61871471420850f,0x64f94f61874f74f,0x10f0c398411f0c3,0x4400124824427c4,0x860802c0092080,0x800400110022c2,0x140007002041087,0x800c14c308200,0xc44c31a300440,0x59e7830cc58c01a,0x18b2d03d030331e,0x4d30414074061a7,0x1454c84d00504c7,0x41a41315334834d,0x35045035a34d44d,0x58d484492596344,0x2c71cb04b5471cd,0x555155248215041,0x5c9646a09145548,0x2ce2c65d7246249,0x28b10b24e389109,0x5c150514128128a,0xa8e38110150aa41,0xac55c504e38a104,0x38e6430c538e28a,0x6430e01041430d4,0x8030ec104]⟩,
  ⟨31,8,[ew209,ew115,ew116,ew117,ew118,ew119,ew120,ew214],lh 6 [189,1,179,164,13,30,283,161,4,6,243,27,194,203,16,329,18,282,2,176,197,26,246,188,244,184,190,218,196,327,326,284,210,245,303,22,15,220,222,330,247,32,29,38] [0x8f0004420a2000,0x1c71868c64d3442,0x28f6da24918f906,0x15f49268a68a249,0x2cb7c514f492945,0x7167162cb58f99c,0x9cf6186cf6cf618,0x44001040244274f,0x860800c0090080,0x800400110020c2,0x480009002041089,0x800c48c308200,0x31411450b2cc10c,0x45451950c44c30b,0x1830d33d3319314,0x5550414c94c61a8,0x492548553053549,0x34b35549534534d,0x34d10d40b410104,0x44d419410450359,0x1c91c704780924d,0x3871470ce3a0041,0x1031cb1c31431ce,0x746a471040cb0c3,0x465d70c60c35c3,0x38e28515d38e045,0x58410128128a281,0x20e10458aa815c1,0x84539638810821e,0x15e14884821e205,0x28aac45c4]⟩,
  ⟨31,8,[ew209,ew115,ew116,ew117,ew118,ew119,ew120,ew215],lh 6 [189,11,179,29,0,41,289,4,5,245,6,26,331,18,161,288,210,176,164,326,194,197,203,246,23,188,244,184,193,220,196,290,243,306,22,15,222,332,247,32,30,38] [0x8c0003c20a1000,0x4921868864513c2,0x4c30df14518c8c6,0x75c1c77c30cc145,0x2087097091c724c,0x7977972085cc91e,0x94c69a74c74c69a,0x3c000d3423c24cc,0x8608040008d080,0x8060000f002402,0x4000a00261808a,0x70140545071c0,0x515115548214114,0x3d555b5403c0508,0x18e39131101b015,0x2cb61844a4461a6,0x412c72d16112c3,0x58858b04b587596,0x2d611634834d104,0x3cb35b34d3cd2db,0x38514e0c340514b,0x4100504871d00d0,0x112388212041407,0x4c69ce104488492,0x4665938638e64e,0x2431410454c50c1,0x28428a4ca144103,0x28a4ca0e00c55c5,0x2412492434c32a0,0x5c9a016415c4101,0x249a44644]⟩,
  ⟨31,8,[ew115,ew116,ew219,ew117,ew118,ew119,ew120],lh 6 [251,176,23,334,333,35,30,41,183,38,197,2,21,13,336,27,191,194,337,203,16,6,7,188,5,18,338,4,88,219,184,244,15,193,220,196,222,339,335,190] [0x20810a04111c208,0x10a74a11c04110a,0x78a10c74c10c78c,0xc14c00a10a10a,0x8c00a14500c00c,0xd00900d01e60cc,0x1863902d00cc1c7,0x3901901112d1111,0x34a10a249491351,0x15c149125110a,0x9c10085c8008008,0x80080011410c1,0x1c10017c1008145,0xc81c70080820c1,0x2cb3811810c1081,0x3812c1113193113,0x25911934d493253,0x17160493353119,0x820171c70007e0,0x170820c31c7000,0x1866a22cb3a1186,0x4a32493a12cb6a2,0x34d96424996434d,0x820051c74a3,0x5140050820031c7,0x55140052cb016,0x2560053c50162d6,0x52450163cf016,0x1820c25140d5186,0xc22420d55150c2,0x3cf0d52550d53d5,0x69b6183863c60c2,0x48661839b3db]⟩,
  ⟨31,8,[ew115,ew116,ew220,ew117,ew118,ew119,ew120],lh 6 [255,173,340,176,342,16,38,15,23,41,2,13,179,189,341,29,7,21,343,27,194,4,197,188,220,10,18,6,5,219,184,244,190,196,222,237,257,259,193,35] [0x6590960c308c659,0x8c74c08c0cc096,0x78c091751091791,0x111d100d08d08c,0x20d00d1cd011011,0x8c20c08c24c38d,0x16410d28d38d24d,0x10d145114294114,0x2d60961a54942d4,0x35c3494186096,0x9830015c1001001,0x10010031c3103,0x3c30037c30011c7,0x813cf081201383,0x281103143383208,0x10328a101141001,0x19a09a2cb481181,0x171c74812c109a,0x2083a03cf0007e7,0x3a02086183cf618,0x14500028a017145,0x4a118601728a104,0x2cb8e21868e22cb,0x72080102494a1,0x150010210007249,0x414500028a010,0x2d00074c7010290,0x72cb0104d3010,0x55510914938f54f,0x38918910f145389,0x4d339b19b61b4d3,0x115715105186489,0x10571c115186]⟩,
  ⟨31,8,[ew115,ew116,ew221,ew117,ew118,ew119,ew120],lh 6 [262,13,183,344,21,176,347,35,23,2,16,27,189,41,345,15,346,29,30,203,179,194,5,188,10,197,222,6,4,219,184,244,190,218,193,220,348,259,196,161] [0x60c0cc1450d4618,0xcc74c0d41540cc,0x78c0c47440c4784,0x41c400c0cc0cc,0x20400c1cc004004,0xd42080d4354384,0x28a404244384344,0x4042840d52550d5,0x591992e5195055,0x55c51952cb199,0x9850025c2002002,0x20020053c5185,0x4450057c50023cf,0xc24510c2202385,0x249402482385205,0x4022420d34930d3,0x2c20020421932d3,0x173cf193053182,0x2083a04510007e7,0x3a02086a14516a1,0x492923249422492,0x172cb422249923,0x411862cb000041,0xf208007347017,0x28f00720700f34d,0x728a00724700f,0x410072c700f249,0x70410062cb000,0x48d68d28a391492,0x38d58d41128a38d,0x4139b59b19b041,0x19c59640a04118d,0x18a59641c05c]⟩
]
def nodesBlock9 : Array Node := #[
  ⟨31,8,[ew222,ew115,ew116,ew117,ew118,ew119,ew120],lh 6 [351,276,41,15,9,26,2,352,27,349,23,161,16,38,189,203,35,1,353,11,13,22,176,190,188,354,173,18,7,5,194,184,219,196,222,220,350,172,193,335,199] [0x5960418de25839e,0x4159604114505f,0xc39202cb05f145,0x9600c32582cb258,0x28a00008201728a,0x186017082000,0x30c01718601730c,0x6622084a134d1e6,0x69a4a120866234d,0x4e68e04e145044,0xc404e2cb044144,0x4e0c32442c4244,0x28a0000a7004284,0x4184004082000,0x3041c71861c730c,0x4420448e50e1c4,0xc348e20e044514,0x2550d52552e8045,0x2850150950452cb,0x1528a005085005,0x30f1cf18f1c5305,0x48f34f1c51861cf,0x50f05b35b05b514,0x24b28a01009048f,0x30c25029000b082,0x1d03102501901c3,0x34d483203243183,0x24334365c21c25c,0x4d30021820114d1,0x2342011191002,0x208011351011211,0x1d37531c6208002,0x1c675d1d3213]⟩,
  ⟨31,8,[ew223,ew115,ew116,ew117,ew118,ew119,ew120],lh 6 [356,276,15,22,23,2,357,27,189,179,355,41,16,38,161,1,197,358,194,35,11,13,190,188,359,176,18,7,5,184,203,244,172,196,222,220,193] [0x41005d249041410,0x2970de04124905d,0x8281f38e0418de,0x81f08229738e297,0x1040002cb016104,0x1450162cb000,0x30c01614501630c,0x6221c746134d1a4,0x494611c762234d,0x480480480c3049,0x820483880490c9,0x4808828938e289,0x1090092c9008108,0x1881480082c8009,0x30819215219230c,0x501c7452552188,0x824521d2050550,0x28308328338e059,0x1040032c3059399,0x31040002cb000,0x30c186145183303,0x4431c3003145186,0x54305a35a05a555,0x2821040132cb443,0x3022931130022c2,0x193313293153182,0x34d4421c2282142,0x28234261b1db29b,0x51400414500f50f,0x434d00f14f004,0x1c700f34f00f1cf,0x1947141851c7004,0x18571c1941d4]⟩,
  ⟨31,8,[ew115,ew116,ew224,ew117,ew118,ew119,ew120],lh 6 [277,361,189,7,176,23,2,179,38,173,362,41,16,13,360,363,203,27,6,32,194,4,188,184,364,197,18,5,219,244,15,196,222,259,220,190] [0x242382104387247,0x4c2702387107382,0x5c24c77073875c7,0x70c70024c2382,0x1420020c3007007,0x471470472c7042,0x30c2821820422c2,0x282302294194294,0x3593992213d4354,0x3845c43d4208619,0x7443895c94c9749,0x90090040c44c4,0x2c40044c40090c3,0x492cb049149044,0x189284304044145,0x284186290310290,0x21a61a34d3d0210,0x160de3d035039a,0x1450162cb00089e,0x161450412cb000,0x30c00018601630c,0x3df208016186063,0x34d62020862034d,0x1450032c33df,0x3030031430012cb,0xa30c000186003,0x34300f451003183,0x34d003451003,0x555005186052552,0x45205052192045,0x451052208052452,0x2956d5286208045,0x2866db295208]⟩,
  ⟨31,8,[ew225,ew115,ew116,ew117,ew118,ew119,ew120],lh 6 [367,282,6,15,173,23,16,27,161,370,88,365,13,2,176,26,368,189,0,194,35,30,1,190,188,369,18,7,4,197,184,219,193,220,218,366,172,196] [0x10404189d2d84dd,0x411040413cf05e,0xc38df20805e3cf,0x91f0c32d82082d8,0x596000082017596,0x42034d017082000,0x18666134d661186,0x171c700030c420,0x10a2651c701730c,0x531040533cf04a,0xca05321304a3ca,0x530c32ca2082ca,0x14500008200a14a,0x41135100a08a000,0x19104a34d04a18a,0x2491c7011311411,0xc32511d124930c,0x2c40c42c420804f,0x14500e08204f208,0xe14e004084004,0x18404434d40e18e,0x24e1ce40e34e044,0x30e25a1da25a30c,0x2c814501408224e,0x1832d4154008088,0x6541862d4354403,0x30c2431c32c3343,0x2c330325b1db2db,0x545005186002542,0x5485002186005,0x1c50024920021c2,0x25c4924151d5005,0x25549241c1dc]⟩,
  ⟨31,8,[ew226,ew115,ew116,ew117,ew118,ew119,ew120],lh 6 [372,282,13,6,23,16,15,179,35,375,189,371,30,27,22,373,203,161,0,176,194,2,190,188,374,197,7,4,184,18,244,172,1,29,193,220,218,196,259] [0x28a05c1c704128a,0x2d741d0411c705c,0x1867de20804191d,0x7de1862d72082d7,0x1210000c3016820,0x3e230c0160e1000,0x14562330c623145,0x1634d0000823e2,0x4726534d016082,0x4a04a04a4ca047,0x18604a44a0474d3,0x4a1862c74512c7,0x1040070c300a104,0x3c754700a0c3007,0x145054554054145,0x2593662540943c7,0x19325434d259099,0x2ce18e2ce451053,0x10400e0ce053451,0xe1040000c3000,0x3100505553ce30e,0x2503503ce54e050,0x9024934d249082,0x2c61040080c3010,0x1462c81080060c3,0x6081452c83083c6,0x822483482c630c,0x2c808825a35a2da,0x30c00414500330c,0x4484003145004,0x82003492003082,0x25b4923c5082004,0x2454923db09b]⟩,
  ⟨31,8,[ew115,ew116,ew227,ew117,ew118,ew119,ew120],lh 6 [283,41,377,27,189,1,179,176,35,30,173,13,380,16,376,2,378,194,5,32,4,188,184,379,197,18,203,219,244,193,220,15,218,190] [0x28438469a386286,0x4c46c43861c6384,0x5844c66c6386586,0x62060044c4384,0x144004208006006,0x86146086046084,0x5144043c4084041,0x4045045d13d1391,0x2d83180c33112d1,0x3875873110d1318,0x70738a58a4ca70a,0xa00a0072084c7,0x410074c700a208,0x8a04108a14a087,0x3cf407247087145,0x4073cf38a2495ca,0xd93192cb3070c7,0x152083072cb319,0x14501504100081f,0x15145082041000,0x2495de3cf41d249,0x150c341d3cf5de,0x2cb0a10c30002cb,0x145008041015,0x34d008145002041,0x834d008249010,0x2cb0080c3000249,0x82cb00c0c3000,0x24908134d085249,0x8148108534d081,0xc30854920050c3,0x31449240d0cd081,0x30d4924140d4]⟩,
  ⟨31,8,[ew228,ew115,ew116,ew117,ew118,ew119,ew120],lh 6 [383,4,189,288,5,173,35,41,13,161,23,384,381,2,203,382,179,15,176,29,220,11,193,0,188,18,7,6,197,184,219,172,190,196] [0x1450c351c31809c,0xc31450c338e0dd,0x1867de2490dd38e,0x7de186318249318,0x28a5141c73e028a,0x165553e01c7514,0x41000555000041,0x161040005d7016,0x1502e11040165d7,0xc21420c238e0d0,0x1900c22420d0390,0xc2182310249310,0x28a0d01d03c2282,0x23423c21c20d0,0x4200034d000041,0x2cb104002202002,0x1862c21022cb208,0x3051853052490ce,0x28a3ce1c70ce249,0x3ce28a0c51c50c5,0x4500534d012041,0x2d2112012352005,0x2122d91192d9208,0x30928a3c61c72d2,0x513062865091c9,0x6041306346011,0x2082d1111311351,0x3112112da11a31a,0x410073473d3041,0x3d31130133533c7,0x2133db11b2db208,0x110100d2082d3,0xd104001201]⟩,
  ⟨31,8,[ew229,ew115,ew116,ew117,ew118,ew119,ew120],lh 6 [387,288,35,5,4,88,13,41,29,388,385,2,26,15,189,386,191,23,161,22,220,176,11,193,0,6,188,197,7,184,18,244,172,190,196,259] [0x38e05d14504138e,0x29a31e04114505d,0x8281f34d04151e,0x81f08229a34d29a,0x2085141c73e1451,0x175963e11c7514,0x104000596000104,0x170c3000618017,0x452620c3017618,0x4e04e04e54e045,0x8204e48e045555,0x4e082285492285,0x4500502083c5445,0x102d03c5208050,0x1040052cb005105,0x25b0e3250190010,0x3552500c325b19b,0x293353293492055,0x4513d3213055492,0x3d345304c20c04c,0x1040002cb00c10c,0x24c0cc00c2cc000,0x18c2490c3249186,0x28d2083c21c200c,0x10d28220250d1c7,0x21022822c200d,0x1862420c228d2cd,0x28218225c0dc29c,0x1070072c73c8108,0x3c70c70082cb3c7,0x1863d90d9259199,0x40c300b186247,0xb0c3004186]⟩,
  ⟨31,8,[ew115,ew116,ew230,ew117,ew118,ew119,ew120],lh 5 [289,176,88,11,16,391,0,15,173,27,189,29,41,23,390,392,389,220,179,32,6,188,184,5,197,18,219,244,190,35,193] [0x8290a8282184912,0x80ac29ab4a84821,0x2a6a82aca98b42,0x28ea00802008e2,0x8c9ad84a92709a2,0x288822a86a70a82,0x788c22a88428862,0x78ae27e0d87e2f7,0x822c89a368806c1,0x2008004e198761,0x7056100661020e8,0x705ad8216b8a1ad,0x2a0842a06828484,0x7e4c67852128461,0x54e7784c17e539,0x8c5ad7716b0023d,0x5484771ad8c56b,0x54632948400063,0x2f929000c605529,0x1d670398c054c6,0x1c870016b01d8c,0x1c630148400063,0x3d29000c601d27,0x2b08c72c6301cc7,0x730cc2ac8b7306c,0x7b12c750d47d129,0x28d2300cc329129,0x290c6]⟩,
  ⟨31,7,[ew231,ew115,ew116,ew117,ew118,ew119,ew120],lh 6 [7,161,29,30,38,27,176,224,16,41,189,173,21,26,191,184,23,2,393,13,22,219,5,164,197,18,15,294,223,222,216,221,217,300,394,296,395] [0x38f30c3ce39230c,0x51448d34f51448e,0x79768f01a3cd352,0x2550823d75d2000,0xc354925f0826c9,0x5482200c36c8215,0x15d10474515c104,0x2cb38d3472c7705,0x3000070471cd1ce,0x1ca40c1c01cc041,0x44a2822874101c2,0x2832874511c31ca,0x2984d860410a4ca,0xb2c1046000284,0x2d040608618118b,0x4460c619018b082,0x10619118b0c32d1,0x1931991196534c6,0x81241042080240,0x208043040200002,0x41011410030c1,0x2020c3044040145,0x1090882090c9248,0x245162104845149,0x5a41458d6588145,0x216]⟩,
  ⟨31,7,[ew232,ew115,ew116,ew117,ew118,ew119,ew120],lh 6 [88,27,29,30,161,16,176,191,6,35,38,173,26,184,1,2,164,396,13,21,22,219,4,197,18,15,303,221,220,216,223,217,300,397,398,399] [0x1cd4d33471d14d3,0x51444c30d514447,0x74464d25934c311,0x215082344111249,0xc354821e082688,0x6c515c0c370515b,0x5f28a68105528a,0x2cb1cc3002c0541,0x900710400c007,0x803801c9240100,0x3c700200738e1c2,0x1c30c03cf003007,0x174975c1040480,0x24b2c42c6249001,0x2ce38608618418b,0x3c60c618e18b082,0x4618f18b0c32cf,0x192198298612486,0x84208102089209,0x1451030d0145242,0x40a404044403404,0x1480c810a290041,0x28a2051610c3805,0x81048288201042,0x1560565a2585041,0x163]⟩,
  ⟨31,7,[ew233,ew115,ew116,ew117,ew118,ew119,ew120],lh 6 [15,4,5,194,29,41,176,161,30,38,179,173,210,203,189,184,23,400,11,0,21,22,296,219,6,197,18,217,306,35,216,223,221,401,402] [0xcf5143c30d1514,0x55544d34f555443,0x78774f0003cd351,0x15b1043c71d1000,0x2086c5156104585,0x5c105f208701057,0xa0249702097249,0x2cb0cd34a2ca5c2,0x2802831c728d283,0x28e4030c000a1ca,0x48e38438a410284,0x3813834830c104e,0xd94d96420834c3,0x2c72c60000c2,0x2d04061061871cb,0x48620619018b104,0x24619218b2082d2,0x19319a25a6934c6,0x3071451c410c145,0x41308300040304,0x30930008000800c,0x14404100900c082,0x82121105041156,0x162158098616605,0x81241042088249,0x202]⟩,
  ⟨31,7,[ew115,ew116,ew234,ew117,ew118,ew119,ew120],lh 6 [7,161,30,191,23,29,22,38,179,2,13,26,27,41,203,189,194,16,393,176,188,190,404,5,184,197,403,18,164,196,222,259,199,265,193,327,326,405] [0x18f48f3c6188488,0x4830d80c8488206,0x200203703218203,0xcf10f0c0008708,0x2433cd3431040cd,0xc20d0250402083,0x1d92996477d0290,0x60b2d42d3693407,0x18180b00b4d44cb,0x2c61462c1046006,0x8618410b1452c4,0x18924e08e389386,0x29b1db6ca84e1ce,0x50105a00038a,0x584115145681054,0x256082544116145,0x1c7889255082549,0x74a29e1c778a29d,0x101341044100340,0x451049040440004,0xa001301009001,0x44508204a04030c,0x1c515114d08d351,0x14c1561c78cc305,0x5e530c9175c2302,0x97]⟩,
  ⟨31,7,[ew115,ew116,ew235,ew117,ew118,ew119,ew120],lh 6 [22,38,30,35,16,191,6,29,179,27,161,26,189,203,164,194,1,2,13,396,197,188,190,407,4,184,406,18,15,193,220,196,327,408,409] [0xc4cc3000084c8,0x4c51591484c8200,0x203205285219205,0x14c40c1430c8288,0x445306305410146,0x14214f44f3c2085,0x5449450150f48f,0x64b2d52c06803c1,0xa00b0cb01500b,0x2c01c02ca2800c0,0x8001000b1c72d0,0x1100d08d351440,0x35b05b6d248d04d,0xc354a71a0dc352,0x5c61961c768a295,0x11d0825861971c7,0x4174411e082784,0x7c9256041589257,0xca1862871c3186,0x1040c208e1040c7,0x381383249382383,0x1060820c104e24e,0x41184117082804,0x1c9246041189247,0x118058621604041,0x122]⟩,
  ⟨31,7,[ew115,ew116,ew236,ew117,ew118,ew119,ew120],lh 5 [15,194,203,41,179,30,38,26,22,161,23,29,4,11,0,210,5,400,197,188,326,193,411,6,189,184,410,18,190,196,412] [0x221188e30841224,0x264818843909224,0x80244a48000521,0x8c245288318541,0x214a16b425091a4,0x98d274a46905c1,0x44d02c885312348,0x124480010948802,0x1284719cea50862,0x3b4e22884d11ca7,0x3b8fb36f6e71cc7,0xd2533002694e800,0xe29545ae8a5716b,0xab5b6296cd6d4a5,0xeb9d531aae758c6,0x7ade018c0b5bc63,0x140f631e578180,0x180f841e678200,0x5d963630741ad8c,0x1f87785ef4b8e10,0x2c0ac33190814c6]⟩
]
def nodesGet (i : Nat) : Option Node :=
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
def fastViews : QFast.Table View := ⟨32,viewsGet⟩
def fastNodes : QFast.Table Node := ⟨159,nodesGet⟩
end SignedProjection

namespace SignedProjection
end SignedProjection

namespace SignedProjection
def aliasMap0 : Array Nat := #[0,0,0,0,0,0,1,0,0,0,0,0,0,0,9,0,0,0,0,0,0,0,17,0,0,0,0,0,0,0,25,0,0,0,0,0,0,0,33,0,0,0,0,0,0,0,41,0,0,0,0,0,0,0,49,0,0,0,0,0,0,0,57,0]
def aliasMap1 : Array Nat := #[0,0,0,0,0,0,1,0,0,0,0,0,0,0,5,0,0,0,0,0,0,0,17,0,0,0,0,0,0,0,21,0,0,0,0,0,0,0,33,0,0,0,0,0,0,0,37,0,0,0,0,0,0,0,49,0,0,0,0,0,0,0,53,0]
def aliasMap2 : Array Nat := #[0,0,0,0,0,0,1,0,0,0,0,0,0,0,5,0,0,0,0,0,0,0,9,0,0,0,0,0,0,0,13,0,0,0,0,0,0,0,33,0,0,0,0,0,0,0,37,0,0,0,0,0,0,0,41,0,0,0,0,0,0,0,45,0]
def aliasMap3 : Array Nat := #[0,0,0,0,0,0,1,0,0,0,0,0,0,0,5,0,0,0,0,0,0,0,9,0,0,0,0,0,0,0,13,0,0,0,0,0,0,0,17,0,0,0,0,0,0,0,21,0,0,0,0,0,0,0,25,0,0,0,0,0,0,0,29,0]
def aliasMap4 : Array Nat := #[0,0,0,0,4,5,6,7,0,0,0,0,0,0,0,0,0,0,0,0,12,13,14,15,0,0,0,0,0,0,0,0,0,0,0,0,36,37,38,39,0,0,0,0,0,0,0,0,0,0,0,0,44,45,46,47,0,0,0,0,0,0,0,0]
def aliasMap5 : Array Nat := #[0,0,0,0,4,5,6,7,0,0,0,0,0,0,0,0,0,0,0,0,12,13,14,15,0,0,0,0,0,0,0,0,0,0,0,0,20,21,22,23,0,0,0,0,0,0,0,0,0,0,0,0,28,29,30,31,0,0,0,0,0,0,0,0]
def aliasMap6 : Array Nat := #[0,0,0,0,16,17,18,19,0,0,0,0,0,0,0,0,0,0,0,0,20,21,22,23,0,0,0,0,0,0,0,0,0,0,0,0,48,49,50,51,0,0,0,0,0,0,0,0,0,0,0,0,52,53,54,55,0,0,0,0,0,0,0,0]
def aliasMap7 : Array Nat := #[0,0,0,0,32,33,34,35,0,0,0,0,0,0,0,0,0,0,0,0,36,37,38,39,0,0,0,0,0,0,0,0,0,0,0,0,48,49,50,51,0,0,0,0,0,0,0,0,0,0,0,0,52,53,54,55,0,0,0,0,0,0,0,0]
def aliasMap8 : Array Nat := #[0,0,0,0,8,9,10,11,0,0,0,0,0,0,0,0,0,0,0,0,12,13,14,15,0,0,0,0,0,0,0,0,0,0,0,0,40,41,42,43,0,0,0,0,0,0,0,0,0,0,0,0,44,45,46,47,0,0,0,0,0,0,0,0]
def aliasMap9 : Array Nat := #[0,0,0,0,8,9,10,11,0,0,0,0,0,0,0,0,0,0,0,0,12,13,14,15,0,0,0,0,0,0,0,0,0,0,0,0,24,25,26,27,0,0,0,0,0,0,0,0,0,0,0,0,28,29,30,31,0,0,0,0,0,0,0,0]
def aliasMap10 : Array Nat := #[0,0,0,0,16,17,18,19,0,0,0,0,0,0,0,0,0,0,0,0,20,21,22,23,0,0,0,0,0,0,0,0,0,0,0,0,24,25,26,27,0,0,0,0,0,0,0,0,0,0,0,0,28,29,30,31,0,0,0,0,0,0,0,0]
def aliasMap11 : Array Nat := #[0,6,0,0,0,5,0,0,0,14,0,0,0,13,0,0,0,22,0,0,0,21,0,0,0,30,0,0,0,29,0,0,0,38,0,0,0,37,0,0,0,46,0,0,0,45,0,0,0,54,0,0,0,53,0,0,0,62,0,0,0,61,0,0]
def aliasMap12 : Array Nat := #[0,53,0,0,0,54,0,0,0,49,0,0,0,50,0,0,0,37,0,0,0,38,0,0,0,33,0,0,0,34,0,0,0,21,0,0,0,22,0,0,0,17,0,0,0,18,0,0,0,5,0,0,0,6,0,0,0,1,0,0,0,2,0,0]
def aliasMap13 : Array Nat := #[0,45,0,0,0,46,0,0,0,41,0,0,0,42,0,0,0,37,0,0,0,38,0,0,0,33,0,0,0,34,0,0,0,13,0,0,0,14,0,0,0,9,0,0,0,10,0,0,0,5,0,0,0,6,0,0,0,1,0,0,0,2,0,0]
def aliasMap14 : Array Nat := #[0,29,0,0,0,30,0,0,0,25,0,0,0,26,0,0,0,21,0,0,0,22,0,0,0,17,0,0,0,18,0,0,0,13,0,0,0,14,0,0,0,9,0,0,0,10,0,0,0,5,0,0,0,6,0,0,0,1,0,0,0,2,0,0]
def aliasMap15 : Array Nat := #[0,0,0,0,0,0,0,0,0,54,51,0,0,52,49,0,0,0,0,0,0,0,0,0,0,38,35,0,0,36,33,0,0,0,0,0,0,0,0,0,0,22,19,0,0,20,17,0,0,0,0,0,0,0,0,0,0,6,3,0,0,4,1,0]
def aliasMap16 : Array Nat := #[0,0,0,0,0,0,0,0,0,9,12,0,0,11,14,0,0,0,0,0,0,0,0,0,0,25,28,0,0,27,30,0,0,0,0,0,0,0,0,0,0,41,44,0,0,43,46,0,0,0,0,0,0,0,0,0,0,57,60,0,0,59,62,0]
def aliasMap17 : Array Nat := #[0,0,0,0,0,0,0,0,0,46,43,0,0,44,41,0,0,0,0,0,0,0,0,0,0,38,35,0,0,36,33,0,0,0,0,0,0,0,0,0,0,14,11,0,0,12,9,0,0,0,0,0,0,0,0,0,0,6,3,0,0,4,1,0]
def aliasMap18 : Array Nat := #[0,0,0,0,0,0,0,0,0,17,20,0,0,19,22,0,0,0,0,0,0,0,0,0,0,25,28,0,0,27,30,0,0,0,0,0,0,0,0,0,0,49,52,0,0,51,54,0,0,0,0,0,0,0,0,0,0,57,60,0,0,59,62,0]
def aliasMap19 : Array Nat := #[0,0,0,0,0,0,0,0,0,46,39,0,0,44,37,0,0,0,0,0,0,0,0,0,0,42,35,0,0,40,33,0,0,0,0,0,0,0,0,0,0,14,7,0,0,12,5,0,0,0,0,0,0,0,0,0,0,10,3,0,0,8,1,0]
def aliasMap20 : Array Nat := #[0,0,0,0,0,0,0,0,0,30,23,0,0,28,21,0,0,0,0,0,0,0,0,0,0,26,19,0,0,24,17,0,0,0,0,0,0,0,0,0,0,14,7,0,0,12,5,0,0,0,0,0,0,0,0,0,0,10,3,0,0,8,1,0]
def aliasMap21 : Array Nat := #[0,1,0,7,0,0,6,0,0,9,0,15,8,0,14,0,0,17,0,23,16,0,22,0,0,25,0,31,24,0,30,0,0,33,0,39,32,0,38,0,0,41,0,47,40,0,46,0,0,49,0,55,48,0,54,0,0,57,0,63,56,0,62,0]
def aliasMap22 : Array Nat := #[0,0,0,0,55,54,53,52,0,0,0,0,51,50,49,48,0,0,0,0,39,38,37,36,0,0,0,0,35,34,33,32,0,0,0,0,23,22,21,20,0,0,0,0,19,18,17,16,0,0,0,0,7,6,5,4,0,0,0,0,3,2,1,0]
def aliasMap23 : Array Nat := #[0,0,0,0,47,46,45,44,0,0,0,0,43,42,41,40,0,0,0,0,39,38,37,36,0,0,0,0,35,34,33,32,0,0,0,0,15,14,13,12,0,0,0,0,11,10,9,8,0,0,0,0,7,6,5,4,0,0,0,0,3,2,1,0]
def aliasMap24 : Array Nat := #[0,0,0,0,31,30,29,28,0,0,0,0,27,26,25,24,0,0,0,0,23,22,21,20,0,0,0,0,19,18,17,16,0,0,0,0,15,14,13,12,0,0,0,0,11,10,9,8,0,0,0,0,7,6,5,4,0,0,0,0,3,2,1,0]
def rootAliases : QFast.AliasTable
  | 1 => some (0, aliasMap0)
  | 2 => some (0, aliasMap1)
  | 3 => some (0, aliasMap2)
  | 4 => some (0, aliasMap3)
  | 7 => some (6, aliasMap4)
  | 8 => some (6, aliasMap5)
  | 9 => some (6, aliasMap6)
  | 10 => some (6, aliasMap7)
  | 11 => some (6, aliasMap8)
  | 12 => some (6, aliasMap9)
  | 13 => some (6, aliasMap10)
  | 14 => some (5, aliasMap11)
  | 15 => some (5, aliasMap12)
  | 17 => some (5, aliasMap13)
  | 18 => some (5, aliasMap14)
  | 19 => some (16, aliasMap15)
  | 20 => some (16, aliasMap16)
  | 21 => some (16, aliasMap17)
  | 22 => some (16, aliasMap18)
  | 23 => some (16, aliasMap19)
  | 24 => some (16, aliasMap20)
  | 26 => some (25, aliasMap21)
  | 28 => some (27, aliasMap22)
  | 29 => some (27, aliasMap23)
  | 30 => some (27, aliasMap24)
  | _ => none
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockRoots_0 : QFast.passBlock (QFast.symCheckRoot rootAliases fastViews fastNodes) 0 26 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockRoots_26 : QFast.passBlock (QFast.symCheckRoot rootAliases fastViews fastNodes) 26 6 = true := by decide +kernel
theorem joinRoots_0_0 : QFast.passBlock (QFast.symCheckRoot rootAliases fastViews fastNodes) 0 32 = true :=
  @QFast.merge_blocks (QFast.symCheckRoot rootAliases fastViews fastNodes) 0 26 6 blockRoots_0 blockRoots_26
theorem certifiedRoots : QFast.passBlock (QFast.symCheckRoot rootAliases fastViews fastNodes) 0 32 = true := joinRoots_0_0
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockNodes_0 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 0 54 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockNodes_54 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 54 64 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockNodes_118 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 118 7 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockNodes_125 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 125 7 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockNodes_132 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 132 7 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockNodes_139 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 139 7 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockNodes_146 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 146 7 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockNodes_153 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 153 6 = true := by decide +kernel
theorem joinNodes_0_0 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 0 118 = true :=
  @QFast.merge_blocks (QFast.checkNodeAt fastViews fastNodes) 0 54 64 blockNodes_0 blockNodes_54
theorem joinNodes_0_118 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 118 14 = true :=
  @QFast.merge_blocks (QFast.checkNodeAt fastViews fastNodes) 118 7 7 blockNodes_118 blockNodes_125
theorem joinNodes_0_132 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 132 14 = true :=
  @QFast.merge_blocks (QFast.checkNodeAt fastViews fastNodes) 132 7 7 blockNodes_132 blockNodes_139
theorem joinNodes_0_146 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 146 13 = true :=
  @QFast.merge_blocks (QFast.checkNodeAt fastViews fastNodes) 146 7 6 blockNodes_146 blockNodes_153
theorem joinNodes_1_0 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 0 132 = true :=
  @QFast.merge_blocks (QFast.checkNodeAt fastViews fastNodes) 0 118 14 joinNodes_0_0 joinNodes_0_118
theorem joinNodes_1_132 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 132 27 = true :=
  @QFast.merge_blocks (QFast.checkNodeAt fastViews fastNodes) 132 14 13 joinNodes_0_132 joinNodes_0_146
theorem joinNodes_2_0 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 0 159 = true :=
  @QFast.merge_blocks (QFast.checkNodeAt fastViews fastNodes) 0 132 27 joinNodes_1_0 joinNodes_1_132
theorem certifiedNodes : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 0 159 = true := joinNodes_2_0
end SignedProjection

namespace SignedProjection
def bMatches (z : Option View) : Bool :=
  match z with
  | none => false
  | some v => vg v == (0xeaeaeaa8eaa8a888 : Word) && vk v == 10 && (vs v).toFinset == Direct64.cols.toFinset

theorem rootNegative : ¬ CoreSigned.build signedOps (0xeaeaeaa8eaa8a888 : BitVec 64) 10 Direct64.cols.toFinset := by
  have shape : bMatches (QFast.get fastViews 31) = true := by decide +kernel
  cases ev : QFast.get fastViews 31 with
  | none => simp [ev, bMatches] at shape
  | some v =>
    have valid := QFast.symCertified rootAliases fastViews fastNodes certifiedRoots certifiedNodes ev
    simp only [ev,bMatches,Bool.and_eq_true,beq_iff_eq] at shape
    change ¬ CoreSigned.build signedOps (vg v) (vk v) (vs v).toFinset at valid
    rwa [shape.1.1,shape.1.2,shape.2] at valid
end SignedProjection

end PEqualNP.Outside.L_meta_47120_aux

open PEqualNP.Outside.L_meta_47120_aux in
theorem PEqualNP.Outside.L_meta_47120 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (3941264040 * 2 ^ 32 + 3936921736) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (3941264040 * 2 ^ 32 + 3936921736) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  LowerSymSix.finish SignedProjection.rootNegative
