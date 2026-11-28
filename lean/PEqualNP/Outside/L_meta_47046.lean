import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_47046_aux
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
  ⟨[⟨.and,[0,1]⟩, ⟨.and,[0,3]⟩, ⟨.or,[7,5]⟩, ⟨.or,[8,4]⟩, ⟨.and,[9,0]⟩,
    ⟨.or,[10,1]⟩, ⟨.and,[4,3]⟩, ⟨.or,[12,6]⟩, ⟨.and,[13,8]⟩, ⟨.or,[14,2]⟩,
    ⟨.and,[15,11]⟩],16⟩

theorem size : witness.size = 11 := rfl

theorem monotone : Monotone2 witness := by
  simp [Monotone2,witness]

set_option maxRecDepth 16000 in
theorem correct : ∀ x : Fin 6 → Bool, witness.eval (List.ofFn x) =
    Nat.testBit (4008241384 * 2 ^ 32 + 3940608192) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  decide +kernel

end LowerSymSix

namespace Direct64
open PEqualNP.CircuitLowerBounds SignedProjection
abbrev W := BitVec 64
abbrev basicOps (a b : W) := signedOps a b
abbrev goal : W := ~~~0xeee8e8e8eae0e8c0
open CoreSigned (build)
def tableB (x : Fin 6 → Bool) :=
  Nat.testBit (4008241384 * 2 ^ 32 + 3940608192) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
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

theorem low (reject : ¬ build basicOps (0xeee8e8e8eae0e8c0 : W) 9 cols.toFinset)
    (gs : List Gate) (o : ℕ) (hg : ∀ g ∈ gs, legal g)
    (he : ∀ x : Fin 6 → Bool, Circuit.eval ⟨gs,o⟩ (List.ofFn x) = tableB x) : 9 < binaryCost gs := by
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
    (reject : ¬ CoreSigned.build SignedProjection.signedOps (0xeee8e8e8eae0e8c0 : BitVec 64) 9 Direct64.cols.toFinset) :
∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4008241384 * 2 ^ 32 + 3940608192) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4008241384 * 2 ^ 32 + 3940608192) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
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
def ew0 : Word := 0x20202020
def ew1 : Word := 0x22002200
def ew2 : Word := 0x22220000
def ew3 : Word := 0x8800000088
def ew4 : Word := 0xa0000000a0
def ew5 : Word := 0xaa00000000
def ew6 : Word := 0x8888
def ew7 : Word := 0xa0a0
def ew8 : Word := 0xaa00
def ew9 : Word := 0x808000008080000
def ew10 : Word := 0xc0000000c000000
def ew11 : Word := 0xc0c000000000000
def ew12 : Word := 0xa0a000000000000
def ew13 : Word := 0xf00000000000000
def ew14 : Word := 0xaa000000000000
def ew15 : Word := 0xcc000000000000
def ew16 : Word := 0xf0000000000000
def ew17 : Word := 0xcc00
def ew18 : Word := 0xf000
def ew19 : Word := 0x2020202020202020
def ew20 : Word := 0x2200220022002200
def ew21 : Word := 0x2222000022220000
def ew22 : Word := 0x2222222200000000
def ew23 : Word := 0xaa000000aa0000
def ew24 : Word := 0x88004400880044
def ew25 : Word := 0xa0005000a00050
def ew26 : Word := 0xaa005500000000
def ew27 : Word := 0x882200008822
def ew28 : Word := 0xcc000000cc00
def ew29 : Word := 0xc0300000c030
def ew30 : Word := 0xcc3300000000
def ew31 : Word := 0x8822000088220000
def ew32 : Word := 0xcc000000cc000000
def ew33 : Word := 0xc0300000c0300000
def ew34 : Word := 0xcc33000000000000
def ew35 : Word := 0x88008800220022
def ew36 : Word := 0xcc00cc00000000
def ew37 : Word := 0xc000c000300030
def ew38 : Word := 0xcc000000330000
def ew39 : Word := 0x8888000088880000
def ew40 : Word := 0xc0c00000c0c00000
def ew41 : Word := 0xcccc000000000000
def ew42 : Word := 0x2200220000220022
def ew43 : Word := 0x3000300000300030
def ew44 : Word := 0x3300330000000000
def ew45 : Word := 0x3300000000330000
def ew46 : Word := 0x8888000000008888
def ew47 : Word := 0xa0a000000000a0a0
def ew48 : Word := 0xaa0000000000aa00
def ew49 : Word := 0xaaaa000000000000
def ew50 : Word := 0x2222000000002222
def ew51 : Word := 0x3030000000003030
def ew52 : Word := 0x3300000000003300
def ew53 : Word := 0x3333000000000000
def ew54 : Word := 0xc0c000000000c0c0
def ew55 : Word := 0xcc0000000000cc00
def ew56 : Word := 0xa0a000000000a0a
def ew57 : Word := 0xc0c000000000c0c
def ew58 : Word := 0xf00000000000f00
def ew59 : Word := 0xf0f000000000000
def ew60 : Word := 0x808080808080808
def ew61 : Word := 0xa000a000a000a00
def ew62 : Word := 0xa0a00000a0a0000
def ew63 : Word := 0xa0a0a0a00000000
def ew64 : Word := 0x8020802080208020
def ew65 : Word := 0x8400840084008400
def ew66 : Word := 0x8421000084210000
def ew67 : Word := 0x8421842100000000
def ew68 : Word := 0x8080202080802020
def ew69 : Word := 0x8484000084840000
def ew70 : Word := 0x8400210084002100
def ew71 : Word := 0x8484212100000000
def ew72 : Word := 0x8080808020202020
def ew73 : Word := 0x8484848400000000
def ew74 : Word := 0x8400840021002100
def ew75 : Word := 0x8484000021210000
def ew76 : Word := 0xa000a00000a000a0
def ew77 : Word := 0x8400840000840084
def ew78 : Word := 0xa500a50000000000
def ew79 : Word := 0xa500000000a50000
def ew80 : Word := 0x44444444
def ew81 : Word := 0x60606060
def ew82 : Word := 0x66006600
def ew83 : Word := 0x66660000
def ew84 : Word := 0x5500550000000000
def ew85 : Word := 0x4488448800000000
def ew86 : Word := 0x50a050a000000000
def ew87 : Word := 0x55aa000000000000
def ew88 : Word := 0x4444000044440000
def ew89 : Word := 0x4040808040408080
def ew90 : Word := 0x4400880044008800
def ew91 : Word := 0x4444888800000000
def ew92 : Word := 0x505000005050000
def ew93 : Word := 0x404080804040808
def ew94 : Word := 0x5000a0005000a00
def ew95 : Word := 0x5050a0a00000000
def ew96 : Word := 0x5500000055000000
def ew97 : Word := 0x5000a0005000a000
def ew98 : Word := 0x5500aa0000000000
def ew99 : Word := 0x5555000000000000
def ew100 : Word := 0x5050a0a000000000
def ew101 : Word := 0xa000a00a000a0
def ew102 : Word := 0xc000c00c000c0
def ew103 : Word := 0xf000f00000000
def ew104 : Word := 0xf000000f00000
def ew105 : Word := 0x5555000055550000
def ew106 : Word := 0x4444888844448888
def ew107 : Word := 0x5050a0a05050a0a0
def ew108 : Word := 0x5500aa005500aa00
def ew109 : Word := 0x5555aaaa00000000
def ew110 : Word := 0x8888222288882222
def ew111 : Word := 0xcccc0000cccc0000
def ew112 : Word := 0xc0c03030c0c03030
def ew113 : Word := 0xcc003300cc003300
def ew114 : Word := 0xcccc333300000000
def ew115 : Word := 0x8888888822222222
def ew116 : Word := 0xcccccccc00000000
def ew117 : Word := 0xc0c0c0c030303030
def ew118 : Word := 0xcc00cc0033003300
def ew119 : Word := 0xcccc000033330000
def ew120 : Word := 0xaaaa00000000aaaa
def ew121 : Word := 0xcccc00000000cccc
def ew122 : Word := 0xf0f000000000f0f0
def ew123 : Word := 0xff0000000000ff00
def ew124 : Word := 0xffff000000000000
def ew125 : Word := 0x8888888888888888
def ew126 : Word := 0xa0a0a0a0a0a0a0a0
def ew127 : Word := 0xaa00aa00aa00aa00
def ew128 : Word := 0xaaaa0000aaaa0000
def ew129 : Word := 0xaaaaaaaa00000000
def ew130 : Word := 0xa0a0a0a0a0a0a0a
def ew131 : Word := 0xc0c0c0c0c0c0c0c
def ew132 : Word := 0xf000f000f000f00
def ew133 : Word := 0xf0f00000f0f0000
def ew134 : Word := 0xf0f0f0f00000000
def ew135 : Word := 0xaa00aa00aa00aa
def ew136 : Word := 0xcc00cc00cc00cc
def ew137 : Word := 0xf000f000f000f0
def ew138 : Word := 0xff000000ff0000
def ew139 : Word := 0xff00ff00000000
def ew140 : Word := 0xcc00cc00cc00cc00
def ew141 : Word := 0xf000f000f000f000
def ew142 : Word := 0xff000000ff000000
def ew143 : Word := 0xff00ff0000000000
def ew144 : Word := 0xf0f00000f0f00000
def ew145 : Word := 0xaaaaaaaa
def ew146 : Word := 0xcccccccc
def ew147 : Word := 0xf0f0f0f0
def ew148 : Word := 0xff00ff00
def ew149 : Word := 0xffff0000
def ew150 : Word := 0xa0a0a0aa0a0a0a0
def ew151 : Word := 0xc0c0c0cc0c0c0c0
def ew152 : Word := 0xf000f00f000f000
def ew153 : Word := 0xf0f0000f0f00000
def ew154 : Word := 0xaaaaaaaaaaaaaaaa
def ew155 : Word := 0xcccccccccccccccc
def ew156 : Word := 0xf0f0f0f0f0f0f0f0
def ew157 : Word := 0xff00ff00ff00ff00
def ew158 : Word := 0xffff0000ffff0000
def ew159 : Word := 0xffffffff00000000
def ew160 : Word := 0x8080000000008080
def ew161 : Word := 0xa8a800000000a8a8
def ew162 : Word := 0x808000000000808
def ew163 : Word := 0x2020000000002020
def ew164 : Word := 0x8800000000008800
def ew165 : Word := 0xaa8800000000aa88
def ew166 : Word := 0x88000000000088
def ew167 : Word := 0x2200000000002200
def ew168 : Word := 0xa00000000000a000
def ew169 : Word := 0xaaa000000000aaa0
def ew170 : Word := 0xa00000000000a0
def ew171 : Word := 0xa00000000000a00
def ew172 : Word := 0xaa8000000000aa80
def ew173 : Word := 0x2a00000000002a00
def ew174 : Word := 0xaaaa000000008080
def ew175 : Word := 0xa8a000000000a8a0
def ew176 : Word := 0x20a00000000020a0
def ew177 : Word := 0xaaaa000000008800
def ew178 : Word := 0xa88800000000a888
def ew179 : Word := 0x888000000000888
def ew180 : Word := 0xaaaa00000000a000
def ew181 : Word := 0x8000800080008000
def ew182 : Word := 0x8420842084208420
def ew183 : Word := 0x20002000200020
def ew184 : Word := 0x400040004000400
def ew185 : Word := 0x8020000080200000
def ew186 : Word := 0x8421802084218020
def ew187 : Word := 0x802000008020
def ew188 : Word := 0x401000004010000
def ew189 : Word := 0x8020802000000000
def ew190 : Word := 0x8421842180208020
def ew191 : Word := 0x80208020
def ew192 : Word := 0x401040100000000
def ew193 : Word := 0x8400000084000000
def ew194 : Word := 0x8421840084218400
def ew195 : Word := 0x840000008400
def ew196 : Word := 0x21000000210000
def ew197 : Word := 0x8400840000000000
def ew198 : Word := 0x8421842184008400
def ew199 : Word := 0x84008400
def ew200 : Word := 0x21002100000000
def ew201 : Word := 0x8421000000000000
def ew202 : Word := 0x8421842184210000
def ew203 : Word := 0x84210000
def ew204 : Word := 0x842100000000
def ew205 : Word := 0x8421800084218000
def ew206 : Word := 0x421000004210000
def ew207 : Word := 0x8421842180008000
def ew208 : Word := 0x421042100000000
def ew209 : Word := 0x8420000084200000
def ew210 : Word := 0x842000008420
def ew211 : Word := 0x8420842000000000
def ew212 : Word := 0x84208420
def ew213 : Word := 0x8420840084208400
def ew214 : Word := 0x400840004008400
def ew215 : Word := 0x8421842180200000
def ew216 : Word := 0x401842100000000
def ew217 : Word := 0x8400800084008000
def ew218 : Word := 0x21002000210020
def ew219 : Word := 0x8421802000000000
def ew220 : Word := 0x84218020
def ew221 : Word := 0x8420842084008400
def ew222 : Word := 0x400040084008400
def ew223 : Word := 0x8421802084210000
def ew224 : Word := 0x401000084210000
def ew225 : Word := 0x8400840080008000
def ew226 : Word := 0x21002100200020
def ew227 : Word := 0x8421000080200000
def ew228 : Word := 0x842100008020
def ew229 : Word := 0x8421842100008400
def ew230 : Word := 0x8421002100000000
def ew231 : Word := 0x8421842100210000
def ew232 : Word := 0x8400842100000000
def ew233 : Word := 0x8421000084218400
def ew234 : Word := 0x8421000000210000
def ew235 : Word := 0x8421002184210000
def ew236 : Word := 0x8400000084210000
def ew237 : Word := 0x8400840084218400
def ew238 : Word := 0x8400840000008400
def ew239 : Word := 0x8400842184008400
def ew240 : Word := 0x8400000084008400
def ew241 : Word := 0x60006000
def ew242 : Word := 0x66606660
def ew243 : Word := 0x600060
def ew244 : Word := 0x6000600
def ew245 : Word := 0x60600000
def ew246 : Word := 0x66666060
def ew247 : Word := 0x6060
def ew248 : Word := 0x6060000
def ew249 : Word := 0x66000000
def ew250 : Word := 0x66666600
def ew251 : Word := 0x6600
def ew252 : Word := 0x660000
def ew253 : Word := 0x64446444
def ew254 : Word := 0x66666000
def ew255 : Word := 0x6660000
def ew256 : Word := 0x22202220
def ew257 : Word := 0x66600000
def ew258 : Word := 0x6660
def ew259 : Word := 0x64644444
def ew260 : Word := 0x66606600
def ew261 : Word := 0x6006600
def ew262 : Word := 0x22222020
def ew263 : Word := 0x66006000
def ew264 : Word := 0x660060
def ew265 : Word := 0x44446644
def ew266 : Word := 0x44664444
def ew267 : Word := 0x888800008888
def ew268 : Word := 0x5555a0a05555a0a0
def ew269 : Word := 0x5050a8a85050a8a8
def ew270 : Word := 0x80800000808
def ew271 : Word := 0x4444808044448080
def ew272 : Word := 0x5555080855550808
def ew273 : Word := 0xc000c000c000c0
def ew274 : Word := 0xfc00fc00fc00fc
def ew275 : Word := 0xc000c000c000c
def ew276 : Word := 0x30003000300030
def ew277 : Word := 0x2a002a002a002a
def ew278 : Word := 0xa800a800a800a8
def ew279 : Word := 0x2222222222222222
def ew280 : Word := 0xfcfcfcfcfcfcfcfc
def ew281 : Word := 0xffffffffcccccccc
def ew282 : Word := 0xf8f8f8f8f8f8f8f8
def ew283 : Word := 0xa8a8a8a8a8a8a8a8
def labelsBlock0 : Array Nat := #[
  0xd14,
  0x1544,
  0x1924,
  0x1,
  0x2514,
  0x1514,
  0xd24,
  0x1002,
  0x334c,
  0x1b68,
  0x1b4c,
  0x1648,
  0x100e,
  0x330c,
  0xb0c,
  0x714
]
def labelsBlock1 : Array Nat := #[
  0x5,
  0x230c,
  0xb24,
  0x81,
  0x2580,
  0x3aa8,
  0x3ac0,
  0x3a68,
  0x85,
  0x614,
  0x185,
  0x2584,
  0x2384,
  0x328c,
  0x1f5,
  0x610
]
def labelsBlock2 : Array Nat := #[
  0xd30,
  0x608,
  0x219,
  0x70c,
  0x21d,
  0x1550,
  0x221,
  0x1944,
  0x1650,
  0x23d,
  0x1858,
  0x2964,
  0x241,
  0x9,
  0xd,
  0x11
]
def labelsBlock3 : Array Nat := #[
  0x704,
  0x33c4,
  0x15,
  0x39c4,
  0x19,
  0x1d,
  0xb04,
  0x21,
  0x25,
  0x3514,
  0x100a,
  0x35c4,
  0x29,
  0x2d,
  0x31,
  0xd04
]
def labelsBlock4 : Array Nat := #[
  0x35,
  0x3924,
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
  0x69,
  0x6d
]
def labelsBlock5 : Array Nat := #[
  0x71,
  0x75,
  0x79,
  0x7d,
  0x318c,
  0x2304,
  0x3164,
  0x234c,
  0x89,
  0x1a54,
  0xf14,
  0xf28,
  0x8d,
  0x91,
  0xf00,
  0x95
]
def labelsBlock6 : Array Nat := #[
  0x99,
  0x1540,
  0x9d,
  0xa1,
  0x1500,
  0xa5,
  0xa9,
  0xad,
  0xb1,
  0xb5,
  0xb9,
  0xbd,
  0xc1,
  0xc5,
  0xc9,
  0xcd
]
def labelsBlock7 : Array Nat := #[
  0xd1,
  0xd5,
  0xd9,
  0xdd,
  0xe1,
  0xe5,
  0xe9,
  0xed,
  0xf1,
  0xf5,
  0x1a3c,
  0xf9,
  0xfd,
  0x101,
  0x105,
  0x109
]
def labelsBlock8 : Array Nat := #[
  0x10d,
  0x111,
  0x115,
  0x119,
  0x11d,
  0x121,
  0x125,
  0x3540,
  0x3a80,
  0x129,
  0x12d,
  0x131,
  0x135,
  0x2a3c,
  0x139,
  0x13d
]
def labelsBlock9 : Array Nat := #[
  0x141,
  0x145,
  0x1f68,
  0x149,
  0x14d,
  0x151,
  0x155,
  0x159,
  0x2fa8,
  0x15d,
  0x3a28,
  0x161,
  0x165,
  0x2f14,
  0x169,
  0x16d
]
def labelsBlock10 : Array Nat := #[
  0x35c0,
  0x171,
  0x175,
  0x179,
  0x17d,
  0x181,
  0x2500,
  0x1a64,
  0x189,
  0xa18,
  0x18d,
  0x191,
  0x195,
  0x1218,
  0x199,
  0x19d
]
def labelsBlock11 : Array Nat := #[
  0x1a1,
  0x1504,
  0x1a5,
  0x1a9,
  0x1ad,
  0x1b1,
  0x1b5,
  0x1b9,
  0x1bd,
  0x1c1,
  0x1904,
  0x1c5,
  0x1c9,
  0x1cd,
  0x1d1,
  0x604
]
def labelsBlock12 : Array Nat := #[
  0x1948,
  0x1928,
  0x1d5,
  0x1d9,
  0x1644,
  0x1dd,
  0x1e1,
  0x1e5,
  0x1e68,
  0x1e9,
  0x1ed,
  0x1f1,
  0x1604,
  0xe04,
  0x1c34,
  0x1006
]
def labelsBlock13 : Array Nat := #[
  0x1066,
  0x1f9,
  0x1a2c,
  0x106a,
  0x3494,
  0x1fd,
  0x36c8,
  0x3ac8,
  0x201,
  0x36d0,
  0x106e,
  0x1072,
  0x205,
  0x209,
  0x3ae0,
  0x1614
]
def labelsBlock14 : Array Nat := #[
  0x71006a,
  0x20d,
  0x141c,
  0x510066,
  0x211,
  0x121c,
  0x215,
  0x1e70,
  0x160c,
  0x101c,
  0x182c,
  0x103a,
  0xb28,
  0x33c8,
  0x1012,
  0x1042
]
def labelsBlock15 : Array Nat := #[
  0x103e,
  0x101a,
  0x1016,
  0x39a4,
  0x2388,
  0x225,
  0x154c,
  0x229,
  0x22d,
  0x600,
  0x231,
  0x102e,
  0x1608,
  0x1076,
  0x235,
  0x710
]
def labelsBlock16 : Array Nat := #[
  0x60c,
  0x708,
  0x239,
  0x1418,
  0x2218,
  0x1510,
  0x1a58,
  0x3154,
  0x2690,
  0x245,
  0x108a,
  0x249,
  0x108e,
  0x24d,
  0x1092,
  0x1096
]
def labelsBlock17 : Array Nat := #[
  0x107a,
  0x109a,
  0x109e,
  0x251,
  0x255,
  0x259,
  0x25d,
  0x107e,
  0x261,
  0x1082,
  0x265,
  0x10a2,
  0x1086,
  0x105e,
  0x269,
  0x174c
]
def labelsBlock18 : Array Nat := #[
  0x1046,
  0x410096,
  0x41009a,
  0x1960,
  0x71007a,
  0x2590,
  0x1036,
  0x132c,
  0x51007a,
  0x610096,
  0x61009a,
  0x52007a,
  0x104e,
  0x104a,
  0x620096,
  0x62009a
]
def labelsBlock19 : Array Nat := #[
  0x1052,
  0x1056,
  0xe28,
  0x2688,
  0x105a,
  0x54007a,
  0x1062,
  0x64008e,
  0x640092,
  0x640096,
  0x64009a,
  0x2ba8,
  0x2308,
  0x51008a,
  0x26d,
  0x521092
]
def labelsBlock20 : Array Nat := #[
  0x521096,
  0x52107a,
  0x52109a,
  0x52109e,
  0xe30,
  0x61008a,
  0x62107a,
  0x621092,
  0x621096,
  0x62109a,
  0x62109e,
  0x4210a2,
  0x40107a,
  0x43008a,
  0x43108e,
  0x431092
]
def labelsBlock21 : Array Nat := #[
  0x431096,
  0x44109e,
  0x1026,
  0x4410a2,
  0x54008a,
  0x54108e,
  0x541092,
  0x541096,
  0x54107a,
  0x54109a,
  0x2ba4,
  0x54107e,
  0x2418,
  0x5210a2,
  0x70207a,
  0x73108a
]
def labelsBlock22 : Array Nat := #[
  0x71207e,
  0x732092,
  0x732096,
  0x74209e,
  0x4420a2,
  0x742082,
  0x149410096,
  0x1022,
  0x102a,
  0x41008e,
  0x114121092,
  0x1d412107a,
  0x39e0
]
def labelsGet (i : Nat) : Nat :=
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
def lh (s : Nat) (d : List Nat) (ws : List Nat) (i : Nat) : Nat :=
  labelsGet (d.getD (((ws.getD (i / (64 / s)) 0) >>> ((i % (64 / s)) * s)) % 2 ^ s) 0)
def viewsBlock0 : Array View := #[
  ⟨0x22222222,⟨1,by decide⟩,0x22202000,[ew0,ew1,ew2],3,lh 2 [0,1,2,3] [0xd090]⟩,
  ⟨0xaa000000aa,⟨1,by decide⟩,0xa800000080,[ew3,ew4,ew5],3,fun _ => 3⟩,
  ⟨0xaaaa,⟨1,by decide⟩,0xa880,[ew6,ew7,ew8],3,fun _ => 3⟩,
  ⟨0xc0c00000c0c0000,⟨18,by decide⟩,0xc08000008000000,[ew9,ew10,ew11],3,fun _ => 3⟩,
  ⟨0xf0f000000000000,⟨48,by decide⟩,0xe08000000000000,[ew12,ew11,ew13],3,fun _ => 3⟩,
  ⟨0xff000000000000,⟨48,by decide⟩,0xe8000000000000,[ew14,ew15,ew16],3,fun _ => 3⟩,
  ⟨0xff00,⟨8,by decide⟩,0xe800,[ew8,ew17,ew18],3,fun _ => 3⟩,
  ⟨0x2222222222222222,⟨1,by decide⟩,0x2220202022202000,[ew19,ew20,ew21,ew22],4,lh 3 [4,5,6,0,7] [0x89a249000000]⟩,
  ⟨0xaa005500aa0055,⟨0,by decide⟩,0xa8004000a00040,[ew23,ew24,ew25,ew26],4,fun _ => 3⟩,
  ⟨0xcc330000cc33,⟨0,by decide⟩,0xc8200000c800,[ew27,ew28,ew29,ew30],4,fun _ => 3⟩,
  ⟨0xcc330000cc330000,⟨16,by decide⟩,0xcc200000c8200000,[ew31,ew32,ew33,ew34],4,fun _ => 3⟩,
  ⟨0xcc00cc00330033,⟨0,by decide⟩,0xc800c800200000,[ew35,ew36,ew37,ew38],4,fun _ => 3⟩,
  ⟨0xcccc0000cccc0000,⟨18,by decide⟩,0xccc80000c8c00000,[ew39,ew40,ew32,ew41],4,lh 3 [8,9,10,11,12] [0x859451000000]⟩,
  ⟨0x3300330000330033,⟨0,by decide⟩,0x2200200000200000,[ew42,ew43,ew44,ew45],4,fun _ => 3⟩,
  ⟨0xaaaa00000000aaaa,⟨1,by decide⟩,0xaaa800000000a880,[ew46,ew47,ew48,ew49],5,lh 3 [13,14,15,6,16] [0x89a249000000]⟩,
  ⟨0x3333000000003333,⟨0,by decide⟩,0x2220000000002000,[ew50,ew51,ew52,ew53],4,fun _ => 3⟩
]
def viewsBlock1 : Array View := #[
  ⟨0xcccc00000000cccc,⟨2,by decide⟩,0xccc800000000c8c0,[ew46,ew54,ew55,ew41],4,fun _ => 3⟩,
  ⟨0xf0f000000000f0f,⟨0,by decide⟩,0xe08000000000800,[ew56,ew57,ew58,ew59],5,fun _ => 3⟩,
  ⟨0xa0a0a0a0a0a0a0a,⟨1,by decide⟩,0xa0808080a000800,[ew60,ew61,ew62,ew63],3,lh 3 [17,2,18,14,19] [0x89a249000000]⟩,
  ⟨0x8421842184218421,⟨0,by decide⟩,0x8420802080208000,[ew64,ew65,ew66,ew67],5,lh 3 [20,21,22,23,24] [0x810208610208]⟩,
  ⟨0x8484212184842121,⟨0,by decide⟩,0x8480202080802000,[ew68,ew69,ew70,ew71],5,fun _ => 3⟩,
  ⟨0x8484848421212121,⟨0,by decide⟩,0x8480808020202000,[ew72,ew73,ew74,ew75],5,fun _ => 3⟩,
  ⟨0xa500a50000a500a5,⟨0,by decide⟩,0xa400a00000a00080,[ew76,ew77,ew78,ew79],5,fun _ => 3⟩,
  ⟨0x66666666,⟨1,by decide⟩,0x62606040,[ew80,ew81,ew82,ew83],5,lh 3 [5,0,25,6,26] [0x89a249000000]⟩,
  ⟨0x55aa55aa00000000,⟨33,by decide⟩,0x44a840a800000000,[ew84,ew85,ew86,ew87],4,fun _ => 3⟩,
  ⟨0x4444888844448888,⟨3,by decide⟩,0x4440888840408880,[ew88,ew89,ew90,ew91],4,fun _ => 3⟩,
  ⟨0x5050a0a05050a0a,⟨1,by decide⟩,0x400080800000800,[ew92,ew93,ew94,ew95],4,fun _ => 3⟩,
  ⟨0x5500aa005500aa00,⟨9,by decide⟩,0x4400a8004000a800,[ew96,ew90,ew97,ew98],4,fun _ => 3⟩,
  ⟨0x5555aaaa00000000,⟨33,by decide⟩,0x4440a8a800000000,[ew99,ew91,ew100,ew98],4,fun _ => 3⟩,
  ⟨0xf000f00f000f0,⟨4,by decide⟩,0x8000800e000c0,[ew101,ew102,ew103,ew104],4,fun _ => 3⟩,
  ⟨0x5555aaaa5555aaaa,⟨1,by decide⟩,0x4440a8a84040a880,[ew105,ew106,ew107,ew108,ew109],7,lh 3 [27,28,4,0,29,30] [0x1000489000489000,0x1612000d9]⟩,
  ⟨0xcccc3333cccc3333,⟨0,by decide⟩,0xccc82020c8c02000,[ew110,ew111,ew112,ew113,ew114],7,fun _ => 3⟩
]
def viewsBlock2 : Array View := #[
  ⟨0xcccccccc33333333,⟨0,by decide⟩,0xccc8c8c822202000,[ew115,ew116,ew117,ew118,ew119],7,fun _ => 3⟩,
  ⟨0xffff00000000ffff,⟨0,by decide⟩,0xeee800000000e8c0,[ew120,ew121,ew122,ew123,ew124],7,lh 3 [13,14,31,32,33,34] [0x1249000000000000,0x15a51a449]⟩,
  ⟨0xaaaaaaaaaaaaaaaa,⟨1,by decide⟩,0xaaa8a8a8aaa0a880,[ew125,ew126,ew127,ew128,ew129],6,lh 3 [17,5,14,15,35,36] [0x1249000000000000,0x15c692449]⟩,
  ⟨0xf0f0f0f0f0f0f0f,⟨0,by decide⟩,0xe0808080a000800,[ew130,ew131,ew132,ew133,ew134],6,fun _ => 3⟩,
  ⟨0xff00ff00ff00ff,⟨0,by decide⟩,0xe800e800e000c0,[ew135,ew136,ew137,ew138,ew139],6,lh 3 [31,33,5,4,37,38] [0x2406c0240480240,0x160048090]⟩,
  ⟨0xff00ff00ff00ff00,⟨8,by decide⟩,0xee00e800ea00e800,[ew127,ew140,ew141,ew142,ew143],6,fun _ => 3⟩,
  ⟨0xffff0000ffff0000,⟨16,by decide⟩,0xeee80000eae00000,[ew128,ew111,ew144,ew142,ew124],6,lh 3 [8,39,40,37,1,41] [0x1249000000000000,0x15a51a449]⟩,
  ⟨0xffffffff,⟨0,by decide⟩,0xeae0e8c0,[ew145,ew146,ew147,ew148,ew149],6,fun _ => 3⟩,
  ⟨0xf0f0f0ff0f0f0f0,⟨4,by decide⟩,0xe080808e0e0e0c0,[ew150,ew151,ew134,ew152,ew153],7,fun _ => 3⟩,
  ⟨0xffffffffffffffff,⟨0,by decide⟩,0xeee8e8e8eae0e8c0,[ew154,ew155,ew156,ew157,ew158,ew159],9,lh 4 [28,1,14,37,42,43,10,17,5,44] [0x5300110053001144,0x7300110063001144,0x8300110023001144,0x9300110022222222]⟩
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
  ⟨0,3,[ew0,ew1,ew2],lh 3 [1,0,5,6,39,2] [0xa020eb04b8d9220,0x69894b0a4d2]⟩,
  ⟨14,5,[ew46,ew47,ew48,ew49],lh 5 [58,13,6,14,18,57,15,51,59,49,35,0,65,54,45,46,47,48,50,52,53,55,56,60,61,62,63,64] [0x818427994a71042,0xa1064998e692551,0x10a5b186da90ed,0x1024024a902421,0xc8863c096bba068,0x20a500821da17a,0xc21008a202021,0xd8301c2701d8c]⟩,
  ⟨14,4,[ew160,ew46,ew47,ew48,ew49],lh 4 [57,6,18,49,14,65,15,35,66,67,68,58,69,63] [0x331cb0a094847162,0x1501d1142030322,0x505]⟩,
  ⟨14,4,[ew46,ew47,ew161,ew48,ew49],lh 4 [0,57,65,51,14,15,35,49,13,6,69] [0x699818140457765a,0x121203031212040,0x33]⟩,
  ⟨14,4,[ew162,ew46,ew47,ew48,ew49],lh 4 [13,14,15,51,57,6,0,49,35,48] [0x2925040413138572,0x504061610402131,0x103]⟩,
  ⟨14,4,[ew163,ew46,ew47,ew48,ew49],lh 4 [13,14,57,0,51,15,6,49,35,48] [0x4987202031316655,0x202031310202141,0x104]⟩,
  ⟨14,4,[ew164,ew46,ew47,ew48,ew49],lh 4 [13,15,6,51,0,14,57,18,70,71,72,58,48,73] [0xc112b0a055928271,0x20604343060113d,0x403]⟩,
  ⟨14,4,[ew46,ew47,ew48,ew165,ew49],lh 4 [35,18,59,65,14,13,57,6,73,15,51] [0x4701651914180701,0x63535a4022020020,0x363]⟩,
  ⟨14,4,[ew166,ew46,ew47,ew48,ew49],lh 4 [57,59,35,65,18,13,14,51,15,54,0] [0x2121505066212184,0x30317a14050947,0x303]⟩,
  ⟨14,4,[ew167,ew46,ew47,ew48,ew49],lh 4 [57,59,65,6,14,18,35,13,51,15,54] [0x6161202084313155,0x20214317070a49,0x202]⟩,
  ⟨14,4,[ew46,ew168,ew47,ew48,ew49],lh 4 [49,57,65,59,18,14,74,75,35,54,6,0,76,58,77] [0x4001094003800760,0x1121235ed1c1b5a3,0x212]⟩,
  ⟨14,4,[ew46,ew47,ew48,ew169,ew49],lh 4 [15,6,49,0,57,65,13,18,77,59,14] [0x220200203702001,0x63453a3154191318,0x464]⟩,
  ⟨14,4,[ew170,ew46,ew47,ew48,ew49],lh 4 [13,15,14,49,6,57,59,0,54,63,65] [0x3114505072641313,0x405094203012821,0x20a]⟩,
  ⟨14,4,[ew171,ew46,ew47,ew48,ew49],lh 4 [18,13,15,65,6,14,0,57,49,59,63] [0x220313155440202,0x17171a6908102002,0x613]⟩,
  ⟨14,3,[ew46,ew47,ew172,ew49],lh 3 [65,18,49,57,6,35,78,14] [0x3618b6721044a531,0x18]⟩,
  ⟨14,3,[ew173,ew46,ew47,ew49],lh 3 [57,49,65,18,35,6,14,15] [0x26083e1410d2c659,0x10]⟩
]
def nodesBlock1 : Array Node := #[
  ⟨14,3,[ew46,ew47,ew48,ew174],lh 3 [57,49,65,18,6,14,79,63] [0x82f656082d9331,0x82]⟩,
  ⟨14,3,[ew160,ew161,ew48,ew49],lh 4 [57,65,35,49,63,48,78,14,79,18] [0x144932080276253,0x101001]⟩,
  ⟨14,3,[ew46,ew175,ew48,ew49],lh 4 [13,15,51,6,18,57,0,14,80] [0x7762050112814413,0x60203050]⟩,
  ⟨14,3,[ew176,ew46,ew48,ew49],lh 3 [18,13,14,15,0,57,6,51] [0x1148403c698a2618,0x8f]⟩,
  ⟨14,3,[ew46,ew47,ew48,ew177],lh 4 [15,13,51,6,18,0,48,81,57,14] [0x5252441002706003,0x91213181]⟩,
  ⟨14,3,[ew164,ew47,ew165,ew49],lh 4 [18,13,51,15,6,80,54,81,57] [0x8132320170600450,0x121341]⟩,
  ⟨14,3,[ew47,ew178,ew48,ew49],lh 4 [49,57,65,59,18,35,82,14,54] [0x840121237633050,0x21214001]⟩,
  ⟨14,3,[ew179,ew47,ew48,ew49],lh 4 [49,57,65,59,18,35,54,0,14] [0x3873400106400350,0x21211212]⟩,
  ⟨14,3,[ew46,ew47,ew48,ew180],lh 4 [49,59,57,18,65,6,0,35,54,83,14] [0x1a91300208300170,0x66425524]⟩,
  ⟨14,3,[ew46,ew168,ew169,ew49],lh 4 [0,49,57,35,59,82,18,63,83] [0x8070611214311050,0x242302]⟩,
  ⟨14,2,[ew161,ew172,ew49],lh 3 [49,18,35,65,13] [0x71a201050]⟩,
  ⟨14,2,[ew161,ew48,ew174],lh 2 [65,57,49,18] [0x1144be]⟩,
  ⟨14,2,[ew175,ew165,ew49],lh 3 [18,13,51,15,57] [0x28b060602]⟩,
  ⟨14,2,[ew47,ew165,ew177],lh 3 [18,51,15,57,6] [0x42818451]⟩,
  ⟨14,2,[ew178,ew169,ew49],lh 3 [49,57,35,59,18] [0x2ca8010d0]⟩,
  ⟨14,2,[ew46,ew169,ew180],lh 3 [0,49,35,59,18] [0xc28082d1]⟩
]
def nodesBlock2 : Array Node := #[
  ⟨18,3,[ew60,ew61,ew62,ew63],lh 4 [39,2,17,18,14,85,84,86,87] [0x1004552331614030,0x12820270]⟩,
  ⟨19,5,[ew64,ew65,ew66,ew67],lh 6 [4,22,90,21,5,23,20,91,97,88,89,92,93,94,95,96,98,99,100,101,102,103,104,105,106,107,108,109,110,111,112,113,114,115,116,117] [0x412c708a246046,0x3c70c738608d307,0x1124480c3408104,0x5460005081484c7,0x1025c8000586146,0x6811046410c3602,0x1417020026c20c2,0x7c2145781001741,0x843143804000,0x8c4144883]⟩,
  ⟨19,4,[ew181,ew64,ew65,ew66,ew67],lh 4 [21,20,22,23,97,4,91,90,118,119,120,121,89,5] [0x112cb3a390807261,0x53225020d4114104,0x300]⟩,
  ⟨19,4,[ew64,ew65,ew182,ew66,ew67],lh 4 [21,23,91,90,4,20,122,22,89,5,123,124,125,126] [0x3772141206655328,0x41d1c0b0a1413090,0x100]⟩,
  ⟨19,4,[ew183,ew64,ew65,ew66,ew67],lh 4 [4,21,5,23,22,91,20,122,90,94] [0x7954030321218466,0x304012125303517,0x201]⟩,
  ⟨19,4,[ew184,ew64,ew65,ew66,ew67],lh 4 [4,90,5,21,20,23,91,22,94,97] [0x4814505032327164,0x105112310409232,0x203]⟩,
  ⟨19,4,[ew185,ew64,ew65,ew66,ew67],lh 4 [90,91,4,21,5,20,22,97,127,128,129,130,122,23] [0x115b2a244908071,0x202600630152113c,0xd23]⟩,
  ⟨19,4,[ew64,ew65,ew66,ew186,ew67],lh 4 [90,4,5,22,97,91,23,89,122,131,132,21,133,134] [0x2301614552480307,0xc2161b20130a0090,0x1d1]⟩,
  ⟨19,4,[ew187,ew64,ew65,ew66,ew67],lh 4 [90,23,4,22,91,5,21,97,135,136,89,100] [0x30a212155030344,0x2121099608827b76,0x121]⟩,
  ⟨19,4,[ew188,ew64,ew65,ew66,ew67],lh 4 [22,23,90,4,91,5,97,21,100] [0x2040131375020264,0x3100220024131854,0x131]⟩,
  ⟨19,4,[ew189,ew64,ew65,ew66,ew67],lh 4 [5,22,21,97,23,90,20,137,138,139,140,4,91,141] [0x31c1b4a090817163,0x5115202034d0202,0x22]⟩,
  ⟨19,4,[ew64,ew65,ew66,ew67,ew190],lh 4 [90,5,4,20,21,22,141,97,142,143,144,145,23] [0x1407323614130503,0x11a1242900802500,0xc2b]⟩,
  ⟨19,4,[ew191,ew64,ew65,ew66,ew67],lh 4 [90,5,21,22,20,4,97,23,135] [0x304551212030364,0x1033001208471214,0x122]⟩,
  ⟨19,4,[ew192,ew64,ew65,ew66,ew67],lh 4 [90,5,21,22,4,20,23,97,135] [0x303642121303055,0x4043001208471212,0x142]⟩,
  ⟨19,4,[ew64,ew193,ew65,ew66,ew67],lh 4 [146,4,20,90,5,23,22,21,147] [0x210400230022002,0x1315334851517463,0x415]⟩,
  ⟨19,4,[ew64,ew65,ew66,ew194,ew67],lh 4 [146,20,4,23,22,21,90,5,147] [0x120100110011001,0x2325277324266548,0x323]⟩
]
def nodesBlock3 : Array Node := #[
  ⟨19,4,[ew195,ew64,ew65,ew66,ew67],lh 4 [91,4,146,5,20,90,22,23,21,148,149,136] [0x4004a19183550202,0x17161b6304100220,0x317]⟩,
  ⟨19,4,[ew196,ew64,ew65,ew66,ew67],lh 4 [91,4,90,97,5,20,146,21,23,22,150,151,136] [0x2005b1a144923030,0x12182c7205100660,0x817]⟩,
  ⟨19,4,[ew64,ew197,ew65,ew66,ew67],lh 4 [152,90,91,5,21,4,146,20,22,23,153] [0x2002066010072002,0x515a134195434381,0x354]⟩,
  ⟨19,4,[ew64,ew65,ew66,ew67,ew198],lh 4 [152,23,5,21,20,146,97,22,154,91,153,90,4] [0x6006910105504004,0x3328812b717a3232,0xc12]⟩,
  ⟨19,4,[ew199,ew64,ew65,ew66,ew67],lh 4 [21,97,22,152,91,23,5,4,90,155,156,157] [0x123255a090824141,0x7b27020613313010,0x600]⟩,
  ⟨19,4,[ew200,ew64,ew65,ew66,ew67],lh 4 [20,5,21,97,22,23,152,158,159,4,90,157] [0x660958172440303,0x1b5a212130031210,0x122]⟩,
  ⟨19,4,[ew64,ew65,ew201,ew66,ew67],lh 4 [90,160,22,20,5,4,97,21,23,161] [0x5116411331130203,0x8574052004200220,0x459]⟩,
  ⟨19,4,[ew64,ew65,ew66,ew67,ew202],lh 4 [160,91,90,22,21,5,4,161,23] [0x1001100110010110,0x5847233223322342,0x665]⟩,
  ⟨19,4,[ew203,ew64,ew65,ew66,ew67],lh 4 [91,90,160,4,97,5,21,22,162,163,23,154] [0x2002a35591814040,0x1371176102200220,0xb63]⟩,
  ⟨19,4,[ew204,ew64,ew65,ew66,ew67],lh 4 [91,90,160,5,22,20,4,164,165,21,23,154] [0x2002669381715050,0x1441134102200220,0xba3]⟩,
  ⟨19,3,[ew64,ew65,ew205,ew67],lh 3 [20,122,21,22,4,23,5] [0x4adc4d6201048048,0x152]⟩,
  ⟨19,3,[ew206,ew64,ew65,ew67],lh 4 [20,21,22,122,90,23,97,4,91] [0x280511721141033,0x52246006]⟩,
  ⟨19,3,[ew64,ew65,ew66,ew207],lh 3 [20,21,22,97,4,23,89,5] [0x4a9428f6030580b0,0x149]⟩,
  ⟨19,3,[ew208,ew64,ew65,ew66],lh 4 [21,20,22,97,90,23,89,122,4] [0x1266050825241313,0x2041077]⟩,
  ⟨19,3,[ew64,ew65,ew209,ew67],lh 4 [21,20,23,89,122,90,4,91,166,22] [0x905811210441733,0x20062625]⟩,
  ⟨19,3,[ew210,ew64,ew65,ew67],lh 4 [21,22,23,97,122,90,4,89,91] [0x3177600250014480,0x21153263]⟩
]
def nodesBlock4 : Array Node := #[
  ⟨19,3,[ew64,ew65,ew211,ew66],lh 4 [21,89,91,97,4,20,122,90,23,22,5] [0x9987206655433211,0x8040a07]⟩,
  ⟨19,3,[ew212,ew64,ew65,ew66],lh 4 [21,20,22,23,90,89,122,91,97,4] [0x1255903042328171,0x2041066]⟩,
  ⟨19,3,[ew64,ew213,ew66,ew67],lh 4 [91,90,4,20,89,21,5,22,23] [0x1651032004401003,0x82521271]⟩,
  ⟨19,3,[ew214,ew64,ew66,ew67],lh 3 [91,90,4,21,5,89,22,20] [0x21d00e02b1319045,0x113]⟩,
  ⟨19,3,[ew64,ew65,ew66,ew215],lh 3 [91,90,4,21,20,22,122,5] [0x22a93591100f0204,0x1d3]⟩,
  ⟨19,3,[ew216,ew64,ew65,ew66],lh 3 [91,90,4,21,5,20,22,89] [0x10e020751a471a10,0x63]⟩,
  ⟨19,3,[ew64,ew217,ew66,ew67],lh 4 [90,4,5,91,97,22,89,122,20,23] [0x250181424273306,0x21910150]⟩,
  ⟨19,3,[ew218,ew64,ew66,ew67],lh 3 [91,90,4,5,21,89,22,23] [0x21d0118391319a08,0xd4]⟩,
  ⟨19,3,[ew64,ew65,ew66,ew219],lh 4 [91,90,4,5,22,89,97,20,23] [0x1341072006301005,0x32821241]⟩,
  ⟨19,3,[ew220,ew64,ew65,ew66],lh 4 [90,4,5,21,91,22,20,89,122] [0x507132105014416,0x2302328]⟩,
  ⟨19,3,[ew64,ew221,ew66,ew67],lh 4 [21,22,97,20,23,90,5,91,100,141] [0x105249280203371,0x60064115]⟩,
  ⟨19,3,[ew222,ew64,ew66,ew67],lh 4 [5,21,20,22,141,91,90,23,97] [0x102733610103252,0x1108244]⟩,
  ⟨19,3,[ew64,ew65,ew223,ew67],lh 4 [5,21,22,97,141,23,91,20,90] [0x1010354407013262,0x1105228]⟩,
  ⟨19,3,[ew224,ew64,ew65,ew67],lh 4 [5,21,20,22,141,91,97,90,23] [0x2352011001101002,0x83376244]⟩,
  ⟨19,3,[ew64,ew225,ew66,ew67],lh 3 [90,4,5,20,21,22,141] [0x10680a02ce513143,0x8c]⟩,
  ⟨19,3,[ew226,ew64,ew66,ew67],lh 3 [90,4,5,20,21,22,141] [0x12ce513148110605,0x8c]⟩
]
def nodesBlock5 : Array Node := #[
  ⟨19,3,[ew64,ew65,ew227,ew67],lh 3 [90,4,5,20,21,22,141] [0x10680a02ce513143,0x8c]⟩,
  ⟨19,3,[ew228,ew64,ew65,ew67],lh 3 [90,4,5,21,20,22,141] [0x30e1442ca0c2893,0xd]⟩,
  ⟨19,3,[ew64,ew193,ew194,ew67],lh 3 [146,20,90,4,23,136,21] [0x38a3cea058401201,0x2]⟩,
  ⟨19,3,[ew64,ew65,ew66,ew229],lh 3 [91,146,5,21,4,20,90,22] [0x4dbc69a201048a05,0xa3]⟩,
  ⟨19,3,[ew64,ew65,ew66,ew230],lh 3 [91,90,4,20,146,22,5,23] [0x22a93a90d0120203,0x197]⟩,
  ⟨19,3,[ew64,ew65,ew66,ew231],lh 3 [91,90,4,20,146,21,22,5] [0x22b13a90d0120203,0x1d5]⟩,
  ⟨19,3,[ew64,ew65,ew232,ew66],lh 3 [91,90,4,20,146,21,5,23] [0x23a92b91200d0203,0xb5]⟩,
  ⟨19,3,[ew64,ew197,ew66,ew198],lh 3 [152,90,5,21,91,146,97,157] [0x167969a206168804,0x2]⟩,
  ⟨19,3,[ew64,ew65,ew233,ew67],lh 3 [21,154,22,152,97,4,5] [0x528d08685962089a,0x40]⟩,
  ⟨19,3,[ew64,ew65,ew234,ew67],lh 3 [21,22,152,97,90,157,4,154] [0x6a4c044693418651,0x1c0]⟩,
  ⟨19,3,[ew64,ew65,ew235,ew67],lh 3 [20,21,22,152,97,90,5,23] [0x6e9528d804601098,0x189]⟩,
  ⟨19,3,[ew64,ew236,ew65,ew67],lh 3 [5,20,21,152,97,23,90,157] [0x609009084c2d9081,0x17d]⟩,
  ⟨19,3,[ew64,ew65,ew201,ew202],lh 3 [160,90,22,20,91,4,21,154] [0x53512b1804603088,0x7]⟩,
  ⟨19,3,[ew64,ew237,ew66,ew67],lh 3 [160,91,90,4,21,5,22,154] [0x34f2562201201048,0x1dc]⟩,
  ⟨19,3,[ew64,ew238,ew66,ew67],lh 3 [160,91,90,4,21,5,22] [0x34f2562201201048,0x15c]⟩,
  ⟨19,3,[ew64,ew239,ew66,ew67],lh 3 [160,91,90,21,5,22,4] [0x45aa51a201201048,0x11b]⟩
]
def nodesBlock6 : Array Node := #[
  ⟨19,3,[ew64,ew240,ew66,ew67],lh 3 [160,91,90,4,22,5,23] [0x34e2562201201048,0x15e]⟩,
  ⟨23,5,[ew80,ew81,ew82,ew83],lh 5 [7,167,25,5,6,33,0,2,39,1,168,169,170,171,63,172,173,174,175,176,177,178,179,180,181,182] [0x882008a200484,0x401008c6004a5,0x86300802004c1,0x8020046100401,0x69104610cb51505,0x92469890f0794ce,0xb1863a94749a4e7,0xc98e7c2063ba0e7]⟩,
  ⟨23,4,[ew80,ew241,ew81,ew82,ew83],lh 4 [167,33,39,5,25,177,186,183,7,6,0,184,185,169] [0x4003420214100870,0x3553112dc3b3a291,0x662]⟩,
  ⟨23,4,[ew80,ew81,ew82,ew242,ew83],lh 4 [167,2,25,6,5,0,39,7,187,169,33,188,189] [0x2101800720050220,0xb1414663143a3539,0x1c1]⟩,
  ⟨23,4,[ew243,ew80,ew81,ew82,ew83],lh 4 [2,6,167,25,39,5,33,0,63,186] [0x2131505074613232,0x5105181430203424,0x90]⟩,
  ⟨23,4,[ew244,ew80,ew81,ew82,ew83],lh 4 [25,167,2,5,0,6,39,33,63,173,177] [0x7001232366551010,0x4a29284702100110,0x432]⟩,
  ⟨23,4,[ew80,ew245,ew81,ew82,ew83],lh 5 [25,0,2,33,6,191,192,193,5,186,190,7,1,194,195,63,173] [0x4c62940402d40,0x421c168584008e7,0x252208c501bc23]⟩,
  ⟨23,4,[ew80,ew81,ew82,ew83,ew246],lh 4 [0,5,167,1,25,39,192,33,196,7,197,173,198,199,2] [0xa229422140668343,0xc01517713b0505,0xe1d]⟩,
  ⟨23,4,[ew247,ew80,ew81,ew82,ew83],lh 4 [25,167,0,2,39,33,5,1,177] [0x1001632424550101,0x2873242403130210,0x343]⟩,
  ⟨23,4,[ew248,ew80,ew81,ew82,ew83],lh 4 [25,167,0,39,5,33,2,1,177] [0x1001663232751010,0x4845232304100210,0x243]⟩,
  ⟨23,4,[ew80,ew81,ew249,ew82,ew83],lh 4 [33,25,200,167,0,1,5,2,39,201] [0x1631143113310505,0x7784022002200220,0x469]⟩,
  ⟨23,4,[ew80,ew81,ew82,ew83,ew250],lh 4 [200,33,25,2,39,1,167,192,193,201,0,5] [0x2662238324720505,0x4349100110011001,0xb3a]⟩,
  ⟨23,4,[ew251,ew80,ew81,ew82,ew83],lh 4 [6,25,167,5,200,39,0,202,7,2,33,186] [0x2010936604048172,0x430a00513211521,0xb53]⟩,
  ⟨23,4,[ew252,ew80,ew81,ew82,ew83],lh 4 [1,25,6,2,0,167,203,7,39,5,186] [0x5010938402027161,0x2003022013531451,0xa34]⟩,
  ⟨23,3,[ew81,ew253,ew82,ew83],lh 4 [39,167,33,5,25,177,169,0,186] [0x7010553220604221,0x80034113]⟩,
  ⟨23,3,[ew80,ew81,ew82,ew254],lh 3 [167,33,39,25,5,169,177,186] [0x4da12ad6046822c8,0x1fa]⟩
]
def nodesBlock7 : Array Node := #[
  ⟨23,3,[ew255,ew80,ew81,ew82],lh 3 [167,33,39,5,25,177,186,169] [0x7882308d93b59103,0x57]⟩,
  ⟨23,3,[ew256,ew81,ew82,ew83],lh 4 [33,167,5,25,39,169,204,2,6] [0x855211344131030,0x72726620]⟩,
  ⟨23,3,[ew80,ew81,ew82,ew257],lh 4 [6,2,33,167,25,5,0,169,186] [0x2007413143362020,0x18150150]⟩,
  ⟨23,3,[ew258,ew80,ew81,ew82],lh 3 [6,2,186,25,167,177,5,204] [0x26a2e18c4a141319,0x140]⟩,
  ⟨23,3,[ew81,ew259,ew82,ew83],lh 4 [0,25,6,191,173,2,5,169,63,192,193,186] [0x1090254408073312,0xb5066a1]⟩,
  ⟨23,3,[ew80,ew81,ew260,ew83],lh 4 [33,25,0,2,191,192,193,5,6,1,173] [0x920136612554418,0x773203a0]⟩,
  ⟨23,3,[ew261,ew80,ew81,ew83],lh 4 [33,1,0,5,192,25,193,63,2] [0x101238370202544,0x1105366]⟩,
  ⟨23,3,[ew262,ew81,ew82,ew83],lh 4 [167,33,25,0,205,1,39,196,192,193,5] [0x4431900280020170,0x366a1551]⟩,
  ⟨23,3,[ew80,ew81,ew263,ew83],lh 4 [0,5,167,25,39,33,196,173,1] [0x404312330202652,0x1411817]⟩,
  ⟨23,3,[ew264,ew80,ew81,ew83],lh 3 [25,5,0,167,39,205,173,186] [0x6058a0330a8940c2,0x79]⟩,
  ⟨23,3,[ew80,ew81,ew249,ew250],lh 3 [200,33,2,25,1,167,5,186] [0x22012017ab6aa104,0x7]⟩,
  ⟨23,3,[ew265,ew81,ew82,ew83],lh 4 [5,167,39,200,0,33,1,25,186] [0x5232701044121631,0x80200305]⟩,
  ⟨23,3,[ew266,ew81,ew82,ew83],lh 4 [2,6,25,0,167,39,33,200,186] [0x3116204023524121,0x8031070]⟩,
  ⟨30,7,[ew105,ew106,ew107,ew108,ew109],lh 5 [23,207,210,35,215,18,4,212,208,0,211,28,27,58,6,217,218,29,40,15,219,206,14,17,209,11,213,214,216,48] [0x4456b446510d56b,0xd1f275098cc5652,0x9ec750b6209c67,0x9c8408ac208882,0x9ee769c0008ae2,0x44c63515c568802,0xbd294147de4dd3,0x43c848152541485,0xa3cc643c00694c5,0x8392950c8341405,0x50c0308d2353884,0x68cc653000a30c6,0xa10c6810000a4c6,0x82400]⟩,
  ⟨30,6,[ew267,ew106,ew107,ew108,ew105,ew109],lh 5 [40,206,4,6,0,35,222,14,208,17,27,215,23,207,212,58,11,28,211,210,224,220,221,223] [0xa94b25290d8a011,0x69ced212452d94a,0x422680cda73b484,0x7a52f109e94bc42,0x314c01800529863,0x1c06218c730080,0x80845c0803421,0x29ca0480c231926,0x1d0652146718c83,0x1a4630861484021,0x2388310d4952842,0x208440856e5ac21,0x8827631625ad8b,0x1631c27398c]⟩,
  ⟨30,6,[ew106,ew107,ew108,ew105,ew268,ew109],lh 5 [18,23,11,215,14,17,40,206,211,212,0,207,15,4,208,58,28,200,214,222,227,225,226,228,221,229,6,210] [0x84ca98c214d13,0x61180500040314c,0x5006398d4b00e0,0x3806c18ce302e0,0x4106c201081a0,0x129511c62a50863,0x1384b39c4812119,0x916526b44112d1a,0x1a46339c89209a2,0x1ac6358c8b210e4,0x1946308c8521164,0x394a846d2e49021,0x794a7085254a421,0xf085e52bc21]⟩
]
def nodesBlock8 : Array Node := #[
  ⟨30,6,[ew93,ew106,ew107,ew108,ew105,ew109],lh 5 [0,6,210,215,23,17,231,208,4,27,40,206,15,29,207,212,14,211,217,218,58,219,18,35,230,221,48,225] [0x39ee7084f1b1d8c,0x70c73002631b800,0x708597bf02139ef,0xa1095422a425108,0x501473e94754421,0x62d8a828c031863,0x320cc108cb59846,0x4c20629648948a5,0x88290243008400,0x94215862216d6b,0x3401405254a509,0x14001006d18c42,0x114a02106518c83,0x2211a56b484]⟩,
  ⟨30,5,[ew106,ew107,ew269,ew108,ew105,ew109],lh 4 [222,15,35,23,215,4,0,206,232,210,27,208] [0x1001100101100120,0x5288722462a21001,0x4653537b99646423,0x3537343574]⟩,
  ⟨30,5,[ew270,ew106,ew107,ew108,ew105,ew109],lh 4 [15,14,4,23,17,222,0,215,206,35,210,11,28,27] [0x54343aa171799c0,0x6145400858151050,0x326776242b8b8d61,0x323262]⟩,
  ⟨30,5,[ew93,ew106,ew108,ew105,ew268,ew109],lh 5 [11,0,4,14,23,15,212,27,215,210,6,222,229,208,233,223,48,17] [0x1d800180118160,0x7186118402201a0,0x404a22160529de6,0x4a4222086108c28,0x5444a20882]⟩,
  ⟨30,5,[ew271,ew106,ew107,ew108,ew105,ew109],lh 4 [215,23,0,6,11,4,206,18,40,14,17,85,227,210,234] [0x1ad6c60909434388,0x1776e6020243471a,0x2515334432020bb,0x1515251520]⟩,
  ⟨30,5,[ew106,ew107,ew108,ew105,ew272,ew109],lh 4 [0,4,15,6,23,11,215,40,210,214,212] [0x2772278220609223,0x3553355303067147,0x141066006805415,0x41418141a8]⟩,
  ⟨33,7,[ew120,ew121,ew122,ew123,ew124],lh 5 [235,236,215,154,18,0,57,6,15,35,237,238,239,32,240,58,31,33,49,59,14,13,25,241,242] [0x6010051603610,0x352d0062103508,0x284a0052903631,0x2a8a0044200681,0x286302aaa00461,0x62129590e4006a1,0x720a861124720e7,0x62042710a561044,0x748d264863710c4,0xb9ca55a44261064,0x79c67c24a559c47,0x79cc65cc735ccc6,0x588c658863794c6,0x79465]⟩,
  ⟨34,6,[ew125,ew126,ew127,ew128,ew129],lh 5 [7,18,207,6,0,4,2,5,1,39,15,14,49,35,17,27,51,8,243,84,86,87] [0x2863029aa00461,0x5610288a005a1,0x4e10296b00484,0x401030ec03013,0x30a5031cc004a1,0x10c841356b005c1,0x10cc31348410d63,0x10ce3120c8120e7,0x3dcf03ca5021c8,0x124c6110e4020a8,0x24a9110c6124e9,0x2409040b004054,0x48b204a35018a6,0x1a31]⟩,
  ⟨36,6,[ew135,ew136,ew137,ew138,ew139],lh 5 [207,37,244,1,28,5,4,242,40,33,31,35,17,27,15,8,251,253,87,25,245,246,247,248,249,250,84,252] [0x942009d30054a,0x56100922005ce,0x8020096b00521,0x8a200401004a1,0x802008c200401,0xb2975a1063004c1,0x10a4c9138ba863,0x1004020a8020fa,0x810c4391843a0c8,0xca50240982188,0x88d83024bb00ce3,0x38cc33b58d8b4cd,0xc601df2014d2,0x15ef]⟩,
  ⟨36,5,[ew135,ew273,ew136,ew137,ew138,ew139],lh 5 [5,17,37,28,1,4,244,27,207,242,254,15,35,253,246,84,87] [0x208861986212902,0x611630982200806,0xc8e6852140120,0x9c80384a128c0f,0xb0294e7]⟩,
  ⟨36,5,[ew135,ew136,ew137,ew274,ew138,ew139],lh 5 [31,33,5,4,37,207,244,17,87,25,255,256,257,258,246,28,259,1,252,242,251,253] [0x2908d6056150120,0x40e1986411046,0xc42019c001400f,0xa0a62284e308642,0x86840ea3]⟩,
  ⟨36,5,[ew275,ew135,ew136,ew137,ew138,ew139],lh 4 [37,244,4,5,17,31,27,1,28,33,242,207,249,259,87] [0x4242b3a397881010,0x110100110010110,0x46736424553d5c57,0x32e2266]⟩,
  ⟨36,5,[ew276,ew135,ew136,ew137,ew138,ew139],lh 4 [244,37,5,4,28,17,33,27,252,87,31,207,242,249,84] [0x35352c2b77a41010,0x3031212001101001,0x68826544342e2d64,0x2399653]⟩,
  ⟨36,4,[ew277,ew136,ew137,ew138,ew139],lh 4 [28,1,37,244,31,17,5,33,35,259,260,87] [0x2332322312180302,0x7117400406900140,0x65b515a1]⟩,
  ⟨36,4,[ew278,ew136,ew137,ew138,ew139],lh 4 [4,5,31,17,244,25,255,256,257,261,37,246,33,252,259,87] [0xa44a991488776655,0xdd1c303221e2c2bb,0x10f00303]⟩,
  ⟨38,6,[ew128,ew111,ew144,ew142,ew124],lh 5 [12,9,49,215,242,11,23,39,37,231,200,40,8,1,237,59,167,262,263] [0x561004500216b,0x21a8004a102042,0x22068005a1020a5,0x220e720463204e1,0x238ce2398c204c1,0x2ca5009a220581,0x8e2008a502dab,0x863024e902463,0x802008c602409,0x281101463024c9,0x28ca014050286a,0x280a03ccf03c12,0x20d8c20cc621d87,0x21cc7]⟩
]
def nodesBlock9 : Array Node := #[
  ⟨41,9,[ew154,ew155,ew156,ew157,ew158,ew159],lh 6 [51,23,236,31,37,33,266,243,268,27,270,271,6,17,2,21,18,5,273,14,4,32,274,215,244,40,0,1,264,15,272,28,281,283,39,284,265,25,267,255,269,257,35,275,276,277,249,278,259,279,280,169,173,282,86] [0xc218276590471c,0x202145195767982,0xaa9a15145195255,0x1820022845c4182,0x3c21840042c25d7,0x4843cf7841c4782,0x34d5840441821c2,0x182342ad8058198,0x30cb03145210249,0x28300021016eb43,0x4d32d00102d04d0,0x4993f0bc31c3283,0x503c433cf4991d9,0x81f514c9f041583,0x6b3209000803041,0x28969a20c00c2cc,0x1db49b47420c1cc,0x845041d4c45121b,0x505209041849509,0x2c0380293451585,0x3762d338e280440,0x2803402c00402a2,0x4158e34e2e2041,0x8ce04e8c7347487]⟩,
  ⟨41,8,[ew125,ew154,ew155,ew156,ew157,ew158,ew159],lh 6 [285,23,31,33,37,289,222,290,32,4,1,51,243,5,7,17,215,0,21,6,207,291,2,39,235,287,14,294,273,293,27,28,35,271,272,292,244,264,286,288,25,295,86] [0x95f00e024000104,0x28a01801f000,0x6590000c3026820,0x16169a0002cb027,0x30c01469a1612cb,0x1dc30c1dc01c000,0x3cf000041022022,0x3cf000041000,0x8000082000028,0x6086483950c3008,0x4046156553880c8,0x1554101552d5384,0x3048c84886042c4,0x6083081c44928c4,0x5d01d3cf004044,0x6c64d30043cf01d,0xc66c24d33820c3,0x1464066c2442386,0x342382402146451,0x1c634d1c64866c2,0x46002242382482,0x2042006249006,0x413153451503410,0x503483503443153,0x3431ca48a1ca34d,0x1e24900a04a503,0x34d00a24a01e05e,0x1d73571575a9511,0x6a017257151596,0x15704100b24b14b,0x24c1cc041016256,0x1d604100c]⟩,
  ⟨41,8,[ew279,ew154,ew155,ew156,ew157,ew158,ew159],lh 6 [266,31,21,6,7,23,33,4,5,285,222,297,244,0,208,298,236,14,51,215,9,1,39,207,296,272,243,17,27,288,12,271,273,32,15,255,235] [0x41000261619410,0x39d186000022619,0xc339e1861040c3,0x2df49239745111d,0x821044922df451,0x3e00823e069a619,0x1c724914511969a,0x2491c73846db104,0x23010010009041,0xc3010186000,0x4cc0100c301e186,0x104d301045100c,0x20860c08c00c44c,0xc208014094614,0x14500c6cc014154,0x10a0c30146d400c,0x1861010c1381186,0x2ca4ca10134138a,0x2013814c12ca34d,0x3ca20a3ca08a101,0x14a2411c1381082,0x24114110a1c738a,0x4c32c334d5c64c6,0x5c30825c634d2c3,0x2033d50953d5208,0x11c1c72551555c3,0x20d2551d511c15c,0x3d62162d60825cd,0x1452561d62cd082,0x2d61561121d22d2,0x1c73c21452481c8,0x3c8145902]⟩,
  ⟨41,8,[ew130,ew154,ew155,ew156,ew157,ew158,ew159],lh 6 [266,268,2,23,0,17,18,31,32,37,33,5,215,7,302,21,51,303,40,11,300,301,306,39,299,4,272,15,285,12,207,293,28,307,243,236,271,273,238,305,27,257,304,169,173,86,308,235] [0x6db00006361a223,0x51d6db55d18651c,0x2861a28a54d186,0x3a441051e104000,0x2cb55e4103a4104,0x4652cb46508261a,0x14551c0c355a082,0x55c1455260c3566,0x1c70001860081c8,0x128a00818601d,0x309000029008008,0x830c008104009,0x896083c8009109,0x80820093cf609,0xdf01f1450090c9,0x4604600914901f,0x28a047347047287,0x38630c347107046,0x8750730c386104,0x4520924523cf347,0xc3352652a873cf,0x9d20d29e0660360,0x31605612b04a30a,0x563d604a104056,0x2cb0530930532ec,0x61659053153056,0x2cb053653061161,0x4572d7397082784,0xed357157384082,0x3970c3b90150390,0x1624620c3342145,0x4420c3be2]⟩,
  ⟨41,8,[ew145,ew154,ew155,ew156,ew157,ew158,ew159],lh 6 [266,31,33,5,23,274,7,312,14,293,311,35,215,2,313,21,15,314,315,18,1,39,244,0,40,309,237,6,272,285,28,27,51,243,310,268,238,270,271,273,17,37,316,207,260,235] [0x4100016965c596,0x88604175d41075d,0x2cb2a3082186410,0x2a32cb8a4082186,0x30c3a62081e530c,0x65c3cf1e52083a6,0xc34673cf4670c3,0x2865c12819c,0x41016410009041,0x16082009409016,0x2cb0090890092c9,0x12208009309016,0x3d2009209012312,0x1a3da65a0c3652,0x1a0051040120d2,0x2936d300002a01a,0x2d31816c11812cb,0x3933131c15c1293,0xc11c13013935d7,0x4580d84583cf181,0x11e1581581813c1,0x15810415e19e15e,0x21b39b5d728230c,0x2823421c25c229b,0xc22943544540c3,0x15f92c294114ac2,0xc815415429f11f,0x1d50d539534d1c8,0x1041d51d538834d,0x3951151e01e03a0,0xb6146110414d14d,0x44d10d161]⟩,
  ⟨41,8,[ew154,ew155,ew156,ew280,ew157,ew158,ew159],lh 6 [268,236,17,31,317,37,5,2,39,33,319,320,23,14,12,322,324,40,306,11,7,208,215,21,323,0,32,51,243,4,291,321,15,35,244,264,307,274,266,272,270,271,207,273,283,318,246,18,6,86,288] [0xc310180151a0c3,0x124111a820541,0x86101a24911a85a,0x10198139eb5e101,0x58511e99e541381,0x2c15961016c1285,0x7057c15c11056c5,0x1017013c55d77c5,0x322122082605305,0x2e105085522,0x9c3000249003503,0x28364300002f7c3,0x5832d06502d0596,0x3d15d7510190283,0x7515505d03d1191,0x523763563082611,0x307c99c9611091,0x12659009349014,0x1d2009659012352,0x131d3013186012,0x75d013093012192,0x137530240a4024,0x2082e934d2a8208,0x3aa1c72a834d2e9,0x1863eb1c73eb186,0x54e0826253a556a,0x18d6250823ac3ac,0x2881882c81c828d,0x3312880882cd1c7,0x2c830c29b09b2db,0x9c3dc30c607082,0x3c730cc9c]⟩,
  ⟨41,8,[ew131,ew154,ew155,ew156,ew157,ew158,ew159],lh 6 [268,6,23,236,4,7,37,325,32,21,215,327,328,243,2,15,51,14,329,0,324,5,40,330,1,17,39,294,31,326,331,244,264,27,266,272,307,270,271,273,274,283,285,18,207,249,86,288] [0x2081e20c36ea208,0x76371c1450c31e2,0x16476306400002b,0x3264512e5410000,0x34d2e5451326410,0x4a734d4a72496c5,0x825e810416c249,0x5e80827a9104169,0x7031c33c36c8708,0x30031c83cf143,0x410081481c8041,0x1c34512c62861c3,0x2491c644630328a,0x486246746346743,0x1045c60861c3343,0x1c610615f09f1df,0x2d00f14f000041,0x31428a2cf4cf000,0x5542cf28a3144d4,0x4965564962496d4,0x825d6116154254,0x5d60966e0120160,0x2810014d301828a,0x13810184d8001,0x54101838e018558,0x7a1104781081001,0x555001104021661,0x2da55a31a38e2d3,0xae2da65a31338e,0x31a0822d0650310,0x64d48d0825ce659,0x48e082bcd]⟩,
  ⟨41,8,[ew154,ew111,ew155,ew156,ew157,ew158,ew159],lh 6 [273,31,17,32,23,5,7,9,333,37,14,334,335,336,11,18,215,6,35,0,1,332,337,2,39,243,4,236,272,294,244,28,27,51,266,33,268,338,270,271,274,339,40,12,21,235,259,86] [0x70720788755b71b,0x74304121b89b187,0x3c31870472073c7,0x2034832c78c7203,0x4092074921838c3,0x343410203283309,0x649543543209289,0x203643009009549,0x11e21e082589109,0x55c04120908219e,0x38e2e449200002a,0x2e438e9464921ab,0x28a36741032628a,0x55c145326410367,0x1045a80820001ac,0x5a810496d082186,0x44118138e2cf44f,0x3014c12cf38f741,0x40134f4d334f40f,0x14500002e301,0x82581681001181,0x58108175f69f19f,0x28a3514d32ce28e,0x2d15d130e4d32d1,0x1512d45d4014145,0xa6069aa54094011,0x1455946942e00a0,0x3181583585d730a,0x12f31809834a5d7,0x3581043210a1361,0x99019104005085,0x5104019]⟩,
  ⟨41,8,[ew154,ew155,ew156,ew157,ew158,ew159,ew281],lh 6 [5,274,37,17,236,340,14,23,1,33,341,342,343,39,264,7,51,32,345,244,346,49,27,243,28,35,21,2,6,0,344,349,285,215,347,208,266,272,268,283,270,271,279,273,310,348,31,173,58,260,4] [0x384144618811391,0x2842441516118c4,0x6593d1249151651,0x1441842c2842144,0x684142186304861,0x48269a782002784,0xc30421c2144000,0x1420c30531d3153,0x3d3153913802802,0x29871c142902b13,0x6583ce70e8ce659,0x3141862ce74e298,0x142ce18e314754,0x89501549569a3d4,0x3d504106d894694,0x7959550410c3055,0x75d28918904106e,0x2c974929c18631c,0x6c848802f2896c9,0x7c80c8c09000288,0x482960d67d67f1,0x7d69d6288988048,0x3c89c8296996,0x2cd00d30d6db2c6,0x1d02cd0cd3066db,0x30d1c72d00d0310,0xa10310a502cda0d,0x400c330da4d2d0,0x1c70570d74971c7,0x497ad73c0a80480,0x947480ac0897a97,0x4f072787]⟩,
  ⟨41,8,[ew133,ew154,ew155,ew156,ew157,ew158,ew159],lh 6 [268,31,5,39,273,17,37,23,351,354,33,291,0,353,32,49,207,6,8,215,18,40,236,350,35,4,272,352,355,14,356,244,28,27,51,266,7,279,1,270,271,274,283,357,338,2,256,259,58,177,86,288] [0x5962232cb5da596,0xb2404141a2cb223,0x3cf6e50414253cf,0x1265da466424,0x30c2680c336730c,0x5da0823670c3268,0x49272914500002d,0x7294927aa14542a,0x412163cf40b04b,0xb28b20b3cf416,0x61800e28e20e62e,0x20e0ce3464c620b,0x5ce2060c624e4d3,0x1061065c60865ce,0x4927061c620e082,0x20648641f1df21f,0x451001618014454,0x341301014614001,0x4c125430c2544d4,0x11512f101081341,0x6556c16c16d5095,0xae0660c201c7715,0x30c00a4d3ad51d5,0xa30a011751011,0x3100408200a00a,0x7a165978a14a000,0x8200a64a021161,0x34308324324335d,0x1f234314325d25d,0x2431c7362162262,0x1451041c7102145,0x1021c7133]⟩,
  ⟨41,7,[ew154,ew155,ew156,ew282,ew157,ew158,ew159],lh 6 [31,17,5,222,23,35,32,14,37,285,2,39,291,0,287,4,215,21,264,235,15,293,51,243,256,7,300,246,294,288,358,359,271,25,33,211,208,360,338] [0x509492254848492,0x68618560c658194,0x19318c64c305306,0x308408313306686,0x44620720c410307,0x182188451202206,0x55115541048108,0x7000056c371b201,0x1d0034c30c5140,0xc03400dd0c04c0,0x8001000334d0d0,0x110030820d10c0,0x33cf0c10c03c0,0x1c5249885245001,0x14d35e1c778d345,0x8e28e382085285,0x4124f3ce04e142,0x8071df2cb38f389,0xa328a7c71e02cb,0x1049820a528a902,0x241049104241049,0x28b08b2ca2c7087,0x5658410b04b1ca,0x5c410a0412c4116,0x284117057]⟩,
  ⟨41,7,[ew283,ew154,ew155,ew156,ew157,ew158,ew159],lh 6 [31,17,291,5,23,222,33,35,215,14,0,317,15,51,243,21,11,2,4,306,39,266,272,361,364,307,270,271,273,274,310,246,32,300,268,208,362,363,7,173,86] [0x3150002e1816082,0x18654c3220002cc,0x5471d71862c71d5,0x25b34d6c925a34d,0x38e7030d638e689,0x78105d1045830dc,0x30200274105e104,0x18208c0a30002cc,0x870971862c71c2,0x242208089264208,0x3cf0830e53cf2c9,0x6010421042c30c2,0x7c55df081058118,0x280147140980007,0x800528a148140,0x50c514f1400c0,0x49214114048000f,0x4ca286208001005,0x9d33d318a193213,0x504c30d0450403,0x412419059652490,0x4540d451144a0c3,0x4d344a14054291,0x38411104150410d,0x44410e04e]⟩
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
def fastViews : QFast.Table View := ⟨42,viewsGet⟩
def fastNodes : QFast.Table Node := ⟨156,nodesGet⟩
end SignedProjection

namespace SignedProjection
end SignedProjection

namespace SignedProjection
def aliasMap0 : Array Nat := #[0,1,0,0,0,3,0,0,0,5,0,0,0,7,0,0,0,33,0,0,0,35,0,0,0,37,0,0,0,39,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
def aliasMap1 : Array Nat := #[0,1,0,0,0,3,0,0,0,5,0,0,0,7,0,0,0,9,0,0,0,11,0,0,0,13,0,0,0,15,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
def aliasMap2 : Array Nat := #[0,18,0,0,0,19,0,0,0,26,0,0,0,27,0,0,0,50,0,0,0,51,0,0,0,58,0,0,0,59,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
def aliasMap3 : Array Nat := #[0,48,0,0,0,49,0,0,0,50,0,0,0,51,0,0,0,56,0,0,0,57,0,0,0,58,0,0,0,59,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
def aliasMap4 : Array Nat := #[0,48,0,0,0,49,0,0,0,50,0,0,0,51,0,0,0,52,0,0,0,53,0,0,0,54,0,0,0,55,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
def aliasMap5 : Array Nat := #[0,8,0,0,0,9,0,0,0,10,0,0,0,11,0,0,0,12,0,0,0,13,0,0,0,14,0,0,0,15,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
def aliasMap6 : Array Nat := #[0,55,0,0,0,51,0,0,0,38,0,0,0,34,0,0,0,53,0,0,0,49,0,0,0,36,0,0,0,32,0,0,0,23,0,0,0,19,0,0,0,6,0,0,0,2,0,0,0,21,0,0,0,17,0,0,0,4,0,0,0,0,0,0]
def aliasMap7 : Array Nat := #[0,47,0,0,0,37,0,0,0,46,0,0,0,36,0,0,0,43,0,0,0,33,0,0,0,42,0,0,0,32,0,0,0,15,0,0,0,5,0,0,0,14,0,0,0,4,0,0,0,11,0,0,0,1,0,0,0,10,0,0,0,0,0,0]
def aliasMap8 : Array Nat := #[0,16,0,0,0,26,0,0,0,17,0,0,0,27,0,0,0,20,0,0,0,30,0,0,0,21,0,0,0,31,0,0,0,48,0,0,0,58,0,0,0,49,0,0,0,59,0,0,0,52,0,0,0,62,0,0,0,53,0,0,0,63,0,0]
def aliasMap9 : Array Nat := #[0,55,0,0,0,21,0,0,0,54,0,0,0,20,0,0,0,51,0,0,0,17,0,0,0,50,0,0,0,16,0,0,0,39,0,0,0,5,0,0,0,38,0,0,0,4,0,0,0,35,0,0,0,1,0,0,0,34,0,0,0,0,0,0]
def aliasMap10 : Array Nat := #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,61,57,0,0,60,56,0,0,21,17,0,0,20,16,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,45,41,0,0,44,40,0,0,5,1,0,0,4,0]
def aliasMap11 : Array Nat := #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,61,57,0,0,60,56,0,0,53,49,0,0,52,48,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,13,9,0,0,12,8,0,0,5,1,0,0,4,0]
def aliasMap12 : Array Nat := #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,2,3,0,0,6,7,0,0,10,11,0,0,14,15,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,50,51,0,0,54,55,0,0,58,59,0,0,62,63]
def aliasMap13 : Array Nat := #[0,59,0,58,0,57,0,56,0,51,0,50,0,49,0,48,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,11,0,10,0,9,0,8,0,3,0,2,0,1,0,0]
def aliasMap14 : Array Nat := #[0,0,0,0,0,5,0,0,0,0,18,0,0,0,0,23,8,0,0,0,0,13,0,0,0,0,26,0,0,0,0,31,32,0,0,0,0,37,0,0,0,0,50,0,0,0,0,55,40,0,0,0,0,45,0,0,0,0,58,0,0,0,0,63]
def aliasMap15 : Array Nat := #[0,0,0,0,0,5,0,0,0,0,34,0,0,0,0,39,8,0,0,0,0,13,0,0,0,0,42,0,0,0,0,47,16,0,0,0,0,21,0,0,0,0,50,0,0,0,0,55,24,0,0,0,0,29,0,0,0,0,58,0,0,0,0,63]
def aliasMap16 : Array Nat := #[0,0,0,0,0,5,0,0,0,0,2,0,0,0,0,7,40,0,0,0,0,45,0,0,0,0,42,0,0,0,0,47,16,0,0,0,0,21,0,0,0,0,18,0,0,0,0,23,56,0,0,0,0,61,0,0,0,0,58,0,0,0,0,63]
def aliasMap17 : Array Nat := #[0,40,0,0,0,42,0,0,0,33,0,0,0,35,0,0,0,44,0,0,0,46,0,0,0,37,0,0,0,39,0,0,0,56,0,0,0,58,0,0,0,49,0,0,0,51,0,0,0,60,0,0,0,62,0,0,0,53,0,0,0,55,0,0]
def aliasMap18 : Array Nat := #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,18,3,0,0,22,7,0,0,26,11,0,0,30,15,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,50,35,0,0,54,39,0,0,58,43,0,0,62,47]
def aliasMap19 : Array Nat := #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,43,58,0,0,41,56,0,0,35,50,0,0,33,48,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,11,26,0,0,9,24,0,0,3,18,0,0,1,16]
def aliasMap20 : Array Nat := #[0,24,0,0,0,26,0,0,0,9,0,0,0,11,0,0,0,28,0,0,0,30,0,0,0,13,0,0,0,15,0,0,0,56,0,0,0,58,0,0,0,41,0,0,0,43,0,0,0,60,0,0,0,62,0,0,0,45,0,0,0,47,0,0]
def aliasMap21 : Array Nat := #[0,48,0,0,0,50,0,0,0,33,0,0,0,35,0,0,0,52,0,0,0,54,0,0,0,37,0,0,0,39,0,0,0,56,0,0,0,58,0,0,0,41,0,0,0,43,0,0,0,60,0,0,0,62,0,0,0,45,0,0,0,47,0,0]
def aliasMap22 : Array Nat := #[0,23,0,0,0,21,0,0,0,22,0,0,0,20,0,0,0,51,0,0,0,49,0,0,0,50,0,0,0,48,0,0,0,7,0,0,0,5,0,0,0,6,0,0,0,4,0,0,0,35,0,0,0,33,0,0,0,34,0,0,0,32,0,0]
def aliasMap23 : Array Nat := #[0,1,0,19,0,5,0,23,0,9,0,27,0,13,0,31,0,0,18,0,4,0,22,0,8,0,26,0,12,0,30,0,0,33,0,51,0,37,0,55,0,41,0,59,0,45,0,63,32,0,50,0,36,0,54,0,40,0,58,0,44,0,62,0]
def aliasMap24 : Array Nat := #[0,59,0,25,0,58,0,24,0,51,0,17,0,50,0,16,63,0,29,0,62,0,28,0,55,0,21,0,54,0,20,0,0,43,0,9,0,42,0,8,0,35,0,1,0,34,0,0,47,0,13,0,46,0,12,0,39,0,5,0,38,0,4,0]
def aliasMap25 : Array Nat := #[0,59,0,57,0,58,0,56,0,51,0,49,0,50,0,48,0,27,0,25,0,26,0,24,0,19,0,17,0,18,0,16,0,43,0,41,0,42,0,40,0,35,0,33,0,34,0,32,0,11,0,9,0,10,0,8,0,3,0,1,0,2,0,0]
def aliasMap26 : Array Nat := #[63,59,61,57,62,58,60,56,0,0,0,0,0,0,0,0,31,27,29,25,30,26,28,24,0,0,0,0,0,0,0,0,47,43,45,41,46,42,44,40,0,0,0,0,0,0,0,0,15,11,13,9,14,10,12,8,0,0,0,0,0,0,0,0]
def aliasMap27 : Array Nat := #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,31,27,29,25,30,26,28,24,23,19,21,17,22,18,20,16,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,15,11,13,9,14,10,12,8,7,3,5,1,6,2,4,0]
def aliasMap28 : Array Nat := #[0,59,0,57,0,58,0,56,0,51,0,49,0,50,0,48,31,0,29,0,30,0,28,0,23,0,21,0,22,0,20,0,0,43,0,41,0,42,0,40,0,35,0,33,0,34,0,32,15,0,13,0,14,0,12,0,7,0,5,0,6,0,4,0]
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
  | 11 => some (7, aliasMap9)
  | 13 => some (12, aliasMap10)
  | 15 => some (12, aliasMap11)
  | 16 => some (12, aliasMap12)
  | 17 => some (14, aliasMap13)
  | 20 => some (19, aliasMap14)
  | 21 => some (19, aliasMap15)
  | 22 => some (19, aliasMap16)
  | 24 => some (7, aliasMap17)
  | 25 => some (12, aliasMap18)
  | 26 => some (12, aliasMap19)
  | 27 => some (7, aliasMap20)
  | 28 => some (7, aliasMap21)
  | 29 => some (7, aliasMap22)
  | 31 => some (30, aliasMap23)
  | 32 => some (30, aliasMap24)
  | 35 => some (34, aliasMap25)
  | 37 => some (36, aliasMap26)
  | 39 => some (38, aliasMap27)
  | 40 => some (30, aliasMap28)
  | _ => none
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockRoots_0 : QFast.passBlock (QFast.symCheckRoot rootAliases fastViews fastNodes) 0 26 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockRoots_26 : QFast.passBlock (QFast.symCheckRoot rootAliases fastViews fastNodes) 26 15 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockRoots_41 : QFast.passBlock (QFast.symCheckRoot rootAliases fastViews fastNodes) 41 1 = true := by decide +kernel
theorem joinRoots_0_0 : QFast.passBlock (QFast.symCheckRoot rootAliases fastViews fastNodes) 0 41 = true :=
  @QFast.merge_blocks (QFast.symCheckRoot rootAliases fastViews fastNodes) 0 26 15 blockRoots_0 blockRoots_26
theorem joinRoots_1_0 : QFast.passBlock (QFast.symCheckRoot rootAliases fastViews fastNodes) 0 42 = true :=
  @QFast.merge_blocks (QFast.symCheckRoot rootAliases fastViews fastNodes) 0 41 1 joinRoots_0_0 blockRoots_41
theorem certifiedRoots : QFast.passBlock (QFast.symCheckRoot rootAliases fastViews fastNodes) 0 42 = true := joinRoots_1_0
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockNodes_0 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 0 64 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockNodes_64 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 64 64 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockNodes_128 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 128 19 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockNodes_147 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 147 7 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockNodes_154 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 154 2 = true := by decide +kernel
theorem joinNodes_0_0 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 0 128 = true :=
  @QFast.merge_blocks (QFast.checkNodeAt fastViews fastNodes) 0 64 64 blockNodes_0 blockNodes_64
theorem joinNodes_0_128 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 128 26 = true :=
  @QFast.merge_blocks (QFast.checkNodeAt fastViews fastNodes) 128 19 7 blockNodes_128 blockNodes_147
theorem joinNodes_1_0 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 0 154 = true :=
  @QFast.merge_blocks (QFast.checkNodeAt fastViews fastNodes) 0 128 26 joinNodes_0_0 joinNodes_0_128
theorem joinNodes_2_0 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 0 156 = true :=
  @QFast.merge_blocks (QFast.checkNodeAt fastViews fastNodes) 0 154 2 joinNodes_1_0 blockNodes_154
theorem certifiedNodes : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 0 156 = true := joinNodes_2_0
end SignedProjection

namespace SignedProjection
def bMatches (z : Option View) : Bool :=
  match z with
  | none => false
  | some v => vg v == (0xeee8e8e8eae0e8c0 : Word) && vk v == 9 && (vs v).toFinset == Direct64.cols.toFinset

theorem rootNegative : ¬ CoreSigned.build signedOps (0xeee8e8e8eae0e8c0 : BitVec 64) 9 Direct64.cols.toFinset := by
  have shape : bMatches (QFast.get fastViews 41) = true := by decide +kernel
  cases ev : QFast.get fastViews 41 with
  | none => simp [ev, bMatches] at shape
  | some v =>
    have valid := QFast.symCertified rootAliases fastViews fastNodes certifiedRoots certifiedNodes ev
    simp only [ev,bMatches,Bool.and_eq_true,beq_iff_eq] at shape
    change ¬ CoreSigned.build signedOps (vg v) (vk v) (vs v).toFinset at valid
    rwa [shape.1.1,shape.1.2,shape.2] at valid
end SignedProjection

end PEqualNP.Outside.L_meta_47046_aux

open PEqualNP.Outside.L_meta_47046_aux in
theorem PEqualNP.Outside.L_meta_47046 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4008241384 * 2 ^ 32 + 3940608192) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4008241384 * 2 ^ 32 + 3940608192) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  LowerSymSix.finish SignedProjection.rootNegative
