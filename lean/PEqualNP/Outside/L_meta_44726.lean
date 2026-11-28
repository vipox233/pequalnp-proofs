import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_44726_aux
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
  ⟨[⟨.and,[0,1]⟩, ⟨.or,[6,5]⟩, ⟨.and,[7,2]⟩, ⟨.or,[0,1]⟩, ⟨.or,[9,8]⟩,
    ⟨.and,[10,3]⟩, ⟨.and,[11,4]⟩, ⟨.or,[11,4]⟩, ⟨.and,[13,7]⟩, ⟨.or,[14,2]⟩,
    ⟨.and,[15,9]⟩, ⟨.or,[16,12]⟩],17⟩

theorem size : witness.size = 12 := rfl

theorem monotone : Monotone2 witness := by
  simp [Monotone2,witness]

set_option maxRecDepth 16000 in
theorem correct : ∀ x : Fin 6 → Bool, witness.eval (List.ofFn x) =
    Nat.testBit (4277071584 * 2 ^ 32 + 4008241376) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  decide +kernel

end LowerSymSix

namespace Direct64
open PEqualNP.CircuitLowerBounds SignedProjection
abbrev W := BitVec 64
abbrev basicOps (a b : W) := signedOps a b
abbrev goal : W := ~~~0xfeeeeee0eee8e8e0
open CoreSigned (build)
def tableB (x : Fin 6 → Bool) :=
  Nat.testBit (4277071584 * 2 ^ 32 + 4008241376) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
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

theorem low (reject : ¬ build basicOps (0xfeeeeee0eee8e8e0 : W) 10 cols.toFinset)
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
    (reject : ¬ CoreSigned.build SignedProjection.signedOps (0xfeeeeee0eee8e8e0 : BitVec 64) 10 Direct64.cols.toFinset) :
∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4277071584 * 2 ^ 32 + 4008241376) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4277071584 * 2 ^ 32 + 4008241376) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
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
def ew0 : Word := 0x400040004000400
def ew1 : Word := 0x404000004040000
def ew2 : Word := 0x404040400000000
def ew3 : Word := 0x200020002000200
def ew4 : Word := 0x202000002020000
def ew5 : Word := 0x202020200000000
def ew6 : Word := 0x8080808
def ew7 : Word := 0xa000a00
def ew8 : Word := 0xa0a0000
def ew9 : Word := 0xc000c00
def ew10 : Word := 0xc0c0000
def ew11 : Word := 0xf000000
def ew12 : Word := 0xaa0000
def ew13 : Word := 0xcc0000
def ew14 : Word := 0xf00000
def ew15 : Word := 0x4400440044004400
def ew16 : Word := 0x5000500050005000
def ew17 : Word := 0x5500000055000000
def ew18 : Word := 0x5500550000000000
def ew19 : Word := 0xa000a000a000a00
def ew20 : Word := 0x804080408040804
def ew21 : Word := 0xa0500000a050000
def ew22 : Word := 0xa050a0500000000
def ew23 : Word := 0xaa00aa
def ew24 : Word := 0xcc00cc
def ew25 : Word := 0xf000f0
def ew26 : Word := 0xff0000
def ew27 : Word := 0xaa000000aa00
def ew28 : Word := 0x884400008844
def ew29 : Word := 0xa0500000a050
def ew30 : Word := 0xaa5500000000
def ew31 : Word := 0xaa00aa00
def ew32 : Word := 0x88448844
def ew33 : Word := 0xa050a050
def ew34 : Word := 0xaa550000
def ew35 : Word := 0xa0a0a0a
def ew36 : Word := 0xc0c0c0c
def ew37 : Word := 0xf000f00
def ew38 : Word := 0xf0f0000
def ew39 : Word := 0xa00a0000a00a0000
def ew40 : Word := 0xc00c0000c00c0000
def ew41 : Word := 0xf0000000f0000000
def ew42 : Word := 0xf00f000000000000
def ew43 : Word := 0xa0000a00a0000a00
def ew44 : Word := 0xc0000c00c0000c00
def ew45 : Word := 0xf0000f0000000000
def ew46 : Word := 0x808080808080808
def ew47 : Word := 0xa0a00000a0a0000
def ew48 : Word := 0xa0a0a0a00000000
def ew49 : Word := 0x4040404004040404
def ew50 : Word := 0x5050505000000000
def ew51 : Word := 0x5000500005000500
def ew52 : Word := 0x5050000005050000
def ew53 : Word := 0x4040404040404040
def ew54 : Word := 0x4444000044440000
def ew55 : Word := 0x4444444400000000
def ew56 : Word := 0x8080808008080808
def ew57 : Word := 0xa0a0a0a000000000
def ew58 : Word := 0xa000a0000a000a00
def ew59 : Word := 0xa0a000000a0a0000
def ew60 : Word := 0x2020202002020202
def ew61 : Word := 0x3030303000000000
def ew62 : Word := 0x3000300003000300
def ew63 : Word := 0x3030000003030000
def ew64 : Word := 0xc000c0000c000c00
def ew65 : Word := 0xf000f00000000000
def ew66 : Word := 0xf00000000f000000
def ew67 : Word := 0xc0c000000c0c0000
def ew68 : Word := 0xf0f0000000000000
def ew69 : Word := 0xaa00000000aa0000
def ew70 : Word := 0xcc00000000cc0000
def ew71 : Word := 0xf000000000f00000
def ew72 : Word := 0xff00000000000000
def ew73 : Word := 0xaa0000000000aa00
def ew74 : Word := 0xcc0000000000cc00
def ew75 : Word := 0xf00000000000f000
def ew76 : Word := 0x5050000050500000
def ew77 : Word := 0x5555000000000000
def ew78 : Word := 0x2020202020202020
def ew79 : Word := 0x2200220022002200
def ew80 : Word := 0x2222000022220000
def ew81 : Word := 0x2222222200000000
def ew82 : Word := 0x88888888
def ew83 : Word := 0xa0a0a0a0
def ew84 : Word := 0xaaaa0000
def ew85 : Word := 0x3000300030003000
def ew86 : Word := 0x3300000033000000
def ew87 : Word := 0x3300330000000000
def ew88 : Word := 0x3030000030300000
def ew89 : Word := 0x3333000000000000
def ew90 : Word := 0xa000a000a000a
def ew91 : Word := 0xc000c000c000c
def ew92 : Word := 0xf0000000f0000
def ew93 : Word := 0xf000f00000000
def ew94 : Word := 0xc000c000c000c00
def ew95 : Word := 0xf0000000f000000
def ew96 : Word := 0xf000f0000000000
def ew97 : Word := 0xc0c00000c0c0000
def ew98 : Word := 0xf0f000000000000
def ew99 : Word := 0x1010101010101010
def ew100 : Word := 0x1200120012001200
def ew101 : Word := 0x1212000012120000
def ew102 : Word := 0x1212121200000000
def ew103 : Word := 0x50005000500050
def ew104 : Word := 0x48004800480048
def ew105 : Word := 0x5a0000005a0000
def ew106 : Word := 0x5a005a00000000
def ew107 : Word := 0x4800480048004800
def ew108 : Word := 0x5a0000005a000000
def ew109 : Word := 0x5a005a0000000000
def ew110 : Word := 0x505000005050
def ew111 : Word := 0x484800004848
def ew112 : Word := 0x5a0000005a00
def ew113 : Word := 0x5a5a00000000
def ew114 : Word := 0x4848000048480000
def ew115 : Word := 0x5a5a000000000000
def ew116 : Word := 0x50505050
def ew117 : Word := 0x48484848
def ew118 : Word := 0x5a005a00
def ew119 : Word := 0x5a5a0000
def ew120 : Word := 0x4848484800000000
def ew121 : Word := 0x55005500
def ew122 : Word := 0x44884488
def ew123 : Word := 0x50a050a0
def ew124 : Word := 0x55aa0000
def ew125 : Word := 0x1111111100000000
def ew126 : Word := 0x1010101020202020
def ew127 : Word := 0x1100110022002200
def ew128 : Word := 0x1111000022220000
def ew129 : Word := 0x505050500000000
def ew130 : Word := 0x404040408080808
def ew131 : Word := 0x50005000a000a00
def ew132 : Word := 0x50500000a0a0000
def ew133 : Word := 0x55005500000000
def ew134 : Word := 0x44004400880088
def ew135 : Word := 0x50005000a000a0
def ew136 : Word := 0x55000000aa0000
def ew137 : Word := 0x4400440088008800
def ew138 : Word := 0x50005000a000a000
def ew139 : Word := 0x55000000aa000000
def ew140 : Word := 0x555500000000
def ew141 : Word := 0x444400008888
def ew142 : Word := 0x50500000a0a0
def ew143 : Word := 0x55000000aa00
def ew144 : Word := 0x4444000088880000
def ew145 : Word := 0x50500000a0a00000
def ew146 : Word := 0x1400140014001400
def ew147 : Word := 0x1414000014140000
def ew148 : Word := 0x1414141400000000
def ew149 : Word := 0xaa00aa00aa00aa00
def ew150 : Word := 0x8844884488448844
def ew151 : Word := 0xa050a050a050a050
def ew152 : Word := 0xaa550000aa550000
def ew153 : Word := 0xaa55aa5500000000
def ew154 : Word := 0xaaaa0000aaaa0000
def ew155 : Word := 0x8888444488884444
def ew156 : Word := 0xa0a05050a0a05050
def ew157 : Word := 0xaa005500aa005500
def ew158 : Word := 0xaaaa555500000000
def ew159 : Word := 0x8822882288228822
def ew160 : Word := 0xcc00cc00cc00cc00
def ew161 : Word := 0xc030c030c030c030
def ew162 : Word := 0xcc330000cc330000
def ew163 : Word := 0xcc33cc3300000000
def ew164 : Word := 0x8888222288882222
def ew165 : Word := 0xcccc0000cccc0000
def ew166 : Word := 0xc0c03030c0c03030
def ew167 : Word := 0xcc003300cc003300
def ew168 : Word := 0xcccc333300000000
def ew169 : Word := 0xa00aa00aa00aa00a
def ew170 : Word := 0xc00cc00cc00cc00c
def ew171 : Word := 0xf000f000f000f000
def ew172 : Word := 0xf00f0000f00f0000
def ew173 : Word := 0xf00ff00f00000000
def ew174 : Word := 0xa0a00a0aa0a00a0a
def ew175 : Word := 0xc0c00c0cc0c00c0c
def ew176 : Word := 0xf0f00000f0f00000
def ew177 : Word := 0xf0000f00f0000f00
def ew178 : Word := 0xf0f00f0f00000000
def ew179 : Word := 0xa0a0a0a00a0a0a0a
def ew180 : Word := 0xc0c0c0c00c0c0c0c
def ew181 : Word := 0xf0f0f0f000000000
def ew182 : Word := 0xf000f0000f000f00
def ew183 : Word := 0xf0f000000f0f0000
def ew184 : Word := 0xaa00aa0000aa00aa
def ew185 : Word := 0xcc00cc0000cc00cc
def ew186 : Word := 0xf000f00000f000f0
def ew187 : Word := 0xff00ff0000000000
def ew188 : Word := 0xff00000000ff0000
def ew189 : Word := 0xaaaa00000000aaaa
def ew190 : Word := 0xcccc00000000cccc
def ew191 : Word := 0xf0f000000000f0f0
def ew192 : Word := 0xff0000000000ff00
def ew193 : Word := 0xffff000000000000
def ew194 : Word := 0x4444444444444444
def ew195 : Word := 0x5050505050505050
def ew196 : Word := 0x5500550055005500
def ew197 : Word := 0x5555000055550000
def ew198 : Word := 0x5555555500000000
def ew199 : Word := 0x8888888888888888
def ew200 : Word := 0xa0a0a0a0a0a0a0a0
def ew201 : Word := 0xaaaaaaaa00000000
def ew202 : Word := 0x2222222222222222
def ew203 : Word := 0x3030303030303030
def ew204 : Word := 0x3300330033003300
def ew205 : Word := 0x3333000033330000
def ew206 : Word := 0x3333333300000000
def ew207 : Word := 0xc0c0c0c0c0c0c0c0
def ew208 : Word := 0xcccccccc00000000
def ew209 : Word := 0xa0a0a0a0a0a0a0a
def ew210 : Word := 0xc0c0c0c0c0c0c0c
def ew211 : Word := 0xf000f000f000f00
def ew212 : Word := 0xf0f00000f0f0000
def ew213 : Word := 0xf0f0f0f00000000
def ew214 : Word := 0xaa00aa00aa00aa
def ew215 : Word := 0xcc00cc00cc00cc
def ew216 : Word := 0xf000f000f000f0
def ew217 : Word := 0xff000000ff0000
def ew218 : Word := 0xff00ff00000000
def ew219 : Word := 0xff000000ff000000
def ew220 : Word := 0xaaaa0000aaaa
def ew221 : Word := 0xcccc0000cccc
def ew222 : Word := 0xf0f00000f0f0
def ew223 : Word := 0xff000000ff00
def ew224 : Word := 0xffff00000000
def ew225 : Word := 0xaaaaaaaa
def ew226 : Word := 0xcccccccc
def ew227 : Word := 0xf0f0f0f0
def ew228 : Word := 0xff00ff00
def ew229 : Word := 0xffff0000
def ew230 : Word := 0x4848484848484848
def ew231 : Word := 0x5a005a005a005a00
def ew232 : Word := 0x5a5a00005a5a0000
def ew233 : Word := 0x5a5a5a5a00000000
def ew234 : Word := 0x4444444488888888
def ew235 : Word := 0x50505050a0a0a0a0
def ew236 : Word := 0x55005500aa00aa00
def ew237 : Word := 0x55550000aaaa0000
def ew238 : Word := 0x2828282828282828
def ew239 : Word := 0x3c003c003c003c00
def ew240 : Word := 0x3c3c00003c3c0000
def ew241 : Word := 0x3c3c3c3c00000000
def ew242 : Word := 0x2222222288888888
def ew243 : Word := 0x30303030c0c0c0c0
def ew244 : Word := 0x33003300cc00cc00
def ew245 : Word := 0x33330000cccc0000
def ew246 : Word := 0xaaaaaaaaaaaaaaaa
def ew247 : Word := 0xcccccccccccccccc
def ew248 : Word := 0xf0f0f0f0f0f0f0f0
def ew249 : Word := 0xff00ff00ff00ff00
def ew250 : Word := 0xffff0000ffff0000
def ew251 : Word := 0xffffffff00000000
def ew252 : Word := 0x4000400040004000
def ew253 : Word := 0x5400540054005400
def ew254 : Word := 0x1000100010001000
def ew255 : Word := 0x4400000044000000
def ew256 : Word := 0x5500440055004400
def ew257 : Word := 0x440000004400
def ew258 : Word := 0x1100000011000000
def ew259 : Word := 0x4400440000000000
def ew260 : Word := 0x5500550044004400
def ew261 : Word := 0x44004400
def ew262 : Word := 0x1100110000000000
def ew263 : Word := 0x5000000050000000
def ew264 : Word := 0x5500500055005000
def ew265 : Word := 0x500000005000
def ew266 : Word := 0x500000005000000
def ew267 : Word := 0x5000500000000000
def ew268 : Word := 0x5500550050005000
def ew269 : Word := 0x50005000
def ew270 : Word := 0x500050000000000
def ew271 : Word := 0x5500000000000000
def ew272 : Word := 0x5500550055000000
def ew273 : Word := 0x55000000
def ew274 : Word := 0x550000000000
def ew275 : Word := 0x5500400055004000
def ew276 : Word := 0x1500000015000000
def ew277 : Word := 0x5500550040004000
def ew278 : Word := 0x1500150000000000
def ew279 : Word := 0x5400000054000000
def ew280 : Word := 0x540000005400
def ew281 : Word := 0x5400540000000000
def ew282 : Word := 0x54005400
def ew283 : Word := 0x5400500054005000
def ew284 : Word := 0x1000500010005000
def ew285 : Word := 0x5500550044000000
def ew286 : Word := 0x1100550000000000
def ew287 : Word := 0x5000400050004000
def ew288 : Word := 0x500040005000400
def ew289 : Word := 0x5500440000000000
def ew290 : Word := 0x55004400
def ew291 : Word := 0x5400540050005000
def ew292 : Word := 0x1000100050005000
def ew293 : Word := 0x5500440055000000
def ew294 : Word := 0x1100000055000000
def ew295 : Word := 0x5000500040004000
def ew296 : Word := 0x500050004000400
def ew297 : Word := 0x5500000044000000
def ew298 : Word := 0x550000004400
def ew299 : Word := 0x5500550000005000
def ew300 : Word := 0x5500050000000000
def ew301 : Word := 0x5500550005000000
def ew302 : Word := 0x5000550000000000
def ew303 : Word := 0x5500000055005000
def ew304 : Word := 0x5500000005000000
def ew305 : Word := 0x5500050055000000
def ew306 : Word := 0x5000000055000000
def ew307 : Word := 0x5000500055005000
def ew308 : Word := 0x5000500000005000
def ew309 : Word := 0x5000550050005000
def ew310 : Word := 0x5000000050005000
def ew311 : Word := 0x8000800
def ew312 : Word := 0x7000700
def ew313 : Word := 0x8080000
def ew314 : Word := 0x7070000
def ew315 : Word := 0x40c040c
def ew316 : Word := 0xa000000
def ew317 : Word := 0x50f0000
def ew318 : Word := 0x4040c0c
def ew319 : Word := 0x5000f00
def ew320 : Word := 0x20a020a
def ew321 : Word := 0xc000000
def ew322 : Word := 0x30f0000
def ew323 : Word := 0x2020a0a
def ew324 : Word := 0x3000f00
def ew325 : Word := 0xa0a0a
def ew326 : Word := 0xc0c0c
def ew327 : Word := 0x70f0000
def ew328 : Word := 0x7000f00
def ew329 : Word := 0x40c0c0c
def ew330 : Word := 0x20a0a0a
def ew331 : Word := 0x48004800
def ew332 : Word := 0x5a485a48
def ew333 : Word := 0x480048
def ew334 : Word := 0x12001200
def ew335 : Word := 0x48480000
def ew336 : Word := 0x5a5a4848
def ew337 : Word := 0x4848
def ew338 : Word := 0x12120000
def ew339 : Word := 0x5a000000
def ew340 : Word := 0x5a5a5a00
def ew341 : Word := 0x5a00
def ew342 : Word := 0x5a0000
def ew343 : Word := 0x58505850
def ew344 : Word := 0x5a5a4800
def ew345 : Word := 0x125a0000
def ew346 : Word := 0xa080a08
def ew347 : Word := 0x5a480000
def ew348 : Word := 0x5a48
def ew349 : Word := 0x58585050
def ew350 : Word := 0x5a485a00
def ew351 : Word := 0x12005a00
def ew352 : Word := 0xa0a0808
def ew353 : Word := 0x5a004800
def ew354 : Word := 0x5a0048
def ew355 : Word := 0x50505a50
def ew356 : Word := 0x505a5050
def ew357 : Word := 0x4040404000000000
def ew358 : Word := 0x5858585800000000
def ew359 : Word := 0x1010101000000000
def ew360 : Word := 0x808080800000000
def ew361 : Word := 0x5a505a5000000000
def ew362 : Word := 0x50005000000000
def ew363 : Word := 0xa000a0000000000
def ew364 : Word := 0x5050000000000000
def ew365 : Word := 0x5a5a505000000000
def ew366 : Word := 0x505000000000
def ew367 : Word := 0xa0a000000000000
def ew368 : Word := 0x4800480000000000
def ew369 : Word := 0x5a485a4800000000
def ew370 : Word := 0x48004800000000
def ew371 : Word := 0x1200120000000000
def ew372 : Word := 0x4848000000000000
def ew373 : Word := 0x5a5a484800000000
def ew374 : Word := 0x484800000000
def ew375 : Word := 0x1212000000000000
def ew376 : Word := 0x5a00000000000000
def ew377 : Word := 0x5a5a5a0000000000
def ew378 : Word := 0x5a0000000000
def ew379 : Word := 0x5a000000000000
def ew380 : Word := 0x5a405a4000000000
def ew381 : Word := 0x1a001a0000000000
def ew382 : Word := 0x5a5a404000000000
def ew383 : Word := 0x1a1a000000000000
def ew384 : Word := 0x4840484000000000
def ew385 : Word := 0x1210121000000000
def ew386 : Word := 0x5a5a005000000000
def ew387 : Word := 0x5a0a000000000000
def ew388 : Word := 0x4a484a4800000000
def ew389 : Word := 0x4048404800000000
def ew390 : Word := 0x5a5a0a0000000000
def ew391 : Word := 0x505a000000000000
def ew392 : Word := 0x4848404000000000
def ew393 : Word := 0x1212101000000000
def ew394 : Word := 0x5a005a5000000000
def ew395 : Word := 0x5a000a0000000000
def ew396 : Word := 0x4a4a484800000000
def ew397 : Word := 0x4040484800000000
def ew398 : Word := 0x5a0a5a0000000000
def ew399 : Word := 0x50005a0000000000
def ew400 : Word := 0x5850585000000000
def ew401 : Word := 0x1050105000000000
def ew402 : Word := 0x5a5a480000000000
def ew403 : Word := 0x125a000000000000
def ew404 : Word := 0x5858505000000000
def ew405 : Word := 0x1010505000000000
def ew406 : Word := 0x5a485a0000000000
def ew407 : Word := 0x12005a0000000000
def ew408 : Word := 0x5a48484800000000
def ew409 : Word := 0x48484800000000
def ew410 : Word := 0x5a50505000000000
def ew411 : Word := 0x50505000000000
def ew412 : Word := 0x8800880088008800
def ew413 : Word := 0xaa44aa44aa44aa44
def ew414 : Word := 0x44004400440044
def ew415 : Word := 0xaa55aa00aa55aa00
def ew416 : Word := 0xaa55aa55aa00aa00
def ew417 : Word := 0xaa558844aa558844
def ew418 : Word := 0xaa55aa5588448844
def ew419 : Word := 0xaa55aa55aa550000
def ew420 : Word := 0xa850a850a850a850
def ew421 : Word := 0xaa558800aa558800
def ew422 : Word := 0x880000008800
def ew423 : Word := 0x2255000022550000
def ew424 : Word := 0xaa55aa5588008800
def ew425 : Word := 0x88008800
def ew426 : Word := 0x2255225500000000
def ew427 : Word := 0xa040a040a040a04
def ew428 : Word := 0xaa440000aa440000
def ew429 : Word := 0xaa55aa44aa55aa44
def ew430 : Word := 0xaa440000aa44
def ew431 : Word := 0xaa44aa4400000000
def ew432 : Word := 0xaa55aa55aa44aa44
def ew433 : Word := 0xaa44aa44
def ew434 : Word := 0xaa552200aa552200
def ew435 : Word := 0x220000002200
def ew436 : Word := 0xaa55aa5522002200
def ew437 : Word := 0x22002200
def ew438 : Word := 0xaa550044aa550044
def ew439 : Word := 0x4400000044
def ew440 : Word := 0xaa55aa5500440044
def ew441 : Word := 0x440044
def ew442 : Word := 0x8844880088448800
def ew443 : Word := 0x2211220022112200
def ew444 : Word := 0xaa55aa0000000000
def ew445 : Word := 0xaa55aa55aa55aa00
def ew446 : Word := 0xaa55aa00
def ew447 : Word := 0x8844aa448844aa44
def ew448 : Word := 0x8844004488440044
def ew449 : Word := 0xaa55aa550000aa00
def ew450 : Word := 0xaa00
def ew451 : Word := 0x8844884488008800
def ew452 : Word := 0x2211221122002200
def ew453 : Word := 0xaa550000aa000000
def ew454 : Word := 0xaa550000aa00
def ew455 : Word := 0x88448844aa44aa44
def ew456 : Word := 0x8844884400440044
def ew457 : Word := 0xaa550000aa55aa00
def ew458 : Word := 0xaa008800aa008800
def ew459 : Word := 0x55004400550044
def ew460 : Word := 0xaa55aa55aa558844
def ew461 : Word := 0xaa558844
def ew462 : Word := 0xaa00aa44aa00aa44
def ew463 : Word := 0xaa002200aa002200
def ew464 : Word := 0xaa55aa5500008844
def ew465 : Word := 0x8844
def ew466 : Word := 0xaa55221100000000
def ew467 : Word := 0xaa00aa0088008800
def ew468 : Word := 0x55005500440044
def ew469 : Word := 0xaa5500008844
def ew470 : Word := 0xaa00aa00aa44aa44
def ew471 : Word := 0xaa00aa0022002200
def ew472 : Word := 0xaa550000aa558844
def ew473 : Word := 0xaa55000022110000
def ew474 : Word := 0x8844884488440000
def ew475 : Word := 0x2211221122110000
def ew476 : Word := 0xaa00aa00aa000000
def ew477 : Word := 0x55005500550000
def ew478 : Word := 0xaa55a850aa55a850
def ew479 : Word := 0x205000002050000
def ew480 : Word := 0xaa55aa55a850a850
def ew481 : Word := 0x205020500000000
def ew482 : Word := 0xa050a850a050a850
def ew483 : Word := 0xaa55aa5500008800
def ew484 : Word := 0xa050a050a850a850
def ew485 : Word := 0xaa550000aa558800
def ew486 : Word := 0x2244224422442244
def ew487 : Word := 0xa0400000a040000
def ew488 : Word := 0xa0400000a04
def ew489 : Word := 0xa040a0400000000
def ew490 : Word := 0xa040a04
def ew491 : Word := 0xa050a040a050a04
def ew492 : Word := 0xaa55aa44
def ew493 : Word := 0xa050a050a040a04
def ew494 : Word := 0xaa550000aa44
def ew495 : Word := 0xaa552200
def ew496 : Word := 0xaa5500002200
def ew497 : Word := 0xaa55aa5500000044
def ew498 : Word := 0xaa550000aa550044
def ew499 : Word := 0xaa55aa50a050a050
def ew500 : Word := 0x8040a0408040a04
def ew501 : Word := 0x8844aa44
def ew502 : Word := 0xaa55a050aa50a050
def ew503 : Word := 0x80408040a040a04
def ew504 : Word := 0x88440000aa44
def ew505 : Word := 0xaa50a850aa50a850
def ew506 : Word := 0xaa55aa55aa008800
def ew507 : Word := 0xaa55a251a050a050
def ew508 : Word := 0xaa50aa50a850a850
def ew509 : Word := 0xaa55aa00aa558800
def ew510 : Word := 0xaa55a050a251a050
def ew511 : Word := 0xa251a251a251a050
def ew512 : Word := 0xaa44aa44aa448844
def ew513 : Word := 0x44004400448844
def ew514 : Word := 0xaa50aa50aa50a050
def ew515 : Word := 0xe0e0e0e00e0e0e0e
def ew516 : Word := 0x5a505a505a505a50
def ew517 : Word := 0x5a5a50505a5a5050
def ew518 : Word := 0x5a5a5a005a5a5a00
def ew519 : Word := 0xa5a00000a5a0000
def ew520 : Word := 0x5a5000005a500000
def ew521 : Word := 0x5a5a00505a5a0050
def ew522 : Word := 0x5a0a00005a0a0000
def ew523 : Word := 0xa0000000a000000
def ew524 : Word := 0x5a5a0a005a5a0a00
def ew525 : Word := 0x505a0000505a0000
def ew526 : Word := 0xa005a000a005a00
def ew527 : Word := 0x5a0050005a005000
def ew528 : Word := 0x5a005a505a005a50
def ew529 : Word := 0x5a000a005a000a00
def ew530 : Word := 0x5a0a5a005a0a5a00
def ew531 : Word := 0x50005a0050005a00
def ew532 : Word := 0x5a5050505a505050
def ew533 : Word := 0x50505000505050
def ew534 : Word := 0xa0a0a000a0a0a00
def ew535 : Word := 0x50505a5050505a50
def ew536 : Word := 0x505a5050505a5050
def ew537 : Word := 0x505a5000505a50
def ew538 : Word := 0x4a4848484a484848
def ew539 : Word := 0xa5a0a000a5a0a00
def ew540 : Word := 0x5a5050005a5050
def ew541 : Word := 0xa0a5a000a0a5a00
def ew542 : Word := 0x5a5a00005a5a00
def ew543 : Word := 0x5a5a5a5a4a484848
def ew544 : Word := 0x1012121200000000
def ew545 : Word := 0xa0a00000a0a00
def ew546 : Word := 0x5a0a0a005a0a0a00
def ew547 : Word := 0x505a5a50505a5a50
def ew548 : Word := 0x54545454a8a8a8a8
def ew549 : Word := 0x51505150a2a0a2a0
def ew550 : Word := 0x51515050a2a2a0a0
def ew551 : Word := 0x454445448a888a88
def ew552 : Word := 0x454544448a8a8888
def ew553 : Word := 0x55444444aa888888
def ew554 : Word := 0x55505050aaa0a0a0
def ew555 : Word := 0xeeeeeeeeeeeeeeee
def ew556 : Word := 0xffffffffaaaaaaaa
def ew557 : Word := 0xffffffffcccccccc
def ew558 : Word := 0xee00ee00ee00ee00
def ew559 : Word := 0xeeee0000eeee0000
def ew560 : Word := 0xff00ff00aa00aa00
def ew561 : Word := 0xffff0000aaaa0000
def ew562 : Word := 0xff00ff00cc00cc00
def ew563 : Word := 0xffff0000cccc0000
def ew564 : Word := 0xffaaaaaaffaaaaaa
def ew565 : Word := 0xffccccccffcccccc
def ew566 : Word := 0xfff0f0f0fff0f0f0
def ew567 : Word := 0xee000000ee000000
def ew568 : Word := 0x11ff000011ff0000
def ew569 : Word := 0x1100ff001100ff00
def ew570 : Word := 0xffeeeeeeffeeeeee
def ew571 : Word := 0xeeeeee00eeeeee
def ew572 : Word := 0xffffff00aaaaaa
def ew573 : Word := 0xffffff00cccccc
def ew574 : Word := 0x3322222233222222
def ew575 : Word := 0x5544444455444444
def ew576 : Word := 0xf0fefefef0fefefe
def ew577 : Word := 0xe0e0e000e0e0e
def labelsBlock0 : Array Nat := #[
  0x3248,
  0x2a88,
  0x1a28,
  0x1,
  0x2aa0,
  0x3ce0,
  0x3c70,
  0x3cb0,
  0x5,
  0x130c,
  0x504,
  0x610,
  0x510,
  0x101a,
  0x1924,
  0x1944
]
def labelsBlock1 : Array Nat := #[
  0x1344,
  0x1348,
  0x105,
  0x2924,
  0xb24,
  0xb0c,
  0x1006,
  0x2a28,
  0x1a48,
  0x608,
  0x1002,
  0x3144,
  0x60c,
  0x1b1,
  0x1b5,
  0x36d0
]
def labelsBlock2 : Array Nat := #[
  0x2b8c,
  0x2ca4,
  0x225,
  0xc14,
  0x35d,
  0xb08,
  0x361,
  0xd30,
  0xd04,
  0x1036,
  0x2504,
  0xb28,
  0x6a1,
  0x2904,
  0x29a0,
  0x105a
]
def labelsBlock3 : Array Nat := #[
  0x1a60,
  0x6b9,
  0x106a,
  0x1032,
  0x107e,
  0xd24,
  0x6bd,
  0x3184,
  0x2984,
  0x2690,
  0x2590,
  0x2584,
  0x1066,
  0x6c1,
  0x2414,
  0x7ed
]
def labelsBlock4 : Array Nat := #[
  0x1014,
  0x3c50,
  0x82d,
  0x3288,
  0x9,
  0x1c68,
  0xe28,
  0xe30,
  0xd,
  0x11,
  0xe20,
  0x15,
  0x19,
  0x1d,
  0x21,
  0x1a20
]
def labelsBlock5 : Array Nat := #[
  0x25,
  0x29,
  0x2c38,
  0x2d,
  0x31,
  0x2a20,
  0x35,
  0x39,
  0x3d,
  0x41,
  0x45,
  0x49,
  0x4d,
  0x2e28,
  0x51,
  0x55
]
def labelsBlock6 : Array Nat := #[
  0x59,
  0x5d,
  0x61,
  0x65,
  0x69,
  0x6d,
  0x71,
  0x75,
  0x1c38,
  0x79,
  0x7d,
  0x81,
  0x85,
  0x89,
  0x8d,
  0x91
]
def labelsBlock7 : Array Nat := #[
  0x95,
  0x99,
  0x9d,
  0xa1,
  0xa5,
  0xa9,
  0xad,
  0xb1,
  0xb5,
  0xb9,
  0xbd,
  0xc1,
  0xc5,
  0x1e70,
  0xc9,
  0xcd
]
def labelsBlock8 : Array Nat := #[
  0xd1,
  0x1e28,
  0xd5,
  0xd9,
  0x2eb0,
  0xdd,
  0xe1,
  0xe5,
  0xe9,
  0xed,
  0x3ae0,
  0xf1,
  0xf5,
  0xf9,
  0x3a28,
  0xfd
]
def labelsBlock9 : Array Nat := #[
  0x101,
  0x1960,
  0x109,
  0x100a,
  0x100e,
  0x10d,
  0x1012,
  0x111,
  0x1016,
  0x115,
  0x119,
  0x11d,
  0x121,
  0x125,
  0x129,
  0x12d
]
def labelsBlock10 : Array Nat := #[
  0x131,
  0x135,
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
  0x165,
  0x169,
  0x16d
]
def labelsBlock11 : Array Nat := #[
  0x171,
  0x175,
  0x179,
  0x17d,
  0x181,
  0x185,
  0x189,
  0x18d,
  0x191,
  0x195,
  0x199,
  0x19d,
  0x1a1,
  0x1a5,
  0x1a9,
  0x1ad
]
def labelsBlock12 : Array Nat := #[
  0x3190,
  0x2318,
  0x2418,
  0x3104,
  0x1c64,
  0x1b9,
  0xc18,
  0x1bd,
  0x1c1,
  0xb04,
  0x1c5,
  0x1c9,
  0x1418,
  0x1cd,
  0x1d1,
  0x1304
]
def labelsBlock13 : Array Nat := #[
  0x1d5,
  0x1d9,
  0x1dd,
  0x1904,
  0x1e1,
  0x1e5,
  0x1e9,
  0x1ed,
  0x1f1,
  0x1f5,
  0x1f9,
  0x1fd,
  0x201,
  0x205,
  0x209,
  0x1950
]
def labelsBlock14 : Array Nat := #[
  0x1930,
  0x1644,
  0x20d,
  0x211,
  0x215,
  0x219,
  0x21d,
  0x221,
  0x604,
  0x229,
  0x34c4,
  0x22d,
  0x2cac,
  0x268c,
  0x231,
  0x2684
]
def labelsBlock15 : Array Nat := #[
  0x235,
  0x239,
  0x23d,
  0x241,
  0x2990,
  0x3cd0,
  0x245,
  0x249,
  0x2e8c,
  0x24d,
  0x251,
  0x255,
  0x259,
  0x368c,
  0x25d,
  0x261
]
def labelsBlock16 : Array Nat := #[
  0x298c,
  0x265,
  0x269,
  0x2b84,
  0x26d,
  0x271,
  0x318c,
  0x338c,
  0x275,
  0x279,
  0x3384,
  0x27d,
  0x281,
  0x285,
  0x289,
  0x28d
]
def labelsBlock17 : Array Nat := #[
  0x299,
  0x295,
  0x29d,
  0x2a1,
  0x2a5,
  0x2a9,
  0x2ad,
  0x2b1,
  0x2b5,
  0x2b9,
  0x291,
  0x2bd,
  0x2c1,
  0x2c5,
  0x2c9,
  0x2cd
]
def labelsBlock18 : Array Nat := #[
  0x2d1,
  0x2d5,
  0x2d9,
  0x2dd,
  0x2e1,
  0x2e5,
  0x2e9,
  0x2c98,
  0x2e90,
  0x3c90,
  0x2ed,
  0x2f1,
  0x2f5,
  0x2f9,
  0x2fd,
  0x301
]
def labelsBlock19 : Array Nat := #[
  0x305,
  0x309,
  0x3498,
  0x3690,
  0x30d,
  0x311,
  0x315,
  0x319,
  0x31d,
  0x321,
  0x325,
  0x329,
  0x32d,
  0x331,
  0x335,
  0x339
]
def labelsBlock20 : Array Nat := #[
  0x33d,
  0x3984,
  0x341,
  0x345,
  0x349,
  0x34d,
  0x351,
  0x31b0,
  0x355,
  0x359,
  0xc1c,
  0xe0c,
  0x1328,
  0x50c,
  0x704,
  0x1114
]
def labelsBlock21 : Array Nat := #[
  0xd10,
  0x365,
  0x369,
  0x1b48,
  0x36d,
  0xb00,
  0x371,
  0x2980,
  0x2688,
  0x1022,
  0x102a,
  0x1940,
  0x375,
  0x379,
  0x102e,
  0x39c0
]
def labelsBlock22 : Array Nat := #[
  0x37d,
  0x381,
  0x2900,
  0x1650,
  0x385,
  0x389,
  0x1610,
  0x38d,
  0x391,
  0x2610,
  0x1648,
  0x2218,
  0x395,
  0x399,
  0x39d,
  0x3a1
]
def labelsBlock23 : Array Nat := #[
  0x3a5,
  0x410022,
  0x3a9,
  0x3ad,
  0x3b1,
  0x3b5,
  0x3b9,
  0x3bd,
  0x3c1,
  0x3c5,
  0x3c9,
  0x3cd,
  0x3d1,
  0x3d5,
  0x32c0,
  0x1948
]
def labelsBlock24 : Array Nat := #[
  0x3d9,
  0x3dd,
  0x1218,
  0x2434,
  0x510022,
  0x3e1,
  0x3e5,
  0x3e9,
  0x3ed,
  0x3f1,
  0x3f5,
  0x3f9,
  0x3fd,
  0x1608,
  0x2b88,
  0x401
]
def labelsBlock25 : Array Nat := #[
  0x405,
  0x409,
  0x40d,
  0x411,
  0x415,
  0x419,
  0x41d,
  0x421,
  0x425,
  0x429,
  0x610022,
  0x42d,
  0x431,
  0x435,
  0x439,
  0x43d
]
def labelsBlock26 : Array Nat := #[
  0x441,
  0x445,
  0x222c,
  0x710022,
  0x449,
  0x44d,
  0x451,
  0x455,
  0x459,
  0x45d,
  0x461,
  0x465,
  0x469,
  0x46d,
  0x471,
  0x1d50
]
def labelsBlock27 : Array Nat := #[
  0x520022,
  0x122c,
  0x475,
  0x479,
  0x47d,
  0x481,
  0x485,
  0x489,
  0x48d,
  0x491,
  0x495,
  0x620022,
  0x499,
  0x49d,
  0x4a1,
  0x1900
]
def labelsBlock28 : Array Nat := #[
  0x63002e,
  0x4a5,
  0x4a9,
  0x4ad,
  0x2d90,
  0x530022,
  0x4b1,
  0x4b5,
  0x4b9,
  0x4bd,
  0x4c1,
  0x4c5,
  0x4c9,
  0x4cd,
  0x630022,
  0x4d1
]
def labelsBlock29 : Array Nat := #[
  0x4d5,
  0x63002a,
  0x4d9,
  0x521022,
  0x4dd,
  0x4e1,
  0x53102e,
  0x4e5,
  0x4e9,
  0x621022,
  0x4ed,
  0x4f1,
  0x4f5,
  0x4f9,
  0x4fd,
  0x501
]
def labelsBlock30 : Array Nat := #[
  0x505,
  0x509,
  0x50d,
  0x531022,
  0x511,
  0x515,
  0x53102a,
  0x519,
  0x631022,
  0x51d,
  0x521,
  0x525,
  0x529,
  0x52d,
  0x531,
  0x535
]
def labelsBlock31 : Array Nat := #[
  0x539,
  0x53d,
  0x532022,
  0x541,
  0x545,
  0x549,
  0x54d,
  0x551,
  0xd00,
  0x555,
  0x559,
  0xb10,
  0x55d,
  0x561,
  0x565,
  0x569
]
def labelsBlock32 : Array Nat := #[
  0x56d,
  0x571,
  0x575,
  0x579,
  0x57d,
  0x2608,
  0x2b08,
  0x581,
  0x149010022,
  0x585,
  0x589,
  0x1434,
  0x600,
  0x58d,
  0x591,
  0x595
]
def labelsBlock33 : Array Nat := #[
  0x1c9010022,
  0x599,
  0x59d,
  0x5a1,
  0x14d010022,
  0x5a5,
  0x5a9,
  0x5ad,
  0x1cd010022,
  0x5b1,
  0xd08,
  0x918,
  0x1908,
  0x2988,
  0x5b5,
  0x1640
]
def labelsBlock34 : Array Nat := #[
  0x3240,
  0x3208,
  0x5b9,
  0x2680,
  0x5bd,
  0x1b08,
  0x3280,
  0x5c1,
  0x5c5,
  0x5c9,
  0x5cd,
  0x1018,
  0x5d1,
  0x5d5,
  0x5d9,
  0x5dd
]
def labelsBlock35 : Array Nat := #[
  0x109110022,
  0x5e1,
  0x5e5,
  0x5e9,
  0x5ed,
  0x5f1,
  0x189110022,
  0x1d10,
  0x5f5,
  0x5f9,
  0x10d110022,
  0x5fd,
  0x601,
  0x605,
  0x18d110022,
  0x2d10
]
def labelsBlock36 : Array Nat := #[
  0x609,
  0x60d,
  0x611,
  0x615,
  0x102c,
  0x202c,
  0x2b00,
  0x619,
  0x61d,
  0x621,
  0x625,
  0x629,
  0x62d,
  0x631,
  0x635,
  0x18d120022
]
def labelsBlock37 : Array Nat := #[
  0x1b24,
  0x639,
  0x63d,
  0x3924,
  0x2064,
  0x641,
  0x645,
  0x1d0930022,
  0x2b24,
  0x649,
  0x64d,
  0x651,
  0x655,
  0x14d221022,
  0x659,
  0x65d
]
def labelsBlock38 : Array Nat := #[
  0x661,
  0x665,
  0x669,
  0x66d,
  0x149231022,
  0x671,
  0x675,
  0x2650,
  0x679,
  0x73102a,
  0x67d,
  0x681,
  0x685,
  0x43002a,
  0x242c,
  0x3290
]
def labelsBlock39 : Array Nat := #[
  0x689,
  0x3250,
  0x2908,
  0x2018,
  0x2600,
  0x2034,
  0x68d,
  0x2058,
  0x1034,
  0x2640,
  0x691,
  0x695,
  0x1600,
  0x699,
  0x2910,
  0x2940
]
def labelsBlock40 : Array Nat := #[
  0x69d,
  0x14933102a,
  0x15043002a,
  0x1910,
  0x15083002a,
  0x6a5,
  0x6a9,
  0x6ad,
  0xb20,
  0x6b1,
  0x3544,
  0x1052,
  0x1056,
  0x2524,
  0x2d24,
  0x2544
]
def labelsBlock41 : Array Nat := #[
  0x410032,
  0x1042,
  0x104a,
  0x410052,
  0x410056,
  0x270c,
  0x6b5,
  0x104e,
  0x3c60,
  0x510032,
  0x510052,
  0x510056,
  0x610032,
  0x610052,
  0x610056,
  0x710032
]
def labelsBlock42 : Array Nat := #[
  0x710052,
  0x710056,
  0x144010032,
  0x144010052,
  0x144010056,
  0x10c2,
  0x101e,
  0x1062,
  0x1072,
  0x103a,
  0x105e,
  0x108a,
  0x6c5,
  0x6c9,
  0x6cd,
  0x6d1
]
def labelsBlock43 : Array Nat := #[
  0x6d5,
  0x6d9,
  0x6dd,
  0x160c,
  0x6e1,
  0x109e,
  0x10a2,
  0x6e5,
  0x6e9,
  0x6ed,
  0x6f1,
  0x41008a,
  0x103e,
  0x6f5,
  0x109a,
  0x6f9
]
def labelsBlock44 : Array Nat := #[
  0x42009e,
  0x4200a2,
  0x1092,
  0x108e,
  0x51008a,
  0x6fd,
  0x701,
  0x52009e,
  0x5200a2,
  0x705,
  0x709,
  0x61008a,
  0x70d,
  0x711,
  0x715,
  0x62009e
]
def labelsBlock45 : Array Nat := #[
  0x6200a2,
  0x71008a,
  0x719,
  0x71d,
  0x721,
  0x725,
  0x72009e,
  0x7200a2,
  0x729,
  0x72d,
  0x731,
  0x735,
  0x42008a,
  0x739,
  0x73d,
  0x43009e
]
def labelsBlock46 : Array Nat := #[
  0x4300a2,
  0x1096,
  0x52008a,
  0x53009e,
  0x5300a2,
  0x741,
  0x745,
  0x62008a,
  0x749,
  0x74d,
  0x751,
  0x63009e,
  0x6300a2,
  0x72008a,
  0x755,
  0x759
]
def labelsBlock47 : Array Nat := #[
  0x75d,
  0x73009e,
  0x7300a2,
  0x761,
  0x765,
  0x42108a,
  0x769,
  0x76d,
  0x771,
  0x43209e,
  0x4320a2,
  0x775,
  0x52108a,
  0x779,
  0x53209e,
  0x5320a2
]
def labelsBlock48 : Array Nat := #[
  0x62108a,
  0x77d,
  0x781,
  0x63209e,
  0x6320a2,
  0x72108a,
  0x785,
  0x73209e,
  0x7320a2,
  0x1c501008a,
  0x1c902009e,
  0x1c901008a,
  0x1cd02009e,
  0x3970,
  0x789,
  0x78d
]
def labelsBlock49 : Array Nat := #[
  0x791,
  0x795,
  0x799,
  0x79d,
  0x10851008a,
  0x1c58,
  0x7a1,
  0x10911008a,
  0x14921008a,
  0x14d22009e,
  0x14d2200a2,
  0x1c921008a,
  0x1cd22009e,
  0x1cd2200a2,
  0x7a5,
  0x10931008a
]
def labelsBlock50 : Array Nat := #[
  0x1c931008a,
  0x7a9,
  0x1cd3200a2,
  0x7ad,
  0x260c,
  0x7b1,
  0x10871008a,
  0x7b5,
  0x1c871008a,
  0x1c502008a,
  0x1c903009e,
  0x1c902008a,
  0x1cd03009e,
  0x10852008a,
  0x7b9,
  0x11052008a
]
def labelsBlock51 : Array Nat := #[
  0x14522008a,
  0x14923009e,
  0x1492300a2,
  0x1c522008a,
  0x1c923009e,
  0x1c92300a2,
  0x1c532008a,
  0x1c93300a2,
  0x10872008a,
  0x7bd,
  0x18872008a,
  0x15002108a,
  0x1500320a2,
  0x7c1,
  0x7c5,
  0x14842108a
]
def labelsBlock52 : Array Nat := #[
  0x7c9,
  0x14c83209e,
  0x14c8320a2,
  0x7cd,
  0x1d012108a,
  0x14122108a,
  0x14123209e,
  0x1c522108a,
  0x14132108a,
  0x14133209e,
  0x1c18,
  0x3c10,
  0x234c,
  0xe10,
  0x7d1,
  0x7d5
]
def labelsBlock53 : Array Nat := #[
  0x3150,
  0x232c,
  0x1e10,
  0x1e0c,
  0x3c30,
  0x7d9,
  0x7dd,
  0x7e1,
  0x7e5,
  0x7504842108a,
  0x7e9,
  0x7544842108a,
  0x190c,
  0x1b0c,
  0x2164,
  0x241c
]
def labelsBlock54 : Array Nat := #[
  0x7f1,
  0x3864,
  0x10aa,
  0x7f5,
  0x10ae,
  0x10b6,
  0x7f9,
  0x10be,
  0x7fd,
  0x801,
  0x1544,
  0x805,
  0x809,
  0x106e,
  0x70c,
  0x6100ae
]
def labelsBlock55 : Array Nat := #[
  0x6100b6,
  0x6100be,
  0x80d,
  0x510066,
  0x5210b6,
  0x5210be,
  0x10b2,
  0x10ba,
  0x811,
  0x720066,
  0x7310be,
  0x815,
  0x730066,
  0x914,
  0x2014,
  0x7310b6
]
def labelsBlock56 : Array Nat := #[
  0x819,
  0x721066,
  0x2c34,
  0x224c,
  0x3454,
  0x81d,
  0x731066,
  0x1504,
  0x821,
  0x4320aa,
  0x432066,
  0x825,
  0x829,
  0xf24,
  0x282c,
  0x304c
]
def labelsBlock57 : Array Nat := #[
  0x38c8,
  0x38a8,
  0x5310b6,
  0x14c6100b6,
  0x10ea,
  0x831,
  0x10f2,
  0x1116,
  0x10fa,
  0x1102,
  0x835,
  0x110a,
  0x839,
  0x83d,
  0x110e,
  0x111e
]
def labelsBlock58 : Array Nat := #[
  0x841,
  0x845,
  0x849,
  0x84d,
  0x851,
  0x10de,
  0x855,
  0x859,
  0x85d,
  0x610116,
  0x107a,
  0x71011e,
  0x5100fa,
  0x861,
  0x865,
  0x510102
]
def labelsBlock59 : Array Nat := #[
  0x10c6,
  0x10ee,
  0x869,
  0x86d,
  0x51010a,
  0x10ca,
  0x51010e,
  0x111a,
  0x1112,
  0x871,
  0x875,
  0x5100de,
  0x879,
  0x420116,
  0x7200f2,
  0x7200fa
]
def labelsBlock60 : Array Nat := #[
  0x73010a,
  0x73010e,
  0x72011e,
  0x87d,
  0x881,
  0x2114,
  0x720032,
  0x7300de,
  0x430116,
  0x7300f2,
  0x7300fa,
  0x730102,
  0x74010e,
  0x1308,
  0x73011e,
  0x885
]
def labelsBlock61 : Array Nat := #[
  0x889,
  0x730032,
  0x7400de,
  0x640116,
  0x31c0,
  0x54011e,
  0x5400f2,
  0x5400fa,
  0x540102,
  0x54010a,
  0x5200de,
  0x88d,
  0x891,
  0x895,
  0x7200ea,
  0x10ce
]
def labelsBlock62 : Array Nat := #[
  0x721116,
  0x7210fa,
  0x42111e,
  0x73110a,
  0x73110e,
  0xa18,
  0x899,
  0x721032,
  0x7310de,
  0x7300ea,
  0x1550,
  0x1076,
  0x10d2,
  0x731116,
  0x7310fa,
  0x43111e
]
def labelsBlock63 : Array Nat := #[
  0x731102,
  0x74110e,
  0x89d,
  0x731032,
  0x7410de,
  0x5400ea,
  0x541116,
  0x5410fa,
  0x541102,
  0x54110a,
  0x1122,
  0x64111e,
  0x5210de,
  0x8a1,
  0x8a5,
  0x8a9
]
def labelsBlock64 : Array Nat := #[
  0x7210ea,
  0x10d6,
  0x720116,
  0x7210f2,
  0x72111e,
  0x73210a,
  0x7320de,
  0x73210e,
  0x7310ea,
  0x10da,
  0x730116,
  0x7310f2,
  0x73111e,
  0x732102,
  0x7420de,
  0x74210e
]
def labelsBlock65 : Array Nat := #[
  0x4320ea,
  0x4320f2,
  0x432116,
  0x4320fa,
  0x8ad,
  0x8b1,
  0x10fe,
  0x44310e,
  0x43211e,
  0x8b5,
  0x8b9,
  0x8bd,
  0x432032,
  0x4430de,
  0x1026,
  0x10e2
]
def labelsBlock66 : Array Nat := #[
  0x6420ea,
  0x6420f2,
  0x6230de,
  0x6420fa,
  0x642116,
  0x64310a,
  0x64211e,
  0x6430ea,
  0x10e6,
  0x6430f2,
  0x6240de,
  0x6430fa,
  0x643102,
  0x643116,
  0x64311e,
  0x4200ea
]
def labelsBlock67 : Array Nat := #[
  0x1c9610116,
  0x4200f2,
  0x1c971011e,
  0x1095100fa,
  0x10d51010a,
  0x1106,
  0x10d51010e,
  0x51003a,
  0x109110032,
  0x10d5100de,
  0x51005e,
  0x10f6,
  0x5100d6,
  0x5100c6,
  0x8c1,
  0x8c5
]
def labelsBlock68 : Array Nat := #[
  0x510112,
  0x5100e2,
  0x8c9,
  0x420066,
  0x8cd,
  0x4300ea,
  0x1cd610116,
  0x4300f2,
  0x1cd71011e,
  0x10d5100fa,
  0x10d510102,
  0x11151010e,
  0x510036,
  0x10d110032,
  0x1115100de,
  0x51005a
]
def labelsBlock69 : Array Nat := #[
  0x5100da,
  0x8d1,
  0x5100ca,
  0x5100e6,
  0x430066,
  0x8d5,
  0x1082,
  0x1c8210116,
  0x1c871011e,
  0x7020c6,
  0x7210ee,
  0x7320ca,
  0x73211a,
  0x732112,
  0x1cc91010e,
  0x1086
]
def labelsBlock70 : Array Nat := #[
  0x1cc210116,
  0x1cc71011e,
  0x7320c6,
  0x7020ca,
  0x7310ee,
  0x74211a,
  0x742112,
  0x1d091010e,
  0x10ca10116,
  0x8d9,
  0x43207a,
  0x10cb1011e,
  0x8dd,
  0x8e1,
  0x8e5,
  0x8e9
]
def labelsBlock71 : Array Nat := #[
  0x8ed,
  0x4300c6,
  0x44311a,
  0x443112,
  0x8f1,
  0x7310c6,
  0x7300d2,
  0x730112,
  0x741112,
  0x720036,
  0x72103a,
  0x1c8020116,
  0x1c87200f2,
  0x7200d6,
  0x1c872011e,
  0x1ccb3010a
]
def labelsBlock72 : Array Nat := #[
  0x1ccb300de,
  0x1ccb3010e,
  0xe08,
  0x7010c6,
  0x7300c6,
  0x7300ce,
  0x7310ca,
  0x740112,
  0x731112,
  0x721036,
  0x72003a,
  0x1cc030116,
  0x1cc7300f2,
  0x7200da,
  0x1cc73011e,
  0x1ccb30102
]
def labelsBlock73 : Array Nat := #[
  0x1d0b400de,
  0x1d0b4010e,
  0x39e0,
  0x5400ce,
  0x5400d6,
  0x110d200de,
  0x5400c6,
  0x8f5,
  0x4420ea,
  0x194a40116,
  0x11494011e,
  0x1149400f2,
  0x1149400fa,
  0x114d4010a,
  0x40310e,
  0x402032
]
def labelsBlock74 : Array Nat := #[
  0x114d200de,
  0x4430ea,
  0x194e40116,
  0x114d4011e,
  0x114d400f2,
  0x114d400fa,
  0x114d40102,
  0x40410e,
  0x403032,
  0x1151200de,
  0x53005a,
  0x1c842111e,
  0x1c87200ea,
  0x7210d6,
  0x1c8321116,
  0x7120ce
]
def labelsBlock75 : Array Nat := #[
  0x1ccb3110a,
  0x1ccb310de,
  0x1ccb3110e,
  0x1cc43111e,
  0x1cc7300ea,
  0x7210da,
  0x1cc331116,
  0x7120d2,
  0x1ccb31102,
  0x1d0b410de,
  0x1d0b4110e,
  0x1414,
  0x7320ce,
  0x5410c6,
  0x5410d6,
  0x110d210de
]
def labelsBlock76 : Array Nat := #[
  0x443122,
  0x4310ce,
  0x5410ce,
  0x8f9,
  0x1149400ea,
  0x4420f2,
  0x114941116,
  0x1149410fa,
  0x114d4110a,
  0x41310e,
  0x194a4111e,
  0x412032,
  0x114d210de,
  0x114d400ea,
  0x4430f2,
  0x114d41116
]
def labelsBlock77 : Array Nat := #[
  0x114d410fa,
  0x114d41102,
  0x41410e,
  0x194e4111e,
  0x413032,
  0x1151210de,
  0x53105a,
  0x194032116,
  0x1d70,
  0x1c54,
  0x530102,
  0x1c34,
  0x53010a,
  0x15403211e,
  0x1540320f2,
  0x1540320fa
]
def labelsBlock78 : Array Nat := #[
  0x15404310e,
  0x520036,
  0x52003a,
  0x150032032,
  0x1540430de,
  0x8fd,
  0x901,
  0x1540320ea,
  0x154432116,
  0x1544320fa,
  0x531102,
  0x53110a,
  0x15444310e,
  0x19443211e,
  0x521036,
  0x52103a
]
def labelsBlock79 : Array Nat := #[
  0x150432032,
  0x1544430de,
  0x905,
  0x1544320ea,
  0x1544320f2,
  0x154032116,
  0x532102,
  0x53210a,
  0x15484310e,
  0x15443211e,
  0x1548430de,
  0x10d4200ea,
  0x909,
  0x1cd510102,
  0x1cd4200ea,
  0x10c8200ea
]
def labelsBlock80 : Array Nat := #[
  0x5100ce,
  0x1c94300ea,
  0x10c8300ea,
  0x5100d2,
  0x10d5100c6,
  0x90d,
  0x1d60,
  0x4030ca,
  0x3960,
  0x14c110102,
  0x1e60,
  0x1544300c6,
  0x4130d2,
  0x3a60,
  0x14c510102,
  0x14d510102
]
def labelsBlock81 : Array Nat := #[
  0x1940320ea,
  0x911,
  0x915,
  0x18d510102,
  0x5600ca10116,
  0x5610cb1011e,
  0x1d14320ea,
  0x1c1032032,
  0x1d4d40102,
  0x1c144310e,
  0x1d4d4010a,
  0x1d14320f2,
  0x1c5032032,
  0x1d4d41102,
  0x1c544310e,
  0x1d4d4110a
]
def labelsBlock82 : Array Nat := #[
  0x14c530102,
  0x1d40320ea,
  0x1d4530102,
  0x1d4131102,
  0x184c,
  0x182c,
  0x5314c110102
]
def labelsGet (i : Nat) : Nat :=
  if i < 656 then
    if i < 320 then
      if i < 160 then
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
          if i < 112 then
            if i < 96 then
              labelsBlock5.getD (i-80) 3
            else
              labelsBlock6.getD (i-96) 3
          else
            if i < 128 then
              labelsBlock7.getD (i-112) 3
            else
              if i < 144 then
                labelsBlock8.getD (i-128) 3
              else
                labelsBlock9.getD (i-144) 3
      else
        if i < 240 then
          if i < 192 then
            if i < 176 then
              labelsBlock10.getD (i-160) 3
            else
              labelsBlock11.getD (i-176) 3
          else
            if i < 208 then
              labelsBlock12.getD (i-192) 3
            else
              if i < 224 then
                labelsBlock13.getD (i-208) 3
              else
                labelsBlock14.getD (i-224) 3
        else
          if i < 272 then
            if i < 256 then
              labelsBlock15.getD (i-240) 3
            else
              labelsBlock16.getD (i-256) 3
          else
            if i < 288 then
              labelsBlock17.getD (i-272) 3
            else
              if i < 304 then
                labelsBlock18.getD (i-288) 3
              else
                labelsBlock19.getD (i-304) 3
    else
      if i < 480 then
        if i < 400 then
          if i < 352 then
            if i < 336 then
              labelsBlock20.getD (i-320) 3
            else
              labelsBlock21.getD (i-336) 3
          else
            if i < 368 then
              labelsBlock22.getD (i-352) 3
            else
              if i < 384 then
                labelsBlock23.getD (i-368) 3
              else
                labelsBlock24.getD (i-384) 3
        else
          if i < 432 then
            if i < 416 then
              labelsBlock25.getD (i-400) 3
            else
              labelsBlock26.getD (i-416) 3
          else
            if i < 448 then
              labelsBlock27.getD (i-432) 3
            else
              if i < 464 then
                labelsBlock28.getD (i-448) 3
              else
                labelsBlock29.getD (i-464) 3
      else
        if i < 560 then
          if i < 512 then
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
    if i < 992 then
      if i < 816 then
        if i < 736 then
          if i < 688 then
            if i < 672 then
              labelsBlock41.getD (i-656) 3
            else
              labelsBlock42.getD (i-672) 3
          else
            if i < 704 then
              labelsBlock43.getD (i-688) 3
            else
              if i < 720 then
                labelsBlock44.getD (i-704) 3
              else
                labelsBlock45.getD (i-720) 3
        else
          if i < 768 then
            if i < 752 then
              labelsBlock46.getD (i-736) 3
            else
              labelsBlock47.getD (i-752) 3
          else
            if i < 784 then
              labelsBlock48.getD (i-768) 3
            else
              if i < 800 then
                labelsBlock49.getD (i-784) 3
              else
                labelsBlock50.getD (i-800) 3
      else
        if i < 896 then
          if i < 848 then
            if i < 832 then
              labelsBlock51.getD (i-816) 3
            else
              labelsBlock52.getD (i-832) 3
          else
            if i < 864 then
              labelsBlock53.getD (i-848) 3
            else
              if i < 880 then
                labelsBlock54.getD (i-864) 3
              else
                labelsBlock55.getD (i-880) 3
        else
          if i < 944 then
            if i < 912 then
              labelsBlock56.getD (i-896) 3
            else
              if i < 928 then
                labelsBlock57.getD (i-912) 3
              else
                labelsBlock58.getD (i-928) 3
          else
            if i < 960 then
              labelsBlock59.getD (i-944) 3
            else
              if i < 976 then
                labelsBlock60.getD (i-960) 3
              else
                labelsBlock61.getD (i-976) 3
    else
      if i < 1152 then
        if i < 1072 then
          if i < 1024 then
            if i < 1008 then
              labelsBlock62.getD (i-992) 3
            else
              labelsBlock63.getD (i-1008) 3
          else
            if i < 1040 then
              labelsBlock64.getD (i-1024) 3
            else
              if i < 1056 then
                labelsBlock65.getD (i-1040) 3
              else
                labelsBlock66.getD (i-1056) 3
        else
          if i < 1104 then
            if i < 1088 then
              labelsBlock67.getD (i-1072) 3
            else
              labelsBlock68.getD (i-1088) 3
          else
            if i < 1120 then
              labelsBlock69.getD (i-1104) 3
            else
              if i < 1136 then
                labelsBlock70.getD (i-1120) 3
              else
                labelsBlock71.getD (i-1136) 3
      else
        if i < 1232 then
          if i < 1184 then
            if i < 1168 then
              labelsBlock72.getD (i-1152) 3
            else
              labelsBlock73.getD (i-1168) 3
          else
            if i < 1200 then
              labelsBlock74.getD (i-1184) 3
            else
              if i < 1216 then
                labelsBlock75.getD (i-1200) 3
              else
                labelsBlock76.getD (i-1216) 3
        else
          if i < 1280 then
            if i < 1248 then
              labelsBlock77.getD (i-1232) 3
            else
              if i < 1264 then
                labelsBlock78.getD (i-1248) 3
              else
                labelsBlock79.getD (i-1264) 3
          else
            if i < 1296 then
              labelsBlock80.getD (i-1280) 3
            else
              if i < 1312 then
                labelsBlock81.getD (i-1296) 3
              else
                labelsBlock82.getD (i-1312) 3
def lh (s : Nat) (d : List Nat) (ws : List Nat) (i : Nat) : Nat :=
  labelsGet (d.getD (((ws.getD (i / (64 / s)) 0) >>> ((i % (64 / s)) * s)) % 2 ^ s) 0)
def viewsBlock0 : Array View := #[
  ⟨0x404040404040404,⟨2,by decide⟩,0x404040004000000,[ew0,ew1,ew2],3,lh 2 [0,1,2,3] [0xd900]⟩,
  ⟨0x202020202020202,⟨1,by decide⟩,0x202020002000000,[ew3,ew4,ew5],3,fun _ => 3⟩,
  ⟨0xa0a0a0a,⟨1,by decide⟩,0xa080800,[ew6,ew7,ew8],3,fun _ => 3⟩,
  ⟨0xc0c0c0c,⟨2,by decide⟩,0xc080800,[ew6,ew9,ew10],3,fun _ => 3⟩,
  ⟨0xf000f00,⟨8,by decide⟩,0xe000800,[ew7,ew9,ew11],3,fun _ => 3⟩,
  ⟨0xf0f0000,⟨16,by decide⟩,0xe080000,[ew8,ew10,ew11],3,fun _ => 3⟩,
  ⟨0xff0000,⟨16,by decide⟩,0xe80000,[ew12,ew13,ew14],3,fun _ => 3⟩,
  ⟨0x5500550055005500,⟨8,by decide⟩,0x5400440044004000,[ew15,ew16,ew17,ew18],5,lh 3 [4,5,6,7,8] [0x808608408408]⟩,
  ⟨0xa050a050a050a05,⟨0,by decide⟩,0xa040a000a000800,[ew19,ew20,ew21,ew22],5,fun _ => 3⟩,
  ⟨0xff00ff,⟨0,by decide⟩,0xe800e0,[ew23,ew24,ew25,ew26],4,lh 3 [9,10,11,12,13] [0x8d2249000000]⟩,
  ⟨0xaa550000aa55,⟨0,by decide⟩,0xaa400000a840,[ew27,ew28,ew29,ew30],4,fun _ => 3⟩,
  ⟨0xaa55aa55,⟨0,by decide⟩,0xaa40a840,[ew31,ew32,ew33,ew34],4,fun _ => 3⟩,
  ⟨0xf0f0f0f,⟨0,by decide⟩,0xe080800,[ew35,ew36,ew37,ew38],6,lh 3 [14,15,16,17,18] [0x8d2249000000]⟩,
  ⟨0xf00f0000f00f0000,⟨16,by decide⟩,0xf00e0000e0080000,[ew39,ew40,ew41,ew42],6,fun _ => 3⟩,
  ⟨0xf0000f00f0000f00,⟨8,by decide⟩,0xf0000e00e0000800,[ew43,ew44,ew41,ew45],6,fun _ => 3⟩,
  ⟨0xa0a0a0a0a0a0a0a,⟨1,by decide⟩,0xa0a0a000a080800,[ew46,ew19,ew47,ew48],4,lh 3 [19,9,20,21,22] [0x89a249000000]⟩
]
def viewsBlock1 : Array View := #[
  ⟨0x5050505005050505,⟨0,by decide⟩,0x5040404004000000,[ew49,ew50,ew51,ew52],4,fun _ => 3⟩,
  ⟨0x4444444444444444,⟨2,by decide⟩,0x4444444044404040,[ew53,ew15,ew54,ew55],4,lh 3 [23,24,2,25,26] [0x8c9489000000]⟩,
  ⟨0xa0a0a0a00a0a0a0a,⟨1,by decide⟩,0xa0a0a0a00a080800,[ew56,ew57,ew58,ew59],4,fun _ => 3⟩,
  ⟨0x3030303003030303,⟨0,by decide⟩,0x3020202002000000,[ew60,ew61,ew62,ew63],4,fun _ => 3⟩,
  ⟨0xf000f0000f000f00,⟨8,by decide⟩,0xf000e0000e000800,[ew58,ew64,ew65,ew66],6,fun _ => 3⟩,
  ⟨0xf0f000000f0f0000,⟨16,by decide⟩,0xf0e000000e080000,[ew59,ew67,ew68,ew66],6,fun _ => 3⟩,
  ⟨0xff00000000ff0000,⟨16,by decide⟩,0xfe00000000e80000,[ew69,ew70,ew71,ew72],6,fun _ => 3⟩,
  ⟨0xff0000000000ff00,⟨8,by decide⟩,0xfe0000000000e800,[ew73,ew74,ew75,ew72],6,fun _ => 3⟩,
  ⟨0x5555000055550000,⟨16,by decide⟩,0x5444000044400000,[ew54,ew76,ew17,ew77],5,fun _ => 3⟩,
  ⟨0x5555555500000000,⟨32,by decide⟩,0x5444444000000000,[ew55,ew50,ew18,ew77],5,fun _ => 3⟩,
  ⟨0x2222222222222222,⟨1,by decide⟩,0x2222222022202020,[ew78,ew79,ew80,ew81],4,fun _ => 3⟩,
  ⟨0xaaaaaaaa,⟨1,by decide⟩,0xaaa8a8a0,[ew82,ew83,ew31,ew84],4,fun _ => 3⟩,
  ⟨0x3300330033003300,⟨8,by decide⟩,0x3200220022002000,[ew79,ew85,ew86,ew87],5,fun _ => 3⟩,
  ⟨0x3333000033330000,⟨16,by decide⟩,0x3222000022200000,[ew80,ew88,ew86,ew89],5,fun _ => 3⟩,
  ⟨0x3333333300000000,⟨32,by decide⟩,0x3222222000000000,[ew81,ew61,ew87,ew89],5,fun _ => 3⟩,
  ⟨0xf000f000f000f,⟨0,by decide⟩,0xe000000080000,[ew90,ew91,ew92,ew93],4,fun _ => 3⟩
]
def viewsBlock2 : Array View := #[
  ⟨0xf000f000f000f00,⟨8,by decide⟩,0xe000e000e000800,[ew19,ew94,ew95,ew96],4,fun _ => 3⟩,
  ⟨0xf0f00000f0f0000,⟨16,by decide⟩,0xe0e00000e080000,[ew47,ew97,ew95,ew98],4,fun _ => 3⟩,
  ⟨0x1212121212121212,⟨1,by decide⟩,0x1202020002000000,[ew99,ew100,ew101,ew102],6,fun _ => 3⟩,
  ⟨0x5a005a005a005a,⟨1,by decide⟩,0x4a004000480040,[ew103,ew104,ew105,ew106],3,lh 3 [27,28,16,9,29] [0x851651000000]⟩,
  ⟨0x5a005a005a005a00,⟨9,by decide⟩,0x5a004a004a004800,[ew16,ew107,ew108,ew109],4,fun _ => 3⟩,
  ⟨0x5a5a00005a5a,⟨1,by decide⟩,0x4a4000004840,[ew110,ew111,ew112,ew113],3,fun _ => 3⟩,
  ⟨0x5a5a00005a5a0000,⟨17,by decide⟩,0x5a4a00004a480000,[ew76,ew114,ew108,ew115],4,fun _ => 3⟩,
  ⟨0x5a5a5a5a,⟨1,by decide⟩,0x4a484840,[ew116,ew117,ew118,ew119],5,lh 3 [21,16,9,28,30] [0x8c9000489000]⟩,
  ⟨0x5a5a5a5a00000000,⟨33,by decide⟩,0x5a4a4a4000000000,[ew50,ew120,ew109,ew115],5,lh 3 [7,31,32,33,34] [0x8c9489000000]⟩,
  ⟨0x55aa55aa,⟨1,by decide⟩,0x44a840a0,[ew121,ew122,ew123,ew124],3,lh 3 [35,10,16,9,36] [0x810208610208]⟩,
  ⟨0x1111111122222222,⟨1,by decide⟩,0x1000000022202020,[ew125,ew126,ew127,ew128],4,fun _ => 3⟩,
  ⟨0x50505050a0a0a0a,⟨1,by decide⟩,0x40404000a080800,[ew129,ew130,ew131,ew132],4,fun _ => 3⟩,
  ⟨0x55005500aa00aa,⟨1,by decide⟩,0x44004000a800a0,[ew133,ew134,ew135,ew136],3,fun _ => 3⟩,
  ⟨0x55005500aa00aa00,⟨9,by decide⟩,0x54004400aa00a800,[ew18,ew137,ew138,ew139],4,fun _ => 3⟩,
  ⟨0x55550000aaaa,⟨1,by decide⟩,0x44400000a8a0,[ew140,ew141,ew142,ew143],3,fun _ => 3⟩,
  ⟨0x55550000aaaa0000,⟨17,by decide⟩,0x54440000aaa80000,[ew77,ew144,ew145,ew139],4,fun _ => 3⟩
]
def viewsBlock3 : Array View := #[
  ⟨0x1414141414141414,⟨2,by decide⟩,0x1404040004000000,[ew99,ew146,ew147,ew148],6,fun _ => 3⟩,
  ⟨0xaa55aa55aa55aa55,⟨0,by decide⟩,0xaa44aa40aa40a840,[ew149,ew150,ew151,ew152,ew153],7,lh 3 [14,37,25,11,19,38] [0x859451000000,0x14b28a200]⟩,
  ⟨0xaaaa5555aaaa5555,⟨0,by decide⟩,0xaaaa4440aaa84040,[ew154,ew155,ew156,ew157,ew158],7,fun _ => 3⟩,
  ⟨0xcc33cc33cc33cc33,⟨0,by decide⟩,0xcc22cc20cc20c820,[ew159,ew160,ew161,ew162,ew163],7,fun _ => 3⟩,
  ⟨0xcccc3333cccc3333,⟨0,by decide⟩,0xcccc2220ccc82020,[ew164,ew165,ew166,ew167,ew168],7,fun _ => 3⟩,
  ⟨0xf00ff00ff00ff00f,⟨0,by decide⟩,0xf00ee000e008e000,[ew169,ew170,ew171,ew172,ew173],7,lh 3 [27,39,40,16,7,41] [0x1451000000000000,0x14b28a30b]⟩,
  ⟨0xf0f00f0ff0f00f0f,⟨0,by decide⟩,0xf0e00e00e0e00800,[ew174,ew175,ew176,ew177,ew178],7,fun _ => 3⟩,
  ⟨0xf0f0f0f00f0f0f0f,⟨0,by decide⟩,0xf0e0e0e00e080800,[ew179,ew180,ew181,ew182,ew183],8,lh 3 [42,21,20,43,14,44] [0x10008d2000249000,0x15a400049]⟩,
  ⟨0xff00ff0000ff00ff,⟨0,by decide⟩,0xfe00ee0000e800e0,[ew184,ew185,ew186,ew187,ew188],7,lh 3 [45,10,9,11,46,47] [0x492249000000,0x163649200]⟩,
  ⟨0xffff00000000ffff,⟨0,by decide⟩,0xfeee00000000e8e0,[ew189,ew190,ew191,ew192,ew193],7,fun _ => 3⟩,
  ⟨0x5555555555555555,⟨0,by decide⟩,0x5444444044404040,[ew194,ew195,ew196,ew197,ew198],7,lh 3 [23,24,2,48,25,49] [0x2249000000000000,0x15c649292]⟩,
  ⟨0xaaaaaaaaaaaaaaaa,⟨1,by decide⟩,0xaaaaaaa0aaa8a8a0,[ew199,ew200,ew149,ew154,ew201],5,lh 3 [19,9,20,21,10,50] [0x1249000000000000,0x1544d3449]⟩,
  ⟨0x3333333333333333,⟨0,by decide⟩,0x3222222022202020,[ew202,ew203,ew204,ew205,ew206],7,fun _ => 3⟩,
  ⟨0xcccccccccccccccc,⟨2,by decide⟩,0xccccccc0ccc8c8c0,[ew199,ew207,ew160,ew165,ew208],5,fun _ => 3⟩,
  ⟨0xf0f0f0f0f0f0f0f,⟨0,by decide⟩,0xe0e0e000e080800,[ew209,ew210,ew211,ew212,ew213],7,lh 3 [43,21,14,16,19,51] [0x208818208410208,0x143041082]⟩,
  ⟨0xff00ff00ff00ff,⟨0,by decide⟩,0xee00e000e800e0,[ew214,ew215,ew216,ew217,ew218],5,lh 3 [12,27,9,11,10,52] [0x410208208208208,0x143103082]⟩
]
def viewsBlock4 : Array View := #[
  ⟨0xff00ff00ff00ff00,⟨8,by decide⟩,0xfe00ee00ee00e800,[ew149,ew160,ew171,ew219,ew187],7,lh 3 [19,14,53,43,20,54] [0x1249000000000000,0x15c692449]⟩,
  ⟨0xffff0000ffff,⟨0,by decide⟩,0xeee00000e8e0,[ew220,ew221,ew222,ew223,ew224],5,fun _ => 3⟩,
  ⟨0xffff0000ffff0000,⟨16,by decide⟩,0xfeee0000eee80000,[ew154,ew165,ew176,ew219,ew193],7,fun _ => 3⟩,
  ⟨0xffffffff,⟨0,by decide⟩,0xeee8e8e0,[ew225,ew226,ew227,ew228,ew229],7,lh 3 [21,48,53,43,2,51] [0x8c9489000000,0x159291200]⟩,
  ⟨0xffffffff00000000,⟨32,by decide⟩,0xfeeeeee000000000,[ew201,ew208,ew181,ew187,ew193],6,lh 3 [55,56,57,58,59,60] [0x1249000000000000,0x15a51a449]⟩,
  ⟨0x5a5a5a5a5a5a5a5a,⟨1,by decide⟩,0x5a4a4a404a484840,[ew195,ew230,ew231,ew232,ew233],8,lh 3 [19,9,21,28,11,61] [0x1249000000000000,0x15c692449]⟩,
  ⟨0x55555555aaaaaaaa,⟨1,by decide⟩,0x54444440aaa8a8a0,[ew198,ew234,ew235,ew236,ew237],7,lh 3 [62,9,20,21,10,63] [0x610208208208208,0x1421020c2]⟩,
  ⟨0x3c3c3c3c3c3c3c3c,⟨2,by decide⟩,0x3c2c2c202c282820,[ew238,ew203,ew239,ew240,ew241],8,fun _ => 3⟩,
  ⟨0x33333333cccccccc,⟨2,by decide⟩,0x32222220ccc8c8c0,[ew242,ew206,ew243,ew244,ew245],7,fun _ => 3⟩,
  ⟨0xffffffffffffffff,⟨0,by decide⟩,0xfeeeeee0eee8e8e0,[ew246,ew247,ew248,ew249,ew250,ew251],10,lh 4 [46,16,64,7,10,65,19,21,66] [0x3010321230103212,0x6010401050105010,0x3010321230103212,0x8010401070104010]⟩
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
      if i < 64 then
        viewsBlock3[(i-48)]?
      else
        viewsBlock4[(i-64)]?
def nodesBlock0 : Array Node := #[
  ⟨0,3,[ew0,ew1,ew2],lh 3 [1,67,0,23,24,2] [0x483112144265808,0x1522c946b71b]⟩,
  ⟨7,5,[ew15,ew16,ew17,ew18],lh 6 [5,2,23,6,70,4,7,48,71,93,68,69,72,73,74,75,76,77,78,79,80,81,82,83,84,85,86,87,88,89,90,91,92,94,95,96,97,98,99] [0x30810b285005,0x4081883c510e348,0x53487187447047,0x5c50965470c3508,0x416870996050c5,0x7400417001806c4,0xc07c4082784184,0x8840c9840089800,0x829060c38c1082,0x9810c1946]⟩,
  ⟨7,4,[ew252,ew15,ew16,ew17,ew18],lh 4 [4,5,6,7,23,71,70,100,101,102,103,69,48,85,2] [0x1ba29283736150,0x42114311ed00203c,0x232]⟩,
  ⟨7,4,[ew15,ew16,ew253,ew17,ew18],lh 4 [6,7,23,2,4,104,5,69,71,70,105,106,107,108] [0x3662020315544987,0x20d0c1b1a0202131,0x10]⟩,
  ⟨7,4,[ew0,ew15,ew16,ew17,ew18],lh 4 [6,5,23,7,2,4,104,70,71,74] [0x6981202043437155,0x2011231142020436,0x30]⟩,
  ⟨7,4,[ew254,ew15,ew16,ew17,ew18],lh 4 [23,2,6,4,70,7,71,5,74] [0x3843202051517463,0x402041510302151,0x102]⟩,
  ⟨7,4,[ew255,ew15,ew16,ew17,ew18],lh 4 [23,70,71,5,2,4,6,48,109,110,111,112,104,7] [0x1225b0a044918172,0x1030133105022dc,0x606]⟩,
  ⟨7,4,[ew15,ew16,ew17,ew256,ew18],lh 4 [23,48,70,2,5,6,104,71,113,114,7,115,116] [0x3431501713161421,0xb3050a3204092282,0xc0]⟩,
  ⟨7,4,[ew257,ew15,ew16,ew17,ew18],lh 4 [23,48,5,70,6,2,71,7,79] [0x1231040455323261,0x302032231401817,0x404]⟩,
  ⟨7,4,[ew258,ew15,ew16,ew17,ew18],lh 4 [23,6,5,70,2,71,48,7,4,79] [0x3558101074232366,0x122032240101945,0x101]⟩,
  ⟨7,4,[ew259,ew15,ew16,ew17,ew18],lh 4 [5,7,6,48,2,4,117,118,119,120,23,71,79,82,70] [0x30b0a29181706053,0x4200e100432dc131,0x212]⟩,
  ⟨7,4,[ew15,ew16,ew17,ew18,ew260],lh 4 [5,4,7,2,23,70,6,82,48,121,122,123,124] [0x38141712311051,0x22b3224a00950042,0x66c]⟩,
  ⟨7,4,[ew261,ew15,ew16,ew17,ew18],lh 4 [5,4,7,2,6,70,48,23,85] [0x1051743232505061,0x3400520038141231,0x424]⟩,
  ⟨7,4,[ew262,ew15,ew16,ew17,ew18],lh 4 [5,7,2,70,48,23,4,6,71,79,85] [0x4080771212030366,0x530051002a549141,0x211]⟩,
  ⟨7,4,[ew15,ew263,ew16,ew17,ew18],lh 4 [125,4,23,6,70,5,7,82,85,126,2] [0x870100110011001,0x242344a932326655,0x323]⟩,
  ⟨7,4,[ew15,ew16,ew17,ew264,ew18],lh 4 [125,4,23,6,5,7,70,82,85,126,2] [0x870100110011001,0x23232a5344266549,0x323]⟩
]
def nodesBlock1 : Array Node := #[
  ⟨7,4,[ew265,ew15,ew16,ew17,ew18],lh 4 [71,23,2,125,70,4,5,6,7,127,128,85,129] [0x5005a19182440303,0x17161c620b100320,0x217]⟩,
  ⟨7,4,[ew266,ew15,ew16,ew17,ew18],lh 4 [48,23,71,7,6,70,2,5,130,131,85,129] [0x220918166750202,0x14141b350a102303,0x434]⟩,
  ⟨7,4,[ew15,ew267,ew16,ew17,ew18],lh 4 [132,48,7,2,70,6,23,5,133] [0x1001021010011001,0x6468232355232374,0x322]⟩,
  ⟨7,4,[ew15,ew16,ew17,ew18,ew268],lh 4 [132,5,48,7,6,2,133,70,23] [0x2002200403202101,0x3354345714163115,0x845]⟩,
  ⟨7,4,[ew269,ew15,ew16,ew17,ew18],lh 4 [132,5,7,48,71,6,2,23,70,134,135,93] [0x310155a292814040,0x7b17211630030230,0x622]⟩,
  ⟨7,4,[ew270,ew15,ew16,ew17,ew18],lh 4 [4,7,6,132,2,5,48,136,137,23,70,93] [0x330928171550303,0x4b2a141460020160,0x212]⟩,
  ⟨7,4,[ew15,ew16,ew271,ew17,ew18],lh 4 [4,5,138,70,48,2,23,93,7,6,132,139] [0x42240220022001a0,0x9988771631153113,0x56b]⟩,
  ⟨7,4,[ew15,ew16,ew17,ew18,ew272],lh 4 [138,5,70,6,4,71,7,132,48,139,2,23] [0x5005800340040170,0x6369211221122112,0xb3a]⟩,
  ⟨7,4,[ew273,ew15,ew16,ew17,ew18],lh 4 [70,138,23,5,48,2,4,140,141,6,7,142] [0x301925580704141,0x232033021246116,0xba2]⟩,
  ⟨7,4,[ew274,ew15,ew16,ew17,ew18],lh 4 [70,138,2,5,4,23,6,143,144,7,48,142] [0x301559280704141,0x3300232a1162124,0xb62]⟩,
  ⟨7,3,[ew15,ew16,ew275,ew18],lh 3 [4,104,5,6,7,23,2] [0x5695896201048048,0xe3]⟩,
  ⟨7,3,[ew276,ew15,ew16,ew18],lh 4 [4,5,6,7,104,23,2,71,85] [0x170232513163044,0x21158002]⟩,
  ⟨7,3,[ew15,ew16,ew17,ew277],lh 4 [4,5,6,7,23,69,48,85,2] [0x3118700203600150,0x23242114]⟩,
  ⟨7,3,[ew278,ew15,ew16,ew17],lh 4 [5,6,4,7,23,69,104,85,2] [0x2055311401042721,0x30082366]⟩,
  ⟨7,3,[ew15,ew16,ew279,ew18],lh 4 [6,4,7,23,69,104,5,71,85,2] [0x6629811012551744,0x2030303]⟩,
  ⟨7,3,[ew280,ew15,ew16,ew18],lh 3 [5,6,7,23,2,104,69,48] [0x3e59e36651810b62,0x40]⟩
]
def nodesBlock2 : Array Node := #[
  ⟨7,3,[ew15,ew16,ew281,ew17],lh 4 [6,7,23,2,69,4,104,5,71,48] [0x7702316655209844,0x10021313]⟩,
  ⟨7,3,[ew282,ew15,ew16,ew17],lh 3 [5,4,6,23,7,69,104,2] [0x733622d694610459,0x100]⟩,
  ⟨7,3,[ew15,ew283,ew17,ew18],lh 4 [23,71,4,48,69,70,5,2,6] [0x7765020114413312,0x80805060]⟩,
  ⟨7,3,[ew284,ew15,ew17,ew18],lh 3 [48,23,2,71,5,70,4,6] [0x1188403a61aa2618,0x8f]⟩,
  ⟨7,3,[ew15,ew16,ew17,ew285],lh 4 [71,23,70,5,48,4,104,7,6,2] [0x2332441007602005,0x91812131]⟩,
  ⟨7,3,[ew286,ew15,ew16,ew17],lh 3 [48,23,2,71,5,70,4,6] [0x24030d82b9361c08,0x154]⟩,
  ⟨7,3,[ew15,ew287,ew17,ew18],lh 4 [48,23,2,70,5,71,104,4,6] [0x3242071020060530,0x21813141]⟩,
  ⟨7,3,[ew288,ew15,ew17,ew18],lh 3 [48,23,2,71,70,5,6] [0x118840334c5540c3,0x8e]⟩,
  ⟨7,3,[ew15,ew16,ew17,ew289],lh 3 [48,23,2,71,5,70,4,6] [0x1a61aa21884030d8,0x8f]⟩,
  ⟨7,3,[ew290,ew15,ew16,ew17],lh 3 [48,23,2,70,5,4,6,104] [0x2407118391319045,0xd4]⟩,
  ⟨7,3,[ew15,ew291,ew17,ew18],lh 4 [5,6,7,4,48,2,71,79,82,70] [0x2005418172423360,0x12151009]⟩,
  ⟨7,3,[ew292,ew15,ew17,ew18],lh 4 [4,5,7,6,23,48,82,71,2] [0x250311421181070,0x32345066]⟩,
  ⟨7,3,[ew15,ew16,ew293,ew18],lh 4 [5,6,48,7,4,82,2,71,70] [0x3006215544232070,0x13161008]⟩,
  ⟨7,3,[ew294,ew15,ew16,ew18],lh 4 [4,5,7,6,48,23,82,2,71] [0x180323512172040,0x31154066]⟩,
  ⟨7,3,[ew15,ew295,ew17,ew18],lh 4 [4,5,7,48,82,2,23,70,6] [0x2115304402300170,0x52268116]⟩,
  ⟨7,3,[ew296,ew15,ew17,ew18],lh 3 [5,4,7,6,23,2,82,48] [0x48762a9803a023c8,0xd3]⟩
]
def nodesBlock3 : Array Node := #[
  ⟨7,3,[ew15,ew16,ew297,ew18],lh 4 [4,5,7,23,2,82,6,71,70] [0x2114305502400170,0x66238113]⟩,
  ⟨7,3,[ew298,ew15,ew16,ew18],lh 4 [4,5,7,6,79,23,82,2,70] [0x180532371210402,0x31154066]⟩,
  ⟨7,3,[ew15,ew263,ew264,ew18],lh 3 [125,4,5,23,6,82,85,129] [0x38e24fa1a8201201,0x4]⟩,
  ⟨7,3,[ew15,ew16,ew17,ew299],lh 4 [71,23,2,4,125,5,129,70,6] [0x6252100404203003,0x21817151]⟩,
  ⟨7,3,[ew15,ew16,ew17,ew300],lh 4 [71,23,2,70,5,4,125,85,6] [0x3242071006203005,0x21813141]⟩,
  ⟨7,3,[ew15,ew16,ew17,ew301],lh 3 [48,71,23,70,5,129,6,2] [0x26a2763201201048,0x1d6]⟩,
  ⟨7,3,[ew15,ew16,ew302,ew17],lh 3 [48,71,23,7,2,85,6,70] [0x271ceb2201150048,0xe3]⟩,
  ⟨7,3,[ew15,ew267,ew17,ew268],lh 3 [5,132,48,7,2,93,23] [0x37a860444a2d1408,0x4]⟩,
  ⟨7,3,[ew15,ew16,ew303,ew18],lh 3 [5,132,48,7,6,23,93,2] [0x5d8560744c2d1408,0x11c]⟩,
  ⟨7,3,[ew15,ew16,ew304,ew18],lh 3 [5,132,48,7,23,93,6,2] [0x4b4460744a2d1408,0x1b3]⟩,
  ⟨7,3,[ew15,ew16,ew305,ew18],lh 4 [4,5,132,6,2,7,93,48,70] [0x5114700320020120,0x35346618]⟩,
  ⟨7,3,[ew15,ew306,ew16,ew18],lh 4 [4,6,7,48,132,5,23,93,2] [0x5528300104400230,0x77161216]⟩,
  ⟨7,3,[ew15,ew16,ew271,ew272],lh 4 [138,5,4,71,6,93,132,70,23,142] [0x4117300320020160,0x945518]⟩,
  ⟨7,3,[ew15,ew307,ew17,ew18],lh 3 [23,138,70,5,4,6,2,142] [0x418d9a04584c4d1,0x1c5]⟩,
  ⟨7,3,[ew15,ew308,ew17,ew18],lh 3 [23,2,70,138,5,4,48,7] [0x4204610c62cd513,0x47]⟩,
  ⟨7,3,[ew15,ew309,ew17,ew18],lh 4 [2,138,70,4,6,5,23,48,142] [0x2050711401032321,0x8406652]⟩
]
def nodesBlock4 : Array Node := #[
  ⟨7,3,[ew15,ew310,ew17,ew18],lh 3 [23,2,70,138,5,6,4] [0x4204610c52ce513,0x45]⟩,
  ⟨12,6,[ew35,ew36,ew37,ew38],lh 5 [14,15,16,17,24,2,147,48,148,145,150,152,9,43,20,21,146,149,151,153,154,155] [0x40ce330c42824e7,0x3242188c8432442,0x934a530c2152484,0x3340058ca530c00,0x51c2141c8498821,0x408a2a380040882,0xabd8c438a558800,0x53c005858150400]⟩,
  ⟨12,5,[ew6,ew35,ew36,ew37,ew38],lh 5 [14,15,147,24,2,145,48,9,21,148,17,16,150,152,156,157,158,159,160,161,162,163] [0x1096232c49508aa,0x7a10c0858843821,0x89ced001a73c000,0x90c651152630842,0x99082084a319421,0xa0422000a421400,0xa800918cc109863,0x41ce9210c001884,0x80002708400]⟩,
  ⟨12,5,[ew7,ew35,ew36,ew37,ew38],lh 5 [14,16,147,2,17,24,20,48,150,9,148,15,152,145,156,164,165,166,160,167,168,169] [0x518ce0844868884,0x109622ade632821,0x8800c18d8004063,0x10424390810c8e7,0x98c641110528842,0xd0220008319000,0x30001284e839ca5,0xaa52618c2000461,0x8000a929400]⟩,
  ⟨12,5,[ew8,ew35,ew36,ew37,ew38],lh 5 [15,16,147,24,48,2,43,152,20,21,17,148,150,14,158,170,165,171,161,167,172,173] [0x5842e21047508ca,0x6001018de10ac84,0x109a22b62003063,0x10426210c10c884,0x1000618cc004c63,0x8006118e528842,0x451011848001063,0x4d52829427084a1,0x929407000a0]⟩,
  ⟨12,5,[ew35,ew9,ew36,ew37,ew38],lh 5 [14,17,16,15,2,148,43,145,147,150,9,152,156,174,162,168,48,24,175,176,177,178] [0xa026698c830581,0x388412842211dc7,0x8c6749ce3185e1,0x300012102001884,0x2962818ca982042,0x9908b0016424800,0xa000228923194a5,0xaa9452104000882,0x90006a18c00]⟩,
  ⟨12,5,[ew35,ew10,ew36,ew37,ew38],lh 5 [15,17,24,14,145,148,20,147,152,43,21,16,150,158,179,163,172,175,180,2,177,181] [0x21c8170427091a4,0x2188128426091e4,0x80041088000442,0x48c61404231a609,0x60851000a859ccb,0x2966718e4213000,0x28846000c215000,0x5554629903194a5,0xa18c0800063]⟩,
  ⟨12,5,[ew35,ew36,ew11,ew37,ew38],lh 5 [16,17,48,145,150,9,21,147,152,43,20,148,15,14,165,182,169,173,175,183,178,181] [0x180011042000c42,0x9c2378c67185c1,0x982320c6618601,0x494a1404250a629,0x2c029884b10240,0x18022084610280,0x514a04000502aaa,0x211a72b48861ccc,0x62190529084]⟩,
  ⟨12,4,[ew311,ew35,ew36,ew37,ew38],lh 4 [14,15,16,24,2,17,43,20,21,152,184,48,9] [0x13252ba090817265,0xc40202131040413,0x1]⟩,
  ⟨12,4,[ew312,ew35,ew36,ew37,ew38],lh 3 [14,16,17,48,145,9,2,15] [0x488a2c517f6598a2,0xa2e0416c8c32]⟩,
  ⟨12,4,[ew313,ew35,ew36,ew37,ew38],lh 4 [15,14,24,2,17,16,48,150,185,9,43,145,21] [0x2b6a69180705544,0x1c31312020131302,0x10]⟩,
  ⟨12,4,[ew314,ew35,ew36,ew37,ew38],lh 4 [15,48,145,24,43,21,9,17,16,20,14] [0x41aa050519882477,0x1930306224030321,0x500661]⟩,
  ⟨12,4,[ew6,ew7,ew36,ew37,ew38],lh 4 [14,24,17,2,48,148,145,16,9,15,150,186] [0x54802021a1772652,0x3030141b03039964,0x108]⟩,
  ⟨12,4,[ew6,ew8,ew36,ew37,ew38],lh 4 [15,2,24,48,145,148,17,16,43,21,14,152,187] [0x5381b19080776654,0x131c2020aa020243,0x1009]⟩,
  ⟨12,4,[ew6,ew35,ew9,ew37,ew38],lh 4 [14,15,16,2,48,147,9,145,17,150,186,24] [0x5460202191245282,0x3030b10303171a74,0x106]⟩,
  ⟨12,4,[ew6,ew35,ew10,ew37,ew38],lh 4 [15,14,24,48,17,147,16,20,21,145,152,187,2] [0x5371a18070665344,0xc12020191b020293,0x1018]⟩
]
def nodesBlock5 : Array Node := #[
  ⟨12,4,[ew315,ew35,ew36,ew37,ew38],lh 3 [14,15,24,2,145,17,16,9] [0x22a5b18611476b2c,0x23b0c2288619]⟩,
  ⟨12,4,[ew316,ew35,ew36,ew37,ew38],lh 4 [16,2,17,24,15,14,48,9,145,148,188,43,20] [0xb302065544a09082,0x17100c0630712123,0x13]⟩,
  ⟨12,4,[ew317,ew35,ew36,ew37,ew38],lh 4 [16,14,17,24,43,20,15,21,48,145,2] [0x8a1376605052429,0x108301214234302,0x131751]⟩,
  ⟨12,4,[ew7,ew8,ew36,ew37,ew38],lh 4 [16,2,17,24,150,43,20,15,48,14,145,152,189] [0x851b1776050a242,0x1006083099234302,0x131c]⟩,
  ⟨12,4,[ew7,ew35,ew9,ew36,ew38],lh 4 [14,15,2,16,24,147,17,145,148,186,48] [0x5401021381145171,0x2020a30202363964,0x2030]⟩,
  ⟨12,4,[ew7,ew35,ew36,ew11,ew38],lh 4 [16,17,24,9,20,147,15,48,14,145,152,21,189] [0x7b3a36652404091,0x40720311c125201,0x8830]⟩,
  ⟨12,4,[ew318,ew35,ew36,ew37,ew38],lh 4 [14,15,16,24,2,17,145,43,48,21] [0x2640403131827655,0x2021310404131327,0x10940]⟩,
  ⟨12,4,[ew319,ew35,ew36,ew37,ew38],lh 4 [16,15,17,2,48,9,43,14,145,24,20] [0x435779140406282,0xa01415323161202,0x311530]⟩,
  ⟨12,4,[ew8,ew35,ew10,ew36,ew37],lh 4 [14,15,24,2,43,147,20,16,17,148,187] [0x5310020690035080,0x2131771212644a43,0x2121]⟩,
  ⟨12,4,[ew8,ew35,ew36,ew11,ew37],lh 4 [16,48,2,43,17,147,14,9,21,15,150,189] [0x178a76652010144,0x100120833b325201,0x9901]⟩,
  ⟨12,4,[ew320,ew35,ew36,ew37,ew38],lh 3 [14,15,16,24,2,48,17,9] [0x32d554410b2d5576,0x23c0822c8821]⟩,
  ⟨12,4,[ew35,ew321,ew36,ew37,ew38],lh 4 [14,15,17,16,145,9,147,190,43,48,24,2,20] [0x208141232342762,0x5503031c1b0a193,0x1]⟩,
  ⟨12,4,[ew322,ew35,ew36,ew37,ew38],lh 4 [15,16,17,2,43,20,21,14,145,48,24] [0x1877060a15192424,0x1510504323080212,0x300631]⟩,
  ⟨12,4,[ew35,ew9,ew10,ew37,ew38],lh 4 [14,15,17,16,43,145,150,48,24,152,20,2,191] [0x204151232352442,0xb03161a090817363,0x10c]⟩,
  ⟨12,4,[ew35,ew9,ew36,ew11,ew38],lh 4 [17,16,15,9,43,145,148,14,48,24,152,21,191] [0x3004252010150440,0x1c1262b3a3926281,0x7731]⟩,
  ⟨12,4,[ew323,ew35,ew36,ew37,ew38],lh 4 [14,15,24,2,17,16,48,20,145,21] [0x4603031212765584,0x3021210303121274,0x10930]⟩
]
def nodesBlock6 : Array Node := #[
  ⟨12,4,[ew324,ew35,ew36,ew37,ew38],lh 4 [14,16,17,145,24,9,20,15,48,2,43] [0x1305097761813232,0x101641020a243412,0x40550]⟩,
  ⟨12,4,[ew35,ew10,ew36,ew11,ew37],lh 4 [145,17,14,20,16,148,9,21,2,150,191,15] [0x1001202101100110,0x3a32526796825244,0xb273]⟩,
  ⟨12,4,[ew325,ew35,ew36,ew37,ew38],lh 4 [16,2,48,24,9,17,15,21,14,145,20] [0x241887366020255,0xa02304191739302,0x131410]⟩,
  ⟨12,4,[ew326,ew35,ew36,ew37,ew38],lh 4 [14,15,17,145,9,48,16,21,24,2,43] [0x2540907181662323,0x507151020a131232,0x10440]⟩,
  ⟨12,3,[ew327,ew35,ew36,ew37],lh 3 [14,15,16,2,24,9,48,17] [0x130c5d62050d0603,0x8c]⟩,
  ⟨12,3,[ew328,ew35,ew36,ew38],lh 3 [14,15,16,24,2,9,48,17] [0x1045d604529964b,0x102]⟩,
  ⟨12,3,[ew6,ew7,ew9,ew38],lh 3 [14,15,16,2,147,24,148,9] [0x43361e10562471,0xc3]⟩,
  ⟨12,3,[ew6,ew8,ew10,ew37],lh 4 [14,15,2,147,16,24,148,17,43,21] [0x230918144327060,0x51211005]⟩,
  ⟨12,3,[ew329,ew35,ew37,ew38],lh 3 [14,15,16,24,2,48,17,9] [0x71042cb810459c95,0x8]⟩,
  ⟨12,3,[ew7,ew8,ew36,ew11],lh 4 [16,17,2,147,15,48,14,150,145,43,20] [0x1054432a0908171,0x5206632]⟩,
  ⟨12,3,[ew330,ew36,ew37,ew38],lh 3 [14,15,16,24,2,48,17,9] [0x78104591042cb595,0x8]⟩,
  ⟨12,3,[ew35,ew9,ew10,ew11],lh 4 [14,16,17,43,145,148,150,48,24] [0x7161040212142332,0x10508050]⟩,
  ⟨35,3,[ew103,ew104,ew105,ew106],lh 4 [28,11,27,16,9,195,192,193,194] [0x1331027204601003,0x55241281]⟩,
  ⟨39,5,[ew116,ew117,ew118,ew119],lh 5 [147,196,28,16,21,14,11,9,15,20,211,197,198,199,200,201,202,203,204,205,206,207,208,209,210,212,213] [0x862008c600463,0x40100882004c1,0x8e20080200481,0x802004e100401,0x725096a48c58d03,0x98cf2898a58188f,0xb90e4b18f5a0ca5,0xd10aaca0eac20a5]⟩,
  ⟨39,4,[ew331,ew117,ew116,ew118,ew119],lh 4 [9,28,15,11,196,16,20,214,147,21,215,216,198,211] [0x1334b0a092817165,0x10401242050332c,0xd02]⟩,
  ⟨39,4,[ew117,ew116,ew118,ew332,ew119],lh 4 [14,28,20,196,9,11,15,198,21,147,217,218,219] [0x3314042558272312,0xb0404661030a1191,0xc0]⟩
]
def nodesBlock7 : Array Node := #[
  ⟨39,4,[ew333,ew117,ew116,ew118,ew119],lh 4 [14,9,196,28,15,20,11,21,201] [0x5235101074323266,0x1302034241010854,0x10]⟩,
  ⟨39,4,[ew334,ew117,ew116,ew118,ew119],lh 4 [14,28,196,9,11,15,20,21,201] [0x1442030355212164,0x3102012213030874,0x30]⟩,
  ⟨39,4,[ew335,ew117,ew116,ew118,ew119],lh 4 [28,21,20,14,11,224,16,220,147,221,222,9,204,223,211] [0x2402b3a191807064,0x1035501d023c1224,0x1e3]⟩,
  ⟨39,4,[ew117,ew116,ew118,ew119,ew336],lh 4 [15,28,21,196,16,225,9,20,204,223,147,226,227,228,14] [0x907764820245514,0xc2002b33a13311,0xe6d]⟩,
  ⟨39,4,[ew337,ew117,ew116,ew118,ew119],lh 4 [21,28,16,196,15,14,11,9,207] [0x2312750404131362,0x153110308250402,0x45]⟩,
  ⟨39,4,[ew338,ew117,ew116,ew118,ew119],lh 4 [28,21,196,15,11,9,16,14,207] [0x402773131202066,0x1052001208541314,0x153]⟩,
  ⟨39,4,[ew117,ew116,ew339,ew118,ew119],lh 4 [28,125,16,21,196,11,9,14,207,15,229] [0x8115311221120502,0x7793064003400440,0x36a]⟩,
  ⟨39,4,[ew117,ew116,ew118,ew119,ew340],lh 4 [125,28,196,14,16,11,21,229,15,9] [0x5005500340041004,0x6387122113211221,0x936]⟩,
  ⟨39,4,[ew341,ew117,ew116,ew118,ew119],lh 4 [20,125,15,28,14,196,230,147,21,16,223,9,211] [0x110448273630101,0x355332a201109202,0xc2b]⟩,
  ⟨39,4,[ew342,ew117,ew116,ew118,ew119],lh 4 [196,20,28,16,125,15,14,21,231,147,9,211] [0x1040a65590803131,0x2002200214417113,0xb67]⟩,
  ⟨39,3,[ew117,ew343,ew118,ew119],lh 4 [15,196,28,16,20,11,198,9,211] [0x2010533530604421,0x80072112]⟩,
  ⟨39,3,[ew117,ew116,ew118,ew344],lh 3 [9,11,15,196,28,198,20,211] [0x81889a1812a984b,0x1c2]⟩,
  ⟨39,3,[ew345,ew117,ew116,ew118],lh 4 [9,11,15,20,196,28,16,211,198] [0x3113072005406001,0x52421381]⟩,
  ⟨39,3,[ew346,ew117,ew118,ew119],lh 3 [14,11,9,20,28,196,15,198] [0x24102f9144dac659,0x10]⟩,
  ⟨39,3,[ew117,ew116,ew118,ew347],lh 3 [14,11,9,20,28,196,198] [0x282896c4102f164b,0x10]⟩,
  ⟨39,3,[ew348,ew117,ew116,ew118],lh 3 [14,9,211,28,196,20,198,21] [0x2eb2b1d201118048,0xd4]⟩
]
def nodesBlock8 : Array Node := #[
  ⟨39,3,[ew117,ew349,ew118,ew119],lh 4 [14,11,16,201,15,196,21,20,198,204,28,9,211] [0xa454109033812217,0x6c06b050]⟩,
  ⟨39,3,[ew117,ew116,ew350,ew119],lh 4 [21,11,14,28,20,204,16,223,224,9] [0x3070125506014114,0x9203283]⟩,
  ⟨39,3,[ew351,ew117,ew116,ew119],lh 4 [21,28,16,14,9,204,224,201,223,11] [0x1912043001817002,0x13664255]⟩,
  ⟨39,3,[ew352,ew117,ew118,ew119],lh 4 [196,15,21,28,204,225,20,224,16,232] [0x2121700310030650,0x21129844]⟩,
  ⟨39,3,[ew117,ew116,ew353,ew119],lh 4 [196,15,28,21,232,204,20,16,11] [0x2001875561314420,0x31132002]⟩,
  ⟨39,3,[ew354,ew117,ew116,ew119],lh 4 [196,15,21,28,11,20,225,204,16,224] [0x6030211210304421,0x30095875]⟩,
  ⟨39,3,[ew117,ew116,ew339,ew340],lh 4 [125,28,16,196,21,11,207,14,211] [0x1731600520021002,0x841431]⟩,
  ⟨39,3,[ew117,ew355,ew118,ew119],lh 4 [20,28,16,125,9,15,196,21,14,211] [0x1761033020021002,0x95541481]⟩,
  ⟨39,3,[ew117,ew356,ew118,ew119],lh 4 [196,20,125,28,21,211,16,223,14] [0x3007122141161020,0x55843003]⟩,
  ⟨40,5,[ew50,ew120,ew109,ew115],lh 6 [7,237,55,33,31,32,245,56,132,234,57,239,263,233,235,236,238,240,241,242,243,244,246,247,248,249,250,251,252,253,254,255,256,257,258,259,260,261,262,264,265,266,267,268,269,270,271] [0x44b40110f389343,0x5011414c910b481,0x1985c3143583195,0x6c9000681081641,0x1ca78301d709082,0x8881c78481607ca,0x32694800890a163,0xa88329a040049c4,0x86b06000ac5082,0xb87007b46]⟩,
  ⟨40,4,[ew357,ew50,ew109,ew115],lh 4 [7,31,32,132,234,263,33,245,237,272,273,274,275,276,277] [0x13233b3121a98161,0x223e31001d13001c,0x4046554746226764,0x755700255600454,0x20]⟩,
  ⟨40,4,[ew357,ew120,ew50,ew109,ew115],lh 4 [7,234,32,263,31,56,237,278,279,280,281,236,272,33] [0x5c1ba09082726144,0x3011312d13030252,0x30]⟩,
  ⟨40,4,[ew120,ew50,ew358,ew109,ew115],lh 4 [7,245,31,263,132,234,32,56,55,236,237,273] [0x65530202442b2a29,0x3080817170303161,0x11]⟩,
  ⟨40,4,[ew359,ew50,ew109,ew115],lh 4 [245,239,7,263,31,32,132,236,272,282,283,284,285,286] [0x656600454987411,0x5162243442263340,0xc22131101b55a001,0x2030020533121d33,0x52]⟩,
  ⟨40,4,[ew359,ew120,ew50,ew109,ew115],lh 4 [245,237,263,7,32,31,234,272,239] [0x817323204046155,0x2123114012323404,0x300]⟩,
  ⟨40,4,[ew360,ew120,ew50,ew109,ew115],lh 4 [245,7,263,31,234,32,237,282,239,132] [0x834212150506673,0x2144205042131309,0x100]⟩
]
def nodesBlock9 : Array Node := #[
  ⟨40,4,[ew120,ew267,ew50,ew109,ew115],lh 4 [237,7,31,263,132,234,245,239,33,244,32] [0x3121244207052442,0x305500a913136680,0x131]⟩,
  ⟨40,4,[ew120,ew50,ew109,ew361,ew115],lh 4 [33,245,7,263,31,236,283,132,287,288,244,237,32] [0x3242944841716050,0x32113c10320b010a,0x232]⟩,
  ⟨40,4,[ew362,ew120,ew50,ew109,ew115],lh 4 [7,33,31,132,263,245,237,289,290,236,284,32,248] [0xa191807055612323,0x41401c1b40202332,0x40]⟩,
  ⟨40,4,[ew363,ew120,ew50,ew109,ew115],lh 5 [234,245,55,57,31,33,237,296,262,291,292,56,7,293,294,295,248,192,297] [0x709ac584a551124,0x1890839de330060,0x4821118008c020]⟩,
  ⟨40,4,[ew120,ew364,ew50,ew109,ew115],lh 4 [31,56,33,245,57,237,55,295,262,234,7,192] [0x4008037052024004,0x126b5121a6313192,0x133]⟩,
  ⟨40,4,[ew120,ew50,ew109,ew115,ew365],lh 4 [56,7,31,245,234,57,285,256,298,299,192,33,297,55] [0x9558512120706224,0x3301c10b414a3030,0xd10]⟩,
  ⟨40,4,[ew366,ew120,ew50,ew109,ew115],lh 4 [245,57,234,55,56,31,33,300,301,7,286,295,253] [0xa212938474621515,0x3c230402135310b0,0x400]⟩,
  ⟨40,4,[ew367,ew120,ew50,ew109,ew115],lh 5 [57,56,234,55,33,237,7,297,302,303,245,304,305,239,256,306,307,253] [0x18d815a84248100,0x41e0005c068004,0x1ce60c4c528481]⟩,
  ⟨40,4,[ew368,ew120,ew50,ew109,ew115],lh 4 [33,56,7,57,237,132,308,309,32,310,311,256,262,253,297] [0x4040a29281706453,0x10d20410132c331b,0x1e2]⟩,
  ⟨40,4,[ew120,ew50,ew109,ew369,ew115],lh 4 [263,33,32,234,132,237,57,7,56,55,256] [0x21207046624a5141,0x9207088133031135,0x90]⟩,
  ⟨40,4,[ew370,ew120,ew50,ew109,ew115],lh 4 [237,55,234,263,56,57,7,32,132,259,33] [0x202313174020255,0x1012004a03131984,0x616]⟩,
  ⟨40,4,[ew371,ew120,ew50,ew109,ew115],lh 4 [33,7,237,55,57,56,263,132,32,259] [0x2020131355020274,0x3031020026161984,0x131]⟩,
  ⟨40,4,[ew372,ew120,ew50,ew109,ew115],lh 4 [56,33,132,7,237,55,31,312,313,314,315,263,259,262] [0x4121b3a090817162,0x1531401023dc020,0x53]⟩,
  ⟨40,4,[ew120,ew50,ew109,ew115,ew373],lh 4 [33,32,31,237,56,245,234,7,262,263,132] [0x101a292814143220,0x5541551033006603,0x774]⟩,
  ⟨40,4,[ew374,ew120,ew50,ew109,ew115],lh 4 [245,32,33,31,237,7,55,132,263,266] [0x4332851010424273,0x6265201019351010,0x160]⟩,
  ⟨40,4,[ew375,ew120,ew50,ew109,ew115],lh 4 [234,32,245,263,33,31,55,132,239,266] [0x8070662121040455,0x3400301209371212,0x132]⟩
]
def nodesBlock10 : Array Node := #[
  ⟨40,4,[ew120,ew50,ew376,ew109,ew115],lh 5 [237,32,55,234,31,239,56,245,316,317,263,266,318,319,33,7,320] [0x98262250429483,0x5c00358058942,0x450788e700c60]⟩,
  ⟨40,4,[ew120,ew50,ew109,ew115,ew377],lh 4 [237,57,33,245,31,7,234,132,239,320,56,55] [0x1441144117730806,0x3539022026520230,0xb5a]⟩,
  ⟨40,4,[ew378,ew120,ew50,ew109,ew115],lh 4 [33,31,245,237,132,56,7,57,234,55,321] [0x3010665503034141,0x880202371171242,0xa29]⟩,
  ⟨40,4,[ew379,ew120,ew50,ew109,ew115],lh 4 [33,31,56,57,234,7,237,245,55,132,321] [0x6010857240401313,0x450620231131292,0xa52]⟩,
  ⟨40,3,[ew357,ew50,ew109,ew115],lh 4 [7,256,234,262,33,57,237,295,306] [0x2321415080517164,0x30302]⟩,
  ⟨40,3,[ew359,ew50,ew109,ew115],lh 3 [262,7,245,256,234,295,306,296] [0x24082134f622dee4,0x1]⟩,
  ⟨40,3,[ew359,ew357,ew109,ew115],lh 4 [7,32,263,31,237,33,245,322,323] [0x8041710202615133,0x20240]⟩,
  ⟨40,3,[ew357,ew50,ew380,ew115],lh 4 [7,263,132,31,32,322,324,33,245] [0x101847420603352,0x101]⟩,
  ⟨40,3,[ew381,ew357,ew50,ew115],lh 4 [7,263,31,32,132,33,245,237,57] [0x8020720101365342,0x101]⟩,
  ⟨40,3,[ew357,ew50,ew109,ew382],lh 4 [7,263,31,32,323,324,132,33,245] [0x101837360235242,0x101]⟩,
  ⟨40,3,[ew383,ew357,ew50,ew109],lh 4 [7,263,132,32,31,237,57,33,245] [0x6223521001100140,0x8373]⟩,
  ⟨40,3,[ew120,ew50,ew380,ew115],lh 4 [234,7,263,132,31,322,56,33,32] [0x870212144365030,0x12121002]⟩,
  ⟨40,3,[ew381,ew120,ew50,ew115],lh 4 [234,7,31,263,132,56,33,32,237] [0x8020131370605242,0x10033121]⟩,
  ⟨40,3,[ew120,ew50,ew109,ew382],lh 3 [234,7,31,263,32,323,56,33] [0x32031386515a2a10,0x59]⟩,
  ⟨40,3,[ew383,ew120,ew50,ew109],lh 4 [234,7,263,132,32,31,237,56,33] [0x6030211201021251,0x4804337]⟩,
  ⟨40,3,[ew359,ew109,ew361,ew115],lh 3 [245,239,236,7,31,263,234,32] [0x359605e546b1084]⟩
]
def nodesBlock11 : Array Node := #[
  ⟨40,3,[ew362,ew359,ew109,ew115],lh 3 [239,236,31,7,263,245,325] [0x470a651283c28050,0x3]⟩,
  ⟨40,3,[ew359,ew109,ew115,ew365],lh 3 [245,239,234,132,7,32,236,263] [0xe690601718930c2]⟩,
  ⟨40,3,[ew366,ew359,ew109,ew115],lh 4 [239,245,132,234,263,236,326,7,32] [0x3412137001600520,0x811423]⟩,
  ⟨40,3,[ew384,ew50,ew109,ew115],lh 4 [33,245,7,132,31,234,236,237,244,263] [0x1008324241317060,0x21190550]⟩,
  ⟨40,3,[ew385,ew50,ew109,ew115],lh 3 [33,245,7,237,263,31,132,244] [0x411060755438d0c3,0x89]⟩,
  ⟨40,3,[ew120,ew50,ew109,ew386],lh 4 [33,245,7,31,263,234,236,325,132,237] [0x1005423231817060,0x21140950]⟩,
  ⟨40,3,[ew120,ew50,ew109,ew387],lh 4 [33,237,31,7,263,132,245,244,234] [0x1007234325521010,0x66340480]⟩,
  ⟨40,3,[ew388,ew50,ew109,ew115],lh 4 [245,237,7,33,31,263,248,234,239,132] [0x6601524240901833,0x20051771]⟩,
  ⟨40,3,[ew389,ew50,ew109,ew115],lh 4 [33,245,7,237,31,263,248,234,132,244] [0x6609524241813030,0x21150770]⟩,
  ⟨40,3,[ew120,ew50,ew109,ew390],lh 4 [237,245,234,31,7,248,33,55,239,295,57,56] [0x5510a43431910802,0xb7170266]⟩,
  ⟨40,3,[ew120,ew50,ew391,ew109],lh 4 [55,57,56,33,237,262,295,192,248,245] [0x3070126110504113,0x2908232]⟩,
  ⟨40,3,[ew392,ew50,ew109,ew115],lh 4 [57,256,7,33,237,295,31,245,234,297] [0x7131026001504003,0x19212823]⟩,
  ⟨40,3,[ew393,ew50,ew109,ew115],lh 4 [57,7,256,237,245,295,33,31,234,297] [0x3242071055406003,0x29121813]⟩,
  ⟨40,3,[ew120,ew50,ew394,ew115],lh 4 [55,234,295,7,31,326,256,33,56] [0x1871204042265121,0x30303010]⟩,
  ⟨40,3,[ew120,ew50,ew395,ew115],lh 4 [234,55,295,237,56,245,256,31,33,7] [0x480217124623020,0x95513101]⟩,
  ⟨40,3,[ew396,ew50,ew109,ew115],lh 4 [262,245,57,234,56,7,239,295,55,253] [0x1414080221716233,0x50109050]⟩
]
def nodesBlock12 : Array Node := #[
  ⟨40,3,[ew397,ew50,ew109,ew115],lh 4 [245,234,57,55,239,262,253,295,56,7] [0x801235520704421,0x90036613]⟩,
  ⟨40,3,[ew120,ew50,ew398,ew115],lh 4 [33,245,57,307,56,239,295,306,234,327,253] [0x1008337221615020,0x41140a90]⟩,
  ⟨40,3,[ew120,ew399,ew50,ew115],lh 4 [56,57,33,245,256,239,306,307,192,253] [0x320176151121040,0x29820330]⟩,
  ⟨40,3,[ew120,ew400,ew109,ew115],lh 4 [33,132,237,7,57,297,262,253,55] [0x2002136141142010,0x55380730]⟩,
  ⟨40,3,[ew401,ew120,ew109,ew115],lh 4 [33,237,7,57,262,297,132,253,256,56,55] [0x3983072010010160,0x552a3244]⟩,
  ⟨40,3,[ew120,ew50,ew109,ew402],lh 4 [33,56,237,57,262,132,7,256,253,32] [0x2101554431732020,0x19610860]⟩,
  ⟨40,3,[ew403,ew120,ew50,ew109],lh 4 [56,33,7,262,132,237,32,253,297] [0x5141802071212433,0x50106060]⟩,
  ⟨40,3,[ew120,ew404,ew109,ew115],lh 3 [31,33,132,237,7,55] [0x536164b402090601,0x12c]⟩,
  ⟨40,3,[ew405,ew120,ew109,ew115],lh 4 [33,7,132,237,55,31,57,259,263] [0x7226041030030355,0x14142182]⟩,
  ⟨40,3,[ew120,ew50,ew406,ew115],lh 3 [33,132,7,237,55,31,57,262] [0x41106032b9b4e608,0xa2]⟩,
  ⟨40,3,[ew407,ew120,ew50,ew115],lh 3 [56,31,33,132,237,7,55,262] [0x267f84a1a8110058,0xb5]⟩,
  ⟨40,3,[ew50,ew109,ew408,ew115],lh 4 [234,55,32,33,239,245,31,56,328,263,266] [0x5527300144600230,0xa1912181]⟩,
  ⟨40,3,[ew409,ew50,ew109,ew115],lh 3 [237,245,32,55,234,239,263,266] [0x3120088ef3451144,0x99]⟩,
  ⟨40,3,[ew120,ew109,ew410,ew115],lh 3 [237,245,32,55,234,239,263,266] [0x4cb408ef3144451,0x24]⟩,
  ⟨40,3,[ew411,ew120,ew109,ew115],lh 4 [237,32,55,234,56,239,245,263,266,329] [0x1414033001605003,0x12928272]⟩,
  ⟨40,3,[ew120,ew50,ew376,ew377],lh 4 [237,7,234,55,239,328,31,263,266,329,321] [0x1910837361510402,0xa10220]⟩
]
def nodesBlock13 : Array Node := #[
  ⟨40,2,[ew359,ew380,ew115],lh 3 [263,7,31,132,245] [0x2082088d2]⟩,
  ⟨40,2,[ew359,ew109,ew382],lh 3 [7,31,263,33,32] [0x82042319]⟩,
  ⟨40,2,[ew50,ew380,ew382],lh 2 [7,31,263,32] [0x122277]⟩,
  ⟨40,2,[ew359,ew109,ew386],lh 3 [239,245,234,236,7] [0x8086102ca]⟩,
  ⟨40,2,[ew359,ew394,ew115],lh 2 [239,245,236,234] [0x14be44]⟩,
  ⟨40,2,[ew50,ew408,ew377],lh 3 [234,55,239,245,237,263,266] [0xc69801498]⟩,
  ⟨40,2,[ew411,ew120,ew377],lh 3 [237,234,55,239,263,266] [0xaa2048601]⟩,
  ⟨41,3,[ew121,ew122,ew123,ew124],lh 4 [35,10,9,207,330,16,331,332,333,334,71,335] [0x9181027060010540,0x12b2332a]⟩,
  ⟨49,7,[ew149,ew150,ew151,ew152,ew153],lh 6 [345,67,0,11,19,344,53,37,343,14,336,346,362,20,350,57,355,347,351,337,338,339,340,341,342,348,349,352,353,354,204,356,357,358,359,360,361,363,364] [0x3cf5073474ca0c3,0x814860a357595,0x18800a14a00a18a,0x6512512c8048008,0x872c7247691041,0x7080826d2112387,0x14500d18638711d,0xd14d003183003,0x2507d005e2c3243,0x3901042c3061810,0xa48cf10488f082,0xc00c006041383,0x8200600600c041,0x508500502500c,0x822c910400c00c,0x3890892c1101981]⟩,
  ⟨49,6,[ew412,ew150,ew151,ew149,ew152,ew153],lh 6 [19,53,336,11,14,67,0,25,369,355,362,347,345,343,382,346,350,57,344,365,370,20,366,367,368,37,371,372,373,374,375,376,377,378,379,380,381,383,384,385,386,363,387] [0x5cc1c759354c0c3,0x34d308308041218,0x75c6cf10469464c,0x8100003df3de104,0x414244230008a1,0x3873830430c70ce,0xc35034c20a79a5,0x14524424914e0c4,0x440451186240243,0x410821cb1c9189,0x22804504708204b,0x28028120128528a,0x8a20a480492229,0x1042c52cb10b085,0x34634d02a086082,0x145186100002000,0x4186140]⟩,
  ⟨49,6,[ew150,ew151,ew149,ew413,ew152,ew153],lh 6 [14,20,0,53,388,19,67,37,362,339,344,25,345,398,346,350,389,390,11,383,384,385,371,391,392,393,394,395,396,386,397,363,336,366,399,400,401,402,403,404,405,406,407,408] [0x440c310a2810c1,0x1c705005551304a,0x4005159204c491,0x41181600017186,0x82685159082045,0xc70c31032c72c1,0xc310310c30b10b,0x11d2c001c11b0cc,0x20520b11e200208,0x1c810828528a11f,0x1c61d08601cc,0x242247000246249,0x38914934234d145,0x9a59231863a2,0xaeaa680823e73ce,0x14608600500f082,0x80185]⟩,
  ⟨49,6,[ew79,ew150,ew151,ew149,ew152,ew153],lh 6 [14,53,0,19,67,410,25,11,344,339,37,362,355,57,345,398,390,343,370,346,350,382,20,409,411,412,413,414,415,341,416,417,194,386,363,418] [0x4e2085d058e34d,0x251381045208141,0x64001310461244e,0xd40824c001a104,0x415030dc0826c3,0x5461870471c6195,0x1f79d40a287487,0x10730030c1041c0,0x34334d0a0303307,0x4114118a18c082,0x16104004614604a,0x2c22c11412c02cb,0x28b14b202208162,0x244249000284,0x3c23cf0e324224a,0xc40840030c90c3,0x80103]⟩,
  ⟨49,6,[ew414,ew150,ew151,ew149,ew152,ew153],lh 6 [53,0,67,19,20,336,14,344,419,362,347,345,25,343,365,389,346,350,11,411,398,409,420,421,422,423,341,416,417,424,425,426,427,386,363,387] [0x1cb0004ce48b104,0x1452c71c8000207,0x58209018654f50b,0x510c3402097186,0x4410590c3601,0x1071c80002071c4,0x19c6da10f10e145,0x8478619d082106,0x8030df041103104,0x14530a304044,0x22100200c14c00a,0x241240200242249,0x892091c11c7222,0x18528228a18a142,0x34134d0e3141145,0xc20411830c50c3,0x6041083]⟩,
  ⟨49,6,[ew150,ew151,ew149,ew152,ew415,ew153],lh 6 [11,19,362,20,14,0,25,346,431,347,53,344,432,355,345,339,57,351,350,434,428,429,400,421,430,363,433,37,67,435,436,437,438,439,440] [0xc028000b2c328a,0x2430cf0c02400cb,0x35434010000f3c3,0xc054000700d10d,0x400180035c30d6,0x5010050405140,0x20a249288286249,0x10208c086106188,0x8c08638618c182,0x64204218c182382,0x1da08c08b04b2cc,0x20e207104213207,0x4510412051471db,0x1dc10e109041445,0x1c105d145101113,0x81f04149e484145,0x120418a1]⟩,
  ⟨49,6,[ew27,ew150,ew151,ew149,ew152,ew153],lh 6 [11,19,25,0,20,67,53,346,431,362,443,347,345,339,355,57,344,351,336,14,434,350,375,441,413,442,444,445,204,446,386,363,447,448] [0x1180005c4116000,0x8228618c082644,0x1c748c35230618a,0x550c31d44cc153,0x18454105b0c3681,0x102100180002084,0x3442c410d1002c0,0x74e3857001c000d,0x3c30c004000514e,0x1822c200300f04f,0x1420882062cb188,0x8a08914924a782,0x25005040a7c90c9,0x1e021420714524a,0x443451041203207,0x450c31c1048041,0x210c3141]⟩,
  ⟨49,6,[ew150,ew151,ew149,ew152,ew153,ew416],lh 6 [14,20,11,19,344,362,351,67,355,350,452,25,453,53,343,345,398,57,346,454,204,449,450,405,423,451,386,418,37,455,456,437,457,458,459,0] [0x42342084101341,0x181050042182044,0x207502002090401,0x4480c80871c8008,0x5882092110c3455,0x99081601057042,0x28d38e34a34b38e,0x514c68b00b2ca,0x10c1050c52cc2c5,0x1053c514c1440c4,0x1ca14c1443c410c,0x2802861c618000a,0x1890c319318925b,0x7470030c925c18f,0x7924802401c31c7,0xe28600120007c0,0x132630cf]⟩
]
def nodesBlock14 : Array Node := #[
  ⟨49,6,[ew31,ew150,ew151,ew149,ew152,ew153],lh 6 [53,14,11,67,0,20,362,25,350,343,355,462,398,57,351,345,452,344,346,19,454,465,380,460,415,461,336,463,445,464,386,363,354] [0x1580825c515634d,0x1c72c000f1c7645,0x20868f30c3c000b,0x5c0c36c10520c3,0x2144cf113481,0x146142002086185,0x30524514c142242,0x4a2830c204208c,0x34410a20a08308a,0x730728428d74d,0x401d0400240010,0xb00604618b780,0x19111144b7c6106,0xce3810490c918b,0x39438810424124e,0xc3104055048220,0x11040d5]⟩,
  ⟨49,6,[ew150,ew151,ew149,ew152,ew417,ew153],lh 6 [53,19,336,0,382,362,37,67,355,346,467,344,345,351,25,347,343,466,11,350,391,424,204,386,363,433,428,468,400,413,469,387,14,470,471,472] [0x10800020b204000,0x34d50618434410b,0x111109256106115,0x20925220c4891c7,0xc81011040c3201,0x6000082386188,0x14529700700e08e,0x28500c000280147,0x14114028014c145,0x852852c12cb298,0x2423c73cf699087,0x19d18670609b082,0x41005f083082782,0x2601cc1c2041403,0x1c10470c3241051,0x620c34c10610c3,0x130c38c1]⟩,
  ⟨49,6,[ew28,ew150,ew151,ew149,ew152,ew153],lh 6 [53,37,19,382,362,14,0,355,336,346,344,347,473,345,350,343,67,466,57,375,474,421,475,476,477,478,479,480,392,425,358,363,446,447,481] [0x28d00024948d1c7,0x20834a28c00030a,0x581055208501053,0x5ce18625140d150,0x39b39a082658,0xc40c70071c41c3,0xdd208701043203,0x25e0d10c91450c1,0xc20c31831c21c9,0x40200101107186,0x304005004204001,0x102080300105104,0x4430428228a31f,0x1612e02cb145049,0x3c63cf0822c62c1,0xa218614214b08b,0x5185242]⟩,
  ⟨49,6,[ew150,ew151,ew149,ew152,ew153,ew418],lh 6 [67,53,382,14,37,0,336,57,347,350,362,344,483,25,345,343,482,486,346,19,393,426,194,11,386,363,447,418,449,484,405,415,485,471,487] [0x3470471cd1c2041,0x18650410218208d,0x800870c7084095,0x892561c01c20c3,0x25708e089145090,0x44041181344109,0x28a31804000d186,0x319285281301280,0x4e04a30a2c52cb,0x13012ce2cb30b,0xda2002080c3100,0x3c53cf71b205204,0x10478419d208248,0x1400d10c680611f,0xd20c3145011000,0x4c3883012000840,0x1025314e]⟩,
  ⟨49,6,[ew32,ew150,ew151,ew149,ew152,ew153],lh 6 [14,53,336,19,382,362,344,57,37,67,350,347,488,345,346,343,0,482,11,380,489,423,490,491,492,493,479,494,394,427,361,386,464,495] [0x14d04128a48d1c7,0x8234514c041305,0x588215082508213,0x39a0006585ce249,0x4129140d0d039b,0x1061070471c6184,0x11d082708204084,0x109107007108,0x11110a0c31c91c4,0x4108218818a29e,0x31f040046086048,0x143141301140145,0x853051830c6306,0x2c92cb000089,0x3e03cf0c32ca2c2,0xc984900300b0cb,0x280243]⟩,
  ⟨49,6,[ew150,ew151,ew149,ew152,ew153,ew419],lh 5 [53,20,67,347,344,0,346,11,343,355,336,362,57,37,498,350,345,25,19,481,495,496,471,479,497,435,455,499,437,445,500,14] [0x9027000e420401,0x3b5a14042d09d07,0x88499a522484c1,0x4952ca31852a5e9,0x3e0ecbb19661ea1,0x8a9404000a54508,0x380b12d6e58040,0x5b9642908e22cab,0x38048108e20200,0x5194310c791a842,0x1bc682951a40ca3,0x6f9a3e8c7c1b76a,0x1404f29446118c6,0x6348b093cdf]⟩,
  ⟨49,5,[ew414,ew412,ew151,ew149,ew152,ew153],lh 5 [20,25,0,14,336,53,11,361,504,447,345,383,204,194,501,341,502,503,386,363,387,19] [0x30d835902509540,0x801e0005c539da6,0x905082040288003,0xa09291902298823,0x5510c82]⟩,
  ⟨49,5,[ew414,ew150,ew151,ew149,ew152,ew153],lh 4 [0,25,67,336,20,53,14,19,37,11,341,386,363,387] [0x707262688151594,0x107044624a431515,0x326310c012b1353,0x20630d]⟩,
  ⟨49,5,[ew150,ew420,ew149,ew152,ew153],lh 5 [0,53,67,25,11,336,14,19,347,355,382,57,362,344,343,507,363,383,505,506,501,508,204,386,509,510,511,512] [0x50d44090831a821,0x255f42be72890a4,0x2084932522b10c4,0x4812b3ad60024e9,0x194a14042528d03,0x1e42c33198b8441,0xec6d035ba80c10,0x298c81090641445,0x41cee039c73a008,0x3000238840018e6]⟩,
  ⟨49,5,[ew412,ew150,ew420,ew149,ew152,ew153],lh 5 [11,343,0,14,53,344,67,19,501,345,508,513,514,515,516,383,386,397] [0x6898358d4149100,0x198000bca0011c2,0x1c0650902038800,0x844130c2411451,0x230867]⟩,
  ⟨49,5,[ew79,ew412,ew150,ew151,ew152,ew153],lh 5 [37,343,53,25,0,11,14,67,361,397,517,345,383,336,341,508,433,418,386,363,19] [0x9cc108c4161560,0x8000378dc068424,0x394621880488006,0x9892990908214a6,0x942194a]⟩,
  ⟨49,5,[ew79,ew150,ew151,ew149,ew152,ew153],lh 4 [53,67,11,25,37,14,19,0,518,20,336,341,386,363,433] [0x67675151a4030392,0x426721512b423030,0x441e106d001c0300,0x5115886]⟩,
  ⟨49,5,[ew150,ew151,ew149,ew421,ew153],lh 5 [433,11,67,19,53,382,336,14,0,362,25,520,344,343,519,502,386,363] [0x2a8a12042a51484,0x802f319c0004c1,0x8845394a2284e1,0xa10518ca840463,0x518c4010863280a,0x22c891252b81044,0x4ad2c1b18b8a469,0x31ce01000701842,0xc0d435a318100,0x3a0e21884811c67]⟩,
  ⟨49,5,[ew412,ew150,ew151,ew149,ew421,ew153],lh 5 [53,11,19,25,336,0,344,14,358,386,397,447,354,502,513,520,343,433,346,521,522,383,204,363,523,387] [0x98a478c1e6719a1,0x458212546018282,0x525230006111428,0x6648b5e08015c0a,0x5114ec]⟩,
  ⟨49,5,[ew150,ew151,ew149,ew152,ew421,ew153],lh 4 [19,11,336,355,25,362,0,53,347,354,14,524,383,363,433] [0x1331133112c2b717,0x4554455447743063,0x9908288228e250d5,0x60606060aa]⟩,
  ⟨49,5,[ew422,ew150,ew151,ew149,ew152,ew153],lh 5 [25,19,336,11,53,14,0,447,355,20,362,525,345,37,526,527,350,383,204,386,363] [0x785c5689845a928,0x90c6288c0401201,0x980041006130c65,0x88e728801a0005,0xc130446]⟩
]
def nodesBlock15 : Array Node := #[
  ⟨49,5,[ew423,ew412,ew150,ew151,ew149,ew153],lh 5 [11,336,19,25,14,0,204,386,447,53,363,526,20,514,528,37,529,530,383] [0x2048339c8031964,0x70da3600a228908,0xc86002622809e1,0x129414846011400,0x128823]⟩,
  ⟨49,5,[ew150,ew151,ew149,ew152,ew424],lh 5 [382,336,19,53,11,67,418,14,0,362,347,25,532,344,383,531,503,204,386,363] [0x2c041908b20063,0x18d0085e670020,0x214a039c05010f1,0x220801080841044,0x5842330c610acc6,0x1b0692a52c90ca3,0x4b12d135ac9a449,0x9c2a2a947384a1,0x50946418c21290a,0x3a0e5114a841c42]⟩,
  ⟨49,5,[ew412,ew150,ew151,ew149,ew152,ew424],lh 5 [11,67,19,336,344,347,14,418,0,362,503,515,532,521,529,350,53,383] [0x705a139d8459140,0x304002c480041e2,0xa42328ca012000,0x408630986911044,0x610443]⟩,
  ⟨49,5,[ew150,ew151,ew149,ew152,ew153,ew424],lh 4 [53,336,11,67,14,344,57,343,19,383,347,386,418] [0x2662243221915020,0x55003b0100a2662,0x177117c113410550,0x8843344334]⟩,
  ⟨49,5,[ew425,ew150,ew151,ew149,ew152,ew153],lh 5 [53,14,19,336,11,25,0,344,447,57,20,533,345,343,37,67,534,346,535,383,204,386,363] [0x8860f7358759d49,0xa108398ca028242,0xa80a00148231081,0x10d0808c02b0001,0x2230466]⟩,
  ⟨49,5,[ew426,ew412,ew150,ew151,ew149,ew152],lh 5 [11,53,14,19,336,0,25,363,386,447,535,20,516,536,37,522,530,383,204] [0x1906139c6028143,0x6858158062288a4,0x244c000602789c4,0x12106084c014800,0x948881]⟩,
  ⟨49,5,[ew412,ew150,ew151,ew413,ew152,ew153],lh 5 [37,14,25,0,541,347,336,538,539,11,383,517,354,20,505,53,537,433,418,540,504,386,363,387,19] [0x6218000f701a0,0x98529420e700e40,0xa8a821154422881,0xb98c52996bb0841,0x781858c]⟩,
  ⟨49,5,[ew412,ew151,ew149,ew413,ew152,ew153],lh 5 [25,20,14,382,11,19,541,538,540,383,0,506,37,542,519,531,539,524,386,363,336] [0x89c26858108160,0x88c0339e00095e1,0x11a830166000a40,0x190831112632508,0x14550883]⟩,
  ⟨49,5,[ew414,ew150,ew151,ew413,ew152,ew153],lh 5 [53,37,67,20,14,343,19,383,344,0,447,336,345,341,504,386,363] [0x904160420400e7,0x10da31810009921,0x781c00146648c64,0x2ad4a1140680002,0x8211165]⟩,
  ⟨49,5,[ew79,ew151,ew149,ew413,ew152,ew153],lh 4 [53,382,19,0,20,14,67,11,25,383,345,524,386,363,341] [0x23245654a4990804,0x3d006c0b1018008,0x17711723235656e1,0x323271]⟩,
  ⟨49,5,[ew151,ew149,ew413,ew152,ew417,ew153],lh 5 [53,19,67,355,25,382,20,0,37,540,541,518,204,544,543,386,363,336,433,418,346,11,14,545] [0x9e07140520004,0x9222501e0001886,0x6316b9a0c852929,0xb09ad08ea31d043,0x384e1b8441]⟩,
  ⟨49,5,[ew28,ew151,ew149,ew413,ew152,ew153],lh 5 [355,20,362,37,53,383,0,382,25,517,518,11,67,546,363,336,418,346,358,14,19] [0x605611942541101,0x80710c82099a1,0x28de04a5c220844,0x382400454a80c65,0xd434c07]⟩,
  ⟨49,5,[ew151,ew149,ew413,ew152,ew153,ew418],lh 5 [53,0,382,67,14,57,25,37,383,194,545,547,386,363,336,418,20,350,11,19] [0xd805880230006,0x20dc2018c0005a0,0x11607420e178483,0x92452c4254a4a2,0x984831914a]⟩,
  ⟨49,5,[ew32,ew151,ew149,ew413,ew152,ew153],lh 5 [20,344,57,53,37,19,67,14,25,397,549,550,383,11,548,0,382,386,336,433,541,350] [0x701a02000c40d00,0x104500906178006,0x99242184234a621,0x2d56b388b42914a,0xe631ca2]⟩,
  ⟨49,5,[ew427,ew150,ew149,ew152,ew153],lh 5 [14,0,37,25,53,19,524,504,67,543,20,362,344,547,339,398,551,397,552,553,554,363,555] [0x228833186a190c4,0x1884439c8220ce3,0x1800b92d6089204,0x186aca318108e63,0x308ca39d42118e7,0x3210902528b1800,0x4852d2b5a10a4a9,0x1000e439c001d08,0x1144f0bde528822,0x42829501080a5]⟩,
  ⟨49,5,[ew427,ew150,ew149,ew413,ew152,ew153],lh 5 [53,398,20,0,14,344,67,386,19,37,345,383,547,504,339,556,557,558,559] [0x3014008005014a0,0x1304112c05180e7,0x7102d0890310886,0x90e26819e908524,0x440c83]⟩
]
def nodesBlock16 : Array Node := #[
  ⟨49,5,[ew150,ew151,ew149,ew428,ew413,ew153],lh 5 [53,14,19,20,398,0,344,67,11,383,386,560,556,363,339,336,561,562,563] [0x41c2719069300c3,0xa8260008311468,0x704801344c00160,0x11450088822bc81,0x591621]⟩,
  ⟨49,5,[ew150,ew151,ew149,ew152,ew429,ew153],lh 5 [53,355,0,37,67,25,19,20,433,11,386,345,564,363,336,561,350,565] [0x2042709c61280a0,0x500a000c2610521,0x420026818002c04,0x119e4188c370c64,0x5114044]⟩,
  ⟨49,5,[ew430,ew150,ew151,ew149,ew153],lh 5 [14,20,362,19,447,355,67,53,0,567,566,37,550,344,398,433,363] [0x426294c1300a5,0x1c0a1094738040,0x32de02100b01886,0xc66420c330100,0x8845394a2104e1,0x2aca12102b09484,0xa02c1b18840463,0x12527210e938884,0x1284d1b5aa80863,0x48d2e439c31a509]⟩,
  ⟨49,5,[ew430,ew150,ew151,ew149,ew413,ew153],lh 5 [67,20,53,398,344,19,0,14,362,346,383,550,566,557,567,568,569] [0x1c600208008027,0xa882204a001920,0x61042184a60ac23,0x18cce188c413442,0x5815e5]⟩,
  ⟨49,5,[ew430,ew150,ew151,ew149,ew152,ew153],lh 4 [0,362,347,355,19,20,53,37,398,14,358,363] [0x4099828261615353,0x3a3353252131540,0x2710b06116126204,0x404704772]⟩,
  ⟨49,5,[ew150,ew151,ew149,ew431,ew413,ew152],lh 5 [67,53,20,37,0,362,19,14,383,355,363,570,558,347,571,562,568] [0x108c410c48284a2,0x228250846038049,0x218610140c08561,0x200ce20c0703463,0x801e0]⟩,
  ⟨49,5,[ew150,ew151,ew149,ew152,ew153,ew432],lh 5 [67,20,53,37,0,362,19,14,383,355,363,345,572,347,346,573,571] [0x1c0118428088a1,0x280a210d2109881,0x3818212c4450840,0x2000668c6430c60,0x2047800e]⟩,
  ⟨49,5,[ew433,ew150,ew151,ew149,ew152],lh 4 [361,344,14,0,20,354,19,53,67,575,37,574,544,362,339,386] [0x7313644300344606,0x566aa353377b11b7,0x6223883236863aa6,0x4055411070011474,0x2cc880220a04554a,0x199755797155080c,0x29891b1d2ddbf122,0x929e8ee2]⟩,
  ⟨49,5,[ew433,ew150,ew151,ew149,ew413,ew152],lh 5 [0,67,20,53,339,19,362,14,344,350,383,544,574,559,575,563,569] [0x1480020c028045,0x12843308e001520,0x61863204e112c44,0x902e20c260b463,0x1805e7]⟩,
  ⟨49,5,[ew433,ew150,ew151,ew149,ew152,ew153],lh 4 [14,343,344,57,53,67,20,339,0,383,362] [0x505717142426363,0x3630503191232488,0x1422420a0214163,0x550711705]⟩,
  ⟨49,5,[ew150,ew151,ew149,ew413,ew152,ew153],lh 5 [19,14,344,53,67,0,20,57,343,383,339,345,576,362,346,561,350,571] [0x90273a8c910c43,0x1096218c4601404,0x22103008020b42c,0x805e1700a028481,0x40400220]⟩,
  ⟨49,5,[ew412,ew150,ew151,ew149,ew152,ew153],lh 5 [19,14,344,343,57,53,67,0,20,577,345,339,526,346,535,350,383,362] [0x6858158d4248904,0x907011045781c0,0x886519c0401026,0x384c11940200831,0x40600060]⟩,
  ⟨49,5,[ew150,ew151,ew149,ew152,ew434,ew153],lh 4 [344,57,355,362,19,14,37,347,0,53,341,518,383,67,350,578] [0x12211225aac10109,0x330033509902412,0xbb47677667563403,0x8f8e8484d5]⟩,
  ⟨49,5,[ew435,ew150,ew151,ew149,ew152,ew153],lh 5 [19,11,67,53,25,362,347,0,37,358,518,20,336,14,386,363,433,545] [0x1da26186519561,0x10426404a108c07,0x710831982038129,0x21028088079082,0x2201014a]⟩,
  ⟨49,5,[ew150,ew151,ew149,ew152,ew153,ew436],lh 5 [25,37,11,53,57,344,67,343,341,358,397,549,14,204,386,433,387,346,579,19,0] [0x4a5a24202200c03,0xc611108211082,0x14a0014a0529c0,0x9ce109e015ade1,0x293918d1618cc]⟩,
  ⟨49,5,[ew437,ew150,ew151,ew149,ew152,ew153],lh 5 [25,37,57,0,53,67,14,343,549,545,20,336,19,11,386,363,433,418] [0x314c559c8020142,0x288270880201183,0x70001204621b446,0x885088040378005,0x12919823]⟩
]
def nodesBlock17 : Array Node := #[
  ⟨49,5,[ew414,ew79,ew150,ew151,ew152,ew153],lh 5 [341,37,25,19,14,53,336,447,354,0,537,11,549,518,20,580,581,386,363] [0x91810944158141,0x218a2289c008da1,0x7800510108198e7,0x908448900380004,0x12348c43]⟩,
  ⟨49,5,[ew414,ew79,ew151,ew149,ew152,ew153],lh 4 [25,19,14,53,11,67,341,20,0,582,542,37,204,336,386,363] [0x418442c4b40303a7,0x3618172527d63030,0x16252501f005e006,0x215199]⟩,
  ⟨49,5,[ew150,ew151,ew149,ew152,ew438,ew153],lh 5 [0,53,336,347,20,19,355,25,397,14,344,341,67,11,339,386,363,387] [0x219845888220541,0x1042e01406698c4,0x3820709ce1421e1,0x1822310c6210c62,0x50140501529]⟩,
  ⟨49,5,[ew439,ew150,ew151,ew149,ew152,ew153],lh 5 [53,0,14,362,355,19,20,336,25,447,11,347,37,67,583,350,341,363,387,354] [0x715a262d0040144,0x20a0731c60199e5,0x1806000c25090c4,0x9052911c0188402,0x2508a61]⟩,
  ⟨49,5,[ew150,ew151,ew149,ew152,ew153,ew440],lh 4 [336,20,67,25,14,53,343,57,362,0,504,19,341,386,363,523] [0x17911421c1108585,0x39e332d3aa031771,0x660066002f05335,0xbb42244224]⟩,
  ⟨49,5,[ew441,ew150,ew151,ew149,ew152,ew153],lh 5 [14,53,20,67,344,57,336,25,19,354,11,343,37,584,346,0,341,386] [0x701a062ce138545,0x18a0211841209e8,0x880c10904528860,0x4180300c2420420,0x318129]⟩,
  ⟨49,5,[ew414,ew151,ew149,ew152,ew417,ew153],lh 5 [344,0,19,20,53,336,347,355,204,504,397,37,67,57,386,580,14] [0x69d874216501004,0x529c04a4a008827,0x299e52080420c03,0x8a0330446198c5,0x6208c22]⟩,
  ⟨49,5,[ew28,ew414,ew151,ew149,ew152,ew153],lh 5 [53,0,362,20,19,355,336,25,347,14,37,447,346,341,67,585,358,363,523] [0x6a068380e019583,0x528401006478dc9,0x1000209025814a9,0x5ae460062100840,0x902430486]⟩,
  ⟨49,5,[ew414,ew151,ew149,ew152,ew153,ew418],lh 5 [14,336,67,25,53,0,20,343,362,194,57,504,517,545,37,355,386,363,581,19] [0x4a440101c141104,0x182035ac237a8aa,0x8022186663223,0x6b4a009ce109e41,0x26500846]⟩,
  ⟨49,5,[ew32,ew414,ew151,ew149,ew152,ew153],lh 5 [53,344,14,20,67,11,25,343,37,57,336,447,354,350,341,586,0,19,361,386,523,387] [0x71c67300c0295a3,0x4202008203189e2,0x80019253120882,0x5ae8a0042008a61,0x11082632aa]⟩,
  ⟨49,5,[ew150,ew151,ew149,ew417,ew415,ew153],lh 5 [53,0,19,25,355,67,339,580,204,523,14,344,11,363,37,526,470] [0x4218439cc459080,0x1806001822090a4,0x4a46168c6000c03,0x2a8af1044171546,0x1145008822]⟩,
  ⟨49,5,[ew442,ew150,ew151,ew149,ew152,ew153],lh 4 [0,14,53,339,336,362,19,11,25,355,526,67,204,363] [0x6b1a13434585897,0x771c13434525206,0x1420d22152422306,0x601306013]⟩,
  ⟨49,5,[ew443,ew150,ew151,ew149,ew152,ew153],lh 4 [19,347,53,0,362,67,14,339,20,363] [0x365651717242488,0x3056567171424203,0x1520902542412130,0x3030030161]⟩,
  ⟨49,5,[ew27,ew150,ew151,ew149,ew415,ew153],lh 4 [344,53,20,0,14,57,19,433,431,545,345,447,448] [0x4364a47710104524,0x2532522552280101,0x63b8130301100110,0x996c63]⟩,
  ⟨49,5,[ew150,ew151,ew149,ew415,ew153,ew419],lh 4 [53,11,25,67,347,344,20,0,57,351,433,14,350,37,19] [0x1871163114642026,0x550200220021881,0x3cb4aa4994d30550,0xe7b33c73]⟩,
  ⟨49,5,[ew150,ew151,ew149,ew152,ew444,ew415],lh 4 [344,355,362,19,53,57,20,14,0,347,37,587,433,588,589] [0x1381611656650404,0x23b2022004405115,0x387aa983979c0220,0xe3d77]⟩
]
def nodesBlock18 : Array Node := #[
  ⟨49,5,[ew150,ew151,ew149,ew152,ew153,ew445],lh 4 [14,362,355,347,19,20,0,11,344,25,37,53,433,590,589] [0x2462502023531215,0x1481801013b37227,0x60aa3643030c9119,0xe4d004]⟩,
  ⟨49,5,[ew446,ew150,ew151,ew149,ew152],lh 4 [344,19,53,20,14,0,545,11,355,354,339,431,591,362,347] [0x2100188577588177,0x911ee595122c00c2,0x1415665451615e51,0x3799303722700322,0x488663437aa3933a,0xbb2aa2b20aa3638,0xb9660c0d4ddcd044,0x944b6bb4]⟩,
  ⟨49,5,[ew446,ew150,ew151,ew149,ew152,ew415],lh 4 [362,355,431,14,19,344,0,20,339,11,350,433,354,545] [0x3634242605041614,0x19731312820107a4,0x2b50055003082091,0xd3c23]⟩,
  ⟨49,5,[ew446,ew150,ew151,ew149,ew152,ew153],lh 4 [67,343,25,11,431,14,362,355,19,361,517,20,339,194,363,433] [0x5050414162627373,0xd3050331c1232b88,0xf0aae22060214199,0x5005411410]⟩,
  ⟨49,5,[ew150,ew447,ew151,ew149,ew152,ew153],lh 5 [347,20,25,67,19,53,37,0,592,14,11,345,593,561,350,594,386,363] [0x184c10802510541,0x300ac2ace438508,0x2808f2386d4a4c0,0xc448884380840,0xe319007200c0]⟩,
  ⟨49,5,[ew448,ew150,ew151,ew149,ew152,ew153],lh 4 [0,53,14,19,339,25,336,347,67,20,11,37,386,363] [0x3828247b75151aa,0x392824947915103,0x2610d012c2541403,0x303603664]⟩,
  ⟨49,5,[ew150,ew151,ew149,ew152,ew153,ew449],lh 5 [67,25,11,339,19,57,344,53,343,20,358,347,14,386,447,595,448,0] [0x528021a46249c47,0x8ce3114a2114a4,0x98c1098c1081a1,0x5a10b2208370060,0x2248018c78004]⟩,
  ⟨49,5,[ew450,ew150,ew151,ew149,ew152,ew153],lh 5 [347,53,20,0,25,343,344,11,57,14,358,361,397,545,37,19,204,386,363,465] [0x4a5c00982612048,0x81ce210041305e3,0x890810816b19d4a,0x280a0014839118c,0x1ad1cc05]⟩,
  ⟨49,5,[ew28,ew27,ew150,ew151,ew149,ew153],lh 4 [67,25,53,14,19,0,447,355,339,561,204,549,448,592,37,363] [0x408b01210a70390,0x4543e3312137d3c0,0x1626545476871212,0x654625f2]⟩,
  ⟨49,5,[ew150,ew151,ew149,ew152,ew418,ew416],lh 4 [57,25,14,0,53,67,19,398,194,387,351,355,386,37,486,535] [0x88b002500a701004,0x43411415c1174130,0x2656d36799252513,0x366f322e]⟩,
  ⟨49,5,[ew451,ew150,ew151,ew149,ew152,ew153],lh 4 [67,398,53,336,344,14,19,57,25,535,0,194,11,386] [0x9605051313484877,0xb6050513134242a6,0x50244220d23221c6,0x5006311310]⟩,
  ⟨49,5,[ew452,ew150,ew151,ew149,ew152,ew153],lh 4 [343,0,53,67,344,11,14,398,19,20,358,386,433,37] [0x8163630707242499,0x15aa355070455281,0xc0214123b2402018,0x6316d10103]⟩,
  ⟨49,5,[ew31,ew150,ew151,ew149,ew152,ew416],lh 4 [53,11,20,67,351,19,344,362,418,14,345,452,354,465,545] [0xa553938806062125,0x1221193112212010,0xb443700703706004,0xe33dc4]⟩,
  ⟨49,5,[ew150,ew151,ew149,ew152,ew416,ew419],lh 4 [53,11,362,20,355,67,351,0,37,418,19,346,344,596,14] [0x4334145113313010,0x20020220c0061441,0x7ba69988d6650220,0xa77be575]⟩,
  ⟨49,5,[ew150,ew151,ew149,ew453,ew153,ew416],lh 4 [53,362,20,14,355,67,57,344,343,19,37,597,418,590,598] [0x2662235242241410,0x77005b010014664,0x553aa98c35381771,0xe9d33]⟩,
  ⟨49,5,[ew454,ew150,ew151,ew149,ew153],lh 4 [14,19,20,53,11,67,25,344,545,549,567,57,447,343,599,37] [0x70600b05445bb040,0xcc0d05c5070e66e7,0x115855110805df0,0x24cc262434466233,0x1bb882124992c229,0x6aa3993a3699282b,0x1a8a3e37177e7313,0xa1ad8dd1]⟩
]
def nodesBlock19 : Array Node := #[
  ⟨49,5,[ew454,ew150,ew151,ew149,ew152,ew153],lh 4 [19,0,347,53,11,25,343,344,57,67,358,397,20,204,386] [0x199626275758484,0x10aad442c2545301,0x263073bbe3533210,0x1010010162]⟩,
  ⟨49,5,[ew454,ew150,ew151,ew149,ew153,ew416],lh 4 [397,20,358,53,14,67,57,344,343,19,346,418,447,545] [0x4554544530301212,0x62166121121301a4,0x8b07700770033026,0xd9c89]⟩,
  ⟨49,5,[ew150,ew455,ew151,ew149,ew152,ew153],lh 5 [37,53,14,343,20,0,57,344,67,600,25,19,397,363,517,549,354,545,345,601,346,602,571,386,433,418] [0x4080320ce1390c6,0xd530c92929102,0x80b65ac5515003,0xc01ce6b58cb8541,0x23128a10c81ef]⟩,
  ⟨49,5,[ew456,ew150,ew151,ew149,ew152,ew153],lh 4 [19,67,398,25,336,53,14,20,0,37,11,386,363,523] [0x80161624993535a7,0x8016172424353580,0xd130c031b1424270,0x6010020421]⟩,
  ⟨49,5,[ew150,ew151,ew149,ew152,ew457,ew153],lh 5 [25,355,362,347,53,11,14,343,20,398,361,517,0,595,19,194,363,523,67,465] [0x404282a12501004,0x1089529e128425,0x5ae020084000840,0x19ce338c6730cd1,0x193739ad61a46]⟩,
  ⟨49,5,[ew32,ew31,ew150,ew151,ew149,ew152],lh 5 [25,57,53,14,19,0,398,67,354,571,355,518,465,600,37,595,386] [0x598020094129124,0x100816858528ca6,0x40221de471840,0x204838ce10a0c1,0x19c6800e03]⟩,
  ⟨49,5,[ew28,ew150,ew151,ew149,ew417,ew153],lh 5 [382,53,67,37,25,355,351,19,517,336,14,354,0,204,344,345,470,358,363,418] [0x7884618841705a0,0x1860004a080847,0x2048108ca001620,0x98d235250891024,0x1876296b]⟩,
  ⟨49,5,[ew150,ew151,ew458,ew149,ew152,ew153],lh 5 [336,25,67,53,19,344,11,20,358,361,0,523,354,382,346,541,194,603,345,386,397,363,37,526,14,604,350,545] [0x301e039dcd28ca3,0x1ca254a60642046,0xaaa10d26108c01,0x5af44cab02b8ac0,0x3641118c20002]⟩,
  ⟨49,5,[ew459,ew150,ew151,ew149,ew152,ew153],lh 4 [0,67,25,14,53,355,20,19,37,386,363,387,336] [0x713138824245656,0x513135665242407,0x3120a02191244207,0x103c0b031]⟩,
  ⟨49,5,[ew150,ew151,ew149,ew152,ew153,ew460],lh 5 [37,347,53,25,343,336,355,0,204,57,386,397,363,517,545,14,67,11,433,486,19] [0x819080100418862,0x528a028229324e6,0x90043189ad6316b,0x3cca10942420401,0x2877bdce]⟩,
  ⟨49,5,[ew461,ew150,ew151,ew149,ew152,ew153],lh 5 [67,355,37,25,57,336,53,19,347,344,354,470,14,0,386,433,595] [0x415051986609024,0x10461099a760160,0x288242040101045,0x7886948c60700a2,0x20001d4a38840]⟩,
  ⟨49,5,[ew150,ew151,ew149,ew462,ew152,ew153],lh 4 [53,20,19,355,362,344,0,37,14,336,549,67,561] [0x1331311331735050,0x440400450051261,0xbb7627aa87994254,0x826226268c]⟩,
  ⟨49,5,[ew150,ew151,ew463,ew149,ew152,ew153],lh 4 [67,362,19,0,37,53,355,14,20,341,346,363,336,433] [0x60799466a881615,0x5010145415516232,0xd023237070c412b1,0x3032432340]⟩,
  ⟨49,5,[ew150,ew151,ew149,ew152,ew464],lh 5 [355,37,19,14,53,363,0,362,336,347,194,545,605,382,67,546,585] [0x695a0200052b484,0x410421e108100,0x539401800e02863,0x180a1094650040,0x2a1040848841425,0x2308719cec39064,0x3b0e5108ac29c47,0x8c295a52318561,0x48921318220a4c9,0x198cb12d6630c42]⟩,
  ⟨49,5,[ew28,ew150,ew151,ew149,ew152,ew464],lh 4 [25,347,0,14,37,362,19,194,545,355,350,382,358,336] [0xba2884141050577,0x1d02626c93414109,0x2423134500203530,0x36231]⟩,
  ⟨49,5,[ew150,ew151,ew149,ew152,ew153,ew464],lh 5 [53,14,25,37,355,67,347,57,343,517,336,19,358,194,362,363,418] [0x610811986610040,0x1000221ce421da4,0x8404a5e0005c0,0x5210a1a20319823,0x16b094a1094a1]⟩
]
def nodesBlock20 : Array Node := #[
  ⟨49,5,[ew465,ew150,ew151,ew149,ew152,ew153],lh 5 [37,362,53,14,336,57,67,19,344,25,447,354,0,11,606,607,355,387] [0x7180401122489a5,0x30c0401022089e7,0x8c201020529cc3,0x8814a1802840501,0x18760d6b]⟩,
  ⟨49,5,[ew28,ew150,ew151,ew149,ew152,ew466],lh 4 [37,362,19,336,14,53,25,0,355,447,11,608,607,358,609] [0x65c2b403036161a8,0x507272d84030365,0x720994012e151153,0x42740]⟩,
  ⟨49,5,[ew28,ew150,ew151,ew149,ew153,ew419],lh 4 [37,344,343,53,67,14,355,382,362,0,350,544,11,358,19] [0x45a44902021818c7,0x65bb9602021317a4,0x20351331131330d6,0xe5022002]⟩,
  ⟨49,5,[ew32,ew150,ew151,ew149,ew152,ew418],lh 4 [37,14,336,25,0,382,194,53,57,447,67,486,345,544,386,19] [0xc4b1410202373466,0x20d5815102023835,0x29910733f31e120,0x1aa120]⟩,
  ⟨49,5,[ew150,ew151,ew467,ew149,ew152,ew153],lh 5 [14,0,25,11,336,344,20,347,361,504,19,447,545,53,350,383,67,610,345,386,363,37,611,346,535,387] [0x19de7319c328cad,0x14a254202318200,0x10682102624a482,0x114ac06e0b02a4,0x18c08081c856b]⟩,
  ⟨49,5,[ew468,ew150,ew151,ew149,ew152,ew153],lh 4 [25,67,57,20,53,19,14,37,0,336,354,386,363,523,545] [0x8516167704042323,0x2316122332040485,0xd105c001b1044032,0xe515aa5991]⟩,
  ⟨49,5,[ew469,ew150,ew151,ew149,ew152,ew153],lh 4 [37,57,25,355,53,0,362,336,14,447,595,67,486,19,363,418] [0xc5b8070724241313,0x13133107012424d5,0x8065e62662204031,0xaa5805f099]⟩,
  ⟨49,5,[ew150,ew151,ew149,ew470,ew152,ew153],lh 4 [67,25,37,20,344,57,14,53,19,518,0,11,386,336,433,571] [0x603b33523251757,0x40c4411412713553,0x60998220e0d21441,0x68068faa60]⟩,
  ⟨49,5,[ew150,ew151,ew471,ew149,ew152,ew153],lh 4 [53,37,67,344,11,14,0,19,20,341,350,386,336] [0x452499144a883030,0x5b0310130034764,0x5276765252c10630,0x6225167112]⟩,
  ⟨49,5,[ew150,ew151,ew149,ew472,ew153],lh 5 [25,204,19,336,67,37,14,53,57,545,612,344,343,382,0,548,586] [0x6800138420034e7,0x943018de528461,0x41101304240a0c6,0xb8281090e40441,0xc07294e3180a0,0x3a8e02000a01c84,0x280b12d6a58042,0x198c5210a628c84,0x1884c4b18210d23,0x325241088949846]⟩,
  ⟨49,5,[ew32,ew150,ew151,ew149,ew472,ew153],lh 4 [37,344,14,343,336,57,25,545,382,19,67,204,346,361] [0x1877c203036161b5,0x40d595282030315,0x3344004611912624,0x2aa24]⟩,
  ⟨49,5,[ew150,ew151,ew149,ew152,ew472,ew153],lh 5 [53,336,57,355,344,25,347,19,0,37,397,354,67,204,361,386,433,387] [0x10da24852120080,0x80091b84310c62,0x29085014a0529e0,0x5ae26098c109a01,0x10741d0741d8c]⟩,
  ⟨49,5,[ew32,ew150,ew151,ew149,ew473,ew153],lh 4 [25,344,14,67,347,433,53,19,336,11,354,606,613,57,361,614] [0x16c7b25454010199,0x664ed73232545416,0xa788328011003f00,0x2332a]⟩,
  ⟨49,5,[ew32,ew150,ew151,ew149,ew152,ew419],lh 4 [37,19,53,362,343,67,382,0,346,615,347,11,361,14] [0x71857504043232b6,0x6156990404323287,0xa0213125353020c1,0xd114100a]⟩,
  ⟨49,5,[ew474,ew150,ew151,ew149,ew152,ew153],lh 4 [339,53,344,19,11,67,37,14,362,57,0,20,354,194] [0xa357570606212199,0xd447544b04b121a3,0x682281885201043,0x7353cc3060]⟩,
  ⟨49,5,[ew475,ew150,ew151,ew149,ew152,ew153],lh 5 [67,25,347,11,0,336,37,344,20,524,361,57,616,345,350,14,346,19,358,386,363,418,343,617,545] [0x70045115a761d63,0x409290a224811e0,0x2854a20c7200c62,0x10024a042098422,0x30005cd6a98c0]⟩
]
def nodesBlock21 : Array Node := #[
  ⟨49,5,[ew150,ew151,ew476,ew149,ew152,ew153],lh 5 [37,0,67,11,344,25,53,341,358,361,386,397,618,619,204,620,345,336,363,517,347,350,14,346,19,433,418,621,545] [0x39c031b58321886,0x2c1e44a423421c3,0x986415ad4a28225,0xc8b01b86c2a8a80,0x38216c01d0002]⟩,
  ⟨49,5,[ew477,ew150,ew151,ew149,ew152,ew153],lh 4 [20,355,362,19,0,25,14,37,11,347,67,336,344,447] [0x43a6a69925251818,0x4001101001012043,0x672cc45225b7b203,0x63433437dd]⟩,
  ⟨49,4,[ew414,ew420,ew149,ew152,ew153],lh 5 [53,14,25,11,336,383,204,517,447,354,0,194,361,386,363,622,19] [0x58c61318a510040,0x70001680800086c,0x5052979108090e7,0x150]⟩,
  ⟨49,4,[ew414,ew151,ew149,ew421,ew153],lh 4 [53,11,20,25,19,336,0,433,204,386,363,341] [0x314611281713030,0x455b2504a0029030,0x246256]⟩,
  ⟨49,4,[ew414,ew151,ew149,ew152,ew424],lh 4 [25,11,20,336,14,53,447,341,0,383,204,194,386,363] [0x3012b114a4930115,0x23664302d004c005,0x828277]⟩,
  ⟨49,4,[ew150,ew420,ew413,ew152,ew153],lh 5 [383,53,347,541,336,540,397,517,354,0,25,11,504,386,363,387,14,19] [0x180602956000540,0x704c66858208803,0x4c10879082110e7,0x131]⟩,
  ⟨49,4,[ew420,ew149,ew413,ew152,ew153],lh 4 [382,25,541,19,11,0,14,540,539,524,386,363,336] [0x13b116a190101282,0x4400432257762c0,0x535340]⟩,
  ⟨49,4,[ew79,ew150,ew420,ew152,ew153],lh 5 [336,53,507,447,354,358,361,397,517,0,541,25,504,523,387,524,204,194,386,363,14,19] [0x700636818002d40,0x888a5809e110484,0x4d108984e7904c6,0x135]⟩,
  ⟨49,4,[ew150,ew420,ew149,ew478,ew153],lh 4 [57,386,336,14,19,623,67,355,354,0,383,347,53,624] [0x7007630302a21055,0x42323614d1c31b21,0x949488]⟩,
  ⟨49,4,[ew479,ew150,ew420,ew149,ew153],lh 4 [67,25,0,14,53,19,11,383,362,336,363,354] [0x1420050330803003,0xa114416526697714,0xb25212]⟩,
  ⟨49,4,[ew150,ew420,ew149,ew152,ew480],lh 4 [11,336,363,347,67,625,507,19,0,383,14,624,25] [0x80070a4066902055,0x131331c224b21312,0x844731]⟩,
  ⟨49,4,[ew481,ew150,ew420,ew149,ew152],lh 4 [19,347,53,11,0,336,67,358,397,344,25,383,507,386] [0x3204604001900343,0xd252217763c1b1a2,0x511588]⟩,
  ⟨49,4,[ew150,ew420,ew149,ew421,ew153],lh 4 [11,343,0,14,53,344,67,19,383,386,397] [0x720036001805004,0x16314252a3935141,0x26237112]⟩,
  ⟨49,4,[ew423,ew150,ew420,ew149,ew153],lh 4 [11,343,0,14,67,53,344,19,386,397,383] [0x2423413139833040,0x6151072001a06005,0x71125262]⟩,
  ⟨49,4,[ew150,ew420,ew149,ew152,ew424],lh 4 [11,343,0,14,53,344,67,19,383,386,397] [0x720036001805004,0x16314252a3935141,0x26237112]⟩,
  ⟨49,4,[ew426,ew150,ew420,ew149,ew152],lh 4 [11,343,0,14,344,53,67,19,383,386,397] [0x6223171225427020,0x4151036001804005,0x1631a393]⟩
]
def nodesBlock22 : Array Node := #[
  ⟨49,4,[ew151,ew149,ew413,ew421,ew153],lh 4 [25,11,382,433,541,14,517,0,53,386,363,336,19] [0x66a0059010020380,0x21122134434354b1,0x7c7512]⟩,
  ⟨49,4,[ew150,ew151,ew149,ew421,ew424],lh 4 [11,343,344,14,53,361,362,447,336,0,383,67,194,363,19] [0x55c003b001a02004,0x7731622d23632141,0x9e938118]⟩,
  ⟨49,4,[ew426,ew150,ew151,ew149,ew421],lh 4 [19,0,25,53,336,11,20,397,433,344,383,204,386] [0x110100102900110,0x233266b554a42323,0x488477c3]⟩,
  ⟨49,4,[ew150,ew482,ew149,ew152,ew153],lh 4 [53,11,0,19,336,347,14,447,362,20,383,204,386,363] [0x132116b115a59080,0x776402d006c04005,0x23234234]⟩,
  ⟨49,4,[ew150,ew151,ew149,ew421,ew153],lh 5 [14,11,336,25,361,504,517,354,0,53,524,383,204,194,386,363,37,387,19] [0x81800896250429,0x181c329443211a1,0x39e2204002319e3,0x44900]⟩,
  ⟨49,4,[ew150,ew151,ew149,ew152,ew483],lh 4 [25,11,336,53,0,19,358,397,447,418,383,204,386,363,523,14] [0x154166b112a10303,0x88e205d077c00320,0x454f2992]⟩,
  ⟨49,4,[ew423,ew150,ew151,ew149,ew424],lh 4 [25,336,11,0,19,53,204,386,447,358,397,523,14,383,363] [0x343c88b1a0779266,0x1510243221d20505,0x134104e0]⟩,
  ⟨49,4,[ew423,ew426,ew150,ew151,ew149],lh 4 [336,11,19,25,0,14,363,53,204,386,447,383] [0xa050539351814242,0x3117402023662141,0x70310b0]⟩,
  ⟨49,4,[ew151,ew149,ew413,ew152,ew424],lh 4 [20,418,382,11,383,25,386,397,363,0,53,336,204] [0x50887766323251a1,0x3322c01041441b1,0x909002]⟩,
  ⟨49,4,[ew150,ew484,ew149,ew152,ew153],lh 4 [343,344,57,53,67,14,20,11,336,19,383,386] [0x7227254220a06613,0x450311314b11030,0x59498008]⟩,
  ⟨49,4,[ew150,ew151,ew149,ew485,ew153],lh 4 [344,343,57,53,433,67,20,11,19,0,383,386,37] [0x7227665221a10203,0xc441300305b00131,0x98984114]⟩,
  ⟨49,4,[ew150,ew151,ew149,ew152,ew424],lh 4 [14,19,336,344,343,0,57,447,53,383,204,386,25] [0x515160a064943638,0x7702c13130b02424,0x1502512]⟩,
  ⟨49,4,[ew486,ew150,ew151,ew152,ew153],lh 5 [37,25,341,19,53,14,382,418,0,20,336,523,447,387,580,581,386,363] [0x31600288031809,0x115c20902439da0,0x8e210960510de2,0x40d03]⟩,
  ⟨49,4,[ew486,ew151,ew149,ew152,ew153],lh 5 [25,20,341,524,37,358,19,361,397,517,540,626,0,336,204,539,386,363,580,581,14] [0x295c16848418c01,0x42200009e039cc1,0x5ae6252a424a620,0x61994]⟩,
  ⟨49,4,[ew151,ew149,ew413,ew152,ew464],lh 4 [37,382,53,362,383,194,25,355,20,0,543,336] [0x36632332a1216020,0x57511540040440b1,0x989875]⟩,
  ⟨49,4,[ew151,ew149,ew413,ew472,ew153],lh 4 [37,53,382,57,25,20,344,67,19,204,555,336,545] [0x16611441a2124010,0x3932230c805007b2,0x587593]⟩
]
def nodesBlock23 : Array Node := #[
  ⟨49,4,[ew487,ew427,ew150,ew149,ew153],lh 4 [504,524,53,67,14,37,363,628,518,386,25,19,627,629] [0xa143343040413192,0xc1105066b2502021,0x88d077]⟩,
  ⟨49,4,[ew488,ew427,ew150,ew149,ew153],lh 4 [524,504,0,14,20,37,19,362,397,630] [0x4062635331404387,0x2001512927515740,0x126106]⟩,
  ⟨49,4,[ew489,ew427,ew150,ew149,ew152],lh 4 [25,524,504,0,19,37,362,14,549,363,20,555] [0x143343242413190,0xb1125206600250a0,0x887217]⟩,
  ⟨49,4,[ew490,ew427,ew150,ew149,ew152],lh 4 [344,504,14,524,0,19,37,25,20,630,555,549] [0x354454151534370,0xa231612920016080,0x2b2132]⟩,
  ⟨49,4,[ew427,ew150,ew149,ew428,ew153],lh 4 [504,14,67,53,20,398,0,363,628,547,386] [0x77631a1350304943,0x212886421215040,0x12210550]⟩,
  ⟨49,4,[ew430,ew427,ew150,ew149,ew153],lh 4 [67,20,14,25,53,19,518,386,504,517,363,383,398,631,37] [0x2002082020024007,0xc11b3a9334431314,0x665e15d1]⟩,
  ⟨49,4,[ew427,ew150,ew149,ew431,ew152],lh 4 [20,19,0,524,25,37,67,386,549,504,517,363,631,518,632] [0x77641b1a59540343,0xd2120c6021203003,0x122188e5]⟩,
  ⟨49,4,[ew433,ew427,ew150,ew149,ew152],lh 4 [0,20,25,19,53,14,363,383,37,517,518,397,386,633,549] [0x300303a010039066,0x81772cb224424214,0x5e5815d1]⟩,
  ⟨49,4,[ew430,ew150,ew151,ew149,ew153],lh 4 [19,20,25,14,53,0,386,336,398,11,339,383,363] [0x503773a66431913,0x24421050811b2421,0x80520c2]⟩,
  ⟨49,4,[ew150,ew151,ew149,ew428,ew431],lh 4 [0,67,25,336,19,20,11,14,53,386,363] [0x404171563532625,0x317120a021912832,0x1043040]⟩,
  ⟨49,4,[ew433,ew150,ew151,ew149,ew428],lh 4 [0,67,53,19,25,20,37,14,363,336,383,386] [0x3001093008403003,0x42261715655a4245,0x617621b2]⟩,
  ⟨49,4,[ew491,ew150,ew149,ew152,ew153],lh 4 [355,53,37,0,67,19,25,386,363,336,20,433] [0x1831174121161060,0x24b20530400a0920,0x34352352]⟩,
  ⟨49,4,[ew492,ew150,ew151,ew149,ew152],lh 4 [355,53,0,37,67,19,25,20,433,363,336,386] [0x52243a3219120205,0x6113400707306001,0x348814b1]⟩,
  ⟨49,4,[ew430,ew150,ew151,ew149,ew431],lh 4 [358,20,67,19,53,398,0,386,344,567,14] [0xa226295277421010,0x8445036001101001,0x35364383]⟩,
  ⟨49,4,[ew433,ew430,ew150,ew151,ew149],lh 4 [19,14,20,53,67,344,398,358,0,386,383] [0x8006053007201004,0x2352411419311421,0x5336622a]⟩,
  ⟨49,4,[ew433,ew150,ew151,ew149,ew152],lh 4 [67,20,53,37,0,362,19,14,363,347,383] [0x6040393428241416,0x52230701311a1251,0x30702050]⟩
]
def nodesBlock24 : Array Node := #[
  ⟨49,4,[ew493,ew150,ew149,ew152,ew153],lh 4 [67,20,53,37,0,362,19,363,383,355,14] [0x2742050232251512,0x30a0164109013118,0x40063463]⟩,
  ⟨49,4,[ew494,ew150,ew151,ew149,ew153],lh 4 [67,20,53,37,0,362,19,355,347,383,363] [0x6004083005201007,0x5223164131191251,0x346324a2]⟩,
  ⟨49,4,[ew427,ew150,ew149,ew152,ew153],lh 4 [19,14,57,344,67,53,343,20,0,362,383] [0x305191366535332,0x14147020214127a2,0x10400808]⟩,
  ⟨49,4,[ew150,ew420,ew149,ew152,ew153],lh 4 [19,14,343,344,57,53,67,0,383,362] [0x7040416142823435,0x1612503031913252,0x10600207]⟩,
  ⟨49,4,[ew495,ew150,ew151,ew149,ew152],lh 4 [0,362,518,53,347,19,355,344,14,11] [0x5005024007106005,0x1332966824241313,0x24423113]⟩,
  ⟨49,4,[ew496,ew150,ew151,ew149,ew153],lh 4 [67,14,344,53,343,549,11,57,397,387] [0x1001011008201001,0x2334677654542323,0x54493223]⟩,
  ⟨49,4,[ew150,ew151,ew149,ew152,ew497],lh 4 [20,67,336,347,362,363,355,19,354,0,37,14] [0x790061060030650,0x2132475454412323,0xb11788a2]⟩,
  ⟨49,4,[ew150,ew151,ew149,ew498,ew153],lh 4 [53,343,386,14,204,57,344,37,447,336,545,20,11,19] [0x4554c44351b12020,0x8877066003232101,0xada39119]⟩,
  ⟨49,4,[ew414,ew151,ew149,ew152,ew464],lh 4 [25,67,14,362,53,347,20,194,341,37,11] [0x40a7761212950404,0x6521213003033105,0x211288]⟩,
  ⟨49,4,[ew414,ew151,ew149,ew472,ew153],lh 4 [25,19,53,14,545,67,343,11,344,341,37,336] [0xb041417753a60202,0x1499352882200306,0x315114]⟩,
  ⟨49,4,[ew150,ew149,ew152,ew415,ew499],lh 4 [355,362,20,347,14,57,19,344,433,37,634] [0x1012500520020220,0x74614a4316393438,0x171]⟩,
  ⟨49,4,[ew27,ew150,ew151,ew149,ew444],lh 4 [14,362,347,355,19,20,0,53,37,634] [0x1506408801700350,0x9112723463325213,0x264214]⟩,
  ⟨49,4,[ew446,ew150,ew151,ew149,ew152],lh 4 [14,362,347,355,19,0,20,344,37,53,433] [0x504882517143534,0x1292603032621316,0x20a7010]⟩,
  ⟨49,4,[ew454,ew150,ew151,ew149,ew153],lh 4 [11,25,14,347,53,20,344,19,0,37] [0x2872992321612050,0x1441078003501015,0x38734664]⟩,
  ⟨49,4,[ew500,ew150,ew149,ew152,ew153],lh 4 [19,37,0,53,11,347,20,386,592,14,363,555] [0xa03779313153463,0x1551202088b41614,0x20200202]⟩,
  ⟨49,4,[ew501,ew150,ew151,ew149,ew152],lh 4 [19,347,0,67,25,53,37,363,20,592,386] [0x323200277500220,0x4151893861614545,0x611343a4]⟩
]
def nodesBlock25 : Array Node := #[
  ⟨49,4,[ew150,ew149,ew502,ew153,ew416],lh 4 [53,57,20,67,355,343,19,362,418,37,635] [0x4114211220101221,0x70330956580303,0xa67]⟩,
  ⟨49,4,[ew31,ew150,ew151,ew149,ew453],lh 4 [14,344,53,57,67,343,20,37,635] [0x1204047721216363,0x8015213040356512,0x40510]⟩,
  ⟨49,4,[ew503,ew150,ew149,ew152,ew153],lh 5 [20,37,53,0,343,386,363,636,600,549,354,545,344,397,555,632,629,14] [0x295a20882403002,0x39dc00800431862,0x52a014a5e142060,0x5ac71]⟩,
  ⟨49,4,[ew504,ew150,ew151,ew149,ew153],lh 4 [20,37,343,53,14,25,0,11,386,545,600,363] [0x4699121288547704,0x5331aa6010020350,0x122136b3]⟩,
  ⟨49,4,[ew150,ew149,ew505,ew152,ew153],lh 5 [53,11,67,507,358,194,361,336,354,397,517,19,0,541,20,344,347,523,387,386,363] [0x210417002018da1,0x38a220400f318a5,0x52a804a66042247,0x62d8b]⟩,
  ⟨49,4,[ew150,ew151,ew149,ew152,ew506],lh 4 [336,53,418,11,67,19,25,358,0,386,363,523,14] [0x3583774320236161,0x4b018a114910202,0xc5450220]⟩,
  ⟨49,4,[ew150,ew151,ew149,ew472,ew153],lh 4 [53,25,19,336,67,37,57,11,344,204,343,14] [0x9262774653531010,0x3454088001101001,0xb2422a23]⟩,
  ⟨49,4,[ew150,ew151,ew149,ew152,ew464],lh 4 [344,14,67,53,19,362,336,418,194,11,343] [0x9884212176760303,0x1212500505510330,0x14214a46]⟩,
  ⟨49,4,[ew150,ew151,ew149,ew466,ew417],lh 4 [37,53,19,14,336,0,25,11,637] [0x1073525204046161,0x405201361128140,0x235330]⟩,
  ⟨49,4,[ew28,ew150,ew149,ew152,ew507],lh 4 [362,37,336,53,14,355,11,25,447,637,358] [0x1212707094121266,0x3103088410553a54,0x30]⟩,
  ⟨49,4,[ew150,ew149,ew508,ew152,ew153],lh 5 [53,11,14,347,336,383,638,397,517,545,344,20,204,194,361,343,387,386,363,0] [0x89825814008ca5,0x20c4403c030b9a1,0x4224039e2031a04,0x4a662]⟩,
  ⟨49,4,[ew150,ew151,ew149,ew509,ew153],lh 4 [433,336,53,11,25,14,0,361,397,517,639,19,204,386,363,387] [0x776335c301034242,0x100199e288d21010,0xbb65aaf1]⟩,
  ⟨49,4,[ew150,ew151,ew149,ew473,ew418],lh 4 [53,14,0,344,347,19,433,11,640,387,354] [0x477212164643030,0x5912120530018030,0x12215a]⟩,
  ⟨49,4,[ew32,ew150,ew149,ew510,ew153],lh 4 [336,37,25,67,57,19,11,347,640,53,361,354] [0x1010852323101764,0x20b501001a452429,0x233]⟩,
  ⟨49,4,[ew150,ew511,ew149,ew152,ew153],lh 4 [20,344,336,11,339,362,358,14,638,545,67,194,57,629,641,0] [0xcb066a030030310,0x2442511577512421,0x99fe88d2]⟩,
  ⟨49,4,[ew151,ew149,ew512,ew152,ew153],lh 4 [344,11,0,67,53,362,336,358,361,37,347,433,418,642] [0x5002055010140440,0x773162c263b3a191,0x232d8821]⟩
]
def nodesBlock26 : Array Node := #[
  ⟨49,4,[ew513,ew151,ew149,ew152,ew153],lh 4 [37,344,11,0,362,53,347,67,358,361,14,433,418] [0x9932887206021225,0x6b0411314411050,0xa73a03c0]⟩,
  ⟨49,4,[ew150,ew149,ew514,ew152,ew153],lh 5 [20,336,11,37,25,341,643,638,517,545,204,358,194,361,433,418,386,14,363,644,0] [0x2d400084029462,0x319c11842303580,0x422442460439de1,0x4a693]⟩,
  ⟨49,3,[ew150,ew149,ew478,ew480],lh 3 [19,14,386,623,383,336,67] [0x8234e418c59764,0x42]⟩,
  ⟨49,3,[ew490,ew488,ew150,ew149],lh 3 [504,524,0,19,37,20] [0x820a694186514da,0x44]⟩,
  ⟨49,3,[ew27,ew150,ew149,ew499],lh 3 [14,362,347,20,355,37,19] [0x1c8c2e2681c2d118,0x2]⟩,
  ⟨49,3,[ew31,ew150,ew149,ew502],lh 3 [53,57,20,343,67,37] [0x40d020b4c412d451,0x3]⟩,
  ⟨49,3,[ew150,ew149,ew417,ew507],lh 3 [37,53,336,14,25,11] [0x18422180a186b082,0x3]⟩,
  ⟨49,3,[ew150,ew149,ew510,ew418],lh 3 [53,0,347,433,11,19,387,354] [0x122fb8106420869a]⟩,
  ⟨55,8,[ew179,ew180,ew181,ew182,ew183],lh 5 [51,651,58,7,20,245,43,650,9,517,652,21,57,654,16,17,145,14,48,15,645,646,647,648,649,653,655] [0xb3e4fa99cea4250,0x8e701926c4097,0x88a2018e600922,0x8a62098a609a66,0x53c6f53e3150862,0x3129010e750a22,0xb0ac01129030ec,0xb16b090a409164,0x5386e5390851064,0x34b90256b51108,0x350d024a50356d,0x346301d0701c7a,0x9505094630ad08,0xac63]⟩,
  ⟨55,7,[ew56,ew179,ew180,ew182,ew183,ew181],lh 5 [656,659,21,48,660,9,145,657,664,517,58,245,7,57,14,661,51,15,42,651,652,43,20,658,662,663] [0x406339cf5040c6,0xcc42086313dcf6,0x211ce084420ce31,0x210a5251ce250a5,0x252001ef04252,0x39c633e4f8041ef,0x98420a96b3a8ea,0x2298c0a84209966,0x229ca21986219c6,0x2908029ea01906,0x8c420b56b019e6,0x2358d0b44d08d63,0x234a520d8320ca3,0x350d0352d00d03,0xad8c088a500d29,0x929089820aca5,0x90202d2902d08,0x31290310801529,0x1505]⟩,
  ⟨55,7,[ew179,ew180,ew515,ew182,ew183,ew181],lh 5 [665,666,42,667,245,43,7,20,21,9,16,17,664,657,15,14,517,658,51,651,652,662,663,145,48] [0x8c4e7695a56d9b5,0xac848c63701645,0xad0b0948509505,0x1accb1ad2b194c5,0x4202e0b19525,0x1e4702c4200210,0x9d070a9ca6b5b8,0x19de70a90a09dce,0x19d271a9ef1a92a,0x42002100284a,0xcdce0848402a0a,0x18cc6085ce0cc84,0x18def1d0c61d1ef,0x18c000420498c,0x90c60a12904842,0x20480a0c809124,0x2188010440118c,0x18460198c02449,0x2589]⟩,
  ⟨55,7,[ew60,ew179,ew180,ew182,ew183,ew181],lh 5 [668,669,48,670,21,17,657,9,42,57,15,43,245,7,14,664,654,517,51,650,651,652,145,16,658,648,663,653,655] [0x4842318d6048a5,0xd14a08484360d7,0x18ce70854a0d084,0x18dce1d4e71d5ce,0x1ef00108049ef,0x314c53184204908,0xac840958c368d9,0x1adab094850ad8b,0x1aceb195a5194e5,0x1ef0010802deb,0x88820a58c02d08,0x1a5a90a48908982,0x1a4e9189a2188e2,0x25090262900908,0xa9ad090e700a31,0x2a2a091c40a8ea,0x2a100322c0321b,0x360d0367c03a10,0x3a73]⟩,
  ⟨55,7,[ew49,ew179,ew180,ew182,ew183,ew181],lh 5 [671,672,20,673,145,517,58,14,24,21,9,42,15,657,245,7,2,650,16,654,658,51,651,652,43,48,648,663,653,655] [0x5442a529805484,0xd908085ce6b5b9,0x18def085080d9ce,0x18e101ddef1de10,0x231000a505631,0xa5042691a4054a5,0x9124099086edba,0x19a060992909108,0x1994a1921019144,0x18a601966010a5,0x89290c9920116b,0x188e20c93208982,0x189421c8e71c952,0x16b000a500962,0xb0e70a54a008a2,0x316c0a4e70b14c,0x32730396e03a7c,0x3e6f03e3d01e73,0x1e31]⟩,
  ⟨55,6,[ew56,ew515,ew182,ew183,ew181],lh 5 [674,675,58,16,21,661,664,48,14,245,7,676,15,20,9,42,657,648,658] [0x8d8c84a11034e7,0x8c830b58c0b484,0x58d0858dc35b50d,0xa500de35b5ce,0x892200ca3001ef,0x898209d2909d8c,0x59d4a59d0858942,0x8a201cc758902,0x91ce01ca5008c6,0x91440a5c90a54a,0x24a9024c6010a4,0x28c6020a8010c4,0x20c6028aa]⟩,
  ⟨58,7,[ew194,ew195,ew196,ew197,ew198],lh 5 [678,11,25,679,5,24,7,6,48,245,60,23,2,1,0,67,677,4] [0x804818044282088,0x20a50052182048,0x184c1004a102129,0x185811a0c61a18c,0x544e75456b504e1,0x1129008a550561,0x1898200922010a4,0x188c219184190c6,0x51164510e750962,0x24c6035ed508e2,0x15c5034cd025ef,0x14e7035ce034ed,0x1bd6f1bdce1b16b,0x1b1ce]⟩,
  ⟨64,7,[ew149,ew160,ew171,ew219,ew187],lh 5 [678,680,39,70,2,23,71,145,48,7,5,6,43,53,14,19,20,681,651,682,46,4] [0x30c60320c008c2,0x9a20306c00a02,0x882031ad00863,0x9c201c8701dce,0x50b4051ef01ca7,0x98630c1ad01de7,0x99c60c063099a6,0x98840a1c80a084,0xd5f50d4a50a1e8,0x8a92988c840a0a8,0x90ca588d298a88a,0x90d6b928aa9296a,0x9a4a99a56b990a5,0x9916b]⟩
]
def nodesBlock27 : Array Node := #[
  ⟨69,8,[ew195,ew230,ew231,ew232,ew233],lh 6 [683,19,21,9,28,7,56,57,16,27,20,196,693,694,33,6,14,11,245,55,15,684,685,686,331,687,688,224,689,690,691,692,695,696,697,211,698] [0x28a00444400b28a,0x54408200b44b004,0x4985cb08258e48e,0x70b15b6844d3644,0x417c415e74b0c3,0x34e04134e3cf304,0x820071863043cf,0x708200a18600a,0x1480080c3007145,0x80480070c3008,0x8007041007007,0x8541458060c3008,0x2499024238940c3,0x346246346046302,0x249310041302042,0x310249345041345]⟩,
  ⟨69,7,[ew230,ew16,ew195,ew231,ew232,ew233],lh 5 [699,700,9,71,27,234,15,7,28,6,56,20,704,705,16,19,683,11,21,57,706,14,693,694,707,194,196,245,701,702,703,223] [0xe0300c0302e0b,0xd0302cab02c0b,0x44d102d0b00ca5,0x465200cc600e43,0x3aae0384200ea3,0x4c19039ee00c43,0x40a50380e04df3,0xf03b040c60843a,0x84420f4e708442,0x6dd29658840f8e7,0xd03f659296dc84,0xa0480a0280854a,0xa0e809445094e7,0x694856952562084,0xa18e6c284262129,0x61884a28eac1842,0x619266a88a6a92a,0x69def69c84609e2,0x60882]⟩,
  ⟨69,7,[ew230,ew195,ew231,ew516,ew232,ew233],lh 5 [708,14,11,706,27,245,196,16,711,700,55,19,712,33,20,683,9,57,7,6,21,693,694,194,223,234,701,709,710,713,714,702] [0x8c200802039ad,0x380e008a20380e,0x1de700802038ae,0x1c07009e200802,0x1c2101e0700822,0x441701c8700a02,0x48d3801c0704491,0x19e618ca549926,0xd9a464b42118f59,0x41884e365249821,0x41a666348d63673,0x1f6104a534015f4,0x18c211954519421,0x614856156542084,0x18c211f94a4216b,0x4548418c211fd4a,0x4556b658846596b,0x6296a6288a40561,0x40481]⟩,
  ⟨69,7,[ew103,ew230,ew195,ew231,ew232,ew233],lh 5 [715,700,19,196,20,21,9,11,719,720,16,7,57,15,706,56,14,33,27,683,693,694,6,55,237,245,716,702,717,718,194,331] [0x84000e704c84,0x843804c6304ce7,0x86f70b83904ca5,0xf43c084c60ec3a,0x4d4424d43545042,0x300c0106a45034,0x31ef0100403063,0x1ca5011e4010a4,0x2a0a028c601e07,0x301e0284a01cc7,0x84a50280a0304c,0xc6100b83f08c23,0xc56b08e1008d63,0x4c4514c6d140c43,0x7356b714c540ed6,0x4364d71565734cd,0x4344d4be4f4bc42,0x4ac424ae5241846,0x41a52]⟩,
  ⟨69,7,[ew19,ew230,ew195,ew231,ew232,ew233],lh 6 [721,14,27,28,245,9,16,726,20,700,706,727,11,234,6,19,683,707,57,7,237,55,702,693,694,196,56,722,723,724,725,194,331,728,729,193,730,731] [0x30c00020801030c,0x100c3010208000,0x25a01010428a299,0x71604145b145249,0x8279d041456145,0x2d80822d83cf1d7,0xcc00634d1d73cf,0x60c300c34d00c,0x104008008006106,0x8041006006008,0x145006041006145,0x1201f006082008,0x243006006012092,0x24a26028a104243,0x4184d4cd243043,0x1c30828834d324d,0x38e2d40942d43a3,0x2840414641451c3,0x822a5041444145,0x2c40842c438e1c7,0x821c13c11c738e,0x1c10822d53d52d5]⟩,
  ⟨69,7,[ew230,ew76,ew195,ew231,ew232,ew233],lh 5 [732,700,21,27,355,33,245,20,28,9,6,735,736,57,55,14,683,16,702,693,694,737,19,196,706,733,7,734,224] [0x1204010040360d,0x1104044b10340d,0x10c404511010a5,0x104201cc701c42,0x11c40112401dc7,0x340d01c6701d29,0x40a501c0703463,0xe0c60844208437,0x41ce0e4c608442,0x6514a5cc630ec3a,0xa0425cd4a65063,0xa0c809445094c6,0x9425085290c83c,0x61465615455a068,0x919e6a89295a148,0x58862a89ef91929,0x58942618636194a,0x63ace638635becf,0x5bc6f]⟩,
  ⟨69,7,[ew230,ew195,ew231,ew232,ew517,ew233],lh 5 [738,15,702,19,11,16,56,27,20,7,234,739,700,196,740,6,683,21,57,245,706,9,693,694,194,709,728,224,28,734,741,742] [0x11a401004021ad,0x22280102402008,0x11240122402021,0x10040152501405,0x16050140502208,0x48180146502008,0x628210140504872,0xd2a7363421cb66d,0x109296298a6099b,0x5b46310bbc02a0a,0x5b5ef7286a729ea,0x104411052911bd1,0x1068111be611926,0x584e711a8610441,0x585e1718e6719e6,0x5ac636319502615,0x5ace772463724e7,0x75c6375ce75d863,0x5d8e7]⟩,
  ⟨69,7,[ew110,ew230,ew195,ew231,ew232,ew233],lh 5 [743,700,21,57,19,196,16,9,245,14,747,748,20,234,6,27,702,683,11,693,694,15,55,56,237,744,706,745,746,7,194,691] [0x18c002520458c,0x8438044a504652,0x84420e839086f7,0xc03d045290f03b,0x5d0845d03454c84,0xc03018a654c33,0xea30180600ca3,0xc42032b50304c,0x1929018e600d29,0xc030189e00ce7,0xb4420180600c83,0xb5080944209505,0xc03f0b42d084e7,0x5b4845b5cd51485,0x82128808e7515ce,0x509e280922820e8,0x509ce5a1ef5a1ce,0x5d8965d9ef51c84,0x51def]⟩,
  ⟨69,7,[ew47,ew230,ew195,ew231,ew232,ew233],lh 6 [749,11,15,19,33,16,21,7,28,753,700,6,702,754,27,245,683,737,20,57,56,706,693,694,196,722,750,751,752,9,194,710,729,691,755,756,297] [0x41000145010041,0x10208010145000,0x824593cf30c318,0x71b082455186695,0xc328a29d0101c7,0x3570c335738e256,0x20801210425638e,0x12208001101001,0x82012186001081,0x11c1001181012,0x10051c5005005,0x1301e0050c5001,0x820050050130d3,0x2840847c43c4288,0x1c72842848083cf,0x2480c328c2a130c,0x2cb3440c43442c4,0x3021c2446886248,0x3864461e43028c2,0x3543943542cb246,0x2c72490c32462c6,0x2492cb3470c3347]⟩,
  ⟨69,7,[ew230,ew195,ew108,ew231,ew232,ew233],lh 6 [757,196,19,28,16,125,9,21,706,702,761,762,57,56,11,6,27,55,683,707,237,700,737,693,694,194,758,759,760,722,713,730,741,755,15,14,763] [0x4100c0cc004044,0x44840040c300c,0x4005485005005,0x51c5004344004,0x44c0041c4005345,0x545100518500e,0x1900e08e00e18e,0xe00e00c08c00c,0x5416c16814c3543,0x4c31c74c3743701,0x7c32011c1201781,0x2418015831864c3,0x81583843241181,0x2d40942d43cf281,0x2620121c72813c1,0x208223012186249,0x822d83cf297082,0x2092242973cf2d8,0x40720d20d249186,0x2cd4102cd08d287,0x410286082287082,0x2864102d10912d1]⟩,
  ⟨69,7,[ew230,ew195,ew231,ew232,ew518,ew233],lh 5 [764,706,27,11,196,16,28,15,7,19,766,767,20,14,237,702,245,683,57,6,693,694,700,194,765,763,21,9] [0xc8300dce03084,0x300c00ce3030cc,0xd0300c03030ec,0xc03015a501405,0x16250140500e23,0x48170152500c03,0x98e60140504932,0x9a10090e409204,0x791ad79104799ad,0x902409ac679908,0x518420bb06092c4,0x51a735b8425ba6e,0x850809c270bc39,0x51c420843a01e27,0x51d275c0425c129,0x53529085fb02228,0x534425a1295a042,0x5d4355d44255034,0x55042]⟩,
  ⟨69,7,[ew112,ew230,ew195,ew231,ew232,ew233],lh 5 [768,702,237,9,196,15,27,11,20,6,706,771,772,245,57,19,55,683,33,125,700,28,693,694,707,769,21,770,14,194,756,211] [0x1ce00108045ce,0xe6520d04204508,0x44a50d252086b5,0x5295c044630ec3a,0x65cc665def5d8c6,0x4c42020845d9ef,0x1ca70204804c84,0x1c07020a502008,0x4e1004c6301e07,0x381d01cc701c67,0xc08a501c07038ce,0xc09ad510a5511a4,0x90640902408862,0x60922590c608bc2,0x846359129608c6,0x594c55055f5354d,0x59529634cd63529,0x641f06412958de3,0x58d23]⟩,
  ⟨69,7,[ew105,ew230,ew195,ew231,ew232,ew233],lh 5 [773,706,57,28,27,16,19,56,7,20,196,21,775,776,234,14,683,702,6,237,700,693,694,737,774,245,9,770,194,731,193,211] [0x42000a504042,0xe1ce0d063040a5,0x416b0d1ce08463,0xec3a0410808439,0x6d8c66d884654c6,0x862025c965484,0x8e20246300942,0x96b024e702569,0x15050140502509,0x81c0148502409,0x8ce70140500882,0x8fa30a8e70a82a,0x8a9ef8a90ab8de3,0x6ce5e6288ab8d08,0x9c2762a526ccd3,0x62c8b0c43f08508,0x62ccb69c8769cc6,0x6a0c66a08463cc6,0x63c84]⟩,
  ⟨69,6,[ew19,ew230,ew195,ew231,ew232,ew233],lh 5 [9,57,27,245,6,16,28,7,777,234,19,14,683,20,706,700,71,237,707,702,693,694,778,196,15,699,737,331] [0x635a80850d6b021,0xca30c18deebb129,0xd2d730026b5c800,0xa295510aaa55042,0x298c14842609525,0xa03018e0880463,0x8005594a028561,0x2a0a11082809442,0x3000f7edc319906,0x308c639d20024e9,0x90006212228c489,0xb084e39c6000ce7,0x28162106210c84,0x210ea51c84]⟩,
  ⟨69,6,[ew519,ew230,ew195,ew231,ew232,ew233],lh 5 [15,234,19,16,7,11,700,27,21,33,57,237,20,779,6,707,683,28,56,245,706,693,694,780,196,9,194,223] [0x80c6d529a31c14a,0x304265acc1c196b,0x78014422809bd13,0xb1cf5108c6cc084,0x2ad6c086a73d842,0x621850158b61425,0x1b465214a82b00c,0x5374310cad28c83,0x49b610006d1a84a,0x9029324260a409,0x4b93114524204c1,0x10887a22e72442,0x939c038104401e0,0x21cf71080e048f2,0x2e739042]⟩,
  ⟨69,6,[ew230,ew195,ew231,ew516,ew232,ew517,ew233],lh 5 [57,7,27,16,19,196,20,245,706,33,21,297,702,194,223,234,224,781,782,783,6,784,785,14] [0x18003018c018003,0x1800d3000600461,0x895290960f29cae,0x41cf35ac32528a4,0x431160b035a08e2,0x11041112e120882,0x44]⟩
]
def nodesBlock28 : Array Node := #[
  ⟨69,6,[ew47,ew230,ew195,ew231,ew516,ew232,ew233],lh 5 [20,19,16,27,7,33,245,11,706,702,9,28,196,786,707,194,244,700,6,15,787,297,737] [0x439a64198510040,0x11ce21846152928,0x8401000238007,0x890ab598b0005e0,0x8c9525266914a1,0x1842308c8925823,0x64]⟩,
  ⟨69,6,[ew230,ew195,ew108,ew516,ew232,ew233],lh 5 [19,11,196,245,21,16,9,244,55,706,6,788,125,56,27,33,20,57,223,700,711,789,194,28,707,782,787,15,790,14,702] [0x82e017842b0c1ef,0xac2c1b18ba8461,0x2908c6b584615a5,0x9825420a628501,0x2acb10462bb1405,0x38c629884391e72,0x1644741d38b8882,0x3a8e2008fa38902,0x4f36320c4a51c07,0x1a95400129e8cc3,0x4a52431a8a50c00,0x6800471089278c6,0x439c601880035cd,0xce72008]⟩,
  ⟨69,6,[ew230,ew195,ew231,ew520,ew232,ew233],lh 5 [21,28,245,196,27,355,11,9,55,6,19,706,20,791,700,125,683,57,237,16,693,694,194,785,707,784,737,193,14] [0x6042f18de17cc73,0x3000c1318061842,0x334c5814ad29a06,0x31cc5414a729906,0x2b4b12462db1485,0x88230006218400,0xe02370c77185c1,0xe82340c7918501,0xa53254a49d8481,0x38025884e10160,0x2c0239c4b100e0,0x29422104a10080,0xaa5342116be40e7,0x4108751e894d484,0xe422148]⟩,
  ⟨69,6,[ew230,ew195,ew231,ew521,ew233],lh 5 [792,11,20,21,196,27,7,192,700,19,55,9,33,793,794,245,706,57,6,15,56,194] [0x4810040100882,0x862005e100802,0x94200461009e2,0x9620054100561,0x44b104415004a1,0x411e441c6300401,0x4314a41de701064,0x430c641d4741cc7,0x7312c7324c690a4,0x84cc680d4369252,0x68ca380cc684d73,0x68d23750b475129,0x71929718a56ad2b,0x6aca5]⟩,
  ⟨69,6,[ew230,ew195,ew231,ew522,ew233],lh 5 [795,11,196,28,7,9,27,700,56,16,19,15,20,21,796,797,57,706,33,6,237,194,193] [0x6410047003252,0x31ac0050103063,0x481005a10310c,0x4a102489024a5,0x40d004015024c9,0x388e238d0302409,0x38ca338ce300902,0x38c84388a238882,0x7d1547d276708c2,0x8ac848b4ad70a73,0x72ccb8b48d8acab,0x72d4b7a0c87a14a,0x7914a790c671545,0x714c6]⟩,
  ⟨69,6,[ew230,ew195,ew231,ew522,ew232,ew233],lh 5 [56,196,11,27,28,16,700,15,795,706,19,20,237,6,683,57,21,9,693,694,796,797,194,193] [0x5b1620884c62c21,0x1404b02d7058802,0x12045714a8289c2,0x12045414a828902,0x2a0af1bde8b1465,0x218810042609000,0x2188130426090c4,0x2188130426090c4,0x235ac1b18db9064,0x240749ce938120,0x240749ce938120,0x3b4e01800d69c67,0x98c72528c68b911,0xa8c7452a431cd4a,0x2831d54a]⟩,
  ⟨69,6,[ew523,ew230,ew195,ew231,ew232,ew233],lh 5 [21,19,234,245,9,11,28,20,7,707,16,27,683,33,6,799,57,55,693,694,798,196,785,15,14,737,194,244,192] [0x63d8f841e9a30e7,0x4a6ec18ec9ab042,0x9a67208729c3084,0x298c710a4994c21,0x380e5194e631445,0x51085894a001c67,0x83f4a0a8a42aa2a,0x68f660014f54030,0x1238d8b4c31b40d,0x13846099a840a22,0x1a100200ce70821,0x1b9c05800800c84,0x42d640900e00d6b,0x8b5a021]⟩,
  ⟨69,6,[ew19,ew230,ew195,ew231,ew232,ew524,ew233],lh 5 [11,20,28,27,245,16,234,19,14,15,707,196,702,683,737,194,331,700,706,9,726,727] [0x6a18a4a56208020,0x84010002719c6e,0x1bca02940129420,0x118c2118c281045,0x910914108a118c2,0x1d06719e6839083,0x75]⟩,
  ⟨69,6,[ew230,ew195,ew525,ew231,ew232,ew233],lh 5 [245,21,234,16,6,28,14,11,27,20,33,19,800,700,706,707,683,57,693,694,802,194,244,224,801,737,15,9] [0x194a711ce528c42,0x3b0e380c6c19e07,0x384290252109c07,0x4b12330c6c1a4c9,0x1b0714462ca8d03,0x2b8a26884e115a5,0x2800a0a940b1425,0x5654230858ba8ca,0x290824084411508,0x6800e085c0d3421,0x990925adefdc0c6,0x18017864424d6b,0x100142026301e0,0xa10865982420100,0xc42516b]⟩,
  ⟨69,6,[ew19,ew230,ew195,ew525,ew231,ew232,ew233],lh 5 [20,19,16,28,245,234,6,11,27,707,14,9,33,683,702,21,194,331,700,706] [0x525e47358301c07,0x1080039c01304c9,0xc0401080200040,0x194a38906329462,0x3056b24c92314a1,0x428280a144224c1,0x101]⟩,
  ⟨69,6,[ew19,ew230,ew195,ew231,ew232,ew517,ew233],lh 5 [20,27,19,57,234,16,245,7,706,702,707,6,297,196,21,801,700,192,28,803,14] [0x79d27719a400c03,0xc60104414250a,0x14a0014a018003,0x910e48c0c428865,0x418ca630f359082,0x882208a87584c1,0x22]⟩,
  ⟨69,6,[ew19,ew47,ew230,ew195,ew231,ew232,ew233],lh 5 [16,20,27,19,7,28,11,245,706,707,702,804,33,21,737,234,14,194,331,691,193,805,297] [0x69d850982642909,0x4011886271144,0x10c438112741de5,0x800100420018c0,0xa16642c8e500e20,0x10c62188962556b,0x44]⟩,
  ⟨69,6,[ew19,ew230,ew195,ew108,ew232,ew233],lh 5 [21,20,19,234,245,6,55,125,9,11,56,700,28,702,706,707,806,237,57,726,196,789,194,803,805,14] [0x504204800102929,0x6ad60201cea0220,0x6bda04000b03484,0x509402800f03508,0x4c52118402128aa,0x3c2a1210310a463,0x3a0e13043009c87,0x942c711c2809cc6,0x7908358cf03c852,0x1dc6c318641bd6b,0x1946c1319860cc6,0x73b243198528c43,0x994a4108852cc42,0x41506118c52a042]⟩,
  ⟨69,6,[ew105,ew19,ew230,ew195,ew232,ew233],lh 5 [16,28,21,234,19,245,20,14,297,11,6,808,56,27,706,57,700,726,702,15,807,9,707,196,194] [0x5800531a8e99445,0x28c70084a002cc6,0xb3aa539e0319421,0x8b5a5214ad2c484,0x618c20084613000,0x91ce2409ceb8822,0x611826884714908,0x4842619844231ac,0x2c09424c132469,0x7af002012b48100,0x1a0613840b03c8f,0x1a8612042808ce7,0x4294721c2a50c83,0xea52084]⟩,
  ⟨69,6,[ew526,ew230,ew195,ew231,ew232,ew233],lh 5 [20,28,355,9,27,19,245,14,700,33,234,809,6,55,683,57,196,21,707,706,737,693,694,810,194,224] [0x7000b1096003842,0x425280850982030,0x99cf218d088b8d1,0xb14b5212873cc63,0x10420482a52d884,0x2c023080108929,0x10c606804b100c0,0x7af0029403189a2,0x499214040b03caf,0x52321184260a509,0x53141294280a86a,0x31cf218c2c628aa,0x330d72128739866,0x6908729eec61884,0xe4234ad]⟩,
  ⟨69,6,[ew47,ew230,ew195,ew231,ew232,ew233],lh 5 [21,245,27,7,16,6,20,28,33,811,57,15,11,19,683,702,700,234,707,706,693,694,812,55,732,194,691,737] [0x71089529242394a,0x9ad720860f8b8f1,0xc26ee18e4b5cc21,0xa0855296a2150a5,0x21cec4318739104,0x60006598c00316c,0x324c41908921866,0x324ca12949c9846,0x384280010141c00,0x3b4f0869e31a128,0x6c072950d6a0a8,0x80018c2f08461,0xb35a029422104a5,0x161086d18c42]⟩
]
def nodesBlock29 : Array Node := #[
  ⟨69,6,[ew230,ew195,ew108,ew231,ew517,ew233],lh 5 [196,57,9,19,7,56,21,192,125,6,20,813,55,702,27,16,706,224,700,739,104,194,782,803,28,737,15,14,814] [0x7ade10002b0bc00,0xac282210ba0481,0x98c829506404a1,0x50848631024298a,0x52d414842baa92a,0x390e09000489e51,0x3dce02801601ca7,0x3a4e0181b9c0040,0x6b7442940949c63,0x2253318dbcd9044,0x6c20610a6949064,0x28c66718d033442,0x639c2188c3315c5,0x4e7306c]⟩,
  ⟨69,6,[ew230,ew195,ew527,ew231,ew232,ew233],lh 5 [28,196,9,71,7,11,21,6,19,27,56,16,815,55,700,702,20,683,57,237,707,706,693,694,194,785,783,193,15] [0x80005094a004030,0x2b0a388c6c19625,0x298a350c6619545,0x1886b6ad6210da3,0x5b1724ca4cc2d2b,0x500170439081c0,0x50015043a08140,0x108168424081a0,0x1cf344e67d8100,0x71095109efe44c6,0xb9cf6422a423842,0x7908610ac73dd08,0x51ce6498c433c42,0x22522408c73292a,0x4949108]⟩,
  ⟨69,6,[ew230,ew195,ew528,ew232,ew233],lh 5 [816,11,16,21,196,27,9,297,700,245,56,14,234,19,817,6,818,244,20,706,57,194] [0x4810040104892,0x4610094a04812,0x5610086200541,0x4c10096b008c2,0x50b405015008a2,0x411244314a00802,0x4456b4312941144,0x444e70316c430ec,0x845ad845f1711a4,0x9a4e798cc3711ef,0x70ca398ce39a4c6,0x70de3824a5825ef,0x81dad81ca5719a6,0x718a5]⟩,
  ⟨69,6,[ew230,ew195,ew529,ew232,ew233],lh 5 [819,21,28,11,27,245,196,9,700,14,16,20,820,6,821,57,702,237,55,19,194,193] [0xcc300c4f02cc6,0x2c2b00ca302c42,0xd2300c2302cab,0xce30292a028e7,0x3c8f03c140288a,0x418a6408220280a,0x40929408a541821,0x409020192941906,0x74491745b560882,0x81525804e1609ad,0x6048180521814e7,0x605a171484715ad,0x74a727488461e67,0x61c84]⟩,
  ⟨69,6,[ew230,ew195,ew529,ew231,ew232,ew233],lh 5 [196,237,55,20,19,57,700,14,27,819,16,702,683,9,6,21,706,693,694,820,821,194] [0x18465000a108c0a,0x2a4a360c6919585,0x2a4a348c6919525,0x1b46a1294d68c43,0x52545214a9aa88a,0x982030006004c1,0x982030006004c1,0x98201000600442,0x38012102e08080,0x59cf0108c67b12f,0x91091422073ac42,0x59ceb10a2424908,0xa1093421673ac42,0x1204721e6425108,0xe838882]⟩,
  ⟨69,6,[ew47,ew230,ew195,ew231,ew530,ew232,ew233],lh 5 [27,20,16,33,11,28,15,7,19,737,14,6,196,706,683,707,194,691,21,700,702,753,754] [0x53dc66a58511044,0x84c2210405816a,0x40211082408482,0x89c6518ca518cc1,0x418e63a64628c65,0x2016054f43cd00,0x8]⟩,
  ⟨69,6,[ew230,ew531,ew195,ew231,ew232,ew233],lh 5 [9,28,7,15,16,11,27,20,33,6,234,822,19,700,707,683,57,702,21,706,693,694,823,194,786,737] [0x22c8779ceb391e4,0x38425414a129d08,0x2aca719ceb39465,0x280041108001445,0x22c903420bb90c4,0x6a1110862843421,0x9884d001ce93c72,0xab194319a214c00,0x4610118e8c654c6,0x508410002e0a063,0x52541304220a80a,0x1886e000294a8ca,0xb252330f2210c03,0x12440600694d8c6,0x948982]⟩,
  ⟨69,6,[ew47,ew230,ew531,ew195,ew231,ew232,ew233],lh 5 [20,27,57,7,6,28,15,33,16,234,737,19,683,706,707,9,21,700,702,691] [0x1a8ce4a5ac40902,0x10802000412048f,0x208001a002000c0,0x8e438c0c729ca0,0x39663294e731024,0xac81204661a8a1,0x2b]⟩,
  ⟨69,6,[ew47,ew230,ew195,ew108,ew231,ew233],lh 5 [9,28,7,33,21,6,27,57,11,56,19,55,20,700,125,706,702,737,824,16,753,196,104,194,244,787,805,15] [0x5cd60380139ace7,0x7b5a010210a8020,0x7c5e02000d03c42,0x599602801103c84,0x3842c18c0632cab,0x74acc1318161c63,0x711c84a1926384e,0x3cae83210443929,0x888416851241cc7,0x1e70148422145ad,0x194613043a08d23,0x843624882528d43,0xa14a2528452d14a,0x228893192a510c4]⟩,
  ⟨69,6,[ew112,ew47,ew230,ew195,ew231,ew233],lh 5 [7,9,20,28,33,11,15,6,27,297,826,55,16,19,702,57,700,753,706,14,825,21,737,196,194] [0x508402968e98020,0x101018c02028a5,0xb3aa03020420060,0x8b5a03800d044e7,0x5b1811042c0ac42,0x918c1485ceb8481,0x5a161684260c929,0x28c6c2302842dab,0x128454958319485,0x7ab02408aa28922,0x2248330c4a13d0f,0x21c8340c69190c6,0x49ce64186739104,0xc73a508]⟩,
  ⟨69,6,[ew230,ew195,ew231,ew532,ew232,ew233],lh 5 [57,196,21,55,19,245,7,27,16,125,6,827,56,9,707,700,683,11,28,737,828,702,706,693,694,194,781] [0x42d000800b02021,0x8096252248180,0x42d008000b02208,0x340918d2d48060,0x8ae202000b04499,0x714a1604250b98c,0x983318dce90612,0xa2b412066630463,0x2bca2a882a55084,0x298c21884f116a5,0x290823884611465,0x798d618c44114e7,0xc295739ec633c63,0x31ced212ea560e7,0x1a769884]⟩,
  ⟨69,6,[ew230,ew195,ew108,ew231,ew532,ew232,ew233],lh 5 [196,125,20,21,9,6,27,57,707,19,706,702,45,28,737,245,683,700,7,829] [0x1842710422100e0,0x98e11042210422,0x8d020001a008,0x3489183c603140e,0x28c6498d6a194c5,0x290a92a5445918c,0x89]⟩,
  ⟨69,6,[ew533,ew230,ew195,ew108,ew231,ew232,ew233],lh 5 [11,196,6,125,9,21,20,19,706,702,707,45,28,683,785,762,761,194,700,737,15,14,830] [0x495057358101806,0x30006809e241124,0xc6000c6000c60,0x228212a83218a23,0x3d494284e20cc21,0x1116b114a4b08e2,0x87]⟩,
  ⟨69,6,[ew230,ew195,ew108,ew518,ew233],lh 5 [831,196,11,125,19,237,14,706,56,28,6,7,833,834,21,20,57,9,707,104,194,829,830,832,211,835] [0x822008a503c21,0xc13008c203caf,0x9020080200cc3,0xa2200d0800e23,0x40900401400c83,0xa8561914c600c03,0x3a5099256bb04c1,0x396e938501384e1,0x694856954562489,0x39f38019c66254a,0x6ac8b6ad4a61884,0x6a084638ee6194a,0x6388e6a0e8]⟩,
  ⟨69,6,[ew534,ew230,ew195,ew231,ew232,ew233],lh 5 [19,57,7,15,16,245,28,836,14,706,6,27,702,700,683,20,237,693,694,196,832] [0x71087084e423821,0x48c6d295299b8c6,0x6210d109a31a4a5,0x90011529a843042,0x9824392200494a,0x79de129486204e1,0x21c81108270bca5,0x9c240002709042,0x494a61988720400,0x60846420c52a463,0x82946000c213108,0x1886c4d0ca54010,0x2800358d2210d23,0x12d68000601956b,0x10b58800]⟩,
  ⟨69,6,[ew230,ew195,ew535,ew231,ew232,ew233],lh 5 [33,15,16,20,7,9,6,27,245,837,57,702,707,700,683,19,838,706,693,694,194,237] [0x1a46a0014950c00,0x1244370c69189c2,0x1244308c6918822,0x194622084510c83,0x1244a3a949a08e2,0x200c0856ba81c0,0x590802818840020,0x181039c0422ca5,0x6a10c08606300e0,0x8908d2958843421,0x998d239da4244a5,0x902b2964634ce7,0x418c138564204a1,0x218c5794260a0e8,0xa6311ef]⟩
]
def nodesBlock30 : Array Node := #[
  ⟨69,6,[ew230,ew195,ew108,ew231,ew232,ew233],lh 5 [57,196,28,125,56,9,19,21,706,6,27,839,55,683,16,237,33,700,707,693,694,785,702,737,15,768,7] [0x708408000213a0e,0x2c0368c6b181a0,0x1ce32106718080,0x14a36306518180,0x1ac603180b00cc3,0x148418843508a22,0x148412042808884,0x15c4128436088a5,0xa42f33de9484c1,0x4234d2972bc3484,0x9a53431a894ccc6,0x3a8e4411652a108,0x298a731c8a510c4,0x5529866314a]⟩,
  ⟨69,6,[ew230,ew195,ew536,ew231,ew232,ew233],lh 5 [234,20,21,19,245,16,14,7,840,706,6,27,57,700,683,737,841,693,694,194,28,707] [0x2a0ac0018861400,0xa025714a8285c1,0x288a12042209485,0xa025318a8284c1,0xa02c1b18898461,0x4908010129a01c0,0x1c0f3180422442,0x281018de7380c6,0x4908d10a0a50060,0x69cef319a422442,0x9295118ea73b4c6,0x21ce248a2a54863,0x20c625884739124,0x3ad6618c431116b,0xcb59c63]⟩,
  ⟨69,5,[ew230,ew195,ew108,ew516,ew517,ew233],lh 5 [57,21,19,7,196,20,16,9,224,45,842,192,33,781,15,14,843,706,844] [0x802600d4330006,0x191082880528005,0x78dc1209a461164,0x4a44109e2180862,0x38a47]⟩,
  ⟨69,5,[ew230,ew195,ew527,ew516,ew232,ew233],lh 5 [11,196,244,16,6,9,7,19,845,361,223,21,45,20,198,194,28,15] [0x18003421c068001,0x1054a4a5e300c60,0x8ac221044108a02,0x314c521c87314c5,0x21c876308b]⟩,
  ⟨69,5,[ew230,ew195,ew231,ew520,ew517,ew233],lh 4 [20,21,245,11,196,192,6,27,19,224,204,7,194,28,9,14] [0x3300ba030030334,0x54d55499212107c0,0xfe17211221122145,0x68686867]⟩,
  ⟨69,5,[ew230,ew195,ew231,ew532,ew232,ew233],lh 4 [20,21,7,245,11,19,6,9,196,28,194,14] [0x270044040040448,0x65272799318105a0,0x2713311331133165,0x622565652b]⟩,
  ⟨69,5,[ew230,ew531,ew195,ew516,ew232,ew233],lh 4 [16,9,19,20,33,27,223,245,15,11,194,21,7,28,211] [0x3003033004900730,0x75c171b7464605a0,0xe88162424161d625,0x12528528]⟩,
  ⟨69,5,[ew47,ew230,ew195,ew108,ew516,ew233],lh 5 [9,11,6,16,244,297,19,700,7,21,638,45,20,207,196,706,844,33,539,842,194,28,15] [0x78008381c06800c,0x986410c40280009,0x29062a0c6108c28,0x11ac51114aa90a7,0x16b32446]⟩,
  ⟨69,5,[ew537,ew230,ew195,ew108,ew232,ew233],lh 4 [6,16,57,196,15,125,244,19,21,28,55,245,706,211] [0x788acab499632121,0x2525521551132180,0xd406036336643450,0x7074704]⟩,
  ⟨69,5,[ew538,ew195,ew231,ew232,ew233],lh 5 [9,20,245,21,33,28,7,11,16,19,234,27,57,55,6,194,846,847,244] [0x9427210e538481,0x38ce11042309c47,0x80286a100005a1,0x4450c4b1907a168,0x288441908291465,0x2188a0294631004,0x2b8aa4a94e51525,0x198620004610c00,0x1a4625884910d63,0x2c06498cb30120]⟩,
  ⟨69,5,[ew230,ew195,ew525,ew231,ew517,ew233],lh 4 [224,57,245,21,19,27,16,20,196,9,194,192,33,848] [0x7117127216616010,0xd0c0200388b0611a,0x3223545499232304,0x54543545]⟩,
  ⟨69,5,[ew19,ew230,ew195,ew108,ew517,ew233],lh 4 [6,16,9,192,19,21,7,20,700,57,196,706,842,28,14] [0x4052b55685a37151,0x90212716c1139340,0x4e20304d2386310,0x240204]⟩,
  ⟨69,5,[ew19,ew47,ew230,ew195,ew108,ew233],lh 5 [9,21,20,11,19,28,297,16,7,700,45,14,850,851,706,201,691,244,849,207,192,844,842,194,193,843] [0x4a23079c27081c1,0xa026300d4a90428,0x10c62012a05ad20,0x6b4c5112e2632c2,0xc98c429305]⟩,
  ⟨69,5,[ew19,ew539,ew230,ew195,ew232,ew233],lh 4 [19,297,234,20,15,245,16,14,28,57,6,21,223,9,194] [0xa047141c43934b4,0x50ad15125583935,0x122760e636613282,0x70108220]⟩,
  ⟨69,5,[ew540,ew230,ew195,ew108,ew231,ew233],lh 5 [196,192,11,125,20,21,6,14,9,57,28,19,45,7,706,844,194,211] [0x715a75282049124,0x18882111067a105,0x1c6680c4318843,0x894010802000420,0x6316532cc7]⟩,
  ⟨69,5,[ew47,ew541,ew230,ew195,ew231,ew233],lh 4 [28,33,14,297,6,16,11,15,20,27,852,9,224,19,21,194] [0x2d927323c25652b2,0x94aae37310105656,0x11084f868830101,0x73474140]⟩
]
def nodesBlock31 : Array Node := #[
  ⟨69,5,[ew230,ew195,ew108,ew532,ew518,ew233],lh 5 [125,20,196,19,11,21,7,6,28,14,194,27,224,9,853,781,297,852,706,854,45] [0x80010800108001,0x4184c22d4420004,0x325221bc4e109a8,0x19c732c8b119870,0x5a1ca7]⟩,
  ⟨69,5,[ew533,ew230,ew195,ew108,ew518,ew233],lh 5 [125,21,6,11,14,196,19,28,20,45,7,706,855,834,833,194,707,856,781,211] [0x60561510e718060,0x1900440008709a2,0xc0a4009e208023,0x308d3094d2344a5,0x948822]⟩,
  ⟨69,5,[ew534,ew230,ew195,ew108,ew233],lh 5 [20,14,6,21,28,57,7,19,857,56,125,237,706,196,855,854,853,856] [0x4812328c60024a5,0x7042330d8c68c83,0x49ce310c610bcc6,0x29080400671a442,0x521400800401505,0x2a0a01000802821,0x818c40840801442,0x588443908624421,0x308413848212ceb,0x22118e6]⟩,
  ⟨69,5,[ew542,ew230,ew195,ew108,ew233],lh 5 [21,861,6,19,56,20,125,196,57,237,297,28,33,11,859,321,244,858,854,14,831,860,194] [0x214804000529108,0x30124a62c81124,0x20c801028e98140,0x6ada56300319042,0x306a5514ab5b58d,0x43ac6198a109946,0x3a94b084ce32068,0x4884719d6a59c27,0x78841184e23a469,0x220bc6f]⟩,
  ⟨69,4,[ew538,ew195,ew231,ew232,ew543],lh 4 [33,194,9,27,28,6,245,19,21,55,16,192,56] [0x4a1292116814110,0x53c262500302b240,0x373753]⟩,
  ⟨69,4,[ew544,ew538,ew195,ew231,ew232],lh 4 [19,16,9,27,28,33,57,6,20,7,11,55,192] [0xa103303003077066,0xc44554212b188115,0x929242]⟩,
  ⟨69,4,[ew534,ew230,ew108,ew532,ew233],lh 4 [7,11,28,20,196,27,45,194,804,224,9,125,14,843,193] [0x6654a24290403131,0x5c01577211310b0,0x88e2d0]⟩,
  ⟨69,4,[ew545,ew230,ew195,ew108,ew233],lh 5 [11,21,19,28,211,45,297,804,201,244,14,196,232,860,194,193,862] [0x294415052140020,0x9c0019a06000b,0x20a0439de3190c3]⟩,
  ⟨69,4,[ew230,ew195,ew108,ew546,ew233],lh 4 [6,21,125,14,19,28,11,196,45,20,194,7] [0x20a0121663235229,0x4b1040451715373,0x880104]⟩,
  ⟨69,4,[ew533,ew534,ew230,ew108,ew233],lh 4 [196,6,21,851,125,28,7,19,14,244,232,193,45,194,11] [0x22051b166a45490,0xe1d138380c702002,0x3713]⟩,
  ⟨69,4,[ew230,ew195,ew547,ew108,ew233],lh 4 [11,297,211,33,56,21,6,638,20,860,194,237] [0x6a0029050048003,0x45121463771213b3,0x211254]⟩,
  ⟨70,7,[ew198,ew234,ew235,ew236,ew237],lh 5 [60,62,20,344,21,865,9,7,10,67,245,866,1,868,31,869,57,16,871,53,874,863,864,867,870,14,872,873,875,876] [0x58420021500441,0x4610150800601,0x4810146300508,0x58c0148501585,0x14c501525004c1,0xbc0635890800529,0x5b94a688635b90e,0xc38845894278882,0x5c731944c6588e7,0x7cd5368c84d08c2,0x68d29d8d436cc84,0xe0ce76d129950f4,0x928c67a8e7e90c4,0x7b0ec]⟩,
  ⟨70,6,[ew125,ew234,ew235,ew236,ew237],lh 5 [9,866,877,21,62,5,245,7,20,865,878,16,60,879,10,147,880,57,881,333,882] [0x125ce6319161111,0x124a5111c4110a4,0x12469124c911064,0x124e911004110c6,0xa0a5110e712409,0xa14a084a50bd53,0xa0c80a0680acc6,0xac0b0a0e80ac63,0x6a8630a0000aceb,0x7a8ca69463814c6,0x69400914e76a800,0x818e7a0c007a8ea,0x80ce391800]⟩,
  ⟨70,6,[ew234,ew235,ew548,ew236,ew237,ew198],lh 5 [865,245,7,62,344,15,14,866,57,132,31,21,67,883,9,868,60,1,878,886,869,887,871,333,20,147,10,884,885] [0x4410f2110741cf7,0x495298c50543cf8,0x5194a631264a231,0x5014a6a9a002589,0x214a73e890234f9,0x218c4085e52ec21,0x90004109e637042,0x994b218c8021064,0xa98d3086852d021,0x6801510ac635842,0x5b18d18e0004063,0x58d6b12c2e08442,0x70dcb02c2318400,0xe0384318800]⟩,
  ⟨70,6,[ew127,ew234,ew235,ew236,ew237,ew198],lh 5 [9,7,865,21,53,62,16,10,57,866,878,874,60,869,886,889,344,1,20,868,871,31,888,245,887,201,890] [0xb109339d2d932b2,0x4a6ec18e64238e7,0xc0434002810b800,0x7884c2958213ca5,0x3294839d0a418e7,0x404294e5a319926,0x30848000c109800,0x50d4649902121e8,0x2008a72883211a4,0x58964091605ac21,0x1800b2ae02840a5,0x1946308f4003421,0x140310e258c442,0x1002528442]⟩,
  ⟨70,6,[ew128,ew234,ew235,ew236,ew237,ew198],lh 5 [21,245,865,57,9,62,20,874,53,866,878,344,60,871,892,67,16,868,10,887,886,869,895,891,7,207,893,894] [0xb9cf15ad2d830d0,0xa8434002273ce52,0x4a70c212810d400,0x7084c29582138a5,0x3294338c6a198e7,0x18066098c030c23,0x308c94e5a420d23,0x501464986218dc3,0x4110a085004203a,0x409089a0e439da7,0x1008295625acbb,0x1400b0024206c1,0x214801002528442,0x4111e57bc42]⟩
]
def nodesBlock32 : Array Node := #[
  ⟨70,6,[ew131,ew234,ew235,ew236,ew237,ew198],lh 5 [57,245,20,16,62,14,9,7,865,878,874,868,898,10,897,886,60,869,344,900,67,866,871,896,53,21,887,333,147,40,899] [0xa884f18ee215400,0x5af3008571c41ad,0xd14b639ec52bce7,0x721102120843884,0x1a52068009d8dad,0x3c020885110020,0x118c338c66308e2,0x1f0604000e00d03,0x498cb5f6210a569,0x521493a546528e7,0x798ca22a4894884,0x7109129426084a5,0x2b18e6302420581,0x59ce8ca527e]⟩,
  ⟨70,6,[ew132,ew234,ew235,ew236,ew237,ew198],lh 5 [62,57,7,15,16,865,21,245,53,878,20,868,902,60,871,887,10,344,866,886,869,901,874,67,147,903] [0x9108f52aa42494a,0xa0c7339d6eb3529,0x5aeed10a631d0e7,0x614ad001a52b000,0x225218042949210,0x982a18d4630461,0xbc241088e20441,0x260810042c09000,0x49ce81a1073a463,0x4150b5e5c212168,0x33cc8022258c400,0x300c61186e18c42,0x60006298e001ca5,0xc29440108a2]⟩,
  ⟨70,6,[ew234,ew235,ew139,ew236,ew237,ew198],lh 5 [10,5,20,21,62,9,865,138,869,16,57,53,905,60,898,344,886,906,871,1,900,67,866,868,245,7,904,863,882,907,887,899] [0x13c4a5ad4f7896b,0x14047b1cfa38ac2,0x48c6761ce33a589,0x114a96252548982,0x1704a32951d88c2,0x4001b843d082e0,0x40011842808060,0x780128432080a0,0x108130424200c0,0x4232d2e512c3478,0x898cd211a634484,0x1908340e452a108,0x2b9c370e649ccc6,0x5a52aead69f]⟩,
  ⟨70,5,[ew125,ew234,ew235,ew139,ew236,ew237],lh 4 [20,5,62,9,10,21,865,878,16,57,908,866,245,7,880] [0x6225622662171790,0x3050080ba0017023,0xc543144514411438,0x53ed3]⟩,
  ⟨70,5,[ew234,ew235,ew549,ew236,ew237,ew198],lh 4 [53,21,9,16,57,7,865,62,245,20,201,31,909,10,877,60] [0x4334aa133499c0b0,0x7052508001d03443,0x526f6e5252818176,0x2762176112]⟩,
  ⟨70,5,[ew234,ew235,ew550,ew236,ew237,ew198],lh 4 [57,20,9,865,7,62,1,245,207,344,335,874,16,877,60] [0x88200110100c1001,0x5b4baa7676991001,0x423e3d4242767653,0x2532353542]⟩,
  ⟨70,5,[ew234,ew551,ew235,ew236,ew237,ew198],lh 4 [20,62,245,7,14,10,21,865,344,67,16,910] [0xb0049060020580a0,0x7143436262858507,0x3917153434262571,0x4131612132]⟩,
  ⟨70,5,[ew234,ew552,ew235,ew236,ew237,ew198],lh 4 [16,21,245,865,878,7,67,900,10,20,344,911,899] [0xb06005121008a090,0x3765651212484807,0x2143734654212437,0x353c323112]⟩,
  ⟨70,5,[ew234,ew235,ew236,ew553,ew237,ew198],lh 5 [21,138,344,53,9,62,865,912,913,905,14,20,908,335,15,914,418] [0x42161004e708c41,0x10c401818109481,0x246210c4469062,0x2240580004791c0,0xc5314c53154a]⟩,
  ⟨70,5,[ew234,ew235,ew236,ew554,ew237,ew198],lh 4 [5,57,62,20,9,7,245,21,16,863,10,865,877,60] [0x1841311313313010,0xb5004a060073119,0x5472625654766720,0x42522d2c54]⟩,
  ⟨70,4,[ew125,ew235,ew236,ew553,ew237],lh 4 [62,20,9,21,878,5,865,10,16,915] [0x260016003605004,0x1318725771414353,0x28213292]⟩,
  ⟨73,10,[ew246,ew247,ew248,ew249,ew250,ew251],lh 6 [11,12,27,59,9,7,21,916,43,19,918,56,920,921,20,25,923,6,16,53,926,245,24,17,23,15,874,46,919,10,58,927,57,0,933,55,917,922,2,924,925,333,928,14,929,194,930,931,932,51,934,935,45,936,195] [0x9084921db01b,0x7083c82813811c8,0x7481c13cf701741,0x3482c81c1581308,0x1459412c11c8596,0x1d79974171041c1,0x821c14519c1101,0x5010821de618a1e,0xc07c03e97ce0c3,0x28064030e3cf280,0x18628e65934e18e,0x412104280145a80,0x249b00100292ad2,0x2a0249ba062d280,0x553303186500861,0xbc3543313186353,0x10441a15a303103,0x313082c0314331a,0x451883082c43443,0x355145c86106893,0x8234b14b4158e3,0xccb08b34b44b506,0x82504249346274,0x4040b6d45249405]⟩,
  ⟨73,9,[ew246,ew247,ew555,ew248,ew249,ew250,ew251],lh 6 [916,918,9,43,16,10,17,20,21,7,19,56,27,245,6,23,5,940,943,937,25,948,59,55,24,919,60,950,2,939,15,14,945,874,53,11,920,921,923,926,955,46,938,700,941,942,944,946,947,949,951,952,953,954,665,956] [0x104003003000000,0x10294c3643001,0x5144d31454c3503,0x6606003145000,0x206003618003203,0x6086003243006,0x3c6003082006706,0x3cf02a28a006,0x234c7663006286,0x75d514747147000,0x784047507041145,0x4779e047607044,0x7040477c7044604,0x477070447df044,0x28a05a3cf044284,0x4644100443c4041,0x145ad94104d9145,0x4a5208b6c34d464,0x24982e2084a534d,0x566249566082c2f,0x28a6e738e831082,0x6e728a6b338e832,0x2cb4903504452cb,0x456082d0534d450,0x256461082561261,0xd9639646230cd56,0x88a223a2a1630c,0x54d5d748d249dc8,0x38b6c830c48b24b,0x48838e68b30b48b,0x3d75573176c23c2,0x54230c697]⟩,
  ⟨73,9,[ew196,ew246,ew247,ew248,ew249,ew250,ew251],lh 6 [916,921,20,12,11,17,23,19,9,944,15,958,70,59,959,27,10,21,71,56,2,7,960,874,6,957,25,919,55,961,14,58,16,57,53,918,678,920,24,923,926,962,967,43,952,37,963,194,60,893,964,681,965,966,682] [0x8200006b65b0c3,0x2490822644922e3,0x30c3a569a2e3492,0x3a530c65b69a25b,0x71c00002665b4e6,0x5a771c5a7514249,0x1867683cf264514,0x7681862491c726c,0x485005082003492,0x645305003082005,0x41000330c643403,0x1451005005005,0x20500351400002d,0x3208005505005,0x19f01f1c7003183,0xa424100031c301f,0x6822c4404a4430c,0x424422c4284382,0x7840444442c228a,0x2e07a05a02082c4,0x1af2c41c7b84204,0x7441862e11e1c21,0x4e20620713904d3,0x38d78d04dc903a2,0x54d397797597557,0xd4d60d3971b4ccd,0x211a97618a8d18d,0x4a20a04a555051,0x61804a3ca051551,0x4a60a0533d3053,0x1c75953cf7481c8,0x5883cfd95]⟩,
  ⟨73,9,[ew197,ew246,ew247,ew248,ew249,ew250,ew251],lh 6 [916,11,923,21,12,43,20,27,969,949,10,9,19,970,971,55,245,53,355,362,24,14,59,0,16,6,968,23,919,56,972,58,25,57,1,874,17,918,679,920,921,2,926,974,15,978,944,952,973,62,333,975,194,60,893,41,335,976,977,47] [0x410000a469c124,0x249041266492225,0x4d3367596225492,0x3674d369c28a25c,0x75d3a851426e75d,0x69c2e92665143a8,0x5d77aa30c000029,0x7aa5d724930c26f,0x485005186004492,0x6854c5004186005,0x2850044d368428a,0x50c5004514005,0x40040c3005505,0x300022cb004,0x5df01f3310045c4,0xac628600430c01f,0x820201281ac1832,0x3860c3201b01346,0x3cfcc10c1206b06,0x2183d80982cb201,0x6f42183180812c1,0x7986db221321d61,0x89139143634a8a2,0x3513d1dca410351,0xe513633e30a30b8,0xe966563511c7096,0x2c3b51659b561c7,0x902cb390550083,0x6597831c3383555,0x383643ed01c7390,0x6cf08f1c70956d5,0x951d508f]⟩,
  ⟨73,9,[ew246,ew247,ew248,ew249,ew250,ew251,ew556],lh 6 [916,24,11,20,25,2,19,21,58,46,926,59,982,27,984,57,951,980,983,16,985,874,9,15,53,56,979,55,10,7,938,919,14,986,245,981,952,918,51,933,921,923,62,12,893,335,965,987,988,944,989,949,23] [0x8201e0c3008088,0x6891040080c3000,0x2c90081046882c8,0x91c9008048009,0x1490081c8009041,0x111510116db009,0x1100002a0096c9,0x6917d100a186011,0x1048c370300a02b,0x48310430271c8c2,0x5d73830413025c2,0x303803782041303,0x145313813513145,0x28f90f313193783,0x94229329330f18f,0x30f94f40f40f302,0x8ac49c5d7402782,0x99c8a24985d8398,0x81551576d498818,0x49519599875d495,0x85584b18b28b92e,0x68b7cb4849c4855,0x5874047c484b9cb,0x5016db381141bc7,0x19928734d399159,0x387187299359399,0xc47387a07401c01,0x296186381a01407,0x34d29d18651d34d,0x516a56405c85516,0x7cd505a45416cd6,0x3468d]⟩
]
def nodesBlock33 : Array Node := #[
  ⟨73,9,[ew204,ew246,ew247,ew248,ew249,ew250,ew251],lh 6 [918,11,921,19,12,9,24,990,53,43,39,21,991,25,14,23,59,993,16,17,7,995,10,6,27,2,992,996,874,994,58,57,1,916,680,919,920,927,923,926,1000,944,20,15,952,975,938,333,201,194,997,998,681,965,999,682] [0x10432228a1e1104,0x6a30411e128a329,0x20846434d0000aa,0x46420876534d325,0x14500002b6a32cb,0x56614556638e30c,0xc36e73cf32238e,0x6e70c330c3cf32c,0x490094891ca04a,0x68934900a4921c9,0x2091ca34a68a208,0x892c91c4184449,0x6440842c41c9186,0x1d36535531451c4,0xc31d33d3b44144,0x6d30d31de3deb9e,0x58174136f752212,0x100101234d001,0x381000030002186,0x1238e012659001,0x3f10010c1001641,0x13cf01f0df01f,0x2c80880b24562d6,0x450390090cd6448,0x51045c39c55c51c,0xd905d04560f5d10,0x14ba165d7a100d0,0x8614608651408b,0x5d708660608b50b,0x865c60a06200a0,0xc35546186c50c5,0x545618dd4]⟩,
  ⟨73,9,[ew205,ew246,ew247,ew248,ew249,ew250,ew251],lh 6 [918,43,11,27,1002,923,15,2,1001,19,10,9,20,1004,1006,1008,245,53,874,25,59,24,6,21,23,12,1005,1,1009,1007,58,57,67,916,1003,16,919,920,927,921,14,926,1012,949,991,952,963,62,938,207,893,41,386,1010,1011,47] [0x659362104221659,0x6a40a322110436b,0x4923a5514000163,0x3a549276628a366,0x6db3e718636c6db,0x6a42e83621863e7,0xc3729249000028,0x7290c334d24936d,0x8100130c204084,0x6814c100430c201,0x2812044d368428a,0x3c1181204544381,0x1c1b84186201555,0x2041c71442cb201,0x26f2016011412c1,0x70124921e61ec1e,0x2827424d374c28c,0x218200c4d3002,0x54200c18600c555,0x51c7002002002,0x618002242000031,0x260201f25f01f,0x1913d143238a186,0x3912d1cca410391,0xd513922d2152174,0xd945943910c3154,0x2d7a91596a940c3,0x1502cb3d01d0157,0x5967170c33d71c7,0x3d7597dd00c33d0,0x2601600c3147247,0x1470c7160]⟩,
  ⟨73,9,[ew246,ew247,ew248,ew249,ew250,ew251,ew557],lh 6 [918,15,23,57,12,43,1013,21,9,14,874,926,10,1016,58,0,1015,17,1017,1018,382,59,25,4,53,7,60,1014,2,1020,56,24,1019,245,952,916,919,51,933,927,55,921,923,67,951,194,11,893,335,363,1021,1022,991,1023,1004,19] [0xc50056851840c3,0x6c5585004004185,0x30c1845966c4304,0x3451c51847c4405,0xac56841c71857df,0x191711491208185,0x88e191091685208,0x2d12d118e08e2ce,0x8ce4ceb0e1848c4,0x81730c4c468418e,0x59700330c803596,0x171d7003043017,0x2430031c3017041,0x1425401471c003,0x1400002d003703,0x6d491400b082014,0x86f40c04100b02e,0x94c861418058358,0x24a48a670418258,0x40a08a95865940a,0x74a7550952d58b1,0x8159d540a98a74a,0x2074ca9ca755995,0x481a28341241c87,0x822c13cf35e249,0x3410822de3de35e,0xd07347a474c1cc1,0x2c8082341a414c7,0x3cf2d90824993d9,0x488a884c9d49488,0x90f489a894c8d88,0x376cf]⟩,
  ⟨73,9,[ew211,ew246,ew247,ew248,ew249,ew250,ew251],lh 6 [920,20,921,43,19,12,11,245,1024,9,1027,14,10,7,1025,27,25,2,16,6,1029,17,874,1026,59,1031,23,919,41,0,1028,1030,58,51,57,916,918,927,21,923,933,53,952,953,964,62,998,40,335,965] [0x14539b0c3223145,0x2a41862230c35db,0x417a51863a5041,0xa95db6182a4,0x2490000265db1e6,0x5272495272cb38e,0x1047e875d39c2cb,0x66810438e75d3aa,0x183ac3041205185,0x5c3403285041203,0x30c2054105c5305,0x830832051c7003,0x443085b052031c7,0x2154555152cb203,0x12d2156957032cb,0x6551042206a0860,0x30678641078130c,0x2861c6001410286,0xb862811c1081081,0x5124512812c1086,0x1127014412922d2,0x2a212286269a292,0x1c700c00c652692,0xc45100002f002,0x34d016256016370,0x184f101611600c,0x2497d64d37d8118,0x8724908734d09c,0x4d30993cf08234d,0x824d30873cf087,0x10450d3cf649104,0x5093cf84d]⟩,
  ⟨73,9,[ew212,ew246,ew247,ew248,ew249,ew250,ew251],lh 6 [11,920,16,17,923,15,7,21,1032,27,1035,6,43,19,12,245,1037,53,1033,59,25,20,1034,1039,23,919,681,24,10,1036,1038,58,51,57,916,918,927,921,9,933,874,1025,952,954,976,62,1010,893,903,965] [0x38e4990c322238e,0x2a30002220c3599,0x827640004a4082,0x411285994d32a3,0x1c74251454a91c7,0x5991a649a145425,0x2497a72cb041066,0x5e72494922cb4aa,0xac308220e000,0x58350328e082203,0x4c320e51458e4ce,0x40c1452036c3043,0x18c68314520c6cc,0x20318610310320c,0x36d20c60c10cb0c,0x5cc34d21f61f81f,0x700740514755702,0x280140055515280,0x6c02951454156d5,0x102102280180680,0x342100b80282182,0x2a1361821618282,0x3ef05c1455c2602,0x5c3cf051151051,0x70044186051051,0x532f1051351041,0x6877912cb793353,0x10f10f40f18f107,0x2cb5c7247407187,0x4072c780f24940f,0x34610624911734d,0x104249106]⟩,
  ⟨73,9,[ew246,ew247,ew248,ew219,ew249,ew250,ew251],lh 6 [921,12,27,11,9,5,10,21,923,145,138,1040,1041,6,43,1043,20,25,55,23,56,1042,1047,58,59,916,1046,1,67,1048,918,48,920,41,1053,919,926,19,956,1044,1045,944,987,333,1049,1050,991,1021,1051,52,1025,681,1052,245,7,952,1054,1055,47] [0xce98e4102c10c1,0x54e44e3014102ce,0x60e2c1451541601,0xa099c92ce64e3ce,0x6c1681a412c9649,0x2c96c90091c92c1,0x1092c17010011c1,0x2011012c9709209,0x4d7a970822c14c1,0x7501865810812d7,0x45130318374346b,0xb5fb1f3037833d0,0x503683b8330a78a,0x30a50a00a1ca303,0x1043034920031c3,0x20310430a48a20a,0x82bca4ca303082,0x3c68065834d330a,0xc863c5805c45c05,0x50053c61c7846,0x1040068463c51c5,0x3c51052052053c6,0x3453c6082206cc6,0x88634d885085d05,0x1040002355631c7,0x5a4082000036563,0x34deb9082e3734d,0x81040000005a4,0x34d007082007007,0x7347014094014,0x952212082204944,0x204084212]⟩,
  ⟨73,9,[ew228,ew246,ew247,ew248,ew249,ew250,ew251],lh 6 [921,53,20,11,56,43,27,12,14,1056,1057,926,1055,7,1059,1061,16,874,9,5,17,1,2,0,25,245,1058,1060,55,47,58,57,59,916,60,918,933,51,919,923,1062,952,944,938,991,1025,21,19,62,335,965,45] [0x1c73221452611c7,0x2a30c326114532a,0x8232c0c332b082,0x3250416a44d32a3,0x1043a404132d4d3,0x30c71c0002ee6e6,0x2083e771c3e7208,0x2f6e618631d,0xc38850822470c3,0x6c54c5287082245,0x412474c76c7041,0x5105247547385,0x585007107245555,0x2545943d4208245,0x1b02545d4745208,0x2d418625e5de2de,0x43a03603a02041,0x283103382618283,0x543282104002542,0x3d0596282202003,0x190742582290210,0x29f19f2df5d7290,0x6413981042d05d0,0x18659381101001,0x2113d1371381201,0x39119194134d391,0x6916a01a02e0a72,0x1934d004484691,0x186004344019492,0x3300400400b,0xa4d3cd1862d22d2,0x3d21922cd]⟩,
  ⟨73,9,[ew229,ew246,ew247,ew248,ew249,ew250,ew251],lh 6 [11,923,874,16,17,15,19,1063,21,55,1065,926,43,1068,245,12,1064,1067,7,59,25,67,20,53,23,1066,1069,24,682,58,10,57,916,60,918,933,51,921,9,919,1070,952,949,938,1004,1033,1055,27,62,893,965,195] [0x3cf4211041e03cf,0x2a20001e010442a,0xc342c00042b0c3,0x4240826634d32a2,0x20846308242d4d3,0x36520836514542e,0x2e66a726641c145,0x4106f6a7186041,0x8440c31cf000,0x68450428f0c31c4,0x821cf51468f082,0x34c1451c46c4444,0x54c7041451cc6cc,0x1c45550442491cc,0x1b01cc60c04c24c,0x2cc1861dd61d2dd,0x780a00514a16082,0x280140456516280,0x6c02961453566d6,0x43555280240700,0x183040540283243,0x29f19f2df618283,0x3b145e1452c3603,0x91e38e457157357,0x242042482457257,0x442182057492442,0x6426531932d3a72,0x34e492048249642,0x2c834848804e24e,0x2cea4e34e1862c8,0x5204b186348188,0x41073052]⟩,
  ⟨73,8,[ew246,ew247,ew558,ew248,ew249,ew250,ew251],lh 6 [1071,43,12,1073,20,943,9,11,245,19,6,16,25,27,14,1075,53,7,1046,17,10,874,2,23,1076,916,1078,1072,58,57,59,5,1074,920,1025,21,923,926,1055,1081,918,919,944,1077,335,1079,965,1080,1082] [0x1c10012cb0021c2,0x26420022c2001,0x2001641001001,0x6c25026c17c1002,0x2020015140027c2,0x1201001001002,0x38e001581002002,0x1381013593013,0x5dc01c2490135d3,0x700701325301c,0x6470c4a04004644,0x807307804504007,0x2070c430c0c7514,0xc42040c40c4007,0x5960c43840c70c7,0xc45840cb38b0cb,0x25d0dd5d70cb24b,0x3e130c0cb5cb0dd,0x4104a230c4a2410,0x145aa36e92233e1,0x18662438e492186,0x6a534d4ab38e624,0x2494a634d4a6249,0x1502083cc3cc6a5,0x18614c2083d03d0,0x3d519561546c3d0,0x2ae3d5355b50451,0x9d528a9de35ebde,0x186148451152186,0x15a34d145451148,0x28a14834d14828a,0x61128a686246145,0x60628ac11249]⟩,
  ⟨73,8,[ew246,ew247,ew558,ew555,ew248,ew249,ew250,ew251],lh 6 [17,16,6,245,9,1071,14,27,43,20,7,25,23,943,59,53,874,1073,19,1072,916,2,5,1075,10,945,1078,55,937,940,700,1085,948,950,1076,12,918,11,1074,1083,919,921,1084,21,1086,1087,1088,1089,944,1090,1091,965,1092] [0x11249205205145,0x140214208148014,0xb011163013000,0x38014b2d338e,0x1402030c8148003,0x1500010020a200,0x99492002008104,0x509045040480142,0x53041501264249,0x3a62cb04e045165,0x4490430412c144e,0x2462414412430c9,0x49555046181541,0x30c4524a730c052,0x74b2cd369713a01,0xdd3cfa8b2de3cf,0x186b0410d7eb703,0x8420ad18680a2a0,0x5a130cbc20ae30c,0x6187965936185d6,0x35fc0d0c334d357,0x12228a88413128a,0x826471da082644,0x3c30d05d06871f2,0x28f1044030cf5cf,0x1f33ca29010440a,0x40208e1ce382090,0x1831040c61b4104,0x1c70c209a1c7346,0x6c71c6306342083,0x1871db31b]⟩,
  ⟨73,8,[ew246,ew247,ew559,ew248,ew249,ew250,ew251],lh 6 [1093,17,21,1095,7,43,16,11,948,20,19,874,27,245,53,15,1097,6,12,25,1077,1098,10,23,916,1099,1094,24,58,57,59,5,1096,920,1033,1046,921,926,1064,1102,918,919,9,949,893,1100,965,1101,1103] [0x1c50052490121d2,0x5605012249005,0x5001601001001,0x6925926817c1005,0x6c10015960127d2,0x56db005085001,0x1005105001082,0x5005001101001,0x5dc01c30c0015c1,0x900900128101c,0x6090c6a06006606,0x8074c7806586009,0x3c60c64d30c7596,0xc93cf0c90820c6,0xc60071090c6086,0xc70c70c61040c6,0x29d0dd5d70c7287,0x4214d30c75c70dd,0x2cb5224d35222cb,0x5643cf523082421,0x1045233cf564082,0x66528a208aea6a9,0x30c52628a52630c,0x54e36c40b3cb665,0x40eb4b34d40e3ce,0x40b40b20b10b40e,0x46e40e30e20e10e,0x9ce4519de31ebde,0x20d54d10d202502,0x64230254210420d,0x442c0d30d54d451,0x20444421928a542,0x20845120428a]⟩,
  ⟨73,8,[ew246,ew247,ew559,ew555,ew248,ew249,ew250,ew251],lh 6 [17,15,16,6,27,7,1093,25,43,20,5,10,19,948,21,245,1095,59,24,1094,916,23,874,1097,945,1099,56,937,940,700,943,1106,950,1098,12,918,11,1096,1083,919,923,1104,1086,1105,9,1088,1107,1090,949,1108,1109,45] [0x210249206206186,0x188014000180214,0x70101a2013008,0x4401871d3451,0x380212488388012,0x5000180205200,0xd830c003008188,0x502246240300183,0x930895090a3082,0x4651c70910861a4,0x4920810821c2411,0x245242482241049,0x89409085082402,0x55540c32655508c,0x7071cd3686d39c2,0x39c596a471dd596,0x4178e39e041a8e,0x8030cd7ec6c516b,0x2a0104b830ed104,0x1c774a2931c75ca,0x84f3e1041bcf3d7,0xc0d14534d358041,0xc36041190c335f,0x28f3cb041644131,0x14b5cb2cf2ca041,0x10b2c52ca5ca285,0x2c32ca1042830cb,0x14134104504ec8e,0x11a6830c1101385,0x14411930c043cda,0x34410530c]⟩,
  ⟨73,8,[ew211,ew246,ew247,ew555,ew248,ew249,ew250,ew251],lh 6 [43,19,20,10,245,7,2,14,27,9,1024,6,17,16,1026,937,943,940,25,23,874,1027,1084,1100,920,921,59,916,918,939,700,948,955,665,1029,1031,919,1110,53,56,1088,12,1111,11,1112,1113,1114,1115,1116,1117,40,1118] [0xf30c3c001b30c,0x34d74209c34d6c0,0x3d63d638e70209d,0x98f0c379694f3a4,0x2494519cf104450,0x5c71df2497c71d6,0x56208a01060208,0x8200a00a28a801,0x120152a900e015,0x3000c02924aa0c3,0x28c004000280304,0x30618c1c700600c,0x4e10410130001c7,0x2ab08e080041293,0x5430ec49208308a,0x102542344342492,0x1860871cd54d084,0x810421863471cd,0x6024d35410614d3,0xc339e38e0c3611,0x644119419404118,0x1621865c5150bad,0x418cb2ef186885,0xd10e3041c4b2f0,0x143183451c90104,0x540c5154194505,0x50b51a05a68b2d4,0x144249105157249,0x20810b2f3208405,0x14820904940b2c4,0x248205045]⟩,
  ⟨73,8,[ew212,ew246,ew247,ew555,ew248,ew249,ew250,ew251],lh 6 [7,17,16,245,23,10,24,21,19,27,1032,6,43,20,53,1034,15,937,948,940,25,1035,59,1104,1079,920,923,916,918,939,700,943,9,955,665,1037,1039,919,1119,874,1084,1088,12,1120,11,1121,1122,1123,1124,1125,1126,903,1127] [0x5130c44105b30c,0x34d74209c34d6c1,0x4574573cf70209d,0x9d15967979913e5,0x1c77d04280c34d2,0x4d381102061041f,0x257208a49261208,0x8204a04a28a849,0x540552aa04f055,0x4114529452b145,0x1c730618c1c7046,0x40001281300001,0x12220804404c28c,0x2ac08f081208284,0x54516d51408514a,0x40d186090402514,0x542340002186350,0x8820d54d080002,0x642104548222104,0x1453de3cf145653,0x8c30e31866030d9,0x1a49a48002e186,0x10490b2d2c2f680,0x1461a4104c8b2f1,0x3850c338638e0c3,0x10e4d3cd2000393,0x38b39611658b2ce,0x34830c00c7607,0x2490cb2c72471c0,0x92741041cb1c3,0x489240100]⟩,
  ⟨73,8,[ew246,ew247,ew555,ew248,ew219,ew249,ew250,ew251],lh 7 [10,9,23,21,5,43,6,20,1040,943,17,16,1041,19,25,56,55,948,27,1042,59,916,945,1,67,918,1046,921,923,11,1043,1047,940,245,937,7,950,12,1128,1129,1130,333,1131,1083,1132,906,1086,1133,1134,1135,1136,944,1085,1137,1092,1077,1109,1138,1139,1140,1084,1100,1079,1088,1089] [0xc0e1c2880a20408,0x51c146084a14985,0x5281440e1c98a14,0x82a553882c14a85,0x50614517142840a,0x530145030614b97,0x502045183028081,0x8040940d1a28102,0x810743933a2868a,0xc000150e521c007,0x2c18ac3990e1c70e,0xb1e2c58c1630c99,0xb060c38f1e1c187,0xb2040581021c807,0x2d040858d1a1c081,0x1e0810582043068d,0x1e0000984084c000,0x3262c17962c6971a,0x1b060c4b634d5a33,0x1170dc483066c49b,0x110204e113870081,0x3a0c19c82047c306,0x47610020007c102,0x60003c0011004,0x7a002030610484,0x402042110800080,0x40c180020001f00,0x2206840060010104,0x9128d10146248a1,0x400409f860c90102,0x1102044891290306,0xf0c18192060c483,0x104041860c3c90f,0x124488022040912]⟩,
  ⟨73,8,[ew205,ew196,ew246,ew247,ew248,ew249,ew250,ew251],lh 6 [15,9,874,27,20,12,21,11,19,23,25,17,2,1001,958,58,1002,71,53,70,10,6,1141,960,1008,944,1005,57,59,56,67,1142,1004,916,16,957,959,962,921,14,961,918,1006,923,1009,678,1143,43,24,1144,37,62,333,207,194,893,1145,386,1146,965] [0x65682059fb59599,0x3cf3504213cf656,0x3978a31e285040d,0xa528a9420a428a,0x186980018186902,0x38e9e3067600026,0xdf208b830e8208,0x1c7358bda410a03,0xa5144e1c7391469,0x4da0826934ea082,0x4134dc1a186a93,0x5cc32b041acc317,0x2560c3c4926c0c3,0x44b2c4110451b09,0x15414b4cb14410b,0x1853452d45054c5,0x4b14c14d372606,0x1491450452cc2cb,0x5052083c93cf233,0x28a1d41c72b4114,0x1001041861c01c4,0xd5704110e107187,0x21b6c9d8420438e,0x498dca00010925b,0xe520522b8292012,0x2424ba482042097,0x9555c25c715ec2,0x30004000c006041,0xdd7555400c018c,0x7830c120101501d,0x430de21e]⟩
]
def nodesBlock34 : Array Node := #[
  ⟨73,8,[ew211,ew196,ew246,ew247,ew248,ew250,ew251],lh 6 [1024,245,959,12,20,17,14,23,21,10,19,56,1113,1148,9,1147,1151,25,11,6,57,71,16,7,874,15,1149,1153,2,916,920,1150,1152,58,59,921,27,1145,1031,966,919,1026,957,37,53,849,43,198,678,1154,62,194,335,965] [0x4102aa683cb04b,0x1d0c308b78b01d,0x2b3cb0c300b30b,0x68810835951401d,0x2483591047c8508,0x6883880828ec3c8,0x18641938e419199,0x68b2ad808908688,0xc36c828a68b90b,0x3411040008ee3c1,0x55530c10433056f,0x8130109e249341,0x18609e0b13c1249,0x40118140170130c,0x1c16e628a32571c,0x6e61c7301281301,0x545005104003555,0x3c5445003104005,0x2450034513c3243,0x5385003703005,0x1c500338e005705,0x211e10212b2005,0x4517c424400528a,0x844513522527d2,0x19641638e352192,0x356296952392356,0x1c73542949d41f3,0x985f40891866d6,0x1d80895d7098198,0x8221e20a24f5098,0x4d36c61c78184d3,0x4064d39d71d7417]⟩,
  ⟨73,8,[ew204,ew197,ew246,ew247,ew248,ew249,ew250,ew251],lh 6 [11,14,43,53,21,19,24,9,16,10,23,12,990,969,58,25,39,362,0,874,6,27,971,995,1158,992,355,57,59,1,55,1157,991,949,916,20,968,970,974,15,923,972,918,993,921,996,944,1155,1156,679,1159,17,2,1160,973,62,333,201,194,997,1161,335,1162,965] [0x85882061fc70bee,0x38e31042238e858,0x3568e402389040c,0xe62499830e5249,0x1c734d9e4127943,0x5c10681c7a01057,0x15f28ac8516928a,0x317cd9410a45,0xa9a68d00035a6aa,0x4590c365146b0c3,0x104b06196104ad1,0x30cd190415861ac,0x498145d524ad145,0x208808b000b52,0x2c92c24422c8202,0x8b18b08924b44b,0x3022c4102182084,0x9208c3365c71c2,0x24214539238e177,0x3cf0090003f8209,0x34de5610400d008,0x80482071c0040,0x15b6cae88148007,0xd6ecf10f20a29b,0xf430433fc3c3103,0x2930fe0d30534d7,0x4d451c29c714fd3,0x461c61810441c4,0x55d754506546101,0x79554114119419d,0x5555e15e]⟩,
  ⟨73,8,[ew212,ew197,ew246,ew247,ew248,ew249,ew251],lh 6 [1032,7,11,15,970,12,43,9,14,10,1123,1164,27,20,1163,53,245,1167,19,0,25,6,355,21,57,1165,1169,24,55,916,920,16,1166,1168,58,23,59,923,1162,1039,977,919,1034,968,973,874,844,17,204,679,397,1122,62,893,965] [0x4102baa938705c,0x1d14510778701d,0x2c387145007287,0x6477c72c861801d,0x3c82c87df807087,0x64740710496d388,0xc34484084480c8,0x65c32e848488647,0x14568830c65c49c,0x2c108200096f381,0x59628a0822b15b0,0x10128111e2492c1,0xc311e132381249,0x4410c14416c12b3,0x4c16a730c2a66db,0x6a74d3281301281,0x58600634d005596,0x38650600534d006,0x246005514385245,0x65c60056c5006,0x4c60055d70066c6,0x224e20224b4006,0x51480d24d006492,0x10d5142c2242802,0xc344d5d72c20c2,0x2c24829825c22cd,0x8c22d8498a184d3,0x10f4351090c3682,0x8cf10941010f0cf,0x8648e412457610f,0x55568330384f555,0x443555a1030c450]⟩,
  ⟨73,8,[ew246,ew247,ew248,ew219,ew249,ew250,ew251,ew556],lh 6 [25,11,5,56,55,1170,19,20,46,984,58,48,1040,57,27,1047,1138,985,1,21,67,9,1042,1130,10,1139,1052,926,47,921,923,59,916,982,1041,983,1053,979,951,62,12,1171,1172,1173,15,14,952,944,1137,1174,1175,1054,682,6] [0x1cc0415c71ca041,0xa29f288000287,0x14c14880821f20a,0x14a48a20c205805,0x508293285492153,0x215205514155148,0x14f18614c14c327,0x11d81cf328156,0x1e11c7000058601,0x47a472e12cb5cb,0x4812c30cb48b043,0x2c410b50b044041,0x34d64d046041501,0x40d0620413c1346,0x230015c136234d,0xc0a800a3082682,0x680083082242003,0x84082442004100,0x82642006000680,0x582024000ac0086,0x9430c05800a4082,0x18926d94410946c,0x3db3c618f66e6c6,0xc70be642641c71b,0xd1104249250cf2,0x3830c60d338e0c9,0xdd0d025c4c64c3,0x11519525d743243,0x47454e38418410e,0x45e78444411e110,0x30cd4e58e]⟩,
  ⟨73,8,[ew246,ew247,ew248,ew560,ew249,ew250,ew251],lh 6 [1176,17,19,984,20,24,10,46,7,27,11,1179,53,9,1180,25,2,16,874,12,0,1181,47,1182,916,1183,1177,55,14,57,59,1184,1178,918,991,1046,920,1025,21,923,335,965,952,919,944,921] [0x281001104013293,0x6813c1013104001,0x1860133cf693193,0x7007001601001,0x141001001007607,0x7145007007001,0x6c1007407001001,0x76c7001410001,0x514007087001501,0x804186001082007,0x3cf2ca18680a3cf,0x8c48842ca84a384,0x2ca8ca88a2c4844,0x2c42c40c41452ca,0x4102c46c40ca145,0x5844102d1711551,0x9d5dd5142d1091,0x3869065d15112dd,0x94638c90c64c94c,0xcc0cc386145646,0x70c0c664638c14c,0x39271255222838c,0xaa939209264c208,0x7d27d27de09e5de,0x34d0c3b266ab166,0x56734d567208596,0x82000249596208,0xed082018249018,0x34d0c52050d634d,0x52490c32080c5,0x820d72490c3082,0x5482495cd0820c5,0x54d2495c8082]⟩,
  ⟨73,8,[ew246,ew247,ew248,ew249,ew561,ew250,ew251],lh 6 [1185,43,20,21,2,19,985,245,16,980,1188,53,874,27,12,1189,1190,11,25,23,1191,59,10,916,1192,1186,15,682,57,1193,24,1187,918,1004,1077,920,1033,47,921,893,965,952,1194,919,9,949,923] [0x44100108200e44e,0x64148100e082001,0x54100e49264e54e,0x10c100e78e001,0x5c100e0ce001781,0x95c9009009001,0x9001101001001,0x1001009109009,0x4d30091490014c1,0x7c2582001141009,0x4922915967d1492,0x4020c22916913c2,0x8026d10c328269a,0x288808888848282,0x108282282882842,0x182102288288188,0x15c51c4d3288148,0x3d60c35084c829c,0x1c73cb0cb40b1e7,0x60c90c3cb8cb616,0x10b60b90b3cc8cc,0x3cc10418c18c3cb,0xa683cc14c18b60b,0x74c74c755155515,0x9474079876c3943,0x1836c3403983a87,0x104187187407104,0x407147503343403,0x10440314550734d,0x145186b6c66b,0x34d01714501734d,0x18634d0041441ae,0x18434d194145]⟩,
  ⟨73,8,[ew211,ew204,ew246,ew247,ew248,ew250,ew251],lh 6 [1027,245,43,10,14,19,11,993,24,9,1196,21,1199,39,1200,16,25,6,57,17,7,1195,1197,1198,27,1202,23,12,918,920,1201,1,58,874,59,921,1161,1031,2,999,927,1028,994,201,53,849,35,680,1113,20,40,62,335,965] [0x4102aa6854b04b,0x2886db1cb74b01c,0x825cb6db58b08b,0x830801c492288,0xc801c02b548488,0x58b24b1c78ec5c8,0x104388249388108,0x59f16d78860858b,0x8264814559f61f,0x33008232f36e281,0x8f15c118128134d,0x1c13011dd0c3000,0x2491dd1f25410c1,0x38124138110130c,0x141665618324104,0x665145301601301,0x1820023c228d186,0x5c240200d3cf282,0xc328d4105cd0cd,0x3932492829821c2,0x693902249293993,0x2a06a09e0173293,0x41054f0c3653145,0xf4100060c6546,0x10400f249006106,0x614600624600f,0x68601215201269a,0x1e15341c3104006,0x1431c35141e1121,0x7a21621e24751c3,0x451644144783451,0x3844519d4154394]⟩,
  ⟨73,8,[ew212,ew205,ew246,ew247,ew248,ew249,ew251],lh 6 [1035,7,2,11,1006,12,1204,19,10,9,15,20,43,27,1207,1002,21,24,17,53,245,1208,25,23,57,6,1203,1205,1206,1210,918,920,1209,67,58,59,923,1146,1039,1011,927,1036,1007,207,874,844,1211,1003,1123,16,903,1212,893,965] [0x4102aa68689049,0x1821451097c901e,0x4927091456c9489,0x238201e618182,0x4c201e02b682602,0x6c950910492c702,0x28a542502542282,0x6e136d8021c26c9,0x49274234d6e11e1,0x3b04923af3ee181,0x9317010c11813cf,0x10138111f208000,0x41011f132681201,0x5414105412813b3,0x3417661c73a528a,0x76634d3811c7381,0xcc00c2cb18f0c3,0x70c58c00f2cb18c,0x20c18f59670f208,0x54c28c18544f10c,0x5c594528518c451,0x1a25e29e21c7185,0x59668b20b7451c5,0xb596003203683,0x28b00b451003283,0x31c300344300b,0x5c30181d80185d7,0x113534108448003,0x5d3108514113453,0x8235e3123675113,0x659750350813659,0x5506509d434d554]⟩,
  ⟨73,8,[ew246,ew247,ew248,ew219,ew249,ew250,ew251,ew557],lh 6 [23,5,10,145,56,55,43,138,12,4,1016,1041,57,58,25,1,1047,1017,0,67,1216,59,21,9,906,1139,1052,926,47,921,923,1013,1040,918,1042,1015,1053,1048,1014,1018,1213,1138,194,11,1214,1215,15,14,952,991,1217,1218,1219,1054,682,19] [0x206306198188308,0x38e21520638620b,0xd80c67c6195188,0xc83c81a81837c3,0x4c62162033cf0d6,0x1971834d30d70c6,0xcd00d359343003,0x80d3693438030d0,0x30e3895550d80cd,0x1c984924e24c08c,0x10c24b2478471cb,0x30f3c71041cf1cc,0x2471451d31c9149,0x1cb1cb2ea253,0xa30902eb1e21d0,0x102b02063041681,0x682044041281084,0x45041441085142,0x41641080082682,0x9410a4082b42040,0x984102942064041,0xa2af98514a46e,0x41b4000106706c0,0xcf2c6752751c71b,0x11114528a294d74,0x48410001649210a,0x11d11429c580004,0x15700029d744284,0x4765d2485000152,0x45e78544515e154,0x2cbdc0880]⟩,
  ⟨73,8,[ew246,ew247,ew248,ew562,ew249,ew250,ew251],lh 6 [1221,43,23,1016,27,16,4,15,10,12,1220,14,7,70,1223,25,874,9,17,1224,47,1225,2,11,918,1227,1222,58,59,1228,916,944,1046,1226,920,1025,21,923,62,335,965,952,919,991,921] [0x5c10011412895c9,0x6813c1009145281,0x2082893cf689209,0x8017c1289789381,0x2898097c9281781,0x2812810c11c1289,0x2cb2815810c91c7,0x5012c12925924d2,0x9b55b126292092,0x84520855210429b,0x3cf0172088573cf,0x6006005605005,0x1c7005005006606,0x61c6006006005,0x5960062c6005005,0x65860052cb005,0x106006086005104,0x388888005082006,0x8c838d88d64d8cd,0xcd0cd3881c7648,0x2cd0c864838d1cd,0x3902d04d032738d,0xa6839009064d30c,0x75075075c09c55c,0x2cb0c3ae46aa1e4,0x4e52cb4e530c514,0x8200010451430c,0xec082018104018,0x4510c73070d4451,0x71040c330c0c7,0x820d51040c3082,0x4cc1045510820c7,0x4d111154c082]⟩,
  ⟨73,8,[ew246,ew247,ew248,ew249,ew563,ew250,ew251],lh 6 [1230,20,21,43,19,1017,1229,14,245,0,362,17,382,53,12,10,11,1232,1233,25,1234,15,23,918,1236,1231,24,682,58,59,1237,916,949,1077,1235,920,1033,47,921,62,893,965,952,1238,919,9,1004,923] [0x40300304118e40e,0x6434c300e041183,0x3cf18e4d364e3ce,0x48308318e68e443,0x7c36ce08218369a,0x18b7cb84b80b183,0x1cb183183843803,0x1431c318b18b14b,0x59c51c12718b24b,0x8813cf50b10419c,0x4d30103cf8904d3,0x1082010550001,0x5c1010090001541,0xc5cc00c00c001,0xc0011c1001001,0x100100c1c700c,0x10c00c58c001101,0x44f55500158100c,0x20844d54d48d228,0x60a90a44d8cd60f,0x1cd60d90d44a8ca,0x44a1ca14a14a44d,0xaa944a58a14d60d,0x78a78a79d11d51d,0x9484889886c2942,0x1426c2482982ac8,0x1c21481484881c8,0x488104502242482,0x1c7482102508249,0x104145bad66c,0x249017104017249,0x14524900710416f,0x147249154104]⟩,
  ⟨73,8,[ew246,ew247,ew248,ew249,ew564,ew250,ew251],lh 6 [1040,11,21,1242,25,23,20,1240,14,1,67,9,1244,15,27,10,1246,145,19,1247,945,59,16,874,6,1239,916,919,1170,57,1248,53,1241,1243,1245,918,920,1252,926,951,43,944,333,1083,194,906,893,1249,335,1250,965,1251,921] [0x41014186011051,0x651111011191000,0x551007107647555,0x70a0000260011,0x6c7003082007249,0x2a1029028647,0x2cb00728a0072e1,0x1c49200714700c,0x3cf00749201c15c,0x4013c188112a886,0x864013414c6104,0xc108240634d0c6,0x8c65065064018c1,0x401201501ac1406,0x2c14162163162cb,0xb5d16c416496301,0x8279614541d49d,0x4df09f0df0ee4c4,0x6cf4c49040cfbcf,0x5046c44cf90f64f,0x2d73173304c42c4,0x4d7497304c444d7,0x618955495cd5632,0x2682009009957,0x2c20096890c20c2,0xcd2cd0cd208002,0x6090cd38d0c2208,0xcd60d0c938e0c9,0x28a01a20800028a,0x7a61450f420801a,0x38e52714552738e,0x30a38a3081457a6,0x30838e30a145]⟩,
  ⟨73,8,[ew246,ew247,ew248,ew219,ew249,ew564,ew250,ew251],lh 6 [23,5,11,25,1040,1240,21,10,9,1,48,6,1242,67,27,20,55,145,16,1042,1244,19,1170,56,57,1239,1137,1246,1041,1247,1249,1043,1248,1047,1129,944,12,1253,1046,1133,1254,194,52,1250,15,919,916,14,906,1194,921,1138,1139] [0x3c408288f3d1091,0xc51471d10d144f,0x1441441044471c5,0x24518510925a123,0x12415314c186149,0x14d14520510d35a,0x596555140154208,0xc33c71c5555580,0x3db3cf0c30871c2,0x8298229b28a94a,0x1822975ca18a097,0x29c28a9ca09c082,0x492208090082a02,0x2948b482208490,0x1dd1d200060b618,0x1c778705d041a81,0x7870461813011c6,0x5f0414c10df0c7,0x415010d00c34c3,0x2c10c00c3ac3050,0x6461832c3040041,0x40412e653b4c52c,0x2cb80000c32f650,0x2442602cbc40030,0x30910918c186106,0x38624c25441030c,0x18b2c938e24b246,0x20434d10820434d,0xcce3a1000c88,0x34e34800084e3b4,0x20e20d000]⟩,
  ⟨73,8,[ew246,ew247,ew248,ew249,ew565,ew250,ew251],lh 6 [1041,43,21,1258,48,58,25,2,1255,9,24,1259,56,55,27,6,10,1257,23,19,53,1083,17,874,918,1256,1260,1261,125,138,59,916,945,789,104,920,927,1265,926,1018,62,1130,919,11,991,893,1262,335,1263,965,1264,921] [0x101001541205104,0x641181005005201,0x401205186645410,0xc1081205285441,0x7c50c508220128a,0x2017c1541801205,0x2492011c1545805,0x2c12492161d62d6,0x485a454e8216496,0x6c44046964d3205,0x18601c41c6dc186,0x40a1000321004,0xa8400308200430c,0x36202c02b644,0x24900434d004262,0x1d4920044c400b,0x8200449201d4dd,0x4540940d40ed450,0x9064548d40d0b90,0x5549144468c66c6,0x2572d72ef446246,0x4574972c6c06457,0x3cf95e49ec9e3f1,0x260200c00c957,0x24200c60c0c20c2,0xca24a0ca1c7002,0x3cc0ca38a0c21c7,0xca3ca0cc38e0cc,0x34d0181c700034d,0x6a638e0f31c7018,0x3cf56738e5673cf,0x2cd38d2c74c76a6,0x2c738e2cd4d3]⟩,
  ⟨73,8,[ew246,ew247,ew248,ew219,ew249,ew565,ew250,ew251],lh 6 [10,21,5,1041,6,55,12,125,9,23,43,145,56,1258,27,25,17,48,19,1259,1,58,138,1256,1255,1040,67,1217,1042,1257,1262,1043,1048,1260,1047,1132,1253,1046,1133,1266,991,11,52,1263,24,919,918,2,1130,1238,921,1216,1139] [0x18a44a2a3286451,0x3cf18018a3ca183,0x2e42ca60a280006,0x2c65062a528b60b,0x64618104b5142c1,0x1a718b64b2e62c6,0x210690408206686,0x115552490110188,0x1cf3d1000412415,0x1c30c344f3c7007,0x470cc31b0e81c3,0x1dc1cd0411cc307,0x1472070c515b0e9,0x2491d21d32081c5,0x1d007249592596,0x4078009d082a82,0x780081082342001,0x9f08280201f000,0x824c2005140800,0x102009240ac0085,0x5c1040104089082,0x1430ee5dcb4d4ec,0x10484924d36f5c5,0x303321104c49270,0x34c0cc04d0410c1,0x38104d05314534d,0x4410c38e304101,0x2031450c8203145,0x38ecc412238ec88,0x14e388248884134,0x20e205249]⟩,
  ⟨73,8,[ew246,ew247,ew248,ew249,ew566,ew250,ew251],lh 6 [1043,43,11,5,1270,20,7,12,27,56,55,245,1267,1268,21,6,1271,19,17,16,9,1269,67,23,1052,1273,1274,920,138,1,919,58,1272,57,916,52,918,927,933,952,1140,10,1025,921] [0x701a0114530771c,0x5410c1347145301,0x13070c7547547,0x101381307747001,0x88110738e30175d,0x307887547787301,0x5143015818c1781,0x401501312592412,0x5df61f2083125d2,0x6450c581221231f,0x53420c2642642,0x10538e342242005,0x905102382345249,0x342902642942345,0x5963422828c5945,0x402582353293413,0x4616215d7353453,0x2498135d3361,0x2cb0032490032c3,0x2a029543783004,0x28a00318300028a,0x451010186003,0x3cf6834510033c3,0xb6cb00900969a,0x28a0096c910b10b,0x10b28b10b186009,0x3cf10e20e109186,0x10e3ce10b20810b,0x28a01b18600028a,0x82620812b18601b,0x3cf6272086273cf,0x4062084144516a6,0x414214406446]⟩
]
def nodesBlock35 : Array Node := #[
  ⟨73,7,[ew246,ew247,ew567,ew555,ew248,ew249,ew250,ew251],lh 5 [43,23,21,6,7,17,245,9,16,10,5,53,25,20,918,916,19,11,201,207,1275,12,919,1276,1084,940,15,14,1089,950] [0x62c15001ee02014,0xc0a029405000a0,0x4316c5c62873d05,0xb36016ce676ca42,0xf03b3e8594e137,0x21c82308c95255d,0x510e61184118467,0x30c443104350c24,0x320c23]⟩,
  ⟨73,7,[ew568,ew246,ew247,ew555,ew248,ew249,ew250,ew251],lh 5 [6,17,16,10,21,245,14,23,5,20,43,19,921,923,1277,943,7,1278,12,11,333,1077,1076] [0x7b9ac124490a82a,0x1e06290a440d03,0x8d030c8220c407,0x12c0b52821504a4,0x109224a4421d073,0x290a340d0759d69,0x2148701c06b1aa4,0x29880400e3320c5,0x380c028086]⟩,
  ⟨73,7,[ew246,ew247,ew558,ew559,ew248,ew249,ew250,ew251],lh 5 [43,16,20,245,17,53,19,27,874,11,10,12,6,943,21,7,9,5,62,194,1098,923,921,948,1077,1046,965,346,297] [0x10805800b5a409,0x10802000454544,0x104224884903240,0x10422088410a521,0x2a8aab55b40b261,0x414c73330fbbdce,0x398e68432368d05,0x41f482a10519468,0x398e630c67e0c7b]⟩,
  ⟨73,7,[ew246,ew247,ew558,ew555,ew248,ew219,ew250,ew251],lh 5 [17,16,6,23,21,25,5,245,9,43,20,19,59,1085,948,45,1279,12,11,1280,921,893,944,346,1076,14] [0x2b0110012902930,0x12c09001203b400,0x85850c8215282b,0x20d630a821504f3,0x438843b8842d494,0x3b4e5314cf78c84,0x318a310c48c22f6,0x1e5023086531907,0x86240862]⟩,
  ⟨73,7,[ew569,ew246,ew247,ew555,ew248,ew249,ew250,ew251],lh 5 [43,9,17,7,23,16,20,27,25,6,53,15,5,1098,874,21,11,923,921,943,14,1281,12,1046] [0x6ce51314c500802,0x21c61a05ef5394e,0x1010a0580505487,0x808871004200800,0x294c5318a852150,0x6aee862184390c6,0x5b164491211846b,0x8c296248308c28,0x719c293a563]⟩,
  ⟨73,7,[ew246,ew247,ew559,ew555,ew248,ew219,ew249,ew251],lh 5 [9,43,20,10,5,6,19,21,7,17,16,973,1106,207,23,943,45,1282,12,27,11,333,1283,923,335,844,1284,346,1098,15] [0x20c320ad6008831,0x2cd290852143021,0x108751504d68049,0x38ce5284250916,0x3bc0043c001e017,0x4310320c8036400,0x21066298a7e1f7a,0x374e521463210e3,0x4205394c5]⟩,
  ⟨73,7,[ew247,ew555,ew248,ew219,ew249,ew564,ew250,ew251],lh 5 [20,145,5,9,25,43,23,21,6,17,10,19,16,1041,1286,1137,1288,45,11,59,1285,1246,201,944,1287,15,916,14,1289] [0x3015a009320240,0x3006c180a0036c0,0xbee10bdce5040b,0x304610e0a10b4e1,0x1154211d4212a10,0xc9c821108211082,0x2a4a942d0bd8f45,0x48d232c62839c7c,0xcc8324c8]⟩,
  ⟨73,7,[ew246,ew555,ew248,ew219,ew249,ew565,ew250,ew251],lh 5 [48,5,43,9,10,25,21,20,19,6,16,23,1040,1290,1217,1293,45,17,12,1285,1255,1,67,1291,1292,333,24,918,2,1294] [0x154549888521651,0x40876188e2130c2,0x3ae0039ad2810b,0x58060060e0030c0,0xe4a1098a1095ef,0xd18810908109081,0x3a8ea4ad2be0f67,0x50d433c2093187d,0xd0942909]⟩,
  ⟨73,7,[ew246,ew247,ew248,ew219,ew249,ew570,ew250,ew251],lh 5 [5,43,25,16,17,6,19,21,9,145,20,48,10,23,923,921,45,12,333,11,1043,1042,15,919,1276,14,1295,1047,1138] [0xa5210818148469,0x310242062420424,0x58d4b5a84c9308d,0x699a350c6a98c6b,0xa80141000210002,0xc5ec71000610002,0x469e73b8a629b28,0xe1768721f0814e7,0x531505]⟩,
  ⟨73,7,[ew571,ew246,ew247,ew248,ew249,ew250,ew251],lh 6 [20,21,19,9,43,10,7,245,6,17,145,16,27,48,25,1240,125,56,53,874,23,55,916,5,921,1296,1299,1,1170,138,59,920,14,926,952,918,1297,1298,923,893,335,965] [0x11928a64411628a,0x34d58001934d584,0x90515f5d78c0016,0x5a1c77c51655d7,0x1a06810581c7601,0x6030da186983818,0xa22088820a1208,0x34410000a34a842,0x3c5144384280284,0x3c96c910514f38f,0x18424104f6db3c1,0x1030c9189243244,0x9c51c702089509,0x15040e380145242,0x40140b44b00e390,0x2c05402c12d0451,0x8000300b5552c3,0x1401d09d754500,0x1d24524879c5451,0x5534c6a12552147,0x788a53093486193,0x1810c14c821e09e,0x3010460470c31c6,0x4804730c1c8201,0x30608218c303083,0xcc]⟩,
  ⟨73,7,[ew571,ew246,ew247,ew555,ew248,ew249,ew250,ew251],lh 5 [245,5,6,43,21,20,7,9,19,10,59,27,23,916,1296,15,14,918,919,1137,145,48,333,201] [0x506722b4ae1c46d,0x588e6840807bd41,0xc2a0d0651b962,0x28d8b18cc731003,0x31cd7014050d835,0x10090a42c430a7,0x200881204731cc4,0x820892908520,0x24090200884]⟩,
  ⟨73,7,[ew571,ew246,ew247,ew248,ew219,ew249,ew250,ew251],lh 5 [5,10,145,6,20,43,17,48,21,9,16,23,19,12,11,921,1299,45,919,1085,923,333,245,7] [0x8020738876b4a2,0x60d304bd0f45272,0x114400884520983,0x618a6314c2118a2,0x3a88739080a90c3,0x5635a88a51147,0x4200042000420,0x4c06b1aee9b2020,0x358d3188d08]⟩,
  ⟨73,7,[ew246,ew247,ew555,ew248,ew249,ew566,ew250,ew251],lh 5 [43,9,7,6,245,21,20,5,23,19,937,11,1269,1267,16,12,1300,916,1301,939,918,1043,52,919,10] [0x803c00f0380d,0x1a400104008a805,0x314c6218f23ad69,0x3a1283184131a93,0x12997b1485254ec,0x390a42a06818441,0x210a338d0208838,0x882320ca208825,0x310c2340d02]⟩,
  ⟨73,7,[ew572,ew246,ew247,ew248,ew249,ew250,ew251],lh 6 [58,145,11,6,19,56,55,57,2,21,10,24,9,20,16,53,5,25,874,27,916,1302,1303,1304,921,59,918,1083,920,15,14,923,926,1130,333,1139,1305,893,335,1306,965] [0x15041540014041,0x826c71da082500,0x58a29c4106871db,0x7572dd70a296410,0x21e5c51582cb605,0x6061972087c6798,0x1140c35041150c3,0x1c784d3401c0804,0xa00140100d355,0x402cb04a280400,0x2080092412cb049,0xc30120804c040,0x1000c30041010c3,0x28209188d28a044,0x349242142351442,0x30218208908d145,0x10e08c08e18e38c,0x3a43871071e31ce,0x44f14f3d7951145,0x1924a798f18f456,0x643a121123d63d2,0x2051864830d9119,0x4c924820b30b2c8,0x2432454c51430c9,0x4c61061934cc10c,0x313]⟩,
  ⟨73,7,[ew573,ew246,ew247,ew248,ew249,ew250,ew251],lh 6 [15,23,12,14,43,10,125,25,6,57,58,56,55,17,874,0,1,9,138,918,1307,5,1308,1309,921,48,67,21,4,53,59,916,945,11,920,923,926,906,1139,1310,893,335,1311] [0x2a008280a29f082,0x4a151c7134927ca,0x5871e25554dc854,0x2d70008871d6555,0xc35cb2d800060b,0x60c3170c38cc318,0x532084c1054208,0x644125102482901,0x850841c4094084,0x1024021051421c7,0x684080084410100,0x10310d68d3430c4,0x34a04a2a628d04d,0x1461871d9145367,0x190189000647646,0x1890c9250246000,0x20625a2460c319a,0x181049208241246,0x15d01d757a05000,0xce3aaa450c5156,0x78820e04e15614e,0xdb45b38839e05e,0x3c06c36c0440003,0x100b3cb2c1040,0x3cc04c30f3d1051,0x44f]⟩,
  ⟨73,7,[ew246,ew247,ew248,ew249,ew564,ew565,ew250,ew251],lh 5 [48,1170,1,25,55,23,56,19,67,10,9,21,1240,1040,1285,12,945,1041,1083,11,893,335,965,1312,1255,916,918] [0x584220b181081c0,0x95480a2010b5e1,0x456601809180e5,0x1ca04110498240,0x48c691a52349a86,0x118c2196c3192a3,0x5884b112e230846,0x394e522088d670d,0x51c8a29ca751144]⟩
]
def nodesBlock36 : Array Node := #[
  ⟨73,7,[ew574,ew246,ew247,ew248,ew219,ew249,ew250,ew251],lh 5 [10,145,21,55,5,43,19,25,17,11,6,56,9,23,361,45,48,1313,1040,916,918,1083,1246,194,15,14,1314] [0x9440701e0909425,0x3346c1b16258a93,0x940701c25284cd,0x32068415010a0a1,0x12d36aa4e03810d,0x201ceba52360c4b,0x2000420c0420804,0x1e94651b23c0804,0xa328cf7a842]⟩,
  ⟨73,7,[ew575,ew246,ew247,ew248,ew219,ew249,ew250,ew251],lh 5 [10,20,5,48,21,19,16,25,23,9,6,1,67,12,145,1255,55,45,1040,918,916,945,62,15,14,1315] [0x7c8e038061185ce,0x415906416459293,0xab40701c230b505,0xb212c4b08b22daf,0x1982318420385a8,0x100c541926304c3,0x100021000210002,0x4e54551709b9002,0xa2a8b18a884]⟩,
  ⟨73,6,[ew571,ew246,ew247,ew248,ew249,ew250,ew251],lh 5 [20,9,10,23,7,245,21,6,48,5,19,145,43,17,25,15,14,333] [0x725c9020086adab,0x51d4709210315ef,0x314c51244902008,0xa2261d4c61164,0x1a8600902030005,0x10ce310481118a2,0x8ce31946620481]⟩,
  ⟨73,6,[ew555,ew248,ew249,ew564,ew565,ew250,ew251],lh 5 [145,25,10,21,16,9,17,23,20,43,19,1286,1316,1040,1317,1288,42,45,1041,12,11,27,893,335,965,37,201,1318,849,844] [0x980121818c5ac20,0x7bea0281cea000d,0x104220884108ec1,0xc986684302116e2,0x8c78319765d1064,0x51d49498c92188d,0x29fa7428e841088]⟩,
  ⟨73,6,[ew246,ew247,ew248,ew576,ew249,ew250,ew251],lh 5 [10,12,20,48,11,9,145,19,7,43,21,6,42,15,919,14,45,62,333,194,5,893,335,965,933,952] [0x304260040910c43,0xae21098c10a521,0x208441884310240,0xa828022e6420c64,0x6b58cb8005b000a,0x414f93e0ae7bd4e,0xa841e103a905]⟩,
  ⟨73,6,[ew577,ew246,ew247,ew248,ew249,ew250,ew251],lh 4 [6,245,21,9,19,20,43,11,7,12,10,15,14,194] [0xc821bbaa57576969,0x2169965757404038,0x2157756040383621,0x83121250d0383521,0x441422313040483,0x4]⟩
]
def nodesGet (i : Nat) : Option Node :=
  if i < 288 then
    if i < 144 then
      if i < 64 then
        if i < 32 then
          if i < 16 then
            nodesBlock0[(i-0)]?
          else
            nodesBlock1[(i-16)]?
        else
          if i < 48 then
            nodesBlock2[(i-32)]?
          else
            nodesBlock3[(i-48)]?
      else
        if i < 96 then
          if i < 80 then
            nodesBlock4[(i-64)]?
          else
            nodesBlock5[(i-80)]?
        else
          if i < 112 then
            nodesBlock6[(i-96)]?
          else
            if i < 128 then
              nodesBlock7[(i-112)]?
            else
              nodesBlock8[(i-128)]?
    else
      if i < 208 then
        if i < 176 then
          if i < 160 then
            nodesBlock9[(i-144)]?
          else
            nodesBlock10[(i-160)]?
        else
          if i < 192 then
            nodesBlock11[(i-176)]?
          else
            nodesBlock12[(i-192)]?
      else
        if i < 240 then
          if i < 224 then
            nodesBlock13[(i-208)]?
          else
            nodesBlock14[(i-224)]?
        else
          if i < 256 then
            nodesBlock15[(i-240)]?
          else
            if i < 272 then
              nodesBlock16[(i-256)]?
            else
              nodesBlock17[(i-272)]?
  else
    if i < 432 then
      if i < 352 then
        if i < 320 then
          if i < 304 then
            nodesBlock18[(i-288)]?
          else
            nodesBlock19[(i-304)]?
        else
          if i < 336 then
            nodesBlock20[(i-320)]?
          else
            nodesBlock21[(i-336)]?
      else
        if i < 384 then
          if i < 368 then
            nodesBlock22[(i-352)]?
          else
            nodesBlock23[(i-368)]?
        else
          if i < 400 then
            nodesBlock24[(i-384)]?
          else
            if i < 416 then
              nodesBlock25[(i-400)]?
            else
              nodesBlock26[(i-416)]?
    else
      if i < 512 then
        if i < 464 then
          if i < 448 then
            nodesBlock27[(i-432)]?
          else
            nodesBlock28[(i-448)]?
        else
          if i < 480 then
            nodesBlock29[(i-464)]?
          else
            if i < 496 then
              nodesBlock30[(i-480)]?
            else
              nodesBlock31[(i-496)]?
      else
        if i < 544 then
          if i < 528 then
            nodesBlock32[(i-512)]?
          else
            nodesBlock33[(i-528)]?
        else
          if i < 560 then
            nodesBlock34[(i-544)]?
          else
            if i < 576 then
              nodesBlock35[(i-560)]?
            else
              nodesBlock36[(i-576)]?
def fastViews : QFast.Table View := ⟨74,viewsGet⟩
def fastNodes : QFast.Table Node := ⟨582,nodesGet⟩
end SignedProjection

namespace SignedProjection
end SignedProjection

namespace SignedProjection
def aliasMap0 : Array Nat := #[0,0,1,0,0,0,0,0,0,0,9,0,0,0,0,0,0,0,17,0,0,0,0,0,0,0,25,0,0,0,0,0,0,0,33,0,0,0,0,0,0,0,41,0,0,0,0,0,0,0,49,0,0,0,0,0,0,0,57,0,0,0,0,0]
def aliasMap1 : Array Nat := #[0,0,1,0,0,0,0,0,0,0,3,0,0,0,0,0,0,0,9,0,0,0,0,0,0,0,11,0,0,0,0,0,0,0,17,0,0,0,0,0,0,0,19,0,0,0,0,0,0,0,25,0,0,0,0,0,0,0,27,0,0,0,0,0]
def aliasMap2 : Array Nat := #[0,0,2,0,0,0,0,0,0,0,3,0,0,0,0,0,0,0,10,0,0,0,0,0,0,0,11,0,0,0,0,0,0,0,18,0,0,0,0,0,0,0,19,0,0,0,0,0,0,0,26,0,0,0,0,0,0,0,27,0,0,0,0,0]
def aliasMap3 : Array Nat := #[0,0,8,0,0,0,0,0,0,0,9,0,0,0,0,0,0,0,10,0,0,0,0,0,0,0,11,0,0,0,0,0,0,0,24,0,0,0,0,0,0,0,25,0,0,0,0,0,0,0,26,0,0,0,0,0,0,0,27,0,0,0,0,0]
def aliasMap4 : Array Nat := #[0,0,16,0,0,0,0,0,0,0,17,0,0,0,0,0,0,0,18,0,0,0,0,0,0,0,19,0,0,0,0,0,0,0,24,0,0,0,0,0,0,0,25,0,0,0,0,0,0,0,26,0,0,0,0,0,0,0,27,0,0,0,0,0]
def aliasMap5 : Array Nat := #[0,0,16,0,0,0,0,0,0,0,17,0,0,0,0,0,0,0,18,0,0,0,0,0,0,0,19,0,0,0,0,0,0,0,20,0,0,0,0,0,0,0,21,0,0,0,0,0,0,0,22,0,0,0,0,0,0,0,23,0,0,0,0,0]
def aliasMap6 : Array Nat := #[0,0,0,0,0,0,0,0,0,0,9,0,2,0,11,0,0,0,0,0,0,0,0,0,16,0,25,0,18,0,27,0,0,0,0,0,0,0,0,0,32,0,41,0,34,0,43,0,0,0,0,0,0,0,0,0,48,0,57,0,50,0,59,0]
def aliasMap7 : Array Nat := #[47,45,43,41,38,36,34,32,0,0,0,0,0,0,0,0,15,13,11,9,6,4,2,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
def aliasMap8 : Array Nat := #[31,29,27,25,22,20,18,16,0,0,0,0,0,0,0,0,15,13,11,9,6,4,2,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
def aliasMap9 : Array Nat := #[63,62,61,60,0,0,0,0,51,50,49,48,0,0,0,0,31,30,29,28,0,0,0,0,19,18,17,16,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
def aliasMap10 : Array Nat := #[63,62,61,60,0,0,0,0,43,42,41,40,0,0,0,0,31,30,29,28,0,0,0,0,11,10,9,8,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
def aliasMap11 : Array Nat := #[0,62,0,54,0,0,0,0,0,60,0,52,0,0,0,0,0,26,0,18,0,0,0,0,0,24,0,16,0,0,0,0,0,46,0,38,0,0,0,0,0,44,0,36,0,0,0,0,0,10,0,2,0,0,0,0,0,8,0,0,0,0,0,0]
def aliasMap12 : Array Nat := #[0,0,1,0,0,0,37,0,0,0,3,0,0,0,39,0,0,0,9,0,0,0,45,0,0,0,11,0,0,0,47,0,0,0,17,0,0,0,53,0,0,0,19,0,0,0,55,0,0,0,25,0,0,0,61,0,0,0,27,0,0,0,63,0]
def aliasMap13 : Array Nat := #[0,61,0,53,0,0,0,0,0,60,0,52,0,0,0,0,0,25,0,17,0,0,0,0,0,24,0,16,0,0,0,0,0,45,0,37,0,0,0,0,0,44,0,36,0,0,0,0,0,9,0,1,0,0,0,0,0,8,0,0,0,0,0,0]
def aliasMap14 : Array Nat := #[63,62,61,60,0,0,0,0,27,26,25,24,0,0,0,0,47,46,45,44,0,0,0,0,11,10,9,8,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
def aliasMap15 : Array Nat := #[63,62,61,60,0,0,0,0,27,26,25,24,0,0,0,0,55,54,53,52,0,0,0,0,19,18,17,16,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
def aliasMap16 : Array Nat := #[63,62,61,60,0,0,0,0,59,58,57,56,0,0,0,0,23,22,21,20,0,0,0,0,19,18,17,16,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
def aliasMap17 : Array Nat := #[63,62,61,60,0,0,0,0,59,58,57,56,0,0,0,0,15,14,13,12,0,0,0,0,11,10,9,8,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
def aliasMap18 : Array Nat := #[0,0,0,0,0,0,0,0,16,0,18,0,20,0,22,0,0,0,0,0,0,0,0,0,24,0,26,0,28,0,30,0,0,0,0,0,0,0,0,0,48,0,50,0,52,0,54,0,0,0,0,0,0,0,0,0,56,0,58,0,60,0,62,0]
def aliasMap19 : Array Nat := #[0,0,0,0,0,0,0,0,32,0,34,0,36,0,38,0,0,0,0,0,0,0,0,0,40,0,42,0,44,0,46,0,0,0,0,0,0,0,0,0,48,0,50,0,52,0,54,0,0,0,0,0,0,0,0,0,56,0,58,0,60,0,62,0]
def aliasMap20 : Array Nat := #[0,0,1,0,0,0,5,0,0,0,9,0,0,0,13,0,0,0,17,0,0,0,21,0,0,0,25,0,0,0,29,0,0,0,33,0,0,0,37,0,0,0,41,0,0,0,45,0,0,0,49,0,0,0,53,0,0,0,57,0,0,0,61,0]
def aliasMap21 : Array Nat := #[0,0,1,0,0,0,5,0,0,0,3,0,0,0,7,0,0,0,9,0,0,0,13,0,0,0,11,0,0,0,15,0,0,0,17,0,0,0,21,0,0,0,19,0,0,0,23,0,0,0,25,0,0,0,29,0,0,0,27,0,0,0,31,0]
def aliasMap22 : Array Nat := #[0,0,0,0,0,0,0,0,8,0,9,0,12,0,13,0,0,0,0,0,0,0,0,0,24,0,25,0,28,0,29,0,0,0,0,0,0,0,0,0,40,0,41,0,44,0,45,0,0,0,0,0,0,0,0,0,56,0,57,0,60,0,61,0]
def aliasMap23 : Array Nat := #[0,0,0,0,0,0,0,0,16,0,17,0,20,0,21,0,0,0,0,0,0,0,0,0,24,0,25,0,28,0,29,0,0,0,0,0,0,0,0,0,48,0,49,0,52,0,53,0,0,0,0,0,0,0,0,0,56,0,57,0,60,0,61,0]
def aliasMap24 : Array Nat := #[0,0,0,0,0,0,0,0,32,0,33,0,36,0,37,0,0,0,0,0,0,0,0,0,40,0,41,0,44,0,45,0,0,0,0,0,0,0,0,0,48,0,49,0,52,0,53,0,0,0,0,0,0,0,0,0,56,0,57,0,60,0,61,0]
def aliasMap25 : Array Nat := #[0,0,51,0,0,0,35,0,0,0,50,0,0,0,34,0,0,0,49,0,0,0,33,0,0,0,48,0,0,0,32,0,0,0,19,0,0,0,3,0,0,0,18,0,0,0,2,0,0,0,17,0,0,0,1,0,0,0,16,0,0,0,0,0]
def aliasMap26 : Array Nat := #[0,8,0,24,0,0,0,0,0,9,0,25,0,0,0,0,0,10,0,26,0,0,0,0,0,11,0,27,0,0,0,0,0,40,0,56,0,0,0,0,0,41,0,57,0,0,0,0,0,42,0,58,0,0,0,0,0,43,0,59,0,0,0,0]
def aliasMap27 : Array Nat := #[0,16,0,24,0,0,0,0,0,17,0,25,0,0,0,0,0,18,0,26,0,0,0,0,0,19,0,27,0,0,0,0,0,48,0,56,0,0,0,0,0,49,0,57,0,0,0,0,0,50,0,58,0,0,0,0,0,51,0,59,0,0,0,0]
def aliasMap28 : Array Nat := #[4,1,12,9,0,0,0,0,20,17,28,25,0,0,0,0,36,33,44,41,0,0,0,0,52,49,60,57,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
def aliasMap29 : Array Nat := #[0,0,12,0,0,0,14,0,0,0,9,0,0,0,11,0,0,0,28,0,0,0,30,0,0,0,25,0,0,0,27,0,0,0,44,0,0,0,46,0,0,0,41,0,0,0,43,0,0,0,60,0,0,0,62,0,0,0,57,0,0,0,59,0]
def aliasMap30 : Array Nat := #[0,1,0,3,4,0,6,0,0,0,0,0,0,0,0,0,0,9,0,11,12,0,14,0,0,0,0,0,0,0,0,0,0,33,0,35,36,0,38,0,0,0,0,0,0,0,0,0,0,41,0,43,44,0,46,0,0,0,0,0,0,0,0,0]
def aliasMap31 : Array Nat := #[0,0,20,0,0,0,22,0,0,0,17,0,0,0,19,0,0,0,28,0,0,0,30,0,0,0,25,0,0,0,27,0,0,0,52,0,0,0,54,0,0,0,49,0,0,0,51,0,0,0,60,0,0,0,62,0,0,0,57,0,0,0,59,0]
def aliasMap32 : Array Nat := #[0,29,0,21,0,0,0,0,0,60,0,52,0,0,0,0,0,25,0,17,0,0,0,0,0,56,0,48,0,0,0,0,0,13,0,5,0,0,0,0,0,44,0,36,0,0,0,0,0,9,0,1,0,0,0,0,0,40,0,32,0,0,0,0]
def aliasMap33 : Array Nat := #[32,40,48,56,34,42,50,58,0,0,0,0,0,0,0,0,1,9,17,25,3,11,19,27,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
def aliasMap34 : Array Nat := #[0,1,0,3,0,5,0,7,32,0,34,0,36,0,38,0,0,17,0,19,0,21,0,23,48,0,50,0,52,0,54,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
def aliasMap35 : Array Nat := #[0,0,40,0,0,0,42,0,0,0,9,0,0,0,11,0,0,0,44,0,0,0,46,0,0,0,13,0,0,0,15,0,0,0,56,0,0,0,58,0,0,0,25,0,0,0,27,0,0,0,60,0,0,0,62,0,0,0,29,0,0,0,31,0]
def aliasMap36 : Array Nat := #[0,1,0,3,0,5,0,7,32,0,34,0,36,0,38,0,0,9,0,11,0,13,0,15,40,0,42,0,44,0,46,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
def aliasMap37 : Array Nat := #[0,0,48,0,0,0,50,0,0,0,17,0,0,0,19,0,0,0,52,0,0,0,54,0,0,0,21,0,0,0,23,0,0,0,56,0,0,0,58,0,0,0,25,0,0,0,27,0,0,0,60,0,0,0,62,0,0,0,29,0,0,0,31,0]
def aliasMap38 : Array Nat := #[4,2,12,10,0,0,0,0,20,18,28,26,0,0,0,0,36,34,44,42,0,0,0,0,52,50,60,58,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
def aliasMap39 : Array Nat := #[0,0,2,0,4,0,6,0,0,17,0,19,0,21,0,23,8,0,10,0,12,0,14,0,0,25,0,27,0,29,0,31,32,0,34,0,36,0,38,0,0,49,0,51,0,53,0,55,40,0,42,0,44,0,46,0,0,57,0,59,0,61,0,63]
def aliasMap40 : Array Nat := #[0,0,1,0,4,0,5,0,0,10,0,11,0,14,0,15,16,0,17,0,20,0,21,0,0,26,0,27,0,30,0,31,32,0,33,0,36,0,37,0,0,42,0,43,0,46,0,47,48,0,49,0,52,0,53,0,0,58,0,59,0,62,0,63]
def aliasMap41 : Array Nat := #[0,0,1,0,4,0,5,0,0,18,0,19,0,22,0,23,8,0,9,0,12,0,13,0,0,26,0,27,0,30,0,31,32,0,33,0,36,0,37,0,0,50,0,51,0,54,0,55,40,0,41,0,44,0,45,0,0,58,0,59,0,62,0,63]
def aliasMap42 : Array Nat := #[0,1,2,3,0,0,0,0,0,0,0,0,20,21,22,23,8,9,10,11,0,0,0,0,0,0,0,0,28,29,30,31,32,33,34,35,0,0,0,0,0,0,0,0,52,53,54,55,40,41,42,43,0,0,0,0,0,0,0,0,60,61,62,63]
def aliasMap43 : Array Nat := #[0,1,2,3,4,5,6,7,0,0,0,0,0,0,0,0,8,9,10,11,12,13,14,15,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,48,49,50,51,52,53,54,55,0,0,0,0,0,0,0,0,56,57,58,59,60,61,62,63]
def aliasMap44 : Array Nat := #[0,0,1,0,4,0,5,0,8,0,9,0,12,0,13,0,16,0,17,0,20,0,21,0,24,0,25,0,28,0,29,0,32,0,33,0,36,0,37,0,40,0,41,0,44,0,45,0,48,0,49,0,52,0,53,0,56,0,57,0,60,0,61,0]
def aliasMap45 : Array Nat := #[0,2,0,3,0,6,0,7,0,10,0,11,0,14,0,15,0,18,0,19,0,22,0,23,0,26,0,27,0,30,0,31,0,34,0,35,0,38,0,39,0,42,0,43,0,46,0,47,0,50,0,51,0,54,0,55,0,58,0,59,0,62,0,63]
def aliasMap46 : Array Nat := #[0,1,2,3,4,5,6,7,0,0,0,0,0,0,0,0,8,9,10,11,12,13,14,15,0,0,0,0,0,0,0,0,32,33,34,35,36,37,38,39,0,0,0,0,0,0,0,0,40,41,42,43,44,45,46,47,0,0,0,0,0,0,0,0]
def aliasMap47 : Array Nat := #[0,0,0,0,0,0,0,0,16,17,18,19,20,21,22,23,0,0,0,0,0,0,0,0,24,25,26,27,28,29,30,31,0,0,0,0,0,0,0,0,48,49,50,51,52,53,54,55,0,0,0,0,0,0,0,0,56,57,58,59,60,61,62,63]
def aliasMap48 : Array Nat := #[0,2,0,3,4,0,5,0,0,10,0,11,12,0,13,0,0,18,0,19,20,0,21,0,0,26,0,27,28,0,29,0,0,34,0,35,36,0,37,0,0,42,0,43,44,0,45,0,0,50,0,51,52,0,53,0,0,58,0,59,60,0,61,0]
def aliasMap49 : Array Nat := #[0,2,0,3,0,6,0,7,0,10,0,11,0,14,0,15,0,18,0,19,0,22,0,23,0,26,0,27,0,30,0,31,32,0,33,0,36,0,37,0,40,0,41,0,44,0,45,0,48,0,49,0,52,0,53,0,56,0,57,0,60,0,61,0]
def rootAliases : QFast.AliasTable
  | 1 => some (0, aliasMap0)
  | 2 => some (0, aliasMap1)
  | 3 => some (0, aliasMap2)
  | 4 => some (0, aliasMap3)
  | 5 => some (0, aliasMap4)
  | 6 => some (0, aliasMap5)
  | 8 => some (7, aliasMap6)
  | 10 => some (9, aliasMap7)
  | 11 => some (9, aliasMap8)
  | 13 => some (12, aliasMap9)
  | 14 => some (12, aliasMap10)
  | 16 => some (15, aliasMap11)
  | 18 => some (17, aliasMap12)
  | 19 => some (15, aliasMap13)
  | 20 => some (12, aliasMap14)
  | 21 => some (12, aliasMap15)
  | 22 => some (12, aliasMap16)
  | 23 => some (12, aliasMap17)
  | 24 => some (7, aliasMap18)
  | 25 => some (7, aliasMap19)
  | 26 => some (17, aliasMap20)
  | 27 => some (17, aliasMap21)
  | 28 => some (7, aliasMap22)
  | 29 => some (7, aliasMap23)
  | 30 => some (7, aliasMap24)
  | 31 => some (17, aliasMap25)
  | 32 => some (15, aliasMap26)
  | 33 => some (15, aliasMap27)
  | 34 => some (12, aliasMap28)
  | 36 => some (17, aliasMap29)
  | 37 => some (35, aliasMap30)
  | 38 => some (17, aliasMap31)
  | 42 => some (15, aliasMap32)
  | 43 => some (9, aliasMap33)
  | 44 => some (41, aliasMap34)
  | 45 => some (17, aliasMap35)
  | 46 => some (41, aliasMap36)
  | 47 => some (17, aliasMap37)
  | 48 => some (12, aliasMap38)
  | 50 => some (49, aliasMap39)
  | 51 => some (49, aliasMap40)
  | 52 => some (49, aliasMap41)
  | 54 => some (53, aliasMap42)
  | 57 => some (56, aliasMap43)
  | 60 => some (58, aliasMap44)
  | 61 => some (59, aliasMap45)
  | 65 => some (63, aliasMap46)
  | 66 => some (64, aliasMap47)
  | 71 => some (69, aliasMap48)
  | 72 => some (70, aliasMap49)
  | _ => none
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockRoots_0 : QFast.passBlock (QFast.symCheckRoot rootAliases fastViews fastNodes) 0 27 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockRoots_27 : QFast.passBlock (QFast.symCheckRoot rootAliases fastViews fastNodes) 27 25 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockRoots_52 : QFast.passBlock (QFast.symCheckRoot rootAliases fastViews fastNodes) 52 11 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockRoots_63 : QFast.passBlock (QFast.symCheckRoot rootAliases fastViews fastNodes) 63 10 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockRoots_73 : QFast.passBlock (QFast.symCheckRoot rootAliases fastViews fastNodes) 73 1 = true := by decide +kernel
theorem joinRoots_0_0 : QFast.passBlock (QFast.symCheckRoot rootAliases fastViews fastNodes) 0 52 = true :=
  @QFast.merge_blocks (QFast.symCheckRoot rootAliases fastViews fastNodes) 0 27 25 blockRoots_0 blockRoots_27
theorem joinRoots_0_52 : QFast.passBlock (QFast.symCheckRoot rootAliases fastViews fastNodes) 52 21 = true :=
  @QFast.merge_blocks (QFast.symCheckRoot rootAliases fastViews fastNodes) 52 11 10 blockRoots_52 blockRoots_63
theorem joinRoots_1_0 : QFast.passBlock (QFast.symCheckRoot rootAliases fastViews fastNodes) 0 73 = true :=
  @QFast.merge_blocks (QFast.symCheckRoot rootAliases fastViews fastNodes) 0 52 21 joinRoots_0_0 joinRoots_0_52
theorem joinRoots_2_0 : QFast.passBlock (QFast.symCheckRoot rootAliases fastViews fastNodes) 0 74 = true :=
  @QFast.merge_blocks (QFast.symCheckRoot rootAliases fastViews fastNodes) 0 73 1 joinRoots_1_0 blockRoots_73
theorem certifiedRoots : QFast.passBlock (QFast.symCheckRoot rootAliases fastViews fastNodes) 0 74 = true := joinRoots_2_0
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockNodes_0 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 0 64 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockNodes_64 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 64 54 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockNodes_118 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 118 64 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockNodes_182 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 182 44 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockNodes_226 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 226 31 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockNodes_257 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 257 39 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockNodes_296 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 296 39 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockNodes_335 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 335 59 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockNodes_394 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 394 36 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockNodes_430 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 430 11 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockNodes_441 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 441 14 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockNodes_455 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 455 17 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockNodes_472 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 472 25 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockNodes_497 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 497 26 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockNodes_523 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 523 7 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockNodes_530 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 530 7 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockNodes_537 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 537 7 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockNodes_544 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 544 7 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockNodes_551 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 551 7 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockNodes_558 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 558 16 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockNodes_574 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 574 8 = true := by decide +kernel
theorem joinNodes_0_0 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 0 118 = true :=
  @QFast.merge_blocks (QFast.checkNodeAt fastViews fastNodes) 0 64 54 blockNodes_0 blockNodes_64
theorem joinNodes_0_118 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 118 108 = true :=
  @QFast.merge_blocks (QFast.checkNodeAt fastViews fastNodes) 118 64 44 blockNodes_118 blockNodes_182
theorem joinNodes_0_226 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 226 70 = true :=
  @QFast.merge_blocks (QFast.checkNodeAt fastViews fastNodes) 226 31 39 blockNodes_226 blockNodes_257
theorem joinNodes_0_296 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 296 98 = true :=
  @QFast.merge_blocks (QFast.checkNodeAt fastViews fastNodes) 296 39 59 blockNodes_296 blockNodes_335
theorem joinNodes_0_394 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 394 47 = true :=
  @QFast.merge_blocks (QFast.checkNodeAt fastViews fastNodes) 394 36 11 blockNodes_394 blockNodes_430
theorem joinNodes_0_441 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 441 31 = true :=
  @QFast.merge_blocks (QFast.checkNodeAt fastViews fastNodes) 441 14 17 blockNodes_441 blockNodes_455
theorem joinNodes_0_472 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 472 51 = true :=
  @QFast.merge_blocks (QFast.checkNodeAt fastViews fastNodes) 472 25 26 blockNodes_472 blockNodes_497
theorem joinNodes_0_523 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 523 14 = true :=
  @QFast.merge_blocks (QFast.checkNodeAt fastViews fastNodes) 523 7 7 blockNodes_523 blockNodes_530
theorem joinNodes_0_537 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 537 14 = true :=
  @QFast.merge_blocks (QFast.checkNodeAt fastViews fastNodes) 537 7 7 blockNodes_537 blockNodes_544
theorem joinNodes_0_551 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 551 23 = true :=
  @QFast.merge_blocks (QFast.checkNodeAt fastViews fastNodes) 551 7 16 blockNodes_551 blockNodes_558
theorem joinNodes_1_0 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 0 226 = true :=
  @QFast.merge_blocks (QFast.checkNodeAt fastViews fastNodes) 0 118 108 joinNodes_0_0 joinNodes_0_118
theorem joinNodes_1_226 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 226 168 = true :=
  @QFast.merge_blocks (QFast.checkNodeAt fastViews fastNodes) 226 70 98 joinNodes_0_226 joinNodes_0_296
theorem joinNodes_1_394 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 394 78 = true :=
  @QFast.merge_blocks (QFast.checkNodeAt fastViews fastNodes) 394 47 31 joinNodes_0_394 joinNodes_0_441
theorem joinNodes_1_472 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 472 65 = true :=
  @QFast.merge_blocks (QFast.checkNodeAt fastViews fastNodes) 472 51 14 joinNodes_0_472 joinNodes_0_523
theorem joinNodes_1_537 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 537 37 = true :=
  @QFast.merge_blocks (QFast.checkNodeAt fastViews fastNodes) 537 14 23 joinNodes_0_537 joinNodes_0_551
theorem joinNodes_2_0 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 0 394 = true :=
  @QFast.merge_blocks (QFast.checkNodeAt fastViews fastNodes) 0 226 168 joinNodes_1_0 joinNodes_1_226
theorem joinNodes_2_394 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 394 143 = true :=
  @QFast.merge_blocks (QFast.checkNodeAt fastViews fastNodes) 394 78 65 joinNodes_1_394 joinNodes_1_472
theorem joinNodes_2_537 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 537 45 = true :=
  @QFast.merge_blocks (QFast.checkNodeAt fastViews fastNodes) 537 37 8 joinNodes_1_537 blockNodes_574
theorem joinNodes_3_0 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 0 537 = true :=
  @QFast.merge_blocks (QFast.checkNodeAt fastViews fastNodes) 0 394 143 joinNodes_2_0 joinNodes_2_394
theorem joinNodes_4_0 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 0 582 = true :=
  @QFast.merge_blocks (QFast.checkNodeAt fastViews fastNodes) 0 537 45 joinNodes_3_0 joinNodes_2_537
theorem certifiedNodes : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 0 582 = true := joinNodes_4_0
end SignedProjection

namespace SignedProjection
def bMatches (z : Option View) : Bool :=
  match z with
  | none => false
  | some v => vg v == (0xfeeeeee0eee8e8e0 : Word) && vk v == 10 && (vs v).toFinset == Direct64.cols.toFinset

theorem rootNegative : ¬ CoreSigned.build signedOps (0xfeeeeee0eee8e8e0 : BitVec 64) 10 Direct64.cols.toFinset := by
  have shape : bMatches (QFast.get fastViews 73) = true := by decide +kernel
  cases ev : QFast.get fastViews 73 with
  | none => simp [ev, bMatches] at shape
  | some v =>
    have valid := QFast.symCertified rootAliases fastViews fastNodes certifiedRoots certifiedNodes ev
    simp only [ev,bMatches,Bool.and_eq_true,beq_iff_eq] at shape
    change ¬ CoreSigned.build signedOps (vg v) (vk v) (vs v).toFinset at valid
    rwa [shape.1.1,shape.1.2,shape.2] at valid
end SignedProjection

end PEqualNP.Outside.L_meta_44726_aux

open PEqualNP.Outside.L_meta_44726_aux in
theorem PEqualNP.Outside.L_meta_44726 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4277071584 * 2 ^ 32 + 4008241376) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4277071584 * 2 ^ 32 + 4008241376) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  LowerSymSix.finish SignedProjection.rootNegative
