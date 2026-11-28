import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_38647

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

abbrev W := BitVec 128

def ops (x y : W) : List W := [x &&& y, x ||| y, x &&& ~~~y, y &&& ~~~x]
def sep (x : W) : BitVec 64 := ((x >>> 64) ^^^ x).setWidth 64
def cuts (ws : List W) : BitVec 64 := ws.foldr (fun w v => sep w ||| v) 0
def goal : W := (-1 : BitVec 64) ++ (0 : BitVec 64)
def singles {α : Type} : List α → List (α × List α)
  | [] => []
  | a :: rest => (a, rest) :: (singles rest).map (fun (b, bs) => (b, a :: bs))

def pairs {α : Type} : List α → List (α × α × List α)
  | [] => []
  | a :: rest => (singles rest).map (fun (b, bs) => (a, b, bs)) ++
      (pairs rest).map (fun (b, c, bs) => (b, c, a :: bs))

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

abbrev basicOps (a b : W) : Finset W := (ops a b).toFinset

def differs (i : Fin 64) (w : W) : Prop :=
  w.getLsbD (64+i.val) ≠ w.getLsbD i.val

theorem ops_differs (i : Fin 64) (a b : W) (z : W) (hz : z ∈ basicOps a b)
    (hd : differs i z) : differs i a ∨ differs i b := by
  simp only [basicOps, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hz
  by_contra! fail
  obtain ⟨ha,hb⟩ := fail
  apply hd
  unfold differs at ha hb
  simp only [not_not] at ha hb
  have hi : 64+i.val < 128 := by omega
  have hi' : i.val < 128 := by omega
  rcases hz with rfl | rfl | rfl | rfl <;>
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_not, hi, hi', decide_true,
      Bool.true_and, ha, hb]

theorem cuts_spec (ws : List W) (i : Fin 64) :
    (cuts ws).getLsbD i.val = true ↔ ∃ w ∈ ws, differs i w := by
  induction ws with
  | nil => simp [cuts]
  | cons a rest ih =>
    change (sep a ||| cuts rest).getLsbD i.val = true ↔ _
    rw [BitVec.getLsbD_or, Bool.or_eq_true, ih]
    have bx (p q : Bool) : Bool.xor p q = true ↔ p ≠ q := by cases p <;> cases q <;> decide
    simp [sep, i.isLt, differs, Nat.add_comm, bx]

theorem cuts_full {g : W} (hg : g = goal ∨ g = ~~~goal) {k : ℕ} {ws : List W}
    (h : live basicOps g k ws.toFinset) : cuts ws = -1 := by
  have hd : ∀ i, differs i g := by rcases hg with rfl | rfl <;> unfold differs <;> decide +kernel
  apply BitVec.eq_of_getElem_eq
  intro j hj
  have hw := live_separates (differs ⟨j, hj⟩) (hd ⟨j,hj⟩) (ops_differs ⟨j, hj⟩) h
  have hbit := (cuts_spec ws ⟨j, hj⟩).mpr (by simpa using hw)
  change (cuts ws)[j] = (BitVec.allOnes 64)[j]
  rw [BitVec.getElem_allOnes]
  simpa only [BitVec.getLsbD_eq_getElem hj] using hbit

theorem ops_swap (a b : W) : basicOps a b = basicOps b a := by
  ext z
  simp only [basicOps, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false]
  rw [BitVec.and_comm a b, BitVec.or_comm a b]
  tauto

def keepChoices (a b : W) (r : List W) : List (List W) := [r, a :: r, b :: r, a :: b :: r]

theorem recover_kept {ws r : List W} {a b : W} {needed : Finset W}
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

theorem singleton_list {goal : W} {ws : List W} (hn : ws.Nodup) (hs : ws.toFinset = {goal}) : ws = [goal] := by
  have hc := List.toFinset_card_of_nodup hn
  rw [hs] at hc
  cases ws with
  | nil => simp at hc
  | cons w ws =>
    cases ws with
    | nil => simpa using hs
    | cons => simp at hc

def insertW (x : W) : List W → List W
  | [] => [x]
  | y :: ys => if x.toNat ≤ y.toNat then x :: y :: ys else y :: insertW x ys

def canon : List W → List W
  | [] => []
  | x :: xs => insertW x (canon xs)

theorem insertW_perm (x : W) : ∀ l : List W, (insertW x l).Perm (x :: l)
  | [] => List.Perm.refl _
  | y :: ys => by
    unfold insertW
    split
    · exact List.Perm.refl _
    · exact ((insertW_perm x ys).cons y).trans (List.Perm.swap _ _ _)

theorem canon_perm : ∀ l : List W, (canon l).Perm l
  | [] => List.Perm.refl _
  | x :: xs => (insertW_perm x (canon xs)).trans ((canon_perm xs).cons x)

def dispatch (extra : ℕ) (next : ℕ → List W → Bool) (a b : W) (r : List W) : Bool :=
  let base := cuts r
  (ops a b).any fun w =>
    let v := sep w ||| base
    ((v == -1) && next extra (w :: r)) ||
    ((extra != 0) && (((v ||| sep a == -1) && next (extra - 1) (w :: a :: r)) ||
                       ((v ||| sep b == -1) && next (extra - 1) (w :: b :: r)))) ||
    ((extra ≥ 2) && (v ||| sep a ||| sep b == -1) && next (extra - 2) (w :: a :: b :: r))

def optimized : ℕ → ℕ → List W → Bool
  | 0, _, ws => (ws == [goal] || ws == [~~~goal])
  | k + 1, extra, ws => (ws == [goal] || ws == [~~~goal]) ||
    (pairs ws).any (fun (a, b, r) => dispatch extra (fun e l => optimized k e (canon l)) a b r)

theorem dispatch_complete {k extra : ℕ} {a b z : W} {r kept : List W}
    (next : ℕ → List W → Bool)
    (hz : z ∈ basicOps a b) (hk : kept ∈ keepChoices a b r)
    (he : extra + r.length = k) (hn : kept.length ≤ k)
    (hc : cuts (z :: kept) = -1) (ht : next (k - kept.length) (z :: kept) = true) :
    dispatch extra next a b r = true := by
  apply List.any_eq_true.mpr
  refine ⟨z, List.mem_toFinset.mp hz, ?_⟩
  simp [keepChoices] at hk
  rcases hk with rfl | rfl | rfl | rfl <;>
    simp only [cuts, List.foldr_cons] at hc ⊢ <;>
    (try simp only [List.length_cons] at *) <;>
    simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, bne_iff_ne]
  · left; left; exact ⟨hc, by convert ht using 2; omega⟩
  · left; right; exact ⟨by omega, .inl ⟨by convert hc using 1; ac_rfl, by convert ht using 2; omega⟩⟩
  · left; right; exact ⟨by omega, .inr ⟨by convert hc using 1; ac_rfl, by convert ht using 2; omega⟩⟩
  · right; exact ⟨⟨by omega, by convert hc using 1; ac_rfl⟩, by convert ht using 2; omega⟩

theorem optimized_complete {g : W} (hg : g = goal ∨ g = ~~~goal) (n : ℕ) (ws : List W) (extra : ℕ) (hn : ws.Nodup)
    (room : extra + ws.length = n + 1) (h : live basicOps g n ws.toFinset) :
    optimized n extra ws = true := by
  induction n generalizing ws extra with
  | zero => rcases hg with rfl | rfl <;> simp [optimized, singleton_list hn h]
  | succ k ih =>
    rcases first_live h with done | ⟨a, ha, b, hb, hab, z, hz, hout, needed, hs, tail⟩
    · rcases hg with rfl | rfl <;> simp [optimized, singleton_list hn done]
    · obtain ⟨r, hm, hp⟩ := pick_two (List.mem_toFinset.mp ha) (List.mem_toFinset.mp hb) hab
      have go {a b : W} (perm : ws.Perm (a :: b :: r))
          (hset : ws.toFinset = insert a (insert b needed)) (hop : z ∈ basicOps a b) :
          dispatch extra (fun e l => optimized k e (canon l)) a b r = true := by
        obtain ⟨kept, hk, hnk, hfin⟩ := recover_kept perm hn hset
        have hznew : z ∉ kept := by
          intro hu
          apply hout
          rw [hset]
          exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (hfin ▸ (List.mem_toFinset.mpr hu)))
        have hnd : (z :: kept).Nodup := List.nodup_cons.mpr ⟨hznew, hnk⟩
        have hl : live basicOps g k (z :: kept).toFinset := by
          simpa [hfin] using tail
        have hc := live_card hl
        rw [List.toFinset_card_of_nodup hnd, List.length_cons] at hc
        have len := perm.length_eq
        simp only [List.length_cons] at len
        have hcn : (canon (z :: kept)).Perm (z :: kept) := canon_perm _
        apply dispatch_complete (k := k) (extra := extra) (fun e l => optimized k e (canon l)) hop hk (by omega) (by omega) (cuts_full hg hl)
        refine ih _ _ (hcn.nodup_iff.mpr hnd) ?_ (by rw [List.toFinset_eq_of_perm _ _ hcn]; exact hl)
        rw [hcn.length_eq]; simp; omega
      simp only [optimized, Bool.or_eq_true, List.any_eq_true]
      right
      rcases hm with direct | swap
      · exact ⟨(a, b, r), direct, go hp hs hz⟩
      · exact ⟨(b, a, r), swap, go (hp.trans (.swap _ _ _)) (by rw [hs, Finset.insert_comm]) (ops_swap a b ▸ hz)⟩

def search (n : ℕ) (inputs : List W) : Bool :=
  inputs.sublists.any fun ws =>
    decide (ws.length ≤ n+1) && (cuts ws == -1) && optimized n (n+1-ws.length) (canon ws)

theorem search_complete {g : W} (hg : g = goal ∨ g = ~~~goal) (n : ℕ) (inputs : List W)
    (hn : inputs.Nodup) (h : build basicOps g n inputs.toFinset) : search n inputs = true := by
  classical
  obtain ⟨s,hs,hl⟩ := compress h
  let ws := inputs.filter (· ∈ s)
  have eq : ws.toFinset = s := by
    ext w
    simp only [ws, List.mem_toFinset, List.mem_filter, decide_eq_true_eq, and_iff_right_iff_imp]
    exact fun hw => List.mem_toFinset.mp (hs hw)
  have hnd : ws.Nodup := hn.filter _
  have hl' : live basicOps g n ws.toFinset := eq.symm ▸ hl
  have sz := live_card hl'
  rw [List.toFinset_card_of_nodup hnd] at sz
  have hcn : (canon ws).Perm ws := canon_perm ws
  have hopt : optimized n (n+1-ws.length) (canon ws) = true :=
    optimized_complete hg n (canon ws) _ (hcn.nodup_iff.mpr hnd) (by rw [hcn.length_eq]; omega) (by rw [List.toFinset_eq_of_perm _ _ hcn]; exact hl')
  exact List.any_eq_true.mpr ⟨ws,List.mem_sublists.mpr (List.filter_sublist ..),
    by simp [sz, cuts_full hg hl', hopt]⟩

def kidsOf (extra : ℕ) (a b : W) (r : List W) (w : W) : List (ℕ × List W) :=
  let v := sep w ||| cuts r
  (if v == -1 then [(extra, canon (w :: r))] else []) ++
  (if extra != 0 && (v ||| sep a == -1) then [(extra - 1, canon (w :: a :: r))] else []) ++
  (if extra != 0 && (v ||| sep b == -1) then [(extra - 1, canon (w :: b :: r))] else []) ++
  (if extra ≥ 2 && (v ||| sep a ||| sep b == -1) then [(extra - 2, canon (w :: a :: b :: r))] else [])

def children (c : ℕ × List W) : List (ℕ × List W) :=
  (pairs c.2).flatMap fun p => (ops p.1 p.2.1).flatMap fun w => kidsOf c.1 p.1 p.2.1 p.2.2 w

def goalFree (ws : List W) : Bool := !(ws == [goal] || ws == [~~~goal])

theorem dispatch_false {extra k : ℕ} {a b : W} {r : List W}
    (h : ∀ w ∈ ops a b, ∀ c ∈ kidsOf extra a b r w, optimized k c.1 c.2 = false) :
    dispatch extra (fun e l => optimized k e (canon l)) a b r = false := by
  unfold dispatch
  rw [List.any_eq_false]
  intro w hw hcon
  have h1 := h w hw
  simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, bne_iff_ne] at hcon
  rcases hcon with (⟨hv, hn⟩ | ⟨hx, (⟨hv, hn⟩ | ⟨hv, hn⟩)⟩) | ⟨⟨hx, hv⟩, hn⟩
  · have := h1 (extra, canon (w :: r)) (by simp [kidsOf, hv])
    simp_all
  · have := h1 (extra - 1, canon (w :: a :: r)) (by simp [kidsOf, hv, hx])
    simp_all
  · have := h1 (extra - 1, canon (w :: b :: r)) (by simp [kidsOf, hv, hx])
    simp_all
  · have := h1 (extra - 2, canon (w :: a :: b :: r)) (by simp [kidsOf, hv, hx])
    simp_all

theorem opt_false {k e : ℕ} {ws : List W} (hg : goalFree ws = true)
    (h : ∀ c ∈ children (e, ws), optimized k c.1 c.2 = false) :
    optimized (k + 1) e ws = false := by
  unfold optimized
  rw [Bool.or_eq_false_iff]
  refine ⟨by simpa [goalFree] using hg, ?_⟩
  rw [List.any_eq_false]
  rintro ⟨a, b, r⟩ hx hcon
  have key := dispatch_false (extra := e) (k := k) (a := a) (b := b) (r := r)
    (fun w hw c hc => h c (List.mem_flatMap.mpr ⟨(a, b, r), hx, List.mem_flatMap.mpr ⟨w, hw, hc⟩⟩))
  simp_all

def FalseAt (k : ℕ) (L : List (ℕ × List W)) : Prop := ∀ c ∈ L, optimized k c.1 c.2 = false

theorem falseAt_expand {k : ℕ} {L : List (ℕ × List W)}
    (hg : ∀ c ∈ L, goalFree c.2 = true) (h : FalseAt k (L.flatMap children)) : FalseAt (k + 1) L := by
  intro c hc
  exact opt_false (hg c hc) (fun c' hc' => h c' (List.mem_flatMap.mpr ⟨c, hc, hc'⟩))

def expandN : ℕ → List (ℕ × List W) → List (ℕ × List W)
  | 0, L => L
  | d + 1, L => expandN d (L.flatMap children)

def allGoalFree : ℕ → List (ℕ × List W) → Bool
  | 0, _ => true
  | d + 1, L => L.all (fun c => goalFree c.2) && allGoalFree d (L.flatMap children)

theorem falseAt_expandN : ∀ (d : ℕ) {j : ℕ} {L : List (ℕ × List W)},
    allGoalFree d L = true → FalseAt j (expandN d L) → FalseAt (j + d) L
  | 0, _, _, _, h => h
  | d + 1, j, L, hg, h => by
    simp only [allGoalFree, Bool.and_eq_true, List.all_eq_true] at hg
    exact falseAt_expand hg.1 (falseAt_expandN d hg.2 h)

def level0 (n : ℕ) (inputs : List W) : List (ℕ × List W) :=
  (inputs.sublists.filter (fun ws => decide (ws.length ≤ n + 1) && (cuts ws == -1))).map
    (fun ws => (n + 1 - ws.length, canon ws))

theorem search_of_false {n : ℕ} {inputs : List W} (h : FalseAt n (level0 n inputs)) :
    search n inputs = false := by
  unfold search
  rw [List.any_eq_false]
  intro ws hws hcon
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hcon
  obtain ⟨⟨hl, hc⟩, ho⟩ := hcon
  have hmem : (n + 1 - ws.length, canon ws) ∈ level0 n inputs := by
    simp only [level0, List.mem_map, List.mem_filter]
    exact ⟨ws, ⟨hws, by simp [hl, hc]⟩, rfl⟩
  have := h _ hmem
  simp_all

theorem search_false_of_chunks {n d j : ℕ} {inputs : List W} (hj : j + d = n)
    (hg : allGoalFree d (level0 n inputs) = true)
    (hl : FalseAt j (expandN d (level0 n inputs))) : search n inputs = false := by
  subst hj
  exact search_of_false (falseAt_expandN d hg hl)

def chunkOK (j : ℕ) (L : List (ℕ × List W)) : Bool := L.all fun c => !optimized j c.1 c.2

theorem falseAt_of_chunkOK {j : ℕ} {L : List (ℕ × List W)} (h : chunkOK j L = true) : FalseAt j L := by
  intro c hc
  have := List.all_eq_true.mp h c hc
  simpa using this

def hashW (acc : ℕ) (w : W) : ℕ := (acc * 31 + w.toNat) % 1000003

def hashS (nb : ℕ) (c : ℕ × List W) : ℕ := (c.2.foldl hashW c.1) % nb

def inB (bk : List (List (ℕ × List W))) (c : ℕ × List W) : Bool :=
  (bk.getD (hashS bk.length c) []).any fun x => decide (x = c)

theorem inB_mem {bk : List (List (ℕ × List W))} {c : ℕ × List W} (h : inB bk c = true) :
    c ∈ bk.flatten := by
  unfold inB at h
  rw [List.any_eq_true] at h
  obtain ⟨x, hx, hxc⟩ := h
  have hxc' : x = c := of_decide_eq_true hxc
  subst hxc'
  rw [List.mem_flatten]
  by_cases hi : hashS bk.length x < bk.length
  · exact ⟨bk.getD (hashS bk.length x) [], by simp [List.getD_eq_getElem?_getD, hi], hx⟩
  · simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (not_lt.mp hi)] at hx

def windowsF (j : ℕ) (L : List (List (ℕ × List W))) (a : ℕ) : List ℕ → Bool
  | [] => (L.drop a).isEmpty
  | s :: rest => chunkOK j ((L.drop a).take s).flatten && windowsF j L (a + s) rest

theorem falseAt_of_windowsF {j : ℕ} {L : List (List (ℕ × List W))} :
    ∀ (sizes : List ℕ) (a : ℕ), windowsF j L a sizes = true → FalseAt j (L.drop a).flatten
  | [], a, h => by
    intro c hc
    simp only [windowsF, List.isEmpty_iff] at h
    rw [h] at hc
    simp at hc
  | s :: rest, a, h => by
    simp only [windowsF, Bool.and_eq_true] at h
    have h1 := falseAt_of_chunkOK h.1
    have h2 := falseAt_of_windowsF rest (a + s) h.2
    intro c hc
    have split : L.drop a = (L.drop a).take s ++ L.drop (a + s) := by
      rw [← List.drop_drop, List.take_append_drop]
    rw [split, List.flatten_append] at hc
    rcases List.mem_append.mp hc with hc | hc
    · exact h1 c hc
    · exact h2 c hc

theorem windowsF_cons {j : ℕ} {L : List (List (ℕ × List W))} {a s : ℕ} {rest : List ℕ}
    (h1 : chunkOK j ((L.drop a).take s).flatten = true)
    (h2 : windowsF j L (a + s) rest = true) : windowsF j L a (s :: rest) = true := by
  simp [windowsF, h1, h2]

theorem windowsF_nil {j : ℕ} {L : List (List (ℕ × List W))} {a : ℕ} (h : (L.drop a).isEmpty = true) :
    windowsF j L a [] = true := h

theorem dispatch_mono {extra : ℕ} {n1 n2 : ℕ → List W → Bool} (a b : W) (r : List W)
    (h : ∀ e l, n2 e l = true → n1 e l = true) :
    dispatch extra n2 a b r = true → dispatch extra n1 a b r = true := by
  unfold dispatch
  simp only [List.any_eq_true]
  rintro ⟨w, hw, hx⟩
  refine ⟨w, hw, ?_⟩
  simp only [Bool.or_eq_true, Bool.and_eq_true] at hx ⊢
  rcases hx with (⟨hv, hn⟩ | ⟨hx1, (⟨hv, hn⟩ | ⟨hv, hn⟩)⟩) | ⟨⟨hx1, hv⟩, hn⟩
  · exact Or.inl (Or.inl ⟨hv, h _ _ hn⟩)
  · exact Or.inl (Or.inr ⟨hx1, Or.inl ⟨hv, h _ _ hn⟩⟩)
  · exact Or.inl (Or.inr ⟨hx1, Or.inr ⟨hv, h _ _ hn⟩⟩)
  · exact Or.inr ⟨⟨hx1, hv⟩, h _ _ hn⟩

def optB (S : ℕ × List W → Bool) : ℕ → ℕ → List W → Bool
  | 0, e, ws => S (e, ws)
  | k + 1, e, ws => (ws == [goal] || ws == [~~~goal]) ||
    (pairs ws).any (fun (a, b, r) => dispatch e (fun e' l => optB S k e' (canon l)) a b r)

theorem optB_sound (S : ℕ × List W → Bool) (J : ℕ)
    (hS : ∀ c, S c = false → optimized J c.1 c.2 = false) :
    ∀ (k e : ℕ) (ws : List W), optB S k e ws = false → optimized (J + k) e ws = false
  | 0, e, ws, h => hS (e, ws) h
  | k + 1, e, ws, h => by
    have ih := optB_sound S J hS k
    unfold optB at h
    rw [Bool.or_eq_false_iff] at h
    show optimized ((J + k) + 1) e ws = false
    unfold optimized
    rw [Bool.or_eq_false_iff]
    refine ⟨h.1, ?_⟩
    have h2 := h.2
    rw [List.any_eq_false] at h2 ⊢
    rintro ⟨a, b, r⟩ hp hcon
    apply h2 (a, b, r) hp
    refine dispatch_mono a b r ?_ hcon
    intro e' l hl
    by_contra hne
    have hf : optB S k e' (canon l) = false := by simpa using hne
    have := ih e' (canon l) hf
    simp_all

def chunkB (S : ℕ × List W → Bool) (d : ℕ) (L : List (ℕ × List W)) : Bool :=
  L.all fun c => !optB S d c.1 c.2

def windowsG (f : List (ℕ × List W) → Bool) (L : List (ℕ × List W)) (a : ℕ) : List ℕ → Bool
  | [] => (L.drop a).isEmpty
  | s :: rest => f ((L.drop a).take s) && windowsG f L (a + s) rest

theorem windowsG_sound {f : List (ℕ × List W) → Bool} {P : ℕ × List W → Prop}
    (hf : ∀ X, f X = true → ∀ c ∈ X, P c) {L : List (ℕ × List W)} :
    ∀ (sizes : List ℕ) (a : ℕ), windowsG f L a sizes = true → ∀ c ∈ L.drop a, P c
  | [], a, h => by
    intro c hc
    simp only [windowsG, List.isEmpty_iff] at h
    rw [h] at hc
    simp at hc
  | s :: rest, a, h => by
    simp only [windowsG, Bool.and_eq_true] at h
    have h1 := hf _ h.1
    have h2 := windowsG_sound hf rest (a + s) h.2
    intro c hc
    have split : L.drop a = (L.drop a).take s ++ L.drop (a + s) := by
      rw [← List.drop_drop, List.take_append_drop]
    rw [split] at hc
    rcases List.mem_append.mp hc with hc | hc
    · exact h1 c hc
    · exact h2 c hc

theorem windowsG_cons {f : List (ℕ × List W) → Bool} {L : List (ℕ × List W)} {a s : ℕ} {rest : List ℕ}
    (h1 : f ((L.drop a).take s) = true) (h2 : windowsG f L (a + s) rest = true) :
    windowsG f L a (s :: rest) = true := by
  simp [windowsG, h1, h2]

theorem windowsG_nil {f : List (ℕ × List W) → Bool} {L : List (ℕ × List W)} {a : ℕ}
    (h : (L.drop a).isEmpty = true) : windowsG f L a [] = true := h

theorem search_false_B {n dp J d : ℕ} {inputs : List W} {bk : List (List (ℕ × List W))} {sa sb : List ℕ}
    (hj : J + d + dp = n)
    (hg : allGoalFree dp (level0 n inputs) = true)
    (hB : windowsF J bk 0 sb = true)
    (hA : windowsG (chunkB (fun c => !inB bk c) d) (expandN dp (level0 n inputs)) 0 sa = true) :
    search n inputs = false := by
  have hBF : FalseAt J bk.flatten := by
    have := falseAt_of_windowsF sb 0 hB
    simpa using this
  have hS : ∀ c, (fun c => !inB bk c) c = false → optimized J c.1 c.2 = false := by
    intro c hc
    have hin : inB bk c = true := by simpa using hc
    exact hBF c (inB_mem hin)
  have hP : ∀ c ∈ (expandN dp (level0 n inputs)).drop 0, optB (fun c => !inB bk c) d c.1 c.2 = false := by
    refine windowsG_sound (P := fun c => optB (fun c => !inB bk c) d c.1 c.2 = false) ?_ sa 0 hA
    intro X hX c hc
    have := List.all_eq_true.mp hX c hc
    simpa using this
  have hF : FalseAt (J + d) (expandN dp (level0 n inputs)) := by
    intro c hc
    exact optB_sound _ J hS d c.1 c.2 (hP c (by simpa using hc))
  exact search_false_of_chunks (j := J + d) (d := dp) hj hg hF

theorem getD_mem_or_nil {α : Type} (l : List (List α)) (i : ℕ) :
    l.getD i [] ∈ l ∨ l.getD i [] = [] := by
  by_cases hi : i < l.length
  · left
    simp [List.getD_eq_getElem?_getD, hi]
  · right
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (not_lt.mp hi)]

def inB2 (g nb : ℕ) (bk2 : List (List (List (ℕ × List W)))) (c : ℕ × List W) : Bool :=
  ((bk2.getD (hashS nb c / g) []).getD (hashS nb c % g) []).any fun x => decide (x = c)

theorem inB2_mem {g nb : ℕ} {bk2 : List (List (List (ℕ × List W)))} {c : ℕ × List W}
    (h : inB2 g nb bk2 c = true) : c ∈ bk2.flatten.flatten := by
  unfold inB2 at h
  rw [List.any_eq_true] at h
  obtain ⟨x, hx, hxc⟩ := h
  have hxc' : x = c := of_decide_eq_true hxc
  subst hxc'
  have hG := getD_mem_or_nil bk2 (hashS nb x / g)
  have hB := getD_mem_or_nil (bk2.getD (hashS nb x / g) []) (hashS nb x % g)
  rw [List.mem_flatten]
  rcases hB with hB | hB
  · rcases hG with hG | hG
    · exact ⟨_, List.mem_flatten.mpr ⟨_, hG, hB⟩, hx⟩
    · rw [hG] at hB
      simp at hB
  · rw [hB] at hx
    simp at hx

theorem search_false_B2 {n dp J d g nb : ℕ} {inputs : List W} {bk2 : List (List (List (ℕ × List W)))} {sa sb : List ℕ}
    (hj : J + d + dp = n)
    (hg : allGoalFree dp (level0 n inputs) = true)
    (hB : windowsF J bk2.flatten 0 sb = true)
    (hA : windowsG (chunkB (fun c => !inB2 g nb bk2 c) d) (expandN dp (level0 n inputs)) 0 sa = true) :
    search n inputs = false := by
  have hBF : FalseAt J bk2.flatten.flatten := by
    have := falseAt_of_windowsF sb 0 hB
    simpa using this
  have hS : ∀ c, (fun c => !inB2 g nb bk2 c) c = false → optimized J c.1 c.2 = false := by
    intro c hc
    have hin : inB2 g nb bk2 c = true := by simpa using hc
    exact hBF c (inB2_mem hin)
  have hP : ∀ c ∈ (expandN dp (level0 n inputs)).drop 0, optB (fun c => !inB2 g nb bk2 c) d c.1 c.2 = false := by
    refine windowsG_sound (P := fun c => optB (fun c => !inB2 g nb bk2 c) d c.1 c.2 = false) ?_ sa 0 hA
    intro X hX c hc
    have := List.all_eq_true.mp hX c hc
    simpa using this
  have hF : FalseAt (J + d) (expandN dp (level0 n inputs)) := by
    intro c hc
    exact optB_sound _ J hS d c.1 c.2 (hP c (by simpa using hc))
  exact search_false_of_chunks (j := J + d) (d := dp) hj hg hF

theorem search_false_C2 {n dp J d g1 nb1 g2 nb2 : ℕ} {inputs : List W}
    {bkA bkB : List (List (List (ℕ × List W)))} {sa sb sc : List ℕ}
    (hj : J + 1 + d + dp = n)
    (hg : allGoalFree dp (level0 n inputs) = true)
    (hC : windowsF J bkB.flatten 0 sc = true)
    (hB : windowsG (chunkB (fun c => !inB2 g2 nb2 bkB c) 1) bkA.flatten.flatten 0 sb = true)
    (hA : windowsG (chunkB (fun c => !inB2 g1 nb1 bkA c) d) (expandN dp (level0 n inputs)) 0 sa = true) :
    search n inputs = false := by
  have hCF : FalseAt J bkB.flatten.flatten := by
    have := falseAt_of_windowsF sc 0 hC
    simpa using this
  have hS2 : ∀ c, (fun c => !inB2 g2 nb2 bkB c) c = false → optimized J c.1 c.2 = false := by
    intro c hc
    have hin : inB2 g2 nb2 bkB c = true := by simpa using hc
    exact hCF c (inB2_mem hin)
  have hP2 : ∀ c ∈ bkA.flatten.flatten, optimized (J + 1) c.1 c.2 = false := by
    have h1 : ∀ c ∈ (bkA.flatten.flatten).drop 0, optB (fun c => !inB2 g2 nb2 bkB c) 1 c.1 c.2 = false := by
      refine windowsG_sound (P := fun c => optB (fun c => !inB2 g2 nb2 bkB c) 1 c.1 c.2 = false) ?_ sb 0 hB
      intro X hX c hc
      have := List.all_eq_true.mp hX c hc
      simpa using this
    intro c hc
    exact optB_sound _ J hS2 1 c.1 c.2 (h1 c (by simpa using hc))
  have hS1 : ∀ c, (fun c => !inB2 g1 nb1 bkA c) c = false → optimized (J + 1) c.1 c.2 = false := by
    intro c hc
    have hin : inB2 g1 nb1 bkA c = true := by simpa using hc
    exact hP2 c (inB2_mem hin)
  have hP : ∀ c ∈ (expandN dp (level0 n inputs)).drop 0, optB (fun c => !inB2 g1 nb1 bkA c) d c.1 c.2 = false := by
    refine windowsG_sound (P := fun c => optB (fun c => !inB2 g1 nb1 bkA c) d c.1 c.2 = false) ?_ sa 0 hA
    intro X hX c hc
    have := List.all_eq_true.mp hX c hc
    simpa using this
  have hF : FalseAt (J + 1 + d) (expandN dp (level0 n inputs)) := by
    intro c hc
    exact optB_sound _ (J + 1) hS1 d c.1 c.2 (hP c (by simpa using hc))
  exact search_false_of_chunks (j := J + 1 + d) (d := dp) hj hg hF

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def holds (av : Finset W) (z : W) : Prop :=
  z = 0 ∨ z = ~~~0 ∨ ∃ a ∈ av, z = a ∨ z = ~~~a

theorem holds_insert {av : Finset W} {z a : W} (h : holds av z) : holds (insert a av) z := by
  rcases h with h|h|⟨u,hu,he⟩
  · exact .inl h
  · exact .inr (.inl h)
  · exact .inr (.inr ⟨u,Finset.mem_insert_of_mem hu,he⟩)

theorem holds_not {av : Finset W} {z : W} (h : holds av z) : holds av (~~~z) := by
  rcases h with rfl|rfl|⟨a,ha,he⟩
  · exact .inr (.inl rfl)
  · exact .inl BitVec.not_not
  · rcases he with he|he <;> rw [he]
    · exact .inr (.inr ⟨a, ha, .inr rfl⟩)
    · exact .inr (.inr ⟨a, ha, .inl BitVec.not_not⟩)

def reachable (av : Finset W) (z : W) : Prop :=
  holds av z ∨ ∃ a ∈ av, ∃ b ∈ av, a ≠ b ∧ ∃ w ∈ basicOps a b, holds (insert w av) z

theorem reachable_not {av : Finset W} {z : W} (h : reachable av z) : reachable av (~~~z) := by
  rcases h with h|⟨a,ha,b,hb,ne,w,hop,hw⟩
  · exact .inl (holds_not h)
  · exact .inr ⟨a,ha,b,hb,ne,w,hop,holds_not hw⟩

set_option maxRecDepth 5000 in
theorem and_reach {av : Finset W} {x y : W} (hx : holds av x) (hy : holds av y) :
    reachable av (x &&& y) := by
  have const : holds av (0 : W) := .inl rfl
  have oldx := hx
  rcases hx with rfl|rfl|⟨a,ha,ea⟩
  · rw [show (0 : W) &&& y = 0 from BitVec.zero_and]; exact .inl const
  · change reachable av (BitVec.allOnes 128 &&& y)
    rw [BitVec.allOnes_and]; exact .inl hy
  rcases hy with rfl|rfl|⟨b,hb,eb⟩
  · rw [show x &&& (0 : W) = 0 from BitVec.and_zero]; exact .inl const
  · change reachable av (x &&& BitVec.allOnes 128)
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
  · exact add _ (by simp [basicOps,ops] : a &&& b ∈ basicOps a b) _ (.inl rfl)
  · exact add _ (by simp [basicOps,ops] : a &&& ~~~b ∈ basicOps a b) _ (.inl rfl)
  · exact add _ (by simp [basicOps,ops] : b &&& ~~~a ∈ basicOps a b) _ (.inl (BitVec.and_comm ..))
  · exact add _ (by simp [basicOps,ops] : a ||| b ∈ basicOps a b) _ (.inr BitVec.not_or.symm)

theorem or_reach {av : Finset W} {x y : W} (hx : holds av x) (hy : holds av y) :
    reachable av (x ||| y) := by
  simpa only [BitVec.not_and, BitVec.not_not] using reachable_not (and_reach (holds_not hx) (holds_not hy))

private def bit (k : Fin 128) (z : W) : Bool := z[k.val]
private def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private theorem read_bit (w : List W) (i : ℕ) (k : Fin 128) :
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

set_option maxRecDepth 5000 in
theorem action_spec (w : List W) (g : Gate) (hg : legal g) (k : Fin 128) :
    step (w.map (bit k)) g = (w ++ [action w g]).map (bit k) := by
  obtain ⟨op,args⟩ := g
  obtain ⟨hop,cap⟩ := hg
  change op = .and ∨ op = .or ∨ op = .not at hop
  change args.length ≤ 2 at cap
  rcases args with _|⟨i,_|⟨j,_|⟨u,tail⟩⟩⟩ <;> simp at cap
  all_goals have bit0 : (0 : W)[k.val] = false := by change (0#128)[k.val] = false; simp
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

theorem available_read {av : Finset W} {w : List W} (hw : ∀ u ∈ w, holds av u) (i : ℕ) :
    holds av (w.getD i 0) := by
  by_cases h : i < w.length
  · exact hw _ (by simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h])
  · rw [List.getD_eq_default _ _ (Nat.le_of_not_gt h)]
    exact .inl rfl

set_option maxRecDepth 5000 in
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

set_option maxRecDepth 4000 in
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

def target (x : Fin 6 → Bool) : Bool :=
  Nat.testBit (4276808362 * 2 ^ 32 + 4007717536) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

theorem bound_from_search (inputs : List W) (width : inputs.length = 6)
    (nd : inputs.Nodup) (reject : search 8 inputs = false)
    (sample : ∀ k : Fin 128,
      target (fun i => (inputs.getD i.val 0)[k.val]) = (~~~goal)[k.val])
    (gs : List Gate) (o : ℕ) (hg : ∀ g ∈ gs, legal g)
    (he : ∀ x : Fin 6 → Bool, Circuit.eval ⟨gs,o⟩ (List.ofFn x) = target x) :
    8 < binaryCost gs := by
  by_contra! low
  have init : ∀ u ∈ inputs, holds inputs.toFinset u := by
    intro u hu
    exact .inr (.inr ⟨u, List.mem_toFinset.mpr hu, .inl rfl⟩)
  have evaluate (k : Fin 128) :
      (gs.foldl step (inputs.map (bit k))).getD o false = bit k (~~~goal) := by
    let x (i : Fin 6) : Bool := bit k (inputs.getD i.val 0)
    have same : List.ofFn x = inputs.map (bit k) := by
      apply List.ext_getElem
      · simp [width]
      · intro i hi hj
        have hlt : i < inputs.length := by simpa using hj
        simp only [List.getElem_ofFn, List.getElem_map, x, List.getD_eq_getElem?_getD,
          List.getElem?_eq_getElem hlt, Option.getD_some]
    change Circuit.eval ⟨gs,o⟩ (inputs.map (bit k)) = bit k (~~~goal)
    rw [← same, he]
    exact sample k
  obtain ⟨t, ht, run⟩ := compile gs o hg inputs inputs.toFinset init evaluate
  have lift {a b : ℕ} (h : a ≤ b) (hr : build basicOps t a inputs.toFinset) :
      build basicOps t b inputs.toFinset := by
    induction h with
    | refl => exact hr
    | step _ ih => exact Or.inl ih
  exact Bool.noConfusion (reject.symm.trans (search_complete ht 8 inputs nd (lift low run)))

def rows : List W :=
  [(0x0400014014861055#64 ++ 0xfac047c7fd8e31ff#64 : BitVec 128),
   (0x08419b1ab0b2c6cc#64 ++ 0xf7c3bb3ab2f3cecc#64 : BitVec 128),
   (0x501c2c2cc3016b0a#64 ++ 0xef7c3c3cc303ff0f#64 : BitVec 128),
   (0x602ec03703580da0#64 ++ 0xdfffc03f03fc0ff0#64 : BitVec 128),
   (0x80b777c003efb000#64 ++ 0xbfbfffc003fff000#64 : BitVec 128),
   (0x003bfebfe8000000#64 ++ 0x7e3ffffffc000000#64 : BitVec 128)]

def witness : Circuit :=
  ⟨[⟨.or, [0, 1]⟩, ⟨.and, [2, 3]⟩, ⟨.or, [0, 7]⟩, ⟨.and, [6, 8]⟩, ⟨.or, [9, 4]⟩, ⟨.or, [2, 3]⟩, ⟨.and, [6, 11]⟩, ⟨.and, [8, 5]⟩, ⟨.or, [12, 13]⟩, ⟨.and, [14, 10]⟩], 15⟩

def mkw (a b : BitVec 64) : W := a ++ b

def z0 : W := mkw 0x00182c2cc0000000 0x6e3c3c3cc0000000

def z1 : W := mkw 0x003bfebfe8000000 0x7e3ffffffc000000

def z2 : W := mkw 0x0400014014861055 0xfac047c7fd8e31ff

def z3 : W := mkw 0x08419b1ab0b2c6cc 0xf7c3bb3ab2f3cecc

def z4 : W := mkw 0x501c2c2cc3016b0a 0xef7c3c3cc303ff0f

def z5 : W := mkw 0x602ec03703580da0 0xdfffc03f03fc0ff0

def z6 : W := mkw 0x80b777c003efb000 0xbfbfffc003fff000

def z7 : W := mkw 0x0000801200100480 0xdfc3c03f03fc0ff0

def z8 : W := mkw 0x08419a1aa030c688 0x0503b8380271ce00

def z9 : W := mkw 0x80b776800369a000 0x053fb8000271c000

def z10 : W := mkw 0x400c082c83004b08 0xef7c383c8303cf0c

def z11 : W := mkw 0x501c2c2cc3016b0a 0x487c043cc1003f0f

def z12 : W := mkw 0x4008002400000900 0x4040003c00000f00

def z13 : W := mkw 0x003a64a548000000 0x083c44c54c000000

def z14 : W := mkw 0x0840010010b2c6cc 0x81c0000002f3cecc

def z15 : W := mkw 0x642ec17717de1df5 0xdfffc3ff3ffc0ff0

def z16 : W := mkw 0x0400014014861055 0x7a0047c7fc02300f

def z17 : W := mkw 0x84b777c017efb055 0xbfffffc003fff1ff

def z18 : W := mkw 0x0008883fe8000000 0x4000003ffc000000

def z19 : W := mkw 0x0033768000000000 0x3e3fffc000000000

def z20 : W := mkw 0x84a353c014ee9055 0xfac3c7c7fdfe31ff

def z21 : W := mkw 0x003ffebfeb480000 0xffbffffffffc0000

def z22 : W := mkw 0x503e6cadcb016b0a 0xef7c7cfdcf03ff0f

def z23 : W := mkw 0x0c419b5ab4b6d6dd 0xffc3ffffffffffff

def z24 : W := mkw 0x541c2d6cd7877b5f 0xfffc7fffff8fffff

def z25 : W := mkw 0x541c2d6cd7877b5f 0xef7c3ffcff03ff0f

def z26 : W := mkw 0x84b777c017efb055 0xffffffc7fffff1ff

def z27 : W := mkw 0x8cf7ffdab7fff6dd 0xffffffffffffffff

def z28 : W := mkw 0x0001931200b28480 0xf7c3bb3a02f3cec0

def z29 : W := mkw 0x0400004004041011 0x080044c54d0c3133

def z30 : W := mkw 0x501c2c2cc3016b0a 0x053c38380201ce00

def z31 : W := mkw 0x0400014014861055 0x200007c0fc02300f

def z32 : W := mkw 0x642ec17717de1df5 0xffffc7fffffe3fff

def z33 : W := mkw 0x2022c013005804a0 0x1083c00300fc00f0

def z34 : W := mkw 0x003b7eade8000000 0x283c7fc5fc000000

def z35 : W := mkw 0x503bfebfe8004b0a 0x7e7ffffffc000f0f

def z36 : W := mkw 0x501c2c2cc3016b0a 0xff7c7fffff03ff0f

def z37 : W := mkw 0x043bfffffc861055 0xfefffffffd8e31ff

def z38 : W := mkw 0x00019a1aa0000000 0x7603bb3ab0000000

def z39 : W := mkw 0x087bffbff8b2c6cc 0xfffffffffef3cecc

def z40 : W := mkw 0x0000010000a28000 0x8180000002f3c000

def z41 : W := mkw 0x0400014014861055 0x108043c33c8c00f0

def z42 : W := mkw 0x0400000014000055 0xea400407fd0231ff

def z43 : W := mkw 0x0000000000000000 0xfa4047c7fd02310f

def z44 : W := mkw 0x80b7f7d32befb000 0xbfbfffc33ffff000

def z45 : W := mkw 0x0022400000000000 0x1e3fc00000000000

def z46 : W := mkw 0x0014240003012000 0x083c040001003000

def z47 : W := mkw 0x80b777c003efb000 0x283c7fc0010ff000

def z48 : W := mkw 0x003b7eacc0000000 0x7e3ffffcc0000000

def z49 : W := mkw 0x08411b08b0b2c6cc 0xa1c03b00b2f3cecc

def z50 : W := mkw 0x84a353c014ee9055 0x1083c3c33cfc00f0

def z51 : W := mkw 0x0000080880004208 0xe74038388203ce0c

def z52 : W := mkw 0x602e402503480920 0x083c4005010c0130

def z53 : W := mkw 0x603ffebfeb480920 0x7e3ffffffd0c0130

def z54 : W := mkw 0x0000881a80104688 0xf7c3b83a82f3cecc

def z55 : W := mkw 0x00019a1aa0000000 0x0403b83800000000

def z56 : W := mkw 0x501cac3feb016b0a 0xef7c3c3fff03ff0f

def z57 : W := mkw 0x0000000000000000 0xea400404c102310f

def z58 : W := mkw 0x80b77fc883eff208 0xfffffff883fffe0c

def z59 : W := mkw 0x0033778000a28000 0xbfbfffc002f3c000

def z60 : W := mkw 0x002ac03700000000 0x5e3fc03f00000000

def z61 : W := mkw 0xd09c2d6cc3effb0a 0xeffc3c3cc3ffff0f

def z62 : W := mkw 0x8484014017efb055 0x81c0000003fff1ff

def z63 : W := mkw 0x0000010010820044 0xfac04307b18e01fc

def z64 : W := mkw 0x10102c08c001620a 0xe7403c38c203fe0f

def z65 : W := mkw 0x603ffebfeb580da0 0xfffffffffffc0ff0

def z66 : W := mkw 0x80b377c000a7b000 0x3e3fffc00003f000

def z67 : W := mkw 0x08419b1ab0b2c6cc 0xffc3fffffef3cecc

def z68 : W := mkw 0x003bfebfe8000000 0x043fb83800000000

def z69 : W := mkw 0x0848883ff81046cc 0x4040003ffc000ecc

def z70 : W := mkw 0x0023d29328000000 0x1003c3c33c000000

def z71 : W := mkw 0x5004000003016b0a 0x814000000303ff0f

def z72 : W := mkw 0x0840881ab01046cc 0x4040003ab0000ecc

def z73 : W := mkw 0x80b664c0034d3000 0x083c44c0010c3000

def z74 : W := mkw 0x0033fe9be8000000 0x3003ffc3fc000000

def z75 : W := mkw 0x0000000000000000 0x7a0047c7fc000000

def z76 : W := mkw 0x501c2c2cc3016b0a 0x0d3c3c3c4301ff03

def z77 : W := mkw 0x80b6648003492000 0x003c000000000000

def z78 : W := mkw 0x0001130010a28044 0xf7c3bb02b2f3c0cc

def z79 : W := mkw 0x0c41935234b694d5 0xfac3c7c7fdfe31ff

def z80 : W := mkw 0x003aecbfe8000000 0x483c44fffc000000

def z81 : W := mkw 0x00011b0880a2c208 0xf7c3bb3882f3ce0c

def z82 : W := mkw 0x0840090890b2c6cc 0xe7c0383882f3cecc

def z83 : W := mkw 0x703eec3fc3596faa 0xdffff83f03fdcff0

def z84 : W := mkw 0x809137c000a7b000 0xba807fc0018ff000

def z85 : W := mkw 0x0400000014000055 0xdac04007fd8c01ff

def z86 : W := mkw 0x603ffebfeb580da0 0xdffff83f03fc0ff0

def z87 : W := mkw 0x80bff7f703efb000 0xffbfffff03fff000

def z88 : W := mkw 0x00113e88e8000000 0x20003fc0fc000000

def z89 : W := mkw 0x686fdb3fb3facfec 0xfffffb3fb3ffcffc

def z90 : W := mkw 0x0841931230b284c4 0xf2c38302b0f200cc

def z91 : W := mkw 0xe0bff7f703ffbda0 0xffffffff03fffff0

def z92 : W := mkw 0x003bfebfe8004208 0xff7ffffffe03ce0c

def z93 : W := mkw 0x501c242443012902 0xcf7c043c43003f03

def z94 : W := mkw 0x0000010010820044 0xf2c00302b08200cc

def z95 : W := mkw 0xd4bf7fecd7effb5f 0xffffffffffffffff

def z96 : W := mkw 0x0008883fe8000000 0x7a0047fffc000000

def z97 : W := mkw 0x501c2c2cc3016b0a 0x283c3c04c103f10f

def z98 : W := mkw 0x642ec17717de1df5 0xdfffc03f03fe3fff

def z99 : W := mkw 0x0840811210b2c6cc 0xd7c3803a02f3cecc

def z100 : W := mkw 0x0000000000000000 0xdac04007018c01f0

def z101 : W := mkw 0x0000801200100480 0xd7c3803a02f00ec0

def z102 : W := mkw 0x0001130000a28000 0xb783bb0002f3c000

def z103 : W := mkw 0x00337e88e8000000 0x3e3fffc0fc000000

def z104 : W := mkw 0x6008803700100da0 0x4040003f00000ff0

def z105 : W := mkw 0x0000010010820044 0x20000300b002000c

def z106 : W := mkw 0x087bfebfe830c688 0x7f3ffffffe71ce00

def z107 : W := mkw 0x501c242443012902 0xea7c0404c102310f

def z108 : W := mkw 0x0023d29328000000 0x7a03c7c7fc000000

def z109 : W := mkw 0x603ffebfeb580da0 0x7f3ffffffe700e00

def z110 : W := mkw 0x585dbf3ef3b3efce 0xffffbf3ef3f3ffcf

def z111 : W := mkw 0x0015370003a3a000 0xbfbfbf0003f3f000

def z112 : W := mkw 0x80b377c000ee9000 0x3ebfffc000fc0000

def z113 : W := mkw 0x602ec83feb580da0 0xdfffc03ffffc0ff0

def z114 : W := mkw 0x08419b1ab0b2c6cc 0x2503bb38b273ce0c

def z115 : W := mkw 0x04008152149614d5 0xffc3c7fffffe3fff

def z116 : W := mkw 0x08411b08b0a2c24c 0x20003b00b003c00c

def z117 : W := mkw 0x10102c08c001620a 0x20003c00c003f00f

def z118 : W := mkw 0x103bfebfe801620a 0x7e3ffffffc03f00f

def z119 : W := mkw 0x14102d48d487725f 0xfac07fc7fd8ff1ff

def z120 : W := mkw 0x0014240003012000 0xaf3c3c000303f000

def z121 : W := mkw 0x80a353c000ee9000 0x1083c3c000fc0000

def z122 : W := mkw 0x0026400003480000 0x9fbfc00003fc0000

def z123 : W := mkw 0x5008082cc0004b0a 0x4040003cc0000f0f

def z124 : W := mkw 0x0400000014000055 0x00400000000001ff

def z125 : W := mkw 0x6404014017de1df5 0xfbc047c7fffe3fff

def z126 : W := mkw 0x80bfffffebefb000 0xffbffffffffff000

def z127 : W := mkw 0x8084014003efb000 0x8180000003fff000

def z128 : W := mkw 0x80b665c003cf3000 0xbabc47c0018e3000

def z129 : W := mkw 0x003bffffe8861000 0xfebffffffd8e3000

def z130 : W := mkw 0x0000014000861000 0xba8047c0018e3000

def z131 : W := mkw 0x08419a1ab030c6cc 0x4543b83ab271cecc

def z132 : W := mkw 0x501c2d6cc3877b0a 0xfffc7ffcc38fff0f

def z133 : W := mkw 0x80b777c003efb000 0xffffffc703fff1f0

def z134 : W := mkw 0x602fd33703fa8da0 0xfffffb3f03ffcff0

def z135 : W := mkw 0x0036640003492000 0xbfbffc0003fff000

def z136 : W := mkw 0x503ffebfeb016b0a 0xff7fffffff03ff0f

def z137 : W := mkw 0x20000000005804a0 0x0080000000fc00f0

def z138 : W := mkw 0x80be64e54b4d3000 0x083c44c54d0c3000

def z139 : W := mkw 0x642ec077075c1db1 0xdfffc4ff4ffc3ff3

def z140 : W := mkw 0x703eec3fc3596faa 0xfffffc3fc3ffffff

def z141 : W := mkw 0x003bfebfe8100480 0xfffffffffef00ec0

def z142 : W := mkw 0x440c016417861955 0xfffc47ffff8e3fff

def z143 : W := mkw 0x00182c2cc0000000 0xee7c3c3cc102310f

def z144 : W := mkw 0x80b776c0036db000 0x0d3ffcc0037df000

def z145 : W := mkw 0x686fda3fa378cfa8 0xdffff83f03fdcff0

def z146 : W := mkw 0x0000000000000000 0x9a804000018c0000

def z147 : W := mkw 0x501c2c2cc3016b0a 0xcf7c383c0301cf00

def z148 : W := mkw 0x003bfebfe8000000 0x3e3ffff800000000

def z149 : W := mkw 0x80b664c0034d3000 0xaf3c7cc0030ff000

def z150 : W := mkw 0x88f7ffdab3fff6cc 0xfffffffab3fffecc

def z151 : W := mkw 0x0010240000012000 0x20003c000003f000

def z152 : W := mkw 0x6004000003580da0 0x0100000002700e00

def z153 : W := mkw 0x50182c2cc0004b0a 0x6e7c3c3cc0000f0f

def z154 : W := mkw 0x00182c2cc0000000 0x7e3c7ffffc000000

def z155 : W := mkw 0x403ffebfeb000900 0xff7fffffff000f00

def z156 : W := mkw 0x0018ac3fe8000000 0x6e3c3c3ffc000000

def z157 : W := mkw 0x003a64a548000000 0x003c000000000000

def z158 : W := mkw 0x2422c15314de14f5 0x1083c3c33cfc00f0

def z159 : W := mkw 0x80a240c0004c1000 0x000040c0000c0000

def z160 : W := mkw 0x08419b1ab0b2c6cc 0x60403b3ab003cecc

def z161 : W := mkw 0x849137c014a7b055 0x20003fc0fc03f00f

def z162 : W := mkw 0x0840891ab09246cc 0xf2c0033ab0820ecc

def z163 : W := mkw 0x08411b08b0a2c24c 0xe7403b38b203ce0c

def z164 : W := mkw 0x002bdabfe8000000 0x5003c3fffc000000

def z165 : W := mkw 0x80840040034d3000 0x00000000010c3000

def z166 : W := mkw 0x002a402500000000 0x083c400500000000

def z167 : W := mkw 0x08419b1ab0b284c4 0x7683bb3ab0f000c0

def z168 : W := mkw 0x80bffebfeb69a000 0x053fb8380271c000

def z169 : W := mkw 0x08419b1ab0b2c6cc 0xffc3fb3fb3ffcffc

def z170 : W := mkw 0x0423d3d33c861055 0x1083c3c33c8c00f0

def z171 : W := mkw 0x00019a1aa0100480 0xf7c3bb3ab2f00ec0

def z172 : W := mkw 0x602ec03703580da0 0xd7ff803a02f00ec0

def z173 : W := mkw 0x80913fc8e8a7b000 0x20003fc0fc03f000

def z174 : W := mkw 0x501c242443012902 0xaf3c3c044303f103

def z175 : W := mkw 0x0c419b5ab4b6d6dd 0xf7c3bb3ab3ffffff

def z176 : W := mkw 0x501c2c2cc3016b0a 0x253c3c38c203fe0f

def z177 : W := mkw 0x08419a1aa030c688 0xd7c3b83a02f1cec0

def z178 : W := mkw 0x686fdb3fb3facfec 0xf7ffbb3ab2f3cecc

def z179 : W := mkw 0x5404014017877b5f 0x81c00000038fffff

def z180 : W := mkw 0x84b777c017efb055 0xbfbfffc33ffff0f0

def z181 : W := mkw 0x6848883fb0104fec 0x4040003fb0000ffc

def z182 : W := mkw 0x0014240003012000 0xef7c3c04c303f10f

def z183 : W := mkw 0x087bffbff8b284c4 0x7ebffffffcf000c0

def z184 : W := mkw 0x6008883fe8100da0 0x4040003ffc000ff0

def z185 : W := mkw 0x003bfebfe8000000 0x6e3fbc3cc0000000

def z186 : W := mkw 0x703e6c2dc3496b2a 0xef7c7c3dc30fff3f

def z187 : W := mkw 0xc0bf77e403efb900 0xfffffffc03ffff00

def z188 : W := mkw 0x0400014014861055 0x80c00000018e31ff

def z189 : W := mkw 0x0022c01300000000 0x1003c00300000000

def z190 : W := mkw 0x702ec03703596faa 0xdfffc03f03ffffff

def z191 : W := mkw 0x0400000014000055 0x7a4047c7fc0001ff

def z192 : W := mkw 0x80b777c013efb044 0xffffffc2b3fff0cc

def z193 : W := mkw 0x0400014014861055 0x88c044c54d8e31ff

def z194 : W := mkw 0x0000010010820044 0xfac047c7fc8200cc

def z195 : W := mkw 0x2863d31330fa84e4 0x1083c30330fc00f0

def z196 : W := mkw 0x0840881ab01046cc 0xe740383ab203cecc

def z197 : W := mkw 0x0000000000000000 0x0000000000000000

def z198 : W := mkw 0x5848883ef0104fce 0x4040003ef0000fcf

def z199 : W := mkw 0x402ec03703000900 0xdf7fc03f03000f00

def z200 : W := mkw 0x08411b08b0a2c24c 0xb783bb00b2f3c00c

def z201 : W := mkw 0x0022408108000000 0x000040c10c000000

def z202 : W := mkw 0x001c2c2cc3012000 0xef3c3c3cc303f000

def z203 : W := mkw 0x0000000010000044 0x40400002b00000cc

def z204 : W := mkw 0x00099a3fe8000000 0x7603bb3ffc000000

def z205 : W := mkw 0x80b777c003efb000 0x85bfb80003fff000

def z206 : W := mkw 0x08419a1aa030c688 0x7703bb3ab271ce00

def z207 : W := mkw 0x0400014014861055 0xbac047c0018e31ff

def z208 : W := mkw 0x6004000003580da0 0x81c0000003fc0ff0

def z209 : W := mkw 0x0033768000000000 0x7e3fffc7fc000000

def z210 : W := mkw 0x0033768000000000 0x043fb80000000000

def z211 : W := mkw 0x00113e88e8000000 0x0000380000000000

def z212 : W := mkw 0x0841921220308480 0x0003800000700000

def z213 : W := mkw 0x0c419b5ab4b6d6dd 0xf7c3fbfbbeffcefc

def z214 : W := mkw 0x0000014000861000 0x108043c0008c0000

def z215 : W := mkw 0x0400004004041011 0xdac044c74d8c31f3

def z216 : W := mkw 0x501c2c2cc3016b0a 0xfffc7c3fc38fffff

def z217 : W := mkw 0x400c002403000900 0xcf7c003c03000f00

def z218 : W := mkw 0xd084014003effb0a 0x81c0000003ffff0f

def z219 : W := mkw 0x809137c000a7b000 0x20003fc00003f000

def z220 : W := mkw 0x0841931230b284c4 0x1083830230f000c0

def z221 : W := mkw 0x0000000000000000 0x08004005010c0130

def z222 : W := mkw 0x003bfebfe8000000 0x5e3ff83f00000000

def z223 : W := mkw 0x04019b5ab4861055 0xfec3fffffd8e31ff

def z224 : W := mkw 0x0863db9bb8b2c6cc 0xf7c3fbfbbef3cecc

def z225 : W := mkw 0x501c2c2cc3016b0a 0xe77c38388203ce0c

def z226 : W := mkw 0x686fda3fa378cfa8 0x053fb8380271ce00

def z227 : W := mkw 0x6c6fdb7fb7fedffd 0xffffffffffffffff

def z228 : W := mkw 0x90913fc8c0a7f20a 0x20003fc0c003f00f

def z229 : W := mkw 0x58459b1ab3b3efce 0xf7c3bb3ab3f3ffcf

def z230 : W := mkw 0x002ac03700000000 0x7e3fc7fffc000000

def z231 : W := mkw 0x602e402503480920 0xcf7c403d030c0f30

def z232 : W := mkw 0x003bfebfe8000000 0xfefffffffd8c01f0

def z233 : W := mkw 0x501c242443012902 0x083c040441003103

def z234 : W := mkw 0x08419b1ab0b2c6cc 0x1583bb3a32f1cec0

def z235 : W := mkw 0x602ec03703580da0 0x15bfc03b02fc0ef0

def z236 : W := mkw 0x0026c01203580480 0xdfffc03a03fc0ec0

def z237 : W := mkw 0x043a64e54c041011 0x083c44c54d0c3133

def z238 : W := mkw 0x585c2d2cd3b3efce 0xeffc3c3cc3f3ffcf

def z239 : W := mkw 0x602ec03703580da0 0x053f803802700e00

def z240 : W := mkw 0x0400014014861055 0x00800000008c00f0

def z241 : W := mkw 0x00019b1aa0a28000 0xf783bb3ab2f3c000

def z242 : W := mkw 0x0000010010820044 0x10800302308000c0

def z243 : W := mkw 0x602ec03703580da0 0xffffc43fc3fe3fff

def z244 : W := mkw 0x003bfebfe8000000 0x243fbff8fc000000

def z245 : W := mkw 0x809136800021a000 0x000038000001c000

def z246 : W := mkw 0xe0bff6b70379ada0 0x053fb8380271ce00

def z247 : W := mkw 0x0026414003ce1000 0xbfbfc7c003fe3000

def z248 : W := mkw 0x08419b5ab0b6d6cc 0xffc3fffab3fffecc

def z249 : W := mkw 0x5008082cc0004b0a 0x0000003800000e00

def z250 : W := mkw 0x0400014014861055 0xf2c007c2fc8230cf

def z251 : W := mkw 0x0000080880000000 0x6600383880000000

def z252 : W := mkw 0x8484014017efb055 0xfbc047c7fffff1ff

def z253 : W := mkw 0x84b777c007efb011 0xbfbfffc54ffff133

def z254 : W := mkw 0x0033f69328000000 0x3e3fffc33c000000

def z255 : W := mkw 0x0018242440000000 0x083c040440000000

def z256 : W := mkw 0x80b377c000efb000 0x3083ffc000fff000

def z257 : W := mkw 0x541c246447053913 0x083c44c54d0c3133

def z258 : W := mkw 0x2026c013035804a0 0x9fbfc00303fc00f0

def z259 : W := mkw 0x602ec03703580da0 0x85ff803803fc0ff0

def z260 : W := mkw 0x0840010010a2c24c 0x000000000003c00c

def z261 : W := mkw 0x003a64a548000000 0x7a3c47c7fc000000

def z262 : W := mkw 0x003bfebfe8000000 0x143ffbfb3c000000

def z263 : W := mkw 0x80b777c003efb000 0xffffffc4c3fff10f

def z264 : W := mkw 0x0400004004041011 0xea4044c5cd0e313f

def z265 : W := mkw 0x0004000003480000 0x8180000003fc0000

def z266 : W := mkw 0x500c082cc3016b0a 0xc140003cc303ff0f

def z267 : W := mkw 0x0c411b48b4a6d25d 0xfac07fc7fd8ff1ff

def z268 : W := mkw 0x80b776c0034d3000 0x3e3fffc0010c3000

def z269 : W := mkw 0x80a753c003efb000 0x9183c3c003fff000

def z270 : W := mkw 0xd0bf7fecc3effb0a 0xfffffffcc3ffff0f

def z271 : W := mkw 0xe084014003ffbda0 0x81c0000003fffff0

def z272 : W := mkw 0x88f7fe9aa379e688 0x053fb8380271ce00

def z273 : W := mkw 0x002ec03703480000 0xdfbfc03f03fc0000

def z274 : W := mkw 0x400c002403000900 0xdffc403f038c0ff0

def z275 : W := mkw 0x88f77fc8b3eff24c 0xbfbfffc0b3fff00c

def z276 : W := mkw 0x702ec83fc3584faa 0xdfffc03fc3fc0fff

def z277 : W := mkw 0x501c2c2cc3012902 0x6e3c3c3cc1003103

def z278 : W := mkw 0x003b76a548000000 0x3e3fffc54c000000

def z279 : W := mkw 0x88e3dbdab0fed6cc 0xf7c3fbfab2ffcecc

def z280 : W := mkw 0x043bfffffc861055 0x7ebffffffc8c00f0

def z281 : W := mkw 0x0c7bfffffcb6d6dd 0xffffffffffffffff

def z282 : W := mkw 0x0001120000208000 0x0503b8000271c000

def z283 : W := mkw 0x743eed7fd7df7fff 0xffffffffffffffff

def z284 : W := mkw 0x809537c003a7b000 0xaf3c3fc00303f000

def z285 : W := mkw 0xd0be64e4434d3902 0x083c44c4410c3103

def z286 : W := mkw 0x643fffffffde1df5 0xfffffffffffe3fff

def z287 : W := mkw 0x0000000000004208 0x814000000203ce0c

def z288 : W := mkw 0x043377c014861055 0xfeffffc7fd8e31ff

def z289 : W := mkw 0x6404014017de1df5 0x81c0000003fe3fff

def z290 : W := mkw 0x0004000003000000 0x8f3c000003000000

def z291 : W := mkw 0x0000000000000000 0x080044c54c000000

def z292 : W := mkw 0x68459b1ab3facfec 0xf7c3bb3ab3ffcffc

def z293 : W := mkw 0x10182c2cc001620a 0x6e3c3c3cc003f00f

def z294 : W := mkw 0x541c2c6cc7057b1b 0xef7c7cfdcf0fff3f

def z295 : W := mkw 0x0000801200100480 0x0503803802700e00

def z296 : W := mkw 0x0027530003ea8000 0xbfbffb0003ffc000

def z297 : W := mkw 0xe0bee4f7035d3da0 0xdfffc4ff03fc3ff0

def z298 : W := mkw 0x808113c000a69000 0x000003c000000000

def z299 : W := mkw 0x80bfffffebefb000 0xbfbffff803fff000

def z300 : W := mkw 0x003ae4b748000000 0x5e3fc4ff4c000000

def z301 : W := mkw 0x6004000003580da0 0xdbc0400703fc0ff0

def z302 : W := mkw 0x00011a08a0000000 0x20003b00b0000000

def z303 : W := mkw 0x0841931230b2c6cc 0x91c3830232f3cecc

def z304 : W := mkw 0x08411a08a020c208 0x000038000001c000

def z305 : W := mkw 0x88f7ff9ab3fbe6cc 0xf7ffbb3ab2f3cecc

def z306 : W := mkw 0x585cac3ef3116fce 0xef7c3c3ef303ffcf

def z307 : W := mkw 0xd0bf7eacc369eb0a 0x053fb8380271ce00

def z308 : W := mkw 0x80bbffffe8ee9000 0x7ebffffffcfc0000

def z309 : W := mkw 0x0000000000000000 0xe24000008002000c

def z310 : W := mkw 0x003bfebfe8000000 0x763fbb3ab0000000

def z311 : W := mkw 0x80bffebfeb69a000 0x7f3ffffffe71c000

def z312 : W := mkw 0x602ec83f83584fa8 0xfffff83f83ffcffc

def z313 : W := mkw 0x04113fc8fc861055 0x20003fc0fc02300f

def z314 : W := mkw 0x602ec03703580da0 0x0d3fc03d037c0f30

def z315 : W := mkw 0x003bfebfe8000000 0xfe7ffffffd02310f

def z316 : W := mkw 0x002bda3fa0000000 0x7e3ffb3fb0000000

def z317 : W := mkw 0x0400000014000055 0x40400007fc0001ff

def z318 : W := mkw 0x602fda3fa3580da0 0xfffffb3fb3fc0ff0

def z319 : W := mkw 0x602e402503480920 0x003c000000000000

def z320 : W := mkw 0x0400014014861055 0x188047c77d8c31f3

def z321 : W := mkw 0x5004080883016b0a 0xe74038388303ff0f

def z322 : W := mkw 0x0c419b5ab4b6d6dd 0xf7c3bffafef3fecf

def z323 : W := mkw 0x642ec03717580df5 0xdfffc03ffffc0fff

def z324 : W := mkw 0x0000881aa0000000 0x4000003ab0000000

def z325 : W := mkw 0x08419a1ab01046cc 0x7643bb3ab0000ecc

def z326 : W := mkw 0x501c2d2cd3836b4e 0xfffc3f3ef383ffcf

def z327 : W := mkw 0x087bffbff8b2c6cc 0xf7ffbb3ab2f3cecc

def z328 : W := mkw 0x587fffbffbb3efce 0xfffffffffff3ffcf

def z329 : W := mkw 0x2422c15314de14f5 0xfac3c7c7fdfe31ff

def z330 : W := mkw 0xe0be64e5034d3920 0x083c44c5010c3130

def z331 : W := mkw 0x602fd2b72b580da0 0xdfffc3ff3ffc0ff0

def z332 : W := mkw 0x08419b1aa0b2c688 0xb783bb3802f3ce00

def z333 : W := mkw 0x602ec03703580da0 0x5f3fc03f02700e00

def z334 : W := mkw 0x042ac17714861055 0xfeffc7fffd8e31ff

def z335 : W := mkw 0x501cac3ec3116f8a 0xffffbc3ec3f3ffcf

def z336 : W := mkw 0x602e402503480920 0x9fbfc00503fc0130

def z337 : W := mkw 0x0408883ffc000055 0x4040003ffc0001ff

def z338 : W := mkw 0x08400000101046cc 0x0040000000000ecc

def z339 : W := mkw 0x5008082cc0004b0a 0xe740383cc203cf0f

def z340 : W := mkw 0x0000014000861000 0x80800000018e3000

def z341 : W := mkw 0x6008803700100da0 0x0000003800000e00

def z342 : W := mkw 0xa0b7f7d303ffb4a0 0xbfbfffc303fff0f0

def z343 : W := mkw 0x703ffebfeb596faa 0xffffffffffffffff

def z344 : W := mkw 0x0c419b1ab4b2c6dd 0xf7c3bb3ffef3cfff

def z345 : W := mkw 0x0000000000000000 0xa70038000203c000

def z346 : W := mkw 0x80b777c003efb000 0xffbfffc7fffff000

def z347 : W := mkw 0x0400004004041011 0x00000000010c3133

def z348 : W := mkw 0xd0b777c003effb0a 0xbfffffc003ffff0f

def z349 : W := mkw 0x80b7778003eba000 0xb7bfbb0002f3c000

def z350 : W := mkw 0x003bf6b768000000 0x183fc7c77c000000

def z351 : W := mkw 0x0023da9ba8000000 0x7603fbfbbc000000

def z352 : W := mkw 0x88c59b5ab3fff6cc 0xf7c3bb3ab3fffecc

def z353 : W := mkw 0x6008803700100da0 0xdac0403f018c0ff0

def z354 : W := mkw 0x6000000000100da0 0x0040000000000ff0

def z355 : W := mkw 0x0000010000820000 0xb280030000820000

def z356 : W := mkw 0x603e64a54b480920 0x083c44c54d0c0130

def z357 : W := mkw 0xd8fffffef3ffffce 0xfffffffef3ffffcf

def z358 : W := mkw 0x0000000000000000 0xfac047c7fd8c01f0

def z359 : W := mkw 0x603ee43703592da0 0xfffffc3f03fffff0

def z360 : W := mkw 0x5004000003016b0a 0x010000000201ce00

def z361 : W := mkw 0x4004000003000900 0x8140000003000f00

def z362 : W := mkw 0x0014240003012000 0x053c38000201c000

def z363 : W := mkw 0x0840010010b284c4 0x0080000000f000c0

def z364 : W := mkw 0x0400014014861055 0x280047c5fd0e313f

def z365 : W := mkw 0x80b664c0034d3000 0x9fbfc4c003fc3000

def z366 : W := mkw 0x5408096cd4865b5f 0xfac047fffd8e3fff

def z367 : W := mkw 0x401c242403012900 0xef7c3c3c0303ff00

def z368 : W := mkw 0x80a3d3d328ee9000 0x1083c3c33cfc0000

def z369 : W := mkw 0x2022400100480020 0x00004001000c0030

def z370 : W := mkw 0x0026400003480000 0x083c4000010c0000

def z371 : W := mkw 0x0400000014000055 0x000000033c0000f0

def z372 : W := mkw 0xe0bff7f703ffbda0 0xbfbffff803fffe00

def z373 : W := mkw 0x0000000000000000 0x200007c0fc000000

def z374 : W := mkw 0x0000000000000000 0xfac04407c18e31ff

def z375 : W := mkw 0x602ac03700580da0 0x50c3c03f00fc0ff0

def z376 : W := mkw 0x686ec13713facfec 0xdfffc03f03ffcffc

def z377 : W := mkw 0x0c41935234b694d5 0x1083c3c33cfc00f0

def z378 : W := mkw 0x50182c2cc0016b0a 0x60403c3cc003ff0f

def z379 : W := mkw 0x602ec03703580da0 0xffffc7fffffc0ff0

def z380 : W := mkw 0x80b665c003efb000 0x89bc44c003fff000

def z381 : W := mkw 0x0400004004041011 0x7a0047c7fd0c3133

def z382 : W := mkw 0x0400014014861055 0xc0c00007fd8e31ff

def z383 : W := mkw 0x0423d3d33c861055 0xfac3c7c7fd8e31ff

def z384 : W := mkw 0x0000000000000000 0x40400004c000010f

def z385 : W := mkw 0x503ffebfeb012902 0x7e3ffffffd003103

def z386 : W := mkw 0x0855bf1ab3b3e6cc 0xffffbf3ab3f3fecc

def z387 : W := mkw 0xe0b777c003ffbda0 0xbfffffc003fffff0

def z388 : W := mkw 0x80a6414003efb000 0x9fbfc00003fff000

def z389 : W := mkw 0x00019a1aa0000000 0x7e03fffffc000000

def z390 : W := mkw 0x5408082cd4004b5f 0x4040003ffc000fff

def z391 : W := mkw 0x686fd33733fa8de4 0xdfffc33f33fc0ff0

def z392 : W := mkw 0x703e642543492922 0x083c4405410c3133

def z393 : W := mkw 0x0032648000000000 0x083c44c000000000

def z394 : W := mkw 0x88f7ffdaa3fff688 0xbfbffff803fffe00

def z395 : W := mkw 0x0019be3ee0000000 0x7e3fbf3ef0000000

def z396 : W := mkw 0x88fffffffbfff6cc 0xfffffffffffffecc

def z397 : W := mkw 0x0000000000000000 0x20000400c002300f

def z398 : W := mkw 0x80b777c003efb000 0x15bffbc002fdc000

def z399 : W := mkw 0x0841130030a28044 0x0000030030000000

def z400 : W := mkw 0x541c256457873957 0xfafc47c7fd8e31ff

def z401 : W := mkw 0x0001134000a69000 0xbf83ffc003fff000

def z402 : W := mkw 0x08419b1ab0b2c6cc 0xffc3bf3ef3f3ffcf

def z403 : W := mkw 0x0859bf3ef0b2c6cc 0xffffbf3ef2f3cecc

def z404 : W := mkw 0x0000080880004208 0xef403c3cc303ff0f

def z405 : W := mkw 0x80b776800369a000 0x9fbff80003fdc000

def z406 : W := mkw 0x087bffbff8a2c24c 0x7e3ffffffc03c00c

def z407 : W := mkw 0x585d3f2cf3a3eb4e 0xef7c3f3cf303ff0f

def z408 : W := mkw 0x08419a1aa030c688 0xe743b8388273ce0c

def z409 : W := mkw 0x00193eace8000000 0x6e3c3ffcfc000000

def z410 : W := mkw 0x603bfebfe8100da0 0x7e7ffffffc000ff0

def z411 : W := mkw 0x0000000000000000 0x100043c33c000000

def z412 : W := mkw 0x0000000000000000 0xd2c00002008000c0

def z413 : W := mkw 0x80b777c003efb000 0x253fbfc00273f000

def z414 : W := mkw 0x6026c01303580da0 0x91c3c00303fc0ff0

def z415 : W := mkw 0x585dbe3ee331ef8a 0xef7fbc3cc373ff0f

def z416 : W := mkw 0x0000014010861044 0xfac047c2b18e30cc

def z417 : W := mkw 0x809537c003efb000 0xa1803fc003fff000

def z418 : W := mkw 0x0001130000a28000 0x1083830000f00000

def z419 : W := mkw 0x0414254017873055 0xfffc7fc7ff8ff1ff

def z420 : W := mkw 0x08408012301004c4 0x00000002300000c0

def z421 : W := mkw 0x00019a1aa0004208 0xf743bb3ab203ce0c

def z422 : W := mkw 0x0840881aa0104688 0x0000003800000e00

def z423 : W := mkw 0xd0bf7fecc3effb0a 0xbfbffff803fffe00

def z424 : W := mkw 0x0010240000000000 0x2e3c3c0000000000

def z425 : W := mkw 0x809137c000a7b000 0xb783bfc002f3f000

def z426 : W := mkw 0x602ec03703580da0 0x487c403f010c0ff0

def z427 : W := mkw 0x08419b1ab0b2c6cc 0x85c3b83802f3cecc

def z428 : W := mkw 0x0023528000000000 0x1003c3c000000000

def z429 : W := mkw 0x84b777c017efb055 0xbfbfffc0fffff00f

def z430 : W := mkw 0x501d3f2cc3a3eb0a 0xffffbf3cc3f3ff0f

def z431 : W := mkw 0x0400014014861055 0xba8047c33d8e30f0

def z432 : W := mkw 0x086bdb3fb0b2c6cc 0xfffffb3fb2f3cecc

def z433 : W := mkw 0x2023d293285804a0 0x1083c3c33cfc00f0

def z434 : W := mkw 0x084000000030c688 0x010000000271ce00

def z435 : W := mkw 0x2863db1bb0fac6ec 0xf7c3fb3bb2ffcefc

def z436 : W := mkw 0x849137c014a7b055 0xfac07fc7fd8ff1ff

def z437 : W := mkw 0x0000000000000000 0x40000007fc000000

def z438 : W := mkw 0x2022c013005804a0 0xdac3c00701fc01f0

def z439 : W := mkw 0x7008883fc0104faa 0x4040003fc0000fff

def z440 : W := mkw 0x602ec03703580da0 0x9fbfc03803fc0e00

def z441 : W := mkw 0xa0a3d3d300fe94a0 0x1083c3c300fc00f0

def z442 : W := mkw 0x0008883fe8000000 0x0000003800000000

def z443 : W := mkw 0x603ee4b74b580da0 0xdfffc4ff4ffc0ff0

def z444 : W := mkw 0x0400014014861055 0x000003c03c000000

def z445 : W := mkw 0x08419b1ab0b2c6cc 0x50c3833ab0f00ecc

def z446 : W := mkw 0x602e402503480920 0xdafc4007018c01f0

def z447 : W := mkw 0x602ec17703de1da0 0xffffc7ff03fe3ff0

def z448 : W := mkw 0x0000010010820044 0xfac00706f18231cf

def z449 : W := mkw 0x80b7f7d203ffb480 0xfffffffa03fffec0

def z450 : W := mkw 0x0841931230b284c4 0xd7c3833a32f00ec0

def z451 : W := mkw 0x00182c2cc0000000 0x043c383800000000

def z452 : W := mkw 0x0000080880004208 0x050038380201ce00

def z453 : W := mkw 0x703eec3fc3596faa 0x053fb8380271ce00

def z454 : W := mkw 0x6004801203580da0 0xd7c3803a03fc0ff0

def z455 : W := mkw 0x603ffebfeb580da0 0x053fb83802700e00

def z456 : W := mkw 0x000009089082424c 0xf7c03b3ab283cecc

def z457 : W := mkw 0x503ffebfeb016b0a 0x7f3ffffffe01ce00

def z458 : W := mkw 0x90b77fc8c3eff20a 0xbfbfffc0c3fff00f

def z459 : W := mkw 0x0426414017ce1055 0xffffc7c7fffe31ff

def z460 : W := mkw 0x0010248048000000 0x000004c04c000000

def z461 : W := mkw 0x80b77fc8ebefb000 0xbfbfffc0fffff000

def z462 : W := mkw 0x703eec3fc3596faa 0xef7fbc3cc373ff0f

def z463 : W := mkw 0x5008082cc0004b0a 0xea40043cc1023f0f

def z464 : W := mkw 0x80b776800369a000 0x3f3fffc00271c000

def z465 : W := mkw 0x0001120000000000 0x3603bb0000000000

def z466 : W := mkw 0x0400014014861055 0x7a8047c7fc8c00f0

def z467 : W := mkw 0x043bfffffc861055 0x7e3ffffffc02300f

def z468 : W := mkw 0x541c2c2cd7016b5f 0xef7c3c3fff03ffff

def z469 : W := mkw 0x10000808c000420a 0x00000000c000000f

def z470 : W := mkw 0x0008002400000000 0x4e3c003c00000000

def z471 : W := mkw 0x002bd2b728000000 0x5e3fc3ff3c000000

def z472 : W := mkw 0x0037768003480000 0xbfbfffc003fc0000

def z473 : W := mkw 0x0000000000000000 0x40400007000001f0

def z474 : W := mkw 0x0400014014861055 0xdac043c73d8c01f0

def z475 : W := mkw 0x501c2c2cc3016b0a 0x857c38380303ff0f

def z476 : W := mkw 0x0000000000000000 0x804000000102310f

def z477 : W := mkw 0x503f7eacc3016b0a 0xff7ffffcc303ff0f

def z478 : W := mkw 0x0c40014014b6d6dd 0x81c0000003ffffff

def z479 : W := mkw 0x20008013001004a0 0x00000003000000f0

def z480 : W := mkw 0x0000801328000000 0x000000033c000000

def z481 : W := mkw 0x0019bebfe8000000 0x60003ffffc000000

def z482 : W := mkw 0x503ffebfeb016b0a 0xef7fbc3cc303ff0f

def z483 : W := mkw 0x80bf7fecc3efb000 0xffbffffcc3fff000

def z484 : W := mkw 0x08499b3ff8b2c6cc 0xf7c3bb3ffef3cecc

def z485 : W := mkw 0x0000801200000000 0x5603803a00000000

def z486 : W := mkw 0x18513f08f0a3e24e 0x20003f00f003f00f

def z487 : W := mkw 0x501dbe3ee3016b0a 0xff7fbf3ef303ff0f

def z488 : W := mkw 0x600c803703580da0 0xc1c0003f03fc0ff0

def z489 : W := mkw 0x80b777c003efb000 0x18bfc7c001fc3000

def z490 : W := mkw 0x0840891ab0b2c6cc 0xc1c0003ab2f3cecc

def z491 : W := mkw 0x585dbf3ef3b3efce 0xf7ffbb3ab2f3cecc

def z492 : W := mkw 0x0000000000000000 0xc740003802000e00

def z493 : W := mkw 0x703ee43743592da2 0xdfffc43f43fc3ff3

def z494 : W := mkw 0x2022c013005804a0 0xd7c3c03b02fc0ef0

def z495 : W := mkw 0x00142c0883016208 0xef7c3c388303fe0c

def z496 : W := mkw 0x541c2d6cd7877b5f 0xeffc3c3cc38fffff

def z497 : W := mkw 0x04182d6cd4861055 0xfefc7ffffd8e31ff

def z498 : W := mkw 0x84b664c0074d3011 0x083c44c54d0c3133

def z499 : W := mkw 0x0023d29328000000 0x0003800000000000

def z500 : W := mkw 0x642e416517ce1975 0xfafc47c7fd8e31ff

def z501 : W := mkw 0x5c5dbf7ef7b7ffdf 0xffffffffffffffff

def z502 : W := mkw 0x0000004000041000 0x080044c0010c3000

def z503 : W := mkw 0x5004000003016b0a 0xeb400404c303ff0f

def z504 : W := mkw 0x602ac03700100da0 0x5e7fc03f00000ff0

def z505 : W := mkw 0x501c2c2cc3016b0a 0x457c383cc201cf0f

def z506 : W := mkw 0x0000801200100480 0x4040003a00000ec0

def z507 : W := mkw 0x7004000003596faa 0x81c0000003ffffff

def z508 : W := mkw 0x58499b3ef0b2cfce 0xf7c3bb3ef2f3cfcf

def z509 : W := mkw 0x00000808e8000000 0x00000000fc000000

def z510 : W := mkw 0x0026400003480000 0xdfffc00703fc01f0

def z511 : W := mkw 0x501c2c2cc3016b0a 0xaf3c3c380303fe00

def z512 : W := mkw 0xe0bff6b70379ada0 0xdffff83f03fdcff0

def z513 : W := mkw 0x0004000003012000 0x810000000303f000

def z514 : W := mkw 0x0400004004041011 0x000040c10c0c0030

def z515 : W := mkw 0x602ec03703580da0 0x18bfc00701fc01f0

def z516 : W := mkw 0xd0be6cecc34d7b0a 0xef7c7cfcc30fff0f

def z517 : W := mkw 0x0000000000000000 0x3a0047c000000000

def z518 : W := mkw 0x500c002403016b0a 0xcf7c003c0303ff0f

def z519 : W := mkw 0x00113e88e8000000 0x7a007fc7fc000000

def z520 : W := mkw 0x808400000369a000 0x010000000271c000

def z521 : W := mkw 0x002ac83fe8000000 0x5e3fc03ffc000000

def z522 : W := mkw 0x687fffbffbfacfec 0xffffffffffffcffc

def z523 : W := mkw 0x503eec3fc3016b0a 0xff7ffc3fc303ff0f

def z524 : W := mkw 0x80a3528000688000 0x0003800000700000

def z525 : W := mkw 0x400c002403000900 0x083c000401000100

def z526 : W := mkw 0x0033fe9aa0000000 0x7e3ffffab0000000

def z527 : W := mkw 0x0c40895ab49656dd 0xfac047fffd8e3fff

def z528 : W := mkw 0x0c40881ab41046dd 0x4040003ffc000fff

def z529 : W := mkw 0x602ec03703580da0 0x457f803f02700ff0

def z530 : W := mkw 0x585dbe3ee331ef8a 0x053fb8380271ce00

def z531 : W := mkw 0x0000080880004208 0x200038008003c00c

def z532 : W := mkw 0x003377c000861000 0xbebfffc0018e3000

def z533 : W := mkw 0x686ec83fb3584fec 0xdfffc03fb3fc0ffc

def z534 : W := mkw 0x0008803700000000 0x4000003f00000000

def z535 : W := mkw 0x003aec3fc0000000 0x7e3ffc3fc0000000

def z536 : W := mkw 0x402e402403480900 0xdfffc03c03fc0f00

def z537 : W := mkw 0x0000000000000000 0x6a000404c0000000

def z538 : W := mkw 0x1010240040012002 0x0000040040003003

def z539 : W := mkw 0x10142c08c301620a 0xaf3c3c00c303f00f

def z540 : W := mkw 0x0000010010820044 0x80c00000008200cc

def z541 : W := mkw 0x501c2c2cc3016b0a 0x6f3c3c3cc201ce00

def z542 : W := mkw 0x0400014014861055 0x000000000002300f

def z543 : W := mkw 0x401c2c2cc3000900 0xef7c3c3cc3000f00

def z544 : W := mkw 0x04113fc8fc861055 0xfac07fc7fd8e31ff

def z545 : W := mkw 0x003a6cadc8000000 0x6e3c7cfdcc000000

def z546 : W := mkw 0x0400000004000011 0x000000054c000133

def z547 : W := mkw 0x087bfebff81046cc 0x7e7ffffffc000ecc

def z548 : W := mkw 0xe8ffffffb3ffffec 0xffffffffb3fffffc

def z549 : W := mkw 0x6408817714961df5 0xfac047fffd8e3fff

def z550 : W := mkw 0x0400014014861055 0xf2c00302b18e31ff

def z551 : W := mkw 0x80bf77e54befb000 0xbfbfffc54ffff000

def z552 : W := mkw 0x10102c08c001620a 0x000038000001c000

def z553 : W := mkw 0x787fff3ff3fbefee 0xffffff3ff3ffffff

def z554 : W := mkw 0x88c4014013fff6cc 0x81c0000003fffecc

def z555 : W := mkw 0x6008803700100da0 0xd7c3803f02f00ff0

def z556 : W := mkw 0x701cac3fc3116faa 0xef7c3c3fc303ffff

def z557 : W := mkw 0x0008082cc0000000 0x4000003cc0000000

def z558 : W := mkw 0xd09d3fecc3a7fb0a 0xef7c3ffcc303ff0f

def z559 : W := mkw 0x203bfebfe85804a0 0x7ebffffffcfc00f0

def z560 : W := mkw 0x8084014003efb000 0xbb8047c003fff000

def z561 : W := mkw 0x80b776800369a000 0xaf3fbc000373f000

def z562 : W := mkw 0x0000000000000000 0x5a00400700000000

def z563 : W := mkw 0x400c002403000900 0x053c003802000e00

def z564 : W := mkw 0x80a353c000ee9000 0xba83c7c001fe3000

def z565 : W := mkw 0x0026400003480000 0x053f800002700000

def z566 : W := mkw 0x80bffeffeb4d3000 0x7e3ffffffd0c3000

def z567 : W := mkw 0x0000014000861000 0xfac047c4c18e310f

def z568 : W := mkw 0x5844010013b3efce 0x81c0000003f3ffcf

def z569 : W := mkw 0x80a353c000ee9000 0xb783fbc002ffc000

def z570 : W := mkw 0x484d9b3eb3b2cfcc 0xffffbb3eb3f3cfcc

def z571 : W := mkw 0x08400808b000424c 0x00000000b000000c

def z572 : W := mkw 0x0400014014861055 0x308047c3fc8e30ff

def z573 : W := mkw 0x6004000003480920 0x00000000010c0130

def z574 : W := mkw 0x8085134003efb000 0xb783bb0003fff000

def z575 : W := mkw 0x0408897ffc861055 0xfac047fffd8e31ff

def z576 : W := mkw 0x003bfebfe8000000 0x0c3ffcfd4c000000

def z577 : W := mkw 0x0c411b48b4a6d25d 0x20003fc0fc03f00f

def z578 : W := mkw 0x0011be9ae8000000 0x7603bffafc000000

def z579 : W := mkw 0x003ffebfeb012000 0xff3fffffff03f000

def z580 : W := mkw 0x0400014014861055 0x90c043c33d8e31ff

def z581 : W := mkw 0x5008883fe8004b0a 0x4040003ffc000f0f

def z582 : W := mkw 0xe0aec17703ffbda0 0xdfffc03f03fffff0

def z583 : W := mkw 0x88f7f7d233ffb4c4 0xbfbfffc233fff0c0

def z584 : W := mkw 0x0400000014000055 0x00000000fc00000f

def z585 : W := mkw 0x0841130010b2c6cc 0xb7c3bb0002f3cecc

def z586 : W := mkw 0x503e6c2cc3496b0a 0xfffffc3cc3ffff0f

def z587 : W := mkw 0x603eec3fc3580da0 0xfffffc3fc3fc0ff0

def z588 : W := mkw 0x503ffebfeb016b0a 0x053fb8380201ce00

def z589 : W := mkw 0x68499b3fb0b2cfec 0xf7c3bb3fb2f3cffc

def z590 : W := mkw 0x84bfffffffefb055 0xfffffffffffff1ff

def z591 : W := mkw 0x602ec13713da0de4 0xffffc33fb3fe0ffc

def z592 : W := mkw 0xe0afd3f703fe9da0 0xdfffc3ff03fc0ff0

def z593 : W := mkw 0x603ff6b703580da0 0xffffffff03fc0ff0

def z594 : W := mkw 0x0400014014861055 0x604007c7fc0231ff

def z595 : W := mkw 0x0400010014820055 0xf2c00307fc8201ff

def z596 : W := mkw 0x0400014004861011 0xba8047c54d8e3133

def z597 : W := mkw 0x1851bf1af0b3e6ce 0xf7c3bf3af2f3fecf

def z598 : W := mkw 0x0c40014014b6d6dd 0xfbc047c7ffffffff

def z599 : W := mkw 0x0400004014041055 0x484044c7fd0c31ff

def z600 : W := mkw 0x003bffbff8820044 0xfefffffffc8200cc

def z601 : W := mkw 0x6408803714100df5 0x4040003ffc000fff

def z602 : W := mkw 0x600c803703100da0 0xcf7c003f03000ff0

def z603 : W := mkw 0x6026400003580da0 0x9fffc00003fc0ff0

def z604 : W := mkw 0x0000000000000000 0xca40000401000100

def z605 : W := mkw 0x0840010010b2c6cc 0xf3c00302b2f3cecc

def z606 : W := mkw 0x5000000000004b0a 0x0040000000000f0f

def z607 : W := mkw 0x14102d48d487725f 0x20003fc0fc03f00f

def z608 : W := mkw 0x0400014014861055 0x50c043c7fc8c01ff

def z609 : W := mkw 0x50142c08c3016b0a 0xa1403c00c303ff0f

def z610 : W := mkw 0x0873ff9ab0b2c6cc 0xfffffffab2f3cecc

def z611 : W := mkw 0x00182c2cc0004208 0xef7c3c3cc203ce0c

def z612 : W := mkw 0x0000014000861000 0xfa8047c7fd8e3000

def z613 : W := mkw 0x0000000000000000 0xaa00040001023000

def z614 : W := mkw 0xd0bf7eacc369eb0a 0xef7fbc3cc373ff0f

def z615 : W := mkw 0x80a753c003ee9000 0x9fbfc3c003fc0000

def z616 : W := mkw 0x0840881ab01046cc 0xd7c3803ab2f00ecc

def z617 : W := mkw 0x501c242443012902 0x003c000000000000

def z618 : W := mkw 0x0863d39338b284c4 0x1083c3c33cf000c0

def z619 : W := mkw 0x043a65e55c861055 0xfafc47c7fd8e31ff

def z620 : W := mkw 0x0400014014861055 0xeac00404c18e31ff

def z621 : W := mkw 0x400c803603100d80 0xdfff803e03f00fc0

def z622 : W := mkw 0x602e402503580da0 0x89fc400503fc0ff0

def z623 : W := mkw 0x0400014014861055 0xba8047c0fd8e300f

def z624 : W := mkw 0x0000000000000000 0x72000302b0000000

def z625 : W := mkw 0x0000000000000000 0x10804003008c00f0

def z626 : W := mkw 0x501c242443016b0a 0x897c04044303ff0f

def z627 : W := mkw 0x202ac037005804a0 0x5ebfc03f00fc00f0

def z628 : W := mkw 0x809024c000053000 0x000004c000003000

def z629 : W := mkw 0x84b665c017cf3055 0xfafc47c7fd8e31ff

def z630 : W := mkw 0x0867db1ab3fac6cc 0xfffffb3ab3ffcecc

def z631 : W := mkw 0x0000014000861000 0xfac047c7018e31f0

def z632 : W := mkw 0x0400014014861055 0xa0c007c0fd8e31ff

def z633 : W := mkw 0x0000000000000000 0x9783800002f00000

def z634 : W := mkw 0x0400014014861055 0xea4007c4fd02310f

def z635 : W := mkw 0x88d1bfdab0b7f6cc 0xf7c3bffab2f3fecc

def z636 : W := mkw 0x0014254003873000 0xbfbc7fc0038ff000

def z637 : W := mkw 0x0851bf9af8b2c6cc 0xf7c3bffafef3cecc

def z638 : W := mkw 0x0400004004041011 0x000004c04c003003

def z639 : W := mkw 0x00008112109204c4 0xf7c3833ab2f20ecc

def z640 : W := mkw 0xe4bff7f717ffbdf5 0xffffffffffffffff

def z641 : W := mkw 0x00019b1ab0820044 0xf6c3bb3ab08200cc

def z642 : W := mkw 0x0401134014a69055 0xffc3ffc7fffff1ff

def z643 : W := mkw 0x08419b1ab0b2c6cc 0x3083bb02b0f3c0cc

def z644 : W := mkw 0x80b7ffdaa3efb000 0xffbffffab3fff000

def z645 : W := mkw 0x88f777c013fff6cc 0xbfffffc003fffecc

def z646 : W := mkw 0x0841931230b284c4 0xb783bb0232f3c0c0

def z647 : W := mkw 0x701c2c2cc3596faa 0xeffc3c3cc3ffffff

def z648 : W := mkw 0x0000014000861000 0x200007c000023000

def z649 : W := mkw 0x0000080880004208 0x4040003880000e0c

def z650 : W := mkw 0x0000801200100480 0x1083800200f000c0

def z651 : W := mkw 0x8080014000a7b000 0x000000000003f000

def z652 : W := mkw 0x6844010013facfec 0x81c0000003ffcffc

def z653 : W := mkw 0x5404014017877b5f 0xfbc047c7ff8fffff

def z654 : W := mkw 0xd0bf77e443efb902 0xbfbfffc443fff103

def z655 : W := mkw 0x0001921220000000 0x1003830230000000

def z656 : W := mkw 0x0000000000100480 0x81c0000002f00ec0

def z657 : W := mkw 0xd0bfffffebeffb0a 0xffffffffffffff0f

def z658 : W := mkw 0x600c002403580da0 0xcffc003c03fc0ff0

def z659 : W := mkw 0x88e3d3d230fe94c4 0x1083c3c230fc00c0

def z660 : W := mkw 0x00102c08c0000000 0x20003c00c0000000

def z661 : W := mkw 0x0000000000000000 0x80c00000018c01f0

def z662 : W := mkw 0x087bfebfe830c688 0x053fb8380271ce00

def z663 : W := mkw 0x8094254003efb000 0xafbc3c0003fff000

def z664 : W := mkw 0x88d13fc8b0a7f24c 0x20003fc0b003f00c

def z665 : W := mkw 0x002ac03700100480 0xdfffc03f02f00ec0

def z666 : W := mkw 0x08411b08b0a2c24c 0xf2c03b02b083c0cc

def z667 : W := mkw 0x6008002500000920 0x0000000500000130

def z668 : W := mkw 0x500c082cc3004b0a 0xcf7c003cc3000f0f

def z669 : W := mkw 0x002ac03700000000 0xdeffc03f018c01f0

def z670 : W := mkw 0x8080014000ee9000 0x0080000000fc0000

def z671 : W := mkw 0x0001128028000000 0x000003c03c000000

def z672 : W := mkw 0x5014240003016b0a 0xaf7c3c000303ff0f

def z673 : W := mkw 0x0000000000000000 0x0800040441003103

def z674 : W := mkw 0x10113e88e801620a 0x20003fc0fc03f00f

def z675 : W := mkw 0x0037768003012000 0xbf3fffc00303f000

def z676 : W := mkw 0x043bfeffec041011 0x7e3ffffffd0c3133

def z677 : W := mkw 0x602ec03703580da0 0xcf7f803c03700f00

def z678 : W := mkw 0x642e4065074c1931 0x083c44c54d0c3133

def z679 : W := mkw 0x040009489486525d 0xffc07fffff8fffff

def z680 : W := mkw 0x08513f88f8a2c24c 0x20003fc0fc03c00c

def z681 : W := mkw 0x10102c08c001620a 0xea403c04c103f10f

def z682 : W := mkw 0x003bffbfe8a28000 0xffbffffffef3c000

def z683 : W := mkw 0x0008002548000000 0x000000054c000000

def z684 : W := mkw 0x501d3eaceb016b0a 0xef7c3ffcff03ff0f

def z685 : W := mkw 0x0001130000a28000 0x20003b000003c000

def z686 : W := mkw 0x002ac03700000000 0x043f803800000000

def z687 : W := mkw 0x503e64a54b012902 0x083c44c54d003103

def z688 : W := mkw 0x0011368000000000 0x20003fc000000000

def z689 : W := mkw 0x400c002403000900 0xef7c043cc3023f0f

def z690 : W := mkw 0x003bfebfe8000000 0x443fb83ffc000000

def z691 : W := mkw 0xe0bf77e503efb920 0xbfbfffc503fff130

def z692 : W := mkw 0x5004000003012902 0x0000000001003103

def z693 : W := mkw 0x08419b1ab0a2c24c 0x7603bb3ab003c00c

def z694 : W := mkw 0x80bbffffe8a7b000 0x7e3ffffffc03f000

def z695 : W := mkw 0x003bf6b700000000 0x7e3fffff00000000

def z696 : W := mkw 0x0400014014861055 0xdac04007018e31ff

def z697 : W := mkw 0x2022c013005804a0 0x0003800000700000

def z698 : W := mkw 0x0400014014861055 0xf2c043c3bc8e00fc

def z699 : W := mkw 0xf0bfffffc3ffffaa 0xffffffffc3ffffff

def z700 : W := mkw 0xe0bfffffebffbda0 0xfffffffffffffff0

def z701 : W := mkw 0x543fffffff877b5f 0xffffffffff8fffff

def z702 : W := mkw 0x0022400000480000 0x1083c00000fc0000

def z703 : W := mkw 0x043bfebffc000055 0x7e7ffffffc0001ff

def z704 : W := mkw 0x5008002440000902 0x0000000440000103

def z705 : W := mkw 0x602ec03703480920 0x5e3fc03f010c0130

def z706 : W := mkw 0x100000000001620a 0x000000000003f00f

def z707 : W := mkw 0x80b777c003efb000 0x35bfffc002fff000

def z708 : W := mkw 0x08419b1aa0b2c688 0xf783bb3ab2f3ce00

def z709 : W := mkw 0x80b777c003efb000 0x2d3fffc0037ff000

def z710 : W := mkw 0x3032ec1bc05966aa 0x3083fc03c0fff0ff

def z711 : W := mkw 0x703e64a54b492922 0x083c44c54d0c3133

def z712 : W := mkw 0x60153e88eb580da0 0xa1c03fc0fffc0ff0

def z713 : W := mkw 0x0019bebee8000000 0x7e3fbffefc000000

def z714 : W := mkw 0x08419b1ab0b2c6cc 0xd7c3bb3a32f1cec0

def z715 : W := mkw 0x0000891a909246cc 0xf7c3bb3ab2f3cecc

def z716 : W := mkw 0x087a65a558b2c6cc 0x89fc44c54ef3cecc

def z717 : W := mkw 0x08419a1aa030c688 0xef43bc3cc373ff0f

def z718 : W := mkw 0xd0be64a443492902 0x003c000000000000

def z719 : W := mkw 0x103bfebfe801620a 0x7e3ffffffc01c000

def z720 : W := mkw 0x042ac17714861055 0xdeffc03f018e31ff

def z721 : W := mkw 0x808c897febefb000 0xc180003ffffff000

def z722 : W := mkw 0x08419b1ab0b2c6cc 0x55c3bb3ab2f1cecc

def z723 : W := mkw 0x0033f69328000000 0x7e3fffc7fc000000

def z724 : W := mkw 0x7008883fc0104faa 0x4040003cc0000f0f

def z725 : W := mkw 0x642ec17717de1df5 0x253f87f8fe723e0f

def z726 : W := mkw 0x0033f69328000000 0x143ffbc33c000000

def z727 : W := mkw 0x08419b1ab0b2c6cc 0xf7c3fbfbbef3cecc

def z728 : W := mkw 0x087bfebfe820c208 0x7e3ffffffc01c000

def z729 : W := mkw 0x0008002400000000 0x7e3c47fffc000000

def z730 : W := mkw 0x0c419b5ab4b6d6dd 0xf7c3bffffef3ffff

def z731 : W := mkw 0x84b777c017efb055 0xffffffc2b3fff1ff

def z732 : W := mkw 0x0c419b5ab4b6d6dd 0xffc3fffffeffcefc

def z733 : W := mkw 0x087bfebfe8104688 0x7e3ffffffc000e00

def z734 : W := mkw 0x80b7778003eba000 0x253fbb000273c000

def z735 : W := mkw 0xe0b777c003efb920 0xbfbfffc003fff130

def z736 : W := mkw 0x0033fe9aa0000000 0x7e3ffffffc000000

def z737 : W := mkw 0x7404014017df7fff 0x81c0000003ffffff

def z738 : W := mkw 0x003a6cadc8000000 0x7e3c7ffffc000000

def z739 : W := mkw 0x203bfebfe85804a0 0x7e3ffffffc700000

def z740 : W := mkw 0x08419b1aa0b2c688 0x2503bb380273ce00

def z741 : W := mkw 0x80b777c003efb000 0xbfbfffc443fff103

def z742 : W := mkw 0x80b777c013efb044 0xffffffc7b3fff1fc

def z743 : W := mkw 0xa4a3d3d314fe94f5 0x1083c3c33cfc00f0

def z744 : W := mkw 0x08419a1ab030c6cc 0x7743bb3ab271cecc

def z745 : W := mkw 0x087bfebfe8308480 0x7e3ffffffc700000

def z746 : W := mkw 0x08419b1ab0b2c6cc 0xf7c3bb3ef2f3cfcf

def z747 : W := mkw 0x703bfebfe8104faa 0x7e7ffffffc000fff

def z748 : W := mkw 0x0c419b5ab4b6d6dd 0xffc3fbffbfffcffc

def z749 : W := mkw 0x80b777c003efb000 0x9fbffbc003fdc000

def z750 : W := mkw 0x80b777c003efb000 0xb7bfbfc002f3f000

def z751 : W := mkw 0x80b7778003eba000 0x85bfb80002f3c000

def z752 : W := mkw 0x003bfebfe8000000 0xfe7ffffffc02000c

def z753 : W := mkw 0x003bfebfe8000000 0xff7ffffffe000e00

def z754 : W := mkw 0x0033778010a28044 0xffffffc7fef3c0cc

def z755 : W := mkw 0x08419b1ab0b2c6cc 0x3583bb3ab2f3cecc

def z756 : W := mkw 0x90b777c043efb002 0xbfbfffc043fff003

def z757 : W := mkw 0x0026c01203580480 0xdfffc03f03fc0ff0

def z758 : W := mkw 0x7008883fc0104faa 0x0000003800000e00

def z759 : W := mkw 0x500c082c83016b0a 0xef7c383c8303ff0f

def z760 : W := mkw 0x08419a1aa030c688 0x1503bb3a3271ce00

def z761 : W := mkw 0x003bfebfe8004208 0xff7fffffff03ff0f

def z762 : W := mkw 0x003b7eade8000000 0x203c3fc0fc000000

def z763 : W := mkw 0x501c2c2cc3016b0a 0xef7c7cfdcf03ff0f

def z764 : W := mkw 0x6008883f80104fa8 0x4040003f80000ffc

def z765 : W := mkw 0x80b777c013efb044 0xbfffffc003fff0cc

def z766 : W := mkw 0x0c419b5ab4b6d6dd 0xf7c3bb3fffffffff

def z767 : W := mkw 0x0c419b5ab4b6d6dd 0xf7c3bbfabef3cecc

def z768 : W := mkw 0x003b7eade8000000 0x6e3c7ffdfc000000

def z769 : W := mkw 0x686f5b2db3eacb6c 0x283c7b05b10fc13c

def z770 : W := mkw 0x08419b1ab0b2c6cc 0xc5c3b83ab2f3cecc

def z771 : W := mkw 0x003a64a548000000 0x283c47c5fc000000

def z772 : W := mkw 0x043bfffffc861055 0x84ffb838018e31ff

def z773 : W := mkw 0x80b776800369a000 0x253fbfc00271c000

def z774 : W := mkw 0x585db73673b3adc6 0x18bf870671f031c3

def z775 : W := mkw 0x003bfebfe8000000 0x043fbbf83c000000

def z776 : W := mkw 0x0022400000000000 0x7e3fc7c7fc000000

def z777 : W := mkw 0xd0ab5becc0eedb0a 0x50c3c3fcc0fc0f0f

def z778 : W := mkw 0x0026400003480000 0xbfbff80003ffc000

def z779 : W := mkw 0x04182d6cd4861055 0xeefc3c3cc18e31ff

def z780 : W := mkw 0x08419b9ab8b2c6cc 0xf7c3bbfabef3cecc

def z781 : W := mkw 0x003bfebfe8000000 0x343ffffbfc000000

def z782 : W := mkw 0x003bfebfe8000000 0x7ebffffffc8c00f0

def z783 : W := mkw 0x0027530013ea8044 0xfffffb07b3ffc1fc

def z784 : W := mkw 0x501c2c2cc3016b0a 0x6f3c3c3cc203fe0f

def z785 : W := mkw 0x103bfebfe801620a 0xfe7ffffffd03f10f

def z786 : W := mkw 0x003b76a548000000 0x7e3fffc7fc000000

def z787 : W := mkw 0x0014240003012000 0xbfbfbc0003f3f000

def z788 : W := mkw 0x602ec03703580da0 0xffffc7ff03fc0ff0

def z789 : W := mkw 0x0018ac3fe8000000 0x7e3c7ffffc000000

def z790 : W := mkw 0x08419a1aa030c688 0x9783b83802f1ce00

def z791 : W := mkw 0x08419a1aa030c688 0x4543b83a0271cec0

def z792 : W := mkw 0x701c2c2cc3496b2a 0xef7c3c3cc30fff3f

def z793 : W := mkw 0x0c419b1ab4b2c6dd 0xf7c3bb3bbef3cefc

def z794 : W := mkw 0xe0be64e54b4d3920 0x083c44c54d0c3130

def z795 : W := mkw 0x603bfebfe8100da0 0xfefffffffd8c0ff0

def z796 : W := mkw 0x80b377c000ee9000 0xbfbfffc002ffc000

def z797 : W := mkw 0x00019b1aa0a2c208 0xf7c3bb3ab2f3ce0c

def z798 : W := mkw 0x003b7eacc0000000 0x7e3ffffffc000000

def z799 : W := mkw 0x103bfebfe8012002 0x7e3ffffffc003003

def z800 : W := mkw 0x80b7778003eba000 0xbfbfffc002f3c000

def z801 : W := mkw 0x80b776800369a000 0xbfbffc0003fff000

def z802 : W := mkw 0x703e642543492922 0x083c4005010c0130

def z803 : W := mkw 0x503bfebfe8004b0a 0xfe7ffffffd023f0f

def z804 : W := mkw 0x6c48883fb4104ffd 0x4040003ffc000fff

def z805 : W := mkw 0x80b776800369a000 0x2f3fbc000271c000

def z806 : W := mkw 0x2026c013035804a0 0xdfffc03b03fc0ef0

def z807 : W := mkw 0x84b777c007efb011 0xffbfffc7fffff133

def z808 : W := mkw 0x501c2c2cc3016b0a 0xfffc3c3ec383ffcf

def z809 : W := mkw 0x501c2c2cc3016b0a 0xa57c3c38c303ff0f

def z810 : W := mkw 0x00182c2cc0004208 0xef7c3c3cc303ff0f

def z811 : W := mkw 0x0001921200308480 0xd7c3b83a02f1cec0

def z812 : W := mkw 0x002bdabfe8000000 0x5e3fc3fffc000000

def z813 : W := mkw 0x001536000321a000 0x053fb8000271c000

def z814 : W := mkw 0x0848883fe8104688 0x4000003ffc000e00

def z815 : W := mkw 0x6004000003580da0 0xfbc047c7fffc0ff0

def z816 : W := mkw 0x5027d2932b016b0a 0x9143c3c33f03ff0f

def z817 : W := mkw 0x503bfebfe8000902 0x7e3ffffffc000103

def z818 : W := mkw 0x203bfebfe81004a0 0x7e3ffffffc0000f0

def z819 : W := mkw 0x08419b1ab0b2c6cc 0x0583b83802f1cec0

def z820 : W := mkw 0x0404014017ce1055 0x81c0000003fe31ff

def z821 : W := mkw 0x001536000321a000 0xaf3fbc000373f000

def z822 : W := mkw 0x003bfebfe8000000 0x643fbffffc000000

def z823 : W := mkw 0xe0be64a503492920 0x083c4005010c0130

def z824 : W := mkw 0x003bfebfe8000000 0x683c7ffffc000000

def z825 : W := mkw 0x743e656557cf3977 0xfafc47c7fd8e31ff

def z826 : W := mkw 0x0015370003a3a000 0xb7bfbb0002f3c000

def z827 : W := mkw 0x0c419b5ab4b6d6dd 0xffc3fffafffffecf

def z828 : W := mkw 0x002ac83fe8000000 0x7e3fc7fffc000000

def z829 : W := mkw 0x8095374003efb000 0xbfbfbf0003fff000

def z830 : W := mkw 0x0400014014861055 0x684047c7fd0e31ff

def z831 : W := mkw 0x08419a1ab030c6cc 0x0503b838b271ce0c

def z832 : W := mkw 0x0c419b5ab4b6d6dd 0xf7c3fbfffeffcfff

def z833 : W := mkw 0x08419b1ab0b2c6cc 0xf7c3bb3ffef3cecc

def z834 : W := mkw 0x84b777c007efb011 0xbfbfffc04ffff003

def z835 : W := mkw 0x84b777c017efb055 0xffffffc3bffff0fc

def z836 : W := mkw 0x0033fe9ba8000000 0x7e3ffffbbc000000

def z837 : W := mkw 0x602ec03703592da0 0xdfffc03f03fffff0

def z838 : W := mkw 0x80b777c003efb000 0x38bfffc001fff000

def z839 : W := mkw 0x0027534003ee9000 0xbfbfffc003fff000

def z840 : W := mkw 0x541c2d6cd7877b5f 0x15bc7bfb3e8dcef0

def z841 : W := mkw 0x08419b5ab0b6d6cc 0xffc3ffffb3fffffc

def z842 : W := mkw 0x80b777c003efb000 0xbfbfffc54ffff000

def z843 : W := mkw 0x003bfebfe8000000 0xfebffffffd8c0000

def z844 : W := mkw 0x602ec03703580da0 0xcfff803c03fc0ff0

def z845 : W := mkw 0x0033f69328000000 0x183fc7c33c000000

def z846 : W := mkw 0x003bfebfe8480000 0x7ebffffffcfc0000

def z847 : W := mkw 0x0036654003cf3000 0xbfbfffc003fff000

def z848 : W := mkw 0x80b776c0036db000 0xaf3ffcc0037ff000

def z849 : W := mkw 0x1c513f48f4a7f25f 0x20003fc0fc03f00f

def z850 : W := mkw 0x603bfebfe8100da0 0x7e3ffffffc000e00

def z851 : W := mkw 0x501c242403016b0a 0xef7c3c3c0303ff0f

def z852 : W := mkw 0x0400014014861055 0xffc3c7c7fffe31ff

def z853 : W := mkw 0x0033778000a28000 0xb7bfbb0002f3c000

def z854 : W := mkw 0x0c513fc8fca6d25d 0x20003fc0fc03f00f

def z855 : W := mkw 0x003b7eade8000000 0x7a3c7fc7fc000000

def z856 : W := mkw 0x501c2c2cc3016b0a 0xef7c7c3dc30fff3f

def z857 : W := mkw 0x08419b5ab0b6d6cc 0xf7c3bffab2f3fecc

def z858 : W := mkw 0xa0b777c103efb020 0xbfbfffc103fff030

def z859 : W := mkw 0x0c419b5ab4b6d6dd 0xffc3fb3fb3ffffff

def z860 : W := mkw 0x8cd13fc8b4a7f25d 0x20003fc0fc03f00f

def z861 : W := mkw 0xe099b7f700b7bda0 0x60403fff0003fff0

def z862 : W := mkw 0x0400014014a69055 0xfbc047c7fffff1ff

def z863 : W := mkw 0x80b777c003efb000 0xbfffffc003fff1f0

def z864 : W := mkw 0x501c2c2cc3016b0a 0xaf7c3c380303ff0f

def z865 : W := mkw 0x80b776800369a000 0xa73fb8000273c000

def z866 : W := mkw 0x0033768000000000 0x3e3fffc33c000000

def z867 : W := mkw 0x4404014017861955 0x81c00000038e3fff

def z868 : W := mkw 0x08419b1ab0b2c6cc 0xffc3fffffff3ffcf

def z869 : W := mkw 0x003bf6b768000000 0x7a3fc7c7fc000000

def z870 : W := mkw 0x5848893ef0924fce 0xfac0073ef1823fcf

def z871 : W := mkw 0x0005130003a28000 0xbfbfbb0003f3c000

def z872 : W := mkw 0x003bfebfe8208000 0x7f3ffffffe71c000

def z873 : W := mkw 0x603bfebfe8100da0 0xfffffffffef00ff0

def z874 : W := mkw 0x80b776800369a000 0x0d3fbc000371f000

def z875 : W := mkw 0x80b776800369a000 0x153ffbc00271c000

def z876 : W := mkw 0x0037778003a3a000 0xbfbfffc003f3f000

def z877 : W := mkw 0xd0b777c003efb902 0xbfbfffc003fff103

def z878 : W := mkw 0x10182c2cc001620a 0xef7c3c3cc203fe0f

def z879 : W := mkw 0x5c48883ef4104fdf 0x4040003ffc000fff

def z880 : W := mkw 0x80b776800369a000 0x7f3fffc7fe71c000

def z881 : W := mkw 0x0c419b5ab4b6d6dd 0xf7c3bb3ab2f3fecf

def z882 : W := mkw 0x84b777c017efb055 0xffffffc703fff1ff

def z883 : W := mkw 0x003bfebfe8000000 0x763fbffafc000000

def z884 : W := mkw 0x5008883ec0104f8a 0x4040003ec0000fcf

def z885 : W := mkw 0x602ec03703580da0 0x9fbfc03b03fc0ef0

def z886 : W := mkw 0x0840891a90b2c6cc 0xf7c3b83a82f3cecc

def z887 : W := mkw 0x0c419a5aa434d699 0x0d03fcfd4f7dff33

def z888 : W := mkw 0x6c48897fb4965ffd 0xfac047fffd8e3fff

def z889 : W := mkw 0x003b7eace8000000 0x7e3ffffcfc000000

def z890 : W := mkw 0x08419a1aa030c688 0x85c3b83802f1cec0

def z891 : W := mkw 0x80b777c013efb044 0xbfbfffc0b3fff00c

def z892 : W := mkw 0x002ac03700000000 0x5e3fc3ff3c000000

def z893 : W := mkw 0x002bd2b728000000 0x7e3fc7fffc000000

def z894 : W := mkw 0x80b664c0034d3000 0xbfbffcc003fff000

def z895 : W := mkw 0x08419b1ab0b2c6cc 0xd7c3b83a02f3cecc

def z896 : W := mkw 0x08419b5ab0b6d6cc 0xf7c3bb3ab3fffecc

def z897 : W := mkw 0x08419a1aa030c688 0x6703b8388271ce00

def z898 : W := mkw 0x0c48897ffc9656dd 0xfac047fffd8e3fff

def z899 : W := mkw 0x80b777c003efb000 0xffffffc083fff00c

def z900 : W := mkw 0x00337e88e8000000 0x7e3fffc7fc000000

def z901 : W := mkw 0x0400014014861055 0x58c047c7fd8c31ff

def z902 : W := mkw 0x8cc4014017fff6dd 0x81c0000003ffffff

def z903 : W := mkw 0x88f6ecdab35d76cc 0x487c44fab10c3ecc

def z904 : W := mkw 0x002ac03700100480 0xdfffc03f03fc0ff0

def z905 : W := mkw 0x80b776800369a000 0x1f3ff8000271c000

def z906 : W := mkw 0x08419b5aa0b6d688 0xbf83fff803fffe00

def z907 : W := mkw 0x003bfebfe8000000 0x543ffbfffc000000

def z908 : W := mkw 0x602ec03703580da0 0xdfffc03ffffc0ff0

def z909 : W := mkw 0x8ce3d3d234fe94d5 0x1083c3c33cfc00f0

def z910 : W := mkw 0x0848883fe8104688 0x0000003800000e00

def z911 : W := mkw 0x5c44014017b7ffdf 0x81c0000003ffffff

def z912 : W := mkw 0x703e642543492922 0x003c000000000000

def z913 : W := mkw 0x0c48883ffc1046dd 0x4040003ffc000fff

def z914 : W := mkw 0x50142c0883016b0a 0xef7c3c388303ff0f

def z915 : W := mkw 0x8484014017cf3055 0x80c00000018e31ff

def z916 : W := mkw 0x80b777c003efb000 0xfffffff803fffe00

def z917 : W := mkw 0x0400004014041055 0x7a4047c7fd0c31ff

def z918 : W := mkw 0x003bfebfe8004208 0x7f3ffffffe01ce00

def z919 : W := mkw 0x003bfebfe8004208 0x7e3ffffffc03c00c

def z920 : W := mkw 0x80b777c003efb000 0xffffffc7fffff10f

def z921 : W := mkw 0x80b776800369a000 0x85bfb80003fdc000

def z922 : W := mkw 0x2c63d35334fe94f5 0x1083c3c33cfc00f0

def z923 : W := mkw 0x002bda3fa0000000 0x7e3ffffffc000000

def z924 : W := mkw 0x80b776c0036db000 0x053fbcc00271f000

def z925 : W := mkw 0x503bfebfe8004b0a 0xff7ffffffe03cf0f

def z926 : W := mkw 0x703ffebfeb596faa 0x053fb8380271ce00

def z927 : W := mkw 0xd484014017effb5f 0x81c0000003ffffff

def z928 : W := mkw 0x84b777c017efb055 0xbfffffc0fffff1ff

def z929 : W := mkw 0x0427534017ee9055 0xffffffc7fffff1ff

def z930 : W := mkw 0x08419b1ab0b2c6cc 0xffc3fb3fb2f3cecc

def z931 : W := mkw 0x0c419b5ab4b6d6dd 0x2503bff8fe73fe0f

def z932 : W := mkw 0x0033768000208000 0x053fb8000271c000

def z933 : W := mkw 0x501c2c2cc3016b0a 0x2d3c3c3cc303ff0f

def z934 : W := mkw 0xd4be64e4474d3913 0x083c44c54d0c3133

def z935 : W := mkw 0x80b776800369a000 0x853fb8000373f000

def z936 : W := mkw 0xd0be64e54b4d3902 0x083c44c54d0c3103

def z937 : W := mkw 0x402e402403480900 0xdfffc03f03fc0ff0

def z938 : W := mkw 0x203bfebfe8480020 0x7e3ffffffc0c0030

def z939 : W := mkw 0x0001931210b284c4 0xf7c3bb3ab2f3cecc

def z940 : W := mkw 0x0000080880004208 0xf7c3b83882f3ce0c

def z941 : W := mkw 0x08419b1aa0b2c688 0xf7c3bb3a02f3cec0

def z942 : W := mkw 0x6848883fb0104fec 0x4040003ab0000ecc

def z943 : W := mkw 0x003bfebfe8000000 0x7e3ffffffc02300f

def z944 : W := mkw 0x703e642543492922 0x083c040441003103

def z945 : W := mkw 0x00337e88e8000000 0x243fbfc0fc000000

def z946 : W := mkw 0x5404014017873957 0x80c00000018e31ff

def z947 : W := mkw 0x80b777c003efb000 0xbfbfffc33ffff000

def z948 : W := mkw 0x003bfebfe8000000 0xfefffffffc8000c0

def z949 : W := mkw 0x203bfebfe85804a0 0xfffffffffefc0ef0

def z950 : W := mkw 0x0011370000a28000 0xbfbfbf0002f3c000

def z951 : W := mkw 0x002bdabfa8000000 0x7e3ffbffbc000000

def z952 : W := mkw 0xd4be65e457cf3957 0xfafc47c7fd8e31ff

def z953 : W := mkw 0x0023d29328000000 0x1e3fc3c33c000000

def z954 : W := mkw 0x103bfebfe800420a 0x7e3ffffffc00000f

def z955 : W := mkw 0x6c44014017fedffd 0x81c0000003ffffff

def z956 : W := mkw 0x401c242403012900 0xef7c3c3cc303ff0f

def z957 : W := mkw 0x80b777c003efb000 0x05bfb80002fdc000

def z958 : W := mkw 0x0032648000000000 0x7a3c47c7fc000000

def z959 : W := mkw 0x0404014017873055 0x81c00000038ff1ff

def z960 : W := mkw 0x08419b5ab0b6d6cc 0xf7c3fbfab2ffcecc

def z961 : W := mkw 0x0019be3ee0000000 0x7e3ffffffc000000

def z962 : W := mkw 0x002bd2b728000000 0x183fc3c73c000000

def z963 : W := mkw 0x08419b1ab0b2c6cc 0x95c3bb3a32f3cecc

def z964 : W := mkw 0x602ec0b70b580da0 0xdfffc0ff0ffc0ff0

def z965 : W := mkw 0x003bf6b768000000 0x3e3fffc77c000000

def z966 : W := mkw 0x80b777c003efb000 0xb7bfbb0003fff000

def z967 : W := mkw 0x08419a1aa030c688 0x2503bb38b271ce00

def z968 : W := mkw 0x0c419b5ab4b6d6dd 0xf7c3bffaffffffff

def z969 : W := mkw 0x80b777c003efb000 0x053fb8000273f000

def z970 : W := mkw 0x501c2c2cc3016b0a 0x687c3c3cc103ff0f

def z971 : W := mkw 0x84b777c017efb055 0x85ffb80003fff1ff

def z972 : W := mkw 0x08419b1ab0b2c6cc 0x7703bb3ab273ce0c

def z973 : W := mkw 0x80b776800369a000 0xbfbfffc003fdc000

def z974 : W := mkw 0x0848883ef01046cc 0x4040003ef0000ecc

def z975 : W := mkw 0x84b776801769a055 0x457fb807fe71c1ff

def z976 : W := mkw 0x8484014017efb055 0x8180000003fff0f0

def z977 : W := mkw 0x5848883ee0104f8a 0x4040003cc0000f0f

def z978 : W := mkw 0x80a7534003efb000 0xbfbffb0003fff000

def z979 : W := mkw 0x80b776800369a000 0xbf3fffc00373f000

def z980 : W := mkw 0x08419b1ab0b2c6cc 0xf7c3fb3bb2ffcefc

def z981 : W := mkw 0x80b777c04befb000 0xbfbfffc04ffff000

def z982 : W := mkw 0xe484014017ffbdf5 0x81c0000003ffffff

def z983 : W := mkw 0x702ec03703592da2 0xdfffc03f03fc3ff3

def z984 : W := mkw 0x0000000000000000 0xfac047c7fd8e31ff

def z985 : W := mkw 0x00019b1aa0b28480 0xf7c3bb3ab2f3cec0

def z986 : W := mkw 0x88f777c033efb044 0xbfbfffc033fff000

def z987 : W := mkw 0x80b777c003efb000 0xffffffc7c3fff1ff

def z988 : W := mkw 0x0c419b5ab4b6d6dd 0xffc3bffefff3ffcf

def z989 : W := mkw 0x003bfebfe8100480 0xfffffffffffc0ff0

def z990 : W := mkw 0x0001921200308480 0x0503b8380271ce00

def z991 : W := mkw 0x0841931230b284c4 0xf7c3bb3a32f3cec0

def z992 : W := mkw 0x003bfebfe8000000 0xfe3ffffffd023000

def z993 : W := mkw 0x94913fc8d4a7f25f 0x20003fc0fc03f00f

def z994 : W := mkw 0x501c2c2cc3016b0a 0x053c38380203fe0f

def z995 : W := mkw 0x80b777c003efb000 0x3fbfffc002fdc000

def z996 : W := mkw 0x003bfebfe8000000 0x1c3fffff7c000000

def z997 : W := mkw 0x84b777c017efb055 0xffbfffc7fffff0f0

def z998 : W := mkw 0xe0be64e5034d3920 0x083c44c0010c3000

def z999 : W := mkw 0x0036640003492000 0xfffffc07c3fff1ff

def z1000 : W := mkw 0xd0be65e443cf3902 0xfafc47c4c18e310f

def z1001 : W := mkw 0x0001931200b28480 0xb783bb3802f3ce00

def z1002 : W := mkw 0x501c2c2cc3016b0a 0xc57c383cc303ff0f

def z1003 : W := mkw 0x602ec03703580da0 0xffffc03f83fe0ffc

def z1004 : W := mkw 0x602ec03703580da0 0xc5ff803f03fc0ff0

def z1005 : W := mkw 0x84b777c017efb055 0xffffffc73ffff1f0

def z1006 : W := mkw 0x400c082c83004b08 0xef7c3c3cc303ff0f

def z1007 : W := mkw 0x80b777c013efb044 0xffffffc6f3fff1cf

def z1008 : W := mkw 0x80b777c003efb000 0x3f3fffc00273f000

def z1009 : W := mkw 0x80b7778003eba000 0xbfbffb0003ffc000

def z1010 : W := mkw 0x602ec03703580da0 0xdfffc4ff4ffc0ff0

def z1011 : W := mkw 0x0000801200100480 0xf7c3b83a02f3cec0

def z1012 : W := mkw 0x6027d2932b580da0 0x91c3c3c33ffc0ff0

def z1013 : W := mkw 0x0001130000a28000 0xf7c3bb3802f3ce00

def z1014 : W := mkw 0x0c419b1ab4b2c6dd 0xffc3bf3ffff3ffff

def z1015 : W := mkw 0xe0be64a503492920 0x003c000000000000

def z1016 : W := mkw 0x0c419b5ab4b6d6dd 0xf7c3bb3ab2ffcefc

def z1017 : W := mkw 0x501c2c2dcb016b0a 0xef7c3c3dcf03ff0f

def z1018 : W := mkw 0x00193eace8000000 0x7e3c7ffffc000000

def z1019 : W := mkw 0x003a64a548000000 0x183c47c77c000000

def z1020 : W := mkw 0x00011b4880a6d208 0xffc3fffcc3ffff0f

def z1021 : W := mkw 0x0400014014861055 0xffc07fc7ff8ff1ff

def z1022 : W := mkw 0x84b777c017efb055 0xbfbfffc003fff00f

def z1023 : W := mkw 0x0c419b1ab4b2c6dd 0xffc3fb3fffffcfff

def z1024 : W := mkw 0x80b777c003efb000 0xa5bfbfc003fff000

def z1025 : W := mkw 0x501c2c2cc3016b0a 0xff7c3f3ef303ff0f

def z1026 : W := mkw 0x08419a1aa030c688 0xf743bb3ab273ce0c

def z1027 : W := mkw 0x600c803603580da0 0xdfff803e03fc0ff0

def z1028 : W := mkw 0x80b777c013efb044 0xbfbfffc233fff0c0

def z1029 : W := mkw 0x88c19bdab0b6d6cc 0xf7c3bbfab2f3cecc

def z1030 : W := mkw 0x00142c0883016208 0xef7c3c3cc303ff0f

def z1031 : W := mkw 0x602ec03703580da0 0xd7ff803a03fc0ff0

def z1032 : W := mkw 0x80bbfebfe8688000 0x7e3ffffffc700000

def z1033 : W := mkw 0x08419a1aa030c688 0xa703b8380273ce00

def z1034 : W := mkw 0x602ec03703580da0 0xdfffc03f03fe3fff

def z1035 : W := mkw 0x400c803603100d80 0xdfffc03f03fc0ff0

def z1036 : W := mkw 0x80b777c003efb000 0xffffffc203fff0c0

def z1037 : W := mkw 0x00193eace8000000 0x283c3fc4fc000000

def z1038 : W := mkw 0x08419a1ab030c6cc 0x0543b8380271cecc

def z1039 : W := mkw 0x602ec03703580da0 0x58ffc03f01fc0ff0

def z1040 : W := mkw 0x703e642543492922 0xfafc4407c18e31ff

def z1041 : W := mkw 0x0033768000000000 0x3e3fffc0fc000000

def z1042 : W := mkw 0x08419a1aa030c688 0x7f03fffffe71ce00

def z1043 : W := mkw 0x602ec03703580da0 0xffffc43f03fe3ff0

def z1044 : W := mkw 0x003bfebfe8000000 0x763ffbfbbc000000

def z1045 : W := mkw 0x00011a088020c208 0xe743b8388273ce0c

def z1046 : W := mkw 0x602ec03703580da0 0x05bf803802fc0ef0

def z1047 : W := mkw 0x501c2c2ceb016b0a 0xef7c3c3cff03ff0f

def z1048 : W := mkw 0x80b776800369a000 0x0d3ffcc00271c000

def z1049 : W := mkw 0x7408897fd4965fff 0xfac047fffd8e3fff

def z1050 : W := mkw 0x501c2c2cc3016b0a 0xaf3c3c38c303fe0f

def z1051 : W := mkw 0x80b777c003efb000 0xb7bffbc002ffc000

def z1052 : W := mkw 0x08419b1ab0b2c6cc 0xf7c3bb3fb2f3cffc

def z1053 : W := mkw 0x00182c2cc0000000 0x6e3c3ffcfc000000

def z1054 : W := mkw 0x087bfebfe830c688 0xff7ffffffe73ce0c

def z1055 : W := mkw 0x08419b1ab0b2c6cc 0x6543bb3ab273cecc

def z1056 : W := mkw 0x08419b1ab0b2c6cc 0xb783bb38b2f3ce0c

def z1057 : W := mkw 0x501c2c2cc3016b0a 0xcf7c383c0303ff0f

def z1058 : W := mkw 0x6848893fb0924fec 0xfac0433fb18e0ffc

def z1059 : W := mkw 0x04011b4894a6d25d 0xffc3ffffffffffff

def z1060 : W := mkw 0x80b777c003efb000 0xffbfffc4c3fff000

def z1061 : W := mkw 0x003bfebfe8000000 0x3e3ffffb3c000000

def z1062 : W := mkw 0x08419b1aa0b2c688 0x1583bb3802f1ce00

def z1063 : W := mkw 0x80b777c003efb000 0x1dbfffc003fdf000

def z1064 : W := mkw 0x003bf6b768000000 0x103fc3c33c000000

def z1065 : W := mkw 0x84b777c017efb055 0xbfffffc54ffff1ff

def z1066 : W := mkw 0xd0be64a443492902 0x083c040441003103

def z1067 : W := mkw 0x0400014014861055 0x388047c7fd8e31ff

def z1068 : W := mkw 0x003b7eade8000000 0x3e3fffc5fc000000

def z1069 : W := mkw 0x603bfebfe8000920 0x7e3ffffffc000130

def z1070 : W := mkw 0x003bfebfe8100480 0x7f3ffffffe700e00

def z1071 : W := mkw 0x7848883ff0104fee 0x4040003ff0000fff

def z1072 : W := mkw 0x603e642503492920 0x083c4405010c3130

def z1073 : W := mkw 0x80b777c003efb000 0xffffffc403fff100

def z1074 : W := mkw 0x602ec03703580da0 0x55ffc03f02fc0ff0

def z1075 : W := mkw 0x0400014014861055 0xffc047ffff8e3fff

def z1076 : W := mkw 0x84b777c017efb055 0xbfbfffc3fffff0ff

def z1077 : W := mkw 0x602ec03703580da0 0xffffc7fffffe3fff

def z1078 : W := mkw 0x08419b1af8b2c6cc 0xf7c3bb3afef3cecc

def z1079 : W := mkw 0x003bfebfe8000000 0x7e3ffffffd0c0130

def z1080 : W := mkw 0x0c419b1ab4b2c6dd 0xffc3fffffef3cfff

def z1081 : W := mkw 0x08419a1aa030c688 0x3703bb380271ce00

def z1082 : W := mkw 0x501c2caccb016b0a 0xef7c3cfccf03ff0f

def z1083 : W := mkw 0x08411b08b0a2c24c 0xf7c3bb38b2f3ce0c

def z1084 : W := mkw 0x0000881a80104688 0xd7c3b83a02f1cec0

def z1085 : W := mkw 0xc0b777c003efb900 0xbfffffc003ffff00

def z1086 : W := mkw 0x08419b1ab0b2c6cc 0xe7c3b83882f3cecc

def z1087 : W := mkw 0x003aecbfe8000000 0x7a3c47fffc000000

def z1088 : W := mkw 0x501c2c2cc3016b0a 0xef7c3c3fff03ff0f

def z1089 : W := mkw 0x08419b1ab0b2c6cc 0xffc3ffffffffcffc

def z1090 : W := mkw 0x5404014017877b5f 0x814000000303ff0f

def z1091 : W := mkw 0x501c2c2cc3016b0a 0xff7c7c3fc303ff0f

def z1092 : W := mkw 0x0015374003a7b000 0xbfbfffc003fff000

def z1093 : W := mkw 0x08419b5ab0b6d6cc 0xffc3fffef3ffffcf

def z1094 : W := mkw 0x6404014017ce1975 0x80c00000018e31ff

def z1095 : W := mkw 0x0033fe9ae8000000 0x7e3ffffafc000000

def z1096 : W := mkw 0x702ec03743580da2 0xdfffc03f43fc0ff3

def z1097 : W := mkw 0x80b777c003efb000 0xbfbfffc303fff0f0

def z1098 : W := mkw 0x08419a1aa030c688 0xc743b8380271ce00

def z1099 : W := mkw 0x84b777c017efb055 0xbfbfffc5fffff13f

def z1100 : W := mkw 0x84b777c017efb055 0xffffffc2fffff0cf

def z1101 : W := mkw 0x0033768028000000 0x3e3fffc03c000000

def z1102 : W := mkw 0x0037768003492000 0xbfbfffc003fff000

def z1103 : W := mkw 0x08419a1aa030c688 0x4543b8388271ce0c

def z1104 : W := mkw 0x602ec03703580da0 0xdfffc3ff3ffc0ff0

def z1105 : W := mkw 0x0000881a80104688 0xe743b8388273ce0c

def z1106 : W := mkw 0x08419b1aa0b2c688 0x8583b83802f3ce00

def z1107 : W := mkw 0x80b777c013efb044 0xffffffc7fffff0cc

def z1108 : W := mkw 0x00019b1a80b2c688 0xf7c3bb3a82f3cecc

def z1109 : W := mkw 0x0c419b5ab4b6d6dd 0x85c3b83803ffffff

def z1110 : W := mkw 0x80b6654003efb000 0xbfbffc0003fff000

def z1111 : W := mkw 0x003ae4b748000000 0x7e3fc7fffc000000

def z1112 : W := mkw 0x08419b1ab0b2c6cc 0xf7c3bffafef3cecc

def z1113 : W := mkw 0x501c2c2cc3016b0a 0xef7c3c3fc303ffff

def z1114 : W := mkw 0x08419a1ab030c6cc 0xd7c3b83ab2f1cecc

def z1115 : W := mkw 0x003bf6b700000000 0x7e3ffffffc000000

def z1116 : W := mkw 0x00113e88e8000000 0x2e3c3fc0fc000000

def z1117 : W := mkw 0x08419b1ab0b2c6cc 0xffc3ff3ff3ffffff

def z1118 : W := mkw 0x84b777c007efb011 0xbfbfffc003fff133

def z1119 : W := mkw 0x003bf6b768000000 0x5e3fc7ff7c000000

def z1120 : W := mkw 0x80b777c003efb000 0x95bffbc003fff000

def z1121 : W := mkw 0x003bfebfe8000000 0x2c3ffffdfc000000

def z1122 : W := mkw 0x0000881a80104688 0xffc3fc3fc3ffffff

def z1123 : W := mkw 0x08419a1aa030c688 0x2503b8388273ce0c

def z1124 : W := mkw 0x80b776c0036db000 0x053fb800037df000

def z1125 : W := mkw 0x80b777c003efb000 0xbfbfffc503fff130

def z1126 : W := mkw 0x84b777c017efb055 0xffffffc4fffff10f

def z1127 : W := mkw 0x003bfebfe8000000 0x6e3fbffcfc000000

def z1128 : W := mkw 0x80a753c003ee9000 0xbfbffbc003ffc000

def z1129 : W := mkw 0x0027520003688000 0x053fb8000271c000

def z1130 : W := mkw 0x0c419b1ab4b2c6dd 0xf7c3bb3afef3cecf

def z1131 : W := mkw 0x80b777c003efb000 0xbfbfffc0c3fff00f

def z1132 : W := mkw 0x0c419b5ab4b6d6dd 0xffc3fffab3ffffff

def z1133 : W := mkw 0x08419b1ab0b2c6cc 0xffc3bf3ab3f3fecc

def z1134 : W := mkw 0x08419a1aa030c688 0x1583b83a02f1cec0

def z1135 : W := mkw 0x602ec03703580da0 0x8dffc03d03fc0ff0

def z1136 : W := mkw 0x0c63d3d33cb694d5 0x1083c3c33cfc00f0

def z1137 : W := mkw 0x80b777c003efb000 0xafbfbc0003fff000

def z1138 : W := mkw 0x80b377c000a7b000 0xbfbfffc002f3f000

def z1139 : W := mkw 0x0033768000208000 0x3f3fffc00271c000

def z1140 : W := mkw 0x203bfebfe85804a0 0xfefffffffdfc01f0

def z1141 : W := mkw 0x0027530003ea8000 0xb7bfbb0002f3c000

def z1142 : W := mkw 0x0036640003492000 0x053fb8000271c000

def z1143 : W := mkw 0x08419b1ab0b2c6cc 0xf7c3bb3ab3f3ffcf

def z1144 : W := mkw 0x0027520003688000 0x9fbff80003fdc000

def z1145 : W := mkw 0x18419b1af0b2c6ce 0xf7c3bb3af2f3cecf

def z1146 : W := mkw 0x08419a1aa030c688 0xdfc3f83f03fdcff0

def z1147 : W := mkw 0x84b777c017efb055 0xbfbfffc03ffff000

def z1148 : W := mkw 0x0036640003492000 0xaf3fbc000373f000

def z1149 : W := mkw 0x00011b0890a2c24c 0xf7c3bb3ab2f3cecc

def z1150 : W := mkw 0x08419b1ab0b2c6cc 0xa5c3bb38b2f3cecc

def z1151 : W := mkw 0x08419a1aa030c688 0xf7c3bb3ab2f1cec0

def z1152 : W := mkw 0x80b7778013eba044 0xf7ffbb02b2f3c0cc

def z1153 : W := mkw 0x602ec0372b580da0 0xdfffc03f3ffc0ff0

def z1154 : W := mkw 0x003b76a568000000 0x083c47c57c000000

def z1155 : W := mkw 0x80b777c003efb000 0xffbfffc2b3fff000

def z1156 : W := mkw 0x0848893ff89246cc 0xfac047fffc820ecc

def z1157 : W := mkw 0x202ac037005804a0 0xdfffc03f02fc0ef0

def z1158 : W := mkw 0x0036640003492000 0x9fbff80003fdc000

def z1159 : W := mkw 0x80b7778003eba000 0x15bfbb0002f1c000

def z1160 : W := mkw 0x84b777c017efb055 0xbfffffc33ffff1ff

def z1161 : W := mkw 0x602ec03703580da0 0x9fffc03803fc0ff0

def z1162 : W := mkw 0x003bfebfe8000000 0x7e7ffffffc00010f

def z1163 : W := mkw 0x10142c08c301620a 0xef7c3c38c303fe0f

def z1164 : W := mkw 0x003bfebfe8100480 0x7ebffffffcf000c0

def z1165 : W := mkw 0x08419b1ab0b2c6cc 0x7783bb3ab2f1cec0

def z1166 : W := mkw 0x0c419a1ab430c6dd 0x4543b83ffe71cfff

def z1167 : W := mkw 0x003bfebfe8012000 0x7e3ffffffc03f000

def z1168 : W := mkw 0x08419a1ab030c6cc 0x0503b83a3271cec0

def z1169 : W := mkw 0x003bfebfe8000000 0x7e7ffffffc0001f0

def z1170 : W := mkw 0x6848883fa0104fa8 0x4040003f00000ff0

def z1171 : W := mkw 0x003bfebfe8000000 0x5e3ffbff3c000000

def z1172 : W := mkw 0x80b777c02befb000 0xbfbfffc03ffff000

def z1173 : W := mkw 0x003bfebfe8004208 0x7e7ffffffc000e0c

def z1174 : W := mkw 0x80b776800369a000 0x253fbc000273f000

def z1175 : W := mkw 0x003bfebfe8000000 0x3e3ffff8fc000000

def z1176 : W := mkw 0x80b776800369a000 0xdffff80703fdc1f0

def z1177 : W := mkw 0x08419b1ab0b2c6cc 0x0503bb383271ce00

def z1178 : W := mkw 0x0400895a949656dd 0xffc3ffffffffffff

def z1179 : W := mkw 0x002bd2b728000000 0x143fc3fb3c000000

def z1180 : W := mkw 0x5c48897ef4965fdf 0xfac047fffd8e3fff

def z1181 : W := mkw 0x80b776c0036db000 0x9fbffcc003fdf000

def z1182 : W := mkw 0x84b777c007efb011 0xffffffc5cffff13f

def z1183 : W := mkw 0x501c2c2cc3016b0a 0x657c3c3cc203ff0f

def z1184 : W := mkw 0x0840881ab01046cc 0xf7c3b83ab2f3cecc

def z1185 : W := mkw 0x08419b1ab0b2c6cc 0xffc3fffab2f3cecc

def z1186 : W := mkw 0x0436654017cf3055 0xffffffc7fffff1ff

def z1187 : W := mkw 0x80b777c003efb000 0xffffffc7fffff1f0

def z1188 : W := mkw 0x0841931210b2c6cc 0xf7c3bb3a02f3cecc

def z1189 : W := mkw 0x0415374017a7b055 0xffffffc7fffff1ff

def z1190 : W := mkw 0x602e402403580da0 0xdfffc03c03fc0ff0

def z1191 : W := mkw 0x003377c000a69000 0xbfbfffc003fff000

def z1192 : W := mkw 0x0015370013a3a044 0xffffbf06f3f3f1cf

def z1193 : W := mkw 0x501c2c2cc3016b0a 0xfffc7c3cc38fff0f

def z1194 : W := mkw 0x003bfebfe8000000 0x383fffc7fc000000

def z1195 : W := mkw 0x80b776800369a000 0x97bfb80002f1c000

def z1196 : W := mkw 0x80b776800369a000 0x8f3fb8000371c000

def z1197 : W := mkw 0x80b777c003efb000 0x053fbbc00271c000

def z1198 : W := mkw 0x00011a088020c208 0x0503b8380271ce00

def z1199 : W := mkw 0x403bfebfe8000900 0x7e7ffffffc000f00

def z1200 : W := mkw 0x0037778003ea8000 0xbfbfffc003ffc000

def z1201 : W := mkw 0x701c2c2dc3016b2a 0xef7c3c3dc303ff3f

def z1202 : W := mkw 0x602ec0374b580da0 0xdfffc03f4ffc0ff0

def z1203 : W := mkw 0x84b777c007efb011 0xbfbfffc10ffff030

def z1204 : W := mkw 0x002a402500000000 0x7a3c47c7fc000000

def z1205 : W := mkw 0xf0be64e5434d3922 0x083c44c5410c3133

def z1206 : W := mkw 0x80b777c10befb000 0xbfbfffc10ffff000

def z1207 : W := mkw 0x08419b1ab0b2c6cc 0xf7c3bf3af2f3fecf

def z1208 : W := mkw 0x503bfebfe8004b0a 0x7e3ffffffc000e00

def z1209 : W := mkw 0x80b776800369a000 0xef7fbc04c373f10f

def z1210 : W := mkw 0x003aec3fc0000000 0x7e3ffffffc000000

def z1211 : W := mkw 0x5848883ff8104fce 0x4040003ffc000fcf

def z1212 : W := mkw 0x84b777c017efb055 0x253fbfc0fe73f00f

def z1213 : W := mkw 0x0c419b5ab4b6d6dd 0xffc3fffbbffffefc

def z1214 : W := mkw 0x503e642443492902 0x083c4404410c3103

def z1215 : W := mkw 0x501c2c2cc3016b0a 0xeffc3c3cc38fffff

def z1216 : W := mkw 0x00011b0880a2c208 0xb783bb3802f3ce00

def z1217 : W := mkw 0x003bfebfe8000000 0xff3ffffffe03c000

def z1218 : W := mkw 0x003bfebfe8000000 0xfe7ffffffd000100

def z1219 : W := mkw 0x80b777c003efb000 0xbfffffc003fff10f

def z1220 : W := mkw 0x501c2c2cc3016b0a 0xe77c38388303ff0f

def z1221 : W := mkw 0x08419a1aa030c688 0x4503b83ab271ce00

def z1222 : W := mkw 0x602ec03703580da0 0xdfffc03fc3fc0fff

def z1223 : W := mkw 0x0c419b5ab4b6d6dd 0xf7c3fbfbbfffffff

def z1224 : W := mkw 0x08419b1ab0b2c6cc 0xffc3fb3ab3ffcecc

def z1225 : W := mkw 0x80b777c003efb000 0x9fbff80003fff000

def z1226 : W := mkw 0x0c419b5ab4b6d6dd 0xffc3bf3ef3ffffff

def z1227 : W := mkw 0x103bfebfe801620a 0xff7ffffffe03fe0f

def z1228 : W := mkw 0x501c2c2cc3016b0a 0xe77c3c38c203fe0f

def z1229 : W := mkw 0x80bbfebfe821a000 0x7e3ffffffc01c000

def z1230 : W := mkw 0x50153e88eb016b0a 0xa1403fc0ff03ff0f

def z1231 : W := mkw 0x28419b1bb0b2c6ec 0xf7c3bb3bb2f3cefc

def z1232 : W := mkw 0x602ec03703580da0 0xffffc43fc3fc0ff0

def z1233 : W := mkw 0x809537c003a7b000 0xbfbfbfc003f3f000

def z1234 : W := mkw 0x5004000003016b0a 0xfb4047c7ff03ff0f

def z1235 : W := mkw 0xe4be64e5074d3931 0x083c44c54d0c3133

def z1236 : W := mkw 0x0c419b5ab4b6d6dd 0xffc3fffffef3fecf

def z1237 : W := mkw 0x003bf6b728000000 0x7e3fffff3c000000

def z1238 : W := mkw 0xe0be65e503cf3920 0xfafc47c7018e31f0

def z1239 : W := mkw 0x0018242440000000 0x7a3c47c7fc000000

def z1240 : W := mkw 0x743e6465474d3933 0x083c44c54d0c3133

def z1241 : W := mkw 0x7008883fc0104faa 0x4040003f00000ff0

def z1242 : W := mkw 0x003bfebfe8104688 0xfffffffffef3cecc

def z1243 : W := mkw 0x80b776c0036db000 0x3f3fffc0037df000

def z1244 : W := mkw 0x80b776800369a000 0x15bff80002fdc000

def z1245 : W := mkw 0x043377c014a69055 0xffffffc7fffff1ff

def z1246 : W := mkw 0x08419b5ab0b6d6cc 0xffc3fffffffffecc

def z1247 : W := mkw 0x80b776800369a000 0x0d3ff800037dc000

def z1248 : W := mkw 0x00019a1aa0104688 0xf7c3bb3ab2f3cecc

def z1249 : W := mkw 0x0019bebfe8000000 0x6e3c3ffffc000000

def z1250 : W := mkw 0x603bfebfe8580da0 0x7efffffffcfc0ff0

def z1251 : W := mkw 0x0000881a80104688 0x0503b8380271ce00

def z1252 : W := mkw 0x087bfebfe830c688 0xfffffffffef1cec0

def z1253 : W := mkw 0x7008883fc0104faa 0xfac0443fc18e3fff

def z1254 : W := mkw 0x80b7778003eba000 0xbfbfbf0003f3f000

def z1255 : W := mkw 0x84b777c017efb055 0x15bffbc33efdc0f0

def z1256 : W := mkw 0xc0be64e4034d3900 0x083c44c4010c3100

def z1257 : W := mkw 0x602ec03703580da0 0x1dbfc03f03fc0ff0

def z1258 : W := mkw 0x08419b1ab0b2c6cc 0xb7c3bb3802f3cecc

def z1259 : W := mkw 0x80b377c000efb000 0x3ebfffc000fff000

def z1260 : W := mkw 0x5848883ee0104f8a 0x0000003800000e00

def z1261 : W := mkw 0x4848883eb0104fcc 0x4040003eb0000fcc

def z1262 : W := mkw 0x602ec03703580da0 0x5fbfc03f02fc0ef0

def z1263 : W := mkw 0x80b776800369a000 0x373fbb000271c000

def z1264 : W := mkw 0x00193eace8000000 0x243c3ff8fc000000

def z1265 : W := mkw 0x0848883ff81046cc 0x4040003ab0000ecc

def z1266 : W := mkw 0x602ec03703580da0 0xdfffc43f43fc3ff3

def z1267 : W := mkw 0x0033fe9be8000000 0x3e3fffc3fc000000

def z1268 : W := mkw 0xd0be64e4434d3902 0x083c44c0010c3000

def z1269 : W := mkw 0x08419b1ab0b2c6cc 0xf7c3bb3ab3ffcffc

def z1270 : W := mkw 0x84b777c017efb055 0xffffffc4c3fff1ff

def z1271 : W := mkw 0x0848883fb01046cc 0x4040003fb0000ecc

def z1272 : W := mkw 0x003bfebfe8000000 0xfefffffffd8e31ff

def z1273 : W := mkw 0x503bfebfe8016b0a 0x7e7ffffffc03ff0f

def z1274 : W := mkw 0x501c2c2cc3016b0a 0x8d7c3c3c4303ff0f

def z1275 : W := mkw 0x003bfebfe8000000 0xffbffffffef00000

def z1276 : W := mkw 0x6848883ff8104fec 0x4040003ffc000ffc

def z1277 : W := mkw 0x08419b1ab0b2c6cc 0xffc3bf3ef2f3cecc

def z1278 : W := mkw 0x80b777c003efb000 0x8dbffcc003fff000

def z1279 : W := mkw 0x80b777c003efb000 0xffbfffc703fff000

def z1280 : W := mkw 0x0c419b5ab4b6d6dd 0xf7c3fffbfefffeff

def z1281 : W := mkw 0x80b776c0036db000 0x053ff8c0027dc000

def z1282 : W := mkw 0x0010240000000000 0x7e3c7fc7fc000000

def z1283 : W := mkw 0x84b777c017efb055 0xbfbfffc003fff0f0

def z1284 : W := mkw 0x08419b1ab0b2c6cc 0xffc3bb3eb3f3cfcc

def z1285 : W := mkw 0x5848883ef0104fce 0x4040003ab0000ecc

def z1286 : W := mkw 0xe4be65e517cf3975 0xfafc47c7fd8e31ff

def z1287 : W := mkw 0x08419b1ab0b2c6cc 0xb783bb3a32f3cec0

def z1288 : W := mkw 0x80b777c003efb000 0xaf3fbfc00373f000

def z1289 : W := mkw 0x7408883fd4104fff 0x4040003ffc000fff

def z1290 : W := mkw 0x08419a1aa030c688 0xf7c3b83a82f3cecc

def z1291 : W := mkw 0x6848883fa0104fa8 0x0000003800000e00

def z1292 : W := mkw 0x6404014017de1df5 0x81c0000003fc0ff0

def z1293 : W := mkw 0x00337e88e8000000 0x283c7fc0fc000000

def z1294 : W := mkw 0x003bfebfe8000000 0x7e3ffffffd003103

def z1295 : W := mkw 0x602ec03703580da0 0x95ffc03b03fc0ff0

def z1296 : W := mkw 0x08419a1aa030c688 0x8543b8380273ce0c

def z1297 : W := mkw 0x08419b1aa0b2c688 0xf7c3bb3882f3ce0c

def z1298 : W := mkw 0x84b777c017efb055 0xbfbfffc77ffff1f3

def z1299 : W := mkw 0x602ec03703580da0 0xd7ffc03b02fc0ef0

def z1300 : W := mkw 0x0023530000a28000 0xbfbffb0002f3c000

def z1301 : W := mkw 0x50182c2cc0016b0a 0x6e7c3c3cc003ff0f

def z1302 : W := mkw 0x602ec03703580da0 0xffffc33fb3fc0ff0

def z1303 : W := mkw 0x8484014017efb055 0x8180000003fff00f

def z1304 : W := mkw 0x602ac03700580da0 0x5effc03f00fc0ff0

def z1305 : W := mkw 0x84b776c0076db011 0x0d3ffcc54f7df133

def z1306 : W := mkw 0x84b777c007efb011 0xffffffc74ffff1f3

def z1307 : W := mkw 0x0001935200b69480 0xffc3ffff03fffff0

def z1308 : W := mkw 0x7008883fe8104faa 0x4040003ffc000fff

def z1309 : W := mkw 0x0c419b5ab4b6d6dd 0x1583fbfb3efdcef0

def z1310 : W := mkw 0x80b777c003efb000 0xbfbfffc0fffff000

def z1311 : W := mkw 0x08419a1aa030c688 0x5703b83a0271ce00

def z1312 : W := mkw 0x08419b1ab0b2c6cc 0x0503b8380273ce0c

def z1313 : W := mkw 0x501c2c2cc3016b0a 0xffffbc3cc3f3ff0f

def z1314 : W := mkw 0x602ec03703580da0 0xfffff83f03ffcff0

def z1315 : W := mkw 0x501c2c2cc3496b0a 0xeffc3c3cc3ffff0f

def z1316 : W := mkw 0x08419a1ab030c6cc 0xe743b83ab273cecc

def z1317 : W := mkw 0x6026c01203580da0 0xdfffc03a03fc0ff0

def z1318 : W := mkw 0x0c419b1ab4b2c6dd 0xf7c3bb3ab2f3cfff

def z1319 : W := mkw 0x501c2c2cc3016b0a 0xef7c3ffcff03ff0f

def z1320 : W := mkw 0x501c2c2cc3016b0a 0xff7c7ffcc303ff0f

def z1321 : W := mkw 0x501c2c2cc3016b0a 0xfffc7fffff8fffff

def z1322 : W := mkw 0x08411b0890b2c6cc 0xf7c3bb3882f3cecc

def z1323 : W := mkw 0x84b777c017efb055 0xffbfffc7fffff00f

def z1324 : W := mkw 0x0037770003eba000 0xbfbfff0003fff000

def z1325 : W := mkw 0x003bfebfe8100480 0x7e7ffffffc000ec0

def z1326 : W := mkw 0x08419b1ab0b2c6cc 0xe743bb38b273ce0c

def z1327 : W := mkw 0x08419b1bb8b2c6cc 0xf7c3bb3bbef3cecc

def z1328 : W := mkw 0x0401935214b694d5 0xffc3ffffffffffff

def z1329 : W := mkw 0x003bfebfe8000000 0x583fc7fffc000000

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkA : List (List (List (ℕ × List W))) :=
  [[[(0,[z0,z1,z2,z3,z4,z5,z6]),(0,[z7,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z8,z4,z5,z9,z6]),(0,[z1,z2,z3,z10,z4,z5,z6]),(0,[z1,z2,z3,z11,z4,z5,z6]),(0,[z1,z2,z3,z12,z4,z5,z6])],[(0,[z13,z1,z2,z3,z4,z5,z9]),(0,[z1,z2,z14,z3,z4,z5,z9]),(0,[z1,z2,z3,z4,z5,z15,z6])],[(0,[z1,z16,z2,z3,z4,z5,z6])],[(1,[z1,z2,z3,z4,z5,z17]),(0,[z18,z19,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z20]),(0,[z1,z21,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z22,z5,z6]),(0,[z1,z2,z23,z4,z24,z5,z6]),(0,[z1,z2,z3,z4,z25,z5,z6]),(0,[z1,z2,z3,z4,z5,z26,z27]),(1,[z28,z1,z2,z4,z5,z6])],[(1,[z1,z29,z8,z4,z5,z6]),(0,[z1,z3,z30,z4,z24,z5,z6]),(0,[z1,z2,z3,z4,z24,z5,z6]),(0,[z1,z31,z2,z3,z4,z32,z6]),(0,[z1,z2,z3,z33,z4,z32,z6]),(0,[z34,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z35,z5,z6])],[(0,[z1,z2,z3,z4,z36,z5,z6]),(0,[z1,z2,z37,z3,z4,z5,z9]),(1,[z38,z2,z39,z4,z5,z6]),(0,[z40,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z8,z3,z4,z5,z26]),(0,[z1,z41,z3,z30,z4,z5,z6]),(0,[z1,z42,z2,z3,z4,z5,z6])],[(0,[z43,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z44]),(0,[z45,z1,z2,z3,z4,z5,z6]),(0,[z46,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z47,z6]),(0,[z48,z1,z2,z3,z4,z5,z6])]],
   [[(0,[z1,z2,z49,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z50,z26]),(0,[z51,z1,z2,z4,z52,z5,z6]),(0,[z1,z2,z3,z4,z5,z53,z6]),(1,[z54,z1,z2,z4,z5,z6])],[(0,[z55,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z56,z5,z6]),(0,[z57,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z58])],[(1,[z59,z1,z2,z3,z4,z5]),(0,[z13,z1,z2,z14,z4,z5,z6]),(0,[z60,z1,z2,z3,z4,z5,z9]),(0,[z1,z2,z3,z4,z5,z6,z61]),(0,[z1,z2,z3,z4,z5,z6,z62]),(0,[z63,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z64,z4,z5,z6])],[(0,[z2,z37,z3,z4,z5,z65,z6]),(0,[z1,z2,z3,z4,z5,z66,z6])],[(0,[z1,z2,z3,z67,z4,z5,z6]),(0,[z68,z1,z37,z3,z4,z5,z6]),(1,[z1,z2,z3,z69,z4,z5]),(0,[z70,z2,z3,z71,z4,z5,z6]),(0,[z1,z2,z3,z71,z4,z5,z26]),(0,[z51,z1,z2,z3,z4,z5,z6]),(1,[z1,z2,z72,z4,z5,z73]),(0,[z74,z1,z2,z3,z4,z5,z6])],[(0,[z75,z1,z37,z3,z4,z5,z6]),(0,[z1,z2,z3,z76,z4,z5,z6]),(0,[z1,z2,z23,z4,z5,z77,z6]),(0,[z78,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z79,z4,z5,z6]),(0,[z80,z1,z2,z3,z4,z5,z6]),(0,[z81,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z82,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z77,z6]),(0,[z1,z2,z3,z4,z5,z83,z6]),(0,[z1,z2,z3,z4,z5,z84,z6]),(1,[z1,z2,z3,z4,z5,z26]),(0,[z1,z85,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z86,z6]),(0,[z1,z2,z3,z4,z5,z6,z87]),(0,[z88,z1,z2,z23,z4,z5,z6]),(0,[z1,z2,z23,z4,z5,z89,z6]),(0,[z1,z2,z90,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z9,z91]),(0,[z51,z92,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z93,z4,z5,z6])]],
   [[(0,[z94,z1,z2,z3,z4,z5,z6]),(0,[z1,z29,z2,z8,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z26,z95]),(0,[z96,z1,z2,z3,z4,z5,z9]),(0,[z1,z2,z3,z97,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z98,z6]),(0,[z1,z2,z99,z3,z4,z5,z6]),(0,[z100,z1,z31,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z26,z91]),(0,[z101,z102,z1,z2,z4,z5,z6]),(0,[z103,z2,z3,z4,z104,z5,z6])],[(0,[z75,z1,z2,z67,z4,z5,z6]),(0,[z105,z1,z2,z3,z4,z5,z6]),(1,[z2,z3,z106,z4,z5,z6]),(0,[z1,z2,z3,z107,z4,z5,z6]),(0,[z108,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z109,z6]),(0,[z51,z1,z2,z4,z110,z5,z6]),(1,[z111,z1,z2,z3,z4,z5])],[(0,[z1,z2,z3,z4,z5,z112,z6]),(0,[z1,z2,z3,z4,z5,z113,z6]),(0,[z1,z2,z114,z3,z4,z5,z6]),(0,[z1,z2,z115,z3,z4,z5,z6]),(0,[z1,z2,z116,z4,z52,z5,z6]),(0,[z2,z3,z117,z118,z4,z5,z6]),(0,[z1,z2,z3,z119,z4,z5,z6]),(0,[z120,z1,z2,z3,z4,z5,z121]),(0,[z122,z1,z2,z3,z123,z4,z5])],[(0,[z1,z124,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z125,z6]),(0,[z1,z2,z3,z4,z5,z6,z126]),(0,[z18,z2,z3,z4,z5,z127,z6]),(1,[z1,z2,z23,z4,z5,z9]),(0,[z1,z2,z8,z4,z5,z128,z6]),(0,[z1,z129,z2,z3,z4,z5,z6]),(0,[z130,z1,z2,z131,z4,z5,z6]),(0,[z1,z2,z3,z4,z132,z5,z6])],[(0,[z18,z1,z2,z3,z4,z5,z6]),(1,[z94,z1,z23,z4,z5,z6]),(0,[z1,z2,z72,z8,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z133]),(0,[z1,z2,z3,z4,z5,z134,z6]),(1,[z135,z1,z2,z3,z4,z5])],[(0,[z75,z1,z2,z3,z36,z5,z6]),(0,[z60,z2,z3,z4,z136,z5,z6]),(0,[z1,z2,z3,z137,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z138]),(0,[z94,z1,z3,z23,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z139,z6]),(0,[z1,z2,z3,z24,z5,z140,z6]),(0,[z101,z141,z2,z3,z4,z5,z6]),(0,[z101,z1,z2,z116,z4,z5,z6])],[(0,[z1,z2,z116,z3,z4,z5,z6]),(0,[z1,z2,z3,z142,z4,z5,z6])]],
   [[(0,[z143,z1,z2,z3,z4,z5,z6]),(1,[z1,z2,z3,z4,z5,z144]),(0,[z1,z2,z8,z4,z5,z145,z6]),(0,[z146,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z147,z4,z5,z6]),(0,[z148,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z149,z6])],[(0,[z102,z1,z2,z3,z4,z5,z26]),(0,[z102,z1,z2,z3,z4,z5,z150]),(0,[z151,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z152,z5,z6]),(0,[z19,z1,z2,z8,z4,z5,z6]),(0,[z1,z2,z3,z153,z4,z5,z6]),(0,[z130,z1,z2,z8,z4,z5,z6]),(1,[z154,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z26,z26]),(0,[z1,z2,z3,z4,z5,z26,z150]),(0,[z101,z1,z2,z3,z4,z5,z9]),(0,[z1,z2,z3,z155,z4,z5,z6]),(0,[z156,z1,z2,z3,z4,z5,z6])],[(0,[z157,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z8,z3,z4,z5,z9]),(0,[z1,z2,z3,z158,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z159,z6]),(0,[z1,z2,z160,z3,z4,z5,z6])],[(0,[z1,z2,z3,z30,z4,z5,z26]),(0,[z1,z2,z3,z4,z5,z161,z26]),(0,[z1,z2,z162,z3,z4,z5,z6]),(0,[z51,z1,z2,z3,z110,z5,z6]),(0,[z1,z2,z163,z3,z4,z5,z6]),(0,[z164,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z165,z6]),(0,[z166,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z167,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z168]),(0,[z1,z31,z2,z8,z4,z5,z6]),(0,[z100,z1,z2,z169,z4,z5,z6])],[(0,[z75,z2,z3,z71,z4,z5,z6]),(0,[z1,z2,z170,z3,z4,z5,z6]),(0,[z171,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z172,z5,z6])],[(0,[z0,z1,z2,z3,z136,z5,z6]),(0,[z1,z2,z3,z4,z5,z173,z6]),(0,[z1,z2,z3,z4,z5,z127,z26]),(0,[z100,z1,z2,z23,z4,z5,z6]),(1,[z141,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z174,z4,z5,z6])]],
   [[(1,[z1,z2,z175,z4,z5,z6]),(0,[z70,z1,z2,z3,z71,z5,z6]),(1,[z1,z2,z3,z176,z5,z6]),(0,[z1,z2,z177,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z178,z6])],[(0,[z1,z2,z14,z23,z4,z5,z6]),(0,[z1,z2,z3,z4,z179,z5,z6]),(1,[z1,z2,z3,z4,z5,z180]),(1,[z51,z1,z2,z110,z5,z6]),(0,[z1,z2,z3,z4,z5,z181,z6])],[(0,[z182,z1,z2,z3,z4,z5,z6]),(0,[z51,z101,z1,z2,z4,z5,z6]),(0,[z1,z2,z3,z183,z4,z5,z6])],[(0,[z1,z2,z3,z4,z184,z5,z6]),(0,[z1,z2,z8,z4,z24,z5,z6]),(0,[z185,z1,z2,z3,z4,z5,z6]),(1,[z1,z2,z3,z4,z5,z9]),(0,[z1,z2,z3,z4,z5,z186,z6]),(0,[z1,z2,z72,z3,z4,z5,z73]),(0,[z1,z2,z3,z4,z5,z6,z187])],[(1,[z68,z188,z3,z4,z5,z6]),(0,[z189,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z190,z6]),(0,[z1,z191,z2,z3,z4,z5,z6]),(1,[z1,z2,z3,z4,z5,z192]),(0,[z101,z1,z2,z3,z4,z52,z6])],[(0,[z1,z193,z2,z3,z4,z5,z6]),(0,[z194,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z195,z4,z5,z6]),(0,[z102,z120,z1,z2,z3,z4,z5]),(0,[z1,z2,z3,z33,z5,z140,z6])],[(0,[z38,z1,z2,z3,z4,z5,z26]),(0,[z1,z2,z23,z4,z5,z73,z6]),(0,[z1,z2,z196,z3,z4,z5,z6])],[(0,[z197,z1,z2,z23,z4,z5,z6]),(0,[z1,z2,z23,z4,z52,z5,z6]),(0,[z1,z2,z3,z176,z4,z5,z6]),(0,[z1,z2,z3,z4,z198,z110,z5])]],
   [[(0,[z19,z188,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z199,z4,z5,z6]),(0,[z1,z41,z2,z23,z4,z5,z6]),(0,[z1,z2,z3,z4,z52,z5,z6]),(0,[z1,z2,z200,z3,z4,z5,z6])],[(0,[z201,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z23,z4,z5,z65,z6]),(0,[z202,z1,z2,z3,z4,z5,z6]),(0,[z203,z1,z2,z3,z4,z5,z6]),(0,[z204,z1,z2,z3,z4,z5,z6])],[(0,[z60,z1,z2,z23,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z65,z6])],[(1,[z1,z2,z3,z4,z5,z205]),(0,[z1,z188,z2,z206,z4,z5,z6]),(0,[z1,z207,z2,z3,z4,z5,z6]),(0,[z1,z2,z23,z4,z5,z32,z6])],[(0,[z188,z2,z3,z71,z4,z5,z6]),(0,[z1,z2,z3,z4,z208,z5,z26]),(0,[z1,z2,z23,z4,z5,z6,z27]),(0,[z1,z2,z8,z33,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z32,z6]),(1,[z209,z2,z3,z4,z5,z6]),(0,[z210,z1,z2,z3,z4,z5,z9])],[(0,[z211,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z136,z24,z5,z6]),(0,[z1,z2,z212,z3,z4,z5,z6]),(0,[z1,z2,z3,z213,z4,z5,z6]),(0,[z214,z1,z2,z3,z4,z5,z6]),(0,[z101,z1,z2,z4,z5,z89,z6])],[(0,[z1,z2,z8,z4,z5,z89,z6]),(0,[z100,z1,z2,z3,z4,z5,z6]),(0,[z102,z1,z2,z3,z4,z5,z9]),(0,[z1,z215,z2,z3,z4,z5,z6])],[(0,[z70,z1,z2,z8,z4,z5,z6]),(0,[z57,z1,z2,z3,z24,z5,z6]),(0,[z100,z1,z2,z3,z216,z5,z6]),(0,[z1,z2,z3,z217,z4,z5,z26]),(0,[z1,z2,z3,z4,z5,z6,z218]),(0,[z1,z2,z3,z4,z104,z5,z219])]],
   [[(0,[z13,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z14,z3,z4,z5,z6]),(0,[z1,z2,z220,z23,z4,z5,z6]),(0,[z221,z1,z2,z3,z4,z5,z6]),(0,[z222,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z23,z4,z110,z5,z6]),(0,[z1,z141,z2,z3,z4,z5,z6])],[(0,[z88,z2,z37,z3,z4,z5,z6]),(0,[z1,z2,z223,z3,z4,z5,z6]),(0,[z1,z2,z3,z224,z4,z5,z6]),(0,[z2,z3,z4,z5,z65,z127,z6]),(0,[z88,z1,z2,z3,z4,z5,z9]),(0,[z1,z2,z3,z225,z4,z5,z6]),(1,[z1,z41,z3,z30,z5,z6]),(0,[z1,z2,z3,z4,z5,z226,z6])],[(0,[z1,z2,z23,z4,z5,z227,z6])],[(0,[z75,z60,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z127,z9]),(0,[z1,z2,z3,z4,z5,z227,z6]),(0,[z1,z29,z8,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z228])],[(0,[z1,z2,z37,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z229,z5,z6]),(0,[z230,z2,z3,z4,z5,z32,z6]),(0,[z1,z2,z3,z4,z231,z5,z6]),(0,[z1,z2,z116,z3,z4,z89,z6])],[(0,[z1,z2,z3,z39,z4,z5,z26]),(0,[z1,z232,z2,z3,z4,z5,z6]),(0,[z1,z2,z233,z4,z5,z73,z6])],[(0,[z1,z29,z2,z3,z4,z5,z26]),(0,[z57,z1,z2,z234,z4,z5,z6]),(1,[z1,z2,z3,z4,z235,z6]),(0,[z1,z2,z3,z123,z4,z5,z26]),(0,[z1,z2,z233,z4,z52,z5,z6]),(0,[z236,z1,z2,z3,z4,z5,z6]),(0,[z135,z1,z2,z3,z4,z5,z140])]],
   [[(0,[z1,z2,z237,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z17]),(0,[z1,z2,z3,z4,z238,z5,z6]),(0,[z1,z2,z3,z4,z239,z5,z26])],[(0,[z60,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z95])],[(0,[z1,z240,z2,z3,z4,z5,z6]),(0,[z241,z1,z2,z3,z4,z5,z6]),(0,[z242,z1,z2,z3,z4,z5,z6]),(1,[z1,z2,z3,z4,z243,z6]),(0,[z100,z244,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z245,z9]),(0,[z1,z2,z3,z4,z5,z6,z246])],[(0,[z1,z2,z8,z23,z4,z5,z6]),(0,[z247,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z248,z4,z5,z6]),(0,[z1,z2,z3,z249,z4,z5,z26]),(0,[z1,z250,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z117,z4,z5,z6])],[(0,[z251,z1,z2,z3,z4,z5,z6]),(1,[z0,z2,z3,z136,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z252]),(1,[z1,z2,z3,z4,z5,z253]),(0,[z120,z1,z2,z8,z4,z5,z6]),(0,[z1,z2,z72,z3,z4,z5,z26]),(0,[z254,z2,z3,z123,z4,z5,z6])],[(0,[z255,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z256,z6])],[(0,[z1,z2,z3,z4,z257,z5,z6]),(0,[z1,z2,z3,z258,z4,z5,z6]),(0,[z122,z1,z2,z3,z4,z5,z91])],[(0,[z75,z1,z2,z3,z4,z259,z6]),(0,[z188,z2,z3,z4,z5,z127,z6]),(0,[z1,z2,z260,z3,z4,z5,z6]),(1,[z261,z2,z3,z4,z5,z6]),(1,[z262,z2,z3,z4,z5,z6]),(1,[z1,z2,z3,z4,z5,z263]),(0,[z96,z1,z2,z3,z4,z5,z6]),(0,[z1,z264,z2,z3,z4,z5,z6])]],
   [[(0,[z68,z1,z2,z8,z4,z5,z6]),(0,[z265,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z266,z4,z5,z6]),(0,[z1,z2,z3,z233,z4,z5,z6]),(0,[z1,z2,z3,z267,z4,z5,z6]),(0,[z122,z1,z2,z72,z3,z4,z5])],[(0,[z75,z1,z2,z8,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z268,z6]),(0,[z1,z2,z3,z4,z5,z269,z6]),(0,[z1,z2,z3,z4,z208,z5,z9]),(0,[z19,z1,z2,z3,z4,z5,z26]),(1,[z1,z2,z169,z4,z5,z6]),(0,[z130,z1,z2,z3,z4,z5,z26]),(0,[z1,z2,z3,z4,z5,z26,z270]),(0,[z1,z2,z233,z4,z110,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z271])],[(0,[z60,z2,z3,z4,z5,z65,z6]),(0,[z1,z2,z23,z4,z5,z6,z26]),(0,[z1,z2,z23,z4,z5,z6,z150]),(0,[z1,z2,z8,z106,z4,z5,z6]),(0,[z100,z1,z2,z3,z4,z5,z9]),(0,[z1,z2,z3,z4,z104,z5,z26]),(0,[z1,z2,z3,z4,z5,z6,z272])],[(0,[z273,z1,z2,z3,z4,z5,z6]),(1,[z1,z2,z23,z4,z5,z6]),(0,[z1,z2,z3,z274,z4,z5,z6]),(0,[z100,z232,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z26]),(0,[z1,z2,z3,z4,z5,z6,z275]),(0,[z1,z2,z3,z4,z5,z6,z150]),(0,[z1,z2,z3,z4,z5,z276,z6])],[(0,[z1,z2,z3,z277,z4,z5,z6]),(0,[z18,z1,z2,z72,z3,z4,z5]),(0,[z1,z31,z2,z3,z4,z5,z26]),(0,[z1,z2,z3,z217,z4,z5,z9]),(0,[z101,z1,z2,z4,z5,z73,z6]),(0,[z278,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z279])],[(0,[z1,z2,z8,z4,z5,z73,z6]),(0,[z122,z1,z2,z3,z4,z104,z6])],[(0,[z1,z2,z8,z4,z52,z5,z6]),(0,[z1,z2,z280,z3,z4,z5,z6]),(0,[z1,z31,z2,z3,z4,z239,z6]),(0,[z1,z2,z3,z33,z4,z239,z6]),(0,[z1,z2,z3,z4,z5,z121,z26])],[(0,[z1,z2,z23,z281,z4,z5,z6]),(0,[z282,z1,z2,z3,z4,z5,z9])]],
   [[(0,[z75,z2,z3,z39,z4,z5,z6]),(0,[z1,z2,z3,z281,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z283,z6]),(0,[z1,z2,z3,z4,z5,z284,z6]),(0,[z1,z2,z3,z4,z5,z6,z285])],[(0,[z1,z2,z3,z4,z5,z286,z6]),(0,[z287,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z288,z3,z4,z5,z6]),(0,[z1,z41,z2,z3,z4,z5,z180]),(0,[z1,z2,z3,z4,z5,z289,z6]),(0,[z101,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z8,z3,z4,z5,z6]),(0,[z1,z2,z8,z4,z5,z32,z6]),(0,[z197,z1,z2,z3,z4,z5,z9]),(1,[z34,z2,z3,z4,z5,z6]),(1,[z1,z2,z3,z4,z5,z181]),(0,[z290,z1,z2,z3,z4,z5,z6])],[(0,[z291,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z39,z4,z5,z9]),(0,[z1,z2,z3,z4,z5,z292,z6]),(0,[z1,z2,z3,z293,z4,z5,z6]),(0,[z1,z2,z3,z4,z294,z5,z6]),(0,[z295,z1,z2,z3,z4,z5,z6]),(0,[z1,z41,z2,z3,z4,z5,z9]),(0,[z296,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z297]),(0,[z1,z2,z3,z4,z5,z298,z6]),(0,[z81,z1,z2,z4,z5,z6,z270])],[(0,[z1,z2,z3,z4,z5,z6,z299]),(0,[z188,z2,z3,z4,z208,z5,z6]),(0,[z300,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z219,z6,z91])],[(0,[z1,z2,z3,z4,z301,z5,z6]),(0,[z1,z2,z3,z4,z239,z5,z9])],[(0,[z68,z188,z2,z3,z4,z5,z6]),(0,[z302,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z303,z3,z4,z5,z6]),(0,[z102,z1,z2,z23,z4,z5,z6]),(0,[z1,z2,z304,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z305]),(0,[z1,z2,z3,z4,z306,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z307]),(0,[z1,z2,z3,z4,z5,z6,z308])],[(0,[z88,z19,z2,z3,z4,z5,z6]),(0,[z309,z1,z2,z3,z4,z5,z6]),(0,[z310,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z117,z4,z5,z9]),(0,[z1,z2,z3,z4,z5,z6,z311]),(0,[z1,z2,z3,z4,z5,z312,z6]),(0,[z120,z122,z1,z2,z3,z4,z5])]],
   [[(0,[z1,z2,z313,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z314,z5,z6]),(0,[z1,z2,z8,z4,z110,z5,z6]),(0,[z57,z315,z2,z3,z4,z5,z6])],[(0,[z88,z68,z2,z3,z4,z5,z6]),(0,[z316,z1,z2,z3,z4,z5,z6])],[(1,[z1,z2,z3,z4,z5,z6]),(0,[z0,z1,z2,z8,z4,z5,z6]),(0,[z1,z317,z2,z8,z4,z5,z6]),(1,[z2,z3,z4,z179,z5,z6])],[(0,[z1,z2,z3,z4,z5,z318,z6]),(0,[z1,z2,z23,z4,z319,z5,z6]),(0,[z1,z2,z3,z23,z4,z5,z26]),(1,[z1,z2,z3,z216,z5,z6]),(0,[z1,z2,z220,z3,z4,z5,z9]),(0,[z1,z320,z2,z3,z4,z5,z6]),(1,[z296,z1,z2,z3,z4,z5])],[(0,[z1,z2,z3,z321,z4,z5,z6]),(1,[z18,z2,z3,z4,z5,z127]),(0,[z1,z2,z3,z4,z319,z5,z6]),(1,[z1,z2,z322,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z323,z6]),(0,[z1,z2,z3,z233,z4,z5,z9])],[(0,[z59,z1,z2,z3,z4,z5,z6]),(0,[z19,z1,z2,z3,z4,z5,z126])],[(0,[z188,z2,z3,z39,z4,z5,z6]),(0,[z324,z1,z2,z3,z4,z5,z6]),(0,[z70,z1,z2,z3,z4,z5,z26]),(0,[z1,z2,z23,z4,z5,z6,z126]),(0,[z1,z2,z325,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z326,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z180])],[(0,[z1,z2,z3,z327,z4,z5,z6]),(0,[z1,z2,z3,z4,z328,z5,z6]),(0,[z19,z1,z2,z3,z4,z5,z127]),(0,[z1,z2,z8,z4,z5,z140,z6]),(0,[z1,z2,z3,z4,z104,z5,z9]),(0,[z1,z2,z3,z329,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z330])]],
   [[(0,[z1,z2,z3,z4,z5,z331,z6]),(0,[z1,z2,z8,z4,z5,z6,z91]),(1,[z1,z2,z332,z4,z5,z6])],[(0,[z1,z2,z3,z4,z333,z5,z6]),(0,[z1,z188,z2,z8,z4,z5,z6]),(0,[z1,z2,z334,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z192]),(0,[z1,z2,z3,z4,z335,z5,z6]),(0,[z102,z1,z2,z4,z52,z5,z6]),(0,[z1,z2,z3,z4,z336,z5,z6])],[(0,[z1,z2,z337,z3,z4,z5,z6]),(0,[z1,z2,z338,z3,z4,z5,z6]),(0,[z1,z2,z3,z339,z4,z5,z6])],[(0,[z210,z1,z2,z3,z4,z5,z6]),(0,[z340,z1,z2,z3,z4,z5,z6]),(0,[z38,z1,z2,z23,z4,z5,z6]),(0,[z1,z8,z3,z23,z4,z5,z6]),(0,[z57,z1,z2,z8,z4,z5,z6]),(0,[z1,z2,z3,z4,z341,z5,z6]),(0,[z1,z2,z3,z4,z5,z9,z26]),(0,[z1,z2,z3,z4,z5,z9,z150]),(0,[z1,z2,z3,z4,z5,z121,z9]),(0,[z1,z2,z3,z4,z5,z6,z342]),(0,[z1,z2,z3,z5,z121,z6,z270])],[(0,[z88,z13,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z343,z6]),(0,[z1,z317,z2,z344,z4,z5,z6]),(0,[z345,z1,z2,z3,z4,z5,z6]),(0,[z120,z1,z2,z72,z3,z4,z5])],[(1,[z1,z2,z3,z4,z5,z346]),(0,[z1,z347,z2,z3,z4,z5,z6]),(0,[z1,z2,z39,z23,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z348]),(1,[z1,z2,z3,z4,z5,z349]),(1,[z350,z2,z3,z4,z5,z6]),(0,[z351,z1,z2,z3,z4,z5,z6]),(0,[z102,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z6,z352]),(0,[z51,z1,z2,z8,z4,z5,z6]),(1,[z244,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z161]),(0,[z1,z2,z3,z123,z4,z5,z270]),(1,[z1,z2,z3,z123,z5,z121])],[(0,[z1,z2,z8,z4,z136,z5,z6]),(0,[z1,z2,z8,z4,z5,z219,z6]),(0,[z1,z2,z3,z4,z353,z5,z9]),(0,[z1,z2,z3,z4,z5,z181,z89])]],
   [[(0,[z0,z188,z2,z3,z4,z5,z6]),(0,[z88,z2,z3,z4,z5,z127,z6]),(0,[z1,z2,z3,z4,z354,z5,z6]),(0,[z355,z1,z2,z3,z4,z5,z6]),(1,[z1,z2,z8,z4,z5,z26]),(0,[z1,z2,z3,z30,z4,z5,z6])],[(0,[z88,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z356,z6]),(0,[z1,z2,z8,z4,z5,z6,z26]),(0,[z1,z2,z3,z4,z5,z6,z357])],[(0,[z19,z2,z3,z4,z136,z5,z6]),(0,[z358,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z23,z4,z5,z127,z6]),(0,[z94,z1,z2,z8,z4,z5,z6]),(0,[z130,z1,z317,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z359,z6])],[(0,[z1,z2,z3,z360,z4,z5,z6]),(0,[z1,z2,z3,z361,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z127,z6]),(0,[z122,z1,z2,z8,z4,z5,z6]),(0,[z120,z1,z2,z3,z4,z5,z26]),(0,[z362,z1,z2,z3,z4,z5,z9])],[(0,[z1,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z363,z3,z4,z5,z6]),(0,[z1,z2,z3,z71,z4,z5,z9]),(0,[z1,z364,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z365,z6]),(0,[z1,z2,z3,z4,z366,z5,z6]),(0,[z1,z2,z3,z367,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z368,z6]),(0,[z1,z29,z2,z3,z4,z5,z253])],[(0,[z1,z2,z3,z4,z5,z9,z305])],[(0,[z68,z1,z2,z3,z4,z5,z26]),(0,[z18,z1,z2,z8,z4,z5,z6]),(1,[z232,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z9,z311]),(0,[z1,z92,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z369,z4,z5,z6]),(0,[z101,z1,z2,z3,z4,z89,z6]),(0,[z370,z1,z2,z3,z4,z5,z6]),(0,[z102,z1,z2,z3,z4,z104,z5])]],
   [[(0,[z75,z1,z2,z3,z4,z5,z26]),(0,[z100,z1,z2,z3,z4,z32,z6])],[(0,[z1,z2,z23,z4,z5,z6,z270]),(0,[z1,z2,z2,z8,z4,z5,z6]),(0,[z1,z371,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z245,z6]),(0,[z1,z2,z3,z4,z5,z6,z372]),(0,[z1,z2,z3,z123,z5,z121,z6])],[(0,[z373,z1,z2,z3,z4,z5,z6]),(1,[z13,z2,z14,z4,z5,z6]),(0,[z374,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z375,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z270])],[(0,[z1,z2,z3,z69,z39,z4,z5]),(0,[z1,z2,z3,z117,z30,z5,z6])],[(0,[z1,z2,z3,z4,z5,z376,z6]),(0,[z1,z2,z377,z23,z4,z5,z6]),(0,[z1,z29,z2,z23,z4,z5,z6]),(0,[z1,z2,z3,z378,z4,z5,z6])],[(1,[z1,z2,z3,z4,z379,z6]),(0,[z1,z2,z3,z4,z5,z380,z6]),(0,[z1,z381,z2,z3,z4,z5,z6]),(0,[z88,z2,z3,z4,z208,z5,z6]),(0,[z1,z382,z2,z3,z4,z5,z6]),(0,[z230,z1,z2,z3,z4,z5,z6]),(0,[z51,z1,z2,z220,z4,z5,z6])],[(0,[z1,z2,z383,z3,z4,z5,z6]),(1,[z70,z2,z3,z71,z5,z6]),(0,[z384,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z385,z5,z6]),(0,[z135,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z117,z33,z4,z6]),(0,[z1,z2,z3,z386,z4,z5,z6]),(1,[z1,z2,z4,z5,z6,z285])],[(0,[z1,z2,z23,z4,z208,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z387]),(0,[z1,z2,z3,z4,z5,z9,z126])]],
   [[(0,[z2,z3,z4,z136,z5,z127,z6]),(0,[z1,z2,z3,z4,z208,z5,z6]),(0,[z1,z2,z3,z4,z5,z388,z6]),(0,[z389,z1,z2,z23,z4,z5,z6]),(0,[z1,z2,z3,z4,z390,z5,z6]),(0,[z1,z2,z3,z4,z5,z391,z6]),(0,[z1,z2,z4,z5,z392,z140,z6])],[(0,[z393,z1,z2,z3,z4,z5,z6]),(0,[z94,z1,z29,z3,z4,z5,z6]),(0,[z1,z2,z72,z23,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z253]),(0,[z1,z2,z3,z4,z5,z6,z394]),(0,[z395,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z6,z396]),(0,[z1,z2,z23,z217,z4,z5,z6]),(0,[z397,z1,z2,z3,z4,z5,z6]),(0,[z57,z1,z2,z3,z4,z5,z398]),(0,[z1,z2,z399,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z400,z5,z6]),(1,[z1,z2,z3,z4,z104,z219])],[(0,[z1,z2,z3,z4,z5,z205,z6]),(0,[z401,z1,z2,z23,z4,z5,z6]),(1,[z2,z8,z106,z4,z5,z6]),(0,[z1,z2,z8,z107,z4,z5,z6]),(0,[z57,z1,z2,z402,z4,z5,z6]),(0,[z1,z31,z3,z4,z239,z5,z6]),(0,[z1,z2,z3,z217,z4,z5,z6])],[(0,[z1,z2,z3,z403,z4,z5,z6]),(0,[z404,z1,z2,z23,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z263]),(0,[z1,z2,z3,z30,z4,z5,z9]),(0,[z1,z31,z2,z3,z4,z5,z405]),(0,[z1,z2,z3,z406,z4,z5,z6]),(0,[z102,z1,z2,z4,z5,z6,z150]),(0,[z1,z2,z3,z4,z5,z392,z6])],[(1,[z1,z2,z67,z4,z5,z6]),(0,[z1,z188,z2,z3,z4,z5,z17]),(0,[z1,z2,z8,z4,z5,z6,z126]),(0,[z1,z2,z220,z3,z233,z5,z6]),(0,[z1,z2,z3,z4,z407,z5,z6]),(0,[z120,z1,z2,z3,z5,z6,z270])],[(0,[z19,z1,z2,z23,z4,z5,z6]),(0,[z130,z1,z2,z23,z4,z5,z6]),(0,[z282,z1,z2,z3,z4,z5,z6]),(0,[z57,z1,z41,z3,z4,z5,z6]),(1,[z1,z2,z408,z4,z5,z6]),(0,[z409,z1,z2,z3,z4,z5,z6]),(0,[z2,z3,z4,z104,z5,z410,z6])],[(0,[z411,z1,z2,z3,z4,z5,z6]),(0,[z75,z0,z2,z3,z4,z5,z6]),(0,[z88,z2,z3,z39,z4,z5,z6]),(0,[z412,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z413,z6]),(0,[z1,z2,z3,z4,z5,z219,z26]),(0,[z122,z1,z2,z3,z4,z5,z219])]],
   [[(0,[z1,z2,z3,z4,z414,z5,z6]),(0,[z2,z3,z71,z4,z136,z5,z6]),(0,[z19,z2,z3,z4,z5,z6,z126]),(0,[z1,z2,z3,z4,z415,z5,z6]),(0,[z416,z1,z2,z3,z4,z5,z6])],[(0,[z197,z1,z2,z3,z4,z5,z6]),(0,[z0,z1,z2,z3,z4,z5,z26]),(0,[z1,z31,z2,z23,z4,z5,z6]),(0,[z1,z317,z2,z3,z4,z5,z26]),(0,[z54,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z39,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z417,z6]),(0,[z1,z41,z2,z3,z4,z5,z6]),(1,[z1,z2,z3,z4,z5,z413]),(1,[z2,z3,z4,z5,z289,z6]),(0,[z418,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z419,z3,z4,z5,z6])],[(0,[z1,z2,z3,z123,z4,z5,z6])],[(0,[z68,z1,z2,z3,z4,z5,z9]),(0,[z1,z2,z3,z4,z239,z5,z6]),(0,[z1,z2,z420,z3,z4,z5,z6])],[(0,[z421,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z23,z117,z4,z5,z6]),(0,[z1,z2,z422,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z235,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z423])],[(0,[z38,z1,z2,z3,z4,z5,z9]),(0,[z13,z1,z2,z39,z4,z5,z6]),(0,[z424,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z24,z5,z26]),(0,[z1,z2,z3,z4,z5,z425,z6]),(0,[z1,z2,z3,z4,z426,z5,z6])],[(0,[z389,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z249,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z50]),(0,[z1,z2,z72,z3,z4,z5,z150])]],
   [[(1,[z1,z2,z427,z4,z5,z6]),(0,[z1,z188,z2,z3,z4,z5,z26]),(0,[z428,z1,z2,z3,z4,z5,z6]),(1,[z1,z2,z234,z4,z5,z6]),(1,[z1,z2,z177,z4,z5,z6]),(1,[z1,z2,z3,z4,z5,z429]),(0,[z1,z2,z3,z4,z430,z5,z6]),(0,[z1,z431,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z432,z4,z5,z6]),(0,[z1,z2,z3,z433,z4,z5,z6]),(0,[z1,z2,z434,z8,z4,z5,z6]),(0,[z1,z2,z3,z435,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z436])],[(0,[z437,z1,z2,z3,z4,z5,z6]),(0,[z13,z1,z2,z8,z4,z5,z6]),(0,[z1,z2,z23,z233,z4,z5,z6]),(0,[z57,z1,z2,z3,z4,z5,z26]),(0,[z1,z2,z3,z4,z5,z9,z270]),(0,[z1,z2,z220,z3,z4,z5,z6]),(0,[z1,z2,z3,z117,z4,z140,z6])],[(0,[z404,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z438,z4,z5,z6]),(0,[z1,z2,z3,z117,z217,z5,z6]),(0,[z1,z2,z3,z4,z5,z439,z140])],[(0,[z1,z3,z4,z239,z5,z32,z6]),(0,[z1,z2,z3,z4,z440,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z441])],[(0,[z75,z1,z2,z3,z4,z5,z205]),(0,[z1,z2,z23,z4,z104,z5,z6]),(0,[z442,z1,z2,z3,z4,z5,z26]),(0,[z51,z1,z2,z3,z4,z5,z26])],[(0,[z1,z2,z3,z4,z5,z443,z6]),(0,[z0,z1,z2,z3,z71,z5,z6]),(0,[z1,z2,z3,z4,z65,z32,z6]),(0,[z102,z19,z1,z2,z3,z4,z5]),(0,[z1,z444,z2,z3,z4,z5,z6]),(0,[z100,z1,z3,z4,z5,z32,z6]),(0,[z54,z1,z2,z4,z5,z140,z6]),(0,[z1,z2,z445,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z104,z5,z6])],[(0,[z1,z2,z37,z8,z4,z5,z6]),(0,[z38,z1,z2,z14,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z6]),(0,[z1,z2,z3,z4,z446,z5,z6]),(0,[z1,z2,z3,z4,z5,z447,z6]),(0,[z1,z2,z3,z33,z4,z5,z26]),(0,[z448,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z449]),(0,[z1,z2,z450,z3,z4,z5,z6])]],
   [[(0,[z451,z1,z2,z3,z4,z5,z6]),(0,[z68,z2,z3,z4,z136,z5,z6]),(0,[z452,z1,z2,z8,z4,z5,z6]),(0,[z1,z2,z8,z4,z5,z6,z270]),(0,[z1,z2,z3,z344,z4,z5,z6]),(0,[z1,z317,z3,z4,z5,z9,z6])],[(0,[z94,z1,z2,z3,z4,z5,z26]),(0,[z1,z2,z23,z4,z5,z121,z6]),(0,[z1,z2,z3,z4,z5,z89,z26]),(0,[z296,z1,z2,z3,z4,z5,z89]),(0,[z1,z2,z3,z4,z5,z453,z6])],[(0,[z70,z68,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z454,z5,z6]),(0,[z1,z2,z3,z4,z5,z455,z6]),(0,[z456,z1,z2,z3,z4,z5,z6]),(0,[z122,z1,z2,z3,z4,z5,z26]),(0,[z1,z2,z3,z4,z5,z121,z6]),(0,[z120,z1,z2,z3,z4,z5,z270])],[(0,[z70,z1,z2,z23,z4,z5,z6]),(0,[z1,z2,z8,z4,z5,z65,z6]),(0,[z1,z2,z3,z4,z457,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z458]),(0,[z1,z2,z459,z3,z4,z5,z6])],[(0,[z460,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z461]),(0,[z1,z2,z3,z4,z5,z462,z6]),(0,[z1,z2,z3,z463,z4,z5,z9])],[(1,[z1,z2,z3,z4,z5,z464]),(0,[z465,z1,z2,z3,z4,z5,z6]),(0,[z1,z466,z2,z3,z4,z5,z6]),(0,[z1,z2,z467,z3,z4,z5,z6]),(0,[z209,z1,z2,z3,z4,z5,z26]),(0,[z1,z2,z3,z4,z468,z5,z6]),(0,[z1,z2,z3,z469,z4,z5,z6])],[(0,[z1,z2,z427,z3,z4,z5,z6]),(0,[z470,z1,z2,z3,z4,z5,z6]),(0,[z19,z2,z3,z4,z5,z65,z6]),(0,[z18,z1,z2,z3,z4,z5,z26]),(0,[z1,z317,z2,z3,z4,z5,z9]),(0,[z1,z2,z3,z4,z353,z5,z6]),(1,[z471,z2,z3,z4,z5,z6])],[(0,[z472,z1,z2,z3,z4,z5,z6]),(0,[z1,z29,z2,z3,z4,z5,z9]),(0,[z473,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z123,z4,z5,z9]),(0,[z1,z474,z2,z3,z4,z5,z6])]],
   [[(0,[z1,z2,z3,z475,z4,z5,z6]),(0,[z13,z188,z2,z3,z4,z5,z6]),(0,[z88,z2,z3,z71,z4,z5,z6]),(0,[z1,z2,z131,z3,z4,z5,z6]),(0,[z1,z2,z2,z3,z4,z5,z26]),(0,[z1,z2,z116,z3,z4,z5,z26])],[(0,[z476,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z477,z5,z6]),(0,[z1,z2,z3,z478,z4,z5,z6]),(0,[z261,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z479,z4,z5,z6]),(0,[z28,z1,z2,z4,z5,z6,z91])],[(0,[z75,z1,z2,z3,z475,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z346]),(0,[z1,z188,z2,z175,z4,z5,z6]),(0,[z1,z2,z23,z71,z4,z5,z6]),(0,[z2,z3,z4,z179,z24,z5,z6]),(0,[z362,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z104,z219,z6])],[(0,[z1,z2,z3,z71,z4,z5,z6]),(0,[z480,z1,z2,z3,z4,z5,z6]),(0,[z481,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z482,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z483]),(0,[z1,z2,z3,z484,z4,z5,z6]),(1,[z100,z1,z3,z4,z32,z6]),(0,[z1,z2,z72,z3,z4,z5,z9]),(1,[z122,z1,z2,z3,z4,z91])],[(0,[z1,z188,z2,z3,z4,z5,z9]),(0,[z485,z1,z2,z3,z4,z5,z6]),(0,[z100,z1,z2,z114,z4,z5,z6]),(0,[z1,z2,z3,z486,z4,z5,z6])],[(0,[z1,z2,z3,z4,z487,z5,z6]),(0,[z2,z3,z39,z4,z5,z65,z6]),(0,[z0,z70,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z488,z5,z6]),(0,[z1,z2,z3,z402,z4,z5,z6]),(1,[z1,z2,z213,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z489,z6])],[(0,[z2,z3,z4,z208,z5,z65,z6])]],
   [[(0,[z120,z1,z2,z23,z4,z5,z6]),(1,[z92,z2,z3,z4,z5,z6])],[(0,[z88,z1,z2,z3,z4,z65,z6]),(0,[z88,z1,z2,z3,z4,z208,z6]),(0,[z1,z2,z490,z3,z4,z5,z6]),(0,[z19,z1,z2,z3,z4,z5,z9]),(0,[z1,z2,z3,z4,z5,z398,z6]),(0,[z1,z2,z3,z4,z491,z5,z6]),(0,[z100,z1,z2,z3,z4,z5,z413]),(0,[z130,z1,z2,z3,z4,z5,z9]),(0,[z492,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z493,z6])],[(0,[z0,z2,z3,z4,z136,z5,z6]),(0,[z1,z2,z3,z494,z4,z5,z6]),(0,[z495,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z496,z5,z6]),(0,[z1,z2,z497,z3,z4,z5,z6]),(0,[z101,z1,z2,z8,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z498,z26]),(0,[z182,z1,z2,z3,z4,z5,z26]),(1,[z120,z1,z2,z3,z5,z270])],[(0,[z499,z1,z2,z3,z4,z5,z6]),(0,[z68,z1,z2,z23,z4,z5,z6]),(0,[z1,z2,z8,z117,z4,z5,z6]),(0,[z1,z31,z2,z3,z4,z5,z9]),(0,[z1,z2,z3,z33,z4,z5,z9]),(0,[z1,z2,z3,z4,z5,z500,z6]),(0,[z1,z2,z4,z5,z73,z6,z150]),(1,[z2,z3,z4,z5,z410,z6])],[(0,[z75,z1,z2,z23,z4,z5,z6]),(0,[z1,z2,z23,z4,z501,z5,z6]),(0,[z295,z1,z2,z8,z4,z5,z6]),(0,[z1,z2,z3,z4,z216,z5,z6])],[(0,[z1,z2,z3,z4,z501,z5,z6]),(0,[z502,z1,z2,z3,z4,z5,z6]),(0,[z55,z1,z2,z8,z4,z5,z6]),(0,[z1,z41,z2,z408,z4,z5,z6]),(1,[z1,z2,z3,z217,z140,z6])],[(0,[z1,z2,z3,z503,z4,z5,z6]),(0,[z1,z2,z3,z4,z504,z5,z6]),(0,[z1,z2,z234,z3,z4,z5,z6]),(0,[z154,z2,z3,z4,z24,z5,z6]),(0,[z1,z2,z3,z505,z4,z5,z6]),(0,[z122,z1,z2,z3,z4,z5,z9]),(0,[z506,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z33,z217,z4,z6]),(0,[z1,z2,z3,z4,z5,z507,z6]),(0,[z1,z2,z3,z117,z33,z5,z6]),(0,[z1,z2,z3,z4,z508,z5,z6])]],
   [[(0,[z509,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z478,z23,z4,z5,z6]),(0,[z1,z2,z304,z8,z4,z5,z6]),(0,[z1,z41,z2,z3,z24,z5,z6]),(0,[z510,z1,z2,z3,z4,z5,z26]),(0,[z1,z2,z3,z4,z5,z73,z26]),(0,[z1,z2,z3,z511,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z512]),(0,[z101,z1,z2,z233,z4,z5,z6])],[(0,[z2,z14,z3,z39,z4,z5,z6]),(0,[z1,z2,z8,z233,z4,z5,z6]),(0,[z1,z2,z3,z4,z52,z5,z26]),(0,[z350,z1,z2,z3,z4,z5,z6])],[(0,[z513,z1,z2,z3,z4,z5,z6]),(0,[z18,z1,z2,z3,z4,z5,z126]),(0,[z1,z2,z23,z30,z4,z5,z6]),(0,[z1,z514,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z515,z5,z6]),(0,[z102,z1,z2,z3,z123,z4,z5]),(0,[z1,z2,z3,z4,z5,z6,z516])],[(0,[z517,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z65,z26]),(0,[z1,z2,z3,z518,z4,z5,z6]),(0,[z519,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z332,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z520,z9]),(0,[z521,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z522,z6]),(0,[z2,z3,z71,z4,z5,z65,z6]),(0,[z1,z2,z3,z4,z523,z5,z6]),(0,[z18,z1,z2,z3,z4,z5,z127]),(0,[z1,z2,z8,z4,z5,z6,z150]),(0,[z1,z2,z3,z117,z24,z5,z6]),(1,[z1,z2,z248,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z524,z9]),(0,[z1,z2,z3,z525,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z32,z26]),(1,[z209,z2,z3,z4,z5,z26]),(0,[z1,z2,z2,z3,z4,z5,z9]),(0,[z526,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z527,z4,z5,z6])],[(0,[z88,z60,z2,z3,z4,z5,z6]),(1,[z88,z2,z3,z4,z208,z6]),(0,[z1,z2,z528,z23,z4,z5,z6])],[(0,[z1,z2,z3,z4,z529,z5,z6])]],
   [[(0,[z38,z13,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z530,z5,z6])],[(0,[z13,z1,z2,z3,z4,z5,z26]),(0,[z100,z1,z2,z3,z4,z239,z6]),(0,[z531,z1,z2,z3,z4,z5,z6])],[(0,[z532,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z208,z32,z6]),(0,[z1,z41,z2,z3,z30,z5,z6]),(0,[z1,z2,z3,z4,z5,z533,z6])],[(0,[z68,z1,z2,z3,z4,z5,z6]),(0,[z534,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z23,z4,z5,z9]),(0,[z1,z315,z2,z3,z4,z5,z6]),(0,[z57,z1,z2,z3,z4,z235,z6]),(0,[z1,z2,z3,z4,z110,z5,z26]),(0,[z535,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z116,z8,z4,z5,z6])],[(0,[z38,z1,z2,z3,z4,z5,z6]),(0,[z2,z3,z39,z4,z136,z5,z6]),(0,[z1,z2,z3,z536,z4,z5,z6])],[(0,[z537,z1,z2,z3,z4,z5,z6]),(0,[z70,z2,z37,z3,z4,z5,z6]),(0,[z1,z2,z37,z3,z4,z5,z26]),(0,[z0,z1,z2,z23,z4,z5,z6]),(0,[z70,z1,z2,z3,z4,z5,z9]),(0,[z1,z317,z2,z23,z4,z5,z6]),(0,[z1,z2,z3,z538,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z410,z6]),(0,[z1,z2,z3,z539,z4,z5,z6])],[(0,[z540,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z541,z4,z5,z6]),(0,[z1,z542,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z543,z4,z5,z6])]],
   [[(0,[z1,z2,z544,z3,z4,z5,z6]),(1,[z1,z31,z3,z4,z239,z6]),(0,[z209,z2,z3,z4,z5,z6,z26]),(0,[z545,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z8,z71,z4,z5,z6]),(0,[z1,z546,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z349,z6])],[(0,[z1,z2,z3,z4,z5,z140,z26]),(0,[z1,z2,z3,z547,z4,z5,z6])],[(0,[z88,z1,z2,z8,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z128,z6]),(0,[z57,z1,z2,z3,z4,z5,z263]),(1,[z230,z2,z3,z4,z5,z6]),(1,[z2,z3,z4,z5,z62,z26]),(0,[z1,z2,z3,z4,z5,z9,z9]),(0,[z1,z2,z3,z4,z5,z6,z548]),(0,[z1,z2,z3,z4,z5,z549,z6])],[(0,[z68,z2,z3,z4,z5,z65,z6]),(0,[z60,z1,z2,z3,z4,z208,z6]),(0,[z60,z1,z2,z3,z4,z65,z6]),(0,[z1,z2,z3,z4,z239,z65,z6]),(0,[z2,z8,z3,z106,z4,z5,z6]),(0,[z102,z1,z2,z233,z4,z5,z6])],[(0,[z1,z188,z2,z23,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z429]),(0,[z1,z2,z3,z4,z5,z73,z9])],[(0,[z1,z550,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z551]),(0,[z1,z31,z2,z3,z4,z5,z429]),(0,[z1,z2,z3,z118,z4,z5,z6])],[(0,[z75,z1,z2,z3,z4,z5,z346]),(0,[z1,z2,z3,z175,z4,z5,z6]),(0,[z57,z1,z2,z23,z4,z5,z6]),(0,[z1,z2,z3,z552,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z553,z6]),(0,[z102,z1,z2,z72,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z554]),(0,[z1,z2,z3,z4,z555,z5,z6]),(0,[z1,z2,z3,z4,z5,z556,z6])]],
   [[(0,[z557,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z144,z6]),(1,[z1,z2,z8,z4,z5,z9]),(0,[z2,z3,z4,z5,z6,z62,z26]),(0,[z1,z2,z3,z4,z5,z9,z512]),(0,[z1,z2,z3,z4,z5,z6,z558])],[(1,[z1,z2,z206,z4,z5,z6]),(0,[z1,z2,z3,z71,z24,z5,z6]),(1,[z1,z8,z23,z4,z5,z6]),(1,[z1,z2,z114,z4,z5,z6]),(0,[z1,z2,z3,z4,z32,z140,z6]),(0,[z2,z3,z33,z559,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z560,z6]),(0,[z1,z2,z3,z4,z136,z5,z26]),(0,[z51,z1,z2,z23,z4,z5,z6]),(0,[z261,z2,z8,z3,z4,z5,z6]),(1,[z1,z2,z3,z4,z5,z561]),(0,[z1,z2,z3,z30,z5,z140,z6]),(0,[z1,z2,z3,z217,z4,z140,z6]),(0,[z1,z2,z3,z4,z5,z439,z6])],[(0,[z562,z1,z2,z3,z4,z5,z6]),(1,[z1,z2,z3,z4,z5,z398]),(0,[z1,z2,z3,z563,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z564,z6]),(0,[z1,z2,z3,z463,z4,z5,z6]),(0,[z120,z1,z2,z3,z4,z5,z9]),(1,[z2,z3,z559,z4,z5,z6])],[(1,[z1,z2,z3,z36,z5,z6]),(1,[z1,z2,z23,z4,z5,z26]),(0,[z100,z1,z2,z3,z4,z5,z133]),(0,[z51,z1,z2,z3,z233,z5,z6])],[(0,[z1,z2,z23,z123,z4,z5,z6]),(0,[z1,z317,z2,z3,z4,z5,z6]),(1,[z1,z317,z3,z4,z5,z9]),(0,[z565,z1,z2,z3,z4,z5,z9]),(0,[z102,z1,z2,z3,z4,z5,z73]),(0,[z1,z2,z3,z4,z5,z6,z566]),(0,[z567,z1,z2,z3,z4,z5,z6])],[(0,[z1,z29,z2,z3,z4,z5,z6]),(0,[z94,z1,z2,z23,z4,z5,z6]),(0,[z1,z2,z23,z4,z239,z5,z6]),(0,[z1,z41,z2,z213,z4,z5,z6]),(0,[z1,z2,z3,z4,z568,z5,z6]),(0,[z1,z2,z3,z4,z5,z569,z6]),(0,[z1,z2,z72,z4,z5,z73,z6]),(0,[z1,z2,z3,z570,z4,z5,z6])],[(0,[z122,z1,z2,z23,z4,z5,z6]),(0,[z1,z2,z571,z3,z4,z5,z6]),(0,[z1,z572,z2,z3,z4,z5,z6])]],
   [[(0,[z75,z2,z37,z3,z4,z5,z6]),(0,[z75,z1,z2,z3,z4,z5,z9]),(0,[z1,z2,z3,z4,z573,z5,z6]),(0,[z1,z2,z3,z4,z5,z574,z6]),(0,[z2,z3,z4,z136,z208,z5,z6]),(0,[z1,z2,z575,z3,z4,z5,z6]),(0,[z576,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z577,z23,z4,z5,z6]),(0,[z1,z2,z3,z4,z110,z5,z9]),(0,[z578,z1,z2,z3,z4,z5,z6]),(0,[z1,z579,z2,z3,z4,z5,z6]),(1,[z1,z2,z4,z5,z6,z330])],[(0,[z1,z580,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z581,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z582]),(0,[z1,z2,z8,z30,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z583])],[(0,[z1,z2,z3,z30,z136,z5,z6]),(0,[z1,z2,z212,z8,z4,z5,z6]),(0,[z1,z584,z2,z3,z4,z5,z6]),(0,[z101,z1,z2,z3,z4,z5,z26]),(0,[z102,z122,z1,z2,z3,z4,z5])],[(0,[z38,z2,z3,z39,z4,z5,z6]),(0,[z1,z2,z3,z71,z30,z5,z6]),(0,[z1,z2,z585,z3,z4,z5,z6]),(0,[z18,z1,z2,z23,z4,z5,z6]),(0,[z100,z1,z2,z8,z4,z5,z6]),(0,[z1,z2,z3,z4,z239,z140,z6]),(0,[z1,z317,z2,z332,z4,z5,z6]),(0,[z1,z2,z72,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z586,z5,z6])],[(0,[z1,z188,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z587,z6]),(0,[z1,z2,z3,z4,z588,z5,z6]),(0,[z1,z2,z8,z4,z5,z127,z6]),(0,[z51,z1,z2,z4,z5,z73,z6]),(0,[z1,z2,z3,z4,z5,z589,z6])],[(0,[z1,z2,z3,z4,z5,z6,z590]),(0,[z1,z2,z14,z8,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z591,z6]),(0,[z1,z2,z2,z23,z4,z5,z6]),(0,[z1,z2,z116,z23,z4,z5,z6]),(0,[z401,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z62,z26]),(0,[z1,z2,z72,z3,z123,z4,z5]),(0,[z1,z2,z3,z4,z5,z6,z592])],[(0,[z0,z2,z3,z4,z5,z65,z6]),(0,[z1,z2,z3,z4,z5,z593,z6]),(1,[z81,z1,z2,z4,z5,z6]),(0,[z1,z594,z2,z3,z4,z5,z6]),(0,[z28,z1,z2,z3,z4,z5,z6])],[(0,[z75,z1,z2,z3,z4,z379,z6]),(0,[z1,z2,z3,z4,z5,z140,z9]),(0,[z1,z595,z2,z3,z4,z5,z6])]],
   [[(0,[z19,z1,z2,z3,z4,z5,z6]),(0,[z102,z18,z1,z2,z3,z4,z5]),(0,[z282,z1,z2,z8,z4,z5,z6]),(0,[z130,z1,z2,z3,z4,z5,z6]),(0,[z1,z596,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z597,z4,z5,z6]),(0,[z1,z2,z3,z123,z4,z104,z5])],[(0,[z442,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z598,z4,z5,z6]),(0,[z157,z1,z2,z23,z4,z5,z6]),(0,[z1,z29,z2,z3,z4,z5,z349]),(0,[z78,z1,z2,z3,z4,z5,z26]),(1,[z101,z1,z2,z4,z89,z6]),(0,[z471,z2,z3,z117,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z379,z6]),(0,[z13,z2,z3,z4,z136,z5,z6]),(0,[z1,z2,z23,z33,z4,z5,z6]),(0,[z1,z599,z2,z3,z4,z5,z6])],[(0,[z70,z19,z2,z3,z4,z5,z6]),(0,[z1,z600,z2,z3,z4,z5,z6]),(0,[z197,z1,z2,z8,z4,z5,z6]),(0,[z1,z31,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z601,z6]),(0,[z1,z2,z3,z33,z4,z5,z6]),(0,[z1,z2,z3,z4,z602,z5,z6])],[(0,[z1,z2,z3,z4,z603,z5,z6]),(0,[z1,z41,z2,z8,z4,z5,z6])],[(1,[z19,z2,z3,z4,z5,z126]),(0,[z604,z1,z2,z3,z4,z5,z6]),(0,[z1,z31,z2,z322,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z89,z6]),(0,[z1,z2,z72,z3,z4,z104,z5]),(0,[z1,z2,z3,z217,z5,z140,z6]),(0,[z1,z2,z3,z559,z4,z5,z6]),(0,[z120,z1,z2,z3,z123,z5,z6])],[(0,[z188,z2,z37,z3,z4,z5,z6]),(0,[z1,z2,z605,z3,z4,z5,z6]),(0,[z1,z2,z3,z606,z4,z5,z6]),(0,[z60,z1,z2,z8,z4,z5,z6]),(0,[z1,z2,z3,z607,z4,z5,z6]),(0,[z1,z608,z2,z3,z4,z5,z6]),(0,[z122,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z136,z5,z9]),(0,[z1,z2,z3,z609,z4,z5,z6]),(1,[z60,z2,z3,z4,z65,z6]),(0,[z1,z2,z3,z610,z4,z5,z6]),(0,[z1,z2,z422,z8,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z219,z9])]],
   [[(0,[z68,z1,z188,z3,z4,z5,z6]),(0,[z611,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z561,z6])],[(0,[z75,z1,z188,z3,z4,z5,z6]),(0,[z0,z1,z2,z3,z4,z5,z9]),(0,[z1,z2,z8,z4,z208,z5,z6]),(0,[z612,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z377,z4,z5,z6]),(0,[z613,z1,z2,z3,z4,z5,z6]),(1,[z57,z1,z3,z24,z5,z6]),(0,[z209,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z498]),(1,[z409,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z259,z5,z6]),(0,[z1,z2,z3,z4,z5,z520,z6]),(0,[z59,z1,z2,z3,z39,z4,z5]),(0,[z1,z2,z8,z4,z5,z6,z394]),(0,[z1,z2,z3,z4,z5,z6,z614])],[(0,[z1,z2,z3,z4,z5,z524,z6]),(0,[z122,z1,z2,z3,z4,z6,z91])],[(0,[z1,z2,z2,z3,z4,z5,z6]),(1,[z261,z2,z8,z4,z5,z6]),(0,[z1,z2,z8,z217,z4,z5,z6]),(0,[z1,z2,z220,z8,z4,z5,z6]),(0,[z1,z2,z3,z4,z341,z5,z26]),(0,[z51,z350,z2,z3,z4,z5,z6]),(0,[z51,z102,z1,z2,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z615,z6]),(0,[z1,z2,z616,z3,z4,z5,z6])],[(0,[z1,z2,z23,z617,z4,z5,z6]),(0,[z1,z2,z220,z3,z110,z5,z6]),(1,[z1,z2,z3,z4,z5,z439])],[(0,[z1,z2,z3,z618,z4,z5,z6]),(0,[z94,z1,z2,z3,z4,z5,z144]),(0,[z1,z2,z3,z617,z4,z5,z6]),(0,[z1,z2,z3,z4,z24,z5,z9]),(1,[z102,z1,z2,z4,z5,z150])],[(0,[z1,z2,z619,z3,z4,z5,z6]),(0,[z1,z620,z2,z3,z4,z5,z6]),(0,[z1,z2,z408,z3,z4,z5,z6]),(0,[z130,z1,z2,z248,z4,z5,z6]),(0,[z1,z2,z3,z621,z4,z5,z6]),(1,[z1,z2,z3,z117,z33,z6])]],
   [[(0,[z1,z2,z3,z4,z622,z5,z6]),(0,[z70,z13,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z169,z4,z5,z6])],[(0,[z1,z2,z23,z23,z4,z5,z6]),(0,[z1,z2,z8,z4,z415,z5,z6]),(1,[z1,z3,z4,z5,z9,z26]),(0,[z1,z2,z220,z233,z4,z5,z6]),(0,[z1,z623,z2,z3,z4,z5,z6])],[(0,[z624,z1,z2,z3,z4,z5,z6]),(0,[z75,z1,z2,z427,z4,z5,z6]),(0,[z88,z1,z2,z3,z4,z5,z26]),(0,[z1,z2,z3,z23,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z243,z6]),(0,[z57,z1,z2,z3,z4,z5,z9]),(0,[z625,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z626,z4,z5,z6]),(0,[z1,z2,z8,z39,z4,z5,z6]),(0,[z1,z2,z3,z627,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z628,z6]),(1,[z103,z2,z3,z4,z5,z6])],[(0,[z60,z188,z2,z3,z4,z5,z6]),(0,[z70,z2,z3,z4,z5,z127,z6]),(0,[z1,z2,z3,z4,z5,z126,z26]),(0,[z1,z2,z8,z123,z4,z5,z6]),(1,[z315,z2,z3,z4,z5,z6]),(1,[z1,z2,z3,z4,z198,z5])],[(0,[z75,z19,z2,z3,z4,z5,z6]),(0,[z70,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z8,z4,z239,z5,z6]),(0,[z51,z1,z2,z3,z4,z5,z9]),(0,[z1,z2,z3,z4,z5,z6,z629]),(1,[z1,z2,z4,z5,z392,z6]),(0,[z409,z2,z3,z33,z4,z5,z6])],[(0,[z13,z1,z2,z23,z4,z5,z6]),(0,[z1,z2,z3,z630,z4,z5,z6]),(0,[z631,z1,z2,z3,z4,z5,z6])],[(0,[z75,z68,z2,z3,z4,z5,z6]),(0,[z2,z37,z3,z4,z136,z5,z6]),(0,[z1,z2,z3,z4,z4,z5,z6]),(0,[z70,z60,z2,z3,z4,z5,z6]),(0,[z1,z2,z8,z8,z4,z5,z6]),(0,[z244,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z26,z590]),(0,[z1,z2,z3,z4,z5,z77,z9]),(0,[z2,z3,z123,z4,z35,z5,z6])]],
   [[(0,[z1,z632,z2,z3,z4,z5,z6]),(1,[z1,z2,z3,z4,z5,z133]),(0,[z633,z1,z2,z3,z4,z5,z6]),(0,[z1,z634,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z635])],[(1,[z75,z37,z3,z4,z5,z6]),(0,[z94,z1,z2,z3,z4,z5,z9]),(0,[z1,z2,z23,z4,z5,z9,z6]),(0,[z1,z2,z3,z106,z4,z5,z6]),(0,[z636,z1,z2,z3,z4,z5,z6]),(1,[z1,z2,z131,z4,z5,z6]),(1,[z130,z1,z3,z4,z5,z26]),(0,[z1,z2,z3,z4,z5,z89,z9]),(0,[z111,z1,z2,z3,z4,z110,z5])],[(0,[z1,z2,z3,z637,z4,z5,z6]),(0,[z94,z1,z2,z3,z4,z5,z192]),(0,[z1,z2,z3,z528,z4,z5,z6]),(0,[z1,z638,z2,z3,z4,z5,z6]),(0,[z1,z41,z2,z3,z4,z5,z561]),(0,[z639,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z640]),(0,[z1,z2,z3,z4,z5,z9,z6]),(0,[z254,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z37,z23,z4,z5,z6]),(0,[z641,z1,z2,z3,z4,z5,z6]),(0,[z261,z1,z2,z8,z4,z5,z6]),(0,[z1,z2,z4,z52,z5,z89,z6])],[(0,[z510,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z642,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z73,z6]),(0,[z1,z2,z643,z3,z4,z5,z6])],[(1,[z1,z2,z3,z4,z259,z6]),(0,[z1,z2,z3,z4,z5,z6,z644]),(0,[z1,z2,z3,z4,z5,z6,z645]),(0,[z1,z2,z646,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z647,z6]),(0,[z18,z1,z2,z3,z4,z5,z9]),(0,[z648,z1,z2,z3,z4,z5,z6]),(0,[z649,z1,z2,z3,z4,z5,z6]),(0,[z650,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z4,z5,z6,z285,z270])],[(0,[z1,z2,z3,z4,z5,z651,z6]),(1,[z1,z2,z8,z4,z5,z6]),(0,[z1,z2,z8,z4,z104,z5,z6]),(0,[z1,z2,z3,z4,z5,z652,z6]),(1,[z2,z3,z118,z4,z5,z6]),(0,[z1,z2,z3,z123,z4,z5,z121])]],
   [[(0,[z1,z2,z206,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z653,z5,z6]),(0,[z1,z2,z8,z4,z446,z5,z6]),(0,[z1,z2,z116,z3,z4,z5,z9]),(0,[z1,z2,z3,z4,z5,z6,z654])],[(0,[z1,z2,z3,z3,z4,z5,z6]),(0,[z88,z0,z2,z3,z4,z5,z6]),(0,[z70,z2,z3,z4,z208,z5,z6]),(1,[z1,z2,z220,z233,z5,z6])],[(0,[z75,z13,z2,z3,z4,z5,z6]),(0,[z655,z1,z2,z3,z4,z5,z6]),(0,[z656,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z657]),(0,[z1,z2,z3,z4,z658,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z27]),(0,[z100,z1,z2,z3,z4,z5,z26]),(0,[z1,z2,z3,z4,z5,z9,z614]),(0,[z1,z2,z3,z4,z5,z6,z659]),(0,[z120,z1,z2,z3,z4,z5,z6])],[(0,[z660,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z208,z239,z6]),(0,[z1,z2,z8,z4,z5,z121,z6]),(0,[z1,z2,z3,z322,z4,z5,z6]),(0,[z111,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z434,z3,z4,z5,z6]),(0,[z661,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z662,z4,z5,z6]),(0,[z1,z2,z14,z3,z4,z5,z26]),(0,[z1,z2,z3,z4,z5,z663,z6]),(0,[z262,z1,z2,z3,z4,z5,z6]),(0,[z565,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z664])],[(0,[z665,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z666,z3,z4,z5,z6]),(0,[z1,z2,z162,z3,z4,z5,z9]),(0,[z1,z2,z3,z4,z667,z5,z6])],[(0,[z75,z2,z3,z4,z5,z127,z6]),(0,[z1,z2,z3,z69,z4,z5,z6]),(0,[z2,z3,z4,z5,z127,z6,z126]),(0,[z1,z2,z3,z4,z198,z5,z6]),(0,[z1,z2,z4,z5,z6,z330,z91]),(0,[z1,z2,z3,z668,z4,z5,z6])],[(0,[z75,z1,z2,z3,z4,z5,z6]),(0,[z669,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z670,z6]),(0,[z671,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z672,z4,z5,z6]),(0,[z1,z2,z3,z4,z110,z5,z6]),(0,[z103,z1,z2,z3,z4,z5,z6])]],
   [[(0,[z673,z1,z2,z3,z4,z5,z6]),(0,[z1,z3,z4,z5,z9,z6,z26])],[(0,[z1,z2,z3,z674,z4,z5,z6]),(0,[z675,z1,z2,z3,z4,z5,z6]),(0,[z7,z1,z2,z23,z4,z5,z6]),(0,[z1,z2,z676,z3,z4,z5,z6]),(0,[z57,z1,z2,z3,z4,z243,z6]),(0,[z1,z2,z3,z4,z677,z5,z6]),(0,[z1,z2,z3,z4,z5,z678,z6]),(1,[z1,z2,z344,z4,z5,z6]),(0,[z1,z2,z679,z3,z4,z5,z6])],[(0,[z1,z2,z3,z680,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z5,z6]),(0,[z102,z1,z2,z8,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z405,z6]),(0,[z197,z1,z2,z3,z4,z5,z26]),(0,[z1,z2,z116,z3,z4,z52,z6]),(0,[z471,z1,z2,z3,z4,z5,z6])],[(0,[z70,z2,z3,z39,z4,z5,z6]),(0,[z452,z1,z2,z3,z4,z5,z6]),(0,[z1,z41,z2,z3,z4,z5,z26]),(0,[z1,z2,z3,z681,z4,z5,z6]),(0,[z1,z682,z2,z3,z4,z5,z6]),(1,[z2,z3,z4,z35,z5,z6])],[(0,[z130,z1,z3,z4,z5,z6,z26]),(0,[z120,z1,z2,z3,z4,z104,z5])],[(1,[z1,z2,z3,z475,z5,z6]),(0,[z683,z1,z2,z3,z4,z5,z6]),(0,[z60,z1,z2,z3,z4,z5,z26]),(0,[z1,z2,z23,z4,z5,z140,z6])],[(0,[z1,z2,z3,z4,z5,z464,z6]),(0,[z13,z2,z3,z4,z5,z65,z6]),(0,[z1,z2,z3,z4,z684,z5,z6]),(0,[z1,z2,z23,z4,z5,z6,z91]),(0,[z57,z262,z2,z3,z4,z5,z6]),(0,[z57,z1,z2,z3,z30,z5,z6]),(0,[z1,z2,z422,z3,z4,z5,z26]),(0,[z685,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z140,z6]),(0,[z1,z2,z3,z4,z104,z5,z91])],[(0,[z686,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z687,z5,z6]),(0,[z688,z1,z2,z3,z4,z5,z6]),(0,[z19,z1,z2,z72,z3,z4,z5]),(0,[z101,z1,z2,z23,z4,z5,z6]),(0,[z57,z1,z3,z4,z24,z5,z6]),(0,[z1,z2,z3,z689,z4,z5,z6]),(0,[z690,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z117,z4,z5,z26]),(0,[z1,z2,z3,z4,z5,z6,z691]),(0,[z1,z2,z3,z4,z5,z6,z91])]],
   [[(0,[z1,z2,z3,z692,z4,z5,z6]),(0,[z1,z2,z693,z3,z4,z5,z6]),(0,[z2,z3,z4,z5,z289,z32,z6]),(1,[z2,z3,z4,z5,z6,z62]),(0,[z1,z2,z3,z4,z5,z6,z694])],[(0,[z1,z31,z2,z177,z4,z5,z6]),(0,[z1,z2,z3,z4,z52,z5,z9])],[(0,[z1,z2,z3,z4,z5,z145,z6]),(1,[z1,z2,z116,z4,z52,z6]),(0,[z1,z2,z4,z52,z5,z73,z6]),(0,[z695,z1,z2,z3,z4,z5,z6])],[(0,[z75,z2,z3,z4,z208,z5,z6]),(0,[z38,z1,z2,z39,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z65,z9]),(0,[z1,z696,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z577,z4,z5,z6]),(0,[z1,z2,z3,z697,z4,z5,z6]),(1,[z1,z2,z3,z4,z5,z405]),(0,[z1,z2,z220,z3,z4,z5,z26]),(0,[z1,z698,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z699]),(1,[z254,z2,z3,z4,z5,z6])],[(0,[z13,z2,z14,z3,z4,z5,z6]),(0,[z70,z1,z2,z3,z136,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z700]),(0,[z100,z1,z2,z3,z176,z5,z6]),(0,[z1,z2,z3,z233,z4,z5,z26]),(0,[z1,z2,z3,z4,z5,z26,z640])],[(0,[z1,z2,z3,z4,z701,z5,z6]),(0,[z1,z2,z23,z4,z136,z5,z6]),(0,[z1,z2,z23,z4,z5,z219,z6]),(0,[z1,z2,z3,z4,z5,z32,z9]),(0,[z702,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z136,z5,z6]),(0,[z154,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z703,z3,z4,z5,z6]),(0,[z1,z2,z3,z704,z4,z5,z6]),(0,[z101,z34,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z219,z6])],[(0,[z1,z188,z2,z3,z4,z5,z464]),(0,[z38,z1,z2,z8,z4,z5,z6]),(0,[z1,z2,z3,z4,z705,z5,z6]),(0,[z1,z2,z3,z706,z4,z5,z6]),(1,[z1,z2,z402,z4,z5,z6])]]]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkB : List (List (List (ℕ × List W))) :=
  [[[(0,[z54,z1,z2,z4,z5,z9])],[(0,[z1,z2,z3,z4,z5,z707])],[(0,[z1,z2,z708,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z709]),(0,[z94,z1,z23,z4,z5,z144]),(0,[z1,z2,z3,z117,z710,z6])],[],[(0,[z1,z2,z175,z4,z5,z6]),(0,[z1,z2,z4,z5,z711,z6]),(0,[z1,z2,z3,z176,z5,z6])],[(0,[z88,z2,z3,z4,z712,z6]),(0,[z111,z1,z2,z8,z4,z5]),(0,[z1,z2,z3,z4,z5,z180]),(0,[z713,z2,z3,z4,z5,z6])],[(0,[z1,z2,z8,z4,z5,z464]),(0,[z1,z2,z714,z4,z5,z6]),(0,[z715,z1,z2,z4,z5,z6]),(0,[z28,z122,z1,z2,z4,z91])],[(0,[z1,z2,z427,z475,z5,z6]),(0,[z38,z2,z716,z4,z5,z6]),(0,[z1,z2,z717,z4,z5,z6]),(0,[z1,z2,z4,z5,z6,z718]),(0,[z471,z2,z8,z4,z5,z6]),(0,[z2,z3,z719,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z133])],[(0,[z2,z720,z3,z4,z5,z6]),(0,[z18,z2,z3,z4,z5,z721]),(0,[z262,z2,z3,z4,z235,z6]),(0,[z1,z2,z722,z4,z5,z6]),(0,[z723,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z724]),(0,[z102,z1,z2,z4,z5,z305])],[(0,[z1,z16,z3,z4,z239,z6]),(0,[z1,z3,z4,z5,z725,z6]),(0,[z726,z2,z3,z4,z5,z9])],[(0,[z1,z2,z727,z4,z5,z6]),(0,[z13,z2,z14,z4,z5,z26]),(0,[z2,z8,z728,z4,z5,z6]),(0,[z51,z111,z1,z2,z4,z5]),(0,[z729,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z243,z263]),(0,[z1,z2,z730,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z731]),(0,[z1,z2,z732,z4,z5,z6]),(0,[z1,z2,z23,z4,z235,z6]),(0,[z2,z3,z733,z4,z5,z26])],[(0,[z1,z2,z3,z4,z379,z26]),(0,[z94,z1,z23,z4,z5,z9]),(0,[z100,z1,z8,z4,z32,z6]),(0,[z1,z2,z3,z4,z5,z734])],[(0,[z1,z2,z3,z4,z5,z735]),(0,[z70,z2,z3,z71,z5,z26]),(0,[z94,z1,z23,z4,z5,z192]),(0,[z736,z2,z3,z4,z5,z6]),(0,[z2,z3,z4,z5,z737,z6])],[(0,[z1,z2,z3,z4,z5,z205]),(0,[z738,z2,z8,z4,z5,z6]),(0,[z2,z3,z739,z4,z5,z6]),(0,[z1,z679,z3,z4,z5,z26])]],
   [[(0,[z209,z2,z3,z4,z5,z6])],[(0,[z1,z2,z23,z4,z5,z253]),(0,[z1,z2,z377,z233,z5,z6]),(0,[z1,z2,z740,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z741]),(0,[z1,z2,z3,z4,z5,z742])],[(0,[z2,z8,z106,z4,z5,z26]),(0,[z1,z8,z79,z4,z5,z6]),(0,[z244,z2,z3,z4,z5,z9]),(0,[z1,z2,z3,z5,z26,z743]),(0,[z565,z1,z2,z3,z4,z512])],[(0,[z1,z2,z744,z4,z5,z6]),(0,[z261,z2,z23,z4,z5,z6]),(0,[z262,z2,z23,z4,z5,z6]),(0,[z2,z8,z745,z4,z5,z6]),(0,[z1,z2,z746,z4,z5,z6]),(0,[z1,z2,z233,z5,z186,z6]),(0,[z2,z3,z4,z5,z747,z6])],[(0,[z448,z1,z23,z4,z5,z6]),(0,[z1,z2,z3,z33,z710,z6])],[(0,[z1,z29,z8,z4,z5,z253]),(0,[z1,z2,z748,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z749]),(0,[z130,z1,z248,z4,z5,z26]),(0,[z141,z2,z3,z4,z5,z9]),(0,[z1,z642,z3,z4,z5,z9])],[(0,[z1,z2,z3,z4,z5,z750])],[(0,[z188,z3,z4,z5,z125,z6]),(0,[z1,z2,z3,z4,z5,z751]),(0,[z752,z2,z3,z4,z5,z6]),(0,[z389,z2,z281,z4,z5,z6]),(0,[z261,z29,z8,z4,z5,z6]),(0,[z1,z2,z3,z117,z438,z6]),(0,[z753,z2,z3,z4,z5,z6])],[(0,[z754,z1,z2,z3,z4,z5]),(0,[z2,z3,z4,z35,z5,z6]),(0,[z1,z2,z755,z4,z5,z6]),(0,[z2,z3,z4,z5,z289,z26]),(0,[z1,z2,z3,z4,z5,z756])],[(0,[z57,z154,z3,z24,z5,z6]),(0,[z1,z474,z3,z30,z5,z6]),(0,[z757,z1,z2,z3,z4,z26]),(0,[z1,z2,z3,z4,z5,z758])],[(0,[z0,z2,z3,z4,z379,z6]),(0,[z75,z288,z3,z4,z5,z6]),(0,[z13,z2,z478,z4,z5,z6]),(0,[z232,z2,z3,z4,z5,z9]),(0,[z2,z3,z559,z4,z32,z6]),(0,[z1,z364,z3,z4,z5,z26])],[],[(0,[z209,z2,z8,z4,z5,z26]),(0,[z1,z3,z4,z725,z32,z6])],[(0,[z2,z3,z4,z5,z6,z62]),(0,[z1,z2,z3,z759,z5,z6]),(0,[z88,z2,z8,z4,z208,z6]),(0,[z34,z2,z23,z4,z5,z6]),(0,[z1,z2,z23,z4,z5,z181])]],
   [[(0,[z0,z2,z3,z136,z5,z6])],[(0,[z404,z1,z2,z110,z5,z6]),(0,[z1,z698,z23,z4,z5,z6]),(0,[z122,z1,z2,z3,z4,z512])],[(0,[z1,z23,z4,z24,z5,z26]),(0,[z1,z572,z23,z4,z5,z6])],[(0,[z1,z2,z760,z4,z5,z6]),(0,[z1,z2,z577,z4,z52,z6]),(0,[z761,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z263])],[(0,[z762,z2,z23,z4,z5,z6])],[(0,[z1,z2,z3,z763,z5,z6]),(0,[z1,z2,z169,z4,z5,z6]),(0,[z1,z2,z3,z4,z764,z5])],[(0,[z1,z2,z3,z4,z5,z765]),(0,[z57,z1,z234,z24,z5,z6]),(0,[z1,z2,z169,z216,z5,z6])],[(0,[z1,z2,z766,z4,z5,z6]),(0,[z1,z2,z767,z4,z5,z6])],[(0,[z102,z1,z2,z610,z4,z5])],[(0,[z1,z223,z8,z4,z5,z6]),(0,[z18,z2,z23,z4,z5,z127]),(0,[z768,z2,z3,z4,z5,z6]),(0,[z1,z2,z4,z769,z89,z6]),(0,[z28,z122,z1,z2,z4,z5])],[(0,[z1,z2,z3,z4,z379,z205]),(0,[z1,z2,z770,z4,z5,z6]),(0,[z1,z619,z23,z4,z5,z6]),(0,[z771,z2,z3,z4,z5,z6])],[(0,[z75,z37,z67,z4,z5,z6])],[(0,[z2,z772,z3,z4,z5,z6]),(0,[z75,z334,z3,z4,z5,z6]),(0,[z18,z2,z3,z4,z5,z62]),(0,[z230,z2,z8,z4,z5,z6]),(0,[z2,z8,z118,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z773])],[(0,[z68,z1,z23,z4,z5,z26])],[(0,[z2,z3,z4,z504,z65,z6]),(0,[z1,z2,z4,z774,z5,z6]),(0,[z1,z2,z3,z4,z769,z6]),(0,[z775,z2,z3,z4,z5,z6]),(0,[z776,z2,z3,z4,z5,z6])]],
   [[(0,[z1,z2,z3,z5,z121,z777])],[(0,[z1,z115,z3,z4,z5,z26]),(0,[z103,z2,z72,z3,z4,z5])],[(0,[z1,z2,z23,z4,z5,z346])],[(0,[z1,z2,z3,z36,z259,z6]),(0,[z1,z2,z577,z4,z319,z6]),(0,[z1,z2,z23,z123,z5,z121]),(0,[z1,z2,z8,z4,z5,z561])],[(0,[z1,z2,z8,z4,z5,z398])],[(0,[z1,z2,z427,z4,z5,z9]),(0,[z19,z682,z2,z3,z4,z5]),(0,[z1,z2,z177,z4,z5,z9]),(0,[z778,z1,z2,z3,z4,z5]),(0,[z28,z1,z2,z4,z104,z5])],[(0,[z2,z779,z3,z4,z5,z6]),(0,[z2,z3,z4,z179,z5,z6]),(0,[z1,z2,z780,z4,z5,z6]),(0,[z1,z317,z8,z4,z5,z9]),(0,[z781,z2,z3,z4,z5,z6]),(0,[z1,z2,z213,z4,z5,z26]),(0,[z782,z2,z3,z4,z5,z6]),(0,[z783,z1,z2,z3,z4,z5])],[(0,[z1,z2,z3,z784,z5,z6]),(0,[z261,z2,z3,z4,z5,z9]),(0,[z262,z2,z3,z4,z5,z9]),(0,[z1,z2,z3,z216,z5,z6]),(0,[z2,z3,z785,z4,z5,z6]),(0,[z2,z3,z4,z5,z9,z62]),(0,[z786,z2,z3,z4,z5,z26]),(0,[z787,z1,z2,z3,z4,z5]),(0,[z296,z1,z2,z3,z4,z5])],[(0,[z2,z3,z4,z208,z712,z6]),(0,[z2,z8,z4,z35,z5,z6]),(0,[z92,z2,z3,z4,z5,z26])],[(0,[z1,z2,z3,z4,z788,z6]),(0,[z789,z2,z3,z4,z5,z6]),(0,[z111,z1,z2,z3,z4,z5]),(0,[z1,z2,z790,z4,z5,z6]),(0,[z1,z2,z791,z4,z5,z6])],[(0,[z88,z2,z3,z4,z301,z6]),(0,[z1,z2,z3,z5,z792,z6]),(0,[z1,z41,z408,z30,z5,z6]),(0,[z1,z2,z793,z4,z5,z6])],[(0,[z1,z2,z4,z5,z6,z794])],[(0,[z232,z2,z23,z4,z5,z6]),(0,[z296,z1,z2,z23,z4,z5]),(0,[z1,z2,z3,z5,z6,z743]),(0,[z2,z3,z4,z5,z795,z6])],[(0,[z1,z2,z3,z4,z5,z796]),(0,[z797,z1,z2,z4,z5,z6])],[(0,[z1,z23,z4,z5,z6,z629]),(0,[z111,z1,z2,z23,z4,z5]),(0,[z1,z2,z72,z4,z5,z77]),(0,[z1,z320,z8,z4,z5,z6]),(0,[z798,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z217,z140,z26]),(0,[z1,z3,z4,z5,z9,z436]),(0,[z2,z3,z799,z4,z5,z6])],[(0,[z1,z2,z67,z475,z5,z6]),(0,[z19,z2,z3,z4,z379,z6]),(0,[z1,z2,z116,z4,z769,z6])]],
   [[(0,[z1,z2,z3,z4,z5,z800]),(0,[z261,z2,z14,z4,z5,z6]),(0,[z442,z2,z3,z4,z5,z62])],[(0,[z188,z3,z4,z5,z6,z252]),(0,[z350,z2,z3,z4,z5,z6]),(0,[z29,z8,z106,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z801]),(0,[z1,z2,z4,z5,z802,z6]),(0,[z2,z3,z4,z803,z5,z6]),(0,[z102,z1,z2,z4,z5,z449]),(1,[z1,z2,z3,z5,z777])],[(0,[z1,z2,z23,z4,z5,z804])],[(0,[z1,z2,z3,z4,z5,z805]),(0,[z471,z2,z3,z4,z5,z9])],[(0,[z1,z2,z3,z806,z4,z6])],[(0,[z1,z2,z3,z4,z5,z807]),(0,[z1,z2,z3,z808,z5,z6])],[(0,[z1,z2,z3,z809,z5,z6]),(0,[z1,z207,z3,z4,z5,z26]),(0,[z810,z1,z2,z23,z5,z6]),(0,[z296,z1,z2,z8,z4,z5]),(0,[z811,z1,z2,z4,z5,z6]),(0,[z102,z1,z2,z704,z4,z5])],[(0,[z1,z2,z23,z4,z104,z219])],[(0,[z60,z2,z8,z4,z65,z6])],[(0,[z416,z1,z23,z4,z5,z6]),(0,[z1,z2,z234,z4,z235,z6]),(0,[z1,z2,z213,z4,z5,z180]),(0,[z100,z1,z3,z4,z32,z9]),(0,[z812,z2,z3,z4,z5,z6])],[(0,[z409,z2,z8,z4,z5,z6]),(0,[z813,z1,z2,z3,z4,z5])],[(0,[z68,z188,z3,z4,z5,z6]),(0,[z389,z2,z39,z4,z5,z6]),(0,[z2,z3,z814,z106,z4,z5]),(0,[z51,z1,z2,z415,z5,z6])],[(0,[z2,z3,z4,z815,z5,z6]),(0,[z1,z2,z402,z4,z5,z398]),(0,[z1,z2,z322,z4,z5,z9]),(0,[z78,z1,z2,z4,z5,z150])],[(1,[z2,z716,z4,z5,z6]),(0,[z2,z3,z71,z816,z5,z6])],[(0,[z13,z2,z14,z4,z5,z6]),(0,[z2,z3,z153,z136,z5,z6]),(0,[z2,z3,z4,z817,z5,z6]),(0,[z2,z3,z818,z4,z5,z6])],[(0,[z43,z37,z3,z4,z5,z6]),(0,[z1,z2,z819,z4,z5,z6]),(0,[z1,z2,z23,z4,z5,z413]),(0,[z2,z820,z3,z4,z5,z6])]],
   [[(0,[z821,z1,z2,z3,z4,z5]),(0,[z1,z2,z3,z563,z140,z6]),(0,[z1,z2,z332,z4,z5,z9])],[(0,[z1,z2,z3,z4,z379,z6]),(0,[z261,z2,z427,z4,z5,z6]),(0,[z822,z2,z3,z4,z5,z6])],[(0,[z13,z2,z82,z4,z5,z6]),(1,[z2,z3,z4,z712,z6]),(0,[z1,z2,z3,z710,z5,z6])],[(0,[z1,z2,z4,z5,z6,z823]),(0,[z824,z2,z3,z4,z5,z6]),(0,[z1,z2,z4,z5,z825,z6])],[(0,[z2,z3,z4,z5,z721,z6]),(0,[z103,z2,z8,z4,z5,z6]),(0,[z57,z262,z3,z24,z5,z6]),(0,[z826,z1,z2,z3,z4,z5]),(0,[z130,z1,z131,z4,z5,z26]),(0,[z1,z2,z827,z4,z5,z6])],[(0,[z315,z2,z8,z4,z5,z6]),(0,[z828,z2,z3,z4,z5,z6])],[],[(0,[z1,z2,z3,z4,z5,z829]),(0,[z2,z8,z106,z4,z5,z6]),(0,[z1,z830,z3,z4,z5,z6]),(0,[z1,z2,z831,z4,z5,z6])],[(0,[z75,z37,z3,z4,z259,z6]),(0,[z1,z2,z832,z4,z5,z6])],[(0,[z1,z2,z833,z4,z5,z6]),(0,[z2,z716,z39,z4,z5,z6]),(0,[z1,z8,z23,z4,z5,z26]),(0,[z1,z2,z3,z4,z5,z834]),(0,[z1,z2,z8,z4,z5,z133]),(0,[z1,z2,z248,z4,z5,z9]),(0,[z1,z2,z3,z4,z5,z835]),(0,[z836,z2,z3,z4,z5,z6])],[(0,[z194,z1,z23,z4,z5,z6]),(0,[z1,z2,z3,z4,z837,z6]),(0,[z1,z2,z3,z4,z5,z838])],[(0,[z839,z1,z2,z3,z4,z5]),(0,[z1,z3,z30,z840,z5,z6]),(0,[z2,z3,z559,z4,z5,z26]),(0,[z1,z2,z841,z4,z5,z6])],[(0,[z1,z2,z3,z36,z5,z26])],[(0,[z2,z3,z559,z4,z239,z6])],[(0,[z1,z2,z8,z4,z259,z6]),(0,[z2,z3,z4,z5,z289,z6])],[(0,[z1,z2,z3,z4,z5,z842]),(0,[z821,z1,z2,z8,z4,z5]),(0,[z843,z2,z3,z4,z5,z6]),(0,[z1,z2,z4,z52,z493,z6])]],
   [[(0,[z154,z2,z3,z136,z5,z6]),(0,[z839,z1,z2,z23,z4,z5])],[(0,[z1,z2,z3,z4,z243,z6]),(0,[z57,z1,z3,z24,z5,z398])],[(0,[z1,z2,z23,z4,z5,z464])],[(0,[z1,z2,z3,z4,z844,z6]),(0,[z471,z2,z23,z4,z5,z6]),(0,[z1,z2,z3,z689,z140,z6])],[(0,[z1,z2,z67,z4,z5,z346]),(0,[z757,z1,z2,z23,z4,z6]),(0,[z1,z2,z3,z4,z5,z429]),(0,[z845,z2,z3,z4,z5,z6]),(0,[z846,z2,z3,z4,z5,z6])],[(0,[z847,z1,z2,z3,z4,z5]),(0,[z1,z31,z3,z4,z239,z9])],[(0,[z611,z2,z3,z136,z5,z6]),(0,[z1,z2,z3,z4,z5,z848]),(0,[z1,z2,z3,z849,z4,z6]),(0,[z81,z1,z2,z4,z5,z26])],[(0,[z2,z3,z4,z5,z850,z6])],[(0,[z154,z2,z3,z36,z5,z6]),(0,[z1,z2,z3,z851,z5,z6]),(0,[z230,z2,z3,z4,z5,z9]),(0,[z1,z852,z3,z4,z5,z6])],[(0,[z68,z772,z3,z4,z5,z6]),(0,[z100,z1,z23,z4,z32,z6]),(0,[z2,z8,z814,z106,z4,z5]),(0,[z101,z1,z2,z4,z89,z26]),(0,[z1,z2,z3,z463,z5,z524]),(0,[z1,z2,z642,z4,z5,z150])],[(0,[z853,z1,z2,z3,z4,z5]),(0,[z1,z2,z23,z854,z4,z6]),(0,[z855,z2,z3,z4,z5,z6]),(0,[z244,z2,z3,z4,z5,z413])],[(0,[z0,z2,z3,z36,z5,z6]),(0,[z1,z2,z3,z856,z5,z6]),(0,[z1,z2,z4,z5,z9,z823]),(0,[z1,z2,z72,z4,z5,z589])],[(0,[z1,z2,z3,z475,z259,z6]),(0,[z1,z2,z857,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z858])],[(0,[z1,z2,z67,z4,z5,z9]),(0,[z1,z2,z859,z4,z5,z6]),(0,[z315,z2,z402,z4,z5,z6]),(0,[z1,z2,z3,z4,z26,z860]),(0,[z1,z2,z3,z4,z861,z91])],[(0,[z75,z497,z3,z4,z5,z6]),(0,[z1,z2,z408,z4,z5,z9])],[(0,[z1,z2,z427,z4,z5,z346]),(0,[z1,z862,z3,z4,z5,z6]),(0,[z51,z1,z2,z335,z5,z6])]],
   [[(0,[z1,z2,z3,z4,z5,z863])],[(0,[z1,z2,z3,z864,z5,z6]),(0,[z57,z1,z3,z24,z5,z26]),(0,[z1,z2,z3,z4,z5,z865])],[],[(0,[z1,z2,z422,z4,z5,z128]),(0,[z866,z2,z3,z4,z5,z180]),(0,[z510,z1,z2,z3,z4,z91]),(0,[z2,z3,z867,z4,z5,z6])],[(0,[z1,z2,z868,z4,z5,z6]),(0,[z1,z2,z8,z4,z5,z405]),(0,[z869,z2,z8,z4,z5,z6])],[(0,[z1,z2,z3,z4,z870,z5]),(0,[z871,z1,z2,z3,z4,z5])],[(0,[z872,z2,z8,z4,z5,z6]),(0,[z111,z1,z2,z233,z4,z5]),(0,[z2,z3,z4,z5,z873,z6])],[(0,[z1,z2,z3,z117,z33,z26]),(0,[z1,z2,z3,z4,z5,z874])],[(0,[z1,z2,z3,z4,z5,z875]),(0,[z1,z2,z234,z4,z5,z9]),(1,[z1,z2,z4,z769,z6]),(0,[z122,z1,z2,z3,z4,z91])],[(0,[z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z36,z5,z205]),(0,[z876,z1,z2,z3,z4,z5]),(0,[z1,z2,z3,z4,z5,z877]),(0,[z102,z254,z2,z3,z4,z5])],[(0,[z1,z2,z3,z878,z5,z6]),(0,[z209,z2,z23,z4,z5,z26])],[(0,[z13,z2,z99,z4,z5,z6]),(0,[z88,z2,z23,z4,z208,z6]),(0,[z1,z2,z23,z4,z879,z5]),(0,[z786,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z880]),(0,[z92,z2,z3,z4,z5,z6]),(0,[z1,z288,z3,z4,z5,z9]),(0,[z1,z2,z3,z774,z5,z6])],[(0,[z122,z1,z2,z23,z4,z91]),(0,[z1,z3,z4,z5,z9,z20]),(0,[z409,z2,z3,z117,z33,z6])],[(0,[z1,z2,z881,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z882]),(0,[z883,z2,z3,z4,z5,z6]),(0,[z1,z41,z3,z30,z5,z561]),(0,[z1,z2,z3,z884,z4,z5])],[(0,[z1,z2,z3,z4,z885,z6])]],
   [[(0,[z1,z2,z886,z4,z5,z6]),(1,[z1,z887,z4,z5,z6]),(0,[z2,z8,z4,z5,z6,z62]),(0,[z1,z2,z3,z4,z5,z888])],[(0,[z75,z37,z3,z4,z5,z26]),(0,[z1,z431,z3,z4,z5,z26])],[(0,[z1,z3,z4,z366,z5,z26]),(0,[z209,z2,z72,z3,z4,z5]),(0,[z889,z2,z3,z4,z5,z6])],[],[(0,[z810,z1,z2,z3,z5,z6]),(0,[z154,z2,z3,z71,z5,z6]),(0,[z1,z2,z890,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z349]),(0,[z1,z2,z3,z4,z5,z891]),(0,[z1,z2,z3,z4,z235,z398]),(0,[z892,z2,z3,z4,z5,z6])],[(0,[z1,z31,z23,z4,z239,z6]),(0,[z1,z596,z8,z4,z5,z6]),(0,[z893,z2,z3,z4,z5,z6]),(0,[z232,z2,z3,z4,z32,z6]),(0,[z210,z2,z3,z4,z5,z311])],[(0,[z1,z2,z3,z4,z5,z894])],[(0,[z1,z2,z895,z4,z5,z6]),(0,[z1,z381,z8,z4,z5,z6]),(0,[z1,z2,z8,z4,z5,z26]),(0,[z122,z1,z2,z8,z4,z91]),(0,[z1,z2,z3,z24,z243,z6]),(0,[z1,z2,z3,z4,z104,z276])],[(0,[z1,z2,z896,z4,z5,z6]),(0,[z1,z2,z897,z4,z5,z6]),(0,[z230,z2,z23,z4,z5,z6])],[(0,[z1,z2,z3,z898,z4,z5]),(0,[z261,z2,z8,z4,z5,z9]),(0,[z1,z2,z3,z142,z140,z6])],[(0,[z1,z2,z3,z4,z5,z899]),(0,[z900,z2,z3,z4,z5,z26])],[],[(0,[z1,z8,z598,z4,z5,z6]),(0,[z1,z901,z3,z4,z5,z6])],[(0,[z2,z3,z4,z5,z6,z902]),(0,[z1,z2,z4,z5,z903,z150])],[(0,[z19,z2,z3,z36,z5,z6]),(0,[z904,z1,z2,z3,z4,z6]),(0,[z2,z206,z39,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z905]),(0,[z1,z2,z906,z4,z5,z6]),(0,[z1,z3,z4,z5,z549,z26])],[(0,[z1,z2,z23,z4,z5,z561]),(0,[z907,z2,z3,z4,z5,z6])]],
   [[(0,[z1,z2,z23,z4,z5,z398])],[(0,[z1,z2,z3,z4,z908,z6]),(0,[z1,z2,z206,z4,z5,z17]),(0,[z315,z2,z3,z4,z5,z9]),(0,[z1,z2,z3,z30,z243,z6])],[(0,[z1,z317,z23,z4,z5,z9]),(0,[z1,z2,z3,z5,z6,z909]),(0,[z1,z2,z4,z5,z392,z9]),(0,[z1,z2,z4,z5,z73,z654])],[(0,[z1,z2,z3,z910,z4,z5]),(0,[z904,z1,z2,z23,z4,z6]),(0,[z2,z3,z4,z911,z5,z6]),(0,[z154,z2,z8,z4,z5,z6]),(0,[z2,z3,z733,z4,z5,z6]),(0,[z209,z2,z3,z4,z5,z62]),(0,[z1,z2,z233,z5,z6,z516])],[(0,[z38,z2,z106,z4,z5,z6]),(0,[z1,z2,z4,z5,z912,z6]),(0,[z262,z2,z234,z4,z5,z6]),(0,[z2,z3,z4,z5,z410,z9]),(0,[z102,z1,z2,z630,z4,z5])],[(0,[z1,z2,z3,z475,z5,z26]),(0,[z1,z2,z3,z913,z4,z5]),(0,[z70,z2,z3,z71,z5,z6]),(0,[z1,z2,z3,z4,z5,z721])],[(0,[z1,z2,z3,z4,z6,z860]),(0,[z1,z31,z322,z4,z239,z6]),(0,[z1,z2,z131,z4,z5,z9])],[(0,[z1,z2,z3,z914,z5,z6]),(0,[z2,z8,z4,z179,z5,z6]),(0,[z101,z1,z2,z4,z145,z6]),(0,[z209,z3,z4,z5,z9,z26]),(0,[z2,z3,z4,z5,z6,z915])],[(0,[z1,z2,z3,z4,z5,z916])],[(0,[z1,z917,z3,z4,z5,z6]),(0,[z2,z3,z4,z816,z5,z6]),(0,[z1,z2,z8,z176,z5,z6]),(0,[z918,z2,z3,z4,z5,z6]),(0,[z1,z634,z3,z4,z239,z6]),(0,[z919,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z259,z9]),(0,[z1,z2,z3,z4,z5,z920]),(0,[z1,z2,z8,z4,z5,z180]),(0,[z1,z2,z116,z4,z52,z26])],[(0,[z1,z2,z3,z4,z5,z921]),(0,[z1,z2,z23,z922,z5,z6]),(0,[z923,z2,z3,z4,z5,z6]),(0,[z254,z2,z3,z4,z5,z26]),(0,[z1,z2,z3,z4,z5,z924]),(0,[z2,z3,z4,z925,z5,z6])],[(0,[z1,z3,z4,z5,z926,z6]),(0,[z2,z3,z4,z5,z6,z927]),(0,[z2,z3,z118,z4,z5,z9])],[(0,[z209,z2,z3,z4,z5,z126]),(0,[z1,z8,z23,z4,z5,z6]),(0,[z57,z1,z3,z24,z243,z6])],[(0,[z75,z37,z3,z4,z5,z205]),(0,[z1,z2,z3,z4,z5,z928]),(0,[z88,z2,z3,z4,z208,z9]),(0,[z51,z111,z1,z2,z110,z5]),(0,[z101,z141,z2,z4,z89,z6]),(0,[z1,z2,z929,z3,z4,z5])],[(0,[z1,z2,z930,z4,z5,z6]),(0,[z1,z2,z931,z4,z5,z6]),(0,[z1,z2,z402,z4,z5,z26]),(0,[z130,z3,z4,z5,z62,z26])]],
   [[(0,[z1,z2,z3,z36,z5,z6]),(0,[z2,z3,z4,z208,z379,z6]),(0,[z100,z1,z3,z4,z32,z413])],[(0,[z510,z1,z2,z3,z4,z640]),(0,[z1,z2,z4,z5,z73,z691])],[(0,[z13,z2,z427,z4,z5,z6]),(0,[z757,z1,z2,z3,z4,z6]),(0,[z55,z2,z106,z4,z5,z6]),(0,[z57,z1,z3,z24,z5,z263])],[(0,[z932,z1,z2,z3,z4,z5]),(0,[z1,z2,z3,z933,z5,z6]),(0,[z1,z2,z4,z5,z6,z934])],[(0,[z1,z2,z8,z4,z5,z205]),(0,[z60,z2,z23,z4,z65,z6]),(0,[z28,z1,z2,z4,z5,z26]),(0,[z1,z2,z162,z4,z5,z73])],[(0,[z1,z2,z3,z4,z5,z935]),(0,[z1,z29,z8,z4,z5,z26]),(0,[z209,z2,z8,z4,z5,z6]),(0,[z315,z2,z3,z4,z235,z6])],[(0,[z38,z2,z39,z4,z5,z26]),(0,[z0,z2,z3,z816,z5,z6]),(0,[z1,z2,z4,z5,z6,z936]),(0,[z409,z2,z23,z4,z5,z6])],[(0,[z2,z3,z4,z5,z26,z902]),(0,[z1,z2,z3,z937,z4,z26]),(0,[z2,z3,z938,z4,z5,z6])],[(0,[z54,z1,z2,z4,z5,z26]),(0,[z939,z1,z2,z4,z5,z26]),(0,[z120,z1,z2,z3,z5,z777]),(0,[z940,z1,z2,z4,z5,z6])],[(0,[z244,z2,z114,z4,z5,z6]),(0,[z102,z1,z2,z386,z4,z5])],[(0,[z2,z3,z39,z4,z379,z6]),(0,[z1,z2,z941,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z942])],[(0,[z943,z2,z3,z4,z5,z6]),(0,[z1,z2,z4,z5,z944,z6]),(0,[z945,z2,z3,z4,z5,z9]),(0,[z2,z3,z4,z946,z5,z6])],[(0,[z1,z2,z3,z5,z26,z909])],[(0,[z1,z2,z3,z4,z5,z947]),(0,[z948,z2,z3,z4,z5,z6]),(0,[z7,z1,z2,z4,z227,z6]),(0,[z2,z3,z949,z4,z5,z6]),(0,[z101,z1,z2,z4,z89,z6])],[(0,[z950,z1,z2,z3,z4,z5]),(0,[z1,z2,z212,z107,z5,z6])],[(0,[z1,z2,z162,z4,z5,z77]),(0,[z951,z2,z3,z4,z5,z6]),(0,[z1,z2,z4,z5,z6,z952]),(0,[z953,z2,z3,z4,z5,z6])]],
   [[(0,[z2,z14,z716,z4,z5,z6]),(0,[z103,z2,z23,z4,z5,z6])],[(0,[z1,z2,z206,z4,z5,z9]),(0,[z612,z1,z3,z4,z5,z26]),(0,[z315,z2,z23,z4,z5,z6]),(0,[z1,z2,z114,z4,z5,z9]),(0,[z2,z3,z954,z4,z5,z6])],[(0,[z1,z2,z3,z475,z5,z205]),(0,[z2,z23,z4,z5,z955,z6]),(0,[z232,z2,z114,z4,z5,z6]),(0,[z1,z2,z3,z956,z5,z26]),(0,[z872,z2,z3,z4,z5,z9])],[(0,[z1,z2,z8,z4,z243,z6])],[(0,[z1,z2,z3,z4,z5,z957]),(0,[z70,z2,z3,z816,z5,z6])],[(0,[z1,z2,z175,z4,z5,z17]),(0,[z0,z2,z8,z136,z5,z6]),(0,[z94,z1,z23,z4,z5,z26]),(0,[z1,z2,z23,z4,z5,z133]),(0,[z57,z1,z3,z24,z5,z6])],[(0,[z232,z2,z3,z4,z5,z413]),(0,[z2,z3,z4,z5,z26,z927]),(0,[z1,z3,z4,z5,z26,z246])],[],[(0,[z1,z2,z8,z4,z5,z263]),(0,[z958,z2,z3,z4,z5,z6]),(0,[z2,z959,z3,z4,z5,z6])],[(0,[z1,z2,z960,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z439])],[(0,[z1,z2,z23,z4,z259,z6]),(0,[z961,z2,z3,z4,z5,z6]),(0,[z962,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z36,z379,z6]),(0,[z157,z2,z478,z4,z5,z6])],[(0,[z1,z2,z963,z4,z5,z6]),(0,[z1,z2,z3,z4,z964,z6]),(0,[z736,z2,z23,z4,z5,z6]),(0,[z855,z2,z8,z4,z5,z6]),(0,[z965,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z966]),(0,[z1,z2,z967,z4,z5,z6]),(0,[z1,z2,z213,z4,z5,z6]),(0,[z1,z3,z4,z5,z9,z26]),(0,[z1,z2,z4,z5,z26,z934]),(0,[z1,z2,z72,z4,z508,z5])],[(0,[z1,z2,z968,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z969]),(0,[z1,z3,z4,z5,z26,z272])],[(0,[z686,z2,z3,z4,z65,z6]),(0,[z2,z8,z4,z5,z289,z6]),(0,[z141,z2,z3,z4,z5,z26]),(0,[z1,z2,z3,z970,z5,z6])]],
   [[(0,[z1,z2,z3,z4,z5,z971]),(0,[z68,z696,z3,z4,z5,z6]),(0,[z1,z2,z972,z4,z5,z6]),(0,[z631,z1,z3,z4,z5,z26]),(0,[z1,z2,z3,z4,z198,z5])],[(0,[z519,z2,z3,z4,z208,z6]),(0,[z51,z1,z2,z110,z5,z26])],[(0,[z1,z2,z3,z4,z5,z973]),(0,[z1,z2,z3,z974,z4,z5]),(0,[z2,z3,z293,z136,z5,z6]),(0,[z2,z23,z4,z5,z410,z6]),(0,[z1,z31,z177,z4,z239,z6])],[(0,[z665,z2,z3,z4,z65,z6]),(0,[z1,z2,z3,z4,z5,z975]),(0,[z1,z3,z527,z4,z5,z26])],[(0,[z59,z2,z3,z4,z5,z65])],[(0,[z1,z2,z3,z217,z140,z6])],[(0,[z19,z2,z3,z4,z5,z721]),(0,[z1,z31,z23,z4,z5,z26]),(0,[z1,z2,z3,z274,z140,z6]),(0,[z2,z3,z4,z5,z6,z976]),(0,[z232,z2,z3,z4,z239,z6])],[(0,[z60,z2,z3,z4,z65,z9]),(0,[z2,z3,z4,z184,z5,z127]),(0,[z2,z3,z106,z4,z5,z9])],[(0,[z1,z2,z3,z4,z977,z5])],[(0,[z1,z2,z3,z4,z5,z978]),(0,[z409,z2,z3,z4,z5,z9])],[(0,[z2,z23,z118,z4,z5,z6])],[(0,[z1,z2,z8,z4,z5,z6]),(0,[z1,z2,z402,z4,z243,z6])],[(0,[z1,z2,z3,z4,z5,z979]),(0,[z1,z2,z8,z216,z5,z6]),(0,[z1,z2,z980,z4,z5,z6]),(0,[z101,z34,z2,z4,z89,z6])],[(0,[z1,z2,z3,z4,z5,z981]),(0,[z2,z3,z4,z5,z6,z982]),(0,[z122,z1,z2,z3,z4,z359])],[(0,[z1,z31,z3,z4,z725,z6]),(0,[z900,z2,z3,z4,z5,z6]),(0,[z1,z2,z4,z52,z6,z297])],[(0,[z1,z2,z3,z4,z983,z6]),(0,[z2,z497,z3,z136,z5,z6]),(0,[z984,z1,z3,z4,z5,z6]),(0,[z262,z2,z3,z4,z5,z398]),(0,[z1,z2,z3,z840,z5,z6]),(0,[z154,z2,z3,z4,z5,z9])]],
   [[(0,[z985,z1,z2,z4,z5,z6]),(0,[z1,z2,z23,z4,z5,z405]),(0,[z1,z2,z402,z4,z5,z263]),(0,[z2,z3,z4,z5,z976,z180]),(0,[z244,z2,z3,z4,z5,z133])],[(0,[z1,z3,z887,z4,z5,z6]),(0,[z761,z2,z23,z4,z5,z6])],[(0,[z1,z41,z3,z30,z5,z26]),(0,[z1,z2,z3,z4,z5,z986])],[(0,[z1,z23,z4,z400,z5,z6]),(0,[z103,z2,z3,z4,z5,z9]),(0,[z1,z2,z233,z774,z5,z6])],[(0,[z1,z2,z3,z4,z259,z346]),(0,[z1,z2,z3,z4,z5,z987]),(0,[z1,z2,z988,z4,z5,z6])],[(0,[z1,z2,z175,z4,z5,z9]),(0,[z989,z2,z23,z4,z5,z6]),(0,[z1,z2,z3,z176,z5,z9])],[(0,[z1,z23,z4,z5,z226,z6]),(0,[z1,z2,z8,z4,z5,z349]),(0,[z990,z1,z2,z4,z5,z6]),(0,[z350,z2,z8,z4,z5,z6])],[(0,[z2,z3,z4,z5,z127,z721]),(0,[z1,z2,z3,z4,z235,z26]),(0,[z1,z3,z4,z5,z975,z26]),(0,[z1,z2,z991,z4,z5,z6])],[(0,[z1,z2,z206,z4,z5,z464]),(0,[z992,z2,z3,z4,z5,z6]),(0,[z2,z3,z117,z33,z559,z6])],[(0,[z1,z2,z3,z475,z5,z6]),(0,[z1,z2,z3,z4,z6,z993]),(0,[z232,z2,z3,z4,z5,z133])],[(0,[z1,z2,z3,z994,z5,z6]),(0,[z2,z3,z4,z5,z62,z26]),(0,[z1,z2,z72,z4,z5,z498]),(0,[z102,z495,z1,z2,z4,z5])],[(0,[z13,z2,z206,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z995]),(0,[z996,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z997])],[(0,[z88,z2,z3,z4,z414,z6]),(0,[z1,z2,z4,z5,z6,z998])],[(0,[z1,z575,z3,z4,z5,z26]),(0,[z1,z459,z23,z4,z5,z6])],[(0,[z13,z2,z716,z4,z5,z6]),(0,[z254,z2,z3,z4,z5,z6]),(0,[z2,z3,z4,z712,z5,z6]),(0,[z261,z2,z3,z4,z5,z26]),(0,[z262,z2,z3,z4,z5,z26]),(0,[z100,z1,z114,z4,z32,z6]),(0,[z100,z230,z3,z4,z32,z6]),(0,[z999,z1,z2,z3,z4,z5]),(0,[z103,z2,z3,z4,z104,z219])]],
   [[(0,[z75,z37,z3,z4,z379,z6]),(0,[z1,z250,z23,z4,z5,z6]),(0,[z1,z2,z4,z5,z6,z1000]),(0,[z1001,z1,z2,z4,z5,z6])],[(0,[z1,z2,z3,z1002,z5,z6]),(0,[z2,z3,z4,z5,z721,z126]),(0,[z1,z2,z3,z4,z1003,z6]),(0,[z1,z2,z322,z4,z5,z405]),(0,[z209,z2,z3,z4,z5,z9]),(0,[z1,z2,z220,z233,z5,z9]),(0,[z362,z1,z2,z3,z5,z614])],[(0,[z1,z2,z3,z4,z1004,z6]),(0,[z2,z3,z559,z4,z5,z6]),(0,[z96,z2,z3,z4,z5,z127]),(0,[z1,z2,z3,z4,z5,z1005])],[(0,[z1,z2,z23,z4,z5,z26]),(0,[z1,z2,z23,z1006,z5,z6]),(0,[z1,z2,z402,z4,z5,z6])],[(0,[z1,z2,z304,z4,z446,z6]),(0,[z1,z2,z3,z4,z5,z1007])],[(0,[z1,z2,z3,z4,z5,z1008]),(0,[z1,z2,z3,z4,z5,z1009]),(0,[z57,z1,z3,z840,z5,z6]),(0,[z1,z41,z3,z30,z5,z180])],[(0,[z1,z2,z3,z4,z1010,z6]),(0,[z1,z2,z8,z4,z379,z6]),(0,[z1,z2,z72,z4,z5,z629]),(0,[z1011,z1,z2,z4,z5,z6])],[(0,[z2,z3,z4,z1012,z5,z6]),(0,[z19,z2,z3,z4,z5,z44]),(0,[z70,z2,z8,z71,z5,z6]),(0,[z102,z1,z2,z4,z5,z27]),(0,[z866,z2,z3,z4,z5,z6]),(0,[z2,z3,z4,z5,z26,z982]),(0,[z120,z1,z2,z3,z5,z614]),(0,[z1013,z1,z2,z4,z5,z6]),(0,[z1,z2,z1014,z4,z5,z6])],[(0,[z1,z2,z4,z5,z6,z1015]),(0,[z1,z679,z8,z4,z5,z6])],[(0,[z1,z2,z1016,z4,z5,z6]),(0,[z2,z334,z3,z4,z65,z6]),(0,[z1,z2,z344,z4,z5,z9])],[(0,[z1,z2,z3,z1017,z5,z6]),(0,[z19,z2,z3,z4,z5,z62]),(0,[z34,z2,z3,z4,z5,z26]),(0,[z1,z317,z332,z4,z5,z9])],[(0,[z1,z2,z3,z937,z4,z6]),(0,[z1,z2,z3,z4,z725,z6]),(0,[z2,z3,z4,z35,z5,z9])],[(0,[z1,z2,z67,z4,z259,z6]),(0,[z1018,z2,z3,z4,z5,z6]),(0,[z1019,z2,z408,z4,z5,z6])],[(0,[z188,z3,z4,z653,z5,z6]),(0,[z81,z1,z2,z4,z5,z6])],[(0,[z1020,z1,z2,z4,z5,z6])],[(0,[z68,z620,z3,z4,z5,z6]),(0,[z154,z2,z23,z4,z5,z6]),(0,[z1,z1021,z3,z4,z5,z6])]],
   [[(0,[z1,z2,z3,z4,z5,z1022]),(0,[z1,z2,z4,z5,z6,z903])],[(0,[z188,z3,z662,z4,z5,z6]),(0,[z1,z2,z1023,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z1024])],[(0,[z59,z1,z2,z23,z4,z5]),(0,[z100,z1,z3,z4,z725,z6]),(0,[z78,z1,z2,z4,z5,z27]),(0,[z1,z2,z3,z4,z26,z993])],[(0,[z1,z2,z3,z1025,z5,z6]),(0,[z1,z2,z3,z475,z379,z6]),(0,[z19,z2,z3,z4,z5,z126]),(0,[z2,z8,z733,z4,z5,z6]),(0,[z1,z2,z322,z4,z5,z26]),(0,[z102,z103,z2,z3,z4,z5])],[(0,[z1,z2,z1026,z4,z5,z6]),(0,[z43,z1,z3,z24,z5,z6]),(0,[z1,z2,z23,z176,z5,z6]),(0,[z1,z364,z8,z4,z5,z6])],[(0,[z1,z2,z3,z4,z1027,z6]),(0,[z1,z2,z23,z4,z5,z180]),(0,[z1,z2,z422,z4,z5,z73]),(0,[z1,z2,z169,z4,z5,z9])],[(0,[z1,z2,z427,z4,z259,z6]),(0,[z1,z2,z3,z4,z5,z1028]),(0,[z1,z2,z4,z5,z6,z1029])],[(0,[z2,z8,z4,z5,z62,z26]),(0,[z1030,z1,z2,z3,z5,z26]),(0,[z1,z2,z332,z4,z5,z26])],[(0,[z1,z2,z3,z4,z1031,z6]),(0,[z2,z3,z39,z36,z5,z6]),(0,[z68,z188,z23,z4,z5,z6]),(0,[z1,z3,z4,z5,z9,z252]),(0,[z1,z2,z8,z4,z5,z429]),(0,[z2,z3,z4,z5,z6,z1032]),(0,[z1,z2,z1033,z4,z5,z6])],[(0,[z51,z1,z2,z198,z110,z5])],[(0,[z1,z2,z3,z4,z1034,z6]),(0,[z122,z1,z2,z4,z330,z91])],[(0,[z68,z188,z3,z4,z5,z17]),(0,[z1,z2,z175,z4,z5,z464]),(0,[z1,z2,z3,z1035,z4,z6])],[(0,[z59,z1,z2,z8,z4,z5]),(0,[z1,z2,z3,z4,z5,z1036]),(0,[z1037,z2,z3,z4,z5,z6])],[(1,[z2,z3,z4,z5,z721]),(0,[z244,z2,z3,z4,z5,z26]),(0,[z1,z2,z3,z117,z33,z6])],[(0,[z1,z2,z1038,z4,z5,z6])]],
   [[(0,[z1,z2,z23,z4,z5,z205]),(0,[z374,z1,z3,z4,z32,z6]),(0,[z1,z2,z3,z249,z5,z50]),(0,[z1,z2,z3,z4,z1039,z6]),(0,[z2,z3,z4,z104,z410,z219])],[(0,[z209,z2,z23,z4,z5,z6]),(0,[z1,z2,z4,z5,z1040,z6]),(0,[z1041,z2,z3,z4,z5,z6]),(0,[z1,z459,z3,z4,z5,z9]),(0,[z1,z2,z3,z463,z5,z121])],[(0,[z70,z59,z2,z3,z4,z5]),(0,[z1,z215,z8,z4,z5,z6])],[(0,[z1,z2,z1042,z4,z5,z6]),(0,[z1,z8,z267,z4,z5,z6]),(0,[z1,z2,z3,z4,z1043,z6]),(0,[z100,z244,z3,z4,z32,z6])],[(0,[z1044,z2,z3,z4,z5,z6]),(0,[z1045,z1,z2,z4,z5,z6])],[(0,[z1,z2,z3,z4,z1046,z6]),(0,[z1,z2,z3,z1047,z5,z6]),(0,[z1,z608,z23,z4,z5,z6]),(0,[z1,z2,z408,z4,z5,z561]),(0,[z51,z1,z2,z110,z5,z6])],[(0,[z1,z2,z3,z4,z5,z1048]),(0,[z100,z1,z3,z4,z32,z133]),(0,[z1,z2,z3,z4,z5,z1049])],[(0,[z2,z3,z4,z179,z5,z9]),(0,[z232,z2,z3,z4,z5,z26])],[(0,[z75,z37,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z192]),(0,[z1,z2,z3,z4,z235,z263]),(0,[z1,z2,z114,z4,z5,z413]),(0,[z1,z2,z3,z1050,z5,z6]),(0,[z130,z1,z3,z4,z5,z26]),(1,[z1,z2,z774,z5,z6])],[(0,[z1,z23,z4,z530,z5,z6]),(0,[z1,z2,z3,z4,z5,z1051]),(0,[z1,z2,z1052,z4,z5,z6])],[(0,[z401,z1,z2,z4,z5,z150]),(0,[z1,z115,z8,z4,z5,z6]),(0,[z1053,z2,z3,z4,z5,z6]),(0,[z789,z2,z3,z4,z5,z9])],[(0,[z669,z2,z3,z4,z65,z6]),(0,[z2,z3,z1054,z4,z5,z6]),(0,[z1,z2,z1055,z4,z5,z6]),(0,[z1,z2,z1056,z4,z5,z6])],[(0,[z1,z2,z3,z1057,z5,z6]),(0,[z1,z2,z3,z4,z5,z1058]),(0,[z1,z2,z1059,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z1060]),(0,[z452,z1,z2,z415,z5,z6]),(0,[z1061,z2,z3,z4,z5,z6]),(0,[z57,z3,z179,z24,z5,z6]),(0,[z1,z2,z177,z4,z5,z405])],[(0,[z1,z2,z1062,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z1063]),(0,[z1,z2,z23,z4,z243,z6]),(0,[z1064,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z341,z161])]],
   [[(0,[z1,z2,z3,z4,z5,z1065]),(0,[z786,z2,z8,z4,z5,z6]),(0,[z1,z2,z234,z4,z5,z398]),(0,[z244,z2,z3,z176,z5,z6]),(0,[z1,z2,z4,z5,z6,z1066]),(0,[z1,z1067,z3,z4,z5,z6])],[(0,[z59,z2,z3,z4,z136,z5]),(0,[z0,z2,z23,z136,z5,z6]),(0,[z92,z2,z8,z4,z5,z6]),(0,[z1,z2,z3,z123,z5,z50]),(0,[z1068,z2,z3,z4,z5,z6]),(0,[z2,z3,z4,z5,z1069,z6])],[(0,[z70,z2,z3,z321,z5,z6]),(0,[z230,z2,z3,z4,z208,z6]),(0,[z1070,z2,z3,z4,z5,z6]),(0,[z350,z2,z3,z4,z5,z9]),(0,[z2,z3,z4,z803,z5,z9]),(0,[z1,z2,z3,z4,z5,z1071]),(0,[z1,z2,z4,z5,z1072,z6])],[(0,[z1,z191,z3,z4,z5,z9]),(0,[z1,z2,z3,z4,z5,z1073])],[(0,[z1,z2,z23,z4,z5,z263]),(0,[z1,z2,z23,z849,z4,z6]),(0,[z416,z1,z3,z4,z5,z26])],[(0,[z1,z2,z67,z4,z5,z26]),(0,[z1,z2,z3,z4,z1074,z6]),(0,[z1,z1075,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z1076])],[(0,[z1,z2,z3,z4,z1077,z6]),(0,[z1,z41,z3,z30,z5,z6]),(0,[z1,z2,z408,z4,z5,z26])],[(0,[z1,z2,z1078,z4,z5,z6]),(0,[z1079,z2,z3,z4,z5,z6]),(0,[z1,z2,z8,z217,z140,z6]),(0,[z811,z1,z2,z4,z5,z9])],[(0,[z19,z2,z3,z4,z5,z17]),(0,[z0,z2,z3,z684,z5,z6]),(0,[z1,z2,z1080,z4,z5,z6])],[(0,[z2,z23,z4,z35,z5,z6]),(0,[z232,z2,z3,z176,z5,z6])],[(0,[z1,z2,z1081,z4,z5,z6]),(0,[z1,z595,z23,z4,z5,z6])],[(0,[z209,z2,z3,z4,z5,z346]),(0,[z261,z2,z106,z4,z5,z6]),(0,[z1,z2,z3,z4,z235,z6])],[(0,[z188,z772,z3,z4,z5,z6]),(0,[z68,z188,z3,z4,z5,z9]),(0,[z1,z2,z3,z1082,z5,z6]),(0,[z2,z3,z433,z71,z5,z6]),(0,[z1,z2,z1083,z4,z5,z6])],[(0,[z1084,z1,z2,z4,z5,z6]),(1,[z1,z2,z3,z4,z861])],[(0,[z1,z2,z3,z816,z5,z6]),(0,[z1,z2,z3,z4,z5,z1085]),(0,[z2,z23,z4,z5,z6,z62]),(0,[z1,z8,z4,z5,z9,z26])],[(0,[z13,z2,z14,z4,z5,z9])]],
   [[(0,[z1,z2,z427,z4,z5,z26]),(0,[z1,z2,z3,z4,z5,z253]),(0,[z100,z232,z3,z4,z32,z6]),(0,[z1,z2,z177,z4,z5,z26]),(0,[z1,z2,z220,z774,z5,z6])],[(0,[z1,z2,z1086,z4,z5,z6]),(0,[z282,z1,z2,z4,z5,z394]),(0,[z1087,z2,z3,z4,z5,z6]),(0,[z1,z2,z116,z4,z52,z6]),(0,[z1,z2,z3,z710,z4,z6]),(0,[z122,z1,z2,z3,z4,z861])],[(0,[z2,z37,z3,z4,z379,z6]),(0,[z1,z2,z3,z4,z379,z9]),(0,[z1,z2,z3,z1088,z5,z6]),(0,[z1,z2,z1089,z4,z5,z6]),(0,[z2,z3,z4,z1090,z5,z6]),(0,[z2,z3,z123,z35,z5,z121])],[(0,[z1,z2,z3,z1091,z5,z6]),(0,[z1092,z1,z2,z23,z4,z5]),(0,[z1,z2,z1093,z4,z5,z6])],[(0,[z60,z2,z3,z4,z331,z6])],[(0,[z1,z3,z4,z5,z168,z26]),(0,[z1,z2,z3,z123,z5,z777])],[(0,[z828,z2,z3,z4,z5,z9]),(0,[z120,z1,z2,z5,z285,z270])],[(0,[z1,z2,z23,z4,z5,z6]),(0,[z295,z1,z2,z4,z145,z6]),(0,[z2,z3,z4,z5,z1094,z6]),(0,[z1095,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z6,z861])],[(0,[z2,z3,z627,z4,z65,z6]),(0,[z1,z2,z23,z216,z5,z6]),(0,[z2,z8,z106,z4,z5,z9]),(0,[z1,z2,z4,z5,z9,z1066]),(0,[z1,z608,z3,z4,z5,z9]),(0,[z1,z2,z3,z4,z1096,z6]),(0,[z101,z296,z1,z2,z4,z5])],[(0,[z2,z3,z4,z5,z127,z17])],[(0,[z1,z2,z3,z4,z5,z17]),(0,[z1,z2,z3,z4,z5,z1097]),(0,[z1,z2,z1098,z4,z5,z6])],[(0,[z102,z1,z2,z4,z5,z394]),(0,[z1,z2,z114,z4,z5,z133]),(0,[z1,z2,z3,z4,z5,z1099]),(0,[z28,z1,z2,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z1100]),(0,[z1101,z2,z3,z4,z5,z6])],[(0,[z1102,z1,z2,z3,z4,z5]),(0,[z1,z29,z8,z4,z5,z6]),(0,[z1,z2,z3,z176,z5,z413]),(0,[z1,z2,z1103,z4,z5,z6])],[(0,[z38,z2,z39,z4,z5,z6]),(0,[z1,z2,z3,z5,z6,z777])],[(0,[z1,z2,z3,z4,z1104,z6]),(0,[z34,z2,z3,z4,z5,z6]),(0,[z60,z2,z3,z4,z712,z6]),(0,[z2,z106,z23,z4,z5,z6]),(0,[z918,z2,z8,z4,z5,z6]),(0,[z1105,z1,z2,z4,z5,z6]),(0,[z471,z2,z3,z4,z5,z26])],[(0,[z75,z37,z3,z36,z5,z6]),(0,[z19,z2,z3,z4,z5,z346]),(0,[z939,z1,z2,z4,z5,z6]),(0,[z1041,z2,z3,z4,z5,z429]),(0,[z54,z1,z2,z4,z5,z6])]],
   [[(0,[z421,z2,z39,z4,z5,z6]),(0,[z1,z2,z1106,z4,z5,z6]),(0,[z1,z2,z3,z681,z33,z6])],[(0,[z59,z1,z2,z3,z4,z5]),(0,[z1,z2,z3,z4,z5,z1107]),(0,[z315,z2,z234,z4,z5,z6]),(0,[z244,z2,z169,z4,z5,z6]),(0,[z1108,z1,z2,z4,z5,z6])],[(0,[z1,z2,z67,z4,z5,z205]),(0,[z1,z2,z1109,z4,z5,z6]),(0,[z2,z3,z816,z136,z5,z6]),(0,[z1,z2,z3,z4,z5,z1110]),(0,[z1,z2,z23,z4,z5,z349]),(0,[z350,z2,z23,z4,z5,z6]),(0,[z1,z8,z887,z4,z5,z6]),(0,[z1111,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z243,z9])],[(0,[z1,z2,z1112,z4,z5,z6]),(0,[z1,z2,z3,z69,z4,z5]),(0,[z1,z191,z23,z4,z5,z6]),(0,[z762,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z1113,z5,z6]),(0,[z1,z2,z1114,z4,z5,z6])],[(0,[z2,z427,z39,z4,z5,z6]),(0,[z0,z2,z3,z136,z5,z9]),(0,[z100,z1,z3,z4,z32,z26]),(0,[z1115,z2,z3,z4,z5,z26])],[(0,[z1,z2,z8,z36,z5,z6]),(0,[z2,z23,z4,z179,z5,z6]),(0,[z1116,z2,z3,z4,z5,z6])],[(0,[z1,z2,z1117,z4,z5,z6])],[(0,[z1,z29,z8,z4,z5,z349])],[(0,[z726,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z956,z5,z6])],[(0,[z1,z2,z3,z4,z5,z1118]),(0,[z232,z2,z169,z4,z5,z6])],[],[(0,[z94,z1,z23,z4,z5,z6]),(0,[z1030,z1,z2,z3,z5,z6]),(0,[z1,z41,z3,z840,z5,z6]),(0,[z2,z3,z4,z5,z410,z26]),(0,[z1119,z2,z3,z4,z5,z6])],[(0,[z1,z2,z427,z4,z5,z205]),(0,[z1,z2,z3,z4,z5,z1120]),(0,[z1121,z2,z3,z4,z5,z6]),(0,[z1,z31,z3,z4,z239,z405]),(0,[z1,z595,z3,z4,z5,z9]),(0,[z120,z1,z2,z3,z586,z5])],[(0,[z1,z2,z72,z484,z4,z5]),(0,[z1122,z1,z2,z4,z5,z6]),(0,[z1,z2,z1123,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z144]),(0,[z1,z2,z3,z4,z104,z533]),(0,[z81,z120,z1,z2,z4,z5])]],
   [[(0,[z1,z2,z3,z4,z5,z1124]),(0,[z1,z23,z4,z5,z500,z6]),(0,[z1,z2,z3,z4,z5,z1125])],[(0,[z1,z2,z3,z4,z5,z346]),(0,[z68,z2,z3,z4,z379,z6]),(0,[z1030,z1,z2,z23,z5,z6]),(0,[z1,z2,z3,z4,z5,z1126])],[(0,[z244,z2,z3,z4,z5,z6]),(0,[z1,z2,z23,z4,z379,z6]),(0,[z1127,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z123,z5,z121]),(0,[z1,z2,z3,z4,z5,z777])],[(0,[z68,z188,z3,z4,z5,z464]),(0,[z70,z2,z23,z71,z5,z6]),(0,[z2,z8,z559,z4,z5,z6]),(0,[z244,z2,z3,z216,z5,z6]),(0,[z1,z2,z3,z4,z5,z1128])],[(0,[z1,z2,z23,z4,z6,z860]),(0,[z1,z2,z3,z814,z4,z5]),(0,[z1,z2,z248,z4,z5,z26]),(0,[z1129,z1,z2,z3,z4,z5])],[(0,[z88,z2,z3,z4,z488,z6]),(0,[z1,z2,z1130,z4,z5,z6])],[(0,[z141,z2,z3,z4,z5,z6]),(0,[z88,z2,z3,z4,z208,z26]),(0,[z19,z2,z8,z4,z5,z126]),(0,[z1,z2,z3,z4,z5,z1131]),(0,[z100,z1,z3,z176,z32,z6])],[(0,[z1,z2,z1132,z4,z5,z6])],[(0,[z1,z2,z1133,z4,z5,z6]),(0,[z1,z2,z1134,z4,z5,z6])],[(0,[z1,z2,z3,z4,z1135,z6]),(0,[z1,z23,z4,z5,z32,z26])],[(0,[z1,z2,z3,z4,z5,z9]),(0,[z1,z2,z3,z1136,z5,z6]),(0,[z57,z1,z8,z24,z5,z6])],[(0,[z1,z2,z3,z4,z5,z1137]),(0,[z232,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z1138]),(0,[z120,z1,z2,z8,z5,z270]),(0,[z1139,z2,z3,z106,z4,z5]),(0,[z1,z3,z840,z24,z5,z6]),(0,[z1,z2,z3,z216,z5,z9]),(0,[z1,z2,z217,z392,z140,z6])],[(0,[z232,z2,z3,z216,z5,z6])],[(0,[z1,z2,z169,z4,z5,z413]),(0,[z92,z2,z3,z4,z5,z9]),(0,[z1,z2,z4,z5,z73,z903])],[(0,[z1,z2,z8,z4,z5,z439]),(0,[z262,z2,z3,z4,z243,z6]),(0,[z2,z3,z1140,z4,z5,z6]),(0,[z1141,z1,z2,z3,z4,z5]),(0,[z209,z2,z3,z4,z5,z590]),(0,[z1142,z1,z2,z3,z4,z5])],[(0,[z1,z2,z3,z4,z5,z861])]],
   [[(0,[z451,z2,z3,z136,z5,z6]),(0,[z1,z41,z23,z4,z5,z26]),(0,[z1,z2,z8,z117,z33,z6]),(0,[z1,z31,z3,z4,z239,z26]),(0,[z2,z3,z4,z5,z795,z9])],[(0,[z1,z2,z1143,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z804]),(0,[z254,z2,z72,z3,z4,z5])],[(0,[z1144,z1,z2,z3,z4,z5]),(0,[z1,z2,z3,z4,z353,z245]),(0,[z1,z2,z3,z4,z5,z903]),(0,[z1,z2,z527,z4,z5,z73]),(0,[z1,z2,z3,z217,z439,z140]),(0,[z1,z2,z1145,z4,z5,z6])],[(0,[z1,z2,z1146,z4,z5,z6]),(0,[z262,z2,z3,z4,z5,z263]),(0,[z230,z2,z3,z4,z5,z26])],[(0,[z1,z2,z3,z4,z5,z1147]),(0,[z1148,z1,z2,z3,z4,z5]),(0,[z2,z3,z4,z5,z9,z1032])],[(0,[z1,z2,z23,z4,z5,z429]),(0,[z1,z2,z8,z4,z198,z5]),(0,[z1149,z1,z2,z4,z5,z26])],[(0,[z1,z2,z1150,z4,z5,z6]),(0,[z1,z2,z1151,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z1152]),(0,[z1,z2,z3,z4,z104,z219])],[(0,[z1,z2,z3,z4,z1153,z6]),(0,[z1,z3,z4,z5,z9,z629])],[(0,[z1,z2,z69,z23,z4,z5]),(0,[z771,z2,z177,z4,z5,z6])],[(0,[z1,z2,z206,z4,z5,z26]),(0,[z1,z2,z114,z4,z5,z26])],[(0,[z75,z37,z8,z4,z5,z6]),(0,[z2,z3,z4,z712,z65,z6]),(0,[z130,z1,z8,z4,z5,z26]),(0,[z1,z41,z213,z30,z5,z6]),(0,[z54,z1154,z2,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z1155]),(0,[z1,z2,z3,z1156,z4,z5])],[(0,[z1,z2,z3,z4,z379,z346]),(0,[z1,z2,z3,z1157,z4,z6]),(0,[z1158,z1,z2,z3,z4,z5]),(0,[z567,z1,z3,z4,z5,z26])],[(0,[z1,z2,z8,z4,z977,z5]),(0,[z1,z317,z3,z4,z5,z975]),(0,[z1,z2,z3,z4,z5,z1159]),(0,[z102,z1,z2,z4,z5,z903])],[(0,[z1,z2,z3,z4,z5,z1160])],[]],
   [[(0,[z1,z2,z3,z4,z1161,z6])],[(0,[z2,z3,z36,z5,z127,z6]),(0,[z1092,z1,z2,z3,z4,z5]),(0,[z1144,z1,z2,z8,z4,z5]),(0,[z1162,z2,z3,z4,z5,z6])],[(0,[z2,z3,z4,z379,z127,z6]),(0,[z57,z1,z402,z24,z5,z6]),(0,[z1,z2,z3,z1163,z5,z6])],[(0,[z1,z2,z234,z4,z5,z26]),(0,[z1164,z2,z3,z4,z5,z6])],[(0,[z1,z2,z427,z4,z5,z6]),(0,[z2,z3,z71,z496,z5,z6]),(0,[z1,z2,z1165,z4,z5,z6]),(0,[z1,z2,z177,z4,z5,z6]),(0,[z1,z2,z1166,z4,z5,z6]),(0,[z1070,z2,z8,z4,z5,z6]),(0,[z1167,z2,z3,z4,z5,z6]),(0,[z1,z2,z1168,z4,z5,z6])],[(0,[z108,z2,z3,z71,z5,z6]),(0,[z1169,z2,z3,z4,z5,z6]),(0,[z1,z320,z3,z4,z5,z26])],[(0,[z261,z2,z3,z4,z5,z6]),(0,[z262,z2,z3,z4,z5,z6]),(0,[z70,z2,z3,z71,z5,z9]),(0,[z1,z2,z3,z4,z5,z1170]),(0,[z1171,z2,z3,z4,z5,z6]),(0,[z1,z2,z322,z4,z5,z429])],[(0,[z100,z1,z169,z4,z32,z6])],[(0,[z1,z2,z3,z4,z5,z1172]),(0,[z1,z8,z527,z4,z5,z6]),(0,[z1173,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z1174])],[(0,[z1,z594,z23,z4,z5,z6]),(0,[z1175,z2,z3,z4,z5,z6]),(0,[z51,z350,z2,z110,z5,z6])],[(0,[z1,z2,z114,z176,z5,z6]),(0,[z1101,z2,z3,z4,z5,z439])],[(0,[z13,z2,z106,z4,z5,z6]),(0,[z19,z2,z3,z4,z5,z461]),(0,[z315,z2,z3,z4,z5,z398]),(0,[z1,z2,z408,z4,z5,z180]),(0,[z1,z2,z4,z5,z26,z285])],[(0,[z92,z2,z23,z4,z5,z6]),(0,[z1,z2,z72,z4,z5,z128]),(0,[z1,z2,z3,z4,z5,z1176]),(0,[z102,z209,z2,z3,z4,z5]),(0,[z1,z2,z1177,z4,z5,z6])],[(0,[z2,z3,z36,z208,z5,z6]),(0,[z1,z2,z8,z475,z5,z6]),(0,[z1,z8,z23,z4,z5,z9]),(0,[z1,z2,z4,z52,z769,z6])],[(0,[z60,z2,z3,z4,z65,z26]),(0,[z1,z2,z1178,z4,z5,z6]),(0,[z54,z1,z2,z4,z5,z439])]],
   [[(0,[z1,z193,z8,z4,z5,z6]),(0,[z2,z3,z4,z5,z955,z6])],[(0,[z1,z2,z3,z4,z5,z464]),(0,[z2,z37,z3,z36,z5,z6]),(0,[z1,z2,z3,z36,z5,z9]),(0,[z1,z2,z3,z216,z32,z6]),(0,[z409,z2,z3,z4,z5,z26]),(0,[z1,z2,z3,z4,z5,z181])],[(0,[z471,z2,z3,z4,z5,z6]),(0,[z1,z599,z8,z4,z5,z6]),(0,[z2,z3,z4,z5,z289,z9]),(0,[z1179,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z1180,z5])],[(0,[z1,z2,z3,z4,z5,z1181]),(0,[z1,z2,z23,z217,z140,z6]),(0,[z1,z2,z3,z123,z5,z556])],[(0,[z1,z2,z67,z4,z379,z6]),(0,[z261,z2,z8,z4,z5,z26]),(0,[z254,z2,z8,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z1182])],[(0,[z59,z188,z2,z3,z4,z5]),(0,[z1,z2,z3,z1183,z5,z6])],[(0,[z1,z3,z4,z5,z6,z975]),(0,[z1,z2,z1184,z4,z5,z6])],[],[(0,[z100,z1,z3,z4,z32,z6]),(0,[z1115,z2,z3,z4,z5,z6])],[(0,[z1,z2,z1185,z4,z5,z6]),(0,[z1,z772,z3,z4,z5,z6]),(0,[z1,z2,z3,z854,z4,z6]),(0,[z100,z1,z3,z216,z32,z6]),(0,[z1,z2,z1186,z3,z4,z5])],[],[(0,[z1,z2,z3,z4,z5,z1187]),(0,[z1,z2,z1188,z4,z5,z6]),(0,[z18,z2,z3,z4,z5,z127]),(0,[z1,z2,z322,z4,z5,z6]),(0,[z103,z2,z3,z4,z5,z26]),(0,[z1,z2,z1189,z3,z4,z5]),(0,[z54,z1,z2,z217,z140,z6])],[(0,[z1,z2,z8,z4,z5,z17]),(0,[z1,z2,z3,z4,z1190,z6]),(0,[z18,z2,z3,z547,z4,z5]),(0,[z1191,z1,z2,z23,z4,z5]),(0,[z315,z2,z3,z4,z5,z26]),(0,[z1192,z1,z2,z3,z4,z5])],[(0,[z1,z2,z3,z1193,z5,z6]),(0,[z1,z2,z4,z5,z392,z26])],[(0,[z101,z1,z2,z4,z89,z9]),(0,[z1194,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z1195])],[(0,[z1,z2,z427,z4,z379,z6]),(0,[z1,z2,z332,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z1196]),(0,[z120,z1,z2,z3,z5,z270])]],
   [[(0,[z2,z3,z71,z4,z379,z6])],[(0,[z2,z3,z674,z4,z208,z6]),(0,[z1,z2,z131,z4,z5,z26])],[(0,[z1,z2,z3,z4,z5,z1197])],[(0,[z2,z3,z4,z5,z127,z346]),(0,[z1,z2,z23,z5,z6,z909]),(0,[z1198,z1,z2,z4,z5,z6]),(0,[z1,z317,z344,z4,z5,z9])],[(0,[z120,z1,z2,z23,z5,z270]),(0,[z1,z2,z3,z4,z104,z161]),(0,[z2,z3,z1199,z4,z5,z6])],[(0,[z1,z2,z3,z4,z259,z26]),(0,[z1200,z1,z2,z3,z4,z5]),(0,[z1019,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z5,z1201,z6])],[(0,[z1,z2,z3,z4,z1202,z6]),(0,[z1,z2,z23,z913,z4,z5]),(0,[z102,z236,z1,z2,z4,z5])],[(1,[z2,z3,z816,z5,z6]),(0,[z1,z2,z3,z4,z5,z1203]),(0,[z3,z4,z5,z9,z62,z26]),(0,[z736,z2,z3,z4,z5,z26]),(0,[z2,z3,z118,z4,z5,z26])],[(0,[z88,z59,z2,z3,z4,z5]),(0,[z1,z2,z248,z4,z5,z6]),(0,[z209,z2,z422,z3,z4,z5]),(0,[z101,z1,z2,z4,z769,z6]),(0,[z1204,z2,z3,z4,z5,z6]),(0,[z1,z2,z4,z5,z6,z1205])],[(0,[z7,z1,z2,z4,z89,z6]),(0,[z1,z2,z220,z233,z5,z26])],[(0,[z1,z2,z3,z4,z5,z1206]),(0,[z261,z8,z23,z4,z5,z6]),(0,[z1,z2,z220,z107,z5,z6]),(0,[z1,z2,z1207,z4,z5,z6]),(0,[z2,z3,z4,z1208,z5,z26]),(0,[z122,z1,z2,z3,z4,z134])],[(0,[z1,z2,z3,z4,z5,z1209]),(0,[z1210,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z1211,z5]),(0,[z923,z2,z23,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z1212]),(0,[z1,z2,z1213,z4,z5,z6]),(0,[z1,z2,z4,z1214,z5,z6])],[(0,[z1,z2,z3,z1215,z5,z6]),(0,[z404,z1,z2,z501,z5,z6]),(0,[z1216,z1,z2,z4,z5,z6]),(0,[z1,z594,z3,z4,z5,z9]),(0,[z1217,z2,z3,z4,z5,z6])],[(0,[z94,z1,z887,z4,z5,z6]),(0,[z1218,z2,z3,z4,z5,z6]),(0,[z1,z2,z213,z4,z5,z9])],[(0,[z13,z2,z3,z4,z379,z6]),(0,[z1,z2,z3,z4,z5,z1219]),(0,[z1,z2,z528,z4,z5,z73]),(0,[z1,z2,z234,z4,z243,z6])]],
   [[(0,[z68,z2,z3,z36,z5,z6]),(0,[z101,z296,z1,z2,z4,z89])],[(0,[z1,z2,z3,z1220,z5,z6]),(0,[z1,z2,z23,z36,z5,z6]),(0,[z1,z2,z1221,z4,z5,z6]),(0,[z1,z2,z8,z4,z5,z144]),(0,[z1,z2,z344,z4,z5,z26])],[(0,[z1,z2,z3,z176,z5,z133]),(0,[z100,z3,z4,z289,z32,z6]),(0,[z1,z2,z177,z4,z5,z429]),(0,[z1,z623,z3,z4,z5,z26])],[(1,[z1,z3,z840,z5,z6]),(0,[z1,z3,z4,z239,z725,z6]),(0,[z2,z3,z4,z35,z5,z26])],[(0,[z358,z1,z3,z4,z32,z6]),(0,[z1,z2,z234,z4,z5,z263]),(0,[z1,z2,z3,z4,z1222,z6]),(0,[z1,z31,z3,z4,z239,z6])],[(0,[z1,z2,z1223,z4,z5,z6]),(0,[z70,z2,z3,z609,z5,z6]),(0,[z1,z2,z1224,z4,z5,z6]),(0,[z1,z2,z4,z5,z6,z285])],[(0,[z60,z2,z3,z4,z379,z6]),(0,[z1,z2,z3,z4,z5,z1225]),(0,[z1,z2,z1226,z4,z5,z6]),(0,[z1,z2,z8,z814,z4,z5]),(0,[z1,z2,z3,z217,z140,z9]),(0,[z51,z1,z2,z430,z5,z6]),(0,[z2,z3,z1227,z4,z5,z6])],[(0,[z230,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z1228,z5,z6]),(0,[z1,z3,z4,z840,z5,z6])],[(0,[z141,z2,z8,z4,z5,z6])],[(0,[z2,z3,z4,z5,z6,z1229]),(0,[z1,z2,z3,z710,z140,z6])],[(0,[z2,z3,z1230,z4,z5,z6]),(0,[z1,z2,z528,z4,z5,z77]),(0,[z57,z1,z3,z24,z235,z6]),(0,[z135,z1,z2,z4,z5,z392])],[(1,[z1,z2,z4,z5,z903]),(0,[z1,z2,z1231,z4,z5,z6])],[(0,[z1,z2,z67,z4,z5,z6]),(0,[z1,z2,z3,z4,z1232,z6]),(0,[z1,z2,z8,z4,z5,z9]),(0,[z1,z887,z23,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z1233])],[(0,[z2,z3,z1234,z4,z5,z6]),(0,[z1,z23,z4,z5,z6,z252]),(0,[z1,z2,z8,z4,z5,z192]),(0,[z1,z2,z408,z4,z5,z6]),(0,[z1,z2,z114,z4,z5,z6]),(0,[z1139,z2,z8,z106,z4,z5])],[(0,[z1,z2,z3,z4,z5,z561]),(0,[z1,z2,z114,z216,z5,z6]),(0,[z1,z2,z4,z5,z26,z1235]),(0,[z1,z2,z774,z110,z5,z6]),(0,[z1,z2,z3,z4,z219,z861])],[]],
   [[(0,[z1,z662,z23,z4,z5,z6]),(0,[z2,z23,z4,z5,z289,z6]),(0,[z1,z2,z3,z123,z306,z5])],[(0,[z1,z2,z1236,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z413]),(0,[z1,z85,z3,z4,z5,z9])],[(0,[z1,z2,z3,z4,z259,z205]),(0,[z19,z2,z23,z4,z5,z126]),(0,[z1,z2,z3,z216,z5,z413]),(0,[z182,z1,z2,z3,z5,z95]),(0,[z1237,z2,z3,z4,z5,z6])],[],[(0,[z57,z315,z3,z24,z5,z6]),(0,[z1,z2,z4,z5,z6,z330])],[(0,[z1,z2,z4,z5,z6,z1238])],[(0,[z57,z1,z23,z24,z5,z6]),(0,[z102,z1,z2,z4,z667,z5])],[(0,[z1,z550,z23,z4,z5,z6]),(0,[z1,z2,z234,z4,z5,z6]),(0,[z261,z2,z434,z4,z5,z6]),(0,[z1239,z2,z3,z4,z5,z6])],[(0,[z2,z3,z581,z4,z5,z127]),(0,[z315,z2,z3,z4,z243,z6]),(0,[z1,z2,z4,z5,z1240,z6])],[(0,[z2,z3,z728,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z1241]),(0,[z1,z2,z3,z4,z353,z219]),(0,[z1242,z2,z3,z4,z5,z6])],[(0,[z75,z619,z3,z4,z5,z6]),(0,[z143,z2,z3,z136,z5,z6]),(0,[z1,z2,z3,z4,z5,z1243]),(0,[z1,z2,z23,z1035,z4,z6]),(0,[z1,z2,z23,z4,z5,z439]),(0,[z1,z2,z3,z922,z5,z6]),(0,[z1,z2,z3,z4,z5,z1244])],[(0,[z1,z2,z3,z36,z5,z346]),(0,[z75,z37,z3,z475,z5,z6]),(0,[z1,z2,z1245,z3,z4,z5]),(0,[z1,z2,z1246,z4,z5,z6]),(0,[z961,z2,z23,z4,z5,z6]),(0,[z1,z41,z8,z30,z5,z6]),(0,[z1,z2,z3,z4,z5,z1247])],[(0,[z2,z3,z716,z4,z5,z6]),(0,[z1248,z1,z2,z4,z5,z6]),(0,[z1,z2,z23,z117,z33,z6]),(0,[z1,z596,z3,z4,z5,z26]),(0,[z1,z2,z72,z4,z5,z903]),(0,[z1249,z2,z3,z4,z5,z6]),(0,[z2,z3,z4,z5,z1250,z6])],[(0,[z1251,z1,z2,z4,z5,z6]),(0,[z315,z2,z3,z4,z5,z263]),(0,[z1,z2,z4,z5,z9,z285])],[(0,[z1,z381,z3,z4,z5,z26])],[(0,[z75,z1,z23,z4,z5,z26]),(0,[z8,z106,z23,z4,z5,z6]),(0,[z2,z3,z1252,z4,z5,z6])]],
   [[(0,[z1,z2,z8,z4,z235,z6]),(0,[z1,z2,z3,z4,z5,z1253]),(0,[z254,z2,z3,z4,z5,z9]),(0,[z120,z1,z2,z3,z430,z5])],[(0,[z1,z2,z23,z4,z198,z5]),(0,[z1,z2,z3,z4,z5,z1254]),(0,[z1,z2,z3,z4,z5,z1255]),(0,[z2,z3,z4,z5,z9,z1229]),(0,[z1,z2,z4,z5,z6,z1256]),(0,[z2,z3,z117,z118,z33,z6])],[(0,[z230,z2,z3,z4,z379,z6]),(0,[z68,z188,z206,z4,z5,z6]),(0,[z1,z2,z3,z4,z1257,z6]),(0,[z2,z3,z106,z4,z5,z26]),(0,[z1,z2,z3,z216,z239,z6]),(0,[z101,z1,z2,z4,z134,z6]),(0,[z54,z135,z1,z2,z4,z5]),(0,[z2,z3,z4,z5,z439,z747])],[(0,[z1,z2,z1258,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z1259]),(0,[z2,z3,z745,z4,z5,z6]),(0,[z1,z2,z169,z4,z5,z133]),(0,[z1,z2,z3,z4,z1260,z5]),(0,[z2,z3,z559,z4,z5,z9])],[(0,[z261,z2,z39,z4,z5,z6]),(0,[z1,z2,z402,z4,z5,z9]),(0,[z1,z2,z3,z1261,z4,z5])],[(0,[z1,z2,z3,z4,z1262,z6]),(0,[z1,z2,z3,z4,z5,z1263]),(0,[z409,z2,z3,z4,z5,z6]),(0,[z1,z2,z8,z4,z5,z253]),(0,[z1264,z2,z3,z4,z5,z6])],[(0,[z75,z37,z23,z4,z5,z6]),(0,[z1,z2,z3,z1265,z4,z5]),(0,[z130,z1,z23,z4,z5,z26]),(0,[z1,z2,z3,z4,z1266,z6]),(0,[z1087,z2,z8,z4,z5,z6]),(0,[z1267,z2,z3,z4,z5,z6])],[],[(0,[z261,z2,z8,z4,z5,z6]),(0,[z262,z2,z8,z4,z5,z6]),(0,[z1,z2,z8,z4,z5,z1170])],[(0,[z1,z264,z8,z4,z5,z6]),(0,[z1,z2,z4,z5,z6,z1268])],[(0,[z1191,z1,z2,z3,z4,z5]),(0,[z1,z466,z3,z30,z5,z6]),(0,[z154,z2,z3,z4,z5,z26])],[(0,[z1,z2,z377,z617,z5,z6]),(0,[z1,z23,z142,z4,z5,z6])],[(0,[z1,z2,z1269,z4,z5,z6]),(0,[z1,z2,z887,z4,z5,z6]),(0,[z78,z209,z2,z3,z4,z5])],[(0,[z1064,z2,z23,z4,z5,z6]),(0,[z738,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z1270]),(0,[z1,z2,z4,z5,z26,z330]),(0,[z81,z1,z2,z4,z5,z9])],[(0,[z1,z2,z3,z1271,z4,z5]),(0,[z103,z2,z3,z4,z5,z6])]],
   [[(0,[z315,z2,z3,z4,z5,z6]),(0,[z1,z2,z175,z4,z5,z26]),(0,[z1,z2,z3,z176,z5,z26]),(0,[z1272,z2,z3,z4,z5,z6]),(0,[z1,z2,z4,z5,z439,z392]),(0,[z81,z120,z1,z2,z5,z270]),(0,[z2,z3,z4,z1273,z5,z6])],[(0,[z1,z2,z3,z1274,z5,z6]),(0,[z1,z2,z4,z5,z392,z6])],[(0,[z1,z31,z3,z4,z239,z429])],[(0,[z1,z2,z67,z36,z5,z6]),(0,[z2,z3,z4,z5,z410,z6]),(0,[z34,z2,z8,z4,z5,z6]),(0,[z1,z2,z8,z4,z5,z181]),(0,[z1,z42,z3,z4,z5,z9]),(0,[z102,z1,z2,z4,z5,z58])],[(0,[z68,z188,z3,z4,z5,z26]),(0,[z1,z41,z23,z30,z5,z6]),(0,[z723,z2,z3,z4,z5,z26]),(0,[z1275,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z1276]),(0,[z1,z2,z131,z4,z5,z6]),(0,[z135,z1,z2,z8,z4,z5]),(0,[z1,z2,z3,z216,z5,z133])],[(0,[z1,z2,z3,z4,z104,z861])],[(0,[z1111,z2,z8,z4,z5,z6]),(0,[z1139,z1,z2,z3,z4,z5]),(0,[z1,z2,z4,z5,z6,z1235])],[(0,[z1,z2,z1277,z4,z5,z6]),(0,[z1,z2,z8,z69,z4,z5]),(0,[z1,z2,z402,z4,z235,z6])],[(0,[z1,z2,z3,z4,z259,z6]),(0,[z772,z37,z3,z4,z5,z6]),(0,[z57,z1,z3,z24,z5,z9])],[(0,[z1,z2,z23,z475,z5,z6]),(0,[z1,z2,z3,z4,z243,z398]),(1,[z1,z3,z4,z5,z975]),(0,[z1,z3,z4,z5,z26,z307])],[(0,[z1,z2,z3,z4,z5,z1278]),(0,[z2,z3,z118,z4,z5,z6])],[(0,[z209,z2,z3,z4,z5,z26])],[(0,[z1,z2,z3,z4,z5,z1279]),(0,[z88,z2,z3,z4,z208,z6]),(0,[z18,z2,z8,z4,z5,z127]),(0,[z1,z419,z23,z4,z5,z6]),(0,[z1,z2,z3,z4,z879,z5]),(0,[z1,z2,z220,z233,z5,z6])],[(0,[z1,z2,z427,z36,z5,z6]),(0,[z2,z3,z4,z1208,z5,z6]),(0,[z1,z2,z1280,z4,z5,z6])],[(0,[z2,z3,z71,z36,z5,z6]),(0,[z2,z3,z4,z5,z62,z17]),(0,[z230,z2,z3,z4,z65,z6]),(0,[z2,z23,z4,z5,z6,z902]),(0,[z1,z2,z3,z117,z33,z9]),(0,[z1,z2,z3,z4,z5,z1281])]],
   [[(0,[z75,z37,z3,z4,z5,z346]),(0,[z88,z2,z3,z4,z454,z6]),(0,[z254,z2,z23,z4,z5,z6]),(0,[z262,z2,z402,z4,z5,z6]),(0,[z296,z1,z2,z4,z52,z5]),(0,[z1282,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z1283]),(0,[z1,z3,z4,z5,z9,z975]),(0,[z51,z92,z2,z110,z5,z6]),(0,[z54,z1242,z2,z4,z5,z6])],[(0,[z1,z2,z1284,z4,z5,z6]),(0,[z1,z2,z3,z4,z1285,z5])],[(0,[z182,z1,z2,z3,z5,z270]),(0,[z1,z2,z4,z5,z6,z1286])],[],[(0,[z2,z23,z4,z911,z5,z6]),(0,[z63,z1,z23,z4,z5,z6]),(0,[z1,z2,z344,z4,z5,z6]),(0,[z1,z2,z1287,z4,z5,z6]),(0,[z1045,z1,z2,z4,z5,z9])],[(0,[z1,z2,z8,z4,z5,z346]),(0,[z68,z188,z175,z4,z5,z6]),(0,[z1139,z1,z2,z8,z4,z5]),(0,[z1,z2,z3,z4,z5,z1288]),(0,[z51,z1,z2,z110,z5,z9])],[(0,[z244,z2,z8,z4,z5,z6]),(0,[z1,z2,z8,z123,z5,z121]),(0,[z1,z2,z3,z4,z5,z1289]),(0,[z1,z2,z1290,z4,z5,z6])],[(0,[z1,z2,z23,z4,z5,z17]),(0,[z1,z382,z3,z4,z5,z9]),(0,[z1,z2,z3,z4,z5,z1291])],[(0,[z75,z37,z3,z4,z5,z9]),(0,[z2,z23,z4,z5,z62,z26]),(0,[z130,z1,z3,z4,z5,z975]),(0,[z130,z209,z3,z4,z5,z26])],[(0,[z358,z37,z3,z4,z5,z6]),(0,[z1,z29,z887,z4,z5,z6]),(0,[z1,z2,z3,z4,z243,z26]),(0,[z96,z2,z3,z4,z5,z520]),(0,[z945,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z710,z217,z6]),(0,[z1,z2,z3,z5,z777,z270])],[(0,[z38,z2,z69,z39,z4,z5]),(0,[z1,z642,z8,z4,z5,z6])],[(0,[z0,z2,z3,z136,z5,z26]),(0,[z1149,z1,z2,z4,z5,z6]),(0,[z2,z3,z4,z5,z1292,z6]),(0,[z1293,z2,z3,z4,z5,z6])],[(0,[z75,z59,z2,z3,z4,z5]),(0,[z1294,z2,z3,z4,z5,z6])],[(0,[z13,z2,z3,z36,z5,z6])],[(0,[z1,z2,z3,z4,z1295,z6]),(0,[z869,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z405])]],
   [[(0,[z1,z2,z206,z4,z5,z6]),(0,[z1,z2,z1296,z4,z5,z6]),(0,[z232,z2,z8,z4,z5,z6]),(0,[z1,z2,z1297,z4,z5,z6]),(0,[z1,z2,z422,z4,z5,z498]),(0,[z2,z3,z4,z5,z850,z26])],[(0,[z2,z23,z559,z4,z5,z6]),(0,[z2,z8,z4,z5,z410,z6]),(0,[z872,z2,z3,z4,z5,z6]),(0,[z1,z2,z169,z4,z5,z26]),(0,[z1,z2,z3,z4,z5,z1298])],[(1,[z772,z3,z4,z5,z6]),(0,[z209,z2,z3,z4,z5,z127]),(0,[z1,z2,z3,z4,z1299,z6]),(0,[z1,z2,z3,z4,z5,z398]),(0,[z1,z2,z213,z4,z5,z561])],[(0,[z1300,z1,z2,z3,z4,z5]),(0,[z1,z2,z3,z1301,z5,z6])],[(0,[z1,z2,z3,z4,z1302,z6]),(0,[z1,z2,z3,z475,z5,z346]),(0,[z1,z2,z716,z4,z5,z6]),(0,[z989,z2,z3,z4,z5,z6]),(0,[z1,z317,z3,z4,z5,z9])],[(0,[z60,z2,z3,z36,z5,z6]),(0,[z2,z3,z4,z5,z6,z1303])],[(0,[z1,z2,z3,z4,z1304,z6]),(0,[z1,z2,z3,z4,z5,z1305]),(0,[z1,z23,z4,z5,z6,z272]),(0,[z315,z2,z3,z24,z5,z6]),(0,[z2,z177,z1252,z4,z5,z6])],[(0,[z2,z3,z4,z208,z98,z6]),(0,[z1,z3,z598,z4,z5,z26]),(0,[z1,z41,z3,z30,z5,z9]),(0,[z1,z2,z3,z4,z5,z1306])],[(0,[z1307,z1,z2,z4,z5,z6]),(0,[z135,z1,z2,z3,z217,z140])],[(0,[z1,z2,z3,z4,z712,z6])],[(0,[z75,z772,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z1308]),(0,[z70,z2,z3,z266,z5,z6]),(0,[z1,z2,z1309,z4,z5,z6]),(0,[z1,z2,z8,z4,z104,z219]),(0,[z254,z2,z3,z123,z5,z121])],[(0,[z19,z2,z3,z4,z5,z311]),(0,[z1,z2,z3,z4,z235,z9]),(0,[z374,z1,z3,z24,z5,z6]),(0,[z101,z1,z2,z4,z312,z6])],[(0,[z1,z2,z3,z475,z5,z9]),(0,[z1,z2,z3,z4,z5,z1310]),(0,[z1,z2,z23,z4,z5,z144])],[(0,[z1,z2,z1311,z4,z5,z6]),(0,[z1,z2,z1312,z4,z5,z6])],[(0,[z81,z1,z2,z123,z4,z5])]],
   [[(0,[z244,z2,z23,z4,z5,z6]),(0,[z315,z2,z3,z30,z5,z6]),(0,[z2,z3,z4,z5,z1303,z429]),(0,[z1,z419,z3,z4,z5,z9]),(0,[z1,z2,z3,z1313,z5,z6]),(0,[z1,z2,z72,z4,z5,z73])],[(0,[z2,z3,z118,z24,z5,z6]),(0,[z1,z599,z3,z4,z5,z9]),(0,[z1,z2,z3,z4,z1314,z6]),(0,[z1154,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z26]),(0,[z70,z2,z3,z503,z5,z6]),(0,[z1,z2,z3,z1006,z5,z6]),(0,[z2,z3,z4,z179,z5,z26]),(1,[z1,z3,z4,z725,z6]),(0,[z1,z2,z116,z4,z52,z9]),(0,[z1087,z2,z3,z4,z5,z9])],[(0,[z75,z37,z427,z4,z5,z6]),(0,[z1,z2,z3,z1315,z5,z6]),(0,[z1,z2,z8,z4,z5,z413]),(0,[z282,z1,z2,z4,z5,z150]),(0,[z1,z2,z1316,z4,z5,z6]),(0,[z1,z2,z169,z176,z5,z6]),(0,[z1,z2,z3,z216,z5,z26]),(1,[z1,z2,z3,z710,z6])],[(0,[z38,z59,z2,z39,z4,z5]),(0,[z1,z2,z3,z4,z1317,z6]),(0,[z401,z1,z2,z4,z5,z27]),(0,[z141,z2,z23,z4,z5,z6])],[(0,[z2,z206,z106,z4,z5,z6]),(0,[z1,z2,z1318,z4,z5,z6]),(0,[z1,z2,z4,z5,z769,z6])],[(0,[z1,z2,z3,z1319,z5,z6]),(0,[z2,z3,z106,z4,z5,z6]),(0,[z60,z2,z3,z4,z65,z6])],[(0,[z1,z2,z3,z1320,z5,z6]),(0,[z1,z2,z3,z1321,z5,z6]),(0,[z471,z2,z3,z117,z33,z6])],[(0,[z1,z2,z23,z1136,z5,z6]),(0,[z1,z2,z23,z4,z5,z9]),(0,[z51,z1,z2,z774,z5,z6])],[(0,[z1,z2,z23,z4,z5,z192]),(0,[z1,z2,z116,z4,z446,z6]),(0,[z2,z408,z1054,z4,z5,z6]),(0,[z135,z1,z2,z3,z4,z5])],[(0,[z171,z2,z39,z4,z5,z6]),(0,[z1,z2,z1322,z4,z5,z6]),(0,[z798,z2,z3,z4,z5,z26])],[(0,[z1,z2,z3,z4,z5,z1323]),(0,[z2,z3,z118,z30,z5,z6]),(0,[z1324,z1,z2,z3,z4,z5]),(0,[z1325,z2,z3,z4,z5,z6])],[(0,[z1,z2,z1326,z4,z5,z6]),(0,[z28,z1,z2,z4,z5,z9]),(0,[z101,z1,z2,z4,z181,z89]),(0,[z102,z1,z2,z4,z5,z272])],[(0,[z1,z2,z1327,z4,z5,z6]),(0,[z1,z29,z8,z4,z5,z9]),(0,[z350,z2,z3,z4,z5,z26]),(0,[z102,z1,z2,z4,z5,z150]),(0,[z1,z2,z1328,z4,z5,z6])],[(0,[z154,z2,z3,z4,z5,z6]),(0,[z38,z2,z39,z4,z5,z9]),(0,[z135,z1,z2,z23,z4,z5]),(0,[z282,z1,z2,z4,z5,z305]),(0,[z1329,z2,z3,z4,z5,z6])],[(0,[z1,z23,z4,z5,z9,z26]),(0,[z34,z2,z3,z4,z5,z9]),(0,[z1,z2,z4,z5,z9,z330])]]]

def SA : ℕ × List W → Bool := fun c => !inB2 8 256 bkA c

def SB : ℕ × List W → Bool := fun c => !inB2 16 512 bkB c

def parents : List (ℕ × List W) := expandN 0 (level0 8 rows)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem gf : allGoalFree 0 (level0 8 rows) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pa0 : chunkB SA 2 ((parents.drop 0).take 1) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem paend : ((parents.drop 1)).isEmpty = true := by
  decide +kernel

theorem windowsA : windowsG (chunkB SA 2) parents 0 [1] = true :=
  windowsG_cons pa0 (windowsG_nil paend)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb0 : chunkB SB 1 ((bkA.flatten.flatten.drop 0).take 512) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb1 : chunkB SB 1 ((bkA.flatten.flatten.drop 512).take 504) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb2 : chunkB SB 1 ((bkA.flatten.flatten.drop 1016).take 406) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pbend : ((bkA.flatten.flatten.drop 1422)).isEmpty = true := by
  decide +kernel

theorem windowsB : windowsG (chunkB SB 1) bkA.flatten.flatten 0 [512, 504, 406] = true :=
  windowsG_cons pb0 (windowsG_cons pb1 (windowsG_cons pb2 (windowsG_nil pbend)))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc0 : chunkOK 5 ((bkB.flatten.drop 0).take 166).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc1 : chunkOK 5 ((bkB.flatten.drop 166).take 156).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc2 : chunkOK 5 ((bkB.flatten.drop 322).take 155).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc3 : chunkOK 5 ((bkB.flatten.drop 477).take 35).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pcend : ((bkB.flatten.drop 512)).isEmpty = true := by
  decide +kernel

theorem windowsC : windowsF 5 bkB.flatten 0 [166, 156, 155, 35] = true :=
  windowsF_cons pc0 (windowsF_cons pc1 (windowsF_cons pc2 (windowsF_cons pc3 (windowsF_nil pcend))))

theorem reject : search 8 rows = false :=
  search_false_C2 (dp := 0) (J := 5) (d := 2) (g1 := 8) (nb1 := 256) (g2 := 16) (nb2 := 512) (by norm_num) gf windowsC windowsB windowsA

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem witness_ok : ∀ x : Fin 6 → Bool, Circuit.eval witness (List.ofFn x) = target x := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sample_ok : ∀ k : Fin 128, target (fun i => (rows.getD i.val 0)[k.val]) = (~~~goal)[k.val] := by
  decide +kernel

theorem solve (s : ℕ) (hs : HasCircuitSize 6 target s) :
    ∃ C : Circuit, Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = target x := by
  obtain ⟨C, fits, size, computes⟩ := hs
  by_cases hasNot : ∃ g ∈ C.gates, g.op = GateOp.not
  · obtain ⟨g, mem, op⟩ := hasNot
    have short : binaryCost C.gates < C.size :=
      (List.length_filter_lt_length_iff_exists (p := isBinary)).mpr
        ⟨g, mem, by simp [isBinary, op]⟩
    have bound := bound_from_search rows rfl (by decide) reject sample_ok C.gates C.output fits computes
    refine ⟨witness, by simp [Monotone2, witness], ?_, witness_ok⟩
    change 10 ≤ s
    omega
  · refine ⟨C, ?_, size, computes⟩
    intro g mem
    obtain ⟨op, cap⟩ := fits g mem
    change g.op = .and ∨ g.op = .or ∨ g.op = .not at op
    exact ⟨op.elim Or.inl (fun h => h.elim Or.inr (fun eq => (hasNot ⟨g, mem, eq⟩).elim)), cap⟩

end PEqualNP.Outside.L_meta_38647

theorem PEqualNP.Outside.L_meta_38647 :
    ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276808362 * 2 ^ 32 + 4007717536) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276808362 * 2 ^ 32 + 4007717536) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  exact PEqualNP.Outside.L_meta_38647.solve