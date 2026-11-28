import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_41042

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
  Nat.testBit (4276808426 * 2 ^ 32 + 4276808360) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

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
  [(0x0010000004001025#64 ++ 0xf7e809ce3c08f1ff#64 : BitVec 128),
   (0x90e03294d0334692#64 ++ 0xefdc76b5d0774e93#64 : BitVec 128),
   (0x4241852961858b18#64 ++ 0xdfbf8739e3878f1c#64 : BitVec 128),
   (0x6482d83e02d80dc0#64 ++ 0xbd7ff83e03f80fe0#64 : BitVec 128),
   (0x87036fc0036ee000#64 ++ 0x7cfbffc003fff000#64 : BitVec 128),
   (0xf803ffffb8000000#64 ++ 0x03fbfffffc000000#64 : BitVec 128)]

def witness : Circuit :=
  ⟨[⟨.and, [1, 2]⟩, ⟨.or, [0, 6]⟩, ⟨.or, [1, 2]⟩, ⟨.and, [3, 4]⟩, ⟨.or, [0, 9]⟩, ⟨.and, [8, 10]⟩, ⟨.or, [3, 4]⟩, ⟨.or, [12, 5]⟩, ⟨.and, [7, 13]⟩, ⟨.or, [14, 11]⟩], 15⟩

def mkw (a b : BitVec 64) : W := a ++ b

def z0 : W := mkw 0x0010000004001025 0xf7e809ce3c08f1ff

def z1 : W := mkw 0x4241852961858b18 0xdfbf8739e3878f1c

def z2 : W := mkw 0x6482d83e02d80dc0 0xbd7ff83e03f80fe0

def z3 : W := mkw 0x87036fc0036ee000 0x7cfbffc003fff000

def z4 : W := mkw 0x90e03294d0334692 0x285476b5d0774e83

def z5 : W := mkw 0xf803ffffb8000000 0x03fbfffffc000000

def z6 : W := mkw 0x9000329490000000 0xe7d876b5d0004093

def z7 : W := mkw 0x90e03294d0334692 0xefdc76b5d0774e93

def z8 : W := mkw 0x0010000004001025 0xf40000000008f1ff

def z9 : W := mkw 0x9000329490000000 0x03d876b5d0000000

def z10 : W := mkw 0x6482d83e02d80dc0 0x3063f80e03f801e0

def z11 : W := mkw 0x0402480002480000 0x3c7bf80003f80000

def z12 : W := mkw 0x6080903e00900dc0 0x8104003e00000fe0

def z13 : W := mkw 0x0000000000000000 0x77e809ce3c08f000

def z14 : W := mkw 0xff03ffffbb6ee000 0x7ffbfffffffff000

def z15 : W := mkw 0x0000000000000000 0xe7c8008410004093

def z16 : W := mkw 0x7800903fb8000000 0x0300003ffc000000

def z17 : W := mkw 0x0201050001048000 0x5cbb870003878000

def z18 : W := mkw 0x85026ac0026a6000 0x204078c000787000

def z19 : W := mkw 0x6402c82a02c80940 0x1023880a03880160

def z20 : W := mkw 0xf4e2fabed2fb4fd2 0xfffffebfd3ff4ff3

def z21 : W := mkw 0x4040802960810b18 0xcf9c0639e0070f1c

def z22 : W := mkw 0x6482d83e02d80dc0 0x8917f03e03f00fe0

def z23 : W := mkw 0x6482d83e02d80dc0 0xfffff8be13f84ff3

def z24 : W := mkw 0x4000802800800900 0x9d3f803803800f00

def z25 : W := mkw 0xb8037fd7b8000000 0x02c07fc7fc000000

def z26 : W := mkw 0x0211050005049025 0xfffb8fce3f8ff1ff

def z27 : W := mkw 0x0240000041858b18 0xdc04000003878f1c

def z28 : W := mkw 0x6803cd6b28000000 0x0023894a2c000000

def z29 : W := mkw 0x4040802960810b18 0x00040031c0000e00

def z30 : W := mkw 0x6492d83e06d81de5 0xfffff9fe3ff8ffff

def z31 : W := mkw 0xff03ffffbb6ee000 0x0bfbfffffff70000

def z32 : W := mkw 0x0010000004001025 0x1020094a2c08b16c

def z33 : W := mkw 0x85036fc0026a6000 0x20fbffc000787000

def z34 : W := mkw 0x980127c1b8000000 0x028007c1fc000000

def z35 : W := mkw 0xb8027ad698000000 0x004078c61c000000

def z36 : W := mkw 0x8080329400324480 0xeddc76b400774e80

def z37 : W := mkw 0x6002d83e00000000 0x017bf83e00000000

def z38 : W := mkw 0x4251852965859b3d 0xffff8fffff8fffff

def z39 : W := mkw 0xfc83ffffbad80dc0 0xbffffffffff80fe0

def z40 : W := mkw 0x87036fc0036ee000 0x0813f60003f70000

def z41 : W := mkw 0x87036fc0036ee000 0x6cdbf68003f74000

def z42 : W := mkw 0x6492d83e06d81de5 0xfd7ff83e03f8ffff

def z43 : W := mkw 0x10a0101490100482 0x0000000410000083

def z44 : W := mkw 0xff43fffffbefeb18 0xffffffffffffff1c

def z45 : W := mkw 0x07034d40034ca000 0x102389400388b000

def z46 : W := mkw 0xff03ffffbb4ca000 0x13fbffffff88b000

def z47 : W := mkw 0xe803efeb28000000 0x00fbffca2c000000

def z48 : W := mkw 0x1000101490000000 0x03000035d0000000

def z49 : W := mkw 0x66c3dd3f63dd8fd8 0xbd7ffe3fc3ff0fe0

def z50 : W := mkw 0xe783fffe03feedc0 0xbd7ffe3e03ff0fe0

def z51 : W := mkw 0xf8e3fffff8334692 0xeffffffffc774e93

def z52 : W := mkw 0x4241852961858b18 0x08178631c3870e00

def z53 : W := mkw 0xfa43fffff9858b18 0xdfffffffff878f1c

def z54 : W := mkw 0x0010000004001025 0x428001c03c00f01f

def z55 : W := mkw 0x0000000000000000 0x03e809ce3c000000

def z56 : W := mkw 0xf803ffffb8000000 0x0013f631c0000000

def z57 : W := mkw 0x4480802802d80dc0 0xbd3f803803f80fe0

def z58 : W := mkw 0x4001852920800900 0x9fbf8739e3800f00

def z59 : W := mkw 0x0000000000000000 0x408001c00000f000

def z60 : W := mkw 0x0000000000000000 0x00e809c000000000

def z61 : W := mkw 0xf4e2fabed2fb4fd2 0xefdff6b5d3f74e93

def z62 : W := mkw 0x87136fc0076ef025 0xfffbffce3ffff1ff

def z63 : W := mkw 0x0201050121048008 0x000001002000800c

def z64 : W := mkw 0xb4e27a96d27b46d2 0xefdc7eb7d07f4ef3

def z65 : W := mkw 0x24825816025804c0 0x20407806007800e0

def z66 : W := mkw 0x98036fc1b8000000 0x02fbffc1fc000000

def z67 : W := mkw 0x80036fc000000000 0x00fbffc000000000

def z68 : W := mkw 0x6082d83e00100480 0xad7ff83e00700e80

def z69 : W := mkw 0x0010000004001025 0x020000003c00001f

def z70 : W := mkw 0x6482d83e02d80dc0 0x0817f03003f00e00

def z71 : W := mkw 0xe783fffe03feedc0 0xfdfffffe03ffffe0

def z72 : W := mkw 0x00e0000040334692 0x0804000000770e00

def z73 : W := mkw 0xd2e1b7bdf1b7cf9a 0xfffff7bdf3f7cf9f

def z74 : W := mkw 0x0010000004001025 0x306009ce3c08f1ef

def z75 : W := mkw 0x0241050161058218 0x00000601c0070000

def z76 : W := mkw 0x87436fc043efeb18 0xfcffffc003ffff1c

def z77 : W := mkw 0x87036fc0036ee000 0x2853fec003ff7000

def z78 : W := mkw 0x4040802960810b18 0x83040039e0000f1c

def z79 : W := mkw 0x90602280d0234212 0x42800681d0074013

def z80 : W := mkw 0x0000000000000000 0xb7e809ce3c0801e0

def z81 : W := mkw 0xfce3fffffafb4fd2 0xffffffffffff4ff3

def z82 : W := mkw 0x9f036fc1bb6ee000 0x7efbffc1fffff000

def z83 : W := mkw 0x0000000000000000 0xb568080e000801e0

def z84 : W := mkw 0x87036fc0036ee000 0x4893f7c003f7f000

def z85 : W := mkw 0x0000000000000000 0x74e809c00008f000

def z86 : W := mkw 0xfa03ffffb9848908 0x13fbffffff80810c

def z87 : W := mkw 0x4001852920000000 0x03bb8739e0000000

def z88 : W := mkw 0xf801b7ffb8000000 0x038007fffc000000

def z89 : W := mkw 0x0480000002d80dc0 0xbc04000003f80fe0

def z90 : W := mkw 0x0000000000000000 0x004008c61c000000

def z91 : W := mkw 0x07000000036ee000 0x7c00000003fff000

def z92 : W := mkw 0xf803ffffb8000000 0x0033ff7bec000000

def z93 : W := mkw 0x4000802800000000 0x013b803800000000

def z94 : W := mkw 0x90a0329490324482 0x23d876b5d0704083

def z95 : W := mkw 0xf7e3fffed3ffefd2 0xffffffffd3fffff3

def z96 : W := mkw 0x4241852961858b18 0x4a978731e3878e1c

def z97 : W := mkw 0x90e03294d0334692 0x8b147635d0770e93

def z98 : W := mkw 0x85126ac0066a7025 0xf7e879ce3c78f1ff

def z99 : W := mkw 0x24825816025804c0 0xad5c783600780ee0

def z100 : W := mkw 0x0010000004001025 0xf44008c61c08f1ff

def z101 : W := mkw 0x0010000004001025 0x74e809ca2c08f16c

def z102 : W := mkw 0x0250000045859b3d 0xfc040000038fffff

def z103 : W := mkw 0x0000000000000000 0x4280008010004013

def z104 : W := mkw 0xc743efe963efeb18 0x7cfffff1c3fffe00

def z105 : W := mkw 0x90e03294d0334692 0xfffc7ebfd07f4ff3

def z106 : W := mkw 0xf803ffffb8800900 0x9fffffffff800f00

def z107 : W := mkw 0x7800903fb8000000 0x00000031c0000000

def z108 : W := mkw 0x4241852961858b18 0x5cbf8731c3878e00

def z109 : W := mkw 0x0412480006481025 0xfffbf9ce3ff8f1ff

def z110 : W := mkw 0xf803ffffb8224000 0x6ffbfffffc774000

def z111 : W := mkw 0x85026ac0026a6000 0x74e879c00078f000

def z112 : W := mkw 0x87036fc0036ee000 0xfdfbffce03fff1e0

def z113 : W := mkw 0x0010000004001025 0x8300000e3c0001ff

def z114 : W := mkw 0x830127c00126e000 0x408007c00007f000

def z115 : W := mkw 0x6482d83e02d80dc0 0x097ff83e03f00e00

def z116 : W := mkw 0x0000000000000000 0xd7a801082000811c

def z117 : W := mkw 0x87036fc0036ee000 0xfffbffc413fff093

def z118 : W := mkw 0xf6e3ffbff3ffcfda 0xffffffbff3ffcfff

def z119 : W := mkw 0xb8027ad698000000 0x03d87ef7dc000000

def z120 : W := mkw 0x0241050161058218 0x42800701e007801c

def z121 : W := mkw 0x4000802800800900 0xbd7f883e03880fe0

def z122 : W := mkw 0x80e0228040334692 0xecdc768000774e93

def z123 : W := mkw 0x0200000001048000 0x5c00000003878000

def z124 : W := mkw 0x030105400104a000 0x000001400000b000

def z125 : W := mkw 0xf803ffffb8000000 0x77fbfffffc08f000

def z126 : W := mkw 0x9020228090224002 0x0000008010004003

def z127 : W := mkw 0x7800903fb8000000 0x03e809fffc000000

def z128 : W := mkw 0x0080101400100480 0xbd7c783e00780fe0

def z129 : W := mkw 0x9000329490000000 0x03f87ffffc000000

def z130 : W := mkw 0x0000000000000000 0xf7e8090e200881fc

def z131 : W := mkw 0x8040228040234210 0xefdc76b1c0774e10

def z132 : W := mkw 0xf803ffffb8000000 0x0293f7f1fc000000

def z133 : W := mkw 0xf813ffffbc001025 0xf7fbfffffc08f1ff

def z134 : W := mkw 0x4000802920000000 0x03000039e0000000

def z135 : W := mkw 0x4011852924001025 0xf7fb8ffffc08f1ff

def z136 : W := mkw 0x6783dd7e03dcadc0 0xbd7ff97e03f8bfe0

def z137 : W := mkw 0x66c2d83e43dd8fd8 0xfd7ff83e03ff8ffc

def z138 : W := mkw 0x0080101400100480 0xad5c703400700e80

def z139 : W := mkw 0xf482fabe92d80dc0 0xbffffebfd3f80fe0

def z140 : W := mkw 0x87002280036ee000 0x7cd8768003fff000

def z141 : W := mkw 0x0010000004001025 0x204008c61c0870e3

def z142 : W := mkw 0x90e03294d0334692 0x4a9476b1d0774e13

def z143 : W := mkw 0xc743efe963efeb18 0x0817f631c3f70e00

def z144 : W := mkw 0xff03ffffbb6ee000 0x0813f631c3f70000

def z145 : W := mkw 0x830127c00126e000 0x0000060000070000

def z146 : W := mkw 0x0000000000000000 0x0020094a2c000000

def z147 : W := mkw 0x7c82d83fbad80dc0 0xbf7ff83ffff80fe0

def z148 : W := mkw 0x90e03294d0334692 0x08147631c0770e00

def z149 : W := mkw 0x0010000004001025 0xd7a8010e3c0081ff

def z150 : W := mkw 0x7802d83fb8000000 0x037bf83ffc000000

def z151 : W := mkw 0x0010000004001025 0xf420094a2c08f1ff

def z152 : W := mkw 0xe582fafe02fa6dc0 0xbd7ff8fe03f87fe0

def z153 : W := mkw 0x2802484208000000 0x000008420c000000

def z154 : W := mkw 0x07034d40034ca000 0x5cbb8f40038fb000

def z155 : W := mkw 0x0050000044011235 0xfffc0ffffc0fffff

def z156 : W := mkw 0x0080101400100480 0x8104003400000e80

def z157 : W := mkw 0x4240802841858b18 0xdd3f803803878f1c

def z158 : W := mkw 0xfa53fffffd859b3d 0xffffffffff8fffff

def z159 : W := mkw 0x6482d83e02d80dc0 0xfdfff9fe03f8ffe0

def z160 : W := mkw 0x90a0329490324482 0x2040708410704083

def z161 : W := mkw 0x42e1852961b7cf9a 0xffbf8739e3f7cf9f

def z162 : W := mkw 0x66c3dd3f63dd8fd8 0xffffff3fe3ff8ffc

def z163 : W := mkw 0x90b03294943254a7 0xf7e879ce3c78f1ff

def z164 : W := mkw 0xf803ffffb8000000 0x00fbfff1c0000000

def z165 : W := mkw 0x90f03294d43356b7 0xfffc7ffffc7fffff

def z166 : W := mkw 0x6482d83e02d80dc0 0xbffff9fe3ff80fe0

def z167 : W := mkw 0x90e03294d0334692 0xeffc7ffffc774e93

def z168 : W := mkw 0x10e01014d0110692 0xaf5c7035d0700e93

def z169 : W := mkw 0x00e0000040334692 0xef9c0631c0774e93

def z170 : W := mkw 0x6090903e04901de5 0xf7ec09fe3c08ffff

def z171 : W := mkw 0x7a41953ff9858b18 0xdfbf873fff878f1c

def z172 : W := mkw 0x0000000000000000 0x20400806000800e0

def z173 : W := mkw 0xff83ffffbbfeedc0 0xffffffffffffffe0

def z174 : W := mkw 0x00e0000040334692 0xec04000000774e93

def z175 : W := mkw 0x18000001b8000000 0x02000001fc000000

def z176 : W := mkw 0xbd027ad69a6a6000 0x204078c61c787000

def z177 : W := mkw 0x4041852960010210 0xcfbf8739e0070e10

def z178 : W := mkw 0x90602280d0234212 0x00000601c0070000

def z179 : W := mkw 0x0010000004001025 0x0000000a2c00016c

def z180 : W := mkw 0x4040802960810b18 0x9f3f8039e3800f1c

def z181 : W := mkw 0x0010000004001025 0x80000000000001ff

def z182 : W := mkw 0x24825816025804c0 0x0000700000700000

def z183 : W := mkw 0xe7c3ffff63ffefd8 0xffffffffe3fffffc

def z184 : W := mkw 0x981127c1bc001025 0xf7e80fcffc08f1ff

def z185 : W := mkw 0x0000000000000000 0x102001082000810c

def z186 : W := mkw 0x0000000000000000 0x3468080000080000

def z187 : W := mkw 0x07034d40034ca000 0x0003800003800000

def z188 : W := mkw 0x87136fc0076ef025 0x7cfbffca2ffff16c

def z189 : W := mkw 0x07034d40034ca000 0x3c7bf94003f8b000

def z190 : W := mkw 0x4241852961858b18 0xffff8f3fe38f8ffc

def z191 : W := mkw 0x87136fc0076ef025 0x7efbffc03ffff01f

def z192 : W := mkw 0x0402480002480000 0xbd7bf80e03f801e0

def z193 : W := mkw 0xbf037fd69b6ee000 0x7cfbffc61ffff000

def z194 : W := mkw 0x83036fc00126e000 0x40fbffc00007f000

def z195 : W := mkw 0x07024800036ee000 0x7c7bf80003fff000

def z196 : W := mkw 0xf803ffffb8000000 0xd7fbfffffc00811c

def z197 : W := mkw 0x10e01014d0110692 0x00040031c0000e00

def z198 : W := mkw 0x4241852961858b18 0xffff87bdf387cf9f

def z199 : W := mkw 0x7801953fb8000000 0x03bb873ffc000000

def z200 : W := mkw 0x90702280d4235237 0xf7e80fcffc0ff1ff

def z201 : W := mkw 0x4201852921848908 0x102381082380810c

def z202 : W := mkw 0x4241852961858b18 0xffff8ff9e38fff1c

def z203 : W := mkw 0x4000802800800900 0x1023800803800100

def z204 : W := mkw 0x4240802961858b18 0xdf040039e3878f1c

def z205 : W := mkw 0xc753efe967effb3d 0xffffffffffffffff

def z206 : W := mkw 0x4040802960810b18 0xd7ac0139e0008f1c

def z207 : W := mkw 0x6080903e00900dc0 0x9d3f803e03800fe0

def z208 : W := mkw 0x6803cd6b28000000 0x03bb8f7bec000000

def z209 : W := mkw 0x0000000000000000 0xf7e809c41008f093

def z210 : W := mkw 0x6402d83e02480000 0x3d7bf83e03f80000

def z211 : W := mkw 0x0482480002d80dc0 0xbc7ff80003f80fe0

def z212 : W := mkw 0x0801054128000000 0x000001402c000000

def z213 : W := mkw 0xf802faffb8000000 0x034078fffc000000

def z214 : W := mkw 0x90e03294d0334692 0xc38406b5d0074e93

def z215 : W := mkw 0x07034d40034ca000 0x74eb89c00388f000

def z216 : W := mkw 0x90e03294d0334692 0x62c07685d0774093

def z217 : W := mkw 0xfd03ffffba6a6000 0x23fbfffffc787000

def z218 : W := mkw 0x8000228000224000 0x6cd8768000774000

def z219 : W := mkw 0x4201852921848908 0x13bb8739e380810c

def z220 : W := mkw 0x6482d83e02d80dc0 0x2857f83603f80ee0

def z221 : W := mkw 0x0482581402580480 0xbd7ff83403f80e80

def z222 : W := mkw 0x4241852961858b18 0x18378739e3878f0c

def z223 : W := mkw 0xf0e2fabed0334692 0xeffffebfd0774e93

def z224 : W := mkw 0x98e137d5f8334692 0xefdc77f5fc774e93

def z225 : W := mkw 0x97e37fd4d37fe692 0xfffffff5d3fffe93

def z226 : W := mkw 0xd801a7e9b8000000 0x03bb87f9fc000000

def z227 : W := mkw 0x6000802a00800940 0x0000000a00000160

def z228 : W := mkw 0x831127c00526f025 0xf7e80fce3c0ff1ff

def z229 : W := mkw 0x4241852961858b18 0x52a38709e387811c

def z230 : W := mkw 0x980022c098000000 0x000000c01c000000

def z231 : W := mkw 0x90e03294d0334692 0xfffc7ff5d07ffe93

def z232 : W := mkw 0x90e03294d0334692 0xa34470b5d0704e93

def z233 : W := mkw 0x78e0903ff8110692 0x8304003ffc000e93

def z234 : W := mkw 0x6482d83e02d80dc0 0x9d3ff03803f00f00

def z235 : W := mkw 0x6482d83e02d80dc0 0xbc17f03003f80fe0

def z236 : W := mkw 0x6003dd3f20000000 0x03fbff3fe0000000

def z237 : W := mkw 0x830127c00126e000 0x74e80fc0000ff000

def z238 : W := mkw 0x87136fc0076ef025 0xfcfbffc003fff1ff

def z239 : W := mkw 0x6683dd3f23dc8dc8 0xbd7ff93e23f88fec

def z240 : W := mkw 0x84036fc002480000 0x3cfbffc003f80000

def z241 : W := mkw 0x0000000000000000 0x03c8008410000000

def z242 : W := mkw 0x7880903fb8900dc0 0x8304003ffc000fe0

def z243 : W := mkw 0x90603294d0234212 0x43d876b5d0074013

def z244 : W := mkw 0x90e03294d0334692 0xec147631c0774e93

def z245 : W := mkw 0x00901014041014a5 0xfffc79fe3c78ffff

def z246 : W := mkw 0x90e37fd4d0334692 0xeffffff5d0774e93

def z247 : W := mkw 0xffe3fffffb7fe692 0xfffffffffffffe93

def z248 : W := mkw 0x0000000000000000 0x1c3b800003800000

def z249 : W := mkw 0x85026ac0026a6000 0x6cd87ec0007f7000

def z250 : W := mkw 0x0000000000000000 0xd7e809ce3c00811c

def z251 : W := mkw 0xf803efebb8000000 0x02a38fcbfc000000

def z252 : W := mkw 0x6080903e00900dc0 0xad5c703e00700fe0

def z253 : W := mkw 0xe483fffe02d80dc0 0xbdfffffe03f80fe0

def z254 : W := mkw 0x0010000004001025 0x000000c01c007003

def z255 : W := mkw 0x64c2d83e42d90fd0 0xfffffe3fc3ff0ff0

def z256 : W := mkw 0x4201852801848900 0xddbf873803878f00

def z257 : W := mkw 0x421185292584992d 0xf7eb89ce3f88f1ff

def z258 : W := mkw 0x0000000000000000 0x0000000000000000

def z259 : W := mkw 0x6c83dd7f2ad80dc0 0xbd7ff97e2ff80fe0

def z260 : W := mkw 0xef03efeb2b6ee000 0x7cfbffca2ffff000

def z261 : W := mkw 0x4251852965859b3d 0xdfbf87f9ff87ff1f

def z262 : W := mkw 0xe783fffe03feedc0 0x7cfffff003fffe00

def z263 : W := mkw 0x0040000040010210 0xcf9c0631c0070e10

def z264 : W := mkw 0x421185292584992d 0x1023894a2f88b16c

def z265 : W := mkw 0x00e0000040334692 0xefcc008410774e93

def z266 : W := mkw 0x0040000160010218 0x02000001e000001c

def z267 : W := mkw 0x0010000004001025 0xf4e809c00008f1ff

def z268 : W := mkw 0x6412c82a06c81965 0x1023894a2f88b16c

def z269 : W := mkw 0xf4a2fabe92fa4dc2 0xbd7ff8be13f84fe3

def z270 : W := mkw 0xd241b7bdf1858b18 0xdffff7bdf3878f1c

def z271 : W := mkw 0x87036fc0036ee000 0xfffbffc823fff11c

def z272 : W := mkw 0x87036fc0036ee000 0x7c13f60003fff000

def z273 : W := mkw 0x9a4127c1f9058218 0x428007c1fc07801c

def z274 : W := mkw 0x0250000045859b3d 0xffec09ce3f8fffff

def z275 : W := mkw 0x8000228000224000 0x4080068000074000

def z276 : W := mkw 0x0010000004001025 0xb568094e2c08b1ec

def z277 : W := mkw 0x87e36fc0437fe692 0xfcffffc003fffe93

def z278 : W := mkw 0x0480000002d80dc0 0x0804000003f00e00

def z279 : W := mkw 0x0000000000000000 0x8300000410000093

def z280 : W := mkw 0xc743efe963efeb18 0xfffffff9e3ffff1c

def z281 : W := mkw 0x87036fc0036ee000 0x50a38fc0038ff000

def z282 : W := mkw 0x7803dd7fb8000000 0x0323897ffc000000

def z283 : W := mkw 0xfc83ffffba5804c0 0x23fbfffffc7800e0

def z284 : W := mkw 0x0000000000000000 0x2c58700000700000

def z285 : W := mkw 0xfc93ffffbed81de5 0xfffffffffff8ffff

def z286 : W := mkw 0x0502484002482000 0x0000084000083000

def z287 : W := mkw 0xd001b7bdb0000000 0x03fbf7bdf0000000

def z288 : W := mkw 0xe783fffe03feedc0 0x0817f63003f70e00

def z289 : W := mkw 0x0000000000000000 0xc788000000000010

def z290 : W := mkw 0xf813ffffbc001025 0x23fbfffffc0870e3

def z291 : W := mkw 0xf4f2fabed6fb5ff7 0xffffffffffffffff

def z292 : W := mkw 0xf803ffffb8000000 0x0313f63ffc000000

def z293 : W := mkw 0xe482fabe02fa4dc0 0xfdfffebe03ff4fe0

def z294 : W := mkw 0xf803ffffb8000000 0x03bbf739e0000000

def z295 : W := mkw 0x820127800126c000 0x7cfbf78003f7c000

def z296 : W := mkw 0x3800101698000000 0x000000061c000000

def z297 : W := mkw 0x85126ac0066a7025 0x204078c61c7870e3

def z298 : W := mkw 0x0000000000000000 0x0300000e3c000000

def z299 : W := mkw 0x6482d83e025804c0 0x217bf83e007800e0

def z300 : W := mkw 0x9000329490224000 0x6fd876b5d0774000

def z301 : W := mkw 0x6482d83e02d80dc0 0xfffff93e23f88ffc

def z302 : W := mkw 0x6080903e00900dc0 0x0004003000000e00

def z303 : W := mkw 0xf8e3fffff8334692 0xefdff6b5d0774e93

def z304 : W := mkw 0x0010000004001025 0xf700000e3c08f1ff

def z305 : W := mkw 0x0241050041858b18 0xdcbf870003878f1c

def z306 : W := mkw 0xb8a27ad698324482 0x204078c61c704083

def z307 : W := mkw 0x90f03294d43356b7 0xefdc7ef7dc7f7ef3

def z308 : W := mkw 0x80036fc000000000 0x03fbffce3c000000

def z309 : W := mkw 0x07000000034ca000 0x100000000388b000

def z310 : W := mkw 0x10e01014d0110692 0xcf9c0635d0070e93

def z311 : W := mkw 0x0040000040010210 0xcc04000000070e10

def z312 : W := mkw 0x4241852961058218 0x43bb8739e007801c

def z313 : W := mkw 0xfc83ffffbad80dc0 0x0bfffffffff00e00

def z314 : W := mkw 0x6002d83e00800900 0x9d7ff83e03800f00

def z315 : W := mkw 0x0241050161058218 0x5ebb8701e387801c

def z316 : W := mkw 0x42c1953d61958f98 0xfffff73de3f78f9c

def z317 : W := mkw 0x4080903c00900d80 0xbd7ff03c03f00f80

def z318 : W := mkw 0x52e1953df1958f9a 0xdfbf873df3878f9f

def z319 : W := mkw 0x4050802964811b3d 0x8304003ffc000fff

def z320 : W := mkw 0xfc03ffffba480000 0x3ffbfffffff80000

def z321 : W := mkw 0x0241050161058218 0xcf9c0731e0078e1c

def z322 : W := mkw 0x0400000002c80940 0x1000000003880160

def z323 : W := mkw 0x0400000002480000 0x3c00000003f80000

def z324 : W := mkw 0x90e03294d0334692 0xfffc77bdf077cf9f

def z325 : W := mkw 0x0010000004001025 0x20000000000870e3

def z326 : W := mkw 0x66c3dd3f63dd8fd8 0xdfbff739e3f78f1c

def z327 : W := mkw 0xf8e3fffff8334692 0x0bfffffffc770e00

def z328 : W := mkw 0xf8a3ffffb8324482 0x23fbfffffc704083

def z329 : W := mkw 0xf863fffff8234212 0x43fbfffffc074013

def z330 : W := mkw 0x0000000000800900 0x9c04000003800f00

def z331 : W := mkw 0x90a0329490324482 0x0000700000700000

def z332 : W := mkw 0x4001852920000000 0x03fb8ffffc000000

def z333 : W := mkw 0x00034d4000000000 0x0023894000000000

def z334 : W := mkw 0x986127c1f8234212 0x428007c1fc074013

def z335 : W := mkw 0x90e03294d0110692 0x83dc76b5d0000e93

def z336 : W := mkw 0x6703cd6a03cca940 0x1023894a0388b160

def z337 : W := mkw 0x97636fc0d36fe212 0x7efbffc1d3fff013

def z338 : W := mkw 0x0201050001048000 0x4080070000078000

def z339 : W := mkw 0x6800802b28000000 0x0000000a2c000000

def z340 : W := mkw 0x0200000001848908 0x100000000380810c

def z341 : W := mkw 0x10e01014d0110692 0x83040035d0000e93

def z342 : W := mkw 0x9010329494001025 0xf7f87ffffc08f1ff

def z343 : W := mkw 0x6483dd3f22d80dc0 0xbfffff3fe3f80fe0

def z344 : W := mkw 0xfc03ffffbac80940 0x13fbffffff880160

def z345 : W := mkw 0x95a27ad4927a6482 0x204078c410787083

def z346 : W := mkw 0x0000000000000000 0x028001c03c000000

def z347 : W := mkw 0xe793fffe07fefde5 0xfffffffe3fffffff

def z348 : W := mkw 0x82036fc001048000 0x5cfbffc003878000

def z349 : W := mkw 0x6412c82a06c81965 0xf7eb89ce3f88f1ff

def z350 : W := mkw 0x87036fc0036ee000 0x5cbbf70003f78000

def z351 : W := mkw 0x87036fc0036ee000 0x7ffbffce3ffff000

def z352 : W := mkw 0x0002480000000000 0x007bf80000000000

def z353 : W := mkw 0x980127c1b8000000 0x00000601c0000000

def z354 : W := mkw 0xf813ffffbc001025 0x83fbfffffc0001ff

def z355 : W := mkw 0x4241852961858b18 0xdfff8fffff878f1c

def z356 : W := mkw 0xf803ffffb8000000 0xb7fbfffffc0801e0

def z357 : W := mkw 0x025105016505923d 0xf7e80fcffc0ff1ff

def z358 : W := mkw 0x50e0903df0910f9a 0x8304003df0000f9f

def z359 : W := mkw 0x0010000004001025 0xf68001c03c08f1ff

def z360 : W := mkw 0x10e01014d0110692 0xe7cc00b5d0004e93

def z361 : W := mkw 0x7810903fbc001025 0x8300003ffc0001ff

def z362 : W := mkw 0x80036fc000000000 0x0013f60000000000

def z363 : W := mkw 0x4402c82802c80900 0xbd7ff83803f80f00

def z364 : W := mkw 0x90037fd490000000 0x03fbfff5d0000000

def z365 : W := mkw 0x8000228000224000 0x0810760000770000

def z366 : W := mkw 0x00f00000443356b7 0xfc040000007fffff

def z367 : W := mkw 0x87036fc0036ee000 0x1833ff4003ffb000

def z368 : W := mkw 0x0010000004001025 0xe7c808c61c0870f3

def z369 : W := mkw 0x0010000004001025 0xc38001ce3c00f1ff

def z370 : W := mkw 0xf883ffffb8900dc0 0x83fffffffc000fe0

def z371 : W := mkw 0x9b0127c1b926e000 0x428007c1fc07f000

def z372 : W := mkw 0x0010000004001025 0x83e809ce3c0001ff

def z373 : W := mkw 0xff13ffffbf6ef025 0xfffbfffffffff1ff

def z374 : W := mkw 0x4703cd6923cca908 0x102389482388b10c

def z375 : W := mkw 0x97a37fd4937ee482 0x7cfbffc413fff083

def z376 : W := mkw 0xc241a7a961a7cb18 0xfffff7b9e3f7cf1c

def z377 : W := mkw 0xb8127ad69c001025 0x204078c61c0870e3

def z378 : W := mkw 0x6080903e00900dc0 0xb56c083e00080fe0

def z379 : W := mkw 0x0010000004001025 0xd7a801c83c00f11f

def z380 : W := mkw 0x0000000000224000 0x6c00000000774000

def z381 : W := mkw 0x4241852961858b18 0x8b178639e3870f1c

def z382 : W := mkw 0x0000000000000000 0x102009400008b000

def z383 : W := mkw 0x4000802800800900 0x8104003800000f00

def z384 : W := mkw 0x4041852960810b18 0x83bf8739e0000f1c

def z385 : W := mkw 0x6000903e00000000 0x0100003e00000000

def z386 : W := mkw 0xfa43fffff9858b18 0xdfbff739e3878f1c

def z387 : W := mkw 0xc703efe803eee900 0xfdfffff803ffff00

def z388 : W := mkw 0x0000000000000000 0x4c98060000070000

def z389 : W := mkw 0x9080329490100480 0xafdc76b5d0700e80

def z390 : W := mkw 0x6480903e02d80dc0 0xbd04003e03f80fe0

def z391 : W := mkw 0x80036fc000224000 0x6cfbffc000774000

def z392 : W := mkw 0x00e0000040110692 0x8004000000000e93

def z393 : W := mkw 0x06034d00034c8000 0x7cfbff0003ff8000

def z394 : W := mkw 0xfec3fffffbdd8fd8 0xffffffffffff8ffc

def z395 : W := mkw 0x6a03cd6b29848908 0x1023894a2f80810c

def z396 : W := mkw 0xfb03ffffb926e000 0x43fbfffffc07f000

def z397 : W := mkw 0xf002fabe90000000 0x03fbfebfd0000000

def z398 : W := mkw 0x66d3dd3f67dd9ffd 0xffffffffffffffff

def z399 : W := mkw 0x4241852961858b18 0xc3840739e0078f1c

def z400 : W := mkw 0x0241050161858b18 0xde840701e3878f1c

def z401 : W := mkw 0x0000000000000000 0x204008c000087000

def z402 : W := mkw 0x810022c000226000 0x000000c000007000

def z403 : W := mkw 0x4251852965859b3d 0xffbf8739e38fffff

def z404 : W := mkw 0x0000000000000000 0x03980631c0000000

def z405 : W := mkw 0x0001050120000000 0x02800701e0000000

def z406 : W := mkw 0x0010000004001025 0xf7c800841008f1ff

def z407 : W := mkw 0xc743efe963efeb18 0xdfbff739e3f78f1c

def z408 : W := mkw 0x0010000004001025 0x100000000008b16c

def z409 : W := mkw 0x6f03cd6b2b4ca000 0x1023894a2f88b000

def z410 : W := mkw 0x74e2d83ed2d90fd2 0xbf7ff83fd3f80ff3

def z411 : W := mkw 0x6082d83e00900dc0 0x817ff83e00000fe0

def z412 : W := mkw 0x90602280d0234212 0xe7c80685d0074093

def z413 : W := mkw 0x6603cd2b23cc8948 0x1023890a2388816c

def z414 : W := mkw 0x4040802840810b10 0xdfbf8639c3870f10

def z415 : W := mkw 0x0480101402d80dc0 0xbd5c703403f80fe0

def z416 : W := mkw 0x6402c82a02c80940 0x9d3f883a03880f60

def z417 : W := mkw 0x46c1852963dd8fd8 0xffbf8739e3ff8ffc

def z418 : W := mkw 0x10f01014d41116b7 0x8304003ffc000fff

def z419 : W := mkw 0x0240000041058218 0x400000000007801c

def z420 : W := mkw 0x0080000000900dc0 0x8004000000000fe0

def z421 : W := mkw 0x800127c000000000 0x008007c000000000

def z422 : W := mkw 0xf803ffffb8000000 0xe7fbfffffc004093

def z423 : W := mkw 0x0080000000100480 0xac04000000700e80

def z424 : W := mkw 0x0201050001048000 0xdfbb87082387811c

def z425 : W := mkw 0x80136fc004001025 0xf7fbffce3c08f1ff

def z426 : W := mkw 0x24925816065814e5 0xf7e879ce3c78f1ff

def z427 : W := mkw 0xb8e27ad6d8334692 0xefdc7ef7dc774e93

def z428 : W := mkw 0xb4a27a96927a44c2 0x20407886107840e3

def z429 : W := mkw 0x8010228004225025 0xfff87fce3c7ff1ff

def z430 : W := mkw 0x6492d83e06d81de5 0xbd7ff8fe1ff87fe3

def z431 : W := mkw 0x0201050001048000 0x1023810003808000

def z432 : W := mkw 0x6c03cd6b2ac80940 0x1023894a2f880160

def z433 : W := mkw 0x07134d40074cb025 0xf7eb89ce3f88f1ff

def z434 : W := mkw 0x7810903fbc001025 0xf7e809fffc08f1ff

def z435 : W := mkw 0x0000000000000000 0x03a8010820000000

def z436 : W := mkw 0x80036fc000000000 0x74fbffc00008f000

def z437 : W := mkw 0x07000000036ee000 0x0800000003f70000

def z438 : W := mkw 0x8000228000224000 0x7cf87fc0007ff000

def z439 : W := mkw 0xd2e1b7bdf1b7cf9a 0x0817f631c3f70e00

def z440 : W := mkw 0x0010000004001025 0xf7a801082008f1ff

def z441 : W := mkw 0x97e37fd4d37fe692 0x0817f631c3f70e00

def z442 : W := mkw 0x07134d40074cb025 0x1023894a2f88b16c

def z443 : W := mkw 0x90b03294943254a7 0x204078c61c7870e3

def z444 : W := mkw 0x90f03294d43356b7 0xffdc76b5d07fffff

def z445 : W := mkw 0x6012d83e04001025 0xf7fbf9fe3c08f1ff

def z446 : W := mkw 0xf800b2bfb8000000 0x03d876bffc000000

def z447 : W := mkw 0x97e03294d37fe692 0xffdc76b5d3fffe93

def z448 : W := mkw 0xc243efe961858b18 0xdffffff9e3878f1c

def z449 : W := mkw 0x6803dd7f28000000 0x017bf97e2c000000

def z450 : W := mkw 0x94e03294d2fb4fd2 0xffdc76b5d3ff4ff3

def z451 : W := mkw 0x4000802800800900 0x0817803003800e00

def z452 : W := mkw 0x0080101400100480 0xefdc70b410704e93

def z453 : W := mkw 0x6402c82a02c80940 0x0003800003800000

def z454 : W := mkw 0x0000000000000000 0xf5e809ce0008f1e0

def z455 : W := mkw 0xf803ffffb8000000 0x0053fef7dc000000

def z456 : W := mkw 0x980127c1b8000000 0x03e80fcffc000000

def z457 : W := mkw 0x07000000036ee000 0x7ce809c003fff000

def z458 : W := mkw 0x0010000004001025 0xb768080e3c0801ff

def z459 : W := mkw 0x0080101400100480 0x0814703000700e00

def z460 : W := mkw 0x6482d83e02d80dc0 0x1837f83a03f80f60

def z461 : W := mkw 0xc003efe920000000 0x03fbfff9e0000000

def z462 : W := mkw 0x87036fc0036ee000 0x3063f9c003f8f000

def z463 : W := mkw 0xda41a7e9f9858b18 0xdfbf87f9ff878f1c

def z464 : W := mkw 0x64e2d83e42fb4fd2 0xfd7ff83e03ff4ff3

def z465 : W := mkw 0x6482c82a02d80dc0 0xbc27880a03f80fe0

def z466 : W := mkw 0xfa03ffffb9048000 0x5ffbffffff878000

def z467 : W := mkw 0x64c2d83f62d90fd8 0xbf7ff83fe3f80ffc

def z468 : W := mkw 0x95e27ad4d27b6692 0xefdc7ef5d07f7e93

def z469 : W := mkw 0xd2e1b7bdf1b7cf9a 0xefdff6b5d3f74e93

def z470 : W := mkw 0x97e37fd4d37fe692 0xefdff6b5d3f74e93

def z471 : W := mkw 0xfc83ffffbad80dc0 0x0817f631c3f00e00

def z472 : W := mkw 0x0201050001048000 0x0813860003870000

def z473 : W := mkw 0x24925816065814e5 0x204078c61c7870e3

def z474 : W := mkw 0x87436fc1636fe218 0x7efbffc1e3fff01c

def z475 : W := mkw 0x0010000004001025 0x400000000000f01f

def z476 : W := mkw 0x6482d83e02d80dc0 0xad5ff03403f00e80

def z477 : W := mkw 0x0000000000000000 0xf7e8088e100841f3

def z478 : W := mkw 0x0060000040234212 0x4000000000074013

def z479 : W := mkw 0x6090903e04901de5 0x8304003e3c000fff

def z480 : W := mkw 0x9000329490000000 0x00107631c0000000

def z481 : W := mkw 0xf813ffffbc001025 0x43fbfffffc00f01f

def z482 : W := mkw 0x4001852920000000 0xd7bb8739e000811c

def z483 : W := mkw 0xa5827ad6027a64c0 0x204078c6007870e0

def z484 : W := mkw 0x66c3dd3f63dd8fd8 0x0817f631c3f70e00

def z485 : W := mkw 0x0010000004001025 0x52a009ca3c08f17f

def z486 : W := mkw 0x0201050001048000 0x7cfb8fc0038ff000

def z487 : W := mkw 0xd2f1b7bdf5b7dfbf 0xffffffffffffffff

def z488 : W := mkw 0x4241852961858b18 0x9d3f8639c3870f00

def z489 : W := mkw 0x97f37fd4d77ff6b7 0xffffffffffffffff

def z490 : W := mkw 0x0040000040010210 0x42800601c0070010

def z491 : W := mkw 0x4050802964811b3d 0xf7ec09fffc08ffff

def z492 : W := mkw 0x980137d5b8000000 0x03d877f5fc000000

def z493 : W := mkw 0x6002d83e00000000 0x03fbf9fe3c000000

def z494 : W := mkw 0x0040000040810b18 0x8004000000000f1c

def z495 : W := mkw 0x24825816025804c0 0xb568780e007801e0

def z496 : W := mkw 0x90403294d0010210 0xcfdc76b5d0070e10

def z497 : W := mkw 0x4241852961858b18 0x93278139e3808f1c

def z498 : W := mkw 0x4000802920800908 0x000000082000010c

def z499 : W := mkw 0x4201852921048000 0x5fbb8739e3878000

def z500 : W := mkw 0x4741852963efeb18 0xffbf8739e3ffff1c

def z501 : W := mkw 0x87436fc0436fe210 0xfffffff1c3fffe10

def z502 : W := mkw 0x00f00000443356b7 0xffec09ce3c7fffff

def z503 : W := mkw 0x0000000000000000 0xb4000000000801e0

def z504 : W := mkw 0x0402480002480000 0x2040780000780000

def z505 : W := mkw 0x0010000004001025 0x43e809ce3c00f01f

def z506 : W := mkw 0xf8e0b2bff8334692 0xefdc76bffc774e93

def z507 : W := mkw 0x0010000004001025 0x23e809ce3c0870e3

def z508 : W := mkw 0xfa43fffff9858b18 0x0bffffffff870e00

def z509 : W := mkw 0x0402480002480000 0x0813f00003f00000

def z510 : W := mkw 0xd261a7a9f1a7cb1a 0xdfbf87b9f387cf1f

def z511 : W := mkw 0x07034d40036ee000 0x7c23894003fff000

def z512 : W := mkw 0xa7837fd6037ee4c0 0x7cfbffc603fff0e0

def z513 : W := mkw 0x90a0329490324482 0x6cd8768410774083

def z514 : W := mkw 0x0780000003feedc0 0xfc04000003ffffe0

def z515 : W := mkw 0x0000000000000000 0x54a8010000008000

def z516 : W := mkw 0x87136fc0076ef025 0x7cfbffc61ffff0e3

def z517 : W := mkw 0x0000000000000000 0x8100000e000001e0

def z518 : W := mkw 0x04800000025804c0 0x20000000007800e0

def z519 : W := mkw 0xf803ffffb8000000 0x0063f9ce3c000000

def z520 : W := mkw 0xc703efe923eee908 0x7cfbffc823fff10c

def z521 : W := mkw 0x0000000000000000 0xf7e809c82008f11c

def z522 : W := mkw 0x030000000126e000 0x400000000007f000

def z523 : W := mkw 0x90702280d4235237 0x428007c1fc07f01f

def z524 : W := mkw 0x834127c16127e218 0x428007c1e007f01c

def z525 : W := mkw 0x62c1953f61958fd8 0xdfbf873fe3878ffc

def z526 : W := mkw 0x0000000000000000 0x9528000800000100

def z527 : W := mkw 0x0000000000000000 0x2040008410004083

def z528 : W := mkw 0x0490000006d81de5 0xfc04000003f8ffff

def z529 : W := mkw 0x6402c82a02c80940 0xb56b880e038801e0

def z530 : W := mkw 0x0010000004001025 0x000008420c083060

def z531 : W := mkw 0x4001852920000000 0x00138631c0000000

def z532 : W := mkw 0x07100000076ef025 0xfc00000003fff1ff

def z533 : W := mkw 0x90a0329490324482 0xad5c70b410704e83

def z534 : W := mkw 0x6a43cd6b69858b18 0xdfbf8f7bef878f1c

def z535 : W := mkw 0x0402480002480000 0x7cfbf9c003f8f000

def z536 : W := mkw 0x90e03294d0334692 0x0bdc76b5d0770e00

def z537 : W := mkw 0x05000000026a6000 0x2000000000787000

def z538 : W := mkw 0x0010000004001025 0xe7c801c43c00f09f

def z539 : W := mkw 0x870127c0036ee000 0x7c8007c003fff000

def z540 : W := mkw 0x4241852961858b18 0x0bbf8739e3870e00

def z541 : W := mkw 0x4201852921848908 0x5cbb87082387810c

def z542 : W := mkw 0x0040000040010210 0xefdc06b5d0074e93

def z543 : W := mkw 0xf803ffffb8000000 0x03dbf6b5d0000000

def z544 : W := mkw 0x6482d83e02d80dc0 0x9127883e03880fe0

def z545 : W := mkw 0x0240000041858b18 0xdf9c0631c3878f1c

def z546 : W := mkw 0x0000000000000000 0x64c8008000004000

def z547 : W := mkw 0x4251852965859b3d 0xdfbf873fff878fff

def z548 : W := mkw 0xf8e3fffff8334692 0x0817f631c0770e00

def z549 : W := mkw 0x90a0329490324482 0xe7c8708410704093

def z550 : W := mkw 0x0040000040010210 0x08140631c0070e00

def z551 : W := mkw 0x4251852965859b3d 0xdfbf8f7bef8fbf7c

def z552 : W := mkw 0x0080101400100480 0x2040700400700080

def z553 : W := mkw 0x6002d83e00000000 0x0013f03000000000

def z554 : W := mkw 0x0000000000000000 0x8d1c003000000e00

def z555 : W := mkw 0x6643cd2b63cd8b58 0xdfbf8f3be38f8f7c

def z556 : W := mkw 0x6492d83e06d81de5 0xbf7ff83e3ff80fff

def z557 : W := mkw 0xf802fafe98000000 0x017bf8fe1c000000

def z558 : W := mkw 0x6492d83e06d81de5 0xbd7ff97e2ff8bfec

def z559 : W := mkw 0xfc82fafe9ad80dc0 0xbd7ff8fe1ff80fe0

def z560 : W := mkw 0x00e0101440334692 0xed5c703400774e93

def z561 : W := mkw 0x97037fd4936ee000 0x7ffbfff5d3fff000

def z562 : W := mkw 0xb8027ad698000000 0x0000700000000000

def z563 : W := mkw 0x90f03294d43356b7 0xefdc76bffc774fff

def z564 : W := mkw 0xd0e0b2bcd0b34f92 0xfffff6bdd3f74f93

def z565 : W := mkw 0x60c0903f60910fd8 0x8304003fe0000ffc

def z566 : W := mkw 0x4000802800800900 0xdfbf813823808f1c

def z567 : W := mkw 0xc341a7e961a7eb18 0xdfbf87f9e387ff1c

def z568 : W := mkw 0x4241852961858b18 0xdc178631c3878f1c

def z569 : W := mkw 0x07010500036ee000 0x7cbb870003fff000

def z570 : W := mkw 0x87837fd4037ee480 0xfdfffff403fffe80

def z571 : W := mkw 0x97e37fd4d37fe692 0x7cfffff1c3fffe00

def z572 : W := mkw 0x6803cd6b28000000 0x03eb89ce3c000000

def z573 : W := mkw 0x24825816025804c0 0x3c7bf80603f800e0

def z574 : W := mkw 0xd0e0b2bdf0b34f9a 0xefdc76bdf0774f9f

def z575 : W := mkw 0x0000000000000000 0x428001002000801c

def z576 : W := mkw 0x90e03294d0334692 0xad5c7635c0770e80

def z577 : W := mkw 0x06c0000043dd8fd8 0xfc04000003ff8ffc

def z578 : W := mkw 0x0001050000000000 0x00bb870000000000

def z579 : W := mkw 0xfa43fffff9858b18 0x0817f631c3870e00

def z580 : W := mkw 0x0402480002480000 0x1023880003880000

def z581 : W := mkw 0x87036fc0036ee000 0x3c7bfe0003ff0000

def z582 : W := mkw 0x0000000000000000 0xe400000000004093

def z583 : W := mkw 0x0480000002d80dc0 0xbd6c080e03f80fe0

def z584 : W := mkw 0xd0e1b7bdf0334692 0xeffff7bdf0774e93

def z585 : W := mkw 0x6482d83e02d80dc0 0xa144783e00780fe0

def z586 : W := mkw 0x6402c82a02c80940 0x3c7bf80a03f80160

def z587 : W := mkw 0x0000000000000000 0x830000082000011c

def z588 : W := mkw 0xfa43fffff9058218 0x43fbfffffc07801c

def z589 : W := mkw 0x90e02280d0334692 0xee840681d0774e93

def z590 : W := mkw 0x4743cd6963cdab18 0xdfbf8f79e38fbf1c

def z591 : W := mkw 0xf8f3fffffc3356b7 0xfffffffffc7fffff

def z592 : W := mkw 0x4201852921848908 0xd7ab81082380811c

def z593 : W := mkw 0x0740000043efeb18 0xfc04000003ffff1c

def z594 : W := mkw 0x00c0101440110690 0xefdc7635c0770e90

def z595 : W := mkw 0x0010000004001025 0x74e809c61c08f0e3

def z596 : W := mkw 0x0000101400000000 0x0158703400000000

def z597 : W := mkw 0xf843fffff8010210 0xcffffffffc070e10

def z598 : W := mkw 0x00a0000000324482 0x2000000000704083

def z599 : W := mkw 0xf883ffffb8100480 0xaffffffffc700e80

def z600 : W := mkw 0x4001852920000000 0x0023810820000000

def z601 : W := mkw 0xe703efea03eee940 0x7cfbffca03fff160

def z602 : W := mkw 0x9000228090000000 0x02800681d0000000

def z603 : W := mkw 0x981127c1bc001025 0x428007c1fc00f01f

def z604 : W := mkw 0x0040000040010210 0x83040031c0000e10

def z605 : W := mkw 0x10f01014d41116b7 0xf7ec09fffc08ffff

def z606 : W := mkw 0x0010000004001025 0x13e809ce3c08b16c

def z607 : W := mkw 0x0010000004001025 0xb56808ce1c0871e3

def z608 : W := mkw 0x6782d83e03feedc0 0xfd7ff83e03ffffe0

def z609 : W := mkw 0x0240000041858b18 0xdfac010823878f1c

def z610 : W := mkw 0x70e0903ed0910fd2 0x8304003fd0000ff3

def z611 : W := mkw 0x8000228000224000 0xefd8768410774093

def z612 : W := mkw 0x90602280d0234212 0xcf9c06b1d0074e13

def z613 : W := mkw 0x0000000000000000 0xe7e809ce3c004093

def z614 : W := mkw 0x6813cd6b2c001025 0x1023894a2c08b16c

def z615 : W := mkw 0x87026ac0036ee000 0x7c4078c003fff000

def z616 : W := mkw 0x90602280d0234212 0x6ed87681d0774013

def z617 : W := mkw 0x831127c00526f025 0x428007c03c07f01f

def z618 : W := mkw 0x87036fc0036ee000 0x08fbffc003f70000

def z619 : W := mkw 0xc703efe9236ee000 0x7ffbfff9e3fff000

def z620 : W := mkw 0xb8127ad69c001025 0xf7e879ce3c08f1ff

def z621 : W := mkw 0x8000228000224000 0x2040708000704000

def z622 : W := mkw 0x830127c00126e000 0x6cd877c00077f000

def z623 : W := mkw 0x6243dd3f61858b18 0xdfffff3fe3878f1c

def z624 : W := mkw 0x07e00000437fe692 0xfc04000003fffe93

def z625 : W := mkw 0x90e03294d0334692 0xec44708410774e93

def z626 : W := mkw 0x90e03294d0334692 0xcf9c7631c0770e10

def z627 : W := mkw 0x6002d83e00000000 0xb57bf83e000801e0

def z628 : W := mkw 0x6803cd6b28000000 0x0003800000000000

def z629 : W := mkw 0x04e0000042fb4fd2 0xfc04000003ff4ff3

def z630 : W := mkw 0x4201852921848908 0x0003800003800000

def z631 : W := mkw 0x94e27a94d27b4692 0xfffffeb5d3ff4e93

def z632 : W := mkw 0x0010000004001025 0x9320094e3c08b1ff

def z633 : W := mkw 0x90e03294d0334692 0x6cdc76b1c0774e00

def z634 : W := mkw 0x6683dd3e03dc8dc0 0xfdffff3e03ff8fe0

def z635 : W := mkw 0x0241050041058210 0xdfbf8731c3878e10

def z636 : W := mkw 0x2402480202480040 0x0000080200080060

def z637 : W := mkw 0x0010000004001025 0xe7c8008e3c0041ff

def z638 : W := mkw 0x0000000000000000 0x1020080a00080160

def z639 : W := mkw 0xe703fffe036ee000 0x7dfbfffe03fff000

def z640 : W := mkw 0x7840903ff8810b18 0x8304003ffc000f1c

def z641 : W := mkw 0xe003fffe00000000 0x01fbfffe00000000

def z642 : W := mkw 0x4201852921848908 0x9d3f813823808f0c

def z643 : W := mkw 0xbc827ad69a5804c0 0x204078c61c7800e0

def z644 : W := mkw 0x0000000000000000 0xf7e8018c3000c19f

def z645 : W := mkw 0x9000329490000000 0x0040708410000000

def z646 : W := mkw 0x6482d83e02d80dc0 0x3c7ff83003f80e00

def z647 : W := mkw 0x0010000004001025 0x62c009c63c08f0ff

def z648 : W := mkw 0x0010000004001025 0xd7a8094a2c08b17c

def z649 : W := mkw 0x87836fc003feedc0 0xfcffffc003ffffe0

def z650 : W := mkw 0x0010000004001025 0xf568080e0008f1ff

def z651 : W := mkw 0x0240000041858b18 0x0804000003870e00

def z652 : W := mkw 0x0000000000000000 0x740000000008f000

def z653 : W := mkw 0xfae3fffff9b7cf9a 0xfffffffffff7cf9f

def z654 : W := mkw 0x02e0000041b7cf9a 0xfc04000003f7cf9f

def z655 : W := mkw 0xf0e0b2bed0b34fd2 0xefdc76bfd0774ff3

def z656 : W := mkw 0x10e01014d0334692 0xef040035d0774e93

def z657 : W := mkw 0x4241852961858b18 0xdc27810823878f1c

def z658 : W := mkw 0x6402d83e02c80940 0x117bf83e03880160

def z659 : W := mkw 0x0010000004001025 0x000000061c0000e3

def z660 : W := mkw 0x85026ac0026a6000 0x3c7bf8c003f87000

def z661 : W := mkw 0xb8037fd698000000 0x00fbffc61c000000

def z662 : W := mkw 0x936127c0d127e212 0x428007c1d007f013

def z663 : W := mkw 0x0010000004001025 0xa34008ce3c0871ff

def z664 : W := mkw 0xd7e3fffdf3ffef9a 0xfffffffdf3ffff9f

def z665 : W := mkw 0x0010000004001025 0x76e809c03c08f01f

def z666 : W := mkw 0x025105016505923d 0x428007c1fc07f01f

def z667 : W := mkw 0x0000000000000000 0x0168080e00000000

def z668 : W := mkw 0x0040000040010210 0xdfbc0739e0078f1c

def z669 : W := mkw 0x93e137d4d137e692 0xefdc77f5d077fe93

def z670 : W := mkw 0xf4e2fabed2fb4fd2 0xbd7ffe3fc3ff0fe0

def z671 : W := mkw 0x87036fc0036ee000 0x60c07fc0007ff000

def z672 : W := mkw 0x2482581602d80dc0 0xbc44780603f80fe0

def z673 : W := mkw 0x92e03294d1b7cf9a 0xffdc76b5d3f7cf9f

def z674 : W := mkw 0x0000000000000000 0xd40000000000811c

def z675 : W := mkw 0x90f03294d43356b7 0xefdc77f5fc77fe9f

def z676 : W := mkw 0xfc83ffffbad80dc0 0xbd7ffe3fc3f80fe0

def z677 : W := mkw 0x2002581600000000 0x0040780600000000

def z678 : W := mkw 0x92e13794d137c692 0xfffff7b5d3f7ce93

def z679 : W := mkw 0x8000228000000000 0x00d8768000000000

def z680 : W := mkw 0x80026ac000000000 0x004078c000000000

def z681 : W := mkw 0x92612781f127c21a 0x42800781f007c01f

def z682 : W := mkw 0x0490000006d81de5 0xffec09ce3ff8ffff

def z683 : W := mkw 0x87036fc0034ca000 0x10fbffc00388b000

def z684 : W := mkw 0x85026ac0026a6000 0x0000700000700000

def z685 : W := mkw 0xf803ffffb8000000 0x017bfe3fc0000000

def z686 : W := mkw 0xf813ffffbc001025 0x13fbfffffc08b16c

def z687 : W := mkw 0x4643cd2963cd8b18 0xffffff39e3ff8f1c

def z688 : W := mkw 0x07100000076ef025 0xffe809ce3ffff1ff

def z689 : W := mkw 0x92e13795f137c69a 0xefdc77b5f077ce9f

def z690 : W := mkw 0x20801016001004c0 0x00000006000000e0

def z691 : W := mkw 0xf8e3fffff8110692 0x83fffffffc000e93

def z692 : W := mkw 0xb8027ad698000000 0x03e879ce3c000000

def z693 : W := mkw 0x4241852961858b18 0xcf9f8631c3870e10

def z694 : W := mkw 0x0241050161058218 0xd7a80709e007811c

def z695 : W := mkw 0x830127c00126e000 0x5cbb87c00387f000

def z696 : W := mkw 0x0000000000000000 0xa548000400000080

def z697 : W := mkw 0xd2e1b7bdf1b7cf9a 0xdfbff739e3f78f1c

def z698 : W := mkw 0xff03ffffbb6ee000 0x7cfbfff1c3fff000

def z699 : W := mkw 0x4010802804801925 0xffff89fe3f88ffff

def z700 : W := mkw 0x10600000d0010212 0x02000001d0000013

def z701 : W := mkw 0xf4e2fabed2fb4fd2 0x0817f631c3f70e00

def z702 : W := mkw 0x84026a80026a4000 0x7cfbfe8003ff4000

def z703 : W := mkw 0xf843fffff8810b18 0x83fffffffc000f1c

def z704 : W := mkw 0x6002c82a00000000 0x0023880a00000000

def z705 : W := mkw 0x6813cd6b2c001025 0xf7eb89ce3c08f1ff

def z706 : W := mkw 0x0010000004001025 0x000001402c00b00c

def z707 : W := mkw 0x6482d83e02d80dc0 0x3c7ff83a03f80f60

def z708 : W := mkw 0x87036fc1236ee008 0x7cfbffc023fff00c

def z709 : W := mkw 0x90e03294d0334692 0xefdc77f5fc774e93

def z710 : W := mkw 0x6482d83e02d80dc0 0xbd3ff03803f80fe0

def z711 : W := mkw 0xfc83ffffbad80dc0 0x8b17f63ffff00fe0

def z712 : W := mkw 0x9a0127c1b9048000 0x428007c1fc078000

def z713 : W := mkw 0xfc83ffffbad80dc0 0x9ffffffffff00f00

def z714 : W := mkw 0x87036fc0036ee000 0x5cbbff4003ffb000

def z715 : W := mkw 0x7800903fb8000000 0xb768083ffc0801e0

def z716 : W := mkw 0x00f00000443356b7 0xec0400000077fe9f

def z717 : W := mkw 0x7c82d83fbad80dc0 0xbffff9fffff80fe0

def z718 : W := mkw 0x0010000004001025 0xd3a009ce3c08f1ff

def z719 : W := mkw 0xf803ffffb8000000 0x2ffbfffffc700000

def z720 : W := mkw 0x4241852961858b18 0x88178631c3870f1c

def z721 : W := mkw 0x0070000044235237 0x400000000007f01f

def z722 : W := mkw 0xfa03ffffb9848908 0x9fffffffff808f0c

def z723 : W := mkw 0x820127800126c000 0x7cfbffc003fff000

def z724 : W := mkw 0xf8a3ffffb8324482 0x03fbfffffc700000

def z725 : W := mkw 0xd801b7fdb8000000 0x03fbf7fdfc000000

def z726 : W := mkw 0x1000101490000000 0x03e809fffc000000

def z727 : W := mkw 0x6482d83e02d80dc0 0xbc57f83603f80fe0

def z728 : W := mkw 0xf803ffffb8000000 0x83fbfffffc000093

def z729 : W := mkw 0x68e3cd6b68334692 0xec27894a2c774e93

def z730 : W := mkw 0x4241852961858b18 0xdfbf8f3be38f8f7c

def z731 : W := mkw 0x025000004505923d 0xf4000000000ff1ff

def z732 : W := mkw 0x6482d83e02d80dc0 0xfffff9fe23f8fffc

def z733 : W := mkw 0x7800903fb8000000 0x02000031fc000000

def z734 : W := mkw 0xff03ffffbb6ee000 0x4a93f7f1fff7f000

def z735 : W := mkw 0xfd03ffffba6a6000 0x3ffbfffffff87000

def z736 : W := mkw 0xd2a1b7bdb1b6cd8a 0x3063f18c33f0c18f

def z737 : W := mkw 0x00e0101440334692 0xefdc7635c0774e93

def z738 : W := mkw 0xf801b7ffb8000000 0x03e80ffffc000000

def z739 : W := mkw 0x4241852961858b18 0xdfbf873df3878f9f

def z740 : W := mkw 0xfa03ffffb9848908 0x5ffbffffff87810c

def z741 : W := mkw 0xfd03ffffba6a6000 0x77fbfffffc78f000

def z742 : W := mkw 0xff03ffffbb6ee000 0xfffbfffffffff093

def z743 : W := mkw 0x7802d87fb8000000 0x0300087ffc000000

def z744 : W := mkw 0xf803ffffb8800900 0xdfffffffff808f1c

def z745 : W := mkw 0x18000001b8000000 0x0300000ffc000000

def z746 : W := mkw 0x4241852961858b18 0xdfbf8f79e38fbf1c

def z747 : W := mkw 0x0010000004001025 0x72e009ce3c08f1ff

def z748 : W := mkw 0xfc03ffffba480000 0x0bfbfffffff00000

def z749 : W := mkw 0x9000228090000000 0x03e80fcffc000000

def z750 : W := mkw 0xfa03ffffb9848908 0x03fbffffff800000

def z751 : W := mkw 0x87036fc0036ee000 0x7efbffc013fff013

def z752 : W := mkw 0x7f00903fbb6ee000 0x7f00003ffffff000

def z753 : W := mkw 0x00f01014443356b7 0xfd7c783e007fffff

def z754 : W := mkw 0xf883ffffb8100480 0x23fbfffffc700080

def z755 : W := mkw 0xfe83ffffbbdc8dc0 0xffffffffffff8fe0

def z756 : W := mkw 0xf462eaaad2eb4b52 0x52a38e8bd38f4173

def z757 : W := mkw 0xf883ffffb8100480 0xbffffffffc780fe0

def z758 : W := mkw 0xf903ffffb8226000 0x03fbfffffc007000

def z759 : W := mkw 0xff03efebbb6ee000 0x7efbffcbfffff000

def z760 : W := mkw 0x4251852965859b3d 0x28578ef7df8f7ee3

def z761 : W := mkw 0x90e03294d0334692 0xfffc7eb5d07f4e93

def z762 : W := mkw 0x6613cd2b27cc996d 0x1023894a2f88b16c

def z763 : W := mkw 0x90e03294d0334692 0xfffc7fbff07fcfff

def z764 : W := mkw 0x7800903fb8000000 0xd7a8013ffc00811c

def z765 : W := mkw 0x6803cd6b28000000 0x00338f7bec000000

def z766 : W := mkw 0x980127c1b8000000 0x02bb87c1fc000000

def z767 : W := mkw 0x00e0101440110692 0x8104003400000e93

def z768 : W := mkw 0x6482d83e02d80dc0 0xbd7ff93e23f88fec

def z769 : W := mkw 0x980127c1b8000000 0x00000741ec000000

def z770 : W := mkw 0x6482d83e02d80dc0 0xfffff9fe3ff88ffc

def z771 : W := mkw 0x7800903fb8000000 0x03c800bffc000000

def z772 : W := mkw 0xff03ffffbb6ee000 0xfffbfffffffff11c

def z773 : W := mkw 0xf803ffffb8224000 0x7ffbfffffc7ff000

def z774 : W := mkw 0xff03ffffbb4ca000 0x5ffbffffff8fb000

def z775 : W := mkw 0x80f02280443356b7 0xfcfc7fc0007fffff

def z776 : W := mkw 0x6482d83e02d80dc0 0xbd7ff97e2ff80fe0

def z777 : W := mkw 0xf880b2bfb8900dc0 0xafdc76bffc700fe0

def z778 : W := mkw 0x9010329494001025 0xf7d876b5d008f1ff

def z779 : W := mkw 0xfc83ffffba5804c0 0x3ffbfffffff800e0

def z780 : W := mkw 0x0201050121048000 0x5ebb8701e3878000

def z781 : W := mkw 0x4241852961858b18 0x4bbf8739e3878e1c

def z782 : W := mkw 0xfc03ffffbac80900 0xbffffffffff80f00

def z783 : W := mkw 0xf803ffffb8000000 0x97fbfffffc000100

def z784 : W := mkw 0x87036fc0036ee000 0x7efbffc03ffff000

def z785 : W := mkw 0xf803ffffb8000000 0x67fbfffffc004000

def z786 : W := mkw 0x980127c1b8000000 0x76e80fc1fc08f000

def z787 : W := mkw 0x9f036fc1bb6ee000 0x0813f601c3f70000

def z788 : W := mkw 0xf803ffffb8000000 0x03c07ffffc000000

def z789 : W := mkw 0xfc83ffffbafa4dc0 0xffffffffffff4fe0

def z790 : W := mkw 0x26c35d17635d86d8 0x62c07f07e07f80fc

def z791 : W := mkw 0xb8037fd7b8000000 0x03e87fcffc000000

def z792 : W := mkw 0x90e03294d0334692 0xefdc7ef7dc774e93

def z793 : W := mkw 0x4001852920000000 0x03bb87f9fc000000

def z794 : W := mkw 0x6482d83e02d80dc0 0xbd5ff03403f80fe0

def z795 : W := mkw 0xda01a7e9b9848908 0x12a387c9ff80810c

def z796 : W := mkw 0x9f036fc1bb6ee000 0x7ffbffcffffff000

def z797 : W := mkw 0xf801b7ffb8000000 0x028007f1fc000000

def z798 : W := mkw 0xfc83ffffbad80dc0 0xbd7fff7feff80fe0

def z799 : W := mkw 0x87f36fc0477ff6b7 0xfcffffc003ffffff

def z800 : W := mkw 0xf813ffffbc001025 0xf413f631c008f1ff

def z801 : W := mkw 0xfc83ffffbad80dc0 0x2bfffffffff80ee0

def z802 : W := mkw 0x6482d83e02d80dc0 0xbd7ff8fe03f87fe0

def z803 : W := mkw 0x4241852961858b18 0xffff87b9e387cf1c

def z804 : W := mkw 0xff03ffffbb6ee000 0x1833ff7befffb000

def z805 : W := mkw 0xf8a0b2bfb8324482 0x234070bffc704083

def z806 : W := mkw 0x90e03294d0334692 0xad5c76b5d0774e83

def z807 : W := mkw 0x7800903fb8000000 0x03a8013ffc000000

def z808 : W := mkw 0x90e03294d0334692 0xefdc7eb7d07f4ef3

def z809 : W := mkw 0xf883ffffb81004c0 0x03fbfffffc0000e0

def z810 : W := mkw 0x0482581402580480 0xbd7ff83e03f80fe0

def z811 : W := mkw 0xf803ffffb8800900 0x83fffffffc000f00

def z812 : W := mkw 0x0241050041858b18 0xdfbf8731c3878f1c

def z813 : W := mkw 0x4241852961858b18 0xdfbf873fff878f1c

def z814 : W := mkw 0x3c8258169a5804c0 0x204078061c7800e0

def z815 : W := mkw 0xf803ffffb8000000 0xc7fbfffffc000010

def z816 : W := mkw 0xc003efe920000000 0x03fbfffffc000000

def z817 : W := mkw 0x7c02d83fbac80940 0x1323883fff880160

def z818 : W := mkw 0x0482581402d80dc0 0xbd7ff83403f80fe0

def z819 : W := mkw 0x7803cd6bb8000000 0x0223894bfc000000

def z820 : W := mkw 0xff03ffffbb4ca000 0x3ffbfffffff8b000

def z821 : W := mkw 0x4241852961858b18 0xdfbf87f9ff878f1c

def z822 : W := mkw 0x0241050041058210 0xdfbf8739e3878f1c

def z823 : W := mkw 0xf803ffffb8000000 0x00fbfffbec000000

def z824 : W := mkw 0x90f03294d43356b7 0x18347f7bec7fbf6c

def z825 : W := mkw 0x0240000041858b18 0xdfec09ce3f878f1c

def z826 : W := mkw 0xd801a7e9b8800900 0x9fbf87f9ff800f00

def z827 : W := mkw 0x87036fc1236ee000 0x7efbffc1e3fff000

def z828 : W := mkw 0x7802d83fb8000000 0x0340783ffc000000

def z829 : W := mkw 0xc542eae962eb6b18 0xa34478f9e0787f1c

def z830 : W := mkw 0xb80137d7b8000000 0x028007c7fc000000

def z831 : W := mkw 0xfc83ffffbad80dc0 0xfffffffffff8ffe0

def z832 : W := mkw 0xff03ffffbbeee900 0xffffffffffffff00

def z833 : W := mkw 0x90e03294d0334692 0x48147631c0774e13

def z834 : W := mkw 0x6482d83e02d80dc0 0xfdfff8be03f84fe0

def z835 : W := mkw 0x0801054128000000 0x02800741ec000000

def z836 : W := mkw 0xba427ad6d9858b18 0xdc4478c61f878f1c

def z837 : W := mkw 0xf800b2bfb8224000 0x6fd876bffc774000

def z838 : W := mkw 0xc703efe9236ee000 0x7ffbfffffffff000

def z839 : W := mkw 0x4011852924001025 0xf7bb8739e008f1ff

def z840 : W := mkw 0x9c8127c1bad80dc0 0xbe8407c1fff80fe0

def z841 : W := mkw 0x6482d83e02d80dc0 0xfffff9fe3ff8ffe0

def z842 : W := mkw 0xf803ffffb8000000 0xf7fbfffffc08f11c

def z843 : W := mkw 0xb8036fc3b8000000 0x02800fc3fc000000

def z844 : W := mkw 0xfe03ffffbbcc8948 0x13fbffffff88816c

def z845 : W := mkw 0x97036fc0936ee000 0x7efbffc1d3fff000

def z846 : W := mkw 0x1000101490000000 0x0300003ffc000000

def z847 : W := mkw 0x6492d83e06d81de5 0x4a97f1f03ff0fe1f

def z848 : W := mkw 0xfc03ffffbac80940 0x03fbffffff800000

def z849 : W := mkw 0xfc82faffbad80dc0 0xbf7ff8fffff80fe0

def z850 : W := mkw 0x0000000000000000 0x76e809c03c08f000

def z851 : W := mkw 0xfb03ffffb904a000 0x03fbfffffc00b000

def z852 : W := mkw 0x6482d83e02d80dc0 0x9d3ff83a03f80f60

def z853 : W := mkw 0xfd02faffba6a6000 0x234078fffc787000

def z854 : W := mkw 0x4241852961858b18 0x1bbf8739e3878f0c

def z855 : W := mkw 0x6482d83e02d80dc0 0xbd7ff8fe1ff80fe0

def z856 : W := mkw 0x4241852961858b18 0xdfff8ff9e3878f1c

def z857 : W := mkw 0xf883ffffb8900dc0 0xb7fffffffc080fe0

def z858 : W := mkw 0x4241852961858b18 0x9d3f8739e3878f0c

def z859 : W := mkw 0xfc83ffffba5804c0 0xaffffffffc780ee0

def z860 : W := mkw 0x9c036fc1ba480000 0x3efbffc1fff80000

def z861 : W := mkw 0x980127c1b8000000 0x02a00fcbfc000000

def z862 : W := mkw 0x2482581602d80dc0 0xbc7ff80603f80fe0

def z863 : W := mkw 0x87136fc0076ef025 0x8b13f60e3ff701ff

def z864 : W := mkw 0x7800903fb8000000 0x0368083ffc000000

def z865 : W := mkw 0x9f036fc1bb6ee000 0x0a93f7c1fff70000

def z866 : W := mkw 0x90e03294d0334692 0xcf9c76b1d0774e13

def z867 : W := mkw 0xb8037fd7b8000000 0x028077c1fc000000

def z868 : W := mkw 0x980127c1b8000000 0xb7e80fcffc0801e0

def z869 : W := mkw 0x7800903fb8800900 0x9f3f803fff800f00

def z870 : W := mkw 0x7f03dd7fbb4ca000 0x1323897fff88b000

def z871 : W := mkw 0x6482d83e02d80dc0 0xfdfffe3e03ff0fe0

def z872 : W := mkw 0xf803efebb8000000 0x02fbffcbfc000000

def z873 : W := mkw 0xfc03efebbac80940 0x12a38fcbff880160

def z874 : W := mkw 0xf803ffffb8800900 0x13fbffffff800100

def z875 : W := mkw 0x90e03294d0334692 0xfffc7ffffc7f4ff3

def z876 : W := mkw 0x6c02c82b2ac80940 0x1023880a2f880160

def z877 : W := mkw 0x7803dd7fb8000000 0x0303803ffc000000

def z878 : W := mkw 0x9a0127c1b9048008 0x028007c1fc00800c

def z879 : W := mkw 0xf8a3ffffb8324482 0xaffffffffc704e83

def z880 : W := mkw 0xd801a7e9b8000000 0x038007f9fc000000

def z881 : W := mkw 0xf803ffffb8000000 0x23fbfffffc0800e0

def z882 : W := mkw 0x90e03294d0334692 0xfffc7ffffc77cf9f

def z883 : W := mkw 0x980127c1b8000000 0x03a807c9fc000000

def z884 : W := mkw 0x90e03294d0334692 0xfffc77b5d077ce93

def z885 : W := mkw 0xf803ffffb8000000 0x0013f6f1dc000000

def z886 : W := mkw 0x6482d83e02d80dc0 0xa957f83e03f80fe0

def z887 : W := mkw 0x00e0000040334692 0xefec09ce3c774e93

def z888 : W := mkw 0x98e032d4d8334692 0xefdc76f5dc774e93

def z889 : W := mkw 0x6800802b28000000 0x0300003bec000000

def z890 : W := mkw 0x87036fc0036ee000 0x7cfbffc603fff0e0

def z891 : W := mkw 0x7c92d83fbed81de5 0xfffff9fffff8ffff

def z892 : W := mkw 0xfd03ffffba6a6000 0x03fbfffffc700000

def z893 : W := mkw 0x980127c1b8000000 0x038007cffc000000

def z894 : W := mkw 0xb800329698000000 0x03d876b7dc000000

def z895 : W := mkw 0xf8a3ffffb8324482 0x6ffbfffffc774083

def z896 : W := mkw 0x7800903fb8800940 0x0300003ffc000160

def z897 : W := mkw 0x87036fc0036ee000 0x7cbbf70003fff000

def z898 : W := mkw 0x4241852961858b18 0x5cbf8739e3878f0c

def z899 : W := mkw 0x0000000000000000 0x03f80ffffc000000

def z900 : W := mkw 0x6482d83e02d80dc0 0x0817f83203f80e60

def z901 : W := mkw 0x0010000004001025 0xfff879ce3c78f1ff

def z902 : W := mkw 0x6482d83e02d80dc0 0xbc7ff83003f80fe0

def z903 : W := mkw 0x87036fc0036ee000 0x7dfbffce03fff000

def z904 : W := mkw 0x980127c1b8000000 0x039807f1fc000000

def z905 : W := mkw 0xe381b7fe01b6edc0 0xc18407fe0007ffe0

def z906 : W := mkw 0x9f0127c1bb6ee000 0x7e8007c1fffff000

def z907 : W := mkw 0x6482d83e02d80dc0 0xbffff93e23f80fe0

def z908 : W := mkw 0x90e03294d0334692 0xfffc76bdd0774f93

def z909 : W := mkw 0x6482d83e02d80dc0 0xbf7ff83e23f80ffc

def z910 : W := mkw 0x6482d83e02d80dc0 0x1817f03003f80f60

def z911 : W := mkw 0x90e03294d0334692 0xffdc76b5d077cf9f

def z912 : W := mkw 0xf803ffffb8000000 0x03bbf73ffc000000

def z913 : W := mkw 0x0001050120000000 0x028007c1fc000000

def z914 : W := mkw 0x6482d83e02d80dc0 0xad5ff83603f80ee0

def z915 : W := mkw 0xfa03ffffb926c000 0x7ffbfffffff7c000

def z916 : W := mkw 0x6a41852b69858b18 0xdfbf873bef878f1c

def z917 : W := mkw 0x6241852b61858b58 0xdfbf873be3878f7c

def z918 : W := mkw 0xf803ffffb8224000 0x0bfbfffffc770000

def z919 : W := mkw 0x6c82d87e0ad80dc0 0xbd7ff87e0ff80fe0

def z920 : W := mkw 0x00f00000443356b7 0xec04000000774fff

def z921 : W := mkw 0x90e03294d0334692 0xecdc76b1c0774e93

def z922 : W := mkw 0xff03ffffbb6ee000 0x7cfbfff7dffff000

def z923 : W := mkw 0x98002281b8000000 0x02800681fc000000

def z924 : W := mkw 0x00f00000443356b7 0xec040000007f7ef3

def z925 : W := mkw 0x7c83dd7fbad80dc0 0x9327897fff880fe0

def z926 : W := mkw 0x7c83dd7fbad80dc0 0xbf7ff97ffff80fe0

def z927 : W := mkw 0x6482d83e02d80dc0 0xbf7ff83e3ff80fe0

def z928 : W := mkw 0xf803ffffb8000000 0x017bfeffdc000000

def z929 : W := mkw 0x6482d83e02d80dc0 0xfdfff93e03f88fe0

def z930 : W := mkw 0x90e03294d0334692 0xab5476b5d0774e93

def z931 : W := mkw 0x4402c82802c80900 0xbd7ff83e03f80fe0

def z932 : W := mkw 0xf803ffffb8000000 0x0363f9fffc000000

def z933 : W := mkw 0x90e03294d0334692 0xee9476b1d0774e93

def z934 : W := mkw 0xfd03ffffba6a6000 0x6ffbfffffc7f7000

def z935 : W := mkw 0xb8037fd7b8000000 0x03d87ff7fc000000

def z936 : W := mkw 0x87036fc0036ee000 0xfffbffce3ffff1e0

def z937 : W := mkw 0x7803dd7fb8000000 0x03bb8f7ffc000000

def z938 : W := mkw 0xf883ffffb8900d80 0xbffffffffff00f80

def z939 : W := mkw 0x4241852961858b18 0x48178631c3878e1c

def z940 : W := mkw 0xf802faffb8000000 0x0300703ffc000000

def z941 : W := mkw 0x87036fc0036ee000 0x5cbbf7c003f7f000

def z942 : W := mkw 0x07024800036ee000 0x7cfbf9c003fff000

def z943 : W := mkw 0x7c83dd3fbad80dc0 0xbfffff3ffff80fe0

def z944 : W := mkw 0x6482d83e02d80dc0 0x0817f03a03f00f60

def z945 : W := mkw 0x980022c098000000 0x028006c1dc000000

def z946 : W := mkw 0x87036fc0036ee000 0x4813f60003f7f000

def z947 : W := mkw 0xf802faffb8000000 0x004078f7dc000000

def z948 : W := mkw 0x90e03294d0334692 0xefdc76bfd0774ff3

def z949 : W := mkw 0x00f00000441116b7 0x8004000000000fff

def z950 : W := mkw 0x0250000045859b3d 0xdc0400000387ff1f

def z951 : W := mkw 0x4241852961858b18 0xdf178639e3878f1c

def z952 : W := mkw 0xfce2fabffafb4fd2 0xfffffebfffff4ff3

def z953 : W := mkw 0x980137d5b8000000 0x03f87ffffc000000

def z954 : W := mkw 0x7800903fb8800900 0x8304003ffc000f00

def z955 : W := mkw 0x7802d83fb8000000 0x0313f03ffc000000

def z956 : W := mkw 0x90e03294d0334692 0xeffc7ff5d0774e93

def z957 : W := mkw 0x92712781f527d23f 0x428007c1fc07f01f

def z958 : W := mkw 0x980127c1b8000000 0x428007c1fc00f000

def z959 : W := mkw 0x6482d83e02d80dc0 0x897ff83e03f00fe0

def z960 : W := mkw 0xfc03ffffbac80940 0x9fffffffff880f60

def z961 : W := mkw 0x7800903fb8000000 0x034008fffc000000

def z962 : W := mkw 0x87036fc0036ee000 0xfdfbffc403fff080

def z963 : W := mkw 0x87036fc0036ee000 0x6cdbf7c003f7f000

def z964 : W := mkw 0x7803dd7fb8000000 0x03eb89fffc000000

def z965 : W := mkw 0xb8027ad698000000 0x00507ef7dc000000

def z966 : W := mkw 0x6482d83e02d80dc0 0xad5ff03e03f00fe0

def z967 : W := mkw 0x9b0127c1b926e000 0x028007c1fc070000

def z968 : W := mkw 0x6482d83e02d80dc0 0xbffff8be13f80fe0

def z969 : W := mkw 0xfc83ffffbad80dc0 0xfffffffffff88ffc

def z970 : W := mkw 0x4241852961858b18 0x9f3f8639e3870f1c

def z971 : W := mkw 0x7ec3dd3ffbdd8fd8 0xffffff3fffff8ffc

def z972 : W := mkw 0xf803ffffb8000000 0x13fbfffffc08b000

def z973 : W := mkw 0x980127c1b8000000 0x03c807c5fc000000

def z974 : W := mkw 0xf803ffffb8000000 0x83fbfffffc00011c

def z975 : W := mkw 0xf803ffffb8000000 0x03dbfef7dc000000

def z976 : W := mkw 0x4241852961858b18 0xdfbf87b9f387cf1f

def z977 : W := mkw 0x0010000004001025 0x408001c00000f01f

def z978 : W := mkw 0x90e03294d0334692 0xed5c7635c0774e93

def z979 : W := mkw 0x6482d83e02d80dc0 0xbffffe3fc3f80fe0

def z980 : W := mkw 0xfca3ffffba7a44c2 0x23fbfffffc7840e3

def z981 : W := mkw 0xaf036fc20b6ee000 0x7cfbffc20ffff000

def z982 : W := mkw 0xf803ffffb8000000 0x037bfe3ffc000000

def z983 : W := mkw 0x7802d83fb8000000 0x0323883ffc000000

def z984 : W := mkw 0x3800101698000000 0x03000037dc000000

def z985 : W := mkw 0x8f036fc12b6ee000 0x7cfbffc02ffff000

def z986 : W := mkw 0xb8027ad698000000 0x02c07ec7dc000000

def z987 : W := mkw 0x07034d40036ee000 0x7c7bf94003fff000

def z988 : W := mkw 0x90e03294d0334692 0xef147635d0774e93

def z989 : W := mkw 0x0250000045859b3d 0xdc040000038fbf7c

def z990 : W := mkw 0xfa03ffffb9848908 0xd7fbffffff80811c

def z991 : W := mkw 0x0070000044235237 0xf4000000000ff1ff

def z992 : W := mkw 0xfc83ffffbad80dc0 0x93ffffffff880fe0

def z993 : W := mkw 0x980127c1b8000000 0x428007c1fc004013

def z994 : W := mkw 0x9000228090000000 0x028007c1fc000000

def z995 : W := mkw 0xf883ffffb8900dc0 0x9fffffffff800fe0

def z996 : W := mkw 0xf801a7ebb8000000 0x028007cbfc000000

def z997 : W := mkw 0x7803dd7fb8000000 0x037bf97ffc000000

def z998 : W := mkw 0x0010000004001025 0xf46009ce3c08f1ff

def z999 : W := mkw 0xff03ffffbb4ca000 0x77fbffffff88f000

def z1000 : W := mkw 0x87036fc0036ee000 0x3c7bfec003ff7000

def z1001 : W := mkw 0xb8e27ad6d8334692 0xec4478c61c774e93

def z1002 : W := mkw 0xf803ffffb8000000 0x0333ff7ffc000000

def z1003 : W := mkw 0x0001050120000000 0x03e80fcffc000000

def z1004 : W := mkw 0xf881b7ffb8900dc0 0x838407fffc000fe0

def z1005 : W := mkw 0x980127c1b8000000 0x428007c1fc00801c

def z1006 : W := mkw 0xbf037fd7bb6ee000 0x62c07fc7fc7ff000

def z1007 : W := mkw 0x04f0000046fb5ff7 0xfc04000003ffffff

def z1008 : W := mkw 0x7c82d83e9ad80dc0 0xbd7ff83e1ff80fe0

def z1009 : W := mkw 0x4482c82802d80dc0 0xbd7ff83803f80fe0

def z1010 : W := mkw 0x7803dd3fb8000000 0x03fbff3ffc000000

def z1011 : W := mkw 0xf802faffb8000000 0x03d87efffc000000

def z1012 : W := mkw 0x87036fc0036ee000 0x7c7bfe0003fff000

def z1013 : W := mkw 0x4241852961858b18 0xffbf8739e387cf9f

def z1014 : W := mkw 0x7a01953fb9048000 0x5fbb873fff878000

def z1015 : W := mkw 0x87036fc0036ee000 0xfffbffce13fff1f3

def z1016 : W := mkw 0x90e03294d0334692 0xffdc76b5d07f4ff3

def z1017 : W := mkw 0x980137d5b8000000 0x029077f1fc000000

def z1018 : W := mkw 0x0482480002d80dc0 0xbc17f00003f80fe0

def z1019 : W := mkw 0x7803dd7fb8000000 0x0023897bec000000

def z1020 : W := mkw 0x4480903c02d80dc0 0xbd7ff03c03f80fe0

def z1021 : W := mkw 0x18010541b8000000 0x02000141fc000000

def z1022 : W := mkw 0xfe83ffffbbdc8dc8 0xbffffffffff88fec

def z1023 : W := mkw 0x4241852961858b18 0xdfbf873fe3878ffc

def z1024 : W := mkw 0xfc83ffffbad80dc0 0xaffffffffff00e80

def z1025 : W := mkw 0x98003295b8000000 0x03d876b5fc000000

def z1026 : W := mkw 0xf803ffffb8000000 0x00fbfff7dc000000

def z1027 : W := mkw 0x6482d83e02d80dc0 0xbd7ff97e03f8bfe0

def z1028 : W := mkw 0x87036fc0036ee000 0xfffbffce3ffff093

def z1029 : W := mkw 0xfa03ffffb9048000 0x7ffbffffff8ff000

def z1030 : W := mkw 0x7c82d83fbad80dc0 0xbd7ff83fc3f80fe0

def z1031 : W := mkw 0x4241852961858b18 0xde978731e3878f1c

def z1032 : W := mkw 0x87036fc0036ee000 0x48fbffc003f7f000

def z1033 : W := mkw 0x87036fc0036ee000 0x7ffbfff1c3fff000

def z1034 : W := mkw 0x9fe37fd5fb7fe692 0xfffffff5fffffe93

def z1035 : W := mkw 0x90e03294d0334692 0xefdc76bffc774e93

def z1036 : W := mkw 0x4a41856969858b18 0xdfbf8779ef878f1c

def z1037 : W := mkw 0x6c82d83f2ad80dc0 0xbd7ff83e2ff80fe0

def z1038 : W := mkw 0x87036fc0036ee000 0x7c53fec003fff000

def z1039 : W := mkw 0x07f00000477ff6b7 0xfc04000003ffffff

def z1040 : W := mkw 0xfb01b7ffb926e000 0x438007fffc07f000

def z1041 : W := mkw 0x4241852961858b18 0xdf9f8631c3878f1c

def z1042 : W := mkw 0x7881953fb8900dc0 0x9fbf873fff800fe0

def z1043 : W := mkw 0x7802d83fb8000000 0x03fbf9fffc000000

def z1044 : W := mkw 0x87026ac0036ee000 0x7c7bf8c003fff000

def z1045 : W := mkw 0x07024800036ee000 0x7c13f00003fff000

def z1046 : W := mkw 0x980032d498000000 0x03d876f5dc000000

def z1047 : W := mkw 0xf803ffffb8000000 0x0213f631fc000000

def z1048 : W := mkw 0x4241852961858b18 0xffbf8739e38f8ffc

def z1049 : W := mkw 0x90e03294d0334692 0x88147631c0770e93

def z1050 : W := mkw 0x6482d83f22d80dc0 0xbf7ff83fe3f80fe0

def z1051 : W := mkw 0x6482d83e02d80dc0 0xfd7ff83e03f88ffc

def z1052 : W := mkw 0x90e03294d0334692 0xe3c476b5d0774e93

def z1053 : W := mkw 0x6482d83e02d80dc0 0xfffff9be33f8cfff

def z1054 : W := mkw 0xff03ffffbbeee940 0x7ffbfffffffff160

def z1055 : W := mkw 0xd001b7bdb0000000 0x03fbfffffc000000

def z1056 : W := mkw 0x980127c1b8000000 0x02e80fc1fc000000

def z1057 : W := mkw 0xf803ffffb8800900 0xbfffffffff880fe0

def z1058 : W := mkw 0xf803ffffb8000000 0x03a38ffffc000000

def z1059 : W := mkw 0x87036fc0036ee000 0x0813f74003f7b000

def z1060 : W := mkw 0x87026a80036ee000 0x7cfbfe8003fff000

def z1061 : W := mkw 0x6482d83e02d80dc0 0xfffff9fe3ff84ff3

def z1062 : W := mkw 0x980127c1b8000000 0x02c00fc7fc000000

def z1063 : W := mkw 0x07034d00036ee000 0x7cfbff0003fff000

def z1064 : W := mkw 0xf803ffffb8000000 0xf7fbfffffc00c19f

def z1065 : W := mkw 0x6482d83e02d80dc0 0xb167f83e03f80fe0

def z1066 : W := mkw 0xff03ffffbb6ee000 0x6ffbfffffff74000

def z1067 : W := mkw 0x0050000044811b3d 0xf40400000008ffff

def z1068 : W := mkw 0x7c82d83fbad80dc0 0x0817f031c3f00e00

def z1069 : W := mkw 0x9000329490000000 0x03d87ef7dc000000

def z1070 : W := mkw 0x6801852b28000000 0x03bb873bec000000

def z1071 : W := mkw 0x90e03294d0334692 0xeffc77bdf0774e93

def z1072 : W := mkw 0x90e03294d0334692 0xefdc77b5f077ce9f

def z1073 : W := mkw 0xfc82fabfbad80dc0 0xbffffebffff80fe0

def z1074 : W := mkw 0x4040802960810b18 0xdfbf8639e3870f1c

def z1075 : W := mkw 0xfc03ffffba6a4000 0x7ffbffffffff4000

def z1076 : W := mkw 0xf8a3ffffb8100482 0x03fbfffffc000083

def z1077 : W := mkw 0x90e03294d0334692 0x081476b1d0774e03

def z1078 : W := mkw 0xff03ffffbb6ee000 0x0b13f63ffff70000

def z1079 : W := mkw 0x4241852961858b18 0x08178639e3870f0c

def z1080 : W := mkw 0xf803ffffb8000000 0xa7fbfffffc000080

def z1081 : W := mkw 0x90037fd490000000 0x03fbfffffc000000

def z1082 : W := mkw 0xf800b2bfb8000000 0x03f87ffffc000000

def z1083 : W := mkw 0xf803ffffb8800908 0x03fbfffffc00010c

def z1084 : W := mkw 0x980137d5b8000000 0x02c077c5fc000000

def z1085 : W := mkw 0x7482d83e92d80dc0 0xbf7ff83fd3f80fe0

def z1086 : W := mkw 0x7800903fb8000000 0xe7c800bffc004093

def z1087 : W := mkw 0x7a01953fb9848908 0x1323813fff80810c

def z1088 : W := mkw 0x980127c1b8224000 0x6ed877c1fc774000

def z1089 : W := mkw 0x6482d83e02d80dc0 0xfd7ff83e03f8ffe0

def z1090 : W := mkw 0xffa3ffffbb7ee482 0x7ffbfffffffff083

def z1091 : W := mkw 0xf801b7ffb8000000 0x03d877fffc000000

def z1092 : W := mkw 0x4240802841858b18 0xdfbf8639c3878f1c

def z1093 : W := mkw 0x7800903fb8000000 0x8300003ffc0001e0

def z1094 : W := mkw 0xfc82fafe9ad80dc0 0xbffffeffdff80fe0

def z1095 : W := mkw 0x0010000004001025 0x8100000e000001ff

def z1096 : W := mkw 0xff83ffffbbfeedc0 0x7ffffffffffffe00

def z1097 : W := mkw 0x6c03cd6b2ac80940 0x9fbf8f7bef880f60

def z1098 : W := mkw 0x91e032d4d0336692 0xefdc76f5d0777e93

def z1099 : W := mkw 0x90e03294d0334692 0xefdc76bdf0774f9f

def z1100 : W := mkw 0xf803ffffb8224000 0x43fbfffffc074000

def z1101 : W := mkw 0x4241852961858b18 0xdd3f8639c3878f1c

def z1102 : W := mkw 0x0f034d412b4ca000 0x102389402f88b000

def z1103 : W := mkw 0xfc83ffffbad80dc0 0xa3fffffffc780fe0

def z1104 : W := mkw 0xfa03ffffb9048000 0x13fbffffff808000

def z1105 : W := mkw 0x98036fc1b8000000 0x02c07fc1fc000000

def z1106 : W := mkw 0x87012780036ee000 0x7cfbf78003fff000

def z1107 : W := mkw 0x7c80903fbad80dc0 0xbf04003ffff80fe0

def z1108 : W := mkw 0xdf43efe9fbefeb18 0xfffffff9ffffff1c

def z1109 : W := mkw 0xff03ffffbb6ee000 0x1bfbffffffffb000

def z1110 : W := mkw 0x90e03294d0334692 0xfffff6b5d3f74e93

def z1111 : W := mkw 0xff03ffffbbeee908 0x7ffbfffffffff10c

def z1112 : W := mkw 0x980127c1b8000000 0xd7a807c9fc00811c

def z1113 : W := mkw 0xff83ffffbbfeedc0 0xbfffffffffff0fe0

def z1114 : W := mkw 0x4241852961858b18 0xdfbf8f7bef878f1c

def z1115 : W := mkw 0x24825816025804c0 0xbd7ff83603f80ee0

def z1116 : W := mkw 0xf883ffffb8100480 0x0bfffffffc700e00

def z1117 : W := mkw 0x4001852920000000 0x03bb873ffc000000

def z1118 : W := mkw 0x6482d83e02d80dc0 0xbd7ff8be13f84fe3

def z1119 : W := mkw 0x982127c1b8224002 0x028007c1fc004003

def z1120 : W := mkw 0x90e03294d0334692 0xaf5c7635d0770e93

def z1121 : W := mkw 0xfd03ffffba482000 0x03fbfffffc083000

def z1122 : W := mkw 0x90e03294d0334692 0xcb9476b5d0774e93

def z1123 : W := mkw 0xff03ffffbb6ee000 0x2853fef7dfff7000

def z1124 : W := mkw 0xf803efebb8000000 0x00238f4bec000000

def z1125 : W := mkw 0x0000000000000000 0xb768080e3c0801e0

def z1126 : W := mkw 0x70f0903ed4911ff7 0x8304003ffc000fff

def z1127 : W := mkw 0x9080329490100480 0xbffc7ffffc780fe0

def z1128 : W := mkw 0xfc03ffffbac80940 0x3ffbfffffff80160

def z1129 : W := mkw 0xf8a3ffffb8324482 0xe7fbfffffc704093

def z1130 : W := mkw 0x4241852961858b18 0xcb978739e3878f1c

def z1131 : W := mkw 0xfc82faffbad80dc0 0xa34478fffc780fe0

def z1132 : W := mkw 0x4241852961858b18 0xffff8fffff8fff1c

def z1133 : W := mkw 0xfc83ffffbad80dc0 0xfffffffffff84ff3

def z1134 : W := mkw 0x78a0903fb8100482 0x0300003ffc000083

def z1135 : W := mkw 0xf802faffb8000000 0x037bf8fffc000000

def z1136 : W := mkw 0x9f036fc09b6ee000 0x7cfbffc01ffff000

def z1137 : W := mkw 0x4241852961858b18 0xdfbf87f9e387ff1c

def z1138 : W := mkw 0x6803cd6b28000000 0x02a38f4bec000000

def z1139 : W := mkw 0x4250802845859b3d 0xfd7f883e038fffff

def z1140 : W := mkw 0x4241852961858b18 0x8bbf8739e3870f1c

def z1141 : W := mkw 0xf803ffffb8800940 0x03fbfffffc000160

def z1142 : W := mkw 0x87036fc0036ee000 0xfffbffce3ffff11c

def z1143 : W := mkw 0x4241852961858b18 0xffff8fffff8f8ffc

def z1144 : W := mkw 0xf482fabe92d80dc0 0xbffffffffff80fe0

def z1145 : W := mkw 0xfe03ffffbb4c8000 0x7ffbffffffff8000

def z1146 : W := mkw 0xfc83ffffbad80dc0 0x33fbfffffff801e0

def z1147 : W := mkw 0x6482d83e02d80dc0 0x3877f83e03f80fe0

def z1148 : W := mkw 0x4241852961858b18 0xdfff8f3fe3878f1c

def z1149 : W := mkw 0xff03ffffbb6ee000 0x4bfbfffffff7f000

def z1150 : W := mkw 0xbc827ad69a5804c0 0xafdc7ef7dc780ee0

def z1151 : W := mkw 0xfb03ffffb926e000 0x77fbfffffc0ff000

def z1152 : W := mkw 0x90e03294d0334692 0x6edc76b1d0774e13

def z1153 : W := mkw 0xb0e03296d03346d2 0xefdc76b7d0774ef3

def z1154 : W := mkw 0x0482480002d80dc0 0xbd7ff80e03f80fe0

def z1155 : W := mkw 0xfd83ffffba7a64c0 0x23fbfffffc7870e0

def z1156 : W := mkw 0x4241852961858b18 0xcf9f8731e3878e1c

def z1157 : W := mkw 0x988137d5b8100480 0xafdc77f5fc700e80

def z1158 : W := mkw 0x7801953fb8000000 0x0313863ffc000000

def z1159 : W := mkw 0x830127c00126e000 0x7cfbf7c003f7f000

def z1160 : W := mkw 0xf803ffffb8000000 0xf7fbfffffc08f1e0

def z1161 : W := mkw 0x4241852961858b18 0xffff8ffdf38fff9f

def z1162 : W := mkw 0x980127c1b8000000 0x000006c1dc000000

def z1163 : W := mkw 0x6482d83e02d80dc0 0xfffff83e03f80ff0

def z1164 : W := mkw 0x87536fc047effb3d 0xfcffffc003ffffff

def z1165 : W := mkw 0xf803ffffb8000000 0x03bbff7bec000000

def z1166 : W := mkw 0xfc83ffffbad80dc0 0x3ffffffffff80e00

def z1167 : W := mkw 0x7800802bb8000000 0x0200000bfc000000

def z1168 : W := mkw 0xfa03ffffb9048000 0x43fbfffffc078000

def z1169 : W := mkw 0x17e35d54d35da692 0x93278975d388be93

def z1170 : W := mkw 0x9000228090224000 0x6ed87681d0774000

def z1171 : W := mkw 0x9b0137d5b926e000 0x6fd877f5fc77f000

def z1172 : W := mkw 0xff03ffffbb6ee000 0x2bfbffffffff7000

def z1173 : W := mkw 0xf803ffffb8000000 0x0013f63bec000000

def z1174 : W := mkw 0xb8e03296d8334692 0xefdc76b7dc774e93

def z1175 : W := mkw 0x6482d83e02d80dc0 0xfffff9fe13f8fff3

def z1176 : W := mkw 0x9000329490000000 0x03d876bffc000000

def z1177 : W := mkw 0x7800903fb8000000 0x8300003ffc000093

def z1178 : W := mkw 0x0010000004001025 0xe3c009ce3c08f1ff

def z1179 : W := mkw 0x87036fc0036ee000 0xfdfffff003fffe00

def z1180 : W := mkw 0x87036fc0036ee000 0x70e3ffc003fff000

def z1181 : W := mkw 0x6482d83e02d80dc0 0x3c7ff83603f80ee0

def z1182 : W := mkw 0x7800903fb8000000 0x00000037dc000000

def z1183 : W := mkw 0x990127c1b8226000 0x028007c1fc007000

def z1184 : W := mkw 0x6482c82a02d80dc0 0xbc7ff80a03f80fe0

def z1185 : W := mkw 0xfc83ffffba5804c0 0xb7fbfffffc7801e0

def z1186 : W := mkw 0xf883ffffb8900dc0 0x03fffffffc000e00

def z1187 : W := mkw 0x0010000004001025 0xfffc09fe3c08ffff

def z1188 : W := mkw 0xfc83ffffbad80dc0 0x1837ff7beff80f60

def z1189 : W := mkw 0x8060228040234212 0x4080068000074013

def z1190 : W := mkw 0xff03efebbb6ee000 0x52a38fcbff8ff000

def z1191 : W := mkw 0xf803ffffb8000000 0xf7fbfffffc0841f3

def z1192 : W := mkw 0x90e03294d0334692 0xef9c7631c0774e93

def z1193 : W := mkw 0xbc837fd7ba5804c0 0x22c07fc7fc7800e0

def z1194 : W := mkw 0x7c02d83fba480000 0x3f7bf83ffff80000

def z1195 : W := mkw 0x87036fc0036ee000 0x7cfbffca2ffff000

def z1196 : W := mkw 0x6482d83e02d80dc0 0xfd7ff83e03f84ff3

def z1197 : W := mkw 0xf883ffffb8900dc0 0xaffffffffc700fe0

def z1198 : W := mkw 0xf803ffffb8000000 0xf7fbfffffc0881fc

def z1199 : W := mkw 0xbf037fd69b6ee000 0x7ffbfff7dffff000

def z1200 : W := mkw 0x4040802840810b10 0xdfbf8739e3878f1c

def z1201 : W := mkw 0xf801b7ffb8000000 0x0300063ffc000000

def z1202 : W := mkw 0xf803ffffb8000000 0x017bff7fec000000

def z1203 : W := mkw 0x7801957fb8000000 0x0300017ffc000000

def z1204 : W := mkw 0x87036fc0036ee000 0xfffbffcc33fff19f

def z1205 : W := mkw 0x4241852961858b18 0xd3a78739e3878f1c

def z1206 : W := mkw 0x4000802920800900 0x9f3f8039e3800f00

def z1207 : W := mkw 0x4713cd6927ccb92d 0x1023894a2f88b16c

def z1208 : W := mkw 0xff03ffffbbcca940 0x13fbffffff88b160

def z1209 : W := mkw 0x7801953fb8000000 0x0380073ffc000000

def z1210 : W := mkw 0xf803ffffb8000000 0x37fbfffffc080000

def z1211 : W := mkw 0x90e03294d0334692 0x4bdc76b5d0774e13

def z1212 : W := mkw 0xb8027ad698000000 0x034078f7dc000000

def z1213 : W := mkw 0x87036fc0036ee000 0x7cfbffc61ffff000

def z1214 : W := mkw 0xbd027ad69a6a6000 0x6fd87ef7dc7f7000

def z1215 : W := mkw 0x0241050161058218 0xdfbf8731e3878e1c

def z1216 : W := mkw 0x7880903fb8900dc0 0x0304003ffc000e00

def z1217 : W := mkw 0xfc83ffffbad80dc0 0x8bfffffffff00fe0

def z1218 : W := mkw 0x87036fc0036ee000 0x7ffbffc413fff000

def z1219 : W := mkw 0xf803efebb8000000 0x03bb8ffbfc000000

def z1220 : W := mkw 0x4080903c00900d80 0xbd7ff83e03f80fe0

def z1221 : W := mkw 0x025000004505923d 0x400000000007f01f

def z1222 : W := mkw 0x980127c1b8000000 0x02000601fc000000

def z1223 : W := mkw 0xff03ffffbb4ca000 0x03fbffffff800000

def z1224 : W := mkw 0xf803ffffb8224000 0x23fbfffffc704000

def z1225 : W := mkw 0x434185696185ab18 0xdfbf8779e387bf1c

def z1226 : W := mkw 0x6482d83e02d80dc0 0xbc67f80e03f80fe0

def z1227 : W := mkw 0x6c83dd7f2ad80dc0 0xbfffff7feff80fe0

def z1228 : W := mkw 0x90e03294d0334692 0xfffc7ffffc7ffe93

def z1229 : W := mkw 0x90e03294d0334692 0x8bdc76b5d0770e93

def z1230 : W := mkw 0x7801953fb8000000 0x03fb8ffffc000000

def z1231 : W := mkw 0x87036fc0036ee000 0xfcfbffc003fff1e0

def z1232 : W := mkw 0xfc03ffffba480000 0x13fbffffff880000

def z1233 : W := mkw 0xf800b2ffb8000000 0x030000fffc000000

def z1234 : W := mkw 0x4801856928000000 0x03bb8779ec000000

def z1235 : W := mkw 0x87036fc0036ee000 0x0813fe4003ff3000

def z1236 : W := mkw 0xfca3ffffbafa4dc2 0xbffffffffff84fe3

def z1237 : W := mkw 0x90e03294d0334692 0xfffc7fffd07ffff3

def z1238 : W := mkw 0x9b0127c1b904a000 0x028007c1fc00b000

def z1239 : W := mkw 0x87036fc0036ee000 0x3873ffc003fff000

def z1240 : W := mkw 0x7800903fb8000000 0x038001fffc000000

def z1241 : W := mkw 0x4241852961858b18 0xffff8fbff38fcfff

def z1242 : W := mkw 0xf803ffffb8000000 0x57fbfffffc008000

def z1243 : W := mkw 0x6482d83e02d80dc0 0x9937f83e03f80fe0

def z1244 : W := mkw 0x0250000045859b3d 0xdc04000003878fff

def z1245 : W := mkw 0x6482d83e02d80dc0 0x8817f03003f00fe0

def z1246 : W := mkw 0x87036fc0036ee000 0xfffbffc003fff010

def z1247 : W := mkw 0xfa03ffffb9048000 0x0bfbffffff870000

def z1248 : W := mkw 0x6482d83e02d80dc0 0xbd17f03e03f80fe0

def z1249 : W := mkw 0xf883ffffb8324480 0xeffffffffc774e80

def z1250 : W := mkw 0x00c0101440110690 0xefdc76b5d0774e93

def z1251 : W := mkw 0xb8037fd7b8000000 0x00407ec7dc000000

def z1252 : W := mkw 0x18001015b8000000 0x03000035fc000000

def z1253 : W := mkw 0xfc03ffffba480000 0xbffbfffffff801e0

def z1254 : W := mkw 0xf803ffffb8000000 0x0013f771ec000000

def z1255 : W := mkw 0x87036fc0036ee000 0x6cdbfec003ff7000

def z1256 : W := mkw 0x18000001b8000000 0x028001c1fc000000

def z1257 : W := mkw 0xff03ffffbbcca908 0x13fbffffff88b10c

def z1258 : W := mkw 0x6803cd6b28000000 0x0323897bec000000

def z1259 : W := mkw 0xfc83ffffbad80dc0 0x2857fef7dff80ee0

def z1260 : W := mkw 0x4241852961858b18 0x18178631c3878f0c

def z1261 : W := mkw 0x7800903fb8000000 0x0000003bec000000

def z1262 : W := mkw 0x4241852961858b18 0xffff8f39e38f8f1c

def z1263 : W := mkw 0xff03ffffbb6ee000 0x53fbffffff8ff000

def z1264 : W := mkw 0xfb03ffffb926e000 0x5ffbffffff87f000

def z1265 : W := mkw 0xff83ffffbbdcadc0 0xbffffffffff8bfe0

def z1266 : W := mkw 0x90e03294d0334692 0x6cdc76b5d0774e83

def z1267 : W := mkw 0x60d0903f64911ffd 0x8304003ffc000fff

def z1268 : W := mkw 0xf803ffffb8000000 0x83fbfffffc0001e0

def z1269 : W := mkw 0x0241050041058218 0x408007000007801c

def z1270 : W := mkw 0x90e03294d0334692 0x6ad476b5d0774e93

def z1271 : W := mkw 0x64f2d83e46fb5ff7 0xfd7ff83e03ffffff

def z1272 : W := mkw 0x9a0127c1b9048000 0x5ebb87c1ff878000

def z1273 : W := mkw 0x7800903fb8000000 0x8300003ffc00011c

def z1274 : W := mkw 0x87036fc0036ee000 0x7cfbffca03fff160

def z1275 : W := mkw 0x90e03294d0334692 0xcf9c7635d0770e93

def z1276 : W := mkw 0x4241852961858b18 0xdfff87bdf3878f1c

def z1277 : W := mkw 0x90e03294d0334692 0x28147631c0774e83

def z1278 : W := mkw 0x87036fc0036ee000 0x7cfbffc413fff083

def z1279 : W := mkw 0x4241852961858b18 0xfffff739e3f78f1c

def z1280 : W := mkw 0x38001017b8000000 0x02000007fc000000

def z1281 : W := mkw 0x6803dd7f28000000 0x03fbff7fec000000

def z1282 : W := mkw 0xfa03ffffb9048008 0x03fbfffffc00800c

def z1283 : W := mkw 0xb8037fd698000000 0x03fbfff7dc000000

def z1284 : W := mkw 0x6003dd3f20000000 0x03fbfffffc000000

def z1285 : W := mkw 0xff03ffffbb6ee000 0xfffbfffffffff1e0

def z1286 : W := mkw 0x9000329490000000 0x03d877f5fc000000

def z1287 : W := mkw 0x937127c0d527f237 0x428007c1fc07f01f

def z1288 : W := mkw 0x87036fc0036ee000 0x7c63f9c003fff000

def z1289 : W := mkw 0x87036fc0036ee000 0x7ffbffc823fff000

def z1290 : W := mkw 0x6482d83e02d80dc0 0x297ff83e03f80ee0

def z1291 : W := mkw 0x97037fd4936ee000 0x7ffbfffffffff000

def z1292 : W := mkw 0x0251050045859b3d 0xfcff8fc0038fffff

def z1293 : W := mkw 0x6f03cd6b2b4ca000 0x5fbb8f7bef8fb000

def z1294 : W := mkw 0x7800903fb8000000 0x0320097ffc000000

def z1295 : W := mkw 0x9d036fc1ba6a6000 0x22c07fc1fc787000

def z1296 : W := mkw 0xff03ffffbb6ee000 0x33fbfffffff8f000

def z1297 : W := mkw 0xf802faffb8000000 0x03e879fffc000000

def z1298 : W := mkw 0xfd83ffffbafa6dc0 0xbffffffffff87fe0

def z1299 : W := mkw 0x6482d83e02d80dc0 0xbf7ff83e13f80ff3

def z1300 : W := mkw 0xf801b7ffb8000000 0x03bb87fffc000000

def z1301 : W := mkw 0xff83ffffbbfeedc0 0x0bfffffffff70e00

def z1302 : W := mkw 0x7800903fb8000000 0x0358703ffc000000

def z1303 : W := mkw 0x4241852961858b18 0xdcbf8731c3878f1c

def z1304 : W := mkw 0x87036fc0036ee000 0x7c93f7c003fff000

def z1305 : W := mkw 0xfa03ffffb9848900 0xdfffffffff878f00

def z1306 : W := mkw 0x87036fc0036ee000 0xfcfbffc003fff093

def z1307 : W := mkw 0x9f037fd5bb6ee000 0x7ffbfff5fffff000

def z1308 : W := mkw 0xb8027ad698000000 0x03f87ffffc000000

def z1309 : W := mkw 0x98036fc1b8000000 0x02a38fc1fc000000

def z1310 : W := mkw 0x6482d83e02d80dc0 0x9d3ff03e03f00fe0

def z1311 : W := mkw 0xf803ffffb8000000 0x02b3fffbfc000000

def z1312 : W := mkw 0xf803ffffb8000000 0x23fbfffffc087000

def z1313 : W := mkw 0xff83ffffbb7ee480 0xfffffffffffffe80

def z1314 : W := mkw 0x1080101490100480 0xaf5c7035d0700e80

def z1315 : W := mkw 0xf802fabfb8000000 0x03fbfebffc000000

def z1316 : W := mkw 0xf803ffffb8000000 0x03dbf6bffc000000

def z1317 : W := mkw 0xdb01a7e9b926e000 0x5fbb87f9ff87f000

def z1318 : W := mkw 0xe803efeb28000000 0x03fbfffbec000000

def z1319 : W := mkw 0x4000802920000000 0x03e809fffc000000

def z1320 : W := mkw 0xf800b2bfb8000000 0x034070bffc000000

def z1321 : W := mkw 0x4241852961858b18 0x9b378739e3878f1c

def z1322 : W := mkw 0x02f0000045b7dfbf 0xfc04000003ffffff

def z1323 : W := mkw 0xf803efebb8000000 0x028387c1fc000000

def z1324 : W := mkw 0xf803ffffb8000000 0x1ffbffffff800000

def z1325 : W := mkw 0xfc03ffffba480000 0x7ffbfffffff8f000

def z1326 : W := mkw 0x7880903fb81004c0 0x0300003ffc0000e0

def z1327 : W := mkw 0x87036fc0036ee000 0xfdfbffc803fff100

def z1328 : W := mkw 0x90e03294d0334692 0xffdc76b5d07ffe93

def z1329 : W := mkw 0xf803ffffb8000000 0x03bbf7f9fc000000

def z1330 : W := mkw 0xf803ffffb8000000 0x0013f637dc000000

def z1331 : W := mkw 0x90e03294d0334692 0x0a147631d0770e13

def z1332 : W := mkw 0xff03ffffbb6ee000 0x3ffbffffffff0000

def z1333 : W := mkw 0xef03efeb2b6ee000 0x7ffbfffbeffff000

def z1334 : W := mkw 0xfc83ffffbad80dc0 0xbd7ffeffdff80fe0

def z1335 : W := mkw 0x87036fc0036ee000 0x7cdbf68003fff000

def z1336 : W := mkw 0xf802fafe98000000 0x03fbfeffdc000000

def z1337 : W := mkw 0x980127c1b8000000 0x02d877c1fc000000

def z1338 : W := mkw 0x00f00000441116b7 0xf40400000008ffff

def z1339 : W := mkw 0x6582d87e02d82dc0 0xbd7ff87e03f83fe0

def z1340 : W := mkw 0x835127c16527f23d 0x428007c1fc07f01f

def z1341 : W := mkw 0x10e01014d0110692 0xefdc7635d0770e93

def z1342 : W := mkw 0xf803ffffb8000000 0x0393f7fffc000000

def z1343 : W := mkw 0x98a137d5b8324482 0x22c077c5fc704083

def z1344 : W := mkw 0xf803ffffb8800900 0x0bffffffff800e00

def z1345 : W := mkw 0x7c82d83fba5804c0 0x2340783ffc7800e0

def z1346 : W := mkw 0xb4b27a96967a54e7 0x204078c61c7870e3

def z1347 : W := mkw 0xf803ffffb8000000 0x43fbfffffc00f000

def z1348 : W := mkw 0x7800903fb8000000 0x0398063ffc000000

def z1349 : W := mkw 0x18010501b8000000 0x02800701fc000000

def z1350 : W := mkw 0x6482d83e02d80dc0 0x0817f03603f00ee0

def z1351 : W := mkw 0xfb03ffffb926e000 0x03fbfffffc070000

def z1352 : W := mkw 0x18000001b8000000 0x03e809cffc000000

def z1353 : W := mkw 0xf803ffffb8000000 0x0073fffffc000000

def z1354 : W := mkw 0x87036fc0036ee000 0x7c33ff4003fff000

def z1355 : W := mkw 0xff03ffffbb6ee000 0x63fbfffffc7ff000

def z1356 : W := mkw 0x74a2d83e92d80dc2 0xbd7ff83e13f80fe3

def z1357 : W := mkw 0x90e03294d0334692 0xfffc7ffdf07fff9f

def z1358 : W := mkw 0x87036fc0036ee000 0x7efbffc023fff01c

def z1359 : W := mkw 0x4241852961858b18 0x5ab78739e3878f1c

def z1360 : W := mkw 0x9f136fc1bf6ef025 0xfffbffcffffff1ff

def z1361 : W := mkw 0x80e0228040334692 0xefdc76b1c0774e93

def z1362 : W := mkw 0x90e03294d0334692 0x2bdc76b5d0774e83

def z1363 : W := mkw 0x87036fc0036ee000 0x58b3ffc003fff000

def z1364 : W := mkw 0xff03ffffbb6ee000 0x5ffbfffffff78000

def z1365 : W := mkw 0xf803ffffb8224000 0xeffbfffffc774093

def z1366 : W := mkw 0xf803ffffb8000000 0x13fbfffffc00810c

def z1367 : W := mkw 0xfc83ffffba5804c0 0x03fbfffffc700000

def z1368 : W := mkw 0x87036fc0036ee000 0x2813f60003ff7000

def z1369 : W := mkw 0xfda3ffffba7a6482 0x23fbfffffc787083

def z1370 : W := mkw 0x4201852921048000 0x7ffb8fffff8ff000

def z1371 : W := mkw 0xf803efebb8000000 0x03eb8fcffc000000

def z1372 : W := mkw 0x9d026ac09a6a6000 0x204078c01c787000

def z1373 : W := mkw 0xf803ffffb8000000 0x43fbfffffc004013

def z1374 : W := mkw 0xf803ffffb8000000 0x02e3ffcffc000000

def z1375 : W := mkw 0xf803ffffb8000000 0x8ffffffffc000e00

def z1376 : W := mkw 0x4241852961858b18 0xffff8fffe38ffffc

def z1377 : W := mkw 0x9f036fc1bb4ca000 0x12a38fc1ff88b000

def z1378 : W := mkw 0xfc83ffffbad80dc0 0x0a97f7f1fff00e00

def z1379 : W := mkw 0x7880903fb8100480 0x8304003ffc000e80

def z1380 : W := mkw 0x7880903fb8100480 0xaf5c703ffc700e80

def z1381 : W := mkw 0xfc83ffffba580480 0xbffffffffff80e80

def z1382 : W := mkw 0xf800b2bfb8000000 0x0310763ffc000000

def z1383 : W := mkw 0xf803ffffb8000000 0x43fbfffffc00801c

def z1384 : W := mkw 0xf002fabe90000000 0x03fbfffffc000000

def z1385 : W := mkw 0x87036fc0036ee000 0x3c7bff4003ffb000

def z1386 : W := mkw 0x6483dd3f22d80dc0 0xbffffffffff80fe0

def z1387 : W := mkw 0x7801953fb8000000 0x0323813ffc000000

def z1388 : W := mkw 0x98037fd5b8000000 0x03fbfff5fc000000

def z1389 : W := mkw 0x6482d83e02d80dc0 0x197ff83e03f80f60

def z1390 : W := mkw 0x58008029b8000000 0x03000039fc000000

def z1391 : W := mkw 0xf803ffffb8000000 0x4ffbfffffc070000

def z1392 : W := mkw 0x6482d83f22d80dc8 0xbd7ff83e23f80fec

def z1393 : W := mkw 0x0010000004001025 0xf7f80ffffc08f1ff

def z1394 : W := mkw 0x4241852961858b18 0x5ebf8731e3878e1c

def z1395 : W := mkw 0xff03ffffbb6ee000 0x7efbfff1fffff000

def z1396 : W := mkw 0xf801b7bfb8000000 0x03fbf7bffc000000

def z1397 : W := mkw 0x9000329490224000 0x7ff87ffffc7ff000

def z1398 : W := mkw 0x90e03294d0334692 0xefdc7ef5d07f7e93

def z1399 : W := mkw 0x4241852961858b18 0xffff873de3878f9c

def z1400 : W := mkw 0x7800903fb8800908 0x0300003ffc00010c

def z1401 : W := mkw 0x90602280d0234212 0xefdc76b1d0774e13

def z1402 : W := mkw 0x7800903fb8000000 0x77e809fffc08f000

def z1403 : W := mkw 0x6080903e00900dc0 0xbd7ff03e03f00fe0

def z1404 : W := mkw 0xf883ffffb8100480 0x83fffffffc000e80

def z1405 : W := mkw 0x85026ac0026a6000 0x7cfbfec003ff7000

def z1406 : W := mkw 0xf803ffffb8000000 0x0353fefffc000000

def z1407 : W := mkw 0x6803cd6b28000000 0x03fb8ffffc000000

def z1408 : W := mkw 0x980127c1b8000000 0xe7c807c5fc004093

def z1409 : W := mkw 0xf803ffffb8000000 0xf7fbfffffc08f093

def z1410 : W := mkw 0x87036fc0036ee000 0xfcfbffc003fff11c

def z1411 : W := mkw 0x8040228040234210 0xefdc76b5d0774e93

def z1412 : W := mkw 0x4000802920000000 0x0300003ffc000000

def z1413 : W := mkw 0xf803ffffb8000000 0x03dbf7f5fc000000

def z1414 : W := mkw 0x87036fc0036ee000 0x0813f6c003f77000

def z1415 : W := mkw 0xfc03ffffbac80940 0xb7fbffffff8801e0

def z1416 : W := mkw 0xfc83ffffbad80dc0 0x1bfffffffff80f60

def z1417 : W := mkw 0x87036fc0036ee000 0x1813f60003ffb000

def z1418 : W := mkw 0xfc03ffffba480000 0x23fbfffffc780000

def z1419 : W := mkw 0xb8027ad7b8000000 0x024078c7fc000000

def z1420 : W := mkw 0x0050000044811b3d 0x8004000000000fff

def z1421 : W := mkw 0xf800b2bfb8000000 0x038006bffc000000

def z1422 : W := mkw 0x0010000004001025 0xfff80fce3c0ff1ff

def z1423 : W := mkw 0xf883ffffb8100480 0xeffffffffc704e93

def z1424 : W := mkw 0x0010000004001025 0xfffb89ce3f88f1ff

def z1425 : W := mkw 0x7800903fb8000000 0x033b803ffc000000

def z1426 : W := mkw 0x66d2d83e47dd9ffd 0xfd7ff83e03ffffff

def z1427 : W := mkw 0xfa03ffffb9048000 0xdffbffffff87811c

def z1428 : W := mkw 0xd803efe9b8000000 0x03fbfff9fc000000

def z1429 : W := mkw 0x6402c82a02c80940 0xbd7ff83a03f80f60

def z1430 : W := mkw 0xd801a7e9b8000000 0x02a387c9fc000000

def z1431 : W := mkw 0x87036fc0036ee000 0x28fbffc003ff7000

def z1432 : W := mkw 0x06d0000047dd9ffd 0xfc04000003ffffff

def z1433 : W := mkw 0x6a43cd6b69858b18 0xdc27894a2f878f1c

def z1434 : W := mkw 0x98036fc1b8000000 0x03fbffcffc000000

def z1435 : W := mkw 0xdf03efe9bb6ee000 0x7ffbfff9fffff000

def z1436 : W := mkw 0x0050000044011235 0xfc040000000fffff

def z1437 : W := mkw 0x87036fc0036ee000 0x7cfbffc823fff10c

def z1438 : W := mkw 0x4001852920000000 0x03bb8f7bec000000

def z1439 : W := mkw 0x9b0127c1b926e000 0x77e80fcffc0ff000

def z1440 : W := mkw 0x6482d83e02d80dc0 0xbdfff9fe03f80fe0

def z1441 : W := mkw 0x980127c1b8224000 0x428007c1fc074000

def z1442 : W := mkw 0xd801a7e9b8000000 0x029387f1fc000000

def z1443 : W := mkw 0x90e03294d0334692 0x08147635d0770e83

def z1444 : W := mkw 0xfb03ffffb926e000 0x6ffbfffffc77f000

def z1445 : W := mkw 0x4241852961858b18 0xffff8fffff87cf9f

def z1446 : W := mkw 0x4241852961858b18 0x08178731e3878e0c

def z1447 : W := mkw 0x6482d83e02d80dc0 0xbc37f83a03f80fe0

def z1448 : W := mkw 0x7c82d83fbad80dc0 0x0b17f03ffff00e00

def z1449 : W := mkw 0x6482d83e02d80dc0 0x2817f03003f80ee0

def z1450 : W := mkw 0x4241852961858b18 0x0a178631e3870e1c

def z1451 : W := mkw 0xf803ffffb8000000 0x0013fe73cc000000

def z1452 : W := mkw 0x4241852961858b18 0xdc378739e3878f1c

def z1453 : W := mkw 0x9f036fc1bb6ee000 0x7cfbffc1c3fff000

def z1454 : W := mkw 0xfc03ffffba480040 0x03fbfffffc080060

def z1455 : W := mkw 0x87036fc0036ee000 0x68d3ffc003fff000

def z1456 : W := mkw 0x87036fc0036ee000 0xfffbffce23fff1fc

def z1457 : W := mkw 0xf803ffffb8000000 0x02fbfff1fc000000

def z1458 : W := mkw 0xfc83ffffbad80dc0 0xbf7ffe3ffff80fe0

def z1459 : W := mkw 0x7880903fb8900dc0 0xb7ec09fffc080fe0

def z1460 : W := mkw 0x07034d40034ca000 0x7cfbff4003ffb000

def z1461 : W := mkw 0x4001852920800900 0xbfff8fffff880fe0

def z1462 : W := mkw 0x95b27ad4967a74a7 0x204078c61c7870e3

def z1463 : W := mkw 0xf823ffffb8224002 0x03fbfffffc004003

def z1464 : W := mkw 0x980022c1b8000000 0x020000c1fc000000

def z1465 : W := mkw 0xf803ffffb8000000 0x02d3fff7fc000000

def z1466 : W := mkw 0x06034d00034c8000 0x7cfbffc003fff000

def z1467 : W := mkw 0xf803ffffb8000000 0x13fbfffffc080160

def z1468 : W := mkw 0x90e03294d0334692 0xefdc77f5d077fe93

def z1469 : W := mkw 0xb8037fd7b8000000 0x02fbffc7fc000000

def z1470 : W := mkw 0x90e03294d0334692 0xec5476b5d0774e93

def z1471 : W := mkw 0x90e03294d0334692 0xeffc7ebfd0774e93

def z1472 : W := mkw 0x87036fc0036ee000 0x18fbffc003ffb000

def z1473 : W := mkw 0x0010000004001025 0xb36009ce3c08f1ff

def z1474 : W := mkw 0x980137d5b8000000 0x038007f5fc000000

def z1475 : W := mkw 0xd801a7e9b8000000 0x03fb8ffffc000000

def z1476 : W := mkw 0xa7036fc2036ee040 0x7cfbffc203fff060

def z1477 : W := mkw 0x0750000047effb3d 0xfc04000003ffffff

def z1478 : W := mkw 0x98036fc1b8000000 0x0293f7c1fc000000

def z1479 : W := mkw 0x84026a80026a4000 0x7cfbffc003fff000

def z1480 : W := mkw 0xbf037fd7bb6ee000 0x7efbffc7fffff000

def z1481 : W := mkw 0x4040802840810b18 0x8104003800000f1c

def z1482 : W := mkw 0x50f0903df4911fbf 0x8304003ffc000fff

def z1483 : W := mkw 0xff83ffffbb7ee4c0 0x7ffbfffffffff0e0

def z1484 : W := mkw 0x97236fc0936ee002 0x7cfbffc013fff003

def z1485 : W := mkw 0xf803ffffb8000000 0x23fbfffffc004083

def z1486 : W := mkw 0x4241852961858b18 0xffbf8739e38fff1c

def z1487 : W := mkw 0x58018529b8000000 0x03bb8739fc000000

def z1488 : W := mkw 0x4241852961858b18 0xcf9f8639e3870f1c

def z1489 : W := mkw 0xff03ffffbb6ee000 0x7cfbfffbeffff000

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkA : List (List (List (ℕ × List W))) :=
  [[[(1,[z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z6,z7,z5]),(0,[z8,z0,z1,z2,z3,z9,z7]),(0,[z0,z1,z10,z2,z3,z7,z5]),(0,[z0,z11,z1,z12,z3,z7,z5]),(0,[z13,z0,z1,z2,z3,z7,z14])],[(0,[z15,z0,z1,z2,z16,z3,z7]),(0,[z0,z17,z1,z2,z18,z7,z5]),(0,[z0,z1,z19,z2,z3,z20,z5]),(0,[z0,z21,z1,z2,z3,z7,z5])],[(1,[z0,z1,z22,z3,z7,z5]),(0,[z15,z0,z1,z23,z3,z7,z5]),(0,[z0,z24,z1,z2,z3,z7,z25]),(0,[z0,z26,z1,z2,z3,z7,z5]),(0,[z0,z17,z1,z2,z16,z3,z7]),(0,[z0,z27,z1,z2,z28,z3,z7])],[(0,[z0,z29,z1,z2,z3,z7,z5]),(0,[z0,z1,z2,z30,z16,z3,z7]),(0,[z0,z1,z2,z3,z7,z5,z31]),(0,[z32,z0,z1,z2,z3,z7,z14]),(0,[z0,z1,z2,z33,z3,z7,z5]),(0,[z0,z1,z2,z3,z7,z34,z35]),(0,[z0,z1,z2,z36,z3,z7,z5]),(0,[z0,z1,z37,z2,z3,z7,z34])],[(0,[z0,z1,z38,z2,z3,z7,z39]),(0,[z0,z1,z2,z40,z3,z7,z34]),(0,[z0,z1,z2,z41,z3,z7,z5]),(0,[z0,z1,z2,z42,z3,z7,z5]),(0,[z0,z43,z1,z2,z3,z7,z5]),(0,[z0,z1,z2,z3,z7,z5,z44]),(0,[z0,z1,z2,z18,z3,z7,z39]),(0,[z0,z45,z1,z2,z3,z7,z46]),(0,[z0,z1,z2,z3,z7,z47,z5]),(0,[z0,z48,z1,z2,z16,z3,z7])],[(0,[z0,z1,z2,z49,z3,z7,z5]),(0,[z0,z1,z2,z3,z7,z50,z5]),(0,[z0,z1,z2,z3,z7,z34,z51])],[(0,[z0,z52,z2,z3,z7,z5,z53]),(0,[z0,z52,z1,z2,z3,z7,z34]),(0,[z54,z0,z1,z2,z16,z3,z7]),(0,[z55,z0,z1,z2,z3,z7,z39]),(0,[z8,z0,z1,z2,z3,z7,z56]),(0,[z0,z1,z2,z3,z7,z56,z53]),(0,[z0,z1,z57,z2,z3,z7,z5]),(0,[z0,z58,z1,z2,z3,z7,z5])],[(0,[z59,z0,z1,z2,z3,z7,z5]),(0,[z60,z0,z1,z2,z3,z7,z5])]],
   [[(0,[z0,z1,z2,z3,z7,z61,z5]),(0,[z0,z1,z2,z18,z62,z7,z5]),(0,[z0,z63,z1,z2,z3,z7,z5]),(0,[z0,z1,z2,z3,z7,z64,z5]),(0,[z0,z65,z1,z2,z3,z7,z34]),(0,[z0,z1,z12,z2,z3,z7,z66]),(0,[z0,z1,z2,z67,z3,z7,z14]),(0,[z0,z1,z68,z2,z3,z7,z5])],[(0,[z69,z0,z1,z2,z3,z7,z5]),(0,[z54,z0,z1,z70,z3,z7,z5]),(0,[z0,z1,z2,z62,z7,z71,z5]),(0,[z0,z72,z1,z2,z3,z7,z5]),(0,[z0,z1,z2,z16,z3,z7,z73]),(0,[z0,z11,z1,z2,z16,z3,z7]),(0,[z0,z1,z37,z2,z3,z7,z5])],[(0,[z74,z0,z1,z2,z3,z7,z5]),(0,[z0,z27,z1,z2,z16,z3,z7])],[(0,[z0,z75,z1,z2,z3,z7,z5]),(0,[z0,z1,z2,z3,z76,z7,z5]),(0,[z0,z11,z1,z2,z7,z71,z5])],[(0,[z0,z52,z1,z2,z3,z7,z5]),(0,[z0,z1,z2,z77,z3,z7,z5]),(0,[z0,z78,z1,z2,z18,z7,z5]),(0,[z0,z1,z2,z16,z3,z7,z20]),(1,[z0,z1,z19,z3,z79,z5])],[(0,[z80,z0,z1,z2,z3,z7,z39]),(0,[z0,z1,z2,z3,z7,z39,z81]),(0,[z0,z1,z2,z7,z34,z82,z5])],[(0,[z83,z0,z1,z2,z84,z7,z5]),(0,[z85,z0,z1,z22,z3,z7,z5]),(0,[z0,z65,z1,z2,z3,z7,z5]),(0,[z0,z1,z2,z3,z7,z5,z86]),(0,[z0,z27,z87,z2,z3,z7,z5]),(0,[z0,z1,z2,z3,z9,z7,z53]),(1,[z0,z1,z2,z3,z7,z88]),(0,[z0,z11,z89,z1,z3,z7,z5])],[(0,[z90,z0,z1,z2,z3,z7,z5]),(0,[z0,z89,z1,z30,z3,z7,z5]),(0,[z0,z91,z1,z2,z40,z7,z5]),(1,[z0,z1,z2,z3,z7,z92]),(0,[z0,z93,z1,z2,z3,z7,z5]),(0,[z0,z1,z2,z3,z94,z7,z5]),(0,[z0,z1,z2,z3,z7,z95,z5]),(1,[z0,z1,z3,z7,z34,z39]),(0,[z0,z1,z2,z3,z7,z39,z14])]],
   [[(1,[z0,z96,z2,z3,z7,z5]),(0,[z85,z0,z1,z2,z3,z97,z5]),(0,[z0,z1,z2,z98,z3,z7,z5]),(0,[z0,z99,z1,z2,z3,z7,z5]),(0,[z100,z0,z1,z2,z3,z7,z5]),(0,[z101,z0,z1,z2,z3,z7,z5])],[(0,[z0,z102,z1,z2,z3,z7,z5]),(0,[z0,z27,z52,z2,z3,z7,z5]),(0,[z103,z0,z1,z2,z3,z7,z5]),(0,[z0,z1,z37,z2,z3,z7,z14])],[(0,[z0,z1,z2,z3,z7,z104,z5]),(1,[z0,z1,z2,z3,z105,z5]),(0,[z0,z1,z2,z40,z3,z7,z14]),(0,[z55,z0,z1,z2,z3,z7,z56]),(0,[z0,z1,z2,z3,z7,z5,z106]),(0,[z0,z1,z2,z107,z16,z3,z7])],[(0,[z85,z1,z2,z3,z62,z7,z5]),(0,[z0,z108,z1,z2,z3,z7,z5]),(0,[z0,z109,z1,z2,z3,z7,z5]),(1,[z0,z1,z2,z3,z7,z110])],[(0,[z0,z1,z2,z111,z3,z7,z5]),(0,[z0,z78,z52,z2,z3,z7,z5]),(0,[z0,z52,z1,z2,z3,z7,z14]),(1,[z0,z1,z2,z112,z7,z5]),(0,[z113,z0,z1,z2,z3,z7,z5]),(0,[z0,z1,z2,z114,z62,z7,z5]),(0,[z0,z1,z115,z2,z3,z7,z5])],[(0,[z116,z0,z1,z2,z77,z7,z5]),(1,[z0,z1,z2,z117,z7,z5]),(0,[z0,z1,z2,z3,z7,z118,z5]),(0,[z0,z1,z2,z3,z7,z119,z5]),(0,[z0,z1,z2,z16,z3,z7,z53])],[(0,[z116,z0,z1,z2,z3,z4,z5]),(0,[z0,z120,z38,z2,z3,z7,z5]),(0,[z0,z121,z1,z2,z3,z7,z5]),(0,[z0,z65,z1,z2,z3,z7,z14]),(0,[z0,z1,z2,z16,z122,z3,z7])],[(1,[z83,z1,z30,z3,z7,z5]),(0,[z0,z123,z1,z2,z3,z7,z5]),(0,[z0,z1,z2,z16,z3,z7,z71]),(0,[z0,z124,z1,z2,z3,z7,z5])]],
   [[(0,[z0,z1,z2,z3,z7,z5,z125]),(0,[z0,z1,z2,z3,z126,z7,z5])],[(0,[z0,z1,z2,z127,z3,z7,z5]),(0,[z0,z128,z1,z2,z3,z7,z5]),(0,[z0,z1,z2,z3,z129,z7,z5]),(0,[z130,z0,z1,z2,z3,z7,z5]),(0,[z0,z1,z2,z131,z3,z7,z5])],[(0,[z83,z0,z1,z2,z3,z7,z132]),(0,[z8,z0,z1,z2,z3,z7,z133]),(0,[z0,z134,z1,z2,z3,z7,z5]),(0,[z0,z135,z1,z2,z3,z7,z5]),(0,[z0,z1,z37,z3,z7,z5,z39]),(0,[z0,z1,z2,z136,z3,z7,z5]),(0,[z0,z91,z1,z2,z16,z3,z7])],[(0,[z0,z1,z2,z3,z7,z71,z39])],[(1,[z0,z1,z2,z3,z7,z31]),(0,[z0,z1,z2,z3,z7,z5,z133]),(0,[z0,z120,z24,z2,z3,z7,z5]),(0,[z0,z1,z2,z137,z3,z7,z5]),(0,[z0,z138,z1,z2,z16,z3,z7]),(0,[z0,z1,z3,z7,z34,z5,z39]),(0,[z0,z1,z2,z3,z7,z139,z5]),(0,[z0,z1,z2,z140,z3,z7,z5])],[(0,[z141,z52,z1,z2,z3,z7,z5]),(1,[z0,z1,z2,z3,z142,z5]),(0,[z0,z1,z2,z3,z7,z143,z5]),(0,[z0,z1,z2,z3,z7,z35,z5]),(0,[z0,z1,z12,z2,z3,z7,z14]),(0,[z0,z1,z2,z3,z7,z5,z144])],[(0,[z0,z1,z2,z145,z3,z7,z5]),(0,[z146,z0,z1,z2,z3,z7,z5]),(0,[z0,z87,z2,z3,z7,z5,z53]),(0,[z0,z87,z1,z2,z3,z7,z34]),(2,[z0,z1,z147,z3,z7]),(0,[z0,z1,z2,z122,z3,z7,z5])],[(0,[z32,z1,z2,z3,z148,z7,z5]),(0,[z149,z0,z1,z2,z3,z7,z5]),(0,[z0,z1,z2,z150,z114,z3,z7]),(1,[z0,z1,z2,z16,z3,z7]),(0,[z151,z0,z1,z2,z3,z7,z5])]],
   [[(0,[z85,z0,z1,z2,z40,z7,z5]),(1,[z0,z1,z23,z3,z7,z5]),(0,[z0,z1,z2,z3,z7,z152,z5]),(0,[z0,z153,z1,z2,z3,z7,z5]),(0,[z0,z154,z1,z2,z3,z7,z5])],[(0,[z0,z45,z1,z2,z40,z7,z5]),(0,[z0,z155,z1,z2,z3,z7,z5]),(0,[z0,z156,z1,z2,z3,z7,z5]),(0,[z0,z157,z1,z2,z3,z7,z34])],[(0,[z0,z1,z2,z3,z7,z5,z158]),(1,[z0,z1,z159,z3,z7,z5]),(0,[z113,z0,z1,z2,z3,z7,z39]),(1,[z0,z1,z37,z3,z7,z39])],[(0,[z0,z1,z2,z16,z3,z160,z7]),(0,[z0,z1,z161,z2,z3,z7,z5])],[(0,[z0,z24,z1,z162,z3,z7,z5]),(0,[z0,z1,z2,z3,z163,z7,z5]),(0,[z0,z87,z1,z2,z3,z7,z5])],[(0,[z54,z0,z1,z30,z3,z7,z5]),(0,[z0,z1,z2,z3,z7,z164,z5]),(0,[z113,z1,z2,z40,z3,z7,z5]),(1,[z15,z1,z2,z3,z165,z5]),(1,[z0,z1,z166,z3,z7,z5]),(0,[z0,z1,z2,z3,z7,z167,z5]),(0,[z0,z168,z1,z2,z3,z7,z5])],[(0,[z113,z0,z1,z2,z62,z7,z5]),(0,[z55,z0,z1,z2,z3,z7,z133]),(0,[z0,z78,z1,z2,z3,z7,z34]),(0,[z0,z1,z2,z28,z3,z7,z39])],[(0,[z0,z1,z70,z2,z16,z3,z7]),(0,[z0,z1,z2,z28,z3,z5,z51])]],
   [[(1,[z0,z1,z12,z2,z7,z14]),(0,[z0,z1,z2,z16,z16,z3,z7]),(1,[z0,z1,z2,z3,z9,z51])],[(0,[z0,z17,z1,z2,z3,z7,z14]),(0,[z0,z169,z1,z2,z3,z7,z5]),(0,[z0,z1,z170,z2,z3,z7,z5]),(0,[z0,z1,z2,z16,z171,z3,z7])],[(0,[z172,z0,z1,z2,z3,z7,z5]),(0,[z0,z1,z2,z30,z3,z7,z14]),(0,[z0,z1,z2,z3,z3,z7,z5]),(0,[z0,z1,z2,z3,z148,z73,z5]),(0,[z0,z1,z2,z3,z7,z39,z173]),(0,[z0,z174,z1,z2,z3,z7,z39]),(0,[z0,z175,z1,z2,z3,z7,z34]),(0,[z0,z1,z2,z3,z7,z176,z14]),(0,[z0,z177,z1,z2,z3,z7,z5])],[(0,[z0,z1,z2,z3,z178,z7,z5]),(0,[z85,z0,z1,z2,z16,z3,z7]),(0,[z179,z0,z1,z2,z3,z7,z5]),(0,[z0,z1,z2,z3,z148,z7,z39]),(1,[z0,z1,z2,z3,z7,z106]),(0,[z0,z1,z2,z3,z7,z35,z39]),(0,[z0,z180,z1,z2,z3,z7,z5]),(0,[z181,z0,z1,z2,z3,z7,z14])],[(0,[z0,z182,z1,z2,z3,z7,z5]),(0,[z0,z1,z2,z3,z148,z5,z51]),(0,[z0,z1,z2,z3,z7,z183,z5]),(0,[z0,z78,z1,z2,z3,z7,z5]),(0,[z0,z1,z2,z3,z7,z34,z184]),(0,[z0,z45,z1,z2,z16,z3,z7])],[(0,[z54,z0,z1,z2,z3,z7,z14])],[(0,[z185,z0,z1,z2,z3,z7,z5]),(0,[z186,z0,z1,z2,z3,z7,z5]),(0,[z85,z0,z1,z159,z3,z7,z5]),(0,[z0,z187,z1,z2,z3,z7,z5]),(0,[z0,z1,z2,z3,z188,z7,z5]),(0,[z0,z24,z1,z2,z3,z7,z34]),(0,[z0,z189,z1,z2,z3,z7,z5])],[(1,[z0,z190,z2,z3,z7,z5]),(0,[z0,z1,z2,z3,z191,z7,z5]),(0,[z0,z192,z1,z2,z3,z7,z5]),(0,[z0,z1,z2,z3,z7,z193,z5]),(0,[z0,z1,z2,z194,z3,z7,z5]),(1,[z0,z195,z1,z2,z7,z34])]],
   [[(0,[z0,z1,z2,z3,z4,z7,z5]),(0,[z0,z1,z2,z3,z7,z5,z196]),(0,[z0,z197,z1,z2,z3,z7,z5]),(0,[z0,z1,z198,z2,z3,z7,z5]),(0,[z0,z1,z2,z199,z18,z3,z7]),(0,[z0,z11,z1,z2,z3,z7,z14]),(0,[z0,z175,z1,z2,z3,z7,z5]),(0,[z0,z1,z2,z3,z200,z7,z5])],[(1,[z0,z1,z2,z3,z7,z125]),(0,[z0,z1,z2,z3,z165,z5,z51]),(1,[z0,z24,z162,z3,z7,z5]),(1,[z0,z201,z2,z3,z160,z5]),(1,[z0,z1,z2,z3,z7,z66])],[(0,[z0,z1,z2,z3,z7,z132,z5]),(0,[z0,z1,z202,z2,z3,z7,z5]),(0,[z0,z1,z2,z28,z3,z7,z56]),(0,[z0,z203,z1,z2,z3,z7,z5]),(0,[z0,z87,z1,z2,z3,z7,z39]),(0,[z0,z1,z2,z3,z7,z51,z39]),(0,[z0,z204,z1,z2,z3,z7,z5]),(0,[z0,z1,z2,z3,z3,z7,z14])],[(0,[z0,z1,z2,z3,z7,z205,z5]),(0,[z0,z206,z1,z2,z3,z7,z5]),(0,[z0,z1,z207,z2,z3,z7,z5]),(0,[z0,z1,z2,z208,z3,z7,z5]),(0,[z0,z89,z1,z2,z16,z3,z7]),(0,[z209,z0,z1,z2,z3,z7,z5]),(0,[z0,z1,z210,z2,z3,z7,z14]),(1,[z0,z211,z1,z16,z3,z7])],[(0,[z0,z24,z1,z2,z3,z7,z5]),(0,[z0,z78,z1,z2,z3,z7,z14]),(0,[z0,z212,z1,z2,z3,z7,z34])],[(0,[z0,z17,z1,z2,z3,z7,z213]),(0,[z0,z1,z2,z3,z214,z7,z5])],[(0,[z0,z89,z1,z70,z3,z7,z5]),(0,[z0,z1,z2,z3,z7,z7,z5]),(0,[z0,z215,z1,z2,z3,z7,z5]),(0,[z0,z1,z2,z3,z216,z7,z5]),(0,[z0,z1,z2,z3,z7,z5,z217]),(0,[z0,z201,z1,z2,z3,z73,z5]),(0,[z0,z1,z2,z3,z7,z5,z53]),(0,[z0,z1,z2,z3,z7,z34,z39]),(0,[z0,z1,z2,z16,z218,z3,z7]),(0,[z0,z219,z1,z2,z3,z7,z5])],[(0,[z0,z1,z220,z2,z3,z7,z5]),(0,[z0,z1,z2,z3,z7,z35,z56]),(0,[z0,z201,z1,z2,z3,z7,z39]),(0,[z0,z1,z2,z3,z7,z144,z14])]],
   [[(0,[z0,z221,z1,z2,z3,z7,z5])],[(1,[z141,z52,z2,z3,z7,z5]),(0,[z83,z0,z1,z2,z3,z7,z5]),(0,[z15,z0,z222,z2,z3,z7,z5]),(0,[z0,z1,z2,z3,z7,z165,z34]),(0,[z0,z1,z2,z3,z7,z223,z5]),(1,[z0,z1,z2,z3,z7,z82]),(0,[z0,z1,z2,z3,z7,z34,z224])],[(0,[z0,z1,z2,z40,z7,z225,z5]),(0,[z0,z65,z1,z2,z3,z7,z226]),(0,[z0,z27,z1,z2,z3,z7,z53]),(0,[z0,z1,z227,z2,z3,z7,z5]),(0,[z0,z1,z2,z228,z3,z7,z5]),(0,[z0,z229,z1,z2,z3,z7,z5]),(0,[z0,z212,z1,z2,z3,z7,z5])],[(0,[z54,z1,z70,z2,z3,z7,z5]),(0,[z0,z1,z2,z3,z7,z230,z34]),(0,[z13,z0,z1,z2,z3,z7,z5])],[(0,[z0,z1,z1,z2,z3,z7,z5]),(1,[z0,z1,z2,z3,z231,z5]),(0,[z0,z1,z2,z3,z232,z7,z5]),(0,[z0,z1,z19,z2,z16,z3,z7]),(0,[z0,z1,z2,z233,z3,z7,z5])],[(0,[z0,z1,z234,z2,z3,z7,z5]),(0,[z0,z1,z2,z3,z148,z20,z5]),(1,[z0,z1,z235,z3,z7,z5]),(0,[z0,z1,z236,z2,z3,z7,z5]),(0,[z0,z1,z2,z67,z3,z7,z34]),(0,[z0,z1,z2,z3,z7,z5,z110])],[(0,[z141,z0,z38,z2,z3,z7,z5]),(0,[z0,z1,z2,z237,z3,z7,z5]),(0,[z0,z1,z2,z3,z238,z7,z5]),(0,[z0,z1,z2,z239,z3,z7,z5]),(0,[z0,z1,z2,z240,z3,z7,z5])],[(0,[z0,z1,z19,z70,z3,z7,z5]),(0,[z241,z0,z1,z2,z3,z7,z5]),(0,[z0,z1,z2,z3,z7,z165,z5]),(1,[z0,z1,z12,z114,z7,z5]),(0,[z0,z1,z2,z242,z3,z7,z5]),(0,[z0,z1,z2,z3,z243,z7,z5]),(0,[z0,z211,z1,z2,z16,z3,z7])]],
   [[(1,[z0,z1,z2,z3,z244,z5]),(0,[z0,z1,z2,z3,z7,z56,z14]),(0,[z0,z245,z1,z2,z3,z7,z5]),(0,[z0,z1,z2,z3,z7,z246,z5]),(0,[z0,z1,z2,z3,z7,z14,z247])],[(0,[z248,z0,z1,z2,z3,z7,z5]),(0,[z0,z1,z2,z3,z7,z230,z5]),(0,[z0,z1,z2,z249,z3,z7,z5]),(0,[z250,z0,z1,z2,z3,z7,z5])],[(0,[z0,z1,z2,z3,z7,z34,z56]),(0,[z0,z24,z1,z2,z3,z7,z39])],[(1,[z0,z175,z1,z2,z3,z7]),(0,[z0,z195,z1,z2,z7,z34,z5]),(0,[z0,z1,z2,z67,z3,z7,z5]),(0,[z0,z1,z2,z16,z3,z3,z7])],[(0,[z0,z120,z52,z2,z3,z7,z5]),(0,[z0,z87,z1,z2,z3,z7,z51]),(0,[z0,z138,z1,z2,z3,z7,z251]),(0,[z0,z1,z252,z2,z3,z7,z5]),(0,[z0,z1,z2,z3,z7,z253,z5])],[(0,[z254,z0,z1,z2,z3,z7,z5]),(0,[z0,z1,z2,z255,z3,z7,z5]),(0,[z0,z256,z1,z2,z3,z7,z5])],[(0,[z0,z1,z2,z18,z40,z7,z5]),(0,[z0,z1,z2,z28,z3,z7,z133]),(0,[z0,z257,z1,z2,z3,z7,z5]),(0,[z0,z1,z2,z3,z7,z14,z44]),(0,[z258,z0,z1,z2,z16,z3,z7]),(0,[z0,z1,z2,z259,z3,z7,z5]),(0,[z0,z1,z2,z3,z7,z260,z5])],[(0,[z83,z0,z1,z2,z3,z7,z39]),(1,[z0,z1,z2,z3,z97,z5]),(0,[z0,z1,z2,z23,z3,z7,z5]),(0,[z32,z0,z1,z2,z3,z165,z5]),(0,[z0,z1,z2,z3,z7,z165,z14]),(0,[z8,z0,z1,z2,z16,z3,z7]),(1,[z0,z1,z2,z3,z7,z251])]],
   [[(0,[z0,z1,z261,z2,z3,z7,z5]),(0,[z0,z1,z2,z3,z7,z262,z5]),(0,[z85,z0,z1,z2,z3,z231,z5]),(0,[z0,z263,z1,z2,z16,z3,z7]),(0,[z0,z1,z2,z3,z9,z7,z14])],[(1,[z0,z1,z2,z3,z7,z196]),(0,[z0,z264,z1,z2,z3,z7,z5]),(0,[z0,z1,z2,z159,z3,z7,z5]),(0,[z0,z265,z1,z2,z3,z7,z5]),(0,[z0,z120,z65,z2,z3,z7,z5]),(0,[z0,z201,z1,z2,z3,z7,z86])],[],[(0,[z0,z266,z1,z2,z3,z7,z5]),(0,[z0,z1,z2,z3,z7,z73,z14]),(0,[z267,z0,z1,z2,z3,z7,z5])],[(0,[z0,z1,z30,z3,z7,z20,z5]),(1,[z0,z1,z30,z3,z7,z39]),(0,[z0,z1,z268,z2,z3,z7,z5]),(0,[z32,z0,z1,z2,z3,z7,z39]),(0,[z0,z1,z2,z166,z3,z7,z5]),(0,[z0,z1,z2,z3,z7,z269,z5]),(0,[z0,z1,z2,z240,z3,z7,z39]),(0,[z0,z1,z2,z3,z7,z270,z5])],[(1,[z0,z1,z2,z271,z7,z5]),(0,[z0,z1,z2,z40,z3,z7,z5]),(0,[z0,z1,z2,z16,z3,z148,z7]),(1,[z0,z1,z2,z272,z7,z5]),(0,[z0,z1,z2,z3,z7,z273,z5]),(0,[z0,z274,z1,z2,z3,z7,z5]),(0,[z0,z27,z2,z3,z7,z35,z5]),(0,[z0,z1,z2,z275,z3,z7,z5]),(0,[z276,z0,z1,z2,z3,z7,z5]),(0,[z0,z1,z2,z242,z3,z7,z39]),(0,[z0,z1,z2,z3,z277,z7,z5])],[(0,[z0,z278,z1,z2,z3,z7,z5]),(0,[z279,z0,z1,z2,z3,z7,z5]),(0,[z0,z1,z2,z3,z7,z34,z280]),(0,[z0,z1,z2,z281,z3,z7,z5])],[(0,[z55,z0,z1,z2,z3,z9,z7]),(1,[z0,z1,z2,z3,z7,z217]),(0,[z0,z1,z2,z16,z3,z7,z14])]],
   [[(0,[z0,z38,z2,z162,z3,z7,z5]),(0,[z0,z1,z2,z40,z7,z5,z14]),(1,[z0,z1,z2,z282,z3,z7])],[(0,[z116,z0,z38,z2,z3,z7,z5]),(0,[z0,z38,z2,z3,z7,z280,z5]),(0,[z0,z1,z38,z2,z16,z3,z7]),(0,[z0,z222,z1,z2,z3,z7,z5]),(0,[z0,z1,z2,z67,z3,z7,z39]),(0,[z0,z1,z2,z16,z67,z3,z7])],[(0,[z85,z0,z1,z2,z3,z7,z14]),(0,[z0,z1,z2,z114,z40,z7,z5]),(0,[z0,z1,z2,z3,z7,z5,z283]),(0,[z284,z0,z1,z2,z3,z7,z5]),(0,[z0,z1,z12,z2,z3,z7,z34]),(0,[z0,z1,z2,z3,z7,z39,z285]),(0,[z0,z1,z16,z147,z3,z7,z5])],[(1,[z0,z1,z2,z127,z3,z7]),(0,[z55,z0,z1,z2,z16,z3,z7]),(0,[z0,z286,z1,z2,z3,z7,z5]),(0,[z0,z1,z2,z3,z7,z287,z5]),(0,[z0,z1,z2,z3,z7,z288,z5])],[(0,[z289,z0,z1,z2,z3,z7,z5]),(0,[z0,z1,z2,z3,z7,z5,z290]),(0,[z0,z1,z2,z3,z7,z291,z5]),(1,[z0,z1,z2,z3,z7,z292]),(0,[z8,z0,z27,z1,z2,z3,z7]),(0,[z0,z1,z2,z3,z7,z225,z34]),(0,[z0,z1,z2,z3,z7,z293,z5])],[(0,[z0,z1,z2,z3,z7,z294,z5]),(0,[z0,z1,z2,z295,z3,z7,z5]),(0,[z0,z296,z1,z2,z16,z3,z7]),(1,[z0,z1,z16,z147,z3,z7])],[(0,[z0,z52,z2,z3,z7,z73,z5]),(0,[z0,z1,z2,z297,z3,z7,z5]),(0,[z0,z1,z2,z62,z7,z225,z5]),(0,[z298,z0,z1,z2,z3,z7,z5]),(0,[z15,z0,z1,z2,z3,z148,z5]),(0,[z0,z1,z2,z3,z7,z34,z133]),(0,[z0,z120,z1,z2,z3,z7,z34]),(0,[z0,z1,z299,z2,z3,z7,z5]),(0,[z0,z1,z2,z3,z300,z7,z5])],[(1,[z0,z1,z301,z3,z7,z5]),(0,[z0,z1,z302,z2,z3,z7,z5]),(0,[z15,z0,z198,z2,z3,z7,z5]),(1,[z0,z222,z2,z3,z7,z5]),(0,[z0,z1,z2,z3,z244,z7,z5]),(0,[z0,z1,z2,z3,z7,z5,z303]),(0,[z0,z58,z1,z2,z3,z7,z39]),(0,[z304,z0,z1,z2,z3,z7,z5]),(0,[z0,z305,z1,z2,z16,z3,z7]),(0,[z0,z1,z2,z3,z7,z306,z5])]],
   [[(0,[z0,z1,z2,z3,z7,z307,z5]),(0,[z0,z1,z12,z2,z3,z7,z5]),(0,[z0,z1,z2,z16,z3,z79,z7]),(0,[z0,z1,z2,z3,z7,z39,z39])],[(0,[z0,z1,z2,z308,z3,z7,z5]),(0,[z55,z0,z1,z166,z3,z7,z5]),(0,[z0,z309,z1,z2,z3,z7,z5])],[(0,[z0,z310,z1,z2,z3,z7,z5]),(0,[z0,z311,z1,z2,z3,z7,z5]),(0,[z0,z1,z37,z2,z3,z7,z39]),(0,[z0,z312,z1,z2,z3,z7,z5]),(0,[z0,z89,z1,z2,z3,z7,z14]),(0,[z0,z1,z2,z3,z7,z225,z5])],[(0,[z0,z1,z19,z30,z3,z7,z5]),(1,[z0,z1,z2,z3,z7,z313]),(0,[z0,z1,z2,z40,z3,z7,z39]),(0,[z0,z1,z314,z2,z3,z7,z5]),(0,[z0,z315,z1,z2,z3,z7,z5]),(0,[z0,z1,z316,z2,z3,z7,z5])],[(0,[z0,z120,z1,z2,z3,z7,z5]),(0,[z0,z317,z1,z2,z3,z7,z5]),(0,[z0,z1,z318,z2,z3,z7,z5])],[(0,[z0,z319,z1,z2,z3,z7,z5]),(0,[z0,z52,z1,z2,z3,z7,z39]),(0,[z15,z0,z1,z2,z3,z7,z34])],[(0,[z0,z17,z1,z2,z3,z7,z34]),(0,[z0,z1,z2,z3,z9,z7,z35]),(0,[z0,z11,z1,z2,z3,z7,z320]),(0,[z0,z91,z1,z12,z2,z7,z5]),(0,[z0,z1,z2,z3,z7,z20,z14]),(0,[z0,z321,z1,z2,z3,z7,z5]),(0,[z0,z322,z1,z2,z3,z7,z5]),(0,[z0,z1,z2,z3,z300,z7,z14])],[(0,[z116,z0,z1,z2,z3,z7,z196]),(0,[z0,z1,z2,z30,z3,z7,z34]),(0,[z0,z1,z2,z3,z7,z133,z53]),(0,[z0,z65,z1,z2,z3,z7,z39]),(0,[z0,z323,z1,z2,z3,z7,z5]),(0,[z0,z1,z2,z171,z3,z7,z5])]],
   [[(0,[z0,z1,z2,z3,z7,z324,z5]),(0,[z325,z0,z1,z2,z3,z7,z5]),(0,[z0,z1,z2,z326,z3,z7,z5]),(0,[z85,z0,z1,z2,z3,z7,z292]),(0,[z0,z1,z2,z3,z7,z5,z327]),(0,[z0,z1,z235,z2,z3,z7,z5]),(0,[z55,z0,z27,z1,z2,z3,z7]),(0,[z0,z1,z2,z3,z7,z5,z328]),(0,[z0,z1,z2,z3,z7,z5,z329]),(0,[z0,z174,z1,z2,z3,z9,z5]),(0,[z0,z1,z2,z3,z9,z7,z51])],[(0,[z330,z0,z1,z2,z3,z7,z5]),(1,[z0,z89,z1,z3,z7,z34]),(0,[z0,z91,z1,z2,z16,z7,z5])],[(0,[z0,z1,z2,z3,z331,z7,z5]),(0,[z0,z332,z1,z38,z2,z3,z7]),(0,[z54,z0,z1,z2,z3,z7,z34]),(0,[z0,z201,z2,z3,z160,z7,z5]),(0,[z0,z1,z2,z3,z7,z225,z14]),(0,[z333,z0,z1,z2,z3,z7,z5]),(0,[z0,z1,z2,z3,z7,z334,z5])],[(0,[z116,z0,z1,z2,z271,z7,z5]),(0,[z0,z1,z70,z2,z3,z7,z313]),(0,[z15,z0,z1,z2,z3,z7,z5]),(0,[z0,z1,z2,z3,z129,z7,z165]),(0,[z0,z1,z2,z3,z335,z7,z5])],[(0,[z0,z1,z2,z16,z3,z62,z7]),(0,[z113,z0,z1,z2,z40,z7,z5]),(0,[z0,z120,z1,z2,z3,z7,z14]),(0,[z0,z17,z1,z2,z3,z7,z5]),(0,[z0,z1,z2,z3,z7,z34,z73]),(0,[z0,z1,z2,z336,z3,z7,z5]),(0,[z0,z1,z2,z3,z7,z337,z5]),(0,[z0,z1,z2,z3,z7,z224,z5])],[(0,[z141,z0,z1,z2,z16,z3,z7]),(0,[z0,z1,z2,z30,z3,z7,z5]),(0,[z0,z1,z2,z127,z40,z3,z7]),(0,[z0,z338,z1,z2,z3,z7,z5]),(0,[z0,z1,z2,z16,z3,z7,z35]),(0,[z0,z11,z1,z2,z3,z7,z34]),(0,[z0,z1,z2,z3,z7,z176,z5]),(0,[z0,z1,z2,z339,z16,z3,z7])],[(0,[z181,z0,z1,z2,z3,z7,z5]),(0,[z15,z32,z1,z2,z3,z7,z5]),(0,[z0,z340,z1,z2,z3,z7,z5]),(0,[z0,z27,z1,z2,z3,z7,z34]),(0,[z0,z1,z12,z2,z3,z7,z39]),(0,[z0,z1,z2,z218,z3,z7,z34]),(0,[z0,z48,z1,z2,z3,z7,z5]),(0,[z0,z341,z1,z2,z16,z3,z7]),(0,[z0,z1,z2,z3,z342,z7,z5])],[(0,[z0,z1,z2,z343,z3,z7,z5]),(1,[z0,z1,z2,z3,z7,z344]),(0,[z0,z1,z2,z3,z7,z345,z5]),(0,[z0,z1,z2,z16,z3,z7,z51])]],
   [[(0,[z54,z0,z1,z2,z3,z7,z5]),(0,[z346,z0,z1,z2,z3,z7,z34])],[(0,[z0,z1,z2,z3,z7,z347,z5]),(0,[z0,z1,z2,z3,z7,z53,z14]),(1,[z0,z11,z1,z3,z7,z39]),(1,[z0,z174,z1,z2,z28,z3])],[(0,[z0,z1,z2,z3,z7,z92,z5]),(0,[z0,z1,z2,z348,z3,z7,z5]),(0,[z0,z1,z349,z2,z3,z7,z5]),(0,[z0,z157,z1,z2,z3,z7,z5])],[(0,[z0,z1,z2,z350,z3,z7,z5]),(0,[z15,z0,z1,z2,z3,z7,z14]),(0,[z0,z1,z2,z3,z351,z7,z5]),(1,[z0,z1,z2,z3,z7,z283]),(0,[z0,z11,z1,z2,z3,z7,z5]),(0,[z352,z0,z1,z2,z3,z7,z5]),(0,[z0,z1,z2,z3,z7,z353,z34])],[(0,[z141,z0,z52,z2,z3,z7,z5]),(0,[z0,z1,z30,z3,z7,z5,z39]),(0,[z0,z1,z2,z62,z7,z5,z14]),(0,[z0,z1,z2,z3,z7,z5,z354]),(0,[z15,z0,z1,z2,z3,z165,z5]),(0,[z0,z1,z355,z2,z3,z7,z5]),(0,[z0,z27,z1,z2,z3,z7,z5]),(0,[z0,z1,z2,z16,z114,z3,z7]),(0,[z0,z1,z2,z218,z3,z7,z5])],[(0,[z83,z0,z1,z2,z3,z7,z356]),(0,[z0,z357,z1,z2,z3,z7,z5]),(0,[z0,z1,z358,z2,z3,z7,z5]),(0,[z0,z1,z2,z3,z160,z7,z328]),(1,[z0,z11,z1,z2,z7,z14]),(0,[z258,z0,z1,z2,z3,z7,z14])],[(0,[z346,z0,z1,z2,z3,z7,z5]),(0,[z0,z1,z2,z3,z97,z7,z5]),(0,[z8,z1,z2,z3,z7,z56,z5]),(0,[z0,z1,z2,z3,z7,z5,z81]),(1,[z0,z1,z2,z16,z7,z14]),(0,[z0,z1,z210,z2,z3,z7,z5])],[(0,[z0,z263,z1,z2,z3,z7,z14]),(0,[z0,z1,z12,z114,z3,z7,z5]),(0,[z0,z138,z1,z3,z7,z20,z5]),(0,[z359,z0,z1,z2,z3,z7,z5]),(0,[z0,z1,z2,z28,z3,z9,z7]),(0,[z0,z174,z1,z2,z28,z3,z7])]],
   [[(0,[z0,z360,z1,z2,z3,z7,z5]),(1,[z0,z1,z2,z3,z167,z5]),(0,[z0,z1,z2,z361,z3,z7,z5]),(0,[z0,z1,z2,z3,z7,z5,z14])],[(0,[z0,z1,z2,z3,z7,z353,z5]),(0,[z0,z1,z2,z362,z3,z7,z5]),(0,[z55,z0,z1,z235,z3,z7,z5]),(0,[z0,z1,z363,z2,z3,z7,z5]),(0,[z0,z1,z2,z3,z364,z7,z5])],[(0,[z0,z1,z2,z365,z3,z7,z5]),(0,[z0,z366,z1,z2,z3,z7,z5]),(0,[z0,z17,z1,z2,z3,z7,z39]),(1,[z0,z78,z2,z18,z7,z5])],[(0,[z0,z1,z2,z30,z3,z7,z39]),(1,[z0,z1,z70,z3,z7,z39]),(0,[z0,z1,z2,z367,z3,z7,z5]),(0,[z0,z263,z1,z2,z3,z160,z5]),(0,[z368,z0,z1,z2,z3,z7,z5]),(0,[z369,z0,z1,z2,z3,z7,z5]),(0,[z0,z1,z12,z2,z3,z7,z370]),(0,[z0,z1,z2,z3,z7,z371,z14]),(0,[z372,z0,z1,z2,z3,z7,z5]),(1,[z0,z1,z2,z147,z3,z7]),(0,[z0,z1,z2,z28,z16,z3,z7])],[(0,[z0,z1,z2,z3,z7,z5,z373]),(0,[z0,z1,z2,z107,z3,z7,z5]),(0,[z55,z0,z1,z2,z3,z244,z5]),(0,[z0,z1,z374,z2,z3,z7,z5]),(0,[z0,z1,z2,z3,z7,z375,z5]),(0,[z0,z27,z1,z2,z3,z7,z14]),(0,[z0,z1,z2,z3,z7,z376,z5]),(0,[z0,z1,z2,z218,z3,z7,z14])],[(1,[z0,z198,z2,z3,z7,z5]),(0,[z0,z1,z2,z3,z7,z377,z5]),(0,[z8,z0,z174,z1,z2,z3,z7]),(0,[z0,z17,z78,z2,z3,z7,z5]),(0,[z0,z134,z1,z2,z16,z3,z7])],[(0,[z0,z1,z378,z2,z3,z7,z5]),(0,[z0,z91,z1,z2,z3,z7,z34])],[(1,[z0,z202,z2,z3,z7,z5]),(0,[z1,z2,z3,z148,z7,z165,z5]),(1,[z32,z1,z2,z3,z148,z5]),(0,[z379,z0,z1,z2,z3,z7,z5]),(0,[z380,z0,z1,z2,z3,z7,z5]),(0,[z0,z174,z1,z2,z16,z3,z7])]],
   [[(0,[z116,z0,z1,z2,z16,z3,z7]),(0,[z83,z54,z1,z2,z3,z7,z5]),(0,[z0,z381,z1,z2,z3,z7,z5]),(0,[z382,z0,z1,z2,z3,z7,z5]),(0,[z0,z383,z1,z2,z3,z7,z5]),(1,[z0,z1,z2,z3,z7,z119]),(0,[z0,z138,z1,z2,z3,z7,z34]),(1,[z0,z195,z1,z2,z7,z5])],[(0,[z0,z1,z2,z3,z62,z7,z34]),(0,[z55,z8,z1,z2,z3,z7,z5]),(0,[z0,z1,z2,z162,z16,z3,z7]),(1,[z0,z1,z2,z3,z7,z328]),(0,[z0,z11,z1,z2,z3,z7,z39]),(0,[z0,z384,z1,z2,z3,z7,z5]),(0,[z0,z1,z385,z2,z16,z3,z7])],[(0,[z0,z1,z70,z3,z7,z20,z5]),(0,[z0,z1,z2,z3,z7,z5,z386]),(0,[z0,z1,z2,z3,z7,z387,z5]),(1,[z0,z120,z65,z3,z7,z5]),(0,[z388,z0,z1,z2,z3,z7,z5]),(0,[z0,z1,z2,z3,z389,z7,z5]),(0,[z0,z1,z390,z2,z3,z7,z5]),(0,[z0,z1,z2,z391,z3,z7,z5])],[(0,[z0,z1,z2,z3,z7,z56,z5]),(1,[z0,z1,z2,z3,z7,z34]),(0,[z0,z392,z1,z2,z3,z7,z14])],[(1,[z85,z1,z2,z62,z7,z5]),(0,[z0,z393,z1,z2,z3,z7,z5]),(0,[z0,z11,z1,z3,z7,z5,z39]),(0,[z0,z1,z2,z3,z7,z39,z394]),(1,[z0,z1,z2,z7,z82,z5]),(0,[z0,z91,z1,z2,z3,z7,z5]),(0,[z0,z1,z2,z16,z147,z3,z7])],[(0,[z0,z1,z30,z3,z7,z71,z5]),(0,[z0,z78,z1,z2,z3,z7,z39]),(0,[z0,z1,z2,z3,z160,z7,z14]),(0,[z0,z1,z2,z395,z3,z7,z5]),(0,[z0,z1,z2,z3,z7,z5,z396]),(0,[z0,z1,z2,z3,z7,z397,z5]),(0,[z0,z1,z2,z3,z9,z7,z34])],[(0,[z0,z1,z2,z301,z3,z7,z5]),(0,[z0,z138,z1,z2,z3,z7,z5])],[(0,[z116,z0,z52,z2,z3,z7,z5]),(0,[z0,z1,z2,z398,z3,z7,z5]),(0,[z0,z1,z2,z3,z62,z7,z5])]],
   [[(0,[z0,z399,z1,z2,z3,z7,z5])],[(1,[z0,z1,z2,z3,z7,z5]),(0,[z55,z0,z1,z2,z272,z7,z5]),(0,[z55,z0,z174,z1,z2,z3,z7]),(0,[z0,z1,z2,z18,z3,z7,z217]),(0,[z0,z1,z12,z2,z114,z7,z5]),(0,[z0,z400,z1,z2,z3,z7,z5]),(0,[z0,z45,z1,z2,z218,z7,z5])],[(0,[z401,z0,z1,z2,z3,z7,z5]),(0,[z0,z1,z2,z402,z3,z7,z5]),(0,[z0,z195,z1,z2,z3,z7,z34])],[(0,[z0,z1,z70,z2,z3,z7,z34]),(0,[z85,z0,z202,z2,z3,z7,z5]),(0,[z0,z1,z403,z2,z3,z7,z5]),(0,[z404,z0,z1,z2,z3,z7,z5]),(0,[z405,z0,z1,z2,z3,z7,z34]),(1,[z0,z1,z147,z3,z7,z5]),(0,[z0,z211,z1,z16,z3,z7,z5]),(0,[z0,z1,z2,z3,z9,z7,z5]),(0,[z406,z0,z1,z2,z3,z7,z5])],[(0,[z0,z201,z1,z2,z16,z3,z7]),(0,[z0,z1,z2,z114,z3,z7,z14]),(0,[z0,z1,z2,z16,z3,z7,z34]),(0,[z0,z91,z1,z2,z3,z7,z14])],[(0,[z83,z0,z96,z2,z3,z7,z5]),(0,[z0,z1,z2,z3,z7,z5,z313]),(0,[z85,z113,z1,z2,z3,z7,z5]),(0,[z0,z1,z2,z3,z7,z407,z5]),(0,[z408,z0,z1,z2,z3,z7,z5]),(0,[z0,z1,z2,z409,z3,z7,z5])],[(0,[z0,z1,z2,z3,z7,z73,z5]),(0,[z0,z138,z1,z2,z3,z7,z14]),(0,[z0,z1,z2,z410,z3,z7,z5]),(0,[z0,z1,z411,z2,z3,z7,z5])],[(0,[z83,z0,z1,z2,z3,z105,z5]),(0,[z0,z1,z2,z3,z412,z7,z5]),(0,[z85,z0,z1,z2,z3,z7,z34]),(0,[z0,z1,z2,z3,z62,z7,z14]),(0,[z0,z1,z2,z3,z7,z184,z5]),(0,[z0,z1,z2,z282,z218,z3,z7])]],
   [[(0,[z0,z1,z2,z3,z142,z7,z5]),(0,[z0,z1,z2,z413,z3,z7,z5]),(0,[z0,z2,z3,z7,z35,z5,z53]),(0,[z0,z414,z1,z2,z3,z7,z5]),(0,[z0,z1,z2,z3,z389,z7,z39]),(0,[z0,z45,z1,z2,z3,z7,z34]),(0,[z0,z195,z1,z2,z3,z7,z5]),(0,[z0,z1,z2,z16,z3,z7,z225]),(0,[z0,z1,z2,z3,z7,z5,z51]),(0,[z0,z415,z1,z2,z3,z7,z5])],[(0,[z0,z1,z70,z2,z3,z7,z5]),(0,[z83,z0,z1,z2,z112,z7,z5]),(0,[z405,z0,z1,z2,z3,z7,z5]),(0,[z0,z1,z416,z2,z3,z7,z5]),(0,[z0,z1,z417,z2,z3,z7,z5]),(0,[z0,z1,z2,z67,z7,z5,z14]),(1,[z0,z1,z2,z3,z7,z14])],[(0,[z0,z1,z22,z2,z3,z7,z5]),(0,[z0,z418,z1,z2,z3,z7,z5]),(0,[z0,z419,z1,z2,z3,z7,z5]),(0,[z0,z27,z1,z2,z3,z7,z35]),(0,[z0,z420,z1,z2,z3,z7,z5]),(0,[z0,z1,z2,z421,z3,z7,z34]),(0,[z0,z1,z2,z16,z3,z7,z5])],[(0,[z15,z0,z1,z2,z3,z7,z422]),(0,[z0,z423,z1,z2,z3,z7,z5])],[(0,[z141,z0,z1,z2,z3,z7,z14]),(0,[z0,z27,z1,z2,z3,z7,z51]),(0,[z0,z45,z341,z1,z2,z3,z5])],[(0,[z85,z0,z1,z2,z3,z7,z5]),(0,[z0,z424,z1,z2,z3,z7,z5]),(0,[z0,z11,z1,z3,z7,z71,z5]),(0,[z0,z341,z1,z2,z3,z7,z14]),(0,[z0,z1,z2,z425,z3,z7,z5]),(0,[z0,z1,z2,z409,z3,z7,z14])],[(0,[z0,z1,z30,z162,z3,z7,z5]),(0,[z0,z1,z2,z3,z7,z35,z133]),(0,[z0,z426,z1,z2,z3,z7,z5]),(0,[z0,z1,z2,z3,z7,z427,z5]),(0,[z0,z1,z2,z3,z7,z428,z5]),(0,[z0,z1,z2,z429,z3,z7,z5]),(0,[z0,z45,z1,z2,z3,z7,z5])],[(0,[z0,z1,z2,z430,z3,z7,z5]),(0,[z0,z120,z1,z162,z3,z7,z5]),(0,[z0,z431,z1,z2,z3,z7,z5]),(0,[z0,z1,z3,z79,z7,z20,z5]),(0,[z0,z89,z1,z2,z3,z7,z34])]],
   [[(0,[z0,z1,z2,z3,z7,z165,z39]),(0,[z0,z1,z2,z421,z3,z7,z5]),(0,[z0,z1,z2,z432,z3,z7,z5]),(0,[z0,z1,z2,z218,z3,z225,z5]),(0,[z0,z433,z1,z2,z3,z7,z5]),(1,[z0,z1,z2,z3,z7,z371]),(0,[z0,z1,z2,z434,z3,z7,z5])],[(0,[z435,z0,z1,z2,z3,z7,z5]),(0,[z0,z1,z70,z2,z3,z7,z14]),(0,[z0,z1,z2,z436,z3,z7,z5]),(0,[z0,z263,z201,z2,z3,z7,z5]),(0,[z0,z1,z2,z114,z3,z7,z396]),(0,[z0,z1,z2,z3,z7,z5,z344]),(0,[z0,z1,z2,z3,z9,z7,z39])],[(0,[z83,z0,z1,z2,z3,z142,z5]),(0,[z0,z437,z1,z2,z3,z7,z5]),(0,[z0,z1,z2,z438,z3,z7,z5]),(1,[z0,z1,z2,z3,z7,z25]),(0,[z0,z120,z65,z1,z3,z7,z5]),(0,[z0,z1,z2,z3,z7,z439,z5]),(0,[z440,z0,z1,z2,z3,z7,z5]),(0,[z0,z1,z2,z3,z7,z441,z5]),(0,[z0,z420,z1,z2,z3,z7,z14])],[(0,[z0,z442,z1,z2,z3,z7,z5]),(0,[z0,z1,z2,z3,z443,z7,z5]),(0,[z0,z1,z2,z3,z7,z444,z5]),(0,[z0,z1,z445,z2,z3,z7,z5]),(0,[z0,z45,z1,z2,z3,z7,z446]),(0,[z0,z1,z2,z3,z7,z447,z5])],[(0,[z116,z1,z38,z2,z3,z7,z5]),(1,[z0,z366,z1,z2,z3,z7]),(0,[z0,z11,z1,z2,z114,z7,z5]),(0,[z0,z1,z2,z3,z7,z448,z5])],[(1,[z0,z1,z2,z3,z7,z213]),(0,[z0,z89,z1,z2,z3,z7,z5]),(1,[z0,z211,z1,z3,z7,z5])],[(1,[z0,z1,z2,z3,z7,z396]),(0,[z0,z1,z2,z449,z3,z7,z5]),(0,[z0,z1,z2,z3,z7,z450,z5]),(0,[z0,z45,z1,z2,z3,z7,z14])],[(0,[z83,z0,z1,z70,z3,z7,z5]),(0,[z1,z70,z2,z30,z3,z7,z5]),(1,[z0,z1,z2,z67,z7,z14])]],
   [[(0,[z0,z451,z1,z2,z3,z7,z5]),(0,[z0,z452,z1,z2,z3,z7,z5]),(0,[z0,z1,z453,z2,z3,z7,z5]),(0,[z0,z1,z2,z3,z7,z213,z5]),(0,[z454,z0,z1,z2,z3,z7,z5]),(0,[z0,z1,z19,z2,z3,z7,z34]),(0,[z0,z419,z1,z2,z3,z7,z39]),(0,[z0,z1,z2,z16,z3,z7,z39]),(0,[z0,z1,z2,z282,z3,z7,z5]),(1,[z0,z1,z2,z218,z225,z5])],[(1,[z0,z1,z2,z84,z7,z5]),(0,[z32,z0,z1,z2,z16,z3,z7]),(0,[z0,z1,z2,z3,z7,z133,z14]),(0,[z0,z1,z2,z3,z7,z20,z5])],[(1,[z0,z1,z2,z3,z7,z455]),(1,[z0,z1,z2,z3,z7,z456]),(0,[z0,z1,z70,z3,z7,z5,z39]),(0,[z8,z0,z87,z1,z2,z3,z7]),(0,[z0,z457,z1,z2,z3,z7,z5]),(0,[z458,z0,z1,z2,z3,z7,z5])],[(0,[z0,z459,z1,z2,z3,z7,z5]),(0,[z85,z0,z1,z2,z3,z7,z39]),(0,[z15,z0,z1,z460,z3,z7,z5]),(0,[z15,z0,z1,z2,z367,z7,z5]),(0,[z0,z1,z2,z272,z3,z7,z5]),(0,[z0,z1,z2,z3,z7,z56,z51]),(0,[z0,z24,z1,z2,z3,z7,z106]),(0,[z0,z1,z2,z3,z7,z461,z5])],[(0,[z0,z1,z2,z462,z3,z7,z5]),(0,[z0,z1,z2,z3,z7,z34,z463]),(0,[z0,z1,z2,z218,z7,z225,z5]),(0,[z0,z1,z2,z464,z3,z7,z5])],[(1,[z0,z1,z220,z3,z7,z5]),(0,[z0,z1,z2,z3,z7,z34,z82]),(0,[z0,z1,z465,z2,z3,z7,z5])],[(0,[z0,z17,z1,z2,z3,z7,z466]),(0,[z0,z1,z2,z467,z3,z7,z5]),(0,[z0,z1,z2,z3,z7,z468,z5]),(0,[z0,z1,z2,z3,z7,z5,z320]),(0,[z0,z1,z12,z2,z7,z5,z14]),(0,[z0,z1,z19,z2,z3,z7,z5]),(0,[z0,z1,z2,z3,z79,z7,z14]),(0,[z0,z1,z2,z432,z3,z7,z39])],[(0,[z116,z0,z1,z2,z3,z7,z14]),(0,[z0,z1,z2,z3,z7,z469,z5]),(0,[z0,z1,z2,z3,z7,z470,z5]),(0,[z0,z1,z2,z3,z7,z5,z471]),(0,[z0,z174,z1,z2,z28,z3,z5])]],
   [[(0,[z0,z201,z38,z2,z3,z7,z5]),(0,[z0,z472,z1,z2,z3,z7,z5]),(0,[z0,z96,z1,z2,z3,z7,z5]),(0,[z0,z1,z2,z162,z3,z7,z14])],[(0,[z0,z473,z1,z2,z3,z7,z5]),(0,[z0,z1,z2,z3,z7,z456,z5]),(0,[z0,z1,z2,z3,z474,z7,z5]),(0,[z0,z1,z2,z3,z7,z280,z14]),(0,[z0,z1,z114,z3,z7,z5,z39]),(0,[z0,z211,z1,z2,z3,z7,z5])],[(1,[z0,z332,z1,z2,z3,z7]),(0,[z475,z0,z1,z2,z3,z7,z5]),(0,[z0,z1,z70,z2,z3,z7,z456]),(0,[z0,z1,z476,z2,z3,z7,z5]),(1,[z8,z1,z2,z3,z7,z56]),(0,[z477,z0,z1,z2,z3,z7,z5]),(0,[z0,z478,z1,z2,z3,z7,z5]),(0,[z258,z0,z1,z2,z3,z7,z34]),(0,[z0,z1,z2,z2,z3,z7,z34])],[(0,[z8,z0,z1,z2,z3,z7,z34]),(0,[z0,z89,z1,z2,z3,z7,z39]),(0,[z0,z45,z341,z1,z2,z7,z5])],[(0,[z83,z0,z190,z2,z3,z7,z5]),(0,[z0,z1,z479,z2,z3,z7,z5]),(1,[z54,z1,z70,z3,z7,z5]),(0,[z0,z1,z2,z3,z480,z7,z5]),(0,[z55,z0,z1,z2,z3,z167,z5]),(0,[z0,z1,z2,z16,z3,z7,z56]),(0,[z0,z263,z1,z2,z3,z7,z34]),(1,[z0,z1,z2,z3,z7,z173]),(0,[z0,z341,z1,z2,z218,z3,z5])],[(1,[z0,z1,z2,z3,z7,z132]),(0,[z83,z1,z2,z30,z3,z7,z5]),(0,[z0,z1,z2,z3,z7,z5,z481]),(0,[z0,z1,z2,z40,z3,z7,z31]),(0,[z0,z482,z1,z2,z3,z7,z5]),(0,[z0,z1,z2,z3,z7,z483,z5])],[(0,[z55,z0,z87,z1,z2,z3,z7]),(0,[z0,z1,z2,z484,z3,z7,z5]),(0,[z0,z1,z19,z2,z3,z7,z14])],[(0,[z0,z174,z1,z2,z3,z7,z53]),(0,[z485,z0,z1,z2,z3,z7,z5]),(0,[z0,z1,z2,z3,z7,z20,z39]),(0,[z0,z1,z37,z2,z16,z3,z7])]],
   [[(0,[z258,z0,z1,z2,z3,z7,z5]),(0,[z0,z486,z1,z2,z3,z7,z5]),(0,[z0,z1,z2,z3,z7,z487,z5]),(0,[z0,z1,z2,z2,z3,z7,z5]),(0,[z0,z488,z1,z2,z3,z7,z5]),(0,[z0,z1,z2,z3,z7,z489,z5]),(0,[z0,z490,z1,z2,z3,z7,z5]),(0,[z0,z491,z1,z2,z3,z7,z5]),(0,[z0,z1,z2,z3,z7,z492,z5])],[(0,[z0,z1,z493,z2,z3,z7,z5]),(1,[z0,z1,z2,z3,z7,z422]),(0,[z8,z0,z1,z2,z3,z7,z5]),(0,[z0,z494,z1,z2,z3,z7,z5]),(0,[z0,z2,z3,z160,z7,z73,z5]),(0,[z0,z1,z2,z16,z434,z3,z7])],[(0,[z116,z141,z1,z2,z3,z7,z5]),(0,[z0,z495,z1,z2,z3,z7,z5]),(0,[z0,z52,z1,z2,z16,z3,z7]),(0,[z0,z263,z1,z2,z3,z7,z5]),(0,[z0,z1,z2,z3,z496,z7,z5]),(0,[z0,z1,z2,z3,z7,z34,z20]),(0,[z0,z497,z1,z2,z3,z7,z5]),(0,[z0,z1,z2,z147,z3,z7,z5])],[(1,[z0,z1,z2,z3,z324,z5]),(0,[z0,z38,z2,z3,z7,z5,z53]),(0,[z0,z52,z2,z162,z3,z7,z5]),(0,[z0,z1,z2,z84,z3,z7,z5]),(0,[z0,z1,z2,z3,z160,z148,z5]),(0,[z0,z1,z2,z3,z7,z5,z5]),(0,[z0,z498,z1,z2,z3,z7,z5]),(0,[z0,z1,z2,z3,z7,z225,z39])],[(0,[z0,z52,z2,z3,z7,z280,z5]),(0,[z0,z65,z1,z2,z16,z3,z7]),(0,[z0,z89,z1,z114,z3,z7,z5]),(0,[z0,z499,z1,z2,z3,z7,z14]),(0,[z0,z1,z500,z2,z3,z7,z5])],[(0,[z0,z1,z38,z2,z3,z7,z34]),(0,[z0,z65,z2,z162,z3,z7,z5]),(0,[z0,z120,z1,z2,z3,z7,z39]),(1,[z0,z1,z2,z3,z7,z226]),(0,[z0,z1,z2,z18,z3,z7,z34]),(1,[z0,z91,z1,z2,z16,z7])],[(0,[z0,z1,z2,z3,z501,z7,z5]),(1,[z0,z87,z2,z3,z7,z53]),(0,[z0,z1,z2,z3,z7,z371,z5]),(0,[z0,z502,z1,z2,z3,z7,z5])],[(0,[z503,z0,z1,z2,z3,z7,z5]),(0,[z0,z65,z1,z70,z3,z7,z5]),(0,[z55,z0,z1,z2,z3,z7,z34]),(0,[z0,z504,z1,z2,z3,z7,z5]),(0,[z0,z201,z1,z2,z3,z160,z5]),(0,[z0,z87,z1,z2,z3,z7,z53]),(0,[z505,z0,z1,z2,z3,z7,z5]),(0,[z0,z1,z2,z16,z3,z7,z506])]],
   [[(0,[z116,z0,z1,z301,z3,z7,z5]),(0,[z116,z0,z1,z2,z3,z7,z455]),(0,[z507,z0,z1,z2,z3,z7,z5]),(0,[z475,z0,z1,z2,z3,z7,z39]),(0,[z0,z478,z1,z2,z3,z7,z39])],[(0,[z0,z1,z2,z3,z7,z5,z508]),(0,[z0,z509,z1,z2,z3,z7,z5]),(1,[z0,z355,z2,z3,z7,z5]),(0,[z0,z1,z2,z3,z7,z133,z51]),(0,[z8,z0,z1,z2,z3,z7,z14]),(1,[z0,z1,z2,z208,z3,z7]),(0,[z0,z11,z1,z2,z7,z5,z14]),(0,[z0,z1,z2,z3,z7,z510,z5]),(0,[z0,z494,z1,z2,z3,z7,z14]),(0,[z0,z511,z1,z2,z3,z7,z5])],[(0,[z113,z0,z1,z2,z16,z3,z7]),(0,[z0,z1,z2,z3,z7,z512,z5]),(0,[z0,z1,z2,z3,z513,z7,z5]),(0,[z0,z1,z2,z3,z160,z7,z34]),(0,[z0,z1,z2,z3,z7,z53,z39]),(0,[z0,z1,z114,z3,z7,z71,z5]),(0,[z0,z514,z1,z2,z3,z7,z5]),(0,[z0,z45,z1,z2,z3,z225,z5]),(0,[z0,z1,z2,z3,z7,z14,z14])],[(0,[z515,z0,z1,z2,z3,z7,z5]),(0,[z0,z1,z38,z2,z3,z7,z5]),(0,[z0,z1,z2,z3,z516,z7,z5]),(0,[z517,z0,z1,z2,z3,z7,z5]),(0,[z83,z0,z1,z30,z3,z7,z5]),(0,[z0,z518,z1,z2,z3,z7,z5]),(0,[z0,z1,z2,z18,z3,z7,z5]),(0,[z0,z1,z2,z3,z7,z519,z5]),(0,[z0,z1,z2,z3,z7,z520,z5]),(0,[z0,z1,z2,z3,z7,z34,z53])],[(0,[z15,z0,z1,z2,z3,z7,z39]),(0,[z521,z0,z1,z2,z3,z7,z5]),(0,[z0,z522,z1,z2,z3,z7,z5])],[(0,[z0,z1,z2,z3,z523,z7,z5]),(0,[z55,z0,z1,z2,z3,z7,z5]),(0,[z0,z65,z1,z2,z3,z7,z283]),(0,[z0,z1,z2,z524,z3,z7,z5]),(0,[z0,z11,z1,z2,z3,z7,z88]),(0,[z0,z1,z2,z3,z7,z34,z71]),(1,[z0,z1,z2,z3,z7,z492])],[(1,[z0,z102,z1,z2,z3,z7]),(0,[z0,z1,z525,z2,z3,z7,z5]),(0,[z258,z0,z1,z2,z3,z7,z39]),(0,[z0,z392,z1,z2,z3,z7,z5]),(0,[z0,z1,z2,z3,z7,z14,z373])],[(0,[z526,z0,z1,z2,z3,z7,z5]),(0,[z527,z0,z1,z2,z3,z7,z5]),(0,[z0,z528,z1,z2,z3,z7,z5]),(0,[z0,z1,z529,z2,z3,z7,z5]),(0,[z0,z296,z1,z2,z3,z7,z5]),(1,[z0,z1,z2,z3,z7,z320])]],
   [[(0,[z530,z0,z1,z2,z3,z7,z5]),(0,[z0,z531,z1,z2,z3,z7,z5]),(0,[z0,z532,z1,z2,z3,z7,z5]),(0,[z0,z1,z2,z3,z533,z7,z5]),(0,[z0,z1,z2,z3,z160,z7,z5]),(0,[z0,z263,z1,z2,z3,z7,z39]),(1,[z0,z11,z1,z7,z71,z5]),(0,[z0,z1,z2,z534,z3,z7,z5])],[(0,[z0,z535,z1,z2,z3,z7,z5]),(0,[z54,z0,z1,z2,z3,z7,z39]),(1,[z0,z1,z460,z3,z7,z5]),(1,[z0,z1,z2,z367,z7,z5]),(0,[z0,z1,z2,z3,z536,z7,z5]),(0,[z0,z537,z1,z2,z3,z7,z5]),(0,[z0,z1,z2,z114,z3,z7,z34]),(0,[z0,z1,z2,z3,z7,z5,z39]),(0,[z0,z305,z1,z2,z3,z7,z5])],[(0,[z0,z87,z1,z2,z28,z3,z7]),(0,[z538,z0,z1,z2,z3,z7,z5]),(0,[z0,z1,z2,z539,z3,z7,z5])],[(0,[z0,z1,z38,z2,z3,z7,z14]),(0,[z85,z0,z381,z2,z3,z7,z5]),(0,[z0,z341,z1,z2,z3,z148,z5]),(0,[z1,z2,z3,z7,z56,z5,z133]),(0,[z0,z540,z1,z2,z3,z7,z5]),(1,[z0,z1,z2,z3,z7,z466]),(0,[z0,z1,z2,z18,z3,z7,z14]),(0,[z0,z541,z1,z2,z3,z7,z5])],[(1,[z0,z1,z2,z77,z7,z5]),(0,[z0,z542,z1,z2,z3,z7,z5]),(0,[z0,z1,z70,z162,z3,z7,z5]),(0,[z0,z1,z2,z40,z7,z280,z5]),(0,[z0,z366,z1,z2,z3,z7,z165]),(0,[z0,z1,z2,z3,z7,z543,z5]),(0,[z0,z1,z544,z2,z3,z7,z5]),(0,[z0,z545,z1,z2,z3,z7,z5])],[(0,[z0,z1,z2,z3,z112,z7,z5]),(0,[z546,z0,z1,z2,z3,z7,z5]),(0,[z0,z1,z547,z2,z3,z7,z5]),(0,[z55,z0,z1,z2,z3,z7,z14]),(0,[z0,z27,z1,z2,z3,z7,z39]),(0,[z0,z175,z1,z2,z3,z7,z71]),(0,[z0,z1,z2,z218,z3,z7,z39]),(0,[z0,z1,z2,z3,z7,z5,z548])],[(0,[z0,z1,z2,z3,z549,z7,z5]),(0,[z0,z1,z2,z3,z7,z292,z5]),(0,[z0,z1,z2,z3,z117,z7,z5])],[(0,[z0,z550,z1,z2,z3,z7,z5]),(0,[z0,z1,z551,z2,z3,z7,z5]),(0,[z0,z552,z1,z2,z3,z7,z5]),(0,[z0,z1,z2,z114,z3,z7,z5]),(0,[z0,z138,z1,z2,z3,z79,z5])]],
   [[(0,[z0,z1,z2,z3,z165,z225,z5])],[(0,[z116,z0,z1,z2,z3,z324,z5]),(0,[z141,z0,z1,z2,z3,z7,z34]),(0,[z0,z1,z553,z2,z3,z7,z5]),(0,[z0,z1,z2,z3,z160,z165,z5]),(0,[z0,z1,z2,z3,z7,z25,z5]),(0,[z0,z17,z2,z3,z7,z280,z5])],[(0,[z52,z1,z38,z2,z3,z7,z5]),(0,[z0,z102,z1,z38,z2,z3,z7]),(1,[z0,z1,z2,z351,z7,z5]),(0,[z554,z0,z1,z2,z3,z7,z5]),(0,[z0,z87,z1,z2,z16,z3,z7]),(0,[z0,z522,z1,z2,z3,z7,z39]),(0,[z0,z341,z1,z2,z3,z7,z34])],[(0,[z0,z1,z2,z555,z3,z7,z5])],[(0,[z0,z1,z2,z556,z3,z7,z5]),(0,[z0,z1,z2,z3,z7,z557,z5])],[],[(1,[z116,z38,z2,z3,z7,z5]),(0,[z0,z1,z2,z558,z3,z7,z5]),(0,[z0,z1,z2,z3,z160,z7,z39]),(0,[z0,z1,z2,z3,z7,z5,z559]),(0,[z0,z1,z2,z3,z7,z5,z370]),(0,[z0,z560,z1,z2,z3,z7,z34]),(0,[z0,z1,z2,z3,z7,z561,z5])],[(0,[z141,z0,z1,z2,z3,z7,z5]),(0,[z0,z1,z2,z3,z7,z562,z5]),(0,[z0,z1,z2,z3,z7,z105,z5]),(0,[z0,z1,z2,z3,z7,z563,z5]),(1,[z0,z1,z2,z3,z129,z7]),(0,[z0,z1,z2,z3,z7,z564,z5]),(0,[z0,z1,z565,z2,z3,z7,z5]),(0,[z0,z1,z19,z2,z3,z7,z344]),(0,[z0,z1,z2,z339,z3,z7,z5])]],
   [[(0,[z0,z566,z1,z2,z3,z7,z5]),(0,[z0,z1,z2,z3,z7,z567,z5]),(0,[z0,z138,z1,z19,z3,z7,z5]),(0,[z0,z1,z2,z3,z7,z463,z5]),(0,[z0,z341,z1,z2,z3,z7,z5])],[(1,[z113,z1,z2,z40,z7,z5]),(1,[z0,z568,z2,z3,z7,z5]),(0,[z0,z569,z1,z2,z3,z7,z5]),(0,[z0,z1,z2,z3,z570,z7,z5]),(1,[z0,z1,z2,z3,z7,z446])],[(0,[z0,z1,z2,z3,z7,z571,z5]),(0,[z0,z1,z2,z572,z3,z7,z5]),(0,[z0,z573,z1,z2,z3,z7,z5]),(0,[z0,z1,z2,z3,z7,z574,z5]),(0,[z0,z78,z1,z2,z16,z3,z7]),(0,[z0,z1,z2,z3,z7,z71,z5])],[(0,[z575,z0,z1,z2,z3,z7,z5]),(0,[z0,z65,z1,z30,z3,z7,z5]),(0,[z0,z1,z2,z3,z576,z7,z5]),(0,[z113,z0,z1,z2,z3,z7,z34]),(0,[z0,z577,z1,z2,z3,z7,z5]),(0,[z578,z0,z1,z2,z3,z7,z5]),(0,[z0,z1,z2,z3,z7,z5,z579]),(0,[z0,z580,z1,z2,z3,z7,z5])],[(0,[z0,z1,z2,z581,z3,z7,z5]),(0,[z582,z0,z1,z2,z3,z7,z5]),(0,[z0,z1,z2,z3,z79,z148,z5]),(0,[z0,z174,z1,z2,z3,z148,z5]),(1,[z55,z1,z2,z3,z7,z133]),(0,[z0,z583,z1,z2,z3,z7,z5]),(0,[z0,z1,z2,z3,z7,z56,z39]),(0,[z0,z1,z2,z208,z3,z160,z7]),(0,[z0,z1,z2,z3,z7,z584,z5]),(0,[z0,z560,z1,z2,z3,z7,z5])],[(0,[z0,z1,z585,z2,z3,z7,z5]),(0,[z0,z1,z2,z114,z3,z7,z39]),(0,[z0,z91,z1,z2,z3,z7,z39]),(0,[z0,z1,z586,z2,z3,z7,z5]),(0,[z0,z91,z1,z2,z67,z7,z5]),(0,[z0,z1,z2,z3,z7,z14,z173])],[(0,[z0,z201,z52,z2,z3,z7,z5]),(1,[z0,z1,z2,z199,z3,z7]),(0,[z0,z1,z2,z3,z7,z5,z173]),(0,[z0,z175,z1,z2,z16,z3,z7])],[(0,[z587,z0,z1,z2,z3,z7,z5]),(0,[z0,z1,z2,z3,z7,z5,z588]),(0,[z0,z1,z2,z3,z7,z226,z5]),(0,[z0,z138,z1,z2,z3,z7,z39]),(0,[z0,z1,z19,z3,z79,z7,z5]),(0,[z0,z1,z2,z28,z3,z7,z34])]],
   [[(0,[z0,z1,z2,z3,z62,z7,z39]),(0,[z0,z568,z1,z2,z3,z7,z5]),(0,[z0,z1,z2,z3,z589,z7,z5]),(0,[z0,z1,z590,z2,z3,z7,z5]),(0,[z0,z1,z2,z16,z7,z5,z14]),(0,[z0,z1,z2,z3,z7,z5,z506])],[(0,[z0,z1,z2,z3,z7,z455,z5]),(0,[z0,z91,z1,z2,z62,z7,z5]),(0,[z0,z341,z1,z2,z3,z165,z5]),(0,[z0,z1,z2,z3,z7,z5,z591]),(0,[z0,z592,z1,z2,z3,z7,z5]),(0,[z0,z593,z1,z2,z3,z7,z5])],[(0,[z0,z1,z12,z30,z3,z7,z5]),(0,[z0,z1,z460,z2,z3,z7,z5]),(0,[z0,z24,z1,z2,z16,z3,z7]),(0,[z0,z594,z1,z2,z3,z7,z5]),(0,[z595,z0,z1,z2,z3,z7,z5]),(0,[z0,z1,z2,z3,z7,z71,z14]),(0,[z596,z0,z1,z2,z3,z7,z5]),(0,[z0,z1,z19,z2,z3,z7,z492]),(1,[z0,z1,z2,z3,z7,z39]),(0,[z0,z89,z1,z3,z7,z34,z5])],[(0,[z0,z1,z2,z3,z7,z5,z422]),(0,[z0,z24,z2,z162,z3,z7,z5]),(0,[z0,z17,z1,z2,z7,z280,z5]),(0,[z0,z1,z2,z3,z7,z5,z597]),(0,[z0,z598,z1,z2,z3,z7,z5]),(0,[z0,z1,z2,z3,z7,z5,z599]),(0,[z0,z1,z2,z3,z79,z7,z34]),(0,[z0,z174,z1,z2,z3,z7,z34])],[(0,[z116,z0,z1,z2,z3,z7,z34]),(0,[z0,z1,z2,z16,z3,z7,z165]),(0,[z0,z1,z2,z3,z148,z7,z34]),(0,[z0,z65,z24,z1,z3,z7,z5]),(0,[z0,z600,z1,z2,z3,z7,z5]),(0,[z0,z1,z2,z3,z7,z601,z5]),(0,[z0,z1,z2,z3,z602,z7,z34])],[(0,[z141,z0,z1,z2,z3,z7,z39]),(0,[z0,z1,z2,z3,z7,z603,z5]),(0,[z0,z1,z2,z162,z3,z7,z34]),(0,[z0,z604,z1,z2,z3,z7,z5]),(0,[z0,z605,z1,z2,z3,z7,z5]),(0,[z0,z1,z2,z28,z3,z7,z5]),(0,[z0,z1,z2,z3,z9,z5,z51]),(0,[z606,z0,z1,z2,z3,z7,z5])],[(0,[z0,z1,z2,z16,z40,z3,z7]),(0,[z607,z0,z1,z2,z3,z7,z5]),(0,[z0,z341,z1,z2,z3,z7,z39])],[(0,[z83,z0,z1,z2,z16,z3,z7]),(0,[z0,z2,z18,z3,z7,z280,z5]),(0,[z0,z1,z2,z3,z7,z73,z39]),(0,[z0,z1,z2,z608,z3,z7,z5])]],
   [[(0,[z0,z1,z2,z62,z7,z280,z5]),(0,[z55,z1,z2,z3,z7,z5,z133]),(0,[z0,z609,z1,z2,z3,z7,z5]),(0,[z0,z1,z2,z610,z3,z7,z5])],[(0,[z0,z1,z2,z611,z3,z7,z5]),(0,[z113,z0,z1,z2,z3,z7,z14]),(1,[z0,z1,z2,z40,z7,z14]),(0,[z0,z1,z2,z3,z612,z7,z5]),(0,[z0,z1,z2,z3,z79,z7,z5]),(0,[z0,z174,z1,z2,z3,z7,z5]),(0,[z613,z0,z1,z2,z3,z7,z5])],[(0,[z116,z0,z1,z2,z3,z7,z5]),(0,[z0,z1,z70,z2,z3,z7,z39]),(0,[z0,z1,z2,z3,z148,z7,z5]),(0,[z0,z1,z2,z614,z3,z7,z5]),(0,[z0,z1,z2,z199,z3,z7,z5]),(0,[z0,z1,z2,z615,z3,z7,z5]),(0,[z0,z1,z2,z3,z616,z7,z5]),(0,[z0,z1,z2,z3,z602,z7,z5])],[(0,[z0,z1,z2,z617,z3,z7,z5]),(0,[z0,z1,z2,z162,z3,z7,z5]),(0,[z0,z1,z385,z2,z3,z7,z5])],[(0,[z0,z1,z2,z618,z3,z7,z5]),(0,[z0,z1,z2,z3,z7,z280,z5]),(1,[z0,z1,z2,z150,z3,z7])],[(0,[z0,z1,z2,z3,z7,z5,z394]),(1,[z0,z17,z2,z7,z280,z5]),(0,[z0,z201,z1,z2,z3,z7,z119]),(0,[z0,z1,z2,z3,z7,z619,z5]),(0,[z0,z1,z2,z3,z7,z620,z5]),(0,[z0,z1,z2,z28,z3,z7,z14])],[(1,[z0,z1,z2,z62,z7,z14]),(0,[z0,z78,z1,z2,z7,z280,z5]),(0,[z0,z1,z2,z621,z3,z7,z5]),(0,[z0,z1,z2,z622,z3,z7,z5]),(0,[z0,z1,z623,z2,z3,z7,z5]),(0,[z0,z624,z1,z2,z3,z7,z5]),(0,[z0,z1,z2,z3,z7,z5,z46])],[(0,[z0,z1,z2,z3,z7,z5,z356]),(0,[z0,z1,z2,z3,z625,z7,z5]),(1,[z0,z1,z2,z3,z7,z370]),(0,[z0,z1,z19,z2,z3,z79,z5]),(0,[z0,z45,z1,z2,z3,z7,z39]),(1,[z0,z1,z2,z242,z3,z7]),(0,[z0,z1,z2,z3,z7,z34,z34])]],
   [[(0,[z0,z1,z2,z3,z626,z7,z5]),(0,[z0,z1,z627,z2,z3,z7,z5]),(0,[z0,z1,z2,z16,z18,z3,z7]),(0,[z0,z201,z1,z2,z3,z7,z34])],[(0,[z0,z138,z1,z2,z3,z20,z5]),(0,[z0,z174,z1,z2,z3,z7,z14]),(0,[z0,z1,z2,z16,z3,z9,z7])],[(0,[z85,z0,z1,z2,z62,z7,z5]),(0,[z1,z2,z40,z3,z62,z7,z5]),(0,[z0,z1,z2,z3,z79,z165,z5]),(0,[z0,z174,z1,z2,z3,z165,z5]),(0,[z0,z1,z2,z628,z3,z7,z5]),(0,[z0,z1,z2,z3,z148,z7,z14]),(0,[z0,z1,z2,z3,z7,z133,z39]),(0,[z0,z1,z2,z3,z7,z35,z14]),(0,[z0,z1,z2,z3,z7,z82,z5])],[(0,[z0,z27,z38,z2,z3,z7,z5]),(0,[z0,z45,z1,z2,z62,z7,z5]),(0,[z0,z1,z2,z3,z7,z66,z5]),(0,[z0,z629,z1,z2,z3,z7,z5])],[(0,[z0,z630,z1,z2,z3,z7,z5]),(1,[z0,z1,z2,z3,z7,z86]),(0,[z0,z1,z2,z3,z7,z631,z5]),(0,[z632,z0,z1,z2,z3,z7,z5]),(0,[z0,z1,z2,z3,z7,z446,z5])],[(0,[z0,z1,z2,z3,z633,z7,z5]),(0,[z55,z0,z355,z2,z3,z7,z5]),(0,[z0,z1,z2,z634,z3,z7,z5]),(0,[z0,z1,z2,z3,z7,z5,z466]),(0,[z0,z89,z1,z37,z3,z7,z5]),(0,[z0,z1,z2,z3,z7,z34,z5]),(0,[z0,z635,z1,z2,z3,z7,z5])],[(0,[z0,z78,z38,z2,z3,z7,z5]),(0,[z0,z636,z1,z2,z3,z7,z5]),(0,[z0,z78,z2,z18,z3,z7,z5]),(0,[z0,z201,z1,z2,z3,z7,z5]),(0,[z637,z0,z1,z2,z3,z7,z5])],[(0,[z638,z0,z1,z2,z3,z7,z5]),(0,[z0,z1,z2,z3,z79,z7,z39]),(0,[z0,z1,z2,z3,z7,z639,z5]),(0,[z0,z499,z1,z2,z3,z7,z5])]],
   [[(0,[z116,z0,z1,z2,z3,z7,z39]),(1,[z0,z263,z2,z3,z73,z5]),(0,[z0,z1,z2,z640,z3,z7,z5]),(0,[z0,z1,z2,z3,z7,z641,z5]),(0,[z0,z1,z2,z3,z7,z251,z5]),(0,[z0,z642,z1,z2,z3,z7,z5]),(0,[z0,z1,z2,z3,z7,z643,z5])],[(0,[z0,z1,z2,z162,z3,z7,z39]),(0,[z644,z0,z1,z2,z3,z7,z5]),(0,[z0,z1,z2,z3,z645,z7,z5]),(0,[z0,z87,z1,z2,z3,z7,z14]),(1,[z0,z1,z114,z3,z7,z39]),(0,[z0,z138,z1,z2,z3,z7,z599]),(0,[z0,z1,z2,z3,z7,z51,z14]),(0,[z267,z0,z1,z2,z16,z3,z7])],[(0,[z0,z1,z190,z2,z3,z7,z5]),(0,[z0,z1,z646,z2,z3,z7,z5]),(0,[z647,z0,z1,z2,z3,z7,z5]),(0,[z0,z1,z2,z3,z7,z280,z39]),(0,[z648,z0,z1,z2,z3,z7,z5]),(0,[z0,z1,z2,z3,z649,z7,z5]),(0,[z650,z0,z1,z2,z3,z7,z34])],[(0,[z0,z651,z1,z2,z3,z7,z5]),(0,[z652,z0,z1,z2,z3,z7,z5]),(0,[z0,z1,z2,z3,z7,z5,z653]),(0,[z0,z654,z1,z2,z3,z7,z5]),(0,[z0,z1,z2,z3,z7,z655,z5]),(0,[z0,z656,z1,z2,z3,z7,z5])],[(0,[z15,z1,z2,z3,z7,z165,z5]),(0,[z0,z1,z2,z3,z165,z73,z5]),(1,[z0,z1,z2,z3,z7,z599]),(0,[z0,z657,z1,z2,z3,z7,z5]),(0,[z0,z1,z658,z2,z3,z7,z5])],[(0,[z659,z0,z1,z2,z3,z7,z5]),(0,[z0,z1,z2,z40,z7,z71,z5]),(0,[z0,z1,z2,z660,z3,z7,z5]),(0,[z0,z1,z2,z3,z7,z661,z5]),(0,[z0,z1,z2,z3,z7,z71,z173]),(0,[z0,z1,z2,z3,z7,z34,z14]),(0,[z0,z1,z2,z3,z7,z662,z5])],[(0,[z0,z1,z70,z3,z7,z71,z5]),(0,[z32,z0,z1,z2,z3,z148,z5]),(0,[z663,z0,z1,z2,z3,z7,z5]),(0,[z0,z1,z2,z3,z7,z664,z5]),(0,[z0,z201,z1,z2,z3,z7,z14]),(0,[z665,z0,z1,z2,z3,z7,z5]),(2,[z0,z1,z2,z7,z82])],[(0,[z0,z666,z1,z2,z3,z7,z5]),(0,[z667,z0,z1,z2,z3,z7,z5]),(0,[z0,z668,z1,z2,z3,z7,z5]),(0,[z0,z1,z2,z3,z7,z669,z5]),(0,[z0,z1,z19,z2,z3,z7,z39]),(0,[z0,z1,z2,z3,z7,z471,z39])]],
   [[(0,[z83,z0,z1,z2,z3,z7,z34]),(0,[z0,z1,z2,z3,z7,z670,z5]),(0,[z0,z1,z2,z671,z3,z7,z5]),(0,[z0,z672,z1,z2,z3,z7,z5]),(0,[z0,z1,z2,z3,z7,z673,z5]),(0,[z0,z1,z2,z3,z7,z88,z5]),(0,[z650,z0,z1,z2,z3,z7,z5])],[(0,[z674,z0,z1,z2,z3,z7,z5]),(0,[z0,z1,z2,z3,z7,z675,z5]),(0,[z0,z1,z2,z3,z7,z231,z5]),(0,[z15,z0,z1,z2,z3,z7,z92]),(0,[z0,z11,z91,z1,z2,z7,z5])],[(1,[z0,z381,z2,z3,z7,z5]),(0,[z0,z1,z2,z3,z7,z5,z676]),(0,[z0,z677,z1,z2,z3,z7,z5]),(0,[z0,z1,z2,z3,z7,z678,z5]),(1,[z0,z138,z1,z3,z20,z5]),(0,[z0,z1,z2,z679,z3,z7,z5])],[(0,[z0,z1,z2,z16,z3,z7,z280]),(0,[z0,z1,z2,z680,z3,z7,z5]),(0,[z0,z1,z2,z3,z7,z681,z5]),(0,[z0,z682,z1,z2,z3,z7,z5]),(0,[z0,z1,z2,z683,z3,z7,z5])],[(0,[z0,z1,z2,z684,z3,z7,z5]),(0,[z0,z332,z1,z2,z3,z7,z5]),(0,[z0,z1,z2,z3,z7,z685,z5]),(0,[z0,z1,z2,z3,z7,z5,z686]),(0,[z0,z263,z2,z3,z7,z73,z5]),(0,[z0,z1,z687,z2,z3,z7,z5]),(1,[z0,z1,z2,z7,z34,z82]),(0,[z0,z688,z1,z2,z3,z7,z5]),(0,[z298,z0,z1,z2,z16,z3,z7])],[(0,[z32,z0,z1,z2,z3,z7,z34]),(0,[z0,z1,z2,z3,z7,z689,z5])],[(0,[z116,z0,z1,z220,z3,z7,z5]),(0,[z0,z1,z2,z3,z271,z7,z5]),(0,[z0,z1,z2,z3,z7,z5,z285]),(0,[z55,z0,z1,z2,z351,z7,z5]),(0,[z0,z690,z1,z2,z3,z7,z5]),(0,[z0,z1,z12,z2,z16,z3,z7]),(0,[z0,z1,z2,z3,z7,z643,z39]),(0,[z0,z1,z2,z3,z7,z5,z691])],[(0,[z0,z1,z2,z3,z7,z692,z5]),(0,[z15,z0,z1,z2,z117,z7,z5]),(0,[z0,z693,z1,z2,z3,z7,z5]),(0,[z0,z174,z1,z2,z3,z7,z35]),(1,[z0,z1,z2,z3,z7,z46])]],
   [[(1,[z0,z1,z2,z3,z7,z356]),(0,[z0,z694,z1,z2,z3,z7,z5]),(0,[z0,z1,z12,z2,z7,z71,z5]),(0,[z0,z341,z1,z2,z7,z225,z5])],[(0,[z0,z0,z1,z2,z3,z7,z5]),(0,[z0,z1,z12,z70,z3,z7,z5]),(0,[z0,z24,z1,z2,z3,z7,z14]),(0,[z0,z1,z2,z695,z3,z7,z5]),(0,[z0,z1,z2,z2,z3,z7,z39]),(0,[z0,z174,z1,z2,z3,z7,z51])],[(0,[z696,z0,z1,z2,z3,z7,z5]),(0,[z85,z0,z1,z2,z3,z7,z125]),(0,[z0,z1,z2,z3,z7,z697,z5]),(0,[z8,z0,z1,z2,z3,z7,z39]),(0,[z0,z1,z2,z3,z7,z5,z698]),(0,[z0,z699,z1,z2,z3,z7,z5]),(0,[z0,z120,z1,z2,z16,z3,z7]),(0,[z0,z263,z1,z2,z3,z73,z5]),(0,[z0,z1,z2,z150,z3,z7,z5])],[(0,[z0,z38,z2,z3,z7,z73,z5]),(0,[z32,z0,z1,z2,z3,z7,z5]),(0,[z0,z1,z2,z16,z3,z7,z133]),(1,[z0,z27,z2,z3,z7,z35]),(0,[z0,z700,z1,z2,z3,z7,z5]),(0,[z0,z1,z2,z3,z7,z701,z5]),(0,[z0,z1,z2,z702,z3,z7,z5])],[(0,[z0,z1,z2,z3,z7,z5,z703])],[(0,[z55,z0,z568,z2,z3,z7,z5])],[(0,[z83,z0,z1,z2,z3,z7,z14]),(0,[z0,z1,z2,z3,z148,z225,z5]),(0,[z0,z1,z704,z2,z3,z7,z5]),(0,[z0,z1,z2,z218,z3,z7,z110]),(0,[z0,z1,z2,z3,z7,z5,z247]),(0,[z0,z1,z2,z705,z3,z7,z5])],[(0,[z706,z0,z1,z2,z3,z7,z5]),(0,[z0,z1,z2,z3,z165,z20,z5]),(0,[z0,z87,z1,z2,z3,z7,z35]),(0,[z80,z0,z1,z2,z3,z7,z5]),(1,[z0,z45,z341,z1,z2,z5])]]]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkB : List (List (List (ℕ × List W))) :=
  [[[(0,[z0,z1,z220,z3,z4,z5]),(0,[z0,z1,z2,z112,z7,z14]),(0,[z0,z1,z2,z3,z7,z31]),(0,[z0,z1,z707,z3,z7,z5]),(0,[z0,z1,z3,z7,z34,z559])],[(0,[z85,z1,z159,z62,z7,z5]),(0,[z0,z109,z1,z3,z7,z39]),(0,[z0,z11,z1,z2,z7,z82])],[(0,[z0,z1,z38,z147,z3,z7]),(0,[z505,z1,z70,z3,z7,z5]),(0,[z0,z1,z2,z117,z165,z5]),(0,[z0,z1,z235,z16,z3,z7]),(0,[z0,z1,z2,z708,z7,z5]),(0,[z0,z1,z2,z3,z709,z34]),(0,[z0,z1,z2,z16,z7,z82]),(0,[z0,z195,z1,z2,z16,z7])],[(0,[z0,z1,z301,z3,z7,z196]),(0,[z0,z1,z710,z3,z7,z5]),(0,[z0,z1,z2,z3,z7,z711]),(0,[z0,z1,z166,z3,z7,z34]),(0,[z0,z1,z2,z351,z7,z56]),(0,[z0,z1,z2,z3,z7,z712]),(0,[z0,z1,z2,z3,z9,z427]),(0,[z0,z45,z341,z1,z2,z16])],[(0,[z0,z1,z2,z3,z7,z713]),(0,[z0,z1,z2,z714,z7,z5]),(0,[z0,z1,z2,z715,z3,z7]),(0,[z0,z1,z23,z3,z7,z5]),(0,[z0,z1,z159,z3,z231,z5]),(0,[z8,z0,z1,z2,z7,z82])],[],[(0,[z0,z38,z2,z3,z324,z5]),(0,[z0,z716,z1,z2,z3,z7]),(0,[z0,z1,z127,z717,z3,z7]),(0,[z718,z1,z2,z3,z7,z5]),(0,[z0,z1,z2,z3,z7,z719]),(0,[z0,z211,z1,z3,z7,z88]),(0,[z0,z138,z1,z16,z3,z20]),(0,[z0,z1,z37,z3,z7,z39]),(0,[z0,z720,z2,z3,z7,z14])],[(0,[z0,z1,z2,z40,z7,z371]),(0,[z0,z721,z1,z2,z3,z7]),(0,[z55,z135,z1,z2,z3,z7]),(0,[z0,z174,z1,z2,z395,z3]),(0,[z0,z11,z89,z1,z7,z14]),(0,[z0,z1,z2,z3,z7,z722]),(0,[z0,z1,z385,z2,z7,z82])],[(0,[z0,z1,z2,z723,z7,z5]),(0,[z0,z1,z2,z3,z7,z724]),(0,[z368,z52,z2,z3,z7,z5]),(0,[z0,z1,z2,z3,z7,z725]),(0,[z0,z726,z1,z2,z3,z7])],[(0,[z0,z1,z727,z3,z7,z5]),(0,[z0,z27,z2,z3,z7,z692]),(0,[z0,z1,z2,z3,z142,z14]),(0,[z0,z1,z2,z3,z7,z728]),(0,[z0,z305,z2,z3,z7,z35]),(0,[z0,z1,z12,z3,z7,z371]),(0,[z0,z174,z1,z2,z729,z3])],[(0,[z0,z730,z2,z3,z7,z5]),(0,[z0,z731,z1,z2,z3,z7]),(0,[z0,z1,z732,z3,z7,z5])],[(0,[z0,z1,z2,z733,z112,z7]),(0,[z0,z1,z2,z3,z7,z734]),(0,[z0,z202,z2,z3,z7,z125]),(0,[z0,z265,z1,z2,z28,z3]),(0,[z0,z1,z2,z3,z7,z86])],[(0,[z0,z96,z2,z84,z7,z5]),(0,[z0,z1,z23,z3,z7,z14]),(0,[z0,z1,z2,z3,z7,z735]),(0,[z0,z2,z3,z736,z73,z5]),(0,[z0,z201,z2,z3,z160,z119])],[(0,[z0,z201,z2,z3,z160,z328]),(0,[z0,z737,z1,z2,z3,z34])],[(0,[z0,z1,z2,z84,z105,z5]),(0,[z0,z1,z171,z147,z3,z7])],[(0,[z0,z332,z355,z2,z3,z7]),(0,[z0,z1,z2,z3,z7,z738]),(0,[z0,z1,z2,z3,z7,z106]),(0,[z0,z201,z2,z3,z160,z34])]],
   [[(0,[z85,z1,z2,z62,z7,z125]),(0,[z0,z1,z2,z611,z225,z5]),(0,[z0,z739,z2,z3,z7,z5]),(0,[z0,z1,z235,z3,z167,z5]),(0,[z0,z1,z2,z3,z7,z740])],[(0,[z0,z1,z2,z3,z7,z741]),(0,[z0,z1,z2,z107,z7,z14]),(1,[z0,z1,z717,z3,z7]),(0,[z0,z1,z2,z3,z7,z742]),(0,[z0,z1,z2,z743,z3,z7])],[(0,[z0,z1,z2,z3,z7,z744]),(0,[z0,z694,z65,z3,z7,z5]),(0,[z0,z745,z1,z2,z3,z7]),(0,[z0,z746,z2,z3,z7,z5]),(0,[z0,z1,z42,z3,z7,z39]),(0,[z0,z17,z2,z7,z280,z39])],[(0,[z0,z190,z2,z3,z7,z5]),(0,[z747,z1,z2,z3,z7,z5]),(0,[z0,z1,z147,z3,z7,z280])],[(0,[z0,z1,z2,z7,z224,z82]),(0,[z0,z1,z2,z729,z3,z9])],[(0,[z0,z1,z2,z3,z7,z748]),(0,[z0,z1,z2,z16,z3,z231]),(0,[z0,z1,z2,z3,z749,z7])],[(0,[z0,z1,z2,z3,z7,z750]),(0,[z0,z1,z2,z16,z84,z7]),(0,[z0,z1,z2,z751,z7,z5]),(1,[z0,z1,z147,z3,z7]),(0,[z0,z1,z12,z114,z7,z66]),(1,[z0,z1,z2,z752,z7])],[(0,[z0,z753,z1,z2,z3,z7]),(0,[z0,z1,z2,z3,z7,z754]),(0,[z0,z1,z2,z3,z7,z755]),(0,[z0,z138,z1,z3,z756,z5]),(0,[z0,z1,z2,z7,z82,z463])],[(0,[z0,z1,z10,z3,z7,z39]),(0,[z0,z134,z1,z147,z3,z7]),(0,[z0,z511,z1,z2,z16,z7])],[(0,[z0,z52,z2,z271,z7,z5]),(0,[z0,z1,z2,z3,z7,z757]),(0,[z0,z355,z2,z351,z7,z5]),(0,[z0,z1,z2,z3,z7,z758]),(0,[z0,z1,z2,z3,z7,z759]),(0,[z475,z1,z2,z3,z7,z471])],[(0,[z52,z760,z2,z3,z7,z5]),(0,[z0,z1,z2,z3,z761,z5]),(0,[z0,z1,z2,z660,z7,z14])],[(0,[z0,z1,z2,z762,z3,z5]),(0,[z0,z78,z2,z111,z7,z5]),(0,[z0,z190,z2,z3,z7,z14]),(0,[z0,z1,z2,z40,z7,z173]),(0,[z0,z1,z147,z3,z7,z133]),(0,[z0,z195,z1,z7,z34,z39])],[(0,[z0,z1,z2,z112,z7,z132]),(0,[z0,z1,z159,z3,z7,z292]),(0,[z0,z222,z2,z16,z3,z7]),(0,[z0,z1,z2,z3,z763,z5])],[(0,[z141,z52,z2,z3,z7,z5]),(0,[z0,z1,z2,z764,z3,z7]),(0,[z0,z1,z2,z765,z3,z7]),(0,[z0,z1,z2,z3,z7,z766]),(0,[z0,z263,z2,z3,z73,z39]),(0,[z0,z1,z2,z3,z7,z82]),(0,[z0,z767,z1,z2,z7,z82])],[(0,[z0,z1,z343,z3,z7,z34])],[(0,[z0,z1,z768,z3,z7,z5]),(0,[z0,z1,z2,z3,z7,z769]),(0,[z0,z128,z1,z3,z20,z5]),(0,[z0,z1,z2,z3,z129,z167]),(0,[z0,z1,z770,z3,z7,z5]),(1,[z0,z195,z1,z7,z39]),(0,[z0,z341,z1,z147,z3,z7])]],
   [[(0,[z0,z1,z2,z771,z367,z7]),(0,[z0,z45,z341,z1,z2,z34])],[(0,[z0,z1,z2,z117,z7,z422]),(0,[z0,z1,z627,z3,z7,z39]),(0,[z0,z120,z1,z147,z3,z7]),(0,[z0,z11,z1,z608,z7,z5]),(0,[z0,z1,z242,z114,z3,z7])],[(0,[z15,z222,z2,z3,z165,z5])],[(0,[z0,z52,z301,z3,z7,z5]),(0,[z0,z1,z2,z271,z7,z772]),(0,[z0,z1,z2,z3,z7,z773]),(0,[z0,z1,z235,z3,z244,z5]),(0,[z0,z1,z2,z3,z7,z774])],[(0,[z0,z1,z717,z40,z3,z7]),(0,[z0,z1,z2,z775,z3,z7]),(0,[z0,z1,z776,z3,z7,z5]),(0,[z0,z78,z2,z18,z7,z217]),(0,[z0,z1,z19,z3,z79,z492])],[(0,[z141,z52,z2,z3,z7,z14]),(0,[z0,z1,z2,z3,z142,z132]),(0,[z0,z499,z2,z3,z7,z44])],[(0,[z0,z24,z162,z3,z7,z25]),(0,[z0,z1,z2,z3,z7,z777])],[(0,[z0,z175,z1,z2,z3,z7]),(0,[z0,z138,z1,z3,z20,z39])],[(0,[z0,z1,z2,z3,z231,z14]),(0,[z0,z1,z2,z3,z778,z7]),(0,[z0,z1,z2,z3,z7,z779]),(0,[z0,z780,z1,z2,z7,z82])],[(0,[z0,z1,z22,z3,z7,z5]),(0,[z0,z1,z2,z16,z3,z142]),(0,[z0,z781,z2,z3,z7,z5]),(0,[z0,z1,z235,z3,z7,z14]),(0,[z0,z1,z2,z3,z7,z782]),(0,[z0,z1,z147,z3,z7,z73]),(0,[z0,z11,z1,z7,z71,z88])],[(0,[z0,z1,z2,z3,z7,z783]),(0,[z0,z1,z137,z3,z7,z39])],[(0,[z0,z1,z2,z3,z97,z5]),(0,[z0,z45,z341,z1,z2,z446])],[(0,[z0,z1,z2,z784,z7,z5]),(0,[z0,z1,z2,z3,z7,z785]),(0,[z0,z1,z2,z3,z7,z786]),(0,[z0,z27,z403,z2,z3,z7]),(0,[z0,z1,z3,z7,z34,z676]),(0,[z0,z1,z147,z3,z7,z20]),(0,[z0,z1,z2,z7,z787,z82])],[(0,[z0,z1,z2,z3,z7,z196]),(0,[z0,z1,z2,z3,z7,z788]),(0,[z0,z1,z2,z242,z7,z173]),(0,[z0,z1,z2,z3,z7,z789])],[(0,[z0,z790,z24,z3,z7,z5])],[(0,[z0,z1,z2,z3,z7,z791]),(0,[z0,z509,z1,z3,z7,z39])]],
   [[(0,[z0,z1,z2,z3,z792,z5]),(0,[z0,z793,z1,z2,z3,z7]),(0,[z0,z1,z2,z62,z7,z46]),(0,[z0,z1,z235,z272,z7,z5]),(0,[z0,z1,z2,z3,z9,z167]),(0,[z0,z24,z1,z2,z7,z82]),(0,[z0,z305,z296,z2,z3,z7])],[(0,[z0,z1,z794,z3,z7,z5]),(0,[z0,z1,z2,z3,z7,z795]),(0,[z0,z11,z1,z147,z3,z7]),(0,[z0,z1,z2,z3,z389,z81])],[(0,[z0,z1,z2,z7,z796,z5]),(0,[z0,z1,z2,z7,z165,z82]),(0,[z0,z341,z1,z2,z7,z82]),(0,[z0,z1,z2,z16,z752,z7])],[(0,[z0,z1,z2,z3,z97,z14]),(0,[z0,z1,z2,z3,z7,z797]),(0,[z0,z1,z2,z3,z7,z798]),(0,[z0,z1,z2,z3,z799,z7]),(0,[z0,z1,z2,z3,z7,z800]),(0,[z0,z1,z2,z3,z7,z217]),(0,[z0,z1,z2,z16,z615,z7]),(0,[z0,z1,z2,z640,z7,z14]),(0,[z0,z1,z2,z7,z88,z14]),(0,[z0,z1,z2,z9,z7,z82])],[(0,[z0,z52,z2,z3,z324,z5]),(0,[z0,z1,z2,z3,z7,z801]),(0,[z0,z1,z802,z3,z7,z5]),(0,[z0,z803,z2,z3,z7,z5]),(0,[z0,z1,z2,z3,z7,z804]),(0,[z8,z0,z1,z147,z3,z7]),(0,[z0,z1,z2,z162,z7,z82]),(0,[z0,z1,z2,z3,z7,z805]),(0,[z0,z45,z341,z1,z2,z39])],[(0,[z0,z1,z2,z3,z806,z5]),(0,[z0,z1,z2,z807,z3,z7]),(0,[z0,z1,z2,z3,z808,z5]),(0,[z0,z482,z2,z3,z7,z53]),(0,[z0,z1,z2,z3,z7,z809]),(0,[z13,z1,z2,z3,z7,z373])],[(0,[z0,z810,z1,z3,z7,z5]),(0,[z0,z1,z2,z3,z7,z811]),(0,[z0,z1,z2,z702,z7,z14]),(0,[z0,z812,z2,z3,z7,z5])],[(0,[z0,z190,z2,z3,z7,z132]),(0,[z0,z813,z2,z3,z7,z5]),(0,[z0,z1,z385,z147,z3,z7]),(0,[z0,z814,z1,z147,z3,z7])],[(0,[z0,z1,z2,z3,z7,z815]),(0,[z0,z1,z2,z3,z7,z816]),(0,[z83,z1,z30,z3,z7,z34]),(0,[z113,z0,z1,z2,z7,z82]),(0,[z0,z1,z114,z240,z7,z39]),(0,[z0,z1,z2,z817,z3,z7]),(0,[z0,z89,z195,z1,z7,z5]),(0,[z0,z818,z1,z16,z3,z7])],[(0,[z0,z355,z166,z3,z7,z5]),(0,[z0,z1,z2,z819,z3,z7]),(0,[z0,z1,z2,z3,z7,z820]),(0,[z0,z821,z2,z3,z7,z34]),(0,[z0,z45,z1,z2,z7,z82])],[(0,[z0,z822,z2,z3,z7,z5]),(0,[z0,z1,z2,z3,z7,z823]),(0,[z0,z198,z2,z16,z3,z7]),(0,[z352,z0,z1,z2,z7,z14])],[(0,[z1,z2,z3,z824,z165,z5]),(0,[z0,z825,z1,z2,z3,z7]),(0,[z0,z1,z2,z3,z7,z826]),(0,[z0,z1,z2,z827,z7,z5]),(0,[z0,z1,z2,z828,z3,z7]),(0,[z0,z2,z3,z7,z829,z5]),(0,[z0,z1,z2,z3,z7,z830]),(0,[z650,z0,z1,z2,z7,z82]),(0,[z0,z560,z1,z2,z7,z82])],[(0,[z0,z202,z2,z16,z3,z7]),(0,[z0,z1,z23,z367,z7,z5]),(0,[z0,z1,z2,z752,z7,z5])],[],[(0,[z0,z1,z159,z3,z7,z831]),(0,[z0,z1,z2,z3,z7,z832]),(0,[z0,z1,z2,z3,z833,z39]),(0,[z0,z1,z68,z3,z7,z39])],[(0,[z0,z202,z159,z3,z7,z5]),(0,[z0,z1,z834,z3,z7,z5]),(0,[z15,z1,z2,z3,z824,z5]),(0,[z0,z835,z1,z2,z3,z7]),(0,[z0,z2,z3,z7,z836,z5]),(0,[z0,z1,z2,z3,z7,z837])]],
   [[(0,[z0,z1,z2,z3,z7,z838]),(0,[z141,z0,z1,z147,z3,z7]),(0,[z15,z198,z2,z3,z165,z5]),(0,[z0,z839,z1,z2,z3,z7]),(0,[z0,z1,z363,z3,z7,z39]),(0,[z0,z1,z2,z3,z9,z224])],[(0,[z0,z1,z19,z3,z79,z39]),(0,[z0,z1,z3,z7,z840,z5]),(0,[z0,z1,z841,z3,z7,z14]),(0,[z0,z1,z2,z729,z3,z51])],[(0,[z0,z1,z2,z3,z7,z842]),(0,[z0,z1,z2,z3,z7,z843])],[(0,[z0,z1,z159,z3,z7,z34]),(0,[z0,z222,z2,z3,z7,z14]),(0,[z32,z0,z1,z2,z7,z82]),(0,[z0,z1,z2,z3,z7,z844]),(0,[z0,z1,z2,z7,z845,z5])],[(0,[z0,z1,z2,z3,z142,z5]),(0,[z0,z846,z1,z2,z3,z7]),(0,[z0,z1,z2,z752,z7,z14])],[(0,[z0,z96,z2,z3,z7,z39]),(0,[z54,z1,z847,z3,z7,z5]),(0,[z0,z1,z2,z3,z7,z848]),(0,[z0,z1,z2,z3,z7,z849]),(0,[z0,z657,z2,z3,z7,z35]),(0,[z850,z0,z1,z2,z7,z82])],[(0,[z1,z70,z30,z3,z7,z39]),(0,[z0,z535,z1,z7,z71,z5]),(0,[z15,z1,z2,z3,z165,z34]),(0,[z648,z1,z2,z3,z148,z5]),(0,[z0,z1,z2,z3,z94,z51]),(0,[z0,z1,z2,z114,z7,z82]),(0,[z0,z1,z2,z3,z7,z851])],[(0,[z0,z1,z852,z3,z7,z5]),(0,[z0,z1,z2,z3,z105,z39]),(0,[z0,z1,z2,z3,z7,z853])],[(0,[z116,z38,z2,z16,z3,z7]),(0,[z0,z854,z2,z3,z7,z5]),(0,[z0,z1,z2,z107,z351,z7]),(0,[z0,z120,z65,z3,z7,z283])],[(0,[z0,z1,z220,z3,z7,z196]),(0,[z0,z1,z855,z3,z7,z5]),(0,[z0,z856,z2,z3,z7,z5]),(0,[z0,z1,z2,z3,z7,z857]),(0,[z0,z355,z2,z3,z7,z133])],[(0,[z0,z1,z2,z271,z7,z455]),(0,[z1,z760,z2,z3,z7,z5]),(0,[z0,z1,z2,z117,z7,z39]),(0,[z0,z1,z166,z351,z7,z5]),(0,[z0,z1,z390,z2,z7,z14])],[(0,[z0,z858,z2,z3,z7,z5]),(0,[z0,z568,z2,z16,z3,z7]),(0,[z0,z1,z2,z3,z7,z859]),(0,[z0,z1,z2,z3,z7,z860])],[(0,[z83,z1,z30,z3,z7,z39]),(0,[z0,z1,z237,z3,z7,z39]),(0,[z0,z1,z2,z3,z7,z861]),(0,[z0,z862,z1,z16,z3,z7])],[(0,[z1,z2,z863,z62,z7,z5]),(0,[z0,z11,z1,z3,z7,z39])],[(0,[z0,z1,z12,z237,z7,z5]),(0,[z0,z1,z2,z76,z7,z14])],[(0,[z0,z1,z2,z864,z84,z7]),(0,[z0,z1,z2,z3,z7,z283]),(0,[z346,z1,z2,z3,z7,z184])]],
   [[(0,[z0,z1,z220,z3,z7,z801]),(0,[z0,z1,z2,z3,z7,z865]),(0,[z0,z78,z2,z18,z7,z34]),(0,[z0,z1,z2,z16,z218,z225])],[(0,[z0,z1,z2,z16,z3,z324]),(0,[z80,z1,z30,z3,z7,z39]),(0,[z0,z568,z166,z3,z7,z5]),(0,[z0,z1,z2,z3,z7,z836]),(0,[z0,z1,z2,z218,z225,z110])],[(0,[z0,z1,z2,z3,z866,z5]),(0,[z0,z192,z1,z2,z7,z14]),(0,[z0,z24,z162,z3,z7,z34]),(0,[z267,z0,z1,z147,z3,z7])],[(0,[z0,z1,z2,z3,z7,z867]),(0,[z141,z0,z1,z2,z7,z82]),(0,[z0,z1,z70,z3,z7,z868]),(0,[z0,z1,z2,z869,z3,z7]),(0,[z0,z1,z2,z870,z3,z7])],[(0,[z0,z1,z2,z807,z77,z7]),(0,[z0,z1,z19,z3,z412,z5]),(0,[z0,z1,z871,z3,z7,z5]),(0,[z0,z1,z358,z2,z7,z14]),(0,[z0,z1,z2,z3,z7,z872]),(0,[z0,z1,z2,z3,z7,z873]),(0,[z0,z1,z2,z3,z9,z506])],[(0,[z0,z457,z1,z2,z16,z7])],[(0,[z83,z1,z30,z84,z7,z5]),(0,[z0,z1,z2,z3,z7,z874]),(0,[z0,z1,z12,z2,z7,z371]),(0,[z0,z195,z1,z2,z7,z34]),(0,[z0,z1,z2,z3,z875,z5]),(0,[z0,z1,z876,z147,z3,z7])],[(0,[z0,z1,z2,z3,z324,z196]),(0,[z0,z27,z332,z2,z3,z7]),(0,[z0,z381,z22,z3,z7,z5]),(0,[z0,z1,z159,z3,z7,z39]),(0,[z0,z1,z2,z877,z3,z7]),(0,[z0,z1,z2,z3,z7,z878]),(0,[z0,z1,z57,z3,z7,z34])],[(0,[z0,z52,z1,z2,z7,z82]),(0,[z0,z1,z2,z3,z7,z66]),(0,[z0,z11,z1,z2,z7,z371])],[(0,[z0,z1,z2,z3,z7,z879]),(0,[z0,z1,z2,z3,z7,z880]),(0,[z0,z211,z91,z1,z16,z7])],[(0,[z0,z1,z2,z3,z7,z881]),(0,[z0,z1,z166,z3,z7,z39]),(0,[z15,z1,z2,z3,z165,z39]),(0,[z0,z1,z2,z351,z7,z133]),(0,[z0,z1,z2,z3,z882,z5]),(0,[z0,z11,z1,z3,z7,z370]),(0,[z0,z11,z1,z242,z3,z7])],[(0,[z0,z1,z2,z3,z7,z883]),(0,[z0,z1,z2,z3,z884,z5]),(0,[z15,z1,z2,z16,z3,z165]),(0,[z0,z1,z2,z3,z7,z885]),(0,[z0,z1,z3,z7,z273,z39])],[(0,[z0,z1,z886,z3,z7,z5]),(0,[z0,z887,z1,z2,z3,z7]),(0,[z0,z1,z2,z3,z7,z119]),(0,[z405,z0,z2,z3,z7,z463])],[(0,[z0,z1,z2,z3,z888,z5]),(0,[z0,z65,z1,z2,z7,z82]),(0,[z0,z1,z2,z3,z7,z328])],[(0,[z0,z78,z2,z7,z829,z5]),(0,[z0,z1,z2,z889,z3,z7]),(0,[z0,z1,z2,z7,z371,z82]),(0,[z0,z195,z175,z1,z2,z7])],[(0,[z0,z1,z2,z890,z7,z5]),(0,[z0,z1,z147,z891,z3,z7])]],
   [[(0,[z0,z1,z114,z40,z7,z39]),(0,[z8,z1,z2,z3,z7,z471]),(0,[z0,z24,z1,z147,z3,z7]),(0,[z0,z1,z12,z114,z7,z34]),(0,[z0,z195,z1,z3,z7,z39])],[(0,[z0,z1,z2,z3,z7,z892]),(0,[z0,z1,z2,z3,z7,z893]),(0,[z0,z198,z2,z3,z7,z14]),(0,[z0,z1,z2,z3,z244,z34])],[(0,[z0,z1,z2,z3,z7,z894]),(0,[z0,z1,z2,z3,z7,z895]),(0,[z0,z11,z1,z3,z7,z173]),(0,[z0,z1,z2,z896,z3,z7])],[(0,[z0,z1,z2,z897,z7,z5]),(0,[z0,z1,z2,z3,z231,z5]),(0,[z0,z202,z2,z3,z7,z14]),(0,[z0,z898,z2,z3,z7,z5]),(0,[z32,z1,z2,z3,z148,z14]),(0,[z899,z0,z1,z2,z3,z7]),(0,[z0,z1,z900,z3,z7,z5]),(0,[z901,z1,z2,z3,z7,z5]),(0,[z0,z1,z902,z16,z3,z7]),(0,[z0,z1,z147,z3,z3,z7])],[(0,[z0,z1,z235,z3,z7,z5])],[(0,[z0,z1,z2,z903,z7,z5]),(0,[z0,z393,z1,z2,z7,z14]),(0,[z0,z1,z2,z3,z7,z904]),(0,[z0,z201,z2,z3,z736,z5])],[(0,[z0,z1,z166,z3,z7,z56]),(0,[z0,z1,z2,z361,z7,z14]),(0,[z0,z24,z162,z3,z7,z39]),(0,[z0,z201,z2,z3,z160,z39]),(0,[z0,z1,z12,z7,z905,z5]),(1,[z0,z1,z12,z7,z371])],[(0,[z0,z1,z2,z3,z7,z906])],[(0,[z0,z1,z907,z3,z7,z5]),(0,[z85,z1,z2,z62,z7,z14]),(0,[z113,z0,z1,z147,z3,z7]),(0,[z0,z11,z1,z7,z905,z5]),(0,[z0,z1,z242,z114,z7,z5])],[(0,[z0,z1,z2,z3,z908,z5]),(0,[z0,z1,z909,z3,z7,z5]),(1,[z1,z847,z3,z7,z5]),(0,[z0,z45,z1,z147,z3,z7]),(0,[z0,z305,z1,z147,z3,z7]),(0,[z0,z1,z910,z3,z7,z5])],[(1,[z760,z2,z3,z7,z5]),(0,[z0,z1,z12,z2,z7,z173]),(0,[z0,z1,z2,z2,z7,z82])],[(0,[z0,z1,z2,z3,z911,z5]),(0,[z0,z96,z2,z3,z7,z356]),(0,[z0,z1,z479,z2,z7,z14]),(0,[z0,z211,z1,z147,z3,z7])],[(0,[z0,z1,z2,z3,z7,z912]),(0,[z55,z1,z235,z3,z7,z133]),(0,[z0,z11,z1,z2,z7,z173])],[(0,[z913,z0,z1,z2,z3,z7]),(0,[z0,z1,z2,z3,z105,z356])],[(0,[z0,z1,z2,z271,z7,z34]),(0,[z0,z1,z914,z3,z7,z5]),(0,[z0,z1,z2,z272,z7,z34])],[(0,[z0,z1,z2,z3,z7,z915]),(0,[z0,z1,z147,z3,z7,z14])]],
   [[(0,[z0,z1,z3,z7,z334,z39]),(0,[z0,z2,z916,z16,z3,z7])],[(0,[z0,z1,z2,z188,z7,z14])],[(0,[z83,z1,z30,z3,z7,z356]),(0,[z0,z1,z2,z62,z7,z82]),(0,[z0,z917,z2,z3,z7,z5])],[(0,[z116,z332,z38,z2,z3,z7]),(0,[z0,z1,z2,z3,z7,z918]),(0,[z0,z222,z460,z3,z7,z5]),(0,[z0,z222,z2,z367,z7,z5]),(0,[z32,z0,z1,z147,z3,z7]),(0,[z0,z211,z1,z3,z7,z34])],[(0,[z15,z1,z2,z3,z165,z422]),(0,[z250,z1,z2,z3,z7,z133]),(0,[z0,z1,z919,z3,z7,z5]),(0,[z0,z1,z2,z3,z7,z371]),(0,[z0,z1,z12,z114,z7,z39])],[(0,[z0,z920,z1,z2,z3,z7]),(0,[z0,z1,z2,z3,z921,z5]),(0,[z0,z1,z2,z3,z244,z39])],[(0,[z116,z38,z2,z271,z7,z5]),(0,[z0,z355,z2,z16,z3,z7]),(0,[z0,z699,z162,z3,z7,z5]),(0,[z0,z1,z2,z3,z7,z25]),(0,[z0,z17,z2,z7,z34,z280])],[(0,[z0,z1,z220,z3,z7,z883]),(0,[z0,z1,z2,z3,z7,z922]),(0,[z0,z419,z2,z3,z7,z643]),(0,[z0,z1,z2,z3,z7,z923]),(0,[z0,z1,z2,z282,z3,z7])],[(0,[z0,z1,z301,z3,z7,z34]),(0,[z0,z924,z1,z2,z3,z7]),(0,[z0,z91,z1,z2,z7,z88]),(0,[z0,z1,z2,z925,z3,z7])],[(0,[z0,z568,z2,z272,z7,z5]),(0,[z0,z1,z2,z926,z3,z7]),(0,[z0,z1,z927,z16,z3,z7])],[(0,[z0,z1,z2,z3,z7,z928]),(0,[z0,z1,z929,z3,z7,z5]),(0,[z0,z1,z2,z3,z930,z5]),(0,[z0,z1,z931,z3,z7,z5]),(0,[z0,z1,z166,z3,z7,z133]),(0,[z0,z1,z2,z3,z7,z932])],[(0,[z0,z1,z2,z3,z933,z5]),(0,[z0,z1,z2,z3,z7,z292]),(0,[z0,z1,z23,z3,z7,z769]),(0,[z0,z1,z2,z3,z7,z934])],[(0,[z0,z1,z2,z3,z7,z935]),(0,[z0,z1,z2,z936,z7,z5]),(0,[z0,z1,z841,z3,z7,z5])],[(0,[z0,z1,z2,z84,z7,z5]),(0,[z0,z1,z2,z937,z3,z7])],[(0,[z0,z222,z2,z3,z7,z5]),(0,[z0,z1,z2,z3,z7,z456]),(0,[z0,z91,z1,z2,z127,z7]),(0,[z0,z1,z2,z3,z7,z938]),(0,[z0,z1,z658,z3,z7,z39])],[(0,[z0,z1,z3,z7,z353,z39]),(0,[z0,z939,z2,z3,z7,z39])]],
   [[(0,[z116,z38,z301,z3,z7,z5]),(0,[z0,z1,z2,z3,z7,z940]),(0,[z0,z1,z2,z941,z7,z5]),(0,[z0,z942,z1,z2,z7,z5]),(0,[z0,z1,z2,z7,z82,z51])],[(0,[z276,z1,z2,z3,z148,z5]),(0,[z0,z1,z2,z238,z7,z14]),(0,[z0,z1,z2,z943,z3,z7]),(0,[z0,z1,z12,z114,z7,z370]),(0,[z0,z1,z944,z3,z7,z5])],[(0,[z0,z1,z2,z271,z7,z39]),(0,[z0,z38,z2,z3,z7,z86]),(0,[z54,z1,z70,z3,z7,z34]),(0,[z0,z592,z2,z3,z160,z5]),(0,[z0,z1,z2,z272,z7,z39]),(0,[z0,z1,z2,z3,z7,z945]),(0,[z0,z1,z2,z946,z7,z5])],[(0,[z0,z1,z2,z3,z7,z947]),(0,[z0,z1,z2,z7,z82,z173]),(0,[z0,z91,z1,z16,z147,z7])],[(0,[z0,z1,z2,z3,z948,z5]),(0,[z0,z1,z147,z3,z62,z7]),(0,[z0,z949,z1,z2,z3,z7]),(0,[z0,z27,z1,z2,z3,z167]),(1,[z0,z2,z3,z7,z836]),(0,[z0,z1,z2,z218,z225,z14])],[(0,[z0,z96,z2,z3,z105,z5]),(0,[z0,z1,z2,z84,z7,z14]),(0,[z0,z950,z1,z2,z3,z7]),(0,[z0,z951,z2,z3,z7,z5]),(0,[z0,z1,z147,z3,z7,z35]),(1,[z0,z1,z3,z756,z5]),(0,[z0,z1,z147,z3,z7,z952])],[(0,[z0,z1,z2,z3,z7,z953]),(0,[z13,z1,z2,z62,z7,z14]),(0,[z8,z1,z2,z3,z7,z56]),(0,[z0,z1,z2,z954,z3,z7]),(1,[z0,z790,z3,z7,z5])],[(0,[z116,z102,z38,z2,z3,z7]),(0,[z0,z1,z2,z955,z3,z7]),(0,[z0,z1,z70,z2,z7,z796]),(0,[z0,z1,z2,z3,z956,z5]),(0,[z0,z1,z2,z117,z7,z92]),(0,[z0,z87,z1,z2,z3,z167]),(0,[z0,z11,z91,z1,z7,z39]),(0,[z0,z211,z175,z1,z3,z7])],[(0,[z0,z1,z3,z7,z957,z5]),(0,[z0,z52,z1,z147,z3,z7]),(0,[z0,z1,z2,z62,z7,z217])],[(0,[z0,z1,z2,z3,z324,z34]),(0,[z0,z1,z2,z733,z3,z7]),(0,[z0,z1,z2,z3,z7,z958])],[(0,[z0,z1,z959,z3,z7,z5]),(0,[z0,z1,z2,z362,z7,z14]),(0,[z0,z1,z2,z3,z7,z960])],[(0,[z0,z1,z2,z961,z3,z7]),(0,[z0,z1,z2,z962,z7,z5]),(0,[z0,z1,z2,z963,z7,z5]),(0,[z0,z1,z2,z964,z3,z7]),(0,[z0,z1,z2,z3,z7,z965]),(0,[z0,z1,z2,z3,z34,z888])],[(0,[z0,z1,z301,z3,z7,z39]),(0,[z83,z1,z30,z3,z105,z5]),(0,[z0,z1,z966,z3,z7,z5]),(0,[z0,z1,z147,z114,z3,z7])],[(0,[z0,z424,z2,z7,z280,z5]),(0,[z0,z1,z2,z3,z7,z967]),(0,[z0,z1,z968,z3,z7,z5]),(0,[z0,z65,z1,z147,z3,z7]),(0,[z0,z78,z2,z16,z18,z7])],[(0,[z0,z1,z2,z3,z7,z344])],[(0,[z0,z1,z301,z3,z7,z969])]],
   [[(0,[z0,z970,z2,z3,z7,z5]),(1,[z0,z1,z7,z905,z5]),(0,[z0,z1,z147,z971,z3,z7]),(0,[z0,z174,z1,z2,z28,z3])],[(0,[z116,z38,z2,z3,z324,z5]),(0,[z0,z381,z2,z3,z231,z5]),(0,[z0,z1,z2,z3,z7,z972]),(0,[z0,z198,z2,z367,z7,z5]),(0,[z0,z1,z2,z3,z7,z973]),(0,[z0,z1,z2,z3,z167,z34]),(0,[z0,z1,z2,z16,z3,z244]),(0,[z0,z120,z790,z3,z7,z5])],[(0,[z0,z1,z2,z3,z7,z974]),(0,[z0,z1,z2,z3,z7,z975]),(0,[z0,z96,z2,z16,z3,z7])],[(0,[z0,z976,z2,z3,z7,z5]),(0,[z0,z415,z1,z3,z7,z34]),(0,[z977,z0,z1,z147,z3,z7])],[(0,[z0,z1,z2,z112,z142,z5]),(0,[z0,z1,z2,z3,z978,z5]),(0,[z0,z1,z410,z3,z7,z39])],[(0,[z0,z1,z2,z717,z3,z7]),(0,[z0,z1,z979,z3,z7,z5]),(0,[z0,z1,z2,z3,z7,z980]),(0,[z0,z1,z3,z7,z184,z39])],[(0,[z0,z1,z12,z30,z7,z14]),(0,[z0,z27,z1,z2,z351,z7]),(0,[z0,z89,z1,z3,z7,z840])],[(0,[z0,z1,z301,z3,z7,z455]),(0,[z0,z1,z460,z3,z7,z34]),(0,[z0,z1,z2,z367,z7,z34]),(0,[z15,z1,z2,z3,z165,z92]),(0,[z0,z355,z2,z3,z244,z5]),(0,[z0,z1,z2,z7,z981,z5]),(0,[z0,z1,z3,z7,z756,z5])],[(0,[z0,z1,z2,z3,z7,z982]),(0,[z0,z1,z2,z983,z3,z7])],[(0,[z0,z1,z70,z112,z7,z5]),(0,[z0,z1,z159,z40,z7,z5]),(0,[z0,z984,z1,z2,z3,z7]),(0,[z0,z1,z2,z985,z7,z5]),(0,[z0,z1,z2,z3,z7,z986]),(0,[z0,z987,z1,z2,z7,z34])],[(0,[z0,z1,z220,z3,z7,z455]),(0,[z0,z1,z2,z3,z7,z772]),(0,[z0,z1,z2,z3,z988,z5]),(0,[z0,z989,z1,z2,z3,z7]),(0,[z0,z201,z1,z2,z7,z82]),(0,[z0,z1,z2,z147,z3,z7]),(0,[z0,z818,z1,z3,z7,z5]),(0,[z0,z1,z2,z683,z7,z14])],[(0,[z0,z1,z2,z3,z7,z990]),(0,[z0,z1,z115,z3,z7,z39]),(0,[z0,z120,z65,z3,z7,z34]),(0,[z0,z219,z2,z3,z7,z53]),(0,[z0,z991,z1,z2,z3,z7]),(0,[z0,z1,z2,z3,z7,z992])],[(0,[z0,z198,z2,z3,z7,z5]),(0,[z0,z381,z2,z3,z97,z5]),(0,[z0,z1,z2,z3,z7,z993]),(0,[z0,z1,z2,z3,z994,z7]),(0,[z0,z568,z2,z3,z167,z5]),(0,[z0,z1,z2,z3,z7,z995])],[(0,[z0,z1,z2,z3,z7,z831]),(0,[z15,z1,z2,z117,z165,z5]),(0,[z0,z355,z2,z3,z7,z14])],[(0,[z0,z202,z2,z3,z7,z5]),(0,[z32,z1,z2,z3,z148,z5]),(0,[z0,z195,z1,z7,z5,z39]),(0,[z0,z1,z2,z3,z7,z996])],[(0,[z0,z1,z114,z3,z7,z173]),(0,[z0,z1,z2,z997,z3,z7])]],
   [[(0,[z0,z17,z2,z16,z7,z280]),(0,[z998,z1,z2,z3,z7,z5]),(0,[z0,z11,z1,z7,z5,z173]),(0,[z346,z0,z1,z2,z7,z82]),(0,[z0,z1,z3,z7,z34,z253])],[(0,[z0,z1,z2,z84,z7,z132]),(0,[z54,z1,z70,z3,z7,z456]),(0,[z1,z2,z40,z863,z7,z5])],[(0,[z0,z1,z2,z3,z7,z34]),(0,[z0,z1,z2,z16,z3,z4]),(0,[z0,z1,z2,z3,z7,z999])],[(0,[z0,z1,z2,z1000,z7,z5]),(0,[z85,z1,z2,z62,z7,z5]),(0,[z0,z1,z2,z3,z7,z1001]),(0,[z0,z91,z1,z2,z7,z82])],[(0,[z0,z451,z162,z3,z7,z5]),(0,[z0,z1,z2,z3,z7,z1002]),(0,[z0,z355,z2,z272,z7,z5]),(0,[z267,z1,z2,z3,z7,z56]),(0,[z1003,z0,z1,z2,z3,z7]),(0,[z0,z11,z1,z3,z7,z1004])],[(0,[z0,z1,z2,z3,z7,z1005]),(0,[z0,z1,z2,z3,z167,z39]),(0,[z0,z174,z1,z2,z3,z167]),(0,[z0,z1,z2,z3,z7,z1006])],[(0,[z0,z190,z2,z112,z7,z5]),(0,[z0,z1007,z1,z2,z3,z7]),(0,[z0,z1,z16,z1008,z3,z7]),(0,[z0,z1,z1009,z16,z3,z7])],[(0,[z0,z1,z166,z16,z3,z7]),(0,[z0,z1,z2,z1010,z3,z7]),(0,[z0,z1,z2,z3,z7,z1011]),(0,[z0,z78,z2,z18,z7,z39]),(0,[z0,z1,z2,z7,z337,z14]),(0,[z0,z1,z2,z1012,z7,z34])],[(0,[z0,z1,z2,z77,z7,z14]),(0,[z0,z1,z2,z3,z324,z455]),(0,[z0,z1,z2,z40,z7,z125]),(0,[z0,z1013,z2,z3,z7,z5]),(0,[z0,z1,z2,z351,z244,z5])],[(0,[z0,z381,z2,z3,z7,z292]),(0,[z0,z1,z2,z1014,z3,z7]),(0,[z0,z1,z2,z1015,z7,z5])],[(0,[z116,z38,z2,z3,z7,z5]),(0,[z0,z1,z2,z3,z1016,z5]),(0,[z458,z1,z2,z40,z7,z5]),(0,[z0,z1,z2,z3,z7,z1017]),(0,[z0,z1,z147,z3,z7,z5]),(0,[z0,z174,z1,z2,z409,z3])],[(0,[z0,z1018,z1,z127,z3,z7])],[(0,[z0,z1,z2,z3,z4,z196]),(0,[z0,z1,z22,z3,z97,z5]),(0,[z0,z1,z2,z1019,z3,z7]),(0,[z209,z1,z2,z3,z165,z5]),(0,[z0,z1,z467,z3,z7,z39]),(0,[z0,z135,z2,z3,z7,z53]),(0,[z0,z420,z11,z1,z7,z14])],[(0,[z0,z1,z1020,z3,z7,z5]),(0,[z0,z195,z1,z2,z7,z39]),(0,[z0,z1021,z1,z2,z3,z7]),(0,[z0,z1,z2,z3,z7,z446])],[(0,[z0,z1,z2,z351,z7,z14]),(0,[z55,z1,z2,z3,z342,z7]),(0,[z0,z862,z1,z3,z7,z5]),(0,[z0,z1,z2,z3,z7,z1022])],[(0,[z0,z190,z2,z3,z142,z5]),(0,[z0,z1023,z2,z3,z7,z5]),(0,[z0,z1,z3,z7,z456,z39]),(0,[z0,z568,z2,z3,z244,z5]),(0,[z0,z120,z65,z3,z7,z39])]],
   [[(0,[z0,z52,z2,z3,z7,z86]),(0,[z0,z1,z2,z3,z7,z1024])],[(0,[z0,z1,z2,z3,z167,z56]),(0,[z0,z1,z2,z3,z7,z1025]),(0,[z0,z1,z2,z7,z82,z39])],[(0,[z0,z1,z2,z3,z7,z1026]),(0,[z116,z38,z2,z3,z7,z14]),(0,[z0,z1,z1027,z3,z7,z5]),(0,[z0,z1,z3,z7,z34,z139]),(0,[z0,z1,z2,z1028,z7,z5])],[],[(0,[z0,z1,z2,z3,z7,z1029]),(0,[z0,z190,z70,z3,z7,z5]),(0,[z0,z1,z2,z365,z225,z5]),(0,[z0,z1,z19,z2,z7,z82])],[(0,[z0,z1,z30,z112,z7,z5]),(0,[z1,z2,z847,z3,z7,z5]),(0,[z113,z1,z2,z40,z7,z14]),(0,[z0,z568,z2,z3,z7,z14]),(0,[z0,z1,z16,z1030,z3,z7])],[(0,[z0,z1,z2,z3,z7,z39]),(0,[z0,z1031,z2,z3,z7,z5]),(0,[z0,z1,z2,z1032,z7,z5]),(0,[z0,z1,z159,z3,z7,z125]),(0,[z0,z1,z2,z1033,z7,z5])],[(0,[z0,z174,z1,z2,z351,z7]),(0,[z0,z1,z2,z7,z82,z1034])],[(0,[z0,z1,z2,z62,z231,z5]),(0,[z0,z1,z2,z3,z1035,z5]),(0,[z0,z1036,z2,z3,z7,z34]),(0,[z0,z1,z1037,z16,z3,z7])],[(0,[z0,z1,z301,z77,z7,z5]),(0,[z0,z1,z2,z1038,z7,z5]),(0,[z0,z1039,z1,z2,z3,z7]),(0,[z0,z1,z2,z33,z7,z14]),(0,[z0,z11,z1,z114,z7,z39]),(0,[z0,z1,z2,z7,z1040,z14]),(0,[z0,z392,z1,z2,z409,z3])],[(0,[z0,z1041,z2,z3,z7,z5]),(0,[z0,z174,z355,z2,z3,z7]),(0,[z0,z1,z2,z1042,z3,z7]),(0,[z0,z1,z2,z18,z7,z82])],[(0,[z0,z1,z2,z1043,z3,z7]),(0,[z0,z1,z2,z1044,z7,z34])],[(0,[z0,z1045,z1,z2,z7,z5]),(0,[z0,z1,z2,z3,z7,z1046]),(0,[z0,z11,z1,z649,z7,z5]),(0,[z0,z1,z2,z3,z7,z1047]),(0,[z0,z1,z2,z16,z7,z639])],[(0,[z0,z1048,z2,z3,z7,z5]),(0,[z0,z174,z1,z2,z3,z444]),(0,[z0,z1,z2,z7,z82,z56]),(0,[z0,z1,z2,z3,z1049,z14]),(0,[z0,z1,z1050,z16,z3,z7])],[(0,[z0,z1,z220,z3,z7,z34]),(0,[z0,z1,z1051,z3,z7,z5]),(0,[z0,z1,z2,z3,z1052,z5]),(0,[z0,z1,z1053,z3,z7,z5]),(0,[z0,z1,z2,z3,z7,z1054]),(0,[z0,z89,z1,z7,z34,z82]),(0,[z0,z1,z2,z67,z7,z14])],[(0,[z0,z1,z2,z3,z7,z1055]),(0,[z0,z1,z2,z3,z7,z1056]),(0,[z0,z1,z2,z218,z225,z5]),(1,[z0,z1,z2,z729,z3])]],
   [[(0,[z0,z1,z2,z150,z3,z7])],[(0,[z0,z1,z2,z3,z7,z455]),(0,[z0,z1,z2,z3,z7,z1057]),(0,[z13,z1,z2,z62,z7,z5])],[(0,[z0,z1,z553,z3,z7,z39]),(0,[z0,z1,z2,z3,z7,z1058]),(1,[z0,z11,z1,z7,z173])],[(0,[z0,z1,z847,z3,z7,z5]),(0,[z0,z1,z524,z3,z7,z39]),(0,[z0,z1,z2,z3,z7,z370]),(0,[z0,z1,z2,z242,z3,z7]),(0,[z0,z1,z2,z1059,z7,z5]),(0,[z0,z1,z2,z1060,z7,z34]),(0,[z0,z1,z1061,z3,z7,z5])],[(0,[z0,z760,z2,z3,z7,z5]),(0,[z0,z78,z1,z2,z7,z82])],[(0,[z0,z1,z2,z3,z7,z1062]),(0,[z0,z1,z902,z3,z7,z5]),(0,[z0,z1,z460,z3,z7,z422]),(0,[z0,z1,z2,z367,z7,z422]),(0,[z0,z1063,z1,z2,z7,z5]),(0,[z0,z1,z2,z3,z7,z1064])],[(0,[z116,z38,z220,z3,z7,z5]),(0,[z0,z1,z1065,z3,z7,z5])],[(0,[z0,z1,z2,z3,z7,z1066]),(0,[z0,z355,z2,z3,z167,z5]),(0,[z0,z1067,z1,z2,z3,z7]),(0,[z0,z573,z1,z3,z7,z39]),(0,[z0,z1,z1068,z147,z3,z7])],[(0,[z0,z1,z2,z16,z112,z7]),(0,[z0,z1,z166,z3,z244,z5])],[(0,[z0,z1,z2,z62,z7,z371]),(0,[z0,z1,z460,z3,z7,z973]),(0,[z55,z1,z2,z3,z7,z184]),(0,[z0,z17,z2,z7,z280,z14]),(0,[z0,z1,z2,z7,z82,z280]),(0,[z0,z263,z2,z16,z3,z73])],[(0,[z0,z1,z2,z77,z324,z5]),(0,[z0,z1,z2,z3,z1069,z7]),(0,[z0,z201,z1,z147,z3,z7]),(0,[z0,z211,z1,z3,z7,z39]),(0,[z0,z1,z2,z1070,z3,z7])],[(0,[z116,z0,z1,z2,z7,z82]),(0,[z0,z1,z2,z3,z480,z51]),(0,[z606,z1,z2,z3,z148,z5]),(0,[z0,z1,z2,z3,z7,z173])],[(0,[z0,z1,z2,z3,z1071,z5]),(0,[z0,z263,z2,z3,z73,z5]),(0,[z0,z87,z2,z534,z3,z7]),(0,[z0,z1,z2,z79,z7,z82])],[(0,[z0,z1,z2,z16,z271,z7]),(0,[z83,z96,z30,z3,z7,z5]),(0,[z0,z1,z114,z3,z7,z39])],[(0,[z0,z1,z2,z3,z1072,z5]),(0,[z0,z1,z378,z2,z7,z14]),(0,[z0,z1,z2,z3,z7,z1073])],[(0,[z0,z1074,z2,z3,z7,z5]),(0,[z0,z1,z2,z3,z7,z1075]),(0,[z0,z1,z2,z242,z7,z14]),(0,[z0,z1,z147,z3,z7,z506]),(0,[z0,z1,z2,z339,z122,z3])]],
   [[(0,[z0,z190,z30,z3,z7,z5]),(0,[z0,z381,z2,z3,z7,z34]),(0,[z0,z1,z2,z3,z7,z422]),(0,[z15,z366,z1,z2,z3,z165]),(0,[z0,z1,z2,z3,z7,z1076])],[(0,[z85,z381,z2,z62,z7,z5]),(0,[z0,z174,z1,z2,z572,z3]),(0,[z0,z1,z2,z7,z82,z133]),(0,[z0,z1,z2,z3,z1077,z5]),(0,[z0,z1,z2,z7,z905,z5])],[(0,[z0,z1,z220,z3,z7,z39]),(0,[z0,z27,z1,z166,z3,z7]),(0,[z0,z245,z1,z3,z20,z5]),(0,[z0,z2,z916,z3,z7,z5])],[(0,[z0,z1,z2,z3,z7,z1078]),(0,[z0,z1,z210,z3,z7,z173]),(0,[z0,z1,z2,z434,z7,z14]),(0,[z0,z91,z1,z2,z752,z7]),(0,[z0,z91,z1,z147,z3,z7])],[(0,[z0,z198,z460,z3,z7,z5]),(0,[z0,z1,z558,z3,z7,z39]),(0,[z0,z263,z2,z3,z73,z14]),(0,[z0,z1079,z2,z3,z7,z5]),(0,[z0,z91,z1,z2,z16,z7])],[(0,[z0,z87,z1,z166,z3,z7]),(0,[z0,z1,z166,z272,z7,z5]),(0,[z0,z17,z2,z7,z280,z213])],[(0,[z0,z1,z2,z3,z7,z1080]),(0,[z0,z1,z2,z3,z1081,z7]),(0,[z0,z1,z646,z3,z7,z39]),(0,[z0,z1,z2,z3,z7,z1082]),(0,[z0,z1,z2,z16,z117,z7]),(0,[z0,z1,z2,z3,z7,z1083]),(0,[z0,z1,z2,z3,z7,z1084]),(0,[z0,z1,z1085,z16,z3,z7])],[(0,[z141,z760,z2,z3,z7,z5]),(0,[z0,z1,z2,z1086,z3,z7]),(0,[z0,z1,z2,z1087,z3,z7]),(0,[z0,z1,z2,z3,z7,z1088])],[(0,[z0,z355,z2,z3,z7,z5]),(0,[z0,z1,z1089,z3,z7,z5]),(0,[z0,z1,z717,z3,z7,z5]),(0,[z0,z1,z2,z351,z167,z5]),(0,[z0,z1,z2,z3,z7,z1090]),(0,[z0,z1,z2,z3,z7,z1091]),(0,[z0,z89,z1,z3,z7,z88]),(0,[z0,z1092,z2,z3,z7,z5]),(0,[z0,z1,z2,z240,z7,z14])],[(0,[z0,z201,z2,z3,z549,z5]),(0,[z0,z1,z2,z1093,z3,z7]),(0,[z54,z1,z70,z3,z7,z39]),(0,[z0,z1018,z1,z3,z7,z5]),(0,[z0,z1,z2,z3,z7,z1094]),(0,[z1095,z0,z1,z2,z7,z82])],[(0,[z0,z531,z2,z3,z7,z53]),(0,[z0,z1,z2,z3,z7,z1096]),(0,[z0,z222,z23,z3,z7,z5]),(0,[z0,z1,z2,z1097,z3,z7]),(0,[z0,z1,z114,z3,z7,z370])],[(0,[z0,z1,z927,z3,z7,z5]),(0,[z15,z0,z1,z2,z7,z82]),(0,[z0,z1,z2,z3,z1098,z5])],[(0,[z0,z1,z2,z3,z1099,z5]),(0,[z0,z1,z2,z3,z7,z356]),(0,[z83,z1,z30,z16,z3,z7]),(0,[z0,z27,z355,z2,z3,z7]),(0,[z0,z87,z1,z2,z351,z7]),(0,[z0,z1,z2,z3,z7,z1100]),(0,[z0,z1,z2,z3,z7,z492]),(0,[z0,z1101,z2,z3,z7,z34]),(0,[z0,z1102,z1,z2,z7,z82])],[(0,[z0,z1,z2,z62,z7,z173]),(0,[z0,z1,z2,z3,z7,z1103]),(0,[z0,z1,z2,z3,z7,z1104]),(0,[z0,z1,z2,z3,z7,z1105]),(0,[z0,z1,z2,z1106,z7,z5]),(0,[z0,z1,z2,z1107,z3,z7]),(0,[z0,z1,z2,z7,z82,z1108])],[(0,[z0,z1,z2,z3,z4,z34]),(0,[z0,z1,z2,z367,z7,z1109]),(0,[z8,z1,z2,z3,z7,z144]),(0,[z0,z1,z2,z3,z1110,z5]),(0,[z0,z1,z2,z3,z7,z1111]),(0,[z0,z11,z175,z1,z7,z71]),(0,[z0,z91,z1,z2,z7,z66]),(0,[z0,z1,z12,z150,z114,z7]),(0,[z0,z138,z1,z3,z20,z14]),(0,[z0,z1,z445,z3,z7,z39]),(0,[z258,z0,z1,z2,z7,z82])],[(0,[z0,z87,z355,z2,z3,z7]),(0,[z0,z1,z2,z7,z82,z73]),(0,[z0,z138,z1,z3,z20,z251])]],
   [[(0,[z0,z1,z2,z3,z324,z39]),(0,[z0,z1,z2,z3,z7,z1112]),(0,[z0,z192,z1,z7,z71,z5]),(0,[z55,z355,z2,z3,z7,z133])],[(0,[z0,z1,z3,z7,z1004,z39])],[(0,[z1,z2,z62,z7,z144,z14]),(0,[z0,z1,z2,z3,z7,z466]),(0,[z0,z11,z1,z7,z14,z173])],[(0,[z0,z1,z2,z77,z7,z5]),(0,[z0,z175,z1,z2,z7,z82])],[(0,[z0,z1,z22,z3,z231,z5]),(0,[z0,z1,z2,z3,z7,z1113]),(0,[z0,z1114,z2,z3,z7,z5]),(0,[z0,z1115,z1,z3,z7,z5]),(0,[z0,z1,z19,z147,z3,z7])],[(0,[z0,z1,z2,z3,z7,z1116]),(0,[z0,z1117,z1,z2,z3,z7]),(0,[z0,z1,z378,z114,z7,z5]),(0,[z1,z2,z3,z7,z5,z800])],[(0,[z85,z0,z1,z2,z7,z82])],[(0,[z0,z38,z2,z3,z7,z196]),(0,[z0,z1,z159,z16,z3,z7])],[(0,[z0,z1,z1118,z3,z7,z5]),(0,[z0,z1,z2,z3,z7,z1119]),(0,[z0,z1,z114,z7,z905,z5])],[(0,[z0,z1,z2,z3,z1120,z5]),(0,[z0,z1,z2,z351,z7,z5]),(0,[z0,z1,z2,z3,z7,z1109]),(0,[z0,z1,z2,z3,z7,z1121]),(0,[z0,z201,z2,z16,z3,z160]),(0,[z0,z87,z2,z171,z3,z7])],[(0,[z760,z38,z2,z3,z7,z5]),(0,[z0,z1,z2,z3,z1122,z5])],[(0,[z0,z1,z2,z3,z7,z1123]),(0,[z0,z1,z2,z3,z7,z1124]),(0,[z0,z45,z341,z1,z2,z14]),(0,[z1125,z0,z1,z147,z3,z7])],[(0,[z0,z1,z2,z1126,z7,z5]),(0,[z0,z1,z2,z3,z1127,z7]),(0,[z0,z1,z150,z147,z3,z7]),(0,[z0,z1,z2,z3,z7,z1128])],[(0,[z0,z1,z2,z3,z7,z1129]),(0,[z0,z11,z1,z7,z71,z39]),(0,[z0,z1,z2,z3,z833,z5])],[(0,[z0,z1130,z2,z3,z7,z5]),(0,[z0,z1,z460,z3,z7,z39]),(0,[z0,z1,z2,z367,z7,z39]),(0,[z0,z1,z242,z147,z3,z7])],[(0,[z0,z2,z3,z7,z35,z836]),(0,[z0,z89,z195,z1,z7,z34]),(0,[z0,z1,z390,z3,z7,z34])]],
   [[(0,[z0,z568,z2,z3,z7,z5]),(0,[z0,z1,z70,z3,z7,z283]),(0,[z113,z1,z2,z40,z7,z5]),(0,[z0,z1,z19,z3,z79,z5]),(0,[z0,z174,z1,z2,z432,z3])],[(0,[z55,z1,z2,z351,z7,z133]),(0,[z0,z1,z2,z3,z7,z1131]),(0,[z0,z1,z2,z501,z7,z14]),(0,[z0,z478,z1,z2,z432,z3])],[(0,[z0,z1,z2,z112,z7,z34]),(0,[z0,z1132,z2,z3,z7,z14])],[(0,[z0,z202,z2,z62,z7,z5]),(1,[z1,z2,z863,z7,z5]),(0,[z0,z1,z2,z3,z7,z92]),(0,[z0,z1,z2,z3,z7,z1133]),(0,[z0,z174,z1,z166,z3,z7]),(0,[z0,z1,z2,z1134,z3,z7]),(0,[z0,z1,z3,z7,z34,z39])],[(0,[z0,z96,z2,z3,z7,z5]),(0,[z0,z1,z147,z3,z7,z165]),(0,[z0,z1,z2,z3,z7,z1135]),(0,[z0,z78,z1,z147,z3,z7]),(0,[z181,z1,z2,z3,z7,z144])],[(0,[z0,z420,z1,z3,z7,z371])],[(0,[z0,z1,z2,z3,z105,z5]),(0,[z406,z1,z2,z3,z7,z56]),(0,[z0,z24,z162,z16,z3,z7]),(0,[z0,z1,z2,z7,z1136,z5])],[(0,[z0,z535,z1,z3,z7,z39]),(0,[z0,z1137,z2,z3,z7,z5]),(0,[z0,z1,z23,z3,z148,z5]),(0,[z0,z1,z2,z436,z7,z14]),(0,[z0,z1,z2,z1138,z3,z7]),(0,[z0,z17,z2,z7,z829,z5])],[(0,[z0,z1,z70,z147,z3,z7]),(0,[z0,z198,z23,z3,z7,z5]),(0,[z55,z568,z2,z3,z7,z133]),(0,[z0,z1,z166,z3,z167,z5]),(0,[z1,z2,z3,z7,z56,z800]),(0,[z0,z1,z3,z7,z371,z71]),(0,[z0,z1,z19,z3,z79,z14]),(0,[z0,z1,z2,z3,z1049,z5])],[(0,[z0,z1,z1139,z2,z3,z7]),(0,[z0,z1140,z2,z3,z7,z5]),(0,[z0,z1,z2,z117,z7,z5]),(0,[z0,z78,z2,z199,z18,z7]),(0,[z0,z1,z2,z3,z7,z1141])],[(0,[z0,z1,z2,z28,z7,z82]),(0,[z0,z48,z1,z2,z3,z506])],[(0,[z116,z0,z1,z147,z3,z7]),(0,[z0,z1,z2,z3,z129,z51]),(0,[z0,z1,z529,z3,z79,z5]),(0,[z0,z1,z2,z1142,z7,z5]),(0,[z0,z1143,z2,z3,z7,z39]),(0,[z0,z1,z3,z7,z662,z39])],[(0,[z0,z1,z2,z3,z7,z969]),(0,[z0,z96,z2,z3,z7,z14]),(0,[z0,z1,z22,z3,z7,z292]),(0,[z0,z1,z2,z3,z7,z1144]),(0,[z0,z1,z2,z3,z7,z1145])],[(0,[z0,z1,z2,z3,z4,z455]),(0,[z0,z668,z2,z3,z73,z5]),(0,[z0,z1,z2,z3,z7,z1146]),(0,[z0,z1,z2,z16,z7,z561])],[(0,[z0,z1,z1147,z3,z7,z5]),(0,[z0,z1,z2,z3,z105,z14]),(0,[z0,z1148,z2,z3,z7,z5]),(0,[z0,z1,z2,z3,z97,z292]),(0,[z0,z1,z23,z3,z7,z34])],[(0,[z0,z1,z220,z77,z7,z5]),(0,[z644,z38,z2,z3,z7,z5]),(0,[z0,z1,z2,z84,z7,z1149]),(0,[z0,z1,z2,z3,z7,z1150])]],
   [[(0,[z0,z1,z2,z3,z7,z1151]),(0,[z0,z459,z1,z3,z20,z5]),(0,[z0,z1,z2,z40,z7,z14]),(0,[z650,z1,z2,z3,z7,z56]),(0,[z0,z1,z147,z18,z3,z7]),(0,[z0,z1,z37,z3,z7,z840])],[(0,[z0,z1,z2,z117,z7,z14]),(0,[z0,z1,z3,z7,z681,z39]),(0,[z0,z1,z210,z3,z7,z39]),(0,[z0,z1,z147,z3,z9,z7])],[(0,[z0,z1,z2,z3,z1152,z5]),(0,[z0,z1,z2,z3,z1153,z5]),(0,[z0,z11,z1,z7,z71,z173]),(0,[z0,z1154,z1,z16,z3,z7])],[(0,[z83,z1,z30,z3,z7,z14]),(0,[z15,z1,z2,z3,z129,z165]),(0,[z0,z1,z2,z3,z7,z1155])],[(0,[z0,z1156,z2,z3,z7,z5]),(0,[z0,z26,z2,z7,z280,z5]),(0,[z0,z17,z2,z7,z280,z5]),(0,[z0,z1,z2,z3,z7,z1157])],[(0,[z0,z332,z2,z3,z7,z53]),(0,[z0,z109,z1,z2,z7,z14])],[(0,[z0,z1,z2,z1158,z3,z7]),(0,[z113,z1,z2,z16,z40,z7]),(0,[z0,z1,z2,z1159,z7,z5]),(0,[z0,z1,z2,z3,z7,z1160]),(0,[z0,z1161,z2,z3,z7,z5])],[(0,[z0,z1,z301,z3,z7,z1162]),(0,[z0,z1,z1163,z3,z7,z5]),(0,[z0,z1,z2,z3,z1164,z7]),(0,[z0,z1,z2,z3,z7,z1165])],[(0,[z0,z1,z30,z3,z7,z344]),(0,[z0,z1,z2,z3,z709,z5]),(0,[z0,z1,z2,z3,z7,z1166]),(0,[z0,z1,z2,z3,z167,z133]),(0,[z0,z790,z162,z3,z7,z5]),(0,[z0,z1,z1009,z3,z7,z5]),(0,[z0,z1,z150,z3,z7,z39]),(0,[z0,z1,z2,z1167,z3,z7])],[(0,[z0,z1,z166,z3,z7,z5]),(0,[z0,z1,z2,z3,z7,z1168]),(0,[z0,z1,z2,z3,z756,z5])],[(0,[z0,z1169,z1,z2,z218,z5])],[(0,[z0,z1,z70,z2,z7,z82]),(0,[z15,z0,z1,z147,z3,z7]),(0,[z0,z1,z2,z41,z7,z14]),(1,[z0,z1,z242,z114,z7]),(0,[z0,z1,z2,z1170,z7,z82])],[(0,[z0,z1,z30,z3,z7,z283]),(0,[z0,z1,z2,z3,z7,z1171]),(0,[z0,z1,z2,z3,z9,z51])],[(0,[z0,z1,z2,z77,z7,z1172]),(0,[z0,z190,z2,z3,z7,z34]),(0,[z0,z1,z2,z40,z7,z396]),(0,[z0,z1,z23,z3,z165,z5]),(0,[z55,z1,z2,z3,z7,z800]),(0,[z0,z2,z3,z7,z836,z53]),(0,[z0,z1,z2,z3,z7,z1004]),(0,[z0,z89,z1,z2,z7,z82]),(0,[z0,z1,z2,z3,z7,z1173]),(0,[z0,z1,z2,z16,z3,z1174])],[(0,[z0,z1,z159,z3,z7,z14]),(0,[z372,z1,z2,z40,z7,z5]),(0,[z0,z1,z1175,z3,z7,z5]),(0,[z258,z0,z1,z147,z3,z7])],[(0,[z0,z1,z2,z3,z1176,z7]),(0,[z0,z1,z2,z1177,z3,z7]),(0,[z1178,z1,z2,z3,z7,z5]),(0,[z0,z1,z2,z1179,z7,z5]),(0,[z0,z1,z2,z1180,z7,z5]),(0,[z0,z27,z1,z2,z7,z82])]],
   [[(0,[z0,z1,z1181,z3,z7,z5]),(0,[z0,z1,z2,z7,z456,z796]),(0,[z0,z1,z2,z218,z7,z82])],[(0,[z15,z1,z2,z3,z165,z14]),(0,[z0,z1,z166,z3,z7,z14])],[(0,[z0,z87,z1,z2,z7,z82])],[(0,[z0,z1,z2,z1182,z271,z7]),(0,[z0,z737,z1,z2,z3,z5]),(0,[z0,z1,z2,z3,z7,z1183]),(0,[z0,z175,z1,z147,z3,z7]),(0,[z0,z1,z1184,z16,z3,z7])],[(0,[z0,z1,z2,z3,z7,z1185]),(0,[z0,z1,z30,z147,z3,z7])],[(0,[z0,z52,z2,z3,z7,z196]),(0,[z0,z1,z2,z3,z7,z1186]),(0,[z0,z1,z2,z3,z7,z125]),(0,[z1187,z1,z2,z3,z7,z5])],[(0,[z85,z0,z1,z147,z3,z7]),(0,[z1,z2,z40,z62,z7,z14]),(0,[z0,z1,z2,z3,z7,z1188])],[(0,[z141,z52,z2,z3,z7,z34]),(0,[z0,z1,z314,z3,z7,z39]),(0,[z0,z211,z1,z16,z3,z7]),(0,[z0,z1,z147,z1189,z3,z7])],[(0,[z0,z96,z2,z3,z7,z132]),(0,[z0,z1,z2,z3,z7,z1190])],[(0,[z0,z1,z2,z84,z142,z5]),(0,[z0,z138,z1,z3,z20,z5]),(0,[z0,z1,z2,z3,z7,z1191])],[(0,[z0,z1,z2,z3,z105,z132]),(0,[z55,z0,z1,z2,z7,z82]),(0,[z0,z1,z1037,z3,z7,z5])],[(0,[z0,z1,z7,z34,z82,z39])],[(0,[z0,z1,z301,z16,z3,z7])],[(0,[z0,z1,z2,z3,z1192,z5]),(0,[z0,z24,z162,z3,z7,z14]),(0,[z0,z1,z2,z3,z7,z1193]),(0,[z0,z201,z2,z3,z160,z14]),(0,[z0,z1,z2,z1194,z3,z7])],[(0,[z0,z452,z1,z3,z20,z5]),(0,[z0,z1,z2,z1195,z7,z5]),(0,[z0,z790,z1,z3,z7,z5])],[(0,[z0,z1,z2,z77,z4,z5]),(0,[z0,z202,z22,z3,z7,z5]),(0,[z0,z1,z1196,z3,z7,z5]),(0,[z0,z1,z476,z3,z7,z39]),(0,[z0,z1,z1050,z3,z7,z5]),(0,[z0,z1,z586,z3,z7,z39])]],
   [[],[(0,[z0,z202,z2,z3,z97,z5]),(0,[z0,z1,z2,z3,z7,z1197]),(0,[z0,z1,z2,z729,z3,z5])],[(0,[z0,z1,z114,z62,z7,z39]),(0,[z0,z1,z2,z3,z7,z1198]),(0,[z0,z1,z2,z3,z7,z1199]),(0,[z0,z27,z2,z3,z7,z35])],[(0,[z0,z1200,z2,z3,z7,z5]),(0,[z0,z1,z22,z3,z7,z34]),(0,[z0,z211,z1,z16,z7,z14]),(0,[z0,z1,z107,z147,z3,z7])],[(0,[z595,z52,z2,z3,z7,z5]),(0,[z379,z1,z70,z3,z7,z5]),(0,[z85,z1,z22,z62,z7,z5]),(0,[z1,z2,z3,z7,z824,z5]),(0,[z0,z1,z465,z3,z7,z34]),(0,[z0,z1,z2,z3,z342,z51])],[(0,[z0,z1,z2,z3,z7,z1201]),(0,[z0,z1,z2,z3,z7,z1202]),(0,[z0,z1,z2,z3,z97,z34]),(0,[z0,z1,z2,z7,z82,z14]),(0,[z0,z1,z2,z7,z82,z20]),(0,[z0,z1,z2,z1203,z3,z7])],[(0,[z54,z1,z70,z16,z3,z7]),(0,[z85,z1,z2,z62,z97,z5]),(0,[z0,z1,z2,z1204,z7,z5]),(0,[z0,z1,z2,z7,z66,z14]),(0,[z0,z1,z2,z784,z7,z34]),(0,[z0,z45,z341,z1,z2,z5])],[(0,[z0,z381,z2,z3,z7,z39]),(0,[z0,z58,z2,z3,z7,z53])],[(0,[z0,z206,z2,z18,z7,z5])],[(0,[z116,z38,z2,z3,z4,z5]),(0,[z0,z1,z70,z3,z7,z173])],[(0,[z0,z138,z1,z3,z34,z20])],[(0,[z0,z190,z2,z84,z7,z5]),(0,[z0,z1,z460,z3,z7,z92]),(0,[z0,z1,z2,z367,z7,z92]),(0,[z0,z1205,z2,z3,z7,z5]),(0,[z0,z1,z12,z114,z7,z14]),(0,[z0,z1,z2,z67,z7,z82]),(0,[z0,z1206,z1,z147,z3,z7])],[(0,[z0,z1,z1207,z2,z3,z5]),(0,[z0,z1,z145,z3,z7,z39]),(0,[z0,z1,z302,z2,z7,z14]),(0,[z0,z1,z23,z3,z7,z422]),(0,[z0,z1,z2,z3,z244,z14]),(0,[z0,z1,z2,z3,z7,z1208]),(1,[z0,z1,z3,z7,z840]),(0,[z298,z0,z1,z147,z3,z7])],[(0,[z0,z1,z2,z1209,z3,z7]),(0,[z0,z1,z2,z649,z7,z14]),(0,[z0,z1132,z2,z3,z7,z5])],[(0,[z0,z1,z2,z3,z7,z1210]),(0,[z0,z1,z2,z3,z1211,z5]),(0,[z0,z11,z514,z1,z7,z5]),(0,[z0,z1,z19,z16,z3,z79]),(0,[z0,z939,z2,z3,z7,z5]),(0,[z0,z1169,z1,z2,z3,z5]),(0,[z0,z1,z2,z3,z7,z1212])],[(0,[z0,z1,z2,z1213,z7,z5]),(0,[z0,z1,z70,z3,z7,z344]),(0,[z0,z355,z2,z3,z9,z7]),(0,[z0,z1,z2,z3,z7,z1214]),(0,[z0,z1215,z2,z3,z7,z5])]],
   [[(0,[z0,z1,z2,z1216,z3,z7]),(0,[z0,z1,z2,z3,z7,z1217]),(0,[z0,z1,z2,z1218,z7,z5]),(0,[z0,z560,z212,z1,z2,z3]),(0,[z0,z174,z1,z2,z7,z82])],[(0,[z0,z1,z2,z3,z7,z1162]),(0,[z0,z1,z460,z117,z7,z5]),(0,[z0,z1,z2,z3,z7,z1219])],[(0,[z0,z1220,z1,z3,z7,z5]),(0,[z0,z472,z2,z7,z280,z5]),(0,[z0,z1,z2,z233,z7,z14])],[(0,[z0,z1221,z1,z2,z3,z7]),(0,[z0,z509,z1,z2,z7,z14]),(0,[z0,z1,z159,z3,z7,z1222]),(0,[z0,z1,z2,z272,z244,z5]),(0,[z0,z1,z1008,z3,z7,z5])],[(0,[z0,z1,z2,z618,z7,z14]),(0,[z0,z1,z2,z7,z230,z82]),(0,[z0,z1,z2,z3,z300,z51]),(0,[z0,z1,z2,z729,z3,z7])],[(0,[z0,z1,z2,z3,z4,z39]),(0,[z0,z1,z2,z3,z7,z1223]),(0,[z0,z1,z2,z3,z7,z1224]),(0,[z0,z1,z147,z3,z7,z53]),(0,[z0,z1,z2,z827,z7,z34])],[(0,[z0,z1,z2,z3,z231,z292]),(0,[z352,z0,z1,z3,z7,z39]),(0,[z0,z1225,z2,z3,z7,z5])],[(0,[z0,z1,z22,z3,z7,z39]),(0,[z0,z1,z1226,z3,z7,z5]),(0,[z0,z1,z2,z1227,z3,z7]),(0,[z0,z1,z147,z3,z7,z71]),(0,[z0,z942,z1,z2,z7,z34])],[(0,[z0,z1,z12,z114,z7,z396]),(0,[z0,z1,z1085,z3,z7,z5]),(0,[z0,z1,z2,z3,z1228,z14])],[(0,[z0,z1,z2,z271,z7,z14]),(0,[z0,z1,z2,z16,z3,z105]),(0,[z0,z1,z2,z3,z1229,z5]),(0,[z0,z1,z2,z272,z7,z14]),(0,[z0,z1,z16,z147,z3,z7])],[(0,[z0,z1,z2,z1230,z3,z7]),(0,[z0,z1,z235,z3,z7,z456]),(0,[z113,z1,z2,z127,z40,z7]),(0,[z0,z1,z2,z3,z7,z110])],[(0,[z0,z1,z234,z3,z7,z39]),(0,[z0,z1,z2,z1231,z7,z5])],[(0,[z0,z1,z166,z3,z7,z353])],[(0,[z0,z1,z2,z3,z7,z1232]),(0,[z0,z89,z1,z147,z3,z7]),(0,[z0,z1,z2,z7,z845,z34])],[(0,[z83,z1,z30,z3,z7,z5]),(0,[z0,z1,z2,z3,z142,z34]),(0,[z0,z1,z2,z3,z7,z1233]),(0,[z0,z1,z1234,z2,z3,z7])],[(0,[z0,z821,z2,z3,z7,z5]),(0,[z0,z120,z65,z16,z3,z7]),(0,[z0,z1,z2,z1235,z7,z5]),(0,[z0,z1,z2,z3,z7,z1236]),(0,[z0,z27,z1,z147,z3,z7]),(0,[z0,z11,z1,z7,z39,z173]),(0,[z0,z1,z2,z3,z1237,z5]),(0,[z0,z1,z434,z147,z3,z7])]],
   [[(0,[z0,z1,z22,z3,z7,z1056]),(0,[z0,z1,z2,z351,z9,z7]),(0,[z0,z65,z790,z3,z7,z5]),(0,[z0,z1,z2,z3,z7,z1238])],[(0,[z0,z1,z2,z1239,z7,z5]),(0,[z0,z1,z2,z1240,z3,z7]),(0,[z15,z1,z460,z3,z165,z5]),(0,[z15,z1,z2,z367,z165,z5]),(0,[z0,z138,z1,z3,z20,z599]),(0,[z0,z1241,z2,z3,z7,z5])],[(0,[z665,z1,z70,z3,z7,z5]),(0,[z0,z87,z1,z147,z3,z7])],[(0,[z0,z1,z301,z3,z7,z14]),(0,[z0,z1,z2,z3,z7,z1242]),(0,[z80,z1,z30,z3,z7,z5]),(0,[z0,z2,z7,z829,z280,z5]),(0,[z0,z1,z147,z3,z160,z7]),(0,[z0,z1,z12,z7,z371,z14])],[],[(0,[z0,z1,z30,z3,z7,z173]),(0,[z0,z1,z1243,z3,z7,z5]),(0,[z0,z1244,z1,z2,z3,z7]),(0,[z113,z1,z2,z863,z7,z5]),(0,[z0,z1,z565,z2,z7,z14]),(0,[z0,z89,z1,z3,z7,z34]),(0,[z0,z1169,z1,z2,z7,z5]),(0,[z0,z1,z16,z147,z7,z14])],[(0,[z0,z1,z2,z16,z3,z7]),(0,[z101,z1,z2,z3,z148,z5]),(0,[z8,z274,z1,z2,z3,z7]),(0,[z0,z1,z1245,z3,z7,z5])],[(0,[z0,z1,z2,z1246,z7,z5]),(0,[z0,z1,z2,z3,z7,z1247]),(0,[z0,z1,z1248,z3,z7,z5]),(0,[z0,z1,z2,z3,z7,z1249])],[(0,[z0,z1250,z1,z2,z3,z5]),(0,[z0,z1,z2,z3,z7,z1251]),(0,[z113,z1,z2,z40,z7,z31]),(0,[z0,z1,z170,z2,z7,z14]),(0,[z0,z1,z228,z3,z7,z39]),(0,[z0,z1252,z1,z2,z3,z7])],[(0,[z0,z1,z2,z112,z7,z39]),(0,[z0,z1,z159,z3,z7,z5]),(0,[z0,z1,z2,z3,z7,z1253]),(0,[z0,z1,z2,z3,z7,z1254])],[(0,[z0,z1,z301,z271,z7,z5]),(0,[z0,z1,z2,z1255,z7,z5]),(1,[z1,z2,z3,z824,z5]),(0,[z55,z0,z1,z147,z3,z7])],[(0,[z0,z1256,z1,z2,z3,z7]),(0,[z0,z1,z2,z3,z389,z51]),(0,[z0,z1,z2,z3,z978,z34])],[(0,[z15,z1,z2,z3,z165,z5]),(0,[z0,z1,z2,z3,z7,z1257]),(0,[z0,z1,z2,z1258,z3,z7]),(0,[z0,z1,z2,z242,z114,z7]),(0,[z0,z1,z2,z425,z7,z14])],[(0,[z0,z1,z220,z271,z7,z5]),(0,[z0,z1,z2,z3,z7,z1259]),(0,[z0,z1,z2,z863,z7,z5]),(0,[z0,z1,z2,z7,z829,z5]),(0,[z0,z1,z2,z7,z225,z82]),(0,[z0,z1260,z2,z3,z7,z5])],[(0,[z0,z192,z1,z3,z7,z39]),(0,[z0,z1,z2,z1261,z117,z7]),(0,[z0,z1,z1245,z3,z7,z14]),(0,[z0,z1,z2,z16,z3,z1035])],[(0,[z116,z760,z2,z3,z7,z5]),(0,[z0,z1262,z2,z3,z7,z5]),(0,[z0,z1,z23,z3,z7,z1133]),(0,[z0,z157,z2,z3,z7,z35]),(0,[z0,z1,z12,z2,z7,z14])]],
   [[(0,[z0,z1,z2,z3,z148,z328])],[(0,[z1,z30,z3,z7,z471,z39]),(0,[z0,z11,z1,z2,z7,z14])],[(0,[z0,z1,z2,z3,z142,z39]),(0,[z0,z1,z2,z3,z7,z1263]),(0,[z0,z522,z1,z2,z242,z7]),(0,[z0,z1,z2,z16,z7,z14])],[(0,[z0,z1,z2,z3,z7,z1264]),(0,[z0,z1,z255,z3,z7,z39]),(0,[z0,z1,z3,z7,z905,z5]),(0,[z0,z1,z19,z3,z756,z5]),(0,[z0,z1,z2,z194,z7,z14])],[(0,[z55,z1,z166,z3,z7,z133]),(0,[z0,z1,z2,z3,z7,z1265]),(0,[z0,z212,z1,z2,z7,z82])],[(0,[z0,z1,z2,z3,z1266,z5]),(0,[z0,z1,z1267,z2,z7,z5]),(0,[z0,z1,z23,z3,z7,z39]),(0,[z32,z1,z2,z3,z148,z34])],[(0,[z0,z1,z2,z3,z7,z1268]),(0,[z0,z78,z2,z18,z7,z5]),(0,[z0,z1,z147,z218,z3,z7]),(0,[z0,z1269,z1,z147,z3,z7])],[(0,[z0,z1,z2,z3,z1270,z5]),(0,[z0,z1,z70,z3,z7,z39]),(0,[z0,z1,z2,z1271,z3,z7]),(0,[z0,z1,z2,z3,z7,z1272]),(0,[z0,z499,z2,z3,z7,z53])],[(0,[z0,z1,z2,z1273,z3,z7]),(0,[z0,z1,z2,z1274,z7,z5]),(0,[z477,z1,z30,z3,z7,z5]),(0,[z0,z24,z162,z3,z7,z5]),(0,[z0,z201,z2,z3,z160,z5])],[(0,[z0,z1,z2,z3,z1275,z5]),(0,[z0,z202,z2,z3,z231,z5]),(0,[z0,z1276,z2,z3,z7,z5]),(0,[z0,z1,z2,z3,z1277,z5]),(0,[z0,z45,z341,z1,z2,z46])],[(0,[z0,z1,z2,z1278,z7,z5]),(0,[z0,z1,z2,z771,z3,z7]),(0,[z0,z1279,z2,z3,z7,z5]),(0,[z0,z89,z1,z3,z7,z371])],[(0,[z0,z1,z2,z271,z324,z5]),(0,[z613,z1,z2,z3,z165,z5])],[(0,[z83,z0,z1,z2,z7,z82]),(0,[z0,z1,z2,z3,z167,z14]),(0,[z0,z1280,z1,z2,z3,z7]),(0,[z0,z1,z2,z16,z7,z193]),(0,[z0,z195,z1,z2,z7,z5]),(0,[z0,z1,z12,z2,z7,z396]),(1,[z0,z211,z1,z7,z14])],[(0,[z0,z1,z2,z3,z231,z34]),(0,[z0,z1,z2,z1281,z3,z7]),(0,[z0,z1,z2,z3,z7,z1282]),(0,[z0,z17,z1,z2,z7,z82]),(0,[z0,z1,z2,z3,z7,z1283])],[(0,[z0,z1,z1284,z2,z3,z7]),(0,[z0,z1,z2,z3,z7,z1285]),(0,[z85,z1,z2,z62,z231,z5]),(0,[z0,z1,z235,z3,z7,z34]),(0,[z0,z78,z2,z18,z7,z14]),(0,[z0,z11,z1,z2,z7,z396])],[(0,[z0,z1,z2,z3,z1286,z7]),(0,[z0,z1,z3,z7,z1287,z5]),(0,[z0,z1,z2,z1288,z7,z5])]],
   [[(0,[z0,z1,z166,z3,z9,z7]),(0,[z0,z1,z2,z7,z82,z5]),(0,[z0,z174,z1,z147,z3,z7])],[],[(0,[z0,z1,z220,z16,z3,z7]),(0,[z0,z1,z2,z1289,z7,z5]),(0,[z83,z1,z30,z3,z7,z132]),(0,[z54,z1,z70,z3,z7,z313]),(0,[z0,z1,z2,z117,z7,z742]),(0,[z0,z1,z2,z16,z7,z619])],[(0,[z0,z1,z1290,z3,z7,z5]),(0,[z0,z1,z2,z3,z7,z1291]),(0,[z0,z1,z2,z272,z167,z5])],[(0,[z0,z190,z2,z3,z7,z39]),(0,[z0,z89,z1,z3,z7,z456]),(0,[z0,z1,z70,z3,z7,z370]),(0,[z0,z1,z70,z242,z3,z7]),(0,[z0,z1154,z1,z3,z7,z5]),(0,[z0,z1,z2,z438,z225,z5]),(0,[z0,z1,z12,z16,z114,z7]),(0,[z0,z1,z2,z7,z353,z82]),(0,[z0,z195,z1,z2,z7,z14])],[(0,[z0,z1,z301,z3,z324,z5]),(0,[z0,z1,z2,z16,z77,z7]),(0,[z0,z1292,z1,z2,z3,z7]),(0,[z0,z1,z2,z1293,z3,z7]),(0,[z0,z1,z2,z28,z3,z625])],[(0,[z0,z1,z2,z3,z165,z328]),(0,[z0,z1,z2,z1294,z3,z7]),(0,[z0,z120,z65,z3,z7,z14]),(0,[z0,z1,z12,z114,z7,z5])],[(0,[z454,z1,z2,z62,z7,z5]),(0,[z0,z1,z2,z3,z244,z5]),(0,[z8,z502,z1,z2,z3,z7]),(0,[z0,z1,z2,z3,z300,z247])],[(0,[z0,z1,z2,z77,z7,z196]),(0,[z0,z1,z2,z3,z7,z1295]),(0,[z0,z1,z2,z3,z7,z1296]),(0,[z0,z1,z2,z160,z7,z82])],[(0,[z0,z568,z235,z3,z7,z5]),(0,[z0,z1169,z1,z2,z225,z5])],[(0,[z0,z1,z2,z3,z7,z1297]),(0,[z0,z1,z2,z62,z7,z125]),(0,[z0,z1,z2,z3,z7,z1298])],[(0,[z0,z221,z1,z3,z7,z39])],[(0,[z32,z1,z2,z16,z3,z148])],[(0,[z0,z1,z2,z3,z7,z14]),(0,[z0,z1,z1299,z3,z7,z5]),(0,[z0,z1,z147,z3,z148,z7]),(0,[z0,z1,z2,z3,z7,z1300]),(0,[z0,z1,z2,z3,z7,z1301])],[(0,[z141,z52,z2,z3,z7,z39]),(0,[z0,z1,z2,z40,z7,z46]),(0,[z0,z1,z2,z3,z7,z251]),(0,[z0,z1,z2,z1302,z3,z7]),(0,[z0,z1303,z2,z16,z3,z7])],[(0,[z0,z1,z2,z112,z7,z356]),(0,[z0,z1,z2,z1304,z7,z5]),(0,[z55,z1,z2,z3,z244,z133])]],
   [[(0,[z0,z1,z2,z3,z7,z1305])],[(0,[z0,z202,z2,z3,z7,z292]),(0,[z0,z1,z2,z3,z231,z39]),(0,[z0,z1,z2,z1306,z7,z5]),(0,[z0,z1,z2,z3,z7,z1307]),(0,[z0,z1,z147,z67,z3,z7])],[(0,[z116,z38,z2,z3,z7,z196]),(0,[z0,z1,z2,z3,z7,z1308]),(0,[z0,z1,z2,z191,z7,z14]),(0,[z0,z1,z235,z3,z7,z39]),(0,[z0,z1,z2,z348,z7,z14]),(0,[z0,z1,z2,z3,z7,z1309])],[(0,[z0,z1,z30,z3,z7,z39]),(0,[z0,z1,z2,z462,z7,z14]),(0,[z0,z1,z2,z3,z1228,z5])],[(0,[z0,z1,z2,z271,z7,z5]),(0,[z0,z381,z2,z16,z3,z7]),(0,[z0,z1,z2,z272,z7,z5]),(0,[z0,z155,z2,z3,z73,z5])],[(0,[z0,z1,z1310,z3,z7,z5]),(0,[z0,z189,z1,z2,z7,z14]),(0,[z0,z1,z1184,z3,z7,z5])],[(0,[z0,z1,z2,z3,z7,z1311]),(0,[z85,z1,z2,z62,z7,z292]),(0,[z0,z1,z242,z114,z7,z39])],[(0,[z0,z1,z2,z84,z7,z34]),(0,[z0,z381,z159,z3,z7,z5]),(0,[z0,z1,z1030,z3,z7,z5]),(0,[z0,z1,z2,z16,z3,z167]),(0,[z0,z1,z3,z756,z20,z5])],[(0,[z0,z1,z2,z3,z142,z356]),(0,[z0,z222,z2,z3,z7,z34]),(0,[z0,z201,z2,z3,z160,z86]),(0,[z0,z138,z1,z2,z7,z82]),(0,[z0,z1,z147,z3,z79,z7])],[(0,[z0,z1,z2,z3,z7,z213]),(0,[z0,z211,z1,z3,z7,z5]),(0,[z0,z1,z147,z122,z3,z7])],[(0,[z250,z38,z2,z3,z7,z5]),(0,[z0,z1,z2,z3,z7,z1312]),(0,[z0,z1,z2,z127,z3,z7]),(0,[z0,z11,z1,z12,z7,z14]),(0,[z0,z1,z2,z3,z7,z396]),(0,[z0,z1,z2,z3,z7,z1313]),(0,[z0,z1,z2,z7,z184,z82]),(0,[z0,z1314,z1,z147,z3,z7])],[(0,[z0,z1,z2,z16,z3,z97]),(0,[z0,z1,z2,z1261,z3,z7]),(0,[z0,z201,z2,z208,z3,z160]),(0,[z0,z157,z2,z3,z7,z230])],[(0,[z0,z1,z2,z3,z97,z39]),(0,[z55,z1,z2,z272,z7,z133])],[(0,[z0,z1,z70,z3,z7,z356]),(0,[z0,z1,z2,z3,z7,z1315]),(0,[z0,z1,z2,z3,z602,z224]),(0,[z0,z296,z1,z147,z3,z7])],[(0,[z0,z1,z301,z3,z7,z5]),(0,[z0,z1,z460,z16,z3,z7]),(0,[z0,z1,z2,z3,z736,z5]),(0,[z0,z1,z2,z7,z82,z35]),(0,[z0,z1,z12,z7,z371,z5])],[(0,[z0,z1,z2,z864,z3,z7]),(0,[z0,z1,z2,z3,z7,z1316]),(0,[z0,z1,z2,z3,z7,z1317]),(0,[z0,z1,z2,z3,z7,z1318]),(0,[z0,z1319,z1,z2,z3,z7]),(0,[z0,z1,z2,z3,z7,z1320]),(0,[z0,z157,z1,z2,z7,z82]),(0,[z0,z1,z2,z16,z140,z7])]],
   [[(0,[z0,z1,z30,z3,z7,z370]),(0,[z0,z1,z30,z242,z3,z7]),(0,[z0,z1321,z2,z3,z7,z5]),(0,[z613,z1,z2,z3,z7,z133]),(1,[z0,z2,z7,z829,z5])],[(0,[z0,z1322,z1,z2,z3,z7]),(0,[z0,z1,z2,z3,z7,z1323]),(0,[z0,z1,z2,z3,z7,z1324]),(0,[z0,z1,z2,z282,z218,z225]),(0,[z0,z211,z1,z3,z7,z14])],[(0,[z0,z1,z2,z3,z7,z313]),(0,[z0,z1,z2,z3,z7,z1325])],[(0,[z0,z1,z2,z1326,z3,z7]),(0,[z298,z1,z2,z434,z3,z7])],[(0,[z0,z1,z2,z1327,z7,z5]),(0,[z0,z1,z2,z3,z1328,z5])],[(0,[z0,z1,z2,z3,z7,z1329]),(0,[z0,z120,z495,z3,z7,z5]),(0,[z0,z174,z1,z2,z3,z129]),(0,[z0,z1,z2,z3,z7,z1330]),(0,[z0,z1,z2,z3,z1331,z5])],[(0,[z0,z332,z1,z2,z3,z7]),(0,[z0,z1,z2,z3,z7,z1332]),(0,[z0,z381,z2,z3,z7,z125]),(0,[z0,z1,z2,z127,z7,z14])],[(0,[z0,z96,z2,z112,z7,z5]),(0,[z0,z263,z1,z2,z7,z82]),(0,[z0,z1,z2,z3,z7,z1333]),(0,[z0,z11,z1,z7,z34,z71]),(0,[z0,z1,z147,z3,z7,z51])],[(0,[z0,z1,z2,z3,z7,z1334]),(0,[z54,z1,z70,z3,z7,z5]),(0,[z0,z1,z2,z1335,z7,z5]),(0,[z0,z1,z2,z3,z7,z1336]),(0,[z0,z1,z2,z3,z7,z1337]),(0,[z0,z1338,z1,z2,z3,z7])],[(0,[z0,z1,z220,z3,z7,z14]),(0,[z0,z1,z2,z112,z105,z5]),(0,[z0,z1,z2,z16,z351,z7]),(0,[z0,z1,z1339,z3,z7,z5])],[(0,[z0,z1,z1340,z3,z7,z5]),(0,[z0,z190,z2,z3,z7,z356]),(0,[z0,z1341,z1,z2,z3,z5]),(0,[z0,z1,z162,z147,z3,z7]),(0,[z0,z120,z65,z3,z7,z226])],[(0,[z0,z1,z2,z3,z7,z1342]),(0,[z0,z1,z2,z3,z7,z1343]),(0,[z0,z522,z11,z1,z7,z39]),(0,[z0,z1,z2,z16,z539,z7])],[(0,[z0,z1,z2,z1182,z3,z7]),(0,[z83,z0,z1,z147,z3,z7]),(0,[z454,z1,z30,z3,z7,z5]),(0,[z0,z222,z2,z3,z7,z39])],[(0,[z0,z1,z2,z3,z7,z1344]),(0,[z0,z1,z2,z1345,z3,z7]),(0,[z0,z17,z1,z147,z3,z7])],[(0,[z0,z1,z3,z7,z371,z173])],[(0,[z0,z1,z2,z3,z324,z5]),(0,[z0,z2,z3,z7,z1346,z5]),(0,[z0,z1,z2,z3,z7,z1347]),(0,[z0,z198,z2,z3,z148,z5]),(0,[z0,z1,z2,z1348,z3,z7])]],
   [[(0,[z0,z96,z2,z3,z142,z5]),(0,[z54,z1,z70,z3,z7,z14]),(0,[z0,z1349,z1,z2,z3,z7]),(0,[z0,z1,z2,z277,z7,z14])],[(0,[z644,z1,z2,z3,z165,z5]),(0,[z0,z1,z2,z3,z7,z226]),(0,[z0,z1,z1350,z3,z7,z5]),(1,[z0,z1169,z1,z2,z5]),(0,[z0,z1,z2,z391,z7,z14]),(0,[z0,z48,z1,z147,z3,z7])],[(0,[z0,z1045,z1,z2,z7,z456]),(0,[z0,z1,z2,z3,z7,z1222]),(0,[z0,z1,z23,z3,z7,z92]),(0,[z0,z1,z3,z7,z840,z39])],[(0,[z0,z1,z2,z3,z7,z1351]),(0,[z0,z109,z1,z7,z71,z5]),(0,[z0,z1352,z1,z2,z3,z7]),(0,[z0,z1,z2,z7,z66,z82]),(0,[z0,z1,z2,z985,z7,z34])],[(0,[z0,z1,z2,z3,z7,z1353]),(0,[z0,z1,z2,z1354,z7,z5]),(0,[z0,z355,z235,z3,z7,z5]),(0,[z0,z1,z2,z3,z7,z1355])],[(0,[z0,z1,z1356,z3,z7,z5]),(0,[z0,z1,z2,z208,z3,z7]),(0,[z0,z263,z2,z3,z736,z5])],[(0,[z1,z70,z847,z3,z7,z5]),(0,[z0,z1,z22,z3,z7,z125]),(0,[z0,z198,z2,z3,z7,z34])],[(0,[z0,z1,z2,z3,z324,z14]),(0,[z0,z1,z70,z3,z105,z5]),(0,[z0,z1,z2,z3,z167,z5]),(0,[z0,z215,z341,z1,z2,z5]),(0,[z0,z1,z2,z3,z1357,z5]),(0,[z0,z1,z2,z242,z7,z71])],[(0,[z0,z1,z2,z1358,z7,z5]),(0,[z0,z1359,z2,z3,z7,z5]),(0,[z0,z202,z2,z3,z7,z34]),(0,[z0,z1,z2,z3,z97,z125]),(0,[z637,z1,z2,z40,z7,z5]),(0,[z0,z1,z23,z117,z7,z5]),(0,[z0,z1,z2,z7,z82,z1360])],[(0,[z0,z1,z30,z3,z7,z356]),(0,[z85,z202,z2,z62,z7,z5]),(0,[z0,z1,z2,z16,z7,z698]),(0,[z0,z1,z2,z7,z34,z1136]),(0,[z0,z1,z2,z16,z1361,z3])],[(0,[z0,z1,z2,z3,z1362,z5]),(0,[z0,z102,z1,z2,z3,z7]),(0,[z0,z1,z2,z1363,z7,z5]),(0,[z0,z1,z385,z2,z7,z14]),(0,[z0,z341,z1169,z1,z2,z5])],[(0,[z0,z1,z2,z3,z7,z1364]),(0,[z0,z1,z2,z3,z7,z1365]),(0,[z0,z1,z2,z3,z7,z320]),(0,[z0,z560,z1,z2,z28,z3])],[(0,[z0,z1,z2,z16,z272,z7]),(0,[z0,z1,z147,z147,z3,z7])],[(0,[z0,z1,z2,z3,z7,z1366]),(0,[z0,z1,z2,z3,z7,z1367]),(0,[z0,z1,z430,z3,z7,z39]),(0,[z0,z1,z2,z367,z7,z5]),(0,[z85,z1,z2,z62,z7,z34])],[(0,[z0,z1,z159,z62,z7,z5]),(0,[z0,z1,z2,z1368,z7,z5]),(0,[z0,z1,z421,z3,z7,z39]),(0,[z0,z1,z2,z3,z7,z1369])],[(0,[z55,z1,z2,z3,z167,z133])]],
   [[(0,[z0,z1370,z1,z2,z3,z7]),(0,[z0,z1,z2,z3,z7,z1371]),(0,[z0,z1,z2,z610,z7,z14])],[(0,[z55,z1,z2,z434,z3,z7]),(0,[z0,z120,z65,z3,z7,z5]),(0,[z0,z1,z2,z7,z1372,z82])],[(0,[z0,z550,z2,z3,z73,z5]),(0,[z0,z1,z2,z3,z7,z1373]),(0,[z0,z1,z23,z16,z3,z7]),(0,[z0,z1,z2,z3,z7,z1374]),(0,[z0,z1,z2,z3,z1174,z5])],[],[(0,[z116,z38,z2,z3,z7,z34]),(0,[z0,z190,z2,z3,z105,z5]),(0,[z0,z1,z2,z3,z824,z5]),(0,[z0,z1,z2,z3,z7,z1375]),(0,[z0,z11,z1,z7,z71,z14]),(0,[z0,z1,z147,z3,z7,z34])],[(1,[z0,z1,z2,z7,z796]),(0,[z0,z198,z2,z3,z165,z5]),(0,[z0,z1,z460,z3,z7,z14]),(0,[z0,z1,z2,z367,z7,z14]),(0,[z0,z1,z235,z351,z7,z5]),(0,[z0,z1,z299,z3,z7,z39]),(0,[z0,z1376,z2,z3,z7,z5]),(0,[z0,z1,z2,z3,z7,z1377])],[(0,[z0,z1,z2,z3,z7,z1378]),(0,[z0,z222,z2,z3,z7,z422]),(0,[z0,z195,z1,z2,z7,z88]),(0,[z0,z89,z1,z150,z3,z7])],[(0,[z32,z1,z2,z3,z824,z5]),(0,[z0,z568,z2,z3,z7,z34]),(0,[z0,z1,z2,z1379,z3,z7]),(0,[z0,z1,z2,z3,z875,z39])],[(0,[z0,z1,z2,z3,z7,z5]),(0,[z1,z847,z30,z3,z7,z5]),(0,[z15,z1,z23,z3,z165,z5]),(0,[z0,z11,z1,z2,z7,z1040]),(0,[z0,z1,z2,z1380,z3,z7]),(0,[z0,z138,z1,z147,z3,z7]),(0,[z0,z1,z2,z3,z7,z1381]),(0,[z0,z1,z147,z3,z7,z225])],[(0,[z83,z190,z30,z3,z7,z5]),(0,[z0,z1,z2,z3,z7,z1382])],[(0,[z0,z1,z493,z3,z7,z39]),(0,[z0,z198,z2,z3,z7,z39]),(0,[z0,z1,z464,z3,z7,z39])],[(0,[z0,z1,z2,z3,z7,z1383]),(0,[z0,z1,z220,z3,z324,z5]),(0,[z0,z1,z2,z3,z7,z1384]),(0,[z0,z1,z2,z1385,z7,z5])],[(0,[z0,z1,z2,z1386,z3,z7]),(0,[z0,z202,z2,z3,z7,z39]),(0,[z32,z1,z2,z3,z148,z39]),(0,[z0,z1,z2,z1387,z3,z7]),(0,[z0,z1,z2,z3,z7,z1388])],[(0,[z0,z1,z2,z1012,z7,z5]),(0,[z0,z1,z1389,z3,z7,z5]),(0,[z0,z1,z1390,z2,z3,z7]),(0,[z0,z1,z2,z3,z7,z1391]),(0,[z0,z1,z1392,z3,z7,z5]),(0,[z1393,z1,z2,z3,z7,z5]),(0,[z0,z27,z2,z3,z7,z836]),(0,[z0,z27,z2,z3,z7,z176])],[(0,[z0,z1,z2,z112,z7,z1285]),(0,[z0,z1394,z2,z3,z7,z5]),(0,[z0,z1,z2,z3,z7,z1395]),(0,[z538,z1,z70,z3,z7,z5]),(0,[z0,z1,z2,z3,z7,z1396])],[(0,[z0,z1,z2,z3,z1397,z7])]],
   [[(0,[z0,z1,z2,z271,z4,z5]),(0,[z0,z1,z2,z3,z1398,z5]),(0,[z0,z1,z2,z40,z7,z82]),(0,[z55,z1,z2,z3,z7,z133]),(0,[z0,z87,z2,z3,z7,z836]),(0,[z0,z1,z2,z3,z7,z840]),(0,[z405,z0,z1,z2,z7,z82])],[(0,[z0,z190,z2,z16,z3,z7]),(0,[z0,z1399,z2,z3,z7,z5]),(0,[z0,z1,z2,z30,z7,z82]),(0,[z0,z1,z22,z3,z7,z1217]),(0,[z85,z1,z2,z62,z7,z39]),(0,[z0,z1,z2,z1400,z3,z7]),(0,[z0,z11,z1,z16,z7,z71]),(0,[z0,z1,z2,z421,z7,z82])],[(0,[z0,z1,z2,z3,z1401,z5])],[(0,[z0,z1,z30,z3,z105,z5]),(0,[z0,z1,z2,z40,z231,z5]),(0,[z0,z1,z2,z1402,z3,z7]),(0,[z0,z211,z91,z1,z7,z5])],[(0,[z149,z1,z2,z40,z7,z5]),(0,[z0,z1,z1403,z3,z7,z5])],[(0,[z0,z1,z2,z1361,z3,z5]),(0,[z0,z1,z2,z3,z7,z1404])],[(0,[z0,z1,z2,z1405,z7,z5])],[(0,[z0,z1,z2,z3,z7,z1406]),(0,[z0,z263,z1,z147,z3,z7]),(0,[z0,z91,z1,z2,z242,z7])],[(0,[z0,z535,z1,z2,z7,z14]),(0,[z0,z1,z147,z3,z7,z39])],[(0,[z0,z1,z2,z1407,z3,z7]),(0,[z607,z52,z2,z3,z7,z5]),(0,[z0,z1,z2,z3,z7,z1408]),(0,[z0,z1,z2,z218,z225,z34]),(0,[z0,z1,z2,z429,z225,z5]),(0,[z0,z1,z2,z3,z7,z1409]),(0,[z0,z1,z339,z147,z3,z7])],[(0,[z0,z1,z301,z3,z4,z5]),(0,[z0,z1,z2,z1410,z7,z5]),(0,[z0,z1,z2,z1411,z3,z5]),(0,[z0,z1,z37,z2,z7,z82])],[(0,[z0,z1412,z1,z2,z3,z7]),(0,[z141,z52,z2,z16,z3,z7]),(0,[z0,z1,z2,z3,z7,z1413]),(0,[z0,z366,z1,z2,z3,z7]),(0,[z0,z1,z2,z1414,z7,z5]),(0,[z0,z2,z3,z7,z736,z5]),(0,[z0,z569,z1,z2,z16,z7]),(0,[z0,z1,z411,z3,z7,z39])],[(0,[z0,z1,z2,z3,z7,z1415]),(0,[z0,z1,z3,z7,z371,z39])],[(0,[z0,z1,z2,z28,z122,z3])],[(0,[z0,z1,z2,z1402,z40,z7]),(0,[z0,z87,z2,z3,z7,z463]),(0,[z0,z1036,z2,z3,z7,z5])],[(0,[z0,z1,z2,z1402,z7,z14]),(0,[z0,z24,z162,z3,z7,z106]),(0,[z0,z1063,z1,z2,z7,z34]),(0,[z0,z211,z1,z7,z5,z14]),(0,[z0,z134,z2,z171,z3,z7])]],
   [[(0,[z0,z542,z2,z3,z73,z5]),(0,[z0,z1,z460,z3,z7,z1416]),(0,[z0,z1,z2,z1417,z7,z5])],[(0,[z0,z509,z1,z7,z71,z5]),(0,[z1,z2,z3,z863,z7,z5]),(0,[z0,z1,z2,z1044,z7,z5]),(0,[z0,z1,z2,z16,z7,z260])],[(0,[z54,z0,z1,z2,z7,z82]),(0,[z0,z1,z2,z62,z7,z14]),(0,[z0,z1,z2,z3,z7,z1418]),(0,[z0,z1,z2,z3,z7,z1419])],[(0,[z116,z38,z2,z3,z7,z455]),(0,[z0,z121,z162,z3,z7,z5]),(0,[z0,z1420,z1,z2,z3,z7]),(0,[z0,z1,z2,z3,z148,z422])],[(0,[z0,z1,z220,z3,z7,z5]),(0,[z0,z198,z2,z3,z7,z422]),(0,[z1,z2,z3,z7,z800,z133]),(0,[z0,z1,z147,z3,z7,z56]),(0,[z0,z2,z18,z7,z829,z5]),(0,[z0,z1,z2,z3,z7,z1040])],[(0,[z0,z1,z2,z350,z7,z14])],[(0,[z0,z1,z2,z40,z7,z217])],[(0,[z0,z1,z22,z16,z3,z7]),(0,[z0,z1,z2,z3,z7,z1421]),(0,[z0,z1,z28,z147,z3,z7])],[(0,[z1,z2,z3,z148,z824,z5]),(0,[z0,z1,z539,z3,z7,z39])],[(0,[z0,z222,z2,z3,z7,z92]),(0,[z0,z1,z2,z16,z367,z7]),(0,[z1422,z1,z2,z3,z7,z5]),(0,[z0,z1,z2,z295,z7,z14]),(0,[z0,z27,z2,z3,z7,z643]),(0,[z0,z1,z2,z1060,z7,z5])],[(0,[z0,z1,z2,z3,z7,z1423]),(0,[z85,z1,z2,z16,z62,z7])],[(0,[z0,z1,z2,z3,z7,z1416]),(0,[z1424,z1,z2,z3,z7,z5]),(0,[z0,z1,z2,z1425,z3,z7])],[(0,[z0,z1,z2,z1426,z3,z7]),(0,[z507,z52,z2,z3,z7,z5]),(0,[z0,z1,z2,z3,z7,z132]),(0,[z0,z1,z159,z3,z97,z5]),(0,[z521,z1,z2,z62,z7,z5]),(0,[z0,z1,z2,z3,z7,z1427]),(0,[z0,z1,z2,z3,z7,z1428])],[(0,[z0,z1,z2,z148,z7,z82]),(0,[z0,z1,z1429,z3,z7,z5]),(0,[z0,z1,z2,z936,z7,z39]),(0,[z0,z1,z2,z218,z225,z39]),(0,[z0,z1,z2,z602,z7,z82]),(0,[z0,z1,z147,z3,z7,z173])],[(0,[z0,z1,z2,z84,z7,z39]),(0,[z0,z1,z2,z3,z7,z1430]),(0,[z0,z58,z2,z3,z7,z394]),(0,[z0,z211,z1,z2,z7,z14])],[(0,[z130,z38,z2,z3,z7,z5]),(0,[z0,z1,z2,z62,z7,z396]),(0,[z0,z222,z2,z117,z7,z5])]],
   [[(0,[z0,z1,z2,z3,z231,z125]),(0,[z0,z1303,z2,z3,z7,z5]),(0,[z0,z1,z2,z127,z272,z7]),(0,[z0,z583,z1,z3,z7,z34]),(0,[z0,z1,z2,z3,z7,z599])],[(0,[z83,z1,z30,z112,z7,z5]),(0,[z80,z1,z2,z3,z7,z285]),(0,[z0,z195,z1,z2,z7,z82])],[(0,[z0,z1,z2,z3,z7,z1172]),(0,[z0,z1,z2,z1431,z7,z5]),(0,[z0,z1432,z1,z2,z3,z7]),(0,[z0,z1,z38,z2,z7,z82]),(0,[z130,z1,z30,z3,z7,z5]),(0,[z0,z1,z556,z3,z7,z39]),(0,[z0,z355,z2,z3,z7,z34]),(0,[z0,z11,z1,z7,z71,z320]),(0,[z0,z1,z12,z210,z7,z14]),(0,[z0,z1092,z2,z3,z7,z34])],[(0,[z0,z1,z2,z1433,z3,z7]),(0,[z0,z1,z2,z946,z7,z39]),(0,[z0,z1,z2,z28,z729,z3])],[(0,[z0,z1,z2,z3,z7,z1434]),(0,[z0,z1,z12,z70,z7,z14]),(0,[z0,z1,z2,z3,z7,z1435]),(0,[z0,z1436,z1,z2,z3,z7]),(0,[z0,z812,z2,z16,z3,z7])],[(0,[z0,z1,z2,z1437,z7,z5]),(0,[z0,z1,z460,z367,z7,z5]),(0,[z0,z1438,z1,z2,z3,z7]),(0,[z0,z790,z2,z3,z7,z5]),(0,[z0,z87,z2,z3,z7,z53]),(0,[z0,z1,z2,z7,z82,z82]),(0,[z0,z813,z2,z16,z3,z7])],[(0,[z0,z381,z2,z3,z7,z5]),(0,[z0,z1,z2,z3,z7,z1439]),(0,[z0,z1,z1440,z3,z7,z5]),(0,[z0,z1,z19,z3,z79,z344]),(0,[z650,z1,z2,z3,z7,z353]),(0,[z0,z1,z2,z3,z7,z1441])],[(0,[z0,z27,z2,z3,z7,z306])],[(0,[z0,z1,z2,z3,z7,z1442]),(0,[z0,z1,z2,z3,z6,z51]),(0,[z0,z1,z2,z3,z1443,z5]),(0,[z0,z1,z2,z3,z7,z1444]),(0,[z0,z1,z2,z7,z34,z82]),(0,[z0,z1,z2,z16,z3,z921]),(0,[z0,z1445,z2,z3,z7,z5])],[(0,[z0,z1,z2,z3,z165,z422]),(1,[z1,z2,z3,z7,z800])],[(0,[z83,z1,z30,z3,z142,z5]),(0,[z0,z609,z2,z3,z7,z35]),(0,[z0,z1446,z2,z3,z7,z5])],[(0,[z0,z1,z1447,z3,z7,z5]),(0,[z0,z1,z2,z3,z7,z46])],[(0,[z0,z1,z2,z3,z7,z796]),(0,[z0,z1,z2,z1448,z3,z7]),(0,[z0,z1,z1449,z3,z7,z5]),(0,[z0,z1450,z2,z3,z7,z5])],[(0,[z0,z1,z2,z77,z7,z34]),(0,[z0,z45,z360,z1,z2,z5]),(0,[z13,z1,z2,z3,z7,z133]),(0,[z0,z1,z2,z3,z7,z1451])],[(0,[z0,z381,z2,z3,z7,z14]),(0,[z0,z1452,z2,z3,z7,z5]),(0,[z0,z317,z1,z3,z7,z39]),(0,[z0,z1,z2,z7,z34,z1453])],[(0,[z83,z1,z847,z3,z7,z5]),(0,[z0,z11,z1,z7,z71,z5])]],
   [[(0,[z0,z1,z460,z3,z7,z5]),(0,[z0,z1,z2,z3,z7,z1454])],[(0,[z0,z11,z1,z7,z39,z14])],[(0,[z0,z1101,z2,z3,z7,z5]),(0,[z0,z987,z1,z2,z7,z5])],[(0,[z0,z1,z2,z351,z7,z34]),(0,[z0,z1,z3,z7,z603,z39])],[(0,[z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z474,z7,z14]),(0,[z0,z45,z1169,z1,z2,z5])],[(0,[z116,z38,z2,z77,z7,z5]),(0,[z0,z1,z7,z905,z71,z5]),(0,[z0,z1,z608,z3,z7,z39])],[(0,[z0,z355,z2,z3,z7,z39]),(1,[z0,z1,z2,z7,z82])],[(0,[z0,z1,z2,z3,z7,z1149]),(0,[z0,z198,z2,z3,z7,z92]),(0,[z477,z1,z2,z3,z165,z5]),(0,[z0,z672,z1,z3,z7,z34]),(0,[z267,z1,z2,z107,z3,z7])],[(0,[z0,z1,z2,z1455,z7,z5]),(0,[z0,z1,z2,z581,z7,z14]),(0,[z0,z1,z3,z7,z868,z39]),(0,[z0,z1,z2,z1456,z7,z5]),(0,[z0,z494,z2,z3,z7,z176])],[(0,[z0,z1,z2,z3,z7,z1457]),(0,[z0,z1,z2,z3,z7,z1458]),(0,[z0,z1,z617,z3,z7,z39]),(0,[z0,z1,z2,z1459,z3,z7])],[(0,[z113,z1,z2,z40,z7,z34]),(0,[z0,z1,z19,z3,z79,z34]),(0,[z0,z1,z37,z147,z3,z7])],[(0,[z0,z38,z2,z271,z7,z5]),(0,[z0,z1460,z1,z2,z7,z5]),(0,[z0,z1,z2,z7,z82,z53])],[(0,[z0,z1,z2,z3,z4,z14]),(0,[z0,z1,z2,z117,z148,z5]),(0,[z0,z1,z12,z147,z3,z7])],[(0,[z0,z1461,z1,z2,z3,z7]),(0,[z0,z2,z3,z7,z1462,z5]),(0,[z0,z198,z2,z117,z7,z5]),(0,[z0,z263,z2,z3,z34,z73]),(0,[z0,z1,z2,z7,z82,z71]),(0,[z0,z1143,z2,z3,z7,z5]),(0,[z0,z1,z3,z7,z34,z840])],[(0,[z521,z38,z2,z3,z7,z5]),(0,[z0,z96,z2,z3,z7,z34]),(0,[z0,z202,z2,z40,z7,z5]),(0,[z0,z1,z22,z3,z7,z14]),(0,[z0,z1,z2,z3,z129,z7]),(0,[z0,z568,z2,z351,z7,z5]),(0,[z0,z1,z2,z3,z7,z1463]),(0,[z0,z1,z2,z3,z7,z1464])],[(0,[z0,z1,z2,z3,z7,z1465]),(0,[z0,z1466,z1,z2,z7,z5]),(0,[z0,z1,z2,z7,z1453,z5])]],
   [[(0,[z0,z1,z2,z3,z105,z34])],[(0,[z0,z1,z2,z77,z7,z39]),(0,[z0,z1,z2,z3,z7,z1467]),(0,[z0,z1,z2,z3,z1468,z5]),(0,[z0,z1,z2,z3,z7,z1469]),(0,[z0,z120,z1,z2,z7,z82])],[(0,[z0,z1,z2,z3,z1470,z5]),(0,[z54,z0,z1,z147,z3,z7]),(0,[z0,z355,z2,z3,z7,z56]),(0,[z440,z1,z2,z3,z7,z56]),(0,[z0,z1,z2,z3,z7,z88])],[(0,[z85,z1,z2,z863,z7,z5]),(0,[z0,z1,z2,z117,z7,z34]),(0,[z0,z1,z2,z240,z7,z173])],[(0,[z0,z1,z2,z84,z7,z356]),(0,[z0,z1,z2,z3,z1471,z5]),(0,[z0,z1,z2,z1472,z7,z5]),(0,[z1473,z1,z2,z3,z7,z5]),(1,[z0,z2,z3,z736,z5])],[(0,[z0,z38,z301,z3,z7,z5]),(0,[z0,z1,z2,z3,z7,z868]),(0,[z0,z1,z2,z199,z3,z7]),(0,[z0,z1,z2,z752,z3,z7])],[(0,[z0,z1,z2,z516,z7,z14]),(0,[z0,z1,z147,z40,z3,z7]),(0,[z0,z1,z2,z3,z7,z1474]),(0,[z0,z1,z2,z752,z67,z7])],[(0,[z0,z1,z2,z3,z7,z1475]),(0,[z0,z1,z2,z351,z7,z39]),(0,[z80,z1,z2,z3,z7,z133]),(0,[z8,z1,z2,z3,z7,z800]),(0,[z0,z1,z2,z7,z1476,z5]),(0,[z0,z1,z3,z79,z756,z5]),(0,[z0,z1,z147,z421,z3,z7])],[(0,[z0,z1477,z1,z2,z3,z7]),(0,[z0,z1,z2,z112,z7,z5]),(0,[z209,z1,z2,z62,z7,z5]),(0,[z0,z1,z2,z3,z7,z1478])],[(0,[z0,z1,z2,z271,z7,z196]),(0,[z0,z1,z2,z1479,z7,z5]),(0,[z0,z1,z2,z3,z7,z1480]),(0,[z0,z1481,z1,z2,z7,z82])],[(0,[z0,z486,z2,z7,z280,z5]),(0,[z0,z1,z1482,z2,z7,z5]),(0,[z0,z1,z2,z3,z7,z1483]),(0,[z0,z2,z3,z160,z736,z5])],[(0,[z116,z38,z2,z3,z7,z39]),(0,[z0,z17,z2,z7,z280,z466])],[(0,[z0,z1,z2,z77,z7,z455]),(0,[z0,z1,z2,z7,z1484,z5])],[(0,[z0,z1,z2,z3,z7,z1485]),(0,[z0,z1486,z2,z3,z7,z5]),(0,[z0,z1,z1487,z2,z3,z7]),(0,[z0,z1,z259,z3,z7,z34])],[(0,[z0,z1488,z2,z3,z7,z5]),(0,[z113,z1,z2,z40,z7,z39]),(0,[z0,z568,z2,z3,z7,z39]),(0,[z0,z1,z3,z7,z88,z39]),(0,[z0,z720,z2,z3,z7,z5])],[(0,[z0,z566,z162,z3,z7,z5]),(0,[z0,z1,z2,z308,z7,z14]),(0,[z0,z1,z2,z3,z7,z1489]),(0,[z0,z1,z12,z2,z7,z82])]]]

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
theorem pb0 : chunkB SB 1 ((bkA.flatten.flatten.drop 0).take 482) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb1 : chunkB SB 1 ((bkA.flatten.flatten.drop 482).take 483) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb2 : chunkB SB 1 ((bkA.flatten.flatten.drop 965).take 471) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pbend : ((bkA.flatten.flatten.drop 1436)).isEmpty = true := by
  decide +kernel

theorem windowsB : windowsG (chunkB SB 1) bkA.flatten.flatten 0 [482, 483, 471] = true :=
  windowsG_cons pb0 (windowsG_cons pb1 (windowsG_cons pb2 (windowsG_nil pbend)))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc0 : chunkOK 5 ((bkB.flatten.drop 0).take 86).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc1 : chunkOK 5 ((bkB.flatten.drop 86).take 86).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc2 : chunkOK 5 ((bkB.flatten.drop 172).take 88).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc3 : chunkOK 5 ((bkB.flatten.drop 260).take 91).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc4 : chunkOK 5 ((bkB.flatten.drop 351).take 101).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc5 : chunkOK 5 ((bkB.flatten.drop 452).take 60).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pcend : ((bkB.flatten.drop 512)).isEmpty = true := by
  decide +kernel

theorem windowsC : windowsF 5 bkB.flatten 0 [86, 86, 88, 91, 101, 60] = true :=
  windowsF_cons pc0 (windowsF_cons pc1 (windowsF_cons pc2 (windowsF_cons pc3 (windowsF_cons pc4 (windowsF_cons pc5 (windowsF_nil pcend))))))

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

end PEqualNP.Outside.L_meta_41042

theorem PEqualNP.Outside.L_meta_41042 :
    ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276808426 * 2 ^ 32 + 4276808360) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276808426 * 2 ^ 32 + 4276808360) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  exact PEqualNP.Outside.L_meta_41042.solve