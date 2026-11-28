import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_37369

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
  Nat.testBit (3937069736 * 2 ^ 32 + 3937052808) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

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
  [(0x6a800080cd0124d5#64 ++ 0xfffc7f87ff0fffff#64 : BitVec 128),
   (0x1501aa3a2274922a#64 ++ 0x1fffaa7a23f4923f#64 : BitVec 128),
   (0xa606cc5c34b8e34c#64 ++ 0xe65fcc7c3cf8e3cc#64 : BitVec 128),
   (0xd80b706f40df03b0#64 ++ 0xf81ff07fc0ff03f0#64 : BitVec 128),
   (0x0013ff0000eed800#64 ++ 0x0017ff8000fffc00#64 : BitVec 128),
   (0x0023fff7bb000000#64 ++ 0x001bffffff000000#64 : BitVec 128)]

def witness : Circuit :=
  ⟨[⟨.and, [2, 3]⟩, ⟨.and, [1, 6]⟩, ⟨.or, [0, 7]⟩, ⟨.or, [1, 6]⟩, ⟨.and, [0, 9]⟩, ⟨.or, [10, 4]⟩, ⟨.or, [2, 3]⟩, ⟨.and, [12, 5]⟩, ⟨.or, [13, 11]⟩, ⟨.and, [8, 14]⟩], 15⟩

def mkw (a b : BitVec 64) : W := a ++ b

def z0 : W := mkw 0x0013ff0000eed800 0x0017ff8000fffc00

def z1 : W := mkw 0x0023fff7bb000000 0x001bffffff000000

def z2 : W := mkw 0x1501aa3a2274922a 0x1fffaa7a23f4923f

def z3 : W := mkw 0x1533ffffbbfeda2a 0x1ffffffffffffe3f

def z4 : W := mkw 0x6a800080cd0124d5 0xfffc7f87ff0fffff

def z5 : W := mkw 0xa606cc5c34b8e34c 0xe65fcc7c3cf8e3cc

def z6 : W := mkw 0xd80b706f40df03b0 0xf81ff07fc0ff03f0

def z7 : W := mkw 0x150000080074922a 0x0000000000f00000

def z8 : W := mkw 0x6a800080cd0124d5 0x1fe03f83ff07fc3f

def z9 : W := mkw 0x0000000000000000 0x00142a0000049000

def z10 : W := mkw 0x002000f7bb000000 0x0008007fff000000

def z11 : W := mkw 0xb707ee7e36fcf36e 0xffffee7e3ffcf3ff

def z12 : W := mkw 0x05008a102220900a 0x07e00a002300900f

def z13 : W := mkw 0x0003706700000000 0x001bf07fc0000000

def z14 : W := mkw 0x00108f0000eed800 0x00040f8000fffc00

def z15 : W := mkw 0x1513ff3a22feda2a 0x0003807800f00000

def z16 : W := mkw 0x00208ff7bb000000 0x00080fffff000000

def z17 : W := mkw 0x6a800080cd0124d5 0xffe80f87ff00ffff

def z18 : W := mkw 0x0011bb0000669800 0x0017bb8000f79c00

def z19 : W := mkw 0x0002cc0000a8c000 0x0017cc0000f8e000

def z20 : W := mkw 0x00125500008a4800 0x00005580000b6c00

def z21 : W := mkw 0x0033fff7bbeed800 0x001bfffffff00000

def z22 : W := mkw 0xfe0f707f74df23fc 0xfe5ff07ffcff03fc

def z23 : W := mkw 0x0003ff0000000000 0x0003800000000000

def z24 : W := mkw 0x1523ffffbb74922a 0x1ffffffffff4923f

def z25 : W := mkw 0x8406cc5c30b8c308 0x0003807800f00000

def z26 : W := mkw 0xa604005c3410234c 0xe648007c3c0003cc

def z27 : W := mkw 0x59093223424710b2 0x19a03203c3071033

def z28 : W := mkw 0x228000808d002445 0x1ffc2f823f04fe3f

def z29 : W := mkw 0x4800000040010090 0x18003003c0070030

def z30 : W := mkw 0x0033fff7bbeed800 0x001ffffffffffc00

def z31 : W := mkw 0xd8080008401103b0 0xf8000000000003f0

def z32 : W := mkw 0x0003700000ce0000 0x0017f00000ff0000

def z33 : W := mkw 0x00108f000020d800 0x00000f800000fc00

def z34 : W := mkw 0xd808000840df03b0 0xf81c7007c0ff03f0

def z35 : W := mkw 0x6aa133a3cf0124d5 0xfffc7f87ff0fffff

def z36 : W := mkw 0x0013ff6700eed800 0x001fffffc0fffc00

def z37 : W := mkw 0x6a800080cd0124d5 0xffe40f803f0fffff

def z38 : W := mkw 0x26048c103420e04c 0x06400c003c00e00c

def z39 : W := mkw 0x58093023404700b0 0x18003003c0070030

def z40 : W := mkw 0x1503ff3a2274922a 0x1ffffffa23f4923f

def z41 : W := mkw 0x1513ff3a22feda2a 0x1ffffffa23fffe3f

def z42 : W := mkw 0xa616cf5c34b8fb4c 0xe65fcffc3cf8ffcc

def z43 : W := mkw 0x0002cc5430000000 0x001bcc7c3c000000

def z44 : W := mkw 0x002255c599000000 0x00005585dc000000

def z45 : W := mkw 0xee86ccdcfdb9e7dd 0xe65fddfdfcfbefcc

def z46 : W := mkw 0x1001202a00540220 0x181fa07a00f40230

def z47 : W := mkw 0xc80a5045408b0190 0xe0005005c00b01c0

def z48 : W := mkw 0x4803700040cf0090 0xf81ff007c0ff03f0

def z49 : W := mkw 0x4800000040010090 0xf8080007c00003f0

def z50 : W := mkw 0x0401aa1820749208 0x065faa7820f4920c

def z51 : W := mkw 0x1003706f00540220 0x181ff07fc0f40230

def z52 : W := mkw 0x6a800000440124d5 0xffe40000000fffff

def z53 : W := mkw 0xa604000804b8e34c 0xe644000000f8e3cc

def z54 : W := mkw 0xfa8b706f44df27f5 0xfffff07fc0ffffff

def z55 : W := mkw 0x0011330000eed800 0x0004338000fffc00

def z56 : W := mkw 0x0000008089000000 0x00080007ff000000

def z57 : W := mkw 0x1501203a2254022a 0x1fffa07a23f4023f

def z58 : W := mkw 0x6a800000440124d5 0xfffc4c043c0fffff

def z59 : W := mkw 0xa606cc5434a8e14c 0xe6404c043c08e1cc

def z60 : W := mkw 0x0023fff7bb000000 0x0003b3fbc3000000

def z61 : W := mkw 0x900b706f00de0320 0xe01fc07c00f803c0

def z62 : W := mkw 0x0002cc5430a8c000 0x001fcc7c3cf8e000

def z63 : W := mkw 0x0010000000eed800 0x0004000000fffc00

def z64 : W := mkw 0x8417ff5c30fedb08 0x0003807800f00000

def z65 : W := mkw 0xd808006f401103b0 0xf808007fc00003f0

def z66 : W := mkw 0x0001aa3222000000 0x1fffaa7a2304923f

def z67 : W := mkw 0x902bff7f32de0320 0x0003807800f00000

def z68 : W := mkw 0x228000808d002445 0x07e00f803f00fc0f

def z69 : W := mkw 0x0033ffc599eed800 0x0017ff85dcfffc00

def z70 : W := mkw 0xa62400ffbf10234c 0xe648007fff0003cc

def z71 : W := mkw 0xa202404c04982344 0xe65fcc7c3cf8e3cc

def z72 : W := mkw 0x1501aa322264902a 0x1fe02a022304903f

def z73 : W := mkw 0x00200090bb000000 0x000000003f000000

def z74 : W := mkw 0x0001aa0000649000 0x1fffaa0223f4923f

def z75 : W := mkw 0xa627ffffbf10234c 0xe65bffffff0003cc

def z76 : W := mkw 0x6a800080cd0124d5 0xf9a07787df0f7df3

def z77 : W := mkw 0xfa88000844df27f5 0xffe4000000ffffff

def z78 : W := mkw 0x0013ff0000461800 0x0013ff8000071c00

def z79 : W := mkw 0x1123fff7bb441022 0x19bbffffff041033

def z80 : W := mkw 0x26848c90bd20e44d 0x07e00f803f00fc0f

def z81 : W := mkw 0xee86ccdcfdb9e7dd 0xffffffffffffffff

def z82 : W := mkw 0x8417ff5c30fedb08 0x0017fff800fffc00

def z83 : W := mkw 0x0400881820308208 0x065f887820f0820c

def z84 : W := mkw 0xa617ff5c34fefb4c 0xe65ffffc3cffffcc

def z85 : W := mkw 0x0023fff7bbce0000 0x001fffffffff0000

def z86 : W := mkw 0x6f808a90ef21b4df 0xfffc7f87ff0fffff

def z87 : W := mkw 0xd81bff6f40ffdbb0 0xf81fffffc0fffff0

def z88 : W := mkw 0x150000080074922a 0x1fe4000000f4923f

def z89 : W := mkw 0x7f8000084475b6ff 0xffe4000000ffffff

def z90 : W := mkw 0xfa8b70efcddf27f5 0xffffffffffffffff

def z91 : W := mkw 0xa606445c3498634c 0xe648447c3c0863cc

def z92 : W := mkw 0x002375e799000000 0x001bf5ffdc000000

def z93 : W := mkw 0x6a800080cd0124d5 0xffe80007ff0003ff

def z94 : W := mkw 0xee97ffdcfdffffdd 0xffffffffffffffff

def z95 : W := mkw 0x150088182074922a 0x1fff887820f4923f

def z96 : W := mkw 0xd808000840df03b0 0xf804000000ff03f0

def z97 : W := mkw 0x0001aa0000649000 0x0017ff8000fffc00

def z98 : W := mkw 0x7f81aabaef75b6ff 0xffffffffffffffff

def z99 : W := mkw 0x48800080c9010491 0x19a03383c3071c33

def z100 : W := mkw 0x2627fff7bf20e04c 0x065bffffff00e00c

def z101 : W := mkw 0x002255f7bb000000 0x000855ffff000000

def z102 : W := mkw 0x9008000800de0320 0x0000000000f00000

def z103 : W := mkw 0x8002cc5c30980300 0xe01fcc7c3cf803c0

def z104 : W := mkw 0x5801202a405502b0 0xf81ff07fc0ff03f0

def z105 : W := mkw 0x002255c599000000 0x00187f87ff000000

def z106 : W := mkw 0xfa8800efcd1127f5 0xffe8007fff0003ff

def z107 : W := mkw 0xa607ee7e36b8e34c 0xe65fee7e3ff8e3cc

def z108 : W := mkw 0x0001222202000000 0x0000220203000000

def z109 : W := mkw 0x0003ff0000000000 0x0017ff80000ffc00

def z110 : W := mkw 0x6aa3fff7ff0124d5 0xffffffffff0fffff

def z111 : W := mkw 0x0013770000ce5800 0x00007780000f7c00

def z112 : W := mkw 0x2200000004002044 0xe65c4c043c08e3cc

def z113 : W := mkw 0x00308f90bb20d800 0x00000f803f00fc00

def z114 : W := mkw 0xd83bfffffbffdbb0 0xf81ffffffffffff0

def z115 : W := mkw 0x002133a38b000000 0x00003383c3000000

def z116 : W := mkw 0x6a800080cd0124d5 0xfffc2a07ff0493ff

def z117 : W := mkw 0x1501aa3a2274922a 0x001baa7a23f00000

def z118 : W := mkw 0x5809302b405702b0 0x181fb07bc0f70230

def z119 : W := mkw 0xdd0bfa7f62ff93ba 0xfffffa7fe3ff93ff

def z120 : W := mkw 0xea8a50c5cd8b25d5 0xfffc7f87ff0fffff

def z121 : W := mkw 0x003255c5998a4800 0x00005585dc0b6c00

def z122 : W := mkw 0x0001220000441000 0x0000220000041000

def z123 : W := mkw 0x1503ee3a22fcd22a 0x1fffee7a23fcf23f

def z124 : W := mkw 0xa206444414886144 0xe00044041c0861c0

def z125 : W := mkw 0x0033fff7bb461800 0x001bffffff071c00

def z126 : W := mkw 0xa206444c14986344 0xe01fc47c1cf863c0

def z127 : W := mkw 0xee84000844b9e7dd 0xffe4000000ffffff

def z128 : W := mkw 0x900b706f00de0320 0x0003807800f00000

def z129 : W := mkw 0x0001aa0000649000 0x0017aa0000f49000

def z130 : W := mkw 0x112133a38b441022 0x19a03383c3041033

def z131 : W := mkw 0x4800000040010090 0xf81c7007c00f03f0

def z132 : W := mkw 0x6aa000f7ff0124d5 0xfffc7fffff0fffff

def z133 : W := mkw 0x6a800080cd0124d5 0xe0147f85dc0ffdc0

def z134 : W := mkw 0x1511af3a2274da2a 0x1fffaffa23f4fe3f

def z135 : W := mkw 0x0023ff7732000000 0x0003807800000000

def z136 : W := mkw 0x0000000000000000 0x1ffc2a022304923f

def z137 : W := mkw 0xa606cc5c34b8e34c 0xe003c47c1cf861c0

def z138 : W := mkw 0xfa8b70efcddf27f5 0xf81ff5ffdcff6ff0

def z139 : W := mkw 0x1401a83a20748228 0x1e5fa87a20f4823c

def z140 : W := mkw 0x0013ff3222eed800 0x001ffffa23fffc00

def z141 : W := mkw 0x0000000000000000 0x00184c043c000000

def z142 : W := mkw 0x1111332202461822 0x19a0338203071c33

def z143 : W := mkw 0x0021aaf7bb000000 0x001baa7fff000000

def z144 : W := mkw 0x0010110000020800 0x0000118000030c00

def z145 : W := mkw 0x7f81aa3a6675b6ff 0xffffaa7a23ffffff

def z146 : W := mkw 0xa616dd5c34baeb4c 0xe65fddfc3cfbefcc

def z147 : W := mkw 0x0501aa102264900a 0x07f7aa0023f4900f

def z148 : W := mkw 0xa604881824b8e34c 0xe65f887820f8e3cc

def z149 : W := mkw 0x0013ff00008a4800 0x0013ff80000b6c00

def z150 : W := mkw 0x260088182430a24c 0xe65fcc7c3cf8e3cc

def z151 : W := mkw 0x0013ff0000eed800 0x0017aa0000f49000

def z152 : W := mkw 0x1501aa3a2274922a 0x065f887820f0820c

def z153 : W := mkw 0x8002404c00980300 0x0003807800f00000

def z154 : W := mkw 0x0023fff7bba8c000 0x001ffffffff8e000

def z155 : W := mkw 0x0011330000461800 0x0000338000071c00

def z156 : W := mkw 0x0000008089000000 0x00187f87ff000000

def z157 : W := mkw 0xc82a55c5d98b0190 0xe0005585dc0b01c0

def z158 : W := mkw 0x58193323404718b0 0x18003383c0071c30

def z159 : W := mkw 0x7f8000baef1126ff 0xffe8007fff0003ff

def z160 : W := mkw 0x6a900080cdeffcd5 0xfffc7f87ffffffff

def z161 : W := mkw 0xd81b756f40df4bb0 0xf81ff5ffc0ff6ff0

def z162 : W := mkw 0x2200000004002044 0xe64400000008e3cc

def z163 : W := mkw 0x48800080c9010491 0x00001181c0030c00

def z164 : W := mkw 0x0010030000001800 0x0000038000001c00

def z165 : W := mkw 0x8002404c00980300 0xe01fc07c00f803c0

def z166 : W := mkw 0xa206cc4414a8e144 0xe017cc041cf8e1c0

def z167 : W := mkw 0xa606cc5c34b8e34c 0xe64b807c3cf003cc

def z168 : W := mkw 0x0000000000000000 0x00147f80000ffc00

def z169 : W := mkw 0x0013ff5430eed800 0x001ffffc3cfffc00

def z170 : W := mkw 0x0013ff0000eed800 0x1fffff8223fffe3f

def z171 : W := mkw 0x6a800080cd0124d5 0xe0005585dc0b6dc0

def z172 : W := mkw 0x0013750000ce4800 0x0017f58000ff6c00

def z173 : W := mkw 0xfe0ffc7f74ffe3fc 0xfe5ffc7ffcffe3fc

def z174 : W := mkw 0xd80b706f40df03b0 0xf80b807fc0f003f0

def z175 : W := mkw 0xa606405c3498234c 0xe65fc07c3cf803cc

def z176 : W := mkw 0x2202cc5434002044 0xe65fcc7c3c08e3cc

def z177 : W := mkw 0x1501222a0274922a 0x1fe4220203f4923f

def z178 : W := mkw 0x580b7067404700b0 0x181bf07fc0070030

def z179 : W := mkw 0x0023fff7bb000000 0x0003d5fddc000000

def z180 : W := mkw 0x48800080c9010491 0x19b47f83c30ffc33

def z181 : W := mkw 0x950bfa7f22fe932a 0x0003807800f00000

def z182 : W := mkw 0x1501aa3a2274922a 0x07e38a7823f0900f

def z183 : W := mkw 0x0000000000ce0000 0x0004000000ff0000

def z184 : W := mkw 0x0033fff7bb20d800 0x001bffffff00fc00

def z185 : W := mkw 0x1521bbbbab74922a 0x1fffbbfbe3f4923f

def z186 : W := mkw 0xff87eefefffdf7ff 0xffffffffffffffff

def z187 : W := mkw 0xd80b706740cf01b0 0xf8007007c00f01f0

def z188 : W := mkw 0x1000002a00100220 0x1808007a00000230

def z189 : W := mkw 0x6a800080cd0124d5 0xffe85587ff0b6fff

def z190 : W := mkw 0xd818000840ffdbb0 0xf804000000fffff0

def z191 : W := mkw 0x58093023404700b0 0xf81c7007c00f03f0

def z192 : W := mkw 0x48a133a3cb010491 0x19a03383c3071c33

def z193 : W := mkw 0xd82bfffffbdf03b0 0xf81fffffffff03f0

def z194 : W := mkw 0x0003700000ce0000 0x0017ff8000fffc00

def z195 : W := mkw 0x0100020002001002 0x01a0020003001003

def z196 : W := mkw 0xdd0b707f62df03ba 0xfffff07fe3ff03ff

def z197 : W := mkw 0x0020007732000000 0x0000007800000000

def z198 : W := mkw 0x0501aa322220900a 0x07fbaa7a2300900f

def z199 : W := mkw 0xd82b70fffbdf03b0 0xf81ff07fffff03f0

def z200 : W := mkw 0x1511bb3a22769a2a 0x1fffbbfa23f79e3f

def z201 : W := mkw 0x0002cc0000a8c000 0x0017ff8000fffc00

def z202 : W := mkw 0x48a3fff7fb010491 0x19bbffffff071c33

def z203 : W := mkw 0x1501aa3a2274922a 0x0017aa7800f49000

def z204 : W := mkw 0x2200000004002044 0xe65c7f843c0fffcc

def z205 : W := mkw 0xa606cc5c34b8e34c 0x06438c783cf0e00c

def z206 : W := mkw 0x0001330000000000 0x0000338000000000

def z207 : W := mkw 0x0000008089000000 0x00003383c3000000

def z208 : W := mkw 0x0002ccd4b9000000 0x001bffffff000000

def z209 : W := mkw 0x588930a3c94704b1 0x19a03383c3071c33

def z210 : W := mkw 0x8023ffffbb980300 0xe01ffffffff803c0

def z211 : W := mkw 0x0003fc7730000000 0x001bfc7ffc000000

def z212 : W := mkw 0x00008f0000000000 0x00000f8000000000

def z213 : W := mkw 0x1500003a2210022a 0x1fe8007a2300023f

def z214 : W := mkw 0x1523ff7f3274922a 0x0003807800f00000

def z215 : W := mkw 0xa606cc5c34b8e34c 0xffffee7e3ffcf3ff

def z216 : W := mkw 0x8006444410884100 0x0000000000000000

def z217 : W := mkw 0x0003fa7722000000 0x001bfa7fe3000000

def z218 : W := mkw 0x6a800000440124d5 0xfff47f80000fffff

def z219 : W := mkw 0xb706cc7e36b8e36e 0xffffcc7e3ff8e3ff

def z220 : W := mkw 0x0023fff7bb000000 0x001fffffff0ffc00

def z221 : W := mkw 0x6aa255c5dd0124d5 0xfffc7f87ff0fffff

def z222 : W := mkw 0x6a93ff0044effcd5 0xfff7ff8000ffffff

def z223 : W := mkw 0x0000000000000000 0x065c08002000820c

def z224 : W := mkw 0x002133a38b000000 0x00187f87ff000000

def z225 : W := mkw 0xfe0c007f741123fc 0xfe48007ffc0003fc

def z226 : W := mkw 0x6a800000440124d5 0xffe00000000003ff

def z227 : W := mkw 0x0023fff7bb000000 0x000b807fff000000

def z228 : W := mkw 0x6a837080cdcf24d5 0xffffff87ffffffff

def z229 : W := mkw 0x6a800080cd0124d5 0xffe43383c30fffff

def z230 : W := mkw 0x0002404400000000 0x001bc07c00000000

def z231 : W := mkw 0x27808a90af20b44f 0x07e00f803f00fc0f

def z232 : W := mkw 0x6a800080cd0124d5 0xe65c5d85fc0befcc

def z233 : W := mkw 0x0000003222000000 0x0008007a23000000

def z234 : W := mkw 0xb727ffffbffcf36e 0xfffffffffffcf3ff

def z235 : W := mkw 0x0020058099000000 0x000005801c000000

def z236 : W := mkw 0x6a800000440124d5 0xfffc7007c00fffff

def z237 : W := mkw 0x1501aa3a2274922a 0x0003807800f00000

def z238 : W := mkw 0x7f93ffbaeffffeff 0xffffffffffffffff

def z239 : W := mkw 0x002133f7bb000000 0x000833ffff000000

def z240 : W := mkw 0x0022ccf7bb000000 0x001bcc7fff000000

def z241 : W := mkw 0x26248f90bf20e04c 0x06400f803f00e00c

def z242 : W := mkw 0xa606444c14b8e34c 0xe64444041cf8e3cc

def z243 : W := mkw 0x900b706f00de0320 0x001bf07fc0f00000

def z244 : W := mkw 0x0000000000000000 0x00144c000008e000

def z245 : W := mkw 0x0010000000eed800 0x00147f8000fffc00

def z246 : W := mkw 0xfe2fffffffffe3fc 0xfe5fffffffffe3fc

def z247 : W := mkw 0xfe0f706f44ffe3fc 0xfe5ff07fc0ffe3fc

def z248 : W := mkw 0x1100002202000022 0x19a0000203000033

def z249 : W := mkw 0x6a800080cd0124d5 0xfffc7007ff0f03ff

def z250 : W := mkw 0x0013ff8089eed800 0x001fff87fffffc00

def z251 : W := mkw 0x22908f808d20fc45 0x07e00f803f00fc0f

def z252 : W := mkw 0x1101222202441022 0x19a0220203041033

def z253 : W := mkw 0x2293ff808deefc45 0x07f7ff803ffffc0f

def z254 : W := mkw 0x0003ff0000000000 0x0013ff8000000000

def z255 : W := mkw 0x001000000020d800 0x000000000000fc00

def z256 : W := mkw 0xa637ffffbffefb4c 0xe65fffffffffffcc

def z257 : W := mkw 0x6a90000044effcd5 0xffe4000000ffffff

def z258 : W := mkw 0x0513ff1022eed80a 0x07f7ff8023fffc0f

def z259 : W := mkw 0x581bff2340efd8b0 0x1817ff83c0fffc30

def z260 : W := mkw 0x1501aa080074922a 0x1ff7aa0000f4923f

def z261 : W := mkw 0x8002cc4c00b8c300 0xe01fcc7c00f8e3c0

def z262 : W := mkw 0xd80b70efc9df03b0 0xf81fffffffff03f0

def z263 : W := mkw 0x0023ff90bb000000 0x0013ff803f000000

def z264 : W := mkw 0x0000000000000000 0x1fe400000004923f

def z265 : W := mkw 0x5d01aa3a627592ba 0xfffffa7fe3ff93ff

def z266 : W := mkw 0xee8400dcfd1127dd 0xffe8007fff0003ff

def z267 : W := mkw 0xd809206f405503b0 0xf81fa07fc0f403f0

def z268 : W := mkw 0xd80a404c40df03b0 0xf81fc07c00ff03f0

def z269 : W := mkw 0x1501aa3a2274922a 0x1feb807a23f0023f

def z270 : W := mkw 0xd80b706f40df03b0 0xe003d07dc0fb01c0

def z271 : W := mkw 0x05108f102220d80a 0x07e00f802300fc0f

def z272 : W := mkw 0x6a93ff80cdeffcd5 0xffffff87ffffffff

def z273 : W := mkw 0x228000808d002445 0x07f87f87ff00fc0f

def z274 : W := mkw 0x002000a38b000000 0x00000003c3000000

def z275 : W := mkw 0x0013ff0000eed800 0x0003800000f00000

def z276 : W := mkw 0x6a800000440124d5 0xfffc2a02230fffff

def z277 : W := mkw 0x6a800080cd0124d5 0xe7e05f85ff0bfdcf

def z278 : W := mkw 0xc802404c40990390 0xf81ff07fc0ff03f0

def z279 : W := mkw 0x0000008089000000 0x1ffc7f87ff04923f

def z280 : W := mkw 0x00208f90bb000000 0x00000f803f000000

def z281 : W := mkw 0x0001aa3222000000 0x001baa7a23000000

def z282 : W := mkw 0xd80bfc7f70df03b0 0xf81ffc7ffcff03f0

def z283 : W := mkw 0xd80b706f40df03b0 0x1803b07bc0f70030

def z284 : W := mkw 0x0023fff7bb649000 0x001ffffffff49000

def z285 : W := mkw 0x002000f7bb000000 0x00187fffff000000

def z286 : W := mkw 0x2606cc1034a8e04c 0x0657cc003cf8e00c

def z287 : W := mkw 0xa607ff5c34b8e34c 0xe65ffffc3cf8e3cc

def z288 : W := mkw 0xa627ff7f36b8e34c 0xe65fcc7c3cf8e3cc

def z289 : W := mkw 0x4800000040010090 0xfffc7a07e30f93ff

def z290 : W := mkw 0x0033fff7bb8a4800 0x001bffffff0b6c00

def z291 : W := mkw 0x6a800080cd0124d5 0xe0187f87ff0b6dc0

def z292 : W := mkw 0xea8644c4dd8965d5 0xe0005585dc0b6dc0

def z293 : W := mkw 0xc808004540010190 0xe0000005c00001c0

def z294 : W := mkw 0x002000c599000000 0x00000005dc000000

def z295 : W := mkw 0x00008c000020c000 0x00000c000000e000

def z296 : W := mkw 0xb705aa7e3674b36e 0xffffaa7e3ff493ff

def z297 : W := mkw 0xfe0c000844ffe3fc 0xfe44000000ffe3fc

def z298 : W := mkw 0xa626ccffbfb8e34c 0xe65fcc7ffff8e3cc

def z299 : W := mkw 0x0001aab2ab000000 0x001bffffff000000

def z300 : W := mkw 0x228000808d002445 0x000005801c006c00

def z301 : W := mkw 0x4808100140030090 0x00001001c0030000

def z302 : W := mkw 0xfa0f746f54df63f4 0xf81ff47fdcff63f0

def z303 : W := mkw 0x0003fc0000eec000 0x0017fc0000ffe000

def z304 : W := mkw 0xa627ffffbfb8e34c 0xe65ffffffff8e3cc

def z305 : W := mkw 0x598122a2cb4514b3 0x19a03383c3071c33

def z306 : W := mkw 0x0080008089000401 0x01a0038003001c03

def z307 : W := mkw 0x150000080010022a 0x1fe000000000023f

def z308 : W := mkw 0x6aa3fff7ff0124d5 0xfffbffffff0003ff

def z309 : W := mkw 0x1503fa7f2274922a 0x1ffffa7fe3f4923f

def z310 : W := mkw 0x9503ea7e22fc932a 0xffffea7e23fc93ff

def z311 : W := mkw 0xea0e5445548b61d4 0xe0005405dc0b61c0

def z312 : W := mkw 0x0001aa3222649000 0x001faa7a23f49000

def z313 : W := mkw 0x6a82cc80cda9e4d5 0xffffff87ffffffff

def z314 : W := mkw 0xd88b70efc9df07b1 0xf9bff3ffc3ff1ff3

def z315 : W := mkw 0xd80b700840df03b0 0xf817f00000ff03f0

def z316 : W := mkw 0xfa8800efcd1127f5 0xfffc7fffff0fffff

def z317 : W := mkw 0xfe0ecc7f74b9e3fc 0xfe5fcc7ffcf8e3fc

def z318 : W := mkw 0xb707ee7e36fcf36e 0xe65fcc7c3cf8e3cc

def z319 : W := mkw 0x8013ff4c00fedb00 0xe01ffffc00ffffc0

def z320 : W := mkw 0x8404005c30100308 0x0000007800000000

def z321 : W := mkw 0x4800000040010090 0xf8040000000f03f0

def z322 : W := mkw 0xd81b736f40df1bb0 0xf81ff3ffc0ff1ff0

def z323 : W := mkw 0xc80a504d409b0390 0xe01fd07dc0fb03c0

def z324 : W := mkw 0x0021afb2bb000000 0x001baffa3f000000

def z325 : W := mkw 0x0023fff7bb000000 0x1fffffffff04923f

def z326 : W := mkw 0x0013ff0000eed800 0x0017cc0000f8e000

def z327 : W := mkw 0x8000000800980300 0xe004000000f803c0

def z328 : W := mkw 0x0402cc1820b8c208 0x065fcc7820f8e20c

def z329 : W := mkw 0x0023fff7bb000000 0x00038ff83f000000

def z330 : W := mkw 0xee06cc5c74b9e3dc 0xfe5ffc7ffcffe3fc

def z331 : W := mkw 0xa604885c3430a34c 0xe65f887c3cf083cc

def z332 : W := mkw 0x2223fff7bf002044 0xe65fffffff08e3cc

def z333 : W := mkw 0x0023ff7732000000 0x001bf07fc0000000

def z334 : W := mkw 0xdd08007f621103ba 0xffe8007fe30003ff

def z335 : W := mkw 0xc80b704540cf0190 0xe017f005c0ff01c0

def z336 : W := mkw 0xd81b706f40ffdbb0 0xf81ff07fc0fffff0

def z337 : W := mkw 0x1113ff2202eed822 0x19b7ff8203fffc33

def z338 : W := mkw 0x1001aa2a00749220 0x181faa7a00f49230

def z339 : W := mkw 0x6aa000f7ff0124d5 0xffe8007fff0003ff

def z340 : W := mkw 0xa2165544148a6944 0xe00055841c0b6dc0

def z341 : W := mkw 0x1000000800540220 0x1804000000f40230

def z342 : W := mkw 0xa626cfdcbfb8e34c 0xe65fcffc3ff8e3cc

def z343 : W := mkw 0xa227fff7bf886144 0xe01bffffff0861c0

def z344 : W := mkw 0xea8a50c5cd8b25d5 0xe0005585dc0b6dc0

def z345 : W := mkw 0x901bff6f00fedb20 0x0017fff800fffc00

def z346 : W := mkw 0xa606cc0804b8e34c 0xe657cc0000f8e3cc

def z347 : W := mkw 0x0000000000000000 0x00187007c0000000

def z348 : W := mkw 0x1521afbabb74922a 0x1fffaffa3ff4923f

def z349 : W := mkw 0x1001202a00540220 0x1fffaa7a23f4923f

def z350 : W := mkw 0xb60ffc7f34fee36c 0xe65fcc7c3cf8e3cc

def z351 : W := mkw 0x0000005430000000 0x0008007c3c000000

def z352 : W := mkw 0x0000000000000000 0x0000338000071c00

def z353 : W := mkw 0x0023ff7732000000 0x0013fff800000000

def z354 : W := mkw 0x22a08f90bf002445 0x07e00f803f00fc0f

def z355 : W := mkw 0x6a000000440120d4 0xfe5c7c07fc0fe3fc

def z356 : W := mkw 0x0033ff7732eed800 0x0017fff800fffc00

def z357 : W := mkw 0x0003700000000000 0x0013f00000000000

def z358 : W := mkw 0x8003706f00980300 0xe01ff07fc0f803c0

def z359 : W := mkw 0x0002cc0000000000 0x0013cc0000000000

def z360 : W := mkw 0x0002504500000000 0x00005005c0000000

def z361 : W := mkw 0x6aa255c5dd0124d5 0xe0005585dc0b6dc0

def z362 : W := mkw 0xa6048c1834b8e34c 0xe6440c003cf8e3cc

def z363 : W := mkw 0x0013ff0000eed800 0x0003d58000fb6c00

def z364 : W := mkw 0x0013730000ce1800 0x0017f38000ff1c00

def z365 : W := mkw 0x48800080c9010491 0x19a00003c3000033

def z366 : W := mkw 0x1521aaffbb74922a 0x1fffaa7ffff4923f

def z367 : W := mkw 0x0000000800100200 0x001f807800f00200

def z368 : W := mkw 0xfa9bffefcdfffff5 0xffffffffffffffff

def z369 : W := mkw 0x6a913380cd473cd5 0xfffc7f87ff0fffff

def z370 : W := mkw 0x1500883a2230822a 0x1fff887a23f0823f

def z371 : W := mkw 0xd80bfa7f62df03b0 0xf81ffa7fe3ff03f0

def z372 : W := mkw 0x3701aa3a2674b26e 0xffffee7e3ffcf3ff

def z373 : W := mkw 0xee86ccdcfdb9e7dd 0xffffcc7ffff8e3ff

def z374 : W := mkw 0x260400103400204c 0x064000003c00000c

def z375 : W := mkw 0xdd2bfffffbff93ba 0xffffffffffff93ff

def z376 : W := mkw 0x1101aa2202649022 0x19b7aa0203f49033

def z377 : W := mkw 0xa614000804fefb4c 0xe644000000ffffcc

def z378 : W := mkw 0xee86cc5c74b9e7dd 0xffffcc7c3cffffff

def z379 : W := mkw 0x002373e78b000000 0x001bf3ffc3000000

def z380 : W := mkw 0x2200000004002044 0xe64800043c0003cc

def z381 : W := mkw 0xb704000804fcf36e 0xffe4000000fcf3ff

def z382 : W := mkw 0xa606cc5c3410234c 0xe65bcc7c3c0003cc

def z383 : W := mkw 0x1501223a2254122a 0x1fe8227a2304123f

def z384 : W := mkw 0x1001aa3a22540220 0x181faa7a23f40230

def z385 : W := mkw 0x1003702a00de0220 0x181ff07a00ff0230

def z386 : W := mkw 0xc81bff4540efd990 0xe017ff85c0fffdc0

def z387 : W := mkw 0x000370e789000000 0x001bffffff000000

def z388 : W := mkw 0x8406cc5c30b8c308 0x001bcc7c3cf00000

def z389 : W := mkw 0x0022ddd5b9000000 0x001bddfdfc000000

def z390 : W := mkw 0x7a8120aacd5526f5 0xffffffffffffffff

def z391 : W := mkw 0x0000000000000000 0xe01c4004000803c0

def z392 : W := mkw 0x48800080c9010491 0x19b87f87ff071c33

def z393 : W := mkw 0x0003ff0000ce0000 0x0017ff8000ff0000

def z394 : W := mkw 0x0400881020208008 0x064008002000800c

def z395 : W := mkw 0x2200000004002044 0xfffc6e063f0cf3ff

def z396 : W := mkw 0x0523fff7bb20900a 0x07fbffffff00900f

def z397 : W := mkw 0x003133a38b461800 0x00003383c3071c00

def z398 : W := mkw 0xa606cc5c34b8e34c 0xe65ffffc3cffffcc

def z399 : W := mkw 0x0023ffa38b000000 0x0013ff83c3000000

def z400 : W := mkw 0x0022cfd4bb000000 0x001bcffc3f000000

def z401 : W := mkw 0xa607fc5c34fee34c 0xe65ffc7c3cffe3cc

def z402 : W := mkw 0xdc0bf87f60ff83b8 0xfe5ff87fe0ff83fc

def z403 : W := mkw 0x1501aa3a2274922a 0x1ffffffa23fffe3f

def z404 : W := mkw 0xd808006f401103b0 0xf81c707fc00f03f0

def z405 : W := mkw 0x0012dd0000aac800 0x0017dd8000fbec00

def z406 : W := mkw 0xa217ff4414eef944 0xe017ff841cfffdc0

def z407 : W := mkw 0x0021bbb3ab000000 0x001bbbfbe3000000

def z408 : W := mkw 0x0013ff0000eed800 0x0003b38000f71c00

def z409 : W := mkw 0xd80bfc6f40ffc3b0 0xf81ffc7fc0ffe3f0

def z410 : W := mkw 0x6a800080cd0124d5 0xfffc4c07ff08e3ff

def z411 : W := mkw 0xa604000804b8e34c 0xe65c4c043cf8e3cc

def z412 : W := mkw 0xd81bff0840ffdbb0 0xf817ff8000fffff0

def z413 : W := mkw 0x0413ff1820feda08 0x065ffff820fffe0c

def z414 : W := mkw 0x4813ff0040efd890 0xf81fff87c0fffff0

def z415 : W := mkw 0x0033ff7732eed800 0x0003807800f00000

def z416 : W := mkw 0xd80b706f401103b0 0xf81bf07fc00003f0

def z417 : W := mkw 0x7f8000baef1126ff 0xfffc7fffff0fffff

def z418 : W := mkw 0x1500003a2274922a 0x1fec007a23f4923f

def z419 : W := mkw 0x0023ffc599000000 0x0013ff85dc000000

def z420 : W := mkw 0xd80b706f40df03b0 0xfffffa7fe3ff93ff

def z421 : W := mkw 0xdd08000840ff93ba 0xffe4000000ff93ff

def z422 : W := mkw 0xd81bff6f40ffdbb0 0xf81ff07fc0ff03f0

def z423 : W := mkw 0xa204000004886144 0xe0000000000861c0

def z424 : W := mkw 0x0013700000eed800 0x0017f00000fffc00

def z425 : W := mkw 0x1001202a00540220 0x0003807800f00000

def z426 : W := mkw 0xd80a406f409903b0 0xf81fc07fc0f803f0

def z427 : W := mkw 0x0402cc5c30308208 0x065fcc7c3cf0820c

def z428 : W := mkw 0x0012cc0000eed800 0x0017cc0000fffc00

def z429 : W := mkw 0xc82bfff7fb8b0190 0xe01bffffff0b01c0

def z430 : W := mkw 0x0003ff3222000000 0x001bfffa23000000

def z431 : W := mkw 0x6e848c90fd21e4dd 0xfffc7f87ff0fffff

def z432 : W := mkw 0x9507ee7e32fcd32a 0x1fffaa7a23f4923f

def z433 : W := mkw 0x0000006700000000 0x0008007fc0000000

def z434 : W := mkw 0x58080000404700b0 0x1800000000070030

def z435 : W := mkw 0x6a908f80cd21fcd5 0xfffc7f87ff0fffff

def z436 : W := mkw 0x00208f1032000000 0x0000000000000000

def z437 : W := mkw 0x4823fff7fb010090 0xf81fffffff0f03f0

def z438 : W := mkw 0x15008a3a2230922a 0x1fe80a7a2300923f

def z439 : W := mkw 0x580b702340cf00b0 0x1817f003c0ff0030

def z440 : W := mkw 0x228000808d002445 0x07f47f803f0ffc0f

def z441 : W := mkw 0x0013ff000020d800 0x0013ff800000fc00

def z442 : W := mkw 0x1101222202441022 0x1ffc2a022304923f

def z443 : W := mkw 0x0400000800308208 0x0644000000f0820c

def z444 : W := mkw 0x00008c1030000000 0x00000c003c000000

def z445 : W := mkw 0x0033ff90bbeed800 0x0017ff803ffffc00

def z446 : W := mkw 0x00008a0000209000 0x00000a0000009000

def z447 : W := mkw 0x2202cc0004a8e044 0xe65fcc043cf8e3cc

def z448 : W := mkw 0x00008a1022000000 0x00000a0023000000

def z449 : W := mkw 0x4800000040010090 0xe0005005c00b01c0

def z450 : W := mkw 0x228000808d002445 0xe7fc4f843f08ffcf

def z451 : W := mkw 0xd809306f405703b0 0xf808307fc00703f0

def z452 : W := mkw 0x1501aa3a2274922a 0x181fa07a00f40230

def z453 : W := mkw 0x3705ae3a3674f26e 0x1fffae7a3ff4f23f

def z454 : W := mkw 0x6a800080cd0124d5 0xffec0007ff0fffff

def z455 : W := mkw 0xd80b706f40df03b0 0xf81fffffc0fffff0

def z456 : W := mkw 0x05208f90bb20900a 0x07e00f803f00900f

def z457 : W := mkw 0x002370f7bb000000 0x001bf07fff000000

def z458 : W := mkw 0x0003ee7632000000 0x001bee7e3f000000

def z459 : W := mkw 0x9003606e00dc0320 0xf81fe07e00fc03f0

def z460 : W := mkw 0x1503fa3a22fe922a 0x1ffffa7a23ff923f

def z461 : W := mkw 0x0000000000649000 0x0004000000f49000

def z462 : W := mkw 0x0000000000000000 0x00005580000b6c00

def z463 : W := mkw 0x0011330000461800 0x0000000000000000

def z464 : W := mkw 0xd808006f40df03b0 0xf80c007fc0ff03f0

def z465 : W := mkw 0x7f81aabaef75b6ff 0xffffaa7ffff493ff

def z466 : W := mkw 0x0003ee0000ecd000 0x0017ee0000fcf000

def z467 : W := mkw 0xa607ee5c34fcf34c 0xe65fee7c3cfcf3cc

def z468 : W := mkw 0x1501aa3a2274922a 0x19a3a27a03f41033

def z469 : W := mkw 0xa606cc5c34b8e34c 0xe647807800f8e3cc

def z470 : W := mkw 0x8402c85c20b88308 0xe65fc87c20f883cc

def z471 : W := mkw 0x6a83ff80cd0124d5 0xffffff87ff0fffff

def z472 : W := mkw 0x940ffc7f30fec328 0x0003807800f00000

def z473 : W := mkw 0x2617ff1034eef84c 0x0657ff803cfffc0c

def z474 : W := mkw 0x05008a182230920a 0x07ff8a7823f0920f

def z475 : W := mkw 0xdd09aa3a62ff93ba 0xffffaa7a23ff93ff

def z476 : W := mkw 0x0010000000eed800 0x0000000000f00000

def z477 : W := mkw 0x0000880000208000 0x0017880000f08000

def z478 : W := mkw 0x901bff6f00fedb20 0x0003807800f00000

def z479 : W := mkw 0x1501aa3a2210022a 0x1ffbaa7a2300023f

def z480 : W := mkw 0x9008006f00100320 0x0000007800000000

def z481 : W := mkw 0x0020118189000000 0x00001181c0000000

def z482 : W := mkw 0x1501aa3a2274922a 0x1fe7807800f4923f

def z483 : W := mkw 0x220000808d002044 0xe65c7f87ff08e3cc

def z484 : W := mkw 0x6a800080cd0124d5 0xe0000005dc0001c0

def z485 : W := mkw 0x002003808b000000 0x0000038003000000

def z486 : W := mkw 0x800a5045008a0100 0x0000000000000000

def z487 : W := mkw 0x0401aa3a22308208 0x065faa7a23f0820c

def z488 : W := mkw 0x0023ff7732000000 0x001bcc7c3c000000

def z489 : W := mkw 0x0000000000a8c000 0x0004000000f8e000

def z490 : W := mkw 0x0000000000000000 0x0000000000000000

def z491 : W := mkw 0x0012550000eed800 0x0004558000fffc00

def z492 : W := mkw 0x1511aa3a22feda2a 0x1fffaa7a23fffe3f

def z493 : W := mkw 0xd809302b40df03b0 0xf8043003c0ff03f0

def z494 : W := mkw 0x6aa3fff7ff0124d5 0xe01bffffff0b6dc0

def z495 : W := mkw 0x1100000000441022 0x19a0000000041033

def z496 : W := mkw 0xd90b726f42df13b2 0xf9bff27fc3ff13f3

def z497 : W := mkw 0x0002cc5430000000 0x0003807800000000

def z498 : W := mkw 0x48800080c9010491 0xf9bc7387c30f1ff3

def z499 : W := mkw 0x00025000008a0000 0x00005000000b0000

def z500 : W := mkw 0x0000000000000000 0x00182a0223000000

def z501 : W := mkw 0xee0edc5d74bbe3dc 0xe65fdc7dfcfbe3cc

def z502 : W := mkw 0x0400881820308208 0x1fffaa7a23f4923f

def z503 : W := mkw 0xdd09aa7f627593ba 0xffffaa7fe3f493ff

def z504 : W := mkw 0x6a82ccd4fd0124d5 0xffffffffff0fffff

def z505 : W := mkw 0x0003ff5430000000 0x001bfffc3c000000

def z506 : W := mkw 0x1001202200440020 0x1800200200040030

def z507 : W := mkw 0xea8644c4dd8965d5 0xfffc7f87ff0fffff

def z508 : W := mkw 0xd80bfa6f40ff93b0 0xf81ffa7fc0ff93f0

def z509 : W := mkw 0x0002440000884000 0x0000440000086000

def z510 : W := mkw 0xa606404c04b8e34c 0xe65fc07c00f8e3cc

def z511 : W := mkw 0x2200000004002044 0x06400c003c00e00c

def z512 : W := mkw 0x0022554510000000 0x0000000000000000

def z513 : W := mkw 0x0001aa3222000000 0x0003807800000000

def z514 : W := mkw 0x0033ffa38beed800 0x0017ff83c3fffc00

def z515 : W := mkw 0x1101222202441022 0x0000000000000000

def z516 : W := mkw 0x6a800080cd0124d5 0xfff87f87ff0003ff

def z517 : W := mkw 0xdd0b706f40ff93ba 0xfffff07fc0ff93ff

def z518 : W := mkw 0xa60400080410234c 0xe6400000000003cc

def z519 : W := mkw 0x0001aa0000649000 0x0003800000f00000

def z520 : W := mkw 0x6a925580cd8b6cd5 0xfffc7f87ff0fffff

def z521 : W := mkw 0xfe8ffcfffdffe7fd 0xffffffffffffffff

def z522 : W := mkw 0xd82b75efd9df03b0 0xf81ff5ffdcff03f0

def z523 : W := mkw 0xa617ff0804fefb4c 0xe657ff8000ffffcc

def z524 : W := mkw 0x7a8930a3cd4724f5 0xfffc7f87ff0fffff

def z525 : W := mkw 0x0001302300000000 0x00003003c0000000

def z526 : W := mkw 0x6e808898ed31a6dd 0xffffffffffffffff

def z527 : W := mkw 0x00108f000020d800 0x0000000000000000

def z528 : W := mkw 0xfe1fff7f74fffbfc 0xfe5ffffffcfffffc

def z529 : W := mkw 0x4880000040010491 0x19a0000000071c33

def z530 : W := mkw 0xfa880088cddf27f5 0xfffc7f87ffffffff

def z531 : W := mkw 0x0000000000000000 0x19a0220203041033

def z532 : W := mkw 0xa206444414886144 0xe65c4c043c08e3cc

def z533 : W := mkw 0x0011bf000066d800 0x00003f800007fc00

def z534 : W := mkw 0x0002550000000000 0x0000558000000000

def z535 : W := mkw 0xd80bff6f40df03b0 0xf81fffffc0ff03f0

def z536 : W := mkw 0xa607fc7f34b8e34c 0xe65ffc7ffcf8e3cc

def z537 : W := mkw 0x9507ee7e32fcd32a 0x0003807800f00000

def z538 : W := mkw 0xfa0b706f44df23f4 0xfe5ffc7ffcffe3fc

def z539 : W := mkw 0x7fa3ffffff75b6ff 0xffffffffffffffff

def z540 : W := mkw 0x0011aa0000eed800 0x0017aa0000fffc00

def z541 : W := mkw 0x582933a3cb4700b0 0x18003383c3070030

def z542 : W := mkw 0x0003706700ce0000 0x001ff07fc0ff0000

def z543 : W := mkw 0x0000000000000000 0x00000f800000fc00

def z544 : W := mkw 0x48913380c9471c91 0x19a03383c3071c33

def z545 : W := mkw 0xb704007e3610236e 0xffe8007e3f0003ff

def z546 : W := mkw 0xa204004414002144 0xe00000041c0001c0

def z547 : W := mkw 0xfa8b70efcddf27f5 0xfffff07fffff03ff

def z548 : W := mkw 0x1101aa3222441022 0x19bbaa7a23041033

def z549 : W := mkw 0x2200000004002044 0xe00044041c0861c0

def z550 : W := mkw 0x6a8370e7cd0124d5 0xffffffffff0fffff

def z551 : W := mkw 0x6a93ff80cdeffcd5 0xe017ff85dcfffdc0

def z552 : W := mkw 0x6a800080cd0124d5 0xf81c7587dc0f6ff0

def z553 : W := mkw 0x582bfff7fb4700b0 0x181bffffff070030

def z554 : W := mkw 0x0000008089000000 0x001c7f87ff0ffc00

def z555 : W := mkw 0xc8080000408b0190 0xe0000000000b01c0

def z556 : W := mkw 0x15008a182274922a 0x1fe40a0023f4923f

def z557 : W := mkw 0x1501202a0074922a 0x1fffa07a00f4923f

def z558 : W := mkw 0xee840088cdb9e7dd 0xfffc7f87ffffffff

def z559 : W := mkw 0x1513ff3a22feda2a 0x1fffaa7a23f4923f

def z560 : W := mkw 0x7f800088cd75b6ff 0xfffc7f87ffffffff

def z561 : W := mkw 0x1501aabaab74922a 0x1ffffffffff4923f

def z562 : W := mkw 0xc80a5045408b0190 0xf81c7007c00f03f0

def z563 : W := mkw 0x0010000000461800 0x0000000000071c00

def z564 : W := mkw 0x00108f000020d800 0x00147f80000ffc00

def z565 : W := mkw 0x1513ff3a22feda2a 0x0017fff800fffc00

def z566 : W := mkw 0xff0ffe7f76fff3fe 0xfffffe7ffffff3ff

def z567 : W := mkw 0x6a800080cd0124d5 0xffe83387ff071fff

def z568 : W := mkw 0x6a81aab2ef0124d5 0xffffffffff0fffff

def z569 : W := mkw 0x0002444410000000 0x000044041c000000

def z570 : W := mkw 0x27048e103620f04e 0x07e00e003f00f00f

def z571 : W := mkw 0xa686ccdcbdb8e74d 0xe7ffcffc3ff8ffcf

def z572 : W := mkw 0x05008a102220900a 0x1ffc2a022304923f

def z573 : W := mkw 0x6a81aa80cd65b4d5 0xffffff87ffffffff

def z574 : W := mkw 0xd80a506f409b03b0 0xf808507fc00b03f0

def z575 : W := mkw 0x002377e79b000000 0x00007787df000000

def z576 : W := mkw 0x2280000004002445 0x07e000000000fc0f

def z577 : W := mkw 0x1023ffffbb540220 0x181ffffffff40230

def z578 : W := mkw 0x0000000000000000 0x00040000000ffc00

def z579 : W := mkw 0xa617ff5c34fefb4c 0xe65fcc7c3cf8e3cc

def z580 : W := mkw 0x0001202200000000 0x001ba07a00000000

def z581 : W := mkw 0xfaabffffffdf27f5 0xffffffffffffffff

def z582 : W := mkw 0x1503ee7e3274922a 0x1fffee7e3ff4923f

def z583 : W := mkw 0xa706ce5c36b8f34e 0xe7ffce7c3ff8f3cf

def z584 : W := mkw 0x0011af000064d800 0x0017af8000f4fc00

def z585 : W := mkw 0x4800000040010090 0xf81c7f87c00ffff0

def z586 : W := mkw 0xa606ccdcbdb8e34c 0xe65ffffffff8e3cc

def z587 : W := mkw 0xdc0ffc7f70ffc3b8 0xf81ff07fc0ff03f0

def z588 : W := mkw 0x0003ff8089000000 0x001bff87ff000000

def z589 : W := mkw 0x0021332302000000 0x0000000000000000

def z590 : W := mkw 0x0000000000000000 0x07e00a002300900f

def z591 : W := mkw 0x0023ff7732000000 0x001baa7a23000000

def z592 : W := mkw 0x1013ff2a00feda20 0x181ffffa00fffe30

def z593 : W := mkw 0x1510000800feda2a 0x1fe4000000fffe3f

def z594 : W := mkw 0x228000808d002445 0x07e000003f00000f

def z595 : W := mkw 0x0002cc0000a8c000 0x0003800000f00000

def z596 : W := mkw 0x6a800000440124d5 0xe0000000000b6dc0

def z597 : W := mkw 0x58080023400100b0 0x18000003c0000030

def z598 : W := mkw 0x8406cc5c30b8c308 0x065f887820f0820c

def z599 : W := mkw 0x0000000000000000 0x00107f8000000000

def z600 : W := mkw 0x0003706700000000 0x0003807800000000

def z601 : W := mkw 0x48000080c9010090 0xf81c7f87ff0f03f0

def z602 : W := mkw 0x0012df0000aad800 0x00005f80000bfc00

def z603 : W := mkw 0x0021bfb3bb000000 0x00003f83ff000000

def z604 : W := mkw 0x00100000008a4800 0x00000000000b6c00

def z605 : W := mkw 0x0001300000460000 0x0000300000070000

def z606 : W := mkw 0x7b8122a2cf4534f7 0xfffc7f87ff0fffff

def z607 : W := mkw 0x1101222a02541222 0x19bfa27a03f41233

def z608 : W := mkw 0xeea7ffffffb9e7dd 0xffffffffffffffff

def z609 : W := mkw 0x0003fa0000ee9000 0x0017fa0000ff9000

def z610 : W := mkw 0x8427ffffbbb8c308 0x001bfffffff00000

def z611 : W := mkw 0x5d81aabaeb7596bb 0x1fffbbfbe3f79e3f

def z612 : W := mkw 0x0003ff6700000000 0x001bffffc0000000

def z613 : W := mkw 0xb705aa3a26fcf36e 0xffffaa7a23fcf3ff

def z614 : W := mkw 0x26048c183430e24c 0x065f8c783cf0e20c

def z615 : W := mkw 0x0013ff0000eed800 0x00038f8000f0fc00

def z616 : W := mkw 0x152000ffbb10022a 0x1fe8007fff00023f

def z617 : W := mkw 0x050000000020900a 0x07e000000000900f

def z618 : W := mkw 0xff8bfaffefffb7ff 0xffffffffffffffff

def z619 : W := mkw 0x6ab3fff7ffeffcd5 0xffffffffffffffff

def z620 : W := mkw 0xa604005c3410234c 0xe65c4c7c3c08e3cc

def z621 : W := mkw 0x8000004c00100300 0xe008007c000003c0

def z622 : W := mkw 0xd82800fffb1103b0 0xf808007fff0003f0

def z623 : W := mkw 0xfe0ecc5c74ffe3fc 0xfe5fcc7c3cffe3fc

def z624 : W := mkw 0x4893ff80c9efdc91 0x19b7ff83c3fffc33

def z625 : W := mkw 0x0400001820100208 0x064800782000020c

def z626 : W := mkw 0x1500003a2210022a 0x1ffc2a7a2304923f

def z627 : W := mkw 0xd82b73efcbdf03b0 0xf81ff3ffc3ff03f0

def z628 : W := mkw 0xa22655c59d886144 0xe0005585dc0861c0

def z629 : W := mkw 0x0000000000000000 0x181c200200040230

def z630 : W := mkw 0xdd1bff7f62ffdbba 0xffffffffe3ffffff

def z631 : W := mkw 0x48800080c9010491 0x1ffc3b83e3079e3f

def z632 : W := mkw 0xea8240cccd9927d5 0xffffffffffffffff

def z633 : W := mkw 0x0001aa0000000000 0x0013aa0000000000

def z634 : W := mkw 0x26148f103420f84c 0x06400f803c00fc0c

def z635 : W := mkw 0xd80b706f40df03b0 0xf807807800ff03f0

def z636 : W := mkw 0x2204040014006044 0x000004001c006000

def z637 : W := mkw 0x8406cc5c30b8c308 0xe01fc07c00f803c0

def z638 : W := mkw 0x0000000000000000 0x00147000000f0000

def z639 : W := mkw 0x150000080074922a 0x1ffc2a0223f4923f

def z640 : W := mkw 0x260400000420e04c 0x064000000000e00c

def z641 : W := mkw 0xc81a5545408b4990 0xe0005585c00b6dc0

def z642 : W := mkw 0xb717ff7e36fefb6e 0xfffffffe3fffffff

def z643 : W := mkw 0x0010050000004800 0x0000058000006c00

def z644 : W := mkw 0xd82bff7f72df03b0 0xf81ff07fc0ff03f0

def z645 : W := mkw 0x2213ff0004eef844 0xe65fff843cffffcc

def z646 : W := mkw 0x0003ff0000649000 0x0017ff8000f49000

def z647 : W := mkw 0x2606cc543420e04c 0x065bcc7c3c00e00c

def z648 : W := mkw 0x0012cf0000a8d800 0x0017cf8000f8fc00

def z649 : W := mkw 0x0001200000440000 0x0017a00000f40000

def z650 : W := mkw 0x6a925580cd8b6cd5 0xe0005585dc0b6dc0

def z651 : W := mkw 0x0013ff0000eed800 0x0007800000fffc00

def z652 : W := mkw 0x0000000000000000 0x1fe800022300023f

def z653 : W := mkw 0x0011330000461800 0x00147f80000ffc00

def z654 : W := mkw 0xd82bfffffb1103b0 0xf81bffffff0003f0

def z655 : W := mkw 0xd80a504d40df03b0 0xf8045005c0ff03f0

def z656 : W := mkw 0x26048c103420e04c 0xe65c4c043c08e3cc

def z657 : W := mkw 0xa6048c5c3430e34c 0xe6480c7c3c00e3cc

def z658 : W := mkw 0x0000008089000000 0x00005585dc000000

def z659 : W := mkw 0x05008a102220900a 0x0000000000000000

def z660 : W := mkw 0x0013ff0000eed800 0x0013ff8000f00000

def z661 : W := mkw 0x050000102200000a 0x07e000002300000f

def z662 : W := mkw 0x1523ff7f3274922a 0x1fffaa7a23f4923f

def z663 : W := mkw 0xdd0bfa7f62ff93ba 0xf81ff07fc0ff03f0

def z664 : W := mkw 0x0003700000ce0000 0x0003800000f00000

def z665 : W := mkw 0x8003704c00de0300 0xe01ff07c00ff03c0

def z666 : W := mkw 0x0000008089000000 0x00000f803f000000

def z667 : W := mkw 0x8427ff7f32b8c308 0x0003807800f00000

def z668 : W := mkw 0x00208f90bb000000 0x00187f87ff000000

def z669 : W := mkw 0x0003ff0000a8c000 0x0017ff8000f8e000

def z670 : W := mkw 0x902bffffbbde0320 0x001bfffffff00000

def z671 : W := mkw 0x4803706740010090 0xf81ff07fc00f03f0

def z672 : W := mkw 0x1523ffffbb74922a 0x001bfffffff00000

def z673 : W := mkw 0x0000000000000000 0x1ffc7f82230ffe3f

def z674 : W := mkw 0x0022dfd5bb000000 0x00005f85ff000000

def z675 : W := mkw 0x00125500008a4800 0x0000000000000000

def z676 : W := mkw 0x900b706f00de0320 0x181fa07a00f40230

def z677 : W := mkw 0x950bfa7f22fe932a 0x1fffaa7a23f4923f

def z678 : W := mkw 0xa616cc5c34fefb4c 0xe65fcc7c3cffffcc

def z679 : W := mkw 0x1513ff0800feda2a 0x1ff7ff8000fffe3f

def z680 : W := mkw 0xb706cc5c34fcf36e 0xffffcc7c3cfcf3ff

def z681 : W := mkw 0xc80b7067408b0190 0xe01bf07fc00b01c0

def z682 : W := mkw 0x04048c103020c008 0x0000000000000000

def z683 : W := mkw 0x8404000800b8c308 0x0000000000f00000

def z684 : W := mkw 0x0423ffffbb308208 0x065ffffffff0820c

def z685 : W := mkw 0x6aa08f90ff0124d5 0xfffc7f87ff0fffff

def z686 : W := mkw 0xa604005c34b8e34c 0xe64c007c3cf8e3cc

def z687 : W := mkw 0x0013ff0000eed800 0x0017f00000ff0000

def z688 : W := mkw 0x900b706f00de0320 0x0017f07800ff0000

def z689 : W := mkw 0x6a800080cd0124d5 0xffe45585dc0fffff

def z690 : W := mkw 0x8002404400880100 0xe0004004000801c0

def z691 : W := mkw 0x1009302300460020 0x0000000000000000

def z692 : W := mkw 0x1500003a2210022a 0x0000007800000000

def z693 : W := mkw 0xee8400dcfd1127dd 0xfffc7fffff0fffff

def z694 : W := mkw 0x0002400000880000 0x0017c00000f80000

def z695 : W := mkw 0x0000881020000000 0x001b887820000000

def z696 : W := mkw 0xa626ddddbdb8e34c 0xe65fddfdfcf8e3cc

def z697 : W := mkw 0x22a3fff7bf002445 0x07fbffffff00fc0f

def z698 : W := mkw 0x8406cc5c30b8c308 0x0017cc7800f8e000

def z699 : W := mkw 0xa206cc5434886144 0xe01bcc7c3c0861c0

def z700 : W := mkw 0x0400881820308208 0x0003807800f00000

def z701 : W := mkw 0x1523ffffbb10022a 0x1ffbffffff00023f

def z702 : W := mkw 0x3781aabaaf74b66f 0x1fffaffa3ff4fe3f

def z703 : W := mkw 0x5d09ba3b627792ba 0x1fffba7be3f7923f

def z704 : W := mkw 0xd809202a40df03b0 0xf81fa07a00ff03f0

def z705 : W := mkw 0x00125500008a4800 0x00147f80000ffc00

def z706 : W := mkw 0xb607ec7e34fce36c 0xfe5fec7e3cfce3fc

def z707 : W := mkw 0x0023fff7bb000000 0x181fffffff040230

def z708 : W := mkw 0x8002405c30980300 0xe01fc07c3cf803c0

def z709 : W := mkw 0x0033fff7bbce5800 0x001bffffff0f7c00

def z710 : W := mkw 0x7e0dbc337467e0fc 0x1e403c03fc07e03c

def z711 : W := mkw 0x582930a3cb4700b0 0x18003003c3070030

def z712 : W := mkw 0xfe0c000844b9e3fc 0xfe44000000f8e3fc

def z713 : W := mkw 0x0012dd0000aac800 0x0017ff8000fffc00

def z714 : W := mkw 0x27248f90bf20f04e 0x07e00f803f00f00f

def z715 : W := mkw 0x0021aaf7bb649000 0x001faa7ffff49000

def z716 : W := mkw 0x26048c183430e24c 0xe65fcc7c3cf8e3cc

def z717 : W := mkw 0x0023fff7bb000000 0x001bffffff0b6c00

def z718 : W := mkw 0x0023fff7bbce0000 0x001bfffffff00000

def z719 : W := mkw 0x7f800008441126ff 0xffe00000000003ff

def z720 : W := mkw 0xa706cc5c36b8e34e 0xe7ffcc7c3ff8e3cf

def z721 : W := mkw 0x0413ff1020eed808 0x0657ff8020fffc0c

def z722 : W := mkw 0xb307666616cc7166 0xf9a066061f0c71f3

def z723 : W := mkw 0x002133f7bb000000 0x0008007fff000000

def z724 : W := mkw 0x0010030000eed800 0x0004038000fffc00

def z725 : W := mkw 0x6aa3ff77760124d5 0xffe78078000fffff

def z726 : W := mkw 0x0417ff1030eed808 0x0017ff8000fffc00

def z727 : W := mkw 0x002000f7bb000000 0x000833ffff000000

def z728 : W := mkw 0x0013730000eed800 0x0017f38000fffc00

def z729 : W := mkw 0x0023fff7bb000000 0x000bd5ffff000000

def z730 : W := mkw 0xa606444c14b8e34c 0xe65fc47c1cf8e3cc

def z731 : W := mkw 0xcc86ccdcf9b9c799 0x19a3b3fbc3f71c33

def z732 : W := mkw 0x0033ff4510eed800 0x0017ff8000fffc00

def z733 : W := mkw 0xfe0c0008441123fc 0xfe400000000003fc

def z734 : W := mkw 0x1401a83a20748228 0x1fffaa7a23f4923f

def z735 : W := mkw 0xa606445c3498634c 0xe65fc47c3cf863cc

def z736 : W := mkw 0xc803706f40990390 0xf81ff07fc0ff03f0

def z737 : W := mkw 0x1501222a0274922a 0x1fffa27a03f4923f

def z738 : W := mkw 0x003133f7bb461800 0x000833ffff071c00

def z739 : W := mkw 0x0023fff7bb440000 0x001ffffffff40000

def z740 : W := mkw 0x27808a90af20b44f 0x07e00a003f00900f

def z741 : W := mkw 0x0013ff0000eed800 0x001fff8223fffc00

def z742 : W := mkw 0x002088f7bb000000 0x001b887fff000000

def z743 : W := mkw 0xa606cc5c34b8e34c 0xe64f807c3cf8e3cc

def z744 : W := mkw 0x003000f7bbeed800 0x000c007ffffffc00

def z745 : W := mkw 0x0002ccd4b9a8c000 0x001ffffffffffc00

def z746 : W := mkw 0x8002504d00980300 0xe01fd07dc0f803c0

def z747 : W := mkw 0xd8188f6f4031dbb0 0xf8080fffc000fff0

def z748 : W := mkw 0xa206444c14986344 0xe003c47c1cf861c0

def z749 : W := mkw 0xa616df5c34bafb4c 0xe65fdffc3cfbffcc

def z750 : W := mkw 0xc80b706740cf0190 0xe01ff07fc0ff01c0

def z751 : W := mkw 0x1001202a00540220 0x1fffa07a23f4023f

def z752 : W := mkw 0x7f81aabaef75b6ff 0xe003d5fddcfb6dc0

def z753 : W := mkw 0x1133fff7bbeed822 0x19bffffffffffc33

def z754 : W := mkw 0xee840008441127dd 0xffe00000000003ff

def z755 : W := mkw 0xfa8b700844df27f5 0xfff7ff8000ffffff

def z756 : W := mkw 0x5801202a405502b0 0xf81fa07fc0f403f0

def z757 : W := mkw 0xff84000844fdf7ff 0xffe4000000ffffff

def z758 : W := mkw 0xd809202a40df03b0 0xf81ff07fc0ff03f0

def z759 : W := mkw 0x1501aa3a2274922a 0x1ffbaa7a23f0023f

def z760 : W := mkw 0xa604885c34b8e34c 0xe65f887c3cf8e3cc

def z761 : W := mkw 0x002000f7bb000000 0x001c7fffff0ffc00

def z762 : W := mkw 0xd80b706f40df03b0 0xfffff07fc0ff93ff

def z763 : W := mkw 0x1123fff7bb441022 0x1fffffffff04923f

def z764 : W := mkw 0x0003ff0000ce0000 0x0017ff8000fffc00

def z765 : W := mkw 0x3301222206443066 0xfffc6e063f0cf3ff

def z766 : W := mkw 0x1501aa3a2274922a 0x1fe7a27a03f4923f

def z767 : W := mkw 0x1500883a2230822a 0x1feb807a23f0023f

def z768 : W := mkw 0x0002ccd4b9000000 0x001bcc7fff000000

def z769 : W := mkw 0x8002404c00980300 0xe01ff07fc0f803c0

def z770 : W := mkw 0x152255cd9974922a 0x1fe45585dcf4923f

def z771 : W := mkw 0x0013ff1030eed800 0x0017ff803cfffc00

def z772 : W := mkw 0xb28b70ef8dde2765 0x07e38ff83ff0fc0f

def z773 : W := mkw 0x27908f90af20fc4f 0x07e00f803f00fc0f

def z774 : W := mkw 0xd80b746f40df43b0 0xf81ff47fc0ff63f0

def z775 : W := mkw 0x0002cc7730000000 0x001bcc7ffc000000

def z776 : W := mkw 0x0023fff7bbce0000 0x001ffffffffffc00

def z777 : W := mkw 0x1501203a2254022a 0x1fffaa7a23f4923f

def z778 : W := mkw 0xd81b736f40df1bb0 0xf81fffffc0fffff0

def z779 : W := mkw 0x1123fff7bb000022 0x19bbffffff000033

def z780 : W := mkw 0xa202404c04982344 0xe01fc47c1cf863c0

def z781 : W := mkw 0x7a800008445526f5 0xffe4000000ffffff

def z782 : W := mkw 0x7f800088cd1126ff 0xffe80007ff0003ff

def z783 : W := mkw 0x0010110000eed800 0x0004118000fffc00

def z784 : W := mkw 0x0533fff7bbeed80a 0x07fffffffffffc0f

def z785 : W := mkw 0xa60edc5d34bae34c 0xe65fcc7c3cf8e3cc

def z786 : W := mkw 0x0033fff7bbce1800 0x001fffffffff1c00

def z787 : W := mkw 0x1501203a2254022a 0x1feb807a23f0023f

def z788 : W := mkw 0xc80b704d40df0390 0xe01ff07dc0ff03c0

def z789 : W := mkw 0xff0c000844fff3fe 0xffe4000000fff3ff

def z790 : W := mkw 0xfa0c000844df63f4 0xf804000000ff63f0

def z791 : W := mkw 0x0023fff7bb000000 0x001bf07fff000000

def z792 : W := mkw 0x002011f7bb000000 0x000811ffff000000

def z793 : W := mkw 0x1521bb3b2274922a 0x1fffaa7a23f4923f

def z794 : W := mkw 0x0023fff7bb460000 0x001bffffff070000

def z795 : W := mkw 0x1500003a2210022a 0x1fff807a23f0023f

def z796 : W := mkw 0x002130f7bb000000 0x0008307fff000000

def z797 : W := mkw 0xa202cc5c34982344 0xe65fcc7c3cf8e3cc

def z798 : W := mkw 0x1521af3a3274922a 0x1fffaa7a23f4923f

def z799 : W := mkw 0xa606405c34b8e34c 0xe65fc07c3cf8e3cc

def z800 : W := mkw 0x0013ff0000eed800 0x0017dd8000fbec00

def z801 : W := mkw 0x0023fdf7b9000000 0x001bfdfffc000000

def z802 : W := mkw 0x0513ff1022eed80a 0x1fffff8223fffe3f

def z803 : W := mkw 0x0011aa0000eed800 0x0017ff8000fffc00

def z804 : W := mkw 0x0000880000208000 0x0017ff8000fffc00

def z805 : W := mkw 0xee84000844b9e7dd 0xffe4000000f8e3ff

def z806 : W := mkw 0x0523fff7bb00000a 0x07fbffffff00000f

def z807 : W := mkw 0xa606dd5c34b8e34c 0xe65fddfc3cf8e3cc

def z808 : W := mkw 0xa206444c14986344 0xe65fcc7c3cf8e3cc

def z809 : W := mkw 0xa606cc5c34b8e34c 0xffffcc7c3cfcf3ff

def z810 : W := mkw 0x0513ff1022eed80a 0x0017ff8000fffc00

def z811 : W := mkw 0x0013ff0000eed800 0x0003df8000fbfc00

def z812 : W := mkw 0xd80b706f40df03b0 0xf80bd07fc0fb03f0

def z813 : W := mkw 0x00125500008a4800 0x0017d58000fb6c00

def z814 : W := mkw 0x002255f7bb000000 0x0008007fff000000

def z815 : W := mkw 0xa606cc5c34b8e34c 0xe65f887c3cf083cc

def z816 : W := mkw 0x0123fff7bb001002 0x01bbffffff001003

def z817 : W := mkw 0x26248c90bf20e04c 0x06400c003f00e00c

def z818 : W := mkw 0xea8644c4dd8965d5 0xe0004405dc0861c0

def z819 : W := mkw 0x0033ff7732eed800 0x001ffffc3cfffc00

def z820 : W := mkw 0xd80b706f40df03b0 0xf803f07fc0ff01f0

def z821 : W := mkw 0x002255c599000000 0x001bd5fddc000000

def z822 : W := mkw 0x1501202a0074922a 0x1fffaa7a23f4923f

def z823 : W := mkw 0x0002cc5430000000 0x001bfc7ffc000000

def z824 : W := mkw 0xa616cd5c34b8eb4c 0xe65fcdfc3cf8efcc

def z825 : W := mkw 0xd81b736f40df1bb0 0xf81ff07fc0ff03f0

def z826 : W := mkw 0x1512553a229a4a2a 0x1fe855fa230b6e3f

def z827 : W := mkw 0x0023fff7bba8c000 0x001ffffffffffc00

def z828 : W := mkw 0x1501aa3a2274922a 0x1fffaa7a23fffe3f

def z829 : W := mkw 0x002000f7bb000000 0x0000007ddc000000

def z830 : W := mkw 0x0003faf7ab000000 0x001bffffff000000

def z831 : W := mkw 0xb706cc5c34b8e36e 0xffffcc7c3cf8e3ff

def z832 : W := mkw 0x4803706740cf0090 0xf81ff07fc0ff03f0

def z833 : W := mkw 0x0023fff7bb000000 0x07fbffffff00900f

def z834 : W := mkw 0x0023ff7732000000 0x001bfc7ffc000000

def z835 : W := mkw 0xd809206f405503b0 0xf81ff07fc0ff03f0

def z836 : W := mkw 0x002375e799000000 0x0003d5fddc000000

def z837 : W := mkw 0xd80b706f40df03b0 0xf81fc07fc0f803f0

def z838 : W := mkw 0x0003700000ce0000 0x0017f58000ff6c00

def z839 : W := mkw 0x0022cff7bb000000 0x001bcfffff000000

def z840 : W := mkw 0x0013ff0000eed800 0x001fff843cfffc00

def z841 : W := mkw 0x0427fff7bb20c008 0x001bffffff000000

def z842 : W := mkw 0xa202404c04982344 0xe65fc07c3cf803cc

def z843 : W := mkw 0xff8800ffef1127ff 0xffe8007fff0003ff

def z844 : W := mkw 0x0012cf0000a8d800 0x0017ff8000fffc00

def z845 : W := mkw 0x0012cc0000eed800 0x0017ff8000fffc00

def z846 : W := mkw 0xa606404c04b8e34c 0xe65fcc7c3cf8e3cc

def z847 : W := mkw 0x0023fff7bb000000 0x065fffffff00820c

def z848 : W := mkw 0xc803704c40df0390 0xf81ff07fc0ff03f0

def z849 : W := mkw 0x1501aa3a2274922a 0x1ffffa7fe3f4923f

def z850 : W := mkw 0x1013ff2200eed820 0x1817ff8200fffc30

def z851 : W := mkw 0x0000000000a8c000 0x00147f8000fffc00

def z852 : W := mkw 0x002000d5b9000000 0x0008007dfc000000

def z853 : W := mkw 0x000000d4b9000000 0x00187fffff000000

def z854 : W := mkw 0xa62533ab8fb8e34c 0xe6443383c3f8e3cc

def z855 : W := mkw 0x003255f7bb8a4800 0x000855ffff0b6c00

def z856 : W := mkw 0x0013ff4500eed800 0x0017ff85c0fffc00

def z857 : W := mkw 0xd80b706f40df03b0 0xffffffffe3ffffff

def z858 : W := mkw 0x0023fff7bb649000 0x001bfffffff00000

def z859 : W := mkw 0xa606cc5c34b8e34c 0xe003807c1cf001c0

def z860 : W := mkw 0x6a93ff80cdeffcd5 0xffeb8007fff003ff

def z861 : W := mkw 0xa616dd5c34baeb4c 0xe65fcc7c3cf8e3cc

def z862 : W := mkw 0x1509ba3b2276922a 0x1fffaa7a23f4923f

def z863 : W := mkw 0x002240f7bb000000 0x001bc07fff000000

def z864 : W := mkw 0xea8240c4cd8925d5 0xe0005585dc0b6dc0

def z865 : W := mkw 0x002375f7bb000000 0x001bf5ffff000000

def z866 : W := mkw 0x0001aa3222649000 0x1fffaa7a23f4923f

def z867 : W := mkw 0x6ab255c5dd8b6cd5 0xe0005585dc0b6dc0

def z868 : W := mkw 0xd80b706f40df03b0 0xe01bf07fc0fb01c0

def z869 : W := mkw 0xd80f746f50df43b0 0xf81ff07fc0ff03f0

def z870 : W := mkw 0x0013ffe789eed800 0x001ffffffffffc00

def z871 : W := mkw 0x7fa000ffff1126ff 0xffe8007fff0003ff

def z872 : W := mkw 0x0013ff7722eed800 0x001fffffe3fffc00

def z873 : W := mkw 0x0003ffe789000000 0x001bffffff000000

def z874 : W := mkw 0x0001aab2ab000000 0x001baa7fff000000

def z875 : W := mkw 0x002122f7bb000000 0x0008227fff000000

def z876 : W := mkw 0x0011bf000066d800 0x0017bf8000f7fc00

def z877 : W := mkw 0x00208af7bb000000 0x00080a7fff000000

def z878 : W := mkw 0x0021bff7bb000000 0x00083fffff000000

def z879 : W := mkw 0xa604885c3430a34c 0xe64b807c3cf003cc

def z880 : W := mkw 0xd803606e40dd03b0 0xf81ff07fc0ff03f0

def z881 : W := mkw 0xa626cf5c36b8e34c 0xe65fcc7c3cf8e3cc

def z882 : W := mkw 0xd8288f98fbdf03b0 0xf8040f803fff03f0

def z883 : W := mkw 0xff88000844ffb7ff 0xffe4000000ffffff

def z884 : W := mkw 0xc80a404d40990390 0xe01fc07dc0f803c0

def z885 : W := mkw 0xa206404c14982344 0xe01fc07c1cf803c0

def z886 : W := mkw 0xd80b706f40df03b0 0xf81fa07fc0f403f0

def z887 : W := mkw 0x0013ff2200eed800 0x001ffffa00fffc00

def z888 : W := mkw 0xd90b706f40df13b2 0xf9bff07fc0ff13f3

def z889 : W := mkw 0xee84000844b9e7dd 0xe644000000fbefcc

def z890 : W := mkw 0x0023fff7bbecd000 0x001ffffffffcf000

def z891 : W := mkw 0xa6048c5c3430e34c 0xe65f8c7c3cf0e3cc

def z892 : W := mkw 0x0033fff7bbeed800 0x001bfffffff71c00

def z893 : W := mkw 0x002377f7bb000000 0x000877ffff000000

def z894 : W := mkw 0x0033fff7bbeed800 0x001ffffffff8e000

def z895 : W := mkw 0x0013ff0000eed800 0x0013ff8000fb6c00

def z896 : W := mkw 0xee840088cd1127dd 0xffe80007ff0003ff

def z897 : W := mkw 0xd80b706f40df03b0 0xe01fd07dc0fb03c0

def z898 : W := mkw 0x0033ff2302eed800 0x0017ff8000fffc00

def z899 : W := mkw 0x002373e78b000000 0x001bffffff000000

def z900 : W := mkw 0xd80b706f40df03b0 0xf81fffffc0ff03f0

def z901 : W := mkw 0xd80b706f40df03b0 0xfffff07fe3ff03ff

def z902 : W := mkw 0x0021aaf7bb000000 0x001bffffff000000

def z903 : W := mkw 0x00a3fff7bb000401 0x01bbffffff001c03

def z904 : W := mkw 0x1501aa3a2274922a 0x1fffaffa23f4fe3f

def z905 : W := mkw 0x0012550000aac800 0x0004558000fbec00

def z906 : W := mkw 0x1023fff7bb440020 0x181bffffff040030

def z907 : W := mkw 0x0023fff7bbee9000 0x001fffffffff9000

def z908 : W := mkw 0xd80b706f409903b0 0xf81ff07fc0f803f0

def z909 : W := mkw 0x1501aa3a2274922a 0x1fff887a23f0823f

def z910 : W := mkw 0x8002444c10980300 0xe01fc47c1cf803c0

def z911 : W := mkw 0xa606dc5d34b8e34c 0xe65fdc7dfcf8e3cc

def z912 : W := mkw 0xee0c000844bbe3dc 0xe644000000fbe3cc

def z913 : W := mkw 0x0003fcf7b9000000 0x001bffffff000000

def z914 : W := mkw 0x1113ff2202eed822 0x1fffff8223fffe3f

def z915 : W := mkw 0xa616cf5c34b8fb4c 0xe65fcc7c3cf8e3cc

def z916 : W := mkw 0x0013ff1020eed800 0x001ffff820fffc00

def z917 : W := mkw 0x7f90000844fffeff 0xffe4000000ffffff

def z918 : W := mkw 0x7f800008441126ff 0xffe40000000fffff

def z919 : W := mkw 0x5809302b405702b0 0xf81ff07fc0ff03f0

def z920 : W := mkw 0x0033fff7bbeed800 0x000b807ffff00000

def z921 : W := mkw 0xa616dd5c34baeb4c 0xe65ffffc3cffffcc

def z922 : W := mkw 0xcd0ada5562ab919a 0xe7e05a05e30b91cf

def z923 : W := mkw 0xd82b736f42df03b0 0xf81ff07fc0ff03f0

def z924 : W := mkw 0xa602c85c24b8a34c 0xe65fcc7c3cf8e3cc

def z925 : W := mkw 0x1113ff2202eed822 0x0017ff8000fffc00

def z926 : W := mkw 0x2602cc5c3430a24c 0xe65fcc7c3cf8e3cc

def z927 : W := mkw 0x0033fff7bbaac800 0x001ffffffffbec00

def z928 : W := mkw 0x000000b2ab000000 0x00187fffff000000

def z929 : W := mkw 0xc802404c40990390 0xf81fc07fc0f803f0

def z930 : W := mkw 0xfe0c000844df23fc 0xfe44000000ff03fc

def z931 : W := mkw 0x0012550000ce4800 0x0004558000ff6c00

def z932 : W := mkw 0x0013ff7730eed800 0x001ffffffcfffc00

def z933 : W := mkw 0xfa98000844fffff5 0xffe4000000ffffff

def z934 : W := mkw 0x0023eef7bb000000 0x001bee7fff000000

def z935 : W := mkw 0xa615335c34563b4c 0xe64833fc3c071fcc

def z936 : W := mkw 0x0013750000eed800 0x0017f58000fffc00

def z937 : W := mkw 0xa606cc5c34b8e34c 0xe65ffc7ffcf8e3cc

def z938 : W := mkw 0x0033fff7bbeed800 0x0017fffddcfffc00

def z939 : W := mkw 0x002000f7bb000000 0x00080fffff000000

def z940 : W := mkw 0x0401aa3a22308208 0x1fffaa7a23f4923f

def z941 : W := mkw 0x0000000000ce0000 0x00147f8000fffc00

def z942 : W := mkw 0xa606cc5c34b8e34c 0xe7ffce7c3ff8f3cf

def z943 : W := mkw 0xd80b706f40df03b0 0xf81ff07fc0fffff0

def z944 : W := mkw 0x0033fff7bb8a4800 0x001bffffff000000

def z945 : W := mkw 0xd80b706f40df03b0 0xf807d07dc0ff03f0

def z946 : W := mkw 0xea8e54c5dd8b65d5 0xe0005585dc0b6dc0

def z947 : W := mkw 0xa606cc5c34b8e34c 0xe64bc47c3cf863cc

def z948 : W := mkw 0x0023fff7bb000000 0x1ffbffffff00023f

def z949 : W := mkw 0xd80b706f40df03b0 0xf80bb07fc0f703f0

def z950 : W := mkw 0x1523fff7bb64902a 0x1ffbffffff04903f

def z951 : W := mkw 0x1501aa3a2274922a 0xffffea7e23fc93ff

def z952 : W := mkw 0xd80b736f40df03b0 0xf81ff3ffc0ff03f0

def z953 : W := mkw 0x0002cc0000a8c000 0x0017dd8000fbec00

def z954 : W := mkw 0x0013ff0000eed800 0x181fff8200fffe30

def z955 : W := mkw 0x002000e799000000 0x0008007fdc000000

def z956 : W := mkw 0xd80b706f40df03b0 0xf9bff27fc3ff13f3

def z957 : W := mkw 0x0023fff7bb000000 0x0013fffddc000000

def z958 : W := mkw 0x0013ff0000eed800 0x07f7ff8023fffc0f

def z959 : W := mkw 0x0022ccf7bba8c000 0x001fcc7ffff8e000

def z960 : W := mkw 0xee86cc0844b9e7dd 0xfff7ff8000ffffff

def z961 : W := mkw 0xfe0ffc0844ffe3fc 0xfe57fc0000ffe3fc

def z962 : W := mkw 0xa202cc4c04b8e344 0xe65fcc7c3cf8e3cc

def z963 : W := mkw 0x002000f7bb000000 0x00182a7fff000000

def z964 : W := mkw 0xfe8c00fffd1127fd 0xffe8007fff0003ff

def z965 : W := mkw 0x0013ff0000eed800 0x0007d58000fffc00

def z966 : W := mkw 0xd81b756f40df4bb0 0xf81fffffc0fffff0

def z967 : W := mkw 0xa606cc5c3498234c 0xe65fcc7c3cf803cc

def z968 : W := mkw 0x150000888974922a 0x1ffc7f87fff4923f

def z969 : W := mkw 0xfa88000844df27f5 0xf804000000ff6ff0

def z970 : W := mkw 0x2602cc1824b8e24c 0xe65fcc7c3cf8e3cc

def z971 : W := mkw 0x0022ddd5b9000000 0x0003d5fddc000000

def z972 : W := mkw 0x0400881820308208 0x1fff887a23f0823f

def z973 : W := mkw 0xeaa655c5dd8965d5 0xe0005585dc0b6dc0

def z974 : W := mkw 0x0033fff7bbeed800 0x0003d5fddcfb6c00

def z975 : W := mkw 0x0011bf0000eed800 0x00043f8000fffc00

def z976 : W := mkw 0x0023fff7bb000000 0x0003bffbff000000

def z977 : W := mkw 0x0013fd0000eec800 0x0017fd8000ffec00

def z978 : W := mkw 0x102bfff7bb460020 0x001bffffff000000

def z979 : W := mkw 0xa606cc5c34b8e34c 0xe017cc7c1cf8e1c0

def z980 : W := mkw 0x1500003a2210022a 0x1ffc7ffa230ffe3f

def z981 : W := mkw 0x0023fff7bb000000 0x001bf5ffdc000000

def z982 : W := mkw 0xa616cf5c34b8fb4c 0xe65ffffc3cffffcc

def z983 : W := mkw 0x1501aa3a2274922a 0x1ffffffa23f4923f

def z984 : W := mkw 0xa606cc5c34b8e34c 0xe65ffffc3cf8e3cc

def z985 : W := mkw 0x1511af3a2274da2a 0x1ffffffa23fffe3f

def z986 : W := mkw 0xa606cc5c34b8e34c 0xe643cc7c3cf8e1cc

def z987 : W := mkw 0x0003fc7730eec000 0x001ffc7ffcffe000

def z988 : W := mkw 0xfaa800ffff1127f5 0xffe8007fff0003ff

def z989 : W := mkw 0x1501ba3b2274922a 0x1fffba7be3f4923f

def z990 : W := mkw 0xd80b706f40df03b0 0xe017f07dc0ff01c0

def z991 : W := mkw 0x0023fff7bb000000 0x001bcc7fff000000

def z992 : W := mkw 0x7f93ff0844fffeff 0xfff7ff8000ffffff

def z993 : W := mkw 0xa604885c3430a34c 0xe65fcc7c3cf8e3cc

def z994 : W := mkw 0x1501aa3a2274922a 0x1fe78a7823f4923f

def z995 : W := mkw 0x0523fff7bb64900a 0x07fffffffff4900f

def z996 : W := mkw 0xff8400feff1127ff 0xffe8007fff0003ff

def z997 : W := mkw 0xd809206f40df03b0 0xf81fa07fc0ff03f0

def z998 : W := mkw 0x1133fff7bb461822 0x19bbffffff071c33

def z999 : W := mkw 0xa206cc4c14b8e344 0xe01fcc7c1cf8e3c0

def z1000 : W := mkw 0xc80b706f409b0390 0xe01ff07fc0fb03c0

def z1001 : W := mkw 0x580930a3c94700b0 0x18003383c3070030

def z1002 : W := mkw 0x6e800098ed1126dd 0xffe8007fff0003ff

def z1003 : W := mkw 0x1501aa3a2274922a 0x1ffffa7a23ff923f

def z1004 : W := mkw 0xd81b776f40df5bb0 0xf81ff7ffc0ff7ff0

def z1005 : W := mkw 0xa716cf5c36b8fb4e 0xe7ffcffc3ff8ffcf

def z1006 : W := mkw 0x6a81aa80cd65b4d5 0xffffaa07fff493ff

def z1007 : W := mkw 0xa206cc5c34986344 0xe01fcc7c3cf863c0

def z1008 : W := mkw 0x8017ff4410eed900 0x0017ff8000fffc00

def z1009 : W := mkw 0xd81b716f40df0bb0 0xf81ff1ffc0ff0ff0

def z1010 : W := mkw 0x0013ff0000eed800 0x00078f8000fffc00

def z1011 : W := mkw 0x1123fff7bb441022 0x001bffffff000000

def z1012 : W := mkw 0xfe8c000844ffe7fd 0xffe4000000ffffff

def z1013 : W := mkw 0xd81b756f40df4bb0 0xf81ff07fc0ff03f0

def z1014 : W := mkw 0xa606cc5c34b8e34c 0xfe5fec7e3cfce3fc

def z1015 : W := mkw 0xa606cc5c34b8e34c 0xe65bcc7c3cf003cc

def z1016 : W := mkw 0x0023fff7bb649000 0x001ffffffffffc00

def z1017 : W := mkw 0x8002404c00980300 0xe01fcc7c3cf803c0

def z1018 : W := mkw 0x0033fff7bbeed800 0x1ffffffffffffe3f

def z1019 : W := mkw 0x150088182074922a 0x1fffaa7a23f4923f

def z1020 : W := mkw 0x002000f7bb000000 0x000855ffff000000

def z1021 : W := mkw 0xa706cc5c34b8f34e 0xe7ffcc7c3cf8f3cf

def z1022 : W := mkw 0x0013ff0000eed800 0x0007b38000fffc00

def z1023 : W := mkw 0x0013ff0000eed800 0xe01fff8400ffffc0

def z1024 : W := mkw 0xa606c85c34b8a34c 0xe65fc87c3cf883cc

def z1025 : W := mkw 0xd90b706f42df03b2 0xf9bff07fc3ff03f3

def z1026 : W := mkw 0x0022cfd4bb000000 0x001bffffff000000

def z1027 : W := mkw 0x0013ff1022eed800 0x0017ff8023fffc00

def z1028 : W := mkw 0xa606cc5c34b8e34c 0xe01fc47c1cf863c0

def z1029 : W := mkw 0x0023fff7bb441000 0x001bffffff041000

def z1030 : W := mkw 0xd80b746f50df03b0 0xf81ff47fdcff03f0

def z1031 : W := mkw 0xd80a406f409903b0 0xf80b807fc0f003f0

def z1032 : W := mkw 0x00208cf7bb000000 0x00080c7fff000000

def z1033 : W := mkw 0xa616cc5c34b8fb4c 0xe65fcc7c3cf8ffcc

def z1034 : W := mkw 0x0033fff7bb461800 0x001bffffff000000

def z1035 : W := mkw 0x588930a3c94704b1 0x19a03003c3070033

def z1036 : W := mkw 0x000000e789000000 0x00187fffff000000

def z1037 : W := mkw 0xa626dd5d34b8e34c 0xe65fcc7c3cf8e3cc

def z1038 : W := mkw 0xd80b706f40df03b0 0xf807b07bc0ff03f0

def z1039 : W := mkw 0x0013ff0000eed800 0x0017f58000ff6c00

def z1040 : W := mkw 0xa606ce5c36b8e34c 0xe65fce7c3ff8e3cc

def z1041 : W := mkw 0x5803702a40df02b0 0xf81ff07fc0ff03f0

def z1042 : W := mkw 0x0003707730000000 0x001bf07ffc000000

def z1043 : W := mkw 0x0013ffd4b9eed800 0x001ffffffffffc00

def z1044 : W := mkw 0xfa9bff0844fffff5 0xfff7ff8000ffffff

def z1045 : W := mkw 0x1501a83a2274822a 0x1fffa87a23f4823f

def z1046 : W := mkw 0x0003746710000000 0x001bf47fdc000000

def z1047 : W := mkw 0x0012dd0000eed800 0x0017dd8000fffc00

def z1048 : W := mkw 0x0033fff7bb004800 0x001bffffff006c00

def z1049 : W := mkw 0x0023fff7bb000000 0x001bddfdfc000000

def z1050 : W := mkw 0x002244f7bb000000 0x0008447fff000000

def z1051 : W := mkw 0x8402cc5c30b88308 0xe65fcc7c3cf883cc

def z1052 : W := mkw 0x0013ff0000eed800 0x0003f78000ff7c00

def z1053 : W := mkw 0x8003706f00de0300 0xe01ff07fc0ff03c0

def z1054 : W := mkw 0x7f81aa084475b6ff 0xfff7ff8000ffffff

def z1055 : W := mkw 0xfa880008441127f5 0xffe40000000fffff

def z1056 : W := mkw 0xa606cc5c34b8e34c 0xe65fcc7c3cffffcc

def z1057 : W := mkw 0x1511af3a2274da2a 0x1fffaa7a23f4923f

def z1058 : W := mkw 0x1123fff7bb649022 0x19bffffffff49033

def z1059 : W := mkw 0x900b706f00de0320 0xe01ff07fc0f803c0

def z1060 : W := mkw 0x0523fff7bb20900a 0x1fffffffff04923f

def z1061 : W := mkw 0x0023fff7bb000000 0x001bffffff071c00

def z1062 : W := mkw 0x0033fff7bb20d800 0x001bffffff000000

def z1063 : W := mkw 0x0011bb0000eed800 0x0017bb8000fffc00

def z1064 : W := mkw 0x0023fff7bb000000 0x001fffffff08e000

def z1065 : W := mkw 0x0023fff7bb000000 0x000bb3ffff000000

def z1066 : W := mkw 0x0033ffd5b9eed800 0x001ffffdfcfffc00

def z1067 : W := mkw 0x583933a3cb4718b0 0x18003383c3071c30

def z1068 : W := mkw 0x0033fff7bb020800 0x001bffffff030c00

def z1069 : W := mkw 0x0013750000ce4800 0x0003d58000fb6c00

def z1070 : W := mkw 0x002255f7bb000000 0x000055fddc000000

def z1071 : W := mkw 0x0013ff0000eed800 0x001fff87c0fffc00

def z1072 : W := mkw 0x0033ff1032eed800 0x0017ff8000fffc00

def z1073 : W := mkw 0x0023fff7bb20c000 0x001bffffff00e000

def z1074 : W := mkw 0x0021aaf7bb000000 0x000b807fff000000

def z1075 : W := mkw 0xc802404c40990390 0xe01fd07dc0fb03c0

def z1076 : W := mkw 0xdd0b706f40df03ba 0xfffff07fc0ff03ff

def z1077 : W := mkw 0x0013ff2202eed800 0x0017ff8203fffc00

def z1078 : W := mkw 0x588930a3c94704b1 0x18003183c0070c30

def z1079 : W := mkw 0x1501aa3a2274922a 0x1feba27a23f4123f

def z1080 : W := mkw 0xa606cc5c34b8e34c 0xe65fc07c3cf803cc

def z1081 : W := mkw 0xea9a55c5cd8b6dd5 0xe0005585dc0b6dc0

def z1082 : W := mkw 0x0013ff4410eed800 0x0017ff841cfffc00

def z1083 : W := mkw 0xd88b706f40df07b1 0xf9bff07fc0ff1ff3

def z1084 : W := mkw 0x8002cc5c30b8c300 0xe01fcc7c3cf8e3c0

def z1085 : W := mkw 0x0023ffd5b9000000 0x001bfffdfc000000

def z1086 : W := mkw 0x0013700000eed800 0x0017ff8000fffc00

def z1087 : W := mkw 0x000000e789000000 0x0008007fff000000

def z1088 : W := mkw 0xd82b756f50df03b0 0xf81ff07fc0ff03f0

def z1089 : W := mkw 0x0033fff7bb8a4800 0x001fffffff0ffc00

def z1090 : W := mkw 0xd80b706f40df03b0 0xfe5ff87fe0ff83fc

def z1091 : W := mkw 0x0010050000eed800 0x0004058000fffc00

def z1092 : W := mkw 0xd80b706f40df03b0 0xf81bf07fc0f003f0

def z1093 : W := mkw 0x0023fff7bb000000 0x1fffffffff0ffe3f

def z1094 : W := mkw 0x0013750000ce4800 0x0017ff8000fffc00

def z1095 : W := mkw 0x0002ccd4b9000000 0x001bddfdfc000000

def z1096 : W := mkw 0x0013ff7632eed800 0x001ffffe3ffffc00

def z1097 : W := mkw 0x0002dc5530000000 0x001bdc7dfc000000

def z1098 : W := mkw 0x1500883a2274922a 0x1fff887a23f4923f

def z1099 : W := mkw 0x1501223a2254122a 0x1fffa27a23f4123f

def z1100 : W := mkw 0x8013ff4400eed900 0xe017ff8400fffdc0

def z1101 : W := mkw 0xa606cf5c34b8e34c 0xe65fcffc3cf8e3cc

def z1102 : W := mkw 0x0022ddf7bb000000 0x001bddffff000000

def z1103 : W := mkw 0x801bff4500eed900 0x0017ff8000fffc00

def z1104 : W := mkw 0x002375e799000000 0x001bffffff000000

def z1105 : W := mkw 0xc80a504d409b0390 0xe003d07dc0fb01c0

def z1106 : W := mkw 0x8002406f00980300 0xe01fc07fc0f803c0

def z1107 : W := mkw 0x05208af7bb20900a 0x07e80a7fff00900f

def z1108 : W := mkw 0x1501aa3a2274922a 0x1fffee7a23fcf23f

def z1109 : W := mkw 0x00208ff7bb000000 0x0008007fff000000

def z1110 : W := mkw 0x582931a3c94700b0 0x18003183c0070030

def z1111 : W := mkw 0xa706ce5c36b8f34e 0xe65fcc7c3cf8e3cc

def z1112 : W := mkw 0x26848c90bd20e44d 0x07e00c003f00e00f

def z1113 : W := mkw 0x002003f7bb000000 0x000803ffff000000

def z1114 : W := mkw 0xd809306f405703b0 0xf81fb07fc0f703f0

def z1115 : W := mkw 0x0023fff7bb000000 0x0003807ddc000000

def z1116 : W := mkw 0x0023faf7bb000000 0x001bfa7fff000000

def z1117 : W := mkw 0x0003eef6bb000000 0x001bffffff000000

def z1118 : W := mkw 0x0023fff7bb208000 0x001ffffffff08000

def z1119 : W := mkw 0xa606cc5c3430a34c 0xe65fcc7c3cf083cc

def z1120 : W := mkw 0x802bfff7bb8a0100 0x001bffffff000000

def z1121 : W := mkw 0x00108f0000eed800 0x00147f8000fffc00

def z1122 : W := mkw 0x000000d4b9000000 0x0008007fff000000

def z1123 : W := mkw 0x00208ff7bb000000 0x00187fffff000000

def z1124 : W := mkw 0xd80b756f40df03b0 0xf81ff5ffc0ff03f0

def z1125 : W := mkw 0x0021afb2bb000000 0x001bffffff000000

def z1126 : W := mkw 0x002370f7bbce0000 0x001ff07fffff0000

def z1127 : W := mkw 0x0022ccf7bb000000 0x001bffffff000000

def z1128 : W := mkw 0x112122f7bb441022 0x19a8227fff041033

def z1129 : W := mkw 0xee94000844ffffdd 0xffe4000000ffffff

def z1130 : W := mkw 0xea9655c4dd8b6dd5 0xe0005585dc0b6dc0

def z1131 : W := mkw 0x0021bbb3ab000000 0x001bffffff000000

def z1132 : W := mkw 0x0033fff7bba8d800 0x001ffffffff8fc00

def z1133 : W := mkw 0xd80a406f40df03b0 0xf81fc07fc0ff03f0

def z1134 : W := mkw 0x22b08f90bf20fc45 0x07e00f803f00fc0f

def z1135 : W := mkw 0x589933a3c9471cb1 0x19a03383c3071c33

def z1136 : W := mkw 0x0003ff0000649000 0x0017ff8000fffc00

def z1137 : W := mkw 0xd80b706f40df03b0 0xf81ffa7fc0ff93f0

def z1138 : W := mkw 0x15008a182274922a 0x1fff8a7823f4923f

def z1139 : W := mkw 0xfe1c000844fffbfc 0xfe44000000fffffc

def z1140 : W := mkw 0x0013ff5430eed800 0x0017fff800fffc00

def z1141 : W := mkw 0x002000f7bb000000 0x0018707fff000000

def z1142 : W := mkw 0x26348f90bf20f84c 0x06400f803f00fc0c

def z1143 : W := mkw 0xd80b706f40df03b0 0xf81ffc7fc0ffe3f0

def z1144 : W := mkw 0x48b133a3cb471c91 0x19a03383c3071c33

def z1145 : W := mkw 0x328120aa8d542665 0x1fffaffa3ff4fe3f

def z1146 : W := mkw 0x0013770000ce5800 0x0017f78000ff7c00

def z1147 : W := mkw 0x0012cf0000eed800 0x0017cf8000fffc00

def z1148 : W := mkw 0x0021bfb3bb000000 0x001bbffbff000000

def z1149 : W := mkw 0x26848c90bd20e44d 0x06400d803c00ec0c

def z1150 : W := mkw 0xeaaa55c5dd8b25d5 0xe0005585dc0b6dc0

def z1151 : W := mkw 0x0021aff7bb000000 0x001bafffff000000

def z1152 : W := mkw 0x599133a2cb471cb3 0x19a03383c3071c33

def z1153 : W := mkw 0x0013ff0000aac800 0x0017ff8000fbec00

def z1154 : W := mkw 0x0001200000440000 0x0017ff8000fffc00

def z1155 : W := mkw 0xd80a504d40df03b0 0xf81fd07dc0ff03f0

def z1156 : W := mkw 0x26048c90bd20e04c 0x06400f803f00e00c

def z1157 : W := mkw 0xfe1fff0844fffbfc 0xfe57ff8000fffffc

def z1158 : W := mkw 0xa706ce5c36b8f34e 0xffffee7e3ffcf3ff

def z1159 : W := mkw 0x0013730000ce1800 0x0017ff8000fffc00

def z1160 : W := mkw 0x000000b2ab000000 0x0008007fff000000

def z1161 : W := mkw 0xd80b726f40df13b0 0xf81ff27fc0ff13f0

def z1162 : W := mkw 0x002133f7bb000000 0x00187fffff000000

def z1163 : W := mkw 0x0013ffb2abeed800 0x001ffffffffffc00

def z1164 : W := mkw 0x002377e79b000000 0x001bf7ffdf000000

def z1165 : W := mkw 0x002120f7bb000000 0x001ba07fff000000

def z1166 : W := mkw 0x0013ff2300eed800 0x0017ff83c0fffc00

def z1167 : W := mkw 0x002370f7bb000000 0x001bffffff000000

def z1168 : W := mkw 0x2200000804102244 0xe65fcc7c3cf8e3cc

def z1169 : W := mkw 0xeea400ffff1127dd 0xffe8007fff0003ff

def z1170 : W := mkw 0x58a933a3cb4704b1 0x19a03383c3071c33

def z1171 : W := mkw 0xea800008449927d5 0xffe4000000ffffff

def z1172 : W := mkw 0xa606cc5c34b8e34c 0xe647c47c1cf8e3cc

def z1173 : W := mkw 0x0033fff7bbaad800 0x001bffffff0bfc00

def z1174 : W := mkw 0x0033ffe799eed800 0x001fffffdcfffc00

def z1175 : W := mkw 0x000240c489000000 0x001bffffff000000

def z1176 : W := mkw 0x05008a182230920a 0x1fffaa7a23f4923f

def z1177 : W := mkw 0x7f8000084475b6ff 0xffe4000000f493ff

def z1178 : W := mkw 0x0023fcf7bb000000 0x001bfc7fff000000

def z1179 : W := mkw 0x0013ff0000ce4800 0x0017ff8000ff6c00

def z1180 : W := mkw 0x0000007730000000 0x0008007ffc000000

def z1181 : W := mkw 0x002255d5b9000000 0x000855fdfc000000

def z1182 : W := mkw 0xd808006f401103b0 0xf81f807fc0f003f0

def z1183 : W := mkw 0x0033fff7bbeed800 0x001bfffffffb6c00

def z1184 : W := mkw 0x0033fff7bbeed800 0x001ffffffff49000

def z1185 : W := mkw 0x0033fff7bb20d800 0x001fffffff0ffc00

def z1186 : W := mkw 0x1501aa3a2274922a 0x1fef807a23f4923f

def z1187 : W := mkw 0x0010000000eed800 0x0004558000fffc00

def z1188 : W := mkw 0xd80a406f409903b0 0xf81ff07fc0ff03f0

def z1189 : W := mkw 0x0033fff7bbeed800 0x001bfffffff0fc00

def z1190 : W := mkw 0x0023fff7bb649000 0x1ffffffffff4923f

def z1191 : W := mkw 0x0013ff4400eed800 0x001ffffc00fffc00

def z1192 : W := mkw 0x0023ffe799000000 0x001bffffdc000000

def z1193 : W := mkw 0x000370e789000000 0x001bf07fff000000

def z1194 : W := mkw 0xa606cc5c34b8e34c 0xe65fee7e3ff8e3cc

def z1195 : W := mkw 0x0003fe7732000000 0x001bfe7fff000000

def z1196 : W := mkw 0xea8000cccd1127d5 0xffe8007fff0003ff

def z1197 : W := mkw 0x0022dff7bb000000 0x00085fffff000000

def z1198 : W := mkw 0x1501ae3a2274d22a 0x1fffae7a23f4f23f

def z1199 : W := mkw 0x1001aa3a22540220 0x1fffaa7a23f4923f

def z1200 : W := mkw 0x0022ccf7bb000000 0x000b807fff000000

def z1201 : W := mkw 0xa606cc5c34b8e34c 0xe65fcffc3cf8ffcc

def z1202 : W := mkw 0x112000f7bb000022 0x19a8007fff000033

def z1203 : W := mkw 0x0033fff7bbce4800 0x001fffffffff6c00

def z1204 : W := mkw 0x8023fff7bb880100 0xe01bffffff0801c0

def z1205 : W := mkw 0x0033ff7732eed800 0x001ffffa23fffc00

def z1206 : W := mkw 0x0033fff7bb64d800 0x001ffffffff4fc00

def z1207 : W := mkw 0x2202cc5434a8e044 0xe65fcc7c3cf8e3cc

def z1208 : W := mkw 0x5803706f405502b0 0xf81ff07fc0ff03f0

def z1209 : W := mkw 0x0013ff3222eed800 0x0017fff800fffc00

def z1210 : W := mkw 0xd81b706f40df1bb0 0xf81ff07fc0ff1ff0

def z1211 : W := mkw 0xa606cc5c34b8e34c 0xe65fddfc3cfbefcc

def z1212 : W := mkw 0x260088182430a24c 0xe65f887c3cf083cc

def z1213 : W := mkw 0x0022ddd5b9000000 0x001bffffff000000

def z1214 : W := mkw 0x0033fff7bbeed800 0x001fffffffff0000

def z1215 : W := mkw 0x0032ddd5b9aac800 0x001fddfdfcfbec00

def z1216 : W := mkw 0x002370e799000000 0x001bf07fdc000000

def z1217 : W := mkw 0xa606cc5c34b8e34c 0xffffcc7e3ff8e3ff

def z1218 : W := mkw 0x0013ff0000eed800 0x1ff7ff8000fffe3f

def z1219 : W := mkw 0x002250f7bb000000 0x0008507fff000000

def z1220 : W := mkw 0x8406cc5c30b8c308 0xe01fcc7c3cf803c0

def z1221 : W := mkw 0x1501af3a2274922a 0x1fffaffa23f4923f

def z1222 : W := mkw 0x0013770000eed800 0x0004778000fffc00

def z1223 : W := mkw 0x0012df0000aad800 0x0017df8000fbfc00

def z1224 : W := mkw 0xfa08000844df23f4 0xfe44000000ffe3fc

def z1225 : W := mkw 0x1501aa3a2230822a 0x1fffaa7a23f0823f

def z1226 : W := mkw 0x1501aa3a2274922a 0x1fe3aa7a23f4903f

def z1227 : W := mkw 0x0022ccd5b9000000 0x001bcc7dfc000000

def z1228 : W := mkw 0x00308ff7bb20d800 0x00080fffff00fc00

def z1229 : W := mkw 0xee97ff0844ffffdd 0xfff7ff8000ffffff

def z1230 : W := mkw 0xa606405c3498234c 0xe64b807c3cf003cc

def z1231 : W := mkw 0x0023fff7bbeec000 0x001fffffffffe000

def z1232 : W := mkw 0xd90b726f42df13b2 0xf81ff07fc0ff03f0

def z1233 : W := mkw 0x052000f7bb00000a 0x07e8007fff00000f

def z1234 : W := mkw 0x0023fff7bb000000 0xe01fffffff0803c0

def z1235 : W := mkw 0x0010000000eed800 0x00040f8000fffc00

def z1236 : W := mkw 0x1113ff3222eed822 0x19bffffa23fffc33

def z1237 : W := mkw 0x0013ff0000eed800 0x19b7ff8203fffc33

def z1238 : W := mkw 0x0003706700000000 0x001bfc7ffc000000

def z1239 : W := mkw 0x0023fff7bb000000 0x000b8fffff000000

def z1240 : W := mkw 0x8027fff7bb884100 0x001bffffff000000

def z1241 : W := mkw 0xa206cc5434a8e144 0xe01fcc7c3cf8e1c0

def z1242 : W := mkw 0x1511bb3a22769a2a 0x1ffffffa23fffe3f

def z1243 : W := mkw 0xee840008441127dd 0xffe40000000fffff

def z1244 : W := mkw 0x0013ff3222eed800 0x1ffffffa23fffe3f

def z1245 : W := mkw 0x26808890ad20a44d 0x07e00f803f00fc0f

def z1246 : W := mkw 0x1001aa2a00749220 0x1fffaa7a23f4923f

def z1247 : W := mkw 0x6a81aa32660124d5 0xffffaa7a230fffff

def z1248 : W := mkw 0x0010000000eed800 0x0004338000fffc00

def z1249 : W := mkw 0xa606dc5c34bae34c 0xe65fdc7c3cfbe3cc

def z1250 : W := mkw 0x0401aa1820749208 0x1fffaa7a23f4923f

def z1251 : W := mkw 0x00008890a9000000 0x001bffffff000000

def z1252 : W := mkw 0xea8a50c5cd8b25d5 0xe0005005dc0b01c0

def z1253 : W := mkw 0x0013ff0000eed800 0x0003bf8000f7fc00

def z1254 : W := mkw 0x0033fff7bb461800 0x001fffffff0ffc00

def z1255 : W := mkw 0x0003ff0000a8c000 0x0017ff8000fffc00

def z1256 : W := mkw 0xc80a504d409b0390 0xf81ff07fc0ff03f0

def z1257 : W := mkw 0x0021bbf7bb000000 0x001bbbffff000000

def z1258 : W := mkw 0x598122a2cb4514b3 0x19a02203c3041033

def z1259 : W := mkw 0x0003fc0000eec000 0x0017ff8000fffc00

def z1260 : W := mkw 0x002370f7bb000000 0x000b807fff000000

def z1261 : W := mkw 0x0003ffd4b9000000 0x001bffffff000000

def z1262 : W := mkw 0xd80b706f40df03b0 0xf80f807fc0ff03f0

def z1263 : W := mkw 0xd80b706f40df03b0 0xf81ffa7fe3ff03f0

def z1264 : W := mkw 0x0513ff3222eed80a 0x07fffffa23fffc0f

def z1265 : W := mkw 0x0033fff7bb66d800 0x001bffffff07fc00

def z1266 : W := mkw 0x002005f7bb000000 0x000805ffff000000

def z1267 : W := mkw 0xa616cc5c34baeb4c 0xe65fcc7c3cfbefcc

def z1268 : W := mkw 0x26a48f90bf20e44d 0x07e00f803f00fc0f

def z1269 : W := mkw 0x598932a3cb4714b3 0x19a03383c3071c33

def z1270 : W := mkw 0x0533fff7bb20d80a 0x07fbffffff00fc0f

def z1271 : W := mkw 0x0033fff7bb001800 0x001bffffff001c00

def z1272 : W := mkw 0x0023fff7bb884000 0x001bffffff086000

def z1273 : W := mkw 0x0011330000eed800 0x00147f8000fffc00

def z1274 : W := mkw 0x26248d90bd20e04c 0x06400d803c00e00c

def z1275 : W := mkw 0xfa880008441127f5 0xffe00000000003ff

def z1276 : W := mkw 0x59a133a3cb4514b3 0x19a03383c3071c33

def z1277 : W := mkw 0x0023fff7bb000000 0x001fffffff049000

def z1278 : W := mkw 0x1501aa3a2274922a 0x1feb8a7a23f0923f

def z1279 : W := mkw 0x0012550000eed800 0x0000558000fb6c00

def z1280 : W := mkw 0x1101222a02541222 0x1fffaa7a23f4923f

def z1281 : W := mkw 0xa606cc5c34b8e34c 0xfffffffe3fffffff

def z1282 : W := mkw 0x6e8000084431a6dd 0xffe4000000ffffff

def z1283 : W := mkw 0x1513ff3222eed82a 0x1ff7ff8223fffc3f

def z1284 : W := mkw 0x15008a3a2230922a 0x1fff8a7a23f0923f

def z1285 : W := mkw 0x0023fff7bb000000 0x001baa7fff000000

def z1286 : W := mkw 0xa606ce5c34b8f34c 0xe65fce7c3cf8f3cc

def z1287 : W := mkw 0x4800000840110290 0xf81ff07fc0ff03f0

def z1288 : W := mkw 0x101bff2300eed820 0x0017ff8000fffc00

def z1289 : W := mkw 0x000120a289000000 0x001bffffff000000

def z1290 : W := mkw 0xd809302b40df03b0 0xf81fb07bc0ff03f0

def z1291 : W := mkw 0x1511aa3a22769a2a 0x1fffaa7a23f79e3f

def z1292 : W := mkw 0xa604881824b8e34c 0xe65fcc7c3cf8e3cc

def z1293 : W := mkw 0xd81b706f40df4bb0 0xf81ff07fc0ff6ff0

def z1294 : W := mkw 0xd91b736f42df1bb2 0xf9bff3ffc3ff1ff3

def z1295 : W := mkw 0x1511ab3a22749a2a 0x1fffabfa23f49e3f

def z1296 : W := mkw 0x592933a3cb4710b2 0x19a03383c3071033

def z1297 : W := mkw 0x0023fff7bb000000 0x001fffffff0f0000

def z1298 : W := mkw 0x7a8000aacd1126f5 0xffe8007fff0003ff

def z1299 : W := mkw 0x0002400000880000 0x0017ff8000fffc00

def z1300 : W := mkw 0xd80b726f42df03b0 0xf81ff27fc3ff03f0

def z1301 : W := mkw 0x0012550000eed800 0x00147f8000fffc00

def z1302 : W := mkw 0x26948f90bd20fc4d 0x07e00f803f00fc0f

def z1303 : W := mkw 0xd90b726f42df13b2 0xfffffa7fe3ff93ff

def z1304 : W := mkw 0xa606cc5c34b8e34c 0xe6478c783cf8e3cc

def z1305 : W := mkw 0xd809206f405503b0 0xf80b807fc0f003f0

def z1306 : W := mkw 0x4d008a106221909a 0xfffc7a07e30f93ff

def z1307 : W := mkw 0x0023fff7bb000000 0x0003f7ffdf000000

def z1308 : W := mkw 0x1511bb3a22769a2a 0x1fffaa7a23f4923f

def z1309 : W := mkw 0x002255e799000000 0x000855ffdc000000

def z1310 : W := mkw 0x0013ff0000eed800 0x065fff8020fffe0c

def z1311 : W := mkw 0x1505ae3a3274d22a 0x1fffaa7a23f4923f

def z1312 : W := mkw 0x000370e789000000 0x001bf5ffdc000000

def z1313 : W := mkw 0x003375e799ce4800 0x001ff5ffdcff6c00

def z1314 : W := mkw 0x0033fff7bb669800 0x001ffffffff79c00

def z1315 : W := mkw 0x0013ff6700eed800 0x0017fff800fffc00

def z1316 : W := mkw 0x0011bb0000669800 0x0017ff8000fffc00

def z1317 : W := mkw 0x002255f7bb000000 0x00187fffff000000

def z1318 : W := mkw 0x0000000800100200 0x1fffaa7a23f4923f

def z1319 : W := mkw 0x9003706f00dc0320 0xf81ff07fc0fc03f0

def z1320 : W := mkw 0x1501aa3a2274922a 0x1fffee7e3ff4923f

def z1321 : W := mkw 0x002000f7bb000000 0x00184c7fff000000

def z1322 : W := mkw 0xee04000844b9e3dc 0xfe44000000ffe3fc

def z1323 : W := mkw 0x002000f7bb000000 0x1ffc2a7fff04923f

def z1324 : W := mkw 0x0023fff7bb880000 0x001ffffffff80000

def z1325 : W := mkw 0x27a08f90bf20b44f 0x07e00f803f00fc0f

def z1326 : W := mkw 0x0001aab2ab649000 0x001ffffffffffc00

def z1327 : W := mkw 0x0003ffb2ab000000 0x001bffffff000000

def z1328 : W := mkw 0x0023fff7bba8c000 0x001bfffffff00000

def z1329 : W := mkw 0xa686cc5c34b8e74d 0xe7ffcc7c3cf8ffcf

def z1330 : W := mkw 0x0003fa0000ee9000 0x0017ff8000fffc00

def z1331 : W := mkw 0x1500883a2230822a 0x1fffaa7a23f4923f

def z1332 : W := mkw 0x0012df0000eed800 0x00045f8000fffc00

def z1333 : W := mkw 0xa6048c1834b8e34c 0xe65f8c783cf8e3cc

def z1334 : W := mkw 0x4c808898e9318699 0x1fffbbfbe3f79e3f

def z1335 : W := mkw 0xd80b706f40df03b0 0xf81ff3ffc0ff1ff0

def z1336 : W := mkw 0xee8400dcfd1127dd 0xe648007dfc0003cc

def z1337 : W := mkw 0xfa8800efcd1127f5 0xf808007fdc0003f0

def z1338 : W := mkw 0xa604005c3410234c 0xe65f807c3cf003cc

def z1339 : W := mkw 0xd80b606f40dd03b0 0xf81fe07fc0fc03f0

def z1340 : W := mkw 0x1501203a2274922a 0x1fffa07a23f4923f

def z1341 : W := mkw 0xfa880088cd1127f5 0xffe80007ff0003ff

def z1342 : W := mkw 0x000370e789ce0000 0x001ffffffffffc00

def z1343 : W := mkw 0x1501aa3a2274922a 0x1fffa07a23f4023f

def z1344 : W := mkw 0x1113ff0000eed822 0x19b7ff8000fffc33

def z1345 : W := mkw 0x588120a2c94504b1 0x19a03383c3071c33

def z1346 : W := mkw 0xd80b706f40df03b0 0xf81ff5ffc0ff6ff0

def z1347 : W := mkw 0xa606cc5c34b8e34c 0xe64b8c7c3cf0e3cc

def z1348 : W := mkw 0xa606405c3498234c 0xe65fcc7c3cf8e3cc

def z1349 : W := mkw 0x0003ff7730000000 0x001bfffffc000000

def z1350 : W := mkw 0x0011af0000eed800 0x0017af8000fffc00

def z1351 : W := mkw 0x0011af000064d800 0x0017ff8000fffc00

def z1352 : W := mkw 0x1511bf3a2276da2a 0x1fffbffa23f7fe3f

def z1353 : W := mkw 0xd80a506f409b03b0 0xf81fd07fc0fb03f0

def z1354 : W := mkw 0x1501aa3a2254022a 0x1fffaa7a23f4023f

def z1355 : W := mkw 0x1501aa3a2274922a 0x1fffbbfa23f79e3f

def z1356 : W := mkw 0x27848e90bf20f44f 0x07e00f803f00fc0f

def z1357 : W := mkw 0x0523fff7bb20900a 0x001bffffff000000

def z1358 : W := mkw 0x002373f7bb000000 0x001bf3ffff000000

def z1359 : W := mkw 0x0012dd0000aac800 0x0003d58000fb6c00

def z1360 : W := mkw 0x0033ff7732eed800 0x001fffffc0fffc00

def z1361 : W := mkw 0xa606cc5c34b8e34c 0xe65fee7c3cfcf3cc

def z1362 : W := mkw 0x1501ba3a2276922a 0x1fffba7a23f7923f

def z1363 : W := mkw 0x002000f7bb000000 0x1fe8007fff00023f

def z1364 : W := mkw 0x0003ee0000ecd000 0x0017ff8000fffc00

def z1365 : W := mkw 0xfa88000844df27f5 0xffe4000000ff03ff

def z1366 : W := mkw 0x0113ff0002eed802 0x01b7ff8003fffc03

def z1367 : W := mkw 0x1501bb3a2274922a 0x1fffbbfa23f4923f

def z1368 : W := mkw 0x0513ff0000eed80a 0x07f7ff8000fffc0f

def z1369 : W := mkw 0x1511aa3a2274da2a 0x1fffaa7a23f4fe3f

def z1370 : W := mkw 0x0023fff7bb000000 0x001bffffff00fc00

def z1371 : W := mkw 0x0423fff7bb208008 0x065bffffff00800c

def z1372 : W := mkw 0x0022dfd5bb000000 0x001bdffdff000000

def z1373 : W := mkw 0xd80b706f40df03b0 0xe003807dc0f001c0

def z1374 : W := mkw 0xa606cc5c34b8e34c 0xe65ffc7c3cffe3cc

def z1375 : W := mkw 0x0023fff7bb8a0000 0x001bffffff0b0000

def z1376 : W := mkw 0xa606cc5c34b8e34c 0xe01bcc7c3cf861c0

def z1377 : W := mkw 0xd80a404c40df03b0 0xf81ff07fc0ff03f0

def z1378 : W := mkw 0x1501ae3a3274922a 0x1fffae7a3ff4923f

def z1379 : W := mkw 0x0023fff7bb000000 0x19bbffffff041033

def z1380 : W := mkw 0xd80b706f40df03b0 0xf81ffc7ffcff03f0

def z1381 : W := mkw 0xd80b706f405503b0 0xf81ff07fc0f403f0

def z1382 : W := mkw 0x0023fff7bb209000 0x001bffffff009000

def z1383 : W := mkw 0x0000000000649000 0x00147f8000fffc00

def z1384 : W := mkw 0x0023fff7bb000000 0x0003dffdff000000

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkA : List (List (List (ℕ × List W))) :=
  [[[(0,[z0,z1,z2,z3,z4,z5,z6]),(0,[z0,z1,z7,z2,z4,z5,z6]),(0,[z0,z1,z2,z8,z4,z5,z6])],[(0,[z9,z0,z1,z2,z4,z5,z6])],[(0,[z0,z10,z2,z4,z5,z11,z6]),(0,[z0,z10,z12,z2,z4,z5,z6]),(0,[z13,z14,z1,z2,z4,z5,z6])],[(0,[z0,z1,z2,z15,z4,z5,z6]),(0,[z0,z16,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z17,z4,z5,z6]),(0,[z18,z0,z1,z2,z4,z5,z6])],[(0,[z19,z20,z1,z2,z4,z5,z6]),(0,[z0,z1,z21,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z22])],[],[(0,[z23,z0,z1,z2,z4,z5,z6]),(0,[z0,z10,z2,z24,z4,z5,z6]),(0,[z0,z1,z2,z4,z25,z26,z6]),(0,[z0,z1,z2,z27,z4,z5,z6]),(0,[z0,z1,z2,z28,z4,z5,z6]),(0,[z0,z1,z2,z29,z4,z5,z6])],[(0,[z0,z30,z2,z4,z5,z31,z6]),(0,[z32,z33,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z34,z6]),(0,[z0,z1,z2,z4,z35,z5,z6]),(1,[z36,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z37,z4,z5,z6]),(1,[z0,z1,z2,z38,z39,z4])]],
   [[(0,[z0,z1,z2,z40,z4,z5,z6]),(0,[z0,z10,z2,z41,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z42,z6]),(0,[z43,z0,z44,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z45]),(0,[z0,z1,z46,z2,z4,z5,z47]),(0,[z0,z1,z2,z39,z4,z5,z6])],[(1,[z0,z10,z2,z4,z5,z6]),(0,[z0,z30,z2,z3,z4,z5,z6]),(0,[z0,z1,z2,z48,z4,z5,z6]),(0,[z0,z1,z2,z49,z4,z5,z6]),(0,[z0,z1,z50,z2,z4,z5,z6]),(0,[z0,z1,z51,z2,z4,z5,z6]),(0,[z0,z2,z52,z4,z53,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z54]),(0,[z55,z0,z1,z2,z4,z5,z6])],[(0,[z56,z0,z10,z2,z4,z5,z6]),(0,[z33,z0,z1,z57,z4,z5,z6]),(0,[z0,z1,z2,z58,z4,z5,z6]),(0,[z0,z1,z2,z4,z59,z5,z6]),(0,[z0,z1,z2,z38,z4,z5,z47]),(0,[z0,z60,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z61,z5,z6])],[(0,[z0,z10,z1,z2,z4,z5,z6]),(0,[z62,z0,z30,z2,z4,z5,z6]),(0,[z63,z0,z10,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z64,z5,z6]),(1,[z33,z1,z2,z4,z5,z65]),(0,[z66,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z67,z5,z6]),(0,[z0,z1,z2,z68,z38,z4,z5])],[(0,[z43,z0,z30,z2,z4,z5,z6]),(0,[z0,z1,z69,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z70,z6]),(1,[z0,z1,z2,z4,z71,z6]),(0,[z0,z1,z72,z2,z4,z5,z6])],[(0,[z0,z0,z1,z2,z4,z5,z6]),(0,[z0,z73,z10,z2,z4,z5,z6]),(0,[z74,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z75,z6]),(0,[z0,z1,z2,z76,z4,z5,z6]),(1,[z0,z2,z4,z5,z6,z77])],[(0,[z78,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z79,z2,z4,z5,z6]),(0,[z0,z1,z2,z80,z4,z5,z81]),(0,[z0,z1,z2,z4,z82,z5,z6])],[(0,[z0,z10,z83,z2,z4,z5,z6]),(0,[z19,z0,z1,z2,z4,z84,z6]),(0,[z0,z1,z85,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z86,z5,z6])]],
   [[(0,[z63,z1,z2,z4,z5,z6,z87]),(0,[z0,z1,z88,z2,z4,z5,z6]),(1,[z0,z2,z4,z89,z5,z6]),(0,[z0,z2,z4,z5,z6,z77,z90])],[(0,[z0,z30,z2,z39,z4,z5,z6]),(0,[z0,z1,z2,z4,z91,z5,z6]),(0,[z32,z0,z1,z2,z4,z5,z65]),(1,[z0,z92,z2,z4,z5,z6])],[(0,[z63,z1,z2,z93,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z94]),(0,[z0,z1,z95,z2,z4,z5,z6]),(0,[z0,z2,z4,z53,z5,z96,z6]),(0,[z97,z1,z2,z4,z98,z5,z6]),(0,[z0,z1,z2,z99,z4,z25,z6]),(0,[z0,z1,z2,z100,z4,z5,z6])],[(1,[z0,z101,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z102,z5,z6]),(0,[z0,z1,z2,z4,z103,z5,z6]),(0,[z0,z1,z2,z104,z4,z98,z5]),(0,[z0,z105,z1,z2,z4,z5,z6]),(0,[z1,z2,z4,z5,z6,z106,z90])],[(0,[z0,z1,z2,z4,z5,z107,z6]),(0,[z108,z0,z1,z2,z4,z5,z6]),(0,[z109,z0,z1,z2,z4,z5,z6]),(0,[z0,z2,z52,z4,z110,z5,z6]),(0,[z111,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z112,z4,z25,z6])],[(0,[z0,z113,z30,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z114]),(0,[z33,z0,z10,z2,z4,z5,z6]),(0,[z0,z10,z115,z2,z4,z5,z6]),(0,[z0,z1,z2,z116,z4,z5,z6]),(0,[z0,z1,z117,z2,z4,z5,z6]),(0,[z0,z1,z83,z2,z112,z4,z6]),(0,[z0,z1,z2,z118,z4,z5,z6]),(0,[z0,z1,z46,z2,z68,z4,z5]),(0,[z0,z1,z4,z5,z47,z6,z119]),(0,[z0,z1,z2,z4,z5,z6,z120])],[(0,[z0,z121,z30,z2,z4,z5,z6]),(0,[z122,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z123,z4,z5,z6]),(0,[z0,z1,z2,z39,z4,z124,z6])],[(1,[z0,z125,z2,z4,z5,z6]),(0,[z0,z1,z12,z2,z4,z126,z6]),(1,[z0,z2,z4,z5,z6,z127]),(1,[z0,z1,z2,z68,z128,z5])]],
   [[(0,[z129,z0,z10,z2,z4,z5,z6]),(0,[z43,z0,z2,z24,z4,z5,z6]),(0,[z0,z1,z130,z2,z4,z5,z6]),(0,[z0,z1,z2,z131,z4,z128,z5])],[(0,[z0,z30,z88,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z132,z5,z6]),(0,[z0,z1,z41,z4,z124,z5,z6]),(0,[z0,z1,z2,z133,z4,z5,z6]),(0,[z0,z1,z2,z134,z4,z5,z6]),(0,[z0,z135,z1,z2,z110,z5,z6]),(0,[z136,z0,z1,z2,z4,z137,z6]),(0,[z0,z1,z2,z4,z5,z6,z138]),(0,[z0,z1,z139,z2,z4,z5,z6])],[(0,[z0,z10,z2,z4,z5,z6,z90]),(0,[z0,z140,z1,z2,z4,z5,z6]),(0,[z141,z0,z1,z2,z4,z5,z6])],[(0,[z0,z1,z142,z2,z4,z5,z6]),(0,[z0,z143,z1,z2,z4,z5,z6]),(0,[z144,z0,z1,z2,z4,z5,z6]),(0,[z13,z0,z2,z52,z4,z5,z6]),(0,[z0,z1,z2,z4,z145,z5,z6])],[(1,[z0,z1,z2,z4,z146,z6]),(0,[z0,z1,z147,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z148,z5,z6]),(0,[z149,z0,z1,z2,z4,z5,z6]),(1,[z0,z1,z2,z150,z4,z6]),(0,[z151,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z152,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z153,z5,z6])],[(0,[z1,z30,z2,z41,z4,z5,z6]),(0,[z0,z1,z154,z2,z4,z5,z6]),(0,[z155,z1,z2,z4,z26,z5,z6]),(0,[z0,z1,z2,z4,z128,z5,z65]),(0,[z156,z0,z135,z2,z4,z5,z6]),(0,[z43,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z157,z6])],[(0,[z0,z30,z2,z4,z5,z6,z114]),(0,[z0,z1,z2,z158,z4,z5,z6]),(0,[z1,z2,z4,z159,z98,z5,z6])],[(0,[z0,z1,z2,z4,z160,z5,z6]),(0,[z129,z1,z2,z93,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z161]),(0,[z0,z1,z2,z162,z4,z5,z6]),(0,[z0,z1,z2,z163,z4,z5,z6]),(0,[z0,z1,z2,z38,z39,z4,z6])]],
   [[(0,[z164,z0,z1,z2,z4,z5,z6]),(0,[z43,z0,z1,z2,z4,z165,z6])],[(0,[z0,z1,z2,z4,z166,z5,z6]),(1,[z0,z1,z2,z4,z167,z6]),(0,[z168,z19,z1,z2,z4,z5,z6]),(0,[z0,z169,z1,z2,z4,z5,z6]),(0,[z0,z170,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z171,z4,z5,z6])],[(0,[z129,z0,z101,z2,z4,z5,z6]),(0,[z32,z0,z16,z2,z4,z5,z6]),(0,[z172,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z99,z39,z4,z6]),(1,[z0,z1,z2,z4,z165,z173])],[(0,[z0,z1,z46,z41,z4,z5,z6]),(0,[z168,z0,z1,z2,z4,z5,z174]),(1,[z0,z1,z2,z4,z175,z6]),(0,[z0,z1,z2,z176,z4,z5,z6]),(0,[z0,z1,z177,z2,z4,z5,z6]),(0,[z0,z1,z2,z178,z4,z5,z6]),(0,[z0,z179,z1,z2,z4,z5,z6])],[(0,[z0,z30,z2,z4,z5,z6,z87]),(0,[z0,z10,z2,z4,z5,z65,z6]),(0,[z0,z1,z2,z180,z4,z5,z6]),(0,[z0,z44,z135,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z181,z5,z6]),(0,[z0,z1,z182,z2,z4,z5,z6])],[(0,[z0,z30,z2,z52,z4,z5,z6]),(0,[z183,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z2,z4,z5,z6]),(0,[z0,z1,z125,z2,z4,z5,z6]),(1,[z0,z184,z2,z4,z5,z6]),(0,[z0,z1,z2,z185,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z186]),(0,[z0,z1,z2,z4,z5,z187,z6]),(0,[z0,z1,z2,z131,z4,z5,z6])],[(0,[z0,z30,z2,z93,z4,z5,z6]),(0,[z0,z1,z188,z2,z4,z5,z6]),(0,[z0,z88,z2,z52,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z119])],[(0,[z0,z1,z2,z189,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z190]),(0,[z43,z0,z115,z2,z4,z5,z6]),(0,[z0,z1,z2,z191,z4,z5,z6]),(0,[z0,z1,z2,z38,z4,z5,z173])]],
   [[(0,[z0,z10,z2,z4,z98,z5,z6]),(0,[z0,z1,z2,z192,z4,z5,z6]),(0,[z13,z0,z2,z4,z5,z6,z193]),(0,[z0,z1,z83,z2,z99,z4,z6]),(0,[z0,z1,z2,z4,z126,z5,z6]),(1,[z194,z1,z2,z4,z5,z6])],[(1,[z136,z0,z1,z98,z5,z6]),(0,[z0,z1,z195,z2,z4,z5,z6])],[(0,[z0,z30,z2,z171,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z196]),(0,[z0,z2,z24,z4,z5,z96,z6])],[(0,[z0,z197,z10,z2,z4,z5,z6]),(0,[z0,z1,z198,z2,z4,z5,z6])],[(0,[z0,z10,z2,z4,z5,z6,z199]),(1,[z0,z1,z200,z4,z5,z6]),(0,[z0,z115,z1,z2,z4,z53,z6]),(1,[z201,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z202,z4,z5,z6])],[(1,[z0,z1,z2,z4,z5,z161]),(0,[z0,z1,z203,z2,z4,z5,z6]),(0,[z0,z1,z2,z204,z4,z5,z6]),(0,[z0,z1,z2,z4,z205,z5,z6])],[(0,[z206,z0,z1,z2,z4,z5,z6]),(0,[z20,z0,z10,z2,z4,z5,z6]),(0,[z0,z1,z12,z2,z4,z5,z87]),(0,[z207,z0,z1,z2,z4,z5,z6]),(1,[z208,z0,z2,z4,z5,z6]),(1,[z0,z1,z2,z209,z4,z6]),(0,[z0,z1,z2,z4,z210,z5,z6]),(0,[z211,z0,z1,z2,z4,z5,z6])],[(0,[z212,z0,z1,z2,z4,z5,z6]),(0,[z0,z30,z2,z4,z5,z6,z119]),(0,[z0,z1,z213,z4,z98,z5,z6]),(0,[z33,z0,z1,z2,z4,z175,z6]),(0,[z0,z1,z2,z214,z4,z5,z6]),(0,[z13,z0,z44,z2,z4,z5,z6]),(0,[z156,z0,z88,z2,z4,z5,z6]),(0,[z136,z0,z1,z2,z4,z215,z6]),(0,[z0,z1,z2,z4,z216,z5,z6]),(0,[z217,z0,z1,z2,z4,z5,z6])]],
   [[(0,[z0,z10,z2,z218,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z219,z6]),(1,[z0,z220,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z221,z5,z6]),(0,[z0,z1,z2,z4,z222,z5,z6]),(0,[z223,z0,z1,z2,z4,z5,z6]),(0,[z0,z224,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z225])],[(0,[z136,z0,z30,z2,z4,z5,z6]),(0,[z0,z1,z2,z226,z4,z5,z6]),(0,[z32,z0,z10,z2,z4,z5,z6]),(0,[z168,z0,z227,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z228,z5,z6]),(0,[z33,z0,z184,z2,z4,z5,z6]),(0,[z43,z169,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z229,z4,z5,z6]),(0,[z136,z0,z1,z2,z171,z5,z6])],[(0,[z0,z30,z2,z4,z5,z47,z6])],[(0,[z33,z1,z30,z2,z4,z5,z6]),(0,[z13,z0,z30,z2,z4,z5,z6]),(0,[z230,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z96,z6]),(0,[z0,z1,z2,z231,z4,z5,z6]),(0,[z0,z1,z2,z232,z4,z5,z6])],[(0,[z233,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z234,z6]),(0,[z0,z235,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z236,z4,z5,z6]),(1,[z0,z1,z237,z171,z5,z6])],[(0,[z0,z1,z2,z4,z238,z5,z6]),(0,[z19,z0,z239,z2,z4,z5,z6]),(1,[z0,z240,z2,z4,z5,z6]),(0,[z33,z0,z1,z2,z4,z5,z87]),(1,[z0,z1,z2,z241,z4,z5]),(0,[z0,z1,z2,z4,z165,z5,z6])],[(0,[z32,z1,z2,z4,z5,z6,z87]),(0,[z0,z1,z2,z4,z242,z5,z6]),(0,[z0,z44,z88,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z243,z5,z6]),(1,[z0,z1,z2,z104,z4,z5]),(0,[z0,z1,z2,z4,z128,z5,z47]),(0,[z0,z1,z2,z4,z5,z6,z81])],[(0,[z63,z1,z2,z41,z4,z5,z6]),(0,[z0,z1,z213,z237,z4,z5,z6]),(0,[z244,z0,z1,z2,z4,z5,z6])]],
   [[(0,[z32,z1,z2,z93,z4,z5,z6]),(1,[z245,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z246]),(0,[z0,z1,z2,z4,z5,z6,z247]),(1,[z14,z1,z2,z4,z5,z6]),(1,[z172,z1,z2,z4,z5,z6])],[(0,[z0,z1,z248,z2,z4,z5,z6]),(1,[z0,z21,z2,z4,z5,z6]),(0,[z0,z1,z2,z249,z4,z5,z6]),(0,[z0,z250,z1,z2,z4,z5,z6]),(1,[z0,z1,z2,z4,z103,z6]),(0,[z0,z1,z2,z4,z103,z6,z193]),(0,[z0,z1,z12,z2,z4,z5,z119])],[(0,[z0,z1,z2,z251,z4,z5,z6]),(0,[z0,z1,z83,z2,z4,z84,z6]),(0,[z0,z1,z252,z4,z124,z5,z6]),(0,[z0,z1,z2,z253,z4,z5,z6])],[(0,[z254,z0,z10,z2,z4,z5,z6]),(0,[z255,z0,z1,z2,z4,z5,z6])],[(0,[z155,z0,z30,z2,z4,z5,z6]),(0,[z0,z30,z2,z4,z5,z256,z6]),(0,[z0,z30,z2,z4,z5,z96,z6]),(0,[z0,z1,z2,z4,z257,z5,z6]),(1,[z0,z1,z2,z4,z42,z6]),(0,[z136,z0,z1,z4,z98,z5,z6]),(0,[z0,z1,z2,z4,z5,z119,z90]),(1,[z1,z258,z2,z4,z5,z6]),(0,[z0,z1,z2,z259,z4,z5,z6])],[(0,[z0,z10,z260,z2,z4,z5,z6]),(0,[z0,z1,z252,z2,z4,z26,z6]),(0,[z0,z1,z2,z4,z261,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z262]),(0,[z0,z92,z12,z2,z4,z5,z6])],[(0,[z0,z30,z2,z4,z165,z5,z6]),(0,[z168,z0,z10,z2,z4,z5,z6]),(0,[z0,z263,z1,z2,z4,z5,z6]),(0,[z264,z0,z1,z2,z4,z5,z6]),(1,[z13,z0,z2,z4,z5,z193]),(0,[z0,z1,z2,z265,z4,z5,z6])],[(0,[z13,z0,z2,z24,z4,z5,z6]),(1,[z1,z2,z4,z5,z6,z266])]],
   [[(1,[z0,z1,z2,z4,z5,z267]),(0,[z0,z1,z2,z4,z5,z268,z6])],[(0,[z0,z1,z113,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z31,z6]),(0,[z1,z2,z41,z4,z5,z65,z6]),(0,[z0,z1,z269,z2,z4,z5,z6]),(1,[z0,z1,z57,z4,z5,z6]),(1,[z0,z115,z2,z4,z53,z6]),(1,[z0,z1,z2,z4,z5,z270]),(0,[z0,z1,z2,z39,z4,z11,z6]),(0,[z0,z1,z2,z128,z5,z6,z90])],[(0,[z0,z1,z271,z2,z4,z5,z6]),(0,[z1,z2,z93,z4,z272,z5,z6]),(0,[z0,z1,z2,z273,z4,z5,z6])],[(0,[z0,z274,z10,z2,z4,z5,z6]),(0,[z168,z1,z2,z4,z5,z65,z6]),(1,[z275,z1,z2,z93,z5,z6]),(0,[z0,z1,z2,z276,z4,z5,z6]),(1,[z0,z79,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z165,z124,z6]),(0,[z0,z1,z2,z277,z4,z5,z6]),(1,[z0,z1,z2,z4,z5,z278])],[(0,[z129,z1,z2,z41,z4,z5,z6]),(1,[z0,z85,z2,z4,z5,z6]),(0,[z279,z0,z1,z2,z4,z5,z6]),(0,[z13,z0,z1,z2,z4,z5,z6]),(0,[z13,z0,z1,z2,z4,z5,z193]),(0,[z0,z280,z1,z2,z4,z165,z5])],[(0,[z0,z30,z2,z4,z5,z11,z6]),(0,[z0,z10,z2,z4,z25,z5,z6]),(0,[z1,z2,z93,z4,z26,z5,z6]),(0,[z281,z0,z2,z52,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z282]),(0,[z0,z1,z237,z171,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z283,z6]),(0,[z201,z1,z2,z4,z5,z6,z81])],[(0,[z0,z10,z46,z2,z4,z5,z6]),(1,[z0,z284,z2,z4,z5,z6]),(0,[z0,z285,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z5,z6]),(0,[z0,z1,z2,z4,z5,z65,z90]),(0,[z0,z1,z2,z286,z4,z5,z6]),(0,[z136,z0,z1,z4,z5,z47,z6]),(0,[z0,z92,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z112,z99,z5,z6])],[(0,[z0,z1,z2,z4,z5,z287,z6]),(0,[z0,z1,z2,z4,z5,z288,z6]),(0,[z0,z1,z2,z289,z4,z5,z6])]],
   [[(0,[z0,z10,z2,z38,z4,z5,z6]),(0,[z20,z0,z290,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z84,z6,z81]),(0,[z33,z0,z1,z2,z4,z42,z6]),(0,[z0,z1,z2,z291,z4,z5,z6]),(1,[z0,z1,z4,z5,z6,z292])],[(0,[z0,z1,z2,z4,z5,z293,z6]),(0,[z0,z1,z237,z2,z4,z5,z6])],[(0,[z0,z294,z10,z2,z4,z5,z6]),(0,[z168,z32,z1,z2,z4,z5,z6]),(0,[z295,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z296,z6]),(0,[z0,z88,z2,z24,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z297])],[(0,[z0,z30,z2,z41,z4,z5,z6]),(0,[z275,z0,z10,z2,z4,z5,z6]),(0,[z0,z10,z2,z4,z5,z298,z6]),(0,[z0,z10,z2,z99,z4,z5,z6]),(1,[z299,z0,z2,z4,z5,z6]),(0,[z0,z1,z2,z300,z4,z5,z6]),(0,[z0,z1,z2,z301,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z302]),(0,[z303,z0,z1,z2,z4,z5,z6])],[(0,[z0,z10,z2,z4,z5,z304,z6]),(0,[z0,z10,z2,z4,z53,z5,z6]),(1,[z155,z1,z2,z4,z26,z6]),(1,[z0,z1,z2,z305,z4,z6]),(0,[z0,z1,z306,z2,z4,z5,z6])],[(0,[z0,z30,z307,z2,z4,z5,z6]),(0,[z0,z10,z2,z112,z4,z5,z6]),(0,[z0,z1,z2,z4,z308,z5,z6]),(0,[z155,z0,z1,z2,z4,z5,z6]),(0,[z14,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z309,z4,z5,z6]),(0,[z0,z1,z2,z4,z310,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z311])],[(0,[z312,z0,z30,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z313,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z314])],[(1,[z20,z30,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z315,z6]),(0,[z0,z1,z2,z4,z167,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z316]),(0,[z0,z1,z2,z4,z5,z6,z317]),(0,[z0,z1,z2,z4,z5,z318,z6]),(0,[z0,z1,z2,z4,z319,z5,z6])]],
   [[(0,[z19,z0,z30,z2,z4,z5,z6]),(1,[z20,z1,z213,z4,z5,z6]),(0,[z0,z1,z2,z4,z320,z5,z6]),(1,[z0,z135,z2,z52,z5,z6]),(0,[z0,z1,z2,z321,z4,z5,z6])],[(0,[z0,z1,z2,z4,z5,z6,z322]),(1,[z0,z1,z2,z4,z5,z323]),(0,[z0,z324,z1,z2,z4,z5,z6])],[(0,[z0,z30,z237,z2,z4,z5,z6]),(0,[z0,z30,z83,z2,z4,z5,z6]),(0,[z20,z0,z1,z2,z4,z5,z161]),(0,[z275,z1,z2,z93,z4,z5,z6]),(1,[z0,z154,z2,z4,z5,z6]),(0,[z156,z0,z2,z4,z5,z96,z6]),(0,[z136,z0,z325,z2,z4,z5,z6]),(0,[z326,z0,z1,z2,z4,z5,z6])],[(0,[z0,z135,z30,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z327,z5,z6])],[(0,[z0,z1,z284,z2,z4,z5,z6]),(0,[z0,z1,z328,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z47,z90]),(0,[z0,z329,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z330])],[(0,[z129,z0,z284,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z331,z5,z6]),(1,[z0,z1,z2,z4,z126,z6]),(0,[z0,z1,z2,z332,z4,z5,z6]),(0,[z0,z1,z2,z68,z4,z5,z90]),(0,[z0,z333,z1,z2,z4,z5,z6])],[(0,[z168,z0,z1,z2,z4,z167,z6]),(0,[z13,z0,z1,z2,z4,z5,z96]),(0,[z136,z170,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z104,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z334])],[(0,[z0,z10,z10,z2,z4,z5,z6]),(0,[z0,z10,z2,z4,z110,z5,z6]),(0,[z0,z1,z2,z4,z5,z335,z6]),(0,[z0,z36,z1,z2,z4,z5,z6]),(0,[z0,z280,z1,z2,z38,z4,z5])]],
   [[(0,[z0,z1,z2,z4,z5,z6,z336]),(0,[z1,z252,z337,z2,z4,z5,z6]),(0,[z208,z0,z2,z4,z5,z6,z81])],[(0,[z0,z0,z10,z2,z4,z5,z6]),(0,[z0,z1,z338,z2,z4,z5,z6]),(0,[z281,z0,z44,z2,z4,z5,z6]),(0,[z0,z44,z2,z4,z5,z96,z6]),(0,[z0,z1,z2,z4,z339,z5,z6]),(1,[z211,z0,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z340,z5,z6]),(0,[z0,z1,z341,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z342,z6]),(0,[z136,z0,z1,z46,z4,z5,z6]),(0,[z0,z1,z2,z4,z343,z5,z6]),(0,[z0,z1,z4,z5,z6,z344,z90]),(0,[z0,z1,z2,z4,z345,z5,z6])],[(0,[z0,z1,z2,z4,z346,z5,z6]),(0,[z347,z0,z1,z2,z4,z5,z6]),(0,[z43,z55,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z348,z4,z5,z6]),(0,[z0,z1,z349,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z350,z6])],[(0,[z168,z1,z30,z2,z4,z5,z6]),(0,[z351,z0,z1,z2,z4,z5,z6]),(0,[z0,z10,z280,z2,z4,z5,z6]),(0,[z352,z0,z1,z2,z4,z5,z6]),(0,[z0,z353,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z354,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z270,z6])],[(0,[z0,z30,z2,z4,z5,z6,z90]),(0,[z0,z10,z2,z4,z272,z5,z6]),(0,[z32,z1,z2,z41,z4,z5,z6]),(0,[z33,z1,z2,z4,z5,z65,z6]),(0,[z43,z0,z1,z2,z4,z304,z6]),(0,[z0,z1,z2,z355,z4,z5,z6])],[(0,[z0,z1,z2,z4,z5,z65,z6]),(0,[z0,z1,z2,z4,z5,z6,z87]),(1,[z1,z356,z2,z4,z5,z6]),(0,[z43,z0,z2,z4,z5,z304,z6]),(0,[z0,z1,z2,z241,z4,z5,z304]),(0,[z0,z1,z2,z4,z5,z6,z344])],[(0,[z312,z0,z1,z2,z4,z5,z6]),(1,[z0,z1,z2,z4,z5,z322]),(0,[z0,z135,z2,z24,z4,z5,z6]),(0,[z0,z1,z2,z52,z4,z5,z6])]],
   [[(0,[z0,z10,z2,z4,z26,z5,z6]),(0,[z0,z1,z2,z93,z4,z5,z6]),(0,[z0,z1,z2,z68,z4,z128,z5])],[(0,[z357,z0,z1,z2,z4,z5,z6]),(0,[z19,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z358,z5,z304])],[(0,[z359,z0,z1,z2,z4,z5,z6]),(0,[z63,z20,z1,z2,z4,z5,z6]),(0,[z360,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z361,z5,z6]),(0,[z0,z1,z2,z4,z98,z5,z6])],[],[(0,[z0,z1,z252,z2,z4,z84,z6]),(0,[z0,z135,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z362,z5,z6]),(0,[z0,z280,z2,z4,z5,z96,z6]),(1,[z363,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z278,z81]),(0,[z364,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z38,z39,z4,z5])],[(0,[z20,z0,z1,z2,z4,z5,z267]),(0,[z168,z0,z220,z2,z4,z5,z6]),(0,[z0,z1,z2,z365,z4,z5,z6]),(0,[z0,z2,z4,z53,z5,z304,z6])],[(0,[z0,z10,z2,z366,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z199]),(0,[z367,z0,z1,z2,z4,z5,z6])],[(0,[z0,z30,z2,z4,z5,z65,z6]),(0,[z0,z1,z2,z4,z5,z6,z368]),(0,[z1,z2,z4,z5,z6,z266,z81])]],
   [[(0,[z0,z1,z2,z4,z369,z5,z6])],[(0,[z43,z0,z10,z2,z4,z5,z6]),(1,[z168,z1,z2,z272,z5,z6]),(0,[z281,z0,z2,z24,z4,z5,z6])],[(0,[z155,z0,z1,z370,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z371]),(1,[z1,z2,z4,z159,z5,z6]),(0,[z0,z1,z2,z372,z4,z5,z6])],[(0,[z0,z30,z2,z4,z98,z5,z6]),(0,[z20,z275,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z373]),(0,[z0,z1,z2,z374,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z375]),(0,[z156,z13,z0,z2,z4,z5,z6])],[(0,[z0,z1,z376,z2,z4,z5,z6]),(0,[z32,z0,z85,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z193]),(0,[z0,z1,z2,z4,z5,z47,z6])],[(0,[z0,z1,z2,z4,z5,z377,z6]),(0,[z0,z1,z2,z4,z5,z6,z378]),(0,[z0,z1,z2,z68,z4,z5,z6]),(0,[z0,z1,z2,z131,z4,z165,z5]),(0,[z0,z379,z1,z2,z4,z5,z6])],[(0,[z0,z1,z2,z380,z4,z5,z6]),(0,[z281,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z381,z6]),(0,[z0,z1,z2,z4,z165,z11,z6])],[(0,[z0,z1,z2,z4,z382,z5,z6]),(0,[z0,z10,z2,z4,z124,z5,z6]),(0,[z129,z20,z1,z2,z4,z5,z6]),(0,[z0,z1,z383,z2,z4,z5,z6]),(0,[z0,z1,z384,z2,z4,z5,z6])]],
   [[(0,[z0,z1,z385,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z25,z84,z6]),(0,[z0,z2,z4,z5,z96,z6,z193]),(0,[z0,z1,z2,z4,z5,z386,z6])],[(1,[z387,z0,z2,z4,z5,z6])],[(0,[z254,z63,z1,z2,z4,z5,z6]),(0,[z0,z1,z46,z2,z4,z5,z87]),(0,[z156,z43,z0,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z388,z5,z6]),(0,[z0,z389,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z390,z5,z6]),(0,[z391,z0,z1,z2,z4,z5,z6]),(1,[z0,z1,z2,z80,z4,z5])],[(0,[z0,z2,z52,z4,z5,z96,z6]),(0,[z0,z1,z2,z241,z4,z5,z6]),(0,[z0,z1,z2,z392,z4,z5,z6]),(0,[z393,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z394,z2,z4,z5,z6]),(0,[z0,z1,z2,z395,z4,z5,z6]),(1,[z0,z396,z2,z4,z5,z6])],[(0,[z0,z397,z30,z2,z4,z5,z6]),(0,[z0,z10,z2,z4,z128,z5,z6]),(0,[z0,z1,z2,z4,z5,z398,z6]),(0,[z0,z399,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z38,z4,z5,z87]),(1,[z0,z1,z2,z4,z358,z5]),(0,[z211,z0,z2,z4,z5,z6,z173]),(0,[z0,z400,z1,z2,z4,z5,z6])],[(0,[z0,z30,z2,z4,z5,z6,z193]),(0,[z168,z63,z1,z2,z4,z5,z6]),(0,[z0,z10,z213,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z401,z6]),(0,[z0,z1,z2,z4,z5,z6,z402]),(0,[z0,z1,z2,z99,z4,z6,z81])],[(0,[z0,z30,z2,z68,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z256,z6]),(0,[z20,z1,z2,z4,z5,z65,z6]),(0,[z1,z213,z2,z93,z4,z5,z6]),(0,[z0,z1,z213,z4,z124,z5,z6]),(0,[z168,z0,z1,z403,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z404,z6]),(0,[z156,z281,z0,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z358,z5,z6]),(0,[z0,z280,z1,z2,z4,z5,z193]),(0,[z136,z0,z179,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z215,z6]),(1,[z405,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z406,z5,z6]),(0,[z0,z407,z1,z2,z4,z5,z6])],[(0,[z0,z1,z30,z2,z4,z5,z6]),(0,[z275,z1,z2,z41,z4,z5,z6]),(0,[z43,z0,z1,z2,z39,z4,z6]),(0,[z408,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z112,z4,z6,z81])]],
   [[],[(0,[z0,z1,z2,z4,z5,z6,z409]),(0,[z0,z1,z2,z410,z4,z5,z6]),(0,[z0,z1,z2,z4,z411,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z412]),(0,[z0,z1,z413,z2,z4,z5,z6]),(0,[z0,z1,z2,z414,z4,z5,z6])],[(0,[z0,z1,z415,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z416,z6]),(0,[z1,z2,z41,z4,z272,z5,z6]),(0,[z0,z1,z2,z4,z417,z5,z6]),(0,[z135,z1,z356,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z165,z5,z47])],[(0,[z0,z1,z418,z2,z4,z5,z6]),(0,[z0,z419,z1,z2,z4,z5,z6]),(0,[z168,z275,z1,z2,z4,z5,z6]),(0,[z275,z0,z21,z2,z4,z5,z6]),(0,[z281,z140,z1,z2,z4,z5,z6]),(0,[z0,z1,z237,z2,z171,z5,z6])],[(0,[z0,z10,z252,z2,z4,z5,z6]),(0,[z0,z1,z83,z213,z4,z5,z6]),(0,[z168,z1,z2,z4,z272,z5,z6])],[(0,[z1,z2,z41,z4,z26,z5,z6]),(0,[z136,z0,z1,z2,z4,z5,z420]),(0,[z0,z1,z46,z2,z4,z5,z119]),(0,[z0,z1,z2,z4,z5,z6,z421])],[],[(0,[z0,z1,z2,z4,z5,z6,z422]),(0,[z0,z1,z2,z4,z423,z5,z6]),(0,[z424,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z137,z5,z6]),(0,[z0,z1,z425,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z11,z6]),(0,[z0,z1,z12,z2,z4,z5,z6]),(0,[z0,z1,z2,z38,z4,z5,z119]),(1,[z0,z2,z4,z5,z6,z297])]],
   [[(0,[z0,z30,z30,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z426,z6]),(0,[z0,z1,z427,z2,z4,z5,z6]),(0,[z428,z0,z1,z2,z4,z5,z6])],[(0,[z0,z10,z135,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z175,z5,z6]),(0,[z0,z135,z1,z2,z52,z5,z6]),(0,[z0,z1,z396,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z429,z6])],[(0,[z430,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z83,z2,z4,z11,z6]),(0,[z0,z1,z252,z2,z112,z4,z6]),(0,[z0,z1,z2,z68,z128,z5,z6]),(0,[z0,z1,z2,z4,z431,z5,z6])],[(0,[z0,z1,z2,z24,z4,z5,z6]),(0,[z136,z0,z1,z2,z4,z5,z270]),(1,[z0,z1,z2,z99,z25,z6]),(0,[z0,z1,z2,z4,z432,z5,z6])],[(0,[z433,z0,z1,z2,z4,z5,z6]),(0,[z20,z0,z1,z2,z4,z146,z6]),(1,[z0,z1,z403,z4,z5,z6]),(0,[z0,z1,z2,z434,z4,z5,z6]),(0,[z405,z1,z252,z2,z4,z5,z6])],[(0,[z0,z1,z2,z41,z4,z5,z6]),(0,[z0,z1,z2,z4,z435,z5,z6]),(0,[z13,z0,z2,z4,z53,z5,z6]),(0,[z136,z0,z1,z2,z98,z5,z6]),(0,[z194,z1,z2,z4,z5,z6,z90])],[(0,[z0,z436,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z437,z4,z5,z6])],[(0,[z0,z1,z307,z2,z4,z5,z6]),(0,[z136,z0,z1,z237,z4,z5,z6]),(0,[z136,z0,z1,z83,z4,z5,z6]),(0,[z0,z1,z4,z124,z5,z11,z6]),(0,[z0,z1,z2,z80,z4,z5,z6])]],
   [[(0,[z0,z1,z1,z2,z4,z5,z6]),(0,[z0,z30,z12,z2,z4,z5,z6]),(0,[z0,z30,z2,z4,z25,z5,z6]),(1,[z0,z1,z2,z4,z331,z6]),(0,[z32,z20,z1,z2,z4,z5,z6]),(0,[z0,z1,z438,z2,z4,z5,z6]),(0,[z0,z280,z1,z2,z4,z5,z96]),(0,[z0,z1,z83,z171,z4,z5,z6])],[(0,[z0,z30,z46,z2,z4,z5,z6]),(0,[z0,z1,z2,z439,z4,z5,z6]),(0,[z0,z1,z2,z440,z4,z5,z6]),(0,[z441,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z442,z2,z4,z5,z6])],[(0,[z0,z1,z443,z2,z4,z5,z6])],[(0,[z19,z1,z2,z4,z5,z84,z6]),(0,[z1,z2,z4,z26,z5,z84,z6]),(0,[z155,z0,z1,z2,z4,z5,z426]),(0,[z444,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z445,z2,z4,z5,z6])],[(0,[z0,z30,z2,z24,z4,z5,z6]),(1,[z63,z10,z2,z4,z5,z6]),(0,[z446,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z267,z6]),(0,[z0,z1,z2,z447,z4,z5,z6]),(0,[z448,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z449,z4,z5,z6]),(0,[z0,z1,z83,z2,z4,z5,z6]),(1,[z1,z337,z2,z4,z5,z6]),(0,[z0,z1,z258,z2,z4,z5,z6]),(0,[z0,z1,z2,z450,z4,z5,z6])],[(0,[z0,z1,z2,z4,z5,z451,z6]),(1,[z0,z44,z88,z4,z5,z6]),(0,[z299,z0,z2,z4,z98,z5,z6]),(0,[z0,z1,z252,z2,z4,z5,z323]),(0,[z0,z1,z452,z2,z4,z5,z6]),(0,[z0,z1,z2,z453,z4,z5,z6])],[(0,[z0,z1,z2,z454,z4,z5,z6]),(0,[z0,z30,z2,z99,z4,z5,z6]),(0,[z136,z0,z10,z2,z4,z5,z6]),(0,[z168,z0,z1,z2,z4,z5,z455]),(0,[z0,z1,z2,z4,z5,z6,z455])],[(0,[z20,z1,z30,z2,z4,z5,z6]),(0,[z0,z30,z2,z4,z5,z304,z6]),(0,[z0,z30,z2,z4,z53,z5,z6]),(0,[z0,z1,z2,z39,z4,z26,z6]),(0,[z0,z1,z57,z2,z4,z5,z6]),(0,[z0,z1,z456,z2,z4,z5,z6]),(1,[z0,z1,z46,z4,z5,z119]),(0,[z0,z1,z2,z4,z5,z6,z266])]],
   [[(0,[z0,z30,z2,z112,z4,z5,z6]),(0,[z13,z0,z10,z2,z4,z5,z6]),(0,[z0,z227,z1,z2,z4,z5,z6]),(0,[z0,z457,z1,z2,z4,z5,z6]),(0,[z458,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z459,z5,z6]),(0,[z387,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z39,z4,z6,z173])],[(1,[z0,z239,z2,z4,z5,z6]),(0,[z155,z0,z1,z2,z4,z26,z6]),(0,[z0,z1,z2,z460,z4,z5,z6])],[(0,[z461,z0,z1,z2,z4,z5,z6]),(0,[z462,z0,z1,z2,z4,z5,z6]),(0,[z463,z0,z1,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z5,z464,z6]),(0,[z0,z10,z88,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z465,z5,z6]),(0,[z0,z44,z1,z88,z4,z5,z6]),(0,[z466,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z39,z4,z165,z5])],[(0,[z0,z10,z2,z4,z5,z6,z173]),(0,[z0,z1,z2,z200,z4,z5,z6]),(0,[z32,z0,z1,z2,z4,z5,z87]),(1,[z0,z1,z2,z4,z137,z6]),(0,[z172,z1,z12,z2,z4,z5,z6]),(1,[z1,z2,z4,z5,z6,z106])],[(0,[z0,z1,z2,z4,z5,z467,z6]),(0,[z13,z0,z280,z2,z4,z5,z6]),(0,[z0,z1,z83,z252,z4,z5,z6]),(0,[z0,z1,z252,z2,z99,z4,z6]),(0,[z0,z1,z468,z2,z4,z5,z6])],[(0,[z156,z0,z30,z2,z4,z5,z6]),(0,[z0,z1,z121,z2,z4,z5,z6]),(0,[z281,z0,z1,z88,z4,z5,z6]),(0,[z0,z1,z2,z4,z469,z5,z6]),(0,[z0,z1,z2,z4,z470,z5,z6])],[(0,[z0,z1,z2,z4,z471,z5,z6]),(0,[z0,z1,z2,z4,z5,z174,z6]),(0,[z0,z1,z2,z4,z272,z5,z6]),(0,[z43,z0,z1,z2,z4,z53,z6]),(0,[z0,z1,z2,z4,z5,z6,z90]),(0,[z0,z1,z2,z4,z165,z5,z173]),(0,[z0,z1,z2,z4,z472,z5,z6])]],
   [[(0,[z0,z1,z325,z2,z4,z5,z6]),(0,[z405,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z473,z4,z5,z6]),(0,[z0,z1,z474,z2,z4,z5,z6])],[(0,[z155,z0,z10,z2,z4,z5,z6]),(0,[z0,z1,z41,z4,z5,z47,z6]),(0,[z0,z1,z2,z4,z5,z6,z475]),(0,[z0,z1,z2,z4,z124,z6,z81])],[(0,[z476,z0,z1,z2,z4,z5,z6]),(0,[z477,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z478,z5,z6]),(0,[z0,z1,z83,z2,z4,z124,z6]),(0,[z0,z1,z2,z4,z5,z278,z6])],[(0,[z1,z213,z2,z41,z4,z5,z6])],[(0,[z254,z1,z30,z2,z4,z5,z6]),(0,[z0,z1,z479,z2,z4,z5,z6]),(1,[z0,z1,z2,z4,z5,z455]),(0,[z0,z1,z2,z4,z480,z5,z6]),(0,[z0,z481,z1,z2,z4,z5,z6]),(0,[z0,z1,z482,z2,z4,z5,z6]),(0,[z0,z1,z2,z483,z4,z5,z6])],[(0,[z0,z44,z30,z2,z4,z5,z6]),(0,[z0,z1,z2,z484,z4,z5,z6]),(0,[z0,z1,z2,z131,z5,z6,z90])],[(0,[z0,z485,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z486,z5,z6])],[(0,[z156,z0,z1,z2,z110,z5,z6]),(0,[z0,z1,z487,z2,z4,z5,z6]),(0,[z0,z488,z1,z2,z4,z5,z6]),(0,[z387,z0,z2,z4,z5,z6,z90])]],
   [[(0,[z0,z30,z2,z4,z272,z5,z6]),(0,[z281,z0,z30,z2,z4,z5,z6]),(0,[z489,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z128,z5,z87]),(0,[z0,z389,z252,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z71,z5,z6])],[(0,[z490,z0,z1,z2,z4,z5,z6]),(0,[z0,z115,z30,z2,z4,z5,z6]),(0,[z281,z491,z1,z2,z4,z5,z6])],[(0,[z0,z1,z2,z492,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z493,z6]),(0,[z0,z1,z2,z4,z494,z5,z6])],[(0,[z0,z30,z2,z4,z26,z5,z6]),(0,[z0,z1,z495,z2,z4,z5,z6]),(0,[z0,z1,z83,z4,z5,z11,z6]),(0,[z0,z1,z2,z4,z5,z6,z496])],[(0,[z0,z1,z2,z4,z165,z5,z65]),(0,[z497,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z498,z4,z5,z6])],[(0,[z499,z0,z1,z2,z4,z5,z6]),(0,[z19,z0,z1,z2,z4,z26,z6]),(0,[z500,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z12,z2,z131,z4,z5]),(0,[z0,z1,z2,z4,z5,z6,z501])],[(0,[z63,z1,z2,z4,z5,z84,z6]),(0,[z0,z1,z502,z4,z5,z6,z81])],[(0,[z155,z0,z125,z2,z4,z5,z6]),(0,[z156,z0,z1,z2,z4,z5,z6])]],
   [[(0,[z0,z280,z30,z2,z4,z5,z6]),(0,[z351,z0,z10,z2,z4,z5,z6]),(0,[z0,z10,z2,z131,z4,z5,z6]),(0,[z0,z1,z370,z2,z4,z5,z6]),(0,[z245,z0,z1,z2,z4,z5,z6])],[(0,[z0,z1,z237,z41,z4,z5,z6]),(0,[z0,z1,z83,z41,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z503]),(0,[z0,z1,z2,z4,z504,z5,z6]),(0,[z0,z1,z2,z4,z124,z5,z6])],[(0,[z505,z0,z1,z2,z4,z5,z6]),(1,[z0,z389,z2,z4,z5,z6]),(0,[z0,z1,z506,z2,z4,z5,z6]),(0,[z0,z1,z252,z2,z4,z5,z496]),(0,[z0,z1,z2,z4,z5,z6,z507]),(0,[z208,z0,z1,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z5,z6,z508]),(0,[z509,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z510,z5,z6]),(0,[z0,z1,z2,z4,z128,z5,z119]),(0,[z0,z1,z2,z511,z4,z5,z6]),(1,[z0,z1,z502,z4,z5,z6])],[(1,[z0,z30,z2,z4,z5,z6]),(0,[z19,z155,z1,z2,z4,z5,z6]),(0,[z0,z512,z1,z2,z4,z5,z6])],[(1,[z30,z2,z4,z5,z84,z6]),(0,[z19,z0,z10,z2,z4,z5,z6]),(0,[z0,z1,z2,z218,z4,z5,z6]),(0,[z20,z0,z1,z2,z4,z331,z6]),(0,[z168,z0,z1,z2,z272,z5,z6]),(1,[z491,z1,z2,z4,z5,z6]),(0,[z513,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z514,z2,z4,z5,z6]),(0,[z363,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z231,z4,z98,z5]),(0,[z0,z1,z515,z2,z4,z5,z6])],[(0,[z63,z0,z30,z2,z4,z5,z6]),(0,[z0,z1,z2,z516,z4,z5,z6]),(0,[z0,z44,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z517]),(0,[z0,z1,z356,z2,z4,z5,z6]),(0,[z0,z1,z2,z99,z25,z5,z6])],[(0,[z0,z1,z2,z4,z518,z5,z6]),(0,[z519,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z520,z5,z6]),(0,[z20,z1,z2,z4,z272,z5,z6]),(0,[z168,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z6]),(0,[z0,z1,z171,z4,z98,z5,z6]),(0,[z0,z1,z2,z150,z4,z5,z6])]],
   [[(0,[z0,z1,z2,z4,z5,z87,z90]),(0,[z0,z1,z2,z4,z5,z6,z292]),(0,[z0,z1,z2,z4,z5,z6,z521])],[(1,[z0,z1,z134,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z522]),(0,[z0,z1,z2,z4,z5,z523,z6]),(1,[z0,z1,z2,z4,z5,z496]),(0,[z0,z1,z2,z4,z524,z5,z6])],[(0,[z0,z30,z2,z4,z124,z5,z6]),(0,[z20,z1,z2,z4,z26,z5,z6]),(0,[z0,z115,z1,z2,z4,z5,z6]),(0,[z525,z0,z1,z2,z4,z5,z6]),(0,[z0,z2,z4,z89,z98,z5,z6]),(0,[z0,z1,z2,z4,z526,z5,z6])],[(1,[z0,z143,z2,z4,z5,z6]),(0,[z0,z1,z46,z213,z4,z5,z6]),(0,[z527,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z528]),(0,[z0,z1,z2,z529,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z530]),(0,[z531,z0,z1,z2,z4,z5,z6]),(0,[z299,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z532,z5,z6]),(1,[z0,z1,z4,z5,z6,z344]),(0,[z533,z0,z1,z2,z4,z5,z6])],[(0,[z19,z1,z2,z93,z4,z5,z6])],[(0,[z534,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z535]),(0,[z0,z115,z1,z2,z4,z165,z6]),(0,[z0,z1,z2,z4,z5,z536,z6]),(0,[z0,z1,z2,z4,z537,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z538])],[(0,[z0,z10,z2,z4,z5,z96,z6]),(0,[z0,z1,z2,z39,z4,z84,z6]),(0,[z0,z1,z2,z4,z539,z5,z6]),(0,[z540,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z541,z4,z5,z6]),(0,[z0,z1,z252,z2,z4,z5,z6])],[(0,[z542,z0,z30,z2,z4,z5,z6]),(0,[z0,z30,z2,z4,z128,z5,z6]),(0,[z543,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z544,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z545,z6])]],
   [[(0,[z0,z30,z213,z2,z4,z5,z6]),(0,[z33,z0,z30,z2,z4,z5,z6]),(0,[z0,z30,z2,z4,z518,z5,z6]),(0,[z0,z1,z2,z4,z546,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z547]),(0,[z1,z2,z4,z5,z65,z6,z87]),(0,[z0,z1,z548,z2,z4,z5,z6]),(0,[z0,z1,z2,z549,z4,z5,z6]),(0,[z0,z252,z79,z2,z4,z5,z6])],[(0,[z0,z10,z2,z4,z5,z6,z81]),(0,[z0,z280,z1,z2,z4,z5,z6]),(0,[z0,z1,z171,z4,z5,z47,z6]),(0,[z0,z12,z396,z2,z4,z5,z6])],[(0,[z0,z10,z2,z4,z5,z84,z6]),(0,[z0,z1,z260,z2,z4,z5,z6]),(0,[z281,z0,z10,z2,z4,z5,z6]),(0,[z275,z0,z1,z2,z272,z5,z6]),(0,[z0,z1,z2,z4,z550,z5,z6]),(0,[z0,z1,z2,z4,z159,z5,z6]),(0,[z0,z1,z2,z4,z551,z5,z6]),(0,[z0,z1,z2,z552,z4,z5,z6]),(0,[z0,z2,z4,z5,z6,z127,z81]),(0,[z0,z1,z2,z553,z4,z5,z6])],[(0,[z129,z0,z30,z2,z4,z5,z6]),(0,[z554,z0,z30,z2,z4,z5,z6]),(0,[z0,z101,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z555,z6])],[(0,[z129,z0,z1,z213,z4,z5,z6]),(0,[z275,z0,z1,z2,z4,z5,z6]),(0,[z155,z0,z1,z200,z4,z5,z6]),(0,[z0,z1,z2,z4,z165,z26,z6]),(0,[z0,z1,z556,z2,z4,z5,z6]),(0,[z0,z1,z557,z2,z4,z5,z6]),(0,[z0,z1,z4,z5,z6,z292,z81])],[(1,[z0,z1,z2,z4,z5,z6]),(0,[z63,z10,z1,z2,z4,z5,z6]),(0,[z33,z0,z1,z134,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z558]),(0,[z97,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z165,z6,z173])],[(0,[z56,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z559,z4,z5,z6]),(0,[z0,z1,z2,z4,z560,z5,z6]),(0,[z0,z1,z2,z561,z4,z5,z6])],[(0,[z63,z0,z1,z2,z4,z5,z6]),(0,[z0,z30,z252,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z562,z6]),(0,[z0,z1,z46,z171,z4,z5,z6])]],
   [[(0,[z563,z0,z1,z2,z4,z5,z6]),(0,[z0,z2,z24,z4,z53,z5,z6])],[(0,[z0,z73,z1,z2,z4,z5,z6]),(0,[z564,z0,z1,z2,z4,z5,z6])],[(0,[z168,z1,z2,z4,z26,z5,z6]),(0,[z0,z1,z2,z565,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z566]),(0,[z0,z1,z2,z4,z25,z5,z6])],[(0,[z233,z0,z10,z2,z4,z5,z6]),(0,[z0,z1,z2,z567,z4,z5,z6]),(0,[z0,z1,z2,z4,z568,z5,z6]),(0,[z569,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z570,z4,z5,z6]),(0,[z0,z1,z46,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z571,z6]),(0,[z0,z1,z572,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z573,z5,z6]),(0,[z0,z1,z2,z4,z5,z574,z6]),(1,[z32,z1,z2,z4,z5,z87]),(0,[z156,z0,z1,z2,z52,z5,z6]),(0,[z0,z575,z1,z2,z4,z5,z6]),(0,[z0,z1,z252,z2,z4,z124,z6]),(0,[z0,z1,z46,z4,z5,z6,z119]),(0,[z0,z1,z12,z2,z4,z5,z47])],[(1,[z0,z1,z269,z4,z5,z6]),(0,[z155,z0,z240,z2,z4,z5,z6]),(0,[z0,z1,z2,z576,z4,z5,z6]),(0,[z0,z1,z577,z2,z4,z5,z6]),(0,[z0,z1,z2,z38,z4,z5,z6])],[(0,[z578,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z579,z6]),(0,[z1,z2,z93,z4,z5,z65,z6]),(0,[z0,z239,z1,z2,z4,z5,z6]),(0,[z580,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z581]),(0,[z0,z1,z2,z582,z4,z5,z6]),(0,[z136,z0,z1,z4,z124,z5,z6]),(0,[z0,z1,z2,z4,z5,z583,z6]),(0,[z0,z1,z12,z4,z5,z47,z6]),(0,[z584,z0,z1,z2,z4,z5,z6])],[(0,[z63,z155,z1,z2,z4,z5,z6]),(0,[z20,z1,z213,z2,z4,z5,z6])]],
   [[(0,[z542,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z298,z6]),(0,[z0,z1,z2,z585,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z586,z6]),(1,[z43,z0,z2,z4,z304,z6]),(0,[z43,z0,z2,z4,z5,z96,z6]),(0,[z0,z1,z2,z99,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z587]),(0,[z0,z1,z2,z38,z4,z165,z6])],[(0,[z168,z129,z1,z2,z4,z5,z6]),(0,[z588,z0,z1,z2,z4,z5,z6]),(0,[z275,z0,z285,z2,z4,z5,z6]),(0,[z33,z0,z1,z2,z4,z5,z6]),(0,[z0,z44,z1,z24,z4,z5,z6]),(0,[z0,z589,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z53,z5,z6]),(0,[z0,z1,z2,z4,z5,z304,z6]),(0,[z0,z115,z1,z2,z39,z4,z6]),(0,[z590,z0,z1,z2,z4,z5,z6]),(0,[z0,z591,z1,z2,z4,z5,z6]),(0,[z0,z1,z592,z2,z4,z5,z6])],[(0,[z0,z1,z2,z593,z4,z5,z6]),(1,[z0,z285,z2,z4,z5,z6]),(0,[z0,z1,z2,z594,z4,z5,z6]),(1,[z140,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z112,z4,z5,z6]),(0,[z0,z1,z2,z131,z4,z5,z90]),(0,[z0,z1,z2,z209,z4,z5,z6])],[(0,[z595,z0,z1,z2,z4,z5,z6]),(0,[z0,z2,z24,z4,z110,z5,z6]),(0,[z0,z1,z2,z596,z4,z5,z6]),(0,[z0,z1,z2,z99,z4,z165,z6])],[(0,[z554,z0,z1,z2,z4,z5,z6]),(0,[z0,z10,z237,z2,z4,z5,z6]),(0,[z129,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z597,z4,z5,z6]),(1,[z0,z457,z2,z4,z5,z6]),(0,[z281,z0,z1,z24,z4,z5,z6]),(0,[z0,z1,z2,z305,z4,z98,z6]),(0,[z0,z1,z2,z4,z598,z5,z6])],[(0,[z599,z0,z1,z2,z4,z5,z6]),(0,[z0,z240,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z26,z6,z81]),(0,[z600,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z601,z4,z5,z6]),(1,[z0,z325,z2,z4,z5,z6]),(0,[z602,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z112,z4,z165,z6]),(0,[z0,z1,z349,z4,z5,z6,z90]),(0,[z0,z603,z1,z2,z4,z5,z6])],[(1,[z33,z30,z2,z4,z5,z6]),(0,[z0,z30,z2,z38,z4,z5,z6]),(0,[z604,z0,z1,z2,z4,z5,z6]),(0,[z0,z10,z2,z39,z4,z5,z6]),(0,[z605,z0,z1,z2,z4,z5,z6]),(1,[z156,z0,z2,z110,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z173])],[(0,[z1,z30,z2,z4,z5,z84,z6]),(0,[z13,z0,z1,z2,z4,z165,z5]),(0,[z0,z1,z237,z2,z98,z5,z6]),(0,[z0,z1,z2,z4,z606,z5,z6]),(0,[z0,z1,z607,z2,z4,z5,z6])]],
   [[(0,[z433,z0,z10,z2,z4,z5,z6]),(0,[z0,z1,z83,z2,z4,z26,z6]),(0,[z0,z1,z2,z4,z5,z6,z608]),(0,[z0,z1,z2,z4,z25,z124,z6]),(0,[z609,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z610,z5,z6])],[(0,[z20,z0,z30,z2,z4,z5,z6]),(1,[z169,z1,z2,z4,z5,z6]),(0,[z13,z36,z1,z2,z4,z5,z6]),(1,[z170,z1,z2,z4,z5,z6]),(0,[z0,z1,z12,z2,z68,z4,z5]),(0,[z0,z1,z2,z611,z4,z5,z6])],[(0,[z0,z10,z2,z4,z5,z315,z6]),(0,[z0,z1,z41,z4,z98,z5,z6]),(0,[z20,z0,z1,z213,z4,z5,z6]),(0,[z612,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z613,z6]),(0,[z0,z1,z2,z614,z4,z5,z6]),(0,[z615,z0,z1,z2,z4,z5,z6])],[(0,[z490,z0,z30,z2,z4,z5,z6]),(0,[z491,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z616,z4,z5,z6]),(0,[z0,z1,z617,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z618]),(1,[z0,z1,z2,z112,z6,z81])],[(0,[z32,z0,z30,z2,z4,z5,z6]),(1,[z30,z2,z4,z5,z6,z87]),(0,[z0,z1,z2,z4,z619,z5,z6]),(0,[z0,z1,z2,z4,z620,z5,z6]),(0,[z0,z1,z2,z4,z621,z5,z6]),(0,[z0,z1,z2,z4,z110,z5,z6]),(1,[z0,z1,z252,z4,z124,z6])],[(0,[z0,z1,z2,z4,z5,z6,z622]),(0,[z0,z1,z2,z4,z5,z6,z623]),(0,[z0,z1,z2,z624,z4,z5,z6])],[(1,[z30,z2,z93,z4,z5,z6]),(0,[z0,z1,z625,z2,z4,z5,z6]),(0,[z0,z1,z626,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z627])],[(0,[z0,z30,z2,z4,z5,z6,z173]),(0,[z168,z1,z213,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z628,z5,z6]),(0,[z629,z0,z1,z2,z4,z5,z6])]],
   [[(0,[z20,z0,z143,z2,z4,z5,z6]),(0,[z33,z0,z457,z2,z4,z5,z6]),(0,[z0,z1,z502,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z77]),(0,[z0,z1,z2,z209,z4,z6,z90])],[(0,[z62,z0,z1,z2,z4,z5,z6]),(0,[z19,z1,z2,z41,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z630]),(0,[z1,z12,z258,z2,z4,z5,z6]),(0,[z201,z0,z1,z2,z4,z5,z6])],[(1,[z0,z1,z370,z4,z5,z6]),(0,[z0,z1,z2,z305,z4,z5,z6]),(0,[z0,z1,z2,z631,z4,z5,z6]),(0,[z0,z1,z12,z46,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z632])],[(0,[z633,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z634,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z635,z6]),(0,[z0,z1,z2,z4,z89,z5,z6]),(0,[z0,z1,z2,z636,z4,z5,z6]),(0,[z0,z1,z2,z4,z637,z5,z6])],[(0,[z0,z1,z2,z4,z4,z5,z6]),(0,[z638,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z639,z2,z4,z5,z6]),(0,[z0,z1,z2,z640,z4,z5,z6]),(0,[z0,z1,z2,z541,z4,z6,z193]),(0,[z0,z1,z337,z2,z4,z5,z6])],[(0,[z0,z30,z2,z4,z619,z5,z6]),(0,[z0,z415,z30,z2,z4,z5,z6]),(0,[z0,z30,z2,z4,z110,z5,z6]),(0,[z168,z0,z1,z2,z4,z398,z6]),(0,[z0,z1,z2,z4,z26,z5,z6]),(1,[z19,z1,z2,z4,z84,z6]),(0,[z0,z1,z2,z4,z5,z641,z6]),(1,[z0,z280,z2,z4,z5,z96])],[(0,[z254,z0,z30,z2,z4,z5,z6]),(0,[z0,z10,z2,z4,z346,z5,z6]),(0,[z0,z1,z2,z4,z5,z642,z6]),(0,[z643,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z644]),(0,[z0,z1,z2,z645,z4,z5,z6])],[(0,[z0,z10,z2,z4,z132,z5,z6]),(0,[z0,z197,z1,z2,z4,z5,z6])]],
   [[(1,[z168,z30,z2,z4,z5,z6]),(1,[z0,z290,z2,z4,z5,z6]),(0,[z646,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z647,z4,z5,z6]),(1,[z0,z1,z2,z131,z5,z90]),(0,[z648,z0,z1,z2,z4,z5,z6])],[(0,[z168,z0,z30,z2,z4,z5,z6]),(0,[z63,z33,z1,z2,z4,z5,z6]),(0,[z0,z10,z2,z4,z5,z6,z87]),(0,[z649,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z650,z5,z6]),(0,[z651,z0,z1,z2,z4,z5,z6]),(0,[z43,z13,z0,z2,z4,z5,z6]),(0,[z0,z1,z2,z112,z5,z6,z81]),(0,[z0,z1,z2,z112,z39,z4,z6])],[(0,[z0,z10,z2,z52,z4,z5,z6]),(0,[z20,z0,z1,z2,z4,z5,z6]),(0,[z652,z0,z1,z2,z4,z5,z6]),(0,[z13,z0,z1,z2,z38,z4,z5]),(0,[z0,z1,z2,z4,z5,z6,z127])],[(0,[z0,z10,z2,z93,z4,z5,z6]),(0,[z0,z1,z2,z366,z4,z5,z6]),(0,[z0,z1,z2,z4,z165,z84,z6]),(0,[z653,z0,z1,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z165,z5,z87]),(0,[z0,z1,z2,z4,z5,z6,z654]),(0,[z0,z1,z2,z4,z5,z655,z6]),(0,[z0,z1,z2,z150,z4,z98,z6]),(0,[z0,z1,z2,z4,z5,z6,z106]),(0,[z0,z1,z2,z656,z4,z5,z6])],[(0,[z32,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z657,z5,z6])],[(1,[z254,z30,z2,z4,z5,z6]),(0,[z658,z0,z1,z2,z4,z5,z6])],[(0,[z0,z10,z2,z171,z4,z5,z6]),(0,[z0,z1,z659,z2,z4,z5,z6])]],
   [[(0,[z0,z1,z2,z4,z5,z146,z6]),(0,[z156,z0,z2,z4,z53,z5,z6]),(0,[z660,z0,z1,z2,z4,z5,z6])],[(0,[z129,z0,z1,z41,z4,z5,z6]),(0,[z0,z1,z661,z2,z4,z5,z6]),(0,[z136,z363,z1,z2,z4,z5,z6]),(0,[z0,z1,z46,z2,z131,z4,z5])],[(1,[z281,z0,z24,z4,z5,z6]),(0,[z0,z1,z2,z662,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z420])],[(0,[z0,z30,z2,z131,z4,z5,z6]),(1,[z0,z1,z2,z4,z398,z6]),(0,[z0,z1,z2,z4,z5,z6,z663]),(0,[z0,z1,z2,z68,z131,z5,z6]),(0,[z0,z1,z2,z38,z131,z4,z5])],[(0,[z0,z1,z397,z2,z4,z5,z6]),(0,[z0,z10,z2,z4,z5,z6,z119]),(0,[z0,z1,z2,z403,z4,z5,z6])],[(1,[z10,z30,z2,z4,z5,z6]),(0,[z490,z0,z10,z2,z4,z5,z6]),(0,[z664,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z665,z5,z6]),(0,[z666,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z667,z5,z6]),(1,[z0,z1,z2,z4,z215,z6]),(0,[z0,z1,z2,z4,z11,z6,z81]),(0,[z0,z668,z1,z2,z4,z5,z6])],[(0,[z275,z0,z30,z2,z4,z5,z6]),(0,[z0,z1,z290,z2,z4,z5,z6]),(1,[z0,z1,z2,z4,z5,z174]),(0,[z0,z1,z12,z2,z4,z5,z65]),(0,[z669,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z670,z5,z6])],[(0,[z254,z0,z1,z2,z4,z5,z6]),(0,[z0,z10,z2,z4,z5,z47,z6]),(0,[z0,z10,z2,z4,z5,z6,z193]),(0,[z168,z0,z1,z2,z93,z5,z6]),(0,[z155,z0,z1,z2,z4,z5,z322]),(0,[z0,z1,z46,z2,z4,z5,z65]),(0,[z0,z44,z2,z4,z53,z5,z6]),(0,[z0,z1,z2,z671,z4,z5,z6]),(0,[z0,z1,z2,z672,z4,z5,z6]),(0,[z0,z1,z252,z2,z4,z11,z6]),(0,[z0,z1,z2,z4,z165,z5,z119])]],
   [[(0,[z0,z10,z2,z68,z4,z5,z6]),(0,[z673,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z184,z2,z4,z5,z6]),(0,[z0,z674,z1,z2,z4,z5,z6])],[(0,[z675,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z38,z4,z5,z65]),(1,[z0,z1,z2,z541,z4,z6]),(1,[z0,z179,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z128,z5,z6]),(0,[z0,z1,z2,z4,z71,z6,z90])],[(0,[z0,z1,z213,z2,z4,z5,z6]),(0,[z0,z115,z1,z2,z4,z304,z6]),(0,[z0,z1,z2,z4,z676,z5,z6]),(0,[z0,z1,z2,z4,z677,z5,z6])],[(0,[z0,z1,z2,z4,z5,z678,z6]),(0,[z156,z0,z10,z2,z4,z5,z6]),(0,[z156,z0,z2,z4,z110,z5,z6]),(0,[z0,z115,z2,z4,z53,z5,z6])],[(1,[z129,z1,z41,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z84,z6]),(0,[z0,z1,z2,z679,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z680,z6]),(0,[z0,z1,z2,z4,z5,z681,z6]),(0,[z43,z0,z2,z52,z4,z5,z6]),(0,[z0,z1,z682,z2,z4,z5,z6])],[(0,[z33,z0,z1,z2,z4,z5,z65]),(0,[z0,z1,z2,z4,z683,z5,z6]),(1,[z97,z1,z2,z4,z5,z6]),(0,[z0,z1,z684,z2,z4,z5,z6]),(1,[z0,z1,z12,z4,z5,z47])],[(0,[z1,z30,z2,z4,z5,z6,z87]),(0,[z0,z10,z44,z2,z4,z5,z6]),(0,[z0,z1,z213,z4,z5,z47,z6]),(0,[z19,z0,z154,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z685,z5,z6]),(0,[z0,z1,z171,z4,z124,z5,z6]),(0,[z0,z1,z2,z4,z5,z323,z6])],[(0,[z0,z1,z2,z4,z686,z5,z6]),(1,[z155,z30,z2,z4,z5,z6]),(0,[z0,z30,z2,z226,z4,z5,z6]),(0,[z0,z274,z1,z2,z4,z5,z6]),(1,[z0,z1,z349,z4,z5,z6]),(0,[z687,z0,z1,z2,z4,z5,z6])]],
   [[(0,[z1,z30,z2,z93,z4,z5,z6]),(0,[z0,z1,z2,z4,z688,z5,z6]),(0,[z0,z1,z2,z689,z4,z5,z6]),(0,[z0,z135,z2,z52,z4,z5,z6]),(1,[z0,z1,z2,z4,z5,z420]),(1,[z0,z1,z83,z4,z11,z6]),(0,[z0,z1,z2,z25,z5,z6,z81]),(0,[z0,z1,z2,z68,z4,z165,z5])],[(0,[z0,z1,z2,z4,z690,z5,z6]),(0,[z0,z1,z691,z2,z4,z5,z6])],[(0,[z0,z10,z30,z2,z4,z5,z6]),(0,[z155,z1,z30,z2,z4,z5,z6]),(0,[z0,z1,z692,z2,z4,z5,z6]),(0,[z168,z0,z1,z269,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z693]),(1,[z0,z16,z2,z4,z5,z6]),(0,[z0,z44,z2,z4,z110,z5,z6]),(1,[z0,z1,z2,z4,z583,z6])],[(1,[z30,z2,z41,z4,z5,z6]),(0,[z10,z1,z30,z2,z4,z5,z6]),(0,[z0,z10,z2,z4,z165,z5,z6]),(0,[z0,z1,z220,z2,z4,z5,z6]),(0,[z694,z0,z1,z2,z4,z5,z6]),(0,[z155,z0,z1,z2,z4,z84,z6]),(1,[z0,z1,z2,z4,z5,z426]),(0,[z695,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z696,z6]),(1,[z55,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z25,z11,z6]),(0,[z194,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z697,z4,z5,z6])],[(0,[z0,z0,z30,z2,z4,z5,z6]),(0,[z0,z30,z2,z4,z5,z6,z81]),(1,[z0,z227,z2,z4,z5,z6]),(0,[z275,z0,z1,z2,z93,z5,z6]),(0,[z0,z1,z2,z4,z698,z5,z6]),(0,[z0,z1,z2,z4,z699,z5,z6]),(0,[z0,z1,z700,z2,z4,z5,z6])],[(0,[z0,z30,z2,z4,z5,z84,z6]),(0,[z0,z1,z2,z701,z4,z5,z6]),(0,[z0,z1,z2,z702,z4,z5,z6]),(0,[z0,z2,z4,z5,z6,z297,z173]),(0,[z0,z1,z2,z703,z4,z5,z6])],[(0,[z0,z294,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z704,z6])],[(0,[z20,z0,z1,z41,z4,z5,z6]),(0,[z245,z135,z1,z2,z4,z5,z6]),(0,[z136,z0,z1,z2,z4,z5,z6]),(1,[z0,z1,z2,z231,z4,z5]),(0,[z705,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z706,z6]),(0,[z0,z1,z12,z2,z4,z583,z6])]]]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkB : List (List (List (ℕ × List W))) :=
  [[[(0,[z0,z707,z2,z4,z5,z6]),(0,[z136,z0,z1,z104,z4,z5]),(0,[z0,z1,z2,z150,z4,z6])],[(0,[z30,z252,z2,z4,z84,z6]),(0,[z0,z1,z2,z112,z4,z323]),(0,[z0,z1,z349,z131,z4,z5])],[(0,[z0,z10,z2,z4,z708,z6]),(0,[z0,z10,z46,z4,z5,z119]),(0,[z0,z709,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z710,z173])],[(0,[z63,z1,z2,z4,z5,z455]),(0,[z0,z10,z2,z711,z4,z6]),(0,[z20,z21,z2,z4,z5,z6]),(0,[z168,z220,z2,z272,z5,z6]),(0,[z32,z1,z403,z4,z5,z6])],[(0,[z0,z30,z2,z4,z5,z174]),(0,[z1,z403,z4,z26,z5,z6]),(0,[z0,z2,z4,z5,z6,z712]),(0,[z713,z1,z2,z4,z5,z6]),(0,[z0,z1,z80,z4,z5,z292])],[(0,[z0,z1,z2,z714,z4,z5]),(0,[z36,z2,z52,z4,z5,z6]),(0,[z136,z170,z1,z98,z5,z6]),(0,[z0,z179,z2,z4,z215,z6])],[(0,[z20,z715,z2,z4,z5,z6]),(0,[z0,z397,z2,z4,z518,z6]),(0,[z109,z30,z2,z4,z5,z6]),(0,[z0,z1,z2,z716,z4,z6]),(0,[z0,z1,z2,z4,z165,z173])],[(0,[z62,z30,z2,z4,z84,z6]),(1,[z30,z200,z4,z5,z6]),(0,[z0,z290,z2,z4,z5,z6]),(0,[z10,z514,z2,z4,z5,z6]),(0,[z0,z10,z2,z4,z137,z6]),(0,[z0,z717,z2,z4,z5,z6]),(0,[z0,z718,z2,z4,z5,z6])],[(0,[z206,z30,z2,z4,z5,z6]),(0,[z0,z2,z4,z719,z5,z6]),(0,[z170,z325,z2,z4,z5,z6]),(0,[z201,z1,z2,z80,z4,z5])],[(0,[z0,z1,z2,z4,z720,z6]),(0,[z281,z0,z561,z4,z5,z6]),(0,[z1,z721,z2,z4,z5,z6]),(0,[z0,z1,z4,z5,z722,z6]),(0,[z201,z723,z2,z4,z5,z6]),(0,[z211,z724,z2,z4,z5,z6])],[(0,[z129,z30,z41,z4,z5,z6]),(0,[z0,z2,z4,z725,z5,z6]),(0,[z208,z0,z2,z80,z4,z5]),(0,[z1,z726,z2,z4,z5,z6])],[(0,[z1,z41,z4,z573,z5,z6]),(0,[z0,z727,z2,z4,z5,z6])],[(0,[z728,z1,z2,z4,z5,z6])],[(0,[z0,z729,z2,z4,z5,z6]),(0,[z136,z0,z1,z98,z5,z6])],[(0,[z172,z1,z2,z4,z5,z87]),(0,[z0,z1,z2,z4,z730,z6]),(0,[z0,z1,z2,z731,z6,z81])],[(0,[z0,z1,z403,z4,z167,z6]),(0,[z1,z732,z2,z4,z5,z6]),(0,[z169,z1,z2,z39,z4,z6]),(0,[z363,z1,z2,z4,z5,z270])]],
   [[(0,[z136,z0,z30,z98,z5,z6]),(0,[z0,z2,z4,z5,z6,z733]),(0,[z0,z1,z734,z4,z5,z6])],[(0,[z30,z2,z4,z5,z398,z6]),(0,[z30,z2,z38,z4,z5,z87]),(0,[z0,z1,z2,z4,z735,z6]),(0,[z0,z1,z2,z4,z5,z736]),(0,[z0,z1,z737,z4,z5,z6])],[(0,[z0,z738,z2,z4,z5,z6]),(0,[z0,z739,z2,z4,z5,z6]),(0,[z0,z1,z2,z740,z4,z5]),(0,[z36,z2,z4,z5,z6,z193])],[(0,[z30,z2,z4,z406,z5,z6]),(0,[z1,z2,z4,z26,z146,z6])],[(0,[z0,z30,z2,z4,z5,z270]),(0,[z10,z2,z4,z159,z5,z6]),(0,[z0,z1,z213,z4,z5,z267])],[(0,[z0,z30,z2,z231,z4,z5]),(0,[z1,z30,z403,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z174]),(0,[z741,z1,z2,z4,z5,z6]),(0,[z0,z44,z556,z4,z5,z6]),(0,[z136,z0,z1,z104,z98,z5]),(0,[z0,z742,z2,z4,z5,z6]),(0,[z172,z396,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z743,z6]),(0,[z254,z744,z2,z4,z5,z6]),(0,[z30,z413,z2,z4,z5,z6]),(0,[z745,z0,z2,z4,z5,z6]),(0,[z0,z1,z502,z4,z26,z6]),(0,[z0,z1,z2,z4,z746,z5]),(0,[z0,z2,z80,z4,z5,z127])],[(0,[z312,z30,z41,z4,z5,z6]),(1,[z30,z2,z4,z42,z6]),(0,[z646,z30,z2,z4,z5,z6]),(0,[z32,z1,z2,z4,z5,z747]),(0,[z0,z1,z2,z4,z748,z6])],[(0,[z62,z1,z2,z4,z84,z6]),(0,[z63,z1,z134,z4,z5,z6]),(0,[z0,z1,z237,z171,z5,z6]),(0,[z0,z1,z2,z4,z749,z6])],[(0,[z0,z30,z2,z4,z5,z750]),(0,[z0,z1,z751,z4,z5,z6]),(0,[z1,z200,z4,z26,z5,z6])],[(0,[z0,z1,z752,z98,z5,z6])],[(0,[z0,z753,z2,z4,z5,z6]),(0,[z0,z30,z4,z5,z6,z292]),(0,[z0,z10,z2,z4,z398,z6]),(0,[z32,z1,z2,z4,z5,z455]),(0,[z97,z1,z2,z231,z4,z5]),(0,[z2,z4,z5,z6,z754,z266])],[(0,[z0,z2,z4,z5,z6,z755]),(0,[z0,z1,z2,z756,z4,z5])],[(0,[z36,z30,z2,z4,z5,z6]),(0,[z0,z21,z2,z4,z5,z6]),(0,[z0,z10,z2,z4,z215,z6]),(0,[z0,z1,z269,z4,z5,z174]),(0,[z0,z2,z4,z5,z6,z757])],[(0,[z0,z10,z502,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z758])],[(0,[z0,z744,z2,z4,z5,z6]),(0,[z0,z1,z759,z4,z5,z6]),(0,[z0,z1,z2,z4,z331,z161]),(0,[z0,z88,z4,z145,z5,z6])]],
   [[(0,[z0,z1,z2,z4,z760,z6]),(0,[z0,z1,z349,z4,z5,z47])],[(0,[z0,z16,z2,z4,z5,z6]),(0,[z0,z761,z2,z4,z5,z6]),(0,[z33,z30,z2,z4,z5,z65]),(0,[z0,z1,z2,z4,z5,z762]),(0,[z0,z763,z2,z4,z5,z6]),(0,[z0,z1,z2,z38,z4,z571]),(0,[z0,z2,z4,z165,z297,z173])],[(0,[z30,z2,z41,z4,z5,z6]),(0,[z0,z30,z2,z4,z71,z6]),(0,[z353,z30,z2,z4,z5,z6]),(0,[z764,z1,z2,z4,z5,z6]),(0,[z0,z389,z2,z4,z5,z323])],[(0,[z0,z1,z2,z5,z731,z6])],[(0,[z542,z30,z2,z4,z5,z87]),(0,[z0,z1,z2,z4,z5,z267]),(0,[z0,z1,z2,z765,z4,z6])],[(0,[z97,z10,z2,z4,z5,z6]),(0,[z0,z115,z2,z4,z346,z6]),(0,[z0,z1,z766,z4,z5,z6]),(0,[z0,z115,z2,z4,z53,z6]),(0,[z0,z1,z2,z4,z5,z270]),(0,[z0,z1,z767,z4,z5,z6])],[(0,[z0,z10,z4,z5,z6,z344]),(0,[z0,z1,z46,z4,z5,z630]),(0,[z768,z0,z2,z4,z5,z6]),(0,[z33,z1,z134,z4,z5,z65]),(0,[z0,z1,z2,z4,z769,z5])],[(0,[z30,z2,z4,z5,z287,z6]),(0,[z0,z1,z142,z4,z124,z6]),(0,[z0,z1,z2,z4,z167,z455]),(0,[z0,z1,z770,z4,z5,z6]),(0,[z771,z1,z2,z4,z5,z6]),(0,[z136,z0,z1,z98,z137,z6]),(0,[z0,z1,z2,z5,z772,z90])],[(0,[z0,z30,z2,z4,z126,z6]),(0,[z0,z1,z2,z773,z4,z5]),(0,[z0,z1,z2,z4,z5,z774]),(0,[z32,z16,z2,z4,z5,z87]),(0,[z775,z0,z2,z4,z5,z6]),(0,[z194,z776,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z710,z5])],[(0,[z36,z2,z24,z4,z5,z6]),(0,[z0,z2,z725,z110,z5,z6]),(0,[z136,z363,z1,z98,z5,z6]),(0,[z136,z0,z179,z98,z5,z6])],[(0,[z0,z1,z2,z4,z5,z750]),(0,[z0,z1,z777,z4,z5,z6]),(0,[z154,z2,z93,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z778])],[(0,[z30,z2,z4,z5,z6,z455]),(0,[z673,z0,z1,z98,z5,z6])],[(0,[z30,z2,z4,z5,z6,z266]),(0,[z20,z1,z626,z4,z5,z6]),(0,[z0,z779,z2,z4,z5,z6]),(0,[z170,z179,z2,z4,z5,z6]),(0,[z0,z1,z4,z5,z6,z292]),(0,[z0,z1,z2,z4,z780,z6]),(0,[z0,z2,z4,z781,z5,z6])],[(0,[z1,z30,z2,z4,z5,z455]),(0,[z1,z2,z4,z782,z5,z6]),(0,[z783,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z68,z4,z126])],[(0,[z715,z30,z2,z4,z5,z6]),(0,[z0,z784,z2,z4,z5,z6]),(0,[z36,z1,z2,z4,z5,z6]),(0,[z281,z0,z366,z4,z5,z6]),(0,[z129,z101,z41,z4,z5,z6]),(0,[z194,z1,z2,z4,z5,z455]),(0,[z0,z1,z2,z4,z785,z6]),(0,[z0,z786,z2,z4,z5,z6])],[(0,[z74,z1,z41,z4,z5,z6]),(0,[z0,z548,z24,z4,z5,z6]),(0,[z0,z325,z2,z4,z5,z420]),(0,[z0,z1,z2,z128,z5,z772])]],
   [[(0,[z30,z2,z4,z465,z5,z6]),(0,[z155,z1,z2,z4,z26,z6]),(0,[z32,z1,z134,z4,z5,z6]),(0,[z136,z97,z1,z98,z5,z6]),(0,[z0,z1,z2,z305,z4,z6])],[(0,[z554,z0,z2,z619,z5,z6]),(0,[z554,z0,z2,z110,z5,z6]),(0,[z405,z1,z2,z4,z5,z323]),(0,[z0,z1,z2,z38,z4,z710])],[(0,[z33,z1,z2,z4,z5,z65]),(0,[z0,z1,z787,z4,z5,z6]),(0,[z0,z1,z2,z39,z4,z710])],[(0,[z63,z457,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z788])],[(0,[z0,z135,z2,z52,z5,z6]),(0,[z136,z299,z0,z98,z5,z6]),(0,[z0,z2,z4,z5,z6,z789]),(0,[z0,z1,z4,z71,z6,z344])],[(0,[z30,z2,z473,z4,z5,z6]),(0,[z542,z1,z2,z4,z5,z87]),(0,[z0,z2,z4,z5,z6,z790]),(0,[z0,z1,z2,z99,z731,z6])],[(0,[z0,z154,z2,z4,z5,z6]),(0,[z1,z142,z2,z4,z26,z6]),(0,[z0,z791,z2,z4,z5,z6]),(0,[z0,z240,z370,z4,z5,z6]),(0,[z0,z792,z2,z4,z5,z6])],[(0,[z0,z30,z2,z4,z167,z6]),(0,[z32,z10,z2,z4,z5,z87]),(0,[z0,z10,z2,z38,z39,z4]),(0,[z0,z1,z793,z4,z5,z6]),(0,[z169,z274,z2,z4,z5,z6]),(0,[z0,z1,z2,z104,z305,z4])],[(0,[z168,z30,z2,z4,z5,z174]),(0,[z0,z10,z269,z4,z5,z6]),(0,[z0,z794,z2,z4,z5,z6]),(0,[z97,z1,z2,z150,z4,z6]),(0,[z0,z1,z795,z4,z5,z6]),(0,[z0,z796,z2,z4,z5,z6])],[(0,[z0,z30,z2,z4,z175,z6]),(0,[z0,z143,z2,z4,z146,z6]),(0,[z0,z1,z46,z4,z5,z503]),(0,[z0,z1,z2,z4,z797,z6]),(0,[z0,z1,z798,z4,z5,z6]),(0,[z170,z1,z2,z4,z5,z270]),(0,[z0,z1,z2,z4,z126,z6])],[(0,[z0,z1,z2,z4,z799,z6]),(0,[z30,z2,z484,z4,z5,z6]),(0,[z30,z2,z4,z340,z5,z6]),(1,[z30,z2,z4,z5,z322]),(0,[z800,z1,z2,z4,z5,z6]),(0,[z0,z801,z2,z4,z5,z6]),(0,[z1,z2,z131,z5,z106,z90]),(0,[z1,z802,z2,z4,z5,z6])],[(0,[z803,z1,z2,z4,z5,z6]),(0,[z135,z356,z2,z52,z5,z6])],[(0,[z0,z1,z2,z4,z165,z22]),(0,[z36,z280,z2,z4,z5,z6]),(0,[z804,z1,z2,z4,z5,z6])],[(0,[z30,z2,z4,z128,z5,z87]),(0,[z170,z1,z237,z4,z5,z6]),(0,[z136,z0,z1,z98,z215,z6])],[(0,[z194,z30,z2,z4,z5,z6]),(0,[z0,z2,z4,z5,z6,z805]),(0,[z0,z1,z134,z4,z175,z6]),(0,[z0,z2,z4,z5,z6,z127]),(0,[z0,z1,z46,z300,z4,z5]),(0,[z1,z2,z80,z4,z5,z266])],[(0,[z0,z806,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z137,z270]),(0,[z136,z0,z1,z752,z5,z6]),(0,[z1,z12,z258,z4,z5,z47]),(0,[z0,z1,z2,z28,z128,z5])]],
   [[(0,[z0,z1,z2,z4,z807,z6]),(0,[z0,z1,z2,z4,z808,z6])],[(0,[z20,z30,z2,z4,z331,z6]),(0,[z19,z1,z2,z4,z398,z6]),(0,[z33,z457,z2,z4,z5,z65])],[(0,[z1,z30,z134,z4,z5,z6]),(0,[z0,z1,z2,z4,z809,z6]),(0,[z1,z810,z2,z4,z5,z6])],[(0,[z0,z30,z2,z4,z5,z161]),(0,[z0,z1,z2,z4,z398,z174]),(0,[z811,z1,z2,z4,z5,z6])],[(0,[z169,z10,z2,z4,z5,z6]),(0,[z170,z10,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z812]),(0,[z0,z1,z2,z4,z165,z317]),(0,[z813,z1,z2,z4,z5,z6])],[(0,[z97,z814,z2,z4,z5,z6])],[(0,[z30,z2,z4,z5,z6,z199]),(0,[z30,z237,z41,z4,z5,z6]),(0,[z0,z1,z2,z4,z815,z6]),(0,[z0,z1,z2,z99,z606,z6]),(0,[z0,z816,z2,z4,z5,z6])],[(0,[z0,z10,z2,z817,z4,z5]),(0,[z0,z1,z403,z4,z5,z455]),(0,[z168,z1,z2,z313,z5,z6]),(0,[z1,z337,z2,z4,z5,z323])],[(0,[z0,z1,z2,z4,z167,z6]),(0,[z0,z1,z4,z5,z6,z818]),(0,[z1,z819,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z5,z820]),(0,[z0,z821,z2,z4,z5,z6])],[(0,[z0,z30,z237,z171,z5,z6]),(0,[z0,z2,z4,z5,z6,z754]),(0,[z0,z1,z2,z4,z175,z6]),(0,[z0,z1,z349,z4,z5,z65]),(0,[z0,z1,z822,z4,z5,z6]),(0,[z823,z0,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z824,z6]),(0,[z0,z1,z2,z4,z5,z825]),(0,[z36,z73,z2,z4,z5,z6])],[(0,[z0,z184,z2,z4,z5,z6]),(0,[z1,z2,z826,z4,z5,z6]),(0,[z0,z1,z252,z4,z124,z323]),(0,[z0,z827,z2,z4,z5,z6])],[(0,[z0,z1,z828,z4,z5,z6]),(0,[z1,z213,z403,z4,z5,z6]),(0,[z0,z2,z104,z4,z89,z5])],[(0,[z30,z2,z4,z5,z523,z6]),(0,[z1,z2,z4,z159,z5,z6])],[(0,[z194,z1,z2,z4,z5,z6]),(0,[z170,z829,z2,z4,z5,z6]),(0,[z830,z0,z2,z4,z5,z6])]],
   [[(0,[z30,z2,z4,z5,z386,z6]),(0,[z0,z1,z269,z4,z167,z6]),(0,[z0,z814,z2,z4,z5,z6])],[(0,[z0,z30,z2,z4,z831,z6]),(0,[z0,z30,z2,z832,z4,z5]),(0,[z168,z21,z2,z4,z5,z6]),(0,[z0,z1,z57,z4,z5,z65]),(0,[z13,z36,z2,z4,z5,z193])],[(0,[z30,z2,z4,z5,z6,z535]),(0,[z63,z1,z2,z4,z398,z6]),(0,[z0,z833,z2,z4,z5,z6]),(0,[z0,z1,z4,z5,z47,z138]),(0,[z0,z834,z2,z4,z5,z6])],[(0,[z30,z2,z39,z4,z84,z6]),(0,[z0,z10,z2,z131,z5,z90]),(0,[z1,z147,z41,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z835]),(0,[z0,z179,z2,z4,z5,z420]),(0,[z0,z836,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z5,z161]),(0,[z0,z227,z2,z4,z5,z174]),(0,[z0,z1,z2,z4,z5,z837]),(0,[z838,z1,z2,z4,z5,z6])],[(0,[z30,z2,z4,z5,z6,z547]),(0,[z653,z30,z2,z4,z5,z6]),(0,[z0,z1,z4,z124,z215,z6]),(0,[z0,z1,z2,z4,z215,z270]),(0,[z0,z1,z171,z752,z5,z6])],[(0,[z0,z30,z2,z4,z5,z267]),(0,[z0,z30,z2,z99,z25,z6]),(0,[z1,z826,z41,z4,z5,z6]),(0,[z0,z839,z2,z4,z5,z6]),(0,[z840,z1,z2,z4,z5,z6]),(0,[z0,z841,z2,z4,z5,z6]),(0,[z0,z1,z2,z131,z71,z90])],[(0,[z0,z30,z403,z4,z5,z6]),(0,[z30,z2,z4,z159,z5,z6]),(0,[z612,z30,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z842,z6]),(0,[z55,z240,z2,z4,z5,z6]),(0,[z1,z2,z4,z5,z6,z843]),(0,[z844,z1,z2,z4,z5,z6])],[(0,[z845,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z846,z6]),(0,[z0,z847,z2,z4,z5,z6])],[(0,[z275,z30,z2,z93,z5,z6]),(0,[z0,z1,z2,z4,z5,z848]),(0,[z0,z457,z2,z4,z175,z6]),(0,[z0,z1,z849,z4,z5,z6]),(0,[z1,z850,z2,z4,z5,z6])],[(0,[z0,z1,z252,z4,z340,z6]),(0,[z0,z2,z52,z560,z5,z6]),(0,[z851,z1,z2,z4,z5,z6])],[(0,[z0,z30,z2,z4,z331,z6]),(0,[z33,z30,z2,z4,z175,z6]),(0,[z0,z125,z370,z4,z5,z6])],[(0,[z0,z10,z200,z4,z5,z6]),(0,[z250,z10,z2,z4,z5,z6]),(0,[z0,z852,z2,z4,z5,z6]),(0,[z0,z1,z213,z4,z331,z6]),(0,[z853,z0,z2,z4,z5,z6]),(0,[z0,z2,z4,z5,z854,z6])],[(0,[z0,z855,z2,z4,z5,z6]),(0,[z856,z1,z2,z4,z5,z6]),(0,[z136,z0,z1,z526,z5,z6])],[(0,[z312,z0,z24,z4,z5,z6]),(0,[z194,z387,z2,z4,z5,z6]),(0,[z0,z1,z209,z4,z6,z344])],[(0,[z0,z1,z2,z4,z5,z857])]],
   [[(0,[z543,z30,z2,z4,z5,z6]),(0,[z0,z858,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z859,z6])],[(1,[z1,z2,z860,z5,z6]),(0,[z1,z2,z4,z5,z6,z747])],[(0,[z155,z30,z2,z4,z26,z6]),(0,[z0,z30,z2,z305,z4,z6]),(0,[z0,z1,z2,z4,z831,z6]),(0,[z0,z1,z2,z832,z4,z5]),(0,[z363,z1,z2,z4,z137,z6])],[(0,[z0,z715,z2,z4,z5,z6]),(0,[z0,z2,z4,z5,z6,z297])],[(0,[z0,z10,z2,z541,z4,z6]),(0,[z0,z1,z2,z4,z861,z6])],[(0,[z0,z1,z862,z4,z5,z6]),(0,[z0,z863,z2,z4,z5,z6]),(0,[z0,z1,z4,z5,z6,z864])],[(0,[z20,z30,z213,z4,z5,z6]),(0,[z30,z592,z2,z4,z5,z6]),(0,[z10,z69,z2,z4,z5,z6]),(0,[z0,z10,z2,z104,z4,z5]),(0,[z0,z865,z2,z4,z5,z6]),(0,[z0,z290,z2,z4,z146,z6]),(0,[z1,z2,z4,z5,z6,z266]),(0,[z0,z1,z2,z4,z26,z426]),(0,[z43,z0,z2,z4,z358,z5])],[(0,[z542,z0,z2,z4,z5,z114]),(0,[z866,z0,z1,z4,z5,z6]),(0,[z0,z1,z2,z99,z25,z6])],[(0,[z0,z30,z4,z867,z5,z6]),(0,[z0,z10,z12,z4,z5,z47]),(0,[z0,z1,z403,z4,z5,z6]),(0,[z44,z356,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z868]),(0,[z13,z0,z2,z640,z4,z5]),(0,[z0,z1,z2,z4,z165,z536]),(0,[z97,z1,z2,z305,z4,z6]),(0,[z0,z1,z2,z4,z5,z869]),(0,[z0,z870,z2,z4,z5,z6])],[(0,[z13,z0,z2,z4,z103,z5]),(1,[z0,z1,z4,z722,z6]),(0,[z201,z1,z2,z112,z6,z81])],[(0,[z866,z0,z30,z4,z5,z6]),(0,[z0,z10,z349,z4,z5,z6]),(0,[z275,z1,z2,z93,z5,z6]),(0,[z168,z154,z2,z4,z5,z6]),(0,[z0,z79,z2,z4,z5,z6]),(0,[z1,z2,z4,z871,z5,z6]),(0,[z872,z1,z2,z4,z5,z6])],[(0,[z168,z30,z2,z4,z167,z6]),(0,[z0,z10,z2,z4,z5,z420]),(0,[z0,z10,z83,z4,z11,z6]),(0,[z873,z0,z2,z4,z5,z6]),(0,[z874,z0,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z26,z278]),(0,[z0,z1,z171,z5,z6,z507]),(0,[z405,z875,z2,z4,z5,z6]),(0,[z876,z1,z2,z4,z5,z6]),(0,[z0,z877,z2,z4,z5,z6]),(0,[z208,z0,z2,z112,z6,z81])],[(0,[z0,z113,z2,z4,z5,z96]),(0,[z0,z1,z2,z4,z331,z6]),(0,[z0,z878,z2,z4,z5,z6]),(0,[z0,z1,z4,z124,z722,z6])],[(0,[z0,z10,z2,z4,z583,z6]),(0,[z0,z1,z349,z4,z71,z6])],[(0,[z0,z10,z2,z4,z5,z426]),(0,[z0,z1,z2,z4,z879,z6]),(0,[z0,z1,z502,z99,z4,z6])],[(0,[z0,z30,z2,z4,z5,z455]),(0,[z615,z30,z2,z4,z5,z6]),(0,[z36,z2,z4,z53,z5,z6]),(0,[z0,z1,z2,z4,z5,z880])]],
   [[(0,[z0,z1,z2,z4,z881,z6]),(0,[z0,z1,z2,z4,z5,z882]),(0,[z0,z2,z4,z5,z6,z883])],[(0,[z0,z10,z57,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z884]),(0,[z405,z1,z252,z4,z124,z6]),(0,[z0,z1,z12,z4,z126,z47])],[(0,[z0,z1,z2,z4,z885,z6]),(0,[z0,z1,z2,z4,z5,z886]),(0,[z887,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z888]),(0,[z194,z1,z2,z131,z5,z90])],[(0,[z155,z1,z2,z4,z382,z6]),(0,[z0,z10,z2,z4,z5,z278]),(1,[z0,z1,z2,z731,z6])],[(0,[z0,z1,z2,z711,z4,z6]),(0,[z0,z2,z4,z5,z6,z889]),(0,[z0,z890,z2,z4,z5,z6])],[(0,[z428,z10,z2,z4,z5,z6])],[(0,[z20,z30,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z891,z6]),(0,[z0,z1,z83,z395,z4,z6]),(0,[z0,z892,z2,z4,z5,z6])],[(0,[z20,z1,z213,z4,z5,z6])],[(0,[z30,z2,z634,z4,z5,z6])],[(0,[z56,z30,z2,z4,z5,z6]),(0,[z0,z1,z4,z867,z5,z6]),(0,[z0,z893,z2,z4,z5,z6]),(0,[z0,z1,z2,z150,z104,z4]),(0,[z0,z1,z2,z150,z231,z4])],[(0,[z30,z2,z4,z5,z641,z6]),(0,[z363,z30,z2,z4,z5,z6]),(0,[z441,z30,z2,z4,z5,z6]),(0,[z0,z1,z41,z104,z4,z5]),(0,[z0,z894,z2,z4,z5,z6]),(0,[z0,z776,z2,z4,z5,z6])],[(0,[z30,z2,z4,z5,z642,z6])],[(0,[z1,z30,z2,z4,z398,z6]),(0,[z0,z1,z2,z4,z5,z747]),(0,[z281,z140,z24,z4,z5,z6]),(0,[z895,z1,z2,z4,z5,z6]),(0,[z1,z2,z4,z5,z6,z896]),(0,[z170,z1,z4,z124,z5,z6])],[(0,[z0,z1,z2,z4,z165,z282]),(0,[z0,z1,z2,z4,z5,z897])],[(0,[z33,z1,z2,z4,z5,z416]),(0,[z1,z898,z2,z4,z5,z6])],[(0,[z337,z753,z2,z4,z5,z6]),(0,[z0,z899,z2,z4,z5,z6])]],
   [[(0,[z0,z1,z2,z4,z5,z900]),(0,[z30,z2,z4,z165,z84,z6]),(0,[z540,z10,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z901]),(0,[z0,z1,z2,z4,z5,z455]),(0,[z0,z1,z502,z4,z84,z6])],[(0,[z0,z902,z2,z4,z5,z6]),(0,[z155,z154,z2,z4,z5,z6]),(0,[z0,z903,z2,z4,z5,z6])],[(0,[z129,z1,z403,z4,z5,z6]),(0,[z0,z1,z904,z4,z5,z6]),(0,[z19,z1,z200,z4,z5,z6]),(0,[z905,z1,z2,z4,z5,z6]),(0,[z0,z389,z2,z4,z5,z496]),(0,[z0,z906,z2,z4,z5,z6]),(0,[z0,z1,z2,z5,z772,z6])],[(0,[z136,z0,z89,z98,z5,z6]),(0,[z0,z907,z2,z4,z5,z6]),(0,[z211,z0,z2,z4,z165,z6])],[(0,[z0,z30,z134,z4,z5,z6]),(0,[z284,z2,z93,z4,z5,z6])],[(0,[z30,z2,z4,z5,z146,z6]),(0,[z0,z1,z2,z4,z5,z908]),(0,[z0,z1,z909,z4,z5,z6]),(0,[z140,z2,z52,z4,z5,z6]),(0,[z43,z0,z2,z434,z4,z6]),(0,[z0,z1,z2,z4,z165,z311])],[(0,[z0,z1,z2,z131,z209,z90])],[(0,[z73,z30,z2,z4,z5,z6]),(0,[z0,z227,z2,z4,z167,z6]),(0,[z724,z1,z2,z4,z5,z6])],[(0,[z0,z220,z2,z4,z5,z174]),(0,[z194,z1,z4,z5,z6,z344])],[(0,[z30,z2,z403,z4,z5,z6]),(0,[z155,z30,z2,z4,z84,z6]),(0,[z194,z1,z349,z4,z5,z6])],[(0,[z0,z10,z2,z68,z128,z5]),(0,[z0,z1,z2,z4,z910,z6]),(0,[z405,z389,z2,z4,z5,z6])],[(0,[z168,z30,z403,z4,z5,z6]),(0,[z363,z1,z2,z4,z5,z6]),(0,[z0,z1,z57,z4,z175,z6]),(0,[z172,z1,z2,z4,z5,z65]),(0,[z0,z1,z2,z4,z911,z6]),(0,[z136,z0,z1,z98,z5,z420]),(0,[z337,z79,z2,z4,z5,z6]),(0,[z0,z2,z4,z5,z6,z912]),(0,[z913,z0,z2,z4,z5,z6])],[(0,[z705,z30,z2,z4,z5,z6]),(0,[z0,z1,z12,z4,z5,z641]),(0,[z169,z2,z52,z4,z5,z6]),(0,[z1,z914,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z165,z330])],[(0,[z705,z1,z213,z4,z5,z6]),(0,[z0,z1,z2,z4,z915,z6]),(0,[z0,z1,z2,z4,z84,z426]),(0,[z0,z184,z57,z4,z5,z6]),(0,[z916,z1,z2,z4,z5,z6]),(0,[z0,z280,z2,z100,z4,z5]),(0,[z0,z92,z2,z4,z126,z6])],[],[(0,[z0,z10,z2,z4,z146,z6]),(0,[z0,z2,z4,z917,z5,z6]),(0,[z0,z2,z4,z918,z5,z6]),(0,[z140,z294,z2,z4,z5,z6]),(0,[z0,z1,z2,z919,z4,z5])]],
   [[(0,[z168,z920,z2,z4,z5,z6])],[(0,[z30,z2,z679,z4,z5,z6]),(0,[z0,z2,z4,z358,z53,z5]),(0,[z405,z1,z2,z4,z5,z496]),(0,[z258,z396,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z921,z6])],[(0,[z240,z30,z2,z4,z5,z6]),(0,[z63,z1,z200,z4,z5,z6]),(0,[z0,z1,z12,z4,z5,z922])],[(0,[z0,z1,z2,z4,z5,z923]),(0,[z0,z1,z2,z4,z924,z6]),(0,[z1,z925,z2,z4,z5,z6])],[(0,[z0,z1,z134,z4,z5,z6]),(0,[z0,z1,z2,z926,z4,z6]),(0,[z0,z927,z2,z4,z5,z6]),(0,[z0,z1,z349,z4,z5,z119])],[(0,[z649,z1,z41,z4,z5,z6]),(0,[z928,z0,z2,z4,z5,z6]),(0,[z0,z1,z403,z4,z398,z6]),(0,[z564,z1,z2,z4,z5,z65])],[(0,[z0,z1,z2,z4,z5,z929]),(0,[z201,z1,z2,z4,z26,z6]),(0,[z0,z2,z4,z5,z6,z882]),(0,[z0,z1,z2,z68,z4,z71])],[(0,[z0,z2,z4,z5,z6,z930]),(0,[z387,z0,z2,z4,z5,z6]),(0,[z156,z0,z2,z550,z5,z6]),(0,[z931,z1,z2,z4,z5,z6])],[(0,[z0,z1,z131,z5,z344,z90]),(0,[z211,z932,z2,z4,z5,z6])],[(0,[z0,z2,z4,z5,z6,z933]),(0,[z0,z1,z2,z4,z165,z501])],[(0,[z0,z934,z2,z4,z5,z6]),(1,[z1,z2,z4,z935,z6]),(0,[z936,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z937,z6]),(0,[z43,z36,z2,z4,z5,z6]),(0,[z0,z938,z2,z4,z5,z6]),(0,[z201,z1,z4,z5,z6,z292]),(0,[z0,z939,z2,z4,z5,z6])],[(0,[z63,z240,z2,z4,z5,z6]),(0,[z0,z1,z940,z4,z5,z6])],[(0,[z533,z30,z2,z4,z5,z6]),(0,[z0,z274,z2,z4,z346,z6]),(0,[z941,z1,z2,z4,z5,z6]),(0,[z0,z1,z502,z4,z124,z6])],[(0,[z0,z1,z2,z4,z854,z6]),(0,[z2,z4,z89,z159,z5,z6]),(0,[z0,z1,z237,z752,z5,z6])],[(0,[z0,z920,z2,z4,z5,z6]),(0,[z201,z10,z2,z4,z5,z6]),(0,[z155,z1,z200,z4,z26,z6]),(0,[z0,z1,z2,z4,z71,z87])]],
   [[(0,[z97,z1,z403,z4,z5,z6]),(0,[z0,z1,z2,z4,z942,z6])],[(0,[z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z943]),(0,[z0,z10,z2,z209,z4,z6]),(0,[z0,z944,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z945]),(0,[z156,z0,z2,z568,z5,z6]),(0,[z0,z1,z4,z5,z6,z946])],[(0,[z13,z14,z2,z4,z5,z193]),(0,[z0,z1,z72,z4,z124,z6])],[(0,[z168,z30,z2,z4,z5,z455]),(0,[z0,z1,z2,z4,z947,z6]),(0,[z1,z376,z41,z4,z5,z6]),(0,[z0,z1,z370,z4,z5,z322]),(0,[z0,z1,z46,z4,z5,z334])],[(0,[z129,z284,z41,z4,z5,z6]),(0,[z0,z948,z2,z4,z5,z6]),(0,[z0,z457,z134,z4,z5,z6])],[(0,[z30,z2,z4,z5,z42,z6]),(0,[z0,z30,z46,z4,z5,z119]),(0,[z1,z2,z4,z5,z65,z161]),(0,[z0,z1,z2,z4,z5,z949]),(0,[z0,z389,z252,z4,z124,z6]),(0,[z0,z2,z950,z4,z5,z6])],[(0,[z63,z227,z2,z4,z5,z6]),(0,[z1,z2,z4,z26,z935,z6]),(0,[z0,z2,z4,z5,z96,z54]),(0,[z0,z1,z951,z4,z5,z6])],[(0,[z648,z1,z2,z4,z84,z6]),(0,[z1,z337,z2,z4,z5,z496])],[(0,[z0,z1,z2,z4,z5,z952]),(0,[z0,z10,z2,z241,z4,z5]),(0,[z0,z1,z2,z4,z165,z528]),(0,[z155,z240,z2,z4,z26,z6])],[(0,[z30,z2,z4,z5,z70,z6]),(0,[z140,z2,z24,z4,z5,z6]),(0,[z953,z1,z2,z4,z5,z6])],[(0,[z0,z30,z2,z4,z137,z6]),(0,[z1,z2,z93,z5,z6,z316]),(0,[z954,z1,z2,z4,z5,z6]),(0,[z955,z258,z2,z4,z5,z6])],[(0,[z30,z2,z4,z82,z5,z6]),(0,[z172,z10,z2,z4,z5,z6]),(0,[z245,z10,z2,z4,z5,z6]),(0,[z14,z10,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z956])],[(0,[z0,z10,z2,z4,z103,z6]),(0,[z0,z957,z2,z4,z5,z6]),(0,[z958,z1,z2,z4,z5,z6]),(0,[z0,z1,z252,z4,z124,z496])],[(0,[z201,z2,z4,z5,z6,z127])],[(0,[z462,z30,z2,z4,z5,z6]),(0,[z0,z959,z2,z4,z5,z6]),(0,[z140,z1,z2,z4,z5,z6]),(0,[z0,z2,z4,z5,z6,z960]),(0,[z0,z2,z4,z5,z6,z961]),(0,[z0,z1,z2,z4,z398,z455]),(0,[z0,z1,z2,z4,z962,z6]),(0,[z363,z963,z2,z4,z5,z6]),(0,[z0,z502,z4,z5,z6,z127]),(0,[z1,z2,z4,z5,z6,z964])],[(0,[z0,z10,z2,z4,z42,z6])]],
   [[(0,[z0,z457,z2,z4,z5,z6]),(0,[z965,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z966])],[(0,[z0,z1,z2,z4,z967,z6]),(0,[z155,z1,z2,z4,z26,z426])],[(0,[z156,z0,z2,z110,z5,z6])],[(0,[z0,z1,z2,z4,z146,z161]),(0,[z0,z968,z2,z4,z5,z6]),(1,[z0,z2,z725,z5,z6])],[(0,[z299,z0,z2,z231,z4,z5]),(0,[z0,z2,z4,z5,z6,z969])],[(0,[z169,z1,z2,z4,z5,z6]),(0,[z85,z2,z41,z4,z5,z6]),(0,[z0,z1,z2,z970,z4,z6]),(0,[z19,z1,z2,z4,z146,z6]),(0,[z0,z971,z2,z4,z5,z6])],[(0,[z30,z41,z4,z124,z5,z6]),(0,[z30,z2,z134,z4,z5,z6]),(0,[z0,z1,z2,z4,z708,z6]),(1,[z1,z826,z4,z5,z6]),(0,[z0,z1,z972,z4,z5,z6]),(0,[z0,z1,z2,z4,z175,z87]),(0,[z33,z1,z57,z4,z5,z65]),(0,[z0,z1,z4,z5,z6,z973]),(0,[z0,z1,z46,z4,z5,z119])],[(0,[z0,z974,z2,z4,z5,z6]),(0,[z975,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z131,z390,z5]),(0,[z0,z976,z2,z4,z5,z6])],[(0,[z136,z0,z1,z150,z98,z6]),(0,[z977,z1,z2,z4,z5,z6]),(0,[z0,z978,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z979,z6]),(0,[z43,z169,z2,z4,z304,z6]),(0,[z0,z1,z2,z4,z731,z6])],[(0,[z1,z980,z2,z4,z5,z6]),(0,[z0,z981,z2,z4,z5,z6])],[(0,[z0,z220,z2,z4,z167,z6]),(0,[z363,z1,z2,z4,z215,z6]),(0,[z0,z1,z2,z4,z137,z6]),(0,[z387,z0,z2,z131,z5,z90]),(0,[z0,z1,z2,z4,z982,z6])],[(0,[z0,z1,z983,z4,z5,z6]),(0,[z0,z1,z2,z4,z984,z6]),(0,[z0,z1,z2,z4,z26,z323])],[(0,[z1,z30,z200,z4,z5,z6]),(0,[z0,z197,z2,z218,z5,z6])],[(0,[z0,z30,z2,z4,z398,z6]),(0,[z20,z1,z479,z4,z5,z6]),(0,[z154,z2,z4,z5,z84,z6]),(0,[z0,z1,z2,z395,z6,z81]),(0,[z0,z1,z985,z4,z5,z6])],[(0,[z0,z955,z2,z4,z5,z6]),(0,[z0,z1,z502,z4,z215,z6])]],
   [[(0,[z0,z30,z2,z4,z215,z6]),(0,[z0,z1,z2,z585,z5,z90]),(1,[z13,z0,z2,z4,z103]),(0,[z0,z1,z150,z171,z4,z6]),(0,[z194,z1,z2,z209,z4,z6])],[(0,[z168,z30,z2,z93,z5,z6]),(0,[z0,z30,z502,z4,z5,z6]),(0,[z0,z280,z2,z4,z5,z882])],[(0,[z0,z397,z2,z4,z53,z6]),(0,[z0,z1,z2,z4,z986,z6])],[(0,[z987,z0,z2,z4,z5,z6]),(0,[z0,z1,z2,z204,z6,z81]),(0,[z1,z2,z4,z5,z6,z988]),(0,[z0,z1,z2,z99,z4,z278])],[(0,[z168,z30,z2,z4,z5,z6]),(0,[z0,z10,z2,z4,z5,z323]),(0,[z1,z83,z41,z4,z26,z6]),(0,[z0,z2,z770,z4,z5,z6]),(0,[z0,z1,z989,z4,z5,z6]),(0,[z0,z963,z2,z4,z5,z6]),(0,[z0,z4,z5,z6,z292,z127]),(0,[z0,z1,z2,z131,z5,z90]),(0,[z0,z1,z2,z68,z5,z772])],[(0,[z0,z1,z2,z4,z5,z990])],[(0,[z63,z1,z2,z4,z146,z6]),(0,[z0,z1,z2,z4,z146,z267]),(0,[z0,z991,z2,z4,z5,z6]),(0,[z363,z1,z2,z4,z5,z420]),(0,[z0,z2,z4,z992,z5,z6]),(0,[z211,z0,z1,z2,z4,z165])],[(0,[z0,z1,z2,z4,z993,z6]),(0,[z0,z1,z994,z4,z5,z6])],[(0,[z97,z30,z2,z4,z5,z6]),(0,[z1,z41,z4,z5,z574,z6]),(0,[z0,z995,z2,z4,z5,z6]),(0,[z1,z2,z4,z5,z6,z996]),(0,[z0,z1,z502,z4,z11,z6]),(1,[z211,z0,z2,z4,z165])],[(0,[z0,z1,z2,z4,z5,z997]),(0,[z0,z30,z4,z5,z6,z344]),(0,[z0,z998,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z999,z6]),(0,[z97,z1,z213,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z1000]),(0,[z0,z1,z2,z1001,z4,z6]),(0,[z1,z2,z4,z1002,z5,z6])],[(0,[z254,z30,z2,z4,z5,z6]),(0,[z491,z143,z2,z4,z5,z6]),(0,[z0,z1,z1003,z4,z5,z6]),(0,[z156,z0,z2,z504,z5,z6]),(0,[z0,z1,z2,z4,z5,z1004]),(0,[z0,z1,z442,z4,z124,z6])],[(0,[z30,z12,z2,z4,z5,z87]),(0,[z0,z1,z2,z4,z1005,z6]),(0,[z0,z1,z269,z4,z5,z455]),(0,[z0,z184,z2,z4,z42,z6])],[(0,[z168,z30,z269,z4,z5,z6]),(0,[z1,z2,z4,z1006,z5,z6]),(0,[z0,z1,z2,z4,z1007,z6]),(0,[z1,z2,z4,z1008,z5,z6])],[(0,[z30,z2,z4,z222,z5,z6]),(0,[z0,z1,z271,z4,z5,z47]),(0,[z0,z1,z2,z4,z5,z1009]),(0,[z155,z125,z2,z4,z26,z6])],[(0,[z281,z0,z24,z4,z5,z6]),(0,[z1010,z1,z2,z4,z5,z6]),(0,[z0,z280,z1,z2,z4,z103]),(0,[z0,z1011,z2,z4,z5,z6]),(0,[z0,z2,z4,z5,z6,z1012])],[(0,[z172,z1,z2,z4,z5,z161]),(0,[z0,z1,z2,z4,z398,z6]),(0,[z111,z1,z2,z4,z26,z6]),(0,[z0,z44,z770,z4,z5,z6]),(0,[z156,z0,z2,z725,z5,z6]),(0,[z170,z1,z2,z4,z137,z6])]],
   [[],[(0,[z0,z1,z2,z4,z5,z1013]),(0,[z0,z1,z2,z4,z215,z6]),(0,[z299,z0,z2,z150,z4,z6]),(0,[z387,z0,z4,z5,z6,z344])],[(0,[z0,z10,z2,z4,z5,z322]),(0,[z0,z1,z502,z4,z5,z6]),(0,[z0,z1,z2,z4,z1014,z6]),(0,[z852,z337,z2,z4,z5,z6]),(0,[z387,z0,z349,z4,z5,z6])],[(0,[z0,z30,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z1015,z6]),(0,[z0,z1016,z2,z4,z5,z6])],[(0,[z477,z1,z41,z4,z5,z6]),(0,[z0,z1,z2,z4,z1017,z6])],[(0,[z20,z30,z2,z4,z146,z6]),(0,[z168,z1,z2,z160,z5,z6]),(0,[z1,z2,z93,z417,z5,z6]),(0,[z0,z1,z2,z4,z84,z278])],[(0,[z0,z1018,z2,z4,z5,z6]),(0,[z20,z1,z213,z4,z146,z6]),(0,[z0,z1,z171,z5,z6,z120]),(0,[z0,z1,z252,z611,z4,z6]),(0,[z1,z502,z4,z5,z6,z266])],[(0,[z430,z30,z2,z4,z5,z6]),(0,[z0,z121,z88,z4,z5,z6]),(0,[z0,z1,z1019,z4,z5,z6]),(0,[z0,z1020,z2,z4,z5,z6])],[(0,[z673,z30,z2,z4,z5,z6]),(0,[z19,z239,z2,z4,z84,z6]),(0,[z0,z1,z2,z4,z1021,z6]),(0,[z1022,z1,z2,z4,z5,z6])],[(0,[z97,z1,z2,z4,z5,z6]),(0,[z1,z2,z4,z26,z6,z373]),(0,[z0,z2,z4,z5,z882,z193]),(0,[z0,z1,z12,z4,z5,z47]),(0,[z1023,z1,z2,z4,z5,z6])],[(0,[z32,z30,z2,z4,z5,z87]),(0,[z0,z30,z2,z38,z39,z4]),(0,[z0,z1,z2,z4,z1024,z6]),(0,[z1,z2,z104,z4,z159,z5]),(0,[z0,z1,z4,z5,z6,z344]),(0,[z211,z0,z2,z39,z4,z6])],[(0,[z155,z30,z2,z4,z5,z6]),(0,[z0,z30,z269,z4,z5,z6]),(0,[z312,z0,z3,z4,z5,z6]),(0,[z0,z220,z403,z4,z5,z6]),(0,[z43,z0,z2,z4,z536,z6])],[(0,[z168,z10,z2,z272,z5,z6]),(0,[z0,z1,z2,z4,z5,z1025]),(0,[z0,z1026,z2,z4,z5,z6])],[(0,[z1027,z1,z2,z4,z5,z6]),(0,[z0,z770,z24,z4,z5,z6]),(0,[z0,z1,z2,z4,z1028,z6])],[(0,[z505,z30,z2,z4,z5,z6]),(0,[z136,z0,z1,z231,z98,z5]),(0,[z92,z258,z2,z4,z5,z6]),(0,[z0,z2,z112,z6,z127,z81])],[(0,[z0,z1029,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z426]),(0,[z0,z2,z4,z53,z854,z6])]],
   [[(0,[z140,z30,z2,z4,z5,z6]),(0,[z208,z0,z4,z5,z6,z292])],[(0,[z143,z30,z2,z4,z5,z6]),(0,[z0,z10,z2,z4,z5,z496]),(0,[z405,z1,z2,z4,z26,z6]),(0,[z33,z1,z2,z4,z5,z747])],[(0,[z0,z1,z2,z4,z5,z1030])],[(0,[z136,z0,z10,z98,z5,z6]),(0,[z0,z1,z2,z4,z5,z1031])],[(1,[z744,z2,z4,z5,z6]),(0,[z136,z0,z325,z98,z5,z6]),(0,[z0,z1032,z2,z4,z5,z6])],[(0,[z30,z2,z4,z84,z6,z81]),(0,[z0,z1,z2,z4,z1033,z6]),(0,[z10,z445,z2,z4,z5,z6]),(0,[z0,z10,z2,z80,z4,z5]),(0,[z0,z1034,z2,z4,z5,z6]),(0,[z0,z1,z2,z1035,z4,z6]),(0,[z170,z1,z2,z4,z215,z6]),(0,[z0,z1,z2,z112,z278,z81]),(0,[z211,z0,z2,z4,z165,z173])],[(0,[z63,z1,z2,z4,z42,z6]),(0,[z10,z258,z2,z4,z5,z6]),(0,[z21,z2,z41,z4,z5,z6]),(0,[z1036,z0,z2,z4,z5,z6]),(0,[z0,z44,z177,z4,z5,z6]),(0,[z136,z0,z1,z150,z4,z6]),(0,[z172,z877,z2,z4,z5,z6])],[(0,[z169,z30,z2,z4,z5,z6]),(0,[z170,z30,z2,z4,z5,z6]),(0,[z0,z10,z2,z4,z358,z5]),(0,[z168,z1,z2,z228,z5,z6]),(0,[z0,z2,z231,z4,z89,z5]),(0,[z0,z1,z4,z124,z6,z45])],[(0,[z648,z30,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z126,z87]),(0,[z0,z1,z2,z4,z722,z6])],[(0,[z33,z30,z134,z4,z5,z6]),(0,[z405,z10,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z1037,z6]),(0,[z0,z1,z2,z4,z5,z1038]),(0,[z156,z36,z2,z4,z5,z6]),(0,[z1039,z1,z2,z4,z5,z6])],[(0,[z0,z227,z403,z4,z5,z6]),(0,[z0,z1,z83,z4,z296,z6]),(0,[z0,z1,z2,z4,z1040,z6]),(0,[z170,z1018,z2,z4,z5,z6]),(0,[z0,z1,z2,z112,z80,z81]),(0,[z2,z4,z5,z6,z127,z266])],[(0,[z0,z1,z2,z1041,z4,z5]),(0,[z1042,z0,z2,z4,z5,z6]),(0,[z32,z1,z2,z4,z5,z87]),(0,[z156,z356,z2,z4,z5,z6]),(0,[z0,z1,z2,z38,z39,z4])],[(0,[z0,z1,z269,z4,z5,z6]),(0,[z1,z4,z5,z6,z292,z266]),(0,[z0,z1043,z2,z4,z5,z6]),(0,[z0,z2,z4,z5,z6,z1044])],[],[(0,[z30,z2,z4,z5,z6,z322]),(0,[z43,z0,z2,z4,z298,z6]),(0,[z0,z1,z1045,z4,z5,z6]),(0,[z43,z0,z1,z2,z4,z358]),(0,[z1046,z0,z2,z4,z5,z6])],[(0,[z1047,z1,z2,z4,z5,z6]),(0,[z43,z0,z2,z4,z304,z6]),(0,[z0,z1,z46,z289,z4,z5])]],
   [[(0,[z1,z30,z2,z4,z146,z6]),(0,[z1,z30,z2,z4,z5,z322])],[(0,[z0,z1048,z2,z4,z5,z6]),(0,[z0,z1049,z2,z4,z5,z6]),(0,[z0,z1050,z2,z4,z5,z6]),(0,[z1,z349,z4,z5,z6,z106])],[(0,[z168,z30,z2,z4,z398,z6]),(0,[z0,z1,z2,z4,z1051,z6]),(0,[z245,z135,z2,z52,z5,z6]),(0,[z170,z1,z4,z98,z5,z6]),(0,[z1052,z1,z2,z4,z5,z6])],[(0,[z0,z30,z2,z4,z1053,z5]),(0,[z0,z2,z4,z1054,z5,z6]),(0,[z0,z220,z2,z4,z5,z455]),(0,[z0,z2,z4,z5,z6,z1055]),(0,[z169,z2,z24,z4,z5,z6])],[(0,[z168,z1,z2,z272,z167,z6]),(0,[z33,z1,z2,z4,z42,z65]),(0,[z0,z2,z4,z89,z5,z6])],[(0,[z33,z30,z2,z4,z5,z6]),(0,[z30,z2,z116,z4,z5,z6]),(0,[z651,z10,z2,z4,z5,z6]),(0,[z424,z10,z2,z4,z5,z6]),(0,[z602,z1,z2,z4,z5,z65]),(0,[z0,z92,z2,z4,z5,z6])],[(0,[z30,z2,z4,z339,z5,z6]),(0,[z0,z30,z2,z131,z5,z90]),(0,[z281,z0,z770,z4,z5,z6]),(0,[z0,z1,z2,z4,z137,z420])],[(0,[z0,z101,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z1056,z6]),(0,[z0,z1,z1057,z4,z5,z6]),(0,[z172,z1,z2,z4,z126,z6])],[(0,[z170,z1,z2,z4,z5,z6]),(0,[z0,z1058,z2,z4,z5,z6]),(0,[z1,z134,z4,z5,z65,z6]),(0,[z0,z1,z2,z4,z1059,z5])],[(0,[z155,z959,z2,z4,z5,z6]),(0,[z0,z1060,z2,z4,z5,z6])],[(0,[z0,z1061,z2,z4,z5,z6]),(0,[z0,z1062,z2,z4,z5,z6]),(0,[z1063,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z165,z566]),(1,[z932,z2,z4,z5,z6])],[(0,[z30,z2,z4,z5,z6,z87]),(0,[z30,z142,z2,z4,z5,z6]),(0,[z0,z1,z2,z817,z4,z5]),(0,[z584,z1,z41,z4,z5,z6]),(0,[z1,z258,z2,z4,z126,z6])],[(0,[z170,z1,z4,z5,z47,z6]),(0,[z0,z1,z83,z372,z4,z6])],[(0,[z30,z2,z93,z4,z5,z6]),(0,[z1,z2,z4,z5,z747,z87])],[(0,[z0,z1064,z2,z4,z5,z6]),(0,[z0,z1065,z2,z4,z5,z6]),(0,[z194,z1,z2,z4,z5,z87]),(0,[z0,z79,z2,z4,z5,z323]),(0,[z201,z827,z2,z4,z5,z6])],[(0,[z0,z30,z200,z4,z5,z6]),(0,[z56,z0,z2,z132,z5,z6]),(0,[z0,z1066,z2,z4,z5,z6])]],
   [[(0,[z0,z30,z2,z1067,z4,z6]),(0,[z0,z1068,z2,z4,z5,z6]),(0,[z0,z1,z2,z231,z305,z4])],[(0,[z201,z1,z2,z4,z84,z6]),(0,[z299,z0,z2,z305,z4,z6]),(0,[z0,z1,z2,z131,z4,z126]),(0,[z1069,z1,z2,z4,z5,z6])],[(0,[z30,z2,z365,z4,z5,z6]),(0,[z0,z227,z2,z4,z5,z455]),(0,[z0,z1070,z2,z4,z5,z6]),(0,[z1071,z1,z2,z4,z5,z6]),(0,[z1,z1072,z2,z4,z5,z6])],[(0,[z0,z1073,z2,z4,z5,z6]),(0,[z0,z1074,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z1075])],[(0,[z0,z1,z2,z4,z1053,z5]),(0,[z0,z10,z252,z4,z124,z6]),(0,[z168,z1,z2,z272,z5,z174]),(0,[z0,z280,z2,z4,z5,z96])],[(0,[z0,z30,z2,z4,z5,z1076]),(0,[z1077,z1,z2,z4,z5,z6])],[(0,[z0,z1,z2,z1078,z4,z6])],[(0,[z0,z30,z2,z541,z4,z6])],[(1,[z30,z2,z4,z5,z161]),(0,[z30,z2,z4,z5,z6,z373]),(0,[z10,z356,z2,z4,z5,z6]),(0,[z0,z1,z1079,z4,z5,z6]),(0,[z0,z1,z2,z4,z1080,z6])],[(0,[z63,z1,z2,z4,z5,z322]),(0,[z0,z1,z237,z133,z5,z6]),(0,[z0,z2,z4,z53,z6,z378]),(0,[z387,z0,z2,z209,z4,z6])],[(0,[z121,z30,z41,z4,z5,z6]),(0,[z0,z10,z370,z4,z5,z6]),(0,[z0,z1,z213,z104,z4,z5]),(0,[z0,z1,z4,z5,z6,z1081])],[(0,[z0,z30,z12,z4,z5,z47]),(0,[z97,z1016,z2,z4,z5,z6]),(0,[z211,z0,z2,z4,z165,z5])],[(0,[z1082,z1,z2,z4,z5,z6]),(0,[z0,z2,z52,z5,z6,z530]),(0,[z0,z1,z2,z4,z5,z1083])],[(0,[z30,z2,z4,z25,z84,z6]),(0,[z0,z30,z349,z4,z5,z6]),(0,[z0,z1,z2,z4,z1084,z6]),(0,[z0,z280,z2,z4,z5,z315])],[(0,[z0,z30,z2,z4,z5,z420]),(0,[z0,z30,z83,z4,z11,z6]),(0,[z20,z85,z2,z4,z5,z6])],[(0,[z30,z46,z2,z4,z5,z87]),(0,[z1,z2,z4,z5,z935,z6])]],
   [[(0,[z0,z30,z2,z4,z583,z6]),(0,[z1,z30,z2,z4,z42,z6]),(0,[z20,z284,z2,z4,z5,z6]),(0,[z0,z1,z200,z4,z5,z6]),(0,[z0,z1085,z2,z4,z5,z6]),(0,[z1,z2,z4,z5,z65,z747]),(0,[z170,z1,z46,z4,z5,z6]),(0,[z0,z1,z4,z752,z5,z6])],[(0,[z0,z30,z2,z4,z5,z426]),(0,[z364,z30,z2,z4,z5,z6]),(0,[z0,z1,z2,z1067,z4,z6]),(0,[z1086,z1,z2,z4,z5,z6])],[(0,[z1087,z2,z4,z5,z6,z106])],[(0,[z0,z1,z2,z4,z5,z1088])],[(0,[z0,z30,z57,z4,z5,z6]),(0,[z0,z220,z2,z4,z5,z6]),(0,[z1,z2,z4,z5,z65,z455]),(0,[z0,z1089,z2,z4,z5,z6]),(0,[z0,z1,z2,z99,z4,z323])],[(0,[z1,z41,z4,z91,z5,z6]),(0,[z155,z1,z2,z4,z26,z322]),(0,[z0,z1,z2,z4,z5,z1090]),(0,[z0,z1,z4,z722,z11,z6]),(0,[z0,z1,z502,z4,z5,z278]),(0,[z1,z2,z4,z71,z6,z106])],[(0,[z30,z2,z4,z5,z6,z412]),(0,[z0,z30,z2,z4,z5,z278]),(0,[z30,z2,z414,z4,z5,z6]),(0,[z564,z30,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z1076]),(0,[z0,z1,z83,z4,z215,z6]),(0,[z1091,z1,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z5,z1092]),(0,[z0,z1093,z2,z4,z5,z6]),(0,[z1094,z1,z2,z4,z5,z6]),(1,[z0,z1,z2,z5,z772])],[(0,[z0,z1,z2,z541,z4,z6]),(0,[z0,z2,z4,z5,z96,z247]),(0,[z1095,z0,z2,z4,z5,z6])],[(0,[z0,z240,z2,z4,z5,z6]),(0,[z155,z30,z2,z4,z5,z426]),(0,[z36,z44,z2,z4,z5,z6]),(0,[z0,z2,z4,z103,z96,z6]),(0,[z1096,z1,z2,z4,z5,z6])],[(0,[z0,z143,z2,z4,z5,z267]),(0,[z0,z1,z269,z4,z398,z6]),(0,[z0,z1,z2,z104,z4,z5]),(0,[z1097,z0,z2,z4,z5,z6])],[(0,[z0,z1,z1098,z4,z5,z6]),(0,[z0,z1,z1099,z4,z5,z6]),(0,[z0,z2,z4,z5,z96,z882]),(0,[z0,z79,z2,z4,z5,z496])],[(0,[z0,z73,z2,z4,z5,z315])],[(0,[z10,z744,z2,z4,z5,z6]),(0,[z0,z1,z41,z150,z4,z6]),(0,[z0,z1,z2,z4,z103,z6]),(1,[z0,z1,z752,z5,z6]),(0,[z136,z0,z1,z390,z5,z6]),(0,[z1,z2,z4,z1100,z5,z6])],[(0,[z0,z1,z349,z4,z5,z6]),(0,[z0,z2,z150,z4,z89,z6]),(0,[z211,z0,z2,z38,z4,z5])],[(0,[z0,z1,z2,z4,z1101,z6]),(0,[z0,z1102,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z420]),(0,[z1,z2,z4,z1103,z5,z6]),(0,[z0,z1104,z2,z4,z5,z6]),(0,[z0,z1,z83,z4,z11,z6])]],
   [[(0,[z491,z10,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z1105])],[(0,[z0,z10,z2,z4,z1106,z5]),(0,[z0,z1107,z2,z4,z5,z6]),(0,[z0,z1,z1108,z4,z5,z6]),(0,[z43,z0,z2,z4,z696,z6]),(0,[z0,z1,z2,z4,z583,z6]),(1,[z0,z1,z4,z5,z922]),(0,[z194,z1109,z2,z4,z5,z6])],[(0,[z0,z1,z2,z1110,z4,z6]),(0,[z0,z1,z2,z39,z4,z627]),(0,[z0,z1,z2,z4,z1111,z6]),(0,[z0,z1,z2,z112,z731,z6])],[(0,[z0,z227,z2,z4,z5,z6]),(0,[z393,z30,z2,z4,z5,z6]),(0,[z0,z1,z4,z5,z47,z420]),(0,[z405,z79,z2,z4,z5,z6])],[(0,[z281,z491,z24,z4,z5,z6]),(1,[z0,z770,z4,z5,z6]),(0,[z208,z2,z4,z5,z6,z266])],[(0,[z0,z1,z57,z4,z5,z6]),(0,[z275,z1,z2,z860,z5,z6]),(0,[z258,z784,z2,z4,z5,z6])],[(0,[z1,z46,z41,z4,z5,z65]),(0,[z0,z1,z2,z4,z84,z323])],[(0,[z0,z1,z2,z4,z5,z278]),(0,[z0,z349,z4,z5,z6,z77])],[(0,[z0,z85,z2,z4,z5,z6]),(0,[z136,z1,z159,z98,z5,z6])],[(0,[z0,z415,z2,z226,z5,z6]),(0,[z30,z258,z2,z4,z5,z6]),(0,[z0,z1,z2,z1112,z4,z5]),(0,[z0,z2,z4,z5,z278,z127])],[(0,[z0,z1113,z2,z4,z5,z6])],[(0,[z30,z2,z454,z4,z5,z6]),(0,[z55,z10,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z1114]),(0,[z0,z227,z269,z4,z5,z6]),(0,[z14,z457,z2,z4,z5,z6]),(0,[z136,z0,z1,z305,z98,z6])],[(0,[z0,z135,z2,z725,z5,z6]),(0,[z97,z2,z4,z89,z5,z6])],[(0,[z0,z30,z2,z68,z128,z5]),(0,[z0,z115,z1,z2,z4,z358]),(0,[z0,z1,z83,z4,z722,z6]),(0,[z0,z1,z349,z68,z4,z5])],[(0,[z0,z1115,z2,z4,z5,z6]),(0,[z0,z1116,z2,z4,z5,z6]),(0,[z1117,z0,z2,z4,z5,z6])],[(0,[z30,z2,z4,z319,z5,z6]),(0,[z0,z1118,z2,z4,z5,z6])]],
   [[(0,[z554,z30,z2,z93,z5,z6]),(0,[z0,z1,z2,z4,z1119,z6]),(0,[z0,z2,z4,z1120,z5,z6]),(0,[z0,z1,z306,z2,z4,z165])],[(0,[z30,z2,z200,z4,z5,z6])],[(0,[z0,z30,z2,z4,z146,z6]),(0,[z1121,z1,z2,z4,z5,z6]),(0,[z0,z396,z2,z4,z126,z6])],[(0,[z164,z30,z2,z4,z5,z6]),(0,[z170,z1,z2,z4,z5,z420]),(0,[z1122,z2,z4,z5,z6,z266])],[(0,[z0,z294,z260,z4,z5,z6]),(0,[z0,z1123,z2,z4,z5,z6]),(0,[z0,z457,z57,z4,z5,z6]),(0,[z13,z0,z2,z4,z5,z882]),(0,[z2,z4,z5,z6,z77,z106])],[(0,[z0,z1,z2,z4,z5,z1124]),(0,[z0,z325,z2,z4,z5,z270]),(0,[z0,z1125,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z124,z278]),(0,[z0,z1,z2,z4,z71,z47])],[(0,[z10,z337,z2,z4,z5,z6]),(0,[z0,z1,z2,z112,z526,z6])],[(0,[z0,z1126,z2,z4,z5,z6]),(0,[z0,z1127,z2,z4,z5,z6]),(0,[z0,z1,z46,z4,z5,z420]),(0,[z1,z337,z4,z124,z5,z6])],[(0,[z0,z1128,z2,z4,z5,z6]),(0,[z0,z2,z4,z5,z6,z1129]),(0,[z0,z1,z4,z5,z6,z1130]),(1,[z0,z1,z2,z4,z710])],[],[(0,[z0,z1131,z2,z4,z5,z6])],[],[(0,[z0,z1132,z2,z4,z5,z6])],[(0,[z170,z1,z83,z4,z5,z6])],[(0,[z0,z1,z2,z4,z5,z1133]),(0,[z0,z125,z2,z4,z5,z6]),(0,[z10,z2,z4,z5,z6,z106]),(0,[z1,z2,z4,z5,z65,z547]),(0,[z0,z1,z2,z68,z128,z5])],[(0,[z0,z30,z2,z1134,z4,z5]),(0,[z0,z30,z2,z4,z1084,z6]),(0,[z0,z1,z2,z1135,z4,z6]),(0,[z1136,z1,z2,z4,z5,z6]),(0,[z1,z2,z209,z4,z6,z106])]],
   [[(0,[z0,z1,z2,z4,z5,z1137]),(0,[z0,z1,z1138,z4,z5,z6]),(0,[z0,z1,z2,z4,z165,z302])],[(0,[z0,z2,z4,z5,z6,z1139]),(0,[z13,z0,z1,z2,z4,z103]),(0,[z97,z299,z2,z4,z5,z6]),(0,[z201,z1,z502,z4,z5,z6]),(0,[z0,z1,z349,z131,z5,z90])],[(0,[z201,z30,z2,z4,z5,z6]),(0,[z0,z220,z2,z4,z398,z6])],[(0,[z149,z30,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z146,z6]),(0,[z1140,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z124,z323]),(0,[z208,z0,z502,z4,z5,z6]),(0,[z0,z1141,z2,z4,z5,z6])],[(0,[z0,z30,z2,z1142,z4,z5]),(0,[z0,z30,z2,z209,z4,z6])],[(0,[z212,z30,z2,z4,z5,z6]),(0,[z1,z271,z2,z4,z5,z65]),(0,[z0,z1,z2,z4,z5,z1143]),(0,[z0,z1,z370,z4,z26,z6]),(0,[z0,z1,z2,z440,z128,z5])],[(0,[z0,z10,z2,z112,z6,z81])],[(0,[z0,z30,z2,z1144,z4,z6]),(0,[z0,z1,z4,z5,z922,z119]),(0,[z0,z1,z2,z1145,z4,z5])],[(0,[z19,z1,z2,z4,z935,z6]),(0,[z1146,z1,z2,z4,z5,z6])],[(0,[z1147,z1,z2,z4,z5,z6]),(0,[z0,z2,z305,z4,z89,z6]),(0,[z0,z1148,z2,z4,z5,z6])],[(0,[z30,z2,z218,z4,z5,z6]),(0,[z155,z30,z200,z4,z5,z6]),(0,[z0,z143,z2,z4,z5,z161]),(0,[z0,z1,z2,z1149,z4,z5]),(0,[z0,z1,z2,z131,z5,z632])],[(0,[z0,z30,z2,z241,z4,z5]),(0,[z405,z1,z2,z4,z84,z6]),(0,[z85,z2,z4,z5,z6,z87]),(0,[z0,z2,z4,z71,z6,z77])],[(0,[z0,z30,z2,z104,z4,z5]),(0,[z0,z10,z2,z150,z4,z6]),(0,[z0,z1,z4,z5,z6,z1150])],[(0,[z30,z2,z4,z5,z87,z90]),(0,[z0,z1151,z2,z4,z5,z6]),(0,[z155,z1,z370,z4,z26,z6])],[(0,[z172,z30,z2,z4,z5,z6]),(0,[z1,z415,z2,z93,z5,z6]),(0,[z245,z30,z2,z4,z5,z6]),(0,[z14,z30,z2,z4,z5,z6]),(0,[z0,z1,z2,z1152,z4,z6]),(0,[z0,z1,z200,z4,z5,z426]),(0,[z405,z927,z2,z4,z5,z6])],[(0,[z0,z30,z2,z4,z103,z6]),(0,[z154,z2,z41,z4,z5,z6]),(0,[z1153,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z215,z420]),(0,[z1154,z1,z2,z4,z5,z6])]],
   [[(0,[z30,z2,z4,z5,z6,z528]),(0,[z0,z1,z2,z1134,z4,z5]),(0,[z19,z10,z2,z4,z84,z6]),(0,[z0,z1,z2,z4,z5,z1155]),(0,[z0,z1,z2,z1156,z4,z5]),(0,[z0,z2,z4,z5,z6,z1157])],[(0,[z0,z121,z307,z4,z5,z6]),(0,[z0,z227,z2,z4,z398,z6]),(0,[z1,z2,z4,z5,z278,z266])],[(0,[z0,z30,z2,z4,z42,z6]),(0,[z0,z10,z2,z4,z165,z173]),(0,[z97,z1,z2,z104,z4,z5]),(0,[z0,z1,z2,z99,z524,z6]),(0,[z0,z1,z2,z4,z1158,z6])],[(0,[z201,z1,z2,z4,z5,z6]),(0,[z1159,z1,z2,z4,z5,z6])],[(0,[z660,z30,z2,z4,z5,z6])],[(0,[z0,z1,z2,z1142,z4,z5]),(0,[z1,z2,z93,z5,z6,z693]),(0,[z208,z0,z2,z4,z5,z6]),(0,[z1160,z2,z4,z159,z5,z6]),(0,[z0,z1,z2,z209,z4,z6])],[(0,[z227,z30,z2,z4,z5,z6]),(0,[z457,z30,z2,z4,z5,z6]),(0,[z19,z154,z2,z4,z84,z6])],[(0,[z168,z1,z403,z272,z5,z6]),(0,[z0,z240,z2,z4,z5,z426]),(0,[z0,z1,z134,z4,z42,z6]),(0,[z0,z485,z1,z2,z4,z165]),(0,[z0,z1,z83,z4,z545,z6])],[(0,[z0,z1,z2,z1144,z4,z6])],[(0,[z30,z2,z410,z4,z5,z6]),(0,[z408,z30,z2,z4,z5,z6]),(0,[z0,z2,z52,z5,z6,z558]),(0,[z0,z179,z2,z4,z5,z270]),(0,[z0,z1,z349,z4,z5,z420]),(0,[z0,z1,z2,z752,z5,z6]),(0,[z0,z1,z12,z4,z583,z47])],[(0,[z0,z1,z2,z4,z5,z1161]),(0,[z20,z1,z383,z4,z5,z6]),(0,[z0,z1,z4,z5,z278,z292])],[(0,[z1160,z0,z2,z4,z5,z6]),(0,[z275,z1,z2,z116,z5,z6]),(0,[z0,z1162,z2,z4,z5,z6]),(0,[z0,z1163,z2,z4,z5,z6]),(0,[z0,z1,z502,z112,z4,z6])],[(0,[z168,z85,z2,z4,z5,z6]),(0,[z0,z1,z2,z241,z4,z5]),(0,[z0,z1164,z2,z4,z5,z6]),(0,[z0,z1165,z2,z4,z5,z6])],[(0,[z63,z143,z2,z4,z5,z6]),(0,[z1166,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z772])],[(0,[z168,z284,z2,z4,z5,z6]),(0,[z0,z1167,z2,z4,z5,z6])],[(0,[z245,z1,z2,z4,z5,z6]),(0,[z14,z1,z2,z4,z5,z6]),(1,[z30,z403,z4,z5,z6]),(0,[z30,z2,z565,z4,z5,z6]),(0,[z13,z0,z2,z4,z5,z199]),(0,[z172,z1,z2,z4,z5,z6]),(0,[z0,z220,z269,z4,z5,z6]),(0,[z0,z1,z2,z4,z71,z65])]],
   [[(0,[z0,z1,z2,z4,z11,z278]),(0,[z0,z1,z2,z1168,z4,z6])],[(0,[z0,z10,z2,z4,z5,z174]),(0,[z233,z0,z366,z4,z5,z6]),(0,[z1,z2,z4,z5,z6,z1169]),(0,[z0,z1,z2,z1170,z4,z6]),(0,[z0,z2,z4,z5,z6,z1171])],[(0,[z18,z1,z41,z4,z5,z6]),(0,[z0,z143,z2,z4,z331,z6]),(0,[z0,z1,z2,z4,z1172,z6]),(0,[z0,z1173,z2,z4,z5,z6]),(0,[z0,z1174,z2,z4,z5,z6]),(0,[z1175,z0,z2,z4,z5,z6])],[(0,[z1,z258,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z42,z6]),(0,[z0,z1,z1176,z4,z5,z6])],[(0,[z0,z10,z237,z171,z5,z6]),(0,[z1122,z0,z2,z4,z5,z6]),(0,[z0,z2,z4,z1177,z5,z6]),(0,[z0,z1178,z2,z4,z5,z6])],[(0,[z30,z2,z4,z5,z298,z6]),(0,[z30,z2,z585,z4,z5,z6]),(0,[z0,z1,z2,z4,z126,z65]),(0,[z1179,z1,z2,z4,z5,z6]),(0,[z0,z115,z2,z4,z854,z6]),(0,[z13,z0,z2,z4,z5,z193])],[(0,[z1180,z0,z2,z4,z5,z6]),(0,[z0,z1181,z2,z4,z5,z6]),(0,[z0,z1,z2,z38,z4,z342])],[(0,[z30,z2,z594,z4,z5,z6]),(0,[z0,z30,z2,z4,z5,z323]),(0,[z129,z10,z41,z4,z5,z6]),(0,[z1,z258,z4,z5,z47,z6])],[(0,[z156,z140,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z165,z225])],[(0,[z43,z0,z2,z4,z854,z6]),(0,[z0,z1,z2,z4,z5,z1182])],[(1,[z43,z0,z2,z4,z358])],[(0,[z43,z0,z2,z4,z210,z6]),(0,[z0,z1,z2,z38,z27,z4]),(0,[z0,z1,z2,z131,z4,z71])],[(0,[z0,z1,z370,z4,z84,z6]),(0,[z2,z4,z719,z159,z5,z6]),(0,[z299,z2,z4,z159,z5,z6])],[(0,[z0,z284,z2,z4,z5,z6]),(0,[z20,z143,z213,z4,z5,z6]),(1,[z0,z2,z4,z5,z882]),(0,[z363,z1183,z2,z4,z5,z6]),(0,[z0,z1184,z2,z4,z5,z6]),(0,[z0,z1,z12,z702,z4,z5]),(0,[z0,z1185,z2,z4,z5,z6])],[(0,[z0,z1,z1186,z4,z5,z6]),(0,[z1187,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z11,z323])],[(0,[z30,z41,z4,z98,z5,z6]),(0,[z168,z1,z2,z272,z5,z455]),(0,[z0,z1,z2,z4,z5,z1188]),(0,[z0,z875,z2,z4,z5,z6]),(0,[z0,z1189,z2,z4,z5,z6])]],
   [[(0,[z643,z30,z2,z4,z5,z6]),(0,[z30,z2,z616,z4,z5,z6]),(0,[z0,z10,z2,z4,z5,z267]),(0,[z0,z1190,z2,z4,z5,z6]),(0,[z0,z92,z12,z4,z5,z47])],[(0,[z0,z10,z2,z4,z5,z270]),(0,[z0,z2,z4,z53,z6,z623]),(0,[z0,z1,z2,z631,z25,z6]),(0,[z0,z1,z607,z4,z5,z119]),(0,[z932,z1,z2,z4,z5,z6])],[(0,[z30,z2,z4,z5,z6,z622]),(0,[z0,z10,z2,z231,z4,z5]),(0,[z32,z85,z2,z4,z5,z87]),(0,[z0,z457,z2,z4,z42,z6]),(0,[z299,z0,z2,z4,z5,z6]),(0,[z13,z169,z2,z4,z5,z6]),(0,[z1191,z1,z2,z4,z5,z6]),(0,[z0,z1,z572,z4,z5,z47])],[(0,[z0,z1192,z2,z4,z5,z6]),(0,[z1193,z0,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z1194,z6]),(0,[z1195,z0,z2,z4,z5,z6]),(0,[z0,z1109,z2,z4,z5,z6]),(0,[z1,z2,z4,z5,z6,z1196])],[(0,[z33,z30,z2,z4,z42,z6]),(0,[z1,z2,z4,z935,z84,z6])],[(0,[z0,z239,z2,z4,z5,z6]),(0,[z0,z30,z2,z4,z5,z322]),(0,[z0,z1197,z2,z4,z5,z6]),(0,[z0,z1,z1198,z4,z5,z6]),(0,[z0,z1,z1199,z4,z5,z6]),(0,[z0,z1,z46,z265,z4,z5]),(0,[z0,z92,z2,z4,z583,z6]),(0,[z0,z2,z209,z4,z6,z77])],[(0,[z30,z2,z4,z5,z6,z630]),(0,[z0,z1,z2,z4,z175,z65]),(0,[z0,z1200,z2,z4,z5,z6])],[(1,[z30,z2,z4,z5,z455]),(0,[z0,z290,z2,z4,z5,z161]),(0,[z0,z1,z46,z4,z5,z196]),(0,[z0,z1,z2,z4,z1201,z6]),(0,[z275,z285,z2,z93,z5,z6]),(0,[z1,z2,z112,z6,z266,z81])],[(0,[z0,z10,z4,z5,z6,z292]),(0,[z0,z1,z2,z4,z5,z323]),(0,[z0,z1202,z2,z4,z5,z6]),(0,[z0,z1203,z2,z4,z5,z6])],[(0,[z30,z41,z4,z5,z47,z6]),(0,[z33,z30,z57,z4,z5,z6]),(0,[z30,z337,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z167,z174]),(0,[z0,z2,z4,z1204,z5,z6])],[(0,[z111,z30,z2,z4,z5,z6]),(0,[z36,z10,z2,z4,z5,z6]),(0,[z1,z1205,z2,z4,z5,z6]),(0,[z0,z1206,z2,z4,z5,z6])],[(0,[z30,z2,z645,z4,z5,z6]),(0,[z111,z1,z213,z4,z5,z6]),(0,[z194,z1,z2,z4,z5,z65]),(0,[z1,z258,z46,z4,z5,z6])],[(0,[z0,z30,z2,z1207,z4,z6]),(0,[z0,z10,z2,z305,z4,z6]),(0,[z0,z125,z2,z4,z5,z426]),(0,[z0,z1,z2,z1208,z4,z5])],[(0,[z1209,z1,z2,z4,z5,z6])],[(0,[z33,z10,z2,z4,z5,z65]),(0,[z0,z1,z83,z4,z642,z6]),(0,[z0,z1,z2,z4,z126,z47]),(0,[z1,z4,z5,z6,z344,z106])],[(0,[z168,z30,z2,z272,z5,z6]),(0,[z0,z1,z2,z4,z5,z1210]),(0,[z0,z10,z2,z4,z71,z6])]],
   [[(0,[z30,z2,z366,z4,z5,z6]),(0,[z0,z1,z2,z4,z1211,z6]),(0,[z211,z0,z2,z4,z5,z6]),(0,[z0,z2,z4,z854,z304,z6])],[(0,[z30,z2,z4,z165,z5,z87]),(0,[z30,z2,z4,z5,z6,z106]),(0,[z201,z1,z2,z4,z398,z6]),(0,[z0,z1,z2,z1212,z4,z6]),(0,[z0,z1213,z2,z4,z5,z6]),(0,[z0,z1214,z2,z4,z5,z6])],[(0,[z0,z1215,z2,z4,z5,z6]),(0,[z0,z1216,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z1217,z6])],[(0,[z0,z1183,z2,z4,z5,z6])],[(0,[z0,z30,z2,z4,z5,z496]),(0,[z0,z1,z41,z4,z5,z267]),(1,[z1,z2,z4,z5,z747]),(0,[z1218,z1,z2,z4,z5,z6]),(0,[z0,z1219,z2,z4,z5,z6])],[(0,[z1,z356,z2,z4,z5,z6]),(0,[z0,z10,z2,z4,z126,z6]),(0,[z1,z403,z4,z5,z65,z6]),(0,[z0,z1,z2,z4,z1220,z6])],[(0,[z0,z1,z1221,z4,z5,z6]),(0,[z959,z30,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z322]),(0,[z1222,z1,z2,z4,z5,z6]),(0,[z1223,z1,z2,z4,z5,z6]),(0,[z0,z2,z4,z5,z6,z1224])],[(0,[z0,z1,z1225,z4,z5,z6]),(0,[z0,z1,z1226,z4,z5,z6]),(0,[z0,z1,z502,z80,z4,z5])],[(0,[z599,z30,z2,z4,z5,z6]),(0,[z0,z30,z2,z80,z4,z5]),(0,[z0,z1227,z2,z4,z5,z6]),(0,[z0,z1,z2,z634,z39,z4]),(0,[z0,z240,z200,z4,z5,z6])],[(0,[z30,z83,z41,z4,z5,z6]),(0,[z0,z1228,z2,z4,z5,z6])],[(0,[z0,z30,z2,z4,z358,z5]),(0,[z0,z290,z2,z4,z5,z267]),(0,[z43,z0,z2,z241,z4,z304]),(0,[z0,z1,z2,z570,z39,z4]),(0,[z0,z2,z4,z5,z6,z1229]),(0,[z0,z1,z2,z4,z1230,z6]),(0,[z0,z1231,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z5,z1232]),(0,[z0,z1233,z2,z4,z5,z6]),(0,[z0,z1234,z2,z4,z5,z6])],[(1,[z30,z134,z4,z5,z6]),(0,[z405,z30,z2,z4,z5,z6]),(0,[z1235,z1,z2,z4,z5,z6])],[(0,[z352,z30,z2,z4,z5,z6]),(0,[z0,z1,z2,z1207,z4,z6]),(0,[z168,z1,z2,z860,z5,z6]),(0,[z33,z85,z2,z4,z5,z6]),(0,[z0,z2,z52,z725,z5,z6]),(0,[z1,z1236,z2,z4,z5,z6]),(0,[z1237,z1,z2,z4,z5,z6]),(0,[z1238,z0,z2,z4,z5,z6])],[(0,[z0,z1239,z2,z4,z5,z6]),(0,[z364,z1,z2,z4,z5,z87]),(0,[z0,z389,z2,z4,z5,z6]),(0,[z0,z2,z4,z1240,z5,z6]),(0,[z0,z2,z131,z5,z77,z90])],[(0,[z62,z0,z2,z4,z256,z6]),(0,[z0,z1,z349,z209,z4,z6])]],
   [[(0,[z0,z1,z2,z4,z1241,z6]),(0,[z168,z1,z2,z272,z5,z6]),(0,[z85,z2,z93,z4,z5,z6]),(0,[z0,z1,z1242,z4,z5,z6])],[(0,[z30,z2,z4,z5,z84,z6]),(0,[z0,z2,z4,z5,z6,z1243]),(0,[z1244,z1,z2,z4,z5,z6]),(0,[z136,z0,z1,z98,z5,z270])],[],[(0,[z20,z30,z41,z4,z5,z6]),(0,[z0,z1,z2,z1245,z4,z5])],[(0,[z0,z10,z2,z4,z167,z6]),(0,[z20,z1,z826,z4,z5,z6])],[(0,[z0,z1,z1246,z4,z5,z6]),(0,[z0,z2,z4,z1247,z5,z6]),(0,[z0,z1,z2,z4,z5,z496])],[(0,[z0,z10,z2,z4,z175,z6]),(0,[z201,z1,z2,z4,z5,z278]),(0,[z1248,z1,z2,z4,z5,z6])],[(0,[z0,z143,z2,z4,z5,z6]),(0,[z172,z1,z12,z4,z5,z47])],[(0,[z168,z1,z269,z272,z5,z6]),(0,[z33,z1,z2,z4,z175,z65]),(0,[z0,z44,z639,z4,z5,z6]),(0,[z0,z1,z2,z131,z5,z772])],[(0,[z0,z1,z2,z4,z1249,z6]),(0,[z0,z1,z1250,z4,z5,z6]),(0,[z140,z44,z2,z4,z5,z6]),(0,[z13,z0,z2,z541,z4,z193]),(0,[z1251,z0,z2,z4,z5,z6]),(0,[z0,z1,z2,z80,z4,z5])],[(0,[z1,z744,z2,z4,z5,z6]),(0,[z20,z290,z213,z4,z5,z6]),(0,[z0,z1,z4,z5,z6,z1252]),(0,[z33,z184,z2,z4,z5,z65]),(0,[z0,z396,z2,z4,z5,z6]),(0,[z0,z723,z2,z4,z5,z6])],[(0,[z113,z30,z2,z4,z5,z87]),(0,[z194,z10,z2,z4,z5,z6]),(1,[z0,z2,z4,z854,z6]),(0,[z0,z1,z2,z4,z358,z5]),(0,[z363,z325,z2,z4,z5,z6]),(0,[z1253,z1,z2,z4,z5,z6]),(0,[z0,z1254,z2,z4,z5,z6])],[(0,[z33,z1126,z2,z4,z5,z6]),(0,[z0,z1,z2,z860,z5,z6]),(0,[z1255,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z1256]),(0,[z172,z1,z2,z4,z583,z6])],[(0,[z78,z30,z2,z4,z5,z6]),(0,[z405,z1,z2,z4,z5,z6]),(0,[z0,z1257,z2,z4,z5,z6]),(0,[z0,z1,z2,z1258,z4,z6]),(0,[z389,z337,z2,z4,z5,z6]),(0,[z1259,z1,z2,z4,z5,z6]),(0,[z0,z1260,z2,z4,z5,z6])],[(0,[z245,z227,z2,z4,z5,z6]),(0,[z1261,z0,z2,z4,z5,z6]),(0,[z0,z1,z2,z112,z6,z632]),(0,[z194,z1,z2,z4,z71,z6])],[(0,[z0,z1,z2,z4,z5,z1262]),(0,[z0,z1,z2,z4,z5,z1263]),(0,[z0,z115,z2,z553,z4,z6]),(0,[z0,z1,z2,z25,z731,z6]),(0,[z194,z2,z4,z5,z6,z77])]],
   [[(0,[z0,z10,z2,z4,z5,z161]),(0,[z169,z44,z2,z4,z5,z6]),(0,[z1,z1264,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z922]),(0,[z1,z258,z2,z4,z583,z6]),(0,[z0,z1265,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z710,z6])],[(0,[z0,z1,z2,z180,z25,z6])],[(0,[z63,z744,z2,z4,z5,z6]),(0,[z0,z198,z24,z4,z5,z6])],[(0,[z1,z2,z860,z272,z5,z6]),(0,[z169,z2,z4,z5,z96,z6]),(0,[z0,z1266,z2,z4,z5,z6])],[(0,[z33,z30,z2,z4,z5,z87]),(0,[z0,z1,z2,z4,z1267,z6]),(0,[z673,z1,z2,z272,z5,z6]),(0,[z0,z1,z4,z5,z47,z922]),(0,[z0,z1,z2,z68,z431,z5])],[(0,[z30,z2,z40,z4,z5,z6]),(0,[z0,z1,z2,z1268,z4,z5]),(0,[z0,z1,z2,z1269,z4,z6])],[],[(0,[z0,z30,z252,z4,z124,z6]),(0,[z0,z1270,z2,z4,z5,z6]),(0,[z0,z1271,z2,z4,z5,z6])],[(0,[z0,z1272,z2,z4,z5,z6]),(0,[z1273,z1,z2,z4,z5,z6])],[(0,[z284,z2,z41,z4,z5,z6]),(0,[z0,z1,z2,z1274,z4,z5]),(0,[z13,z0,z2,z4,z210,z5])],[(0,[z653,z1,z2,z4,z26,z6]),(0,[z13,z0,z2,z4,z5,z522]),(0,[z0,z1,z2,z4,z71,z119])],[(0,[z0,z130,z2,z4,z53,z6]),(0,[z43,z0,z2,z4,z586,z6])],[(0,[z0,z2,z4,z5,z6,z1275]),(0,[z32,z1,z2,z4,z5,z161]),(0,[z0,z1,z2,z1276,z4,z6]),(0,[z0,z1,z104,z171,z4,z5])],[(0,[z0,z125,z200,z4,z5,z6]),(0,[z0,z1,z2,z38,z158,z4])],[(0,[z0,z285,z2,z4,z5,z6]),(0,[z0,z1277,z2,z4,z5,z6]),(0,[z0,z1,z1278,z4,z5,z6]),(0,[z1,z2,z4,z860,z5,z6])],[(0,[z1126,z30,z2,z4,z5,z6]),(0,[z0,z88,z770,z4,z5,z6]),(0,[z1279,z1,z2,z4,z5,z6]),(0,[z0,z1,z1280,z4,z5,z6])]],
   [[(0,[z0,z135,z2,z218,z5,z6]),(0,[z0,z1,z2,z4,z1281,z6]),(0,[z56,z356,z2,z4,z5,z6]),(0,[z0,z2,z4,z1282,z5,z6])],[(0,[z415,z30,z2,z93,z5,z6])],[(0,[z0,z184,z2,z4,z175,z6])],[(0,[z63,z10,z2,z4,z5,z6]),(0,[z0,z10,z2,z99,z25,z6]),(0,[z1,z337,z2,z4,z5,z6]),(0,[z172,z92,z2,z4,z5,z6]),(0,[z1,z2,z1283,z4,z5,z6])],[(0,[z0,z10,z403,z4,z5,z6]),(0,[z0,z1,z1284,z4,z5,z6]),(0,[z0,z44,z88,z4,z5,z6])],[(0,[z43,z13,z0,z2,z4,z165])],[(0,[z275,z10,z2,z93,z5,z6]),(0,[z0,z1,z2,z725,z5,z6]),(0,[z1,z83,z337,z4,z5,z6])],[(0,[z0,z1285,z2,z4,z5,z6]),(0,[z20,z1,z213,z4,z5,z267]),(0,[z1,z2,z231,z4,z159,z5]),(0,[z932,z2,z4,z5,z6,z173])],[(0,[z602,z30,z2,z4,z5,z6]),(0,[z0,z10,z2,z4,z331,z6]),(0,[z0,z1,z252,z4,z124,z6]),(0,[z0,z1,z46,z4,z5,z922])],[(0,[z0,z1,z2,z4,z1286,z6]),(0,[z602,z1,z213,z4,z5,z6]),(0,[z36,z1,z2,z4,z165,z5])],[(0,[z279,z0,z2,z110,z5,z6]),(0,[z0,z456,z2,z4,z5,z96]),(0,[z0,z1,z2,z1287,z4,z5]),(0,[z1,z1288,z2,z4,z5,z6])],[(0,[z30,z2,z158,z4,z5,z6]),(0,[z1,z2,z4,z5,z6,z106]),(0,[z1289,z0,z2,z4,z5,z6])],[(0,[z30,z2,z4,z5,z6,z161]),(0,[z0,z1,z2,z4,z5,z1290]),(0,[z387,z2,z4,z5,z6,z106])],[(0,[z274,z30,z2,z4,z5,z6]),(0,[z669,z30,z2,z4,z5,z6]),(0,[z168,z1,z2,z573,z5,z6])],[(0,[z1,z30,z2,z4,z5,z161]),(0,[z542,z0,z2,z4,z5,z193]),(0,[z0,z1,z370,z4,z5,z6]),(0,[z1,z403,z4,z272,z5,z6]),(0,[z168,z1,z2,z272,z398,z6]),(0,[z0,z1,z83,z163,z4,z6])],[(0,[z0,z1,z1291,z4,z5,z6]),(0,[z155,z10,z2,z4,z26,z6]),(0,[z0,z1,z2,z4,z1292,z6]),(0,[z169,z115,z2,z4,z5,z6]),(0,[z363,z179,z2,z4,z5,z6]),(0,[z201,z208,z2,z4,z5,z6])]],
   [[(0,[z30,z46,z41,z4,z5,z6]),(0,[z155,z30,z2,z4,z5,z322]),(0,[z0,z1,z2,z4,z5,z1293])],[(0,[z0,z1,z2,z4,z5,z1294]),(0,[z21,z2,z93,z4,z5,z6]),(0,[z19,z1,z2,z4,z84,z6]),(0,[z0,z1,z1295,z4,z5,z6]),(0,[z0,z1,z2,z1296,z4,z6])],[(0,[z0,z30,z2,z4,z1241,z6]),(0,[z519,z1,z41,z4,z5,z6]),(0,[z0,z1297,z2,z4,z5,z6]),(0,[z1,z2,z4,z1298,z5,z6]),(0,[z1299,z1,z2,z4,z5,z6])],[(0,[z491,z30,z2,z4,z5,z6]),(0,[z20,z10,z213,z4,z5,z6]),(0,[z43,z55,z2,z4,z304,z6])],[(0,[z294,z30,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z1300])],[(0,[z1301,z1,z2,z4,z5,z6])],[(1,[z30,z2,z4,z398,z6]),(0,[z0,z1,z2,z1302,z4,z5]),(0,[z0,z1,z2,z4,z5,z1303]),(0,[z0,z1,z2,z4,z710,z165])],[(0,[z0,z1,z2,z4,z1304,z6]),(0,[z156,z169,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z1305]),(0,[z0,z1,z2,z1306,z4,z5])],[(0,[z129,z1,z826,z4,z5,z6]),(0,[z0,z1307,z2,z4,z5,z6]),(0,[z2,z4,z5,z6,z1275,z106])],[(0,[z0,z1,z1308,z4,z5,z6]),(0,[z0,z1309,z2,z4,z5,z6]),(0,[z43,z0,z2,z4,z358,z304]),(0,[z1310,z1,z2,z4,z5,z6]),(0,[z0,z1,z1311,z4,z5,z6])],[(0,[z30,z2,z204,z4,z5,z6]),(0,[z1312,z0,z2,z4,z5,z6])],[(0,[z0,z325,z2,z4,z137,z6])],[(0,[z0,z1313,z2,z4,z5,z6]),(0,[z0,z10,z2,z4,z5,z455]),(0,[z0,z1,z41,z4,z331,z6]),(0,[z36,z1,z2,z38,z4,z5]),(0,[z0,z1314,z2,z4,z5,z6])],[(0,[z584,z30,z2,z4,z5,z6]),(0,[z0,z1,z349,z4,z5,z87]),(0,[z1315,z1,z2,z4,z5,z6]),(0,[z1316,z1,z2,z4,z5,z6])],[(0,[z55,z30,z2,z4,z5,z6]),(0,[z0,z1317,z2,z4,z5,z6]),(0,[z1318,z0,z1,z4,z5,z6])],[(0,[z168,z227,z2,z272,z5,z6]),(0,[z0,z1,z2,z4,z1319,z5])]],
   [[(0,[z0,z1,z83,z4,z219,z6]),(0,[z0,z135,z2,z276,z5,z6]),(0,[z0,z1,z1320,z4,z5,z6]),(0,[z356,z2,z52,z4,z5,z6]),(0,[z0,z1,z4,z5,z922,z6]),(0,[z0,z1,z2,z355,z4,z165])],[(0,[z10,z30,z2,z4,z5,z6])],[(0,[z0,z290,z2,z4,z331,z6])],[(0,[z0,z1321,z2,z4,z5,z6]),(0,[z0,z2,z4,z5,z6,z1322])],[(0,[z491,z1,z2,z4,z5,z6]),(0,[z0,z1323,z2,z4,z5,z6]),(0,[z0,z1324,z2,z4,z5,z6]),(0,[z0,z1,z57,z4,z5,z87]),(0,[z0,z1,z2,z289,z5,z90])],[(0,[z0,z1,z2,z4,z1106,z5]),(0,[z0,z179,z2,z4,z5,z6]),(0,[z0,z1,z2,z1325,z4,z5]),(0,[z0,z1,z2,z68,z86,z5])],[(0,[z30,z2,z249,z4,z5,z6]),(0,[z1326,z0,z2,z4,z5,z6]),(0,[z1,z213,z826,z4,z5,z6]),(0,[z0,z1,z2,z4,z935,z6]),(0,[z66,z0,z24,z4,z5,z6]),(0,[z1,z2,z305,z4,z159,z6])],[(0,[z144,z30,z2,z4,z5,z6]),(0,[z30,z83,z2,z4,z84,z6]),(0,[z63,z1,z2,z4,z5,z161]),(0,[z363,z10,z2,z4,z5,z6]),(0,[z0,z396,z2,z4,z583,z6])],[(0,[z129,z1,z41,z4,z5,z6]),(0,[z1327,z0,z2,z4,z5,z6])],[(0,[z30,z2,z259,z4,z5,z6]),(0,[z20,z154,z2,z4,z5,z6]),(0,[z0,z1328,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z1329,z6]),(0,[z1330,z1,z2,z4,z5,z6]),(0,[z0,z1,z72,z4,z5,z47])],[(0,[z744,z30,z2,z4,z5,z6]),(0,[z433,z0,z2,z4,z5,z199]),(0,[z19,z1,z403,z4,z5,z6]),(0,[z0,z1,z1331,z4,z5,z6]),(0,[z533,z1,z2,z4,z5,z65]),(0,[z1332,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z1333,z6]),(0,[z0,z1,z2,z1334,z4,z6]),(0,[z0,z1,z474,z4,z11,z6])],[(0,[z208,z0,z2,z4,z5,z278])],[(0,[z0,z1,z403,z4,z5,z174]),(0,[z0,z1,z2,z4,z5,z1335]),(0,[z1,z2,z4,z5,z6,z1336]),(0,[z1,z2,z4,z5,z6,z1337]),(0,[z0,z1,z2,z4,z1338,z6])],[(0,[z0,z1,z2,z4,z5,z1339]),(0,[z0,z1,z2,z39,z4,z314])],[(0,[z0,z1,z1340,z4,z5,z6]),(0,[z155,z1,z2,z4,z935,z6]),(0,[z43,z0,z2,z4,z358,z6]),(0,[z1,z2,z4,z5,z6,z1341])],[(0,[z55,z1,z2,z4,z5,z6]),(0,[z30,z271,z2,z4,z5,z6]),(0,[z1342,z0,z2,z4,z5,z6]),(0,[z0,z1,z1343,z4,z5,z6]),(0,[z1,z1344,z2,z4,z5,z6])]],
   [[(0,[z920,z30,z2,z4,z5,z6]),(0,[z0,z125,z2,z4,z5,z322]),(0,[z0,z1,z2,z1345,z4,z6])],[(0,[z0,z10,z134,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z1346]),(0,[z0,z1,z2,z4,z1347,z6]),(0,[z13,z0,z2,z4,z103,z193]),(0,[z13,z0,z2,z4,z103,z6]),(0,[z0,z325,z2,z4,z215,z6])],[(0,[z62,z0,z2,z4,z304,z6]),(0,[z1,z2,z4,z26,z398,z6])],[(0,[z0,z1,z2,z4,z1348,z6]),(0,[z1349,z0,z2,z4,z5,z6]),(0,[z1350,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z231,z4,z5])],[(0,[z0,z113,z2,z4,z5,z31]),(0,[z1351,z1,z2,z4,z5,z6]),(0,[z0,z1,z112,z6,z292,z81]),(0,[z0,z1,z1352,z4,z5,z6])],[(0,[z312,z1,z41,z4,z5,z6])],[(0,[z20,z30,z2,z4,z5,z161]),(0,[z0,z1,z2,z4,z5,z1353]),(0,[z275,z21,z2,z93,z5,z6])],[(0,[z20,z1,z213,z4,z5,z161]),(0,[z0,z1,z57,z4,z42,z6]),(0,[z387,z0,z2,z4,z71,z6])],[(0,[z356,z30,z2,z4,z5,z6]),(0,[z0,z1,z1354,z4,z5,z6]),(0,[z0,z1,z1355,z4,z5,z6]),(0,[z0,z12,z396,z4,z5,z47]),(0,[z0,z1,z502,z112,z6,z81])],[(0,[z0,z30,z2,z112,z6,z81]),(0,[z351,z0,z2,z4,z298,z6]),(0,[z10,z2,z4,z5,z6,z266]),(0,[z0,z1,z2,z1356,z4,z5]),(0,[z0,z1357,z2,z4,z5,z6])],[(0,[z0,z252,z79,z4,z124,z6])],[(0,[z63,z1,z403,z4,z5,z6]),(0,[z299,z0,z2,z104,z4,z5])],[],[(0,[z0,z10,z2,z4,z5,z6]),(0,[z0,z1358,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z165,z538])],[(0,[z1087,z0,z2,z4,z5,z6]),(0,[z1,z2,z150,z4,z159,z6]),(0,[z1,z252,z337,z4,z124,z6]),(0,[z1359,z1,z2,z4,z5,z6]),(0,[z1,z1360,z2,z4,z5,z6])],[(0,[z0,z30,z2,z150,z4,z6]),(0,[z0,z1,z2,z4,z331,z267]),(0,[z1,z2,z93,z860,z5,z6]),(0,[z0,z179,z2,z4,z137,z6])]],
   [[(0,[z0,z30,z370,z4,z5,z6]),(0,[z0,z1,z2,z4,z1361,z6]),(0,[z0,z1,z213,z150,z4,z6]),(0,[z0,z1,z1362,z4,z5,z6]),(0,[z0,z1363,z2,z4,z5,z6]),(0,[z1364,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z71,z6])],[(0,[z18,z30,z2,z4,z5,z6]),(0,[z0,z1,z826,z4,z5,z6]),(0,[z275,z1,z403,z4,z5,z6]),(0,[z0,z2,z4,z5,z6,z1365]),(0,[z0,z2,z4,z5,z6,z77]),(0,[z1,z1366,z2,z4,z5,z6]),(0,[z0,z1,z252,z4,z722,z6])],[(0,[z0,z1,z1367,z4,z5,z6]),(0,[z533,z1,z2,z4,z26,z6]),(0,[z1,z1368,z2,z4,z5,z6]),(0,[z0,z932,z2,z4,z5,z6])],[(0,[z19,z30,z2,z4,z84,z6]),(0,[z0,z415,z2,z52,z5,z6]),(0,[z0,z1,z1369,z4,z5,z6]),(0,[z20,z1,z438,z4,z5,z6]),(0,[z0,z1370,z2,z4,z5,z6]),(0,[z13,z0,z2,z4,z5,z262]),(0,[z0,z1,z2,z4,z126,z119]),(0,[z172,z1203,z2,z4,z5,z6]),(0,[z0,z1,z2,z112,z4,z278])],[(0,[z1,z213,z4,z465,z5,z6]),(0,[z0,z325,z2,z4,z5,z6]),(0,[z356,z2,z24,z4,z5,z6])],[(0,[z0,z30,z2,z4,z165,z173]),(0,[z0,z1,z200,z4,z5,z322]),(0,[z0,z1371,z2,z4,z5,z6]),(0,[z0,z1372,z2,z4,z5,z6])],[(0,[z97,z1,z41,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z1373]),(0,[z169,z2,z4,z5,z304,z6])],[(1,[z30,z2,z4,z146,z6]),(0,[z30,z2,z4,z345,z5,z6]),(0,[z156,z0,z2,z132,z5,z6]),(0,[z0,z4,z5,z6,z344,z77])],[(0,[z155,z30,z370,z4,z5,z6]),(0,[z0,z829,z2,z4,z5,z6])],[(0,[z20,z30,z2,z4,z5,z267]),(0,[z397,z30,z2,z4,z84,z6]),(0,[z0,z1,z2,z4,z1374,z6])],[(0,[z140,z10,z2,z4,z5,z6]),(0,[z0,z1375,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z1376,z6]),(0,[z0,z1,z2,z4,z5,z1377]),(0,[z0,z1,z1378,z4,z5,z6]),(0,[z0,z1379,z2,z4,z5,z6]),(0,[z0,z1,z2,z112,z6,z81])],[(0,[z0,z44,z260,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z1380]),(0,[z169,z1,z2,z4,z165,z6]),(0,[z13,z0,z2,z4,z5,z282])],[(0,[z0,z1,z2,z4,z5,z1381]),(0,[z0,z1382,z2,z4,z5,z6]),(0,[z405,z1,z2,z4,z146,z6]),(0,[z0,z1,z370,z4,z5,z426])],[(0,[z534,z30,z2,z4,z5,z6]),(0,[z0,z184,z134,z4,z5,z6]),(0,[z1383,z1,z2,z4,z5,z6])],[(0,[z0,z240,z2,z4,z5,z322])],[(0,[z20,z1,z213,z4,z331,z6]),(0,[z0,z1384,z2,z4,z5,z6])]]]

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
theorem pb0 : chunkB SB 1 ((bkA.flatten.flatten.drop 0).take 502) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb1 : chunkB SB 1 ((bkA.flatten.flatten.drop 502).take 499) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb2 : chunkB SB 1 ((bkA.flatten.flatten.drop 1001).take 355) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pbend : ((bkA.flatten.flatten.drop 1356)).isEmpty = true := by
  decide +kernel

theorem windowsB : windowsG (chunkB SB 1) bkA.flatten.flatten 0 [502, 499, 355] = true :=
  windowsG_cons pb0 (windowsG_cons pb1 (windowsG_cons pb2 (windowsG_nil pbend)))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc0 : chunkOK 5 ((bkB.flatten.drop 0).take 107).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc1 : chunkOK 5 ((bkB.flatten.drop 107).take 113).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc2 : chunkOK 5 ((bkB.flatten.drop 220).take 122).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc3 : chunkOK 5 ((bkB.flatten.drop 342).take 113).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc4 : chunkOK 5 ((bkB.flatten.drop 455).take 57).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pcend : ((bkB.flatten.drop 512)).isEmpty = true := by
  decide +kernel

theorem windowsC : windowsF 5 bkB.flatten 0 [107, 113, 122, 113, 57] = true :=
  windowsF_cons pc0 (windowsF_cons pc1 (windowsF_cons pc2 (windowsF_cons pc3 (windowsF_cons pc4 (windowsF_nil pcend)))))

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

end PEqualNP.Outside.L_meta_37369

theorem PEqualNP.Outside.L_meta_37369 :
    ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (3937069736 * 2 ^ 32 + 3937052808) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (3937069736 * 2 ^ 32 + 3937052808) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  exact PEqualNP.Outside.L_meta_37369.solve