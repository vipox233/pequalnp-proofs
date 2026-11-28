import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_38723

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
  Nat.testBit (4276808424 * 2 ^ 32 + 4008372936) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

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
  [(0x428000411a009131#64 ++ 0xff6013cf3e89f3f3#64 : BitVec 128),
   (0x8500651444324486#64 ++ 0xfef0ed34c7764c9f#64 : BitVec 128),
   (0x32070a28a9858b18#64 ++ 0xddff0e38f9878f1c#64 : BitVec 128),
   (0x240bb03e01d80ec0#64 ++ 0xbbdff03f01f80fe0#64 : BitVec 128),
   (0x380ddf8001ef6000#64 ++ 0x77cfffc001fff000#64 : BitVec 128),
   (0xc02efffff6000000#64 ++ 0x0feffffffe000000#64 : BitVec 128)]

def witness : Circuit :=
  ⟨[⟨.and, [1, 2]⟩, ⟨.or, [0, 6]⟩, ⟨.and, [2, 5]⟩, ⟨.or, [1, 8]⟩, ⟨.and, [9, 3]⟩, ⟨.or, [7, 10]⟩, ⟨.or, [9, 3]⟩, ⟨.and, [7, 12]⟩, ⟨.or, [13, 4]⟩, ⟨.and, [11, 14]⟩], 15⟩

def mkw (a b : BitVec 64) : W := a ++ b

def z0 : W := mkw 0x240bb03e01d80ec0 0xbbdff03f01f80fe0

def z1 : W := mkw 0x32070a28a9858b18 0xddff0e38f9878f1c

def z2 : W := mkw 0x380ddf8001ef6000 0x77cfffc001fff000

def z3 : W := mkw 0x428000411a009131 0xff6013cf3e89f3f3

def z4 : W := mkw 0x802effbee4000000 0x0defee38f8000000

def z5 : W := mkw 0x8500651444324486 0xfef0ed34c7764c9f

def z6 : W := mkw 0x12040a00a8058118 0x44200e00f807801c

def z7 : W := mkw 0x402e9aebb2000000 0x010f12cb38000000

def z8 : W := mkw 0x18044f8000276000 0x44000fc00007f000

def z9 : W := mkw 0x2009900001c80000 0x33cff00001f80000

def z10 : W := mkw 0xc02efffff6000000 0x0feffffffe000000

def z11 : W := mkw 0x200b902a01c80a40 0x000f000000000000

def z12 : W := mkw 0x0000000000000000 0xdcf00c30c1060c1c

def z13 : W := mkw 0x00060a28a0000000 0x0def0e38f8000000

def z14 : W := mkw 0x8500201444100486 0x88300034c6000c9f

def z15 : W := mkw 0xc52efffff6100486 0x8ffffffffe000c9f

def z16 : W := mkw 0x32870a28a9859b39 0xfdff0e38f98fffff

def z17 : W := mkw 0x4a88d5c11a6af131 0xff60f3cf3ef9f3f3

def z18 : W := mkw 0x000cdf8000000000 0x07cfffc000000000

def z19 : W := mkw 0xc52efffff6324486 0xffffffffff764c9f

def z20 : W := mkw 0x428000411a009131 0x010012cb3889b360

def z21 : W := mkw 0x72870a69bb859b39 0xffff1fffff8fffff

def z22 : W := mkw 0xc028f5d756000000 0x0200f1c706000000

def z23 : W := mkw 0x32070a28a9858b18 0xffff1ff8f98fff1c

def z24 : W := mkw 0x0400000000100480 0xb010000001700c80

def z25 : W := mkw 0x5a844fc11a27f131 0xff601fcf3e8ff3f3

def z26 : W := mkw 0x240bb03e01d80ec0 0x009fe03001700c00

def z27 : W := mkw 0x428000411a009131 0x442003c03e01f013

def z28 : W := mkw 0x0000201400000000 0x0ac0e03400000000

def z29 : W := mkw 0x30070a28a1850a08 0x009f0c30c1060c0c

def z30 : W := mkw 0x3201000009858b18 0xd010000001878f1c

def z31 : W := mkw 0x782f9aebb3cd2000 0x010f12cb3889b000

def z32 : W := mkw 0x32050a0009858b18 0xd5df0e0001878f1c

def z33 : W := mkw 0xc38045415e22d137 0x44200fc0fe07f01f

def z34 : W := mkw 0xc78065555e32d5b7 0xfff0ffffffffffff

def z35 : W := mkw 0x4000004112000000 0xff6013cf3e004093

def z36 : W := mkw 0x320fba3ea9858b18 0xdffffe3ff9878f1c

def z37 : W := mkw 0x0000450000224000 0x76c0ed0001764000

def z38 : W := mkw 0xbd0dff9445ff6486 0xfffffff4c7fffc9f

def z39 : W := mkw 0x32070a28a9858b18 0xffff0f3cff87cf9f

def z40 : W := mkw 0x0000000000000000 0xfe60010406004093

def z41 : W := mkw 0xc02efffff6000000 0x018ffefbf8000000

def z42 : W := mkw 0xb7076f3cedb7cf9e 0xffffef3cfff7cf9f

def z43 : W := mkw 0x0000450000224000 0x77c0ffc001fff000

def z44 : W := mkw 0x0000000000000000 0xff4013cf0089f3e0

def z45 : W := mkw 0xfc2ffffff7ff6ec0 0xffffffffffffffe0

def z46 : W := mkw 0x7e8fffff1bfffff1 0xffffffff3ffffff3

def z47 : W := mkw 0xc022207ff6000000 0x0820003ffe000000

def z48 : W := mkw 0x0402203e00100ec0 0x8810003f00000fe0

def z49 : W := mkw 0xc42efffff6100ec0 0x8ffffffffe000fe0

def z50 : W := mkw 0x802effbee4000000 0x0bcffc3fc0000000

def z51 : W := mkw 0x200b902a01c80a40 0x010f100b00880360

def z52 : W := mkw 0x8500651444324486 0x2200e10406704083

def z53 : W := mkw 0x7a8ddfc11beff131 0xffefffcf3ffff3f3

def z54 : W := mkw 0x36072a3ca9958f98 0xffffee3cf9f78f9c

def z55 : W := mkw 0x788ddfc113ef7021 0x77cfffc707fff0e3

def z56 : W := mkw 0x2409b01401d80480 0xbbdff03401f80c80

def z57 : W := mkw 0x268bb03e09d89ff1 0xfbdff03f01f9fff3

def z58 : W := mkw 0xc0264fe9f6000000 0x0def0ff8fe000000

def z59 : W := mkw 0xbd0fffbe45ff6ec6 0xffffffffc7ffffff

def z60 : W := mkw 0x8d08f594447a6486 0xfef0fdf4c77e7c9f

def z61 : W := mkw 0x32070a28a9858b18 0x010f020838818300

def z62 : W := mkw 0x00060a28a0000000 0x008f0c30c0000000

def z63 : W := mkw 0xb70165144db7cf9e 0xfef0ed34c7f7cf9f

def z64 : W := mkw 0x8000651444000000 0x0ee0ed34c6000000

def z65 : W := mkw 0x3c0fffbe01ff6ec0 0xffdfffff01ffffe0

def z66 : W := mkw 0x380d9a8001cd2000 0x010f12c00089b000

def z67 : W := mkw 0xc0244fc1f6000000 0x0f601fcffe000000

def z68 : W := mkw 0x3a0fdfa8a9efeb18 0xfffffff8f9ffff1c

def z69 : W := mkw 0x0808d580006a6000 0x2200f1c000787000

def z70 : W := mkw 0x380ddf8001ef6000 0x008fec0001760000

def z71 : W := mkw 0x428000411a009131 0x8820000f3e0003f3

def z72 : W := mkw 0xa50bb03e45d80ec6 0xbbfff03fc7f80fff

def z73 : W := mkw 0x2003002801800a00 0x99df003801800f00

def z74 : W := mkw 0x0400201400100480 0x8810003400000c80

def z75 : W := mkw 0x0400201400100480 0xbad0e03401700c80

def z76 : W := mkw 0xe02ffffff7c80a40 0x0feffffffe880360

def z77 : W := mkw 0x000edfa8a0000000 0x0feffff8f8000000

def z78 : W := mkw 0x0000000000000000 0xf000000000004093

def z79 : W := mkw 0x30070a28a1850a08 0x99df0c38c1860f0c

def z80 : W := mkw 0x2409900001d80ec0 0xb3dff00001f80fe0

def z81 : W := mkw 0x30070a2801850a00 0xdddf0e3801878f00

def z82 : W := mkw 0x0000000000000000 0xff60110f068843f3

def z83 : W := mkw 0x000ab03e00000000 0x0bcff03f00000000

def z84 : W := mkw 0x4000004112000000 0x0f6013cf3e000000

def z85 : W := mkw 0x4080004112001021 0x220011c7060870e3

def z86 : W := mkw 0x0000000000000000 0x774013c00089f000

def z87 : W := mkw 0x668bb07f1bd89ff1 0xfffff3ff3ff9fff3

def z88 : W := mkw 0x3203002809858b18 0xd9df003801878f1c

def z89 : W := mkw 0x8500201444100486 0xfe700134c6004c9f

def z90 : W := mkw 0xc78020555e1095b7 0xff7013fffe89ffff

def z91 : W := mkw 0x380d9a8001cd2000 0x774f13c00089f000

def z92 : W := mkw 0x0408b016005804c0 0x2200f007007800e0

def z93 : W := mkw 0x240bb03e01d80ec0 0xfffff13f07f84ff3

def z94 : W := mkw 0x782fdfebb3ef6000 0x77cfffcb39fff000

def z95 : W := mkw 0x0000000000000000 0xbb40100f008803e0

def z96 : W := mkw 0xc02efffff6000000 0x04afeff0fe000000

def z97 : W := mkw 0xc38045415e22d137 0xff601fcffe8ff3ff

def z98 : W := mkw 0x3a81000009eff131 0xf000000001fff3f3

def z99 : W := mkw 0x380ddf8001ef6000 0xffefffc407fff093

def z100 : W := mkw 0x3701000009b7cf9e 0xf010000001f7cf9f

def z101 : W := mkw 0x4888d5c1126a7021 0x2200f1c7067870e3

def z102 : W := mkw 0x0280000008009131 0xf74013c00089f3f3

def z103 : W := mkw 0x8100651444224006 0x4ee0ed34c606401f

def z104 : W := mkw 0x8500651444324486 0x0090ec30c1760c0c

def z105 : W := mkw 0x200bb03e01c80000 0x3bcff03f01f80000

def z106 : W := mkw 0x402e9aebb2000000 0x0f6f13cf3e000000

def z107 : W := mkw 0x4682207f1a109ff1 0xff7013ff3e89fff3

def z108 : W := mkw 0xa50bf53e45fa4ec6 0xfffffd3fc7fe4fff

def z109 : W := mkw 0x2001000001c80a40 0x0000000000880360

def z110 : W := mkw 0xe42ffffff7d80ec0 0xbffffffffff80fe0

def z111 : W := mkw 0x12060a28a8058118 0x4def0e38f807801c

def z112 : W := mkw 0xc0aefffff6001021 0x2feffffffe0870e3

def z113 : W := mkw 0x0500000000324486 0xf010000001764c9f

def z114 : W := mkw 0x8502653e44324ec6 0xfef0ed3fc7764fff

def z115 : W := mkw 0x8100450044224006 0x44200d00c606401f

def z116 : W := mkw 0x7a8fdfe9bbeffb39 0xffffffffffffffff

def z117 : W := mkw 0x380fdfa8a1ef6a08 0x77dffff0c1fffc0c

def z118 : W := mkw 0x0000000000000000 0x7640010000004000

def z119 : W := mkw 0x2401000001d80ec0 0xb010000001f80fe0

def z120 : W := mkw 0x3c0fffbe01ff6ec0 0xbbdffc3f01fe0fe0

def z121 : W := mkw 0x32030028a9858b18 0xd8300038f9878f1c

def z122 : W := mkw 0x0280000008009131 0xf00000000089f3f3

def z123 : W := mkw 0x802effbee4000000 0x008fec30c0000000

def z124 : W := mkw 0xc5806555563254a7 0xfef0fdf7c77e7cff

def z125 : W := mkw 0x0000000000000000 0x8820000406000093

def z126 : W := mkw 0x0408b016005804c0 0x0000e00000700000

def z127 : W := mkw 0x2009900001c80000 0x008fe00001700000

def z128 : W := mkw 0x8100450044224006 0x76e0ed00c776401f

def z129 : W := mkw 0x402ebaffb2000000 0x0bcff2ff38000000

def z130 : W := mkw 0x000c9a8000000000 0x010f12c000000000

def z131 : W := mkw 0x040ab03e00100480 0xbbdff03f01700c80

def z132 : W := mkw 0x000eba3ea0000000 0x0feffe3ff8000000

def z133 : W := mkw 0x360fba3ea9dd8fd8 0xfffffe3ff9ff8ffc

def z134 : W := mkw 0x00040a00a0000000 0x04200e00f8000000

def z135 : W := mkw 0x602f9aebb3c80a40 0x010f12cb38880360

def z136 : W := mkw 0x5a844fc11a27f131 0x44200fc03e07f013

def z137 : W := mkw 0x12060a28a8058b18 0xcc300e38f8078f1c

def z138 : W := mkw 0x2203002809808b10 0xddff023839818f10

def z139 : W := mkw 0x3801000001ef6000 0x7000000001fff000

def z140 : W := mkw 0x85066f3ce4324486 0xffffef3cff764c9f

def z141 : W := mkw 0xc52efffff6324486 0x0fffffffff760c0c

def z142 : W := mkw 0x428000411a009131 0xf10012cb3889f3f3

def z143 : W := mkw 0x250bb03e01fa4ec6 0xfbdff03f01fe4fff

def z144 : W := mkw 0x802effbee4000000 0x0eefed34c6000000

def z145 : W := mkw 0x00060a28a0000000 0xddff0e38f9060c1c

def z146 : W := mkw 0xfd2ffffff7ff6486 0xfffffffffffffc9f

def z147 : W := mkw 0x0002002800000000 0x09cf003800000000

def z148 : W := mkw 0x4000004112000000 0x042003c03e000000

def z149 : W := mkw 0x180cdf8000276000 0x47cfffc00007f000

def z150 : W := mkw 0x8702653cec32cf9e 0xfef0ed3cff764f9f

def z151 : W := mkw 0xc522207ff6100486 0x8830003ffe000c9f

def z152 : W := mkw 0xf02ffffff7850000 0x5fefffffff878000

def z153 : W := mkw 0x40060a69b2000000 0x0fef1ffffe000000

def z154 : W := mkw 0x3a01000009efeb18 0xf010000001ffff1c

def z155 : W := mkw 0x0400651400324480 0xfed0ed3401764c80

def z156 : W := mkw 0x32070a28a9858b18 0x452f0e08f887831c

def z157 : W := mkw 0x3c0dff9401ff6480 0xffdffff401fffc80

def z158 : W := mkw 0x0000000000000000 0x0e60010406000000

def z159 : W := mkw 0x200b902801c80a00 0xbbdff03801f80f00

def z160 : W := mkw 0x4022006bb2000000 0x0000000b38000000

def z161 : W := mkw 0xc828f5d7566a6000 0x2200f1c706787000

def z162 : W := mkw 0x4080004112001021 0xbb4011cf068873e3

def z163 : W := mkw 0x36070a28a9dd8fd8 0xfdff0e38f9ff8ffc

def z164 : W := mkw 0xe6afffffffd89ff1 0xfffffffffff9fff3

def z165 : W := mkw 0x7a8ddfc11beff131 0x77efffc03ffff013

def z166 : W := mkw 0xc0244fc1f6000000 0x04200fc0fe000000

def z167 : W := mkw 0x42820069ba009b39 0xff7013fffe89ffff

def z168 : W := mkw 0x32070a28a9858b18 0x88bf0c38f9060f1c

def z169 : W := mkw 0xb80dff9445ef6000 0x7feffff4c7fff000

def z170 : W := mkw 0x0002002800000a00 0x8810003800000f00

def z171 : W := mkw 0x870065144c32c596 0xfff0ef3cfff7cf9f

def z172 : W := mkw 0x200b902a01c80a40 0x99df103b01880f60

def z173 : W := mkw 0xc2aefffffe009131 0xffeffffffe89f3f3

def z174 : W := mkw 0xa509f51445fa4486 0xfffffd34c7fe4c9f

def z175 : W := mkw 0x428000411a009131 0xaa2011cf3e0873f3

def z176 : W := mkw 0xc028f5d756000000 0x0f60f3cf3e000000

def z177 : W := mkw 0x040ab03e005804c0 0x2bcff03f007800e0

def z178 : W := mkw 0x428000411a009131 0xf820000f3e89f3f3

def z179 : W := mkw 0xf22fffffff858b18 0xdfffffffff878f1c

def z180 : W := mkw 0x380ddf8001ef6000 0x018ffec001ffb000

def z181 : W := mkw 0x3801450001ef6000 0x76c0ed0001fff000

def z182 : W := mkw 0x428000411a009131 0x892012cf3e89b3f3

def z183 : W := mkw 0x8500651444324486 0x44b0ed30c7764c1f

def z184 : W := mkw 0x3281000009859b39 0xf0100000018fffff

def z185 : W := mkw 0x400cdfc112000000 0x0fefffcf3e000000

def z186 : W := mkw 0x99044f8044276006 0x44200fc0c607f01f

def z187 : W := mkw 0xe52ffffff7fa4ec6 0xfffffffffffe4fff

def z188 : W := mkw 0xc42efffff6100480 0xbfffffffff700c80

def z189 : W := mkw 0xf82ffffff7ef6000 0x7feffffffffff000

def z190 : W := mkw 0xc2a2207ffe009131 0xff6013fffe89f3f3

def z191 : W := mkw 0x240bb03e01d80ec0 0x019ff03b01f80f60

def z192 : W := mkw 0x3e0fffbea9ffefd8 0xfffffffff9fffffc

def z193 : W := mkw 0x8500651444324486 0xfff0fd3fc7fe4fff

def z194 : W := mkw 0xc0262a7ff6000000 0x0def0e3ffe000000

def z195 : W := mkw 0xc02efffff6000000 0xdfffffffff060c1c

def z196 : W := mkw 0x0402203e00100ec0 0xbad0e03f01700fe0

def z197 : W := mkw 0x8500651444324486 0xcc300d34c6064c9f

def z198 : W := mkw 0x0000450000224000 0x2200e10000704000

def z199 : W := mkw 0x0280000008009131 0xfd6002083889f3f3

def z200 : W := mkw 0x0000450000224000 0xfee0ed0407764093

def z201 : W := mkw 0x428045411a22d131 0xffe0ffcf3ffff3f3

def z202 : W := mkw 0x428000411a009131 0xf20011c70689f3f3

def z203 : W := mkw 0x0000000000000000 0x010012c00089b000

def z204 : W := mkw 0x240bb03e01d80ec0 0x33dff03001f80c00

def z205 : W := mkw 0xf62fffffffdd8fd8 0xffffffffffff8ffc

def z206 : W := mkw 0xd82efffff6276000 0x4feffffffe07f000

def z207 : W := mkw 0x7a8ddfc11beff131 0x77cfffcb39fff360

def z208 : W := mkw 0x02060a28a8008110 0xddef0e38f8818310

def z209 : W := mkw 0x2401000001d80ec0 0xbb50100f01f80fe0

def z210 : W := mkw 0x0402203e00100ec0 0x0010003000000c00

def z211 : W := mkw 0xa50bf53e45fa4ec6 0xfeffed34c7764c9f

def z212 : W := mkw 0x8500450044324486 0xf4300d00c7764c9f

def z213 : W := mkw 0x02020028a8008b18 0x88300038f8000f1c

def z214 : W := mkw 0xe02ffffff7800a00 0x9fffffffff800f00

def z215 : W := mkw 0x0200000008008110 0xdd60020838818310

def z216 : W := mkw 0x3809d58001ef6000 0x7200f1c001fff000

def z217 : W := mkw 0x0200000008008110 0xddf00e38f9878f1c

def z218 : W := mkw 0x00060a28a0000000 0x010f020838000000

def z219 : W := mkw 0x380ddf8001ef6000 0x448fefc00177f000

def z220 : W := mkw 0xe42ffffff7d80ec0 0x0fffffffff700c00

def z221 : W := mkw 0xc12efffff6224006 0x4feffffffe06401f

def z222 : W := mkw 0x240bb03e01d80ec0 0xffdff3ff01f9ffe0

def z223 : W := mkw 0x0500000000324486 0x0010000001760c0c

def z224 : W := mkw 0x780ddfc113ef6000 0x7fefffcf3ffff000

def z225 : W := mkw 0xc02ab07ff6000000 0x0beff03ffe000000

def z226 : W := mkw 0x8508f516447a44c6 0x2200f107067840e3

def z227 : W := mkw 0x850cff9444324486 0xfffffff4c7764c9f

def z228 : W := mkw 0x300d9a0001cd0000 0x77cffe0001ff8000

def z229 : W := mkw 0x628b906b1bc89b71 0x010f12cb3889b360

def z230 : W := mkw 0x8500651444324486 0x0000e00000700000

def z231 : W := mkw 0xc1244fc1f6224006 0x44200fc0fe06401f

def z232 : W := mkw 0x402890c312000000 0x000010c300000000

def z233 : W := mkw 0x42860a69ba009131 0xffef1ffffe89f3f3

def z234 : W := mkw 0xc528f5d756324486 0x2200f1c706704083

def z235 : W := mkw 0xf82dffd757ef6000 0x77cfffc707fff000

def z236 : W := mkw 0x2403203e01d80ec0 0xb810003f01f80fe0

def z237 : W := mkw 0x7a8100411beff131 0xff6013cf3ffff3f3

def z238 : W := mkw 0xc02efffff6000000 0xffeffffffe004093

def z239 : W := mkw 0x80066f3ce4000000 0x0fefef3cfe000000

def z240 : W := mkw 0xc02efffff6000000 0x7feffffffe89f000

def z241 : W := mkw 0x32074f28a9a7cb18 0xffffef38f9f7cf1c

def z242 : W := mkw 0xbd0dff9445ff6486 0x77dffff0c1fffc0c

def z243 : W := mkw 0x12040a00a8058118 0x0000020038018000

def z244 : W := mkw 0x8000450044000000 0x04200d00c6000000

def z245 : W := mkw 0x8500651444324486 0xfff0fff4c7fffc9f

def z246 : W := mkw 0x002e9aaaa0000000 0x000f000000000000

def z247 : W := mkw 0x12040a00a8058118 0xdcf00e30f9078c1c

def z248 : W := mkw 0x72870a69bb859b39 0xddff0ff8ff87ff1f

def z249 : W := mkw 0x0100000000224006 0x400000000006401f

def z250 : W := mkw 0xf72fffffffb7cf9e 0xfffffffffff7cf9f

def z251 : W := mkw 0x32070a28a9858b18 0x99df023839818f00

def z252 : W := mkw 0x380d9a8001cd2000 0x33cff2c001f9b000

def z253 : W := mkw 0xf82ffffff7cd2000 0x0feffffffe89b000

def z254 : W := mkw 0x668bb07f1bd89ff1 0xbbdff2ff39f9bfe0

def z255 : W := mkw 0x0000000000000000 0x2200010406004083

def z256 : W := mkw 0x40240ac1b2000000 0x000002c038000000

def z257 : W := mkw 0x30050a0001850000 0x010f020000818000

def z258 : W := mkw 0x240bf53e01fa4ec0 0xffdffd3f01fe4fe0

def z259 : W := mkw 0x42ae9aebba009131 0xff6f13cf3e89f3f3

def z260 : W := mkw 0x20070a28a1800a00 0x9dff0e38f9800f00

def z261 : W := mkw 0x0808908000482000 0x000010c000083000

def z262 : W := mkw 0x72870a69bb859b39 0xff6f13cf3e89f3f3

def z263 : W := mkw 0x0200000008008b18 0x8010000000000f1c

def z264 : W := mkw 0x360bb03e09dd8fd8 0xfbdff03f01ff8ffc

def z265 : W := mkw 0x000ab03e00000000 0xbbcff03f008803e0

def z266 : W := mkw 0xb82fffbee5ef6000 0x77cffff0c1fff000

def z267 : W := mkw 0xc02efffff6000000 0xbfeffffffe8803e0

def z268 : W := mkw 0x8400651444100480 0xbef0ed34c7700c80

def z269 : W := mkw 0x0080000000001021 0x20000000000870e3

def z270 : W := mkw 0x800cff9444000000 0x0feffff4c6000000

def z271 : W := mkw 0x200b902a01c80a40 0x33cff00b01f80360

def z272 : W := mkw 0x0000000000000000 0x0000000000000000

def z273 : W := mkw 0xc42efffff65804c0 0x2feffffffe7800e0

def z274 : W := mkw 0x8500651444324486 0x0ef0ed34c7760c0c

def z275 : W := mkw 0x3801000001cd2000 0x000000000089b000

def z276 : W := mkw 0xc02af5ff56000000 0x0bcff1ff06000000

def z277 : W := mkw 0x2001000001c80000 0x3000000001f80000

def z278 : W := mkw 0x8100000044000006 0x00200000c600001f

def z279 : W := mkw 0x0280000008009131 0xfb40100f0089f3f3

def z280 : W := mkw 0x02020028a8008b18 0xdd700238f8818f1c

def z281 : W := mkw 0x3a0f9aa8a9cdab18 0x010f12c83889b300

def z282 : W := mkw 0x0000000000000000 0x00900c30c1060c0c

def z283 : W := mkw 0xc222207ffe008b18 0x8830003ffe000f1c

def z284 : W := mkw 0xf7876f7dffb7dfbf 0xffffffffffffffff

def z285 : W := mkw 0x3601000009dd8fd8 0xf010000001ff8ffc

def z286 : W := mkw 0x32050a00a9858b18 0xd4300e00f9878f1c

def z287 : W := mkw 0x30050a0001850000 0x008f0c0001060000

def z288 : W := mkw 0x428000411a009131 0xbb60100f3e8803f3

def z289 : W := mkw 0x0400201400100480 0x0090e03001700c00

def z290 : W := mkw 0x240bb03e01d80ec0 0x889fe03f01700fe0

def z291 : W := mkw 0x18044f8000276000 0x77401fc0008ff000

def z292 : W := mkw 0x648bb07f13d81ee1 0xbbdff1ff07f87fe3

def z293 : W := mkw 0x0000450000000000 0x06c0ed0000000000

def z294 : W := mkw 0x380ddf8001ef6000 0x76cfed0001764000

def z295 : W := mkw 0x30050a0001850000 0x55cf0e0001878000

def z296 : W := mkw 0x0408b016005804c0 0xbad0f03701780ce0

def z297 : W := mkw 0xbd01651445ff6486 0xfef0ed34c7fffc9f

def z298 : W := mkw 0x72870a69bb859b39 0xddff1efbf98fbf7c

def z299 : W := mkw 0xc2aefffffe009131 0x4feffffffe01f013

def z300 : W := mkw 0x4080004112001021 0x2f6013cf3e0870e3

def z301 : W := mkw 0x30050a0001850000 0xddff0e30c1878c1c

def z302 : W := mkw 0x8500651444324486 0x76c0ed0407764083

def z303 : W := mkw 0x240bb03e01d80ec0 0xbadfe03401700c80

def z304 : W := mkw 0x380ddf8001ef6000 0x708fec0001fff000

def z305 : W := mkw 0xbf0fffbcedffef9e 0xfffffffcffffff9f

def z306 : W := mkw 0x3c0bb03e01ff6ec0 0xfbdff03f01ffffe0

def z307 : W := mkw 0x32070a28a9858b18 0x019f0e38f9878f0c

def z308 : W := mkw 0x52840a41ba059139 0x44200fc0fe07f01f

def z309 : W := mkw 0x240bb03e01d80ec0 0x230ff00f00f803e0

def z310 : W := mkw 0x00020028a0000000 0x08200038f8000000

def z311 : W := mkw 0xc0266ffff6000000 0x0c200ffffe000000

def z312 : W := mkw 0x3809900001ef6000 0x73cff00001fff000

def z313 : W := mkw 0x0000000000000000 0x0ce00c30c0000000

def z314 : W := mkw 0x628300691b809b31 0xffff13ff3f89fff3

def z315 : W := mkw 0x340fba3ea1dd0ec8 0xbbdffc3fc1fe0fec

def z316 : W := mkw 0x0000000000000000 0x22001007000800e0

def z317 : W := mkw 0x0008b01600000000 0x0200f00700000000

def z318 : W := mkw 0x0000000000000000 0x88300030c0000c1c

def z319 : W := mkw 0xc2aefffffe009131 0x8feffffffe0003f3

def z320 : W := mkw 0x04000000005804c0 0x20000000007800e0

def z321 : W := mkw 0x0808d580006a6000 0x76c0fdc0017e7000

def z322 : W := mkw 0x3c0fbabe01dd2ec0 0xbbdff2ff01f9bfe0

def z323 : W := mkw 0xc2aefffffe009131 0x0feffffffe89b360

def z324 : W := mkw 0xa501651445fa4ec6 0xfef0ed34c7fe4fff

def z325 : W := mkw 0x3201000009858b18 0x0000000000818300

def z326 : W := mkw 0xc78065555e32d5b7 0xff60f3cf3ef9f3f3

def z327 : W := mkw 0x8000651444224000 0x7ee0ed34c7764000

def z328 : W := mkw 0x9d046f9444376486 0xfef0eff4c777fc9f

def z329 : W := mkw 0x0280000008009131 0xfe6001040689f3f3

def z330 : W := mkw 0xb90ddf8045ef6006 0x77efffc0c7fff01f

def z331 : W := mkw 0x3a0ddf8009efeb18 0xf7dfffc001ffff1c

def z332 : W := mkw 0xc02af5fff6000000 0x0a20f1fffe000000

def z333 : W := mkw 0x00020028a0000a08 0x00100030c0000c0c

def z334 : W := mkw 0x320f9a2aa9cd8b58 0xddff1e3bf98f8f7c

def z335 : W := mkw 0x0000000000000000 0x5540020000818000

def z336 : W := mkw 0x380ddf8001ef6000 0x55cfee0001f78000

def z337 : W := mkw 0x30054f0001a74000 0x77cfef0001f7c000

def z338 : W := mkw 0xf2272a7fff858b18 0xddff0e3fff878f1c

def z339 : W := mkw 0x2681000009d89ff1 0xf010000001f9fff3

def z340 : W := mkw 0xf22fffffff858b18 0x0feffffffe818300

def z341 : W := mkw 0x340fba3ea1dd0ec8 0x009fec30c1760c0c

def z342 : W := mkw 0xe78bf57f5ffadff7 0xffffffffffffffff

def z343 : W := mkw 0xc422207ff6100ec0 0x8830003ffe000fe0

def z344 : W := mkw 0x428000411a009131 0x230013cf3e89f3e3

def z345 : W := mkw 0x8500651444324486 0x2ee0ed34c6704083

def z346 : W := mkw 0xc02efffff6000000 0x08afec3ffe000000

def z347 : W := mkw 0x428000411a009131 0xbb4012cf3889b3e0

def z348 : W := mkw 0x380ddf8001ef6000 0xfffffff0c1fffc1c

def z349 : W := mkw 0xbd0dff9445ff6486 0x009fec30c1760c0c

def z350 : W := mkw 0x32070a28a9858b18 0xffff1e3ff98f8ffc

def z351 : W := mkw 0x8500651444324486 0x88b0ec34c7760c9f

def z352 : W := mkw 0x240bb03e01d80ec0 0x0bdff03f01700c00

def z353 : W := mkw 0x642fbaffb3d80ec0 0xbbdff2ff39f80fe0

def z354 : W := mkw 0x080cdf80006a6000 0x27cfffc000787000

def z355 : W := mkw 0x852effbee4324486 0xfeffed34c7764c9f

def z356 : W := mkw 0xc428f5d7565804c0 0x2200f1c7067800e0

def z357 : W := mkw 0x2401201401d80ec0 0xbad0e03401f80fe0

def z358 : W := mkw 0xe02ffffff7c80000 0x3feffffffff80000

def z359 : W := mkw 0x468020551a1095b1 0xfff0f3ff3ff9fff3

def z360 : W := mkw 0x240bb03e01d80ec0 0xfffffc3fc1fe0ffc

def z361 : W := mkw 0x8500651444324486 0x6620ed04c676409f

def z362 : W := mkw 0x852effbee4324486 0x009fec30c1760c0c

def z363 : W := mkw 0x0000000000000000 0xff6013c40689f093

def z364 : W := mkw 0xc28065555e009131 0xffe0fffffe89f3f3

def z365 : W := mkw 0x3201000009858b18 0xdcf00c30c1878f1c

def z366 : W := mkw 0x2009900001c80000 0x77cff3c001f9f000

def z367 : W := mkw 0x000ab03e00000000 0x008fe03000000000

def z368 : W := mkw 0x4682207f1a109ff1 0x8830003f3e000ff3

def z369 : W := mkw 0x800af53e44000000 0x0feffd3fc6000000

def z370 : W := mkw 0x478000411a32d5b7 0xff7013cf3fffffff

def z371 : W := mkw 0x0200000008008110 0xff60030c3e81c393

def z372 : W := mkw 0x3a0fdfa8a9efeb18 0x77cfffc839fff300

def z373 : W := mkw 0xb82fffbee5ef6000 0x008fec30c1760000

def z374 : W := mkw 0x0000000000000000 0x440003c00001f000

def z375 : W := mkw 0x428000411a009131 0xf42003c03e89f3f3

def z376 : W := mkw 0x1a044f80a827e118 0x44200fc0f807f01c

def z377 : W := mkw 0x0000000000000000 0x700000000089f000

def z378 : W := mkw 0x0280000008009131 0x000000000089b360

def z379 : W := mkw 0xc22efffffe008b18 0x8ffffffffe000f1c

def z380 : W := mkw 0x3801000001ef6000 0x0000000001760000

def z381 : W := mkw 0x0500000000324486 0xfe70010407764c9f

def z382 : W := mkw 0x32070a28a9858b18 0x44bf0e30f9078c1c

def z383 : W := mkw 0x8502203e44100ec6 0x8830003fc6000fff

def z384 : W := mkw 0x0000450000224000 0xfef0ed30c1764c1c

def z385 : W := mkw 0x260bb03e09d88fd0 0xfffff23f39f98ff0

def z386 : W := mkw 0x3001000001850a08 0x0010000001060c0c

def z387 : W := mkw 0x32050a0009858110 0xddef0e0839878310

def z388 : W := mkw 0x078000000832d5b7 0xf010000001ffffff

def z389 : W := mkw 0x72870a69bb859b39 0xddff0e3fff878fff

def z390 : W := mkw 0x4000004112000000 0xbf6013cf3e8803e0

def z391 : W := mkw 0xc02efffff6000000 0x030ff3cf3e000000

def z392 : W := mkw 0x380fdfa8a1ef6000 0x7feffff8f9fff000

def z393 : W := mkw 0xff8dffd55ffff5b7 0xffffffffffffffff

def z394 : W := mkw 0xb5076f3ce5b74e8e 0xfeffed34c7764c9f

def z395 : W := mkw 0x320f9a28a9cd8b18 0xfffffe38f9ff8f1c

def z396 : W := mkw 0x428000411a009131 0xdd6012cb3889b370

def z397 : W := mkw 0x0000000000224000 0x7000000001764000

def z398 : W := mkw 0x000a902a00000000 0x010f100b00000000

def z399 : W := mkw 0x402e9aebb2000000 0x0def1efbf8000000

def z400 : W := mkw 0x32070a28a9858b18 0x0def0e38f8818300

def z401 : W := mkw 0x0000000000000000 0x4420010006004013

def z402 : W := mkw 0x0200000008008110 0x8820000838000310

def z403 : W := mkw 0x0800458000226000 0x000001c000007000

def z404 : W := mkw 0x428000411a009131 0xcc2003cf3e01f3f3

def z405 : W := mkw 0x0000000000000000 0xb0000000008803e0

def z406 : W := mkw 0xc020205756000000 0x0000000706000000

def z407 : W := mkw 0x8702203cec108f9e 0x8830003cfe000f9f

def z408 : W := mkw 0xc7aefffffe32d5b7 0xffffffffffffffff

def z409 : W := mkw 0x402edfebb2000000 0x07cfffcb38000000

def z410 : W := mkw 0xb5056f1445b74486 0xffffef34c7f7cc9f

def z411 : W := mkw 0x380ddf8001ef6000 0x230ff3c000f9f000

def z412 : W := mkw 0x240fba3ea1d80ec0 0xbffffe3ff9f80fe0

def z413 : W := mkw 0xc528f5d756324486 0xfef0fdf7c7764c9f

def z414 : W := mkw 0x000cdf8000224000 0x77cfffc001764000

def z415 : W := mkw 0x42820069ba009b39 0x8830003ffe000fff

def z416 : W := mkw 0x4080004112001021 0xfe6011c7060870f3

def z417 : W := mkw 0x3a0f9aa8a9cdab18 0xddff1ef8f98fbf1c

def z418 : W := mkw 0x02020028a8008b18 0x0000000838000300

def z419 : W := mkw 0x400ab07f12000000 0x0feff3ff3e000000

def z420 : W := mkw 0x8000651444000000 0x0200e10406000000

def z421 : W := mkw 0x0008d58000000000 0x0200f1c000000000

def z422 : W := mkw 0xc028f5d756000000 0x0ee0fdf7c6000000

def z423 : W := mkw 0x0c08f596007a64c0 0x2200f1c7007870e0

def z424 : W := mkw 0x8500201444100486 0x0000000406000083

def z425 : W := mkw 0x32070a28a9858b18 0xd09f0c30c1878f1c

def z426 : W := mkw 0x628b906b1bc89b71 0xff6f13cf3e89f3f3

def z427 : W := mkw 0x8500651444324486 0xfe60e10406704093

def z428 : W := mkw 0x320fdfa8a9858b18 0xdffffff8f9878f1c

def z429 : W := mkw 0x320f9a2aa9cd8b58 0x010f120b38898360

def z430 : W := mkw 0x8500201444324486 0xf8300034c7764c9f

def z431 : W := mkw 0xc5806555563254a7 0x2200f1c7067870e3

def z432 : W := mkw 0x2003002801800a00 0xbbdf103f01880fe0

def z433 : W := mkw 0x200bb03e01800a00 0x9bdff03f01800f00

def z434 : W := mkw 0x30070a28a1850a08 0x0dff0e38f9060c0c

def z435 : W := mkw 0xb3074f28eda7cb1e 0xddff0f38ff87cf1f

def z436 : W := mkw 0xc82efffff66a6000 0x2feffffffe787000

def z437 : W := mkw 0x240bb03e01d80ec0 0x99dfe03801f00f00

def z438 : W := mkw 0x2403002801d80ec0 0xb9df003801f80fe0

def z439 : W := mkw 0x8000651444000000 0x0080ec30c0000000

def z440 : W := mkw 0x0200000008008110 0xff60120f388983f0

def z441 : W := mkw 0x8100450044224006 0x0000010006004003

def z442 : W := mkw 0x0000000000000000 0xfef00d34c7064c9f

def z443 : W := mkw 0x878065144c32d5b7 0xfef0ed34c7ffffff

def z444 : W := mkw 0x380fdfaa01ef6a40 0x77cfffcb01fff360

def z445 : W := mkw 0x8500651444324486 0xf210e10407764c9f

def z446 : W := mkw 0x4000004112000000 0x010012cb38000000

def z447 : W := mkw 0x380ddf8001cd2000 0x07cfffc00089b000

def z448 : W := mkw 0x1200000008058118 0x400000000007801c

def z449 : W := mkw 0x380ddf8001ef6000 0xffcfffcf01fff3e0

def z450 : W := mkw 0x8100450044224006 0x00000c00c006000c

def z451 : W := mkw 0x0000000000000000 0x98d0003001000c00

def z452 : W := mkw 0xc02cdfc1f6000000 0x07efffc0fe000000

def z453 : W := mkw 0x32070a28a9858b18 0x893f0238f8818f1c

def z454 : W := mkw 0x640bb07f13d80ec0 0xbffff3ff3ff80fe0

def z455 : W := mkw 0xb22fffbeed858b18 0xddffee38f9878f1c

def z456 : W := mkw 0x4080004112001021 0x000001c006007003

def z457 : W := mkw 0xc02edfebf6000000 0x052f1fcbfe000000

def z458 : W := mkw 0x000effbe00000000 0x0fcfffff00000000

def z459 : W := mkw 0x2c0bf5be01fa6ec0 0xbbdff1ff01f87fe0

def z460 : W := mkw 0x8500651444324486 0xdcf0ec30c1760c1c

def z461 : W := mkw 0x8000201444000000 0x08200034c6000000

def z462 : W := mkw 0x0000000000000000 0x0100100b00880360

def z463 : W := mkw 0xc2a44fc1fe009131 0xff601fcffe89f3f3

def z464 : W := mkw 0x0808d580006a6000 0x0000e00000700000

def z465 : W := mkw 0x8500651444324486 0xbad0e13407704c83

def z466 : W := mkw 0x8028f59644000000 0x0000e00000000000

def z467 : W := mkw 0x2003002801800a00 0x010f000800800300

def z468 : W := mkw 0x2809d58001ea6000 0x33cff1c001f87000

def z469 : W := mkw 0xfaafffffffeff131 0xffeffffffffff3f3

def z470 : W := mkw 0x000cdf8000000000 0x008fec0000000000

def z471 : W := mkw 0x0000000000000000 0x3340100000880000

def z472 : W := mkw 0x8500651444324486 0xbad0ec34c1760c8c

def z473 : W := mkw 0x4000004112000000 0x0820000f3e000000

def z474 : W := mkw 0x200b902a01c80a40 0xbb4f100f008803e0

def z475 : W := mkw 0x4688b0571a5895f1 0xff60f3cf3ef9f3f3

def z476 : W := mkw 0x0500201400324486 0xfad0e03401764c9f

def z477 : W := mkw 0xc02cffd756000000 0x07cfffc706000000

def z478 : W := mkw 0x4080004112001021 0x000010c300083060

def z479 : W := mkw 0x8500201444100486 0xbaf0e034c7700c9f

def z480 : W := mkw 0x8500651444324486 0x76d0ed30c1764c0c

def z481 : W := mkw 0x32070a28a9858b18 0x55cf0e0839878300

def z482 : W := mkw 0x3201000009858b18 0xdd70020839878f1c

def z483 : W := mkw 0x0000000000000000 0x54c00c0001060000

def z484 : W := mkw 0x040ab03e00100ec0 0x8bdff03f00000fe0

def z485 : W := mkw 0x428000411a009131 0x452013cb3e89f373

def z486 : W := mkw 0xe42bb07ff7d80ec0 0xbbfff03ffff80fe0

def z487 : W := mkw 0x0000000000000000 0xd010000001060c1c

def z488 : W := mkw 0xc78065555e32d5b7 0xfef0ed3fff764fff

def z489 : W := mkw 0x8508f516447a44c6 0xfef0fd37c77e4cff

def z490 : W := mkw 0x2401000001d80ec0 0x0010000001700c00

def z491 : W := mkw 0x4000004112000000 0x020011c706000000

def z492 : W := mkw 0xc02efffff6224000 0x7fefffffff764000

def z493 : W := mkw 0x668bb07f1bd89ff1 0xbbfff03f3ff80ff3

def z494 : W := mkw 0x428000411a009131 0xfe60010f3e0043f3

def z495 : W := mkw 0xd22efffffe058118 0x4feffffffe07801c

def z496 : W := mkw 0xa503653c45b24e86 0xffffed3cc7f64f9f

def z497 : W := mkw 0x428000411a009131 0xdd60020f3e8183f3

def z498 : W := mkw 0xf82ffffff7ef6000 0x0fefffffff760000

def z499 : W := mkw 0xd8244fc1f6276000 0x44200fc0fe07f000

def z500 : W := mkw 0x380ddf8001ef6000 0x228ffdc0017e7000

def z501 : W := mkw 0x8d08f594447a6486 0x2200f1c406787083

def z502 : W := mkw 0x7a8d9ac11bcdb131 0x010f12cb3889b360

def z503 : W := mkw 0x2409b01601d80ec0 0xb210f00701f80fe0

def z504 : W := mkw 0x0008900000000000 0x03cff00000000000

def z505 : W := mkw 0xa50bf53e45fa4ec6 0x009fec30c1760c0c

def z506 : W := mkw 0x0200000008008110 0xd000000000818310

def z507 : W := mkw 0x0500000000324486 0x2000000000704083

def z508 : W := mkw 0x722f9aebbb858b18 0x010f12cb38818300

def z509 : W := mkw 0x52840a41ba059139 0xff601fcffe8ff3ff

def z510 : W := mkw 0x380f9aaa01cd2a40 0x010f12cb0089b360

def z511 : W := mkw 0x30070a28a1850a08 0x000f000000000000

def z512 : W := mkw 0x728100411b859b39 0xff7013cf3f8fffff

def z513 : W := mkw 0xc02ebafff6000000 0x092f12fffe000000

def z514 : W := mkw 0x38054f8001a76000 0x55cf0fc00187f000

def z515 : W := mkw 0x4488b057125814e1 0x2200f1c7067870e3

def z516 : W := mkw 0xfa2fffffffefeb18 0xffffffffffffff1c

def z517 : W := mkw 0x0000000000000000 0xdc60000000000010

def z518 : W := mkw 0x00040a0000000000 0x05cf0e0000000000

def z519 : W := mkw 0x3c01000001ff6ec0 0xf010000001ffffe0

def z520 : W := mkw 0x1800000000276000 0x400000000007f000

def z521 : W := mkw 0x8500651444324486 0xaa30e134c6704c9f

def z522 : W := mkw 0xa50bf53e45fa4ec6 0xbbdffc3fc1fe0fec

def z523 : W := mkw 0x768fba7fbbdd9ff9 0xffffffffffffffff

def z524 : W := mkw 0x3c0dff9601ff64c0 0x77cfffc701fff0e0

def z525 : W := mkw 0x0000000000000000 0x44200c00c006001c

def z526 : W := mkw 0x7a8d9ac11bcdb131 0xff6f13cf3e89f3f3

def z527 : W := mkw 0x37070a28a9b7cf9e 0xfdff0e38f9f7cf9f

def z528 : W := mkw 0xc02cffd7f6000000 0x0620ffc7fe000000

def z529 : W := mkw 0x2009900001c80000 0xbbcff00f01f803e0

def z530 : W := mkw 0x36072a3ea9958fd8 0xddff0e3ff9878ffc

def z531 : W := mkw 0x0000450000224000 0x0080ec0001760000

def z532 : W := mkw 0x0000000000000000 0x8800000f000003e0

def z533 : W := mkw 0xe42bf5ff57d80ec0 0xbbdff1ff07f80fe0

def z534 : W := mkw 0x380ddf8001ef6000 0x07cfffc001760000

def z535 : W := mkw 0x428000411a009131 0xdd6003c83e81f313

def z536 : W := mkw 0xb02fffbee5850a08 0x009fec30c1060c0c

def z537 : W := mkw 0x10040a00a0050008 0x00000c00c006000c

def z538 : W := mkw 0x02000000a8008118 0x00200000f800001c

def z539 : W := mkw 0x2009900001c80000 0x010f100000880000

def z540 : W := mkw 0x18044f8000276000 0x76c0efc00177f000

def z541 : W := mkw 0x260bb03ea9d88fd8 0xbbfff03ff9f80ffc

def z542 : W := mkw 0x4000004112000000 0x7f6013cf3e89f000

def z543 : W := mkw 0x30070a28a1850a08 0xdcff0c30c1060c1c

def z544 : W := mkw 0x180cdf80006f6000 0x6600ffc0007ff000

def z545 : W := mkw 0xc0200041f6000000 0x00200000fe000000

def z546 : W := mkw 0x0000000000000000 0xba40000400000080

def z547 : W := mkw 0x0280000008009131 0x400000000001f013

def z548 : W := mkw 0x428000411a009131 0x0000000b38000360

def z549 : W := mkw 0xc000655556000000 0x0fe0fffffe000000

def z550 : W := mkw 0x428000411a009131 0x002000003e000013

def z551 : W := mkw 0x360fba3ea9dd8fd8 0xddffee38f9f78f1c

def z552 : W := mkw 0xb7072a3ced958f9e 0xddff0e3cff878f9f

def z553 : W := mkw 0x30070a28a1850a08 0x55df0e30c1878c0c

def z554 : W := mkw 0x2001000001800a00 0x9010000001800f00

def z555 : W := mkw 0x428000411a009131 0xfff01fffff8fffff

def z556 : W := mkw 0x0400201400100480 0x2200e00400700080

def z557 : W := mkw 0x38054f8001ef6000 0x74000fc001fff000

def z558 : W := mkw 0x2409b01601d804c0 0x33cff00701f800e0

def z559 : W := mkw 0x8500651444324486 0x2290ed34c7764c8f

def z560 : W := mkw 0x380fdfa801ef6a00 0xffdffff801ffff00

def z561 : W := mkw 0x0400201400100480 0xfef0ec34c1760c9c

def z562 : W := mkw 0x3a070a28a9efeb18 0xfdff0e38f9ffff1c

def z563 : W := mkw 0x04002016001004c0 0x00000007000000e0

def z564 : W := mkw 0x2501000001fa4ec6 0xf010000001fe4fff

def z565 : W := mkw 0x4080004112001021 0x00000007060000e3

def z566 : W := mkw 0x200ddf8001c80000 0x37cfffc001f80000

def z567 : W := mkw 0x3a0ddf8009efe110 0xffefffc839fff310

def z568 : W := mkw 0x0280000008009131 0x80000000000003f3

def z569 : W := mkw 0x8500651444324486 0xf090ec30c1764c9f

def z570 : W := mkw 0x3801000001ef6000 0x774013c001fff000

def z571 : W := mkw 0xc22efffffe008110 0xdfeffffffe818310

def z572 : W := mkw 0xf2afffffff859b39 0xffffffffff8fffff

def z573 : W := mkw 0x380d9a8001cd2000 0x000f000000000000

def z574 : W := mkw 0x3c0fffbe01ff6ec0 0x009fec3001760c00

def z575 : W := mkw 0x00044f8000000000 0x04000fc000000000

def z576 : W := mkw 0xc78065555e32d5b7 0xfef0eff4ff77fc9f

def z577 : W := mkw 0x420000411a008110 0xdf6013cf3e818310

def z578 : W := mkw 0x3d01000001ff6486 0xf010000001fffc9f

def z579 : W := mkw 0xb7076f3cedb7cf9e 0xddffee38f9f78f1c

def z580 : W := mkw 0xc2a44fc1fe009131 0x44200fc0fe01f013

def z581 : W := mkw 0x02020028a8008b18 0xdcf00c38f9060f1c

def z582 : W := mkw 0x8500201444100486 0x00100030c0000c0c

def z583 : W := mkw 0x722f9aebbb858b18 0xddff1efbf9878f1c

def z584 : W := mkw 0x93044f00ec27c11e 0x44200f00fe07c01f

def z585 : W := mkw 0xc52efffff6324486 0x2feffffffe704083

def z586 : W := mkw 0xc02045c156000000 0x000001c006000000

def z587 : W := mkw 0x0402203e00100ec0 0xbb50103f00880fe0

def z588 : W := mkw 0xc500655556324486 0xfff0ffffff764c9f

def z589 : W := mkw 0x0000000000000000 0x0b40100f00000000

def z590 : W := mkw 0x360fba3ea9dd8fd8 0xbbdff23f39f98fe0

def z591 : W := mkw 0x0500000000100486 0x8010000000000c9f

def z592 : W := mkw 0xb2076f3ced858b18 0xdfffef3cff878f1c

def z593 : W := mkw 0x2009d50001ea4000 0x77cffd0001fe4000

def z594 : W := mkw 0x380fffbe01ef6000 0x7fcfffff01fff000

def z595 : W := mkw 0x32070a28a9858b18 0xdd6f020838818310

def z596 : W := mkw 0x0400000000100ec0 0x8010000000000fe0

def z597 : W := mkw 0x0400201400100480 0xfef0e13407704c93

def z598 : W := mkw 0x0200000008008110 0xff6013c83889f310

def z599 : W := mkw 0x0000450000224000 0x44000d0000064000

def z600 : W := mkw 0x428000411a009131 0x000002c03801b000

def z601 : W := mkw 0xc02efffff6000000 0x028ffdf7c6000000

def z602 : W := mkw 0xd2244fc1fe058118 0x44200fc0fe07801c

def z603 : W := mkw 0x02060a28a8008b18 0x8dff0e38f8000f1c

def z604 : W := mkw 0x3001000001850000 0x5000000001878000

def z605 : W := mkw 0x8000651444000000 0xfee0ed34c6004093

def z606 : W := mkw 0x3a074fa8a9a7eb18 0xddff0ff8f987ff1c

def z607 : W := mkw 0xf02ffffff7850a08 0x0fffffffff060c0c

def z608 : W := mkw 0xc2a8f5d75e009131 0xff60f3cf3e89f3f3

def z609 : W := mkw 0xf2274fe9ff858b18 0xddff0ff8ff878f1c

def z610 : W := mkw 0x0002203e00000000 0x0800003f00000000

def z611 : W := mkw 0x8100450044224006 0xfe600d04c606409f

def z612 : W := mkw 0x240bb03e01d80ec0 0xb09fe03001f80fe0

def z613 : W := mkw 0x2003002801800a00 0xddff0c38c1860f1c

def z614 : W := mkw 0x8000651444000000 0xdef0ed34c7060c1c

def z615 : W := mkw 0xc78020555e1095b7 0x8830003ffe000fff

def z616 : W := mkw 0x3a0ddf80a9efe118 0x77efffc0f9fff01c

def z617 : W := mkw 0x80244f80e4000000 0x00000c00c0000000

def z618 : W := mkw 0x380ddf8001ef6000 0x33cffc0001fe0000

def z619 : W := mkw 0x0000000000000000 0x074013c000000000

def z620 : W := mkw 0x428000411a009131 0x774013cb3889f360

def z621 : W := mkw 0x428000411a009131 0x776013c03e89f013

def z622 : W := mkw 0x380ddf8001ef6000 0x450f1fc0008ff000

def z623 : W := mkw 0xf82ddfc1f7ef6000 0x77efffc0fffff000

def z624 : W := mkw 0x8500201444100486 0xdcf00c34c7060c9f

def z625 : W := mkw 0x30050a0001850000 0x77cf1fc0018ff000

def z626 : W := mkw 0x628990411bc89131 0xffeff3cf3ff9f3f3

def z627 : W := mkw 0x3a0fdfa8a9efeb18 0xddffee38f9f78f1c

def z628 : W := mkw 0x32050a00a9858118 0x55ef0e00f987801c

def z629 : W := mkw 0x0002002a00000a40 0x0000000b00000360

def z630 : W := mkw 0xa42fffbee5d80ec0 0x009fec30c1700c00

def z631 : W := mkw 0x72850a411b859131 0xffef1fcf3f8ff3f3

def z632 : W := mkw 0x8100450044224006 0xdcf00d30c7064c1f

def z633 : W := mkw 0xa42fffbee5d80ec0 0xbbdffc3fc1f80fe0

def z634 : W := mkw 0x22030028a9808b18 0x99ff0038f9800f1c

def z635 : W := mkw 0x3c0ddf8001ff6ec0 0xf7dfffc001ffffe0

def z636 : W := mkw 0x12040a00a8058118 0xdd600e08f887831c

def z637 : W := mkw 0x4080004112001021 0x774013c70689f0e3

def z638 : W := mkw 0xbd0dff9445ff6486 0x77cfffc407fff083

def z639 : W := mkw 0x38050a0001ef6000 0x75cf0e0001fff000

def z640 : W := mkw 0x240b902a01d80ec0 0xb11f100b01f80fe0

def z641 : W := mkw 0x18040a8000052000 0x000002c00001b000

def z642 : W := mkw 0x850af53e44324486 0xfffffd3fc7764c9f

def z643 : W := mkw 0x200bb03e01c80a40 0x0bcff03f00880360

def z644 : W := mkw 0x428000411a009131 0x4f6013cf3e01f013

def z645 : W := mkw 0x0500450000324486 0xf6d0ed0001764c9f

def z646 : W := mkw 0x428000411a009131 0x662013c73e09f0f3

def z647 : W := mkw 0x428cdfc11a009131 0xffefffcf3e89f3f3

def z648 : W := mkw 0x3c0fffbe01ff6ec0 0x77dffff001fffc00

def z649 : W := mkw 0x0808d580006a6000 0x7740f3c000f9f000

def z650 : W := mkw 0x380d9a8001cd2000 0x55cf1ec0018fb000

def z651 : W := mkw 0x802effbee4000000 0x07cffff0c0000000

def z652 : W := mkw 0x0400201400100480 0xbbd0f03f01f80fe0

def z653 : W := mkw 0x428000411a009131 0x0f6013cf3e89b360

def z654 : W := mkw 0x0000000000000000 0x220011c000087000

def z655 : W := mkw 0x428000411a009131 0x8f6013cf3e0003f3

def z656 : W := mkw 0x2403203c01900e80 0xbbdfe03c01f00f80

def z657 : W := mkw 0x30070a28a1850000 0x5def0e38f9878000

def z658 : W := mkw 0x000cdf8000000000 0x77cfffc00089f000

def z659 : W := mkw 0xc022657ff6000000 0x0ee0ed3ffe000000

def z660 : W := mkw 0xb70fff3eedffcfde 0xffffff3fffffcfff

def z661 : W := mkw 0x2403203e01900ec0 0x99df003f01800fe0

def z662 : W := mkw 0x8022203ee4000000 0x00000030c0000000

def z663 : W := mkw 0x240fffbe01d80ec0 0xbfdfffff01f80fe0

def z664 : W := mkw 0x0000000000000000 0x9940000800800300

def z665 : W := mkw 0x0602203ea8108fd8 0x8830003ff8000ffc

def z666 : W := mkw 0xb5076f3ce5b74e8e 0x009fec30c1760c0c

def z667 : W := mkw 0x240bb03e01d80ec0 0x891f103f00880fe0

def z668 : W := mkw 0x0500000000324486 0xfcf00c30c1764c9f

def z669 : W := mkw 0x3a8ddf8009eff131 0xf7cfffc001fff3f3

def z670 : W := mkw 0x040ab03e00580ec0 0xaa10f03f00780fe0

def z671 : W := mkw 0x72070a69bb858b18 0xdfff1fffff878f1c

def z672 : W := mkw 0x32070a28a9858b18 0xd11f020839878f1c

def z673 : W := mkw 0x2003002801800a00 0x009f003001000c00

def z674 : W := mkw 0x0200000008008110 0x0100020838818300

def z675 : W := mkw 0x10040a0000050000 0x44000e0000078000

def z676 : W := mkw 0x0408b016005804c0 0xbb40f00f00f803e0

def z677 : W := mkw 0xa40bf53e45d80ec0 0xbffffd3fc7f80fe0

def z678 : W := mkw 0x0200000008008110 0x4420020038018010

def z679 : W := mkw 0x08000000006a6000 0x2000000000787000

def z680 : W := mkw 0x0000000000000000 0x0d60020838000000

def z681 : W := mkw 0xc2a2207ffe009131 0x8820003ffe0003f3

def z682 : W := mkw 0x340fba3e01dd0ec0 0xffdffe3f01ff8fe0

def z683 : W := mkw 0xbd0dff9445ff6486 0xfeffed34c7764c9f

def z684 : W := mkw 0x428ab07f1a009131 0xffeff3ff3e89f3f3

def z685 : W := mkw 0x380fdfa8a1ef6a08 0x009fec30c1760c0c

def z686 : W := mkw 0xa50bf53e45fa4ec6 0xbbdff13f07f84fe3

def z687 : W := mkw 0x2001000001800000 0x11cf000001800000

def z688 : W := mkw 0x300ddf8001850000 0x57cfffc001878000

def z689 : W := mkw 0x3d0ddf8001ff6486 0xf7dfffc001fffc9f

def z690 : W := mkw 0x0000000000000000 0x32c0e00001700000

def z691 : W := mkw 0x240bb03e01d80ec0 0x229ff03701780ce0

def z692 : W := mkw 0xc522657ff6324486 0xfef0ed3fff764c9f

def z693 : W := mkw 0x0008900000480000 0x2200f00000780000

def z694 : W := mkw 0x668100411bd89ff1 0xff7013cf3ff9fff3

def z695 : W := mkw 0xc5246fd5f6324486 0xfef0eff4ff764c9f

def z696 : W := mkw 0xc0a8f5d756001021 0x2200f1c7060870e3

def z697 : W := mkw 0xc0246fd5f6000000 0x0ee0eff4fe000000

def z698 : W := mkw 0x42ae9aebba009131 0x010f12cb3889b360

def z699 : W := mkw 0x380d9a8001ef6000 0x710f12c001fff000

def z700 : W := mkw 0x97046f14ec37c59e 0xfef0ef34ff77cc9f

def z701 : W := mkw 0x18044f8000276000 0x00000c0000060000

def z702 : W := mkw 0x428000411a009131 0xfe6003c43e01f093

def z703 : W := mkw 0x72870a69bb859b39 0x010f12cb3889b360

def z704 : W := mkw 0x0008900200480040 0x0000100300080060

def z705 : W := mkw 0xc022207ff6000000 0x0f6013fffe000000

def z706 : W := mkw 0x8500651444100486 0x8ef0ed34c6000c9f

def z707 : W := mkw 0x3701000009958f9e 0xd010000001878f9f

def z708 : W := mkw 0xc02efffff6000000 0x0feffffffe880360

def z709 : W := mkw 0xc02efffff6224000 0x0fefffffff760000

def z710 : W := mkw 0xc02cdfc1f6000000 0x0fefffcffe000000

def z711 : W := mkw 0x402e9aebb2480040 0x010f12cb38080060

def z712 : W := mkw 0x70870a69b3851a29 0x229f1df7c70e7cef

def z713 : W := mkw 0x240bb03e01d80ec0 0xbffff23f39f80fe0

def z714 : W := mkw 0xc02efffff6000000 0x07cffffbf8000000

def z715 : W := mkw 0xc78065555e32d5b7 0x0190fefbf9ffbf6c

def z716 : W := mkw 0x400cdfc112000000 0x07efffc03e000000

def z717 : W := mkw 0xb7076f3cedb7cf9e 0x230fe30c3ef1c383

def z718 : W := mkw 0x3201000009858b18 0x5000000001878300

def z719 : W := mkw 0x428000411a009131 0xbb4013cf3e89f3e3

def z720 : W := mkw 0x3601201409dd8fd8 0xfef0ec34c1ff8ffc

def z721 : W := mkw 0x0402203e00100ec0 0xff5013ff0089ffe0

def z722 : W := mkw 0xc02efffff6000000 0x0defee3ffe000000

def z723 : W := mkw 0x028cdf8008009131 0xf7cfffc00089f3f3

def z724 : W := mkw 0xc42efffff65804c0 0xbfffffffff780ce0

def z725 : W := mkw 0x2681000009d89ff1 0xb010000001f80ff3

def z726 : W := mkw 0x380ddf8001ef6a40 0x77cfffc001fff360

def z727 : W := mkw 0x380ddf8001ef6000 0xf7cfffc001fff3e0

def z728 : W := mkw 0x3201000009858b18 0x9010000001818f00

def z729 : W := mkw 0xc0aefffff6001021 0x0feffffffe0000e3

def z730 : W := mkw 0xc02efffff6000000 0x0eefeff4fe000000

def z731 : W := mkw 0x240bb03ea1d80ec0 0xbbfff03ff9f80fe0

def z732 : W := mkw 0x30054f0001a74000 0x77cfffc001fff000

def z733 : W := mkw 0x380ddf8001ef6000 0x76cfefc00177f000

def z734 : W := mkw 0x380d9a8001cd2000 0x018ff2c001f9b000

def z735 : W := mkw 0xc12efffff6224006 0x0feffffffe004003

def z736 : W := mkw 0x3201000009858b18 0xf0100000018fff1c

def z737 : W := mkw 0x40260a6bb2000000 0x0def0e3bf8000000

def z738 : W := mkw 0x3701000009b7cf9e 0xd010000001f78f1c

def z739 : W := mkw 0x32070a28a9858b18 0xfdff0e38f98f8ffc

def z740 : W := mkw 0xc02edfebf6000000 0x010f1ecbf8000000

def z741 : W := mkw 0x2009d50001ea4000 0x77cfffc001fff000

def z742 : W := mkw 0x000cdf8000000000 0x0fefffc838000000

def z743 : W := mkw 0x240bb03e01d80ec0 0xbfdff3ff01f80fe0

def z744 : W := mkw 0x628990411bc89131 0xbbeff00f3ff803f3

def z745 : W := mkw 0x40060a69b2000000 0x0def0ff8fe000000

def z746 : W := mkw 0xc02efffff6000000 0x0deffefbf8000000

def z747 : W := mkw 0x380ddf8001ef6000 0x07cfffc001ffb000

def z748 : W := mkw 0xc52efffff6324486 0xfeffed3fff764c9f

def z749 : W := mkw 0x000effbea0000000 0x0feffffff8000000

def z750 : W := mkw 0x000ab03ea0000000 0x0beff03ff8000000

def z751 : W := mkw 0x0a0ad5a8a86aeb18 0xaa30f1f8f8787f1c

def z752 : W := mkw 0x240bb03e01d80ec0 0xfffffd3fc7fe4fff

def z753 : W := mkw 0xc02af5ff56000000 0x0feff3ff3e000000

def z754 : W := mkw 0xc12efffff6224006 0x0feffffffe06000c

def z755 : W := mkw 0x85066f3ce4324486 0x0dffee38f9760c0c

def z756 : W := mkw 0xc8aefffff66a7021 0x2feffffffe7870e3

def z757 : W := mkw 0x8500651444324486 0xfef0eff4c777fc9f

def z758 : W := mkw 0xc42efffff61004c0 0x0feffffffe0000e0

def z759 : W := mkw 0x32070a28a9858b18 0xddff0e3cff878f9f

def z760 : W := mkw 0xd82efffff6276000 0x7feffffffe8ff000

def z761 : W := mkw 0x2281000009c89b71 0xf00000000089f3f3

def z762 : W := mkw 0xb20165144d858b18 0xdef0ed34c7878f1c

def z763 : W := mkw 0x240bb03e01d80ec0 0x899ff03f01f80fe0

def z764 : W := mkw 0xc02edfebf6000000 0x010f13cb3e000000

def z765 : W := mkw 0xc02ebafff6000000 0x0beff2fffe000000

def z766 : W := mkw 0x32070a28a9858b18 0xffff1f3fff8fcfff

def z767 : W := mkw 0x00060a28a0000000 0x0dff0e38f9060c0c

def z768 : W := mkw 0x402e9aebb2000000 0x774f13cb3889f000

def z769 : W := mkw 0x180cdf80006f6000 0x67cfffc0007ff000

def z770 : W := mkw 0x3281000009859b39 0xfef00d34c78fffff

def z771 : W := mkw 0x582edfebb2276000 0x450f1fcb3807f000

def z772 : W := mkw 0xc5266f7ff6324486 0xffffef3fff764c9f

def z773 : W := mkw 0x7a8ddfc11beff131 0x88afec0f3f7603f3

def z774 : W := mkw 0x380ddf8001ef6000 0xffefffcf07fff3f3

def z775 : W := mkw 0xb70165144db7cf9e 0xd090ec30c1f78f1c

def z776 : W := mkw 0x452e9aebb2324486 0xf11f12cb39764c9f

def z777 : W := mkw 0x040ab03e00100ec0 0xbbdff03f01700fe0

def z778 : W := mkw 0x3281000009859b39 0xd0100000018fbf7c

def z779 : W := mkw 0x380ddf80a1ef6008 0x77cfffc0c1fff00c

def z780 : W := mkw 0x3a01000009cdab18 0xd0100000018fbf1c

def z781 : W := mkw 0x2809d58001ea6000 0x77cff3c001f9f000

def z782 : W := mkw 0x000cdf8000224000 0x77cfffc001fff000

def z783 : W := mkw 0x32070a28a9858b18 0x009f0e30f9078c0c

def z784 : W := mkw 0xc02efffff6000000 0x05affffbfe000000

def z785 : W := mkw 0x200b902801c80a00 0xbbdff03f01f80fe0

def z786 : W := mkw 0x82aeffbeec009131 0xf08fec30c089f3f3

def z787 : W := mkw 0x00060a28a0000000 0x018f0e38f8000000

def z788 : W := mkw 0x3a054f8009a7eb18 0xd4100fc00187ff1c

def z789 : W := mkw 0x400eba7fb2000000 0x0feffffffe000000

def z790 : W := mkw 0xc02efffff6224000 0x4feffffffe064000

def z791 : W := mkw 0xc52efffff6324486 0xfffffffffffe4fff

def z792 : W := mkw 0x3301000009a7cb1e 0xd01000000187cf1f

def z793 : W := mkw 0x340bb03e01dd0ec0 0xfbdff03f01ff8fe0

def z794 : W := mkw 0xc42efffff65804c0 0xbfeffffffef803e0

def z795 : W := mkw 0x8500651444324486 0xf290ed34c7764c9f

def z796 : W := mkw 0xd82efffff6276000 0x7fefffffff77f000

def z797 : W := mkw 0x00060a28a0000000 0xffef0f3cfe004093

def z798 : W := mkw 0x30070a28a1850a08 0x5dff0e38f9878c0c

def z799 : W := mkw 0x3a070a28a9cdab18 0xddff0e38f98fbf1c

def z800 : W := mkw 0x380fdfa8a1ef6000 0xfffffff8f9fffc1c

def z801 : W := mkw 0x2409b01601d80ec0 0xb3dff00701f80fe0

def z802 : W := mkw 0x2409900001d80ec0 0xbbdff00f01f80fe0

def z803 : W := mkw 0x42860a69ba009131 0xffff1fffff8fffff

def z804 : W := mkw 0xc02efffff6000000 0x072fffcffe000000

def z805 : W := mkw 0x32050a00a9858118 0xddff0e30f9878c1c

def z806 : W := mkw 0xb82ddf80e5ef6000 0x77cfffc0c1fff000

def z807 : W := mkw 0xc528f5d7567a44c6 0x2200f1c7067840e3

def z808 : W := mkw 0x240bb03e01d80ec0 0x2bcff03f00f803e0

def z809 : W := mkw 0x32070a28a9858b18 0x8dff0e38f9060f1c

def z810 : W := mkw 0xd02efffff6050008 0x0feffffffe06000c

def z811 : W := mkw 0x852effbee4324486 0xffffef3cff764c9f

def z812 : W := mkw 0xc02af5fff6000000 0x0beff1fffe000000

def z813 : W := mkw 0x00040a00a0000000 0x05ef0e00f8000000

def z814 : W := mkw 0x240bb03e01d80ec0 0xfbdff03f01f84ff3

def z815 : W := mkw 0x32870a28a9859b39 0xffff1ff8f98fffff

def z816 : W := mkw 0x8d00659444326486 0xfef0edf4c7767c9f

def z817 : W := mkw 0x3a01000009a7eb18 0xd01000000187ff1c

def z818 : W := mkw 0x80262a3ee4000000 0x0def0e38f8000000

def z819 : W := mkw 0xc5266ffdf6324486 0xffffeffcff764c9f

def z820 : W := mkw 0x380ddf8001ef6000 0x748fefc001fff000

def z821 : W := mkw 0x32070a28a9858b18 0xffff1ffcff8fff9f

def z822 : W := mkw 0x3201000009858b18 0xd0900c30c1878f1c

def z823 : W := mkw 0xcd88f5d5567a74a7 0x2200f1c7067870e3

def z824 : W := mkw 0x240bb03e01d80ec0 0xab1ff03f00f80fe0

def z825 : W := mkw 0x8500651444324486 0x66b0ed34c7764c9f

def z826 : W := mkw 0x002e9aaaa0000000 0x010f020838000000

def z827 : W := mkw 0x428000411a009131 0xff7013cf3f8fffff

def z828 : W := mkw 0x38054f8001a76000 0x77cfefc001f7f000

def z829 : W := mkw 0xc02efffff6224000 0x2feffffffe704000

def z830 : W := mkw 0xd82efffff6052000 0x0feffffffe01b000

def z831 : W := mkw 0xc02efffff6000000 0xbfeffffffe000080

def z832 : W := mkw 0x32070a28a9858b18 0xddff0f38ff87cf1f

def z833 : W := mkw 0x428000411a009131 0xffe01fcf3f8ff3f3

def z834 : W := mkw 0x380ddf80a1ef6000 0x77efffc0f9fff000

def z835 : W := mkw 0x400cdfc112000000 0x07cfffcb38000000

def z836 : W := mkw 0x8500651444324486 0xf8b0ec34c7764c9f

def z837 : W := mkw 0x32070a28a9858b18 0x009f0c38f9060f0c

def z838 : W := mkw 0x850eff3ee4324486 0xffffff3fff764c9f

def z839 : W := mkw 0x8500651444324486 0xfef0fdf4c77e7c9f

def z840 : W := mkw 0x428000411a009131 0x2f6013cf3e89f3e3

def z841 : W := mkw 0x8500651444324486 0xdcf0ed30c7764c1f

def z842 : W := mkw 0xc52efffff6324486 0xbfffffffff760c8c

def z843 : W := mkw 0x040ab03e00100480 0xbbdff03f01f80fe0

def z844 : W := mkw 0x240bb03e01d80ec0 0xffdffc3f01fe0fe0

def z845 : W := mkw 0x40060a69b2000000 0x010f12cb38000000

def z846 : W := mkw 0x400c9ac112000000 0x0f6f13cf3e000000

def z847 : W := mkw 0x32050a00a9858b18 0xd0100c00c1878f1c

def z848 : W := mkw 0x200b902a01c80a40 0xbbdff03b01f80f60

def z849 : W := mkw 0x32870a28a9859b39 0xffff0f3cff8fffff

def z850 : W := mkw 0x380ddf8001ef6000 0xf7dfffc001fffc1c

def z851 : W := mkw 0x428000411a009131 0xff7013fffe89ffff

def z852 : W := mkw 0x00060a28a0000000 0x05cf0e0838000000

def z853 : W := mkw 0xc02efffff6000000 0x0bcffefff8000000

def z854 : W := mkw 0xc5066f7df6324486 0xffffffffff764c9f

def z855 : W := mkw 0x240bb03e01d80ec0 0xfbdff03f01fe0ffc

def z856 : W := mkw 0x00060a28a0000000 0x8dff0e38f8000c1c

def z857 : W := mkw 0x240bb03e01d80ec0 0xbffff13f07f80fe0

def z858 : W := mkw 0x02060a28a8008110 0xddff0e38f9878f1c

def z859 : W := mkw 0x668bb07f1bd89ff1 0x44bfe3f03f71fc13

def z860 : W := mkw 0x7a89d5c11beff131 0xf200f1c707fff3f3

def z861 : W := mkw 0xc02ebafff6000000 0x0f6f13fffe000000

def z862 : W := mkw 0x442ebaffb2100480 0xbbdff2ff39700c80

def z863 : W := mkw 0x30070a28a1850a08 0x019f0e38f9060c0c

def z864 : W := mkw 0x3609b01609dd8fd8 0xf210f00701ff8ffc

def z865 : W := mkw 0x7a8f9ae9bbcdbb39 0x010f12cb3889b360

def z866 : W := mkw 0xcd28f5d7567a6486 0x2200f1c706787083

def z867 : W := mkw 0xc02efffff6000000 0x07effff0fe000000

def z868 : W := mkw 0x30070a28a1850a08 0x04bf0e30f9060c0c

def z869 : W := mkw 0x380ddf8001ef6000 0xfffffff4c7fffc9f

def z870 : W := mkw 0x8100450044224006 0xfef0ed30c7764c1f

def z871 : W := mkw 0xa42bb03ee5d80ec0 0xbbdff03fc1f80fe0

def z872 : W := mkw 0x402e9aebb2000000 0xddff1efbf9060c1c

def z873 : W := mkw 0x3201000009858b18 0xd550020001878f1c

def z874 : W := mkw 0xf8254fc1f7ef6000 0x74200fc0fffff000

def z875 : W := mkw 0x380ddf8001ef6000 0x670fffc000fff000

def z876 : W := mkw 0x2281000009c89131 0xf000000001f9f3f3

def z877 : W := mkw 0xf229f5d75f858b18 0xd210f1c707878f1c

def z878 : W := mkw 0xc02efffff6000000 0x0bcff3ff3e000000

def z879 : W := mkw 0x402e9aebb2000000 0x0fef1ffffe000000

def z880 : W := mkw 0xc7a2207ffe1095b7 0x8830003ffe000fff

def z881 : W := mkw 0x0400201400100480 0xfef0ed34c7764c9f

def z882 : W := mkw 0x040eba3ea0100480 0xfffffe3ff9760c9c

def z883 : W := mkw 0x850effbce4324486 0xfffffffcff764c9f

def z884 : W := mkw 0xbd0dba9445dd2486 0x893f12f4c689bc9f

def z885 : W := mkw 0xc5a8f5d7563254a7 0x2200f1c7067870e3

def z886 : W := mkw 0x800effbce4000000 0x0feffffcfe000000

def z887 : W := mkw 0xc0264fe9f6000000 0x052f0fc8fe000000

def z888 : W := mkw 0x240bb03e01d80ec0 0xbbdff2ff01f9bfe0

def z889 : W := mkw 0x240bb03e01d80ec0 0xbadfe03f01700fe0

def z890 : W := mkw 0xbf0165144dffef9e 0xfef0ed34c7ffff9f

def z891 : W := mkw 0xc02efffff6000000 0x038ffffffe000000

def z892 : W := mkw 0x3a070aa8a985ab18 0xddff0ef8f987bf1c

def z893 : W := mkw 0x000e9aa8a0000000 0x010f12c838000000

def z894 : W := mkw 0x240bb03e01d80ec0 0xbb4ff00f00f803e0

def z895 : W := mkw 0xc02efffff6000000 0x0f6ff3cf3e000000

def z896 : W := mkw 0x3201000009858b18 0x0010000001878f0c

def z897 : W := mkw 0x3a81000009eff131 0x7000000001fff360

def z898 : W := mkw 0xc02efffff6000000 0x9fffffffff000c00

def z899 : W := mkw 0xc0262a7ff6000000 0x0fef1ffffe000000

def z900 : W := mkw 0x32870a28a9859b39 0xddff0e38f98fbf7c

def z901 : W := mkw 0x402ebaffb2000000 0x090f12ff38000000

def z902 : W := mkw 0x380ddf8001ef6000 0x728ffdc001fff000

def z903 : W := mkw 0xc52efffff6324486 0x0feffffffe700000

def z904 : W := mkw 0x00060a28a0000000 0x092f0238f8000000

def z905 : W := mkw 0xc782207dfe109fbf 0x8830003ffe000fff

def z906 : W := mkw 0x3201000009858b18 0xfe7001040787cf9f

def z907 : W := mkw 0x240bb03e01d80ec0 0xbbdff1ff01f87fe0

def z908 : W := mkw 0xc42efffff6100480 0xbffffffffff80fe0

def z909 : W := mkw 0xb78165144db7dfbf 0xfef0ed34c7ffffff

def z910 : W := mkw 0x3281000009859b39 0xd01000000187ff1f

def z911 : W := mkw 0x080cdf80006a6000 0x77cfffc000f9f000

def z912 : W := mkw 0xc02efffff6000000 0x09affefffe000000

def z913 : W := mkw 0x3201450009a7cb18 0xf6d0ed0001f7cf1c

def z914 : W := mkw 0x00040a00a0000000 0x44200e00f806001c

def z915 : W := mkw 0x32070a28a9858b18 0xffff1e38f98f8f1c

def z916 : W := mkw 0x402e9aebb2000000 0xbb4f12cf388803e0

def z917 : W := mkw 0xc12efffff6224006 0x7fefffffff76401f

def z918 : W := mkw 0xd3844f41fe27d13f 0x44200fc0fe07f01f

def z919 : W := mkw 0x00060a28a0000000 0x5def0e38f9060000

def z920 : W := mkw 0x3203002809858b18 0xd810003801878f1c

def z921 : W := mkw 0x80064f28e4000000 0x0def0f38fe000000

def z922 : W := mkw 0x380ddf8001ef6000 0x7fefffc839fff000

def z923 : W := mkw 0x3201000009858b18 0xf75013c0018fff1c

def z924 : W := mkw 0xc02cdfc1f6000000 0x04afefc0fe000000

def z925 : W := mkw 0x22030028a9808b18 0xddff0c38f9860f1c

def z926 : W := mkw 0x12060a28a8058118 0xddff0e38f9078c1c

def z927 : W := mkw 0xc52efffff6324486 0xbfffffffff704c83

def z928 : W := mkw 0x10060a28a0050008 0x0def0e38f806000c

def z929 : W := mkw 0x3601000009dd8fd8 0xd010000001f78f1c

def z930 : W := mkw 0x380ddf8001ef6000 0x730ff3c001fff000

def z931 : W := mkw 0x402e9aebb2000000 0x074f13cb38000000

def z932 : W := mkw 0xc02efffff6224000 0x7feffffffffff000

def z933 : W := mkw 0x428000411a009131 0x220011c70689f3e3

def z934 : W := mkw 0x380ddf8001ef6000 0x010ff2c000f9b000

def z935 : W := mkw 0x3201000009cd8b18 0xf010000001ff8f1c

def z936 : W := mkw 0x160cba16a85d85d8 0x6620fe07f87f80fc

def z937 : W := mkw 0x4008904112000000 0x0feff3cf3e000000

def z938 : W := mkw 0x8500651444324486 0x00b0ec30c7760c1f

def z939 : W := mkw 0x8500201444100486 0xfef0ec34c7760c9f

def z940 : W := mkw 0x728f9a6bbbcd9b79 0x010f12cb3889b360

def z941 : W := mkw 0x1c066fbe00376ec0 0xcc100fff0007ffe0

def z942 : W := mkw 0x240bb03e01d80ec0 0x009fe03b01700f60

def z943 : W := mkw 0xc82efffff6226000 0x0feffffffe007000

def z944 : W := mkw 0x10060a28a0050000 0x4def0e38f8078000

def z945 : W := mkw 0x000eba3ea0000000 0x0bcff23f38000000

def z946 : W := mkw 0x240bb03e01d80ec0 0x010ff00b00f80360

def z947 : W := mkw 0xc0266f7ff6000000 0x0fefef3ffe000000

def z948 : W := mkw 0x3281000009859b39 0x000000000089b360

def z949 : W := mkw 0xf823207ff7ef6000 0x7820003ffffff000

def z950 : W := mkw 0x4682207fba109ff9 0x8830003ffe000fff

def z951 : W := mkw 0xc0aefffff6001021 0x7feffffffe89f0e3

def z952 : W := mkw 0x3201000009858b18 0xd4d00c0001878f1c

def z953 : W := mkw 0x32070a28a9858b18 0xd8bf0c38f9878f1c

def z954 : W := mkw 0x40060a69b2000000 0x0def0e3ffe000000

def z955 : W := mkw 0xc02efffff6000000 0x9feffffffe800300

def z956 : W := mkw 0xc12efffff6000006 0x0feffffffe00001f

def z957 : W := mkw 0x32030028a9858b18 0xd0100030c1878f1c

def z958 : W := mkw 0x448ab07f125814e1 0x2feff3ff3e7870e3

def z959 : W := mkw 0xc02ab07ff6000000 0x0feff3fffe000000

def z960 : W := mkw 0x32070a28a9cd8b58 0xddff0e38f98f8f7c

def z961 : W := mkw 0xc52efffff6324ec6 0xffffffffff764fff

def z962 : W := mkw 0xc02efffff6000000 0x0feffffffe89b000

def z963 : W := mkw 0x240bb03e01d80ec0 0x8bdff03f01700fe0

def z964 : W := mkw 0x2781000009fadff7 0xf010000001ffffff

def z965 : W := mkw 0x00040a0000000000 0x55cf0e0001060000

def z966 : W := mkw 0x180cdf8000276000 0x77cfffc00177f000

def z967 : W := mkw 0x3a01000009efeb18 0xd010000001f78f1c

def z968 : W := mkw 0x040ab03e00580ec0 0xabdff03f00780fe0

def z969 : W := mkw 0xb90ddf8045ef6006 0x77cfffc0c1fff00c

def z970 : W := mkw 0x250bb03e01d80ec6 0xbbdff03f01f80fff

def z971 : W := mkw 0x2009900001c80000 0x33cff00b01f80360

def z972 : W := mkw 0xc0266ffff6000000 0x0def0ffffe000000

def z973 : W := mkw 0x3a81000009eff131 0x7000000001fff013

def z974 : W := mkw 0xc42efffff6324480 0xffffffffff764c80

def z975 : W := mkw 0xc02efffff6000000 0x8feffffffe0003e0

def z976 : W := mkw 0x3a81450009eff131 0xfee0ed0407fff3f3

def z977 : W := mkw 0x8500651444324486 0xfef0fd37c77e4cff

def z978 : W := mkw 0x40860a69b2001021 0x2fef1ffffe0870e3

def z979 : W := mkw 0x02060a28a8008b18 0xddff0e38f9060f1c

def z980 : W := mkw 0x0002002800000000 0x99df003801000c00

def z981 : W := mkw 0x3201000009a7cb18 0xf010000001f7cf1c

def z982 : W := mkw 0xc50af57f56324486 0xffffffffff764c9f

def z983 : W := mkw 0xc0266ffdf6000000 0x0fefeffcfe000000

def z984 : W := mkw 0x3a01000009efeb18 0x7000000001fff300

def z985 : W := mkw 0x200bb03e01c80000 0xbbcff03f01f803e0

def z986 : W := mkw 0x32070a28a9858b18 0x55ff0e30f9878c1c

def z987 : W := mkw 0xc588f557567a54e7 0x2200f1c7067870e3

def z988 : W := mkw 0x85066f3ce4324486 0x2fefef3cfe704083

def z989 : W := mkw 0x0000450000224000 0xfef0ed34c7764c9f

def z990 : W := mkw 0x5a844fc11a27f131 0x44000fc03807f000

def z991 : W := mkw 0x00062a3ca0000000 0x0fefee3cf8000000

def z992 : W := mkw 0x2009900001c80000 0x33cff2c001f9b000

def z993 : W := mkw 0xc02edfebf6000000 0x07efffcbfe000000

def z994 : W := mkw 0xc52efffff6100ec6 0x8ffffffffe000fff

def z995 : W := mkw 0xc02efffff6000000 0x0d2f1ffffe000000

def z996 : W := mkw 0x380d9a8001cd2000 0x77cff3c001f9f000

def z997 : W := mkw 0x3201000009858b18 0xd8300030c1878f1c

def z998 : W := mkw 0x400edfe9b2000000 0x0feffffffe000000

def z999 : W := mkw 0x40060a69b2000000 0x0f6f13cf3e000000

def z1000 : W := mkw 0x2409b01601d804c0 0xbbcff00f01f803e0

def z1001 : W := mkw 0x3201000009858b18 0x4010000001078c1c

def z1002 : W := mkw 0xa10bd52a45ea4a46 0x452f1d0bc68e437f

def z1003 : W := mkw 0x00060a28a0000000 0xddef0e38f8000010

def z1004 : W := mkw 0x5a844fc1ba27f139 0x44200fc0fe07f01f

def z1005 : W := mkw 0x32070a28a9858b18 0x0dff0e38f9878f0c

def z1006 : W := mkw 0x428000411a009131 0xffe01ffffe89f3f3

def z1007 : W := mkw 0x800eff3ee4000000 0x0fefff3ffe000000

def z1008 : W := mkw 0x00060a28a0000000 0x04af0e30f8000000

def z1009 : W := mkw 0xc42efffff6100480 0x8ffffffffe000c80

def z1010 : W := mkw 0xc4aefffff65814e1 0x2feffffffe7870e3

def z1011 : W := mkw 0x440ab07f12100480 0xfffff3ff3f704c93

def z1012 : W := mkw 0x442ebaffb2100ec0 0x891f12ff38000fe0

def z1013 : W := mkw 0x240bb03e01d80ec0 0xbbdff13f07f84fe3

def z1014 : W := mkw 0xb70165144dffcfde 0xfef0ed34c7ffcfff

def z1015 : W := mkw 0xc0066f7df6000000 0x0feffffffe000000

def z1016 : W := mkw 0x200bb03e01c80a40 0x3bcff03f01f80360

def z1017 : W := mkw 0xcd2efffff67a6486 0xffffffffff7e7c9f

def z1018 : W := mkw 0xb90ddf8045ef6006 0xffefffc4c7fff09f

def z1019 : W := mkw 0xc02efffff6000000 0x0eefed3ffe000000

def z1020 : W := mkw 0x240b902a01d80ec0 0xb3dff00b01f80fe0

def z1021 : W := mkw 0x3601000009958f98 0xf010000001f78f9c

def z1022 : W := mkw 0x3809d58001ef6000 0x73cff1c001fff000

def z1023 : W := mkw 0x402e9aebb2000000 0x010f12cb38880360

def z1024 : W := mkw 0xc02efffff6000000 0xffffffffff064c9f

def z1025 : W := mkw 0x32070a28a9858b18 0xdfff1ff8f9878f1c

def z1026 : W := mkw 0x00020028a0000000 0x88300038f8000c1c

def z1027 : W := mkw 0xc02ebafff6000000 0x010f12cf3e000000

def z1028 : W := mkw 0xc02efffff6000000 0x2feffffffe087000

def z1029 : W := mkw 0x240bb03e01d80ec0 0xb19ff03b01f80fe0

def z1030 : W := mkw 0x240fba3ea1d80ec0 0xfffffe3ff9fe0ffc

def z1031 : W := mkw 0xc0aefffff6001021 0xffeffffffe0870f3

def z1032 : W := mkw 0x240bb03e01d80ec0 0x239ff03f01f80fe0

def z1033 : W := mkw 0xc52efffff6324486 0x6feffffffe76409f

def z1034 : W := mkw 0x85006516443244c6 0xfef0ed37c7764cff

def z1035 : W := mkw 0xa50bb03e45d80ec6 0xbbdff03fc1f80fec

def z1036 : W := mkw 0x380ddf8001ef6000 0x77efffc0c1fff01c

def z1037 : W := mkw 0x4682207f1a109ff1 0x8810003f38000fe0

def z1038 : W := mkw 0x8500651444324486 0xfff0ef34c7f7cc9f

def z1039 : W := mkw 0xc0264fe9f6000000 0x0fef1ffffe000000

def z1040 : W := mkw 0x240bb03e01d80ec0 0xbffffc3fc1f80fe0

def z1041 : W := mkw 0xc5aefffff63254a7 0xffffffffff7e7cff

def z1042 : W := mkw 0x340bb03e01dd0ec8 0xbbdff03f01fe0fec

def z1043 : W := mkw 0x3601000009958fd8 0xd010000001878ffc

def z1044 : W := mkw 0x3603203e09958fd8 0xd810003f01878ffc

def z1045 : W := mkw 0x32070a28a9858b18 0xffff0e3cf9878f9c

def z1046 : W := mkw 0x7801004113ef6000 0x7f6013cf3ffff000

def z1047 : W := mkw 0x000e9a28a0000000 0x0feffe38f8000000

def z1048 : W := mkw 0xc02efffff6000000 0x008feef0f8000000

def z1049 : W := mkw 0xc52efffff67a44c6 0xffffffffff7e4cff

def z1050 : W := mkw 0x240bb03e01d80ec0 0xaa9ff03f01780fe0

def z1051 : W := mkw 0x240bb03ea1d80ec8 0xbbdff03fc1f80fec

def z1052 : W := mkw 0x240bb03e01d80ec0 0xffdff23f01f98fe0

def z1053 : W := mkw 0x380d9a8001cd2000 0x230ff2c000f9b000

def z1054 : W := mkw 0x402e9aebb2000000 0x000f02c038000000

def z1055 : W := mkw 0x380ddf8001ef6000 0x55cffec001ffb000

def z1056 : W := mkw 0xc02efffff6000000 0x4feffffffe01f000

def z1057 : W := mkw 0xe4254fc1f7d80ec0 0xb4300fc0fff80fe0

def z1058 : W := mkw 0x728100411b859b39 0xf21011c7078fffff

def z1059 : W := mkw 0x4002006912000000 0x0fef13ff3e000000

def z1060 : W := mkw 0x40260ae9b2000000 0x010f02c838000000

def z1061 : W := mkw 0x3201000009858b18 0xfb50100f018f8ffc

def z1062 : W := mkw 0xc02ebafff6000000 0x010f12fbf8000000

def z1063 : W := mkw 0x380ddf8001ef6000 0x7fcfffcf01fff000

def z1064 : W := mkw 0x000e9a2aa0000000 0x010f120b38000000

def z1065 : W := mkw 0x32070a28a9858b18 0x99ff0c38f9860f1c

def z1066 : W := mkw 0xb30145004da7cb1e 0xd4300d00c787cf1f

def z1067 : W := mkw 0x00060a28a0000000 0x08af0c38f8000000

def z1068 : W := mkw 0x00060a28a0000000 0x0fef1e3ff8000000

def z1069 : W := mkw 0x32870a28a9859b39 0xffff1e3ff98fffff

def z1070 : W := mkw 0x32070a28a9858b18 0x4dff0e38f9078c1c

def z1071 : W := mkw 0x240bb03e01d80ec0 0xffdff13f01f84fe0

def z1072 : W := mkw 0x00060a28a0000000 0x5def0e38f8818000

def z1073 : W := mkw 0x2281000009c89b71 0x000000000089b360

def z1074 : W := mkw 0x32070a28a9858b18 0x89bf0e38f9878f1c

def z1075 : W := mkw 0x002e9aaaa0000000 0x0def0e38f8000000

def z1076 : W := mkw 0xc02efffff6000000 0x0b2ff3fffe000000

def z1077 : W := mkw 0xc82efffff66a6000 0x0feffffffe700000

def z1078 : W := mkw 0x80264fa8e4000000 0x0def0e38f8000000

def z1079 : W := mkw 0x04062a3ca0100480 0xbfffee3cf9700c80

def z1080 : W := mkw 0xc02efffff6000000 0x4feffffffe004013

def z1081 : W := mkw 0xc52efffff6324486 0x88bfec3fff760c9f

def z1082 : W := mkw 0x380ddf8001ef6000 0x718ffec001fff000

def z1083 : W := mkw 0x32070a28a9858b18 0xddff1e3bf98f8f7c

def z1084 : W := mkw 0x40ae9aebb2001021 0x230f13cf3e0870e3

def z1085 : W := mkw 0x040ab03e005804c0 0xbbcff03f00f803e0

def z1086 : W := mkw 0x240bb03e01d80ec0 0xb31ff00f01f80fe0

def z1087 : W := mkw 0xc52efffff6324486 0x8fffffffff760c9f

def z1088 : W := mkw 0x380ddf8001ef6000 0x7feffff0c1fff000

def z1089 : W := mkw 0x8500651444324486 0xfff0ffffc7ffffff

def z1090 : W := mkw 0xc02efffff6000000 0x010ff2cb38000000

def z1091 : W := mkw 0x852effbee4324486 0xddffee38f9760c1c

def z1092 : W := mkw 0x380ddf8001ef6000 0x33cff3c001f9f000

def z1093 : W := mkw 0x028ab03e08009131 0xfbcff03f0089f3f3

def z1094 : W := mkw 0x240bb03e01d80ec0 0x33cff00f01f803e0

def z1095 : W := mkw 0x488cdfc1126a7021 0x2fefffcf3e7870e3

def z1096 : W := mkw 0xc52efffff6324486 0x4fffffffff764c1f

def z1097 : W := mkw 0x240bb03e01d80ec0 0xbbfff03fc1f80ffc

def z1098 : W := mkw 0x000edfa8a0000000 0x07cfffc838000000

def z1099 : W := mkw 0x3201000009858b18 0xf01000000187cf9f

def z1100 : W := mkw 0x428000411a009131 0xfff013ff3f89fff3

def z1101 : W := mkw 0x8500651444324486 0x8ef0ed34c7760c9f

def z1102 : W := mkw 0xc02efffff6000000 0x4feffffffe06001c

def z1103 : W := mkw 0x380d9a8001ef6000 0x73cff2c001fff000

def z1104 : W := mkw 0xc52efffff6100486 0xdfffffffff060c9f

def z1105 : W := mkw 0xc022207ff6000000 0x09ef003ffe000000

def z1106 : W := mkw 0x402ebaffb2000000 0x030ff2cf38000000

def z1107 : W := mkw 0x482e9aebb2482000 0x010f12cb38083000

def z1108 : W := mkw 0x40060a69b2000000 0x0def1efbf8000000

def z1109 : W := mkw 0x3201000009858118 0x500000000187801c

def z1110 : W := mkw 0x380ddf8001ef6000 0xf7cfffc001fff093

def z1111 : W := mkw 0x00060a28a0000000 0xbfef1e3ff88803e0

def z1112 : W := mkw 0x32070a28a9858b18 0xffff0f38f987cf1c

def z1113 : W := mkw 0x240bb03e01d80ec0 0xfbdff03f01f9ffe0

def z1114 : W := mkw 0x00064f28a0000000 0x0fefef38f8000000

def z1115 : W := mkw 0x240bb03e01d80ec0 0xfffff3ff07f9fff3

def z1116 : W := mkw 0x8500651444324486 0xfff0fd34c7fe4c9f

def z1117 : W := mkw 0x428000411a009131 0xffe0f3cf3ff9f3f3

def z1118 : W := mkw 0x802effbee4000000 0x0feffff8f8000000

def z1119 : W := mkw 0x3201000009858b18 0xd950000801878f1c

def z1120 : W := mkw 0x240bb03e01d80ec0 0x0bdff03f01f80f60

def z1121 : W := mkw 0x402e9aebb2000000 0x0d6f12cb38000000

def z1122 : W := mkw 0x428000411a009131 0xcd2013cf3e89f3f3

def z1123 : W := mkw 0x00060a28a0000000 0x052f0e08f8000000

def z1124 : W := mkw 0x402ebaffb2000000 0x018ff2fb38000000

def z1125 : W := mkw 0x32070a28a9858b18 0xfdff0e38f98fff1c

def z1126 : W := mkw 0xc02ab07ff6000000 0x092f103ffe000000

def z1127 : W := mkw 0x2403203c01900e80 0xbbdff03f01f80fe0

def z1128 : W := mkw 0x2409b01401d80480 0xbbdff03f01f80fe0

def z1129 : W := mkw 0x380ddf8001ef6000 0xffcfffc801fff300

def z1130 : W := mkw 0x00060a28a0000000 0x0fef1ff8f8000000

def z1131 : W := mkw 0x3201000009858b18 0xf0100000018f8ffc

def z1132 : W := mkw 0x6689b0571bd89ff1 0xf210f1c707f9fff3

def z1133 : W := mkw 0x32870a28a9859b39 0xddff0e38f987ff1f

def z1134 : W := mkw 0xc52efffff6100486 0xbfffffffff700c9f

def z1135 : W := mkw 0x3a01000009efe118 0x7000000001fff01c

def z1136 : W := mkw 0xc02efffff6000000 0x0defeff8fe000000

def z1137 : W := mkw 0x402e9aebb2000000 0x092f12cf3e000000

def z1138 : W := mkw 0x32070a28a9858b18 0xddff1ef8f98fbf1c

def z1139 : W := mkw 0x380ddf8001ef6000 0x47cfffc00177f000

def z1140 : W := mkw 0xb70165144db7cf9e 0xf210e10407f7cf9f

def z1141 : W := mkw 0x402effffb2000000 0x0fcfffff38000000

def z1142 : W := mkw 0x32070a28a9858b18 0x45bf0e38f9878f1c

def z1143 : W := mkw 0x8500651444324486 0xfef0ed34c7fe4fff

def z1144 : W := mkw 0x380ddf8001ef6000 0x77dffff0c1fffc0c

def z1145 : W := mkw 0x402edfebb2224000 0x77cfffcb39764000

def z1146 : W := mkw 0x3e81000009fffff1 0xf010000001fffff3

def z1147 : W := mkw 0xc00af57f56000000 0x0feffffffe000000

def z1148 : W := mkw 0x3809d58001ef6000 0x2200f1c000f9f000

def z1149 : W := mkw 0x380ddf8001ef6000 0x008feec00177b000

def z1150 : W := mkw 0xc02efffff6000000 0x06affff7fe000000

def z1151 : W := mkw 0x000cdf80a0000000 0x07efffc0f8000000

def z1152 : W := mkw 0x402e9aebb2000a40 0x010f12cb38000360

def z1153 : W := mkw 0x390ddf8001ef6006 0x77cfffc001fff01f

def z1154 : W := mkw 0x402e9aebb2000000 0x0b4f12cf38000000

def z1155 : W := mkw 0x32070a28a9858b18 0xdfff0f3cff878f1c

def z1156 : W := mkw 0xc42efffff6100ec0 0x0ffffffffe000c00

def z1157 : W := mkw 0x402edfebb2000000 0x050f1fcb38000000

def z1158 : W := mkw 0x3a09d58009efeb18 0xf210f1c001ffff1c

def z1159 : W := mkw 0x3a81000009cdb131 0xf00000000089f3f3

def z1160 : W := mkw 0xc52ab07ff6100486 0xbbfff03fff700c9f

def z1161 : W := mkw 0x380ddf8001ef6000 0x77cfffcb01fff360

def z1162 : W := mkw 0x380ddf8001ef6000 0x77efffc007fff013

def z1163 : W := mkw 0xc50cffd556324486 0xffffffffff764c9f

def z1164 : W := mkw 0x402ab07fb2000000 0x0bcff03f38000000

def z1165 : W := mkw 0xc0aefffff6001021 0x0feffffffe007003

def z1166 : W := mkw 0x400effff12000000 0x0fefffff3e000000

def z1167 : W := mkw 0x582e9aebb2052000 0x010f12cb3801b000

def z1168 : W := mkw 0x05060a28a0324486 0xfdff0e38f9764c9f

def z1169 : W := mkw 0x32050a0009858110 0xddff0e38f9878f1c

def z1170 : W := mkw 0x3c0bb03e01dd2ec0 0xbbdff03f01f9bfe0

def z1171 : W := mkw 0x380ddf8001cd2000 0x37cfffc001f9b000

def z1172 : W := mkw 0x400ab07f12000000 0x0bcff2ff38000000

def z1173 : W := mkw 0xc02efffff6000000 0xffeffffffe89f3e0

def z1174 : W := mkw 0x2601000009d88fd0 0xf010000001f98ff0

def z1175 : W := mkw 0x04062a3ea0100ec0 0x8dff0e3ff8000fe0

def z1176 : W := mkw 0xc42efffff6100480 0xffffffffff760c9c

def z1177 : W := mkw 0x380d9a8001cd2000 0x77cffec001ffb000

def z1178 : W := mkw 0x402a906bb2000000 0x010f100b38000000

def z1179 : W := mkw 0x8500651444324486 0x4ef0ed34c7764c1f

def z1180 : W := mkw 0x380ddf8001ef6a00 0xf7dfffc001ffff00

def z1181 : W := mkw 0x8500651444324486 0xfff0fd3fc7764c9f

def z1182 : W := mkw 0x18064fa8a0276000 0x4def0ff8f807f000

def z1183 : W := mkw 0x3201000009858b18 0x8010000001060f1c

def z1184 : W := mkw 0xc02edfebf6000000 0x0def1ffbfe000000

def z1185 : W := mkw 0x240bb03e01d80ec0 0xbbdffc3fc1fe0fec

def z1186 : W := mkw 0x400ab07f12000000 0x0beff03f3e000000

def z1187 : W := mkw 0x30070a28a1850a08 0xddff0e38f9060c1c

def z1188 : W := mkw 0x8500651444324486 0x76f0ed30c7764c1f

def z1189 : W := mkw 0x0002002800000000 0x0def023838000000

def z1190 : W := mkw 0x3f81000009fff5b7 0xf010000001ffffff

def z1191 : W := mkw 0x400a906b12000000 0x010f12cb38000000

def z1192 : W := mkw 0x428000411a009131 0xf30013cf3e89f3f3

def z1193 : W := mkw 0x8500651444324486 0xfff0ef3cff764c9f

def z1194 : W := mkw 0xc02efffff6000000 0x0aaffdfffe000000

def z1195 : W := mkw 0x428000411a009131 0x672013cf3e89f3f3

def z1196 : W := mkw 0xc02edfe9f6000000 0x0feffff8fe000000

def z1197 : W := mkw 0xc02edfebf6000000 0x0f6f1fcffe000000

def z1198 : W := mkw 0xc52efffff6100486 0xfffffffffe004c9f

def z1199 : W := mkw 0x00064fa8a0000000 0x0def0ff8f8000000

def z1200 : W := mkw 0x00020028a0000000 0x09ef0038f8000000

def z1201 : W := mkw 0x00060a28a0000000 0x0fef0f3cfe000000

def z1202 : W := mkw 0x32070a28a9858b18 0x99df0e38f9878f0c

def z1203 : W := mkw 0xc02efffff6000000 0xffeffffffe8843f3

def z1204 : W := mkw 0x85062a3ce4100486 0x8dff0e3cfe000c9f

def z1205 : W := mkw 0xc02efffff6224000 0xffefffffff764093

def z1206 : W := mkw 0x3a81000009cdb131 0x000000000089b360

def z1207 : W := mkw 0x40040a4112000000 0x0fef1fcf3e000000

def z1208 : W := mkw 0xb80ddf8045ef6000 0x77efffc0c7fff000

def z1209 : W := mkw 0xc42efffff6580ec0 0xaffffffffe780fe0

def z1210 : W := mkw 0x400cdfc112224000 0xffefffcf3f764093

def z1211 : W := mkw 0x00060a28a0000000 0x9def0e38f8800300

def z1212 : W := mkw 0x080edfa8a06a6000 0x2feffff8f8787000

def z1213 : W := mkw 0x240bb03e01d80ec0 0x99dff03b01f80f60

def z1214 : W := mkw 0x30070a28a1850a08 0x08bf0c38f9060c0c

def z1215 : W := mkw 0xcd2efffff67a6486 0x2feffffffe787083

def z1216 : W := mkw 0x402e9aebb2000000 0x09cf12fb38000000

def z1217 : W := mkw 0x32070a28a9858b18 0xddff0e3ff9878ffc

def z1218 : W := mkw 0x3281000009859131 0xf0000000018ff3f3

def z1219 : W := mkw 0x402c9ac1b2000000 0x010f12c038000000

def z1220 : W := mkw 0xc02efffff6000000 0x2feffffffe004083

def z1221 : W := mkw 0x3201000009858b18 0xdc70000001878f1c

def z1222 : W := mkw 0x000edfa8a0000000 0x0defee38f8000000

def z1223 : W := mkw 0x402edfebb2000000 0x018ffecb38000000

def z1224 : W := mkw 0xc02efffff6000a40 0x0feffffffe000360

def z1225 : W := mkw 0xc02efffff6000000 0x008fec3bf8000000

def z1226 : W := mkw 0x00064f28a0224000 0x7fefef38f9764000

def z1227 : W := mkw 0x00060a28a0000000 0x0d6f020838000000

def z1228 : W := mkw 0x8500651444324486 0xccb0ed34c7764c9f

def z1229 : W := mkw 0xc528f5d756324486 0x0200f1c706700000

def z1230 : W := mkw 0xc02efffff6000000 0x5fefffffff060000

def z1231 : W := mkw 0xc0264fe9f6000000 0x04af0ff0fe000000

def z1232 : W := mkw 0xc52efffff6324486 0xfffffffffffffc9f

def z1233 : W := mkw 0x00060a28a0000000 0x4def0e38f806001c

def z1234 : W := mkw 0xc5aefffff63254a7 0x2feffffffe7870e3

def z1235 : W := mkw 0x3201000009cd8b58 0x0000000000898360

def z1236 : W := mkw 0xc02cffd756000000 0x0fefffcf3e000000

def z1237 : W := mkw 0x40260a6bb2000000 0x010f020b38000000

def z1238 : W := mkw 0x3a01000009efe110 0xf000000001fff310

def z1239 : W := mkw 0xc02efffff6000000 0x8feffffffe000093

def z1240 : W := mkw 0xd92efffff6276006 0x4feffffffe07f01f

def z1241 : W := mkw 0x8500651444324486 0xf4b0ed30c7764c9f

def z1242 : W := mkw 0xc12efffff6224006 0xffeffffffe06409f

def z1243 : W := mkw 0x40ae9aebb2001021 0x010f12cb38083060

def z1244 : W := mkw 0x000e9aa8a0000000 0x0def1ef8f8000000

def z1245 : W := mkw 0x000eba3ea0000000 0x0defee38f8000000

def z1246 : W := mkw 0xc02cffd7f6000000 0x07efffc7fe000000

def z1247 : W := mkw 0x20070a28a1800a00 0xddff0e38f9860f1c

def z1248 : W := mkw 0x30070a28a1850000 0xddff0e38f9878c1c

def z1249 : W := mkw 0x3781000009b7dfbf 0xf010000001ffffff

def z1250 : W := mkw 0xc02efffff6000a08 0x0ffffffffe000c0c

def z1251 : W := mkw 0xc82efffff66a6000 0x7fefffffff7e7000

def z1252 : W := mkw 0x32070a28a9858b18 0xd19f0e38f9878f1c

def z1253 : W := mkw 0xe423207ff7d80ec0 0xb830003ffff80fe0

def z1254 : W := mkw 0x00040a0000000000 0x0def0e0838000000

def z1255 : W := mkw 0x8500651444324486 0xfff0fff4c7764c9f

def z1256 : W := mkw 0x12060a28a8058b18 0xcdff0e38f8078f1c

def z1257 : W := mkw 0xc02efffff6000000 0x0beffc3ffe000000

def z1258 : W := mkw 0x2201000009808b18 0x9010000001800f1c

def z1259 : W := mkw 0xc52efffff6324486 0x7fefffffff764083

def z1260 : W := mkw 0xdaa44fc1fe27f131 0x44200fc0fe07f013

def z1261 : W := mkw 0x802effbee4000000 0x0feffe3ff8000000

def z1262 : W := mkw 0x402ebaffb2000000 0x0feffefff8000000

def z1263 : W := mkw 0xc02efffff6000000 0x3fefffffff700000

def z1264 : W := mkw 0x00062a3ea0000000 0x0def0e3ff8000000

def z1265 : W := mkw 0xc42efffff6100480 0xffffffffff704c93

def z1266 : W := mkw 0xc02efffff6480000 0x2feffffffe780000

def z1267 : W := mkw 0x80066f3ce4000000 0x0defee38f8000000

def z1268 : W := mkw 0xb90ddf8045ef6006 0x77cfffc007fff003

def z1269 : W := mkw 0xc12cdfc1f6224006 0x77efffc0ff76401f

def z1270 : W := mkw 0x32070a28a9858b18 0x55df0e38f9878f0c

def z1271 : W := mkw 0xa40bb03e45d80ec0 0xbbfff03fc7f80fe0

def z1272 : W := mkw 0x380ddf8001ef6000 0xffefffc001fff010

def z1273 : W := mkw 0x00060a28a0000000 0x7fef1ff8f889f000

def z1274 : W := mkw 0x32070a28a9858b18 0xffff1ffff98ffffc

def z1275 : W := mkw 0x402ebaffb2000000 0x0feff3ff3e000000

def z1276 : W := mkw 0xc42efffff6100ec0 0xbffffffffe880fe0

def z1277 : W := mkw 0x380ddf8001ef6000 0x774ff3c000f9f000

def z1278 : W := mkw 0x402e9aebb2000000 0x052f1ecbf8000000

def z1279 : W := mkw 0x380ddf8001ef6000 0x33cffec001ffb000

def z1280 : W := mkw 0x30070a28a1850a08 0x9dff0e38f9860f0c

def z1281 : W := mkw 0xa50bb03e45d80ec6 0xfffffc3fc7fe0fff

def z1282 : W := mkw 0xc52af57ff6324486 0xfffffd3fff764c9f

def z1283 : W := mkw 0xc82efffff6482000 0x0feffffffe083000

def z1284 : W := mkw 0xc52cffd5f6324486 0xfffffff4ff764c9f

def z1285 : W := mkw 0x3f01000009ffef9e 0xf010000001ffff9f

def z1286 : W := mkw 0xc0aefffff6001021 0xbfeffffffe8873e3

def z1287 : W := mkw 0x402edfebb2000000 0x030ff3cb38000000

def z1288 : W := mkw 0xc82efffff66a6000 0x7feffffffef9f000

def z1289 : W := mkw 0x3201000009858b18 0xd8d0003001878f1c

def z1290 : W := mkw 0x380ddf8001ef6000 0x55cfefc001f7f000

def z1291 : W := mkw 0x32070a2aa9858b58 0xddff0e3bf9878f7c

def z1292 : W := mkw 0x428000411a009131 0x774013cf3e89f3e3

def z1293 : W := mkw 0xa78165144dfadff7 0xfef0ed34c7ffffff

def z1294 : W := mkw 0x402e9aebb2000000 0x05cf1ecb38000000

def z1295 : W := mkw 0x380ddf8001ef6000 0x77cfffc407fff083

def z1296 : W := mkw 0xc52efffff6324486 0x44bfeff0ff764c1f

def z1297 : W := mkw 0x402e9aebb2000000 0x052f13cb3e000000

def z1298 : W := mkw 0x00060a28a0000000 0x9dff0e38f9000c00

def z1299 : W := mkw 0x40060a69b2000000 0xffff1fffff064c9f

def z1300 : W := mkw 0xc5262a7ff6100486 0xddff0e3fff060c9f

def z1301 : W := mkw 0xc52ebafff6100486 0x893f12fffe000c9f

def z1302 : W := mkw 0xc52efffff6100486 0x0feffffffe000083

def z1303 : W := mkw 0x3281000009859b39 0xf00000000089f3f3

def z1304 : W := mkw 0x3a01000009cdab18 0x000000000089b300

def z1305 : W := mkw 0xc02efffff6000000 0x0fffffffff060c0c

def z1306 : W := mkw 0xb70120144d958f9e 0xd8300034c7878f9f

def z1307 : W := mkw 0xc0aefffff6001021 0x0feffffffe083060

def z1308 : W := mkw 0xc12efffff6224006 0xdfffffffff064c1f

def z1309 : W := mkw 0x402e9aebb2000000 0x092f12fbf8000000

def z1310 : W := mkw 0xc42efffff6100ec0 0xbfffffffff700fe0

def z1311 : W := mkw 0x32070a28a9cd8b18 0xfdff0e38f9ff8f1c

def z1312 : W := mkw 0x3e01000009ffefd8 0xf010000001fffffc

def z1313 : W := mkw 0x380ddf8201ef6040 0x77cfffc301fff060

def z1314 : W := mkw 0x3281000009859b39 0xd010000001878fff

def z1315 : W := mkw 0x3701000009ffcfde 0xf010000001ffcfff

def z1316 : W := mkw 0xc02efffff6480040 0x0feffffffe080060

def z1317 : W := mkw 0xdb844fc15e27f137 0x44200fc0fe07f01f

def z1318 : W := mkw 0x2409b01601d80ec0 0x2200f00700f803e0

def z1319 : W := mkw 0x8500651444324486 0xfef0ed3fc7764fff

def z1320 : W := mkw 0x8500651444324486 0xaab0ed34c7764c9f

def z1321 : W := mkw 0x000edfa8a0224000 0xfffffff8f9764c1c

def z1322 : W := mkw 0x00060a28a0000a08 0x0dff0e38f8000c0c

def z1323 : W := mkw 0x32050a0009858b18 0xd4100e0001878f1c

def z1324 : W := mkw 0x380ddf8001ef6000 0x458fffc001fff000

def z1325 : W := mkw 0xc6a2207ffe109ff1 0x8830003ffe000ff3

def z1326 : W := mkw 0x200ddf8001c80000 0x77cfffc001f9f000

def z1327 : W := mkw 0xd82efffff6276000 0x0feffffffe060000

def z1328 : W := mkw 0xdd2efffff6376486 0xffffffffff77fc9f

def z1329 : W := mkw 0x200b902a01c80a40 0xbbcff00f01f803e0

def z1330 : W := mkw 0x000e9a2aa0000000 0x0def1e3bf8000000

def z1331 : W := mkw 0x802effbee4000000 0x04afee30f8000000

def z1332 : W := mkw 0x40260ae9b2000000 0x0def0ef8f8000000

def z1333 : W := mkw 0x380ddf8001ef6000 0x27cfffc000f9f000

def z1334 : W := mkw 0x402e9aebb2000000 0x000f000b38000000

def z1335 : W := mkw 0xc0244fc1f6000000 0x05ef0fc0fe000000

def z1336 : W := mkw 0xc02e9aebf6000000 0x012f12cbfe000000

def z1337 : W := mkw 0x402e9aebb2000000 0xff6f13cf3e004093

def z1338 : W := mkw 0x2c0bb0be01d82ec0 0xbbdff0ff01f83fe0

def z1339 : W := mkw 0xc00cffd556000000 0x0feffffffe000000

def z1340 : W := mkw 0xc52efffff6324486 0x2fffffffff764c8f

def z1341 : W := mkw 0xc42efffff65804c0 0x0feffffffe700000

def z1342 : W := mkw 0x32070a28a9858b18 0xddff0ff8f987ff1c

def z1343 : W := mkw 0xc52efffff6324486 0xfeffeff4ff764c9f

def z1344 : W := mkw 0xa50bb03e45d80ec6 0xbbdff03f07f80fe3

def z1345 : W := mkw 0x428000411a009131 0xff601fcffe8ff3ff

def z1346 : W := mkw 0xc02efffff6000000 0x3feffffffe880000

def z1347 : W := mkw 0x3601000009dd8fd8 0xb010000001f98fe0

def z1348 : W := mkw 0x3601201409958f98 0xfad0e03401f78f9c

def z1349 : W := mkw 0x2281000009809b31 0xf01000000189fff3

def z1350 : W := mkw 0x3201000009cd8b58 0xd0100000018f8f7c

def z1351 : W := mkw 0x240bb03e01d80ec0 0xbbfff03f07f80ff3

def z1352 : W := mkw 0xc52efffff67a44c6 0x2feffffffe7840e3

def z1353 : W := mkw 0x80062a3ce4000000 0x0def0e3cfe000000

def z1354 : W := mkw 0x3201000009858110 0xd000000001878310

def z1355 : W := mkw 0x802effbee4000000 0x018fee38f8000000

def z1356 : W := mkw 0xc02cdfc1f6000000 0x052f1fc0fe000000

def z1357 : W := mkw 0x400a906b12000000 0x0f6f13cf3e000000

def z1358 : W := mkw 0x380ddf8001ef6a08 0x77dfffc001fffc0c

def z1359 : W := mkw 0x8500651444324486 0xfff0ed3cc7f64f9f

def z1360 : W := mkw 0x3201000009858b18 0x400000000087831c

def z1361 : W := mkw 0x81064f28e4224006 0x4def0f38fe06401f

def z1362 : W := mkw 0xc02efffff6000000 0x07cfffcf3e000000

def z1363 : W := mkw 0xc02ebafff6000000 0x082f003ffe000000

def z1364 : W := mkw 0x32070a28a9858b18 0xd4bf0e30f9878f1c

def z1365 : W := mkw 0xc02efffff6000000 0x2feffffffe0800e0

def z1366 : W := mkw 0x402e9aebb2000000 0x010f12cb3889b000

def z1367 : W := mkw 0x240bb03e01d80ec0 0xb29ff03701f80fe0

def z1368 : W := mkw 0x3201000009858b18 0x8010000000818f1c

def z1369 : W := mkw 0xc3a44fc1fe22d137 0x44200fc0fe07f01f

def z1370 : W := mkw 0x240bb03e01d80ec0 0x99dfe03f01f00fe0

def z1371 : W := mkw 0x0000000000000000 0xdd60020838000010

def z1372 : W := mkw 0xc782207f5e109ff7 0x8830003ffe000fff

def z1373 : W := mkw 0x402cdfc1b2000000 0x07cfffc038000000

def z1374 : W := mkw 0xc02efffff6000000 0x5feffffffe818000

def z1375 : W := mkw 0x8500651444324486 0xfef0ed34c7fffc9f

def z1376 : W := mkw 0xc52efffff6324486 0x230ff3cf3e704083

def z1377 : W := mkw 0x3201000009858b18 0xd000000000818310

def z1378 : W := mkw 0x2203002809808b10 0xddff0e38f9878f1c

def z1379 : W := mkw 0x200b902a01c80a40 0x018ff00b01f80360

def z1380 : W := mkw 0x6401004113d80ec0 0xbf7013cf3ff80fe0

def z1381 : W := mkw 0xc0262a7ff6000000 0x092f023ffe000000

def z1382 : W := mkw 0x240bb03e01d80ec0 0x33dff03b01f80f60

def z1383 : W := mkw 0x8500651444324486 0xdcf0ec34c7760c9f

def z1384 : W := mkw 0xc42efffff6100480 0x2feffffffe700080

def z1385 : W := mkw 0x2201000009808b10 0xd010000001818f10

def z1386 : W := mkw 0x402edfebb2000000 0x0fefffcf3e000000

def z1387 : W := mkw 0x32070a28a9858b18 0xdcff0e30f9078c1c

def z1388 : W := mkw 0x482edfebb26a6000 0x230ff3cb38787000

def z1389 : W := mkw 0xc52efffff6324486 0xffeffffffe704093

def z1390 : W := mkw 0x00060a28a0000000 0x009f0c30c1060c0c

def z1391 : W := mkw 0x32070a28a9858b18 0xdfff1e3ff9878f1c

def z1392 : W := mkw 0x380ddf8001ef6000 0xffdffff001fffc00

def z1393 : W := mkw 0xc1264fe9f6224006 0xddff0ff8ff064c1f

def z1394 : W := mkw 0xc02efffff6224000 0xffffffffff764c1c

def z1395 : W := mkw 0x00060a28a0000000 0x09cf023838000000

def z1396 : W := mkw 0xc0262a7ff6000000 0x08af0c3ffe000000

def z1397 : W := mkw 0x628990411bc89131 0x77eff3c03ff9f013

def z1398 : W := mkw 0xc0260a69f6000000 0x0def0e38fe000000

def z1399 : W := mkw 0xc02edfebf6000000 0x042f0fc0fe000000

def z1400 : W := mkw 0x428000411a009131 0xab2013cf3e89f3f3

def z1401 : W := mkw 0x2681000009d89ff1 0xb010000001f9bfe0

def z1402 : W := mkw 0x380ddf8001ef6000 0xffcfffc401fff080

def z1403 : W := mkw 0x000ab03e00000000 0x0feff23f38000000

def z1404 : W := mkw 0x300d9a0001cd0000 0x77cfffc001fff000

def z1405 : W := mkw 0xc12edfebf6224006 0x452f1fcbfe06401f

def z1406 : W := mkw 0x32070a28a9858b18 0x00bf0c30f9060c1c

def z1407 : W := mkw 0x240bb03e01d80ec0 0xfffff03f01f80ff0

def z1408 : W := mkw 0xc52efffff6324486 0x019ffefbf9760c0c

def z1409 : W := mkw 0x3201000009858b18 0xd4300c00c1878f1c

def z1410 : W := mkw 0xc02eba7ff6000000 0x0feffe3ffe000000

def z1411 : W := mkw 0xbf8165144dfff5b7 0xfef0ed34c7ffffff

def z1412 : W := mkw 0x32870a28a9859b39 0xddff0e38f9878fff

def z1413 : W := mkw 0x2681201409d89ff1 0xfef0e13407f9fff3

def z1414 : W := mkw 0xc52efffff6324486 0xcffffffffe064c9f

def z1415 : W := mkw 0x402e9aebb2000000 0x03cff2cb38000000

def z1416 : W := mkw 0x32070a28a9858b18 0xffffee38f9f78f1c

def z1417 : W := mkw 0xc02efffff6000000 0x8ffffffffe000c1c

def z1418 : W := mkw 0x802effbee4000000 0x0fefef3cfe000000

def z1419 : W := mkw 0xc02efffff6000000 0x0cafeffffe000000

def z1420 : W := mkw 0x2601000009d88fd8 0xb010000001f80ffc

def z1421 : W := mkw 0x2403203e01900ec0 0xbbdfe03f01f00fe0

def z1422 : W := mkw 0x200b902a01c80a40 0x230ff00b00f80360

def z1423 : W := mkw 0x380ddf8001ef6000 0x668fffc0017ff000

def z1424 : W := mkw 0x3681000009dd9ff9 0xf010000001ffffff

def z1425 : W := mkw 0x32070a28a9858b18 0xdcff0c38f9060f1c

def z1426 : W := mkw 0xc02efffff6000000 0x7feffffffe004000

def z1427 : W := mkw 0x380ddf8001ef6000 0x77cfffc701fff0e0

def z1428 : W := mkw 0x32070a28a9858b18 0xcd3f0e38f8878f1c

def z1429 : W := mkw 0x040eba3ea05804c0 0x2feffe3ff87800e0

def z1430 : W := mkw 0xd02efffff6050000 0x4feffffffe078000

def z1431 : W := mkw 0x32070a28a9858b18 0xccbf0e38f9078f1c

def z1432 : W := mkw 0xcc2efffff67a64c0 0x2feffffffe7870e0

def z1433 : W := mkw 0xc42efffff6100480 0x0fffffffff700c00

def z1434 : W := mkw 0x3a81000009effb39 0xf010000001ffffff

def z1435 : W := mkw 0xc02ebafff6000000 0x0def1efffe000000

def z1436 : W := mkw 0x380ddf8001ef6000 0x238fffc001fff000

def z1437 : W := mkw 0x400c9ac112000000 0x010f12cb38000000

def z1438 : W := mkw 0xc02efffff6000000 0xffeffffffe89f093

def z1439 : W := mkw 0xc52efffff6324486 0x7fffffffff764c0c

def z1440 : W := mkw 0x3a01450009efeb18 0xfef0ed30c1ffff1c

def z1441 : W := mkw 0x802effbee4000000 0x08afec38f8000000

def z1442 : W := mkw 0x3809900001ef6000 0x77cff3c001fff000

def z1443 : W := mkw 0xc02af57ff6000000 0x0feffd3ffe000000

def z1444 : W := mkw 0xc02cffd5f6000000 0x0feffff4fe000000

def z1445 : W := mkw 0xc52efffff6324486 0xaffffffffe704c9f

def z1446 : W := mkw 0x402edfebb2000000 0x0feffffbf8000000

def z1447 : W := mkw 0x240bb03e01d80ec0 0xb89fe03f01f80fe0

def z1448 : W := mkw 0xc02efffff6000000 0xdfeffffffe000010

def z1449 : W := mkw 0x442ebaffb25804c0 0x230ff2cf387800e0

def z1450 : W := mkw 0xc02ab07ff6000000 0x08afe03ffe000000

def z1451 : W := mkw 0xd82efffff66f6000 0x6feffffffe7ff000

def z1452 : W := mkw 0xc02efffff6000000 0x00afec30fe000000

def z1453 : W := mkw 0x380ddf8001ef6000 0x7fefffc407fff000

def z1454 : W := mkw 0xb90ddf8045ef6006 0xfffffff0c7fffc1f

def z1455 : W := mkw 0x8500651444324486 0xbaf0ec34c7760c9f

def z1456 : W := mkw 0xc52efffff6324486 0xdfffffffff760c1c

def z1457 : W := mkw 0x00060a28a0000a00 0x8dff0e38f8000f00

def z1458 : W := mkw 0xc02efffff6000a00 0x8ffffffffe000f00

def z1459 : W := mkw 0x402e9aebb2000000 0x030f13cf3e000000

def z1460 : W := mkw 0xa50bb03e45d80ec6 0xfffff13fc7f84fff

def z1461 : W := mkw 0x32070a28a9858b18 0xfdff0e38f987cf9f

def z1462 : W := mkw 0x18044f8000276000 0xff401fcf008ff3e0

def z1463 : W := mkw 0xc52efffff6100486 0x0ffffffffe000c0c

def z1464 : W := mkw 0x402e9aebb2000000 0x018f1efbf8000000

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkA : List (List (List (ℕ × List W))) :=
  [[[(1,[z0,z1,z2,z3,z4,z5])],[(0,[z6,z0,z1,z2,z7,z3,z5]),(0,[z8,z9,z0,z1,z3,z5,z10]),(0,[z11,z0,z1,z2,z3,z5,z10]),(0,[z12,z13,z0,z1,z2,z3,z5]),(0,[z0,z1,z2,z3,z14,z5,z15]),(1,[z0,z16,z2,z3,z5,z10])],[(0,[z0,z1,z2,z3,z17,z5,z10]),(0,[z18,z0,z1,z2,z3,z5,z19])],[(0,[z0,z1,z2,z20,z21,z5,z10]),(0,[z0,z1,z2,z3,z5,z22,z10]),(0,[z0,z1,z23,z2,z3,z5,z10])],[(0,[z24,z0,z1,z2,z3,z5,z10])],[(0,[z0,z1,z2,z3,z25,z5,z10]),(0,[z8,z0,z1,z2,z3,z5,z19]),(0,[z26,z0,z1,z2,z27,z5,z10]),(0,[z28,z0,z1,z2,z3,z5,z10]),(0,[z0,z29,z1,z2,z3,z5,z19]),(1,[z13,z0,z30,z2,z3,z5]),(0,[z0,z1,z2,z3,z31,z5,z10]),(0,[z0,z32,z1,z2,z3,z5,z10]),(0,[z0,z1,z2,z3,z5,z10,z33]),(0,[z0,z1,z2,z3,z5,z19,z34]),(0,[z0,z1,z2,z35,z3,z5,z19])],[(0,[z0,z1,z36,z2,z3,z5,z10]),(0,[z37,z0,z1,z2,z3,z38,z10]),(0,[z0,z1,z39,z2,z3,z5,z10]),(0,[z40,z0,z1,z2,z3,z5,z41])],[(0,[z0,z1,z2,z3,z5,z42,z19]),(0,[z43,z0,z1,z2,z3,z5,z10])]],
   [[(0,[z44,z0,z1,z2,z3,z5,z10]),(0,[z0,z1,z2,z3,z5,z10,z45])],[(0,[z13,z6,z0,z1,z2,z3,z5]),(0,[z0,z1,z2,z3,z46,z5,z10]),(0,[z18,z0,z1,z2,z3,z5,z47])],[(0,[z48,z0,z1,z2,z3,z5,z49]),(0,[z0,z1,z2,z3,z50,z5,z10]),(0,[z13,z51,z0,z1,z2,z3,z5]),(0,[z0,z2,z3,z52,z5,z42,z10]),(0,[z0,z1,z2,z3,z53,z5,z10])],[(0,[z8,z1,z2,z27,z3,z5,z10]),(0,[z0,z30,z1,z2,z27,z3,z5]),(0,[z0,z1,z54,z2,z3,z5,z10]),(0,[z0,z1,z2,z3,z55,z5,z10]),(0,[z56,z0,z1,z2,z3,z5,z10]),(0,[z0,z57,z1,z2,z3,z5,z10])],[(1,[z0,z1,z2,z3,z5,z58]),(0,[z0,z1,z2,z3,z5,z59,z10]),(0,[z0,z1,z2,z3,z5,z60,z10]),(0,[z0,z61,z2,z3,z52,z5,z10]),(0,[z62,z13,z0,z1,z2,z3,z5]),(1,[z0,z1,z2,z3,z5,z63]),(0,[z0,z1,z3,z53,z5,z38,z10]),(0,[z0,z1,z2,z3,z64,z10,z19])],[(0,[z9,z0,z1,z65,z3,z5,z10]),(0,[z48,z0,z1,z66,z3,z5,z10]),(0,[z0,z1,z2,z3,z5,z67,z10]),(0,[z13,z0,z1,z2,z27,z3,z5]),(0,[z0,z1,z2,z68,z3,z5,z10]),(0,[z69,z0,z1,z2,z3,z5,z19]),(0,[z13,z0,z29,z1,z2,z3,z5]),(0,[z0,z30,z1,z66,z2,z3,z5]),(1,[z0,z1,z70,z71,z5,z10]),(1,[z1,z2,z3,z5,z72,z10])],[(0,[z13,z73,z0,z1,z2,z3,z5]),(0,[z74,z0,z1,z2,z3,z5,z10]),(0,[z75,z0,z30,z1,z2,z3,z5])],[(0,[z0,z1,z2,z3,z5,z10,z76]),(0,[z77,z0,z1,z2,z3,z5,z10]),(0,[z78,z0,z1,z2,z3,z5,z10])]],
   [[(0,[z0,z79,z1,z2,z3,z5,z10]),(0,[z69,z0,z1,z3,z5,z38,z10]),(0,[z80,z0,z1,z2,z3,z5,z10])],[(0,[z0,z81,z1,z2,z3,z5,z10]),(0,[z0,z1,z2,z27,z3,z5,z19]),(0,[z82,z0,z1,z2,z3,z5,z10]),(0,[z83,z0,z1,z2,z84,z3,z5]),(0,[z0,z29,z2,z85,z3,z5,z10]),(0,[z86,z13,z0,z1,z2,z3,z5])],[(0,[z0,z1,z2,z7,z3,z87,z5]),(0,[z0,z88,z1,z2,z3,z5,z10]),(0,[z0,z30,z1,z2,z84,z3,z5]),(0,[z0,z1,z2,z3,z89,z5,z10]),(0,[z0,z1,z2,z3,z5,z10,z90]),(0,[z0,z1,z91,z2,z3,z5,z10])],[(0,[z92,z0,z1,z2,z7,z3,z5])],[(0,[z83,z0,z1,z2,z3,z5,z19]),(0,[z13,z0,z1,z2,z20,z3,z5]),(0,[z40,z93,z1,z2,z3,z5,z10]),(0,[z0,z1,z2,z7,z3,z94,z5])],[(0,[z95,z0,z1,z2,z3,z5,z96]),(0,[z0,z1,z2,z3,z5,z10,z97]),(0,[z0,z30,z1,z2,z3,z5,z19]),(1,[z0,z1,z2,z98,z3,z5]),(1,[z0,z1,z99,z3,z5,z10]),(0,[z0,z1,z2,z84,z3,z5,z19])],[(1,[z0,z1,z100,z2,z3,z5]),(0,[z0,z1,z2,z3,z101,z5,z10]),(0,[z102,z0,z1,z2,z3,z5,z10])],[(0,[z0,z1,z2,z3,z103,z5,z10]),(0,[z0,z1,z2,z3,z104,z38,z10]),(0,[z105,z0,z1,z2,z3,z5,z10]),(0,[z0,z1,z2,z106,z3,z5,z10])]],
   [[(0,[z9,z0,z1,z66,z3,z5,z10]),(0,[z0,z1,z2,z3,z107,z5,z10]),(0,[z48,z0,z1,z71,z3,z5,z10]),(0,[z0,z1,z2,z3,z5,z108,z10]),(0,[z109,z0,z1,z2,z3,z5,z10]),(0,[z13,z0,z1,z2,z3,z5,z110]),(0,[z0,z1,z2,z3,z5,z19,z110]),(0,[z111,z0,z1,z2,z3,z5,z10]),(0,[z0,z1,z2,z85,z3,z5,z112]),(0,[z113,z0,z1,z2,z7,z3,z10])],[(0,[z0,z1,z2,z3,z5,z114,z10]),(0,[z0,z1,z2,z3,z3,z5,z10]),(0,[z0,z30,z1,z2,z3,z115,z5]),(0,[z0,z1,z2,z3,z116,z5,z10]),(0,[z0,z1,z2,z117,z3,z5,z10]),(0,[z0,z1,z2,z7,z3,z5,z42]),(0,[z118,z0,z1,z2,z3,z5,z10]),(1,[z86,z0,z1,z53,z5,z10])],[(0,[z13,z119,z0,z1,z2,z3,z5]),(0,[z0,z1,z2,z120,z3,z5,z10]),(0,[z0,z121,z1,z2,z3,z5,z10]),(0,[z122,z0,z1,z2,z123,z5,z10])],[(0,[z0,z1,z2,z3,z5,z10,z124]),(0,[z125,z0,z1,z2,z3,z5,z10])],[(0,[z126,z0,z1,z2,z3,z5,z10]),(0,[z127,z0,z1,z2,z3,z5,z10]),(0,[z0,z1,z2,z3,z128,z5,z10]),(0,[z75,z0,z1,z2,z3,z115,z10]),(1,[z0,z1,z2,z129,z3,z5]),(0,[z13,z0,z1,z1,z2,z3,z5]),(0,[z130,z0,z1,z2,z3,z5,z10]),(0,[z131,z0,z1,z2,z3,z5,z19])],[(0,[z132,z0,z1,z133,z2,z3,z5]),(0,[z0,z61,z1,z2,z3,z5,z19]),(0,[z0,z1,z2,z7,z3,z5,z10])],[(0,[z134,z0,z1,z2,z3,z5,z10]),(0,[z0,z1,z2,z3,z135,z5,z10]),(0,[z0,z1,z2,z85,z3,z4,z5]),(0,[z13,z0,z1,z2,z3,z5,z47]),(0,[z1,z2,z3,z136,z53,z5,z10]),(0,[z0,z1,z2,z3,z5,z38,z10])],[(0,[z73,z0,z133,z2,z3,z5,z10]),(0,[z137,z0,z1,z2,z3,z5,z10]),(0,[z138,z0,z1,z2,z3,z5,z10]),(0,[z0,z1,z139,z2,z3,z5,z110]),(1,[z0,z1,z2,z3,z5,z140]),(0,[z13,z0,z1,z2,z3,z53,z5]),(1,[z0,z1,z2,z3,z5,z141]),(0,[z0,z1,z2,z142,z3,z5,z10]),(0,[z0,z143,z1,z2,z3,z5,z10])]],
   [[(0,[z0,z1,z71,z3,z53,z5,z10]),(0,[z0,z1,z2,z3,z144,z5,z10]),(1,[z145,z0,z2,z3,z5,z10])],[(0,[z0,z29,z2,z3,z5,z22,z10]),(0,[z0,z1,z2,z7,z3,z5,z34]),(0,[z0,z1,z2,z3,z5,z19,z146])],[(0,[z147,z0,z1,z2,z3,z5,z10]),(0,[z0,z1,z2,z148,z3,z5,z10]),(0,[z0,z1,z2,z3,z115,z5,z10]),(0,[z83,z1,z2,z3,z5,z10,z110]),(0,[z149,z0,z1,z2,z3,z5,z10]),(0,[z0,z1,z2,z3,z5,z150,z10]),(0,[z134,z13,z0,z1,z2,z3,z5]),(0,[z37,z0,z1,z2,z7,z3,z5]),(0,[z0,z1,z2,z3,z5,z151,z19])],[(0,[z0,z1,z133,z2,z3,z5,z19]),(0,[z9,z0,z1,z71,z3,z5,z10]),(0,[z0,z1,z2,z3,z5,z10,z152]),(0,[z0,z61,z2,z3,z21,z5,z10]),(0,[z0,z1,z2,z153,z3,z21,z5]),(0,[z0,z1,z2,z3,z5,z72,z10])],[(1,[z0,z1,z2,z154,z3,z5])],[(0,[z155,z0,z1,z2,z3,z5,z10]),(0,[z13,z8,z0,z1,z2,z3,z5]),(0,[z75,z51,z1,z2,z3,z5,z10]),(0,[z0,z156,z1,z2,z3,z5,z10]),(0,[z0,z1,z2,z157,z3,z5,z10]),(0,[z158,z0,z1,z2,z3,z5,z10])],[(0,[z73,z0,z1,z2,z3,z5,z10]),(0,[z159,z0,z1,z2,z3,z5,z10]),(0,[z147,z13,z0,z1,z2,z3,z5]),(0,[z0,z1,z2,z160,z3,z5,z10]),(0,[z0,z1,z2,z3,z5,z10,z161])],[(0,[z73,z0,z30,z1,z2,z3,z5]),(0,[z0,z1,z2,z162,z3,z5,z10]),(0,[z51,z0,z1,z2,z3,z5,z19]),(0,[z0,z1,z163,z2,z3,z5,z10]),(1,[z0,z1,z2,z7,z3,z5])]],
   [[(0,[z0,z1,z2,z3,z5,z10,z164]),(0,[z0,z1,z2,z3,z165,z5,z10]),(0,[z0,z1,z2,z3,z123,z5,z166]),(0,[z0,z1,z2,z3,z167,z5,z10]),(0,[z86,z0,z168,z2,z3,z5,z10]),(0,[z0,z1,z2,z3,z5,z169,z10])],[(0,[z170,z0,z1,z2,z3,z5,z10]),(0,[z0,z1,z2,z3,z5,z171,z10]),(0,[z12,z13,z0,z2,z3,z5,z10]),(0,[z172,z0,z1,z2,z3,z5,z10]),(0,[z122,z0,z1,z2,z3,z5,z173]),(0,[z145,z0,z1,z2,z3,z5,z10])],[(0,[z0,z1,z2,z3,z5,z174,z10]),(0,[z0,z1,z2,z175,z3,z5,z10]),(0,[z0,z1,z2,z3,z5,z176,z10]),(0,[z177,z0,z1,z2,z3,z5,z10]),(0,[z0,z1,z2,z178,z3,z5,z10]),(0,[z122,z0,z1,z139,z2,z3,z5])],[(0,[z0,z1,z2,z3,z5,z5,z10]),(1,[z119,z1,z2,z3,z5,z166]),(0,[z0,z2,z3,z5,z22,z10,z179]),(1,[z0,z1,z180,z3,z5,z10]),(0,[z0,z1,z2,z3,z104,z5,z141]),(0,[z0,z1,z181,z2,z7,z3,z5])],[(0,[z0,z1,z2,z182,z3,z5,z10]),(0,[z37,z0,z1,z2,z3,z14,z10]),(0,[z0,z1,z2,z3,z5,z47,z19])],[(0,[z1,z133,z2,z3,z5,z108,z10]),(0,[z95,z0,z1,z2,z3,z183,z10]),(1,[z0,z1,z184,z2,z3,z5])],[(0,[z0,z1,z2,z3,z5,z19,z179]),(0,[z0,z1,z70,z2,z53,z5,z10]),(1,[z0,z1,z2,z185,z3,z5]),(0,[z0,z1,z2,z3,z5,z186,z10]),(0,[z0,z1,z2,z3,z5,z19,z187])],[(0,[z13,z48,z0,z1,z2,z3,z5]),(0,[z0,z1,z2,z3,z5,z10,z188]),(0,[z86,z0,z1,z70,z3,z5,z10]),(0,[z0,z1,z2,z3,z5,z10,z189]),(0,[z0,z1,z2,z3,z5,z10,z190]),(0,[z191,z0,z1,z2,z3,z5,z10])]],
   [[(0,[z0,z1,z2,z192,z3,z5,z10]),(1,[z9,z1,z65,z3,z5,z10]),(0,[z95,z0,z1,z2,z3,z193,z10]),(0,[z0,z1,z2,z3,z5,z194,z10]),(0,[z0,z1,z2,z3,z5,z10,z195]),(0,[z196,z0,z1,z2,z3,z5,z10])],[(0,[z0,z1,z2,z3,z197,z5,z10]),(0,[z198,z0,z1,z2,z3,z5,z10]),(0,[z0,z1,z2,z3,z123,z5,z189])],[(0,[z199,z0,z1,z2,z3,z5,z10]),(0,[z200,z0,z1,z2,z3,z5,z10]),(0,[z0,z1,z2,z3,z201,z5,z10]),(1,[z0,z1,z2,z7,z3,z19])],[(0,[z0,z1,z2,z202,z3,z5,z10]),(0,[z203,z0,z1,z2,z3,z5,z10]),(0,[z204,z0,z1,z2,z3,z5,z10])],[(0,[z0,z1,z2,z3,z5,z10,z205]),(0,[z0,z1,z2,z65,z7,z3,z5]),(0,[z0,z1,z2,z3,z5,z10,z206]),(0,[z0,z1,z2,z3,z5,z166,z10]),(0,[z0,z1,z2,z3,z207,z5,z10]),(0,[z208,z0,z1,z2,z3,z5,z10]),(0,[z209,z0,z1,z2,z3,z5,z10])],[(0,[z0,z30,z1,z2,z3,z21,z5]),(0,[z13,z0,z29,z2,z3,z5,z10])],[(0,[z210,z0,z1,z2,z3,z5,z10]),(0,[z0,z1,z2,z3,z5,z211,z10]),(0,[z0,z1,z2,z3,z212,z5,z10]),(0,[z213,z0,z1,z2,z7,z3,z5])],[(0,[z0,z1,z2,z3,z5,z10,z214]),(0,[z8,z0,z1,z2,z3,z5,z206]),(0,[z119,z0,z1,z2,z3,z5,z110]),(0,[z215,z0,z1,z2,z7,z3,z5]),(0,[z0,z1,z216,z2,z3,z5,z10]),(1,[z0,z1,z139,z3,z5,z47]),(0,[z217,z0,z1,z2,z3,z5,z10]),(0,[z0,z1,z2,z7,z3,z10,z19]),(0,[z218,z0,z1,z2,z7,z3,z5])]],
   [[(0,[z95,z0,z1,z219,z3,z5,z10]),(0,[z0,z1,z2,z3,z5,z10,z220]),(0,[z0,z1,z2,z3,z115,z5,z221]),(0,[z215,z0,z2,z3,z21,z5,z10]),(1,[z222,z1,z2,z3,z5,z10]),(0,[z40,z0,z1,z2,z3,z5,z10]),(0,[z223,z0,z1,z2,z3,z5,z10]),(0,[z0,z1,z2,z3,z224,z5,z10])],[(0,[z13,z9,z0,z1,z2,z3,z5]),(0,[z0,z1,z2,z3,z5,z225,z10]),(0,[z13,z0,z1,z2,z3,z87,z5]),(0,[z0,z1,z2,z3,z5,z226,z10]),(0,[z40,z0,z30,z1,z2,z3,z5]),(0,[z0,z1,z66,z3,z53,z5,z10]),(0,[z0,z1,z2,z3,z5,z227,z10]),(0,[z122,z0,z1,z2,z3,z5,z10])],[(0,[z0,z1,z2,z3,z5,z58,z10]),(0,[z75,z1,z2,z3,z5,z108,z10]),(0,[z122,z0,z30,z1,z2,z3,z5])],[],[(0,[z0,z228,z1,z2,z3,z5,z10]),(0,[z95,z26,z1,z2,z3,z5,z10]),(0,[z0,z1,z2,z3,z229,z5,z10]),(0,[z0,z1,z2,z3,z230,z5,z10]),(0,[z40,z13,z0,z1,z2,z3,z5]),(0,[z0,z1,z2,z3,z5,z10,z231]),(0,[z0,z1,z2,z232,z7,z3,z5])],[(0,[z0,z1,z2,z3,z233,z5,z10]),(0,[z0,z1,z70,z2,z3,z5,z10]),(0,[z18,z0,z1,z139,z3,z5,z10]),(0,[z122,z0,z1,z2,z3,z123,z5]),(0,[z0,z1,z2,z3,z5,z234,z19])],[(0,[z0,z1,z2,z3,z5,z10,z235]),(1,[z0,z23,z2,z3,z5,z10]),(0,[z236,z0,z1,z2,z3,z5,z10]),(0,[z0,z1,z2,z3,z237,z5,z10]),(0,[z0,z1,z2,z3,z5,z10,z238])],[(0,[z51,z1,z133,z2,z3,z5,z10]),(0,[z6,z0,z1,z2,z3,z5,z19]),(1,[z0,z1,z2,z3,z239,z5]),(0,[z0,z1,z2,z3,z5,z10,z240]),(0,[z0,z1,z241,z2,z3,z5,z10]),(0,[z0,z1,z2,z3,z5,z242,z10])]],
   [[(0,[z243,z0,z1,z2,z3,z5,z10]),(0,[z48,z0,z1,z2,z7,z3,z5]),(0,[z95,z0,z1,z2,z27,z5,z10]),(0,[z0,z1,z2,z3,z244,z5,z10]),(0,[z13,z0,z1,z2,z3,z5,z42]),(1,[z0,z1,z2,z3,z245,z10]),(0,[z246,z0,z1,z2,z7,z3,z5])],[(0,[z247,z0,z1,z2,z3,z5,z10]),(0,[z86,z0,z1,z2,z53,z5,z10]),(0,[z0,z1,z2,z7,z3,z14,z5]),(1,[z0,z39,z2,z3,z5,z10]),(1,[z113,z0,z1,z2,z7,z3])],[],[(0,[z0,z1,z2,z3,z248,z5,z10]),(0,[z249,z0,z1,z2,z3,z5,z10]),(0,[z0,z1,z2,z3,z5,z173,z110]),(0,[z77,z0,z1,z2,z68,z3,z5]),(0,[z0,z1,z2,z3,z5,z19,z250])],[(0,[z0,z1,z2,z129,z3,z115,z5]),(0,[z69,z0,z1,z2,z3,z5,z194]),(0,[z0,z1,z2,z3,z239,z5,z42])],[(0,[z6,z0,z2,z3,z21,z5,z10]),(0,[z48,z0,z1,z65,z3,z5,z10]),(0,[z0,z251,z1,z2,z3,z5,z10]),(0,[z0,z1,z252,z3,z115,z5,z10]),(1,[z12,z0,z2,z3,z42,z10]),(0,[z13,z0,z30,z1,z2,z3,z5]),(0,[z0,z1,z2,z71,z3,z5,z19]),(0,[z0,z1,z2,z3,z5,z10,z253]),(0,[z0,z1,z2,z3,z254,z5,z10]),(0,[z0,z1,z2,z3,z5,z10,z19])],[(0,[z9,z0,z1,z2,z3,z5,z19]),(0,[z18,z0,z1,z2,z3,z5,z110]),(0,[z255,z0,z1,z2,z3,z5,z10]),(0,[z0,z30,z1,z2,z3,z5,z34]),(0,[z0,z1,z2,z3,z5,z63,z10])],[(0,[z0,z1,z2,z256,z3,z5,z10]),(0,[z0,z257,z1,z2,z3,z5,z10]),(0,[z0,z258,z1,z2,z3,z5,z10]),(0,[z0,z1,z2,z3,z123,z5,z19]),(0,[z0,z1,z2,z3,z259,z5,z10])]],
   [[(0,[z260,z0,z1,z2,z3,z5,z10]),(0,[z261,z0,z1,z2,z3,z5,z10]),(0,[z0,z1,z2,z3,z239,z5,z10]),(0,[z0,z1,z2,z3,z262,z5,z10]),(0,[z13,z13,z0,z1,z2,z3,z5]),(0,[z13,z0,z1,z2,z3,z5,z34]),(0,[z263,z0,z30,z1,z2,z3,z5]),(0,[z0,z1,z264,z2,z3,z5,z10]),(0,[z265,z0,z1,z2,z3,z5,z10]),(0,[z0,z1,z2,z3,z5,z266,z10])],[(0,[z0,z1,z2,z3,z5,z10,z267]),(0,[z0,z1,z2,z3,z268,z5,z10]),(0,[z269,z0,z1,z2,z3,z5,z10]),(0,[z12,z0,z1,z2,z3,z42,z10]),(0,[z0,z1,z2,z3,z270,z5,z10]),(0,[z271,z1,z2,z3,z14,z5,z10]),(0,[z272,z0,z1,z2,z3,z5,z19])],[(0,[z0,z1,z2,z3,z5,z10,z273]),(0,[z0,z1,z2,z7,z3,z5,z179]),(0,[z0,z1,z2,z3,z274,z5,z10])],[(0,[z9,z0,z1,z2,z7,z3,z5]),(0,[z62,z0,z1,z2,z3,z5,z10]),(0,[z0,z1,z2,z7,z85,z3,z5]),(0,[z0,z1,z275,z2,z3,z5,z10]),(0,[z0,z1,z139,z2,z3,z5,z10]),(0,[z40,z0,z1,z180,z3,z5,z10]),(0,[z0,z2,z3,z5,z10,z234,z19])],[(0,[z0,z1,z2,z3,z5,z276,z10]),(0,[z277,z0,z1,z2,z3,z5,z10]),(0,[z0,z1,z2,z3,z278,z5,z10]),(0,[z113,z0,z30,z1,z2,z3,z5])],[(0,[z26,z1,z2,z65,z3,z5,z10]),(0,[z279,z0,z1,z2,z3,z5,z10]),(0,[z280,z0,z1,z2,z3,z5,z10])],[(0,[z13,z83,z0,z1,z2,z3,z5]),(0,[z0,z1,z2,z281,z3,z5,z10]),(0,[z282,z0,z1,z2,z3,z5,z10]),(0,[z0,z1,z2,z3,z5,z10,z283]),(0,[z0,z222,z1,z2,z3,z5,z10]),(0,[z272,z0,z1,z2,z7,z3,z5])],[(1,[z0,z1,z2,z3,z5,z188]),(0,[z0,z1,z2,z3,z5,z10,z284]),(0,[z12,z0,z1,z2,z7,z3,z5]),(0,[z0,z1,z66,z2,z7,z3,z5])]],
   [[(0,[z0,z1,z285,z2,z3,z5,z10]),(0,[z75,z0,z1,z2,z3,z5,z10]),(0,[z0,z286,z1,z2,z3,z5,z10]),(0,[z0,z287,z1,z2,z3,z5,z10]),(1,[z0,z1,z2,z3,z5,z195]),(0,[z86,z0,z1,z2,z3,z5,z10]),(0,[z0,z1,z2,z98,z3,z53,z5]),(1,[z0,z1,z66,z3,z14,z10]),(0,[z0,z1,z2,z7,z3,z5,z173])],[(0,[z92,z0,z1,z2,z3,z5,z19]),(0,[z0,z1,z2,z288,z3,z5,z10]),(0,[z289,z0,z1,z2,z3,z5,z10]),(0,[z86,z0,z30,z1,z2,z3,z5]),(0,[z290,z0,z1,z2,z3,z5,z10])],[(0,[z95,z0,z1,z2,z87,z5,z10]),(0,[z95,z13,z0,z1,z2,z3,z5]),(0,[z291,z0,z1,z2,z3,z5,z10]),(1,[z0,z1,z252,z3,z5,z10]),(0,[z0,z29,z2,z3,z5,z42,z10]),(0,[z0,z1,z2,z3,z292,z5,z10]),(0,[z293,z0,z1,z2,z3,z5,z10]),(0,[z0,z1,z294,z2,z3,z5,z10]),(0,[z0,z1,z2,z106,z3,z104,z5])],[(0,[z0,z295,z1,z2,z3,z5,z10]),(0,[z296,z0,z1,z2,z3,z5,z10]),(0,[z0,z1,z2,z3,z5,z245,z10]),(0,[z0,z1,z2,z3,z5,z297,z10]),(0,[z0,z1,z2,z3,z298,z5,z10])],[(1,[z0,z1,z2,z3,z5,z206]),(0,[z8,z0,z1,z70,z3,z5,z10]),(0,[z0,z1,z2,z3,z5,z10,z299]),(0,[z0,z295,z30,z1,z2,z3,z5]),(0,[z0,z30,z1,z2,z300,z3,z5]),(0,[z0,z301,z1,z2,z3,z5,z10]),(0,[z0,z1,z2,z84,z5,z10,z173])],[(0,[z0,z1,z2,z3,z302,z5,z10]),(0,[z0,z30,z1,z2,z20,z3,z5]),(0,[z303,z0,z1,z2,z3,z5,z10])],[(0,[z92,z0,z1,z2,z3,z5,z273]),(0,[z26,z0,z1,z2,z3,z5,z10]),(0,[z0,z1,z2,z7,z3,z64,z5])],[(0,[z6,z1,z133,z2,z3,z5,z10]),(0,[z0,z133,z2,z3,z21,z5,z10]),(0,[z26,z0,z30,z1,z2,z3,z5]),(0,[z18,z122,z0,z1,z2,z3,z5]),(0,[z0,z1,z304,z2,z3,z5,z10])]],
   [[(0,[z83,z0,z1,z2,z3,z5,z110]),(0,[z0,z1,z2,z3,z5,z305,z10]),(0,[z13,z215,z0,z1,z2,z3,z5]),(0,[z0,z1,z2,z306,z3,z5,z10]),(0,[z0,z307,z1,z2,z3,z5,z10]),(0,[z0,z1,z2,z7,z3,z104,z5])],[(1,[z0,z1,z2,z3,z5,z96]),(0,[z0,z30,z1,z2,z3,z5,z110]),(0,[z0,z1,z2,z3,z308,z5,z10]),(0,[z0,z2,z3,z21,z5,z42,z10]),(0,[z309,z0,z1,z2,z3,z5,z10]),(0,[z0,z1,z66,z2,z3,z14,z10])],[(0,[z13,z92,z0,z1,z2,z3,z5]),(0,[z26,z0,z1,z2,z87,z5,z10]),(0,[z310,z13,z0,z1,z2,z3,z5]),(0,[z13,z18,z0,z1,z2,z3,z5])],[(0,[z0,z1,z2,z3,z5,z311,z10]),(0,[z0,z1,z312,z2,z3,z5,z10]),(0,[z313,z0,z1,z2,z3,z5,z10]),(0,[z0,z1,z2,z3,z14,z5,z10]),(0,[z0,z1,z2,z3,z5,z10,z15])],[(0,[z0,z1,z2,z3,z314,z5,z10]),(0,[z0,z1,z139,z3,z5,z47,z10]),(0,[z40,z191,z1,z2,z3,z5,z10])],[(0,[z0,z1,z315,z2,z3,z5,z10]),(0,[z0,z30,z1,z1,z2,z3,z5])],[(0,[z316,z0,z1,z2,z3,z5,z10]),(0,[z317,z0,z1,z2,z3,z5,z10]),(0,[z13,z75,z0,z1,z2,z3,z5]),(0,[z83,z0,z1,z2,z3,z5,z47]),(0,[z318,z0,z1,z2,z3,z5,z10]),(0,[z0,z1,z2,z3,z5,z10,z319]),(1,[z0,z1,z2,z3,z5,z238])],[(0,[z320,z0,z1,z2,z3,z5,z10]),(0,[z0,z1,z2,z68,z7,z3,z5]),(0,[z321,z0,z1,z2,z3,z5,z10]),(0,[z313,z13,z0,z1,z2,z3,z5]),(0,[z0,z30,z1,z2,z3,z5,z47]),(1,[z0,z1,z2,z3,z5,z240]),(0,[z0,z1,z2,z322,z3,z5,z10]),(0,[z0,z1,z2,z3,z5,z10,z323]),(0,[z0,z1,z2,z20,z3,z104,z10])]],
   [[(0,[z0,z1,z2,z3,z5,z324,z10]),(1,[z309,z1,z2,z3,z5,z10]),(0,[z0,z325,z61,z1,z2,z3,z5]),(0,[z0,z1,z2,z3,z5,z10,z326]),(0,[z0,z30,z1,z2,z3,z53,z5]),(0,[z37,z0,z1,z2,z3,z5,z19])],[(0,[z0,z1,z2,z3,z327,z5,z10])],[(0,[z0,z1,z2,z3,z5,z328,z10]),(0,[z0,z1,z2,z154,z68,z3,z5]),(0,[z12,z0,z61,z2,z3,z5,z10]),(0,[z329,z0,z1,z2,z3,z5,z10])],[(0,[z51,z0,z1,z2,z3,z115,z10]),(0,[z0,z1,z3,z115,z5,z330,z10]),(0,[z119,z0,z1,z2,z3,z5,z10]),(1,[z13,z0,z2,z3,z52,z5]),(0,[z0,z1,z2,z331,z3,z5,z10]),(1,[z0,z30,z2,z3,z5,z22]),(0,[z37,z0,z1,z3,z5,z38,z10])],[(0,[z119,z0,z30,z1,z2,z3,z5]),(0,[z0,z1,z2,z3,z5,z332,z10]),(0,[z333,z0,z1,z2,z3,z5,z10]),(0,[z0,z1,z2,z7,z3,z123,z5])],[(0,[z0,z1,z2,z3,z5,z108,z19]),(0,[z0,z1,z334,z2,z3,z5,z10]),(0,[z335,z0,z1,z2,z3,z5,z10]),(0,[z0,z1,z336,z2,z3,z5,z10]),(0,[z122,z0,z16,z2,z3,z5,z10]),(1,[z0,z1,z2,z3,z5,z19])],[(0,[z48,z8,z0,z1,z3,z5,z10]),(0,[z213,z0,z1,z68,z3,z5,z10]),(0,[z0,z337,z1,z2,z3,z5,z10]),(0,[z0,z325,z1,z2,z3,z5,z10]),(0,[z0,z1,z2,z3,z52,z5,z19]),(0,[z0,z1,z2,z3,z5,z10,z338])],[(1,[z132,z0,z1,z2,z3,z5]),(1,[z0,z339,z1,z2,z3,z5]),(0,[z0,z1,z2,z3,z5,z166,z173]),(0,[z0,z1,z2,z3,z5,z10,z340]),(0,[z0,z325,z30,z1,z2,z3,z5]),(0,[z0,z1,z70,z71,z3,z5,z10])]],
   [[(0,[z0,z1,z341,z2,z3,z5,z10]),(0,[z0,z1,z2,z3,z5,z10,z342]),(0,[z0,z1,z2,z3,z5,z10,z343]),(1,[z0,z1,z2,z344,z5,z10]),(0,[z13,z0,z1,z2,z3,z14,z5]),(0,[z0,z30,z1,z2,z3,z345,z5]),(1,[z0,z1,z2,z3,z5,z346])],[(1,[z0,z1,z2,z3,z5,z267]),(0,[z0,z1,z2,z347,z3,z5,z10]),(0,[z83,z119,z1,z2,z3,z5,z10]),(0,[z83,z122,z0,z1,z2,z3,z5]),(0,[z0,z1,z2,z348,z3,z5,z10]),(0,[z0,z1,z2,z3,z5,z349,z10])],[(1,[z0,z1,z2,z3,z5,z273]),(0,[z95,z0,z350,z2,z3,z5,z10]),(0,[z0,z1,z2,z3,z87,z5,z19]),(0,[z0,z61,z1,z2,z3,z52,z10]),(1,[z0,z1,z2,z3,z351,z10]),(0,[z352,z0,z1,z2,z3,z5,z10]),(1,[z0,z2,z3,z5,z10,z234]),(0,[z0,z1,z2,z3,z353,z5,z10])],[(0,[z354,z0,z1,z2,z3,z5,z10]),(0,[z0,z1,z2,z3,z5,z355,z10])],[(0,[z8,z1,z2,z65,z3,z5,z10]),(0,[z0,z1,z2,z3,z5,z10,z356]),(0,[z13,z122,z0,z1,z2,z3,z5]),(0,[z354,z0,z30,z1,z2,z3,z5]),(0,[z357,z0,z1,z2,z3,z5,z10])],[(0,[z0,z1,z2,z3,z5,z10,z358]),(0,[z0,z1,z2,z3,z359,z5,z10]),(0,[z0,z1,z2,z3,z115,z10,z34]),(1,[z360,z1,z2,z3,z5,z10]),(0,[z13,z0,z30,z2,z3,z5,z10]),(1,[z37,z0,z1,z3,z38,z10]),(1,[z271,z1,z2,z3,z5,z10])],[(0,[z0,z1,z2,z3,z361,z5,z10]),(0,[z0,z29,z133,z2,z3,z5,z10]),(0,[z0,z1,z2,z3,z5,z362,z19]),(0,[z130,z0,z1,z2,z7,z3,z5])],[(0,[z0,z1,z2,z3,z115,z5,z19]),(0,[z363,z0,z1,z2,z3,z5,z10]),(0,[z0,z1,z2,z3,z5,z10,z364]),(1,[z0,z365,z1,z2,z3,z5]),(0,[z0,z1,z2,z7,z7,z3,z5])]],
   [[(0,[z366,z0,z1,z2,z3,z5,z10]),(0,[z367,z0,z1,z2,z3,z5,z10]),(0,[z0,z30,z1,z2,z85,z3,z5])],[(0,[z0,z1,z2,z3,z368,z5,z10]),(0,[z0,z1,z2,z3,z369,z5,z10]),(0,[z13,z0,z1,z2,z3,z5,z179]),(0,[z0,z1,z2,z3,z104,z5,z19]),(0,[z0,z1,z2,z3,z370,z5,z10])],[(0,[z0,z1,z2,z65,z3,z5,z19]),(1,[z26,z1,z2,z27,z5,z10]),(0,[z13,z0,z1,z2,z85,z3,z5]),(0,[z371,z0,z1,z2,z3,z5,z10]),(0,[z0,z1,z2,z372,z3,z5,z10]),(0,[z18,z0,z1,z2,z3,z5,z10]),(0,[z0,z1,z2,z3,z5,z373,z10])],[(0,[z73,z0,z1,z2,z3,z5,z19]),(0,[z374,z0,z1,z2,z3,z5,z10]),(0,[z0,z1,z2,z375,z3,z5,z10]),(0,[z376,z0,z1,z2,z3,z5,z10]),(0,[z0,z1,z2,z153,z3,z5,z10]),(0,[z18,z0,z30,z1,z2,z3,z5]),(0,[z377,z0,z1,z2,z3,z5,z10]),(0,[z378,z0,z1,z2,z3,z5,z19]),(0,[z0,z365,z1,z2,z3,z5,z10])],[(0,[z0,z1,z2,z3,z5,z10,z379]),(0,[z213,z0,z1,z2,z3,z5,z19]),(0,[z0,z1,z380,z2,z3,z5,z10]),(0,[z381,z0,z1,z2,z3,z5,z10])],[(0,[z8,z0,z1,z2,z3,z5,z10]),(0,[z95,z0,z382,z2,z3,z5,z10]),(0,[z0,z1,z2,z3,z5,z383,z10]),(0,[z384,z0,z1,z2,z3,z5,z10]),(0,[z0,z385,z1,z2,z3,z5,z10]),(0,[z0,z29,z1,z2,z3,z5,z10]),(0,[z215,z0,z1,z2,z3,z5,z19]),(0,[z0,z386,z1,z2,z3,z5,z10]),(0,[z0,z387,z1,z2,z3,z5,z10]),(0,[z388,z0,z1,z2,z3,z5,z10])],[(0,[z8,z0,z30,z1,z2,z3,z5]),(0,[z0,z1,z2,z3,z183,z5,z10]),(0,[z0,z29,z30,z1,z2,z3,z5]),(0,[z0,z386,z30,z1,z2,z3,z5]),(0,[z86,z0,z23,z2,z3,z5,z10]),(0,[z0,z1,z2,z3,z389,z5,z10]),(0,[z0,z1,z180,z2,z3,z5,z10]),(0,[z0,z1,z2,z3,z5,z10,z34]),(0,[z145,z0,z1,z2,z3,z5,z19])],[(0,[z0,z1,z2,z390,z3,z5,z10]),(0,[z0,z1,z2,z3,z5,z391,z10]),(0,[z0,z1,z2,z3,z5,z42,z10]),(0,[z13,z0,z1,z2,z3,z5,z173]),(0,[z0,z1,z2,z7,z3,z259,z5])]],
   [[(0,[z73,z0,z1,z2,z7,z3,z5]),(0,[z0,z1,z3,z368,z87,z5,z10]),(0,[z12,z0,z1,z2,z3,z5,z195]),(0,[z0,z1,z2,z392,z3,z5,z10]),(0,[z13,z0,z1,z139,z2,z3,z5]),(0,[z86,z0,z1,z2,z3,z245,z10]),(0,[z0,z1,z2,z3,z5,z10,z393]),(0,[z40,z0,z1,z99,z3,z5,z10]),(1,[z0,z2,z3,z5,z234,z19]),(0,[z0,z1,z2,z160,z7,z3,z5])],[(0,[z0,z1,z2,z3,z5,z394,z10])],[(0,[z0,z1,z395,z2,z3,z5,z10]),(0,[z0,z30,z1,z2,z3,z87,z5]),(0,[z213,z0,z2,z3,z21,z5,z10]),(0,[z13,z213,z0,z1,z2,z3,z5]),(0,[z0,z1,z2,z396,z3,z5,z10]),(0,[z13,z0,z1,z2,z202,z3,z5]),(0,[z397,z0,z1,z2,z3,z5,z10]),(0,[z0,z1,z2,z20,z3,z10,z34])],[(1,[z0,z1,z285,z2,z3,z5]),(0,[z398,z0,z1,z2,z3,z5,z10]),(0,[z0,z1,z2,z399,z3,z5,z10]),(1,[z0,z1,z2,z3,z5,z15]),(0,[z0,z1,z2,z3,z5,z19,z189]),(1,[z0,z1,z2,z84,z5,z173]),(0,[z0,z400,z1,z2,z3,z5,z10])],[(1,[z0,z1,z219,z3,z5,z10]),(0,[z401,z0,z1,z2,z3,z5,z10]),(0,[z402,z0,z1,z2,z3,z5,z10]),(0,[z0,z1,z2,z7,z3,z5,z38]),(0,[z0,z1,z2,z20,z3,z5,z19])],[(0,[z403,z0,z1,z2,z3,z5,z10]),(0,[z0,z1,z2,z404,z3,z5,z10]),(0,[z405,z0,z1,z2,z3,z5,z10]),(0,[z69,z0,z1,z2,z3,z5,z10]),(0,[z0,z1,z2,z3,z21,z5,z19]),(0,[z13,z0,z1,z2,z3,z64,z5])],[(0,[z48,z0,z1,z2,z3,z5,z19]),(0,[z1,z2,z27,z3,z87,z5,z10]),(0,[z0,z1,z2,z3,z5,z406,z10]),(0,[z69,z0,z30,z1,z2,z3,z5]),(0,[z0,z1,z2,z3,z5,z407,z10]),(0,[z40,z0,z1,z2,z3,z5,z238]),(0,[z0,z1,z2,z3,z5,z19,z408])],[(0,[z0,z1,z66,z68,z3,z5,z10]),(0,[z0,z30,z61,z1,z2,z3,z5]),(0,[z13,z0,z1,z2,z3,z104,z5]),(0,[z0,z1,z2,z409,z3,z14,z5])]],
   [[(0,[z95,z1,z2,z3,z87,z5,z10]),(0,[z0,z1,z2,z3,z5,z410,z10]),(1,[z77,z0,z1,z2,z3,z5]),(1,[z0,z1,z411,z3,z5,z10]),(0,[z13,z0,z412,z1,z2,z3,z5]),(0,[z0,z1,z2,z3,z5,z10,z413]),(0,[z414,z0,z1,z2,z3,z5,z19])],[(0,[z48,z0,z1,z3,z5,z38,z10]),(0,[z95,z8,z1,z2,z3,z5,z10]),(0,[z0,z1,z2,z27,z3,z5,z10]),(0,[z0,z1,z68,z3,z5,z38,z10]),(0,[z0,z1,z2,z3,z415,z5,z10]),(0,[z0,z30,z1,z2,z3,z5,z42]),(0,[z0,z1,z2,z416,z3,z5,z10]),(0,[z13,z0,z61,z1,z2,z3,z5]),(0,[z0,z1,z2,z3,z38,z10,z34]),(0,[z0,z1,z2,z417,z3,z5,z10])],[(0,[z418,z0,z1,z2,z3,z5,z10]),(1,[z12,z13,z0,z2,z3,z5]),(0,[z0,z1,z2,z7,z3,z5,z22]),(0,[z0,z1,z139,z2,z3,z5,z189]),(0,[z0,z1,z2,z3,z64,z5,z19])],[(0,[z1,z2,z3,z87,z5,z108,z10]),(1,[z0,z1,z2,z419,z3,z5]),(0,[z26,z1,z2,z3,z5,z108,z10]),(0,[z0,z1,z2,z85,z3,z5,z19]),(0,[z0,z360,z1,z2,z3,z5,z10]),(0,[z0,z1,z2,z3,z420,z5,z10]),(0,[z0,z1,z2,z3,z5,z41,z10]),(0,[z40,z0,z1,z2,z3,z10,z34])],[(0,[z0,z1,z285,z133,z2,z3,z5]),(0,[z51,z0,z1,z2,z3,z108,z10]),(0,[z83,z0,z1,z2,z3,z5,z10]),(0,[z421,z0,z1,z2,z3,z5,z10]),(0,[z0,z1,z2,z3,z5,z422,z10]),(1,[z0,z307,z2,z3,z5,z10])],[(0,[z423,z0,z1,z2,z3,z5,z10]),(0,[z51,z26,z1,z2,z3,z5,z10]),(0,[z83,z0,z30,z1,z2,z3,z5]),(0,[z0,z1,z2,z3,z424,z5,z10]),(0,[z0,z30,z1,z2,z3,z5,z10]),(0,[z0,z425,z1,z2,z3,z5,z10]),(0,[z0,z1,z2,z84,z3,z5,z10])],[(0,[z51,z1,z2,z3,z87,z5,z10]),(0,[z0,z1,z2,z3,z426,z5,z10]),(1,[z0,z1,z2,z153,z3,z5]),(0,[z0,z1,z2,z3,z427,z5,z10]),(0,[z0,z30,z30,z1,z2,z3,z5]),(0,[z0,z1,z428,z2,z3,z5,z10]),(0,[z122,z0,z1,z2,z3,z5,z19])],[(0,[z0,z1,z429,z2,z3,z5,z10]),(0,[z75,z0,z1,z2,z3,z5,z188]),(0,[z13,z0,z1,z2,z3,z5,z10]),(0,[z0,z1,z2,z3,z430,z5,z10]),(0,[z0,z1,z2,z3,z5,z10,z431])]],
   [[(0,[z0,z1,z2,z7,z3,z5,z108]),(0,[z432,z0,z1,z2,z3,z5,z10]),(0,[z12,z309,z1,z2,z3,z5,z10]),(0,[z433,z0,z1,z2,z3,z5,z10]),(0,[z0,z1,z2,z3,z345,z5,z10]),(1,[z0,z434,z2,z3,z5,z10])],[(0,[z0,z1,z2,z3,z5,z435,z10]),(0,[z0,z1,z2,z3,z5,z10,z110]),(0,[z213,z69,z0,z2,z3,z5,z10]),(0,[z69,z0,z1,z2,z3,z5,z436]),(0,[z0,z2,z85,z3,z21,z5,z10]),(0,[z0,z29,z1,z2,z85,z5,z10]),(0,[z437,z0,z1,z2,z3,z5,z10]),(0,[z0,z30,z1,z2,z3,z123,z5]),(0,[z438,z0,z1,z2,z3,z5,z10]),(0,[z0,z1,z2,z3,z439,z5,z10]),(0,[z0,z1,z2,z84,z3,z123,z5]),(0,[z0,z1,z2,z123,z5,z10,z173])],[(0,[z440,z0,z1,z2,z3,z5,z10]),(0,[z0,z1,z2,z3,z441,z5,z10]),(0,[z263,z0,z1,z2,z3,z5,z10]),(0,[z442,z0,z1,z2,z3,z5,z10]),(0,[z40,z0,z1,z2,z7,z3,z5]),(0,[z0,z434,z1,z2,z3,z5,z10]),(0,[z0,z1,z2,z3,z5,z443,z10])],[(0,[z0,z1,z2,z2,z3,z5,z10]),(0,[z0,z1,z2,z444,z3,z5,z10]),(0,[z0,z1,z2,z3,z123,z5,z110]),(0,[z0,z1,z2,z344,z3,z5,z10]),(0,[z13,z0,z1,z2,z3,z445,z5]),(0,[z13,z0,z1,z2,z3,z123,z5]),(0,[z0,z1,z2,z446,z3,z5,z10]),(0,[z122,z0,z1,z2,z7,z3,z5]),(0,[z0,z1,z447,z2,z3,z5,z10])],[(0,[z9,z0,z1,z3,z5,z38,z10]),(0,[z0,z29,z1,z2,z21,z5,z10]),(0,[z13,z0,z1,z70,z2,z3,z5]),(0,[z13,z0,z2,z3,z5,z10,z179]),(0,[z0,z30,z1,z2,z331,z3,z5]),(0,[z86,z0,z1,z3,z53,z5,z10])],[(0,[z448,z0,z1,z2,z3,z5,z10]),(0,[z8,z51,z1,z2,z3,z5,z10]),(0,[z95,z0,z1,z449,z3,z5,z10]),(0,[z0,z1,z2,z3,z450,z5,z10]),(0,[z0,z61,z1,z2,z3,z5,z10]),(0,[z12,z0,z1,z2,z3,z5,z19]),(0,[z0,z1,z66,z2,z3,z5,z19])],[(0,[z451,z0,z1,z2,z3,z5,z10]),(0,[z13,z0,z1,z2,z65,z3,z5]),(0,[z0,z1,z2,z3,z5,z452,z10]),(0,[z0,z1,z2,z7,z3,z5,z166]),(0,[z13,z0,z1,z2,z3,z5,z140]),(0,[z448,z0,z30,z1,z2,z3,z5]),(0,[z0,z453,z1,z2,z3,z5,z10]),(0,[z0,z1,z2,z3,z454,z5,z10]),(0,[z0,z1,z2,z3,z5,z455,z10]),(0,[z113,z0,z1,z2,z3,z5,z10])],[(0,[z0,z1,z2,z456,z3,z5,z10]),(0,[z9,z1,z2,z27,z3,z5,z10]),(0,[z86,z48,z0,z1,z3,z5,z10]),(1,[z0,z1,z2,z3,z5,z457]),(0,[z0,z1,z70,z2,z7,z3,z5])]],
   [[(0,[z458,z0,z1,z2,z3,z5,z10]),(0,[z0,z459,z1,z2,z3,z5,z10]),(0,[z12,z0,z1,z2,z344,z5,z10]),(0,[z0,z1,z100,z2,z3,z5,z42]),(0,[z0,z1,z2,z7,z71,z3,z5]),(1,[z0,z1,z2,z106,z3,z5])],[(0,[z95,z0,z1,z2,z3,z5,z10]),(0,[z119,z0,z1,z2,z3,z5,z166]),(0,[z0,z1,z2,z3,z460,z5,z10]),(0,[z0,z1,z2,z3,z461,z5,z10]),(0,[z0,z1,z2,z3,z123,z5,z47])],[(0,[z462,z0,z1,z2,z3,z5,z10]),(0,[z95,z0,z30,z1,z2,z3,z5]),(0,[z0,z1,z2,z3,z5,z10,z463]),(0,[z213,z0,z29,z2,z3,z5,z10]),(0,[z464,z0,z1,z2,z3,z5,z10]),(0,[z0,z1,z2,z3,z5,z10,z146])],[(0,[z0,z1,z133,z2,z3,z5,z10]),(0,[z0,z1,z2,z3,z465,z5,z10]),(0,[z215,z0,z29,z2,z3,z5,z10]),(0,[z0,z1,z2,z3,z466,z5,z10]),(0,[z0,z1,z2,z85,z5,z10,z34]),(0,[z0,z1,z2,z3,z5,z22,z19])],[(0,[z467,z0,z1,z2,z3,z5,z10]),(0,[z0,z468,z1,z2,z3,z5,z10]),(0,[z0,z1,z70,z65,z3,z5,z10])],[(0,[z92,z6,z1,z2,z3,z5,z10]),(0,[z95,z9,z1,z2,z3,z5,z10]),(0,[z0,z1,z2,z3,z115,z104,z10]),(0,[z12,z360,z1,z2,z3,z5,z10]),(0,[z0,z1,z2,z3,z5,z346,z10]),(0,[z0,z1,z2,z3,z5,z10,z469]),(0,[z470,z0,z1,z2,z3,z5,z10])],[(0,[z471,z0,z1,z2,z3,z5,z10]),(0,[z0,z1,z2,z3,z472,z5,z10]),(0,[z0,z2,z3,z52,z5,z22,z10]),(0,[z13,z0,z1,z2,z7,z3,z5]),(0,[z0,z1,z70,z2,z71,z5,z10]),(0,[z0,z1,z2,z473,z3,z5,z10]),(0,[z474,z0,z1,z2,z3,z5,z10])],[(0,[z0,z1,z2,z3,z475,z5,z10]),(0,[z51,z0,z1,z2,z3,z5,z10]),(0,[z1,z2,z3,z5,z166,z10,z110]),(0,[z476,z0,z1,z2,z3,z5,z10]),(0,[z0,z2,z68,z3,z21,z5,z10]),(0,[z0,z1,z2,z3,z5,z477,z10]),(1,[z0,z29,z2,z85,z5,z10]),(0,[z0,z1,z2,z478,z3,z5,z10]),(0,[z0,z168,z1,z2,z3,z5,z10]),(0,[z0,z1,z2,z7,z3,z5,z189])]],
   [[(0,[z0,z1,z2,z3,z479,z5,z10]),(0,[z51,z0,z30,z1,z2,z3,z5]),(0,[z0,z1,z2,z3,z480,z5,z10])],[(0,[z310,z0,z1,z2,z3,z5,z10]),(0,[z0,z481,z1,z2,z3,z5,z10]),(0,[z0,z1,z2,z256,z7,z3,z5])],[(0,[z92,z73,z1,z2,z3,z5,z10]),(0,[z0,z1,z1,z2,z3,z5,z10]),(0,[z119,z0,z1,z2,z3,z5,z189]),(0,[z0,z1,z2,z3,z53,z5,z19]),(0,[z0,z482,z1,z2,z3,z5,z10])],[(0,[z483,z0,z1,z2,z3,z5,z10]),(0,[z0,z1,z2,z3,z4,z5,z10]),(0,[z484,z0,z1,z2,z3,z5,z10])],[(0,[z0,z1,z2,z485,z3,z5,z10]),(1,[z0,z1,z2,z3,z5,z194]),(0,[z69,z0,z1,z66,z3,z5,z10]),(0,[z0,z1,z2,z3,z5,z47,z10])],[(0,[z75,z0,z1,z2,z3,z5,z19]),(0,[z0,z1,z2,z68,z3,z5,z19]),(0,[z86,z0,z1,z2,z3,z5,z19]),(0,[z0,z1,z139,z2,z7,z3,z5]),(0,[z0,z1,z2,z3,z5,z10,z486])],[(0,[z487,z0,z1,z2,z3,z5,z10]),(1,[z1,z2,z3,z136,z5,z10]),(0,[z0,z1,z2,z3,z5,z10,z488]),(0,[z0,z1,z2,z409,z3,z5,z10])],[(0,[z0,z1,z2,z3,z5,z489,z10]),(0,[z490,z0,z1,z2,z3,z5,z10]),(0,[z0,z1,z2,z3,z5,z10,z187]),(0,[z0,z1,z184,z2,z3,z21,z5]),(0,[z0,z1,z2,z491,z3,z5,z10]),(0,[z0,z1,z2,z3,z5,z140,z10]),(0,[z487,z0,z30,z1,z2,z3,z5]),(0,[z0,z1,z2,z3,z5,z10,z492])]],
   [[(0,[z6,z0,z29,z2,z3,z5,z10]),(0,[z18,z0,z1,z2,z3,z5,z166]),(0,[z86,z0,z1,z2,z3,z5,z346])],[(0,[z6,z73,z0,z2,z3,z5,z10])],[(0,[z8,z1,z2,z3,z5,z108,z10]),(0,[z75,z0,z1,z2,z7,z3,z5]),(0,[z0,z1,z411,z2,z3,z5,z10]),(0,[z86,z0,z1,z2,z3,z351,z10]),(0,[z86,z0,z1,z2,z7,z3,z5]),(0,[z0,z1,z2,z3,z493,z5,z10]),(0,[z0,z1,z2,z494,z3,z5,z10])],[(0,[z0,z1,z2,z3,z5,z10,z495]),(0,[z13,z0,z1,z2,z3,z5,z38]),(1,[z0,z1,z2,z3,z5,z41])],[(0,[z0,z1,z2,z3,z5,z496,z10]),(0,[z0,z1,z2,z497,z3,z5,z10]),(0,[z40,z0,z39,z2,z3,z5,z10])],[(0,[z0,z295,z1,z2,z7,z3,z5]),(0,[z0,z1,z2,z3,z5,z10,z498]),(0,[z0,z1,z2,z3,z5,z10,z499])],[(0,[z0,z1,z65,z3,z53,z5,z10]),(0,[z0,z1,z500,z2,z3,z5,z10]),(0,[z13,z113,z0,z1,z2,z3,z5]),(0,[z0,z1,z2,z185,z3,z53,z5]),(0,[z0,z1,z2,z3,z5,z501,z10]),(0,[z0,z1,z2,z3,z5,z173,z189])],[(1,[z73,z133,z2,z3,z5,z10]),(0,[z0,z1,z2,z3,z502,z5,z10]),(0,[z0,z1,z2,z104,z5,z10,z34])]],
   [[(0,[z26,z0,z1,z2,z7,z3,z5]),(0,[z12,z0,z1,z411,z3,z5,z10]),(0,[z13,z503,z0,z1,z2,z3,z5]),(0,[z109,z0,z1,z2,z3,z5,z19])],[(0,[z504,z0,z1,z2,z3,z5,z10]),(0,[z0,z1,z2,z3,z5,z505,z10]),(0,[z506,z0,z1,z2,z3,z5,z10]),(0,[z12,z0,z2,z3,z5,z22,z10]),(0,[z507,z0,z1,z2,z3,z5,z10]),(0,[z13,z0,z1,z2,z3,z5,z22]),(0,[z0,z1,z2,z3,z508,z5,z10]),(0,[z0,z30,z1,z2,z3,z14,z5]),(0,[z86,z0,z1,z2,z71,z5,z10]),(0,[z18,z0,z1,z2,z3,z5,z189])],[(0,[z0,z1,z2,z3,z509,z5,z10]),(0,[z0,z1,z2,z510,z3,z5,z10]),(0,[z0,z511,z1,z2,z3,z5,z10]),(0,[z506,z0,z30,z1,z2,z3,z5]),(0,[z0,z30,z1,z2,z3,z512,z5]),(0,[z0,z1,z2,z3,z5,z513,z10])],[(0,[z0,z1,z514,z2,z3,z5,z10]),(0,[z0,z1,z2,z3,z515,z5,z10]),(0,[z0,z1,z2,z3,z5,z10,z516]),(0,[z517,z0,z1,z2,z3,z5,z10]),(0,[z518,z13,z0,z1,z2,z3,z5]),(0,[z40,z0,z1,z2,z3,z104,z10])],[(0,[z0,z1,z2,z519,z3,z5,z10]),(0,[z520,z0,z1,z2,z3,z5,z10]),(0,[z119,z1,z2,z3,z5,z166,z10]),(0,[z0,z1,z2,z3,z521,z5,z10]),(0,[z0,z1,z2,z3,z5,z522,z10])],[(0,[z0,z1,z2,z21,z5,z10,z34]),(1,[z0,z168,z2,z3,z5,z10]),(0,[z0,z1,z2,z7,z3,z5,z19])],[(0,[z0,z1,z2,z3,z523,z5,z10]),(0,[z0,z1,z2,z524,z3,z5,z10]),(0,[z92,z6,z0,z2,z3,z5,z10]),(0,[z525,z0,z1,z2,z3,z5,z10]),(1,[z290,z1,z2,z3,z5,z10]),(0,[z0,z1,z2,z3,z5,z38,z19]),(0,[z0,z1,z2,z3,z526,z5,z10]),(2,[z145,z0,z2,z3,z5]),(0,[z0,z1,z527,z2,z3,z5,z10])],[(0,[z6,z0,z1,z2,z3,z5,z10]),(0,[z0,z1,z2,z3,z5,z528,z10]),(0,[z13,z0,z1,z2,z3,z5,z108])]],
   [[(0,[z6,z0,z30,z1,z2,z3,z5]),(0,[z119,z0,z1,z2,z3,z5,z19]),(1,[z145,z0,z2,z3,z5,z19])],[(0,[z0,z1,z2,z7,z3,z115,z5]),(1,[z13,z0,z2,z3,z21,z5]),(0,[z529,z0,z1,z2,z3,z5,z10]),(1,[z93,z1,z2,z3,z5,z10])],[(0,[z0,z30,z1,z2,z3,z5,z179])],[(0,[z0,z1,z530,z2,z3,z5,z10]),(1,[z0,z1,z348,z3,z5,z10]),(0,[z86,z222,z1,z2,z3,z5,z10]),(0,[z531,z0,z1,z2,z3,z5,z10]),(0,[z0,z325,z1,z2,z3,z5,z19])],[(0,[z532,z0,z1,z2,z3,z5,z10]),(1,[z0,z1,z2,z3,z183,z10]),(0,[z0,z1,z2,z3,z5,z10,z250]),(0,[z0,z1,z2,z3,z5,z10,z533]),(0,[z0,z1,z2,z3,z136,z5,z10]),(0,[z0,z1,z534,z2,z3,z5,z10]),(0,[z329,z0,z1,z2,z7,z3,z5])],[(0,[z0,z1,z2,z535,z3,z5,z10]),(0,[z0,z1,z2,z3,z5,z10,z10]),(0,[z119,z0,z1,z2,z7,z3,z5]),(0,[z13,z0,z1,z2,z3,z5,z166]),(0,[z0,z1,z2,z3,z5,z536,z10]),(0,[z0,z1,z2,z71,z3,z5,z10])],[(0,[z537,z0,z1,z2,z3,z5,z10]),(0,[z0,z1,z350,z2,z3,z5,z10]),(0,[z0,z412,z1,z2,z3,z5,z10])],[(0,[z538,z0,z1,z2,z3,z5,z10]),(0,[z539,z0,z1,z2,z3,z5,z10]),(1,[z0,z1,z2,z3,z193,z10]),(0,[z540,z0,z1,z2,z3,z5,z10]),(0,[z0,z541,z1,z2,z3,z5,z10]),(0,[z13,z0,z1,z2,z71,z3,z5]),(0,[z0,z1,z2,z3,z351,z5,z10]),(0,[z0,z1,z2,z542,z3,z5,z10]),(0,[z0,z543,z1,z2,z3,z5,z10]),(0,[z0,z1,z2,z3,z123,z5,z10])]],
   [[(0,[z544,z0,z1,z2,z3,z5,z10]),(0,[z0,z1,z2,z3,z5,z545,z10]),(0,[z546,z0,z1,z2,z3,z5,z10]),(0,[z547,z0,z1,z2,z3,z5,z10]),(0,[z0,z30,z1,z2,z3,z5,z173]),(0,[z0,z1,z2,z98,z3,z5,z10]),(0,[z0,z1,z2,z548,z3,z5,z10]),(0,[z0,z1,z2,z3,z5,z549,z10]),(0,[z0,z1,z2,z84,z3,z5,z173]),(0,[z0,z1,z2,z35,z3,z5,z10])],[(0,[z0,z30,z1,z133,z2,z3,z5]),(0,[z0,z1,z2,z550,z3,z5,z10]),(1,[z0,z382,z2,z3,z5,z10]),(1,[z51,z1,z2,z3,z115,z10]),(0,[z0,z30,z1,z2,z68,z3,z5]),(0,[z0,z30,z1,z139,z2,z3,z5]),(1,[z18,z0,z1,z3,z5,z189])],[(0,[z92,z0,z133,z2,z3,z5,z10]),(0,[z0,z1,z551,z2,z3,z5,z10]),(0,[z37,z0,z1,z2,z3,z5,z492]),(0,[z0,z1,z2,z3,z5,z552,z10])],[(0,[z13,z0,z1,z133,z2,z3,z5]),(1,[z0,z1,z3,z368,z5,z10]),(0,[z83,z0,z1,z2,z3,z5,z189]),(0,[z13,z0,z1,z2,z68,z3,z5]),(0,[z0,z553,z1,z2,z3,z5,z10]),(0,[z0,z1,z2,z3,z5,z5,z19])],[(0,[z0,z1,z139,z2,z3,z5,z166]),(1,[z0,z1,z2,z3,z5,z391]),(0,[z0,z1,z2,z3,z445,z5,z10]),(0,[z0,z30,z1,z2,z3,z5,z63]),(0,[z0,z30,z1,z2,z3,z5,z189]),(0,[z0,z1,z3,z14,z5,z38,z10]),(0,[z0,z1,z2,z3,z5,z173,z19])],[(0,[z554,z0,z1,z2,z3,z5,z10]),(1,[z0,z1,z2,z555,z5,z10]),(0,[z272,z13,z0,z1,z2,z3,z5])],[(0,[z556,z0,z1,z2,z3,z5,z10]),(0,[z0,z1,z557,z2,z3,z5,z10]),(0,[z558,z0,z1,z2,z3,z5,z10]),(0,[z0,z1,z2,z3,z559,z5,z10]),(0,[z0,z1,z2,z3,z555,z5,z10]),(0,[z13,z0,z1,z2,z3,z5,z189]),(0,[z554,z0,z30,z1,z2,z3,z5]),(0,[z0,z30,z1,z2,z3,z64,z5]),(0,[z357,z0,z1,z2,z7,z3,z5])],[(0,[z0,z1,z2,z560,z3,z5,z10]),(0,[z561,z0,z1,z2,z3,z5,z10]),(0,[z366,z0,z1,z3,z87,z5,z10]),(1,[z0,z1,z2,z3,z5,z492]),(0,[z0,z1,z2,z562,z3,z5,z10])]],
   [[(1,[z92,z6,z2,z3,z5,z10]),(0,[z0,z30,z1,z2,z3,z104,z5])],[(0,[z92,z0,z1,z2,z3,z5,z10]),(0,[z563,z0,z1,z2,z3,z5,z10]),(0,[z0,z564,z1,z2,z3,z5,z10]),(0,[z0,z1,z2,z565,z3,z5,z10]),(0,[z0,z1,z2,z3,z5,z10,z436]),(0,[z13,z69,z0,z1,z2,z3,z5])],[(0,[z92,z0,z30,z1,z2,z3,z5]),(0,[z0,z1,z2,z3,z108,z10,z34]),(1,[z83,z1,z2,z3,z5,z110]),(0,[z566,z0,z1,z2,z3,z5,z10]),(0,[z0,z1,z2,z567,z3,z5,z10]),(0,[z0,z1,z2,z7,z3,z52,z5]),(0,[z568,z0,z1,z2,z3,z5,z10]),(0,[z0,z1,z2,z3,z569,z5,z10]),(0,[z0,z1,z570,z2,z3,z5,z10])],[(1,[z0,z1,z2,z3,z5,z452]),(0,[z0,z1,z2,z419,z3,z87,z5]),(0,[z0,z1,z2,z3,z5,z10,z571]),(0,[z13,z0,z2,z3,z52,z5,z10])],[(1,[z366,z0,z1,z3,z5,z10]),(0,[z0,z1,z2,z3,z5,z166,z19]),(0,[z213,z0,z295,z2,z3,z5,z10]),(0,[z0,z1,z2,z3,z5,z10,z572]),(1,[z529,z1,z2,z3,z5,z10]),(0,[z0,z1,z573,z2,z3,z5,z10]),(0,[z18,z0,z1,z2,z7,z3,z5])],[(0,[z0,z1,z2,z574,z3,z5,z10]),(0,[z575,z0,z1,z2,z3,z5,z10]),(0,[z0,z1,z2,z3,z5,z10,z576]),(0,[z503,z0,z1,z2,z3,z5,z10]),(0,[z0,z1,z2,z577,z3,z5,z10]),(0,[z0,z1,z2,z578,z3,z5,z10]),(0,[z0,z1,z2,z3,z5,z579,z10]),(0,[z0,z1,z2,z3,z5,z10,z580]),(0,[z0,z365,z1,z2,z7,z3,z5])],[(0,[z0,z295,z2,z68,z3,z5,z10]),(0,[z13,z0,z1,z216,z2,z3,z5]),(0,[z581,z0,z1,z2,z3,z5,z10]),(0,[z0,z1,z16,z2,z3,z5,z10])],[(0,[z8,z0,z1,z2,z7,z3,z5]),(0,[z75,z0,z1,z2,z3,z5,z457]),(0,[z0,z29,z1,z2,z7,z3,z5]),(0,[z0,z93,z1,z2,z3,z5,z10])]],
   [[(0,[z0,z1,z2,z3,z582,z5,z10]),(0,[z40,z0,z1,z2,z3,z5,z19])],[(0,[z0,z1,z2,z3,z512,z5,z10]),(0,[z0,z1,z2,z7,z3,z583,z5])],[(0,[z0,z1,z2,z449,z3,z5,z10]),(0,[z0,z1,z2,z3,z5,z193,z10]),(0,[z0,z1,z2,z3,z5,z584,z10]),(0,[z0,z1,z2,z3,z5,z10,z585])],[(0,[z0,z1,z2,z3,z5,z586,z10]),(0,[z0,z1,z2,z3,z5,z10,z221]),(0,[z0,z1,z2,z185,z3,z5,z10]),(0,[z587,z0,z1,z2,z3,z5,z10]),(1,[z0,z1,z2,z409,z3,z5]),(0,[z0,z1,z2,z99,z3,z5,z10])],[(0,[z8,z0,z1,z2,z3,z5,z225]),(0,[z122,z119,z0,z1,z2,z3,z5]),(0,[z69,z0,z295,z1,z3,z5,z10]),(0,[z13,z0,z1,z66,z2,z3,z5]),(0,[z0,z1,z2,z3,z5,z10,z588])],[(0,[z589,z0,z1,z2,z3,z5,z10]),(0,[z0,z1,z2,z7,z3,z21,z5]),(0,[z0,z1,z590,z2,z3,z5,z10]),(0,[z0,z30,z1,z70,z2,z3,z5]),(0,[z0,z1,z70,z2,z3,z5,z19]),(0,[z0,z1,z66,z3,z14,z5,z10]),(0,[z591,z0,z1,z2,z3,z5,z10]),(0,[z0,z1,z2,z3,z5,z592,z10]),(0,[z398,z0,z1,z2,z7,z3,z5])],[(0,[z73,z1,z133,z2,z3,z5,z10]),(0,[z9,z51,z1,z2,z3,z5,z10]),(0,[z0,z1,z2,z419,z3,z5,z10]),(0,[z593,z0,z1,z2,z3,z5,z10]),(0,[z0,z1,z2,z3,z104,z108,z10]),(0,[z51,z1,z2,z3,z115,z5,z10]),(0,[z0,z1,z2,z3,z14,z104,z10])],[(0,[z0,z30,z1,z2,z65,z3,z5]),(0,[z0,z1,z2,z594,z3,z5,z10]),(0,[z69,z0,z1,z2,z7,z3,z5]),(0,[z0,z1,z2,z3,z5,z47,z173]),(0,[z0,z595,z1,z2,z3,z5,z10]),(0,[z131,z0,z1,z2,z3,z5,z10])]],
   [[(0,[z596,z0,z1,z2,z3,z5,z10]),(0,[z597,z0,z1,z2,z3,z5,z10]),(0,[z598,z0,z1,z2,z3,z5,z10]),(1,[z213,z69,z0,z3,z5,z10]),(0,[z529,z1,z2,z3,z53,z5,z10]),(0,[z0,z1,z70,z3,z5,z38,z10]),(0,[z37,z0,z1,z2,z3,z5,z10])],[(0,[z0,z1,z2,z3,z5,z10,z49]),(0,[z599,z0,z1,z2,z3,z5,z10]),(1,[z0,z1,z449,z3,z5,z10]),(0,[z0,z1,z2,z600,z3,z5,z10]),(0,[z0,z1,z2,z3,z5,z601,z10]),(0,[z13,z0,z1,z2,z84,z3,z5]),(0,[z0,z1,z2,z3,z5,z10,z602]),(0,[z37,z0,z30,z1,z2,z3,z5])],[(0,[z603,z0,z1,z2,z3,z5,z10])],[(0,[z0,z604,z1,z2,z3,z5,z10]),(0,[z18,z0,z1,z3,z5,z10,z189]),(0,[z0,z1,z2,z3,z605,z5,z10])],[(0,[z0,z1,z2,z606,z3,z5,z10]),(0,[z1,z2,z3,z115,z5,z108,z10]),(0,[z0,z1,z2,z3,z5,z10,z607]),(1,[z0,z325,z1,z2,z3,z5]),(1,[z0,z61,z2,z3,z52,z10]),(0,[z37,z13,z0,z1,z2,z3,z5]),(0,[z13,z0,z1,z2,z3,z5,z19]),(0,[z0,z604,z30,z1,z2,z3,z5]),(0,[z0,z1,z2,z3,z5,z19,z19]),(0,[z145,z0,z2,z3,z5,z10,z19])],[(1,[z0,z1,z2,z3,z5,z10]),(0,[z0,z295,z1,z68,z3,z5,z10]),(0,[z0,z1,z2,z3,z5,z10,z608]),(0,[z0,z1,z2,z3,z94,z5,z10])],[(0,[z83,z0,z1,z2,z7,z3,z5]),(0,[z0,z1,z2,z3,z5,z10,z609]),(0,[z0,z1,z2,z3,z52,z5,z10]),(1,[z0,z30,z1,z2,z3,z5]),(1,[z0,z1,z2,z3,z64,z19])],[(0,[z610,z0,z1,z2,z3,z5,z10]),(0,[z0,z1,z2,z3,z611,z5,z10]),(0,[z0,z1,z100,z2,z3,z5,z10]),(0,[z0,z30,z1,z264,z2,z3,z5]),(0,[z0,z30,z1,z2,z7,z3,z5]),(0,[z612,z0,z1,z2,z3,z5,z10]),(0,[z0,z1,z2,z84,z7,z3,z5])]],
   [[(0,[z613,z0,z1,z2,z3,z5,z10]),(0,[z13,z0,z1,z2,z3,z115,z5]),(0,[z0,z1,z2,z3,z614,z5,z10]),(0,[z0,z1,z139,z2,z84,z3,z5]),(0,[z40,z0,z1,z2,z5,z10,z34]),(0,[z0,z1,z2,z3,z5,z10,z615])],[(0,[z92,z51,z1,z2,z3,z5,z10]),(0,[z0,z1,z2,z616,z3,z5,z10]),(0,[z0,z1,z2,z3,z617,z5,z10]),(0,[z0,z1,z618,z2,z3,z5,z10]),(0,[z0,z61,z1,z2,z3,z42,z10]),(1,[z0,z1,z2,z399,z3,z5]),(1,[z13,z0,z1,z2,z3,z5]),(0,[z0,z1,z2,z300,z3,z5,z10]),(0,[z619,z0,z1,z2,z3,z5,z10]),(0,[z271,z0,z1,z2,z3,z5,z10]),(0,[z0,z1,z2,z620,z3,z5,z10]),(0,[z0,z1,z181,z2,z3,z5,z10])],[(0,[z0,z1,z2,z621,z3,z5,z10]),(0,[z0,z1,z2,z3,z87,z5,z10]),(0,[z0,z1,z622,z2,z3,z5,z10]),(0,[z0,z1,z2,z3,z5,z10,z623]),(0,[z0,z1,z2,z3,z624,z5,z10]),(0,[z13,z0,z2,z3,z21,z5,z10]),(0,[z0,z625,z1,z2,z3,z5,z10]),(0,[z0,z29,z61,z2,z3,z5,z10]),(0,[z0,z1,z2,z3,z5,z10,z112]),(0,[z12,z0,z1,z2,z3,z52,z10]),(0,[z12,z0,z2,z3,z5,z42,z10]),(0,[z13,z0,z1,z2,z392,z3,z5]),(0,[z86,z0,z1,z2,z3,z5,z240])],[(0,[z0,z1,z2,z3,z626,z5,z10]),(1,[z48,z8,z1,z3,z5,z10]),(0,[z12,z0,z1,z348,z3,z5,z10]),(0,[z0,z1,z2,z627,z3,z5,z10]),(0,[z0,z1,z139,z2,z3,z5,z19]),(0,[z0,z1,z275,z2,z3,z5,z19]),(0,[z113,z0,z1,z2,z3,z5,z19])],[(0,[z86,z9,z0,z1,z3,z5,z10]),(0,[z0,z628,z1,z2,z3,z5,z10]),(0,[z629,z0,z1,z2,z3,z5,z10]),(0,[z48,z0,z1,z2,z3,z5,z452]),(0,[z48,z26,z1,z2,z3,z5,z10]),(0,[z0,z1,z2,z3,z5,z96,z10]),(0,[z0,z1,z2,z3,z5,z330,z10]),(0,[z0,z1,z66,z70,z3,z5,z10])],[(0,[z48,z1,z2,z3,z87,z5,z10]),(0,[z0,z1,z2,z3,z5,z630,z10]),(0,[z0,z1,z2,z399,z3,z52,z5]),(0,[z0,z1,z2,z446,z7,z3,z5])],[(0,[z48,z8,z1,z2,z3,z5,z10]),(0,[z95,z0,z1,z2,z3,z5,z19]),(0,[z0,z1,z2,z3,z631,z5,z10]),(0,[z0,z1,z2,z3,z5,z362,z10])],[(0,[z0,z1,z2,z3,z632,z5,z10]),(0,[z218,z0,z61,z1,z2,z3,z5]),(0,[z0,z61,z1,z2,z7,z3,z5])]],
   [[(0,[z13,z26,z0,z1,z2,z3,z5]),(0,[z0,z1,z2,z3,z5,z633,z10]),(0,[z113,z0,z1,z2,z7,z3,z5])],[(0,[z634,z0,z1,z2,z3,z5,z10]),(0,[z0,z1,z2,z635,z3,z5,z10]),(1,[z0,z1,z2,z3,z5,z436]),(0,[z0,z1,z2,z3,z104,z5,z10])],[(0,[z0,z1,z2,z65,z3,z5,z10]),(0,[z95,z0,z1,z2,z3,z5,z267]),(0,[z636,z0,z1,z2,z3,z5,z10]),(0,[z0,z1,z2,z637,z3,z5,z10]),(0,[z0,z1,z2,z3,z5,z638,z10]),(0,[z0,z1,z2,z3,z5,z10,z179]),(0,[z0,z1,z639,z2,z3,z5,z10]),(0,[z0,z1,z139,z2,z3,z5,z47]),(0,[z640,z0,z1,z2,z3,z5,z10])],[(0,[z9,z1,z2,z3,z5,z108,z10]),(0,[z641,z0,z1,z2,z3,z5,z10]),(0,[z95,z0,z1,z2,z7,z3,z5]),(1,[z0,z1,z3,z5,z330,z10]),(0,[z0,z1,z2,z3,z5,z642,z10]),(0,[z0,z295,z1,z2,z3,z5,z19]),(0,[z378,z0,z1,z2,z3,z5,z10]),(0,[z643,z0,z1,z2,z3,z5,z10])],[(0,[z0,z1,z2,z644,z3,z5,z10]),(0,[z213,z0,z1,z2,z3,z5,z10]),(0,[z12,z0,z1,z2,z3,z5,z391]),(0,[z0,z30,z1,z2,z3,z5,z38]),(0,[z645,z0,z1,z2,z3,z5,z10])],[(0,[z0,z1,z2,z646,z3,z5,z10]),(0,[z0,z1,z133,z2,z7,z3,z5]),(0,[z0,z339,z1,z2,z3,z87,z5]),(0,[z213,z0,z30,z1,z2,z3,z5]),(0,[z215,z0,z1,z2,z3,z5,z10]),(1,[z215,z0,z2,z21,z5,z10]),(0,[z0,z2,z3,z21,z5,z22,z10]),(0,[z12,z0,z1,z2,z555,z5,z10]),(0,[z218,z0,z1,z2,z3,z5,z10]),(0,[z0,z1,z2,z3,z647,z5,z10]),(0,[z0,z1,z2,z7,z3,z5,z5])],[(0,[z0,z1,z2,z648,z3,z5,z10]),(0,[z26,z0,z1,z2,z3,z5,z19]),(0,[z0,z1,z2,z7,z27,z3,z5]),(0,[z215,z0,z30,z1,z2,z3,z5]),(0,[z649,z0,z1,z2,z3,z5,z10]),(0,[z0,z1,z650,z2,z3,z5,z10]),(0,[z86,z290,z1,z2,z3,z5,z10]),(0,[z0,z1,z2,z3,z651,z5,z10]),(0,[z652,z0,z1,z2,z3,z5,z10]),(0,[z0,z1,z2,z653,z3,z5,z10])],[(0,[z654,z0,z1,z2,z3,z5,z10]),(0,[z0,z30,z1,z2,z3,z52,z5]),(0,[z0,z1,z2,z655,z3,z5,z10]),(0,[z40,z0,z307,z2,z3,z5,z10]),(1,[z122,z0,z1,z2,z123,z5])]],
   [[(0,[z0,z29,z2,z68,z3,z5,z10]),(0,[z656,z0,z1,z2,z3,z5,z10]),(0,[z177,z0,z30,z1,z2,z3,z5]),(0,[z0,z657,z1,z2,z3,z5,z10]),(0,[z0,z1,z2,z3,z5,z10,z173]),(0,[z0,z1,z2,z3,z5,z231,z19])],[(0,[z132,z0,z1,z2,z3,z5,z10]),(1,[z0,z1,z2,z3,z5,z225]),(1,[z95,z1,z2,z87,z5,z10]),(0,[z51,z0,z1,z2,z7,z3,z5]),(0,[z13,z0,z1,z2,z3,z52,z5]),(0,[z13,z0,z1,z2,z3,z233,z5]),(0,[z218,z13,z0,z1,z2,z3,z5]),(0,[z0,z1,z2,z3,z14,z10,z34]),(0,[z658,z0,z1,z2,z3,z5,z10])],[(0,[z518,z0,z1,z2,z3,z5,z10]),(0,[z0,z1,z2,z232,z3,z5,z10]),(1,[z0,z1,z2,z3,z5,z585]),(0,[z0,z30,z1,z2,z3,z5,z22]),(0,[z0,z1,z2,z3,z5,z659,z10])],[(0,[z0,z0,z1,z2,z3,z5,z10]),(0,[z0,z1,z2,z3,z5,z660,z10]),(1,[z75,z1,z2,z3,z108,z10]),(1,[z0,z1,z2,z3,z5,z221]),(0,[z0,z1,z2,z154,z3,z5,z10]),(0,[z661,z0,z1,z2,z3,z5,z10]),(1,[z218,z0,z1,z2,z3,z5]),(0,[z0,z1,z2,z3,z52,z5,z585]),(1,[z13,z0,z2,z3,z5,z179]),(0,[z0,z1,z2,z3,z662,z5,z10]),(0,[z0,z1,z2,z3,z14,z5,z19]),(0,[z0,z663,z1,z2,z3,z5,z10])],[(0,[z664,z0,z1,z2,z3,z5,z10]),(0,[z665,z0,z1,z2,z3,z5,z10]),(0,[z26,z1,z2,z27,z3,z5,z10]),(0,[z0,z1,z2,z3,z5,z457,z10]),(0,[z0,z1,z2,z85,z20,z5,z10]),(0,[z0,z1,z2,z3,z5,z666,z10]),(0,[z667,z0,z1,z2,z3,z5,z10]),(0,[z0,z1,z2,z20,z3,z5,z10]),(0,[z122,z0,z434,z2,z3,z5,z10]),(0,[z0,z1,z2,z3,z5,z10,z234])],[(0,[z0,z1,z2,z3,z21,z5,z10]),(0,[z668,z0,z1,z2,z3,z5,z10]),(0,[z0,z1,z2,z7,z20,z3,z5]),(0,[z0,z1,z2,z669,z3,z5,z10])],[(0,[z92,z1,z2,z3,z5,z108,z10]),(0,[z48,z0,z1,z2,z3,z5,z10]),(0,[z1,z2,z65,z3,z87,z5,z10]),(0,[z670,z0,z1,z2,z3,z5,z10]),(0,[z0,z30,z2,z3,z5,z22,z10]),(0,[z40,z0,z1,z2,z20,z5,z10]),(0,[z246,z0,z1,z2,z3,z5,z10]),(0,[z0,z1,z2,z3,z671,z5,z10])],[(0,[z48,z0,z30,z1,z2,z3,z5]),(0,[z0,z1,z219,z2,z3,z5,z10]),(0,[z0,z1,z184,z2,z3,z5,z10]),(0,[z37,z0,z1,z66,z3,z5,z10]),(0,[z0,z1,z2,z3,z5,z10,z408]),(0,[z122,z0,z1,z2,z84,z5,z10]),(0,[z0,z672,z1,z2,z3,z5,z10])]],
   [[(0,[z9,z1,z2,z65,z3,z5,z10]),(0,[z0,z339,z1,z2,z3,z5,z10]),(0,[z0,z30,z1,z2,z3,z5,z108]),(0,[z119,z0,z1,z2,z84,z3,z5]),(0,[z69,z0,z2,z68,z3,z5,z10]),(0,[z0,z1,z66,z2,z3,z38,z10]),(1,[z40,z0,z1,z2,z10,z34]),(0,[z414,z0,z1,z2,z3,z5,z10])],[(1,[z0,z1,z2,z3,z5,z49]),(1,[z0,z350,z2,z3,z5,z10]),(0,[z0,z1,z252,z2,z3,z5,z10]),(0,[z0,z1,z2,z7,z3,z5,z110])],[(0,[z48,z9,z1,z2,z3,z5,z10]),(0,[z0,z1,z2,z3,z64,z5,z10]),(0,[z0,z1,z2,z3,z5,z10,z151])],[(0,[z673,z0,z1,z2,z3,z5,z10]),(0,[z0,z1,z2,z129,z3,z5,z10]),(0,[z0,z1,z2,z85,z3,z5,z10]),(0,[z674,z0,z1,z2,z3,z5,z10])],[(0,[z675,z0,z1,z2,z3,z5,z10]),(0,[z8,z0,z1,z3,z53,z5,z10]),(1,[z0,z295,z68,z3,z5,z10]),(0,[z13,z0,z1,z2,z3,z21,z5]),(0,[z676,z0,z1,z2,z3,z5,z10]),(0,[z37,z0,z1,z2,z3,z5,z513]),(0,[z0,z1,z2,z3,z5,z677,z10]),(0,[z0,z1,z2,z7,z3,z353,z5])],[(0,[z678,z0,z1,z2,z3,z5,z10]),(0,[z83,z0,z1,z2,z3,z5,z166]),(0,[z679,z0,z1,z2,z3,z5,z10]),(0,[z680,z0,z1,z2,z3,z5,z10]),(0,[z0,z1,z2,z3,z5,z10,z681])],[(0,[z0,z30,z1,z2,z3,z5,z166]),(0,[z0,z1,z682,z2,z3,z5,z10]),(1,[z13,z0,z29,z2,z3,z5]),(0,[z0,z1,z2,z3,z5,z683,z10]),(0,[z1,z2,z3,z14,z5,z72,z10])],[(0,[z0,z1,z2,z3,z684,z5,z10]),(0,[z0,z1,z2,z7,z3,z5,z47]),(0,[z0,z1,z2,z20,z104,z5,z10])]],
   [[(0,[z92,z0,z1,z2,z3,z5,z58]),(0,[z0,z1,z2,z685,z3,z5,z10]),(0,[z213,z69,z0,z1,z3,z5,z10]),(0,[z0,z1,z2,z3,z5,z686,z10]),(0,[z0,z30,z1,z2,z71,z3,z5]),(0,[z0,z1,z2,z7,z3,z53,z5]),(1,[z145,z0,z1,z2,z3,z5])],[(0,[z687,z0,z1,z2,z3,z5,z10]),(0,[z9,z0,z1,z2,z3,z5,z10]),(0,[z215,z0,z1,z2,z85,z5,z10]),(0,[z680,z13,z0,z1,z2,z3,z5]),(1,[z0,z1,z2,z3,z5,z513]),(1,[z191,z1,z2,z3,z5,z10])],[(0,[z9,z0,z30,z1,z2,z3,z5]),(0,[z75,z0,z1,z2,z3,z108,z10]),(0,[z119,z0,z1,z2,z3,z5,z47]),(1,[z0,z1,z2,z3,z5,z112]),(0,[z0,z688,z1,z2,z3,z5,z10]),(0,[z0,z1,z2,z689,z3,z5,z10])],[(0,[z690,z0,z1,z2,z3,z5,z10]),(0,[z691,z0,z1,z2,z3,z5,z10]),(0,[z0,z1,z3,z5,z47,z10,z189]),(0,[z0,z1,z2,z3,z5,z10,z692])],[(0,[z272,z0,z1,z2,z3,z5,z10]),(0,[z693,z0,z1,z2,z3,z5,z10]),(0,[z0,z1,z2,z3,z694,z5,z10]),(0,[z0,z1,z2,z3,z5,z10,z695]),(0,[z13,z0,z295,z1,z2,z3,z5]),(0,[z215,z0,z1,z2,z21,z5,z10]),(0,[z0,z1,z2,z3,z5,z10,z696])],[(0,[z0,z1,z2,z3,z5,z697,z10]),(0,[z12,z0,z1,z2,z3,z5,z10]),(0,[z272,z0,z30,z1,z2,z3,z5]),(0,[z0,z1,z66,z2,z3,z5,z10]),(0,[z0,z1,z2,z3,z698,z5,z10]),(0,[z0,z1,z699,z2,z3,z5,z10])],[(0,[z0,z1,z2,z3,z5,z700,z10]),(0,[z701,z0,z1,z2,z3,z5,z10]),(0,[z0,z1,z2,z702,z3,z5,z10]),(0,[z0,z1,z2,z3,z703,z5,z10]),(0,[z12,z0,z30,z1,z2,z3,z5]),(1,[z0,z1,z2,z20,z104,z10]),(0,[z0,z1,z2,z3,z583,z5,z10])],[(0,[z704,z0,z1,z2,z3,z5,z10]),(0,[z0,z382,z1,z2,z3,z5,z10]),(0,[z0,z1,z2,z3,z5,z705,z10]),(0,[z18,z0,z1,z2,z84,z3,z5]),(0,[z0,z1,z2,z3,z706,z5,z10]),(0,[z0,z1,z2,z3,z5,z10,z141]),(0,[z113,z0,z1,z2,z3,z64,z10])]]]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkB : List (List (List (ℕ × List W))) :=
  [[[(0,[z145,z0,z2,z3,z5,z42]),(0,[z0,z1,z707,z2,z3,z5]),(0,[z398,z1,z2,z3,z353,z5]),(0,[z0,z1,z181,z160,z3,z5])],[(0,[z0,z1,z2,z3,z5,z708]),(0,[z51,z1,z2,z3,z611,z10]),(0,[z0,z1,z2,z3,z5,z709]),(0,[z0,z434,z2,z7,z3,z5])],[(0,[z13,z9,z1,z65,z3,z5]),(0,[z0,z1,z2,z3,z5,z710]),(0,[z13,z0,z2,z3,z389,z5])],[(0,[z0,z1,z2,z711,z3,z5]),(1,[z0,z2,z712,z5,z10]),(0,[z13,z0,z2,z3,z614,z5]),(0,[z0,z1,z70,z3,z245,z10])],[(0,[z713,z1,z2,z3,z5,z10]),(0,[z13,z0,z2,z3,z5,z607]),(0,[z0,z1,z2,z3,z5,z714])],[(0,[z0,z1,z2,z10,z715,z34])],[(0,[z0,z1,z2,z716,z3,z5]),(0,[z12,z0,z2,z3,z717,z10]),(0,[z506,z0,z1,z2,z512,z5]),(0,[z0,z718,z1,z2,z3,z5]),(0,[z0,z1,z2,z7,z20,z104])],[(0,[z0,z1,z2,z719,z5,z10]),(0,[z12,z0,z348,z3,z42,z10])],[(0,[z0,z1,z720,z2,z3,z5]),(0,[z721,z0,z1,z3,z5,z10]),(0,[z0,z1,z2,z3,z5,z722]),(0,[z145,z215,z0,z2,z3,z5]),(0,[z1,z2,z7,z3,z136,z5]),(0,[z0,z1,z66,z409,z3,z14]),(0,[z723,z0,z1,z2,z3,z5]),(0,[z145,z0,z2,z3,z5,z34])],[(0,[z12,z13,z309,z2,z3,z5]),(0,[z0,z1,z2,z3,z5,z724]),(0,[z0,z725,z1,z2,z3,z5])],[(0,[z0,z1,z726,z3,z5,z10]),(0,[z145,z69,z0,z2,z3,z5]),(0,[z0,z2,z555,z5,z22,z10]),(0,[z0,z1,z2,z3,z508,z19])],[(0,[z26,z1,z2,z702,z5,z10])],[(0,[z0,z1,z727,z3,z5,z10]),(0,[z0,z728,z1,z2,z3,z5]),(0,[z0,z1,z2,z3,z5,z729])],[(0,[z0,z1,z2,z3,z5,z730]),(0,[z731,z1,z2,z3,z5,z10]),(0,[z0,z732,z1,z3,z5,z10]),(0,[z86,z0,z1,z98,z53,z5])],[(0,[z0,z1,z733,z3,z5,z10]),(0,[z0,z1,z734,z3,z5,z10]),(0,[z13,z0,z286,z2,z3,z5]),(0,[z0,z30,z168,z2,z3,z5]),(0,[z122,z0,z1,z2,z123,z5])],[(0,[z0,z1,z2,z3,z5,z735]),(0,[z119,z1,z2,z3,z5,z166]),(0,[z0,z736,z1,z2,z3,z5]),(0,[z0,z1,z180,z3,z5,z10]),(0,[z0,z1,z2,z737,z3,z5]),(0,[z271,z1,z66,z3,z14,z10]),(0,[z145,z113,z0,z2,z3,z5])]],
   [[(0,[z95,z1,z2,z87,z5,z10]),(0,[z12,z0,z2,z3,z42,z391]),(0,[z0,z1,z738,z2,z3,z5])],[(0,[z95,z1,z2,z626,z5,z10]),(0,[z0,z739,z2,z3,z5,z10]),(0,[z0,z1,z2,z3,z5,z740]),(0,[z12,z0,z2,z555,z42,z10]),(0,[z13,z0,z16,z2,z3,z5])],[(0,[z741,z0,z1,z3,z5,z10]),(0,[z0,z1,z2,z3,z5,z221]),(0,[z742,z0,z1,z2,z3,z5]),(0,[z218,z0,z1,z2,z3,z5]),(0,[z743,z1,z2,z3,z5,z10]),(0,[z1,z2,z3,z136,z5,z19])],[(0,[z13,z0,z32,z2,z3,z5]),(0,[z668,z0,z1,z2,z7,z3]),(0,[z40,z145,z0,z2,z3,z5])],[(0,[z9,z1,z65,z3,z5,z10]),(0,[z0,z1,z3,z744,z5,z10]),(0,[z0,z350,z449,z3,z5,z10]),(0,[z0,z1,z2,z745,z3,z5]),(0,[z122,z0,z1,z2,z694,z5]),(0,[z0,z1,z2,z3,z5,z746]),(0,[z0,z1,z2,z84,z233,z5]),(0,[z0,z1,z747,z3,z5,z10])],[(0,[z529,z1,z71,z3,z5,z10])],[(0,[z0,z1,z2,z3,z5,z748]),(0,[z0,z1,z2,z7,z3,z19])],[(0,[z749,z0,z1,z2,z3,z5]),(0,[z750,z0,z1,z2,z3,z5]),(0,[z213,z751,z0,z3,z5,z10]),(0,[z752,z1,z2,z3,z5,z10]),(0,[z0,z325,z2,z3,z5,z234])],[(0,[z0,z1,z2,z3,z5,z753]),(0,[z0,z1,z2,z3,z5,z754]),(0,[z0,z1,z2,z3,z5,z755]),(0,[z0,z1,z2,z3,z5,z756]),(0,[z40,z191,z1,z2,z10,z34])],[(0,[z0,z1,z2,z3,z757,z10]),(0,[z145,z213,z0,z2,z3,z5]),(0,[z13,z0,z2,z3,z5,z455])],[],[(0,[z0,z295,z68,z3,z5,z10])],[(0,[z0,z1,z2,z3,z5,z758]),(0,[z0,z1,z2,z3,z183,z96]),(0,[z0,z1,z2,z202,z123,z5]),(0,[z290,z1,z2,z3,z5,z240]),(0,[z0,z759,z2,z3,z5,z10])],[(0,[z191,z1,z99,z3,z5,z10])],[(0,[z0,z1,z2,z3,z5,z760]),(0,[z761,z0,z1,z2,z3,z5]),(0,[z0,z1,z2,z3,z5,z762]),(0,[z0,z39,z2,z20,z5,z10])],[(0,[z0,z1,z2,z3,z193,z96]),(0,[z145,z0,z1,z2,z3,z5])]],
   [[(0,[z73,z133,z2,z7,z3,z5]),(0,[z13,z73,z133,z2,z3,z5]),(0,[z0,z1,z3,z5,z330,z221]),(0,[z215,z0,z2,z7,z21,z5]),(0,[z0,z657,z30,z2,z3,z5]),(0,[z763,z1,z2,z3,z5,z10])],[(0,[z0,z1,z2,z3,z5,z764]),(0,[z0,z1,z2,z3,z5,z765]),(0,[z0,z766,z2,z3,z5,z10]),(0,[z0,z1,z2,z3,z103,z19]),(0,[z13,z290,z1,z2,z3,z5]),(0,[z767,z0,z1,z2,z3,z5])],[(0,[z51,z1,z2,z3,z197,z10]),(0,[z0,z1,z2,z768,z3,z5])],[(0,[z769,z0,z1,z3,z5,z10]),(0,[z769,z0,z30,z1,z3,z5]),(0,[z0,z365,z2,z3,z5,z22])],[(0,[z0,z1,z770,z2,z3,z5]),(0,[z282,z13,z0,z2,z3,z5]),(0,[z0,z2,z3,z5,z234,z585]),(0,[z0,z1,z2,z3,z245,z10])],[(0,[z0,z1,z2,z3,z771,z5]),(0,[z0,z1,z2,z3,z5,z772]),(0,[z0,z39,z2,z3,z5,z10]),(0,[z13,z0,z1,z2,z344,z5]),(0,[z86,z0,z1,z53,z245,z10]),(0,[z0,z1,z70,z773,z5,z10]),(0,[z0,z1,z2,z20,z104,z10])],[(0,[z0,z1,z774,z3,z5,z10]),(0,[z0,z1,z2,z3,z5,z775]),(0,[z0,z168,z2,z7,z3,z5]),(0,[z86,z0,z1,z185,z53,z5]),(0,[z0,z1,z2,z3,z776,z64])],[(0,[z0,z30,z1,z252,z3,z5]),(0,[z13,z0,z1,z66,z3,z14]),(0,[z271,z1,z3,z5,z38,z10]),(0,[z777,z1,z2,z3,z5,z10]),(0,[z0,z1,z778,z2,z3,z5])],[(0,[z0,z1,z779,z3,z5,z10]),(0,[z119,z57,z1,z2,z3,z5]),(0,[z0,z16,z2,z3,z5,z10]),(0,[z13,z1,z2,z3,z5,z72]),(0,[z0,z30,z400,z2,z3,z5]),(0,[z86,z145,z0,z2,z3,z5])],[(0,[z587,z8,z1,z3,z5,z10]),(0,[z0,z1,z2,z780,z3,z5])],[(0,[z0,z781,z1,z3,z5,z10]),(0,[z782,z0,z1,z3,z5,z19])],[(0,[z95,z30,z1,z2,z87,z5]),(0,[z0,z783,z2,z3,z5,z10]),(0,[z0,z29,z2,z416,z5,z10]),(0,[z12,z13,z0,z2,z3,z140])],[(0,[z0,z1,z2,z3,z5,z784]),(0,[z0,z1,z2,z20,z104,z141])],[(0,[z51,z1,z2,z3,z115,z19]),(0,[z0,z295,z154,z68,z3,z5]),(0,[z785,z1,z2,z3,z5,z10]),(1,[z12,z0,z2,z3,z140]),(0,[z30,z1,z2,z3,z136,z5]),(0,[z0,z1,z2,z84,z786,z5])],[(0,[z787,z0,z307,z2,z3,z5])],[(0,[z0,z1,z2,z788,z3,z5]),(0,[z0,z1,z3,z368,z5,z19]),(0,[z0,z30,z23,z2,z3,z5]),(0,[z0,z1,z2,z7,z3,z430]),(0,[z414,z0,z1,z3,z5,z189]),(0,[z40,z0,z1,z2,z238,z34])]],
   [[(0,[z0,z1,z2,z789,z3,z5]),(0,[z48,z222,z1,z3,z5,z10]),(0,[z0,z1,z2,z3,z5,z790]),(0,[z0,z1,z2,z3,z193,z791]),(0,[z0,z1,z792,z2,z3,z5]),(0,[z1,z793,z2,z3,z5,z10]),(0,[z0,z1,z2,z3,z5,z794]),(0,[z13,z0,z1,z2,z3,z795])],[(0,[z8,z529,z1,z3,z5,z10]),(0,[z0,z382,z2,z3,z5,z267]),(0,[z0,z1,z2,z3,z5,z796]),(0,[z797,z0,z1,z2,z3,z5]),(0,[z145,z0,z2,z3,z5,z179]),(0,[z0,z798,z2,z3,z5,z10]),(0,[z0,z1,z2,z3,z274,z19]),(0,[z0,z2,z799,z3,z5,z19])],[(0,[z73,z30,z133,z2,z3,z5]),(0,[z0,z382,z2,z7,z3,z5]),(0,[z145,z0,z2,z85,z3,z5]),(0,[z0,z2,z3,z717,z42,z10]),(0,[z145,z378,z0,z2,z3,z5])],[(0,[z191,z1,z180,z3,z5,z10]),(0,[z145,z0,z2,z800,z3,z5])],[(0,[z13,z801,z1,z2,z3,z5]),(0,[z0,z1,z70,z71,z5,z10]),(0,[z802,z1,z2,z3,z5,z10]),(0,[z102,z0,z1,z2,z123,z5]),(0,[z145,z0,z2,z3,z803,z5])],[(0,[z0,z1,z2,z3,z5,z804]),(0,[z0,z805,z2,z3,z5,z10]),(0,[z0,z1,z3,z5,z806,z10]),(0,[z0,z1,z2,z7,z3,z445]),(0,[z0,z2,z3,z5,z807,z19])],[(0,[z0,z30,z61,z2,z3,z52]),(0,[z0,z307,z2,z3,z5,z41])],[(0,[z111,z0,z30,z2,z3,z5]),(0,[z808,z1,z2,z3,z5,z10]),(0,[z0,z809,z2,z3,z5,z10]),(0,[z145,z0,z2,z3,z5,z173])],[(0,[z0,z1,z2,z3,z5,z810]),(0,[z366,z0,z1,z3,z5,z19]),(0,[z0,z1,z2,z3,z5,z811]),(0,[z145,z0,z139,z2,z3,z5])],[(0,[z92,z6,z2,z7,z3,z5]),(0,[z0,z1,z2,z3,z5,z812]),(0,[z13,z0,z395,z2,z3,z5]),(0,[z813,z0,z1,z2,z3,z5]),(0,[z13,z0,z2,z3,z248,z5]),(0,[z0,z30,z2,z562,z3,z5]),(0,[z145,z18,z0,z2,z3,z5]),(0,[z814,z1,z2,z3,z5,z10])],[(0,[z9,z222,z1,z3,z5,z10])],[],[(0,[z12,z13,z0,z348,z3,z5]),(0,[z0,z1,z2,z98,z3,z5]),(0,[z0,z815,z2,z3,z5,z10])],[(0,[z13,z137,z0,z2,z3,z5]),(0,[z13,z0,z184,z2,z3,z5]),(0,[z0,z1,z100,z2,z3,z5]),(0,[z0,z325,z1,z2,z3,z345]),(0,[z529,z1,z2,z7,z3,z5])],[(0,[z0,z1,z2,z3,z816,z10]),(0,[z0,z1,z2,z817,z3,z5]),(0,[z13,z0,z1,z411,z3,z5]),(0,[z222,z1,z70,z3,z5,z10]),(0,[z131,z1,z2,z3,z5,z187]),(0,[z145,z0,z2,z3,z5,z408])],[(0,[z145,z0,z2,z3,z104,z5])]],
   [[(0,[z13,z0,z2,z3,z5,z536])],[(0,[z0,z625,z68,z3,z5,z10]),(0,[z0,z1,z2,z3,z818,z5]),(0,[z767,z0,z2,z3,z104,z5])],[(0,[z0,z1,z2,z3,z5,z819]),(0,[z0,z1,z820,z3,z5,z10]),(0,[z0,z821,z2,z3,z5,z10]),(0,[z0,z1,z2,z3,z5,z238]),(0,[z0,z822,z1,z2,z3,z5])],[(0,[z0,z2,z3,z5,z10,z823])],[(0,[z309,z1,z2,z3,z5,z10]),(0,[z1,z449,z3,z87,z5,z10]),(0,[z824,z1,z2,z3,z5,z10]),(0,[z213,z69,z0,z3,z5,z19]),(0,[z658,z0,z1,z3,z5,z189]),(0,[z93,z307,z2,z3,z5,z10])],[(0,[z0,z1,z2,z3,z825,z10]),(0,[z826,z0,z1,z2,z3,z5]),(0,[z0,z30,z1,z2,z555,z5]),(0,[z0,z30,z1,z2,z827,z5])],[(0,[z0,z1,z828,z3,z5,z10]),(0,[z0,z1,z2,z3,z5,z829]),(0,[z0,z1,z2,z3,z5,z140]),(0,[z0,z1,z2,z773,z5,z10]),(0,[z145,z0,z2,z3,z5,z250])],[(0,[z0,z1,z2,z3,z5,z830]),(0,[z0,z1,z2,z3,z171,z19]),(0,[z13,z0,z2,z3,z52,z5]),(0,[z145,z0,z2,z3,z5,z10]),(0,[z13,z0,z365,z2,z3,z5]),(0,[z0,z30,z2,z3,z5,z22]),(0,[z1,z2,z7,z3,z5,z72])],[(0,[z0,z1,z2,z3,z5,z831]),(0,[z0,z832,z2,z3,z5,z10]),(0,[z0,z1,z2,z833,z5,z10]),(0,[z13,z0,z1,z834,z3,z5]),(0,[z40,z0,z30,z1,z2,z34]),(0,[z0,z1,z2,z835,z3,z5]),(0,[z145,z0,z2,z3,z64,z19])],[(0,[z0,z1,z2,z3,z5,z19]),(0,[z0,z1,z449,z3,z5,z267]),(0,[z75,z1,z2,z3,z108,z188]),(0,[z13,z0,z1,z180,z3,z5]),(0,[z191,z39,z2,z3,z5,z10]),(0,[z767,z0,z2,z3,z5,z10])],[(0,[z0,z1,z449,z7,z3,z5]),(0,[z0,z23,z2,z3,z245,z10])],[(0,[z13,z366,z0,z1,z3,z5]),(0,[z13,z0,z2,z20,z21,z5]),(0,[z218,z0,z61,z2,z3,z52]),(0,[z145,z0,z30,z2,z3,z5]),(0,[z0,z1,z99,z7,z3,z5]),(0,[z145,z0,z2,z3,z123,z5])],[(0,[z0,z1,z2,z344,z5,z10]),(0,[z0,z1,z2,z3,z5,z346]),(0,[z0,z1,z2,z3,z836,z10]),(0,[z0,z837,z2,z3,z5,z10])],[(0,[z0,z1,z2,z3,z5,z838]),(0,[z145,z9,z0,z2,z3,z5]),(0,[z0,z1,z2,z3,z839,z10]),(0,[z0,z1,z2,z840,z5,z10]),(0,[z12,z13,z0,z2,z3,z445]),(0,[z122,z0,z1,z2,z5,z362])],[(0,[z0,z1,z2,z3,z5,z273]),(0,[z0,z2,z3,z5,z10,z234]),(0,[z13,z0,z2,z3,z583,z5]),(0,[z0,z1,z2,z3,z351,z10]),(0,[z0,z1,z2,z3,z698,z19])],[(0,[z0,z1,z2,z3,z841,z10]),(0,[z48,z8,z1,z3,z5,z19]),(0,[z0,z1,z2,z3,z5,z842]),(0,[z843,z1,z2,z3,z5,z19])]],
   [[(0,[z844,z1,z2,z3,z5,z10]),(0,[z0,z1,z2,z845,z3,z5]),(0,[z0,z1,z2,z846,z3,z5]),(0,[z767,z0,z2,z3,z5,z141])],[(0,[z360,z1,z2,z3,z5,z10]),(0,[z0,z847,z1,z2,z3,z5]),(0,[z83,z412,z1,z2,z3,z5]),(0,[z848,z1,z2,z3,z5,z10]),(0,[z12,z0,z2,z3,z140,z10]),(0,[z0,z849,z2,z3,z5,z10])],[(0,[z12,z0,z100,z2,z3,z42]),(0,[z86,z13,z0,z1,z53,z5])],[(0,[z1,z2,z3,z479,z108,z10]),(0,[z0,z30,z1,z850,z3,z5]),(0,[z0,z30,z2,z3,z5,z161]),(0,[z0,z1,z2,z3,z327,z19])],[(0,[z0,z1,z184,z2,z3,z5])],[(0,[z0,z1,z2,z851,z5,z10]),(0,[z0,z1,z2,z185,z3,z5])],[(0,[z48,z1,z3,z5,z186,z10]),(0,[z26,z1,z2,z27,z5,z10]),(0,[z852,z0,z1,z2,z3,z5]),(0,[z86,z0,z1,z773,z5,z10])],[(0,[z0,z1,z2,z3,z5,z853]),(0,[z0,z1,z3,z5,z330,z19]),(0,[z0,z1,z2,z3,z5,z854]),(0,[z855,z30,z1,z2,z3,z5]),(0,[z856,z0,z1,z2,z3,z5])],[(0,[z51,z1,z2,z129,z3,z115]),(0,[z857,z1,z2,z3,z5,z10]),(0,[z0,z1,z2,z123,z786,z5])],[(0,[z366,z1,z27,z3,z5,z10]),(0,[z0,z30,z39,z2,z3,z5]),(0,[z858,z0,z2,z3,z5,z10])],[(0,[z26,z1,z2,z859,z5,z10]),(0,[z0,z1,z2,z3,z860,z5]),(0,[z0,z1,z2,z3,z5,z861])],[(0,[z44,z9,z1,z3,z5,z10]),(0,[z0,z1,z2,z3,z862,z5]),(0,[z0,z863,z2,z3,z5,z10])],[(0,[z0,z1,z864,z2,z3,z5]),(0,[z0,z1,z2,z3,z865,z10]),(0,[z0,z30,z2,z3,z5,z234]),(0,[z0,z2,z3,z5,z19,z866])],[],[(0,[z0,z1,z2,z3,z5,z867]),(0,[z0,z868,z2,z3,z5,z10]),(0,[z69,z751,z0,z3,z5,z10]),(0,[z0,z1,z869,z3,z5,z10]),(0,[z0,z168,z2,z3,z5,z240])],[(0,[z0,z1,z285,z2,z3,z5]),(0,[z0,z1,z2,z3,z870,z10]),(0,[z222,z1,z2,z3,z5,z10]),(0,[z1,z2,z3,z5,z871,z10]),(0,[z0,z1,z2,z3,z5,z15])]],
   [[(0,[z13,z0,z2,z3,z5,z195]),(0,[z0,z1,z2,z872,z3,z5]),(0,[z0,z30,z1,z2,z840,z5]),(0,[z0,z1,z3,z53,z245,z10]),(0,[z0,z873,z1,z2,z3,z5])],[(0,[z0,z30,z350,z2,z3,z5]),(0,[z95,z1,z2,z87,z5,z267]),(0,[z0,z1,z2,z3,z5,z874]),(0,[z86,z290,z1,z53,z5,z10]),(0,[z0,z1,z180,z7,z3,z5])],[],[(0,[z51,z1,z2,z7,z3,z115]),(0,[z0,z2,z3,z712,z5,z10]),(0,[z0,z365,z61,z2,z3,z5]),(0,[z93,z1,z2,z3,z5,z41])],[(0,[z0,z1,z875,z3,z5,z10]),(0,[z0,z382,z2,z3,z5,z96]),(0,[z0,z1,z411,z3,z5,z10])],[(0,[z0,z350,z2,z3,z5,z19])],[(0,[z876,z0,z1,z2,z3,z5]),(0,[z9,z1,z65,z7,z3,z5]),(0,[z0,z1,z2,z3,z239,z5]),(0,[z0,z2,z3,z5,z10,z877]),(0,[z191,z1,z2,z3,z5,z238])],[(0,[z0,z1,z2,z3,z5,z878]),(0,[z12,z0,z1,z2,z3,z63])],[(0,[z0,z1,z2,z879,z3,z5]),(0,[z0,z1,z3,z5,z10,z880])],[(0,[z881,z0,z1,z2,z3,z10]),(0,[z145,z0,z2,z3,z5,z22])],[(0,[z882,z0,z1,z2,z3,z5]),(0,[z0,z1,z2,z3,z5,z883]),(0,[z0,z325,z1,z2,z3,z63]),(0,[z0,z1,z66,z3,z884,z10]),(0,[z0,z2,z3,z5,z19,z885]),(0,[z0,z863,z2,z7,z3,z5])],[],[(0,[z0,z1,z2,z3,z886,z5]),(0,[z0,z1,z2,z3,z5,z887])],[(0,[z0,z295,z68,z7,z3,z5]),(0,[z888,z1,z2,z3,z5,z10]),(0,[z191,z1,z2,z3,z5,z19])],[(0,[z889,z1,z2,z3,z5,z10])],[(0,[z145,z0,z2,z3,z5,z108]),(0,[z0,z1,z2,z3,z5,z890]),(0,[z0,z1,z2,z3,z5,z891]),(0,[z0,z30,z307,z2,z3,z5]),(0,[z0,z1,z2,z106,z20,z104])]],
   [[(0,[z0,z2,z892,z3,z5,z10]),(0,[z893,z0,z1,z2,z3,z5]),(0,[z894,z1,z2,z3,z5,z10]),(0,[z0,z1,z2,z3,z5,z895]),(0,[z0,z1,z71,z773,z5,z10]),(0,[z0,z386,z434,z2,z3,z5])],[(0,[z0,z1,z2,z3,z297,z19])],[(0,[z0,z896,z307,z2,z3,z5])],[(0,[z0,z1,z2,z7,z344,z5]),(0,[z0,z2,z3,z5,z717,z10]),(0,[z40,z0,z39,z2,z10,z34]),(0,[z0,z1,z2,z897,z3,z5])],[(0,[z0,z1,z2,z3,z5,z898]),(0,[z0,z1,z2,z3,z5,z899]),(0,[z13,z731,z1,z2,z3,z5]),(0,[z0,z30,z2,z3,z5,z877])],[(0,[z145,z0,z2,z3,z5,z166]),(0,[z37,z0,z1,z3,z38,z513]),(0,[z0,z900,z2,z3,z5,z19]),(0,[z113,z0,z1,z2,z3,z776])],[(0,[z145,z0,z325,z2,z3,z5])],[(0,[z0,z1,z2,z3,z5,z195]),(0,[z0,z1,z66,z3,z14,z10]),(0,[z0,z39,z2,z7,z3,z5]),(0,[z0,z1,z2,z3,z786,z5])],[(0,[z0,z1,z2,z901,z3,z5]),(0,[z801,z1,z2,z3,z5,z10])],[(0,[z474,z1,z2,z3,z115,z10]),(0,[z0,z1,z902,z3,z5,z10]),(0,[z0,z1,z2,z3,z5,z903]),(0,[z904,z0,z1,z2,z3,z5])],[(0,[z0,z2,z3,z21,z4,z5]),(0,[z0,z1,z3,z5,z10,z905]),(0,[z12,z0,z1,z2,z3,z140]),(0,[z0,z2,z3,z5,z22,z585]),(0,[z13,z529,z1,z2,z3,z5]),(0,[z0,z906,z1,z2,z3,z5]),(0,[z37,z145,z0,z2,z3,z5]),(0,[z0,z16,z2,z7,z3,z5])],[(0,[z145,z0,z2,z68,z3,z5]),(0,[z907,z1,z2,z3,z5,z10]),(0,[z12,z0,z2,z3,z239,z42]),(0,[z0,z1,z2,z3,z5,z908])],[(0,[z0,z350,z219,z3,z5,z10]),(0,[z0,z382,z2,z3,z183,z10]),(0,[z0,z1,z449,z3,z5,z96]),(0,[z95,z13,z1,z2,z87,z5])],[(0,[z0,z184,z16,z2,z3,z5]),(0,[z0,z1,z2,z3,z5,z909])],[(0,[z1,z2,z27,z25,z5,z10]),(0,[z0,z1,z910,z2,z3,z5]),(0,[z0,z1,z2,z3,z324,z19]),(0,[z911,z0,z1,z3,z5,z10]),(0,[z0,z1,z348,z3,z5,z391]),(0,[z911,z0,z30,z1,z3,z5]),(0,[z0,z1,z2,z3,z776,z19]),(0,[z145,z0,z2,z3,z5,z234])],[(0,[z0,z382,z2,z3,z193,z10]),(0,[z0,z2,z21,z5,z171,z10]),(0,[z215,z0,z2,z153,z21,z5]),(0,[z13,z215,z0,z2,z21,z5]),(0,[z0,z1,z348,z555,z5,z10]),(0,[z0,z1,z2,z3,z5,z912])]],
   [[(0,[z0,z1,z3,z128,z38,z10]),(0,[z213,z69,z0,z30,z3,z5]),(0,[z0,z913,z1,z2,z3,z5]),(0,[z914,z145,z0,z2,z3,z5])],[(0,[z0,z915,z2,z3,z5,z10]),(0,[z0,z1,z2,z916,z3,z5]),(0,[z77,z0,z29,z2,z3,z5]),(0,[z1,z2,z3,z5,z72,z19]),(0,[z246,z329,z0,z1,z2,z5])],[(0,[z371,z0,z2,z21,z5,z10]),(0,[z0,z2,z3,z52,z5,z140])],[(0,[z13,z0,z1,z70,z71,z5]),(0,[z0,z1,z2,z35,z5,z173])],[(0,[z0,z736,z23,z2,z3,z5])],[(0,[z0,z1,z2,z3,z5,z917]),(0,[z1,z2,z3,z5,z10,z918]),(0,[z222,z23,z2,z3,z5,z10]),(0,[z919,z0,z1,z2,z3,z5])],[(0,[z0,z920,z1,z2,z3,z5]),(0,[z0,z1,z2,z3,z921,z5]),(0,[z13,z0,z1,z922,z3,z5]),(0,[z0,z923,z1,z2,z3,z5]),(0,[z0,z1,z2,z3,z5,z924])],[],[(0,[z1,z65,z3,z626,z5,z10]),(0,[z925,z0,z2,z3,z5,z10]),(0,[z0,z1,z2,z555,z5,z391]),(0,[z926,z0,z2,z3,z5,z19])],[(0,[z0,z1,z2,z3,z5,z927]),(0,[z26,z1,z2,z3,z193,z10]),(0,[z928,z0,z1,z2,z3,z5]),(0,[z0,z1,z929,z2,z3,z5]),(0,[z40,z0,z307,z2,z10,z34])],[(0,[z1,z2,z3,z87,z193,z10]),(0,[z113,z0,z1,z2,z3,z63]),(0,[z37,z0,z1,z7,z3,z38]),(0,[z145,z0,z2,z3,z5,z362]),(0,[z0,z1,z2,z35,z5,z408])],[(0,[z18,z0,z1,z3,z5,z623]),(0,[z12,z13,z0,z2,z344,z5]),(0,[z13,z0,z1,z930,z3,z5]),(0,[z0,z1,z2,z931,z3,z351]),(0,[z0,z1,z2,z3,z5,z932]),(0,[z145,z0,z2,z933,z3,z5])],[(0,[z0,z1,z934,z3,z5,z10]),(0,[z145,z0,z66,z2,z3,z5])],[(0,[z0,z935,z1,z2,z3,z5]),(0,[z86,z0,z1,z53,z5,z19])],[(0,[z0,z30,z1,z219,z3,z5]),(0,[z119,z1,z2,z3,z5,z499])],[(0,[z6,z936,z2,z3,z5,z10]),(0,[z0,z1,z2,z937,z3,z5]),(0,[z0,z1,z2,z3,z938,z10]),(0,[z13,z247,z0,z2,z3,z5]),(0,[z0,z1,z252,z3,z5,z221])]],
   [[(0,[z0,z1,z2,z3,z939,z10]),(0,[z0,z30,z1,z348,z3,z5]),(0,[z86,z0,z1,z53,z5,z346])],[(0,[z0,z1,z2,z3,z940,z10]),(0,[z941,z9,z1,z3,z5,z10]),(0,[z9,z1,z322,z3,z5,z10]),(0,[z0,z1,z3,z773,z5,z10]),(0,[z0,z2,z7,z3,z234,z19])],[(0,[z119,z0,z434,z2,z3,z5]),(0,[z0,z29,z2,z712,z5,z10]),(0,[z86,z0,z1,z53,z351,z10]),(0,[z942,z1,z2,z3,z5,z10])],[(0,[z0,z1,z2,z3,z5,z943]),(0,[z944,z0,z1,z2,z3,z5]),(0,[z8,z1,z3,z5,z383,z10]),(0,[z0,z61,z2,z3,z427,z10]),(0,[z945,z0,z1,z2,z3,z5]),(0,[z13,z0,z1,z99,z3,z5]),(0,[z290,z30,z1,z2,z3,z5]),(0,[z1,z66,z3,z14,z72,z10])],[(0,[z271,z1,z2,z3,z5,z10]),(0,[z8,z941,z1,z3,z5,z10]),(0,[z0,z1,z449,z3,z183,z10]),(0,[z95,z1,z2,z87,z5,z96]),(0,[z946,z1,z2,z3,z5,z10]),(0,[z218,z0,z1,z2,z3,z140])],[(0,[z0,z1,z2,z3,z5,z947]),(0,[z13,z0,z2,z3,z21,z5]),(0,[z13,z0,z2,z3,z230,z5]),(0,[z0,z1,z948,z2,z3,z5]),(0,[z13,z0,z1,z2,z3,z245]),(0,[z0,z1,z139,z3,z5,z949]),(0,[z145,z0,z275,z2,z3,z5])],[(0,[z0,z1,z3,z950,z5,z10]),(0,[z0,z1,z2,z3,z5,z951]),(0,[z309,z1,z2,z7,z3,z5]),(0,[z93,z30,z1,z2,z3,z5]),(0,[z0,z1,z3,z201,z38,z10])],[(0,[z0,z1,z449,z3,z193,z10]),(0,[z0,z1,z2,z7,z3,z642]),(0,[z1,z2,z3,z5,z72,z15]),(0,[z0,z1,z2,z104,z10,z715]),(1,[z0,z1,z2,z786,z5])],[(0,[z145,z0,z2,z3,z115,z5]),(0,[z0,z952,z1,z2,z3,z5]),(0,[z0,z1,z2,z7,z3,z227])],[(0,[z0,z953,z2,z3,z5,z10]),(0,[z0,z1,z2,z954,z3,z5]),(0,[z0,z1,z2,z620,z104,z10]),(0,[z145,z0,z2,z7,z3,z5])],[(0,[z1,z2,z3,z859,z5,z10]),(0,[z12,z13,z0,z2,z3,z42])],[(0,[z0,z1,z2,z3,z5,z955]),(0,[z0,z1,z2,z3,z5,z956]),(0,[z0,z30,z1,z2,z3,z351]),(0,[z222,z1,z3,z53,z5,z10]),(0,[z0,z957,z1,z2,z3,z5]),(1,[z0,z1,z3,z5,z949])],[(0,[z0,z1,z2,z3,z958,z5]),(0,[z215,z0,z2,z21,z5,z19]),(0,[z0,z1,z181,z3,z5,z47])],[(0,[z51,z1,z2,z3,z115,z10])],[],[(0,[z9,z1,z2,z3,z193,z10]),(0,[z0,z1,z3,z368,z5,z10]),(0,[z0,z1,z2,z3,z5,z959]),(0,[z442,z0,z2,z3,z42,z10]),(0,[z442,z0,z1,z2,z10,z34]),(0,[z0,z1,z2,z3,z614,z19])]],
   [[(0,[z0,z960,z2,z3,z5,z10]),(0,[z0,z1,z3,z330,z10,z34]),(0,[z0,z29,z2,z85,z5,z112]),(0,[z357,z1,z2,z256,z3,z5])],[(0,[z0,z1,z2,z3,z5,z961]),(0,[z13,z0,z1,z2,z3,z183]),(0,[z0,z1,z2,z3,z5,z962])],[(0,[z963,z1,z2,z3,z5,z10]),(0,[z0,z1,z2,z84,z5,z173])],[(0,[z0,z1,z219,z3,z5,z10]),(0,[z0,z964,z1,z2,z3,z5]),(0,[z360,z1,z2,z7,z3,z5]),(0,[z965,z145,z0,z2,z3,z5]),(0,[z0,z849,z2,z7,z3,z5])],[(0,[z12,z0,z2,z3,z42,z195])],[(0,[z26,z30,z1,z2,z27,z5]),(0,[z966,z0,z1,z3,z5,z10]),(0,[z0,z1,z2,z967,z3,z5])],[(0,[z48,z0,z1,z3,z245,z10]),(1,[z145,z0,z2,z3,z5]),(0,[z968,z30,z1,z2,z3,z5])],[(0,[z0,z1,z3,z5,z969,z10]),(0,[z0,z1,z2,z3,z345,z19])],[(0,[z366,z0,z30,z1,z3,z5]),(0,[z0,z1,z70,z494,z5,z10]),(0,[z970,z1,z2,z3,z5,z10]),(0,[z0,z307,z99,z3,z5,z10]),(0,[z971,z1,z2,z3,z5,z10])],[(0,[z0,z1,z2,z3,z5,z972]),(0,[z82,z1,z2,z87,z5,z10]),(0,[z0,z1,z2,z973,z3,z5]),(0,[z122,z0,z1,z2,z237,z5]),(1,[z767,z0,z2,z3,z5])],[(0,[z0,z1,z2,z3,z5,z974]),(0,[z0,z1,z2,z3,z5,z975]),(0,[z0,z1,z2,z976,z3,z5])],[(0,[z132,z0,z29,z2,z3,z5]),(0,[z0,z1,z2,z3,z977,z10]),(0,[z597,z1,z2,z3,z108,z10]),(0,[z0,z295,z30,z68,z3,z5]),(0,[z0,z29,z2,z637,z5,z10]),(0,[z13,z507,z0,z2,z3,z5])],[(0,[z95,z1,z2,z87,z183,z10]),(0,[z0,z1,z2,z978,z3,z5]),(0,[z979,z0,z2,z3,z5,z19])],[(0,[z290,z168,z2,z3,z5,z10]),(0,[z980,z145,z0,z2,z3,z5])],[(0,[z145,z83,z0,z2,z3,z5]),(0,[z484,z1,z2,z3,z5,z110]),(0,[z0,z1,z2,z3,z245,z240])],[(0,[z145,z92,z0,z2,z3,z5]),(0,[z95,z1,z2,z87,z193,z10]),(0,[z0,z1,z7,z3,z368,z5]),(0,[z30,z1,z2,z3,z5,z72]),(0,[z0,z981,z1,z2,z3,z5])]],
   [[(0,[z9,z0,z1,z3,z245,z10]),(0,[z145,z8,z0,z2,z3,z5]),(0,[z95,z145,z0,z2,z3,z5]),(0,[z0,z1,z2,z3,z5,z982])],[(0,[z13,z0,z1,z2,z3,z193]),(0,[z222,z1,z2,z7,z3,z5])],[(0,[z0,z1,z2,z3,z5,z983]),(0,[z0,z1,z219,z7,z3,z5]),(0,[z0,z1,z2,z984,z3,z5]),(0,[z0,z23,z2,z3,z5,z19])],[(0,[z13,z145,z0,z2,z3,z5]),(0,[z985,z1,z2,z3,z5,z10])],[(0,[z0,z986,z2,z3,z5,z10]),(0,[z0,z2,z3,z5,z10,z987]),(0,[z213,z69,z0,z3,z5,z10]),(0,[z13,z0,z2,z3,z5,z988]),(0,[z0,z2,z3,z5,z22,z877])],[(1,[z1,z2,z859,z5,z10]),(0,[z989,z0,z1,z2,z3,z10]),(0,[z0,z30,z1,z2,z20,z104]),(0,[z0,z23,z2,z3,z5,z346]),(0,[z1,z2,z3,z990,z5,z10])],[(0,[z0,z1,z2,z3,z5,z457]),(0,[z991,z0,z1,z2,z3,z5]),(0,[z0,z1,z411,z7,z3,z5]),(0,[z992,z0,z1,z3,z5,z10])],[(0,[z0,z1,z2,z3,z5,z993]),(0,[z0,z1,z2,z3,z5,z994]),(0,[z0,z1,z2,z3,z64,z140]),(0,[z0,z23,z2,z3,z351,z10])],[(0,[z0,z1,z2,z3,z5,z995]),(0,[z13,z0,z1,z3,z368,z5]),(0,[z0,z1,z996,z3,z5,z10]),(0,[z0,z997,z1,z2,z3,z5])],[(0,[z0,z1,z2,z998,z3,z5]),(0,[z12,z0,z2,z3,z42,z19]),(0,[z0,z1,z2,z999,z3,z5])],[(0,[z13,z0,z36,z2,z3,z5]),(0,[z1000,z1,z2,z3,z5,z10]),(0,[z86,z529,z1,z53,z5,z10]),(0,[z0,z365,z2,z232,z3,z5])],[(0,[z0,z1001,z382,z2,z3,z5]),(1,[z1,z2,z3,z1002,z10]),(0,[z487,z13,z0,z2,z3,z5]),(0,[z1003,z0,z1,z2,z3,z5])],[(0,[z1,z2,z3,z1004,z5,z10]),(0,[z12,z0,z2,z344,z42,z10]),(0,[z0,z1005,z2,z3,z5,z10])],[(0,[z13,z0,z1,z2,z3,z5]),(0,[z13,z0,z1,z2,z1006,z5]),(0,[z487,z145,z0,z2,z3,z5])],[(0,[z0,z1,z2,z3,z1007,z5]),(0,[z177,z448,z1,z2,z3,z5]),(0,[z0,z307,z180,z3,z5,z10])],[(0,[z48,z8,z1,z3,z5,z10]),(0,[z48,z8,z30,z1,z3,z5]),(0,[z1008,z0,z382,z2,z3,z5]),(0,[z95,z1,z2,z859,z5,z10]),(0,[z0,z1,z139,z669,z3,z5]),(0,[z843,z1,z2,z3,z5,z10])]],
   [[(0,[z0,z1,z2,z3,z5,z1009]),(0,[z0,z1,z3,z104,z330,z10]),(0,[z213,z69,z0,z3,z5,z436]),(0,[z581,z69,z0,z3,z5,z10]),(0,[z13,z0,z434,z2,z3,z5])],[(0,[z0,z1,z2,z3,z5,z1010]),(0,[z0,z1,z2,z3,z1011,z5]),(0,[z0,z1,z139,z3,z5,z151])],[(0,[z0,z1,z2,z3,z1012,z5]),(0,[z1013,z1,z2,z3,z5,z10]),(0,[z0,z1,z3,z5,z949,z189])],[],[(0,[z62,z0,z1,z2,z202,z5])],[(0,[z1,z2,z3,z136,z5,z10]),(0,[z0,z1,z2,z3,z5,z436]),(0,[z0,z39,z2,z5,z10,z34])],[(0,[z440,z0,z2,z21,z5,z10]),(0,[z0,z1,z2,z3,z5,z1014]),(0,[z0,z1,z252,z3,z5,z19]),(0,[z83,z0,z434,z2,z3,z5]),(0,[z0,z29,z2,z202,z5,z10]),(0,[z13,z360,z1,z2,z3,z5]),(0,[z531,z0,z1,z3,z38,z10])],[(0,[z0,z1,z2,z3,z5,z1015]),(0,[z1016,z1,z2,z3,z5,z10]),(0,[z0,z1,z99,z3,z5,z41])],[(0,[z0,z1,z2,z3,z5,z1017])],[(0,[z0,z30,z382,z2,z3,z5]),(0,[z0,z1,z3,z5,z1018,z10]),(0,[z0,z1,z2,z3,z5,z1019]),(0,[z86,z529,z1,z3,z5,z10]),(0,[z1020,z1,z2,z3,z5,z10])],[(0,[z48,z1,z3,z493,z5,z10]),(0,[z0,z1,z1021,z2,z3,z5])],[(0,[z0,z1,z1022,z3,z5,z10]),(0,[z0,z1,z2,z3,z5,z988])],[(0,[z0,z1,z2,z1023,z3,z5]),(0,[z0,z1,z2,z3,z5,z1024]),(0,[z13,z0,z2,z3,z5,z592]),(0,[z0,z1,z2,z7,z3,z692]),(0,[z145,z0,z2,z3,z5,z5])],[(0,[z145,z0,z2,z27,z3,z5]),(0,[z0,z1,z2,z7,z3,z695]),(0,[z86,z0,z30,z1,z53,z5]),(0,[z0,z1025,z2,z3,z5,z10]),(0,[z0,z2,z3,z5,z10,z866]),(0,[z1026,z145,z0,z2,z3,z5])],[(0,[z0,z1,z2,z3,z5,z1027]),(0,[z0,z1,z2,z3,z5,z1028]),(0,[z0,z1,z2,z3,z5,z585]),(0,[z13,z0,z168,z2,z3,z5]),(0,[z1029,z1,z2,z3,z5,z10]),(0,[z145,z0,z1030,z2,z3,z5])],[(0,[z0,z1,z2,z3,z5,z1031])]],
   [[(0,[z1032,z1,z2,z3,z5,z10]),(0,[z130,z0,z1,z3,z94,z5])],[(0,[z0,z1,z2,z3,z5,z1033]),(0,[z0,z1,z2,z3,z1034,z10]),(0,[z1,z2,z3,z5,z1035,z10])],[(0,[z0,z1,z1036,z3,z5,z10]),(0,[z12,z13,z0,z2,z3,z52]),(0,[z0,z1,z3,z1037,z5,z10])],[(0,[z0,z1,z2,z3,z1038,z10])],[(0,[z12,z0,z411,z3,z42,z10])],[(0,[z0,z350,z2,z3,z5,z10]),(0,[z0,z1,z2,z3,z5,z1039]),(0,[z0,z1,z2,z3,z5,z49]),(0,[z751,z0,z295,z3,z5,z10]),(0,[z0,z29,z30,z2,z85,z5]),(0,[z13,z1040,z1,z2,z3,z5]),(0,[z93,z1,z99,z3,z5,z10]),(0,[z40,z93,z1,z2,z10,z34])],[(0,[z51,z1,z3,z115,z330,z10]),(0,[z0,z1,z2,z3,z5,z1041])],[(0,[z1,z1042,z2,z3,z5,z10])],[(0,[z0,z1,z1043,z2,z3,z5]),(1,[z751,z0,z3,z5,z10]),(0,[z0,z1,z2,z3,z351,z240])],[(0,[z0,z1,z1044,z2,z3,z5]),(0,[z0,z1045,z2,z3,z5,z10])],[(0,[z0,z1,z2,z3,z1046,z5])],[(0,[z1047,z0,z1,z2,z3,z5]),(0,[z48,z8,z1,z3,z5,z49]),(0,[z0,z1,z2,z3,z5,z1048]),(0,[z0,z1,z3,z5,z47,z949]),(0,[z0,z2,z3,z5,z10,z885])],[(0,[z0,z1,z2,z3,z5,z1049]),(0,[z9,z1,z510,z3,z5,z10]),(0,[z0,z382,z449,z3,z5,z10]),(0,[z442,z13,z0,z2,z3,z5]),(0,[z0,z61,z2,z7,z3,z52])],[(0,[z191,z1,z2,z3,z5,z10]),(0,[z1050,z1,z2,z3,z5,z10]),(0,[z0,z1,z180,z3,z5,z41]),(0,[z782,z0,z1,z3,z5,z10])],[],[(0,[z1051,z1,z2,z3,z5,z10])]],
   [[(0,[z503,z1,z2,z3,z5,z166]),(0,[z1052,z1,z2,z3,z5,z10])],[(0,[z0,z1,z1053,z3,z5,z10]),(0,[z0,z1,z2,z1054,z3,z193]),(0,[z0,z2,z3,z5,z10,z807]),(0,[z0,z1,z1055,z3,z5,z10]),(0,[z37,z0,z1,z3,z38,z19]),(0,[z0,z1,z2,z5,z10,z715])],[(0,[z9,z30,z1,z65,z3,z5]),(0,[z13,z0,z1,z449,z3,z5]),(0,[z0,z1,z2,z3,z717,z10]),(0,[z0,z1,z66,z3,z89,z10])],[(0,[z0,z1,z2,z3,z5,z1056]),(0,[z119,z1,z2,z3,z5,z1057]),(0,[z13,z0,z2,z3,z1058,z5]),(0,[z13,z0,z2,z3,z298,z5])],[(0,[z0,z1,z2,z1059,z3,z5]),(0,[z0,z1,z2,z1060,z3,z5]),(0,[z0,z1,z219,z3,z5,z96]),(0,[z0,z1061,z1,z2,z3,z5]),(0,[z0,z1,z7,z3,z5,z330]),(0,[z0,z2,z799,z3,z5,z10])],[(0,[z0,z1,z2,z3,z5,z1062]),(0,[z0,z900,z2,z3,z5,z10])],[(0,[z26,z1,z449,z3,z5,z10]),(0,[z1,z2,z3,z1002,z108,z10]),(0,[z0,z1,z2,z3,z5,z492]),(0,[z271,z1,z2,z7,z3,z5]),(0,[z109,z1,z2,z3,z5,z231])],[(0,[z529,z1,z449,z3,z5,z10]),(0,[z12,z13,z0,z411,z3,z5]),(0,[z134,z503,z1,z2,z3,z5]),(0,[z363,z0,z1,z53,z5,z10])],[(0,[z44,z0,z1,z53,z5,z10]),(0,[z0,z1,z1063,z3,z5,z10]),(0,[z751,z0,z2,z3,z5,z10]),(0,[z13,z309,z1,z2,z3,z5])],[(0,[z83,z1,z2,z3,z5,z110]),(0,[z13,z0,z30,z2,z3,z5]),(0,[z222,z1,z2,z3,z5,z240])],[(0,[z1064,z0,z1,z2,z3,z5]),(0,[z1,z2,z3,z104,z72,z10])],[(0,[z366,z0,z1,z3,z5,z10]),(0,[z0,z1065,z2,z3,z5,z10]),(0,[z0,z1,z2,z3,z5,z1066]),(0,[z1067,z0,z1,z2,z3,z5]),(0,[z0,z1,z3,z5,z884,z10]),(0,[z93,z1,z180,z3,z5,z10]),(0,[z145,z131,z0,z2,z3,z5])],[(0,[z1068,z0,z1,z2,z3,z5]),(0,[z0,z1069,z2,z3,z5,z10]),(0,[z13,z0,z386,z2,z3,z5]),(1,[z13,z0,z2,z555,z5]),(0,[z145,z0,z61,z2,z3,z5]),(0,[z529,z30,z1,z2,z3,z5])],[(0,[z127,z1,z65,z3,z5,z10]),(0,[z13,z0,z1,z3,z5,z330])],[(0,[z0,z1070,z2,z3,z5,z10]),(0,[z0,z1,z2,z3,z140,z34]),(0,[z1071,z1,z2,z3,z5,z10]),(0,[z1072,z0,z1,z2,z3,z5])],[(0,[z12,z360,z2,z3,z42,z10])]],
   [[(0,[z0,z1,z2,z3,z5,z58]),(0,[z1073,z0,z1,z2,z3,z5]),(0,[z0,z1,z2,z827,z5,z10]),(0,[z0,z1074,z2,z3,z5,z10]),(0,[z40,z0,z1,z2,z7,z34]),(0,[z1075,z0,z1,z2,z3,z5])],[(0,[z132,z73,z133,z2,z3,z5]),(0,[z1,z2,z3,z5,z72,z10]),(0,[z0,z307,z2,z3,z5,z238])],[(0,[z0,z1,z2,z3,z5,z1076]),(0,[z199,z0,z2,z21,z5,z10]),(0,[z381,z0,z1,z2,z7,z3])],[(0,[z0,z1,z2,z3,z5,z1077]),(0,[z0,z1,z2,z3,z706,z19]),(0,[z0,z39,z2,z3,z5,z41])],[(0,[z95,z382,z2,z87,z5,z10]),(0,[z0,z1,z219,z3,z5,z267]),(0,[z0,z1,z2,z3,z1078,z5]),(0,[z0,z29,z2,z3,z5,z140]),(0,[z0,z1,z3,z5,z10,z949])],[(0,[z1079,z0,z1,z2,z3,z5])],[(0,[z0,z1,z2,z3,z5,z1080])],[(0,[z0,z30,z527,z2,z3,z5]),(0,[z0,z1,z2,z3,z5,z1081]),(0,[z0,z1,z1082,z3,z5,z10])],[(0,[z0,z1083,z2,z3,z5,z10]),(0,[z926,z0,z2,z3,z5,z10]),(0,[z0,z1,z2,z1084,z3,z5]),(0,[z0,z307,z2,z3,z5,z19])],[(0,[z1085,z1,z2,z3,z5,z10]),(0,[z145,z0,z29,z2,z3,z5]),(0,[z13,z1086,z1,z2,z3,z5]),(0,[z218,z0,z1,z2,z3,z445]),(0,[z208,z0,z30,z2,z3,z5]),(0,[z0,z1,z2,z3,z351,z1087])],[(0,[z13,z51,z1,z2,z3,z115]),(0,[z0,z1,z2,z3,z1058,z5]),(0,[z13,z0,z2,z3,z5,z585]),(0,[z13,z0,z1,z1088,z3,z5])],[(0,[z0,z1,z2,z3,z1089,z10]),(0,[z0,z1,z2,z3,z5,z1090]),(0,[z0,z1,z2,z3,z5,z1091])],[(0,[z0,z1,z2,z3,z5,z10]),(0,[z0,z1,z1092,z3,z5,z10]),(0,[z9,z1,z449,z3,z5,z10]),(0,[z1093,z0,z1,z2,z3,z5]),(0,[z1094,z1,z2,z3,z5,z10]),(0,[z0,z1,z2,z3,z1095,z5]),(0,[z1067,z0,z168,z2,z3,z5]),(0,[z0,z168,z2,z3,z245,z10]),(0,[z0,z434,z2,z3,z5,z19])],[(0,[z0,z1,z2,z3,z5,z1096]),(0,[z83,z1,z2,z3,z5,z486]),(0,[z1097,z1,z2,z3,z5,z10]),(0,[z1098,z0,z1,z2,z3,z5]),(0,[z290,z1,z2,z3,z245,z10]),(0,[z86,z0,z1,z53,z5,z10]),(0,[z0,z1099,z1,z2,z3,z5]),(0,[z0,z1,z2,z3,z64,z19])],[(0,[z0,z1,z2,z1100,z5,z10]),(0,[z0,z1,z2,z3,z1101,z10])],[(0,[z0,z1,z2,z3,z5,z1102]),(0,[z0,z1,z2,z7,z3,z193]),(0,[z0,z1,z1103,z3,z5,z10]),(0,[z0,z1,z2,z3,z5,z1104])]],
   [[(0,[z0,z1,z2,z3,z5,z1105]),(0,[z0,z1,z2,z1106,z3,z5]),(0,[z0,z1,z2,z129,z3,z5]),(0,[z0,z1,z2,z20,z460,z10])],[(0,[z13,z0,z29,z2,z85,z5]),(1,[z0,z2,z3,z717,z10]),(0,[z13,z191,z1,z2,z3,z5]),(0,[z93,z39,z2,z3,z5,z10])],[(0,[z1,z2,z27,z859,z5,z10]),(0,[z265,z1,z2,z3,z5,z110]),(0,[z0,z1,z2,z3,z1107,z5]),(0,[z0,z1,z2,z1108,z3,z5])],[(0,[z0,z1109,z1,z2,z3,z5]),(0,[z0,z339,z1,z3,z368,z5]),(0,[z236,z1,z2,z3,z5,z166]),(0,[z0,z1,z2,z3,z5,z141])],[(0,[z0,z1,z1110,z3,z5,z10])],[(0,[z1111,z0,z1,z2,z3,z5]),(0,[z652,z1,z2,z3,z108,z10]),(0,[z0,z1112,z2,z3,z5,z10])],[(0,[z13,z0,z2,z3,z5,z609]),(0,[z213,z69,z0,z7,z3,z5]),(0,[z1113,z1,z2,z3,z5,z10]),(0,[z1114,z0,z1,z2,z3,z5]),(0,[z1115,z1,z2,z3,z5,z10])],[(0,[z0,z1,z2,z3,z1116,z10]),(0,[z0,z1,z2,z1117,z5,z10]),(0,[z279,z0,z1,z2,z123,z5]),(0,[z0,z2,z3,z52,z5,z988])],[(0,[z0,z1,z2,z7,z3,z212]),(0,[z0,z1,z2,z154,z3,z5]),(0,[z93,z1,z2,z3,z104,z10])],[(0,[z0,z1,z2,z3,z1118,z5]),(0,[z1086,z1,z2,z3,z5,z10])],[(0,[z0,z1,z3,z5,z330,z10]),(0,[z82,z0,z1,z2,z10,z34]),(0,[z13,z0,z2,z3,z512,z5]),(0,[z529,z1,z66,z3,z5,z10])],[(0,[z0,z1119,z1,z2,z3,z5]),(0,[z0,z29,z2,z85,z5,z19]),(0,[z13,z0,z428,z2,z3,z5]),(0,[z1120,z1,z2,z3,z5,z10])],[(0,[z95,z1,z449,z87,z5,z10]),(0,[z215,z0,z2,z21,z5,z10]),(0,[z0,z1,z2,z1121,z3,z5]),(0,[z0,z2,z3,z239,z52,z5])],[(0,[z0,z1,z2,z1122,z5,z10]),(0,[z1123,z0,z1,z2,z3,z5])],[(0,[z0,z1,z2,z1124,z3,z5]),(0,[z13,z0,z79,z2,z3,z5]),(0,[z86,z0,z168,z53,z5,z10]),(0,[z0,z1125,z2,z3,z5,z10])],[(0,[z0,z1,z2,z3,z5,z1126]),(0,[z1127,z1,z2,z3,z5,z10]),(0,[z0,z543,z2,z85,z5,z10])]],
   [[(0,[z936,z0,z2,z3,z5,z10]),(0,[z0,z1,z2,z3,z5,z225]),(0,[z0,z301,z68,z3,z5,z10]),(0,[z1128,z1,z2,z3,z5,z10])],[(0,[z0,z1,z1129,z3,z5,z10]),(0,[z86,z0,z1,z626,z5,z10]),(0,[z48,z8,z1,z7,z3,z5]),(0,[z476,z0,z1,z2,z7,z3]),(0,[z1130,z0,z1,z2,z3,z5])],[(0,[z0,z1131,z1,z2,z3,z5]),(0,[z0,z1,z2,z3,z1132,z5]),(0,[z51,z30,z1,z2,z3,z115]),(0,[z0,z1,z348,z3,z5,z195]),(0,[z13,z0,z2,z3,z5,z179])],[(0,[z0,z1133,z2,z3,z5,z10])],[(0,[z0,z29,z2,z3,z239,z5])],[(0,[z0,z1,z2,z3,z5,z1134]),(0,[z12,z0,z30,z2,z3,z42]),(0,[z0,z1,z2,z3,z605,z19])],[(0,[z0,z1,z2,z1135,z3,z5]),(0,[z48,z8,z1,z3,z5,z225])],[(0,[z936,z73,z2,z3,z5,z10]),(0,[z0,z1,z2,z3,z5,z1136]),(0,[z83,z1,z2,z3,z5,z1057]),(1,[z0,z1,z773,z5,z10]),(0,[z0,z1,z2,z3,z31,z19]),(0,[z0,z1,z2,z786,z5,z173])],[(0,[z313,z0,z1,z2,z3,z140]),(0,[z0,z1,z2,z1137,z3,z5])],[(0,[z13,z0,z301,z2,z3,z5]),(0,[z0,z1138,z2,z3,z5,z10])],[(0,[z0,z1,z1139,z3,z5,z10]),(0,[z75,z1,z2,z7,z3,z108]),(0,[z51,z1,z252,z3,z115,z10]),(0,[z0,z1,z2,z3,z5,z1140]),(0,[z0,z1,z2,z542,z5,z173])],[(0,[z73,z133,z2,z3,z5,z19]),(0,[z145,z0,z2,z3,z5,z110]),(0,[z0,z1,z3,z14,z884,z10])],[(0,[z0,z1,z2,z1141,z3,z5]),(0,[z0,z1,z922,z3,z5,z10]),(0,[z0,z1,z2,z555,z5,z195]),(0,[z13,z0,z2,z3,z5,z234])],[(0,[z0,z1142,z2,z3,z5,z10]),(0,[z0,z1,z2,z3,z1143,z10]),(0,[z0,z1,z2,z446,z259,z5])],[(0,[z0,z1,z1144,z3,z5,z10]),(0,[z0,z1,z2,z1145,z3,z5]),(0,[z93,z1,z2,z3,z5,z238]),(0,[z0,z1,z275,z3,z5,z151])],[(0,[z86,z0,z1,z7,z53,z5]),(0,[z378,z0,z1,z2,z5,z362])]],
   [[(0,[z0,z1,z2,z1146,z3,z5]),(0,[z0,z1,z2,z3,z5,z1147]),(0,[z215,z0,z2,z712,z5,z10]),(0,[z145,z0,z1148,z2,z3,z5])],[(0,[z13,z0,z350,z2,z3,z5]),(0,[z0,z1,z1149,z3,z5,z10]),(0,[z0,z1,z91,z3,z14,z10])],[(0,[z0,z1,z2,z3,z5,z1150]),(0,[z0,z29,z2,z162,z5,z10]),(0,[z0,z23,z2,z3,z5,z10]),(0,[z13,z0,z2,z3,z427,z5]),(0,[z309,z1,z348,z3,z5,z10]),(0,[z0,z30,z1,z2,z344,z5]),(0,[z290,z1,z2,z3,z5,z19])],[(0,[z613,z133,z2,z3,z5,z10]),(0,[z1151,z0,z1,z2,z3,z5]),(0,[z0,z1,z2,z1152,z3,z5]),(0,[z0,z1,z1153,z3,z5,z10]),(0,[z0,z29,z2,z7,z85,z5]),(0,[z93,z1,z2,z3,z10,z34])],[(0,[z561,z1,z2,z3,z108,z10]),(0,[z0,z1,z2,z1154,z3,z183]),(0,[z0,z1,z2,z3,z135,z19]),(0,[z0,z30,z1,z66,z3,z14]),(0,[z0,z168,z2,z3,z5,z346]),(0,[z145,z0,z2,z3,z5,z146])],[(0,[z0,z1,z71,z107,z5,z10]),(0,[z1,z2,z859,z87,z5,z10]),(0,[z0,z1,z2,z3,z268,z19]),(0,[z119,z1,z2,z3,z5,z231]),(0,[z290,z1,z2,z3,z5,z346]),(0,[z93,z1,z2,z3,z5,z19]),(0,[z0,z1155,z2,z3,z5,z10])],[(0,[z215,z0,z184,z2,z21,z5]),(0,[z0,z168,z2,z3,z351,z10]),(0,[z0,z1,z2,z7,z3,z245])],[(0,[z0,z1,z2,z3,z5,z1156]),(0,[z0,z1,z2,z1157,z3,z5]),(0,[z0,z350,z2,z7,z3,z5]),(0,[z751,z0,z68,z3,z5,z10]),(0,[z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z348,z3,z5,z19]),(0,[z12,z0,z2,z3,z5,z140]),(0,[z290,z1,z2,z3,z351,z10]),(0,[z0,z1,z2,z786,z5,z10])],[(0,[z0,z1,z2,z3,z183,z19]),(0,[z1,z2,z3,z359,z108,z10]),(0,[z131,z1,z2,z3,z5,z110]),(0,[z0,z1,z2,z1158,z3,z5]),(0,[z0,z1,z1088,z3,z5,z10]),(0,[z0,z1,z2,z1159,z3,z5]),(0,[z145,z0,z2,z3,z14,z5])],[(0,[z0,z1,z66,z3,z197,z10]),(0,[z0,z1,z2,z3,z5,z1160]),(0,[z0,z1,z1161,z3,z5,z10]),(0,[z12,z0,z2,z3,z42,z10])],[(0,[z0,z1,z1162,z3,z5,z10]),(0,[z13,z0,z1,z252,z3,z5]),(0,[z0,z1,z348,z344,z5,z10]),(0,[z0,z1,z2,z3,z5,z1163])],[(0,[z0,z1,z2,z3,z193,z19]),(0,[z309,z1,z2,z3,z5,z391]),(0,[z529,z1,z2,z98,z3,z5]),(0,[z0,z1,z2,z1164,z3,z5])],[(0,[z0,z1,z2,z3,z5,z1165]),(0,[z309,z1,z2,z555,z5,z10])],[(0,[z941,z0,z1,z3,z5,z10]),(0,[z0,z1,z2,z1166,z3,z5]),(0,[z0,z382,z2,z3,z5,z19])],[(0,[z9,z1,z550,z3,z5,z10])],[(0,[z218,z0,z29,z2,z3,z5]),(0,[z360,z1,z348,z3,z5,z10]),(0,[z86,z0,z23,z53,z5,z10]),(0,[z191,z1,z2,z7,z3,z5])]],
   [[(0,[z0,z1,z2,z3,z1167,z5]),(0,[z0,z1,z2,z1054,z3,z5]),(0,[z1168,z0,z1,z2,z3,z5]),(0,[z0,z1169,z2,z3,z5,z10]),(0,[z1,z2,z1170,z3,z5,z19])],[(0,[z0,z1,z2,z84,z684,z5]),(0,[z0,z1,z2,z555,z5,z19]),(0,[z0,z1,z2,z3,z776,z10])],[(0,[z0,z1,z2,z7,z3,z183]),(0,[z13,z0,z23,z2,z3,z5])],[(0,[z145,z73,z0,z2,z3,z5]),(0,[z0,z1,z2,z3,z5,z188]),(0,[z0,z1,z1171,z3,z5,z10]),(0,[z13,z217,z0,z2,z3,z5]),(0,[z0,z1,z2,z1172,z3,z5])],[(0,[z92,z6,z2,z3,z5,z19]),(0,[z0,z1,z2,z3,z5,z1173]),(0,[z145,z119,z0,z2,z3,z5]),(0,[z0,z1174,z1,z2,z3,z5]),(0,[z13,z0,z2,z3,z5,z877])],[(0,[z1175,z0,z1,z2,z3,z5])],[(0,[z0,z1,z2,z3,z5,z1176]),(0,[z0,z1,z1177,z3,z5,z10]),(0,[z0,z1,z2,z1178,z3,z5]),(0,[z0,z1,z2,z3,z1179,z10])],[(0,[z0,z1,z1180,z3,z5,z10]),(0,[z0,z1,z2,z3,z1181,z10]),(0,[z222,z168,z2,z3,z5,z10])],[(0,[z1182,z0,z1,z2,z3,z5]),(0,[z360,z1,z2,z3,z5,z391]),(0,[z808,z30,z1,z2,z3,z5]),(0,[z0,z1183,z1,z2,z3,z5])],[(0,[z92,z6,z2,z3,z5,z273]),(0,[z360,z1,z2,z555,z5,z10]),(0,[z13,z0,z61,z2,z3,z52]),(0,[z145,z414,z0,z2,z3,z5])],[(0,[z0,z1,z2,z3,z5,z1184]),(0,[z145,z109,z0,z2,z3,z5])],[(0,[z1185,z1,z2,z3,z5,z10]),(0,[z86,z1,z136,z53,z5,z10]),(0,[z37,z0,z1,z3,z38,z492])],[(0,[z366,z0,z339,z1,z3,z5]),(0,[z145,z0,z2,z3,z87,z5]),(0,[z77,z0,z2,z3,z21,z5]),(0,[z12,z13,z360,z2,z3,z5]),(0,[z0,z1,z2,z1186,z3,z5]),(0,[z0,z1187,z2,z3,z5,z19])],[(0,[z0,z1,z2,z3,z1188,z10]),(0,[z1189,z0,z1,z2,z3,z5]),(0,[z366,z0,z1,z7,z3,z5]),(0,[z0,z1,z2,z1190,z3,z5]),(0,[z145,z0,z2,z3,z64,z5])],[(0,[z48,z8,z1,z3,z5,z206]),(0,[z0,z1,z2,z1191,z3,z5]),(0,[z0,z1,z2,z1192,z5,z10]),(0,[z13,z0,z1,z2,z3,z1193])],[(0,[z0,z1,z219,z3,z183,z10]),(0,[z177,z1,z2,z3,z5,z110]),(0,[z0,z1,z2,z84,z647,z5])]],
   [[(0,[z0,z1,z2,z1154,z3,z5]),(0,[z0,z1,z2,z3,z5,z1194])],[(0,[z0,z1,z2,z1195,z5,z10])],[(0,[z0,z1,z219,z3,z193,z10]),(0,[z0,z1,z2,z20,z10,z715])],[(0,[z0,z1,z2,z3,z5,z1196]),(0,[z0,z1,z2,z3,z5,z1197]),(0,[z1130,z0,z23,z2,z3,z5])],[(0,[z529,z1,z2,z185,z3,z5]),(0,[z0,z1,z2,z3,z5,z1198])],[(0,[z432,z133,z2,z3,z5,z10]),(0,[z309,z30,z1,z2,z3,z5])],[(0,[z1199,z0,z1,z2,z3,z5]),(0,[z1200,z0,z1,z2,z3,z5]),(0,[z8,z1,z3,z165,z5,z10]),(0,[z0,z30,z1,z180,z3,z5]),(0,[z1201,z0,z1,z2,z3,z5])],[(0,[z0,z1202,z2,z3,z5,z10]),(0,[z0,z1,z2,z3,z5,z1203]),(1,[z1,z2,z3,z5,z1057]),(0,[z1,z2,z3,z5,z166,z1057]),(0,[z13,z0,z2,z3,z555,z5]),(0,[z12,z0,z2,z3,z239,z5]),(0,[z0,z61,z2,z3,z717,z10]),(0,[z0,z1,z2,z3,z5,z1204]),(0,[z0,z1,z2,z3,z5,z1205]),(0,[z0,z1,z2,z1206,z3,z5]),(0,[z271,z1,z2,z409,z3,z5])],[(0,[z13,z0,z1,z2,z555,z5]),(0,[z0,z61,z2,z3,z52,z19]),(0,[z680,z0,z1,z2,z233,z5])],[(0,[z0,z1,z2,z1207,z3,z5]),(0,[z13,z0,z295,z68,z3,z5]),(0,[z0,z1183,z168,z2,z3,z5])],[(0,[z0,z1,z3,z5,z1208,z10]),(0,[z0,z1,z2,z3,z5,z1209]),(0,[z0,z1,z2,z1210,z3,z5])],[(0,[z1211,z0,z1,z2,z3,z5]),(0,[z0,z339,z1,z2,z3,z5]),(0,[z209,z1,z2,z3,z5,z166]),(0,[z1212,z0,z1,z2,z3,z5]),(0,[z0,z1,z411,z3,z5,z391]),(0,[z0,z61,z2,z399,z3,z52]),(0,[z0,z1,z2,z3,z5,z877]),(0,[z30,z1,z793,z2,z3,z5]),(0,[z0,z1,z2,z3,z884,z10])],[(0,[z1,z252,z3,z5,z108,z10]),(0,[z1213,z1,z2,z3,z5,z10]),(0,[z0,z1,z411,z555,z5,z10]),(0,[z145,z0,z70,z2,z3,z5]),(0,[z0,z1214,z2,z3,z5,z10])],[(0,[z0,z1,z2,z3,z5,z267]),(0,[z0,z1,z2,z3,z5,z1215]),(0,[z0,z1,z570,z3,z5,z47]),(1,[z0,z1,z2,z3,z776])],[(0,[z0,z1,z2,z7,z3,z5]),(0,[z0,z1,z2,z1216,z3,z5]),(0,[z0,z1,z2,z3,z5,z791]),(0,[z51,z1,z252,z3,z5,z10])],[(0,[z0,z2,z3,z5,z877,z179])]],
   [[(0,[z0,z1217,z2,z3,z5,z10]),(0,[z1068,z0,z350,z2,z3,z5]),(0,[z0,z1,z1218,z2,z3,z5]),(0,[z43,z0,z1,z3,z38,z10])],[(0,[z0,z1,z2,z1219,z3,z5]),(0,[z48,z366,z1,z3,z5,z10]),(0,[z0,z1,z2,z3,z5,z1220]),(0,[z0,z30,z16,z2,z3,z5]),(0,[z0,z1,z2,z7,z3,z413]),(0,[z37,z0,z1,z3,z38,z10]),(0,[z0,z1221,z1,z2,z3,z5])],[(0,[z13,z48,z8,z1,z3,z5]),(0,[z95,z1,z368,z87,z5,z10]),(0,[z384,z0,z1,z3,z38,z10]),(0,[z360,z30,z1,z2,z3,z5])],[(0,[z1222,z0,z1,z2,z3,z5]),(0,[z0,z1,z2,z1223,z3,z5])],[(0,[z0,z1,z2,z3,z5,z1224]),(0,[z12,z309,z2,z3,z42,z10]),(0,[z0,z1,z2,z3,z5,z1225])],[(0,[z518,z0,z1,z392,z3,z5]),(0,[z1226,z0,z1,z2,z3,z5]),(0,[z0,z1,z180,z3,z5,z238])],[(0,[z366,z0,z1,z419,z3,z5]),(0,[z855,z1,z2,z3,z5,z10]),(0,[z1227,z0,z1,z2,z3,z5])],[(0,[z0,z1,z2,z3,z1228,z10]),(0,[z751,z0,z1,z3,z5,z10]),(0,[z0,z1,z70,z7,z71,z5])],[(0,[z0,z2,z3,z5,z1229,z141])],[(0,[z0,z350,z2,z3,z5,z96]),(0,[z0,z1,z2,z3,z5,z1230]),(0,[z0,z1,z2,z3,z5,z1231]),(0,[z0,z1,z2,z3,z245,z1232])],[(0,[z1233,z0,z1,z2,z3,z5])],[(0,[z48,z291,z1,z3,z5,z10]),(0,[z0,z1,z2,z3,z5,z1234])],[(0,[z0,z1235,z1,z2,z3,z5]),(0,[z0,z30,z163,z2,z3,z5]),(0,[z13,z0,z39,z2,z3,z5]),(0,[z40,z0,z1,z2,z10,z715])],[(0,[z95,z1,z2,z87,z5,z19]),(0,[z0,z1,z2,z3,z5,z1236]),(0,[z0,z1,z2,z1237,z3,z5]),(0,[z0,z1,z2,z1238,z3,z5]),(0,[z0,z1,z2,z3,z5,z1239]),(0,[z0,z1,z2,z3,z5,z1240]),(0,[z18,z0,z1,z3,z94,z5])],[(0,[z0,z1,z2,z3,z1241,z10]),(0,[z0,z1,z2,z3,z5,z1242]),(0,[z0,z1,z66,z3,z624,z10]),(0,[z0,z1,z2,z1243,z3,z5]),(0,[z0,z1,z773,z53,z5,z10]),(0,[z1244,z0,z1,z2,z3,z5]),(0,[z0,z1,z139,z3,z5,z47])],[(0,[z1245,z0,z1,z2,z3,z5]),(0,[z75,z1,z2,z3,z108,z19]),(0,[z13,z0,z672,z2,z3,z5]),(0,[z979,z0,z2,z3,z5,z10])]],
   [[(0,[z0,z1,z2,z3,z5,z1246]),(0,[z0,z1,z419,z3,z368,z5]),(0,[z13,z213,z69,z0,z3,z5]),(0,[z0,z2,z712,z21,z5,z10]),(0,[z222,z30,z1,z2,z3,z5]),(0,[z1,z2,z98,z3,z136,z5]),(0,[z40,z0,z1,z180,z10,z34]),(0,[z1247,z0,z2,z3,z5,z19]),(0,[z0,z1248,z2,z3,z5,z19])],[(0,[z0,z2,z3,z52,z717,z10]),(0,[z145,z0,z2,z7,z3,z19])],[(0,[z122,z0,z16,z2,z123,z5])],[(0,[z12,z0,z2,z7,z3,z42]),(0,[z145,z0,z2,z3,z5,z38]),(0,[z40,z0,z1,z2,z19,z34])],[(0,[z77,z0,z1,z2,z3,z5]),(0,[z0,z1,z1249,z2,z3,z5]),(0,[z0,z1,z2,z3,z63,z19]),(0,[z0,z168,z2,z3,z5,z19]),(0,[z0,z1,z2,z3,z5,z1087]),(0,[z0,z1,z66,z7,z3,z14])],[(0,[z0,z1,z2,z3,z5,z1250]),(0,[z13,z0,z29,z2,z233,z5]),(0,[z0,z1,z2,z3,z5,z1251]),(0,[z0,z61,z1,z2,z3,z63]),(0,[z0,z39,z99,z3,z5,z10]),(0,[z0,z1252,z2,z3,z5,z10])],[(0,[z132,z0,z2,z3,z21,z5]),(0,[z12,z13,z0,z2,z3,z5]),(0,[z0,z2,z3,z64,z234,z19])],[(0,[z0,z1,z2,z419,z3,z5]),(0,[z0,z1,z2,z3,z5,z1253])],[(0,[z0,z307,z2,z3,z5,z10]),(0,[z12,z145,z0,z2,z3,z5]),(0,[z13,z0,z543,z2,z3,z5]),(0,[z113,z0,z1,z2,z7,z3])],[(0,[z0,z350,z2,z3,z5,z267])],[(1,[z0,z2,z3,z5,z877])],[(0,[z0,z1,z850,z3,z5,z10]),(0,[z1254,z0,z1,z2,z3,z5]),(0,[z13,z271,z1,z2,z3,z5])],[(0,[z0,z1,z2,z859,z5,z10]),(0,[z0,z30,z2,z3,z5,z696]),(0,[z0,z1,z2,z3,z1255,z10])],[(0,[z1256,z0,z2,z3,z5,z10]),(0,[z0,z1,z2,z3,z5,z1257])],[(0,[z1258,z0,z1,z2,z3,z5]),(0,[z0,z1,z2,z3,z5,z1259]),(0,[z1,z2,z3,z5,z10,z1260])],[(0,[z0,z1,z2,z3,z1261,z5]),(0,[z0,z1,z2,z1262,z3,z5]),(0,[z0,z1,z2,z3,z5,z1263]),(0,[z13,z222,z1,z2,z3,z5])]],
   [[(0,[z1264,z0,z1,z2,z3,z5]),(0,[z0,z1,z2,z3,z5,z1265])],[(0,[z0,z1,z2,z3,z5,z1266])],[(0,[z0,z1,z2,z3,z1002,z10]),(0,[z13,z0,z307,z2,z3,z5]),(0,[z0,z1,z2,z3,z1267,z5]),(0,[z145,z122,z0,z2,z3,z5]),(0,[z145,z0,z2,z35,z3,z5])],[(0,[z0,z1,z3,z5,z1268,z10]),(0,[z44,z1,z2,z87,z5,z10]),(0,[z0,z1,z2,z3,z5,z1269]),(0,[z13,z75,z1,z2,z3,z108]),(0,[z0,z184,z2,z3,z5,z22]),(0,[z1,z2,z185,z3,z136,z5])],[(0,[z0,z23,z2,z7,z3,z5]),(0,[z0,z1270,z2,z3,z5,z10]),(0,[z1,z2,z3,z5,z1271,z10])],[(0,[z0,z1,z1272,z3,z5,z10]),(0,[z1273,z0,z1,z2,z3,z5])],[(0,[z0,z1274,z2,z3,z5,z10]),(0,[z0,z1131,z350,z2,z3,z5]),(0,[z1,z2,z3,z5,z1057,z110]),(0,[z0,z1,z2,z344,z5,z391])],[(0,[z366,z1,z65,z3,z5,z10]),(0,[z0,z1,z2,z1275,z3,z5]),(0,[z0,z1,z129,z3,z5,z330]),(0,[z0,z365,z2,z3,z5,z42]),(0,[z145,z0,z2,z71,z3,z5]),(0,[z18,z0,z1,z3,z5,z949])],[(0,[z0,z61,z1,z2,z3,z140]),(0,[z0,z1,z2,z3,z5,z1276])],[(0,[z0,z1,z252,z3,z5,z10]),(0,[z95,z339,z1,z2,z87,z5]),(0,[z0,z1,z1277,z3,z5,z10]),(0,[z787,z0,z1,z2,z3,z5]),(0,[z487,z0,z1,z2,z3,z63])],[(0,[z0,z1,z2,z1278,z3,z5]),(0,[z0,z1,z1279,z3,z5,z10]),(0,[z0,z1280,z2,z3,z5,z10]),(0,[z83,z1,z2,z3,z454,z5]),(0,[z260,z0,z30,z2,z3,z5]),(0,[z0,z1,z139,z3,z5,z343]),(0,[z1,z2,z3,z5,z1281,z10]),(0,[z37,z13,z0,z1,z3,z38])],[(0,[z145,z0,z133,z2,z3,z5]),(0,[z0,z1,z2,z3,z5,z206]),(0,[z0,z1,z2,z3,z5,z1282]),(0,[z213,z69,z0,z3,z5,z194]),(0,[z0,z1,z2,z3,z5,z1283]),(0,[z0,z1,z2,z3,z795,z10]),(0,[z529,z1,z2,z3,z5,z19]),(0,[z0,z39,z180,z3,z5,z10])],[(0,[z0,z1,z2,z3,z5,z1284]),(0,[z95,z1,z2,z7,z87,z5]),(0,[z0,z1,z2,z1285,z3,z5])],[(0,[z0,z1,z2,z3,z5,z1286]),(0,[z0,z1,z252,z129,z3,z5]),(0,[z0,z1,z2,z1287,z3,z5]),(0,[z0,z1,z2,z3,z5,z1288])],[(0,[z0,z1289,z1,z2,z3,z5]),(0,[z0,z30,z1,z411,z3,z5]),(0,[z0,z2,z555,z5,z42,z10]),(0,[z529,z1,z3,z5,z38,z10]),(0,[z200,z0,z1,z3,z38,z10]),(0,[z145,z0,z2,z3,z5,z189])],[(0,[z0,z1,z1290,z3,z5,z10]),(0,[z0,z1291,z2,z3,z5,z10]),(0,[z0,z1,z2,z1292,z5,z10]),(0,[z13,z0,z1,z2,z1192,z5])]],
   [[(0,[z0,z1,z2,z3,z5,z96]),(0,[z0,z1,z2,z3,z5,z1293]),(0,[z0,z1,z2,z3,z5,z194]),(0,[z0,z1,z2,z1294,z3,z5]),(0,[z0,z2,z85,z712,z5,z10]),(0,[z0,z1,z1295,z3,z5,z10]),(0,[z147,z412,z1,z2,z3,z5]),(0,[z0,z30,z1,z70,z71,z5]),(0,[z18,z0,z1,z3,z224,z5])],[(0,[z9,z1,z3,z5,z59,z10]),(0,[z0,z1,z2,z3,z5,z1296]),(0,[z0,z1,z70,z71,z5,z19])],[(0,[z676,z6,z2,z3,z5,z10]),(0,[z0,z1,z2,z1297,z3,z5]),(0,[z1298,z0,z1,z2,z3,z5]),(0,[z0,z1,z2,z1299,z3,z5]),(0,[z0,z1,z99,z3,z5,z238])],[(0,[z0,z1,z2,z3,z5,z1300]),(0,[z0,z1,z2,z3,z5,z1301])],[(0,[z0,z1,z2,z3,z5,z1302]),(0,[z0,z1,z2,z7,z3,z355]),(0,[z145,z0,z2,z3,z5,z151])],[(0,[z0,z1,z1303,z2,z3,z5]),(0,[z122,z0,z1,z2,z786,z5])],[(0,[z0,z1,z2,z1304,z3,z5]),(0,[z0,z1,z2,z3,z5,z1305]),(0,[z0,z1,z2,z3,z5,z240])],[(0,[z0,z382,z219,z3,z5,z10]),(0,[z0,z1,z2,z3,z5,z1306]),(0,[z222,z1,z2,z3,z245,z10]),(0,[z86,z0,z1,z53,z5,z240]),(0,[z0,z1,z3,z884,z38,z10]),(0,[z0,z1,z99,z3,z10,z34]),(0,[z0,z1,z2,z3,z5,z41])],[(0,[z0,z1,z449,z3,z5,z19])],[(0,[z75,z1,z2,z3,z108,z457]),(0,[z0,z1,z2,z3,z5,z1307]),(0,[z0,z1,z99,z3,z5,z19])],[(0,[z0,z1,z2,z3,z5,z1308]),(0,[z51,z1,z2,z3,z1002,z10]),(0,[z40,z13,z0,z1,z2,z34]),(0,[z263,z354,z0,z1,z3,z5])],[(0,[z8,z1,z2,z3,z193,z10]),(0,[z0,z1,z2,z1309,z3,z5]),(0,[z0,z1,z2,z3,z5,z1310]),(0,[z145,z0,z2,z3,z5,z231])],[(0,[z0,z1311,z2,z3,z5,z10]),(0,[z191,z307,z2,z3,z5,z10]),(0,[z0,z1,z2,z3,z10,z715])],[(0,[z0,z1,z2,z1312,z3,z5]),(0,[z0,z1,z1313,z3,z5,z10]),(0,[z0,z2,z3,z52,z10,z413])],[(0,[z132,z0,z1,z2,z3,z5]),(0,[z0,z1,z1314,z2,z3,z5])],[(0,[z0,z1,z1315,z2,z3,z5]),(0,[z0,z1,z2,z3,z5,z1316]),(0,[z1,z2,z3,z5,z10,z1317]),(0,[z145,z1318,z0,z2,z3,z5])]],
   [[(0,[z0,z1,z2,z3,z1319,z10]),(0,[z0,z1,z2,z3,z1320,z10]),(0,[z1321,z0,z1,z2,z3,z5]),(0,[z13,z0,z2,z3,z5,z326]),(0,[z0,z30,z1,z99,z3,z5]),(0,[z1322,z0,z1,z2,z3,z5])],[(0,[z145,z0,z2,z65,z3,z5]),(0,[z0,z1323,z1,z2,z3,z5]),(0,[z13,z0,z1,z219,z3,z5]),(0,[z0,z1,z1324,z3,z5,z10]),(0,[z0,z1,z3,z5,z10,z1325]),(0,[z145,z0,z2,z3,z5,z140])],[(0,[z290,z1,z2,z3,z5,z10]),(0,[z1326,z0,z1,z3,z5,z10])],[(0,[z598,z0,z2,z21,z5,z10]),(0,[z13,z0,z1,z348,z3,z5])],[(0,[z0,z1,z2,z3,z5,z1327]),(0,[z0,z1,z2,z3,z5,z1328]),(0,[z1329,z1,z2,z3,z5,z10]),(0,[z145,z0,z2,z3,z5,z19])],[(0,[z145,z48,z0,z2,z3,z5]),(0,[z95,z1,z2,z419,z87,z5]),(0,[z93,z1,z2,z3,z5,z10]),(0,[z1330,z0,z1,z2,z3,z5]),(0,[z271,z30,z1,z2,z3,z5])],[(0,[z0,z1,z2,z3,z1331,z5]),(0,[z0,z1,z2,z1332,z3,z5]),(0,[z0,z1,z2,z7,z555,z5]),(0,[z0,z1,z1333,z3,z5,z10]),(0,[z0,z365,z1,z2,z3,z5]),(0,[z13,z0,z2,z3,z5,z338]),(0,[z0,z1,z2,z1334,z3,z245])],[(0,[z0,z1,z2,z3,z5,z1335]),(0,[z0,z1,z348,z3,z5,z10])],[(0,[z0,z1,z2,z3,z5,z1336]),(0,[z0,z1,z2,z3,z183,z10]),(0,[z13,z0,z1,z1022,z3,z5]),(0,[z0,z1,z2,z1337,z3,z5]),(0,[z329,z0,z1,z2,z123,z5])],[(0,[z1338,z1,z2,z3,z5,z10]),(0,[z0,z2,z3,z21,z5,z140])],[(0,[z554,z1,z264,z2,z3,z5]),(0,[z0,z1,z2,z3,z5,z1339]),(0,[z0,z1,z726,z3,z5,z19])],[(0,[z0,z1,z2,z3,z193,z10]),(0,[z75,z1,z2,z3,z1002,z10]),(0,[z0,z1,z2,z3,z5,z1340]),(0,[z603,z0,z30,z2,z3,z5])],[(0,[z0,z1,z2,z3,z5,z1341]),(0,[z218,z0,z365,z2,z3,z5]),(0,[z218,z0,z2,z3,z52,z5]),(0,[z0,z1099,z39,z2,z3,z5])],[(0,[z0,z1342,z2,z3,z5,z10]),(0,[z0,z1,z2,z3,z5,z1343]),(0,[z366,z222,z1,z3,z5,z10]),(0,[z145,z0,z295,z2,z3,z5]),(0,[z1,z2,z3,z5,z1344,z10]),(0,[z0,z1,z2,z7,z3,z588])],[(0,[z48,z941,z1,z3,z5,z10]),(0,[z13,z0,z1,z2,z3,z351]),(0,[z272,z145,z0,z2,z3,z5])],[(0,[z0,z1,z2,z1345,z5,z10]),(0,[z0,z1,z2,z3,z5,z1346]),(0,[z0,z1,z1347,z2,z3,z5]),(0,[z0,z1,z180,z3,z5,z19]),(0,[z0,z434,z2,z3,z5,z173]),(0,[z0,z2,z3,z5,z234,z19])]],
   [[(0,[z0,z1,z1348,z2,z3,z5]),(0,[z0,z1,z2,z390,z5,z173]),(0,[z1,z2,z1170,z3,z5,z10]),(0,[z0,z434,z139,z2,z3,z5])],[(0,[z1349,z0,z1,z2,z3,z5]),(0,[z0,z1350,z1,z2,z3,z5]),(0,[z0,z1,z2,z555,z5,z10]),(0,[z0,z1,z2,z300,z5,z173])],[(0,[z0,z1,z2,z3,z1193,z10]),(0,[z40,z0,z1,z2,z41,z34])],[(0,[z0,z1,z70,z288,z5,z10]),(0,[z1351,z1,z2,z3,z5,z10]),(0,[z218,z0,z2,z3,z583,z5])],[(0,[z9,z1,z65,z3,z5,z19]),(0,[z0,z1,z2,z3,z5,z1352]),(0,[z0,z1,z2,z3,z1353,z5])],[(0,[z941,z1,z2,z3,z5,z10]),(0,[z366,z51,z1,z3,z5,z10]),(0,[z310,z0,z1,z216,z3,z5]),(0,[z0,z1354,z1,z2,z3,z5])],[(0,[z0,z29,z2,z85,z4,z5]),(0,[z0,z1,z2,z3,z1355,z5]),(0,[z13,z1,z2,z3,z136,z5]),(0,[z0,z1,z2,z3,z5,z1356]),(0,[z858,z0,z2,z3,z5,z19])],[(0,[z0,z1,z2,z3,z5,z452]),(0,[z0,z1,z2,z1357,z3,z5])],[(0,[z0,z30,z1,z1358,z3,z5]),(0,[z0,z1,z2,z3,z443,z19]),(0,[z0,z1,z2,z7,z3,z776])],[(0,[z0,z1,z2,z3,z1359,z10]),(0,[z0,z1360,z1,z2,z3,z5]),(0,[z1,z2,z3,z115,z1002,z10]),(0,[z83,z1,z2,z3,z353,z5]),(0,[z145,z0,z2,z3,z52,z5])],[(1,[z941,z1,z3,z5,z10]),(0,[z95,z366,z1,z3,z5,z10]),(0,[z0,z1,z2,z3,z1361,z5]),(0,[z0,z1,z2,z3,z5,z1362]),(0,[z0,z1,z2,z931,z3,z5]),(0,[z40,z0,z1,z99,z10,z34]),(0,[z0,z1,z2,z3,z5,z1363])],[(0,[z0,z1364,z2,z3,z5,z10]),(0,[z0,z295,z68,z3,z5,z19]),(0,[z191,z1,z2,z3,z5,z41])],[(0,[z0,z1,z216,z3,z5,z47]),(0,[z222,z1,z2,z3,z5,z19]),(0,[z0,z23,z2,z3,z5,z240]),(1,[z0,z1,z2,z10,z715]),(0,[z0,z1187,z2,z3,z5,z10])],[(0,[z48,z8,z1,z3,z5,z452]),(0,[z366,z1,z3,z5,z108,z10]),(0,[z0,z1,z2,z153,z3,z5]),(0,[z0,z1,z2,z1006,z5,z10])],[(0,[z0,z1,z2,z3,z5,z1365]),(0,[z0,z30,z1,z2,z3,z193]),(0,[z95,z366,z1,z87,z5,z10]),(0,[z0,z1,z2,z1366,z3,z5]),(0,[z0,z39,z2,z3,z5,z238])],[(0,[z0,z434,z2,z3,z5,z10]),(0,[z13,z1367,z1,z2,z3,z5]),(0,[z0,z1368,z1,z2,z3,z5]),(0,[z222,z1,z2,z3,z5,z346]),(0,[z86,z222,z1,z53,z5,z10]),(0,[z0,z1,z2,z409,z3,z5]),(0,[z0,z1,z99,z3,z104,z10]),(0,[z1,z2,z3,z5,z10,z1369])]],
   [[(0,[z1008,z0,z1,z2,z3,z5]),(0,[z0,z30,z1,z1333,z3,z5])],[(0,[z1370,z1,z2,z3,z5,z10]),(0,[z0,z1,z2,z3,z559,z19]),(0,[z222,z1,z2,z3,z351,z10]),(0,[z1371,z145,z0,z2,z3,z5]),(0,[z1,z2,z3,z5,z1369,z19])],[(0,[z0,z1,z3,z5,z10,z1372]),(0,[z1,z2,z3,z5,z1002,z10]),(0,[z0,z1,z2,z1373,z3,z5])],[(0,[z13,z0,z2,z3,z5,z226]),(0,[z51,z1,z2,z3,z115,z221]),(0,[z13,z0,z29,z2,z21,z5]),(0,[z13,z0,z29,z2,z202,z5]),(0,[z0,z434,z30,z2,z3,z5]),(0,[z271,z1,z66,z3,z5,z10]),(0,[z0,z434,z2,z3,z123,z5])],[(0,[z0,z350,z2,z3,z183,z10]),(0,[z0,z1,z2,z3,z5,z1374]),(0,[z145,z0,z2,z3,z21,z5]),(0,[z13,z713,z1,z2,z3,z5]),(0,[z0,z1,z2,z3,z245,z19]),(0,[z0,z1,z2,z3,z1375,z10]),(0,[z0,z1,z3,z5,z19,z880])],[(0,[z0,z30,z1,z3,z368,z5]),(0,[z0,z1,z2,z3,z5,z1376]),(0,[z0,z1377,z1,z2,z3,z5]),(0,[z0,z39,z2,z3,z5,z19]),(0,[z0,z1,z2,z20,z104,z19])],[(0,[z0,z2,z3,z5,z10,z1229]),(0,[z0,z1,z2,z3,z776,z5]),(0,[z0,z2,z7,z3,z5,z234])],[(0,[z0,z350,z2,z3,z193,z10]),(0,[z95,z1,z219,z87,z5,z10]),(0,[z1378,z0,z2,z3,z5,z10]),(0,[z13,z0,z2,z3,z5,z431]),(0,[z0,z1,z2,z3,z245,z346]),(0,[z0,z1,z2,z106,z3,z5]),(0,[z777,z1,z2,z3,z5,z19])],[(0,[z13,z92,z6,z2,z3,z5]),(0,[z357,z1,z2,z3,z5,z166]),(0,[z0,z325,z1,z2,z3,z5]),(0,[z13,z0,z1,z2,z20,z104]),(0,[z1379,z1,z2,z3,z5,z10]),(0,[z0,z16,z2,z3,z5,z19])],[(0,[z0,z1,z2,z3,z1380,z5]),(0,[z0,z2,z3,z21,z239,z5]),(0,[z0,z1,z2,z3,z5,z1381]),(0,[z0,z1,z2,z3,z104,z140]),(0,[z1382,z1,z2,z3,z5,z10])],[(0,[z0,z1,z2,z3,z1383,z10]),(0,[z0,z307,z2,z7,z3,z5])],[(0,[z0,z1,z2,z3,z5,z1384]),(0,[z1385,z0,z1,z2,z3,z5]),(0,[z0,z604,z1,z331,z3,z5])],[(0,[z92,z247,z2,z3,z5,z10]),(0,[z13,z0,z2,z3,z5,z501]),(0,[z0,z1,z2,z1386,z3,z5])],[(0,[z9,z1,z444,z3,z5,z10]),(0,[z13,z0,z2,z21,z5,z34]),(0,[z0,z1,z1358,z3,z5,z10]),(0,[z0,z1,z2,z399,z3,z5]),(0,[z0,z896,z1,z2,z3,z5])],[(0,[z0,z29,z2,z85,z5,z10]),(0,[z13,z93,z1,z2,z3,z5]),(0,[z0,z1,z2,z1334,z3,z5])],[(0,[z73,z285,z133,z2,z3,z5]),(0,[z0,z1387,z2,z3,z5,z10]),(0,[z0,z1,z2,z3,z1388,z5]),(0,[z0,z1,z2,z3,z5,z1389]),(0,[z309,z1,z2,z3,z5,z195]),(0,[z1390,z145,z0,z2,z3,z5])]],
   [[(0,[z0,z1391,z2,z3,z5,z10])],[(0,[z0,z1,z1392,z3,z5,z10]),(1,[z936,z2,z3,z5,z10]),(0,[z0,z1,z2,z3,z5,z1393]),(0,[z13,z0,z334,z2,z3,z5]),(0,[z0,z1,z2,z3,z5,z1394])],[(0,[z1395,z0,z1,z2,z3,z5]),(0,[z145,z0,z2,z3,z5,z195])],[(0,[z0,z61,z2,z555,z5,z10])],[(0,[z0,z1,z2,z3,z5,z1396]),(0,[z30,z1,z1042,z2,z3,z5]),(0,[z0,z1,z66,z3,z14,z19])],[(0,[z26,z1,z2,z621,z5,z10]),(0,[z13,z26,z1,z2,z27,z5]),(0,[z218,z145,z0,z2,z3,z5])],[],[(0,[z1,z2,z3,z1397,z5,z10]),(0,[z0,z1,z2,z3,z5,z1398]),(0,[z0,z1,z2,z344,z5,z195]),(0,[z354,z0,z1,z3,z5,z189]),(0,[z0,z1,z2,z3,z5,z1399])],[(0,[z1,z2,z3,z5,z10,z1057]),(0,[z13,z0,z2,z3,z345,z5]),(0,[z13,z0,z2,z417,z3,z5]),(0,[z1,z2,z409,z3,z5,z72])],[(0,[z75,z30,z1,z2,z3,z108]),(0,[z0,z1,z2,z1400,z5,z10]),(0,[z13,z0,z553,z2,z3,z5]),(0,[z0,z1,z2,z84,z259,z5])],[(0,[z674,z0,z2,z21,z5,z10]),(0,[z0,z1,z930,z3,z5,z10]),(0,[z0,z1,z2,z3,z5,z949]),(0,[z0,z1401,z1,z2,z3,z5])],[(0,[z0,z1,z1402,z3,z5,z10]),(0,[z0,z1,z252,z7,z3,z5]),(0,[z1403,z0,z1,z2,z3,z5])],[(0,[z0,z1404,z1,z3,z5,z10]),(0,[z13,z0,z382,z2,z3,z5]),(0,[z0,z1,z2,z3,z5,z1405]),(0,[z360,z1,z2,z3,z5,z195])],[(0,[z12,z218,z0,z2,z3,z5]),(0,[z13,z0,z2,z555,z5,z10]),(0,[z0,z61,z2,z3,z52,z585])],[(0,[z73,z133,z2,z3,z5,z10]),(0,[z0,z1,z139,z331,z3,z5]),(0,[z122,z0,z434,z2,z123,z5])],[(0,[z0,z1406,z2,z3,z5,z10]),(0,[z75,z1,z2,z3,z108,z10]),(0,[z1407,z1,z2,z3,z5,z10]),(0,[z13,z0,z482,z2,z3,z5])]],
   [[(0,[z1247,z0,z2,z3,z5,z10]),(0,[z0,z1,z2,z7,z3,z140]),(0,[z13,z0,z2,z3,z671,z5]),(0,[z0,z1248,z2,z3,z5,z10])],[(0,[z0,z1,z2,z3,z5,z1408])],[(0,[z0,z1409,z1,z2,z3,z5]),(0,[z149,z0,z1,z3,z5,z189]),(0,[z215,z0,z30,z2,z21,z5]),(0,[z18,z0,z434,z2,z3,z5]),(0,[z145,z145,z0,z2,z3,z5])],[(0,[z0,z1,z2,z3,z5,z1410]),(0,[z0,z1,z2,z3,z5,z1411]),(0,[z0,z1412,z2,z3,z5,z10]),(0,[z363,z0,z1,z2,z10,z34])],[(0,[z0,z1413,z1,z2,z3,z5]),(0,[z0,z168,z2,z3,z5,z10]),(0,[z309,z1,z2,z3,z5,z19]),(0,[z40,z0,z1,z2,z10,z34]),(0,[z145,z0,z2,z20,z3,z5]),(0,[z145,z0,z2,z84,z3,z5])],[(0,[z0,z29,z2,z3,z4,z5]),(0,[z0,z30,z1,z2,z3,z245]),(0,[z414,z0,z1,z3,z5,z146])],[(0,[z0,z1,z2,z3,z5,z1414]),(0,[z0,z1,z2,z1415,z3,z5]),(0,[z13,z0,z121,z2,z3,z5])],[(0,[z0,z1416,z2,z3,z5,z10]),(0,[z0,z1,z2,z3,z5,z1417]),(0,[z217,z0,z2,z21,z5,z10]),(0,[z309,z1,z2,z344,z5,z10]),(0,[z13,z0,z425,z2,z3,z5])],[(0,[z0,z1,z2,z3,z1418,z5])],[(0,[z145,z6,z0,z2,z3,z5]),(1,[z0,z1,z3,z884,z10]),(0,[z0,z1,z2,z7,z3,z569])],[(0,[z13,z613,z0,z2,z3,z5]),(0,[z0,z1,z2,z347,z104,z10]),(0,[z13,z0,z29,z2,z3,z5]),(0,[z0,z1,z66,z3,z14,z15])],[(0,[z92,z6,z2,z3,z5,z58]),(0,[z0,z1,z2,z3,z5,z1419]),(0,[z13,z0,z88,z2,z3,z5]),(0,[z0,z1420,z1,z2,z3,z5]),(0,[z1421,z1,z2,z3,z5,z10])],[(0,[z0,z1,z2,z3,z183,z1096]),(0,[z0,z30,z2,z3,z5,z356]),(0,[z213,z649,z0,z3,z5,z10]),(0,[z1422,z1,z2,z3,z5,z10]),(0,[z0,z1,z2,z344,z5,z19])],[(0,[z0,z1,z1423,z3,z5,z10]),(0,[z0,z1,z1424,z2,z3,z5]),(0,[z0,z1,z2,z3,z5,z513])],[(0,[z0,z1,z2,z3,z5,z112]),(0,[z191,z30,z1,z2,z3,z5]),(0,[z0,z1,z2,z3,z351,z19]),(0,[z145,z0,z2,z3,z5,z47])],[(0,[z0,z30,z1,z449,z3,z5]),(0,[z0,z1,z411,z3,z5,z195]),(0,[z145,z0,z2,z3,z53,z5])]],
   [[(0,[z0,z382,z2,z3,z5,z10]),(0,[z92,z936,z2,z3,z5,z10]),(0,[z0,z2,z3,z5,z22,z195]),(0,[z0,z1425,z2,z3,z5,z10]),(0,[z18,z0,z1,z3,z5,z189])],[(0,[z0,z30,z1,z2,z3,z183]),(0,[z360,z1,z2,z3,z5,z19]),(0,[z0,z1,z2,z3,z5,z1426]),(0,[z0,z1,z2,z3,z351,z346]),(0,[z271,z1,z2,z3,z5,z19])],[],[(0,[z0,z1,z1427,z3,z5,z10]),(0,[z51,z1,z2,z3,z632,z10]),(0,[z0,z1428,z2,z3,z5,z10]),(0,[z0,z1,z2,z3,z5,z391]),(0,[z13,z581,z0,z2,z3,z5])],[(0,[z1429,z0,z1,z2,z3,z5]),(0,[z0,z1,z2,z3,z5,z1430]),(0,[z0,z1,z2,z712,z5,z10]),(0,[z360,z1,z2,z344,z5,z10]),(0,[z290,z1,z2,z7,z3,z5])],[(0,[z0,z1431,z2,z3,z5,z10]),(0,[z0,z1,z2,z3,z5,z1432]),(0,[z13,z0,z1,z902,z3,z5]),(0,[z1201,z0,z39,z2,z3,z5])],[(0,[z26,z1,z2,z27,z5,z19]),(0,[z145,z51,z0,z2,z3,z5])],[(0,[z92,z6,z2,z3,z5,z10]),(0,[z0,z1,z2,z3,z5,z1433]),(0,[z0,z1,z2,z1434,z3,z5]),(0,[z0,z1,z2,z3,z5,z1435]),(0,[z0,z1,z1436,z3,z5,z10]),(0,[z0,z1,z2,z1437,z3,z5]),(0,[z0,z1,z2,z3,z5,z1438]),(0,[z93,z1,z2,z7,z3,z5])],[(0,[z8,z1,z449,z3,z5,z10]),(0,[z0,z1,z557,z3,z5,z47]),(0,[z968,z1,z2,z3,z5,z10]),(0,[z0,z1,z2,z3,z5,z1439])],[(0,[z95,z350,z2,z87,z5,z10]),(0,[z0,z1,z2,z3,z183,z267]),(0,[z0,z1,z2,z1440,z3,z5]),(0,[z0,z1,z2,z3,z1441,z5]),(0,[z0,z1,z348,z7,z3,z5])],[(0,[z0,z1,z1442,z3,z5,z10]),(0,[z0,z30,z1,z3,z5,z330]),(0,[z218,z0,z2,z3,z21,z5])],[(0,[z92,z6,z30,z2,z3,z5]),(0,[z529,z1,z2,z3,z5,z10]),(0,[z0,z1,z2,z3,z5,z1443])],[(0,[z0,z1,z2,z3,z5,z1444]),(0,[z0,z1,z2,z3,z193,z267]),(0,[z0,z1,z2,z3,z5,z1445]),(0,[z0,z1,z2,z1446,z3,z5]),(0,[z122,z0,z1,z2,z512,z5]),(0,[z0,z1,z2,z7,z3,z351]),(0,[z1447,z1,z2,z3,z5,z10])],[(0,[z0,z1,z2,z3,z5,z1448]),(0,[z0,z960,z2,z3,z5,z19])],[(0,[z0,z1,z2,z3,z1449,z5]),(0,[z0,z1,z2,z3,z5,z1232]),(0,[z145,z0,z2,z3,z5,z187])],[(0,[z0,z1001,z1,z2,z3,z5]),(0,[z0,z1,z2,z3,z5,z1450]),(0,[z1367,z1,z2,z3,z5,z10]),(0,[z309,z1,z411,z3,z5,z10]),(0,[z0,z30,z1,z1180,z3,z5])]],
   [[(0,[z0,z1,z2,z3,z5,z1451]),(0,[z936,z133,z2,z3,z5,z10]),(0,[z0,z1,z834,z3,z5,z10]),(0,[z0,z1,z219,z3,z5,z19]),(0,[z119,z1,z264,z2,z3,z5]),(0,[z77,z0,z295,z68,z3,z5]),(0,[z0,z1,z2,z3,z5,z63]),(0,[z37,z0,z1,z3,z884,z10])],[(0,[z0,z1,z2,z3,z5,z1452]),(0,[z12,z13,z0,z2,z555,z5]),(0,[z0,z325,z61,z2,z3,z52]),(0,[z0,z1,z1453,z3,z5,z10])],[(0,[z0,z1,z3,z5,z1454,z10]),(0,[z966,z0,z1,z3,z5,z19])],[(0,[z0,z1,z2,z3,z1455,z10]),(0,[z289,z1,z2,z3,z108,z10])],[(0,[z145,z26,z0,z2,z3,z5]),(0,[z13,z0,z2,z3,z5,z572]),(0,[z0,z1,z2,z3,z5,z1456]),(0,[z0,z1,z411,z3,z5,z19])],[(0,[z37,z0,z30,z1,z3,z38]),(0,[z645,z0,z1,z2,z7,z3])],[(0,[z26,z1,z2,z7,z27,z5])],[(0,[z936,z1,z2,z3,z5,z10]),(0,[z1457,z0,z1,z2,z3,z5]),(0,[z0,z2,z3,z1058,z21,z5]),(0,[z0,z1,z411,z344,z5,z10]),(0,[z1040,z1,z2,z3,z5,z10]),(0,[z271,z1,z2,z3,z5,z15])],[(0,[z0,z1,z2,z3,z5,z1458]),(0,[z0,z1,z449,z3,z5,z10])],[(0,[z0,z1,z2,z1459,z3,z5]),(0,[z0,z1,z99,z3,z5,z10])],[(0,[z1085,z30,z1,z2,z3,z5]),(0,[z1,z2,z3,z5,z1460,z10])],[(0,[z0,z61,z2,z3,z52,z10]),(0,[z290,z23,z2,z3,z5,z10])],[(0,[z941,z1,z65,z3,z5,z10]),(0,[z145,z75,z0,z2,z3,z5]),(0,[z360,z1,z411,z3,z5,z10]),(0,[z18,z0,z1,z392,z3,z5]),(0,[z0,z1461,z2,z3,z5,z10])],[(0,[z0,z30,z1,z2,z3,z5]),(0,[z1,z2,z3,z72,z10,z34])],[(0,[z1462,z1,z2,z3,z5,z10]),(0,[z0,z1,z2,z3,z5,z1057]),(0,[z0,z386,z1,z2,z300,z5]),(0,[z0,z1,z2,z3,z5,z1463])],[(0,[z529,z1,z65,z3,z5,z10]),(0,[z0,z1,z2,z1464,z3,z5])]]]

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
theorem pb0 : chunkB SB 1 ((bkA.flatten.flatten.drop 0).take 499) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb1 : chunkB SB 1 ((bkA.flatten.flatten.drop 499).take 494) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb2 : chunkB SB 1 ((bkA.flatten.flatten.drop 993).take 436) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pbend : ((bkA.flatten.flatten.drop 1429)).isEmpty = true := by
  decide +kernel

theorem windowsB : windowsG (chunkB SB 1) bkA.flatten.flatten 0 [499, 494, 436] = true :=
  windowsG_cons pb0 (windowsG_cons pb1 (windowsG_cons pb2 (windowsG_nil pbend)))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc0 : chunkOK 5 ((bkB.flatten.drop 0).take 109).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc1 : chunkOK 5 ((bkB.flatten.drop 109).take 118).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc2 : chunkOK 5 ((bkB.flatten.drop 227).take 121).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc3 : chunkOK 5 ((bkB.flatten.drop 348).take 103).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc4 : chunkOK 5 ((bkB.flatten.drop 451).take 61).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pcend : ((bkB.flatten.drop 512)).isEmpty = true := by
  decide +kernel

theorem windowsC : windowsF 5 bkB.flatten 0 [109, 118, 121, 103, 61] = true :=
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

end PEqualNP.Outside.L_meta_38723

theorem PEqualNP.Outside.L_meta_38723 :
    ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276808424 * 2 ^ 32 + 4008372936) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276808424 * 2 ^ 32 + 4008372936) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  exact PEqualNP.Outside.L_meta_38723.solve