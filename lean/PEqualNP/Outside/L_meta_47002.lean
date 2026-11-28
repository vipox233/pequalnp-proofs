import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_47002

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
  Nat.testBit (3941264040 * 2 ^ 32 + 3936922248) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

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
  [(0x2a0000c04d013495#64 ++ 0xff7387c3ff0fffff#64 : BitVec 128),
   (0x94053a1d22748a4a#64 ++ 0x9ffd7a3d23f48e4f#64 : BitVec 128),
   (0x181a5c2e34b8d38c#64 ++ 0x19fe7c3e3cf8f38c#64 : BitVec 128),
   (0xc02f803780de0360#64 ++ 0xe1bf803fc0ff03f0#64 : BitVec 128),
   (0x004fef4000efec00#64 ++ 0x01dfffc000fffc00#64 : BitVec 128),
   (0x008ff7bbfb000000#64 ++ 0x01efffffff000000#64 : BitVec 128)]

def witness : Circuit :=
  ⟨[⟨.and, [4, 5]⟩, ⟨.or, [3, 6]⟩, ⟨.and, [1, 7]⟩, ⟨.or, [0, 8]⟩, ⟨.or, [1, 7]⟩, ⟨.and, [0, 10]⟩, ⟨.and, [9, 2]⟩, ⟨.or, [4, 5]⟩, ⟨.and, [12, 13]⟩, ⟨.or, [11, 14]⟩], 15⟩

def mkw (a b : BitVec 64) : W := a ++ b

def z0 : W := mkw 0x004fef4000efec00 0x01dfffc000fffc00

def z1 : W := mkw 0x008ff7bbfb000000 0x01efffffff000000

def z2 : W := mkw 0x181a5c2e34b8d38c 0x19fe7c3e3cf8f38c

def z3 : W := mkw 0x2a0000c04d013495 0xff7387c3ff0fffff

def z4 : W := mkw 0x94053a1d22748a4a 0x9ffd7a3d23f48e4f

def z5 : W := mkw 0xc02f803780100360 0xe1af803fc00003f0

def z6 : W := mkw 0xc02f803780de0360 0xe1bf803fc0ff03f0

def z7 : W := mkw 0x0040084000efec00 0x0010000000fffc00

def z8 : W := mkw 0x008010bbfb000000 0x0020003fff000000

def z9 : W := mkw 0x0000000000000000 0x0151020000048c00

def z10 : W := mkw 0x185a7f6e34b9ff8c 0x19fe7ffe3cf8ff8c

def z11 : W := mkw 0x0000000000000000 0x9f71020123048e4f

def z12 : W := mkw 0xbe053add6f75bedf 0xffffffffffffffff

def z13 : W := mkw 0xd83f903fb4de13ec 0xf9bf803ffcff03fc

def z14 : W := mkw 0xc020003780100360 0xe133803fc00f03f0

def z15 : W := mkw 0x00cfffc87befec00 0x01dfffc03ffffc00

def z16 : W := mkw 0x94053a1d22748a4a 0x19fc783c20f0820c

def z17 : W := mkw 0xbe0008440475bedf 0xfe10000000ffffff

def z18 : W := mkw 0x0000000000000000 0xe1338003c00f03f0

def z19 : W := mkw 0x181a5c2e34b8d38c 0xf9fffc3ffcfff3fc

def z20 : W := mkw 0x18dfffffffffff8c 0x19ffffffffffff8c

def z21 : W := mkw 0x0000004000012400 0x015387c0000ffc00

def z22 : W := mkw 0x004fef0000eec800 0x008c780000f00000

def z23 : W := mkw 0x0800000004001084 0x197204023c08f38c

def z24 : W := mkw 0x3a1a5cee7db9f79d 0xffffffffffffffff

def z25 : W := mkw 0x2a1a44e25d897595 0x600285c2dc0b71b0

def z26 : W := mkw 0x18105c083420d08c 0x18407c003c00f00c

def z27 : W := mkw 0x8405221102440842 0x8601020103040c43

def z28 : W := mkw 0x2a8ff7fbff013495 0x1fefffffff00fc0f

def z29 : W := mkw 0x004008400021ec00 0x000000000000fc00

def z30 : W := mkw 0x0000000000000000 0x016204023c000000

def z31 : W := mkw 0x008ac5a2d9000000 0x000285c2dc000000

def z32 : W := mkw 0x9400080400748a4a 0x9e10000000f48e4f

def z33 : W := mkw 0x105fff6e30ffef08 0x01dffffc00fffc00

def z34 : W := mkw 0x1c107e083620d88e 0x1e407e003f00fc0f

def z35 : W := mkw 0x0045ab400067ac00 0x01ddfbc000f78c00

def z36 : W := mkw 0x081a442214885184 0x000204021c087180

def z37 : W := mkw 0x402a8026809a0320 0x61be803ec0fb03b0

def z38 : W := mkw 0x0800004004013484 0x197387c23c0fff8c

def z39 : W := mkw 0x0005321922000000 0x01ed7a3d23000000

def z40 : W := mkw 0x948fffbffb748a4a 0x9ffffffffff48e4f

def z41 : W := mkw 0x00406f000020c800 0x0000780000000000

def z42 : W := mkw 0x008ff7887b000000 0x01cfffc03f000000

def z43 : W := mkw 0x004a4c4000efec00 0x01de7c0000fffc00

def z44 : W := mkw 0x1000180c20308208 0x19fc783c20f0820c

def z45 : W := mkw 0x9c1f7e3f36fcdbce 0x9fff7e3f3ffcffcf

def z46 : W := mkw 0xc025801180460060 0xe0018001c0070070

def z47 : W := mkw 0xc06fef5180efec60 0xe1dfffc1c0fffc70

def z48 : W := mkw 0xd83fdc3fb4fed3ec 0x19fe7c3e3cf8f38c

def z49 : W := mkw 0x00004c000020c000 0x00407c000000f000

def z50 : W := mkw 0x1810080404b8d38c 0x1810000000f8f38c

def z51 : W := mkw 0x189fffbfffb8d38c 0x19fffffffff8f38c

def z52 : W := mkw 0x0000008049000000 0x016387c3ff000000

def z53 : W := mkw 0x8005001500540240 0x81bd003d00f40240

def z54 : W := mkw 0x402a8022808a0120 0x60028002c00b01b0

def z55 : W := mkw 0x008023804b000000 0x000003c003000000

def z56 : W := mkw 0xbe0008c44d75bedf 0xff7387c3ffffffff

def z57 : W := mkw 0x000a4c4000a9e400 0x01dfffc000fffc00

def z58 : W := mkw 0x1800180c2430928c 0x19fe7c3e3cf8f38c

def z59 : W := mkw 0x80052a1500748a40 0x81fd7a3d00f48e40

def z60 : W := mkw 0xd4253a1d22fe8b6a 0xfffd7a3d23ff8fff

def z61 : W := mkw 0xd42fba3fa2fe8b6a 0xfffffa3fe3ff8fff

def z62 : W := mkw 0x0000008049000000 0x00200003ff000000

def z63 : W := mkw 0xc060084400ffef60 0xe010000000fffff0

def z64 : W := mkw 0x220000c049012411 0xe60183c1c3070c73

def z65 : W := mkw 0x004a6f4000a9ec00 0x01de7fc000f8fc00

def z66 : W := mkw 0x181a102e3498138c 0x19be003e3cf8038c

def z67 : W := mkw 0x10053a1d22308208 0x19fd7a3d23f0820c

def z68 : W := mkw 0x000f803780980300 0x01bf803fc0f80380

def z69 : W := mkw 0x008077887b000000 0x00407fc03f000000

def z70 : W := mkw 0xc0aff7bffbde0360 0xe1ffffffffff03f0

def z71 : W := mkw 0x0400220002000802 0x0600020003000c03

def z72 : W := mkw 0x3a1a5cee7db9f79d 0x79fefdfefcfbf3bc

def z73 : W := mkw 0x00456f400065ec00 0x01dd7fc000f4fc00

def z74 : W := mkw 0x000fe70000000000 0x01cfffc000000000

def z75 : W := mkw 0x00cffffbfbefec00 0x01fffffffffffc00

def z76 : W := mkw 0x2a85a3d1cf013495 0xff7387c3ff0fffff

def z77 : W := mkw 0x0000008049000000 0xe17387c3ff0f03f0

def z78 : W := mkw 0x2a0000c04d013495 0x797285c2fc0bf3bc

def z79 : W := mkw 0x000fd43bb0000000 0x01effc3ffc000000

def z80 : W := mkw 0x004fef4000efec00 0x9fffffc123fffe4f

def z81 : W := mkw 0xc02f803780de0360 0xffff823fe3ff8fff

def z82 : W := mkw 0x000fb23ba2000000 0x01effa3fe3000000

def z83 : W := mkw 0x0005221102000000 0x0001020103000000

def z84 : W := mkw 0x000fe74000012400 0x01dfffc0000ffc00

def z85 : W := mkw 0x000f803380000000 0xe1bf803fc00f03f0

def z86 : W := mkw 0x2a0000c04d013495 0x616387c3ff0b71b0

def z87 : W := mkw 0x9c053a1d26749ace 0x9fff7e3f3ffcffcf

def z88 : W := mkw 0xd83fdc3fb4fed3ec 0xf9fffc3ffcfff3fc

def z89 : W := mkw 0x2a0000c04d013495 0x000005c01c007000

def z90 : W := mkw 0xc02f803780de0360 0x008c003c00f00000

def z91 : W := mkw 0xea2f80f7cddf37f5 0xffff87ffffffffff

def z92 : W := mkw 0x2200008049000011 0xe6000001c3000073

def z93 : W := mkw 0x008ff73bb2000000 0x008c783c00000000

def z94 : W := mkw 0x1000180c20308208 0x9ffd7a3d23f48e4f

def z95 : W := mkw 0x940f7e1d22fcca4a 0x9fff7e3d23fcfe4f

def z96 : W := mkw 0xc020000400de0360 0xe1338003c0ff03f0

def z97 : W := mkw 0x40200000008a0120 0x60000000000b01b0

def z98 : W := mkw 0xc06f887780ffef60 0xe1bf803fc0fffff0

def z99 : W := mkw 0x000a542a30000000 0x008c783c00000000

def z100 : W := mkw 0xc020000400de0360 0xe010000000ff03f0

def z101 : W := mkw 0x000a002600980300 0x01be003e00f80380

def z102 : W := mkw 0x004fef4000efec00 0x00cc7fc000f0fc00

def z103 : W := mkw 0x94cffffffbffee4a 0x9ffffffffffffe4f

def z104 : W := mkw 0x0000080000a8c000 0x0010000000f8f000

def z105 : W := mkw 0x00406f400021ec00 0x00407fc00000fc00

def z106 : W := mkw 0x000a542a30000000 0x01ee7c3e3c000000

def z107 : W := mkw 0x000a002600980300 0x008c003c00f00000

def z108 : W := mkw 0x004fef6600ffef00 0x01fffffe00ffff80

def z109 : W := mkw 0x402f802280ce0120 0x619f8002c0ff01b0

def z110 : W := mkw 0x181a5c2a3420d08c 0x19ee7c3e3c00f00c

def z111 : W := mkw 0x2a406fc04d21fc95 0xff73ffc3ff0fffff

def z112 : W := mkw 0xc0a010bffb100360 0xe020003fff0003f0

def z113 : W := mkw 0x0005800000460000 0x0001800000070000

def z114 : W := mkw 0x2a0000804d001095 0x60000002dc0001b0

def z115 : W := mkw 0xc02f803780de0360 0x019f803c00ff0000

def z116 : W := mkw 0x2a0000c04d013495 0xe60387c3df0f7df3

def z117 : W := mkw 0xe22580d1c9472471 0xe60183c1c3070c73

def z118 : W := mkw 0x00cfefd1cbefec00 0x01dfffc1c3fffc00

def z119 : W := mkw 0x000fef0000648800 0x01dfffc000f48c00

def z120 : W := mkw 0x101a5c2e30b8c308 0x008c783c00f00000

def z121 : W := mkw 0x94053a1d22748a4a 0xfffffa3fe3ff8fff

def z122 : W := mkw 0x00400040008b6400 0x00000000000b7000

def z123 : W := mkw 0xc020003780100360 0x0000003c00000000

def z124 : W := mkw 0x2a8ff7bbff001095 0xffefffffff0003ff

def z125 : W := mkw 0x008ff7bbfbce0000 0x01ffffffffff0000

def z126 : W := mkw 0x2a0f80c04dcf3495 0xffff87c3ffffffff

def z127 : W := mkw 0x0045a34000472c00 0x000183c000070c00

def z128 : W := mkw 0x185fff6e34ffff8c 0x19fffffe3cffff8c

def z129 : W := mkw 0x94053a1d22748a4a 0x81bd783d00f40240

def z130 : W := mkw 0x004fef0000eec800 0x01de7c0000f8f000

def z131 : W := mkw 0x181000040410138c 0x180000000000038c

def z132 : W := mkw 0x940f3a3f22fc8b4a 0x9fff7a3f23fc8fcf

def z133 : W := mkw 0x000fe70000000000 0x008c780000000000

def z134 : W := mkw 0x94453a5d22ffee4a 0x9ffd7a3d23fffe4f

def z135 : W := mkw 0xc020000000460060 0xe000000000070070

def z136 : W := mkw 0x40aac5a2d98a0120 0x600285c2dc0b01b0

def z137 : W := mkw 0x8005001500540240 0xe1bf803fc0ff03f0

def z138 : W := mkw 0x004fe74000472c00 0x01cfffc000070c00

def z139 : W := mkw 0xc0a5a391cb460060 0xe00183c1c3070070

def z140 : W := mkw 0x940fff1d22748a4a 0x9ffffffd23f48e4f

def z141 : W := mkw 0xd83a5c3fb4b8d3ec 0xf9fe7c3ffcf8f3fc

def z142 : W := mkw 0xc02fd43fb0de0360 0xe1fffc3ffcff03f0

def z143 : W := mkw 0x0080458059000000 0x000005c01c000000

def z144 : W := mkw 0xd425ba1da2768a6a 0xfffdfa3de3f78e7f

def z145 : W := mkw 0x84052a1102648842 0x87dd7a0103f48c43

def z146 : W := mkw 0x0085a391cb000000 0x000183c1c3000000

def z147 : W := mkw 0x2a8ac5e2dd013495 0x600285c2dc0b71b0

def z148 : W := mkw 0x008ac52290000000 0x0000000000000000

def z149 : W := mkw 0x000a802280000000 0x00028002c0000000

def z150 : W := mkw 0x2a4fefc04deffc95 0xffffffc3ffffffff

def z151 : W := mkw 0x181f7e2e34fcdb8c 0x19ff7e3e3cfcff8c

def z152 : W := mkw 0x2a0000c04d013495 0x1f6387c3ff00fc0f

def z153 : W := mkw 0x0085a391cb000000 0x016387c3ff000000

def z154 : W := mkw 0x0000000000000000 0x0000000000000000

def z155 : W := mkw 0x000a4c0000a8c000 0x01de7c0000f8f000

def z156 : W := mkw 0x944fff5d22ffee4a 0x9ffffffd23fffe4f

def z157 : W := mkw 0xc02a002600de0360 0xe1be003e00ff03f0

def z158 : W := mkw 0xd4afffbffbfe8b6a 0xffffffffffff8fff

def z159 : W := mkw 0x000a002600980300 0xe1bf803fc0ff03f0

def z160 : W := mkw 0x14003a082220880a 0x1e407a0023008c0f

def z161 : W := mkw 0x40aff7bbfb8a0120 0x61efffffff0b01b0

def z162 : W := mkw 0x000a5c2a30a8c000 0x01fe7c3e3cf8f000

def z163 : W := mkw 0x0000100820000000 0x01ec783c20000000

def z164 : W := mkw 0xc020003780de0360 0xe030003fc0ff03f0

def z165 : W := mkw 0x2a45a3c04d473c95 0xff7387c3ff0fffff

def z166 : W := mkw 0x181010083400108c 0x180000003c00000c

def z167 : W := mkw 0x2a00004004013495 0x1e0000000000fc0f

def z168 : W := mkw 0xc06fef7780ffef60 0xe1ffffffc0fffff0

def z169 : W := mkw 0x18507f483421fc8c 0x18407fc03c00fc0c

def z170 : W := mkw 0x2a00004004013495 0xfe100000000fffff

def z171 : W := mkw 0xc020000400de0360 0x0000000000f00000

def z172 : W := mkw 0x2a0000c04d013495 0x1e4007c03f00fc0f

def z173 : W := mkw 0xa60522d14b452c53 0xe60183c1c3070c73

def z174 : W := mkw 0x008a54bbfb000000 0x01ee7c3fff000000

def z175 : W := mkw 0x000f800000ce0000 0x019f800000ff0000

def z176 : W := mkw 0x000fef0000a8c000 0x01dfffc000f8f000

def z177 : W := mkw 0x181f7e3f36b8d38c 0x19ff7e3f3ff8f38c

def z178 : W := mkw 0x3a10084404b9f79d 0xfe10000000ffffff

def z179 : W := mkw 0x181a5c2e34b8d38c 0x008e7c3e1cf87180

def z180 : W := mkw 0x008af7aafb000000 0x0042ffc2ff000000

def z181 : W := mkw 0x004ac540008b6400 0x000285c0000b7000

def z182 : W := mkw 0x9400101d2210024a 0x9e20003d2300024f

def z183 : W := mkw 0xc02f803380ce0160 0xe0038003c00f01f0

def z184 : W := mkw 0x004fa34000cf2c00 0x019f83c000ff0c00

def z185 : W := mkw 0x3a1010ee7d11379d 0xff7387ffff0fffff

def z186 : W := mkw 0x0005a30000000000 0x000183c000000000

def z187 : W := mkw 0x2a00004004013495 0xff7204023c0fffff

def z188 : W := mkw 0x008ff7bbfb000000 0xe1ffffffff0f03f0

def z189 : W := mkw 0x00052a0000648800 0x9ffd7a0123f48e4f

def z190 : W := mkw 0xc06fef4400ffef60 0xe1dfffc000fffff0

def z191 : W := mkw 0x18105c0c3430d28c 0x19fc7c3c3cf0f20c

def z192 : W := mkw 0x000a440000884000 0x0002040000087000

def z193 : W := mkw 0x1810102e3410138c 0x1820003e3c00038c

def z194 : W := mkw 0xc06fef3780fecb60 0x008c783c00f00000

def z195 : W := mkw 0x004ac540008b6400 0x015387c0000ffc00

def z196 : W := mkw 0x00cff7fbfb472c00 0x01efffffff070c00

def z197 : W := mkw 0x1810182e3430938c 0x19fc783e3cf0838c

def z198 : W := mkw 0x2a4fef4004effc95 0xffdfffc000ffffff

def z199 : W := mkw 0x085ac562148b7584 0x000285c21c0b7180

def z200 : W := mkw 0x0045ef400067ec00 0x0041ffc00007fc00

def z201 : W := mkw 0x008fe7a2d9000000 0x01cfffc2dc000000

def z202 : W := mkw 0x004fef4000efec00 0xe1ffffc3c0fffff0

def z203 : W := mkw 0x181a542e3498538c 0x1822043e3c08738c

def z204 : W := mkw 0xea2f80f7cddf37f5 0xe1bf85ffdcff73f0

def z205 : W := mkw 0x2a0000c04d013495 0x1f5387c03f0ffc0f

def z206 : W := mkw 0x0800000004001084 0x181000000008f38c

def z207 : W := mkw 0x0810000004885184 0x0000000000087180

def z208 : W := mkw 0xc02a802680de0360 0xe0128002c0ff03f0

def z209 : W := mkw 0x8005001500540240 0x008c003c00f00000

def z210 : W := mkw 0x189a5cbfffb8d38c 0x19fe7c3ffff8f38c

def z211 : W := mkw 0x080a4c0004a8d084 0x19fe7c023cf8f38c

def z212 : W := mkw 0xc020003780100360 0xe020003fc00003f0

def z213 : W := mkw 0x940fba3fa2748a4a 0x9ffffa3fe3f48e4f

def z214 : W := mkw 0xd42f903fa2de036a 0xffbf803fe3ff03ff

def z215 : W := mkw 0xd03fdc3fb0fec368 0xe1bff83fc0ff03f0

def z216 : W := mkw 0xc02a003780980360 0xe1be003fc0f803f0

def z217 : W := mkw 0x0000004000012400 0x000285c0000b7000

def z218 : W := mkw 0x2a0000c04d013495 0xfe6007c3ff00ffff

def z219 : W := mkw 0x104fff4c20ffee08 0x19fffffc20fffe0c

def z220 : W := mkw 0xd03fdc3fb0fec368 0x008c783c00f00000

def z221 : W := mkw 0x2a0000804d001095 0xff338003ff0f03ff

def z222 : W := mkw 0x008ff7bbfb000000 0x00cc7ffc3f000000

def z223 : W := mkw 0x00406f400021ec00 0x0153ffc0000ffc00

def z224 : W := mkw 0x9405321d2210024a 0x9fed7a3d2300024f

def z225 : W := mkw 0x008010bbfb000000 0x016387ffff000000

def z226 : W := mkw 0xc0aff7bffb100360 0xe1efffffff0003f0

def z227 : W := mkw 0x940f7e3f32748a4a 0x9fff7e3f3ff48e4f

def z228 : W := mkw 0x14807f887b20880a 0x1e407fc03f008c0f

def z229 : W := mkw 0x00052a0000648800 0x01dd7a0000f48c00

def z230 : W := mkw 0x189fff3fb6b8d38c 0x19fe7c3e3cf8f38c

def z231 : W := mkw 0xc025001500de0360 0xe1bd003d00ff03f0

def z232 : W := mkw 0x1850084404ffff8c 0x1810000000ffff8c

def z233 : W := mkw 0x1010102e30100308 0x0000003c00000000

def z234 : W := mkw 0x2a8ff7fbff013495 0xffffffffff0fffff

def z235 : W := mkw 0xc02f803780de0360 0x01af803fc0f00000

def z236 : W := mkw 0x004fff5922efec00 0x01fffffd23fffc00

def z237 : W := mkw 0xc0aff7bbfb460060 0xe1efffffff070070

def z238 : W := mkw 0x100a5c2e30308208 0x19fe7c3e3cf0820c

def z239 : W := mkw 0x000a002200880100 0x0002000200080180

def z240 : W := mkw 0x004fef4000efec00 0x008efdc000fb7000

def z241 : W := mkw 0x004ac500008a4000 0x0000000000000000

def z242 : W := mkw 0x0005801180000000 0x00018001c0000000

def z243 : W := mkw 0x140008000020880a 0x1e00000000008c0f

def z244 : W := mkw 0x0085f799fb000000 0x0041ffc1ff000000

def z245 : W := mkw 0xd42fba3fa2fe8b6a 0x9ffd7a3d23f48e4f

def z246 : W := mkw 0xd42fba3fa2fe8b6a 0x008c783c00f00000

def z247 : W := mkw 0x000f800000000000 0x018f800000000000

def z248 : W := mkw 0x00c5a3d1cb472c00 0x000183c1c3070c00

def z249 : W := mkw 0x2a0000804d001095 0xfe200003ff0003ff

def z250 : W := mkw 0x2a40084004effc95 0xfe10000000ffffff

def z251 : W := mkw 0x0005000000440000 0x019d000000f40000

def z252 : W := mkw 0xae0522d14f453cd7 0xff7387c3ff0fffff

def z253 : W := mkw 0x185fff4834effc8c 0x19dfffc03cfffc0c

def z254 : W := mkw 0xc06fef7780ffef60 0x01dffffc00fffc00

def z255 : W := mkw 0x008010887b000000 0x000000003f000000

def z256 : W := mkw 0x000a54aa79000000 0x01efffffff000000

def z257 : W := mkw 0x181a5c6e34b9f78c 0x19fffffe3cffff8c

def z258 : W := mkw 0x00808180c9000000 0x000081c0c0000000

def z259 : W := mkw 0x0000000000000000 0x0132000200080380

def z260 : W := mkw 0xb6053add6b75ae5b 0xfffdfbfde3f78e7f

def z261 : W := mkw 0x189ff7bfff10138c 0x19efffffff00038c

def z262 : W := mkw 0x8000001500100240 0x8020003d00000240

def z263 : W := mkw 0x0000008049000000 0x9f7387c3ff048e4f

def z264 : W := mkw 0xc02f803780de0360 0x608e803ec0fb01b0

def z265 : W := mkw 0xea2000b7cd1013f5 0xfe20003fff0003ff

def z266 : W := mkw 0x00052a400065ac00 0x01dfffc000fffc00

def z267 : W := mkw 0x0040814000032400 0x000081c000030000

def z268 : W := mkw 0x000ff71922000000 0x01effffd23000000

def z269 : W := mkw 0x000f803380000000 0x01af803fc0000000

def z270 : W := mkw 0x004fef7380efec00 0x01ffffffc0fffc00

def z271 : W := mkw 0x94053a1d22748a4a 0x008c783c00f00000

def z272 : W := mkw 0x008ff7bbfb000000 0x00ac783fff000000

def z273 : W := mkw 0x3a1a5cae7db8d39d 0xfffe7c3ffff8f3ff

def z274 : W := mkw 0xc065a35180472c60 0xe00183c1c0070c70

def z275 : W := mkw 0x94052a1502748a4a 0x9e11020103f48e4f

def z276 : W := mkw 0x004fefc049efec00 0x01ffffc3fffffc00

def z277 : W := mkw 0x2a0000c04d013495 0xfe5007c03f0fffff

def z278 : W := mkw 0xd830080404fed3ec 0xf810000000fff3fc

def z279 : W := mkw 0xc02fe73780de0360 0xe1ffffffc0ff03f0

def z280 : W := mkw 0x3a1a5c6e34b9f79d 0xfffe7c3e3cffffff

def z281 : W := mkw 0x800f803780540240 0x81bf803fc0f40240

def z282 : W := mkw 0xd02f983fa0fe8368 0xf9fff83fe0ff83fc

def z283 : W := mkw 0x402a8022808a0120 0x0000000000000000

def z284 : W := mkw 0x0000003380000000 0x0020003fc0000000

def z285 : W := mkw 0xbe0010dd6f1136df 0xff7387ffff0fffff

def z286 : W := mkw 0xc025801580de0360 0xe0118001c0ff03f0

def z287 : W := mkw 0xc02fb23fa2de0360 0xe1fffa3fe3ff03f0

def z288 : W := mkw 0x228ff7fbfb012411 0xe7efffffff070c73

def z289 : W := mkw 0x000f800000ce0000 0xe1bf8003c0ff03f0

def z290 : W := mkw 0x008a77aa7b000000 0x01ee7ffe3f000000

def z291 : W := mkw 0x2a0000c04d013495 0xfe300003ff0fffff

def z292 : W := mkw 0x181a4c0404b8d38c 0x19de7c0000f8f38c

def z293 : W := mkw 0x3a1010ae7d10139d 0xfe20003fff0003ff

def z294 : W := mkw 0x948fffbffb748a4a 0x01effffffff00000

def z295 : W := mkw 0x2a0a4cc04da9f495 0xffffffc3ffffffff

def z296 : W := mkw 0x008077bbfb000000 0x00607fffff000000

def z297 : W := mkw 0x8405321922440842 0x87ed7a3d23040c43

def z298 : W := mkw 0x948010bffb10024a 0x9e20003fff00024f

def z299 : W := mkw 0x220000c049012411 0xff7183c1e3078e7f

def z300 : W := mkw 0xc025803780560360 0xe021803fc00703f0

def z301 : W := mkw 0x008ff7bbfb000000 0x008efdfedc000000

def z302 : W := mkw 0x181a5c2e34b8d38c 0x18cc7c3c3cf0f00c

def z303 : W := mkw 0x109fffbffbb8c308 0x01effffffff00000

def z304 : W := mkw 0x080a002604981384 0x19fe043e3cf8f38c

def z305 : W := mkw 0x94053a5d2275ae4a 0x9ffffffd23fffe4f

def z306 : W := mkw 0x00cfffbbfbeec800 0x01effffffff00000

def z307 : W := mkw 0x8005321d22540240 0x81fd7a3d23f40240

def z308 : W := mkw 0x008077887b000000 0x0163ffc3ff000000

def z309 : W := mkw 0x94052a0400748a4a 0x9fdd7a0000f48e4f

def z310 : W := mkw 0x2a0000c04d013495 0x600285c2dc0b71b0

def z311 : W := mkw 0x000faa0000ee8800 0x01dffa0000ff8c00

def z312 : W := mkw 0x14053a192220880a 0x1fed7a3d23008c0f

def z313 : W := mkw 0xc02f803780de0360 0xe08d803dc0f70070

def z314 : W := mkw 0x3a105cc87d21f49d 0xff73ffc3ff0fffff

def z315 : W := mkw 0xc425a21182460862 0xe6018201c3070c73

def z316 : W := mkw 0x0000002600100300 0x0020003e00000380

def z317 : W := mkw 0xd46fff7fa2ffef6a 0xffffffffe3ffffff

def z318 : W := mkw 0x0000000000000000 0xe0018001c0070070

def z319 : W := mkw 0x085fef6214effd84 0x01dfffc21cfffd80

def z320 : W := mkw 0x181a5c0834a8d08c 0x19de7c003cf8f00c

def z321 : W := mkw 0xea2000f7cd1137f5 0xff7387ffff0fffff

def z322 : W := mkw 0x804fef5500ffee40 0x81fffffd00fffe40

def z323 : W := mkw 0x0085b3bbfb000000 0x002183ffff000000

def z324 : W := mkw 0xc0af90bffbde0360 0xe1bf803fffff03f0

def z325 : W := mkw 0x2a0000c04d013495 0xfe1285c2dc0fffff

def z326 : W := mkw 0x0000004000012400 0x004007c00000fc00

def z327 : W := mkw 0x9485bb9deb748a4a 0x9ffdfbfde3f48e4f

def z328 : W := mkw 0x220000c049012411 0x060003c003000c03

def z329 : W := mkw 0x000ac50000000000 0x000285c000000000

def z330 : W := mkw 0xbe8fffffff75bedf 0xffffffffffffffff

def z331 : W := mkw 0x004acd4000abe400 0x01defdc000fbf000

def z332 : W := mkw 0x0000670000000000 0x00407fc000000000

def z333 : W := mkw 0x8400001102000042 0x8600000103000043

def z334 : W := mkw 0xbe4fffdd6ffffedf 0xffffffffffffffff

def z335 : W := mkw 0x944fff5d22ffee4a 0x01dffffc00fffc00

def z336 : W := mkw 0x3a5fffee7dffff9d 0xffffffffffffffff

def z337 : W := mkw 0xc02f803780de0360 0xe09c003c00ff03f0

def z338 : W := mkw 0x181fdc3fb4b8d38c 0x19fffc3ffcf8f38c

def z339 : W := mkw 0x808ff7bffb540240 0x81fffffffff40240

def z340 : W := mkw 0x00cac5e2d98b6400 0x000285c2dc0b7000

def z341 : W := mkw 0x000fe78049000000 0x01efffc3ff000000

def z342 : W := mkw 0x9440084400ffee4a 0x9e10000000fffe4f

def z343 : W := mkw 0x181fdc2e34fed38c 0x19fffc3e3cfff38c

def z344 : W := mkw 0x2a8077c87f013495 0x1e407fc03f00fc0f

def z345 : W := mkw 0x94857f9d7b748a4a 0x9ffd7ffd3ff48e4f

def z346 : W := mkw 0x001a442210884100 0x0000000000000000

def z347 : W := mkw 0x185fff2e34fedb8c 0x19fe7c3e3cf8f38c

def z348 : W := mkw 0x008577997b000000 0x01ed7ffd3f000000

def z349 : W := mkw 0x14003a0c22308a0a 0x1ffc7a3c23f08e0f

def z350 : W := mkw 0x000a4c0000a8c000 0x008c780000f00000

def z351 : W := mkw 0x2a0000804d001095 0x1e0000003f00000f

def z352 : W := mkw 0x008ff73bb2000000 0x01ed7a3d23000000

def z353 : W := mkw 0x0000000000000000 0x015204000008f000

def z354 : W := mkw 0xbe053a5d2675bedf 0xfffd7a3d23ffffff

def z355 : W := mkw 0xd83a5c2e34fed3ec 0xf9fe7c3e3cfff3fc

def z356 : W := mkw 0x008fffbbfba8c000 0x01fffffffff8f000

def z357 : W := mkw 0xc83fc43794de53e4 0xe1bf843fdcff73f0

def z358 : W := mkw 0x008ff73bb2000000 0x01cffffc00000000

def z359 : W := mkw 0x406fef6280efed20 0x61dfffc2c0fffdb0

def z360 : W := mkw 0x00053a1922648800 0x01fd7a3d23f48c00

def z361 : W := mkw 0x2a0a54ea7d013495 0xffffffffff0fffff

def z362 : W := mkw 0x0005220000440800 0x0001020000040c00

def z363 : W := mkw 0x101a5c2e30b8c308 0x01de7c3c00f8f000

def z364 : W := mkw 0xc025801180460060 0xe1338003c00f03f0

def z365 : W := mkw 0x844fef5102efec42 0x87dfffc103fffc43

def z366 : W := mkw 0x181a5c2e34b8d38c 0x9fff7e3f3ffcffcf

def z367 : W := mkw 0x004fc54000cf6400 0x019f85c000ff7000

def z368 : W := mkw 0x1000100c20100208 0x1820003c2000020c

def z369 : W := mkw 0x181a082604b8d38c 0x19be003e00f8f38c

def z370 : W := mkw 0x101a5c2e30b8c308 0x19fc783c20f0820c

def z371 : W := mkw 0x9445bb5d2277ae4a 0x9ffdfbfd23f78e4f

def z372 : W := mkw 0x0000000000000000 0x9e2000012300024f

def z373 : W := mkw 0x004fef4000efec00 0x009c780000fffc00

def z374 : W := mkw 0x402f8033808a0120 0x61af803fc00b01b0

def z375 : W := mkw 0xc02f801180ce0060 0xe19f8001c0ff0070

def z376 : W := mkw 0x9400101d2210024a 0x9f71023d23048e4f

def z377 : W := mkw 0xbe1f7eff7ffdffdf 0xffffffffffffffff

def z378 : W := mkw 0x008ac5a2d9000000 0x016387c3ff000000

def z379 : W := mkw 0x9405321d22540a4a 0x9e21023d23040e4f

def z380 : W := mkw 0xc020001180000060 0xe0000001c0000070

def z381 : W := mkw 0x2285a3d1cb012411 0xe60183c1c3070c73

def z382 : W := mkw 0xc0aff73fb2de0360 0xe1bff83fc0ff03f0

def z383 : W := mkw 0x94853abffb748a4a 0x9ffd7a3ffff48e4f

def z384 : W := mkw 0xc0aff73fb2de0360 0x008c783c00f00000

def z385 : W := mkw 0x220000c049012411 0x600081c0c0030030

def z386 : W := mkw 0x583adc2eb4bad3ac 0x79fefc3efcfbf3bc

def z387 : W := mkw 0x2a4ac5c04d8b7495 0xff7387c3ff0fffff

def z388 : W := mkw 0x189010bfff10138c 0x1820003fff00038c

def z389 : W := mkw 0xc02f803380460060 0xe1af803fc0070070

def z390 : W := mkw 0xc02f80b7c9de0360 0xe1ff87ffffff03f0

def z391 : W := mkw 0x1810080404b8d38c 0x197204023cf8f38c

def z392 : W := mkw 0x181a4c2614b8d38c 0x181204021cf8f38c

def z393 : W := mkw 0x2a0000c04d013495 0xfe4187c1ff07fc7f

def z394 : W := mkw 0xc0effffffbffef60 0xe1fffffffffffff0

def z395 : W := mkw 0x004fef0000eec800 0x01cfffc000f00000

def z396 : W := mkw 0x3a105cc87d21f49d 0x1e407fc03f00fc0f

def z397 : W := mkw 0x080a542a34001084 0x19fe7c3e3c08f38c

def z398 : W := mkw 0x081a542a34885184 0x01ee7c3e3c087180

def z399 : W := mkw 0x0800000004001084 0xf9738403fc0ff3fc

def z400 : W := mkw 0xc82f803784de13e4 0xf9ff843ffcfff3fc

def z401 : W := mkw 0x3a1a5cee7db9f79d 0x1ffe7ffe3ff8ff8f

def z402 : W := mkw 0x00cfff3bb2eec800 0x008c783c00f00000

def z403 : W := mkw 0x2a406fc04d21fc95 0x1e407fc03f00fc0f

def z404 : W := mkw 0x008fe7b3db000000 0x000387c3df000000

def z405 : W := mkw 0xc0aff7bffbde0360 0x01effffffff00000

def z406 : W := mkw 0x0000000000000000 0x014387c000000000

def z407 : W := mkw 0x2a4008c04deffc95 0xff7387c3ffffffff

def z408 : W := mkw 0x2a0000c04d013495 0xfe2285c3ff0b73ff

def z409 : W := mkw 0x948ff7bffb10024a 0x9fefffffff00024f

def z410 : W := mkw 0xea20004404df37f5 0xfe10000000ffffff

def z411 : W := mkw 0x0045ab4000efec00 0x001183c000fffc00

def z412 : W := mkw 0x9400080400748a4a 0x9f71020123f48e4f

def z413 : W := mkw 0x2a0f80f3cd013495 0xffff87ffff0fffff

def z414 : W := mkw 0x224fefc049efec11 0xe7dfffc1c3fffc73

def z415 : W := mkw 0x0000080000648800 0x0010000000f48c00

def z416 : W := mkw 0x800f801500de0240 0x81bf803d00ff0240

def z417 : W := mkw 0x185add6e34bbf78c 0x19fefdfe3cfbf38c

def z418 : W := mkw 0x0005321922000000 0x008c783c00000000

def z419 : W := mkw 0xe22f80f7c9df2771 0xe7bf83ffc3ff0ff3

def z420 : W := mkw 0x000532996b000000 0x01efffffff000000

def z421 : W := mkw 0x94053a1d22748a4a 0x01ed7a3d23f00000

def z422 : W := mkw 0x9c1a5c2e34fcdbce 0x9ffe7c3e3cfcffcf

def z423 : W := mkw 0x0005220000000000 0x01cd7a0000000000

def z424 : W := mkw 0x2a8010fbff013495 0xff7387ffff0fffff

def z425 : W := mkw 0xc02f803780de0360 0xe0ac003fc0f003f0

def z426 : W := mkw 0x00cfefe2d9efec00 0x01dfffc2dcfffc00

def z427 : W := mkw 0x0085b399eb000000 0x01edfbfde3000000

def z428 : W := mkw 0x2a0000c04d013495 0xfe2183c3ff070fff

def z429 : W := mkw 0x14407f482221ec0a 0x1e407fc02300fc0f

def z430 : W := mkw 0x94457f5d2275ee4a 0x9ffd7ffd23f4fe4f

def z431 : W := mkw 0x0000008049000000 0x000183c1c3000000

def z432 : W := mkw 0x0040004000472c00 0x0000000000070c00

def z433 : W := mkw 0xea2f80b7cdde13f5 0xffbf803fffff03ff

def z434 : W := mkw 0x008ad5aaf9000000 0x01eefdfefc000000

def z435 : W := mkw 0xc0afa3b7cbde0360 0xe1bf83ffc3ff03f0

def z436 : W := mkw 0xea2000c44ddf37f5 0xff7387c3ffffffff

def z437 : W := mkw 0x008ff7fbfb012400 0x01ffffffff0ffc00

def z438 : W := mkw 0x3a9fffffffb9f79d 0xffffffffffffffff

def z439 : W := mkw 0x9c9fffbffffcdbce 0x9ffffffffffcffcf

def z440 : W := mkw 0x100a182e20b88308 0x19fe783e20f8838c

def z441 : W := mkw 0x181008000420d08c 0x180000000000f00c

def z442 : W := mkw 0xc02f803780de0360 0x01be003e00f80380

def z443 : W := mkw 0x4020800080020020 0x60008000c0030030

def z444 : W := mkw 0x2a8ff7fbff013495 0x61efffffff0b71b0

def z445 : W := mkw 0x081a442614985384 0x01be043e1cf87380

def z446 : W := mkw 0x00406f4000efec00 0x00507fc000fffc00

def z447 : W := mkw 0x800f003700dc0340 0x81bf003f00fc03c0

def z448 : W := mkw 0x94053a1d22748a4a 0x01dd7a3c00f48c00

def z449 : W := mkw 0x008ff7bbfb000000 0x9fffffffff048e4f

def z450 : W := mkw 0x940000040010024a 0x9e0000000000024f

def z451 : W := mkw 0x0810002214001184 0x000000021c000180

def z452 : W := mkw 0x000a002200000000 0x01ae003e00000000

def z453 : W := mkw 0x94003a0c22748a4a 0x9e507a0023f48e4f

def z454 : W := mkw 0x008ad5bbfb000000 0x002285ffff000000

def z455 : W := mkw 0x000ff72a30000000 0x01effffe3c000000

def z456 : W := mkw 0x220000c049012411 0xe76387c3ff070c73

def z457 : W := mkw 0x944fef4400ffee4a 0x9fdfffc000fffe4f

def z458 : W := mkw 0x2a4fefc04deffc95 0x61dfffc2dcfffdb0

def z459 : W := mkw 0xd83f883784fed3ec 0xf9bf803fc0fff3fc

def z460 : W := mkw 0x9c10080404fcdbce 0x9e10000000fcffcf

def z461 : W := mkw 0x081a442214885184 0x197204023c08f38c

def z462 : W := mkw 0x3e003ac86f21bc9f 0xff73ffc3ff0fffff

def z463 : W := mkw 0x9c153a1d26fcdbce 0x9ffd7a3d23fcffcf

def z464 : W := mkw 0x004f884000efec00 0x019f800000fffc00

def z465 : W := mkw 0x108fffbffb308208 0x19fffffffff0820c

def z466 : W := mkw 0x0000000000000000 0x1e40020023008c0f

def z467 : W := mkw 0x10053a0c20748a08 0x19fd7a3c20f48e0c

def z468 : W := mkw 0x2200004000012411 0xe600000000070c73

def z469 : W := mkw 0x004fef0000eec800 0x019ff80000ff0000

def z470 : W := mkw 0x4020002280000120 0x60000002c00001b0

def z471 : W := mkw 0x000a8000008a0000 0x00028000000b0000

def z472 : W := mkw 0x9c10103f361013ce 0x9e20003f3f0003cf

def z473 : W := mkw 0xc025801580560260 0xe1bd803dc0f70270

def z474 : W := mkw 0x0000000000ce0000 0x0010000000ff0000

def z475 : W := mkw 0x000a542e30980300 0x01fe7c3e3cf80380

def z476 : W := mkw 0x000fcc0000eec000 0x01dffc0000fff000

def z477 : W := mkw 0x483ac422948a51a4 0x60028402dc0b71b0

def z478 : W := mkw 0xbe00109d6f1012df 0xfe20003fff0003ff

def z479 : W := mkw 0x0000080000208000 0x01dc780000f08000

def z480 : W := mkw 0x189a7fae7fb8d38c 0x19fe7ffe3ff8f38c

def z481 : W := mkw 0x18105c2e3430d38c 0x18607c3e3c00f38c

def z482 : W := mkw 0xc02f803780de0360 0x81bd003d00f40240

def z483 : W := mkw 0x004fe74000cf6c00 0x000387c0000f7c00

def z484 : W := mkw 0x0040234000012c00 0x000003c000000c00

def z485 : W := mkw 0x004fef400021ec00 0x01cfffc00000fc00

def z486 : W := mkw 0x6a2a80e2cd8b35b5 0xff7387c3ff0fffff

def z487 : W := mkw 0x0045a30000460800 0x0000000000000000

def z488 : W := mkw 0x1000180c20308208 0x008c783c00f00000

def z489 : W := mkw 0x848ff7bbfb440842 0x87efffffff040c43

def z490 : W := mkw 0x9c5fff7f36ffffce 0x9fffffff3fffffcf

def z491 : W := mkw 0x100a5c0c20b8c208 0x19fe7c3c20f8f20c

def z492 : W := mkw 0xc0afc5b7d9de0360 0xe1bf85ffdcff03f0

def z493 : W := mkw 0xc42fa23782de0b62 0xe7bf823fc3ff0ff3

def z494 : W := mkw 0x2a0000c04d013495 0xe13385c3dc0f73f0

def z495 : W := mkw 0x140010082200000a 0x1e0000002300000f

def z496 : W := mkw 0x18105c083420d08c 0x19727c023c08f38c

def z497 : W := mkw 0x8405221102440842 0x9f71020123048e4f

def z498 : W := mkw 0x0000004000012400 0x9f7387c1230ffe4f

def z499 : W := mkw 0x1000180820208008 0x184078002000800c

def z500 : W := mkw 0x2a0000c04d013495 0x9f7107c13f04fe4f

def z501 : W := mkw 0xaa0500d54d5536d5 0xffff87ffffffffff

def z502 : W := mkw 0x0000102a30000000 0x0020003e3c000000

def z503 : W := mkw 0x0080103bb2000000 0x0000003c00000000

def z504 : W := mkw 0x181a5c2e34b8d38c 0x18ac783e3cf0038c

def z505 : W := mkw 0x8000000400540240 0x8010000000f40240

def z506 : W := mkw 0x0810440014005084 0x000004001c007000

def z507 : W := mkw 0x181a542e3410138c 0x19ee7c3e3c00038c

def z508 : W := mkw 0xc02f800400de0360 0xe19f800000ff03f0

def z509 : W := mkw 0x2a0000804d001095 0xff720403ff08f3ff

def z510 : W := mkw 0xea6feff7cdfffff5 0xffffffffffffffff

def z511 : W := mkw 0x9405081500748a4a 0x9fbd003d00f48e4f

def z512 : W := mkw 0x2a00004004013495 0xff710201230fffff

def z513 : W := mkw 0x9400181d2230824a 0x9ffc783d23f0824f

def z514 : W := mkw 0x948fff3fb2748a4a 0x9ffd7a3d23f48e4f

def z515 : W := mkw 0x948fff3fb2748a4a 0x008c783c00f00000

def z516 : W := mkw 0x3e003ac86f21bc9f 0x1e407fc03f00fc0f

def z517 : W := mkw 0x181a5c2a34a8d18c 0x18427c023c08f18c

def z518 : W := mkw 0x008fe791cb000000 0x01cfffc1c3000000

def z519 : W := mkw 0x94053a1d22748a4a 0x9eac783d23f0024f

def z520 : W := mkw 0x0800000004001084 0x9f7306033f0cffcf

def z521 : W := mkw 0x0005001100000000 0x01ad003d00000000

def z522 : W := mkw 0x144fff4822efec0a 0x1fdfffc023fffc0f

def z523 : W := mkw 0x0000004000012400 0xe17387c3c00ffff0

def z524 : W := mkw 0x2a0532d96f013495 0xffffffffff0fffff

def z525 : W := mkw 0x2a1a44e25d897595 0xff7387c3ff0fffff

def z526 : W := mkw 0x0800000004001084 0x184004003c00f00c

def z527 : W := mkw 0x0000101922000000 0x0020003d23000000

def z528 : W := mkw 0x004acd4000efec00 0x001285c000fffc00

def z529 : W := mkw 0xfa3fdcfffdfff7fd 0xffffffffffffffff

def z530 : W := mkw 0xc02fcc3780fec360 0xe1fffc3fc0fff3f0

def z531 : W := mkw 0x9c157e1d3674dace 0x9ffd7e3d3ff4fe4f

def z532 : W := mkw 0x008000a2d9000000 0x00000002dc000000

def z533 : W := mkw 0x0000000000000000 0x0161020123000000

def z534 : W := mkw 0x004fe740008b6400 0x01cfffc0000b7000

def z535 : W := mkw 0x000a440000000000 0x01ce7c0000000000

def z536 : W := mkw 0x1010080400b8c308 0x0000000000f00000

def z537 : W := mkw 0x1000080400308208 0x1810000000f0820c

def z538 : W := mkw 0x94053a192264884a 0x9e417a0123048c4f

def z539 : W := mkw 0x2a00004004013495 0xff5387c0000fffff

def z540 : W := mkw 0xd8bfffbffffed3ec 0xf9fffffffffff3fc

def z541 : W := mkw 0x94053a1d22748a4a 0x9e9c783c00f48e4f

def z542 : W := mkw 0xd420080400fe8b6a 0xfe10000000ff8fff

def z543 : W := mkw 0x8445a35102472c42 0x860183c103070c43

def z544 : W := mkw 0xfe2fbaffefffbfff 0xffffffffffffffff

def z545 : W := mkw 0x00cff7fbfb8b6400 0x01efffffff0b7000

def z546 : W := mkw 0xc025003780540360 0xe1bd003fc0f403f0

def z547 : W := mkw 0x0000004000012400 0x00100000000ffc00

def z548 : W := mkw 0xc02f807780df2760 0xe1ff87ffc0fffff0

def z549 : W := mkw 0x2a00004004013495 0xff338003c00fffff

def z550 : W := mkw 0x089ac5a2dd885184 0x000285c2dc087180

def z551 : W := mkw 0x0000008049000000 0x004007c03f000000

def z552 : W := mkw 0x0000000000000000 0x60028002c00b01b0

def z553 : W := mkw 0x000f803380000000 0x008c003c00000000

def z554 : W := mkw 0x008ff73bb2000000 0x01aff83fc0000000

def z555 : W := mkw 0x0000000000000000 0xe0200003c00003f0

def z556 : W := mkw 0x181a5cae7db8d38c 0x19fffffffff8f38c

def z557 : W := mkw 0xbe053a9d6f749adf 0xfffd7a3ffff48fff

def z558 : W := mkw 0x0080770832000000 0x0000780000000000

def z559 : W := mkw 0x000a000000880000 0x019e000000f80000

def z560 : W := mkw 0x081a4c2214a8d184 0x01de7c021cf8f180

def z561 : W := mkw 0x0800000004001084 0x000204021c087180

def z562 : W := mkw 0x941f7e3f32fccb4a 0x9ffd7a3d23f48e4f

def z563 : W := mkw 0x941f7e3f32fccb4a 0x008c783c00f00000

def z564 : W := mkw 0x00cffffbfb21ec00 0x01efffffff00fc00

def z565 : W := mkw 0x109fff3fb2b8c308 0x008c783c00f00000

def z566 : W := mkw 0x18907f887f20d08c 0x18407fc03f00f00c

def z567 : W := mkw 0x0000000000000000 0x9e10000000048e4f

def z568 : W := mkw 0xd830103fb41013ec 0xf820003ffc0003fc

def z569 : W := mkw 0x105fff2e30fecb08 0x008c783c00f00000

def z570 : W := mkw 0x00052a0000648800 0x008c780000f00000

def z571 : W := mkw 0x00cfff7bb2efec00 0x01dffffc00fffc00

def z572 : W := mkw 0x0800000004001084 0x182000023c00038c

def z573 : W := mkw 0x181fff2e34b8d38c 0x19fffffe3cf8f38c

def z574 : W := mkw 0x94053a1d22748a4a 0x1ecc7a3c23f08c0f

def z575 : W := mkw 0x00002a0000208800 0x00407a0000008c00

def z576 : W := mkw 0x004fff6a30efec00 0x01fffffe3cfffc00

def z577 : W := mkw 0x080000804d001084 0x197387c3ff08f38c

def z578 : W := mkw 0x008fa3b3cb000000 0x01af83ffc3000000

def z579 : W := mkw 0x101a5c2e30b8c308 0x01be783e00f80380

def z580 : W := mkw 0x14053a082264880a 0x1fdd7a0023f48c0f

def z581 : W := mkw 0x2a0000c04d013495 0x7e4287c2ff0bfdbf

def z582 : W := mkw 0x9400101d2210024a 0x0000003c00000000

def z583 : W := mkw 0xc025801180460060 0x0000000000000000

def z584 : W := mkw 0x0000000400980300 0x0010000000f80380

def z585 : W := mkw 0xea2f807784df37f5 0xffbf803fc0ffffff

def z586 : W := mkw 0x0000540830000000 0x00407c003c000000

def z587 : W := mkw 0x0000320822000000 0x00407a0023000000

def z588 : W := mkw 0x3a1008c44db9f79d 0xff7387c3ffffffff

def z589 : W := mkw 0x0000000000000000 0xe0100000000f03f0

def z590 : W := mkw 0x8005001100440040 0x8001000100040040

def z591 : W := mkw 0x2a4ac5c04d8b7495 0x600285c2dc0b71b0

def z592 : W := mkw 0x2a8ac5e2dd013495 0xff7387c3ff0fffff

def z593 : W := mkw 0x084fef4004effc84 0x19ffffc23cffff8c

def z594 : W := mkw 0x0000000000000000 0x197000002000820c

def z595 : W := mkw 0x3a0018cc6d31b69d 0xffffffffffffffff

def z596 : W := mkw 0xc02a8037809a0360 0xe022803fc00b03f0

def z597 : W := mkw 0x189addaefdb8d38c 0x19fefdfefcf8f38c

def z598 : W := mkw 0x0000000000000000 0x01238003c0000000

def z599 : W := mkw 0x2a00004004013495 0x60000000000b71b0

def z600 : W := mkw 0x004fef4000efec00 0x008dfbc000f70c00

def z601 : W := mkw 0x088ff7bbff001084 0x19ffffffff08f38c

def z602 : W := mkw 0x0045a34000472c00 0x015387c0000ffc00

def z603 : W := mkw 0x089ff7bbff885184 0x01efffffff087180

def z604 : W := mkw 0xc02faa3780fe8b60 0xe1fffa3fc0ff8ff0

def z605 : W := mkw 0xc06fc57780df6760 0xe1bf85ffc0ff73f0

def z606 : W := mkw 0x0085a31182000000 0x0000000000000000

def z607 : W := mkw 0x0040084000efec00 0x015387c000fffc00

def z608 : W := mkw 0x008ff73bb2000000 0x01ee7c3e3c000000

def z609 : W := mkw 0x14003a082220880a 0x9f717a0123048e4f

def z610 : W := mkw 0x189fffbbff20d08c 0x19efffffff00f00c

def z611 : W := mkw 0x0000004000012400 0x000183c000070c00

def z612 : W := mkw 0x9005181d20748248 0x99fd783d20f4824c

def z613 : W := mkw 0x000a4c2600b8c300 0x01fe7c3e00f8f380

def z614 : W := mkw 0x2a0000c04d013495 0xfe1183c1c30fffff

def z615 : W := mkw 0x181a5c2e34b8d38c 0x189c783c00f8f38c

def z616 : W := mkw 0x1810180c24b8d38c 0x19fc783c20f8f38c

def z617 : W := mkw 0x9400080400748a4a 0x0000000000f00000

def z618 : W := mkw 0x00452a4000efec00 0x01dd7a0000fffc00

def z619 : W := mkw 0x0000000400100200 0x01bc003c00f00200

def z620 : W := mkw 0x9c1f7e3f36fcdbce 0x19fe7c3e3cf8f38c

def z621 : W := mkw 0x0000008049000000 0x000285c2dc000000

def z622 : W := mkw 0x000f803380ce0000 0x01bf803fc0ff0000

def z623 : W := mkw 0x148fffbbfb20880a 0x1fefffffff008c0f

def z624 : W := mkw 0x008fc5b3d9000000 0x01af85ffdc000000

def z625 : W := mkw 0x00c07fc87b21ec00 0x00407fc03f00fc00

def z626 : W := mkw 0x18105c0c34b8d38c 0x18507c003cf8f38c

def z627 : W := mkw 0x000f763b32000000 0x01ef7e3f3f000000

def z628 : W := mkw 0x0000000000000000 0x01138000000f0000

def z629 : W := mkw 0x2245a3c049472c11 0xe60183c1c3070c73

def z630 : W := mkw 0x1c1a7e2e36b8db8e 0x1ffe7e3e3ff8ff8f

def z631 : W := mkw 0x8005001500540240 0x9ffd023d23f48e4f

def z632 : W := mkw 0x981f5c3f34fcd3cc 0x99ff7c3f3cfcf3cc

def z633 : W := mkw 0xd87fff7fb4ffffec 0xf9fffffffcfffffc

def z634 : W := mkw 0x008fffbbfb648800 0x01fffffffff48c00

def z635 : W := mkw 0x10105c083020c008 0x0000780000000000

def z636 : W := mkw 0x0000000000000000 0x8131000100040240

def z637 : W := mkw 0x2a0000804d001095 0xff6387c3ff0003ff

def z638 : W := mkw 0x220000c049012411 0xe75387c1c30ffc73

def z639 : W := mkw 0x0040454000016400 0x000005c000007000

def z640 : W := mkw 0x008ff7bbfb000000 0x008dfbfdc3000000

def z641 : W := mkw 0x185a5c6e34ffff8c 0x19fe7c3e3cffff8c

def z642 : W := mkw 0x0040080000eec800 0x0000000000f00000

def z643 : W := mkw 0x8485a391cb440842 0x860183c1c3040c43

def z644 : W := mkw 0x2a0a00e64d993795 0xffff87ffffffffff

def z645 : W := mkw 0x8405221502540a42 0x87bd023d03f40e43

def z646 : W := mkw 0x9400181d22748a4a 0x9e30003d23f48e4f

def z647 : W := mkw 0x000fe73380000000 0x01efffffc0000000

def z648 : W := mkw 0x406ac562808b6520 0x600285c2c00b71b0

def z649 : W := mkw 0x402a8022808a0120 0xe1338003c00f03f0

def z650 : W := mkw 0x2a00000004001095 0xfe000000000003ff

def z651 : W := mkw 0x000f802600de0300 0x01bf803e00ff0380

def z652 : W := mkw 0x8400000000440842 0x8600000000040c43

def z653 : W := mkw 0x0000000000000000 0xff738203e30f8fff

def z654 : W := mkw 0x14003a082220880a 0x0000780000000000

def z655 : W := mkw 0x00800091cb000000 0x00000001c3000000

def z656 : W := mkw 0x2a8010bbff001095 0xfe20003fff0003ff

def z657 : W := mkw 0xea2580d1cd4734f5 0xff7387c3ff0fffff

def z658 : W := mkw 0x2a0000c04d013495 0x615387c2dc0ffdb0

def z659 : W := mkw 0x0000000000000000 0x8601020103040c43

def z660 : W := mkw 0x000f804000cf2400 0x01df87c000fffc00

def z661 : W := mkw 0xc06fef3780fecb60 0xe1bff83fc0ff03f0

def z662 : W := mkw 0x94003a1d22308a4a 0x9e607a3d23008e4f

def z663 : W := mkw 0xc020000400100360 0xe0000000000003f0

def z664 : W := mkw 0xd4253a3fa2748b6a 0xfffd7a3fe3f48fff

def z665 : W := mkw 0x94053a9d6b748a4a 0x9ffffffffff48e4f

def z666 : W := mkw 0x000fe70000ce0000 0x01dfffc000ff0000

def z667 : W := mkw 0x000f6e0000ecc800 0x01df7e0000fcfc00

def z668 : W := mkw 0xdc3ffe3fb6fedbee 0xfffffe3fffffffff

def z669 : W := mkw 0x944fff1d22feca4a 0x9ffd7a3d23f48e4f

def z670 : W := mkw 0x944fff1d22feca4a 0x008c783c00f00000

def z671 : W := mkw 0xeaaff7ffffdf37f5 0xffffffffffffffff

def z672 : W := mkw 0x9400180c20748a4a 0x9ffc783c20f48e4f

def z673 : W := mkw 0x0005321922000000 0x9ffd7a3d23048e4f

def z674 : W := mkw 0x220000c049012411 0xe73383c3c30f0ff3

def z675 : W := mkw 0x9405101d2254024a 0x9fbd003d23f4024f

def z676 : W := mkw 0x2a0000804d001095 0xff710203ff048fff

def z677 : W := mkw 0x000a442210000000 0x000204021c000000

def z678 : W := mkw 0x008532bbfb000000 0x01ed7a3fff000000

def z679 : W := mkw 0x6a2a80e2cd8b35b5 0x600285c2dc0b71b0

def z680 : W := mkw 0x004aef4000abec00 0x0042ffc0000bfc00

def z681 : W := mkw 0x9c1a5c3f36b8d3ce 0x9ffe7c3f3ff8f3cf

def z682 : W := mkw 0x94053a1d22748a4a 0x868d7a3d03f40c43

def z683 : W := mkw 0x2a0000c04d013495 0x1f7207c23f08ff8f

def z684 : W := mkw 0xc06fa37780df2f60 0xe1bf83ffc0ff0ff0

def z685 : W := mkw 0xd420103fa210036a 0xfe20003fe30003ff

def z686 : W := mkw 0x2a0fe7c04d013495 0xffffffc3ff0fffff

def z687 : W := mkw 0xbe053add6f75bedf 0x9ffd7ffd3ff4fe4f

def z688 : W := mkw 0x2a8077c87f013495 0xff73ffc3ff0fffff

def z689 : W := mkw 0x8405221102440842 0x0000000000000000

def z690 : W := mkw 0x008ff7bffb980300 0x01fffffffff80380

def z691 : W := mkw 0x2acffffbffeffc95 0xffffffffffffffff

def z692 : W := mkw 0x000f800000ce0000 0x008c000000f00000

def z693 : W := mkw 0x000000c049012400 0x017387c3ff0ffc00

def z694 : W := mkw 0x940fba1d22fe8a4a 0x9ffffa3d23ff8e4f

def z695 : W := mkw 0x101a5c2e30b8c308 0x01ee7c3e3cf00000

def z696 : W := mkw 0xd42fba3fa2fe8b6a 0xe1bff83fc0ff03f0

def z697 : W := mkw 0x004fef0000eec800 0x01dd7a0000f48c00

def z698 : W := mkw 0x008f90bbfb000000 0x01af803fff000000

def z699 : W := mkw 0x2a4fefc04deffc95 0x1fdfffc03ffffc0f

def z700 : W := mkw 0x2a052ac04d65bc95 0xffffffc3ffffffff

def z701 : W := mkw 0x000f80b3c9000000 0x01ef87ffff000000

def z702 : W := mkw 0x1810182e34b8d38c 0x1830003e3cf8f38c

def z703 : W := mkw 0x9c153a3f36749bce 0x9ffd7a3f3ff48fcf

def z704 : W := mkw 0x1810102e3410138c 0x1972043e3c08f38c

def z705 : W := mkw 0x185fef4404ffff8c 0x19dfffc000ffff8c

def z706 : W := mkw 0xd42f883780fe8b6a 0xffbf803fc0ff8fff

def z707 : W := mkw 0x008577997b000000 0x01efffffff000000

def z708 : W := mkw 0xc0606f778031ef60 0xe0607fffc000fff0

def z709 : W := mkw 0x00cff7bbfb460800 0x01efffffff000000

def z710 : W := mkw 0x008ff7bbfb880000 0x01fffffffff80000

def z711 : W := mkw 0x40aff7bbfbce0120 0x61ffffffffff01b0

def z712 : W := mkw 0x9400088449748a4a 0x9f7387c3fff48e4f

def z713 : W := mkw 0x948acda6d9748a4a 0x9e1285c2dcf48e4f

def z714 : W := mkw 0x004aef4000abec00 0x01deffc000fbfc00

def z715 : W := mkw 0xbe053add6f75bedf 0x608efdfedcfb71b0

def z716 : W := mkw 0x6a6ac5e2cd8b75b5 0x600285c2dc0b71b0

def z717 : W := mkw 0x004fef4000efec00 0x01ffffc123fffc00

def z718 : W := mkw 0x080a542e34981384 0x19fe7c3e3cf8f38c

def z719 : W := mkw 0xc02f803780de0360 0x619f803ec0ff01b0

def z720 : W := mkw 0xea2f80f7cddf37f5 0x1ecc07fc3ff0fc0f

def z721 : W := mkw 0x406fef6280efed20 0x01dfffc000fffc00

def z722 : W := mkw 0x004fef5102efec00 0x01dfffc103fffc00

def z723 : W := mkw 0xc0a0778c7bde0360 0xe0507fc03fff03f0

def z724 : W := mkw 0x94053a1d22748a4a 0x9ebc783d23f48e4f

def z725 : W := mkw 0x004fef4000abe400 0x01dfffc000fbf000

def z726 : W := mkw 0x004fef4000efec00 0x008fffc000ff7c00

def z727 : W := mkw 0x1855b36e34573f8c 0x182183fe3c070f8c

def z728 : W := mkw 0x2a4fef804deed895 0xfeac7803fff003ff

def z729 : W := mkw 0xbe8010bfff1012df 0xfe20003fff0003ff

def z730 : W := mkw 0x008ff7bbfb000000 0x01affdffdc000000

def z731 : W := mkw 0x004acd4000abe400 0x01dfffc000fffc00

def z732 : W := mkw 0x3a507fc87d21fc9d 0x1e407fc03f00fc0f

def z733 : W := mkw 0xd4253a1da2748a6a 0xfffd7a3de3f48e7f

def z734 : W := mkw 0x583a5c2e34bad3ac 0x79fe7c3e3cfbf3bc

def z735 : W := mkw 0xc025803780560360 0xe1bd803fc0f703f0

def z736 : W := mkw 0x1810084404b9f78c 0x1810000000ffff8c

def z737 : W := mkw 0xd8b010bfff1013ec 0xf820003fff0003fc

def z738 : W := mkw 0x00c018fbfbefec00 0x0030003ffffffc00

def z739 : W := mkw 0x9c50084404ffffce 0x9e10000000ffffcf

def z740 : W := mkw 0x8c1f663316cc59c6 0x860306031f0c7dc3

def z741 : W := mkw 0x008ff7bbfb000000 0x1fefffffff008c0f

def z742 : W := mkw 0x3a9010bfff10139d 0xfe20003fff0003ff

def z743 : W := mkw 0x000008400021a400 0x01dfffc000fffc00

def z744 : W := mkw 0x008ff7bbfb884000 0x01efffffff087000

def z745 : W := mkw 0x008ff7bbfb000000 0x00ec7fffff000000

def z746 : W := mkw 0x80052a1500748a40 0x9ffd7a3d23f48e4f

def z747 : W := mkw 0x542aba2aa2aa892a 0x7e42fa02e30b8dbf

def z748 : W := mkw 0xc02a003780980360 0xe1bf803fc0ff03f0

def z749 : W := mkw 0x9485bb1da2748a4a 0x9ffd7a3d23f48e4f

def z750 : W := mkw 0xc03fc43790de4360 0xe1bf803fc0ff03f0

def z751 : W := mkw 0x008ff7bbfb000000 0x01eefdfefc000000

def z752 : W := mkw 0x1850084404b9ff8c 0x1810000000f8ff8c

def z753 : W := mkw 0x9005181d20748248 0x9ffd7a3d23f48e4f

def z754 : W := mkw 0xc025801580560260 0xe1bf803fc0ff03f0

def z755 : W := mkw 0x18105c2e3430d38c 0x19fc7c3e3cf0f38c

def z756 : W := mkw 0x9405ba1da2748a4a 0x9ffdfa3de3f48e4f

def z757 : W := mkw 0x18105c0c34b8d38c 0x19fc7c3c3cf8f38c

def z758 : W := mkw 0xc46fef5182efec62 0xe7dfffc1c3fffc73

def z759 : W := mkw 0x181a5c2e34b8d38c 0x19fc7c3c3cf0f20c

def z760 : W := mkw 0x94053a1d22748a4a 0xfffd7a3d23ff8fff

def z761 : W := mkw 0xc42fa23782de0b62 0xe1bf803fc0ff03f0

def z762 : W := mkw 0xc02f803780de0360 0xffbf803fe3ff03ff

def z763 : W := mkw 0x3a10084404b9f79d 0x7810000000fbf3bc

def z764 : W := mkw 0x008ff7bbfb000000 0x9fefffffff00024f

def z765 : W := mkw 0x004fef4000efec00 0x019ffdc000ff7000

def z766 : W := mkw 0x2a1a44e25d897595 0x000205c21c087180

def z767 : W := mkw 0xbe1010bf7f1013df 0xfe20003fff0003ff

def z768 : W := mkw 0x008a77bbfb000000 0x01ee7fffff000000

def z769 : W := mkw 0x181a5c2e34b8d38c 0x18ce7c3e3cf8f18c

def z770 : W := mkw 0x181a5c2e34b8d38c 0x189e7c3e1cf8f38c

def z771 : W := mkw 0xc02f803780de0360 0xe7bf823fc3ff0ff3

def z772 : W := mkw 0x1895ab95cfb8d38c 0x181183c1c3f8f38c

def z773 : W := mkw 0x2a8ff77bb6013495 0xfe9c783c000fffff

def z774 : W := mkw 0xc02fc43780de0360 0xe1fffc3fc0ff03f0

def z775 : W := mkw 0x181a5c2e34b8d38c 0x01de7c3e1cf8f180

def z776 : W := mkw 0xc42fa23782de0b62 0xffff823fe3ff8fff

def z777 : W := mkw 0xc02f803780de0360 0x61be803ec0fb03b0

def z778 : W := mkw 0x181a5c2e34b8d38c 0xfffffe3fffffffff

def z779 : W := mkw 0x004fef4000efec00 0x00cdffc000f7fc00

def z780 : W := mkw 0xc06fef4000efec60 0xe1dfffc000fffc70

def z781 : W := mkw 0x004fef4000efec00 0x01ffffc3c0fffc00

def z782 : W := mkw 0x2a05325926013495 0xfffd7a3d230fffff

def z783 : W := mkw 0xc02f803780de0360 0xf9ff803fe0ff83fc

def z784 : W := mkw 0xc025003780de0360 0xe1bd003fc0ff03f0

def z785 : W := mkw 0x944ad55d229b664a 0x9e2285fd230b724f

def z786 : W := mkw 0x181a5c2e34b8d38c 0x9ffe7c3e3cfcffcf

def z787 : W := mkw 0x008ff7bbfb000000 0x01ee7ffe3f000000

def z788 : W := mkw 0xd870084404ffffec 0xf810000000fffffc

def z789 : W := mkw 0x008ad5aaf9000000 0x008efdfedc000000

def z790 : W := mkw 0xc0aff7bbfb460060 0xe1ffffffff0f03f0

def z791 : W := mkw 0x004fef6200efed00 0x01dfffc200fffd80

def z792 : W := mkw 0x9405ba1d22768a4a 0x9ffdfa3d23f78e4f

def z793 : W := mkw 0x181a5c2e3430d28c 0x19fe7c3e3cf0f20c

def z794 : W := mkw 0x848ff7bbfb440842 0x01efffffff000000

def z795 : W := mkw 0x008577bbfb000000 0x01ed7fffff000000

def z796 : W := mkw 0x94053a1d22748a4a 0x9edc7a3c23f48e4f

def z797 : W := mkw 0x0085f7bbfb000000 0x0061ffffff000000

def z798 : W := mkw 0x94053a1d22748a4a 0x1fdd7a3c23f48c0f

def z799 : W := mkw 0x004fe74000cf6400 0x01dfffc000ff7000

def z800 : W := mkw 0xfa3010bffd1013fd 0xfe20003fff0003ff

def z801 : W := mkw 0x008ff7bbfb000000 0x01ffffffff0f0000

def z802 : W := mkw 0x189010ae7f10138c 0x1820003e3f00038c

def z803 : W := mkw 0x000f803380ce0000 0xe1bf803fc0ff03f0

def z804 : W := mkw 0x080a5c2a34a8d084 0x19fe7c3e3cf8f38c

def z805 : W := mkw 0x406fef4000efed20 0x61dfffc000fffdb0

def z806 : W := mkw 0x004a6f4000a9ec00 0x01dfffc000fffc00

def z807 : W := mkw 0x000fef400065ac00 0x01dfffc000fffc00

def z808 : W := mkw 0x00456f4000efec00 0x01dd7fc000fffc00

def z809 : W := mkw 0x9400181d2230824a 0x9ffd7a3d23f48e4f

def z810 : W := mkw 0x008ff7bbfb8a0000 0x01efffffff0b0000

def z811 : W := mkw 0x2a9ac5e2dd897595 0x600285c2dc0b71b0

def z812 : W := mkw 0x8c052211064418c6 0x9f7306033f0cffcf

def z813 : W := mkw 0xd835dc19b466d0ec 0xf841fc01fc07f07c

def z814 : W := mkw 0x008ff7bbfb000000 0x00cdfffdff000000

def z815 : W := mkw 0xc02f803780de0360 0xe1ff87ffc0ff03f0

def z816 : W := mkw 0x402a8026809a0320 0xe1bf803fc0ff03f0

def z817 : W := mkw 0xc0aff7bbfbce0160 0xe1efffffff0f01f0

def z818 : W := mkw 0xc0e5a3d1cb472c60 0xe00183c1c3070c70

def z819 : W := mkw 0x004fef5180efec00 0x01dfffc1c0fffc00

def z820 : W := mkw 0x008ff7bbfb880100 0x01efffffff080180

def z821 : W := mkw 0xc020003780de0360 0xe133803fc0ff03f0

def z822 : W := mkw 0x148ff7bbfb00000a 0x1fefffffff00000f

def z823 : W := mkw 0xc0afa33782de0360 0xe1bf803fc0ff03f0

def z824 : W := mkw 0xc42f803782de0362 0xe7bf803fc3ff03f3

def z825 : W := mkw 0x008077bbfb000000 0x0163ffffff000000

def z826 : W := mkw 0x583a5c2eb4b8d3ac 0x79fe7c3efcf8f3bc

def z827 : W := mkw 0x004fef4000efec00 0x01de7fc000f8fc00

def z828 : W := mkw 0x008af7aafb000000 0x01eefffeff000000

def z829 : W := mkw 0x844fef4000efec42 0x87dfffc000fffc43

def z830 : W := mkw 0xc02fa23782de0360 0xe1bf823fc3ff03f0

def z831 : W := mkw 0x004fef4000efec00 0xe1dfffc1c0fffc70

def z832 : W := mkw 0xc025803780de0360 0xe031803fc0ff03f0

def z833 : W := mkw 0x181a5c2e34b8d38c 0x19fffc3e3cfff38c

def z834 : W := mkw 0x008ff7bbfb440000 0x01fffffffff40000

def z835 : W := mkw 0x181a5c2e34b8d38c 0xf9fe7c3e3cfff3fc

def z836 : W := mkw 0x008ff7bbfb000000 0xffffffffff0f8fff

def z837 : W := mkw 0x008ff7aaf9000000 0x01effffefc000000

def z838 : W := mkw 0x008ff7bbfb000000 0xe1efffffff0003f0

def z839 : W := mkw 0x0045ef4000efec00 0x0051ffc000fffc00

def z840 : W := mkw 0x004fef4000efec00 0x01cfffc000fb7000

def z841 : W := mkw 0x6aaac5e2dd8b35b5 0x600285c2dc0b71b0

def z842 : W := mkw 0x14003a0c22308a0a 0x1ecc7a3c23f08c0f

def z843 : W := mkw 0xbe40084404fffedf 0xfe10000000ffffff

def z844 : W := mkw 0x181a5c2e34b8d38c 0x19de7c3c3cf8f00c

def z845 : W := mkw 0x000f6e4000edec00 0x01dfffc000fffc00

def z846 : W := mkw 0x6a3ac4e2dd8b75b5 0x600285c2dc0b71b0

def z847 : W := mkw 0x000f802600de0300 0xe1bf803fc0ff03f0

def z848 : W := mkw 0x40aff7bbfb000120 0x61efffffff0001b0

def z849 : W := mkw 0x181a5c2e34b8d38c 0x19ff7e3f3ff8f38c

def z850 : W := mkw 0x94053a1d22748a4a 0xfffdfa3de3f78e7f

def z851 : W := mkw 0x000a002600980300 0x61be803ec0fb03b0

def z852 : W := mkw 0x0045ab400067ac00 0x01dfffc000fffc00

def z853 : W := mkw 0x000a4c4000a9e400 0x01de7fc000f8fc00

def z854 : W := mkw 0x000a6f0000a8c000 0x01de7fc000f8f000

def z855 : W := mkw 0x0000108869000000 0x01efffffff000000

def z856 : W := mkw 0x808ff7bbfb440040 0x81efffffff040040

def z857 : W := mkw 0xc0aff7bbfbce0060 0xe1ffffffffff0070

def z858 : W := mkw 0xc025003780540360 0xe1bf803fc0ff03f0

def z859 : W := mkw 0x000a5c2e30b8c300 0x01fe7c3e3cf8f380

def z860 : W := mkw 0x008a55aa79000000 0x01ee7dfe3c000000

def z861 : W := mkw 0x008ff7bbfb000000 0x01cffffc3f000000

def z862 : W := mkw 0x000acd0000a8c000 0x01defdc000f8f000

def z863 : W := mkw 0x008ff7bbfb000000 0x00adfbffff000000

def z864 : W := mkw 0x848ff7bbfb000042 0x87efffffff000043

def z865 : W := mkw 0xeaa010bfff1013f5 0xfe20003fff0003ff

def z866 : W := mkw 0x94053a1d22748a4a 0x9ead7a3d23f40e4f

def z867 : W := mkw 0x004fef0000eec800 0x01dfffc000f8f000

def z868 : W := mkw 0x008ff7bbfb000000 0x01ffffffff080380

def z869 : W := mkw 0x004a6f4000a9ec00 0x00cc7fc000f0fc00

def z870 : W := mkw 0x406fef7380efed20 0x61ffffffc0fffdb0

def z871 : W := mkw 0xc02fc43790de0360 0xe1bf843fdcff03f0

def z872 : W := mkw 0x224fef4000efec11 0xe7dfffc000fffc73

def z873 : W := mkw 0x000fef4000a9e400 0x01dfffc000fffc00

def z874 : W := mkw 0x009ff7bbfb884100 0x01efffffff000000

def z875 : W := mkw 0xc4aff7bbfb460862 0xe7efffffff070c73

def z876 : W := mkw 0x181a5c2e34b8d38c 0x18dc7c3c3cf8f38c

def z877 : W := mkw 0x800f803780540240 0xe1bf803fc0ff03f0

def z878 : W := mkw 0x00452a4000efec00 0x01dfffc000fffc00

def z879 : W := mkw 0x189add2eb4b8d38c 0x19fe7c3e3cf8f38c

def z880 : W := mkw 0x1c1a5c2e34b8db8e 0x1ffe7c3e3cf8ff8f

def z881 : W := mkw 0x008ff7bbfb000000 0x01ffffffff08f000

def z882 : W := mkw 0x0085f799fb000000 0x01edfffdff000000

def z883 : W := mkw 0x321a5cee79b9e719 0xe68dfbfdc3f70c73

def z884 : W := mkw 0x3a1010ae7d10139d 0x7820003efc0003bc

def z885 : W := mkw 0xc0aff7bbfb000060 0xe1efffffff000070

def z886 : W := mkw 0xe265a3d1c9472c71 0xe60183c1c3070c73

def z887 : W := mkw 0x008fe7b3d9000000 0x01efffffdc000000

def z888 : W := mkw 0x40aff7bbfb8a0120 0x01efffffff000000

def z889 : W := mkw 0x000a4c0000a8c000 0x01dfffc000f8f000

def z890 : W := mkw 0x100a5c2e30b8c208 0x19fe7c3e3cf8f20c

def z891 : W := mkw 0x004fef4000efec00 0x61dfffc2c0fffdb0

def z892 : W := mkw 0x180a5c0c24b8d28c 0x19fe7c3e3cf8f38c

def z893 : W := mkw 0x080a4c2604b8d384 0x19fe7c3e3cf8f38c

def z894 : W := mkw 0x008577997b000000 0x00cc7ffc3f000000

def z895 : W := mkw 0x94053a1d22748a4a 0x9fff7e3f3ff48e4f

def z896 : W := mkw 0x320018cc6931a619 0xfffdfbfde3f78e7f

def z897 : W := mkw 0x004a4d4000a9e400 0x01de7dc000f8f000

def z898 : W := mkw 0x9c1a5c2e34b8d3ce 0x9ffe7c3e3cf8f3cf

def z899 : W := mkw 0x008af7bbfb000000 0x0062ffffff000000

def z900 : W := mkw 0x3a00108c6d10129d 0xfe20003fff0003ff

def z901 : W := mkw 0x10053a0c20748a08 0x9ffd7a3d23f48e4f

def z902 : W := mkw 0x000f803780980300 0xe1bf803fc0ff03f0

def z903 : W := mkw 0xd425ba1da2768a6a 0x9ffd7a3d23f48e4f

def z904 : W := mkw 0x00406f4000efec00 0x0153ffc000fffc00

def z905 : W := mkw 0x94053a1d22748a4a 0x9fff7a3f23fc8fcf

def z906 : W := mkw 0x0000000400100200 0xe1bf803fc0ff03f0

def z907 : W := mkw 0x004fef5100efec00 0x01fffffd00fffc00

def z908 : W := mkw 0x18105c0c3430d28c 0x18cc7c3c3cf0f00c

def z909 : W := mkw 0x3e407fc86f21fc9f 0x1e407fc03f00fc0f

def z910 : W := mkw 0xc02f803780de0360 0xe08f803fc0ff01f0

def z911 : W := mkw 0xc02f803780de0360 0xe09e803ec0ff03f0

def z912 : W := mkw 0x800f003700dc0340 0xe1bf803fc0ff03f0

def z913 : W := mkw 0x008ff7bbfb000000 0x008c7dfc1c000000

def z914 : W := mkw 0xc02a003780de0360 0xe1be003fc0ff03f0

def z915 : W := mkw 0x0045ab4000efec00 0x01ddfbc000fffc00

def z916 : W := mkw 0xc02a802680de0360 0xe1be803ec0ff03f0

def z917 : W := mkw 0x18105c0c3430d28c 0x19fe7c3e3cf8f38c

def z918 : W := mkw 0xc02f803780de0360 0xe1ff823fc0ff8ff0

def z919 : W := mkw 0x008ff7bbfb000000 0x01ffffffff048c00

def z920 : W := mkw 0x181a5c0c34b8d28c 0x19fe7c3c3cf8f20c

def z921 : W := mkw 0x000fd4bbf9000000 0x01efffffff000000

def z922 : W := mkw 0x004fef7380efec00 0xe1ffffffc0fffff0

def z923 : W := mkw 0x000532996b000000 0x01ed7ffd3f000000

def z924 : W := mkw 0x181a5c2e34b8d38c 0x18ae7c3e3cf8738c

def z925 : W := mkw 0x008ff7bbfbce0000 0xe1ffffffffff03f0

def z926 : W := mkw 0x180a5c2e3430928c 0x19fe7c3e3cf8f38c

def z927 : W := mkw 0xc02fc53780de0360 0xe1bf85ffc0ff03f0

def z928 : W := mkw 0xc02f803780de0360 0xe1ff843fc0fff3f0

def z929 : W := mkw 0x008ff7bbfb460000 0x01efffffff070000

def z930 : W := mkw 0x004fef6280efec00 0x01dfffc2c0fffc00

def z931 : W := mkw 0x40aff7bbfb020020 0x61efffffff030030

def z932 : W := mkw 0xc06fef5180efec60 0xe1ffffc3c0fffff0

def z933 : W := mkw 0xc025801580de0360 0xe1bd803dc0ff03f0

def z934 : W := mkw 0x94003a0c22748a4a 0x9ffc7a3c23f48e4f

def z935 : W := mkw 0xc02f803780de0360 0xe09d803dc0ff03f0

def z936 : W := mkw 0x844fef5102efec42 0x01dfffc000fffc00

def z937 : W := mkw 0x84c5a3d1cb472c42 0x860183c1c3070c43

def z938 : W := mkw 0x14053a192264880a 0x1ffd7a3d23f48c0f

def z939 : W := mkw 0x008a77aa7b000000 0x01efffffff000000

def z940 : W := mkw 0x008ff7bbfb000000 0x81ffffffff040240

def z941 : W := mkw 0x1c1a5c2e36b8d38e 0x1ffe7c3e3ff8f38f

def z942 : W := mkw 0x004fef4000efec00 0x9fdfffc000fffe4f

def z943 : W := mkw 0xc0aff7bbfb460060 0x01efffffff000000

def z944 : W := mkw 0x004fef4000efec00 0x008c7dc000f07000

def z945 : W := mkw 0x804fef5100efec40 0x81dfffc100fffc40

def z946 : W := mkw 0xc02a803780de0360 0xe032803fc0ff03f0

def z947 : W := mkw 0xa645a3d14b472c53 0xe60183c1c3070c73

def z948 : W := mkw 0xc025001500de0360 0xe1bf803fc0ff03f0

def z949 : W := mkw 0x94053a1d22748a4a 0x9e9d7a3d03f48e4f

def z950 : W := mkw 0xc02f803780de0360 0xe0ad803fc0f703f0

def z951 : W := mkw 0x00406f4000efec00 0x00407fc000f0fc00

def z952 : W := mkw 0x008ff7bbfbce0000 0x01effffffff00000

def z953 : W := mkw 0xd42f803780de036a 0xffbf803fc0ff03ff

def z954 : W := mkw 0xc06fc53780de4360 0xe1bf803fc0ff03f0

def z955 : W := mkw 0xc02a002600de0360 0xe1bf803fc0ff03f0

def z956 : W := mkw 0x008ff7aa7b000000 0x01effffe3f000000

def z957 : W := mkw 0xc02f803780de0360 0xe0ae803fc0fb03f0

def z958 : W := mkw 0x008ff7bbfb440800 0x01efffffff040c00

def z959 : W := mkw 0x1000180c20308208 0x1ffc7a3c23f08e0f

def z960 : W := mkw 0x004fef6210efec00 0x01dfffc21cfffc00

def z961 : W := mkw 0x181add2e34b8d38c 0x19fefdfe3cf8f38c

def z962 : W := mkw 0x000a772a30000000 0x01ee7ffe3c000000

def z963 : W := mkw 0x189010aefd10138c 0x1820003efc00038c

def z964 : W := mkw 0x2acac5e2dd8b7495 0x600285c2dc0b71b0

def z965 : W := mkw 0x181a5c2e34b8d38c 0xf9fe7c3ffcf8f3fc

def z966 : W := mkw 0x181a5c2e34b8d38c 0x19fffc3ffcf8f38c

def z967 : W := mkw 0x008ff7bbfb000000 0x008fffffdf000000

def z968 : W := mkw 0x0085b399eb000000 0x01efffffff000000

def z969 : W := mkw 0x000ff7aa79000000 0x01efffffff000000

def z970 : W := mkw 0x94053a1d22748a4a 0x9ffffa3d23ff8e4f

def z971 : W := mkw 0x000a54aa79000000 0x01eefdfefc000000

def z972 : W := mkw 0x9c9010bfff1013ce 0x9e20003fff0003cf

def z973 : W := mkw 0x181adc2eb4b8d38c 0x19fefc3efcf8f38c

def z974 : W := mkw 0x081a542e34985384 0x01fe7c3e3cf87380

def z975 : W := mkw 0x583adc2eb4bad3ac 0x19fe7c3e3cf8f38c

def z976 : W := mkw 0x004fef4000efec00 0x01dd7fc000f4fc00

def z977 : W := mkw 0xaa0500d54d5536d5 0x9ffd07fd3ff4fe4f

def z978 : W := mkw 0x9400180c20748a4a 0x9ffd7a3d23f48e4f

def z979 : W := mkw 0x94053a1d22748a4a 0x9ffffa3fe3f48e4f

def z980 : W := mkw 0x000ad52a30000000 0x01eefdfe3c000000

def z981 : W := mkw 0x081a4c2614b8d384 0x01fe7c3e1cf8f380

def z982 : W := mkw 0x94053a1d22748a4a 0x9eec7a3d23f08e4f

def z983 : W := mkw 0x004fef4000efec00 0x01ffffc23cfffc00

def z984 : W := mkw 0xc02fe73780de0360 0xe1bff83fc0ff03f0

def z985 : W := mkw 0x94053a1d22748a4a 0x1fed7a3d23f08c0f

def z986 : W := mkw 0x406fef4080efec20 0x61dfffc0c0fffc30

def z987 : W := mkw 0xc02a8037809a0360 0xe1be803fc0fb03f0

def z988 : W := mkw 0x008532bbfb000000 0x01efffffff000000

def z989 : W := mkw 0x1810180c24b8d38c 0x19fe7c3e3cf8f38c

def z990 : W := mkw 0x40aff7bbfb8a0120 0xe1ffffffff0f03f0

def z991 : W := mkw 0x181a5c2e34b8d38c 0x1ffe7e3e3ff8ff8f

def z992 : W := mkw 0x10053a1d22308208 0x9ffd7a3d23f48e4f

def z993 : W := mkw 0x004fef4000efec00 0x87dfffc103fffc43

def z994 : W := mkw 0x008ff7bbfb000000 0x19ffffffff00820c

def z995 : W := mkw 0x008ff7bbfb000000 0x00cefffeff000000

def z996 : W := mkw 0x000ff7996b000000 0x01efffffff000000

def z997 : W := mkw 0x180a182e24b8938c 0x19fe7c3e3cf8f38c

def z998 : W := mkw 0xc02fa23780de0360 0xe1fffa3fc0ff03f0

def z999 : W := mkw 0x848ff7bbfb440842 0x9fffffffff048e4f

def z1000 : W := mkw 0x181a5c2a34a8d08c 0x19fe7c3e3cf8f00c

def z1001 : W := mkw 0x008ad5bbfb000000 0x01eefdffff000000

def z1002 : W := mkw 0x3a0008440431b69d 0xfe10000000ffffff

def z1003 : W := mkw 0x0045ef400067ec00 0x01ddffc000f7fc00

def z1004 : W := mkw 0xfe20084404ffbfff 0xfe10000000ffffff

def z1005 : W := mkw 0x004fef4000efec00 0x81ffffc100fffe40

def z1006 : W := mkw 0x008077bbfb000000 0x00407ffc3f000000

def z1007 : W := mkw 0x004a6f4000efec00 0x01de7fc000fffc00

def z1008 : W := mkw 0x004fef4000efec00 0xffffffc3e3ffffff

def z1009 : W := mkw 0x000a542a30000000 0x01effffe3c000000

def z1010 : W := mkw 0x000fef0000ecc800 0x01dfffc000fcfc00

def z1011 : W := mkw 0x008fd5bbf9000000 0x01effdfffc000000

def z1012 : W := mkw 0x004fef4000efec00 0x1fdfffc023fffc0f

def z1013 : W := mkw 0x081a5c2a34a8d184 0x01fe7c3e3cf8f180

def z1014 : W := mkw 0x94003a1d22308a4a 0x9ffc7a3d23f08e4f

def z1015 : W := mkw 0x3a1010ae7d10139d 0x1e20003e3f00038f

def z1016 : W := mkw 0x008a54bbfb000000 0x01efffffff000000

def z1017 : W := mkw 0x004fef4000efec00 0x01cfffc000f0fc00

def z1018 : W := mkw 0x94053a1d22748a4a 0x9fff7e3d23fcfe4f

def z1019 : W := mkw 0x005fef6210efed00 0x01dfffc000fffc00

def z1020 : W := mkw 0x004acd4000efec00 0x01defdc000fffc00

def z1021 : W := mkw 0x402f802680de0320 0x61bf803ec0ff03b0

def z1022 : W := mkw 0x004fef4000efec00 0x19ffffc020fffe0c

def z1023 : W := mkw 0x1810182e3430938c 0x19fe7c3e3cf8f38c

def z1024 : W := mkw 0x3e807fc87f21bc9f 0x1e407fc03f00fc0f

def z1025 : W := mkw 0xc02fa33780de0360 0xe1bf83ffc0ff03f0

def z1026 : W := mkw 0x000fe74000cf2400 0x01dfffc000fffc00

def z1027 : W := mkw 0x004aef4000efec00 0x0052ffc000fffc00

def z1028 : W := mkw 0x000f76bb7b000000 0x01efffffff000000

def z1029 : W := mkw 0x3e107ec87f21fc9f 0x1e407fc03f00fc0f

def z1030 : W := mkw 0x2ac07fc87f21fc95 0x1e407fc03f00fc0f

def z1031 : W := mkw 0x004fef4000efec00 0x009efdc000fffc00

def z1032 : W := mkw 0x3a105cc87d21f49d 0x18407dc03c00f00c

def z1033 : W := mkw 0x000ff73b32000000 0x01efffff3f000000

def z1034 : W := mkw 0xd425ba1da2768a6a 0xfffffa3fe3ff8fff

def z1035 : W := mkw 0x008ff7bbfb000000 0x61efffffff0b01b0

def z1036 : W := mkw 0xc06fa33780de0b60 0xe1bf803fc0ff03f0

def z1037 : W := mkw 0x008f77bb7b000000 0x01ef7fff3f000000

def z1038 : W := mkw 0xea60084404fffff5 0xfe10000000ffffff

def z1039 : W := mkw 0x181adc2e34bad38c 0x19fefc3e3cfbf38c

def z1040 : W := mkw 0x00406f4000a9ec00 0x00507fc000f8fc00

def z1041 : W := mkw 0x004f6f4000edec00 0x01df7fc000fcfc00

def z1042 : W := mkw 0x181a5c2e34b8d38c 0x008c7c3c1cf07000

def z1043 : W := mkw 0xc02f803780de0360 0xe0bc003fc0ff03f0

def z1044 : W := mkw 0x008ff73bb2000000 0x01effffe3c000000

def z1045 : W := mkw 0x004a4c4000efec00 0x01dfffc000fffc00

def z1046 : W := mkw 0x94053a1d22748a4a 0x9ffffffd23f48e4f

def z1047 : W := mkw 0xc0afc53790de0360 0xe1bf803fc0ff03f0

def z1048 : W := mkw 0x94053a1d22748a4a 0x9ecd7a3d23f48c4f

def z1049 : W := mkw 0x000fb2bbeb000000 0x01efffffff000000

def z1050 : W := mkw 0x181a5c2e34b8d38c 0x19ff7e3e3cfcff8c

def z1051 : W := mkw 0x004fef7380efec00 0x01dffffc00fffc00

def z1052 : W := mkw 0x004acd4000abe400 0x008efdc000fb7000

def z1053 : W := mkw 0x181a5c2e34b8d38c 0x01ee7c3e3cf87180

def z1054 : W := mkw 0x3a10084404b9f79d 0x1e10000000f8ff8f

def z1055 : W := mkw 0xa60522d14b452c53 0x860103c103040c43

def z1056 : W := mkw 0x402f803380ce0120 0x61bf803fc0ff01b0

def z1057 : W := mkw 0x2a052a804d649895 0xfffd7a03fff48fff

def z1058 : W := mkw 0x181a5c2e34b8d38c 0x9ffe7c3f3ff8f3cf

def z1059 : W := mkw 0x181010ae7d10138c 0x1820003fff00038c

def z1060 : W := mkw 0x181a5c2e34b8d38c 0x01be7c3e1cf87380

def z1061 : W := mkw 0x00406f400065ec00 0x00507fc000f4fc00

def z1062 : W := mkw 0x3a0018c86d21b49d 0x1e407fc03f00fc0f

def z1063 : W := mkw 0x1850084404bbf78c 0x1810000000fbf38c

def z1064 : W := mkw 0xd4253a1d22768a6a 0xfffd7a3d23f78e7f

def z1065 : W := mkw 0x402a8026809a0320 0x608e803ec0fb01b0

def z1066 : W := mkw 0xd83a5c2e34b8d3ec 0xf9fe7c3e3cf8f3fc

def z1067 : W := mkw 0xc42f803780de0b62 0xe7bf803fc0ff0ff3

def z1068 : W := mkw 0xc02fa23780de0b60 0xe1bf823fc0ff0ff0

def z1069 : W := mkw 0x00cfef5182efec00 0x01dfffc000fffc00

def z1070 : W := mkw 0x004fef4000efec00 0x00dc7fc000fffc00

def z1071 : W := mkw 0xc02f803780de0360 0xffbf803fc0ff8fff

def z1072 : W := mkw 0x004fef4000efec00 0x01ffffc200ffff80

def z1073 : W := mkw 0x00456f400065ec00 0x01dfffc000fffc00

def z1074 : W := mkw 0x008077887b000000 0x01ec7ffc3f000000

def z1075 : W := mkw 0x181a5c2e34b8d38c 0x18bc783e3cf8f38c

def z1076 : W := mkw 0x228ff7bbfb000011 0xe7efffffff000073

def z1077 : W := mkw 0x9445bb1d22768a4a 0x9ffd7a3d23f48e4f

def z1078 : W := mkw 0x008ff7bbfb000000 0x00aefdffff000000

def z1079 : W := mkw 0x14053a1d22308a0a 0x1ffd7a3d23f08e0f

def z1080 : W := mkw 0x008ff7bbfb000000 0x01ed7ffd3f000000

def z1081 : W := mkw 0xe625a2d1cb472c73 0xe60183c1c3070c73

def z1082 : W := mkw 0x9400181d22748a4a 0x9ffc783d23f48e4f

def z1083 : W := mkw 0x008ad5aaf9000000 0x01efffffff000000

def z1084 : W := mkw 0xc06fef7380efed60 0xe1dfffc3c0fffdf0

def z1085 : W := mkw 0x583adc2eb4bad3ac 0xf9fffc3ffcfff3fc

def z1086 : W := mkw 0x101a5c2e30b8c308 0x01fe7c3e3cf8f000

def z1087 : W := mkw 0x94053a1d22748a4a 0x1ffc7a3c23f08e0f

def z1088 : W := mkw 0x00406f400021ec00 0x01dc7fc000f0fc00

def z1089 : W := mkw 0x000faa4000efac00 0x01dfffc000fffc00

def z1090 : W := mkw 0x402f8037809a0320 0x61bf803fc0fb03b0

def z1091 : W := mkw 0x1810182e34b8d38c 0x19fc783e3cf8f38c

def z1092 : W := mkw 0xc02f803780de0360 0xe1ff823fe3ff03f0

def z1093 : W := mkw 0xfe2010bfef1013ff 0xfe20003fff0003ff

def z1094 : W := mkw 0x004fef4000a9ec00 0x01dfffc000f8fc00

def z1095 : W := mkw 0x004fef4000efec00 0x00ceffc000fbfc00

def z1096 : W := mkw 0x004fef4000efec00 0x009dfbc000fffc00

def z1097 : W := mkw 0xa685a3d1cb452c53 0xe60183c1c3070c73

def z1098 : W := mkw 0x3a1a5c2e34b8d39d 0xfffe7c3e3cf8f3ff

def z1099 : W := mkw 0x00053a1922648800 0x9ffd7a3d23f48e4f

def z1100 : W := mkw 0x3a50084404ffff9d 0xfe10000000ffffff

def z1101 : W := mkw 0x004fef4000efec00 0xe1dfffc000fffff0

def z1102 : W := mkw 0x000fcc4000efe400 0x01dfffc000fffc00

def z1103 : W := mkw 0xc06fef5180efec60 0x01dfffc000fffc00

def z1104 : W := mkw 0xd4253a1d22748b6a 0xfffd7a3d23f48fff

def z1105 : W := mkw 0x0085b3bbfb000000 0x01edfbffff000000

def z1106 : W := mkw 0x000fef0000eec000 0x01dfffc000fff000

def z1107 : W := mkw 0x000a54aa79000000 0x01ee7ffe3f000000

def z1108 : W := mkw 0x004fef400065ec00 0x01dfffc000f4fc00

def z1109 : W := mkw 0x181a5c2e34b8d38c 0x99ff7c3f3cfcf3cc

def z1110 : W := mkw 0x9400105d2211264a 0x9f7387fd230ffe4f

def z1111 : W := mkw 0x94053a1d22748a4a 0xfffd7a3fe3f48fff

def z1112 : W := mkw 0x008ff7997b000000 0x01effffd3f000000

def z1113 : W := mkw 0xfa30084404fff7fd 0xfe10000000ffffff

def z1114 : W := mkw 0x008077aa7b000000 0x00607ffe3f000000

def z1115 : W := mkw 0x3a907fc87f21f49d 0x1e407fc03f00fc0f

def z1116 : W := mkw 0xc06fef7380efec60 0xe1ffffffc0fffc70

def z1117 : W := mkw 0x008ff7bbfb000000 0xe1efffffff070070

def z1118 : W := mkw 0x008ff7bbfb000000 0x01cffffedc000000

def z1119 : W := mkw 0x00052a400065ac00 0x01dd7fc000f4fc00

def z1120 : W := mkw 0x800f801500de0240 0xe1bf803fc0ff03f0

def z1121 : W := mkw 0x22c5a3d1cb472c11 0xe60183c1c3070c73

def z1122 : W := mkw 0x8005321d22540240 0x9ffd7a3d23f48e4f

def z1123 : W := mkw 0xc02fc43780de4360 0xe1bf843fc0ff73f0

def z1124 : W := mkw 0xc02f803780de0360 0x61af803fc0fb01b0

def z1125 : W := mkw 0x00456f400065ec00 0x00cc7fc000f0fc00

def z1126 : W := mkw 0x844fef5102efec42 0x9fffffc123fffe4f

def z1127 : W := mkw 0x00cff7bbfb8a4000 0x01efffffff000000

def z1128 : W := mkw 0x181a5c2e34b8d38c 0x19ee7c3e3cf0f00c

def z1129 : W := mkw 0x008a77aa7b000000 0x00cc7ffc3f000000

def z1130 : W := mkw 0x1800180c2430928c 0x19fc7c3c3cf0f20c

def z1131 : W := mkw 0x000ff73bb0000000 0x01effffffc000000

def z1132 : W := mkw 0x9405bb1d22748a4a 0x9ffdfbfd23f48e4f

def z1133 : W := mkw 0x000fe7b3c9000000 0x01efffffff000000

def z1134 : W := mkw 0x004fef4000efec00 0x01defdc000fbf000

def z1135 : W := mkw 0x2a5ac5e25d8b7595 0x600285c2dc0b71b0

def z1136 : W := mkw 0x008077997b000000 0x00607ffd3f000000

def z1137 : W := mkw 0xc02f803780de0360 0xe1ff843ffcff03f0

def z1138 : W := mkw 0x004fef6200efec00 0x01fffffe00fffc00

def z1139 : W := mkw 0x14053a0c22748a0a 0x1ffd7a3c23f48e0f

def z1140 : W := mkw 0xe2a5a3d1cb472471 0xe60183c1c3070c73

def z1141 : W := mkw 0x048ff7bbfb000802 0x07efffffff000c03

def z1142 : W := mkw 0xbe0008440475bedf 0x9e10000000f4fe4f

def z1143 : W := mkw 0x00cfef6290efec00 0x01dfffc000fffc00

def z1144 : W := mkw 0xbe10084404fdffdf 0xfe10000000ffffff

def z1145 : W := mkw 0x044fef4002efec02 0x07dfffc003fffc03

def z1146 : W := mkw 0x14003a082220880a 0xff73fa03e30f8fff

def z1147 : W := mkw 0x004fcd4000efe400 0x01dffdc000fff000

def z1148 : W := mkw 0xbe00109d6f1012df 0x9e20003d3f00024f

def z1149 : W := mkw 0x000a4c4000a9e400 0x01defdc000fbf000

def z1150 : W := mkw 0x181a5c2e34b8d38c 0x19fffffe3cf8f38c

def z1151 : W := mkw 0x185add2e34bad38c 0x19fe7c3e3cf8f38c

def z1152 : W := mkw 0x008ff7bbfb000000 0x87efffffff040c43

def z1153 : W := mkw 0x181a5c2e34b8d38c 0x79fefc3efcfbf3bc

def z1154 : W := mkw 0x181a5c2e34b8d38c 0x18ec7c3e3cf0f38c

def z1155 : W := mkw 0x144fef4000efec0a 0x1fdfffc000fffc0f

def z1156 : W := mkw 0x14003a0c22308a0a 0x9ffd7a3d23f48e4f

def z1157 : W := mkw 0x406fef6280efed20 0xe1ffffc3c0fffff0

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkA : List (List (List (ℕ × List W))) :=
  [[[(0,[z0,z1,z2,z3,z4,z5,z6]),(0,[z7,z0,z8,z2,z3,z4,z6]),(0,[z9,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z10,z3,z4,z6]),(0,[z11,z0,z1,z2,z3,z12,z6])],[(0,[z0,z1,z2,z3,z4,z6,z13]),(0,[z0,z1,z2,z3,z4,z14,z6]),(0,[z0,z1,z15,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z16,z4,z6]),(1,[z0,z2,z3,z4,z17,z6]),(0,[z18,z0,z1,z19,z3,z4,z6])],[(0,[z0,z1,z2,z20,z3,z4,z6]),(0,[z21,z22,z1,z2,z3,z4,z6]),(0,[z0,z1,z23,z2,z24,z4,z6]),(0,[z0,z1,z2,z3,z25,z4,z6]),(0,[z0,z1,z26,z3,z27,z4,z6]),(0,[z0,z1,z2,z3,z28,z4,z6])],[(0,[z29,z0,z1,z2,z3,z4,z6]),(0,[z30,z0,z1,z2,z3,z4,z6]),(0,[z0,z31,z2,z3,z32,z4,z6]),(0,[z0,z1,z23,z3,z27,z4,z6]),(0,[z0,z1,z33,z2,z3,z4,z6]),(0,[z0,z1,z2,z34,z3,z4,z6]),(0,[z35,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z36,z3,z27,z4,z6]),(1,[z0,z1,z2,z3,z37,z4])],[(0,[z0,z1,z38,z2,z3,z4,z6]),(0,[z39,z0,z1,z2,z3,z40,z6])],[(1,[z7,z8,z2,z3,z4,z6]),(0,[z41,z0,z1,z2,z3,z4,z6]),(0,[z0,z42,z1,z2,z3,z4,z6]),(0,[z43,z0,z1,z2,z3,z4,z6]),(1,[z0,z1,z44,z3,z45,z6])],[(0,[z1,z2,z3,z4,z46,z6,z47]),(0,[z0,z1,z2,z3,z4,z6,z48])],[(0,[z49,z0,z1,z2,z3,z4,z6]),(0,[z0,z50,z2,z51,z3,z4,z6]),(0,[z52,z0,z2,z3,z32,z4,z6]),(0,[z0,z1,z2,z3,z53,z4,z6]),(0,[z0,z1,z2,z3,z54,z53,z4])]],
   [[(0,[z0,z55,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z56,z6]),(1,[z57,z1,z2,z3,z4,z6]),(1,[z0,z1,z58,z3,z4,z6])],[(0,[z0,z1,z2,z3,z59,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z60]),(0,[z0,z1,z26,z2,z3,z4,z61])],[(0,[z62,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z63]),(0,[z0,z1,z64,z3,z27,z4,z6]),(0,[z65,z1,z2,z3,z4,z46,z6])],[(0,[z0,z1,z66,z2,z3,z4,z6]),(0,[z0,z1,z67,z2,z3,z4,z6]),(0,[z68,z0,z1,z2,z3,z4,z6]),(0,[z0,z69,z1,z2,z3,z4,z70]),(0,[z0,z1,z71,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z72,z4,z6]),(1,[z73,z1,z2,z3,z4,z6])],[(0,[z74,z0,z75,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z76,z4,z6]),(0,[z77,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z78,z3,z4,z6]),(0,[z79,z0,z1,z2,z3,z4,z6]),(0,[z0,z80,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z81]),(0,[z82,z0,z1,z2,z3,z4,z6])],[(0,[z83,z0,z1,z2,z3,z4,z6]),(0,[z84,z0,z1,z2,z3,z4,z6]),(0,[z85,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z86,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z87,z6]),(0,[z0,z1,z3,z27,z4,z6,z88]),(0,[z0,z1,z2,z89,z3,z4,z6]),(0,[z0,z1,z2,z4,z90,z6,z91])],[(0,[z0,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z92,z3,z4,z6]),(0,[z0,z93,z1,z2,z3,z4,z6]),(0,[z39,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z94,z2,z3,z24,z6]),(0,[z0,z1,z2,z3,z54,z4,z6])],[(0,[z0,z1,z2,z3,z4,z95,z6]),(0,[z0,z1,z2,z3,z4,z96,z6])]],
   [[(0,[z0,z1,z2,z3,z97,z4,z6])],[(0,[z0,z1,z2,z3,z4,z6,z98]),(0,[z99,z0,z1,z2,z3,z4,z6]),(1,[z0,z69,z2,z3,z4,z100]),(1,[z101,z0,z1,z3,z4,z88])],[(0,[z102,z0,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z4,z103,z6]),(0,[z104,z0,z1,z2,z3,z4,z6]),(0,[z7,z105,z1,z2,z3,z4,z6]),(0,[z21,z0,z1,z2,z3,z4,z6]),(0,[z106,z0,z1,z51,z3,z4,z6]),(0,[z107,z0,z1,z2,z3,z4,z6]),(0,[z0,z108,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z109,z4,z6]),(0,[z0,z69,z93,z2,z3,z4,z6]),(0,[z0,z1,z110,z2,z3,z4,z6])],[(0,[z0,z1,z26,z3,z24,z4,z6])],[(0,[z0,z1,z2,z3,z111,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z112]),(0,[z0,z1,z23,z3,z24,z4,z6]),(0,[z0,z1,z36,z3,z24,z4,z6])],[(0,[z113,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z114,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z115,z6]),(0,[z0,z1,z2,z116,z3,z4,z6]),(0,[z101,z0,z1,z26,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z117])]],
   [[(0,[z0,z1,z118,z2,z3,z4,z6]),(0,[z119,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z120,z3,z4,z45,z6]),(0,[z0,z1,z44,z3,z4,z45,z6]),(0,[z0,z1,z2,z3,z4,z121,z6])],[(0,[z122,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z123,z6]),(0,[z0,z1,z2,z3,z124,z4,z6]),(0,[z0,z1,z125,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z126,z4,z6]),(0,[z0,z1,z26,z3,z4,z46,z6])],[(0,[z127,z0,z1,z128,z3,z4,z6]),(0,[z52,z39,z0,z2,z3,z4,z6]),(0,[z65,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z129,z4,z6])],[(0,[z0,z75,z2,z3,z4,z6,z70]),(0,[z130,z0,z1,z2,z3,z4,z6])],[(0,[z0,z1,z131,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z132,z6]),(0,[z0,z1,z26,z2,z3,z4,z46]),(0,[z0,z1,z2,z3,z4,z90,z6])],[(0,[z133,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z134,z6]),(0,[z0,z1,z2,z3,z4,z135,z6]),(0,[z0,z1,z2,z3,z136,z4,z6]),(0,[z0,z1,z64,z3,z24,z4,z6]),(1,[z0,z1,z2,z3,z137,z4])],[(0,[z106,z0,z2,z51,z3,z4,z6]),(0,[z138,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z139]),(1,[z0,z1,z94,z2,z3,z6]),(0,[z0,z1,z2,z3,z4,z45,z6]),(0,[z0,z1,z36,z2,z3,z6,z61]),(0,[z101,z0,z1,z2,z3,z4,z88])],[(0,[z0,z1,z2,z3,z4,z140,z6]),(0,[z0,z1,z2,z3,z4,z6,z141]),(0,[z0,z1,z2,z3,z4,z6,z142]),(0,[z0,z143,z1,z2,z3,z4,z6])]],
   [[(0,[z0,z1,z2,z3,z4,z6,z144])],[(0,[z0,z1,z2,z3,z145,z4,z6]),(1,[z0,z146,z50,z3,z4,z6]),(0,[z0,z1,z2,z3,z147,z4,z6]),(0,[z0,z148,z1,z2,z3,z4,z6]),(0,[z149,z0,z1,z2,z3,z4,z6])],[(0,[z105,z1,z2,z3,z150,z4,z6]),(0,[z0,z1,z2,z151,z3,z4,z6]),(0,[z0,z1,z2,z152,z3,z4,z6]),(0,[z0,z153,z1,z2,z3,z4,z6])],[(0,[z154,z0,z1,z2,z3,z4,z6]),(0,[z155,z1,z2,z3,z4,z156,z6]),(0,[z0,z1,z50,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z157,z6]),(0,[z0,z1,z2,z3,z4,z6,z158]),(0,[z159,z0,z1,z2,z3,z24,z4]),(0,[z0,z1,z120,z64,z3,z4,z6]),(0,[z0,z1,z44,z64,z3,z4,z6]),(0,[z0,z1,z160,z2,z3,z54,z6]),(1,[z0,z2,z3,z161,z4,z6])],[(0,[z162,z0,z1,z2,z3,z4,z6]),(0,[z163,z0,z1,z2,z3,z4,z6])],[(0,[z74,z0,z1,z2,z3,z4,z164]),(0,[z0,z1,z2,z3,z165,z4,z6]),(0,[z0,z69,z50,z2,z3,z4,z6])],[(0,[z0,z1,z166,z2,z3,z4,z6]),(0,[z1,z2,z3,z150,z4,z156,z6]),(0,[z0,z1,z2,z167,z3,z4,z6])],[(0,[z1,z75,z2,z3,z4,z6,z168]),(0,[z0,z1,z2,z169,z3,z4,z6]),(0,[z52,z0,z1,z2,z170,z4,z6]),(0,[z0,z1,z2,z3,z4,z171,z6]),(0,[z101,z0,z1,z2,z172,z3,z4])]],
   [[(0,[z0,z1,z2,z3,z4,z173,z6])],[(0,[z0,z174,z1,z2,z3,z4,z6]),(0,[z175,z0,z125,z2,z3,z4,z6]),(0,[z176,z1,z2,z51,z3,z4,z6]),(0,[z0,z1,z2,z177,z3,z4,z6]),(1,[z0,z2,z3,z178,z4,z6]),(0,[z11,z0,z1,z179,z3,z4,z6]),(0,[z0,z180,z1,z2,z3,z4,z6])],[(0,[z181,z0,z1,z2,z3,z182,z6]),(0,[z0,z1,z2,z3,z4,z183,z6]),(0,[z184,z0,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z185,z4,z6]),(0,[z105,z22,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z182,z4,z6])],[(0,[z186,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z187,z3,z4,z6]),(0,[z0,z1,z120,z3,z4,z6,z88]),(0,[z0,z1,z44,z3,z4,z6,z88]),(1,[z0,z1,z36,z3,z27,z6]),(1,[z0,z188,z2,z3,z4,z6])],[(0,[z189,z0,z1,z2,z3,z4,z6]),(0,[z1,z2,z3,z182,z4,z6,z168]),(0,[z0,z1,z2,z3,z4,z6,z190]),(0,[z0,z1,z191,z3,z54,z4,z6])],[(0,[z192,z0,z1,z2,z3,z4,z6]),(1,[z127,z1,z193,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z194]),(1,[z0,z93,z2,z170,z4,z6]),(0,[z195,z0,z1,z2,z3,z4,z6])],[(0,[z0,z1,z196,z2,z3,z4,z6]),(0,[z0,z1,z197,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z198,z4,z6]),(0,[z0,z1,z2,z172,z3,z4,z90])]],
   [[(0,[z0,z1,z199,z2,z3,z4,z6]),(0,[z21,z1,z2,z3,z182,z4,z6]),(0,[z200,z0,z1,z2,z3,z4,z6])],[(0,[z0,z201,z1,z2,z3,z4,z6]),(0,[z18,z202,z1,z2,z3,z4,z6])],[(0,[z0,z1,z203,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z204])],[(0,[z0,z1,z2,z205,z3,z4,z6]),(0,[z0,z1,z206,z2,z3,z4,z6]),(0,[z0,z1,z207,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z208,z6]),(0,[z0,z1,z2,z3,z209,z4,z6])],[(0,[z0,z1,z2,z210,z3,z4,z6]),(0,[z0,z1,z211,z2,z3,z4,z6]),(0,[z105,z1,z2,z3,z4,z212,z6]),(0,[z106,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z213,z6]),(1,[z159,z0,z1,z2,z3,z4])],[(0,[z0,z1,z2,z3,z4,z6,z214]),(0,[z106,z0,z2,z3,z4,z40,z6]),(0,[z0,z1,z2,z3,z4,z6,z215])],[(0,[z0,z1,z2,z3,z4,z216,z6]),(0,[z217,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z218,z3,z4,z6]),(0,[z0,z1,z219,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z220])],[(0,[z181,z1,z2,z3,z150,z4,z6])]],
   [[(0,[z0,z69,z75,z2,z3,z4,z6]),(0,[z0,z1,z2,z128,z3,z4,z6]),(0,[z0,z1,z2,z221,z3,z4,z6]),(0,[z0,z222,z1,z2,z3,z4,z6]),(0,[z223,z0,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z224,z4,z6]),(0,[z0,z225,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z226]),(0,[z0,z1,z2,z3,z4,z227,z6]),(0,[z0,z1,z228,z2,z3,z4,z6])],[(0,[z0,z1,z193,z2,z3,z4,z6]),(0,[z229,z105,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z230,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z231,z6])],[],[(0,[z0,z2,z232,z128,z3,z4,z6]),(0,[z0,z1,z233,z2,z3,z4,z6]),(0,[z105,z0,z1,z2,z3,z4,z6]),(1,[z52,z0,z2,z234,z4,z6]),(0,[z0,z1,z2,z3,z4,z235,z6]),(0,[z0,z236,z1,z2,z3,z4,z6]),(0,[z0,z1,z3,z27,z4,z45,z6]),(0,[z0,z1,z2,z3,z4,z6,z237])],[(0,[z0,z8,z69,z2,z3,z4,z6]),(0,[z0,z1,z238,z2,z3,z4,z6]),(0,[z0,z2,z3,z178,z24,z4,z6]),(0,[z239,z0,z1,z2,z3,z4,z6]),(1,[z80,z1,z2,z3,z4,z6]),(0,[z11,z240,z1,z2,z3,z4,z6])],[(0,[z241,z0,z1,z2,z3,z4,z6]),(0,[z242,z0,z1,z2,z3,z4,z6]),(0,[z0,z69,z2,z3,z234,z4,z6]),(0,[z0,z1,z243,z2,z3,z4,z6]),(0,[z57,z1,z2,z3,z24,z4,z6]),(0,[z0,z244,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z245]),(0,[z0,z1,z2,z3,z4,z6,z246])],[(0,[z247,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z248,z75,z3,z4,z6]),(0,[z155,z105,z1,z2,z3,z4,z6]),(0,[z21,z1,z193,z2,z3,z4,z6]),(0,[z22,z0,z1,z2,z249,z4,z6])]],
   [[(0,[z0,z1,z2,z3,z250,z4,z6]),(0,[z251,z0,z1,z2,z3,z4,z6]),(0,[z11,z0,z1,z44,z2,z3,z6]),(0,[z0,z1,z2,z3,z4,z252,z6]),(0,[z0,z1,z2,z253,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z254])],[(0,[z0,z255,z1,z2,z3,z4,z6]),(0,[z155,z1,z2,z249,z3,z4,z6]),(1,[z256,z0,z2,z3,z4,z6]),(1,[z0,z1,z2,z3,z53,z61])],[(0,[z0,z1,z2,z257,z3,z4,z6])],[(0,[z0,z258,z1,z2,z3,z4,z6]),(0,[z259,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z260,z6]),(1,[z0,z1,z191,z3,z4,z6])],[(0,[z21,z155,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z261,z3,z4,z6]),(0,[z0,z1,z2,z3,z262,z4,z6]),(0,[z0,z1,z2,z3,z32,z4,z6]),(0,[z263,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z264,z6]),(0,[z0,z1,z2,z3,z4,z6,z265])],[(0,[z74,z0,z8,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z25,z24,z6]),(0,[z266,z1,z2,z3,z4,z12,z6]),(0,[z0,z1,z2,z3,z4,z6,z61])],[(0,[z7,z8,z1,z2,z3,z4,z6]),(0,[z267,z0,z1,z2,z3,z4,z6]),(0,[z268,z0,z1,z2,z3,z4,z6]),(0,[z269,z270,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z271,z4,z6])],[(0,[z0,z272,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z273,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z274]),(0,[z0,z1,z2,z3,z275,z4,z6]),(0,[z0,z276,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z277,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z278]),(1,[z0,z1,z2,z3,z4,z81]),(1,[z0,z1,z2,z3,z4,z264]),(1,[z266,z1,z2,z3,z4,z6])]],
   [[(0,[z74,z0,z1,z2,z3,z4,z279]),(0,[z0,z1,z2,z3,z280,z4,z6]),(0,[z0,z1,z2,z3,z281,z4,z6])],[(0,[z7,z1,z2,z3,z4,z6,z168]),(0,[z0,z1,z2,z3,z4,z6,z282]),(0,[z0,z1,z2,z3,z283,z4,z6])],[(0,[z284,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z285,z6]),(0,[z0,z1,z2,z3,z4,z286,z6]),(0,[z0,z1,z2,z3,z4,z6,z287]),(0,[z0,z1,z2,z288,z3,z4,z6])],[(0,[z289,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z37,z4,z6]),(0,[z0,z290,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z291,z3,z4,z6]),(0,[z0,z1,z292,z2,z3,z4,z6]),(0,[z0,z1,z2,z232,z3,z4,z6]),(0,[z0,z1,z2,z3,z293,z4,z6]),(0,[z0,z1,z2,z3,z4,z294,z6])],[(0,[z0,z1,z2,z3,z295,z4,z6]),(1,[z0,z296,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z297,z4,z6]),(0,[z0,z1,z2,z3,z4,z298,z6]),(0,[z0,z1,z2,z299,z3,z4,z6]),(0,[z11,z0,z1,z2,z3,z271,z6])],[(0,[z0,z1,z2,z3,z4,z6,z279]),(0,[z0,z1,z2,z3,z4,z300,z6]),(0,[z0,z301,z1,z2,z3,z4,z6]),(0,[z0,z1,z302,z2,z3,z4,z6])],[(1,[z22,z1,z2,z249,z4,z6]),(0,[z175,z105,z1,z2,z3,z4,z6]),(1,[z269,z0,z2,z3,z4,z70]),(0,[z0,z1,z303,z2,z3,z4,z6]),(0,[z0,z1,z304,z2,z3,z4,z6])]],
   [[(0,[z0,z1,z2,z3,z4,z305,z6]),(0,[z0,z1,z306,z2,z3,z4,z6]),(0,[z106,z0,z69,z2,z3,z4,z6]),(0,[z0,z2,z170,z3,z234,z4,z6]),(0,[z39,z0,z1,z2,z3,z32,z6])],[(0,[z22,z0,z1,z2,z150,z4,z6]),(0,[z181,z0,z1,z2,z3,z4,z6]),(0,[z39,z0,z2,z3,z4,z6,z70]),(0,[z0,z1,z2,z3,z307,z4,z6]),(0,[z0,z308,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z309,z4,z6]),(0,[z0,z93,z2,z3,z4,z40,z6]),(0,[z39,z0,z2,z3,z4,z40,z6]),(0,[z57,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z44,z2,z310,z3,z6]),(1,[z0,z1,z2,z310,z271,z6]),(0,[z0,z1,z2,z3,z54,z4,z90]),(0,[z311,z0,z1,z2,z3,z4,z6])],[(0,[z0,z1,z312,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z313,z6])],[(0,[z0,z1,z2,z3,z314,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z315])],[(0,[z316,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z317]),(0,[z318,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z319,z2,z3,z4,z6]),(0,[z0,z1,z58,z3,z4,z12,z6])],[(0,[z0,z1,z320,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z321]),(0,[z0,z1,z2,z3,z322,z4,z6])],[(0,[z0,z323,z1,z2,z3,z4,z6]),(1,[z105,z1,z2,z3,z4,z212]),(0,[z0,z31,z1,z2,z3,z40,z6])]],
   [[(0,[z0,z1,z2,z3,z4,z6,z324]),(0,[z0,z1,z2,z310,z3,z12,z6])],[(0,[z0,z1,z2,z325,z3,z4,z6]),(0,[z0,z2,z3,z32,z4,z40,z6]),(0,[z73,z0,z1,z2,z3,z4,z6])],[(1,[z74,z75,z2,z3,z4,z6]),(0,[z326,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z327,z6]),(0,[z0,z1,z3,z24,z4,z6,z88]),(0,[z0,z1,z2,z328,z3,z4,z6])],[(0,[z329,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z330,z6]),(0,[z331,z1,z2,z3,z27,z4,z6]),(0,[z0,z1,z160,z2,z3,z12,z6]),(0,[z0,z1,z160,z2,z3,z54,z4])],[(0,[z332,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z333,z4,z6]),(0,[z0,z1,z2,z3,z4,z334,z6]),(0,[z22,z1,z2,z3,z4,z156,z6]),(0,[z105,z0,z1,z2,z3,z4,z168])],[(0,[z21,z229,z1,z2,z3,z4,z6]),(0,[z106,z0,z1,z50,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z335,z6])],[(0,[z0,z1,z2,z3,z336,z4,z6]),(0,[z0,z1,z2,z3,z4,z337,z6]),(0,[z0,z1,z2,z338,z3,z4,z6]),(0,[z0,z1,z2,z3,z339,z4,z6])],[(0,[z0,z1,z340,z2,z3,z4,z6]),(0,[z341,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z342,z6]),(0,[z0,z1,z2,z343,z3,z4,z6]),(0,[z0,z146,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z344,z4,z6]),(0,[z269,z0,z1,z2,z3,z4,z100]),(0,[z0,z1,z2,z3,z4,z345,z6]),(0,[z346,z0,z1,z2,z3,z4,z6]),(1,[z102,z1,z2,z3,z4,z6]),(1,[z0,z222,z2,z3,z4,z6])]],
   [[(0,[z0,z1,z2,z347,z3,z4,z6]),(0,[z0,z31,z1,z2,z3,z32,z6]),(0,[z101,z0,z1,z2,z3,z54,z4]),(0,[z0,z1,z2,z3,z4,z12,z6]),(0,[z0,z348,z1,z2,z3,z4,z6])],[(0,[z229,z1,z2,z3,z4,z156,z6]),(0,[z0,z50,z2,z3,z4,z40,z6]),(0,[z0,z31,z1,z2,z3,z4,z6]),(0,[z0,z1,z23,z44,z3,z4,z6]),(0,[z0,z1,z36,z44,z3,z4,z6]),(1,[z0,z1,z349,z2,z3,z6])],[(0,[z350,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z351,z3,z4,z6]),(1,[z0,z1,z2,z3,z25,z6]),(0,[z0,z352,z1,z2,z3,z4,z6])],[(0,[z353,z0,z1,z2,z3,z4,z6])],[(0,[z105,z1,z75,z2,z3,z4,z6]),(0,[z0,z8,z2,z3,z4,z6,z70]),(0,[z0,z1,z2,z3,z4,z17,z6]),(0,[z0,z1,z2,z172,z3,z4,z91])],[(0,[z1,z2,z249,z3,z150,z4,z6]),(0,[z52,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z354,z6]),(0,[z0,z1,z2,z3,z4,z6,z355]),(0,[z159,z0,z1,z2,z3,z4,z6])],[(0,[z0,z1,z356,z2,z3,z4,z6]),(0,[z269,z0,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z4,z6,z357]),(1,[z0,z1,z2,z3,z121,z6])]],
   [[],[(0,[z0,z358,z1,z2,z3,z4,z6]),(0,[z0,z1,z160,z2,z3,z53,z6]),(0,[z1,z2,z3,z54,z359,z4,z6])],[(0,[z0,z1,z2,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z100,z212])],[(0,[z8,z1,z75,z2,z3,z4,z6]),(0,[z360,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z361,z4,z6])],[(0,[z155,z74,z1,z2,z3,z4,z6]),(0,[z362,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z363,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z364,z6])],[(0,[z39,z0,z69,z2,z3,z4,z6]),(0,[z0,z1,z2,z310,z271,z4,z6])],[(0,[z181,z1,z2,z3,z182,z4,z6]),(0,[z0,z1,z2,z3,z365,z4,z6]),(1,[z65,z1,z2,z3,z4,z6]),(1,[z0,z1,z366,z3,z4,z6]),(0,[z18,z0,z1,z302,z3,z4,z6]),(0,[z18,z0,z1,z2,z3,z53,z4]),(0,[z367,z0,z1,z2,z3,z4,z6])],[(0,[z0,z1,z368,z2,z3,z4,z6]),(0,[z0,z1,z369,z2,z3,z4,z6]),(1,[z0,z1,z2,z3,z6,z144]),(0,[z0,z1,z370,z2,z3,z4,z6]),(0,[z0,z1,z160,z2,z3,z4,z61])]],
   [[(0,[z155,z0,z1,z128,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z371,z6]),(0,[z372,z0,z1,z2,z3,z4,z6]),(0,[z175,z0,z1,z2,z3,z4,z212]),(0,[z373,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z374,z4,z6]),(0,[z0,z2,z3,z4,z17,z12,z6])],[(0,[z0,z1,z2,z3,z4,z375,z6]),(0,[z0,z1,z2,z3,z376,z4,z6]),(0,[z0,z1,z2,z3,z4,z377,z6])],[(0,[z11,z0,z1,z2,z4,z12,z6]),(0,[z0,z378,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z379,z4,z6]),(0,[z0,z1,z2,z3,z4,z380,z6]),(1,[z0,z125,z2,z3,z4,z6]),(0,[z0,z1,z2,z381,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z382])],[(0,[z0,z1,z2,z3,z4,z383,z6]),(0,[z0,z1,z2,z3,z4,z6,z384]),(0,[z0,z1,z2,z385,z3,z4,z6]),(0,[z0,z1,z36,z2,z310,z3,z6]),(0,[z18,z0,z1,z2,z4,z6,z91]),(1,[z0,z1,z3,z386,z4,z6])],[(0,[z155,z1,z2,z3,z4,z6,z168]),(0,[z1,z193,z2,z3,z4,z156,z6]),(0,[z0,z1,z2,z3,z387,z4,z6]),(0,[z1,z2,z388,z51,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z389,z6]),(0,[z101,z0,z1,z3,z4,z6,z88]),(0,[z18,z0,z1,z2,z3,z4,z6])],[(0,[z7,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z390]),(0,[z0,z1,z391,z2,z3,z4,z6]),(0,[z0,z1,z392,z2,z3,z4,z6])],[(1,[z0,z1,z248,z3,z4,z6]),(0,[z155,z127,z1,z2,z3,z4,z6]),(0,[z21,z0,z1,z2,z249,z4,z6]),(0,[z106,z0,z2,z3,z4,z6,z70]),(0,[z0,z1,z2,z393,z3,z4,z6])]],
   [[(0,[z0,z1,z2,z3,z4,z6,z394]),(0,[z1,z2,z3,z150,z4,z6,z168])],[(0,[z395,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z396,z24,z4])],[(0,[z0,z1,z397,z2,z3,z4,z6]),(0,[z0,z1,z398,z2,z3,z4,z6]),(0,[z0,z1,z399,z2,z3,z4,z6])],[(0,[z162,z0,z1,z75,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z400]),(0,[z0,z2,z3,z54,z161,z4,z6])],[(0,[z0,z1,z2,z3,z137,z4,z12]),(0,[z0,z1,z2,z3,z401,z4,z6])],[(0,[z0,z1,z402,z2,z3,z4,z6]),(0,[z181,z1,z193,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z403,z4,z6]),(1,[z1,z2,z3,z293,z4,z6]),(0,[z0,z404,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z91]),(0,[z0,z1,z2,z3,z4,z6,z405])],[(0,[z406,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z407,z4,z6]),(0,[z0,z1,z2,z3,z3,z4,z6]),(0,[z0,z1,z2,z408,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z409,z6]),(0,[z0,z1,z2,z3,z4,z6,z410])],[(0,[z229,z1,z2,z249,z3,z4,z6]),(0,[z229,z0,z1,z2,z3,z156,z6]),(0,[z411,z0,z1,z2,z3,z4,z6]),(1,[z1,z2,z388,z3,z4,z6]),(0,[z0,z1,z2,z3,z412,z4,z6]),(0,[z0,z1,z2,z3,z413,z4,z6]),(0,[z0,z1,z2,z414,z3,z4,z6])]],
   [[(0,[z415,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z416,z4,z6]),(0,[z0,z1,z2,z417,z3,z4,z6]),(0,[z418,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z419]),(0,[z0,z1,z3,z4,z46,z6,z88]),(0,[z420,z0,z2,z3,z4,z12,z6])],[(0,[z0,z146,z1,z51,z3,z4,z6]),(0,[z0,z1,z2,z3,z421,z4,z6])],[(0,[z0,z1,z2,z170,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z422,z6])],[(0,[z423,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z424,z4,z6]),(0,[z0,z1,z2,z3,z4,z425,z6])],[(0,[z0,z1,z2,z3,z4,z164,z6]),(0,[z0,z296,z1,z2,z3,z4,z6]),(0,[z0,z1,z426,z2,z3,z4,z6]),(0,[z0,z427,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z428,z3,z4,z6]),(0,[z0,z1,z429,z2,z3,z4,z6]),(0,[z175,z1,z2,z3,z4,z6,z168]),(0,[z0,z1,z2,z3,z4,z430,z6]),(0,[z431,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z26,z2,z3,z4,z6])],[(0,[z432,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z433]),(0,[z0,z2,z3,z234,z4,z6,z70]),(0,[z0,z434,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z4,z6,z435]),(0,[z0,z2,z3,z234,z4,z40,z6]),(0,[z0,z1,z2,z3,z4,z6,z436]),(0,[z101,z0,z1,z2,z3,z4,z46])]],
   [[(0,[z0,z1,z437,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z438,z4,z6]),(0,[z0,z1,z2,z3,z4,z439,z6]),(0,[z0,z1,z94,z2,z3,z4,z6]),(1,[z0,z1,z120,z64,z4,z6]),(0,[z0,z434,z2,z3,z27,z4,z6]),(1,[z0,z1,z19,z3,z4,z6]),(0,[z0,z1,z440,z2,z3,z4,z6])],[(0,[z21,z0,z1,z2,z150,z4,z6]),(0,[z0,z69,z2,z3,z32,z4,z6]),(0,[z0,z1,z3,z24,z4,z45,z6]),(0,[z0,z1,z2,z172,z4,z90,z6]),(0,[z0,z1,z191,z2,z3,z4,z6])],[(0,[z0,z1,z441,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z442,z6]),(0,[z0,z1,z2,z3,z443,z4,z6]),(0,[z0,z1,z2,z3,z444,z4,z6]),(0,[z0,z1,z445,z2,z3,z4,z6])],[(0,[z269,z446,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z447,z4,z6]),(0,[z0,z2,z3,z4,z46,z6,z237]),(0,[z0,z1,z2,z3,z53,z4,z61])],[(0,[z0,z1,z2,z3,z448,z4,z6]),(0,[z0,z1,z2,z51,z3,z4,z6]),(0,[z0,z1,z2,z3,z178,z4,z6]),(1,[z0,z449,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z450,z4,z6]),(1,[z11,z0,z1,z2,z12,z6])],[(0,[z0,z1,z451,z2,z3,z4,z6]),(0,[z452,z0,z1,z2,z3,z4,z6]),(0,[z0,z31,z93,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z453,z4,z6])],[(0,[z127,z0,z1,z2,z3,z4,z6]),(0,[z0,z454,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z156,z6])]],
   [[(0,[z455,z0,z2,z128,z3,z4,z6]),(0,[z0,z1,z2,z456,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z457,z6]),(0,[z11,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z458,z4,z6])],[(0,[z0,z1,z2,z388,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z459]),(0,[z0,z1,z2,z3,z4,z460,z6]),(0,[z0,z1,z461,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z462,z4,z6])],[(1,[z106,z0,z51,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z463,z6]),(0,[z464,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z465,z2,z3,z4,z6]),(0,[z466,z0,z1,z2,z3,z4,z6])],[(0,[z1,z193,z2,z249,z3,z4,z6]),(0,[z0,z1,z3,z54,z386,z4,z6])],[(0,[z0,z1,z467,z2,z3,z4,z6]),(0,[z0,z1,z2,z468,z3,z4,z6]),(0,[z0,z93,z2,z3,z4,z6,z70]),(0,[z469,z0,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z470,z4,z6]),(0,[z471,z0,z1,z2,z3,z4,z6]),(0,[z0,z2,z3,z4,z100,z6,z70]),(0,[z0,z1,z2,z3,z4,z472,z6]),(0,[z0,z1,z2,z3,z4,z473,z6]),(1,[z0,z1,z179,z3,z4,z6]),(0,[z18,z102,z1,z2,z3,z4,z6])],[(0,[z474,z0,z1,z2,z3,z4,z6]),(0,[z475,z0,z1,z2,z3,z4,z6]),(0,[z256,z0,z1,z2,z3,z4,z6]),(0,[z476,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z477,z4,z6]),(1,[z0,z2,z3,z4,z6,z237]),(0,[z0,z1,z2,z3,z4,z478,z6])],[(0,[z479,z0,z1,z2,z3,z4,z6])]],
   [[(0,[z0,z1,z2,z480,z3,z4,z6]),(1,[z0,z434,z2,z3,z4,z6])],[(0,[z0,z1,z481,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z482,z6])],[(0,[z483,z0,z1,z2,z3,z4,z6])],[(0,[z106,z7,z0,z2,z3,z4,z6]),(0,[z484,z0,z1,z2,z3,z4,z6]),(0,[z0,z2,z170,z3,z32,z4,z6]),(0,[z0,z2,z3,z32,z4,z6,z70]),(0,[z485,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z46,z6,z144]),(0,[z0,z1,z2,z3,z271,z6,z61]),(0,[z0,z1,z2,z3,z486,z4,z6])],[(0,[z487,z0,z1,z2,z3,z4,z6]),(0,[z1,z2,z249,z3,z182,z4,z6]),(0,[z229,z181,z1,z2,z3,z4,z6]),(0,[z105,z1,z2,z3,z182,z4,z6]),(0,[z0,z1,z488,z2,z3,z4,z6]),(0,[z73,z1,z2,z3,z54,z4,z6])],[(0,[z0,z69,z1,z2,z3,z4,z100]),(0,[z1,z2,z3,z27,z365,z4,z6]),(0,[z0,z1,z2,z3,z489,z4,z6]),(0,[z18,z0,z1,z2,z3,z121,z6])],[(0,[z0,z1,z2,z3,z4,z490,z6]),(0,[z127,z0,z146,z1,z3,z4,z6])],[(0,[z0,z1,z491,z2,z3,z4,z6]),(0,[z0,z31,z50,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z492]),(1,[z1,z2,z3,z365,z4,z6]),(0,[z0,z1,z2,z3,z53,z6,z61]),(0,[z0,z1,z2,z3,z386,z4,z6])]],
   [[(0,[z0,z1,z2,z3,z27,z4,z493]),(1,[z0,z301,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z90,z61]),(0,[z0,z1,z2,z494,z3,z4,z6])],[(0,[z155,z181,z1,z2,z3,z4,z6]),(0,[z0,z1,z495,z2,z3,z4,z6]),(0,[z0,z1,z496,z2,z3,z4,z6])],[(0,[z0,z1,z1,z2,z3,z4,z6]),(0,[z155,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z497,z4,z6]),(0,[z0,z1,z179,z2,z3,z4,z6]),(0,[z0,z1,z58,z2,z3,z4,z6])],[(0,[z498,z0,z1,z2,z3,z4,z6]),(0,[z0,z50,z2,z3,z4,z6,z70]),(0,[z0,z1,z499,z2,z3,z4,z6]),(0,[z0,z1,z2,z500,z3,z4,z6])],[(0,[z0,z1,z2,z3,z27,z4,z6]),(0,[z0,z1,z2,z3,z4,z501,z6])],[(0,[z502,z0,z1,z2,z3,z4,z6]),(0,[z0,z503,z1,z2,z3,z4,z6]),(0,[z0,z1,z504,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z505,z4,z6]),(0,[z0,z1,z506,z2,z3,z4,z6]),(0,[z0,z1,z2,z310,z3,z4,z6]),(0,[z0,z1,z2,z310,z3,z271,z6]),(0,[z18,z0,z188,z2,z3,z4,z6])],[(0,[z0,z1,z507,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z508,z6]),(1,[z0,z2,z232,z3,z4,z6]),(0,[z0,z1,z2,z509,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z510]),(1,[z176,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z511,z4,z6]),(0,[z0,z1,z2,z3,z54,z6,z61])],[(1,[z39,z0,z2,z3,z40,z6]),(0,[z0,z1,z2,z512,z3,z4,z6]),(0,[z0,z1,z120,z2,z3,z4,z6]),(0,[z0,z1,z44,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z47]),(1,[z0,z290,z2,z3,z4,z6]),(0,[z0,z290,z2,z3,z4,z46,z6]),(1,[z0,z1,z2,z172,z4,z90]),(0,[z0,z1,z2,z3,z359,z4,z6])]],
   [[(0,[z0,z1,z2,z3,z513,z4,z6]),(0,[z0,z1,z2,z3,z4,z514,z6]),(0,[z0,z1,z2,z3,z4,z515,z6]),(0,[z0,z1,z2,z3,z516,z4,z12])],[(1,[z0,z1,z2,z3,z4,z164]),(0,[z127,z0,z1,z193,z3,z4,z6]),(0,[z0,z1,z44,z160,z2,z3,z6]),(0,[z0,z1,z517,z2,z3,z4,z6])],[(0,[z0,z518,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z519,z4,z6]),(0,[z106,z0,z146,z2,z3,z4,z6]),(0,[z0,z1,z520,z2,z3,z4,z6])],[(0,[z105,z1,z193,z2,z3,z4,z6]),(0,[z176,z0,z1,z2,z3,z4,z6]),(0,[z521,z0,z1,z2,z3,z4,z6]),(0,[z0,z270,z1,z2,z3,z4,z6]),(0,[z256,z0,z2,z3,z24,z4,z6]),(1,[z331,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z37,z27,z4]),(0,[z0,z1,z522,z2,z3,z4,z6])],[(0,[z523,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z524,z4,z6]),(0,[z0,z1,z2,z3,z4,z100,z6]),(0,[z0,z1,z2,z3,z525,z4,z6]),(0,[z18,z101,z0,z1,z2,z3,z4]),(0,[z0,z1,z349,z2,z3,z4,z6])],[(0,[z0,z1,z2,z249,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z168,z70]),(0,[z0,z1,z526,z2,z3,z4,z6])],[(0,[z527,z0,z1,z2,z3,z4,z6]),(0,[z528,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z529]),(0,[z0,z1,z36,z2,z3,z27,z6])],[(0,[z0,z1,z2,z3,z4,z6,z530]),(0,[z155,z106,z0,z1,z3,z4,z6]),(0,[z446,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z531,z6]),(0,[z18,z0,z1,z160,z2,z3,z4])]],
   [[(0,[z0,z532,z1,z2,z3,z4,z6]),(0,[z11,z0,z1,z36,z2,z3,z6])],[(0,[z155,z0,z146,z1,z3,z4,z6]),(0,[z533,z0,z1,z2,z3,z4,z6]),(0,[z534,z0,z1,z2,z3,z4,z6])],[(0,[z535,z0,z1,z2,z3,z4,z6]),(0,[z8,z1,z193,z2,z3,z4,z6]),(0,[z175,z0,z1,z2,z3,z4,z6])],[(0,[z229,z1,z2,z3,z4,z6,z168]),(0,[z0,z1,z536,z2,z3,z4,z6]),(0,[z0,z1,z537,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z538,z4,z6]),(0,[z0,z1,z26,z2,z3,z4,z88])],[(0,[z7,z0,z50,z2,z3,z4,z6]),(0,[z0,z1,z2,z539,z3,z4,z6])],[(0,[z155,z8,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z540]),(0,[z0,z1,z2,z3,z541,z4,z6]),(0,[z0,z1,z2,z3,z516,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z542])],[(0,[z0,z1,z2,z3,z543,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z544])],[(0,[z0,z1,z545,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z546,z6]),(0,[z0,z1,z2,z3,z24,z4,z6]),(0,[z101,z0,z1,z2,z3,z4,z61]),(0,[z0,z1,z2,z271,z4,z12,z6])]],
   [[(0,[z547,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z548]),(0,[z0,z31,z2,z3,z234,z4,z6]),(0,[z1,z2,z3,z293,z24,z4,z6])],[(0,[z229,z0,z1,z2,z3,z182,z6]),(0,[z0,z1,z2,z549,z3,z4,z6]),(0,[z18,z0,z1,z2,z3,z4,z90])],[(0,[z0,z1,z550,z2,z3,z4,z6]),(0,[z551,z0,z1,z2,z3,z4,z6]),(1,[z0,z1,z26,z3,z4,z46]),(0,[z552,z0,z1,z2,z3,z4,z6])],[(0,[z74,z0,z1,z2,z3,z4,z6]),(0,[z127,z1,z193,z2,z3,z4,z6]),(0,[z553,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z396,z4,z6]),(0,[z0,z554,z1,z2,z3,z4,z6])],[(0,[z155,z0,z1,z193,z3,z4,z6]),(0,[z555,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z556,z3,z4,z6]),(0,[z52,z0,z2,z3,z234,z4,z6]),(0,[z0,z2,z3,z27,z489,z4,z6]),(0,[z0,z1,z26,z2,z172,z3,z4]),(0,[z0,z1,z2,z3,z4,z61,z91])],[(0,[z22,z1,z2,z249,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z557,z6]),(0,[z0,z558,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z493])],[(0,[z559,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z560,z2,z3,z4,z6]),(0,[z0,z1,z561,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z562,z6]),(0,[z0,z1,z2,z3,z4,z563,z6])],[(0,[z0,z1,z564,z2,z3,z4,z6]),(0,[z0,z1,z565,z2,z3,z4,z6]),(0,[z0,z1,z2,z566,z3,z4,z6]),(0,[z567,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z568]),(0,[z11,z0,z1,z366,z3,z4,z6])]],
   [[(0,[z0,z1,z569,z2,z3,z4,z6]),(0,[z570,z0,z1,z2,z3,z4,z6]),(0,[z175,z0,z296,z2,z3,z4,z6]),(0,[z0,z1,z571,z2,z3,z4,z6]),(1,[z0,z1,z2,z3,z396,z4])],[(0,[z0,z1,z572,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z6])],[(0,[z0,z1,z2,z573,z3,z4,z6]),(0,[z420,z0,z1,z2,z3,z4,z6]),(1,[z0,z1,z2,z3,z574,z6])],[(0,[z575,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z212,z6]),(0,[z0,z576,z1,z2,z3,z4,z6]),(0,[z0,z1,z577,z2,z3,z4,z6]),(0,[z0,z578,z1,z2,z3,z4,z6]),(0,[z0,z1,z579,z2,z3,z4,z6]),(1,[z0,z348,z2,z3,z4,z6])],[],[(0,[z1,z2,z3,z4,z212,z6,z168]),(0,[z269,z0,z69,z2,z3,z4,z6]),(0,[z331,z0,z1,z2,z3,z4,z6])],[(0,[z0,z1,z580,z2,z3,z4,z6]),(0,[z0,z1,z2,z581,z3,z4,z6])],[(0,[z7,z0,z75,z2,z3,z4,z6]),(0,[z1,z193,z2,z3,z4,z6,z168]),(0,[z0,z1,z2,z3,z582,z4,z6]),(0,[z0,z1,z2,z3,z4,z583,z6]),(1,[z1,z2,z3,z4,z478,z6])]],
   [[(1,[z175,z1,z2,z3,z4,z168]),(0,[z584,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z585])],[(0,[z586,z0,z1,z2,z3,z4,z6]),(0,[z587,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z23,z2,z3,z4,z6]),(0,[z0,z1,z36,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z161,z4,z6])],[(0,[z0,z1,z2,z3,z588,z4,z6]),(0,[z589,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z590,z4,z6]),(0,[z0,z202,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z54,z4,z91])],[(0,[z0,z1,z2,z3,z591,z4,z6]),(0,[z0,z146,z1,z50,z3,z4,z6]),(0,[z0,z1,z2,z3,z592,z4,z6]),(0,[z0,z1,z593,z2,z3,z4,z6]),(0,[z594,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z120,z2,z64,z4,z6]),(0,[z0,z1,z36,z160,z2,z3,z6])],[(1,[z0,z1,z2,z3,z4,z279]),(0,[z155,z1,z2,z128,z3,z4,z6]),(1,[z21,z1,z2,z150,z4,z6]),(0,[z0,z1,z2,z3,z4,z100,z168]),(0,[z0,z93,z1,z2,z234,z4,z6]),(0,[z0,z1,z2,z3,z595,z4,z6]),(0,[z0,z1,z2,z3,z137,z4,z6]),(0,[z0,z348,z2,z3,z54,z4,z6])],[(0,[z106,z127,z0,z1,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z596,z6]),(0,[z0,z1,z2,z597,z3,z4,z6]),(0,[z269,z0,z1,z2,z3,z4,z70]),(1,[z0,z1,z160,z2,z3,z54])],[(0,[z598,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z599,z3,z4,z6]),(0,[z600,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z120,z26,z3,z4,z6]),(0,[z0,z1,z44,z26,z3,z4,z6])],[(0,[z0,z1,z601,z2,z3,z4,z6]),(0,[z602,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z44,z2,z3,z27,z6]),(0,[z0,z1,z603,z2,z3,z4,z6])]],
   [[(0,[z0,z93,z1,z2,z170,z4,z6])],[(0,[z0,z1,z2,z3,z4,z6,z604]),(0,[z0,z1,z2,z3,z4,z6,z605]),(0,[z106,z0,z2,z170,z3,z4,z6]),(0,[z0,z606,z1,z2,z3,z4,z6]),(0,[z607,z0,z1,z2,z3,z4,z6]),(0,[z0,z608,z1,z2,z3,z4,z6]),(0,[z11,z80,z1,z2,z3,z4,z6]),(0,[z1,z2,z3,z4,z478,z12,z6]),(0,[z0,z1,z609,z2,z3,z4,z6])],[(0,[z175,z0,z1,z2,z3,z4,z168]),(0,[z0,z1,z2,z610,z3,z4,z6]),(0,[z0,z1,z188,z2,z3,z4,z6])],[(0,[z611,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z612,z4,z6])],[(1,[z181,z1,z2,z3,z182,z6]),(0,[z613,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z614,z3,z4,z6]),(0,[z0,z1,z615,z2,z3,z4,z6]),(0,[z0,z1,z616,z2,z3,z4,z6])],[(0,[z52,z0,z93,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z617,z4,z6]),(0,[z0,z1,z44,z2,z3,z45,z6])],[(0,[z618,z0,z1,z2,z3,z4,z6]),(0,[z619,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z620,z6])],[(0,[z621,z0,z1,z2,z3,z4,z6])]],
   [[(1,[z1,z2,z3,z4,z6,z47]),(0,[z18,z0,z222,z2,z3,z4,z6]),(1,[z1,z2,z3,z359,z4,z6])],[(0,[z622,z0,z1,z2,z3,z4,z6]),(0,[z52,z106,z0,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z574,z4,z6])],[(0,[z0,z1,z623,z2,z3,z4,z6]),(0,[z0,z624,z1,z2,z3,z4,z6])],[(0,[z0,z1,z625,z2,z3,z4,z6]),(0,[z1,z193,z2,z128,z3,z4,z6]),(0,[z22,z0,z1,z2,z3,z4,z6]),(0,[z1,z2,z3,z182,z4,z156,z6]),(0,[z0,z1,z626,z2,z3,z4,z6]),(0,[z627,z0,z1,z2,z3,z4,z6]),(0,[z11,z0,z1,z2,z3,z4,z81]),(0,[z11,z0,z1,z2,z3,z4,z264])],[(0,[z628,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z629,z3,z4,z6]),(0,[z106,z0,z31,z2,z3,z4,z6]),(1,[z270,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z366,z3,z4,z6]),(0,[z18,z0,z1,z2,z172,z4,z6]),(0,[z0,z1,z2,z630,z3,z4,z6])],[(0,[z11,z0,z449,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z631,z4,z6]),(0,[z0,z1,z2,z3,z4,z632,z6])],[(0,[z0,z8,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z633]),(0,[z0,z1,z634,z2,z3,z4,z6]),(1,[z446,z1,z2,z3,z4,z6]),(0,[z0,z1,z635,z2,z3,z4,z6]),(0,[z636,z0,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z637,z3,z4,z6]),(0,[z0,z1,z2,z638,z3,z4,z6]),(0,[z639,z0,z1,z2,z3,z4,z6]),(0,[z0,z640,z1,z2,z3,z4,z6]),(0,[z0,z1,z160,z2,z172,z3,z4])]],
   [[(0,[z0,z1,z2,z641,z3,z4,z6]),(0,[z229,z0,z1,z2,z3,z4,z6]),(0,[z0,z146,z50,z2,z3,z4,z6]),(0,[z52,z0,z1,z2,z234,z4,z6]),(0,[z0,z1,z120,z2,z24,z4,z6])],[(0,[z642,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z168]),(0,[z0,z1,z2,z3,z643,z4,z6]),(0,[z0,z1,z2,z3,z644,z4,z6]),(0,[z0,z1,z2,z3,z645,z4,z6]),(1,[z18,z0,z1,z2,z4,z91])],[(0,[z0,z1,z2,z3,z646,z4,z6]),(0,[z647,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z648,z4,z6]),(0,[z0,z1,z2,z3,z649,z4,z6])],[(0,[z74,z1,z75,z2,z3,z4,z6]),(0,[z0,z1,z2,z650,z3,z4,z6]),(1,[z0,z1,z2,z3,z516,z4])],[(0,[z651,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z652,z4,z6]),(0,[z0,z1,z2,z172,z3,z53,z4]),(0,[z653,z0,z1,z2,z3,z4,z6])],[(1,[z229,z1,z2,z3,z156,z6]),(0,[z0,z1,z2,z3,z4,z6,z70]),(0,[z0,z1,z654,z2,z3,z4,z6])],[(0,[z106,z74,z0,z2,z3,z4,z6]),(0,[z0,z655,z1,z2,z3,z4,z6]),(0,[z52,z0,z50,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z40,z6]),(1,[z0,z31,z2,z3,z32,z6]),(0,[z0,z1,z2,z64,z3,z4,z6]),(0,[z11,z0,z1,z2,z310,z4,z6])],[(0,[z74,z1,z193,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z212,z70]),(0,[z0,z1,z2,z3,z656,z4,z6]),(0,[z0,z69,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z657])]],
   [[(0,[z0,z1,z248,z2,z3,z4,z6]),(0,[z0,z1,z2,z658,z3,z4,z6]),(0,[z659,z0,z1,z2,z3,z4,z6])],[(1,[z162,z0,z1,z3,z4,z6]),(1,[z455,z0,z2,z3,z4,z6]),(0,[z660,z0,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z4,z6,z661]),(0,[z0,z1,z2,z3,z662,z4,z6])],[(0,[z0,z1,z2,z3,z4,z663,z6]),(0,[z0,z1,z2,z3,z4,z6,z664]),(0,[z0,z1,z2,z3,z4,z665,z6]),(0,[z666,z0,z1,z2,z3,z4,z6]),(0,[z667,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z668]),(0,[z0,z1,z160,z2,z3,z271,z6]),(0,[z0,z1,z2,z172,z3,z4,z6]),(0,[z0,z1,z160,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z4,z669,z6]),(0,[z0,z1,z2,z3,z4,z670,z6]),(0,[z0,z1,z2,z3,z4,z6,z671]),(0,[z269,z0,z2,z3,z4,z6,z70]),(0,[z18,z0,z1,z26,z2,z3,z4]),(1,[z240,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z672,z4,z6]),(0,[z673,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z23,z2,z64,z4,z6]),(0,[z0,z1,z2,z674,z3,z4,z6]),(0,[z0,z1,z2,z3,z12,z6,z61])],[(0,[z0,z1,z2,z3,z675,z4,z6]),(0,[z0,z93,z2,z170,z3,z4,z6]),(0,[z39,z0,z2,z170,z3,z4,z6]),(0,[z0,z1,z23,z120,z3,z4,z6]),(0,[z0,z1,z36,z120,z3,z4,z6]),(0,[z240,z0,z1,z2,z3,z4,z6]),(0,[z18,z0,z1,z2,z3,z4,z91])],[(0,[z0,z1,z2,z3,z4,z6,z88]),(0,[z0,z1,z449,z2,z3,z4,z6])]],
   [[(0,[z0,z1,z2,z3,z4,z4,z6]),(0,[z181,z0,z1,z2,z3,z156,z6]),(0,[z0,z1,z2,z676,z3,z4,z6]),(0,[z677,z0,z1,z2,z3,z4,z6]),(0,[z101,z0,z1,z2,z3,z4,z6])],[(0,[z22,z1,z2,z3,z4,z6,z168]),(0,[z0,z678,z1,z2,z3,z4,z6]),(0,[z0,z69,z2,z3,z4,z100,z6]),(0,[z11,z0,z301,z2,z3,z4,z6]),(1,[z420,z0,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z679,z4,z6]),(0,[z680,z0,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z4,z681,z6]),(0,[z0,z1,z2,z3,z682,z4,z6]),(0,[z0,z1,z2,z683,z3,z4,z6])],[(0,[z0,z1,z75,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z684]),(1,[z0,z1,z23,z24,z4,z6]),(0,[z266,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z685])],[(0,[z0,z1,z2,z3,z686,z4,z6]),(0,[z0,z1,z2,z3,z150,z4,z6]),(0,[z0,z1,z3,z4,z173,z12,z6])],[(0,[z0,z1,z26,z2,z3,z54,z4]),(1,[z0,z1,z302,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z687,z6])],[(0,[z0,z1,z2,z19,z3,z4,z6])],[(0,[z74,z7,z1,z2,z3,z4,z6]),(0,[z0,z1,z36,z2,z3,z45,z6]),(1,[z0,z2,z3,z489,z4,z6])]],
   [[(0,[z0,z1,z2,z3,z688,z4,z6]),(0,[z0,z1,z2,z3,z689,z4,z6]),(1,[z0,z1,z2,z3,z4,z493]),(0,[z0,z1,z690,z2,z3,z4,z6]),(0,[z18,z0,z1,z2,z3,z574,z6])],[(0,[z74,z0,z50,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z691,z4,z6]),(0,[z21,z1,z2,z3,z150,z4,z6]),(0,[z692,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z234,z4,z6]),(0,[z39,z0,z31,z2,z3,z4,z6])],[(0,[z693,z0,z1,z2,z3,z4,z6]),(0,[z455,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z694,z6]),(0,[z105,z0,z1,z2,z3,z4,z212]),(0,[z0,z1,z695,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z696])],[(1,[z155,z1,z128,z3,z4,z6]),(0,[z697,z0,z1,z2,z3,z4,z6]),(1,[z202,z1,z2,z3,z4,z6])],[(1,[z0,z1,z2,z3,z4,z6]),(0,[z0,z698,z1,z2,z3,z4,z6]),(0,[z0,z1,z44,z2,z3,z6,z61]),(0,[z0,z1,z2,z3,z699,z4,z6])],[(0,[z181,z22,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z700,z4,z6]),(0,[z0,z50,z2,z170,z3,z4,z6]),(0,[z0,z1,z349,z2,z3,z46,z6]),(1,[z0,z1,z3,z4,z173,z6]),(0,[z701,z0,z1,z2,z3,z4,z6])],[(0,[z0,z1,z702,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z46,z6])],[(0,[z0,z1,z2,z3,z4,z703,z6]),(0,[z0,z1,z704,z2,z3,z4,z6]),(0,[z0,z1,z2,z705,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z706])]]]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkB : List (List (List (ℕ × List W))) :=
  [[[(0,[z0,z707,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z4,z708])],[(0,[z0,z709,z2,z3,z4,z6]),(0,[z229,z1,z2,z3,z430,z6]),(0,[z331,z1,z36,z3,z27,z6])],[(0,[z0,z710,z2,z3,z4,z6]),(0,[z0,z2,z3,z711,z4,z6]),(0,[z1,z2,z3,z4,z708,z168]),(0,[z0,z2,z3,z712,z4,z6]),(0,[z0,z31,z2,z3,z713,z6]),(0,[z270,z2,z3,z4,z6,z70]),(0,[z714,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z715,z12,z6])],[(0,[z0,z1,z2,z3,z716,z6]),(0,[z717,z1,z2,z3,z4,z6]),(0,[z0,z1,z718,z3,z4,z6]),(0,[z0,z2,z3,z137,z4,z17])],[(0,[z446,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z719]),(0,[z0,z146,z50,z3,z4,z6]),(0,[z0,z1,z2,z4,z720,z91])],[(0,[z1,z2,z3,z721,z4,z6])],[(0,[z464,z8,z2,z3,z4,z6]),(0,[z722,z1,z2,z3,z4,z6]),(0,[z0,z2,z3,z4,z100,z723]),(0,[z0,z1,z179,z3,z4,z81]),(0,[z0,z1,z179,z3,z4,z264]),(0,[z0,z1,z2,z3,z121,z91])]],
   [[],[(0,[z21,z1,z2,z295,z4,z6]),(0,[z155,z455,z2,z3,z4,z6]),(0,[z0,z449,z179,z3,z4,z6]),(0,[z0,z222,z2,z3,z574,z6]),(0,[z18,z0,z1,z2,z4,z720])],[(0,[z0,z1,z2,z3,z724,z6]),(0,[z189,z1,z2,z3,z156,z6]),(0,[z106,z176,z2,z3,z4,z6]),(0,[z725,z1,z2,z3,z4,z6]),(0,[z726,z1,z2,z3,z4,z6]),(0,[z11,z240,z1,z2,z12,z6])],[(0,[z0,z1,z727,z3,z4,z6]),(1,[z1,z2,z728,z4,z6]),(0,[z176,z50,z2,z3,z4,z6]),(0,[z1,z2,z3,z4,z729,z6]),(0,[z0,z2,z3,z713,z40,z6]),(0,[z0,z1,z36,z3,z497,z6]),(0,[z0,z730,z2,z3,z4,z6])],[(0,[z229,z1,z2,z3,z156,z6]),(0,[z731,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z732,z4]),(0,[z0,z1,z2,z3,z6,z733]),(0,[z0,z2,z3,z178,z4,z6]),(0,[z0,z31,z2,z3,z32,z6]),(0,[z0,z1,z3,z734,z4,z6]),(0,[z0,z1,z58,z3,z137,z4])],[(0,[z74,z75,z2,z3,z4,z279]),(0,[z57,z1,z94,z2,z3,z6]),(0,[z0,z1,z26,z3,z37,z4])],[(0,[z0,z1,z2,z3,z4,z735]),(0,[z0,z736,z2,z3,z4,z6]),(1,[z1,z2,z3,z4,z708]),(0,[z202,z188,z2,z3,z4,z6])]],
   [[(0,[z455,z0,z2,z3,z4,z6]),(0,[z1,z2,z3,z4,z6,z737]),(0,[z159,z0,z1,z23,z24,z4]),(0,[z65,z1,z26,z3,z4,z46])],[(0,[z8,z738,z2,z3,z4,z6]),(0,[z0,z2,z3,z4,z739,z6]),(0,[z159,z0,z1,z94,z2,z3]),(0,[z0,z1,z44,z3,z740,z6]),(0,[z101,z0,z1,z3,z386,z4]),(0,[z0,z741,z2,z3,z4,z6])],[(0,[z162,z7,z0,z3,z4,z6]),(0,[z1,z2,z3,z742,z4,z6]),(0,[z266,z1,z2,z3,z516,z4])],[(0,[z1,z2,z3,z648,z182,z6])],[(0,[z21,z1,z2,z728,z4,z6]),(0,[z743,z1,z2,z3,z4,z6])],[(0,[z284,z0,z2,z3,z4,z70]),(0,[z0,z744,z2,z3,z4,z6]),(0,[z0,z745,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z746,z6]),(0,[z0,z125,z2,z3,z4,z212]),(0,[z0,z50,z3,z4,z6,z139]),(0,[z0,z2,z3,z374,z4,z70]),(0,[z0,z26,z3,z4,z46,z237]),(0,[z0,z1,z2,z3,z747,z4])],[(0,[z0,z1,z2,z3,z4,z748]),(0,[z0,z1,z2,z3,z749,z6]),(0,[z52,z0,z2,z524,z4,z6]),(0,[z0,z1,z2,z3,z4,z750]),(0,[z0,z751,z2,z3,z4,z6])],[(0,[z0,z2,z752,z3,z4,z6])]],
   [[(0,[z1,z2,z3,z145,z156,z6]),(0,[z0,z1,z2,z3,z713,z6]),(0,[z159,z0,z1,z2,z3,z4]),(0,[z619,z0,z1,z2,z3,z61]),(0,[z0,z1,z26,z19,z3,z4]),(0,[z0,z1,z2,z271,z715,z6])],[(0,[z1,z193,z210,z3,z4,z6]),(0,[z57,z2,z3,z178,z4,z6]),(0,[z0,z1,z2,z3,z753,z6]),(0,[z0,z1,z2,z3,z4,z754])],[(0,[z0,z50,z641,z3,z4,z6]),(0,[z0,z1,z755,z3,z4,z6]),(0,[z0,z2,z3,z4,z389,z70]),(0,[z0,z94,z2,z3,z178,z6]),(0,[z0,z2,z3,z489,z4,z493])],[(0,[z0,z1,z2,z3,z756,z6]),(0,[z0,z50,z3,z643,z4,z6]),(0,[z0,z1,z757,z3,z4,z6]),(0,[z0,z1,z349,z26,z3,z46]),(0,[z240,z1,z2,z3,z4,z81]),(0,[z240,z1,z2,z3,z4,z264]),(0,[z1,z2,z3,z4,z6,z758])],[(0,[z0,z2,z3,z4,z6,z723]),(0,[z0,z1,z302,z3,z4,z6]),(0,[z256,z0,z23,z24,z4,z6]),(0,[z0,z1,z520,z44,z3,z6]),(0,[z0,z1,z759,z3,z4,z6])],[(0,[z0,z1,z2,z3,z760,z6]),(0,[z0,z301,z179,z3,z4,z6]),(0,[z11,z0,z1,z2,z516,z12]),(0,[z0,z58,z3,z4,z17,z6])],[(0,[z647,z75,z2,z3,z4,z6]),(0,[z0,z2,z3,z489,z4,z6]),(0,[z0,z1,z2,z3,z4,z761]),(0,[z0,z1,z44,z2,z3,z81]),(0,[z0,z1,z2,z3,z747,z61]),(0,[z1,z191,z3,z359,z4,z6])],[(0,[z0,z1,z2,z3,z4,z762]),(0,[z270,z69,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z493]),(0,[z0,z2,z3,z763,z4,z6]),(0,[z0,z348,z3,z386,z4,z6])]],
   [[(0,[z332,z75,z2,z3,z4,z6]),(0,[z0,z764,z2,z3,z4,z6]),(0,[z765,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z766,z6])],[(0,[z1,z2,z3,z4,z767,z6]),(0,[z18,z0,z188,z2,z4,z91])],[(0,[z0,z768,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z4,z6]),(0,[z127,z1,z727,z3,z4,z6]),(0,[z175,z125,z2,z3,z4,z168]),(0,[z0,z1,z2,z3,z645,z61]),(0,[z0,z1,z769,z3,z4,z6]),(0,[z0,z1,z2,z3,z53,z121]),(0,[z0,z1,z2,z4,z6,z720])],[(0,[z106,z0,z2,z3,z4,z279]),(0,[z0,z1,z770,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z771])],[(0,[z256,z0,z2,z3,z4,z6]),(0,[z106,z0,z772,z3,z4,z6]),(0,[z52,z0,z2,z773,z4,z6]),(0,[z1,z2,z3,z293,z396,z4]),(0,[z11,z0,z449,z2,z12,z6]),(0,[z0,z1,z2,z3,z53,z61])],[(0,[z0,z1,z2,z3,z4,z774]),(0,[z0,z1,z775,z3,z4,z6]),(0,[z0,z1,z36,z94,z3,z6]),(0,[z0,z1,z2,z3,z4,z776]),(0,[z0,z1,z2,z3,z4,z777]),(0,[z0,z1,z778,z3,z4,z6])],[(0,[z0,z146,z772,z3,z4,z6]),(0,[z779,z1,z2,z3,z4,z6])]],
   [[(1,[z0,z1,z2,z715,z6])],[(0,[z1,z2,z3,z4,z6,z780])],[(0,[z1,z2,z3,z728,z4,z6]),(0,[z781,z1,z2,z3,z4,z6]),(0,[z0,z2,z3,z782,z4,z6]),(0,[z0,z1,z2,z3,z4,z783]),(0,[z0,z1,z2,z3,z37,z4])],[(0,[z0,z1,z2,z3,z4,z784]),(0,[z266,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z271,z81])],[(0,[z162,z8,z1,z3,z4,z6]),(0,[z1,z193,z3,z273,z4,z6]),(0,[z1,z2,z3,z785,z156,z6]),(0,[z106,z176,z51,z3,z4,z6]),(0,[z0,z1,z786,z3,z4,z6]),(0,[z269,z0,z2,z3,z4,z723]),(0,[z0,z1,z94,z3,z6,z88]),(0,[z0,z787,z2,z3,z4,z6]),(0,[z0,z1,z349,z3,z6,z88]),(0,[z266,z1,z3,z4,z173,z6])],[(0,[z0,z2,z3,z4,z6,z788]),(0,[z0,z789,z2,z3,z4,z6]),(0,[z0,z1,z160,z191,z3,z54])],[(0,[z0,z2,z3,z4,z6,z790]),(0,[z791,z1,z2,z3,z4,z6])],[(0,[z7,z1,z2,z3,z4,z279]),(0,[z0,z1,z2,z3,z792,z6]),(0,[z0,z1,z793,z3,z4,z6])]],
   [[(0,[z0,z2,z3,z794,z4,z6]),(0,[z0,z2,z3,z6,z237,z144]),(0,[z266,z2,z3,z4,z17,z6]),(0,[z18,z0,z1,z2,z121,z91])],[(0,[z0,z296,z2,z3,z4,z6]),(0,[z0,z50,z2,z3,z4,z279]),(0,[z0,z795,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z796,z6]),(0,[z0,z348,z191,z3,z4,z6])],[(0,[z0,z797,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z798,z6]),(0,[z73,z1,z2,z3,z4,z6]),(0,[z799,z1,z2,z3,z4,z6]),(0,[z0,z1,z36,z366,z3,z6]),(0,[z0,z1,z3,z37,z4,z88]),(0,[z0,z1,z19,z3,z574,z6])],[(0,[z22,z1,z2,z249,z4,z6]),(0,[z269,z0,z2,z3,z4,z70]),(0,[z1,z2,z3,z4,z6,z800])],[(0,[z0,z801,z2,z3,z4,z6]),(0,[z1,z2,z802,z3,z4,z6])],[(0,[z803,z0,z1,z2,z3,z4]),(0,[z1,z23,z293,z24,z4,z6]),(0,[z0,z1,z160,z2,z3,z747])],[(0,[z0,z1,z804,z3,z4,z6]),(0,[z1,z2,z3,z805,z4,z6]),(0,[z806,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z740,z6]),(0,[z0,z1,z2,z310,z271,z6])],[(0,[z162,z74,z0,z3,z4,z6]),(0,[z1,z193,z727,z3,z4,z6]),(0,[z807,z1,z2,z3,z4,z6]),(0,[z808,z1,z2,z3,z4,z6]),(0,[z266,z1,z58,z3,z4,z6])]],
   [[(0,[z0,z2,z773,z234,z4,z6]),(0,[z0,z69,z2,z3,z4,z100])],[(0,[z0,z1,z2,z3,z809,z6]),(0,[z0,z810,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z811,z6]),(0,[z0,z1,z3,z812,z4,z6]),(0,[z0,z1,z3,z4,z46,z813])],[(0,[z0,z8,z2,z3,z4,z279]),(0,[z162,z74,z75,z3,z4,z6]),(0,[z0,z2,z3,z32,z354,z6]),(0,[z0,z814,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z4,z815]),(0,[z75,z2,z3,z4,z168,z70]),(0,[z125,z2,z3,z4,z6,z168]),(0,[z0,z1,z2,z3,z816,z4]),(0,[z0,z2,z3,z4,z6,z817])],[(0,[z0,z1,z3,z4,z6,z818]),(0,[z155,z1,z727,z3,z4,z6]),(0,[z819,z1,z2,z3,z4,z6]),(0,[z0,z2,z3,z773,z4,z6]),(0,[z0,z820,z2,z3,z4,z6]),(0,[z102,z1,z302,z3,z4,z6]),(0,[z0,z222,z302,z3,z4,z6])],[(0,[z0,z1,z2,z3,z4,z821]),(0,[z0,z822,z2,z3,z4,z6])],[(0,[z74,z75,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z823])],[(0,[z0,z1,z2,z3,z4,z824]),(0,[z0,z825,z2,z3,z4,z6]),(0,[z0,z1,z3,z826,z4,z6]),(0,[z0,z50,z3,z280,z4,z6]),(0,[z827,z1,z2,z3,z4,z6]),(0,[z0,z1,z36,z2,z3,z493]),(0,[z0,z828,z2,z3,z4,z6]),(0,[z0,z1,z3,z4,z6,z813]),(0,[z653,z0,z1,z2,z12,z6])]],
   [[(0,[z1,z2,z3,z829,z4,z6]),(0,[z0,z1,z2,z3,z4,z830]),(0,[z0,z2,z170,z773,z4,z6]),(0,[z831,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z4,z832]),(0,[z0,z1,z833,z3,z4,z6]),(0,[z0,z834,z2,z3,z4,z6]),(0,[z0,z1,z835,z3,z4,z6]),(0,[z0,z836,z2,z3,z4,z6])],[(0,[z0,z837,z2,z3,z4,z6]),(0,[z0,z838,z2,z3,z4,z6]),(0,[z240,z1,z366,z3,z4,z6]),(0,[z202,z222,z2,z3,z4,z6])],[(0,[z102,z1,z2,z3,z4,z6]),(0,[z839,z1,z2,z3,z4,z6]),(0,[z0,z222,z2,z3,z4,z6]),(0,[z840,z1,z2,z3,z4,z6]),(0,[z18,z0,z1,z19,z4,z91]),(0,[z0,z1,z160,z3,z54,z386])],[(0,[z0,z75,z2,z3,z4,z279]),(0,[z0,z1,z2,z3,z137,z4]),(0,[z0,z1,z302,z3,z121,z6])],[(0,[z0,z1,z2,z3,z841,z6]),(0,[z0,z1,z94,z2,z3,z6]),(0,[z0,z1,z842,z2,z3,z6]),(0,[z0,z1,z349,z2,z3,z6])],[(0,[z0,z2,z3,z4,z843,z6]),(0,[z0,z1,z844,z3,z4,z6]),(0,[z0,z1,z2,z3,z25,z6]),(0,[z845,z1,z2,z3,z4,z6])],[(0,[z74,z248,z75,z3,z4,z6]),(0,[z39,z0,z2,z3,z345,z6]),(0,[z159,z1,z2,z3,z293,z4]),(0,[z256,z0,z94,z2,z3,z6]),(0,[z0,z1,z2,z3,z846,z6]),(0,[z0,z1,z2,z172,z4,z720])]],
   [[(0,[z847,z0,z1,z2,z3,z4]),(0,[z18,z0,z1,z2,z574,z91]),(0,[z653,z0,z1,z2,z4,z91])],[(0,[z0,z2,z3,z848,z4,z6]),(0,[z1,z2,z3,z109,z4,z168]),(0,[z0,z1,z849,z3,z4,z6]),(0,[z0,z69,z2,z3,z4,z96]),(0,[z0,z1,z520,z24,z4,z6]),(0,[z0,z1,z2,z3,z850,z6]),(0,[z0,z290,z26,z3,z4,z46])],[(0,[z0,z2,z3,z161,z4,z6]),(0,[z851,z0,z1,z2,z3,z4]),(0,[z202,z1,z2,z3,z121,z6])],[(0,[z852,z1,z2,z3,z4,z6]),(1,[z0,z1,z3,z740,z6]),(0,[z0,z1,z2,z3,z121,z6]),(0,[z0,z1,z2,z3,z137,z121]),(0,[z853,z1,z2,z3,z4,z6])],[(0,[z854,z1,z2,z3,z4,z6]),(0,[z855,z0,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z473,z61]),(0,[z0,z2,z3,z856,z4,z6]),(0,[z11,z0,z301,z2,z12,z6]),(0,[z266,z1,z2,z3,z137,z4]),(0,[z0,z188,z302,z3,z4,z6])],[(0,[z0,z2,z3,z4,z6,z857]),(0,[z0,z1,z2,z3,z4,z858]),(0,[z0,z1,z2,z494,z271,z6])],[(0,[z859,z0,z1,z3,z4,z6]),(0,[z105,z1,z2,z3,z4,z300]),(0,[z1,z125,z2,z3,z4,z168]),(0,[z0,z1,z3,z37,z386,z4]),(0,[z0,z860,z2,z3,z4,z6])],[(1,[z738,z2,z3,z4,z6]),(0,[z0,z2,z170,z588,z4,z6]),(0,[z0,z1,z36,z3,z27,z493]),(0,[z0,z1,z2,z3,z54,z538])]],
   [[(0,[z1,z2,z3,z182,z557,z6])],[(0,[z0,z861,z2,z3,z4,z6]),(0,[z0,z2,z3,z25,z178,z6]),(0,[z0,z1,z26,z3,z386,z4])],[(1,[z75,z2,z3,z4,z279]),(0,[z155,z106,z74,z3,z4,z6]),(0,[z65,z1,z2,z3,z4,z6]),(0,[z666,z1,z2,z3,z4,z168]),(0,[z77,z0,z2,z234,z4,z6]),(0,[z862,z1,z2,z3,z4,z6]),(0,[z57,z1,z2,z3,z25,z6]),(0,[z0,z1,z366,z3,z4,z6]),(0,[z0,z3,z161,z386,z4,z6])],[(0,[z0,z863,z2,z3,z4,z6]),(0,[z0,z2,z3,z864,z4,z6]),(0,[z0,z188,z2,z3,z4,z6]),(0,[z1,z2,z3,z4,z6,z865]),(0,[z0,z1,z36,z3,z27,z6])],[(0,[z0,z1,z2,z3,z866,z6]),(0,[z867,z1,z2,z3,z4,z6])],[(0,[z127,z1,z193,z3,z4,z6]),(0,[z0,z93,z2,z170,z4,z6])],[(0,[z0,z868,z2,z3,z4,z6]),(0,[z0,z1,z23,z94,z3,z6]),(0,[z869,z1,z2,z3,z4,z6])],[(0,[z0,z125,z2,z3,z4,z6]),(0,[z1,z2,z3,z870,z4,z6]),(0,[z1,z26,z3,z4,z46,z47])]],
   [[(0,[z0,z1,z2,z3,z4,z871]),(0,[z1,z2,z872,z3,z4,z6]),(0,[z0,z1,z3,z386,z4,z6])],[(0,[z155,z655,z1,z3,z4,z6]),(0,[z127,z1,z118,z3,z4,z6]),(0,[z1,z2,z249,z728,z4,z6]),(0,[z873,z1,z2,z3,z4,z6]),(0,[z0,z874,z2,z3,z4,z6]),(0,[z0,z2,z3,z4,z6,z875]),(0,[z73,z2,z3,z161,z4,z6])],[(0,[z0,z1,z876,z3,z4,z6]),(0,[z0,z1,z2,z3,z877,z4]),(0,[z878,z1,z2,z3,z4,z6]),(0,[z0,z1,z879,z3,z4,z6]),(0,[z0,z1,z880,z3,z4,z6])],[(0,[z0,z1,z248,z3,z4,z6]),(0,[z0,z881,z2,z3,z4,z6]),(0,[z105,z1,z2,z3,z4,z708]),(0,[z0,z1,z94,z3,z45,z6]),(0,[z0,z882,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z501,z61])],[(1,[z1,z727,z3,z4,z6]),(0,[z0,z69,z2,z3,z4,z723])],[(0,[z155,z455,z0,z3,z4,z6]),(0,[z0,z1,z883,z24,z4,z6]),(0,[z1,z2,z3,z884,z4,z6])],[(0,[z0,z2,z3,z4,z6,z885]),(0,[z106,z176,z0,z3,z4,z6])],[(0,[z155,z455,z1,z3,z4,z6]),(0,[z0,z1,z3,z4,z6,z886]),(0,[z0,z887,z2,z3,z4,z6]),(0,[z0,z2,z3,z888,z4,z6])]],
   [[(0,[z889,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z773,z4,z6]),(0,[z263,z0,z2,z234,z4,z6]),(0,[z240,z449,z2,z3,z4,z6]),(0,[z11,z0,z1,z366,z12,z6]),(1,[z0,z1,z2,z3,z747])],[(0,[z0,z1,z890,z3,z4,z6]),(0,[z0,z1,z64,z4,z252,z6]),(0,[z101,z0,z1,z2,z3,z121]),(0,[z891,z1,z2,z3,z4,z6])],[(0,[z202,z1,z2,z3,z574,z6]),(0,[z0,z160,z2,z3,z54,z161])],[(0,[z0,z1,z892,z3,z4,z6]),(0,[z0,z1,z893,z3,z4,z6]),(0,[z52,z0,z2,z234,z4,z6]),(0,[z0,z1,z399,z24,z4,z6]),(0,[z0,z894,z2,z3,z4,z6])],[(0,[z80,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z895,z6]),(0,[z0,z270,z2,z3,z4,z70]),(0,[z0,z1,z3,z896,z4,z6]),(0,[z0,z1,z160,z2,z3,z121]),(0,[z897,z1,z2,z3,z4,z6])],[(0,[z85,z0,z2,z3,z4,z70]),(0,[z0,z1,z23,z25,z24,z6])],[(0,[z0,z1,z3,z4,z898,z6]),(0,[z0,z899,z2,z3,z4,z6]),(0,[z0,z31,z2,z3,z275,z6]),(0,[z0,z2,z3,z4,z713,z6]),(0,[z1,z2,z3,z900,z4,z6]),(0,[z0,z1,z36,z3,z37,z27]),(0,[z2,z3,z359,z161,z4,z6])],[(0,[z74,z131,z2,z3,z4,z6]),(0,[z1,z2,z727,z3,z4,z6]),(0,[z0,z1,z901,z2,z3,z6]),(0,[z902,z0,z1,z2,z3,z4]),(0,[z0,z1,z2,z3,z6,z903]),(0,[z73,z1,z3,z386,z4,z6])]],
   [[(0,[z289,z1,z2,z3,z4,z168]),(0,[z904,z1,z2,z3,z4,z6]),(0,[z269,z270,z2,z3,z4,z70]),(0,[z0,z1,z2,z3,z905,z6]),(0,[z906,z0,z1,z2,z3,z4]),(0,[z11,z266,z1,z2,z12,z6])],[(0,[z155,z1,z573,z3,z4,z6]),(0,[z0,z1,z3,z740,z4,z6]),(0,[z0,z1,z36,z3,z72,z6]),(0,[z240,z1,z179,z3,z4,z6]),(0,[z0,z191,z3,z161,z4,z6])],[(0,[z155,z1,z417,z3,z4,z6]),(0,[z175,z1,z2,z3,z4,z708]),(0,[z907,z1,z2,z3,z4,z6]),(0,[z0,z1,z120,z299,z4,z6]),(0,[z0,z1,z191,z3,z4,z6]),(0,[z0,z1,z908,z3,z4,z6])],[(0,[z0,z1,z2,z3,z909,z4]),(0,[z0,z1,z2,z3,z4,z910]),(0,[z11,z0,z1,z58,z3,z6]),(0,[z202,z1,z19,z3,z4,z6]),(0,[z0,z1,z2,z3,z54,z747])],[(0,[z523,z1,z2,z150,z4,z6])],[(0,[z0,z1,z2,z3,z4,z911])],[(0,[z0,z1,z772,z3,z4,z6]),(0,[z0,z1,z2,z3,z912,z4]),(0,[z331,z434,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z81]),(0,[z0,z1,z2,z3,z4,z264]),(0,[z0,z913,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z4,z914]),(0,[z1,z2,z249,z185,z4,z6]),(0,[z1,z193,z3,z4,z6,z274])]],
   [[(0,[z915,z1,z2,z3,z4,z6]),(0,[z0,z449,z2,z3,z4,z6])],[(0,[z106,z388,z51,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z916]),(0,[z18,z0,z1,z2,z644,z4]),(0,[z11,z0,z1,z2,z715,z6]),(0,[z0,z1,z917,z3,z4,z6])],[(0,[z0,z1,z2,z3,z4,z918])],[(0,[z0,z919,z2,z3,z4,z6]),(0,[z0,z1,z920,z3,z4,z6]),(0,[z0,z31,z2,z3,z412,z6]),(0,[z102,z188,z2,z3,z4,z6])],[(0,[z0,z69,z2,z3,z4,z208]),(0,[z921,z0,z2,z3,z4,z6]),(0,[z240,z301,z2,z3,z4,z6])],[(0,[z922,z1,z2,z3,z4,z6]),(1,[z0,z1,z2,z4,z720]),(0,[z923,z0,z2,z3,z4,z6])],[(0,[z0,z1,z924,z3,z4,z6]),(0,[z0,z925,z2,z3,z4,z6]),(0,[z0,z1,z926,z3,z4,z6]),(0,[z11,z0,z1,z2,z595,z6])],[(0,[z0,z1,z2,z3,z4,z927]),(0,[z162,z0,z69,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z928]),(0,[z0,z929,z2,z3,z4,z6]),(0,[z0,z125,z2,z3,z4,z168]),(0,[z0,z1,z3,z477,z27,z6])]],
   [[(0,[z106,z0,z356,z3,z4,z6]),(0,[z159,z0,z2,z3,z178,z4]),(0,[z0,z348,z160,z2,z3,z54])],[(1,[z162,z74,z3,z4,z6]),(0,[z22,z1,z2,z676,z4,z6]),(0,[z0,z2,z772,z3,z4,z6]),(0,[z930,z1,z2,z3,z4,z6]),(1,[z0,z2,z3,z4,z723]),(0,[z0,z2,z3,z931,z4,z6]),(0,[z420,z0,z2,z3,z516,z4]),(0,[z73,z1,z191,z3,z4,z6])],[(0,[z1,z2,z3,z4,z6,z932])],[(0,[z0,z188,z2,z3,z121,z6])],[(0,[z162,z74,z1,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z933])],[(0,[z7,z738,z2,z3,z4,z6]),(0,[z455,z193,z2,z3,z4,z6]),(0,[z1,z2,z3,z4,z785,z6]),(0,[z0,z1,z2,z3,z934,z6])],[(0,[z105,z1,z2,z3,z4,z212]),(0,[z0,z1,z2,z3,z4,z935]),(0,[z0,z1,z2,z4,z90,z720]),(0,[z1,z3,z359,z386,z4,z6])],[(0,[z0,z69,z2,z3,z4,z286]),(0,[z1,z2,z3,z936,z4,z6])]],
   [[(0,[z162,z1,z3,z4,z6,z168]),(0,[z0,z1,z2,z883,z4,z6])],[(0,[z0,z1,z36,z3,z740,z6]),(0,[z101,z0,z1,z2,z3,z144])],[(0,[z0,z1,z3,z937,z4,z6]),(0,[z0,z1,z938,z2,z3,z6]),(0,[z0,z939,z2,z3,z4,z6]),(0,[z0,z940,z2,z3,z4,z6]),(0,[z1,z3,z4,z173,z478,z6])],[(0,[z666,z75,z2,z3,z4,z6]),(0,[z0,z1,z941,z3,z4,z6]),(0,[z942,z1,z2,z3,z4,z6]),(0,[z0,z2,z3,z4,z6,z943]),(0,[z944,z1,z2,z3,z4,z6])],[(0,[z0,z301,z2,z3,z4,z6]),(0,[z269,z446,z2,z3,z4,z70]),(0,[z0,z1,z94,z26,z3,z6]),(0,[z1,z2,z3,z945,z4,z6]),(0,[z0,z1,z349,z26,z3,z6]),(0,[z0,z1,z58,z3,z6,z61]),(0,[z0,z1,z3,z516,z4,z173])],[(0,[z0,z1,z2,z3,z4,z946]),(0,[z0,z1,z3,z4,z947,z6]),(0,[z0,z1,z2,z3,z4,z948])],[(0,[z11,z0,z1,z58,z12,z6])],[(0,[z0,z1,z2,z3,z949,z6]),(0,[z0,z1,z23,z94,z24,z6]),(0,[z0,z2,z3,z37,z489,z4])]],
   [[(0,[z0,z1,z2,z3,z4,z950]),(0,[z951,z1,z2,z3,z4,z6]),(0,[z0,z1,z44,z385,z3,z6])],[(0,[z0,z952,z2,z3,z4,z6])],[(0,[z176,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z953]),(0,[z2,z3,z365,z489,z4,z6])],[(0,[z0,z69,z2,z3,z4,z508]),(0,[z0,z1,z2,z3,z4,z954]),(0,[z0,z1,z2,z3,z4,z955]),(0,[z39,z0,z2,z3,z40,z6]),(0,[z256,z0,z2,z3,z25,z6]),(0,[z0,z1,z2,z172,z4,z90])],[(0,[z622,z1,z2,z3,z4,z168]),(0,[z0,z956,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z957]),(0,[z101,z0,z1,z3,z4,z813])],[(0,[z0,z1,z2,z3,z4,z164]),(0,[z0,z958,z2,z3,z4,z6]),(0,[z0,z2,z170,z4,z56,z6]),(0,[z0,z1,z959,z2,z3,z6])],[(0,[z474,z1,z2,z3,z4,z168]),(0,[z1,z2,z249,z4,z285,z6]),(0,[z960,z1,z2,z3,z4,z6]),(0,[z0,z1,z36,z2,z3,z81]),(0,[z0,z1,z26,z3,z401,z4]),(0,[z18,z0,z222,z2,z4,z91])],[(0,[z0,z1,z961,z3,z4,z6]),(0,[z962,z0,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z121,z90])]],
   [[(0,[z0,z93,z2,z512,z4,z6]),(0,[z1,z2,z963,z3,z4,z6]),(0,[z159,z256,z0,z2,z3,z4]),(0,[z0,z1,z58,z3,z516,z4]),(0,[z0,z1,z2,z3,z137,z61])],[(0,[z0,z1,z2,z3,z964,z6]),(0,[z0,z1,z965,z3,z4,z6]),(0,[z0,z1,z966,z3,z4,z6]),(0,[z0,z967,z2,z3,z4,z6]),(0,[z0,z968,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z747,z53])],[(0,[z969,z0,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z970,z6]),(0,[z971,z0,z2,z3,z4,z6])],[(0,[z1,z2,z3,z4,z972,z6]),(0,[z0,z1,z973,z3,z4,z6]),(0,[z0,z1,z974,z3,z4,z6]),(0,[z80,z1,z366,z3,z4,z6]),(0,[z0,z1,z2,z3,z715,z6]),(0,[z420,z0,z3,z4,z173,z6]),(0,[z0,z1,z3,z975,z4,z6]),(0,[z976,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z977])],[(1,[z155,z455,z3,z4,z6]),(0,[z155,z455,z128,z3,z4,z6]),(0,[z0,z1,z2,z3,z978,z6]),(0,[z0,z1,z2,z3,z979,z6]),(1,[z0,z2,z3,z713,z6]),(0,[z0,z1,z3,z883,z4,z6])],[(0,[z8,z2,z261,z3,z4,z6]),(0,[z980,z0,z2,z3,z4,z6]),(1,[z0,z1,z883,z4,z6]),(0,[z159,z0,z1,z2,z3,z25]),(0,[z101,z0,z1,z19,z3,z4])],[(0,[z0,z1,z981,z3,z4,z6]),(0,[z159,z0,z1,z19,z3,z4]),(0,[z0,z1,z44,z26,z3,z61]),(0,[z0,z1,z2,z3,z6,z144])],[(0,[z0,z1,z2,z3,z982,z6]),(0,[z983,z1,z2,z3,z4,z6]),(0,[z0,z1,z3,z740,z45,z6]),(0,[z0,z1,z58,z310,z3,z6])]],
   [[(0,[z0,z1,z2,z3,z4,z984]),(0,[z0,z1,z2,z3,z985,z6]),(0,[z1,z2,z3,z986,z4,z6])],[(0,[z0,z1,z2,z3,z4,z987]),(0,[z0,z988,z2,z3,z4,z6]),(0,[z105,z1,z2,z3,z4,z14]),(0,[z0,z1,z989,z3,z4,z6]),(0,[z0,z1,z23,z396,z24,z4]),(0,[z1,z2,z3,z516,z4,z478]),(0,[z0,z2,z3,z990,z4,z6])],[(0,[z181,z1,z2,z3,z785,z6]),(0,[z159,z0,z1,z26,z3,z4]),(0,[z0,z1,z26,z3,z4,z315]),(0,[z0,z1,z991,z3,z4,z6]),(0,[z11,z0,z1,z2,z137,z12]),(0,[z0,z1,z2,z3,z747,z6])],[(0,[z1,z193,z3,z543,z4,z6]),(0,[z0,z1,z2,z3,z785,z6]),(0,[z0,z1,z992,z2,z3,z6]),(0,[z993,z1,z2,z3,z4,z6]),(0,[z0,z1,z3,z137,z4,z173])],[(0,[z485,z1,z2,z3,z4,z212]),(0,[z0,z994,z2,z3,z4,z6]),(0,[z0,z995,z2,z3,z4,z6])],[(0,[z1,z2,z3,z37,z365,z4]),(0,[z0,z1,z366,z3,z4,z81]),(0,[z0,z1,z366,z3,z4,z264])],[(0,[z996,z0,z2,z3,z4,z6]),(0,[z0,z1,z26,z3,z4,z46]),(0,[z420,z2,z3,z4,z478,z6]),(0,[z420,z0,z58,z3,z4,z6]),(0,[z0,z1,z997,z3,z4,z6])],[(0,[z0,z1,z2,z3,z4,z998]),(0,[z0,z2,z3,z999,z4,z6]),(0,[z0,z1,z302,z3,z574,z6]),(0,[z0,z1,z517,z2,z3,z61])]],
   [[(0,[z0,z1,z1000,z3,z4,z6]),(0,[z0,z1001,z2,z3,z4,z6]),(0,[z0,z2,z3,z1002,z4,z6]),(0,[z1003,z1,z2,z3,z4,z6]),(0,[z0,z2,z3,z4,z6,z1004])],[(0,[z0,z1,z26,z2,z3,z121]),(0,[z1005,z1,z2,z3,z4,z6]),(0,[z0,z1,z160,z191,z3,z6])],[(0,[z0,z1006,z2,z3,z4,z6]),(0,[z229,z1,z2,z3,z785,z6]),(0,[z1007,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z500,z4,z90]),(0,[z1008,z1,z2,z3,z4,z6])],[(0,[z1009,z0,z2,z3,z4,z6]),(0,[z106,z176,z1,z3,z4,z6]),(0,[z1010,z1,z2,z3,z4,z6]),(0,[z0,z1011,z2,z3,z4,z6]),(0,[z1012,z1,z2,z3,z4,z6])],[(0,[z0,z1,z1013,z3,z4,z6]),(0,[z1,z2,z3,z293,z4,z6]),(0,[z0,z1,z2,z3,z1014,z6]),(0,[z0,z1,z2,z3,z396,z4]),(0,[z1,z2,z3,z1015,z4,z6])],[],[(0,[z1,z2,z388,z3,z4,z6]),(0,[z0,z1016,z2,z3,z4,z6]),(0,[z1,z2,z3,z4,z375,z168]),(0,[z1017,z1,z2,z3,z4,z6]),(0,[z0,z1,z94,z64,z3,z6]),(0,[z0,z1,z2,z3,z574,z6]),(0,[z102,z222,z2,z3,z4,z6])],[(0,[z162,z105,z1,z3,z4,z6]),(0,[z0,z1,z2,z3,z1018,z6]),(0,[z1019,z1,z2,z3,z4,z6])]],
   [[(0,[z0,z146,z196,z3,z4,z6]),(0,[z1020,z1,z2,z3,z4,z6]),(0,[z1,z94,z2,z3,z293,z6]),(0,[z290,z2,z3,z4,z6,z47]),(0,[z0,z1,z2,z3,z209,z61])],[(0,[z0,z1,z2,z3,z1021,z4]),(0,[z22,z1,z2,z728,z4,z6]),(0,[z1022,z1,z2,z3,z4,z6]),(0,[z0,z1,z23,z595,z4,z6]),(0,[z0,z1,z160,z2,z3,z649])],[(0,[z434,z2,z3,z365,z4,z6]),(0,[z18,z0,z1,z302,z4,z91])],[(0,[z1,z2,z3,z4,z478,z6])],[(0,[z0,z1,z1023,z3,z4,z6]),(0,[z175,z1,z2,z3,z4,z168]),(0,[z0,z1,z2,z3,z1024,z4]),(0,[z0,z1,z609,z2,z3,z54])],[(0,[z0,z1,z2,z3,z4,z1025]),(0,[z0,z1,z44,z630,z3,z6])],[(0,[z1026,z1,z2,z3,z4,z6]),(0,[z1027,z1,z2,z3,z4,z6]),(0,[z1028,z0,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z1029,z4]),(0,[z102,z1,z2,z3,z121,z6]),(0,[z0,z222,z2,z3,z121,z6])],[(0,[z0,z1,z2,z3,z1030,z4]),(0,[z0,z1,z120,z64,z4,z6]),(0,[z0,z1,z19,z3,z4,z6]),(0,[z80,z1,z2,z3,z4,z81]),(0,[z80,z1,z2,z3,z4,z264])]],
   [[(0,[z0,z1,z2,z3,z4,z279]),(0,[z21,z1,z2,z150,z4,z6]),(0,[z1031,z1,z2,z3,z4,z6]),(0,[z57,z1,z2,z3,z396,z4]),(0,[z0,z1,z3,z27,z260,z6]),(0,[z0,z1,z2,z172,z314,z4]),(0,[z1,z2,z3,z137,z4,z478]),(0,[z0,z1,z2,z3,z1032,z4])],[(0,[z74,z356,z2,z3,z4,z6]),(0,[z106,z432,z0,z3,z4,z6]),(0,[z1033,z0,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z6,z1034]),(0,[z80,z449,z2,z3,z4,z6]),(0,[z0,z1035,z2,z3,z4,z6]),(0,[z0,z1,z160,z2,z3,z54])],[(0,[z0,z1,z2,z3,z4,z1036]),(0,[z0,z1037,z2,z3,z4,z6])],[(0,[z0,z2,z3,z4,z6,z1038]),(0,[z0,z1,z3,z27,z740,z6])],[(0,[z1,z727,z128,z3,z4,z6]),(0,[z1,z2,z3,z4,z6,z708]),(0,[z0,z93,z2,z549,z4,z6]),(0,[z0,z1,z26,z3,z4,z364]),(0,[z11,z0,z1,z2,z12,z6])],[(0,[z0,z1,z1039,z3,z4,z6]),(0,[z1040,z1,z2,z3,z4,z6]),(1,[z270,z2,z3,z4,z70]),(0,[z0,z1,z94,z2,z3,z396]),(0,[z1041,z1,z2,z3,z4,z6]),(0,[z0,z1,z1042,z3,z4,z6])],[(0,[z0,z1,z2,z3,z4,z1043]),(0,[z0,z1044,z2,z3,z4,z6]),(0,[z1,z2,z3,z4,z212,z708]),(0,[z1045,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z25,z396]),(0,[z0,z1,z44,z3,z6,z668]),(0,[z11,z0,z1,z179,z12,z6]),(0,[z18,z202,z1,z2,z4,z91])],[(0,[z0,z1,z2,z3,z1046,z6]),(0,[z0,z1,z2,z3,z4,z1047]),(0,[z0,z1,z2,z3,z1048,z6]),(0,[z0,z1,z26,z3,z46,z144]),(0,[z65,z1,z349,z2,z3,z6]),(0,[z1049,z0,z2,z3,z4,z6])]],
   [[(0,[z181,z1,z2,z3,z182,z6]),(0,[z1,z2,z3,z182,z785,z6])],[(0,[z0,z1,z1050,z3,z4,z6]),(0,[z21,z1,z2,z700,z4,z6]),(0,[z106,z0,z51,z3,z4,z6]),(0,[z1051,z1,z2,z3,z4,z6]),(0,[z270,z1,z2,z3,z4,z100]),(0,[z1052,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z728,z4,z6]),(1,[z106,z176,z3,z4,z6]),(1,[z0,z1,z3,z4,z813])],[(0,[z622,z0,z2,z3,z4,z70]),(0,[z0,z1,z1053,z3,z4,z6]),(0,[z0,z434,z2,z3,z4,z493]),(0,[z0,z449,z2,z3,z4,z81]),(0,[z0,z449,z2,z3,z4,z264]),(0,[z2,z3,z4,z17,z478,z6]),(0,[z0,z2,z3,z1054,z4,z6]),(0,[z0,z1,z3,z4,z1055,z6])],[(0,[z0,z1,z2,z3,z1056,z4]),(0,[z7,z2,z705,z3,z4,z6]),(0,[z1,z2,z3,z1057,z4,z6]),(0,[z0,z1,z1058,z3,z4,z6]),(0,[z1,z1059,z2,z3,z4,z6]),(0,[z0,z1,z179,z3,z4,z6]),(0,[z0,z349,z2,z3,z6,z237]),(0,[z11,z0,z1,z2,z12,z81]),(0,[z0,z1,z1060,z3,z4,z6]),(0,[z11,z0,z1,z2,z12,z264]),(0,[z0,z3,z4,z173,z17,z6])],[(0,[z738,z75,z2,z3,z4,z6]),(0,[z0,z2,z3,z4,z6,z237]),(0,[z1061,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z1062,z4]),(0,[z0,z1,z44,z3,z531,z6]),(0,[z348,z2,z3,z359,z4,z6])],[(0,[z0,z2,z1063,z3,z4,z6]),(0,[z0,z1,z2,z3,z6,z1064]),(0,[z0,z1,z2,z3,z1065,z4])],[(0,[z0,z1,z3,z4,z6,z1066]),(0,[z0,z434,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z1067]),(0,[z0,z1,z191,z3,z6,z61])]],
   [[(0,[z270,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z1068]),(0,[z1,z1069,z2,z3,z4,z6]),(0,[z1070,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z1071]),(0,[z73,z1,z160,z2,z3,z54])],[(0,[z0,z1,z26,z2,z3,z144])],[(0,[z1072,z1,z2,z3,z4,z6]),(0,[z0,z1,z44,z366,z3,z6]),(0,[z1,z2,z3,z365,z4,z493]),(0,[z0,z1,z2,z4,z715,z6]),(0,[z1073,z1,z2,z3,z4,z6])],[(0,[z0,z1074,z2,z3,z4,z6]),(0,[z0,z1,z26,z3,z4,z183]),(0,[z11,z0,z2,z17,z12,z6]),(0,[z18,z0,z1,z2,z4,z501])],[(0,[z0,z1,z1075,z3,z4,z6]),(0,[z0,z2,z3,z297,z40,z6]),(0,[z0,z36,z3,z27,z489,z6])],[(0,[z106,z0,z480,z3,z4,z6]),(0,[z65,z1,z2,z3,z6,z144]),(0,[z80,z301,z2,z3,z4,z6]),(0,[z18,z0,z1,z2,z4,z91])],[(0,[z0,z2,z1076,z3,z4,z6]),(0,[z1,z2,z3,z365,z4,z6]),(0,[z0,z434,z2,z3,z37,z4]),(0,[z102,z1,z2,z3,z574,z6])],[(0,[z0,z1,z2,z3,z1077,z6]),(0,[z0,z1,z2,z3,z516,z4])]],
   [[(0,[z74,z738,z2,z3,z4,z6]),(1,[z125,z2,z3,z4,z168])],[(0,[z0,z1078,z2,z3,z4,z6]),(0,[z181,z1,z2,z3,z376,z6]),(0,[z0,z1,z1079,z2,z3,z6])],[(0,[z0,z1,z120,z674,z4,z6]),(0,[z0,z1080,z2,z3,z4,z6])],[(0,[z673,z0,z2,z3,z40,z6]),(0,[z0,z1,z3,z4,z6,z1081])],[(0,[z0,z1,z2,z3,z1082,z6]),(0,[z0,z1083,z2,z3,z4,z6]),(0,[z0,z1,z26,z3,z4,z813]),(0,[z1,z160,z2,z3,z54,z359])],[(0,[z162,z0,z1,z3,z4,z6]),(0,[z0,z2,z232,z3,z4,z6]),(0,[z229,z1,z2,z3,z305,z6]),(0,[z39,z0,z2,z3,z713,z6]),(0,[z1,z2,z3,z4,z6,z1084]),(0,[z331,z2,z3,z489,z4,z6])],[(0,[z0,z290,z2,z3,z4,z6]),(0,[z331,z1,z2,z3,z4,z493]),(0,[z0,z1,z3,z1085,z4,z6]),(0,[z0,z1,z160,z2,z3,z687])],[(0,[z0,z1,z1086,z3,z4,z6]),(0,[z0,z1,z2,z3,z1087,z6]),(0,[z0,z1,z44,z2,z3,z493]),(0,[z1088,z1,z2,z3,z4,z6]),(0,[z0,z301,z2,z3,z4,z81]),(0,[z0,z301,z2,z3,z4,z264]),(0,[z1089,z1,z2,z3,z4,z6]),(0,[z102,z1,z19,z3,z4,z6]),(0,[z0,z222,z19,z3,z4,z6])]],
   [[(0,[z240,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z1090,z4]),(0,[z0,z93,z2,z773,z4,z6])],[(0,[z0,z1,z1091,z3,z4,z6]),(0,[z105,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z1092]),(0,[z0,z2,z3,z178,z396,z4]),(0,[z1,z2,z3,z4,z6,z1093])],[(0,[z331,z1,z2,z3,z4,z6]),(0,[z0,z1,z36,z3,z6,z315])],[(0,[z1094,z1,z2,z3,z4,z6]),(0,[z39,z0,z2,z3,z665,z6]),(0,[z1095,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z172,z462,z4])],[(0,[z22,z1,z2,z221,z4,z6]),(0,[z1096,z1,z2,z3,z4,z6]),(0,[z0,z1,z3,z4,z1097,z6]),(0,[z57,z256,z2,z3,z4,z6])],[(0,[z1,z738,z2,z3,z4,z6]),(0,[z0,z1,z3,z1098,z4,z6]),(0,[z52,z0,z2,z361,z4,z6]),(0,[z420,z0,z2,z3,z4,z6])],[(0,[z0,z188,z2,z3,z574,z6])],[(0,[z1099,z0,z1,z2,z3,z6]),(0,[z0,z2,z3,z1100,z4,z6]),(0,[z0,z1,z23,z24,z4,z6]),(0,[z0,z1,z19,z3,z121,z6])]],
   [[(0,[z1,z75,z2,z3,z4,z279]),(0,[z1,z2,z728,z150,z4,z6]),(0,[z105,z1,z2,z3,z4,z596]),(0,[z0,z772,z51,z3,z4,z6]),(0,[z1101,z1,z2,z3,z4,z6]),(0,[z0,z1,z44,z3,z87,z6]),(0,[z266,z420,z2,z3,z4,z6]),(0,[z202,z1,z302,z3,z4,z6])],[(0,[z647,z0,z2,z3,z4,z70]),(0,[z1102,z1,z2,z3,z4,z6]),(0,[z1,z2,z3,z4,z6,z1103]),(0,[z331,z1,z2,z3,z37,z4]),(0,[z2,z3,z4,z6,z47,z237])],[(0,[z0,z1,z2,z3,z6,z1104]),(0,[z0,z1105,z2,z3,z4,z6]),(0,[z1106,z1,z2,z3,z4,z6]),(0,[z1,z36,z3,z27,z365,z6]),(0,[z1107,z0,z2,z3,z4,z6])],[(0,[z7,z698,z2,z3,z4,z6]),(0,[z1108,z1,z2,z3,z4,z6]),(0,[z0,z1,z1109,z3,z4,z6])],[(0,[z1,z193,z2,z3,z4,z279]),(0,[z75,z2,z3,z4,z6,z279]),(0,[z1,z2,z3,z1110,z4,z6]),(0,[z0,z1,z2,z3,z1111,z6]),(0,[z0,z1112,z2,z3,z4,z6]),(0,[z176,z146,z1,z3,z4,z6]),(1,[z0,z2,z773,z4,z6]),(0,[z0,z2,z3,z4,z6,z1113])],[(0,[z0,z1114,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z1115,z4]),(0,[z1,z2,z3,z4,z6,z1116]),(0,[z0,z1117,z2,z3,z4,z6])],[(0,[z0,z1118,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z12,z81]),(0,[z1119,z1,z2,z3,z4,z6])],[(0,[z155,z1,z128,z3,z4,z6]),(0,[z202,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z1120,z4]),(0,[z1,z2,z3,z25,z293,z6]),(0,[z0,z1,z2,z310,z525,z6]),(0,[z0,z188,z19,z3,z4,z6])]],
   [[(0,[z0,z1,z1121,z3,z4,z6]),(0,[z0,z1,z2,z3,z1122,z6]),(0,[z0,z2,z3,z136,z32,z6]),(0,[z0,z1,z160,z2,z3,z137]),(0,[z0,z1,z2,z3,z4,z720])],[(0,[z155,z1,z2,z3,z4,z279]),(0,[z0,z1,z2,z3,z4,z1123]),(0,[z0,z1,z2,z3,z4,z1124]),(0,[z0,z1,z3,z4,z173,z6]),(0,[z0,z1,z160,z2,z3,z183]),(0,[z11,z0,z1,z173,z12,z6])],[(0,[z0,z449,z366,z3,z4,z6]),(0,[z1125,z1,z2,z3,z4,z6])],[(0,[z162,z74,z2,z3,z4,z6]),(0,[z57,z1,z23,z24,z4,z6]),(0,[z1,z2,z3,z1126,z4,z6]),(0,[z1,z58,z3,z4,z478,z6])],[(0,[z181,z1,z2,z3,z379,z6]),(0,[z270,z1,z2,z3,z4,z70])],[(0,[z0,z1127,z2,z3,z4,z6]),(0,[z0,z2,z3,z4,z17,z6]),(0,[z0,z1,z1128,z3,z4,z6]),(0,[z0,z1129,z2,z3,z4,z6]),(0,[z0,z1,z3,z4,z813,z88]),(0,[z0,z1,z1130,z3,z4,z6])],[(0,[z1131,z0,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z1132,z6]),(0,[z1133,z0,z2,z3,z4,z6]),(0,[z0,z42,z2,z3,z4,z100]),(0,[z256,z2,z3,z293,z4,z6]),(0,[z2,z3,z178,z293,z4,z6])]],
   [[(0,[z0,z1,z120,z883,z4,z6]),(0,[z0,z1,z2,z3,z4,z813])],[(0,[z7,z8,z2,z3,z4,z6]),(0,[z155,z1,z257,z3,z4,z6]),(0,[z106,z0,z556,z3,z4,z6]),(0,[z256,z0,z2,z3,z396,z4]),(0,[z1134,z1,z2,z3,z4,z6]),(0,[z0,z1,z44,z3,z45,z6]),(0,[z1,z2,z3,z6,z47,z144]),(0,[z11,z1,z2,z478,z12,z6]),(0,[z0,z1,z2,z310,z715,z6]),(0,[z18,z102,z1,z2,z4,z91])],[(0,[z155,z1,z10,z3,z4,z6]),(0,[z0,z1,z2,z3,z1135,z6]),(0,[z0,z1136,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z1137]),(0,[z1138,z1,z2,z3,z4,z6]),(1,[z0,z772,z3,z4,z6]),(0,[z0,z348,z2,z3,z4,z6])],[(0,[z74,z75,z2,z3,z4,z164]),(0,[z0,z1,z1139,z2,z3,z6]),(0,[z0,z1,z3,z4,z6,z1140]),(0,[z0,z1141,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z631,z61]),(0,[z0,z2,z3,z4,z1142,z6])],[(0,[z57,z1,z2,z3,z4,z6]),(1,[z1,z2,z3,z785,z6]),(0,[z0,z1,z58,z3,z4,z6]),(0,[z0,z1,z44,z34,z3,z6]),(0,[z65,z2,z3,z4,z6,z237])],[(0,[z155,z232,z128,z3,z4,z6]),(0,[z0,z2,z3,z516,z4,z17])],[(0,[z1,z1143,z2,z3,z4,z6]),(0,[z0,z2,z3,z4,z1144,z6])],[(0,[z106,z0,z573,z3,z4,z6]),(0,[z0,z50,z772,z3,z4,z6]),(0,[z0,z434,z36,z3,z27,z6])]],
   [[(0,[z0,z2,z3,z4,z723,z70]),(0,[z1,z1145,z2,z3,z4,z6]),(0,[z0,z290,z349,z2,z3,z6]),(0,[z0,z1,z1146,z2,z3,z4])],[(0,[z455,z127,z0,z3,z4,z6]),(0,[z498,z1,z2,z150,z4,z6]),(0,[z0,z1,z94,z366,z3,z6]),(0,[z11,z420,z0,z2,z12,z6])],[(0,[z162,z0,z3,z4,z6,z70]),(0,[z1147,z1,z2,z3,z4,z6]),(0,[z1,z2,z3,z4,z1148,z6])],[(0,[z74,z576,z2,z3,z4,z6]),(0,[z155,z576,z1,z3,z4,z6]),(0,[z0,z23,z178,z24,z4,z6])],[(0,[z105,z125,z2,z3,z4,z6])],[(0,[z101,z0,z1,z3,z4,z88]),(0,[z1149,z1,z2,z3,z4,z6])],[(0,[z0,z1,z1150,z3,z4,z6]),(0,[z159,z0,z1,z3,z4,z88]),(0,[z11,z80,z1,z2,z12,z6]),(0,[z0,z301,z366,z3,z4,z6]),(0,[z420,z0,z2,z3,z137,z4])],[(0,[z0,z1,z1151,z3,z4,z6]),(0,[z0,z1152,z2,z3,z4,z6]),(0,[z0,z1,z160,z58,z3,z6]),(0,[z0,z1,z1153,z3,z4,z6])]],
   [[],[(0,[z0,z1,z1154,z3,z4,z6]),(0,[z73,z348,z2,z3,z4,z6])],[(0,[z106,z0,z597,z3,z4,z6])],[(0,[z0,z1,z23,z883,z4,z6])],[(0,[z1,z1155,z2,z3,z4,z6]),(0,[z0,z1,z64,z883,z4,z6])],[(0,[z175,z296,z2,z3,z4,z168]),(0,[z0,z2,z3,z32,z713,z6]),(0,[z0,z1,z2,z3,z4,z723]),(0,[z0,z1,z1156,z2,z3,z6]),(0,[z65,z290,z2,z3,z4,z6]),(0,[z80,z1,z179,z3,z4,z6])],[(0,[z0,z738,z2,z3,z4,z6]),(0,[z1,z349,z2,z3,z6,z47]),(0,[z0,z290,z2,z3,z6,z144]),(0,[z1,z2,z3,z1157,z4,z6])],[(0,[z1,z2,z3,z4,z6,z47]),(0,[z1,z2,z3,z359,z4,z6]),(0,[z159,z57,z1,z2,z3,z4])]]]

def SA : ℕ × List W → Bool := fun c => !inB2 8 256 bkA c

def SB : ℕ × List W → Bool := fun c => !inB2 8 256 bkB c

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
theorem pb0 : chunkB SB 1 ((bkA.flatten.flatten.drop 0).take 544) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb1 : chunkB SB 1 ((bkA.flatten.flatten.drop 544).take 536) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb2 : chunkB SB 1 ((bkA.flatten.flatten.drop 1080).take 26) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pbend : ((bkA.flatten.flatten.drop 1106)).isEmpty = true := by
  decide +kernel

theorem windowsB : windowsG (chunkB SB 1) bkA.flatten.flatten 0 [544, 536, 26] = true :=
  windowsG_cons pb0 (windowsG_cons pb1 (windowsG_cons pb2 (windowsG_nil pbend)))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc0 : chunkOK 5 ((bkB.flatten.drop 0).take 107).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc1 : chunkOK 5 ((bkB.flatten.drop 107).take 124).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc2 : chunkOK 5 ((bkB.flatten.drop 231).take 25).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pcend : ((bkB.flatten.drop 256)).isEmpty = true := by
  decide +kernel

theorem windowsC : windowsF 5 bkB.flatten 0 [107, 124, 25] = true :=
  windowsF_cons pc0 (windowsF_cons pc1 (windowsF_cons pc2 (windowsF_nil pcend)))

theorem reject : search 8 rows = false :=
  search_false_C2 (dp := 0) (J := 5) (d := 2) (g1 := 8) (nb1 := 256) (g2 := 8) (nb2 := 256) (by norm_num) gf windowsC windowsB windowsA

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

end PEqualNP.Outside.L_meta_47002

theorem PEqualNP.Outside.L_meta_47002 :
    ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (3941264040 * 2 ^ 32 + 3936922248) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (3941264040 * 2 ^ 32 + 3936922248) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  exact PEqualNP.Outside.L_meta_47002.solve